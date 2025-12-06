#include <iostream>
#include <vector>
#include <string>
#include <unordered_map>
#include <unordered_set>

#define EXPECT_TRUE(x) do { if(!(x)) { std::cerr << "EXPECT_TRUE failed: " #x " at " << __FILE__ << ":" << __LINE__ << "\n"; return 1; } } while(0)
#define EXPECT_EQ(a,b) do { if(!((a)==(b))) { std::cerr << "EXPECT_EQ failed: " #a " vs " #b " => " << (a) << " != " << (b) << " at " << __FILE__ << ":" << __LINE__ << "\n"; return 1; } } while(0)

#include "../project1.cpp"

using namespace backend;

static CFG makeSampleCFG() {
    CFG g;
    BasicBlock b0{0, "L0", {}, {}, {}};
    // v0 = v1 + v2; v3 = v0 * v4; v5 = v3 < v6
    b0.instrs.push_back(Instr{OpKind::Add, Operand::virt(0), Operand::virt(1), Operand::virt(2), {}});
    b0.instrs.push_back(Instr{OpKind::Mul, Operand::virt(3), Operand::virt(0), Operand::virt(4), {}});
    b0.instrs.push_back(Instr{OpKind::CmpLT, Operand::virt(5), Operand::virt(3), Operand::virt(6), {}});
    g.blocks.push_back(b0);
    return g;
}

int main() {
    // use/def test
    Instr add{OpKind::Add, Operand::virt(10), Operand::virt(1), Operand::virt(2), {}};
    auto ud = computeUseDef(add);
    EXPECT_TRUE(ud.use.count(1));
    EXPECT_TRUE(ud.use.count(2));
    EXPECT_TRUE(ud.def.count(10));

    // liveness basic
    CFG g = makeSampleCFG();
    auto lv = liveness(g);
    EXPECT_TRUE(!lv.in[0].empty());
    EXPECT_TRUE(!lv.out[0].empty());

    // // interference graph
    auto ig = buildInterference(g, lv);
    EXPECT_TRUE(!ig.adj.empty());

    // // allocation with small K triggers spill and start-over produces asm
    Backend be; be.cfg.K = 2; // force spills
    auto asmRes = be.compile(g);
    EXPECT_TRUE(asmRes.asmText.find("LOAD") != std::string::npos);
    EXPECT_TRUE(asmRes.asmText.find("STORE") != std::string::npos);

    // // codegen register bounds
    // EXPECT_TRUE(asmRes.usedRegs >= 2);

    // // Larger K reduces spills
    // Backend be2; be2.cfg.K = 6;
    // auto asmRes2 = be2.compile(g);
    // // May or may not have spills, but should compile
    // EXPECT_TRUE(asmRes2.asmText.size() > 0);

    // // Restart behavior and allocation correctness tests
    // // K=2 forced restart: construct sparse IG where alloc.spilled.empty() then forced spill inserts LOAD
    // CFG g2;
    // BasicBlock c0{0, "C0", {}, {}, {}};
    // // v0 = v1 (def v0), next uses v1 to keep it live across first def
    // c0.instrs.push_back(Instr{OpKind::Move, Operand::virt(0), Operand::virt(1), {}, {}});
    // c0.instrs.push_back(Instr{OpKind::Move, Operand::virt(3), Operand::virt(1), {}, {}});
    // g2.blocks.push_back(c0);

    // Backend be3; be3.cfg.K = 2;
    // auto asmRes3 = be3.compile(g2);
    // EXPECT_TRUE(asmRes3.asmText.find("LOAD") != std::string::npos);
    // // also ensure registers used do not exceed K
    auto maxRegFromAsm = [](const std::string &s){
        int m = -1; 
        for (size_t i = 0; i < s.size(); ++i) {
            if (s[i] == 'R' && i + 1 < s.size() && isdigit(static_cast<unsigned char>(s[i+1]))) {
                size_t j = i + 1; int val = 0; 
                while (j < s.size() && isdigit(static_cast<unsigned char>(s[j]))) { val = val*10 + (s[j]-'0'); ++j; }
                if (val > m) m = val;
            }
        }
        return m;
    };
    // EXPECT_TRUE(maxRegFromAsm(asmRes3.asmText) < be3.cfg.K);

    // K=12: allocator should produce conflict-free colors and codegen should not exceed K
    CFG g3 = makeSampleCFG();
    
    auto lv3 = liveness(g3);

    auto ig3 = buildInterference(g3, lv3);
    auto alloc3 = allocateRegisters(ig3, 12);
    
    for (const auto &p : ig3.adj) {
        int u = p.first; 
        for (int v : p.second) {
            EXPECT_TRUE(alloc3.assign.count(u));
            EXPECT_TRUE(alloc3.assign.count(v));

            EXPECT_TRUE(alloc3.assign.at(u) != alloc3.assign.at(v));
            EXPECT_TRUE(alloc3.assign.at(u) >= 0 && alloc3.assign.at(u) < 12);
            EXPECT_TRUE(alloc3.assign.at(v) >= 0 && alloc3.assign.at(v) < 12);
        }
    }

    Backend be4; be4.cfg.K = 12;
    auto asmRes4 = be4.compile(g3);
    EXPECT_TRUE(maxRegFromAsm(asmRes4.asmText) < be4.cfg.K);

    std::cout << "All tests passed" << std::endl;
    return 0;
}

