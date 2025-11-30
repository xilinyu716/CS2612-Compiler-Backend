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
    BasicBlock b0{0, "L0", {}, {1}, {}};
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

    // interference graph
    auto ig = buildInterference(g, lv);
    EXPECT_TRUE(!ig.adj.empty());

    // allocation with small K triggers spill and start-over produces asm
    Backend be; be.cfg.K = 2; // force spills
    auto asmRes = be.compile(g);
    EXPECT_TRUE(asmRes.asmText.find("LOAD") != std::string::npos);
    EXPECT_TRUE(asmRes.asmText.find("STORE") != std::string::npos);

    // codegen register bounds
    EXPECT_TRUE(asmRes.usedRegs >= 2);

    // Larger K reduces spills
    Backend be2; be2.cfg.K = 6;
    auto asmRes2 = be2.compile(g);
    // May or may not have spills, but should compile
    EXPECT_TRUE(asmRes2.asmText.size() > 0);

    std::cout << "All tests passed" << std::endl;
    return 0;
}

