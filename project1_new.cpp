#include <iostream>
#include <vector>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <optional>
#include <sstream>

namespace backend {

enum class OpKind { Add, Sub, Mul, CmpLT, Load, Store, Move, Jump, CJump, Label };

struct Operand {
    enum class Kind { VirtReg, Imm, MemSlot, Label };
    Kind kind;
    int value;
    std::string label;
    static Operand virt(int v) { return Operand{Kind::VirtReg, v, {}}; }
    static Operand imm(int v) { return Operand{Kind::Imm, v, {}}; }
    static Operand mem(int slot) { return Operand{Kind::MemSlot, slot, {}}; }
    static Operand lab(const std::string &l) { return Operand{Kind::Label, 0, l}; }
    bool isVirt() const { return kind == Kind::VirtReg; }
    bool isImm() const { return kind == Kind::Imm; }
    bool isMem() const { return kind == Kind::MemSlot; }
    bool isLabel() const { return kind == Kind::Label; }
};

struct Instr {
    OpKind op;
    std::optional<Operand> dst;
    std::optional<Operand> src1;
    std::optional<Operand> src2;
    std::optional<Operand> extra; // for memory addr or label
    std::string toString() const {
        std::ostringstream os;
        switch (op) {
            case OpKind::Add: os << "ADD"; break;
            case OpKind::Sub: os << "SUB"; break;
            case OpKind::Mul: os << "MUL"; break;
            case OpKind::CmpLT: os << "CMPLT"; break;
            case OpKind::Load: os << "LOAD"; break;
            case OpKind::Store: os << "STORE"; break;
            case OpKind::Move: os << "MOVE"; break;
            case OpKind::Jump: os << "BR"; break;
            case OpKind::CJump: os << "BNEZ"; break;
            case OpKind::Label: os << "LABEL"; break;
        }
        auto printOp = [&](const std::optional<Operand> &o) {
            if (!o) return;
            const Operand &x = *o;
            if (x.isVirt()) os << " v" << x.value;
            else if (x.isImm()) os << " #" << x.value;
            else if (x.isMem()) os << " [slot" << x.value << "]";
            else if (x.isLabel()) os << " " << x.label;
        };
        os << " "; printOp(dst); printOp(src1); printOp(src2); printOp(extra);
        return os.str();
    }
};

struct BasicBlock {
    int id;
    std::string label;
    std::vector<Instr> instrs;
    std::vector<int> succ;
    std::vector<int> pred;
};

struct CFG {
    std::vector<BasicBlock> blocks;
    int entry = 0;
};

using RegSet = std::unordered_set<int>;

struct UseDef {
    RegSet use;
    RegSet def;
};

static UseDef computeUseDef(const Instr &ins) {
    UseDef ud;
    auto addUse = [&](const std::optional<Operand> &o){ if (o && o->isVirt()) ud.use.insert(o->value); };
    auto addDef = [&](const std::optional<Operand> &o) {if (o && o->isVirt()) ud.def.insert(o->value); };
    switch (ins.op) {
        case OpKind::Add:
            addUse(ins.src1); addUse(ins.src2); addDef(ins.dst); break;
        case OpKind::Sub:
            addUse(ins.src1); addUse(ins.src2); addDef(ins.dst); break;
        case OpKind::Mul:
            addUse(ins.src1); addUse(ins.src2); addDef(ins.dst); break;
        case OpKind::CmpLT:
            addUse(ins.src1); addUse(ins.src2); addDef(ins.dst); break;
        case OpKind::Move:
            addUse(ins.src1); addDef(ins.dst); break;
        case OpKind::Load:
            addDef(ins.dst); break;
        case OpKind::Store:
            addUse(ins.src1); break;
        case OpKind::CJump:
            addUse(ins.src1); break;
        case OpKind::Jump:
            break;
        case OpKind::Label:
            break;
    }
    return ud;
}

struct LivenessInfo {
    std::vector<std::vector<RegSet>> in;
    std::vector<std::vector<RegSet>> out;
};

static LivenessInfo liveness(const CFG &cfg) {
    LivenessInfo lv;
    lv.in.resize(cfg.blocks.size());
    lv.out.resize(cfg.blocks.size());
    for (size_t b = 0; b < cfg.blocks.size(); ++b) {
        lv.in[b].resize(cfg.blocks[b].instrs.size());
        lv.out[b].resize(cfg.blocks[b].instrs.size());
    }

    bool changed = true;
    while (changed) {
        changed = false;
        for (int b = (int)cfg.blocks.size() - 1; b >= 0; --b) {
            const auto &blk = cfg.blocks[b];
            for (int i = (int)blk.instrs.size() - 1; i >= 0; --i) {
                const auto &ins = blk.instrs[i];
                UseDef ud = computeUseDef(ins);
                RegSet outSet;

                if (i + 1 < (int)blk.instrs.size()) {
                    outSet = lv.in[b][i + 1];
                } else {
                    for (int s : blk.succ) {
                        if (!cfg.blocks[s].instrs.empty()) {
                            for (int v : lv.in[s][0]) outSet.insert(v);
                        }
                    }
                }
                RegSet inSet = ud.use;
                for (int v : outSet) {
                    if (!ud.def.count(v)) { inSet.insert(v); }
                }

                if (lv.in[b][i] != inSet || lv.out[b][i] != outSet) {
                    lv.in[b][i] = std::move(inSet);
                    lv.out[b][i] = std::move(outSet);
                    changed = true;
                }
            }
        }
    }
    return lv;
}

struct InterferenceGraph {
    std::unordered_map<int, RegSet> adj;
};

// 【重要修复 1】: 修复干扰图构建逻辑
static InterferenceGraph buildInterference(const CFG &cfg, const LivenessInfo &lv) {
    InterferenceGraph g;
    for (size_t b = 0; b < cfg.blocks.size(); ++b) {
        const auto &blk = cfg.blocks[b];

        for (size_t i = 0; i < blk.instrs.size(); ++i) {
            const auto &ins = blk.instrs[i];

            // 1. 输入变量之间的干扰 (LiveIn 中的变量两两互斥)
            for (int v : lv.in[b][i]) {
                for (int u : lv.in[b][i]) {
                    if (v == u) continue;
                    g.adj[v].insert(u);
                    g.adj[u].insert(v);
                }
            }

            // 2. 【新增】定义变量与活跃出口变量的干扰
            // 如果 v 是这行指令定义的，u 是这行指令之后还要用的(LiveOut)，
            // 那么 v 和 u 必须占用不同寄存器。
            if (ins.dst && ins.dst->isVirt()) {
                int d = ins.dst->value;
                for (int outVar : lv.out[b][i]) {
                    if (d != outVar) { // 自己不和自己冲突
                        g.adj[d].insert(outVar);
                        g.adj[outVar].insert(d);
                    }
                }
            }
        }
    }
    return g;
}

struct AllocationResult {
    std::unordered_map<int, int> assign;
    std::unordered_set<int> spilled;
};

static AllocationResult allocateRegisters(const InterferenceGraph &g, int K) {
    AllocationResult res;
    std::unordered_map<int, RegSet> adj = g.adj;
    std::vector<int> stack;
    std::unordered_set<int> spillCandidates;
    std::unordered_set<int> nodes;
    for (auto &p : adj) nodes.insert(p.first);

    while (!nodes.empty()) {
        bool simplified = false;
        for (auto it = nodes.begin(); it != nodes.end();) {
            int n = *it;
            size_t deg = adj[n].size();
            if (deg < (size_t)K) {
                stack.push_back(n);
                for (int m : adj[n]) adj[m].erase(n);
                adj.erase(n);
                it = nodes.erase(it);
                simplified = true;
            } else {
                ++it;
            }
        }

        if (!simplified) {
            int pick = -1;
            size_t best = 0;
            for (int n : nodes) {
                size_t deg = adj[n].size();
                if (deg >= best) { best = deg; pick = n; }
            }
            stack.push_back(pick);
            spillCandidates.insert(pick);
            for (int m : adj[pick]) adj[m].erase(pick);
            adj.erase(pick);
            nodes.erase(pick);
        }
    }

    std::unordered_map<int, RegSet> orig = g.adj;
    while (!stack.empty()) {
        int n = stack.back(); stack.pop_back();
        RegSet usedColors;
        for (int m : orig[n]) {
            auto it = res.assign.find(m);
            if (it != res.assign.end()) usedColors.insert(it->second);
        }
        int color = -1;
        for (int c = 0; c < K; ++c) if (!usedColors.count(c)) { color = c; break; }

        if (color == -1) res.spilled.insert(n);
        else res.assign[n] = color;
    }
    for (auto &p : g.adj) if (!res.assign.count(p.first) && !res.spilled.count(p.first)) res.assign[p.first] = 0;
    return res;
}

struct RewriteResult {
    CFG cfg;
    std::unordered_map<int, int> spillSlot;
    int nextVirt;
    int nextSlot;
};

static RewriteResult rewriteForSpills(const CFG &orig, const std::unordered_set<int> &spilled, int startVirt, int startSlot) {
    RewriteResult rr{orig, {}, startVirt, startSlot};
    auto isSpilled = [&](const std::optional<Operand> &o){ return o && o->isVirt() && spilled.count(o->value); };

    auto getSlot = [&](int v){
        auto it = rr.spillSlot.find(v);
        if (it!=rr.spillSlot.end()) return it->second;
        int s = rr.nextSlot++;
        rr.spillSlot[v]=s;
        return s;
    };

    for (auto &blk : rr.cfg.blocks) {
        std::vector<Instr> newIns;

        for (auto &ins : blk.instrs) {
            // 【重要修复 2】: 栈偏移 +1，避免覆盖 [fp-0]
            auto emitLoad = [&](int v){
                int t = rr.nextVirt++;
                int slot = getSlot(v);
                newIns.push_back(Instr{OpKind::Load, Operand::virt(t), {}, {}, Operand::mem(slot + 1)});
                return t;
            };

            auto emitStore = [&](int v, int from){
                int slot = getSlot(v);
                newIns.push_back(Instr{OpKind::Store, {}, Operand::virt(from), {}, Operand::mem(slot + 1)});
            };


            if (ins.op == OpKind::Label || ins.op == OpKind::Jump || ins.op == OpKind::CJump) {
                newIns.push_back(ins);
                continue;
            }

            bool use1Sp = isSpilled(ins.src1);
            bool use2Sp = isSpilled(ins.src2);
            bool defSp = isSpilled(ins.dst);

            int t1 = -1, t2 = -1, td = -1;

            Instr mod = ins;
            if (use1Sp) {
                t1 = emitLoad(ins.src1->value);
                mod.src1 = Operand::virt(t1);
            }
            if (use2Sp) {
                t2 = emitLoad(ins.src2->value);
                mod.src2 = Operand::virt(t2);
            }
            if (defSp && mod.dst) {
                td = rr.nextVirt++;
                mod.dst = Operand::virt(td);
            }
            newIns.push_back(mod);
            if (defSp && td != -1) emitStore(ins.dst->value, td);
        }
        blk.instrs = std::move(newIns);
    }
    return rr;
}

struct CodeGenConfig { int K = 6; };
struct CodeGenResult { std::string asmText; int usedRegs; int stackSlots; };

static CodeGenResult generateAsm(const CFG &cfg, const std::unordered_map<int,int> &assign, int stackSlots, int K) {
    std::ostringstream os;
    os << "; TinyRISC assembly (R0..R" << (K-1) << ")\n";
    os << "PUSH fp\nMOV fp, sp\nSUB sp, sp, #" << (stackSlots*4) << "\n";

    auto formatOp = [&](const Operand &op) -> std::string {
        if (op.isImm()) {
            return "#" + std::to_string(op.value);
        } else if (op.isVirt()) {
            auto it = assign.find(op.value);
            int p = (it == assign.end() ? 0 : it->second);
            return "R" + std::to_string(p);
        }
        return "?";
    };

    auto physReg = [&](const Operand &op) -> std::string {
        return formatOp(op);
    };

    for (const auto &blk : cfg.blocks) {
        os << blk.label << ":\n";
        for (const auto &ins : blk.instrs) {
            switch (ins.op) {
                case OpKind::Add:
                    os << "ADD " << physReg(*ins.dst) << ", " << formatOp(*ins.src1) << ", " << formatOp(*ins.src2) << "\n";
                    break;
                case OpKind::Sub:
                    os << "SUB " << physReg(*ins.dst) << ", " << formatOp(*ins.src1) << ", " << formatOp(*ins.src2) << "\n";
                    break;
                case OpKind::Mul:
                    os << "MUL " << physReg(*ins.dst) << ", " << formatOp(*ins.src1) << ", " << formatOp(*ins.src2) << "\n";
                    break;
                case OpKind::CmpLT:
                    os << "CMPLT " << physReg(*ins.dst) << ", " << formatOp(*ins.src1) << ", " << formatOp(*ins.src2) << "\n";
                    break;
                case OpKind::Move:
                    os << "MOV " << physReg(*ins.dst) << ", " << formatOp(*ins.src1) << "\n";
                    break;
                case OpKind::Load:
                    // 【重要修复 3】: 生成汇编时偏移 +1
                    os << "LOAD " << physReg(*ins.dst) << ", [fp-" << ((ins.extra->value + 1) * 4) << "]\n";
                    break;
                case OpKind::Store:
                    // 【重要修复 3】: 生成汇编时偏移 +1
                    os << "STORE [fp-" << ((ins.extra->value + 1) * 4) << "], " << formatOp(*ins.src1) << "\n";
                    break;
                case OpKind::Jump:
                    os << "BR " << ins.extra->label << "\n";
                    break;
                case OpKind::CJump:
                    os << "BNEZ " << formatOp(*ins.src1) << ", " << ins.extra->label << "\n";
                    break;
                case OpKind::Label:
                    break;
            }
        }
    }
    os << "ADD sp, sp, #" << (stackSlots*4) << "\nPOP fp\nRET\n";
    CodeGenResult r; r.asmText = os.str(); r.usedRegs = K; r.stackSlots = stackSlots; return r;
}

struct Backend {
    CodeGenConfig cfg;
    CodeGenResult compile(CFG ir) {
        int K = cfg.K;
        int stackSlots = 0;
        int currentVirt = 1000;
        int guard = 20;

        while (guard--) {
            auto lv = liveness(ir);
            auto ig = buildInterference(ir, lv);
            auto alloc = allocateRegisters(ig, K);

            if (alloc.spilled.empty()) {
                // 【重要修复 4】：移除强制溢出块，直接返回结果
                return generateAsm(ir, alloc.assign, stackSlots, K);
            }

            auto rr = rewriteForSpills(ir, alloc.spilled, currentVirt, stackSlots);
            ir = rr.cfg;
            stackSlots = rr.nextSlot;
            currentVirt = rr.nextVirt;
        }

        auto lv2 = liveness(ir);
        auto ig2 = buildInterference(ir, lv2);
        auto alloc2 = allocateRegisters(ig2, K);
        return generateAsm(ir, alloc2.assign, stackSlots, K);
    }
};

} // namespace backend



int main() {
    using namespace backend;

    std::cout << "Constructing Complex Test Case: High Register Pressure Loop" << std::endl;
    std::cout << "Scenario: 8 constants live across a loop, with internal branching and accumulation." << std::endl;

    CFG g;

    // ==========================================
    // Virtual Register Map:
    // v1 - v8  : Constants (Loaded once, used inside loop) -> Forces high liveness pressure
    // v10      : Loop Counter (i)
    // v11      : Loop Limit (N)
    // v12      : Accumulator (sum)
    // v20 - v25: Temporary calculation results
    // ==========================================

    // --- Block 0: Initialization ---
    // Init v1..v8, v10=0, v11=10, v12=0
    BasicBlock b0{0, "ENTRY", {}, {1}, {}};
    for(int i=1; i<=8; ++i) {
        // v_i = i * 10
        b0.instrs.push_back(Instr{OpKind::Move, Operand::virt(i), Operand::imm(i * 10), {}, {}});
    }
    b0.instrs.push_back(Instr{OpKind::Move, Operand::virt(10), Operand::imm(0), {}, {}});  // i = 0
    b0.instrs.push_back(Instr{OpKind::Move, Operand::virt(11), Operand::imm(10), {}, {}}); // N = 10
    b0.instrs.push_back(Instr{OpKind::Move, Operand::virt(12), Operand::imm(0), {}, {}});  // sum = 0
    b0.instrs.push_back(Instr{OpKind::Jump, {}, {}, {}, Operand::lab("LOOP_HEADER")});

    // --- Block 1: Loop Header ---
    // if i < N goto BODY else goto EXIT
    BasicBlock b1{1, "LOOP_HEADER", {}, {2, 6}, {0, 5}};
    b1.instrs.push_back(Instr{OpKind::CmpLT, Operand::virt(20), Operand::virt(10), Operand::virt(11), {}}); // t = i < N
    b1.instrs.push_back(Instr{OpKind::CJump, {}, Operand::virt(20), {}, Operand::lab("LOOP_BODY")});
    b1.instrs.push_back(Instr{OpKind::Jump, {}, {}, {}, Operand::lab("EXIT")});

    // --- Block 2: Loop Body (Calculations) ---
    // Force interference: use v1..v8 here.
    // temp1 = v1 + v2
    // temp2 = v3 + v4
    // temp3 = v5 + v6
    // temp4 = v7 + v8
    BasicBlock b2{2, "LOOP_BODY", {}, {3, 4}, {1}};
    b2.instrs.push_back(Instr{OpKind::Add, Operand::virt(21), Operand::virt(1), Operand::virt(2), {}});
    b2.instrs.push_back(Instr{OpKind::Add, Operand::virt(22), Operand::virt(3), Operand::virt(4), {}});
    b2.instrs.push_back(Instr{OpKind::Add, Operand::virt(23), Operand::virt(5), Operand::virt(6), {}});
    b2.instrs.push_back(Instr{OpKind::Add, Operand::virt(24), Operand::virt(7), Operand::virt(8), {}});

    // Condition: if temp1 < temp2 goto TRUE_BRANCH else goto FALSE_BRANCH
    b2.instrs.push_back(Instr{OpKind::CmpLT, Operand::virt(25), Operand::virt(21), Operand::virt(22), {}});
    b2.instrs.push_back(Instr{OpKind::CJump, {}, Operand::virt(25), {}, Operand::lab("TRUE_BRANCH")});
    b2.instrs.push_back(Instr{OpKind::Jump, {}, {}, {}, Operand::lab("FALSE_BRANCH")});

    // --- Block 3: True Branch ---
    // sum = sum + temp3
    BasicBlock b3{3, "TRUE_BRANCH", {}, {5}, {2}};
    b3.instrs.push_back(Instr{OpKind::Add, Operand::virt(12), Operand::virt(12), Operand::virt(23), {}});
    b3.instrs.push_back(Instr{OpKind::Jump, {}, {}, {}, Operand::lab("LOOP_LATCH")});

    // --- Block 4: False Branch ---
    // sum = sum + temp4
    BasicBlock b4{4, "FALSE_BRANCH", {}, {5}, {2}};
    b4.instrs.push_back(Instr{OpKind::Add, Operand::virt(12), Operand::virt(12), Operand::virt(24), {}});
    b4.instrs.push_back(Instr{OpKind::Jump, {}, {}, {}, Operand::lab("LOOP_LATCH")});

    // --- Block 5: Loop Latch (Increment) ---
    // i = i + 1, goto Header
    BasicBlock b5{5, "LOOP_LATCH", {}, {1}, {3, 4}};
    b5.instrs.push_back(Instr{OpKind::Add, Operand::virt(10), Operand::virt(10), Operand::imm(1), {}});
    b5.instrs.push_back(Instr{OpKind::Jump, {}, {}, {}, Operand::lab("LOOP_HEADER")});

    // --- Block 6: Exit ---
    // Result is in v12 (sum)
    BasicBlock b6{6, "EXIT", {}, {}, {1}};
    // Move result to a specific "return" register (e.g. R0) conceptually
    // Here just a move to itself or a dummy use to ensure v12 is live at end
    b6.instrs.push_back(Instr{OpKind::Move, Operand::virt(12), Operand::virt(12), {}, {}});

    // Assemble CFG
    g.blocks.push_back(b0);
    g.blocks.push_back(b1);
    g.blocks.push_back(b2);
    g.blocks.push_back(b3);
    g.blocks.push_back(b4);
    g.blocks.push_back(b5);
    g.blocks.push_back(b6);

    // Set predecessor/successor relationships manually to match instrs
    // (Note: The provided implementation uses these vectors for liveness)
    g.blocks[0].succ = {1};
    g.blocks[1].succ = {2, 6}; g.blocks[1].pred = {0, 5};
    g.blocks[2].succ = {3, 4}; g.blocks[2].pred = {1};
    g.blocks[3].succ = {5};    g.blocks[3].pred = {2};
    g.blocks[4].succ = {5};    g.blocks[4].pred = {2};
    g.blocks[5].succ = {1};    g.blocks[5].pred = {3, 4};
    g.blocks[6].succ = {};     g.blocks[6].pred = {1};

    // ==========================================
    // Compilation
    // ==========================================

    Backend be;
    // CRITICAL: Set K=4.
    // We have v1..v8 (8 regs) + v10, v11, v12 (3 regs) + temps.
    // Total live set > 11. K=4 guarantees heavy spilling.
    be.cfg.K = 4;

    std::cout << "Compiling with K=" << be.cfg.K << " (forcing spills)..." << std::endl;
    std::cout << "---------------------------------------------" << std::endl;

    auto out = be.compile(g);

    std::cout << out.asmText << std::endl;
    std::cout << "---------------------------------------------" << std::endl;
    std::cout << "Compilation Stats:" << std::endl;
    std::cout << "Stack Slots Used: " << out.stackSlots << std::endl;
    std::cout << "Used Registers:   " << out.usedRegs << std::endl;

    return 0;
}
/*int main() {
    using namespace backend;

    std::cout << "=== BUG REPRODUCTION: Def-LiveOut Interference Missing ===" << std::endl;
    std::cout << "Expected Behavior: v1 and v2 must reside in DIFFERENT registers." << std::endl;
    std::cout << "Failure Mode: v2 overwrites v1 because allocator thinks they don't interfere." << std::endl;
    std::cout << "--------------------------------------------------------" << std::endl;

    CFG g;
    BasicBlock b0{0, "ENTRY", {}, {}, {}};

    // 1. 定义 v1 (v1 = 100)
    // LiveOut: {v1}
    b0.instrs.push_back(Instr{OpKind::Move, Operand::virt(1), Operand::imm(100), {}, {}});

    // 2. 定义 v2 (v2 = 200)
    // CRITICAL MOMENT:
    // - v1 is Live (needed in step 3).
    // - v2 is Defined here.
    // - Current logic: Checks LiveIn.
    //   LiveIn here is {v1}. Since only 1 var is in LiveIn, NO interference edge is added.
    // - Correct logic: Should connect Def(v2) with LiveOut(v1).
    b0.instrs.push_back(Instr{OpKind::Move, Operand::virt(2), Operand::imm(200), {}, {}});

    // 3. 使用 v1 和 v2 (v3 = v1 + v2)
    // Should compute 100 + 200 = 300
    b0.instrs.push_back(Instr{OpKind::Add, Operand::virt(3), Operand::virt(1), Operand::virt(2), {}});

    // 4. 防止死代码消除，使用一下 v3
    b0.instrs.push_back(Instr{OpKind::Move, Operand::virt(3), Operand::virt(3), {}, {}});

    g.blocks.push_back(b0);

    // === Compilation ===
    Backend be;
    // Set K=2 (R0, R1).
    // If logic is correct: v1->R0, v2->R1 (or vice versa).
    // If logic is buggy:   v1->R0, v2->R0 (overwrite!).
    be.cfg.K = 2;

    std::cout << "Compiling with K=2..." << std::endl;
    auto out = be.compile(g);

    std::cout << "\nGenerated Assembly:\n-------------------" << std::endl;
    std::cout << out.asmText << std::endl;

    std::cout << "-------------------" << std::endl;
    std::cout << "ANALYSIS:" << std::endl;
    if (out.asmText.find("MOV R0, #100") != std::string::npos &&
        out.asmText.find("MOV R0, #200") != std::string::npos) {
        std::cout << "[FAIL] BUG DETECTED!" << std::endl;
        std::cout << "Both v1 and v2 were assigned to R0." << std::endl;
        std::cout << "Execution trace:" << std::endl;
        std::cout << "  R0 = 100" << std::endl;
        std::cout << "  R0 = 200 (v1 is lost!)" << std::endl;
        std::cout << "  ADD ..., R0, R0 -> Result is 400 (Should be 300)" << std::endl;
    } else {
        std::cout << "[PASS] Logic appears correct (Registers are different)." << std::endl;
    }

    return 0;
}*/
