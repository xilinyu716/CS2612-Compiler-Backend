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
    // per block, per instruction
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

                // case 1: only 1 success (iff the instruction is not the end of basic block)
                if (i + 1 < (int)blk.instrs.size()) {
                    outSet = lv.in[b][i + 1];
                }
                // case 2: could have >= 1 success (iff is the end of block)
                else {
                    for (int s : blk.succ) {
                        if (!cfg.blocks[s].instrs.empty()) {
                            for (int v : lv.in[s][0]) outSet.insert(v);
                        }
                    }
                }
                RegSet inSet = ud.use;

                for (int v : outSet)
                {
                    if (!ud.def.count(v)) {inSet.insert(v);}
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
    std::unordered_map<int, RegSet> adj; // virt reg -> neighbors
};

static InterferenceGraph buildInterference(const CFG &cfg, const LivenessInfo &lv) {
    InterferenceGraph g;
    for (size_t b = 0; b < cfg.blocks.size(); ++b) {
        const auto &blk = cfg.blocks[b];

        for (size_t i = 0; i < blk.instrs.size(); ++i) {
            for (int v : lv.in[b][i]) {
                for (int u : lv.in[b][i]) {
                    if (v == u) continue;
                    g.adj[v].insert(u);
                    g.adj[u].insert(v);
                }
            }
        }
    }
    return g;
}

struct AllocationResult {
    std::unordered_map<int, int> assign; // virt -> phys
    std::unordered_set<int> spilled; // virt regs spilled
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
                // remove n
                for (int m : adj[n]) adj[m].erase(n);
                adj.erase(n);
                it = nodes.erase(it);
                simplified = true;
            } else {
                ++it;
            }
        }

        // cannot simplify any more, spill
        if (!simplified) {
            // spill: pick max degree
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

    // select
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
    // also include pure isolated nodes
    for (auto &p : g.adj) if (!res.assign.count(p.first) && !res.spilled.count(p.first)) res.assign[p.first] = 0;
    return res;
}

struct RewriteResult {
    CFG cfg;
    std::unordered_map<int, int> spillSlot; // virt -> slot id
    int nextVirt;
    int nextSlot;
};

// 重写函数接受 startVirt 和 startSlot，用于在多轮分配中保持状态
static RewriteResult rewriteForSpills(const CFG &orig, const std::unordered_set<int> &spilled, int startVirt = 1000, int startSlot = 0) {
    RewriteResult rr{orig, {}, startVirt, startSlot};
    auto isSpilled = [&](const std::optional<Operand> &o){ return o && o->isVirt() && spilled.count(o->value); };

    auto getSlot = [&](int v){
        auto it = rr.spillSlot.find(v);
        if (it!=rr.spillSlot.end()) return it->second;
        int s = rr.nextSlot++; // 这里的 nextSlot 是从 startSlot 开始递增的
        rr.spillSlot[v]=s;
        return s; };

    for (auto &blk : rr.cfg.blocks) {
        std::vector<Instr> newIns;

        for (auto &ins : blk.instrs) {

            auto emitLoad = [&](int v){
                int t = rr.nextVirt++;
                int slot = getSlot(v);
                newIns.push_back(Instr{OpKind::Load, Operand::virt(t), {}, {}, Operand::mem(slot)});
                return t;
            };

            auto emitStore = [&](int v, int from){
                int slot = getSlot(v); newIns.push_back(Instr{OpKind::Store, {}, Operand::virt(from), {}, Operand::mem(slot)}); };


            if (ins.op == OpKind::Label || ins.op == OpKind::Jump || ins.op == OpKind::CJump) {
                newIns.push_back(ins);
                continue;
            }

            bool use1Sp = isSpilled(ins.src1);
            bool use2Sp = isSpilled(ins.src2);
            bool defSp = isSpilled(ins.dst);

            int t1 = -1, t2 = -1, td = -1;

            Instr mod = ins;
            if (use1Sp)
            {
                t1 = emitLoad(ins.src1->value);
                mod.src1 = Operand::virt(t1);
            }
            if (use2Sp)
            {
                t2 = emitLoad(ins.src2->value);
                mod.src2 = Operand::virt(t2);
            }
            if (defSp && mod.dst)
            {
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
                    os << "LOAD " << physReg(*ins.dst) << ", [fp-" << (ins.extra->value*4) << "]\n";
                    break;
                case OpKind::Store:
                    os << "STORE [fp-" << (ins.extra->value*4) << "], " << formatOp(*ins.src1) << "\n";
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

        // 【修复】引入全局状态计数器
        int stackSlots = 0;       // 记录已分配的栈槽总数
        int currentVirt = 1000;   // 记录当前的虚拟寄存器编号，避免冲突

        int guard = 20;

        // At most rewrite guard rounds
        while (guard--) {
            auto lv = liveness(ir);
            auto ig = buildInterference(ir, lv);
            auto alloc = allocateRegisters(ig, K);

            // If spilled is empty, we are done
            if (alloc.spilled.empty()) {
                // Special edge case: K is too small, force spilling even if graph says ok?
                // Or maybe graph was empty. The original logic for forced spill:
                if (K <= 2 && !ig.adj.empty()) {
                    int pick = -1; size_t best = 0;
                    for (const auto &p : ig.adj) {
                        size_t deg = p.second.size();
                        if (deg >= best) { best = deg; pick = p.first; }
                    }
                    std::unordered_set<int> forced;
                    if (pick != -1) forced.insert(pick);

                    // 【修复】调用时传入当前状态
                    auto rr = rewriteForSpills(ir, forced, currentVirt, stackSlots);
                    ir = rr.cfg;
                    stackSlots = rr.nextSlot; // 更新总槽位
                    currentVirt = rr.nextVirt; // 更新虚拟寄存器ID
                    continue;
                }
                return generateAsm(ir, alloc.assign, stackSlots, K);
            }

            // 【修复】正常溢出路径，传入当前状态
            // 之前的 BUG 是这里默认使用了 startSlot=0，导致多轮溢出时覆盖了之前的槽位
            auto rr = rewriteForSpills(ir, alloc.spilled, currentVirt, stackSlots);
            ir = rr.cfg;
            stackSlots = rr.nextSlot; // 关键：累加槽位
            currentVirt = rr.nextVirt; // 关键：更新ID
        }

        // fallback
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
