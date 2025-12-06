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
    auto addDef = [&](const std::optional<Operand> &o) {if (o && o->isVirt()) ud.use.insert(o->value); };
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

        // optimization
        // We only need to allocate register for a variable when it's defined
        // Then we check the out set of the instruction
        for (size_t i = 0; i < blk.instrs.size(); ++i) {
            UseDef ud = computeUseDef(blk.instrs[i]);
            for (int d : ud.def) {
                for (int v : lv.out[b][i]) {
                    if (v == d) continue;
                    g.adj[d].insert(v);
                    g.adj[v].insert(d);
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

static RewriteResult rewriteForSpills(const CFG &orig, const std::unordered_set<int> &spilled, int startVirt = 1000, int startSlot = 0) {
    RewriteResult rr{orig, {}, startVirt, startSlot};
    auto isSpilled = [&](const std::optional<Operand> &o){ return o && o->isVirt() && spilled.count(o->value); };
    
    auto getSlot = [&](int v){ 
        auto it = rr.spillSlot.find(v); 
        if (it!=rr.spillSlot.end()) return it->second; 
        int s = rr.nextSlot++; 
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
    auto phys = [&](int virt){ auto it = assign.find(virt); int p = (it==assign.end()?0:it->second); return std::string("R") + std::to_string(p); };
    for (const auto &blk : cfg.blocks) {
        os << blk.label << ":\n";
        for (const auto &ins : blk.instrs) {
            switch (ins.op) {
                case OpKind::Add:
                    os << "ADD " << phys(ins.dst->value) << ", " << phys(ins.src1->value) << ", " << phys(ins.src2->value) << "\n"; break;
                case OpKind::Sub:
                    os << "SUB " << phys(ins.dst->value) << ", " << phys(ins.src1->value) << ", " << phys(ins.src2->value) << "\n"; break;
                case OpKind::Mul:
                    os << "MUL " << phys(ins.dst->value) << ", " << phys(ins.src1->value) << ", " << phys(ins.src2->value) << "\n"; break;
                case OpKind::CmpLT:
                    os << "CMPLT " << phys(ins.dst->value) << ", " << phys(ins.src1->value) << ", " << phys(ins.src2->value) << "\n"; break;
                case OpKind::Move:
                    os << "MOV " << phys(ins.dst->value) << ", " << phys(ins.src1->value) << "\n"; break;
                case OpKind::Load:
                    os << "LOAD " << phys(ins.dst->value) << ", [fp-" << (ins.extra->value*4) << "]\n"; break;
                case OpKind::Store:
                    os << "STORE [fp-" << (ins.extra->value*4) << "], " << phys(ins.src1->value) << "\n"; break;
                case OpKind::Jump:
                    os << "BR " << ins.extra->label << "\n"; break;
                case OpKind::CJump:
                    os << "BNEZ " << phys(ins.src1->value) << ", " << ins.extra->label << "\n"; break;
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
        int guard = 20;
        while (guard--) {
            auto lv = liveness(ir);
            auto ig = buildInterference(ir, lv);
            auto alloc = allocateRegisters(ig, K);
            if (alloc.spilled.empty()) {
                if (K <= 2 && !ig.adj.empty()) {
                    int pick = -1; size_t best = 0;
                    for (const auto &p : ig.adj) {
                        size_t deg = p.second.size();
                        if (deg >= best) { best = deg; pick = p.first; }
                    }
                    std::unordered_set<int> forced;
                    if (pick != -1) forced.insert(pick);
                    auto rr = rewriteForSpills(ir, forced);
                    ir = rr.cfg;
                    stackSlots = std::max(stackSlots, rr.nextSlot);
                    continue;
                }
                return generateAsm(ir, alloc.assign, stackSlots, K);
            }
            auto rr = rewriteForSpills(ir, alloc.spilled);
            ir = rr.cfg;
            stackSlots = std::max(stackSlots, rr.nextSlot);
        }
        // fallback
        auto lv2 = liveness(ir);
        auto ig2 = buildInterference(ir, lv2);
        auto alloc2 = allocateRegisters(ig2, K);
        return generateAsm(ir, alloc2.assign, stackSlots, K);
    }
};

} // namespace backend

#ifdef BACKEND_MAIN
int main() {
    using namespace backend;
    CFG g;
    BasicBlock b0{0, "L0", {}, {1}, {}};
    b0.instrs.push_back(Instr{OpKind::Add, Operand::virt(0), Operand::virt(1), Operand::virt(2), {}});
    b0.instrs.push_back(Instr{OpKind::Mul, Operand::virt(3), Operand::virt(0), Operand::virt(4), {}});
    BasicBlock b1{1, "L1", {}, {}, {0}};
    b1.instrs.push_back(Instr{OpKind::CmpLT, Operand::virt(5), Operand::virt(3), Operand::virt(6), {}});
    g.blocks.push_back(b0); g.blocks.push_back(b1);

    Backend be; be.cfg.K = 3;
    auto out = be.compile(g);
    std::cout << out.asmText << std::endl;
    return 0;
}
#endif
