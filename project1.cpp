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
    auto addDef = [&](const std::optional<Operand> &o){ if (o && o->isVirt()) ud.def.insert(o->value); };
    switch (ins.op) {
        case OpKind::Add:
        case OpKind::Sub:
        case OpKind::Mul:
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
    LivenessInfo lv; lv.in.resize(cfg.blocks.size()); lv.out.resize(cfg.blocks.size());
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
                for (int v : outSet) if (!ud.def.count(v)) inSet.insert(v);
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
        if (!simplified) {
            // spill: pick max degree
            int pick = -1; size_t best = 0;
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
    auto getSlot = [&](int v){ auto it = rr.spillSlot.find(v); if (it!=rr.spillSlot.end()) return it->second; int s = rr.nextSlot++; rr.spillSlot[v]=s; return s; };
    for (auto &blk : rr.cfg.blocks) {
        std::vector<Instr> newIns;
        for (auto &ins : blk.instrs) {
            auto emitLoad = [&](int v){ int t = rr.nextVirt++; int slot = getSlot(v); newIns.push_back(Instr{OpKind::Load, Operand::virt(t), {}, {}, Operand::mem(slot)}); return t; };
            auto emitStore = [&](int v, int from){ int slot = getSlot(v); newIns.push_back(Instr{OpKind::Store, {}, Operand::virt(from), {}, Operand::mem(slot)}); };
            if (ins.op == OpKind::Label || ins.op == OpKind::Jump || ins.op == OpKind::CJump) {
                newIns.push_back(ins);
                continue;
            }
            bool use1Sp = isSpilled(ins.src1);
            bool use2Sp = isSpilled(ins.src2);
            bool defSp = isSpilled(ins.dst);
            int t1 = -1, t2 = -1, td = -1;
            Instr mod = ins;
            if (use1Sp) { t1 = emitLoad(ins.src1->value); mod.src1 = Operand::virt(t1); }
            if (use2Sp) { t2 = emitLoad(ins.src2->value); mod.src2 = Operand::virt(t2); }
            if (defSp && mod.dst) { td = rr.nextVirt++; mod.dst = Operand::virt(td); }
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
#ifdef LIVENESS_MAIN
#include <vector>
#include <string>
#include <set>
#include <algorithm>
#include <iterator>
using namespace std;
using Variable = string;
using VariableSet = set<Variable>;

enum class InstructionType {
    ASSIGN_ARITHMETIC,
    ASSIGN_CONSTANT,
    COMPARE,
    MEMORY_STORE,
    MEMORY_LOAD,
    JUMP,
    CONDITIONAL_JUMP,
};

struct Instruction {
    InstructionType type;
    string id;
    VariableSet use;
    VariableSet def;
    VariableSet in;
    VariableSet out;
    Variable result_var;
    Variable operand1;
    Variable operand2;
    Variable address_var;
    Instruction(InstructionType t, const string& i) : type(t), id(i) {}
};

struct BasicBlock {
    string label;
    vector<Instruction> instructions;
    vector<BasicBlock*> successors;
    VariableSet in;
    VariableSet out;
};

VariableSet set_difference(const VariableSet& a, const VariableSet& b) {
    VariableSet result;
    set_difference(a.begin(), a.end(), b.begin(), b.end(),
                   inserter(result, result.begin()));
    return result;
}

VariableSet set_union(const VariableSet& a, const VariableSet& b) {
    VariableSet result = a;
    result.insert(b.begin(), b.end());
    return result;
}

void compute_instruction_use_def(Instruction& instr) {
    instr.use.clear();
    instr.def.clear();
    auto safe_insert = [](VariableSet& set, const Variable& var) {
        if (!var.empty()) {
            set.insert(var);
        }
    };
    switch (instr.type) {
        case InstructionType::ASSIGN_ARITHMETIC:
        case InstructionType::COMPARE:
            safe_insert(instr.def, instr.result_var);
            safe_insert(instr.use, instr.operand1);
            safe_insert(instr.use, instr.operand2);
            break;
        case InstructionType::ASSIGN_CONSTANT:
            safe_insert(instr.def, instr.result_var);
            break;
        case InstructionType::MEMORY_STORE:
            safe_insert(instr.use, instr.operand1);
            safe_insert(instr.use, instr.address_var);
            break;
        case InstructionType::MEMORY_LOAD:
            safe_insert(instr.def, instr.result_var);
            safe_insert(instr.use, instr.address_var);
            break;
        case InstructionType::CONDITIONAL_JUMP:
            safe_insert(instr.use, instr.operand1);
            break;
        case InstructionType::JUMP:
            break;
    }
}

void compute_cfg_use_def(vector<BasicBlock>& cfg_blocks) {
    for (auto& block : cfg_blocks) {
        for (auto& instruction : block.instructions) {
            compute_instruction_use_def(instruction);
        }
    }
}

// ------------------------------------
// ���Է���ʵ��
// ------------------------------------

void liveness_analysis(vector<BasicBlock>& cfg_blocks) {
    bool changed;
    do {
        changed = false;
        // �������������
        for (auto it = cfg_blocks.rbegin(); it != cfg_blocks.rend(); ++it) {
            BasicBlock& block = *it;

            // 1. ���� Basic Block �� OUT ����
            // out(B) = Union of in(S) for all successors S of B
            VariableSet new_block_out;
            for (BasicBlock* succ : block.successors) {
                new_block_out = set_union(new_block_out, succ->in);
            }
            if (new_block_out != block.out) {
                block.out = new_block_out;
                changed = true;
            }

            // 2. ����ָ��Ļ��Դ��� (����)
            VariableSet current_in = block.out;

            // �����������ָ��
            for (auto instr_it = block.instructions.rbegin(); instr_it != block.instructions.rend(); ++instr_it) {
                Instruction& instr = *instr_it;

                // out(u) = in(u+1)
                instr.out = current_in;

                // in(u) = (out(u) - def(u)) U use(u)
                VariableSet new_in = set_union(set_difference(instr.out, instr.def), instr.use);

                if (new_in != instr.in) {
                    instr.in = new_in;
                    changed = true;
                }

                // Ϊǰһ��ָ������ out
                current_in = instr.in;
            }

            // 3. ���� Basic Block �� IN ����
            // in(B) �ǿ��ڵ�һ��ָ��� in ����
            if (!block.instructions.empty()) {
                VariableSet new_block_in = block.instructions.front().in;
                if (new_block_in != block.in) {
                    block.in = new_block_in;
                }
            }
        }
    } while (changed);
}

void print_instruction_liveness(const Instruction& instr) {
    auto print_set = [](const VariableSet& s) {
        cout << "{";
        bool first = true;
        for (const auto& var : s) {
            if (!first) cout << ", ";
            cout << var;
            first = false;
        }
        cout << "}";
    };

    cout << "  Instruction " << instr.id << ":\n";
    cout << "    DEF: ";  print_set(instr.def);
    cout << " | USE: ";  print_set(instr.use);
    cout << " | IN: ";   print_set(instr.in);
    cout << " | OUT: ";  print_set(instr.out);
    cout << "\n";
}

void print_block_liveness(const BasicBlock& block) {
    auto print_set = [](const VariableSet& s) {
        cout << "{";
        bool first = true;
        for (const auto& var : s) {
            if (!first) cout << ", ";
            cout << var;
            first = false;
        }
        cout << "}";
    };
    cout << "Basic Block " << block.label << " Summary:\n";
    cout << "  IN: "; print_set(block.in);
    cout << " | OUT: "; print_set(block.out);
    cout << "\n";
}

int main() {
    // 1. ���� CFG �ṹ
    vector<BasicBlock> cfg;
    BasicBlock bb1;
    bb1.label = "L1";
    BasicBlock bb2;
    bb2.label = "L2";

    // 2. L1 ָ��
    bb1.instructions.emplace_back(InstructionType::ASSIGN_ARITHMETIC, "i1");
    bb1.instructions.back().result_var = "v1";
    bb1.instructions.back().operand1 = "v2";
    bb1.instructions.back().operand2 = "v3";

    bb1.instructions.emplace_back(InstructionType::COMPARE, "i2");
    bb1.instructions.back().result_var = "v4";
    bb1.instructions.back().operand1 = "v1";
    bb1.instructions.back().operand2 = "v5";

    bb1.instructions.emplace_back(InstructionType::MEMORY_STORE, "i3");
    bb1.instructions.back().address_var = "p";
    bb1.instructions.back().operand1 = "v4";

    bb1.instructions.emplace_back(InstructionType::MEMORY_LOAD, "i4");
    bb1.instructions.back().result_var = "v6";
    bb1.instructions.back().address_var = "p";

    bb1.instructions.emplace_back(InstructionType::CONDITIONAL_JUMP, "i5");
    bb1.instructions.back().operand1 = "v6";

    // 3. L2 ָ��
    bb2.instructions.emplace_back(InstructionType::ASSIGN_ARITHMETIC, "i6");
    bb2.instructions.back().result_var = "v7";
    bb2.instructions.back().operand1 = "v1";
    bb2.instructions.back().operand2 = "v5";

    bb2.instructions.emplace_back(InstructionType::ASSIGN_CONSTANT, "i7");
    bb2.instructions.back().result_var = "v8";

    cfg.push_back(bb1);
    cfg.push_back(bb2);

    // 4. ���� CFG �ߣ�L1 -> L2
    cfg[0].successors.push_back(&cfg[1]);

    // 5. ���� Use �� Def
    compute_cfg_use_def(cfg);

    // 6. ִ�л��Է���
    liveness_analysis(cfg);

    // 7. ��ӡ���Է������
    cout << "\n--- ���Է��� (Liveness Analysis) ���ս�� ---\n";

    // ��ӡ����ܽ�
    print_block_liveness(cfg[1]);
    print_block_liveness(cfg[0]);

    cout << "\n--- ����ָ������ ---\n";

    cout << "Basic Block L2:\n";
    for (const auto& instruction : cfg[1].instructions) {
        print_instruction_liveness(instruction);
    }

    cout << "\nBasic Block L1:\n";
    for (const auto& instruction : cfg[0].instructions) {
        print_instruction_liveness(instruction);
    }

    return 0;
}
#endif
