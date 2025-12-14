# CS2612-Project-1
## 寄存器分配与CodeGen
本项目实现了一个编译器后端原型，包含：

- 在控制流图（CFG）上按指令计算 `use/def`
- 基于 `use/def` 的指令级活性分析，计算 `in/out`
- 生成干扰图（Interference Graph）
- 基于干扰图的寄存器分配（simplify/spill）并支持溢出后重写CFG
- 支持 start-over 的迭代寄存器分配，直到无溢出或达到保护上限
- 生成 TinyRISC 风格的汇编代码
- 测试框架

## 数据结构与输入格式

- `Operand`：操作数，类型包括 `VirtReg`（虚拟寄存器，整数ID）、`Imm`（立即数）、`MemSlot`（栈槽ID，用于溢出装载/存储）、`Label`
- `Instr`：指令，`OpKind` 包含 `Add/Sub/Mul/CmpLT/Load/Store/Move/Jump/CJump/Label`
  - `Add/Sub/Mul/CmpLT/Move`：三地址形式，`dst = op(src1, src2)` 或 `dst = src1`
  - `Load`：`dst = [fp - slot*4]`
  - `Store`：`[fp - slot*4] = src1`
  - `Jump/CJump`：跳转与条件跳转（条件非零）
- `BasicBlock`：基本块，包含 `instrs/succ/pred/label`
- `CFG`：控制流图，`blocks` 与 `entry`

示例见 `tests/test_all.cpp` 中 `makeSampleCFG()`。

## use/def 与活性分析

- `use/def`：对每条指令计算使用与定义的虚拟寄存器集合
- 活性分析：对每条指令计算 `in/out`，采用自底向上的迭代数据流：
  - `out[i] = \bigcup in[s]`（后继）或 `in[next]`（块内顺序）
  - `in[i] = use[i] ∪ (out[i] − def[i])`

## 干扰图与寄存器分配

- 干扰图边规则：若存在指令i, 使得寄存器u, v同时在in[i]中，则加边 `(u, v) `
- 分配算法：
  - `simplify`：度 `< K` 的节点入栈并从图中移除
  - 若无法简化，选择最大度节点作为 `spill` 候选，入栈并移除
  - `select`：出栈着色，若无可用颜色则标记为 `spilled`

## 溢出重写与 start-over

- 对被标记为溢出的虚拟寄存器 `v`：
  - 每次使用前插入 `LOAD t, [slot_v]`，将该使用替换为临时 `t`
  - 每次定义后插入 `STORE [slot_v], t`，将定义替换为临时 `t`
- 重写产生新的临时与栈槽，随后重新计算 `use/def`、活性、干扰图并再次分配，直到无溢出或达到迭代上限。

## 汇编代码风格（TinyRISC）

- 物理寄存器：`R0..R(K-1)`，`K` 可配置（默认 `6`）
- 栈框架：使用 `fp` 与 `sp`，函数序言/结尾：
  - `PUSH fp` / `MOV fp, sp` / `SUB sp, sp, #stack_bytes`
  - 结束：`ADD sp, sp, #stack_bytes` / `POP fp` / `RET`
- 指令模板：
  - `ADD dst, src1, src2` / `SUB` / `MUL` / `CMPLT`
  - `MOV dst, src1`
  - `LOAD dst, [fp-offset]` / `STORE [fp-offset], src`
  - `BR label` / `BNEZ r, label`

## 构建与测试
```bash
mkdir -p build && cd build
cmake ..
cmake --build .
./demo
./run_tests```





