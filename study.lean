import Mathlib
open Lean Elab Tactic Meta

example (A B : Set α) : A \ B = A ∩ Bᶜ := by
  ext x
  simp
--这个形式化验证简单，所以描述自然语言语义即可
--
example (A B C:Set α ) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
 --展开几集合相等的定义
  ext x
  --等价/等式展开为两个方向的蕴涵
  constructor
  --第一步，证明x ∈ A ∪ B ∩ C → x ∈ (A ∪ B) ∩ (A ∪ C)
  · intro h --引入目标前提
   -- 将前提h 拆分为两种情况 x ∈ A 和 x ∈ B 且 x ∈ C
    rcases h with (hxA | ⟨hxB,hxC⟩)
    -- 第一种情况，x ∈ A
    · exact ⟨Or.inl hxA, Or.inl hxA⟩  -- 将目标变换成x ∈ A 接着代入前提
     -- 第二种情况，x ∈ B 且 x ∈ C
    · exact ⟨Or.inr hxB, Or.inr hxC⟩
  -- 第二种主情况 证明x ∈ (A ∪ B) ∩ (A ∪ C) → x ∈ A ∪ B ∩ C
  · intro ⟨h1, h2⟩
    -- 将前提h1 拆分为两种情况 x ∈ A ∪ B 和 x ∈ A ∪ C
    rcases h1 with (hxA | hxB)
    -- 第一种情况，x ∈ A ∪ B
    · exact Or.inl hxA
    -- 第二种情况，x ∈ A ∪ C
    · rcases h2 with (hxA' | hxC)
      · exact Or.inl hxA'
      · exact Or.inr ⟨hxB, hxC⟩

example (A B C D : Set α) : (A ×ˢ B) \ (C ×ˢ D) = ((A \ C) ×ˢ B) ∪ (A ×ˢ (B \ D)) := by
  --集合A与集合B的直积除去集合C与集合D的直积等于(集合A除去集合C)与集合B的直积并上(集合A与集合B除去集合D)的直积
  ext ⟨x, y⟩ --集合积是多元组，所以展开需要输入多元组的元素
  simp
  tauto --自动化证明，tauto的输入范畴是命题逻辑范畴，不涉及量词

open Filter

example (A : Set α) (s : ℕ → Set α) : limsup (fun n => A \ s n) atTop = A \ liminf s atTop := by
  ext x
  simp [mem_limsup_iff_frequently_mem, mem_liminf_iff_eventually_mem, eventually_atTop, frequently_atTop]
  constructor
  · intro h
    constructor
    · rcases h 0 with ⟨b, hb, hA, hn⟩; exact hA
    · intro a; rcases h a with ⟨b, hb, hA, hn⟩; exact ⟨b, hb, hn⟩
  · rintro ⟨hA, h⟩ a
    rcases h a with ⟨b, hb, hn⟩
    exact ⟨b, hb, hA, hn⟩

example (A : Set α) (s : ℕ → Set α) : liminf (fun n => A \ s n) atTop = A \ limsup s atTop := by
  ext x
  simp [mem_limsup_iff_frequently_mem, mem_liminf_iff_eventually_mem, eventually_atTop, frequently_atTop]
  constructor
  · rintro ⟨a, ha⟩
    constructor
    · exact (ha a (le_refl a)).1
    · exact ⟨a, fun b hb => (ha b hb).2⟩
  · rintro ⟨hA, a, ha⟩
    refine ⟨a, fun b hb => ⟨hA, ha b hb⟩⟩

def m : IO Unit := IO.println "Hello,Lean"

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStderr

  stdout.putStrLn "How would you like to be adressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"

def first(x : List Nat) : Nat :=
  match x with
  | [] => 0
  | x :: _ => x

def x : List Nat := [1, 2, 3]
def y : List Nat := [4, 5, 6]
def z : List Nat := [7, 8, 9]

def w : List (List Nat) := [x, y, z]

#eval first y

def last(x : List Nat) : Nat :=
  match x with
  | [] => 0
  | x :: [] => x
  | _ :: x => last x

open Lean Elab Tactic


elab "my_tac" : tactic => do
  evalTactic (← `(tactic| trivial))

example : 1 = 1 := by
 my_tac

elab "my_solver" : tactic => do
  evalTactic (← `(tactic|
    first
    | assumption
    | simp
    | trivial))
-- first：按顺序尝试，成功一个就停；全失败则整体失败
-- assumption：尝试使用前提，成功则停；失败则继续尝试
-- simp：尝试使用simp，成功则停；失败则继续尝试
-- trivial：尝试使用trivial，成功则停；失败则整体失败


example : 1 = 1 := by
 my_solver

#eval last y

def seqlim (a : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - a N| < ε

theorem test (ε : ℝ) (n N: ℕ)  (hlim: seqlim  a)(hε : ε > 0) (hnN: n ≥ N): |a n - a N| < ε := by
  unfold seqlim at hlim
  sorry

#check (IO.println)
#check @IO.println
/-3.2.2. 使用实例隐式定义多态函数

🔗

一个对列表中所有元素求和的函数需要两个实例：Add允许元素相加，OfNat α 0实例则为空列表提供一个合理的返回值：

def List.sumOfContents [Add α] [OfNat α 0] : List α → α

| [] => 0

| x :: xs => x + xs.sumOfContents-/

/-3.2.2 使用实例隐式定义多态函数
一个对列表中所有元素求和的函数需要两个实例：Add允许元素相加，OfNar α 0实例则为空列表提供一个合理的返回值：

def List.sumOfContents [Add α] [OfNat α 0] : List α → α
 | [] => 0
 | x :: xs = > x + xs.sumPfContents

-/

--偶数数据类型

inductive Eve : Type where
  | zero : Eve
  | addTwo : Eve → Eve

--写了 (2 : Even) 后，Lean 会展开成 OfNat.ofNat Even 2，然后自动查找类型类实例 OfNat Even 2。因此只要提供实例，就能直接用 2 : Even 而不必手写 Even.addTwo Even.zero。

namespace Eve

instance : OfNat Eve 0 where
  ofNat := zero

instance [OfNat Eve n] : OfNat Eve (n + 2) where
  ofNat := addTwo (OfNat.ofNat (α := Eve) n)

end Eve

#eval (10 : Eve)

def thirdlist (xs : List α) : Option α :=
  xs[2]?

#eval thirdlist [1, 2]

def thirdList' : List α → Option α
  | _x :: _y :: z :: _rest => some z   -- 前两个丢弃，取第三个
  | _ => none                          -- 不够三个，返回无

#eval thirdList' [1, 2, 3, 4, 5]

def thirdSafe {α : Type} (a : Array α) (h : 3 ≤ a.size): α :=
    a[2]

#eval thirdSafe #[1, 2, 3, 4, 5] (by simp)

def M2 : Matrix (Fin 2) (Fin 3) Nat := !![1, 2, 3,;4, 5, 6]
#eval M2 1 2

--手搓矩阵
def mat : List (List Nat) := [[1, 2, 3], [4, 5, 6]]

def getElemMat(m : List (List Nat)) (i j : Nat) : Option Nat :=
  match m[i]? with --在矩阵m中查第i行
  | some row => row[j]? -- 若存在第i行，则在第i行中查第j列，最后返回第i行第j列的元素
  | none => none   -- 若不存在第i行，则返回none

#eval getElemMat mat 1 5

inductive gender where
  | male : gender
  | female : gender

structure human where
  name : String
  age : Nat
  Height : Float
  Weight : Float
  gender : gender


def zhou : human := {name := "周哥", age := 100, Height := 170.0, Weight := 60.0, gender := gender.male}


inductive aBool where
  | true : aBool
  | false : aBool

elab "my_tactic" : tactic => do
  -- 这里运行在 TacticM 里，可以做：
  logInfo "操操操"            -- 打印信息
  -- ... 干点啥 ...

example(a : ℕ): a + a = 2 * a := by

  bound
  my_tactic

elab "inspect_goal" : tactic => do
  let g ← getMainGoal                       -- 拿到当前目标
  let ty ← g.getType                        -- 目标的类型（一个 Expr）

  logInfo m!"当前目标：{g}"
  logInfo m!"目标类型: {ty}"
  logInfo m!"目标是否以 ∀ 开头: {ty.isForall}"
  -- 打印所有假设
  let lctx ← getLCtx
--lctx：局部上下文存进了这个自定义命名
--lctx.decls：局部上下文中的一个字段，表示当前证明点上所有的局部声明
--局部上下文：当前目标携带的声明清单（如变量、假设、let 绑定，注意：每个目标本身携带自己的上下文）
-- 目标 = 上下文 + 待证命题；每个目标各带一份，g.withContext 后 getLCtx 读取。

/-证明状态 (整个 TacticM 状态)
  ├─ 元变量记录表 MetavarContext  （记录所有目标）
  │     └─ 每个目标 MetavarDecl = 上下文 LocalContext + 待证命题 type
  ├─ 未解决目标列表（要处理的 MVarId 列表）
  └─ 回溯栈、索引等-/

  for d in lctx.decls do
  --把 lctx.decls 里的每个元素依次取出来，赋给变量 d，然后执行 do 后面的代码。
  --decl 是局部上下文中的一个声明，包含了这个声明的名字和类型
  --some decl 表示这个声明存在，none 表示这个声明不存在
    match d with
    --对d进行模式匹配，如果d是某个声明，则打印这个声明的名字和类型
    | some decl => logInfo m!"假设 {decl.userName} : {decl.type}"
    | none => pure ()


--pure ()一个负责占位，告诉检查器表示什么都没发生的类型

example(a : ℕ)(h : a > 0) :a + a = 2 * a := by
  inspect_goal
  bound

/-① macro          —— 纯语法糖，编译期文本替换（最简单）
② elab + eval_tactic —— 组装式，带 Monad（能 if/循环/读状态）
③ elab 带参数    —— ident / num / term 参数化
④ syntax + elab_rules —— 自定义全新语法（如中缀符号）
⑤ tacticSeq 参数 —— 接收一段策略块（你的 trace_block 就是这种）
⑥ liftMetaTactic —— 底层直接操作 MVarId
⑦ macro_rules   —— 规则式宏（"遇到这个模式就展开成那个"）-/

macro "eps_begin" : tactic => `(tactic| intro α hα)

def seqlim_L (a : ℕ → ℝ) (L : ℝ): Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, n ≥ N → |a n - L| < ε

example : seqlim_L (fun n => 0) 0 := by
  unfold seqlim_L
  eps_begin
  rename_i ε' hε'   -- ← 等价于打 intro ε hε
  use 0
  intro n hn
  simpa using hε'   -- |0 - 0| < ε 化简后就是 hε

macro "have_h" h:ident ":" t:term : tactic =>
  `(tactic| have $h : $t := by assumption)


/- #奇怪的二维数组 -/

-- 两种元素：用归纳类型正好表示"只有两种"
inductive Cell : Type where
  | Black | White

deriving DecidableEq, Repr

open Cell

-- 网格：r 行 c 列，Fin 索引在类型层面就保证了边界
abbrev Grid (r c : ℕ) := Fin r → Fin c → Cell

/- 从 (i,j) 向上数：连续与起点同色的行数（起点自身算 1）。
   第一个参数 steps 是"剩余步数"，模式匹配让它结构递归 → 终止检查自动通过。 -/
def countUpAux {r c : ℕ} (a : Grid r c) (base : Cell) (j : Fin c) : ℕ → ℕ → ℕ
  | 0, _ => 0                  -- steps 为 0：预算用完，返回 0，结束递归
  | steps + 1, row =>          -- steps 至少 1：拆出 steps，row 是当前行号
    if h : row < r then        -- row 越界吗？（要 row < r 才合法）
      if a ⟨row, h⟩ j = base then       -- 取 (row,j) 的格子，等于 base 吗（同色？）
        1 + countUpAux a base j steps (row - 1)  -- 同色：+1，预算-1，继续数上一行
      else 0                   -- 不同色：连00续断了，返回 0
    else 0                     -- 越界：返回 0

def countUp {r c : ℕ} (a : Grid r c) (i : Fin r) (j : Fin c) : ℕ :=
  countUpAux a (a i j) j (i.val + 1) i.val  -- 起点颜色作 base，预算 i+1，从第 i 行开始数

/- 向右数，对称版本 -/
def countRightAux {r c : ℕ} (a : Grid r c) (base : Cell) (i : Fin r) : ℕ → ℕ → ℕ
  | 0, _ => 0                  -- steps 为 0：预算用完，返回 0，结束递归
  | steps + 1, col =>          -- steps 至少 1：拆出 steps，col 是当前列号
    if h : col < c then        -- col 越界吗？（要 col < c 才合法）
      if a i ⟨col, h⟩ = base then       -- 取 (i,col) 的格子，等于 base 吗（同色？）
        1 + countRightAux a base i steps (col + 1)  -- 同色：+1，预算-1，继续数右一列
      else 0                   -- 不同色：连续断了，返回 0
    else 0                     -- 越界：返回 0

def countRight {r c : ℕ} (a : Grid r c) (i : Fin r) (j : Fin c) : ℕ :=
  countRightAux a (a i j) i (c - j.val) j.val  -- 起点颜色作 base，预算 c-j，从第 j 列开始数

-- 左下角坐标 (r-1, 0)
def bottomLeft (r c : ℕ) (hr : 0 < r) (hc : 0 < c) : Fin r × Fin c :=
  (⟨r - 1, by omega⟩, ⟨0, hc⟩)

/- 奇怪的二维数组：r,c ≥ 2；左下角起点；v1 ∈ [1, r)；v2 ∈ [1, c) -/
def weirdGrid (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (a : Grid r c) : Prop :=
  let p := bottomLeft r c (by omega) (by omega)
  let v1 := countUp a p.1 p.2
  let v2 := countRight a p.1 p.2
  1 ≤ v1 ∧ v1 < r ∧ 1 ≤ v2 ∧ v2 < c

-- 注册可判定性，才能用 decide / native_decide 自动验证
instance (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (a : Grid r c) :
    Decidable (weirdGrid r c hr hc a) := by
  unfold weirdGrid
  infer_instance

/- 通用版本：元素类型任意 α，只要求取值最多两种 -/
def AtMostTwo {α : Type} (r c : ℕ) (a : Fin r → Fin c → α) : Prop :=
  ∃ x y : α, ∀ i j, a i j = x ∨ a i j = y

/- 例子：3×3，底行 = 白 白 黑，其余全黑。
   左下角 (2,0)=白：向上(1,0)=黑 → v1=1；向右 白白黑 → v2=2 ✓ -/
def exampleGrid : Grid 3 3 := fun i j =>
  if i = ⟨2, by decide⟩ then
    if j = ⟨2, by decide⟩ then Black else White
  else Black

-- 机器验证 + 数值检查
example : weirdGrid 3 3 (by norm_num) (by norm_num) exampleGrid := by
  native_decide

#eval countUp exampleGrid ⟨2, by decide⟩ ⟨0, by decide⟩      -- 1
#eval countRight exampleGrid ⟨2, by decide⟩ ⟨0, by decide⟩   -- 2
