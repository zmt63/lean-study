import Mathlib

def seqlim_L (a : ℕ → ℝ ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ,n ≥ N → |a n - L| < ε

-- 数列极限 ε-N ↔ Filter.Tendsto a atTop (nhds L)
theorem seqlim_L_eq (a : ℕ → ℝ) (L : ℝ) : seqlim_L a L ↔ Filter.Tendsto a Filter.atTop (nhds L) := by
  unfold seqlim_L
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε; rcases h ε hε with ⟨N, hN⟩; exact ⟨N, λ n hn => by rw [Real.dist_eq]; exact hN n hn⟩
  · intro h ε hε; rcases h ε hε with ⟨N, hN⟩; exact ⟨N, λ n hn => by rw [← Real.dist_eq]; exact hN n hn⟩

--数列极限收敛为0  ≡ Tendsto a atTop (𝓝 0) 参见 Mathlib/Order/Filter/Defs.lean
def seqlim_zero (a : ℕ → ℝ) : Prop :=
  seqlim_L a 0

--数列发散到正无穷  ≡ Tendsto a atTop atTop 参见 Mathlib/Order/Filter/AtTopBot/Tendsto.lean
def seq_infinity  (a : ℕ → ℝ) : Prop :=
  ∀ M > 0, ∃ N : ℕ, ∀ n, n ≥ N → a n > M

--数列发散到负无穷  ≡ Tendsto a atTop atBot 参见 Mathlib/Order/Filter/AtTopBot/Tendsto.lean
def seq_neginfinity(a : ℕ → ℝ) : Prop :=
  ∀ M < 0, ∃ N : ℕ, ∀ n, n ≥ N → a n < M

--数列发散到无穷  ≡ Tendsto a atTop atTop ∨ Tendsto a atTop atBot
def seq_di_infinity (a : ℕ → ℝ) : Prop :=
  ∀ M > 0, ∃ N, ∀ n ≥ N, |a n| > M

--数列有界  ≡ Metric.IsBounded (Set.range a) 参见 Mathlib/Topology/MetricSpace/Bounded.lean
def seq_bounded (a : ℕ → ℝ) : Prop :=
  ∃ M > 0, ∀ n, |a n| ≤ M

--数列无界
def seq_unbounded  (a : ℕ → ℝ) : Prop :=
  ∀ M > 0, ∃ n, |a n| > M

--数列单调递增  ≡ Monotone a 参见 Mathlib/Order/Monotone/Defs.lean
def seq_monotone_in (a : ℕ → ℝ) : Prop :=
  ∀ n, a n ≤ a (n + 1)

--数列单调递减  ≡ Antitone a 参见 Mathlib/Order/Monotone/Defs.lean
def seq_monotone_de (a : ℕ → ℝ) : Prop :=
  ∀ n, a (n + 1) ≤ a n

--数列严格单调递增  ≡ StrictMono a 参见 Mathlib/Order/Monotone/Defs.lean
def seq_strict_mono_in (a : ℕ → ℝ) : Prop :=
  ∀ n, a n < a (n + 1)

--数列严格单调递减  ≡ StrictAnti a 参见 Mathlib/Order/Monotone/Defs.lean
def seq_strict_mono_de (a : ℕ → ℝ) : Prop :=
  ∀ n, a (n + 1) < a n

--数列单调
def seq_monotone (a : ℕ → ℝ) : Prop :=
  seq_monotone_in a ∨ seq_monotone_de a

--数列严格单调
def seq_strict_mono (a : ℕ → ℝ) : Prop :=
  seq_strict_mono_in a ∨ seq_strict_mono_de a

--定义子列  ≡ ∃ k, StrictMono k ∧ b = a ∘ k 参见 Mathlib/Order/Monotone/Defs.lean
def is_subseq (a : ℕ → ℝ) (b : ℕ → ℝ) : Prop :=
  ∃ k : ℕ → ℕ, (∀ n, k n < k (n + 1)) ∧ b = a ∘ k



--收敛数列的极限是唯一的  ≡ tendsto_nhds_unique 参见 Mathlib/Topology/Defs/Filter.lean
theorem con_seq_un(h_lim_L1: seqlim_L a L1) (h_lim_L2: seqlim_L a L2) : L1 = L2 := by
  by_contra h_neq
  have h_pos : |L1 - L2| / 2 > 0 := by
    simp[abs_pos]
    simp[sub_eq_zero]
    exact h_neq
  let ε := |L1 - L2| / 2
  obtain ⟨N1, h_N1⟩ := h_lim_L1 ε h_pos
  obtain ⟨N2, h_N2⟩ := h_lim_L2 ε h_pos

  let N := max N1 N2
  have h_N : N ≥ N1 ∧ N ≥ N2 := by
   constructor
   · apply le_max_left
   · apply le_max_right

  have h_L1 : |a N - L1| < ε := h_N1 N (h_N.1)
  have h_L2 : |a N - L2| < ε := h_N2 N (h_N.2)

  have h_contra : |L1 - L2| < ε + ε := by
    calc
      |L1 - L2| = |(L1 - a N) + (a N - L2)| := by ring_nf
      _ ≤ |L1 - a N| + |a N - L2| := by apply abs_add_le
      _ < ε + ε := by rw[abs_sub_comm]; exact add_lt_add h_L1 h_L2

  have h_eq : ε + ε = |L1 - L2| := by simp [ε]
  rw [h_eq] at h_contra
  exact lt_irrefl _ h_contra

--收敛数列必有界  ≡ Metric.tendsto_isBounded 参见 Mathlib/Topology/MetricSpace/Bounded.lean
theorem con_seq_bounded (h_lim : seqlim_L a L) : seq_bounded a := by
  let ε : ℝ := 1
  have h_ε_pos : ε > 0 := by norm_num
  obtain ⟨N, h_N⟩ := h_lim ε h_ε_pos

  --这里我不熟悉我自定义的名字，于是先展开成了量词逻辑定义
  unfold seq_bounded;unfold seqlim_L at h_lim

  --证明分为两种情况：n < N 和 n ≥ N，
  --n < N的情况有限个数，取前面N-1项的绝对值构造一个有限集，再取最大值；
  --n ≥ N的情况需要推出不等式 |a n| ≤ |L| + 1
  --接着取M为两者的最大值，最后推出目标

  let S := Finset.image (λ i => |a i|) (Finset.range (N + 1))
  have hSne : S.Nonempty := by
    use |a 0|
    apply Finset.mem_image_of_mem (λ i => |a i|) (Finset.mem_range.mpr (Nat.zero_lt_succ N))
    --这个引理可复用，证明了S非空

  let M := max (S.max' hSne) (|L| + 1)
  use M
  constructor
  --拆分合取表达式，通过·分情况讨论，进而解决n难以引入到局部环境的问题
  · have h_pos : 0 < |L| + 1 := by positivity
    exact lt_of_lt_of_le h_pos (le_max_right _ _)

  · intro n
    by_cases hlt : n < N
    · have ninN : n ∈ Finset.range (N + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_lt hlt)
      have aninS : |a n| ∈ S := Finset.mem_image_of_mem (fun i => |a i|) ninN
      have hmem : |a n| ≤ S.max' hSne := Finset.le_max' S (|a n|) aninS
      have hSmaxleM : S.max' hSne ≤ M := by apply le_max_left
      exact le_trans hmem hSmaxleM

    · have hge : n ≥ N := le_of_not_gt hlt
      have h_lim_near : |a n - L| < 1 := h_N n hge
      have h_tri : |a n| ≤ |L| + |a n - L| := by
        calc
          |a n|
              = |(a n - L) + L| := by ring_nf
          _ ≤ |a n - L| + |L| := abs_add_le _ _ --这里不知道为什么需要占位符
          _ = |L| + |a n - L| := by ring

      have h_le : |a n| ≤ 1 + |L| := by
        calc
          |a n| ≤  |L| + |a n - L| := h_tri
          _ ≤ 1 + |L| := by
           linarith
      have hMle : |L| + 1 ≤ M := le_max_right _ _
      bound

--数列保号性  ≡ Filter.Tendsto.eventually_gt 参见 Mathlib/Order/Filter/Basic.lean
theorem seq_sign_pre(h_lim: seqlim_L a L)(L_pos: L > 0):∃ N:ℕ ,∀ n > N, a n > 0 := by
 let ε := L/2
 have h_ε_pos: ε > 0 := by bound
 obtain⟨N , hN⟩ := h_lim ε h_ε_pos
 use N
 intro n h
 -- specialize对局部环境的hN前提进行了量词提取
 specialize hN n (by omega)
 rw[abs_lt] at hN
 --对前提hN合取式进行拆分
 obtain⟨hN1,hN2⟩ := hN
 have hN_left: a n > -ε + L := by linarith [hN1]
 --在前提hN_left中，将ε替换为它的定义值L/2
 unfold ε at hN_left
 -- 证明-(L/2) + L > 0
 have hL_pos : -(L/2) + L > 0 := by bound
 -- 因为最后的不等式推理简易，则利用不等式处理策略linarith处理,也可以用bound
 linarith

--数列保序性  ≡ Filter.Tendsto.le_of_lim 参见 Mathlib/Order/Filter/Basic.lean
theorem seq_sign_in(h_lim_a:seqlim_L a L1)(h_lim_b:seqlim_L b L2)
(h_N0: ∃N₀:ℕ ,∀n > N₀, a n < b n):
L1 ≤ L2 := by
 unfold seqlim_L at h_lim_a h_lim_b
 let ε := (L1-L2)/2
 by_contra h_con

 have h_ε_pos : ε > 0 := by bound
 obtain⟨N1,lima⟩ := h_lim_a ε h_ε_pos
 obtain⟨N2,limb⟩ := h_lim_b ε h_ε_pos
 -- 这里需要提前引入n在局部环境里面?
 unfold ε at lima limb-- 将lima limb的ε重写成它的定义值，即 (L1 - L2) / 2

 -- 取一个具体的n引入局部环境
 rcases h_N0 with ⟨N0, hN0⟩
 let N' := max N1 N2
 let n := max N' N0 + 1
 have h_n_pos: n ≥ N1 ∧ n ≥ N2 :=  by omega -- omega专门解决线性算术，简单不等式等等

 --现在需要lima和limb的全称量词的实例化版本
 specialize lima n h_n_pos.1
 specialize limb n h_n_pos.2

 --接下来需要用lima和limb推出矛盾
 --首先将他们展开为等价的代数式
 rw[abs_lt] at lima;rcases lima with⟨lima1,lima2⟩
 rw[abs_lt] at limb;rcases limb with⟨limb1,limb2⟩ -- 将lima和limb拆开，即合取式拆分策略rcases
 -- 矛盾引子是a n < b n，即h_N0
 --需要对lima1和limb2进行处理
 have hlimaa: -((L1 - L2) / 2) < a n - L1 → (L1 + L2) / 2 < a n := by bound
 apply hlimaa at lima1
 have hlimbb:  b n - L2 < (L1 - L2) / 2 → b n < (L1 + L2)/2 := by bound
 apply hlimbb at limb2
 have nN: n > N0 := by omega
 specialize hN0 n nN
 --因为矛盾明显，最后用bound自动搜索出矛盾
 bound

--若数列发散到正无穷，则任意子列也发散到正无穷
theorem seq_infinity_subseq_infinity(h_lim: seq_infinity a)(h_sub_ab:is_subseq a b) : seq_infinity b
:= by
  unfold seq_infinity
  intro M hM
  rcases h_sub_ab with ⟨φ, h_inc, rfl⟩
  obtain ⟨N, hN⟩ := h_lim M hM
  -- 用数学归纳法证明 φ 最终大于等于 N
  have ⟨K, hK⟩ : ∃ K, φ K ≥ N :=
  by
      by_contra hc
      push Not at hc
      have h_lt : ∀ k, φ k < N := hc
      -- 因为严格递增，φ (N) ≥ N，与 ∀ k < N 矛盾
      have h_φN_ge_N : φ N ≥ N := by
        have h_φ_ge : ∀ n, n ≤ φ n := by
          intro n
          induction n with
          | zero => exact Nat.zero_le _
          | succ n ih =>
              have h_succ : n + 1 ≤ φ n + 1 := Nat.succ_le_succ ih
              have h_step : φ n + 1 ≤ φ (n + 1) := Nat.succ_le_of_lt (h_inc n)
              exact le_trans h_succ h_step
        exact h_φ_ge N

      exact (not_lt_of_ge h_φN_ge_N) (h_lt N)
  use K
  intro k hk
  have hφ_le : φ K ≤ φ k := by
      induction hk with
      | refl => rfl
      | step _ h_ind => exact le_trans h_ind (le_of_lt (h_inc _))
  apply hN
  linarith [hK, hφ_le]

--夹逼定理（数列版本）
theorem seq_squeeze
  (h_lim_a : seqlim_L a L) (h_lim_c : seqlim_L c L)
  (h_bound : ∃ N₀ : ℕ, ∀ n ≥ N₀, a n ≤ b n ∧ b n ≤ c n) : seqlim_L b L := by
  intro ε h_ε
  obtain ⟨N_a, hN_a⟩ := h_lim_a ε h_ε
  obtain ⟨N_c, hN_c⟩ := h_lim_c ε h_ε
  obtain ⟨N₀, hN₀⟩ := h_bound
  let N := max (max N_a N_c) N₀
  use N
  intro n hn

  have hn_a : n ≥ N_a :=
    le_trans (Nat.le_max_left N_a N_c) (le_trans (Nat.le_max_left (max N_a N_c) N₀) hn)
  have hn_c : n ≥ N_c :=
    le_trans (Nat.le_max_right N_a N_c) (le_trans (Nat.le_max_left (max N_a N_c) N₀) hn)
  have hn₀ : n ≥ N₀ := le_trans (Nat.le_max_right _ _) hn

  have ha := hN_a n hn_a
  have hc := hN_c n hn_c
  obtain ⟨h_ab, h_bc⟩ := hN₀ n hn₀

  rw[abs_lt] at *
  have ha_raw := hN_a n hn_a --这既保留了h_Na,还消去了，而且没有显式声明，那么我理解为这是lean的黑箱技巧，只需要输入要操作的命题，量词，消去的前提，have可以直接命名结论
  have ha_rcw := hN_c n hn_c
  --证明前面这一大段都是消去任意量词，引入前提的前提进入局部空间，消去前提的前提等等重复性工作，为了有了证明脚本或新策略的编码能力可大幅度简化


  --拆分拆分目标的合取左右子式
  constructor

  linarith
  --这里是对ha，hc对等价不等式和目标进行匹配，运用linarith直接变换完毕
  linarith [ha.1, ha.2, hc.1, hc.2]


--单调有界定理（递增有上界）
theorem seq_monotone_convergence_inc
  (h_mono : seq_monotone_in a) (h_bdd : ∃ M, ∀ n, a n ≤ M) :
  ∃ L, seqlim_L a L := by
  --展开定义
  unfold seq_monotone_in at h_mono
  unfold seqlim_L
  --存在例化
  obtain ⟨M, hM⟩ := h_bdd
  --构造 S = {a n | n : ℕ}，取上确界 L = sup S
  let S := Set.range a
  have hS_nonempty : S.Nonempty := ⟨a 0, ⟨0, rfl⟩⟩

  --证明S是上确界
  have hS_bdd_above : BddAbove S := by
    refine ⟨M, λ x hx => ?_⟩
    obtain ⟨n, hn⟩ := hx; rw [← hn]; exact hM n
  set L := sSup S with hL_def
  use L
  --任意量词：ε > 0
  intro ε hε
  --由 sSup 性质，存在一项大于 L - ε
  have hL_lt_sup : L - ε < sSup S := by
    rw [hL_def]; linarith
  obtain ⟨x, hxS, hx⟩ := exists_lt_of_lt_csSup hS_nonempty hL_lt_sup
  have hx_range : x ∈ Set.range a := hxS
  obtain ⟨N, hN⟩ := hx_range
  -- 此时 hN: a N = x, hx: L - ε < x，所以 L - ε < a N
  use N
  intro n hn
  --由单调性，对 k ≥ N 归纳：a N ≤ a k
  have haN_le_an : a N ≤ a n :=
    Nat.le_induction (le_refl (a N)) (λ k hNk hk => le_trans hk (h_mono k)) n hn
  --由 sSup 性质：a n ≤ L
  have han_le_L : a n ≤ L := by
    rw [hL_def]
    exact le_csSup hS_bdd_above (by simp [S])
  --整理不等式
  have haN_gt : L - ε < a N := by
    rw [← hN] at hx; exact hx
  have h_low : L - ε < a n := by linarith
  have h_high : a n < L + ε := by linarith
  rw [abs_lt]; exact ⟨by linarith, by linarith⟩

--单调有界定理（递减有下界）
theorem seq_monotone_convergence_dec
  (h_mono : seq_monotone_de a) (h_bdd : ∃ m, ∀ n, m ≤ a n) :
  ∃ L, seqlim_L a L := by
  --展开定义
  unfold seq_monotone_de at h_mono
  unfold seqlim_L
  --存在例化
  obtain ⟨m, hm⟩ := h_bdd
  -- h_mono: ∀ n, a (n+1) ≤ a n;  hm: ∀ n, m ≤ a n
  --构造 S = {a n | n : ℕ}，取下确界 L = inf S
  let S := Set.range a
  have hS_nonempty : S.Nonempty := ⟨a 0, ⟨0, rfl⟩⟩
  have hS_bdd_below : BddBelow S := by
    refine ⟨m, λ x hx => ?_⟩
    obtain ⟨n, hn⟩ := hx; rw [← hn]; exact hm n
  set L := sInf S with hL_def
  use L
  --任意量词：ε > 0
  intro ε hε
  --由 sInf 性质，存在一项小于 L + ε
  have hL_lt : sInf S < L + ε := by
    rw [hL_def]; linarith
  obtain ⟨x, hxS, hx⟩ := exists_lt_of_csInf_lt hS_nonempty hL_lt
  have hx_range : x ∈ Set.range a := hxS
  obtain ⟨N, hN⟩ := hx_range
  -- 此时 hN: a N = x, hx: x < L + ε，所以 a N < L + ε
  use N
  intro n hn
  --由递减单调性，对 k ≥ N 归纳：a k ≤ a N
  have han_le_aN : a n ≤ a N :=
    Nat.le_induction (le_refl (a N)) (λ k hNk hk => le_trans (h_mono k) hk) n hn
  --由 sInf 性质：L ≤ a n
  have hL_le_an : L ≤ a n := by
    rw [hL_def]
    exact csInf_le hS_bdd_below (by simp [S])
  --整理不等式
  have haN_lt : a N < L + ε := by
    rw [← hN] at hx; exact hx
  have h_low : L - ε < a n := by linarith
  have h_high : a n < L + ε := by linarith
  rw [abs_lt]; exact ⟨by linarith, by linarith⟩

--引理：若 b n → +∞，则对任意常数 x，x / b n → 0
theorem seq_const_div_inf_tendsto_zero (x : ℝ) (h_inf : seq_infinity b) : seqlim_zero (λ n => x / b n) := by
  unfold seqlim_zero seqlim_L
  unfold seq_infinity at h_inf
  intro ε hε
  by_cases hx : x = 0
  · -- x = 0 时恒为 0
    subst x; use 0; intro n hn; simp [hε]
  · -- x ≠ 0，取 M = |x|/ε
    have hM : |x| / ε > 0 := div_pos (abs_pos.mpr hx) hε
    rcases h_inf (|x| / ε) hM with ⟨N, hN⟩
    use N; intro n hn
    have hbn_large : b n > |x| / ε := hN n hn
    have hbn_pos : b n > 0 := by linarith
    simp
    rw [abs_div, abs_of_pos hbn_pos]
    have h' : |x| < b n * ε := by
      calc
        |x| = (|x| / ε) * ε := by field_simp [hε.ne']
        _ < b n * ε := mul_lt_mul_of_pos_right hbn_large hε
    field_simp [hbn_pos.ne']
    nlinarith
