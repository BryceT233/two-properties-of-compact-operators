/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

variable {k : Type v} [rc : RCLike k] {X : Type u_0} [NormedAddCommGroup X]
[NormedSpace k X] {Y : Type u_1} [NormedAddCommGroup Y] [NormedSpace k Y]

-- A map $f$ satisfying $f (r • x) = r • f x$ is a compact operator if and only if for all bounded sequence $u_i$ in X, there exists a converging subsequence of $f (u_i)$ in $Y$
theorem isCompactOperator_iff_seq {f : X → Y} (f_smul : ∀ (r : k) (x : X), f (r • x) = r • f x) :
    IsCompactOperator f ↔ ∀ u : ℕ → X, Bornology.IsBounded (Set.range u) → ∃ a : Y, ∃ φ : ℕ → ℕ,
    StrictMono φ ∧ Filter.Tendsto (f ∘ u ∘ φ) Filter.atTop (nhds a) := by
  constructor
  -- Assume $f$ is a compact operator, take a bounded sequence $u_i$ in $X$
  · intro hf u u_bd; rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact] at hf
  -- By definition, there exists a ball in $X$ whose image under $f$ is contained in a compact set $V$ in $Y$
    rcases hf with ⟨U, hU, ⟨V, hV, hUV⟩⟩
    simp only [Metric.mem_nhds_iff, gt_iff_lt, Metric.ball, dist_zero_right, Set.subset_def,
      Set.mem_setOf_eq] at hU
    rcases hU with ⟨r, rpos, hr⟩
  -- Assume that $u$ is bounded by some $M > 0$
    rw [Metric.isBounded_iff_subset_ball 0] at u_bd
    rcases u_bd with ⟨M, hM⟩; simp only [Set.subset_def, Set.mem_range, Metric.mem_ball,
      dist_zero_right, forall_exists_index, forall_apply_eq_imp_iff] at hM
    have Mpos : 0 < M := by
      specialize hM 0; apply lt_of_le_of_lt _ hM; positivity
  -- Define $z$ to be the sequence $(r / (M + 1)) • u n$, prove that the norm of $z$ is less than $r$
    let z : ℕ → X := fun n => ((rc.ofReal r) / (rc.ofReal M + 1)) • u n
    have nm_z_lt : ∀ n, ‖z n‖ < r := by
      intro n; dsimp [z]; rw [norm_smul]
      by_cases h : u n = 0
      · norm_cast; simp only [h, norm_zero, mul_zero]
        exact rpos
      calc
        _ < r / (M + 1) * M := by
          norm_cast; rw [abs_eq_self.mpr]
          gcongr; apply hM; positivity
        _ < _ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀, mul_add_one]
          simp only [lt_add_iff_pos_right]; all_goals positivity
  -- Rewrite the compactness of $V$ to sequence compactness, then specialize it to $f ∘ z$
    apply IsCompact.isSeqCompact at hV; dsimp [IsSeqCompact] at hV
    have aux : ∀ n, (f ∘ z) n ∈ V := by
      intro n; simp; apply hUV; simp
      use z n; rw [and_comm]; constructor; rfl
      apply hr; apply nm_z_lt
  -- Unfold `hV` to get a converging subsequence $φ$ of $f ∘ z$, suppose the subsequence is converging to $y$
    specialize hV aux; rcases hV with ⟨y, ymem, ⟨φ, φ_mono, hy⟩⟩
  -- Use $((M + 1) / r) • y$ and the subsequence $y$ to fulfill the goal
    use rc.ofReal ((M + 1) / r) • y, φ; constructor; assumption
  -- Rewrite the limits in `hy` and in the goal to ε-δ forms, then finish the goal by computations
    simp only [Metric.tendsto_atTop, gt_iff_lt, ge_iff_le, Function.comp_apply, f_smul, dist_eq_norm, z] at hy
    simp only [Metric.tendsto_atTop, gt_iff_lt, ge_iff_le, Function.comp_apply, dist_eq_norm]
    intro ε εpos; specialize hy ((r / (M + 1)) * ε) (by positivity)
    rcases hy with ⟨N, hN⟩; use N; intro n nge
    specialize hN n nge; rw [← one_smul k y] at hN
    have : (1 : k) = r / (M + 1) * ((M + 1) / r) := by
      norm_cast; rw [div_mul_div_cancel₀, div_self]
      all_goals positivity
    nth_rw 2 [this] at hN; rw [mul_smul, ← smul_sub, norm_smul] at hN
    norm_cast at hN; rw [abs_eq_self.mpr] at hN
    by_cases h : f (u (φ n)) - rc.ofReal ((M + 1) / r) • y = 0
    · simp only [h, norm_zero, gt_iff_lt]; exact εpos
    rw [mul_lt_mul_left] at hN; exact hN
    all_goals positivity
-- Conversely, assume for all bounded sequence $u_i$ in X, there exists a convergent subsequence of $f (u_i)$ in $Y$, we need to show $f$ is a compact operator,
-- which is equivalent to finding a nhds of $0$ in $X$ whose image under $f$ is contained in some compact set $K$
  intro hf; rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
-- We fulfill the goal with the open unit ball in $X$
  use Metric.ball 0 1; constructor
  · apply Metric.ball_mem_nhds; norm_num
-- We will show that the closure of its image under $f$ is compact
  use closure (f '' Metric.ball 0 1); rw [and_comm]; constructor
  · apply subset_closure
-- Rewrite the compactness to sequence compactness, then unfold the definition of sequence compactness
  apply IsSeqCompact.isCompact; dsimp [IsSeqCompact]
-- Take any sequence $x$ in $closure (f '' Metric.ball 0 1)$, we need to find a converging subsequence of $x$.
-- We first simplify the assumption `hx`
  intro x hx; simp only [Metric.mem_closure_iff, gt_iff_lt, Set.mem_image, Metric.mem_ball,
    dist_eq_norm, sub_zero, exists_exists_and_eq_and] at hx
  replace hx : ∀ (n : ℕ), ∃ a, ‖a‖ < 1 ∧ ‖x n - f a‖ < 1 / (n + 1) := by
    intro n; apply hx; positivity
-- Apply `choose` tactics on `hx` to get a sequence $y$ in $X$
  choose y hy using hx
-- Prove that $f ∘ y$ is bounded
  have y_bd : Bornology.IsBounded (Set.range y) := by
    rw [Metric.isBounded_iff_subset_ball 0]; use 1
    simp only [Set.subset_def, Set.mem_range, Metric.mem_ball, dist_zero_right, forall_exists_index,
      forall_apply_eq_imp_iff]
    rw [forall_and] at hy; exact hy.left
-- Specialize `hf` to $y$ to get a converging subsequence $φ$ of $f ∘ y$, suppose it is converging to $a$
  specialize hf y y_bd; rcases hf with ⟨a, φ, φ_mono, φ_lim⟩
-- Rewrite the limit `φ_lim` to ε-δ form
  rw [Metric.tendsto_atTop] at φ_lim
  simp only [gt_iff_lt, ge_iff_le, Function.comp_apply, dist_eq_norm] at φ_lim
-- Use $a$ to fulfill the goal and prove it is a member of $closure (f '' Metric.ball 0 1)$
  use a; constructor
  · rw [Metric.mem_closure_iff]; intro ε εpos
    simp only [Set.mem_image, Metric.mem_ball, dist_eq_norm, sub_zero, exists_exists_and_eq_and]
    specialize φ_lim ε εpos; rcases φ_lim with ⟨N, hN⟩
    specialize hN N (by rfl); rw [norm_sub_rev] at hN
    use y (φ N); exact ⟨(hy (φ N)).left, hN⟩
-- Use the subsequence $φ$ to fulfill the goal, then rewrite the limit goal to ε-δ form and finish it by computations
  use φ; constructor; assumption
  rw [Metric.tendsto_atTop]; intro ε εpos
  simp only [ge_iff_le, Function.comp_apply, dist_eq_norm]
  specialize φ_lim (ε/2) (by linarith); rcases φ_lim with ⟨M, hM⟩
  have φ_ge : ∀ n, n ≤ φ n := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.add_one_le_iff]; apply lt_of_le_of_lt ih
      simp [φ_mono.lt_iff_lt]
  use (⌊2 / ε - 1⌋₊ + 1) ⊔ M; intro n nge; calc
    _ = ‖x (φ n) - f (y (φ n)) + (f (y (φ n)) - a)‖ := by rw [sub_add_sub_cancel]
    _ ≤  _ := norm_add_le _ _
    _ < _ := by
      rw [show ε = ε / 2 + ε / 2 by ring]; apply add_lt_add
      · have := (hy (φ n)).right; apply lt_trans this
        rw [one_div_lt]; simp only [one_div, inv_div]; calc
          _ < (n : ℝ) + 1 := by
            by_cases 2 / ε < 1; linarith
            rw [← sub_lt_iff_lt_add, ← Nat.floor_lt]
            omega; linarith
          _ ≤ _ := by specialize φ_ge n; norm_cast; omega
        all_goals positivity
      apply hM; omega

-- The dual of a compact operator is compact
theorem isCompactOperator_dual {T : X →L[k] Y} (T_cptOp : IsCompactOperator T) :
    IsCompactOperator (fun f : NormedSpace.Dual k Y => f.comp T) := by
-- Prove that $T_dual$ has the required scalar multiplication property and rewrite the goal by the lemma `cptOp_iff_seq`
  set T_dual := fun f : NormedSpace.Dual k Y => f.comp T
  have T_dual_smul : ∀ r : k, ∀ y : NormedSpace.Dual k Y, T_dual (r • y) = r • T_dual y := by
    intros; ext; simp [T_dual]
  rw [isCompactOperator_iff_seq T_dual_smul]
-- Take any bounded sequence $y$ in $NormedSpace.Dual ℝ Y$, assume $y$ is bounded by some $r > 0$
  intro y y_bd; rw [Metric.isBounded_iff_subset_ball 0] at y_bd
  rcases y_bd with ⟨r, y_bd⟩; simp only [Set.subset_def, Set.mem_range, Metric.mem_ball,
    dist_zero_right, forall_exists_index, forall_apply_eq_imp_iff] at y_bd
  have rpos : 0 < r := by
    specialize y_bd 0; apply lt_of_le_of_lt _ y_bd
    positivity
-- Unfold the definition of the compact operator, we get a ball $Metric.ball 0 s$ in $X$ whose image under $T$ is contained in some compact set $K$ in $Y$
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact] at T_cptOp
  rcases T_cptOp with ⟨V, hV, ⟨K, K_cpt, hK⟩⟩; rw [Metric.mem_nhds_iff] at hV
-- Since $K$ is compact, we can assume that it is bounded by some $M > 0$
  rcases hV with ⟨s, spos, hs⟩; have K_bd := K_cpt.isBounded
  rw [Metric.isBounded_iff_subset_ball 0] at K_bd
  rcases K_bd with ⟨M, k_bd⟩; simp only [Set.subset_def, Metric.mem_ball, dist_zero_right,
    Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at k_bd hs hK
  have Mpos : 0 < M := by
    specialize hs 0 (by rw [norm_zero]; positivity); apply hK at hs
    simp only [map_zero] at hs; specialize k_bd _ hs
    simp only [norm_zero] at k_bd; exact k_bd
  rw [isCompact_iff_compactSpace] at K_cpt
-- Restricts $y$ to $K$, we get a sequence of continuous functions on $K$ and denote it by $F_i$
  let F : ℕ → C(K, k) := fun n => ContinuousMap.mk ((y n) ∘ Subtype.val)
-- $F$ naturally induces a sequence of bounded continuous functions on $K$, denote it by $A$
  let A := BoundedContinuousFunction.mkOfCompact '' Set.range F
-- Apply Arzela-Ascoli theorem to show that the closure of $A$ is compact
  have F_conv : IsCompact (closure A) := by
    apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall 0 (r * M))
    · apply isCompact_closedBall
    -- Prove that the functions in the sequence are pointwisely bounded
    · rintro f ⟨w, wmem⟩ fmem
      simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, A] at fmem
      rcases fmem with ⟨n, hn⟩; rw [BoundedContinuousFunction.ext_iff] at hn
      simp only [BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
        Function.comp_apply, Subtype.forall, F] at hn
      simp only [← hn, Metric.mem_closedBall, dist_zero_right]
      specialize y_bd n; apply le_of_lt at y_bd
      rw [ContinuousLinearMap.opNorm_le_iff] at y_bd
      specialize y_bd w; apply le_trans y_bd
      gcongr; apply le_of_lt
      exact k_bd _ wmem; positivity
  -- Prove that the functions in the sequence are equicontinuous
    rintro ⟨x, xmem⟩; rw [Metric.equicontinuousAt_iff]
    intro ε εpos; simp only [gt_iff_lt, Subtype.dist_eq, dist_eq_norm,
      Subtype.forall, Set.mem_image, Set.mem_range, exists_exists_eq_and, forall_exists_index,
      forall_apply_eq_imp_iff, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
      Function.comp_apply, A, F]
    use ε / r; constructor; positivity
    intro a amem hax n; specialize y_bd n
    apply le_of_lt at y_bd; rw [ContinuousLinearMap.opNorm_le_iff] at y_bd
    specialize y_bd (x - a); rw [norm_sub_rev] at y_bd
    rw [← (y n).map_sub]; apply lt_of_le_of_lt y_bd
    by_cases h : a - x = 0
    · simp only [h, norm_zero, mul_zero]; exact εpos
    calc
      _ < r * (ε / r) := by gcongr
      _ = _ := by apply mul_div_cancel₀; positivity
    positivity
-- Rewrite the compactness to sequence compactness and specialize it to $F$
  apply IsCompact.isSeqCompact at F_conv; rw [IsSeqCompact] at F_conv
  have aux : ∀ n, BoundedContinuousFunction.mkOfCompact (F n) ∈ closure A := by
    intro n; apply subset_closure; simp [A]
  specialize F_conv aux; rw [exists_comm]; simp only [exists_and_left]
-- We get a converging subsequence $φ$ of the sequence of functions $F$, rewrite the convergence to a Cauchy sequence form
  rcases F_conv with ⟨f, fmem, ⟨φ, φ_mono, hφ⟩⟩
  replace hφ := hφ.cauchySeq
-- Rewrite the Cauchy sequence condition to an ε-δ form
  simp only [Metric.cauchySeq_iff, gt_iff_lt, ge_iff_le, Function.comp_apply, dist_eq_norm] at hφ
-- Use the subsequence $φ$ to fulfill the goal
  use φ; constructor; assumption
-- Since $NormedSpace.Dual ℝ X$ is complete, we only need to show the sequence in question is a Cauchy sequence
  apply cauchySeq_tendsto_of_complete
  simp only [Metric.cauchySeq_iff, gt_iff_lt, ge_iff_le, Function.comp_apply, dist_eq_norm]
-- Take any $ε > 0$, it suffices to prove the goal in a non-strict inequality form
  intro ε εpos; suffices : ∃ N, ∀ (m : ℕ), N ≤ m → ∀ (n : ℕ), N ≤ n →
  ‖T_dual (y (φ m)) - T_dual (y (φ n))‖ ≤ ε / 2
  · rcases this with ⟨N, hN⟩; use N; intros; calc
      _ ≤ ε / 2 := by apply hN; all_goals assumption
      _ < _ := by linarith only [εpos]
-- Use the property `ContinuousLinearMap.opNorm_le_iff` of operator norm to simplify the inequality
  simp only [ContinuousLinearMap.opNorm_le_iff (show 0 ≤ ε / 2 by positivity),
    ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_comp', Pi.sub_apply, Function.comp_apply,
    T_dual]
-- Specialize `hφ` to a suitable choice of the parameter and simplify it by `BoundedContinuousFunction.norm_lt_iff_of_compact`
  specialize hφ (s * ε / 6) (by positivity)
  simp only [BoundedContinuousFunction.norm_lt_iff_of_compact (show 0 < s * ε / 6 by positivity),
    BoundedContinuousFunction.coe_sub, Pi.sub_apply, BoundedContinuousFunction.mkOfCompact_apply,
    ContinuousMap.coe_mk, Function.comp_apply, Subtype.forall, F] at hφ
-- Extend `hφ` with $N$ and fulfill the goal with $N$, take any $x$ in $X$
  rcases hφ with ⟨N, hN⟩; use N; intro m mge n nge x
-- If $x$ is zero, the goal is trivial
  by_cases hx : x = 0; simp [hx]
-- If $x$ is nonzero, specialize `hN` to $T ((s / (2 * ‖x‖)) • x)$
  rw [← ne_eq, ← norm_pos_iff] at hx; specialize hN m mge n nge (T (rc.ofReal (s / (2 * ‖x‖)) • x))
  have : T (rc.ofReal (s / (2 * ‖x‖)) • x) ∈ K := by
    apply hK; apply hs; rw [norm_smul]; norm_cast
    rw [abs_eq_self.mpr, div_mul, mul_div_cancel_right₀]
    linarith only [spos]; all_goals positivity
-- Simplify `hN` and the goal follows
  specialize hN this; simp only [map_smul, smul_eq_mul] at hN
  rw [← mul_sub, norm_mul] at hN; norm_cast at hN
  rw [abs_eq_self.mpr, ← lt_div_iff₀'] at hN
  apply le_of_lt; apply lt_trans hN; rw [← sub_pos]
  field_simp; rw [← sub_pos]; ring_nf
  all_goals positivity
