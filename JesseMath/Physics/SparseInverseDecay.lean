import JesseMath.Linter.AxiomAudit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

/-!
# Decay of the inverse of a sparse positive matrix

A symmetric real matrix with spectrum in `[lo, hi]`, supported on the edges of a graph, has an inverse
whose entries decay with ratio `1 - lo / hi` in graph distance. The proof expands the inverse as a
Neumann series in `1 - (1 / hi) • H`. This is a general linear algebra statement with no lattice in it.
`YangMillsForestSliceHessian` applies it to the forest-slice curl form.
-/

open BigOperators

namespace JesseMath.Physics.SparseInverseDecay


open Matrix Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Neumann step of `H` at scale `hi`. -/
noncomputable def dampedStep (H : Matrix ι ι ℝ) (hi : ℝ) : Matrix ι ι ℝ :=
  1 - (1 / hi) • H

omit [DecidableEq ι] in
theorem dotProduct_self_eq (x : ι → ℝ) : x ⬝ᵥ x = ∑ i, x i ^ 2 := by
  simp [dotProduct, pow_two]

omit [DecidableEq ι] in
theorem quadratic_eq (H : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ (H *ᵥ x) = ∑ i, ∑ j, x i * H i j * x j := by
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

omit [DecidableEq ι] in
theorem dotProduct_self_nonneg' (x : ι → ℝ) : 0 ≤ x ⬝ᵥ x := by
  rw [dotProduct_self_eq]
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)

omit [DecidableEq ι] in
theorem symm_form (M : Matrix ι ι ℝ) (hM : M.IsSymm) (x y : ι → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, dotProduct_comm]
  congr 1
  conv_lhs => rw [← hM]
  rw [Matrix.vecMul_transpose]

omit [DecidableEq ι] in
/-- A symmetric form between `0` and `q` times the identity has polar bound `q`. -/
theorem polar_bound (M : Matrix ι ι ℝ) (hM : M.IsSymm) {q : ℝ} (hq : 0 ≤ q)
    (h0 : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x))
    (h1 : ∀ x : ι → ℝ, x ⬝ᵥ (M *ᵥ x) ≤ q * (x ⬝ᵥ x)) (x y : ι → ℝ) :
    2 * (x ⬝ᵥ (M *ᵥ y)) ≤ q * (x ⬝ᵥ x + y ⬝ᵥ y) := by
  have hplus := h1 (x + y)
  have hminus := h0 (x - y)
  have hsquare := dotProduct_self_nonneg' (x - y)
  have hsym := symm_form M hM y x
  simp only [mulVec_add, mulVec_sub, add_dotProduct, dotProduct_add, sub_dotProduct,
    dotProduct_sub] at hplus hminus hsquare
  have hcomm : y ⬝ᵥ x = x ⬝ᵥ y := dotProduct_comm y x
  rw [hcomm] at hplus hsquare
  rw [hsym] at hplus hminus
  nlinarith [mul_nonneg hq hsquare]

omit [DecidableEq ι] in
/-- The form bounds give an operator bound in squared norm. -/
theorem normSq_mulVec_le (M : Matrix ι ι ℝ) (hM : M.IsSymm) {q : ℝ} (hq : 0 ≤ q)
    (h0 : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x))
    (h1 : ∀ x : ι → ℝ, x ⬝ᵥ (M *ᵥ x) ≤ q * (x ⬝ᵥ x)) (x : ι → ℝ) :
    (M *ᵥ x) ⬝ᵥ (M *ᵥ x) ≤ q ^ 2 * (x ⬝ᵥ x) := by
  have hscaled : ∀ t : ℝ, 2 * (t * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x))) ≤
      q * (x ⬝ᵥ x + t ^ 2 * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x))) := by
    intro t
    have h := polar_bound M hM hq h0 h1 x (t • (M *ᵥ x))
    rw [mulVec_smul, dotProduct_smul, symm_form M hM x (M *ᵥ x), smul_dotProduct,
      dotProduct_smul] at h
    simpa [smul_eq_mul, pow_two, mul_assoc] using h
  rcases hq.eq_or_lt with rfl | hq'
  · have h := hscaled 1
    have hnn := dotProduct_self_nonneg' (M *ᵥ x)
    nlinarith
  · have h := hscaled (1 / q)
    have hne : q ≠ 0 := hq'.ne'
    have hid : q * (x ⬝ᵥ x + (1 / q) ^ 2 * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x))) =
        q * (x ⬝ᵥ x) + (1 / q) * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x)) := by
      field_simp
    rw [hid] at h
    have h' : (1 / q) * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x)) ≤ q * (x ⬝ᵥ x) := by linarith
    have h'' := mul_le_mul_of_nonneg_left h' hq
    have hcancel : q * ((1 / q) * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x))) = (M *ᵥ x) ⬝ᵥ (M *ᵥ x) := by
      field_simp
    rw [hcancel] at h''
    nlinarith

theorem normSq_pow_mulVec_le (M : Matrix ι ι ℝ) (hM : M.IsSymm) {q : ℝ} (hq : 0 ≤ q)
    (h0 : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x))
    (h1 : ∀ x : ι → ℝ, x ⬝ᵥ (M *ᵥ x) ≤ q * (x ⬝ᵥ x)) (k : ℕ) (x : ι → ℝ) :
    ((M ^ k) *ᵥ x) ⬝ᵥ ((M ^ k) *ᵥ x) ≤ (q ^ k) ^ 2 * (x ⬝ᵥ x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec]
    have h := normSq_mulVec_le M hM hq h0 h1 ((M ^ k) *ᵥ x)
    have h' := mul_le_mul_of_nonneg_left ih (sq_nonneg q)
    calc _ ≤ _ := h
      _ ≤ _ := h'
      _ = _ := by ring

/-- Entries of `M ^ k` are bounded by `q ^ k`. -/
theorem abs_pow_entry_le (M : Matrix ι ι ℝ) (hM : M.IsSymm) {q : ℝ} (hq : 0 ≤ q)
    (h0 : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x))
    (h1 : ∀ x : ι → ℝ, x ⬝ᵥ (M *ᵥ x) ≤ q * (x ⬝ᵥ x)) (k : ℕ) (i j : ι) :
    |(M ^ k) i j| ≤ q ^ k := by
  have h := normSq_pow_mulVec_le M hM hq h0 h1 k (Pi.single j 1)
  have hunit : (Pi.single j (1 : ℝ) : ι → ℝ) ⬝ᵥ Pi.single j 1 = 1 := by simp
  rw [hunit, mul_one, dotProduct_self_eq] at h
  have hsingle : ((M ^ k) i j) ^ 2 ≤ ∑ l, (((M ^ k) *ᵥ Pi.single j (1 : ℝ)) l) ^ 2 := by
    have := Finset.single_le_sum (f := fun l => (((M ^ k) *ᵥ Pi.single j (1 : ℝ)) l) ^ 2)
      (fun l _ => sq_nonneg _) (Finset.mem_univ i)
    simpa using this
  exact abs_le_of_sq_le_sq (hsingle.trans h) (pow_nonneg hq k)

/-- A nonzero entry of `M ^ k` gives a walk of length at most `k`. -/
theorem exists_walk_of_pow_entry_ne_zero (G : SimpleGraph ι) (M : Matrix ι ι ℝ)
    (hsupp : ∀ i j, M i j ≠ 0 → i = j ∨ G.Adj i j) (k : ℕ) :
    ∀ i j, (M ^ k) i j ≠ 0 → ∃ p : G.Walk i j, p.length ≤ k := by
  induction k with
  | zero =>
    intro i j h
    have hij : i = j := by
      by_contra hne
      exact h (by simp [Matrix.one_apply_ne hne])
    subst hij
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    obtain ⟨p, hp⟩ := ih i l (left_ne_zero_of_mul hl)
    rcases hsupp l j (right_ne_zero_of_mul hl) with rfl | hadj
    · exact ⟨p, by omega⟩
    · refine ⟨p.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil), ?_⟩
      simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_nil]
      omega

/-- `M ^ k` vanishes on pairs at graph distance beyond `k`. -/
theorem pow_entry_eq_zero_of_lt_dist (G : SimpleGraph ι) (M : Matrix ι ι ℝ)
    (hsupp : ∀ i j, M i j ≠ 0 → i = j ∨ G.Adj i j) {k : ℕ} {i j : ι} (hk : k < G.dist i j) :
    (M ^ k) i j = 0 := by
  by_contra h
  obtain ⟨p, hp⟩ := exists_walk_of_pow_entry_ne_zero G M hsupp k i j h
  have := SimpleGraph.dist_le p
  omega

/-- `M ^ k` vanishes on pairs in different components. -/
theorem pow_entry_eq_zero_of_not_reachable (G : SimpleGraph ι) (M : Matrix ι ι ℝ)
    (hsupp : ∀ i j, M i j ≠ 0 → i = j ∨ G.Adj i j) {i j : ι} (hij : ¬ G.Reachable i j) (k : ℕ) :
    (M ^ k) i j = 0 := by
  by_contra h
  obtain ⟨p, -⟩ := exists_walk_of_pow_entry_ne_zero G M hsupp k i j h
  exact hij ⟨p⟩

/-- A partial sum that vanishes below `d` and is dominated by `q ^ k` is bounded by the tail. -/
theorem sum_abs_le_tail {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (a : ℕ → ℝ) (d : ℕ)
    (h0 : ∀ k, k < d → a k = 0) (h1 : ∀ k, |a k| ≤ q ^ k) (N : ℕ) :
    ∑ k ∈ range N, |a k| ≤ q ^ d / (1 - q) := by
  have hpos : 0 < 1 - q := by linarith
  have key : ∀ n, (∑ k ∈ range n, |a k|) * (1 - q) ≤ q ^ d - q ^ max d n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, add_mul]
      by_cases hn : n < d
      · rw [h0 n hn, abs_zero, zero_mul, add_zero, max_eq_left (by omega)]
        rwa [max_eq_left hn.le] at ih
      · have hdn : d ≤ n := by omega
        rw [max_eq_right (by omega), pow_succ]
        rw [max_eq_right hdn] at ih
        have hstep := mul_le_mul_of_nonneg_right (h1 n) hpos.le
        nlinarith
  rw [le_div_iff₀ hpos]
  have hnn : 0 ≤ q ^ max d N := pow_nonneg hq _
  linarith [key N]

/-- The Neumann expansion with its remainder, entry by entry. -/
theorem inv_entry_expansion (H : Matrix ι ι ℝ) (hdet : IsUnit H.det) (hi : ℝ) (N : ℕ) (i j : ι) :
    H⁻¹ i j = (H⁻¹ * dampedStep H hi ^ N) i j +
      (1 / hi) * ∑ k ∈ range N, (dampedStep H hi ^ k) i j := by
  have hgeom : (1 - dampedStep H hi) * ∑ k ∈ range N, dampedStep H hi ^ k =
      1 - dampedStep H hi ^ N := mul_neg_geom_sum _ _
  have hone : 1 - dampedStep H hi = (1 / hi) • H := by simp [dampedStep]
  rw [hone, Matrix.smul_mul] at hgeom
  have hmul := congrArg (fun A => H⁻¹ * A) hgeom
  simp only [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul H hdet, Matrix.one_mul] at hmul
  have hentry := congrFun (congrFun hmul i) j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.sum_apply, smul_eq_mul] at hentry
  linarith

/-- The decay estimate from vanishing of the first `d` powers. -/
theorem abs_inv_entry_le (H : Matrix ι ι ℝ) (hdet : IsUnit H.det) {lo hi : ℝ} (hlo : 0 < lo)
    (hlohi : lo ≤ hi)
    (hbound : ∀ k i j, |(dampedStep H hi ^ k) i j| ≤ (1 - lo / hi) ^ k) (i j : ι) (d : ℕ)
    (hvanish : ∀ k, k < d → (dampedStep H hi ^ k) i j = 0) :
    |H⁻¹ i j| ≤ (1 / lo) * (1 - lo / hi) ^ d := by
  have hhi : 0 < hi := hlo.trans_le hlohi
  set q : ℝ := 1 - lo / hi with hqdef
  have hq0 : 0 ≤ q := by
    have : lo / hi ≤ 1 := (div_le_one hhi).2 hlohi
    linarith
  have hq1 : q < 1 := by
    have : 0 < lo / hi := div_pos hlo hhi
    linarith
  set C : ℝ := ∑ l, |H⁻¹ i l| with hC
  have hfinite : ∀ N : ℕ, |H⁻¹ i j| ≤ C * q ^ N + (1 / lo) * q ^ d := by
    intro N
    rw [inv_entry_expansion H hdet hi N i j]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Matrix.mul_apply, hC, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hbound N l j) (abs_nonneg _)
    · have hsum := sum_abs_le_tail hq0 hq1 (fun k => (dampedStep H hi ^ k) i j) d hvanish
        (fun k => hbound k i j) N
      have hrem : (1 / hi) * (q ^ d / (1 - q)) = (1 / lo) * q ^ d := by
        rw [hqdef]
        have hne : hi ≠ 0 := hhi.ne'
        have hne' : lo ≠ 0 := hlo.ne'
        have h1q : 1 - (1 - lo / hi) = lo / hi := by ring
        rw [h1q]
        field_simp
      rw [abs_mul, abs_of_pos (one_div_pos.2 hhi), ← hrem]
      refine mul_le_mul_of_nonneg_left ?_ (one_div_pos.2 hhi).le
      exact (Finset.abs_sum_le_sum_abs _ _).trans hsum
  have hlim : Tendsto (fun N : ℕ => C * q ^ N + (1 / lo) * q ^ d) atTop
      (𝓝 (C * 0 + (1 / lo) * q ^ d)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C).add_const _
  have := ge_of_tendsto' hlim hfinite
  simpa using this

/-- Invertibility from the lower form bound. -/
theorem isUnit_det_of_lower (H : Matrix ι ι ℝ) {lo : ℝ} (hlo : 0 < lo)
    (hlower : ∀ x : ι → ℝ, lo * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, x i * H i j * x j) :
    IsUnit H.det := by
  rw [isUnit_iff_ne_zero]
  intro hzero
  obtain ⟨v, hv, hHv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hzero
  have h := hlower v
  rw [← quadratic_eq, hHv, dotProduct_zero, ← dotProduct_self_eq] at h
  have hnn := dotProduct_self_nonneg' v
  have hzero' : v ⬝ᵥ v = 0 := by nlinarith
  rw [dotProduct_self_eq, Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (v i)] at hzero'
  exact hv (funext fun i => pow_eq_zero_iff (two_ne_zero) |>.1 (hzero' i (Finset.mem_univ i)))

/-- Geometric decay of the inverse of a positive matrix supported on a graph. -/
theorem inverse_entry_decay (G : SimpleGraph ι) (H : Matrix ι ι ℝ) {lo hi : ℝ}
    (hsymm : H.IsSymm) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hlower : ∀ x : ι → ℝ, lo * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, x i * H i j * x j)
    (hupper : ∀ x : ι → ℝ, ∑ i, ∑ j, x i * H i j * x j ≤ hi * ∑ i, x i ^ 2)
    (hsupp : ∀ i j, H i j ≠ 0 → i = j ∨ G.Adj i j) :
    IsUnit H.det ∧
      (∀ i j, |H⁻¹ i j| ≤ (1 / lo) * (1 - lo / hi) ^ G.dist i j) ∧
      ∀ i j, ¬ G.Reachable i j → H⁻¹ i j = 0 := by
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hdet := isUnit_det_of_lower H hlo hlower
  set M := dampedStep H hi with hMdef
  set q : ℝ := 1 - lo / hi with hqdef
  have hq0 : 0 ≤ q := by
    have : lo / hi ≤ 1 := (div_le_one hhi).2 hlohi
    linarith
  have hq1 : q < 1 := by
    have : 0 < lo / hi := div_pos hlo hhi
    linarith
  have hMsymm : M.IsSymm := by
    change (dampedStep H hi)ᵀ = dampedStep H hi
    have hH : Hᵀ = H := hsymm
    simp [dampedStep, Matrix.transpose_sub, Matrix.transpose_smul, hH]
  have hform : ∀ x : ι → ℝ, x ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ x - (1 / hi) * (x ⬝ᵥ (H *ᵥ x)) := by
    intro x
    simp [hMdef, dampedStep, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec]
  have h0 : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
    intro x
    have hu := hupper x
    rw [← quadratic_eq, ← dotProduct_self_eq] at hu
    rw [hform]
    have hu' := mul_le_mul_of_nonneg_left hu (one_div_pos.2 hhi).le
    have hc : (1 / hi) * (hi * (x ⬝ᵥ x)) = x ⬝ᵥ x := by field_simp
    linarith
  have h1 : ∀ x : ι → ℝ, x ⬝ᵥ (M *ᵥ x) ≤ q * (x ⬝ᵥ x) := by
    intro x
    have hl := hlower x
    rw [← quadratic_eq, ← dotProduct_self_eq] at hl
    rw [hform]
    have hl' := mul_le_mul_of_nonneg_left hl (one_div_pos.2 hhi).le
    have hc : (1 / hi) * (lo * (x ⬝ᵥ x)) = (lo / hi) * (x ⬝ᵥ x) := by ring
    rw [hqdef]
    linarith
  have hbound : ∀ k i j, |(M ^ k) i j| ≤ q ^ k := abs_pow_entry_le M hMsymm hq0 h0 h1
  have hMsupp : ∀ i j, M i j ≠ 0 → i = j ∨ G.Adj i j := by
    intro i j hij
    by_cases heq : i = j
    · exact Or.inl heq
    · refine hsupp i j fun hzero => hij ?_
      simp [hMdef, dampedStep, Matrix.sub_apply, Matrix.one_apply_ne heq, hzero]
  refine ⟨hdet, ?_, ?_⟩
  · intro i j
    exact abs_inv_entry_le H hdet hlo hlohi hbound i j (G.dist i j)
      fun k hk => pow_entry_eq_zero_of_lt_dist G M hMsupp hk
  · intro i j hij
    have hall : ∀ d : ℕ, |H⁻¹ i j| ≤ (1 / lo) * q ^ d := fun d =>
      abs_inv_entry_le H hdet hlo hlohi hbound i j d
        fun k _ => pow_entry_eq_zero_of_not_reachable G M hMsupp hij k
    have hlim : Tendsto (fun d : ℕ => (1 / lo) * q ^ d) atTop (𝓝 ((1 / lo) * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul _
    have hle := ge_of_tendsto' hlim hall
    rw [mul_zero] at hle
    exact abs_eq_zero.1 (le_antisymm hle (abs_nonneg _))

/-- Invertibility, the decay bound and vanishing across components for a positive multiple of `H`. -/
theorem inverse_entry_decay_smul (G : SimpleGraph ι) (H : Matrix ι ι ℝ) {lo hi β : ℝ}
    (hsymm : H.IsSymm) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hlower : ∀ x : ι → ℝ, lo * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, x i * H i j * x j)
    (hupper : ∀ x : ι → ℝ, ∑ i, ∑ j, x i * H i j * x j ≤ hi * ∑ i, x i ^ 2)
    (hsupp : ∀ i j, H i j ≠ 0 → i = j ∨ G.Adj i j) (hβ : 0 < β) :
    IsUnit (β • H).det ∧
      (∀ i j, |(β • H)⁻¹ i j| ≤ (1 / (β * lo)) * (1 - lo / hi) ^ G.dist i j) ∧
      ∀ i j, ¬ G.Reachable i j → (β • H)⁻¹ i j = 0 := by
  obtain ⟨hdet, hdecay, hzero⟩ := inverse_entry_decay G H hsymm hlo hlohi hlower hupper hsupp
  have hinv : (β • H)⁻¹ = β⁻¹ • H⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_nonsing_inv H hdet, smul_smul,
      mul_inv_cancel₀ hβ.ne', one_smul]
  refine ⟨?_, fun i j => ?_, fun i j hij => ?_⟩
  · rw [Matrix.det_smul]
    exact (IsUnit.mk0 _ (pow_ne_zero _ hβ.ne')).mul hdet
  · rw [hinv, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 hβ)]
    have h := mul_le_mul_of_nonneg_left (hdecay i j) (inv_pos.2 hβ).le
    have hc : β⁻¹ * ((1 / lo) * (1 - lo / hi) ^ G.dist i j) =
        (1 / (β * lo)) * (1 - lo / hi) ^ G.dist i j := by
      field_simp
    rwa [hc] at h
  · rw [hinv, Matrix.smul_apply, hzero i j hij, smul_zero]

end JesseMath.Physics.SparseInverseDecay

#assert_zfc_axioms
