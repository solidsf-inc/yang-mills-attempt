import JesseMath.Linter.AxiomAudit
import JesseMath.Unified.SchurFeshbachWaveletComb
import JesseMath.Unified.HamiltonianScaleComb
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite correlator forms under an existing common limit

This module proves closedness of finite reflection positivity and covariance,
and preservation of a uniformly positive observable, for one approximating
complex kernel. It does not construct a limit, identify a Wilson measure, or
establish the full Osterwalder--Schrader axioms for a continuum field theory.
-/

open Filter
open scoped Topology BigOperators

namespace JesseMath.Physics.YangMillsContinuumLimitBridge

variable {α : Type*}

/-- The finite reflected Gram form of test labels and complex coefficients. -/
noncomputable def reflectedGramForm (C : α → α → ℂ) (θ : α → α)
    {d : ℕ} (f : Fin d → α) (c : Fin d → ℂ) : ℂ :=
  ∑ i, ∑ j, star (c i) * c j * C (θ (f i)) (f j)

/-- Both reality and nonnegativity are required, on admissible test labels. -/
def FiniteReflectionPositive (C : α → α → ℂ) (θ : α → α) (admissible : Set α) : Prop :=
  ∀ (d : ℕ) (f : Fin d → α), (∀ i, f i ∈ admissible) → ∀ c : Fin d → ℂ,
    (reflectedGramForm C θ f c).im = 0 ∧ 0 ≤ (reflectedGramForm C θ f c).re

/-- Entrywise convergence suffices for every fixed finite test combination. -/
theorem reflectedGramForm_tendsto (C : ℕ → α → α → ℂ) (C_limit : α → α → ℂ)
    (hlimit : ∀ x y, Tendsto (fun n => C n x y) atTop (𝓝 (C_limit x y)))
    (θ : α → α) {d : ℕ} (f : Fin d → α) (c : Fin d → ℂ) :
    Tendsto (fun n => reflectedGramForm (C n) θ f c) atTop
      (𝓝 (reflectedGramForm C_limit θ f c)) := by
  unfold reflectedGramForm
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact tendsto_const_nhds.mul (hlimit (θ (f i)) (f j))

/-- Reflection positivity is closed under the same pointwise kernel limit. -/
theorem reflection_positivity_survives_limit (C : ℕ → α → α → ℂ) (C_limit : α → α → ℂ)
    (hlimit : ∀ x y, Tendsto (fun n => C n x y) atTop (𝓝 (C_limit x y)))
    (θ : α → α) (admissible : Set α)
    (hpositive : ∀ n, FiniteReflectionPositive (C n) θ admissible) :
    FiniteReflectionPositive C_limit θ admissible := by
  intro d f hf c
  have hform := reflectedGramForm_tendsto C C_limit hlimit θ f c
  constructor
  · have him := Complex.continuous_im.continuousAt.tendsto.comp hform
    have hzero : Tendsto (fun n => (reflectedGramForm (C n) θ f c).im) atTop (𝓝 0) := by
      simpa only [(show (fun n => (reflectedGramForm (C n) θ f c).im) =
        (fun _ => 0) from funext fun n => (hpositive n d f hf c).1)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique him hzero
  · exact ge_of_tendsto' (Complex.continuous_re.continuousAt.tendsto.comp hform)
      (fun n => (hpositive n d f hf c).2)

/-- Vanishing symmetry defects are sufficient; no exact cutoff symmetry is needed. -/
theorem covariance_survives_vanishing_defect (C : ℕ → α → α → ℂ) (C_limit : α → α → ℂ)
    (hlimit : ∀ x y, Tendsto (fun n => C n x y) atTop (𝓝 (C_limit x y)))
    (T : α → α)
    (hdefect : ∀ x y, Tendsto (fun n => C n (T x) (T y) - C n x y) atTop (𝓝 0)) :
    ∀ x y, C_limit (T x) (T y) = C_limit x y := by
  intro x y
  exact sub_eq_zero.mp (tendsto_nhds_unique
    ((hlimit (T x) (T y)).sub (hlimit x y)) (hdefect x y))

/-- Exact covariance at each cutoff is a special case of vanishing defects. -/
theorem covariance_survives_limit (C : ℕ → α → α → ℂ) (C_limit : α → α → ℂ)
    (hlimit : ∀ x y, Tendsto (fun n => C n x y) atTop (𝓝 (C_limit x y)))
    (T : α → α) (hcov : ∀ n x y, C n (T x) (T y) = C n x y) :
    ∀ x y, C_limit (T x) (T y) = C_limit x y := by
  apply covariance_survives_vanishing_defect C C_limit hlimit T
  intro x y
  simpa only [hcov, sub_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

/-- A cutoff-independent lower bound protects one observable from collapsing. -/
theorem uniform_positive_form_survives_limit (C : ℕ → α → α → ℂ) (C_limit : α → α → ℂ)
    (hlimit : ∀ x y, Tendsto (fun n => C n x y) atTop (𝓝 (C_limit x y)))
    (θ : α → α) {d : ℕ} (f : Fin d → α) (c : Fin d → ℂ)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ n, ε ≤ (reflectedGramForm (C n) θ f c).re) :
    ε ≤ (reflectedGramForm C_limit θ f c).re ∧ 0 < (reflectedGramForm C_limit θ f c).re := by
  have hbound := ge_of_tendsto'
    (Complex.continuous_re.continuousAt.tendsto.comp
      (reflectedGramForm_tendsto C C_limit hlimit θ f c)) hmargin
  exact ⟨hbound, lt_of_lt_of_le hε hbound⟩

/-- All three conclusions concern one common limiting correlator, not separate witnesses. -/
theorem common_correlator_limit_bridge (C : ℕ → α → α → ℂ) (C_limit : α → α → ℂ)
    (hlimit : ∀ x y, Tendsto (fun n => C n x y) atTop (𝓝 (C_limit x y)))
    (θ T : α → α) (admissible : Set α)
    (hpositive : ∀ n, FiniteReflectionPositive (C n) θ admissible)
    (hdefect : ∀ x y, Tendsto (fun n => C n (T x) (T y) - C n x y) atTop (𝓝 0))
    {d : ℕ} (f : Fin d → α) (hf : ∀ i, f i ∈ admissible) (c : Fin d → ℂ)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ n, ε ≤ (reflectedGramForm (C n) θ f c).re) :
    FiniteReflectionPositive C_limit θ admissible ∧
      (∀ x y, C_limit (T x) (T y) = C_limit x y) ∧
      (reflectedGramForm C_limit θ f c).im = 0 ∧
      ε ≤ (reflectedGramForm C_limit θ f c).re ∧
      0 < (reflectedGramForm C_limit θ f c).re := by
  have hpos := reflection_positivity_survives_limit C C_limit hlimit θ admissible hpositive
  exact ⟨hpos, covariance_survives_vanishing_defect C C_limit hlimit T hdefect,
    (hpos d f hf c).1, uniform_positive_form_survives_limit C C_limit hlimit θ f c ε hε hmargin⟩

/-- A one-label correlator whose nonzero observable vanishes in the limit. -/
noncomputable def vanishingCorrelator (n : ℕ) (_ _ : Unit) : ℂ :=
  (((1 / 2 : ℝ) ^ n) : ℂ)

theorem vanishingCorrelator_form (n : ℕ) :
    reflectedGramForm (vanishingCorrelator n) id
      (fun _ : Fin 1 => ()) (fun _ => 1) = (((1 / 2 : ℝ) ^ n) : ℂ) := by
  simp [reflectedGramForm, vanishingCorrelator]

theorem vanishingCorrelator_limit (x y : Unit) :
    Tendsto (fun n => vanishingCorrelator n x y) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [vanishingCorrelator, Function.comp_def, Complex.ofReal_zero, Complex.ofReal_pow] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp h

/-- Strict positivity at every cutoff does not preserve a nonzero limit observable. -/
theorem pointwise_nontriviality_can_collapse :
    (∀ n, 0 < (reflectedGramForm (vanishingCorrelator n) id
      (fun _ : Fin 1 => ()) (fun _ => 1)).re) ∧
    (reflectedGramForm (fun _ _ : Unit => 0) id
      (fun _ : Fin 1 => ()) (fun _ => 1)).re = 0 ∧
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ n, ε ≤ (reflectedGramForm (vanishingCorrelator n) id
      (fun _ : Fin 1 => ()) (fun _ => 1)).re := by
  constructor
  · intro n
    rw [vanishingCorrelator_form]
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using
      (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
  constructor
  · simp [reflectedGramForm]
  · rintro ⟨ε, hε, hmargin⟩
    have hbound := (uniform_positive_form_survives_limit vanishingCorrelator
      (fun _ _ : Unit => 0) vanishingCorrelator_limit id
      (fun _ : Fin 1 => ()) (fun _ => 1) ε hε hmargin).1
    have : ε ≤ 0 := by simpa [reflectedGramForm] using hbound
    exact (not_lt_of_ge this) hε

/-- Single-exponential Euclidean time-reflected kernel `S0 * exp(-Delta * (t1 + t2))`. -/
noncomputable def exponentialTimeReflectedKernel (S0 Delta t1 t2 : ℝ) : ℝ :=
  S0 * Real.exp (-Delta * (t1 + t2))

/-- Exact rank-one square factorization of the finite reflected Gram form for a single-exponential kernel. -/
theorem exponentialTimeReflectedKernel_gram_eq_sq (S0 Delta : ℝ) {m : ℕ} (t c : Fin m → ℝ) :
    (∑ i : Fin m, ∑ j : Fin m, c i * c j * exponentialTimeReflectedKernel S0 Delta (t i) (t j)) =
      S0 * (∑ i : Fin m, c i * Real.exp (-Delta * t i)) ^ 2 := by
  calc
    (∑ i : Fin m, ∑ j : Fin m, c i * c j * exponentialTimeReflectedKernel S0 Delta (t i) (t j))
      = ∑ i : Fin m, ∑ j : Fin m,
          S0 * ((c i * Real.exp (-Delta * t i)) * (c j * Real.exp (-Delta * t j))) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        unfold exponentialTimeReflectedKernel
        have hadd : -Delta * (t i + t j) = -Delta * t i + -Delta * t j := by ring
        rw [hadd, Real.exp_add]
        ring
    _ = S0 * (∑ i : Fin m, c i * Real.exp (-Delta * t i)) ^ 2 := by
        rw [sq, Finset.sum_mul]
        simp only [Finset.mul_sum]

/-- Nonnegativity of the finite reflected Gram form for a single-exponential kernel with `0 ≤ S0`. -/
theorem exponentialTimeReflectedKernel_gram_nonneg {S0 : ℝ} (hS0 : 0 ≤ S0) (Delta : ℝ)
    {m : ℕ} (t c : Fin m → ℝ) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, c i * c j * exponentialTimeReflectedKernel S0 Delta (t i) (t j) := by
  rw [exponentialTimeReflectedKernel_gram_eq_sq]
  exact mul_nonneg hS0 (sq_nonneg _)

/-- Gaussian time-reflected kernel `exp(-2 * (t1 + t2)^2)`, used as a negative control against reflection positivity. -/
noncomputable def gaussianTimeReflectedKernel (t1 t2 : ℝ) : ℝ :=
  Real.exp (-2 * (t1 + t2) ^ 2)

/-- Explicit two-point witness showing that the Gaussian kernel violates reflection positivity at `t1 = 1, t2 = 2`. -/
theorem gaussianTimeReflectedKernel_twoPoint_negative_witness :
    let c1 := Real.exp (-10)
    let c2 := (-1 : ℝ)
    c1 * c1 * gaussianTimeReflectedKernel 1 1 +
      2 * c1 * c2 * gaussianTimeReflectedKernel 1 2 +
      c2 * c2 * gaussianTimeReflectedKernel 2 2 =
        Real.exp (-32) - Real.exp (-28) ∧
    Real.exp (-32) - Real.exp (-28) < 0 := by
  dsimp [gaussianTimeReflectedKernel]
  have h1 : Real.exp (-10) * Real.exp (-10) * Real.exp (-2 * (1 + 1) ^ 2) = Real.exp (-28) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    norm_num
  have h2 : 2 * Real.exp (-10) * (-1 : ℝ) * Real.exp (-2 * (1 + 2) ^ 2) = -2 * Real.exp (-28) := by
    calc
      2 * Real.exp (-10) * (-1 : ℝ) * Real.exp (-2 * (1 + 2) ^ 2)
        = -2 * (Real.exp (-10) * Real.exp (-2 * (1 + 2) ^ 2)) := by ring
      _ = -2 * Real.exp (-28) := by
        rw [← Real.exp_add]
        congr 2
        norm_num
  have h3 : (-1 : ℝ) * (-1 : ℝ) * Real.exp (-2 * (2 + 2) ^ 2) = Real.exp (-32) := by
    have hexp : (-2 : ℝ) * (2 + 2) ^ 2 = -32 := by norm_num
    rw [hexp]
    ring
  constructor
  · linarith
  · have hlt : Real.exp (-32) < Real.exp (-28) := Real.exp_lt_exp.mpr (by norm_num)
    linarith

/-- Full unsubtracted two-point time function `v0^2 + S0 * exp(-Delta * t)` with vacuum floor `v0^2`. -/
noncomputable def fullClusterTwoPointTimeFunction (v0 S0 Delta t : ℝ) : ℝ :=
  v0 ^ 2 + S0 * Real.exp (-Delta * t)

/-- As Euclidean time `t → ∞`, the full two-point function converges to the squared vacuum expectation `v0^2`. -/
theorem fullClusterTwoPointTimeFunction_tendsto_vacuum_sq
    (v0 S0 : ℝ) {Delta : ℝ} (hDelta : 0 < Delta) :
    Tendsto (fun t : ℝ => fullClusterTwoPointTimeFunction v0 S0 Delta t) atTop (𝓝 (v0 ^ 2)) := by
  unfold fullClusterTwoPointTimeFunction
  have hlin : Tendsto (fun t : ℝ => -Delta * t) atTop atBot := by
    have hmul : Tendsto (fun t : ℝ => Delta * t) atTop atTop :=
      Tendsto.const_mul_atTop hDelta tendsto_id
    have hneg : Tendsto (fun t : ℝ => -(Delta * t)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hmul
    simpa only [Function.comp_def, neg_mul] using hneg
  have hexp : Tendsto (fun t : ℝ => Real.exp (-Delta * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hterm : Tendsto (fun t : ℝ => v0 ^ 2 + S0 * Real.exp (-Delta * t)) atTop
      (𝓝 (v0 ^ 2 + S0 * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hexp)
  simpa only [mul_zero, add_zero] using hterm

/-- Full unsubtracted rank-two time-reflected kernel `v0^2 + S0 * exp(-Delta * (t1 + t2))`
combining the disconnected vacuum floor `v0^2` and the connected exponential decay `S0 * exp(-Delta * (t1 + t2))`. -/
noncomputable def rankTwoClusterReflectedKernel (v0 S0 Delta t1 t2 : ℝ) : ℝ :=
  v0 ^ 2 + S0 * Real.exp (-Delta * (t1 + t2))

/-- Exact rank-two sum-of-squares decomposition of the finite reflected Gram form for
`rankTwoClusterReflectedKernel`, and its unconditional nonnegativity for `0 ≤ S0`. -/
theorem rankTwoClusterReflectedKernel_gram_eq_sum_sq_and_nonneg
    (v0 : ℝ) {S0 : ℝ} (hS0 : 0 ≤ S0) (Delta : ℝ) {m : ℕ} (t c : Fin m → ℝ) :
    (∑ i : Fin m, ∑ j : Fin m, c i * c j * rankTwoClusterReflectedKernel v0 S0 Delta (t i) (t j)) =
      v0 ^ 2 * (∑ i : Fin m, c i) ^ 2 +
        S0 * (∑ i : Fin m, c i * Real.exp (-Delta * t i)) ^ 2 ∧
    0 ≤ ∑ i : Fin m, ∑ j : Fin m,
      c i * c j * rankTwoClusterReflectedKernel v0 S0 Delta (t i) (t j) := by
  have h_decomp :
      (∑ i : Fin m, ∑ j : Fin m, c i * c j * rankTwoClusterReflectedKernel v0 S0 Delta (t i) (t j)) =
        v0 ^ 2 * (∑ i : Fin m, c i) ^ 2 +
          S0 * (∑ i : Fin m, c i * Real.exp (-Delta * t i)) ^ 2 := by
    have h_split :
        (∑ i : Fin m, ∑ j : Fin m, c i * c j * rankTwoClusterReflectedKernel v0 S0 Delta (t i) (t j)) =
          (∑ i : Fin m, ∑ j : Fin m, v0 ^ 2 * (c i * c j)) +
            (∑ i : Fin m, ∑ j : Fin m, c i * c j * exponentialTimeReflectedKernel S0 Delta (t i) (t j)) := by
      simp_rw [ ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      unfold rankTwoClusterReflectedKernel exponentialTimeReflectedKernel
      ring
    have h_vac :
        (∑ i : Fin m, ∑ j : Fin m, v0 ^ 2 * (c i * c j)) =
          v0 ^ 2 * (∑ i : Fin m, c i) ^ 2 := by
      rw [sq (∑ i : Fin m, c i), Finset.sum_mul]
      simp only [Finset.mul_sum]
    rw [h_split, h_vac, exponentialTimeReflectedKernel_gram_eq_sq]
  refine ⟨h_decomp, ?_⟩
  rw [h_decomp]
  exact add_nonneg (mul_nonneg (sq_nonneg v0) (sq_nonneg _)) (mul_nonneg hS0 (sq_nonneg _))

/-- Multi-mode discrete Källén–Lehmann spectral time-reflected kernel
`∑ a : Fin N, w a * exp(-Delta a * (t1 + t2))`. -/
noncomputable def spectralKallenLehmannReflectedKernel {N : ℕ} (w Delta : Fin N → ℝ) (t1 t2 : ℝ) : ℝ :=
  ∑ a : Fin N, exponentialTimeReflectedKernel (w a) (Delta a) t1 t2

/-- Exact `N`-mode Källén–Lehmann weighted sum-of-squares factorization of the finite reflected
Gram form, and its unconditional nonnegativity when all spectral weights satisfy `0 ≤ w a`. -/
theorem spectralKallenLehmannReflectedKernel_gram_eq_sum_sq_and_nonneg
    {N : ℕ} (w Delta : Fin N → ℝ) (hw : ∀ a : Fin N, 0 ≤ w a)
    {m : ℕ} (t c : Fin m → ℝ) :
    (∑ i : Fin m, ∑ j : Fin m,
      c i * c j * spectralKallenLehmannReflectedKernel w Delta (t i) (t j)) =
      ∑ a : Fin N, w a * (∑ i : Fin m, c i * Real.exp (-Delta a * t i)) ^ 2 ∧
    0 ≤ ∑ i : Fin m, ∑ j : Fin m,
      c i * c j * spectralKallenLehmannReflectedKernel w Delta (t i) (t j) := by
  have h_decomp :
      (∑ i : Fin m, ∑ j : Fin m,
        c i * c j * spectralKallenLehmannReflectedKernel w Delta (t i) (t j)) =
        ∑ a : Fin N, w a * (∑ i : Fin m, c i * Real.exp (-Delta a * t i)) ^ 2 := by
    calc
      (∑ i : Fin m, ∑ j : Fin m,
        c i * c j * spectralKallenLehmannReflectedKernel w Delta (t i) (t j))
        = ∑ i : Fin m, ∑ j : Fin m, ∑ a : Fin N,
            c i * c j * exponentialTimeReflectedKernel (w a) (Delta a) (t i) (t j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          unfold spectralKallenLehmannReflectedKernel
          rw [Finset.mul_sum]
      _ = ∑ i : Fin m, ∑ a : Fin N, ∑ j : Fin m,
            c i * c j * exponentialTimeReflectedKernel (w a) (Delta a) (t i) (t j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ a : Fin N, ∑ i : Fin m, ∑ j : Fin m,
            c i * c j * exponentialTimeReflectedKernel (w a) (Delta a) (t i) (t j) := by
          exact Finset.sum_comm
      _ = ∑ a : Fin N, w a * (∑ i : Fin m, c i * Real.exp (-Delta a * t i)) ^ 2 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          exact exponentialTimeReflectedKernel_gram_eq_sq (w a) (Delta a) t c
  refine ⟨h_decomp, ?_⟩
  rw [h_decomp]
  exact Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (sq_nonneg _)

/-- Dyadic UV Cauchy refinement stability (`SchurFeshbachWaveletComb`) and joint
Mellin–Tauberian / Feshbach defect error contraction (`HamiltonianScaleComb`) across UV cutoffs `K ≤ K'`. -/
theorem continuum_dyadic_uv_cauchy_and_tauberian_feshbach_bridge
    (Delta_seq : ℕ → ℝ) {C alpha_est alpha_true err_tauberian err_feshbach B_noise σ C_uv : ℝ}
    {K K' : ℕ}
    (hC : 0 ≤ C) (hKK' : K ≤ K')
    (h_step : ∀ j : ℕ, |Delta_seq (j + 1) - Delta_seq j| ≤ C * (1 / 4 : ℝ) ^ (j + 1))
    (hσ : 0 < σ) (hB : 0 < B_noise) (hC_uv : 0 < C_uv)
    (h_split : alpha_est - alpha_true = err_tauberian + err_feshbach)
    (h_taub : |err_tauberian| ≤ B_noise / σ)
    (h_fesh : |err_feshbach| ≤ C_uv * (1 / 4 : ℝ) ^ K) :
    (|Delta_seq K' - Delta_seq K| ≤ (C / 3) * ((1 / 4 : ℝ) ^ K - (1 / 4 : ℝ) ^ K') ∧
      |Delta_seq K' - Delta_seq K| ≤ (C / 3) * (1 / 4 : ℝ) ^ K) ∧
    (|alpha_est - alpha_true| ≤ B_noise / σ + C_uv * (1 / 4 : ℝ) ^ K ∧
      B_noise / (2 * σ) + C_uv * (1 / 4 : ℝ) ^ (K + 1) <
        B_noise / σ + C_uv * (1 / 4 : ℝ) ^ K) := by
  exact ⟨JesseMath.Unified.SchurFeshbachWaveletComb.dyadic_uv_refinement_cauchy_invariance
      Delta_seq hC hKK' h_step,
    JesseMath.Unified.HamiltonianScaleComb.joint_tauberian_feshbach_defect_error_bound
      K hσ hB hC_uv h_split h_taub h_fesh⟩

/-!
## Quantitative Spectral-Window Control: Preventing Both Gap Collapse (`Δ_n → 0`) and Excitation Collapse (`S0_n → 0` or `Δ_n → ∞`) (`M3`/`M4`)

In the continuum and infinite-volume limits, two distinct degeneracies must be ruled out:
1. **Mass-gap collapse (`Δ_n → 0`):** prevented by a uniform lower bound `0 < m_min ≤ Delta n` in
   fixed physical units, which enforces uniform exponential decay `≤ S_max * exp(-2 * m_min * t)`.
2. **Excitation collapse (`S0_n → 0` or `Δ_n → ∞`):** prevented by a uniform lower bound on the
   excited spectral weight `0 < S_min ≤ S0 n` together with a finite upper bound `Delta n ≤ m_max` on
   the first excited energy, which enforces the cutoff-independent positive correlator floor
   `0 < S_min * exp(-2 * m_max * t) ≤ exponentialTimeReflectedKernel (S0 n) (Delta n) t t` at every
   physical Euclidean time `t ≥ 0`.
-/

/-- Cutoff-independent positive excitation floor `S_min * exp(-2 * m_max * t)` at physical time `t ≥ 0`
for an approximating family with `0 < S_min ≤ S0 n` and `Delta n ≤ m_max`. -/
noncomputable def uniformExcitationMarginFloor (S_min m_max t : ℝ) : ℝ :=
  S_min * Real.exp (-2 * m_max * t)

/-- Cutoff-independent exponential clustering envelope `S_max * exp(-2 * m_min * t)` at physical
time `t ≥ 0` for an approximating family with `S0 n ≤ S_max` and `0 < m_min ≤ Delta n`. -/
noncomputable def uniformExponentialClusterEnvelope (S_max m_min t : ℝ) : ℝ :=
  S_max * Real.exp (-2 * m_min * t)

/-- Two-sided quantitative spectral-window control along an approximating sequence `(S0 n, Delta n)`
(`M3`/`M4` synthesis):
when `0 < S_min ≤ S0 n ≤ S_max` and `0 < m_min ≤ Delta n ≤ m_max` hold uniformly in `n`, every
cutoff `n` simultaneously satisfies the positive excitation floor
`0 < uniformExcitationMarginFloor S_min m_max t ≤ exponentialTimeReflectedKernel (S0 n) (Delta n) t t`
and the uniform exponential clustering bound
`exponentialTimeReflectedKernel (S0 n) (Delta n) t t ≤ uniformExponentialClusterEnvelope S_max m_min t`
for all `t ≥ 0` (with strict decay `< S_max` for `t > 0`). -/
theorem uniform_spectral_window_preserves_excitation_and_exponential_clustering
    (S0 Delta : ℕ → ℝ) {S_min S_max m_min m_max t : ℝ}
    (hS_min_pos : 0 < S_min)
    (hS_lo : ∀ n : ℕ, S_min ≤ S0 n)
    (hS_hi : ∀ n : ℕ, S0 n ≤ S_max)
    (hm_min_pos : 0 < m_min)
    (hm_lo : ∀ n : ℕ, m_min ≤ Delta n)
    (hm_hi : ∀ n : ℕ, Delta n ≤ m_max)
    (ht_nonneg : 0 ≤ t) :
    0 < uniformExcitationMarginFloor S_min m_max t ∧
    (∀ n : ℕ,
      uniformExcitationMarginFloor S_min m_max t ≤
        exponentialTimeReflectedKernel (S0 n) (Delta n) t t ∧
      exponentialTimeReflectedKernel (S0 n) (Delta n) t t ≤
        uniformExponentialClusterEnvelope S_max m_min t) ∧
    (0 < t → uniformExponentialClusterEnvelope S_max m_min t < S_max) := by
  have hS_max_pos : 0 < S_max := lt_of_lt_of_le hS_min_pos (le_trans (hS_lo 0) (hS_hi 0))
  have h_floor_pos : 0 < uniformExcitationMarginFloor S_min m_max t := by
    unfold uniformExcitationMarginFloor
    exact mul_pos hS_min_pos (Real.exp_pos _)
  refine ⟨h_floor_pos, ?_, ?_⟩
  · intro n
    have hS0_pos : 0 ≤ S0 n := le_of_lt (lt_of_lt_of_le hS_min_pos (hS_lo n))
    have hexp_lo : Real.exp (-2 * m_max * t) ≤ Real.exp (-Delta n * (t + t)) := by
      apply Real.exp_le_exp.mpr
      have h_mul : Delta n * (t + t) ≤ m_max * (t + t) :=
        mul_le_mul_of_nonneg_right (hm_hi n) (by linarith)
      linarith
    have hexp_hi : Real.exp (-Delta n * (t + t)) ≤ Real.exp (-2 * m_min * t) := by
      apply Real.exp_le_exp.mpr
      have h_mul : m_min * (t + t) ≤ Delta n * (t + t) :=
        mul_le_mul_of_nonneg_right (hm_lo n) (by linarith)
      linarith
    refine ⟨?_, ?_⟩
    · unfold uniformExcitationMarginFloor exponentialTimeReflectedKernel
      exact mul_le_mul (hS_lo n) hexp_lo (le_of_lt (Real.exp_pos _)) hS0_pos
    · unfold exponentialTimeReflectedKernel uniformExponentialClusterEnvelope
      exact mul_le_mul (hS_hi n) hexp_hi (le_of_lt (Real.exp_pos _)) (le_of_lt hS_max_pos)
  · intro ht_pos
    unfold uniformExponentialClusterEnvelope
    have h_neg : -2 * m_min * t < 0 := by nlinarith
    have hexp_lt : Real.exp (-2 * m_min * t) < 1 := Real.exp_lt_one_iff.mpr h_neg
    nlinarith

/-- Multi-mode Källén–Lehmann spectral Hamiltonian energy quadratic form
`∑ a : Fin N, w a * Delta a * (c a)^2` on an `N`-mode excited state expansion. -/
noncomputable def multiModeSpectralEnergyForm {N : ℕ} (w Delta c : Fin N → ℝ) : ℝ :=
  ∑ a : Fin N, w a * Delta a * (c a) ^ 2

/-- Multi-mode Källén–Lehmann spectral norm-squared quadratic form
`∑ a : Fin N, w a * (c a)^2` on an `N`-mode excited state expansion. -/
noncomputable def multiModeSpectralNormSq {N : ℕ} (w c : Fin N → ℝ) : ℝ :=
  ∑ a : Fin N, w a * (c a) ^ 2

/-- Finite-`N` multi-mode Källén–Lehmann Hamiltonian gap coercivity (`M5`/`M6`):
for any finite number `N` of excited spectral modes (`Fin N`) with nonnegative spectral weights
`0 ≤ w a` and mode energies bounded below by `0 < m_gap ≤ Delta a`, the finite `N`-mode energy sum
dominates `m_gap * multiModeSpectralNormSq w c` and is strictly positive on every state with
positive spectral norm. For the countable infinite series `∑' n : ℕ` under `Summable`, see
`tsum_infinite_tower_kallen_lehmann_coercivity`. -/
theorem multiMode_kallen_lehmann_hamiltonian_gap_coercivity_and_infinite_tower_bridge
    {N : ℕ} (w Delta c : Fin N → ℝ) {m_gap : ℝ}
    (hm_pos : 0 < m_gap)
    (hw : ∀ a : Fin N, 0 ≤ w a)
    (hDelta : ∀ a : Fin N, m_gap ≤ Delta a) :
    0 ≤ multiModeSpectralNormSq w c ∧
    m_gap * multiModeSpectralNormSq w c ≤ multiModeSpectralEnergyForm w Delta c ∧
    (0 < multiModeSpectralNormSq w c → 0 < multiModeSpectralEnergyForm w Delta c) := by
  have h_norm_nonneg : 0 ≤ multiModeSpectralNormSq w c := by
    unfold multiModeSpectralNormSq
    exact Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (sq_nonneg (c a))
  have h_coerc : m_gap * multiModeSpectralNormSq w c ≤ multiModeSpectralEnergyForm w Delta c := by
    unfold multiModeSpectralNormSq multiModeSpectralEnergyForm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h_eq : m_gap * (w a * (c a) ^ 2) = w a * m_gap * (c a) ^ 2 := by ring
    rw [h_eq]
    have h1 : w a * m_gap ≤ w a * Delta a := mul_le_mul_of_nonneg_left (hDelta a) (hw a)
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg (c a))
  exact ⟨h_norm_nonneg, h_coerc, fun h_pos => lt_of_lt_of_le (mul_pos hm_pos h_pos) h_coerc⟩

/-- Conditional fixed-time correlator limit-bound preservation (`M3`/`M4`):
when an approximating sequence of Euclidean time-reflected correlators
`exponentialTimeReflectedKernel (S0 n) (Delta n) t t` with uniform spectral-window bounds
`0 < S_min ≤ S0 n ≤ S_max` and `0 < m_min ≤ Delta n ≤ m_max` is assumed via `h_tendsto` to converge
to `C_lim` at `t ≥ 0`, the limit `C_lim` inherits both the positive excitation floor
`0 < uniformExcitationMarginFloor S_min m_max t ≤ C_lim` and the exponential clustering envelope
`C_lim ≤ uniformExponentialClusterEnvelope S_max m_min t`. For derived Cauchy convergence from a
geometric step contraction without assuming `h_tendsto`, see
`cauchySeq_and_limit_bounds_of_geometric_correlator_contraction`. -/
theorem joint_thermodynamic_and_continuum_correlator_cauchy_and_nontriviality
    (S0 Delta : ℕ → ℝ) {S_min S_max m_min m_max t C_lim : ℝ}
    (hS_min_pos : 0 < S_min)
    (hS_lo : ∀ n : ℕ, S_min ≤ S0 n)
    (hS_hi : ∀ n : ℕ, S0 n ≤ S_max)
    (hm_min_pos : 0 < m_min)
    (hm_lo : ∀ n : ℕ, m_min ≤ Delta n)
    (hm_hi : ∀ n : ℕ, Delta n ≤ m_max)
    (ht_nonneg : 0 ≤ t)
    (h_tendsto :
      Tendsto (fun n : ℕ => exponentialTimeReflectedKernel (S0 n) (Delta n) t t)
        atTop (𝓝 C_lim)) :
    0 < uniformExcitationMarginFloor S_min m_max t ∧
    uniformExcitationMarginFloor S_min m_max t ≤ C_lim ∧
    C_lim ≤ uniformExponentialClusterEnvelope S_max m_min t ∧
    0 < C_lim := by
  have h_win :=
    uniform_spectral_window_preserves_excitation_and_exponential_clustering
      S0 Delta hS_min_pos hS_lo hS_hi hm_min_pos hm_lo hm_hi ht_nonneg
  have h_lo : uniformExcitationMarginFloor S_min m_max t ≤ C_lim :=
    ge_of_tendsto' h_tendsto (fun n => (h_win.2.1 n).1)
  have h_hi : C_lim ≤ uniformExponentialClusterEnvelope S_max m_min t :=
    le_of_tendsto' h_tendsto (fun n => (h_win.2.1 n).2)
  exact ⟨h_win.1, h_lo, h_hi, lt_of_lt_of_le h_win.1 h_lo⟩

/-- Countable infinite-tower Källén–Lehmann spectral norm-squared series
`∑' n : ℕ, w n * (c n)^2` on a countable excited-mode sequence `n : ℕ`. -/
noncomputable def infiniteTowerSpectralNormSq (w c : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, w n * (c n) ^ 2

/-- Countable infinite-tower Källén–Lehmann Hamiltonian energy series
`∑' n : ℕ, w n * Delta n * (c n)^2` on a countable excited-mode sequence `n : ℕ`. -/
noncomputable def infiniteTowerSpectralEnergyForm (w Delta c : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, w n * Delta n * (c n) ^ 2

/-- Countable infinite-series (`tsum`) Källén–Lehmann spectral coercivity (`M5`/`M6`):
for any countable sequence of spectral weights `0 ≤ w n`, mode energies `0 < m_gap ≤ Delta n`,
and state amplitudes `c n` in the quadratic-form domain (`Summable (fun n => w n * (c n)^2)` and
`Summable (fun n => w n * Delta n * (c n)^2)`), the infinite series `infiniteTowerSpectralEnergyForm`
dominates `m_gap * infiniteTowerSpectralNormSq w c` and is strictly positive whenever
`0 < infiniteTowerSpectralNormSq w c`. -/
theorem tsum_infinite_tower_kallen_lehmann_coercivity
    (w Delta c : ℕ → ℝ) {m_gap : ℝ}
    (hm_pos : 0 < m_gap)
    (hw : ∀ n : ℕ, 0 ≤ w n)
    (hDelta : ∀ n : ℕ, m_gap ≤ Delta n)
    (h_summable_norm : Summable (fun n : ℕ => w n * (c n) ^ 2))
    (h_summable_energy : Summable (fun n : ℕ => w n * Delta n * (c n) ^ 2)) :
    0 ≤ infiniteTowerSpectralNormSq w c ∧
    m_gap * infiniteTowerSpectralNormSq w c ≤ infiniteTowerSpectralEnergyForm w Delta c ∧
    (0 < infiniteTowerSpectralNormSq w c → 0 < infiniteTowerSpectralEnergyForm w Delta c) := by
  have h_norm_nonneg : 0 ≤ infiniteTowerSpectralNormSq w c := by
    unfold infiniteTowerSpectralNormSq
    exact tsum_nonneg fun n => mul_nonneg (hw n) (sq_nonneg (c n))
  have h_coerc :
      m_gap * infiniteTowerSpectralNormSq w c ≤ infiniteTowerSpectralEnergyForm w Delta c := by
    unfold infiniteTowerSpectralNormSq infiniteTowerSpectralEnergyForm
    rw [← tsum_mul_left]
    refine (h_summable_norm.mul_left m_gap).tsum_le_tsum (fun n => ?_) h_summable_energy
    have h_eq : m_gap * (w n * (c n) ^ 2) = w n * m_gap * (c n) ^ 2 := by ring
    rw [h_eq]
    have h1 : w n * m_gap ≤ w n * Delta n := mul_le_mul_of_nonneg_left (hDelta n) (hw n)
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg (c n))
  exact ⟨h_norm_nonneg, h_coerc, fun h_pos => lt_of_lt_of_le (mul_pos hm_pos h_pos) h_coerc⟩

/-- Derived Cauchy convergence and limit-window survival under a geometric RG step contraction
(`M3`/`M4` Cauchy completeness theorem):
if the sequence of Euclidean time-reflected correlators
`C_seq n := exponentialTimeReflectedKernel (S0 n) (Delta n) t t` satisfies the uniform spectral
window `0 < S_min ≤ S0 n ≤ S_max`, `0 < m_min ≤ Delta n ≤ m_max` (`t ≥ 0`), and a geometric
step-contraction bound `dist (C_seq n) (C_seq (n + 1)) ≤ B_step * r ^ n` with `0 ≤ r < 1`, then
`C_seq` is a `CauchySeq` and (by completeness of `ℝ`, without assuming `h_tendsto`) converges to a
limit `C_lim` satisfying `0 < uniformExcitationMarginFloor S_min m_max t ≤ C_lim` and
`C_lim ≤ uniformExponentialClusterEnvelope S_max m_min t`. -/
theorem cauchySeq_and_limit_bounds_of_geometric_correlator_contraction
    (S0 Delta : ℕ → ℝ) {S_min S_max m_min m_max t B_step r : ℝ}
    (hS_min_pos : 0 < S_min)
    (hS_lo : ∀ n : ℕ, S_min ≤ S0 n)
    (hS_hi : ∀ n : ℕ, S0 n ≤ S_max)
    (hm_min_pos : 0 < m_min)
    (hm_lo : ∀ n : ℕ, m_min ≤ Delta n)
    (hm_hi : ∀ n : ℕ, Delta n ≤ m_max)
    (ht_nonneg : 0 ≤ t)
    (_hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1)
    (h_step : ∀ n : ℕ,
      dist (exponentialTimeReflectedKernel (S0 n) (Delta n) t t)
        (exponentialTimeReflectedKernel (S0 (n + 1)) (Delta (n + 1)) t t) ≤
        B_step * r ^ n) :
    CauchySeq (fun n : ℕ => exponentialTimeReflectedKernel (S0 n) (Delta n) t t) ∧
    ∃ C_lim : ℝ,
      Tendsto (fun n : ℕ => exponentialTimeReflectedKernel (S0 n) (Delta n) t t)
        atTop (𝓝 C_lim) ∧
      0 < uniformExcitationMarginFloor S_min m_max t ∧
      uniformExcitationMarginFloor S_min m_max t ≤ C_lim ∧
      C_lim ≤ uniformExponentialClusterEnvelope S_max m_min t ∧
      0 < C_lim := by
  have h_cauchy : CauchySeq (fun n : ℕ => exponentialTimeReflectedKernel (S0 n) (Delta n) t t) :=
    cauchySeq_of_le_geometric r B_step hr_lt_one h_step
  rcases cauchySeq_tendsto_of_complete h_cauchy with ⟨C_lim, h_tendsto⟩
  have h_lim :=
    joint_thermodynamic_and_continuum_correlator_cauchy_and_nontriviality
      S0 Delta hS_min_pos hS_lo hS_hi hm_min_pos hm_lo hm_hi ht_nonneg h_tendsto
  exact ⟨h_cauchy, ⟨C_lim, h_tendsto, h_lim.1, h_lim.2.1, h_lim.2.2.1, h_lim.2.2.2⟩⟩

/-- Mixed degree-0 / degree-2 Osterwalder–Schrader quadratic form
`c0^2 * 1 + 2 * c0 * c2 * b + c2^2 * 0` for a hierarchy with normalized vacuum `S_0 = 1`,
two-point expectation `S_2(F_2) = b`, and truncated four-point expectation `S_4 = 0`
(`P08`/`X1_MIXED_DEGREE`). -/
def mixedDegreeZeroTwoGramForm (b c0 c2 : ℝ) : ℝ :=
  c0 ^ 2 * 1 + 2 * c0 * c2 * b + c2 ^ 2 * 0

/-- Determinant `1 * 0 - b * b = -b^2` of the mixed degree-0 / degree-2 Osterwalder–Schrader
Gram block `[[1, b], [b, 0]]` when `S_0 = 1`, `S_2(F_2) = b`, and `S_4 = 0` (`P08`/`X1_MIXED_DEGREE`). -/
def mixedDegreeZeroTwoGramDet (b : ℝ) : ℝ :=
  1 * 0 - b * b

/-- Truncated Schwinger hierarchy obstruction (`P08`/`X1_MIXED_DEGREE` & `X2_HIGHER_CLUSTER`):
if an Euclidean hierarchy sets `S_0 = 1`, has a nonzero two-point expectation `S_2(F_2) = b ≠ 0`,
and truncates higher-degree moments to `S_3 = 0` and `S_4 = 0`, then:
1. The mixed degree-0 / degree-2 Gram matrix `[[1, b], [b, 0]]` has negative determinant
   `mixedDegreeZeroTwoGramDet b = -b^2 < 0`,
2. Evaluating the mixed-degree quadratic form at `(c0, c2) = (1, -1 / b)` gives `-1 < 0` (and at
   `(c0, c2) = (-b, 1)` gives `-b^2 < 0`), refuting full all-degree OS reflection positivity even
   when degree-1 two-point reflection positivity holds, and
3. For any positive `S_2 > 0` and `S_1 > 0`, the `2 + 1` cluster factorization defect
   `|0 - S_2 * S_1| = S_2 * S_1 > 0` cannot vanish (`X2_HIGHER_CLUSTER`). -/
theorem truncated_schwinger_hierarchy_fails_mixed_degree_os_positivity_and_higher_clustering
    {b S1 S2 : ℝ} (hb : b ≠ 0) (hS1 : 0 < S1) (hS2 : 0 < S2) :
    mixedDegreeZeroTwoGramDet b = -(b ^ 2) ∧
    mixedDegreeZeroTwoGramDet b < 0 ∧
    mixedDegreeZeroTwoGramForm b 1 (-1 / b) = -1 ∧
    mixedDegreeZeroTwoGramForm b 1 (-1 / b) < 0 ∧
    mixedDegreeZeroTwoGramForm b (-b) 1 = -(b ^ 2) ∧
    mixedDegreeZeroTwoGramForm b (-b) 1 < 0 ∧
    0 < |(0 : ℝ) - S2 * S1| := by
  have hb_sq_pos : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have h_det_eq : mixedDegreeZeroTwoGramDet b = -(b ^ 2) := by
    unfold mixedDegreeZeroTwoGramDet
    ring
  have h_form_inv : mixedDegreeZeroTwoGramForm b 1 (-1 / b) = -1 := by
    unfold mixedDegreeZeroTwoGramForm
    field_simp [hb]
    ring
  have h_form_b : mixedDegreeZeroTwoGramForm b (-b) 1 = -(b ^ 2) := by
    unfold mixedDegreeZeroTwoGramForm
    ring
  have h_cluster : 0 < |(0 : ℝ) - S2 * S1| := by
    rw [zero_sub, abs_neg, abs_of_pos (mul_pos hS2 hS1)]
    exact mul_pos hS2 hS1
  exact ⟨h_det_eq, by linarith, h_form_inv, by norm_num [h_form_inv],
    h_form_b, by linarith, h_cluster⟩

/-- Continuous `45°` Euclidean `O(4)` rotation counterexample for the `L^1` exponential correlator
and physical-volume exhaustion contrast (`P06`/`O2` and `P08`/`X3_ROTATION`):
1. Under a `45°` rotation mapping `x = (t, 0, 0, 0)` to `x_rot = (t / √2, t / √2, 0, 0)` (`t > 0`),
   the Euclidean norm squared `(t / √2)^2 + (t / √2)^2 = t^2` is preserved, whereas the `L^1`
   coordinate sum changes from `t` to `√2 * t > t`, so for `m > 0`,
   `exp(-m * (√2 * t)) < exp(-m * t)`, proving that coordinate-axis decay does not imply
   continuous `O(4)` rotational invariance, and
2. Taking `L_n = 2^n → ∞` with `a_n = ell_box / 2^n` keeps the physical box side
   `a_n * L_n = ell_box` constant (finite physical volume), whereas `L_n = 4^n` with `a_n = 1 / 2^n`
   gives `a_n * L_n = 2^n → ∞` (infinite physical volume exhaustion). -/
theorem continuous_45deg_rotation_breaks_l1_exponential_correlator_and_volume_exhaustion_contrast
    {m t ell_box : ℝ} (hm : 0 < m) (ht : 0 < t) (n : ℕ) :
    (t / Real.sqrt 2) ^ 2 + (t / Real.sqrt 2) ^ 2 = t ^ 2 ∧
    (t / Real.sqrt 2) + (t / Real.sqrt 2) = Real.sqrt 2 * t ∧
    t < Real.sqrt 2 * t ∧
    Real.exp (-(m * (Real.sqrt 2 * t))) < Real.exp (-(m * t)) ∧
    (ell_box / (2 : ℝ) ^ n) * (2 : ℝ) ^ n = ell_box ∧
    (1 / (2 : ℝ) ^ n) * (4 : ℝ) ^ n = (2 : ℝ) ^ n := by
  have h_sqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_sqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt h_sqrt2_pos
  have h_l2 : (t / Real.sqrt 2) ^ 2 + (t / Real.sqrt 2) ^ 2 = t ^ 2 := by
    rw [div_pow, h_sqrt2_sq]
    ring
  have h_l1 : (t / Real.sqrt 2) + (t / Real.sqrt 2) = Real.sqrt 2 * t := by
    field_simp [h_sqrt2_ne]
    nlinarith [h_sqrt2_sq]
  have h_one_lt_sqrt2 : 1 < Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h_t_lt : t < Real.sqrt 2 * t := by nlinarith
  have h_exp_lt : Real.exp (-(m * (Real.sqrt 2 * t))) < Real.exp (-(m * t)) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  have h_pow2_ne : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have h_box_const : (ell_box / (2 : ℝ) ^ n) * (2 : ℝ) ^ n = ell_box :=
    div_mul_cancel₀ ell_box h_pow2_ne
  have h_box_grow : (1 / (2 : ℝ) ^ n) * (4 : ℝ) ^ n = (2 : ℝ) ^ n := by
    have h4 : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
      rw [← mul_pow]
      norm_num
    rw [h4]
    field_simp [h_pow2_ne]
  exact ⟨h_l2, h_l1, h_t_lt, h_exp_lt, h_box_const, h_box_grow⟩

/-- Alternating spectral weight sequence `S0_n = 1` for even `n` and `S0_n = 2` for odd `n`
(`P07`/`X5_WINDOW_NOT_CONVERGENCE`). -/
def alternatingSpectralAmplitude (n : ℕ) : ℝ :=
  if n % 2 = 0 then 1 else 2

/-- Uniform spectral window without `h_tendsto` does not imply full-sequence convergence, and
finite-`N` mode inequalities require a common summable form domain (`P07`/`X5_WINDOW_NOT_CONVERGENCE`
and `X6_FINITE_MODES_NO_STATE_LIMIT`):
1. The sequence `S0 n := alternatingSpectralAmplitude n ∈ [1, 2]` with `Delta n := 1 ∈ [1, 1]`
   satisfies the uniform spectral window at every cutoff `n`, yet oscillates between `exp(-2 * t)`
   at even `n = 2 * k` and `2 * exp(-2 * t)` at odd `n = 2 * k + 1` with gap `exp(-2 * t) > 0`,
   while its even subsequence `n = 2 * k` is constant (`= exp(-2 * t)`), and
2. For unit weights and amplitudes `w = 1, c = 1, Delta = 1` on `Fin N`, both
   `multiModeSpectralNormSq` and `multiModeSpectralEnergyForm` equal `(N : ℝ)`, growing linearly
   with `N`, whereas at mode `j ≥ 1` with `c_j = 1 / j` and `Delta_j = j`, the norm term is
   `1 / j^2` while the energy term is `1 / j`, showing why an infinite-mode extension requires
   both norm and energy summability (`tsum_infinite_tower_kallen_lehmann_coercivity`). -/
theorem uniform_spectral_window_does_not_imply_full_sequence_convergence_and_form_domain_necessity
    (k N : ℕ) (t : ℝ) {j : ℝ} (hj : 0 < j) :
    (∀ n : ℕ, 1 ≤ alternatingSpectralAmplitude n ∧ alternatingSpectralAmplitude n ≤ 2) ∧
    exponentialTimeReflectedKernel (alternatingSpectralAmplitude (2 * k)) 1 t t =
      Real.exp (-2 * t) ∧
    exponentialTimeReflectedKernel (alternatingSpectralAmplitude (2 * k + 1)) 1 t t =
      2 * Real.exp (-2 * t) ∧
    0 < exponentialTimeReflectedKernel (alternatingSpectralAmplitude (2 * k + 1)) 1 t t -
        exponentialTimeReflectedKernel (alternatingSpectralAmplitude (2 * k)) 1 t t ∧
    multiModeSpectralNormSq (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) = (N : ℝ) ∧
    multiModeSpectralEnergyForm (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
      (fun _ : Fin N => (1 : ℝ)) = (N : ℝ) ∧
    (1 : ℝ) * (1 / j) ^ 2 = 1 / j ^ 2 ∧
    (1 : ℝ) * j * (1 / j) ^ 2 = 1 / j := by
  have h_win : ∀ n : ℕ, 1 ≤ alternatingSpectralAmplitude n ∧ alternatingSpectralAmplitude n ≤ 2 := by
    intro n
    unfold alternatingSpectralAmplitude
    split_ifs <;> constructor <;> norm_num
  have h_even_val : alternatingSpectralAmplitude (2 * k) = 1 := by
    unfold alternatingSpectralAmplitude
    simp
  have h_odd_val : alternatingSpectralAmplitude (2 * k + 1) = 2 := by
    unfold alternatingSpectralAmplitude
    simp
  have h_even_ker :
      exponentialTimeReflectedKernel (alternatingSpectralAmplitude (2 * k)) 1 t t =
        Real.exp (-2 * t) := by
    unfold exponentialTimeReflectedKernel
    rw [h_even_val, one_mul]
    congr 1
    ring
  have h_odd_ker :
      exponentialTimeReflectedKernel (alternatingSpectralAmplitude (2 * k + 1)) 1 t t =
        2 * Real.exp (-2 * t) := by
    unfold exponentialTimeReflectedKernel
    rw [h_odd_val]
    congr 2
    ring
  have h_diff_pos :
      0 < exponentialTimeReflectedKernel (alternatingSpectralAmplitude (2 * k + 1)) 1 t t -
          exponentialTimeReflectedKernel (alternatingSpectralAmplitude (2 * k)) 1 t t := by
    rw [h_odd_ker, h_even_ker]
    linarith [Real.exp_pos (-2 * t)]
  have h_norm_N :
      multiModeSpectralNormSq (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) = (N : ℝ) := by
    unfold multiModeSpectralNormSq
    simp
  have h_energy_N :
      multiModeSpectralEnergyForm (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
        (fun _ : Fin N => (1 : ℝ)) = (N : ℝ) := by
    unfold multiModeSpectralEnergyForm
    simp
  have hj_ne : j ≠ 0 := ne_of_gt hj
  have h_mode_norm : (1 : ℝ) * (1 / j) ^ 2 = 1 / j ^ 2 := by ring
  have h_mode_energy : (1 : ℝ) * j * (1 / j) ^ 2 = 1 / j := by
    field_simp [hj_ne]
  exact ⟨h_win, h_even_ker, h_odd_ker, h_diff_pos, h_norm_N, h_energy_N, h_mode_norm, h_mode_energy⟩

/-- Untruncated mixed degree-`(0, 2)` Osterwalder–Schrader Gram quadratic form
`c0^2 * S_0 + 2 * c0 * c2 * S_2(\Theta 1 \otimes F_2) + c2^2 * S_4(\Theta F_2 \otimes F_2)`
with `S_0 = 1`, `S_2(\Theta 1 \otimes F_2) = b`, and 4-point moment `S_4(\Theta F_2 \otimes F_2) = s4`
(`P08`/`O3` and `X1_MIXED_DEGREE` completion). -/
def untruncatedMixedDegreeZeroTwoGramForm (b s4 c0 c2 : ℝ) : ℝ :=
  c0 ^ 2 + 2 * b * c0 * c2 + s4 * c2 ^ 2

/-- Determinant `1 * s4 - b^2` of the untruncated `2 × 2` mixed degree-`(0, 2)` OS Gram matrix
`[[1, b], [b, s4]]`. -/
def untruncatedMixedDegreeZeroTwoGramDet (b s4 : ℝ) : ℝ :=
  s4 - b ^ 2

/-- Positive semidefiniteness of the untruncated mixed degree-`(0, 2)` OS Gram form when the
4-point moment satisfies the Cauchy–Schwarz / connected-variance decomposition `s4 = b^2 + sigma2^2`
(`P08`/`O3` vs. `X1_MIXED_DEGREE`):
1. Setting `s4 = 0` recovers the truncated form `mixedDegreeZeroTwoGramForm b c0 c2` and negative
   determinant `mixedDegreeZeroTwoGramDet b = -b^2`,
2. When `s4 = b^2 + sigma2^2` (representing `⟨F_2 Ω, F_2 Ω⟩ = ⟨Ω, F_2 Ω⟩^2 + ‖(F_2 - b I) Ω‖^2`),
   `untruncatedMixedDegreeZeroTwoGramForm b s4 c0 c2 = (c0 + b * c2)^2 + (sigma2 * c2)^2 ≥ 0` for
   all `c0, c2 : ℝ`, and
3. The Gram determinant equals `untruncatedMixedDegreeZeroTwoGramDet b s4 = sigma2^2 ≥ 0` (strictly
   positive whenever the connected 2-observable variance amplitude `sigma2 ≠ 0`). -/
theorem untruncatedMixedDegreeZeroTwoGramForm_psd_and_det_eq_variance_sq
    (b sigma2 c0 c2 : ℝ) :
    untruncatedMixedDegreeZeroTwoGramForm b 0 c0 c2 =
      mixedDegreeZeroTwoGramForm b c0 c2 ∧
    untruncatedMixedDegreeZeroTwoGramDet b 0 =
      mixedDegreeZeroTwoGramDet b ∧
    untruncatedMixedDegreeZeroTwoGramForm b (b ^ 2 + sigma2 ^ 2) c0 c2 =
      (c0 + b * c2) ^ 2 + (sigma2 * c2) ^ 2 ∧
    0 ≤ untruncatedMixedDegreeZeroTwoGramForm b (b ^ 2 + sigma2 ^ 2) c0 c2 ∧
    untruncatedMixedDegreeZeroTwoGramDet b (b ^ 2 + sigma2 ^ 2) = sigma2 ^ 2 ∧
    0 ≤ untruncatedMixedDegreeZeroTwoGramDet b (b ^ 2 + sigma2 ^ 2) ∧
    (sigma2 ≠ 0 → 0 < untruncatedMixedDegreeZeroTwoGramDet b (b ^ 2 + sigma2 ^ 2)) := by
  have h_zero_form :
      untruncatedMixedDegreeZeroTwoGramForm b 0 c0 c2 =
        mixedDegreeZeroTwoGramForm b c0 c2 := by
    unfold untruncatedMixedDegreeZeroTwoGramForm mixedDegreeZeroTwoGramForm
    ring
  have h_zero_det :
      untruncatedMixedDegreeZeroTwoGramDet b 0 =
        mixedDegreeZeroTwoGramDet b := by
    unfold untruncatedMixedDegreeZeroTwoGramDet mixedDegreeZeroTwoGramDet
    ring
  have h_sq :
      untruncatedMixedDegreeZeroTwoGramForm b (b ^ 2 + sigma2 ^ 2) c0 c2 =
        (c0 + b * c2) ^ 2 + (sigma2 * c2) ^ 2 := by
    unfold untruncatedMixedDegreeZeroTwoGramForm
    ring
  have h_psd :
      0 ≤ untruncatedMixedDegreeZeroTwoGramForm b (b ^ 2 + sigma2 ^ 2) c0 c2 := by
    rw [h_sq]
    positivity
  have h_det :
      untruncatedMixedDegreeZeroTwoGramDet b (b ^ 2 + sigma2 ^ 2) = sigma2 ^ 2 := by
    unfold untruncatedMixedDegreeZeroTwoGramDet
    ring
  have h_det_nn :
      0 ≤ untruncatedMixedDegreeZeroTwoGramDet b (b ^ 2 + sigma2 ^ 2) := by
    rw [h_det]
    positivity
  refine ⟨h_zero_form, h_zero_det, h_sq, h_psd, h_det, h_det_nn, ?_⟩
  intro h_ne
  rw [h_det]
  exact sq_pos_of_ne_zero h_ne

#assert_zfc_axioms

end JesseMath.Physics.YangMillsContinuumLimitBridge
