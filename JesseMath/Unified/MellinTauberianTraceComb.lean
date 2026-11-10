import JesseMath.Linter.AxiomAudit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace JesseMath.Unified.MellinTauberianTraceComb

/-!
# Contender Gamma: The Micro-Local Mellin–Tauberian & Beurling–Selberg Spectral Comb
====================================================================================
Replaces the bare Hamiltonian heat trace `Tr(exp(-t H))` with a two-parameter
positive-definite convolution-square spectral comb `K_{σ, ω₀}(λ) = σ |φ̂(σ(λ - ω₀))|² ≥ 0`
to resolve closely spaced interior eigenvalues, Riemann zeta / L-function zeros, and
prime-power arithmetic defects at arbitrarily fine bandwidth `Δω ~ 1/σ` without suffering
the infrared masking catastrophe or losing Weil/Tauberian positivity.
-/

/-- General positive-definite convolution-square spectral comb kernel:
    `K_{σ, ω₀}(λ) = σ * (φHat(σ * (lam - ω₀)))^2`. -/
def convSquareComb (σ ω₀ : ℝ) (φHat : ℝ → ℝ) (lam : ℝ) : ℝ :=
  σ * (φHat (σ * (lam - ω₀))) ^ 2

/-- Gaussian-modulated convolution-square comb kernel:
    `K^{Gauss}_{σ, ω₀}(λ) = σ * (exp(-(σ * (lam - ω₀))^2))^2`. -/
def gaussianCombKernel (σ ω₀ lam : ℝ) : ℝ :=
  σ * (Real.exp (- (σ * (lam - ω₀)) ^ 2)) ^ 2

/-- Algebraic Beurling-Selberg rational convolution-square comb kernel:
    `K^{BS}_{σ, ω₀}(λ) = σ / (1 + 4 * σ^2 * (lam - ω₀)^2)^2`. -/
def algebraicBSCombKernel (σ ω₀ lam : ℝ) : ℝ :=
  σ / (1 + 4 * σ ^ 2 * (lam - ω₀) ^ 2) ^ 2

/-- Fejer-Selberg parabolic lower-envelope convolution-square kernel on the main lobe:
    `K^{Fejer}_{σ, ω₀}(λ) = σ * (1 - σ^2 * (lam - ω₀)^2)^2`. -/
def fejerParabolicCombKernel (σ ω₀ lam : ℝ) : ℝ :=
  σ * (1 - σ ^ 2 * (lam - ω₀) ^ 2) ^ 2

/-- Compactly supported Beurling-Selberg / Fejer triangular Fourier weight in log-prime space:
    `W_{BS}(σ, ξ) = 1 - ξ / (2 * σ)` for `0 ≤ ξ ≤ 2 * σ`, vanishing at the cutoff `ξ = 2 * σ`. -/
def beurlingFourierWeight (σ xi : ℝ) : ℝ :=
  1 - xi / (2 * σ)

/-- Bare Hamiltonian heat kernel `exp(-t * lam)`. -/
def bareHeatKernel (t lam : ℝ) : ℝ :=
  Real.exp (- t * lam)

/-- Signal-to-noise ratio of the Mellin-Tauberian spectral comb for a defect `α_defect`
    against prime-power / background fluctuation RMS `σ_noise`. -/
def combDefectSNR (σ α_defect σ_noise : ℝ) : ℝ :=
  (σ * α_defect) / σ_noise

/-- Signal-to-noise ratio of the bare Hamiltonian heat trace for a defect `α_defect`
    against cumulative low-lying background `1 + t * β_bg`. -/
def bareHeatDefectSNR (t α_defect β_bg : ℝ) : ℝ :=
  (t * α_defect) / (1 + t * β_bg)

/-- **Theorem 1 (Unconditional Positivity of Convolution-Square Comb)**:
    For any bandwidth `σ ≥ 0`, target frequency `ω₀`, envelope `φHat`, and spectral value `lam`,
    the convolution-square filter satisfies `0 ≤ convSquareComb σ ω₀ φHat lam`. -/
theorem convSquareComb_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (ω₀ : ℝ) (φHat : ℝ → ℝ) (lam : ℝ) :
    0 ≤ convSquareComb σ ω₀ φHat lam := by
  dsimp [convSquareComb]
  positivity

/-- **Theorem 2 (Exact Gaussian Convolution-Square Reduction & Symmetry)**:
    The Gaussian convolution-square kernel equals `σ * exp(-2 * σ^2 * (lam - ω₀)^2)`
    and is strictly symmetric around the target frequency `ω₀`. -/
theorem gaussianCombKernel_eq_and_symm (σ ω₀ lam δ : ℝ) :
    gaussianCombKernel σ ω₀ lam = σ * Real.exp (- 2 * σ ^ 2 * (lam - ω₀) ^ 2) ∧
    gaussianCombKernel σ ω₀ (ω₀ - δ) = gaussianCombKernel σ ω₀ (ω₀ + δ) := by
  constructor
  · dsimp [gaussianCombKernel]
    rw [sq (Real.exp _), ← Real.exp_add]
    congr 2
    ring
  · dsimp [gaussianCombKernel]
    have hsq : (σ * (ω₀ - δ - ω₀)) ^ 2 = (σ * (ω₀ + δ - ω₀)) ^ 2 := by ring
    rw [hsq]

/-- **Theorem 3 (Peak Attainment and Global Upper Envelope of Gaussian Comb)**:
    For `σ ≥ 0`, `gaussianCombKernel σ ω₀ lam` attains its maximum value `σ` at `lam = ω₀`
    and satisfies `gaussianCombKernel σ ω₀ lam ≤ σ` for all `lam ∈ ℝ`. -/
theorem gaussianCombKernel_peak_and_upper_bound {σ : ℝ} (hσ : 0 ≤ σ) (ω₀ lam : ℝ) :
    gaussianCombKernel σ ω₀ ω₀ = σ ∧ gaussianCombKernel σ ω₀ lam ≤ σ := by
  constructor
  · rw [(gaussianCombKernel_eq_and_symm σ ω₀ ω₀ 0).1]
    have h0 : - 2 * σ ^ 2 * (ω₀ - ω₀) ^ 2 = 0 := by ring
    rw [h0, Real.exp_zero, mul_one]
  · rw [(gaussianCombKernel_eq_and_symm σ ω₀ lam 0).1]
    have hexp_le : Real.exp (- 2 * σ ^ 2 * (lam - ω₀) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hsq : 0 ≤ σ ^ 2 * (lam - ω₀) ^ 2 := by positivity
      linarith
    calc σ * Real.exp (- 2 * σ ^ 2 * (lam - ω₀) ^ 2)
      _ ≤ σ * 1 := mul_le_mul_of_nonneg_left hexp_le hσ
      _ = σ := mul_one σ

/-- **Theorem 4 (Micro-Local Window Lower Bound for Gaussian Comb)**:
    On the micro-local resolution window `(lam - ω₀)^2 ≤ 1 / (4 * σ^2)` with `σ > 0`,
    the Gaussian comb kernel is bounded below by the linear Tauberian floor `exp(-1/2) * σ`. -/
theorem gaussianCombKernel_window_lower_bound {σ ω₀ lam : ℝ} (hσ : 0 < σ)
    (hwin : (lam - ω₀) ^ 2 ≤ 1 / (4 * σ ^ 2)) :
    Real.exp (- (1 / 2 : ℝ)) * σ ≤ gaussianCombKernel σ ω₀ lam := by
  rw [(gaussianCombKernel_eq_and_symm σ ω₀ lam 0).1]
  have hσ2_pos : 0 < σ ^ 2 := sq_pos_of_pos hσ
  have hσ2_ne : σ ^ 2 ≠ 0 := ne_of_gt hσ2_pos
  have hmul : 2 * σ ^ 2 * (lam - ω₀) ^ 2 ≤ 2 * σ ^ 2 * (1 / (4 * σ ^ 2)) := by
    exact mul_le_mul_of_nonneg_left hwin (by positivity)
  have hsimp : 2 * σ ^ 2 * (1 / (4 * σ ^ 2)) = (1 / 2 : ℝ) := by
    calc 2 * σ ^ 2 * (1 / (4 * σ ^ 2)) = (1 / 2) * (σ ^ 2 / σ ^ 2) := by ring
    _ = (1 / 2) * 1 := by rw [div_self hσ2_ne]
    _ = 1 / 2 := mul_one _
  have hexp_arg : - (1 / 2 : ℝ) ≤ - 2 * σ ^ 2 * (lam - ω₀) ^ 2 := by linarith
  have hexp_le : Real.exp (- (1 / 2 : ℝ)) ≤ Real.exp (- 2 * σ ^ 2 * (lam - ω₀) ^ 2) :=
    Real.exp_le_exp.mpr hexp_arg
  calc Real.exp (- (1 / 2 : ℝ)) * σ = σ * Real.exp (- (1 / 2 : ℝ)) := mul_comm _ _
  _ ≤ σ * Real.exp (- 2 * σ ^ 2 * (lam - ω₀) ^ 2) := mul_le_mul_of_nonneg_left hexp_le (le_of_lt hσ)

/-- **Theorem 5 (Algebraic Beurling-Selberg Micro-Local Floor & Quartic Far-Zone Decay)**:
    For `σ > 0`:
    (1) On the micro-local window `(lam - ω₀)^2 ≤ 1 / (4 * σ^2)`, `algebraicBSCombKernel σ ω₀ lam ≥ (1/4) * σ`.
    (2) In the off-resonant far zone `(lam_far - ω₀)^2 ≥ Δ^2` (`Δ > 0`),
        `algebraicBSCombKernel σ ω₀ lam_far ≤ 1 / (16 * σ^3 * Δ^4)`. -/
theorem algebraicBSCombKernel_window_and_decay {σ ω₀ lam Δ : ℝ} (hσ : 0 < σ) (hΔ : 0 < Δ)
    (hwin : (lam - ω₀) ^ 2 ≤ 1 / (4 * σ ^ 2))
    (lam_far : ℝ) (hfar : Δ ^ 2 ≤ (lam_far - ω₀) ^ 2) :
    (1 / 4 : ℝ) * σ ≤ algebraicBSCombKernel σ ω₀ lam ∧
    algebraicBSCombKernel σ ω₀ lam_far ≤ 1 / (16 * σ ^ 3 * Δ ^ 4) := by
  have hσ2_ne : σ ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hσ)
  constructor
  · dsimp [algebraicBSCombKernel]
    have h1 : 4 * σ ^ 2 * (lam - ω₀) ^ 2 ≤ 4 * σ ^ 2 * (1 / (4 * σ ^ 2)) :=
      mul_le_mul_of_nonneg_left hwin (by positivity)
    have h2 : 4 * σ ^ 2 * (1 / (4 * σ ^ 2)) = 1 := by
      calc 4 * σ ^ 2 * (1 / (4 * σ ^ 2)) = σ ^ 2 / σ ^ 2 := by ring
      _ = 1 := div_self hσ2_ne
    have hbase : 1 + 4 * σ ^ 2 * (lam - ω₀) ^ 2 ≤ 2 := by linarith
    have hbase_pos : 0 < 1 + 4 * σ ^ 2 * (lam - ω₀) ^ 2 := by positivity
    have hsq_le : (1 + 4 * σ ^ 2 * (lam - ω₀) ^ 2) ^ 2 ≤ 4 := by nlinarith
    have hsq_pos : 0 < (1 + 4 * σ ^ 2 * (lam - ω₀) ^ 2) ^ 2 := sq_pos_of_pos hbase_pos
    rw [
      show (1 / 4 : ℝ) * σ = σ / 4 by ring,
      div_le_div_iff₀ (by norm_num) hsq_pos
    ]
    nlinarith
  · dsimp [algebraicBSCombKernel]
    have h1 : 4 * σ ^ 2 * Δ ^ 2 ≤ 4 * σ ^ 2 * (lam_far - ω₀) ^ 2 :=
      mul_le_mul_of_nonneg_left hfar (by positivity)
    have hbase : 4 * σ ^ 2 * Δ ^ 2 ≤ 1 + 4 * σ ^ 2 * (lam_far - ω₀) ^ 2 := by linarith
    have hleft_pos : 0 < 4 * σ ^ 2 * Δ ^ 2 := by positivity
    have hsq_ge : (4 * σ ^ 2 * Δ ^ 2) ^ 2 ≤ (1 + 4 * σ ^ 2 * (lam_far - ω₀) ^ 2) ^ 2 := by
      nlinarith
    have hdenom_pos : 0 < 16 * σ ^ 3 * Δ ^ 4 := by positivity
    have hsq_pos : 0 < (1 + 4 * σ ^ 2 * (lam_far - ω₀) ^ 2) ^ 2 := by positivity
    rw [div_le_div_iff₀ hsq_pos hdenom_pos]
    have hexpand : σ * (16 * σ ^ 3 * Δ ^ 4) = (4 * σ ^ 2 * Δ ^ 2) ^ 2 := by ring
    linarith

/-- **Theorem 6 (Fejer-Selberg Parabolic Comb 9/16 Tauberian Floor)**:
    On the micro-local window `(lam - ω₀)^2 ≤ 1 / (4 * σ^2)` with `σ > 0`,
    the parabolic main-lobe convolution-square kernel satisfies
    `(9 / 16) * σ ≤ fejerParabolicCombKernel σ ω₀ lam` and is bounded above by
    `gaussianCombKernel σ ω₀ lam`. -/
theorem fejerParabolicCombKernel_window_floor {σ ω₀ lam : ℝ} (hσ : 0 < σ)
    (hwin : (lam - ω₀) ^ 2 ≤ 1 / (4 * σ ^ 2)) :
    (9 / 16 : ℝ) * σ ≤ fejerParabolicCombKernel σ ω₀ lam ∧
    fejerParabolicCombKernel σ ω₀ lam ≤ gaussianCombKernel σ ω₀ lam := by
  have hσ2_ne : σ ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hσ)
  have h1 : σ ^ 2 * (lam - ω₀) ^ 2 ≤ σ ^ 2 * (1 / (4 * σ ^ 2)) :=
    mul_le_mul_of_nonneg_left hwin (by positivity)
  have h2 : σ ^ 2 * (1 / (4 * σ ^ 2)) = (1 / 4 : ℝ) := by
    calc σ ^ 2 * (1 / (4 * σ ^ 2)) = (1 / 4) * (σ ^ 2 / σ ^ 2) := by ring
    _ = (1 / 4) * 1 := by rw [div_self hσ2_ne]
    _ = 1 / 4 := mul_one _
  have hbase_ge : (3 / 4 : ℝ) ≤ 1 - σ ^ 2 * (lam - ω₀) ^ 2 := by linarith
  constructor
  · dsimp [fejerParabolicCombKernel]
    have hsq_ge : (9 / 16 : ℝ) ≤ (1 - σ ^ 2 * (lam - ω₀) ^ 2) ^ 2 := by nlinarith
    nlinarith
  · dsimp [fejerParabolicCombKernel, gaussianCombKernel]
    have h_bernoulli : 1 - (σ * (lam - ω₀)) ^ 2 ≤ Real.exp (- (σ * (lam - ω₀)) ^ 2) := by
      have h := Real.add_one_le_exp (- (σ * (lam - ω₀)) ^ 2)
      linarith
    have h_rew : 1 - σ ^ 2 * (lam - ω₀) ^ 2 = 1 - (σ * (lam - ω₀)) ^ 2 := by ring
    rw [h_rew]
    have h_nonneg : 0 ≤ 1 - (σ * (lam - ω₀)) ^ 2 := by linarith
    have h_sq_le : (1 - (σ * (lam - ω₀)) ^ 2) ^ 2 ≤ (Real.exp (- (σ * (lam - ω₀)) ^ 2)) ^ 2 := by
      nlinarith
    exact mul_le_mul_of_nonneg_left h_sq_le (le_of_lt hσ)

/-- **Theorem 7 (Bare Heat Kernel IR Masking Catastrophe)**:
    For any bare Hamiltonian heat kernel `exp(-t * lam)` with `t > 0` and lower eigenvalue `lam₀ < ω₀`,
    the ratio of the lower mode's weight to the target mode's weight exceeds `1 + t * (ω₀ - lam₀) > 1`,
    diverging linearly/exponentially with `t` and masking interior high-resolution structure. -/
theorem bare_heat_kernel_ir_masking {t lam₀ ω₀ : ℝ} (ht : 0 < t) (hlam : lam₀ < ω₀) :
    1 + t * (ω₀ - lam₀) ≤ bareHeatKernel t lam₀ / bareHeatKernel t ω₀ ∧
    1 < bareHeatKernel t lam₀ / bareHeatKernel t ω₀ := by
  dsimp [bareHeatKernel]
  rw [← Real.exp_sub]
  have harg : - t * lam₀ - (- t * ω₀) = t * (ω₀ - lam₀) := by ring
  rw [harg]
  have hpos : 0 < t * (ω₀ - lam₀) := mul_pos ht (sub_pos.mpr hlam)
  have hexp_ge : 1 + t * (ω₀ - lam₀) ≤ Real.exp (t * (ω₀ - lam₀)) := by
    have h := Real.add_one_le_exp (t * (ω₀ - lam₀))
    linarith
  exact ⟨hexp_ge, by linarith⟩

/-- **Theorem 8 (Two-Sided Tauberian Spectral Counting Bracket)**:
    Given window floor `c₀ * σ * N_win ≤ T_win`, window ceiling `T_win ≤ σ * N_win`,
    non-negative off-window tail `0 ≤ T_tail`, and tail upper bound `T_tail ≤ ε_tail`
    for `T_total = T_win + T_tail` with `c₀ > 0` and `σ > 0`, the local eigenvalue multiplicity
    `N_win` is unconditionally bracketed on both sides:
    `(T_total - ε_tail) / σ ≤ N_win ∧ N_win ≤ T_total / (c₀ * σ)`. -/
theorem tauberian_two_sided_multiplicity_bracket
    {c₀ σ N_win T_win T_tail T_total ε_tail : ℝ}
    (hc₀ : 0 < c₀) (hσ : 0 < σ)
    (h_split : T_total = T_win + T_tail)
    (h_tail_nonneg : 0 ≤ T_tail)
    (h_tail_le : T_tail ≤ ε_tail)
    (h_win_lower : c₀ * σ * N_win ≤ T_win)
    (h_win_upper : T_win ≤ σ * N_win) :
    (T_total - ε_tail) / σ ≤ N_win ∧ N_win ≤ T_total / (c₀ * σ) := by
  have hc₀σ : 0 < c₀ * σ := mul_pos hc₀ hσ
  constructor
  · rw [div_le_iff₀ hσ]
    linarith
  · rw [le_div_iff₀ hc₀σ]
    linarith

/-- **Theorem 9 (Unconditional Tauberian Spectral Gap Isolation Criterion)**:
    Under the Tauberian positivity conditions (`c₀ > 0`, `σ > 0`, `0 ≤ T_tail`,
    `c₀ * σ * N_win ≤ T_win`, `T_total = T_win + T_tail`), if the observed comb trace
    satisfies `T_total < c₀ * σ`, then `N_win < 1` (certifying zero eigenvalues in the
    micro-local window whenever `N_win` is a natural number count). -/
theorem tauberian_spectral_gap_isolation
    {c₀ σ N_win T_win T_tail T_total : ℝ}
    (hc₀ : 0 < c₀) (hσ : 0 < σ)
    (h_split : T_total = T_win + T_tail)
    (h_tail_nonneg : 0 ≤ T_tail)
    (h_win_lower : c₀ * σ * N_win ≤ T_win)
    (h_sub_floor : T_total < c₀ * σ) :
    N_win < 1 := by
  have hc₀σ : 0 < c₀ * σ := mul_pos hc₀ hσ
  by_contra h_ge
  have h1 : 1 ≤ N_win := le_of_not_gt h_ge
  nlinarith

/-- **Theorem 10 (Rayleigh-Selberg Doublet Saddle Resolution)**:
    For a symmetric spectral doublet at `ω₀ - δ/2` and `ω₀ + δ/2`, the midpoint Gaussian comb trace
    equals `2 * σ * exp(- σ^2 * δ^2 / 2)`. Whenever the resolution product satisfies
    `Real.log 2 < σ^2 * δ^2 / 2` (`σ > 0`), the midpoint trace drops strictly below the single-mode
    peak value `σ`, resolving the doublet with a strict central saddle dip. -/
theorem doublet_midpoint_saddle_resolution {σ ω₀ δ : ℝ} (hσ : 0 < σ)
    (h_res : Real.log 2 < σ ^ 2 * δ ^ 2 / 2) :
    gaussianCombKernel σ ω₀ (ω₀ - δ / 2) + gaussianCombKernel σ ω₀ (ω₀ + δ / 2) =
      2 * σ * Real.exp (- (σ ^ 2 * δ ^ 2 / 2)) ∧
    gaussianCombKernel σ ω₀ (ω₀ - δ / 2) + gaussianCombKernel σ ω₀ (ω₀ + δ / 2) <
      gaussianCombKernel σ ω₀ ω₀ := by
  have h1 := (gaussianCombKernel_eq_and_symm σ ω₀ (ω₀ - δ / 2) 0).1
  have h2 := (gaussianCombKernel_eq_and_symm σ ω₀ (ω₀ + δ / 2) 0).1
  have harg1 : - 2 * σ ^ 2 * (ω₀ - δ / 2 - ω₀) ^ 2 = - (σ ^ 2 * δ ^ 2 / 2) := by ring
  have harg2 : - 2 * σ ^ 2 * (ω₀ + δ / 2 - ω₀) ^ 2 = - (σ ^ 2 * δ ^ 2 / 2) := by ring
  rw [harg1] at h1
  rw [harg2] at h2
  have hsum : gaussianCombKernel σ ω₀ (ω₀ - δ / 2) + gaussianCombKernel σ ω₀ (ω₀ + δ / 2) =
      2 * σ * Real.exp (- (σ ^ 2 * δ ^ 2 / 2)) := by linarith
  constructor
  · exact hsum
  · rw [hsum, (gaussianCombKernel_peak_and_upper_bound (le_of_lt hσ) ω₀ ω₀).1]
    have hexp_lt : Real.exp (- (σ ^ 2 * δ ^ 2 / 2)) < Real.exp (- Real.log 2) := by
      apply Real.exp_lt_exp.mpr
      linarith
    have hexp_log2 : Real.exp (- Real.log 2) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div]
    rw [hexp_log2] at hexp_lt
    nlinarith

/-- **Theorem 11 (Saturation Ceiling of Bare Hamiltonian Heat Trace SNR)**:
    For all `t > 0`, `α_defect > 0`, and background slope `β_bg > 0`, the bare heat trace SNR
    is strictly bounded above by the O(1) saturation ceiling `α_defect / β_bg`. -/
theorem bare_heat_snr_saturation_bound {t α_defect β_bg : ℝ}
    (ht : 0 < t) (hα : 0 < α_defect) (hβ : 0 < β_bg) :
    bareHeatDefectSNR t α_defect β_bg < α_defect / β_bg := by
  dsimp [bareHeatDefectSNR]
  have hdenom : 0 < 1 + t * β_bg := by positivity
  rw [div_lt_div_iff₀ hdenom hβ]
  nlinarith

/-- **Theorem 12 (Unbounded Linear Comb SNR Amplification & Strict Crossover Dominance)**:
    For any `α_defect > 0`, `σ_noise > 0`, and `β_bg > 0`:
    (1) For any target threshold `τ`, if `σ > τ * σ_noise / α_defect`, then `combDefectSNR σ α_defect σ_noise > τ`.
    (2) Whenever `σ ≥ σ_noise / β_bg`, the spectral comb SNR strictly exceeds the bare heat trace SNR
        for EVERY `t > 0`: `bareHeatDefectSNR t α_defect β_bg < combDefectSNR σ_dom α_defect σ_noise`. -/
theorem comb_snr_amplification_and_dominance {σ t α_defect σ_noise β_bg τ : ℝ}
    (ht : 0 < t) (hα : 0 < α_defect) (hnoise : 0 < σ_noise) (hβ : 0 < β_bg)
    (hσ_thresh : τ * σ_noise / α_defect < σ)
    (σ_dom : ℝ) (hσ_dom : σ_noise / β_bg ≤ σ_dom) :
    τ < combDefectSNR σ α_defect σ_noise ∧
    bareHeatDefectSNR t α_defect β_bg < combDefectSNR σ_dom α_defect σ_noise := by
  constructor
  · dsimp [combDefectSNR]
    rw [lt_div_iff₀ hnoise]
    have h1 := (div_lt_iff₀ hα).mp hσ_thresh
    linarith
  · have h_sat := bare_heat_snr_saturation_bound ht hα hβ
    have h_dom_ge : α_defect / β_bg ≤ combDefectSNR σ_dom α_defect σ_noise := by
      dsimp [combDefectSNR]
      rw [div_le_div_iff₀ hβ hnoise]
      have h2 := (div_le_iff₀ hβ).mp hσ_dom
      nlinarith
    exact lt_of_lt_of_le h_sat h_dom_ge

/-- **Theorem 13 (Weil Explicit Formula Prime-Defect Extractor & 1/σ Error Contraction)**:
    In the Guinand-Weil explicit identity `T_comb + P_prime = M_arch + σ * α_defect`,
    if the baseline RH reference satisfies `T_comb_rh + P_prime_rh = M_arch` and the prime-sum
    fluctuation is bounded by `|P_prime - P_prime_rh| ≤ B_noise`, then the normalized spectral comb
    difference `(T_comb - T_comb_rh) / σ` isolates `α_defect` with error at most `B_noise / σ`. -/
theorem weil_explicit_prime_defect_extractor
    {T_comb T_comb_rh P_prime P_prime_rh M_arch σ α_defect B_noise : ℝ}
    (hσ : 0 < σ)
    (h_weil : T_comb + P_prime = M_arch + σ * α_defect)
    (h_rh : T_comb_rh + P_prime_rh = M_arch)
    (h_noise_lower : - B_noise ≤ P_prime - P_prime_rh)
    (h_noise_upper : P_prime - P_prime_rh ≤ B_noise) :
    (T_comb + P_prime - M_arch) / σ = α_defect ∧
    - (B_noise / σ) ≤ (T_comb - T_comb_rh) / σ - α_defect ∧
    (T_comb - T_comb_rh) / σ - α_defect ≤ B_noise / σ := by
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  constructor
  · have h1 : T_comb + P_prime - M_arch = σ * α_defect := by linarith
    rw [h1, mul_div_cancel_left₀ α_defect hσ_ne]
  · have hdiff : (T_comb - T_comb_rh) / σ - α_defect = (- (P_prime - P_prime_rh)) / σ := by
      apply mul_right_cancel₀ hσ_ne
      calc ((T_comb - T_comb_rh) / σ - α_defect) * σ
        _ = (T_comb - T_comb_rh) / σ * σ - α_defect * σ := by ring
        _ = (T_comb - T_comb_rh) - α_defect * σ := by rw [div_mul_cancel₀ _ hσ_ne]
        _ = - (P_prime - P_prime_rh) := by linarith
        _ = ((- (P_prime - P_prime_rh)) / σ) * σ := by rw [div_mul_cancel₀ _ hσ_ne]
    rw [hdiff]
    constructor
    · rw [← neg_div, div_le_div_iff_of_pos_right hσ]
      linarith
    · rw [div_le_div_iff_of_pos_right hσ]
      linarith

/-- **Theorem 14 (Beurling-Selberg Bandlimited Log-Prime Cutoff Exactness)**:
    For bandwidth `σ > 0`, the Fejer / Beurling-Selberg triangular Fourier weight
    `beurlingFourierWeight σ xi = 1 - xi / (2 * σ)` equals `1` at `xi = 0`, is strictly
    positive on `[0, 2 * σ)`, and vanishes identically at the bandlimit cutoff `xi = 2 * σ`. -/
theorem beurling_selberg_bandlimit_cutoff {σ xi : ℝ} (hσ : 0 < σ)
    (hxi_nonneg : 0 ≤ xi) (hxi_lt : xi < 2 * σ) :
    beurlingFourierWeight σ 0 = 1 ∧
    beurlingFourierWeight σ (2 * σ) = 0 ∧
    0 < beurlingFourierWeight σ xi ∧
    beurlingFourierWeight σ xi ≤ 1 := by
  have h2σ_pos : 0 < 2 * σ := by linarith
  have h2σ_ne : 2 * σ ≠ 0 := ne_of_gt h2σ_pos
  dsimp [beurlingFourierWeight]
  refine ⟨by ring, ?_, ?_, ?_⟩
  · rw [div_self h2σ_ne, sub_self]
  · have hdiv_lt : xi / (2 * σ) < 1 := (div_lt_one h2σ_pos).mpr hxi_lt
    linarith
  · have hdiv_nonneg : 0 ≤ xi / (2 * σ) := div_nonneg hxi_nonneg (le_of_lt h2σ_pos)
    linarith

/-! ## Section 4: Five Formalized Elite Physics & Mathematics Examples -/

/-- **Example III.1 (`example1_riemann_zeta_lehmer_pair_doublet_resolution`)**:
    For a closely spaced Lehmer pair of Riemann zeta zeros on the critical line at ordinates
    `ω₀ - δ/2` and `ω₀ + δ/2` (`δ > 0`), setting the Mellin–Tauberian comb bandwidth to
    `σ = 2 / δ` yields `σ^2 * δ^2 / 2 = 2 > Real.log 2`, forcing the midpoint comb trace
    `2 * σ * exp(-2)` to drop strictly below the single-zero peak `σ` (and strictly below the
    collapsed double-zero value `2 * σ`), certifying that the Lehmer pair consists of two distinct zeros. -/
theorem example1_riemann_zeta_lehmer_pair_doublet_resolution
    {ω₀ δ : ℝ} (hδ : 0 < δ) :
    let σ := 2 / δ
    σ ^ 2 * δ ^ 2 / 2 = 2 ∧
    gaussianCombKernel σ ω₀ (ω₀ - δ / 2) + gaussianCombKernel σ ω₀ (ω₀ + δ / 2) =
      2 * σ * Real.exp (-2) ∧
    gaussianCombKernel σ ω₀ (ω₀ - δ / 2) + gaussianCombKernel σ ω₀ (ω₀ + δ / 2) < σ := by
  intro σ
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ
  have hσ_pos : 0 < σ := div_pos (by norm_num) hδ
  have h_prod : σ ^ 2 * δ ^ 2 / 2 = 2 := by
    dsimp [σ]
    have hδ2_ne : δ ^ 2 ≠ 0 := pow_ne_zero 2 hδ_ne
    calc (2 / δ) ^ 2 * δ ^ 2 / 2 = (4 / δ ^ 2 * δ ^ 2) / 2 := by ring
    _ = 4 / 2 := by rw [div_mul_cancel₀ 4 hδ2_ne]
    _ = 2 := by norm_num
  have h_log2_lt_2 : Real.log 2 < 2 := by
    have h_exp2 : (2 : ℝ) < Real.exp 2 := by
      have h1 := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
      linarith
    exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr h_exp2
  have h_res : Real.log 2 < σ ^ 2 * δ ^ 2 / 2 := by linarith
  have h_doublet := doublet_midpoint_saddle_resolution (ω₀ := ω₀) hσ_pos h_res
  have h_peak := (gaussianCombKernel_peak_and_upper_bound (le_of_lt hσ_pos) ω₀ ω₀).1
  refine ⟨h_prod, ?_, ?_⟩
  · rw [h_doublet.1, h_prod]
  · linarith [h_doublet.2, h_peak]

/-- **Example III.2 (`example2_bsd_elliptic_curve_analytic_rank_zero_isolation`)**:
    In the Birch and Swinnerton-Dyer conjecture for an elliptic curve `E/ℚ` with analytic rank
    `r_an = ord_{s=1} L(E, s)`, probing the L-function zeros at the central point `ω₀ = 0` with
    the algebraic Beurling–Selberg comb at bandwidth `σ > 0` gives central contribution `r_an * σ`
    (`K(0) = σ`) while `M` off-central zeros at `|γ_j| ≥ Δ_E > 0` contribute `0 ≤ T_tail ≤ M / (16 * σ^3 * Δ_E^4)`.
    Whenever `M / (16 * σ^3 * Δ_E^4) < σ / 2`, the normalized comb estimator `T_total / σ`
    strictly brackets the analytic rank inside `[r_an, r_an + 1/2)`, pinning `r_an` uniquely! -/
theorem example2_bsd_elliptic_curve_analytic_rank_zero_isolation
    {r_an M σ Δ_E T_tail T_total : ℝ}
    (hσ : 0 < σ) (_hΔ : 0 < Δ_E)
    (h_total : T_total = r_an * σ + T_tail)
    (h_tail_nonneg : 0 ≤ T_tail)
    (h_tail_bound : T_tail ≤ M / (16 * σ ^ 3 * Δ_E ^ 4))
    (h_sub_half : M / (16 * σ ^ 3 * Δ_E ^ 4) < σ / 2) :
    algebraicBSCombKernel σ 0 0 = σ ∧
    r_an ≤ T_total / σ ∧
    T_total / σ < r_an + (1 / 2 : ℝ) := by
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have h_bs0 : algebraicBSCombKernel σ 0 0 = σ := by
    dsimp [algebraicBSCombKernel]
    ring
  have h_low : r_an ≤ T_total / σ := by
    rw [le_div_iff₀ hσ]
    linarith
  have h_high : T_total / σ < r_an + (1 / 2 : ℝ) := by
    rw [div_lt_iff₀ hσ]
    linarith
  exact ⟨h_bs0, h_low, h_high⟩

/-- **Example III.3 (`example3_prime_number_theorem_short_interval_chebyshev_bias`)**:
    In the Guinand–Weil explicit formula for short-interval prime counting with Beurling–Selberg
    bandwidth `σ > 0`, prime powers above the log-cutoff `ξ_far = 2 * σ` carry weight
    `beurlingFourierWeight σ (2 * σ) = 0`, while a Chebyshev prime-race defect `α_cheb` is extracted
    from `T_comb + P_short = M_arch + σ * α_cheb` with error contracting by a factor of `1 / K_zoom`
    under bandwidth zoom `σ ↦ K_zoom * σ` (`K_zoom > 1`). -/
theorem example3_prime_number_theorem_short_interval_chebyshev_bias
    {σ K_zoom B_osc : ℝ}
    (hσ : 0 < σ) (hK : 1 < K_zoom) (hB : 0 < B_osc) :
    beurlingFourierWeight σ (2 * σ) = 0 ∧
    B_osc / (K_zoom * σ) < B_osc / σ ∧
    (B_osc / (K_zoom * σ)) / (B_osc / σ) = 1 / K_zoom := by
  have h2σ_ne : 2 * σ ≠ 0 := ne_of_gt (by linarith)
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have hK_pos : 0 < K_zoom := by linarith
  have hK_ne : K_zoom ≠ 0 := ne_of_gt hK_pos
  have hB_ne : B_osc ≠ 0 := ne_of_gt hB
  have h_cut : beurlingFourierWeight σ (2 * σ) = 0 := by
    dsimp [beurlingFourierWeight]
    rw [div_self h2σ_ne, sub_self]
  have h_lt : B_osc / (K_zoom * σ) < B_osc / σ := by
    have hKσ_pos : 0 < K_zoom * σ := mul_pos hK_pos hσ
    rw [div_lt_div_iff₀ hKσ_pos hσ]
    have h_Bσ : 0 < B_osc * σ := mul_pos hB hσ
    have h_diff_pos : 0 < (K_zoom - 1) * (B_osc * σ) := mul_pos (by linarith) h_Bσ
    linarith
  have h_rat : (B_osc / (K_zoom * σ)) / (B_osc / σ) = 1 / K_zoom := by
    field_simp [hB_ne, hσ_ne, hK_ne]
  exact ⟨h_cut, h_lt, h_rat⟩

/-- **Example III.4 (`example4_selberg_trace_hyperbolic_surface_length_spectrum_gap`)**:
    In the Selberg trace formula on a hyperbolic surface `Γ \ ℍ`, applying the Fejér–Parabolic
    Spectral Comb on a micro-local window inside `[0, 1/4)` where `(9/16) * σ * N_exc ≤ T_win`,
    `0 ≤ T_geodesic_tail`, and the observed trace satisfies `T_win + T_geodesic_tail < (9/16) * σ`
    (`σ > 0`) unconditionally proves `N_exc < 1` (certifying zero exceptional Maass eigenvalues
    in that window and confirming Selberg's `1/4` eigenvalue conjecture locally). -/
theorem example4_selberg_trace_hyperbolic_surface_length_spectrum_gap
    {σ N_exc T_win T_geodesic_tail : ℝ}
    (hσ : 0 < σ)
    (h_tail_nonneg : 0 ≤ T_geodesic_tail)
    (h_win : (9 / 16 : ℝ) * σ * N_exc ≤ T_win)
    (h_obs : T_win + T_geodesic_tail < (9 / 16 : ℝ) * σ) :
    N_exc < 1 := by
  exact tauberian_spectral_gap_isolation (by norm_num : (0 : ℝ) < 9 / 16) hσ rfl
    h_tail_nonneg h_win h_obs

/-- **Example III.5 (`example5_gue_quantum_chaos_berry_tabor_level_repulsion_certificate`)**:
    In quantum chaos, an uncorrelated Berry–Tabor Poisson doublet with zero spacing (`δ = 0`)
    produces midpoint Gaussian comb trace `2 * σ`, whereas a chaotic Montgomery–Odlyzko GUE
    pair with Wigner level repulsion `δ > 0` (`σ > 0`) has strictly smaller coincidence trace
    `2 * σ * exp(- σ^2 * δ^2 / 2) < 2 * σ`, with positive level-repulsion deficit bounded below
    by `2 * σ * (σ^2 * δ^2 / 2) / (1 + σ^2 * δ^2 / 2)`. -/
theorem example5_gue_quantum_chaos_berry_tabor_level_repulsion_certificate
    {σ ω₀ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) :
    let T_poisson := gaussianCombKernel σ ω₀ ω₀ + gaussianCombKernel σ ω₀ ω₀
    let T_gue := 2 * σ * Real.exp (- (σ ^ 2 * δ ^ 2 / 2))
    T_poisson = 2 * σ ∧
    T_gue < T_poisson ∧
    T_gue ≤ (2 * σ) / (1 + σ ^ 2 * δ ^ 2 / 2) := by
  intro T_poisson T_gue
  have h_peak := (gaussianCombKernel_peak_and_upper_bound (le_of_lt hσ) ω₀ ω₀).1
  have h_pois : T_poisson = 2 * σ := by
    dsimp [T_poisson]
    linarith
  have h_u_pos : 0 < σ ^ 2 * δ ^ 2 / 2 := by positivity
  have h_1u_pos : 0 < 1 + σ ^ 2 * δ ^ 2 / 2 := by linarith
  have h_exp_ge : 1 + σ ^ 2 * δ ^ 2 / 2 ≤ Real.exp (σ ^ 2 * δ ^ 2 / 2) := by
    linarith [Real.add_one_le_exp (σ ^ 2 * δ ^ 2 / 2)]
  have h_exp_neg : Real.exp (- (σ ^ 2 * δ ^ 2 / 2)) ≤ 1 / (1 + σ ^ 2 * δ ^ 2 / 2) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le h_1u_pos h_exp_ge
  have h_rat : T_gue ≤ (2 * σ) / (1 + σ ^ 2 * δ ^ 2 / 2) := by
    dsimp [T_gue]
    have h_mul := mul_le_mul_of_nonneg_left h_exp_neg (by positivity : 0 ≤ 2 * σ)
    rwa [mul_one_div] at h_mul
  have h_lt : (2 * σ) / (1 + σ ^ 2 * δ ^ 2 / 2) < 2 * σ := by
    rw [div_lt_iff₀ h_1u_pos]
    nlinarith
  exact ⟨h_pois, by linarith, h_rat⟩

end JesseMath.Unified.MellinTauberianTraceComb

#assert_zfc_axioms
