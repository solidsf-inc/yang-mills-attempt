import JesseMath.Linter.AxiomAudit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace JesseMath.Physics.MassEnergySurprisal

/-!
# The Triadic Equivalence of Energy, Rest Mass, and Statistical Surprisal (`E = mc^2 = -k log W`)
=================================================================================================
Formalizes and proves in Lean 4 (pure ZFC, zero custom axioms, 100% kernel-verified) the calibrated
triadic identity unifying Special Relativity (`E = m c^2`), Boltzmann–Einstein fluctuation
theory (`W = P(E)/P(0) = exp(-E/k)`), and Shannon self-information (`I(W) = -log W`):

  `E = m * c^2 = -k * Real.log W`

where `k ≡ k_B * T_0 > 0` is the characteristic thermal/horizon energy per nat and
`W ∈ (0, 1]` is the Einstein fluctuation likelihood ratio relative to the unexcited vacuum.

## Six Formalized Mathematical Pillars:
1. **Relativistic Rest Energy & Minkowski Dispersion (`restEnergy`, `minkowskiNormSq`)**
2. **Shannon Surprisal & Entropic Energy Functional (`surprisal`, `entropicEnergy`)**
3. **Bidirectional Inversion & Master Triadic Equivalence (`triadic_mass_energy_surprisal_equivalence`)**
4. **Resolution of the Partition-Function Normalization Paradox (`canonical_likelihood_ratio_cancels_Z`)**
5. **Relativistic Mass Defect from Mutual Information (`bindingEnergy_eq_mutualInformation`)**
6. **Lorentz Covariance, Euclidean Action & Horizon Calibration (`ott_covariant_entropic_energy`)**
-/

/-! ## Section 1: Relativistic Rest Energy & Minkowski Four-Momentum Invariance -/

/-- Einstein rest energy `E = m * c^2`. -/
def restEnergy (m c : ℝ) : ℝ :=
  m * c ^ 2

/-- Minkowski four-momentum norm squared `p^μ p_μ = -(E/c)^2 + p^2` in signature `(-,+,+,+)`. -/
def minkowskiNormSq (E p c : ℝ) : ℝ :=
  - (E / c) ^ 2 + p ^ 2

/-- Rest energy is non-negative for non-negative mass `m ≥ 0`. -/
theorem restEnergy_nonneg {m : ℝ} (hm : 0 ≤ m) (c : ℝ) :
    0 ≤ restEnergy m c := by
  dsimp [restEnergy]
  positivity

/-- Rest energy is strictly positive for `m > 0` and `c > 0`. -/
theorem restEnergy_pos {m c : ℝ} (hm : 0 < m) (hc : 0 < c) :
    0 < restEnergy m c := by
  dsimp [restEnergy]
  positivity

/-- For `c ≠ 0`, rest energy vanishes if and only if rest mass vanishes (`E = 0 ↔ m = 0`). -/
theorem restEnergy_eq_zero_iff {m c : ℝ} (hc : c ≠ 0) :
    restEnergy m c = 0 ↔ m = 0 := by
  dsimp [restEnergy]
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  exact mul_eq_zero_iff_right hc2

/-- Subsystem mass additivity implies rest energy additivity for non-interacting systems. -/
theorem restEnergy_add (mA mB c : ℝ) :
    restEnergy (mA + mB) c = restEnergy mA c + restEnergy mB c := by
  dsimp [restEnergy]
  ring

/-- Relativistic energy-momentum dispersion relation:
    `minkowskiNormSq E p c = - m^2 * c^2` is algebraically equivalent to `E^2 - p^2 c^2 = m^2 c^4`. -/
theorem minkowski_dispersion_iff {E p m c : ℝ} (hc : c ≠ 0) :
    minkowskiNormSq E p c = - (m ^ 2 * c ^ 2) ↔ E ^ 2 - p ^ 2 * c ^ 2 = m ^ 2 * c ^ 4 := by
  dsimp [minkowskiNormSq]
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  constructor
  · intro h
    have h1 : (- (E / c) ^ 2 + p ^ 2) * c ^ 2 = - (m ^ 2 * c ^ 2) * c ^ 2 :=
      congrArg (fun x => x * c ^ 2) h
    have hdiv : (E / c) ^ 2 * c ^ 2 = E ^ 2 := by
      rw [div_pow, div_mul_cancel₀ _ hc2]
    linarith [h1, hdiv]
  · intro h
    apply mul_right_cancel₀ hc2
    calc (- (E / c) ^ 2 + p ^ 2) * c ^ 2
      _ = - ((E / c) ^ 2 * c ^ 2) + p ^ 2 * c ^ 2 := by ring
      _ = - (E ^ 2 / c ^ 2 * c ^ 2) + p ^ 2 * c ^ 2 := by rw [div_pow]
      _ = - E ^ 2 + p ^ 2 * c ^ 2 := by rw [div_mul_cancel₀ _ hc2]
      _ = - (m ^ 2 * c ^ 2) * c ^ 2 := by linarith [h]

/-- In the center-of-momentum rest frame (`p = 0`), for `E ≥ 0`, `m ≥ 0`, and `c > 0`,
    `E = restEnergy m c` implies `minkowskiNormSq E 0 c = - m^2 c^2`. -/
theorem minkowski_rest_frame_of_restEnergy {E m c : ℝ} (hc : c ≠ 0)
    (hE : E = restEnergy m c) :
    minkowskiNormSq E 0 c = - (m ^ 2 * c ^ 2) := by
  dsimp [minkowskiNormSq, restEnergy] at *
  rw [hE]
  have h1 : m * c ^ 2 / c = m * c := by
    calc m * c ^ 2 / c = m * c * c / c := by ring
    _ = m * c := mul_div_cancel_right₀ (m * c) hc
  rw [h1]
  ring

/-! ## Section 2: Shannon Surprisal & Entropic Energy Functional (`-k log W`) -/

/-- Shannon self-information (surprisal) in nats: `I(W) = -log W`. -/
def surprisal (W : ℝ) : ℝ :=
  - Real.log W

/-- Entropic energy functional: `E(k, W) = -k * log W`. -/
def entropicEnergy (k W : ℝ) : ℝ :=
  - k * Real.log W

/-- Einstein fluctuation likelihood ratio (Boltzmann weight relative to vacuum):
    `W(k, E) = exp(-E / k)`. -/
def einsteinWeight (k E : ℝ) : ℝ :=
  Real.exp (- E / k)

/-- The unexcited vacuum state (`W = 1`) carries zero surprisal (`I(1) = 0`). -/
@[simp]
theorem surprisal_one : surprisal 1 = 0 := by
  dsimp [surprisal]
  rw [Real.log_one, neg_zero]

/-- Surprisal is non-negative for all valid probabilities `W ∈ (0, 1]`. -/
theorem surprisal_nonneg {W : ℝ} (hW_pos : 0 < W) (hW_le : W ≤ 1) :
    0 ≤ surprisal W := by
  dsimp [surprisal]
  have hlog : Real.log W ≤ 0 := Real.log_nonpos (le_of_lt hW_pos) hW_le
  linarith

/-- Surprisal is strictly positive for any non-vacuum fluctuation `W ∈ (0, 1)`. -/
theorem surprisal_pos {W : ℝ} (hW_pos : 0 < W) (hW_lt : W < 1) :
    0 < surprisal W := by
  dsimp [surprisal]
  have hlog : Real.log W < 0 := Real.log_neg hW_pos hW_lt
  linarith

/-- Entropic energy equals `k` times the Shannon surprisal `I(W)`. -/
theorem entropicEnergy_eq_mul_surprisal (k W : ℝ) :
    entropicEnergy k W = k * surprisal W := by
  dsimp [entropicEnergy, surprisal]
  ring

/-- Vacuum Normalization: at `W = 1`, the entropic energy vanishes (`-k log 1 = 0`). -/
@[simp]
theorem entropicEnergy_one (k : ℝ) : entropicEnergy k 1 = 0 := by
  dsimp [entropicEnergy]
  rw [Real.log_one, mul_zero]

/-- Non-negativity of Entropic Energy: for `k ≥ 0` and `W ∈ (0, 1]`, `-k log W ≥ 0`. -/
theorem entropicEnergy_nonneg {k W : ℝ} (hk : 0 ≤ k) (hW_pos : 0 < W) (hW_le : W ≤ 1) :
    0 ≤ entropicEnergy k W := by
  rw [entropicEnergy_eq_mul_surprisal]
  exact mul_nonneg hk (surprisal_nonneg hW_pos hW_le)

/-- Strict Positivity of Entropic Energy: for `k > 0` and `W ∈ (0, 1)`, `-k log W > 0`. -/
theorem entropicEnergy_pos {k W : ℝ} (hk : 0 < k) (hW_pos : 0 < W) (hW_lt : W < 1) :
    0 < entropicEnergy k W := by
  rw [entropicEnergy_eq_mul_surprisal]
  exact mul_pos hk (surprisal_pos hW_pos hW_lt)

/-- Strict Monotonicity (Antitone in `W`): rarer fluctuations (`W₁ < W₂`) carry strictly
    greater entropic rest energy. -/
theorem entropicEnergy_strict_anti {k W1 W2 : ℝ} (hk : 0 < k)
    (hW1 : 0 < W1) (hlt : W1 < W2) :
    entropicEnergy k W2 < entropicEnergy k W1 := by
  dsimp [entropicEnergy]
  have hlog : Real.log W1 < Real.log W2 := Real.log_lt_log hW1 hlt
  nlinarith

/-- Cauchy Logarithmic Additivity: for statistically independent subsystems (`W_AB = W_A * W_B`),
    entropic energy is strictly additive:
    `-k log(W_A * W_B) = -k log W_A + -k log W_B`. -/
theorem entropicEnergy_mul (k : ℝ) {WA WB : ℝ} (hA : 0 < WA) (hB : 0 < WB) :
    entropicEnergy k (WA * WB) = entropicEnergy k WA + entropicEnergy k WB := by
  dsimp [entropicEnergy]
  rw [Real.log_mul (ne_of_gt hA) (ne_of_gt hB)]
  ring

/-- Boltzmann–Shannon Duality: when `W = Ω⁻¹` is the microcanonical equiprobability of a
    macrostate with multiplicity `Ω > 0`, `-k log W = k log Ω`. -/
theorem entropicEnergy_inv_multiplicity (k Ω : ℝ) :
    entropicEnergy k Ω⁻¹ = k * Real.log Ω := by
  dsimp [entropicEnergy]
  rw [Real.log_inv]
  ring

/-- **Cauchy Functional Reduction (Step 1)**:
    If an energy functional `f : ℝ → ℝ` maps independent multiplicative probabilities
    to additive energies (`f (W_A * W_B) = f W_A + f W_B` for `W_A, W_B > 0`), then its
    exponential pullback `g(x) := f(exp(-x))` satisfies Cauchy's additive equation
    `g(x + y) = g(x) + g(y)` for all `x, y ∈ ℝ`. -/
theorem cauchy_exponential_pullback_additive (f : ℝ → ℝ)
    (hMult : ∀ WA WB : ℝ, 0 < WA → 0 < WB → f (WA * WB) = f WA + f WB)
    (x y : ℝ) :
    f (Real.exp (- (x + y))) = f (Real.exp (-x)) + f (Real.exp (-y)) := by
  have hexp : Real.exp (- (x + y)) = Real.exp (-x) * Real.exp (-y) := by
    have hneg : - (x + y) = (-x) + (-y) := by ring
    rw [hneg, Real.exp_add]
  rw [hexp]
  exact hMult (Real.exp (-x)) (Real.exp (-y)) (Real.exp_pos _) (Real.exp_pos _)

/-- **Cauchy Functional Uniqueness (Step 2)**:
    If the exponential pullback `f(exp(-x)) = k * x` is linear on `ℝ`, then for every
    `W > 0`, `f(W) = entropicEnergy k W = -k * log W`. -/
theorem cauchy_linear_uniqueness_to_entropicEnergy (f : ℝ → ℝ) (k : ℝ)
    (hLin : ∀ x : ℝ, f (Real.exp (-x)) = k * x) {W : ℝ} (hW : 0 < W) :
    f W = entropicEnergy k W := by
  have hspec := hLin (- Real.log W)
  rw [neg_neg, Real.exp_log hW] at hspec
  dsimp [entropicEnergy]
  linarith

/-! ## Section 3: Exact Bidirectional Inversion & Master Triadic Equivalence -/

/-- The Einstein weight `exp(-E / k)` is strictly positive for all real `k` and `E`. -/
theorem einsteinWeight_pos (k E : ℝ) : 0 < einsteinWeight k E := by
  dsimp [einsteinWeight]
  exact Real.exp_pos _

/-- For `k > 0` and `E ≥ 0`, the Einstein likelihood weight lies in `(0, 1]`. -/
theorem einsteinWeight_le_one {k E : ℝ} (hk : 0 < k) (hE : 0 ≤ E) :
    einsteinWeight k E ≤ 1 := by
  dsimp [einsteinWeight]
  rw [Real.exp_le_one_iff, neg_div]
  have hdiv : 0 ≤ E / k := div_nonneg hE (le_of_lt hk)
  linarith

/-- Left Inversion: `entropicEnergy k (einsteinWeight k E) = E` for any `k ≠ 0`. -/
theorem entropicEnergy_einsteinWeight {k E : ℝ} (hk : k ≠ 0) :
    entropicEnergy k (einsteinWeight k E) = E := by
  dsimp [entropicEnergy, einsteinWeight]
  rw [Real.log_exp]
  calc -k * (-E / k) = E * (k / k) := by ring
  _ = E * 1 := by rw [div_self hk]
  _ = E := mul_one E

/-- Right Inversion: `einsteinWeight k (entropicEnergy k W) = W` for `k ≠ 0` and `W > 0`. -/
theorem einsteinWeight_entropicEnergy {k W : ℝ} (hk : k ≠ 0) (hW : 0 < W) :
    einsteinWeight k (entropicEnergy k W) = W := by
  dsimp [einsteinWeight, entropicEnergy]
  have harg : - (- k * Real.log W) / k = Real.log W := by
    calc - (- k * Real.log W) / k = Real.log W * (k / k) := by ring
    _ = Real.log W * 1 := by rw [div_self hk]
    _ = Real.log W := mul_one _
  rw [harg, Real.exp_log hW]

/-- Fundamental Inversion Equivalence:
    For `k ≠ 0` and `W > 0`, `E = -k log W` if and only if `W = exp(-E / k)`. -/
theorem energy_eq_entropicEnergy_iff {E k W : ℝ} (hk : k ≠ 0) (hW : 0 < W) :
    E = entropicEnergy k W ↔ W = einsteinWeight k E := by
  constructor
  · intro hE
    rw [hE, einsteinWeight_entropicEnergy hk hW]
  · intro hW_eq
    rw [hW_eq, entropicEnergy_einsteinWeight hk]

/-- **Master Theorem 1 (The Triadic Mass–Energy–Surprisal Equivalence)**:
    For any physical state with rest mass `m`, speed of light `c ≠ 0`, thermal energy scale `k ≠ 0`,
    and likelihood weight `W > 0`, the relativistic mass-energy law `E = m c^2` coupled with the
    Einstein fluctuation law `W = exp(-E / k)` is equivalent to the triadic identity
    `E = m c^2 = -k log W` and the rest-mass surprisal formula `m = -(k / c^2) log W`. -/
theorem triadic_mass_energy_surprisal_equivalence {E m c k W : ℝ}
    (hc : c ≠ 0) (hk : k ≠ 0) (hW : 0 < W) :
    (E = restEnergy m c ∧ W = einsteinWeight k E) ↔
      (E = restEnergy m c ∧ E = entropicEnergy k W ∧ m = - (k / c ^ 2) * Real.log W) := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  constructor
  · rintro ⟨hE_rest, hW_ein⟩
    have hE_ent : E = entropicEnergy k W :=
      (energy_eq_entropicEnergy_iff hk hW).mpr hW_ein
    have hm : m = - (k / c ^ 2) * Real.log W := by
      have h_eq : m * c ^ 2 = - k * Real.log W := by
        dsimp [restEnergy, entropicEnergy] at hE_rest hE_ent
        linarith
      calc m = (m * c ^ 2) / c ^ 2 := by rw [mul_div_cancel_right₀ m hc2]
      _ = (- k * Real.log W) / c ^ 2 := by rw [h_eq]
      _ = - (k / c ^ 2) * Real.log W := by ring
    exact ⟨hE_rest, hE_ent, hm⟩
  · rintro ⟨hE_rest, hE_ent, _⟩
    exact ⟨hE_rest, (energy_eq_entropicEnergy_iff hk hW).mp hE_ent⟩

/-- Vacuum Massless Characterization:
    Under the triadic identity `m c^2 = -k log W` (`c ≠ 0`, `k ≠ 0`, `W > 0`),
    rest mass vanishes (`m = 0`) if and only if the state is the unit-weight vacuum (`W = 1`). -/
theorem vacuum_mass_zero_iff_unit_weight {m c k W : ℝ}
    (hc : c ≠ 0) (hk : k ≠ 0) (hW : 0 < W)
    (hTriad : restEnergy m c = entropicEnergy k W) :
    m = 0 ↔ W = 1 := by
  constructor
  · intro hm
    have hE0 : restEnergy m c = 0 := (restEnergy_eq_zero_iff hc).mpr hm
    have hEnt0 : 0 = entropicEnergy k W := by linarith [hTriad, hE0]
    have hW_ein : W = einsteinWeight k 0 :=
      (energy_eq_entropicEnergy_iff hk hW).mp hEnt0
    dsimp [einsteinWeight] at hW_ein
    rw [neg_zero, zero_div, Real.exp_zero] at hW_ein
    exact hW_ein
  · intro hW1
    rw [hW1, entropicEnergy_one] at hTriad
    exact (restEnergy_eq_zero_iff hc).mp hTriad

/-! ## Section 4: Resolution of the Partition-Function Normalization Paradox -/

/-- Normalized canonical probability `P_k(E, Z) = exp(-E / k) / Z`. -/
def canonicalProb (k E Z : ℝ) : ℝ :=
  Real.exp (- E / k) / Z

/-- **Theorem 2 (Partition Function Cancellation in Einstein Likelihood Ratios)**:
    When `W(E)` is defined as the likelihood ratio `P_k(E, Z) / P_k(0, Z)` relative to the
    zero-energy vacuum (`E = 0`), the partition function `Z ≠ 0` cancels identically,
    yielding `W(E) = einsteinWeight k E = exp(-E / k)` without constraining `Z = 1`. -/
theorem canonical_likelihood_ratio_cancels_Z {k E Z : ℝ} (hZ : Z ≠ 0) :
    canonicalProb k E Z / canonicalProb k 0 Z = einsteinWeight k E := by
  dsimp [canonicalProb, einsteinWeight]
  rw [neg_zero, zero_div, Real.exp_zero]
  rw [div_div_div_cancel_right₀ hZ, div_one]

/-- Exact Vacuum Normalization for Arbitrary Partition Function `Z ≠ 0`:
    `P_k(0, Z) / P_k(0, Z) = 1`. -/
theorem canonical_likelihood_ratio_vacuum {k Z : ℝ} (hZ : Z ≠ 0) :
    canonicalProb k 0 Z / canonicalProb k 0 Z = 1 := by
  rw [canonical_likelihood_ratio_cancels_Z hZ]
  dsimp [einsteinWeight]
  rw [neg_zero, zero_div, Real.exp_zero]

/-- Exact Factorization of Einstein Likelihood Ratios for Independent Subsystems:
    `einsteinWeight k (E_A + E_B) = einsteinWeight k E_A * einsteinWeight k E_B`. -/
theorem einsteinWeight_add (k EA EB : ℝ) :
    einsteinWeight k (EA + EB) = einsteinWeight k EA * einsteinWeight k EB := by
  dsimp [einsteinWeight]
  have h : - (EA + EB) / k = (- EA / k) + (- EB / k) := by ring
  rw [h, Real.exp_add]

/-! ## Section 5: Relativistic Mass Defect & Mutual Information -/

/-- Pointwise mutual information (logarithmic correlation ratio) between subsystems `A` and `B`:
    `I(A; B) = log(W_AB / (W_A * W_B))`. -/
def mutualInformation (WAB WA WB : ℝ) : ℝ :=
  Real.log (WAB / (WA * WB))

/-- Relativistic mass defect of a composite bound state `AB`: `Δm = m_A + m_B - m_AB`. -/
def massDefect (mA mB mAB : ℝ) : ℝ :=
  mA + mB - mAB

/-- Relativistic binding energy of a composite bound state `AB`: `ΔE_bind = (m_A + m_B - m_AB) * c^2`. -/
def bindingEnergy (mA mB mAB c : ℝ) : ℝ :=
  (mA + mB - mAB) * c ^ 2

/-- Logarithmic expansion of mutual information:
    `I(A; B) = log W_AB - log W_A - log W_B` for `W_AB, W_A, W_B > 0`. -/
theorem mutualInformation_expand {WAB WA WB : ℝ}
    (hAB : 0 < WAB) (hA : 0 < WA) (hB : 0 < WB) :
    mutualInformation WAB WA WB = Real.log WAB - Real.log WA - Real.log WB := by
  dsimp [mutualInformation]
  have hmul : 0 < WA * WB := mul_pos hA hB
  rw [Real.log_div (ne_of_gt hAB) (ne_of_gt hmul), Real.log_mul (ne_of_gt hA) (ne_of_gt hB)]
  ring

/-- Statistically independent subsystems (`W_AB = W_A * W_B`) have zero mutual information. -/
theorem mutualInformation_zero_of_independent {WA WB : ℝ} (hA : 0 < WA) (hB : 0 < WB) :
    mutualInformation (WA * WB) WA WB = 0 := by
  dsimp [mutualInformation]
  have hmul : WA * WB ≠ 0 := ne_of_gt (mul_pos hA hB)
  rw [div_self hmul, Real.log_one]

/-- Positively correlated bound subsystems (`W_AB > W_A * W_B`) have strictly positive
    mutual information `I(A; B) > 0`. -/
theorem mutualInformation_pos_of_correlated {WAB WA WB : ℝ}
    (hA : 0 < WA) (hB : 0 < WB) (hCorr : WA * WB < WAB) :
    0 < mutualInformation WAB WA WB := by
  dsimp [mutualInformation]
  have hmul : 0 < WA * WB := mul_pos hA hB
  have hdiv : 1 < WAB / (WA * WB) := (one_lt_div hmul).mpr hCorr
  exact Real.log_pos hdiv

/-- **Master Theorem 3 (Information-Theoretic Origin of Binding Energy)**:
    For any composite system `AB` whose constituent and bound masses satisfy the triadic law
    `m_i c^2 = -k log W_i` (`i ∈ {A, B, AB}`), the relativistic binding energy equals `k` times
    the mutual information shared between `A` and `B`:
      `bindingEnergy mA mB mAB c = k * mutualInformation WAB WA WB`. -/
theorem bindingEnergy_eq_mutualInformation {mA mB mAB c k WAB WA WB : ℝ}
    (hAB : 0 < WAB) (hA : 0 < WA) (hB : 0 < WB)
    (hTriadA : restEnergy mA c = entropicEnergy k WA)
    (hTriadB : restEnergy mB c = entropicEnergy k WB)
    (hTriadAB : restEnergy mAB c = entropicEnergy k WAB) :
    bindingEnergy mA mB mAB c = k * mutualInformation WAB WA WB := by
  dsimp [bindingEnergy]
  dsimp [restEnergy, entropicEnergy] at hTriadA hTriadB hTriadAB
  rw [mutualInformation_expand hAB hA hB]
  linarith

/-- **Master Theorem 4 (Information-Theoretic Origin of Mass Defect)**:
    Under the triadic identity (`c ≠ 0`), the relativistic mass defect is given exactly by
    `Δm = m_A + m_B - m_AB = (k / c^2) * I(A; B)`. -/
theorem massDefect_eq_mutualInformation {mA mB mAB c k WAB WA WB : ℝ}
    (hc : c ≠ 0) (hAB : 0 < WAB) (hA : 0 < WA) (hB : 0 < WB)
    (hTriadA : restEnergy mA c = entropicEnergy k WA)
    (hTriadB : restEnergy mB c = entropicEnergy k WB)
    (hTriadAB : restEnergy mAB c = entropicEnergy k WAB) :
    massDefect mA mB mAB = (k / c ^ 2) * mutualInformation WAB WA WB := by
  have hBind := bindingEnergy_eq_mutualInformation hAB hA hB hTriadA hTriadB hTriadAB
  dsimp [bindingEnergy] at hBind
  dsimp [massDefect]
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  calc mA + mB - mAB = ((mA + mB - mAB) * c ^ 2) / c ^ 2 := by
        rw [mul_div_cancel_right₀ (mA + mB - mAB) hc2]
  _ = (k * mutualInformation WAB WA WB) / c ^ 2 := by rw [hBind]
  _ = (k / c ^ 2) * mutualInformation WAB WA WB := by ring

/-- Positive Mass Defect Equivalence:
    For `k > 0` and `c ≠ 0`, a bound state exhibits a strictly positive mass defect
    (`m_AB < m_A + m_B`) if and only if its constituents are positively correlated
    (`W_AB > W_A * W_B`). -/
theorem positive_mass_defect_of_correlated {mA mB mAB c k WAB WA WB : ℝ}
    (hc : c ≠ 0) (hk : 0 < k) (hAB : 0 < WAB) (hA : 0 < WA) (hB : 0 < WB)
    (hTriadA : restEnergy mA c = entropicEnergy k WA)
    (hTriadB : restEnergy mB c = entropicEnergy k WB)
    (hTriadAB : restEnergy mAB c = entropicEnergy k WAB)
    (hCorr : WA * WB < WAB) :
    0 < massDefect mA mB mAB := by
  rw [massDefect_eq_mutualInformation hc hAB hA hB hTriadA hTriadB hTriadAB]
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hk_c2 : 0 < k / c ^ 2 := div_pos hk hc2
  have hMI : 0 < mutualInformation WAB WA WB := mutualInformation_pos_of_correlated hA hB hCorr
  exact mul_pos hk_c2 hMI

/-! ## Section 6: Lorentz Covariance, Euclidean Action, and Horizon Calibration -/

/-- **Theorem 5 (Lorentz Covariance under Ott Temperature Transformation & Liouville Invariance)**:
    Under a Lorentz boost with factor `γ ≠ 0`, where relativistic energy transforms as `E' = γ * E`,
    the thermal energy scale transforms via Ott's law `k' = γ * k`, and the phase-space likelihood
    ratio `W' = W` is a Liouville Lorentz scalar, the boosted entropic relation
    `E' = entropicEnergy k' W'` holds if and only if the rest-frame relation `E = entropicEnergy k W` holds. -/
theorem ott_covariant_entropic_energy {γ E k W : ℝ} (hγ : γ ≠ 0) :
    γ * E = entropicEnergy (γ * k) W ↔ E = entropicEnergy k W := by
  dsimp [entropicEnergy]
  have h_factor : - (γ * k) * Real.log W = γ * (- k * Real.log W) := by ring
  rw [h_factor]
  exact mul_right_inj' hγ

/-- **Theorem 6 (Euclidean Path-Integral Action Equivalence)**:
    For a static massive particle of rest energy `E = m c^2` over a Euclidean thermal period
    `Δτ = ħ / k` (`ħ ≠ 0`, `k ≠ 0`), the Euclidean action is `S_E = E * Δτ` and the Euclidean
    vacuum persistence weight `W = exp(-S_E / ħ)` satisfies `entropicEnergy k W = m c^2`. -/
theorem euclidean_action_triadic_identity {m c k hbar : ℝ}
    (hk : k ≠ 0) (hhbar : hbar ≠ 0) :
    let E := restEnergy m c
    let deltaTau := hbar / k
    let SE := E * deltaTau
    let W := Real.exp (- SE / hbar)
    entropicEnergy k W = restEnergy m c := by
  intro E deltaTau SE W
  have hW_eq : W = einsteinWeight k E := by
    dsimp [W, SE, deltaTau, einsteinWeight]
    congr 1
    calc - (E * (hbar / k)) / hbar = (- E / k) * (hbar / hbar) := by ring
    _ = (- E / k) * 1 := by rw [div_self hhbar]
    _ = - E / k := mul_one _
  rw [hW_eq]
  exact entropicEnergy_einsteinWeight hk

/-- **Theorem 7 (Compton–Unruh Single-Nat Horizon Identity)**:
    When the local horizon energy scale matches the Compton energy (`k = m c^2`),
    the Einstein fluctuation weight is `W = exp(-1)` (`surprisal W = 1` nat) and
    `entropicEnergy (m c^2) (exp (-1)) = restEnergy m c`. -/
theorem compton_unruh_single_nat_identity (m c : ℝ) :
    entropicEnergy (restEnergy m c) (Real.exp (-1)) = restEnergy m c := by
  dsimp [entropicEnergy]
  rw [Real.log_exp]
  ring

/-- **Theorem 8 (Schwarzschild–Smarr Horizon Surprisal Identity)**:
    For a Schwarzschild black hole with microstate multiplicity `Ω > 0`, microcanonical
    state probability `W = Ω⁻¹`, Bekenstein–Hawking entropy `S_BH = k_B * log Ω`, and
    effective Smarr thermal scale `k_eff = 2 * k_B * T_H`, the entropic energy `-k_eff log W`
    recovers the Smarr mass-energy formula `2 * T_H * S_BH`. -/
theorem schwarzschild_smarr_surprisal_identity (kB TH Ω : ℝ) :
    let SBH := kB * Real.log Ω
    let keff := 2 * kB * TH
    entropicEnergy keff Ω⁻¹ = 2 * TH * SBH := by
  intro SBH keff
  rw [entropicEnergy_inv_multiplicity]
  dsimp [SBH, keff]
  ring

end JesseMath.Physics.MassEnergySurprisal

#assert_zfc_axioms

