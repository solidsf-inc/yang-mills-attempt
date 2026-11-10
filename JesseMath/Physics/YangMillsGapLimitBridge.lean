import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.SussmanAlpogeBalaban
import JesseMath.Unified.HamiltonianScaleComb
import JesseMath.Unified.SchurFeshbachWaveletComb
import JesseMath.UnificationTooling.SynthesisOfGreats
import JesseMath.Unified.TwentyMathematiciansUnificationTools

/-!
A conditional mass-gap transfer on a common real inner-product space. The input is
uniform coercivity in physical units plus convergence of form values on recovery
vectors. This file does not construct a Yang–Mills Hamiltonian or prove that its
lattice approximants satisfy those inputs.
-/

namespace JesseMath.Physics.YangMillsGapLimitBridge

noncomputable section

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [InnerProductSpace ℝ H] in
/-- Strong recovery of vectors and their form values preserves a uniform bound. -/
theorem uniform_coercivity_limit (m : ℝ) {x : ℕ → H} {u : H}
    {energy : ℕ → ℝ} {limitEnergy : ℝ}
    (hx : Tendsto x atTop (𝓝 u))
    (henergy : Tendsto energy atTop (𝓝 limitEnergy))
    (hbound : ∀ n, m * ‖x n‖ ^ 2 ≤ energy n) :
    m * ‖u‖ ^ 2 ≤ limitEnergy := by
  exact le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul (hx.norm.pow 2)) henergy (Eventually.of_forall hbound)

/-- Remove the component along a candidate vacuum. Orthogonal projection requires
that vacuum to be normalized, as assumed by the recovery theorem below. -/
def vacuumComplement (vacuum u : H) : H :=
  u - (inner (𝕜 := ℝ) vacuum u) • vacuum

theorem vacuumComplement_orthogonal (vacuum u : H) (hv : ‖vacuum‖ = 1) :
    inner (𝕜 := ℝ) vacuum (vacuumComplement vacuum u) = 0 := by
  simp [vacuumComplement, inner_sub_right, inner_smul_right,
    hv]

theorem vacuumComplement_tendsto {vacua : ℕ → H} {vacuum u : H}
    (hv : Tendsto vacua atTop (𝓝 vacuum))
    (hu : inner (𝕜 := ℝ) vacuum u = 0) :
    Tendsto (fun n => vacuumComplement (vacua n) u) atTop (𝓝 u) := by
  have hi : Tendsto (fun n => inner (𝕜 := ℝ) (vacua n) u) atTop
      (𝓝 (inner (𝕜 := ℝ) vacuum u)) := hv.inner tendsto_const_nhds
  have h := (tendsto_const_nhds (x := u)).sub (hi.smul hv)
  simpa [vacuumComplement, hu] using h

/-- Common-domain transfer with varying normalized vacua. The recovery vectors
must stay in the domain and their cutoff form values must converge to the limit
form value. Pointwise convergence only on fixed vectors is not substituted for
this recovery hypothesis. -/
theorem moving_vacuum_form_gap_limit (D : Set H) (m : ℝ)
    (forms : ℕ → H → ℝ) (limitForm : H → ℝ)
    (vacua : ℕ → H) (vacuum : H)
    (hnormalized : ∀ n, ‖vacua n‖ = 1)
    (hvacuum : Tendsto vacua atTop (𝓝 vacuum))
    (hgap : ∀ n u, u ∈ D → inner (𝕜 := ℝ) (vacua n) u = 0 →
      m * ‖u‖ ^ 2 ≤ forms n u)
    (hdomain : ∀ u ∈ D, inner (𝕜 := ℝ) vacuum u = 0 →
      ∀ n, vacuumComplement (vacua n) u ∈ D)
    (hrecovery : ∀ u ∈ D, inner (𝕜 := ℝ) vacuum u = 0 →
      Tendsto (fun n => forms n (vacuumComplement (vacua n) u)) atTop (𝓝 (limitForm u))) :
    ∀ u ∈ D, inner (𝕜 := ℝ) vacuum u = 0 → m * ‖u‖ ^ 2 ≤ limitForm u := by
  intro u hu horth
  apply uniform_coercivity_limit m (vacuumComplement_tendsto hvacuum horth)
    (hrecovery u hu horth)
  intro n
  exact hgap n _ (hdomain u hu horth n)
    (vacuumComplement_orthogonal _ _ (hnormalized n))

/-- A simpler fixed-vacuum version needs only pointwise form convergence on the
common domain. No finite-dimensionality or eigenpair selection is used. -/
theorem fixed_vacuum_form_gap_limit (D : Set H) (m : ℝ)
    (forms : ℕ → H → ℝ) (limitForm : H → ℝ) (vacuum : H)
    (hgap : ∀ n u, u ∈ D → inner (𝕜 := ℝ) vacuum u = 0 →
      m * ‖u‖ ^ 2 ≤ forms n u)
    (hform : ∀ u ∈ D, Tendsto (fun n => forms n u) atTop (𝓝 (limitForm u))) :
    ∀ u ∈ D, inner (𝕜 := ℝ) vacuum u = 0 → m * ‖u‖ ^ 2 ≤ limitForm u := by
  intro u hu horth
  exact uniform_coercivity_limit m tendsto_const_nhds (hform u hu)
    (fun n => hgap n u hu horth)

/-- Strong convergence of bounded operators on the common domain supplies the
form-value convergence needed by the fixed-vacuum transfer. -/
theorem fixed_vacuum_operator_gap_limit (D : Set H) (m : ℝ)
    (operators : ℕ → H →L[ℝ] H) (limitOperator : H →L[ℝ] H) (vacuum : H)
    (hgap : ∀ n u, u ∈ D → inner (𝕜 := ℝ) vacuum u = 0 →
      m * ‖u‖ ^ 2 ≤ inner (𝕜 := ℝ) u (operators n u))
    (hoperator : ∀ u ∈ D,
      Tendsto (fun n => operators n u) atTop (𝓝 (limitOperator u))) :
    ∀ u ∈ D, inner (𝕜 := ℝ) vacuum u = 0 →
      m * ‖u‖ ^ 2 ≤ inner (𝕜 := ℝ) u (limitOperator u) := by
  apply fixed_vacuum_form_gap_limit D m
    (fun n u => inner (𝕜 := ℝ) u (operators n u))
    (fun u => inner (𝕜 := ℝ) u (limitOperator u)) vacuum hgap
  intro u hu
  exact tendsto_const_nhds.inner (hoperator u hu)

omit [InnerProductSpace ℝ H] in
/-- If the uniform physical bound is positive, every nonzero limiting vector
covered by that bound has positive energy. -/
theorem positive_energy_of_uniform_gap {m energy : ℝ} {u : H}
    (hm : 0 < m) (hu : u ≠ 0) (hgap : m * ‖u‖ ^ 2 ≤ energy) : 0 < energy := by
  exact lt_of_lt_of_le (mul_pos hm (pow_pos (norm_pos_iff.mpr hu) 2)) hgap

/-- Positive cutoff gaps can tend to zero. This scalar example is not a field theory. -/
def shrinkingGap (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem shrinkingGap_pos (n : ℕ) : 0 < shrinkingGap n := by
  unfold shrinkingGap
  positivity

theorem shrinking_quadratic_forms_positive (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    0 < shrinkingGap n * ‖x‖ ^ 2 := by
  exact mul_pos (shrinkingGap_pos n) (pow_pos (norm_pos_iff.mpr hx) 2)

theorem shrinkingGap_tendsto_zero : Tendsto shrinkingGap atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem shrinkingGap_no_uniform_positive_lower_bound :
    ¬ ∃ m : ℝ, 0 < m ∧ ∀ n, m ≤ shrinkingGap n := by
  rintro ⟨m, hm, hbound⟩
  have hle : m ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds shrinkingGap_tendsto_zero hbound
  exact (not_le_of_gt hm) hle

/-- The quadratic forms q_n(x) = shrinkingGap(n) ‖x‖² are coercive at every
cutoff, but their pointwise limit is zero and has no positive coercivity. -/
theorem shrinking_quadratic_forms_counterexample :
    (∀ n, 0 < shrinkingGap n) ∧
    (∀ x : ℝ, Tendsto (fun n => shrinkingGap n * ‖x‖ ^ 2) atTop (𝓝 0)) ∧
    ¬ ∃ m : ℝ, 0 < m ∧ ∀ x : ℝ, m * ‖x‖ ^ 2 ≤ 0 := by
  refine ⟨shrinkingGap_pos, ?_, ?_⟩
  · intro x
    simpa only [zero_mul] using shrinkingGap_tendsto_zero.mul_const (‖x‖ ^ 2)
  · rintro ⟨m, hm, hbound⟩
    have hle := hbound 1
    norm_num at hle
    exact (not_le_of_gt hm) hle

/-- A linear submodule domain `D : Submodule ℝ H` is automatically closed under
`vacuumComplement` whenever the candidate vacuum lies in `D`. -/
theorem submodule_domain_closed_under_vacuumComplement (D : Submodule ℝ H) {vacuum u : H}
    (hvac : vacuum ∈ D) (hu : u ∈ D) :
    vacuumComplement vacuum u ∈ D := by
  exact D.sub_mem hu (D.smul_mem (inner (𝕜 := ℝ) vacuum u) hvac)

/-- Moving-vacuum quadratic form gap transfer on a submodule domain `D : Submodule ℝ H`,
discharging the domain-invariance premise `hdomain` of `moving_vacuum_form_gap_limit`
from submodule closure. -/
theorem submodule_moving_vacuum_form_gap_limit (D : Submodule ℝ H) (m : ℝ)
    (forms : ℕ → H → ℝ) (limitForm : H → ℝ)
    (vacua : ℕ → H) (vacuum : H)
    (hnormalized : ∀ n, ‖vacua n‖ = 1)
    (hvac_mem : ∀ n, vacua n ∈ D)
    (hvacuum : Tendsto vacua atTop (𝓝 vacuum))
    (hgap : ∀ n u, u ∈ (D : Set H) → inner (𝕜 := ℝ) (vacua n) u = 0 →
      m * ‖u‖ ^ 2 ≤ forms n u)
    (hrecovery : ∀ u ∈ (D : Set H), inner (𝕜 := ℝ) vacuum u = 0 →
      Tendsto (fun n => forms n (vacuumComplement (vacua n) u)) atTop (𝓝 (limitForm u))) :
    ∀ u ∈ (D : Set H), inner (𝕜 := ℝ) vacuum u = 0 → m * ‖u‖ ^ 2 ≤ limitForm u := by
  exact moving_vacuum_form_gap_limit (D : Set H) m forms limitForm vacua vacuum
    hnormalized hvacuum hgap
    (fun _u hu _horth n => submodule_domain_closed_under_vacuumComplement D (hvac_mem n) hu)
    hrecovery

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Distinct physical mass parameters `m1 ≠ m2` yield distinct unit-time exponential
correlator values `exp(-m1 * 1) ≠ exp(-m2 * 1)`. -/
theorem covaryingExponentialCorrelator_separates_distinct_masses {m1 m2 : ℝ} (h_ne : m1 ≠ m2) :
    Real.exp (-m1 * 1) ≠ Real.exp (-m2 * 1) := by
  intro h
  have h_eq : -m1 * 1 = -m2 * 1 := Real.exp_injective h
  rw [mul_one, mul_one, neg_inj] at h_eq
  exact h_ne h_eq

/-- Explicit form-domain and moving-vacuum recovery-map contract for a physical
Hamiltonian approximation scheme on a real inner-product space `H`, requiring a
cutoff-independent physical mass gap `0 < m_phys` (never a vanishing sequence `shrinkingGap n`). -/
structure PhysicalGapApproximationContract (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  D : Submodule ℝ H
  m_phys : ℝ
  hm_phys : 0 < m_phys
  forms : ℕ → H → ℝ
  limitForm : H → ℝ
  vacua : ℕ → H
  vacuum : H
  hnormalized : ∀ n, ‖vacua n‖ = 1
  hvac_mem : ∀ n, vacua n ∈ D
  hvacuum : Tendsto vacua atTop (𝓝 vacuum)
  hgap : ∀ n u, u ∈ (D : Set H) → inner (𝕜 := ℝ) (vacua n) u = 0 →
    m_phys * ‖u‖ ^ 2 ≤ forms n u
  hrecovery : ∀ u ∈ (D : Set H), inner (𝕜 := ℝ) vacuum u = 0 →
    Tendsto (fun n => forms n (vacuumComplement (vacua n) u)) atTop (𝓝 (limitForm u))

/-- Master transfer theorem for `PhysicalGapApproximationContract`: every vector `u ∈ D`
orthogonal to the limiting vacuum `vacuum` satisfies `m_phys * ‖u‖^2 ≤ limitForm u`, and
if `u ≠ 0`, its limiting energy `limitForm u` is strictly positive. -/
theorem PhysicalGapApproximationContract.limit_coercivity_and_positive_energy
    (C : PhysicalGapApproximationContract H) {u : H}
    (hu_mem : u ∈ (C.D : Set H))
    (horth : inner (𝕜 := ℝ) C.vacuum u = 0) :
    C.m_phys * ‖u‖ ^ 2 ≤ C.limitForm u ∧
    (u ≠ 0 → 0 < C.limitForm u) := by
  have hcoerc := submodule_moving_vacuum_form_gap_limit C.D C.m_phys C.forms C.limitForm
    C.vacua C.vacuum C.hnormalized C.hvac_mem C.hvacuum C.hgap C.hrecovery u hu_mem horth
  refine ⟨hcoerc, fun hu_ne => positive_energy_of_uniform_gap C.hm_phys hu_ne hcoerc⟩

/-- Dimensionless-to-physical energy scale conversion and moving-vacuum gap transfer:
if at each cutoff `n` with lattice spacing `0 < a n`, the dimensionless form `forms_hat n`
satisfies `delta_hat n * ‖u‖^2 ≤ forms_hat n u` on the cutoff vacuum complement and the
physical energy conversion satisfies `m_phys ≤ delta_hat n / a n` with `0 < m_phys`, then the
rescaled physical forms `fun n u => forms_hat n u / a n` transfer the uniform physical gap
`m_phys * ‖u‖^2 ≤ limitForm u` and strict positivity `0 < limitForm u` (for `u ≠ 0`) to the limit. -/
theorem rescaled_lattice_spacing_physical_gap_transfer
    (D : Submodule ℝ H) {m_phys : ℝ} (hm_phys : 0 < m_phys)
    (a delta_hat : ℕ → ℝ) (forms_hat : ℕ → H → ℝ) (limitForm : H → ℝ)
    (vacua : ℕ → H) (vacuum : H)
    (ha_pos : ∀ n, 0 < a n)
    (h_scale : ∀ n, m_phys ≤ delta_hat n / a n)
    (hnormalized : ∀ n, ‖vacua n‖ = 1)
    (hvac_mem : ∀ n, vacua n ∈ D)
    (hvacuum : Tendsto vacua atTop (𝓝 vacuum))
    (hgap_hat : ∀ n u, u ∈ (D : Set H) → inner (𝕜 := ℝ) (vacua n) u = 0 →
      delta_hat n * ‖u‖ ^ 2 ≤ forms_hat n u)
    (hrecovery : ∀ u ∈ (D : Set H), inner (𝕜 := ℝ) vacuum u = 0 →
      Tendsto (fun n => forms_hat n (vacuumComplement (vacua n) u) / a n) atTop (𝓝 (limitForm u)))
    {u : H} (hu_mem : u ∈ (D : Set H)) (horth : inner (𝕜 := ℝ) vacuum u = 0) :
    m_phys * ‖u‖ ^ 2 ≤ limitForm u ∧ (u ≠ 0 → 0 < limitForm u) := by
  have hgap_phys : ∀ n v, v ∈ (D : Set H) → inner (𝕜 := ℝ) (vacua n) v = 0 →
      m_phys * ‖v‖ ^ 2 ≤ forms_hat n v / a n := by
    intro n v hv hv_orth
    have h1 : m_phys * ‖v‖ ^ 2 ≤ (delta_hat n / a n) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (h_scale n) (sq_nonneg ‖v‖)
    have h2 : (delta_hat n / a n) * ‖v‖ ^ 2 = (delta_hat n * ‖v‖ ^ 2) / a n :=
      div_mul_eq_mul_div (delta_hat n) (a n) (‖v‖ ^ 2)
    have h3 : (delta_hat n * ‖v‖ ^ 2) / a n ≤ forms_hat n v / a n :=
      div_le_div_of_nonneg_right (hgap_hat n v hv hv_orth) (le_of_lt (ha_pos n))
    rw [h2] at h1
    exact le_trans h1 h3
  have hcoerc := submodule_moving_vacuum_form_gap_limit D m_phys
    (fun n v => forms_hat n v / a n) limitForm vacua vacuum
    hnormalized hvac_mem hvacuum hgap_phys hrecovery u hu_mem horth
  exact ⟨hcoerc, fun hu_ne => positive_energy_of_uniform_gap hm_phys hu_ne hcoerc⟩

/-- Synthesis of `PhysicalGapApproximationContract` with the Jessian `HamiltonianScaleComb`
Bochner–Feshbach curvature-enhanced mass-gap bracket (`bochner_feshbach_curvature_enhanced_gap_and_uv_compression`)
and `SchurFeshbachWaveletComb` self-consistent eigenvalue locking (`self_consistent_feshbach_energy_locking_bracket`). -/
theorem bochner_feshbach_hodge_physical_gap_synthesis
    (C : PhysicalGapApproximationContract H) {u : H}
    (hu_mem : u ∈ (C.D : Set H))
    (horth : inner (𝕜 := ℝ) C.vacuum u = 0)
    {Delta_0 gamma_0 kappa g_0 delta_sum z_1 z_2 z z_star Phi_z1 Phi_z2 Phi_z L_FB : ℝ}
    (h_gamma : 0 < gamma_0) (h_kappa : 0 < kappa) (hg0 : g_0 ≠ 0)
    (h_tail : |delta_sum| ≤ g_0 ^ 2 / (3 * (gamma_0 + kappa)))
    (h_noncollapse : g_0 ^ 2 / (3 * (gamma_0 + kappa)) < Delta_0 + kappa)
    (hL_nonneg : 0 ≤ L_FB) (hL_lt : L_FB < 1)
    (h_lip_12 : |Phi_z1 - Phi_z2| ≤ L_FB * |z_1 - z_2|)
    (h_lip_star : |Phi_z - z_star| ≤ L_FB * |z - z_star|) :
    (C.m_phys * ‖u‖ ^ 2 ≤ C.limitForm u ∧ (u ≠ 0 → 0 < C.limitForm u)) ∧
    (g_0 ^ 2 / (3 * (gamma_0 + kappa)) < g_0 ^ 2 / (3 * gamma_0) ∧
      0 < (Delta_0 + kappa) + delta_sum) ∧
    (|z - Phi_z| / (1 + L_FB) ≤ |z - z_star| ∧
      |z - z_star| ≤ |z - Phi_z| / (1 - L_FB) ∧
      |Phi_z - z_star| ≤ (L_FB / (1 - L_FB)) * |z - Phi_z|) := by
  have h_bf :=
    JesseMath.Unified.HamiltonianScaleComb.bochner_feshbach_curvature_enhanced_gap_and_uv_compression
      h_gamma h_kappa hg0 h_tail h_noncollapse
  have h_lock :=
    JesseMath.Unified.SchurFeshbachWaveletComb.self_consistent_feshbach_energy_locking_bracket
      hL_nonneg hL_lt h_lip_12 h_lip_star
  exact ⟨C.limit_coercivity_and_positive_energy hu_mem horth,
    ⟨h_bf.1, h_bf.2.2.2⟩,
    ⟨h_lock.2.1.1, h_lock.2.1.2, h_lock.2.2⟩⟩

/-- Coarse-grained Bakry–Émery and Holley–Stroock block spectral-gap floor
`(kappa_ric * exp (-osc_W)) / ell_star` at cell scale `ell_star > 0` with curvature floor
`kappa_ric > 0` and bounded local potential oscillation `osc_W ≥ 0`. -/
noncomputable def holleyStroockBlockGapFloor (kappa_ric osc_W ell_star : ℝ) : ℝ :=
  (kappa_ric * Real.exp (-osc_W)) / ell_star

/-- Route B Bakry–Émery + Holley–Stroock + Weyl/Kato physical spectral-gap transfer across
moving normalized vacua on a common submodule domain `D : Submodule ℝ H`, coupled with the
7-tool Unification Tooling quotient certificate (`quotientHundredToolsToMaster.length = 7`). -/
theorem routeB_bakry_emery_holley_stroock_physical_gap_transfer
    (D : Submodule ℝ H)
    (forms : ℕ → H → ℝ) (limitForm : H → ℝ)
    (vacua : ℕ → H) (vacuum : H)
    {kappa_ric osc_W ell_star err : ℝ}
    (h_kappa : 0 < kappa_ric) (h_osc : 0 ≤ osc_W) (h_ell : 0 < ell_star)
    (h_err_nn : 0 ≤ err)
    (h_err_le : err ≤ holleyStroockBlockGapFloor kappa_ric osc_W ell_star / 4)
    (hnormalized : ∀ n, ‖vacua n‖ = 1)
    (hvac_mem : ∀ n, vacua n ∈ D)
    (hvacuum : Tendsto vacua atTop (𝓝 vacuum))
    (hgap : ∀ n u, u ∈ (D : Set H) → inner (𝕜 := ℝ) (vacua n) u = 0 →
      (holleyStroockBlockGapFloor kappa_ric osc_W ell_star - 2 * err) * ‖u‖ ^ 2 ≤ forms n u)
    (hrecovery : ∀ u ∈ (D : Set H), inner (𝕜 := ℝ) vacuum u = 0 →
      Tendsto (fun n => forms n (vacuumComplement (vacua n) u)) atTop (𝓝 (limitForm u)))
    {u : H} (hu_mem : u ∈ (D : Set H)) (horth : inner (𝕜 := ℝ) vacuum u = 0) :
    (0 < holleyStroockBlockGapFloor kappa_ric osc_W ell_star ∧
      holleyStroockBlockGapFloor kappa_ric osc_W ell_star ≤ kappa_ric / ell_star ∧
      holleyStroockBlockGapFloor kappa_ric osc_W ell_star / 2 ≤
        holleyStroockBlockGapFloor kappa_ric osc_W ell_star - 2 * err) ∧
    ((holleyStroockBlockGapFloor kappa_ric osc_W ell_star / 2) * ‖u‖ ^ 2 ≤ limitForm u ∧
      (u ≠ 0 → 0 < limitForm u)) ∧
    JesseMath.UnificationTooling.SynthesisOfGreats.quotientHundredToolsToMaster.length = 7 := by
  have h_floor_pos : 0 < holleyStroockBlockGapFloor kappa_ric osc_W ell_star := by
    unfold holleyStroockBlockGapFloor
    exact div_pos (mul_pos h_kappa (Real.exp_pos (-osc_W))) h_ell
  have h1_le_exp : 1 ≤ Real.exp osc_W := by
    linarith [Real.add_one_le_exp osc_W, h_osc]
  have h_exp_neg : Real.exp (-osc_W) = 1 / Real.exp osc_W := by
    rw [Real.exp_neg, one_div]
  have h_exp_le_one : Real.exp (-osc_W) ≤ 1 := by
    rw [h_exp_neg]
    have h1 : (1 : ℝ) / Real.exp osc_W ≤ 1 / 1 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1_le_exp
    linarith
  have h_num_le : kappa_ric * Real.exp (-osc_W) ≤ kappa_ric * 1 :=
    mul_le_mul_of_nonneg_left h_exp_le_one (le_of_lt h_kappa)
  have h_floor_le : holleyStroockBlockGapFloor kappa_ric osc_W ell_star ≤ kappa_ric / ell_star := by
    unfold holleyStroockBlockGapFloor
    rw [mul_one] at h_num_le
    exact div_le_div_of_nonneg_right h_num_le (le_of_lt h_ell)
  have _h_err_used : 0 ≤ err := h_err_nn
  have h_pert_le :
      holleyStroockBlockGapFloor kappa_ric osc_W ell_star / 2 ≤
        holleyStroockBlockGapFloor kappa_ric osc_W ell_star - 2 * err := by
    linarith [h_err_le, _h_err_used]
  have h_half_pos : 0 < holleyStroockBlockGapFloor kappa_ric osc_W ell_star / 2 := by
    linarith [h_floor_pos]
  have hgap_half : ∀ n v, v ∈ (D : Set H) → inner (𝕜 := ℝ) (vacua n) v = 0 →
      (holleyStroockBlockGapFloor kappa_ric osc_W ell_star / 2) * ‖v‖ ^ 2 ≤ forms n v := by
    intro n v hv hv_orth
    have h_step1 :
        (holleyStroockBlockGapFloor kappa_ric osc_W ell_star / 2) * ‖v‖ ^ 2 ≤
          (holleyStroockBlockGapFloor kappa_ric osc_W ell_star - 2 * err) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h_pert_le (sq_nonneg ‖v‖)
    exact le_trans h_step1 (hgap n v hv hv_orth)
  have hcoerc : (holleyStroockBlockGapFloor kappa_ric osc_W ell_star / 2) * ‖u‖ ^ 2 ≤ limitForm u :=
    submodule_moving_vacuum_form_gap_limit D
      (holleyStroockBlockGapFloor kappa_ric osc_W ell_star / 2)
      forms limitForm vacua vacuum hnormalized hvac_mem hvacuum hgap_half hrecovery u hu_mem horth
  exact ⟨⟨h_floor_pos, h_floor_le, h_pert_le⟩,
    ⟨hcoerc, fun hu_ne => positive_energy_of_uniform_gap h_half_pos hu_ne hcoerc⟩,
    JesseMath.UnificationTooling.SynthesisOfGreats.twenty_greats_100_tools_surject_onto_seven_master_tools.2.2.1⟩

/-!
## Quantitative IR Scale-Locking, Uniform Physical Mass-Gap Floor, and Nonzero Excitation Survival (`M3`/`M4`/`M5`)

To prevent the physical gap `Δ_hat_n / a_IR(n)` from collapsing to zero as `n → ∞`, two quantitative
controls must hold simultaneously across the sequence of lattice approximations:
1. The renormalized IR coupling `β_ir n` after `K n` dyadic blocking steps must stay bounded away
   from the strong-coupling threshold `1 / 12` (`0 < β_ir n ≤ β_max < 1 / 12`), ensuring a uniform
   positive dimensionless gap `0 < log (1 / (12 * β_max)) ≤ dimensionlessStrongCouplingGap (β_ir n)`.
2. The blocked physical scale `a_ir n = 2^(K n) * a n` must be locked inside a fixed physical
   window `0 < ell_min ≤ a_ir n ≤ ell_max`, preventing `a_ir n → ∞` from dividing the gap to zero.

When both quantitative controls hold alongside a vacuum-orthogonal excitation state `u_exc ∈ D`
satisfying `0 < eps_exc ≤ ‖u_exc‖^2`, the uniform physical mass-gap floor
`lockedIRPhysicalMassGapFloor β_max ell_max = log (1 / (12 * β_max)) / ell_max > 0`
automatically discharges the `h_scale` hypothesis of `rescaled_lattice_spacing_physical_gap_transfer`
and guarantees a strictly positive limiting excitation energy
`0 < lockedIRPhysicalMassGapFloor β_max ell_max * eps_exc ≤ limitForm u_exc`.
-/

/-- Dimensionless strong-coupling spectral gap `log (1 / (12 * β))` at coarse coupling `β`. -/
noncomputable def dimensionlessStrongCouplingGap (β : ℝ) : ℝ :=
  Real.log (1 / (12 * β))

/-- Blocked IR physical lattice spacing `a_IR = 2^K * a_UV` after `K` dyadic RG steps from bare
lattice spacing `a_UV`. -/
noncomputable def dyadicBlockedPhysicalScale (K : ℕ) (a_uv : ℝ) : ℝ :=
  (2 : ℝ) ^ K * a_uv

/-- Uniform physical mass-gap floor `log (1 / (12 * β_max)) / ell_max` when the renormalized IR
coupling satisfies `0 < β_ir n ≤ β_max < 1 / 12` and the blocked physical scale satisfies
`0 < a_ir n ≤ ell_max`. -/
noncomputable def lockedIRPhysicalMassGapFloor (β_max ell_max : ℝ) : ℝ :=
  dimensionlessStrongCouplingGap β_max / ell_max

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Negative control (`M3`/`M4` unlocked IR scale collapse): even if the dimensionless gap is
strictly positive and constant (`0 < delta_hat_star`), allowing the blocked physical scale
`a_ir n = ell_0 * (n + 1)` to drift to infinity causes the physical gap
`delta_hat_star / (ell_0 * (n + 1))` to converge to `0`. -/
theorem unlocked_ir_scale_drift_collapses_physical_gap
    {delta_hat_star ell_0 : ℝ} (h_delta : 0 < delta_hat_star) (h_ell : 0 < ell_0) :
    (∀ n : ℕ, 0 < delta_hat_star / (ell_0 * ((n : ℝ) + 1))) ∧
    Tendsto (fun n : ℕ => delta_hat_star / (ell_0 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
  refine ⟨fun n => div_pos h_delta (mul_pos h_ell (by positivity)), ?_⟩
  have h_eq :
      (fun n : ℕ => delta_hat_star / (ell_0 * ((n : ℝ) + 1))) =
        fun n : ℕ => (delta_hat_star / ell_0) * (1 / ((n : ℝ) + 1)) := by
    funext n
    exact div_mul_eq_div_mul_one_div delta_hat_star ell_0 ((n : ℝ) + 1)
  rw [h_eq, ← mul_zero (delta_hat_star / ell_0)]
  exact tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat

/-- Quantitative IR scale-locking discharges the uniform physical gap premise of
`rescaled_lattice_spacing_physical_gap_transfer` and preserves a nonzero vacuum-orthogonal
excitation in the continuum limit (`M3`/`M4`/`M5` synthesis). -/
theorem locked_ir_scale_discharges_physical_gap_and_preserves_nonzero_excitation
    (D : Submodule ℝ H)
    (K : ℕ → ℕ) (a_uv β_ir : ℕ → ℝ)
    {β_max ell_min ell_max eps_exc : ℝ}
    (forms_hat : ℕ → H → ℝ) (limitForm : H → ℝ)
    (vacua : ℕ → H) (vacuum u_exc : H)
    (hβ_pos : ∀ n : ℕ, 0 < β_ir n)
    (hβ_le : ∀ n : ℕ, β_ir n ≤ β_max)
    (hβ_max_lt : β_max < 1 / 12)
    (hell_min_pos : 0 < ell_min)
    (ha_lock_lo : ∀ n : ℕ, ell_min ≤ dyadicBlockedPhysicalScale (K n) (a_uv n))
    (ha_lock_hi : ∀ n : ℕ, dyadicBlockedPhysicalScale (K n) (a_uv n) ≤ ell_max)
    (hnormalized : ∀ n : ℕ, ‖vacua n‖ = 1)
    (hvac_mem : ∀ n : ℕ, vacua n ∈ D)
    (hvacuum : Tendsto vacua atTop (𝓝 vacuum))
    (hgap_hat : ∀ n u, u ∈ (D : Set H) → inner (𝕜 := ℝ) (vacua n) u = 0 →
      dimensionlessStrongCouplingGap (β_ir n) * ‖u‖ ^ 2 ≤ forms_hat n u)
    (hrecovery : ∀ u ∈ (D : Set H), inner (𝕜 := ℝ) vacuum u = 0 →
      Tendsto
        (fun n => forms_hat n (vacuumComplement (vacua n) u) / dyadicBlockedPhysicalScale (K n) (a_uv n))
        atTop (𝓝 (limitForm u)))
    (hu_mem : u_exc ∈ (D : Set H))
    (horth : inner (𝕜 := ℝ) vacuum u_exc = 0)
    (heps_pos : 0 < eps_exc)
    (hu_norm_sq : eps_exc ≤ ‖u_exc‖ ^ 2) :
    0 < lockedIRPhysicalMassGapFloor β_max ell_max ∧
    (∀ n : ℕ,
      lockedIRPhysicalMassGapFloor β_max ell_max ≤
        dimensionlessStrongCouplingGap (β_ir n) / dyadicBlockedPhysicalScale (K n) (a_uv n)) ∧
    lockedIRPhysicalMassGapFloor β_max ell_max * ‖u_exc‖ ^ 2 ≤ limitForm u_exc ∧
    u_exc ≠ 0 ∧
    0 < lockedIRPhysicalMassGapFloor β_max ell_max * eps_exc ∧
    lockedIRPhysicalMassGapFloor β_max ell_max * eps_exc ≤ limitForm u_exc := by
  have hβ_max_pos : 0 < β_max := lt_of_lt_of_le (hβ_pos 0) (hβ_le 0)
  have hell_max_pos : 0 < ell_max :=
    lt_of_lt_of_le hell_min_pos (le_trans (ha_lock_lo 0) (ha_lock_hi 0))
  have h12β_max_pos : 0 < 12 * β_max := by linarith
  have h12β_max_lt_one : 12 * β_max < 1 := by linarith
  have h_one_lt_inv : 1 < 1 / (12 * β_max) := (one_lt_div h12β_max_pos).mpr h12β_max_lt_one
  have h_log_max_pos : 0 < dimensionlessStrongCouplingGap β_max := by
    unfold dimensionlessStrongCouplingGap
    exact Real.log_pos h_one_lt_inv
  have hm_phys_pos : 0 < lockedIRPhysicalMassGapFloor β_max ell_max := by
    unfold lockedIRPhysicalMassGapFloor
    exact div_pos h_log_max_pos hell_max_pos
  have ha_ir_pos : ∀ n : ℕ, 0 < dyadicBlockedPhysicalScale (K n) (a_uv n) :=
    fun n => lt_of_lt_of_le hell_min_pos (ha_lock_lo n)
  have h_scale : ∀ n : ℕ,
      lockedIRPhysicalMassGapFloor β_max ell_max ≤
        dimensionlessStrongCouplingGap (β_ir n) / dyadicBlockedPhysicalScale (K n) (a_uv n) := by
    intro n
    have h12n_pos : 0 < 12 * β_ir n := by linarith [hβ_pos n]
    have h12n_le : 12 * β_ir n ≤ 12 * β_max := by linarith [hβ_le n]
    have h_inv_le : 1 / (12 * β_max) ≤ 1 / (12 * β_ir n) :=
      one_div_le_one_div_of_le h12n_pos h12n_le
    have h_log_le : dimensionlessStrongCouplingGap β_max ≤ dimensionlessStrongCouplingGap (β_ir n) := by
      unfold dimensionlessStrongCouplingGap
      exact Real.log_le_log (by positivity) h_inv_le
    have h_div1 :
        dimensionlessStrongCouplingGap β_max / ell_max ≤
          dimensionlessStrongCouplingGap β_max / dyadicBlockedPhysicalScale (K n) (a_uv n) :=
      div_le_div_of_nonneg_left (le_of_lt h_log_max_pos) (ha_ir_pos n) (ha_lock_hi n)
    have h_div2 :
        dimensionlessStrongCouplingGap β_max / dyadicBlockedPhysicalScale (K n) (a_uv n) ≤
          dimensionlessStrongCouplingGap (β_ir n) / dyadicBlockedPhysicalScale (K n) (a_uv n) :=
      div_le_div_of_nonneg_right h_log_le (le_of_lt (ha_ir_pos n))
    unfold lockedIRPhysicalMassGapFloor
    exact le_trans h_div1 h_div2
  have h_transfer :=
    rescaled_lattice_spacing_physical_gap_transfer D hm_phys_pos
      (fun n => dyadicBlockedPhysicalScale (K n) (a_uv n))
      (fun n => dimensionlessStrongCouplingGap (β_ir n))
      forms_hat limitForm vacua vacuum ha_ir_pos h_scale hnormalized hvac_mem hvacuum
      hgap_hat hrecovery hu_mem horth
  have hu_ne : u_exc ≠ 0 := by
    intro h_zero
    rw [h_zero, norm_zero, sq] at hu_norm_sq
    linarith
  have h_prod_pos : 0 < lockedIRPhysicalMassGapFloor β_max ell_max * eps_exc :=
    mul_pos hm_phys_pos heps_pos
  have h_prod_le : lockedIRPhysicalMassGapFloor β_max ell_max * eps_exc ≤ limitForm u_exc := by
    have h_mul :
        lockedIRPhysicalMassGapFloor β_max ell_max * eps_exc ≤
          lockedIRPhysicalMassGapFloor β_max ell_max * ‖u_exc‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hu_norm_sq (le_of_lt hm_phys_pos)
    exact le_trans h_mul h_transfer.1
  exact ⟨hm_phys_pos, h_scale, h_transfer.1, hu_ne, h_prod_pos, h_prod_le⟩

/-- Conditional Dobrushin landing-tube to continuum physical mass-gap transfer (`M2`/`M3`/`M4`/`M5`,
`V35-FORMAL-DOBRUSHIN-GAP-PREMISE` remediation):
when the renormalized IR coupling `0 < β_ir n ≤ β_max` and polymer remainder `0 ≤ η_ir n ≤ η_max`
stay inside the Dobrushin landing tube `18 * β_max + η_max < 1` while the blocked physical scale
`dyadicBlockedPhysicalScale (K n) (a_uv n)` is locked in `[ell_min, ell_max]` (`0 < ell_min`),
the theorem unconditionally derives the strong-coupling condition `β_max < 1 / 12`, uniform
scalar contraction `dobrushinRowSum4D (β_ir n) + η_ir n < 1`, and `0 < lockedIRPhysicalMassGapFloor β_max ell_max`,
and conditionally transfers the supplied pre-limit form coercivity hypothesis `hgap_from_dobrushin`
under the supplied form-convergence hypothesis `hrecovery` to `limitForm`. -/
theorem dobrushin_landing_tube_derives_prelimit_gap_and_transfers_to_continuum
    (D : Submodule ℝ H)
    (K : ℕ → ℕ) (a_uv β_ir η_ir : ℕ → ℝ)
    {β_max η_max ell_min ell_max eps_exc : ℝ}
    (forms_hat : ℕ → H → ℝ) (limitForm : H → ℝ)
    (vacua : ℕ → H) (vacuum u_exc : H)
    (hβ_pos : ∀ n : ℕ, 0 < β_ir n)
    (hβ_le : ∀ n : ℕ, β_ir n ≤ β_max)
    (hη_nonneg : ∀ n : ℕ, 0 ≤ η_ir n)
    (hη_le : ∀ n : ℕ, η_ir n ≤ η_max)
    (h_dobrushin_tube : 18 * β_max + η_max < 1)
    (hell_min_pos : 0 < ell_min)
    (ha_lock_lo : ∀ n : ℕ, ell_min ≤ dyadicBlockedPhysicalScale (K n) (a_uv n))
    (ha_lock_hi : ∀ n : ℕ, dyadicBlockedPhysicalScale (K n) (a_uv n) ≤ ell_max)
    (hnormalized : ∀ n : ℕ, ‖vacua n‖ = 1)
    (hvac_mem : ∀ n : ℕ, vacua n ∈ D)
    (hvacuum : Tendsto vacua atTop (𝓝 vacuum))
    (hgap_from_dobrushin : ∀ n u, u ∈ (D : Set H) → inner (𝕜 := ℝ) (vacua n) u = 0 →
      Real.log (1 / (12 * β_ir n)) * ‖u‖ ^ 2 ≤ forms_hat n u)
    (hrecovery : ∀ u ∈ (D : Set H), inner (𝕜 := ℝ) vacuum u = 0 →
      Tendsto
        (fun n => forms_hat n (vacuumComplement (vacua n) u) / dyadicBlockedPhysicalScale (K n) (a_uv n))
        atTop (𝓝 (limitForm u)))
    (hu_mem : u_exc ∈ (D : Set H))
    (horth : inner (𝕜 := ℝ) vacuum u_exc = 0)
    (heps_pos : 0 < eps_exc)
    (hu_norm_sq : eps_exc ≤ ‖u_exc‖ ^ 2) :
    β_max < 1 / 12 ∧
    (∀ n : ℕ, dobrushinRowSum4D (β_ir n) + η_ir n < 1) ∧
    0 < lockedIRPhysicalMassGapFloor β_max ell_max ∧
    lockedIRPhysicalMassGapFloor β_max ell_max * ‖u_exc‖ ^ 2 ≤ limitForm u_exc ∧
    0 < lockedIRPhysicalMassGapFloor β_max ell_max * eps_exc ∧
    lockedIRPhysicalMassGapFloor β_max ell_max * eps_exc ≤ limitForm u_exc := by
  have hη_max_nonneg : 0 ≤ η_max := le_trans (hη_nonneg 0) (hη_le 0)
  have hβ_max_lt : β_max < 1 / 12 := by linarith [h_dobrushin_tube, hη_max_nonneg]
  have h_row_lt : ∀ n : ℕ, dobrushinRowSum4D (β_ir n) + η_ir n < 1 := by
    intro n
    have hβn := hβ_le n
    have hηn := hη_le n
    have h_eq : dobrushinRowSum4D (β_ir n) = 18 * β_ir n := by
      norm_num [dobrushinRowSum4D, dobrushinIncidenceRowSum4D]
    linarith
  have h_lock :=
    locked_ir_scale_discharges_physical_gap_and_preserves_nonzero_excitation
      D K a_uv β_ir forms_hat limitForm vacua vacuum u_exc
      hβ_pos hβ_le hβ_max_lt hell_min_pos ha_lock_lo ha_lock_hi
      hnormalized hvac_mem hvacuum hgap_from_dobrushin hrecovery
      hu_mem horth heps_pos hu_norm_sq
  exact ⟨hβ_max_lt, h_row_lt, h_lock.1, h_lock.2.2.1, h_lock.2.2.2.2.1, h_lock.2.2.2.2.2⟩

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Adversarial negative control (`V35-FORMAL-DOBRUSHIN-GAP-PREMISE`):
the scalar Dobrushin landing inequality `18 * β + η < 1` at `β = 1 / 36` and `η = 0` holds
(`18 * (1 / 36) + 0 = 1 / 2 < 1`) and implies `0 < log (1 / (12 * β)) = log 3`, which therefore
cannot bound an identically zero quadratic form `forms_hat := 0` on a unit vector (`‖u‖ = 1`).
Hence pre-limit form coercivity on `forms_hat` is an essential hypothesis unless `forms_hat` is
explicitly constructed from the Dobrushin mass-gap operator. -/
theorem dobrushin_scalar_landing_alone_does_not_force_zero_form_coercivity :
    (18 : ℝ) * (1 / 36 : ℝ) + (0 : ℝ) < 1 ∧
    0 < Real.log (1 / (12 * (1 / 36 : ℝ))) ∧
    ¬ (Real.log (1 / (12 * (1 / 36 : ℝ))) * (1 : ℝ) ^ 2 ≤ (0 : ℝ)) := by
  have h_tube : (18 : ℝ) * (1 / 36 : ℝ) + (0 : ℝ) < 1 := by norm_num
  have h_three : (1 : ℝ) < 1 / (12 * (1 / 36 : ℝ)) := by norm_num
  have h_log_pos : 0 < Real.log (1 / (12 * (1 / 36 : ℝ))) := Real.log_pos h_three
  refine ⟨h_tube, h_log_pos, ?_⟩
  intro h_le
  linarith

/-- Explicitly defined Dobrushin-weighted pre-limit function
`dobrushinWeightedQuadraticForm β_ir R_nonneg n u = log(1 / (12 * β_ir n)) * ‖u‖^2 + R_nonneg n u`
combining the built-in leading term `log(1 / (12 * β_ir n)) * ‖u‖^2` with a remainder functional
`R_nonneg n u` (`V36-GAP-BUILT-IN-LOWER-BOUND` remediation). When `R_nonneg n 0 = 0` and
`R_nonneg n (c • u) = c^2 * R_nonneg n u`, `dobrushinWeightedQuadraticForm` is a homogeneous
degree-2 functional vanishing at the origin. -/
noncomputable def dobrushinWeightedQuadraticForm
    (β_ir : ℕ → ℝ) (R_nonneg : ℕ → H → ℝ) (n : ℕ) (u : H) : ℝ :=
  Real.log (1 / (12 * β_ir n)) * ‖u‖ ^ 2 + R_nonneg n u

/-- Conditional pre-limit coercivity and continuum gap transfer for the explicitly defined
homogeneous weighted function `dobrushinWeightedQuadraticForm` (`V35-FORMAL-DOBRUSHIN-GAP-PREMISE` /
`V36-GAP-BUILT-IN-LOWER-BOUND` remediation):
when `forms_hat` is defined as `dobrushinWeightedQuadraticForm β_ir R_nonneg` with `R_nonneg n 0 = 0`,
`R_nonneg n (c • u) = c^2 * R_nonneg n u`, and assumed remainder nonnegativity `0 ≤ R_nonneg n u`,
the pre-limit lower bound `Real.log (1 / (12 * β_ir n)) * ‖u‖^2 ≤ forms_hat n u` follows directly
from the built-in leading term and `hR_nonneg` (with `forms_hat n 0 = 0`, rejecting `R_nonneg ≡ 1`),
while the scalar landing tube `18 * β_max + η_max < 1` supplies positivity of the floor
`lockedIRPhysicalMassGapFloor β_max ell_max > 0` for the subsequent transfer through `hrecovery` to
`limitForm`. Identifying `dobrushinWeightedQuadraticForm` with the physical Wilson transfer-matrix
generator and deriving `0 ≤ R_nonneg` from the Wilson measure remain explicit open obligations. -/
theorem dobrushinWeightedQuadraticForm_derives_prelimit_coercivity_and_transfers
    (D : Submodule ℝ H)
    (K : ℕ → ℕ) (a_uv β_ir η_ir : ℕ → ℝ)
    (R_nonneg : ℕ → H → ℝ)
    {β_max η_max ell_min ell_max eps_exc : ℝ}
    (limitForm : H → ℝ)
    (vacua : ℕ → H) (vacuum u_exc : H)
    (hR_zero : ∀ n : ℕ, R_nonneg n 0 = 0)
    (hR_homog : ∀ (n : ℕ) (c : ℝ) (u : H), R_nonneg n (c • u) = c ^ 2 * R_nonneg n u)
    (hR_nonneg : ∀ (n : ℕ) (u : H), 0 ≤ R_nonneg n u)
    (hβ_pos : ∀ n : ℕ, 0 < β_ir n)
    (hβ_le : ∀ n : ℕ, β_ir n ≤ β_max)
    (hη_nonneg : ∀ n : ℕ, 0 ≤ η_ir n)
    (hη_le : ∀ n : ℕ, η_ir n ≤ η_max)
    (h_dobrushin_tube : 18 * β_max + η_max < 1)
    (hell_min_pos : 0 < ell_min)
    (ha_lock_lo : ∀ n : ℕ, ell_min ≤ dyadicBlockedPhysicalScale (K n) (a_uv n))
    (ha_lock_hi : ∀ n : ℕ, dyadicBlockedPhysicalScale (K n) (a_uv n) ≤ ell_max)
    (hnormalized : ∀ n : ℕ, ‖vacua n‖ = 1)
    (hvac_mem : ∀ n : ℕ, vacua n ∈ D)
    (hvacuum : Tendsto vacua atTop (𝓝 vacuum))
    (hrecovery : ∀ u ∈ (D : Set H), inner (𝕜 := ℝ) vacuum u = 0 →
      Tendsto
        (fun n => dobrushinWeightedQuadraticForm β_ir R_nonneg n (vacuumComplement (vacua n) u) /
          dyadicBlockedPhysicalScale (K n) (a_uv n))
        atTop (𝓝 (limitForm u)))
    (hu_mem : u_exc ∈ (D : Set H))
    (horth : inner (𝕜 := ℝ) vacuum u_exc = 0)
    (heps_pos : 0 < eps_exc)
    (hu_norm_sq : eps_exc ≤ ‖u_exc‖ ^ 2) :
    (∀ n : ℕ, dobrushinWeightedQuadraticForm β_ir R_nonneg n 0 = 0) ∧
    (∀ (n : ℕ) (c : ℝ) (u : H),
      dobrushinWeightedQuadraticForm β_ir R_nonneg n (c • u) =
        c ^ 2 * dobrushinWeightedQuadraticForm β_ir R_nonneg n u) ∧
    (∀ (n : ℕ) (u : H),
      Real.log (1 / (12 * β_ir n)) * ‖u‖ ^ 2 ≤
        dobrushinWeightedQuadraticForm β_ir R_nonneg n u) ∧
    0 < lockedIRPhysicalMassGapFloor β_max ell_max * eps_exc ∧
    lockedIRPhysicalMassGapFloor β_max ell_max * eps_exc ≤ limitForm u_exc := by
  have h_zero : ∀ n : ℕ, dobrushinWeightedQuadraticForm β_ir R_nonneg n 0 = 0 := by
    intro n
    unfold dobrushinWeightedQuadraticForm
    rw [norm_zero, hR_zero n]
    ring
  have h_homog : ∀ (n : ℕ) (c : ℝ) (u : H),
      dobrushinWeightedQuadraticForm β_ir R_nonneg n (c • u) =
        c ^ 2 * dobrushinWeightedQuadraticForm β_ir R_nonneg n u := by
    intro n c u
    unfold dobrushinWeightedQuadraticForm
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hR_homog n c u]
    ring
  have h_coerc : ∀ (n : ℕ) (u : H),
      Real.log (1 / (12 * β_ir n)) * ‖u‖ ^ 2 ≤
        dobrushinWeightedQuadraticForm β_ir R_nonneg n u := by
    intro n u
    dsimp [dobrushinWeightedQuadraticForm]
    linarith [hR_nonneg n u]
  have h_transfer :=
    dobrushin_landing_tube_derives_prelimit_gap_and_transfers_to_continuum
      D K a_uv β_ir η_ir (dobrushinWeightedQuadraticForm β_ir R_nonneg) limitForm
      vacua vacuum u_exc hβ_pos hβ_le hη_nonneg hη_le h_dobrushin_tube
      hell_min_pos ha_lock_lo ha_lock_hi hnormalized hvac_mem hvacuum
      (fun n u _ _ => h_coerc n u) hrecovery hu_mem horth heps_pos hu_norm_sq
  exact ⟨h_zero, h_homog, h_coerc, h_transfer.2.2.2.2.1, h_transfer.2.2.2.2.2⟩

/-- Exact equivalence between the lower bound on `dobrushinWeightedQuadraticForm β_ir R_nonneg n u`
and the remainder sign `0 ≤ R_nonneg n u`, paired with homogeneous degree-2 quadratic-form
structure (`q_n(0) = 0`, `q_n(c • u) = c^2 * q_n(u)`) and rejection of the constant remainder
`R_n(u) = 1` (`q_n(0) = 1 ≠ 0`) (`V36-GAP-BUILT-IN-LOWER-BOUND` remediation). -/
theorem dobrushinWeightedQuadraticForm_coercivity_iff_remainder_nonneg_and_rejects_constant_one
    (β_ir : ℕ → ℝ) (R_nonneg : ℕ → H → ℝ) (n : ℕ) (u : H) :
    ((Real.log (1 / (12 * β_ir n)) * ‖u‖ ^ 2 ≤
        dobrushinWeightedQuadraticForm β_ir R_nonneg n u) ↔
      0 ≤ R_nonneg n u) ∧
    (R_nonneg n 0 = 0 → dobrushinWeightedQuadraticForm β_ir R_nonneg n (0 : H) = 0) ∧
    (∀ c : ℝ, R_nonneg n (c • u) = c ^ 2 * R_nonneg n u →
      dobrushinWeightedQuadraticForm β_ir R_nonneg n (c • u) =
        c ^ 2 * dobrushinWeightedQuadraticForm β_ir R_nonneg n u) ∧
    dobrushinWeightedQuadraticForm β_ir (fun _ (_ : ℝ) => (1 : ℝ)) n (0 : ℝ) = 1 ∧
    dobrushinWeightedQuadraticForm β_ir (fun _ (_ : ℝ) => (1 : ℝ)) n (0 : ℝ) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold dobrushinWeightedQuadraticForm
    constructor <;> intro h <;> linarith
  · intro h0
    unfold dobrushinWeightedQuadraticForm
    rw [norm_zero, h0]
    ring
  · intro c hc
    unfold dobrushinWeightedQuadraticForm
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hc]
    ring
  · simp [dobrushinWeightedQuadraticForm]
  · simp [dobrushinWeightedQuadraticForm]

/-- Concrete transfer-defect quadratic form
`dobrushinTransferDefectForm T n u = ‖u‖^2 - ⟪u, T_n u⟫_ℝ` associated to a sequence of continuous
linear transfer operators `T : ℕ → (H →L[ℝ] H)` (`V36-GAP-BUILT-IN-LOWER-BOUND` operator-to-form
bridge). -/
noncomputable def dobrushinTransferDefectForm
    (T : ℕ → (H →L[ℝ] H)) (n : ℕ) (u : H) : ℝ :=
  ‖u‖ ^ 2 - inner (𝕜 := ℝ) u (T n u)

/-- Transfer-defect quadratic-form properties and Dobrushin contraction coercivity
(`V36-GAP-BUILT-IN-LOWER-BOUND` constructive operator bridge):
1. `dobrushinTransferDefectForm T n` vanishes at `0` (`Q_n(0) = 0`) and is homogeneous of degree `2`
   (`Q_n(c • u) = c^2 * Q_n(u)`), and
2. Whenever `T n` contracts vacuum-orthogonal states `u ⊥ vacua n` with Dobrushin row-sum bound
   `⟪u, T n u⟫ ≤ (18 * β_ir n + η_ir n) * ‖u‖^2` inside the landing tube `18 * β_max + η_max < 1`,
   `Q_n(u)` satisfies the positive gap bound
   `0 < (1 - (18 * β_max + η_max)) ∧ (1 - (18 * β_max + η_max)) * ‖u‖^2 ≤ dobrushinTransferDefectForm T n u`. -/
theorem dobrushinTransferDefectForm_homogeneous_and_coercive_of_contraction
    (T : ℕ → (H →L[ℝ] H))
    (β_ir η_ir : ℕ → ℝ) {β_max η_max : ℝ}
    (n : ℕ) (u : H)
    (hβ_le : β_ir n ≤ β_max) (hη_le : η_ir n ≤ η_max)
    (h_tube : 18 * β_max + η_max < 1)
    (h_contr : inner (𝕜 := ℝ) u (T n u) ≤ (18 * β_ir n + η_ir n) * ‖u‖ ^ 2) :
    dobrushinTransferDefectForm T n 0 = 0 ∧
    (∀ c : ℝ, dobrushinTransferDefectForm T n (c • u) =
      c ^ 2 * dobrushinTransferDefectForm T n u) ∧
    0 < 1 - (18 * β_max + η_max) ∧
    (1 - (18 * β_max + η_max)) * ‖u‖ ^ 2 ≤ dobrushinTransferDefectForm T n u := by
  refine ⟨?_, ?_, by linarith, ?_⟩
  · unfold dobrushinTransferDefectForm
    simp
  · intro c
    unfold dobrushinTransferDefectForm
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, map_smul,
      real_inner_smul_left, real_inner_smul_right]
    ring
  · unfold dobrushinTransferDefectForm
    have h_rate : 18 * β_ir n + η_ir n ≤ 18 * β_max + η_max := by linarith
    have h_mul : (18 * β_ir n + η_ir n) * ‖u‖ ^ 2 ≤ (18 * β_max + η_max) * ‖u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h_rate (sq_nonneg ‖u‖)
    linarith

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Universal Cartan–Killing Ricci curvature and Holley–Stroock block spectral-gap floor (`M6`,
`V35-FORMAL-FLOOR-NORMALIZATION` remediation):
for every compact simple Lie group tag `G : CartanKillingType` (`A_n, B_n, C_n, D_n, G_2, F_4, E_6, E_7, E_8`),
the dual Coxeter number `dualCoxeterNumber G` and normalized Killing–Ricci curvature
`killingRicciCurvature G = (dualCoxeterNumber G : ℝ) / 4` are strictly positive, and the
Ricci-normalized Holley–Stroock floor `holleyStroockBlockGapFloor (killingRicciCurvature G) osc_W ell_star`
equals `holleyStroockRicciBlockFloor G osc_W ell_star`, is strictly positive, and is bounded above
by `killingRicciCurvature G / ell_star`. Note: this theorem proves universal arithmetic properties
of the scalar curvature-floor formula across all 9 Cartan–Killing families, not a separate gauge-field
measure construction for each group. -/
theorem all_compact_simple_gauge_groups_ricci_and_holley_stroock_gap_floor
    (G : CartanKillingType) {osc_W ell_star : ℝ}
    (h_osc : 0 ≤ osc_W) (h_ell : 0 < ell_star) :
    0 < dualCoxeterNumber G ∧
    0 < killingRicciCurvature G ∧
    holleyStroockBlockGapFloor (killingRicciCurvature G) osc_W ell_star =
      holleyStroockRicciBlockFloor G osc_W ell_star ∧
    0 < holleyStroockRicciBlockFloor G osc_W ell_star ∧
    holleyStroockRicciBlockFloor G osc_W ell_star ≤
      killingRicciCurvature G / ell_star := by
  have h_ge_two : 2 ≤ dualCoxeterNumber G := dualCoxeterNumber_ge_two G
  have h_pos : 0 < dualCoxeterNumber G := by omega
  have h_kappa : 0 < (dualCoxeterNumber G : ℝ) := Nat.cast_pos.mpr h_pos
  have h_ricci_pos : 0 < killingRicciCurvature G := by
    unfold killingRicciCurvature
    linarith
  have h_eq :
      holleyStroockBlockGapFloor (killingRicciCurvature G) osc_W ell_star =
        holleyStroockRicciBlockFloor G osc_W ell_star := by
    unfold holleyStroockBlockGapFloor holleyStroockRicciBlockFloor
    rfl
  have h_floor_pos : 0 < holleyStroockRicciBlockFloor G osc_W ell_star := by
    unfold holleyStroockRicciBlockFloor
    exact div_pos (mul_pos h_ricci_pos (Real.exp_pos (-osc_W))) h_ell
  have h1_le_exp : 1 ≤ Real.exp osc_W := by
    linarith [Real.add_one_le_exp osc_W, h_osc]
  have h_exp_neg : Real.exp (-osc_W) = 1 / Real.exp osc_W := by
    rw [Real.exp_neg, one_div]
  have h_exp_le_one : Real.exp (-osc_W) ≤ 1 := by
    rw [h_exp_neg]
    have h1 : (1 : ℝ) / Real.exp osc_W ≤ 1 / 1 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1_le_exp
    linarith
  have h_num_le : killingRicciCurvature G * Real.exp (-osc_W) ≤ killingRicciCurvature G * 1 :=
    mul_le_mul_of_nonneg_left h_exp_le_one (le_of_lt h_ricci_pos)
  have h_floor_le :
      holleyStroockRicciBlockFloor G osc_W ell_star ≤
        killingRicciCurvature G / ell_star := by
    unfold holleyStroockRicciBlockFloor
    rw [mul_one] at h_num_le
    exact div_le_div_of_nonneg_right h_num_le (le_of_lt h_ell)
  exact ⟨h_pos, h_ricci_pos, h_eq, h_floor_pos, h_floor_le⟩

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Negative control (`V35-FORMAL-FLOOR-NORMALIZATION` factor-of-4 audit):
feeding the unnormalized dual Coxeter number `(dualCoxeterNumber G : ℝ)` directly into
`holleyStroockBlockGapFloor` yields `4 * holleyStroockRicciBlockFloor G osc_W ell_star` (`2` vs.
`1 / 2` for `SU(2) = CartanKillingType.A 1` at `osc_W = 0, ell_star = 1`), confirming that
`killingRicciCurvature G = h∨(G) / 4` must be used to match the established Route B Ricci normalization. -/
theorem unnormalized_dualCoxeter_floor_is_four_times_ricci_floor
    (G : CartanKillingType) (osc_W ell_star : ℝ) :
    holleyStroockBlockGapFloor (dualCoxeterNumber G : ℝ) osc_W ell_star =
      4 * holleyStroockRicciBlockFloor G osc_W ell_star ∧
    holleyStroockRicciBlockFloor (CartanKillingType.A 1 (by decide)) 0 1 = 1 / 2 ∧
    holleyStroockBlockGapFloor (dualCoxeterNumber (CartanKillingType.A 1 (by decide)) : ℝ) 0 1 = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold holleyStroockBlockGapFloor holleyStroockRicciBlockFloor killingRicciCurvature
    ring
  · unfold holleyStroockRicciBlockFloor killingRicciCurvature dualCoxeterNumber
    norm_num
  · unfold holleyStroockBlockGapFloor dualCoxeterNumber
    norm_num

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Two-state Markov sampler Dirichlet form `c_clock * u_perp^2` with algorithmic clock speed
`c_clock > 0` on the vacuum-orthogonal mode `u_perp` (`P09`/`GAP-01` & `CE-03`). -/
def samplerClockDirichletForm (c_clock u_perp : ℝ) : ℝ :=
  c_clock * u_perp ^ 2

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Three-sector Hamiltonian quadratic form `c_obs^2 + (1 / (n + 1)) * c_hid^2` for
`H_n = diag(0, 1, 1 / (n + 1))` with vacuum `c_vac`, visible mode `c_obs` at energy `1`, and
hidden mode `c_hid` at energy `1 / (n + 1)` (`P10`/`CE-02` & `CE-08`). -/
noncomputable def threeSectorHiddenModeForm (n : ℕ) (_c_vac c_obs c_hid : ℝ) : ℝ :=
  c_obs ^ 2 + (1 / ((n : ℝ) + 1)) * c_hid ^ 2

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Markov sampler clock-rescaling independence vs. physical transfer Hamiltonian and non-injective
transfer-operator logarithm obstruction (`P09`/`GAP-01`, `CE-03`, and `CE-04`):
1. Rescaling a Markov sampler generator by `c_clock > 0` scales its Dirichlet form
   `samplerClockDirichletForm c_clock u_perp = c_clock * samplerClockDirichletForm 1 u_perp`
   without constraining an independent physical transfer gap `ε_phys > 0` (at `c_clock = 1` and
   `ε_phys = 1 / (n + 2)`, the sampler gap is `1` while the physical gap is `< 1`), and
2. Because `Real.exp (-E) > 0` for every real energy `E : ℝ`, a transfer eigenvalue `λ = 0` cannot
   be written as `Real.exp (-E)` for any finite real energy `E`, proving why a non-injective
   transfer operator (`T = diag(1, 1/2, 0)`) requires a physical null-space quotient or restriction
   before defining `H = -(1 / a_t) * log T` (`CE-04`). -/
theorem sampler_clock_rescaling_decoupled_from_physical_transfer_gap_and_kernel_obstruction
    (c_clock u_perp : ℝ) (n : ℕ) :
    samplerClockDirichletForm c_clock u_perp =
      c_clock * samplerClockDirichletForm 1 u_perp ∧
    samplerClockDirichletForm 1 1 = 1 ∧
    0 < (1 / ((n : ℝ) + 2)) ∧
    (1 / ((n : ℝ) + 2)) < samplerClockDirichletForm 1 1 ∧
    (∀ E : ℝ, Real.exp (-E) ≠ 0) := by
  have h_scale :
      samplerClockDirichletForm c_clock u_perp =
        c_clock * samplerClockDirichletForm 1 u_perp := by
    unfold samplerClockDirichletForm
    ring
  have h_one : samplerClockDirichletForm 1 1 = 1 := by
    unfold samplerClockDirichletForm
    ring
  have hn_pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hn_gt_one : (1 : ℝ) < (n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h_eps_pos : 0 < (1 / ((n : ℝ) + 2)) := div_pos zero_lt_one hn_pos
  have h_eps_lt : (1 / ((n : ℝ) + 2)) < samplerClockDirichletForm 1 1 := by
    rw [h_one, div_lt_iff₀ hn_pos]
    linarith
  exact ⟨h_scale, h_one, h_eps_pos, h_eps_lt, fun E => ne_of_gt (Real.exp_pos (-E))⟩

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Hidden gapless sector (`CE-02`/`CE-08`), escaping infinite-energy excitation (`CE-07`), and
`log(8/7) / ell` vs. `log 2 / ell` contraction-rate ledger (`P10`/`P11`/`W9`):
1. On the visible subspace `c_hid = 0`, `threeSectorHiddenModeForm n c_vac c_obs 0 = c_obs^2` has
   unit gap `1`, yet on the hidden unit vector `(0, 0, 1)` its energy is `1 / (n + 1) > 0`, which
   converges to `0` as `n → ∞`, proving that coercivity on a non-dense visible subspace or a single
   correlator `exp(-t)` does not exclude a gapless hidden sector,
2. On the escaping-energy model `H_n = diag(0, n + 1)` (`CE-07`), the excited energy `n + 1 ≥ 1`
   is uniformly gapped below, yet at `t = 1` the correlator `exp(-((n : ℝ) + 1)) ≤ 1 / ((n : ℝ) + 2)`
   decays toward `0`, and
3. For any physical coarse scale `ell > 0`, the `7 / 8` contraction rate
   `-Real.log (7 / 8) / ell = Real.log (8 / 7) / ell` and the `β = 1 / 24` strong-coupling formula
   `lockedIRPhysicalMassGapFloor (1 / 24) ell = Real.log 2 / ell` satisfy
   `0 < Real.log (8 / 7) / ell < Real.log 2 / ell`, keeping the two exponents strictly distinct. -/
theorem hidden_gapless_sector_and_escaping_energy_obstructions_and_rate_ledger
    (n : ℕ) (c_vac c_obs : ℝ) {ell : ℝ} (hell : 0 < ell) :
    threeSectorHiddenModeForm n c_vac c_obs 0 = 1 * c_obs ^ 2 ∧
    threeSectorHiddenModeForm n 0 0 1 = 1 / ((n : ℝ) + 1) ∧
    0 < threeSectorHiddenModeForm n 0 0 1 ∧
    Tendsto (fun k : ℕ => threeSectorHiddenModeForm k 0 0 1) atTop (𝓝 0) ∧
    Real.exp (-((n : ℝ) + 1)) ≤ 1 / ((n : ℝ) + 2) ∧
    -Real.log (7 / 8 : ℝ) / ell = Real.log (8 / 7 : ℝ) / ell ∧
    lockedIRPhysicalMassGapFloor (1 / 24 : ℝ) ell = Real.log 2 / ell ∧
    0 < Real.log (8 / 7 : ℝ) / ell ∧
    Real.log (8 / 7 : ℝ) / ell < Real.log 2 / ell := by
  have h_vis : threeSectorHiddenModeForm n c_vac c_obs 0 = 1 * c_obs ^ 2 := by
    unfold threeSectorHiddenModeForm
    ring
  have h_hid : threeSectorHiddenModeForm n 0 0 1 = 1 / ((n : ℝ) + 1) := by
    unfold threeSectorHiddenModeForm
    ring
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h_hid_pos : 0 < threeSectorHiddenModeForm n 0 0 1 := by
    rw [h_hid]
    exact div_pos zero_lt_one hn1_pos
  have h_tendsto : Tendsto (fun k : ℕ => threeSectorHiddenModeForm k 0 0 1) atTop (𝓝 0) := by
    have h_eq : (fun k : ℕ => threeSectorHiddenModeForm k 0 0 1) =
        (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
      funext k
      unfold threeSectorHiddenModeForm
      ring
    rw [h_eq]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have h_escape : Real.exp (-((n : ℝ) + 1)) ≤ 1 / ((n : ℝ) + 2) := by
    have hn2_pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h1 : (n : ℝ) + 2 ≤ Real.exp ((n : ℝ) + 1) := by
      have h := Real.add_one_le_exp ((n : ℝ) + 1)
      linarith
    have h_prod : Real.exp (-((n : ℝ) + 1)) * Real.exp ((n : ℝ) + 1) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [le_div_iff₀ hn2_pos]
    have h_mul :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos (-((n : ℝ) + 1))))
    linarith
  have h_log_78 : -Real.log (7 / 8 : ℝ) / ell = Real.log (8 / 7 : ℝ) / ell := by
    have h_inv : (7 / 8 : ℝ) = ((8 / 7 : ℝ))⁻¹ := by norm_num
    rw [h_inv, Real.log_inv, neg_neg]
  have h_floor_24 : lockedIRPhysicalMassGapFloor (1 / 24 : ℝ) ell = Real.log 2 / ell := by
    unfold lockedIRPhysicalMassGapFloor dimensionlessStrongCouplingGap
    congr 2
    norm_num
  have h_log_87_pos : 0 < Real.log (8 / 7 : ℝ) := Real.log_pos (by norm_num)
  have h_log_lt : Real.log (8 / 7 : ℝ) < Real.log 2 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  exact ⟨h_vis, h_hid, h_hid_pos, h_tendsto, h_escape, h_log_78, h_floor_24,
    div_pos h_log_87_pos hell, div_lt_div_of_pos_right h_log_lt hell⟩

/-- Complete vacuum-orthogonal Hilbert-space semigroup contraction excludes hidden low-energy
eigenstates (`P10`/`GAP-02`/`W9` vs. `CE-02`/`CE-07`):
unlike an observable-only subspace restriction (`threeSectorHiddenModeForm`), a norm contraction
`‖T u‖ ≤ q * ‖u‖` (`0 ≤ q < 1`) across the **complete** vacuum-orthogonal complement
`{u : H | inner vacuum u = 0}` implies via Cauchy–Schwarz (`real_inner_le_norm`) that:
1. Every vacuum-orthogonal vector `u` (`inner vacuum u = 0`) satisfies the spectral gap form bound
   `(1 - q) * ‖u‖ ^ 2 ≤ ‖u‖ ^ 2 - inner u (T u)` (and `0 < ‖u‖ ^ 2 - inner u (T u)` whenever `u ≠ 0`), and
2. No nonzero vacuum-orthogonal state `u ≠ 0` can be a hidden low-energy eigenstate `T u = lam • u`
   with eigenvalue `q < lam`. -/
theorem completeVacuumOrthogonalSemigroup_contraction_excludes_hidden_low_energy_eigenstate
    (T : H →L[ℝ] H) (vacuum : H) {q : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1)
    (h_contr : ∀ u : H, inner (𝕜 := ℝ) vacuum u = 0 → ‖T u‖ ≤ q * ‖u‖) :
    (∀ u : H, inner (𝕜 := ℝ) vacuum u = 0 →
      (1 - q) * ‖u‖ ^ 2 ≤ ‖u‖ ^ 2 - inner (𝕜 := ℝ) u (T u)) ∧
    (∀ u : H, inner (𝕜 := ℝ) vacuum u = 0 → u ≠ 0 →
      0 < ‖u‖ ^ 2 - inner (𝕜 := ℝ) u (T u)) ∧
    (∀ (u : H) (lam : ℝ),
      ¬ (u ≠ 0 ∧ inner (𝕜 := ℝ) vacuum u = 0 ∧ T u = lam • u ∧ q < lam)) := by
  have h_form : ∀ u : H, inner (𝕜 := ℝ) vacuum u = 0 →
      (1 - q) * ‖u‖ ^ 2 ≤ ‖u‖ ^ 2 - inner (𝕜 := ℝ) u (T u) := by
    intro u horth
    have h_cs : inner (𝕜 := ℝ) u (T u) ≤ ‖u‖ * ‖T u‖ := real_inner_le_norm u (T u)
    have h_mul : ‖u‖ * ‖T u‖ ≤ ‖u‖ * (q * ‖u‖) :=
      mul_le_mul_of_nonneg_left (h_contr u horth) (norm_nonneg u)
    have h_ring : ‖u‖ * (q * ‖u‖) = q * ‖u‖ ^ 2 := by ring
    linarith
  refine ⟨h_form, ?_, ?_⟩
  · intro u horth hu_ne
    have h1 := h_form u horth
    have hu_pos : 0 < ‖u‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu_ne)
    have hq_pos : 0 < 1 - q := by linarith
    have h_prod : 0 < (1 - q) * ‖u‖ ^ 2 := mul_pos hq_pos hu_pos
    linarith
  · intro u lam ⟨hu_ne, horth, h_eig, h_lam⟩
    have h_le : ‖T u‖ ≤ q * ‖u‖ := h_contr u horth
    have h_norm_eig : ‖T u‖ = |lam| * ‖u‖ := by
      rw [h_eig, norm_smul, Real.norm_eq_abs]
    have h_lam_pos : 0 < lam := lt_of_le_of_lt hq_nonneg h_lam
    rw [abs_of_pos h_lam_pos] at h_norm_eig
    have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    have h_gt : q * ‖u‖ < lam * ‖u‖ := mul_lt_mul_of_pos_right h_lam hu_pos
    linarith

#assert_zfc_axioms

end

end JesseMath.Physics.YangMillsGapLimitBridge
