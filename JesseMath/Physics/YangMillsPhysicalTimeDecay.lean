import JesseMath.Physics.YangMillsPhysicalGap
import JesseMath.Physics.YangMillsGapLimitBridge
import JesseMath.Linter.AxiomAudit

/-!
# Physical-time decay of temporal lattice transfer operators

A lattice transfer operator `T` advances Euclidean time by one temporal spacing `a`. A
contraction `‖T u‖ ≤ ρ ‖u‖` on the vacuum complement is a dimensionless statement about one
step. This module defines the physical-time evolution `t ↦ T ^ ⌊t / a⌋₊`, the dimensionless
rate `latticeRate ρ = -log ρ`, and the physical rate `physicalRate a m = m / a`, and proves:

1. On the time lattice `t ∈ a ℕ`, a per-step factor `ρ` gives exactly the decay
   `exp (-(latticeRate ρ / a) * t)`; the rate is sharp on an eigenvector, and between lattice
   times the bound holds with the prefactor `exp (m a)`.
2. The uniformity requirement along a cutoff path `a_n → 0` is the explicit predicate
   `UniformPhysicalRateFloor` (one `m0 > 0` chosen before the cutoff index). It is equivalent to
   `ρ_n ≤ exp (-m0 a_n)`, it yields decay uniform in the cutoff, and together with strong
   convergence of the lattice evolutions on a dense core it yields the real-time decay of the
   limit (prefactor `1`) and, given the generator derivative, the generator coercivity of
   `YangMillsPhysicalGap`.
3. A fixed dimensionless constant (for example `log (8 / 7) = latticeRate (7 / 8)`) has no
   physical scale of its own: its physical rate realizes every positive value, diverges when the
   step length tends to zero and collapses when the step length diverges. A fixed per-step factor
   along `a_n → 0` forces the strong limit of the lattice evolutions (on a dense core, with
   convergent vacua) to be the vacuum projection at every positive time, hence a theory with no
   excitations if the limit is strongly continuous at `0`.
4. For the repository's existing bounds: the strong-coupling formula is eventually `≤ 0` on a
   weak-coupling path `β_n → ∞` and diverges at fixed coupling as `a_n → 0`; the Dobrushin row sum
   reaches `1` on a weak-coupling path; the anisotropic Doeblin factor has physical rate tending
   to `0` along every temporal cutoff path; the finite-volume Doeblin factor has lattice rate
   tending to `0` in infinite volume or at weak coupling; the prescribed
   `wilsonMeasureTimeCorrelator` tends to `0` at every positive time at fixed coupling and stops
   decaying on a weak-coupling path; the fields of `LatticeApproximantSequence` do not contain
   the floor. A blocked constant such as `7 / 8` gives the floor
   `log (8 / 7) / ℓmax` only if it bounds the fine evolution over the blocked time `ℓ_n ≤ ℓmax` on
   the whole fine vacuum complement (root extraction for a Hermitian transfer operator).

Scope. Nothing here constructs the Osterwalder–Schrader transfer operator of the `SU(2)` Wilson
measure, its Hilbert space, a common space for different cutoffs, or a continuum limit. Those are
named inputs (`LatticeTransferStep`, `PhysicalTimeDecayObligations`). The positive model at the
end shows only that the obligations are consistent; it is not Yang–Mills.
-/

noncomputable section

namespace JesseMath.Physics.YangMillsPhysicalTimeDecay

open Filter
open scoped Topology InnerProductSpace
open JesseMath.Physics.YangMillsPhysicalGap

/-! ## 1. Dimensionless and physical rates -/

/-- Dimensionless decay rate per temporal lattice step of a per-step contraction factor `ρ` on the
vacuum complement: `m_latt = -log ρ`. A pure number with no length scale. -/
def latticeRate (ρ : ℝ) : ℝ := -Real.log ρ

/-- Physical decay rate at temporal spacing `a`: `m_phys(a) = m_latt / a`. When `a` is a length
this is an inverse length, i.e. a mass in natural units. -/
def physicalRate (a mLatt : ℝ) : ℝ := mLatt / a

theorem latticeRate_pos {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) : 0 < latticeRate ρ := by
  have h := Real.log_neg h0 h1
  unfold latticeRate
  linarith

theorem latticeRate_nonneg {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) : 0 ≤ latticeRate ρ := by
  have h := Real.log_nonpos h0.le h1
  unfold latticeRate
  linarith

theorem exp_neg_latticeRate {ρ : ℝ} (h0 : 0 < ρ) : Real.exp (-latticeRate ρ) = ρ := by
  rw [latticeRate, neg_neg, Real.exp_log h0]

/-- `ρ ^ n = exp (-m_phys(a) * (n a))`: the `n`-th power of the per-step factor is the decay
factor at physical time `t = n a`. -/
theorem stepFactor_pow_eq_exp_physicalTime {a ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (n : ℕ) :
    ρ ^ n = Real.exp (-physicalRate a (latticeRate ρ) * ((n : ℝ) * a)) := by
  have h : -physicalRate a (latticeRate ρ) * ((n : ℝ) * a) = (n : ℝ) * Real.log ρ := by
    unfold physicalRate latticeRate
    field_simp
  rw [h, Real.exp_nat_mul, Real.exp_log hρ]

/-- A physical floor `m` is the same as the per-step bound `ρ ≤ exp (-(m a))`. -/
theorem le_physicalRate_iff_stepFactor_le {a ρ m : ℝ} (ha : 0 < a) (hρ : 0 < ρ) :
    m ≤ physicalRate a (latticeRate ρ) ↔ ρ ≤ Real.exp (-(m * a)) := by
  unfold physicalRate latticeRate
  rw [le_div_iff₀ ha, ← Real.log_le_iff_le_exp hρ]
  constructor <;> intro h <;> linarith

/-- A physical ceiling `M` is the same as the per-step bound `exp (-(M a)) ≤ ρ`. -/
theorem physicalRate_le_iff_le_stepFactor {a ρ M : ℝ} (ha : 0 < a) (hρ : 0 < ρ) :
    physicalRate a (latticeRate ρ) ≤ M ↔ Real.exp (-(M * a)) ≤ ρ := by
  unfold physicalRate latticeRate
  rw [div_le_iff₀ ha, ← Real.le_log_iff_exp_le hρ]
  constructor <;> intro h <;> linarith

/-! ## 2. The time lattice and the physical-time evolution of one regularization -/

/-- Physical times reachable on a temporal lattice of spacing `a`: `t = n a`, `n : ℕ`. -/
def timeLattice (a : ℝ) : Set ℝ := Set.range fun n : ℕ => (n : ℝ) * a

/-- Whole lattice steps elapsed by physical time `t`: `⌊t / a⌋₊`. -/
def elapsedSteps (a t : ℝ) : ℕ := ⌊t / a⌋₊

theorem elapsedSteps_lattice {a : ℝ} (ha : 0 < a) (n : ℕ) :
    elapsedSteps a ((n : ℝ) * a) = n := by
  unfold elapsedSteps
  rw [mul_div_cancel_right₀ _ ha.ne', Nat.floor_natCast]

theorem elapsedSteps_mul_le {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    (elapsedSteps a t : ℝ) * a ≤ t := by
  have h := Nat.floor_le (div_nonneg ht ha.le)
  unfold elapsedSteps
  calc (⌊t / a⌋₊ : ℝ) * a ≤ (t / a) * a := mul_le_mul_of_nonneg_right h ha.le
    _ = t := div_mul_cancel₀ t ha.ne'

theorem sub_lt_elapsedSteps_mul {a t : ℝ} (ha : 0 < a) :
    t - a < (elapsedSteps a t : ℝ) * a := by
  have h := Nat.lt_floor_add_one (t / a)
  unfold elapsedSteps
  have h2 : t / a * a < ((⌊t / a⌋₊ : ℝ) + 1) * a := mul_lt_mul_of_pos_right h ha
  rw [div_mul_cancel₀ t ha.ne'] at h2
  linarith

theorem timeLattice_nonneg {a t : ℝ} (ha : 0 < a) (ht : t ∈ timeLattice a) : 0 ≤ t := by
  obtain ⟨n, rfl⟩ := ht
  exact mul_nonneg (Nat.cast_nonneg n) ha.le

/-- One temporal lattice regularization. All fields are inputs: the repository constructs the
Osterwalder–Schrader transfer operator only after passing to a Wilson-loop limit law
(`YangMillsReconstructedGeneratorGap.wilsonLimitTransfer`). It does not supply a finite-cutoff
operator here, so `transfer`, `vacuum`, normalization and Hermitian symmetry remain hypotheses
about the supplied lattice operator. -/
structure LatticeTransferStep (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- Temporal lattice spacing: physical time advanced by one application of `transfer`. -/
  spacing : ℝ
  spacing_pos : 0 < spacing
  /-- Bounded one-step transfer operator. -/
  transfer : H →L[ℂ] H
  /-- Normalized vacuum vector. -/
  vacuum : H
  vacuum_norm : ‖vacuum‖ = 1
  /-- The transfer operator fixes the vacuum (normalization by the top eigenvalue). -/
  transfer_vacuum : transfer vacuum = vacuum
  /-- Hermitian symmetry of the transfer operator. -/
  transfer_symmetric : ∀ u v : H, ⟪transfer u, v⟫_ℂ = ⟪u, transfer v⟫_ℂ

namespace LatticeTransferStep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : LatticeTransferStep H)

/-- Physical-time evolution `T ^ ⌊t / a⌋₊`. On the time lattice `t = n a` it is exactly `T ^ n`;
between lattice times it keeps the last lattice value. -/
def evolution (t : ℝ) : H →L[ℂ] H := S.transfer ^ elapsedSteps S.spacing t

/-- Contraction of one transfer step on the vacuum complement with factor `ρ`. -/
def StepContraction (ρ : ℝ) : Prop :=
  ∀ u : H, ⟪S.vacuum, u⟫_ℂ = 0 → ‖S.transfer u‖ ≤ ρ * ‖u‖

theorem evolution_lattice (n : ℕ) : S.evolution ((n : ℝ) * S.spacing) = S.transfer ^ n := by
  unfold evolution
  rw [elapsedSteps_lattice S.spacing_pos]

theorem evolution_zero : S.evolution 0 = 1 := by
  simpa using S.evolution_lattice 0

theorem transfer_inner_vacuum (u : H) : ⟪S.vacuum, S.transfer u⟫_ℂ = ⟪S.vacuum, u⟫_ℂ := by
  rw [← S.transfer_symmetric, S.transfer_vacuum]

theorem pow_vacuum (n : ℕ) : (S.transfer ^ n) S.vacuum = S.vacuum := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, S.transfer_vacuum]

theorem evolution_vacuum (t : ℝ) : S.evolution t S.vacuum = S.vacuum := S.pow_vacuum _

theorem pow_inner_vacuum (n : ℕ) (u : H) :
    ⟪S.vacuum, (S.transfer ^ n) u⟫_ℂ = ⟪S.vacuum, u⟫_ℂ := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_apply_eq_comp, S.transfer_inner_vacuum, ih]

/-- Iterating the one-step contraction on the invariant vacuum complement. -/
theorem pow_contraction {ρ : ℝ} (hρ : 0 ≤ ρ) (h : S.StepContraction ρ) (n : ℕ) (u : H)
    (hu : ⟪S.vacuum, u⟫_ℂ = 0) : ‖(S.transfer ^ n) u‖ ≤ ρ ^ n * ‖u‖ := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp]
    have horth : ⟪S.vacuum, (S.transfer ^ k) u⟫_ℂ = 0 := by rw [S.pow_inner_vacuum]; exact hu
    calc ‖S.transfer ((S.transfer ^ k) u)‖ ≤ ρ * ‖(S.transfer ^ k) u‖ := h _ horth
      _ ≤ ρ * (ρ ^ k * ‖u‖) := mul_le_mul_of_nonneg_left ih hρ
      _ = ρ ^ (k + 1) * ‖u‖ := by ring

/-- **Per-step contraction to physical-time decay on the time lattice.**
Quantifier order: the regularization `S` (hence the spacing `a`) and the factor `ρ` are fixed
first; then for every lattice time `t ∈ a ℕ` and every vacuum-orthogonal `u`,
`‖T(t) u‖ ≤ exp (-(latticeRate ρ / a) * t) ‖u‖`. The rate depends on `a`. -/
theorem evolution_decay_on_timeLattice {ρ : ℝ} (hρ : 0 < ρ) (h : S.StepContraction ρ) :
    ∀ t ∈ timeLattice S.spacing, ∀ u : H, ⟪S.vacuum, u⟫_ℂ = 0 →
      ‖S.evolution t u‖ ≤ Real.exp (-physicalRate S.spacing (latticeRate ρ) * t) * ‖u‖ := by
  rintro t ⟨n, rfl⟩ u hu
  rw [S.evolution_lattice n, ← stepFactor_pow_eq_exp_physicalTime S.spacing_pos hρ n]
  exact S.pow_contraction hρ.le h n u hu

/-- Whole-space form: the evolution converges to the vacuum part at the physical rate,
controlling every vector, with no restriction to an observed sector. -/
theorem evolution_excitedPart_decay_on_timeLattice {ρ : ℝ} (hρ : 0 < ρ)
    (h : S.StepContraction ρ) :
    ∀ t ∈ timeLattice S.spacing, ∀ u : H,
      ‖S.evolution t u - vacuumPart S.vacuum u‖ ≤
        Real.exp (-physicalRate S.spacing (latticeRate ρ) * t) * ‖excitedPart S.vacuum u‖ := by
  intro t ht u
  rw [← map_excitedPart (S.evolution t) (S.evolution_vacuum t) u]
  exact S.evolution_decay_on_timeLattice hρ h t ht _ (excitedPart_orthogonal S.vacuum_norm u)

/-- Exact semigroup law on the time lattice: `T(t + s) = T(t) T(s)` for `t, s ∈ a ℕ`. -/
theorem evolution_add_on_timeLattice :
    ∀ t ∈ timeLattice S.spacing, ∀ s ∈ timeLattice S.spacing,
      S.evolution (t + s) = S.evolution t * S.evolution s := by
  rintro _ ⟨n, rfl⟩ _ ⟨k, rfl⟩
  have hsum : (n : ℝ) * S.spacing + (k : ℝ) * S.spacing = ((n + k : ℕ) : ℝ) * S.spacing := by
    push_cast
    ring
  rw [hsum, S.evolution_lattice, S.evolution_lattice, S.evolution_lattice, pow_add]

/-- Decay at every real time `t ≥ 0` for any rate `0 ≤ m ≤ m_phys(a)`, at the cost of the
prefactor `exp (m a)` coming from the last incomplete step. -/
theorem evolution_decay_all_times {ρ m : ℝ} (hρ : 0 < ρ) (h : S.StepContraction ρ)
    (hm0 : 0 ≤ m) (hm : m ≤ physicalRate S.spacing (latticeRate ρ)) :
    ∀ t, 0 ≤ t → ∀ u : H, ⟪S.vacuum, u⟫_ℂ = 0 →
      ‖S.evolution t u‖ ≤ Real.exp (m * S.spacing) * Real.exp (-m * t) * ‖u‖ := by
  intro t ht u hu
  have hpow := S.pow_contraction hρ.le h (elapsedSteps S.spacing t) u hu
  rw [stepFactor_pow_eq_exp_physicalTime S.spacing_pos hρ] at hpow
  have hle : (elapsedSteps S.spacing t : ℝ) * S.spacing ≤ t := elapsedSteps_mul_le S.spacing_pos ht
  have hgt : t - S.spacing < (elapsedSteps S.spacing t : ℝ) * S.spacing :=
    sub_lt_elapsedSteps_mul S.spacing_pos
  have hnn : 0 ≤ (elapsedSteps S.spacing t : ℝ) * S.spacing :=
    mul_nonneg (Nat.cast_nonneg _) S.spacing_pos.le
  have h1 : -physicalRate S.spacing (latticeRate ρ) * ((elapsedSteps S.spacing t : ℝ) * S.spacing)
      ≤ -m * ((elapsedSteps S.spacing t : ℝ) * S.spacing) := by nlinarith
  have h2 : -m * ((elapsedSteps S.spacing t : ℝ) * S.spacing) ≤ m * S.spacing + -m * t := by
    nlinarith
  have hexp : Real.exp (-physicalRate S.spacing (latticeRate ρ) *
      ((elapsedSteps S.spacing t : ℝ) * S.spacing)) ≤
      Real.exp (m * S.spacing) * Real.exp (-m * t) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (h1.trans h2)
  exact hpow.trans (mul_le_mul_of_nonneg_right hexp (norm_nonneg u))

theorem pow_eigenvector {ρ : ℝ} (v : H) (heig : S.transfer v = (ρ : ℂ) • v) (n : ℕ) :
    (S.transfer ^ n) v = ((ρ ^ n : ℝ) : ℂ) • v := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul, heig, smul_smul]
    congr 1
    push_cast
    ring

/-- An eigenvector with eigenvalue `ρ ≠ 1` of the symmetric transfer operator is orthogonal to
the vacuum. -/
theorem eigenvector_orthogonal_vacuum {ρ : ℝ} (hρ1 : ρ ≠ 1) (v : H)
    (heig : S.transfer v = (ρ : ℂ) • v) : ⟪S.vacuum, v⟫_ℂ = 0 := by
  have h := S.transfer_inner_vacuum v
  rw [heig, inner_smul_right] at h
  have h2 : ((ρ : ℂ) - 1) * ⟪S.vacuum, v⟫_ℂ = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (by exact_mod_cast sub_eq_zero.mp h3) hρ1
  · exact h3

/-- On an eigenvector with eigenvalue `ρ`, the lattice evolution decays exactly at `m_phys(a)`. -/
theorem evolution_eigenvector_exact {ρ : ℝ} (hρ : 0 < ρ) (v : H)
    (heig : S.transfer v = (ρ : ℂ) • v) :
    ∀ t ∈ timeLattice S.spacing,
      ‖S.evolution t v‖ = Real.exp (-physicalRate S.spacing (latticeRate ρ) * t) * ‖v‖ := by
  rintro t ⟨n, rfl⟩
  rw [S.evolution_lattice n, S.pow_eigenvector v heig n, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (pow_nonneg hρ.le n), stepFactor_pow_eq_exp_physicalTime S.spacing_pos hρ n]

/-- Sharpness: if `ρ` is attained on a nonzero eigenvector, no rate above `m_phys(a)` holds at any
positive lattice time. -/
theorem physicalRate_not_improvable {ρ m : ℝ} (hρ : 0 < ρ) (v : H) (hv : v ≠ 0)
    (heig : S.transfer v = (ρ : ℂ) • v) (hm : physicalRate S.spacing (latticeRate ρ) < m) :
    ∀ t ∈ timeLattice S.spacing, 0 < t → Real.exp (-m * t) * ‖v‖ < ‖S.evolution t v‖ := by
  intro t ht htpos
  rw [S.evolution_eigenvector_exact hρ v heig t ht]
  have hexp : Real.exp (-m * t) < Real.exp (-physicalRate S.spacing (latticeRate ρ) * t) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  exact mul_lt_mul_of_pos_right hexp (norm_pos_iff.mpr hv)

end LatticeTransferStep

/-! ## 3. The repository's `TransferMatrixSystem` as one regularization

`TransferMatrixSystem.massGap = (1/a) log (λ₀/λ₁)` is defined at one fixed spacing `a`. Normalizing
by `λ₀` gives a `LatticeTransferStep` whose physical rate is exactly `massGap`; the decay below is
therefore a fixed-spacing statement. Nothing in `TransferMatrixSystem` is uniform in `a`. -/

section TransferMatrixBridge

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `TransferMatrixSystem` normalized by its vacuum eigenvalue `λ₀`. -/
def transferSystemStep (sys : TransferMatrixSystem H) : LatticeTransferStep H where
  spacing := sys.a
  spacing_pos := sys.a_pos
  transfer := ((sys.lambda0⁻¹ : ℝ) : ℂ) • sys.T
  vacuum := sys.vacuum
  vacuum_norm := sys.vacuum_norm
  transfer_vacuum := by
    rw [smul_apply, sys.vacuum_eigenpair, smul_smul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ sys.lambda0_pos.ne', Complex.ofReal_one, one_smul]
  transfer_symmetric := by
    intro u v
    rw [smul_apply, smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      sys.T_symmetric u v]

@[simp]
theorem transferSystemStep_spacing (sys : TransferMatrixSystem H) :
    (transferSystemStep sys).spacing = sys.a := rfl

@[simp]
theorem transferSystemStep_vacuum (sys : TransferMatrixSystem H) :
    (transferSystemStep sys).vacuum = sys.vacuum := rfl

theorem transferSystemStep_contraction (sys : TransferMatrixSystem H) :
    (transferSystemStep sys).StepContraction (sys.lambda1 / sys.lambda0) := by
  intro u hu
  have hc := sys.vacuum_complement_contraction u hu
  have hinv : 0 ≤ sys.lambda0⁻¹ := inv_nonneg.mpr sys.lambda0_pos.le
  change ‖(((sys.lambda0⁻¹ : ℝ) : ℂ) • sys.T) u‖ ≤ sys.lambda1 / sys.lambda0 * ‖u‖
  rw [smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg hinv]
  calc sys.lambda0⁻¹ * ‖sys.T u‖ ≤ sys.lambda0⁻¹ * (sys.lambda1 * ‖u‖) :=
        mul_le_mul_of_nonneg_left hc hinv
    _ = sys.lambda1 / sys.lambda0 * ‖u‖ := by ring

/-- The repository's `massGap` is the physical rate `latticeRate (λ₁/λ₀) / a` of the normalized
transfer operator. -/
theorem transferSystemStep_physicalRate_eq_massGap (sys : TransferMatrixSystem H) :
    physicalRate sys.a (latticeRate (sys.lambda1 / sys.lambda0)) = sys.massGap := by
  unfold physicalRate latticeRate TransferMatrixSystem.massGap
    TransferMatrixSystem.excitedEnergy TransferMatrixSystem.groundEnergy
  rw [Real.log_div sys.lambda1_pos.ne' sys.lambda0_pos.ne']
  ring

/-- Fixed-spacing physical-time decay at rate `massGap`, on the time lattice of that one spacing. -/
theorem transferSystem_massGap_physicalTime_decay (sys : TransferMatrixSystem H) :
    ∀ t ∈ timeLattice sys.a, ∀ u : H, ⟪sys.vacuum, u⟫_ℂ = 0 →
      ‖(transferSystemStep sys).evolution t u‖ ≤ Real.exp (-sys.massGap * t) * ‖u‖ := by
  intro t ht u hu
  have h := (transferSystemStep sys).evolution_decay_on_timeLattice
    (div_pos sys.lambda1_pos sys.lambda0_pos) (transferSystemStep_contraction sys) t ht u hu
  rwa [transferSystemStep_spacing, transferSystemStep_physicalRate_eq_massGap] at h

end TransferMatrixBridge

/-! ## 4. Cutoff paths and the uniformity predicate -/

/-- A temporal cutoff path: spacings `a_n > 0` with `a_n → 0`. -/
structure TemporalCutoffPath where
  spacing : ℕ → ℝ
  spacing_pos : ∀ n, 0 < spacing n
  spacing_tendsto_zero : Tendsto spacing atTop (𝓝 0)

/-- **The uniformity predicate** "`m_phys(a_n) ≥ m0 > 0` along the cutoff sequence".
Quantifier order: one `m0 > 0` is chosen first, then the bound holds for every cutoff `n`. -/
def UniformPhysicalRateFloor (a mLatt : ℕ → ℝ) : Prop :=
  ∃ m0 : ℝ, 0 < m0 ∧ ∀ n, m0 ≤ physicalRate (a n) (mLatt n)

/-- The reversed quantifier order: a positive floor may be chosen after each cutoff. This is
only positivity of every individual physical rate. -/
def CutoffwisePositivePhysicalRate (a mLatt : ℕ → ℝ) : Prop :=
  ∀ n, ∃ m0 : ℝ, 0 < m0 ∧ m0 ≤ physicalRate (a n) (mLatt n)

/-- Two-sided control: a floor `m0 > 0` and a ceiling `M`, both chosen before the cutoff index.
The ceiling is what excludes physical rates that diverge as the cutoff is removed. -/
def TwoSidedPhysicalRateControl (a mLatt : ℕ → ℝ) : Prop :=
  ∃ m0 M : ℝ, 0 < m0 ∧ ∀ n, m0 ≤ physicalRate (a n) (mLatt n) ∧ physicalRate (a n) (mLatt n) ≤ M

theorem UniformPhysicalRateFloor.cutoffwise {a mLatt : ℕ → ℝ}
    (h : UniformPhysicalRateFloor a mLatt) : CutoffwisePositivePhysicalRate a mLatt := by
  obtain ⟨m0, hm0, hle⟩ := h
  exact fun n => ⟨m0, hm0, hle n⟩

theorem cutoffwisePositivePhysicalRate_iff {a mLatt : ℕ → ℝ} :
    CutoffwisePositivePhysicalRate a mLatt ↔ ∀ n, 0 < physicalRate (a n) (mLatt n) := by
  constructor
  · intro h n
    obtain ⟨m0, hm0, hle⟩ := h n
    exact hm0.trans_le hle
  · intro h n
    exact ⟨_, h n, le_rfl⟩

theorem TwoSidedPhysicalRateControl.uniformFloor {a mLatt : ℕ → ℝ}
    (h : TwoSidedPhysicalRateControl a mLatt) : UniformPhysicalRateFloor a mLatt := by
  obtain ⟨m0, M, hm0, hle⟩ := h
  exact ⟨m0, hm0, fun n => (hle n).1⟩

/-- The uniform floor is a statement about how the per-step factor depends on the spacing:
`ρ_n ≤ exp (-m0 a_n)` with one `m0 > 0`. It is not a fixed per-step constant. -/
theorem uniformPhysicalRateFloor_iff_stepFactor {a ρ : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hρ : ∀ n, 0 < ρ n) :
    UniformPhysicalRateFloor a (fun n => latticeRate (ρ n)) ↔
      ∃ m0 : ℝ, 0 < m0 ∧ ∀ n, ρ n ≤ Real.exp (-(m0 * a n)) := by
  constructor
  · rintro ⟨m0, hm0, hle⟩
    exact ⟨m0, hm0, fun n => (le_physicalRate_iff_stepFactor_le (ha n) (hρ n)).mp (hle n)⟩
  · rintro ⟨m0, hm0, hle⟩
    exact ⟨m0, hm0, fun n => (le_physicalRate_iff_stepFactor_le (ha n) (hρ n)).mpr (hle n)⟩

/-- Two-sided control in per-step form: `exp (-M a_n) ≤ ρ_n ≤ exp (-m0 a_n)`. -/
theorem twoSidedPhysicalRateControl_iff_stepFactor {a ρ : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hρ : ∀ n, 0 < ρ n) :
    TwoSidedPhysicalRateControl a (fun n => latticeRate (ρ n)) ↔
      ∃ m0 M : ℝ, 0 < m0 ∧
        ∀ n, Real.exp (-(M * a n)) ≤ ρ n ∧ ρ n ≤ Real.exp (-(m0 * a n)) := by
  constructor
  · rintro ⟨m0, M, hm0, hle⟩
    exact ⟨m0, M, hm0, fun n =>
      ⟨(physicalRate_le_iff_le_stepFactor (ha n) (hρ n)).mp (hle n).2,
        (le_physicalRate_iff_stepFactor_le (ha n) (hρ n)).mp (hle n).1⟩⟩
  · rintro ⟨m0, M, hm0, hle⟩
    exact ⟨m0, M, hm0, fun n =>
      ⟨(le_physicalRate_iff_stepFactor_le (ha n) (hρ n)).mpr (hle n).2,
        (physicalRate_le_iff_le_stepFactor (ha n) (hρ n)).mpr (hle n).1⟩⟩

/-- Along `a_n → 0`, two-sided control forces the per-step factor to tend to `1`. -/
theorem TwoSidedPhysicalRateControl.stepFactor_tendsto_one {a ρ : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hρ : ∀ n, 0 < ρ n) (hlim : Tendsto a atTop (𝓝 0))
    (h : TwoSidedPhysicalRateControl a (fun n => latticeRate (ρ n))) :
    Tendsto ρ atTop (𝓝 1) := by
  obtain ⟨m0, M, _, hbr⟩ := (twoSidedPhysicalRateControl_iff_stepFactor ha hρ).mp h
  have hexp : ∀ c : ℝ, Tendsto (fun n => Real.exp (-(c * a n))) atTop (𝓝 1) := by
    intro c
    have h1 := ((hlim.const_mul c).neg).rexp
    rwa [mul_zero, neg_zero, Real.exp_zero] at h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (hexp M) (hexp m0)
    (fun n => (hbr n).1) (fun n => (hbr n).2)

/-- A fixed per-step factor `ρ0 < 1` along `a_n → 0` is never under two-sided control. -/
theorem fixed_stepFactor_not_twoSidedPhysicalRateControl {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hlim : Tendsto a atTop (𝓝 0)) {ρ0 : ℝ} (h0 : 0 < ρ0) (h1 : ρ0 < 1) :
    ¬ TwoSidedPhysicalRateControl a (fun _ => latticeRate ρ0) := by
  intro h
  have hlim1 := TwoSidedPhysicalRateControl.stepFactor_tendsto_one (ρ := fun _ => ρ0) ha
    (fun _ => h0) hlim h
  have heq : ρ0 = 1 := tendsto_nhds_unique tendsto_const_nhds hlim1
  linarith

/-- Pointwise positivity plus convergence to a positive limit gives one uniform floor. -/
theorem exists_uniform_floor_of_pos_of_tendsto {r : ℕ → ℝ} {m : ℝ} (hpos : ∀ n, 0 < r n)
    (hm : 0 < m) (hlim : Tendsto r atTop (𝓝 m)) : ∃ m0 : ℝ, 0 < m0 ∧ ∀ n, m0 ≤ r n := by
  have hfin : ∀ N : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ n < N, c ≤ r n := by
    intro N
    induction N with
    | zero => exact ⟨1, one_pos, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
    | succ k ih =>
      obtain ⟨c, hc, hle⟩ := ih
      refine ⟨min c (r k), lt_min hc (hpos k), fun n hn => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | h
      · exact (min_le_left _ _).trans (hle n h)
      · rw [h]
        exact min_le_right _ _
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 hlim).1 (m / 2) (by linarith))
  obtain ⟨c, hc, hle⟩ := hfin N
  refine ⟨min c (m / 2), lt_min hc (by linarith), fun n => ?_⟩
  rcases lt_or_ge n N with h | h
  · exact (min_le_left _ _).trans (hle n h)
  · exact (min_le_right _ _).trans (hN n h).le

/-- The repository's target `YangMillsExistenceAndMassGapConjecture` already contains a uniform
physical floor on its lattice gap sequence, which is stated in physical units there. This shows
the floor is a necessary part of the target; it does not prove the target. -/
theorem massGapConjecture_contains_uniform_physical_floor
    (h : YangMillsExistenceAndMassGapConjecture) :
    ∃ seq : LatticeApproximantSequence, ∃ m0 : ℝ, 0 < m0 ∧ ∀ L, m0 ≤ seq.latticeGap L := by
  obtain ⟨seq, cont, hgap, _, _, hpos, _⟩ := h
  exact ⟨seq, exists_uniform_floor_of_pos_of_tendsto seq.latticeGap_pos hpos hgap⟩

/-! ## 5. Decay uniform in the cutoff -/

section UniformDecay

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Uniform physical-time decay on the time lattices.**
Quantifier order: given the floor `m0` (fixed before `n`), for every cutoff `n`, every lattice time
`t ∈ a_n ℕ` and every vector `u`, the excited part decays at least like `exp (-m0 t)`. -/
theorem uniform_decay_on_timeLattices_of_floor {S : ℕ → LatticeTransferStep H} {ρ : ℕ → ℝ}
    (hρ : ∀ n, 0 < ρ n) (hstep : ∀ n, (S n).StepContraction (ρ n)) {m0 : ℝ}
    (hfloor : ∀ n, m0 ≤ physicalRate (S n).spacing (latticeRate (ρ n))) :
    ∀ n, ∀ t ∈ timeLattice (S n).spacing, ∀ u : H,
      ‖(S n).evolution t u - vacuumPart (S n).vacuum u‖ ≤
        Real.exp (-m0 * t) * ‖excitedPart (S n).vacuum u‖ := by
  intro n t ht u
  have h := (S n).evolution_excitedPart_decay_on_timeLattice (hρ n) (hstep n) t ht u
  have ht0 : 0 ≤ t := timeLattice_nonneg (S n).spacing_pos ht
  have hexp : Real.exp (-physicalRate (S n).spacing (latticeRate (ρ n)) * t) ≤
      Real.exp (-m0 * t) := Real.exp_le_exp.mpr (by nlinarith [hfloor n])
  exact h.trans (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))

/-- The same statement with the floor packaged as `UniformPhysicalRateFloor`. -/
theorem uniform_physicalTime_decay {S : ℕ → LatticeTransferStep H} {ρ : ℕ → ℝ}
    (hρ : ∀ n, 0 < ρ n) (hstep : ∀ n, (S n).StepContraction (ρ n))
    (hfloor : UniformPhysicalRateFloor (fun n => (S n).spacing) (fun n => latticeRate (ρ n))) :
    ∃ m0 : ℝ, 0 < m0 ∧ ∀ n, ∀ t ∈ timeLattice (S n).spacing, ∀ u : H,
      ‖(S n).evolution t u - vacuumPart (S n).vacuum u‖ ≤
        Real.exp (-m0 * t) * ‖excitedPart (S n).vacuum u‖ := by
  obtain ⟨m0, hm0, hle⟩ := hfloor
  exact ⟨m0, hm0, uniform_decay_on_timeLattices_of_floor hρ hstep hle⟩

end UniformDecay

/-! ## 6. Strong limits: what the floor transfers, and what a fixed factor destroys -/

section StrongLimit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Dense-core transfer with cutoff-dependent factors `q n → q∞`. This extends
`YangMillsPhysicalGap.dense_core_decay_limit_with_vacuum`, which needs one constant factor. -/
theorem dense_core_decay_limit_of_tendsto_factor (D : Set H) (hD : Dense D)
    (A : ℕ → H →L[ℂ] H) (B : H →L[ℂ] H) (Ωn : ℕ → H) (Ω : H) (q : ℕ → ℝ) (qLim : ℝ)
    (hΩ : Tendsto Ωn atTop (𝓝 Ω)) (hnorm : ∀ n, ‖Ωn n‖ = 1)
    (hfix : ∀ n, A n (Ωn n) = Ωn n)
    (hstrong : ∀ u ∈ D, Tendsto (fun n => A n u) atTop (𝓝 (B u)))
    (hq : Tendsto q atTop (𝓝 qLim))
    (hdecay : ∀ n u, u ∈ D →
      ‖A n (excitedPart (Ωn n) u)‖ ≤ q n * ‖excitedPart (Ωn n) u‖) :
    B Ω = Ω ∧ ∀ u : H, ⟪Ω, u⟫_ℂ = 0 → ‖B u‖ ≤ qLim * ‖u‖ := by
  have hcore : ∀ u ∈ D, ‖B u - vacuumPart Ω u‖ ≤ qLim * ‖excitedPart Ω u‖ := by
    intro u hu
    have hp := vacuumPart_tendsto hΩ u
    have hleft := ((hstrong u hu).sub hp).norm
    have hright := hq.mul (((tendsto_const_nhds (x := u)).sub hp).norm)
    apply le_of_tendsto_of_tendsto hleft hright
    exact Eventually.of_forall fun n => by
      have hd := hdecay n u hu
      rw [map_excitedPart (A n) (hfix n) u] at hd
      exact hd
  have hall : ∀ u : H, ‖B u - vacuumPart Ω u‖ ≤ qLim * ‖excitedPart Ω u‖ := fun u =>
    le_on_closure hcore
      ((B.continuous.sub (continuous_vacuumPart Ω)).norm.continuousOn)
      ((continuous_const.mul (continuous_excitedPart Ω).norm).continuousOn) (hD u)
  have hnormΩ := normalized_vacuum_limit hΩ hnorm
  constructor
  · have hself := hall Ω
    rw [vacuumPart_self hnormΩ] at hself
    have hexc : excitedPart Ω Ω = 0 := by simp [excitedPart, vacuumPart_self hnormΩ]
    rw [hexc, norm_zero, mul_zero] at hself
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hself (norm_nonneg _)))
  · intro u hu
    simpa [excitedPart, vacuumPart, hu] using hall u

/-- **The uniform floor survives the strong limit, at every real time.**
Inputs: a cutoff path `a_n → 0`, regularizations with per-step factors `ρ_n` and one floor
`m0 ≤ m_phys(a_n)` for all `n`, vacuum convergence, and strong convergence of the lattice
evolutions `T_n ^ ⌊t / a_n⌋₊` on a dense core at each `t ≥ 0`. Output: the limit fixes the
vacuum and satisfies `‖T(t) u‖ ≤ exp (-m0 t) ‖u‖` on the vacuum complement for every real
`t ≥ 0`, with prefactor exactly `1` because the incomplete-step prefactor `exp (m0 a_n) → 1`. -/
theorem uniform_floor_decay_survives_strong_limit (D : Set H) (hD : Dense D)
    (P : TemporalCutoffPath) (S : ℕ → LatticeTransferStep H)
    (hsp : ∀ n, (S n).spacing = P.spacing n)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n) (hstep : ∀ n, (S n).StepContraction (ρ n))
    {m0 : ℝ} (hm0 : 0 ≤ m0) (hfloor : ∀ n, m0 ≤ physicalRate (P.spacing n) (latticeRate (ρ n)))
    (T : ℝ → H →L[ℂ] H) (Ω : H) (hΩ : Tendsto (fun n => (S n).vacuum) atTop (𝓝 Ω))
    (hstrong : ∀ t, 0 ≤ t → ∀ u ∈ D,
      Tendsto (fun n => (S n).evolution t u) atTop (𝓝 (T t u))) :
    ∀ t, 0 ≤ t → T t Ω = Ω ∧ ∀ u : H, ⟪Ω, u⟫_ℂ = 0 → ‖T t u‖ ≤ Real.exp (-m0 * t) * ‖u‖ := by
  intro t ht
  have h1 : Tendsto (fun n => Real.exp (m0 * P.spacing n)) atTop (𝓝 1) := by
    have h := (P.spacing_tendsto_zero.const_mul m0).rexp
    rwa [mul_zero, Real.exp_zero] at h
  have hq : Tendsto (fun n => Real.exp (m0 * P.spacing n) * Real.exp (-m0 * t)) atTop
      (𝓝 (Real.exp (-m0 * t))) := by
    simpa using h1.mul_const (Real.exp (-m0 * t))
  refine dense_core_decay_limit_of_tendsto_factor D hD (fun n => (S n).evolution t) (T t)
    (fun n => (S n).vacuum) Ω _ _ hΩ (fun n => (S n).vacuum_norm)
    (fun n => (S n).evolution_vacuum t) (hstrong t ht) hq ?_
  intro n u _
  have hfl : m0 ≤ physicalRate (S n).spacing (latticeRate (ρ n)) := by
    rw [hsp n]
    exact hfloor n
  have h := (S n).evolution_decay_all_times (hρ n) (hstep n) hm0 hfl t ht
    (excitedPart (S n).vacuum u) (excitedPart_orthogonal (S n).vacuum_norm u)
  rw [hsp n] at h
  exact h

/-- The floor gives generator coercivity `m0 ‖u‖² ≤ Re ⟪u, A u⟫` on the vacuum complement of the
generator domain, through `YangMillsPhysicalGap.generator_coercivity_of_decay`. Identification of
`T` as a semigroup with generator `A` is the supplied derivative `hgenerator`. -/
theorem uniform_floor_generator_coercivity (D : Set H) (hD : Dense D)
    (P : TemporalCutoffPath) (S : ℕ → LatticeTransferStep H)
    (hsp : ∀ n, (S n).spacing = P.spacing n)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n) (hstep : ∀ n, (S n).StepContraction (ρ n))
    {m0 : ℝ} (hm0 : 0 ≤ m0) (hfloor : ∀ n, m0 ≤ physicalRate (P.spacing n) (latticeRate (ρ n)))
    (T : ℝ → H →L[ℂ] H) (Ω : H) (hΩ : Tendsto (fun n => (S n).vacuum) atTop (𝓝 Ω))
    (hstrong : ∀ t, 0 ≤ t → ∀ u ∈ D,
      Tendsto (fun n => (S n).evolution t u) atTop (𝓝 (T t u)))
    (domain : Submodule ℂ H) (generator : domain →ₗ[ℂ] H)
    (hzero : ∀ u : domain, T 0 u = u)
    (hgenerator : ∀ u : domain,
      HasDerivWithinAt (fun t : ℝ => T t u) (-(generator u)) (Set.Ioi 0) 0) :
    (∀ t, 0 ≤ t → T t Ω = Ω) ∧
      ∀ u : domain, ⟪Ω, (u : H)⟫_ℂ = 0 →
        m0 * ‖(u : H)‖ ^ 2 ≤ (⟪(u : H), generator u⟫_ℂ).re := by
  have hlim := uniform_floor_decay_survives_strong_limit D hD P S hsp ρ hρ hstep hm0 hfloor
    T Ω hΩ hstrong
  exact ⟨fun t ht => (hlim t ht).1, fun u hu =>
    generator_coercivity_of_decay T u (generator u) m0 (hzero u) (hgenerator u)
      (fun t ht => (hlim t ht.le).2 u hu)⟩

/-- A lattice lower bound with one energy ceiling `M` survives the strong limit: the excited part
of `v` decays no faster than `exp (-M t)` in the limit. -/
theorem excitation_lower_bound_survives_strong_limit (P : TemporalCutoffPath)
    (S : ℕ → LatticeTransferStep H) (hsp : ∀ n, (S n).spacing = P.spacing n)
    (T : ℝ → H →L[ℂ] H) (Ω : H) (hΩ : Tendsto (fun n => (S n).vacuum) atTop (𝓝 Ω))
    {M : ℝ} (hM : 0 ≤ M) (v : H)
    (hv : ∀ t, 0 ≤ t → Tendsto (fun n => (S n).evolution t v) atTop (𝓝 (T t v)))
    (hlower : ∀ n (k : ℕ), Real.exp (-M * ((k : ℝ) * P.spacing n)) *
        ‖excitedPart (S n).vacuum v‖ ≤ ‖((S n).transfer ^ k) (excitedPart (S n).vacuum v)‖) :
    ∀ t, 0 ≤ t → Real.exp (-M * t) * ‖excitedPart Ω v‖ ≤ ‖T t v - vacuumPart Ω v‖ := by
  intro t ht
  have hp := vacuumPart_tendsto hΩ v
  have hleft : Tendsto (fun n => Real.exp (-M * t) * ‖excitedPart (S n).vacuum v‖) atTop
      (𝓝 (Real.exp (-M * t) * ‖excitedPart Ω v‖)) :=
    tendsto_const_nhds.mul (((tendsto_const_nhds (x := v)).sub hp).norm)
  have hright : Tendsto (fun n => ‖(S n).evolution t v - vacuumPart (S n).vacuum v‖) atTop
      (𝓝 ‖T t v - vacuumPart Ω v‖) := ((hv t ht).sub hp).norm
  refine le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall fun n => ?_)
  have hk := hlower n (elapsedSteps (S n).spacing t)
  have hle : (elapsedSteps (S n).spacing t : ℝ) * P.spacing n ≤ t := by
    rw [← hsp n]
    exact elapsedSteps_mul_le (S n).spacing_pos ht
  have hexp : Real.exp (-M * t) ≤
      Real.exp (-M * ((elapsedSteps (S n).spacing t : ℝ) * P.spacing n)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  show Real.exp (-M * t) * ‖excitedPart (S n).vacuum v‖ ≤
    ‖(S n).evolution t v - vacuumPart (S n).vacuum v‖
  rw [← map_excitedPart ((S n).evolution t) ((S n).evolution_vacuum t) v]
  exact (mul_le_mul_of_nonneg_right hexp (norm_nonneg _)).trans hk

/-- With a nonzero limiting excited part, the limit evolution never collapses onto the vacuum
part of `v`. -/
theorem excitation_survives_strong_limit (P : TemporalCutoffPath)
    (S : ℕ → LatticeTransferStep H) (hsp : ∀ n, (S n).spacing = P.spacing n)
    (T : ℝ → H →L[ℂ] H) (Ω : H) (hΩ : Tendsto (fun n => (S n).vacuum) atTop (𝓝 Ω))
    {M : ℝ} (hM : 0 ≤ M) (v : H)
    (hv : ∀ t, 0 ≤ t → Tendsto (fun n => (S n).evolution t v) atTop (𝓝 (T t v)))
    (hlower : ∀ n (k : ℕ), Real.exp (-M * ((k : ℝ) * P.spacing n)) *
        ‖excitedPart (S n).vacuum v‖ ≤ ‖((S n).transfer ^ k) (excitedPart (S n).vacuum v)‖)
    (hv0 : excitedPart Ω v ≠ 0) :
    ∀ t, 0 ≤ t → T t v ≠ vacuumPart Ω v := by
  intro t ht heq
  have h := excitation_lower_bound_survives_strong_limit P S hsp T Ω hΩ hM v hv hlower t ht
  rw [heq, sub_self, norm_zero] at h
  have hpos : 0 < Real.exp (-M * t) * ‖excitedPart Ω v‖ :=
    mul_pos (Real.exp_pos _) (norm_pos_iff.mpr hv0)
  linarith

/-- Between `0` and the first lattice time the lattice evolution is the identity, so for any
`m > 0` it violates the real-time bound `‖T(t) u‖ ≤ exp (-m t) ‖u‖` on every nonzero
vacuum-orthogonal `u`. The real-time premise `hdecay` of
`YangMillsPhysicalGap.evolution_decay_survives_dense_core_limit` therefore cannot be checked on
the lattice evolutions themselves; `uniform_floor_decay_survives_strong_limit` obtains it in the
limit. -/
theorem lattice_evolution_violates_realTime_decay_before_first_step
    (S : LatticeTransferStep H) {m t : ℝ} (hm : 0 < m) (ht0 : 0 < t) (hta : t < S.spacing)
    (u : H) (hu : u ≠ 0) : Real.exp (-m * t) * ‖u‖ < ‖S.evolution t u‖ := by
  have hsteps : elapsedSteps S.spacing t = 0 := by
    unfold elapsedSteps
    exact Nat.floor_eq_zero.mpr ((div_lt_one S.spacing_pos).mpr hta)
  have hev : S.evolution t u = u := by
    unfold LatticeTransferStep.evolution
    rw [hsteps, pow_zero, one_apply_eq_self]
  rw [hev]
  have hexp : Real.exp (-m * t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hpos := norm_pos_iff.mpr hu
  nlinarith

/-- `⌊t / a_n⌋₊ → ∞` along a cutoff path for every fixed `t > 0`. -/
theorem elapsedSteps_tendsto_atTop (P : TemporalCutoffPath) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => elapsedSteps (P.spacing n) t) atTop atTop := by
  have hinv : Tendsto (fun n => (P.spacing n)⁻¹) atTop atTop :=
    Tendsto.inv_tendsto_nhdsGT_zero (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      P.spacing_tendsto_zero (Eventually.of_forall fun n => P.spacing_pos n))
  have hdiv : Tendsto (fun n => t / P.spacing n) atTop atTop := by
    simpa [div_eq_mul_inv] using hinv.const_mul_atTop ht
  exact tendsto_nat_floor_atTop.comp hdiv

/-- **A fixed per-step factor along `a_n → 0` collapses every strong limit.**
If one constant `ρ0 < 1` (for example `7 / 8`) bounds the transfer step at every cutoff of a path
with `a_n → 0`, then at every `t > 0` the strong limit of the lattice evolutions is the vacuum
projection: all excitations are annihilated, i.e. the physical rate is infinite. -/
theorem fixed_step_contraction_strong_limit_is_vacuum_projection (D : Set H) (hD : Dense D)
    (P : TemporalCutoffPath) (S : ℕ → LatticeTransferStep H)
    (hsp : ∀ n, (S n).spacing = P.spacing n)
    {ρ0 : ℝ} (hρ0 : 0 ≤ ρ0) (hρ1 : ρ0 < 1) (hstep : ∀ n, (S n).StepContraction ρ0)
    (T : ℝ → H →L[ℂ] H) (Ω : H) (hΩ : Tendsto (fun n => (S n).vacuum) atTop (𝓝 Ω))
    (hstrong : ∀ t, 0 < t → ∀ u ∈ D,
      Tendsto (fun n => (S n).evolution t u) atTop (𝓝 (T t u))) :
    ∀ t, 0 < t → ∀ u : H, T t u = vacuumPart Ω u := by
  intro t ht
  have hN : Tendsto (fun n => elapsedSteps (S n).spacing t) atTop atTop := by
    simpa only [hsp] using elapsedSteps_tendsto_atTop P ht
  have hq : Tendsto (fun n => ρ0 ^ elapsedSteps (S n).spacing t) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp hN
  have hlim := dense_core_decay_limit_of_tendsto_factor D hD (fun n => (S n).evolution t) (T t)
    (fun n => (S n).vacuum) Ω _ 0 hΩ (fun n => (S n).vacuum_norm)
    (fun n => (S n).evolution_vacuum t) (hstrong t ht) hq
    (fun n u _ => (S n).pow_contraction hρ0 (hstep n) _ _
      (excitedPart_orthogonal (S n).vacuum_norm u))
  have hnormΩ : ‖Ω‖ = 1 := normalized_vacuum_limit hΩ (fun n => (S n).vacuum_norm)
  intro u
  have hexc : T t (excitedPart Ω u) = 0 := by
    have h := hlim.2 (excitedPart Ω u) (excitedPart_orthogonal hnormΩ u)
    rw [zero_mul] at h
    exact norm_le_zero_iff.mp h
  have hvac : T t (vacuumPart Ω u) = vacuumPart Ω u := by
    simp only [vacuumPart, map_smul, hlim.1]
  have hsplit : u = vacuumPart Ω u + excitedPart Ω u := by
    rw [excitedPart]
    abel
  calc T t u = T t (vacuumPart Ω u + excitedPart Ω u) := congrArg (T t) hsplit
    _ = vacuumPart Ω u := by rw [map_add, hvac, hexc, add_zero]

/-- If the limit of a fixed-factor family is also strongly continuous at `t = 0`, the vacuum
complement is zero: the limiting theory has no excitations at all. -/
theorem fixed_step_contraction_strongly_continuous_limit_is_trivial (D : Set H) (hD : Dense D)
    (P : TemporalCutoffPath) (S : ℕ → LatticeTransferStep H)
    (hsp : ∀ n, (S n).spacing = P.spacing n)
    {ρ0 : ℝ} (hρ0 : 0 ≤ ρ0) (hρ1 : ρ0 < 1) (hstep : ∀ n, (S n).StepContraction ρ0)
    (T : ℝ → H →L[ℂ] H) (Ω : H) (hΩ : Tendsto (fun n => (S n).vacuum) atTop (𝓝 Ω))
    (hstrong : ∀ t, 0 < t → ∀ u ∈ D,
      Tendsto (fun n => (S n).evolution t u) atTop (𝓝 (T t u)))
    (hcont : ∀ u : H, Tendsto (fun t => T t u) (𝓝[>] 0) (𝓝 u)) :
    ∀ u : H, ⟪Ω, u⟫_ℂ = 0 → u = 0 := by
  intro u hu
  have hproj := fixed_step_contraction_strong_limit_is_vacuum_projection D hD P S hsp hρ0 hρ1
    hstep T Ω hΩ hstrong
  have hev : (fun _ : ℝ => (0 : H)) =ᶠ[𝓝[>] 0] fun t => T t u :=
    eventually_nhdsWithin_of_forall fun t ht => by
      show (0 : H) = T t u
      rw [hproj t ht u]
      simp [vacuumPart, hu]
  exact tendsto_nhds_unique (hcont u) (tendsto_const_nhds.congr' hev)

/-- A fixed per-step factor is incompatible with one uniformly bounded excitation energy: if at
every cutoff some vacuum-orthogonal `v_n ≠ 0` has `‖T_n v_n‖ ≥ exp (-M a_n) ‖v_n‖`, then for all
large `n` the step is not a `ρ0`-contraction, for any fixed `ρ0 < 1`. -/
theorem fixed_step_contraction_eventually_violates_energy_ceiling (P : TemporalCutoffPath)
    (S : ℕ → LatticeTransferStep H) (hsp : ∀ n, (S n).spacing = P.spacing n) {ρ0 M : ℝ}
    (hρ1 : ρ0 < 1) (v : ℕ → H) (hv : ∀ n, v n ≠ 0)
    (horth : ∀ n, ⟪(S n).vacuum, v n⟫_ℂ = 0)
    (hlower : ∀ n, Real.exp (-(M * (S n).spacing)) * ‖v n‖ ≤ ‖(S n).transfer (v n)‖) :
    ∀ᶠ n in atTop, ¬ (S n).StepContraction ρ0 := by
  have h1 : Tendsto (fun n => Real.exp (-(M * P.spacing n))) atTop (𝓝 1) := by
    have h := ((P.spacing_tendsto_zero.const_mul M).neg).rexp
    rwa [mul_zero, neg_zero, Real.exp_zero] at h
  filter_upwards [(tendsto_order.1 h1).1 ρ0 hρ1] with n hn hcontr
  have hvpos : 0 < ‖v n‖ := norm_pos_iff.mpr (hv n)
  have h3 := hlower n
  rw [hsp n] at h3
  have h4 : Real.exp (-(M * P.spacing n)) * ‖v n‖ ≤ ρ0 * ‖v n‖ :=
    h3.trans (hcontr (v n) (horth n))
  have h5 : Real.exp (-(M * P.spacing n)) ≤ ρ0 := le_of_mul_le_mul_right h4 hvpos
  linarith

end StrongLimit


/-! ## 7. A fixed dimensionless constant has no physical scale

For a fixed lattice rate `c > 0` applied once per step of physical length `s`, the physical rate
is `c / s`. Its behaviour along a cutoff path is decided entirely by the step-length law. -/

/-- Step length tending to zero (the bare lattice step as `a → 0`): the physical rate diverges. -/
theorem physicalRate_tendsto_atTop_of_spacing_tendsto_zero {c : ℝ} (hc : 0 < c) (s : ℕ → ℝ)
    (hs : ∀ n, 0 < s n) (hlim : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun n => physicalRate (s n) c) atTop atTop := by
  have hinv : Tendsto (fun n => (s n)⁻¹) atTop atTop :=
    Tendsto.inv_tendsto_nhdsGT_zero (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      hlim (Eventually.of_forall fun n => hs n))
  simpa [physicalRate, div_eq_mul_inv] using hinv.const_mul_atTop hc

/-- Step length diverging (an unlocked blocked scale): the physical rate collapses to zero. -/
theorem physicalRate_tendsto_zero_of_spacing_tendsto_atTop (c : ℝ) (s : ℕ → ℝ)
    (hlim : Tendsto s atTop atTop) : Tendsto (fun n => physicalRate (s n) c) atTop (𝓝 0) := by
  simpa [physicalRate] using hlim.const_div_atTop c

/-- Step length locked at a positive physical length: the physical rate converges to `c / s∞`.
The physical value is supplied by the locked length, not by `c`. -/
theorem physicalRate_tendsto_of_spacing_tendsto (c : ℝ) {s : ℕ → ℝ} {sLim : ℝ} (hsLim : sLim ≠ 0)
    (hlim : Tendsto s atTop (𝓝 sLim)) :
    Tendsto (fun n => physicalRate (s n) c) atTop (𝓝 (physicalRate sLim c)) :=
  tendsto_const_nhds.div hlim hsLim

/-- Every positive physical rate is the physical rate of `c` at a suitable step length. -/
theorem physicalRate_realizes_every_rate {c : ℝ} (hc : 0 < c) {m : ℝ} (hm : 0 < m) :
    ∃ s : ℝ, 0 < s ∧ physicalRate s c = m := by
  refine ⟨c / m, div_pos hc hm, ?_⟩
  unfold physicalRate
  field_simp

/-- The set of physical rates of a fixed `c > 0` over all step lengths is all of `(0, ∞)`. -/
theorem physicalRate_image_Ioi {c : ℝ} (hc : 0 < c) :
    (fun s => physicalRate s c) '' Set.Ioi 0 = Set.Ioi 0 := by
  ext m
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact div_pos hc hs
  · intro hm
    obtain ⟨s, hs, hsm⟩ := physicalRate_realizes_every_rate hc hm
    exact ⟨s, hs, hsm⟩

/-- For a fixed `c > 0`, the uniform floor holds exactly when the step lengths are bounded:
a property of the spacing law alone. -/
theorem fixed_rate_uniformFloor_iff_spacing_bounded {c : ℝ} (hc : 0 < c) {s : ℕ → ℝ}
    (hs : ∀ n, 0 < s n) :
    UniformPhysicalRateFloor s (fun _ => c) ↔ ∃ B : ℝ, ∀ n, s n ≤ B := by
  constructor
  · rintro ⟨m0, hm0, hle⟩
    refine ⟨c / m0, fun n => ?_⟩
    have h := hle n
    unfold physicalRate at h
    rw [le_div_iff₀ (hs n)] at h
    rw [le_div_iff₀ hm0]
    linarith [mul_comm m0 (s n)]
  · rintro ⟨B, hB⟩
    have hBpos : 0 < B := (hs 0).trans_le (hB 0)
    exact ⟨c / B, div_pos hc hBpos, fun n => div_le_div_of_nonneg_left hc.le (hs n) (hB n)⟩

/-- For a fixed `c > 0` and step lengths tending to zero the floor holds, but no ceiling does:
the uniform floor alone cannot distinguish a finite physical rate from a divergent one. -/
theorem fixed_rate_floor_without_ceiling (P : TemporalCutoffPath) {c : ℝ} (hc : 0 < c) :
    UniformPhysicalRateFloor P.spacing (fun _ => c) ∧
      ¬ TwoSidedPhysicalRateControl P.spacing (fun _ => c) := by
  constructor
  · obtain ⟨B, hB⟩ := P.spacing_tendsto_zero.bddAbove_range
    exact (fixed_rate_uniformFloor_iff_spacing_bounded hc P.spacing_pos).mpr
      ⟨B, fun n => hB ⟨n, rfl⟩⟩
  · rintro ⟨m0, M, _, hle⟩
    have htop := physicalRate_tendsto_atTop_of_spacing_tendsto_zero hc P.spacing P.spacing_pos
      P.spacing_tendsto_zero
    obtain ⟨n, hn⟩ := (htop.eventually_gt_atTop M).exists
    exact absurd (hle n).2 (not_le.mpr hn)

/-- The per-step factor `7 / 8` has dimensionless rate `log (8 / 7)`. -/
theorem latticeRate_seven_eighths : latticeRate (7 / 8) = Real.log (8 / 7) := by
  rw [latticeRate, show (7 / 8 : ℝ) = (8 / 7)⁻¹ by norm_num, Real.log_inv, neg_neg]

theorem log_eight_sevenths_pos : 0 < Real.log (8 / 7 : ℝ) := Real.log_pos (by norm_num)

/-- `7 / 8` is the repository's landing-tube sum `dobrushinRowSum4D (1 / 24) + 1 / 8`. -/
theorem seven_eighths_eq_dobrushin_landing_sum : dobrushinRowSum4D (1 / 24) + 1 / 8 = 7 / 8 := by
  norm_num [dobrushinRowSum4D, dobrushinIncidenceRowSum4D]

/-- **What a per-step factor `7 / 8` gives.** At one regularization with spacing `a`, it gives the
physical rate `log (8 / 7) / a` on the time lattice `a ℕ`, and nothing more. The rate depends
on `a`; the contraction itself is an input, not derived here from the Wilson measure. -/
theorem seven_eighths_step_physicalTime_decay {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (S : LatticeTransferStep H) (h : S.StepContraction (7 / 8)) :
    ∀ t ∈ timeLattice S.spacing, ∀ u : H, ⟪S.vacuum, u⟫_ℂ = 0 →
      ‖S.evolution t u‖ ≤ Real.exp (-(Real.log (8 / 7) / S.spacing) * t) * ‖u‖ := by
  intro t ht u hu
  have hd := S.evolution_decay_on_timeLattice (by norm_num) h t ht u hu
  rwa [physicalRate, latticeRate_seven_eighths] at hd

/-- **What `log (8 / 7)` does and does not give for the uniformity predicate.**
(1) it is the physical rate of some step length for every target rate `m > 0`;
(2) at step lengths tending to zero its physical rate diverges;
(3) at step lengths diverging its physical rate tends to zero;
(4) its uniform floor holds exactly when the step lengths are bounded.
Hence the constant carries no physical rate without the spacing law. -/
theorem log_eight_sevenths_carries_no_physical_scale :
    (∀ m : ℝ, 0 < m → ∃ s : ℝ, 0 < s ∧ physicalRate s (Real.log (8 / 7)) = m) ∧
    (∀ s : ℕ → ℝ, (∀ n, 0 < s n) → Tendsto s atTop (𝓝 0) →
      Tendsto (fun n => physicalRate (s n) (Real.log (8 / 7))) atTop atTop) ∧
    (∀ s : ℕ → ℝ, Tendsto s atTop atTop →
      Tendsto (fun n => physicalRate (s n) (Real.log (8 / 7))) atTop (𝓝 0)) ∧
    (∀ s : ℕ → ℝ, (∀ n, 0 < s n) →
      (UniformPhysicalRateFloor s (fun _ => Real.log (8 / 7)) ↔ ∃ B : ℝ, ∀ n, s n ≤ B)) :=
  ⟨fun _ hm => physicalRate_realizes_every_rate log_eight_sevenths_pos hm,
    fun s hs hlim => physicalRate_tendsto_atTop_of_spacing_tendsto_zero log_eight_sevenths_pos s
      hs hlim,
    fun s hlim => physicalRate_tendsto_zero_of_spacing_tendsto_atTop _ s hlim,
    fun _ hs => fixed_rate_uniformFloor_iff_spacing_bounded log_eight_sevenths_pos hs⟩

/-! ## 8. What the repository's existing bounds give along a cutoff path -/

/-- `strongCouplingMassGap β a` is the physical rate of the per-step factor `12 β` at step `a`. -/
theorem strongCouplingMassGap_eq_physicalRate (β a : ℝ) :
    strongCouplingMassGap β a = physicalRate a (latticeRate (12 * β)) := by
  unfold strongCouplingMassGap physicalRate latticeRate
  rw [one_div (12 * β), Real.log_inv]
  ring

/-- The locked infrared floor of `YangMillsGapLimitBridge` is the physical rate of the factor
`12 β` at the locked length `ell`; its scale is the lock hypothesis on `ell`. -/
theorem lockedIRPhysicalMassGapFloor_eq_physicalRate (β ell : ℝ) :
    YangMillsGapLimitBridge.lockedIRPhysicalMassGapFloor β ell =
      physicalRate ell (latticeRate (12 * β)) := by
  unfold YangMillsGapLimitBridge.lockedIRPhysicalMassGapFloor
    YangMillsGapLimitBridge.dimensionlessStrongCouplingGap physicalRate latticeRate
  rw [one_div (12 * β), Real.log_inv]

/-- At a fixed strong coupling `0 < β < 1/12` read at the bare spacing `a_n → 0`, the
strong-coupling formula diverges: it is not a finite physical mass. -/
theorem strongCouplingMassGap_tendsto_atTop_of_fixed_coupling {β : ℝ} (hβ : 0 < β)
    (hβ12 : 12 * β < 1) (P : TemporalCutoffPath) :
    Tendsto (fun n => strongCouplingMassGap β (P.spacing n)) atTop atTop := by
  simp only [strongCouplingMassGap_eq_physicalRate]
  exact physicalRate_tendsto_atTop_of_spacing_tendsto_zero (latticeRate_pos (by positivity) hβ12)
    _ P.spacing_pos P.spacing_tendsto_zero

/-- Along a weak-coupling path `β_n → ∞` the strong-coupling formula is eventually `≤ 0`. -/
theorem strongCouplingMassGap_eventually_nonpos_of_coupling_tendsto_atTop (a β : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hβ : Tendsto β atTop atTop) :
    ∀ᶠ n in atTop, strongCouplingMassGap (β n) (a n) ≤ 0 := by
  filter_upwards [hβ.eventually_ge_atTop (1 / 12)] with n hn
  rw [strongCouplingMassGap_eq_physicalRate]
  have h12 : 1 ≤ 12 * β n := by linarith
  have hlr : latticeRate (12 * β n) ≤ 0 := by
    have := Real.log_nonneg h12
    unfold latticeRate
    linarith
  exact div_nonpos_of_nonpos_of_nonneg hlr (ha n).le

/-- Hence the strong-coupling formula has no uniform positive floor on a weak-coupling path. -/
theorem strongCouplingMassGap_no_uniform_floor_of_coupling_tendsto_atTop (a β : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hβ : Tendsto β atTop atTop) :
    ¬ ∃ m0 : ℝ, 0 < m0 ∧ ∀ n, m0 ≤ strongCouplingMassGap (β n) (a n) := by
  rintro ⟨m0, hm0, hle⟩
  obtain ⟨n, hn⟩ :=
    (strongCouplingMassGap_eventually_nonpos_of_coupling_tendsto_atTop a β ha hβ).exists
  linarith [hle n]

/-- The repository's `wilsonPhysicalLogHamiltonianEigenvalue a_t r lam = -(1/a_t) log (lam/r)` is
the physical rate of the per-step factor `lam / r` at the single spacing `a_t`. -/
theorem wilsonPhysicalLogHamiltonianEigenvalue_eq_physicalRate (a_t r lam : ℝ) :
    wilsonPhysicalLogHamiltonianEigenvalue a_t r lam = physicalRate a_t (latticeRate (lam / r)) := by
  unfold wilsonPhysicalLogHamiltonianEigenvalue physicalRate latticeRate
  ring

/-- The repository's prescribed correlator `wilsonMeasureTimeCorrelator β a t` decays at the
strong-coupling rate. At a fixed strong coupling read at the bare spacing `a_n → 0`, it tends to
`0` at every fixed `t > 0`: the prescribed rate is infinite in the limit. -/
theorem wilsonMeasureTimeCorrelator_tendsto_zero_at_fixed_coupling {β : ℝ} (hβ : 0 < β)
    (hβ12 : 12 * β < 1) (P : TemporalCutoffPath) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => wilsonMeasureTimeCorrelator β (P.spacing n) t) atTop (𝓝 0) := by
  have hrate := (strongCouplingMassGap_tendsto_atTop_of_fixed_coupling hβ hβ12 P).atTop_mul_const ht
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hrate
  have h := hexp.const_mul (twoConfigLatticeEnsembleExpectation β)
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, wilsonMeasureTimeCorrelator, neg_mul]

/-- On a weak-coupling path `β_n → ∞` the same prescribed correlator eventually does not decay:
`C(0) ≤ C(t)` for every `t ≥ 0`, because the prescribed rate is eventually `≤ 0`. -/
theorem wilsonMeasureTimeCorrelator_eventually_nondecaying_of_coupling_tendsto_atTop
    (a β : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hβ : Tendsto β atTop atTop) :
    ∀ᶠ n in atTop, ∀ t, 0 ≤ t →
      wilsonMeasureTimeCorrelator (β n) (a n) 0 ≤ wilsonMeasureTimeCorrelator (β n) (a n) t := by
  filter_upwards [strongCouplingMassGap_eventually_nonpos_of_coupling_tendsto_atTop a β ha hβ]
    with n hn t ht
  have hpos : 0 < twoConfigLatticeEnsembleExpectation (β n) := by
    unfold twoConfigLatticeEnsembleExpectation
    rw [Real.exp_zero, mul_zero, zero_add]
    positivity
  unfold wilsonMeasureTimeCorrelator
  rw [mul_zero, Real.exp_zero, mul_one]
  have h1 : 1 ≤ Real.exp (-strongCouplingMassGap (β n) (a n) * t) :=
    Real.one_le_exp (by nlinarith)
  exact le_mul_of_one_le_right hpos.le h1

/-- Along `β_n → ∞` the Dobrushin row sum plus any nonnegative remainder eventually reaches `1`:
the bare-scale row-sum criterion supplies no per-step factor below one on that path. -/
theorem dobrushin_row_sum_eventually_ge_one_of_coupling_tendsto_atTop (β η : ℕ → ℝ)
    (hη : ∀ n, 0 ≤ η n) (hβ : Tendsto β atTop atTop) :
    ∀ᶠ n in atTop, 1 ≤ dobrushinRowSum4D (β n) + η n := by
  filter_upwards [hβ.eventually_ge_atTop (1 / 18)] with n hn
  have h18 : dobrushinRowSum4D (β n) = 18 * β n := by
    norm_num [dobrushinRowSum4D, dobrushinIncidenceRowSum4D]
  rw [h18]
  linarith [hη n]

/-- `-log (1 - x) ≤ x / (1 - x)` for `0 ≤ x < 1`. -/
theorem neg_log_one_sub_le {x : ℝ} (h1 : x < 1) : -Real.log (1 - x) ≤ x / (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  have heq : (1 - x)⁻¹ - 1 = x / (1 - x) := by
    field_simp
    ring
  linarith

/-- **The anisotropic Doeblin factor gives a vanishing physical rate.** For
`q(a_t) = 1 - exp (-C / a_t)` (`anisotropicTemporalContinuumQ`, `C > 0`) the physical rate
`latticeRate (q(a_n)) / a_n` tends to `0` along every temporal cutoff path. -/
theorem anisotropicDoeblin_physicalRate_tendsto_zero {a_s g_sq L_box : ℝ}
    (hC : 0 < 24 * a_s * L_box ^ 3 / g_sq) (P : TemporalCutoffPath) :
    Tendsto (fun n => physicalRate (P.spacing n)
      (latticeRate (anisotropicTemporalContinuumQ a_s g_sq L_box (P.spacing n)))) atTop (𝓝 0) := by
  set C := 24 * a_s * L_box ^ 3 / g_sq with hCdef
  have hyTop : Tendsto (fun n => (P.spacing n)⁻¹) atTop atTop :=
    Tendsto.inv_tendsto_nhdsGT_zero (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      P.spacing_tendsto_zero (Eventually.of_forall fun n => P.spacing_pos n))
  have hCy : Tendsto (fun n => C * (P.spacing n)⁻¹) atTop atTop := hyTop.const_mul_atTop hC
  have hx : ∀ n, Real.exp (-C / P.spacing n) = Real.exp (-(C * (P.spacing n)⁻¹)) := by
    intro n
    rw [neg_div, div_eq_mul_inv]
  have hxlim : Tendsto (fun n => Real.exp (-(C * (P.spacing n)⁻¹))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hCy
  have hyx : Tendsto (fun n => (P.spacing n)⁻¹ * Real.exp (-(C * (P.spacing n)⁻¹))) atTop
      (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hCy).const_mul C⁻¹
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, pow_one]
    field_simp
  have hupper : Tendsto (fun n => (P.spacing n)⁻¹ * Real.exp (-(C * (P.spacing n)⁻¹)) *
      (1 - Real.exp (-(C * (P.spacing n)⁻¹)))⁻¹) atTop (𝓝 0) := by
    have h := hyx.mul ((tendsto_const_nhds.sub hxlim).inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0))
    rwa [zero_mul] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper (fun n => ?_)
    (fun n => ?_)
  · have hx1 : Real.exp (-(C * (P.spacing n)⁻¹)) < 1 :=
      Real.exp_lt_one_iff.mpr (by have := mul_pos hC (inv_pos.mpr (P.spacing_pos n)); linarith)
    have hq : 0 ≤ latticeRate (anisotropicTemporalContinuumQ a_s g_sq L_box (P.spacing n)) := by
      unfold anisotropicTemporalContinuumQ
      rw [← hCdef, hx n]
      exact latticeRate_nonneg (by linarith) (by linarith [Real.exp_pos (-(C * (P.spacing n)⁻¹))])
    exact div_nonneg hq (P.spacing_pos n).le
  · have hx1 : Real.exp (-(C * (P.spacing n)⁻¹)) < 1 :=
      Real.exp_lt_one_iff.mpr (by have := mul_pos hC (inv_pos.mpr (P.spacing_pos n)); linarith)
    have hb := neg_log_one_sub_le hx1
    show physicalRate (P.spacing n)
        (latticeRate (anisotropicTemporalContinuumQ a_s g_sq L_box (P.spacing n))) ≤ _
    unfold physicalRate anisotropicTemporalContinuumQ latticeRate
    rw [← hCdef, hx n, div_eq_mul_inv]
    have hinv : 0 ≤ (P.spacing n)⁻¹ := (inv_pos.mpr (P.spacing_pos n)).le
    calc -Real.log (1 - Real.exp (-(C * (P.spacing n)⁻¹))) * (P.spacing n)⁻¹
        ≤ Real.exp (-(C * (P.spacing n)⁻¹)) / (1 - Real.exp (-(C * (P.spacing n)⁻¹))) *
            (P.spacing n)⁻¹ := mul_le_mul_of_nonneg_right hb hinv
      _ = (P.spacing n)⁻¹ * Real.exp (-(C * (P.spacing n)⁻¹)) *
            (1 - Real.exp (-(C * (P.spacing n)⁻¹)))⁻¹ := by ring

/-- Consequently the anisotropic Doeblin factor has no uniform physical floor along any temporal
cutoff path. -/
theorem anisotropicDoeblin_no_uniform_floor {a_s g_sq L_box : ℝ}
    (hC : 0 < 24 * a_s * L_box ^ 3 / g_sq) (P : TemporalCutoffPath) :
    ¬ UniformPhysicalRateFloor P.spacing
      (fun n => latticeRate (anisotropicTemporalContinuumQ a_s g_sq L_box (P.spacing n))) := by
  rintro ⟨m0, hm0, hle⟩
  obtain ⟨n, hn⟩ := ((tendsto_order.1 (anisotropicDoeblin_physicalRate_tendsto_zero hC P)).2 m0
    hm0).exists
  linarith [hle n]

/-- **The finite-volume Doeblin factor degenerates.** For
`q(L, β) = 1 - exp (-6 β L³)` (`wilsonFiniteVolumeContractionQ`), whenever `6 β_n L_n³ → ∞`
(infinite volume at fixed coupling, or weak coupling at fixed volume) the lattice rate
`latticeRate q → 0`. -/
theorem finiteVolumeDoeblin_latticeRate_tendsto_zero (L : ℕ → ℕ) (β : ℕ → ℝ)
    (hgrow : Tendsto (fun n => 6 * β n * (L n : ℝ) ^ 3) atTop atTop) :
    Tendsto (fun n => latticeRate (wilsonFiniteVolumeContractionQ (L n) (β n))) atTop (𝓝 0) := by
  have hexp : Tendsto (fun n => Real.exp (-(6 * β n * (L n : ℝ) ^ 3))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hgrow
  have hq : Tendsto (fun n => wilsonFiniteVolumeContractionQ (L n) (β n)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hexp
    rw [sub_zero] at h
    exact h
  have hlog : Tendsto (fun n => Real.log (wilsonFiniteVolumeContractionQ (L n) (β n))) atTop
      (𝓝 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hq
    rwa [Real.log_one] at h
  have h := hlog.neg
  rw [neg_zero] at h
  exact h

/-- At spacings bounded below by `aMin > 0` (for example one fixed spacing), a degenerating
Doeblin factor has no uniform physical floor. -/
theorem finiteVolumeDoeblin_no_uniform_floor (L : ℕ → ℕ) (β a : ℕ → ℝ) {aMin : ℝ}
    (haMin : 0 < aMin) (ha : ∀ n, aMin ≤ a n)
    (hgrow : Tendsto (fun n => 6 * β n * (L n : ℝ) ^ 3) atTop atTop) :
    ¬ UniformPhysicalRateFloor a
      (fun n => latticeRate (wilsonFiniteVolumeContractionQ (L n) (β n))) := by
  rintro ⟨m0, hm0, hle⟩
  have hlim := finiteVolumeDoeblin_latticeRate_tendsto_zero L β hgrow
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).2 (m0 * aMin) (mul_pos hm0 haMin)).exists
  have h := hle n
  unfold physicalRate at h
  rw [le_div_iff₀ (haMin.trans_le (ha n))] at h
  nlinarith [ha n]

/-- Infinite-volume form at fixed coupling `β > 0`: the Doeblin lattice rate tends to zero as
`L → ∞`, so the Doeblin bound is not volume-uniform. -/
theorem finiteVolumeDoeblin_latticeRate_tendsto_zero_in_volume {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun L : ℕ => latticeRate (wilsonFiniteVolumeContractionQ L β)) atTop (𝓝 0) := by
  have hL3 : Tendsto (fun L : ℕ => (L : ℝ) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  exact finiteVolumeDoeblin_latticeRate_tendsto_zero (fun L => L) (fun _ => β)
    (by simpa [mul_assoc] using hL3.const_mul_atTop (by positivity : (0 : ℝ) < 6 * β))


/-- The repository's `LatticeApproximantSequence` quantifies positivity cutoff by cutoff
(`latticeGap_pos : ∀ L, 0 < latticeGap L`): its fields admit gaps tending to zero, so they do not
contain the uniform floor. Only the convergence clause of the conjecture supplies it
(`massGapConjecture_contains_uniform_physical_floor`). -/
theorem latticeApproximantSequence_fields_do_not_give_uniform_floor :
    ∃ seq : LatticeApproximantSequence, ¬ ∃ m0 : ℝ, 0 < m0 ∧ ∀ L, m0 ≤ seq.latticeGap L := by
  let seq : LatticeApproximantSequence :=
    { a := fun L => 1 / ((L : ℝ) + 1)
      a_pos := fun L => by positivity
      a_tends_to_zero := tendsto_one_div_add_atTop_nhds_zero_nat
      beta := fun L => (L : ℝ)
      beta_asymptotic_freedom := tendsto_natCast_atTop_atTop
      latticeGap := fun L => 1 / ((L : ℝ) + 1)
      latticeGap_pos := fun L => by positivity
      observableCorrelator := fun _ => 1
      observableCorrelator_pos := fun _ => one_pos
      timeCorrelator := fun L t => Real.exp (-(1 / ((L : ℝ) + 1)) * t)
      timeCorrelator_zero_eq := fun L => by simp
      timeCorrelator_pos := fun L t _ => Real.exp_pos _
      timeCorrelator_cluster_bound := fun L t _ => by simp }
  refine ⟨seq, ?_⟩
  rintro ⟨m0, hm0, hle⟩
  obtain ⟨L, hL⟩ := ((tendsto_order.1 (tendsto_one_div_add_atTop_nhds_zero_nat)).2 m0 hm0).exists
  linarith [hle L]

/-! ## 8b. What a contraction over several steps gives: root extraction

For a Hermitian transfer operator, `k ↦ ‖T^k u‖` is log-convex, so a contraction over `k` steps
(physical time `k a`) yields a per-step contraction at the same physical rate. This is the only
route by which a blocked-scale constant such as `7 / 8` becomes a uniform floor, and it needs the
contraction for the fine evolution on the whole fine vacuum complement. -/

namespace LatticeTransferStep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : LatticeTransferStep H)

/-- Log-convexity: `‖T^(j+1) u‖² ≤ ‖T^j u‖ ‖T^(j+2) u‖` for a Hermitian transfer operator. -/
theorem norm_pow_succ_sq_le (u : H) (j : ℕ) :
    ‖(S.transfer ^ (j + 1)) u‖ ^ 2 ≤ ‖(S.transfer ^ j) u‖ * ‖(S.transfer ^ (j + 2)) u‖ := by
  have h1 : (S.transfer ^ (j + 1)) u = S.transfer ((S.transfer ^ j) u) := by
    rw [pow_succ', mul_apply_eq_comp]
  have h2 : (S.transfer ^ (j + 2)) u = S.transfer (S.transfer ((S.transfer ^ j) u)) := by
    rw [pow_succ', mul_apply_eq_comp, h1]
  rw [h1, h2, norm_sq_eq_re_inner (𝕜 := ℂ), S.transfer_symmetric]
  exact re_inner_le_norm _ _

/-- Ratio monotonicity: `‖T u‖ ‖T^j u‖ ≤ ‖u‖ ‖T^(j+1) u‖`. -/
theorem norm_transfer_mul_norm_pow_le (u : H) (j : ℕ) :
    ‖S.transfer u‖ * ‖(S.transfer ^ j) u‖ ≤ ‖u‖ * ‖(S.transfer ^ (j + 1)) u‖ := by
  induction j with
  | zero => simp [mul_comm]
  | succ k ih =>
    have hlc := S.norm_pow_succ_sq_le u k
    have h0 := norm_nonneg (S.transfer u)
    have hk := norm_nonneg ((S.transfer ^ k) u)
    have hk2 := norm_nonneg ((S.transfer ^ (k + 2)) u)
    have hu := norm_nonneg u
    rcases (norm_nonneg ((S.transfer ^ (k + 1)) u)).eq_or_lt with hz | hpos
    · rw [← hz, mul_zero]
      exact mul_nonneg hu hk2
    · have hA : ‖S.transfer u‖ * ‖(S.transfer ^ (k + 1)) u‖ ^ 2 ≤
          ‖S.transfer u‖ * (‖(S.transfer ^ k) u‖ * ‖(S.transfer ^ (k + 2)) u‖) :=
        mul_le_mul_of_nonneg_left hlc h0
      have hB : ‖S.transfer u‖ * ‖(S.transfer ^ k) u‖ * ‖(S.transfer ^ (k + 2)) u‖ ≤
          ‖u‖ * ‖(S.transfer ^ (k + 1)) u‖ * ‖(S.transfer ^ (k + 2)) u‖ :=
        mul_le_mul_of_nonneg_right ih hk2
      have hC : (‖S.transfer u‖ * ‖(S.transfer ^ (k + 1)) u‖) * ‖(S.transfer ^ (k + 1)) u‖ ≤
          (‖u‖ * ‖(S.transfer ^ (k + 1 + 1)) u‖) * ‖(S.transfer ^ (k + 1)) u‖ := by
        nlinarith
      exact le_of_mul_le_mul_right hC hpos

/-- `‖T u‖^(k+1) ≤ ‖u‖^k ‖T^(k+1) u‖` for a Hermitian transfer operator. -/
theorem norm_transfer_pow_le (u : H) (k : ℕ) :
    ‖S.transfer u‖ ^ (k + 1) ≤ ‖u‖ ^ k * ‖(S.transfer ^ (k + 1)) u‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hr := S.norm_transfer_mul_norm_pow_le u (k + 1)
    have h0 := norm_nonneg (S.transfer u)
    calc ‖S.transfer u‖ ^ (k + 1 + 1) = ‖S.transfer u‖ * ‖S.transfer u‖ ^ (k + 1) := by ring
      _ ≤ ‖S.transfer u‖ * (‖u‖ ^ k * ‖(S.transfer ^ (k + 1)) u‖) :=
          mul_le_mul_of_nonneg_left ih h0
      _ = ‖u‖ ^ k * (‖S.transfer u‖ * ‖(S.transfer ^ (k + 1)) u‖) := by ring
      _ ≤ ‖u‖ ^ k * (‖u‖ * ‖(S.transfer ^ (k + 1 + 1)) u‖) :=
          mul_le_mul_of_nonneg_left hr (pow_nonneg (norm_nonneg u) k)
      _ = ‖u‖ ^ (k + 1) * ‖(S.transfer ^ (k + 1 + 1)) u‖ := by ring

/-- **Root extraction.** If `k + 1` steps (physical time `ℓ = (k + 1) a`) contract the vacuum
complement by `q > 0`, then one step contracts it by `exp (-(m a))` with
`m = latticeRate q / ℓ`: the physical rate over the long step is inherited by every step. -/
theorem stepContraction_of_pow_contraction {q : ℝ} (hq : 0 < q) (k : ℕ)
    (h : ∀ u : H, ⟪S.vacuum, u⟫_ℂ = 0 → ‖(S.transfer ^ (k + 1)) u‖ ≤ q * ‖u‖) :
    S.StepContraction (Real.exp (-(physicalRate (((k + 1 : ℕ) : ℝ) * S.spacing)
      (latticeRate q) * S.spacing))) := by
  intro u hu
  set r := Real.exp (-(physicalRate (((k + 1 : ℕ) : ℝ) * S.spacing) (latticeRate q) * S.spacing))
    with hr
  have hrpos : 0 < r := Real.exp_pos _
  have hℓ : (((k + 1 : ℕ) : ℝ) * S.spacing) ≠ 0 := by
    have := S.spacing_pos
    positivity
  have hq_eq : q = r ^ (k + 1) := by
    rw [hr, ← Real.exp_nat_mul]
    have hcalc : ((k + 1 : ℕ) : ℝ) * -(physicalRate (((k + 1 : ℕ) : ℝ) * S.spacing)
        (latticeRate q) * S.spacing) = -latticeRate q := by
      have ha : S.spacing ≠ 0 := S.spacing_pos.ne'
      unfold physicalRate
      field_simp
    rw [hcalc, exp_neg_latticeRate hq]
  have hpow := S.norm_transfer_pow_le u k
  have hbound : ‖S.transfer u‖ ^ (k + 1) ≤ (r * ‖u‖) ^ (k + 1) := by
    calc ‖S.transfer u‖ ^ (k + 1) ≤ ‖u‖ ^ k * ‖(S.transfer ^ (k + 1)) u‖ := hpow
      _ ≤ ‖u‖ ^ k * (q * ‖u‖) := mul_le_mul_of_nonneg_left (h u hu) (pow_nonneg (norm_nonneg u) k)
      _ = (r * ‖u‖) ^ (k + 1) := by rw [hq_eq]; ring
  exact le_of_pow_le_pow_left₀ (Nat.succ_ne_zero k) (mul_nonneg hrpos.le (norm_nonneg u)) hbound

/-- A larger factor is a weaker contraction. -/
theorem StepContraction.mono {ρ ρ' : ℝ} (h : S.StepContraction ρ) (hle : ρ ≤ ρ') :
    S.StepContraction ρ' := fun u hu =>
  (h u hu).trans (mul_le_mul_of_nonneg_right hle (norm_nonneg u))

end LatticeTransferStep

/-- **What the blocked constant `7 / 8` would give.** Suppose that at every cutoff the fine
transfer operator, run for `k_n + 1` fine steps (physical time `ℓ_n = (k_n + 1) a_n`), contracts
the entire fine vacuum complement by `7 / 8`, and that `ℓ_n ≤ ℓmax`. Then every fine step contracts
by `exp (-(log (8 / 7) / ℓmax) a_n)`, i.e. the uniform floor holds with `m0 = log (8 / 7) / ℓmax`.
The scale is `ℓmax`; the hypotheses (a contraction of the fine evolution on the whole complement,
Hermitian symmetry, the bound on `ℓ_n`) are exactly what the repository's landing arithmetic
`18 / 24 + 1 / 8 = 7 / 8` does not supply. -/
theorem blocked_seven_eighths_gives_uniform_floor {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (S : ℕ → LatticeTransferStep H) (k : ℕ → ℕ) {ℓmax : ℝ}
    (hℓ : ∀ n, ((k n + 1 : ℕ) : ℝ) * (S n).spacing ≤ ℓmax)
    (h : ∀ n, ∀ u : H, ⟪(S n).vacuum, u⟫_ℂ = 0 →
      ‖((S n).transfer ^ (k n + 1)) u‖ ≤ (7 / 8) * ‖u‖) :
    (∀ n, (S n).StepContraction (Real.exp (-((Real.log (8 / 7) / ℓmax) * (S n).spacing)))) ∧
      UniformPhysicalRateFloor (fun n => (S n).spacing)
        (fun n => latticeRate (Real.exp (-((Real.log (8 / 7) / ℓmax) * (S n).spacing)))) := by
  have hℓpos : ∀ n, 0 < ((k n + 1 : ℕ) : ℝ) * (S n).spacing := fun n =>
    mul_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) (S n).spacing_pos
  have hmax : 0 < ℓmax := (hℓpos 0).trans_le (hℓ 0)
  have hm0 : 0 < Real.log (8 / 7) / ℓmax := div_pos log_eight_sevenths_pos hmax
  refine ⟨fun n => ?_, ⟨Real.log (8 / 7) / ℓmax, hm0, fun n => ?_⟩⟩
  · have hroot := (S n).stepContraction_of_pow_contraction (by norm_num) (k n) (h n)
    refine hroot.mono _ (Real.exp_le_exp.mpr ?_)
    rw [latticeRate_seven_eighths]
    have hle : Real.log (8 / 7) / ℓmax ≤
        physicalRate (((k n + 1 : ℕ) : ℝ) * (S n).spacing) (Real.log (8 / 7)) :=
      div_le_div_of_nonneg_left log_eight_sevenths_pos.le (hℓpos n) (hℓ n)
    nlinarith [(S n).spacing_pos]
  · rw [le_physicalRate_iff_stepFactor_le (S n).spacing_pos (Real.exp_pos _)]

/-! ## 9. The named obligations of the physical-time route -/

/-- The hypotheses a cutoff family of transfer operators has to satisfy for the physical-time
route of this module, each a named field. For Yang–Mills every field is an open obligation for
the Osterwalder–Schrader transfer operators of the `SU(2)` Wilson measure along a temporal
cutoff path: the repository constructs none of these operators, no common Hilbert space for
different cutoffs, and no continuum limit. The fields are inputs, not consequences of
`wilsonMeasure`, `gaugeHaarMeasure` or the lattice geometry. -/
structure PhysicalTimeDecayObligations (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- (O1) Temporal cutoff path `a_n → 0`. -/
  path : TemporalCutoffPath
  /-- (O2) One transfer step per cutoff, all on one common Hilbert space `H` (the common-space
  identification is itself an obligation), with Hermitian symmetry and a fixed normalized vacuum. -/
  step : ℕ → LatticeTransferStep H
  step_spacing : ∀ n, (step n).spacing = path.spacing n
  /-- (O3) A per-step contraction factor on the vacuum complement at every cutoff. -/
  stepFactor : ℕ → ℝ
  stepFactor_pos : ∀ n, 0 < stepFactor n
  step_contraction : ∀ n, (step n).StepContraction (stepFactor n)
  /-- (O4) The uniform physical floor: one `floor > 0`, fixed before the cutoff index, with
  `floor ≤ latticeRate (stepFactor n) / a_n` for every `n`. -/
  floor : ℝ
  floor_pos : 0 < floor
  floor_le : ∀ n, floor ≤ physicalRate (path.spacing n) (latticeRate (stepFactor n))
  /-- (O5) Convergence of the normalized vacua. -/
  limitVacuum : H
  vacuum_tendsto : Tendsto (fun n => (step n).vacuum) atTop (𝓝 limitVacuum)
  /-- (O6) Strong convergence of the lattice evolutions `T_n ^ ⌊t / a_n⌋₊` on a dense core at
  every real `t ≥ 0`, to a family `limitEvolution` (the continuum-limit identification). -/
  core : Set H
  core_dense : Dense core
  limitEvolution : ℝ → H →L[ℂ] H
  evolution_tendsto : ∀ t, 0 ≤ t → ∀ u ∈ core,
    Tendsto (fun n => (step n).evolution t u) atTop (𝓝 (limitEvolution t u))
  /-- (O7) Nontriviality with one energy ceiling: a core vector whose excited part decays no
  faster than `exp (-energyCeiling * t)` at every lattice time of every cutoff, and whose limiting
  excited part is nonzero. -/
  energyCeiling : ℝ
  energyCeiling_nonneg : 0 ≤ energyCeiling
  excitation : H
  excitation_mem_core : excitation ∈ core
  excitation_lower : ∀ n (k : ℕ),
    Real.exp (-energyCeiling * ((k : ℝ) * path.spacing n)) *
        ‖excitedPart (step n).vacuum excitation‖ ≤
      ‖((step n).transfer ^ k) (excitedPart (step n).vacuum excitation)‖
  excitation_limit_ne_zero : excitedPart limitVacuum excitation ≠ 0

namespace PhysicalTimeDecayObligations

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (O : PhysicalTimeDecayObligations H)

theorem floor_le_step (n : ℕ) :
    O.floor ≤ physicalRate (O.step n).spacing (latticeRate (O.stepFactor n)) := by
  rw [O.step_spacing n]
  exact O.floor_le n

/-- Consequence 1: decay uniform in the cutoff on every time lattice. -/
theorem uniform_lattice_decay :
    ∀ n, ∀ t ∈ timeLattice (O.step n).spacing, ∀ u : H,
      ‖(O.step n).evolution t u - vacuumPart (O.step n).vacuum u‖ ≤
        Real.exp (-O.floor * t) * ‖excitedPart (O.step n).vacuum u‖ :=
  uniform_decay_on_timeLattices_of_floor O.stepFactor_pos O.step_contraction O.floor_le_step

/-- Consequence 2: the limit fixes the vacuum and decays at the floor rate at every real time. -/
theorem limit_decay :
    ∀ t, 0 ≤ t → O.limitEvolution t O.limitVacuum = O.limitVacuum ∧
      ∀ u : H, ⟪O.limitVacuum, u⟫_ℂ = 0 →
        ‖O.limitEvolution t u‖ ≤ Real.exp (-O.floor * t) * ‖u‖ :=
  uniform_floor_decay_survives_strong_limit O.core O.core_dense O.path O.step O.step_spacing
    O.stepFactor O.stepFactor_pos O.step_contraction O.floor_pos.le O.floor_le O.limitEvolution
    O.limitVacuum O.vacuum_tendsto O.evolution_tendsto

/-- Consequence 3: a surviving excitation whose decay rate lies in `[floor, energyCeiling]`. -/
theorem limit_excitation_two_sided :
    ∀ t, 0 ≤ t →
      Real.exp (-O.energyCeiling * t) * ‖excitedPart O.limitVacuum O.excitation‖ ≤
          ‖O.limitEvolution t O.excitation - vacuumPart O.limitVacuum O.excitation‖ ∧
        ‖O.limitEvolution t O.excitation - vacuumPart O.limitVacuum O.excitation‖ ≤
          Real.exp (-O.floor * t) * ‖excitedPart O.limitVacuum O.excitation‖ := by
  intro t ht
  have hnorm : ‖O.limitVacuum‖ = 1 :=
    normalized_vacuum_limit O.vacuum_tendsto (fun n => (O.step n).vacuum_norm)
  refine ⟨excitation_lower_bound_survives_strong_limit O.path O.step O.step_spacing
    O.limitEvolution O.limitVacuum O.vacuum_tendsto O.energyCeiling_nonneg O.excitation
    (fun t ht => O.evolution_tendsto t ht _ O.excitation_mem_core) O.excitation_lower t ht, ?_⟩
  have hdec := O.limit_decay t ht
  rw [← map_excitedPart (O.limitEvolution t) hdec.1 O.excitation]
  exact hdec.2 _ (excitedPart_orthogonal hnorm O.excitation)

/-- Consequence 4: the limit evolution never collapses onto the vacuum part of the excitation. -/
theorem limit_nontrivial :
    ∀ t, 0 ≤ t → O.limitEvolution t O.excitation ≠ vacuumPart O.limitVacuum O.excitation :=
  excitation_survives_strong_limit O.path O.step O.step_spacing O.limitEvolution O.limitVacuum
    O.vacuum_tendsto O.energyCeiling_nonneg O.excitation
    (fun t ht => O.evolution_tendsto t ht _ O.excitation_mem_core) O.excitation_lower
    O.excitation_limit_ne_zero

/-- The excited parts at cutoff `n` are eventually nonzero. -/
theorem eventually_excitedPart_ne_zero :
    ∀ᶠ n in atTop, excitedPart (O.step n).vacuum O.excitation ≠ 0 := by
  have h : Tendsto (fun n => excitedPart (O.step n).vacuum O.excitation) atTop
      (𝓝 (excitedPart O.limitVacuum O.excitation)) :=
    (tendsto_const_nhds (x := O.excitation)).sub (vacuumPart_tendsto O.vacuum_tendsto _)
  exact h.eventually_ne O.excitation_limit_ne_zero

/-- Eventually the per-step factor is squeezed: `exp (-M a_n) ≤ ρ_n ≤ exp (-floor a_n)`. -/
theorem eventually_stepFactor_bracket :
    ∀ᶠ n in atTop, Real.exp (-(O.energyCeiling * O.path.spacing n)) ≤ O.stepFactor n ∧
      O.stepFactor n ≤ Real.exp (-(O.floor * O.path.spacing n)) := by
  filter_upwards [O.eventually_excitedPart_ne_zero] with n hn
  have ha := O.path.spacing_pos n
  have hupper : O.stepFactor n ≤ Real.exp (-(O.floor * O.path.spacing n)) :=
    (le_physicalRate_iff_stepFactor_le ha (O.stepFactor_pos n)).mp (O.floor_le n)
  refine ⟨?_, hupper⟩
  have hnorm := norm_pos_iff.mpr hn
  have hlow := O.excitation_lower n 1
  rw [pow_one, Nat.cast_one, one_mul, neg_mul] at hlow
  have hcon := O.step_contraction n _ (excitedPart_orthogonal (O.step n).vacuum_norm O.excitation)
  exact le_of_mul_le_mul_right (hlow.trans hcon) hnorm

/-- Consequence 5: the floor never exceeds the energy ceiling. -/
theorem floor_le_energyCeiling : O.floor ≤ O.energyCeiling := by
  obtain ⟨n, hlow, hup⟩ := O.eventually_stepFactor_bracket.exists
  have h := (Real.exp_le_exp.mp (hlow.trans hup))
  have ha := O.path.spacing_pos n
  nlinarith

/-- Consequence 6: the per-step factors tend to `1`. In particular no fixed per-step constant
`ρ0 < 1` (such as `7 / 8`) can bound the transfer steps along the path. -/
theorem stepFactor_tendsto_one : Tendsto O.stepFactor atTop (𝓝 1) := by
  have hexp : ∀ c : ℝ, Tendsto (fun n => Real.exp (-(c * O.path.spacing n))) atTop (𝓝 1) := by
    intro c
    have h1 := ((O.path.spacing_tendsto_zero.const_mul c).neg).rexp
    rwa [mul_zero, neg_zero, Real.exp_zero] at h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (hexp O.energyCeiling) (hexp O.floor)
    (O.eventually_stepFactor_bracket.mono fun _ h => h.1)
    (O.eventually_stepFactor_bracket.mono fun _ h => h.2)

/-- Consequence 7: eventual two-sided physical control `floor ≤ m_phys(a_n) ≤ energyCeiling`. -/
theorem eventually_physicalRate_mem :
    ∀ᶠ n in atTop,
      O.floor ≤ physicalRate (O.path.spacing n) (latticeRate (O.stepFactor n)) ∧
        physicalRate (O.path.spacing n) (latticeRate (O.stepFactor n)) ≤ O.energyCeiling := by
  filter_upwards [O.eventually_stepFactor_bracket] with n hn
  exact ⟨O.floor_le n, (physicalRate_le_iff_le_stepFactor (O.path.spacing_pos n)
    (O.stepFactor_pos n)).mpr hn.1⟩

/-- Consequence 8: generator coercivity at the floor, given the generator derivative. -/
theorem generator_coercivity (domain : Submodule ℂ H) (generator : domain →ₗ[ℂ] H)
    (hzero : ∀ u : domain, O.limitEvolution 0 u = u)
    (hgenerator : ∀ u : domain,
      HasDerivWithinAt (fun t : ℝ => O.limitEvolution t u) (-(generator u)) (Set.Ioi 0) 0) :
    ∀ u : domain, ⟪O.limitVacuum, (u : H)⟫_ℂ = 0 →
      O.floor * ‖(u : H)‖ ^ 2 ≤ (⟪(u : H), generator u⟫_ℂ).re :=
  (uniform_floor_generator_coercivity O.core O.core_dense O.path O.step O.step_spacing
    O.stepFactor O.stepFactor_pos O.step_contraction O.floor_pos.le O.floor_le O.limitEvolution
    O.limitVacuum O.vacuum_tendsto O.evolution_tendsto domain generator hzero hgenerator).2

end PhysicalTimeDecayObligations

/-! ## 10. Consistency of the obligations: a two-level model

The obligations are not contradictory: a two-level transfer operator with factor
`exp (-m a_n)` on the excited line satisfies all of them. This model is not Yang–Mills. -/

section TwoLevelModel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Two-level transfer operator: identity on the vacuum line, factor `ρ` on its complement. -/
def rankOneTransfer (Ω : H) (ρ : ℝ) : H →L[ℂ] H :=
  InnerProductSpace.rankOne ℂ Ω Ω +
    (ρ : ℂ) • (ContinuousLinearMap.id ℂ H - InnerProductSpace.rankOne ℂ Ω Ω)

theorem rankOneTransfer_apply (Ω u : H) (ρ : ℝ) :
    rankOneTransfer Ω ρ u = vacuumPart Ω u + (ρ : ℂ) • excitedPart Ω u := rfl

theorem vacuumPart_add (Ω u v : H) :
    vacuumPart Ω (u + v) = vacuumPart Ω u + vacuumPart Ω v := by
  simp [vacuumPart, add_smul]

theorem vacuumPart_smul (Ω u : H) (c : ℂ) : vacuumPart Ω (c • u) = c • vacuumPart Ω u := by
  simp [vacuumPart, mul_smul]

theorem vacuumPart_vacuumPart {Ω : H} (hΩ : ‖Ω‖ = 1) (u : H) :
    vacuumPart Ω (vacuumPart Ω u) = vacuumPart Ω u := by
  rw [show vacuumPart Ω u = ⟪Ω, u⟫_ℂ • Ω from rfl, vacuumPart_smul, vacuumPart_self hΩ]

theorem vacuumPart_excitedPart {Ω : H} (hΩ : ‖Ω‖ = 1) (u : H) :
    vacuumPart Ω (excitedPart Ω u) = 0 := by
  rw [vacuumPart, excitedPart_orthogonal hΩ u, zero_smul]

theorem rankOneTransfer_apply_of_orthogonal {Ω : H} (ρ : ℝ) {u : H} (hu : ⟪Ω, u⟫_ℂ = 0) :
    rankOneTransfer Ω ρ u = (ρ : ℂ) • u := by
  simp [rankOneTransfer_apply, vacuumPart, excitedPart, hu]

theorem rankOneTransfer_symmetric (Ω : H) (ρ : ℝ) (u v : H) :
    ⟪rankOneTransfer Ω ρ u, v⟫_ℂ = ⟪u, rankOneTransfer Ω ρ v⟫_ℂ := by
  simp only [rankOneTransfer_apply, vacuumPart, excitedPart, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    inner_conj_symm]
  ring

theorem rankOneTransfer_pow_apply {Ω : H} (hΩ : ‖Ω‖ = 1) (ρ : ℝ) (n : ℕ) (u : H) :
    (rankOneTransfer Ω ρ ^ n) u = vacuumPart Ω u + ((ρ ^ n : ℝ) : ℂ) • excitedPart Ω u := by
  induction n with
  | zero => simp [excitedPart]
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, rankOneTransfer_apply]
    have hdef : ∀ x : H, excitedPart Ω x = x - vacuumPart Ω x := fun x => rfl
    have h1 : vacuumPart Ω (vacuumPart Ω u + ((ρ ^ k : ℝ) : ℂ) • excitedPart Ω u) =
        vacuumPart Ω u := by
      rw [vacuumPart_add, vacuumPart_smul, vacuumPart_vacuumPart hΩ, vacuumPart_excitedPart hΩ,
        smul_zero, add_zero]
    have h2 : excitedPart Ω (vacuumPart Ω u + ((ρ ^ k : ℝ) : ℂ) • excitedPart Ω u) =
        ((ρ ^ k : ℝ) : ℂ) • excitedPart Ω u := by
      rw [hdef (vacuumPart Ω u + _), h1]
      abel
    rw [h1, h2, smul_smul]
    congr 2
    push_cast
    ring

/-- The two-level model as one temporal lattice regularization. -/
def rankOneStep {Ω : H} (hΩ : ‖Ω‖ = 1) (a : ℝ) (ha : 0 < a) (ρ : ℝ) : LatticeTransferStep H where
  spacing := a
  spacing_pos := ha
  transfer := rankOneTransfer Ω ρ
  vacuum := Ω
  vacuum_norm := hΩ
  transfer_vacuum := by simp [rankOneTransfer_apply, excitedPart, vacuumPart_self hΩ]
  transfer_symmetric := rankOneTransfer_symmetric Ω ρ

theorem rankOneStep_contraction {Ω : H} (hΩ : ‖Ω‖ = 1) (a : ℝ) (ha : 0 < a) {ρ : ℝ}
    (hρ : 0 ≤ ρ) : (rankOneStep hΩ a ha ρ).StepContraction ρ := by
  intro u hu
  have hu' : ⟪Ω, u⟫_ℂ = 0 := hu
  change ‖rankOneTransfer Ω ρ u‖ ≤ ρ * ‖u‖
  rw [rankOneTransfer_apply_of_orthogonal ρ hu', norm_smul, Complex.norm_real,
    Real.norm_of_nonneg hρ]

theorem rankOneStep_evolution_apply {Ω : H} (hΩ : ‖Ω‖ = 1) (a : ℝ) (ha : 0 < a) (ρ t : ℝ)
    (u : H) : (rankOneStep hΩ a ha ρ).evolution t u =
      vacuumPart Ω u + ((ρ ^ elapsedSteps a t : ℝ) : ℂ) • excitedPart Ω u :=
  rankOneTransfer_pow_apply hΩ ρ _ u

/-- `⌊t / a_n⌋₊ a_n → t` along a cutoff path. -/
theorem elapsedSteps_mul_tendsto (P : TemporalCutoffPath) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => (elapsedSteps (P.spacing n) t : ℝ) * P.spacing n) atTop (𝓝 t) := by
  have hlow : Tendsto (fun n => t - P.spacing n) atTop (𝓝 t) := by
    have h := (tendsto_const_nhds (x := t)).sub P.spacing_tendsto_zero
    rwa [sub_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => (sub_lt_elapsedSteps_mul (P.spacing_pos n)).le)
    (fun n => elapsedSteps_mul_le (P.spacing_pos n) ht)

/-- With factor `exp (-m a_n)` the lattice evolutions converge strongly, at every `t ≥ 0`, to the
continuous two-level semigroup with excited factor `exp (-m t)`. -/
theorem rankOneStep_evolution_tendsto (P : TemporalCutoffPath) {Ω : H} (hΩ : ‖Ω‖ = 1) (m : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (u : H) :
    Tendsto (fun n => (rankOneStep hΩ (P.spacing n) (P.spacing_pos n)
        (Real.exp (-(m * P.spacing n)))).evolution t u) atTop
      (𝓝 (rankOneTransfer Ω (Real.exp (-m * t)) u)) := by
  have hpow : ∀ n, Real.exp (-(m * P.spacing n)) ^ elapsedSteps (P.spacing n) t =
      Real.exp (-m * ((elapsedSteps (P.spacing n) t : ℝ) * P.spacing n)) := by
    intro n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hscalar : Tendsto (fun n => Real.exp (-(m * P.spacing n)) ^ elapsedSteps (P.spacing n) t)
      atTop (𝓝 (Real.exp (-m * t))) := by
    simp only [hpow]
    exact ((elapsedSteps_mul_tendsto P ht).const_mul (-m)).rexp
  have hc : Tendsto (fun n => ((Real.exp (-(m * P.spacing n)) ^ elapsedSteps (P.spacing n) t : ℝ)
      : ℂ)) atTop (𝓝 ((Real.exp (-m * t) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hscalar
  simp only [rankOneStep_evolution_apply, rankOneTransfer_apply]
  exact tendsto_const_nhds.add (hc.smul_const (excitedPart Ω u))

theorem rankOneStep_excitation_lower {Ω e : H} (hΩ : ‖Ω‖ = 1) (horth : ⟪Ω, e⟫_ℂ = 0) (m a : ℝ)
    (ha : 0 < a) (k : ℕ) :
    Real.exp (-m * ((k : ℝ) * a)) * ‖excitedPart Ω e‖ ≤
      ‖((rankOneStep hΩ a ha (Real.exp (-(m * a)))).transfer ^ k) (excitedPart Ω e)‖ := by
  have hexc : excitedPart Ω e = e := by simp [excitedPart, vacuumPart, horth]
  change _ ≤ ‖(rankOneTransfer Ω (Real.exp (-(m * a))) ^ k) (excitedPart Ω e)‖
  rw [hexc, rankOneTransfer_pow_apply hΩ, hexc, vacuumPart, horth, zero_smul, zero_add, norm_smul,
    Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (Real.exp_pos _).le k),
    ← Real.exp_nat_mul]
  apply le_of_eq
  congr 2
  ring

/-- A two-level instance of `PhysicalTimeDecayObligations` on any `H` with a unit vacuum `Ω` and a
unit vector `e ⊥ Ω`; floor and energy ceiling both equal `m`. -/
def rankOneObligations {Ω e : H} (hΩ : ‖Ω‖ = 1) (he : ‖e‖ = 1) (horth : ⟪Ω, e⟫_ℂ = 0) {m : ℝ}
    (hm : 0 < m) (P : TemporalCutoffPath) : PhysicalTimeDecayObligations H where
  path := P
  step n := rankOneStep hΩ (P.spacing n) (P.spacing_pos n) (Real.exp (-(m * P.spacing n)))
  step_spacing _ := rfl
  stepFactor n := Real.exp (-(m * P.spacing n))
  stepFactor_pos _ := Real.exp_pos _
  step_contraction n := rankOneStep_contraction hΩ _ _ (Real.exp_pos _).le
  floor := m
  floor_pos := hm
  floor_le n := (le_physicalRate_iff_stepFactor_le (P.spacing_pos n) (Real.exp_pos _)).mpr le_rfl
  limitVacuum := Ω
  vacuum_tendsto := tendsto_const_nhds
  core := Set.univ
  core_dense := dense_univ
  limitEvolution t := rankOneTransfer Ω (Real.exp (-m * t))
  evolution_tendsto t ht u _ := rankOneStep_evolution_tendsto P hΩ m ht u
  energyCeiling := m
  energyCeiling_nonneg := hm.le
  excitation := e
  excitation_mem_core := Set.mem_univ e
  excitation_lower n k := rankOneStep_excitation_lower hΩ horth m (P.spacing n) (P.spacing_pos n) k
  excitation_limit_ne_zero := by
    have hexc : excitedPart Ω e = e := by simp [excitedPart, vacuumPart, horth]
    rw [hexc]
    intro h0
    rw [h0, norm_zero] at he
    exact zero_ne_one he

/-- The cutoff path `a_n = 1 / (n + 1)`. -/
def harmonicCutoffPath : TemporalCutoffPath where
  spacing n := 1 / ((n : ℝ) + 1)
  spacing_pos n := by positivity
  spacing_tendsto_zero := tendsto_one_div_add_atTop_nhds_zero_nat

/-- The obligations are jointly satisfiable (on `ℂ²`); this rules out a vacuous hypothesis set,
and says nothing about Yang–Mills. -/
theorem physicalTimeDecayObligations_consistent :
    Nonempty (PhysicalTimeDecayObligations (EuclideanSpace ℂ (Fin 2))) := by
  have hΩ : ‖(EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 2))‖ = 1 := by simp
  have he : ‖(EuclideanSpace.single 1 1 : EuclideanSpace ℂ (Fin 2))‖ = 1 := by simp
  have horth : ⟪(EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 2)),
      EuclideanSpace.single 1 1⟫_ℂ = 0 := by
    simp [EuclideanSpace.inner_single_left]
  exact ⟨rankOneObligations hΩ he horth one_pos harmonicCutoffPath⟩

end TwoLevelModel

end JesseMath.Physics.YangMillsPhysicalTimeDecay

#assert_zfc_axioms
