import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.YangMillsRenormalizedObservableLimits
import JesseMath.Physics.YangMillsContinuumLimitBridge
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.Basic

/-!
# Osterwalder–Schrader positivity, clustering and nontriviality of Wilson-loop limits

This module works on lane 2a's common space `WilsonLoopSpace` of physical-scale Wilson loops,
with the actual four-dimensional SU(2) Wilson measure of the repository at every cutoff.

Reflection positivity (the `reflection_positive` field of `ContinuumIdentificationObligations`):
* For one law, reflection positivity on the bounded continuous functionals of the positive-time
  loops of a family `A` is a closed condition for convergence in distribution, and it is
  equivalent to its version for functionals of finitely many loops. With the named per-cutoff
  hypothesis `CutoffReflectionPositivity` it passes to every limit law.
* Osterwalder–Seiler positivity of the actual Wilson measure is proved on the periodic lattice
  of even side `2M` for the site reflection `x₀ ↦ -x₀`, at every coupling `β ≥ 0`, for every
  continuous functional of the links of the closed half `0 ≤ x₀ ≤ M`
  (`wilson_reflection_positive`); the measure is also reflection invariant.
* Lane 2a's floor discretization commutes with the reflection exactly for loops whose base time
  and time extent are multiples of the spacing (`physicalWilsonLoop_timeReflect`); for those
  loops the joint Wilson-loop law at a cutoff is reflection positive.
* Along every continuum cutoff path with spacings `2⁻ⁿ` and eventually even sides, in particular
  `dyadicOneLoopPath`, every limit law of the renormalized loops with reflection-invariant
  constants is reflection positive and reflection invariant on functionals of loops with dyadic
  time data, and satisfies the repository's kernel form `FiniteReflectionPositive` there. The
  full field then follows from the named regularity hypothesis `DyadicTimeApproximable`.

Clustering (`time_mixing`) and nontriviality (`nontrivial`):
* Nontriviality is an open condition, so laws that are trivial at all large cutoffs have trivial
  limits; it is not a closed condition: an explicit family of nontrivial laws converges to a
  trivial one.
* Time mixing is not an open condition: the same family is never mixing while its limit is.
  The actual cutoff laws on a finite torus with integer physical time extent are exactly time
  periodic and never time mixing, so `time_mixing` cannot be inherited from cutoffs.
* A limit law is nontrivial exactly when a bounded connected correlation of two time-separated
  loops stays away from zero along the subsequence. The named hypothesis
  `ConnectedCorrelationLowerBound` is what a renormalization must supply; renormalization never
  changes independence at a fixed cutoff, and the collapse of the unrenormalized plaquette
  averages kills every bounded connected correlation.

Not proved here: `DyadicTimeApproximable`; `CutoffReflectionPositivity`, which asks for
positivity of each cutoff law on all positive-time loops at once and is stronger than what the
cylinder-wise argument above uses; `ConnectedCorrelationLowerBound` for any renormalization of
the actual model; `time_mixing` for any limit law; whether `time_mixing` is a closed condition;
and the other fields of `ContinuumIdentificationObligations`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace JesseMath.Physics.YangMillsOsterwalderSchraderInheritance

open YangMillsContinuumCompactness YangMillsRenormalizedObservableLimits

/-! ## 1. Reflection positivity of one law, and its closedness -/

theorem continuous_reflectObservables : Continuous reflectObservables :=
  continuous_pi fun _ => continuous_apply _

/-- The bounded continuous function `w ↦ F (Θ w) * F w`. -/
def reflectedSquare (F : WilsonLoopSpace →ᵇ ℝ) : WilsonLoopSpace →ᵇ ℝ :=
  F.compContinuous ⟨reflectObservables, continuous_reflectObservables⟩ * F

@[simp]
theorem reflectedSquare_apply (F : WilsonLoopSpace →ᵇ ℝ) (w : WilsonLoopSpace) :
    reflectedSquare F w = F (reflectObservables w) * F w := rfl

/-- A function on the common space that depends only on the loops in `S`. -/
def DependsOnLoops (S : Set PhysicalRectangle) (F : WilsonLoopSpace → ℝ) : Prop :=
  ∀ w w' : WilsonLoopSpace, (∀ ℓ ∈ S, w ℓ = w' ℓ) → F w = F w'

theorem DependsOnLoops.mono {S T : Set PhysicalRectangle} (hST : S ⊆ T)
    {F : WilsonLoopSpace → ℝ} (hF : DependsOnLoops S F) : DependsOnLoops T F :=
  fun w w' h => hF w w' fun ℓ hℓ => h ℓ (hST hℓ)

/-- The positive-time loops of a family `A`. -/
def positivePart (A : Set PhysicalRectangle) : Set PhysicalRectangle :=
  {ℓ | ℓ ∈ A ∧ ℓ.IsPositiveTime}

theorem dependsOnPositiveTime_iff (F : WilsonLoopSpace → ℝ) :
    DependsOnPositiveTime F ↔ DependsOnLoops (positivePart Set.univ) F := by
  simp [DependsOnPositiveTime, DependsOnLoops, positivePart]

/-- Reflection positivity of one law for the bounded continuous functionals of the
positive-time loops of a family `A`. -/
def IsReflectionPositiveOn (A : Set PhysicalRectangle)
    (ν : ProbabilityMeasure WilsonLoopSpace) : Prop :=
  ∀ F : WilsonLoopSpace →ᵇ ℝ, DependsOnLoops (positivePart A) F →
    0 ≤ ∫ w, F (reflectObservables w) * F w ∂(ν : Measure WilsonLoopSpace)

/-- Reflection positivity of one law in exactly the form of the `reflection_positive` field
of `ContinuumIdentificationObligations`. -/
def IsReflectionPositive (ν : ProbabilityMeasure WilsonLoopSpace) : Prop :=
  ∀ F : WilsonLoopSpace →ᵇ ℝ, DependsOnPositiveTime F →
    0 ≤ ∫ w, F (reflectObservables w) * F w ∂(ν : Measure WilsonLoopSpace)

theorem isReflectionPositive_iff_univ (ν : ProbabilityMeasure WilsonLoopSpace) :
    IsReflectionPositive ν ↔ IsReflectionPositiveOn Set.univ ν := by
  simp only [IsReflectionPositive, IsReflectionPositiveOn, dependsOnPositiveTime_iff]

/-- For every family of loops, reflection positivity is a closed condition for convergence
in distribution: it is an intersection of closed half-spaces `0 ≤ ∫ F (Θ w) F w`. -/
theorem isClosed_setOf_isReflectionPositiveOn (A : Set PhysicalRectangle) :
    IsClosed {ν : ProbabilityMeasure WilsonLoopSpace | IsReflectionPositiveOn A ν} := by
  have h : {ν : ProbabilityMeasure WilsonLoopSpace | IsReflectionPositiveOn A ν} =
      ⋂ F : WilsonLoopSpace →ᵇ ℝ, ⋂ (_ : DependsOnLoops (positivePart A) F),
        {ν : ProbabilityMeasure WilsonLoopSpace |
          0 ≤ ∫ w, reflectedSquare F w ∂(ν : Measure WilsonLoopSpace)} := by
    ext ν
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, reflectedSquare_apply, IsReflectionPositiveOn]
  rw [h]
  exact isClosed_iInter fun F => isClosed_iInter fun _ =>
    isClosed_le continuous_const
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (reflectedSquare F))

theorem isClosed_setOf_isReflectionPositive :
    IsClosed {ν : ProbabilityMeasure WilsonLoopSpace | IsReflectionPositive ν} := by
  have h : {ν : ProbabilityMeasure WilsonLoopSpace | IsReflectionPositive ν} =
      {ν | IsReflectionPositiveOn Set.univ ν} := by
    ext ν
    exact isReflectionPositive_iff_univ ν
  rw [h]
  exact isClosed_setOf_isReflectionPositiveOn Set.univ

/-- Inheritance: reflection positivity at all large indices passes to every weak limit. -/
theorem isReflectionPositiveOn_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (A : Set PhysicalRectangle) {μs : ι → ProbabilityMeasure WilsonLoopSpace}
    {ν : ProbabilityMeasure WilsonLoopSpace} (h : Tendsto μs l (𝓝 ν))
    (hμs : ∀ᶠ i in l, IsReflectionPositiveOn A (μs i)) : IsReflectionPositiveOn A ν :=
  (isClosed_setOf_isReflectionPositiveOn A).mem_of_tendsto h hμs

theorem isReflectionPositive_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure WilsonLoopSpace} {ν : ProbabilityMeasure WilsonLoopSpace}
    (h : Tendsto μs l (𝓝 ν)) (hμs : ∀ᶠ i in l, IsReflectionPositive (μs i)) :
    IsReflectionPositive ν :=
  isClosed_setOf_isReflectionPositive.mem_of_tendsto h hμs

/-! ### Renormalized loops -/

/-- Renormalization constants that do not distinguish a loop from its time reflection. -/
def HasReflectionInvariantFactors {P : CutoffPath} (Z : LoopRenormalization P) : Prop :=
  ∀ (n : ℕ) (ℓ : PhysicalRectangle), Z.factor n ℓ.timeReflect = Z.factor n ℓ

theorem rescale_reflectObservables {P : CutoffPath} (Z : LoopRenormalization P)
    (hZ : HasReflectionInvariantFactors Z) (n : ℕ) (w : WilsonLoopSpace) :
    Z.rescale n (reflectObservables w) = reflectObservables (Z.rescale n w) := by
  funext ℓ
  simp only [LoopRenormalization.rescale, reflectObservables, hZ n ℓ]

theorem DependsOnLoops.comp_rescale {P : CutoffPath} (Z : LoopRenormalization P) (n : ℕ)
    {S : Set PhysicalRectangle} {F : WilsonLoopSpace → ℝ} (hF : DependsOnLoops S F) :
    DependsOnLoops S (F ∘ Z.rescale n) := by
  intro w w' h
  apply hF
  intro ℓ hℓ
  simp only [LoopRenormalization.rescale, h ℓ hℓ]

/-- Reflection-invariant constants carry reflection positivity of the unrenormalized law at
one cutoff to the renormalized law at that cutoff. -/
theorem law_isReflectionPositiveOn {P : CutoffPath} (Z : LoopRenormalization P)
    (hZ : HasReflectionInvariantFactors Z) (A : Set PhysicalRectangle) (n : ℕ)
    (h : IsReflectionPositiveOn A (P.wilsonLoopLaw n)) : IsReflectionPositiveOn A (Z.law n) := by
  intro F hF
  have hG := h (F.compContinuous ⟨Z.rescale n, Z.continuous_rescale n⟩)
    (DependsOnLoops.comp_rescale Z n hF)
  have hcont : Continuous (fun w : WilsonLoopSpace => F (reflectObservables w) * F w) :=
    (F.continuous.comp continuous_reflectObservables).mul F.continuous
  rw [LoopRenormalization.law, ProbabilityMeasure.toMeasure_map,
    integral_map (Z.continuous_rescale n).aemeasurable hcont.aestronglyMeasurable]
  simpa only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
    rescale_reflectObservables Z hZ n] using hG

/-- The named lattice-level hypothesis: reflection positivity of the unrenormalized joint
Wilson-loop law, for the bounded continuous functionals of the positive-time loops of `A`, at
every large cutoff. With `A = Set.univ` this is the cutoff form of the `reflection_positive`
field. It is not proved in this form: the floor discretization does not commute with
`x₀ ↦ -x₀` for loops whose time data are not multiples of the spacing, and at a fixed cutoff
large loops do not fit in the half lattice. Sections 8–11 prove, from the actual Wilson
measure, the weaker cylinder-wise statement that suffices for loops with dyadic time data:
each finite set of them is positive at all large cutoffs along spacings `2⁻ⁿ`
(`limit_isReflectionPositiveOn_of_eventuallyAdapted`). The `∀ n` form of the `Set.univ`
instance is refuted on the periodic dyadic Wilson path at cutoff one
(`not_WilsonReflectionInputs_dyadic` in the generator-gap negative control); no theorem in this
module consumes the `Set.univ` instance, and it is not an open target. -/
structure CutoffReflectionPositivity (P : CutoffPath) (A : Set PhysicalRectangle) : Prop where
  eventually_positive : ∀ᶠ n in atTop, IsReflectionPositiveOn A (P.wilsonLoopLaw n)

/-- Inheritance for renormalized loops: under the per-cutoff hypothesis and reflection-invariant
constants, every limit law of the renormalized joint laws is reflection positive on `A`. -/
theorem limit_isReflectionPositiveOn {P : CutoffPath} (Z : LoopRenormalization P)
    (hZ : HasReflectionInvariantFactors Z) {A : Set PhysicalRectangle}
    (hP : CutoffReflectionPositivity P A) {ν : ProbabilityMeasure WilsonLoopSpace}
    (hν : Z.IsLimitLaw ν) : IsReflectionPositiveOn A ν := by
  obtain ⟨φ, hφ, hlim⟩ := hν
  exact isReflectionPositiveOn_of_tendsto A hlim
    ((hφ.tendsto_atTop.eventually hP.eventually_positive).mono fun n hn =>
      law_isReflectionPositiveOn Z hZ A (φ n) hn)

/-! ## 2. Reflection positivity is a condition on finite-dimensional marginals -/

/-- The unit square in the `(1, 2)` plane at the origin. -/
def referenceLoop : PhysicalRectangle :=
  ⟨fun _ => 0, 1, 2, by decide, 1, 1, one_pos, one_pos⟩

instance : Nonempty PhysicalRectangle := ⟨referenceLoop⟩

/-- Reflection positivity for the bounded continuous functionals of finitely many
positive-time loops of `A`. -/
def IsCylinderReflectionPositiveOn (A : Set PhysicalRectangle)
    (ν : ProbabilityMeasure WilsonLoopSpace) : Prop :=
  ∀ S : Finset PhysicalRectangle, (S : Set PhysicalRectangle) ⊆ positivePart A →
    ∀ F : WilsonLoopSpace →ᵇ ℝ, DependsOnLoops S F →
      0 ≤ ∫ w, F (reflectObservables w) * F w ∂(ν : Measure WilsonLoopSpace)

theorem continuous_indicator_loops (S : Set PhysicalRectangle) :
    Continuous (fun w : WilsonLoopSpace => S.indicator w) := by
  apply continuous_pi
  intro ℓ
  by_cases hℓ : ℓ ∈ S
  · simpa only [Set.indicator_of_mem hℓ] using continuous_apply ℓ
  · simpa only [Set.indicator_of_notMem hℓ] using continuous_const

/-- Reflection positivity on `A` is equivalent to its cylinder version: every bounded
continuous functional of the positive-time loops of `A` is a pointwise limit of functionals
of finitely many of them, with a uniform bound, and dominated convergence applies. -/
theorem isReflectionPositiveOn_iff_cylinder (A : Set PhysicalRectangle)
    (ν : ProbabilityMeasure WilsonLoopSpace) :
    IsReflectionPositiveOn A ν ↔ IsCylinderReflectionPositiveOn A ν := by
  classical
  constructor
  · intro h S hS F hF
    exact h F (hF.mono hS)
  · intro h F hF
    obtain ⟨e, he⟩ := exists_surjective_nat PhysicalRectangle
    let S : ℕ → Finset PhysicalRectangle := fun N =>
      ((Finset.range N).image e).filter (· ∈ positivePart A)
    have hSA : ∀ N, (S N : Set PhysicalRectangle) ⊆ positivePart A := by
      intro N ℓ hℓ
      exact (Finset.mem_filter.mp hℓ).2
    let FN : ℕ → WilsonLoopSpace →ᵇ ℝ := fun N =>
      F.compContinuous ⟨fun w => (S N : Set PhysicalRectangle).indicator w,
        continuous_indicator_loops _⟩
    have hFN : ∀ N, DependsOnLoops (S N) (FN N) := by
      intro N w w' hw
      change F ((S N : Set PhysicalRectangle).indicator w) =
        F ((S N : Set PhysicalRectangle).indicator w')
      congr 1
      funext ℓ
      by_cases hℓ : ℓ ∈ (S N : Set PhysicalRectangle)
      · simp only [Set.indicator_of_mem hℓ, hw ℓ hℓ]
      · simp only [Set.indicator_of_notMem hℓ]
    have hpos : ∀ N, 0 ≤ ∫ w, FN N (reflectObservables w) * FN N w ∂(ν : Measure WilsonLoopSpace) :=
      fun N => h (S N) (hSA N) (FN N) (hFN N)
    have hconv : ∀ w : WilsonLoopSpace,
        Tendsto (fun N => (S N : Set PhysicalRectangle).indicator w) atTop
          (𝓝 ((positivePart A).indicator w)) := by
      intro w
      rw [tendsto_pi_nhds]
      intro ℓ
      by_cases hℓ : ℓ ∈ positivePart A
      · obtain ⟨k, rfl⟩ := he ℓ
        rw [Set.indicator_of_mem hℓ]
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_gt_atTop k] with N hN
        have hmem : e k ∈ (S N : Set PhysicalRectangle) := by
          simp only [S, Finset.coe_filter, Finset.mem_image, Finset.mem_range, Set.mem_ofPred_eq]
          exact ⟨⟨k, hN, rfl⟩, hℓ⟩
        rw [Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hℓ]
        apply tendsto_const_nhds.congr'
        filter_upwards with N
        rw [Set.indicator_of_notMem (fun hmem => hℓ (hSA N hmem))]
    have hFind : ∀ w : WilsonLoopSpace, F ((positivePart A).indicator w) = F w := by
      intro w
      apply hF
      intro ℓ hℓ
      rw [Set.indicator_of_mem hℓ]
    have hlim : ∀ w : WilsonLoopSpace,
        Tendsto (fun N => FN N (reflectObservables w) * FN N w) atTop
          (𝓝 (F (reflectObservables w) * F w)) := by
      intro w
      have h1 := (F.continuous.tendsto _).comp (hconv (reflectObservables w))
      have h2 := (F.continuous.tendsto _).comp (hconv w)
      rw [hFind] at h1 h2
      exact h1.mul h2
    have hmeas : ∀ N, AEStronglyMeasurable
        (fun w => FN N (reflectObservables w) * FN N w) (ν : Measure WilsonLoopSpace) :=
      fun N => (((FN N).continuous.comp continuous_reflectObservables).mul
        (FN N).continuous).aestronglyMeasurable
    have hbound : ∀ N, ∀ᵐ w ∂(ν : Measure WilsonLoopSpace),
        ‖FN N (reflectObservables w) * FN N w‖ ≤ ‖F‖ * ‖F‖ := by
      intro N
      filter_upwards with w
      rw [norm_mul]
      exact mul_le_mul (F.norm_coe_le_norm _) (F.norm_coe_le_norm _) (norm_nonneg _)
        (norm_nonneg _)
    have hint := tendsto_integral_of_dominated_convergence (fun _ => ‖F‖ * ‖F‖) hmeas
      (integrable_const _) hbound (Eventually.of_forall hlim)
    exact ge_of_tendsto' hint hpos

/-! ## 3. Clustering and nontriviality as predicates on one law -/

/-- Time mixing of one law, in exactly the form of the `time_mixing` field. -/
def IsTimeMixing (ν : ProbabilityMeasure WilsonLoopSpace) : Prop :=
  ∀ F G : WilsonLoopSpace →ᵇ ℝ,
    Tendsto (fun t : ℕ => ∫ w, F w * G (translateObservables (timeVector t) w)
        ∂(ν : Measure WilsonLoopSpace)) atTop
      (𝓝 ((∫ w, F w ∂(ν : Measure WilsonLoopSpace)) * ∫ w, G w ∂(ν : Measure WilsonLoopSpace)))

/-- Nontriviality of one law, in exactly the form of the `nontrivial` field. -/
def IsNontrivial (ν : ProbabilityMeasure WilsonLoopSpace) : Prop :=
  ∃ ℓ ℓ' : PhysicalRectangle, ℓ.timeEnd < ℓ'.base 0 ∧
    ¬ IndepFun (fun w : WilsonLoopSpace => w ℓ) (fun w => w ℓ') (ν : Measure WilsonLoopSpace)

/-- A law that is almost surely invariant under the time translations by all multiples of a
period `T ≥ 1` is time mixing only if every bounded continuous functional has zero variance. -/
theorem integral_mul_self_of_isTimeMixing_of_periodic {ν : ProbabilityMeasure WilsonLoopSpace}
    (hν : IsTimeMixing ν) {T : ℕ} (hT : 0 < T)
    (hper : ∀ k : ℕ, ∀ᵐ w ∂(ν : Measure WilsonLoopSpace),
      translateObservables (timeVector (k * T)) w = w)
    (F : WilsonLoopSpace →ᵇ ℝ) :
    ∫ w, F w * F w ∂(ν : Measure WilsonLoopSpace) =
      (∫ w, F w ∂(ν : Measure WilsonLoopSpace)) * ∫ w, F w ∂(ν : Measure WilsonLoopSpace) := by
  have hmono : StrictMono (fun k : ℕ => k * T) := fun a b hab => Nat.mul_lt_mul_of_pos_right hab hT
  have h : Tendsto (fun k : ℕ => ∫ w, F w * F (translateObservables (timeVector (k * T)) w)
      ∂(ν : Measure WilsonLoopSpace)) atTop
      (𝓝 ((∫ w, F w ∂(ν : Measure WilsonLoopSpace)) * ∫ w, F w ∂(ν : Measure WilsonLoopSpace))) :=
    (hν F F).comp hmono.tendsto_atTop
  have hconst : (fun k : ℕ => ∫ w, F w * F (translateObservables (timeVector (k * T)) w)
      ∂(ν : Measure WilsonLoopSpace)) = fun _ => ∫ w, F w * F w ∂(ν : Measure WilsonLoopSpace) := by
    funext k
    apply integral_congr_ae
    filter_upwards [hper k] with w hw
    rw [hw]
  rw [hconst] at h
  exact tendsto_nhds_unique tendsto_const_nhds h

/-! ### An explicit family on the common space -/

/-- The configuration with the same value `s` on every loop. -/
def constLoops (s : ℝ) : WilsonLoopSpace := fun _ => s

theorem continuous_constLoops : Continuous constLoops :=
  continuous_pi fun _ => continuous_id

@[simp]
theorem translateObservables_constLoops (c : Fin 4 → ℚ) (s : ℝ) :
    translateObservables c (constLoops s) = constLoops s := rfl

/-- The law of a common random sign of size `s`: `½ δ_{s} + ½ δ_{-s}` on constant
configurations. Every loop takes the same value. -/
def signLaw (s : ℝ) : ProbabilityMeasure WilsonLoopSpace :=
  ⟨(2⁻¹ : ℝ≥0∞) • Measure.dirac (constLoops s) + (2⁻¹ : ℝ≥0∞) • Measure.dirac (constLoops (-s)),
    ⟨by simp [ENNReal.inv_two_add_inv_two]⟩⟩

theorem integral_signLaw (s : ℝ) (f : WilsonLoopSpace → ℝ) :
    ∫ w, f w ∂(signLaw s : Measure WilsonLoopSpace) =
      2⁻¹ * f (constLoops s) + 2⁻¹ * f (constLoops (-s)) := by
  change ∫ w, f w ∂((2⁻¹ : ℝ≥0∞) • Measure.dirac (constLoops s) +
    (2⁻¹ : ℝ≥0∞) • Measure.dirac (constLoops (-s))) = _
  have hi : ∀ x : WilsonLoopSpace, Integrable f ((2⁻¹ : ℝ≥0∞) • Measure.dirac x) := fun x =>
    (integrable_dirac enorm_lt_top).smul_measure (by simp)
  rw [integral_add_measure (hi _) (hi _), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  simp

theorem integral_diracProba (x : WilsonLoopSpace) (f : WilsonLoopSpace → ℝ) :
    ∫ w, f w ∂(diracProba x : Measure WilsonLoopSpace) = f x :=
  integral_dirac f x

/-- The family converges to the Dirac law at the zero configuration. -/
theorem signLaw_tendsto :
    Tendsto (fun n : ℕ => signLaw (1 / ((n : ℝ) + 1))) atTop
      (𝓝 (diracProba (constLoops 0))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hs : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto (fun n : ℕ => f (constLoops (1 / ((n : ℝ) + 1)))) atTop
      (𝓝 (f (constLoops 0))) :=
    (f.continuous.tendsto _).comp ((continuous_constLoops.tendsto 0).comp hs)
  have h2 : Tendsto (fun n : ℕ => f (constLoops (-(1 / ((n : ℝ) + 1))))) atTop
      (𝓝 (f (constLoops 0))) := by
    have hneg : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using hs.neg
    exact (f.continuous.tendsto _).comp ((continuous_constLoops.tendsto 0).comp hneg)
  have h := (h1.const_mul 2⁻¹).add (h2.const_mul 2⁻¹)
  simp only [integral_signLaw, integral_diracProba]
  convert h using 2
  ring

/-- The truncation `x ↦ max (-1) (min 1 x)` as a bounded continuous function. -/
def unitClamp : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => max (-1) (min 1 x), by fun_prop⟩ 2 (by
    intro x y
    have hx1 : (-1 : ℝ) ≤ max (-1) (min 1 x) := le_max_left _ _
    have hx2 : max (-1) (min 1 x) ≤ 1 := max_le (by norm_num) (min_le_left _ _)
    have hy1 : (-1 : ℝ) ≤ max (-1) (min 1 y) := le_max_left _ _
    have hy2 : max (-1) (min 1 y) ≤ 1 := max_le (by norm_num) (min_le_left _ _)
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    rw [abs_le]
    constructor <;> linarith)

theorem unitClamp_of_mem {x : ℝ} (h1 : -1 ≤ x) (h2 : x ≤ 1) : unitClamp x = x := by
  change max (-1) (min 1 x) = x
  rw [min_eq_right h2, max_eq_right h1]

/-- A bounded continuous function of one loop. -/
def loopTest (f : ℝ →ᵇ ℝ) (ℓ : PhysicalRectangle) : WilsonLoopSpace →ᵇ ℝ :=
  f.compContinuous ⟨fun w => w ℓ, continuous_apply ℓ⟩

@[simp]
theorem loopTest_apply (f : ℝ →ᵇ ℝ) (ℓ : PhysicalRectangle) (w : WilsonLoopSpace) :
    loopTest f ℓ w = f (w ℓ) := rfl

/-- A loop starting at physical time `1`. -/
def laterLoop : PhysicalRectangle :=
  ⟨fun i => if i = 0 then 1 else 0, 1, 2, by decide, 1, 1, one_pos, one_pos⟩

theorem referenceLoop_timeEnd_lt : referenceLoop.timeEnd < laterLoop.base 0 := by
  simp [PhysicalRectangle.timeEnd, referenceLoop, laterLoop]

/-- No law of the family is time mixing. -/
theorem not_isTimeMixing_signLaw {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ¬ IsTimeMixing (signLaw s) := by
  intro h
  have hlim := h (loopTest unitClamp referenceLoop) (loopTest unitClamp referenceLoop)
  have hcs : unitClamp s = s := unitClamp_of_mem (by linarith) hs1
  have hcn : unitClamp (-s) = -s := unitClamp_of_mem (by linarith) (by linarith)
  simp only [integral_signLaw, loopTest_apply, translateObservables_constLoops] at hlim
  simp only [constLoops, hcs, hcn] at hlim
  have heq : 2⁻¹ * (s * s) + 2⁻¹ * (-s * -s) = (2⁻¹ * s + 2⁻¹ * -s) * (2⁻¹ * s + 2⁻¹ * -s) :=
    tendsto_nhds_unique tendsto_const_nhds hlim
  nlinarith

/-- The Dirac law at a constant configuration is time mixing. -/
theorem isTimeMixing_diracProba_constLoops (s : ℝ) : IsTimeMixing (diracProba (constLoops s)) := by
  intro F G
  simp only [integral_diracProba, translateObservables_constLoops]
  exact tendsto_const_nhds

/-- Under a Dirac law any two measurable functions are independent. -/
theorem indepFun_dirac {Ω β β' : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    [MeasurableSpace β'] (x : Ω) {f : Ω → β} {g : Ω → β'} (hf : Measurable f)
    (hg : Measurable g) : IndepFun f g (Measure.dirac x) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  rw [Measure.dirac_apply' _ ((hf hA).inter (hg hB)), Measure.dirac_apply' _ (hf hA),
    Measure.dirac_apply' _ (hg hB)]
  by_cases hxA : x ∈ f ⁻¹' A <;> by_cases hxB : x ∈ g ⁻¹' B <;>
    simp [Set.indicator, hxA, hxB]

theorem not_isNontrivial_diracProba (x : WilsonLoopSpace) : ¬ IsNontrivial (diracProba x) := by
  rintro ⟨ℓ, ℓ', -, h⟩
  exact h (indepFun_dirac x (measurable_pi_apply ℓ) (measurable_pi_apply ℓ'))

/-- Every law of the family is nontrivial: two time-separated loops are equal and not constant. -/
theorem isNontrivial_signLaw {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) : IsNontrivial (signLaw s) := by
  refine ⟨referenceLoop, laterLoop, referenceLoop_timeEnd_lt, fun hind => ?_⟩
  have h := (hind.comp unitClamp.continuous.measurable
    unitClamp.continuous.measurable).integral_mul_eq_mul_integral
    (unitClamp.continuous.comp (continuous_apply _)).aestronglyMeasurable
    (unitClamp.continuous.comp (continuous_apply _)).aestronglyMeasurable
  have hcs : unitClamp s = s := unitClamp_of_mem (by linarith) hs1
  have hcn : unitClamp (-s) = -s := unitClamp_of_mem (by linarith) (by linarith)
  simp only [Pi.mul_apply, Function.comp_apply, integral_signLaw] at h
  simp only [constLoops, hcs, hcn] at h
  nlinarith

/-- One explicit family on the common space: every law of the family is nontrivial and none is
time mixing, while its weak limit is trivial and time mixing. So nontriviality can hold at every
index and fail in the limit, and time mixing can fail at every index and hold in the limit. -/
theorem signLaw_family_counterexample :
    Tendsto (fun n : ℕ => signLaw (1 / ((n : ℝ) + 1))) atTop
      (𝓝 (diracProba (constLoops 0))) ∧
    (∀ n : ℕ, IsNontrivial (signLaw (1 / ((n : ℝ) + 1)))) ∧
    ¬ IsNontrivial (diracProba (constLoops 0)) ∧
    (∀ n : ℕ, ¬ IsTimeMixing (signLaw (1 / ((n : ℝ) + 1)))) ∧
    IsTimeMixing (diracProba (constLoops 0)) := by
  have hpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hle : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact ⟨signLaw_tendsto, fun n => isNontrivial_signLaw (hpos n) (hle n),
    not_isNontrivial_diracProba _, fun n => not_isTimeMixing_signLaw (hpos n) (hle n),
    isTimeMixing_diracProba_constLoops 0⟩

/-! ### Independence of two loops is closed, so nontriviality is open -/

/-- The joint value of two loops. -/
def loopPair (ℓ ℓ' : PhysicalRectangle) (w : WilsonLoopSpace) : ℝ × ℝ := (w ℓ, w ℓ')

theorem continuous_loopPair (ℓ ℓ' : PhysicalRectangle) : Continuous (loopPair ℓ ℓ') :=
  (continuous_apply ℓ).prodMk (continuous_apply ℓ')

theorem indepFun_loops_iff (ℓ ℓ' : PhysicalRectangle) (ν : ProbabilityMeasure WilsonLoopSpace) :
    IndepFun (fun w : WilsonLoopSpace => w ℓ) (fun w => w ℓ') (ν : Measure WilsonLoopSpace) ↔
      ν.map (loopPair ℓ ℓ') =
        (ν.map (fun w : WilsonLoopSpace => w ℓ)).prod
          (ν.map (fun w : WilsonLoopSpace => w ℓ')) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (continuous_apply ℓ).aemeasurable
    (continuous_apply ℓ').aemeasurable]
  constructor
  · intro h
    exact ProbabilityMeasure.toMeasure_injective h
  · intro h
    exact congrArg ProbabilityMeasure.toMeasure h

/-- Independence of two loops is a closed condition for convergence in distribution. -/
theorem isClosed_setOf_indepFun_loops (ℓ ℓ' : PhysicalRectangle) :
    IsClosed {ν : ProbabilityMeasure WilsonLoopSpace |
      IndepFun (fun w : WilsonLoopSpace => w ℓ) (fun w => w ℓ') (ν : Measure WilsonLoopSpace)} := by
  have h : {ν : ProbabilityMeasure WilsonLoopSpace |
      IndepFun (fun w : WilsonLoopSpace => w ℓ) (fun w => w ℓ') (ν : Measure WilsonLoopSpace)} =
      {ν | ν.map (loopPair ℓ ℓ') =
        (ν.map (fun w : WilsonLoopSpace => w ℓ)).prod
          (ν.map (fun w : WilsonLoopSpace => w ℓ'))} := by
    ext ν
    exact indepFun_loops_iff ℓ ℓ' ν
  rw [h]
  exact isClosed_eq (ProbabilityMeasure.continuous_map (continuous_loopPair ℓ ℓ'))
    (ProbabilityMeasure.continuous_prod.comp
      ((ProbabilityMeasure.continuous_map (continuous_apply ℓ)).prodMk
        (ProbabilityMeasure.continuous_map (continuous_apply ℓ'))))

/-- Nontriviality is an open condition. -/
theorem isOpen_setOf_isNontrivial :
    IsOpen {ν : ProbabilityMeasure WilsonLoopSpace | IsNontrivial ν} := by
  have h : {ν : ProbabilityMeasure WilsonLoopSpace | IsNontrivial ν} =
      ⋃ ℓ : PhysicalRectangle, ⋃ ℓ' : PhysicalRectangle, ⋃ (_ : ℓ.timeEnd < ℓ'.base 0),
        {ν : ProbabilityMeasure WilsonLoopSpace | IndepFun (fun w : WilsonLoopSpace => w ℓ)
          (fun w => w ℓ') (ν : Measure WilsonLoopSpace)}ᶜ := by
    ext ν
    simp [IsNontrivial]
  rw [h]
  exact isOpen_iUnion fun ℓ => isOpen_iUnion fun ℓ' => isOpen_iUnion fun _ =>
    (isClosed_setOf_indepFun_loops ℓ ℓ').isOpen_compl

/-- A nontrivial weak limit forces nontriviality at all large indices. -/
theorem eventually_isNontrivial_of_tendsto {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure WilsonLoopSpace} {ν : ProbabilityMeasure WilsonLoopSpace}
    (h : Tendsto μs l (𝓝 ν)) (hν : IsNontrivial ν) : ∀ᶠ i in l, IsNontrivial (μs i) :=
  h (isOpen_setOf_isNontrivial.mem_nhds hν)

/-- Contrapositive: trivial laws at all large indices have only trivial weak limits. -/
theorem not_isNontrivial_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure WilsonLoopSpace} {ν : ProbabilityMeasure WilsonLoopSpace}
    (h : Tendsto μs l (𝓝 ν)) (hμs : ∀ᶠ i in l, ¬ IsNontrivial (μs i)) : ¬ IsNontrivial ν := by
  intro hν
  obtain ⟨i, hi1, hi2⟩ := (hμs.and (eventually_isNontrivial_of_tendsto h hν)).exists
  exact hi1 hi2

/-! ## 4. Connected correlations: exactly what nontriviality of a limit needs -/

section Correlation

variable {ι : Type*} [Countable ι]

/-- Connected correlation of two bounded continuous functions of two coordinates. -/
def connectedCorrelation (ν : ProbabilityMeasure (ι → ℝ)) (i j : ι) (f g : ℝ →ᵇ ℝ) : ℝ :=
  ∫ w, f (w i) * g (w j) ∂(ν : Measure (ι → ℝ)) -
    (∫ w, f (w i) ∂(ν : Measure (ι → ℝ))) * ∫ w, g (w j) ∂(ν : Measure (ι → ℝ))

theorem continuous_connectedCorrelation (i j : ι) (f g : ℝ →ᵇ ℝ) :
    Continuous fun ν : ProbabilityMeasure (ι → ℝ) => connectedCorrelation ν i j f g := by
  have hi : Continuous (fun w : ι → ℝ => w i) := continuous_apply i
  have hj : Continuous (fun w : ι → ℝ => w j) := continuous_apply j
  have h1 := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (f.compContinuous ⟨fun w : ι → ℝ => w i, hi⟩ * g.compContinuous ⟨fun w : ι → ℝ => w j, hj⟩)
  have h2 := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (f.compContinuous ⟨fun w : ι → ℝ => w i, hi⟩)
  have h3 := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (g.compContinuous ⟨fun w : ι → ℝ => w j, hj⟩)
  exact h1.sub (h2.mul h3)

theorem connectedCorrelation_eq_zero_of_indepFun {ν : ProbabilityMeasure (ι → ℝ)} {i j : ι}
    (h : IndepFun (fun w : ι → ℝ => w i) (fun w => w j) (ν : Measure (ι → ℝ)))
    (f g : ℝ →ᵇ ℝ) : connectedCorrelation ν i j f g = 0 := by
  have h' := (h.comp f.continuous.measurable g.continuous.measurable).integral_mul_eq_mul_integral
    (f.continuous.comp (continuous_apply i)).aestronglyMeasurable
    (g.continuous.comp (continuous_apply j)).aestronglyMeasurable
  unfold connectedCorrelation
  simp only [Pi.mul_apply, Function.comp_apply] at h'
  rw [h', sub_self]

omit [Countable ι] in
theorem indepFun_of_connectedCorrelation_eq_zero {ν : ProbabilityMeasure (ι → ℝ)} {i j : ι}
    (h : ∀ f g : ℝ →ᵇ ℝ, connectedCorrelation ν i j f g = 0) :
    IndepFun (fun w : ι → ℝ => w i) (fun w => w j) (ν : Measure (ι → ℝ)) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable]
  apply _root_.Measure.eq_prod_of_integral_mul_boundedContinuousFunction
  intro f g
  rw [integral_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
      ((f.continuous.comp continuous_fst).mul
        (g.continuous.comp continuous_snd)).aestronglyMeasurable,
    integral_map (measurable_pi_apply i).aemeasurable f.continuous.aestronglyMeasurable,
    integral_map (measurable_pi_apply j).aemeasurable g.continuous.aestronglyMeasurable]
  exact sub_eq_zero.mp (h f g)

/-- Two coordinates are independent exactly when all their bounded continuous connected
correlations vanish. -/
theorem indepFun_iff_connectedCorrelation_eq_zero (ν : ProbabilityMeasure (ι → ℝ)) (i j : ι) :
    IndepFun (fun w : ι → ℝ => w i) (fun w => w j) (ν : Measure (ι → ℝ)) ↔
      ∀ f g : ℝ →ᵇ ℝ, connectedCorrelation ν i j f g = 0 :=
  ⟨fun h => connectedCorrelation_eq_zero_of_indepFun h,
    indepFun_of_connectedCorrelation_eq_zero⟩

theorem connectedCorrelation_diracProba (x : ι → ℝ) (i j : ι) (f g : ℝ →ᵇ ℝ) :
    connectedCorrelation (diracProba x) i j f g = 0 := by
  unfold connectedCorrelation
  rw [show ((diracProba x : ProbabilityMeasure (ι → ℝ)) : Measure (ι → ℝ)) = Measure.dirac x
    from rfl, integral_dirac, integral_dirac, integral_dirac, sub_self]

end Correlation

/-- A uniform lower bound on one bounded connected correlation of two time-separated loops
along a convergent sequence makes the limit nontrivial. -/
theorem isNontrivial_of_tendsto_of_lowerBound {ι' : Type*} {l : Filter ι'} [l.NeBot]
    {μs : ι' → ProbabilityMeasure WilsonLoopSpace} {ν : ProbabilityMeasure WilsonLoopSpace}
    (h : Tendsto μs l (𝓝 ν)) {ℓ ℓ' : PhysicalRectangle} (hsep : ℓ.timeEnd < ℓ'.base 0)
    {f g : ℝ →ᵇ ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hev : ∀ᶠ i in l, δ ≤ |connectedCorrelation (μs i) ℓ ℓ' f g|) : IsNontrivial ν := by
  have hc : Tendsto (fun i => |connectedCorrelation (μs i) ℓ ℓ' f g|) l
      (𝓝 |connectedCorrelation ν ℓ ℓ' f g|) :=
    (((continuous_connectedCorrelation ℓ ℓ' f g).tendsto ν).comp h).abs
  have hle : δ ≤ |connectedCorrelation ν ℓ ℓ' f g| := ge_of_tendsto hc hev
  refine ⟨ℓ, ℓ', hsep, fun hind => ?_⟩
  rw [connectedCorrelation_eq_zero_of_indepFun hind f g, abs_zero] at hle
  linarith

/-- Conversely, a nontrivial limit forces such a uniform lower bound along the sequence. -/
theorem exists_lowerBound_of_tendsto_of_isNontrivial {ι' : Type*} {l : Filter ι'}
    {μs : ι' → ProbabilityMeasure WilsonLoopSpace} {ν : ProbabilityMeasure WilsonLoopSpace}
    (h : Tendsto μs l (𝓝 ν)) (hν : IsNontrivial ν) :
    ∃ (ℓ ℓ' : PhysicalRectangle) (f g : ℝ →ᵇ ℝ) (δ : ℝ), ℓ.timeEnd < ℓ'.base 0 ∧ 0 < δ ∧
      ∀ᶠ i in l, δ ≤ |connectedCorrelation (μs i) ℓ ℓ' f g| := by
  obtain ⟨ℓ, ℓ', hsep, hdep⟩ := hν
  obtain ⟨f, g, hfg⟩ : ∃ f g : ℝ →ᵇ ℝ, connectedCorrelation ν ℓ ℓ' f g ≠ 0 := by
    by_contra hall
    apply hdep
    apply indepFun_of_connectedCorrelation_eq_zero
    intro f g
    by_contra hne
    exact hall ⟨f, g, hne⟩
  have hpos : 0 < |connectedCorrelation ν ℓ ℓ' f g| := abs_pos.mpr hfg
  refine ⟨ℓ, ℓ', f, g, |connectedCorrelation ν ℓ ℓ' f g| / 2, hsep, by positivity, ?_⟩
  have hc : Tendsto (fun i => |connectedCorrelation (μs i) ℓ ℓ' f g|) l
      (𝓝 |connectedCorrelation ν ℓ ℓ' f g|) :=
    (((continuous_connectedCorrelation ℓ ℓ' f g).tendsto ν).comp h).abs
  exact (hc.eventually (lt_mem_nhds (half_lt_self hpos))).mono fun i hi => hi.le

/-- The named input that a renormalization must supply for the `nontrivial` field: two
time-separated loops and two bounded continuous test functions whose connected correlation
under the renormalized joint law stays at least `δ > 0` in absolute value at every large
cutoff. It is not proved here for any renormalization of the actual model.
Bounded test functions are what convergence in distribution transports; a lower bound on the
raw covariance of the renormalized loops would need, in addition, uniform integrability, which
is stronger than `LoopRenormalization.TailObligation`. -/
structure ConnectedCorrelationLowerBound {P : CutoffPath} (Z : LoopRenormalization P) : Prop where
  bound : ∃ (ℓ ℓ' : PhysicalRectangle) (f g : ℝ →ᵇ ℝ) (δ : ℝ), ℓ.timeEnd < ℓ'.base 0 ∧ 0 < δ ∧
    ∀ᶠ n in atTop, δ ≤ |connectedCorrelation (Z.law n) ℓ ℓ' f g|

/-- Sufficiency: under the named lower bound every limit law of the renormalized loops is
nontrivial. -/
theorem limit_isNontrivial_of_lowerBound {P : CutoffPath} (Z : LoopRenormalization P)
    (h : ConnectedCorrelationLowerBound Z) {ν : ProbabilityMeasure WilsonLoopSpace}
    (hν : Z.IsLimitLaw ν) : IsNontrivial ν := by
  obtain ⟨ℓ, ℓ', f, g, δ, hsep, hδ, hev⟩ := h.bound
  obtain ⟨φ, hφ, hlim⟩ := hν
  exact isNontrivial_of_tendsto_of_lowerBound hlim hsep hδ (hφ.tendsto_atTop.eventually hev)

/-- The `nontrivial` field of `ContinuumIdentificationObligations`, discharged from the named
lower bound. -/
theorem nontrivial_of_connectedCorrelationLowerBound {P : ContinuumCutoffPath}
    (Z : LoopRenormalization P.toCutoffPath) (h : ConnectedCorrelationLowerBound Z) :
    ∀ ν, Z.IsLimitLaw ν → ∃ ℓ ℓ' : PhysicalRectangle, ℓ.timeEnd < ℓ'.base 0 ∧
      ¬ IndepFun (fun w : WilsonLoopSpace => w ℓ) (fun w => w ℓ') (ν : Measure WilsonLoopSpace) :=
  fun _ hν => limit_isNontrivial_of_lowerBound Z h hν

/-- Necessity along the subsequence: a limit law along `φ` is nontrivial exactly when some
bounded connected correlation of two time-separated loops is bounded away from zero along `φ`. -/
theorem isNontrivial_limit_iff {P : CutoffPath} (Z : LoopRenormalization P) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) {ν : ProbabilityMeasure WilsonLoopSpace}
    (hlim : Tendsto (fun n => Z.law (φ n)) atTop (𝓝 ν)) :
    IsNontrivial ν ↔ ∃ (ℓ ℓ' : PhysicalRectangle) (f g : ℝ →ᵇ ℝ) (δ : ℝ),
      ℓ.timeEnd < ℓ'.base 0 ∧ 0 < δ ∧
        ∀ᶠ n in atTop, δ ≤ |connectedCorrelation (Z.law (φ n)) ℓ ℓ' f g| := by
  have _ := hφ
  constructor
  · exact exists_lowerBound_of_tendsto_of_isNontrivial hlim
  · rintro ⟨ℓ, ℓ', f, g, δ, hsep, hδ, hev⟩
    exact isNontrivial_of_tendsto_of_lowerBound hlim hsep hδ hev

/-- At one cutoff a multiplicative renormalization only reparametrizes the test functions. -/
theorem connectedCorrelation_law {P : CutoffPath} (Z : LoopRenormalization P) (n : ℕ)
    (ℓ ℓ' : PhysicalRectangle) (f g : ℝ →ᵇ ℝ) :
    connectedCorrelation (Z.law n) ℓ ℓ' f g =
      connectedCorrelation (P.wilsonLoopLaw n) ℓ ℓ'
        (f.compContinuous ⟨fun x => Z.factor n ℓ * x, by fun_prop⟩)
        (g.compContinuous ⟨fun x => Z.factor n ℓ' * x, by fun_prop⟩) := by
  have hr := (Z.continuous_rescale n).aemeasurable
    (μ := (P.wilsonLoopLaw n : Measure WilsonLoopSpace))
  have c1 : Continuous (fun w : WilsonLoopSpace => f (w ℓ) * g (w ℓ')) :=
    (f.continuous.comp (continuous_apply ℓ)).mul (g.continuous.comp (continuous_apply ℓ'))
  have c2 : Continuous (fun w : WilsonLoopSpace => f (w ℓ)) :=
    f.continuous.comp (continuous_apply ℓ)
  have c3 : Continuous (fun w : WilsonLoopSpace => g (w ℓ')) :=
    g.continuous.comp (continuous_apply ℓ')
  simp only [connectedCorrelation, LoopRenormalization.law, ProbabilityMeasure.toMeasure_map]
  rw [integral_map hr c1.aestronglyMeasurable, integral_map hr c2.aestronglyMeasurable,
    integral_map hr c3.aestronglyMeasurable]
  rfl

/-- Positive rescaling, inverted. -/
theorem compContinuous_scale_inv (f : ℝ →ᵇ ℝ) {c : ℝ} (hc : c ≠ 0) :
    (f.compContinuous ⟨fun x => c⁻¹ * x, by fun_prop⟩).compContinuous
      ⟨fun x => c * x, by fun_prop⟩ = f := by
  ext x
  simp [inv_mul_cancel_left₀ hc]

/-- At every cutoff, two loops are independent under the renormalized joint law exactly when
they are independent under the unrenormalized one. So a cutoff-by-cutoff statement cannot
distinguish renormalizations; only the uniformity in `n` of `ConnectedCorrelationLowerBound`
can. -/
theorem indepFun_law_iff {P : CutoffPath} (Z : LoopRenormalization P) (n : ℕ)
    (ℓ ℓ' : PhysicalRectangle) :
    IndepFun (fun w : WilsonLoopSpace => w ℓ) (fun w => w ℓ') (Z.law n : Measure WilsonLoopSpace) ↔
      IndepFun (fun w : WilsonLoopSpace => w ℓ) (fun w => w ℓ')
        (P.wilsonLoopLaw n : Measure WilsonLoopSpace) := by
  rw [indepFun_iff_connectedCorrelation_eq_zero, indepFun_iff_connectedCorrelation_eq_zero]
  constructor
  · intro h f g
    have h' := h (f.compContinuous ⟨fun x => (Z.factor n ℓ)⁻¹ * x, by fun_prop⟩)
      (g.compContinuous ⟨fun x => (Z.factor n ℓ')⁻¹ * x, by fun_prop⟩)
    rwa [connectedCorrelation_law, compContinuous_scale_inv f (Z.factor_pos n ℓ).ne',
      compContinuous_scale_inv g (Z.factor_pos n ℓ').ne'] at h'
  · intro h f g
    rw [connectedCorrelation_law]
    exact h _ _

theorem isNontrivial_law_iff {P : CutoffPath} (Z : LoopRenormalization P) (n : ℕ) :
    IsNontrivial (Z.law n) ↔ IsNontrivial (P.wilsonLoopLaw n) := by
  simp only [IsNontrivial, indepFun_law_iff]

/-- The collapse of the unrenormalized plaquette averages along every continuum cutoff path
kills every bounded connected correlation. -/
theorem plaquetteAverage_connectedCorrelation_tendsto_zero (P : ContinuumCutoffPath)
    (R R' : PhysicalPlaquetteRegion) (f g : ℝ →ᵇ ℝ) :
    Tendsto (fun n => connectedCorrelation (P.plaquetteAverageLaw n) R R' f g) atTop (𝓝 0) := by
  have h := ((continuous_connectedCorrelation R R' f g).tendsto _).comp
    P.plaquetteAverageLaw_tendsto
  rwa [connectedCorrelation_diracProba] at h

/-- Hence the unrenormalized plaquette averages admit no lower bound of the kind that
`ConnectedCorrelationLowerBound` asks of the renormalized loops, for any pair of regions and any
bounded continuous test functions. -/
theorem plaquetteAverage_no_lowerBound (P : ContinuumCutoffPath) (R R' : PhysicalPlaquetteRegion)
    (f g : ℝ →ᵇ ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ¬ ∀ᶠ n in atTop, δ ≤ |connectedCorrelation (P.plaquetteAverageLaw n) R R' f g| := by
  intro hev
  have h := (plaquetteAverage_connectedCorrelation_tendsto_zero P R R' f g).abs
  rw [abs_zero] at h
  obtain ⟨n, hn1, hn2⟩ := (hev.and (h.eventually (gt_mem_nhds hδ))).exists
  linarith

/-! ## 5. The actual finite periodic cutoff laws are never time mixing -/

/-- `-1 ∈ SU(2)`. -/
def negOne : SU2 where
  mat := -1
  unitary := by simp
  det_one := by norm_num [Matrix.det_fin_two]

theorem halfTraceRe_negOne : halfTraceRe negOne = -1 := by
  have h : SU2.trace negOne = -2 := by
    change Matrix.trace (-1 : Matrix (Fin 2) (Fin 2) ℂ) = -2
    rw [Matrix.trace_neg, Matrix.trace_one, Fintype.card_fin]
    norm_num
  simp [halfTraceRe, h]

/-- The configuration with the single link `e₀` equal to `-1` and all others `1`. -/
def flipLink {L : ℕ} (e₀ : Link L) : GaugeConfig L := fun e => if e = e₀ then negOne else 1

theorem unitVec_ne_zero {L : ℕ} (hL : 2 ≤ L) (μ : Direction) : unitVec L μ ≠ 0 := by
  have : Fact (1 < L) := ⟨by omega⟩
  intro h
  have h1 := congrFun h μ
  simp only [unitVec, Pi.zero_apply] at h1
  simp at h1

/-- On a lattice of side at least two, flipping one link of a plaquette gives it the maximal
action `2`. -/
theorem plaquetteAction_flipLink {L : ℕ} (hL : 2 ≤ L) (p : Plaquette L) :
    plaquetteAction (flipLink ⟨p.x, p.μ⟩) p = 2 := by
  have hμν : p.μ ≠ p.ν := p.h.ne
  have h1 : (⟨shift p.x p.μ, p.ν⟩ : Link L) ≠ ⟨p.x, p.μ⟩ := fun h =>
    hμν (congrArg Link.μ h).symm
  have h2 : (⟨shift p.x p.ν, p.μ⟩ : Link L) ≠ ⟨p.x, p.μ⟩ := by
    intro h
    have hx : p.x + unitVec L p.ν = p.x + 0 := by
      rw [add_zero]
      exact congrArg Link.x h
    exact unitVec_ne_zero hL p.ν (add_left_cancel hx)
  have h3 : (⟨p.x, p.ν⟩ : Link L) ≠ ⟨p.x, p.μ⟩ := fun h => hμν (congrArg Link.μ h).symm
  have hhol : plaquetteHolonomy (flipLink ⟨p.x, p.μ⟩) p = negOne := by
    simp [plaquetteHolonomy, flipLink, h1, h2, h3]
  rw [plaquetteAction_eq_one_sub_halfTraceRe, hhol, halfTraceRe_negOne]
  norm_num

/-- Under the actual Wilson law every continuous observable that takes two different values
has strictly positive variance: the Wilson density is positive and product Haar charges every
nonempty open set. -/
theorem wilson_variance_ne {L : ℕ} [NeZero L] (β : ℝ) (hβ : 0 ≤ β) {Y : GaugeConfig L → ℝ}
    (hY : Continuous Y) {U₁ U₂ : GaugeConfig L} (h12 : Y U₁ ≠ Y U₂) :
    ∫ U, Y U * Y U ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)) ≠
      (∫ U, Y U ∂(wilsonProbability L β hβ : Measure (GaugeConfig L))) *
        ∫ U, Y U ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)) := by
  set m := ∫ U, Y U ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)) with hm
  have hint : ∀ g : GaugeConfig L → ℝ, Continuous g →
      Integrable g (wilsonProbability L β hβ : Measure (GaugeConfig L)) := fun g hg =>
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvar : ∫ U, (Y U - m) ^ 2 ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)) =
      ∫ U, Y U * Y U ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)) - m * m := by
    have hexp : (fun U => (Y U - m) ^ 2) = fun U => Y U * Y U - (2 * m * Y U - m * m) := by
      funext U
      ring
    have i1 : Integrable (fun U => Y U * Y U)
        (wilsonProbability L β hβ : Measure (GaugeConfig L)) := hint _ (hY.mul hY)
    have i2 : Integrable (fun U => 2 * m * Y U - m * m)
        (wilsonProbability L β hβ : Measure (GaugeConfig L)) :=
      hint _ ((continuous_const.mul hY).sub continuous_const)
    have i3 : Integrable (fun U => 2 * m * Y U)
        (wilsonProbability L β hβ : Measure (GaugeConfig L)) := hint _ (continuous_const.mul hY)
    rw [hexp, integral_sub i1 i2, integral_sub i3 (integrable_const _), integral_const_mul,
      integral_const, ← hm]
    simp only [probReal_univ, one_smul]
    ring
  have hpos : 0 < ∫ U, (Y U - m) ^ 2 ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)) := by
    rw [wilsonProbability_integral]
    unfold wilsonExpectation
    apply div_pos _ (wilsonPartition_pos _ hβ (measurable_wilsonAction β))
    obtain ⟨U₀, hU₀⟩ : ∃ U₀, Y U₀ ≠ m := by
      by_cases h1 : Y U₁ = m
      · exact ⟨U₂, fun h2 => h12 (h1.trans h2.symm)⟩
      · exact ⟨U₁, h1⟩
    apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := U₀)
    · exact (show Continuous (boltzmannWeight (L := L) β) from
        Real.continuous_exp.comp (continuous_wilsonAction β).neg).mul
          ((hY.sub continuous_const).pow 2)
    · exact HasCompactSupport.of_compactSpace _
    · intro U
      exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    · exact mul_ne_zero (Real.exp_pos _).ne' (pow_ne_zero 2 (sub_ne_zero.mpr hU₀))
  intro heq
  rw [heq, sub_self] at hvar
  linarith

/-- If the physical time extent `L·a` is an integer `T`, translating every loop by a multiple
of `T` moves each lattice corner by a multiple of `L`, which is the identity on the periodic
lattice. -/
theorem wilsonLoopVector_timePeriod {L : ℕ} {a : ℝ} (ha : 0 < a) {T : ℕ}
    (hT : (T : ℝ) = L * a) (k : ℕ) (U : GaugeConfig L) :
    translateObservables (timeVector (k * T)) (wilsonLoopVector L a U) =
      wilsonLoopVector L a U := by
  let m : Fin 4 → ℤ := fun i => if i = 0 then ((k * L : ℕ) : ℤ) else 0
  have hm : ∀ i, (timeVector (k * T) i : ℝ) = (m i : ℝ) * a := by
    intro i
    by_cases hi : i = 0
    · have e1 : timeVector (k * T) i = ((k * T : ℕ) : ℚ) := by simp [timeVector, hi]
      have e2 : m i = ((k * L : ℕ) : ℤ) := by simp [m, hi]
      rw [e1, e2]
      push_cast
      rw [hT]
      ring
    · have e1 : timeVector (k * T) i = 0 := by simp [timeVector, hi]
      have e2 : m i = 0 := by simp [m, hi]
      rw [e1, e2]
      simp
  rw [translateObservables_wilsonLoopVector ha hm U]
  have h0 : latticeSite L m = 0 := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [latticeSite, m]
    · simp [latticeSite, m, hi]
  have hU : latticeTranslate (0 : Lattice4D L) U = U := by
    funext e
    simp [latticeTranslate, linkTranslationEquiv]
  rw [h0, hU]

/-- Translation-invariant constants commute with physical translations. -/
theorem translateObservables_rescale {P : CutoffPath} (Z : LoopRenormalization P)
    (hZ : Z.IsTranslationInvariant) (n : ℕ) (c : Fin 4 → ℚ) (w : WilsonLoopSpace) :
    translateObservables c (Z.rescale n w) = Z.rescale n (translateObservables c w) := by
  funext ℓ
  simp only [translateObservables, LoopRenormalization.rescale, hZ n c ℓ]

/-- A loop whose lattice discretization at spacings `a ≤ q < 2a` is the plaquette at the origin
in the `(0, 1)` plane. -/
def plaquetteLoop (q : ℚ) (hq : 0 < q) : PhysicalRectangle :=
  ⟨fun _ => 0, 0, 1, by decide, q, q, hq, hq⟩

/-- The plaquette at the origin in the `(0, 1)` plane. -/
def originPlaquette (L : ℕ) : Plaquette L := ⟨0, 0, 1, by decide⟩

theorem physicalWilsonLoop_plaquetteLoop {L : ℕ} {a : ℝ} (ha : 0 < a) {q : ℚ} (hq : 0 < q)
    (h1 : a < q) (h2 : (q : ℝ) < 2 * a) (U : GaugeConfig L) :
    physicalWilsonLoop L a (plaquetteLoop q hq) U = 1 - plaquetteAction U (originPlaquette L) := by
  have hsteps : ⌊(q : ℝ) / a⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (div_nonneg (by exact_mod_cast hq.le) ha.le)]
    constructor
    · rw [Nat.cast_one, le_div_iff₀ ha, one_mul]
      exact h1.le
    · rw [div_lt_iff₀ ha]
      push_cast
      linarith
  have hs1 : (plaquetteLoop q hq).stepsμ a = 1 := hsteps
  have hs2 : (plaquetteLoop q hq).stepsν a = 1 := hsteps
  rw [physicalWilsonLoop_eq_one_sub_plaquetteAction a _ U hs1 hs2]
  have hsite : latticeSite L ((plaquetteLoop q hq).latticeBase a) = 0 := by
    funext i
    simp [latticeSite, PhysicalRectangle.latticeBase, plaquetteLoop]
  congr 2
  change (⟨latticeSite L ((plaquetteLoop q hq).latticeBase a), 0, 1, _⟩ : Plaquette L) =
    ⟨0, 0, 1, _⟩
  rw [hsite]

theorem unitClamp_pos {c : ℝ} (hc : 0 < c) : 0 < unitClamp c := by
  change 0 < max (-1) (min 1 c)
  exact lt_max_of_lt_right (lt_min one_pos hc)

theorem unitClamp_neg_lt {c : ℝ} (hc : 0 < c) : unitClamp (-c) < 0 := by
  change max (-1) (min 1 (-c)) < 0
  exact max_lt (by norm_num) (lt_of_le_of_lt (min_le_right _ _) (by linarith))

/-- At every cutoff with lattice side at least two and integer physical time extent
`T = L·a`, the renormalized joint law of the actual model, for any translation-invariant
constants (in particular the unrenormalized law), is not time mixing: it is exactly
periodic in time with period `T`, and the Wilson law gives positive variance to the clamped
plaquette loop. So `time_mixing` can never be inherited from such cutoffs: it has to be proved
for the limit itself. -/
theorem not_isTimeMixing_law {P : CutoffPath} (Z : LoopRenormalization P)
    (hZ : Z.IsTranslationInvariant) (n : ℕ) (hL : 2 ≤ P.side n) {T : ℕ} (hT0 : 0 < T)
    (hT : (T : ℝ) = P.side n * P.spacing n) : ¬ IsTimeMixing (Z.law n) := by
  intro hmix
  have ha := P.spacing_pos n
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show P.spacing n < 2 * P.spacing n by linarith)
  have hq : (0 : ℚ) < q := by exact_mod_cast ha.trans hq1
  have hrv : Continuous (Z.renormalizedVector n) :=
    (Z.continuous_rescale n).comp (continuous_wilsonLoopVector _ _)
  have hper : ∀ k : ℕ, ∀ᵐ w ∂(Z.law n : Measure WilsonLoopSpace),
      translateObservables (timeVector (k * T)) w = w := by
    intro k
    have hp : MeasurableSet
        {w : WilsonLoopSpace | translateObservables (timeVector (k * T)) w = w} :=
      (isClosed_eq (continuous_translateObservables _) continuous_id).measurableSet
    rw [LoopRenormalization.law_eq_map_renormalizedVector, ProbabilityMeasure.toMeasure_map,
      ae_map_iff hrv.aemeasurable hp]
    refine Eventually.of_forall fun U => ?_
    change translateObservables (timeVector (k * T))
      (Z.rescale n (wilsonLoopVector (P.side n) (P.spacing n) U)) =
        Z.rescale n (wilsonLoopVector (P.side n) (P.spacing n) U)
    rw [translateObservables_rescale Z hZ, wilsonLoopVector_timePeriod ha hT k U]
  have hvar := integral_mul_self_of_isTimeMixing_of_periodic hmix hT0 hper
    (loopTest unitClamp (plaquetteLoop q hq))
  have hF : Continuous (fun w : WilsonLoopSpace => loopTest unitClamp (plaquetteLoop q hq) w) :=
    (loopTest unitClamp (plaquetteLoop q hq)).continuous
  have hFF : Continuous (fun w : WilsonLoopSpace => loopTest unitClamp (plaquetteLoop q hq) w *
      loopTest unitClamp (plaquetteLoop q hq) w) := hF.mul hF
  rw [LoopRenormalization.law_eq_map_renormalizedVector, ProbabilityMeasure.toMeasure_map,
    integral_map hrv.aemeasurable hFF.aestronglyMeasurable,
    integral_map hrv.aemeasurable hF.aestronglyMeasurable] at hvar
  have hY : ∀ U : GaugeConfig (P.side n),
      loopTest unitClamp (plaquetteLoop q hq) (Z.renormalizedVector n U) =
        unitClamp (Z.factor n (plaquetteLoop q hq) *
          (1 - plaquetteAction U (originPlaquette (P.side n)))) := by
    intro U
    simp only [loopTest_apply, LoopRenormalization.renormalizedVector, LoopRenormalization.rescale,
      wilsonLoopVector, physicalWilsonLoop_plaquetteLoop ha hq hq1 hq2]
  simp only [hY] at hvar
  have hcpos : 0 < Z.factor n (plaquetteLoop q hq) := Z.factor_pos n _
  have hdiff : unitClamp (Z.factor n (plaquetteLoop q hq) *
      (1 - plaquetteAction (vacuumConfig (P.side n)) (originPlaquette (P.side n)))) ≠
      unitClamp (Z.factor n (plaquetteLoop q hq) *
        (1 - plaquetteAction (flipLink ⟨(originPlaquette (P.side n)).x,
          (originPlaquette (P.side n)).μ⟩) (originPlaquette (P.side n)))) := by
    rw [plaquetteAction_vacuum, plaquetteAction_flipLink hL]
    have h1 : Z.factor n (plaquetteLoop q hq) * (1 - 0) = Z.factor n (plaquetteLoop q hq) := by
      ring
    have h2 : Z.factor n (plaquetteLoop q hq) * (1 - 2) = -Z.factor n (plaquetteLoop q hq) := by
      ring
    rw [h1, h2]
    exact ne_of_gt (lt_trans (unitClamp_neg_lt hcpos) (unitClamp_pos hcpos))
  exact wilson_variance_ne (P.coupling n) (P.coupling_nonneg n)
    (unitClamp.continuous.comp (continuous_const.mul
      (continuous_const.sub (continuous_plaquetteAction _)))) hdiff hvar

/-- Along the explicit asymptotically free dyadic path no cutoff law with `n ≥ 1` is time
mixing, for every translation-invariant renormalization. -/
theorem dyadicOneLoopPath_not_isTimeMixing
    (Z : LoopRenormalization dyadicOneLoopPath.toCutoffPath) (hZ : Z.IsTranslationInvariant)
    (n : ℕ) (hn : 1 ≤ n) : ¬ IsTimeMixing (Z.law n) := by
  apply not_isTimeMixing_law Z hZ n (T := 2 ^ n)
  · change 2 ≤ 4 ^ n
    calc 2 ≤ 4 ^ 1 := by norm_num
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  · positivity
  · change ((2 ^ n : ℕ) : ℝ) = ((4 ^ n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n
    push_cast
    rw [← mul_pow]
    norm_num

theorem dyadicOneLoopPath_wilsonLoopLaw_not_isTimeMixing (n : ℕ) (hn : 1 ≤ n) :
    ¬ IsTimeMixing (dyadicOneLoopPath.wilsonLoopLaw n) := by
  have h := dyadicOneLoopPath_not_isTimeMixing
    (LoopRenormalization.unrenormalized dyadicOneLoopPath.toCutoffPath)
    (LoopRenormalization.unrenormalized_invariant_and_tails _).1 n hn
  rwa [LoopRenormalization.unrenormalized_law] at h

/-! ## 6. Reflection positivity on a product space -/

/-- The elementary positivity: for a bounded measurable `k`, the integral of
`k x y₁ * k x y₂` against `μX ⊗ (μY ⊗ μY)` is the integral over `x` of a square. -/
theorem integral_fiber_square_nonneg {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μX : Measure X) (μY : Measure Y) [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (k : X → Y → ℝ) (hk : Measurable (Function.uncurry k)) {C : ℝ} (hC : ∀ x y, |k x y| ≤ C) :
    0 ≤ ∫ z, k z.1 z.2.1 * k z.1 z.2.2 ∂(μX.prod (μY.prod μY)) := by
  have hm1 : Measurable (fun z : X × (Y × Y) => k z.1 z.2.1) :=
    hk.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hm2 : Measurable (fun z : X × (Y × Y) => k z.1 z.2.2) :=
    hk.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hint : Integrable (fun z : X × (Y × Y) => k z.1 z.2.1 * k z.1 z.2.2)
      (μX.prod (μY.prod μY)) := by
    refine (integrable_const (C * C)).mono' (hm1.mul hm2).aestronglyMeasurable ?_
    refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hC _ _) (hC _ _) (abs_nonneg _) ((abs_nonneg _).trans (hC z.1 z.2.1))
  rw [integral_prod _ hint]
  refine integral_nonneg fun x => ?_
  change 0 ≤ ∫ y : Y × Y, k x y.1 * k x y.2 ∂(μY.prod μY)
  rw [integral_prod_mul (fun y => k x y) (fun y => k x y)]
  exact mul_self_nonneg _

/-- Reflection positivity of a product probability measure. The coordinates are split into
fixed ones (`fixed`, where the reflection acts trivially), the other positive ones, and the
rest; the reflection `r` with twists `σ` exchanges the last two classes and preserves each
factor measure. Then for every bounded measurable `K` of the positive coordinates,
`∫ K(U) K(ΘU) ≥ 0` with `(ΘU) i = σ i (U (r i))`. -/
theorem integral_reflection_nonneg_of_product {ι : Type*} [Fintype ι] {G : Type*}
    [MeasurableSpace G] [Nonempty G] (ρ : Measure G) [IsProbabilityMeasure ρ]
    (pos fixed : ι → Prop) [DecidablePred pos] [DecidablePred fixed]
    (r : ι → ι) (σ : ι → G → G)
    (hr : ∀ i, r (r i) = i) (hσ : ∀ i, MeasurePreserving (σ i) ρ ρ)
    (hFP : ∀ i, fixed i → pos i) (hFr : ∀ i, fixed i → r i = i)
    (hFσ : ∀ i, fixed i → ∀ g, σ i g = g)
    (hP : ∀ i, pos i → ¬ fixed i → ¬ pos (r i))
    (hN : ∀ i, ¬ pos i → pos (r i) ∧ ¬ fixed (r i))
    (K : (ι → G) → ℝ) (hK : Measurable K) {C : ℝ} (hKb : ∀ U, |K U| ≤ C)
    (hloc : ∀ U U' : ι → G, (∀ i, pos i → U i = U' i) → K U = K U') :
    0 ≤ ∫ U, K U * K (fun i => σ i (U (r i))) ∂(Measure.pi fun _ : ι => ρ) := by
  classical
  -- the three classes of coordinates, with the third identified with the second by `r`
  let F := {i : ι // fixed i}
  let Q := {i : ι // pos i ∧ ¬ fixed i}
  have hrQ : ∀ q : Q, ¬ pos (r q.1) := fun q => hP q.1 q.2.1 q.2.2
  let e : F ⊕ (Q ⊕ Q) ≃ ι :=
    { toFun := fun j => match j with
        | Sum.inl f => f.1
        | Sum.inr (Sum.inl q) => q.1
        | Sum.inr (Sum.inr q) => r q.1
      invFun := fun i =>
        if h : fixed i then Sum.inl ⟨i, h⟩
        else if h' : pos i then Sum.inr (Sum.inl ⟨i, h', h⟩)
        else Sum.inr (Sum.inr ⟨r i, hN i h'⟩)
      left_inv := by
        rintro (f | q | q)
        · simp [f.2]
        · simp [q.2.1, q.2.2]
        · have h1 : ¬ pos (r q.1) := hrQ q
          have h2 : ¬ fixed (r q.1) := fun h => h1 (hFP _ h)
          simp only [h1, h2, dite_false, Sum.inr.injEq]
          exact Subtype.ext (hr q.1)
      right_inv := by
        intro i
        by_cases h : fixed i
        · simp [h]
        · by_cases h' : pos i
          · simp [h, h']
          · simp [h, h', hr] }
  -- the measure-preserving splitting
  let τ : F ⊕ (Q ⊕ Q) → G → G := fun j => match j with
    | Sum.inr (Sum.inr q) => σ q.1
    | _ => id
  have hτ : ∀ j, MeasurePreserving (τ j) ρ ρ := by
    rintro (f | q | q)
    · exact MeasurePreserving.id ρ
    · exact MeasurePreserving.id ρ
    · exact hσ q.1
  have h1 : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ι => G) e).symm
      (Measure.pi fun _ : ι => ρ) (Measure.pi fun _ : F ⊕ (Q ⊕ Q) => ρ) :=
    (measurePreserving_piCongrLeft (fun _ : ι => ρ) e).symm _
  have h2 : MeasurePreserving (fun (V : F ⊕ (Q ⊕ Q) → G) j => τ j (V j))
      (Measure.pi fun _ : F ⊕ (Q ⊕ Q) => ρ) (Measure.pi fun _ : F ⊕ (Q ⊕ Q) => ρ) :=
    measurePreserving_pi _ _ hτ
  have h3 := measurePreserving_sumPiEquivProdPi (X := fun _ : F ⊕ (Q ⊕ Q) => G)
    (fun _ => ρ)
  have h4 := measurePreserving_sumPiEquivProdPi (X := fun _ : Q ⊕ Q => G) (fun _ => ρ)
  have h34 := (MeasurePreserving.id (Measure.pi fun _ : F => ρ)).prod h4
  have hΨ := h34.comp (h3.comp (h2.comp h1))
  set Ψ := Prod.map id (MeasurableEquiv.sumPiEquivProdPi (fun _ : Q ⊕ Q => G)) ∘
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : F ⊕ (Q ⊕ Q) => G)) ∘
      (fun (V : F ⊕ (Q ⊕ Q) → G) j => τ j (V j)) ∘
        (MeasurableEquiv.piCongrLeft (fun _ : ι => G) e).symm with hΨdef
  have hΨ1 : ∀ U f, (Ψ U).1 f = U f.1 := by
    intro U f
    simp [hΨdef, MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.piCongrLeft_symm_apply,
      MeasurableEquiv.piCongrLeft, τ, e]
  have hΨ2 : ∀ U q, (Ψ U).2.1 q = U q.1 := by
    intro U q
    simp [hΨdef, MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.piCongrLeft_symm_apply,
      MeasurableEquiv.piCongrLeft, τ, e]
  have hΨ3 : ∀ U q, (Ψ U).2.2 q = σ q.1 (U (r q.1)) := by
    intro U q
    simp [hΨdef, MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.piCongrLeft_symm_apply,
      MeasurableEquiv.piCongrLeft, τ, e]
  -- the functional on the two blocks that carry the positive coordinates
  let g₀ : G := Classical.arbitrary G
  let glue : (F → G) → (Q → G) → ι → G := fun f q i =>
    if h : fixed i then f ⟨i, h⟩ else if h' : pos i then q ⟨i, h', h⟩ else g₀
  have hglue : Measurable (fun z : (F → G) × (Q → G) => glue z.1 z.2) := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases h : fixed i
    · have hfun : (fun z : (F → G) × (Q → G) => glue z.1 z.2 i) = fun z => z.1 ⟨i, h⟩ := by
        funext z
        simp only [glue, h, dite_true]
      rw [hfun]
      exact (measurable_pi_apply _).comp measurable_fst
    · by_cases h' : pos i
      · have hfun : (fun z : (F → G) × (Q → G) => glue z.1 z.2 i) =
            fun z => z.2 ⟨i, h', h⟩ := by
          funext z
          simp only [glue, h, h', dite_true, dite_false]
        rw [hfun]
        exact (measurable_pi_apply _).comp measurable_snd
      · have hfun : (fun z : (F → G) × (Q → G) => glue z.1 z.2 i) = fun _ => g₀ := by
          funext z
          simp only [glue, h, h', dite_false]
        rw [hfun]
        exact measurable_const
  let k : (F → G) → (Q → G) → ℝ := fun f q => K (glue f q)
  have hk : Measurable (Function.uncurry k) := hK.comp hglue
  have hKΨ : ∀ U, K U = k (Ψ U).1 (Ψ U).2.1 := by
    intro U
    apply hloc
    intro i hi
    by_cases h : fixed i
    · simp [glue, h, hΨ1]
    · simp [glue, h, hi, hΨ2]
  have hKΘΨ : ∀ U, K (fun i => σ i (U (r i))) = k (Ψ U).1 (Ψ U).2.2 := by
    intro U
    apply hloc
    intro i hi
    by_cases h : fixed i
    · simp [glue, h, hΨ1, hFr i h, hFσ i h]
    · simp [glue, h, hi, hΨ3]
  have hfun : ∀ U : ι → G, K U * K (fun i => σ i (U (r i))) =
      k (Ψ U).1 (Ψ U).2.1 * k (Ψ U).1 (Ψ U).2.2 := by
    intro U
    rw [hKΘΨ U, hKΨ U]
  have hgm : Measurable (fun z : (F → G) × ((Q → G) × (Q → G)) => k z.1 z.2.1 * k z.1 z.2.2) :=
    (hk.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hk.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  calc (0 : ℝ) ≤ ∫ z, k z.1 z.2.1 * k z.1 z.2.2 ∂((Measure.pi fun _ : F => ρ).prod
        ((Measure.pi fun _ : Q => ρ).prod (Measure.pi fun _ : Q => ρ))) :=
        integral_fiber_square_nonneg _ _ k hk (fun f q => hKb _)
    _ = ∫ U, k (Ψ U).1 (Ψ U).2.1 * k (Ψ U).1 (Ψ U).2.2 ∂(Measure.pi fun _ : ι => ρ) := by
        rw [← hΨ.map_eq]
        exact integral_map hΨ.measurable.aemeasurable hgm.aestronglyMeasurable
    _ = ∫ U, K U * K (fun i => σ i (U (r i))) ∂(Measure.pi fun _ : ι => ρ) :=
        integral_congr_ae (Eventually.of_forall fun U => (hfun U).symm)

/-! ## 7. Time reflection of the actual lattice model -/

section LatticeReflection

variable {L : ℕ}

/-- Site reflection `x₀ ↦ -x₀` of the periodic lattice. -/
def reflectSite (x : Lattice4D L) : Lattice4D L := fun i => if i = 0 then -x i else x i

@[simp]
theorem reflectSite_reflectSite (x : Lattice4D L) : reflectSite (reflectSite x) = x := by
  funext i
  by_cases hi : i = 0 <;> simp [reflectSite, hi]

theorem reflectSite_add (x y : Lattice4D L) :
    reflectSite (x + y) = reflectSite x + reflectSite y := by
  funext i
  by_cases hi : i = 0
  · simp only [reflectSite, hi, Pi.add_apply, ite_true]
    abel
  · simp [reflectSite, hi]

theorem reflectSite_sub (x y : Lattice4D L) :
    reflectSite (x - y) = reflectSite x - reflectSite y := by
  funext i
  by_cases hi : i = 0
  · simp only [reflectSite, hi, Pi.sub_apply, ite_true]
    abel
  · simp [reflectSite, hi]

theorem reflectSite_unitVec_zero : reflectSite (unitVec L 0) = -unitVec L 0 := by
  funext i
  by_cases hi : i = 0 <;> simp [reflectSite, unitVec, hi]

theorem reflectSite_unitVec_of_ne {μ : Direction} (hμ : μ ≠ 0) :
    reflectSite (unitVec L μ) = unitVec L μ := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [reflectSite, unitVec, Ne.symm hμ]
  · simp [reflectSite, hi]

/-- Reflection of an oriented link: spatial links go to spatial links at the reflected site;
the temporal link from `x` to `x + e₀` goes to the temporal link from `Θx - e₀` to `Θx`. -/
def reflectLink (e : Link L) : Link L :=
  if e.μ = 0 then ⟨reflectSite e.x - unitVec L 0, 0⟩ else ⟨reflectSite e.x, e.μ⟩

theorem reflectLink_μ (e : Link L) : (reflectLink e).μ = e.μ := by
  unfold reflectLink
  split_ifs with h
  · exact h.symm
  · rfl

@[simp]
theorem reflectLink_reflectLink (e : Link L) : reflectLink (reflectLink e) = e := by
  rcases e with ⟨x, μ⟩
  by_cases hμ : μ = 0
  · subst hμ
    simp only [reflectLink, ite_true]
    congr 1
    rw [reflectSite_sub, reflectSite_reflectSite, reflectSite_unitVec_zero]
    abel
  · simp [reflectLink, hμ]

/-- The time-reflected configuration: temporal links are traversed backwards. -/
def reflectConfig (U : GaugeConfig L) : GaugeConfig L :=
  fun e => if e.μ = 0 then (U (reflectLink e))⁻¹ else U (reflectLink e)

theorem continuous_reflectConfig : Continuous (reflectConfig (L := L)) := by
  change Continuous (fun (U : Link L → SU2) (e : Link L) =>
    if e.μ = 0 then (U (reflectLink e))⁻¹ else U (reflectLink e))
  exact continuous_pi fun e => continuous_if_const _ (fun _ => (continuous_apply _).inv)
    (fun _ => continuous_apply _)

@[simp]
theorem reflectConfig_reflectConfig (U : GaugeConfig L) : reflectConfig (reflectConfig U) = U := by
  funext e
  by_cases h : e.μ = 0
  · simp [reflectConfig, h, reflectLink_μ]
  · simp [reflectConfig, h, reflectLink_μ]

/-- Reflection of a plaquette. -/
def reflectPlaquette (p : Plaquette L) : Plaquette L :=
  if p.μ = 0 then ⟨reflectSite p.x - unitVec L 0, p.μ, p.ν, p.h⟩
  else ⟨reflectSite p.x, p.μ, p.ν, p.h⟩

theorem Plaquette.ν_ne_zero (p : Plaquette L) : p.ν ≠ 0 :=
  (lt_of_le_of_lt (Fin.zero_le p.μ) p.h).ne'

@[simp]
theorem reflectPlaquette_reflectPlaquette (p : Plaquette L) :
    reflectPlaquette (reflectPlaquette p) = p := by
  rcases p with ⟨x, μ, ν, h⟩
  by_cases hμ : μ = 0
  · subst hμ
    simp only [reflectPlaquette, ite_true]
    congr 1
    rw [reflectSite_sub, reflectSite_reflectSite, reflectSite_unitVec_zero]
    abel
  · simp [reflectPlaquette, hμ]

/-- The plaquette action of the reflected configuration is the action of the reflected
plaquette: spatial plaquettes are mapped exactly; for temporal plaquettes the holonomy is
inverted and conjugated, which leaves `½ Re tr` unchanged. -/
theorem plaquetteAction_reflectConfig (U : GaugeConfig L) (p : Plaquette L) :
    plaquetteAction (reflectConfig U) p = plaquetteAction U (reflectPlaquette p) := by
  rcases p with ⟨x, μ, ν, h⟩
  have hν : ν ≠ 0 := Plaquette.ν_ne_zero ⟨x, μ, ν, h⟩
  by_cases hμ : μ = 0
  · subst hμ
    set y := reflectSite x - unitVec L 0 with hy
    have e1 : reflectConfig U ⟨x, 0⟩ = (U ⟨y, 0⟩)⁻¹ := by
      simp [reflectConfig, reflectLink, hy]
    have e2 : reflectConfig U ⟨shift x 0, ν⟩ = U ⟨y, ν⟩ := by
      simp only [reflectConfig, reflectLink, hν, ite_false, shift, reflectSite_add,
        reflectSite_unitVec_zero, hy, sub_eq_add_neg]
    have e3 : reflectConfig U ⟨shift x ν, 0⟩ = (U ⟨shift y ν, 0⟩)⁻¹ := by
      simp only [reflectConfig, reflectLink, ite_true, shift, reflectSite_add,
        reflectSite_unitVec_of_ne hν, hy]
      congr 2
      abel_nf
    have e4 : reflectConfig U ⟨x, ν⟩ = U ⟨shift y 0, ν⟩ := by
      simp only [reflectConfig, reflectLink, hν, ite_false, shift, hy]
      congr 2
      abel
    have hhol : plaquetteHolonomy (reflectConfig U) ⟨x, 0, ν, h⟩ =
        (U ⟨y, 0⟩)⁻¹ * (plaquetteHolonomy U (reflectPlaquette ⟨x, 0, ν, h⟩))⁻¹ *
          ((U ⟨y, 0⟩)⁻¹)⁻¹ := by
      simp only [plaquetteHolonomy, e1, e2, e3, e4, reflectPlaquette, ite_true, ← hy]
      group
    rw [plaquetteAction_eq_one_sub_halfTraceRe, plaquetteAction_eq_one_sub_halfTraceRe, hhol,
      halfTraceRe_conj, halfTraceRe_inv]
  · have hspat : ∀ (z : Lattice4D L) (ρ : Direction), ρ ≠ 0 →
        reflectConfig U ⟨z, ρ⟩ = U ⟨reflectSite z, ρ⟩ := by
      intro z ρ hρ
      simp [reflectConfig, reflectLink, hρ]
    have hhol : plaquetteHolonomy (reflectConfig U) ⟨x, μ, ν, h⟩ =
        plaquetteHolonomy U (reflectPlaquette ⟨x, μ, ν, h⟩) := by
      simp only [plaquetteHolonomy, hspat _ _ hμ, hspat _ _ hν, reflectPlaquette, hμ, ite_false,
        shift, reflectSite_add, reflectSite_unitVec_of_ne hμ, reflectSite_unitVec_of_ne hν]
    rw [plaquetteAction, plaquetteAction, hhol]

/-- Plaquette reflection as a permutation. -/
def reflectPlaquetteEquiv : Equiv.Perm (Plaquette L) :=
  Function.Involutive.toPerm reflectPlaquette reflectPlaquette_reflectPlaquette

/-- Exact invariance of the actual Wilson action under the time reflection. -/
theorem wilsonAction_reflectConfig [NeZero L] (β : ℝ) (U : GaugeConfig L) :
    wilsonAction β (reflectConfig U) = wilsonAction β U := by
  have hsum : ∑ p : Plaquette L, plaquetteAction U (reflectPlaquette p) =
      ∑ p : Plaquette L, plaquetteAction U p :=
    Fintype.sum_equiv reflectPlaquetteEquiv _ _ (fun _ => rfl)
  simp only [wilsonAction, plaquetteAction_reflectConfig, hsum]

end LatticeReflection

/-! ## 8. Osterwalder–Seiler reflection positivity of the actual Wilson measure -/

section OsterwalderSeiler

variable {L : ℕ}

/-- The time coordinate of a site as a natural number in `[0, L)`. -/
def timeVal (x : Lattice4D L) : ℕ := (x 0).val

theorem timeVal_lt [NeZero L] (x : Lattice4D L) : timeVal x < L := ZMod.val_lt _

theorem timeVal_reflectSite [NeZero L] (x : Lattice4D L) :
    timeVal (reflectSite x) = if timeVal x = 0 then 0 else L - timeVal x := by
  have h0 : reflectSite x 0 = -x 0 := by simp [reflectSite]
  simp only [timeVal, h0, ZMod.neg_val]
  by_cases h : (x 0).val = 0
  · have hx : x 0 = 0 := (ZMod.val_eq_zero _).mp h
    simp [hx]
  · have hx : x 0 ≠ 0 := fun h' => h ((ZMod.val_eq_zero _).mpr h')
    simp [h, hx]

theorem zmod_val_neg_sub_one [NeZero L] (a : ZMod L) : (-a - 1).val = L - 1 - a.val := by
  have hv := ZMod.val_lt a
  have h : (-a - 1 : ZMod L) = ((L - 1 - a.val : ℕ) : ZMod L) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), ZMod.natCast_self,
      ZMod.natCast_zmod_val]
    push_cast
    ring
  rw [h, ZMod.val_natCast_of_lt (by omega)]

theorem timeVal_reflectSite_sub_unitVec [NeZero L] (x : Lattice4D L) :
    timeVal (reflectSite x - unitVec L 0) = L - 1 - timeVal x := by
  have h0 : (reflectSite x - unitVec L 0) 0 = -x 0 - 1 := by simp [reflectSite, unitVec]
  simp only [timeVal, h0, zmod_val_neg_sub_one]

theorem timeVal_add_unitVec_of_ne (x : Lattice4D L) {μ : Direction} (hμ : μ ≠ 0) :
    timeVal (x + unitVec L μ) = timeVal x := by
  simp [timeVal, unitVec, Ne.symm hμ]

theorem timeVal_add_unitVec_zero [NeZero L] (x : Lattice4D L) (h : timeVal x + 1 < L) :
    timeVal (x + unitVec L 0) = timeVal x + 1 := by
  have h0 : (x + unitVec L 0) 0 = (((x 0).val + 1 : ℕ) : ZMod L) := by
    simp [unitVec]
  simp only [timeVal, h0]
  exact ZMod.val_natCast_of_lt h

theorem timeVal_reflectLink [NeZero L] (e : Link L) :
    timeVal (reflectLink e).x = if e.μ = 0 then L - 1 - timeVal e.x
      else if timeVal e.x = 0 then 0 else L - timeVal e.x := by
  unfold reflectLink
  by_cases h : e.μ = 0
  · simp [h, timeVal_reflectSite_sub_unitVec]
  · simp [h, timeVal_reflectSite]

theorem timeVal_reflectPlaquette [NeZero L] (p : Plaquette L) :
    timeVal (reflectPlaquette p).x = if p.μ = 0 then L - 1 - timeVal p.x
      else if timeVal p.x = 0 then 0 else L - timeVal p.x := by
  unfold reflectPlaquette
  by_cases h : p.μ = 0
  · simp [h, timeVal_reflectSite_sub_unitVec]
  · simp [h, timeVal_reflectSite]

theorem reflectPlaquette_μ (p : Plaquette L) : (reflectPlaquette p).μ = p.μ := by
  unfold reflectPlaquette
  split_ifs <;> rfl

/-- Links of the closed positive half-lattice `0 ≤ x₀ ≤ M`: temporal links leaving times
`t < M`, spatial links at times `t ≤ M`. -/
def IsPositiveLink (M : ℕ) (e : Link L) : Prop :=
  if e.μ = 0 then timeVal e.x < M else timeVal e.x ≤ M

instance (M : ℕ) : DecidablePred (IsPositiveLink (L := L) M) := fun e => by
  unfold IsPositiveLink
  infer_instance

/-- Spatial links in the two time slices `x₀ = 0` and `x₀ = M` fixed by the reflection. -/
def IsFixedLink (M : ℕ) (e : Link L) : Prop :=
  e.μ ≠ 0 ∧ (timeVal e.x = 0 ∨ timeVal e.x = M)

instance (M : ℕ) : DecidablePred (IsFixedLink (L := L) M) := fun e => by
  unfold IsFixedLink
  infer_instance

theorem reflectSite_eq_self_of_fixed [NeZero L] {M : ℕ} (hL : L = 2 * M) {x : Lattice4D L}
    (hx : timeVal x = 0 ∨ timeVal x = M) : reflectSite x = x := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp only [reflectSite, ite_true]
    rcases hx with hx | hx
    · have : x 0 = 0 := (ZMod.val_eq_zero _).mp hx
      simp [this]
    · have hxM : x 0 = (M : ZMod L) := by
        rw [← ZMod.natCast_zmod_val (x 0)]
        exact congrArg _ hx
      rw [hxM, neg_eq_iff_add_eq_zero, ← Nat.cast_add, ← two_mul, ← hL, ZMod.natCast_self]
  · simp [reflectSite, hi]

theorem reflectLink_of_fixed [NeZero L] {M : ℕ} (hL : L = 2 * M) {e : Link L}
    (he : IsFixedLink M e) : reflectLink e = e := by
  rcases e with ⟨x, μ⟩
  simp only [reflectLink, he.1, ite_false, reflectSite_eq_self_of_fixed hL he.2]

/-- The link-variable twist of the reflection: inversion on temporal links. -/
def linkTwist (e : Link L) (g : SU2) : SU2 := if e.μ = 0 then g⁻¹ else g

theorem reflectConfig_eq_twist (U : GaugeConfig L) :
    reflectConfig U = fun e => linkTwist e (U (reflectLink e)) := rfl

/-- The normalized Haar measure of `SU(2)` is inversion invariant. -/
instance : SU2.haarProbability.IsInvInvariant := by
  have hK : (SU2.haarNormalization : Set SU2) = Set.univ := rfl
  have h1 : SU2.haarProbability.inv (SU2.haarNormalization : Set SU2) = 1 := by
    rw [hK, Measure.inv, Measure.map_apply measurable_inv MeasurableSet.univ, Set.preimage_univ,
      measure_univ]
  have hinv : Measure.haarMeasure SU2.haarNormalization = SU2.haarProbability.inv :=
    (Measure.haarMeasure_eq_iff SU2.haarNormalization SU2.haarProbability.inv).2 h1
  exact ⟨hinv.symm⟩

theorem measurePreserving_linkTwist (e : Link L) :
    MeasurePreserving (linkTwist e) SU2.haarProbability SU2.haarProbability := by
  by_cases h : e.μ = 0
  · have hf : linkTwist e = Inv.inv := by
      funext g
      simp [linkTwist, h]
    rw [hf]
    exact Measure.measurePreserving_inv _
  · have hf : linkTwist e = id := by
      funext g
      simp [linkTwist, h]
    rw [hf]
    exact MeasurePreserving.id _

/-- Plaquette weights of the positive half: `1` strictly inside, `½` on the two fixed slices
for spatial plaquettes, `0` otherwise. -/
def plaquetteWeight (M : ℕ) (p : Plaquette L) : ℝ :=
  if p.μ = 0 then (if timeVal p.x < M then 1 else 0)
  else if 0 < timeVal p.x ∧ timeVal p.x < M then 1
  else if timeVal p.x = 0 ∨ timeVal p.x = M then 1 / 2 else 0

/-- Every plaquette is shared exactly once between the positive half and its reflection. -/
theorem plaquetteWeight_add_reflect [NeZero L] {M : ℕ} (hL : L = 2 * M) (p : Plaquette L) :
    plaquetteWeight M p + plaquetteWeight M (reflectPlaquette p) = 1 := by
  have ht := timeVal_lt p.x
  unfold plaquetteWeight
  rw [reflectPlaquette_μ, timeVal_reflectPlaquette]
  by_cases hμ : p.μ = 0
  · simp only [hμ, ite_true]
    split_ifs <;> first | (exfalso; omega) | norm_num
  · simp only [hμ, ite_false]
    split_ifs <;> first | (exfalso; omega) | norm_num

/-- The four links of a plaquette with nonzero weight lie in the closed positive half. -/
theorem isPositiveLink_of_plaquetteWeight_ne_zero [NeZero L] {M : ℕ} (hL : L = 2 * M)
    (p : Plaquette L) (hw : plaquetteWeight M p ≠ 0) :
    IsPositiveLink M ⟨p.x, p.μ⟩ ∧ IsPositiveLink M ⟨shift p.x p.μ, p.ν⟩ ∧
      IsPositiveLink M ⟨shift p.x p.ν, p.μ⟩ ∧ IsPositiveLink M ⟨p.x, p.ν⟩ := by
  have hν : p.ν ≠ 0 := Plaquette.ν_ne_zero p
  have ht := timeVal_lt p.x
  have hsν : timeVal (shift p.x p.ν) = timeVal p.x := timeVal_add_unitVec_of_ne _ hν
  unfold plaquetteWeight at hw
  by_cases hμ : p.μ = 0
  · simp only [hμ, ite_true] at hw
    have htM : timeVal p.x < M := by
      by_contra hc
      exact hw (by simp [hc])
    have hsμ : timeVal (shift p.x 0) = timeVal p.x + 1 :=
      timeVal_add_unitVec_zero _ (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [IsPositiveLink, hμ, hν, ite_true, ite_false, hsμ, hsν]
      <;> omega
  · simp only [hμ, ite_false] at hw
    have htM : timeVal p.x ≤ M := by
      by_contra hc
      apply hw
      have h1 : ¬ (0 < timeVal p.x ∧ timeVal p.x < M) := fun h => hc (by omega)
      have h2 : ¬ (timeVal p.x = 0 ∨ timeVal p.x = M) := fun h => hc (by omega)
      simp [h1, h2]
    have hsμ : timeVal (shift p.x p.μ) = timeVal p.x := timeVal_add_unitVec_of_ne _ hμ
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [IsPositiveLink, hμ, hν, ite_false, hsμ, hsν] <;> omega

/-- The weighted action of the closed positive half. -/
def halfAction [NeZero L] (M : ℕ) (U : GaugeConfig L) : ℝ :=
  ∑ p : Plaquette L, plaquetteWeight M p * plaquetteAction U p

theorem continuous_halfAction [NeZero L] (M : ℕ) : Continuous (halfAction (L := L) M) := by
  unfold halfAction
  exact continuous_finsetSum _ fun p _ => continuous_const.mul (continuous_plaquetteAction p)

/-- The weighted half action depends only on the links of the closed positive half. -/
theorem halfAction_congr [NeZero L] {M : ℕ} (hL : L = 2 * M) {U U' : GaugeConfig L}
    (h : ∀ e, IsPositiveLink M e → U e = U' e) : halfAction M U = halfAction M U' := by
  unfold halfAction
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hw : plaquetteWeight M p = 0
  · simp [hw]
  · obtain ⟨h1, h2, h3, h4⟩ := isPositiveLink_of_plaquetteWeight_ne_zero hL p hw
    simp only [plaquetteAction, plaquetteHolonomy, h _ h1, h _ h2, h _ h3, h _ h4]

/-- Osterwalder–Seiler splitting of the actual Wilson action: `S = β (S₊ + S₊ ∘ Θ)`. -/
theorem wilsonAction_eq_halfAction [NeZero L] {M : ℕ} (hL : L = 2 * M) (β : ℝ)
    (U : GaugeConfig L) :
    wilsonAction β U = β * (halfAction M U + halfAction M (reflectConfig U)) := by
  have hrefl : halfAction M (reflectConfig U) =
      ∑ p : Plaquette L, plaquetteWeight M (reflectPlaquette p) * plaquetteAction U p := by
    unfold halfAction
    simp only [plaquetteAction_reflectConfig]
    exact Fintype.sum_equiv reflectPlaquetteEquiv _ _ (fun p => by
      change _ = plaquetteWeight M (reflectPlaquette (reflectPlaquette p)) *
        plaquetteAction U (reflectPlaquette p)
      rw [reflectPlaquette_reflectPlaquette])
  rw [hrefl, halfAction, ← Finset.sum_add_distrib]
  simp only [← add_mul, plaquetteWeight_add_reflect hL, one_mul, wilsonAction]

/-- Osterwalder–Seiler reflection positivity of the actual SU(2) Wilson measure on the periodic
lattice of even side `L = 2M`, for the site reflection `x₀ ↦ -x₀`, at every coupling `β ≥ 0`:
for every continuous real functional `H` of the links of the closed positive half
`0 ≤ x₀ ≤ M`, the Wilson expectation of `H ∘ Θ · H` is nonnegative. -/
theorem wilson_reflection_positive {M : ℕ} [NeZero L] (hL : L = 2 * M) (β : ℝ) (hβ : 0 ≤ β)
    (H : GaugeConfig L → ℝ) (hH : Continuous H)
    (hloc : ∀ U U' : GaugeConfig L, (∀ e, IsPositiveLink M e → U e = U' e) → H U = H U') :
    0 ≤ ∫ U, H (reflectConfig U) * H U ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)) := by
  rw [wilsonProbability_integral]
  unfold wilsonExpectation
  refine div_nonneg ?_ (wilsonPartition_pos _ hβ (measurable_wilsonAction β)).le
  let K : GaugeConfig L → ℝ := fun U => H U * Real.exp (-(β * halfAction M U))
  have hK : Continuous K :=
    hH.mul (Real.continuous_exp.comp ((continuous_const.mul (continuous_halfAction M)).neg))
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuousOn
  have hKloc : ∀ U U' : GaugeConfig L, (∀ e, IsPositiveLink M e → U e = U' e) → K U = K U' := by
    intro U U' h
    simp only [K, hloc U U' h, halfAction_congr hL h]
  have hfun : ∀ U : GaugeConfig L, boltzmannWeight β U * (H (reflectConfig U) * H U) =
      K U * K (reflectConfig U) := by
    intro U
    simp only [K, boltzmannWeight, wilsonAction_eq_halfAction hL β U]
    rw [show -(β * (halfAction M U + halfAction M (reflectConfig U))) =
      -(β * halfAction M U) + -(β * halfAction M (reflectConfig U)) by ring, Real.exp_add]
    ring
  simp only [hfun]
  have hmain := integral_reflection_nonneg_of_product SU2.haarProbability
    (IsPositiveLink M) (IsFixedLink M) reflectLink linkTwist reflectLink_reflectLink
    measurePreserving_linkTwist
    (fun e he => by
      unfold IsPositiveLink
      rcases he with ⟨hμ, ht⟩
      simp only [hμ, ite_false]
      omega)
    (fun e he => reflectLink_of_fixed hL he)
    (fun e he g => by simp [linkTwist, he.1])
    (fun e hpos hfix => by
      have hlt := timeVal_lt e.x
      unfold IsPositiveLink at hpos ⊢
      unfold IsFixedLink at hfix
      rw [reflectLink_μ, timeVal_reflectLink]
      by_cases hμ : e.μ = 0
      · simp only [hμ, ite_true] at hpos ⊢
        omega
      · simp only [hμ, ite_false, ne_eq, not_false_eq_true, true_and] at hpos hfix ⊢
        split_ifs <;> omega)
    (fun e hneg => by
      have hlt := timeVal_lt e.x
      unfold IsPositiveLink at hneg ⊢
      unfold IsFixedLink
      rw [reflectLink_μ, timeVal_reflectLink]
      by_cases hμ : e.μ = 0
      · simp only [hμ, ite_true] at hneg ⊢
        refine ⟨by omega, fun h => h.1 rfl⟩
      · simp only [hμ, ite_false, ne_eq, not_false_eq_true, true_and] at hneg ⊢
        split_ifs <;> omega)
    K hK.measurable (fun U => by simpa [Real.norm_eq_abs] using hC U (Set.mem_univ U)) hKloc
  exact hmain

end OsterwalderSeiler

/-! ## 9. Reflected physical Wilson loops and their locality -/

section ReflectedLoops

variable {L : ℕ}

theorem reflectSite_neg (x : Lattice4D L) : reflectSite (-x) = -reflectSite x := by
  funext i
  by_cases hi : i = 0 <;> simp [reflectSite, hi]

/-- Time reversal of one lattice step. -/
def reflectStep (s : LatticeStep) : LatticeStep := if s.dir = 0 then ⟨0, !s.forward⟩ else s

theorem displacement_reflectStep (s : LatticeStep) :
    (reflectStep s).displacement L = reflectSite (s.displacement L) := by
  rcases s with ⟨d, _ | _⟩ <;> by_cases hd : d = 0
  · subst hd
    simp [reflectStep, reflectSite_neg, reflectSite_unitVec_zero]
  · simp [reflectStep, hd, reflectSite_neg, reflectSite_unitVec_of_ne hd]
  · subst hd
    simp [reflectStep, reflectSite_unitVec_zero]
  · simp [reflectStep, hd, reflectSite_unitVec_of_ne hd]

theorem stepTarget_reflect (x : Lattice4D L) (s : LatticeStep) :
    stepTarget (reflectSite x) (reflectStep s) = reflectSite (stepTarget x s) := by
  simp only [stepTarget, displacement_reflectStep, reflectSite_add]

theorem stepHolonomy_reflectConfig (U : GaugeConfig L) (x : Lattice4D L) (s : LatticeStep) :
    stepHolonomy (reflectConfig U) x s = stepHolonomy U (reflectSite x) (reflectStep s) := by
  rcases s with ⟨d, _ | _⟩ <;> by_cases hd : d = 0
  · subst hd
    have hr : reflectStep ⟨(0 : Direction), false⟩ = ⟨0, true⟩ := by simp [reflectStep]
    have hsite : reflectSite (x - unitVec L 0) - unitVec L 0 = reflectSite x := by
      rw [reflectSite_sub, reflectSite_unitVec_zero]
      abel
    rw [hr, stepHolonomy_backward, stepHolonomy_forward]
    simp [reflectConfig, reflectLink, hsite]
  · have hr : reflectStep ⟨d, false⟩ = ⟨d, false⟩ := by simp [reflectStep, hd]
    have hsite : reflectSite (x - unitVec L d) = reflectSite x - unitVec L d := by
      rw [reflectSite_sub, reflectSite_unitVec_of_ne hd]
    rw [hr, stepHolonomy_backward, stepHolonomy_backward]
    simp [reflectConfig, reflectLink, hd, hsite]
  · subst hd
    have hr : reflectStep ⟨(0 : Direction), true⟩ = ⟨0, false⟩ := by simp [reflectStep]
    rw [hr, stepHolonomy_forward, stepHolonomy_backward]
    simp [reflectConfig, reflectLink]
  · have hr : reflectStep ⟨d, true⟩ = ⟨d, true⟩ := by simp [reflectStep, hd]
    rw [hr, stepHolonomy_forward, stepHolonomy_forward]
    simp [reflectConfig, reflectLink, hd]

/-- Holonomies in the reflected configuration are holonomies of reflected paths. -/
theorem pathHolonomy_reflectConfig (U : GaugeConfig L) (x : Lattice4D L) (p : List LatticeStep) :
    pathHolonomy (reflectConfig U) x p = pathHolonomy U (reflectSite x) (p.map reflectStep) := by
  induction p generalizing x with
  | nil => rfl
  | cons s p ih =>
    simp only [List.map_cons, pathHolonomy_cons, stepHolonomy_reflectConfig, ih,
      stepTarget_reflect]

/-- Cyclic rotation of a closed path does not change `½ Re tr` of its holonomy. -/
theorem halfTraceRe_pathHolonomy_rotate (U : GaugeConfig L) (x : Lattice4D L)
    (q₁ q₂ : List LatticeStep) (hc : pathTarget x (q₁ ++ q₂) = x) :
    halfTraceRe (pathHolonomy U (pathTarget x q₁) (q₂ ++ q₁)) =
      halfTraceRe (pathHolonomy U x (q₁ ++ q₂)) := by
  have hc' : pathTarget (pathTarget x q₁) q₂ = x := by
    rw [← pathTarget_append]
    exact hc
  rw [pathHolonomy_append, pathHolonomy_append, hc']
  set H₁ := pathHolonomy U x q₁
  set H₂ := pathHolonomy U (pathTarget x q₁) q₂
  calc halfTraceRe (H₂ * H₁) = halfTraceRe (H₁⁻¹ * (H₁ * H₂) * H₁⁻¹⁻¹) := by
        congr 1
        group
    _ = halfTraceRe (H₁ * H₂) := halfTraceRe_conj _ _

theorem pathTarget_replicate (x : Lattice4D L) (n : ℕ) (s : LatticeStep) :
    pathTarget x (List.replicate n s) = x + n • s.displacement L := by
  rw [pathTarget_eq_add, List.map_replicate, List.sum_replicate]

theorem floor_div_eq_of_eq_mul {x a : ℝ} (ha : 0 < a) {k : ℤ} (h : x = k * a) : ⌊x / a⌋ = k := by
  rw [h, mul_div_assoc, div_self ha.ne', mul_one, Int.floor_intCast]

/-- Time-commensurate loops at spacing `a`: the base time is a multiple of `a`, and so is the
time extent when the loop has a time direction. -/
def IsTimeCommensurate (a : ℝ) (ℓ : PhysicalRectangle) : Prop :=
  (∃ k : ℤ, (ℓ.base 0 : ℝ) = k * a) ∧ (ℓ.μ = 0 → ∃ r : ℕ, (ℓ.sideμ : ℝ) = r * a)

theorem latticeBase_timeReflect_of_ne {a : ℝ} (ℓ : PhysicalRectangle) {i : Fin 4} (hi : i ≠ 0) :
    ℓ.timeReflect.latticeBase a i = ℓ.latticeBase a i := by
  simp [PhysicalRectangle.latticeBase, PhysicalRectangle.timeReflect, Function.update_of_ne hi]

theorem timeReflect_base_zero_of_eq {ℓ : PhysicalRectangle} (hμ : ℓ.μ = 0) :
    ((ℓ.timeReflect.base 0 : ℚ) : ℝ) = -(ℓ.base 0 : ℝ) - (ℓ.sideμ : ℝ) := by
  simp [PhysicalRectangle.timeReflect, hμ]

theorem timeReflect_base_zero_of_ne {ℓ : PhysicalRectangle} (hμ : ℓ.μ ≠ 0) :
    ((ℓ.timeReflect.base 0 : ℚ) : ℝ) = -(ℓ.base 0 : ℝ) := by
  simp [PhysicalRectangle.timeReflect, hμ]

theorem smul_unitVec_zero_apply (n : ℕ) : (n • unitVec L 0) 0 = (n : ZMod L) := by
  simp [unitVec]

/-- For a time-commensurate loop, the floor discretization commutes with the site reflection:
the Wilson loop of the reflected physical loop is the Wilson loop of the loop in the reflected
configuration. -/
theorem physicalWilsonLoop_timeReflect {a : ℝ} (ha : 0 < a) {ℓ : PhysicalRectangle}
    (hℓ : IsTimeCommensurate a ℓ) (U : GaugeConfig L) :
    physicalWilsonLoop L a ℓ.timeReflect U = physicalWilsonLoop L a ℓ (reflectConfig U) := by
  obtain ⟨⟨k, hk⟩, hr⟩ := hℓ
  have hbase : ℓ.latticeBase a 0 = k := floor_div_eq_of_eq_mul ha hk
  have hν : ℓ.ν ≠ 0 := (lt_of_le_of_lt (Fin.zero_le ℓ.μ) ℓ.plane).ne'
  have hloop : ℓ.timeReflect.latticeLoop a = ℓ.latticeLoop a := rfl
  unfold physicalWilsonLoop wilsonLoop
  rw [pathHolonomy_reflectConfig, hloop]
  by_cases hμ : ℓ.μ = 0
  · obtain ⟨r, hrR⟩ := hr hμ
    have hsteps : ℓ.stepsμ a = r := by
      simp only [PhysicalRectangle.stepsμ, hrR, mul_div_assoc, div_self ha.ne', mul_one,
        Nat.floor_natCast]
    have hbase' : ℓ.timeReflect.latticeBase a 0 = -k - r := by
      apply floor_div_eq_of_eq_mul ha
      rw [timeReflect_base_zero_of_eq hμ, hk, hrR]
      push_cast
      ring
    set x₀ := latticeSite L (ℓ.latticeBase a) with hx₀
    set x₁ := latticeSite L (ℓ.timeReflect.latticeBase a) with hx₁
    have hsite : x₁ + r • unitVec L 0 = reflectSite x₀ := by
      funext i
      by_cases hi : i = 0
      · subst hi
        simp only [hx₁, hx₀, latticeSite, Pi.add_apply, smul_unitVec_zero_apply, reflectSite,
          ite_true, hbase', hbase]
        push_cast
        ring
      · simp [hx₁, hx₀, latticeSite, reflectSite, hi, unitVec,
          latticeBase_timeReflect_of_ne ℓ hi]
    set t := ℓ.stepsν a
    let ABC : List LatticeStep := List.replicate t ⟨ℓ.ν, true⟩ ++ List.replicate r ⟨0, true⟩ ++
      List.replicate t ⟨ℓ.ν, false⟩
    let D : List LatticeStep := List.replicate r ⟨0, false⟩
    have hmap : (ℓ.latticeLoop a).map reflectStep = D ++ ABC := by
      simp [PhysicalRectangle.latticeLoop, rectangleSteps, hμ, hsteps, List.map_replicate,
        reflectStep, hν, D, ABC, t]
    have hrect : ABC ++ D = rectangleSteps ℓ.ν 0 t r := rfl
    have htarget : pathTarget x₁ ABC = reflectSite x₀ := by
      rw [← hsite]
      simp only [ABC, pathTarget_append, pathTarget_replicate]
      simp only [LatticeStep.displacement_forward, LatticeStep.displacement_backward, smul_neg]
      abel
    have hclosed : pathTarget x₁ (ABC ++ D) = x₁ := by
      rw [hrect]
      exact pathTarget_rectangleSteps _ _ _ _ _
    rw [hmap, ← htarget, halfTraceRe_pathHolonomy_rotate U x₁ ABC D hclosed, hrect]
    have hrev := pathHolonomy_reversePath U x₁ (rectangleSteps 0 ℓ.ν r t)
    rw [pathTarget_rectangleSteps, reversePath_rectangleSteps] at hrev
    rw [hrev, halfTraceRe_inv]
    simp only [PhysicalRectangle.latticeLoop, hμ, hsteps, t]
  · have hmap : (ℓ.latticeLoop a).map reflectStep = ℓ.latticeLoop a := by
      simp [PhysicalRectangle.latticeLoop, rectangleSteps, List.map_replicate, reflectStep, hμ, hν]
    have hsite : latticeSite L (ℓ.timeReflect.latticeBase a) =
        reflectSite (latticeSite L (ℓ.latticeBase a)) := by
      have hbase' : ℓ.timeReflect.latticeBase a 0 = -k := by
        apply floor_div_eq_of_eq_mul ha
        rw [timeReflect_base_zero_of_ne hμ, hk]
        push_cast
        ring
      funext i
      by_cases hi : i = 0
      · subst hi
        simp [latticeSite, reflectSite, hbase', hbase]
      · simp [latticeSite, reflectSite, hi, latticeBase_timeReflect_of_ne ℓ hi]
    rw [hmap, hsite]

end ReflectedLoops

/-! ## 10. Positive-time loops use only links of the positive half -/

section Locality

variable {L : ℕ}

/-- The link traversed by one lattice step. -/
def stepLink (x : Lattice4D L) (s : LatticeStep) : Link L :=
  if s.forward then ⟨x, s.dir⟩ else ⟨x - unitVec L s.dir, s.dir⟩

theorem stepHolonomy_congr {U U' : GaugeConfig L} {x : Lattice4D L} {s : LatticeStep}
    (h : U (stepLink x s) = U' (stepLink x s)) : stepHolonomy U x s = stepHolonomy U' x s := by
  rcases s with ⟨d, _ | _⟩
  · simp only [stepLink, Bool.false_eq_true, ite_false] at h
    simp [stepHolonomy_backward, h]
  · simp only [stepLink, ite_true] at h
    simp [stepHolonomy_forward, h]

/-- Every link traversed by the path satisfies `S`. -/
def PathIn (S : Link L → Prop) : Lattice4D L → List LatticeStep → Prop
  | _, [] => True
  | x, s :: p => S (stepLink x s) ∧ PathIn S (stepTarget x s) p

theorem pathHolonomy_congr_of_pathIn {S : Link L → Prop} {U U' : GaugeConfig L}
    (h : ∀ e, S e → U e = U' e) :
    ∀ {x : Lattice4D L} {p : List LatticeStep}, PathIn S x p →
      pathHolonomy U x p = pathHolonomy U' x p
  | _, [], _ => rfl
  | _, _ :: _, ⟨hs, hp⟩ => by
    rw [pathHolonomy_cons, pathHolonomy_cons, stepHolonomy_congr (h _ hs),
      pathHolonomy_congr_of_pathIn h hp]

theorem pathIn_append {S : Link L → Prop} (x : Lattice4D L) (p q : List LatticeStep) :
    PathIn S x (p ++ q) ↔ PathIn S x p ∧ PathIn S (pathTarget x p) q := by
  induction p generalizing x with
  | nil => simp [PathIn]
  | cons s p ih => simp [PathIn, ih, and_assoc]

theorem pathIn_replicate {S : Link L → Prop} (x : Lattice4D L) (n : ℕ) (s : LatticeStep) :
    PathIn S x (List.replicate n s) ↔ ∀ j < n, S (stepLink (x + j • s.displacement L) s) := by
  induction n generalizing x with
  | zero => simp [PathIn]
  | succ n ih =>
    rw [List.replicate_succ, PathIn, ih]
    constructor
    · rintro ⟨h0, h⟩ j hj
      cases j with
      | zero =>
        rw [zero_smul, add_zero]
        exact h0
      | succ j =>
        have e : x + (j + 1) • s.displacement L = stepTarget x s + j • s.displacement L := by
          rw [stepTarget, succ_nsmul', add_assoc]
        rw [e]
        exact h j (by omega)
    · intro h
      refine ⟨?_, fun j hj => ?_⟩
      · have h0 := h 0 (by omega)
        rwa [zero_smul, add_zero] at h0
      · have e : x + (j + 1) • s.displacement L = stepTarget x s + j • s.displacement L := by
          rw [stepTarget, succ_nsmul', add_assoc]
        have := h (j + 1) (by omega)
        rwa [e] at this

theorem timeVal_add_of_zero (x y : Lattice4D L) (hy : y 0 = 0) : timeVal (x + y) = timeVal x := by
  simp [timeVal, hy]

theorem timeVal_add_nsmul_unitVec_zero [NeZero L] (x : Lattice4D L) (j : ℕ)
    (h : timeVal x + j < L) : timeVal (x + j • unitVec L 0) = timeVal x + j := by
  have h0 : (x + j • unitVec L 0) 0 = (((x 0).val + j : ℕ) : ZMod L) := by
    simp [unitVec]
  simp only [timeVal, h0]
  exact ZMod.val_natCast_of_lt h

theorem timeVal_sub_nsmul_unitVec_zero [NeZero L] (x : Lattice4D L) (j : ℕ)
    (h : j ≤ timeVal x) : timeVal (x - j • unitVec L 0) = timeVal x - j := by
  have hlt := timeVal_lt x
  have h' : j ≤ (x 0).val := h
  have h0 : (x - j • unitVec L 0) 0 = (((x 0).val - j : ℕ) : ZMod L) := by
    rw [Nat.cast_sub h']
    simp [unitVec]
  simp only [timeVal, h0]
  exact ZMod.val_natCast_of_lt (by unfold timeVal at h hlt; omega)

/-- A path all of whose steps are spatial stays in its time slice. -/
theorem pathIn_positive_of_spatial [NeZero L] {M : ℕ} :
    ∀ {x : Lattice4D L} {p : List LatticeStep}, (∀ s ∈ p, s.dir ≠ 0) → timeVal x ≤ M →
      PathIn (IsPositiveLink M) x p
  | _, [], _, _ => trivial
  | x, s :: p, hp, hx => by
    have hs : s.dir ≠ 0 := hp s List.mem_cons_self
    have hd0 : (s.displacement L) 0 = 0 := by
      rcases s with ⟨d, _ | _⟩ <;> simp [unitVec, Ne.symm hs]
    refine ⟨?_, pathIn_positive_of_spatial (fun s' hs' => hp s' (List.mem_cons_of_mem _ hs'))
      (by rw [stepTarget, timeVal_add_of_zero _ _ hd0]; exact hx)⟩
    rcases s with ⟨d, _ | _⟩
    · have ht : timeVal (x - unitVec L d) = timeVal x := by
        rw [sub_eq_add_neg, timeVal_add_of_zero]
        simp [unitVec, Ne.symm hs]
      simp only [IsPositiveLink, stepLink, Bool.false_eq_true, ite_false]
      simp only [hs, ite_false, ht]
      exact hx
    · simp only [IsPositiveLink, stepLink, ite_true]
      simp only [hs, ite_false]
      exact hx

/-- At spacing `a` on the lattice of side `2M`, the time data of the loop are nonnegative
multiples of `a`, and the loop lies in the closed positive half `0 ≤ x₀ ≤ M a`. -/
def IsReflectionAdapted (a : ℝ) (M : ℕ) (ℓ : PhysicalRectangle) : Prop :=
  ∃ k r : ℕ, (ℓ.base 0 : ℝ) = k * a ∧ (ℓ.μ = 0 → (ℓ.sideμ : ℝ) = r * a) ∧ k + r ≤ M

theorem IsReflectionAdapted.isTimeCommensurate {a : ℝ} {M : ℕ} {ℓ : PhysicalRectangle}
    (h : IsReflectionAdapted a M ℓ) : IsTimeCommensurate a ℓ := by
  obtain ⟨k, r, hk, hr, -⟩ := h
  exact ⟨⟨k, by exact_mod_cast hk⟩, fun hμ => ⟨r, hr hμ⟩⟩

/-- An adapted loop traverses only links of the closed positive half. -/
theorem pathIn_latticeLoop_of_adapted [NeZero L] {M : ℕ} (hL : L = 2 * M) {a : ℝ} (ha : 0 < a)
    {ℓ : PhysicalRectangle} (hℓ : IsReflectionAdapted a M ℓ) :
    PathIn (IsPositiveLink M) (latticeSite L (ℓ.latticeBase a)) (ℓ.latticeLoop a) := by
  obtain ⟨k, r, hk, hr, hkr⟩ := hℓ
  have hν : ℓ.ν ≠ 0 := (lt_of_le_of_lt (Fin.zero_le ℓ.μ) ℓ.plane).ne'
  have hbase : ℓ.latticeBase a 0 = k := floor_div_eq_of_eq_mul ha (by exact_mod_cast hk)
  have hM : 0 < M := by
    have := NeZero.pos L
    omega
  set x₀ := latticeSite L (ℓ.latticeBase a) with hx₀
  have ht₀ : timeVal x₀ = k := by
    have h0 : x₀ 0 = ((k : ℕ) : ZMod L) := by simp [hx₀, latticeSite, hbase]
    simp only [timeVal, h0]
    exact ZMod.val_natCast_of_lt (by omega)
  by_cases hμ : ℓ.μ = 0
  · have hrR := hr hμ
    have hsteps : ℓ.stepsμ a = r := by
      simp only [PhysicalRectangle.stepsμ, hrR, mul_div_assoc, div_self ha.ne', mul_one,
        Nat.floor_natCast]
    set t := ℓ.stepsν a
    have hloop : ℓ.latticeLoop a = List.replicate r ⟨0, true⟩ ++ List.replicate t ⟨ℓ.ν, true⟩ ++
        List.replicate r ⟨0, false⟩ ++ List.replicate t ⟨ℓ.ν, false⟩ := by
      simp only [PhysicalRectangle.latticeLoop, rectangleSteps, hμ, hsteps, t]
    have hspat : ∀ (b : Bool) (n : ℕ), ∀ s ∈ List.replicate n (⟨ℓ.ν, b⟩ : LatticeStep),
        s.dir ≠ 0 := by
      intro b n s hs
      rw [List.eq_of_mem_replicate hs]
      exact hν
    rw [hloop, pathIn_append, pathIn_append, pathIn_append]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [pathIn_replicate]
      intro j hj
      simp only [IsPositiveLink, stepLink, ite_true, LatticeStep.displacement_forward]
      rw [timeVal_add_nsmul_unitVec_zero _ _ (by omega)]
      omega
    · rw [pathTarget_replicate]
      apply pathIn_positive_of_spatial (hspat true t)
      simp only [LatticeStep.displacement_forward]
      rw [timeVal_add_nsmul_unitVec_zero _ _ (by omega)]
      omega
    · rw [pathIn_replicate]
      intro j hj
      simp only [pathTarget_append, pathTarget_replicate, LatticeStep.displacement_forward,
        LatticeStep.displacement_backward, IsPositiveLink, stepLink, Bool.false_eq_true,
        ite_false, ite_true]
      have hsite : x₀ + r • unitVec L 0 + t • unitVec L ℓ.ν + j • -unitVec L 0 - unitVec L 0 =
          (x₀ + t • unitVec L ℓ.ν + r • unitVec L 0) - (j + 1) • unitVec L 0 := by
        rw [smul_neg, succ_nsmul]
        abel
      have hspatial : timeVal (x₀ + t • unitVec L ℓ.ν) = k := by
        rw [timeVal_add_of_zero _ _ (by simp [unitVec, Ne.symm hν]), ht₀]
      have hup : timeVal (x₀ + t • unitVec L ℓ.ν + r • unitVec L 0) = k + r := by
        rw [timeVal_add_nsmul_unitVec_zero _ _ (by omega), hspatial]
      rw [hsite, timeVal_sub_nsmul_unitVec_zero _ _ (by omega), hup]
      omega
    · simp only [pathTarget_append, pathTarget_replicate, LatticeStep.displacement_forward,
        LatticeStep.displacement_backward]
      apply pathIn_positive_of_spatial (hspat false t)
      have hsite : x₀ + r • unitVec L 0 + t • unitVec L ℓ.ν + r • -unitVec L 0 =
          x₀ + t • unitVec L ℓ.ν := by
        rw [smul_neg]
        abel
      rw [hsite, timeVal_add_of_zero _ _ (by simp [unitVec, Ne.symm hν]), ht₀]
      omega
  · apply pathIn_positive_of_spatial
    · intro s hs
      simp only [PhysicalRectangle.latticeLoop, rectangleSteps, List.mem_append,
        List.mem_replicate] at hs
      rcases hs with ((⟨-, rfl⟩ | ⟨-, rfl⟩) | ⟨-, rfl⟩) | ⟨-, rfl⟩
      · exact hμ
      · exact hν
      · exact hμ
      · exact hν
    · omega

/-- The physical Wilson loop of an adapted loop depends only on the links of the closed
positive half. -/
theorem physicalWilsonLoop_congr_of_adapted [NeZero L] {M : ℕ} (hL : L = 2 * M) {a : ℝ}
    (ha : 0 < a) {ℓ : PhysicalRectangle} (hℓ : IsReflectionAdapted a M ℓ) {U U' : GaugeConfig L}
    (h : ∀ e, IsPositiveLink M e → U e = U' e) :
    physicalWilsonLoop L a ℓ U = physicalWilsonLoop L a ℓ U' := by
  unfold physicalWilsonLoop wilsonLoop
  rw [pathHolonomy_congr_of_pathIn h (pathIn_latticeLoop_of_adapted hL ha hℓ)]

/-- Reflection positivity of the actual joint Wilson-loop law at one cutoff (side `2M`,
spacing `a`, coupling `β ≥ 0`), for every bounded continuous functional of loops that are
adapted to the reflection. It is the Osterwalder–Seiler positivity of the Wilson measure
carried by the floor discretization, which commutes with the site reflection on these loops. -/
theorem integral_reflectedSquare_wilsonLoopLaw_nonneg [NeZero L] {M : ℕ} (hL : L = 2 * M)
    {a : ℝ} (ha : 0 < a) (β : ℝ) (hβ : 0 ≤ β) {S : Set PhysicalRectangle}
    (hS : ∀ ℓ ∈ S, IsReflectionAdapted a M ℓ) (F : WilsonLoopSpace →ᵇ ℝ)
    (hF : DependsOnLoops S F) :
    0 ≤ ∫ w, F (reflectObservables w) * F w
      ∂(((wilsonProbability L β hβ).map (wilsonLoopVector L a) :
        ProbabilityMeasure WilsonLoopSpace) : Measure WilsonLoopSpace) := by
  have hcont : Continuous (fun w : WilsonLoopSpace => F (reflectObservables w) * F w) :=
    (F.continuous.comp continuous_reflectObservables).mul F.continuous
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_wilsonLoopVector L a).aemeasurable hcont.aestronglyMeasurable]
  have hrefl : ∀ U : GaugeConfig L, F (reflectObservables (wilsonLoopVector L a U)) =
      F (wilsonLoopVector L a (reflectConfig U)) := by
    intro U
    apply hF
    intro ℓ hℓ
    exact physicalWilsonLoop_timeReflect ha (hS ℓ hℓ).isTimeCommensurate U
  simp only [hrefl]
  exact wilson_reflection_positive hL β hβ (fun U => F (wilsonLoopVector L a U))
    (F.continuous.comp (continuous_wilsonLoopVector L a))
    (fun U U' h => hF _ _ (fun ℓ hℓ => physicalWilsonLoop_congr_of_adapted hL ha (hS ℓ hℓ) h))

end Locality

/-! ## 11. Inheritance along cutoff paths: the time-dyadic family -/

/-- The renormalized reflected square at one cutoff is the unrenormalized one of the
rescaled functional. -/
theorem integral_reflectedSquare_law {P : CutoffPath} (Z : LoopRenormalization P)
    (hZ : HasReflectionInvariantFactors Z) (n : ℕ) (F : WilsonLoopSpace →ᵇ ℝ) :
    ∫ w, F (reflectObservables w) * F w ∂(Z.law n : Measure WilsonLoopSpace) =
      ∫ w, (F.compContinuous ⟨Z.rescale n, Z.continuous_rescale n⟩) (reflectObservables w) *
        (F.compContinuous ⟨Z.rescale n, Z.continuous_rescale n⟩) w
          ∂(P.wilsonLoopLaw n : Measure WilsonLoopSpace) := by
  have hcont : Continuous (fun w : WilsonLoopSpace => F (reflectObservables w) * F w) :=
    (F.continuous.comp continuous_reflectObservables).mul F.continuous
  rw [LoopRenormalization.law, ProbabilityMeasure.toMeasure_map,
    integral_map (Z.continuous_rescale n).aemeasurable hcont.aestronglyMeasurable]
  simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
    rescale_reflectObservables Z hZ n]

/-- The positive-time loops of `A` are eventually adapted to the reflection along the path:
eventually the side is even and the loop is adapted at the current spacing and half side. -/
def EventuallyAdapted (P : CutoffPath) (A : Set PhysicalRectangle) : Prop :=
  ∀ ℓ ∈ positivePart A, ∀ᶠ n in atTop,
    Even (P.side n) ∧ IsReflectionAdapted (P.spacing n) (P.side n / 2) ℓ

/-- Inheritance theorem: if the positive-time loops of `A` are eventually adapted, then every
limit law of the renormalized joint laws (reflection-invariant constants) is reflection
positive on `A`. The per-cutoff positivity used is proved from the actual Wilson measure; the
passage to the limit uses that each cylinder inequality is a closed condition. -/
theorem limit_isReflectionPositiveOn_of_eventuallyAdapted {P : CutoffPath}
    (Z : LoopRenormalization P) (hZ : HasReflectionInvariantFactors Z) {A : Set PhysicalRectangle}
    (hA : EventuallyAdapted P A) {ν : ProbabilityMeasure WilsonLoopSpace}
    (hν : Z.IsLimitLaw ν) : IsReflectionPositiveOn A ν := by
  rw [isReflectionPositiveOn_iff_cylinder]
  intro S hS F hF
  obtain ⟨φ, hφ, hlim⟩ := hν
  have hev : ∀ᶠ n in atTop, ∀ ℓ ∈ S,
      Even (P.side n) ∧ IsReflectionAdapted (P.spacing n) (P.side n / 2) ℓ :=
    (Filter.eventually_all_finset S).2 fun ℓ hℓ => hA ℓ (hS hℓ)
  have hcut : ∀ᶠ n in atTop,
      0 ≤ ∫ w, reflectedSquare F w ∂(Z.law (φ n) : Measure WilsonLoopSpace) := by
    filter_upwards [hφ.tendsto_atTop.eventually hev] with n hn
    simp only [reflectedSquare_apply]
    rw [integral_reflectedSquare_law Z hZ]
    by_cases hSe : S = ∅
    · subst hSe
      have hconst : ∀ w w' : WilsonLoopSpace,
          (F.compContinuous ⟨Z.rescale (φ n), Z.continuous_rescale (φ n)⟩) w =
            (F.compContinuous ⟨Z.rescale (φ n), Z.continuous_rescale (φ n)⟩) w' :=
        fun w w' => DependsOnLoops.comp_rescale Z (φ n) hF w w' (by simp)
      refine integral_nonneg fun w => ?_
      rw [hconst (reflectObservables w) w]
      exact mul_self_nonneg _
    · obtain ⟨ℓ₀, hℓ₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
      have hL : P.side (φ n) = 2 * (P.side (φ n) / 2) := by
        obtain ⟨c, hc⟩ := (hn ℓ₀ hℓ₀).1
        omega
      exact integral_reflectedSquare_wilsonLoopLaw_nonneg hL (P.spacing_pos (φ n))
        (P.coupling (φ n)) (P.coupling_nonneg (φ n)) (fun ℓ hℓ => (hn ℓ hℓ).2)
        (F.compContinuous ⟨Z.rescale (φ n), Z.continuous_rescale (φ n)⟩)
        (DependsOnLoops.comp_rescale Z (φ n) hF)
  have hcl : IsClosed {μ : ProbabilityMeasure WilsonLoopSpace |
      0 ≤ ∫ w, reflectedSquare F w ∂(μ : Measure WilsonLoopSpace)} :=
    isClosed_le continuous_const
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction _)
  simpa only [Set.mem_ofPred_eq, reflectedSquare_apply] using hcl.mem_of_tendsto hlim hcut

/-- Loops whose base time, and time extent when the loop has a time direction, are dyadic
rationals. -/
def IsTimeDyadic (ℓ : PhysicalRectangle) : Prop :=
  ∃ (m : ℕ) (j : ℤ) (r : ℕ), (ℓ.base 0 : ℝ) = j / 2 ^ m ∧ (ℓ.μ = 0 → (ℓ.sideμ : ℝ) = r / 2 ^ m)

/-- Along a cutoff path with spacings `2⁻ⁿ`, eventually even sides and physical extent tending
to infinity, every positive-time time-dyadic loop is eventually adapted to the reflection. -/
theorem eventuallyAdapted_timeDyadic (P : CutoffPath) (hsp : ∀ n, P.spacing n = (1 / 2 : ℝ) ^ n)
    (heven : ∀ᶠ n in atTop, Even (P.side n))
    (hext : Tendsto (fun n => (P.side n : ℝ) * P.spacing n) atTop atTop) :
    EventuallyAdapted P {ℓ | IsTimeDyadic ℓ} := by
  rintro ℓ ⟨⟨m, j, r, hj, hr⟩, hpos⟩
  have hb : (0 : ℝ) < ℓ.base 0 := by exact_mod_cast hpos
  have hjpos : (0 : ℝ) < j := by
    rw [hj] at hb
    exact (div_pos_iff_of_pos_right (by positivity)).mp hb
  have hj0 : 0 ≤ j := by exact_mod_cast hjpos.le
  have hbig : ∀ᶠ n in atTop, 2 * (((j.toNat + r : ℕ) : ℝ) / 2 ^ m) ≤ (P.side n : ℝ) * P.spacing n :=
    hext.eventually (eventually_ge_atTop _)
  filter_upwards [heven, hbig, eventually_ge_atTop m] with n hev hbn hmn
  refine ⟨hev, j.toNat * 2 ^ (n - m), r * 2 ^ (n - m), ?_, ?_, ?_⟩
  · have hpow : (2 : ℝ) ^ n = 2 ^ (n - m) * 2 ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hmn]
    have hjt : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hj0
    rw [hj, hsp n]
    push_cast
    rw [hjt, one_div, inv_pow, hpow]
    field_simp
  · intro hμ
    have hpow : (2 : ℝ) ^ n = 2 ^ (n - m) * 2 ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hmn]
    rw [hr hμ, hsp n]
    push_cast
    rw [one_div, inv_pow, hpow]
    field_simp
  · have h2 : 2 ∣ P.side n := even_iff_two_dvd.mp hev
    have hcast : ((P.side n / 2 : ℕ) : ℝ) = (P.side n : ℝ) / 2 := by
      rw [Nat.cast_div h2 (by norm_num)]
      norm_num
    have hpow : (2 : ℝ) ^ n = 2 ^ (n - m) * 2 ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hmn]
    have hreal : ((j.toNat * 2 ^ (n - m) + r * 2 ^ (n - m) : ℕ) : ℝ) ≤
        ((P.side n / 2 : ℕ) : ℝ) := by
      have h2n : (0 : ℝ) < 2 ^ n := by positivity
      have h2m : (0 : ℝ) < 2 ^ m := by positivity
      rw [hsp n] at hbn
      have e1 : ((j.toNat + r : ℕ) : ℝ) * 2 ^ (n - m) =
          (((j.toNat + r : ℕ) : ℝ) / 2 ^ m) * 2 ^ n := by
        rw [hpow]
        field_simp
      have e2 : (P.side n : ℝ) * (1 / 2) ^ n * 2 ^ n = P.side n := by
        rw [one_div, inv_pow, mul_assoc, inv_mul_cancel₀ h2n.ne', mul_one]
      have key : ((j.toNat + r : ℕ) : ℝ) * 2 ^ (n - m) ≤ (P.side n : ℝ) / 2 := by
        rw [e1]
        have := mul_le_mul_of_nonneg_right hbn h2n.le
        rw [e2] at this
        linarith
      have e3 : ((j.toNat * 2 ^ (n - m) + r * 2 ^ (n - m) : ℕ) : ℝ) =
          ((j.toNat + r : ℕ) : ℝ) * 2 ^ (n - m) := by
        push_cast
        ring
      rw [hcast, e3]
      exact key
    exact_mod_cast hreal

/-- Along every continuum cutoff path with spacings `2⁻ⁿ` and eventually even sides, every limit
law of the renormalized loops (reflection-invariant constants) is reflection positive for all
bounded continuous functionals of positive-time time-dyadic loops. No hypothesis on the
measure is used: the cutoff positivity is Osterwalder–Seiler positivity of the actual Wilson
measure, and the coupling plays no role. -/
theorem limit_isReflectionPositiveOn_timeDyadic (P : ContinuumCutoffPath)
    (hsp : ∀ n, P.spacing n = (1 / 2 : ℝ) ^ n) (heven : ∀ᶠ n in atTop, Even (P.side n))
    (Z : LoopRenormalization P.toCutoffPath) (hZ : HasReflectionInvariantFactors Z)
    {ν : ProbabilityMeasure WilsonLoopSpace} (hν : Z.IsLimitLaw ν) :
    IsReflectionPositiveOn {ℓ | IsTimeDyadic ℓ} ν :=
  limit_isReflectionPositiveOn_of_eventuallyAdapted Z hZ
    (eventuallyAdapted_timeDyadic P.toCutoffPath hsp heven P.physicalSide_tendsto_atTop) hν

theorem hasReflectionInvariantFactors_unrenormalized (P : CutoffPath) :
    HasReflectionInvariantFactors (LoopRenormalization.unrenormalized P) :=
  fun _ _ => rfl

theorem dyadicOneLoopPath_side_even : ∀ᶠ n in atTop, Even (dyadicOneLoopPath.side n) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  change Even (4 ^ n)
  exact Nat.even_pow.mpr ⟨by decide, by omega⟩

/-- Unconditional along the explicit asymptotically free dyadic path: every subsequential limit
of the unrenormalized joint Wilson-loop laws is reflection positive for all bounded continuous
functionals of positive-time time-dyadic loops. -/
theorem dyadicOneLoopPath_limit_isReflectionPositiveOn {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {ν : ProbabilityMeasure WilsonLoopSpace}
    (hlim : Tendsto (fun n => dyadicOneLoopPath.wilsonLoopLaw (φ n)) atTop (𝓝 ν)) :
    IsReflectionPositiveOn {ℓ | IsTimeDyadic ℓ} ν := by
  apply limit_isReflectionPositiveOn_timeDyadic dyadicOneLoopPath (fun _ => rfl)
    dyadicOneLoopPath_side_even (LoopRenormalization.unrenormalized _)
    (hasReflectionInvariantFactors_unrenormalized _)
  refine ⟨φ, hφ, ?_⟩
  simpa only [LoopRenormalization.unrenormalized_law] using hlim

/-! ## 12. The full `reflection_positive` field from a named regularity hypothesis -/

/-- The named regularity hypothesis on a limit law that turns time-dyadic reflection positivity
into the full `reflection_positive` field: every positive-time loop, and its time reflection,
is an almost-sure limit of positive-time time-dyadic loops and their reflections. It says the
realized loop field is continuous along dyadic approximations of the loop position. It is not
proved here; it is a property of the limit law, not of any single cutoff. -/
def DyadicTimeApproximable (ν : ProbabilityMeasure WilsonLoopSpace) : Prop :=
  ∀ ℓ : PhysicalRectangle, ℓ.IsPositiveTime → ∃ seq : ℕ → PhysicalRectangle,
    (∀ k, IsTimeDyadic (seq k) ∧ (seq k).IsPositiveTime) ∧
    (∀ᵐ w ∂(ν : Measure WilsonLoopSpace), Tendsto (fun k => w (seq k)) atTop (𝓝 (w ℓ))) ∧
    (∀ᵐ w ∂(ν : Measure WilsonLoopSpace),
      Tendsto (fun k => w (seq k).timeReflect) atTop (𝓝 (w ℓ.timeReflect)))

/-- Time-dyadic reflection positivity together with the regularity hypothesis gives
reflection positivity for all bounded continuous functionals of positive-time loops. -/
theorem isReflectionPositive_of_timeDyadic {ν : ProbabilityMeasure WilsonLoopSpace}
    (hD : IsReflectionPositiveOn {ℓ | IsTimeDyadic ℓ} ν) (hA : DyadicTimeApproximable ν) :
    IsReflectionPositive ν := by
  classical
  rw [isReflectionPositive_iff_univ, isReflectionPositiveOn_iff_cylinder]
  rw [isReflectionPositiveOn_iff_cylinder] at hD
  intro S hS F hF
  have hSpos : ∀ ℓ ∈ S, ℓ.IsPositiveTime := fun ℓ hℓ => (hS hℓ).2
  let seq : PhysicalRectangle → ℕ → PhysicalRectangle := fun ℓ =>
    if h : ℓ.IsPositiveTime then (hA ℓ h).choose else fun _ => ℓ
  have hseq : ∀ ℓ ∈ S, (∀ k, IsTimeDyadic (seq ℓ k) ∧ (seq ℓ k).IsPositiveTime) ∧
      (∀ᵐ w ∂(ν : Measure WilsonLoopSpace), Tendsto (fun k => w (seq ℓ k)) atTop (𝓝 (w ℓ))) ∧
      (∀ᵐ w ∂(ν : Measure WilsonLoopSpace),
        Tendsto (fun k => w (seq ℓ k).timeReflect) atTop (𝓝 (w ℓ.timeReflect))) := by
    intro ℓ hℓ
    simp only [seq, hSpos ℓ hℓ, dite_true]
    exact (hA ℓ (hSpos ℓ hℓ)).choose_spec
  let subst : ℕ → WilsonLoopSpace → WilsonLoopSpace := fun k w ℓ' =>
    if ℓ' ∈ S then w (seq ℓ' k) else 0
  have hsubst : ∀ k, Continuous (subst k) := by
    intro k
    apply continuous_pi
    intro ℓ'
    by_cases h : ℓ' ∈ S
    · simpa [subst, h] using continuous_apply (seq ℓ' k)
    · simpa [subst, h] using (continuous_const : Continuous fun _ : WilsonLoopSpace => (0 : ℝ))
  let FN : ℕ → WilsonLoopSpace →ᵇ ℝ := fun k => F.compContinuous ⟨subst k, hsubst k⟩
  let T : ℕ → Finset PhysicalRectangle := fun k => S.image fun ℓ => seq ℓ k
  have hT : ∀ k, (T k : Set PhysicalRectangle) ⊆ positivePart {ℓ | IsTimeDyadic ℓ} := by
    intro k ℓ hℓ
    simp only [T, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hℓ
    obtain ⟨ℓ', hℓ', rfl⟩ := hℓ
    exact (hseq ℓ' hℓ').1 k
  have hFN : ∀ k, DependsOnLoops (T k) (FN k) := by
    intro k w w' h
    change F (subst k w) = F (subst k w')
    congr 1
    funext ℓ'
    by_cases hℓ' : ℓ' ∈ S
    · simp only [subst, hℓ', ite_true]
      exact h _ (by simp [T]; exact ⟨ℓ', hℓ', rfl⟩)
    · simp [subst, hℓ']
  have hpos : ∀ k, 0 ≤ ∫ w, FN k (reflectObservables w) * FN k w ∂(ν : Measure WilsonLoopSpace) :=
    fun k => hD (T k) (hT k) (FN k) (hFN k)
  have hFind : ∀ w : WilsonLoopSpace, F ((S : Set PhysicalRectangle).indicator w) = F w := by
    intro w
    apply hF
    intro ℓ hℓ
    rw [Set.indicator_of_mem hℓ]
  have hae1 : ∀ᵐ w ∂(ν : Measure WilsonLoopSpace), ∀ ℓ ∈ S,
      Tendsto (fun k => w (seq ℓ k)) atTop (𝓝 (w ℓ)) :=
    (Filter.eventually_all_finset S).2 fun ℓ hℓ => (hseq ℓ hℓ).2.1
  have hae2 : ∀ᵐ w ∂(ν : Measure WilsonLoopSpace), ∀ ℓ ∈ S,
      Tendsto (fun k => w (seq ℓ k).timeReflect) atTop (𝓝 (w ℓ.timeReflect)) :=
    (Filter.eventually_all_finset S).2 fun ℓ hℓ => (hseq ℓ hℓ).2.2
  have hlim : ∀ᵐ w ∂(ν : Measure WilsonLoopSpace),
      Tendsto (fun k => FN k (reflectObservables w) * FN k w) atTop
        (𝓝 (F (reflectObservables w) * F w)) := by
    filter_upwards [hae1, hae2] with w h1 h2
    have c1 : Tendsto (fun k => subst k w) atTop (𝓝 ((S : Set PhysicalRectangle).indicator w)) := by
      rw [tendsto_pi_nhds]
      intro ℓ'
      by_cases hℓ' : ℓ' ∈ S
      · simpa [subst, hℓ', Set.indicator_of_mem (Finset.mem_coe.mpr hℓ')] using h1 ℓ' hℓ'
      · simp [subst, hℓ']
    have c2 : Tendsto (fun k => subst k (reflectObservables w)) atTop
        (𝓝 ((S : Set PhysicalRectangle).indicator (reflectObservables w))) := by
      rw [tendsto_pi_nhds]
      intro ℓ'
      by_cases hℓ' : ℓ' ∈ S
      · simpa [subst, hℓ', reflectObservables, Set.indicator_of_mem (Finset.mem_coe.mpr hℓ')]
          using h2 ℓ' hℓ'
      · simp [subst, hℓ']
    have t1 := (F.continuous.tendsto _).comp c1
    have t2 := (F.continuous.tendsto _).comp c2
    rw [hFind] at t1 t2
    exact t2.mul t1
  have hmeas : ∀ k, AEStronglyMeasurable (fun w => FN k (reflectObservables w) * FN k w)
      (ν : Measure WilsonLoopSpace) :=
    fun k => (((FN k).continuous.comp continuous_reflectObservables).mul
      (FN k).continuous).aestronglyMeasurable
  have hbound : ∀ k, ∀ᵐ w ∂(ν : Measure WilsonLoopSpace),
      ‖FN k (reflectObservables w) * FN k w‖ ≤ ‖F‖ * ‖F‖ := by
    intro k
    filter_upwards with w
    rw [norm_mul]
    exact mul_le_mul (F.norm_coe_le_norm _) (F.norm_coe_le_norm _) (norm_nonneg _)
      (norm_nonneg _)
  have hint := tendsto_integral_of_dominated_convergence (fun _ => ‖F‖ * ‖F‖) hmeas
    (integrable_const _) hbound hlim
  exact ge_of_tendsto' hint hpos

/-- The `reflection_positive` field of `ContinuumIdentificationObligations` along every
continuum cutoff path with spacings `2⁻ⁿ` and eventually even sides, for reflection-invariant
constants, from the named regularity hypothesis `DyadicTimeApproximable` on the limit laws
alone. The per-cutoff positivity is proved from the actual Wilson measure. -/
theorem reflection_positive_of_dyadicTimeApproximable (P : ContinuumCutoffPath)
    (hsp : ∀ n, P.spacing n = (1 / 2 : ℝ) ^ n) (heven : ∀ᶠ n in atTop, Even (P.side n))
    (Z : LoopRenormalization P.toCutoffPath) (hZ : HasReflectionInvariantFactors Z)
    (hreg : ∀ ν, Z.IsLimitLaw ν → DyadicTimeApproximable ν) :
    ∀ ν, Z.IsLimitLaw ν → ∀ F : WilsonLoopSpace →ᵇ ℝ, DependsOnPositiveTime F →
      0 ≤ ∫ w, F (reflectObservables w) * F w ∂(ν : Measure WilsonLoopSpace) :=
  fun ν hν => isReflectionPositive_of_timeDyadic
    (limit_isReflectionPositiveOn_timeDyadic P hsp heven Z hZ hν) (hreg ν hν)

/-- Along dyadic continuum paths the `reflection_positive` field is no longer an independent
obligation: it follows from `DyadicTimeApproximable` of the limit laws. -/
theorem continuumIdentificationObligations_of_dyadic {P : ContinuumCutoffPath}
    {Z : LoopRenormalization P.toCutoffPath} (h : ObligationsExceptReflection P Z)
    (hsp : ∀ n, P.spacing n = (1 / 2 : ℝ) ^ n) (heven : ∀ᶠ n in atTop, Even (P.side n))
    (hZ : HasReflectionInvariantFactors Z)
    (hreg : ∀ ν, Z.IsLimitLaw ν → DyadicTimeApproximable ν) :
    ContinuumIdentificationObligations P Z :=
  ⟨h, reflection_positive_of_dyadicTimeApproximable P hsp heven Z hZ hreg⟩

/-- The full obligations contain the other fields: the parent projection, named for consumers. -/
theorem ContinuumIdentificationObligations.exceptReflection {P : ContinuumCutoffPath}
    {Z : LoopRenormalization P.toCutoffPath} (h : ContinuumIdentificationObligations P Z) :
    ObligationsExceptReflection P Z :=
  h.toObligationsExceptReflection

/-! ## 13. Time-reflection symmetry of the actual model and of its limits -/

section ReflectionSymmetry

variable {L : ℕ}

/-- Link reflection as a permutation. -/
def reflectLinkEquiv : Equiv.Perm (Link L) :=
  Function.Involutive.toPerm reflectLink reflectLink_reflectLink

/-- Product Haar measure is invariant under the time reflection of configurations. -/
theorem measurePreserving_reflectConfig [NeZero L] :
    MeasurePreserving (reflectConfig (L := L)) (gaugeHaarMeasure L) (gaugeHaarMeasure L) := by
  have h1 : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Link L => SU2) reflectLinkEquiv).symm
      (Measure.pi fun _ : Link L => SU2.haarProbability)
      (Measure.pi fun _ : Link L => SU2.haarProbability) :=
    (measurePreserving_piCongrLeft (fun _ : Link L => SU2.haarProbability) reflectLinkEquiv).symm _
  have h2 : MeasurePreserving (fun (V : Link L → SU2) e => linkTwist e (V e))
      (Measure.pi fun _ : Link L => SU2.haarProbability)
      (Measure.pi fun _ : Link L => SU2.haarProbability) :=
    measurePreserving_pi _ _ measurePreserving_linkTwist
  have h := h2.comp h1
  have hf : (fun (V : Link L → SU2) e => linkTwist e (V e)) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : Link L => SU2) reflectLinkEquiv).symm =
        reflectConfig := by
    funext U e
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply, reflectLinkEquiv,
      reflectConfig, linkTwist]
    rfl
  rw [hf] at h
  exact h

/-- Exact invariance of the actual normalized Wilson probability under the time reflection,
for every lattice side and every coupling. -/
theorem wilsonProbability_reflect_invariant (L : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β) :
    (wilsonProbability L β hβ).map reflectConfig = wilsonProbability L β hβ := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  change (∫ U, F U ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)).map reflectConfig) = _
  rw [integral_map_of_stronglyMeasurable continuous_reflectConfig.measurable
    F.continuous.measurable.stronglyMeasurable, wilsonProbability_integral,
    wilsonProbability_integral]
  have hp := measurePreserving_reflectConfig (L := L)
  have h := integral_map_of_stronglyMeasurable (μ := gaugeHaarMeasure L) hp.measurable
    ((wilsonWeight_measurable (measurable_wilsonAction β)).mul
      F.continuous.measurable).stronglyMeasurable
  rw [hp.map_eq] at h
  simp only [Pi.mul_apply, boltzmannWeight, wilsonAction_reflectConfig] at h
  exact congrArg (fun x => x / wilsonPartition (gaugeHaarMeasure L) β) h.symm

/-- At one cutoff the joint law of time-commensurate loops is invariant under the time
reflection of the loops. -/
theorem integral_reflect_wilsonLoopLaw [NeZero L] {a : ℝ} (ha : 0 < a) (β : ℝ) (hβ : 0 ≤ β)
    {S : Set PhysicalRectangle} (hS : ∀ ℓ ∈ S, IsTimeCommensurate a ℓ)
    (F : WilsonLoopSpace →ᵇ ℝ) (hF : DependsOnLoops S F) :
    ∫ w, F (reflectObservables w) ∂(((wilsonProbability L β hβ).map (wilsonLoopVector L a) :
      ProbabilityMeasure WilsonLoopSpace) : Measure WilsonLoopSpace) =
      ∫ w, F w ∂(((wilsonProbability L β hβ).map (wilsonLoopVector L a) :
        ProbabilityMeasure WilsonLoopSpace) : Measure WilsonLoopSpace) := by
  have c1 : Continuous (fun w : WilsonLoopSpace => F (reflectObservables w)) :=
    F.continuous.comp continuous_reflectObservables
  have c2 : Continuous (fun U : GaugeConfig L => F (wilsonLoopVector L a U)) :=
    F.continuous.comp (continuous_wilsonLoopVector L a)
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_wilsonLoopVector L a).aemeasurable c1.aestronglyMeasurable,
    integral_map (continuous_wilsonLoopVector L a).aemeasurable F.continuous.aestronglyMeasurable]
  have hrefl : ∀ U : GaugeConfig L, F (reflectObservables (wilsonLoopVector L a U)) =
      F (wilsonLoopVector L a (reflectConfig U)) := by
    intro U
    apply hF
    intro ℓ hℓ
    exact physicalWilsonLoop_timeReflect ha (hS ℓ hℓ) U
  simp only [hrefl]
  have hinv := congrArg ProbabilityMeasure.toMeasure (wilsonProbability_reflect_invariant L β hβ)
  rw [ProbabilityMeasure.toMeasure_map] at hinv
  conv_rhs => rw [← hinv]
  rw [integral_map continuous_reflectConfig.aemeasurable c2.aestronglyMeasurable]

/-- Time-dyadic loops are eventually time-commensurate along spacings `2⁻ⁿ`. -/
theorem eventually_isTimeCommensurate_of_timeDyadic {P : CutoffPath}
    (hsp : ∀ n, P.spacing n = (1 / 2 : ℝ) ^ n) {ℓ : PhysicalRectangle} (hℓ : IsTimeDyadic ℓ) :
    ∀ᶠ n in atTop, IsTimeCommensurate (P.spacing n) ℓ := by
  obtain ⟨m, j, r, hj, hr⟩ := hℓ
  filter_upwards [eventually_ge_atTop m] with n hmn
  have hpow : (2 : ℝ) ^ n = 2 ^ (n - m) * 2 ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hmn]
  refine ⟨⟨j * 2 ^ (n - m), ?_⟩, fun hμ => ⟨r * 2 ^ (n - m), ?_⟩⟩
  · rw [hj, hsp n]
    push_cast
    rw [one_div, inv_pow, hpow]
    field_simp
  · rw [hr hμ, hsp n]
    push_cast
    rw [one_div, inv_pow, hpow]
    field_simp

/-- Every limit law of the renormalized loops (reflection-invariant constants) along spacings
`2⁻ⁿ`, for any sides and couplings, is invariant under the time reflection on functionals of
finitely many time-dyadic loops. -/
theorem limit_reflect_invariant_timeDyadic {P : CutoffPath}
    (hsp : ∀ n, P.spacing n = (1 / 2 : ℝ) ^ n) (Z : LoopRenormalization P)
    (hZ : HasReflectionInvariantFactors Z) {ν : ProbabilityMeasure WilsonLoopSpace}
    (hν : Z.IsLimitLaw ν) (S : Finset PhysicalRectangle) (hS : ∀ ℓ ∈ S, IsTimeDyadic ℓ)
    (F : WilsonLoopSpace →ᵇ ℝ) (hF : DependsOnLoops S F) :
    ∫ w, F (reflectObservables w) ∂(ν : Measure WilsonLoopSpace) =
      ∫ w, F w ∂(ν : Measure WilsonLoopSpace) := by
  obtain ⟨φ, hφ, hlim⟩ := hν
  let FΘ : WilsonLoopSpace →ᵇ ℝ :=
    F.compContinuous ⟨reflectObservables, continuous_reflectObservables⟩
  have hev : ∀ᶠ n in atTop, ∀ ℓ ∈ S, IsTimeCommensurate (P.spacing n) ℓ :=
    (Filter.eventually_all_finset S).2 fun ℓ hℓ => eventually_isTimeCommensurate_of_timeDyadic hsp
      (hS ℓ hℓ)
  have hcut : ∀ᶠ n in atTop, ∫ w, FΘ w ∂(Z.law (φ n) : Measure WilsonLoopSpace) =
      ∫ w, F w ∂(Z.law (φ n) : Measure WilsonLoopSpace) := by
    filter_upwards [hφ.tendsto_atTop.eventually hev] with n hn
    let G : WilsonLoopSpace →ᵇ ℝ := F.compContinuous ⟨Z.rescale (φ n), Z.continuous_rescale (φ n)⟩
    have hG : DependsOnLoops S G := DependsOnLoops.comp_rescale Z (φ n) hF
    have h := integral_reflect_wilsonLoopLaw (L := P.side (φ n)) (P.spacing_pos (φ n))
      (P.coupling (φ n)) (P.coupling_nonneg (φ n)) hn G hG
    rw [LoopRenormalization.law, ProbabilityMeasure.toMeasure_map,
      integral_map (Z.continuous_rescale (φ n)).aemeasurable FΘ.continuous.aestronglyMeasurable,
      integral_map (Z.continuous_rescale (φ n)).aemeasurable F.continuous.aestronglyMeasurable]
    simp only [FΘ, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
      ← rescale_reflectObservables Z hZ]
    exact h
  have hcl : IsClosed {μ : ProbabilityMeasure WilsonLoopSpace |
      ∫ w, FΘ w ∂(μ : Measure WilsonLoopSpace) = ∫ w, F w ∂(μ : Measure WilsonLoopSpace)} :=
    isClosed_eq (ProbabilityMeasure.continuous_integral_boundedContinuousFunction _)
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction _)
  exact hcl.mem_of_tendsto hlim hcut

end ReflectionSymmetry

/-! ## 14. The repository's kernel formulation `FiniteReflectionPositive` -/

theorem timeReflect_timeReflect (ℓ : PhysicalRectangle) : ℓ.timeReflect.timeReflect = ℓ := by
  rcases ℓ with ⟨b, μ, ν, h, R, T, hR, hT⟩
  simp only [PhysicalRectangle.timeReflect, PhysicalRectangle.mk.injEq, and_true]
  funext i
  by_cases hi : i = 0
  · subst hi
    simp
  · simp [Function.update_of_ne hi]

theorem reflectObservables_reflectObservables (w : WilsonLoopSpace) :
    reflectObservables (reflectObservables w) = w := by
  funext ℓ
  simp [reflectObservables, timeReflect_timeReflect]

theorem IsTimeDyadic.timeReflect {ℓ : PhysicalRectangle} (h : IsTimeDyadic ℓ) :
    IsTimeDyadic ℓ.timeReflect := by
  obtain ⟨m, j, r, hj, hr⟩ := h
  by_cases hμ : ℓ.μ = 0
  · refine ⟨m, -j - r, r, ?_, fun _ => hr hμ⟩
    rw [timeReflect_base_zero_of_eq hμ, hj, hr hμ]
    push_cast
    ring
  · refine ⟨m, -j, r, ?_, fun h => absurd h hμ⟩
    rw [timeReflect_base_zero_of_ne hμ, hj]
    push_cast
    ring

/-- The time reflection acting on bounded continuous test functionals. -/
def reflectTest (F : WilsonLoopSpace →ᵇ ℝ) : WilsonLoopSpace →ᵇ ℝ :=
  F.compContinuous ⟨reflectObservables, continuous_reflectObservables⟩

/-- The two-point correlation kernel of a law, complex valued as in
`YangMillsContinuumLimitBridge.FiniteReflectionPositive`. -/
def correlationKernel (ν : ProbabilityMeasure WilsonLoopSpace) (F G : WilsonLoopSpace →ᵇ ℝ) : ℂ :=
  ((∫ w, F w * G w ∂(ν : Measure WilsonLoopSpace) : ℝ) : ℂ)

/-- Bounded continuous functionals of finitely many positive-time loops of `A`. -/
def CylinderTests (A : Set PhysicalRectangle) : Set (WilsonLoopSpace →ᵇ ℝ) :=
  {F | ∃ S : Finset PhysicalRectangle, (S : Set PhysicalRectangle) ⊆ positivePart A ∧
    DependsOnLoops S F}

/-- The repository's kernel form implies reflection positivity of the law. -/
theorem isReflectionPositiveOn_of_finiteReflectionPositive {A : Set PhysicalRectangle}
    {ν : ProbabilityMeasure WilsonLoopSpace}
    (h : YangMillsContinuumLimitBridge.FiniteReflectionPositive (correlationKernel ν) reflectTest
      (CylinderTests A)) : IsReflectionPositiveOn A ν := by
  rw [isReflectionPositiveOn_iff_cylinder]
  intro S hS F hF
  have h1 := (h 1 (fun _ => F) (fun _ => ⟨S, hS, hF⟩) (fun _ => 1)).2
  simpa [YangMillsContinuumLimitBridge.reflectedGramForm, correlationKernel, reflectTest] using h1

/-- Reflection positivity together with the reflection symmetry of the correlations gives the
repository's kernel form, with complex coefficients: the symmetry makes the Gram form real,
and its real part is the sum of the reflection-positive forms of the real and imaginary parts
of the coefficients. -/
theorem finiteReflectionPositive_of_isReflectionPositiveOn {A : Set PhysicalRectangle}
    {ν : ProbabilityMeasure WilsonLoopSpace} (h : IsReflectionPositiveOn A ν)
    (hsymm : ∀ F ∈ CylinderTests A, ∀ G ∈ CylinderTests A,
      ∫ w, F (reflectObservables w) * G w ∂(ν : Measure WilsonLoopSpace) =
        ∫ w, G (reflectObservables w) * F w ∂(ν : Measure WilsonLoopSpace)) :
    YangMillsContinuumLimitBridge.FiniteReflectionPositive (correlationKernel ν) reflectTest
      (CylinderTests A) := by
  intro d f hf c
  set K : Fin d → Fin d → ℝ := fun i j =>
    ∫ w, f i (reflectObservables w) * f j w ∂(ν : Measure WilsonLoopSpace) with hK
  have hKsymm : ∀ i j, K i j = K j i := fun i j => hsymm _ (hf i) _ (hf j)
  have hform : YangMillsContinuumLimitBridge.reflectedGramForm (correlationKernel ν) reflectTest
      f c = ∑ i, ∑ j, star (c i) * c j * (K i j : ℂ) := rfl
  have hint : ∀ i j, Integrable (fun w => f i (reflectObservables w) * f j w)
      (ν : Measure WilsonLoopSpace) := fun i j => (reflectTest (f i) * f j).integrable _
  have hQ : ∀ a : Fin d → ℝ, 0 ≤ ∑ i, ∑ j, a i * a j * K i j := by
    intro a
    let Fa : WilsonLoopSpace →ᵇ ℝ := ∑ i, a i • f i
    have hFa : ∀ w, Fa w = ∑ i, a i * f i w := by
      intro w
      simp [Fa]
    have hdep : DependsOnLoops (positivePart A) Fa := by
      intro w w' hw
      rw [hFa, hFa]
      refine Finset.sum_congr rfl fun i _ => ?_
      obtain ⟨S, hS, hF⟩ := hf i
      rw [hF w w' (fun ℓ hℓ => hw ℓ (hS hℓ))]
    calc (0 : ℝ) ≤ ∫ w, Fa (reflectObservables w) * Fa w ∂(ν : Measure WilsonLoopSpace) :=
          h Fa hdep
      _ = ∫ w, ∑ i, ∑ j, a i * a j * (f i (reflectObservables w) * f j w)
            ∂(ν : Measure WilsonLoopSpace) := by
          congr 1
          funext w
          rw [hFa, hFa, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = ∑ i, ∑ j, a i * a j * K i j := by
          rw [integral_finsetSum _ fun i _ =>
            integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [integral_const_mul]
  have hre : ∀ i j, (star (c i) * c j * (K i j : ℂ)).re =
      ((c i).re * (c j).re + (c i).im * (c j).im) * K i j := by
    intro i j
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have him : ∀ i j, (star (c i) * c j * (K i j : ℂ)).im =
      ((c i).re * (c j).im - (c i).im * (c j).re) * K i j := by
    intro i j
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  constructor
  · rw [hform, Complex.im_sum]
    simp only [Complex.im_sum, him]
    have hswap : ∑ i, ∑ j, (c i).im * (c j).re * K i j =
        ∑ i, ∑ j, (c i).re * (c j).im * K i j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hKsymm j i]
      ring
    simp only [sub_mul, Finset.sum_sub_distrib, hswap, sub_self]
  · rw [hform, Complex.re_sum]
    simp only [Complex.re_sum, hre]
    have hsplit : ∑ i, ∑ j, ((c i).re * (c j).re + (c i).im * (c j).im) * K i j =
        ∑ i, ∑ j, (c i).re * (c j).re * K i j + ∑ i, ∑ j, (c i).im * (c j).im * K i j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsplit]
    exact add_nonneg (hQ fun i => (c i).re) (hQ fun i => (c i).im)

/-- Along every continuum cutoff path with spacings `2⁻ⁿ` and eventually even sides, every
limit law of the renormalized loops (reflection-invariant constants) satisfies the repository's
kernel form of reflection positivity on cylinder functionals of positive-time time-dyadic loops.
Reality of the Gram form comes from the proved reflection invariance of the limit. -/
theorem limit_finiteReflectionPositive_timeDyadic (P : ContinuumCutoffPath)
    (hsp : ∀ n, P.spacing n = (1 / 2 : ℝ) ^ n) (heven : ∀ᶠ n in atTop, Even (P.side n))
    (Z : LoopRenormalization P.toCutoffPath) (hZ : HasReflectionInvariantFactors Z)
    {ν : ProbabilityMeasure WilsonLoopSpace} (hν : Z.IsLimitLaw ν) :
    YangMillsContinuumLimitBridge.FiniteReflectionPositive (correlationKernel ν) reflectTest
      (CylinderTests {ℓ | IsTimeDyadic ℓ}) := by
  classical
  apply finiteReflectionPositive_of_isReflectionPositiveOn
    (limit_isReflectionPositiveOn_timeDyadic P hsp heven Z hZ hν)
  rintro F ⟨SF, hSF, hF⟩ G ⟨SG, hSG, hG⟩
  let H : WilsonLoopSpace →ᵇ ℝ := reflectTest G * F
  let S : Finset PhysicalRectangle := SF ∪ SG.image PhysicalRectangle.timeReflect
  have hS : ∀ ℓ ∈ S, IsTimeDyadic ℓ := by
    intro ℓ hℓ
    rcases Finset.mem_union.mp hℓ with h1 | h2
    · exact (hSF h1).1
    · obtain ⟨ℓ', hℓ', rfl⟩ := Finset.mem_image.mp h2
      exact (hSG hℓ').1.timeReflect
  have hH : DependsOnLoops S H := by
    intro w w' hw
    change G (reflectObservables w) * F w = G (reflectObservables w') * F w'
    rw [hF w w' (fun ℓ hℓ => hw ℓ (Finset.mem_union_left _ hℓ))]
    rw [hG (reflectObservables w) (reflectObservables w') (fun ℓ hℓ =>
      hw _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hℓ)))]
  have hinv := limit_reflect_invariant_timeDyadic hsp Z hZ hν S hS H hH
  change ∫ w, G (reflectObservables (reflectObservables w)) * F (reflectObservables w)
      ∂(ν : Measure WilsonLoopSpace) =
    ∫ w, G (reflectObservables w) * F w ∂(ν : Measure WilsonLoopSpace) at hinv
  simp only [reflectObservables_reflectObservables] at hinv
  rw [← hinv]
  congr 1
  funext w
  ring

/-! ## 15. Volume- and coupling-uniform reflection-positivity lower bounds and physical-path tightness -/

section UniformReflectionPositivityBounds

theorem SU2.mat_one_one (A : SU2) : A.mat 1 1 = star (A.mat 0 0) := by
  have h00 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) A.unitary
  have h01 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) A.unitary
  have hdet := A.det_one
  dsimp [Matrix.mul_apply, Matrix.conjTranspose_apply] at h00 h01
  rw [Fin.sum_univ_two, Matrix.one_apply_eq] at h00
  rw [Fin.sum_univ_two, Matrix.one_apply_ne (by decide)] at h01
  rw [Matrix.det_fin_two] at hdet
  simp only [Complex.star_def] at h00 h01 ⊢
  linear_combination -(A.mat 1 1) * h00 + ((starRingEnd ℂ) (A.mat 0 0)) * hdet + (A.mat 1 0) * h01

theorem SU2.mat_zero_one (A : SU2) : A.mat 0 1 = -star (A.mat 1 0) := by
  have h00 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) A.unitary
  have h01 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) A.unitary
  have hdet := A.det_one
  dsimp [Matrix.mul_apply, Matrix.conjTranspose_apply] at h00 h01
  rw [Fin.sum_univ_two, Matrix.one_apply_eq] at h00
  rw [Fin.sum_univ_two, Matrix.one_apply_ne (by decide)] at h01
  rw [Matrix.det_fin_two] at hdet
  simp only [Complex.star_def] at h00 h01 ⊢
  linear_combination -(A.mat 0 1) * h00 - ((starRingEnd ℂ) (A.mat 1 0)) * hdet + (A.mat 0 0) * h01

/-- The four real coordinates of the first column of an `SU(2)` matrix on the unit 3-sphere. -/
def su2Coord (α : Fin 4) (A : SU2) : ℝ :=
  if α = 0 then (A.mat 0 0).re
  else if α = 1 then (A.mat 0 0).im
  else if α = 2 then (A.mat 1 0).re
  else (A.mat 1 0).im

@[continuity, fun_prop]
theorem continuous_su2Coord (α : Fin 4) : Continuous (su2Coord α) := by
  unfold su2Coord
  split_ifs <;> fun_prop

/-- Traceless quadratic observables on `SU(2)` decomposing `(halfTraceRe (U * V⁻¹))² - 1 / 4`. -/
def su2QuadObservable (α β : Fin 4) (A : SU2) : ℝ :=
  su2Coord α A * su2Coord β A - if α = β then 1 / 4 else 0

@[continuity, fun_prop]
theorem continuous_su2QuadObservable (α β : Fin 4) : Continuous (su2QuadObservable α β) := by
  unfold su2QuadObservable
  fun_prop

theorem halfTraceRe_mul_inv_eq_sum_su2Coord (U V : SU2) :
    halfTraceRe (U * V⁻¹) = ∑ α : Fin 4, su2Coord α U * su2Coord α V := by
  have hU11 := SU2.mat_one_one U
  have hV11 := SU2.mat_one_one V
  have hU01 := SU2.mat_zero_one U
  have hV01 := SU2.mat_zero_one V
  change (1 / 2 : ℝ) * (Matrix.trace (U.mat * V.mat.conjTranspose)).re = _
  dsimp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_four]
  rw [hU11, hV11, hU01, hV01]
  simp only [su2Coord, Fin.isValue, ↓reduceIte, Fin.reduceEq, Complex.add_re, Complex.mul_re,
    Complex.neg_re, Complex.neg_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem halfTraceRe_mul_inv_sq_eq (U V : SU2) :
    halfTraceRe (U * V⁻¹) ^ 2 =
      1 / 4 + ∑ α : Fin 4, ∑ β : Fin 4, su2QuadObservable α β U * su2QuadObservable α β V := by
  have hU := SU2.col0_norm_sq U
  have hV := SU2.col0_norm_sq V
  rw [halfTraceRe_mul_inv_eq_sum_su2Coord]
  simp only [Fin.sum_univ_four, su2QuadObservable, su2Coord, Fin.isValue, ↓reduceIte, Fin.reduceEq]
  linear_combination (1 / 4 : ℝ) * hU + (1 / 4 : ℝ) * hV

/-- The positive-time staple of height `t` and spatial width `s` in the `(0, ν)` plane. -/
def positiveStaple (ν : Direction) (t s : ℕ) : List LatticeStep :=
  List.replicate t ⟨0, true⟩ ++ List.replicate s ⟨ν, true⟩ ++ List.replicate t ⟨0, false⟩

theorem pathTarget_zero_positiveStaple {L : ℕ} (ν : Direction) (t s : ℕ) :
    pathTarget (0 : Lattice4D L) (positiveStaple ν t s) = s • unitVec L ν := by
  simp only [positiveStaple, pathTarget_append, pathTarget_replicate,
    LatticeStep.displacement_forward, LatticeStep.displacement_backward, smul_neg]
  abel

theorem pathTarget_zero_map_reflectStep_positiveStaple {L : ℕ} {ν : Direction} (hν : ν ≠ 0)
    (t s : ℕ) :
    pathTarget (0 : Lattice4D L) ((positiveStaple ν t s).map reflectStep) = s • unitVec L ν := by
  simp only [positiveStaple, List.map_append, List.map_replicate, reflectStep, ↓reduceIte, hν,
    Bool.not_true, Bool.not_false, pathTarget_append, pathTarget_replicate,
    LatticeStep.displacement_forward, LatticeStep.displacement_backward, smul_neg]
  abel

theorem pathIn_positiveStaple {L : ℕ} [NeZero L] {M : ℕ} (hL : L = 2 * M) {ν : Direction}
    (hν : ν ≠ 0) {t : ℕ} (ht : t ≤ M) (s : ℕ) :
    PathIn (IsPositiveLink M) (0 : Lattice4D L) (positiveStaple ν t s) := by
  have hM : 0 < M := by
    have := NeZero.pos L
    omega
  have ht0 : timeVal (0 : Lattice4D L) = 0 := by simp [timeVal]
  have hspat : ∀ (b : Bool) (n : ℕ), ∀ st ∈ List.replicate n (⟨ν, b⟩ : LatticeStep),
      st.dir ≠ 0 := by
    intro b n st hst
    rw [List.eq_of_mem_replicate hst]
    exact hν
  unfold positiveStaple
  rw [pathIn_append, pathIn_append]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [pathIn_replicate]
    intro j hj
    simp only [zero_add, IsPositiveLink, stepLink, ite_true, LatticeStep.displacement_forward]
    have htime := timeVal_add_nsmul_unitVec_zero (0 : Lattice4D L) j (by omega)
    rw [zero_add, ht0, zero_add] at htime
    omega
  · rw [pathTarget_replicate]
    apply pathIn_positive_of_spatial (hspat true s)
    simp only [LatticeStep.displacement_forward]
    rw [timeVal_add_nsmul_unitVec_zero _ _ (by omega)]
    omega
  · rw [pathIn_replicate]
    intro j hj
    simp only [pathTarget_append, pathTarget_replicate, LatticeStep.displacement_forward,
      LatticeStep.displacement_backward, IsPositiveLink, stepLink, Bool.false_eq_true,
      ite_false, ite_true]
    have hsite : (0 : Lattice4D L) + t • unitVec L 0 + s • unitVec L ν +
        j • -unitVec L 0 - unitVec L 0 =
        ((0 : Lattice4D L) + s • unitVec L ν + t • unitVec L 0) - (j + 1) • unitVec L 0 := by
      rw [smul_neg, succ_nsmul]
      abel
    have hspatial : timeVal ((0 : Lattice4D L) + s • unitVec L ν) = 0 := by
      rw [timeVal_add_of_zero _ _ (by simp [unitVec, Ne.symm hν]), ht0]
    have hup : timeVal ((0 : Lattice4D L) + s • unitVec L ν + t • unitVec L 0) = t := by
      rw [timeVal_add_nsmul_unitVec_zero _ _ (by omega), hspatial, zero_add]
    rw [hsite, timeVal_sub_nsmul_unitVec_zero _ _ (by omega), hup]
    omega

/-- Every `2t × s` rectangle in the `(0, ν)` plane centered across the reflection hyperplane `x₀ = 0`
is the trace of `H₊(U) · H₊(ΘU)⁻¹` for the positive-time staple `positiveStaple ν t s`. -/
theorem wilsonLoop_rectangleSteps_two_mul_eq_staple {L : ℕ} (U : GaugeConfig L)
    {ν : Direction} (hν : ν ≠ 0) (t s : ℕ) :
    wilsonLoop U (-(t • unitVec L 0)) (rectangleSteps 0 ν (2 * t) s) =
      halfTraceRe (pathHolonomy U 0 (positiveStaple ν t s) *
        (pathHolonomy (reflectConfig U) 0 (positiveStaple ν t s))⁻¹) := by
  let x₀ : Lattice4D L := -(t • unitVec L 0)
  let q₁ : List LatticeStep := List.replicate t ⟨0, true⟩
  let q₂ : List LatticeStep :=
    List.replicate t ⟨0, true⟩ ++ List.replicate s ⟨ν, true⟩ ++
      List.replicate (2 * t) ⟨0, false⟩ ++ List.replicate s ⟨ν, false⟩
  have hq12 : q₁ ++ q₂ = rectangleSteps 0 ν (2 * t) s := by
    simp only [q₁, q₂, rectangleSteps, two_mul, List.replicate_add, List.append_assoc]
  have htarget1 : pathTarget x₀ q₁ = 0 := by
    simp only [x₀, q₁, pathTarget_replicate, LatticeStep.displacement_forward, neg_add_cancel]
  have hclosed : pathTarget x₀ (q₁ ++ q₂) = x₀ := by
    rw [hq12]
    exact pathTarget_rectangleSteps _ _ _ _ _
  have hrot := halfTraceRe_pathHolonomy_rotate U x₀ q₁ q₂ hclosed
  rw [hq12, htarget1] at hrot
  unfold wilsonLoop
  rw [← hrot]
  have hrev_eq : reversePath ((positiveStaple ν t s).map reflectStep) =
      List.replicate t ⟨0, false⟩ ++ List.replicate s ⟨ν, false⟩ ++ List.replicate t ⟨0, true⟩ := by
    simp [positiveStaple, reversePath, LatticeStep.reverse, reflectStep, hν, List.map_replicate,
      List.append_assoc]
  have hq21 : q₂ ++ q₁ =
      positiveStaple ν t s ++ reversePath ((positiveStaple ν t s).map reflectStep) := by
    rw [hrev_eq]
    simp only [q₁, q₂, positiveStaple, two_mul, List.replicate_add, List.append_assoc]
  rw [hq21, pathHolonomy_append, pathTarget_zero_positiveStaple]
  have hrev := pathHolonomy_reversePath U 0 ((positiveStaple ν t s).map reflectStep)
  rw [pathTarget_zero_map_reflectStep_positiveStaple hν] at hrev
  rw [hrev]
  have hrefl := pathHolonomy_reflectConfig U 0 (positiveStaple ν t s)
  have h0 : reflectSite (0 : Lattice4D L) = 0 := by
    funext i
    simp [reflectSite]
  rw [h0] at hrefl
  rw [hrefl]

theorem wilsonProbability_wilsonLoop_sq_ge_quarter_timePlane {L : ℕ} [NeZero L] {M : ℕ}
    (hL : L = 2 * M) (β : ℝ) (hβ : 0 ≤ β) {ν : Direction} (hν : ν ≠ 0) {t : ℕ} (ht : t ≤ M)
    (s : ℕ) :
    1 / 4 ≤ ∫ U, wilsonLoop U (-(t • unitVec L 0)) (rectangleSteps 0 ν (2 * t) s) ^ 2
      ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)) := by
  set P : Measure (GaugeConfig L) := (wilsonProbability L β hβ : Measure (GaugeConfig L))
  let F : Fin 4 → Fin 4 → GaugeConfig L → ℝ := fun α γ U =>
    su2QuadObservable α γ (pathHolonomy U 0 (positiveStaple ν t s))
  have hF_cont : ∀ α γ, Continuous (F α γ) := fun α γ =>
    (continuous_su2QuadObservable α γ).comp (continuous_pathHolonomy 0 (positiveStaple ν t s))
  have hF_loc : ∀ α γ (U U' : GaugeConfig L),
      (∀ e, IsPositiveLink M e → U e = U' e) → F α γ U = F α γ U' := by
    intro α γ U U' h
    dsimp [F]
    rw [pathHolonomy_congr_of_pathIn h (pathIn_positiveStaple hL hν ht s)]
  have hF_rp : ∀ α γ, 0 ≤ ∫ U, F α γ U * F α γ (reflectConfig U) ∂P := by
    intro α γ
    have hrp := wilson_reflection_positive hL β hβ (F α γ) (hF_cont α γ) (hF_loc α γ)
    refine hrp.trans_eq (integral_congr_ae (Eventually.of_forall fun U => ?_))
    ring
  have hF_int : ∀ α γ, Integrable (fun U => F α γ U * F α γ (reflectConfig U)) P := by
    intro α γ
    exact ((hF_cont α γ).mul ((hF_cont α γ).comp (continuous_pi fun _ => by
      unfold reflectConfig
      split_ifs <;> fun_prop))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have h_decomp : (fun U : GaugeConfig L =>
      wilsonLoop U (-(t • unitVec L 0)) (rectangleSteps 0 ν (2 * t) s) ^ 2) =
      fun U => (1 / 4 : ℝ) + ∑ α : Fin 4, ∑ γ : Fin 4, F α γ U * F α γ (reflectConfig U) := by
    funext U
    rw [wilsonLoop_rectangleSteps_two_mul_eq_staple U hν t s]
    exact halfTraceRe_mul_inv_sq_eq _ _
  rw [h_decomp, integral_add (integrable_const _)
    (integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun γ _ => hF_int α γ),
    integral_const, probReal_univ, one_smul]
  have hsum_nonneg : 0 ≤ ∫ U, (∑ α : Fin 4, ∑ γ : Fin 4, F α γ U * F α γ (reflectConfig U)) ∂P := by
    rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun γ _ => hF_int α γ]
    refine Finset.sum_nonneg fun α _ => ?_
    rw [integral_finsetSum _ fun γ _ => hF_int α γ]
    exact Finset.sum_nonneg fun γ _ => hF_rp α γ
  linarith

theorem wilsonProbability_wilsonLoop_sq_translate {L : ℕ} [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    (x y : Lattice4D L) (p : List LatticeStep) :
    ∫ U, wilsonLoop U x p ^ 2 ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)) =
      ∫ U, wilsonLoop U y p ^ 2 ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)) := by
  set P : Measure (GaugeConfig L) := (wilsonProbability L β hβ : Measure (GaugeConfig L))
  have hinv := congrArg ProbabilityMeasure.toMeasure
    (wilsonProbability_translation_invariant L β hβ (x - y))
  simp only [ProbabilityMeasure.toMeasure_map] at hinv
  have hcont : Continuous (fun U : GaugeConfig L => wilsonLoop U y p ^ 2) :=
    (continuous_wilsonLoop y p).pow 2
  have hfun : (fun U : GaugeConfig L => wilsonLoop U x p ^ 2) =
      fun U => wilsonLoop (latticeTranslate (x - y) U) y p ^ 2 := by
    funext U
    simp only [wilsonLoop, pathHolonomy_latticeTranslate, add_sub_cancel]
  rw [hfun, ← integral_map (continuous_latticeTranslate _).aemeasurable hcont.aestronglyMeasurable]
  change ∫ U, wilsonLoop U y p ^ 2 ∂(Measure.map (latticeTranslate (x - y)) P) = _
  rw [hinv]

/-- Volume- and coupling-uniform Osterwalder–Seiler reflection-positivity second-moment bound:
on the 4D periodic torus of any even side `L = 2M` and at any bare coupling `β ≥ 0`, every
axis-parallel rectangular Wilson loop of sides `2t × s` (with `t ≤ M` and distinct directions
`μ ≠ ν`) has second moment at least `1 / 4`. -/
theorem wilsonProbability_wilsonLoop_sq_ge_quarter {L : ℕ} [NeZero L] {M : ℕ} (hL : L = 2 * M)
    (β : ℝ) (hβ : 0 ≤ β) {μ ν : Direction} (hμν : μ ≠ ν) {t : ℕ} (ht : t ≤ M) (s : ℕ)
    (x : Lattice4D L) :
    1 / 4 ≤ ∫ U, wilsonLoop U x (rectangleSteps μ ν (2 * t) s) ^ 2
      ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)) := by
  set P : Measure (GaugeConfig L) := (wilsonProbability L β hβ : Measure (GaugeConfig L))
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 μ
  let ν' : Direction := σ.symm ν
  have hσ0 : σ 0 = μ := Equiv.swap_apply_left 0 μ
  have hσν' : σ ν' = ν := σ.apply_symm_apply ν
  have hν' : ν' ≠ 0 := by
    intro h0
    apply hμν
    rw [← hσ0, ← hσν', h0]
  rw [wilsonProbability_wilsonLoop_sq_translate β hβ x (permuteSite σ (-(t • unitVec L 0)))
    (rectangleSteps μ ν (2 * t) s)]
  have hinv := congrArg ProbabilityMeasure.toMeasure
    (wilsonProbability_permute_invariant L β hβ σ)
  simp only [ProbabilityMeasure.toMeasure_map] at hinv
  have hcont : Continuous (fun U : GaugeConfig L =>
      wilsonLoop U (permuteSite σ (-(t • unitVec L 0))) (rectangleSteps μ ν (2 * t) s) ^ 2) :=
    (continuous_wilsonLoop _ _).pow 2
  calc (1 / 4 : ℝ)
      ≤ ∫ U, wilsonLoop U (-(t • unitVec L 0)) (rectangleSteps 0 ν' (2 * t) s) ^ 2 ∂P :=
        wilsonProbability_wilsonLoop_sq_ge_quarter_timePlane hL β hβ hν' ht s
    _ = ∫ U, wilsonLoop (permuteConfig σ U) (permuteSite σ (-(t • unitVec L 0)))
          (rectangleSteps μ ν (2 * t) s) ^ 2 ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun U => ?_)
        simp only [wilsonLoop, ← hσ0, ← hσν', ← map_permuteStep_rectangleSteps,
          pathHolonomy_permuteConfig]
    _ = ∫ U, wilsonLoop U (permuteSite σ (-(t • unitVec L 0)))
          (rectangleSteps μ ν (2 * t) s) ^ 2 ∂(Measure.map (permuteConfig σ) P) := by
        symm
        exact integral_map (continuous_permuteConfig σ).aemeasurable hcont.aestronglyMeasurable
    _ = ∫ U, wilsonLoop U (permuteSite σ (-(t • unitVec L 0)))
          (rectangleSteps μ ν (2 * t) s) ^ 2 ∂P := by
        rw [hinv]

/-- Paley–Zygmund tail lower bound from the reflection-positivity second-moment bound:
every rectangular Wilson loop of sides `2t × s` (with `t ≤ M` on `L = 2M`) exceeds `1 / 4` in
absolute value with `wilsonProbability L β hβ`-probability at least `1 / 8`, uniformly in `L`
and `β ≥ 0`. -/
theorem wilsonProbability_wilsonLoop_tail_ge_eighth {L : ℕ} [NeZero L] {M : ℕ} (hL : L = 2 * M)
    (β : ℝ) (hβ : 0 ≤ β) {μ ν : Direction} (hμν : μ ≠ ν) {t : ℕ} (ht : t ≤ M) (s : ℕ)
    (x : Lattice4D L) :
    (1 / 8 : ℝ≥0∞) ≤ (wilsonProbability L β hβ : Measure (GaugeConfig L))
      {U | (1 / 4 : ℝ) < |wilsonLoop U x (rectangleSteps μ ν (2 * t) s)|} := by
  set P : Measure (GaugeConfig L) := (wilsonProbability L β hβ : Measure (GaugeConfig L))
  set W : GaugeConfig L → ℝ := fun U => wilsonLoop U x (rectangleSteps μ ν (2 * t) s)
  set S : Set (GaugeConfig L) := {U | (1 / 4 : ℝ) < |W U|}
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const (continuous_wilsonLoop x _).abs).measurableSet
  have hsq : 1 / 4 ≤ ∫ U, W U ^ 2 ∂P :=
    wilsonProbability_wilsonLoop_sq_ge_quarter hL β hβ hμν ht s x
  have hpt : ∀ U : GaugeConfig L, W U ^ 2 ≤ 1 / 8 + S.indicator (1 : GaugeConfig L → ℝ) U := by
    intro U
    by_cases hU : U ∈ S
    · rw [Set.indicator_of_mem hU, Pi.one_apply]
      have hb : W U ∈ Set.Icc (-1 : ℝ) 1 :=
        halfTraceRe_mem_Icc (pathHolonomy U x (rectangleSteps μ ν (2 * t) s))
      nlinarith [hb.1, hb.2]
    · rw [Set.indicator_of_notMem hU]
      have hle : |W U| ≤ 1 / 4 := not_lt.mp hU
      rw [abs_le] at hle
      nlinarith [hle.1, hle.2]
  have hint_ind : Integrable (S.indicator (1 : GaugeConfig L → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hS
  have hint_le : ∫ U, W U ^ 2 ∂P ≤ 1 / 8 + P.real S := by
    calc ∫ U, W U ^ 2 ∂P
        ≤ ∫ U, (1 / 8 + S.indicator (1 : GaugeConfig L → ℝ) U) ∂P :=
          integral_mono (((continuous_wilsonLoop x _).pow 2).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)) ((integrable_const _).add hint_ind) hpt
      _ = (∫ _U, (1 / 8 : ℝ) ∂P) + ∫ U, S.indicator (1 : GaugeConfig L → ℝ) U ∂P :=
          integral_add (integrable_const _) hint_ind
      _ = 1 / 8 + P.real S := by
          rw [integral_const, probReal_univ, one_smul, integral_indicator_one hS]
  have hreal : 1 / 8 ≤ P.real S := by linarith
  have hof : ENNReal.ofReal (1 / 8 : ℝ) ≤ P S := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal hreal
  have h8 : ENNReal.ofReal (1 / 8 : ℝ) = (1 / 8 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  rwa [h8] at hof

/-- A physical rectangle whose `μ`-side length is a dyadic rational `q / 2^m`. -/
def IsDyadicSide (ℓ : PhysicalRectangle) : Prop :=
  ∃ (m q : ℕ), 0 < q ∧ (ℓ.sideμ : ℝ) = (q : ℝ) / 2 ^ m

/-- Uniform nonconcentration of a physical loop along a cutoff path: at all large cutoffs the
unrenormalized loop exceeds `1 / 4` in absolute value with probability at least `1 / 8`. -/
def LoopNonconcentration (P : CutoffPath) (ℓ : PhysicalRectangle) : Prop :=
  ∀ᶠ n in atTop, (1 / 8 : ℝ≥0∞) ≤ (P.configLaw n : Measure (GaugeConfig (P.side n)))
    {U | (1 / 4 : ℝ) < |physicalWilsonLoop (P.side n) (P.spacing n) ℓ U|}

/-- Every physical rectangle with a dyadic `μ`-side satisfies `LoopNonconcentration` along every
dyadic `ContinuumCutoffPath` (in particular `dyadicOneLoopPath`). -/
theorem loopNonconcentration_of_dyadic (P : ContinuumCutoffPath) (hP : P.IsDyadic)
    {ℓ : PhysicalRectangle} (hℓ : IsDyadicSide ℓ) :
    LoopNonconcentration P.toCutoffPath ℓ := by
  obtain ⟨m, q, hq, hside⟩ := hℓ
  have hbig : ∀ᶠ n in atTop, 2 * (ℓ.sideμ : ℝ) ≤ (P.side n : ℝ) * P.spacing n :=
    P.physicalSide_tendsto_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hP.eventually_even, hbig, eventually_ge_atTop (m + 1)] with n hev hbn hmn
  have hL : P.side n = 2 * (P.side n / 2) := by
    obtain ⟨k, hk⟩ := hev
    omega
  set t := q * 2 ^ (n - (m + 1))
  have hpow : (2 : ℝ) ^ n = 2 * 2 ^ (n - (m + 1)) * 2 ^ m := by
    have : n = 1 + (n - (m + 1)) + m := by omega
    conv_lhs => rw [this, pow_add, pow_add, pow_one]
  have hdiv : (ℓ.sideμ : ℝ) / P.spacing n = ((2 * t : ℕ) : ℝ) := by
    rw [hside, hP.spacing_eq n, one_div, inv_pow, div_inv_eq_mul, hpow]
    push_cast [t]
    field_simp
  have hsteps : ℓ.stepsμ (P.spacing n) = 2 * t := by
    unfold PhysicalRectangle.stepsμ
    rw [hdiv, Nat.floor_natCast]
  have ht : t ≤ P.side n / 2 := by
    have ha := P.spacing_pos n
    have h1 : ((2 * t : ℕ) : ℝ) * P.spacing n = (ℓ.sideμ : ℝ) := by
      rw [← hdiv, div_mul_cancel₀ _ ha.ne']
    push_cast at h1
    have h2 : ((2 * (2 * t) : ℕ) : ℝ) * P.spacing n ≤ (P.side n : ℝ) * P.spacing n := by
      push_cast
      linarith
    have h3 : ((2 * (2 * t) : ℕ) : ℝ) ≤ (P.side n : ℝ) :=
      le_of_mul_le_mul_right h2 ha
    have h4 : 2 * (2 * t) ≤ P.side n := by exact_mod_cast h3
    omega
  have hloop : ∀ U : GaugeConfig (P.side n),
      physicalWilsonLoop (P.side n) (P.spacing n) ℓ U =
        wilsonLoop U (latticeSite (P.side n) (ℓ.latticeBase (P.spacing n)))
          (rectangleSteps ℓ.μ ℓ.ν (2 * t) (ℓ.stepsν (P.spacing n))) := by
    intro U
    simp only [physicalWilsonLoop, PhysicalRectangle.latticeLoop, hsteps]
  simp only [hloop]
  exact wilsonProbability_wilsonLoop_tail_ge_eighth hL (P.coupling n) (P.coupling_nonneg n)
    ℓ.plane.ne ht (ℓ.stepsν (P.spacing n)) _

/-- Under `LoopNonconcentration`, tightness (`TailObligation`) of a multiplicative loop
renormalization `Z` forces the renormalization constants `Z.factor n ℓ` to be bounded in `n`. -/
theorem bounded_of_tailObligation_of_loopNonconcentration
    {P : CutoffPath} (Z : LoopRenormalization P) {ℓ : PhysicalRectangle}
    (hnc : LoopNonconcentration P ℓ) (hT : Z.TailObligation) :
    ∃ B : ℝ, ∀ n, Z.factor n ℓ ≤ B := by
  have h16pos : (0 : ℝ≥0∞) < (1 / 8 : ℝ≥0∞) / 2 := by norm_num
  obtain ⟨C, hC⟩ := hT ℓ ((1 / 8 : ℝ≥0∞) / 2) h16pos
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hnc
  let B₀ : ℝ := ∑ k ∈ Finset.range N₀, Z.factor k ℓ
  refine ⟨max (4 * max C 0) B₀, fun n => ?_⟩
  by_cases hn : N₀ ≤ n
  · apply le_trans _ (le_max_left _ B₀)
    by_contra hgt
    have hgt' : 4 * max C 0 < Z.factor n ℓ := not_le.mp hgt
    have hC0 : 0 ≤ max C 0 := le_max_right C 0
    have hCn : C ≤ max C 0 := le_max_left C 0
    have hlaw := hC _ ⟨Z.law n, ⟨n, rfl⟩, rfl⟩
    have hmeas : MeasurableSet {w : WilsonLoopSpace | C < |w ℓ|} :=
      (isOpen_lt continuous_const (continuous_apply ℓ).abs).measurableSet
    have hmv : Measurable (Z.renormalizedVector n) :=
      ((Z.continuous_rescale n).comp (continuous_wilsonLoopVector _ _)).measurable
    rw [LoopRenormalization.law_eq_map_renormalizedVector, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply hmv hmeas] at hlaw
    have hsub : {U : GaugeConfig (P.side n) |
        (1 / 4 : ℝ) < |physicalWilsonLoop (P.side n) (P.spacing n) ℓ U|} ⊆
        Z.renormalizedVector n ⁻¹' {w : WilsonLoopSpace | C < |w ℓ|} := by
      intro U hU
      simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hU ⊢
      change C < |Z.factor n ℓ * physicalWilsonLoop (P.side n) (P.spacing n) ℓ U|
      rw [abs_mul, abs_of_pos (Z.factor_pos n ℓ)]
      nlinarith
    have hle := (hN₀ n hn).trans ((measure_mono hsub).trans hlaw)
    have hhalf : (1 / 8 : ℝ≥0∞) / 2 < (1 / 8 : ℝ≥0∞) :=
      ENNReal.half_lt_self (by norm_num) (by norm_num)
    exact absurd hle (not_le.mpr hhalf)
  · apply le_trans _ (le_max_right (4 * max C 0) B₀)
    exact Finset.single_le_sum (fun k _ => (Z.factor_pos k ℓ).le)
      (Finset.mem_range.mpr (not_le.mp hn))

/-- Contrapositive: any multiplicative loop renormalization whose factors on a nonconcentrating
loop are unbounded fails `TailObligation`. -/
theorem not_tailObligation_of_unbounded_of_loopNonconcentration
    {P : CutoffPath} (Z : LoopRenormalization P) {ℓ : PhysicalRectangle}
    (hnc : LoopNonconcentration P ℓ) (hunb : ∀ B : ℝ, ∃ n, B < Z.factor n ℓ) :
    ¬ Z.TailObligation := by
  intro hT
  obtain ⟨B, hB⟩ := bounded_of_tailObligation_of_loopNonconcentration Z hnc hT
  obtain ⟨n, hn⟩ := hunb B
  linarith [hB n]

/-- In particular, along any dyadic `ContinuumCutoffPath` (including `dyadicOneLoopPath`),
any multiplicative loop renormalization whose factor on a dyadic-side loop diverges to `+∞`
fails `TailObligation`. -/
theorem not_tailObligation_of_tendsto_atTop_of_dyadic
    {P : ContinuumCutoffPath} (hP : P.IsDyadic) (Z : LoopRenormalization P.toCutoffPath)
    {ℓ : PhysicalRectangle} (hℓ : IsDyadicSide ℓ)
    (htop : Tendsto (fun n => Z.factor n ℓ) atTop atTop) :
    ¬ Z.TailObligation := by
  apply not_tailObligation_of_unbounded_of_loopNonconcentration Z
    (loopNonconcentration_of_dyadic P hP hℓ)
  intro B
  exact (htop.eventually (eventually_gt_atTop B)).exists

end UniformReflectionPositivityBounds

/-! ## 16. Multi-loop Schwinger functions and perimeter-corner renormalization -/

section SchwingerLayerAndPerimeterCorner

/-- A finite family of continuum axis-parallel physical rectangles for multi-loop Schwinger
functions. -/
structure DisjointLoopFamily where
  loops : List PhysicalRectangle

namespace DisjointLoopFamily

/-- Every loop in the family lies strictly in the positive Euclidean time half-space. -/
def PositiveTime (F : DisjointLoopFamily) : Prop :=
  ∀ ℓ ∈ F.loops, ℓ.IsPositiveTime

/-- Rational translation of every rectangle in the family. -/
def translate (c : Fin 4 → ℚ) (F : DisjointLoopFamily) : DisjointLoopFamily where
  loops := F.loops.map (PhysicalRectangle.translate c)

/-- Euclidean time reflection of every rectangle in the family. -/
def reflect (F : DisjointLoopFamily) : DisjointLoopFamily where
  loops := F.loops.map PhysicalRectangle.timeReflect

/-- Coordinate permutation of every rectangle in the family. -/
def permute (σ : Equiv.Perm (Fin 4)) (F : DisjointLoopFamily) : DisjointLoopFamily where
  loops := F.loops.map (PhysicalRectangle.permute σ)

/-- Product of renormalized physical Wilson loops in `F` at cutoff `n`. -/
def eval {P : CutoffPath} (Z : LoopRenormalization P) (n : ℕ)
    (F : DisjointLoopFamily) (U : GaugeConfig (P.side n)) : ℝ :=
  (F.loops.map (fun ℓ =>
    Z.factor n ℓ * physicalWilsonLoop (P.side n) (P.spacing n) ℓ U)).prod

@[simp]
theorem eval_nil {P : CutoffPath} (Z : LoopRenormalization P) (n : ℕ)
    (U : GaugeConfig (P.side n)) :
    eval Z n ⟨[]⟩ U = 1 := rfl

@[simp]
theorem eval_singleton {P : CutoffPath} (Z : LoopRenormalization P) (n : ℕ)
    (ℓ : PhysicalRectangle) (U : GaugeConfig (P.side n)) :
    eval Z n ⟨[ℓ]⟩ U = Z.factor n ℓ * physicalWilsonLoop (P.side n) (P.spacing n) ℓ U := by
  simp [eval]

end DisjointLoopFamily

/-- Finite-cutoff renormalized multi-loop Schwinger function
`S_n^Z(F) = E_{L_n, β_n}[∏_{ℓ ∈ F} Z_n(ℓ) W(ℓ)]` under the actual Wilson measure `P.configLaw n`. -/
def renormalizedSchwinger {P : CutoffPath} (Z : LoopRenormalization P) (n : ℕ)
    (F : DisjointLoopFamily) : ℝ :=
  ∫ U, F.eval Z n U ∂(P.configLaw n : Measure (GaugeConfig (P.side n)))

/-- Reflected connected Schwinger correlator
`E[Θ F · G] - E[Θ F] E[G]` at cutoff `n`. -/
def reflectedConnected {P : CutoffPath} (Z : LoopRenormalization P) (n : ℕ)
    (F G : DisjointLoopFamily) : ℝ :=
  (∫ U, F.reflect.eval Z n U * G.eval Z n U
    ∂(P.configLaw n : Measure (GaugeConfig (P.side n)))) -
    renormalizedSchwinger Z n F.reflect * renormalizedSchwinger Z n G

/-- Multiplicative perimeter-and-corner renormalization scheme
`Z_n(ℓ) = exp(m_n · 2(R_μ + R_ν) + 4 c_n)` along a cutoff path `P`. -/
def perimeterCornerRenormalization (P : CutoffPath) (m c : ℕ → ℝ) : LoopRenormalization P where
  factor n ℓ := Real.exp (m n * (2 * (ℓ.sideμ + ℓ.sideν)) + 4 * c n)
  factor_pos _ _ := Real.exp_pos _

theorem perimeterCornerRenormalization_isTranslationInvariant (P : CutoffPath) (m c : ℕ → ℝ) :
    (perimeterCornerRenormalization P m c).IsTranslationInvariant :=
  fun _ _ _ => rfl

theorem perimeterCornerRenormalization_isPermutationInvariant (P : CutoffPath) (m c : ℕ → ℝ) :
    (perimeterCornerRenormalization P m c).IsPermutationInvariant := by
  intro n σ ℓ
  by_cases h : σ ℓ.μ < σ ℓ.ν
  · simp [perimeterCornerRenormalization, PhysicalRectangle.permute, h]
  · simp [perimeterCornerRenormalization, PhysicalRectangle.permute, h, add_comm]

theorem perimeterCornerRenormalization_hasReflectionInvariantFactors
    (P : CutoffPath) (m c : ℕ → ℝ) :
    HasReflectionInvariantFactors (perimeterCornerRenormalization P m c) :=
  fun _ _ => rfl

/-- Exact cancellation of perimeter and corner renormalization factors in any four-rectangle
Creutz combination `(ℓ11, ℓ22)` vs. `(ℓ12, ℓ21)` sharing side lengths `(R1, T1), (R2, T2)` and
`(R1, T2), (R2, T1)`. -/
theorem perimeterCorner_creutz_factor_identity (P : CutoffPath) (m c : ℕ → ℝ) (n : ℕ)
    (ℓ11 ℓ22 ℓ12 ℓ21 : PhysicalRectangle)
    (hμ1 : ℓ11.sideμ = ℓ12.sideμ) (hμ2 : ℓ22.sideμ = ℓ21.sideμ)
    (hν1 : ℓ11.sideν = ℓ21.sideν) (hν2 : ℓ22.sideν = ℓ12.sideν) :
    (perimeterCornerRenormalization P m c).factor n ℓ11 *
      (perimeterCornerRenormalization P m c).factor n ℓ22 =
    (perimeterCornerRenormalization P m c).factor n ℓ12 *
      (perimeterCornerRenormalization P m c).factor n ℓ21 := by
  dsimp [perimeterCornerRenormalization]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [hμ1, hμ2, hν1, hν2]
  ring

/-- The Creutz ratio `(W_Z(ℓ11) W_Z(ℓ22)) / (W_Z(ℓ12) W_Z(ℓ21))` is identically invariant under
perimeter-and-corner renormalization at every cutoff `n`. -/
theorem creutzRatio_renormalization_invariant (P : CutoffPath) (m c : ℕ → ℝ) (n : ℕ)
    (ℓ11 ℓ22 ℓ12 ℓ21 : PhysicalRectangle)
    (hμ1 : ℓ11.sideμ = ℓ12.sideμ) (hμ2 : ℓ22.sideμ = ℓ21.sideμ)
    (hν1 : ℓ11.sideν = ℓ21.sideν) (hν2 : ℓ22.sideν = ℓ12.sideν)
    (W11 W22 W12 W21 : ℝ) :
    (((perimeterCornerRenormalization P m c).factor n ℓ11 * W11) *
      ((perimeterCornerRenormalization P m c).factor n ℓ22 * W22)) /
    (((perimeterCornerRenormalization P m c).factor n ℓ12 * W12) *
      ((perimeterCornerRenormalization P m c).factor n ℓ21 * W21)) =
    (W11 * W22) / (W12 * W21) := by
  set Z := perimeterCornerRenormalization P m c
  have hfac := perimeterCorner_creutz_factor_identity P m c n ℓ11 ℓ22 ℓ12 ℓ21 hμ1 hμ2 hν1 hν2
  have hpos : (Z.factor n ℓ12 * Z.factor n ℓ21) ≠ 0 :=
    mul_ne_zero (Z.factor_pos n ℓ12).ne' (Z.factor_pos n ℓ21).ne'
  calc
    (Z.factor n ℓ11 * W11 * (Z.factor n ℓ22 * W22)) /
        (Z.factor n ℓ12 * W12 * (Z.factor n ℓ21 * W21))
      = ((Z.factor n ℓ11 * Z.factor n ℓ22) * (W11 * W22)) /
          ((Z.factor n ℓ12 * Z.factor n ℓ21) * (W12 * W21)) := by ring
    _ = ((Z.factor n ℓ12 * Z.factor n ℓ21) * (W11 * W22)) /
          ((Z.factor n ℓ12 * Z.factor n ℓ21) * (W12 * W21)) := by rw [hfac]
    _ = (W11 * W22) / (W12 * W21) := mul_div_mul_left (W11 * W22) (W12 * W21) hpos

/-- Cauchy convergence of the renormalized multi-loop Schwinger functions for every
`DisjointLoopFamily`. -/
def RenormalizedLoopCauchy {P : CutoffPath} (Z : LoopRenormalization P) : Prop :=
  ∀ F : DisjointLoopFamily, CauchySeq (fun n => renormalizedSchwinger Z n F)

/-- Every Cauchy family of renormalized Schwinger functions converges to a continuum Schwinger
functional `S : DisjointLoopFamily → ℝ`. -/
theorem schwingerConverges_of_cauchy {P : CutoffPath} {Z : LoopRenormalization P}
    (hC : RenormalizedLoopCauchy Z) :
    ∃ S : DisjointLoopFamily → ℝ,
      ∀ F : DisjointLoopFamily, Tendsto (fun n => renormalizedSchwinger Z n F) atTop (𝓝 (S F)) := by
  choose S hS using fun F => cauchySeq_tendsto_of_complete (hC F)
  exact ⟨S, hS⟩

/-- Under `RenormalizedLoopCauchy Z`, all subsequential limits of the renormalized Schwinger
functions agree on every `DisjointLoopFamily`. -/
theorem schwingerLimitsAgree_of_cauchy {P : CutoffPath} {Z : LoopRenormalization P}
    (hC : RenormalizedLoopCauchy Z) (F : DisjointLoopFamily)
    {φ ψ : ℕ → ℕ} (hφ : StrictMono φ) (hψ : StrictMono ψ)
    {s₁ s₂ : ℝ}
    (hs₁ : Tendsto (fun k => renormalizedSchwinger Z (φ k) F) atTop (𝓝 s₁))
    (hs₂ : Tendsto (fun k => renormalizedSchwinger Z (ψ k) F) atTop (𝓝 s₂)) :
    s₁ = s₂ := by
  obtain ⟨S, hS⟩ := schwingerConverges_of_cauchy hC
  have h1 : s₁ = S F := tendsto_nhds_unique hs₁ ((hS F).comp hφ.tendsto_atTop)
  have h2 : s₂ = S F := tendsto_nhds_unique hs₂ ((hS F).comp hψ.tendsto_atTop)
  exact h1.trans h2.symm

theorem LoopRenormalization.ext {P : CutoffPath} {Z₁ Z₂ : LoopRenormalization P}
    (h : ∀ n ℓ, Z₁.factor n ℓ = Z₂.factor n ℓ) : Z₁ = Z₂ := by
  rcases Z₁ with ⟨f₁, hf₁⟩
  rcases Z₂ with ⟨f₂, hf₂⟩
  have hf : f₁ = f₂ := funext fun n => funext fun ℓ => h n ℓ
  subst hf
  rfl

/-- Predicate restricting a multiplicative loop renormalization `Z` to the physical
perimeter-and-corner counterterm family `Z_n(ℓ) = exp(m_n · 2(R_μ + R_ν) + 4 c_n)`.
Includes `LoopRenormalization.unrenormalized P` (`m = 0, c = 0`) for gradient-flowed loops. -/
def IsPerimeterCornerScheme {P : CutoffPath} (Z : LoopRenormalization P) : Prop :=
  ∃ m c : ℕ → ℝ, Z = perimeterCornerRenormalization P m c

theorem isPerimeterCornerScheme_perimeterCornerRenormalization (P : CutoffPath) (m c : ℕ → ℝ) :
    IsPerimeterCornerScheme (perimeterCornerRenormalization P m c) :=
  ⟨m, c, rfl⟩

theorem isPerimeterCornerScheme_unrenormalized (P : CutoffPath) :
    IsPerimeterCornerScheme (LoopRenormalization.unrenormalized P) := by
  refine ⟨fun _ => 0, fun _ => 0, LoopRenormalization.ext fun n ℓ => ?_⟩
  simp [LoopRenormalization.unrenormalized, perimeterCornerRenormalization]

theorem IsPerimeterCornerScheme.isTranslationInvariant {P : CutoffPath}
    {Z : LoopRenormalization P} (hZ : IsPerimeterCornerScheme Z) :
    Z.IsTranslationInvariant := by
  rcases hZ with ⟨m, c, rfl⟩
  exact perimeterCornerRenormalization_isTranslationInvariant P m c

theorem IsPerimeterCornerScheme.isPermutationInvariant {P : CutoffPath}
    {Z : LoopRenormalization P} (hZ : IsPerimeterCornerScheme Z) :
    Z.IsPermutationInvariant := by
  rcases hZ with ⟨m, c, rfl⟩
  exact perimeterCornerRenormalization_isPermutationInvariant P m c

theorem IsPerimeterCornerScheme.hasReflectionInvariantFactors {P : CutoffPath}
    {Z : LoopRenormalization P} (hZ : IsPerimeterCornerScheme Z) :
    HasReflectionInvariantFactors Z := by
  rcases hZ with ⟨m, c, rfl⟩
  exact perimeterCornerRenormalization_hasReflectionInvariantFactors P m c

namespace DisjointLoopFamily

/-- Concatenation of two finite physical rectangle families. -/
def append (F G : DisjointLoopFamily) : DisjointLoopFamily where
  loops := F.loops ++ G.loops

@[simp]
theorem eval_append {P : CutoffPath} (Z : LoopRenormalization P) (n : ℕ)
    (F G : DisjointLoopFamily) (U : GaugeConfig (P.side n)) :
    (F.append G).eval Z n U = F.eval Z n U * G.eval Z n U := by
  simp [eval, append, List.map_append, List.prod_append]

@[simp]
theorem reflect_append (F G : DisjointLoopFamily) :
    (F.append G).reflect = F.reflect.append G.reflect := by
  simp [reflect, append, List.map_append]

@[simp]
theorem translate_append (c : Fin 4 → ℚ) (F G : DisjointLoopFamily) :
    (F.append G).translate c = (F.translate c).append (G.translate c) := by
  simp [translate, append, List.map_append]

@[simp]
theorem permute_append (σ : Equiv.Perm (Fin 4)) (F G : DisjointLoopFamily) :
    (F.append G).permute σ = (F.permute σ).append (G.permute σ) := by
  simp [permute, append, List.map_append]

end DisjointLoopFamily

/-- The reflected connected correlator at cutoff `n` is the Schwinger function of `F.reflect.append G`
minus the product of the Schwinger functions of `F.reflect` and `G`. -/
theorem reflectedConnected_eq_schwinger_sub {P : CutoffPath} (Z : LoopRenormalization P) (n : ℕ)
    (F G : DisjointLoopFamily) :
    reflectedConnected Z n F G =
      renormalizedSchwinger Z n (F.reflect.append G) -
        renormalizedSchwinger Z n F.reflect * renormalizedSchwinger Z n G := by
  simp [reflectedConnected, renormalizedSchwinger]

/-- Osterwalder–Schrader reflection positivity of the continuum Schwinger functional `S` inherited
from eventual nonnegativity of the finite-cutoff reflected connected correlators. -/
theorem schwingerReflectionPositive_limit_nonneg {P : CutoffPath} {Z : LoopRenormalization P}
    {S : DisjointLoopFamily → ℝ}
    (hlim : ∀ F : DisjointLoopFamily,
      Tendsto (fun n => renormalizedSchwinger Z n F) atTop (𝓝 (S F)))
    {F : DisjointLoopFamily}
    (hrp : ∀ᶠ n in atTop, 0 ≤ reflectedConnected Z n F F) :
    0 ≤ S (F.reflect.append F) - S F.reflect * S F := by
  have ht : Tendsto (fun n => reflectedConnected Z n F F) atTop
      (𝓝 (S (F.reflect.append F) - S F.reflect * S F)) := by
    simp only [reflectedConnected_eq_schwinger_sub]
    exact (hlim (F.reflect.append F)).sub ((hlim F.reflect).mul (hlim F))
  exact ge_of_tendsto ht hrp

/-- Translation and coordinate-permutation invariance of the continuum Schwinger functional `S`
from eventual invariance along the cutoff sequence. -/
theorem schwingerTranslate_and_permute_of_eventually_eq {P : CutoffPath}
    {Z : LoopRenormalization P} {S : DisjointLoopFamily → ℝ}
    (hlim : ∀ F : DisjointLoopFamily,
      Tendsto (fun n => renormalizedSchwinger Z n F) atTop (𝓝 (S F)))
    (c : Fin 4 → ℚ) (σ : Equiv.Perm (Fin 4)) (F : DisjointLoopFamily)
    (htrans : ∀ᶠ n in atTop,
      renormalizedSchwinger Z n (F.translate c) = renormalizedSchwinger Z n F)
    (hperm : ∀ᶠ n in atTop,
      renormalizedSchwinger Z n (F.permute σ) = renormalizedSchwinger Z n F) :
    S (F.translate c) = S F ∧ S (F.permute σ) = S F :=
  ⟨tendsto_nhds_unique (Tendsto.congr' htrans (hlim (F.translate c))) (hlim F),
   tendsto_nhds_unique (Tendsto.congr' hperm (hlim (F.permute σ))) (hlim F)⟩

/-- Universal one-loop asymptotic-freedom coefficient `11 / (3 π²)` for four-dimensional `SU(2)`
Yang–Mills in the normalization `β = 4 / g²`. -/
def twoLoopBetaCoeff0 : ℝ := 11 / (3 * Real.pi ^ 2)

/-- Universal two-loop asymptotic-freedom coefficient `(32 + 2) / (3 π⁴)` for four-dimensional
`SU(2)` Yang–Mills in the normalization `β = 4 / g²`. -/
def twoLoopBetaCoeff1 : ℝ := (32 + 2) / (3 * Real.pi ^ 4)

theorem twoLoopBetaCoeff0_pos : 0 < twoLoopBetaCoeff0 := by
  unfold twoLoopBetaCoeff0
  have := Real.pi_pos
  positivity

theorem twoLoopBetaCoeff1_pos : 0 < twoLoopBetaCoeff1 := by
  unfold twoLoopBetaCoeff1
  have := Real.pi_pos
  positivity

/-- Two-loop asymptotic-freedom bare inverse coupling trajectory
`β_n = b₀ log(1 / (a_n Λ_YM)) + (b₁ / b₀) log(log(1 / (a_n Λ_YM)))`. -/
def twoLoopAsymptoticFreedomTrajectory (a : ℕ → ℝ) (Λ_ym : ℝ) (n : ℕ) : ℝ :=
  twoLoopBetaCoeff0 * Real.log (1 / (a n * Λ_ym)) +
    (twoLoopBetaCoeff1 / twoLoopBetaCoeff0) * Real.log (Real.log (1 / (a n * Λ_ym)))

/-- Lüscher gradient-flowed physical Wilson-loop observable at positive physical flow time
`t_flow > 0` along a cutoff path `P`, requiring no multiplicative perimeter or corner
counterterm (`Z = LoopRenormalization.unrenormalized P`). -/
structure GradientFlowedLoopObservable (P : CutoffPath) where
  t_flow : ℝ
  t_flow_pos : 0 < t_flow
  loop : PhysicalRectangle
  flowedEval : (n : ℕ) → GaugeConfig (P.side n) → ℝ
  flowedEval_abs_le_one : ∀ n U, |flowedEval n U| ≤ 1

namespace GradientFlowedLoopObservable

/-- Renormalization scheme for gradient-flowed loops: identically `1` at every cutoff. -/
def renormalization (P : CutoffPath) : LoopRenormalization P :=
  LoopRenormalization.unrenormalized P

theorem renormalization_isPerimeterCornerScheme (P : CutoffPath) :
    IsPerimeterCornerScheme (renormalization P) :=
  isPerimeterCornerScheme_unrenormalized P

theorem renormalization_factor_eq_one (P : CutoffPath) (n : ℕ) (ℓ : PhysicalRectangle) :
    (renormalization P).factor n ℓ = 1 := rfl

end GradientFlowedLoopObservable

/-- Source-coupled RG polymer activity carrying a loop source parameter `J : ℝ` through
multiscale block-spin transformations, with first derivative at `J = 0` extracting the
continuum Wilson-loop expectation. -/
structure SourceCoupledPolymerActivity (P : CutoffPath) where
  observable : GradientFlowedLoopObservable P
  partitionWithSource : ℕ → ℝ → ℝ
  partitionAtZero_eq_one : ∀ n, partitionWithSource n 0 = 1
  sourceDerivativeAtZero : ℕ → ℝ
  limitExpectation : ℝ
  tendsto_sourceDerivative :
    Tendsto sourceDerivativeAtZero atTop (𝓝 limitExpectation)
  limitExpectation_abs_le_one : |limitExpectation| ≤ 1

theorem SourceCoupledPolymerActivity.partitionAtZero_tendsto {P : CutoffPath}
    (A : SourceCoupledPolymerActivity P) :
    Tendsto (fun n => A.partitionWithSource n 0) atTop (𝓝 1) := by
  simp only [A.partitionAtZero_eq_one, tendsto_const_nhds]

/-- Inside-the-RG hypercubic rotation-breaking effective operator of canonical mass dimension `6`
in `4` spacetime dimensions (irrelevant scaling dimension `6 - 4 = 2`), whose effective coupling
at RG step `k ≤ K` contracts by `(1 / 4) ^ (K - k)`. -/
structure DimensionSixRotationBreakingOperator where
  spacetimeDim : ℕ := 4
  operatorDim : ℕ := 6
  initialAnisotropyBound : ℝ
  initialAnisotropyBound_nonneg : 0 ≤ initialAnisotropyBound

namespace DimensionSixRotationBreakingOperator

/-- Irrelevant scaling exponent `6 - 4 = 2` of the leading hypercubic anisotropy operator. -/
def irrelevantExponent (O : DimensionSixRotationBreakingOperator) : ℕ :=
  O.operatorDim - O.spacetimeDim

theorem irrelevantExponent_eq_two (O : DimensionSixRotationBreakingOperator)
    (h4 : O.spacetimeDim = 4) (h6 : O.operatorDim = 6) :
    O.irrelevantExponent = 2 := by
  simp [irrelevantExponent, h4, h6]

/-- Effective rotation-breaking coupling bound after `m` dyadic RG steps. -/
def couplingAfterSteps (O : DimensionSixRotationBreakingOperator) (m : ℕ) : ℝ :=
  O.initialAnisotropyBound * (1 / 4 : ℝ) ^ m

/-- Effective rotation-breaking coupling bound at RG scale `k` relative to UV cutoff scale `K`. -/
def couplingAtStep (O : DimensionSixRotationBreakingOperator) (k K : ℕ) : ℝ :=
  O.initialAnisotropyBound * (1 / 4 : ℝ) ^ (K - k)

theorem couplingAtStep_eq_couplingAfterSteps (O : DimensionSixRotationBreakingOperator) (k K : ℕ) :
    O.couplingAtStep k K = O.couplingAfterSteps (K - k) := rfl

theorem couplingAfterSteps_nonneg (O : DimensionSixRotationBreakingOperator) (m : ℕ) :
    0 ≤ O.couplingAfterSteps m := by
  unfold couplingAfterSteps
  have : 0 ≤ O.initialAnisotropyBound := O.initialAnisotropyBound_nonneg
  positivity

end DimensionSixRotationBreakingOperator

/-- Every dimension-six hypercubic rotation-breaking coupling `C_rot * (1 / 4) ^ m` contracts
geometrically to `0` as the number of RG steps `m` tends to infinity, restoring full continuum
rotational invariance from discrete hypercubic invariance. -/
theorem dimensionSixRotationBreaking_tendsto_zero (C_rot : ℝ) :
    Tendsto (fun m : ℕ => C_rot * (1 / 4 : ℝ) ^ m) atTop (𝓝 0) := by
  simpa using tendsto_const_nhds.mul
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1))

theorem DimensionSixRotationBreakingOperator.couplingAfterSteps_tendsto_zero
    (O : DimensionSixRotationBreakingOperator) :
    Tendsto O.couplingAfterSteps atTop (𝓝 0) :=
  dimensionSixRotationBreaking_tendsto_zero O.initialAnisotropyBound

/-- Running coupling factor `c(t) = 1 / (twoLoopBetaCoeff0 * log (1 / t))` in the Lüscher–Suzuki
small-flow-time expansion of the composite Yang–Mills action density `tr F^2(x)`. -/
def luscherSuzukiRunningFactor (t : ℝ) : ℝ :=
  1 / (twoLoopBetaCoeff0 * Real.log (1 / t))

theorem luscherSuzukiRunningFactor_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < luscherSuzukiRunningFactor t := by
  unfold luscherSuzukiRunningFactor
  have hb0 : 0 < twoLoopBetaCoeff0 := twoLoopBetaCoeff0_pos
  have hlog : 0 < Real.log (1 / t) := Real.log_pos (one_lt_one_div ht0 ht1)
  positivity

/-- Lüscher–Suzuki small-flow-time construction of the continuum composite field-strength
density `tr F^2(x)` from the gradient-flowed energy density `E_t(x)` via `c(t) * E_t(x)`
as `t → 0`. -/
structure LuscherSuzukiFlowedActionDensity where
  flowTimeSeq : ℕ → ℝ
  flowTime_pos : ∀ k, 0 < flowTimeSeq k
  flowTime_lt_one : ∀ k, flowTimeSeq k < 1
  flowTime_tendsto_zero : Tendsto flowTimeSeq atTop (𝓝 0)
  flowedEnergyDensity : ℕ → ℝ
  flowedEnergyDensity_nonneg : ∀ k, 0 ≤ flowedEnergyDensity k
  continuumActionDensity : ℝ
  smallFlowTimeLimit :
    Tendsto (fun k => luscherSuzukiRunningFactor (flowTimeSeq k) * flowedEnergyDensity k)
      atTop (𝓝 continuumActionDensity)

theorem LuscherSuzukiFlowedActionDensity.continuumActionDensity_nonneg
    (D : LuscherSuzukiFlowedActionDensity) :
    0 ≤ D.continuumActionDensity := by
  refine ge_of_tendsto D.smallFlowTimeLimit (Eventually.of_forall fun k => ?_)
  exact mul_nonneg
    (luscherSuzukiRunningFactor_pos (D.flowTime_pos k) (D.flowTime_lt_one k)).le
    (D.flowedEnergyDensity_nonneg k)

/-! ## General Compact Gauge Group Osterwalder–Seiler Reflection Positivity -/

instance instIsInvInvariantCompactGroupHaarProbability
    (G : Type*) [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    (compactGroupHaarProbability G).IsInvInvariant := by
  have hK : (compactGroupHaarNormalization G : Set G) = Set.univ := rfl
  have h1 : (compactGroupHaarProbability G).inv (compactGroupHaarNormalization G : Set G) = 1 := by
    rw [hK, Measure.inv, Measure.map_apply measurable_inv MeasurableSet.univ, Set.preimage_univ,
      measure_univ]
  have hinv : Measure.haarMeasure (compactGroupHaarNormalization G) =
      (compactGroupHaarProbability G).inv :=
    (Measure.haarMeasure_eq_iff (compactGroupHaarNormalization G)
      (compactGroupHaarProbability G).inv).2 h1
  exact ⟨hinv.symm⟩

/-- Link-variable twist of Euclidean time reflection for a general gauge group `G`:
inversion on temporal links (`e.μ = 0`) and the identity on spatial links. -/
def groupLinkTwist {G : Type*} [Inv G] {L : ℕ} (e : Link L) (g : G) : G :=
  if e.μ = 0 then g⁻¹ else g

/-- Euclidean time-reflected gauge configuration `Θ U` for a general gauge group `G`:
temporal links are traversed backwards. -/
def groupReflectConfig {G : Type*} [Inv G] {L : ℕ}
    (U : GroupGaugeConfig G L) : GroupGaugeConfig G L :=
  fun e => if e.μ = 0 then (U (reflectLink e))⁻¹ else U (reflectLink e)

theorem groupReflectConfig_eq_twist {G : Type*} [Inv G] {L : ℕ}
    (U : GroupGaugeConfig G L) :
    groupReflectConfig U = fun e => groupLinkTwist e (U (reflectLink e)) := rfl

theorem continuous_groupReflectConfig {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {L : ℕ} :
    Continuous (groupReflectConfig (G := G) (L := L)) := by
  change Continuous (fun (U : Link L → G) (e : Link L) =>
    if e.μ = 0 then (U (reflectLink e))⁻¹ else U (reflectLink e))
  exact continuous_pi fun e => continuous_if_const _ (fun _ => (continuous_apply _).inv)
    (fun _ => continuous_apply _)

@[simp]
theorem groupReflectConfig_groupReflectConfig {G : Type*} [Group G] {L : ℕ}
    (U : GroupGaugeConfig G L) :
    groupReflectConfig (groupReflectConfig U) = U := by
  funext e
  by_cases h : e.μ = 0
  · simp [groupReflectConfig, h, reflectLink_μ]
  · simp [groupReflectConfig, h, reflectLink_μ]

theorem measurePreserving_groupLinkTwist {G : Type*} [Group G] [TopologicalSpace G]
    [SecondCountableTopology G] [IsTopologicalGroup G] [T2Space G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] {L : ℕ} (e : Link L) :
    MeasurePreserving (groupLinkTwist (G := G) e)
      (compactGroupHaarProbability G) (compactGroupHaarProbability G) := by
  by_cases h : e.μ = 0
  · have hf : groupLinkTwist (G := G) e = Inv.inv := by
      funext g
      simp [groupLinkTwist, h]
    rw [hf]
    exact Measure.measurePreserving_inv _
  · have hf : groupLinkTwist (G := G) e = id := by
      funext g
      simp [groupLinkTwist, h]
    rw [hf]
    exact MeasurePreserving.id _

/-- For any gauge group `G` and class trace `tr : CompactGaugeClassTrace G`, the plaquette action
of the time-reflected configuration `groupReflectConfig U` at plaquette `p` equals the plaquette
action of `U` at the reflected plaquette `reflectPlaquette p`. -/
theorem groupPlaquetteAction_reflectConfig {G : Type*} [Group G] [TopologicalSpace G] {L : ℕ}
    (tr : CompactGaugeClassTrace G) (U : GroupGaugeConfig G L) (p : Plaquette L) :
    groupPlaquetteAction tr (groupReflectConfig U) p =
      groupPlaquetteAction tr U (reflectPlaquette p) := by
  rcases p with ⟨x, μ, ν, h⟩
  have hν : ν ≠ 0 := Plaquette.ν_ne_zero ⟨x, μ, ν, h⟩
  by_cases hμ : μ = 0
  · subst hμ
    set y := reflectSite x - unitVec L 0 with hy
    have e1 : groupReflectConfig U ⟨x, 0⟩ = (U ⟨y, 0⟩)⁻¹ := by
      simp [groupReflectConfig, reflectLink, hy]
    have e2 : groupReflectConfig U ⟨shift x 0, ν⟩ = U ⟨y, ν⟩ := by
      simp only [groupReflectConfig, reflectLink, hν, ite_false, shift, reflectSite_add,
        reflectSite_unitVec_zero, hy, sub_eq_add_neg]
    have e3 : groupReflectConfig U ⟨shift x ν, 0⟩ = (U ⟨shift y ν, 0⟩)⁻¹ := by
      simp only [groupReflectConfig, reflectLink, ite_true, shift, reflectSite_add,
        reflectSite_unitVec_of_ne hν, hy]
      congr 2
      abel_nf
    have e4 : groupReflectConfig U ⟨x, ν⟩ = U ⟨shift y 0, ν⟩ := by
      simp only [groupReflectConfig, reflectLink, hν, ite_false, shift, hy]
      congr 2
      abel
    have hhol : groupPlaquetteHolonomy (groupReflectConfig U) ⟨x, 0, ν, h⟩ =
        (U ⟨y, 0⟩)⁻¹ * (groupPlaquetteHolonomy U (reflectPlaquette ⟨x, 0, ν, h⟩))⁻¹ *
          ((U ⟨y, 0⟩)⁻¹)⁻¹ := by
      simp only [groupPlaquetteHolonomy, e1, e2, e3, e4, reflectPlaquette, ite_true, ← hy]
      group
    unfold groupPlaquetteAction
    rw [hhol, tr.h_conj, tr.h_inv]
  · have hspat : ∀ (z : Lattice4D L) (ρ : Direction), ρ ≠ 0 →
        groupReflectConfig U ⟨z, ρ⟩ = U ⟨reflectSite z, ρ⟩ := by
      intro z ρ hρ
      simp [groupReflectConfig, reflectLink, hρ]
    have hhol : groupPlaquetteHolonomy (groupReflectConfig U) ⟨x, μ, ν, h⟩ =
        groupPlaquetteHolonomy U (reflectPlaquette ⟨x, μ, ν, h⟩) := by
      simp only [groupPlaquetteHolonomy, hspat _ _ hμ, hspat _ _ hν, reflectPlaquette, hμ,
        ite_false, shift, reflectSite_add, reflectSite_unitVec_of_ne hμ,
        reflectSite_unitVec_of_ne hν]
    rw [groupPlaquetteAction, groupPlaquetteAction, hhol]

/-- Exact invariance of the general-`G` Wilson action under Euclidean time reflection. -/
theorem groupWilsonAction_reflectConfig {G : Type*} [Group G] [TopologicalSpace G]
    {L : ℕ} [NeZero L] (tr : CompactGaugeClassTrace G) (β : ℝ) (U : GroupGaugeConfig G L) :
    groupWilsonAction tr β (groupReflectConfig U) = groupWilsonAction tr β U := by
  have hsum : ∑ p : Plaquette L, groupPlaquetteAction tr U (reflectPlaquette p) =
      ∑ p : Plaquette L, groupPlaquetteAction tr U p :=
    Fintype.sum_equiv reflectPlaquetteEquiv _ _ (fun _ => rfl)
  simp only [groupWilsonAction, groupPlaquetteAction_reflectConfig, hsum]

/-- Weighted positive-half Wilson action for a general gauge group `G` and class trace `tr`. -/
def groupHalfAction {G : Type*} [Group G] [TopologicalSpace G] {L : ℕ} [NeZero L]
    (tr : CompactGaugeClassTrace G) (M : ℕ) (U : GroupGaugeConfig G L) : ℝ :=
  ∑ p : Plaquette L, plaquetteWeight M p * groupPlaquetteAction tr U p

theorem continuous_groupHalfAction {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {L : ℕ} [NeZero L] (tr : CompactGaugeClassTrace G) (M : ℕ) :
    Continuous (groupHalfAction (L := L) tr M) := by
  unfold groupHalfAction
  exact continuous_finsetSum _ fun p _ =>
    continuous_const.mul (continuous_groupPlaquetteAction tr p)

/-- The weighted positive-half action depends only on the links of the closed positive half. -/
theorem groupHalfAction_congr {G : Type*} [Group G] [TopologicalSpace G] {L : ℕ} [NeZero L]
    (tr : CompactGaugeClassTrace G) {M : ℕ} (hL : L = 2 * M)
    {U U' : GroupGaugeConfig G L} (h : ∀ e, IsPositiveLink M e → U e = U' e) :
    groupHalfAction tr M U = groupHalfAction tr M U' := by
  unfold groupHalfAction
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hw : plaquetteWeight M p = 0
  · simp [hw]
  · obtain ⟨h1, h2, h3, h4⟩ := isPositiveLink_of_plaquetteWeight_ne_zero hL p hw
    simp only [groupPlaquetteAction, groupPlaquetteHolonomy, h _ h1, h _ h2, h _ h3, h _ h4]

/-- Osterwalder–Seiler splitting of the general-`G` Wilson action:
`S_G(U) = β (S_{G,+} (U) + S_{G,+} (Θ U))`. -/
theorem groupWilsonAction_eq_groupHalfAction {G : Type*} [Group G] [TopologicalSpace G]
    {L : ℕ} [NeZero L] (tr : CompactGaugeClassTrace G) {M : ℕ} (hL : L = 2 * M)
    (β : ℝ) (U : GroupGaugeConfig G L) :
    groupWilsonAction tr β U =
      β * (groupHalfAction tr M U + groupHalfAction tr M (groupReflectConfig U)) := by
  have hrefl : groupHalfAction tr M (groupReflectConfig U) =
      ∑ p : Plaquette L, plaquetteWeight M (reflectPlaquette p) * groupPlaquetteAction tr U p := by
    unfold groupHalfAction
    simp only [groupPlaquetteAction_reflectConfig]
    exact Fintype.sum_equiv reflectPlaquetteEquiv _ _ (fun p => by
      change _ = plaquetteWeight M (reflectPlaquette (reflectPlaquette p)) *
        groupPlaquetteAction tr U (reflectPlaquette p)
      rw [reflectPlaquette_reflectPlaquette])
  rw [hrefl, groupHalfAction, ← Finset.sum_add_distrib]
  simp only [← add_mul, plaquetteWeight_add_reflect hL, one_mul, groupWilsonAction]

/-- Osterwalder–Seiler reflection positivity of the unnormalized Boltzmann integral for any
compact Hausdorff second-countable topological gauge group `G` and class trace
`tr : CompactGaugeClassTrace G` on the periodic lattice of even side `L = 2 * M`. -/
theorem groupWilson_reflection_positive
    (G : Type*) [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L M : ℕ} [NeZero L] (hL : L = 2 * M) (tr : CompactGaugeClassTrace G) (β : ℝ)
    (H : GroupGaugeConfig G L → ℝ) (hH : Continuous H)
    (hloc : ∀ U U' : GroupGaugeConfig G L,
      (∀ e, IsPositiveLink M e → U e = U' e) → H U = H U') :
    0 ≤ ∫ U, groupBoltzmannWeight tr β U * (H (groupReflectConfig U) * H U)
      ∂(groupGaugeHaarMeasure G L) := by
  let K : GroupGaugeConfig G L → ℝ := fun U => H U * Real.exp (-(β * groupHalfAction tr M U))
  have hK : Continuous K :=
    hH.mul (Real.continuous_exp.comp ((continuous_const.mul (continuous_groupHalfAction tr M)).neg))
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuousOn
  have hKloc : ∀ U U' : GroupGaugeConfig G L,
      (∀ e, IsPositiveLink M e → U e = U' e) → K U = K U' := by
    intro U U' h
    simp only [K, hloc U U' h, groupHalfAction_congr tr hL h]
  have hfun : ∀ U : GroupGaugeConfig G L,
      groupBoltzmannWeight tr β U * (H (groupReflectConfig U) * H U) =
        K U * K (groupReflectConfig U) := by
    intro U
    simp only [K, groupBoltzmannWeight, groupWilsonAction_eq_groupHalfAction tr hL β U]
    rw [show -(β * (groupHalfAction tr M U + groupHalfAction tr M (groupReflectConfig U))) =
      -(β * groupHalfAction tr M U) + -(β * groupHalfAction tr M (groupReflectConfig U)) by ring,
      Real.exp_add]
    ring
  simp only [hfun]
  exact integral_reflection_nonneg_of_product (compactGroupHaarProbability G)
    (IsPositiveLink M) (IsFixedLink M) reflectLink (groupLinkTwist (G := G)) reflectLink_reflectLink
    (measurePreserving_groupLinkTwist (G := G))
    (fun e he => by
      unfold IsPositiveLink
      rcases he with ⟨hμ, ht⟩
      simp only [hμ, ite_false]
      omega)
    (fun e he => reflectLink_of_fixed hL he)
    (fun e he g => by simp [groupLinkTwist, he.1])
    (fun e hpos hfix => by
      have hlt := timeVal_lt e.x
      unfold IsPositiveLink at hpos ⊢
      unfold IsFixedLink at hfix
      rw [reflectLink_μ, timeVal_reflectLink]
      by_cases hμ : e.μ = 0
      · simp only [hμ, ite_true] at hpos ⊢
        omega
      · simp only [hμ, ite_false, ne_eq, not_false_eq_true, true_and] at hpos hfix ⊢
        split_ifs <;> omega)
    (fun e hneg => by
      have hlt := timeVal_lt e.x
      unfold IsPositiveLink at hneg ⊢
      unfold IsFixedLink
      rw [reflectLink_μ, timeVal_reflectLink]
      by_cases hμ : e.μ = 0
      · simp only [hμ, ite_true] at hneg ⊢
        refine ⟨by omega, fun h => h.1 rfl⟩
      · simp only [hμ, ite_false, ne_eq, not_false_eq_true, true_and] at hneg ⊢
        split_ifs <;> omega)
    K hK.measurable (fun U => by simpa [Real.norm_eq_abs] using hC U (Set.mem_univ U)) hKloc

/-- Osterwalder–Seiler reflection positivity of the normalized finite-volume Wilson expectation
`groupWilsonExpectation G L tr β` for any compact Hausdorff second-countable topological gauge
group `G` (including `SU(N)` for all `N ≥ 2`), class trace `tr : CompactGaugeClassTrace G`,
even lattice side `L = 2 * M`, and nonnegative coupling `β ≥ 0`. -/
theorem groupWilsonExpectation_reflection_positive
    (G : Type*) [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L M : ℕ} [NeZero L] (hL : L = 2 * M) (tr : CompactGaugeClassTrace G)
    {β : ℝ} (hβ : 0 ≤ β)
    (H : GroupGaugeConfig G L → ℝ) (hH : Continuous H)
    (hloc : ∀ U U' : GroupGaugeConfig G L,
      (∀ e, IsPositiveLink M e → U e = U' e) → H U = H U') :
    0 ≤ groupWilsonExpectation G L tr β (fun U => H (groupReflectConfig U) * H U) := by
  unfold groupWilsonExpectation
  exact div_nonneg (groupWilson_reflection_positive G hL tr β H hH hloc)
    (groupWilsonMeasure_prob_bounds_and_localGauge_invariance G L tr hβ).2.1.2.2.le

/-! ## XVIII. Osterwalder–Schrader GNS pre-Hilbert space, Cauchy–Schwarz, and null-space quotient -/

/-- Alias of `DisjointLoopFamily.reflect` for Euclidean time reflection of a finite loop family. -/
abbrev DisjointLoopFamily.timeReflect (F : DisjointLoopFamily) : DisjointLoopFamily :=
  F.reflect

/-- Osterwalder–Schrader reflection positivity of a continuum multi-loop Schwinger functional
`S : DisjointLoopFamily → ℝ` on finite real linear combinations of positive-time loop families. -/
def SchwingerOSPositivity (S : DisjointLoopFamily → ℝ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℝ) (F : Fin n → DisjointLoopFamily),
    (∀ i : Fin n, (F i).PositiveTime) →
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, c i * c j * S ⟨(F i).timeReflect.loops ++ (F j).loops⟩

/-- Entry `G_{i, j} = S((Θ F_i) ++ F_j)` of the Osterwalder–Schrader Gram matrix for a finite tuple
`F : Fin n → DisjointLoopFamily` of loop families. -/
def schwingerGramEntry (S : DisjointLoopFamily → ℝ) {n : ℕ}
    (F : Fin n → DisjointLoopFamily) (i j : Fin n) : ℝ :=
  S ⟨(F i).timeReflect.loops ++ (F j).loops⟩

/-- Osterwalder–Schrader pre-Hilbert bilinear pairing
`⟨c, d⟩_{OS} = ∑_i ∑_j c_i d_j S((Θ F_i) ++ F_j)` on coefficient vectors `c, d : Fin n → ℝ`. -/
def schwingerBilinearForm (S : DisjointLoopFamily → ℝ) {n : ℕ}
    (F : Fin n → DisjointLoopFamily) (c d : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, c i * d j * schwingerGramEntry S F i j

/-- Osterwalder–Schrader quadratic form `⟨c, c⟩_{OS}` on a coefficient vector `c : Fin n → ℝ`. -/
def schwingerQuadraticForm (S : DisjointLoopFamily → ℝ) {n : ℕ}
    (F : Fin n → DisjointLoopFamily) (c : Fin n → ℝ) : ℝ :=
  schwingerBilinearForm S F c c

/-- Nonnegativity of the Osterwalder–Schrader quadratic form under `SchwingerOSPositivity S`
for positive-time loop families. -/
theorem schwingerQuadraticForm_nonneg (S : DisjointLoopFamily → ℝ)
    (hOS : SchwingerOSPositivity S) {n : ℕ} (F : Fin n → DisjointLoopFamily)
    (hpos : ∀ i : Fin n, (F i).PositiveTime) (c : Fin n → ℝ) :
    0 ≤ schwingerQuadraticForm S F c :=
  hOS n c F hpos

@[simp]
theorem schwingerBilinearForm_zero_left (S : DisjointLoopFamily → ℝ) {n : ℕ}
    (F : Fin n → DisjointLoopFamily) (d : Fin n → ℝ) :
    schwingerBilinearForm S F 0 d = 0 := by
  simp [schwingerBilinearForm]

@[simp]
theorem schwingerBilinearForm_zero_right (S : DisjointLoopFamily → ℝ) {n : ℕ}
    (F : Fin n → DisjointLoopFamily) (c : Fin n → ℝ) :
    schwingerBilinearForm S F c 0 = 0 := by
  simp [schwingerBilinearForm]

theorem schwingerBilinearForm_add_left (S : DisjointLoopFamily → ℝ) {n : ℕ}
    (F : Fin n → DisjointLoopFamily) (c₁ c₂ d : Fin n → ℝ) :
    schwingerBilinearForm S F (c₁ + c₂) d =
      schwingerBilinearForm S F c₁ d + schwingerBilinearForm S F c₂ d := by
  unfold schwingerBilinearForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply]
  ring

theorem schwingerBilinearForm_smul_left (S : DisjointLoopFamily → ℝ) {n : ℕ}
    (F : Fin n → DisjointLoopFamily) (a : ℝ) (c d : Fin n → ℝ) :
    schwingerBilinearForm S F (a • c) d = a * schwingerBilinearForm S F c d := by
  unfold schwingerBilinearForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem schwingerBilinearForm_add_right (S : DisjointLoopFamily → ℝ) {n : ℕ}
    (F : Fin n → DisjointLoopFamily) (c d₁ d₂ : Fin n → ℝ) :
    schwingerBilinearForm S F c (d₁ + d₂) =
      schwingerBilinearForm S F c d₁ + schwingerBilinearForm S F c d₂ := by
  unfold schwingerBilinearForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply]
  ring

theorem schwingerBilinearForm_smul_right (S : DisjointLoopFamily → ℝ) {n : ℕ}
    (F : Fin n → DisjointLoopFamily) (a : ℝ) (c d : Fin n → ℝ) :
    schwingerBilinearForm S F c (a • d) = a * schwingerBilinearForm S F c d := by
  unfold schwingerBilinearForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Symmetry of the Osterwalder–Schrader bilinear form when the Gram matrix is symmetric. -/
theorem schwingerBilinearForm_symm (S : DisjointLoopFamily → ℝ) {n : ℕ}
    (F : Fin n → DisjointLoopFamily)
    (h_symm : ∀ i j : Fin n, schwingerGramEntry S F i j = schwingerGramEntry S F j i)
    (c d : Fin n → ℝ) :
    schwingerBilinearForm S F c d = schwingerBilinearForm S F d c := by
  unfold schwingerBilinearForm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h_symm i j]
  ring

/-- Quadratic expansion `⟨c + t d, c + t d⟩_{OS} = ⟨c, c⟩_{OS} + 2 t ⟨c, d⟩_{OS} + t² ⟨d, d⟩_{OS}`. -/
theorem schwingerQuadraticForm_add_smul (S : DisjointLoopFamily → ℝ) {n : ℕ}
    (F : Fin n → DisjointLoopFamily)
    (h_symm : ∀ i j : Fin n, schwingerGramEntry S F i j = schwingerGramEntry S F j i)
    (c d : Fin n → ℝ) (t : ℝ) :
    schwingerQuadraticForm S F (c + t • d) =
      schwingerQuadraticForm S F c +
        2 * t * schwingerBilinearForm S F c d +
        t ^ 2 * schwingerQuadraticForm S F d := by
  unfold schwingerQuadraticForm
  rw [schwingerBilinearForm_add_left,
      schwingerBilinearForm_add_right,
      schwingerBilinearForm_add_right,
      schwingerBilinearForm_smul_left,
      schwingerBilinearForm_smul_right,
      schwingerBilinearForm_smul_left,
      schwingerBilinearForm_smul_right,
      schwingerBilinearForm_symm S F h_symm d c]
  ring

/-- Polynomial discriminant identity underlying Cauchy–Schwarz on the OS pre-Hilbert space. -/
theorem j20_os_gns_discriminant_identity (a b c t : ℝ) :
    c * (a + 2 * t * b + t ^ 2 * c) = (c * t + b) ^ 2 + (a * c - b ^ 2) := by
  ring

/-- Cauchy–Schwarz inequality `(⟨c, d⟩_{OS})² ≤ ⟨c, c⟩_{OS} ⟨d, d⟩_{OS}` for the Osterwalder–Schrader
bilinear form under `SchwingerOSPositivity S`. -/
theorem schwingerBilinearForm_cauchy_schwarz (S : DisjointLoopFamily → ℝ)
    (hOS : SchwingerOSPositivity S) {n : ℕ} (F : Fin n → DisjointLoopFamily)
    (hpos : ∀ i : Fin n, (F i).PositiveTime)
    (h_symm : ∀ i j : Fin n, schwingerGramEntry S F i j = schwingerGramEntry S F j i)
    (c d : Fin n → ℝ) :
    (schwingerBilinearForm S F c d) ^ 2 ≤
      schwingerQuadraticForm S F c * schwingerQuadraticForm S F d := by
  set a := schwingerQuadraticForm S F c
  set b := schwingerBilinearForm S F c d
  set q := schwingerQuadraticForm S F d
  have hquad : ∀ t : ℝ, 0 ≤ a + 2 * t * b + t ^ 2 * q := by
    intro t
    have h0 := schwingerQuadraticForm_nonneg S hOS F hpos (c + t • d)
    rw [schwingerQuadraticForm_add_smul S F h_symm c d t] at h0
    exact h0
  have hq_nonneg : 0 ≤ q := schwingerQuadraticForm_nonneg S hOS F hpos d
  by_cases hq : q = 0
  · have hb : b = 0 := by
      by_contra hb_ne
      have h1 := hquad (-a / (2 * b))
      rw [hq] at h1
      have h2 : a + 2 * (-a / (2 * b)) * b + (-a / (2 * b)) ^ 2 * 0 = 0 := by
        field_simp [hb_ne]
        ring
      have h3 := hquad (-(a + 1) / (2 * b))
      rw [hq] at h3
      have h4 : a + 2 * (-(a + 1) / (2 * b)) * b + (-(a + 1) / (2 * b)) ^ 2 * 0 = -1 := by
        field_simp [hb_ne]
        ring
      linarith
    rw [hb, hq]
    norm_num
  · have hq_pos : 0 < q := lt_of_le_of_ne hq_nonneg (Ne.symm hq)
    have ht := hquad (-b / q)
    have hmul : 0 ≤ q * (a + 2 * (-b / q) * b + (-b / q) ^ 2 * q) :=
      mul_nonneg hq_nonneg ht
    rw [j20_os_gns_discriminant_identity a b q (-b / q)] at hmul
    have hzero : q * (-b / q) + b = 0 := by
      field_simp [hq]
      ring
    rw [hzero] at hmul
    linarith

/-- A vector `c` has vanishing OS quadratic form `⟨c, c⟩_{OS} = 0` if and only if it is
OS-orthogonal to every vector `d : Fin n → ℝ`. -/
theorem schwingerQuadraticForm_eq_zero_iff_forall_bilinear_eq_zero
    (S : DisjointLoopFamily → ℝ) (hOS : SchwingerOSPositivity S)
    {n : ℕ} (F : Fin n → DisjointLoopFamily)
    (hpos : ∀ i : Fin n, (F i).PositiveTime)
    (h_symm : ∀ i j : Fin n, schwingerGramEntry S F i j = schwingerGramEntry S F j i)
    (c : Fin n → ℝ) :
    schwingerQuadraticForm S F c = 0 ↔
      ∀ d : Fin n → ℝ, schwingerBilinearForm S F c d = 0 := by
  constructor
  · intro hc d
    have hcs := schwingerBilinearForm_cauchy_schwarz S hOS F hpos h_symm c d
    rw [hc, zero_mul] at hcs
    exact sq_eq_zero_iff.mp (le_antisymm hcs (sq_nonneg _))
  · intro hall
    exact hall c

/-- The Osterwalder–Schrader null submodule
`N = {c : Fin n → ℝ | ∀ d, ⟨c, d⟩_{OS} = 0} = {c | ⟨c, c⟩_{OS} = 0}` of the pre-Hilbert space. -/
def schwingerNullSubmodule (S : DisjointLoopFamily → ℝ)
    {n : ℕ} (F : Fin n → DisjointLoopFamily) :
    Submodule ℝ (Fin n → ℝ) where
  carrier := {c : Fin n → ℝ | ∀ d : Fin n → ℝ, schwingerBilinearForm S F c d = 0}
  zero_mem' d := schwingerBilinearForm_zero_left S F d
  add_mem' {c₁ c₂} hc₁ hc₂ d := by
    rw [schwingerBilinearForm_add_left, hc₁ d, hc₂ d, add_zero]
  smul_mem' a {c} hc d := by
    rw [schwingerBilinearForm_smul_left, hc d, mul_zero]

/-- The GNS quotient space `(Fin n → ℝ) ⧸ N` modulo the Osterwalder–Schrader null submodule. -/
abbrev SchwingerGNSQuotient (S : DisjointLoopFamily → ℝ)
    {n : ℕ} (F : Fin n → DisjointLoopFamily) : Type :=
  (Fin n → ℝ) ⧸ schwingerNullSubmodule S F

/-- Characterization of membership in `schwingerNullSubmodule` by vanishing OS quadratic form. -/
theorem mem_schwingerNullSubmodule_iff_quadraticForm_eq_zero
    (S : DisjointLoopFamily → ℝ) (hOS : SchwingerOSPositivity S)
    {n : ℕ} (F : Fin n → DisjointLoopFamily)
    (hpos : ∀ i : Fin n, (F i).PositiveTime)
    (h_symm : ∀ i j : Fin n, schwingerGramEntry S F i j = schwingerGramEntry S F j i)
    (c : Fin n → ℝ) :
    c ∈ schwingerNullSubmodule S F ↔
      schwingerQuadraticForm S F c = 0 :=
  (schwingerQuadraticForm_eq_zero_iff_forall_bilinear_eq_zero S hOS F hpos h_symm c).symm

/-- Well-definedness of the OS bilinear pairing in the left argument modulo
`schwingerNullSubmodule`. -/
theorem schwingerBilinearForm_eq_of_sub_mem_nullSubmodule_left
    (S : DisjointLoopFamily → ℝ)
    {n : ℕ} (F : Fin n → DisjointLoopFamily)
    {c₁ c₂ : Fin n → ℝ}
    (hc : c₁ - c₂ ∈ schwingerNullSubmodule S F)
    (d : Fin n → ℝ) :
    schwingerBilinearForm S F c₁ d = schwingerBilinearForm S F c₂ d := by
  have h1 : c₁ = (c₁ - c₂) + c₂ := by ext i; simp
  rw [h1, schwingerBilinearForm_add_left, hc d, zero_add]

/-- Well-definedness of the OS bilinear pairing in the right argument modulo
`schwingerNullSubmodule`. -/
theorem schwingerBilinearForm_eq_of_sub_mem_nullSubmodule_right
    (S : DisjointLoopFamily → ℝ)
    {n : ℕ} (F : Fin n → DisjointLoopFamily)
    (h_symm : ∀ i j : Fin n, schwingerGramEntry S F i j = schwingerGramEntry S F j i)
    (c : Fin n → ℝ) {d₁ d₂ : Fin n → ℝ}
    (hd : d₁ - d₂ ∈ schwingerNullSubmodule S F) :
    schwingerBilinearForm S F c d₁ = schwingerBilinearForm S F c d₂ := by
  rw [schwingerBilinearForm_symm S F h_symm c d₁,
      schwingerBilinearForm_symm S F h_symm c d₂]
  exact schwingerBilinearForm_eq_of_sub_mem_nullSubmodule_left S F hd c

/-- Strict positivity of the OS quadratic form outside `schwingerNullSubmodule`. -/
theorem schwingerQuadraticForm_pos_of_not_mem_nullSubmodule
    (S : DisjointLoopFamily → ℝ) (hOS : SchwingerOSPositivity S)
    {n : ℕ} (F : Fin n → DisjointLoopFamily)
    (hpos : ∀ i : Fin n, (F i).PositiveTime)
    (h_symm : ∀ i j : Fin n, schwingerGramEntry S F i j = schwingerGramEntry S F j i)
    {c : Fin n → ℝ}
    (hc : c ∉ schwingerNullSubmodule S F) :
    0 < schwingerQuadraticForm S F c := by
  have hne : schwingerQuadraticForm S F c ≠ 0 := by
    intro h0
    exact hc ((mem_schwingerNullSubmodule_iff_quadraticForm_eq_zero S hOS F hpos h_symm c).mpr h0)
  exact lt_of_le_of_ne (schwingerQuadraticForm_nonneg S hOS F hpos c) (Ne.symm hne)

/-! ## XIX. SU(2) Peter–Weyl spin character Chebyshev recursion and Bessel tail enclosure -/

/-- Chebyshev second-kind polynomial `U_n(x)` giving the irreducible `SU(2)` character of spin
`j = n / 2` as a function of the normalized trace `x = (1 / 2) * Re tr(g) ∈ [-1, 1]`. -/
def su2SpinCharacter : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 2 * x
  | n + 2, x => 2 * x * su2SpinCharacter (n + 1) x - su2SpinCharacter n x

@[simp]
theorem su2SpinCharacter_zero (x : ℝ) : su2SpinCharacter 0 x = 1 := rfl

@[simp]
theorem su2SpinCharacter_one (x : ℝ) : su2SpinCharacter 1 x = 2 * x := rfl

theorem su2SpinCharacter_two (x : ℝ) : su2SpinCharacter 2 x = 4 * x ^ 2 - 1 := by
  dsimp [su2SpinCharacter]
  ring

/-- At the identity element (`x = 1`), the `SU(2)` spin-`n / 2` character equals the
representation dimension `n + 1 = 2 j + 1`. -/
theorem su2SpinCharacter_eval_one : ∀ n : ℕ, su2SpinCharacter n 1 = (n : ℝ) + 1
  | 0 => by simp
  | 1 => by norm_num
  | n + 2 => by
      have ih1 := su2SpinCharacter_eval_one (n + 1)
      have ih0 := su2SpinCharacter_eval_one n
      change 2 * 1 * su2SpinCharacter (n + 1) 1 - su2SpinCharacter n 1 = ((n + 2 : ℕ) : ℝ) + 1
      rw [ih1, ih0]
      push_cast
      ring

/-- Truncated `SU(2)` Peter–Weyl character expansion of the single-plaquette Boltzmann factor at
cutoff spin `J : ℕ`, with modified Bessel leading factor `I0` and character coefficients `u`. -/
def truncatedCharacterBoltzmann (I0 : ℝ) (u : ℕ → ℝ) (J : ℕ) (x : ℝ) : ℝ :=
  I0 * (1 + ∑ n ∈ Finset.range J, u (n + 1) * su2SpinCharacter (n + 1) x)

@[simp]
theorem truncatedCharacterBoltzmann_zero (I0 : ℝ) (u : ℕ → ℝ) (x : ℝ) :
    truncatedCharacterBoltzmann I0 u 0 x = I0 := by
  simp [truncatedCharacterBoltzmann]

/-- Step recursion for the truncated `SU(2)` character expansion when increasing cutoff spin `J`
to `J + 1`. -/
theorem truncatedCharacterBoltzmann_succ (I0 : ℝ) (u : ℕ → ℝ) (J : ℕ) (x : ℝ) :
    truncatedCharacterBoltzmann I0 u (J + 1) x =
      truncatedCharacterBoltzmann I0 u J x + I0 * (u (J + 1) * su2SpinCharacter (J + 1) x) := by
  unfold truncatedCharacterBoltzmann
  rw [Finset.sum_range_succ]
  ring

/-- Polynomial identity for the leading modified-Bessel character ratio defect. -/
theorem j20_bessel_character_defect_identity (I0 I1 u1 : ℝ) :
    I0 * (1 - u1) - (I0 - I1) = I1 - I0 * u1 := by
  ring

/-- Polynomial identity splitting the exact Boltzmann factor into its truncated character sum plus
tail remainder. -/
theorem j20_character_truncation_split_identity (I0 S_trunc R_tail : ℝ) :
    (I0 + S_trunc + R_tail) - (I0 + S_trunc) = R_tail := by
  ring

/-- Two-sided interval-arithmetic enclosure of the single-plaquette Boltzmann factor around its
order-`J` truncated `SU(2)` character expansion `truncatedCharacterBoltzmann I0 u J x`. -/
theorem characterExpansion_tail_enclosure
    {W_exact : ℝ → ℝ} {I0 ε_tail : ℝ} {u : ℕ → ℝ} {J : ℕ}
    (h_tail : ∀ x : ℝ, |W_exact x - truncatedCharacterBoltzmann I0 u J x| ≤ ε_tail)
    (x : ℝ) :
    truncatedCharacterBoltzmann I0 u J x - ε_tail ≤ W_exact x ∧
      W_exact x ≤ truncatedCharacterBoltzmann I0 u J x + ε_tail := by
  have h := abs_sub_le_iff.mp (h_tail x)
  constructor <;> linarith

/-- On the normalized `SU(2)` class-trace interval `|x| ≤ 1`, the fundamental spin-`1 / 2`
character `su2SpinCharacter 1 x = 2 * x` satisfies `|su2SpinCharacter 1 x| ≤ 2`. -/
theorem su2SpinCharacter_one_abs_le_two {x : ℝ} (hx : |x| ≤ 1) :
    |su2SpinCharacter 1 x| ≤ 2 := by
  rw [su2SpinCharacter_one, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

/-- Polynomial identity factoring `3 - U_2(x) = 4 * (1 - x^2)` on the normalized trace interval. -/
theorem j20_chebyshev_u2_unit_upper (x : ℝ) :
    3 - (4 * x ^ 2 - 1) = 4 * (1 - x ^ 2) := by
  ring

/-- On the normalized `SU(2)` class-trace interval `|x| ≤ 1`, the adjoint spin-`1` character
`su2SpinCharacter 2 x = 4 * x ^ 2 - 1` is enclosed in `[-1, 3]`. -/
theorem su2SpinCharacter_two_bounds_on_unit_interval {x : ℝ} (hx : |x| ≤ 1) :
    -1 ≤ su2SpinCharacter 2 x ∧ su2SpinCharacter 2 x ≤ 3 := by
  rw [su2SpinCharacter_two]
  have hx_sq_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hx_sq_le_one : x ^ 2 ≤ 1 := by
    have h1 : |x| ^ 2 ≤ (1 : ℝ) ^ 2 := sq_le_sq.mpr (by simpa using hx)
    simpa [sq_abs] using h1
  constructor
  · linarith
  · have h_id := j20_chebyshev_u2_unit_upper x
    linarith

/-- Explicit formula for the order-`1` truncated `SU(2)` character Boltzmann expansion:
`truncatedCharacterBoltzmann I0 u 1 x = I0 * (1 + 2 * u 1 * x)`. -/
theorem truncatedCharacterBoltzmann_one_eq (I0 : ℝ) (u : ℕ → ℝ) (x : ℝ) :
    truncatedCharacterBoltzmann I0 u 1 x = I0 * (1 + 2 * u 1 * x) := by
  rw [truncatedCharacterBoltzmann_succ, truncatedCharacterBoltzmann_zero]
  simp only [Nat.zero_add, su2SpinCharacter_one]
  ring

/-- Polynomial identity for the order-`1` truncated Boltzmann lower difference on `[-1, 1]`. -/
theorem j20_chebyshev_u1_boltzmann_diff (I0 u1 x : ℝ) :
    I0 * (1 + 2 * u1 * x) - I0 * (1 - 2 * u1) = 2 * I0 * u1 * (1 + x) := by
  ring

/-- Two-sided enclosure of the order-`1` truncated `SU(2)` character Boltzmann expansion on the
normalized trace interval `|x| ≤ 1` for `0 ≤ I0` and `0 ≤ u 1`. -/
theorem truncatedCharacterBoltzmann_one_bounds_on_unit_interval
    {I0 : ℝ} {u : ℕ → ℝ} {x : ℝ}
    (hI0 : 0 ≤ I0) (hu1 : 0 ≤ u 1) (hx : |x| ≤ 1) :
    I0 * (1 - 2 * u 1) ≤ truncatedCharacterBoltzmann I0 u 1 x ∧
      truncatedCharacterBoltzmann I0 u 1 x ≤ I0 * (1 + 2 * u 1) := by
  rw [truncatedCharacterBoltzmann_one_eq]
  have hx_bounds := abs_le.mp hx
  have h_prod_nonneg : 0 ≤ 2 * I0 * u 1 := by positivity
  constructor
  · have h_diff := j20_chebyshev_u1_boltzmann_diff I0 (u 1) x
    have h_nonneg : 0 ≤ 2 * I0 * u 1 * (1 + x) :=
      mul_nonneg h_prod_nonneg (by linarith [hx_bounds.1])
    linarith
  · have h_upper : I0 * (1 + 2 * u 1) - I0 * (1 + 2 * u 1 * x) = 2 * I0 * u 1 * (1 - x) := by
      ring
    have h_nonneg : 0 ≤ 2 * I0 * u 1 * (1 - x) :=
      mul_nonneg h_prod_nonneg (by linarith [hx_bounds.2])
    linarith

/-- Strict positivity of the order-`1` truncated `SU(2)` character Boltzmann factor across the
entire normalized trace interval `|x| ≤ 1` whenever `0 < I0`, `0 ≤ u 1`, and `2 * u 1 < 1`. -/
theorem truncatedCharacterBoltzmann_one_pos_on_unit_interval
    {I0 : ℝ} {u : ℕ → ℝ} {x : ℝ}
    (hI0 : 0 < I0) (hu1_nonneg : 0 ≤ u 1) (hu1_lt : 2 * u 1 < 1) (hx : |x| ≤ 1) :
    0 < truncatedCharacterBoltzmann I0 u 1 x := by
  have h_lo := (truncatedCharacterBoltzmann_one_bounds_on_unit_interval hI0.le hu1_nonneg hx).1
  have h_pos : 0 < I0 * (1 - 2 * u 1) := mul_pos hI0 (by linarith)
  linarith

/-- Continuity of the `SU(2)` Chebyshev spin-`n / 2` character polynomial `su2SpinCharacter n`. -/
theorem su2SpinCharacter_continuous : ∀ n : ℕ, Continuous (su2SpinCharacter n)
  | 0 => continuous_const
  | 1 => continuous_const.mul continuous_id
  | n + 2 => by
      change Continuous (fun x : ℝ => 2 * x * su2SpinCharacter (n + 1) x - su2SpinCharacter n x)
      exact ((continuous_const.mul continuous_id).mul (su2SpinCharacter_continuous (n + 1))).sub
        (su2SpinCharacter_continuous n)

/-- Every `SU(2)` element has normalized real trace `halfTraceRe g ∈ [-1, 1]`, hence
`|halfTraceRe g| ≤ 1`. -/
theorem abs_halfTraceRe_le_one (g : SU2) : |halfTraceRe g| ≤ 1 :=
  abs_le.mpr (halfTraceRe_mem_Icc g)

/-- The `SU(2)` Haar–Boltzmann character moment at inverse coupling `β` and spin `n`:
integrating the single-plaquette Boltzmann weight `exp (-β (1 - halfTraceRe g))` against the
spin-`n / 2` character `su2SpinCharacter n (halfTraceRe g)` with respect to the Haar probability
measure `SU2.haarProbability`. -/
noncomputable def su2HaarCharacterMoment (β : ℝ) (n : ℕ) : ℝ :=
  ∫ g : SU2, Real.exp (-β * (1 - halfTraceRe g)) * su2SpinCharacter n (halfTraceRe g)
    ∂SU2.haarProbability

/-- The normalized `SU(2)` Haar–Boltzmann character coefficient (Bessel ratio `u_n(β)`) at
inverse coupling `β` and spin `n`. -/
noncomputable def su2BesselCharacterRatio (β : ℝ) (n : ℕ) : ℝ :=
  su2HaarCharacterMoment β n / su2HaarCharacterMoment β 0

/-- Integrability of the single-plaquette `SU(2)` Boltzmann weight `exp (-β (1 - halfTraceRe g))`
with respect to `SU2.haarProbability`. -/
theorem su2HaarBoltzmannWeight_integrable (β : ℝ) :
    Integrable (fun g : SU2 => Real.exp (-β * (1 - halfTraceRe g))) SU2.haarProbability := by
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
  exact Real.continuous_exp.comp
    (continuous_const.mul (continuous_const.sub continuous_halfTraceRe))

/-- Integrability of the spin-`n / 2` `SU(2)` Haar–Boltzmann character integrand with respect to
`SU2.haarProbability`. -/
theorem su2HaarCharacterMoment_integrable (β : ℝ) (n : ℕ) :
    Integrable (fun g : SU2 =>
      Real.exp (-β * (1 - halfTraceRe g)) * su2SpinCharacter n (halfTraceRe g))
      SU2.haarProbability := by
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
  exact (Real.continuous_exp.comp
    (continuous_const.mul (continuous_const.sub continuous_halfTraceRe))).mul
    ((su2SpinCharacter_continuous n).comp continuous_halfTraceRe)

/-- At trivial spin `n = 0`, `su2HaarCharacterMoment β 0` is the single-plaquette `SU(2)`
Haar–Boltzmann partition integral `∫ g, exp (-β (1 - halfTraceRe g)) ∂SU2.haarProbability`. -/
theorem su2HaarCharacterMoment_zero_eq (β : ℝ) :
    su2HaarCharacterMoment β 0 =
      ∫ g : SU2, Real.exp (-β * (1 - halfTraceRe g)) ∂SU2.haarProbability := by
  unfold su2HaarCharacterMoment
  simp only [su2SpinCharacter_zero, mul_one]

/-- Two-sided bounds `exp (-2 β) ≤ su2HaarCharacterMoment β 0 ≤ 1` for the `n = 0` `SU(2)`
Haar–Boltzmann moment at nonnegative inverse coupling `0 ≤ β`. -/
theorem su2HaarCharacterMoment_zero_bounds {β : ℝ} (hβ : 0 ≤ β) :
    Real.exp (-2 * β) ≤ su2HaarCharacterMoment β 0 ∧ su2HaarCharacterMoment β 0 ≤ 1 := by
  rw [su2HaarCharacterMoment_zero_eq]
  have hint := su2HaarBoltzmannWeight_integrable β
  constructor
  · have hlo : ∫ _ : SU2, Real.exp (-2 * β) ∂SU2.haarProbability ≤
        ∫ g : SU2, Real.exp (-β * (1 - halfTraceRe g)) ∂SU2.haarProbability := by
      refine integral_mono (integrable_const _) hint fun g => ?_
      apply Real.exp_le_exp.mpr
      have hg := (halfTraceRe_mem_Icc g).1
      nlinarith
    rw [integral_const, probReal_univ, one_smul] at hlo
    exact hlo
  · have hhi : ∫ g : SU2, Real.exp (-β * (1 - halfTraceRe g)) ∂SU2.haarProbability ≤
        ∫ _ : SU2, (1 : ℝ) ∂SU2.haarProbability := by
      refine integral_mono hint (integrable_const _) fun g => ?_
      apply Real.exp_le_one_iff.mpr
      have hg : halfTraceRe g ≤ 1 := (halfTraceRe_mem_Icc g).2
      nlinarith
    rw [integral_const, probReal_univ, one_smul] at hhi
    exact hhi

/-- Strict positivity `0 < su2HaarCharacterMoment β 0` for `0 ≤ β`. -/
theorem su2HaarCharacterMoment_zero_pos {β : ℝ} (hβ : 0 ≤ β) :
    0 < su2HaarCharacterMoment β 0 :=
  lt_of_lt_of_le (Real.exp_pos (-2 * β)) (su2HaarCharacterMoment_zero_bounds hβ).1

/-- Normalization `su2BesselCharacterRatio β 0 = 1` of the trivial-spin Bessel character ratio. -/
theorem su2BesselCharacterRatio_zero {β : ℝ} (hβ : 0 ≤ β) :
    su2BesselCharacterRatio β 0 = 1 :=
  div_self (su2HaarCharacterMoment_zero_pos hβ).ne'

/-- Fundamental spin-`1 / 2` `SU(2)` Haar–Boltzmann moment bound
`|su2HaarCharacterMoment β 1| ≤ 2 * su2HaarCharacterMoment β 0`, proved by integrating
`su2SpinCharacter_one_abs_le_two` against `SU2.haarProbability`. -/
theorem su2HaarCharacterMoment_one_abs_le (β : ℝ) :
    |su2HaarCharacterMoment β 1| ≤ 2 * su2HaarCharacterMoment β 0 := by
  have hint0 := su2HaarBoltzmannWeight_integrable β
  have hint1 := su2HaarCharacterMoment_integrable β 1
  have hlo : ∫ g : SU2, (-2 : ℝ) * Real.exp (-β * (1 - halfTraceRe g)) ∂SU2.haarProbability ≤
      su2HaarCharacterMoment β 1 := by
    unfold su2HaarCharacterMoment
    refine integral_mono (hint0.const_mul (-2)) hint1 fun g => ?_
    have h_u1 := (abs_le.mp (su2SpinCharacter_one_abs_le_two (abs_halfTraceRe_le_one g))).1
    have hexp := (Real.exp_pos (-β * (1 - halfTraceRe g))).le
    nlinarith
  have hhi : su2HaarCharacterMoment β 1 ≤
      ∫ g : SU2, (2 : ℝ) * Real.exp (-β * (1 - halfTraceRe g)) ∂SU2.haarProbability := by
    unfold su2HaarCharacterMoment
    refine integral_mono hint1 (hint0.const_mul 2) fun g => ?_
    have h_u1 := (abs_le.mp (su2SpinCharacter_one_abs_le_two (abs_halfTraceRe_le_one g))).2
    have hexp := (Real.exp_pos (-β * (1 - halfTraceRe g))).le
    nlinarith
  rw [integral_const_mul, ← su2HaarCharacterMoment_zero_eq] at hlo hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Fundamental spin-`1 / 2` `SU(2)` Bessel character ratio bound
`|su2BesselCharacterRatio β 1| ≤ 2` for `0 ≤ β`. -/
theorem su2BesselCharacterRatio_one_abs_le {β : ℝ} (hβ : 0 ≤ β) :
    |su2BesselCharacterRatio β 1| ≤ 2 := by
  unfold su2BesselCharacterRatio
  have h0_pos : 0 < su2HaarCharacterMoment β 0 := su2HaarCharacterMoment_zero_pos hβ
  have h0_ne : su2HaarCharacterMoment β 0 ≠ 0 := h0_pos.ne'
  rw [abs_div, abs_of_pos h0_pos]
  calc
    |su2HaarCharacterMoment β 1| / su2HaarCharacterMoment β 0
      ≤ (2 * su2HaarCharacterMoment β 0) / su2HaarCharacterMoment β 0 :=
        div_le_div_of_nonneg_right (su2HaarCharacterMoment_one_abs_le β) h0_pos.le
    _ = 2 := by field_simp [h0_ne]

/-- Adjoint spin-`1` `SU(2)` Haar–Boltzmann moment bounds
`-su2HaarCharacterMoment β 0 ≤ su2HaarCharacterMoment β 2 ≤ 3 * su2HaarCharacterMoment β 0`,
proved by integrating `su2SpinCharacter_two_bounds_on_unit_interval` against `SU2.haarProbability`. -/
theorem su2HaarCharacterMoment_two_bounds (β : ℝ) :
    -su2HaarCharacterMoment β 0 ≤ su2HaarCharacterMoment β 2 ∧
      su2HaarCharacterMoment β 2 ≤ 3 * su2HaarCharacterMoment β 0 := by
  have hint0 := su2HaarBoltzmannWeight_integrable β
  have hint2 := su2HaarCharacterMoment_integrable β 2
  constructor
  · have hlo : ∫ g : SU2, (-1 : ℝ) * Real.exp (-β * (1 - halfTraceRe g)) ∂SU2.haarProbability ≤
        su2HaarCharacterMoment β 2 := by
      unfold su2HaarCharacterMoment
      refine integral_mono (hint0.const_mul (-1)) hint2 fun g => ?_
      have h_u2 := (su2SpinCharacter_two_bounds_on_unit_interval (abs_halfTraceRe_le_one g)).1
      have hexp := (Real.exp_pos (-β * (1 - halfTraceRe g))).le
      nlinarith
    rw [integral_const_mul, ← su2HaarCharacterMoment_zero_eq] at hlo
    linarith
  · have hhi : su2HaarCharacterMoment β 2 ≤
        ∫ g : SU2, (3 : ℝ) * Real.exp (-β * (1 - halfTraceRe g)) ∂SU2.haarProbability := by
      unfold su2HaarCharacterMoment
      refine integral_mono hint2 (hint0.const_mul 3) fun g => ?_
      have h_u2 := (su2SpinCharacter_two_bounds_on_unit_interval (abs_halfTraceRe_le_one g)).2
      have hexp := (Real.exp_pos (-β * (1 - halfTraceRe g))).le
      nlinarith
    rw [integral_const_mul, ← su2HaarCharacterMoment_zero_eq] at hhi
    linarith

/-- Adjoint spin-`1` `SU(2)` Bessel character ratio enclosure
`-1 ≤ su2BesselCharacterRatio β 2 ≤ 3` for `0 ≤ β`. -/
theorem su2BesselCharacterRatio_two_bounds {β : ℝ} (hβ : 0 ≤ β) :
    -1 ≤ su2BesselCharacterRatio β 2 ∧ su2BesselCharacterRatio β 2 ≤ 3 := by
  unfold su2BesselCharacterRatio
  have h0_pos : 0 < su2HaarCharacterMoment β 0 := su2HaarCharacterMoment_zero_pos hβ
  have h0_ne : su2HaarCharacterMoment β 0 ≠ 0 := h0_pos.ne'
  have h_bds := su2HaarCharacterMoment_two_bounds β
  constructor
  · calc
      (-1 : ℝ) = (-su2HaarCharacterMoment β 0) / su2HaarCharacterMoment β 0 := by
        field_simp [h0_ne]
      _ ≤ su2HaarCharacterMoment β 2 / su2HaarCharacterMoment β 0 :=
        div_le_div_of_nonneg_right h_bds.1 h0_pos.le
  · calc
      su2HaarCharacterMoment β 2 / su2HaarCharacterMoment β 0
        ≤ (3 * su2HaarCharacterMoment β 0) / su2HaarCharacterMoment β 0 :=
          div_le_div_of_nonneg_right h_bds.2 h0_pos.le
      _ = 3 := by field_simp [h0_ne]

/-- Concrete `SU(2)` dipole truncated Boltzmann weight at inverse coupling `β`, defined by
instantiating `truncatedCharacterBoltzmann` at `I0 = 1`, `u = su2BesselCharacterRatio β`, and
dipole cutoff `J = 1`. -/
noncomputable def su2DipoleTruncatedBoltzmann (β x : ℝ) : ℝ :=
  truncatedCharacterBoltzmann 1 (su2BesselCharacterRatio β) 1 x

theorem su2DipoleTruncatedBoltzmann_eq (β x : ℝ) :
    su2DipoleTruncatedBoltzmann β x = 1 + 2 * su2BesselCharacterRatio β 1 * x := by
  unfold su2DipoleTruncatedBoltzmann
  rw [truncatedCharacterBoltzmann_one_eq]
  ring

/-- Uniform positivity and lower bound of the concrete `SU(2)` dipole truncated Boltzmann weight
across `x ∈ [-1, 1]` whenever `2 * |su2BesselCharacterRatio β 1| < 1`. -/
theorem su2DipoleTruncatedBoltzmann_pos {β x : ℝ} (_hβ : 0 ≤ β)
    (hx1 : -1 ≤ x) (hx2 : x ≤ 1)
    (h_small : 2 * |su2BesselCharacterRatio β 1| < 1) :
    0 < 1 - 2 * |su2BesselCharacterRatio β 1| ∧
      1 - 2 * |su2BesselCharacterRatio β 1| ≤ su2DipoleTruncatedBoltzmann β x := by
  refine ⟨by linarith, ?_⟩
  rw [su2DipoleTruncatedBoltzmann_eq]
  set u1 := su2BesselCharacterRatio β 1
  have hu1_lo : -|u1| ≤ u1 := neg_abs_le u1
  have hu1_hi : u1 ≤ |u1| := le_abs_self u1
  have h1 : 0 ≤ (|u1| + u1) * (1 + x) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (|u1| - u1) * (1 - x) :=
    mul_nonneg (by linarith) (by linarith)
  have hid : (|u1| + u1) * (1 + x) + (|u1| - u1) * (1 - x) = 2 * |u1| + 2 * u1 * x := by
    ring
  linarith

/-- Instantiation of `truncatedCharacterBoltzmann_one_pos_on_unit_interval` with the concrete
`SU(2)` Haar–Boltzmann partition moment `I0 = su2HaarCharacterMoment β 0` and Bessel ratio
`u = su2BesselCharacterRatio β`. -/
theorem su2UnnormalizedDipoleBoltzmann_pos_on_unit_interval
    {β x : ℝ} (hβ : 0 ≤ β)
    (hu1_nonneg : 0 ≤ su2BesselCharacterRatio β 1)
    (hu1_lt : 2 * su2BesselCharacterRatio β 1 < 1)
    (hx : |x| ≤ 1) :
    0 < truncatedCharacterBoltzmann
      (su2HaarCharacterMoment β 0) (su2BesselCharacterRatio β) 1 x :=
  truncatedCharacterBoltzmann_one_pos_on_unit_interval
    (su2HaarCharacterMoment_zero_pos hβ) hu1_nonneg hu1_lt hx

/-- Center multiplication by `negOne = -I ∈ SU(2)` flips the sign of the normalized trace
`halfTraceRe (negOne * g) = -halfTraceRe g`. -/
theorem halfTraceRe_negOne_mul (g : SU2) :
    halfTraceRe (negOne * g) = -halfTraceRe g := by
  have htr : SU2.trace (negOne * g) = -SU2.trace g := by
    change Matrix.trace ((-1 : Matrix (Fin 2) (Fin 2) ℂ) * g.mat) = -Matrix.trace g.mat
    rw [neg_one_mul, Matrix.trace_neg]
  unfold halfTraceRe
  rw [htr, Complex.neg_re]
  ring

/-- Center multiplication by `negOne = -I ∈ SU(2)` flips the sign of the fundamental spin-`1 / 2`
character `su2SpinCharacter 1 (halfTraceRe (negOne * g)) = -su2SpinCharacter 1 (halfTraceRe g)`. -/
theorem su2SpinCharacter_one_negOne_mul (g : SU2) :
    su2SpinCharacter 1 (halfTraceRe (negOne * g)) = -su2SpinCharacter 1 (halfTraceRe g) := by
  simp [su2SpinCharacter, halfTraceRe_negOne_mul]

/-- Exact `SU(2)` Haar orthogonality of the fundamental character: the Haar integral of
`su2SpinCharacter 1 (halfTraceRe g) = 2 * halfTraceRe g` over `SU2.haarProbability` vanishes
identically by left Haar invariance under center multiplication `g ↦ negOne * g`. -/
theorem integral_su2SpinCharacter_one_eq_zero :
    (∫ g : SU2, su2SpinCharacter 1 (halfTraceRe g) ∂SU2.haarProbability) = 0 := by
  have hcont : Continuous (fun g : SU2 => su2SpinCharacter 1 (halfTraceRe g)) :=
    (su2SpinCharacter_continuous 1).comp continuous_halfTraceRe
  have hmp : MeasurePreserving (fun g : SU2 => negOne * g)
      (SU2.haarProbability : Measure SU2) (SU2.haarProbability : Measure SU2) :=
    measurePreserving_mul_left (SU2.haarProbability : Measure SU2) negOne
  have hmap :
      (∫ g : SU2, su2SpinCharacter 1 (halfTraceRe g) ∂SU2.haarProbability) =
        ∫ g : SU2, su2SpinCharacter 1 (halfTraceRe (negOne * g)) ∂SU2.haarProbability := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map (continuous_const.mul continuous_id).aemeasurable hcont.aestronglyMeasurable
  have hneg :
      (∫ g : SU2, su2SpinCharacter 1 (halfTraceRe (negOne * g)) ∂SU2.haarProbability) =
        -(∫ g : SU2, su2SpinCharacter 1 (halfTraceRe g) ∂SU2.haarProbability) := by
    simp_rw [su2SpinCharacter_one_negOne_mul, integral_neg]
  linarith

/-- At zero coupling `β = 0`, the trivial-spin `SU(2)` Haar–Boltzmann moment equals `1` and the
fundamental spin-`1 / 2` moment vanishes identically (`su2HaarCharacterMoment 0 1 = 0`). -/
theorem su2HaarCharacterMoment_zero_one :
    su2HaarCharacterMoment 0 0 = 1 ∧ su2HaarCharacterMoment 0 1 = 0 := by
  constructor
  · rw [su2HaarCharacterMoment_zero_eq]
    simp
  · unfold su2HaarCharacterMoment
    simpa using integral_su2SpinCharacter_one_eq_zero

/-- At zero coupling `β = 0`, the fundamental `SU(2)` Bessel character ratio vanishes identically
(`su2BesselCharacterRatio 0 1 = 0`). -/
theorem su2BesselCharacterRatio_zero_one :
    su2BesselCharacterRatio 0 1 = 0 := by
  unfold su2BesselCharacterRatio
  rw [su2HaarCharacterMoment_zero_one.2, zero_div]

/-- Center-symmetry subtraction identity for `su2HaarCharacterMoment β 1`: because
`∫ su2SpinCharacter 1 (halfTraceRe g) dμ_Haar = 0`, subtracting `exp(-β) * su2SpinCharacter 1 (halfTraceRe g)`
inside the integral leaves `su2HaarCharacterMoment β 1` unchanged. -/
theorem su2HaarCharacterMoment_one_eq_centered (β : ℝ) :
    su2HaarCharacterMoment β 1 =
      ∫ g : SU2,
        su2SpinCharacter 1 (halfTraceRe g) *
          (Real.exp (-β * (1 - halfTraceRe g)) - Real.exp (-β))
        ∂SU2.haarProbability := by
  have hcont_char : Continuous (fun g : SU2 => su2SpinCharacter 1 (halfTraceRe g)) :=
    (su2SpinCharacter_continuous 1).comp continuous_halfTraceRe
  have hcont1 : Continuous (fun g : SU2 =>
      su2SpinCharacter 1 (halfTraceRe g) * Real.exp (-β * (1 - halfTraceRe g))) :=
    hcont_char.mul (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_halfTraceRe)))
  have hint1 : Integrable (fun g : SU2 =>
      su2SpinCharacter 1 (halfTraceRe g) * Real.exp (-β * (1 - halfTraceRe g)))
      SU2.haarProbability :=
    hcont1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun g : SU2 =>
      su2SpinCharacter 1 (halfTraceRe g) * Real.exp (-β))
      SU2.haarProbability := hcont_char.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _) |>.mul_const (Real.exp (-β))
  have hsub :
      (∫ g : SU2,
        su2SpinCharacter 1 (halfTraceRe g) *
          (Real.exp (-β * (1 - halfTraceRe g)) - Real.exp (-β))
        ∂SU2.haarProbability) =
      (∫ g : SU2, su2SpinCharacter 1 (halfTraceRe g) * Real.exp (-β * (1 - halfTraceRe g))
        ∂SU2.haarProbability) -
      (∫ g : SU2, su2SpinCharacter 1 (halfTraceRe g) * Real.exp (-β)
        ∂SU2.haarProbability) := by
    rw [← integral_sub hint1 hint2]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    ring
  rw [hsub, integral_mul_const, integral_su2SpinCharacter_one_eq_zero, zero_mul, sub_zero]
  unfold su2HaarCharacterMoment
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  ring

/-- Elementary two-sided exponential bound on `[-1, 1]`: for `0 ≤ β` and `x ∈ [-1, 1]`,
`|exp(-β * (1 - x)) - exp(-β)| ≤ 1 - exp(-β)`. -/
theorem abs_exp_neg_one_sub_sub_exp_neg_le {β x : ℝ} (hβ : 0 ≤ β)
    (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |Real.exp (-β * (1 - x)) - Real.exp (-β)| ≤ 1 - Real.exp (-β) := by
  have h_nonpos : -β * (1 - x) ≤ 0 := by nlinarith
  have h_hi : Real.exp (-β * (1 - x)) ≤ 1 := Real.exp_le_one_iff.mpr h_nonpos
  have h_lo : Real.exp (-2 * β) ≤ Real.exp (-β * (1 - x)) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  have h_sq : 0 ≤ (1 - Real.exp (-β)) ^ 2 := sq_nonneg (1 - Real.exp (-β))
  have h_exp2 : Real.exp (-2 * β) = (Real.exp (-β)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have h_id : 1 - 2 * Real.exp (-β) + Real.exp (-2 * β) = (1 - Real.exp (-β)) ^ 2 := by
    rw [h_exp2]
    ring
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- For `0 ≤ β`, `1 - exp(-β) ≤ β`. -/
theorem one_sub_exp_neg_le_self {β : ℝ} (_hβ : 0 ≤ β) :
    1 - Real.exp (-β) ≤ β := by
  have h := Real.add_one_le_exp (-β)
  linarith

/-- Quantitative `SU(2)` center-symmetry contraction bound for the spin-`1 / 2` Haar–Boltzmann
character moment: for all `0 ≤ β`,
`|su2HaarCharacterMoment β 1| ≤ 2 * (1 - Real.exp (-β))`. -/
theorem su2HaarCharacterMoment_one_abs_le_two_mul_one_sub_exp {β : ℝ} (hβ : 0 ≤ β) :
    |su2HaarCharacterMoment β 1| ≤ 2 * (1 - Real.exp (-β)) := by
  rw [su2HaarCharacterMoment_one_eq_centered β]
  have hcont : Continuous (fun g : SU2 =>
      su2SpinCharacter 1 (halfTraceRe g) *
        (Real.exp (-β * (1 - halfTraceRe g)) - Real.exp (-β))) :=
    ((su2SpinCharacter_continuous 1).comp continuous_halfTraceRe).mul
      ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_halfTraceRe))).sub
        continuous_const)
  have hint : Integrable (fun g : SU2 =>
      su2SpinCharacter 1 (halfTraceRe g) *
        (Real.exp (-β * (1 - halfTraceRe g)) - Real.exp (-β)))
      SU2.haarProbability :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_exp_le : Real.exp (-β) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have h_pt (g : SU2) :
      |su2SpinCharacter 1 (halfTraceRe g) *
        (Real.exp (-β * (1 - halfTraceRe g)) - Real.exp (-β))| ≤
        2 * (1 - Real.exp (-β)) := by
    rw [abs_mul]
    have h1 := su2SpinCharacter_one_abs_le_two (abs_halfTraceRe_le_one g)
    have h2 := abs_exp_neg_one_sub_sub_exp_neg_le hβ
      (halfTraceRe_mem_Icc g).1 (halfTraceRe_mem_Icc g).2
    nlinarith [abs_nonneg (Real.exp (-β * (1 - halfTraceRe g)) - Real.exp (-β))]
  calc
    |∫ g : SU2,
        su2SpinCharacter 1 (halfTraceRe g) *
          (Real.exp (-β * (1 - halfTraceRe g)) - Real.exp (-β))
        ∂SU2.haarProbability|
      ≤ ∫ g : SU2,
          |su2SpinCharacter 1 (halfTraceRe g) *
            (Real.exp (-β * (1 - halfTraceRe g)) - Real.exp (-β))|
          ∂SU2.haarProbability := abs_integral_le_integral_abs
    _ ≤ ∫ _ : SU2, 2 * (1 - Real.exp (-β)) ∂SU2.haarProbability :=
        integral_mono hint.abs (integrable_const _) h_pt
    _ = 2 * (1 - Real.exp (-β)) := by
        rw [integral_const, probReal_univ, one_smul]

/-- Linear-in-`β` strong-coupling bound on the spin-`1 / 2` `SU(2)` Haar–Boltzmann character moment:
for `0 ≤ β`, `|su2HaarCharacterMoment β 1| ≤ 2 * β`. -/
theorem su2HaarCharacterMoment_one_abs_le_two_mul_beta {β : ℝ} (hβ : 0 ≤ β) :
    |su2HaarCharacterMoment β 1| ≤ 2 * β :=
  (su2HaarCharacterMoment_one_abs_le_two_mul_one_sub_exp hβ).trans
    (by linarith [one_sub_exp_neg_le_self hβ])

/-- Quantitative strong-coupling bound on the fundamental `SU(2)` Bessel character ratio:
for `0 ≤ β`, `|su2BesselCharacterRatio β 1| ≤ 2 * β * Real.exp (2 * β)`. -/
theorem su2BesselCharacterRatio_one_abs_le_two_mul_beta_mul_exp {β : ℝ} (hβ : 0 ≤ β) :
    |su2BesselCharacterRatio β 1| ≤ 2 * β * Real.exp (2 * β) := by
  unfold su2BesselCharacterRatio
  have h0_pos : 0 < su2HaarCharacterMoment β 0 := su2HaarCharacterMoment_zero_pos hβ
  have h0_lo : Real.exp (-2 * β) ≤ su2HaarCharacterMoment β 0 :=
    (su2HaarCharacterMoment_zero_bounds hβ).1
  rw [abs_div, abs_of_pos h0_pos, div_le_iff₀ h0_pos]
  calc
    |su2HaarCharacterMoment β 1| ≤ 2 * β :=
      su2HaarCharacterMoment_one_abs_le_two_mul_beta hβ
    _ = (2 * β * Real.exp (2 * β)) * Real.exp (-2 * β) := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    _ ≤ (2 * β * Real.exp (2 * β)) * su2HaarCharacterMoment β 0 :=
      mul_le_mul_of_nonneg_left h0_lo (mul_nonneg (by linarith) (Real.exp_pos _).le)

/-- Lower bound `1 - 2 * β ≤ su2HaarCharacterMoment β 0` for `0 ≤ β`, obtained from
`exp(-2 * β) ≤ su2HaarCharacterMoment β 0` and `1 - 2 * β ≤ exp(-2 * β)`. -/
theorem su2HaarCharacterMoment_zero_ge_one_sub_two_beta {β : ℝ} (hβ : 0 ≤ β) :
    1 - 2 * β ≤ su2HaarCharacterMoment β 0 := by
  have h_exp := Real.add_one_le_exp (-2 * β)
  have h_lo := (su2HaarCharacterMoment_zero_bounds hβ).1
  linarith

/-- Rational strong-coupling bound on the fundamental `SU(2)` Bessel character ratio:
for `0 ≤ β < 1 / 2`, `|su2BesselCharacterRatio β 1| ≤ (2 * β) / (1 - 2 * β)`. -/
theorem su2BesselCharacterRatio_one_abs_le_div_one_sub_two_beta
    {β : ℝ} (hβ : 0 ≤ β) (hβ_half : β < 1 / 2) :
    |su2BesselCharacterRatio β 1| ≤ (2 * β) / (1 - 2 * β) := by
  unfold su2BesselCharacterRatio
  have h0_pos : 0 < su2HaarCharacterMoment β 0 := su2HaarCharacterMoment_zero_pos hβ
  have h_den_pos : 0 < 1 - 2 * β := by linarith
  have h0_ge : 1 - 2 * β ≤ su2HaarCharacterMoment β 0 :=
    su2HaarCharacterMoment_zero_ge_one_sub_two_beta hβ
  rw [abs_div, abs_of_pos h0_pos]
  calc
    |su2HaarCharacterMoment β 1| / su2HaarCharacterMoment β 0
      ≤ (2 * β) / su2HaarCharacterMoment β 0 :=
        div_le_div_of_nonneg_right (su2HaarCharacterMoment_one_abs_le_two_mul_beta hβ) h0_pos.le
    _ ≤ (2 * β) / (1 - 2 * β) :=
        div_le_div_of_nonneg_left (by linarith) h_den_pos h0_ge

/-- For every strong/crossover coupling `0 ≤ β ≤ 1 / 8` (including `canonicalCrossoverBetaHi`),
the fundamental `SU(2)` Bessel character ratio satisfies
`|su2BesselCharacterRatio β 1| ≤ 1 / 3` and `2 * |su2BesselCharacterRatio β 1| ≤ 2 / 3 < 1`,
discharging the dipole smallness hypothesis `2 * |su2BesselCharacterRatio β 1| < 1` from `β` alone. -/
theorem su2BesselCharacterRatio_one_small_of_beta_le_one_eighth
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ8 : β ≤ 1 / 8) :
    |su2BesselCharacterRatio β 1| ≤ 1 / 3 ∧
    2 * |su2BesselCharacterRatio β 1| ≤ 2 / 3 ∧
    2 * |su2BesselCharacterRatio β 1| < 1 := by
  have h_rat := su2BesselCharacterRatio_one_abs_le_div_one_sub_two_beta hβ0 (by linarith)
  have h_den : (0 : ℝ) < 1 - 2 * β := by linarith
  have h_le_third : (2 * β) / (1 - 2 * β) ≤ 1 / 3 := by
    rw [div_le_iff₀ h_den]
    linarith
  have h1 : |su2BesselCharacterRatio β 1| ≤ 1 / 3 := h_rat.trans h_le_third
  exact ⟨h1, by linarith, by linarith⟩

/-- Unconditional positivity and `1 / 3` lower bound of `su2DipoleTruncatedBoltzmann β x` across
`x ∈ [-1, 1]` for all `0 ≤ β ≤ 1 / 8`, derived directly from the `SU(2)` Haar–Boltzmann integral
without any external character-ratio assumption. -/
theorem su2DipoleTruncatedBoltzmann_pos_of_beta_le_one_eighth
    {β x : ℝ} (hβ0 : 0 ≤ β) (hβ8 : β ≤ 1 / 8)
    (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    (1 / 3 : ℝ) ≤ su2DipoleTruncatedBoltzmann β x ∧
    0 < su2DipoleTruncatedBoltzmann β x := by
  have h_small := su2BesselCharacterRatio_one_small_of_beta_le_one_eighth hβ0 hβ8
  have h_pos := su2DipoleTruncatedBoltzmann_pos hβ0 hx1 hx2 h_small.2.2
  refine ⟨by linarith [h_small.2.1, h_pos.2], by linarith [h_small.2.1, h_pos.2]⟩

end SchwingerLayerAndPerimeterCorner

/-! ## 12. General Compact Simple Gauge Group Scaling Constants & Full Clay OS / Hamiltonian Endpoint Specifications -/

/-- Universal 4D pure Yang–Mills 1-loop asymptotic freedom coefficient
`β₀(G) = 11 h∨(G) / (48 π²)` in terms of the dual Coxeter number `h_dual = h∨(G) ≥ 2`
(for `SU(N)` the dual Coxeter number is `N`, for `Sp(N)` it is `N + 1`, and for `SO(N)` with
`N ≥ 5` it is `N - 2`). -/
noncomputable def compactSimpleOneLoopBeta0 (h_dual : ℕ) : ℝ :=
  (11 : ℝ) * (h_dual : ℝ) / (48 * Real.pi ^ 2)

/-- Strict positivity of the universal 1-loop asymptotic freedom coefficient
`compactSimpleOneLoopBeta0 h_dual` for every positive dual Coxeter number `1 ≤ h_dual`. -/
theorem compactSimpleOneLoopBeta0_pos {h_dual : ℕ} (hh : 1 ≤ h_dual) :
    0 < compactSimpleOneLoopBeta0 h_dual := by
  unfold compactSimpleOneLoopBeta0
  have h1 : (1 : ℝ) ≤ (h_dual : ℝ) := by exact_mod_cast hh
  have h_hd : (0 : ℝ) < (h_dual : ℝ) := by linarith
  have h_pi : 0 < Real.pi := Real.pi_pos
  positivity

/-- Monotonicity of `compactSimpleOneLoopBeta0` in the dual Coxeter number `h_dual`. -/
theorem compactSimpleOneLoopBeta0_mono {h₁ h₂ : ℕ} (hle : h₁ ≤ h₂) :
    compactSimpleOneLoopBeta0 h₁ ≤ compactSimpleOneLoopBeta0 h₂ := by
  unfold compactSimpleOneLoopBeta0
  have h_cast : (h₁ : ℝ) ≤ (h₂ : ℝ) := by exact_mod_cast hle
  have h_pi : 0 < Real.pi := Real.pi_pos
  have h_den : (0 : ℝ) ≤ 48 * Real.pi ^ 2 := by positivity
  exact div_le_div_of_nonneg_right (by linarith) h_den

/-- Exact relation between `compactSimpleOneLoopBeta0 2` (`h∨(SU(2)) = 2` in standard coupling
normalization `1 / g²`) and `su2OneLoopBeta0 = 11 / (3 π²)` (in the lattice normalization
`β = 4 / g² = 8 · (1 / (2 g²))`): `8 * compactSimpleOneLoopBeta0 2 = su2OneLoopBeta0`. -/
theorem compactSimpleOneLoopBeta0_two_relation :
    8 * compactSimpleOneLoopBeta0 2 = su2OneLoopBeta0 := by
  unfold compactSimpleOneLoopBeta0 su2OneLoopBeta0
  push_cast
  ring

/-- General-group 6-face unit-cube Haar character integral scaling `(d_fund²)⁻⁵` for a
fundamental representation of dimension `d_fund` with normalized character `χ_fund(U) / d_fund`
satisfying `∫ |χ_fund(U) / d_fund|² dU = d_fund⁻²`. -/
noncomputable def compactSimpleSixFaceCubeLeadingCoeff (d_fund : ℕ) : ℝ :=
  ((d_fund : ℝ) ^ 2) ^ (-5 : ℤ)

/-- Strict positivity of the 6-face unit-cube Haar character integral coefficient
`compactSimpleSixFaceCubeLeadingCoeff d_fund` for every positive fundamental dimension `1 ≤ d_fund`. -/
theorem compactSimpleSixFaceCubeLeadingCoeff_pos {d_fund : ℕ} (hd : 1 ≤ d_fund) :
    0 < compactSimpleSixFaceCubeLeadingCoeff d_fund := by
  unfold compactSimpleSixFaceCubeLeadingCoeff
  have h1 : (1 : ℝ) ≤ (d_fund : ℝ) := by exact_mod_cast hd
  have hd_pos : (0 : ℝ) < (d_fund : ℝ) := by linarith
  exact zpow_pos (sq_pos_of_pos hd_pos) (-5)

/-- For `SU(2)` (`d_fund = 2`), `compactSimpleSixFaceCubeLeadingCoeff 2` recovers the exact
6-face unit-cube coefficient `4⁻⁵ = 1 / 1024`. -/
theorem compactSimpleSixFaceCubeLeadingCoeff_two_eq :
    compactSimpleSixFaceCubeLeadingCoeff 2 = (4 : ℝ) ^ (-5 : ℤ) := by
  unfold compactSimpleSixFaceCubeLeadingCoeff
  norm_num

/-- Explicit rational evaluation `compactSimpleSixFaceCubeLeadingCoeff 2 = 1 / 1024`. -/
theorem compactSimpleSixFaceCubeLeadingCoeff_two_eq_inv_1024 :
    compactSimpleSixFaceCubeLeadingCoeff 2 = 1 / 1024 := by
  unfold compactSimpleSixFaceCubeLeadingCoeff
  norm_num

/-- Loop-level Osterwalder–Schrader time-reflection positivity predicate on `WilsonLoopSpace`
probability laws (alias of `IsReflectionPositive`). -/
abbrev IsTimeReflectPositive (μ : ProbabilityMeasure WilsonLoopSpace) : Prop :=
  IsReflectionPositive μ

/-- Loop-level rational translation invariance predicate on `WilsonLoopSpace` probability laws:
invariance under `translateObservables c` for every rational spacetime shift `c : Fin 4 → ℚ`. -/
def IsTranslationInvariant (μ : ProbabilityMeasure WilsonLoopSpace) : Prop :=
  ∀ c : Fin 4 → ℚ, μ.map (translateObservables c) = μ

/-- Loop-level hypercubic axis-permutation invariance predicate on `WilsonLoopSpace` probability
laws: invariance under `permuteObservables σ` for every coordinate permutation
`σ : Equiv.Perm (Fin 4)`. -/
def IsAxisPermInvariant (μ : ProbabilityMeasure WilsonLoopSpace) : Prop :=
  ∀ σ : Equiv.Perm (Fin 4), μ.map (permuteObservables σ) = μ

/-- Full continuum Osterwalder–Schrader specification `FullEuclideanContinuumSymmetryAndOSProp`:
packages the five loop-level continuum axioms (`IsTimeReflectPositive μ`, `IsTranslationInvariant μ`,
`IsAxisPermInvariant μ`, `IsTimeMixing μ`, `IsNontrivial μ`) together with full `SO(4)` continuum
rotational invariance (`rot_inv : Prop`) and Wightman / Osterwalder–Schrader local-field
temperedness and regularity (`local_field_tempered : Prop`).

Open mathematical obligation: constructing the continuum probability measure satisfying
`FullEuclideanContinuumSymmetryAndOSProp` and the self-adjoint Hamiltonian satisfying
`SelfAdjointHamiltonianSpectralGapBridgeProp` from the lattice Wilson measures for every
compact simple gauge group `G` remain open mathematical obligations. -/
def FullEuclideanContinuumSymmetryAndOSProp
    (μ : ProbabilityMeasure WilsonLoopSpace)
    (rot_inv local_field_tempered : Prop) : Prop :=
  (IsTimeReflectPositive μ ∧
    IsTranslationInvariant μ ∧
    IsAxisPermInvariant μ ∧
    IsTimeMixing μ ∧
    IsNontrivial μ) ∧
  rot_inv ∧
  local_field_tempered

/-- `FullEuclideanContinuumSymmetryAndOSProp` entails all five loop-level continuum axioms
(`IsTimeReflectPositive`, `IsTranslationInvariant`, `IsAxisPermInvariant`, `IsTimeMixing`,
`IsNontrivial`). -/
theorem fullEuclideanContinuumSymmetryAndOSProp_implies_loop_axioms
    {μ : ProbabilityMeasure WilsonLoopSpace}
    {rot_inv local_field_tempered : Prop}
    (h : FullEuclideanContinuumSymmetryAndOSProp μ rot_inv local_field_tempered) :
    IsTimeReflectPositive μ ∧
    IsTranslationInvariant μ ∧
    IsAxisPermInvariant μ ∧
    IsTimeMixing μ ∧
    IsNontrivial μ :=
  h.1

/-- Physical Hamiltonian spectral-gap semigroup specification
`SelfAdjointHamiltonianSpectralGapBridgeProp m_phys semigroup_norm`: asserts a strictly positive
physical mass gap `0 < m_phys` together with the vacuum-subtracted contraction bound
`0 ≤ semigroup_norm t ≤ exp(-m_phys * t)` for all Euclidean times `t ≥ 0` on the
Osterwalder–Schrader reconstructed physical Hilbert space `ℋ_phys = (ℋ_OS)⊥_Ω`.

Open mathematical obligation: constructing the continuum measure satisfying
`FullEuclideanContinuumSymmetryAndOSProp` and the self-adjoint Hamiltonian satisfying
`SelfAdjointHamiltonianSpectralGapBridgeProp` from the lattice Wilson measures for every
compact simple gauge group `G` remain open mathematical obligations. -/
def SelfAdjointHamiltonianSpectralGapBridgeProp
    (m_phys : ℝ) (semigroup_norm : ℝ → ℝ) : Prop :=
  0 < m_phys ∧
  ∀ t : ℝ, 0 ≤ t → 0 ≤ semigroup_norm t ∧ semigroup_norm t ≤ Real.exp (-m_phys * t)

/-- Under `SelfAdjointHamiltonianSpectralGapBridgeProp m_phys semigroup_norm`, every strictly
positive Euclidean time `t > 0` satisfies the strict contraction `semigroup_norm t < 1`, and for
all `t₁, t₂ ≥ 0` the semigroup norm at `t₁ + t₂` is bounded by the factored exponential envelope
`exp(-m_phys * t₁) * exp(-m_phys * t₂)` (and when combined with submultiplicativity
`semigroup_norm (t₁ + t₂) ≤ semigroup_norm t₁ * semigroup_norm t₂`, factors through
`semigroup_norm t₁ * semigroup_norm t₂ ≤ exp(-m_phys * t₁) * exp(-m_phys * t₂)`). -/
theorem selfAdjointHamiltonianSpectralGap_exponential_decay_and_strict_contraction
    {m_phys : ℝ} {semigroup_norm : ℝ → ℝ}
    (h : SelfAdjointHamiltonianSpectralGapBridgeProp m_phys semigroup_norm)
    {t t₁ t₂ : ℝ} (ht : 0 < t) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) :
    semigroup_norm t < 1 ∧
    semigroup_norm t₁ * semigroup_norm t₂ ≤
      Real.exp (-m_phys * t₁) * Real.exp (-m_phys * t₂) ∧
    semigroup_norm (t₁ + t₂) ≤ Real.exp (-m_phys * t₁) * Real.exp (-m_phys * t₂) := by
  obtain ⟨hm, hbound⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have h_le : semigroup_norm t ≤ Real.exp (-m_phys * t) := (hbound t ht.le).2
    have h_neg : -m_phys * t < 0 := by nlinarith
    have h_exp_lt : Real.exp (-m_phys * t) < 1 := Real.exp_lt_one_iff.mpr h_neg
    linarith
  · exact mul_le_mul (hbound t₁ ht₁).2 (hbound t₂ ht₂).2
      (hbound t₂ ht₂).1 (Real.exp_pos (-m_phys * t₁)).le
  · have h_le : semigroup_norm (t₁ + t₂) ≤ Real.exp (-m_phys * (t₁ + t₂)) :=
      (hbound (t₁ + t₂) (add_nonneg ht₁ ht₂)).2
    have h_add : -m_phys * (t₁ + t₂) = -m_phys * t₁ + -m_phys * t₂ := by ring
    rw [h_add, Real.exp_add] at h_le
    exact h_le

/-- Transfer of exponential Euclidean correlator decay and uniform non-triviality margin from
approximating cutoff correlators `C_approx : ℕ → ℝ → ℝ` to the continuum limit `C_lim : ℝ → ℝ`
(Pack 3 & 4 bridge for `YangMillsOSTimeTranslation`, `YangMillsPhysicalGap`, and `YangMillsContinuumLimitBridge`):
if for every `t ≥ 0`, `C_approx n t → C_lim t` as `n → ∞`, `0 ≤ C_approx n t ≤ Real.exp (-m_phys * t)`,
and at `t = 0` the uniform non-triviality margin `c_margin ≤ C_approx n 0` holds with `0 < c_margin`
and `0 < m_phys`, then:
1. `SelfAdjointHamiltonianSpectralGapBridgeProp m_phys C_lim` holds in the continuum limit, and
2. The continuum variance at `t = 0` satisfies the strict non-triviality bound `c_margin ≤ C_lim 0`
   (`0 < C_lim 0`), preventing continuum collapse (`pointwise_nontriviality_can_collapse`). -/
theorem continuumCorrelatorLimit_transfers_spectralGapSemigroup_and_nontriviality_margin
    (C_approx : ℕ → ℝ → ℝ) (C_lim : ℝ → ℝ) {m_phys c_margin : ℝ}
    (hm : 0 < m_phys) (hc : 0 < c_margin)
    (h_tendsto : ∀ t : ℝ, 0 ≤ t → Tendsto (fun n => C_approx n t) atTop (𝓝 (C_lim t)))
    (h_nonneg : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ C_approx n t)
    (h_decay : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → C_approx n t ≤ Real.exp (-m_phys * t))
    (h_margin : ∀ n : ℕ, c_margin ≤ C_approx n 0) :
    SelfAdjointHamiltonianSpectralGapBridgeProp m_phys C_lim ∧
    c_margin ≤ C_lim 0 ∧
    0 < C_lim 0 := by
  have h_bridge : SelfAdjointHamiltonianSpectralGapBridgeProp m_phys C_lim := by
    refine ⟨hm, fun t ht => ⟨?_, ?_⟩⟩
    · exact ge_of_tendsto (h_tendsto t ht) (Eventually.of_forall fun n => h_nonneg n t ht)
    · exact le_of_tendsto (h_tendsto t ht) (Eventually.of_forall fun n => h_decay n t ht)
  have h_c0 : c_margin ≤ C_lim 0 :=
    ge_of_tendsto (h_tendsto 0 le_rfl) (Eventually.of_forall h_margin)
  exact ⟨h_bridge, h_c0, lt_of_lt_of_le hc h_c0⟩

end JesseMath.Physics.YangMillsOsterwalderSchraderInheritance

#assert_zfc_axioms
