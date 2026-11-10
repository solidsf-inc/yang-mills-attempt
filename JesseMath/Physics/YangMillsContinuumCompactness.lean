import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.YangMillsHaarBlocking
import JesseMath.Physics.YangMillsWeakCoupling
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences

/-!
# Weak compactness of actual finite-volume Wilson laws

The finite SU(2) configuration topology is compact and Polish. Thus the actual normalized
Wilson laws have probability-valued subsequential limits, with one subsequence for every
continuous observable. Continuous dyadic blocking commutes with those limits.

Periodic extension also puts varying finite lattices on one countable integer-link space.
This establishes a common-space weak limit, not a continuum field after physical rescaling.
The actual finite Wilson laws are locally gauge and lattice translation invariant. Every
common-space weak limit inherits global conjugation and integer translation invariance.
No uniqueness, OS reconstruction, rotational symmetry, or nontrivial field-strength limit
is inferred from compactness or these exact lattice symmetries alone.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace JesseMath.Physics.YangMillsContinuumCompactness

instance (L : ℕ) : CompactSpace (GaugeConfig L) :=
  inferInstanceAs (CompactSpace (Link L → SU2))

instance (L : ℕ) : T2Space (GaugeConfig L) :=
  inferInstanceAs (T2Space (Link L → SU2))

instance (L : ℕ) [NeZero L] : PolishSpace (GaugeConfig L) :=
  inferInstanceAs (PolishSpace (Link L → SU2))

/-- The actual Wilson density on normalized finite product Haar, as a probability measure. -/
def wilsonProbability (L : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β) :
    ProbabilityMeasure (GaugeConfig L) :=
  ⟨wilsonMeasure (gaugeHaarMeasure L) β,
    wilsonMeasure_isProbabilityMeasure _ hβ (measurable_wilsonAction β)⟩

@[simp] theorem wilsonProbability_toMeasure (L : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β) :
    (wilsonProbability L β hβ : Measure (GaugeConfig L)) =
      wilsonMeasure (gaugeHaarMeasure L) β := rfl

/-- Integrals of this probability measure are the normalized Wilson expectations. -/
theorem wilsonProbability_integral (L : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    (F : GaugeConfig L → ℝ) :
    (∫ U, F U ∂wilsonProbability L β hβ) = wilsonExpectation (gaugeHaarMeasure L) β F :=
  integral_wilsonMeasure _ hβ (measurable_wilsonAction β) F

/-- Product Haar and the Wilson density give exact local gauge invariance of the actual law.
No measure-preservation premise is supplied by the caller. -/
theorem wilsonProbability_gauge_invariant (L : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    (g : GaugeTransformation L) :
    (wilsonProbability L β hβ).map (gaugeTransform g) = wilsonProbability L β hβ := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  change (∫ U, F U ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)).map
    (gaugeTransform g)) = _
  rw [integral_map_of_stronglyMeasurable (continuous_gaugeTransform g).measurable
    F.continuous.measurable.stronglyMeasurable, wilsonProbability_integral,
    wilsonProbability_integral]
  exact wilsonExpectation_gaugeTransform _ β (measurable_wilsonAction β) g
    (measurePreserving_gaugeTransform g) F.continuous.measurable

/-- Local gauge invariance survives every weak limit of actual fixed-volume Wilson laws. -/
theorem wilsonProbability_limit_gauge_invariant {L : ℕ} [NeZero L]
    (β : ℕ → ℝ) (hβ : ∀ n, 0 ≤ β n) (ν : ProbabilityMeasure (GaugeConfig L))
    (hν : Tendsto (fun n => wilsonProbability L (β n) (hβ n)) atTop (𝓝 ν))
    (g : GaugeTransformation L) : ν.map (gaugeTransform g) = ν := by
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hν
    (continuous_gaugeTransform g)
  simp only [wilsonProbability_gauge_invariant] at hm
  exact tendsto_nhds_unique hm hν

/-- Translation permutes the finite oriented links without changing their directions. -/
def linkTranslationEquiv {L : ℕ} (a : Lattice4D L) : Link L ≃ Link L where
  toFun e := ⟨e.x + a, e.μ⟩
  invFun e := ⟨e.x - a, e.μ⟩
  left_inv := by intro e; simp
  right_inv := by intro e; simp

/-- Pullback of link fields by a finite lattice translation. -/
def latticeTranslate {L : ℕ} (a : Lattice4D L) (U : GaugeConfig L) : GaugeConfig L :=
  fun e => U (linkTranslationEquiv a e)

@[continuity, fun_prop]
theorem continuous_latticeTranslate {L : ℕ} (a : Lattice4D L) :
    Continuous (latticeTranslate a) :=
  continuous_pi fun _ => continuous_apply _

/-- Product Haar is invariant under the actual translation permutation. -/
theorem measurePreserving_latticeTranslate {L : ℕ} [NeZero L] (a : Lattice4D L) :
    MeasurePreserving (latticeTranslate a) (gaugeHaarMeasure L) (gaugeHaarMeasure L) := by
  change MeasurePreserving (fun (U : Link L → SU2) (e : Link L) => U (linkTranslationEquiv a e))
    (Measure.pi (fun _ : Link L => SU2.haarProbability))
    (Measure.pi (fun _ : Link L => SU2.haarProbability))
  have hf : (MeasurableEquiv.piCongrLeft (fun _ : Link L => SU2)
      (linkTranslationEquiv a).symm : (Link L → SU2) → (Link L → SU2)) =
      (fun (U : Link L → SU2) e => U (linkTranslationEquiv a e)) := by
    funext U e
    change (Equiv.piCongrLeft (fun _ : Link L => SU2) (linkTranslationEquiv a).symm U) e = _
    rw [Equiv.piCongrLeft_apply_eq_cast]
    simp
  simpa only [hf] using
    measurePreserving_piCongrLeft (fun _ : Link L => SU2.haarProbability)
      (linkTranslationEquiv a).symm

def plaquetteTranslationEquiv {L : ℕ} (a : Lattice4D L) : Plaquette L ≃ Plaquette L where
  toFun p := ⟨p.x + a, p.μ, p.ν, p.h⟩
  invFun p := ⟨p.x - a, p.μ, p.ν, p.h⟩
  left_inv := by intro p; simp
  right_inv := by intro p; simp

theorem plaquetteAction_latticeTranslate {L : ℕ} (a : Lattice4D L)
    (U : GaugeConfig L) (p : Plaquette L) :
    plaquetteAction (latticeTranslate a U) p =
      plaquetteAction U (plaquetteTranslationEquiv a p) := by
  have hs (x : Lattice4D L) (μ : Direction) : shift x μ + a = shift (x + a) μ := by
    simp [shift, add_right_comm]
  simp [plaquetteAction, plaquetteHolonomy, latticeTranslate, linkTranslationEquiv,
    plaquetteTranslationEquiv, hs]

/-- Translation invariance of the full action comes from reindexing all plaquettes. -/
theorem wilsonAction_latticeTranslate {L : ℕ} [NeZero L] (β : ℝ)
    (a : Lattice4D L) (U : GaugeConfig L) :
    wilsonAction β (latticeTranslate a U) = wilsonAction β U := by
  simp only [wilsonAction, plaquetteAction_latticeTranslate]
  rw [(plaquetteTranslationEquiv a).sum_comp]

/-- Exact lattice translation invariance of the actual normalized Wilson probability. -/
theorem wilsonProbability_translation_invariant (L : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    (a : Lattice4D L) :
    (wilsonProbability L β hβ).map (latticeTranslate a) = wilsonProbability L β hβ := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  change (∫ U, F U ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)).map
    (latticeTranslate a)) = _
  rw [integral_map_of_stronglyMeasurable (continuous_latticeTranslate a).measurable
    F.continuous.measurable.stronglyMeasurable, wilsonProbability_integral,
    wilsonProbability_integral]
  have hp := measurePreserving_latticeTranslate a
  have h := integral_map_of_stronglyMeasurable (μ := gaugeHaarMeasure L) hp.measurable
    ((wilsonWeight_measurable (measurable_wilsonAction β)).mul F.continuous.measurable).stronglyMeasurable
  rw [hp.map_eq] at h
  simp only [Pi.mul_apply, boltzmannWeight, wilsonAction_latticeTranslate] at h
  exact congrArg (fun x => x / wilsonPartition (gaugeHaarMeasure L) β) h.symm

/-- A single subsequence works simultaneously for all continuous finite-lattice observables. -/
theorem wilsonProbability_subsequence (L : ℕ) [NeZero L]
    (β : ℕ → ℝ) (hβ : ∀ n, 0 ≤ β n) :
    ∃ (ν : ProbabilityMeasure (GaugeConfig L)) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (fun n => wilsonProbability L (β (φ n)) (hβ (φ n))) atTop (𝓝 ν) ∧
      ∀ F : C(GaugeConfig L, ℝ),
        Tendsto (fun n => wilsonExpectation (gaugeHaarMeasure L) (β (φ n)) F)
          atTop (𝓝 (∫ U, F U ∂ν)) := by
  obtain ⟨ν, φ, hφ, hν⟩ := CompactSpace.tendsto_subseq
    (fun n => wilsonProbability L (β n) (hβ n))
  refine ⟨ν, φ, hφ, hν, ?_⟩
  intro F
  have h := (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp hν
  simpa only [Function.comp_def, wilsonProbability_integral] using h

/-- At fixed volume, every weak limit along couplings tending to infinity is supported
on the zero-action configurations. This does not identify a unique flat configuration. -/
theorem wilsonProbability_limit_action_zero {L : ℕ} [NeZero L]
    (β : ℕ → ℝ) (hβ : ∀ n, 0 ≤ β n) (hβtop : Tendsto β atTop atTop)
    (ν : ProbabilityMeasure (GaugeConfig L))
    (hν : Tendsto (fun n => wilsonProbability L (β n) (hβ n)) atTop (𝓝 ν)) :
    ∀ᵐ U ∂(ν : Measure (GaugeConfig L)), wilsonAction 1 U = 0 := by
  let S : C(GaugeConfig L, ℝ) := ⟨wilsonAction 1, continuous_wilsonAction 1⟩
  have hw := (ProbabilityMeasure.continuous_integral_continuousMap S).continuousAt.tendsto.comp hν
  have hz := (haarWilsonMeanAction_tendsto (L := L)).comp hβtop
  have heq : (∫ U, wilsonAction 1 U ∂(ν : Measure (GaugeConfig L))) = 0 := by
    apply tendsto_nhds_unique _ hz
    simpa only [Function.comp_def, S, ContinuousMap.coe_mk, wilsonProbability_toMeasure] using hw
  exact (integral_eq_zero_iff_of_nonneg (fun U => wilsonAction_nonneg (by norm_num) U)
    ((continuous_wilsonAction 1).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))).mp heq

/-- The actual fixed-lattice Wilson sequence has a probability-valued, zero-action weak
limit along a subsequence whenever its couplings tend to infinity. -/
theorem wilsonProbability_flat_subsequence (L : ℕ) [NeZero L]
    (β : ℕ → ℝ) (hβ : ∀ n, 0 ≤ β n) (hβtop : Tendsto β atTop atTop) :
    ∃ (ν : ProbabilityMeasure (GaugeConfig L)) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (fun n => wilsonProbability L (β (φ n)) (hβ (φ n))) atTop (𝓝 ν) ∧
      (∀ F : C(GaugeConfig L, ℝ),
        Tendsto (fun n => wilsonExpectation (gaugeHaarMeasure L) (β (φ n)) F)
          atTop (𝓝 (∫ U, F U ∂ν))) ∧
      (∀ᵐ U ∂(ν : Measure (GaugeConfig L)), wilsonAction 1 U = 0) := by
  obtain ⟨ν, φ, hφ, hν, hF⟩ := wilsonProbability_subsequence L β hβ
  exact ⟨ν, φ, hφ, hν, hF, wilsonProbability_limit_action_zero
    (fun n => β (φ n)) (fun n => hβ (φ n)) (hβtop.comp hφ.tendsto_atTop) ν hν⟩

/-- The actual dyadic block map is continuous in the finite product topology. -/
@[continuity, fun_prop]
theorem continuous_dyadicLinkBlockMap (L : ℕ) : Continuous (dyadicLinkBlockMap L) := by
  apply continuous_pi
  intro e
  exact (continuous_apply _).mul (continuous_apply _)

/-- The actual blocked Wilson law is the pushforward of the actual fine Wilson probability. -/
def blockedWilsonProbability (L : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β) :
    ProbabilityMeasure (GaugeConfig L) :=
  (wilsonProbability (2 * L) β hβ).map (dyadicLinkBlockMap L)

@[simp] theorem blockedWilsonProbability_toMeasure (L : ℕ) [NeZero L]
    (β : ℝ) (hβ : 0 ≤ β) :
    (blockedWilsonProbability L β hβ : Measure (GaugeConfig L)) =
      wilsonBlockedMeasure (gaugeHaarMeasure (2 * L)) β (dyadicLinkBlockMap L) := rfl

/-- Blocking and weak limits commute along the same fine-lattice subsequence. -/
theorem blockedWilsonProbability_tendsto {L : ℕ} [NeZero L]
    (β : ℕ → ℝ) (hβ : ∀ n, 0 ≤ β n)
    (ν : ProbabilityMeasure (GaugeConfig (2 * L)))
    (hν : Tendsto (fun n => wilsonProbability (2 * L) (β n) (hβ n)) atTop (𝓝 ν)) :
    Tendsto (fun n => blockedWilsonProbability L (β n) (hβ n))
      atTop (𝓝 (ν.map (dyadicLinkBlockMap L))) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hν
    (continuous_dyadicLinkBlockMap L)

/-- Countable integer lattice links, independent of a periodic lattice side length. -/
abbrev IntegerLink := (Fin 4 → ℤ) × Fin 4
abbrev IntegerGaugeConfig := IntegerLink → SU2

/-- The simultaneous conjugation action on every integer-lattice link. -/
def integerGlobalGaugeTransform (g : SU2) (U : IntegerGaugeConfig) : IntegerGaugeConfig :=
  fun e => g * U e * g⁻¹

@[continuity, fun_prop]
theorem continuous_integerGlobalGaugeTransform (g : SU2) :
    Continuous (integerGlobalGaugeTransform g) := by
  exact continuous_pi fun e => (continuous_const.mul (continuous_apply e)).mul continuous_const

/-- Translation by an integer four-vector, with unchanged lattice units. -/
def integerTranslate (a : Fin 4 → ℤ) (U : IntegerGaugeConfig) : IntegerGaugeConfig :=
  fun e => U (e.1 + a, e.2)

@[continuity, fun_prop]
theorem continuous_integerTranslate (a : Fin 4 → ℤ) : Continuous (integerTranslate a) :=
  continuous_pi fun _ => continuous_apply _

/-- A continuous observable of any chosen finite list of links is a common-space cylinder. -/
def cylinderObservable {ι : Type*} [Fintype ι] (edges : ι → IntegerLink)
    (F : C((ι → SU2), ℝ)) : C(IntegerGaugeConfig, ℝ) :=
  F.comp ⟨fun U i => U (edges i), continuous_pi (fun _ => continuous_apply _)⟩

@[simp] theorem cylinderObservable_apply {ι : Type*} [Fintype ι]
    (edges : ι → IntegerLink) (F : C((ι → SU2), ℝ)) (U : IntegerGaugeConfig) :
    cylinderObservable edges F U = F (fun i => U (edges i)) := rfl

/-- Extend the actual finite configuration periodically to the common integer lattice. -/
def periodicLift (L : ℕ) (U : GaugeConfig L) : IntegerGaugeConfig :=
  fun e => U ⟨fun i => (e.1 i : ZMod L), e.2⟩

@[continuity, fun_prop]
theorem continuous_periodicLift (L : ℕ) : Continuous (periodicLift L) := by
  apply continuous_pi
  intro e
  exact continuous_apply _

/-- A genuine probability law on the common countable link field for each finite Wilson law. -/
def periodicWilsonProbability (L : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β) :
    ProbabilityMeasure IntegerGaugeConfig :=
  (wilsonProbability L β hβ).map (periodicLift L)

/-- Periodic extension intertwines constant finite-lattice gauge transformations exactly. -/
theorem periodicLift_globalGaugeTransform (L : ℕ) (g : SU2) (U : GaugeConfig L) :
    periodicLift L (gaugeTransform (fun _ => g) U) =
      integerGlobalGaugeTransform g (periodicLift L U) := rfl

/-- Arbitrary finite volumes and couplings retain the same exact global gauge symmetry
on the common link space. -/
theorem periodicWilsonProbability_globalGauge_invariant (L : ℕ) [NeZero L]
    (β : ℝ) (hβ : 0 ≤ β) (g : SU2) :
    (periodicWilsonProbability L β hβ).map (integerGlobalGaugeTransform g) =
      periodicWilsonProbability L β hβ := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((wilsonProbability L β hβ : Measure (GaugeConfig L)).map (periodicLift L)).map
    (integerGlobalGaugeTransform g) = (wilsonProbability L β hβ : Measure _).map (periodicLift L)
  rw [Measure.map_map (continuous_integerGlobalGaugeTransform g).measurable
    (continuous_periodicLift L).measurable]
  have hc : integerGlobalGaugeTransform g ∘ periodicLift L =
      periodicLift L ∘ gaugeTransform (fun _ => g) := rfl
  rw [hc, ← Measure.map_map (continuous_periodicLift L).measurable
    (continuous_gaugeTransform (fun _ => g)).measurable]
  have hg := congrArg (fun μ : ProbabilityMeasure (GaugeConfig L) =>
    (μ : Measure (GaugeConfig L))) (wilsonProbability_gauge_invariant L β hβ (fun _ => g))
  change (wilsonProbability L β hβ : Measure (GaugeConfig L)).map
    (gaugeTransform (fun _ => g)) = _ at hg
  rw [hg]

/-- Global gauge symmetry is a proved property of every common-space Wilson weak limit,
including varying volumes. This is not local gauge reconstruction on rescaled fields. -/
theorem periodicWilsonProbability_limit_globalGauge_invariant
    (L : ℕ → ℕ) [∀ n, NeZero (L n)] (β : ℕ → ℝ) (hβ : ∀ n, 0 ≤ β n)
    (ν : ProbabilityMeasure IntegerGaugeConfig)
    (hν : Tendsto (fun n => periodicWilsonProbability (L n) (β n) (hβ n)) atTop (𝓝 ν))
    (g : SU2) : ν.map (integerGlobalGaugeTransform g) = ν := by
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hν
    (continuous_integerGlobalGaugeTransform g)
  simp only [periodicWilsonProbability_globalGauge_invariant] at hm
  exact tendsto_nhds_unique hm hν

/-- Periodic extension intertwines integer translations and their finite-lattice residues. -/
theorem periodicLift_latticeTranslate (L : ℕ) (a : Fin 4 → ℤ) (U : GaugeConfig L) :
    periodicLift L (latticeTranslate (fun i => (a i : ZMod L)) U) =
      integerTranslate a (periodicLift L U) := by
  funext e
  simp only [periodicLift, latticeTranslate, integerTranslate, linkTranslationEquiv,
    Equiv.coe_fn_mk]
  congr 2
  funext i
  exact (Int.cast_add (e.1 i) (a i)).symm

/-- Exact integer translation invariance of every periodic Wilson law, with no large-volume
or small-coupling approximation. -/
theorem periodicWilsonProbability_translation_invariant (L : ℕ) [NeZero L]
    (β : ℝ) (hβ : 0 ≤ β) (a : Fin 4 → ℤ) :
    (periodicWilsonProbability L β hβ).map (integerTranslate a) =
      periodicWilsonProbability L β hβ := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((wilsonProbability L β hβ : Measure (GaugeConfig L)).map (periodicLift L)).map
    (integerTranslate a) = (wilsonProbability L β hβ : Measure _).map (periodicLift L)
  rw [Measure.map_map (continuous_integerTranslate a).measurable
    (continuous_periodicLift L).measurable]
  have hc : integerTranslate a ∘ periodicLift L =
      periodicLift L ∘ latticeTranslate (fun i => (a i : ZMod L)) := by
    funext U
    exact (periodicLift_latticeTranslate L a U).symm
  rw [hc, ← Measure.map_map (continuous_periodicLift L).measurable
    (continuous_latticeTranslate _).measurable]
  have hg := congrArg (fun μ : ProbabilityMeasure (GaugeConfig L) =>
    (μ : Measure (GaugeConfig L)))
    (wilsonProbability_translation_invariant L β hβ (fun i => (a i : ZMod L)))
  change (wilsonProbability L β hβ : Measure (GaugeConfig L)).map
    (latticeTranslate (fun i => (a i : ZMod L))) = _ at hg
  rw [hg]

/-- All common-space Wilson weak limits are invariant under every integer translation.
This does not assert invariance under real translations or rotations after rescaling. -/
theorem periodicWilsonProbability_limit_translation_invariant
    (L : ℕ → ℕ) [∀ n, NeZero (L n)] (β : ℕ → ℝ) (hβ : ∀ n, 0 ≤ β n)
    (ν : ProbabilityMeasure IntegerGaugeConfig)
    (hν : Tendsto (fun n => periodicWilsonProbability (L n) (β n) (hβ n)) atTop (𝓝 ν))
    (a : Fin 4 → ℤ) : ν.map (integerTranslate a) = ν := by
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hν
    (continuous_integerTranslate a)
  simp only [periodicWilsonProbability_translation_invariant] at hm
  exact tendsto_nhds_unique hm hν

/-- Every continuous common-space observable pulls back to the actual finite Wilson expectation. -/
theorem periodicWilsonProbability_integral (L : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β)
    (F : C(IntegerGaugeConfig, ℝ)) :
    (∫ U, F U ∂periodicWilsonProbability L β hβ) =
      wilsonExpectation (gaugeHaarMeasure L) β (fun U => F (periodicLift L U)) := by
  change (∫ U, F U ∂(wilsonProbability L β hβ : Measure (GaugeConfig L)).map
    (periodicLift L)) = _
  rw [integral_map_of_stronglyMeasurable (continuous_periodicLift L).measurable
    F.continuous.measurable.stronglyMeasurable, wilsonProbability_integral]

/-- Varying finite volumes and couplings admit a common probability limit. The chosen
subsequence works for all continuous observables on the countable link product, hence for
all continuous finite-cylinder observables. No uniform estimate is assumed here. -/
theorem periodicWilsonProbability_subsequence (L : ℕ → ℕ) [∀ n, NeZero (L n)]
    (β : ℕ → ℝ) (hβ : ∀ n, 0 ≤ β n) :
    ∃ (ν : ProbabilityMeasure IntegerGaugeConfig) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (fun n => periodicWilsonProbability (L (φ n)) (β (φ n)) (hβ (φ n)))
        atTop (𝓝 ν) ∧
      ∀ F : C(IntegerGaugeConfig, ℝ),
        Tendsto (fun n => wilsonExpectation (gaugeHaarMeasure (L (φ n))) (β (φ n))
          (fun U => F (periodicLift (L (φ n)) U))) atTop (𝓝 (∫ U, F U ∂ν)) := by
  obtain ⟨ν, φ, hφ, hν⟩ := CompactSpace.tendsto_subseq
    (fun n => periodicWilsonProbability (L n) (β n) (hβ n))
  refine ⟨ν, φ, hφ, hν, ?_⟩
  intro F
  have h := (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp hν
  simpa only [Function.comp_def, periodicWilsonProbability_integral] using h

/-- Actual varying-volume Wilson laws have a common weak limit with proved global gauge
and integer translation symmetries. The hypotheses concern only the chosen finite laws;
no symmetry or reconstruction assumption is imposed on the limit. -/
theorem periodicWilsonProbability_symmetric_subsequence
    (L : ℕ → ℕ) [∀ n, NeZero (L n)] (β : ℕ → ℝ) (hβ : ∀ n, 0 ≤ β n) :
    ∃ (ν : ProbabilityMeasure IntegerGaugeConfig) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (fun n => periodicWilsonProbability (L (φ n)) (β (φ n)) (hβ (φ n)))
        atTop (𝓝 ν) ∧
      (∀ F : C(IntegerGaugeConfig, ℝ),
        Tendsto (fun n => wilsonExpectation (gaugeHaarMeasure (L (φ n))) (β (φ n))
          (fun U => F (periodicLift (L (φ n)) U))) atTop (𝓝 (∫ U, F U ∂ν))) ∧
      (∀ g : SU2, ν.map (integerGlobalGaugeTransform g) = ν) ∧
      (∀ a : Fin 4 → ℤ, ν.map (integerTranslate a) = ν) := by
  obtain ⟨ν, φ, hφ, hν, hF⟩ := periodicWilsonProbability_subsequence L β hβ
  let : ∀ n, NeZero ((L ∘ φ) n) := fun n => inferInstanceAs (NeZero (L (φ n)))
  refine ⟨ν, φ, hφ, hν, hF, ?_, ?_⟩
  · exact periodicWilsonProbability_limit_globalGauge_invariant
      (L ∘ φ) (β ∘ φ) (fun n => hβ (φ n)) ν hν
  · exact periodicWilsonProbability_limit_translation_invariant
      (L ∘ φ) (β ∘ φ) (fun n => hβ (φ n)) ν hν

/-- Cylinder expectations and supplied nonnegative finite kernel sums pass through
weak convergence of unscaled periodic Wilson laws. `K_rp` is an arbitrary real
continuous kernel; identifying it with a reflected observable hierarchy and
proving its positivity are separate inputs. No cutoff limit is required here. -/
theorem cylinderObservable_periodicWilsonProbability_tendsto_and_reflection_positivity_transfer
    (L : ℕ → ℕ) [∀ n, NeZero (L n)]
    (β : ℕ → ℝ) (hβ : ∀ n, 0 ≤ β n)
    (ν : ProbabilityMeasure IntegerGaugeConfig)
    (hν : Tendsto (fun n => periodicWilsonProbability (L n) (β n) (hβ n)) atTop (𝓝 ν))
    {ι : Type*} [Fintype ι] (edges : ι → IntegerLink) (F : C((ι → SU2), ℝ))
    (m : ℕ) (c : Fin m → ℝ) (K_rp : Fin m → Fin m → C(IntegerGaugeConfig, ℝ))
    (h_rp_finite : ∀ n : ℕ,
      0 ≤ ∑ a : Fin m, ∑ b : Fin m,
        c a * c b * wilsonExpectation (gaugeHaarMeasure (L n)) (β n)
          (fun U => K_rp a b (periodicLift (L n) U))) :
    Tendsto (fun n => wilsonExpectation (gaugeHaarMeasure (L n)) (β n)
      (fun U => cylinderObservable edges F (periodicLift (L n) U)))
      atTop (𝓝 (∫ U, cylinderObservable edges F U ∂ν)) ∧
    0 ≤ ∑ a : Fin m, ∑ b : Fin m, c a * c b * (∫ U, K_rp a b U ∂ν) := by
  refine ⟨?_, ?_⟩
  · have h :=
      (ProbabilityMeasure.continuous_integral_continuousMap
        (cylinderObservable edges F)).continuousAt.tendsto.comp hν
    simpa only [Function.comp_def, periodicWilsonProbability_integral] using h
  · have h_term : ∀ a b : Fin m,
        Tendsto (fun n => c a * c b * wilsonExpectation (gaugeHaarMeasure (L n)) (β n)
          (fun U => K_rp a b (periodicLift (L n) U)))
          atTop (𝓝 (c a * c b * (∫ U, K_rp a b U ∂ν))) := by
      intro a b
      have hK :=
        (ProbabilityMeasure.continuous_integral_continuousMap (K_rp a b)).continuousAt.tendsto.comp hν
      have hK' : Tendsto (fun n => wilsonExpectation (gaugeHaarMeasure (L n)) (β n)
          (fun U => K_rp a b (periodicLift (L n) U))) atTop (𝓝 (∫ U, K_rp a b U ∂ν)) := by
        simpa only [Function.comp_def, periodicWilsonProbability_integral] using hK
      exact tendsto_const_nhds.mul hK'
    have h_sum : Tendsto (fun n => ∑ a : Fin m, ∑ b : Fin m, c a * c b *
        wilsonExpectation (gaugeHaarMeasure (L n)) (β n) (fun U => K_rp a b (periodicLift (L n) U)))
        atTop (𝓝 (∑ a : Fin m, ∑ b : Fin m, c a * c b * (∫ U, K_rp a b U ∂ν))) :=
      tendsto_finsetSum _ (fun a _ => tendsto_finsetSum _ (fun b _ => h_term a b))
    exact ge_of_tendsto' h_sum h_rp_finite

/-- Scalar exponential envelope; `dist` has no built-in relation to support separation. -/
noncomputable def infiniteVolumeClusterEnvelope (C_clust m_gap dist : ℝ) : ℝ :=
  C_clust * Real.exp (-(m_gap * dist))

/-- A supplied covariance bound passes to a weak limit. The positive rate is an
input, and the final limit concerns the scalar envelope alone. Spatial clustering
needs a family of separated observables and bounds tied to their actual supports. -/
theorem periodicWilsonProbability_exponential_clustering_and_dobrushin_tail_transfer
    (L : ℕ → ℕ) [∀ n, NeZero (L n)]
    (β : ℕ → ℝ) (hβ : ∀ n, 0 ≤ β n)
    (ν : ProbabilityMeasure IntegerGaugeConfig)
    (hν : Tendsto (fun n => periodicWilsonProbability (L n) (β n) (hβ n)) atTop (𝓝 ν))
    (F G : C(IntegerGaugeConfig, ℝ))
    {C_clust m_gap dist : ℝ} (hC : 0 ≤ C_clust) (hm : 0 < m_gap) (hdist : 0 ≤ dist)
    (h_clust_finite : ∀ n : ℕ,
      |wilsonExpectation (gaugeHaarMeasure (L n)) (β n)
          (fun U => (F * G) (periodicLift (L n) U)) -
        wilsonExpectation (gaugeHaarMeasure (L n)) (β n)
          (fun U => F (periodicLift (L n) U)) *
          wilsonExpectation (gaugeHaarMeasure (L n)) (β n)
            (fun U => G (periodicLift (L n) U))| ≤
        infiniteVolumeClusterEnvelope C_clust m_gap dist) :
    |(∫ U, (F * G) U ∂ν) - (∫ U, F U ∂ν) * (∫ U, G U ∂ν)| ≤
      infiniteVolumeClusterEnvelope C_clust m_gap dist ∧
    (0 ≤ infiniteVolumeClusterEnvelope C_clust m_gap dist ∧
      infiniteVolumeClusterEnvelope C_clust m_gap dist ≤ C_clust) ∧
    Tendsto (fun d : ℝ => infiniteVolumeClusterEnvelope C_clust m_gap d) atTop (𝓝 0) := by
  have hFG_raw :=
    (ProbabilityMeasure.continuous_integral_continuousMap (F * G)).continuousAt.tendsto.comp hν
  have hFG : Tendsto (fun n => wilsonExpectation (gaugeHaarMeasure (L n)) (β n)
      (fun U => (F * G) (periodicLift (L n) U))) atTop (𝓝 (∫ U, (F * G) U ∂ν)) := by
    simpa only [Function.comp_def, periodicWilsonProbability_integral] using hFG_raw
  have hF_raw :=
    (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp hν
  have hF : Tendsto (fun n => wilsonExpectation (gaugeHaarMeasure (L n)) (β n)
      (fun U => F (periodicLift (L n) U))) atTop (𝓝 (∫ U, F U ∂ν)) := by
    simpa only [Function.comp_def, periodicWilsonProbability_integral] using hF_raw
  have hG_raw :=
    (ProbabilityMeasure.continuous_integral_continuousMap G).continuousAt.tendsto.comp hν
  have hG : Tendsto (fun n => wilsonExpectation (gaugeHaarMeasure (L n)) (β n)
      (fun U => G (periodicLift (L n) U))) atTop (𝓝 (∫ U, G U ∂ν)) := by
    simpa only [Function.comp_def, periodicWilsonProbability_integral] using hG_raw
  have h_abs : Tendsto (fun n =>
      |wilsonExpectation (gaugeHaarMeasure (L n)) (β n) (fun U => (F * G) (periodicLift (L n) U)) -
        wilsonExpectation (gaugeHaarMeasure (L n)) (β n) (fun U => F (periodicLift (L n) U)) *
          wilsonExpectation (gaugeHaarMeasure (L n)) (β n) (fun U => G (periodicLift (L n) U))|)
      atTop (𝓝 |(∫ U, (F * G) U ∂ν) - (∫ U, F U ∂ν) * (∫ U, G U ∂ν)|) :=
    (hFG.sub (hF.mul hG)).abs
  have h_lim_le := le_of_tendsto' h_abs h_clust_finite
  have h_env_nonneg : 0 ≤ infiniteVolumeClusterEnvelope C_clust m_gap dist :=
    mul_nonneg hC (Real.exp_pos _).le
  have h_exp_le_one : Real.exp (-(m_gap * dist)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hmd : 0 ≤ m_gap * dist := mul_nonneg hm.le hdist
    linarith
  have h_env_le_C : infiniteVolumeClusterEnvelope C_clust m_gap dist ≤ C_clust := by
    dsimp [infiniteVolumeClusterEnvelope]
    nlinarith
  have h_tendsto : Tendsto (fun d : ℝ => infiniteVolumeClusterEnvelope C_clust m_gap d) atTop (𝓝 0) := by
    have hm_top : Tendsto (fun d : ℝ => m_gap * d) atTop atTop := by
      simpa only [mul_comm, id_eq] using tendsto_id.atTop_mul_const hm
    have hexp_zero : Tendsto (fun d : ℝ => Real.exp (-(m_gap * d))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hm_top
    simpa [infiniteVolumeClusterEnvelope] using hexp_zero.const_mul C_clust
  exact ⟨h_lim_le, ⟨h_env_nonneg, h_env_le_C⟩, h_tendsto⟩

/-- Absolute difference of two real numbers; no rotation action is encoded here. -/
noncomputable def so4IsotropicCorrelatorDefect (C_obs C_iso : ℝ) : ℝ :=
  |C_obs - C_iso|

/-- Two specified continuous observables have equal limiting expectations when
their prelimit difference is bounded by a supplied null sequence. A rotation
action, rotated-observable identity and anisotropy estimate are not derived;
this implication alone establishes neither SO(4) covariance nor a continuum limit. -/
theorem periodicWilsonProbability_so4_isotropy_recovery_and_correlator_convergence
    (L : ℕ → ℕ) [∀ n, NeZero (L n)]
    (β : ℕ → ℝ) (hβ : ∀ n, 0 ≤ β n)
    (ν : ProbabilityMeasure IntegerGaugeConfig)
    (hν : Tendsto (fun n => periodicWilsonProbability (L n) (β n) (hβ n)) atTop (𝓝 ν))
    (F_rot F_axis : C(IntegerGaugeConfig, ℝ))
    (δ_aniso : ℕ → ℝ) (hδ_zero : Tendsto δ_aniso atTop (𝓝 0))
    (h_aniso : ∀ n : ℕ,
      |wilsonExpectation (gaugeHaarMeasure (L n)) (β n)
          (fun U => F_rot (periodicLift (L n) U)) -
        wilsonExpectation (gaugeHaarMeasure (L n)) (β n)
          (fun U => F_axis (periodicLift (L n) U))| ≤ δ_aniso n) :
    so4IsotropicCorrelatorDefect (∫ U, F_rot U ∂ν) (∫ U, F_axis U ∂ν) = 0 ∧
    (∫ U, F_rot U ∂ν) = (∫ U, F_axis U ∂ν) := by
  have hF_rot_raw :=
    (ProbabilityMeasure.continuous_integral_continuousMap F_rot).continuousAt.tendsto.comp hν
  have hF_rot : Tendsto (fun n => wilsonExpectation (gaugeHaarMeasure (L n)) (β n)
      (fun U => F_rot (periodicLift (L n) U))) atTop (𝓝 (∫ U, F_rot U ∂ν)) := by
    simpa only [Function.comp_def, periodicWilsonProbability_integral] using hF_rot_raw
  have hF_axis_raw :=
    (ProbabilityMeasure.continuous_integral_continuousMap F_axis).continuousAt.tendsto.comp hν
  have hF_axis : Tendsto (fun n => wilsonExpectation (gaugeHaarMeasure (L n)) (β n)
      (fun U => F_axis (periodicLift (L n) U))) atTop (𝓝 (∫ U, F_axis U ∂ν)) := by
    simpa only [Function.comp_def, periodicWilsonProbability_integral] using hF_axis_raw
  have h_abs : Tendsto (fun n =>
      |wilsonExpectation (gaugeHaarMeasure (L n)) (β n)
          (fun U => F_rot (periodicLift (L n) U)) -
        wilsonExpectation (gaugeHaarMeasure (L n)) (β n)
          (fun U => F_axis (periodicLift (L n) U))|)
      atTop (𝓝 (so4IsotropicCorrelatorDefect (∫ U, F_rot U ∂ν) (∫ U, F_axis U ∂ν))) := by
    simpa only [so4IsotropicCorrelatorDefect] using (hF_rot.sub hF_axis).abs
  have h_le_zero : so4IsotropicCorrelatorDefect (∫ U, F_rot U ∂ν) (∫ U, F_axis U ∂ν) ≤ 0 :=
    le_of_tendsto_of_tendsto h_abs hδ_zero (Eventually.of_forall h_aniso)
  have h_nonneg : 0 ≤ so4IsotropicCorrelatorDefect (∫ U, F_rot U ∂ν) (∫ U, F_axis U ∂ν) :=
    abs_nonneg _
  have h_def_zero : so4IsotropicCorrelatorDefect (∫ U, F_rot U ∂ν) (∫ U, F_axis U ∂ν) = 0 :=
    le_antisymm h_le_zero h_nonneg
  have h_eq : (∫ U, F_rot U ∂ν) = (∫ U, F_axis U ∂ν) :=
    sub_eq_zero.mp (abs_eq_zero.mp h_def_zero)
  exact ⟨h_def_zero, h_eq⟩

/-! ## Infinite-Volume Local Gauge Invariance & Continuous Euclidean $SO(4) \ltimes \mathbb{R}^4$ Loop Action -/

/-- Countable four-dimensional integer lattice site `x ∈ ℤ^4`. -/
abbrev IntegerSite : Type := Fin 4 → ℤ

/-- Unit forward shift `x + e_μ` of an integer lattice site `x ∈ ℤ^4` in direction `μ : Fin 4`. -/
def integerShift (x : IntegerSite) (μ : Fin 4) : IntegerSite :=
  fun i => x i + if i = μ then 1 else 0

/-- Infinite-volume local gauge transformation on the countable link space `IntegerGaugeConfig`:
for any site-dependent gauge field `g : IntegerSite → SU2`, transforms each directed link
`e = (x, μ)` by `g(x) * U(x, μ) * g(x + e_μ)⁻¹`. -/
def integerLocalGaugeTransform (g : IntegerSite → SU2) (U : IntegerGaugeConfig) :
    IntegerGaugeConfig :=
  fun e => g e.1 * U e * (g (integerShift e.1 e.2))⁻¹

/-- Periodic lift of a finite-torus local gauge transformation `g : GaugeTransformation L` to
`IntegerSite → SU2` via residue projection `(x i : ZMod L)`. -/
def periodicLocalGaugeLift (L : ℕ) (g : GaugeTransformation L) : IntegerSite → SU2 :=
  fun x => g (fun i => (x i : ZMod L))

/-- Continuity, group-action laws, specialization to `integerGlobalGaugeTransform` for constant
gauge fields, and exact intertwining `periodicLift L (gaugeTransform g U) = integerLocalGaugeTransform (periodicLocalGaugeLift L g) (periodicLift L U)`
together with local gauge invariance of `periodicWilsonProbability L β hβ` for every finite-torus
local gauge transformation `g : GaugeTransformation L`. -/
theorem continuous_integerLocalGaugeTransform_and_periodicLift_intertwining
    (L : ℕ) [NeZero L] (β : ℝ) (hβ : 0 ≤ β) :
    (∀ g : IntegerSite → SU2, Continuous (integerLocalGaugeTransform g)) ∧
    (∀ U : IntegerGaugeConfig, integerLocalGaugeTransform (fun _ => 1) U = U) ∧
    (∀ (g₀ : SU2) (U : IntegerGaugeConfig),
      integerLocalGaugeTransform (fun _ => g₀) U = integerGlobalGaugeTransform g₀ U) ∧
    (∀ (g : GaugeTransformation L) (U : GaugeConfig L),
      periodicLift L (gaugeTransform g U) =
        integerLocalGaugeTransform (periodicLocalGaugeLift L g) (periodicLift L U)) ∧
    (∀ g : GaugeTransformation L,
      (periodicWilsonProbability L β hβ).map
        (integerLocalGaugeTransform (periodicLocalGaugeLift L g)) =
        periodicWilsonProbability L β hβ) := by
  have h_cont : ∀ g : IntegerSite → SU2, Continuous (integerLocalGaugeTransform g) :=
    fun g => continuous_pi fun e => (continuous_const.mul (continuous_apply e)).mul continuous_const
  have h_intertwine : ∀ (g : GaugeTransformation L) (U : GaugeConfig L),
      periodicLift L (gaugeTransform g U) =
        integerLocalGaugeTransform (periodicLocalGaugeLift L g) (periodicLift L U) := by
    intro g U
    funext e
    have h_shift : shift (fun i => (e.1 i : ZMod L)) e.2 =
        (fun i => ((integerShift e.1 e.2 i : ℤ) : ZMod L)) := by
      funext i
      dsimp [shift, unitVec, integerShift]
      rw [Int.cast_add]
      split_ifs <;> simp
    dsimp [periodicLift, gaugeTransform, integerLocalGaugeTransform, periodicLocalGaugeLift]
    rw [h_shift]
  refine ⟨h_cont, ?_, ?_, h_intertwine, ?_⟩
  · intro U
    funext e
    simp [integerLocalGaugeTransform]
  · intro g₀ U
    rfl
  · intro g
    apply ProbabilityMeasure.toMeasure_injective
    change ((wilsonProbability L β hβ : Measure (GaugeConfig L)).map (periodicLift L)).map
      (integerLocalGaugeTransform (periodicLocalGaugeLift L g)) =
      (wilsonProbability L β hβ : Measure _).map (periodicLift L)
    rw [Measure.map_map (h_cont (periodicLocalGaugeLift L g)).measurable
      (continuous_periodicLift L).measurable]
    have hc : integerLocalGaugeTransform (periodicLocalGaugeLift L g) ∘ periodicLift L =
        periodicLift L ∘ gaugeTransform g := by
      funext U
      exact (h_intertwine g U).symm
    rw [hc, ← Measure.map_map (continuous_periodicLift L).measurable
      (continuous_gaugeTransform g).measurable]
    have hg := congrArg (fun μ : ProbabilityMeasure (GaugeConfig L) =>
      (μ : Measure (GaugeConfig L))) (wilsonProbability_gauge_invariant L β hβ g)
    change (wilsonProbability L β hβ : Measure (GaugeConfig L)).map
      (gaugeTransform g) = _ at hg
    rw [hg]

/-- Any infinite-volume local gauge transformation `g : IntegerSite → SU2` that eventually agrees
with a sequence of `L n`-periodic local gauge transformations `periodicLocalGaugeLift (L n) (g_seq n)`
preserves every weak limit `ν` of `periodicWilsonProbability (L n) (β n) (hβ n)`. -/
theorem periodicWilsonProbability_limit_localGauge_invariant_of_eventually_periodicLift
    (L : ℕ → ℕ) [∀ n, NeZero (L n)] (β : ℕ → ℝ) (hβ : ∀ n, 0 ≤ β n)
    (ν : ProbabilityMeasure IntegerGaugeConfig)
    (hν : Tendsto (fun n => periodicWilsonProbability (L n) (β n) (hβ n)) atTop (𝓝 ν))
    (g : IntegerSite → SU2)
    (g_seq : ∀ n, GaugeTransformation (L n))
    (h_ev : ∀ᶠ n in atTop, periodicLocalGaugeLift (L n) (g_seq n) = g) :
    ν.map (integerLocalGaugeTransform g) = ν := by
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hν
    ((continuous_integerLocalGaugeTransform_and_periodicLift_intertwining 1 0 le_rfl).1 g)
  have h_eq : (fun n => (periodicWilsonProbability (L n) (β n) (hβ n)).map
      (integerLocalGaugeTransform g)) =ᶠ[atTop]
      (fun n => periodicWilsonProbability (L n) (β n) (hβ n)) :=
    h_ev.mono fun n hn => by
      rw [← hn]
      exact (continuous_integerLocalGaugeTransform_and_periodicLift_intertwining
        (L n) (β n) (hβ n)).2.2.2.2 (g_seq n)
  exact tendsto_nhds_unique (hm.congr' h_eq) hν

/-- Point in four-dimensional continuum Euclidean space `ℝ^4`. -/
abbrev EuclideanPoint4D : Type := Fin 4 → ℝ

/-- Parameterized continuum loop `γ : ℝ → ℝ^4` in four-dimensional Euclidean space. -/
abbrev ContinuumLoop4D : Type := ℝ → EuclideanPoint4D

/-- Special orthogonal matrix predicate `R ∈ SO(4)`: `Rᵀ R = I` and `det R = 1`. -/
def IsSO4Matrix (R : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  R.transpose * R = 1 ∧ R.det = 1

/-- Euclidean rigid motion `(R, a) ∈ SO(4) ⋉ ℝ^4` acting on a continuum loop `γ : ℝ → ℝ^4` by
`(s ↦ R γ(s) + a)`. -/
def actEuclideanLoop4D (R : Matrix (Fin 4) (Fin 4) ℝ) (a : EuclideanPoint4D)
    (γ : ContinuumLoop4D) : ContinuumLoop4D :=
  fun s => Matrix.mulVec R (γ s) + a

/-- Group-action laws and Euclidean dot-product norm preservation for `actEuclideanLoop4D` and
`IsSO4Matrix`:
1. Identity action `actEuclideanLoop4D 1 0 γ = γ`,
2. Semidirect-product composition
   `actEuclideanLoop4D R1 a1 (actEuclideanLoop4D R2 a2 γ) = actEuclideanLoop4D (R1 * R2) (Matrix.mulVec R1 a2 + a1) γ`,
3. Closure of `IsSO4Matrix` under matrix multiplication (`IsSO4Matrix 1` and
   `IsSO4Matrix R1 → IsSO4Matrix R2 → IsSO4Matrix (R1 * R2)`), and
4. Exact Euclidean inner-product preservation
   `dotProduct (mulVec R x) (mulVec R y) = dotProduct x y` whenever `R.transpose * R = 1`. -/
theorem actEuclideanLoop4D_group_laws_and_norm_preservation :
    (∀ γ : ContinuumLoop4D, actEuclideanLoop4D 1 0 γ = γ) ∧
    (∀ (R1 R2 : Matrix (Fin 4) (Fin 4) ℝ) (a1 a2 : EuclideanPoint4D) (γ : ContinuumLoop4D),
      actEuclideanLoop4D R1 a1 (actEuclideanLoop4D R2 a2 γ) =
        actEuclideanLoop4D (R1 * R2) (Matrix.mulVec R1 a2 + a1) γ) ∧
    (IsSO4Matrix 1 ∧
      ∀ {R1 R2 : Matrix (Fin 4) (Fin 4) ℝ},
        IsSO4Matrix R1 → IsSO4Matrix R2 → IsSO4Matrix (R1 * R2)) ∧
    (∀ {R : Matrix (Fin 4) (Fin 4) ℝ}, R.transpose * R = 1 →
      ∀ x y : EuclideanPoint4D,
        dotProduct (Matrix.mulVec R x) (Matrix.mulVec R y) = dotProduct x y) := by
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro γ
    funext s
    simp [actEuclideanLoop4D]
  · intro R1 R2 a1 a2 γ
    funext s
    simp only [actEuclideanLoop4D, Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]
  · exact ⟨by simp, by simp⟩
  · intro R1 R2 h1 h2
    refine ⟨?_, ?_⟩
    · calc
        (R1 * R2).transpose * (R1 * R2)
        _ = (R2.transpose * R1.transpose) * (R1 * R2) := by rw [Matrix.transpose_mul]
        _ = R2.transpose * (R1.transpose * (R1 * R2)) := by rw [Matrix.mul_assoc]
        _ = R2.transpose * ((R1.transpose * R1) * R2) := by rw [← Matrix.mul_assoc R1.transpose]
        _ = R2.transpose * (1 * R2) := by rw [h1.1]
        _ = R2.transpose * R2 := by rw [Matrix.one_mul]
        _ = 1 := h2.1
    · rw [Matrix.det_mul, h1.2, h2.2, mul_one]
  · intro R hR x y
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hR,
      Matrix.one_mulVec]

#assert_zfc_axioms

end JesseMath.Physics.YangMillsContinuumCompactness
