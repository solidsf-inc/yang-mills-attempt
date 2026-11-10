import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.LatticeYangMills
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

open scoped ENNReal

/-!
# Concrete SU(2) Haar probability and finite lattice gauge invariance

The topology is the matrix topology on the existing `SU2` representation. Compactness is proved
from the closed special-unitary equations and the unitary entry bound. Haar measure is normalized
on the whole compact group, then used independently on each finite lattice link.
-/

open Matrix MeasureTheory MeasureTheory.Measure Set Topology TopologicalSpace

noncomputable section

namespace JesseMath.Physics
namespace SU2

/-- The existing matrix representation is exactly Mathlib's special unitary group. -/
def equivSpecialUnitary : SU2 ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ where
  toFun A := ⟨A.mat, (Matrix.mem_unitaryGroup_iff').2 A.unitary, A.det_one⟩
  invFun A := ⟨A.val, (Matrix.mem_unitaryGroup_iff').1 A.property.1, A.property.2⟩
  left_inv _ := ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := rfl

instance : TopologicalSpace SU2 := TopologicalSpace.induced mat inferInstance

theorem isEmbedding_mat : IsEmbedding (mat : SU2 → Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨⟨rfl⟩, fun _ _ h => ext h⟩

@[continuity, fun_prop]
theorem continuous_mat : Continuous (mat : SU2 → Matrix (Fin 2) (Fin 2) ℂ) :=
  continuous_induced_dom

instance : T2Space SU2 := isEmbedding_mat.t2Space
instance : SecondCountableTopology SU2 := by
  let : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact isEmbedding_mat.isInducing.secondCountableTopology

instance : ContinuousMul SU2 where
  continuous_mul := continuous_induced_rng.mpr <| by
    change Continuous (fun p : SU2 × SU2 => p.1.mat * p.2.mat)
    exact (continuous_mat.comp continuous_fst).mul (continuous_mat.comp continuous_snd)

instance : ContinuousInv SU2 where
  continuous_inv := continuous_induced_rng.mpr <| by
    change Continuous (fun A : SU2 => A.mat.conjTranspose)
    fun_prop

instance : IsTopologicalGroup SU2 where

/-- The group identification also preserves the concrete matrix topology. -/
def homeomorphSpecialUnitary : SU2 ≃ₜ Matrix.specialUnitaryGroup (Fin 2) ℂ where
  toEquiv := equivSpecialUnitary.toEquiv
  continuous_toFun := continuous_mat.subtype_mk _
  continuous_invFun := continuous_induced_rng.mpr continuous_subtype_val

theorem isCompact_specialUnitary :
    IsCompact (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hd : IsClosed {A : Matrix (Fin 2) (Fin 2) ℂ | A.det = 1} :=
    isClosed_eq continuous_id.matrix_det continuous_const
  have hc : IsClosed (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
    change IsClosed ((_root_.unitary (Matrix (Fin 2) (Fin 2) ℂ) : Set (Matrix (Fin 2) (Fin 2) ℂ)) ∩
      {A : Matrix (Fin 2) (Fin 2) ℂ | A.det = 1})
    exact isClosed_unitary.inter hd
  apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset hc
  intro A hA i j
  rw [Metric.mem_closedBall, dist_zero_right]
  exact entry_norm_bound_of_unitary hA.1 i j

instance : CompactSpace SU2 := by
  let : CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    isCompact_iff_compactSpace.mp isCompact_specialUnitary
  exact homeomorphSpecialUnitary.symm.compactSpace

instance : PolishSpace SU2 := by
  let : PolishSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (PolishSpace (Fin 2 → Fin 2 → ℂ))
  let : PolishSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    isCompact_specialUnitary.isClosed.polishSpace
  exact homeomorphSpecialUnitary.isClosedEmbedding.polishSpace

instance : MeasurableSpace SU2 := borel SU2
instance : BorelSpace SU2 := ⟨rfl⟩

@[fun_prop]
theorem measurable_mat : Measurable (mat : SU2 → Matrix (Fin 2) (Fin 2) ℂ) :=
  continuous_mat.measurable

/-- The compact normalization set is the whole group. -/
def haarNormalization : PositiveCompacts SU2 :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- Normalized Haar measure constructed on the concrete compact matrix group. -/
noncomputable def haarProbability : Measure SU2 := Measure.haarMeasure haarNormalization

instance : Measure.IsHaarMeasure haarProbability := by
  unfold haarProbability
  infer_instance

instance : IsProbabilityMeasure haarProbability :=
  ⟨Measure.haarMeasure_self⟩

instance : IsMulRightInvariant haarProbability where
  map_mul_right_eq_self g := by
    symm
    apply (Measure.haarMeasure_eq_iff haarNormalization
      (haarProbability.map (fun x => x * g))).2
    change (haarProbability.map (fun x => x * g)) Set.univ = 1
    simp


end SU2

instance (L : ℕ) : TopologicalSpace (GaugeConfig L) :=
  inferInstanceAs (TopologicalSpace (Link L → SU2))
instance (L : ℕ) : MeasurableSpace (GaugeConfig L) :=
  inferInstanceAs (MeasurableSpace (Link L → SU2))
instance (L : ℕ) [NeZero L] : BorelSpace (GaugeConfig L) :=
  inferInstanceAs (BorelSpace (Link L → SU2))
instance (L : ℕ) [NeZero L] : StandardBorelSpace (GaugeConfig L) :=
  inferInstanceAs (StandardBorelSpace (Link L → SU2))

/-- Independent normalized Haar variables on every link of the finite periodic lattice. -/
noncomputable def gaugeHaarMeasure (L : ℕ) [NeZero L] : Measure (GaugeConfig L) :=
  Measure.pi (fun _ : Link L => SU2.haarProbability)

instance (L : ℕ) [NeZero L] : IsProbabilityMeasure (gaugeHaarMeasure L) := by
  change IsProbabilityMeasure (Measure.pi (fun _ : Link L => SU2.haarProbability))
  exact Measure.pi.instIsProbabilityMeasure _

@[continuity, fun_prop]
theorem continuous_gaugeTransform {L : ℕ} (g : GaugeTransformation L) :
    Continuous (gaugeTransform g) := by
  apply continuous_pi
  intro e
  exact (continuous_const.mul (continuous_apply e)).mul continuous_const

/-- Left and right Haar invariance on each link imply local gauge invariance of product Haar. -/
theorem measurePreserving_gaugeTransform {L : ℕ} [NeZero L] (g : GaugeTransformation L) :
    MeasurePreserving (gaugeTransform g) (gaugeHaarMeasure L) (gaugeHaarMeasure L) := by
  change MeasurePreserving
    (fun (U : Link L → SU2) (e : Link L) => g e.x * U e * (g (shift e.x e.μ))⁻¹)
    (Measure.pi (fun _ : Link L => SU2.haarProbability))
    (Measure.pi (fun _ : Link L => SU2.haarProbability))
  refine measurePreserving_pi (fun _ : Link L => SU2.haarProbability)
    (fun _ : Link L => SU2.haarProbability)
    (f := fun e x => g e.x * x * (g (shift e.x e.μ))⁻¹) ?_
  intro e
  exact (measurePreserving_mul_right SU2.haarProbability (g (shift e.x e.μ))⁻¹).comp
    (measurePreserving_mul_left SU2.haarProbability (g e.x))

@[continuity, fun_prop]
theorem continuous_plaquetteHolonomy {L : ℕ} (p : Plaquette L) :
    Continuous (fun U : GaugeConfig L => plaquetteHolonomy U p) := by
  unfold plaquetteHolonomy
  fun_prop

@[continuity, fun_prop]
theorem continuous_plaquetteAction {L : ℕ} (p : Plaquette L) :
    Continuous (fun U : GaugeConfig L => plaquetteAction U p) := by
  unfold plaquetteAction SU2.trace Matrix.trace
  fun_prop

@[continuity, fun_prop]
theorem continuous_wilsonAction {L : ℕ} [NeZero L] (β : ℝ) :
    Continuous (wilsonAction (L := L) β) := by
  unfold wilsonAction
  fun_prop

@[fun_prop]
theorem measurable_wilsonAction {L : ℕ} [NeZero L] (β : ℝ) :
    Measurable (wilsonAction (L := L) β) :=
  (continuous_wilsonAction β).measurable

/-! ## Concrete Compact Matrix & Topological Gauge Groups `G` Beyond `SU(2)` -/

/-- For every matrix rank `N : ℕ`, the concrete special unitary group
`Matrix.specialUnitaryGroup (Fin N) ℂ` is a compact subset of `Matrix (Fin N) (Fin N) ℂ`. -/
theorem isCompact_specialUnitary_fin (N : ℕ) :
    IsCompact (Matrix.specialUnitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
  have hd : IsClosed {A : Matrix (Fin N) (Fin N) ℂ | A.det = 1} :=
    isClosed_eq continuous_id.matrix_det continuous_const
  have hc : IsClosed (Matrix.specialUnitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
    change IsClosed ((_root_.unitary (Matrix (Fin N) (Fin N) ℂ) : Set (Matrix (Fin N) (Fin N) ℂ)) ∩
      {A : Matrix (Fin N) (Fin N) ℂ | A.det = 1})
    exact isClosed_unitary.inter hd
  apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset hc
  intro A hA i j
  rw [Metric.mem_closedBall, dist_zero_right]
  exact entry_norm_bound_of_unitary hA.1 i j

/-- Whole-group compact normalization set `Set.univ` for any compact topological group `G`. -/
def compactGroupHaarNormalization (G : Type*) [Group G] [TopologicalSpace G] [CompactSpace G] :
    PositiveCompacts G :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- Normalized Haar probability measure on any compact Hausdorff topological group `G`. -/
noncomputable def compactGroupHaarProbability (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    Measure G :=
  Measure.haarMeasure (compactGroupHaarNormalization G)

instance (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    Measure.IsHaarMeasure (compactGroupHaarProbability G) := by
  unfold compactGroupHaarProbability
  infer_instance

instance (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    IsProbabilityMeasure (compactGroupHaarProbability G) :=
  ⟨Measure.haarMeasure_self⟩

instance (G : Type*) [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    IsMulRightInvariant (compactGroupHaarProbability G) where
  map_mul_right_eq_self g := by
    symm
    apply (Measure.haarMeasure_eq_iff (compactGroupHaarNormalization G)
      ((compactGroupHaarProbability G).map (fun x => x * g))).2
    change ((compactGroupHaarProbability G).map (fun x => x * g)) Set.univ = 1
    simp

/-- Finite-lattice gauge configuration `Link L → G` valued in an arbitrary gauge group `G`. -/
abbrev GroupGaugeConfig (G : Type*) (L : ℕ) : Type _ := Link L → G

/-- Finite-lattice local gauge transformation `Lattice4D L → G` valued in `G`. -/
abbrev GroupGaugeTransformation (G : Type*) (L : ℕ) : Type _ := Lattice4D L → G

/-- Local gauge transformation `U_e ↦ g(x) U_e g(x + e_μ)⁻¹` for a general gauge group `G`. -/
def groupGaugeTransform {G : Type*} [Group G] {L : ℕ}
    (g : GroupGaugeTransformation G L) (U : GroupGaugeConfig G L) : GroupGaugeConfig G L :=
  fun e => g e.x * U e * (g (shift e.x e.μ))⁻¹

/-- Product Haar probability measure on `GroupGaugeConfig G L` for any compact topological group `G`. -/
noncomputable def groupGaugeHaarMeasure (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] : Measure (GroupGaugeConfig G L) :=
  Measure.pi (fun _ : Link L => compactGroupHaarProbability G)

instance (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] : IsProbabilityMeasure (groupGaugeHaarMeasure G L) := by
  change IsProbabilityMeasure (Measure.pi (fun _ : Link L => compactGroupHaarProbability G))
  exact Measure.pi.instIsProbabilityMeasure _

/-- Oriented boundary holonomy `U(x,μ) U(x+μ,ν) U(x+ν,μ)⁻¹ U(x,ν)⁻¹ ∈ G` around plaquette `p`
for an arbitrary gauge group `G`. -/
def groupPlaquetteHolonomy {G : Type*} [Group G] {L : ℕ}
    (U : GroupGaugeConfig G L) (p : Plaquette L) : G :=
  U ⟨p.x, p.μ⟩ * U ⟨shift p.x p.μ, p.ν⟩ * (U ⟨shift p.x p.ν, p.μ⟩)⁻¹ * (U ⟨p.x, p.ν⟩)⁻¹

/-- Normalized real class-function trace structure on a topological gauge group `G`
(for example `g ↦ (1 / N) Re Tr(g)` on `SU(N)`): continuous, normalized to `1` at the identity,
inversion-symmetric, conjugation-invariant (`normReTrace (h * g * h⁻¹) = normReTrace g`), and
bounded in `[-1, 1]`. -/
structure CompactGaugeClassTrace (G : Type*) [Group G] [TopologicalSpace G] where
  normReTrace : G → ℝ
  h_continuous : Continuous normReTrace
  h_one : normReTrace 1 = 1
  h_inv : ∀ g : G, normReTrace g⁻¹ = normReTrace g
  h_conj : ∀ h g : G, normReTrace (h * g * h⁻¹) = normReTrace g
  h_abs_le_one : ∀ g : G, |normReTrace g| ≤ 1

/-- Single-plaquette Wilson action `1 - tr.normReTrace (groupPlaquetteHolonomy U p)` for a general
gauge group `G` equipped with `tr : CompactGaugeClassTrace G`. -/
def groupPlaquetteAction {G : Type*} [Group G] [TopologicalSpace G] {L : ℕ}
    (tr : CompactGaugeClassTrace G) (U : GroupGaugeConfig G L) (p : Plaquette L) : ℝ :=
  1 - tr.normReTrace (groupPlaquetteHolonomy U p)

/-- Total finite-volume Wilson action `β * ∑_p groupPlaquetteAction tr U p` for a general gauge
group `G`. -/
noncomputable def groupWilsonAction {G : Type*} [Group G] [TopologicalSpace G] {L : ℕ} [NeZero L]
    (tr : CompactGaugeClassTrace G) (β : ℝ) (U : GroupGaugeConfig G L) : ℝ :=
  β * ∑ p : Plaquette L, groupPlaquetteAction tr U p

/-- Canonical instantiation of `CompactGaugeClassTrace` on `SU2` via `(1 / 2) * (SU2.trace g).re`. -/
def su2CompactGaugeClassTrace : CompactGaugeClassTrace SU2 where
  normReTrace g := (1 / 2 : ℝ) * (SU2.trace g).re
  h_continuous := by
    unfold SU2.trace Matrix.trace
    fun_prop
  h_one := by
    change (1 / 2 : ℝ) * (Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ)).re = 1
    rw [Matrix.trace_one, Fintype.card_fin]
    norm_num
  h_inv g := by
    change (1 / 2 : ℝ) * (Matrix.trace g.matᴴ).re = (1 / 2 : ℝ) * (Matrix.trace g.mat).re
    rw [Matrix.trace_conjTranspose]
    simp
  h_conj h g := by
    rw [SU2.trace_conj]
  h_abs_le_one g := by
    have hu : g.mat ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
      (Matrix.mem_unitaryGroup_iff').2 g.unitary
    have h00 : |(g.mat 0 0).re| ≤ 1 :=
      (Complex.abs_re_le_norm (g.mat 0 0)).trans (entry_norm_bound_of_unitary hu 0 0)
    have h11 : |(g.mat 1 1).re| ≤ 1 :=
      (Complex.abs_re_le_norm (g.mat 1 1)).trans (entry_norm_bound_of_unitary hu 1 1)
    have htr : (SU2.trace g).re = (g.mat 0 0).re + (g.mat 1 1).re := by
      dsimp [SU2.trace, Matrix.trace]
      rw [Fin.sum_univ_two]
      simp only [Complex.add_re]
    rw [htr, abs_le]
    rcases abs_le.mp h00 with ⟨h00_lo, h00_hi⟩
    rcases abs_le.mp h11 with ⟨h11_lo, h11_hi⟩
    constructor <;> linarith

/-- For every compact Hausdorff topological gauge group `G` and every class trace
`tr : CompactGaugeClassTrace G`:
1. `groupGaugeTransform g` preserves the product Haar probability measure `groupGaugeHaarMeasure G L`,
2. Every plaquette action satisfies `0 ≤ groupPlaquetteAction tr U p ≤ 2` and vanishes at the
   vacuum configuration `fun _ => 1`,
3. `groupPlaquetteAction tr` and `groupWilsonAction tr β` are strictly invariant under arbitrary
   local gauge transformations `g : GroupGaugeTransformation G L` (`h_conj` + cyclic trace identity), and
4. On `G = SU2` with `su2CompactGaugeClassTrace`, `groupWilsonAction` and `compactGroupHaarProbability`
   coincide identically with `wilsonAction` and `SU2.haarProbability`. -/
theorem compactGroupGauge_haar_and_wilsonAction_invariance_and_bounds
    (G : Type*) [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] (tr : CompactGaugeClassTrace G) (β : ℝ) :
    (∀ g : GroupGaugeTransformation G L,
      MeasurePreserving (groupGaugeTransform g)
        (groupGaugeHaarMeasure G L) (groupGaugeHaarMeasure G L)) ∧
    (∀ (U : GroupGaugeConfig G L) (p : Plaquette L),
      0 ≤ groupPlaquetteAction tr U p ∧ groupPlaquetteAction tr U p ≤ 2 ∧
      groupPlaquetteAction tr (fun _ => 1) p = 0) ∧
    (∀ (g : GroupGaugeTransformation G L) (U : GroupGaugeConfig G L) (p : Plaquette L),
      groupPlaquetteAction tr (groupGaugeTransform g U) p = groupPlaquetteAction tr U p) ∧
    (∀ (g : GroupGaugeTransformation G L) (U : GroupGaugeConfig G L),
      groupWilsonAction tr β (groupGaugeTransform g U) = groupWilsonAction tr β U) ∧
    (compactGroupHaarProbability SU2 = SU2.haarProbability ∧
      ∀ U : GaugeConfig L,
        groupWilsonAction su2CompactGaugeClassTrace β U = wilsonAction β U) := by
  have hplaq : ∀ (g : GroupGaugeTransformation G L) (U : GroupGaugeConfig G L) (p : Plaquette L),
      groupPlaquetteAction tr (groupGaugeTransform g U) p = groupPlaquetteAction tr U p := by
    intro g U p
    have hhol : groupPlaquetteHolonomy (groupGaugeTransform g U) p =
        g p.x * groupPlaquetteHolonomy U p * (g p.x)⁻¹ := by
      dsimp [groupPlaquetteHolonomy, groupGaugeTransform]
      have hcomm := shift_comm p.x p.ν p.μ
      rw [hcomm]
      group
    dsimp [groupPlaquetteAction]
    rw [hhol, tr.h_conj]
  refine ⟨?_, ?_, hplaq, ?_, ⟨rfl, fun _ => rfl⟩⟩
  · intro g
    change MeasurePreserving
      (fun (U : Link L → G) (e : Link L) => g e.x * U e * (g (shift e.x e.μ))⁻¹)
      (Measure.pi (fun _ : Link L => compactGroupHaarProbability G))
      (Measure.pi (fun _ : Link L => compactGroupHaarProbability G))
    refine measurePreserving_pi (fun _ : Link L => compactGroupHaarProbability G)
      (fun _ : Link L => compactGroupHaarProbability G)
      (f := fun e x => g e.x * x * (g (shift e.x e.μ))⁻¹) ?_
    intro e
    exact (measurePreserving_mul_right (compactGroupHaarProbability G) (g (shift e.x e.μ))⁻¹).comp
      (measurePreserving_mul_left (compactGroupHaarProbability G) (g e.x))
  · intro U p
    have habs := abs_le.mp (tr.h_abs_le_one (groupPlaquetteHolonomy U p))
    have hvac : groupPlaquetteHolonomy (fun _ : Link L => (1 : G)) p = 1 := by
      dsimp [groupPlaquetteHolonomy]
      group
    refine ⟨?_, ?_, ?_⟩
    · dsimp [groupPlaquetteAction]
      linarith [habs.2]
    · dsimp [groupPlaquetteAction]
      linarith [habs.1]
    · dsimp [groupPlaquetteAction]
      rw [hvac, tr.h_one, sub_self]
  · intro g U
    dsimp [groupWilsonAction]
    simp_rw [hplaq g U]

/-- Pull back a `CompactGaugeClassTrace H` along any continuous group homomorphism `ρ : G →* H`
(for example any continuous unitary representation `G →* Matrix.unitaryGroup (Fin N) ℂ`). -/
def pullbackCompactGaugeClassTrace {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (tr : CompactGaugeClassTrace H) (ρ : G →* H) (hρ : Continuous ρ) :
    CompactGaugeClassTrace G where
  normReTrace g := tr.normReTrace (ρ g)
  h_continuous := tr.h_continuous.comp hρ
  h_one := by rw [map_one, tr.h_one]
  h_inv g := by rw [map_inv, tr.h_inv]
  h_conj h g := by rw [map_mul, map_mul, map_inv, tr.h_conj]
  h_abs_le_one g := tr.h_abs_le_one (ρ g)

/-- Canonical normalized trace `(1 / N) Re Tr(U)` on `U(N)` (`Matrix.unitaryGroup (Fin N) ℂ`)
for every `N ≥ 1`. -/
def unitaryCompactGaugeClassTrace (N : ℕ) [NeZero N] :
    CompactGaugeClassTrace (Matrix.unitaryGroup (Fin N) ℂ) where
  normReTrace U := (1 / (N : ℝ)) * (Matrix.trace (U : Matrix (Fin N) (Fin N) ℂ)).re
  h_continuous := by
    unfold Matrix.trace
    fun_prop
  h_one := by
    have _ : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    change (1 / (N : ℝ)) * (Matrix.trace (1 : Matrix (Fin N) (Fin N) ℂ)).re = 1
    rw [Matrix.trace_one, Fintype.card_fin]
    simp [Complex.natCast_re]
  h_inv U := by
    have hU : (U : Matrix (Fin N) (Fin N) ℂ) * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ = 1 :=
      (Matrix.mem_unitaryGroup_iff.mp U.2)
    have hinv : ((U⁻¹ : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
        (U : Matrix (Fin N) (Fin N) ℂ)ᴴ := by
      calc
        ((U⁻¹ : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
          = ((U⁻¹ : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * 1 :=
            (mul_one _).symm
        _ = ((U⁻¹ : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
              ((U : Matrix (Fin N) (Fin N) ℂ) * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ) := by
            rw [hU]
        _ = (((U⁻¹ * U : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) *
              (U : Matrix (Fin N) (Fin N) ℂ)ᴴ := by
            rw [← mul_assoc]; rfl
        _ = 1 * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ := by
            rw [inv_mul_cancel]; rfl
        _ = (U : Matrix (Fin N) (Fin N) ℂ)ᴴ := one_mul _
    change (1 / (N : ℝ)) *
        (Matrix.trace ((U⁻¹ : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)).re =
      (1 / (N : ℝ)) * (Matrix.trace (U : Matrix (Fin N) (Fin N) ℂ)).re
    rw [hinv, Matrix.trace_conjTranspose]
    simp
  h_conj H U := by
    change (1 / (N : ℝ)) *
        (Matrix.trace (((H * U * H⁻¹ : Matrix.unitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ))).re =
      (1 / (N : ℝ)) * (Matrix.trace (U : Matrix (Fin N) (Fin N) ℂ)).re
    have htr :
        Matrix.trace (((H * U * H⁻¹ : Matrix.unitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ)) =
        Matrix.trace (U : Matrix (Fin N) (Fin N) ℂ) := by
      calc
        Matrix.trace (((H * U * H⁻¹ : Matrix.unitaryGroup (Fin N) ℂ) :
            Matrix (Fin N) (Fin N) ℂ))
          = Matrix.trace (((H * U : Matrix.unitaryGroup (Fin N) ℂ) :
              Matrix (Fin N) (Fin N) ℂ) *
              ((H⁻¹ : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) := rfl
        _ = Matrix.trace (((H⁻¹ : Matrix.unitaryGroup (Fin N) ℂ) :
              Matrix (Fin N) (Fin N) ℂ) *
              ((H * U : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) :=
            Matrix.trace_mul_comm _ _
        _ = Matrix.trace ((((H⁻¹ * H : Matrix.unitaryGroup (Fin N) ℂ) :
              Matrix (Fin N) (Fin N) ℂ)) * (U : Matrix (Fin N) (Fin N) ℂ)) := by
            rw [show ((H⁻¹ : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
              ((H * U : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
              (((H⁻¹ * H : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) *
                (U : Matrix (Fin N) (Fin N) ℂ) from (mul_assoc _ _ _).symm]
        _ = Matrix.trace ((1 : Matrix (Fin N) (Fin N) ℂ) * (U : Matrix (Fin N) (Fin N) ℂ)) := by
            rw [inv_mul_cancel]; rfl
        _ = Matrix.trace (U : Matrix (Fin N) (Fin N) ℂ) := by rw [one_mul]
    rw [htr]
  h_abs_le_one U := by
    have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
    have h_diag : ∀ i : Fin N, |((U : Matrix (Fin N) (Fin N) ℂ) i i).re| ≤ 1 :=
      fun i => (Complex.abs_re_le_norm _).trans (entry_norm_bound_of_unitary U.2 i i)
    have h_sum : |(Matrix.trace (U : Matrix (Fin N) (Fin N) ℂ)).re| ≤ (N : ℝ) := by
      calc
        |(Matrix.trace (U : Matrix (Fin N) (Fin N) ℂ)).re|
          = |(∑ i : Fin N, (U : Matrix (Fin N) (Fin N) ℂ) i i).re| := rfl
        _ = |∑ i : Fin N, ((U : Matrix (Fin N) (Fin N) ℂ) i i).re| := by
            rw [Complex.re_sum]
        _ ≤ ∑ i : Fin N, |((U : Matrix (Fin N) (Fin N) ℂ) i i).re| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, (1 : ℝ) :=
            Finset.sum_le_sum (fun i _ => h_diag i)
        _ = (N : ℝ) := by simp
    calc
      |(1 / (N : ℝ)) * (Matrix.trace (U : Matrix (Fin N) (Fin N) ℂ)).re|
        = (1 / (N : ℝ)) * |(Matrix.trace (U : Matrix (Fin N) (Fin N) ℂ)).re| := by
          rw [abs_mul, abs_of_pos (one_div_pos.mpr hN_pos)]
      _ ≤ (1 / (N : ℝ)) * (N : ℝ) :=
          mul_le_mul_of_nonneg_left h_sum (le_of_lt (one_div_pos.mpr hN_pos))
      _ = 1 := one_div_mul_cancel (ne_of_gt hN_pos)

/-- Continuous group inclusion homomorphism `SU(N) →* U(N)` for every `N : ℕ`. -/
def specialUnitaryToUnitaryHom (N : ℕ) :
    Matrix.specialUnitaryGroup (Fin N) ℂ →* Matrix.unitaryGroup (Fin N) ℂ where
  toFun U := ⟨U.1, U.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Canonical normalized fundamental trace `(1 / N) Re Tr(U)` on `SU(N)`
(`Matrix.specialUnitaryGroup (Fin N) ℂ`) for every `N ≥ 1`. -/
def specialUnitaryCompactGaugeClassTrace (N : ℕ) [NeZero N] :
    CompactGaugeClassTrace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  pullbackCompactGaugeClassTrace (unitaryCompactGaugeClassTrace N)
    (specialUnitaryToUnitaryHom N)
    (Continuous.subtype_mk continuous_subtype_val _)

/-- General compact-group Wilson Boltzmann weight `exp(-groupWilsonAction tr β U)`. -/
noncomputable def groupBoltzmannWeight {G : Type*} [Group G] [TopologicalSpace G]
    {L : ℕ} [NeZero L] (tr : CompactGaugeClassTrace G) (β : ℝ)
    (U : GroupGaugeConfig G L) : ℝ :=
  Real.exp (-groupWilsonAction tr β U)

/-- General compact-group finite-volume Wilson partition function
`Z_{G, L}(β) = ∫ exp(-S_G(U)) dμ_{Haar, G, L}(U)`. -/
noncomputable def groupWilsonPartitionFunction (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] (tr : CompactGaugeClassTrace G) (β : ℝ) : ℝ :=
  ∫ U, groupBoltzmannWeight tr β U ∂(groupGaugeHaarMeasure G L)

/-- General compact-group finite-volume normalized Wilson expectation on `GroupGaugeConfig G L`. -/
noncomputable def groupWilsonExpectation (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] (tr : CompactGaugeClassTrace G) (β : ℝ)
    (F : GroupGaugeConfig G L → ℝ) : ℝ :=
  (∫ U, groupBoltzmannWeight tr β U * F U ∂(groupGaugeHaarMeasure G L)) /
    groupWilsonPartitionFunction G L tr β

/-- General compact-group finite-volume normalized Wilson probability measure on
`GroupGaugeConfig G L`. -/
noncomputable def groupWilsonMeasure (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] (tr : CompactGaugeClassTrace G) (β : ℝ) :
    Measure (GroupGaugeConfig G L) :=
  (groupGaugeHaarMeasure G L).withDensity (fun U =>
    ENNReal.ofReal (groupBoltzmannWeight tr β U / groupWilsonPartitionFunction G L tr β))

@[fun_prop] theorem continuous_groupPlaquetteHolonomy {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {L : ℕ} (p : Plaquette L) :
    Continuous (fun U : GroupGaugeConfig G L => groupPlaquetteHolonomy U p) := by
  unfold groupPlaquetteHolonomy
  fun_prop

@[fun_prop] theorem continuous_groupPlaquetteAction {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {L : ℕ}
    (tr : CompactGaugeClassTrace G) (p : Plaquette L) :
    Continuous (fun U : GroupGaugeConfig G L => groupPlaquetteAction tr U p) := by
  unfold groupPlaquetteAction
  exact continuous_const.sub (tr.h_continuous.comp (continuous_groupPlaquetteHolonomy p))

@[fun_prop] theorem continuous_groupWilsonAction {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {L : ℕ} [NeZero L]
    (tr : CompactGaugeClassTrace G) (β : ℝ) :
    Continuous (groupWilsonAction (L := L) tr β) := by
  unfold groupWilsonAction
  exact continuous_const.mul (continuous_finsetSum _ (fun p _ => continuous_groupPlaquetteAction tr p))

@[fun_prop] theorem continuous_groupBoltzmannWeight {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {L : ℕ} [NeZero L]
    (tr : CompactGaugeClassTrace G) (β : ℝ) :
    Continuous (groupBoltzmannWeight (L := L) tr β) := by
  unfold groupBoltzmannWeight
  exact Real.continuous_exp.comp (continuous_groupWilsonAction tr β).neg

/-- For every compact Hausdorff second-countable topological gauge group `G`, every class trace
`tr : CompactGaugeClassTrace G`, every lattice size `L ≥ 1`, and every nonnegative coupling `β ≥ 0`:
1. The total torus Wilson action satisfies `0 ≤ groupWilsonAction tr β U ≤ 12 * β * (L : ℝ) ^ 4`,
2. The Boltzmann weight satisfies `Real.exp (-(12 * β * (L : ℝ) ^ 4)) ≤ groupBoltzmannWeight tr β U ≤ 1`,
3. The finite-volume partition function satisfies
   `Real.exp (-(12 * β * (L : ℝ) ^ 4)) ≤ groupWilsonPartitionFunction G L tr β ≤ 1` and
   `0 < groupWilsonPartitionFunction G L tr β`,
4. `groupWilsonMeasure G L tr β` is a normalized probability measure (`IsProbabilityMeasure`), and
5. `groupWilsonMeasure G L tr β` and `groupWilsonExpectation G L tr β` are invariant under all
   local gauge transformations `g : GroupGaugeTransformation G L`. -/
theorem groupWilsonMeasure_prob_bounds_and_localGauge_invariance
    (G : Type*) [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] (tr : CompactGaugeClassTrace G) {β : ℝ} (hβ : 0 ≤ β) :
    (∀ U : GroupGaugeConfig G L,
      0 ≤ groupWilsonAction tr β U ∧
      groupWilsonAction tr β U ≤ 12 * β * (L : ℝ) ^ 4 ∧
      Real.exp (-(12 * β * (L : ℝ) ^ 4)) ≤ groupBoltzmannWeight tr β U ∧
      groupBoltzmannWeight tr β U ≤ 1) ∧
    (Real.exp (-(12 * β * (L : ℝ) ^ 4)) ≤ groupWilsonPartitionFunction G L tr β ∧
      groupWilsonPartitionFunction G L tr β ≤ 1 ∧
      0 < groupWilsonPartitionFunction G L tr β) ∧
    IsProbabilityMeasure (groupWilsonMeasure G L tr β) ∧
    (∀ g : GroupGaugeTransformation G L,
      MeasurePreserving (groupGaugeTransform g)
        (groupWilsonMeasure G L tr β) (groupWilsonMeasure G L tr β)) ∧
    (∀ (g : GroupGaugeTransformation G L) {F : GroupGaugeConfig G L → ℝ},
      Measurable F →
      groupWilsonExpectation G L tr β (fun U => F (groupGaugeTransform g U)) =
        groupWilsonExpectation G L tr β F) := by
  have hbase := compactGroupGauge_haar_and_wilsonAction_invariance_and_bounds G L tr β
  have hcard : (Fintype.card (Plaquette L) : ℝ) = 6 * (L : ℝ) ^ 4 := by
    exact_mod_cast card_plaquette_eq_six_mul_pow_four L
  have hact_bounds : ∀ U : GroupGaugeConfig G L,
      0 ≤ groupWilsonAction tr β U ∧
      groupWilsonAction tr β U ≤ 12 * β * (L : ℝ) ^ 4 ∧
      Real.exp (-(12 * β * (L : ℝ) ^ 4)) ≤ groupBoltzmannWeight tr β U ∧
      groupBoltzmannWeight tr β U ≤ 1 := by
    intro U
    have h0 : 0 ≤ groupWilsonAction tr β U := by
      dsimp [groupWilsonAction]
      exact mul_nonneg hβ (Finset.sum_nonneg (fun p _ => (hbase.2.1 U p).1))
    have hsum : (∑ p : Plaquette L, groupPlaquetteAction tr U p) ≤
        (Fintype.card (Plaquette L) : ℝ) * 2 := by
      have h1 := Finset.sum_le_card_nsmul (Finset.univ : Finset (Plaquette L))
        (fun p => groupPlaquetteAction tr U p) 2 (fun p _ => (hbase.2.1 U p).2.1)
      simpa [Finset.card_univ] using h1
    have hup : groupWilsonAction tr β U ≤ 12 * β * (L : ℝ) ^ 4 := by
      dsimp [groupWilsonAction]
      rw [hcard] at hsum
      nlinarith
    refine ⟨h0, hup, ?_, ?_⟩
    · dsimp [groupBoltzmannWeight]
      exact Real.exp_le_exp.mpr (by linarith)
    · dsimp [groupBoltzmannWeight]
      simpa using Real.exp_le_exp.mpr (by linarith : -groupWilsonAction tr β U ≤ 0)
  have hw_meas : Measurable (groupBoltzmannWeight (L := L) tr β) :=
    (continuous_groupBoltzmannWeight tr β).measurable
  have hw_int : Integrable (groupBoltzmannWeight (L := L) tr β) (groupGaugeHaarMeasure G L) := by
    apply (integrable_const (1 : ℝ)).mono' hw_meas.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun U => by
      rw [Real.norm_eq_abs, abs_of_pos (by dsimp [groupBoltzmannWeight]; exact Real.exp_pos _)]
      exact (hact_bounds U).2.2.2)
  have hZ_lo : Real.exp (-(12 * β * (L : ℝ) ^ 4)) ≤ groupWilsonPartitionFunction G L tr β := by
    simpa [groupWilsonPartitionFunction] using
      integral_mono (integrable_const _) hw_int (fun U => (hact_bounds U).2.2.1)
  have hZ_hi : groupWilsonPartitionFunction G L tr β ≤ 1 := by
    simpa [groupWilsonPartitionFunction] using
      integral_mono hw_int (integrable_const (1 : ℝ)) (fun U => (hact_bounds U).2.2.2)
  have hZ_pos : 0 < groupWilsonPartitionFunction G L tr β :=
    lt_of_lt_of_le (Real.exp_pos _) hZ_lo
  have hprob : IsProbabilityMeasure (groupWilsonMeasure G L tr β) := by
    have hi := hw_int.div_const (groupWilsonPartitionFunction G L tr β)
    have hp : ∀ᵐ U ∂(groupGaugeHaarMeasure G L),
        0 ≤ groupBoltzmannWeight tr β U / groupWilsonPartitionFunction G L tr β :=
      Filter.Eventually.of_forall (fun U => div_nonneg (le_of_lt (Real.exp_pos _)) hZ_pos.le)
    constructor
    rw [groupWilsonMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hi hp, integral_div]
    change ENNReal.ofReal
      (groupWilsonPartitionFunction G L tr β / groupWilsonPartitionFunction G L tr β) = 1
    simp [ne_of_gt hZ_pos]
  refine ⟨hact_bounds, ⟨hZ_lo, hZ_hi, hZ_pos⟩, hprob, ?_, ?_⟩
  · intro g
    have hpres := hbase.1 g
    let w : GroupGaugeConfig G L → ℝ≥0∞ := fun U =>
      ENNReal.ofReal (groupBoltzmannWeight tr β U / groupWilsonPartitionFunction G L tr β)
    have hw_enn_meas : Measurable w :=
      (hw_meas.div_const (groupWilsonPartitionFunction G L tr β)).ennreal_ofReal
    have hw_inv : ∀ U : GroupGaugeConfig G L, w (groupGaugeTransform g U) = w U := by
      intro U
      dsimp [w, groupBoltzmannWeight]
      rw [hbase.2.2.2.1 g U]
    refine ⟨hpres.measurable, Measure.ext (fun s hs => ?_)⟩
    rw [Measure.map_apply hpres.measurable hs, groupWilsonMeasure,
      withDensity_apply _ (hpres.measurable hs), withDensity_apply _ hs,
      ← lintegral_indicator (hpres.measurable hs), ← lintegral_indicator hs]
    have hlin := lintegral_map (μ := groupGaugeHaarMeasure G L)
      (f := Set.indicator s w) (g := groupGaugeTransform g)
      (hw_enn_meas.indicator hs) hpres.measurable
    rw [hpres.map_eq] at hlin
    change ∫⁻ a, (groupGaugeTransform g ⁻¹' s).indicator w a ∂groupGaugeHaarMeasure G L =
      ∫⁻ a, s.indicator w a ∂groupGaugeHaarMeasure G L
    rw [hlin]
    congr 1
    funext U
    by_cases hU : groupGaugeTransform g U ∈ s
    · simp [Set.indicator_of_mem, hU, hw_inv U]
    · simp [Set.indicator_of_notMem, hU]
  · intro g F hF
    have hpres := hbase.1 g
    have h := integral_map_of_stronglyMeasurable (μ := groupGaugeHaarMeasure G L)
      hpres.measurable (hw_meas.mul hF).stronglyMeasurable
    rw [hpres.map_eq] at h
    have hboltz : ∀ U : GroupGaugeConfig G L,
        groupBoltzmannWeight tr β (groupGaugeTransform g U) = groupBoltzmannWeight tr β U := by
      intro U
      dsimp [groupBoltzmannWeight]
      rw [hbase.2.2.2.1 g U]
    simp only [Pi.mul_apply, hboltz] at h
    exact congrArg (fun x => x / groupWilsonPartitionFunction G L tr β) h.symm

#assert_zfc_axioms

end JesseMath.Physics
