import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.YangMillsWilsonMeasureBridge
import JesseMath.Physics.YangMillsHaar
import JesseMath.Physics.YangMillsBlockGeometry
import JesseMath.Physics.HaarPairDisintegration
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace JesseMath.Physics

open YangMillsBlockGeometry HaarPairDisintegration

theorem finitePairBlock_eq_dyadicLinkBlockMap (L : ℕ) [NeZero L] :
    finitePairBlock (G := SU2) (dyadicFineLinkEquiv L) = dyadicLinkBlockMap L := by
  funext U e
  simp [finitePairBlock_apply, dyadicLinkBlockMap]

@[fun_prop] theorem measurable_dyadicLinkBlockMap (L : ℕ) [NeZero L] :
    Measurable (dyadicLinkBlockMap L) := by
  rw [← finitePairBlock_eq_dyadicLinkBlockMap L]
  exact measurable_finitePairBlock _

/-- Sample each first link and every unused link from Haar; the second link is
`h⁻¹ * V e`. This is a measurable probability kernel on every coarse configuration. -/
def haarBlockKernel (L : ℕ) [NeZero L] : Kernel (GaugeConfig L) (GaugeConfig (2 * L)) :=
  finitePairKernel SU2.haarProbability (dyadicFineLinkEquiv L)

instance (L : ℕ) [NeZero L] : IsMarkovKernel (haarBlockKernel L) := by
  change IsMarkovKernel (finitePairKernel (I := Link L) (J := unusedFineLinks L)
    (F := Link (2 * L)) (G := SU2) SU2.haarProbability (dyadicFineLinkEquiv L))
  infer_instance

theorem haarBlockKernel_supported (L : ℕ) [NeZero L] (V : GaugeConfig L) :
    ∀ᵐ U ∂haarBlockKernel L V, dyadicLinkBlockMap L U = V := by
  rw [← finitePairBlock_eq_dyadicLinkBlockMap L]
  exact finitePairKernel_supported SU2.haarProbability _ V

theorem dyadicLinkBlockMap_haar (L : ℕ) [NeZero L] :
    (gaugeHaarMeasure (2 * L)).map (dyadicLinkBlockMap L) = gaugeHaarMeasure L := by
  rw [← finitePairBlock_eq_dyadicLinkBlockMap L]
  exact finitePairBlock_map SU2.haarProbability _

/-- The actual joint law of coarse and fine links, established from Haar invariance. -/
theorem haarBlockKernel_graph (L : ℕ) [NeZero L] :
    gaugeHaarMeasure L ⊗ₘ haarBlockKernel L =
      (gaugeHaarMeasure (2 * L)).map (fun U => (dyadicLinkBlockMap L U, U)) := by
  rw [← finitePairBlock_eq_dyadicLinkBlockMap L]
  exact finitePairKernel_graph SU2.haarProbability _

/-- Concrete data for the existing Wilson effective-action interface. Its
disintegration contract is proved separately by `haarBlockKernel_graph`. -/
def haarBlockDisintegration (L : ℕ) [NeZero L] : ConditionalBlockFiberDisintegration L where
  μ_fine := gaugeHaarMeasure (2 * L)
  μ_coarse := gaugeHaarMeasure L
  fiberKernel := haarBlockKernel L
  fine_prob := inferInstance
  coarse_prob := inferInstance
  fiber_prob := fun _ => inferInstance

/-- The constructed Haar family inhabits the supported joint-law interface. -/
def haarSupportedBlockDisintegration (L : ℕ) [NeZero L] : SupportedBlockFiberDisintegration L where
  toConditionalBlockFiberDisintegration := haarBlockDisintegration L
  fiber_measurable := (haarBlockKernel L).measurable
  block_measurable := measurable_dyadicLinkBlockMap L
  h_graph := haarBlockKernel_graph L
  h_support := haarBlockKernel_supported L

/-- Exact finite-volume Wilson blocking: the coarse law has density equal to
the explicit Haar-fiber partition function divided by the fine partition function.
No measurability or disintegration hypothesis is supplied by the caller. -/
theorem haar_wilsonBlockedMeasure_density (L : ℕ) [NeZero L] {β : ℝ} (hβ : 0 ≤ β) :
    wilsonBlockedMeasure (gaugeHaarMeasure (2 * L)) β (dyadicLinkBlockMap L) =
      (gaugeHaarMeasure L).withDensity (fun V =>
        ENNReal.ofReal (wilsonBlockedFiberWeight (haarBlockDisintegration L) β V /
          wilsonPartition (gaugeHaarMeasure (2 * L)) β)) := by
  exact wilsonBlockedMeasure_density_of_graph_disintegration
    (gaugeHaarMeasure (2 * L)) (gaugeHaarMeasure L) (dyadicLinkBlockMap L)
    (measurable_dyadicLinkBlockMap L) (haarBlockKernel L) (haarBlockKernel_graph L)
    hβ (measurable_wilsonAction β)

theorem measurable_haarBlockedFiberWeight (L : ℕ) [NeZero L] (β : ℝ) :
    Measurable (wilsonBlockedFiberWeight (haarBlockDisintegration L) β) := by
  exact (wilsonWeight_measurable (measurable_wilsonAction β)).stronglyMeasurable.integral_kernel.measurable

/-- The real-integral disintegration hypothesis of the earlier Wilson bridge is
now a theorem for the constructed Haar fibers, for every measurable observable. -/
theorem haar_wilson_integral_disintegration (L : ℕ) [NeZero L]
    {β : ℝ} (hβ : 0 ≤ β) {F : GaugeConfig L → ℝ} (hF : Measurable F) :
    (∫ U, boltzmannWeight β U * F (dyadicLinkBlockMap L U) ∂gaugeHaarMeasure (2 * L)) =
      ∫ V, wilsonBlockedFiberWeight (haarBlockDisintegration L) β V * F V
        ∂gaugeHaarMeasure L := by
  have hZ := wilsonPartition_pos (gaugeHaarMeasure (2 * L)) hβ (measurable_wilsonAction β)
  have hw (V : GaugeConfig L) :
      0 ≤ wilsonBlockedFiberWeight (haarBlockDisintegration L) β V :=
    (wilsonBlockedFiberWeight_bounds_and_pos_all_configs (haarBlockDisintegration L)
      hβ (measurable_wilsonAction β) V).1.le
  have hd : Measurable (fun V => ENNReal.ofReal
      (wilsonBlockedFiberWeight (haarBlockDisintegration L) β V /
        wilsonPartition (gaugeHaarMeasure (2 * L)) β)) := ENNReal.measurable_ofReal.comp
    ((measurable_haarBlockedFiberWeight L β).div_const
      (wilsonPartition (gaugeHaarMeasure (2 * L)) β))
  have heq := congrArg (fun μ : Measure (GaugeConfig L) => ∫ V, F V ∂μ)
    (haar_wilsonBlockedMeasure_density L hβ)
  rw [integral_wilsonBlockedMeasure _ hβ (measurable_wilsonAction β)
    (measurable_dyadicLinkBlockMap L) hF,
    integral_withDensity_eq_integral_toReal_smul hd
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at heq
  simp only [ENNReal.toReal_ofReal (div_nonneg (hw _) hZ.le), smul_eq_mul,
    div_mul_eq_mul_div, integral_div, wilsonExpectation] at heq
  exact (div_left_inj' hZ.ne').mp heq

/-- At zero coupling the blocked Wilson law is precisely coarse product Haar. -/
theorem haar_wilsonBlockedMeasure_zero (L : ℕ) [NeZero L] :
    wilsonBlockedMeasure (gaugeHaarMeasure (2 * L)) 0 (dyadicLinkBlockMap L) =
      gaugeHaarMeasure L := by
  have hW : wilsonMeasure (gaugeHaarMeasure (2 * L)) 0 = gaugeHaarMeasure (2 * L) := by
    simp [wilsonMeasure, wilsonPartition, boltzmannWeight, wilsonAction]
  unfold wilsonBlockedMeasure
  rw [hW, dyadicLinkBlockMap_haar]


/-- A link can occur in at most two plaquettes for each of its three transverse directions. -/
def incidentPlaquette {L : ℕ} (e : Link L)
    (a : {ν : Fin 4 // ν ≠ e.μ} × Bool) : Plaquette L :=
  let x := if a.2 then e.x - unitVec L a.1.val else e.x
  if h : e.μ < a.1.val then ⟨x, e.μ, a.1.val, h⟩
  else ⟨x, a.1.val, e.μ, lt_of_le_of_ne (le_of_not_gt h) a.1.property⟩

noncomputable def incidentPlaquettes {L : ℕ} (e : Link L) : Finset (Plaquette L) :=
  Finset.univ.image (incidentPlaquette e)

theorem incidentPlaquettes_card_le_six {L : ℕ} (e : Link L) :
    (incidentPlaquettes e).card ≤ 6 := by
  classical
  have hcard : Fintype.card {ν : Fin 4 // ν ≠ e.μ} = 3 := by simp
  calc
    (incidentPlaquettes e).card ≤ Fintype.card ({ν : Fin 4 // ν ≠ e.μ} × Bool) :=
      Finset.card_image_le.trans_eq (Finset.card_univ)
    _ = 6 := by simp [Fintype.card_prod, hcard]

private theorem plaquette_mem_incident_of_boundary {L : ℕ} (p : Plaquette L) (e : Link L)
    (h : e = ⟨p.x, p.μ⟩ ∨ e = ⟨shift p.x p.μ, p.ν⟩ ∨
      e = ⟨shift p.x p.ν, p.μ⟩ ∨ e = ⟨p.x, p.ν⟩) :
    p ∈ incidentPlaquettes e := by
  classical
  have hμν : p.μ ≠ p.ν := ne_of_lt p.h
  have hνμ : p.ν ≠ p.μ := hμν.symm
  have hnot : ¬p.ν < p.μ := not_lt_of_ge p.h.le
  rcases h with rfl | rfl | rfl | rfl
  · apply Finset.mem_image.mpr
    refine ⟨(⟨p.ν, hνμ⟩, false), Finset.mem_univ _, ?_⟩
    simp [incidentPlaquette, p.h]
  · apply Finset.mem_image.mpr
    refine ⟨(⟨p.μ, hμν⟩, true), Finset.mem_univ _, ?_⟩
    simp [incidentPlaquette, hnot, shift]
  · apply Finset.mem_image.mpr
    refine ⟨(⟨p.ν, hνμ⟩, true), Finset.mem_univ _, ?_⟩
    simp [incidentPlaquette, p.h, shift]
  · apply Finset.mem_image.mpr
    refine ⟨(⟨p.μ, hμν⟩, false), Finset.mem_univ _, ?_⟩
    simp [incidentPlaquette, hnot]

/-- Changing one link leaves every nonincident plaquette unchanged. -/
theorem plaquetteAction_eq_of_agree_off_link {L : ℕ} (U W : GaugeConfig L) (e : Link L)
    (hUW : ∀ f, f ≠ e → U f = W f) (p : Plaquette L)
    (hp : p ∉ incidentPlaquettes e) : plaquetteAction U p = plaquetteAction W p := by
  have h1 : (⟨p.x, p.μ⟩ : Link L) ≠ e := fun h =>
    hp (plaquette_mem_incident_of_boundary p e (Or.inl h.symm))
  have h2 : (⟨shift p.x p.μ, p.ν⟩ : Link L) ≠ e := fun h =>
    hp (plaquette_mem_incident_of_boundary p e (Or.inr (Or.inl h.symm)))
  have h3 : (⟨shift p.x p.ν, p.μ⟩ : Link L) ≠ e := fun h =>
    hp (plaquette_mem_incident_of_boundary p e (Or.inr (Or.inr (Or.inl h.symm))))
  have h4 : (⟨p.x, p.ν⟩ : Link L) ≠ e := fun h =>
    hp (plaquette_mem_incident_of_boundary p e (Or.inr (Or.inr (Or.inr h.symm))))
  simp only [plaquetteAction, plaquetteHolonomy, hUW _ h1, hUW _ h2, hUW _ h3, hUW _ h4]

/-- The actual Wilson action changes by at most `12 * β` under one link change, uniformly in volume. -/
theorem wilsonAction_oscillation_of_agree_off_link {L : ℕ} [NeZero L]
    {β : ℝ} (hβ : 0 ≤ β) (U W : GaugeConfig L) (e : Link L)
    (hUW : ∀ f, f ≠ e → U f = W f) :
    |wilsonAction β U - wilsonAction β W| ≤ 12 * β := by
  classical
  have hsum : (∑ p : Plaquette L, (plaquetteAction U p - plaquetteAction W p)) =
      ∑ p ∈ incidentPlaquettes e, (plaquetteAction U p - plaquetteAction W p) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    rw [plaquetteAction_eq_of_agree_off_link U W e hUW p hp, sub_self]
  have hb (p : Plaquette L) : |plaquetteAction U p - plaquetteAction W p| ≤ 2 := by
    have hu0 := plaquetteAction_nonneg U p
    have hu2 := plaquetteAction_le_two U p
    have hw0 := plaquetteAction_nonneg W p
    have hw2 := plaquetteAction_le_two W p
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs : |∑ p ∈ incidentPlaquettes e, (plaquetteAction U p - plaquetteAction W p)| ≤ 12 := by
    calc
      _ ≤ ∑ p ∈ incidentPlaquettes e, |plaquetteAction U p - plaquetteAction W p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ incidentPlaquettes e, (2 : ℝ) := Finset.sum_le_sum (fun p _ => hb p)
      _ = (incidentPlaquettes e).card * (2 : ℝ) := by simp
      _ ≤ 12 := by exact_mod_cast Nat.mul_le_mul_right 2 (incidentPlaquettes_card_le_six e)
  unfold wilsonAction
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hβ, hsum]
  nlinarith

/-- The four oriented boundary links of a plaquette `p` on the 4D torus of side `L`. -/
noncomputable def plaquetteBoundaryLinks {L : ℕ} (p : Plaquette L) : Finset (Link L) := by
  classical
  exact {⟨p.x, p.μ⟩, ⟨shift p.x p.μ, p.ν⟩, ⟨shift p.x p.ν, p.μ⟩, ⟨p.x, p.ν⟩}

theorem plaquetteBoundaryLinks_card_le_four {L : ℕ} (p : Plaquette L) :
    (plaquetteBoundaryLinks p).card ≤ 4 := by
  classical
  unfold plaquetteBoundaryLinks
  exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
    ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ
      ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ (by simp))))))

theorem mem_plaquetteBoundaryLinks_of_mem_incidentPlaquettes {L : ℕ}
    (e : Link L) (p : Plaquette L) (hp : p ∈ incidentPlaquettes e) :
    e ∈ plaquetteBoundaryLinks p := by
  classical
  rcases e with ⟨x, μ⟩
  unfold incidentPlaquettes at hp
  rcases Finset.mem_image.mp hp with ⟨⟨⟨ν, hν⟩, b⟩, _, rfl⟩
  unfold plaquetteBoundaryLinks incidentPlaquette
  cases b <;> by_cases h : μ < ν <;> simp [h, shift, sub_add_cancel]

theorem plaquetteBoundaryLinks_erase_card_le_three {L : ℕ}
    (e : Link L) (p : Plaquette L) (hp : p ∈ incidentPlaquettes e) :
    ((plaquetteBoundaryLinks p).erase e).card ≤ 3 := by
  classical
  have he := mem_plaquetteBoundaryLinks_of_mem_incidentPlaquettes e p hp
  have hcard := plaquetteBoundaryLinks_card_le_four p
  have herase := Finset.card_erase_of_mem he
  omega

/-- The single-link Dobrushin neighborhood of `e`: all links `e' ≠ e` sharing at least one
incident plaquette with `e`. -/
noncomputable def dobrushinNeighbors {L : ℕ} (e : Link L) : Finset (Link L) := by
  classical
  exact (incidentPlaquettes e).biUnion (fun p => (plaquetteBoundaryLinks p).erase e)

theorem not_mem_dobrushinNeighbors_self {L : ℕ} (e : Link L) :
    e ∉ dobrushinNeighbors e := by
  classical
  simp [dobrushinNeighbors]

/-- Volume-uniform single-link Dobrushin neighborhood bound: on `GaugeConfig L` for every torus
side `L`, every link `e` shares plaquettes with at most `6 × 3 = 18` distinct neighbor links. -/
theorem dobrushinNeighbors_card_le_eighteen {L : ℕ} (e : Link L) :
    (dobrushinNeighbors e).card ≤ 18 := by
  classical
  unfold dobrushinNeighbors
  calc
    ((incidentPlaquettes e).biUnion (fun p => (plaquetteBoundaryLinks p).erase e)).card
      ≤ ∑ p ∈ incidentPlaquettes e, ((plaquetteBoundaryLinks p).erase e).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ incidentPlaquettes e, 3 :=
        Finset.sum_le_sum (fun p hp => plaquetteBoundaryLinks_erase_card_le_three e p hp)
    _ = (incidentPlaquettes e).card * 3 := by simp
    _ ≤ 6 * 3 := Nat.mul_le_mul_right 3 (incidentPlaquettes_card_le_six e)
    _ = 18 := by norm_num

theorem not_mem_incidentPlaquettes_of_not_mem_dobrushinNeighbors {L : ℕ}
    {e e' : Link L} (hne : e' ≠ e) (hn : e' ∉ dobrushinNeighbors e)
    {p : Plaquette L} (hp : p ∈ incidentPlaquettes e) :
    p ∉ incidentPlaquettes e' := by
  classical
  intro hp'
  apply hn
  unfold dobrushinNeighbors
  rw [Finset.mem_biUnion]
  exact ⟨p, hp, Finset.mem_erase.mpr
    ⟨hne, mem_plaquetteBoundaryLinks_of_mem_incidentPlaquettes e' p hp'⟩⟩

/-- Finite-range locality of the actual Wilson action `wilsonAction β` on `GaugeConfig L`:
for any two distinct links `e1` and `e2` with `e2 ∉ dobrushinNeighbors e1`, the two-link mixed
second difference of `wilsonAction β` vanishes identically across all lattice sizes `L`. -/
theorem twoLinkMixedDifference_wilsonAction_eq_zero_of_not_mem_dobrushinNeighbors
    {L : ℕ} [NeZero L] (β : ℝ) (V : GaugeConfig L) (e1 e2 : Link L)
    (hne : e2 ≠ e1) (hn : e2 ∉ dobrushinNeighbors e1) (g1 g2 h1 h2 : SU2) :
    twoLinkMixedDifference L (wilsonAction β) V e1.x e1.μ g1 g2 e2.x e2.μ h1 h2 = 0 := by
  classical
  have h_off_e1 (h : SU2) (f : Link L) (hf : f ≠ e1) :
      updateTwoGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h f =
        updateTwoGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h f := by
    dsimp [updateTwoGaugeLinks]
    by_cases hfe2 : f = e2
    · subst hfe2
      exact ((updateGaugeLink_same_and_other L (updateGaugeLink L V e1.x e1.μ g1) f.x f.μ h).1).trans
        ((updateGaugeLink_same_and_other L (updateGaugeLink L V e1.x e1.μ g2) f.x f.μ h).1).symm
    · have h1f := (updateGaugeLink_same_and_other L (updateGaugeLink L V e1.x e1.μ g1) e2.x e2.μ h).2 f hfe2
      have h2f := (updateGaugeLink_same_and_other L (updateGaugeLink L V e1.x e1.μ g2) e2.x e2.μ h).2 f hfe2
      have h1e := (updateGaugeLink_same_and_other L V e1.x e1.μ g1).2 f hf
      have h2e := (updateGaugeLink_same_and_other L V e1.x e1.μ g2).2 f hf
      exact (h1f.trans h1e).trans (h2f.trans h2e).symm
  have h_off_e2 (g : SU2) (f : Link L) (hf : f ≠ e2) :
      updateTwoGaugeLinks L V e1.x e1.μ g e2.x e2.μ h1 f =
        updateTwoGaugeLinks L V e1.x e1.μ g e2.x e2.μ h2 f := by
    dsimp [updateTwoGaugeLinks]
    exact ((updateGaugeLink_same_and_other L (updateGaugeLink L V e1.x e1.μ g) e2.x e2.μ h1).2 f hf).trans
      ((updateGaugeLink_same_and_other L (updateGaugeLink L V e1.x e1.μ g) e2.x e2.μ h2).2 f hf).symm
  have h_diff (h : SU2) :
      wilsonAction β (updateTwoGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h) -
        wilsonAction β (updateTwoGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h) =
      β * ∑ p ∈ incidentPlaquettes e1,
        (plaquetteAction (updateTwoGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h) p -
          plaquetteAction (updateTwoGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h) p) := by
    unfold wilsonAction
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    rw [plaquetteAction_eq_of_agree_off_link _ _ e1 (h_off_e1 h) p hp, sub_self]
  dsimp [twoLinkMixedDifference]
  rw [h_diff h1, h_diff h2]
  have h_sum_eq :
      (∑ p ∈ incidentPlaquettes e1,
        (plaquetteAction (updateTwoGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h1) p -
          plaquetteAction (updateTwoGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h1) p)) =
      ∑ p ∈ incidentPlaquettes e1,
        (plaquetteAction (updateTwoGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h2) p -
          plaquetteAction (updateTwoGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h2) p) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp2 := not_mem_incidentPlaquettes_of_not_mem_dobrushinNeighbors hne hn hp
    rw [plaquetteAction_eq_of_agree_off_link _ _ e2 (h_off_e2 g1) p hp2,
      plaquetteAction_eq_of_agree_off_link _ _ e2 (h_off_e2 g2) p hp2]
  rw [h_sum_eq, sub_self]

/-- Pointwise two-link mixed second-difference bound for the actual Wilson action `wilsonAction β`
on `GaugeConfig L`: changing two links `(e1.x, e1.μ)` and `(e2.x, e2.μ)` changes the mixed second
difference by at most `24 * β` uniformly in lattice volume `L`. -/
theorem twoLinkMixedDifference_wilsonAction_abs_le_twentyFour_mul_beta
    {L : ℕ} [NeZero L] {β : ℝ} (hβ : 0 ≤ β) (V : GaugeConfig L) (e1 e2 : Link L)
    (g1 g2 h1 h2 : SU2) :
    |twoLinkMixedDifference L (wilsonAction β) V e1.x e1.μ g1 g2 e2.x e2.μ h1 h2| ≤ 24 * β := by
  have h_off_e2 (g : SU2) (f : Link L) (hf : f ≠ e2) :
      updateTwoGaugeLinks L V e1.x e1.μ g e2.x e2.μ h1 f =
        updateTwoGaugeLinks L V e1.x e1.μ g e2.x e2.μ h2 f := by
    dsimp [updateTwoGaugeLinks]
    exact ((updateGaugeLink_same_and_other L (updateGaugeLink L V e1.x e1.μ g) e2.x e2.μ h1).2 f hf).trans
      ((updateGaugeLink_same_and_other L (updateGaugeLink L V e1.x e1.μ g) e2.x e2.μ h2).2 f hf).symm
  have h_osc1 := wilsonAction_oscillation_of_agree_off_link hβ
    (updateTwoGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h1)
    (updateTwoGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h2)
    e2 (h_off_e2 g1)
  have h_osc2 := wilsonAction_oscillation_of_agree_off_link hβ
    (updateTwoGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h1)
    (updateTwoGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h2)
    e2 (h_off_e2 g2)
  have h_re :
      twoLinkMixedDifference L (wilsonAction β) V e1.x e1.μ g1 g2 e2.x e2.μ h1 h2 =
      (wilsonAction β (updateTwoGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h1) -
        wilsonAction β (updateTwoGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h2)) -
      (wilsonAction β (updateTwoGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h1) -
        wilsonAction β (updateTwoGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h2)) := by
    dsimp [twoLinkMixedDifference]
    ring
  have h_tri := abs_sub
    (wilsonAction β (updateTwoGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h1) -
      wilsonAction β (updateTwoGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h2))
    (wilsonAction β (updateTwoGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h1) -
      wilsonAction β (updateTwoGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h2))
  rw [← h_re] at h_tri
  linarith

/-- Volume-uniform finite-range locality and sum bound for the two-link action mixed second
difference of `wilsonAction β` across all torus sizes `L`:
1. Summing `|twoLinkMixedDifference L (wilsonAction β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|`
   over all `4 L^4 - 1` partner links `e' ∈ Finset.univ.erase e` collapses identically to the
   finite neighborhood `dobrushinNeighbors e` (of support cardinality `≤ 18`, independent of `L`),
   with unnormalized sum bounded by `432 * β`.
2. The `(1 / 24)`-rescaled two-link mixed-difference sum
   `(1 / 24) * ∑ e' ∈ Finset.univ.erase e, |twoLinkMixedDifference L (wilsonAction β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|`
   is bounded by `18 * β` uniformly in `L`, and is strictly less than `1` for `0 ≤ β < 1 / 18`. -/
theorem wilson_twoLinkMixedDifference_locality_and_sum_bound
    {L : ℕ} [NeZero L] (e : Link L) {β : ℝ} (hβ : 0 ≤ β) :
    ∀ (V : GaugeConfig L) (g1 g2 : SU2) (h1 h2 : Link L → SU2),
      (∑ e' ∈ Finset.univ.erase e,
        |twoLinkMixedDifference L (wilsonAction β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) =
      (∑ e' ∈ dobrushinNeighbors e,
        |twoLinkMixedDifference L (wilsonAction β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) ∧
      (1 / 24 : ℝ) *
        (∑ e' ∈ Finset.univ.erase e,
          |twoLinkMixedDifference L (wilsonAction β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) ≤
        18 * β ∧
      (β < 1 / 18 →
        (1 / 24 : ℝ) *
          (∑ e' ∈ Finset.univ.erase e,
            |twoLinkMixedDifference L (wilsonAction β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) <
          1) := by
  intro V g1 g2 h1 h2
  have hcollapse :
      (∑ e' ∈ Finset.univ.erase e,
        |twoLinkMixedDifference L (wilsonAction β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) =
      (∑ e' ∈ dobrushinNeighbors e,
        |twoLinkMixedDifference L (wilsonAction β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) := by
    symm
    apply Finset.sum_subset
    · intro e' he'
      exact Finset.mem_erase.mpr ⟨fun h => not_mem_dobrushinNeighbors_self e (h ▸ he'), Finset.mem_univ e'⟩
    · intro e' he' hn
      rw [twoLinkMixedDifference_wilsonAction_eq_zero_of_not_mem_dobrushinNeighbors β V e e'
        (Finset.mem_erase.mp he').1 hn g1 g2 (h1 e') (h2 e'), abs_zero]
  have hcard : ((dobrushinNeighbors e).card : ℝ) ≤ 18 := by
    exact_mod_cast dobrushinNeighbors_card_le_eighteen e
  have hsum_le :
      (∑ e' ∈ Finset.univ.erase e,
        |twoLinkMixedDifference L (wilsonAction β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) ≤
      18 * (24 * β) := by
    rw [hcollapse]
    calc
      (∑ e' ∈ dobrushinNeighbors e,
        |twoLinkMixedDifference L (wilsonAction β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|)
        ≤ ∑ _e' ∈ dobrushinNeighbors e, (24 * β) :=
          Finset.sum_le_sum (fun e' _ =>
            twoLinkMixedDifference_wilsonAction_abs_le_twentyFour_mul_beta hβ V e e' g1 g2 (h1 e') (h2 e'))
      _ = ((dobrushinNeighbors e).card : ℝ) * (24 * β) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 18 * (24 * β) :=
          mul_le_mul_of_nonneg_right hcard (by linarith)
  have hrow :
      (1 / 24 : ℝ) *
        (∑ e' ∈ Finset.univ.erase e,
          |twoLinkMixedDifference L (wilsonAction β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) ≤
      18 * β := by
    linarith
  refine ⟨hcollapse, hrow, fun hlt => by linarith⟩

alias wilson_dobrushin_rowSum_uniform_in_L := wilson_twoLinkMixedDifference_locality_and_sum_bound



/-- The shared Haar sampling variables: one first link per pair and all unused fine links. -/
abbrev HaarFiberCoordinates (L : ℕ) :=
  GaugeConfig L × (unusedFineLinks L → SU2)

noncomputable def haarFiberReference (L : ℕ) [NeZero L] : Measure (HaarFiberCoordinates L) :=
  (gaugeHaarMeasure L).prod (Measure.pi (fun _ : unusedFineLinks L => SU2.haarProbability))

instance (L : ℕ) [NeZero L] : IsProbabilityMeasure (haarFiberReference L) := by
  unfold haarFiberReference
  infer_instance

/-- The same reconstruction used in the constructed Haar kernel, with shared sampling variables. -/
def haarFiberReconstruction (L : ℕ) [NeZero L] (V : GaugeConfig L)
    (r : HaarFiberCoordinates L) : GaugeConfig (2 * L) :=
  (splitConfigEquiv (dyadicFineLinkEquiv L)).symm (rebuild V r)

@[fun_prop] theorem measurable_haarFiberReconstruction (L : ℕ) [NeZero L] (V : GaugeConfig L) :
    Measurable (haarFiberReconstruction L V) :=
  (splitConfigEquiv (dyadicFineLinkEquiv L)).symm.measurable.comp (measurable_rebuild_left (G := Link L → SU2) V)

@[simp] theorem haarFiberReconstruction_first (L : ℕ) [NeZero L] (V : GaugeConfig L)
    (r : HaarFiberCoordinates L) (e : Link L) :
    haarFiberReconstruction L V r (dyadicFineLink L (e, 0)) = r.1 e := by
  have h := congrArg (fun p : ((Link L → SU2) × (Link L → SU2)) × (unusedFineLinks L → SU2) => p.1.1 e)
    ((splitConfigEquiv (dyadicFineLinkEquiv L)).apply_symm_apply (rebuild V r))
  simpa only [haarFiberReconstruction, splitConfigEquiv_first, dyadicFineLinkEquiv_inl, rebuild] using h

@[simp] theorem haarFiberReconstruction_second (L : ℕ) [NeZero L] (V : GaugeConfig L)
    (r : HaarFiberCoordinates L) (e : Link L) :
    haarFiberReconstruction L V r (dyadicFineLink L (e, 1)) = (r.1 e)⁻¹ * V e := by
  have h := congrArg (fun p : ((Link L → SU2) × (Link L → SU2)) × (unusedFineLinks L → SU2) => p.1.2 e)
    ((splitConfigEquiv (dyadicFineLinkEquiv L)).apply_symm_apply (rebuild V r))
  simp only [splitConfigEquiv_second, dyadicFineLinkEquiv_inl, rebuild] at h
  convert h using 1
  rfl

@[simp] theorem haarFiberReconstruction_unused (L : ℕ) [NeZero L] (V : GaugeConfig L)
    (r : HaarFiberCoordinates L) (e : unusedFineLinks L) :
    haarFiberReconstruction L V r e.val = r.2 e := by
  have h := congrArg (fun p : ((Link L → SU2) × (Link L → SU2)) × (unusedFineLinks L → SU2) => p.2 e)
    ((splitConfigEquiv (dyadicFineLinkEquiv L)).apply_symm_apply (rebuild V r))
  simpa only [haarFiberReconstruction, splitConfigEquiv_unused, dyadicFineLinkEquiv_inr, rebuild] using h

/-- With the Haar variables fixed, a coarse link update changes only its selected second fine link. -/
theorem haarFiberReconstruction_agree_off_second (L : ℕ) [NeZero L]
    (V : GaugeConfig L) (e : Link L) (g1 g2 : SU2) (r : HaarFiberCoordinates L)
    (f : Link (2 * L)) (hf : f ≠ dyadicFineLink L (e, 1)) :
    haarFiberReconstruction L (updateGaugeLink L V e.x e.μ g1) r f =
      haarFiberReconstruction L (updateGaugeLink L V e.x e.μ g2) r f := by
  obtain ⟨q, rfl⟩ := (dyadicFineLinkEquiv L).surjective f
  rcases q with ⟨i, b⟩ | j
  · fin_cases b
    · change haarFiberReconstruction L _ r (dyadicFineLink L (i, 0)) =
        haarFiberReconstruction L _ r (dyadicFineLink L (i, 0))
      rw [haarFiberReconstruction_first, haarFiberReconstruction_first]
    · have hie : i ≠ e := by
        intro h
        subst i
        exact hf rfl
      change haarFiberReconstruction L _ r (dyadicFineLink L (i, 1)) =
        haarFiberReconstruction L _ r (dyadicFineLink L (i, 1))
      rw [haarFiberReconstruction_second, haarFiberReconstruction_second]
      congr 1
      exact ((updateGaugeLink_same_and_other L V e.x e.μ g1).2 i hie).trans
        ((updateGaugeLink_same_and_other L V e.x e.μ g2).2 i hie).symm
  · simp

/-- The integral sampling formula is for the actual constructed Haar kernel. -/
theorem haarBlockKernel_eq_reconstruction_map (L : ℕ) [NeZero L] (V : GaugeConfig L) :
    haarBlockKernel L V = (haarFiberReference L).map (haarFiberReconstruction L V) :=
  finitePairKernel_apply SU2.haarProbability (dyadicFineLinkEquiv L) V

theorem haarBlockedFiberWeight_eq_integral (L : ℕ) [NeZero L] (β : ℝ) (V : GaugeConfig L) :
    wilsonBlockedFiberWeight (haarBlockDisintegration L) β V =
      ∫ r, boltzmannWeight β (haarFiberReconstruction L V r) ∂haarFiberReference L := by
  change (∫ U, boltzmannWeight β U ∂haarBlockKernel L V) = _
  rw [haarBlockKernel_eq_reconstruction_map]
  exact integral_map_of_stronglyMeasurable (measurable_haarFiberReconstruction L V)
    (wilsonWeight_measurable (measurable_wilsonAction β)).stronglyMeasurable

private theorem integrable_haarReconstructedWeight (L : ℕ) [NeZero L]
    {β : ℝ} (hβ : 0 ≤ β) (V : GaugeConfig L) :
    Integrable (fun r => boltzmannWeight β (haarFiberReconstruction L V r)) (haarFiberReference L) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((wilsonWeight_measurable (measurable_wilsonAction β)).comp
      (measurable_haarFiberReconstruction L V)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun r => by
    change ‖boltzmannWeight β (haarFiberReconstruction L V r)‖ ≤ 1
    rw [Real.norm_eq_abs]
    change |Real.exp (-wilsonAction β (haarFiberReconstruction L V r))| ≤ 1
    rw [abs_of_pos (Real.exp_pos _)]
    exact (boltzmannWeight_bounds hβ _).2.2

/-- Actual Haar-fiber integration preserves the derived six-plaquette `12 * β` comparison. -/
theorem haarBlockedFiberWeight_singleLink_ratio (L : ℕ) [NeZero L] {β : ℝ} (hβ : 0 ≤ β)
    (V : GaugeConfig L) (e : Link L) (g1 g2 : SU2) :
    wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V e.x e.μ g1) ≤
      Real.exp (12 * β) *
        wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V e.x e.μ g2) := by
  rw [haarBlockedFiberWeight_eq_integral, haarBlockedFiberWeight_eq_integral, ← integral_const_mul]
  apply integral_mono (integrable_haarReconstructedWeight L hβ _)
    ((integrable_haarReconstructedWeight L hβ _).const_mul _)
  intro r
  have hs := wilsonAction_oscillation_of_agree_off_link hβ
    (haarFiberReconstruction L (updateGaugeLink L V e.x e.μ g1) r)
    (haarFiberReconstruction L (updateGaugeLink L V e.x e.μ g2) r)
    (dyadicFineLink L (e, 1))
    (haarFiberReconstruction_agree_off_second L V e g1 g2 r)
  dsimp only
  unfold boltzmannWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := (abs_le.mp hs).1
  linarith

/-- The constructed finite-volume Haar effective action has volume-uniform single-link oscillation.
This elementary ceiling grows with `β`; it is not a weak-coupling smallness estimate. -/
theorem haarBlockedEffectiveAction_singleLink_oscillation (L : ℕ) [NeZero L]
    {β : ℝ} (hβ : 0 ≤ β) (V : GaugeConfig L) (e : Link L) (g1 g2 : SU2) :
    |wilsonBlockedEffectiveAction (haarBlockDisintegration L) β (updateGaugeLink L V e.x e.μ g1) -
      wilsonBlockedEffectiveAction (haarBlockDisintegration L) β (updateGaugeLink L V e.x e.μ g2)| ≤
      12 * β ∧
    |wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β (updateGaugeLink L V e.x e.μ g1) -
      wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β (updateGaugeLink L V e.x e.μ g2)| ≤
      12 * β := by
  exact wilsonBlockedNormalizedEffectiveAction_link_oscillation_from_fiber_ratio
    (haarBlockDisintegration L) hβ (measurable_wilsonAction β) V e.x e.μ g1 g2
    (haarBlockedFiberWeight_singleLink_ratio L hβ V e g1 g2)
    (haarBlockedFiberWeight_singleLink_ratio L hβ V e g2 g1)


/-- Two-sided quotient form of the actual Haar comparison; the denominator is strictly positive. -/
theorem haarBlockedFiberWeight_singleLink_quotient_bounds (L : ℕ) [NeZero L]
    {β : ℝ} (hβ : 0 ≤ β) (V : GaugeConfig L) (e : Link L) (g1 g2 : SU2) :
    Real.exp (-(12 * β)) ≤
      wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V e.x e.μ g1) /
        wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V e.x e.μ g2) ∧
    wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V e.x e.μ g1) /
        wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V e.x e.μ g2) ≤
      Real.exp (12 * β) := by
  have hpos := (wilsonBlockedFiberWeight_bounds_and_pos_all_configs (haarBlockDisintegration L)
    hβ (measurable_wilsonAction β) (updateGaugeLink L V e.x e.μ g2)).1
  constructor
  · apply (le_div_iff₀ hpos).mpr
    have h := mul_le_mul_of_nonneg_left (haarBlockedFiberWeight_singleLink_ratio L hβ V e g2 g1)
      (Real.exp_nonneg (-(12 * β)))
    simpa only [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] using h
  · exact (div_le_iff₀ hpos).mpr (haarBlockedFiberWeight_singleLink_ratio L hβ V e g1 g2)

/-- Unconditional single-link oscillation bound for the unit-coupling Wilson action `wilsonAction 1`:
updating a single link `(x, μ)` changes `wilsonAction 1` by at most `12`, derived directly from the
six-plaquette incidence bound `wilsonAction_oscillation_of_agree_off_link` with zero supplied
oscillation hypotheses. -/
theorem wilsonAction_one_updateGaugeLink_oscillation_le_twelve (L : ℕ) [NeZero L]
    (V : GaugeConfig L) (x : Lattice4D L) (μ : Fin 4) (g1 g2 : SU2) :
    |wilsonAction 1 (updateGaugeLink L V x μ g1) -
        wilsonAction 1 (updateGaugeLink L V x μ g2)| ≤ 12 := by
  have h_agree : ∀ f : Link L, f ≠ ⟨x, μ⟩ →
      updateGaugeLink L V x μ g1 f = updateGaugeLink L V x μ g2 f := by
    intro f hf
    exact ((updateGaugeLink_same_and_other L V x μ g1).2 f hf).trans
      ((updateGaugeLink_same_and_other L V x μ g2).2 f hf).symm
  have h1 := wilsonAction_oscillation_of_agree_off_link (L := L) (β := 1) (by norm_num)
    (updateGaugeLink L V x μ g1) (updateGaugeLink L V x μ g2) ⟨x, μ⟩ h_agree
  linarith

/-- Concrete Haar extracted-remainder single-link oscillation and two-link mixed second-difference
bounds on `haarBlockDisintegration L`:
1. Discharges both supplied oscillation hypotheses (`h_osc_A` and `h_osc_S1`) of
   `extractedCoarseRemainder_link_oscillation_bound` on the actual Haar blocked normalized effective
   action `wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β`, proving that the
   extracted remainder changes by at most `12 * β + 12 * |extractedCoarseCoupling|` under a single
   coarse link update with zero supplied oscillation premises,
2. Bounds the two-link mixed second difference `twoLinkMixedDifference` of both
   `wilsonBlockedEffectiveAction (haarBlockDisintegration L) β` and
   `wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β` by `24 * β` uniformly in
   lattice volume `L`, and
3. Records that both elementary ceilings (`12 * β` and `24 * β`) grow linearly with `β` (`M / 24 ≤ β → M ≤ 24 * β`),
   so weak-coupling smallness (`β → ∞`) remains an open research-frontier obligation. -/
theorem haarExtractedCoarseRemainder_singleLink_oscillation_and_twoLink_mixedDifference
    (L : ℕ) [NeZero L] (ext : LinearPlaquetteCouplingExtractor L)
    {β M : ℝ} (hβ : 0 ≤ β) (V : GaugeConfig L)
    (x1 : Lattice4D L) (μ1 : Fin 4) (g1 g2 : SU2)
    (x2 : Lattice4D L) (μ2 : Fin 4) (h1 h2 : SU2) :
    |extractedCoarseRemainder ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
        (updateGaugeLink L V x1 μ1 g1) -
      extractedCoarseRemainder ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
        (updateGaugeLink L V x1 μ1 g2)| ≤
      12 * β +
        12 * |extractedCoarseCoupling ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)| ∧
    |twoLinkMixedDifference L
        (wilsonBlockedEffectiveAction (haarBlockDisintegration L) β)
        V x1 μ1 g1 g2 x2 μ2 h1 h2| ≤ 24 * β ∧
    |twoLinkMixedDifference L
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
        V x1 μ1 g1 g2 x2 μ2 h1 h2| ≤ 24 * β ∧
    (M / 24 ≤ β → M ≤ 24 * β) := by
  have h_osc_A :=
    (haarBlockedEffectiveAction_singleLink_oscillation L hβ V ⟨x1, μ1⟩ g1 g2).2
  have h_osc_S1 :=
    wilsonAction_one_updateGaugeLink_oscillation_le_twelve L V x1 μ1 g1 g2
  have h_rem :=
    extractedCoarseRemainder_link_oscillation_bound ext
      (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
      V x1 μ1 g1 g2 h_osc_A h_osc_S1
  have h_g1 :=
    haarBlockedEffectiveAction_singleLink_oscillation L hβ
      (updateGaugeLink L V x1 μ1 g1) ⟨x2, μ2⟩ h1 h2
  have h_g2 :=
    haarBlockedEffectiveAction_singleLink_oscillation L hβ
      (updateGaugeLink L V x1 μ1 g2) ⟨x2, μ2⟩ h1 h2
  have h_re_eff :
      twoLinkMixedDifference L
        (wilsonBlockedEffectiveAction (haarBlockDisintegration L) β)
        V x1 μ1 g1 g2 x2 μ2 h1 h2 =
      (wilsonBlockedEffectiveAction (haarBlockDisintegration L) β
          (updateGaugeLink L (updateGaugeLink L V x1 μ1 g1) x2 μ2 h1) -
        wilsonBlockedEffectiveAction (haarBlockDisintegration L) β
          (updateGaugeLink L (updateGaugeLink L V x1 μ1 g1) x2 μ2 h2)) -
      (wilsonBlockedEffectiveAction (haarBlockDisintegration L) β
          (updateGaugeLink L (updateGaugeLink L V x1 μ1 g2) x2 μ2 h1) -
        wilsonBlockedEffectiveAction (haarBlockDisintegration L) β
          (updateGaugeLink L (updateGaugeLink L V x1 μ1 g2) x2 μ2 h2)) := by
    dsimp [twoLinkMixedDifference, updateTwoGaugeLinks]
    ring
  have h_tri_eff := abs_sub
    (wilsonBlockedEffectiveAction (haarBlockDisintegration L) β
        (updateGaugeLink L (updateGaugeLink L V x1 μ1 g1) x2 μ2 h1) -
      wilsonBlockedEffectiveAction (haarBlockDisintegration L) β
        (updateGaugeLink L (updateGaugeLink L V x1 μ1 g1) x2 μ2 h2))
    (wilsonBlockedEffectiveAction (haarBlockDisintegration L) β
        (updateGaugeLink L (updateGaugeLink L V x1 μ1 g2) x2 μ2 h1) -
      wilsonBlockedEffectiveAction (haarBlockDisintegration L) β
        (updateGaugeLink L (updateGaugeLink L V x1 μ1 g2) x2 μ2 h2))
  rw [← h_re_eff] at h_tri_eff
  have h_mix_eff :
      |twoLinkMixedDifference L
          (wilsonBlockedEffectiveAction (haarBlockDisintegration L) β)
          V x1 μ1 g1 g2 x2 μ2 h1 h2| ≤ 24 * β := by
    have h1_bound := h_g1.1
    have h2_bound := h_g2.1
    dsimp at h1_bound h2_bound
    linarith
  have h_re_norm :
      twoLinkMixedDifference L
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
        V x1 μ1 g1 g2 x2 μ2 h1 h2 =
      (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β
          (updateGaugeLink L (updateGaugeLink L V x1 μ1 g1) x2 μ2 h1) -
        wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β
          (updateGaugeLink L (updateGaugeLink L V x1 μ1 g1) x2 μ2 h2)) -
      (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β
          (updateGaugeLink L (updateGaugeLink L V x1 μ1 g2) x2 μ2 h1) -
        wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β
          (updateGaugeLink L (updateGaugeLink L V x1 μ1 g2) x2 μ2 h2)) := by
    dsimp [twoLinkMixedDifference, updateTwoGaugeLinks]
    ring
  have h_tri_norm := abs_sub
    (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β
        (updateGaugeLink L (updateGaugeLink L V x1 μ1 g1) x2 μ2 h1) -
      wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β
        (updateGaugeLink L (updateGaugeLink L V x1 μ1 g1) x2 μ2 h2))
    (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β
        (updateGaugeLink L (updateGaugeLink L V x1 μ1 g2) x2 μ2 h1) -
      wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β
        (updateGaugeLink L (updateGaugeLink L V x1 μ1 g2) x2 μ2 h2))
  rw [← h_re_norm] at h_tri_norm
  have h_mix_norm :
      |twoLinkMixedDifference L
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
          V x1 μ1 g1 g2 x2 μ2 h1 h2| ≤ 24 * β := by
    have h1_bound := h_g1.2
    have h2_bound := h_g2.2
    dsimp at h1_bound h2_bound
    linarith
  refine ⟨h_rem, h_mix_eff, h_mix_norm, ?_⟩
  intro hM
  linarith

/-- Diagonal zero-oscillation identity and conditional sub-Gaussian / Brascamp-Lieb fiber
concentration contract for the concrete `SU(2)` Haar dyadic disintegration
`haarBlockDisintegration L`:
1. On the diagonal (`g1 = g2`), the single-link oscillation of
   `wilsonBlockedEffectiveAction (haarBlockDisintegration L) β`,
   `wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β`, and
   `extractedCoarseRemainder ext (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)`
   vanishes identically (`= 0`), and
2. Whenever the `SU(2)` Haar fiber satisfies a conditional concentration / sub-Gaussian ratio bound
   `wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V x μ g1) ≤ Real.exp δ_subG * wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V x μ g2)`
   (and symmetrically) with `0 ≤ δ_subG`, the effective-action single-link oscillation is bounded by
   `δ_subG` and the extracted remainder oscillation on `haarBlockDisintegration L` is bounded by
   `δ_subG + 12 * |extractedCoarseCoupling ext (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)|`
   uniformly in lattice size `L`. -/
theorem haarBlockedEffectiveAction_and_extractedRemainder_diagonal_zero_and_subgaussian_contract
    (L : ℕ) [NeZero L] (ext : LinearPlaquetteCouplingExtractor L)
    {β δ_subG : ℝ} (hβ : 0 ≤ β) (hδ : 0 ≤ δ_subG)
    (V : GaugeConfig L) (x : Lattice4D L) (μ : Fin 4) (g1 g2 : SU2)
    (h_subG12 :
      wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V x μ g1) ≤
        Real.exp δ_subG *
          wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V x μ g2))
    (h_subG21 :
      wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V x μ g2) ≤
        Real.exp δ_subG *
          wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V x μ g1)) :
    (g1 = g2 →
      |wilsonBlockedEffectiveAction (haarBlockDisintegration L) β (updateGaugeLink L V x μ g1) -
          wilsonBlockedEffectiveAction (haarBlockDisintegration L) β (updateGaugeLink L V x μ g2)| = 0 ∧
      |wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β (updateGaugeLink L V x μ g1) -
          wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β (updateGaugeLink L V x μ g2)| = 0 ∧
      |extractedCoarseRemainder ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
          (updateGaugeLink L V x μ g1) -
        extractedCoarseRemainder ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
          (updateGaugeLink L V x μ g2)| = 0) ∧
    |wilsonBlockedEffectiveAction (haarBlockDisintegration L) β (updateGaugeLink L V x μ g1) -
        wilsonBlockedEffectiveAction (haarBlockDisintegration L) β (updateGaugeLink L V x μ g2)| ≤
      δ_subG ∧
    |wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β (updateGaugeLink L V x μ g1) -
        wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β (updateGaugeLink L V x μ g2)| ≤
      δ_subG ∧
    |extractedCoarseRemainder ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
        (updateGaugeLink L V x μ g1) -
      extractedCoarseRemainder ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
        (updateGaugeLink L V x μ g2)| ≤
      δ_subG +
        12 * |extractedCoarseCoupling ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)| ∧
    0 ≤ δ_subG +
        12 * |extractedCoarseCoupling ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)| := by
  have h_osc_A :=
    wilsonBlockedNormalizedEffectiveAction_link_oscillation_from_fiber_ratio
      (haarBlockDisintegration L) hβ (measurable_wilsonAction β) V x μ g1 g2 h_subG12 h_subG21
  have h_osc_S1 :=
    wilsonAction_one_updateGaugeLink_oscillation_le_twelve L V x μ g1 g2
  have h_rem :=
    extractedCoarseRemainder_link_oscillation_bound ext
      (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
      V x μ g1 g2 h_osc_A.2 h_osc_S1
  have h_abs_nonneg := abs_nonneg (extractedCoarseCoupling ext
    (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β))
  refine ⟨?_, h_osc_A.1, h_osc_A.2, h_rem, by linarith⟩
  intro h_eq
  subst h_eq
  simp

/-- Conditional consequences of supplied inverse-`β` fiber-ratio bounds for the concrete
`SU(2)` Haar dyadic disintegration. Neither ratio bound is proved here:
1. Proves `0 ≤ c_hess / β` for `0 ≤ c_hess` and `0 < β`,
2. Proves that under the `c_hess / β` fiber concentration ratio bound on `haarBlockDisintegration L`,
   the single-link oscillation of `wilsonBlockedEffectiveAction` and
   `wilsonBlockedNormalizedEffectiveAction` is bounded by `c_hess / β` (which shrinks as `β` grows
   and is strictly smaller than `12 * β` for `max 1 c_hess ≤ β`) and the extracted coarse remainder
   oscillation is bounded by `c_hess / β + 12 * |extractedCoarseCoupling ext (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)|`
   uniformly in `L`, and
3. Proves that when `12 * |extractedCoarseCoupling ext (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)| ≤ η_target / 2`
   and `2 * c_hess / η_target ≤ β` (`0 < η_target`), the total single-link oscillation of
   `extractedCoarseRemainder` on `haarBlockDisintegration L` is `≤ η_target`. -/
theorem haarWeakCoupling_inverse_beta_fiber_concentration_bounds_remainder_and_contrasts_linear_ceiling
    (L : ℕ) [NeZero L] (ext : LinearPlaquetteCouplingExtractor L)
    {β c_hess η_target : ℝ} (hβ : 0 < β) (hc : 0 ≤ c_hess) (hη : 0 < η_target)
    (V : GaugeConfig L) (x : Lattice4D L) (μ : Fin 4) (g1 g2 : SU2)
    (h_subG12 :
      wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V x μ g1) ≤
        Real.exp (c_hess / β) *
          wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V x μ g2))
    (h_subG21 :
      wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V x μ g2) ≤
        Real.exp (c_hess / β) *
          wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V x μ g1)) :
    0 ≤ c_hess / β ∧
    |wilsonBlockedEffectiveAction (haarBlockDisintegration L) β (updateGaugeLink L V x μ g1) -
        wilsonBlockedEffectiveAction (haarBlockDisintegration L) β (updateGaugeLink L V x μ g2)| ≤
      c_hess / β ∧
    |wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β (updateGaugeLink L V x μ g1) -
        wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β (updateGaugeLink L V x μ g2)| ≤
      c_hess / β ∧
    |extractedCoarseRemainder ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
        (updateGaugeLink L V x μ g1) -
      extractedCoarseRemainder ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
        (updateGaugeLink L V x μ g2)| ≤
      c_hess / β +
        12 * |extractedCoarseCoupling ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)| ∧
    (max 1 c_hess ≤ β → c_hess / β < 12 * β) ∧
    (12 * |extractedCoarseCoupling ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)| ≤
        η_target / 2 →
      2 * c_hess / η_target ≤ β →
      |extractedCoarseRemainder ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
          (updateGaugeLink L V x μ g1) -
        extractedCoarseRemainder ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
          (updateGaugeLink L V x μ g2)| ≤ η_target) := by
  have hδ : 0 ≤ c_hess / β := div_nonneg hc hβ.le
  have h_base :=
    haarBlockedEffectiveAction_and_extractedRemainder_diagonal_zero_and_subgaussian_contract
      L ext hβ.le hδ V x μ g1 g2 h_subG12 h_subG21
  refine ⟨hδ, h_base.2.1, h_base.2.2.1, h_base.2.2.2.1, ?_, ?_⟩
  · intro h_max
    have hβ1 : 1 ≤ β := le_trans (le_max_left 1 c_hess) h_max
    have hβc : c_hess ≤ β := le_trans (le_max_right 1 c_hess) h_max
    have h_div_le : c_hess / β ≤ 1 := by
      rw [div_le_iff₀ hβ]
      linarith
    linarith
  · intro h_coupl h_beta_thresh
    have h_div_eta : c_hess / β ≤ η_target / 2 := by
      rw [div_le_iff₀ hβ]
      have h1 := (div_le_iff₀ hη).mp h_beta_thresh
      linarith
    have h_rem := h_base.2.2.2.1
    linarith

/-- Sum of an arbitrary coarse function and the pure-Wilson one-step remainder.
No identity identifies this sum with blocking a previous interacting remainder
inside the fiber integral. -/
noncomputable def haarCarriedForwardTotalRemainder
    (L : ℕ) [NeZero L] (ext : LinearPlaquetteCouplingExtractor L)
    (β : ℝ) (K_carried : GaugeConfig L → ℝ) (V : GaugeConfig L) : ℝ :=
  K_carried V +
    extractedCoarseRemainder ext
      (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V

/-- Triangle bound for the supplied sum, conditional on carried-function oscillation
and both fiber ratios. The final inequality is a scalar budget below one; a
single-link oscillation does not bound the off-diagonal conditional-TV row sum.
An actual Dobrushin contraction requires the separate pairwise influence bounds. -/
theorem haarCarriedForwardTotalRemainder_single_link_oscillation_and_dobrushin_tube
    (L : ℕ) [NeZero L] (ext : LinearPlaquetteCouplingExtractor L)
    {β c_hess q_step η_prev η_star β_ir : ℝ}
    (hβ : 0 < β) (hc : 0 ≤ c_hess) (hq : 0 ≤ q_step) (hη_prev : 0 ≤ η_prev) (hβ_ir : 0 ≤ β_ir)
    (K_carried : GaugeConfig L → ℝ)
    (V : GaugeConfig L) (x : Lattice4D L) (μ : Fin 4) (g1 g2 : SU2)
    (h_carried_osc :
      |K_carried (updateGaugeLink L V x μ g1) - K_carried (updateGaugeLink L V x μ g2)| ≤
        q_step * η_prev)
    (h_subG12 :
      wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V x μ g1) ≤
        Real.exp (c_hess / β) *
          wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V x μ g2))
    (h_subG21 :
      wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V x μ g2) ≤
        Real.exp (c_hess / β) *
          wilsonBlockedFiberWeight (haarBlockDisintegration L) β (updateGaugeLink L V x μ g1)) :
    |haarCarriedForwardTotalRemainder L ext β K_carried (updateGaugeLink L V x μ g1) -
        haarCarriedForwardTotalRemainder L ext β K_carried (updateGaugeLink L V x μ g2)| ≤
      q_step * η_prev + c_hess / β +
        12 * |extractedCoarseCoupling ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)| ∧
    0 ≤ q_step * η_prev + c_hess / β +
        12 * |extractedCoarseCoupling ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)| ∧
    (q_step * η_prev + c_hess / β +
        12 * |extractedCoarseCoupling ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)| ≤ η_star →
      18 * β_ir + η_star < 1 →
      0 ≤ 18 * β_ir +
        |haarCarriedForwardTotalRemainder L ext β K_carried (updateGaugeLink L V x μ g1) -
          haarCarriedForwardTotalRemainder L ext β K_carried (updateGaugeLink L V x μ g2)| ∧
      18 * β_ir +
        |haarCarriedForwardTotalRemainder L ext β K_carried (updateGaugeLink L V x μ g1) -
          haarCarriedForwardTotalRemainder L ext β K_carried (updateGaugeLink L V x μ g2)| ≤
        18 * β_ir + η_star ∧
      18 * β_ir +
        |haarCarriedForwardTotalRemainder L ext β K_carried (updateGaugeLink L V x μ g1) -
          haarCarriedForwardTotalRemainder L ext β K_carried (updateGaugeLink L V x μ g2)| < 1) := by
  have hδ : 0 ≤ c_hess / β := div_nonneg hc hβ.le
  have h_base :=
    haarBlockedEffectiveAction_and_extractedRemainder_diagonal_zero_and_subgaussian_contract
      L ext hβ.le hδ V x μ g1 g2 h_subG12 h_subG21
  have h_rem_osc := h_base.2.2.2.1
  have h_rem_nonneg := h_base.2.2.2.2
  have h_split :
      haarCarriedForwardTotalRemainder L ext β K_carried (updateGaugeLink L V x μ g1) -
        haarCarriedForwardTotalRemainder L ext β K_carried (updateGaugeLink L V x μ g2) =
      (K_carried (updateGaugeLink L V x μ g1) - K_carried (updateGaugeLink L V x μ g2)) +
      (extractedCoarseRemainder ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
          (updateGaugeLink L V x μ g1) -
        extractedCoarseRemainder ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
          (updateGaugeLink L V x μ g2)) := by
    dsimp [haarCarriedForwardTotalRemainder]
    ring
  have h_tri := abs_add_le
    (K_carried (updateGaugeLink L V x μ g1) - K_carried (updateGaugeLink L V x μ g2))
    (extractedCoarseRemainder ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
        (updateGaugeLink L V x μ g1) -
      extractedCoarseRemainder ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)
        (updateGaugeLink L V x μ g2))
  rw [← h_split] at h_tri
  have h_tot_osc :
      |haarCarriedForwardTotalRemainder L ext β K_carried (updateGaugeLink L V x μ g1) -
          haarCarriedForwardTotalRemainder L ext β K_carried (updateGaugeLink L V x μ g2)| ≤
        q_step * η_prev + c_hess / β +
          12 * |extractedCoarseCoupling ext
            (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)| := by
    linarith
  have hqη_nonneg : 0 ≤ q_step * η_prev := mul_nonneg hq hη_prev
  have h_abs_tot_nonneg := abs_nonneg
    (haarCarriedForwardTotalRemainder L ext β K_carried (updateGaugeLink L V x μ g1) -
      haarCarriedForwardTotalRemainder L ext β K_carried (updateGaugeLink L V x μ g2))
  refine ⟨h_tot_osc, by linarith, ?_⟩
  intro h_le_star h_tube
  refine ⟨by linarith, by linarith, by linarith⟩

open MeasureTheory.Measure Set Filter
open scoped Topology

/-- The product Haar reference measure on `HaarFiberCoordinates L` assigns strictly positive measure
to every nonempty open subset. -/
instance (L : ℕ) [NeZero L] : IsOpenPosMeasure (haarFiberReference L) := by
  unfold haarFiberReference
  have : IsOpenPosMeasure (gaugeHaarMeasure L) := by
    change IsOpenPosMeasure (Measure.pi (fun _ : Link L => SU2.haarProbability))
    infer_instance
  infer_instance

/-- For any fixed coarse gauge configuration `V : GaugeConfig L`, the Haar-fiber reconstruction map
`haarFiberReconstruction L V : HaarFiberCoordinates L → GaugeConfig (2 * L)` is continuous. -/
@[continuity, fun_prop]
theorem continuous_haarFiberReconstruction (L : ℕ) [NeZero L] (V : GaugeConfig L) :
    Continuous (haarFiberReconstruction L V) := by
  apply continuous_pi
  intro f
  obtain ⟨q, rfl⟩ := (dyadicFineLinkEquiv L).surjective f
  rcases q with ⟨e, b⟩ | j
  · fin_cases b
    · have hc : Continuous (fun r : HaarFiberCoordinates L => r.1 e) :=
        (continuous_apply e).comp continuous_fst
      convert hc using 1
      funext r
      exact haarFiberReconstruction_first L V r e
    · have hc : Continuous (fun r : HaarFiberCoordinates L => (r.1 e)⁻¹ * V e) :=
        ((continuous_apply e).comp continuous_fst).inv.mul continuous_const
      convert hc using 1
      funext r
      exact haarFiberReconstruction_second L V r e
  · have hc : Continuous (fun r : HaarFiberCoordinates L => r.2 j) :=
      (continuous_apply j).comp continuous_snd
    convert hc using 1
    funext r
    exact haarFiberReconstruction_unused L V r j

/-- Every reconstructed fine gauge configuration `haarFiberReconstruction L V r` projects back to
the exact coarse configuration `V` under `dyadicLinkBlockMap L`. -/
@[simp]
theorem dyadicLinkBlockMap_haarFiberReconstruction (L : ℕ) [NeZero L]
    (V : GaugeConfig L) (r : HaarFiberCoordinates L) :
    dyadicLinkBlockMap L (haarFiberReconstruction L V r) = V := by
  funext e
  dsimp [dyadicLinkBlockMap]
  rw [← dyadicFineLink_zero L e, ← dyadicFineLink_one L e,
    haarFiberReconstruction_first, haarFiberReconstruction_second, mul_inv_cancel_left]

/-- Exact geometric identification of the Haar reconstruction fiber: the image of
`haarFiberReconstruction L V` over `HaarFiberCoordinates L` equals the full dyadic block-spin
fiber `{U : GaugeConfig (2 * L) | dyadicLinkBlockMap L U = V}`. -/
theorem range_haarFiberReconstruction_eq_fiber (L : ℕ) [NeZero L] (V : GaugeConfig L) :
    Set.range (haarFiberReconstruction L V) =
      {U : GaugeConfig (2 * L) | dyadicLinkBlockMap L U = V} := by
  ext U
  simp only [Set.mem_range]
  constructor
  · rintro ⟨r, rfl⟩
    exact dyadicLinkBlockMap_haarFiberReconstruction L V r
  · intro hU
    refine ⟨(fun e => U (dyadicFineLink L (e, 0)), fun j => U j.val), ?_⟩
    funext f
    obtain ⟨q, rfl⟩ := (dyadicFineLinkEquiv L).surjective f
    rcases q with ⟨e, b⟩ | j
    · fin_cases b
      · exact haarFiberReconstruction_first L V _ e
      · change haarFiberReconstruction L V _ (dyadicFineLink L (e, 1)) =
          U (dyadicFineLink L (e, 1))
        rw [haarFiberReconstruction_second]
        have h_block : U (dyadicFineLink L (e, 0)) * U (dyadicFineLink L (e, 1)) = V e := by
          have h1 := congrFun hU e
          dsimp [dyadicLinkBlockMap] at h1
          rwa [← dyadicFineLink_zero L e, ← dyadicFineLink_one L e] at h1
        rw [← h_block, inv_mul_cancel_left]
    · exact haarFiberReconstruction_unused L V _ j

/-- Unscaled fine Wilson action energy `S_{2L,1}(haarFiberReconstruction L V r)` on the actual Haar
fiber over a fixed coarse configuration `V : GaugeConfig L`. -/
noncomputable def haarFiberActionEnergy (L : ℕ) [NeZero L] (V : GaugeConfig L)
    (r : HaarFiberCoordinates L) : ℝ :=
  wilsonAction 1 (haarFiberReconstruction L V r)

/-- Because `HaarFiberCoordinates L` is compact and `haarFiberActionEnergy L V` is continuous, the
fiber action attains its global minimum at some `r_min : HaarFiberCoordinates L`, which by
`range_haarFiberReconstruction_eq_fiber` is also the global minimum of `wilsonAction 1 U` over the
entire geometric fiber `{U : GaugeConfig (2 * L) | dyadicLinkBlockMap L U = V}`. -/
theorem exists_haarFiberActionEnergy_minimizer (L : ℕ) [NeZero L] (V : GaugeConfig L) :
    ∃ r_min : HaarFiberCoordinates L,
      (∀ r : HaarFiberCoordinates L,
        haarFiberActionEnergy L V r_min ≤ haarFiberActionEnergy L V r) ∧
      (∀ U : GaugeConfig (2 * L), dyadicLinkBlockMap L U = V →
        haarFiberActionEnergy L V r_min ≤ wilsonAction 1 U) := by
  have : CompactSpace (GaugeConfig L) := inferInstanceAs (CompactSpace (Link L → SU2))
  have h_cont : Continuous (haarFiberActionEnergy L V) :=
    (continuous_wilsonAction (L := 2 * L) 1).comp (continuous_haarFiberReconstruction L V)
  have h_nonempty : (Set.univ : Set (HaarFiberCoordinates L)).Nonempty :=
    ⟨(vacuumConfig L, fun _ => 1), Set.mem_univ _⟩
  obtain ⟨r_min, _, hr_min⟩ :=
    isCompact_univ.exists_isMinOn h_nonempty h_cont.continuousOn
  have h_all_r : ∀ r : HaarFiberCoordinates L,
      haarFiberActionEnergy L V r_min ≤ haarFiberActionEnergy L V r :=
    fun r => hr_min (Set.mem_univ r)
  refine ⟨r_min, h_all_r, ?_⟩
  intro U hU
  have hU_mem : U ∈ Set.range (haarFiberReconstruction L V) := by
    rw [range_haarFiberReconstruction_eq_fiber L V]
    exact hU
  rcases hU_mem with ⟨r, rfl⟩
  exact h_all_r r

/-- Classical minimum fine Wilson action `I_L(V)` on the Haar fiber over `V : GaugeConfig L`. -/
noncomputable def haarFiberMinimumAction (L : ℕ) [NeZero L] (V : GaugeConfig L) : ℝ :=
  haarFiberActionEnergy L V (Classical.choose (exists_haarFiberActionEnergy_minimizer L V))

/-- Nonnegativity, minimizer attainment, geometric-fiber lower bound, and exact vacuum normalization
`I_L(vacuumConfig L) = 0` for the Haar-fiber minimum action `haarFiberMinimumAction L V`. -/
theorem haarFiberMinimumAction_spec_and_vacuum_zero (L : ℕ) [NeZero L] (V : GaugeConfig L) :
    0 ≤ haarFiberMinimumAction L V ∧
    (∃ r_min : HaarFiberCoordinates L,
      haarFiberActionEnergy L V r_min = haarFiberMinimumAction L V) ∧
    (∀ r : HaarFiberCoordinates L,
      haarFiberMinimumAction L V ≤ haarFiberActionEnergy L V r) ∧
    (∀ U : GaugeConfig (2 * L), dyadicLinkBlockMap L U = V →
      haarFiberMinimumAction L V ≤ wilsonAction 1 U) ∧
    haarFiberMinimumAction L (vacuumConfig L) = 0 := by
  have h_spec := Classical.choose_spec (exists_haarFiberActionEnergy_minimizer L V)
  let r_min := Classical.choose (exists_haarFiberActionEnergy_minimizer L V)
  have h_nonneg : 0 ≤ haarFiberMinimumAction L V :=
    wilsonAction_nonneg (L := 2 * L) (β := 1) (by norm_num) (haarFiberReconstruction L V r_min)
  have h_vac_spec := Classical.choose_spec (exists_haarFiberActionEnergy_minimizer L (vacuumConfig L))
  have h_vac_nonneg : 0 ≤ haarFiberMinimumAction L (vacuumConfig L) :=
    wilsonAction_nonneg (L := 2 * L) (β := 1) (by norm_num)
      (haarFiberReconstruction L (vacuumConfig L)
        (Classical.choose (exists_haarFiberActionEnergy_minimizer L (vacuumConfig L))))
  have h_vac_block : dyadicLinkBlockMap L (vacuumConfig (2 * L)) = vacuumConfig L :=
    dyadicLinkBlockMap_vacuum L
  have h_vac_le : haarFiberMinimumAction L (vacuumConfig L) ≤ 0 := by
    have h1 := h_vac_spec.2 (vacuumConfig (2 * L)) h_vac_block
    simpa only [haarFiberMinimumAction, wilsonAction_vacuum] using h1
  exact ⟨h_nonneg, ⟨r_min, rfl⟩, h_spec.1, h_spec.2, le_antisymm h_vac_le h_vac_nonneg⟩

/-- Quantitative Laplace sandwich for the actual Haar-blocked fiber weight
`wilsonBlockedFiberWeight (haarBlockDisintegration L) β V` at fixed `(L, V)`: for every `ε > 0`,
the open sublevel set `{r | haarFiberActionEnergy L V r < I_L(V) + ε}` has strictly positive Haar
reference measure `c ∈ (0, 1]`, yielding two-sided exponential and `-\beta⁻¹ \log W_β(V)` bounds
for all `β > 0` with zero caller-supplied ratio, continuity, compactness, or support hypotheses. -/
theorem haarBlockedFiberWeight_laplace_sandwich (L : ℕ) [NeZero L] (V : GaugeConfig L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ {β : ℝ}, 0 < β →
        (c * Real.exp (-(β * (haarFiberMinimumAction L V + ε))) ≤
          wilsonBlockedFiberWeight (haarBlockDisintegration L) β V ∧
        wilsonBlockedFiberWeight (haarBlockDisintegration L) β V ≤
          Real.exp (-(β * haarFiberMinimumAction L V))) ∧
        (haarFiberMinimumAction L V ≤
          -Real.log (wilsonBlockedFiberWeight (haarBlockDisintegration L) β V) / β ∧
        -Real.log (wilsonBlockedFiberWeight (haarBlockDisintegration L) β V) / β ≤
          haarFiberMinimumAction L V + ε - Real.log c / β) := by
  let S_sub : Set (HaarFiberCoordinates L) :=
    {r | haarFiberActionEnergy L V r < haarFiberMinimumAction L V + ε}
  have h_cont : Continuous (haarFiberActionEnergy L V) :=
    (continuous_wilsonAction (L := 2 * L) 1).comp (continuous_haarFiberReconstruction L V)
  have h_open : IsOpen S_sub := isOpen_lt h_cont continuous_const
  have h_meas : MeasurableSet S_sub := h_open.measurableSet
  have h_spec := haarFiberMinimumAction_spec_and_vacuum_zero L V
  rcases h_spec.2.1 with ⟨r_min, hr_min⟩
  have h_nonempty : S_sub.Nonempty := ⟨r_min, by simp [S_sub, hr_min, hε]⟩
  let c : ℝ := (haarFiberReference L).real S_sub
  have hc_pos : 0 < c :=
    ENNReal.toReal_pos (ne_of_gt (h_open.measure_pos (haarFiberReference L) h_nonempty))
      (measure_ne_top _ _)
  have hc_le_one : c ≤ 1 := measureReal_le_one
  refine ⟨c, hc_pos, hc_le_one, ?_⟩
  intro β hβ
  have hi : Integrable (fun r => boltzmannWeight β (haarFiberReconstruction L V r))
      (haarFiberReference L) := by
    apply (integrable_const (1 : ℝ)).mono'
      ((wilsonWeight_measurable (measurable_wilsonAction β)).comp
        (measurable_haarFiberReconstruction L V)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun r => by
      change ‖boltzmannWeight β (haarFiberReconstruction L V r)‖ ≤ 1
      rw [Real.norm_eq_abs]
      change |Real.exp (-wilsonAction β (haarFiberReconstruction L V r))| ≤ 1
      rw [abs_of_pos (Real.exp_pos _)]
      exact (boltzmannWeight_bounds hβ.le _).2.2
  have h_lower : c * Real.exp (-(β * (haarFiberMinimumAction L V + ε))) ≤
      wilsonBlockedFiberWeight (haarBlockDisintegration L) β V := by
    rw [haarBlockedFiberWeight_eq_integral]
    calc
      c * Real.exp (-(β * (haarFiberMinimumAction L V + ε)))
        = ∫ _ in S_sub, Real.exp (-(β * (haarFiberMinimumAction L V + ε)))
            ∂haarFiberReference L := by
          simp [c]
      _ ≤ ∫ r in S_sub, boltzmannWeight β (haarFiberReconstruction L V r)
            ∂haarFiberReference L := by
          apply setIntegral_mono_on (integrable_const _) hi.integrableOn h_meas
          intro r hr
          unfold boltzmannWeight
          apply Real.exp_le_exp.mpr
          rw [wilsonAction_eq_beta_mul_wilsonAction_one]
          exact neg_le_neg (mul_le_mul_of_nonneg_left (le_of_lt hr) hβ.le)
      _ ≤ ∫ r, boltzmannWeight β (haarFiberReconstruction L V r) ∂haarFiberReference L :=
          setIntegral_le_integral hi (Filter.Eventually.of_forall fun r =>
            (Real.exp_pos (-wilsonAction β (haarFiberReconstruction L V r))).le)
  have h_upper : wilsonBlockedFiberWeight (haarBlockDisintegration L) β V ≤
      Real.exp (-(β * haarFiberMinimumAction L V)) := by
    rw [haarBlockedFiberWeight_eq_integral]
    calc
      (∫ r, boltzmannWeight β (haarFiberReconstruction L V r) ∂haarFiberReference L)
        ≤ ∫ _, Real.exp (-(β * haarFiberMinimumAction L V)) ∂haarFiberReference L := by
          apply integral_mono hi (integrable_const _)
          intro r
          unfold boltzmannWeight
          apply Real.exp_le_exp.mpr
          rw [wilsonAction_eq_beta_mul_wilsonAction_one]
          exact neg_le_neg (mul_le_mul_of_nonneg_left (h_spec.2.2.1 r) hβ.le)
      _ = Real.exp (-(β * haarFiberMinimumAction L V)) := by
          simp
  have hw_pos : 0 < wilsonBlockedFiberWeight (haarBlockDisintegration L) β V :=
    lt_of_lt_of_le (mul_pos hc_pos (Real.exp_pos _)) h_lower
  have h_log_upper := Real.log_le_log hw_pos h_upper
  rw [Real.log_exp] at h_log_upper
  have h_log_lower := Real.log_le_log (mul_pos hc_pos (Real.exp_pos _)) h_lower
  rw [Real.log_mul (ne_of_gt hc_pos) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at h_log_lower
  refine ⟨⟨h_lower, h_upper⟩, ?_, ?_⟩
  · rw [le_div_iff₀ hβ]
    linarith
  · rw [div_le_iff₀ hβ]
    have h_sub_mul : (haarFiberMinimumAction L V + ε - Real.log c / β) * β =
        (haarFiberMinimumAction L V + ε) * β - Real.log c := by
      rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hβ)]
    linarith

/-- Unconditional fixed-`(L, V)` finite-fiber Laplace principle on the actual Haar fiber: as
`β → ∞`, the rescaled negative log fiber weight `-\beta⁻¹ \log W_β(V)` converges to the classical
minimum fine Wilson action `haarFiberMinimumAction L V` over the exact geometric fiber
`{U : GaugeConfig (2 * L) | dyadicLinkBlockMap L U = V}`. Scope note: this is a fixed-`(L, V)`
weak-coupling Laplace limit on the finite-dimensional compact Haar fiber and does not claim
uniform-in-`L` remainder bounds, `O(1 / β)` concentration without Hessian hypotheses, or physical
mass-gap closure. -/
theorem haarBlockedFiberWeight_neg_log_div_beta_tendsto (L : ℕ) [NeZero L] (V : GaugeConfig L) :
    Tendsto
      (fun β : ℝ => -Real.log (wilsonBlockedFiberWeight (haarBlockDisintegration L) β V) / β)
      atTop (𝓝 (haarFiberMinimumAction L V)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨c, _, _, h_bounds⟩ := haarBlockedFiberWeight_laplace_sandwich L V zero_lt_one
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    exact lt_of_lt_of_le ha (h_bounds hβ).2.1
  · intro b hb
    have hε : 0 < (b - haarFiberMinimumAction L V) / 2 := by linarith
    obtain ⟨c, _, _, h_bounds⟩ := haarBlockedFiberWeight_laplace_sandwich L V hε
    have h_div : Tendsto (fun β : ℝ => Real.log c / β) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h_lim : Tendsto
        (fun β : ℝ =>
          haarFiberMinimumAction L V + (b - haarFiberMinimumAction L V) / 2 - Real.log c / β)
        atTop (𝓝 (haarFiberMinimumAction L V + (b - haarFiberMinimumAction L V) / 2)) := by
      simpa using tendsto_const_nhds.sub h_div
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      h_lim.eventually_lt_const
        (by linarith : haarFiberMinimumAction L V + (b - haarFiberMinimumAction L V) / 2 < b)]
      with β hβ hlt
    exact lt_of_le_of_lt (h_bounds hβ).2.2 hlt

/-- Exact algebraic equivalence between two-configuration oscillation of the extracted coarse
remainder `extractedCoarseRemainder ext (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β)`
and compensated fiber-weight ratios on the actual Haar fiber. -/
theorem haarExtractedCoarseRemainder_compensated_ratio_identity_and_iff
    (L : ℕ) [NeZero L] (ext : LinearPlaquetteCouplingExtractor L)
    {β η : ℝ} (hβ : 0 ≤ β) (V1 V2 : GaugeConfig L) :
    0 < Real.exp
        (extractedCoarseCoupling ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) *
          (wilsonAction 1 V1 - wilsonAction 1 V2)) *
        (wilsonBlockedFiberWeight (haarBlockDisintegration L) β V1 /
          wilsonBlockedFiberWeight (haarBlockDisintegration L) β V2) ∧
    extractedCoarseRemainder ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V1 -
      extractedCoarseRemainder ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V2 =
      -Real.log
        (Real.exp
          (extractedCoarseCoupling ext
            (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) *
            (wilsonAction 1 V1 - wilsonAction 1 V2)) *
          (wilsonBlockedFiberWeight (haarBlockDisintegration L) β V1 /
            wilsonBlockedFiberWeight (haarBlockDisintegration L) β V2)) ∧
    (|extractedCoarseRemainder ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V1 -
        extractedCoarseRemainder ext
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V2| ≤ η ↔
      Real.exp (-η) ≤
        Real.exp
          (extractedCoarseCoupling ext
            (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) *
            (wilsonAction 1 V1 - wilsonAction 1 V2)) *
          (wilsonBlockedFiberWeight (haarBlockDisintegration L) β V1 /
            wilsonBlockedFiberWeight (haarBlockDisintegration L) β V2) ∧
      Real.exp
          (extractedCoarseCoupling ext
            (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) *
            (wilsonAction 1 V1 - wilsonAction 1 V2)) *
          (wilsonBlockedFiberWeight (haarBlockDisintegration L) β V1 /
            wilsonBlockedFiberWeight (haarBlockDisintegration L) β V2) ≤
        Real.exp η) := by
  have hw1 : 0 < wilsonBlockedFiberWeight (haarBlockDisintegration L) β V1 :=
    (wilsonBlockedFiberWeight_bounds_and_pos_all_configs (haarBlockDisintegration L)
      hβ (measurable_wilsonAction β) V1).1
  have hw2 : 0 < wilsonBlockedFiberWeight (haarBlockDisintegration L) β V2 :=
    (wilsonBlockedFiberWeight_bounds_and_pos_all_configs (haarBlockDisintegration L)
      hβ (measurable_wilsonAction β) V2).1
  have hdiv_pos : 0 < wilsonBlockedFiberWeight (haarBlockDisintegration L) β V1 /
      wilsonBlockedFiberWeight (haarBlockDisintegration L) β V2 := div_pos hw1 hw2
  have hR_pos : 0 < Real.exp
      (extractedCoarseCoupling ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) *
        (wilsonAction 1 V1 - wilsonAction 1 V2)) *
      (wilsonBlockedFiberWeight (haarBlockDisintegration L) β V1 /
        wilsonBlockedFiberWeight (haarBlockDisintegration L) β V2) :=
    mul_pos (Real.exp_pos _) hdiv_pos
  have h_id :
      extractedCoarseRemainder ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V1 -
      extractedCoarseRemainder ext
        (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V2 =
      -Real.log
        (Real.exp
          (extractedCoarseCoupling ext
            (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) *
            (wilsonAction 1 V1 - wilsonAction 1 V2)) *
          (wilsonBlockedFiberWeight (haarBlockDisintegration L) β V1 /
            wilsonBlockedFiberWeight (haarBlockDisintegration L) β V2)) := by
    rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hdiv_pos),
      Real.log_exp, Real.log_div (ne_of_gt hw1) (ne_of_gt hw2)]
    dsimp [extractedCoarseRemainder, wilsonBlockedNormalizedEffectiveAction, wilsonBlockedEffectiveAction]
    ring
  refine ⟨hR_pos, h_id, ?_⟩
  rw [h_id, abs_neg, abs_le, ← Real.le_log_iff_exp_le hR_pos, ← Real.log_le_iff_le_exp hR_pos]

/-! ## Leading-Order Extracted Remainder Asymptotics & Decisive Analytic Witness

For any fixed lattice size `L ≥ 1` and any coarse probe configuration `P : GaugeConfig L` with
`wilsonAction 1 P ≠ 0`, the concrete point-probe coupling extractor
`canonicalPlaquetteProbeExtractor P hP` and the actual Haar block disintegration
`haarBlockDisintegration L` satisfy the weak-coupling limits (`β → ∞`):
1. `wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β V / β → haarFiberMinimumAction L V`,
2. `extractedCoarseCoupling (canonicalPlaquetteProbeExtractor P hP) A_β / β → haarFiberMinimumAction L P / wilsonAction 1 P`,
3. `extractedCoarseRemainder (canonicalPlaquetteProbeExtractor P hP) A_β V / β → haarLeadingRemainderAction L P V`,
where
`haarLeadingRemainderAction L P V = haarFiberMinimumAction L V - (haarFiberMinimumAction L P / wilsonAction 1 P) * wilsonAction 1 V`.

We then resolve the decisive analytic question at fixed `L = 1`: using the concrete non-commuting
probe `haarCanonicalNoncommutingProbe 1` (`wilsonAction 1 = 2 ≠ 0`), we prove:
- `7 / 6 ≤ haarFiberMinimumAction 1 (haarCanonicalNoncommutingProbe 1)`, so
  `7 / 12 ≤ haarFiberMinimumAction 1 (haarCanonicalNoncommutingProbe 1) / wilsonAction 1 (haarCanonicalNoncommutingProbe 1)`,
- for the explicit 3-4-5 Pythagorean coarse witness `pythagoreanCoarseWitness : GaugeConfig 1`
  (obtained by a single link update `updateGaugeLink 1 flatJSheetCoarseConfig 0 0 su2Pythagorean345`
  from the flat sheet `flatJSheetCoarseConfig`), `haarFiberMinimumAction 1 pythagoreanCoarseWitness ≤ 6 / 5`
  and `wilsonAction 1 pythagoreanCoarseWitness = 54 / 25`,
- hence `haarLeadingRemainderAction 1 (haarCanonicalNoncommutingProbe 1) pythagoreanCoarseWitness ≤ -3 / 50 < 0`
  while `haarLeadingRemainderAction 1 (haarCanonicalNoncommutingProbe 1) flatJSheetCoarseConfig = 0`.

This refutes any global `O(1 / β)` (or `o(β)`) remainder bound and any uniform `O(1 / β)` (or `o(β)`)
single-link oscillation bound for the point-probe-extracted remainder at fixed `L = 1` on the
actual Haar disintegration; it does not refute restricted small-field bounds, alternative
decompositions, or Yang–Mills existence. -/

/-- The leading-order weak-coupling coefficient
`J_{L,P}(V) = I_L(V) - (I_L(P) / S_1(P)) * S_1(V)` of the point-probe-extracted coarse remainder
`extractedCoarseRemainder (canonicalPlaquetteProbeExtractor P hP) (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V`. -/
noncomputable def haarLeadingRemainderAction (L : ℕ) [NeZero L] (P V : GaugeConfig L) : ℝ :=
  haarFiberMinimumAction L V -
    (haarFiberMinimumAction L P / wilsonAction 1 P) * wilsonAction 1 V

/-- On the actual Haar block disintegration `haarBlockDisintegration L` and the concrete
point-probe extractor `canonicalPlaquetteProbeExtractor P hP` with `wilsonAction 1 P ≠ 0`,
`A_β(V) / β → I_L(V)`, `b_β / β → I_L(P) / S_1(P)`, and `K_β(V) / β → J_{L,P}(V)` as `β → ∞`,
with `J_{L,P}(vacuumConfig L) = 0` and `J_{L,P}(P) = 0`. -/
theorem haarBlockedNormalizedEffectiveAction_and_canonicalProbe_div_beta_tendsto
    (L : ℕ) [NeZero L] [NeZero (2 * L)]
    (P : GaugeConfig L) (hP : wilsonAction 1 P ≠ 0) (V : GaugeConfig L) :
    Tendsto
      (fun β : ℝ =>
        wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β V / β)
      atTop (𝓝 (haarFiberMinimumAction L V)) ∧
    Tendsto
      (fun β : ℝ =>
        extractedCoarseCoupling (canonicalPlaquetteProbeExtractor P hP)
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) / β)
      atTop (𝓝 (haarFiberMinimumAction L P / wilsonAction 1 P)) ∧
    Tendsto
      (fun β : ℝ =>
        extractedCoarseRemainder (canonicalPlaquetteProbeExtractor P hP)
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V / β)
      atTop (𝓝 (haarLeadingRemainderAction L P V)) ∧
    haarLeadingRemainderAction L P (vacuumConfig L) = 0 ∧
    haarLeadingRemainderAction L P P = 0 := by
  have hI_vac : haarFiberMinimumAction L (vacuumConfig L) = 0 :=
    (haarFiberMinimumAction_spec_and_vacuum_zero L (vacuumConfig L)).2.2.2.2
  have hA : ∀ W : GaugeConfig L,
      Tendsto
        (fun β : ℝ =>
          wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β W / β)
        atTop (𝓝 (haarFiberMinimumAction L W)) := by
    intro W
    have hW := haarBlockedFiberWeight_neg_log_div_beta_tendsto L W
    have hvac := haarBlockedFiberWeight_neg_log_div_beta_tendsto L (vacuumConfig L)
    rw [hI_vac] at hvac
    have hsub := hW.sub hvac
    rw [sub_zero] at hsub
    refine hsub.congr (fun β => ?_)
    dsimp [wilsonBlockedNormalizedEffectiveAction, wilsonBlockedEffectiveAction]
    ring
  have hAV := hA V
  have hAP := hA P
  have hb :
      Tendsto
        (fun β : ℝ =>
          extractedCoarseCoupling (canonicalPlaquetteProbeExtractor P hP)
            (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) / β)
        atTop (𝓝 (haarFiberMinimumAction L P / wilsonAction 1 P)) := by
    have hdiv := hAP.div_const (wilsonAction 1 P)
    refine hdiv.congr (fun β => ?_)
    dsimp [extractedCoarseCoupling, canonicalPlaquetteProbeExtractor,
      wilsonBlockedNormalizedEffectiveAction]
    ring
  have hK :
      Tendsto
        (fun β : ℝ =>
          extractedCoarseRemainder (canonicalPlaquetteProbeExtractor P hP)
            (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V / β)
        atTop (𝓝 (haarLeadingRemainderAction L P V)) := by
    have hmul := hb.mul_const (wilsonAction 1 V)
    have hsub := hAV.sub hmul
    refine hsub.congr (fun β => ?_)
    dsimp [extractedCoarseRemainder]
    ring
  have hJ_vac : haarLeadingRemainderAction L P (vacuumConfig L) = 0 := by
    dsimp [haarLeadingRemainderAction]
    rw [hI_vac, wilsonAction_vacuum 1]
    ring
  have hJ_P : haarLeadingRemainderAction L P P = 0 := by
    dsimp [haarLeadingRemainderAction]
    rw [div_mul_cancel₀ _ hP, sub_self]
  exact ⟨hAV, hb, hK, hJ_vac, hJ_P⟩

/-- At fixed lattice size `L`, any two-configuration oscillation bound
`|K_β(V1) - K_β(V2)| ≤ η(β)` with `η(β) / β → 0` as `β → ∞` (in particular any `O(1 / β)` bound)
forces `J_{L,P}(V1) = J_{L,P}(V2)`, and any finite chain from `vacuumConfig L` to `V` with `o(β)`
step oscillation forces `J_{L,P}(V) = 0`. -/
theorem haarCanonicalProbeExtractedRemainder_oscillation_and_telescoped_chain_obstruction
    (L : ℕ) [NeZero L] [NeZero (2 * L)]
    (P : GaugeConfig L) (hP : wilsonAction 1 P ≠ 0) :
    (∀ (V1 V2 : GaugeConfig L) (η : ℝ → ℝ),
      Tendsto (fun β : ℝ => η β / β) atTop (𝓝 0) →
      (∀ᶠ β : ℝ in atTop,
        |extractedCoarseRemainder (canonicalPlaquetteProbeExtractor P hP)
            (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V1 -
          extractedCoarseRemainder (canonicalPlaquetteProbeExtractor P hP)
            (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V2| ≤ η β) →
      haarLeadingRemainderAction L P V1 = haarLeadingRemainderAction L P V2) ∧
    (∀ (V1 V2 : GaugeConfig L) (c : ℝ),
      (∀ᶠ β : ℝ in atTop,
        |extractedCoarseRemainder (canonicalPlaquetteProbeExtractor P hP)
            (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V1 -
          extractedCoarseRemainder (canonicalPlaquetteProbeExtractor P hP)
            (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V2| ≤ c / β) →
      haarLeadingRemainderAction L P V1 = haarLeadingRemainderAction L P V2) ∧
    (∀ (m : ℕ) (γ : ℕ → GaugeConfig L) (η : ℝ → ℝ),
      γ 0 = vacuumConfig L →
      Tendsto (fun β : ℝ => η β / β) atTop (𝓝 0) →
      (∀ k < m, ∀ᶠ β : ℝ in atTop,
        |extractedCoarseRemainder (canonicalPlaquetteProbeExtractor P hP)
            (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) (γ (k + 1)) -
          extractedCoarseRemainder (canonicalPlaquetteProbeExtractor P hP)
            (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) (γ k)| ≤ η β) →
      haarLeadingRemainderAction L P (γ m) = 0) := by
  have h_pair :
      ∀ (V1 V2 : GaugeConfig L) (η : ℝ → ℝ),
        Tendsto (fun β : ℝ => η β / β) atTop (𝓝 0) →
        (∀ᶠ β : ℝ in atTop,
          |extractedCoarseRemainder (canonicalPlaquetteProbeExtractor P hP)
              (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V1 -
            extractedCoarseRemainder (canonicalPlaquetteProbeExtractor P hP)
              (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V2| ≤ η β) →
        haarLeadingRemainderAction L P V1 = haarLeadingRemainderAction L P V2 := by
    intro V1 V2 η hη hbound
    have hK1 := (haarBlockedNormalizedEffectiveAction_and_canonicalProbe_div_beta_tendsto L P hP V1).2.2.1
    have hK2 := (haarBlockedNormalizedEffectiveAction_and_canonicalProbe_div_beta_tendsto L P hP V2).2.2.1
    have hdiff :
        Tendsto
          (fun β : ℝ =>
            |extractedCoarseRemainder (canonicalPlaquetteProbeExtractor P hP)
                (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V1 / β -
              extractedCoarseRemainder (canonicalPlaquetteProbeExtractor P hP)
                (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V2 / β|)
          atTop (𝓝 |haarLeadingRemainderAction L P V1 - haarLeadingRemainderAction L P V2|) :=
      (hK1.sub hK2).abs
    have hle :
        ∀ᶠ β : ℝ in atTop,
          |extractedCoarseRemainder (canonicalPlaquetteProbeExtractor P hP)
              (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V1 / β -
            extractedCoarseRemainder (canonicalPlaquetteProbeExtractor P hP)
              (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β) V2 / β| ≤
            η β / β := by
      filter_upwards [eventually_gt_atTop (0 : ℝ), hbound] with β hβ hβ_bound
      rw [← sub_div, abs_div, abs_of_pos hβ]
      exact div_le_div_of_nonneg_right hβ_bound hβ.le
    have habs_le : |haarLeadingRemainderAction L P V1 - haarLeadingRemainderAction L P V2| ≤ 0 :=
      le_of_tendsto_of_tendsto hdiff hη hle
    exact sub_eq_zero.mp (abs_nonpos_iff.mp habs_le)
  refine ⟨h_pair, ?_, ?_⟩
  · intro V1 V2 c hbound
    apply h_pair V1 V2 (fun β => c / β)
    · have h1 : Tendsto (fun β : ℝ => c / β) atTop (𝓝 (0 : ℝ)) :=
        tendsto_const_nhds.div_atTop tendsto_id
      simpa using h1.div_atTop tendsto_id
    · exact hbound
  · intro m γ η h0 hη hsteps
    induction m with
    | zero =>
        rw [h0]
        exact (haarBlockedNormalizedEffectiveAction_and_canonicalProbe_div_beta_tendsto L P hP (vacuumConfig L)).2.2.2.1
    | succ m ih =>
        have hm : haarLeadingRemainderAction L P (γ m) = 0 :=
          ih (fun k hk => hsteps k (Nat.lt_succ_of_lt hk))
        have hstep := h_pair (γ (m + 1)) (γ m) η hη (hsteps m (Nat.lt_succ_self m))
        exact hstep.trans hm

/-- Explicit `2 × 2` complex quaternion matrix `[[a + bi, c + di], [-c + di, a - bi]]` constructed
directly from four real parameters `a, b, c, d : ℝ`. -/
def su2QuatMatrix (a b c d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i = 0 then
      if j = 0 then ⟨a, b⟩ else ⟨c, d⟩
    else
      if j = 0 then ⟨-c, d⟩ else ⟨a, -b⟩

/-- Any real unit quaternion `(a, b, c, d)` with `a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1` defines an
element of `SU(2)`. -/
def su2OfUnitQuat (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) : SU2 where
  mat := su2QuatMatrix a b c d
  unitary := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      simp [su2QuatMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
      linarith [h]
  det_one := by
    rw [Matrix.det_fin_two]
    apply Complex.ext <;>
      simp [su2QuatMatrix] <;>
      linarith [h]

/-- The central element `-I = diag(-1, -1) ∈ SU(2)`. -/
def su2QuatCenterFlip : SU2 :=
  su2OfUnitQuat (-1) 0 0 0 (by norm_num)

/-- The special-unitary quaternion matrix `i_quat = diag(i, -i) ∈ SU(2)`. -/
def su2PauliI : SU2 :=
  su2OfUnitQuat 0 1 0 0 (by norm_num)

/-- The special-unitary quaternion matrix `j_quat = [[0, 1], [-1, 0]] ∈ SU(2)`. -/
def su2PauliJ : SU2 :=
  su2OfUnitQuat 0 0 1 0 (by norm_num)

/-- The rational 3-4-5 Pythagorean diagonal matrix
`diag(4/5 + 3i/5, 4/5 - 3i/5) ∈ SU(2)`. -/
def su2Pythagorean345 : SU2 :=
  su2OfUnitQuat (4 / 5) (3 / 5) 0 0 (by norm_num)

/-- Multiplication, conjugate-transpose, and real-trace formulas for `su2QuatMatrix`, together with
exact algebraic and trace identities for `su2QuatCenterFlip`, `su2PauliI`, `su2PauliJ`, and
`su2Pythagorean345`. -/
theorem su2Pauli_and_pythagorean345_identities :
    (∀ a1 b1 c1 d1 a2 b2 c2 d2 : ℝ,
      su2QuatMatrix a1 b1 c1 d1 * su2QuatMatrix a2 b2 c2 d2 =
        su2QuatMatrix
          (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2)
          (a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2)
          (a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2)
          (a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2)) ∧
    (∀ a b c d : ℝ,
      Matrix.conjTranspose (su2QuatMatrix a b c d) = su2QuatMatrix a (-b) (-c) (-d) ∧
      (Matrix.trace (su2QuatMatrix a b c d)).re = 2 * a) ∧
    su2PauliI * su2PauliJ * su2PauliI⁻¹ * su2PauliJ⁻¹ = su2QuatCenterFlip ∧
    (SU2.trace (su2PauliI * su2PauliJ⁻¹)).re = 0 ∧
    su2Pythagorean345 * su2PauliJ * su2Pythagorean345⁻¹ * su2PauliJ⁻¹ =
      su2Pythagorean345 * su2Pythagorean345 ∧
    (SU2.trace su2QuatCenterFlip).re = -2 ∧
    (SU2.trace su2Pythagorean345).re = 8 / 5 ∧
    (SU2.trace su2Pythagorean345⁻¹).re = 8 / 5 ∧
    (SU2.trace (su2Pythagorean345 * su2Pythagorean345)).re = 14 / 25 := by
  have hmul :
      ∀ a1 b1 c1 d1 a2 b2 c2 d2 : ℝ,
        su2QuatMatrix a1 b1 c1 d1 * su2QuatMatrix a2 b2 c2 d2 =
          su2QuatMatrix
            (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2)
            (a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2)
            (a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2)
            (a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2) := by
    intro a1 b1 c1 d1 a2 b2 c2 d2
    ext i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      simp [su2QuatMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring
  have hconj :
      ∀ a b c d : ℝ,
        Matrix.conjTranspose (su2QuatMatrix a b c d) = su2QuatMatrix a (-b) (-c) (-d) ∧
        (Matrix.trace (su2QuatMatrix a b c d)).re = 2 * a := by
    intro a b c d
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        apply Complex.ext <;>
        simp [su2QuatMatrix, Matrix.conjTranspose_apply]
    · simp [Matrix.trace, Fin.sum_univ_two, su2QuatMatrix]
      ring
  refine ⟨hmul, hconj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply SU2.ext
    change su2QuatMatrix 0 1 0 0 * su2QuatMatrix 0 0 1 0 *
        Matrix.conjTranspose (su2QuatMatrix 0 1 0 0) * Matrix.conjTranspose (su2QuatMatrix 0 0 1 0) =
      su2QuatMatrix (-1) 0 0 0
    rw [(hconj 0 1 0 0).1, (hconj 0 0 1 0).1, hmul, hmul, hmul]
    congr 1 <;> norm_num
  · change (Matrix.trace (su2QuatMatrix 0 1 0 0 * Matrix.conjTranspose (su2QuatMatrix 0 0 1 0))).re = 0
    rw [(hconj 0 0 1 0).1, hmul, (hconj _ _ _ _).2]
    norm_num
  · apply SU2.ext
    change su2QuatMatrix (4 / 5) (3 / 5) 0 0 * su2QuatMatrix 0 0 1 0 *
        Matrix.conjTranspose (su2QuatMatrix (4 / 5) (3 / 5) 0 0) *
        Matrix.conjTranspose (su2QuatMatrix 0 0 1 0) =
      su2QuatMatrix (4 / 5) (3 / 5) 0 0 * su2QuatMatrix (4 / 5) (3 / 5) 0 0
    rw [(hconj (4 / 5) (3 / 5) 0 0).1, (hconj 0 0 1 0).1, hmul, hmul, hmul, hmul]
    congr 1 <;> norm_num
  · change (Matrix.trace (su2QuatMatrix (-1) 0 0 0)).re = -2
    rw [(hconj (-1) 0 0 0).2]
    norm_num
  · change (Matrix.trace (su2QuatMatrix (4 / 5) (3 / 5) 0 0)).re = 8 / 5
    rw [(hconj (4 / 5) (3 / 5) 0 0).2]
    norm_num
  · change (Matrix.trace (Matrix.conjTranspose (su2QuatMatrix (4 / 5) (3 / 5) 0 0))).re = 8 / 5
    rw [(hconj (4 / 5) (3 / 5) 0 0).1, (hconj _ _ _ _).2]
    norm_num
  · change (Matrix.trace (su2QuatMatrix (4 / 5) (3 / 5) 0 0 * su2QuatMatrix (4 / 5) (3 / 5) 0 0)).re = 14 / 25
    rw [hmul, (hconj _ _ _ _).2]
    norm_num

/-- Every `A ∈ SU(2)` satisfies `A.mat 1 1 = star (A.mat 0 0)`, `A.mat 0 1 = -star (A.mat 1 0)`,
and `(SU2.trace A).re = 2 * (A.mat 0 0).re`, and any four `SU(2)` elements with
`M1 * M2 * M3 * M4 = su2QuatCenterFlip` have sum of single-plaquette actions at least `7 / 6`. -/
theorem su2_adjugate_and_four_factor_centerFlip_action_sum_ge_seven_sixths :
    (∀ A : SU2,
      A.mat 1 1 = star (A.mat 0 0) ∧
      A.mat 0 1 = -star (A.mat 1 0) ∧
      (SU2.trace A).re = 2 * (A.mat 0 0).re ∧
      1 - (1 / 2 : ℝ) * (SU2.trace A).re = 1 - (A.mat 0 0).re) ∧
    (∀ M1 M2 M3 M4 : SU2,
      M1 * M2 * M3 * M4 = su2QuatCenterFlip →
      (7 / 6 : ℝ) ≤
        (1 - (1 / 2 : ℝ) * (SU2.trace M1).re) +
        (1 - (1 / 2 : ℝ) * (SU2.trace M2).re) +
        (1 - (1 / 2 : ℝ) * (SU2.trace M3).re) +
        (1 - (1 / 2 : ℝ) * (SU2.trace M4).re)) := by
  have hadj_all :
      ∀ A : SU2,
        A.mat 1 1 = star (A.mat 0 0) ∧
        A.mat 0 1 = -star (A.mat 1 0) ∧
        (SU2.trace A).re = 2 * (A.mat 0 0).re ∧
        1 - (1 / 2 : ℝ) * (SU2.trace A).re = 1 - (A.mat 0 0).re := by
    intro A
    have hadj : A.mat * Matrix.adjugate A.mat = 1 := by
      rw [Matrix.mul_adjugate, A.det_one, one_smul]
    have hadj_eq : Matrix.adjugate A.mat = Matrix.conjTranspose A.mat := by
      calc
        Matrix.adjugate A.mat = (Matrix.conjTranspose A.mat * A.mat) * Matrix.adjugate A.mat := by
          rw [A.unitary, Matrix.one_mul]
        _ = Matrix.conjTranspose A.mat * (A.mat * Matrix.adjugate A.mat) := by rw [Matrix.mul_assoc]
        _ = Matrix.conjTranspose A.mat := by rw [hadj, Matrix.mul_one]
    have h00 : Matrix.adjugate A.mat 0 0 = A.mat 1 1 := by
      simp [Matrix.adjugate_fin_two]
    have h01 : Matrix.adjugate A.mat 0 1 = -A.mat 0 1 := by
      simp [Matrix.adjugate_fin_two]
    have h11 : A.mat 1 1 = star (A.mat 0 0) := by
      have h := congr_fun (congr_fun hadj_eq 0) 0
      simpa [h00, Matrix.conjTranspose_apply] using h
    have h01_eq : A.mat 0 1 = -star (A.mat 1 0) := by
      have h := congr_fun (congr_fun hadj_eq 0) 1
      have h' : -A.mat 0 1 = star (A.mat 1 0) := by
        simpa [h01, Matrix.conjTranspose_apply] using h
      exact neg_eq_iff_eq_neg.mp h'
    have htr : (SU2.trace A).re = 2 * (A.mat 0 0).re := by
      dsimp [SU2.trace, Matrix.trace]
      rw [Fin.sum_univ_two, h11]
      simp [Complex.add_re]
      ring
    refine ⟨h11, h01_eq, htr, ?_⟩
    rw [htr]
    ring
  have hmul_re :
      ∀ A B : SU2,
        ((A.mat 0 0).re + (B.mat 0 0).re) ^ 2 / 2 - 1 ≤ ((A * B).mat 0 0).re := by
    intro A B
    have hA_col := SU2.col0_norm_sq A
    have hB_col := SU2.col0_norm_sq B
    have hmul00 :
        ((A * B).mat 0 0).re =
          (A.mat 0 0).re * (B.mat 0 0).re - (A.mat 0 0).im * (B.mat 0 0).im +
            (A.mat 0 1).re * (B.mat 1 0).re - (A.mat 0 1).im * (B.mat 1 0).im := by
      change (∑ k : Fin 2, A.mat 0 k * B.mat k 0).re = _
      rw [Fin.sum_univ_two, Complex.add_re, Complex.mul_re, Complex.mul_re]
      ring
    have hA_norm :
        (A.mat 0 0).re ^ 2 + (A.mat 0 0).im ^ 2 +
          (A.mat 0 1).re ^ 2 + (A.mat 0 1).im ^ 2 = 1 := by
      have hB1 := (hadj_all A).2.1
      have hre : (A.mat 0 1).re = -(A.mat 1 0).re := by
        rw [hB1]; simp
      have him : (A.mat 0 1).im = (A.mat 1 0).im := by
        rw [hB1]; simp
      rw [hre, him]
      linarith [hA_col]
    have hsq1 : 0 ≤ ((A.mat 0 0).im - (B.mat 0 0).im) ^ 2 := sq_nonneg _
    have hsq2 : 0 ≤ ((A.mat 0 1).re + (B.mat 1 0).re) ^ 2 := sq_nonneg _
    have hsq3 : 0 ≤ ((A.mat 0 1).im - (B.mat 1 0).im) ^ 2 := sq_nonneg _
    have h_ident :
        ((A * B).mat 0 0).re - (((A.mat 0 0).re + (B.mat 0 0).re) ^ 2 / 2 - 1) =
          (1 - ((A.mat 0 0).re ^ 2 + (A.mat 0 0).im ^ 2 + (A.mat 0 1).re ^ 2 + (A.mat 0 1).im ^ 2)) / 2 +
          (1 - ((B.mat 0 0).re ^ 2 + (B.mat 0 0).im ^ 2 + ((B.mat 1 0).re ^ 2 + (B.mat 1 0).im ^ 2))) / 2 +
          ((A.mat 0 0).im - (B.mat 0 0).im) ^ 2 / 2 +
          ((A.mat 0 1).re + (B.mat 1 0).re) ^ 2 / 2 +
          ((A.mat 0 1).im - (B.mat 1 0).im) ^ 2 / 2 := by
      rw [hmul00]
      ring
    rw [hA_norm, hB_col] at h_ident
    linarith
  refine ⟨hadj_all, ?_⟩
  intro M1 M2 M3 M4 hprod
  have h12 : M1 * M2 = su2QuatCenterFlip * (M3 * M4)⁻¹ := by
    calc
      M1 * M2 = (M1 * M2 * M3 * M4) * (M3 * M4)⁻¹ := by group
      _ = su2QuatCenterFlip * (M3 * M4)⁻¹ := by rw [hprod]
  have hsum0 : ((M1 * M2).mat 0 0).re + ((M3 * M4).mat 0 0).re = 0 := by
    have hmat :
        (M1 * M2).mat 0 0 =
          (su2QuatMatrix (-1) 0 0 0 * (M3 * M4).mat.conjTranspose) 0 0 :=
      congr_fun (congr_fun (congrArg SU2.mat h12) 0) 0
    have hre : ((M1 * M2).mat 0 0).re = -((M3 * M4).mat 0 0).re := by
      have hre0 := congrArg Complex.re hmat
      simpa [su2QuatMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] using hre0
    linarith
  have h1 := hmul_re M1 M2
  have h2 := hmul_re M3 M4
  have hsq_sum :
      ((M1.mat 0 0).re + (M2.mat 0 0).re) ^ 2 +
        ((M3.mat 0 0).re + (M4.mat 0 0).re) ^ 2 ≤ 4 := by
    linarith
  have hdiff_sq :
      0 ≤ (((M1.mat 0 0).re + (M2.mat 0 0).re) -
        ((M3.mat 0 0).re + (M4.mat 0 0).re)) ^ 2 := sq_nonneg _
  have htot_id :
      ((M1.mat 0 0).re + (M2.mat 0 0).re +
        (M3.mat 0 0).re + (M4.mat 0 0).re) ^ 2 +
        (((M1.mat 0 0).re + (M2.mat 0 0).re) -
          ((M3.mat 0 0).re + (M4.mat 0 0).re)) ^ 2 =
        2 * (((M1.mat 0 0).re + (M2.mat 0 0).re) ^ 2 +
          ((M3.mat 0 0).re + (M4.mat 0 0).re) ^ 2) := by
    ring
  have htot_sq :
      ((M1.mat 0 0).re + (M2.mat 0 0).re +
        (M3.mat 0 0).re + (M4.mat 0 0).re) ^ 2 ≤ 8 := by
    linarith
  have htot_le :
      (M1.mat 0 0).re + (M2.mat 0 0).re +
        (M3.mat 0 0).re + (M4.mat 0 0).re ≤ 17 / 6 := by
    have h_nonneg :
        0 ≤ (17 / 6 - ((M1.mat 0 0).re + (M2.mat 0 0).re +
          (M3.mat 0 0).re + (M4.mat 0 0).re)) *
          (17 / 6 + ((M1.mat 0 0).re + (M2.mat 0 0).re +
            (M3.mat 0 0).re + (M4.mat 0 0).re)) := by
      have hid2 :
          (17 / 6 - ((M1.mat 0 0).re + (M2.mat 0 0).re +
            (M3.mat 0 0).re + (M4.mat 0 0).re)) *
            (17 / 6 + ((M1.mat 0 0).re + (M2.mat 0 0).re +
              (M3.mat 0 0).re + (M4.mat 0 0).re)) =
            289 / 36 - ((M1.mat 0 0).re + (M2.mat 0 0).re +
              (M3.mat 0 0).re + (M4.mat 0 0).re) ^ 2 := by
        ring
      linarith
    nlinarith
  rw [(hadj_all M1).2.2.2, (hadj_all M2).2.2.2, (hadj_all M3).2.2.2, (hadj_all M4).2.2.2]
  linarith

/-- Concrete non-commuting coarse probe configuration on `GaugeConfig L`: sets link `⟨0, 0⟩` to
`su2PauliI`, link `⟨0, 1⟩` to `su2PauliJ`, and all other links to `1`. -/
def haarCanonicalNoncommutingProbe (L : ℕ) : GaugeConfig L :=
  fun e =>
    if e = ⟨0, 0⟩ then su2PauliI
    else if e = ⟨0, 1⟩ then su2PauliJ
    else 1

/-- Explicit enumeration of the 6 elementary plaquettes on the unit torus `Plaquette 1`. -/
theorem sum_plaquette_one_eq (f : Plaquette 1 → ℝ) :
    (∑ p : Plaquette 1, f p) =
      f ⟨0, 0, 1, by decide⟩ + f ⟨0, 0, 2, by decide⟩ + f ⟨0, 0, 3, by decide⟩ +
      f ⟨0, 1, 2, by decide⟩ + f ⟨0, 1, 3, by decide⟩ + f ⟨0, 2, 3, by decide⟩ := by
  have huniv :
      (Finset.univ : Finset (Plaquette 1)) =
        {⟨0, 0, 1, by decide⟩, ⟨0, 0, 2, by decide⟩, ⟨0, 0, 3, by decide⟩,
         ⟨0, 1, 2, by decide⟩, ⟨0, 1, 3, by decide⟩, ⟨0, 2, 3, by decide⟩} := by
    ext p
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases p with ⟨x, μ, ν, h⟩
    have hx : x = 0 := Subsingleton.elim x 0
    subst hx
    revert h
    fin_cases μ <;> fin_cases ν <;> intro h <;> first | contradiction | simp
  rw [huniv]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  ring

/-- For every `L ≥ 1`, `haarCanonicalNoncommutingProbe L` has strictly positive coarse Wilson action
(`1 ≤ wilsonAction 1 (haarCanonicalNoncommutingProbe L)`, hence `wilsonAction 1 (haarCanonicalNoncommutingProbe L) ≠ 0`),
and on `L = 1` its coarse Wilson action is `wilsonAction 1 (haarCanonicalNoncommutingProbe 1) = 2`. -/
theorem haarCanonicalNoncommutingProbe_wilsonAction_pos_and_ne_zero (L : ℕ) [NeZero L] :
    1 ≤ wilsonAction 1 (haarCanonicalNoncommutingProbe L) ∧
    0 < wilsonAction 1 (haarCanonicalNoncommutingProbe L) ∧
    wilsonAction 1 (haarCanonicalNoncommutingProbe L) ≠ 0 ∧
    wilsonAction 1 (haarCanonicalNoncommutingProbe 1) = 2 := by
  have hid := su2Pauli_and_pythagorean345_identities
  have hp01 : 1 ≤ plaquetteAction (haarCanonicalNoncommutingProbe L) ⟨0, 0, 1, by decide⟩ := by
    by_cases h1 : (1 : ZMod L) = 0
    · have hs0 : shift (0 : Lattice4D L) 0 = 0 := by
        ext i; fin_cases i <;> simp [shift, unitVec, h1]
      have hs1 : shift (0 : Lattice4D L) 1 = 0 := by
        ext i; fin_cases i <;> simp [shift, unitVec, h1]
      have hhol :
          plaquetteHolonomy (haarCanonicalNoncommutingProbe L) ⟨0, 0, 1, by decide⟩ =
            su2QuatCenterFlip := by
        dsimp [plaquetteHolonomy]
        rw [hs0, hs1]
        have h_i : haarCanonicalNoncommutingProbe L ⟨0, 0⟩ = su2PauliI := by
          simp [haarCanonicalNoncommutingProbe]
        have h_j : haarCanonicalNoncommutingProbe L ⟨0, 1⟩ = su2PauliJ := by
          simp [haarCanonicalNoncommutingProbe]
        rw [h_i, h_j]
        exact hid.2.2.1
      dsimp [plaquetteAction]
      rw [hhol, hid.2.2.2.2.2.1]
      norm_num
    · have hs0_ne : shift (0 : Lattice4D L) 0 ≠ 0 := by
        intro h
        have h0 := congr_fun h 0
        simp [shift, unitVec] at h0
        exact h1 h0
      have hs1_ne : shift (0 : Lattice4D L) 1 ≠ 0 := by
        intro h
        have h0 := congr_fun h 1
        simp [shift, unitVec] at h0
        exact h1 h0
      have h_i : haarCanonicalNoncommutingProbe L ⟨0, 0⟩ = su2PauliI := by
        simp [haarCanonicalNoncommutingProbe]
      have h_j : haarCanonicalNoncommutingProbe L ⟨0, 1⟩ = su2PauliJ := by
        simp [haarCanonicalNoncommutingProbe]
      have h_s0 : haarCanonicalNoncommutingProbe L ⟨shift (0 : Lattice4D L) 0, 1⟩ = 1 := by
        simp [haarCanonicalNoncommutingProbe, hs0_ne]
      have h_s1 : haarCanonicalNoncommutingProbe L ⟨shift (0 : Lattice4D L) 1, 0⟩ = 1 := by
        simp [haarCanonicalNoncommutingProbe, hs1_ne]
      have hhol :
          plaquetteHolonomy (haarCanonicalNoncommutingProbe L) ⟨0, 0, 1, by decide⟩ =
            su2PauliI * su2PauliJ⁻¹ := by
        dsimp [plaquetteHolonomy]
        rw [h_i, h_j, h_s0, h_s1]
        group
      dsimp [plaquetteAction]
      rw [hhol, hid.2.2.2.1]
      norm_num
  have hge1 : 1 ≤ wilsonAction 1 (haarCanonicalNoncommutingProbe L) := by
    unfold wilsonAction
    rw [one_mul]
    exact le_trans hp01
      (Finset.single_le_sum (fun p _ => plaquetteAction_nonneg _ p) (Finset.mem_univ _))
  have h1_eq : wilsonAction 1 (haarCanonicalNoncommutingProbe 1) = 2 := by
    unfold wilsonAction
    rw [one_mul, sum_plaquette_one_eq]
    have hs : ∀ (x : Lattice4D 1) (μ : Direction), shift x μ = 0 :=
      fun x μ => Subsingleton.elim _ _
    have h00 : haarCanonicalNoncommutingProbe 1 ⟨0, 0⟩ = su2PauliI := by
      simp [haarCanonicalNoncommutingProbe]
    have h01 : haarCanonicalNoncommutingProbe 1 ⟨0, 1⟩ = su2PauliJ := by
      simp [haarCanonicalNoncommutingProbe]
    have h02 : haarCanonicalNoncommutingProbe 1 ⟨0, 2⟩ = 1 := by
      simp [haarCanonicalNoncommutingProbe]
    have h03 : haarCanonicalNoncommutingProbe 1 ⟨0, 3⟩ = 1 := by
      simp [haarCanonicalNoncommutingProbe]
    have hp1 : plaquetteAction (haarCanonicalNoncommutingProbe 1) ⟨0, 0, 1, by decide⟩ = 2 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h00, h01, hid.2.2.1, hid.2.2.2.2.2.1]
      norm_num
    have hp2 : plaquetteAction (haarCanonicalNoncommutingProbe 1) ⟨0, 0, 2, by decide⟩ = 0 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h00, h02]
      have h1 : su2PauliI * (1 : SU2) * su2PauliI⁻¹ * (1 : SU2)⁻¹ = 1 := by group
      rw [h1, SU2.trace_one]
      norm_num
    have hp3 : plaquetteAction (haarCanonicalNoncommutingProbe 1) ⟨0, 0, 3, by decide⟩ = 0 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h00, h03]
      have h1 : su2PauliI * (1 : SU2) * su2PauliI⁻¹ * (1 : SU2)⁻¹ = 1 := by group
      rw [h1, SU2.trace_one]
      norm_num
    have hp4 : plaquetteAction (haarCanonicalNoncommutingProbe 1) ⟨0, 1, 2, by decide⟩ = 0 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h01, h02]
      have h1 : su2PauliJ * (1 : SU2) * su2PauliJ⁻¹ * (1 : SU2)⁻¹ = 1 := by group
      rw [h1, SU2.trace_one]
      norm_num
    have hp5 : plaquetteAction (haarCanonicalNoncommutingProbe 1) ⟨0, 1, 3, by decide⟩ = 0 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h01, h03]
      have h1 : su2PauliJ * (1 : SU2) * su2PauliJ⁻¹ * (1 : SU2)⁻¹ = 1 := by group
      rw [h1, SU2.trace_one]
      norm_num
    have hp6 : plaquetteAction (haarCanonicalNoncommutingProbe 1) ⟨0, 2, 3, by decide⟩ = 0 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h02, h03]
      have h1 : (1 : SU2) * (1 : SU2) * (1 : SU2)⁻¹ * (1 : SU2)⁻¹ = 1 := by group
      rw [h1, SU2.trace_one]
      norm_num
    rw [hp1, hp2, hp3, hp4, hp5, hp6]
    ring
  exact ⟨hge1, by linarith, by linarith, h1_eq⟩

/-- Every fine configuration `U : GaugeConfig 2` in the geometric fiber over
`haarCanonicalNoncommutingProbe 1` has fine Wilson action at least `7 / 6`, so
`7 / 6 ≤ haarFiberMinimumAction 1 (haarCanonicalNoncommutingProbe 1)` and
`7 / 12 ≤ haarFiberMinimumAction 1 (haarCanonicalNoncommutingProbe 1) / wilsonAction 1 (haarCanonicalNoncommutingProbe 1)`. -/
theorem haarFiberMinimumAction_canonicalProbe_one_lower_bound :
    (∀ U : GaugeConfig 2,
      dyadicLinkBlockMap 1 U = haarCanonicalNoncommutingProbe 1 →
      (7 / 6 : ℝ) ≤ wilsonAction 1 U) ∧
    (7 / 6 : ℝ) ≤ haarFiberMinimumAction 1 (haarCanonicalNoncommutingProbe 1) ∧
    (7 / 12 : ℝ) ≤
      haarFiberMinimumAction 1 (haarCanonicalNoncommutingProbe 1) /
        wilsonAction 1 (haarCanonicalNoncommutingProbe 1) := by
  have hU_bound :
      ∀ U : GaugeConfig 2,
        dyadicLinkBlockMap 1 U = haarCanonicalNoncommutingProbe 1 →
        (7 / 6 : ℝ) ≤ wilsonAction 1 U := by
    intro U hU
    let x00 : Lattice4D 2 := 0
    let x10 : Lattice4D 2 := shift x00 0
    let x01 : Lattice4D 2 := shift x00 1
    let x11 : Lattice4D 2 := shift x10 1
    let q00 : Plaquette 2 := ⟨x00, 0, 1, by decide⟩
    let q10 : Plaquette 2 := ⟨x10, 0, 1, by decide⟩
    let q01 : Plaquette 2 := ⟨x01, 0, 1, by decide⟩
    let q11 : Plaquette 2 := ⟨x11, 0, 1, by decide⟩
    have hx10_0 : shift x10 0 = x00 := by decide
    have hx01_0 : shift x01 0 = x11 := by decide
    have hx01_1 : shift x01 1 = x00 := by decide
    have hx11_0 : shift x11 0 = x01 := by decide
    have hx11_1 : shift x11 1 = x10 := by decide
    have hx2 : (fun i : Fin 4 => ((2 * ((0 : Lattice4D 1) i).val : ℕ) : ZMod 2)) = x00 := by
      ext i; rfl
    have ha : U ⟨x00, 0⟩ * U ⟨x10, 0⟩ = su2PauliI := by
      have h := congr_fun hU ⟨0, 0⟩
      change U ⟨(fun i : Fin 4 => ((2 * ((0 : Lattice4D 1) i).val : ℕ) : ZMod 2)), 0⟩ *
        U ⟨shift (fun i : Fin 4 => ((2 * ((0 : Lattice4D 1) i).val : ℕ) : ZMod 2)) 0, 0⟩ =
        haarCanonicalNoncommutingProbe 1 ⟨0, 0⟩ at h
      rw [hx2] at h
      simpa [haarCanonicalNoncommutingProbe] using h
    have hb : U ⟨x00, 1⟩ * U ⟨x01, 1⟩ = su2PauliJ := by
      have h := congr_fun hU ⟨0, 1⟩
      change U ⟨(fun i : Fin 4 => ((2 * ((0 : Lattice4D 1) i).val : ℕ) : ZMod 2)), 1⟩ *
        U ⟨shift (fun i : Fin 4 => ((2 * ((0 : Lattice4D 1) i).val : ℕ) : ZMod 2)) 1, 1⟩ =
        haarCanonicalNoncommutingProbe 1 ⟨0, 1⟩ at h
      rw [hx2] at h
      simpa [haarCanonicalNoncommutingProbe] using h
    let W00 := plaquetteHolonomy U q00
    let W10 := plaquetteHolonomy U q10
    let W01 := plaquetteHolonomy U q01
    let W11 := plaquetteHolonomy U q11
    let M1 := U ⟨x00, 0⟩ * W10 * (U ⟨x00, 0⟩)⁻¹
    let M2 := W00
    let M3 := (U ⟨x00, 1⟩ * U ⟨x01, 0⟩) * W11 * (U ⟨x00, 1⟩ * U ⟨x01, 0⟩)⁻¹
    let M4 := U ⟨x00, 1⟩ * W01 * (U ⟨x00, 1⟩)⁻¹
    have hW00 : W00 = U ⟨x00, 0⟩ * U ⟨x10, 1⟩ * (U ⟨x01, 0⟩)⁻¹ * (U ⟨x00, 1⟩)⁻¹ := rfl
    have hW10 : W10 = U ⟨x10, 0⟩ * U ⟨x00, 1⟩ * (U ⟨x11, 0⟩)⁻¹ * (U ⟨x10, 1⟩)⁻¹ := by
      dsimp [W10, plaquetteHolonomy, q10]
      rw [hx10_0]
    have hW01 : W01 = U ⟨x01, 0⟩ * U ⟨x11, 1⟩ * (U ⟨x00, 0⟩)⁻¹ * (U ⟨x01, 1⟩)⁻¹ := by
      dsimp [W01, plaquetteHolonomy, q01]
      rw [hx01_0, hx01_1]
    have hW11 : W11 = U ⟨x11, 0⟩ * U ⟨x01, 1⟩ * (U ⟨x10, 0⟩)⁻¹ * (U ⟨x11, 1⟩)⁻¹ := by
      dsimp [W11, plaquetteHolonomy, q11]
      rw [hx11_0, hx11_1]
    have hM_prod : M1 * M2 * M3 * M4 = su2QuatCenterFlip := by
      have hcomm :
          M1 * M2 * M3 * M4 =
            (U ⟨x00, 0⟩ * U ⟨x10, 0⟩) * (U ⟨x00, 1⟩ * U ⟨x01, 1⟩) *
              (U ⟨x00, 0⟩ * U ⟨x10, 0⟩)⁻¹ * (U ⟨x00, 1⟩ * U ⟨x01, 1⟩)⁻¹ := by
        dsimp [M1, M2, M3, M4]
        rw [hW00, hW10, hW01, hW11]
        group
      rw [hcomm, ha, hb, su2Pauli_and_pythagorean345_identities.2.2.1]
    have hfour :=
      su2_adjugate_and_four_factor_centerFlip_action_sum_ge_seven_sixths.2 M1 M2 M3 M4 hM_prod
    have htr1 : SU2.trace M1 = SU2.trace W10 := SU2.trace_conj (U ⟨x00, 0⟩) W10
    have htr3 : SU2.trace M3 = SU2.trace W11 := SU2.trace_conj (U ⟨x00, 1⟩ * U ⟨x01, 0⟩) W11
    have htr4 : SU2.trace M4 = SU2.trace W01 := SU2.trace_conj (U ⟨x00, 1⟩) W01
    have hfour_plaq :
        (7 / 6 : ℝ) ≤
          plaquetteAction U q10 + plaquetteAction U q00 +
            plaquetteAction U q11 + plaquetteAction U q01 := by
      dsimp [plaquetteAction]
      rw [← htr1, ← htr3, ← htr4]
      exact hfour
    let S4 : Finset (Plaquette 2) := {q10, q00, q11, q01}
    have hS4_sum :
        (∑ q ∈ S4, plaquetteAction U q) =
          plaquetteAction U q10 + plaquetteAction U q00 +
            plaquetteAction U q11 + plaquetteAction U q01 := by
      dsimp [S4]
      repeat rw [Finset.sum_insert (by decide)]
      rw [Finset.sum_singleton]
      ring
    unfold wilsonAction
    rw [one_mul]
    calc
      (7 / 6 : ℝ) ≤ ∑ q ∈ S4, plaquetteAction U q := by linarith
      _ ≤ ∑ q : Plaquette 2, plaquetteAction U q :=
        Finset.sum_le_univ_sum_of_nonneg (fun q => plaquetteAction_nonneg U q)
  have hI_bound : (7 / 6 : ℝ) ≤ haarFiberMinimumAction 1 (haarCanonicalNoncommutingProbe 1) := by
    obtain ⟨r_min, hr_min⟩ :=
      (haarFiberMinimumAction_spec_and_vacuum_zero 1 (haarCanonicalNoncommutingProbe 1)).2.1
    rw [← hr_min]
    exact hU_bound
      (haarFiberReconstruction 1 (haarCanonicalNoncommutingProbe 1) r_min)
      (dyadicLinkBlockMap_haarFiberReconstruction 1 (haarCanonicalNoncommutingProbe 1) r_min)
  refine ⟨hU_bound, hI_bound, ?_⟩
  rw [(haarCanonicalNoncommutingProbe_wilsonAction_pos_and_ne_zero 1).2.2.2]
  linarith

/-- Flat fine sheet configuration on `GaugeConfig 2`: sets links in directions `μ ≠ 0` on the
hyperplane `x μ = 0` to `su2PauliJ`, and all other fine links to `1`. -/
def flatJSheetFineConfig : GaugeConfig 2 :=
  fun e => if e.μ ≠ 0 ∧ e.x e.μ = 0 then su2PauliJ else 1

/-- Single-fine-link perturbation of `flatJSheetFineConfig` at link `⟨0, 0⟩ : Link 2` by
`su2Pythagorean345`. -/
def pythagoreanTubeFineConfig : GaugeConfig 2 :=
  updateGaugeLink 2 flatJSheetFineConfig 0 0 su2Pythagorean345

/-- Coarse block image of `flatJSheetFineConfig` on `GaugeConfig 1`: equal to `1` in direction `0`
and `su2PauliJ` in directions `1, 2, 3`. -/
def flatJSheetCoarseConfig : GaugeConfig 1 :=
  fun e => if e.μ = 0 then 1 else su2PauliJ

/-- Single-coarse-link update of `flatJSheetCoarseConfig` at `⟨0, 0⟩ : Link 1` by
`su2Pythagorean345`. -/
def pythagoreanCoarseWitness : GaugeConfig 1 :=
  updateGaugeLink 1 flatJSheetCoarseConfig 0 0 su2Pythagorean345

/-- Complete resolution of the decisive analytic question at fixed `L = 1`:
1. `flatJSheetCoarseConfig` and `pythagoreanCoarseWitness` are the coarse block images of
   `flatJSheetFineConfig` and `pythagoreanTubeFineConfig` and differ at the single coarse link
   `⟨0, 0⟩ : Link 1`.
2. `haarFiberMinimumAction 1 flatJSheetCoarseConfig = 0`,
   `wilsonAction 1 flatJSheetCoarseConfig = 0`, and
   `haarLeadingRemainderAction 1 (haarCanonicalNoncommutingProbe 1) flatJSheetCoarseConfig = 0`.
3. `wilsonAction 1 pythagoreanTubeFineConfig ≤ 6 / 5`,
   `haarFiberMinimumAction 1 pythagoreanCoarseWitness ≤ 6 / 5`, and
   `wilsonAction 1 pythagoreanCoarseWitness = 54 / 25`.
4. `haarLeadingRemainderAction 1 (haarCanonicalNoncommutingProbe 1) pythagoreanCoarseWitness ≤ -3 / 50 < 0`,
   so `haarLeadingRemainderAction 1 (haarCanonicalNoncommutingProbe 1)` is non-vanishing at
   `pythagoreanCoarseWitness` and takes distinct values across the single-link update pair
   `(flatJSheetCoarseConfig, pythagoreanCoarseWitness)`.
5. Consequently, for the actual Haar block disintegration `haarBlockDisintegration 1` and concrete
   probe extractor `canonicalPlaquetteProbeExtractor (haarCanonicalNoncommutingProbe 1)`, neither a
   global `O(1 / β)` remainder bound nor a uniform `O(1 / β)` single-link oscillation bound can hold. -/
theorem haarLeadingRemainderAction_pythagoreanWitness_neg_and_singleLink_refutation :
    let hP0 := (haarCanonicalNoncommutingProbe_wilsonAction_pos_and_ne_zero 1).2.2.1
    let ext0 := canonicalPlaquetteProbeExtractor (haarCanonicalNoncommutingProbe 1) hP0
    (dyadicLinkBlockMap 1 flatJSheetFineConfig = flatJSheetCoarseConfig ∧
      dyadicLinkBlockMap 1 pythagoreanTubeFineConfig = pythagoreanCoarseWitness ∧
      updateGaugeLink 1 flatJSheetCoarseConfig 0 0 1 = flatJSheetCoarseConfig ∧
      updateGaugeLink 1 flatJSheetCoarseConfig 0 0 su2Pythagorean345 = pythagoreanCoarseWitness) ∧
    (wilsonAction 1 flatJSheetFineConfig = 0 ∧
      haarFiberMinimumAction 1 flatJSheetCoarseConfig = 0 ∧
      wilsonAction 1 flatJSheetCoarseConfig = 0 ∧
      haarLeadingRemainderAction 1 (haarCanonicalNoncommutingProbe 1) flatJSheetCoarseConfig = 0) ∧
    (wilsonAction 1 pythagoreanTubeFineConfig ≤ 6 / 5 ∧
      haarFiberMinimumAction 1 pythagoreanCoarseWitness ≤ 6 / 5 ∧
      wilsonAction 1 pythagoreanCoarseWitness = 54 / 25) ∧
    (haarLeadingRemainderAction 1 (haarCanonicalNoncommutingProbe 1) pythagoreanCoarseWitness ≤ -3 / 50 ∧
      haarLeadingRemainderAction 1 (haarCanonicalNoncommutingProbe 1) pythagoreanCoarseWitness ≠ 0 ∧
      haarLeadingRemainderAction 1 (haarCanonicalNoncommutingProbe 1)
          (updateGaugeLink 1 flatJSheetCoarseConfig 0 0 su2Pythagorean345) ≠
        haarLeadingRemainderAction 1 (haarCanonicalNoncommutingProbe 1)
          (updateGaugeLink 1 flatJSheetCoarseConfig 0 0 1)) ∧
    ((¬ ∃ c : ℝ, ∀ᶠ β : ℝ in atTop,
        |extractedCoarseRemainder ext0
            (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration 1) β)
            pythagoreanCoarseWitness| ≤ c / β) ∧
      (¬ ∃ c : ℝ, ∀ᶠ β : ℝ in atTop,
        ∀ (V : GaugeConfig 1) (x : Lattice4D 1) (μ : Fin 4) (g1 g2 : SU2),
          |extractedCoarseRemainder ext0
              (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration 1) β)
              (updateGaugeLink 1 V x μ g1) -
            extractedCoarseRemainder ext0
              (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration 1) β)
              (updateGaugeLink 1 V x μ g2)| ≤ c / β)) := by
  dsimp only
  have hid := su2Pauli_and_pythagorean345_identities
  have hP0 := (haarCanonicalNoncommutingProbe_wilsonAction_pos_and_ne_zero 1).2.2.1
  let ext0 := canonicalPlaquetteProbeExtractor (haarCanonicalNoncommutingProbe 1) hP0
  have hx2 : (fun i : Fin 4 => ((2 * ((0 : Lattice4D 1) i).val : ℕ) : ZMod 2)) = (0 : Lattice4D 2) := by
    ext i; rfl
  have h_block_flat : dyadicLinkBlockMap 1 flatJSheetFineConfig = flatJSheetCoarseConfig := by
    funext e
    rcases e with ⟨x, μ⟩
    have hx : x = 0 := Subsingleton.elim x 0
    subst hx
    change flatJSheetFineConfig ⟨(fun i : Fin 4 => ((2 * ((0 : Lattice4D 1) i).val : ℕ) : ZMod 2)), μ⟩ *
      flatJSheetFineConfig ⟨shift (fun i : Fin 4 => ((2 * ((0 : Lattice4D 1) i).val : ℕ) : ZMod 2)) μ, μ⟩ =
      flatJSheetCoarseConfig ⟨0, μ⟩
    rw [hx2]
    by_cases hμ : μ = 0
    · subst hμ
      simp [flatJSheetFineConfig, flatJSheetCoarseConfig]
    · have hs : (shift (0 : Lattice4D 2) μ) μ ≠ 0 := by simp [shift, unitVec]
      simp [flatJSheetFineConfig, flatJSheetCoarseConfig, hμ, hs]
  have h_block_pyth : dyadicLinkBlockMap 1 pythagoreanTubeFineConfig = pythagoreanCoarseWitness := by
    funext e
    rcases e with ⟨x, μ⟩
    have hx : x = 0 := Subsingleton.elim x 0
    subst hx
    change pythagoreanTubeFineConfig ⟨(fun i : Fin 4 => ((2 * ((0 : Lattice4D 1) i).val : ℕ) : ZMod 2)), μ⟩ *
      pythagoreanTubeFineConfig ⟨shift (fun i : Fin 4 => ((2 * ((0 : Lattice4D 1) i).val : ℕ) : ZMod 2)) μ, μ⟩ =
      pythagoreanCoarseWitness ⟨0, μ⟩
    rw [hx2]
    have hUW : ∀ f : Link 2, f ≠ ⟨0, 0⟩ → pythagoreanTubeFineConfig f = flatJSheetFineConfig f :=
      (updateGaugeLink_same_and_other 2 flatJSheetFineConfig 0 0 su2Pythagorean345).2
    have hUWc : ∀ f : Link 1, f ≠ ⟨0, 0⟩ → pythagoreanCoarseWitness f = flatJSheetCoarseConfig f :=
      (updateGaugeLink_same_and_other 1 flatJSheetCoarseConfig 0 0 su2Pythagorean345).2
    by_cases hμ : μ = 0
    · subst hμ
      have hl1 : pythagoreanTubeFineConfig ⟨0, 0⟩ = su2Pythagorean345 :=
        (updateGaugeLink_same_and_other 2 flatJSheetFineConfig 0 0 su2Pythagorean345).1
      have hs_ne : (⟨shift (0 : Lattice4D 2) 0, 0⟩ : Link 2) ≠ ⟨0, 0⟩ := by decide
      have hl2 : pythagoreanTubeFineConfig ⟨shift (0 : Lattice4D 2) 0, 0⟩ = 1 := by
        rw [hUW _ hs_ne]; simp [flatJSheetFineConfig]
      have hc : pythagoreanCoarseWitness ⟨0, 0⟩ = su2Pythagorean345 :=
        (updateGaugeLink_same_and_other 1 flatJSheetCoarseConfig 0 0 su2Pythagorean345).1
      rw [hl1, hl2, hc, mul_one]
    · have hl1_ne : (⟨0, μ⟩ : Link 2) ≠ ⟨0, 0⟩ := by
        intro h; injection h with _ hm; exact hμ hm
      have hl2_ne : (⟨shift (0 : Lattice4D 2) μ, μ⟩ : Link 2) ≠ ⟨0, 0⟩ := by
        intro h; injection h with _ hm; exact hμ hm
      have hc_ne : (⟨0, μ⟩ : Link 1) ≠ ⟨0, 0⟩ := by
        intro h; injection h with _ hm; exact hμ hm
      have hs : (shift (0 : Lattice4D 2) μ) μ ≠ 0 := by simp [shift, unitVec]
      rw [hUW _ hl1_ne, hUW _ hl2_ne, hUWc _ hc_ne]
      simp [flatJSheetFineConfig, flatJSheetCoarseConfig, hμ, hs]
  have h_upd_1 : updateGaugeLink 1 flatJSheetCoarseConfig 0 0 1 = flatJSheetCoarseConfig := by
    funext e
    by_cases he : e = ⟨0, 0⟩
    · rw [he, (updateGaugeLink_same_and_other 1 flatJSheetCoarseConfig 0 0 1).1]
      simp [flatJSheetCoarseConfig]
    · exact (updateGaugeLink_same_and_other 1 flatJSheetCoarseConfig 0 0 1).2 e he
  have h_flat_plaq : ∀ q : Plaquette 2, plaquetteAction flatJSheetFineConfig q = 0 := by
    intro q
    have hμ : flatJSheetFineConfig ⟨shift q.x q.ν, q.μ⟩ = flatJSheetFineConfig ⟨q.x, q.μ⟩ := by
      have hcoord : (shift q.x q.ν) q.μ = q.x q.μ := by
        simp [shift, unitVec, ne_of_lt q.h]
      simp [flatJSheetFineConfig, hcoord]
    have hν : flatJSheetFineConfig ⟨shift q.x q.μ, q.ν⟩ = flatJSheetFineConfig ⟨q.x, q.ν⟩ := by
      have hcoord : (shift q.x q.μ) q.ν = q.x q.ν := by
        simp [shift, unitVec, ne_of_gt q.h]
      simp [flatJSheetFineConfig, hcoord]
    have hcomm :
        ∀ a b : SU2,
          (a = 1 ∨ a = su2PauliJ) → (b = 1 ∨ b = su2PauliJ) →
          a * b * a⁻¹ * b⁻¹ = 1 := by
      intro a b ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> group
    have ha_mem :
        flatJSheetFineConfig ⟨q.x, q.μ⟩ = 1 ∨ flatJSheetFineConfig ⟨q.x, q.μ⟩ = su2PauliJ := by
      dsimp [flatJSheetFineConfig]
      split_ifs <;> simp
    have hb_mem :
        flatJSheetFineConfig ⟨q.x, q.ν⟩ = 1 ∨ flatJSheetFineConfig ⟨q.x, q.ν⟩ = su2PauliJ := by
      dsimp [flatJSheetFineConfig]
      split_ifs <;> simp
    have hhol : plaquetteHolonomy flatJSheetFineConfig q = 1 := by
      dsimp [plaquetteHolonomy]
      rw [hμ, hν]
      exact hcomm _ _ ha_mem hb_mem
    dsimp [plaquetteAction]
    rw [hhol, SU2.trace_one]
    norm_num
  have hS_flat_fine : wilsonAction 1 flatJSheetFineConfig = 0 := by
    unfold wilsonAction
    simp [h_flat_plaq]
  have hI_flat : haarFiberMinimumAction 1 flatJSheetCoarseConfig = 0 := by
    apply le_antisymm
    · have hle :=
        (haarFiberMinimumAction_spec_and_vacuum_zero 1 flatJSheetCoarseConfig).2.2.2.1
          flatJSheetFineConfig h_block_flat
      linarith
    · exact (haarFiberMinimumAction_spec_and_vacuum_zero 1 flatJSheetCoarseConfig).1
  have hS_flat_coarse : wilsonAction 1 flatJSheetCoarseConfig = 0 := by
    unfold wilsonAction
    rw [one_mul, sum_plaquette_one_eq]
    have hs : ∀ (x : Lattice4D 1) (μ : Direction), shift x μ = 0 :=
      fun x μ => Subsingleton.elim _ _
    have h0 : flatJSheetCoarseConfig ⟨0, 0⟩ = 1 := by simp [flatJSheetCoarseConfig]
    have h1 : flatJSheetCoarseConfig ⟨0, 1⟩ = su2PauliJ := by simp [flatJSheetCoarseConfig]
    have h2 : flatJSheetCoarseConfig ⟨0, 2⟩ = su2PauliJ := by simp [flatJSheetCoarseConfig]
    have h3 : flatJSheetCoarseConfig ⟨0, 3⟩ = su2PauliJ := by simp [flatJSheetCoarseConfig]
    have hp01 : plaquetteAction flatJSheetCoarseConfig ⟨0, 0, 1, by decide⟩ = 0 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h0, h1]
      have hg : (1 : SU2) * su2PauliJ * (1 : SU2)⁻¹ * su2PauliJ⁻¹ = 1 := by group
      rw [hg, SU2.trace_one]; norm_num
    have hp02 : plaquetteAction flatJSheetCoarseConfig ⟨0, 0, 2, by decide⟩ = 0 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h0, h2]
      have hg : (1 : SU2) * su2PauliJ * (1 : SU2)⁻¹ * su2PauliJ⁻¹ = 1 := by group
      rw [hg, SU2.trace_one]; norm_num
    have hp03 : plaquetteAction flatJSheetCoarseConfig ⟨0, 0, 3, by decide⟩ = 0 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h0, h3]
      have hg : (1 : SU2) * su2PauliJ * (1 : SU2)⁻¹ * su2PauliJ⁻¹ = 1 := by group
      rw [hg, SU2.trace_one]; norm_num
    have hp12 : plaquetteAction flatJSheetCoarseConfig ⟨0, 1, 2, by decide⟩ = 0 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h1, h2]
      have hg : su2PauliJ * su2PauliJ * su2PauliJ⁻¹ * su2PauliJ⁻¹ = 1 := by group
      rw [hg, SU2.trace_one]; norm_num
    have hp13 : plaquetteAction flatJSheetCoarseConfig ⟨0, 1, 3, by decide⟩ = 0 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h1, h3]
      have hg : su2PauliJ * su2PauliJ * su2PauliJ⁻¹ * su2PauliJ⁻¹ = 1 := by group
      rw [hg, SU2.trace_one]; norm_num
    have hp23 : plaquetteAction flatJSheetCoarseConfig ⟨0, 2, 3, by decide⟩ = 0 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h2, h3]
      have hg : su2PauliJ * su2PauliJ * su2PauliJ⁻¹ * su2PauliJ⁻¹ = 1 := by group
      rw [hg, SU2.trace_one]; norm_num
    rw [hp01, hp02, hp03, hp12, hp13, hp23]
    ring
  have hJ_flat :
      haarLeadingRemainderAction 1 (haarCanonicalNoncommutingProbe 1) flatJSheetCoarseConfig = 0 := by
    dsimp [haarLeadingRemainderAction]
    rw [hI_flat, hS_flat_coarse]
    ring
  have h_pyth_plaq_le :
      ∀ q : Plaquette 2, plaquetteAction pythagoreanTubeFineConfig q ≤ 1 / 5 := by
    intro q
    have hν_ne : q.ν ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le q.μ) q.h)
    have hUW : ∀ f : Link 2, f ≠ ⟨0, 0⟩ → pythagoreanTubeFineConfig f = flatJSheetFineConfig f :=
      (updateGaugeLink_same_and_other 2 flatJSheetFineConfig 0 0 su2Pythagorean345).2
    have hlink2 : pythagoreanTubeFineConfig ⟨shift q.x q.μ, q.ν⟩ = flatJSheetFineConfig ⟨q.x, q.ν⟩ := by
      have hne : (⟨shift q.x q.μ, q.ν⟩ : Link 2) ≠ ⟨0, 0⟩ := by
        intro h; injection h with _ hν; exact hν_ne hν
      have hcoord : (shift q.x q.μ) q.ν = q.x q.ν := by
        simp [shift, unitVec, ne_of_gt q.h]
      rw [hUW _ hne]
      simp [flatJSheetFineConfig, hcoord]
    have hlink4 : pythagoreanTubeFineConfig ⟨q.x, q.ν⟩ = flatJSheetFineConfig ⟨q.x, q.ν⟩ := by
      have hne : (⟨q.x, q.ν⟩ : Link 2) ≠ ⟨0, 0⟩ := by
        intro h; injection h with _ hν; exact hν_ne hν
      exact hUW _ hne
    by_cases hμ0 : q.μ = 0
    · have hf1 : flatJSheetFineConfig ⟨q.x, q.μ⟩ = 1 := by simp [flatJSheetFineConfig, hμ0]
      have hf3 : flatJSheetFineConfig ⟨shift q.x q.ν, q.μ⟩ = 1 := by simp [flatJSheetFineConfig, hμ0]
      by_cases hx0 : q.x = 0
      · have hl1 : pythagoreanTubeFineConfig ⟨q.x, q.μ⟩ = su2Pythagorean345 := by
          have heq : (⟨q.x, q.μ⟩ : Link 2) = ⟨0, 0⟩ := by rw [hx0, hμ0]
          rw [heq]
          exact (updateGaugeLink_same_and_other 2 flatJSheetFineConfig 0 0 su2Pythagorean345).1
        have hs_ne : (⟨shift q.x q.ν, q.μ⟩ : Link 2) ≠ ⟨0, 0⟩ := by
          intro h
          injection h with hs _
          have hcoord := congr_fun hs q.ν
          rw [hx0] at hcoord
          simp [shift, unitVec] at hcoord
        have hl3 : pythagoreanTubeFineConfig ⟨shift q.x q.ν, q.μ⟩ = 1 := by
          rw [hUW _ hs_ne, hf3]
        have hhol : plaquetteHolonomy pythagoreanTubeFineConfig q = su2Pythagorean345 := by
          dsimp [plaquetteHolonomy]
          rw [hl1, hlink2, hl3, hlink4]
          group
        dsimp [plaquetteAction]
        rw [hhol, hid.2.2.2.2.2.2.1]
        norm_num
      · have hl1_ne : (⟨q.x, q.μ⟩ : Link 2) ≠ ⟨0, 0⟩ := by
          intro h; injection h with hx _; exact hx0 hx
        have hl1 : pythagoreanTubeFineConfig ⟨q.x, q.μ⟩ = 1 := by
          rw [hUW _ hl1_ne, hf1]
        by_cases hs0 : shift q.x q.ν = 0
        · have hl3 : pythagoreanTubeFineConfig ⟨shift q.x q.ν, q.μ⟩ = su2Pythagorean345 := by
            have heq : (⟨shift q.x q.ν, q.μ⟩ : Link 2) = ⟨0, 0⟩ := by rw [hs0, hμ0]
            rw [heq]
            exact (updateGaugeLink_same_and_other 2 flatJSheetFineConfig 0 0 su2Pythagorean345).1
          have hhol :
              plaquetteHolonomy pythagoreanTubeFineConfig q =
                flatJSheetFineConfig ⟨q.x, q.ν⟩ * su2Pythagorean345⁻¹ *
                  (flatJSheetFineConfig ⟨q.x, q.ν⟩)⁻¹ := by
            dsimp [plaquetteHolonomy]
            rw [hl1, hlink2, hl3, hlink4]
            group
          dsimp [plaquetteAction]
          rw [hhol, SU2.trace_conj, hid.2.2.2.2.2.2.2.1]
          norm_num
        · have hl3_ne : (⟨shift q.x q.ν, q.μ⟩ : Link 2) ≠ ⟨0, 0⟩ := by
            intro h; injection h with hs _; exact hs0 hs
          have hl3 : pythagoreanTubeFineConfig ⟨shift q.x q.ν, q.μ⟩ = 1 := by
            rw [hUW _ hl3_ne, hf3]
          have hhol : plaquetteHolonomy pythagoreanTubeFineConfig q = 1 := by
            dsimp [plaquetteHolonomy]
            rw [hl1, hlink2, hl3, hlink4]
            group
          dsimp [plaquetteAction]
          rw [hhol, SU2.trace_one]
          norm_num
    · have hl1_ne : (⟨q.x, q.μ⟩ : Link 2) ≠ ⟨0, 0⟩ := by
        intro h; injection h with _ hμ; exact hμ0 hμ
      have hl3_ne : (⟨shift q.x q.ν, q.μ⟩ : Link 2) ≠ ⟨0, 0⟩ := by
        intro h; injection h with _ hμ; exact hμ0 hμ
      have hlink2_ne : (⟨shift q.x q.μ, q.ν⟩ : Link 2) ≠ ⟨0, 0⟩ := by
        intro h; injection h with _ hν; exact hν_ne hν
      have hlink4_ne : (⟨q.x, q.ν⟩ : Link 2) ≠ ⟨0, 0⟩ := by
        intro h; injection h with _ hν; exact hν_ne hν
      have h_eq : plaquetteAction pythagoreanTubeFineConfig q = plaquetteAction flatJSheetFineConfig q := by
        dsimp [plaquetteAction, plaquetteHolonomy]
        rw [hUW _ hl1_ne, hUW _ hlink2_ne, hUW _ hl3_ne, hUW _ hlink4_ne]
      rw [h_eq, h_flat_plaq q]
      norm_num
  have hS_pyth_fine : wilsonAction 1 pythagoreanTubeFineConfig ≤ 6 / 5 := by
    have hUW : ∀ f : Link 2, f ≠ ⟨0, 0⟩ → pythagoreanTubeFineConfig f = flatJSheetFineConfig f :=
      (updateGaugeLink_same_and_other 2 flatJSheetFineConfig 0 0 su2Pythagorean345).2
    have hsum :
        (∑ q : Plaquette 2, plaquetteAction pythagoreanTubeFineConfig q) =
          ∑ q ∈ incidentPlaquettes (⟨0, 0⟩ : Link 2), plaquetteAction pythagoreanTubeFineConfig q := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro q _ hq
      rw [plaquetteAction_eq_of_agree_off_link pythagoreanTubeFineConfig flatJSheetFineConfig
            ⟨0, 0⟩ hUW q hq, h_flat_plaq q]
    unfold wilsonAction
    rw [one_mul, hsum]
    calc
      (∑ q ∈ incidentPlaquettes (⟨0, 0⟩ : Link 2), plaquetteAction pythagoreanTubeFineConfig q) ≤
          ∑ _q ∈ incidentPlaquettes (⟨0, 0⟩ : Link 2), (1 / 5 : ℝ) :=
        Finset.sum_le_sum (fun q _ => h_pyth_plaq_le q)
      _ = (incidentPlaquettes (⟨0, 0⟩ : Link 2)).card * (1 / 5 : ℝ) := by simp
      _ ≤ 6 * (1 / 5 : ℝ) := by
        have hcard : ((incidentPlaquettes (⟨0, 0⟩ : Link 2)).card : ℝ) ≤ 6 := by
          exact_mod_cast incidentPlaquettes_card_le_six (⟨0, 0⟩ : Link 2)
        linarith
      _ = 6 / 5 := by ring
  have hI_pyth : haarFiberMinimumAction 1 pythagoreanCoarseWitness ≤ 6 / 5 :=
    le_trans
      ((haarFiberMinimumAction_spec_and_vacuum_zero 1 pythagoreanCoarseWitness).2.2.2.1
        pythagoreanTubeFineConfig h_block_pyth)
      hS_pyth_fine
  have hS_pyth_coarse : wilsonAction 1 pythagoreanCoarseWitness = 54 / 25 := by
    unfold wilsonAction
    rw [one_mul, sum_plaquette_one_eq]
    have hs : ∀ (x : Lattice4D 1) (μ : Direction), shift x μ = 0 :=
      fun x μ => Subsingleton.elim _ _
    have hUWc : ∀ f : Link 1, f ≠ ⟨0, 0⟩ → pythagoreanCoarseWitness f = flatJSheetCoarseConfig f :=
      (updateGaugeLink_same_and_other 1 flatJSheetCoarseConfig 0 0 su2Pythagorean345).2
    have h0 : pythagoreanCoarseWitness ⟨0, 0⟩ = su2Pythagorean345 :=
      (updateGaugeLink_same_and_other 1 flatJSheetCoarseConfig 0 0 su2Pythagorean345).1
    have h1 : pythagoreanCoarseWitness ⟨0, 1⟩ = su2PauliJ := by
      rw [hUWc ⟨0, 1⟩ (by decide)]
      simp [flatJSheetCoarseConfig]
    have h2 : pythagoreanCoarseWitness ⟨0, 2⟩ = su2PauliJ := by
      rw [hUWc ⟨0, 2⟩ (by decide)]
      simp [flatJSheetCoarseConfig]
    have h3 : pythagoreanCoarseWitness ⟨0, 3⟩ = su2PauliJ := by
      rw [hUWc ⟨0, 3⟩ (by decide)]
      simp [flatJSheetCoarseConfig]
    have hp01 : plaquetteAction pythagoreanCoarseWitness ⟨0, 0, 1, by decide⟩ = 18 / 25 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h0, h1, hid.2.2.2.2.1, hid.2.2.2.2.2.2.2.2]
      norm_num
    have hp02 : plaquetteAction pythagoreanCoarseWitness ⟨0, 0, 2, by decide⟩ = 18 / 25 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h0, h2, hid.2.2.2.2.1, hid.2.2.2.2.2.2.2.2]
      norm_num
    have hp03 : plaquetteAction pythagoreanCoarseWitness ⟨0, 0, 3, by decide⟩ = 18 / 25 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h0, h3, hid.2.2.2.2.1, hid.2.2.2.2.2.2.2.2]
      norm_num
    have hp12 : plaquetteAction pythagoreanCoarseWitness ⟨0, 1, 2, by decide⟩ = 0 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h1, h2]
      have hg : su2PauliJ * su2PauliJ * su2PauliJ⁻¹ * su2PauliJ⁻¹ = 1 := by group
      rw [hg, SU2.trace_one]; norm_num
    have hp13 : plaquetteAction pythagoreanCoarseWitness ⟨0, 1, 3, by decide⟩ = 0 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h1, h3]
      have hg : su2PauliJ * su2PauliJ * su2PauliJ⁻¹ * su2PauliJ⁻¹ = 1 := by group
      rw [hg, SU2.trace_one]; norm_num
    have hp23 : plaquetteAction pythagoreanCoarseWitness ⟨0, 2, 3, by decide⟩ = 0 := by
      dsimp [plaquetteAction, plaquetteHolonomy]
      rw [hs, hs, h2, h3]
      have hg : su2PauliJ * su2PauliJ * su2PauliJ⁻¹ * su2PauliJ⁻¹ = 1 := by group
      rw [hg, SU2.trace_one]; norm_num
    rw [hp01, hp02, hp03, hp12, hp13, hp23]
    ring
  have hJ_pyth :
      haarLeadingRemainderAction 1 (haarCanonicalNoncommutingProbe 1) pythagoreanCoarseWitness ≤
        -3 / 50 := by
    have hprobe_ratio := haarFiberMinimumAction_canonicalProbe_one_lower_bound.2.2
    dsimp [haarLeadingRemainderAction]
    rw [hS_pyth_coarse]
    linarith
  have hJ_pyth_ne :
      haarLeadingRemainderAction 1 (haarCanonicalNoncommutingProbe 1) pythagoreanCoarseWitness ≠ 0 := by
    linarith
  have hJ_pair_ne :
      haarLeadingRemainderAction 1 (haarCanonicalNoncommutingProbe 1)
          (updateGaugeLink 1 flatJSheetCoarseConfig 0 0 su2Pythagorean345) ≠
        haarLeadingRemainderAction 1 (haarCanonicalNoncommutingProbe 1)
          (updateGaugeLink 1 flatJSheetCoarseConfig 0 0 1) := by
    change haarLeadingRemainderAction 1 (haarCanonicalNoncommutingProbe 1) pythagoreanCoarseWitness ≠ _
    rw [h_upd_1, hJ_flat]
    exact hJ_pyth_ne
  refine ⟨⟨h_block_flat, h_block_pyth, h_upd_1, rfl⟩,
    ⟨hS_flat_fine, hI_flat, hS_flat_coarse, hJ_flat⟩,
    ⟨hS_pyth_fine, hI_pyth, hS_pyth_coarse⟩,
    ⟨hJ_pyth, hJ_pyth_ne, hJ_pair_ne⟩, ?_⟩
  constructor
  · rintro ⟨c, hc⟩
    have hvac_zero :
        ∀ β : ℝ,
          extractedCoarseRemainder ext0
            (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration 1) β)
            (vacuumConfig 1) = 0 :=
      fun β =>
        (effectiveActionDecomposition_unique_of_linearExtractor ext0
          (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration 1) β)).2.2.1
          (by dsimp [wilsonBlockedNormalizedEffectiveAction]; ring)
    have hbound :
        ∀ᶠ β : ℝ in atTop,
          |extractedCoarseRemainder ext0
              (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration 1) β)
              pythagoreanCoarseWitness -
            extractedCoarseRemainder ext0
              (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration 1) β)
              (vacuumConfig 1)| ≤ c / β := by
      filter_upwards [hc] with β hβ
      simpa [hvac_zero β] using hβ
    have heq :=
      (haarCanonicalProbeExtractedRemainder_oscillation_and_telescoped_chain_obstruction 1
        (haarCanonicalNoncommutingProbe 1) hP0).2.1 pythagoreanCoarseWitness (vacuumConfig 1) c hbound
    rw [(haarBlockedNormalizedEffectiveAction_and_canonicalProbe_div_beta_tendsto 1
          (haarCanonicalNoncommutingProbe 1) hP0 (vacuumConfig 1)).2.2.2.1] at heq
    exact hJ_pyth_ne heq
  · rintro ⟨c, hc⟩
    have hbound :
        ∀ᶠ β : ℝ in atTop,
          |extractedCoarseRemainder ext0
              (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration 1) β)
              (updateGaugeLink 1 flatJSheetCoarseConfig 0 0 su2Pythagorean345) -
            extractedCoarseRemainder ext0
              (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration 1) β)
              (updateGaugeLink 1 flatJSheetCoarseConfig 0 0 1)| ≤ c / β := by
      filter_upwards [hc] with β hβ
      exact hβ flatJSheetCoarseConfig 0 0 su2Pythagorean345 1
    have heq :=
      (haarCanonicalProbeExtractedRemainder_oscillation_and_telescoped_chain_obstruction 1
        (haarCanonicalNoncommutingProbe 1) hP0).2.1
        (updateGaugeLink 1 flatJSheetCoarseConfig 0 0 su2Pythagorean345)
        (updateGaugeLink 1 flatJSheetCoarseConfig 0 0 1) c hbound
    exact hJ_pair_ne heq

/-! ## Full-Leading-Action Fluctuation Remainder & Explicit Small-Field Fiber Domain -/

/-- The full-leading-action fluctuation remainder
`R_β(V) := A_β(V) - β * I_L(V)` on the actual Haar block disintegration
`haarBlockDisintegration L`, subtracting the exact classical fiber minimum action
`haarFiberMinimumAction L V` rather than a single-probe linear plaquette proxy. -/
noncomputable def haarFullLeadingFluctuationRemainder (L : ℕ) [NeZero L]
    (β : ℝ) (V : GaugeConfig L) : ℝ :=
  wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β V -
    β * haarFiberMinimumAction L V

/-- Explicit small-field fiber neighborhood `D_{L,V}(δ) ⊂ HaarFiberCoordinates L` where the fine
Wilson action excess `haarFiberActionEnergy L V r - haarFiberMinimumAction L V` above the classical
fiber minimum is strictly less than `δ`. -/
def haarSmallFieldFiberSublevel (L : ℕ) [NeZero L] (V : GaugeConfig L) (δ : ℝ) :
    Set (HaarFiberCoordinates L) :=
  {r : HaarFiberCoordinates L |
    haarFiberActionEnergy L V r - haarFiberMinimumAction L V < δ}

/-- Explicit large-field fiber complement `D_{L,V}(δ)^c ⊂ HaarFiberCoordinates L` where the fine
Wilson action excess above `haarFiberMinimumAction L V` is at least `δ`. -/
def haarLargeFieldFiberComplement (L : ℕ) [NeZero L] (V : GaugeConfig L) (δ : ℝ) :
    Set (HaarFiberCoordinates L) :=
  {r : HaarFiberCoordinates L |
    δ ≤ haarFiberActionEnergy L V r - haarFiberMinimumAction L V}

/-- Explicit gauge-fixed small-field transverse coercivity structure on `HaarFiberCoordinates L`
around an attained classical fiber minimizer `r_min`: records a nonnegative transverse squared
distance `transverseDistSq` vanishing at `r_min` and positive quadratic Hessian bounds
`κ_lo * transverseDistSq r ≤ S_1(U(V, r)) - I_L(V) ≤ κ_hi * transverseDistSq r` across the
small-field sublevel `haarSmallFieldFiberSublevel L V δ`. -/
structure HaarSmallFieldCoerciveGaugeSlice (L : ℕ) [NeZero L] (V : GaugeConfig L) where
  r_min : HaarFiberCoordinates L
  transverseDistSq : HaarFiberCoordinates L → ℝ
  κ_lo : ℝ
  κ_hi : ℝ
  δ : ℝ
  h_min : haarFiberActionEnergy L V r_min = haarFiberMinimumAction L V
  h_κ_lo_pos : 0 < κ_lo
  h_κ_lo_le_hi : κ_lo ≤ κ_hi
  h_δ_pos : 0 < δ
  h_dist_nonneg : ∀ r : HaarFiberCoordinates L, 0 ≤ transverseDistSq r
  h_dist_zero : transverseDistSq r_min = 0
  h_quadratic_sandwich :
    ∀ r ∈ haarSmallFieldFiberSublevel L V δ,
      κ_lo * transverseDistSq r ≤
        haarFiberActionEnergy L V r - haarFiberMinimumAction L V ∧
      haarFiberActionEnergy L V r - haarFiberMinimumAction L V ≤
        κ_hi * transverseDistSq r

/-- For every fixed lattice size `L ≥ 1` and coarse configuration `V : GaugeConfig L`, the
full-leading-action fluctuation remainder `haarFullLeadingFluctuationRemainder L β V` satisfies:
1. Exact decomposition `A_β(V) = β * I_L(V) + R_β(V)`,
2. Exact vacuum normalization `R_β(vacuumConfig L) = 0`, and
3. Sublinear weak-coupling asymptotic `R_β(V) / β → 0` as `β → ∞` for every coarse configuration
   `V : GaugeConfig L` (including `pythagoreanCoarseWitness` at `L = 1`, where the single-probe
   remainder had nonzero `O(β)` slope). Scope note: this is a fixed-`(L, V)` sublinear `o(β)`
   limit and does not by itself establish a uniform-in-`L` `O(1)` or `O(1 / β)` bound. -/
theorem haarFullLeadingFluctuationRemainder_vacuum_zero_and_div_beta_tendsto_zero
    (L : ℕ) [NeZero L] (V : GaugeConfig L) :
    (∀ β : ℝ,
      wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β V =
        β * haarFiberMinimumAction L V + haarFullLeadingFluctuationRemainder L β V) ∧
    (∀ β : ℝ,
      haarFullLeadingFluctuationRemainder L β (vacuumConfig L) = 0) ∧
    Tendsto
      (fun β : ℝ => haarFullLeadingFluctuationRemainder L β V / β)
      atTop (𝓝 0) := by
  have hI_vac : haarFiberMinimumAction L (vacuumConfig L) = 0 :=
    (haarFiberMinimumAction_spec_and_vacuum_zero L (vacuumConfig L)).2.2.2.2
  refine ⟨fun β => ?_, fun β => ?_, ?_⟩
  · dsimp [haarFullLeadingFluctuationRemainder]
    ring
  · dsimp [haarFullLeadingFluctuationRemainder, wilsonBlockedNormalizedEffectiveAction]
    rw [hI_vac]
    ring
  · have hW := haarBlockedFiberWeight_neg_log_div_beta_tendsto L V
    have hvac := haarBlockedFiberWeight_neg_log_div_beta_tendsto L (vacuumConfig L)
    rw [hI_vac] at hvac
    have hA :
        Tendsto
          (fun β : ℝ =>
            wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β V / β)
          atTop (𝓝 (haarFiberMinimumAction L V)) := by
      have hsub := hW.sub hvac
      rw [sub_zero] at hsub
      refine hsub.congr (fun β => ?_)
      dsimp [wilsonBlockedNormalizedEffectiveAction, wilsonBlockedEffectiveAction]
      ring
    have hrem :
        Tendsto
          (fun β : ℝ =>
            wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β V / β -
              haarFiberMinimumAction L V)
          atTop (𝓝 0) := by
      simpa [sub_self] using hA.sub (tendsto_const_nhds (x := haarFiberMinimumAction L V))
    refine hrem.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    dsimp [haarFullLeadingFluctuationRemainder]
    calc
      wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β V / β -
          haarFiberMinimumAction L V
        = wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β V / β -
            (β / β) * haarFiberMinimumAction L V := by
          rw [div_self (ne_of_gt hβ), one_mul]
      _ = (wilsonBlockedNormalizedEffectiveAction (haarBlockDisintegration L) β V -
            β * haarFiberMinimumAction L V) / β := by
          ring

/-- Explicit small-field / large-field decomposition on `HaarFiberCoordinates L`:
1. `haarSmallFieldFiberSublevel L V δ` and `haarLargeFieldFiberComplement L V δ` form a disjoint
   measurable partition of `Set.univ : Set (HaarFiberCoordinates L)`,
2. For every `δ > 0`, `haarSmallFieldFiberSublevel L V δ` is open, contains a classical fiber
   minimizer, and has strictly positive Haar reference measure
   `0 < (haarFiberReference L).real (haarSmallFieldFiberSublevel L V δ)`,
3. On the large-field complement `r ∈ haarLargeFieldFiberComplement L V δ`, for every `β ≥ 0` the
   fine Boltzmann weight is exponentially damped relative to the classical fiber minimum by
   `Real.exp (-wilsonAction β (haarFiberReconstruction L V r)) ≤ Real.exp (-(β * haarFiberMinimumAction L V)) * Real.exp (-(β * δ))`, and
4. Given any `slice : HaarSmallFieldCoerciveGaugeSlice L V`, every `r ∈ haarSmallFieldFiberSublevel L V slice.δ`
   has transverse squared distance bounded by `slice.transverseDistSq r < slice.δ / slice.κ_lo`. -/
theorem haarSmallFieldFiberSublevel_partition_pos_measure_and_largeField_damping
    (L : ℕ) [NeZero L] (V : GaugeConfig L) {δ : ℝ} (hδ : 0 < δ) :
    (haarSmallFieldFiberSublevel L V δ ∪ haarLargeFieldFiberComplement L V δ = Set.univ ∧
      Disjoint (haarSmallFieldFiberSublevel L V δ) (haarLargeFieldFiberComplement L V δ)) ∧
    (IsOpen (haarSmallFieldFiberSublevel L V δ) ∧
      0 < (haarFiberReference L).real (haarSmallFieldFiberSublevel L V δ)) ∧
    (∀ {β : ℝ}, 0 ≤ β → ∀ r ∈ haarLargeFieldFiberComplement L V δ,
      Real.exp (-wilsonAction β (haarFiberReconstruction L V r)) ≤
        Real.exp (-(β * haarFiberMinimumAction L V)) * Real.exp (-(β * δ))) ∧
    (∀ (slice : HaarSmallFieldCoerciveGaugeSlice L V)
      (r : HaarFiberCoordinates L),
      r ∈ haarSmallFieldFiberSublevel L V slice.δ →
      slice.transverseDistSq r < slice.δ / slice.κ_lo) := by
  have h_union :
      haarSmallFieldFiberSublevel L V δ ∪ haarLargeFieldFiberComplement L V δ = Set.univ := by
    ext r
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    change haarFiberActionEnergy L V r - haarFiberMinimumAction L V < δ ∨
      δ ≤ haarFiberActionEnergy L V r - haarFiberMinimumAction L V
    by_cases h : haarFiberActionEnergy L V r - haarFiberMinimumAction L V < δ
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have h_disjoint :
      Disjoint (haarSmallFieldFiberSublevel L V δ) (haarLargeFieldFiberComplement L V δ) := by
    rw [Set.disjoint_left]
    intro r hr1 hr2
    change haarFiberActionEnergy L V r - haarFiberMinimumAction L V < δ at hr1
    change δ ≤ haarFiberActionEnergy L V r - haarFiberMinimumAction L V at hr2
    linarith
  have h_cont : Continuous (haarFiberActionEnergy L V) :=
    (continuous_wilsonAction (L := 2 * L) 1).comp (continuous_haarFiberReconstruction L V)
  have h_open : IsOpen (haarSmallFieldFiberSublevel L V δ) :=
    isOpen_lt (h_cont.sub continuous_const) continuous_const
  have h_spec := haarFiberMinimumAction_spec_and_vacuum_zero L V
  rcases h_spec.2.1 with ⟨r_min, hr_min⟩
  have h_nonempty : (haarSmallFieldFiberSublevel L V δ).Nonempty :=
    ⟨r_min, by simp [haarSmallFieldFiberSublevel, hr_min, hδ]⟩
  have h_meas_pos : 0 < (haarFiberReference L).real (haarSmallFieldFiberSublevel L V δ) :=
    ENNReal.toReal_pos (ne_of_gt (h_open.measure_pos (haarFiberReference L) h_nonempty))
      (measure_ne_top _ _)
  refine ⟨⟨h_union, h_disjoint⟩, ⟨h_open, h_meas_pos⟩, ?_, ?_⟩
  · intro β hβ r hr
    have h_act :
        haarFiberMinimumAction L V + δ ≤ wilsonAction 1 (haarFiberReconstruction L V r) := by
      change δ ≤ wilsonAction 1 (haarFiberReconstruction L V r) - haarFiberMinimumAction L V at hr
      linarith
    have h_mul :
        β * (haarFiberMinimumAction L V + δ) ≤
          β * wilsonAction 1 (haarFiberReconstruction L V r) :=
      mul_le_mul_of_nonneg_left h_act hβ
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [wilsonAction_eq_beta_mul_wilsonAction_one]
    linarith [show β * (haarFiberMinimumAction L V + δ) =
      β * haarFiberMinimumAction L V + β * δ by ring]
  · intro slice r hr
    have h_lo := (slice.h_quadratic_sandwich r hr).1
    have hr_lt : haarFiberActionEnergy L V r - haarFiberMinimumAction L V < slice.δ := hr
    rw [lt_div_iff₀ slice.h_κ_lo_pos]
    linarith [show slice.transverseDistSq r * slice.κ_lo =
      slice.κ_lo * slice.transverseDistSq r by ring]

/-! ## General Compact Gauge Group Dyadic Block Map & Haar Fiber Disintegration Kernel -/

/-- Dyadic fine-to-coarse ordered link multiplication map `GroupGaugeConfig G (2 * L) → GroupGaugeConfig G L`
for an arbitrary gauge group `G`, assigning to each coarse link `e : Link L` the product of its two
disjoint fine links `U (dyadicFineLink L (e, 0)) * U (dyadicFineLink L (e, 1))`. -/
noncomputable def groupDyadicLinkBlockMap (G : Type*) [Group G] [MeasurableSpace G]
    (L : ℕ) [NeZero L] :
    GroupGaugeConfig G (2 * L) → GroupGaugeConfig G L :=
  finitePairBlock (G := G) (dyadicFineLinkEquiv L)

/-- Conditional Haar fiber disintegration Markov kernel `Kernel (GroupGaugeConfig G L) (GroupGaugeConfig G (2 * L))`
for any compact Hausdorff topological group `G`, sampling the first link of each dyadic pair and
each unused fine link independently from `compactGroupHaarProbability G` and setting the second link
to `h⁻¹ * V e`. -/
noncomputable def groupHaarBlockKernel (G : Type*) [Group G] [TopologicalSpace G]
    [SecondCountableTopology G] [IsTopologicalGroup G] [T2Space G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] : Kernel (GroupGaugeConfig G L) (GroupGaugeConfig G (2 * L)) :=
  finitePairKernel (compactGroupHaarProbability G) (dyadicFineLinkEquiv L)

instance (G : Type*) [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] : IsMarkovKernel (groupHaarBlockKernel G L) := by
  change IsMarkovKernel (finitePairKernel (I := Link L) (J := unusedFineLinks L)
    (F := Link (2 * L)) (G := G) (compactGroupHaarProbability G) (dyadicFineLinkEquiv L))
  infer_instance

/-- Exact dyadic Haar block disintegration for every compact Hausdorff second-countable topological
gauge group `G` and every lattice size `L ≥ 1`:
1. `groupDyadicLinkBlockMap G L` is measurable,
2. For every coarse configuration `V : GroupGaugeConfig G L`, `groupHaarBlockKernel G L V` is
   almost everywhere supported on the exact geometric fiber `{U | groupDyadicLinkBlockMap G L U = V}`,
3. The pushforward of fine product Haar `groupGaugeHaarMeasure G (2 * L)` under
   `groupDyadicLinkBlockMap G L` is coarse product Haar `groupGaugeHaarMeasure G L`,
4. The composition-product `groupGaugeHaarMeasure G L ⊗ₘ groupHaarBlockKernel G L` equals the graph
   pushforward `(groupGaugeHaarMeasure G (2 * L)).map (fun U => (groupDyadicLinkBlockMap G L U, U))`, and
5. At `G = SU2`, `groupDyadicLinkBlockMap SU2 L`, `groupHaarBlockKernel SU2 L`,
   `groupWilsonPartitionFunction SU2 L su2CompactGaugeClassTrace β`, and
   `groupWilsonMeasure SU2 L su2CompactGaugeClassTrace β` coincide identically with
   `dyadicLinkBlockMap L`, `haarBlockKernel L`, `wilsonPartition (gaugeHaarMeasure L) β`, and
   `wilsonMeasure (gaugeHaarMeasure L) β`. -/
theorem groupHaarBlockKernel_disintegration_and_su2_parity
    (G : Type*) [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] (β : ℝ) :
    Measurable (groupDyadicLinkBlockMap G L) ∧
    (∀ V : GroupGaugeConfig G L,
      ∀ᵐ U ∂groupHaarBlockKernel G L V, groupDyadicLinkBlockMap G L U = V) ∧
    ((groupGaugeHaarMeasure G (2 * L)).map (groupDyadicLinkBlockMap G L) =
      groupGaugeHaarMeasure G L) ∧
    (groupGaugeHaarMeasure G L ⊗ₘ groupHaarBlockKernel G L =
      (groupGaugeHaarMeasure G (2 * L)).map (fun U => (groupDyadicLinkBlockMap G L U, U))) ∧
    (groupDyadicLinkBlockMap SU2 L = dyadicLinkBlockMap L ∧
      groupHaarBlockKernel SU2 L = haarBlockKernel L ∧
      groupWilsonPartitionFunction SU2 L su2CompactGaugeClassTrace β =
        wilsonPartition (gaugeHaarMeasure L) β ∧
      groupWilsonMeasure SU2 L su2CompactGaugeClassTrace β =
        wilsonMeasure (gaugeHaarMeasure L) β) := by
  refine ⟨measurable_finitePairBlock (dyadicFineLinkEquiv L),
    fun V => finitePairKernel_supported (compactGroupHaarProbability G) (dyadicFineLinkEquiv L) V,
    finitePairBlock_map (compactGroupHaarProbability G) (dyadicFineLinkEquiv L),
    finitePairKernel_graph (compactGroupHaarProbability G) (dyadicFineLinkEquiv L),
    ⟨finitePairBlock_eq_dyadicLinkBlockMap L, rfl, rfl, rfl⟩⟩

/-! ## Abstract Smoothing Block Maps, Gradient Flow RG Step, and Dobrushin–Shlosman Crossover -/

/-- Abstract smoothing or decimation block-map disintegration from a fine lattice `L_fine` to a
coarse lattice `L_coarse` for a compact Hausdorff topological gauge group `G`, packaging the
block map `blockMap`, conditional Markov fiber kernel `fiberKernel`, measurability of `blockMap`,
almost-everywhere support of `fiberKernel V` on `{U | blockMap U = V}`, and exact product-Haar
pushforward `(groupGaugeHaarMeasure G L_fine).map blockMap = groupGaugeHaarMeasure G L_coarse`. -/
structure AbstractBlockMapDisintegration (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L_fine L_coarse : ℕ) [NeZero L_fine] [NeZero L_coarse] where
  blockMap : GroupGaugeConfig G L_fine → GroupGaugeConfig G L_coarse
  fiberKernel : Kernel (GroupGaugeConfig G L_coarse) (GroupGaugeConfig G L_fine)
  [isMarkov : IsMarkovKernel fiberKernel]
  h_measurable : Measurable blockMap
  h_supported : ∀ V : GroupGaugeConfig G L_coarse, ∀ᵐ U ∂fiberKernel V, blockMap U = V
  h_pushforward : (groupGaugeHaarMeasure G L_fine).map blockMap = groupGaugeHaarMeasure G L_coarse

attribute [instance] AbstractBlockMapDisintegration.isMarkov

/-- Canonical dyadic instantiation of `AbstractBlockMapDisintegration G (2 * L) L` via
`groupDyadicLinkBlockMap G L` and `groupHaarBlockKernel G L`. -/
noncomputable def dyadicAbstractBlockMapDisintegration (G : Type*) [Group G]
    [TopologicalSpace G] [SecondCountableTopology G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] : AbstractBlockMapDisintegration G (2 * L) L where
  blockMap := groupDyadicLinkBlockMap G L
  fiberKernel := groupHaarBlockKernel G L
  isMarkov := inferInstance
  h_measurable := measurable_finitePairBlock (dyadicFineLinkEquiv L)
  h_supported V := finitePairKernel_supported (compactGroupHaarProbability G) (dyadicFineLinkEquiv L) V
  h_pushforward := finitePairBlock_map (compactGroupHaarProbability G) (dyadicFineLinkEquiv L)

/-- Gradient-flow / heat-kernel / stout-smearing smoothing block map extending
`AbstractBlockMapDisintegration G L_fine L_coarse` with a strictly positive physical flow time
`t_flow > 0` and gauge covariance under lifted coarse gauge transformations. -/
structure GradientFlowSmoothingBlockMap (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L_fine L_coarse : ℕ) [NeZero L_fine] [NeZero L_coarse]
    extends AbstractBlockMapDisintegration G L_fine L_coarse where
  t_flow : ℝ
  h_t_flow_pos : 0 < t_flow
  coarseGaugeLift : GroupGaugeTransformation G L_coarse → GroupGaugeTransformation G L_fine
  h_gauge_covariant :
    ∀ (g : GroupGaugeTransformation G L_coarse) (U : GroupGaugeConfig G L_fine),
      blockMap (groupGaugeTransform (coarseGaugeLift g) U) =
        groupGaugeTransform g (blockMap U)

/-- Every `GradientFlowSmoothingBlockMap G L_fine L_coarse` has strictly positive smoothing flow
time `0 < S.t_flow` and pulls back every coarse gauge-invariant observable
`F : GroupGaugeConfig G L_coarse → ℝ` to a fine observable invariant under
`groupGaugeTransform (S.coarseGaugeLift g)`. -/
theorem gradientFlowSmoothingBlockMap_pullback_gauge_invariant
    {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L_fine L_coarse : ℕ} [NeZero L_fine] [NeZero L_coarse]
    (S : GradientFlowSmoothingBlockMap G L_fine L_coarse)
    (F : GroupGaugeConfig G L_coarse → ℝ)
    (hF_inv : ∀ (g : GroupGaugeTransformation G L_coarse) (V : GroupGaugeConfig G L_coarse),
      F (groupGaugeTransform g V) = F V)
    (g : GroupGaugeTransformation G L_coarse) (U : GroupGaugeConfig G L_fine) :
    0 < S.t_flow ∧
    F (S.blockMap (groupGaugeTransform (S.coarseGaugeLift g) U)) = F (S.blockMap U) := by
  refine ⟨S.h_t_flow_pos, ?_⟩
  rw [S.h_gauge_covariant g U, hF_inv g (S.blockMap U)]

/-- Blocked conditional fiber Boltzmann weight
`W_D(S_fine, V) := ∫ U, exp(-S_fine U) ∂(D.fiberKernel V)` for an arbitrary
`D : AbstractBlockMapDisintegration G L_fine L_coarse` and fine action `S_fine`. -/
noncomputable def abstractBlockedFiberWeight
    {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L_fine L_coarse : ℕ} [NeZero L_fine] [NeZero L_coarse]
    (D : AbstractBlockMapDisintegration G L_fine L_coarse)
    (S_fine : GroupGaugeConfig G L_fine → ℝ) (V : GroupGaugeConfig G L_coarse) : ℝ :=
  ∫ U, Real.exp (-S_fine U) ∂(D.fiberKernel V)

/-- Blocked coarse effective action `A_D(S_fine, V) := -log W_D(S_fine, V)` for an arbitrary
`D : AbstractBlockMapDisintegration G L_fine L_coarse` and fine action `S_fine`. -/
noncomputable def abstractBlockedEffectiveAction
    {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L_fine L_coarse : ℕ} [NeZero L_fine] [NeZero L_coarse]
    (D : AbstractBlockMapDisintegration G L_fine L_coarse)
    (S_fine : GroupGaugeConfig G L_fine → ℝ) (V : GroupGaugeConfig G L_coarse) : ℝ :=
  -Real.log (abstractBlockedFiberWeight D S_fine V)

/-- Exact 1-step sandwich and monotonicity lemma for `abstractBlockedFiberWeight`: whenever a fine
action `S_fine` is approximated within `ε` by a decomposed fine action `S_0 + K_rem` across
`GroupGaugeConfig G L_fine`, the conditional fiber weight `abstractBlockedFiberWeight D S_fine V`
is sandwiched between `exp(-ε)` and `exp(ε)` times
`abstractBlockedFiberWeight D (fun U => S_0 U + K_rem U) V`. -/
theorem abstractBlockedFiberWeight_sandwich
    {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L_fine L_coarse : ℕ} [NeZero L_fine] [NeZero L_coarse]
    (D : AbstractBlockMapDisintegration G L_fine L_coarse)
    (S_fine S_0 K_rem : GroupGaugeConfig G L_fine → ℝ)
    (V : GroupGaugeConfig G L_coarse) {ε : ℝ}
    (h_int_0 : Integrable (fun U => Real.exp (-(S_0 U + K_rem U))) (D.fiberKernel V))
    (h_int_fine : Integrable (fun U => Real.exp (-S_fine U)) (D.fiberKernel V))
    (h_approx : ∀ U : GroupGaugeConfig G L_fine, |S_fine U - (S_0 U + K_rem U)| ≤ ε) :
    Real.exp (-ε) * abstractBlockedFiberWeight D (fun U => S_0 U + K_rem U) V ≤
      abstractBlockedFiberWeight D S_fine V ∧
    abstractBlockedFiberWeight D S_fine V ≤
      Real.exp ε * abstractBlockedFiberWeight D (fun U => S_0 U + K_rem U) V := by
  unfold abstractBlockedFiberWeight
  constructor
  · rw [← integral_const_mul]
    apply integral_mono (h_int_0.const_mul (Real.exp (-ε))) h_int_fine
    intro U
    dsimp only
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hU := (abs_le.mp (h_approx U)).2
    linarith
  · rw [← integral_const_mul]
    apply integral_mono h_int_fine (h_int_0.const_mul (Real.exp ε))
    intro U
    dsimp only
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hU := (abs_le.mp (h_approx U)).1
    linarith

/-- Balaban's small-field local-axial-gauge background and Gaussian fluctuation Laplacian
covariance decomposition on `GaugeConfig L`, packaging the background field configuration
`backgroundField`, quadratic fluctuation covariance form `fluctuationLaplacianQuadForm`,
nonlocal polymer remainder `K_polymer`, polymer norm `polymerNorm`, decay rate `κ > 0`, and
analytic polymer norm bound `polymerNorm ≤ Real.exp (-κ)`. -/
structure SmallFieldPolymerDecomposition (L : ℕ) [NeZero L] where
  backgroundField : GaugeConfig L → GaugeConfig L
  fluctuationLaplacianQuadForm : GaugeConfig L → ℝ
  K_polymer : GaugeConfig L → ℝ
  polymerNorm : ℝ
  κ : ℝ
  h_κ_pos : 0 < κ
  h_quad_nonneg : ∀ V : GaugeConfig L, 0 ≤ fluctuationLaplacianQuadForm V
  h_pointwise_le_norm : ∀ V : GaugeConfig L, |K_polymer V| ≤ polymerNorm
  h_polymer_norm_bound : polymerNorm ≤ Real.exp (-κ)

/-- Peierls-type large-field action-excess suppression on `GaugeConfig L`, packaging the running
squared coupling `g_sq > 0`, Peierls exponent function `p_peierls : ℝ → ℝ` with
`0 < p_peierls g_sq`, and large-field weight bound `≤ Real.exp (-p_peierls g_sq)`. -/
structure LargeFieldPeierlsSuppression (L : ℕ) [NeZero L] where
  g_sq : ℝ
  p_peierls : ℝ → ℝ
  largeFieldWeight : GaugeConfig L → ℝ
  h_g_sq_pos : 0 < g_sq
  h_peierls_pos : 0 < p_peierls g_sq
  h_weight_nonneg : ∀ V : GaugeConfig L, 0 ≤ largeFieldWeight V
  h_peierls_bound : ∀ V : GaugeConfig L, largeFieldWeight V ≤ Real.exp (-p_peierls g_sq)

/-- Exponential damping bounds for any `SmallFieldPolymerDecomposition L` and
`LargeFieldPeierlsSuppression L` on `GaugeConfig L`: both the small-field polymer remainder norm
`Real.exp (-decomp.κ)` and the large-field Peierls bound `Real.exp (-peierls.p_peierls peierls.g_sq)`
are strictly less than `1`. -/
theorem smallFieldPolymer_and_largeFieldPeierls_exponential_damping
    {L : ℕ} [NeZero L]
    (decomp : SmallFieldPolymerDecomposition L)
    (peierls : LargeFieldPeierlsSuppression L)
    (V : GaugeConfig L) :
    |decomp.K_polymer V| ≤ Real.exp (-decomp.κ) ∧
    Real.exp (-decomp.κ) < 1 ∧
    0 ≤ peierls.largeFieldWeight V ∧
    peierls.largeFieldWeight V ≤ Real.exp (-peierls.p_peierls peierls.g_sq) ∧
    Real.exp (-peierls.p_peierls peierls.g_sq) < 1 := by
  have h_k : |decomp.K_polymer V| ≤ Real.exp (-decomp.κ) :=
    le_trans (decomp.h_pointwise_le_norm V) decomp.h_polymer_norm_bound
  have h_exp_k : Real.exp (-decomp.κ) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith [decomp.h_κ_pos])
  have h_exp_p : Real.exp (-peierls.p_peierls peierls.g_sq) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith [peierls.h_peierls_pos])
  exact ⟨h_k, h_exp_k, peierls.h_weight_nonneg V, peierls.h_peierls_bound V, h_exp_p⟩

/-- Computer-assisted interval-arithmetic Dobrushin–Shlosman finite-block crossover certificate at
intermediate coupling `β_K = O(1)` on a finite block `L_block`: records the crossover coupling
`β_K`, character-expansion truncation order `N_char : ℕ`, interval enclosure bound `r_interval`,
and rigorous character-expansion tail bound `ε_tail` satisfying `0 ≤ r_interval`, `0 ≤ ε_tail`,
and `r_interval + ε_tail < 1`. -/
structure DobrushinShlosmanFiniteBlockCertificate (L_block : ℕ) [NeZero L_block] where
  β_K : ℝ
  N_char : ℕ
  r_interval : ℝ
  ε_tail : ℝ
  h_β_K_pos : 0 < β_K
  h_r_nonneg : 0 ≤ r_interval
  h_tail_nonneg : 0 ≤ ε_tail
  h_contraction : r_interval + ε_tail < 1

/-- Every valid `DobrushinShlosmanFiniteBlockCertificate L_block` has a nonnegative total influence
rate `0 ≤ cert.r_interval + cert.ε_tail < 1` and a strictly positive contraction margin
`0 < 1 - (cert.r_interval + cert.ε_tail)`. -/
theorem dobrushinShlosmanCertificate_contraction_lt_one
    {L_block : ℕ} [NeZero L_block]
    (cert : DobrushinShlosmanFiniteBlockCertificate L_block) :
    0 ≤ cert.r_interval + cert.ε_tail ∧
    cert.r_interval + cert.ε_tail < 1 ∧
    0 < 1 - (cert.r_interval + cert.ε_tail) := by
  have h_nonneg : 0 ≤ cert.r_interval + cert.ε_tail := add_nonneg cert.h_r_nonneg cert.h_tail_nonneg
  have h_lt : cert.r_interval + cert.ε_tail < 1 := cert.h_contraction
  exact ⟨h_nonneg, h_lt, sub_pos.mpr h_lt⟩

/-- Volume-uniform Dobrushin Neumann-series geometric summability and exponential covariance-bound
decay across all torus sizes `L`: for any compact-spin Dobrushin row-sum rate
`r = 18 * β_star + η_star` with `0 ≤ β_star`, `0 ≤ η_star`, and `18 * β_star + η_star < 1`,
the geometric Neumann series `∑_{t ≥ 0} (18 * β_star + η_star)^t` is summable with exact sum
`(1 - (18 * β_star + η_star))⁻¹ > 0`, and for any observables with single-site oscillations bounded
by `M_f, M_g ≥ 0`, the distance-`d` covariance envelope
`M_f * M_g * (1 - (18 * β_star + η_star))⁻¹ * (18 * β_star + η_star) ^ d` is nonnegative and tends
to `0` exponentially as `d → ∞` uniformly in the torus side `L`. -/
theorem dobrushinNeumannSeries_cov_bound_uniform_in_L
    {β_star η_star M_f M_g : ℝ}
    (hβ_star : 0 ≤ β_star) (hη_star : 0 ≤ η_star)
    (h_contract : 18 * β_star + η_star < 1)
    (hM_f : 0 ≤ M_f) (hM_g : 0 ≤ M_g) :
    Summable (fun t : ℕ => (18 * β_star + η_star) ^ t) ∧
    (∑' t : ℕ, (18 * β_star + η_star) ^ t) = (1 - (18 * β_star + η_star))⁻¹ ∧
    0 < (1 - (18 * β_star + η_star))⁻¹ ∧
    (∀ (_L : ℕ) (d : ℕ),
      0 ≤ M_f * M_g * (1 - (18 * β_star + η_star))⁻¹ * (18 * β_star + η_star) ^ d) ∧
    (∀ (_L : ℕ),
      Tendsto
        (fun d : ℕ =>
          M_f * M_g * (1 - (18 * β_star + η_star))⁻¹ * (18 * β_star + η_star) ^ d)
        atTop (𝓝 0)) := by
  have hr_nonneg : 0 ≤ 18 * β_star + η_star := by linarith
  have h_sum : Summable (fun t : ℕ => (18 * β_star + η_star) ^ t) :=
    summable_geometric_of_lt_one hr_nonneg h_contract
  have h_tsum : (∑' t : ℕ, (18 * β_star + η_star) ^ t) = (1 - (18 * β_star + η_star))⁻¹ :=
    tsum_geometric_of_lt_one hr_nonneg h_contract
  have h_inv_pos : 0 < (1 - (18 * β_star + η_star))⁻¹ :=
    inv_pos.mpr (by linarith)
  have h_pow_tendsto : Tendsto (fun d : ℕ => (18 * β_star + η_star) ^ d) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg h_contract
  refine ⟨h_sum, h_tsum, h_inv_pos, ?_, ?_⟩
  · intro _ d
    exact mul_nonneg (mul_nonneg (mul_nonneg hM_f hM_g) h_inv_pos.le)
      (pow_nonneg hr_nonneg d)
  · intro _
    simpa using (tendsto_const_nhds (x := M_f * M_g * (1 - (18 * β_star + η_star))⁻¹)).mul h_pow_tendsto

/-! ## Zero-Coupling (`β = 0`) Wilson Measure Identities & General-Group Dobrushin Row-Sum Bounds -/

/-- At zero coupling (`β = 0`), the `SU(2)` Wilson action vanishes identically on `GaugeConfig L`. -/
theorem wilsonAction_zero {L : ℕ} [NeZero L] (U : GaugeConfig L) :
    wilsonAction 0 U = 0 := by
  simp [wilsonAction]

/-- At zero coupling (`β = 0`), the `SU(2)` Boltzmann weight equals `1` on `GaugeConfig L`. -/
theorem boltzmannWeight_zero {L : ℕ} [NeZero L] (U : GaugeConfig L) :
    boltzmannWeight 0 U = 1 := by
  simp [boltzmannWeight, wilsonAction]

/-- At zero coupling (`β = 0`), the `SU(2)` Wilson partition function of any probability measure `μ`
equals `1`. -/
theorem wilsonPartition_zero {L : ℕ} [NeZero L]
    (μ : Measure (GaugeConfig L)) [IsProbabilityMeasure μ] :
    wilsonPartition μ 0 = 1 := by
  simp [wilsonPartition, boltzmannWeight, wilsonAction]

/-- At zero coupling (`β = 0`), the `SU(2)` Wilson measure coincides with the reference probability
measure `μ`. -/
theorem wilsonMeasure_zero {L : ℕ} [NeZero L]
    (μ : Measure (GaugeConfig L)) [IsProbabilityMeasure μ] :
    wilsonMeasure μ 0 = μ := by
  simp [wilsonMeasure, wilsonPartition, boltzmannWeight, wilsonAction]

/-- At zero coupling (`β = 0`), the general-group Wilson action vanishes identically on
`GroupGaugeConfig G L`. -/
theorem groupWilsonAction_zero {G : Type*} [Group G] [TopologicalSpace G]
    {L : ℕ} [NeZero L] (tr : CompactGaugeClassTrace G) (U : GroupGaugeConfig G L) :
    groupWilsonAction tr 0 U = 0 := by
  simp [groupWilsonAction]

/-- At zero coupling (`β = 0`), the general-group Boltzmann weight equals `1` on
`GroupGaugeConfig G L`. -/
theorem groupBoltzmannWeight_zero {G : Type*} [Group G] [TopologicalSpace G]
    {L : ℕ} [NeZero L] (tr : CompactGaugeClassTrace G) (U : GroupGaugeConfig G L) :
    groupBoltzmannWeight tr 0 U = 1 := by
  simp [groupBoltzmannWeight, groupWilsonAction]

/-- At zero coupling (`β = 0`), the general-group Wilson partition function equals `1`. -/
theorem groupWilsonPartitionFunction_zero (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] (tr : CompactGaugeClassTrace G) :
    groupWilsonPartitionFunction G L tr 0 = 1 := by
  simp [groupWilsonPartitionFunction, groupBoltzmannWeight, groupWilsonAction]

/-- At zero coupling (`β = 0`), the general-group Wilson measure coincides with the product Haar
probability measure `groupGaugeHaarMeasure G L`. -/
theorem groupWilsonMeasure_zero (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] (tr : CompactGaugeClassTrace G) :
    groupWilsonMeasure G L tr 0 = groupGaugeHaarMeasure G L := by
  simp [groupWilsonMeasure, groupWilsonPartitionFunction, groupBoltzmannWeight, groupWilsonAction]

/-- Tight single-plaquette two-link mixed second-difference bound: for every plaquette `p : Plaquette L`,
because `0 ≤ plaquetteAction U p ≤ 2` on every configuration `U`, the two-link mixed second
difference of `fun U => plaquetteAction U p` is bounded in absolute value by `4`. -/
theorem twoLinkMixedDifference_plaquetteAction_abs_le_four
    {L : ℕ} (p : Plaquette L) (V : GaugeConfig L)
    (x1 : Lattice4D L) (μ1 : Fin 4) (g1 g2 : SU2)
    (x2 : Lattice4D L) (μ2 : Fin 4) (h1 h2 : SU2) :
    |twoLinkMixedDifference L (fun U => plaquetteAction U p) V x1 μ1 g1 g2 x2 μ2 h1 h2| ≤ 4 := by
  have h11_lo := plaquetteAction_nonneg (updateTwoGaugeLinks L V x1 μ1 g1 x2 μ2 h1) p
  have h11_hi := plaquetteAction_le_two (updateTwoGaugeLinks L V x1 μ1 g1 x2 μ2 h1) p
  have h21_lo := plaquetteAction_nonneg (updateTwoGaugeLinks L V x1 μ1 g2 x2 μ2 h1) p
  have h21_hi := plaquetteAction_le_two (updateTwoGaugeLinks L V x1 μ1 g2 x2 μ2 h1) p
  have h12_lo := plaquetteAction_nonneg (updateTwoGaugeLinks L V x1 μ1 g1 x2 μ2 h2) p
  have h12_hi := plaquetteAction_le_two (updateTwoGaugeLinks L V x1 μ1 g1 x2 μ2 h2) p
  have h22_lo := plaquetteAction_nonneg (updateTwoGaugeLinks L V x1 μ1 g2 x2 μ2 h2) p
  have h22_hi := plaquetteAction_le_two (updateTwoGaugeLinks L V x1 μ1 g2 x2 μ2 h2) p
  dsimp [twoLinkMixedDifference]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Single-link gauge configuration update on `GroupGaugeConfig G L` for an arbitrary gauge group `G`. -/
def updateGroupGaugeLink {G : Type*} (L : ℕ) (V : GroupGaugeConfig G L)
    (x : Lattice4D L) (μ : Fin 4) (g : G) : GroupGaugeConfig G L :=
  Function.update V ⟨x, μ⟩ g

/-- Evaluation of `updateGroupGaugeLink L V x μ g` at the updated link `⟨x, μ⟩` and at any distinct
link `e ≠ ⟨x, μ⟩`. -/
theorem updateGroupGaugeLink_same_and_other {G : Type*}
    (L : ℕ) (V : GroupGaugeConfig G L) (x : Lattice4D L) (μ : Fin 4) (g : G) :
    updateGroupGaugeLink L V x μ g ⟨x, μ⟩ = g ∧
    ∀ e : Link L, e ≠ ⟨x, μ⟩ → updateGroupGaugeLink L V x μ g e = V e := by
  unfold updateGroupGaugeLink
  exact ⟨Function.update_self ⟨x, μ⟩ g V, fun e he => Function.update_of_ne he g V⟩

/-- Simultaneous two-link gauge configuration perturbation on `GroupGaugeConfig G L`. -/
def updateTwoGroupGaugeLinks {G : Type*} (L : ℕ) (V : GroupGaugeConfig G L)
    (x1 : Lattice4D L) (μ1 : Fin 4) (g : G)
    (x2 : Lattice4D L) (μ2 : Fin 4) (h : G) : GroupGaugeConfig G L :=
  updateGroupGaugeLink L (updateGroupGaugeLink L V x1 μ1 g) x2 μ2 h

/-- Two-link mixed second difference `Δ²_{e1, e2} A(V; g1, g2, h1, h2)` of an action
`A : GroupGaugeConfig G L → ℝ` for an arbitrary gauge group `G`. -/
def groupTwoLinkMixedDifference {G : Type*} (L : ℕ) (A : GroupGaugeConfig G L → ℝ)
    (V : GroupGaugeConfig G L)
    (x1 : Lattice4D L) (μ1 : Fin 4) (g1 g2 : G)
    (x2 : Lattice4D L) (μ2 : Fin 4) (h1 h2 : G) : ℝ :=
  (A (updateTwoGroupGaugeLinks L V x1 μ1 g1 x2 μ2 h1) -
    A (updateTwoGroupGaugeLinks L V x1 μ1 g2 x2 μ2 h1)) -
  (A (updateTwoGroupGaugeLinks L V x1 μ1 g1 x2 μ2 h2) -
    A (updateTwoGroupGaugeLinks L V x1 μ1 g2 x2 μ2 h2))

/-- Changing one link in `GroupGaugeConfig G L` leaves every nonincident plaquette action unchanged. -/
theorem groupPlaquetteAction_eq_of_agree_off_link {G : Type*} [Group G] [TopologicalSpace G]
    {L : ℕ} (tr : CompactGaugeClassTrace G) (U W : GroupGaugeConfig G L) (e : Link L)
    (hUW : ∀ f, f ≠ e → U f = W f) (p : Plaquette L)
    (hp : p ∉ incidentPlaquettes e) : groupPlaquetteAction tr U p = groupPlaquetteAction tr W p := by
  have h1 : (⟨p.x, p.μ⟩ : Link L) ≠ e := fun h =>
    hp (plaquette_mem_incident_of_boundary p e (Or.inl h.symm))
  have h2 : (⟨shift p.x p.μ, p.ν⟩ : Link L) ≠ e := fun h =>
    hp (plaquette_mem_incident_of_boundary p e (Or.inr (Or.inl h.symm)))
  have h3 : (⟨shift p.x p.ν, p.μ⟩ : Link L) ≠ e := fun h =>
    hp (plaquette_mem_incident_of_boundary p e (Or.inr (Or.inr (Or.inl h.symm))))
  have h4 : (⟨p.x, p.ν⟩ : Link L) ≠ e := fun h =>
    hp (plaquette_mem_incident_of_boundary p e (Or.inr (Or.inr (Or.inr h.symm))))
  simp only [groupPlaquetteAction, groupPlaquetteHolonomy, hUW _ h1, hUW _ h2, hUW _ h3, hUW _ h4]

/-- For any gauge group `G` and class trace `tr : CompactGaugeClassTrace G`, the Wilson action
`groupWilsonAction tr β` changes by at most `12 * β` under one link change, uniformly in volume `L`. -/
theorem groupWilsonAction_oscillation_of_agree_off_link {G : Type*} [Group G] [TopologicalSpace G]
    {L : ℕ} [NeZero L] (tr : CompactGaugeClassTrace G)
    {β : ℝ} (hβ : 0 ≤ β) (U W : GroupGaugeConfig G L) (e : Link L)
    (hUW : ∀ f, f ≠ e → U f = W f) :
    |groupWilsonAction tr β U - groupWilsonAction tr β W| ≤ 12 * β := by
  classical
  have hsum : (∑ p : Plaquette L, (groupPlaquetteAction tr U p - groupPlaquetteAction tr W p)) =
      ∑ p ∈ incidentPlaquettes e, (groupPlaquetteAction tr U p - groupPlaquetteAction tr W p) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    rw [groupPlaquetteAction_eq_of_agree_off_link tr U W e hUW p hp, sub_self]
  have hb (p : Plaquette L) : |groupPlaquetteAction tr U p - groupPlaquetteAction tr W p| ≤ 2 := by
    have hu := abs_le.mp (tr.h_abs_le_one (groupPlaquetteHolonomy U p))
    have hw := abs_le.mp (tr.h_abs_le_one (groupPlaquetteHolonomy W p))
    dsimp [groupPlaquetteAction]
    exact abs_le.mpr ⟨by linarith [hu.2, hw.1], by linarith [hu.1, hw.2]⟩
  have hs : |∑ p ∈ incidentPlaquettes e, (groupPlaquetteAction tr U p - groupPlaquetteAction tr W p)| ≤ 12 := by
    calc
      _ ≤ ∑ p ∈ incidentPlaquettes e, |groupPlaquetteAction tr U p - groupPlaquetteAction tr W p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ incidentPlaquettes e, (2 : ℝ) := Finset.sum_le_sum (fun p _ => hb p)
      _ = (incidentPlaquettes e).card * (2 : ℝ) := by simp
      _ ≤ 12 := by exact_mod_cast Nat.mul_le_mul_right 2 (incidentPlaquettes_card_le_six e)
  unfold groupWilsonAction
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hβ, hsum]
  nlinarith

/-- Finite-range locality of `groupWilsonAction tr β` on `GroupGaugeConfig G L` for an arbitrary
gauge group `G`: for any two distinct links `e1` and `e2` with `e2 ∉ dobrushinNeighbors e1`, the
two-link mixed second difference of `groupWilsonAction tr β` vanishes identically across all `L`. -/
theorem groupTwoLinkMixedDifference_groupWilsonAction_eq_zero_of_not_mem_dobrushinNeighbors
    {G : Type*} [Group G] [TopologicalSpace G]
    {L : ℕ} [NeZero L] (tr : CompactGaugeClassTrace G) (β : ℝ)
    (V : GroupGaugeConfig G L) (e1 e2 : Link L)
    (hne : e2 ≠ e1) (hn : e2 ∉ dobrushinNeighbors e1) (g1 g2 h1 h2 : G) :
    groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e1.x e1.μ g1 g2 e2.x e2.μ h1 h2 = 0 := by
  classical
  have h_off_e1 (h : G) (f : Link L) (hf : f ≠ e1) :
      updateTwoGroupGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h f =
        updateTwoGroupGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h f := by
    dsimp [updateTwoGroupGaugeLinks]
    by_cases hfe2 : f = e2
    · subst hfe2
      exact ((updateGroupGaugeLink_same_and_other L (updateGroupGaugeLink L V e1.x e1.μ g1) f.x f.μ h).1).trans
        ((updateGroupGaugeLink_same_and_other L (updateGroupGaugeLink L V e1.x e1.μ g2) f.x f.μ h).1).symm
    · have h1f := (updateGroupGaugeLink_same_and_other L (updateGroupGaugeLink L V e1.x e1.μ g1) e2.x e2.μ h).2 f hfe2
      have h2f := (updateGroupGaugeLink_same_and_other L (updateGroupGaugeLink L V e1.x e1.μ g2) e2.x e2.μ h).2 f hfe2
      have h1e := (updateGroupGaugeLink_same_and_other L V e1.x e1.μ g1).2 f hf
      have h2e := (updateGroupGaugeLink_same_and_other L V e1.x e1.μ g2).2 f hf
      exact (h1f.trans h1e).trans (h2f.trans h2e).symm
  have h_off_e2 (g : G) (f : Link L) (hf : f ≠ e2) :
      updateTwoGroupGaugeLinks L V e1.x e1.μ g e2.x e2.μ h1 f =
        updateTwoGroupGaugeLinks L V e1.x e1.μ g e2.x e2.μ h2 f := by
    dsimp [updateTwoGroupGaugeLinks]
    exact ((updateGroupGaugeLink_same_and_other L (updateGroupGaugeLink L V e1.x e1.μ g) e2.x e2.μ h1).2 f hf).trans
      ((updateGroupGaugeLink_same_and_other L (updateGroupGaugeLink L V e1.x e1.μ g) e2.x e2.μ h2).2 f hf).symm
  have h_diff (h : G) :
      groupWilsonAction tr β (updateTwoGroupGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h) -
        groupWilsonAction tr β (updateTwoGroupGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h) =
      β * ∑ p ∈ incidentPlaquettes e1,
        (groupPlaquetteAction tr (updateTwoGroupGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h) p -
          groupPlaquetteAction tr (updateTwoGroupGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h) p) := by
    unfold groupWilsonAction
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    rw [groupPlaquetteAction_eq_of_agree_off_link tr _ _ e1 (h_off_e1 h) p hp, sub_self]
  dsimp [groupTwoLinkMixedDifference]
  rw [h_diff h1, h_diff h2]
  have h_sum_eq :
      (∑ p ∈ incidentPlaquettes e1,
        (groupPlaquetteAction tr (updateTwoGroupGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h1) p -
          groupPlaquetteAction tr (updateTwoGroupGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h1) p)) =
      ∑ p ∈ incidentPlaquettes e1,
        (groupPlaquetteAction tr (updateTwoGroupGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h2) p -
          groupPlaquetteAction tr (updateTwoGroupGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h2) p) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp2 := not_mem_incidentPlaquettes_of_not_mem_dobrushinNeighbors hne hn hp
    rw [groupPlaquetteAction_eq_of_agree_off_link tr _ _ e2 (h_off_e2 g1) p hp2,
      groupPlaquetteAction_eq_of_agree_off_link tr _ _ e2 (h_off_e2 g2) p hp2]
  rw [h_sum_eq, sub_self]

/-- Pointwise two-link mixed second-difference bound for `groupWilsonAction tr β` on
`GroupGaugeConfig G L`: changing two links `(e1.x, e1.μ)` and `(e2.x, e2.μ)` changes the mixed
second difference by at most `24 * β` uniformly in lattice volume `L` and gauge group `G`. -/
theorem groupTwoLinkMixedDifference_groupWilsonAction_abs_le_twentyFour_mul_beta
    {G : Type*} [Group G] [TopologicalSpace G]
    {L : ℕ} [NeZero L] (tr : CompactGaugeClassTrace G) {β : ℝ} (hβ : 0 ≤ β)
    (V : GroupGaugeConfig G L) (e1 e2 : Link L)
    (g1 g2 h1 h2 : G) :
    |groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e1.x e1.μ g1 g2 e2.x e2.μ h1 h2| ≤
      24 * β := by
  have h_off_e2 (g : G) (f : Link L) (hf : f ≠ e2) :
      updateTwoGroupGaugeLinks L V e1.x e1.μ g e2.x e2.μ h1 f =
        updateTwoGroupGaugeLinks L V e1.x e1.μ g e2.x e2.μ h2 f := by
    dsimp [updateTwoGroupGaugeLinks]
    exact ((updateGroupGaugeLink_same_and_other L (updateGroupGaugeLink L V e1.x e1.μ g) e2.x e2.μ h1).2 f hf).trans
      ((updateGroupGaugeLink_same_and_other L (updateGroupGaugeLink L V e1.x e1.μ g) e2.x e2.μ h2).2 f hf).symm
  have h_osc1 := groupWilsonAction_oscillation_of_agree_off_link tr hβ
    (updateTwoGroupGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h1)
    (updateTwoGroupGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h2)
    e2 (h_off_e2 g1)
  have h_osc2 := groupWilsonAction_oscillation_of_agree_off_link tr hβ
    (updateTwoGroupGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h1)
    (updateTwoGroupGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h2)
    e2 (h_off_e2 g2)
  have h_re :
      groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e1.x e1.μ g1 g2 e2.x e2.μ h1 h2 =
      (groupWilsonAction tr β (updateTwoGroupGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h1) -
        groupWilsonAction tr β (updateTwoGroupGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h2)) -
      (groupWilsonAction tr β (updateTwoGroupGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h1) -
        groupWilsonAction tr β (updateTwoGroupGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h2)) := by
    dsimp [groupTwoLinkMixedDifference]
    ring
  have h_tri := abs_sub
    (groupWilsonAction tr β (updateTwoGroupGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h1) -
      groupWilsonAction tr β (updateTwoGroupGaugeLinks L V e1.x e1.μ g1 e2.x e2.μ h2))
    (groupWilsonAction tr β (updateTwoGroupGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h1) -
      groupWilsonAction tr β (updateTwoGroupGaugeLinks L V e1.x e1.μ g2 e2.x e2.μ h2))
  rw [← h_re] at h_tri
  linarith

/-- Volume-uniform finite-range locality and sum bound for the two-link action mixed second
difference of `groupWilsonAction tr β` across all torus sizes `L` and all compact topological
gauge groups `G`:
1. Summing `|groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|`
   over all `4 L^4 - 1` partner links `e' ∈ Finset.univ.erase e` collapses identically to the
   finite neighborhood `dobrushinNeighbors e` (of support cardinality `≤ 18`, independent of `L`
   and `G`), with unnormalized sum bounded by `432 * β`.
2. The `(1 / 24)`-rescaled two-link mixed-difference sum is bounded by `18 * β` uniformly in `L`
   and `G`, and is strictly less than `1` for `0 ≤ β < 1 / 18`. -/
theorem groupWilson_twoLinkMixedDifference_locality_and_sum_bound
    {G : Type*} [Group G] [TopologicalSpace G]
    {L : ℕ} [NeZero L] (tr : CompactGaugeClassTrace G) (e : Link L) {β : ℝ} (hβ : 0 ≤ β) :
    ∀ (V : GroupGaugeConfig G L) (g1 g2 : G) (h1 h2 : Link L → G),
      (∑ e' ∈ Finset.univ.erase e,
        |groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) =
      (∑ e' ∈ dobrushinNeighbors e,
        |groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) ∧
      (1 / 24 : ℝ) *
        (∑ e' ∈ Finset.univ.erase e,
          |groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) ≤
        18 * β ∧
      (β < 1 / 18 →
        (1 / 24 : ℝ) *
          (∑ e' ∈ Finset.univ.erase e,
            |groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) <
          1) := by
  intro V g1 g2 h1 h2
  have hcollapse :
      (∑ e' ∈ Finset.univ.erase e,
        |groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) =
      (∑ e' ∈ dobrushinNeighbors e,
        |groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) := by
    symm
    apply Finset.sum_subset
    · intro e' he'
      exact Finset.mem_erase.mpr ⟨fun h => not_mem_dobrushinNeighbors_self e (h ▸ he'), Finset.mem_univ e'⟩
    · intro e' he' hn
      rw [groupTwoLinkMixedDifference_groupWilsonAction_eq_zero_of_not_mem_dobrushinNeighbors tr β V e e'
        (Finset.mem_erase.mp he').1 hn g1 g2 (h1 e') (h2 e'), abs_zero]
  have hcard : ((dobrushinNeighbors e).card : ℝ) ≤ 18 := by
    exact_mod_cast dobrushinNeighbors_card_le_eighteen e
  have hsum_le :
      (∑ e' ∈ Finset.univ.erase e,
        |groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) ≤
      18 * (24 * β) := by
    rw [hcollapse]
    calc
      (∑ e' ∈ dobrushinNeighbors e,
        |groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|)
        ≤ ∑ _e' ∈ dobrushinNeighbors e, (24 * β) :=
          Finset.sum_le_sum (fun e' _ =>
            groupTwoLinkMixedDifference_groupWilsonAction_abs_le_twentyFour_mul_beta
              tr hβ V e e' g1 g2 (h1 e') (h2 e'))
      _ = ((dobrushinNeighbors e).card : ℝ) * (24 * β) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 18 * (24 * β) :=
          mul_le_mul_of_nonneg_right hcard (by linarith)
  have hrow :
      (1 / 24 : ℝ) *
        (∑ e' ∈ Finset.univ.erase e,
          |groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) ≤
      18 * β := by
    linarith
  refine ⟨hcollapse, hrow, fun hlt => by linarith⟩

alias groupWilson_dobrushin_rowSum_uniform_in_L :=
  groupWilson_twoLinkMixedDifference_locality_and_sum_bound

/-! ## Dobrushin Coupling Contraction, Geometric Covariance Tail & Time-Slice Link Decomposition -/

/-- Inductive Dobrushin coupling contraction: if a non-negative step-oscillation sequence
`δ : ℕ → ℝ` satisfies `δ (m + 1) ≤ q * δ m` for `0 ≤ q`, then `δ m ≤ q ^ m * δ 0` for all `m : ℕ`. -/
theorem dobrushinStepOscillation_le_pow_mul {q : ℝ} (hq : 0 ≤ q)
    {δ : ℕ → ℝ} (hstep : ∀ m : ℕ, δ (m + 1) ≤ q * δ m) :
    ∀ m : ℕ, δ m ≤ q ^ m * δ 0 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      δ (m + 1) ≤ q * δ m := hstep m
      _ ≤ q * (q ^ m * δ 0) := mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (m + 1) * δ 0 := by rw [pow_succ']; ring

/-- Partial geometric series identity `(1 - q) * ∑_{k < N} q^k = 1 - q^N`. -/
theorem dobrushinPartialGeometricSum_mul_one_sub (q : ℝ) (N : ℕ) :
    (1 - q) * (∑ k ∈ Finset.range N, q ^ k) = 1 - q ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

/-- For `0 ≤ q < 1`, every finite geometric partial sum `∑_{k < N} q^k` is bounded above by
`(1 - q)⁻¹`. -/
theorem dobrushinPartialGeometricSum_le_inv_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    (∑ k ∈ Finset.range N, q ^ k) ≤ (1 - q)⁻¹ := by
  have hq_pos : 0 < 1 - q := by linarith
  have hqN : 0 ≤ q ^ N := pow_nonneg hq0 N
  rw [← one_div, le_div_iff₀ hq_pos, mul_comm, dobrushinPartialGeometricSum_mul_one_sub]
  linarith

/-- Geometric tail bound for a Dobrushin step-oscillation sequence `δ : ℕ → ℝ`: if `0 ≤ q < 1`,
`0 ≤ δ 0`, and `δ (m + 1) ≤ q * δ m` for all `m`, then for every separation distance `d : ℕ` and
truncation horizon `N : ℕ`, `∑_{k < N} δ (d + k) ≤ δ 0 * q ^ d * (1 - q)⁻¹`. -/
theorem dobrushinGeometricTail_sum_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {δ : ℕ → ℝ} (hδ0 : 0 ≤ δ 0) (hstep : ∀ m : ℕ, δ (m + 1) ≤ q * δ m)
    (d N : ℕ) :
    (∑ k ∈ Finset.range N, δ (d + k)) ≤ δ 0 * q ^ d * (1 - q)⁻¹ := by
  have hterm (k : ℕ) : δ (d + k) ≤ (δ 0 * q ^ d) * q ^ k := by
    calc
      δ (d + k) ≤ q ^ (d + k) * δ 0 :=
        dobrushinStepOscillation_le_pow_mul hq0 hstep (d + k)
      _ = (δ 0 * q ^ d) * q ^ k := by
        rw [pow_add]
        ring
  calc
    (∑ k ∈ Finset.range N, δ (d + k))
      ≤ ∑ k ∈ Finset.range N, (δ 0 * q ^ d) * q ^ k :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = (δ 0 * q ^ d) * (∑ k ∈ Finset.range N, q ^ k) := by
        rw [← Finset.mul_sum]
    _ ≤ (δ 0 * q ^ d) * (1 - q)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (dobrushinPartialGeometricSum_le_inv_one_sub hq0 hq1 N)
          (mul_nonneg hδ0 (pow_nonneg hq0 d))

/-- Volume- and group-uniform Dobrushin row-sum contraction and exponential covariance decay for
the 4D Wilson gauge action `groupWilsonAction tr β` on `GroupGaugeConfig G L`:
for any topological group `G`, any class trace `tr : CompactGaugeClassTrace G`, any torus side `L`
(`[NeZero L]`), and any strong coupling `0 ≤ β < 1 / 18`,
1. The normalized torus-wide Dobrushin row sum at every link `e : Link L` is bounded by `18 * β`
   and is strictly less than `1` uniformly in `L` and `G`.
2. For any observable pair with covariance `cov_fg : ℝ` bounded at link-graph distance `d : ℕ` and
   truncation horizon `N : ℕ` by `|cov_fg| ≤ ∑ k ∈ Finset.range N, δ (d + k)` under a Dobrushin
   step-oscillation sequence `δ : ℕ → ℝ` satisfying `0 ≤ δ 0` and
   `∀ m, δ (m + 1) ≤ (18 * β) * δ m`, the covariance decays exponentially with distance `d`:
   `|cov_fg| ≤ δ 0 * (18 * β) ^ d * (1 - 18 * β)⁻¹`. -/
theorem groupWilson_dobrushin_covariance_decay_uniform_in_L
    {G : Type*} [Group G] [TopologicalSpace G]
    {L : ℕ} [NeZero L] (tr : CompactGaugeClassTrace G) (e : Link L)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1 / 18)
    (V : GroupGaugeConfig G L) (g1 g2 : G) (h1 h2 : Link L → G)
    {δ : ℕ → ℝ} (hδ0 : 0 ≤ δ 0) (hstep : ∀ m : ℕ, δ (m + 1) ≤ (18 * β) * δ m)
    {cov_fg : ℝ} (d N : ℕ) (hcov : |cov_fg| ≤ ∑ k ∈ Finset.range N, δ (d + k)) :
    (1 / 24 : ℝ) *
      (∑ e' ∈ Finset.univ.erase e,
        |groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) ≤
      18 * β ∧
    (1 / 24 : ℝ) *
      (∑ e' ∈ Finset.univ.erase e,
        |groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e.x e.μ g1 g2 e'.x e'.μ (h1 e') (h2 e')|) <
      1 ∧
    |cov_fg| ≤ δ 0 * (18 * β) ^ d * (1 - 18 * β)⁻¹ := by
  have hrow := groupWilson_dobrushin_rowSum_uniform_in_L tr e hβ0 V g1 g2 h1 h2
  have hq0 : 0 ≤ 18 * β := by linarith
  have hq1 : 18 * β < 1 := by linarith
  have htail := dobrushinGeometricTail_sum_le hq0 hq1 hδ0 hstep d N
  exact ⟨hrow.2.1, hrow.2.2 hβ1, hcov.trans htail⟩

/-- Boolean predicate identifying spatial links (`e.μ ≠ 0`) lying in the Euclidean time slice
`e.x 0 = t` on the 4D periodic torus `Link L`. -/
def isSpatialSliceLink {L : ℕ} (t : ZMod L) (e : Link L) : Bool :=
  (e.μ != 0) && (e.x 0 == t)

/-- Finite set of spatial links (`e.μ ≠ 0`, `e.x 0 = t`) in time slice `t : ZMod L`. -/
def spatialSliceLinks (L : ℕ) [NeZero L] (t : ZMod L) : Finset (Link L) :=
  Finset.univ.filter (fun e => isSpatialSliceLink t e = true)

/-- Finite set of all links outside the spatial time slice `t : ZMod L` (temporal links and spatial
links at other time slices `e.x 0 ≠ t`). -/
def complementSliceLinks (L : ℕ) [NeZero L] (t : ZMod L) : Finset (Link L) :=
  Finset.univ.filter (fun e => isSpatialSliceLink t e = false)

/-- The spatial time-slice link set `spatialSliceLinks L t` and its complement
`complementSliceLinks L t` are disjoint. -/
theorem disjoint_spatialSliceLinks_complementSliceLinks (L : ℕ) [NeZero L] (t : ZMod L) :
    Disjoint (spatialSliceLinks L t) (complementSliceLinks L t) := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  rw [spatialSliceLinks, Finset.mem_filter] at he1
  rw [complementSliceLinks, Finset.mem_filter] at he2
  have h := he1.2.symm.trans he2.2
  contradiction

/-- Every link in `Finset.univ : Finset (Link L)` belongs to either `spatialSliceLinks L t` or
`complementSliceLinks L t`. -/
theorem spatialSliceLinks_union_complementSliceLinks (L : ℕ) [NeZero L] (t : ZMod L) :
    spatialSliceLinks L t ∪ complementSliceLinks L t = Finset.univ := by
  ext e
  simp only [spatialSliceLinks, complementSliceLinks, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  cases isSpatialSliceLink t e <;> simp

/-- On the 4D periodic torus `Λ = (ℤ/Lℤ)⁴`, there are `4 * L⁴` oriented links. -/
theorem card_link_eq_four_mul_pow_four (L : ℕ) [NeZero L] :
    Fintype.card (Link L) = 4 * L ^ 4 := by
  have h_equiv : Fintype.card (Link L) = Fintype.card (Lattice4D L × Direction) :=
    Fintype.card_congr (linkEquiv L)
  have h_dir : Fintype.card Direction = 4 := by decide
  rw [h_equiv, Fintype.card_prod, card_lattice4D L, h_dir, mul_comm]

/-- The cardinalities of `spatialSliceLinks L t` and `complementSliceLinks L t` sum to the total
number of oriented torus links `4 * L ^ 4`. -/
theorem card_spatialSliceLinks_add_card_complementSliceLinks (L : ℕ) [NeZero L] (t : ZMod L) :
    (spatialSliceLinks L t).card + (complementSliceLinks L t).card = 4 * L ^ 4 := by
  rw [← Finset.card_union_of_disjoint (disjoint_spatialSliceLinks_complementSliceLinks L t),
    spatialSliceLinks_union_complementSliceLinks L t, Finset.card_univ,
    card_link_eq_four_mul_pow_four L]

/-! ## Concrete Transverse-Midpoint Smoothed Block Map & Small/Large-Field Fiber Integral Split -/

/-- Canonical perpendicular lattice direction `μ + 1 (mod 4)` on `Fin 4`. -/
def perpDir (μ : Fin 4) : Fin 4 := μ + 1

/-- For every direction `μ : Fin 4`, the perpendicular direction `perpDir μ = μ + 1` is distinct
from `μ`. -/
theorem perpDir_ne_self (μ : Fin 4) : perpDir μ ≠ μ := by
  fin_cases μ <;> decide

/-- Canonical perpendicular fine link at the midpoint vertex of coarse link `e : Link L`, embedded
into the independent Haar fiber coordinates `unusedFineLinks L`. -/
def dyadicPerpMidpointUnusedLink (L : ℕ) [NeZero L] (e : Link L) : unusedFineLinks L :=
  dyadicMidpointTransverseUnusedLink L e (perpDir e.μ) (perpDir_ne_self e.μ)

/-- Transverse-smoothed coarse block map multiplying the two fine edges `u.1.1 e * u.1.2 e`
by a transverse dressing factor `Φ u.2 e` supported on `unusedFineLinks L`. -/
def transverseSmoothedBlock {G : Type*} [Group G] {L : ℕ}
    (Φ : (unusedFineLinks L → G) → (Link L → G))
    (u : ((Link L → G) × (Link L → G)) × (unusedFineLinks L → G)) : Link L → G :=
  fun e => u.1.1 e * u.1.2 e * Φ u.2 e

/-- Exact fiber reconstruction for `transverseSmoothedBlock Φ`, reconstructing the second fine
edge as `(r.1 e)⁻¹ * v e * (Φ r.2 e)⁻¹`. -/
def transverseSmoothedRebuild {G : Type*} [Group G] {L : ℕ}
    (Φ : (unusedFineLinks L → G) → (Link L → G))
    (v : Link L → G) (r : (Link L → G) × (unusedFineLinks L → G)) :
    ((Link L → G) × (Link L → G)) × (unusedFineLinks L → G) :=
  ((r.1, fun e => (r.1 e)⁻¹ * v e * (Φ r.2 e)⁻¹), r.2)

/-- Pointwise exact reconstruction identity: `transverseSmoothedBlock Φ` is a left inverse to
`transverseSmoothedRebuild Φ v` for every coarse configuration `v` and fiber coordinate `r`. -/
@[simp] theorem transverseSmoothedBlock_rebuild {G : Type*} [Group G] {L : ℕ}
    (Φ : (unusedFineLinks L → G) → (Link L → G))
    (v : Link L → G) (r : (Link L → G) × (unusedFineLinks L → G)) :
    transverseSmoothedBlock Φ (transverseSmoothedRebuild Φ v r) = v := by
  funext e
  simp [transverseSmoothedBlock, transverseSmoothedRebuild, mul_assoc]

/-- Concrete transverse midpoint dressing on `unusedFineLinks L` evaluating the perpendicular
fine link `dyadicPerpMidpointUnusedLink L e` at the midpoint vertex of each coarse link `e`. -/
def midpointStapleDressing {G : Type*} [Group G] (L : ℕ) [NeZero L]
    (z : unusedFineLinks L → G) : Link L → G :=
  fun e => z (dyadicPerpMidpointUnusedLink L e)

/-- Pointwise exact reconstruction identity for `transverseSmoothedBlock` specialized to the
concrete transverse midpoint dressing `midpointStapleDressing L`. -/
@[simp] theorem transverseSmoothedBlock_midpointStaple_rebuild
    {G : Type*} [Group G] (L : ℕ) [NeZero L]
    (v : Link L → G) (r : (Link L → G) × (unusedFineLinks L → G)) :
    transverseSmoothedBlock (midpointStapleDressing L)
      (transverseSmoothedRebuild (midpointStapleDressing L) v r) = v :=
  transverseSmoothedBlock_rebuild (midpointStapleDressing L) v r

/-- Algebraic identity decomposing the total fiber weight defect `(w_sf + w_lf) - w_lead` into the
small-field defect `w_sf - w_lead` plus the large-field complement `w_lf`. -/
theorem j20_small_large_field_split_identity (w_sf w_lf w_lead : ℝ) :
    (w_sf + w_lf) - w_lead = (w_sf - w_lead) + w_lf := by
  ring

/-- Single-step small-field + Peierls large-field fiber integral defect bound: if a total fiber
weight `w_total = w_sf + w_lf` splits into a small-field integral satisfying
`|w_sf - w_lead| ≤ ε_sf` and a non-negative large-field complement integral bounded by the
Peierls factor `w_lf ≤ Real.exp (-(β * δ))`, then
`|w_total - w_lead| ≤ ε_sf + Real.exp (-(β * δ))`. -/
theorem small_and_large_field_fiber_weight_defect_le
    {w_total w_sf w_lf w_lead ε_sf β δ : ℝ}
    (h_split : w_total = w_sf + w_lf)
    (h_sf : |w_sf - w_lead| ≤ ε_sf)
    (h_lf_nonneg : 0 ≤ w_lf)
    (h_lf_le : w_lf ≤ Real.exp (-(β * δ))) :
    |w_total - w_lead| ≤ ε_sf + Real.exp (-(β * δ)) := by
  rw [h_split, j20_small_large_field_split_identity]
  have h_sf_bounds := abs_le.mp h_sf
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ## Single-Link Conditional Gibbs Expectation & Torus-Wide Interdependence Locality -/

/-- Single-link conditional Boltzmann partition function at link `e` given configuration `V`
outside `e`, integrating `Real.exp (-S_act (updateGroupGaugeLink L V e.x e.μ g))` over the
single-link Haar probability measure `compactGroupHaarProbability G`. -/
noncomputable def groupSingleLinkPartition (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) (S_act : GroupGaugeConfig G L → ℝ) (V : GroupGaugeConfig G L)
    (e : Link L) : ℝ :=
  ∫ g : G, Real.exp (-S_act (updateGroupGaugeLink L V e.x e.μ g))
    ∂(compactGroupHaarProbability G : Measure G)

/-- Single-link conditional Gibbs expectation of a bounded test observable `φ : G → ℝ` at link `e`
given the exterior configuration `V`. -/
noncomputable def groupSingleLinkCondExp (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) (S_act : GroupGaugeConfig G L → ℝ) (V : GroupGaugeConfig G L)
    (e : Link L) (φ : G → ℝ) : ℝ :=
  (∫ g : G, Real.exp (-S_act (updateGroupGaugeLink L V e.x e.μ g)) * φ g
    ∂(compactGroupHaarProbability G : Measure G)) /
    groupSingleLinkPartition G L S_act V e

/-- If changing the exterior configuration from `V2` to `V1` shifts the single-link action
`g ↦ S_act (updateGroupGaugeLink L V_i e.x e.μ g)` by a constant `d0` independent of `g : G`,
then the positive factor `Real.exp (-d0)` cancels between numerator and denominator of
`groupSingleLinkCondExp`, leaving the conditional Gibbs expectation at `e` invariant. -/
theorem groupSingleLinkCondExp_eq_of_action_diff_const
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} (S_act : GroupGaugeConfig G L → ℝ)
    (V1 V2 : GroupGaugeConfig G L) (e : Link L) (φ : G → ℝ) {d0 : ℝ}
    (h_diff : ∀ g : G,
      S_act (updateGroupGaugeLink L V1 e.x e.μ g) -
        S_act (updateGroupGaugeLink L V2 e.x e.μ g) = d0) :
    groupSingleLinkCondExp G L S_act V1 e φ =
      groupSingleLinkCondExp G L S_act V2 e φ := by
  have h_exp (g : G) :
      Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)) =
        Real.exp (-d0) * Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) := by
    rw [← Real.exp_add]
    congr 1
    have hg := h_diff g
    linarith
  have h_exp_mul (g : G) :
      Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)) * φ g =
        Real.exp (-d0) * (Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) * φ g) := by
    rw [h_exp g, mul_assoc]
  have h_part :
      groupSingleLinkPartition G L S_act V1 e =
        Real.exp (-d0) * groupSingleLinkPartition G L S_act V2 e := by
    unfold groupSingleLinkPartition
    simp_rw [h_exp]
    exact integral_const_mul (Real.exp (-d0)) _
  have h_num :
      (∫ g : G, Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)) * φ g
        ∂(compactGroupHaarProbability G : Measure G)) =
      Real.exp (-d0) *
        (∫ g : G, Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) * φ g
          ∂(compactGroupHaarProbability G : Measure G)) := by
    simp_rw [h_exp_mul]
    exact integral_const_mul (Real.exp (-d0)) _
  unfold groupSingleLinkCondExp
  rw [h_num, h_part, mul_div_mul_left _ _ (Real.exp_ne_zero (-d0))]

/-- Updating two distinct links `e1 ≠ e2` in `GroupGaugeConfig G L` commutes. -/
theorem updateGroupGaugeLink_comm {G : Type*} (L : ℕ) (V : GroupGaugeConfig G L)
    {e1 e2 : Link L} (hne : e1 ≠ e2) (g1 g2 : G) :
    updateGroupGaugeLink L (updateGroupGaugeLink L V e1.x e1.μ g1) e2.x e2.μ g2 =
      updateGroupGaugeLink L (updateGroupGaugeLink L V e2.x e2.μ g2) e1.x e1.μ g1 := by
  funext f
  by_cases hf2 : f = e2
  · subst hf2
    have h_lhs := (updateGroupGaugeLink_same_and_other L (updateGroupGaugeLink L V e1.x e1.μ g1) f.x f.μ g2).1
    have h_rhs1 := (updateGroupGaugeLink_same_and_other L (updateGroupGaugeLink L V f.x f.μ g2) e1.x e1.μ g1).2 f hne.symm
    have h_rhs2 := (updateGroupGaugeLink_same_and_other L V f.x f.μ g2).1
    exact h_lhs.trans (h_rhs1.trans h_rhs2).symm
  · have h_lhs1 := (updateGroupGaugeLink_same_and_other L (updateGroupGaugeLink L V e1.x e1.μ g1) e2.x e2.μ g2).2 f hf2
    by_cases hf1 : f = e1
    · subst hf1
      have h_lhs2 := (updateGroupGaugeLink_same_and_other L V f.x f.μ g1).1
      have h_rhs := (updateGroupGaugeLink_same_and_other L (updateGroupGaugeLink L V e2.x e2.μ g2) f.x f.μ g1).1
      exact (h_lhs1.trans h_lhs2).trans h_rhs.symm
    · have h_lhs2 := (updateGroupGaugeLink_same_and_other L V e1.x e1.μ g1).2 f hf1
      have h_rhs1 := (updateGroupGaugeLink_same_and_other L (updateGroupGaugeLink L V e2.x e2.μ g2) e1.x e1.μ g1).2 f hf1
      have h_rhs2 := (updateGroupGaugeLink_same_and_other L V e2.x e2.μ g2).2 f hf2
      exact (h_lhs1.trans h_lhs2).trans (h_rhs1.trans h_rhs2).symm

/-- Exact Markov locality of the single-link conditional Gibbs expectation
`groupSingleLinkCondExp G L (groupWilsonAction tr β)`:
flipping any exterior link `e' ≠ e` outside `dobrushinNeighbors e` from `h1` to `h2` leaves the
conditional Gibbs expectation at link `e` strictly unchanged. -/
theorem groupWilson_singleLinkCondExp_eq_of_not_mem_dobrushinNeighbors
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (tr : CompactGaugeClassTrace G) (β : ℝ)
    (V : GroupGaugeConfig G L) (e e' : Link L)
    (h_ne : e' ≠ e) (h_not_mem : e' ∉ dobrushinNeighbors e)
    (h1 h2 : G) (φ : G → ℝ) :
    groupSingleLinkCondExp G L (groupWilsonAction tr β)
        (updateGroupGaugeLink L V e'.x e'.μ h1) e φ =
      groupSingleLinkCondExp G L (groupWilsonAction tr β)
        (updateGroupGaugeLink L V e'.x e'.μ h2) e φ := by
  let V1 := updateGroupGaugeLink L V e'.x e'.μ h1
  let V2 := updateGroupGaugeLink L V e'.x e'.μ h2
  let d0 :=
    groupWilsonAction tr β (updateGroupGaugeLink L V1 e.x e.μ 1) -
      groupWilsonAction tr β (updateGroupGaugeLink L V2 e.x e.μ 1)
  apply groupSingleLinkCondExp_eq_of_action_diff_const G (groupWilsonAction tr β) V1 V2 e φ (d0 := d0)
  intro g
  have h1g : updateGroupGaugeLink L V1 e.x e.μ g =
      updateTwoGroupGaugeLinks L V e.x e.μ g e'.x e'.μ h1 := by
    dsimp [V1, updateTwoGroupGaugeLinks]
    exact updateGroupGaugeLink_comm L V h_ne h1 g
  have h2g : updateGroupGaugeLink L V2 e.x e.μ g =
      updateTwoGroupGaugeLinks L V e.x e.μ g e'.x e'.μ h2 := by
    dsimp [V2, updateTwoGroupGaugeLinks]
    exact updateGroupGaugeLink_comm L V h_ne h2 g
  have h1_one : updateGroupGaugeLink L V1 e.x e.μ 1 =
      updateTwoGroupGaugeLinks L V e.x e.μ 1 e'.x e'.μ h1 := by
    dsimp [V1, updateTwoGroupGaugeLinks]
    exact updateGroupGaugeLink_comm L V h_ne h1 1
  have h2_one : updateGroupGaugeLink L V2 e.x e.μ 1 =
      updateTwoGroupGaugeLinks L V e.x e.μ 1 e'.x e'.μ h2 := by
    dsimp [V2, updateTwoGroupGaugeLinks]
    exact updateGroupGaugeLink_comm L V h_ne h2 1
  have h_mixed :
      (groupWilsonAction tr β (updateGroupGaugeLink L V1 e.x e.μ g) -
        groupWilsonAction tr β (updateGroupGaugeLink L V2 e.x e.μ g)) - d0 =
      groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e.x e.μ g 1 e'.x e'.μ h1 h2 := by
    dsimp [d0, groupTwoLinkMixedDifference]
    rw [h1g, h2g, h1_one, h2_one]
    ring
  have h_zero :=
    groupTwoLinkMixedDifference_groupWilsonAction_eq_zero_of_not_mem_dobrushinNeighbors
      tr β V e e' h_ne h_not_mem g 1 h1 h2
  linarith

/-- Exact finite-range collapse of the torus-wide conditional Gibbs expectation interdependence sum:
summing `|groupSingleLinkCondExp ... (update V e' (h1 e')) e φ - groupSingleLinkCondExp ... (update V e' (h2 e')) e φ|`
over all `4 L^4 - 1` exterior links `e' ∈ Finset.univ.erase e` collapses identically to the
`≤ 18` plaquette-sharing neighbors `e' ∈ dobrushinNeighbors e`, uniformly in `L` and `G`. -/
theorem groupWilson_singleLinkCondExp_locality_sum_eq
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (tr : CompactGaugeClassTrace G) (β : ℝ)
    (V : GroupGaugeConfig G L) (e : Link L) (h1 h2 : Link L → G) (φ : G → ℝ) :
    (∑ e' ∈ Finset.univ.erase e,
      |groupSingleLinkCondExp G L (groupWilsonAction tr β)
          (updateGroupGaugeLink L V e'.x e'.μ (h1 e')) e φ -
        groupSingleLinkCondExp G L (groupWilsonAction tr β)
          (updateGroupGaugeLink L V e'.x e'.μ (h2 e')) e φ|) =
    (∑ e' ∈ dobrushinNeighbors e,
      |groupSingleLinkCondExp G L (groupWilsonAction tr β)
          (updateGroupGaugeLink L V e'.x e'.μ (h1 e')) e φ -
        groupSingleLinkCondExp G L (groupWilsonAction tr β)
          (updateGroupGaugeLink L V e'.x e'.μ (h2 e')) e φ|) := by
  symm
  apply Finset.sum_subset
  · intro e' he'
    exact Finset.mem_erase.mpr ⟨fun h => not_mem_dobrushinNeighbors_self e (h ▸ he'), Finset.mem_univ e'⟩
  · intro e' he' hn
    rw [groupWilson_singleLinkCondExp_eq_of_not_mem_dobrushinNeighbors G tr β V e e'
      (Finset.mem_erase.mp he').1 hn (h1 e') (h2 e') φ, sub_self, abs_zero]

/-- Single-link conditional Gibbs expectation ratio sandwich and oscillation bound from a
centered action-difference oscillation bound `|S_act (update V1 g) - S_act (update V2 g) - d0| ≤ Δ`:
for any nonnegative test observable `φ : G → ℝ`, `groupSingleLinkCondExp G L S_act V1 e φ` is
sandwiched between `Real.exp (-2 * Δ)` and `Real.exp (2 * Δ)` times
`groupSingleLinkCondExp G L S_act V2 e φ`, and whenever `groupSingleLinkCondExp G L S_act V2 e φ ≤ 1`,
the conditional expectation oscillation is bounded by `Real.exp (2 * Δ) - 1`. -/
theorem groupSingleLinkCondExp_ratio_and_oscillation_of_action_diff_bound
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} (S_act : GroupGaugeConfig G L → ℝ)
    (V1 V2 : GroupGaugeConfig G L) (e : Link L) (φ : G → ℝ) {d0 Δ : ℝ}
    (h_int_w1 : Integrable (fun g : G => Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)))
      (compactGroupHaarProbability G))
    (h_int_w2 : Integrable (fun g : G => Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)))
      (compactGroupHaarProbability G))
    (h_int_φ1 : Integrable (fun g : G => Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)) * φ g)
      (compactGroupHaarProbability G))
    (h_int_φ2 : Integrable (fun g : G => Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) * φ g)
      (compactGroupHaarProbability G))
    (hZ2 : 0 < groupSingleLinkPartition G L S_act V2 e)
    (hφ_nonneg : ∀ g : G, 0 ≤ φ g)
    (h_diff : ∀ g : G,
      |S_act (updateGroupGaugeLink L V1 e.x e.μ g) -
        S_act (updateGroupGaugeLink L V2 e.x e.μ g) - d0| ≤ Δ) :
    Real.exp (-2 * Δ) * groupSingleLinkCondExp G L S_act V2 e φ ≤
      groupSingleLinkCondExp G L S_act V1 e φ ∧
    groupSingleLinkCondExp G L S_act V1 e φ ≤
      Real.exp (2 * Δ) * groupSingleLinkCondExp G L S_act V2 e φ ∧
    (groupSingleLinkCondExp G L S_act V2 e φ ≤ 1 →
      |groupSingleLinkCondExp G L S_act V1 e φ -
          groupSingleLinkCondExp G L S_act V2 e φ| ≤ Real.exp (2 * Δ) - 1) := by
  have h_lo_g (g : G) :
      Real.exp (-d0 - Δ) * Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) ≤
        Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (h_diff g)).2])
  have h_hi_g (g : G) :
      Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)) ≤
        Real.exp (-d0 + Δ) * Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (h_diff g)).1])
  have hZ_lo :
      Real.exp (-d0 - Δ) * groupSingleLinkPartition G L S_act V2 e ≤
        groupSingleLinkPartition G L S_act V1 e := by
    unfold groupSingleLinkPartition
    rw [← integral_const_mul]
    exact integral_mono (h_int_w2.const_mul _) h_int_w1 h_lo_g
  have hZ_hi :
      groupSingleLinkPartition G L S_act V1 e ≤
        Real.exp (-d0 + Δ) * groupSingleLinkPartition G L S_act V2 e := by
    unfold groupSingleLinkPartition
    rw [← integral_const_mul]
    exact integral_mono h_int_w1 (h_int_w2.const_mul _) h_hi_g
  have hN_lo :
      Real.exp (-d0 - Δ) *
        (∫ g : G, Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) * φ g
          ∂(compactGroupHaarProbability G : Measure G)) ≤
      ∫ g : G, Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)) * φ g
        ∂(compactGroupHaarProbability G : Measure G) := by
    rw [← integral_const_mul]
    apply integral_mono (h_int_φ2.const_mul _) h_int_φ1
    intro g
    dsimp only
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (h_lo_g g) (hφ_nonneg g)
  have hN_hi :
      (∫ g : G, Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)) * φ g
        ∂(compactGroupHaarProbability G : Measure G)) ≤
      Real.exp (-d0 + Δ) *
        (∫ g : G, Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) * φ g
          ∂(compactGroupHaarProbability G : Measure G)) := by
    rw [← integral_const_mul]
    apply integral_mono h_int_φ1 (h_int_φ2.const_mul _)
    intro g
    dsimp only
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (h_hi_g g) (hφ_nonneg g)
  have hZ1 : 0 < groupSingleLinkPartition G L S_act V1 e :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) hZ2) hZ_lo
  have hN2 :
      0 ≤ ∫ g : G, Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) * φ g
        ∂(compactGroupHaarProbability G : Measure G) :=
    integral_nonneg fun g => mul_nonneg (Real.exp_pos _).le (hφ_nonneg g)
  have hE2_nonneg : 0 ≤ groupSingleLinkCondExp G L S_act V2 e φ :=
    div_nonneg hN2 hZ2.le
  have h_cancel2 :
      groupSingleLinkCondExp G L S_act V2 e φ * groupSingleLinkPartition G L S_act V2 e =
        ∫ g : G, Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) * φ g
          ∂(compactGroupHaarProbability G : Measure G) :=
    div_mul_cancel₀ _ hZ2.ne'
  have h_exp_lo : Real.exp (-d0 - Δ) = Real.exp (-2 * Δ) * Real.exp (-d0 + Δ) := by
    rw [← Real.exp_add]; congr 1; ring
  have h_exp_hi : Real.exp (-d0 + Δ) = Real.exp (2 * Δ) * Real.exp (-d0 - Δ) := by
    rw [← Real.exp_add]; congr 1; ring
  have h_ratio_lo :
      Real.exp (-2 * Δ) * groupSingleLinkCondExp G L S_act V2 e φ ≤
        groupSingleLinkCondExp G L S_act V1 e φ := by
    unfold groupSingleLinkCondExp
    rw [le_div_iff₀ hZ1]
    change Real.exp (-2 * Δ) * groupSingleLinkCondExp G L S_act V2 e φ *
        groupSingleLinkPartition G L S_act V1 e ≤ _
    calc
      Real.exp (-2 * Δ) * groupSingleLinkCondExp G L S_act V2 e φ *
          groupSingleLinkPartition G L S_act V1 e
        ≤ Real.exp (-2 * Δ) * groupSingleLinkCondExp G L S_act V2 e φ *
            (Real.exp (-d0 + Δ) * groupSingleLinkPartition G L S_act V2 e) :=
          mul_le_mul_of_nonneg_left hZ_hi (mul_nonneg (Real.exp_pos _).le hE2_nonneg)
      _ = Real.exp (-2 * Δ) * Real.exp (-d0 + Δ) *
            (groupSingleLinkCondExp G L S_act V2 e φ * groupSingleLinkPartition G L S_act V2 e) := by
          ring
      _ = Real.exp (-d0 - Δ) *
            (∫ g : G, Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) * φ g
              ∂(compactGroupHaarProbability G : Measure G)) := by
          rw [← h_exp_lo, h_cancel2]
      _ ≤ _ := hN_lo
  have h_ratio_hi :
      groupSingleLinkCondExp G L S_act V1 e φ ≤
        Real.exp (2 * Δ) * groupSingleLinkCondExp G L S_act V2 e φ := by
    unfold groupSingleLinkCondExp
    rw [div_le_iff₀ hZ1]
    change _ ≤ Real.exp (2 * Δ) * groupSingleLinkCondExp G L S_act V2 e φ *
        groupSingleLinkPartition G L S_act V1 e
    calc
      (∫ g : G, Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)) * φ g
          ∂(compactGroupHaarProbability G : Measure G))
        ≤ Real.exp (-d0 + Δ) *
            (∫ g : G, Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) * φ g
              ∂(compactGroupHaarProbability G : Measure G)) := hN_hi
      _ = Real.exp (2 * Δ) * Real.exp (-d0 - Δ) *
            (groupSingleLinkCondExp G L S_act V2 e φ * groupSingleLinkPartition G L S_act V2 e) := by
          rw [h_exp_hi, h_cancel2]
      _ = Real.exp (2 * Δ) * groupSingleLinkCondExp G L S_act V2 e φ *
            (Real.exp (-d0 - Δ) * groupSingleLinkPartition G L S_act V2 e) := by
          ring
      _ ≤ Real.exp (2 * Δ) * groupSingleLinkCondExp G L S_act V2 e φ *
            groupSingleLinkPartition G L S_act V1 e :=
          mul_le_mul_of_nonneg_left hZ_lo (mul_nonneg (Real.exp_pos _).le hE2_nonneg)
  refine ⟨h_ratio_lo, h_ratio_hi, ?_⟩
  intro hE2_le_one
  have hΔ_nonneg : 0 ≤ Δ := le_trans (abs_nonneg _) (h_diff 1)
  have h_exp2Δ_ge_one : 1 ≤ Real.exp (2 * Δ) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have h_exp_neg2Δ_le_one : Real.exp (-2 * Δ) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have h_cosh :
      (Real.exp (2 * Δ) - 1) - (1 - Real.exp (-2 * Δ)) =
        (Real.exp Δ - Real.exp (-Δ)) ^ 2 := by
    have h1 : Real.exp (2 * Δ) = Real.exp Δ * Real.exp Δ := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-2 * Δ) = Real.exp (-Δ) * Real.exp (-Δ) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp Δ * Real.exp (-Δ) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc
      (Real.exp (2 * Δ) - 1) - (1 - Real.exp (-2 * Δ))
        = Real.exp (2 * Δ) - 2 * (Real.exp Δ * Real.exp (-Δ)) + Real.exp (-2 * Δ) := by
          rw [h3]; ring
      _ = (Real.exp Δ - Real.exp (-Δ)) ^ 2 := by
          rw [h1, h2]; ring
  have h_sq_nonneg : 0 ≤ (Real.exp Δ - Real.exp (-Δ)) ^ 2 := sq_nonneg _
  have h_up :
      groupSingleLinkCondExp G L S_act V1 e φ - groupSingleLinkCondExp G L S_act V2 e φ ≤
        Real.exp (2 * Δ) - 1 := by
    have h_mul :
        (Real.exp (2 * Δ) - 1) * groupSingleLinkCondExp G L S_act V2 e φ ≤
          (Real.exp (2 * Δ) - 1) * 1 :=
      mul_le_mul_of_nonneg_left hE2_le_one (by linarith)
    linarith
  have h_down :
      -(Real.exp (2 * Δ) - 1) ≤
        groupSingleLinkCondExp G L S_act V1 e φ - groupSingleLinkCondExp G L S_act V2 e φ := by
    have h_mul :
        (1 - Real.exp (-2 * Δ)) * groupSingleLinkCondExp G L S_act V2 e φ ≤
          (1 - Real.exp (-2 * Δ)) * 1 :=
      mul_le_mul_of_nonneg_left hE2_le_one (by linarith)
    linarith
  exact abs_le.mpr ⟨h_down, h_up⟩

/-- Torus-wide single-link conditional Gibbs expectation interdependence sum bound for
`groupWilsonAction tr β` on `GroupGaugeConfig G L`, uniform in `L` and `G`:
for any `[0, 1]`-bounded integrable test observable `φ : G → ℝ`, summing the conditional expectation
oscillation over all `4 L^4 - 1` exterior links `e' ∈ Finset.univ.erase e` collapses to
`dobrushinNeighbors e` (of cardinality `≤ 18`) and is bounded by `18 * (Real.exp (48 * β) - 1)`. -/
theorem groupWilson_singleLinkCondExp_interdependence_sum_le_uniform_in_L
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (tr : CompactGaugeClassTrace G) {β : ℝ} (hβ : 0 ≤ β)
    (V : GroupGaugeConfig G L) (e : Link L) (h1 h2 : Link L → G) (φ : G → ℝ)
    (hφ_nonneg : ∀ g : G, 0 ≤ φ g)
    (h_int_w1 : ∀ e' ∈ dobrushinNeighbors e,
      Integrable (fun g : G =>
        Real.exp (-groupWilsonAction tr β
          (updateGroupGaugeLink L (updateGroupGaugeLink L V e'.x e'.μ (h1 e')) e.x e.μ g)))
        (compactGroupHaarProbability G))
    (h_int_w2 : ∀ e' ∈ dobrushinNeighbors e,
      Integrable (fun g : G =>
        Real.exp (-groupWilsonAction tr β
          (updateGroupGaugeLink L (updateGroupGaugeLink L V e'.x e'.μ (h2 e')) e.x e.μ g)))
        (compactGroupHaarProbability G))
    (h_int_φ1 : ∀ e' ∈ dobrushinNeighbors e,
      Integrable (fun g : G =>
        Real.exp (-groupWilsonAction tr β
          (updateGroupGaugeLink L (updateGroupGaugeLink L V e'.x e'.μ (h1 e')) e.x e.μ g)) * φ g)
        (compactGroupHaarProbability G))
    (h_int_φ2 : ∀ e' ∈ dobrushinNeighbors e,
      Integrable (fun g : G =>
        Real.exp (-groupWilsonAction tr β
          (updateGroupGaugeLink L (updateGroupGaugeLink L V e'.x e'.μ (h2 e')) e.x e.μ g)) * φ g)
        (compactGroupHaarProbability G))
    (hZ2_pos : ∀ e' ∈ dobrushinNeighbors e,
      0 < groupSingleLinkPartition G L (groupWilsonAction tr β)
        (updateGroupGaugeLink L V e'.x e'.μ (h2 e')) e)
    (hE2_le_one : ∀ e' ∈ dobrushinNeighbors e,
      groupSingleLinkCondExp G L (groupWilsonAction tr β)
        (updateGroupGaugeLink L V e'.x e'.μ (h2 e')) e φ ≤ 1) :
    (∑ e' ∈ Finset.univ.erase e,
      |groupSingleLinkCondExp G L (groupWilsonAction tr β)
          (updateGroupGaugeLink L V e'.x e'.μ (h1 e')) e φ -
        groupSingleLinkCondExp G L (groupWilsonAction tr β)
          (updateGroupGaugeLink L V e'.x e'.μ (h2 e')) e φ|) ≤
      18 * (Real.exp (48 * β) - 1) := by
  rw [groupWilson_singleLinkCondExp_locality_sum_eq G tr β V e h1 h2 φ]
  have h_term (e' : Link L) (he' : e' ∈ dobrushinNeighbors e) :
      |groupSingleLinkCondExp G L (groupWilsonAction tr β)
          (updateGroupGaugeLink L V e'.x e'.μ (h1 e')) e φ -
        groupSingleLinkCondExp G L (groupWilsonAction tr β)
          (updateGroupGaugeLink L V e'.x e'.μ (h2 e')) e φ| ≤
        Real.exp (48 * β) - 1 := by
    have h_ne : e' ≠ e := fun h => not_mem_dobrushinNeighbors_self e (h ▸ he')
    let V1 := updateGroupGaugeLink L V e'.x e'.μ (h1 e')
    let V2 := updateGroupGaugeLink L V e'.x e'.μ (h2 e')
    let d0 :=
      groupWilsonAction tr β (updateGroupGaugeLink L V1 e.x e.μ 1) -
        groupWilsonAction tr β (updateGroupGaugeLink L V2 e.x e.μ 1)
    have h_diff (g : G) :
        |groupWilsonAction tr β (updateGroupGaugeLink L V1 e.x e.μ g) -
          groupWilsonAction tr β (updateGroupGaugeLink L V2 e.x e.μ g) - d0| ≤ 24 * β := by
      have h1g : updateGroupGaugeLink L V1 e.x e.μ g =
          updateTwoGroupGaugeLinks L V e.x e.μ g e'.x e'.μ (h1 e') := by
        dsimp [V1, updateTwoGroupGaugeLinks]
        exact updateGroupGaugeLink_comm L V h_ne (h1 e') g
      have h2g : updateGroupGaugeLink L V2 e.x e.μ g =
          updateTwoGroupGaugeLinks L V e.x e.μ g e'.x e'.μ (h2 e') := by
        dsimp [V2, updateTwoGroupGaugeLinks]
        exact updateGroupGaugeLink_comm L V h_ne (h2 e') g
      have h1_one : updateGroupGaugeLink L V1 e.x e.μ 1 =
          updateTwoGroupGaugeLinks L V e.x e.μ 1 e'.x e'.μ (h1 e') := by
        dsimp [V1, updateTwoGroupGaugeLinks]
        exact updateGroupGaugeLink_comm L V h_ne (h1 e') 1
      have h2_one : updateGroupGaugeLink L V2 e.x e.μ 1 =
          updateTwoGroupGaugeLinks L V e.x e.μ 1 e'.x e'.μ (h2 e') := by
        dsimp [V2, updateTwoGroupGaugeLinks]
        exact updateGroupGaugeLink_comm L V h_ne (h2 e') 1
      have h_eq :
          groupWilsonAction tr β (updateGroupGaugeLink L V1 e.x e.μ g) -
            groupWilsonAction tr β (updateGroupGaugeLink L V2 e.x e.μ g) - d0 =
          groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e.x e.μ g 1 e'.x e'.μ (h1 e') (h2 e') := by
        dsimp [d0, groupTwoLinkMixedDifference]
        rw [h1g, h2g, h1_one, h2_one]
        ring
      rw [h_eq]
      exact groupTwoLinkMixedDifference_groupWilsonAction_abs_le_twentyFour_mul_beta
        tr hβ V e e' g 1 (h1 e') (h2 e')
    have h_osc :=
      (groupSingleLinkCondExp_ratio_and_oscillation_of_action_diff_bound
        G (groupWilsonAction tr β) V1 V2 e φ
        (h_int_w1 e' he') (h_int_w2 e' he') (h_int_φ1 e' he') (h_int_φ2 e' he')
        (hZ2_pos e' he') hφ_nonneg h_diff).2.2 (hE2_le_one e' he')
    have h48 : 2 * (24 * β) = 48 * β := by ring
    rw [h48] at h_osc
    exact h_osc
  have hcard : ((dobrushinNeighbors e).card : ℝ) ≤ 18 := by
    exact_mod_cast dobrushinNeighbors_card_le_eighteen e
  have h_exp_nonneg : 0 ≤ Real.exp (48 * β) - 1 := by
    have h1 : (1 : ℝ) ≤ Real.exp (48 * β) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    linarith
  calc
    (∑ e' ∈ dobrushinNeighbors e,
      |groupSingleLinkCondExp G L (groupWilsonAction tr β)
          (updateGroupGaugeLink L V e'.x e'.μ (h1 e')) e φ -
        groupSingleLinkCondExp G L (groupWilsonAction tr β)
          (updateGroupGaugeLink L V e'.x e'.μ (h2 e')) e φ|)
      ≤ ∑ _e' ∈ dobrushinNeighbors e, (Real.exp (48 * β) - 1) :=
        Finset.sum_le_sum h_term
    _ = ((dobrushinNeighbors e).card : ℝ) * (Real.exp (48 * β) - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 18 * (Real.exp (48 * β) - 1) :=
        mul_le_mul_of_nonneg_right hcard h_exp_nonneg

/-- Rational upper bound on the exponential function for `x < 1`:
`Real.exp x ≤ 1 / (1 - x)`, derived from `1 - x ≤ Real.exp (-x)` and `Real.exp x * Real.exp (-x) = 1`. -/
theorem exp_le_one_div_one_sub {x : ℝ} (hx : x < 1) :
    Real.exp x ≤ 1 / (1 - x) := by
  have h1 : 0 < 1 - x := sub_pos.mpr hx
  rw [le_div_iff₀ h1]
  have h2 : 1 - x ≤ Real.exp (-x) := by
    have h := Real.add_one_le_exp (-x)
    linarith
  calc
    Real.exp x * (1 - x) ≤ Real.exp x * Real.exp (-x) :=
      mul_le_mul_of_nonneg_left h2 (Real.exp_pos x).le
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- Rational upper bound on `Real.exp x - 1` for `x < 1`:
`Real.exp x - 1 ≤ x / (1 - x)`. -/
theorem exp_sub_one_le_div_one_sub {x : ℝ} (hx : x < 1) :
    Real.exp x - 1 ≤ x / (1 - x) := by
  have h1 : 0 < 1 - x := sub_pos.mpr hx
  have hexp := exp_le_one_div_one_sub hx
  have hid : 1 / (1 - x) - 1 = x / (1 - x) := by
    have hne : 1 - x ≠ 0 := h1.ne'
    field_simp [hne]
    ring
  linarith

/-- Linear-in-`Δ` upper bound on `Real.exp (2 * Δ) - 1` whenever `0 ≤ Δ ≤ M` and `4 * M < 1`:
since `1 - 2 * Δ ≥ 1 - 2 * M > 1 / 2 > 0`, we have
`Real.exp (2 * Δ) - 1 ≤ (2 * Δ) / (1 - 2 * M) ≤ 4 * Δ`. -/
theorem exp_two_mul_sub_one_le_four_mul {Δ M : ℝ}
    (hΔ0 : 0 ≤ Δ) (hΔM : Δ ≤ M) (hM : 4 * M < 1) :
    Real.exp (2 * Δ) - 1 ≤ (2 * Δ) / (1 - 2 * M) ∧
    (2 * Δ) / (1 - 2 * M) ≤ 4 * Δ := by
  have h2Δ_lt_one : 2 * Δ < 1 := by linarith
  have h_den_M : (1 / 2 : ℝ) < 1 - 2 * M := by linarith
  have h_den_Δ : 1 - 2 * M ≤ 1 - 2 * Δ := by linarith
  have h_exp := exp_sub_one_le_div_one_sub h2Δ_lt_one
  have h_div1 : (2 * Δ) / (1 - 2 * Δ) ≤ (2 * Δ) / (1 - 2 * M) :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) h_den_Δ
  have h_div2 : (2 * Δ) / (1 - 2 * M) ≤ 4 * Δ := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - 2 * M)]
    nlinarith
  exact ⟨h_exp.trans h_div1, h_div2⟩

/-- Off-diagonal single-link conditional Gibbs expectation interdependence matrix entry at link pair
`(e, e')` for an arbitrary effective action `S_act : GroupGaugeConfig G L → ℝ`. -/
noncomputable def singleLinkCondExpInterdependenceMatrix
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) (S_act : GroupGaugeConfig G L → ℝ)
    (V : GroupGaugeConfig G L) (h1 h2 : Link L → G) (φ : G → ℝ)
    (e e' : Link L) : ℝ :=
  if e' = e then 0
  else
    |groupSingleLinkCondExp G L S_act (updateGroupGaugeLink L V e'.x e'.μ (h1 e')) e φ -
      groupSingleLinkCondExp G L S_act (updateGroupGaugeLink L V e'.x e'.μ (h2 e')) e φ|

theorem singleLinkCondExpInterdependenceMatrix_nonneg
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} (S_act : GroupGaugeConfig G L → ℝ)
    (V : GroupGaugeConfig G L) (h1 h2 : Link L → G) (φ : G → ℝ)
    (e e' : Link L) :
    0 ≤ singleLinkCondExpInterdependenceMatrix G L S_act V h1 h2 φ e e' := by
  unfold singleLinkCondExpInterdependenceMatrix
  split_ifs
  · exact le_rfl
  · exact abs_nonneg _

theorem sum_singleLinkCondExpInterdependenceMatrix_eq_erase
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ)
    (V : GroupGaugeConfig G L) (h1 h2 : Link L → G) (φ : G → ℝ)
    (e : Link L) :
    (∑ e' : Link L, singleLinkCondExpInterdependenceMatrix G L S_act V h1 h2 φ e e') =
      ∑ e' ∈ Finset.univ.erase e,
        |groupSingleLinkCondExp G L S_act (updateGroupGaugeLink L V e'.x e'.μ (h1 e')) e φ -
          groupSingleLinkCondExp G L S_act (updateGroupGaugeLink L V e'.x e'.μ (h2 e')) e φ| := by
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Link L)) _ (Finset.mem_univ e)]
  have h_diag : singleLinkCondExpInterdependenceMatrix G L S_act V h1 h2 φ e e = 0 := by
    simp [singleLinkCondExpInterdependenceMatrix]
  rw [h_diag, add_zero]
  refine Finset.sum_congr rfl fun e' he' => ?_
  have hne : e' ≠ e := (Finset.mem_erase.mp he').1
  simp [singleLinkCondExpInterdependenceMatrix, hne]

/-- Self-contained single-link conditional Gibbs expectation oscillation bound for any action
`S_act : GroupGaugeConfig G L → ℝ` whose single-link slice is measurable and bounded:
discharges all integrability, partition-positivity, and conditional-expectation `≤ 1` hypotheses
automatically from `compactGroupHaarProbability G`. -/
theorem groupSingleLinkCondExp_oscillation_of_measurable_and_action_diff_bound
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} (S_act : GroupGaugeConfig G L → ℝ)
    (V1 V2 : GroupGaugeConfig G L) (e : Link L) (φ : G → ℝ) {d0 Δ B : ℝ}
    (hS_meas1 : Measurable (fun g : G => S_act (updateGroupGaugeLink L V1 e.x e.μ g)))
    (hS_meas2 : Measurable (fun g : G => S_act (updateGroupGaugeLink L V2 e.x e.μ g)))
    (hS_bdd2 : ∀ g : G, |S_act (updateGroupGaugeLink L V2 e.x e.μ g)| ≤ B)
    (hφ_meas : Measurable φ)
    (hφ_bounds : ∀ g : G, 0 ≤ φ g ∧ φ g ≤ 1)
    (h_diff : ∀ g : G,
      |S_act (updateGroupGaugeLink L V1 e.x e.μ g) -
        S_act (updateGroupGaugeLink L V2 e.x e.μ g) - d0| ≤ Δ) :
    |groupSingleLinkCondExp G L S_act V1 e φ -
        groupSingleLinkCondExp G L S_act V2 e φ| ≤ Real.exp (2 * Δ) - 1 := by
  have h_w2_le (g : G) :
      Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) ≤ Real.exp B := by
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hS_bdd2 g)).1])
  have h_w2_ge (g : G) :
      Real.exp (-B) ≤ Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) := by
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hS_bdd2 g)).2])
  have h_w1_le (g : G) :
      Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)) ≤ Real.exp (B - d0 + Δ) := by
    exact Real.exp_le_exp.mpr
      (by linarith [(abs_le.mp (hS_bdd2 g)).1, (abs_le.mp (h_diff g)).1])
  have h_int_w1 :
      Integrable (fun g : G => Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)))
        (compactGroupHaarProbability G) := by
    refine (integrable_const (Real.exp (B - d0 + Δ))).mono'
      (Real.continuous_exp.measurable.comp hS_meas1.neg).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact h_w1_le g
  have h_int_w2 :
      Integrable (fun g : G => Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)))
        (compactGroupHaarProbability G) := by
    refine (integrable_const (Real.exp B)).mono'
      (Real.continuous_exp.measurable.comp hS_meas2.neg).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact h_w2_le g
  have h_int_φ1 :
      Integrable (fun g : G => Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)) * φ g)
        (compactGroupHaarProbability G) := by
    refine (integrable_const (Real.exp (B - d0 + Δ))).mono'
      ((Real.continuous_exp.measurable.comp hS_meas1.neg).mul hφ_meas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun g => by
      have h_nonneg : 0 ≤ Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)) * φ g :=
        mul_nonneg (Real.exp_pos _).le (hφ_bounds g).1
      rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
      calc
        Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)) * φ g
          ≤ Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)) * 1 :=
            mul_le_mul_of_nonneg_left (hφ_bounds g).2 (Real.exp_pos _).le
        _ = Real.exp (-S_act (updateGroupGaugeLink L V1 e.x e.μ g)) := mul_one _
        _ ≤ Real.exp (B - d0 + Δ) := h_w1_le g
  have h_int_φ2 :
      Integrable (fun g : G => Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) * φ g)
        (compactGroupHaarProbability G) := by
    refine (integrable_const (Real.exp B)).mono'
      ((Real.continuous_exp.measurable.comp hS_meas2.neg).mul hφ_meas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun g => by
      have h_nonneg : 0 ≤ Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) * φ g :=
        mul_nonneg (Real.exp_pos _).le (hφ_bounds g).1
      rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
      calc
        Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) * φ g
          ≤ Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) * 1 :=
            mul_le_mul_of_nonneg_left (hφ_bounds g).2 (Real.exp_pos _).le
        _ = Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) := mul_one _
        _ ≤ Real.exp B := h_w2_le g
  have hZ2_pos : 0 < groupSingleLinkPartition G L S_act V2 e := by
    have h_lo :
        (∫ _ : G, Real.exp (-B) ∂(compactGroupHaarProbability G : Measure G)) ≤
          groupSingleLinkPartition G L S_act V2 e :=
      integral_mono (integrable_const _) h_int_w2 h_w2_ge
    rw [integral_const, probReal_univ, one_smul] at h_lo
    exact lt_of_lt_of_le (Real.exp_pos (-B)) h_lo
  have hE2_le_one : groupSingleLinkCondExp G L S_act V2 e φ ≤ 1 := by
    unfold groupSingleLinkCondExp
    rw [div_le_iff₀ hZ2_pos, one_mul]
    refine integral_mono h_int_φ2 h_int_w2 fun g => ?_
    calc
      Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) * φ g
        ≤ Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) * 1 :=
          mul_le_mul_of_nonneg_left (hφ_bounds g).2 (Real.exp_pos _).le
      _ = Real.exp (-S_act (updateGroupGaugeLink L V2 e.x e.μ g)) := mul_one _
  exact (groupSingleLinkCondExp_ratio_and_oscillation_of_action_diff_bound
    G S_act V1 V2 e φ h_int_w1 h_int_w2 h_int_φ1 h_int_φ2 hZ2_pos
    (fun g => (hφ_bounds g).1) h_diff).2.2 hE2_le_one

/-- Exact algebraic identity expressing the centered single-link action difference
`(S_act (update V1 e g) - S_act (update V2 e g)) - (S_act (update V1 e 1) - S_act (update V2 e 1))`
for `V1 = update V e' h1`, `V2 = update V e' h2` (`e' ≠ e`) as
`groupTwoLinkMixedDifference L S_act V e.x e.μ g 1 e'.x e'.μ h1 h2`. -/
theorem centeredSingleLinkActionDiff_eq_groupTwoLinkMixedDifference
    {G : Type*} [Group G] {L : ℕ} (S_act : GroupGaugeConfig G L → ℝ)
    (V : GroupGaugeConfig G L) {e e' : Link L} (h_ne : e' ≠ e) (g h1 h2 : G) :
    let V1 := updateGroupGaugeLink L V e'.x e'.μ h1
    let V2 := updateGroupGaugeLink L V e'.x e'.μ h2
    let d0 :=
      S_act (updateGroupGaugeLink L V1 e.x e.μ 1) -
        S_act (updateGroupGaugeLink L V2 e.x e.μ 1)
    S_act (updateGroupGaugeLink L V1 e.x e.μ g) -
      S_act (updateGroupGaugeLink L V2 e.x e.μ g) - d0 =
      groupTwoLinkMixedDifference L S_act V e.x e.μ g 1 e'.x e'.μ h1 h2 := by
  intro V1 V2 d0
  have h1g : updateGroupGaugeLink L V1 e.x e.μ g =
      updateTwoGroupGaugeLinks L V e.x e.μ g e'.x e'.μ h1 :=
    updateGroupGaugeLink_comm L V h_ne h1 g
  have h2g : updateGroupGaugeLink L V2 e.x e.μ g =
      updateTwoGroupGaugeLinks L V e.x e.μ g e'.x e'.μ h2 :=
    updateGroupGaugeLink_comm L V h_ne h2 g
  have h1_one : updateGroupGaugeLink L V1 e.x e.μ 1 =
      updateTwoGroupGaugeLinks L V e.x e.μ 1 e'.x e'.μ h1 :=
    updateGroupGaugeLink_comm L V h_ne h1 1
  have h2_one : updateGroupGaugeLink L V2 e.x e.μ 1 =
      updateTwoGroupGaugeLinks L V e.x e.μ 1 e'.x e'.μ h2 :=
    updateGroupGaugeLink_comm L V h_ne h2 1
  dsimp [d0, groupTwoLinkMixedDifference]
  rw [h1g, h2g, h1_one, h2_one]
  ring

/-- Volume-uniform Dobrushin conditional Gibbs expectation interdependence row-sum theorem for an
arbitrary perturbed or blocked effective action `S_act : GroupGaugeConfig G L → ℝ` (including the
landed IR effective action `st.totalAction = c_vac + wilsonAction β + polymers.eval + R_trunc`):
if at link `e : Link L` and exterior updates `h1, h2 : Link L → G`, the two-link mixed differences
`|groupTwoLinkMixedDifference L S_act V e.x e.μ g 1 e'.x e'.μ (h1 e') (h2 e')|` are bounded by
`Δ e' ≥ 0` with torus-wide row sum `(∑ e' ∈ Finset.univ.erase e, Δ e') ≤ M` and `4 * M < 1`, then
the torus-wide single-link conditional Gibbs expectation interdependence row sum satisfies
`∑ e' : Link L, singleLinkCondExpInterdependenceMatrix G L S_act V h1 h2 φ e e' ≤ (2 * M) / (1 - 2 * M) ≤ 4 * M < 1`,
uniformly in the lattice side `L` and gauge group `G`. -/
theorem groupAction_singleLinkCondExp_interdependence_sum_le_four_mul_of_twoLink_sum
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ)
    (V : GroupGaugeConfig G L) (e : Link L) (h1 h2 : Link L → G) (φ : G → ℝ)
    (Δ : Link L → ℝ) {M B : ℝ}
    (hS_meas : ∀ (W : GroupGaugeConfig G L),
      Measurable (fun g : G => S_act (updateGroupGaugeLink L W e.x e.μ g)))
    (hS_bdd : ∀ e' ∈ Finset.univ.erase e, ∀ g : G,
      |S_act (updateGroupGaugeLink L (updateGroupGaugeLink L V e'.x e'.μ (h2 e')) e.x e.μ g)| ≤ B)
    (hφ_meas : Measurable φ)
    (hφ_bounds : ∀ g : G, 0 ≤ φ g ∧ φ g ≤ 1)
    (hΔ_nonneg : ∀ e' ∈ Finset.univ.erase e, 0 ≤ Δ e')
    (h_mixed : ∀ e' ∈ Finset.univ.erase e, ∀ g : G,
      |groupTwoLinkMixedDifference L S_act V e.x e.μ g 1 e'.x e'.μ (h1 e') (h2 e')| ≤ Δ e')
    (h_sum_le : (∑ e' ∈ Finset.univ.erase e, Δ e') ≤ M)
    (hM_lt : 4 * M < 1) :
    (∑ e' : Link L, singleLinkCondExpInterdependenceMatrix G L S_act V h1 h2 φ e e') ≤
      (2 * M) / (1 - 2 * M) ∧
    (∑ e' : Link L, singleLinkCondExpInterdependenceMatrix G L S_act V h1 h2 φ e e') ≤
      4 * M ∧
    (∑ e' : Link L, singleLinkCondExpInterdependenceMatrix G L S_act V h1 h2 φ e e') < 1 := by
  rw [sum_singleLinkCondExpInterdependenceMatrix_eq_erase]
  have hM_nonneg : 0 ≤ M :=
    le_trans (Finset.sum_nonneg hΔ_nonneg) h_sum_le
  have h_den_pos : (0 : ℝ) < 1 - 2 * M := by linarith
  have h_term (e' : Link L) (he' : e' ∈ Finset.univ.erase e) :
      |groupSingleLinkCondExp G L S_act (updateGroupGaugeLink L V e'.x e'.μ (h1 e')) e φ -
        groupSingleLinkCondExp G L S_act (updateGroupGaugeLink L V e'.x e'.μ (h2 e')) e φ| ≤
        (2 * Δ e') / (1 - 2 * M) := by
    have h_ne : e' ≠ e := (Finset.mem_erase.mp he').1
    have hΔ_le_M : Δ e' ≤ M :=
      le_trans (Finset.single_le_sum hΔ_nonneg he') h_sum_le
    let V1 := updateGroupGaugeLink L V e'.x e'.μ (h1 e')
    let V2 := updateGroupGaugeLink L V e'.x e'.μ (h2 e')
    let d0 :=
      S_act (updateGroupGaugeLink L V1 e.x e.μ 1) -
        S_act (updateGroupGaugeLink L V2 e.x e.μ 1)
    have h_diff (g : G) :
        |S_act (updateGroupGaugeLink L V1 e.x e.μ g) -
          S_act (updateGroupGaugeLink L V2 e.x e.μ g) - d0| ≤ Δ e' := by
      rw [centeredSingleLinkActionDiff_eq_groupTwoLinkMixedDifference S_act V h_ne g (h1 e') (h2 e')]
      exact h_mixed e' he' g
    have h_osc := groupSingleLinkCondExp_oscillation_of_measurable_and_action_diff_bound
      G S_act V1 V2 e φ (hS_meas V1) (hS_meas V2) (hS_bdd e' he') hφ_meas hφ_bounds h_diff
    exact h_osc.trans (exp_two_mul_sub_one_le_four_mul (hΔ_nonneg e' he') hΔ_le_M hM_lt).1
  have h_sum_div :
      (∑ e' ∈ Finset.univ.erase e,
        |groupSingleLinkCondExp G L S_act (updateGroupGaugeLink L V e'.x e'.μ (h1 e')) e φ -
          groupSingleLinkCondExp G L S_act (updateGroupGaugeLink L V e'.x e'.μ (h2 e')) e φ|) ≤
        (2 * M) / (1 - 2 * M) := by
    calc
      (∑ e' ∈ Finset.univ.erase e,
        |groupSingleLinkCondExp G L S_act (updateGroupGaugeLink L V e'.x e'.μ (h1 e')) e φ -
          groupSingleLinkCondExp G L S_act (updateGroupGaugeLink L V e'.x e'.μ (h2 e')) e φ|)
        ≤ ∑ e' ∈ Finset.univ.erase e, (2 * Δ e') / (1 - 2 * M) :=
          Finset.sum_le_sum h_term
      _ = (2 * ∑ e' ∈ Finset.univ.erase e, Δ e') / (1 - 2 * M) := by
          rw [← Finset.sum_div, ← Finset.mul_sum]
      _ ≤ (2 * M) / (1 - 2 * M) :=
          div_le_div_of_nonneg_right (by linarith) h_den_pos.le
  have h_div_le_four : (2 * M) / (1 - 2 * M) ≤ 4 * M :=
    (exp_two_mul_sub_one_le_four_mul hM_nonneg le_rfl hM_lt).2
  exact ⟨h_sum_div, h_sum_div.trans h_div_le_four, (h_sum_div.trans h_div_le_four).trans_lt hM_lt⟩

/-- Iterated `t`-step Dobrushin interdependence row sum `(C^t 1)(e)` on `Link L` for a pairwise
interdependence matrix `C : Link L → Link L → ℝ`. -/
noncomputable def dobrushinIteratedRowSum {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) : ℕ → Link L → ℝ
  | 0, _ => 1
  | t + 1, e => ∑ e' : Link L, C e e' * dobrushinIteratedRowSum C t e'

/-- Nonnegativity and geometric contraction `dobrushinIteratedRowSum C t e ≤ q ^ t` for any
non-negative interdependence matrix `C : Link L → Link L → ℝ` whose row sums are bounded by `q ≥ 0`. -/
theorem dobrushinIteratedRowSum_le_pow_of_rowSum_le {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e')
    (h_row : ∀ e : Link L, (∑ e' : Link L, C e e') ≤ q) :
    ∀ (t : ℕ) (e : Link L),
      0 ≤ dobrushinIteratedRowSum C t e ∧
      dobrushinIteratedRowSum C t e ≤ q ^ t
  | 0, _ => ⟨zero_le_one, by simp [dobrushinIteratedRowSum]⟩
  | t + 1, e => by
      have ih := dobrushinIteratedRowSum_le_pow_of_rowSum_le C hq hC_nonneg h_row t
      have h_nonneg : 0 ≤ dobrushinIteratedRowSum C (t + 1) e :=
        Finset.sum_nonneg fun e' _ => mul_nonneg (hC_nonneg e e') (ih e').1
      have h_le : dobrushinIteratedRowSum C (t + 1) e ≤ q ^ (t + 1) := by
        calc
          dobrushinIteratedRowSum C (t + 1) e
            = ∑ e' : Link L, C e e' * dobrushinIteratedRowSum C t e' := rfl
          _ ≤ ∑ e' : Link L, C e e' * q ^ t :=
              Finset.sum_le_sum fun e' _ => mul_le_mul_of_nonneg_left (ih e').2 (hC_nonneg e e')
          _ = (∑ e' : Link L, C e e') * q ^ t := by rw [← Finset.sum_mul]
          _ ≤ q * q ^ t := mul_le_mul_of_nonneg_right (h_row e) (pow_nonneg hq t)
          _ = q ^ (t + 1) := by rw [pow_succ']
      exact ⟨h_nonneg, h_le⟩

/-- Single-link oscillation $\delta_e(f) = \sup_{V, g_1, g_2} |f(V_{e \leftarrow g_1}) - f(V_{e \leftarrow g_2})|$
of an observable `f : GroupGaugeConfig G L → ℝ` at link `e : Link L`. -/
noncomputable def linkOscillation (G : Type*) (L : ℕ)
    (f : GroupGaugeConfig G L → ℝ) (e : Link L) : ℝ :=
  sSup (Set.range fun p : GroupGaugeConfig G L × G × G =>
    |f (updateGroupGaugeLink L p.1 e.x e.μ p.2.1) -
      f (updateGroupGaugeLink L p.1 e.x e.μ p.2.2)|)

theorem linkOscillation_nonneg (G : Type*) (L : ℕ)
    (f : GroupGaugeConfig G L → ℝ) (e : Link L) :
    0 ≤ linkOscillation G L f e := by
  unfold linkOscillation
  refine Real.sSup_nonneg ?_
  rintro _ ⟨p, rfl⟩
  exact abs_nonneg _

theorem linkOscillation_le_of_forall_le (G : Type*) [One G] {L : ℕ}
    (f : GroupGaugeConfig G L → ℝ) (e : Link L) {B : ℝ}
    (hB : ∀ (V : GroupGaugeConfig G L) (g1 g2 : G),
      |f (updateGroupGaugeLink L V e.x e.μ g1) -
        f (updateGroupGaugeLink L V e.x e.μ g2)| ≤ B) :
    linkOscillation G L f e ≤ B := by
  unfold linkOscillation
  have : Nonempty (GroupGaugeConfig G L × G × G) :=
    ⟨((fun _ => 1), 1, 1)⟩
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨p, rfl⟩
  exact hB p.1 p.2.1 p.2.2

theorem abs_sub_updateGroupGaugeLink_le_linkOscillation (G : Type*) {L : ℕ}
    (f : GroupGaugeConfig G L → ℝ) (e : Link L) {M : ℝ}
    (hf_bdd : ∀ U : GroupGaugeConfig G L, |f U| ≤ M)
    (V : GroupGaugeConfig G L) (g1 g2 : G) :
    |f (updateGroupGaugeLink L V e.x e.μ g1) -
      f (updateGroupGaugeLink L V e.x e.μ g2)| ≤ linkOscillation G L f e := by
  unfold linkOscillation
  refine le_csSup ?_ ⟨(V, g1, g2), rfl⟩
  refine ⟨2 * M, ?_⟩
  rintro _ ⟨p, rfl⟩
  have h1 := hf_bdd (updateGroupGaugeLink L p.1 e.x e.μ p.2.1)
  have h2 := hf_bdd (updateGroupGaugeLink L p.1 e.x e.μ p.2.2)
  calc
    |f (updateGroupGaugeLink L p.1 e.x e.μ p.2.1) -
        f (updateGroupGaugeLink L p.1 e.x e.μ p.2.2)|
      ≤ |f (updateGroupGaugeLink L p.1 e.x e.μ p.2.1)| +
          |f (updateGroupGaugeLink L p.1 e.x e.μ p.2.2)| := abs_sub _ _
    _ ≤ M + M := add_le_add h1 h2
    _ = 2 * M := by ring

theorem linkOscillation_eq_zero_of_independent (G : Type*) [One G] {L : ℕ}
    (f : GroupGaugeConfig G L → ℝ) (e : Link L)
    (h_ind : ∀ (V : GroupGaugeConfig G L) (g1 g2 : G),
      f (updateGroupGaugeLink L V e.x e.μ g1) =
        f (updateGroupGaugeLink L V e.x e.μ g2)) :
    linkOscillation G L f e = 0 := by
  refine le_antisymm ?_ (linkOscillation_nonneg G L f e)
  refine linkOscillation_le_of_forall_le G f e fun V g1 g2 => ?_
  rw [h_ind V g1 g2, sub_self, abs_zero]

/-- Set of single-link conditional Gibbs expectation variations at link `e` induced by varying link
`e'` across all configurations `V : GroupGaugeConfig G L`, link values `h1, h2 : G`, and measurable
test functions `φ : G → [0, 1]`. -/
def dobrushinInterdependenceSet (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (L : ℕ)
    (S_act : GroupGaugeConfig G L → ℝ) (e e' : Link L) : Set ℝ :=
  { r : ℝ | ∃ (V : GroupGaugeConfig G L) (h1 h2 : G) (φ : G → ℝ),
    Measurable φ ∧ (∀ g : G, 0 ≤ φ g ∧ φ g ≤ 1) ∧
    r = |groupSingleLinkCondExp G L S_act (updateGroupGaugeLink L V e'.x e'.μ h1) e φ -
          groupSingleLinkCondExp G L S_act (updateGroupGaugeLink L V e'.x e'.μ h2) e φ| }

theorem zero_mem_dobrushinInterdependenceSet (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (L : ℕ)
    (S_act : GroupGaugeConfig G L → ℝ) (e e' : Link L) :
    (0 : ℝ) ∈ dobrushinInterdependenceSet G L S_act e e' := by
  refine ⟨(fun _ => 1), 1, 1, (fun _ => 0), measurable_const,
    (fun _ => ⟨le_rfl, zero_le_one⟩), ?_⟩
  rw [sub_self, abs_zero]

theorem dobrushinInterdependenceSet_nonempty (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (L : ℕ)
    (S_act : GroupGaugeConfig G L → ℝ) (e e' : Link L) :
    (dobrushinInterdependenceSet G L S_act e e').Nonempty :=
  ⟨0, zero_mem_dobrushinInterdependenceSet G L S_act e e'⟩

/-- Dobrushin's supremum-based interdependence matrix $C_{e, e'}(S_{\mathrm{act}})$ on `Link L`:
for `e = e'`, $C_{e, e} = 0$; for `e ≠ e'`, $C_{e, e'}$ is the supremum over all configurations
`V : GroupGaugeConfig G L`, exterior link values `h1, h2 : G`, and measurable test functions
`φ : G → [0, 1]` of the conditional Gibbs expectation variation
$|\gamma_e(V_{e' \leftarrow h_1}, \varphi) - \gamma_e(V_{e' \leftarrow h_2}, \varphi)|$. -/
noncomputable def dobrushinSupMatrix (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (L : ℕ)
    (S_act : GroupGaugeConfig G L → ℝ) (e e' : Link L) : ℝ :=
  if e' = e then 0
  else sSup (dobrushinInterdependenceSet G L S_act e e')

@[simp]
theorem dobrushinSupMatrix_diag (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (L : ℕ)
    (S_act : GroupGaugeConfig G L → ℝ) (e : Link L) :
    dobrushinSupMatrix G L S_act e e = 0 := by
  simp [dobrushinSupMatrix]

theorem dobrushinSupMatrix_nonneg (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (L : ℕ)
    (S_act : GroupGaugeConfig G L → ℝ) (e e' : Link L) :
    0 ≤ dobrushinSupMatrix G L S_act e e' := by
  unfold dobrushinSupMatrix
  split_ifs
  · exact le_rfl
  · refine Real.sSup_nonneg ?_
    rintro _ ⟨V, h1, h2, φ, _, _, rfl⟩
    exact abs_nonneg _

theorem sum_dobrushinSupMatrix_eq_erase (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L]
    (S_act : GroupGaugeConfig G L → ℝ) (e : Link L) :
    (∑ e' : Link L, dobrushinSupMatrix G L S_act e e') =
      ∑ e' ∈ Finset.univ.erase e, dobrushinSupMatrix G L S_act e e' := by
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Link L)) _ (Finset.mem_univ e)]
  rw [dobrushinSupMatrix_diag, add_zero]

theorem dobrushinSupMatrix_le_of_forall (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] {L : ℕ}
    (S_act : GroupGaugeConfig G L → ℝ) {e e' : Link L} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (V : GroupGaugeConfig G L) (h1 h2 : G) (φ : G → ℝ),
      Measurable φ → (∀ g : G, 0 ≤ φ g ∧ φ g ≤ 1) →
      |groupSingleLinkCondExp G L S_act (updateGroupGaugeLink L V e'.x e'.μ h1) e φ -
        groupSingleLinkCondExp G L S_act (updateGroupGaugeLink L V e'.x e'.μ h2) e φ| ≤ B) :
    dobrushinSupMatrix G L S_act e e' ≤ B := by
  unfold dobrushinSupMatrix
  split_ifs
  · exact hB0
  · refine csSup_le (dobrushinInterdependenceSet_nonempty G L S_act e e') ?_
    rintro _ ⟨V, h1, h2, φ, hφ_meas, hφ_bounds, rfl⟩
    exact hB V h1 h2 φ hφ_meas hφ_bounds

/-- Supremum-based Dobrushin interdependence entry and row-sum theorem for an arbitrary action
`S_act : GroupGaugeConfig G L → ℝ`: if at link `e : Link L` the two-link mixed differences
`|groupTwoLinkMixedDifference L S_act V e.x e.μ g 1 e'.x e'.μ h1 h2|` are bounded uniformly across
all `V, g, h1, h2` by `Δ e' ≥ 0` with `(∑ e' ∈ Finset.univ.erase e, Δ e') ≤ M` and `4 * M < 1`,
then `dobrushinSupMatrix G L S_act e e' ≤ (2 * Δ e') / (1 - 2 * M) ≤ 4 * Δ e'` for every `e' ≠ e`,
and the torus-wide row sum satisfies
`∑ e' : Link L, dobrushinSupMatrix G L S_act e e' ≤ (2 * M) / (1 - 2 * M) ≤ 4 * M < 1`. -/
theorem dobrushinSupMatrix_rowSum_le_four_mul_of_twoLink_sum
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ)
    (e : Link L) (Δ : Link L → ℝ) {M : ℝ}
    (hS_meas : ∀ (W : GroupGaugeConfig G L),
      Measurable (fun g : G => S_act (updateGroupGaugeLink L W e.x e.μ g)))
    (hS_bdd : ∀ (W : GroupGaugeConfig G L), ∃ B : ℝ, ∀ g : G,
      |S_act (updateGroupGaugeLink L W e.x e.μ g)| ≤ B)
    (hΔ_nonneg : ∀ e' ∈ Finset.univ.erase e, 0 ≤ Δ e')
    (h_mixed : ∀ e' ∈ Finset.univ.erase e, ∀ (V : GroupGaugeConfig G L) (g h1 h2 : G),
      |groupTwoLinkMixedDifference L S_act V e.x e.μ g 1 e'.x e'.μ h1 h2| ≤ Δ e')
    (h_sum_le : (∑ e' ∈ Finset.univ.erase e, Δ e') ≤ M)
    (hM_lt : 4 * M < 1) :
    (∀ e' ∈ Finset.univ.erase e,
      dobrushinSupMatrix G L S_act e e' ≤ (2 * Δ e') / (1 - 2 * M) ∧
      dobrushinSupMatrix G L S_act e e' ≤ 4 * Δ e') ∧
    (∑ e' : Link L, dobrushinSupMatrix G L S_act e e') ≤ (2 * M) / (1 - 2 * M) ∧
    (∑ e' : Link L, dobrushinSupMatrix G L S_act e e') ≤ 4 * M ∧
    (∑ e' : Link L, dobrushinSupMatrix G L S_act e e') < 1 := by
  have hM_nonneg : 0 ≤ M :=
    le_trans (Finset.sum_nonneg hΔ_nonneg) h_sum_le
  have h_den_pos : (0 : ℝ) < 1 - 2 * M := by linarith
  have h_entry (e' : Link L) (he' : e' ∈ Finset.univ.erase e) :
      dobrushinSupMatrix G L S_act e e' ≤ (2 * Δ e') / (1 - 2 * M) ∧
      dobrushinSupMatrix G L S_act e e' ≤ 4 * Δ e' := by
    have h_ne : e' ≠ e := (Finset.mem_erase.mp he').1
    have hΔ_le_M : Δ e' ≤ M :=
      le_trans (Finset.single_le_sum hΔ_nonneg he') h_sum_le
    have h_div_nonneg : 0 ≤ (2 * Δ e') / (1 - 2 * M) :=
      div_nonneg (mul_nonneg (by norm_num) (hΔ_nonneg e' he')) h_den_pos.le
    have h_sup : dobrushinSupMatrix G L S_act e e' ≤ (2 * Δ e') / (1 - 2 * M) := by
      refine dobrushinSupMatrix_le_of_forall G S_act h_div_nonneg ?_
      intro V h1 h2 φ hφ_meas hφ_bounds
      let V1 := updateGroupGaugeLink L V e'.x e'.μ h1
      let V2 := updateGroupGaugeLink L V e'.x e'.μ h2
      rcases hS_bdd V2 with ⟨B, hB⟩
      let d0 :=
        S_act (updateGroupGaugeLink L V1 e.x e.μ 1) -
          S_act (updateGroupGaugeLink L V2 e.x e.μ 1)
      have h_diff (g : G) :
          |S_act (updateGroupGaugeLink L V1 e.x e.μ g) -
            S_act (updateGroupGaugeLink L V2 e.x e.μ g) - d0| ≤ Δ e' := by
        rw [centeredSingleLinkActionDiff_eq_groupTwoLinkMixedDifference S_act V h_ne g h1 h2]
        exact h_mixed e' he' V g h1 h2
      have h_osc := groupSingleLinkCondExp_oscillation_of_measurable_and_action_diff_bound
        G S_act V1 V2 e φ (hS_meas V1) (hS_meas V2) hB hφ_meas hφ_bounds h_diff
      exact h_osc.trans (exp_two_mul_sub_one_le_four_mul (hΔ_nonneg e' he') hΔ_le_M hM_lt).1
    have h_four : (2 * Δ e') / (1 - 2 * M) ≤ 4 * Δ e' :=
      (exp_two_mul_sub_one_le_four_mul (hΔ_nonneg e' he') hΔ_le_M hM_lt).2
    exact ⟨h_sup, h_sup.trans h_four⟩
  rw [sum_dobrushinSupMatrix_eq_erase]
  have h_sum_div :
      (∑ e' ∈ Finset.univ.erase e, dobrushinSupMatrix G L S_act e e') ≤
        (2 * M) / (1 - 2 * M) := by
    calc
      (∑ e' ∈ Finset.univ.erase e, dobrushinSupMatrix G L S_act e e')
        ≤ ∑ e' ∈ Finset.univ.erase e, (2 * Δ e') / (1 - 2 * M) :=
          Finset.sum_le_sum fun e' he' => (h_entry e' he').1
      _ = (2 * ∑ e' ∈ Finset.univ.erase e, Δ e') / (1 - 2 * M) := by
          rw [← Finset.sum_div, ← Finset.mul_sum]
      _ ≤ (2 * M) / (1 - 2 * M) :=
          div_le_div_of_nonneg_right (by linarith) h_den_pos.le
  have h_div_le_four : (2 * M) / (1 - 2 * M) ≤ 4 * M :=
    (exp_two_mul_sub_one_le_four_mul hM_nonneg le_rfl hM_lt).2
  exact ⟨h_entry, h_sum_div, h_sum_div.trans h_div_le_four,
    (h_sum_div.trans h_div_le_four).trans_lt hM_lt⟩

/-- Locality of Dobrushin's supremum matrix: if updating `e' ≠ e` leaves the centered single-link
action differences at `e` identically zero (`groupTwoLinkMixedDifference = 0`) and `S_act` has
measurable bounded slices, then `dobrushinSupMatrix G L S_act e e' = 0`. -/
theorem dobrushinSupMatrix_eq_zero_of_twoLinkMixedDifference_eq_zero
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} (S_act : GroupGaugeConfig G L → ℝ) {e e' : Link L}
    (hS_meas : ∀ (W : GroupGaugeConfig G L),
      Measurable (fun g : G => S_act (updateGroupGaugeLink L W e.x e.μ g)))
    (hS_bdd : ∀ (W : GroupGaugeConfig G L), ∃ B : ℝ, ∀ g : G,
      |S_act (updateGroupGaugeLink L W e.x e.μ g)| ≤ B)
    (h_zero : e' ≠ e → ∀ (V : GroupGaugeConfig G L) (g h1 h2 : G),
      groupTwoLinkMixedDifference L S_act V e.x e.μ g 1 e'.x e'.μ h1 h2 = 0) :
    dobrushinSupMatrix G L S_act e e' = 0 := by
  by_cases h_eq : e' = e
  · subst h_eq; exact dobrushinSupMatrix_diag G L S_act e'
  · refine le_antisymm ?_ (dobrushinSupMatrix_nonneg G L S_act e e')
    refine dobrushinSupMatrix_le_of_forall G S_act le_rfl ?_
    intro V h1 h2 φ hφ_meas hφ_bounds
    let V1 := updateGroupGaugeLink L V e'.x e'.μ h1
    let V2 := updateGroupGaugeLink L V e'.x e'.μ h2
    rcases hS_bdd V2 with ⟨B, hB⟩
    let d0 :=
      S_act (updateGroupGaugeLink L V1 e.x e.μ 1) -
        S_act (updateGroupGaugeLink L V2 e.x e.μ 1)
    have h_diff (g : G) :
        |S_act (updateGroupGaugeLink L V1 e.x e.μ g) -
          S_act (updateGroupGaugeLink L V2 e.x e.μ g) - d0| ≤ 0 := by
      rw [centeredSingleLinkActionDiff_eq_groupTwoLinkMixedDifference S_act V h_eq g h1 h2,
        h_zero h_eq V g h1 h2, abs_zero]
    have h_osc := groupSingleLinkCondExp_oscillation_of_measurable_and_action_diff_bound
      G S_act V1 V2 e φ (hS_meas V1) (hS_meas V2) hB hφ_meas hφ_bounds h_diff
    have h_exp0 : Real.exp (2 * (0 : ℝ)) - 1 = 0 := by norm_num
    rw [h_exp0] at h_osc
    exact h_osc

/-- Georgii's single-link Gibbs update operator $\Pi_{e_0} f(V) = \gamma_{e_0}(V, f(V_{e_0 \leftarrow \cdot}))$
for an effective action `S_act : GroupGaugeConfig G L → ℝ`. -/
noncomputable def singleLinkGibbsOperator (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (L : ℕ)
    (S_act : GroupGaugeConfig G L → ℝ) (e₀ : Link L)
    (f : GroupGaugeConfig G L → ℝ) (V : GroupGaugeConfig G L) : ℝ :=
  groupSingleLinkCondExp G L S_act V e₀
    (fun g : G => f (updateGroupGaugeLink L V e₀.x e₀.μ g))

/-- Updating link `e₀` before applying `singleLinkGibbsOperator` at `e₀` leaves the output unchanged,
so the single-link oscillation of `singleLinkGibbsOperator G L S_act e₀ f` at `e₀` is identically `0`
(first clause of Georgii Proposition 8.8). -/
theorem singleLinkGibbsOperator_update_self (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] {L : ℕ}
    (S_act : GroupGaugeConfig G L → ℝ) (e₀ : Link L)
    (f : GroupGaugeConfig G L → ℝ) (V : GroupGaugeConfig G L) (g₀ : G) :
    singleLinkGibbsOperator G L S_act e₀ f (updateGroupGaugeLink L V e₀.x e₀.μ g₀) =
      singleLinkGibbsOperator G L S_act e₀ f V := by
  have h_idem (g : G) :
      updateGroupGaugeLink L (updateGroupGaugeLink L V e₀.x e₀.μ g₀) e₀.x e₀.μ g =
        updateGroupGaugeLink L V e₀.x e₀.μ g := by
    funext e
    unfold updateGroupGaugeLink Function.update
    split_ifs <;> rfl
  unfold singleLinkGibbsOperator groupSingleLinkCondExp groupSingleLinkPartition
  simp_rw [h_idem]

theorem linkOscillation_singleLinkGibbsOperator_self (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] {L : ℕ}
    (S_act : GroupGaugeConfig G L → ℝ) (e₀ : Link L)
    (f : GroupGaugeConfig G L → ℝ) :
    linkOscillation G L (singleLinkGibbsOperator G L S_act e₀ f) e₀ = 0 := by
  refine linkOscillation_eq_zero_of_independent G (singleLinkGibbsOperator G L S_act e₀ f) e₀ ?_
  intro V g1 g2
  rw [singleLinkGibbsOperator_update_self, singleLinkGibbsOperator_update_self]

/-- Matrix power $(C^m)_{e, e'}$ on `Link L` for a pairwise interdependence matrix
`C : Link L → Link L → ℝ`. -/
noncomputable def dobrushinMatrixPow {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) : ℕ → Link L → Link L → ℝ
  | 0, e, e' => if e = e' then 1 else 0
  | m + 1, e, e' => ∑ e'' : Link L, C e e'' * dobrushinMatrixPow C m e'' e'

theorem dobrushinMatrixPow_nonneg {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e') :
    ∀ (m : ℕ) (e e' : Link L), 0 ≤ dobrushinMatrixPow C m e e'
  | 0, e, e' => by
      dsimp [dobrushinMatrixPow]
      split_ifs <;> norm_num
  | m + 1, e, e' =>
      Finset.sum_nonneg fun e'' _ =>
        mul_nonneg (hC_nonneg e e'') (dobrushinMatrixPow_nonneg C hC_nonneg m e'' e')

/-- Exact identity between the row sum of the matrix power `dobrushinMatrixPow C m` and
`dobrushinIteratedRowSum C m`. -/
theorem sum_dobrushinMatrixPow_eq_dobrushinIteratedRowSum {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) :
    ∀ (m : ℕ) (e : Link L),
      (∑ e' : Link L, dobrushinMatrixPow C m e e') = dobrushinIteratedRowSum C m e
  | 0, e => by
      simp [dobrushinMatrixPow, dobrushinIteratedRowSum]
  | m + 1, e => by
      dsimp [dobrushinMatrixPow, dobrushinIteratedRowSum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e'' _ => ?_
      rw [← Finset.mul_sum, sum_dobrushinMatrixPow_eq_dobrushinIteratedRowSum C m e'']

theorem sum_subset_dobrushinMatrixPow_le_pow_of_rowSum_le {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e')
    (h_row : ∀ e : Link L, (∑ e' : Link L, C e e') ≤ q)
    (S : Finset (Link L)) (m : ℕ) (e : Link L) :
    (∑ e' ∈ S, dobrushinMatrixPow C m e e') ≤ q ^ m := by
  calc
    (∑ e' ∈ S, dobrushinMatrixPow C m e e')
      ≤ ∑ e' : Link L, dobrushinMatrixPow C m e e' :=
        Finset.sum_le_univ_sum_of_nonneg fun e' => dobrushinMatrixPow_nonneg C hC_nonneg m e e'
    _ = dobrushinIteratedRowSum C m e :=
        sum_dobrushinMatrixPow_eq_dobrushinIteratedRowSum C m e
    _ ≤ q ^ m :=
        (dobrushinIteratedRowSum_le_pow_of_rowSum_le C hq hC_nonneg h_row m e).2

theorem dobrushinMatrixPow_le_pow_of_rowSum_le {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e')
    (h_row : ∀ e : Link L, (∑ e' : Link L, C e e') ≤ q)
    (m : ℕ) (e e' : Link L) :
    dobrushinMatrixPow C m e e' ≤ q ^ m := by
  simpa using
    sum_subset_dobrushinMatrixPow_le_pow_of_rowSum_le C hq hC_nonneg h_row {e'} m e

/-- Finite-speed propagation of Dobrushin matrix powers under any integer link metric/quasi-metric
`distLink : Link L → Link L → ℕ`: if `distLink e e = 0`, `distLink` obeys the triangle inequality,
and `C e e' ≠ 0 → distLink e e' ≤ 1`, then `(C^m)_{e, e'} = 0` for all `m < distLink e e'`. -/
theorem dobrushinMatrixPow_eq_zero_of_lt_dist {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) (distLink : Link L → Link L → ℕ)
    (h_refl : ∀ e : Link L, distLink e e = 0)
    (h_tri : ∀ e e'' e' : Link L, distLink e e' ≤ distLink e e'' + distLink e'' e')
    (h_step : ∀ e e' : Link L, C e e' ≠ 0 → distLink e e' ≤ 1) :
    ∀ (m : ℕ) (e e' : Link L), m < distLink e e' → dobrushinMatrixPow C m e e' = 0
  | 0, e, e', hm => by
      have hne : e ≠ e' := by
        intro h_eq
        subst h_eq
        rw [h_refl] at hm
        exact Nat.lt_irrefl 0 hm
      simp [dobrushinMatrixPow, hne]
  | m + 1, e, e', hm => by
      dsimp [dobrushinMatrixPow]
      refine Finset.sum_eq_zero fun e'' _ => ?_
      by_cases hC : C e e'' = 0
      · rw [hC, zero_mul]
      · have h_le1 : distLink e e'' ≤ 1 := h_step e e'' hC
        have h_lt : m < distLink e'' e' := by
          have h_tr := h_tri e e'' e'
          omega
        rw [dobrushinMatrixPow_eq_zero_of_lt_dist C distLink h_refl h_tri h_step m e'' e' h_lt,
          mul_zero]

/-- Dobrushin's Neumann comparison series $D_{e, e'} = \sum_{m=0}^{\infty} (C^m)_{e, e'}$. -/
noncomputable def dobrushinComparisonSeries {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) (e e' : Link L) : ℝ :=
  ∑' m : ℕ, dobrushinMatrixPow C m e e'

theorem summable_dobrushinMatrixPow_of_rowSum_lt_one {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) {q : ℝ} (hq : 0 ≤ q) (hq_lt : q < 1)
    (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e')
    (h_row : ∀ e : Link L, (∑ e' : Link L, C e e') ≤ q)
    (e e' : Link L) :
    Summable (fun m : ℕ => dobrushinMatrixPow C m e e') :=
  Summable.of_nonneg_of_le
    (fun m => dobrushinMatrixPow_nonneg C hC_nonneg m e e')
    (fun m => dobrushinMatrixPow_le_pow_of_rowSum_le C hq hC_nonneg h_row m e e')
    (summable_geometric_of_lt_one hq hq_lt)

theorem dobrushinComparisonSeries_nonneg {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e')
    (e e' : Link L) :
    0 ≤ dobrushinComparisonSeries C e e' :=
  tsum_nonneg fun m => dobrushinMatrixPow_nonneg C hC_nonneg m e e'

/-- Dobrushin–Föllmer observable comparison bilinear form
$\sum_{e, e'} \delta_e(f) \, D_{e, e'}(C) \, \delta_{e'}(g)$, which depends on the link supports
of the observables `f` and `g` via their single-link oscillations `linkOscillation G L f e` and
`linkOscillation G L g e'`. -/
noncomputable def dobrushinObservableComparison (G : Type*) {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ)
    (f g : GroupGaugeConfig G L → ℝ) : ℝ :=
  ∑ e : Link L, ∑ e' : Link L,
    linkOscillation G L f e * dobrushinComparisonSeries C e e' * linkOscillation G L g e'

/-- Distance-truncated row sum of `dobrushinComparisonSeries`: if every target link `e' ∈ S` lies
at `C`-step distance at least `t` from `e` (`∀ e' ∈ S, ∀ m < t, dobrushinMatrixPow C m e e' = 0`),
then the sum of `dobrushinComparisonSeries C e e'` over `e' ∈ S` is bounded by `q ^ t / (1 - q)`. -/
theorem sum_dobrushinComparisonSeries_le_of_vanish_lt {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) {q : ℝ} (hq : 0 ≤ q) (hq_lt : q < 1)
    (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e')
    (h_row : ∀ e : Link L, (∑ e' : Link L, C e e') ≤ q)
    (e : Link L) (S : Finset (Link L)) (t : ℕ)
    (h_vanish : ∀ e' ∈ S, ∀ m < t, dobrushinMatrixPow C m e e' = 0) :
    (∑ e' ∈ S, dobrushinComparisonSeries C e e') ≤ q ^ t / (1 - q) := by
  let a : ℕ → ℝ := fun m => ∑ e' ∈ S, dobrushinMatrixPow C m e e'
  have ha_nonneg (m : ℕ) : 0 ≤ a m :=
    Finset.sum_nonneg fun e' _ => dobrushinMatrixPow_nonneg C hC_nonneg m e e'
  have ha_le (m : ℕ) : a m ≤ q ^ m :=
    sum_subset_dobrushinMatrixPow_le_pow_of_rowSum_le C hq hC_nonneg h_row S m e
  have ha_summable : Summable a :=
    Summable.of_nonneg_of_le ha_nonneg ha_le (summable_geometric_of_lt_one hq hq_lt)
  have h_comm :
      (∑ e' ∈ S, dobrushinComparisonSeries C e e') = ∑' m : ℕ, a m := by
    unfold dobrushinComparisonSeries a
    exact (Summable.tsum_finsetSum fun e' _ =>
      summable_dobrushinMatrixPow_of_rowSum_lt_one C hq hq_lt hC_nonneg h_row e e').symm
  rw [h_comm, ← ha_summable.sum_add_tsum_nat_add t]
  have h_prefix : (∑ m ∈ Finset.range t, a m) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm_lt : m < t := Finset.mem_range.mp hm
    exact Finset.sum_eq_zero fun e' he' => h_vanish e' he' m hm_lt
  rw [h_prefix, zero_add]
  have h_shift_summable : Summable (fun k : ℕ => q ^ t * q ^ k) :=
    (summable_geometric_of_lt_one hq hq_lt).mul_left (q ^ t)
  calc
    (∑' k : ℕ, a (k + t))
      ≤ ∑' k : ℕ, (q ^ t * q ^ k) := by
        refine Summable.tsum_le_tsum ?_
          (ha_summable.comp_injective (add_left_injective t)) h_shift_summable
        intro k
        calc
          a (k + t) ≤ q ^ (k + t) := ha_le (k + t)
          _ = q ^ t * q ^ k := by rw [pow_add, mul_comm]
    _ = q ^ t * (∑' k : ℕ, q ^ k) := tsum_mul_left
    _ = q ^ t * (1 - q)⁻¹ := by rw [tsum_geometric_of_lt_one hq hq_lt]
    _ = q ^ t / (1 - q) := div_eq_mul_inv (q ^ t) (1 - q)

/-- Dobrushin's support-dependent observable comparison theorem:
if `f` has link support inside `supp_f` (`∀ e ∉ supp_f, linkOscillation G L f e = 0`),
`g` has link support inside `supp_g` (`∀ e' ∉ supp_g, linkOscillation G L g e' = 0` and
`∀ e' ∈ supp_g, linkOscillation G L g e' ≤ M_g`), and `supp_f` and `supp_g` are separated by at
least `t` steps in the link distance `distLink` (`∀ e ∈ supp_f, ∀ e' ∈ supp_g, t ≤ distLink e e'`),
then the Dobrushin comparison bilinear form obeys the exponential spatial/temporal decay bound
`dobrushinObservableComparison G C f g ≤ (∑ e ∈ supp_f, linkOscillation G L f e) * M_g * (q ^ t / (1 - q))`. -/
theorem dobrushinObservableComparison_le_of_support_dist
    (G : Type*) {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) (distLink : Link L → Link L → ℕ)
    {q M_g : ℝ} (hq : 0 ≤ q) (hq_lt : q < 1) (hMg : 0 ≤ M_g)
    (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e')
    (h_row : ∀ e : Link L, (∑ e' : Link L, C e e') ≤ q)
    (h_refl : ∀ e : Link L, distLink e e = 0)
    (h_tri : ∀ e e'' e' : Link L, distLink e e' ≤ distLink e e'' + distLink e'' e')
    (h_step : ∀ e e' : Link L, C e e' ≠ 0 → distLink e e' ≤ 1)
    (f g : GroupGaugeConfig G L → ℝ)
    (supp_f supp_g : Finset (Link L)) (t : ℕ)
    (hf_supp : ∀ e : Link L, e ∉ supp_f → linkOscillation G L f e = 0)
    (hg_supp : ∀ e' : Link L, e' ∉ supp_g → linkOscillation G L g e' = 0)
    (hg_bdd : ∀ e' ∈ supp_g, linkOscillation G L g e' ≤ M_g)
    (h_sep : ∀ e ∈ supp_f, ∀ e' ∈ supp_g, t ≤ distLink e e') :
    dobrushinObservableComparison G C f g ≤
      (∑ e ∈ supp_f, linkOscillation G L f e) * M_g * (q ^ t / (1 - q)) := by
  unfold dobrushinObservableComparison
  have h_outer :
      (∑ e : Link L, ∑ e' : Link L,
        linkOscillation G L f e * dobrushinComparisonSeries C e e' * linkOscillation G L g e') =
      ∑ e ∈ supp_f, ∑ e' ∈ supp_g,
        linkOscillation G L f e * dobrushinComparisonSeries C e e' * linkOscillation G L g e' := by
    rw [← Finset.sum_subset (Finset.subset_univ supp_f)]
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Finset.sum_subset (Finset.subset_univ supp_g)]
      intro e' _ he'
      rw [hg_supp e' he', mul_zero]
    · intro e _ he
      refine Finset.sum_eq_zero fun e' _ => ?_
      rw [hf_supp e he, zero_mul, zero_mul]
  rw [h_outer]
  have h_inner (e : Link L) (he : e ∈ supp_f) :
      (∑ e' ∈ supp_g,
        linkOscillation G L f e * dobrushinComparisonSeries C e e' * linkOscillation G L g e') ≤
      linkOscillation G L f e * M_g * (q ^ t / (1 - q)) := by
    have hf_nonneg : 0 ≤ linkOscillation G L f e := linkOscillation_nonneg G L f e
    have h_vanish (e' : Link L) (he' : e' ∈ supp_g) (m : ℕ) (hm : m < t) :
        dobrushinMatrixPow C m e e' = 0 :=
      dobrushinMatrixPow_eq_zero_of_lt_dist C distLink h_refl h_tri h_step m e e'
        (lt_of_lt_of_le hm (h_sep e he e' he'))
    have h_series :=
      sum_dobrushinComparisonSeries_le_of_vanish_lt C hq hq_lt hC_nonneg h_row e supp_g t h_vanish
    calc
      (∑ e' ∈ supp_g,
        linkOscillation G L f e * dobrushinComparisonSeries C e e' * linkOscillation G L g e')
        ≤ ∑ e' ∈ supp_g,
            linkOscillation G L f e * M_g * dobrushinComparisonSeries C e e' := by
          refine Finset.sum_le_sum fun e' he' => ?_
          have hD_nonneg := dobrushinComparisonSeries_nonneg C hC_nonneg e e'
          calc
            linkOscillation G L f e * dobrushinComparisonSeries C e e' * linkOscillation G L g e'
              ≤ linkOscillation G L f e * dobrushinComparisonSeries C e e' * M_g :=
                mul_le_mul_of_nonneg_left (hg_bdd e' he') (mul_nonneg hf_nonneg hD_nonneg)
            _ = linkOscillation G L f e * M_g * dobrushinComparisonSeries C e e' := by ring
      _ = linkOscillation G L f e * M_g * (∑ e' ∈ supp_g, dobrushinComparisonSeries C e e') := by
          rw [← Finset.mul_sum]
      _ ≤ linkOscillation G L f e * M_g * (q ^ t / (1 - q)) :=
          mul_le_mul_of_nonneg_left h_series (mul_nonneg hf_nonneg hMg)
  calc
    (∑ e ∈ supp_f, ∑ e' ∈ supp_g,
      linkOscillation G L f e * dobrushinComparisonSeries C e e' * linkOscillation G L g e')
      ≤ ∑ e ∈ supp_f, linkOscillation G L f e * M_g * (q ^ t / (1 - q)) :=
        Finset.sum_le_sum h_inner
    _ = (∑ e ∈ supp_f, linkOscillation G L f e) * M_g * (q ^ t / (1 - q)) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]

/-- Total row sum bound for Dobrushin's Neumann series:
$\sum_{e' : \mathrm{Link}\ L} D_{e, e'}(C) \le 1 / (1 - q)$. -/
theorem sum_dobrushinComparisonSeries_le_inv_sub {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) {q : ℝ} (hq : 0 ≤ q) (hq_lt : q < 1)
    (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e')
    (h_row : ∀ e : Link L, (∑ e' : Link L, C e e') ≤ q)
    (e : Link L) :
    (∑ e' : Link L, dobrushinComparisonSeries C e e') ≤ 1 / (1 - q) := by
  have h0 :=
    sum_dobrushinComparisonSeries_le_of_vanish_lt C hq hq_lt hC_nonneg h_row e Finset.univ 0
      (fun _ _ _ hm => (Nat.not_lt_zero _ hm).elim)
  simpa [pow_zero] using h0

/-- Nonnegativity of the Dobrushin–Föllmer observable comparison bilinear form. -/
theorem dobrushinObservableComparison_nonneg (G : Type*) {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e')
    (f g : GroupGaugeConfig G L → ℝ) :
    0 ≤ dobrushinObservableComparison G C f g := by
  unfold dobrushinObservableComparison
  refine Finset.sum_nonneg fun e _ => Finset.sum_nonneg fun e' _ => ?_
  exact mul_nonneg
    (mul_nonneg (linkOscillation_nonneg G L f e) (dobrushinComparisonSeries_nonneg C hC_nonneg e e'))
    (linkOscillation_nonneg G L g e')

/-- Fixed-point Neumann equation $D = I + C D$ for `dobrushinComparisonSeries`:
`dobrushinComparisonSeries C e₀ e'' = (if e₀ = e'' then 1 else 0) + ∑ e', C e₀ e' * dobrushinComparisonSeries C e' e''`. -/
theorem dobrushinComparisonSeries_eq_ite_add_sum_mul {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) {q : ℝ} (hq : 0 ≤ q) (hq_lt : q < 1)
    (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e')
    (h_row : ∀ e : Link L, (∑ e' : Link L, C e e') ≤ q)
    (e₀ e'' : Link L) :
    dobrushinComparisonSeries C e₀ e'' =
      (if e₀ = e'' then 1 else 0) +
        ∑ e' : Link L, C e₀ e' * dobrushinComparisonSeries C e' e'' := by
  have h_sum (e : Link L) : Summable (fun m : ℕ => dobrushinMatrixPow C m e e'') :=
    summable_dobrushinMatrixPow_of_rowSum_lt_one C hq hq_lt hC_nonneg h_row e e''
  have h_split := (h_sum e₀).sum_add_tsum_nat_add 1
  unfold dobrushinComparisonSeries at *
  rw [← h_split]
  have h_head :
      (∑ m ∈ Finset.range 1, dobrushinMatrixPow C m e₀ e'') =
        if e₀ = e'' then 1 else 0 := by
    simp [dobrushinMatrixPow]
  rw [h_head]
  congr 1
  have h_tail :
      (∑' m : ℕ, dobrushinMatrixPow C (m + 1) e₀ e'') =
        ∑' m : ℕ, ∑ e' : Link L, C e₀ e' * dobrushinMatrixPow C m e' e'' :=
    rfl
  rw [h_tail]
  rw [Summable.tsum_finsetSum fun e' _ => (h_sum e').mul_left (C e₀ e')]
  refine Finset.sum_congr rfl fun e' _ => ?_
  exact tsum_mul_left

/-- Total link-oscillation contraction under a single Georgii Gibbs update step at link `e₀`:
if `f'` satisfies $\delta_{e_0}(f') = 0$ and $\delta_e(f') \le \delta_e(f) + \delta_{e_0}(f)\,C_{e_0, e}$
for all $e \ne e_0$, with $C_{e_0, e_0} = 0$ and $\sum_e C_{e_0, e} \le q$, then
$\sum_e \delta_e(f') + (1 - q)\,\delta_{e_0}(f) \le \sum_e \delta_e(f)$. -/
theorem sum_linkOscillation_le_of_georgii_step
    (G : Type*) {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) {q : ℝ}
    (hC_diag : ∀ e : Link L, C e e = 0)
    (h_row : ∀ e : Link L, (∑ e' : Link L, C e e') ≤ q)
    (f f' : GroupGaugeConfig G L → ℝ) (e₀ : Link L)
    (hf'_self : linkOscillation G L f' e₀ = 0)
    (hf'_other : ∀ e : Link L, e ≠ e₀ →
      linkOscillation G L f' e ≤ linkOscillation G L f e + linkOscillation G L f e₀ * C e₀ e) :
    (∑ e : Link L, linkOscillation G L f' e) + (1 - q) * linkOscillation G L f e₀ ≤
      ∑ e : Link L, linkOscillation G L f e := by
  have h_f'_split :
      (∑ e : Link L, linkOscillation G L f' e) =
        ∑ e ∈ Finset.univ.erase e₀, linkOscillation G L f' e := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ e₀), hf'_self, zero_add]
  have h_f_split :
      (∑ e : Link L, linkOscillation G L f e) =
        linkOscillation G L f e₀ + ∑ e ∈ Finset.univ.erase e₀, linkOscillation G L f e := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ e₀)]
  have h_C_split :
      (∑ e ∈ Finset.univ.erase e₀, C e₀ e) = ∑ e : Link L, C e₀ e := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ e₀), hC_diag e₀, zero_add]
  have h_erase_le :
      (∑ e ∈ Finset.univ.erase e₀, linkOscillation G L f' e) ≤
        (∑ e ∈ Finset.univ.erase e₀, linkOscillation G L f e) +
          linkOscillation G L f e₀ * q := by
    calc
      (∑ e ∈ Finset.univ.erase e₀, linkOscillation G L f' e)
        ≤ ∑ e ∈ Finset.univ.erase e₀,
            (linkOscillation G L f e + linkOscillation G L f e₀ * C e₀ e) :=
          Finset.sum_le_sum fun e he => hf'_other e (Finset.mem_erase.mp he).1
      _ = (∑ e ∈ Finset.univ.erase e₀, linkOscillation G L f e) +
            linkOscillation G L f e₀ * (∑ e ∈ Finset.univ.erase e₀, C e₀ e) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (∑ e ∈ Finset.univ.erase e₀, linkOscillation G L f e) +
            linkOscillation G L f e₀ * (∑ e : Link L, C e₀ e) := by
          rw [h_C_split]
      _ ≤ (∑ e ∈ Finset.univ.erase e₀, linkOscillation G L f e) +
            linkOscillation G L f e₀ * q :=
          add_le_add_right
            (mul_le_mul_of_nonneg_left (h_row e₀) (linkOscillation_nonneg G L f e₀)) _
  rw [h_f'_split, h_f_split]
  linarith

/-- Dobrushin–Georgii Lyapunov Descent Theorem (`dobrushinObservableComparison_le_of_georgii_step`):
whenever `f'` satisfies Georgii's Proposition 8.8 oscillation bounds after a single-link Gibbs update
at `e₀` ($\delta_{e_0}(f') = 0$ and $\delta_e(f') \le \delta_e(f) + \delta_{e_0}(f)\,C_{e_0, e}$
for $e \ne e_0$), the Dobrushin–Föllmer observable comparison functional decreases by at least the
diagonal oscillation product $\delta_{e_0}(f)\,\delta_{e_0}(g)$:
`dobrushinObservableComparison G C f' g + linkOscillation G L f e₀ * linkOscillation G L g e₀ ≤ dobrushinObservableComparison G C f g`. -/
theorem dobrushinObservableComparison_le_of_georgii_step
    (G : Type*) {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) {q : ℝ} (hq : 0 ≤ q) (hq_lt : q < 1)
    (hC_diag : ∀ e : Link L, C e e = 0)
    (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e')
    (h_row : ∀ e : Link L, (∑ e' : Link L, C e e') ≤ q)
    (f f' g : GroupGaugeConfig G L → ℝ) (e₀ : Link L)
    (hf'_self : linkOscillation G L f' e₀ = 0)
    (hf'_other : ∀ e : Link L, e ≠ e₀ →
      linkOscillation G L f' e ≤ linkOscillation G L f e + linkOscillation G L f e₀ * C e₀ e) :
    dobrushinObservableComparison G C f' g +
      linkOscillation G L f e₀ * linkOscillation G L g e₀ ≤
      dobrushinObservableComparison G C f g := by
  have h_col (e'' : Link L) :
      (∑ e : Link L, linkOscillation G L f' e * dobrushinComparisonSeries C e e'') +
        linkOscillation G L f e₀ * (if e₀ = e'' then 1 else 0) ≤
      ∑ e : Link L, linkOscillation G L f e * dobrushinComparisonSeries C e e'' := by
    have h_f'_split :
        (∑ e : Link L, linkOscillation G L f' e * dobrushinComparisonSeries C e e'') =
          ∑ e ∈ Finset.univ.erase e₀,
            linkOscillation G L f' e * dobrushinComparisonSeries C e e'' := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ e₀), hf'_self, zero_mul, zero_add]
    have h_f_split :
        (∑ e : Link L, linkOscillation G L f e * dobrushinComparisonSeries C e e'') =
          linkOscillation G L f e₀ * dobrushinComparisonSeries C e₀ e'' +
            ∑ e ∈ Finset.univ.erase e₀,
              linkOscillation G L f e * dobrushinComparisonSeries C e e'' := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ e₀)]
    have h_C_split :
        (∑ e ∈ Finset.univ.erase e₀, C e₀ e * dobrushinComparisonSeries C e e'') =
          ∑ e : Link L, C e₀ e * dobrushinComparisonSeries C e e'' := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ e₀), hC_diag e₀, zero_mul, zero_add]
    have h_erase_le :
        (∑ e ∈ Finset.univ.erase e₀,
          linkOscillation G L f' e * dobrushinComparisonSeries C e e'') ≤
        (∑ e ∈ Finset.univ.erase e₀,
          linkOscillation G L f e * dobrushinComparisonSeries C e e'') +
          linkOscillation G L f e₀ *
            (∑ e : Link L, C e₀ e * dobrushinComparisonSeries C e e'') := by
      calc
        (∑ e ∈ Finset.univ.erase e₀,
          linkOscillation G L f' e * dobrushinComparisonSeries C e e'')
          ≤ ∑ e ∈ Finset.univ.erase e₀,
              (linkOscillation G L f e * dobrushinComparisonSeries C e e'' +
                linkOscillation G L f e₀ * (C e₀ e * dobrushinComparisonSeries C e e'')) := by
            refine Finset.sum_le_sum fun e he => ?_
            have hD := dobrushinComparisonSeries_nonneg C hC_nonneg e e''
            have h_step :=
              mul_le_mul_of_nonneg_right (hf'_other e (Finset.mem_erase.mp he).1) hD
            linarith
        _ = (∑ e ∈ Finset.univ.erase e₀,
              linkOscillation G L f e * dobrushinComparisonSeries C e e'') +
            linkOscillation G L f e₀ *
              (∑ e ∈ Finset.univ.erase e₀, C e₀ e * dobrushinComparisonSeries C e e'') := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ = (∑ e ∈ Finset.univ.erase e₀,
              linkOscillation G L f e * dobrushinComparisonSeries C e e'') +
            linkOscillation G L f e₀ *
              (∑ e : Link L, C e₀ e * dobrushinComparisonSeries C e e'') := by
            rw [h_C_split]
    have h_neumann :=
      dobrushinComparisonSeries_eq_ite_add_sum_mul C hq hq_lt hC_nonneg h_row e₀ e''
    rw [h_f'_split, h_f_split, h_neumann]
    linarith
  have h_swap (h : GroupGaugeConfig G L → ℝ) :
      dobrushinObservableComparison G C h g =
        ∑ e'' : Link L,
          (∑ e : Link L, linkOscillation G L h e * dobrushinComparisonSeries C e e'') *
            linkOscillation G L g e'' := by
    unfold dobrushinObservableComparison
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e'' _ => ?_
    rw [Finset.sum_mul]
  rw [h_swap f', h_swap f]
  have h_delta :
      linkOscillation G L f e₀ * linkOscillation G L g e₀ =
        ∑ e'' : Link L,
          (linkOscillation G L f e₀ * (if e₀ = e'' then 1 else 0)) *
            linkOscillation G L g e'' := by
    simp [Finset.sum_ite_eq]
  rw [h_delta, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e'' _ => ?_
  calc
    (∑ e : Link L, linkOscillation G L f' e * dobrushinComparisonSeries C e e'') *
        linkOscillation G L g e'' +
      linkOscillation G L f e₀ * (if e₀ = e'' then 1 else 0) * linkOscillation G L g e''
      = ((∑ e : Link L, linkOscillation G L f' e * dobrushinComparisonSeries C e e'') +
          linkOscillation G L f e₀ * (if e₀ = e'' then 1 else 0)) *
          linkOscillation G L g e'' := by ring
    _ ≤ (∑ e : Link L, linkOscillation G L f e * dobrushinComparisonSeries C e e'') *
          linkOscillation G L g e'' :=
        mul_le_mul_of_nonneg_right (h_col e'') (linkOscillation_nonneg G L g e'')

/-- Föllmer–Dobrushin Covariance Comparison Theorem (`follmer_dobrushin_covariance_comparison_of_georgii_chain`):
for any sequence of single-link updated observables `F : ℕ → GroupGaugeConfig G L → ℝ` with `F 0 = f`
along links `e_seq : ℕ → Link L` satisfying Georgii's oscillation step bounds at `e_seq k`, and any
covariance functional `cov` satisfying the single-link Gibbs step inequality
`|cov (F k) g| ≤ |cov (F (k + 1)) g| + κ * linkOscillation G L (F k) (e_seq k) * linkOscillation G L g (e_seq k)`
with `κ ≥ 0`:
1. For every step count `K : ℕ`,
   `|cov f g| + κ * dobrushinObservableComparison G C (F K) g ≤ |cov (F K) g| + κ * dobrushinObservableComparison G C f g`, and
2. Whenever `|cov (F K) g| → 0` as `K → ∞`,
   `|cov f g| ≤ κ * dobrushinObservableComparison G C f g`. -/
theorem follmer_dobrushin_covariance_comparison_of_georgii_chain
    (G : Type*) {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) {q κ : ℝ} (hq : 0 ≤ q) (hq_lt : q < 1) (hκ : 0 ≤ κ)
    (hC_diag : ∀ e : Link L, C e e = 0)
    (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e')
    (h_row : ∀ e : Link L, (∑ e' : Link L, C e e') ≤ q)
    (cov : (GroupGaugeConfig G L → ℝ) → (GroupGaugeConfig G L → ℝ) → ℝ)
    (f g : GroupGaugeConfig G L → ℝ)
    (F : ℕ → GroupGaugeConfig G L → ℝ) (e_seq : ℕ → Link L)
    (hF0 : F 0 = f)
    (h_self : ∀ k : ℕ, linkOscillation G L (F (k + 1)) (e_seq k) = 0)
    (h_other : ∀ (k : ℕ) (e : Link L), e ≠ e_seq k →
      linkOscillation G L (F (k + 1)) e ≤
        linkOscillation G L (F k) e + linkOscillation G L (F k) (e_seq k) * C (e_seq k) e)
    (h_cov_step : ∀ k : ℕ,
      |cov (F k) g| ≤
        |cov (F (k + 1)) g| +
          κ * (linkOscillation G L (F k) (e_seq k) * linkOscillation G L g (e_seq k))) :
    (∀ K : ℕ,
      |cov f g| + κ * dobrushinObservableComparison G C (F K) g ≤
        |cov (F K) g| + κ * dobrushinObservableComparison G C f g) ∧
    (Filter.Tendsto (fun K : ℕ => |cov (F K) g|) Filter.atTop (nhds 0) →
      |cov f g| ≤ κ * dobrushinObservableComparison G C f g) := by
  have h_finite : ∀ K : ℕ,
      |cov f g| + κ * dobrushinObservableComparison G C (F K) g ≤
        |cov (F K) g| + κ * dobrushinObservableComparison G C f g := by
    intro K
    induction K with
    | zero =>
        rw [hF0]
    | succ k ih =>
        have h_lyap :=
          dobrushinObservableComparison_le_of_georgii_step G C hq hq_lt hC_diag hC_nonneg h_row
            (F k) (F (k + 1)) g (e_seq k) (h_self k) (h_other k)
        have h_mul := mul_le_mul_of_nonneg_left h_lyap hκ
        have h_step := h_cov_step k
        linarith
  refine ⟨h_finite, fun h_tendsto => ?_⟩
  have h_le_event (K : ℕ) :
      |cov f g| ≤ |cov (F K) g| + κ * dobrushinObservableComparison G C f g := by
    have h_nonneg : 0 ≤ κ * dobrushinObservableComparison G C (F K) g :=
      mul_nonneg hκ (dobrushinObservableComparison_nonneg G C hC_nonneg (F K) g)
    linarith [h_finite K]
  have h_lim :
      Filter.Tendsto
        (fun K : ℕ => |cov (F K) g| + κ * dobrushinObservableComparison G C f g)
        Filter.atTop (nhds (0 + κ * dobrushinObservableComparison G C f g)) :=
    h_tendsto.add tendsto_const_nhds
  rw [zero_add] at h_lim
  exact le_of_tendsto_of_tendsto tendsto_const_nhds h_lim (Filter.Eventually.of_forall h_le_event)

/-- Affine linearity of `groupSingleLinkCondExp`: for a measurable bounded action slice and a
measurable bounded test function `ψ : G → ℝ`,
`groupSingleLinkCondExp G L S_act W e₀ (fun g => c + d * ψ g) = c + d * groupSingleLinkCondExp G L S_act W e₀ ψ`. -/
theorem groupSingleLinkCondExp_const_add_mul
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} (S_act : GroupGaugeConfig G L → ℝ)
    (W : GroupGaugeConfig G L) (e₀ : Link L) (c d : ℝ) (ψ : G → ℝ)
    (hS_meas : Measurable (fun g : G => S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)))
    (hS_bdd : ∃ B : ℝ, ∀ g : G, |S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)| ≤ B)
    (hψ_meas : Measurable ψ)
    (hψ_bdd : ∃ M : ℝ, ∀ g : G, |ψ g| ≤ M) :
    groupSingleLinkCondExp G L S_act W e₀ (fun g : G => c + d * ψ g) =
      c + d * groupSingleLinkCondExp G L S_act W e₀ ψ := by
  rcases hS_bdd with ⟨B, hB⟩
  rcases hψ_bdd with ⟨M, hM⟩
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (hM 1)
  have h_w_le (g : G) :
      Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) ≤ Real.exp B := by
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp (hB g)).1
    linarith
  have h_w_ge (g : G) :
      Real.exp (-B) ≤ Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) := by
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp (hB g)).2
    linarith
  have h_int_w :
      Integrable (fun g : G => Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)))
        (compactGroupHaarProbability G) := by
    refine (integrable_const (Real.exp B)).mono'
      (Real.continuous_exp.measurable.comp hS_meas.neg).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact h_w_le g
  have h_int_wψ :
      Integrable (fun g : G => Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * ψ g)
        (compactGroupHaarProbability G) := by
    refine (integrable_const (Real.exp B * M)).mono'
      ((Real.continuous_exp.measurable.comp hS_meas.neg).mul hψ_meas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (h_w_le g) (hM g) (abs_nonneg _) (Real.exp_pos _).le
  have hZ_pos : 0 < groupSingleLinkPartition G L S_act W e₀ := by
    have h_lo :
        (∫ _ : G, Real.exp (-B) ∂(compactGroupHaarProbability G : Measure G)) ≤
          groupSingleLinkPartition G L S_act W e₀ :=
      integral_mono (integrable_const _) h_int_w h_w_ge
    rw [integral_const, probReal_univ, one_smul] at h_lo
    exact lt_of_lt_of_le (Real.exp_pos (-B)) h_lo
  have h_expand (g : G) :
      Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * (c + d * ψ g) =
        c * Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) +
          d * (Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * ψ g) := by
    ring
  unfold groupSingleLinkCondExp
  simp_rw [h_expand]
  rw [integral_add (h_int_w.const_mul c) (h_int_wψ.const_mul d),
    integral_const_mul, integral_const_mul]
  change (c * groupSingleLinkPartition G L S_act W e₀ +
    d * ∫ g : G, Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * ψ g
      ∂(compactGroupHaarProbability G : Measure G)) /
    groupSingleLinkPartition G L S_act W e₀ = _
  rw [add_div, mul_div_cancel_right₀ c hZ_pos.ne', mul_div_assoc]

/-- Contraction of `groupSingleLinkCondExp` under a uniform integrand difference bound
`∀ g : G, |φ₁ g - φ₂ g| ≤ δ`. -/
theorem abs_groupSingleLinkCondExp_sub_le_of_abs_sub_le
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} (S_act : GroupGaugeConfig G L → ℝ)
    (W : GroupGaugeConfig G L) (e₀ : Link L) (φ₁ φ₂ : G → ℝ) {δ : ℝ}
    (hS_meas : Measurable (fun g : G => S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)))
    (hS_bdd : ∃ B : ℝ, ∀ g : G, |S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)| ≤ B)
    (hφ₁_meas : Measurable φ₁) (hφ₂_meas : Measurable φ₂)
    (hφ₁_bdd : ∃ M : ℝ, ∀ g : G, |φ₁ g| ≤ M)
    (hφ₂_bdd : ∃ M : ℝ, ∀ g : G, |φ₂ g| ≤ M)
    (h_diff : ∀ g : G, |φ₁ g - φ₂ g| ≤ δ) :
    |groupSingleLinkCondExp G L S_act W e₀ φ₁ -
      groupSingleLinkCondExp G L S_act W e₀ φ₂| ≤ δ := by
  have hδ_nonneg : 0 ≤ δ := le_trans (abs_nonneg _) (h_diff 1)
  rcases hS_bdd with ⟨B, hB⟩
  rcases hφ₁_bdd with ⟨M₁, hM₁⟩
  rcases hφ₂_bdd with ⟨M₂, hM₂⟩
  have h_w_le (g : G) :
      Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) ≤ Real.exp B := by
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp (hB g)).1
    linarith
  have h_w_ge (g : G) :
      Real.exp (-B) ≤ Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) := by
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp (hB g)).2
    linarith
  have h_int_w :
      Integrable (fun g : G => Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)))
        (compactGroupHaarProbability G) := by
    refine (integrable_const (Real.exp B)).mono'
      (Real.continuous_exp.measurable.comp hS_meas.neg).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact h_w_le g
  have h_int_φ₁ :
      Integrable (fun g : G => Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * φ₁ g)
        (compactGroupHaarProbability G) := by
    refine (integrable_const (Real.exp B * M₁)).mono'
      ((Real.continuous_exp.measurable.comp hS_meas.neg).mul hφ₁_meas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (h_w_le g) (hM₁ g) (abs_nonneg _) (Real.exp_pos _).le
  have h_int_φ₂ :
      Integrable (fun g : G => Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * φ₂ g)
        (compactGroupHaarProbability G) := by
    refine (integrable_const (Real.exp B * M₂)).mono'
      ((Real.continuous_exp.measurable.comp hS_meas.neg).mul hφ₂_meas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (h_w_le g) (hM₂ g) (abs_nonneg _) (Real.exp_pos _).le
  have hZ_pos : 0 < groupSingleLinkPartition G L S_act W e₀ := by
    have h_lo :
        (∫ _ : G, Real.exp (-B) ∂(compactGroupHaarProbability G : Measure G)) ≤
          groupSingleLinkPartition G L S_act W e₀ :=
      integral_mono (integrable_const _) h_int_w h_w_ge
    rw [integral_const, probReal_univ, one_smul] at h_lo
    exact lt_of_lt_of_le (Real.exp_pos (-B)) h_lo
  unfold groupSingleLinkCondExp
  rw [← sub_div, abs_div, abs_of_pos hZ_pos, div_le_iff₀ hZ_pos, ← integral_sub h_int_φ₁ h_int_φ₂]
  have h_int_abs :
      Integrable (fun g : G =>
        |Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * φ₁ g -
          Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * φ₂ g|)
        (compactGroupHaarProbability G) :=
    (h_int_φ₁.sub h_int_φ₂).abs
  calc
    |∫ g : G,
        (Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * φ₁ g -
          Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * φ₂ g)
        ∂(compactGroupHaarProbability G : Measure G)|
      ≤ ∫ g : G,
          |Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * φ₁ g -
            Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * φ₂ g|
          ∂(compactGroupHaarProbability G : Measure G) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ g : G, Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * δ
          ∂(compactGroupHaarProbability G : Measure G) := by
        refine integral_mono h_int_abs (h_int_w.mul_const δ) fun g => ?_
        dsimp only
        rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (h_diff g) (Real.exp_pos _).le
    _ = δ * groupSingleLinkPartition G L S_act W e₀ := by
        unfold groupSingleLinkPartition
        rw [integral_mul_const, mul_comm]

/-- For any measurable bounded action slice and `[0, 1]`-valued measurable test function `ψ : G → ℝ`,
`0 ≤ groupSingleLinkCondExp G L S_act W e₀ ψ ≤ 1`. -/
theorem groupSingleLinkCondExp_bounds_zero_one
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} (S_act : GroupGaugeConfig G L → ℝ)
    (W : GroupGaugeConfig G L) (e₀ : Link L) (ψ : G → ℝ)
    (hS_meas : Measurable (fun g : G => S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)))
    (hS_bdd : ∃ B : ℝ, ∀ g : G, |S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)| ≤ B)
    (hψ_meas : Measurable ψ)
    (hψ_bounds : ∀ g : G, 0 ≤ ψ g ∧ ψ g ≤ 1) :
    0 ≤ groupSingleLinkCondExp G L S_act W e₀ ψ ∧
      groupSingleLinkCondExp G L S_act W e₀ ψ ≤ 1 := by
  rcases hS_bdd with ⟨B, hB⟩
  have h_w_le (g : G) :
      Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) ≤ Real.exp B := by
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp (hB g)).1
    linarith
  have h_w_ge (g : G) :
      Real.exp (-B) ≤ Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) := by
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp (hB g)).2
    linarith
  have h_int_w :
      Integrable (fun g : G => Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)))
        (compactGroupHaarProbability G) := by
    refine (integrable_const (Real.exp B)).mono'
      (Real.continuous_exp.measurable.comp hS_meas.neg).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact h_w_le g
  have h_int_ψ :
      Integrable (fun g : G => Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * ψ g)
        (compactGroupHaarProbability G) := by
    refine (integrable_const (Real.exp B)).mono'
      ((Real.continuous_exp.measurable.comp hS_meas.neg).mul hψ_meas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun g => by
      have h_nonneg : 0 ≤ Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * ψ g :=
        mul_nonneg (Real.exp_pos _).le (hψ_bounds g).1
      rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
      calc
        Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * ψ g
          ≤ Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * 1 :=
            mul_le_mul_of_nonneg_left (hψ_bounds g).2 (Real.exp_pos _).le
        _ = Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) := mul_one _
        _ ≤ Real.exp B := h_w_le g
  have hZ_pos : 0 < groupSingleLinkPartition G L S_act W e₀ := by
    have h_lo :
        (∫ _ : G, Real.exp (-B) ∂(compactGroupHaarProbability G : Measure G)) ≤
          groupSingleLinkPartition G L S_act W e₀ :=
      integral_mono (integrable_const _) h_int_w h_w_ge
    rw [integral_const, probReal_univ, one_smul] at h_lo
    exact lt_of_lt_of_le (Real.exp_pos (-B)) h_lo
  refine ⟨?_, ?_⟩
  · unfold groupSingleLinkCondExp
    exact div_nonneg
      (integral_nonneg fun g => mul_nonneg (Real.exp_pos _).le (hψ_bounds g).1)
      hZ_pos.le
  · unfold groupSingleLinkCondExp
    rw [div_le_iff₀ hZ_pos, one_mul]
    refine integral_mono h_int_ψ h_int_w fun g => ?_
    calc
      Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * ψ g
        ≤ Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) * 1 :=
          mul_le_mul_of_nonneg_left (hψ_bounds g).2 (Real.exp_pos _).le
      _ = Real.exp (-S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)) := mul_one _

/-- Every variation in `dobrushinInterdependenceSet G L S_act e₀ e` is bounded above by `1` whenever
`S_act` has measurable bounded slices at `e₀`. -/
theorem bddAbove_dobrushinInterdependenceSet
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} (S_act : GroupGaugeConfig G L → ℝ) (e₀ e : Link L)
    (hS_meas : ∀ W : GroupGaugeConfig G L,
      Measurable (fun g : G => S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)))
    (hS_bdd : ∀ W : GroupGaugeConfig G L,
      ∃ B : ℝ, ∀ g : G, |S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)| ≤ B) :
    BddAbove (dobrushinInterdependenceSet G L S_act e₀ e) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨V, h1, h2, φ, hφ_meas, hφ_bounds, rfl⟩
  have h1_b := groupSingleLinkCondExp_bounds_zero_one G S_act
    (updateGroupGaugeLink L V e.x e.μ h1) e₀ φ (hS_meas _) (hS_bdd _) hφ_meas hφ_bounds
  have h2_b := groupSingleLinkCondExp_bounds_zero_one G S_act
    (updateGroupGaugeLink L V e.x e.μ h2) e₀ φ (hS_meas _) (hS_bdd _) hφ_meas hφ_bounds
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Georgii Proposition 8.8 (second clause) for `singleLinkGibbsOperator` on `GroupGaugeConfig G L`:
for any link `e ≠ e₀`, applying the single-link Gibbs operator at `e₀` satisfies
`linkOscillation G L (singleLinkGibbsOperator G L S_act e₀ f) e ≤ linkOscillation G L f e + linkOscillation G L f e₀ * dobrushinSupMatrix G L S_act e₀ e`. -/
theorem linkOscillation_singleLinkGibbsOperator_le_of_ne
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} (S_act : GroupGaugeConfig G L → ℝ)
    (e₀ e : Link L) (he : e ≠ e₀)
    (f : GroupGaugeConfig G L → ℝ)
    (hS_meas : ∀ W : GroupGaugeConfig G L,
      Measurable (fun g : G => S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)))
    (hS_bdd : ∀ W : GroupGaugeConfig G L,
      ∃ B : ℝ, ∀ g : G, |S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)| ≤ B)
    (hf_meas : ∀ W : GroupGaugeConfig G L,
      Measurable (fun g : G => f (updateGroupGaugeLink L W e₀.x e₀.μ g)))
    (hf_bdd : ∃ M : ℝ, ∀ U : GroupGaugeConfig G L, |f U| ≤ M) :
    linkOscillation G L (singleLinkGibbsOperator G L S_act e₀ f) e ≤
      linkOscillation G L f e +
        linkOscillation G L f e₀ * dobrushinSupMatrix G L S_act e₀ e := by
  rcases hf_bdd with ⟨M, hM⟩
  refine linkOscillation_le_of_forall_le G (singleLinkGibbsOperator G L S_act e₀ f) e ?_
  intro V h1 h2
  let V1 := updateGroupGaugeLink L V e.x e.μ h1
  let V2 := updateGroupGaugeLink L V e.x e.μ h2
  let φ₁ : G → ℝ := fun g => f (updateGroupGaugeLink L V1 e₀.x e₀.μ g)
  let φ₂ : G → ℝ := fun g => f (updateGroupGaugeLink L V2 e₀.x e₀.μ g)
  have h_term1 :
      |groupSingleLinkCondExp G L S_act V1 e₀ φ₁ -
        groupSingleLinkCondExp G L S_act V1 e₀ φ₂| ≤
      linkOscillation G L f e := by
    refine abs_groupSingleLinkCondExp_sub_le_of_abs_sub_le G S_act V1 e₀ φ₁ φ₂
      (hS_meas V1) (hS_bdd V1) (hf_meas V1) (hf_meas V2)
      ⟨M, fun g => hM _⟩ ⟨M, fun g => hM _⟩ fun g => ?_
    dsimp [φ₁, φ₂, V1, V2]
    rw [updateGroupGaugeLink_comm L V he h1 g, updateGroupGaugeLink_comm L V he h2 g]
    exact abs_sub_updateGroupGaugeLink_le_linkOscillation G f e hM
      (updateGroupGaugeLink L V e₀.x e₀.μ g) h1 h2
  have h_term2 :
      |groupSingleLinkCondExp G L S_act V1 e₀ φ₂ -
        groupSingleLinkCondExp G L S_act V2 e₀ φ₂| ≤
      linkOscillation G L f e₀ * dobrushinSupMatrix G L S_act e₀ e := by
    let c : ℝ := sInf (Set.range φ₂)
    let d : ℝ := linkOscillation G L f e₀
    have hd_nonneg : 0 ≤ d := linkOscillation_nonneg G L f e₀
    have h_range_bdd : BddBelow (Set.range φ₂) := by
      refine ⟨-M, ?_⟩
      rintro _ ⟨g, rfl⟩
      exact (abs_le.mp (hM _)).1
    have h_range_nonempty : (Set.range φ₂).Nonempty := ⟨φ₂ 1, 1, rfl⟩
    have hc_le (g : G) : c ≤ φ₂ g := csInf_le h_range_bdd ⟨g, rfl⟩
    have hφ₂_sub_le (g : G) : φ₂ g - c ≤ d := by
      have hc_ge : φ₂ g - d ≤ c := by
        refine le_csInf h_range_nonempty ?_
        rintro _ ⟨g', rfl⟩
        have h_osc := abs_sub_updateGroupGaugeLink_le_linkOscillation G f e₀ hM V2 g g'
        have h_up := (abs_le.mp h_osc).2
        dsimp [φ₂, d] at *
        linarith
      linarith
    by_cases hd0 : d = 0
    · have hφ₂_const (g : G) : φ₂ g = c + 0 * (0 : ℝ) := by
        have h1_le := hc_le g
        have h2_le := hφ₂_sub_le g
        linarith
      have hφ₂_eq : φ₂ = fun _ : G => c + 0 * (0 : ℝ) := funext hφ₂_const
      rw [hφ₂_eq,
        groupSingleLinkCondExp_const_add_mul G S_act V1 e₀ c 0 (fun _ => 0)
          (hS_meas V1) (hS_bdd V1) measurable_const ⟨0, fun _ => by simp⟩,
        groupSingleLinkCondExp_const_add_mul G S_act V2 e₀ c 0 (fun _ => 0)
          (hS_meas V2) (hS_bdd V2) measurable_const ⟨0, fun _ => by simp⟩]
      simp [d, hd0]
    · have hd_pos : 0 < d := lt_of_le_of_ne hd_nonneg (Ne.symm hd0)
      let ψ : G → ℝ := fun g => (φ₂ g - c) / d
      have hψ_meas : Measurable ψ := ((hf_meas V2).sub measurable_const).div_const d
      have hψ_bounds (g : G) : 0 ≤ ψ g ∧ ψ g ≤ 1 := by
        refine ⟨div_nonneg (sub_nonneg.mpr (hc_le g)) hd_pos.le, ?_⟩
        rw [div_le_iff₀ hd_pos, one_mul]
        exact hφ₂_sub_le g
      have hφ₂_decomp : φ₂ = fun g : G => c + d * ψ g := by
        funext g
        dsimp [ψ]
        rw [mul_div_cancel₀ _ hd_pos.ne']
        ring
      have hψ_bdd : ∃ M_ψ : ℝ, ∀ g : G, |ψ g| ≤ M_ψ := by
        refine ⟨1, fun g => abs_le.mpr ⟨by linarith [(hψ_bounds g).1], (hψ_bounds g).2⟩⟩
      have h_lin1 := groupSingleLinkCondExp_const_add_mul G S_act V1 e₀ c d ψ
        (hS_meas V1) (hS_bdd V1) hψ_meas hψ_bdd
      have h_lin2 := groupSingleLinkCondExp_const_add_mul G S_act V2 e₀ c d ψ
        (hS_meas V2) (hS_bdd V2) hψ_meas hψ_bdd
      have h_sub :
          groupSingleLinkCondExp G L S_act V1 e₀ φ₂ -
            groupSingleLinkCondExp G L S_act V2 e₀ φ₂ =
          d * (groupSingleLinkCondExp G L S_act V1 e₀ ψ -
            groupSingleLinkCondExp G L S_act V2 e₀ ψ) := by
        rw [hφ₂_decomp, h_lin1, h_lin2]
        ring
      rw [h_sub, abs_mul, abs_of_pos hd_pos]
      refine mul_le_mul_of_nonneg_left ?_ hd_pos.le
      unfold dobrushinSupMatrix
      simp only [he, ↓reduceIte]
      refine le_csSup (bddAbove_dobrushinInterdependenceSet G S_act e₀ e hS_meas hS_bdd) ?_
      exact ⟨V, h1, h2, ψ, hψ_meas, hψ_bounds, rfl⟩
  change |groupSingleLinkCondExp G L S_act V1 e₀ φ₁ -
      groupSingleLinkCondExp G L S_act V2 e₀ φ₂| ≤ _
  calc
    |groupSingleLinkCondExp G L S_act V1 e₀ φ₁ -
        groupSingleLinkCondExp G L S_act V2 e₀ φ₂|
      = |(groupSingleLinkCondExp G L S_act V1 e₀ φ₁ -
          groupSingleLinkCondExp G L S_act V1 e₀ φ₂) +
        (groupSingleLinkCondExp G L S_act V1 e₀ φ₂ -
          groupSingleLinkCondExp G L S_act V2 e₀ φ₂)| := by ring_nf
    _ ≤ |groupSingleLinkCondExp G L S_act V1 e₀ φ₁ -
          groupSingleLinkCondExp G L S_act V1 e₀ φ₂| +
        |groupSingleLinkCondExp G L S_act V1 e₀ φ₂ -
          groupSingleLinkCondExp G L S_act V2 e₀ φ₂| := abs_add_le _ _
    _ ≤ linkOscillation G L f e +
          linkOscillation G L f e₀ * dobrushinSupMatrix G L S_act e₀ e :=
      add_le_add h_term1 h_term2

/-- Direct specialization of total link-oscillation contraction (`sum_linkOscillation_le_of_georgii_step`)
to `singleLinkGibbsOperator G L S_act e₀ f` and `dobrushinSupMatrix G L S_act`. -/
theorem sum_linkOscillation_singleLinkGibbsOperator_le
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ)
    {q : ℝ}
    (h_row : ∀ e : Link L, (∑ e' : Link L, dobrushinSupMatrix G L S_act e e') ≤ q)
    (e₀ : Link L) (f : GroupGaugeConfig G L → ℝ)
    (hS_meas : ∀ W : GroupGaugeConfig G L,
      Measurable (fun g : G => S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)))
    (hS_bdd : ∀ W : GroupGaugeConfig G L,
      ∃ B : ℝ, ∀ g : G, |S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)| ≤ B)
    (hf_meas : ∀ W : GroupGaugeConfig G L,
      Measurable (fun g : G => f (updateGroupGaugeLink L W e₀.x e₀.μ g)))
    (hf_bdd : ∃ M : ℝ, ∀ U : GroupGaugeConfig G L, |f U| ≤ M) :
    (∑ e : Link L, linkOscillation G L (singleLinkGibbsOperator G L S_act e₀ f) e) +
      (1 - q) * linkOscillation G L f e₀ ≤
      ∑ e : Link L, linkOscillation G L f e :=
  sum_linkOscillation_le_of_georgii_step G (dobrushinSupMatrix G L S_act)
    (dobrushinSupMatrix_diag G L S_act) h_row f
    (singleLinkGibbsOperator G L S_act e₀ f) e₀
    (linkOscillation_singleLinkGibbsOperator_self G S_act e₀ f)
    (fun e he =>
      linkOscillation_singleLinkGibbsOperator_le_of_ne G S_act e₀ e he f
        hS_meas hS_bdd hf_meas hf_bdd)

/-- Direct specialization of the Dobrushin–Georgii Lyapunov Descent Theorem
(`dobrushinObservableComparison_le_of_georgii_step`) to `singleLinkGibbsOperator G L S_act e₀ f`
and `dobrushinSupMatrix G L S_act`. -/
theorem dobrushinObservableComparison_singleLinkGibbsOperator_le
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ)
    {q : ℝ} (hq : 0 ≤ q) (hq_lt : q < 1)
    (h_row : ∀ e : Link L, (∑ e' : Link L, dobrushinSupMatrix G L S_act e e') ≤ q)
    (e₀ : Link L) (f g : GroupGaugeConfig G L → ℝ)
    (hS_meas : ∀ W : GroupGaugeConfig G L,
      Measurable (fun g : G => S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)))
    (hS_bdd : ∀ W : GroupGaugeConfig G L,
      ∃ B : ℝ, ∀ g : G, |S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)| ≤ B)
    (hf_meas : ∀ W : GroupGaugeConfig G L,
      Measurable (fun g : G => f (updateGroupGaugeLink L W e₀.x e₀.μ g)))
    (hf_bdd : ∃ M : ℝ, ∀ U : GroupGaugeConfig G L, |f U| ≤ M) :
    dobrushinObservableComparison G (dobrushinSupMatrix G L S_act)
      (singleLinkGibbsOperator G L S_act e₀ f) g +
      linkOscillation G L f e₀ * linkOscillation G L g e₀ ≤
      dobrushinObservableComparison G (dobrushinSupMatrix G L S_act) f g :=
  dobrushinObservableComparison_le_of_georgii_step G (dobrushinSupMatrix G L S_act)
    hq hq_lt (dobrushinSupMatrix_diag G L S_act) (dobrushinSupMatrix_nonneg G L S_act) h_row
    f (singleLinkGibbsOperator G L S_act e₀ f) g e₀
    (linkOscillation_singleLinkGibbsOperator_self G S_act e₀ f)
    (fun e he =>
      linkOscillation_singleLinkGibbsOperator_le_of_ne G S_act e₀ e he f
        hS_meas hS_bdd hf_meas hf_bdd)

/-! ### Boundedness Requirement, Vacuity Self-Refutation, Greedy Georgii Sweeps & Unconditional Föllmer–Dobrushin Covariance Comparison on `groupGibbsMeasure` -/

/-- In Lean's `Real.sSup`, if the single-link variation set of `f` at `e` is not bounded above,
`linkOscillation G L f e` evaluates to `0` by `Real.sSup_of_not_bddAbove`. -/
theorem linkOscillation_eq_zero_of_not_bddAbove (G : Type*) {L : ℕ}
    (f : GroupGaugeConfig G L → ℝ) (e : Link L)
    (h_unbdd : ∀ B : ℝ, ∃ (V : GroupGaugeConfig G L) (g1 g2 : G),
      B < |f (updateGroupGaugeLink L V e.x e.μ g1) -
        f (updateGroupGaugeLink L V e.x e.μ g2)|) :
    linkOscillation G L f e = 0 := by
  unfold linkOscillation
  apply Real.sSup_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨V, g1, g2, h_gt⟩ := h_unbdd B
  have h_le :
      |f (updateGroupGaugeLink L V e.x e.μ g1) -
        f (updateGroupGaugeLink L V e.x e.μ g2)| ≤ B :=
    hB ⟨(V, g1, g2), rfl⟩
  linarith

/-- Self-refutation of an unrestricted Dobrushin covariance comparison inequality
(`∀ f g, |cov f g| ≤ κ * dobrushinObservableComparison G C f g`) without a boundedness
hypothesis on `f`: if `f` depends only on a single link `e₀` and has unbounded variation on `e₀`,
then `linkOscillation G L f e = 0` for every link `e : Link L` (at `e = e₀` by `Real.sSup_of_not_bddAbove`
and at `e ≠ e₀` by independence), so `dobrushinObservableComparison G C f g = 0`, contradicting
any observable pair `(f, g)` (such as `g = min f 1`) with `cov f g ≠ 0`. -/
theorem not_unrestricted_dobrushin_comparison_of_unbounded_singleLink
    (G : Type*) [One G] {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ)
    (cov : (GroupGaugeConfig G L → ℝ) → (GroupGaugeConfig G L → ℝ) → ℝ)
    (κ : ℝ) (e₀ : Link L) (f g : GroupGaugeConfig G L → ℝ)
    (h_unbdd : ∀ B : ℝ, ∃ (V : GroupGaugeConfig G L) (g1 g2 : G),
      B < |f (updateGroupGaugeLink L V e₀.x e₀.μ g1) -
        f (updateGroupGaugeLink L V e₀.x e₀.μ g2)|)
    (h_ind : ∀ (e : Link L), e ≠ e₀ → ∀ (V : GroupGaugeConfig G L) (g1 g2 : G),
      f (updateGroupGaugeLink L V e.x e.μ g1) =
        f (updateGroupGaugeLink L V e.x e.μ g2))
    (h_cov_ne : cov f g ≠ 0)
    (h_unrestricted : ∀ f₁ g₁ : GroupGaugeConfig G L → ℝ,
      |cov f₁ g₁| ≤ κ * dobrushinObservableComparison G C f₁ g₁) :
    False := by
  have h_osc_zero (e : Link L) : linkOscillation G L f e = 0 := by
    by_cases he : e = e₀
    · subst he
      exact linkOscillation_eq_zero_of_not_bddAbove G f e h_unbdd
    · exact linkOscillation_eq_zero_of_independent G f e (h_ind e he)
  have h_comp_zero : dobrushinObservableComparison G C f g = 0 := by
    unfold dobrushinObservableComparison
    refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun e' _ => ?_
    rw [h_osc_zero e, zero_mul, zero_mul]
  have h_le := h_unrestricted f g
  rw [h_comp_zero, mul_zero] at h_le
  exact h_cov_ne (abs_nonpos_iff.mp h_le)

/-- Joint measurability of `p : GroupGaugeConfig G L × G ↦ updateGroupGaugeLink L p.1 x μ p.2`. -/
theorem measurable_updateGroupGaugeLink_uncurry (G : Type*) [MeasurableSpace G] {L : ℕ}
    (x : Lattice4D L) (μ : Fin 4) :
    Measurable (fun p : GroupGaugeConfig G L × G => updateGroupGaugeLink L p.1 x μ p.2) := by
  refine measurable_pi_iff.mpr fun e => ?_
  by_cases he : e = ⟨x, μ⟩
  · subst he
    have h_eq : (fun p : GroupGaugeConfig G L × G => updateGroupGaugeLink L p.1 x μ p.2 ⟨x, μ⟩) =
        Prod.snd := by
      funext p
      exact (updateGroupGaugeLink_same_and_other L p.1 x μ p.2).1
    rw [h_eq]
    exact measurable_snd
  · have h_eq : (fun p : GroupGaugeConfig G L × G => updateGroupGaugeLink L p.1 x μ p.2 e) =
        fun p => p.1 e := by
      funext p
      exact (updateGroupGaugeLink_same_and_other L p.1 x μ p.2).2 e he
    rw [h_eq]
    exact (measurable_pi_apply e).comp measurable_fst

/-- Slice measurability `g ↦ updateGroupGaugeLink L V x μ g` for any fixed configuration `V`. -/
theorem measurable_updateGroupGaugeLink_right (G : Type*) [MeasurableSpace G] {L : ℕ}
    (V : GroupGaugeConfig G L) (x : Lattice4D L) (μ : Fin 4) :
    Measurable (fun g : G => updateGroupGaugeLink L V x μ g) :=
  (measurable_updateGroupGaugeLink_uncurry G x μ).comp (measurable_const.prodMk measurable_id)

/-- Updating link `e₀` to its existing value `V e₀` is the identity on `V`. -/
theorem updateGroupGaugeLink_self_eq {G : Type*} {L : ℕ}
    (V : GroupGaugeConfig G L) (e₀ : Link L) :
    updateGroupGaugeLink L V e₀.x e₀.μ (V e₀) = V := by
  funext e
  by_cases he : e = e₀
  · subst he
    exact (updateGroupGaugeLink_same_and_other L V e.x e.μ (V e)).1
  · exact (updateGroupGaugeLink_same_and_other L V e₀.x e₀.μ (V e₀)).2 e he

/-- Global measurability of `V ↦ groupSingleLinkPartition G L S_act V e₀` whenever `Measurable S_act`. -/
theorem measurable_groupSingleLinkPartition
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} (S_act : GroupGaugeConfig G L → ℝ) (e₀ : Link L)
    (hS_meas : Measurable S_act) :
    Measurable (fun V : GroupGaugeConfig G L => groupSingleLinkPartition G L S_act V e₀) := by
  have h_joint : Measurable (fun p : GroupGaugeConfig G L × G =>
      Real.exp (-S_act (updateGroupGaugeLink L p.1 e₀.x e₀.μ p.2))) :=
    Real.continuous_exp.measurable.comp
      ((hS_meas.comp (measurable_updateGroupGaugeLink_uncurry G e₀.x e₀.μ)).neg)
  exact (h_joint.stronglyMeasurable.integral_prod_right'
    (ν := (compactGroupHaarProbability G : Measure G))).measurable

/-- Global measurability of `singleLinkGibbsOperator G L S_act e₀ h` whenever `Measurable S_act`
and `Measurable h`. -/
theorem measurable_singleLinkGibbsOperator
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} (S_act : GroupGaugeConfig G L → ℝ) (e₀ : Link L)
    (h : GroupGaugeConfig G L → ℝ)
    (hS_meas : Measurable S_act) (hh_meas : Measurable h) :
    Measurable (singleLinkGibbsOperator G L S_act e₀ h) := by
  have h_num_joint : Measurable (fun p : GroupGaugeConfig G L × G =>
      Real.exp (-S_act (updateGroupGaugeLink L p.1 e₀.x e₀.μ p.2)) *
        h (updateGroupGaugeLink L p.1 e₀.x e₀.μ p.2)) :=
    (Real.continuous_exp.measurable.comp
      ((hS_meas.comp (measurable_updateGroupGaugeLink_uncurry G e₀.x e₀.μ)).neg)).mul
      (hh_meas.comp (measurable_updateGroupGaugeLink_uncurry G e₀.x e₀.μ))
  have h_num : Measurable (fun V : GroupGaugeConfig G L =>
      ∫ g : G, Real.exp (-S_act (updateGroupGaugeLink L V e₀.x e₀.μ g)) *
        h (updateGroupGaugeLink L V e₀.x e₀.μ g)
        ∂(compactGroupHaarProbability G : Measure G)) :=
    (h_num_joint.stronglyMeasurable.integral_prod_right'
      (ν := (compactGroupHaarProbability G : Measure G))).measurable
  exact h_num.div (measurable_groupSingleLinkPartition G S_act e₀ hS_meas)

/-- Uniform sup-norm preservation `|singleLinkGibbsOperator G L S_act e₀ h V| ≤ M` when `|h U| ≤ M`. -/
theorem abs_singleLinkGibbsOperator_le
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} (S_act : GroupGaugeConfig G L → ℝ) (e₀ : Link L)
    (h : GroupGaugeConfig G L → ℝ) {M : ℝ}
    (hS_meas : ∀ W : GroupGaugeConfig G L,
      Measurable (fun g : G => S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)))
    (hS_bdd : ∀ W : GroupGaugeConfig G L,
      ∃ B : ℝ, ∀ g : G, |S_act (updateGroupGaugeLink L W e₀.x e₀.μ g)| ≤ B)
    (hh_meas : ∀ W : GroupGaugeConfig G L,
      Measurable (fun g : G => h (updateGroupGaugeLink L W e₀.x e₀.μ g)))
    (hh_bdd : ∀ U : GroupGaugeConfig G L, |h U| ≤ M)
    (V : GroupGaugeConfig G L) :
    |singleLinkGibbsOperator G L S_act e₀ h V| ≤ M := by
  have h0 : groupSingleLinkCondExp G L S_act V e₀ (fun _ => 0) = 0 := by
    simp [groupSingleLinkCondExp]
  have h_sub := abs_groupSingleLinkCondExp_sub_le_of_abs_sub_le G S_act V e₀
    (fun g => h (updateGroupGaugeLink L V e₀.x e₀.μ g)) (fun _ => 0)
    (hS_meas V) (hS_bdd V) (hh_meas V) measurable_const
    ⟨M, fun g => hh_bdd _⟩ ⟨0, fun _ => by simp⟩
    (fun g => by simpa using hh_bdd (updateGroupGaugeLink L V e₀.x e₀.μ g))
  simpa [singleLinkGibbsOperator, h0] using h_sub

/-- Pointwise single-link conditional deviation bound: for every configuration `V` and link `e₀`,
`|h V - singleLinkGibbsOperator G L S_act e₀ h V| ≤ linkOscillation G L h e₀`. -/
theorem abs_sub_singleLinkGibbsOperator_le_linkOscillation
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} (S_act : GroupGaugeConfig G L → ℝ) (e₀ : Link L)
    (h : GroupGaugeConfig G L → ℝ) {M : ℝ} (V : GroupGaugeConfig G L)
    (hS_meas : Measurable (fun g : G => S_act (updateGroupGaugeLink L V e₀.x e₀.μ g)))
    (hS_bdd : ∃ B : ℝ, ∀ g : G, |S_act (updateGroupGaugeLink L V e₀.x e₀.μ g)| ≤ B)
    (hh_meas : Measurable (fun g : G => h (updateGroupGaugeLink L V e₀.x e₀.μ g)))
    (hh_bdd : ∀ U : GroupGaugeConfig G L, |h U| ≤ M) :
    |h V - singleLinkGibbsOperator G L S_act e₀ h V| ≤ linkOscillation G L h e₀ := by
  have h_const : groupSingleLinkCondExp G L S_act V e₀ (fun _ : G => h V) = h V := by
    simpa using groupSingleLinkCondExp_const_add_mul G S_act V e₀ (h V) 0 (fun _ : G => 0)
      hS_meas hS_bdd measurable_const ⟨0, fun _ => by simp⟩
  have h_sub := abs_groupSingleLinkCondExp_sub_le_of_abs_sub_le G S_act V e₀
    (fun _ : G => h V) (fun g : G => h (updateGroupGaugeLink L V e₀.x e₀.μ g))
    hS_meas hS_bdd measurable_const hh_meas
    ⟨M, fun _ => hh_bdd V⟩ ⟨M, fun g => hh_bdd _⟩
    fun g => by
      have h_self : h V = h (updateGroupGaugeLink L V e₀.x e₀.μ (V e₀)) := by
        rw [updateGroupGaugeLink_self_eq V e₀]
      rw [h_self]
      exact abs_sub_updateGroupGaugeLink_le_linkOscillation G h e₀ hh_bdd V (V e₀) g
  simpa [singleLinkGibbsOperator, h_const] using h_sub

/-- Patch configuration agreeing with `U` on `s : Finset (Link L)` and with `U₀` outside `s`. -/
def patchGroupGaugeConfig {G : Type*} {L : ℕ}
    (s : Finset (Link L)) (U U₀ : GroupGaugeConfig G L) : GroupGaugeConfig G L :=
  fun e => if e ∈ s then U e else U₀ e

theorem patchGroupGaugeConfig_empty {G : Type*} {L : ℕ}
    (U U₀ : GroupGaugeConfig G L) :
    patchGroupGaugeConfig ∅ U U₀ = U₀ := by
  funext e
  simp [patchGroupGaugeConfig]

theorem patchGroupGaugeConfig_univ {G : Type*} {L : ℕ} [NeZero L]
    (U U₀ : GroupGaugeConfig G L) :
    patchGroupGaugeConfig Finset.univ U U₀ = U := by
  funext e
  simp [patchGroupGaugeConfig]

theorem patchGroupGaugeConfig_insert {G : Type*} {L : ℕ}
    (e : Link L) (s : Finset (Link L)) (U U₀ : GroupGaugeConfig G L) :
    patchGroupGaugeConfig (insert e s) U U₀ =
      updateGroupGaugeLink L (patchGroupGaugeConfig s U U₀) e.x e.μ (U e) := by
  funext e'
  unfold patchGroupGaugeConfig updateGroupGaugeLink Function.update
  by_cases h_eq : e' = e
  · subst h_eq
    simp
  · simp [h_eq]

theorem patchGroupGaugeConfig_not_mem_eq_update {G : Type*} {L : ℕ}
    {e : Link L} {s : Finset (Link L)} (he : e ∉ s) (U U₀ : GroupGaugeConfig G L) :
    patchGroupGaugeConfig s U U₀ =
      updateGroupGaugeLink L (patchGroupGaugeConfig s U U₀) e.x e.μ (U₀ e) := by
  funext e'
  unfold patchGroupGaugeConfig updateGroupGaugeLink Function.update
  by_cases h_eq : e' = e
  · subst h_eq
    simp [he]
  · simp [h_eq]

theorem abs_sub_patchGroupGaugeConfig_le_sum_linkOscillation (G : Type*) {L : ℕ}
    (h : GroupGaugeConfig G L → ℝ) {M : ℝ}
    (hh_bdd : ∀ V : GroupGaugeConfig G L, |h V| ≤ M)
    (U U₀ : GroupGaugeConfig G L) (s : Finset (Link L)) :
    |h (patchGroupGaugeConfig s U U₀) - h U₀| ≤
      ∑ e ∈ s, linkOscillation G L h e := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [patchGroupGaugeConfig_empty]
  | @insert e s he ih =>
      rw [Finset.sum_insert he]
      have h_step :
          |h (patchGroupGaugeConfig (insert e s) U U₀) - h (patchGroupGaugeConfig s U U₀)| ≤
            linkOscillation G L h e := by
        rw [patchGroupGaugeConfig_insert e s U U₀]
        conv_lhs =>
          arg 1
          arg 2
          rw [patchGroupGaugeConfig_not_mem_eq_update he U U₀]
        exact abs_sub_updateGroupGaugeLink_le_linkOscillation G h e hh_bdd
          (patchGroupGaugeConfig s U U₀) (U e) (U₀ e)
      calc
        |h (patchGroupGaugeConfig (insert e s) U U₀) - h U₀|
          = |(h (patchGroupGaugeConfig (insert e s) U U₀) - h (patchGroupGaugeConfig s U U₀)) +
              (h (patchGroupGaugeConfig s U U₀) - h U₀)| := by ring_nf
        _ ≤ |h (patchGroupGaugeConfig (insert e s) U U₀) - h (patchGroupGaugeConfig s U U₀)| +
              |h (patchGroupGaugeConfig s U U₀) - h U₀| := abs_add_le _ _
        _ ≤ linkOscillation G L h e + ∑ e' ∈ s, linkOscillation G L h e' :=
            add_le_add h_step ih

/-- Finite-volume link-by-link telescoping oscillation bound: for any bounded observable
`h : GroupGaugeConfig G L → ℝ` and any two configurations `U, U₀`,
`|h U - h U₀| ≤ ∑ e : Link L, linkOscillation G L h e`. -/
theorem abs_sub_le_sum_linkOscillation (G : Type*) {L : ℕ} [NeZero L]
    (h : GroupGaugeConfig G L → ℝ) {M : ℝ}
    (hh_bdd : ∀ V : GroupGaugeConfig G L, |h V| ≤ M)
    (U U₀ : GroupGaugeConfig G L) :
    |h U - h U₀| ≤ ∑ e : Link L, linkOscillation G L h e := by
  simpa [patchGroupGaugeConfig_univ] using
    abs_sub_patchGroupGaugeConfig_le_sum_linkOscillation G h hh_bdd U U₀ Finset.univ

lemma link_univ_nonempty {L : ℕ} [NeZero L] : (Finset.univ : Finset (Link L)).Nonempty :=
  ⟨⟨fun _ => 0, 0⟩, Finset.mem_univ _⟩

/-- Greedy link choice selecting a link `e₀ : Link L` with maximal single-link oscillation
`linkOscillation G L h e₀` over the finite torus `Link L`. -/
noncomputable def greedyOscillationLink (G : Type*) (L : ℕ) [NeZero L]
    (h : GroupGaugeConfig G L → ℝ) : Link L :=
  Classical.choose
    (Finset.exists_max_image (Finset.univ : Finset (Link L))
      (fun e => linkOscillation G L h e) link_univ_nonempty)

theorem le_linkOscillation_greedyOscillationLink (G : Type*) {L : ℕ} [NeZero L]
    (h : GroupGaugeConfig G L → ℝ) (e : Link L) :
    linkOscillation G L h e ≤ linkOscillation G L h (greedyOscillationLink G L h) :=
  (Classical.choose_spec
    (Finset.exists_max_image (Finset.univ : Finset (Link L))
      (fun e' => linkOscillation G L h e') link_univ_nonempty)).2 e (Finset.mem_univ e)

theorem sum_linkOscillation_le_card_mul_greedyOscillationLink (G : Type*) {L : ℕ} [NeZero L]
    (h : GroupGaugeConfig G L → ℝ) :
    (∑ e : Link L, linkOscillation G L h e) ≤
      (Fintype.card (Link L) : ℝ) * linkOscillation G L h (greedyOscillationLink G L h) := by
  calc
    (∑ e : Link L, linkOscillation G L h e)
      ≤ ∑ _e : Link L, linkOscillation G L h (greedyOscillationLink G L h) :=
        Finset.sum_le_sum fun e _ => le_linkOscillation_greedyOscillationLink G h e
    _ = (Fintype.card (Link L) : ℝ) * linkOscillation G L h (greedyOscillationLink G L h) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Greedy single-link Gibbs sweep chain `F_{K + 1} = Π_{e_K} F_K` choosing at each step `K` the
link `e_K = greedyOscillationLink G L F_K` with maximal single-link oscillation. -/
noncomputable def greedySingleLinkGibbsChain (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] (S_act : GroupGaugeConfig G L → ℝ)
    (f : GroupGaugeConfig G L → ℝ) : ℕ → GroupGaugeConfig G L → ℝ
  | 0 => f
  | K + 1 =>
      let F_K := greedySingleLinkGibbsChain G L S_act f K
      singleLinkGibbsOperator G L S_act (greedyOscillationLink G L F_K) F_K

/-- Link sequence `e_K = greedyOscillationLink G L (greedySingleLinkGibbsChain G L S_act f K)`. -/
noncomputable def greedySingleLinkGibbsLinkSeq (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] (S_act : GroupGaugeConfig G L → ℝ)
    (f : GroupGaugeConfig G L → ℝ) (K : ℕ) : Link L :=
  greedyOscillationLink G L (greedySingleLinkGibbsChain G L S_act f K)

theorem measurable_greedySingleLinkGibbsChain
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ)
    (f : GroupGaugeConfig G L → ℝ)
    (hS_meas : Measurable S_act) (hf_meas : Measurable f) :
    ∀ K : ℕ, Measurable (greedySingleLinkGibbsChain G L S_act f K)
  | 0 => hf_meas
  | K + 1 =>
      measurable_singleLinkGibbsOperator G S_act _ _ hS_meas
        (measurable_greedySingleLinkGibbsChain G S_act f hS_meas hf_meas K)

theorem abs_greedySingleLinkGibbsChain_le
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ)
    (f : GroupGaugeConfig G L → ℝ) {B M : ℝ}
    (hS_meas : Measurable S_act) (hS_bdd : ∀ V : GroupGaugeConfig G L, |S_act V| ≤ B)
    (hf_meas : Measurable f) (hf_bdd : ∀ V : GroupGaugeConfig G L, |f V| ≤ M) :
    ∀ (K : ℕ) (V : GroupGaugeConfig G L),
      |greedySingleLinkGibbsChain G L S_act f K V| ≤ M
  | 0, V => hf_bdd V
  | K + 1, V => by
      have hFK_meas := measurable_greedySingleLinkGibbsChain G S_act f hS_meas hf_meas K
      exact abs_singleLinkGibbsOperator_le G S_act _ _
        (fun W => hS_meas.comp (measurable_updateGroupGaugeLink_right G W _ _))
        (fun W => ⟨B, fun g => hS_bdd _⟩)
        (fun W => hFK_meas.comp (measurable_updateGroupGaugeLink_right G W _ _))
        (abs_greedySingleLinkGibbsChain_le G S_act f hS_meas hS_bdd hf_meas hf_bdd K) V

/-- Geometric contraction of total link oscillation along the greedy single-link Gibbs sweep chain:
$$\sum_{e : \mathrm{Link}\ L} \delta_e(F_K) \le \left(1 - \frac{1 - q}{|\mathrm{Link}\ L|}\right)^K \sum_{e : \mathrm{Link}\ L} \delta_e(f).$$ -/
theorem sum_linkOscillation_greedySingleLinkGibbsChain_le_pow
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ)
    {q B M : ℝ} (hq : 0 ≤ q) (hq_lt : q < 1)
    (h_row : ∀ e : Link L, (∑ e' : Link L, dobrushinSupMatrix G L S_act e e') ≤ q)
    (f : GroupGaugeConfig G L → ℝ)
    (hS_meas : Measurable S_act) (hS_bdd : ∀ V : GroupGaugeConfig G L, |S_act V| ≤ B)
    (hf_meas : Measurable f) (hf_bdd : ∀ V : GroupGaugeConfig G L, |f V| ≤ M) :
    ∀ K : ℕ,
      (∑ e : Link L, linkOscillation G L (greedySingleLinkGibbsChain G L S_act f K) e) ≤
        (1 - (1 - q) / (Fintype.card (Link L) : ℝ)) ^ K *
          (∑ e : Link L, linkOscillation G L f e)
  | 0 => by simp [greedySingleLinkGibbsChain]
  | K + 1 => by
      let F_K := greedySingleLinkGibbsChain G L S_act f K
      let e_K := greedyOscillationLink G L F_K
      have hFK_meas := measurable_greedySingleLinkGibbsChain G S_act f hS_meas hf_meas K
      have hFK_bdd := abs_greedySingleLinkGibbsChain_le G S_act f hS_meas hS_bdd hf_meas hf_bdd K
      have h_step := sum_linkOscillation_singleLinkGibbsOperator_le G S_act h_row e_K F_K
        (fun W => hS_meas.comp (measurable_updateGroupGaugeLink_right G W _ _))
        (fun W => ⟨B, fun g => hS_bdd _⟩)
        (fun W => hFK_meas.comp (measurable_updateGroupGaugeLink_right G W _ _))
        ⟨M, hFK_bdd⟩
      have hN_pos_nat : 0 < Fintype.card (Link L) := Fintype.card_pos_iff.mpr ⟨⟨fun _ => 0, 0⟩⟩
      have hN_ge_one : (1 : ℝ) ≤ (Fintype.card (Link L) : ℝ) := by exact_mod_cast hN_pos_nat
      have hN_pos : (0 : ℝ) < (Fintype.card (Link L) : ℝ) := by linarith
      have h_max := sum_linkOscillation_le_card_mul_greedyOscillationLink G F_K
      have h_div :
          ((1 - q) / (Fintype.card (Link L) : ℝ)) * (∑ e : Link L, linkOscillation G L F_K e) ≤
            (1 - q) * linkOscillation G L F_K e_K := by
        have h1q : 0 ≤ (1 - q) / (Fintype.card (Link L) : ℝ) :=
          div_nonneg (sub_nonneg.mpr hq_lt.le) hN_pos.le
        calc
          ((1 - q) / (Fintype.card (Link L) : ℝ)) * (∑ e : Link L, linkOscillation G L F_K e)
            ≤ ((1 - q) / (Fintype.card (Link L) : ℝ)) *
                ((Fintype.card (Link L) : ℝ) * linkOscillation G L F_K e_K) :=
              mul_le_mul_of_nonneg_left h_max h1q
          _ = (1 - q) * linkOscillation G L F_K e_K := by
              rw [← mul_assoc, div_mul_cancel₀ _ hN_pos.ne']
      have h_contract :
          (∑ e : Link L, linkOscillation G L (greedySingleLinkGibbsChain G L S_act f (K + 1)) e) ≤
            (1 - (1 - q) / (Fintype.card (Link L) : ℝ)) *
              (∑ e : Link L, linkOscillation G L F_K e) := by
        change (∑ e : Link L, linkOscillation G L (singleLinkGibbsOperator G L S_act e_K F_K) e) ≤ _
        linarith
      have h_rate_nonneg : 0 ≤ 1 - (1 - q) / (Fintype.card (Link L) : ℝ) := by
        have h_le1 : (1 - q) / (Fintype.card (Link L) : ℝ) ≤ 1 := by
          rw [div_le_iff₀ hN_pos]
          linarith
        linarith
      have ih := sum_linkOscillation_greedySingleLinkGibbsChain_le_pow
        G S_act hq hq_lt h_row f hS_meas hS_bdd hf_meas hf_bdd K
      calc
        (∑ e : Link L, linkOscillation G L (greedySingleLinkGibbsChain G L S_act f (K + 1)) e)
          ≤ (1 - (1 - q) / (Fintype.card (Link L) : ℝ)) *
              ((1 - (1 - q) / (Fintype.card (Link L) : ℝ)) ^ K *
                (∑ e : Link L, linkOscillation G L f e)) :=
            le_trans h_contract (mul_le_mul_of_nonneg_left ih h_rate_nonneg)
        _ = (1 - (1 - q) / (Fintype.card (Link L) : ℝ)) ^ (K + 1) *
              (∑ e : Link L, linkOscillation G L f e) := by
            rw [pow_succ']
            ring

/-- Total link oscillation of `greedySingleLinkGibbsChain G L S_act f K` converges to `0` as `K → ∞`
whenever `0 ≤ q < 1`. -/
theorem tendsto_sum_linkOscillation_greedySingleLinkGibbsChain_zero
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ)
    {q B M : ℝ} (hq : 0 ≤ q) (hq_lt : q < 1)
    (h_row : ∀ e : Link L, (∑ e' : Link L, dobrushinSupMatrix G L S_act e e') ≤ q)
    (f : GroupGaugeConfig G L → ℝ)
    (hS_meas : Measurable S_act) (hS_bdd : ∀ V : GroupGaugeConfig G L, |S_act V| ≤ B)
    (hf_meas : Measurable f) (hf_bdd : ∀ V : GroupGaugeConfig G L, |f V| ≤ M) :
    Filter.Tendsto
      (fun K : ℕ => ∑ e : Link L, linkOscillation G L (greedySingleLinkGibbsChain G L S_act f K) e)
      Filter.atTop (nhds 0) := by
  have hN_pos_nat : 0 < Fintype.card (Link L) := Fintype.card_pos_iff.mpr ⟨⟨fun _ => 0, 0⟩⟩
  have hN_ge_one : (1 : ℝ) ≤ (Fintype.card (Link L) : ℝ) := by exact_mod_cast hN_pos_nat
  have hN_pos : (0 : ℝ) < (Fintype.card (Link L) : ℝ) := by linarith
  set r : ℝ := 1 - (1 - q) / (Fintype.card (Link L) : ℝ)
  have hr_nonneg : 0 ≤ r := by
    have h_le1 : (1 - q) / (Fintype.card (Link L) : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hN_pos]
      linarith
    dsimp [r]
    linarith
  have hr_lt_one : r < 1 := by
    have h_pos : 0 < (1 - q) / (Fintype.card (Link L) : ℝ) :=
      div_pos (sub_pos.mpr hq_lt) hN_pos
    dsimp [r]
    linarith
  have h_tendsto_rhs :
      Filter.Tendsto (fun K : ℕ => r ^ K * (∑ e : Link L, linkOscillation G L f e))
        Filter.atTop (nhds 0) := by
    simpa [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg hr_lt_one).mul_const
        (∑ e : Link L, linkOscillation G L f e)
  exact squeeze_zero
    (fun K => Finset.sum_nonneg fun e _ => linkOscillation_nonneg G L _ e)
    (sum_linkOscillation_greedySingleLinkGibbsChain_le_pow
      G S_act hq hq_lt h_row f hS_meas hS_bdd hf_meas hf_bdd)
    h_tendsto_rhs

/-- Left-multiplication at a single link `e₀ : Link L` by `g : G`. -/
def mulGroupGaugeLinkLeft {G : Type*} [Group G] {L : ℕ}
    (e₀ : Link L) (g : G) (V : GroupGaugeConfig G L) : GroupGaugeConfig G L :=
  fun e => (if e = e₀ then g else 1) * V e

theorem mulGroupGaugeLinkLeft_eq_updateGroupGaugeLink {G : Type*} [Group G] {L : ℕ}
    (e₀ : Link L) (g : G) (V : GroupGaugeConfig G L) :
    mulGroupGaugeLinkLeft e₀ g V = updateGroupGaugeLink L V e₀.x e₀.μ (g * V e₀) := by
  funext e
  unfold mulGroupGaugeLinkLeft updateGroupGaugeLink Function.update
  by_cases he : e = e₀
  · subst he
    simp
  · simp [he]

theorem measurePreserving_mulGroupGaugeLinkLeft
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (e₀ : Link L) (g : G) :
    MeasurePreserving (mulGroupGaugeLinkLeft e₀ g)
      (groupGaugeHaarMeasure G L) (groupGaugeHaarMeasure G L) := by
  change MeasurePreserving
    (fun (V : Link L → G) (e : Link L) => (if e = e₀ then g else 1) * V e)
    (Measure.pi (fun _ : Link L => compactGroupHaarProbability G))
    (Measure.pi (fun _ : Link L => compactGroupHaarProbability G))
  refine measurePreserving_pi (fun _ : Link L => compactGroupHaarProbability G)
    (fun _ : Link L => compactGroupHaarProbability G)
    (f := fun e x => (if e = e₀ then g else 1) * x) ?_
  intro e
  exact measurePreserving_mul_left (compactGroupHaarProbability G) (if e = e₀ then g else 1)

/-- Single-link Haar conditioning identity on `groupGaugeHaarMeasure G L`: for any measurable bounded
observable `H : GroupGaugeConfig G L → ℝ` and any link `e₀ : Link L`,
$$\int H(V) \, d\mu_{\mathrm{Haar}}(V) = \int \left(\int_G H(V_{e_0 \leftarrow g}) \, d\mu_G(g)\right) d\mu_{\mathrm{Haar}}(V).$$ -/
theorem integral_groupGaugeHaarMeasure_eq_integral_updateGroupGaugeLink
    (G : Type*) [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (e₀ : Link L) (H : GroupGaugeConfig G L → ℝ) {M : ℝ}
    (hH_meas : Measurable H) (hH_bdd : ∀ V : GroupGaugeConfig G L, |H V| ≤ M) :
    (∫ V : GroupGaugeConfig G L, H V ∂(groupGaugeHaarMeasure G L)) =
      ∫ V : GroupGaugeConfig G L,
        (∫ g : G, H (updateGroupGaugeLink L V e₀.x e₀.μ g)
          ∂(compactGroupHaarProbability G : Measure G))
        ∂(groupGaugeHaarMeasure G L) := by
  have h_shift (g : G) :
      (∫ V : GroupGaugeConfig G L, H V ∂(groupGaugeHaarMeasure G L)) =
        ∫ V : GroupGaugeConfig G L,
          H (updateGroupGaugeLink L V e₀.x e₀.μ (g * V e₀)) ∂(groupGaugeHaarMeasure G L) := by
    have hmp := measurePreserving_mulGroupGaugeLinkLeft G e₀ g
    calc
      (∫ V : GroupGaugeConfig G L, H V ∂(groupGaugeHaarMeasure G L))
        = ∫ V : GroupGaugeConfig G L, H (mulGroupGaugeLinkLeft e₀ g V)
            ∂(groupGaugeHaarMeasure G L) := by
            conv_lhs => rw [← hmp.map_eq]
            exact integral_map hmp.measurable.aemeasurable hH_meas.aestronglyMeasurable
      _ = ∫ V : GroupGaugeConfig G L,
            H (updateGroupGaugeLink L V e₀.x e₀.μ (g * V e₀))
            ∂(groupGaugeHaarMeasure G L) := by
            simp_rw [mulGroupGaugeLinkLeft_eq_updateGroupGaugeLink]
  have h_uncurry_meas :
      Measurable (Function.uncurry fun (g : G) (V : GroupGaugeConfig G L) =>
        H (updateGroupGaugeLink L V e₀.x e₀.μ (g * V e₀))) := by
    have h_pair :
        Measurable (fun p : G × GroupGaugeConfig G L => (p.2, p.1 * p.2 e₀)) :=
      measurable_snd.prodMk
        (measurable_fst.mul ((measurable_pi_apply e₀).comp measurable_snd))
    exact hH_meas.comp ((measurable_updateGroupGaugeLink_uncurry G e₀.x e₀.μ).comp h_pair)
  have h_uncurry_int :
      Integrable (Function.uncurry fun (g : G) (V : GroupGaugeConfig G L) =>
        H (updateGroupGaugeLink L V e₀.x e₀.μ (g * V e₀)))
        ((compactGroupHaarProbability G : Measure G).prod (groupGaugeHaarMeasure G L)) := by
    refine (integrable_const M).mono' h_uncurry_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact hH_bdd _
  calc
    (∫ V : GroupGaugeConfig G L, H V ∂(groupGaugeHaarMeasure G L))
      = ∫ g : G, (∫ V : GroupGaugeConfig G L, H V ∂(groupGaugeHaarMeasure G L))
          ∂(compactGroupHaarProbability G : Measure G) := by
          rw [integral_const, probReal_univ, one_smul]
    _ = ∫ g : G,
          (∫ V : GroupGaugeConfig G L,
            H (updateGroupGaugeLink L V e₀.x e₀.μ (g * V e₀))
            ∂(groupGaugeHaarMeasure G L))
          ∂(compactGroupHaarProbability G : Measure G) := by
          simp_rw [← h_shift]
    _ = ∫ V : GroupGaugeConfig G L,
          (∫ g : G, H (updateGroupGaugeLink L V e₀.x e₀.μ (g * V e₀))
            ∂(compactGroupHaarProbability G : Measure G))
          ∂(groupGaugeHaarMeasure G L) :=
          integral_integral_swap h_uncurry_int
    _ = ∫ V : GroupGaugeConfig G L,
          (∫ g : G, H (updateGroupGaugeLink L V e₀.x e₀.μ g)
            ∂(compactGroupHaarProbability G : Measure G))
          ∂(groupGaugeHaarMeasure G L) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
          exact integral_mul_right_eq_self
            (μ := (compactGroupHaarProbability G : Measure G))
            (fun g : G => H (updateGroupGaugeLink L V e₀.x e₀.μ g)) (V e₀)

/-- Partition function $\int \exp(-S_{\mathrm{act}}(V)) \, d\mu_{\mathrm{Haar}}(V)$ on `GroupGaugeConfig G L`. -/
noncomputable def groupGibbsPartition
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] (S_act : GroupGaugeConfig G L → ℝ) : ℝ :=
  ∫ V : GroupGaugeConfig G L, Real.exp (-S_act V) ∂(groupGaugeHaarMeasure G L)

/-- Normalized Gibbs measure on `GroupGaugeConfig G L` with action `S_act` relative to
`groupGaugeHaarMeasure G L`. -/
noncomputable def groupGibbsMeasure
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] (S_act : GroupGaugeConfig G L → ℝ) :
    Measure (GroupGaugeConfig G L) :=
  (groupGaugeHaarMeasure G L).withDensity fun V =>
    ENNReal.ofReal (Real.exp (-S_act V) / groupGibbsPartition G L S_act)

/-- Connected two-point covariance $\int f g \, d\mu - (\int f \, d\mu)(\int g \, d\mu)$ on
`GroupGaugeConfig G L`. -/
noncomputable def groupGibbsCov {G : Type*} [MeasurableSpace G] {L : ℕ}
    (μ : Measure (GroupGaugeConfig G L)) (f g : GroupGaugeConfig G L → ℝ) : ℝ :=
  (∫ V, f V * g V ∂μ) - (∫ V, f V ∂μ) * (∫ V, g V ∂μ)

theorem groupGibbsPartition_pos
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ) {B : ℝ}
    (hS_meas : Measurable S_act) (hS_bdd : ∀ V : GroupGaugeConfig G L, |S_act V| ≤ B) :
    0 < groupGibbsPartition G L S_act := by
  have h_w_le (V : GroupGaugeConfig G L) : Real.exp (-S_act V) ≤ Real.exp B :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hS_bdd V)).1])
  have h_w_ge (V : GroupGaugeConfig G L) : Real.exp (-B) ≤ Real.exp (-S_act V) :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hS_bdd V)).2])
  have h_int_w : Integrable (fun V => Real.exp (-S_act V)) (groupGaugeHaarMeasure G L) := by
    refine (integrable_const (Real.exp B)).mono'
      (Real.continuous_exp.measurable.comp hS_meas.neg).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun V => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact h_w_le V
  have h_lo :
      (∫ _ : GroupGaugeConfig G L, Real.exp (-B) ∂(groupGaugeHaarMeasure G L)) ≤
        groupGibbsPartition G L S_act :=
    integral_mono (integrable_const _) h_int_w h_w_ge
  rw [integral_const, probReal_univ, one_smul] at h_lo
  exact lt_of_lt_of_le (Real.exp_pos (-B)) h_lo

theorem groupGibbsMeasure_isProbabilityMeasure
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ) {B : ℝ}
    (hS_meas : Measurable S_act) (hS_bdd : ∀ V : GroupGaugeConfig G L, |S_act V| ≤ B) :
    IsProbabilityMeasure (groupGibbsMeasure G L S_act) := by
  have hZ := groupGibbsPartition_pos G S_act hS_meas hS_bdd
  have h_w_le (V : GroupGaugeConfig G L) : Real.exp (-S_act V) ≤ Real.exp B :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hS_bdd V)).1])
  have h_int_w : Integrable (fun V => Real.exp (-S_act V)) (groupGaugeHaarMeasure G L) := by
    refine (integrable_const (Real.exp B)).mono'
      (Real.continuous_exp.measurable.comp hS_meas.neg).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun V => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact h_w_le V
  have hi := h_int_w.div_const (groupGibbsPartition G L S_act)
  have hp : ∀ᵐ V ∂(groupGaugeHaarMeasure G L),
      0 ≤ Real.exp (-S_act V) / groupGibbsPartition G L S_act :=
    Filter.Eventually.of_forall fun V => div_nonneg (Real.exp_pos _).le hZ.le
  constructor
  rw [groupGibbsMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hp, integral_div]
  change ENNReal.ofReal (groupGibbsPartition G L S_act / groupGibbsPartition G L S_act) = 1
  simp [ne_of_gt hZ]

theorem integral_groupGibbsMeasure
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ) {B : ℝ}
    (hS_meas : Measurable S_act) (hS_bdd : ∀ V : GroupGaugeConfig G L, |S_act V| ≤ B)
    (F : GroupGaugeConfig G L → ℝ) :
    (∫ V, F V ∂(groupGibbsMeasure G L S_act)) =
      (∫ V, Real.exp (-S_act V) * F V ∂(groupGaugeHaarMeasure G L)) /
        groupGibbsPartition G L S_act := by
  have hZ := groupGibbsPartition_pos G S_act hS_meas hS_bdd
  have hw_meas : Measurable (fun V : GroupGaugeConfig G L => Real.exp (-S_act V)) :=
    Real.continuous_exp.measurable.comp hS_meas.neg
  have hm :
      Measurable (fun V : GroupGaugeConfig G L =>
        ENNReal.ofReal (Real.exp (-S_act V) / groupGibbsPartition G L S_act)) :=
    (hw_meas.div_const (groupGibbsPartition G L S_act)).ennreal_ofReal
  have hp (V : GroupGaugeConfig G L) :
      0 ≤ Real.exp (-S_act V) / groupGibbsPartition G L S_act :=
    div_nonneg (Real.exp_pos _).le hZ.le
  rw [groupGibbsMeasure, integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) F]
  simp only [ENNReal.toReal_ofReal (hp _), smul_eq_mul, div_mul_eq_mul_div, integral_div]

/-- General finite-volume covariance bound by total single-link oscillation under any probability
measure `μ` on `GroupGaugeConfig G L`:
`|\mathrm{groupGibbsCov}\ \mu\ h\ g| \le 2 \, M_g \sum_{e : \mathrm{Link}\ L} \delta_e(h)`. -/
theorem abs_groupGibbsCov_le_two_mul_sum_linkOscillation
    (G : Type*) [One G] [MeasurableSpace G] {L : ℕ} [NeZero L]
    (μ : Measure (GroupGaugeConfig G L)) [IsProbabilityMeasure μ]
    (h g : GroupGaugeConfig G L → ℝ) {M_h M_g : ℝ}
    (hh_meas : Measurable h) (hh_bdd : ∀ V : GroupGaugeConfig G L, |h V| ≤ M_h)
    (hg_meas : Measurable g) (hg_bdd : ∀ V : GroupGaugeConfig G L, |g V| ≤ M_g) :
    |groupGibbsCov μ h g| ≤
      2 * M_g * (∑ e : Link L, linkOscillation G L h e) := by
  have hMg_nonneg : 0 ≤ M_g := le_trans (abs_nonneg _) (hg_bdd (fun _ => 1))
  let U₀ : GroupGaugeConfig G L := fun _ => 1
  let c : ℝ := h U₀
  let D : ℝ := ∑ e : Link L, linkOscillation G L h e
  have hD_nonneg : 0 ≤ D := Finset.sum_nonneg fun e _ => linkOscillation_nonneg G L h e
  let h₀ : GroupGaugeConfig G L → ℝ := fun V => h V - c
  have hh₀_meas : Measurable h₀ := hh_meas.sub measurable_const
  have hh₀_bdd (V : GroupGaugeConfig G L) : |h₀ V| ≤ D :=
    abs_sub_le_sum_linkOscillation G h hh_bdd V U₀
  have h_int_h₀ : Integrable h₀ μ := by
    refine (integrable_const D).mono' hh₀_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun V => by
      rw [Real.norm_eq_abs]
      exact hh₀_bdd V
  have h_int_g : Integrable g μ := by
    refine (integrable_const M_g).mono' hg_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun V => by
      rw [Real.norm_eq_abs]
      exact hg_bdd V
  have h_int_h₀g : Integrable (fun V => h₀ V * g V) μ := by
    refine (integrable_const (D * M_g)).mono' (hh₀_meas.mul hg_meas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun V => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hh₀_bdd V) (hg_bdd V) (abs_nonneg _) hD_nonneg
  have h_cov_eq : groupGibbsCov μ h g = groupGibbsCov μ h₀ g := by
    have h_eq1 : (fun V => h V) = fun V => h₀ V + c := by
      funext V
      dsimp [h₀]
      ring
    have h_eq2 : (fun V => h V * g V) = fun V => h₀ V * g V + c * g V := by
      funext V
      dsimp [h₀]
      ring
    unfold groupGibbsCov
    rw [h_eq1, h_eq2, integral_add h_int_h₀ (integrable_const c),
      integral_add h_int_h₀g (h_int_g.const_mul c), integral_const_mul,
      integral_const, probReal_univ, one_smul]
    ring
  have h_term1 : |∫ V, h₀ V * g V ∂μ| ≤ D * M_g := by
    calc
      |∫ V, h₀ V * g V ∂μ| ≤ ∫ V, |h₀ V * g V| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ : GroupGaugeConfig G L, D * M_g ∂μ := by
          refine integral_mono h_int_h₀g.abs (integrable_const _) fun V => ?_
          dsimp only
          rw [abs_mul]
          exact mul_le_mul (hh₀_bdd V) (hg_bdd V) (abs_nonneg _) hD_nonneg
      _ = D * M_g := by rw [integral_const, probReal_univ, one_smul]
  have h_int_h₀_le : |∫ V, h₀ V ∂μ| ≤ D := by
    calc
      |∫ V, h₀ V ∂μ| ≤ ∫ V, |h₀ V| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ : GroupGaugeConfig G L, D ∂μ :=
          integral_mono h_int_h₀.abs (integrable_const _) hh₀_bdd
      _ = D := by rw [integral_const, probReal_univ, one_smul]
  have h_int_g_le : |∫ V, g V ∂μ| ≤ M_g := by
    calc
      |∫ V, g V ∂μ| ≤ ∫ V, |g V| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ : GroupGaugeConfig G L, M_g ∂μ :=
          integral_mono h_int_g.abs (integrable_const _) hg_bdd
      _ = M_g := by rw [integral_const, probReal_univ, one_smul]
  have h_term2 : |(∫ V, h₀ V ∂μ) * (∫ V, g V ∂μ)| ≤ D * M_g := by
    rw [abs_mul]
    exact mul_le_mul h_int_h₀_le h_int_g_le (abs_nonneg _) hD_nonneg
  rw [h_cov_eq]
  unfold groupGibbsCov
  calc
    |(∫ V, h₀ V * g V ∂μ) - (∫ V, h₀ V ∂μ) * (∫ V, g V ∂μ)|
      ≤ |∫ V, h₀ V * g V ∂μ| + |(∫ V, h₀ V ∂μ) * (∫ V, g V ∂μ)| := abs_sub _ _
    _ ≤ D * M_g + D * M_g := add_le_add h_term1 h_term2
    _ = 2 * M_g * D := by ring

/-- Conditional Gibbs orthogonality identity on `groupGibbsMeasure G L S_act`: for any measurable
bounded `h, ψ : GroupGaugeConfig G L → ℝ` such that `ψ` is invariant under updating link `e₀`,
$$\int h(V)\,\psi(V) \, d\mu_{\mathrm{Gibbs}}(V) = \int (\Pi_{e_0} h)(V)\,\psi(V) \, d\mu_{\mathrm{Gibbs}}(V).$$ -/
theorem integral_groupGibbsMeasure_mul_invariant_eq_singleLinkGibbsOperator
    (G : Type*) [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ) {B : ℝ}
    (hS_meas : Measurable S_act) (hS_bdd : ∀ V : GroupGaugeConfig G L, |S_act V| ≤ B)
    (e₀ : Link L)
    (h ψ : GroupGaugeConfig G L → ℝ) {M_h M_ψ : ℝ}
    (hh_meas : Measurable h) (hh_bdd : ∀ V : GroupGaugeConfig G L, |h V| ≤ M_h)
    (hψ_meas : Measurable ψ) (hψ_bdd : ∀ V : GroupGaugeConfig G L, |ψ V| ≤ M_ψ)
    (hψ_inv : ∀ (V : GroupGaugeConfig G L) (g : G),
      ψ (updateGroupGaugeLink L V e₀.x e₀.μ g) = ψ V) :
    (∫ V, h V * ψ V ∂(groupGibbsMeasure G L S_act)) =
      ∫ V, singleLinkGibbsOperator G L S_act e₀ h V * ψ V ∂(groupGibbsMeasure G L S_act) := by
  have hMh_nonneg : 0 ≤ M_h := le_trans (abs_nonneg _) (hh_bdd (fun _ => 1))
  have hMψ_nonneg : 0 ≤ M_ψ := le_trans (abs_nonneg _) (hψ_bdd (fun _ => 1))
  have hPh_meas : Measurable (singleLinkGibbsOperator G L S_act e₀ h) :=
    measurable_singleLinkGibbsOperator G S_act e₀ h hS_meas hh_meas
  have hPh_bdd (V : GroupGaugeConfig G L) :
      |singleLinkGibbsOperator G L S_act e₀ h V| ≤ M_h :=
    abs_singleLinkGibbsOperator_le G S_act e₀ h
      (fun W => hS_meas.comp (measurable_updateGroupGaugeLink_right G W _ _))
      (fun W => ⟨B, fun g => hS_bdd _⟩)
      (fun W => hh_meas.comp (measurable_updateGroupGaugeLink_right G W _ _))
      hh_bdd V
  rw [integral_groupGibbsMeasure G S_act hS_meas hS_bdd (fun V => h V * ψ V),
    integral_groupGibbsMeasure G S_act hS_meas hS_bdd
      (fun V => singleLinkGibbsOperator G L S_act e₀ h V * ψ V)]
  refine congrArg (fun x => x / groupGibbsPartition G L S_act) ?_
  let H₁ : GroupGaugeConfig G L → ℝ := fun V => Real.exp (-S_act V) * (h V * ψ V)
  let H₂ : GroupGaugeConfig G L → ℝ := fun V =>
    Real.exp (-S_act V) * (singleLinkGibbsOperator G L S_act e₀ h V * ψ V)
  have h_w_le (V : GroupGaugeConfig G L) : Real.exp (-S_act V) ≤ Real.exp B :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hS_bdd V)).1])
  have hH₁_meas : Measurable H₁ :=
    (Real.continuous_exp.measurable.comp hS_meas.neg).mul (hh_meas.mul hψ_meas)
  have hH₂_meas : Measurable H₂ :=
    (Real.continuous_exp.measurable.comp hS_meas.neg).mul (hPh_meas.mul hψ_meas)
  have hH₁_bdd (V : GroupGaugeConfig G L) : |H₁ V| ≤ Real.exp B * (M_h * M_ψ) := by
    dsimp [H₁]
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (h_w_le V)
      (mul_le_mul (hh_bdd V) (hψ_bdd V) (abs_nonneg _) hMh_nonneg)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le
  have hH₂_bdd (V : GroupGaugeConfig G L) : |H₂ V| ≤ Real.exp B * (M_h * M_ψ) := by
    dsimp [H₂]
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (h_w_le V)
      (mul_le_mul (hPh_bdd V) (hψ_bdd V) (abs_nonneg _) hMh_nonneg)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le
  rw [integral_groupGaugeHaarMeasure_eq_integral_updateGroupGaugeLink G e₀ H₁ hH₁_meas hH₁_bdd,
    integral_groupGaugeHaarMeasure_eq_integral_updateGroupGaugeLink G e₀ H₂ hH₂_meas hH₂_bdd]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  dsimp [H₁, H₂]
  have hZ_pos : 0 < groupSingleLinkPartition G L S_act V e₀ := by
    have h_w_ge (g : G) :
        Real.exp (-B) ≤ Real.exp (-S_act (updateGroupGaugeLink L V e₀.x e₀.μ g)) :=
      Real.exp_le_exp.mpr
        (by linarith [(abs_le.mp (hS_bdd (updateGroupGaugeLink L V e₀.x e₀.μ g))).2])
    have h_int_w :
        Integrable (fun g : G => Real.exp (-S_act (updateGroupGaugeLink L V e₀.x e₀.μ g)))
          (compactGroupHaarProbability G) := by
      refine (integrable_const (Real.exp B)).mono'
        (Real.continuous_exp.measurable.comp
          ((hS_meas.comp (measurable_updateGroupGaugeLink_right G V e₀.x e₀.μ)).neg)).aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact h_w_le _
    have h_lo :
        (∫ _ : G, Real.exp (-B) ∂(compactGroupHaarProbability G : Measure G)) ≤
          groupSingleLinkPartition G L S_act V e₀ :=
      integral_mono (integrable_const _) h_int_w h_w_ge
    rw [integral_const, probReal_univ, one_smul] at h_lo
    exact lt_of_lt_of_le (Real.exp_pos (-B)) h_lo
  have h_lhs :
      (∫ g : G,
        Real.exp (-S_act (updateGroupGaugeLink L V e₀.x e₀.μ g)) *
          (h (updateGroupGaugeLink L V e₀.x e₀.μ g) *
            ψ (updateGroupGaugeLink L V e₀.x e₀.μ g))
        ∂(compactGroupHaarProbability G : Measure G)) =
      (∫ g : G,
        Real.exp (-S_act (updateGroupGaugeLink L V e₀.x e₀.μ g)) *
          h (updateGroupGaugeLink L V e₀.x e₀.μ g)
        ∂(compactGroupHaarProbability G : Measure G)) * ψ V := by
    simp_rw [hψ_inv V, ← mul_assoc, integral_mul_const]
  have h_rhs :
      (∫ g : G,
        Real.exp (-S_act (updateGroupGaugeLink L V e₀.x e₀.μ g)) *
          (singleLinkGibbsOperator G L S_act e₀ h (updateGroupGaugeLink L V e₀.x e₀.μ g) *
            ψ (updateGroupGaugeLink L V e₀.x e₀.μ g))
        ∂(compactGroupHaarProbability G : Measure G)) =
      groupSingleLinkPartition G L S_act V e₀ *
        singleLinkGibbsOperator G L S_act e₀ h V * ψ V := by
    simp_rw [singleLinkGibbsOperator_update_self G S_act e₀ h V, hψ_inv V, ← mul_assoc,
      integral_mul_const]
    rfl
  rw [h_lhs, h_rhs]
  unfold singleLinkGibbsOperator groupSingleLinkCondExp
  rw [mul_div_cancel₀ _ hZ_pos.ne']

/-- Single-link Gibbs operator expectation invariance under `groupGibbsMeasure G L S_act`:
$\int (\Pi_{e_0} h)(V) \, d\mu_{\mathrm{Gibbs}}(V) = \int h(V) \, d\mu_{\mathrm{Gibbs}}(V)$. -/
theorem integral_groupGibbsMeasure_singleLinkGibbsOperator_eq
    (G : Type*) [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ) {B : ℝ}
    (hS_meas : Measurable S_act) (hS_bdd : ∀ V : GroupGaugeConfig G L, |S_act V| ≤ B)
    (e₀ : Link L) (h : GroupGaugeConfig G L → ℝ) {M_h : ℝ}
    (hh_meas : Measurable h) (hh_bdd : ∀ V : GroupGaugeConfig G L, |h V| ≤ M_h) :
    (∫ V, singleLinkGibbsOperator G L S_act e₀ h V ∂(groupGibbsMeasure G L S_act)) =
      ∫ V, h V ∂(groupGibbsMeasure G L S_act) := by
  simpa using
    (integral_groupGibbsMeasure_mul_invariant_eq_singleLinkGibbsOperator
      G S_act hS_meas hS_bdd e₀ h (fun _ => 1) hh_meas hh_bdd
      measurable_const (fun _ => by norm_num : ∀ V, |(1 : ℝ)| ≤ 1) (fun _ _ => rfl)).symm

/-- Single-link conditional covariance step inequality for `groupGibbsMeasure G L S_act`:
$$|\mathrm{groupGibbsCov}\ \mu_{\mathrm{Gibbs}}\ h\ g| \le |\mathrm{groupGibbsCov}\ \mu_{\mathrm{Gibbs}}\ (\Pi_{e_0} h)\ g| + \delta_{e_0}(h)\,\delta_{e_0}(g).$$ -/
theorem abs_groupGibbsCov_le_singleLinkGibbsOperator_add_linkOscillation
    (G : Type*) [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ) {B : ℝ}
    (hS_meas : Measurable S_act) (hS_bdd : ∀ V : GroupGaugeConfig G L, |S_act V| ≤ B)
    (e₀ : Link L) (h g : GroupGaugeConfig G L → ℝ) {M_h M_g : ℝ}
    (hh_meas : Measurable h) (hh_bdd : ∀ V : GroupGaugeConfig G L, |h V| ≤ M_h)
    (hg_meas : Measurable g) (hg_bdd : ∀ V : GroupGaugeConfig G L, |g V| ≤ M_g) :
    |groupGibbsCov (groupGibbsMeasure G L S_act) h g| ≤
      |groupGibbsCov (groupGibbsMeasure G L S_act)
        (singleLinkGibbsOperator G L S_act e₀ h) g| +
        linkOscillation G L h e₀ * linkOscillation G L g e₀ := by
  have : IsProbabilityMeasure (groupGibbsMeasure G L S_act) :=
    groupGibbsMeasure_isProbabilityMeasure G S_act hS_meas hS_bdd
  let μ := groupGibbsMeasure G L S_act
  let Ph := singleLinkGibbsOperator G L S_act e₀ h
  let Pg := singleLinkGibbsOperator G L S_act e₀ g
  have hMh_nonneg : 0 ≤ M_h := le_trans (abs_nonneg _) (hh_bdd (fun _ => 1))
  have hMg_nonneg : 0 ≤ M_g := le_trans (abs_nonneg _) (hg_bdd (fun _ => 1))
  have hPh_meas : Measurable Ph := measurable_singleLinkGibbsOperator G S_act e₀ h hS_meas hh_meas
  have hPg_meas : Measurable Pg := measurable_singleLinkGibbsOperator G S_act e₀ g hS_meas hg_meas
  have hPh_bdd (V : GroupGaugeConfig G L) : |Ph V| ≤ M_h :=
    abs_singleLinkGibbsOperator_le G S_act e₀ h
      (fun W => hS_meas.comp (measurable_updateGroupGaugeLink_right G W _ _))
      (fun W => ⟨B, fun u => hS_bdd _⟩)
      (fun W => hh_meas.comp (measurable_updateGroupGaugeLink_right G W _ _))
      hh_bdd V
  have hPg_bdd (V : GroupGaugeConfig G L) : |Pg V| ≤ M_g :=
    abs_singleLinkGibbsOperator_le G S_act e₀ g
      (fun W => hS_meas.comp (measurable_updateGroupGaugeLink_right G W _ _))
      (fun W => ⟨B, fun u => hS_bdd _⟩)
      (fun W => hg_meas.comp (measurable_updateGroupGaugeLink_right G W _ _))
      hg_bdd V
  have h_orth : (∫ V, h V * Pg V ∂μ) = ∫ V, Ph V * Pg V ∂μ :=
    integral_groupGibbsMeasure_mul_invariant_eq_singleLinkGibbsOperator
      G S_act hS_meas hS_bdd e₀ h Pg hh_meas hh_bdd hPg_meas hPg_bdd
      (singleLinkGibbsOperator_update_self G S_act e₀ g)
  have h_exp_eq : (∫ V, Ph V ∂μ) = ∫ V, h V ∂μ :=
    integral_groupGibbsMeasure_singleLinkGibbsOperator_eq
      G S_act hS_meas hS_bdd e₀ h hh_meas hh_bdd
  have h_int_hg : Integrable (fun V => h V * g V) μ := by
    refine (integrable_const (M_h * M_g)).mono' (hh_meas.mul hg_meas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun V => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hh_bdd V) (hg_bdd V) (abs_nonneg _) hMh_nonneg
  have h_int_Phg : Integrable (fun V => Ph V * g V) μ := by
    refine (integrable_const (M_h * M_g)).mono' (hPh_meas.mul hg_meas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun V => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hPh_bdd V) (hg_bdd V) (abs_nonneg _) hMh_nonneg
  have h_int_hPg : Integrable (fun V => h V * Pg V) μ := by
    refine (integrable_const (M_h * M_g)).mono' (hh_meas.mul hPg_meas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun V => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hh_bdd V) (hPg_bdd V) (abs_nonneg _) hMh_nonneg
  have h_int_PhPg : Integrable (fun V => Ph V * Pg V) μ := by
    refine (integrable_const (M_h * M_g)).mono' (hPh_meas.mul hPg_meas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun V => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hPh_bdd V) (hPg_bdd V) (abs_nonneg _) hMh_nonneg
  have h_int_diff1 : Integrable (fun V => h V * g V - Ph V * g V) μ := h_int_hg.sub h_int_Phg
  have h_int_diff2 : Integrable (fun V => h V * Pg V - Ph V * Pg V) μ := h_int_hPg.sub h_int_PhPg
  have h_cov_diff :
      groupGibbsCov μ h g - groupGibbsCov μ Ph g =
        ∫ V, (h V - Ph V) * (g V - Pg V) ∂μ := by
    have h_alg :
        (fun V => (h V - Ph V) * (g V - Pg V)) =
          fun V => (h V * g V - Ph V * g V) - (h V * Pg V - Ph V * Pg V) := by
      funext V
      ring
    rw [h_alg, integral_sub h_int_diff1 h_int_diff2,
      integral_sub h_int_hg h_int_Phg, integral_sub h_int_hPg h_int_PhPg, h_orth, sub_self,
      sub_zero]
    unfold groupGibbsCov
    rw [h_exp_eq]
    ring
  have h_prod_int : Integrable (fun V => (h V - Ph V) * (g V - Pg V)) μ := by
    have h_alg :
        (fun V => (h V - Ph V) * (g V - Pg V)) =
          fun V => (h V * g V - Ph V * g V) - (h V * Pg V - Ph V * Pg V) := by
      funext V
      ring
    rw [h_alg]
    exact h_int_diff1.sub h_int_diff2
  have h_diff_le :
      |groupGibbsCov μ h g - groupGibbsCov μ Ph g| ≤
        linkOscillation G L h e₀ * linkOscillation G L g e₀ := by
    rw [h_cov_diff]
    calc
      |∫ V, (h V - Ph V) * (g V - Pg V) ∂μ|
        ≤ ∫ V, |(h V - Ph V) * (g V - Pg V)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ : GroupGaugeConfig G L,
            linkOscillation G L h e₀ * linkOscillation G L g e₀ ∂μ := by
          refine integral_mono h_prod_int.abs (integrable_const _) fun V => ?_
          dsimp only
          rw [abs_mul]
          have hh_osc : |h V - Ph V| ≤ linkOscillation G L h e₀ :=
            abs_sub_singleLinkGibbsOperator_le_linkOscillation G S_act e₀ h V
              (hS_meas.comp (measurable_updateGroupGaugeLink_right G V e₀.x e₀.μ))
              ⟨B, fun u => hS_bdd _⟩
              (hh_meas.comp (measurable_updateGroupGaugeLink_right G V e₀.x e₀.μ))
              hh_bdd
          have hg_osc : |g V - Pg V| ≤ linkOscillation G L g e₀ :=
            abs_sub_singleLinkGibbsOperator_le_linkOscillation G S_act e₀ g V
              (hS_meas.comp (measurable_updateGroupGaugeLink_right G V e₀.x e₀.μ))
              ⟨B, fun u => hS_bdd _⟩
              (hg_meas.comp (measurable_updateGroupGaugeLink_right G V e₀.x e₀.μ))
              hg_bdd
          exact mul_le_mul hh_osc hg_osc (abs_nonneg _) (linkOscillation_nonneg G L h e₀)
      _ = linkOscillation G L h e₀ * linkOscillation G L g e₀ := by
          rw [integral_const, probReal_univ, one_smul]
  calc
    |groupGibbsCov μ h g|
      = |(groupGibbsCov μ h g - groupGibbsCov μ Ph g) + groupGibbsCov μ Ph g| := by ring_nf
    _ ≤ |groupGibbsCov μ h g - groupGibbsCov μ Ph g| + |groupGibbsCov μ Ph g| := abs_add_le _ _
    _ ≤ |groupGibbsCov μ Ph g| + linkOscillation G L h e₀ * linkOscillation G L g e₀ := by
        linarith

/-- Unconditional Föllmer–Dobrushin covariance comparison theorem for the actual finite-volume Gibbs
measure `groupGibbsMeasure G L S_act`: whenever `S_act` is measurable and bounded and its supremum
Dobrushin interdependence matrix `dobrushinSupMatrix G L S_act` has row sum bounded by `q < 1`,
every pair of measurable bounded observables `f, g : GroupGaugeConfig G L → ℝ` satisfies
$$|\mathrm{groupGibbsCov}\ (\mathrm{groupGibbsMeasure}\ G\ L\ S_{\mathrm{act}})\ f\ g| \le \sum_{e, e'} \delta_e(f)\,D_{e, e'}(\mathrm{dobrushinSupMatrix}\ G\ L\ S_{\mathrm{act}})\,\delta_{e'}(g).$$ -/
theorem groupGibbsMeasure_abs_cov_le_dobrushinObservableComparison
    (G : Type*) [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ)
    {q B M_f M_g : ℝ} (hq : 0 ≤ q) (hq_lt : q < 1)
    (h_row : ∀ e : Link L, (∑ e' : Link L, dobrushinSupMatrix G L S_act e e') ≤ q)
    (hS_meas : Measurable S_act) (hS_bdd : ∀ V : GroupGaugeConfig G L, |S_act V| ≤ B)
    (f g : GroupGaugeConfig G L → ℝ)
    (hf_meas : Measurable f) (hf_bdd : ∀ V : GroupGaugeConfig G L, |f V| ≤ M_f)
    (hg_meas : Measurable g) (hg_bdd : ∀ V : GroupGaugeConfig G L, |g V| ≤ M_g) :
    |groupGibbsCov (groupGibbsMeasure G L S_act) f g| ≤
      dobrushinObservableComparison G (dobrushinSupMatrix G L S_act) f g := by
  have : IsProbabilityMeasure (groupGibbsMeasure G L S_act) :=
    groupGibbsMeasure_isProbabilityMeasure G S_act hS_meas hS_bdd
  have hMg_nonneg : 0 ≤ M_g := le_trans (abs_nonneg _) (hg_bdd (fun _ => 1))
  let F := greedySingleLinkGibbsChain G L S_act f
  let e_seq := greedySingleLinkGibbsLinkSeq G L S_act f
  have hF_meas (K : ℕ) : Measurable (F K) :=
    measurable_greedySingleLinkGibbsChain G S_act f hS_meas hf_meas K
  have hF_bdd (K : ℕ) (V : GroupGaugeConfig G L) : |F K V| ≤ M_f :=
    abs_greedySingleLinkGibbsChain_le G S_act f hS_meas hS_bdd hf_meas hf_bdd K V
  have h_chain :=
    follmer_dobrushin_covariance_comparison_of_georgii_chain
      G (dobrushinSupMatrix G L S_act) hq hq_lt zero_le_one
      (dobrushinSupMatrix_diag G L S_act)
      (dobrushinSupMatrix_nonneg G L S_act)
      h_row
      (groupGibbsCov (groupGibbsMeasure G L S_act))
      f g F e_seq rfl
      (fun K => linkOscillation_singleLinkGibbsOperator_self G S_act (e_seq K) (F K))
      (fun K e he =>
        linkOscillation_singleLinkGibbsOperator_le_of_ne G S_act (e_seq K) e he (F K)
          (fun W => hS_meas.comp (measurable_updateGroupGaugeLink_right G W _ _))
          (fun W => ⟨B, fun u => hS_bdd _⟩)
          (fun W => (hF_meas K).comp (measurable_updateGroupGaugeLink_right G W _ _))
          ⟨M_f, hF_bdd K⟩)
      (fun K => by
        change |groupGibbsCov (groupGibbsMeasure G L S_act) (F K) g| ≤
          |groupGibbsCov (groupGibbsMeasure G L S_act)
            (singleLinkGibbsOperator G L S_act (e_seq K) (F K)) g| +
            1 * (linkOscillation G L (F K) (e_seq K) * linkOscillation G L g (e_seq K))
        simpa only [one_mul] using
          abs_groupGibbsCov_le_singleLinkGibbsOperator_add_linkOscillation
            G S_act hS_meas hS_bdd (e_seq K) (F K) g
            (hF_meas K) (hF_bdd K) hg_meas hg_bdd)
  have h_tendsto_osc :=
    tendsto_sum_linkOscillation_greedySingleLinkGibbsChain_zero
      G S_act hq hq_lt h_row f hS_meas hS_bdd hf_meas hf_bdd
  have h_tendsto_cov :
      Filter.Tendsto
        (fun K : ℕ => |groupGibbsCov (groupGibbsMeasure G L S_act) (F K) g|)
        Filter.atTop (nhds 0) := by
    have h_rhs :
        Filter.Tendsto
          (fun K : ℕ => 2 * M_g * (∑ e : Link L, linkOscillation G L (F K) e))
          Filter.atTop (nhds 0) := by
      simpa [mul_zero] using h_tendsto_osc.const_mul (2 * M_g)
    exact squeeze_zero
      (fun K => abs_nonneg _)
      (fun K =>
        abs_groupGibbsCov_le_two_mul_sum_linkOscillation
          G (groupGibbsMeasure G L S_act) (F K) g (hF_meas K) (hF_bdd K) hg_meas hg_bdd)
      h_rhs
  simpa only [one_mul] using h_chain.2 h_tendsto_cov

/-! ### Concrete Torus Link Metric (`zmodCyclicDist`, `linkTemporalDist`, `linkSupDist`), `dobrushinNeighbors` Step-1 Locality & Georgii Theorem 8.20 (Exponentially Tilted Nonlocal Dobrushin Decay) -/

/-- Cyclic distance on `ZMod L`: `min (a - b).val (b - a).val`. -/
def zmodCyclicDist (L : ℕ) (a b : ZMod L) : ℕ :=
  min (a - b).val (b - a).val

@[simp]
theorem zmodCyclicDist_self (L : ℕ) [NeZero L] (a : ZMod L) :
    zmodCyclicDist L a a = 0 := by
  simp [zmodCyclicDist]

theorem zmodCyclicDist_comm (L : ℕ) (a b : ZMod L) :
    zmodCyclicDist L a b = zmodCyclicDist L b a := by
  unfold zmodCyclicDist
  exact min_comm _ _

theorem zmod_val_add_le (L : ℕ) [NeZero L] (u v : ZMod L) :
    (u + v).val ≤ u.val + v.val := by
  rw [ZMod.val_add]
  exact Nat.mod_le _ _

theorem zmod_min_val_sub_le_add_val (L : ℕ) [NeZero L] (u v : ZMod L) :
    min (u - v).val (v - u).val ≤ u.val + v.val := by
  rcases le_total v.val u.val with h | h
  · have h_cast : (((u.val - v.val : ℕ) : ZMod L)) = u - v := by
      rw [Nat.cast_sub h, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have h_val : (u - v).val ≤ u.val - v.val := by
      rw [← h_cast, ZMod.val_natCast]
      exact Nat.mod_le _ _
    exact le_trans (min_le_left _ _) (by omega)
  · have h_cast : (((v.val - u.val : ℕ) : ZMod L)) = v - u := by
      rw [Nat.cast_sub h, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have h_val : (v - u).val ≤ v.val - u.val := by
      rw [← h_cast, ZMod.val_natCast]
      exact Nat.mod_le _ _
    exact le_trans (min_le_right _ _) (by omega)

/-- Triangle inequality for `zmodCyclicDist` on `ZMod L`. -/
theorem zmodCyclicDist_triangle (L : ℕ) [NeZero L] (a b c : ZMod L) :
    zmodCyclicDist L a c ≤ zmodCyclicDist L a b + zmodCyclicDist L b c := by
  unfold zmodCyclicDist
  set x := a - b
  set y := b - c
  have h_ac : a - c = x + y := by dsimp [x, y]; ring
  have h_ca : c - a = (-x) + (-y) := by dsimp [x, y]; ring
  have h_ba : b - a = -x := by dsimp [x]; ring
  have h_cb : c - b = -y := by dsimp [y]; ring
  rw [h_ac, h_ca, h_ba, h_cb]
  have h1 : min (x + y).val ((-x) + (-y)).val ≤ x.val + y.val :=
    le_trans (min_le_left _ _) (zmod_val_add_le L x y)
  have h2 : min (x + y).val ((-x) + (-y)).val ≤ (-x).val + (-y).val :=
    le_trans (min_le_right _ _) (zmod_val_add_le L (-x) (-y))
  have h3 : min (x + y).val ((-x) + (-y)).val ≤ x.val + (-y).val := by
    have h_eq1 : x + y = x - (-y) := by ring
    have h_eq2 : (-x) + (-y) = (-y) - x := by ring
    rw [h_eq1, h_eq2]
    exact zmod_min_val_sub_le_add_val L x (-y)
  have h4 : min (x + y).val ((-x) + (-y)).val ≤ (-x).val + y.val := by
    have h_eq1 : x + y = y - (-x) := by ring
    have h_eq2 : (-x) + (-y) = (-x) - y := by ring
    rw [h_eq1, h_eq2, add_comm]
    exact zmod_min_val_sub_le_add_val L y (-x)
  rcases min_cases x.val (-x).val with ⟨hx, _⟩ | ⟨hx, _⟩ <;>
    rcases min_cases y.val (-y).val with ⟨hy, _⟩ | ⟨hy, _⟩ <;>
    omega

/-- For any `a : ZMod L`, the cyclic distance between `a` and `a + 1` is at most `1`. -/
theorem zmodCyclicDist_add_one_right_le_one (L : ℕ) [NeZero L] (a : ZMod L) :
    zmodCyclicDist L a (a + 1) ≤ 1 := by
  unfold zmodCyclicDist
  have h_sub : (a + 1) - a = ((1 : ℕ) : ZMod L) := by ring
  calc
    min (a - (a + 1)).val ((a + 1) - a).val
      ≤ ((a + 1) - a).val := min_le_right _ _
    _ = ((1 : ℕ) : ZMod L).val := by rw [h_sub]
    _ = 1 % L := ZMod.val_natCast L 1
    _ ≤ 1 := Nat.mod_le 1 L

theorem zmodCyclicDist_add_one_left_le_one (L : ℕ) [NeZero L] (a : ZMod L) :
    zmodCyclicDist L (a + 1) a ≤ 1 := by
  rw [zmodCyclicDist_comm]
  exact zmodCyclicDist_add_one_right_le_one L a

/-- Lower bound on `zmodCyclicDist L (m : ZMod L) (m' : ZMod L)` for integer coordinates
`m, m' : ℤ` separated by `(t : ℤ) ≤ m' - m ≤ (D : ℤ)` on a torus of side `L > 2 * D`. -/
theorem zmodCyclicDist_intCast_ge_of_le (L : ℕ) [NeZero L]
    {m m' : ℤ} {t D : ℕ}
    (h_lo : (t : ℤ) ≤ m' - m) (h_hi : m' - m ≤ (D : ℤ)) (hL : 2 * D < L) :
    t ≤ zmodCyclicDist L (m : ZMod L) (m' : ZMod L) := by
  set d : ℕ := (m' - m).toNat
  have hd_cast : ((d : ℕ) : ℤ) = m' - m := Int.toNat_of_nonneg (by omega)
  have ht_le_d : t ≤ d := by omega
  have hd_le_D : d ≤ D := by omega
  have hd_lt_L : d < L := by omega
  by_cases hd0 : d = 0
  · have ht0 : t = 0 := by omega
    rw [ht0]
    exact Nat.zero_le _
  · have h_diff1 : (m' : ZMod L) - (m : ZMod L) = ((d : ℕ) : ZMod L) := by
      rw [← Int.cast_sub, ← hd_cast, Int.cast_natCast]
    have h_val1 : ((m' : ZMod L) - (m : ZMod L)).val = d := by
      rw [h_diff1]
      exact ZMod.val_natCast_of_lt hd_lt_L
    have h_diff2 : (m : ZMod L) - (m' : ZMod L) = ((L - d : ℕ) : ZMod L) := by
      have h_sub_nat : ((L - d : ℕ) : ZMod L) = (L : ZMod L) - ((d : ℕ) : ZMod L) :=
        Nat.cast_sub (le_of_lt hd_lt_L)
      rw [h_sub_nat, ZMod.natCast_self, zero_sub, ← h_diff1]
      ring
    have h_val2 : ((m : ZMod L) - (m' : ZMod L)).val = L - d := by
      rw [h_diff2]
      exact ZMod.val_natCast_of_lt (by omega)
    unfold zmodCyclicDist
    rw [h_val1, h_val2]
    exact le_min (by omega) ht_le_d

/-- Temporal cyclic distance between two lattice links `e, e' : Link L` along Euclidean time `0 : Fin 4`. -/
def linkTemporalDist {L : ℕ} (e e' : Link L) : ℕ :=
  zmodCyclicDist L (e.x 0) (e'.x 0)

/-- 4D $\ell_\infty$ cyclic distance on `Link L`: maximum of `zmodCyclicDist L (e.x i) (e'.x i)` over `i : Fin 4`. -/
def linkSupDist {L : ℕ} (e e' : Link L) : ℕ :=
  Finset.univ.sup (fun i : Fin 4 => zmodCyclicDist L (e.x i) (e'.x i))

@[simp]
theorem linkTemporalDist_self {L : ℕ} [NeZero L] (e : Link L) :
    linkTemporalDist e e = 0 :=
  zmodCyclicDist_self L (e.x 0)

theorem linkTemporalDist_comm {L : ℕ} (e e' : Link L) :
    linkTemporalDist e e' = linkTemporalDist e' e :=
  zmodCyclicDist_comm L (e.x 0) (e'.x 0)

theorem linkTemporalDist_triangle {L : ℕ} [NeZero L] (e₁ e₂ e₃ : Link L) :
    linkTemporalDist e₁ e₃ ≤ linkTemporalDist e₁ e₂ + linkTemporalDist e₂ e₃ :=
  zmodCyclicDist_triangle L (e₁.x 0) (e₂.x 0) (e₃.x 0)

@[simp]
theorem linkSupDist_self {L : ℕ} [NeZero L] (e : Link L) :
    linkSupDist e e = 0 := by
  unfold linkSupDist
  exact le_antisymm (Finset.sup_le fun i _ => by rw [zmodCyclicDist_self]) (Nat.zero_le _)

theorem linkSupDist_comm {L : ℕ} (e e' : Link L) :
    linkSupDist e e' = linkSupDist e' e := by
  unfold linkSupDist
  congr 1
  funext i
  exact zmodCyclicDist_comm L (e.x i) (e'.x i)

theorem linkSupDist_triangle {L : ℕ} [NeZero L] (e₁ e₂ e₃ : Link L) :
    linkSupDist e₁ e₃ ≤ linkSupDist e₁ e₂ + linkSupDist e₂ e₃ := by
  unfold linkSupDist
  refine Finset.sup_le fun i hi => ?_
  calc
    zmodCyclicDist L (e₁.x i) (e₃.x i)
      ≤ zmodCyclicDist L (e₁.x i) (e₂.x i) + zmodCyclicDist L (e₂.x i) (e₃.x i) :=
        zmodCyclicDist_triangle L (e₁.x i) (e₂.x i) (e₃.x i)
    _ ≤ Finset.univ.sup (fun j : Fin 4 => zmodCyclicDist L (e₁.x j) (e₂.x j)) +
          Finset.univ.sup (fun j : Fin 4 => zmodCyclicDist L (e₂.x j) (e₃.x j)) :=
        Nat.add_le_add
          (Finset.le_sup (f := fun j : Fin 4 => zmodCyclicDist L (e₁.x j) (e₂.x j)) hi)
          (Finset.le_sup (f := fun j : Fin 4 => zmodCyclicDist L (e₂.x j) (e₃.x j)) hi)

theorem linkTemporalDist_le_linkSupDist {L : ℕ} (e e' : Link L) :
    linkTemporalDist e e' ≤ linkSupDist e e' :=
  Finset.le_sup (f := fun i : Fin 4 => zmodCyclicDist L (e.x i) (e'.x i)) (Finset.mem_univ 0)

/-- Every boundary link `f ∈ plaquetteBoundaryLinks p` of a plaquette `p : Plaquette L` has
base coordinate `f.x i = p.x i` or `f.x i = p.x i + 1` in each direction `i : Fin 4`. -/
theorem mem_plaquetteBoundaryLinks_coord_eq_or_add_one {L : ℕ}
    (p : Plaquette L) {f : Link L} (hf : f ∈ plaquetteBoundaryLinks p) (i : Fin 4) :
    f.x i = p.x i ∨ f.x i = p.x i + 1 := by
  classical
  unfold plaquetteBoundaryLinks at hf
  rcases Finset.mem_insert.mp hf with rfl | hf
  · exact Or.inl rfl
  rcases Finset.mem_insert.mp hf with rfl | hf
  · dsimp [shift, unitVec]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl (add_zero _)
  rcases Finset.mem_insert.mp hf with rfl | hf
  · dsimp [shift, unitVec]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl (add_zero _)
  · rcases Finset.mem_singleton.mp hf with rfl
    exact Or.inl rfl

/-- Any two links `e, e'` belonging to `plaquetteBoundaryLinks p` of a common plaquette `p` have
4D $\ell_\infty$ cyclic link distance `linkSupDist e e' ≤ 1`. -/
theorem linkSupDist_le_one_of_mem_plaquetteBoundaryLinks {L : ℕ} [NeZero L]
    (p : Plaquette L) {e e' : Link L}
    (he : e ∈ plaquetteBoundaryLinks p) (he' : e' ∈ plaquetteBoundaryLinks p) :
    linkSupDist e e' ≤ 1 := by
  unfold linkSupDist
  refine Finset.sup_le fun i _ => ?_
  rcases mem_plaquetteBoundaryLinks_coord_eq_or_add_one p he i with h1 | h1 <;>
    rcases mem_plaquetteBoundaryLinks_coord_eq_or_add_one p he' i with h2 | h2 <;>
    rw [h1, h2]
  · rw [zmodCyclicDist_self]
    exact Nat.zero_le 1
  · exact zmodCyclicDist_add_one_right_le_one L (p.x i)
  · exact zmodCyclicDist_add_one_left_le_one L (p.x i)
  · rw [zmodCyclicDist_self]
    exact Nat.zero_le 1

/-- Every link `e' ∈ dobrushinNeighbors e` lies within 4D $\ell_\infty$ cyclic distance
`linkSupDist e e' ≤ 1` of `e`. -/
theorem linkSupDist_le_one_of_mem_dobrushinNeighbors {L : ℕ} [NeZero L]
    {e e' : Link L} (he' : e' ∈ dobrushinNeighbors e) :
    linkSupDist e e' ≤ 1 := by
  classical
  unfold dobrushinNeighbors at he'
  rcases Finset.mem_biUnion.mp he' with ⟨p, hp, he'_p⟩
  exact linkSupDist_le_one_of_mem_plaquetteBoundaryLinks p
    (mem_plaquetteBoundaryLinks_of_mem_incidentPlaquettes e p hp)
    (Finset.mem_of_mem_erase he'_p)

/-- Every link `e' ∈ dobrushinNeighbors e` lies within temporal cyclic distance
`linkTemporalDist e e' ≤ 1` of `e`. -/
theorem linkTemporalDist_le_one_of_mem_dobrushinNeighbors {L : ℕ} [NeZero L]
    {e e' : Link L} (he' : e' ∈ dobrushinNeighbors e) :
    linkTemporalDist e e' ≤ 1 :=
  (linkTemporalDist_le_linkSupDist e e').trans (linkSupDist_le_one_of_mem_dobrushinNeighbors he')

/-- For the local Wilson action `groupWilsonAction tr β`, `dobrushinSupMatrix` vanishes outside
`dobrushinNeighbors e`, so `dobrushinSupMatrix G L (groupWilsonAction tr β) e e' ≠ 0` implies
`e' ∈ dobrushinNeighbors e`, `linkSupDist e e' ≤ 1`, and `linkTemporalDist e e' ≤ 1`. -/
theorem dobrushinSupMatrix_groupWilsonAction_ne_zero_imp_dist_le_one
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (tr : CompactGaugeClassTrace G) {L : ℕ} [NeZero L] (β : ℝ)
    {e e' : Link L}
    (hne : dobrushinSupMatrix G L (groupWilsonAction tr β) e e' ≠ 0) :
    e' ∈ dobrushinNeighbors e ∧ linkSupDist e e' ≤ 1 ∧ linkTemporalDist e e' ≤ 1 := by
  have he_ne : e' ≠ e := by
    intro h_eq
    subst h_eq
    exact hne (dobrushinSupMatrix_diag G L (groupWilsonAction tr β) e')
  have h_mem : e' ∈ dobrushinNeighbors e := by
    by_contra h_not_mem
    refine hne (le_antisymm ?_ (dobrushinSupMatrix_nonneg G L (groupWilsonAction tr β) e e'))
    refine dobrushinSupMatrix_le_of_forall G (groupWilsonAction tr β) le_rfl ?_
    intro V h1 h2 φ _ _
    rw [groupWilson_singleLinkCondExp_eq_of_not_mem_dobrushinNeighbors G tr β V e e'
      he_ne h_not_mem h1 h2 φ, sub_self, abs_zero]
  exact ⟨h_mem,
    linkSupDist_le_one_of_mem_dobrushinNeighbors h_mem,
    linkTemporalDist_le_one_of_mem_dobrushinNeighbors h_mem⟩

/-- Exponentially tilted Dobrushin interdependence matrix
$\widetilde{C}_{e, e'} = \mu^{\mathrm{dist}(e, e')}\, C_{e, e'}$ (Georgii, *Gibbs Measures and
Phase Transitions*, Theorem 8.20) for a general (potentially nonlocal) interdependence matrix `C`. -/
noncomputable def dobrushinTiltedMatrix {L : ℕ}
    (C : Link L → Link L → ℝ) (distLink : Link L → Link L → ℕ) (μ : ℝ)
    (e e' : Link L) : ℝ :=
  μ ^ (distLink e e') * C e e'

theorem dobrushinTiltedMatrix_nonneg {L : ℕ}
    (C : Link L → Link L → ℝ) (distLink : Link L → Link L → ℕ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e') (e e' : Link L) :
    0 ≤ dobrushinTiltedMatrix C distLink μ e e' :=
  mul_nonneg (pow_nonneg hμ _) (hC_nonneg e e')

/-- Submultiplicativity of matrix powers under exponential metric tilting (Georgii Theorem 8.20):
for any pseudo-metric `distLink` (`distLink e e = 0`, triangle inequality) and any `μ ≥ 1`,
$\mu^{\mathrm{dist}(e, e')} (C^m)_{e, e'} \le (\widetilde{C}^m)_{e, e'}$ for every power $m \ge 0$,
with no finite-range restriction on $C$. -/
theorem mul_pow_dobrushinMatrixPow_le_tilted {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) (distLink : Link L → Link L → ℕ) {μ : ℝ} (hμ : 1 ≤ μ)
    (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e')
    (h_refl : ∀ e : Link L, distLink e e = 0)
    (h_tri : ∀ e e'' e' : Link L, distLink e e' ≤ distLink e e'' + distLink e'' e') :
    ∀ (m : ℕ) (e e' : Link L),
      μ ^ (distLink e e') * dobrushinMatrixPow C m e e' ≤
        dobrushinMatrixPow (dobrushinTiltedMatrix C distLink μ) m e e'
  | 0, e, e' => by
      dsimp [dobrushinMatrixPow]
      split_ifs with h_eq
      · subst h_eq
        rw [h_refl, pow_zero, mul_one]
      · rw [mul_zero]
  | m + 1, e, e' => by
      dsimp [dobrushinMatrixPow]
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun e'' _ => ?_
      have h_pow_le :
          μ ^ (distLink e e') ≤ μ ^ (distLink e e'') * μ ^ (distLink e'' e') := by
        rw [← pow_add]
        exact pow_le_pow_right₀ hμ (h_tri e e'' e')
      have h_term_nonneg : 0 ≤ C e e'' * dobrushinMatrixPow C m e'' e' :=
        mul_nonneg (hC_nonneg e e'') (dobrushinMatrixPow_nonneg C hC_nonneg m e'' e')
      calc
        μ ^ (distLink e e') * (C e e'' * dobrushinMatrixPow C m e'' e')
          ≤ (μ ^ (distLink e e'') * μ ^ (distLink e'' e')) *
              (C e e'' * dobrushinMatrixPow C m e'' e') :=
            mul_le_mul_of_nonneg_right h_pow_le h_term_nonneg
        _ = dobrushinTiltedMatrix C distLink μ e e'' *
              (μ ^ (distLink e'' e') * dobrushinMatrixPow C m e'' e') := by
            unfold dobrushinTiltedMatrix
            ring
        _ ≤ dobrushinTiltedMatrix C distLink μ e e'' *
              dobrushinMatrixPow (dobrushinTiltedMatrix C distLink μ) m e'' e' :=
            mul_le_mul_of_nonneg_left
              (mul_pow_dobrushinMatrixPow_le_tilted C distLink hμ hC_nonneg h_refl h_tri m e'' e')
              (dobrushinTiltedMatrix_nonneg C distLink ( by linarith ) hC_nonneg e e'')

/-- Georgii Theorem 8.20 distance-tail bound for `dobrushinComparisonSeries` without any
nearest-neighbor (`distLink ≤ 1`) assumption: if the exponentially tilted matrix
`dobrushinTiltedMatrix C distLink μ` (`1 ≤ μ`) has row sum bounded by `q_tilde < 1`, then for any
target set `S : Finset (Link L)` separated from `e` by `∀ e' ∈ S, t ≤ distLink e e'`,
$\sum_{e' \in S} D_{e, e'}(C) \le (\mu^{-1})^t / (1 - q_{\mathrm{tilde}})$. -/
theorem sum_dobrushinComparisonSeries_le_of_tilted_rowSum {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) (distLink : Link L → Link L → ℕ)
    {μ q_tilde : ℝ} (hμ : 1 ≤ μ) (hq : 0 ≤ q_tilde) (hq_lt : q_tilde < 1)
    (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e')
    (h_refl : ∀ e : Link L, distLink e e = 0)
    (h_tri : ∀ e e'' e' : Link L, distLink e e' ≤ distLink e e'' + distLink e'' e')
    (h_tilted_row : ∀ e : Link L,
      (∑ e' : Link L, dobrushinTiltedMatrix C distLink μ e e') ≤ q_tilde)
    (e : Link L) (S : Finset (Link L)) (t : ℕ)
    (h_sep : ∀ e' ∈ S, t ≤ distLink e e') :
    (∑ e' ∈ S, dobrushinComparisonSeries C e e') ≤ (μ⁻¹) ^ t / (1 - q_tilde) := by
  have hμ_pos : 0 < μ := by linarith
  have hμt_pos : 0 < μ ^ t := pow_pos hμ_pos t
  let C_tilt := dobrushinTiltedMatrix C distLink μ
  have hCt_nonneg : ∀ e₁ e₂ : Link L, 0 ≤ C_tilt e₁ e₂ :=
    dobrushinTiltedMatrix_nonneg C distLink hμ_pos.le hC_nonneg
  have h_entry (e' : Link L) (he' : e' ∈ S) :
      μ ^ t * dobrushinComparisonSeries C e e' ≤ dobrushinComparisonSeries C_tilt e e' := by
    have h_pow_t : μ ^ t ≤ μ ^ (distLink e e') := pow_le_pow_right₀ hμ (h_sep e' he')
    have hD_nonneg : 0 ≤ dobrushinComparisonSeries C e e' :=
      dobrushinComparisonSeries_nonneg C hC_nonneg e e'
    have h_sum_Ct : Summable (fun m : ℕ => dobrushinMatrixPow C_tilt m e e') :=
      summable_dobrushinMatrixPow_of_rowSum_lt_one C_tilt hq hq_lt hCt_nonneg h_tilted_row e e'
    have h_step (m : ℕ) :
        μ ^ (distLink e e') * dobrushinMatrixPow C m e e' ≤ dobrushinMatrixPow C_tilt m e e' :=
      mul_pow_dobrushinMatrixPow_le_tilted C distLink hμ hC_nonneg h_refl h_tri m e e'
    have h_sum_C : Summable (fun m : ℕ => μ ^ (distLink e e') * dobrushinMatrixPow C m e e') :=
      Summable.of_nonneg_of_le
        (fun m => mul_nonneg (pow_nonneg hμ_pos.le _) (dobrushinMatrixPow_nonneg C hC_nonneg m e e'))
        h_step h_sum_Ct
    calc
      μ ^ t * dobrushinComparisonSeries C e e'
        ≤ μ ^ (distLink e e') * dobrushinComparisonSeries C e e' :=
          mul_le_mul_of_nonneg_right h_pow_t hD_nonneg
      _ = ∑' m : ℕ, (μ ^ (distLink e e') * dobrushinMatrixPow C m e e') := by
          unfold dobrushinComparisonSeries
          exact tsum_mul_left.symm
      _ ≤ ∑' m : ℕ, dobrushinMatrixPow C_tilt m e e' :=
          Summable.tsum_le_tsum h_step h_sum_C h_sum_Ct
      _ = dobrushinComparisonSeries C_tilt e e' := rfl
  have h_mul_sum :
      μ ^ t * (∑ e' ∈ S, dobrushinComparisonSeries C e e') ≤ 1 / (1 - q_tilde) := by
    calc
      μ ^ t * (∑ e' ∈ S, dobrushinComparisonSeries C e e')
        = ∑ e' ∈ S, μ ^ t * dobrushinComparisonSeries C e e' := Finset.mul_sum _ _ _
      _ ≤ ∑ e' ∈ S, dobrushinComparisonSeries C_tilt e e' := Finset.sum_le_sum h_entry
      _ ≤ ∑ e' : Link L, dobrushinComparisonSeries C_tilt e e' :=
          Finset.sum_le_univ_sum_of_nonneg fun e' =>
            dobrushinComparisonSeries_nonneg C_tilt hCt_nonneg e e'
      _ ≤ 1 / (1 - q_tilde) :=
          sum_dobrushinComparisonSeries_le_inv_sub C_tilt hq hq_lt hCt_nonneg h_tilted_row e
  calc
    (∑ e' ∈ S, dobrushinComparisonSeries C e e')
      = (μ ^ t)⁻¹ * (μ ^ t * (∑ e' ∈ S, dobrushinComparisonSeries C e e')) := by
        rw [inv_mul_cancel_left₀ hμt_pos.ne']
    _ ≤ (μ ^ t)⁻¹ * (1 / (1 - q_tilde)) :=
        mul_le_mul_of_nonneg_left h_mul_sum (inv_nonneg.mpr hμt_pos.le)
    _ = (μ⁻¹) ^ t / (1 - q_tilde) := by
        rw [inv_pow]
        ring

/-- Georgii Theorem 8.20 observable comparison decay for nonlocal Dobrushin matrices:
whenever `dobrushinTiltedMatrix C distLink μ` (`1 ≤ μ`) has row sum `≤ q_tilde < 1` and `supp_f`,
`supp_g` are separated by `∀ e ∈ supp_f, ∀ e' ∈ supp_g, t ≤ distLink e e'`,
`dobrushinObservableComparison G C f g ≤ (∑ e ∈ supp_f, linkOscillation G L f e) * M_g * ((μ⁻¹) ^ t / (1 - q_tilde))`. -/
theorem dobrushinObservableComparison_le_of_tilted_rowSum
    (G : Type*) {L : ℕ} [NeZero L]
    (C : Link L → Link L → ℝ) (distLink : Link L → Link L → ℕ)
    {μ q_tilde M_g : ℝ} (hμ : 1 ≤ μ) (hq : 0 ≤ q_tilde) (hq_lt : q_tilde < 1) (hMg : 0 ≤ M_g)
    (hC_nonneg : ∀ e e' : Link L, 0 ≤ C e e')
    (h_refl : ∀ e : Link L, distLink e e = 0)
    (h_tri : ∀ e e'' e' : Link L, distLink e e' ≤ distLink e e'' + distLink e'' e')
    (h_tilted_row : ∀ e : Link L,
      (∑ e' : Link L, dobrushinTiltedMatrix C distLink μ e e') ≤ q_tilde)
    (f g : GroupGaugeConfig G L → ℝ)
    (supp_f supp_g : Finset (Link L)) (t : ℕ)
    (hf_supp : ∀ e : Link L, e ∉ supp_f → linkOscillation G L f e = 0)
    (hg_supp : ∀ e' : Link L, e' ∉ supp_g → linkOscillation G L g e' = 0)
    (hg_bdd : ∀ e' ∈ supp_g, linkOscillation G L g e' ≤ M_g)
    (h_sep : ∀ e ∈ supp_f, ∀ e' ∈ supp_g, t ≤ distLink e e') :
    dobrushinObservableComparison G C f g ≤
      (∑ e ∈ supp_f, linkOscillation G L f e) * M_g * ((μ⁻¹) ^ t / (1 - q_tilde)) := by
  unfold dobrushinObservableComparison
  have h_outer :
      (∑ e : Link L, ∑ e' : Link L,
        linkOscillation G L f e * dobrushinComparisonSeries C e e' * linkOscillation G L g e') =
      ∑ e ∈ supp_f, ∑ e' ∈ supp_g,
        linkOscillation G L f e * dobrushinComparisonSeries C e e' * linkOscillation G L g e' := by
    rw [← Finset.sum_subset (Finset.subset_univ supp_f)]
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Finset.sum_subset (Finset.subset_univ supp_g)]
      intro e' _ he'
      rw [hg_supp e' he', mul_zero]
    · intro e _ he
      refine Finset.sum_eq_zero fun e' _ => ?_
      rw [hf_supp e he, zero_mul, zero_mul]
  rw [h_outer]
  have h_inner (e : Link L) (he : e ∈ supp_f) :
      (∑ e' ∈ supp_g,
        linkOscillation G L f e * dobrushinComparisonSeries C e e' * linkOscillation G L g e') ≤
      linkOscillation G L f e * M_g * ((μ⁻¹) ^ t / (1 - q_tilde)) := by
    have hf_nonneg : 0 ≤ linkOscillation G L f e := linkOscillation_nonneg G L f e
    have h_series :=
      sum_dobrushinComparisonSeries_le_of_tilted_rowSum C distLink hμ hq hq_lt
        hC_nonneg h_refl h_tri h_tilted_row e supp_g t (h_sep e he)
    calc
      (∑ e' ∈ supp_g,
        linkOscillation G L f e * dobrushinComparisonSeries C e e' * linkOscillation G L g e')
        ≤ ∑ e' ∈ supp_g,
            linkOscillation G L f e * M_g * dobrushinComparisonSeries C e e' := by
          refine Finset.sum_le_sum fun e' he' => ?_
          have hD_nonneg := dobrushinComparisonSeries_nonneg C hC_nonneg e e'
          calc
            linkOscillation G L f e * dobrushinComparisonSeries C e e' * linkOscillation G L g e'
              ≤ linkOscillation G L f e * dobrushinComparisonSeries C e e' * M_g :=
                mul_le_mul_of_nonneg_left (hg_bdd e' he') (mul_nonneg hf_nonneg hD_nonneg)
            _ = linkOscillation G L f e * M_g * dobrushinComparisonSeries C e e' := by ring
      _ = linkOscillation G L f e * M_g * (∑ e' ∈ supp_g, dobrushinComparisonSeries C e e') := by
          rw [← Finset.mul_sum]
      _ ≤ linkOscillation G L f e * M_g * ((μ⁻¹) ^ t / (1 - q_tilde)) :=
          mul_le_mul_of_nonneg_left h_series (mul_nonneg hf_nonneg hMg)
  calc
    (∑ e ∈ supp_f, ∑ e' ∈ supp_g,
      linkOscillation G L f e * dobrushinComparisonSeries C e e' * linkOscillation G L g e')
      ≤ ∑ e ∈ supp_f, linkOscillation G L f e * M_g * ((μ⁻¹) ^ t / (1 - q_tilde)) :=
        Finset.sum_le_sum h_inner
    _ = (∑ e ∈ supp_f, linkOscillation G L f e) * M_g * ((μ⁻¹) ^ t / (1 - q_tilde)) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]

/-- Tilted Dobrushin interdependence row-sum bound from two-link action mixed differences
(Georgii Theorem 8.20 entrywise input): if at link `e : Link L` the two-link mixed differences of
`S_act` are bounded by `Δ e' ≥ 0` with `∑ e' ∈ Finset.univ.erase e, Δ e' ≤ M`, `4 * M < 1`, and
`∑ e' ∈ Finset.univ.erase e, μ ^ (distLink e e') * Δ e' ≤ M_tilde` for `0 ≤ μ`, then
`∑ e' : Link L, dobrushinTiltedMatrix (dobrushinSupMatrix G L S_act) distLink μ e e' ≤ 4 * M_tilde`. -/
theorem dobrushinTiltedMatrix_rowSum_le_four_mul_of_twoLink_sum
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ)
    (distLink : Link L → Link L → ℕ) {μ M M_tilde : ℝ} (hμ : 0 ≤ μ)
    (e : Link L) (Δ : Link L → ℝ)
    (hS_meas : ∀ (W : GroupGaugeConfig G L),
      Measurable (fun g : G => S_act (updateGroupGaugeLink L W e.x e.μ g)))
    (hS_bdd : ∀ (W : GroupGaugeConfig G L), ∃ B : ℝ, ∀ g : G,
      |S_act (updateGroupGaugeLink L W e.x e.μ g)| ≤ B)
    (hΔ_nonneg : ∀ e' ∈ Finset.univ.erase e, 0 ≤ Δ e')
    (h_mixed : ∀ e' ∈ Finset.univ.erase e, ∀ (V : GroupGaugeConfig G L) (g h1 h2 : G),
      |groupTwoLinkMixedDifference L S_act V e.x e.μ g 1 e'.x e'.μ h1 h2| ≤ Δ e')
    (h_sum_le : (∑ e' ∈ Finset.univ.erase e, Δ e') ≤ M)
    (hM_lt : 4 * M < 1)
    (h_tilted_le : (∑ e' ∈ Finset.univ.erase e, μ ^ (distLink e e') * Δ e') ≤ M_tilde) :
    (∑ e' : Link L,
      dobrushinTiltedMatrix (dobrushinSupMatrix G L S_act) distLink μ e e') ≤ 4 * M_tilde := by
  have h_entry :=
    (dobrushinSupMatrix_rowSum_le_four_mul_of_twoLink_sum G S_act e Δ
      hS_meas hS_bdd hΔ_nonneg h_mixed h_sum_le hM_lt).1
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Link L)) _ (Finset.mem_univ e)]
  have h_diag :
      dobrushinTiltedMatrix (dobrushinSupMatrix G L S_act) distLink μ e e = 0 := by
    simp [dobrushinTiltedMatrix, dobrushinSupMatrix_diag]
  rw [h_diag, add_zero]
  calc
    (∑ e' ∈ Finset.univ.erase e,
      dobrushinTiltedMatrix (dobrushinSupMatrix G L S_act) distLink μ e e')
      ≤ ∑ e' ∈ Finset.univ.erase e, (4 * (μ ^ (distLink e e') * Δ e')) := by
        refine Finset.sum_le_sum fun e' he' => ?_
        unfold dobrushinTiltedMatrix
        calc
          μ ^ (distLink e e') * dobrushinSupMatrix G L S_act e e'
            ≤ μ ^ (distLink e e') * (4 * Δ e') :=
              mul_le_mul_of_nonneg_left (h_entry e' he').2 (pow_nonneg hμ _)
          _ = 4 * (μ ^ (distLink e e') * Δ e') := by ring
    _ = 4 * ∑ e' ∈ Finset.univ.erase e, μ ^ (distLink e e') * Δ e' := by
        rw [← Finset.mul_sum]
    _ ≤ 4 * M_tilde := mul_le_mul_of_nonneg_left h_tilted_le (by norm_num)

/-! ### Quantitative RG Step R5 & h_R_mixed Neighbor-vs-Exponential-Tail Interface -/

/-- Exact subtraction linearity of `groupTwoLinkMixedDifference` with respect to the action argument:
for any two actions `S₁, S₂ : GroupGaugeConfig G L → ℝ`, the two-link mixed second difference of
`fun U => S₁ U - S₂ U` equals the difference of their two-link mixed second differences. -/
theorem groupTwoLinkMixedDifference_sub {G : Type*} (L : ℕ)
    (S₁ S₂ : GroupGaugeConfig G L → ℝ)
    (V : GroupGaugeConfig G L)
    (x : Lattice4D L) (μ : Fin 4) (g₁ g₂ : G)
    (y : Lattice4D L) (ν : Fin 4) (h₁ h₂ : G) :
    groupTwoLinkMixedDifference L (fun U => S₁ U - S₂ U) V x μ g₁ g₂ y ν h₁ h₂ =
      groupTwoLinkMixedDifference L S₁ V x μ g₁ g₂ y ν h₁ h₂ -
        groupTwoLinkMixedDifference L S₂ V x μ g₁ g₂ y ν h₁ h₂ := by
  dsimp [groupTwoLinkMixedDifference]
  ring

/-- Three-term decomposition and triangle-inequality bound for `groupTwoLinkMixedDifference` on the
truncated RG remainder `S_trunc(U) = A_norm(U) - S_wilson(U) - S_poly(U)`:
1. Exact linearity:
   `groupTwoLinkMixedDifference L (fun U => A_norm U - S_wilson U - S_poly U) ... = Δ²A_norm - Δ²S_wilson - Δ²S_poly`,
2. Triangle-inequality bound:
   `|groupTwoLinkMixedDifference L (fun U => A_norm U - S_wilson U - S_poly U) ...| ≤ |Δ²A_norm| + |Δ²S_wilson| + |Δ²S_poly|`, and
3. Off-neighbor reduction: whenever `Δ²S_wilson = 0` (such as for any partner link outside `dobrushinNeighbors ⟨x, μ⟩`),
   `|groupTwoLinkMixedDifference L (fun U => A_norm U - S_wilson U - S_poly U) ...| ≤ |Δ²A_norm| + |Δ²S_poly|`. -/
theorem abs_groupTwoLinkMixedDifference_sub_le {G : Type*} (L : ℕ)
    (A_norm S_wilson S_poly : GroupGaugeConfig G L → ℝ)
    (V : GroupGaugeConfig G L)
    (x : Lattice4D L) (μ : Fin 4) (g₁ g₂ : G)
    (y : Lattice4D L) (ν : Fin 4) (h₁ h₂ : G) :
    groupTwoLinkMixedDifference L (fun U => A_norm U - S_wilson U - S_poly U)
        V x μ g₁ g₂ y ν h₁ h₂ =
      groupTwoLinkMixedDifference L A_norm V x μ g₁ g₂ y ν h₁ h₂ -
        groupTwoLinkMixedDifference L S_wilson V x μ g₁ g₂ y ν h₁ h₂ -
        groupTwoLinkMixedDifference L S_poly V x μ g₁ g₂ y ν h₁ h₂ ∧
    |groupTwoLinkMixedDifference L (fun U => A_norm U - S_wilson U - S_poly U)
        V x μ g₁ g₂ y ν h₁ h₂| ≤
      |groupTwoLinkMixedDifference L A_norm V x μ g₁ g₂ y ν h₁ h₂| +
        |groupTwoLinkMixedDifference L S_wilson V x μ g₁ g₂ y ν h₁ h₂| +
        |groupTwoLinkMixedDifference L S_poly V x μ g₁ g₂ y ν h₁ h₂| ∧
    (groupTwoLinkMixedDifference L S_wilson V x μ g₁ g₂ y ν h₁ h₂ = 0 →
      |groupTwoLinkMixedDifference L (fun U => A_norm U - S_wilson U - S_poly U)
          V x μ g₁ g₂ y ν h₁ h₂| ≤
        |groupTwoLinkMixedDifference L A_norm V x μ g₁ g₂ y ν h₁ h₂| +
          |groupTwoLinkMixedDifference L S_poly V x μ g₁ g₂ y ν h₁ h₂|) := by
  have h_decomp :
      groupTwoLinkMixedDifference L (fun U => A_norm U - S_wilson U - S_poly U)
          V x μ g₁ g₂ y ν h₁ h₂ =
        groupTwoLinkMixedDifference L A_norm V x μ g₁ g₂ y ν h₁ h₂ -
          groupTwoLinkMixedDifference L S_wilson V x μ g₁ g₂ y ν h₁ h₂ -
          groupTwoLinkMixedDifference L S_poly V x μ g₁ g₂ y ν h₁ h₂ := by
    dsimp [groupTwoLinkMixedDifference]
    ring
  have h_tri1 :
      |groupTwoLinkMixedDifference L A_norm V x μ g₁ g₂ y ν h₁ h₂ -
          groupTwoLinkMixedDifference L S_wilson V x μ g₁ g₂ y ν h₁ h₂ -
          groupTwoLinkMixedDifference L S_poly V x μ g₁ g₂ y ν h₁ h₂| ≤
        |groupTwoLinkMixedDifference L A_norm V x μ g₁ g₂ y ν h₁ h₂ -
          groupTwoLinkMixedDifference L S_wilson V x μ g₁ g₂ y ν h₁ h₂| +
          |groupTwoLinkMixedDifference L S_poly V x μ g₁ g₂ y ν h₁ h₂| :=
    abs_sub _ _
  have h_tri2 :
      |groupTwoLinkMixedDifference L A_norm V x μ g₁ g₂ y ν h₁ h₂ -
          groupTwoLinkMixedDifference L S_wilson V x μ g₁ g₂ y ν h₁ h₂| ≤
        |groupTwoLinkMixedDifference L A_norm V x μ g₁ g₂ y ν h₁ h₂| +
          |groupTwoLinkMixedDifference L S_wilson V x μ g₁ g₂ y ν h₁ h₂| :=
    abs_sub _ _
  refine ⟨h_decomp, ?_, ?_⟩
  · rw [h_decomp]
    linarith
  · intro hW
    rw [h_decomp, hW, sub_zero]
    exact abs_sub _ _

/-- Exact partition of the exponentially tilted two-link mixed-difference sum
`∑ e' ∈ Finset.univ.erase e, μ ^ (distLink e e') * Δ e'` across any finite local link neighborhood
`N_e : Finset (Link L)` (such as `dobrushinNeighbors e`) and its off-neighbor complement
`(Finset.univ.erase e) \ N_e`, together with non-negativity of both pieces whenever `0 ≤ μ` and
`∀ e' ∈ Finset.univ.erase e, 0 ≤ Δ e'`. -/
theorem twoLinkMixedDifference_split_neighbors_and_complement
    {L : ℕ} [NeZero L] (distLink : Link L → Link L → ℕ) (μ : ℝ)
    (e : Link L) (N_e : Finset (Link L)) (Δ : Link L → ℝ) :
    (∑ e' ∈ Finset.univ.erase e, μ ^ (distLink e e') * Δ e') =
      (∑ e' ∈ (Finset.univ.erase e) ∩ N_e, μ ^ (distLink e e') * Δ e') +
        (∑ e' ∈ (Finset.univ.erase e) \ N_e, μ ^ (distLink e e') * Δ e') ∧
    (0 ≤ μ → (∀ e' ∈ Finset.univ.erase e, 0 ≤ Δ e') →
      0 ≤ (∑ e' ∈ (Finset.univ.erase e) ∩ N_e, μ ^ (distLink e e') * Δ e') ∧
      0 ≤ (∑ e' ∈ (Finset.univ.erase e) \ N_e, μ ^ (distLink e e') * Δ e')) := by
  have h_disj : Disjoint ((Finset.univ.erase e) ∩ N_e) ((Finset.univ.erase e) \ N_e) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx2).2 (Finset.mem_inter.mp hx1).2
  have h_union : ((Finset.univ.erase e) ∩ N_e) ∪ ((Finset.univ.erase e) \ N_e) = Finset.univ.erase e := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  refine ⟨by rw [← Finset.sum_union h_disj, h_union], ?_⟩
  intro hμ hΔ
  refine ⟨Finset.sum_nonneg fun e' he' =>
      mul_nonneg (pow_nonneg hμ _) (hΔ e' (Finset.mem_inter.mp he').1),
    Finset.sum_nonneg fun e' he' =>
      mul_nonneg (pow_nonneg hμ _) (hΔ e' (Finset.mem_sdiff.mp he').1)⟩

/-- Tilted Dobrushin interdependence row-sum bound from a local neighbor (`N_e`) plus off-neighbor
(`(Finset.univ.erase e) \ N_e`) two-link mixed-difference split: if the unweighted local and
off-neighbor sums are bounded by `M_loc` and `M_tail` with `4 * (M_loc + M_tail) < 1`, and the
`μ`-tilted local and off-neighbor sums are bounded by `M_loc_tilde` and `M_tail_tilde`, then
`∑ e' : Link L, dobrushinSupMatrix G L S_act e e' ≤ 4 * (M_loc + M_tail) < 1` and
`∑ e' : Link L, dobrushinTiltedMatrix (dobrushinSupMatrix G L S_act) distLink μ e e' ≤ 4 * (M_loc_tilde + M_tail_tilde)`.

This connects the exact neighbor truncation `h_R_mixed` (`M_tail = 0`, `M_tail_tilde = 0` on
`N_e = dobrushinNeighbors e`) to a weak-coupling polymer / tree-graph interface where off-neighbor
two-link mixed differences decay exponentially (`M_tail_tilde > 0`). Proving the quantitative
smallness of `M_loc_tilde + M_tail_tilde` for the actual Haar-blocked Wilson measure remains an
open research obligation (`R5`). -/
theorem dobrushinTiltedMatrix_rowSum_le_of_neighbor_and_offNeighbor_tail
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {L : ℕ} [NeZero L] (S_act : GroupGaugeConfig G L → ℝ)
    (distLink : Link L → Link L → ℕ)
    {μ M_loc M_tail M_loc_tilde M_tail_tilde : ℝ} (hμ : 0 ≤ μ)
    (e : Link L) (N_e : Finset (Link L)) (Δ : Link L → ℝ)
    (hS_meas : ∀ (W : GroupGaugeConfig G L),
      Measurable (fun g : G => S_act (updateGroupGaugeLink L W e.x e.μ g)))
    (hS_bdd : ∀ (W : GroupGaugeConfig G L), ∃ B : ℝ, ∀ g : G,
      |S_act (updateGroupGaugeLink L W e.x e.μ g)| ≤ B)
    (hΔ_nonneg : ∀ e' ∈ Finset.univ.erase e, 0 ≤ Δ e')
    (h_mixed : ∀ e' ∈ Finset.univ.erase e, ∀ (V : GroupGaugeConfig G L) (g h1 h2 : G),
      |groupTwoLinkMixedDifference L S_act V e.x e.μ g 1 e'.x e'.μ h1 h2| ≤ Δ e')
    (h_loc_le : (∑ e' ∈ (Finset.univ.erase e) ∩ N_e, Δ e') ≤ M_loc)
    (h_tail_le : (∑ e' ∈ (Finset.univ.erase e) \ N_e, Δ e') ≤ M_tail)
    (hM_lt : 4 * (M_loc + M_tail) < 1)
    (h_tilted_loc_le :
      (∑ e' ∈ (Finset.univ.erase e) ∩ N_e, μ ^ (distLink e e') * Δ e') ≤ M_loc_tilde)
    (h_tilted_tail_le :
      (∑ e' ∈ (Finset.univ.erase e) \ N_e, μ ^ (distLink e e') * Δ e') ≤ M_tail_tilde) :
    (∑ e' ∈ Finset.univ.erase e, Δ e') ≤ M_loc + M_tail ∧
    (∑ e' ∈ Finset.univ.erase e, μ ^ (distLink e e') * Δ e') ≤
      M_loc_tilde + M_tail_tilde ∧
    (∑ e' : Link L, dobrushinSupMatrix G L S_act e e') ≤ 4 * (M_loc + M_tail) ∧
    (∑ e' : Link L, dobrushinSupMatrix G L S_act e e') < 1 ∧
    (∑ e' : Link L,
      dobrushinTiltedMatrix (dobrushinSupMatrix G L S_act) distLink μ e e') ≤
      4 * (M_loc_tilde + M_tail_tilde) ∧
    (4 * (M_loc_tilde + M_tail_tilde) < 1 →
      (∑ e' : Link L,
        dobrushinTiltedMatrix (dobrushinSupMatrix G L S_act) distLink μ e e') < 1 ∧
      0 < 1 - 4 * (M_loc_tilde + M_tail_tilde)) := by
  have h_unweighted_split :
      (∑ e' ∈ Finset.univ.erase e, Δ e') =
        (∑ e' ∈ (Finset.univ.erase e) ∩ N_e, Δ e') +
          (∑ e' ∈ (Finset.univ.erase e) \ N_e, Δ e') := by
    simpa using (twoLinkMixedDifference_split_neighbors_and_complement distLink 1 e N_e Δ).1
  have h_sum_le : (∑ e' ∈ Finset.univ.erase e, Δ e') ≤ M_loc + M_tail := by
    rw [h_unweighted_split]
    exact add_le_add h_loc_le h_tail_le
  have h_tilted_split :=
    (twoLinkMixedDifference_split_neighbors_and_complement distLink μ e N_e Δ).1
  have h_tilted_le :
      (∑ e' ∈ Finset.univ.erase e, μ ^ (distLink e e') * Δ e') ≤
        M_loc_tilde + M_tail_tilde := by
    rw [h_tilted_split]
    exact add_le_add h_tilted_loc_le h_tilted_tail_le
  have h_untilt :=
    dobrushinSupMatrix_rowSum_le_four_mul_of_twoLink_sum G S_act e Δ
      hS_meas hS_bdd hΔ_nonneg h_mixed h_sum_le hM_lt
  have h_tilt :=
    dobrushinTiltedMatrix_rowSum_le_four_mul_of_twoLink_sum G S_act distLink hμ e Δ
      hS_meas hS_bdd hΔ_nonneg h_mixed h_sum_le hM_lt h_tilted_le
  refine ⟨h_sum_le, h_tilted_le, h_untilt.2.2.1, h_untilt.2.2.2, h_tilt, ?_⟩
  intro h_tilt_lt
  exact ⟨lt_of_le_of_lt h_tilt h_tilt_lt, sub_pos.mpr h_tilt_lt⟩

/-- Single-step RG propagation of an effective remainder oscillation defect `δ_rem ≥ 0` and an
off-neighbor two-link mixed-difference tail defect `δ_mix ≥ 0`:
for any effective action decomposition `A_eff V = S_lead V + R_rem V` on `GroupGaugeConfig G L`,
if at link `e : Link L` the leading action has single-link oscillation bounded by `osc_lead ≥ 0`
and the remainder has single-link oscillation bounded by `δ_rem ≥ 0`, while the local and
off-neighbor mixed-difference sums `M_loc ≥ 0` and `δ_mix ≥ 0` satisfy `4 * (M_loc + δ_mix) < 1`,
then:
1. The single-link oscillation of `A_eff` at `e` is bounded by `osc_lead + δ_rem ≥ 0`,
2. The combined Dobrushin row-sum rate `4 * (M_loc + δ_mix)` lies in `[0, 1)`, and
3. The Dobrushin contraction margin satisfies `1 - 4 * (M_loc + δ_mix) = (1 - 4 * M_loc) - 4 * δ_mix > 0`
   with strictly positive Neumann-series inverse `(1 - 4 * (M_loc + δ_mix))⁻¹ > 0`. -/
theorem rgStep_runningCoupling_contraction_margin_of_tail_defect
    {G : Type*} {L : ℕ}
    (A_eff S_lead R_rem : GroupGaugeConfig G L → ℝ)
    (V : GroupGaugeConfig G L) (e : Link L) (g₁ g₂ : G)
    {osc_lead δ_rem M_loc δ_mix : ℝ}
    (h_osc_lead_nonneg : 0 ≤ osc_lead) (hδ_rem_nonneg : 0 ≤ δ_rem)
    (hM_loc_nonneg : 0 ≤ M_loc) (hδ_mix_nonneg : 0 ≤ δ_mix)
    (h_decomp : ∀ U : GroupGaugeConfig G L, A_eff U = S_lead U + R_rem U)
    (h_lead_osc :
      |S_lead (updateGroupGaugeLink L V e.x e.μ g₁) -
        S_lead (updateGroupGaugeLink L V e.x e.μ g₂)| ≤ osc_lead)
    (h_rem_osc :
      |R_rem (updateGroupGaugeLink L V e.x e.μ g₁) -
        R_rem (updateGroupGaugeLink L V e.x e.μ g₂)| ≤ δ_rem)
    (h_contract : 4 * (M_loc + δ_mix) < 1) :
    |A_eff (updateGroupGaugeLink L V e.x e.μ g₁) -
      A_eff (updateGroupGaugeLink L V e.x e.μ g₂)| ≤ osc_lead + δ_rem ∧
    0 ≤ osc_lead + δ_rem ∧
    0 ≤ 4 * (M_loc + δ_mix) ∧
    4 * (M_loc + δ_mix) < 1 ∧
    0 < 1 - 4 * (M_loc + δ_mix) ∧
    1 - 4 * (M_loc + δ_mix) = (1 - 4 * M_loc) - 4 * δ_mix ∧
    0 < (1 - 4 * (M_loc + δ_mix))⁻¹ := by
  have h_diff :
      A_eff (updateGroupGaugeLink L V e.x e.μ g₁) -
        A_eff (updateGroupGaugeLink L V e.x e.μ g₂) =
      (S_lead (updateGroupGaugeLink L V e.x e.μ g₁) -
        S_lead (updateGroupGaugeLink L V e.x e.μ g₂)) +
      (R_rem (updateGroupGaugeLink L V e.x e.μ g₁) -
        R_rem (updateGroupGaugeLink L V e.x e.μ g₂)) := by
    rw [h_decomp, h_decomp]
    ring
  have h_tri := abs_add_le
    (S_lead (updateGroupGaugeLink L V e.x e.μ g₁) -
      S_lead (updateGroupGaugeLink L V e.x e.μ g₂))
    (R_rem (updateGroupGaugeLink L V e.x e.μ g₁) -
      R_rem (updateGroupGaugeLink L V e.x e.μ g₂))
  rw [← h_diff] at h_tri
  have h_osc :
      |A_eff (updateGroupGaugeLink L V e.x e.μ g₁) -
        A_eff (updateGroupGaugeLink L V e.x e.μ g₂)| ≤ osc_lead + δ_rem := by
    linarith
  refine ⟨h_osc, by linarith, by linarith, h_contract, by linarith, by ring,
    inv_pos.mpr (by linarith)⟩

/-- Multi-scale RG remainder influence ceiling and 1-loop/2-loop running coupling drift envelope
(Pack 1 interface for `YangMillsRGBridgeObstruction`):
1. Whenever the per-scale blocking contraction factor satisfies `0 ≤ θ_block < 1` and the single-step
   remainder generation bound satisfies `0 ≤ ε_gen ≤ (1 / 768) * (1 - θ_block)`, the asymptotic
   geometric ceiling `ε_gen / (1 - θ_block)` is non-negative and bounded by `1 / 768`; and
2. For any `K`-step running coupling sequence `β : ℕ → ℝ` satisfying the 1-loop + 2-loop drift bounds
   `|β (k + 1) - (β k - Δβ_1loop)| ≤ δ_2loop k` across `k < K`, the cumulative `K`-step coupling
   drift from the pure 1-loop trajectory `β 0 - K * Δβ_1loop` is bounded by `∑ k ∈ Finset.range K, δ_2loop k`. -/
theorem rgMultiScale_influenceCeiling_and_runningCoupling_drift_envelope
    {θ_block ε_gen Δβ_1loop : ℝ}
    (_hθ0 : 0 ≤ θ_block) (hθ1 : θ_block < 1)
    (hε0 : 0 ≤ ε_gen) (hε_le : ε_gen ≤ (1 / 768 : ℝ) * (1 - θ_block))
    (β δ_2loop : ℕ → ℝ) (K : ℕ)
    (h_drift : ∀ k ∈ Finset.range K, |β (k + 1) - (β k - Δβ_1loop)| ≤ δ_2loop k) :
    0 ≤ ε_gen / (1 - θ_block) ∧
    ε_gen / (1 - θ_block) ≤ 1 / 768 ∧
    |β K - (β 0 - (K : ℝ) * Δβ_1loop)| ≤ ∑ k ∈ Finset.range K, δ_2loop k := by
  have h_den : 0 < 1 - θ_block := by linarith
  have h_ceil_nonneg : 0 ≤ ε_gen / (1 - θ_block) := div_nonneg hε0 h_den.le
  have h_ceil_le : ε_gen / (1 - θ_block) ≤ 1 / 768 := by
    rw [div_le_iff₀ h_den]
    exact hε_le
  have h_tel : ∀ n : ℕ,
      β n - (β 0 - (n : ℝ) * Δβ_1loop) =
        ∑ k ∈ Finset.range n, (β (k + 1) - (β k - Δβ_1loop)) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      push_cast
      ring
  have h_drift_sum :
      |β K - (β 0 - (K : ℝ) * Δβ_1loop)| ≤ ∑ k ∈ Finset.range K, δ_2loop k := by
    rw [h_tel K]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h_drift)
  exact ⟨h_ceil_nonneg, h_ceil_le, h_drift_sum⟩

/-- Unconditional general-compact-group Wilson Gibbs probability, finite-range Dobrushin locality,
volume-uniform row-sum contraction, and Föllmer–Dobrushin covariance comparison theorem
(`generalCompactGroup_wilsonGibbsMeasure_dobrushin_rowSum_and_covariance_comparison`):
for **every** compact Hausdorff second-countable topological group `G`, class trace
`tr : CompactGaugeClassTrace G`, torus size `L : ℕ [NeZero L]`, and coupling `0 ≤ β` satisfying the
strong-coupling Dobrushin condition `4 * (18 * (24 * β)) < 1`:
1. `0 < groupGibbsPartition G L (groupWilsonAction tr β)` and
   `IsProbabilityMeasure (groupGibbsMeasure G L (groupWilsonAction tr β))`,
2. For every link `e : Link L`, `dobrushinSupMatrix G L (groupWilsonAction tr β) e e = 0`,
   `∀ e' ∉ dobrushinNeighbors e, dobrushinSupMatrix G L (groupWilsonAction tr β) e e' = 0`, and
   `(∑ e' : Link L, dobrushinSupMatrix G L (groupWilsonAction tr β) e e') ≤ 4 * (18 * (24 * β)) < 1`
   uniformly in `L` and `G`, and
3. For every pair of measurable bounded observables `f, g : GroupGaugeConfig G L → ℝ`
   (`|f V| ≤ M_f`, `|g V| ≤ M_g`),
   `|groupGibbsCov (groupGibbsMeasure G L (groupWilsonAction tr β)) f g| ≤
    dobrushinObservableComparison G (dobrushinSupMatrix G L (groupWilsonAction tr β)) f g`. -/
theorem generalCompactGroup_wilsonGibbsMeasure_dobrushin_rowSum_and_covariance_comparison
    (G : Type*) [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (tr : CompactGaugeClassTrace G) {L : ℕ} [NeZero L] {β : ℝ}
    (hβ : 0 ≤ β) (h_dob : 4 * (18 * (24 * β)) < 1) :
    0 < groupGibbsPartition G L (groupWilsonAction tr β) ∧
    IsProbabilityMeasure (groupGibbsMeasure G L (groupWilsonAction tr β)) ∧
    (∀ e : Link L,
      dobrushinSupMatrix G L (groupWilsonAction tr β) e e = 0 ∧
      (∀ e' : Link L, e' ∉ dobrushinNeighbors e →
        dobrushinSupMatrix G L (groupWilsonAction tr β) e e' = 0) ∧
      (∑ e' : Link L, dobrushinSupMatrix G L (groupWilsonAction tr β) e e') ≤
        4 * (18 * (24 * β)) ∧
      (∑ e' : Link L, dobrushinSupMatrix G L (groupWilsonAction tr β) e e') < 1) ∧
    (∀ (f g : GroupGaugeConfig G L → ℝ) {M_f M_g : ℝ},
      Measurable f → (∀ V : GroupGaugeConfig G L, |f V| ≤ M_f) →
      Measurable g → (∀ V : GroupGaugeConfig G L, |g V| ≤ M_g) →
      |groupGibbsCov (groupGibbsMeasure G L (groupWilsonAction tr β)) f g| ≤
        dobrushinObservableComparison G (dobrushinSupMatrix G L (groupWilsonAction tr β)) f g) := by
  have hS_meas : Measurable (groupWilsonAction (L := L) tr β) :=
    (continuous_groupWilsonAction tr β).measurable
  have h_prob_base := (groupWilsonMeasure_prob_bounds_and_localGauge_invariance G L tr hβ).1
  let B_act : ℝ := 12 * β * (L : ℝ) ^ 4
  have hS_bdd : ∀ V : GroupGaugeConfig G L, |groupWilsonAction tr β V| ≤ B_act := fun V => by
    have hV := h_prob_base V
    have hB_nonneg : 0 ≤ B_act := le_trans hV.1 hV.2.1
    exact abs_le.mpr ⟨by linarith [hV.1], hV.2.1⟩
  have h_part_pos : 0 < groupGibbsPartition G L (groupWilsonAction tr β) :=
    groupGibbsPartition_pos G (groupWilsonAction tr β) hS_meas hS_bdd
  have h_prob : IsProbabilityMeasure (groupGibbsMeasure G L (groupWilsonAction tr β)) :=
    groupGibbsMeasure_isProbabilityMeasure G (groupWilsonAction tr β) hS_meas hS_bdd
  have h_row_all (e : Link L) :
      dobrushinSupMatrix G L (groupWilsonAction tr β) e e = 0 ∧
      (∀ e' : Link L, e' ∉ dobrushinNeighbors e →
        dobrushinSupMatrix G L (groupWilsonAction tr β) e e' = 0) ∧
      (∑ e' : Link L, dobrushinSupMatrix G L (groupWilsonAction tr β) e e') ≤
        4 * (18 * (24 * β)) ∧
      (∑ e' : Link L, dobrushinSupMatrix G L (groupWilsonAction tr β) e e') < 1 := by
    have h_diag := dobrushinSupMatrix_diag G L (groupWilsonAction tr β) e
    have h_off : ∀ e' : Link L, e' ∉ dobrushinNeighbors e →
        dobrushinSupMatrix G L (groupWilsonAction tr β) e e' = 0 := by
      intro e' h_not_mem
      by_contra hne
      exact h_not_mem (dobrushinSupMatrix_groupWilsonAction_ne_zero_imp_dist_le_one G tr β hne).1
    let Δ : Link L → ℝ := fun e' => if e' ∈ dobrushinNeighbors e then 24 * β else 0
    have hΔ_nonneg : ∀ e' ∈ Finset.univ.erase e, 0 ≤ Δ e' := by
      intro e' _
      dsimp [Δ]
      split_ifs <;> linarith
    have h_mixed : ∀ e' ∈ Finset.univ.erase e, ∀ (V : GroupGaugeConfig G L) (g h1 h2 : G),
        |groupTwoLinkMixedDifference L (groupWilsonAction tr β) V e.x e.μ g 1 e'.x e'.μ h1 h2| ≤
          Δ e' := by
      intro e' he' V g h1 h2
      dsimp [Δ]
      split_ifs with h_mem
      · exact groupTwoLinkMixedDifference_groupWilsonAction_abs_le_twentyFour_mul_beta
          tr hβ V e e' g 1 h1 h2
      · rw [groupTwoLinkMixedDifference_groupWilsonAction_eq_zero_of_not_mem_dobrushinNeighbors
          tr β V e e' (Finset.mem_erase.mp he').1 h_mem g 1 h1 h2, abs_zero]
    have h_collapse :
        (∑ e' ∈ Finset.univ.erase e, Δ e') = ∑ _e' ∈ dobrushinNeighbors e, (24 * β) := by
      have h_sub : (∑ e' ∈ dobrushinNeighbors e, Δ e') = ∑ e' ∈ Finset.univ.erase e, Δ e' := by
        apply Finset.sum_subset
        · intro e' he'
          exact Finset.mem_erase.mpr
            ⟨fun h => not_mem_dobrushinNeighbors_self e (h ▸ he'), Finset.mem_univ e'⟩
        · intro e' _ hn
          dsimp [Δ]
          simp [hn]
      rw [← h_sub]
      refine Finset.sum_congr rfl fun e' he' => ?_
      dsimp [Δ]
      simp [he']
    have hcard : ((dobrushinNeighbors e).card : ℝ) ≤ 18 := by
      exact_mod_cast dobrushinNeighbors_card_le_eighteen e
    have h_sum_le : (∑ e' ∈ Finset.univ.erase e, Δ e') ≤ 18 * (24 * β) := by
      rw [h_collapse, Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard (by linarith)
    have h_sup := dobrushinSupMatrix_rowSum_le_four_mul_of_twoLink_sum
      G (groupWilsonAction tr β) e Δ
      (fun W => hS_meas.comp (measurable_updateGroupGaugeLink_right G W e.x e.μ))
      (fun W => ⟨B_act, fun g => hS_bdd _⟩)
      hΔ_nonneg h_mixed h_sum_le h_dob
    exact ⟨h_diag, h_off, h_sup.2.2.1, h_sup.2.2.2⟩
  refine ⟨h_part_pos, h_prob, h_row_all, ?_⟩
  intro f g M_f M_g hf_meas hf_bdd hg_meas hg_bdd
  exact groupGibbsMeasure_abs_cov_le_dobrushinObservableComparison
    G (groupWilsonAction tr β) (by linarith) h_dob (fun e => (h_row_all e).2.2.1)
    hS_meas hS_bdd f g hf_meas hf_bdd hg_meas hg_bdd

#assert_zfc_axioms

end JesseMath.Physics
