import Mathlib
import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.YangMillsHaar
import JesseMath.Physics.YangMillsBlockGeometry
import JesseMath.Physics.YangMillsWilsonMeasureBridge
import JesseMath.Physics.YangMillsPrivateEdgeHaar

/-!
# Private-edge systems on the lattice

Applies `YangMillsPrivateEdgeHaar` to SU(2) and the Wilson measure. Two-link dyadic blocking appears
as `dyadicSystem`. `privateEdge_wilsonMeasure` and `dyadic_wilsonMeasure` give the Wilson measure in
these coordinates as `Z⁻¹ exp(-β ∑_p D(U_p(W, V))) dH(W) dH(V)`, and `privateEdge_wilsonPartition`
gives `Z`. Holonomies are gauge covariant. A negative control shows the product law fails when two
paths share their only edge.

This is a factorisation of the reference measure only. See `YangMillsPrivateEdgeHaar` for what is
known about variable counts, and for the open question: the locality of the action induced on `W`.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace JesseMath.Physics.YangMillsPrivateEdgeHaar

section GaugeCovariance

variable {G E V' : Type*} [Group G] (src tgt : E → V')

/-- The source of an oriented edge. Orientation swaps the endpoints. -/
def oSrc (p : E × Bool) : V' := cond p.2 (src p.1) (tgt p.1)

/-- The target of an oriented edge. Orientation swaps the endpoints. -/
def oTgt (p : E × Bool) : V' := cond p.2 (tgt p.1) (src p.1)

/-- Each oriented edge of the path ends where the next one starts. -/
def Composable : OrientedPath E → Prop
  | [] => True
  | [_] => True
  | p :: q :: γ => oTgt src tgt p = oSrc src tgt q ∧ Composable (q :: γ)

/-- The gauge action on link variables. -/
def gaugeAct (g : V' → G) (U : E → G) : E → G := fun e => g (src e) * U e * (g (tgt e))⁻¹

theorem orient_gaugeAct (g : V' → G) (U : E → G) (p : E × Bool) :
    orient (gaugeAct src tgt g U p.1) p.2 =
      g (oSrc src tgt p) * orient (U p.1) p.2 * (g (oTgt src tgt p))⁻¹ := by
  obtain ⟨e, b⟩ := p
  cases b <;> simp [gaugeAct, oSrc, oTgt, mul_assoc]

/-- Gauge covariance: a composable path transforms by its first source and its last target. -/
theorem holonomy_gaugeAct (g : V' → G) (U : E → G) (p : E × Bool) (γ : OrientedPath E)
    (h : Composable src tgt (p :: γ)) :
    holonomy (gaugeAct src tgt g U) (p :: γ) =
      g (oSrc src tgt p) * holonomy U (p :: γ) *
        (g (oTgt src tgt ((p :: γ).getLast (List.cons_ne_nil p γ))))⁻¹ := by
  induction γ generalizing p with
  | nil => simp [orient_gaugeAct, mul_assoc]
  | cons q γ ih =>
    obtain ⟨hpq, hq⟩ := h
    rw [holonomy_cons, ih q hq, orient_gaugeAct, hpq,
      List.getLast_cons (List.cons_ne_nil q γ)]
    simp only [holonomy_cons, mul_assoc, inv_mul_cancel_left]

/-- The endpoint of a lattice link. -/
def linkTgt {L : ℕ} (e : Link L) : Lattice4D L := shift e.x e.μ

/-- The repo's lattice gauge transformation is `gaugeAct` for the link endpoints. -/
theorem holonomy_gaugeTransform {L : ℕ} (g : GaugeTransformation L) (U : GaugeConfig L)
    (p : Link L × Bool) (γ : OrientedPath (Link L)) (h : Composable Link.x linkTgt (p :: γ)) :
    holonomy (G := SU2) (gaugeTransform g U) (p :: γ) =
      g (oSrc Link.x linkTgt p) * holonomy (G := SU2) U (p :: γ) *
        (g (oTgt Link.x linkTgt ((p :: γ).getLast (List.cons_ne_nil p γ))))⁻¹ := by
  have hg : (gaugeTransform g U : Link L → SU2) = gaugeAct Link.x linkTgt g U := by
    funext e
    obtain ⟨x, μ⟩ := e
    rfl
  rw [hg]
  exact holonomy_gaugeAct Link.x linkTgt g U p γ h

end GaugeCovariance

section Instances

open YangMillsBlockGeometry

theorem count_edges_pair {E : Type*} [DecidableEq E] {a b : E} (h : a ≠ b) :
    (edges [(a, true), (b, true)]).count b = 1 := by
  simp [edges, h]

theorem not_mem_edges_pair {E : Type*} {a b c : E} (h0 : c ≠ a) (h1 : c ≠ b) :
    c ∉ edges [(a, true), (b, true)] := by
  simp [edges, h0, h1]

/-- A concrete system: two paths share the non-private edge `4` and cross their private edges
backward and forward. Shared non-private edges are allowed. -/
def railSystem : PrivateEdgeSystem (Fin 2) (Fin 5) where
  path i :=
    if i = 0 then [(0, true), (1, false), (4, true)] else [(4, false), (2, true), (3, false)]
  priv i := if i = 0 then 1 else 2
  priv_once := by decide
  priv_not_other := by decide

/-- The two-link dyadic blocking as a private-edge system on the real fine lattice: the second
fine link of each coarse link is private. -/
def dyadicSystem (L : ℕ) [NeZero L] : PrivateEdgeSystem (Link L) (Link (2 * L)) where
  path e := [(dyadicFineLink L (e, 0), true), (dyadicFineLink L (e, 1), true)]
  priv e := dyadicFineLink L (e, 1)
  priv_once e := count_edges_pair ((dyadicFineLink_injective L).ne (by simp))
  priv_not_other i j hij := not_mem_edges_pair
    ((dyadicFineLink_injective L).ne (by simp))
    ((dyadicFineLink_injective L).ne (by simpa using hij))

theorem dyadicSystem_coarse_apply {G : Type*} [Group G] (L : ℕ) [NeZero L]
    (U : Link (2 * L) → G) (e : Link L) :
    (dyadicSystem L).coarse U e = U (dyadicFineLink L (e, 0)) * U (dyadicFineLink L (e, 1)) := by
  simp only [PrivateEdgeSystem.coarse, dyadicSystem, holonomy_cons, holonomy_nil, orient_true,
    mul_one]

/-- The coarse map of `dyadicSystem` is the repo's dyadic block map. -/
theorem dyadicSystem_coarse (L : ℕ) [NeZero L] (U : GaugeConfig (2 * L)) :
    (dyadicSystem L).coarse (G := SU2) U = dyadicLinkBlockMap L U := by
  funext e
  refine (dyadicSystem_coarse_apply (G := SU2) L U e).trans ?_
  simp [dyadicLinkBlockMap]

/-- Inversion invariance of SU(2) Haar measure, from uniqueness of Haar probability measures. -/
instance : IsInvInvariant SU2.haarProbability := by
  have : IsProbabilityMeasure SU2.haarProbability.inv := by
    constructor
    rw [Measure.inv, Measure.map_apply measurable_inv MeasurableSet.univ]
    simp
  have : Measure.IsHaarMeasure SU2.haarProbability.inv := {}
  exact ⟨Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _⟩

/-- Equation (8) for SU(2) Haar measure on any private-edge system. -/
theorem su2_privateEdge_haar_disintegration {ι E : Type*} [DecidableEq E] [Fintype E] [Fintype ι]
    (S : PrivateEdgeSystem ι E) :
    (Measure.pi fun _ : E => SU2.haarProbability).map S.phi =
      (Measure.pi fun _ : ι => SU2.haarProbability).prod
        (Measure.pi fun _ : S.Rest => SU2.haarProbability) :=
  S.privateEdge_haar_disintegration SU2.haarProbability

/-- Equation (8) on the real fine lattice, for dyadic blocking. -/
theorem dyadic_haar_disintegration (L : ℕ) [NeZero L] :
    (gaugeHaarMeasure (2 * L)).map (dyadicSystem L).phi =
      (gaugeHaarMeasure L).prod
        (Measure.pi fun _ : (dyadicSystem L).Rest => SU2.haarProbability) :=
  su2_privateEdge_haar_disintegration (dyadicSystem L)

/-- The density of the Wilson measure against product Haar is measurable. -/
theorem wilsonDensity_measurable (L : ℕ) [NeZero L] (β : ℝ) :
    Measurable (fun U : GaugeConfig L =>
      ENNReal.ofReal (boltzmannWeight β U / wilsonPartition (gaugeHaarMeasure L) β)) :=
  ((wilsonWeight_measurable (measurable_wilsonAction β)).div_const _).ennreal_ofReal

/-- The Wilson measure in the coordinates of a private-edge system on the lattice: density
`Z⁻¹ exp(-β ∑_p D(U_p(W, V)))` against product Haar, with `D = plaquetteAction` and
`U(W, V) = solve W V`. -/
theorem privateEdge_wilsonMeasure {ι : Type*} [Fintype ι] {L : ℕ} [NeZero L]
    (S : PrivateEdgeSystem ι (Link L)) (β : ℝ) :
    (wilsonMeasure (gaugeHaarMeasure L) β).map S.phi =
      ((Measure.pi fun _ : ι => SU2.haarProbability).prod
        (Measure.pi fun _ : S.Rest => SU2.haarProbability)).withDensity fun p =>
          ENNReal.ofReal
            (Real.exp (-(β * ∑ q : Plaquette L, plaquetteAction (S.solve p.1 p.2) q)) /
              wilsonPartition (gaugeHaarMeasure L) β) :=
  S.privateEdge_haar_density SU2.haarProbability (wilsonDensity_measurable L β)

/-- The partition function in the same coordinates. -/
theorem privateEdge_wilsonPartition {ι : Type*} [Fintype ι] {L : ℕ} [NeZero L]
    (S : PrivateEdgeSystem ι (Link L)) (β : ℝ) :
    wilsonPartition (gaugeHaarMeasure L) β =
      ∫ p, Real.exp (-(β * ∑ q : Plaquette L, plaquetteAction (S.solve p.1 p.2) q))
        ∂((Measure.pi fun _ : ι => SU2.haarProbability).prod
          (Measure.pi fun _ : S.Rest => SU2.haarProbability)) := by
  rw [← (S.measurePreserving_phi SU2.haarProbability).integral_comp']
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  change boltzmannWeight β U =
    Real.exp (-(β * ∑ q : Plaquette L, plaquetteAction (S.solve (S.coarse U) (S.rest U)) q))
  rw [S.solve_coarse_rest U]
  rfl

/-- The Wilson measure on the fine lattice, for dyadic blocking. -/
theorem dyadic_wilsonMeasure (L : ℕ) [NeZero L] (β : ℝ) :
    (wilsonMeasure (gaugeHaarMeasure (2 * L)) β).map (dyadicSystem L).phi =
      ((gaugeHaarMeasure L).prod
        (Measure.pi fun _ : (dyadicSystem L).Rest => SU2.haarProbability)).withDensity fun p =>
          ENNReal.ofReal
            (Real.exp (-(β * ∑ q : Plaquette (2 * L),
                plaquetteAction ((dyadicSystem L).solve p.1 p.2) q)) /
              wilsonPartition (gaugeHaarMeasure (2 * L)) β) :=
  privateEdge_wilsonMeasure (dyadicSystem L) β

end Instances

section NegativeControl

variable {G : Type*} [Group G]

/-- Two paths that share their only edge. -/
def sharedPaths : Fin 2 → OrientedPath Unit := fun _ => [((), true)]

/-- These paths are not a private-edge system, whatever edges are proposed as private. -/
theorem sharedPaths_not_private : ¬ ∃ S : PrivateEdgeSystem (Fin 2) Unit, S.path = sharedPaths := by
  rintro ⟨S, hS⟩
  apply S.priv_not_other 0 1 (by decide)
  rw [hS]
  simp [sharedPaths]

/-- The pair of holonomies of the shared paths. -/
def sharedPair (U : Unit → G) : G × G := (holonomy U (sharedPaths 0), holonomy U (sharedPaths 1))

theorem sharedPair_eq : (sharedPair : (Unit → G) → G × G) = fun U => (U (), U ()) := by
  funext U
  simp [sharedPair, sharedPaths]

variable [MeasurableSpace G]

/-- Negative control: if `μ` has a measurable set of measure strictly between 0 and 1, then the
law of `(W₁, W₂) = (U e, U e)` is not a product of any two probability measures. -/
theorem sharedEdge_law_not_product (μ : Measure G) [IsProbabilityMeasure μ] {A : Set G}
    (hA : MeasurableSet A) (h0 : 0 < μ A) (h1 : μ A < 1)
    (ν₁ ν₂ : Measure G) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    (Measure.pi fun _ : Unit => μ).map sharedPair ≠ ν₁.prod ν₂ := by
  intro hL
  have hm : Measurable (sharedPair : (Unit → G) → G × G) := by
    rw [sharedPair_eq]
    exact (measurable_pi_apply ()).prodMk (measurable_pi_apply ())
  have heval : MeasurePreserving (Function.eval ()) (Measure.pi fun _ : Unit => μ) μ :=
    measurePreserving_eval _ ()
  have key {B C : Set G} (hB : MeasurableSet B) (hC : MeasurableSet C) :
      ν₁ B * ν₂ C = μ (B ∩ C) := by
    rw [← Measure.prod_prod, ← hL, Measure.map_apply hm (hB.prod hC)]
    have hpre : sharedPair ⁻¹' (B ×ˢ C) = Function.eval () ⁻¹' (B ∩ C) := by
      rw [sharedPair_eq]
      rfl
    rw [hpre, heval.measure_preimage (hB.inter hC).nullMeasurableSet]
  have hν₁ : ν₁ A = μ A := by
    simpa using key hA MeasurableSet.univ
  have hν₂ : ν₂ Aᶜ = μ Aᶜ := by
    simpa using key MeasurableSet.univ hA.compl
  have hzero : μ A * μ Aᶜ = 0 := by
    have := key hA hA.compl
    simpa [hν₁, hν₂] using this
  have hc : μ Aᶜ ≠ 0 := by
    rw [prob_compl_eq_one_sub hA]
    exact (tsub_pos_of_lt h1).ne'
  exact (mul_ne_zero h0.ne' hc) hzero

/-- The shared-edge coarse law also differs from the product Haar law of equation (8). -/
theorem sharedEdge_coarse_law_ne_pi (μ : Measure G) [IsProbabilityMeasure μ] {A : Set G}
    (hA : MeasurableSet A) (h0 : 0 < μ A) (h1 : μ A < 1) :
    (Measure.pi fun _ : Unit => μ).map (fun U i => holonomy U (sharedPaths i)) ≠
      Measure.pi fun _ : Fin 2 => μ := by
  intro h
  have hm : Measurable (fun (U : Unit → G) (i : Fin 2) => holonomy U (sharedPaths i)) := by
    refine measurable_pi_iff.2 fun i => ?_
    simpa [sharedPaths] using measurable_pi_apply ()
  have h2 := congrArg (Measure.map MeasurableEquiv.finTwoArrow) h
  rw [Measure.map_map MeasurableEquiv.finTwoArrow.measurable hm,
    (measurePreserving_finTwoArrow μ).map_eq] at h2
  exact sharedEdge_law_not_product μ hA h0 h1 μ μ h2

/-- The element `-1` of SU(2). -/
def su2MinusOne : SU2 where
  mat := -1
  unitary := by simp
  det_one := by simp [Matrix.det_neg]

theorem su2MinusOne_ne_one : su2MinusOne ≠ 1 := by
  intro h
  have h2 : (-1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := congrArg SU2.mat h
  have h3 := congrFun (congrFun h2 0) 0
  norm_num at h3

/-- SU(2) Haar measure is not a point mass: it has a set of intermediate measure. -/
theorem su2_haar_intermediate_set :
    ∃ A : Set SU2, MeasurableSet A ∧ 0 < SU2.haarProbability A ∧ SU2.haarProbability A < 1 := by
  obtain ⟨u, v, hu, hv, ha, hb, huv⟩ := t2_separation su2MinusOne_ne_one
  refine ⟨u, hu.measurableSet, hu.measure_pos _ ⟨_, ha⟩, ?_⟩
  have hvpos : 0 < SU2.haarProbability v := hv.measure_pos _ ⟨_, hb⟩
  have hle : SU2.haarProbability u ≤ SU2.haarProbability vᶜ :=
    measure_mono (Set.disjoint_left.1 huv)
  rw [prob_compl_eq_one_sub hv.measurableSet] at hle
  exact hle.trans_lt (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hvpos.ne')

/-- Negative control for SU(2) Haar measure. -/
theorem su2_sharedEdge_law_not_product (ν₁ ν₂ : Measure SU2)
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    (Measure.pi fun _ : Unit => SU2.haarProbability).map sharedPair ≠ ν₁.prod ν₂ := by
  obtain ⟨A, hA, h0, h1⟩ := su2_haar_intermediate_set
  exact sharedEdge_law_not_product _ hA h0 h1 ν₁ ν₂

end NegativeControl

end JesseMath.Physics.YangMillsPrivateEdgeHaar

#assert_zfc_axioms
