import Mathlib
import JesseMath.Linter.AxiomAudit

/-!
# Private-edge path-holonomy Haar disintegration

Each coarse variable is the holonomy of an oriented path. Each path owns a private edge that
occurs exactly once in it and in no other path. Under these hypotheses the map
`U ↦ (coarse holonomies, non-private links)` is a measurable equivalence that sends product Haar
measure to product Haar measure.

This is a factorisation of the reference measure only. It proves nothing about locality of the
induced interactions. In the coordinates `(W, V)` a plaquette term can read all links of each path
whose private edge it contains. For regular blocks of straight paths of `n` links, enumeration
outside this module gives `n + 3` variables for a plaquette with one private edge and `2n + 2` for
one with two, which occurs when the private edge is at the end of its path. Other systems can do
worse: `k` private edges on one plaquette read `k n + 4 - k` when no other link of the plaquette lies
on those paths, and a pinwheel of four straight paths reaches `4 n`.

That count depends on the coordinates. Take straight paths that revisit no vertex, with disjoint
interiors, and with no interior vertex that is an endpoint of any path, as for regular blocks. A
gauge transformation on the interior vertices then sets every non-private path link to `1` and puts
each holonomy on its private edge, inverted on a backward crossing. Every plaquette then reads at
most 4 variables (argued by hand and checked on random systems over `S₃` outside this module, not
formalised here).

This fails for the more general systems allowed here: a cycle of non-private links, or a chain of
them joining two path ends, has a holonomy that such a transformation cannot remove. On `S₃`, by
enumeration outside this module, a triangle is removable exactly when its loop is `1`. For the paths
`(0,0) → (1,0) → (2,0) → (3,0)` and `(1,0) → (1,1) → (1,2)`, each with a private last link, the
interiors are disjoint but `(1,0)` is an endpoint of the second path. The first link can be removed
only when it is already `1`, and the plaquette on the first private edge then reads 5 variables.

Neither count says anything about the action induced on `W` after integrating out the other links.
Its locality is open and is not addressed in this module.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace JesseMath.Physics.YangMillsPrivateEdgeHaar

section Paths

variable {G E : Type*} [Group G]

/-- Read a link forward (`true`) or backward (`false`). -/
def orient (g : G) (b : Bool) : G := cond b g g⁻¹

@[simp] theorem orient_true (g : G) : orient g true = g := rfl

@[simp] theorem orient_false (g : G) : orient g false = g⁻¹ := rfl

@[simp] theorem orient_orient (g : G) (b : Bool) : orient (orient g b) b = g := by
  cases b <;> simp

/-- An oriented path is a list of edges, each with an orientation. -/
abbrev OrientedPath (E : Type*) := List (E × Bool)

/-- The edges of a path, with repetition. -/
def edges (γ : OrientedPath E) : List E := γ.map Prod.fst

@[simp] theorem edges_nil : edges ([] : OrientedPath E) = [] := rfl

@[simp] theorem edges_cons (p : E × Bool) (γ : OrientedPath E) :
    edges (p :: γ) = p.1 :: edges γ := rfl

/-- The ordered product of the oriented link variables along a path. -/
def holonomy (U : E → G) : OrientedPath E → G
  | [] => 1
  | p :: γ => orient (U p.1) p.2 * holonomy U γ

@[simp] theorem holonomy_nil (U : E → G) : holonomy U [] = 1 := rfl

@[simp] theorem holonomy_cons (U : E → G) (p : E × Bool) (γ : OrientedPath E) :
    holonomy U (p :: γ) = orient (U p.1) p.2 * holonomy U γ := rfl

/-- A holonomy reads only the edges of its path. -/
theorem holonomy_congr {U U' : E → G} {γ : OrientedPath E}
    (h : ∀ e ∈ edges γ, U e = U' e) : holonomy U γ = holonomy U' γ := by
  induction γ with
  | nil => rfl
  | cons p γ ih =>
    rw [holonomy_cons, holonomy_cons, h p.1 (by simp), ih fun e he => h e (by simp [he])]

variable [DecidableEq E]

/-- The part of a path strictly before the first occurrence of `e`. -/
def before (e : E) : OrientedPath E → OrientedPath E
  | [] => []
  | p :: γ => if p.1 = e then [] else p :: before e γ

/-- The part of a path strictly after the first occurrence of `e`. -/
def after (e : E) : OrientedPath E → OrientedPath E
  | [] => []
  | p :: γ => if p.1 = e then γ else after e γ

/-- The orientation of the first occurrence of `e`. -/
def sign (e : E) : OrientedPath E → Bool
  | [] => true
  | p :: γ => if p.1 = e then p.2 else sign e γ

/-- Cut a holonomy at an edge of the path. -/
theorem holonomy_split (U : E → G) {e : E} {γ : OrientedPath E} (h : e ∈ edges γ) :
    holonomy U γ = holonomy U (before e γ) * orient (U e) (sign e γ) * holonomy U (after e γ) := by
  induction γ with
  | nil => simp at h
  | cons p γ ih =>
    by_cases hp : p.1 = e
    · subst hp
      simp [before, after, sign]
    · have h' : e ∈ edges γ := by
        rw [edges_cons, List.mem_cons] at h
        exact h.resolve_left (Ne.symm hp)
      simp [before, after, sign, hp, ih h', mul_assoc]

omit [Group G] in
theorem mem_edges_before {e f : E} {γ : OrientedPath E} (h : f ∈ edges (before e γ)) :
    f ∈ edges γ ∧ f ≠ e := by
  induction γ with
  | nil => simp [before] at h
  | cons p γ ih =>
    by_cases hp : p.1 = e
    · simp [before, hp] at h
    · simp only [before, hp, ite_false, edges_cons, List.mem_cons] at h ⊢
      rcases h with rfl | h
      · exact ⟨Or.inl rfl, hp⟩
      · exact ⟨Or.inr (ih h).1, (ih h).2⟩

omit [Group G] in
/-- If `e` occurs once, it does not occur after its occurrence. -/
theorem mem_edges_after {e f : E} {γ : OrientedPath E} (hc : (edges γ).count e = 1)
    (h : f ∈ edges (after e γ)) : f ∈ edges γ ∧ f ≠ e := by
  induction γ with
  | nil => simp [after] at h
  | cons p γ ih =>
    by_cases hp : p.1 = e
    · subst hp
      simp only [after, ite_true] at h
      have h0 : (edges γ).count p.1 = 0 := by
        simpa using hc
      refine ⟨by simp [h], ?_⟩
      rintro rfl
      exact (List.count_eq_zero.1 h0) h
    · have hc' : (edges γ).count e = 1 := by
        rwa [edges_cons, List.count_cons_of_ne hp] at hc
      simp only [after, hp, ite_false] at h
      exact ⟨by simp [(ih hc' h).1], (ih hc' h).2⟩

end Paths

/-- Paths with private edges: `priv i` occurs exactly once in `path i` and in no other path. -/
structure PrivateEdgeSystem (ι E : Type*) [DecidableEq E] where
  /-- The path carrying the coarse variable `i`. -/
  path : ι → OrientedPath E
  /-- The edge owned by the path `i`. -/
  priv : ι → E
  priv_once : ∀ i, (edges (path i)).count (priv i) = 1
  priv_not_other : ∀ i j, i ≠ j → priv i ∉ edges (path j)

namespace PrivateEdgeSystem

section Algebra

variable {ι E G : Type*} [DecidableEq E] (S : PrivateEdgeSystem ι E)

theorem priv_mem_path (i : ι) : S.priv i ∈ edges (S.path i) :=
  List.count_pos_iff.1 (by rw [S.priv_once]; omega)

/-- Distinct paths have distinct private edges. -/
theorem priv_injective : Function.Injective S.priv := by
  intro i j h
  by_contra hij
  exact S.priv_not_other j i (Ne.symm hij) (h ▸ S.priv_mem_path i)

/-- The edge is private to some path. -/
abbrev IsPriv (e : E) : Prop := ∃ i, S.priv i = e

/-- The edges outside the range of `priv`. -/
abbrev Rest : Type _ := {e : E // ¬ S.IsPriv e}

/-- Every edge of `path i` other than `priv i` is outside the range of `priv`. -/
theorem not_isPriv_of_mem {i : ι} {f : E} (hf : f ∈ edges (S.path i)) (hne : f ≠ S.priv i) :
    ¬ S.IsPriv f := by
  rintro ⟨j, rfl⟩
  by_cases hij : j = i
  · exact hne (by rw [hij])
  · exact S.priv_not_other j i hij hf

/-- The restriction of a configuration to the non-private edges. -/
def rest (U : E → G) : S.Rest → G := fun e => U e.1

/-- The coarse variables: the holonomies of the paths. -/
def coarse [Group G] (U : E → G) : ι → G := fun i => holonomy U (S.path i)

variable [Group G] [Fintype ι]

/-- Extend non-private data to all edges, with `1` on the private ones. -/
def fill (V : S.Rest → G) : E → G := fun e => if h : S.IsPriv e then 1 else V ⟨e, h⟩

/-- `A i`: the holonomy before the private edge. Its argument holds no private edge. -/
def A (i : ι) (V : S.Rest → G) : G := holonomy (S.fill V) (before (S.priv i) (S.path i))

/-- `B i`: the holonomy after the private edge. Its argument holds no private edge. -/
def B (i : ι) (V : S.Rest → G) : G := holonomy (S.fill V) (after (S.priv i) (S.path i))

/-- The orientation in which `path i` crosses its private edge. -/
def orientation (i : ι) : Bool := sign (S.priv i) (S.path i)

theorem fill_rest (U : E → G) {f : E} (hf : ¬ S.IsPriv f) : S.fill (S.rest U) f = U f := by
  simp [fill, rest, hf]

/-- Factorisation: `W i = A i (V) * U (priv i)^{±1} * B i (V)`. -/
theorem holonomy_factor (U : E → G) (i : ι) :
    holonomy U (S.path i) =
      S.A i (S.rest U) * orient (U (S.priv i)) (S.orientation i) * S.B i (S.rest U) := by
  have hA : S.A i (S.rest U) = holonomy U (before (S.priv i) (S.path i)) :=
    holonomy_congr fun f hf => by
      obtain ⟨hmem, hne⟩ := mem_edges_before hf
      exact S.fill_rest U (S.not_isPriv_of_mem hmem hne)
  have hB : S.B i (S.rest U) = holonomy U (after (S.priv i) (S.path i)) :=
    holonomy_congr fun f hf => by
      obtain ⟨hmem, hne⟩ := mem_edges_after (S.priv_once i) hf
      exact S.fill_rest U (S.not_isPriv_of_mem hmem hne)
  rw [hA, hB]
  exact holonomy_split U (S.priv_mem_path i)

/-- The inverse: solve `U (priv i)` from `W i` and `V`, and keep `V` on the other edges. -/
def solve (W : ι → G) (V : S.Rest → G) : E → G := fun e =>
  if h : S.IsPriv e then
    orient ((S.A h.choose V)⁻¹ * W h.choose * (S.B h.choose V)⁻¹) (S.orientation h.choose)
  else V ⟨e, h⟩

/-- Forward crossing: `U (priv i) = (A V)⁻¹ * W i * (B V)⁻¹`. Backward crossing: the inverse of that,
`B V * (W i)⁻¹ * A V`. -/
theorem solve_priv (W : ι → G) (V : S.Rest → G) (i : ι) :
    S.solve W V (S.priv i) =
      orient ((S.A i V)⁻¹ * W i * (S.B i V)⁻¹) (S.orientation i) := by
  have h : S.IsPriv (S.priv i) := ⟨i, rfl⟩
  have hi : h.choose = i := S.priv_injective h.choose_spec
  simp only [solve, dite_eq_left h, hi]

theorem solve_rest (W : ι → G) (V : S.Rest → G) {e : E} (h : ¬ S.IsPriv e) :
    S.solve W V e = V ⟨e, h⟩ := by
  simp only [solve, dite_eq_right h]

theorem rest_solve (W : ι → G) (V : S.Rest → G) : S.rest (S.solve W V) = V := by
  funext e
  exact S.solve_rest W V e.2

theorem coarse_solve (W : ι → G) (V : S.Rest → G) : S.coarse (S.solve W V) = W := by
  funext i
  rw [coarse, holonomy_factor, rest_solve, solve_priv, orient_orient]
  group

theorem solve_coarse_rest (U : E → G) : S.solve (S.coarse U) (S.rest U) = U := by
  funext e
  by_cases h : S.IsPriv e
  · obtain ⟨i, rfl⟩ := h
    rw [solve_priv, coarse, holonomy_factor]
    have : (S.A i (S.rest U))⁻¹ * (S.A i (S.rest U) *
        orient (U (S.priv i)) (S.orientation i) * S.B i (S.rest U)) * (S.B i (S.rest U))⁻¹ =
        orient (U (S.priv i)) (S.orientation i) := by group
    rw [this, orient_orient]
  · rw [S.solve_rest _ _ h]
    rfl

/-- `Φ` as a plain bijection. -/
def phiEquiv : (E → G) ≃ (ι → G) × (S.Rest → G) where
  toFun U := (S.coarse U, S.rest U)
  invFun p := S.solve p.1 p.2
  left_inv U := S.solve_coarse_rest U
  right_inv p := Prod.ext (S.coarse_solve p.1 p.2) (S.rest_solve p.1 p.2)

end Algebra

end PrivateEdgeSystem

section Measurability

variable {G E : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

omit [MeasurableMul₂ G] in
theorem measurable_orient (b : Bool) : Measurable (fun x : G => orient x b) := by
  cases b
  · exact measurable_inv
  · exact measurable_id

theorem measurable_holonomy (γ : OrientedPath E) :
    Measurable (fun U : E → G => holonomy U γ) := by
  induction γ with
  | nil => exact measurable_const
  | cons p γ ih => exact ((measurable_orient p.2).comp (measurable_pi_apply p.1)).mul ih

end Measurability

namespace PrivateEdgeSystem

section MeasureSection

variable {ι E G : Type*} [DecidableEq E] [Fintype ι]
  [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  (S : PrivateEdgeSystem ι E)

omit [Fintype ι] [Group G] [MeasurableMul₂ G] [MeasurableInv G] in
theorem measurable_rest : Measurable (S.rest : (E → G) → S.Rest → G) :=
  measurable_pi_iff.2 fun e => measurable_pi_apply e.1

omit [Fintype ι] in
theorem measurable_coarse : Measurable (S.coarse : (E → G) → ι → G) :=
  measurable_pi_iff.2 fun i => measurable_holonomy (S.path i)

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem measurable_fill : Measurable (S.fill : (S.Rest → G) → E → G) := by
  refine measurable_pi_iff.2 fun e => ?_
  by_cases h : S.IsPriv e
  · simpa only [fill, dite_eq_left h] using measurable_const
  · simpa only [fill, dite_eq_right h] using measurable_pi_apply (⟨e, h⟩ : S.Rest)

theorem measurable_A (i : ι) : Measurable (S.A i : (S.Rest → G) → G) :=
  (measurable_holonomy _).comp S.measurable_fill

theorem measurable_B (i : ι) : Measurable (S.B i : (S.Rest → G) → G) :=
  (measurable_holonomy _).comp S.measurable_fill

theorem measurable_solve :
    Measurable (fun p : (ι → G) × (S.Rest → G) => S.solve p.1 p.2) := by
  refine measurable_pi_iff.2 fun e => ?_
  by_cases h : S.IsPriv e
  · obtain ⟨i, rfl⟩ := h
    simp_rw [solve_priv]
    refine (measurable_orient _).comp ?_
    exact (((S.measurable_A i).comp measurable_snd).inv.mul
      ((measurable_pi_apply i).comp measurable_fst)).mul
      ((S.measurable_B i).comp measurable_snd).inv
  · simp_rw [S.solve_rest _ _ h]
    exact (measurable_pi_apply (⟨e, h⟩ : S.Rest)).comp measurable_snd

/-- `Φ U = (coarse U, rest U)` is a measurable equivalence. Its inverse is `solve`. -/
def phi : (E → G) ≃ᵐ (ι → G) × (S.Rest → G) where
  toEquiv := S.phiEquiv
  measurable_toFun := S.measurable_coarse.prodMk S.measurable_rest
  measurable_invFun := S.measurable_solve

@[simp] theorem phi_apply (U : E → G) : S.phi U = (S.coarse U, S.rest U) := rfl

@[simp] theorem phi_symm_apply (p : (ι → G) × (S.Rest → G)) :
    S.phi.symm p = S.solve p.1 p.2 := rfl

variable [Fintype E] (μ : Measure G) [IsProbabilityMeasure μ]

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Split the coordinates into private edges, indexed by `ι`, and the rest. -/
theorem measurePreserving_privSplit :
    MeasurePreserving (fun U : E → G => ((fun i => U (S.priv i) : ι → G), S.rest U))
      (Measure.pi fun _ : E => μ)
      ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : S.Rest => μ)) := by
  let f : ι ≃ {e // S.IsPriv e} := Equiv.ofBijective (fun i => ⟨S.priv i, i, rfl⟩)
    ⟨fun _ _ h => S.priv_injective (congrArg Subtype.val h),
      fun ⟨_, i, hi⟩ => ⟨i, Subtype.ext hi⟩⟩
  have h1 := measurePreserving_piEquivPiSubtypeProd (fun _ : E => μ) S.IsPriv
  have h2 := MeasurePreserving.symm _
    (measurePreserving_piCongrLeft (fun _ : {e // S.IsPriv e} => μ) f)
  exact (h2.prod (MeasurePreserving.id _)).comp h1

/-- The fibre map over fixed non-private data: twist each private variable by `A i`, `B i`. -/
def fiber (V : S.Rest → G) (X : ι → G) : ι → G :=
  fun i => S.A i V * orient (X i) (S.orientation i) * S.B i V

omit [Fintype E] [IsProbabilityMeasure μ] in
theorem measurable_uncurry_fiber : Measurable (Function.uncurry (S.fiber (G := G))) := by
  refine measurable_pi_iff.2 fun i => ?_
  have hX : Measurable (fun p : (S.Rest → G) × (ι → G) => orient (p.2 i) (S.orientation i)) :=
    (measurable_orient (S.orientation i)).comp ((measurable_pi_apply i).comp measurable_snd)
  exact (((S.measurable_A i).comp measurable_fst).mul hX).mul
    ((S.measurable_B i).comp measurable_fst)

variable [IsMulLeftInvariant μ] [IsMulRightInvariant μ] [IsInvInvariant μ]

omit [IsProbabilityMeasure μ] in
omit [DecidableEq E] [Fintype ι] [Fintype E] in
/-- A two-sided translate of an oriented variable preserves `μ`. -/
theorem measurePreserving_twist (a b : G) (s : Bool) :
    MeasurePreserving (fun x : G => a * orient x s * b) μ μ := by
  have ho : MeasurePreserving (fun x : G => orient x s) μ μ := by
    cases s
    · exact measurePreserving_inv μ
    · exact MeasurePreserving.id μ
  exact (measurePreserving_mul_right μ b).comp ((measurePreserving_mul_left μ a).comp ho)

omit [Fintype E] in
theorem measurePreserving_fiber (V : S.Rest → G) :
    MeasurePreserving (S.fiber V) (Measure.pi fun _ : ι => μ) (Measure.pi fun _ : ι => μ) :=
  measurePreserving_pi (fun _ => μ) (fun _ => μ)
    fun i => measurePreserving_twist μ (S.A i V) (S.B i V) (S.orientation i)

/-- `Φ` carries product Haar to product Haar: a skew product over the non-private links. -/
theorem measurePreserving_phi :
    MeasurePreserving S.phi (Measure.pi fun _ : E => μ)
      ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : S.Rest => μ)) := by
  have hsk : MeasurePreserving (fun p : (S.Rest → G) × (ι → G) => (p.1, S.fiber p.1 p.2))
      ((Measure.pi fun _ : S.Rest => μ).prod (Measure.pi fun _ : ι => μ))
      ((Measure.pi fun _ : S.Rest => μ).prod (Measure.pi fun _ : ι => μ)) :=
    MeasurePreserving.skew_product (MeasurePreserving.id _) S.measurable_uncurry_fiber
      (ae_of_all _ fun V => (S.measurePreserving_fiber μ V).map_eq)
  have h := measurePreserving_swap.comp
    (hsk.comp (measurePreserving_swap.comp (S.measurePreserving_privSplit μ)))
  convert h using 1
  funext U
  exact Prod.ext (funext fun i => S.holonomy_factor U i) rfl

/-- The review's equation (8): under product Haar, the coarse holonomies and the non-private
links are independent, and each family is product Haar. -/
theorem privateEdge_haar_disintegration :
    (Measure.pi fun _ : E => μ).map S.phi =
      (Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : S.Rest => μ) :=
  (S.measurePreserving_phi μ).map_eq

/-- The review's equation (9): the density form of the factorisation. -/
theorem privateEdge_haar_density {ρ : (E → G) → ENNReal} (hρ : Measurable ρ) :
    ((Measure.pi fun _ : E => μ).withDensity ρ).map S.phi =
      ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : S.Rest => μ)).withDensity
        (ρ ∘ S.phi.symm) := by
  ext s hs
  rw [Measure.map_apply S.phi.measurable hs, withDensity_apply _ (S.phi.measurable hs),
    withDensity_apply _ hs,
    ← (S.measurePreserving_phi μ).setLIntegral_comp_preimage hs
      (hρ.comp S.phi.symm.measurable)]
  simp [S.solve_coarse_rest]

/-- The coarse marginal alone is product Haar. `sharedEdge_coarse_law_ne_pi` shows this fails
without the private-edge hypothesis. -/
theorem map_coarse :
    (Measure.pi fun _ : E => μ).map S.coarse = Measure.pi fun _ : ι => μ := by
  have h := congrArg (Measure.map Prod.fst) (S.privateEdge_haar_disintegration μ)
  rw [Measure.map_map measurable_fst S.phi.measurable, Measure.map_fst_prod, measure_univ,
    one_smul] at h
  exact h

end MeasureSection

end PrivateEdgeSystem

/-- The hypotheses can be met: one path of one edge, which it owns. -/
example : Nonempty (PrivateEdgeSystem (Fin 1) Unit) :=
  ⟨{ path := fun _ => [((), true)]
     priv := fun _ => ()
     priv_once := fun _ => by simp [edges]
     priv_not_other := fun i j h => absurd (Subsingleton.elim i j) h }⟩

end JesseMath.Physics.YangMillsPrivateEdgeHaar

#assert_zfc_axioms
