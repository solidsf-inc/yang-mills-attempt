import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.YangMillsWilsonPlaquetteTail

/-!
# One link of the Wilson action and the two ground-state sectors on `(0, π)`

Everything in the first part is about the repository's `wilsonAction`, `boltzmannWeight` and
`gaugeHaarMeasure` on `GaugeConfig L`, `L ≥ 2`.

* `wilson_link_reduction`, `wilsonAction_setLink`: with all other links fixed, `S(g) = C - β ⟨g, H⟩`, where `g` and `H` are
  vectors of `ℝ⁴`, `g` is the first column of the link and `H` is the sum of the staples.
* `norm_stapleSum_le`: `|H| ≤ 6`. So for `β ≥ 0` and `H ≠ 0` the unnormalised weight in the link is
  `exp (t ⟨g, h⟩)`, `h` a unit vector, with `t = β |H| ≤ 6 β`, in the normalisation
  `s_p = 1 - (1/2) Re tr U_p`. That rewriting is prose; Lean states the form `exp (β ⟨g, H⟩)`.
* `integral_wilsonWeight_resample`: the unnormalised Wilson integral with the link `e` integrated
  first against `exp (β ⟨g, H⟩) dHaar(g)`. No normalised conditional kernel is built here, and
  nothing is stated about `wilsonMeasure` itself.

The second part is real analysis on `(0, π)`, with `w = exp (t cos θ) sin² θ`.

* `nonradial_identity`, `radial_identity`: the two exact pointwise identities.
* `nonradial_ground_state`, `radial_ground_state`: `∫ (v'² + V v²) w ≥ 3 ∫ v² w` for the potentials
  `V = 2 csc² θ` and `V = 2 csc² θ + t cos θ`, for every real `t`.

Limits. The second part is not the Poincaré inequality on `SU(2)`. It is two one-dimensional
inequalities. Nothing here connects them to the group: the polar form of Haar measure, the gradient
on `SU(2)` and the decomposition of a function over the spheres `S²` are not formalised. The results
also say nothing about more than one link at a time, and give no decay of correlations. No target
theorem uses this module.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology Real RealInnerProductSpace

namespace JesseMath.Physics.YangMillsWilsonLinkSpectral

open JesseMath.Physics.YangMillsWilsonPlaquetteTail

/-! ## One link of the Wilson action -/

/-- First-column coordinates of `SU(2)` as a vector of Euclidean `ℝ⁴`. -/
def su2Vec (x : SU2) : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 x.coord

theorem norm_su2Vec (x : SU2) : ‖su2Vec x‖ = 1 := by
  have h := x.coord_sum_sq
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simpa [su2Vec] using h

theorem inner_su2Vec (a b : SU2) : ⟪su2Vec a, su2Vec b⟫ = 1 - linkDefect (a⁻¹ * b) := by
  rw [linkDefect_inv_mul, PiLp.inner_apply]
  simp [su2Vec, mul_comm]

variable {L : ℕ}

/-- The staple of the plaquette `q` at its boundary link `e`: the path along the other three sides,
oriented parallel to `e`. -/
def plaquetteStaple (U : GaugeConfig L) (q : Plaquette L) (e : Link L) : SU2 :=
  let a := U ⟨q.x, q.μ⟩
  let b := U ⟨shift q.x q.μ, q.ν⟩
  let c := U ⟨shift q.x q.ν, q.μ⟩
  let d := U ⟨q.x, q.ν⟩
  if e = ⟨q.x, q.μ⟩ then d * c * b⁻¹
  else if e = ⟨shift q.x q.μ, q.ν⟩ then a⁻¹ * d * c
  else if e = ⟨shift q.x q.ν, q.μ⟩ then d⁻¹ * a * b
  else a * b * c⁻¹

/-- The four sides of a plaquette are distinct links once `L ≥ 2`. -/
theorem boundary_links_ne (hL : 2 ≤ L) (q : Plaquette L) :
    (⟨q.x, q.μ⟩ : Link L) ≠ ⟨shift q.x q.μ, q.ν⟩ ∧ (⟨q.x, q.μ⟩ : Link L) ≠ ⟨shift q.x q.ν, q.μ⟩ ∧
    (⟨q.x, q.μ⟩ : Link L) ≠ ⟨q.x, q.ν⟩ ∧ (⟨shift q.x q.μ, q.ν⟩ : Link L) ≠ ⟨shift q.x q.ν, q.μ⟩ ∧
    (⟨shift q.x q.μ, q.ν⟩ : Link L) ≠ ⟨q.x, q.ν⟩ ∧ (⟨shift q.x q.ν, q.μ⟩ : Link L) ≠ ⟨q.x, q.ν⟩ := by
  have hμν : q.μ ≠ q.ν := ne_of_lt q.h
  exact ⟨fun h => hμν (congrArg Link.μ h), fun h => shift_ne hL q.x q.ν (congrArg Link.x h).symm,
    fun h => hμν (congrArg Link.μ h), fun h => hμν (congrArg Link.μ h).symm,
    fun h => shift_ne hL q.x q.μ (congrArg Link.x h), fun h => hμν (congrArg Link.μ h)⟩

/-- The configuration `U` with the variable on `e` replaced by `g`. -/
def setLink (U : GaugeConfig L) (e : Link L) (g : SU2) : GaugeConfig L :=
  fun f => if f = e then g else U f

@[simp] theorem setLink_self (U : GaugeConfig L) (e : Link L) (g : SU2) : setLink U e g e = g := by
  simp [setLink]

theorem setLink_of_ne (U : GaugeConfig L) {e f : Link L} (g : SU2) (h : f ≠ e) :
    setLink U e g f = U f := by
  simp [setLink, h]

theorem linkDefect_comm (a b : SU2) : linkDefect (a * b) = linkDefect (b * a) := by
  have h := linkDefect_conj a (b * a)
  rw [show a * (b * a) * a⁻¹ = a * b by group] at h
  exact h

/-- The three ways a plaquette holonomy carries the pair `g`, `W` have the same defect. -/
theorem linkDefect_mul_inv_eq (g W : SU2) : linkDefect (g * W⁻¹) = linkDefect (g⁻¹ * W) := by
  rw [linkDefect_comm, ← linkDefect_inv]
  group

theorem linkDefect_mul_inv_eq' (g W : SU2) : linkDefect (W * g⁻¹) = linkDefect (g⁻¹ * W) :=
  linkDefect_comm _ _

/-- The action of a plaquette through `e`, as a function of the link variable at `e`. -/
theorem plaquetteAction_setLink (hL : 2 ≤ L) (U : GaugeConfig L) (q : Plaquette L) {e : Link L}
    (he : e ∈ plaquetteBoundaryLinks q) (g : SU2) :
    plaquetteAction (setLink U e g) q = 1 - ⟪su2Vec g, su2Vec (plaquetteStaple U q e)⟫ := by
  obtain ⟨d12, d13, d14, d23, d24, d34⟩ := boundary_links_ne hL q
  classical
  rw [inner_su2Vec, plaquetteAction_eq_linkDefect, sub_sub_cancel]
  simp only [plaquetteBoundaryLinks, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · have hs : plaquetteStaple U q ⟨q.x, q.μ⟩ =
        U ⟨q.x, q.ν⟩ * U ⟨shift q.x q.ν, q.μ⟩ * (U ⟨shift q.x q.μ, q.ν⟩)⁻¹ := by
      simp only [plaquetteStaple, ↓reduceIte]
    have : plaquetteHolonomy (setLink U ⟨q.x, q.μ⟩ g) q = g * (plaquetteStaple U q ⟨q.x, q.μ⟩)⁻¹ := by
      rw [hs]
      simp only [plaquetteHolonomy, setLink_self, setLink_of_ne _ _ d12.symm,
        setLink_of_ne _ _ d13.symm, setLink_of_ne _ _ d14.symm]
      group
    rw [this, linkDefect_mul_inv_eq]
  · have hs : plaquetteStaple U q ⟨shift q.x q.μ, q.ν⟩ =
        (U ⟨q.x, q.μ⟩)⁻¹ * U ⟨q.x, q.ν⟩ * U ⟨shift q.x q.ν, q.μ⟩ := by
      simp only [plaquetteStaple, d12.symm, ↓reduceIte]
    have : plaquetteHolonomy (setLink U ⟨shift q.x q.μ, q.ν⟩ g) q =
        U ⟨q.x, q.μ⟩ * (g * (plaquetteStaple U q ⟨shift q.x q.μ, q.ν⟩)⁻¹) * (U ⟨q.x, q.μ⟩)⁻¹ := by
      rw [hs]
      simp only [plaquetteHolonomy, setLink_self, setLink_of_ne _ _ d12,
        setLink_of_ne _ _ d23.symm, setLink_of_ne _ _ d24.symm]
      group
    rw [this, linkDefect_conj, linkDefect_mul_inv_eq]
  · have hs : plaquetteStaple U q ⟨shift q.x q.ν, q.μ⟩ =
        (U ⟨q.x, q.ν⟩)⁻¹ * U ⟨q.x, q.μ⟩ * U ⟨shift q.x q.μ, q.ν⟩ := by
      simp only [plaquetteStaple, d13.symm, d23.symm, ↓reduceIte]
    have : plaquetteHolonomy (setLink U ⟨shift q.x q.ν, q.μ⟩ g) q =
        U ⟨q.x, q.ν⟩ * (plaquetteStaple U q ⟨shift q.x q.ν, q.μ⟩ * g⁻¹) * (U ⟨q.x, q.ν⟩)⁻¹ := by
      rw [hs]
      simp only [plaquetteHolonomy, setLink_self, setLink_of_ne _ _ d13,
        setLink_of_ne _ _ d23, setLink_of_ne _ _ d34.symm]
      group
    rw [this, linkDefect_conj, linkDefect_mul_inv_eq']
  · have hs : plaquetteStaple U q ⟨q.x, q.ν⟩ =
        U ⟨q.x, q.μ⟩ * U ⟨shift q.x q.μ, q.ν⟩ * (U ⟨shift q.x q.ν, q.μ⟩)⁻¹ := by
      simp only [plaquetteStaple, d14.symm, d24.symm, d34.symm, ↓reduceIte]
    have : plaquetteHolonomy (setLink U ⟨q.x, q.ν⟩ g) q =
        plaquetteStaple U q ⟨q.x, q.ν⟩ * g⁻¹ := by
      rw [hs]
      simp only [plaquetteHolonomy, setLink_self, setLink_of_ne _ _ d14,
        setLink_of_ne _ _ d24, setLink_of_ne _ _ d34]
    rw [this, linkDefect_mul_inv_eq']

/-- The staple does not read the variable on `e`. -/
theorem plaquetteStaple_setLink (hL : 2 ≤ L) (U : GaugeConfig L) (q : Plaquette L) {e : Link L}
    (he : e ∈ plaquetteBoundaryLinks q) (g : SU2) :
    plaquetteStaple (setLink U e g) q e = plaquetteStaple U q e := by
  obtain ⟨d12, d13, d14, d23, d24, d34⟩ := boundary_links_ne hL q
  classical
  simp only [plaquetteBoundaryLinks, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · simp only [plaquetteStaple, ↓reduceIte, setLink_of_ne _ _ d12.symm, setLink_of_ne _ _ d13.symm,
      setLink_of_ne _ _ d14.symm]
  · simp only [plaquetteStaple, d12.symm, ↓reduceIte, setLink_of_ne _ _ d12,
      setLink_of_ne _ _ d23.symm, setLink_of_ne _ _ d24.symm]
  · simp only [plaquetteStaple, d13.symm, d23.symm, ↓reduceIte, setLink_of_ne _ _ d13,
      setLink_of_ne _ _ d23, setLink_of_ne _ _ d34.symm]
  · simp only [plaquetteStaple, d14.symm, d24.symm, d34.symm, ↓reduceIte, setLink_of_ne _ _ d14,
      setLink_of_ne _ _ d24, setLink_of_ne _ _ d34]

/-- The staple sum `H` at the link `e`, a vector of `ℝ⁴`. -/
def stapleSum (U : GaugeConfig L) (e : Link L) : EuclideanSpace ℝ (Fin 4) :=
  ∑ q ∈ incidentPlaquettes e, su2Vec (plaquetteStaple U q e)

/-- `|H| ≤ 6`: at most six plaquettes contain a link, and each staple is a unit vector. -/
theorem norm_stapleSum_le (U : GaugeConfig L) (e : Link L) : ‖stapleSum U e‖ ≤ 6 := by
  calc ‖stapleSum U e‖ ≤ ∑ q ∈ incidentPlaquettes e, ‖su2Vec (plaquetteStaple U q e)‖ :=
        norm_sum_le _ _
    _ = ((incidentPlaquettes e).card : ℝ) := by simp [norm_su2Vec]
    _ ≤ 6 := by exact_mod_cast incidentPlaquettes_card_le_six e

theorem stapleSum_setLink (hL : 2 ≤ L) (U : GaugeConfig L) (e : Link L) (g : SU2) :
    stapleSum (setLink U e g) e = stapleSum U e :=
  Finset.sum_congr rfl fun q hq => by
    rw [plaquetteStaple_setLink hL U q (mem_plaquetteBoundaryLinks_of_mem_incidentPlaquettes e q hq)]

variable [NeZero L]

/-- The part of the action `S` that does not read the variable on `e`. -/
def linkActionConst (β : ℝ) (U : GaugeConfig L) (e : Link L) : ℝ :=
  β * (∑ q ∈ Finset.univ \ incidentPlaquettes e, plaquetteAction U q + (incidentPlaquettes e).card)

/-- With every other link fixed, the Wilson action is affine in the link:
`S(g) = C - β ⟨g, H⟩`, with `C` and `H` not reading the variable on `e` and `|H| ≤ 6`. -/
theorem wilsonAction_setLink (hL : 2 ≤ L) (β : ℝ) (U : GaugeConfig L) (e : Link L) (g : SU2) :
    wilsonAction β (setLink U e g) = linkActionConst β U e - β * ⟪su2Vec g, stapleSum U e⟫ := by
  classical
  have hoff : ∀ q ∈ Finset.univ \ incidentPlaquettes e,
      plaquetteAction (setLink U e g) q = plaquetteAction U q := fun q hq =>
    plaquetteAction_eq_of_agree_off_link _ _ e (fun f hf => setLink_of_ne U g hf) q
      (Finset.mem_sdiff.mp hq).2
  have hon : ∑ q ∈ incidentPlaquettes e, plaquetteAction (setLink U e g) q =
      (incidentPlaquettes e).card - ⟪su2Vec g, stapleSum U e⟫ := by
    rw [stapleSum, inner_sum, Finset.card_eq_sum_ones]
    push_cast
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q hq =>
      plaquetteAction_setLink hL U q (mem_plaquetteBoundaryLinks_of_mem_incidentPlaquettes e q hq) g
  unfold wilsonAction linkActionConst
  rw [← Finset.sum_sdiff (Finset.subset_univ (incidentPlaquettes e)), hon,
    Finset.sum_congr rfl hoff]
  ring

theorem linkActionConst_setLink (U : GaugeConfig L) (β : ℝ) (e : Link L) (g : SU2) :
    linkActionConst β (setLink U e g) e = linkActionConst β U e := by
  classical
  have h : ∑ q ∈ Finset.univ \ incidentPlaquettes e, plaquetteAction (setLink U e g) q =
      ∑ q ∈ Finset.univ \ incidentPlaquettes e, plaquetteAction U q :=
    Finset.sum_congr rfl fun q hq =>
      plaquetteAction_eq_of_agree_off_link _ _ e (fun f hf => setLink_of_ne U g hf) q
        (Finset.mem_sdiff.mp hq).2
  rw [linkActionConst, linkActionConst, h]

/-- The Boltzmann weight along one link: the density `exp (β ⟨g, H⟩)`, with `β|H| ≤ 6β`. -/
theorem boltzmannWeight_setLink (hL : 2 ≤ L) (β : ℝ) (U : GaugeConfig L) (e : Link L) (g : SU2) :
    boltzmannWeight β (setLink U e g) =
      Real.exp (-linkActionConst β U e) * Real.exp (β * ⟪su2Vec g, stapleSum U e⟫) := by
  rw [boltzmannWeight, wilsonAction_setLink hL, ← Real.exp_add]
  congr 1
  ring

/-- **Target 1**, assembled: the affine form, the bound on the staple sum, and the fact that neither
the constant nor the staple sum reads the variable on `e`. -/
theorem wilson_link_reduction (hL : 2 ≤ L) (β : ℝ) (U : GaugeConfig L) (e : Link L) :
    (∀ g, wilsonAction β (setLink U e g) = linkActionConst β U e - β * ⟪su2Vec g, stapleSum U e⟫) ∧
      ‖stapleSum U e‖ ≤ 6 ∧
      ∀ g, stapleSum (setLink U e g) e = stapleSum U e ∧
        linkActionConst β (setLink U e g) e = linkActionConst β U e :=
  ⟨wilsonAction_setLink hL β U e, norm_stapleSum_le U e,
    fun g => ⟨stapleSum_setLink hL U e g, linkActionConst_setLink U β e g⟩⟩

/-! ## Integrating one link out of the unnormalised Wilson weight -/

omit [NeZero L] in
theorem setLink_eq_linkMove (U : GaugeConfig L) (e : Link L) (g : SU2) :
    setLink U e g = linkMove e (g * (U e)⁻¹) U := by
  funext f
  by_cases h : f = e
  · subst h
    simp [linkMove_self]
  · rw [setLink_of_ne U g h, linkMove_of_ne e f _ U h]

/-- Resampling one link under product Haar: integrate out the variable on `e` first. -/
theorem integral_gaugeHaar_resample (e : Link L) {F : GaugeConfig L → ℝ} (hF : Continuous F) :
    ∫ U, F U ∂gaugeHaarMeasure L =
      ∫ U, ∫ g, F (setLink U e g) ∂SU2.haarProbability ∂gaugeHaarMeasure L := by
  have : CompactSpace (GaugeConfig L) := inferInstanceAs (CompactSpace (Link L → SU2))
  have heval (f : Link L) : Continuous fun U : GaugeConfig L => U f :=
    continuous_apply (A := fun _ : Link L => SU2) f
  have hjoint : Continuous fun p : SU2 × GaugeConfig L => linkMove e p.1 p.2 := by
    refine continuous_pi fun f => ?_
    simp only [linkMove]
    by_cases h : f = e
    · simp only [h, ↓reduceIte]
      exact continuous_fst.mul ((heval e).comp continuous_snd)
    · simp only [h, ↓reduceIte, one_mul]
      exact (heval f).comp continuous_snd
  have hint : Integrable (Function.uncurry fun (g : SU2) (U : GaugeConfig L) => F (linkMove e g U))
      (SU2.haarProbability.prod (gaugeHaarMeasure L)) :=
    (hF.comp hjoint).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hinv (g : SU2) : ∫ U, F (linkMove e g U) ∂gaugeHaarMeasure L = ∫ U, F U ∂gaugeHaarMeasure L := by
    have hT := measurePreserving_linkMove (L := L) e g
    have h := integral_map (μ := gaugeHaarMeasure L) hT.measurable.aemeasurable
      hF.aestronglyMeasurable
    rw [hT.map_eq] at h
    exact h.symm
  calc ∫ U, F U ∂gaugeHaarMeasure L
      = ∫ _g : SU2, ∫ U, F U ∂gaugeHaarMeasure L ∂SU2.haarProbability := by simp
    _ = ∫ g : SU2, ∫ U, F (linkMove e g U) ∂gaugeHaarMeasure L ∂SU2.haarProbability := by
        simp only [hinv]
    _ = ∫ U, ∫ g : SU2, F (linkMove e g U) ∂SU2.haarProbability ∂gaugeHaarMeasure L :=
        integral_integral_swap hint
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        simp only [setLink_eq_linkMove]
        exact (integral_mul_right_eq_self (μ := SU2.haarProbability)
          (fun g => F (linkMove e g U)) (U e)⁻¹).symm

/-- **Target 1, resampling form.** The unnormalised Wilson integral of `F` with the link `e`
integrated first against `exp (β ⟨g, H⟩) dHaar(g)`, where `H` and the prefactor do not read the
variable on `e`. This is not a normalised conditional kernel. -/
theorem integral_wilsonWeight_resample (hL : 2 ≤ L) (β : ℝ) (e : Link L) {F : GaugeConfig L → ℝ}
    (hF : Continuous F) :
    ∫ U, boltzmannWeight β U * F U ∂gaugeHaarMeasure L =
      ∫ U, Real.exp (-linkActionConst β U e) *
        ∫ g, Real.exp (β * ⟪su2Vec g, stapleSum U e⟫) * F (setLink U e g) ∂SU2.haarProbability
        ∂gaugeHaarMeasure L := by
  have hS : Continuous (boltzmannWeight (L := L) β) :=
    Real.continuous_exp.comp (continuous_wilsonAction β).neg
  rw [integral_gaugeHaar_resample e (F := fun U => boltzmannWeight β U * F U) (hS.mul hF)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only [boltzmannWeight_setLink hL, mul_assoc, MeasureTheory.integral_const_mul]

/-! ## The two supersolutions on `(0, π)` -/

/-- The trial function `sin θ · exp (-c t cos θ)`. -/
def gsPhi (c t θ : ℝ) : ℝ := Real.sin θ * Real.exp (-(c * t) * Real.cos θ)

/-- Its first derivative. -/
def gsPhi' (c t θ : ℝ) : ℝ :=
  (Real.cos θ + c * t * Real.sin θ ^ 2) * Real.exp (-(c * t) * Real.cos θ)

/-- Its second derivative. -/
def gsPhi'' (c t θ : ℝ) : ℝ :=
  (-Real.sin θ + 2 * (c * t) * Real.sin θ * Real.cos θ +
    (Real.cos θ + c * t * Real.sin θ ^ 2) * (c * t * Real.sin θ)) *
    Real.exp (-(c * t) * Real.cos θ)

theorem hasDerivAt_exp_cos (c t θ : ℝ) :
    HasDerivAt (fun x => Real.exp (-(c * t) * Real.cos x))
      (Real.exp (-(c * t) * Real.cos θ) * (c * t * Real.sin θ)) θ := by
  have h := ((Real.hasDerivAt_cos θ).const_mul (-(c * t))).exp
  convert h using 1
  ring

theorem hasDerivAt_gsPhi (c t θ : ℝ) : HasDerivAt (gsPhi c t) (gsPhi' c t θ) θ := by
  have h := (Real.hasDerivAt_sin θ).fun_mul (hasDerivAt_exp_cos c t θ)
  refine HasDerivAt.congr_deriv h ?_
  simp only [gsPhi']
  ring

theorem hasDerivAt_gsPhi' (c t θ : ℝ) : HasDerivAt (gsPhi' c t) (gsPhi'' c t θ) θ := by
  have hs2 : HasDerivAt (fun x => Real.sin x ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
    convert (Real.hasDerivAt_sin θ).pow 2 using 1
    ring
  have h := ((Real.hasDerivAt_cos θ).fun_add (hs2.const_mul (c * t))).fun_mul
    (hasDerivAt_exp_cos c t θ)
  refine HasDerivAt.congr_deriv h ?_
  simp only [gsPhi'']
  ring

theorem deriv_gsPhi (c t : ℝ) : deriv (gsPhi c t) = gsPhi' c t :=
  funext fun θ => (hasDerivAt_gsPhi c t θ).deriv

theorem deriv_deriv_gsPhi (c t θ : ℝ) : deriv (deriv (gsPhi c t)) θ = gsPhi'' c t θ := by
  rw [deriv_gsPhi, (hasDerivAt_gsPhi' c t θ).deriv]

/-- The one-parameter family behind both identities; `V = 2 / sin² θ + (5c - 1) t cos θ`. -/
theorem gsPhi_identity (c t θ : ℝ) (hs : Real.sin θ ≠ 0) :
    -gsPhi'' c t θ - (2 * Real.cos θ / Real.sin θ - t * Real.sin θ) * gsPhi' c t θ +
        (2 / Real.sin θ ^ 2 + (5 * c - 1) * t * Real.cos θ) * gsPhi c t θ =
      (3 + c * (1 - c) * t ^ 2 * Real.sin θ ^ 2) * gsPhi c t θ := by
  have hsk := Real.sin_sq_add_cos_sq θ
  simp only [gsPhi, gsPhi', gsPhi'']
  set s := Real.sin θ
  set k := Real.cos θ
  set e := Real.exp (-(c * t) * k)
  have key : -s * (-s + 2 * (c * t) * s * k + (k + c * t * s ^ 2) * (c * t * s)) -
      (2 * k - t * s ^ 2) * (k + c * t * s ^ 2) + 2 + (5 * c - 1) * t * k * s ^ 2 -
      (3 + c * (1 - c) * t ^ 2 * s ^ 2) * s ^ 2 = 0 := by
    linear_combination (-2) * hsk
  rw [← sub_eq_zero]
  have hfac : -((-s + 2 * (c * t) * s * k + (k + c * t * s ^ 2) * (c * t * s)) * e) -
        (2 * k / s - t * s) * ((k + c * t * s ^ 2) * e) +
        (2 / s ^ 2 + (5 * c - 1) * t * k) * (s * e) -
      (3 + c * (1 - c) * t ^ 2 * s ^ 2) * (s * e) =
      e / s * (-s * (-s + 2 * (c * t) * s * k + (k + c * t * s ^ 2) * (c * t * s)) -
      (2 * k - t * s ^ 2) * (k + c * t * s ^ 2) + 2 + (5 * c - 1) * t * k * s ^ 2 -
      (3 + c * (1 - c) * t ^ 2 * s ^ 2) * s ^ 2) := by
    field_simp
    ring
  rw [hfac, key, mul_zero]

/-- **Target 2, nonradial sector.** -/
theorem nonradial_identity (t : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    -deriv (deriv (gsPhi (1 / 5) t)) θ -
        (2 * Real.cos θ / Real.sin θ - t * Real.sin θ) * deriv (gsPhi (1 / 5) t) θ +
        2 / Real.sin θ ^ 2 * gsPhi (1 / 5) t θ =
      (3 + 4 * t ^ 2 / 25 * Real.sin θ ^ 2) * gsPhi (1 / 5) t θ := by
  have h := gsPhi_identity (1 / 5) t θ (Real.sin_pos_of_mem_Ioo hθ).ne'
  rw [deriv_deriv_gsPhi, deriv_gsPhi]
  convert h using 2 <;> ring

/-- **Target 2, radial sector.** -/
theorem radial_identity (t : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    -deriv (deriv (gsPhi (2 / 5) t)) θ -
        (2 * Real.cos θ / Real.sin θ - t * Real.sin θ) * deriv (gsPhi (2 / 5) t) θ +
        (2 / Real.sin θ ^ 2 + t * Real.cos θ) * gsPhi (2 / 5) t θ =
      (3 + 6 * t ^ 2 / 25 * Real.sin θ ^ 2) * gsPhi (2 / 5) t θ := by
  have h := gsPhi_identity (2 / 5) t θ (Real.sin_pos_of_mem_Ioo hθ).ne'
  rw [deriv_deriv_gsPhi, deriv_gsPhi]
  convert h using 2 <;> ring

/-! ## The weighted ground-state inequality on `(0, π)` -/

/-- The polar weight `exp (t cos θ) sin² θ` of the von Mises-Fisher density on `S³`. -/
def linkWeight (t θ : ℝ) : ℝ := Real.exp (t * Real.cos θ) * Real.sin θ ^ 2

/-- The boundary flux `φ'/φ · w`, which vanishes at both poles without any condition on `v`. -/
def fluxWeight (c t θ : ℝ) : ℝ :=
  Real.exp (t * Real.cos θ) * (Real.sin θ * (Real.cos θ + c * t * Real.sin θ ^ 2))

def fluxWeight' (c t θ : ℝ) : ℝ :=
  Real.exp (t * Real.cos θ) *
    (-(t * Real.sin θ) * (Real.sin θ * (Real.cos θ + c * t * Real.sin θ ^ 2)) +
      (Real.cos θ ^ 2 - Real.sin θ ^ 2 + 3 * (c * t) * Real.sin θ ^ 2 * Real.cos θ))

theorem hasDerivAt_fluxWeight (c t θ : ℝ) :
    HasDerivAt (fluxWeight c t) (fluxWeight' c t θ) θ := by
  have hE : HasDerivAt (fun x => Real.exp (t * Real.cos x))
      (Real.exp (t * Real.cos θ) * (t * -Real.sin θ)) θ :=
    ((Real.hasDerivAt_cos θ).const_mul t).exp
  have hs2 : HasDerivAt (fun x => Real.sin x ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
    convert (Real.hasDerivAt_sin θ).pow 2 using 1
    ring
  have h := hE.fun_mul ((Real.hasDerivAt_sin θ).fun_mul
    ((Real.hasDerivAt_cos θ).fun_add (hs2.const_mul (c * t))))
  refine HasDerivAt.congr_deriv h ?_
  simp only [fluxWeight']
  ring

theorem continuous_fluxWeight (c t : ℝ) : Continuous (fluxWeight c t) := by
  unfold fluxWeight
  fun_prop

/-- The pointwise form of the ground-state representation. -/
theorem flux_deriv_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (t θ v v' : ℝ) :
    fluxWeight' c t θ * v ^ 2 + fluxWeight c t θ * (2 * v * v') ≤
      v' ^ 2 * linkWeight t θ +
        (2 + (5 * c - 1) * t * Real.cos θ * Real.sin θ ^ 2) * Real.exp (t * Real.cos θ) * v ^ 2 -
        3 * (v ^ 2 * linkWeight t θ) := by
  have hsk := Real.sin_sq_add_cos_sq θ
  have hE := Real.exp_pos (t * Real.cos θ)
  simp only [fluxWeight, fluxWeight', linkWeight]
  set s := Real.sin θ
  set k := Real.cos θ
  set E := Real.exp (t * k)
  have hid : v' ^ 2 * (E * s ^ 2) + (2 + (5 * c - 1) * t * k * s ^ 2) * E * v ^ 2 -
        3 * (v ^ 2 * (E * s ^ 2)) -
      (E * (-(t * s) * (s * (k + c * t * s ^ 2)) + (k ^ 2 - s ^ 2 + 3 * (c * t) * s ^ 2 * k)) * v ^ 2 +
        E * (s * (k + c * t * s ^ 2)) * (2 * v * v')) =
      E * ((s * v' - (k + c * t * s ^ 2) * v) ^ 2 + c * (1 - c) * (t * s ^ 2 * v) ^ 2) := by
    linear_combination (-2 * E * v ^ 2) * hsk
  have hnn : 0 ≤ E * ((s * v' - (k + c * t * s ^ 2) * v) ^ 2 + c * (1 - c) * (t * s ^ 2 * v) ^ 2) := by
    have : 0 ≤ c * (1 - c) := mul_nonneg hc0 (by linarith)
    positivity
  linarith

/-- The family version: for every real `t` and every `c ∈ [0, 1]`, with
`V = 2 / sin² θ + (5c - 1) t cos θ`. The function `v` needs no vanishing at the poles: continuity on
`[0, π]` is enough, because the flux weight vanishes there. -/
theorem weighted_ground_state {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (t : ℝ) {v v' : ℝ → ℝ}
    (hv : ContinuousOn v (Icc 0 π)) (hd : ∀ θ ∈ Ioo 0 π, HasDerivAt v (v' θ) θ)
    (hint : IntegrableOn (fun θ => v' θ ^ 2 * linkWeight t θ) (Ioo 0 π)) :
    3 * ∫ θ in (0 : ℝ)..π, v θ ^ 2 * linkWeight t θ ≤
      ∫ θ in (0 : ℝ)..π,
        (v' θ ^ 2 + (2 / Real.sin θ ^ 2 + (5 * c - 1) * t * Real.cos θ) * v θ ^ 2) *
          linkWeight t θ := by
  set C : ℝ → ℝ := fun θ =>
    (2 + (5 * c - 1) * t * Real.cos θ * Real.sin θ ^ 2) * Real.exp (t * Real.cos θ) * v θ ^ 2 with hC
  set B : ℝ → ℝ := fun θ => v θ ^ 2 * linkWeight t θ with hB
  have hE : Continuous fun θ => Real.exp (t * Real.cos θ) := by fun_prop
  have hCcont : ContinuousOn C (Icc 0 π) := by
    apply ContinuousOn.mul
    · exact Continuous.continuousOn (by fun_prop)
    · exact hv.pow 2
  have hBcont : ContinuousOn B (Icc 0 π) := by
    apply ContinuousOn.mul (hv.pow 2)
    unfold linkWeight
    exact Continuous.continuousOn (by fun_prop)
  have hCint : IntegrableOn C (Icc 0 π) := hCcont.integrableOn_Icc
  have hBint : IntegrableOn B (Icc 0 π) := hBcont.integrableOn_Icc
  have hAint : IntegrableOn (fun θ => v' θ ^ 2 * linkWeight t θ) (Icc 0 π) :=
    Iff.mpr integrableOn_Icc_iff_integrableOn_Ioo hint
  have hFint : IntegrableOn (fun θ => v' θ ^ 2 * linkWeight t θ + C θ - 3 * B θ) (Icc 0 π) :=
    (hAint.add hCint).sub (hBint.const_mul 3)
  have hG := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    (g := fun θ => fluxWeight c t θ * v θ ^ 2)
    (g' := fun θ => fluxWeight' c t θ * v θ ^ 2 + fluxWeight c t θ * (2 * v θ * v' θ))
    (φ := fun θ => v' θ ^ 2 * linkWeight t θ + C θ - 3 * B θ) Real.pi_pos.le
    ((continuous_fluxWeight c t).continuousOn.mul (hv.pow 2))
    (fun θ hθ => by
      have h := (hasDerivAt_fluxWeight c t θ).fun_mul ((hd θ hθ).fun_pow 2)
      refine (HasDerivAt.congr_deriv h ?_).hasDerivWithinAt
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one])
    hFint (fun θ _ => flux_deriv_le hc0 hc1 t θ (v θ) (v' θ))
  have hzero : fluxWeight c t π * v π ^ 2 - fluxWeight c t 0 * v 0 ^ 2 = 0 := by
    simp [fluxWeight]
  simp only [hzero] at hG
  have hAi : IntervalIntegrable (fun θ => v' θ ^ 2 * linkWeight t θ) volume 0 π :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le).mpr hAint
  have hCi : IntervalIntegrable C volume 0 π :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le).mpr hCint
  have hBi : IntervalIntegrable B volume 0 π :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le).mpr hBint
  rw [intervalIntegral.integral_sub (hAi.add hCi) (hBi.const_mul 3),
    intervalIntegral.integral_const_mul] at hG
  have hR : ∫ θ in (0 : ℝ)..π,
        (v' θ ^ 2 + (2 / Real.sin θ ^ 2 + (5 * c - 1) * t * Real.cos θ) * v θ ^ 2) * linkWeight t θ =
      ∫ θ in (0 : ℝ)..π, (v' θ ^ 2 * linkWeight t θ + C θ) := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, intervalIntegral.integral_of_le Real.pi_pos.le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
    have hs := (Real.sin_pos_of_mem_Ioo hθ).ne'
    simp only [hC, linkWeight]
    field_simp
  rw [hR]
  linarith

/-- **Target 3, nonradial sector**: `∫ (v'² + 2 csc² θ v²) w ≥ 3 ∫ v² w`. -/
theorem nonradial_ground_state (t : ℝ) {v v' : ℝ → ℝ}
    (hv : ContinuousOn v (Icc 0 π)) (hd : ∀ θ ∈ Ioo 0 π, HasDerivAt v (v' θ) θ)
    (hint : IntegrableOn (fun θ => v' θ ^ 2 * linkWeight t θ) (Ioo 0 π)) :
    3 * ∫ θ in (0 : ℝ)..π, v θ ^ 2 * linkWeight t θ ≤
      ∫ θ in (0 : ℝ)..π, (v' θ ^ 2 + 2 / Real.sin θ ^ 2 * v θ ^ 2) * linkWeight t θ := by
  have h := weighted_ground_state (c := 1 / 5) (by norm_num) (by norm_num) t hv hd hint
  convert h using 4 with θ
  ring

/-- **Target 3, radial sector**: `∫ (v'² + (2 csc² θ + t cos θ) v²) w ≥ 3 ∫ v² w`. -/
theorem radial_ground_state (t : ℝ) {v v' : ℝ → ℝ}
    (hv : ContinuousOn v (Icc 0 π)) (hd : ∀ θ ∈ Ioo 0 π, HasDerivAt v (v' θ) θ)
    (hint : IntegrableOn (fun θ => v' θ ^ 2 * linkWeight t θ) (Ioo 0 π)) :
    3 * ∫ θ in (0 : ℝ)..π, v θ ^ 2 * linkWeight t θ ≤
      ∫ θ in (0 : ℝ)..π,
        (v' θ ^ 2 + (2 / Real.sin θ ^ 2 + t * Real.cos θ) * v θ ^ 2) * linkWeight t θ := by
  have h := weighted_ground_state (c := 2 / 5) (by norm_num) (by norm_num) t hv hd hint
  convert h using 4 with θ
  ring

end JesseMath.Physics.YangMillsWilsonLinkSpectral

#assert_zfc_axioms
