import JesseMath.Linter.AxiomAudit
import JesseMath.Physics.YangMillsWeakCoupling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Volume law for the Haar neighbourhood mass of the flat configurations

The finite-volume weak-coupling bound of `YangMillsWeakCoupling`,
`P_β(S ≥ ε) ≤ exp (-β (ε - δ)) / c(L, δ)` (`haarWilsonMeasure_action_tail`), has denominator
`c(L, δ) = haarVacuumSublevelMass L δ`, the product-Haar mass of the open sublevel `{S < δ}` of the
unit-coupling Wilson action on the periodic `L⁴` torus with `N(L) = 4 L⁴` links. This module
determines how `c(L, δ)` depends on `N(L)` for the repository's `gaugeHaarMeasure` and
`wilsonAction`, with explicit constants and no added hypotheses.

* Single link. For the defect `linkDefect g = 1 - Re tr g / 2` (the plaquette action is the defect
  of the plaquette holonomy) and `c₁(η) = singleLinkMass η`, the Haar mass of `{linkDefect < η}`:
  `η² / 625 ≤ c₁(η)` for `0 < η ≤ 1`, by covering SU(2) with `(2K + 1)⁴` left translates, and
  `c₁(η) ≤ √(2η)`, by disjoint translates along the diagonal subgroup.
* Lower volume law. Four links of defect below `η` give plaquette action below `16 η`, so
  `c₁(δ / (96 L⁴))^N(L) ≤ c(L, δ)`, hence `((δ / (600 N))²)^N ≤ c(L, δ)` and
  `log (1 / c(L, δ)) ≤ 8 L⁴ log (2400 L⁴ / δ)`. At the density threshold `6 L⁴ δ` the base is
  uniform in `L`: `((δ / 400)²)^N(L) ≤ c(L, 6 L⁴ δ)`.
* Upper volume law. The `m(L) = L³ ⌊L/2⌋` direction-0 links whose second coordinate is an even
  number `2j < L - 1` each lie in exactly one of the chosen `(0, 1)` plaquettes. Fubini over these
  links and a union bound give `c(L, δ) ≤ 2^m c₁(2δ / m)^(⌊m/2⌋ + 1)` and
  `log (1 / c(L, δ)) ≥ (m / 4) log (m / (4δ)) - m log 2`. Hence `log (1 / c(L, δ))` is of order
  `N(L) log N(L)`, and a bound `c₁^N(L) ≤ c(L, δ)` with a base independent of `L` fails at every
  fixed `δ > 0`.
* Coupling growth. The bound tends to zero if and only if `β (ε - δ) + log c(L, δ) → ∞`. The
  schedule `β(L) = (8 L⁴ log (2400 L⁴ / δ) + g(L)) / (ε - δ)` with `g → ∞` drives the actual action
  tail to zero as `L → ∞`; if eventually `β(L) (ε - δ) ≤ κ L⁴ log L` with `κ < 1/4`, or
  `β(L) ≤ C L⁴`, the bound diverges. For the actual action tail itself, eventually
  `2400 (β(L) + 1) ≤ L^a` with `a < 1/32` (in particular any fixed `β`) forces
  `P_β(L)(S ≥ ε) → 1`, using `log Z_β ≥ -(8 L⁴ log (2400 (β + 1)) + L⁴)`.
  For density thresholds one fixed `β > 8 log (2400 / δ) / (ε - δ)` suffices on every torus.

Scope: these are finite-volume statements about the product Haar measure and the Wilson law.
For the bound `exp (-β (ε - δ)) / c(L, δ)` the required growth of `β(L)` is pinned to order
`L⁴ log L`; for the action-tail probability itself growth beyond `L^(1/32)` is shown to be
necessary and `L⁴ log L` sufficient, and the gap between the two is not closed here. The
constants are not sharp. No continuum limit, renormalization-group step, or mass gap is
asserted.
-/

noncomputable section
open Matrix MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology Real

namespace JesseMath.Physics

/-! ## Single-link defect and the Frobenius identity -/

/-- The single-element action density `1 - Re tr g / 2`; the plaquette action is this defect of
the plaquette holonomy. -/
def linkDefect (g : SU2) : ℝ := 1 - (1 / 2 : ℝ) * (SU2.trace g).re

/-- Squared Frobenius norm of a `2 × 2` complex matrix, written as the real trace `Re tr (Aᴴ A)`. -/
def frobSq (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (Matrix.trace (Aᴴ * A)).re

theorem SU2.mat_mul (g h : SU2) : (g * h).mat = g.mat * h.mat := rfl

theorem SU2.mat_inv (g : SU2) : (g⁻¹).mat = g.matᴴ := rfl

theorem SU2.mat_one : (1 : SU2).mat = 1 := rfl

theorem frobSq_nonneg (A : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ frobSq A := by
  simp only [frobSq, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Complex.add_re, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (A 0 0).re, sq_nonneg (A 0 0).im, sq_nonneg (A 0 1).re,
    sq_nonneg (A 0 1).im, sq_nonneg (A 1 0).re, sq_nonneg (A 1 0).im,
    sq_nonneg (A 1 1).re, sq_nonneg (A 1 1).im]

/-- Parallelogram identity for the squared Frobenius norm. -/
theorem frobSq_add_add_frobSq_sub (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    frobSq (A + B) + frobSq (A - B) = 2 * frobSq A + 2 * frobSq B := by
  have h : (A + B)ᴴ * (A + B) + (A - B)ᴴ * (A - B) = Aᴴ * A + Aᴴ * A + (Bᴴ * B + Bᴴ * B) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.add_mul,
      Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub]
    abel
  unfold frobSq
  rw [← Complex.add_re, ← Matrix.trace_add, h, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_add]
  simp only [Complex.add_re]
  ring

theorem frobSq_add_le (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    frobSq (A + B) ≤ 2 * frobSq A + 2 * frobSq B := by
  have h1 := frobSq_add_add_frobSq_sub A B
  have h2 := frobSq_nonneg (A - B)
  linarith

/-- Left multiplication by a special unitary matrix preserves the squared Frobenius norm. -/
theorem frobSq_su2_mul (g : SU2) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    frobSq (g.mat * A) = frobSq A := by
  unfold frobSq
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc g.matᴴ, g.unitary,
    Matrix.one_mul]

/-- The defect is a quarter of the squared Frobenius distance to the identity. -/
theorem frobSq_mat_sub_one (g : SU2) : frobSq (g.mat - 1) = 4 * linkDefect g := by
  unfold frobSq linkDefect SU2.trace
  have h : (g.mat - 1)ᴴ * (g.mat - 1) = 1 - g.matᴴ - g.mat + 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, g.unitary, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [h, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_one,
    Matrix.trace_conjTranspose, Fintype.card_fin]
  simp only [Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_re]
  norm_num
  ring

theorem linkDefect_inv (g : SU2) : linkDefect g⁻¹ = linkDefect g := by
  unfold linkDefect SU2.trace
  rw [SU2.mat_inv, Matrix.trace_conjTranspose]
  simp

theorem linkDefect_one : linkDefect 1 = 0 := by
  unfold linkDefect
  rw [SU2.trace_one]
  norm_num

theorem linkDefect_nonneg (g : SU2) : 0 ≤ linkDefect g := by
  unfold linkDefect
  have h := (SU2.trace_re_bounds g).2
  linarith

theorem linkDefect_le_two (g : SU2) : linkDefect g ≤ 2 := by
  unfold linkDefect
  have h := (SU2.trace_re_bounds g).1
  linarith

/-- Quasi-triangle inequality: `‖gh - 1‖² ≤ 2 ‖h - 1‖² + 2 ‖g - 1‖²`. -/
theorem linkDefect_mul_le (g h : SU2) :
    linkDefect (g * h) ≤ 2 * linkDefect g + 2 * linkDefect h := by
  have h1 : (g * h).mat - 1 = g.mat * (h.mat - 1) + (g.mat - 1) := by
    rw [SU2.mat_mul, Matrix.mul_sub, Matrix.mul_one]
    abel
  have h2 := frobSq_add_le (g.mat * (h.mat - 1)) (g.mat - 1)
  rw [frobSq_su2_mul, frobSq_mat_sub_one, frobSq_mat_sub_one, ← h1, frobSq_mat_sub_one] at h2
  linarith

@[continuity, fun_prop]
theorem continuous_linkDefect : Continuous linkDefect := by
  unfold linkDefect SU2.trace Matrix.trace
  fun_prop

/-! ## Plaquette control from four link defects -/

theorem plaquetteAction_eq_linkDefect {L : ℕ} (U : GaugeConfig L) (p : Plaquette L) :
    plaquetteAction U p = linkDefect (plaquetteHolonomy U p) := rfl

/-- Each plaquette action is at most four times the sum of its four link defects. -/
theorem plaquetteAction_le_four_mul_sum_linkDefect {L : ℕ} (U : GaugeConfig L) (p : Plaquette L) :
    plaquetteAction U p ≤ 4 * (linkDefect (U ⟨p.x, p.μ⟩) + linkDefect (U ⟨shift p.x p.μ, p.ν⟩) +
      linkDefect (U ⟨shift p.x p.ν, p.μ⟩) + linkDefect (U ⟨p.x, p.ν⟩)) := by
  rw [plaquetteAction_eq_linkDefect]
  unfold plaquetteHolonomy
  set a := U ⟨p.x, p.μ⟩
  set b := U ⟨shift p.x p.μ, p.ν⟩
  set c := U ⟨shift p.x p.ν, p.μ⟩
  set d := U ⟨p.x, p.ν⟩
  have hre : a * b * c⁻¹ * d⁻¹ = (a * b) * (c⁻¹ * d⁻¹) := by group
  rw [hre]
  have h1 := linkDefect_mul_le (a * b) (c⁻¹ * d⁻¹)
  have h2 := linkDefect_mul_le a b
  have h3 := linkDefect_mul_le c⁻¹ d⁻¹
  rw [linkDefect_inv, linkDefect_inv] at h3
  linarith

/-- Four links of defect below `η` give a plaquette action below `16 η`. -/
theorem plaquetteAction_lt_of_linkDefect_lt {L : ℕ} {U : GaugeConfig L} {η : ℝ}
    (hU : ∀ e : Link L, linkDefect (U e) < η) (p : Plaquette L) :
    plaquetteAction U p < 16 * η := by
  have h := plaquetteAction_le_four_mul_sum_linkDefect U p
  have h1 := hU ⟨p.x, p.μ⟩
  have h2 := hU ⟨shift p.x p.μ, p.ν⟩
  have h3 := hU ⟨shift p.x p.ν, p.μ⟩
  have h4 := hU ⟨p.x, p.ν⟩
  linarith

/-! ## First-column coordinates of SU(2) -/

/-- For `U ∈ SU(2)` the inverse `Uᴴ` is the adjugate, because `det U = 1`. -/
theorem SU2.conjTranspose_eq_adjugate (x : SU2) : x.matᴴ = x.mat.adjugate := by
  have h1 : x.mat⁻¹ = x.matᴴ := Matrix.inv_eq_left_inv x.unitary
  rw [← h1, Matrix.inv_def, x.det_one, Ring.inverse_one, one_smul]

theorem SU2.mat_one_one (x : SU2) : x.mat 1 1 = star (x.mat 0 0) := by
  have h := congrFun (congrFun x.conjTranspose_eq_adjugate 0) 0
  rw [Matrix.conjTranspose_apply, Matrix.adjugate_fin_two] at h
  simpa using h.symm

theorem SU2.mat_zero_one (x : SU2) : x.mat 0 1 = -star (x.mat 1 0) := by
  have h := congrFun (congrFun x.conjTranspose_eq_adjugate 1) 0
  rw [Matrix.conjTranspose_apply, Matrix.adjugate_fin_two] at h
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h
  rw [← star_star (x.mat 0 1), h, star_neg]

/-- Real coordinates `(Re U₀₀, Im U₀₀, Re U₁₀, Im U₁₀)` of the first column. -/
def SU2.coord (x : SU2) : Fin 4 → ℝ :=
  ![(x.mat 0 0).re, (x.mat 0 0).im, (x.mat 1 0).re, (x.mat 1 0).im]

/-- The first-column coordinates form a unit vector of `ℝ⁴`. -/
theorem SU2.coord_sum_sq (x : SU2) : ∑ i, x.coord i ^ 2 = 1 := by
  have h := SU2.col0_norm_sq x
  rw [Fin.sum_univ_four]
  simp only [SU2.coord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linarith

/-- The defect of `g⁻¹ x` is one minus the Euclidean inner product of first columns. -/
theorem linkDefect_inv_mul (g x : SU2) :
    linkDefect (g⁻¹ * x) = 1 - ∑ i, g.coord i * x.coord i := by
  have hg1 := g.mat_one_one
  have hg2 := g.mat_zero_one
  have hx1 := x.mat_one_one
  have hx2 := x.mat_zero_one
  have hm : (g⁻¹ * x).mat = g.matᴴ * x.mat := rfl
  unfold linkDefect SU2.trace
  rw [hm, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, Fin.sum_univ_four]
  simp only [Matrix.conjTranspose_apply, hg1, hg2, hx1, hx2]
  simp only [SU2.coord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Complex.add_re, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im,
    star_neg, Complex.conj_conj]
  ring

/-- The SU(2) element with prescribed unit first-column coordinates. -/
def SU2.ofCoord (q : Fin 4 → ℝ) (hq : ∑ i, q i ^ 2 = 1) : SU2 where
  mat := !![⟨q 0, q 1⟩, ⟨-q 2, q 3⟩; ⟨q 2, q 3⟩, ⟨q 0, -q 1⟩]
  unitary := by
    rw [Fin.sum_univ_four] at hq
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff] <;>
      constructor <;> nlinarith [hq]
  det_one := by
    rw [Fin.sum_univ_four] at hq
    rw [Matrix.det_fin_two_of]
    apply Complex.ext <;> simp <;> nlinarith [hq]

theorem SU2.coord_ofCoord (q : Fin 4 → ℝ) (hq : ∑ i, q i ^ 2 = 1) :
    (SU2.ofCoord q hq).coord = q := by
  funext i
  fin_cases i <;> rfl

/-! ## The explicit single-link neighbourhood and its Haar mass -/

/-- The explicit open identity neighbourhood of defect scale `η`. -/
def linkNeighbourhood (η : ℝ) : Set SU2 := {g | linkDefect g < η}

theorem isOpen_linkNeighbourhood (η : ℝ) : IsOpen (linkNeighbourhood η) :=
  isOpen_lt continuous_linkDefect continuous_const

theorem measurableSet_linkNeighbourhood (η : ℝ) : MeasurableSet (linkNeighbourhood η) :=
  (isOpen_linkNeighbourhood η).measurableSet

theorem one_mem_linkNeighbourhood {η : ℝ} (hη : 0 < η) : (1 : SU2) ∈ linkNeighbourhood η := by
  simp only [linkNeighbourhood, mem_ofPred_eq, linkDefect_one]
  exact hη

theorem linkNeighbourhood_mono {η₁ η₂ : ℝ} (h : η₁ ≤ η₂) :
    linkNeighbourhood η₁ ⊆ linkNeighbourhood η₂ := fun _ hg => lt_of_lt_of_le hg h

theorem linkNeighbourhood_eq_univ_of_two_lt {η : ℝ} (h : 2 < η) : linkNeighbourhood η = univ := by
  apply eq_univ_of_forall
  intro g
  exact lt_of_le_of_lt (linkDefect_le_two g) h

theorem linkNeighbourhood_eq_empty_of_nonpos {η : ℝ} (h : η ≤ 0) : linkNeighbourhood η = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro g hg
  exact (not_lt_of_ge (le_trans h (linkDefect_nonneg g))) hg

/-- The single-link Haar mass `c₁(η)`: the normalized Haar measure of the explicit neighbourhood. -/
def singleLinkMass (η : ℝ) : ℝ := SU2.haarProbability.real (linkNeighbourhood η)

theorem singleLinkMass_nonneg (η : ℝ) : 0 ≤ singleLinkMass η := measureReal_nonneg

theorem singleLinkMass_le_one (η : ℝ) : singleLinkMass η ≤ 1 := measureReal_le_one

theorem singleLinkMass_pos {η : ℝ} (hη : 0 < η) : 0 < singleLinkMass η := by
  have hne : (linkNeighbourhood η).Nonempty := ⟨1, one_mem_linkNeighbourhood hη⟩
  exact ENNReal.toReal_pos (ne_of_gt ((isOpen_linkNeighbourhood η).measure_pos _ hne))
    (measure_ne_top _ _)

theorem singleLinkMass_mono {η₁ η₂ : ℝ} (h : η₁ ≤ η₂) : singleLinkMass η₁ ≤ singleLinkMass η₂ :=
  measureReal_mono (linkNeighbourhood_mono h) (measure_ne_top _ _)

theorem singleLinkMass_eq_one_of_two_lt {η : ℝ} (h : 2 < η) : singleLinkMass η = 1 := by
  unfold singleLinkMass
  rw [linkNeighbourhood_eq_univ_of_two_lt h]
  simp [Measure.real]

theorem singleLinkMass_eq_zero_of_nonpos {η : ℝ} (h : η ≤ 0) : singleLinkMass η = 0 := by
  unfold singleLinkMass
  rw [linkNeighbourhood_eq_empty_of_nonpos h]
  simp

/-- The central element `-1 ∈ SU(2)`, of maximal defect `2`. -/
def negOne : SU2 where
  mat := -1
  unitary := by simp
  det_one := by rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]; norm_num

theorem linkDefect_negOne : linkDefect negOne = 2 := by
  unfold linkDefect SU2.trace negOne
  simp [Matrix.trace_neg, Matrix.trace_one]
  norm_num

/-- Below the maximal defect the neighbourhood misses an open set of positive Haar mass. -/
theorem singleLinkMass_lt_one_of_lt_two {η : ℝ} (h : η < 2) : singleLinkMass η < 1 := by
  set A : Set SU2 := {g | η < linkDefect g} with hA
  have hAo : IsOpen A := isOpen_lt continuous_const continuous_linkDefect
  have hAne : A.Nonempty := ⟨negOne, by simp only [hA, mem_ofPred_eq, linkDefect_negOne]; exact h⟩
  have hApos : 0 < SU2.haarProbability.real A :=
    ENNReal.toReal_pos (ne_of_gt (hAo.measure_pos _ hAne)) (measure_ne_top _ _)
  have hdisj : Disjoint (linkNeighbourhood η) A := by
    rw [Set.disjoint_left]
    intro g hg hgA
    exact lt_asymm (show linkDefect g < η from hg) (show η < linkDefect g from hgA)
  have hunion : SU2.haarProbability.real (linkNeighbourhood η ∪ A) =
      singleLinkMass η + SU2.haarProbability.real A :=
    measureReal_union hdisj hAo.measurableSet
  have hle : SU2.haarProbability.real (linkNeighbourhood η ∪ A) ≤ 1 := measureReal_le_one
  linarith

/-- Left translates of the neighbourhood carry the same Haar mass. -/
theorem haarProbability_real_translate (g : SU2) (η : ℝ) :
    SU2.haarProbability.real ((fun x => g⁻¹ * x) ⁻¹' linkNeighbourhood η) = singleLinkMass η := by
  simp only [Measure.real, singleLinkMass, measure_preimage_mul]

/-! ## Covering lower bound for the single-link mass -/

/-- Integer vectors of the cube `[-K, K]⁴`; scaled by `1 / K` they form a grid in `[-1, 1]⁴`. -/
def coordGrid (K : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(K : ℤ)) K

theorem card_coordGrid (K : ℕ) : (coordGrid K).card = (2 * K + 1) ^ 4 := by
  rw [coordGrid, Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- Squared Euclidean norm of the scaled grid vector `k / K`. -/
def gridNormSq (K : ℕ) (k : Fin 4 → ℤ) : ℝ := ∑ i, ((k i : ℝ) / K) ^ 2

theorem gridNormSq_nonneg (K : ℕ) (k : Fin 4 → ℤ) : 0 ≤ gridNormSq K k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The SU(2) element whose first column is the normalized grid vector `k / K`
(the identity for the zero vector). -/
def gridElement (K : ℕ) (k : Fin 4 → ℤ) : SU2 :=
  if h : gridNormSq K k = 0 then 1 else
    SU2.ofCoord (fun i => (k i : ℝ) / K / Real.sqrt (gridNormSq K k)) (by
      have hpos := gridNormSq_nonneg K k
      calc ∑ i, ((k i : ℝ) / K / Real.sqrt (gridNormSq K k)) ^ 2
          = ∑ i, ((k i : ℝ) / K) ^ 2 / gridNormSq K k := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [div_pow _ (Real.sqrt _), Real.sq_sqrt hpos]
        _ = gridNormSq K k / gridNormSq K k := by rw [← Finset.sum_div]; rfl
        _ = 1 := div_self h)

theorem gridElement_coord {K : ℕ} {k : Fin 4 → ℤ} (h : gridNormSq K k ≠ 0) :
    (gridElement K k).coord = fun i => (k i : ℝ) / K / Real.sqrt (gridNormSq K k) := by
  unfold gridElement
  rw [dite_eq_right_of_eq_false (eq_false h), SU2.coord_ofCoord]

/-- Normalization estimate: if `W = 2P - 1 + S` with `0 ≤ S < 1` and `W > 0`, then
`1 - P / √W ≤ S`. -/
theorem one_sub_div_sqrt_le {P S W : ℝ} (hW : W = 2 * P - 1 + S) (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hWpos : 0 < W) : 1 - P / Real.sqrt W ≤ S := by
  have hn := Real.sqrt_pos.mpr hWpos
  have hn2 := Real.sq_sqrt hWpos.le
  rw [sub_le_comm, le_div_iff₀ hn]
  nlinarith [sq_nonneg (Real.sqrt W - (1 - S)), mul_nonneg hS0 (sub_nonneg.mpr hS1.le)]

/-- Every element of SU(2) lies within defect `1 / K²` of a grid element. -/
theorem exists_gridElement_linkDefect_le {K : ℕ} (hK : 2 ≤ K) (x : SU2) :
    ∃ k ∈ coordGrid K, linkDefect ((gridElement K k)⁻¹ * x) ≤ 1 / (K : ℝ) ^ 2 := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  set c := x.coord with hc_def
  have hc : ∑ i, c i ^ 2 = 1 := x.coord_sum_sq
  set k : Fin 4 → ℤ := fun i => round ((K : ℝ) * c i) with hk_def
  have herr : ∀ i, |(k i : ℝ) / K - c i| ≤ 1 / (2 * K) := by
    intro i
    have h := abs_sub_round ((K : ℝ) * c i)
    have he : (k i : ℝ) / K - c i = -(((K : ℝ) * c i - round ((K : ℝ) * c i)) / K) := by
      simp only [hk_def]
      field_simp
      ring
    rw [he, abs_neg, abs_div, abs_of_pos hKpos, div_le_div_iff₀ hKpos (by positivity)]
    nlinarith
  have hci : ∀ i, |c i| ≤ 1 := by
    intro i
    have h1 : c i ^ 2 ≤ 1 := by
      rw [← hc]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (c j)) (Finset.mem_univ i)
    exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)
  refine ⟨k, ?_, ?_⟩
  · simp only [coordGrid, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h1 := abs_le.mp (abs_sub_round ((K : ℝ) * c i))
    have h2 := abs_le.mp (hci i)
    have hlo : (-(K : ℝ)) - 1 < (k i : ℝ) := by
      simp only [hk_def]
      nlinarith
    have hhi : (k i : ℝ) < (K : ℝ) + 1 := by
      simp only [hk_def]
      nlinarith
    constructor
    · have : -(K : ℤ) - 1 < k i := by exact_mod_cast hlo
      omega
    · have : k i < (K : ℤ) + 1 := by exact_mod_cast hhi
      omega
  · set w : Fin 4 → ℝ := fun i => (k i : ℝ) / K with hw_def
    set S := ∑ i, (w i - c i) ^ 2 with hS_def
    set P := ∑ i, w i * c i with hP_def
    set W := gridNormSq K k with hW_def
    have hS_le : S ≤ 1 / (K : ℝ) ^ 2 := by
      have hterm : ∀ i, (w i - c i) ^ 2 ≤ (1 / (2 * K)) ^ 2 := fun i => by
        have h := abs_le.mp (herr i)
        exact sq_le_sq' h.1 h.2
      calc S ≤ ∑ _i : Fin 4, (1 / (2 * (K : ℝ))) ^ 2 := Finset.sum_le_sum fun i _ => hterm i
        _ = 1 / (K : ℝ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
          ring
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hS1 : S < 1 := by
      have : 1 / (K : ℝ) ^ 2 ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    have hWeq : W = 2 * P - 1 + S := by
      simp only [hW_def, gridNormSq, hS_def, hP_def, hw_def]
      rw [Fin.sum_univ_four] at hc
      simp only [Fin.sum_univ_four]
      linear_combination (-1 : ℝ) * hc
    have hWpos : 0 < W := by
      rcases (gridNormSq_nonneg K k).lt_or_eq with h | h
      · exact h
      · exfalso
        have hw0 : ∀ i, w i = 0 := by
          intro i
          have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ((k j : ℝ) / K))).mp
            h.symm i (Finset.mem_univ i)
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
        have hS : S = 1 := by
          rw [← hc, hS_def]
          exact Finset.sum_congr rfl fun i _ => by rw [hw0 i]; ring
        linarith
    rw [linkDefect_inv_mul, gridElement_coord hWpos.ne']
    have hsum : ∑ i, (k i : ℝ) / K / Real.sqrt W * c i = P / Real.sqrt W := by
      rw [hP_def, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by simp only [hw_def]; ring
    rw [hsum]
    exact (one_sub_div_sqrt_le hWeq hS0 hS1 hWpos).trans hS_le

/-- Covering bound: `(2K + 1)⁴` left translates of the neighbourhood cover SU(2). -/
theorem one_le_card_mul_singleLinkMass {K : ℕ} (hK : 2 ≤ K) {η : ℝ}
    (hη : 1 / (K : ℝ) ^ 2 < η) :
    1 ≤ (((2 * K + 1) ^ 4 : ℕ) : ℝ) * singleLinkMass η := by
  have hcover : (Set.univ : Set SU2) ⊆
      ⋃ k ∈ coordGrid K, (fun x => (gridElement K k)⁻¹ * x) ⁻¹' linkNeighbourhood η := by
    intro x _
    obtain ⟨k, hk, hd⟩ := exists_gridElement_linkDefect_le hK x
    exact Set.mem_biUnion hk
      (show linkDefect ((gridElement K k)⁻¹ * x) < η from lt_of_le_of_lt hd hη)
  have h1 := (measureReal_mono (μ := SU2.haarProbability) hcover (measure_ne_top _ _)).trans
    (measureReal_biUnion_finset_le (μ := SU2.haarProbability) (coordGrid K) _)
  rw [probReal_univ, Finset.sum_congr rfl fun k _ => haarProbability_real_translate _ η,
    Finset.sum_const, card_coordGrid, nsmul_eq_mul] at h1
  exact h1

/-- Explicit single-link Haar mass lower bound `η² / 625 ≤ c₁(η)` on `0 < η ≤ 1`. This
discharges the neighbourhood-mass input from the actual Haar measure by a covering argument;
the exponent `2` is not optimal (the Weyl formula would give `3/2`). -/
theorem singleLinkMass_ge {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    η ^ 2 / 625 ≤ singleLinkMass η := by
  have hs := Real.sqrt_pos.mpr hη
  have hs1 : Real.sqrt η ≤ 1 := Real.sqrt_le_one.mpr hη1
  have hss : Real.sqrt η ^ 2 = η := Real.sq_sqrt hη.le
  set K : ℕ := ⌊1 / Real.sqrt η⌋₊ + 1 with hKdef
  have hinv1 : 1 ≤ 1 / Real.sqrt η := by rw [le_div_iff₀ hs]; linarith
  have hK1 : 1 / Real.sqrt η < K := by
    rw [hKdef]
    push_cast
    exact Nat.lt_floor_add_one _
  have hK2 : (K : ℝ) ≤ 1 / Real.sqrt η + 1 := by
    rw [hKdef]
    push_cast
    linarith [Nat.floor_le (le_trans zero_le_one hinv1)]
  have hKge2 : 2 ≤ K := by
    have : 1 ≤ ⌊1 / Real.sqrt η⌋₊ := Nat.le_floor (by exact_mod_cast hinv1)
    omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hKη : 1 / (K : ℝ) ^ 2 < η := by
    have h1 : 1 < Real.sqrt η * K := by
      have := (div_lt_iff₀ hs).mp hK1
      linarith
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hmain := one_le_card_mul_singleLinkMass hKge2 hKη
  have hcard : (((2 * K + 1) ^ 4 : ℕ) : ℝ) ≤ 625 / η ^ 2 := by
    have hb : (2 * (K : ℝ) + 1) ≤ 5 / Real.sqrt η := by
      rw [le_div_iff₀ hs]
      have : (K : ℝ) * Real.sqrt η ≤ 1 + Real.sqrt η := by
        have := mul_le_mul_of_nonneg_right hK2 hs.le
        rwa [add_mul, one_div, inv_mul_cancel₀ hs.ne', one_mul] at this
      nlinarith
    have h4 : (2 * (K : ℝ) + 1) ^ 4 ≤ (5 / Real.sqrt η) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hb 4
    have h5 : (5 / Real.sqrt η) ^ 4 = 625 / η ^ 2 := by
      have h4' : Real.sqrt η ^ 4 = η ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hss]
      rw [div_pow, h4']
      norm_num
    push_cast
    linarith
  have hm := singleLinkMass_nonneg η
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 625)]
  have : 1 ≤ 625 / η ^ 2 * singleLinkMass η :=
    le_trans hmain (mul_le_mul_of_nonneg_right hcard hm)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
  linarith

/-! ## Packing upper bound for the single-link mass -/

/-- The diagonal one-parameter subgroup `diag (exp (i φ), exp (-i φ))` of SU(2). -/
def SU2.rot (φ : ℝ) : SU2 :=
  SU2.ofCoord ![Real.cos φ, Real.sin φ, 0, 0] (by
    simp [Fin.sum_univ_four, Real.cos_sq_add_sin_sq])

theorem linkDefect_rot_inv_mul (φ ψ : ℝ) :
    linkDefect ((SU2.rot φ)⁻¹ * SU2.rot ψ) = 1 - Real.cos (ψ - φ) := by
  rw [linkDefect_inv_mul, SU2.rot, SU2.rot, SU2.coord_ofCoord, SU2.coord_ofCoord, Real.cos_sub,
    Fin.sum_univ_four]
  simp
  ring

/-- Jordan-type bound `2 θ² / π² ≤ 1 - cos θ` on `[0, π]`. -/
theorem two_mul_sq_div_pi_sq_le_one_sub_cos {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    2 * θ ^ 2 / π ^ 2 ≤ 1 - Real.cos θ := by
  have hpi := Real.pi_pos
  have hsin := Real.mul_le_sin (x := θ / 2) (by linarith) (by linarith)
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h2 := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h2
    rw [h2]
    have h3 := Real.sin_sq_add_cos_sq (θ / 2)
    linarith
  have hlow : θ / π ≤ Real.sin (θ / 2) := by
    calc θ / π = 2 / π * (θ / 2) := by ring
      _ ≤ _ := hsin
  have hnn : 0 ≤ θ / π := div_nonneg h0 hpi.le
  have hsq : (θ / π) ^ 2 ≤ Real.sin (θ / 2) ^ 2 := pow_le_pow_left₀ hnn hlow 2
  rw [hcos]
  have he : 2 * θ ^ 2 / π ^ 2 = 2 * (θ / π) ^ 2 := by ring
  rw [he]
  linarith

/-- Packing bound `c₁(η) ≤ √(2η)`: pairwise disjoint left translates of the neighbourhood along
the diagonal subgroup. -/
theorem singleLinkMass_le_sqrt {η : ℝ} (hη : 0 < η) : singleLinkMass η ≤ Real.sqrt (2 * η) := by
  by_cases hη2 : 1 / 2 < η
  · have h1 : 1 ≤ Real.sqrt (2 * η) := Real.one_le_sqrt.mpr (by linarith)
    exact (singleLinkMass_le_one η).trans h1
  have hη2' : η ≤ 1 / 2 := not_lt.mp hη2
  set s := Real.sqrt (2 * η) with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs1 : s ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hss : s ^ 2 = 2 * η := Real.sq_sqrt (by linarith)
  have hpi := Real.pi_pos
  set θ := π * s with hθ_def
  set n : ℕ := ⌊1 / s⌋₊ + 1 with hn_def
  have hn1 : 1 / s < n := by
    rw [hn_def]
    push_cast
    exact Nat.lt_floor_add_one _
  have hθ0 : 0 < θ := mul_pos hpi hs
  have hθπ : θ ≤ π := by
    rw [hθ_def]
    nlinarith
  have hnθ : ((n : ℝ) - 1) * θ ≤ π := by
    have hn' : ((n : ℝ) - 1) = ⌊1 / s⌋₊ := by
      rw [hn_def]
      push_cast
      ring
    rw [hn', hθ_def]
    have hfl : (⌊1 / s⌋₊ : ℝ) ≤ 1 / s := Nat.floor_le (by positivity)
    have hfl' : (⌊1 / s⌋₊ : ℝ) * s ≤ 1 :=
      (mul_le_mul_of_nonneg_right hfl hs.le).trans (one_div_mul_cancel hs.ne').le
    nlinarith
  have hsep : ∀ j ∈ Finset.range n, ∀ k ∈ Finset.range n, j ≠ k →
      4 * η ≤ linkDefect ((SU2.rot (j * θ))⁻¹ * SU2.rot (k * θ)) := by
    intro j hj k hk hjk
    rw [linkDefect_rot_inv_mul]
    have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hj
    have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hk
    have hd1 : 1 ≤ |(k : ℝ) - j| := by
      rcases Nat.lt_or_gt_of_ne hjk with h | h
      · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]
        linarith
      · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
        rw [abs_of_nonpos (by linarith)]
        linarith
    have hd2 : |(k : ℝ) - j| ≤ (n : ℝ) - 1 := by
      rw [abs_le]
      constructor <;> linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hcos : Real.cos ((k : ℝ) * θ - j * θ) = Real.cos (|(k : ℝ) - j| * θ) := by
      rw [← Real.cos_abs, show (k : ℝ) * θ - j * θ = ((k : ℝ) - j) * θ by ring, abs_mul,
        abs_of_pos hθ0]
    rw [hcos]
    have hle : Real.cos (|(k : ℝ) - j| * θ) ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi hθ0.le
        (le_trans (mul_le_mul_of_nonneg_right hd2 hθ0.le) hnθ) (by nlinarith)
    have hlow := two_mul_sq_div_pi_sq_le_one_sub_cos hθ0.le hθπ
    have he : 2 * θ ^ 2 / π ^ 2 = 4 * η := by
      rw [hθ_def, mul_pow, hss]
      field_simp
      ring
    linarith
  have hdisj : (↑(Finset.range n) : Set ℕ).PairwiseDisjoint
      (fun k : ℕ => (fun x => (SU2.rot (k * θ))⁻¹ * x) ⁻¹' linkNeighbourhood η) := by
    intro j hj k hk hjk
    show Disjoint _ _
    rw [Set.disjoint_left]
    intro x hxj hxk
    have h1 : linkDefect ((SU2.rot (j * θ))⁻¹ * x) < η := hxj
    have h2 : linkDefect ((SU2.rot (k * θ))⁻¹ * x) < η := hxk
    have h3 := linkDefect_mul_le ((SU2.rot (j * θ))⁻¹ * x) ((SU2.rot (k * θ))⁻¹ * x)⁻¹
    rw [linkDefect_inv] at h3
    have hgrp : (SU2.rot (j * θ))⁻¹ * x * ((SU2.rot (k * θ))⁻¹ * x)⁻¹ =
        (SU2.rot (j * θ))⁻¹ * SU2.rot (k * θ) := by group
    rw [hgrp] at h3
    have h4 := hsep j hj k hk hjk
    linarith
  have hunion := measureReal_biUnion_finset (μ := SU2.haarProbability) hdisj
    (fun k _ => (measurableSet_linkNeighbourhood η).preimage (measurable_const_mul _))
  rw [Finset.sum_congr rfl fun k _ => haarProbability_real_translate _ η, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hunion
  have hle : (n : ℝ) * singleLinkMass η ≤ 1 := hunion ▸ measureReal_le_one
  have hnpos : (0 : ℝ) < n := by positivity
  have hns : 1 < (n : ℝ) * s := by
    have := (div_lt_iff₀ hs).mp hn1
    linarith
  calc singleLinkMass η ≤ 1 / n := by rw [le_div_iff₀ hnpos]; linarith
    _ ≤ s := by rw [div_le_iff₀ hnpos]; linarith

/-! ## Product law: lower bounds for the vacuum sublevel mass -/

/-- The actual torus has `N(L) = 4 L⁴` oriented links. -/
theorem card_link (L : ℕ) [NeZero L] : Fintype.card (Link L) = 4 * L ^ 4 := by
  rw [Fintype.card_congr (linkEquiv L), Fintype.card_prod, card_lattice4D]
  simp [Direction, Nat.mul_comm]

/-- Configurations with every link in the explicit neighbourhood. -/
def linkBox (L : ℕ) (η : ℝ) : Set (GaugeConfig L) :=
  Set.univ.pi fun _ : Link L => linkNeighbourhood η

/-- Product Haar gives the box exactly the mass `c₁(η)^{N(L)}` with `N(L) = 4 L⁴`. -/
theorem gaugeHaarMeasure_real_linkBox (L : ℕ) [NeZero L] (η : ℝ) :
    (gaugeHaarMeasure L).real (linkBox L η) = singleLinkMass η ^ (4 * L ^ 4) := by
  change (Measure.pi (fun _ : Link L => SU2.haarProbability)
    (Set.univ.pi fun _ : Link L => linkNeighbourhood η)).toReal = _
  rw [Measure.pi_pi]
  simp [Measure.real, ENNReal.toReal_pow, card_link, singleLinkMass]

/-- Every box configuration has unit-coupling action below `6 L⁴ · 16 η`. -/
theorem linkBox_subset_sublevel (L : ℕ) [NeZero L] (η : ℝ) :
    linkBox L η ⊆ {U | wilsonAction 1 U < 6 * (L : ℝ) ^ 4 * (16 * η)} := by
  intro U hU
  have hlinks : ∀ e : Link L, linkDefect (U e) < η := fun e => hU e (mem_univ _)
  have hplaq : (Fintype.card (Plaquette L) : ℝ) = 6 * (L : ℝ) ^ 4 := by
    exact_mod_cast card_plaquette_eq_six_mul_pow_four L
  change wilsonAction 1 U < 6 * (L : ℝ) ^ 4 * (16 * η)
  calc
    wilsonAction 1 U = ∑ p : Plaquette L, plaquetteAction U p := by simp [wilsonAction]
    _ < ∑ _ : Plaquette L, 16 * η := by
      apply Finset.sum_lt_sum
      · intro p _
        exact (plaquetteAction_lt_of_linkDefect_lt hlinks p).le
      · exact ⟨⟨0, 0, 1, by decide⟩, Finset.mem_univ _,
          plaquetteAction_lt_of_linkDefect_lt hlinks _⟩
    _ = _ := by simp [hplaq]

/-- Product lower bound at a general scale: `c₁(η)^{4 L⁴} ≤ c(L, 96 L⁴ η)`. -/
theorem singleLinkMass_pow_le_haarVacuumSublevelMass (L : ℕ) [NeZero L] (η : ℝ) :
    singleLinkMass η ^ (4 * L ^ 4) ≤ haarVacuumSublevelMass L (6 * (L : ℝ) ^ 4 * (16 * η)) := by
  rw [← gaugeHaarMeasure_real_linkBox]
  exact measureReal_mono (linkBox_subset_sublevel L η) (measure_ne_top _ _)

/-- Density form: total threshold `6 L⁴ δ` (per-plaquette `δ`); the base `c₁(δ / 16)` depends
only on `δ` and the exponent is the link count `N(L) = 4 L⁴`. -/
theorem haarVacuumSublevelMass_density_lower (L : ℕ) [NeZero L] (δ : ℝ) :
    singleLinkMass (δ / 16) ^ (4 * L ^ 4) ≤ haarVacuumSublevelMass L (6 * (L : ℝ) ^ 4 * δ) := by
  have h := singleLinkMass_pow_le_haarVacuumSublevelMass L (δ / 16)
  have he : 6 * (L : ℝ) ^ 4 * (16 * (δ / 16)) = 6 * (L : ℝ) ^ 4 * δ := by ring
  rwa [he] at h

/-- Fixed total threshold `δ`: the single-link scale must shrink like `δ / (96 L⁴)`. -/
theorem haarVacuumSublevelMass_absolute_lower (L : ℕ) [NeZero L] (δ : ℝ) :
    singleLinkMass (δ / (96 * (L : ℝ) ^ 4)) ^ (4 * L ^ 4) ≤ haarVacuumSublevelMass L δ := by
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have h := singleLinkMass_pow_le_haarVacuumSublevelMass L (δ / (96 * (L : ℝ) ^ 4))
  have he : 6 * (L : ℝ) ^ 4 * (16 * (δ / (96 * (L : ℝ) ^ 4))) = δ := by
    field_simp
    ring
  rwa [he] at h

/-- Explicit density bound `(δ / 400)^{2 N(L)} ≤ c(L, 6 L⁴ δ)` for `0 < δ ≤ 16`: each link
contributes the factor `(δ / 400)² = (δ / 16)² / 625 ≤ c₁(δ / 16)`, uniform in `L`. -/
theorem haarVacuumSublevelMass_density_ge (L : ℕ) [NeZero L] {δ : ℝ} (hδ : 0 < δ)
    (hδ16 : δ ≤ 16) :
    ((δ / 400) ^ 2) ^ (4 * L ^ 4) ≤ haarVacuumSublevelMass L (6 * (L : ℝ) ^ 4 * δ) := by
  have h1 := singleLinkMass_ge (η := δ / 16) (by positivity) (by linarith)
  have h2 : (δ / 400) ^ 2 = (δ / 16) ^ 2 / 625 := by ring
  rw [h2]
  exact le_trans (pow_le_pow_left₀ (by positivity) h1 _)
    (haarVacuumSublevelMass_density_lower L δ)

/-- Explicit fixed-threshold bound `(δ / (2400 L⁴))^{2 N(L)} ≤ c(L, δ)` for
`0 < δ ≤ 96 L⁴`. The per-link base necessarily depends on `L`. -/
theorem haarVacuumSublevelMass_ge (L : ℕ) [NeZero L] {δ : ℝ} (hδ : 0 < δ)
    (hδL : δ ≤ 96 * (L : ℝ) ^ 4) :
    ((δ / (2400 * (L : ℝ) ^ 4)) ^ 2) ^ (4 * L ^ 4) ≤ haarVacuumSublevelMass L δ := by
  have hV : 0 < (L : ℝ) ^ 4 := pow_pos (Nat.cast_pos.mpr (NeZero.pos L)) _
  have h1 := singleLinkMass_ge (η := δ / (96 * (L : ℝ) ^ 4)) (by positivity)
    ((div_le_one (by positivity)).mpr hδL)
  have h2 : (δ / (2400 * (L : ℝ) ^ 4)) ^ 2 = (δ / (96 * (L : ℝ) ^ 4)) ^ 2 / 625 := by
    field_simp
    ring
  rw [h2]
  exact le_trans (pow_le_pow_left₀ (by positivity) h1 _)
    (haarVacuumSublevelMass_absolute_lower L δ)

/-- The fixed-threshold product law in terms of the link count `N = N(L) = 4 L⁴`:
`((δ / (600 N))²)^N ≤ c(L, δ)`. -/
theorem haarVacuumSublevelMass_ge_linkCount (L : ℕ) [NeZero L] {δ : ℝ} (hδ : 0 < δ)
    (hδL : δ ≤ 96 * (L : ℝ) ^ 4) :
    ((δ / (600 * (Fintype.card (Link L) : ℝ))) ^ 2) ^ Fintype.card (Link L) ≤
      haarVacuumSublevelMass L δ := by
  rw [card_link]
  have he : (600 : ℝ) * ((4 * L ^ 4 : ℕ) : ℝ) = 2400 * (L : ℝ) ^ 4 := by
    push_cast
    ring
  rw [he]
  exact haarVacuumSublevelMass_ge L hδ hδL

/-- Logarithmic form of the lower bound: `log (1 / c(L, δ)) ≤ 8 L⁴ log (2400 L⁴ / δ)`. -/
theorem log_haarVacuumSublevelMass_ge (L : ℕ) [NeZero L] {δ : ℝ} (hδ : 0 < δ)
    (hδL : δ ≤ 96 * (L : ℝ) ^ 4) :
    -(8 * (L : ℝ) ^ 4 * Real.log (2400 * (L : ℝ) ^ 4 / δ)) ≤
      Real.log (haarVacuumSublevelMass L δ) := by
  have hV : 0 < (L : ℝ) ^ 4 := pow_pos (Nat.cast_pos.mpr (NeZero.pos L)) _
  have hb := haarVacuumSublevelMass_ge L hδ hδL
  have hpos : 0 < ((δ / (2400 * (L : ℝ) ^ 4)) ^ 2) ^ (4 * L ^ 4) := by positivity
  have hlog := Real.log_le_log hpos hb
  rw [Real.log_pow, Real.log_pow] at hlog
  have hinv : Real.log (δ / (2400 * (L : ℝ) ^ 4)) = -Real.log (2400 * (L : ℝ) ^ 4 / δ) := by
    rw [← Real.log_inv, inv_div]
  rw [hinv] at hlog
  push_cast at hlog
  linarith

/-! ## Private links: an upper bound for the vacuum sublevel mass

Choose the plaquettes `(x, 0, 1)` whose base site has second coordinate `2j` with `j < L / 2`, and
call the first link `(x, 0)` of each its private link. The other three links of a chosen plaquette
are never private (two point in direction `1`; the third sits at the odd coordinate `2j + 1 < L`).
Left multiplication of the private links by independent Haar variables therefore multiplies each
chosen plaquette holonomy by its own variable and leaves the product Haar measure invariant. -/

/-- Index set of the private plaquettes: three free coordinates and a half-index `j < L / 2`. -/
abbrev PrivateIndex (L : ℕ) := (Fin 3 → ZMod L) × Fin (L / 2)

/-- The number `m(L) = L³ ⌊L / 2⌋` of private plaquettes. -/
def privateCount (L : ℕ) : ℕ := L ^ 3 * (L / 2)

theorem card_privateIndex (L : ℕ) [NeZero L] : Fintype.card (PrivateIndex L) = privateCount L := by
  simp [PrivateIndex, privateCount, Fintype.card_prod, ZMod.card]

/-- Base site of the private plaquette `i`; its second coordinate is the even number `2j`. -/
def privateSite {L : ℕ} (i : PrivateIndex L) : Lattice4D L :=
  ![i.1 0, ((2 * (i.2 : ℕ) : ℕ) : ZMod L), i.1 1, i.1 2]

/-- The private link of plaquette `i`: the direction-0 link at its base site. -/
def privateLink {L : ℕ} (i : PrivateIndex L) : Link L := ⟨privateSite i, 0⟩

/-- The private plaquette `i`, in the `(0, 1)` plane at `privateSite i`. -/
def privatePlaquette {L : ℕ} (i : PrivateIndex L) : Plaquette L :=
  ⟨privateSite i, 0, 1, by decide⟩

theorem natCast_inj_of_lt {L a b : ℕ} (ha : a < L) (hb : b < L)
    (h : (a : ZMod L) = (b : ZMod L)) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact h

theorem privateSite_injective {L : ℕ} : Function.Injective (privateSite (L := L)) := by
  intro i i' h
  have h0 : i.1 0 = i'.1 0 := congrFun h 0
  have h1 : ((2 * (i.2 : ℕ) : ℕ) : ZMod L) = ((2 * (i'.2 : ℕ) : ℕ) : ZMod L) := congrFun h 1
  have h2 : i.1 1 = i'.1 1 := congrFun h 2
  have h3 : i.1 2 = i'.1 2 := congrFun h 3
  have hi := i.2.isLt
  have hi' := i'.2.isLt
  have hj := natCast_inj_of_lt (by omega) (by omega) h1
  refine Prod.ext (funext fun t => ?_) (Fin.ext (by omega))
  fin_cases t
  · exact h0
  · exact h2
  · exact h3

theorem privateLink_injective {L : ℕ} : Function.Injective (privateLink (L := L)) :=
  fun _ _ h => privateSite_injective (congrArg Link.x h)

theorem privatePlaquette_injective {L : ℕ} : Function.Injective (privatePlaquette (L := L)) :=
  fun _ _ h => privateSite_injective (congrArg Plaquette.x h)

/-- No private link points in direction `1`. -/
theorem privateLink_ne_dir_one {L : ℕ} (i : PrivateIndex L) (x : Lattice4D L) :
    privateLink i ≠ ⟨x, 1⟩ := by
  intro h
  have h' : (0 : Fin 4) = 1 := congrArg Link.μ h
  exact absurd h' (by decide)

/-- The direction-0 link one step along direction `1` from a private site is not private:
its second coordinate `2j + 1` is odd and below `L`. -/
theorem privateLink_ne_shift_one {L : ℕ} (i i' : PrivateIndex L) :
    privateLink i' ≠ ⟨shift (privateSite i) 1, 0⟩ := by
  intro h
  have h1 : privateSite i' 1 = shift (privateSite i) 1 1 := congrFun (congrArg Link.x h) 1
  have hu : unitVec L 1 1 = 1 := by simp [unitVec]
  change ((2 * (i'.2 : ℕ) : ℕ) : ZMod L) = privateSite i 1 + unitVec L 1 1 at h1
  rw [hu] at h1
  change ((2 * (i'.2 : ℕ) : ℕ) : ZMod L) = ((2 * (i.2 : ℕ) : ℕ) : ZMod L) + 1 at h1
  have h1' : ((2 * (i'.2 : ℕ) : ℕ) : ZMod L) = ((2 * (i.2 : ℕ) + 1 : ℕ) : ZMod L) := by
    rw [h1]
    push_cast
    ring
  have hi := i.2.isLt
  have hi' := i'.2.isLt
  have := natCast_inj_of_lt (by omega) (by omega) h1'
  omega

/-- Extension of a private-link field by the identity on all other links. -/
def privateShift {L : ℕ} (y : PrivateIndex L → SU2) : GaugeConfig L :=
  Function.extend privateLink y 1

/-- Left multiplication of the private links by `y`; all other links are unchanged. -/
def privateAct {L : ℕ} (y : PrivateIndex L → SU2) (U : GaugeConfig L) : GaugeConfig L :=
  fun e => privateShift y e * U e

theorem privateShift_privateLink {L : ℕ} (y : PrivateIndex L → SU2) (i : PrivateIndex L) :
    privateShift y (privateLink i) = y i :=
  privateLink_injective.extend_apply y 1 i

theorem privateShift_of_not_private {L : ℕ} (y : PrivateIndex L → SU2) {e : Link L}
    (he : ∀ i, privateLink i ≠ e) : privateShift y e = 1 := by
  unfold privateShift
  rw [Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => he i hi]
  rfl

/-- The private action multiplies each private plaquette holonomy on the left by its variable. -/
theorem plaquetteHolonomy_privateAct {L : ℕ} (y : PrivateIndex L → SU2) (U : GaugeConfig L)
    (i : PrivateIndex L) :
    plaquetteHolonomy (privateAct y U) (privatePlaquette i) =
      y i * plaquetteHolonomy U (privatePlaquette i) := by
  have ha : privateShift y ⟨privateSite i, 0⟩ = y i := privateShift_privateLink y i
  have hb : privateShift y ⟨shift (privateSite i) 0, 1⟩ = 1 :=
    privateShift_of_not_private y fun i' => privateLink_ne_dir_one i' _
  have hc : privateShift y ⟨shift (privateSite i) 1, 0⟩ = 1 :=
    privateShift_of_not_private y fun i' => privateLink_ne_shift_one i i'
  have hd : privateShift y ⟨privateSite i, 1⟩ = 1 :=
    privateShift_of_not_private y fun i' => privateLink_ne_dir_one i' _
  simp only [plaquetteHolonomy, privatePlaquette, privateAct, ha, hb, hc, hd, one_mul]
  group

/-- For each fixed private field the private action preserves product Haar measure. -/
theorem measurePreserving_privateAct {L : ℕ} [NeZero L] (y : PrivateIndex L → SU2) :
    MeasurePreserving (privateAct y) (gaugeHaarMeasure L) (gaugeHaarMeasure L) := by
  change MeasurePreserving (fun (U : Link L → SU2) (e : Link L) => privateShift y e * U e)
    (Measure.pi (fun _ : Link L => SU2.haarProbability))
    (Measure.pi (fun _ : Link L => SU2.haarProbability))
  exact measurePreserving_pi _ _ fun e =>
    measurePreserving_mul_left SU2.haarProbability (privateShift y e)

theorem measurable_privateAct_uncurry {L : ℕ} [NeZero L] :
    Measurable (fun p : (PrivateIndex L → SU2) × GaugeConfig L => privateAct p.1 p.2) := by
  change Measurable (fun p : (PrivateIndex L → SU2) × (Link L → SU2) =>
    fun e => privateShift p.1 e * p.2 e)
  apply Measurable.of_eval
  intro e
  apply Measurable.mul _ ((measurable_pi_apply e).comp measurable_snd)
  by_cases he : ∃ i, privateLink i = e
  · obtain ⟨i, rfl⟩ := he
    simp only [privateShift_privateLink]
    exact (measurable_pi_apply i).comp measurable_fst
  · simp only [privateShift_of_not_private _ fun i hi => he ⟨i, hi⟩]
    exact measurable_const

/-- The private plaquette actions are part of the total unit-coupling action. -/
theorem sum_privatePlaquette_le_wilsonAction {L : ℕ} [NeZero L] (V : GaugeConfig L) :
    ∑ i : PrivateIndex L, plaquetteAction V (privatePlaquette i) ≤ wilsonAction 1 V := by
  calc ∑ i : PrivateIndex L, plaquetteAction V (privatePlaquette i)
      = ∑ p ∈ Finset.univ.image privatePlaquette, plaquetteAction V p :=
        (Finset.sum_image privatePlaquette_injective.injOn).symm
    _ ≤ ∑ p : Plaquette L, plaquetteAction V p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun p _ _ => plaquetteAction_nonneg V p
    _ = wilsonAction 1 V := by simp [wilsonAction]

/-- Private-link Fubini bound: `c(L, δ)` is at most the product-Haar probability that `m(L)`
independent Haar variables have total defect below `δ`. -/
theorem haarVacuumSublevelMass_le_privateMass (L : ℕ) [NeZero L] (δ : ℝ) :
    haarVacuumSublevelMass L δ ≤
      (Measure.pi fun _ : PrivateIndex L => SU2.haarProbability).real
        {z | ∑ i, linkDefect (z i) < δ} := by
  set μ := gaugeHaarMeasure L with hμ
  set ν := Measure.pi fun _ : PrivateIndex L => SU2.haarProbability with hν
  set E : Set (GaugeConfig L) := {U | wilsonAction 1 U < δ} with hE_def
  set A : Set (PrivateIndex L → SU2) := {z | ∑ i, linkDefect (z i) < δ} with hA_def
  have hE : MeasurableSet E := measurableSet_lt (measurable_wilsonAction 1) measurable_const
  have hA : MeasurableSet A :=
    measurableSet_lt (continuous_finsetSum _ fun i _ =>
      continuous_linkDefect.comp (continuous_apply i)).measurable measurable_const
  set G : Set ((PrivateIndex L → SU2) × GaugeConfig L) :=
    (fun p => privateAct p.1 p.2) ⁻¹' E with hG_def
  have hG : MeasurableSet G := hE.preimage measurable_privateAct_uncurry
  have h1 : ν.prod μ G = μ E := by
    rw [Measure.prod_apply hG]
    have hslice : ∀ y, μ (Prod.mk y ⁻¹' G) = μ E := fun y =>
      (measurePreserving_privateAct y).measure_preimage hE.nullMeasurableSet
    simp_rw [hslice]
    rw [lintegral_const, measure_univ, mul_one]
  have h2 : ν.prod μ G ≤ ν A := by
    rw [Measure.prod_apply_symm hG]
    calc ∫⁻ U, ν ((fun y => (y, U)) ⁻¹' G) ∂μ ≤ ∫⁻ _U, ν A ∂μ := by
          apply lintegral_mono
          intro U
          set h : PrivateIndex L → SU2 := fun i => plaquetteHolonomy U (privatePlaquette i)
          have hmp : MeasurePreserving (fun (y : PrivateIndex L → SU2) i => y i * h i) ν ν :=
            measurePreserving_pi _ _ fun i => measurePreserving_mul_right SU2.haarProbability (h i)
          calc ν ((fun y => (y, U)) ⁻¹' G)
              ≤ ν ((fun (y : PrivateIndex L → SU2) i => y i * h i) ⁻¹' A) := by
                apply measure_mono
                intro y hy
                have hy' : wilsonAction 1 (privateAct y U) < δ := hy
                show ∑ i, linkDefect (y i * h i) < δ
                calc ∑ i, linkDefect (y i * h i)
                    = ∑ i, plaquetteAction (privateAct y U) (privatePlaquette i) := by
                      refine Finset.sum_congr rfl fun i _ => ?_
                      rw [plaquetteAction_eq_linkDefect, plaquetteHolonomy_privateAct]
                  _ ≤ wilsonAction 1 (privateAct y U) := sum_privatePlaquette_le_wilsonAction _
                  _ < δ := hy'
            _ = ν A := hmp.measure_preimage hA.nullMeasurableSet
      _ = ν A := by rw [lintegral_const, measure_univ, mul_one]
  have h3 : μ E ≤ ν A := h1 ▸ h2
  exact ENNReal.toReal_mono (measure_ne_top _ _) h3

/-- Union bound for `m` independent Haar links: a total defect below `δ` forces more than half of
the defects below `2 δ / m`. -/
theorem pi_sum_linkDefect_lt_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hm : 0 < Fintype.card ι) {δ : ℝ} (hδ : 0 < δ) :
    (Measure.pi fun _ : ι => SU2.haarProbability).real {z | ∑ i, linkDefect (z i) < δ} ≤
      2 ^ Fintype.card ι *
        singleLinkMass (2 * δ / Fintype.card ι) ^ (Fintype.card ι / 2 + 1) := by
  set m := Fintype.card ι with hm_def
  set η := 2 * δ / m with hη_def
  set ν := Measure.pi fun _ : ι => SU2.haarProbability with hν
  set B : Finset ι → Set (ι → SU2) := fun T =>
    Set.univ.pi fun i => if i ∈ T then linkNeighbourhood η else Set.univ with hB_def
  set S : Finset (Finset ι) := Finset.univ.filter fun T => m < 2 * T.card with hS_def
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcover : {z : ι → SU2 | ∑ i, linkDefect (z i) < δ} ⊆ ⋃ T ∈ S, B T := by
    intro z hz
    have hz' : ∑ i, linkDefect (z i) < δ := hz
    set T := Finset.univ.filter fun i => linkDefect (z i) < η with hT_def
    set Tc := Finset.univ.filter fun i => ¬ linkDefect (z i) < η with hTc_def
    refine Set.mem_biUnion (x := T) ?_ ?_
    · rw [Finset.mem_coe, hS_def, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hcon
      have hle : 2 * T.card ≤ m := not_lt.mp hcon
      have hcard : T.card + Tc.card = m :=
        Finset.card_filter_add_card_filter_not (s := Finset.univ) _
      have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i => linkDefect (z i) < η) (fun i => linkDefect (z i))
      have hT0 : 0 ≤ ∑ i ∈ T, linkDefect (z i) := Finset.sum_nonneg fun i _ => linkDefect_nonneg _
      have hTc : Tc.card • η ≤ ∑ i ∈ Tc, linkDefect (z i) :=
        Finset.card_nsmul_le_sum Tc (fun i => linkDefect (z i)) η
          fun i hi => not_lt.mp (Finset.mem_filter.mp hi).2
      rw [nsmul_eq_mul] at hTc
      have hcardR : (T.card : ℝ) + Tc.card = m := by exact_mod_cast hcard
      have hleR : 2 * (T.card : ℝ) ≤ m := by exact_mod_cast hle
      have hηδ : δ ≤ (Tc.card : ℝ) * η := by
        rw [hη_def]
        have hhalf : (m : ℝ) / 2 ≤ Tc.card := by linarith
        calc δ = (m : ℝ) / 2 * (2 * δ / m) := by field_simp
          _ ≤ (Tc.card : ℝ) * (2 * δ / m) := by
            apply mul_le_mul_of_nonneg_right hhalf
            positivity
      linarith
    · intro i _
      by_cases hi : i ∈ T
      · show z i ∈ (if i ∈ T then linkNeighbourhood η else Set.univ)
        simp only [hi, ↓reduceIte]
        exact (Finset.mem_filter.mp hi).2
      · show z i ∈ (if i ∈ T then linkNeighbourhood η else Set.univ)
        simp only [hi, ↓reduceIte]
        exact Set.mem_univ _
  have hB : ∀ T : Finset ι, ν.real (B T) = singleLinkMass η ^ T.card := by
    intro T
    simp only [hB_def, hν, Measure.real]
    rw [Measure.pi_pi]
    have hite : ∀ i, SU2.haarProbability (if i ∈ T then linkNeighbourhood η else Set.univ) =
        if i ∈ T then SU2.haarProbability (linkNeighbourhood η) else 1 := by
      intro i
      split_ifs <;> simp
    simp_rw [hite]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, ENNReal.toReal_pow]
    rfl
  calc ν.real {z | ∑ i, linkDefect (z i) < δ} ≤ ν.real (⋃ T ∈ S, B T) :=
        measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ T ∈ S, ν.real (B T) := measureReal_biUnion_finset_le S B
    _ ≤ ∑ _T ∈ S, singleLinkMass η ^ (m / 2 + 1) := by
        apply Finset.sum_le_sum
        intro T hT
        rw [hB]
        have hTc : m / 2 + 1 ≤ T.card := by
          have := (Finset.mem_filter.mp hT).2
          omega
        exact pow_le_pow_of_le_one (singleLinkMass_nonneg η) (singleLinkMass_le_one η) hTc
    _ = S.card * singleLinkMass η ^ (m / 2 + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ m * singleLinkMass η ^ (m / 2 + 1) := by
        have hpow : 0 ≤ singleLinkMass η ^ (m / 2 + 1) := pow_nonneg (singleLinkMass_nonneg η) _
        have h1 : S.card ≤ (Finset.univ : Finset (Finset ι)).card := Finset.card_filter_le _ _
        rw [Finset.card_univ, Fintype.card_finset] at h1
        have h1' : (S.card : ℝ) ≤ 2 ^ m := by exact_mod_cast h1
        exact mul_le_mul_of_nonneg_right h1' hpow

/-! ## Two-sided volume law for the vacuum sublevel mass -/

theorem privateCount_pos {L : ℕ} (hL : 2 ≤ L) : 0 < privateCount L := by
  unfold privateCount
  have : 1 ≤ L / 2 := by omega
  positivity

theorem le_privateCount {L : ℕ} (hL : 2 ≤ L) : L ≤ privateCount L := by
  unfold privateCount
  have h1 : 1 ≤ L / 2 := by omega
  calc L ≤ L ^ 3 := Nat.le_self_pow (by norm_num) L
    _ = L ^ 3 * 1 := (mul_one _).symm
    _ ≤ L ^ 3 * (L / 2) := Nat.mul_le_mul_left _ h1

/-- `L⁴ ≤ 4 m(L)` for `L ≥ 2`: the private plaquettes are a fixed fraction of the volume. -/
theorem pow_four_le_four_mul_privateCount {L : ℕ} (hL : 2 ≤ L) :
    L ^ 4 ≤ 4 * privateCount L := by
  unfold privateCount
  have h : L ≤ 4 * (L / 2) := by omega
  calc L ^ 4 = L ^ 3 * L := by ring
    _ ≤ L ^ 3 * (4 * (L / 2)) := Nat.mul_le_mul_left _ h
    _ = 4 * (L ^ 3 * (L / 2)) := by ring

/-- Upper bound `c(L, δ) ≤ 2^m c₁(2δ / m)^(⌊m/2⌋ + 1)` with `m = m(L)` private plaquettes. -/
theorem haarVacuumSublevelMass_le (L : ℕ) [NeZero L] (hL : 2 ≤ L) {δ : ℝ} (hδ : 0 < δ) :
    haarVacuumSublevelMass L δ ≤ 2 ^ privateCount L *
      singleLinkMass (2 * δ / privateCount L) ^ (privateCount L / 2 + 1) := by
  have hm : 0 < Fintype.card (PrivateIndex L) := by
    rw [card_privateIndex]
    exact privateCount_pos hL
  have h := pi_sum_linkDefect_lt_le (ι := PrivateIndex L) hm hδ
  rw [card_privateIndex] at h
  exact (haarVacuumSublevelMass_le_privateMass L δ).trans h

/-- Explicit upper bound `c(L, δ) ≤ 2^m (√(4δ / m))^(⌊m/2⌋ + 1)`. -/
theorem haarVacuumSublevelMass_le_sqrt (L : ℕ) [NeZero L] (hL : 2 ≤ L) {δ : ℝ} (hδ : 0 < δ) :
    haarVacuumSublevelMass L δ ≤ 2 ^ privateCount L *
      Real.sqrt (4 * δ / privateCount L) ^ (privateCount L / 2 + 1) := by
  have hmR : (0 : ℝ) < privateCount L := by exact_mod_cast privateCount_pos hL
  have hs := singleLinkMass_le_sqrt (η := 2 * δ / privateCount L) (by positivity)
  have he : 2 * (2 * δ / (privateCount L : ℝ)) = 4 * δ / privateCount L := by ring
  rw [he] at hs
  exact (haarVacuumSublevelMass_le L hL hδ).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (singleLinkMass_nonneg _) hs _) (by positivity))

/-- Logarithmic upper bound `log c(L, δ) ≤ m log 2 - (m / 4) log (m / (4δ))` once `4δ ≤ m`;
with `m(L) = L³ ⌊L/2⌋` the entropy cost `log (1 / c(L, δ))` grows at least like
`(L⁴ / 2) log L` up to `O(L⁴)`. -/
theorem log_haarVacuumSublevelMass_le (L : ℕ) [NeZero L] (hL : 2 ≤ L) {δ : ℝ} (hδ : 0 < δ)
    (hδm : 4 * δ ≤ privateCount L) :
    Real.log (haarVacuumSublevelMass L δ) ≤
      privateCount L * Real.log 2 -
        privateCount L / 4 * Real.log (privateCount L / (4 * δ)) := by
  set m := privateCount L with hm_def
  have hmR : (0 : ℝ) < m := by exact_mod_cast privateCount_pos hL
  have hc := haarVacuumSublevelMass_pos (L := L) hδ
  have hb := haarVacuumSublevelMass_le_sqrt L hL hδ
  have hq : 0 < 4 * δ / m := by positivity
  have hsq : 0 < Real.sqrt (4 * δ / m) := Real.sqrt_pos.mpr hq
  have hlog := Real.log_le_log hc hb
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_sqrt hq.le] at hlog
  have hneg : Real.log (4 * δ / m) ≤ 0 :=
    Real.log_nonpos hq.le ((div_le_one hmR).mpr hδm)
  have hk : (m : ℝ) / 2 ≤ ((m / 2 + 1 : ℕ) : ℝ) := by
    have h1 : m ≤ 2 * (m / 2 + 1) := by omega
    have h2 : (m : ℝ) ≤ 2 * ((m / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hinv : Real.log ((m : ℝ) / (4 * δ)) = -Real.log (4 * δ / m) := by
    rw [← Real.log_inv, inv_div]
  rw [hinv]
  have h3 : ((m / 2 + 1 : ℕ) : ℝ) * (Real.log (4 * δ / m) / 2) ≤
      (m / 2) * (Real.log (4 * δ / m) / 2) :=
    mul_le_mul_of_nonpos_right hk (by linarith)
  linarith

/-! ## Fixed total-action threshold: the coupling growth law -/

/-- The finite-volume weak-coupling bound `exp (-β (ε - δ)) / c(L, δ)` of
`haarWilsonMeasure_action_tail`. -/
def weakCouplingTailBound (L : ℕ) [NeZero L] (β ε δ : ℝ) : ℝ :=
  Real.exp (-(β * (ε - δ))) / haarVacuumSublevelMass L δ

theorem weakCouplingTailBound_eq (L : ℕ) [NeZero L] {β ε δ : ℝ} (hδ : 0 < δ) :
    weakCouplingTailBound L β ε δ =
      Real.exp (-(β * (ε - δ)) - Real.log (haarVacuumSublevelMass L δ)) := by
  rw [weakCouplingTailBound, Real.exp_sub, Real.exp_log (haarVacuumSublevelMass_pos hδ)]

/-- Sufficient side: `exp (-β(ε - δ)) / c(L, δ) ≤ exp (-(β (ε - δ) - 8 L⁴ log (2400 L⁴ / δ)))`
for every `L` with `δ ≤ 96 L⁴`. -/
theorem weakCouplingTailBound_le (L : ℕ) [NeZero L] {β ε δ : ℝ} (hδ : 0 < δ)
    (hδL : δ ≤ 96 * (L : ℝ) ^ 4) :
    weakCouplingTailBound L β ε δ ≤
      Real.exp (-(β * (ε - δ) - 8 * (L : ℝ) ^ 4 * Real.log (2400 * (L : ℝ) ^ 4 / δ))) := by
  rw [weakCouplingTailBound_eq L hδ]
  apply Real.exp_le_exp.mpr
  have := log_haarVacuumSublevelMass_ge L hδ hδL
  linarith

/-- Necessary side: for `L ≥ 2` and `4δ ≤ m(L)`,
`exp (-β (ε - δ) + (m / 4) log (m / (4δ)) - m log 2) ≤ exp (-β(ε - δ)) / c(L, δ)`. -/
theorem le_weakCouplingTailBound (L : ℕ) [NeZero L] (hL : 2 ≤ L) {β ε δ : ℝ} (hδ : 0 < δ)
    (hδm : 4 * δ ≤ privateCount L) :
    Real.exp (-(β * (ε - δ)) + privateCount L / 4 * Real.log (privateCount L / (4 * δ)) -
        privateCount L * Real.log 2) ≤ weakCouplingTailBound L β ε δ := by
  rw [weakCouplingTailBound_eq L hδ]
  apply Real.exp_le_exp.mpr
  have := log_haarVacuumSublevelMass_le L hL hδ hδm
  linarith

/-- Explicit tail bound at fixed total threshold, valid for every `L` with `δ ≤ 96 L⁴`. -/
theorem haarWilsonMeasure_action_tail_le_explicit {L : ℕ} [NeZero L] {β δ ε : ℝ} (hβ : 0 ≤ β)
    (hδ : 0 < δ) (hδL : δ ≤ 96 * (L : ℝ) ^ 4) :
    (wilsonMeasure (gaugeHaarMeasure L) β).real {U | ε ≤ wilsonAction 1 U} ≤
      Real.exp (-(β * (ε - δ) - 8 * (L : ℝ) ^ 4 * Real.log (2400 * (L : ℝ) ^ 4 / δ))) :=
  (haarWilsonMeasure_action_tail hβ hδ).trans (weakCouplingTailBound_le L hδ hδL)

/-- Concentration along varying volumes at a fixed total threshold. Quantifier order: fix
`0 < δ ≤ 96` and `ε`; then any sizes and couplings whose gain
`β (ε - δ) - 8 L⁴ log (2400 L⁴ / δ)` diverges send the bound and the action tail to zero. -/
theorem haarWilsonMeasure_action_tail_tendsto_of_gain {ε δ : ℝ} (hδ : 0 < δ) (hδ96 : δ ≤ 96)
    (sizes : ℕ → ℕ) [∀ n, NeZero (sizes n)] (β : ℕ → ℝ) (hβ : ∀ n, 0 ≤ β n)
    (hgain : Tendsto (fun n => β n * (ε - δ) -
      8 * (sizes n : ℝ) ^ 4 * Real.log (2400 * (sizes n : ℝ) ^ 4 / δ)) atTop atTop) :
    Tendsto (fun n => weakCouplingTailBound (sizes n) (β n) ε δ) atTop (𝓝 0) ∧
    Tendsto (fun n => (wilsonMeasure (gaugeHaarMeasure (sizes n)) (β n)).real
      {U | ε ≤ wilsonAction 1 U}) atTop (𝓝 0) := by
  have hδL : ∀ n, δ ≤ 96 * (sizes n : ℝ) ^ 4 := fun n => by
    have h1 : (1 : ℝ) ≤ sizes n := by exact_mod_cast (NeZero.one_le : 1 ≤ sizes n)
    have h2 : (1 : ℝ) ≤ (sizes n : ℝ) ^ 4 := one_le_pow₀ h1
    linarith
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hgain
  have hbound : Tendsto (fun n => weakCouplingTailBound (sizes n) (β n) ε δ) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun n =>
        div_nonneg (Real.exp_pos _).le (haarVacuumSublevelMass_pos hδ).le)
      (Filter.Eventually.of_forall fun n => weakCouplingTailBound_le (sizes n) hδ (hδL n)) hexp
  refine ⟨hbound, ?_⟩
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
    (Filter.Eventually.of_forall fun n => haarWilsonMeasure_action_tail (hβ n) hδ) hbound

/-- The explicit coupling schedule `β(L) = (8 L⁴ log (2400 L⁴ / δ) + g(L)) / (ε - δ)` with any
`g ≥ 0` tending to infinity drives the actual Haar–Wilson action tail to zero along `L → ∞`
(`L = n + 1`). Quantifier order: `ε`, then `δ < ε` with `δ ≤ 96`, then `g`, then `L`. -/
theorem haarWilsonMeasure_action_tail_tendsto_schedule {ε δ : ℝ} (hδ : 0 < δ) (hδε : δ < ε)
    (hδ96 : δ ≤ 96) (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hg : Tendsto g atTop atTop) :
    Tendsto (fun n : ℕ => (wilsonMeasure (gaugeHaarMeasure (n + 1))
      ((8 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.log (2400 * ((n + 1 : ℕ) : ℝ) ^ 4 / δ) + g n) /
        (ε - δ))).real {U | ε ≤ wilsonAction 1 U}) atTop (𝓝 0) := by
  have hεδ : 0 < ε - δ := sub_pos.mpr hδε
  have hβ : ∀ n : ℕ, 0 ≤ (8 * ((n + 1 : ℕ) : ℝ) ^ 4 *
      Real.log (2400 * ((n + 1 : ℕ) : ℝ) ^ 4 / δ) + g n) / (ε - δ) := by
    intro n
    have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have h2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 4 := one_le_pow₀ h1
    have h3 : 1 ≤ 2400 * ((n + 1 : ℕ) : ℝ) ^ 4 / δ := by
      rw [le_div_iff₀ hδ]
      nlinarith
    have h4 : 0 ≤ Real.log (2400 * ((n + 1 : ℕ) : ℝ) ^ 4 / δ) := Real.log_nonneg h3
    have h5 : 0 ≤ 8 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.log (2400 * ((n + 1 : ℕ) : ℝ) ^ 4 / δ) := by
      positivity
    exact div_nonneg (by linarith [hg0 n]) hεδ.le
  have hgain : Tendsto (fun n : ℕ => (8 * ((n + 1 : ℕ) : ℝ) ^ 4 *
      Real.log (2400 * ((n + 1 : ℕ) : ℝ) ^ 4 / δ) + g n) / (ε - δ) * (ε - δ) -
      8 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.log (2400 * ((n + 1 : ℕ) : ℝ) ^ 4 / δ)) atTop atTop := by
    refine hg.congr fun n => ?_
    field_simp
    ring
  exact (haarWilsonMeasure_action_tail_tendsto_of_gain hδ hδ96 (fun n => n + 1) _ hβ hgain).2

/-- Linear coupling growth is not enough for this bound: if `β(L) ≤ C L⁴` along volumes
`L → ∞`, then `exp (-β (ε - δ)) / c(L, δ) → ∞` for every `δ ≤ ε`. The sharper
`weakCouplingTailBound_tendsto_atTop_of_le_log` replaces `C L⁴` by `κ L⁴ log L` with `κ < 1/4`. -/
theorem weakCouplingTailBound_tendsto_atTop_of_le_linear {ε δ C : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε)
    (sizes : ℕ → ℕ) [∀ n, NeZero (sizes n)] (hsizes : Tendsto sizes atTop atTop)
    (β : ℕ → ℝ) (hβ : ∀ n, β n ≤ C * (sizes n : ℝ) ^ 4) :
    Tendsto (fun n => weakCouplingTailBound (sizes n) (β n) ε δ) atTop atTop := by
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hεδ : 0 ≤ ε - δ := sub_nonneg.mpr hδε
  have hm : Tendsto (fun n => (privateCount (sizes n) : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun n => (sizes n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hsizes
    apply tendsto_atTop_mono' atTop _ h1
    filter_upwards [hsizes.eventually (eventually_ge_atTop 2)] with n hn
    exact_mod_cast le_privateCount hn
  set K := Real.log 2 + 4 * C' * (ε - δ) with hK
  have hbr : Tendsto (fun n => 1 / 4 * Real.log ((privateCount (sizes n) : ℝ) / (4 * δ)) + -K)
      atTop atTop := by
    have hl := Real.tendsto_log_atTop.comp (hm.atTop_div_const (by positivity : (0 : ℝ) < 4 * δ))
    exact tendsto_atTop_add_const_right _ _ (hl.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 4))
  have hexp := Real.tendsto_exp_atTop.comp (hm.atTop_mul_atTop₀ hbr)
  apply tendsto_atTop_mono' atTop _ hexp
  filter_upwards [hsizes.eventually (eventually_ge_atTop 2),
    hm.eventually (eventually_ge_atTop (4 * δ))] with n hn hmn
  set L := sizes n
  set m := privateCount L
  have hlow := le_weakCouplingTailBound L hn (β := β n) (ε := ε) hδ hmn
  refine le_trans (Real.exp_le_exp.mpr ?_) hlow
  have hL4 : (L : ℝ) ^ 4 ≤ 4 * m := by exact_mod_cast pow_four_le_four_mul_privateCount hn
  have hβC : β n * (ε - δ) ≤ C' * (L : ℝ) ^ 4 * (ε - δ) := by
    have h1 : β n ≤ C' * (L : ℝ) ^ 4 :=
      (hβ n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    exact mul_le_mul_of_nonneg_right h1 hεδ
  have hCm : C' * (L : ℝ) ^ 4 * (ε - δ) ≤ C' * (4 * m) * (ε - δ) := by
    apply mul_le_mul_of_nonneg_right _ hεδ
    exact mul_le_mul_of_nonneg_left hL4 hC'0
  nlinarith

theorem privateCount_mul_two_le (L : ℕ) : 2 * privateCount L ≤ L ^ 4 := by
  unfold privateCount
  have h : 2 * (L / 2) ≤ L := Nat.mul_div_le L 2
  calc 2 * (L ^ 3 * (L / 2)) = L ^ 3 * (2 * (L / 2)) := by ring
    _ ≤ L ^ 3 * L := Nat.mul_le_mul_left _ h
    _ = L ^ 4 := by ring

/-- Exact criterion: along any sequence of tori the bound `exp (-β (ε - δ)) / c(L, δ)` tends to
zero if and only if the gain `β (ε - δ) + log c(L, δ)` tends to infinity. The two preceding
estimates sandwich `log (1 / c(L, δ))` between `(m / 4) log (m / (4δ)) - m log 2` and
`8 L⁴ log (2400 L⁴ / δ)`. -/
theorem weakCouplingTailBound_tendsto_zero_iff {ε δ : ℝ} (hδ : 0 < δ)
    (sizes : ℕ → ℕ) [∀ n, NeZero (sizes n)] (β : ℕ → ℝ) :
    Tendsto (fun n => weakCouplingTailBound (sizes n) (β n) ε δ) atTop (𝓝 0) ↔
      Tendsto (fun n => β n * (ε - δ) + Real.log (haarVacuumSublevelMass (sizes n) δ))
        atTop atTop := by
  have he : ∀ n, weakCouplingTailBound (sizes n) (β n) ε δ =
      Real.exp (-(β n * (ε - δ)) - Real.log (haarVacuumSublevelMass (sizes n) δ)) :=
    fun n => weakCouplingTailBound_eq (sizes n) hδ
  simp_rw [he]
  rw [Real.tendsto_exp_comp_nhds_zero, ← tendsto_neg_atTop_iff]
  exact tendsto_congr fun n => by ring

/-- Sharp-order necessity: if eventually `β(L) (ε - δ) ≤ κ L⁴ log L` with `κ < 1/4` along volumes
`L → ∞`, then `exp (-β (ε - δ)) / c(L, δ) → ∞`. Hence the bound can tend to zero only if
`β(L) (ε - δ) > κ L⁴ log L` infinitely often for every `κ < 1/4`, while
`haarWilsonMeasure_action_tail_tendsto_schedule` shows that `8 L⁴ log (2400 L⁴ / δ) + g(L)`
(leading order `32 L⁴ log L`) suffices: the required growth is of order `N(L) log N(L)`. -/
theorem weakCouplingTailBound_tendsto_atTop_of_le_log {ε δ κ : ℝ} (hδ : 0 < δ) (hκ : κ < 1 / 4)
    (sizes : ℕ → ℕ) [∀ n, NeZero (sizes n)] (hsizes : Tendsto sizes atTop atTop)
    (β : ℕ → ℝ)
    (hβ : ∀ᶠ n in atTop, β n * (ε - δ) ≤ κ * (sizes n : ℝ) ^ 4 * Real.log (sizes n)) :
    Tendsto (fun n => weakCouplingTailBound (sizes n) (β n) ε δ) atTop atTop := by
  have hx : Tendsto (fun n => (sizes n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes
  have hx4 : Tendsto (fun n => (sizes n : ℝ) ^ 4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp hx
  set K := Real.log (16 * δ) / 16 + Real.log 2 / 2 with hK
  have hbr : Tendsto (fun n => (1 / 4 - κ) * Real.log (sizes n) + -K) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      ((Real.tendsto_log_atTop.comp hx).const_mul_atTop (by linarith))
  have hexp := Real.tendsto_exp_atTop.comp (hx4.atTop_mul_atTop₀ hbr)
  apply tendsto_atTop_mono' atTop _ hexp
  filter_upwards [hsizes.eventually (eventually_ge_atTop 2),
    hx4.eventually (eventually_ge_atTop (16 * δ)), hβ] with n hn hL16 hβn
  set L := sizes n
  set m := privateCount L
  have hm4 : (L : ℝ) ^ 4 ≤ 4 * m := by exact_mod_cast pow_four_le_four_mul_privateCount hn
  have hm2 : 2 * (m : ℝ) ≤ (L : ℝ) ^ 4 := by exact_mod_cast privateCount_mul_two_le L
  have hδm : 4 * δ ≤ m := by nlinarith
  have hlow := le_weakCouplingTailBound L hn (β := β n) (ε := ε) hδ hδm
  refine le_trans (Real.exp_le_exp.mpr ?_) hlow
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hq : 1 ≤ (L : ℝ) ^ 4 / (16 * δ) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hlogq : 0 ≤ Real.log ((L : ℝ) ^ 4 / (16 * δ)) := Real.log_nonneg hq
  have hmono : Real.log ((L : ℝ) ^ 4 / (16 * δ)) ≤ Real.log ((m : ℝ) / (4 * δ)) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsplit : Real.log ((L : ℝ) ^ 4 / (16 * δ)) = 4 * Real.log L - Real.log (16 * δ) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hprod : (L : ℝ) ^ 4 / 16 * Real.log ((L : ℝ) ^ 4 / (16 * δ)) ≤
      (m : ℝ) / 4 * Real.log ((m : ℝ) / (4 * δ)) := by
    calc (L : ℝ) ^ 4 / 16 * Real.log ((L : ℝ) ^ 4 / (16 * δ))
        ≤ (L : ℝ) ^ 4 / 16 * Real.log ((m : ℝ) / (4 * δ)) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ ≤ (m : ℝ) / 4 * Real.log ((m : ℝ) / (4 * δ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (hlogq.trans hmono)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hm2' : (m : ℝ) * Real.log 2 ≤ (L : ℝ) ^ 4 / 2 * Real.log 2 :=
    mul_le_mul_of_nonneg_right (by linarith) hlog2
  rw [hsplit] at hprod
  nlinarith

/-! ## The actual action tail at a fixed threshold: a power-law necessary growth -/

/-- The small-action probability of the actual Wilson law is at most `c(L, ε) / Z_β`. -/
theorem haarWilsonMeasure_sublevel_le_div {L : ℕ} [NeZero L] {β ε : ℝ} (hβ : 0 ≤ β) :
    (wilsonMeasure (gaugeHaarMeasure L) β).real {U | wilsonAction 1 U < ε} ≤
      haarVacuumSublevelMass L ε / wilsonPartition (gaugeHaarMeasure L) β := by
  have hA : MeasurableSet {U : GaugeConfig L | wilsonAction 1 U < ε} :=
    measurableSet_lt (measurable_wilsonAction 1) measurable_const
  have hi := wilsonWeight_integrable (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)
  have hZ := wilsonPartition_pos (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)
  have hnum : (∫ U in {U : GaugeConfig L | wilsonAction 1 U < ε},
      boltzmannWeight β U ∂gaugeHaarMeasure L) ≤ haarVacuumSublevelMass L ε := by
    calc _ ≤ ∫ _ in {U : GaugeConfig L | wilsonAction 1 U < ε}, (1 : ℝ) ∂gaugeHaarMeasure L :=
          setIntegral_mono_on hi.integrableOn (integrable_const _) hA
            fun U _ => (boltzmannWeight_bounds hβ U).2.2
      _ = haarVacuumSublevelMass L ε := by
          rw [setIntegral_const, smul_eq_mul, mul_one]
          rfl
  rw [haarWilsonMeasure_real_eq hβ hA]
  exact div_le_div_of_nonneg_right hnum hZ.le

/-- The small-action probability of the actual Wilson law is at most `c(L, ε) exp (12 β L⁴)`,
because the partition function is at least `exp (-12 β L⁴)`. -/
theorem haarWilsonMeasure_sublevel_le {L : ℕ} [NeZero L] {β ε : ℝ} (hβ : 0 ≤ β) :
    (wilsonMeasure (gaugeHaarMeasure L) β).real {U | wilsonAction 1 U < ε} ≤
      haarVacuumSublevelMass L ε * Real.exp (12 * β * (L : ℝ) ^ 4) := by
  have hZlow := (wilsonPartition_bounds (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)).1
  have hcard : (Fintype.card (Plaquette L) : ℝ) = 6 * (L : ℝ) ^ 4 := by
    exact_mod_cast card_plaquette_eq_six_mul_pow_four L
  rw [hcard] at hZlow
  calc _ ≤ haarVacuumSublevelMass L ε / wilsonPartition (gaugeHaarMeasure L) β :=
        haarWilsonMeasure_sublevel_le_div hβ
    _ ≤ haarVacuumSublevelMass L ε / Real.exp (-(2 * β * (6 * (L : ℝ) ^ 4))) :=
        div_le_div_of_nonneg_left measureReal_nonneg (Real.exp_pos _) hZlow
    _ = _ := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        congr 2
        ring

/-- Partition-function lower bound from the explicit link box at scale `1 / (96 (β + 1))`:
`log Z_β ≥ -(8 L⁴ log (2400 (β + 1)) + L⁴)` for every `β ≥ 0`. -/
theorem log_wilsonPartition_ge (L : ℕ) [NeZero L] {β : ℝ} (hβ : 0 ≤ β) :
    -(8 * (L : ℝ) ^ 4 * Real.log (2400 * (β + 1)) + (L : ℝ) ^ 4) ≤
      Real.log (wilsonPartition (gaugeHaarMeasure L) β) := by
  have hV : 0 < (L : ℝ) ^ 4 := pow_pos (Nat.cast_pos.mpr (NeZero.pos L)) _
  set η : ℝ := 1 / (96 * (β + 1)) with hη_def
  have hη : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη_def, div_le_one (by positivity)]
    linarith
  have hZ := wilsonPartition_pos (gaugeHaarMeasure L) hβ (measurable_wilsonAction β)
  have hlow := haarWilsonPartition_sublevel_lower (L := L) (δ := 6 * (L : ℝ) ^ 4 * (16 * η)) hβ
  have hbox := singleLinkMass_pow_le_haarVacuumSublevelMass L η
  have hm := singleLinkMass_ge hη hη1
  have hpow : (η ^ 2 / 625) ^ (4 * L ^ 4) ≤ singleLinkMass η ^ (4 * L ^ 4) :=
    pow_le_pow_left₀ (by positivity) hm _
  have hchain : (η ^ 2 / 625) ^ (4 * L ^ 4) * Real.exp (-(β * (6 * (L : ℝ) ^ 4 * (16 * η)))) ≤
      wilsonPartition (gaugeHaarMeasure L) β :=
    le_trans (mul_le_mul_of_nonneg_right (hpow.trans hbox) (Real.exp_pos _).le) hlow
  have hpos : 0 < (η ^ 2 / 625) ^ (4 * L ^ 4) * Real.exp (-(β * (6 * (L : ℝ) ^ 4 * (16 * η)))) := by
    positivity
  have hlog := Real.log_le_log hpos hchain
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow,
    Real.log_div (by positivity) (by norm_num), Real.log_pow] at hlog
  have hηlog : Real.log η = -Real.log (96 * (β + 1)) := by
    rw [hη_def, one_div, Real.log_inv]
  have h625 : Real.log (625 : ℝ) = 2 * Real.log 25 := by
    rw [show (625 : ℝ) = 25 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hsplit : Real.log (2400 * (β + 1)) = Real.log 25 + Real.log (96 * (β + 1)) := by
    rw [show (2400 : ℝ) * (β + 1) = 25 * (96 * (β + 1)) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  have hβη : β * (6 * (L : ℝ) ^ 4 * (16 * η)) ≤ (L : ℝ) ^ 4 := by
    have he : β * (6 * (L : ℝ) ^ 4 * (16 * η)) = (L : ℝ) ^ 4 * (β / (β + 1)) := by
      rw [hη_def]
      field_simp
      ring
    rw [he]
    have hfrac : β / (β + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    nlinarith
  rw [hηlog, h625] at hlog
  push_cast at hlog
  nlinarith

/-- Power-law necessity for the actual Wilson law at a fixed total threshold `ε`: if eventually
`2400 (β(L) + 1) ≤ L^a` with `a < 1/32`, then `P_β(L)(S ≥ ε) → 1` as `L → ∞`. Concentration at a
fixed total threshold therefore needs `β(L)` to exceed a positive power of `L` infinitely often;
the sufficient schedule of `haarWilsonMeasure_action_tail_tendsto_schedule` grows like
`L⁴ log L`. -/
theorem haarWilsonMeasure_action_tail_tendsto_one_of_le_rpow {ε a : ℝ} (hε : 0 < ε)
    (ha : a < 1 / 32) (sizes : ℕ → ℕ) [∀ n, NeZero (sizes n)]
    (hsizes : Tendsto sizes atTop atTop) (β : ℕ → ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ : ∀ᶠ n in atTop, 2400 * (β n + 1) ≤ (sizes n : ℝ) ^ a) :
    Tendsto (fun n => (wilsonMeasure (gaugeHaarMeasure (sizes n)) (β n)).real
      {U | ε ≤ wilsonAction 1 U}) atTop (𝓝 1) := by
  have hcompl : ∀ n, (wilsonMeasure (gaugeHaarMeasure (sizes n)) (β n)).real
      {U | ε ≤ wilsonAction 1 U} =
        1 - (wilsonMeasure (gaugeHaarMeasure (sizes n)) (β n)).real
          {U | wilsonAction 1 U < ε} := by
    intro n
    have := wilsonMeasure_isProbabilityMeasure (gaugeHaarMeasure (sizes n)) (hβ0 n)
      (measurable_wilsonAction (β n))
    have hA : MeasurableSet {U : GaugeConfig (sizes n) | wilsonAction 1 U < ε} :=
      measurableSet_lt (measurable_wilsonAction 1) measurable_const
    have hset : {U : GaugeConfig (sizes n) | ε ≤ wilsonAction 1 U} =
        {U | wilsonAction 1 U < ε}ᶜ := by
      ext U
      simp [not_lt]
    rw [hset, measureReal_compl hA, probReal_univ]
  have hx : Tendsto (fun n => (sizes n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes
  have hx4 : Tendsto (fun n => (sizes n : ℝ) ^ 4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp hx
  set K := Real.log (16 * ε) / 16 + Real.log 2 / 2 + 1 with hK
  have hbr : Tendsto (fun n => (1 / 4 - 8 * a) * Real.log (sizes n) + -K) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      ((Real.tendsto_log_atTop.comp hx).const_mul_atTop (by linarith))
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hx4.atTop_mul_atTop₀ hbr)
  have hsmall : Tendsto (fun n => (wilsonMeasure (gaugeHaarMeasure (sizes n)) (β n)).real
      {U | wilsonAction 1 U < ε}) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) ?_ hexp
    filter_upwards [hsizes.eventually (eventually_ge_atTop 2),
      hx4.eventually (eventually_ge_atTop (16 * ε)), hβ] with n hn hL16 hβn
    set L := sizes n
    set m := privateCount L
    have hm4 : (L : ℝ) ^ 4 ≤ 4 * m := by exact_mod_cast pow_four_le_four_mul_privateCount hn
    have hm2 : 2 * (m : ℝ) ≤ (L : ℝ) ^ 4 := by exact_mod_cast privateCount_mul_two_le L
    have hεm : 4 * ε ≤ m := by nlinarith
    have hc := haarVacuumSublevelMass_pos (L := L) hε
    have hZ := wilsonPartition_pos (gaugeHaarMeasure L) (hβ0 n) (measurable_wilsonAction (β n))
    have hup := log_haarVacuumSublevelMass_le L hn hε hεm
    have hZlow := log_wilsonPartition_ge L (hβ0 n)
    have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have hq : 1 ≤ (L : ℝ) ^ 4 / (16 * ε) := (le_div_iff₀ (by positivity)).mpr (by linarith)
    have hlogq : 0 ≤ Real.log ((L : ℝ) ^ 4 / (16 * ε)) := Real.log_nonneg hq
    have hmono : Real.log ((L : ℝ) ^ 4 / (16 * ε)) ≤ Real.log ((m : ℝ) / (4 * ε)) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hsplit : Real.log ((L : ℝ) ^ 4 / (16 * ε)) = 4 * Real.log L - Real.log (16 * ε) := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
      push_cast
      ring
    have hprod : (L : ℝ) ^ 4 / 16 * Real.log ((L : ℝ) ^ 4 / (16 * ε)) ≤
        (m : ℝ) / 4 * Real.log ((m : ℝ) / (4 * ε)) := by
      calc (L : ℝ) ^ 4 / 16 * Real.log ((L : ℝ) ^ 4 / (16 * ε))
          ≤ (L : ℝ) ^ 4 / 16 * Real.log ((m : ℝ) / (4 * ε)) :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
        _ ≤ (m : ℝ) / 4 * Real.log ((m : ℝ) / (4 * ε)) :=
            mul_le_mul_of_nonneg_right (by linarith) (hlogq.trans hmono)
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hm2' : (m : ℝ) * Real.log 2 ≤ (L : ℝ) ^ 4 / 2 * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hlog2
    have hβlog : Real.log (2400 * (β n + 1)) ≤ a * Real.log L := by
      rw [← Real.log_rpow hLpos]
      exact Real.log_le_log (by linarith [hβ0 n]) hβn
    have hβL : 8 * (L : ℝ) ^ 4 * Real.log (2400 * (β n + 1)) ≤
        8 * (L : ℝ) ^ 4 * (a * Real.log L) :=
      mul_le_mul_of_nonneg_left hβlog (by positivity)
    rw [hsplit] at hprod
    refine (haarWilsonMeasure_sublevel_le_div (hβ0 n)).trans ?_
    rw [← Real.exp_log hc, ← Real.exp_log hZ, ← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub hsmall
  rw [sub_zero] at hlim
  exact hlim.congr fun n => (hcompl n).symm

/-- At any fixed coupling the fixed-threshold action tail of the actual Wilson law tends to one
as the volume grows. -/
theorem haarWilsonMeasure_action_tail_tendsto_one_fixed_coupling {ε β : ℝ} (hε : 0 < ε)
    (hβ : 0 ≤ β) :
    Tendsto (fun n : ℕ => (wilsonMeasure (gaugeHaarMeasure (n + 1)) β).real
      {U | ε ≤ wilsonAction 1 U}) atTop (𝓝 1) := by
  have hpow : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (1 / 64 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  exact haarWilsonMeasure_action_tail_tendsto_one_of_le_rpow hε (by norm_num) (fun n => n + 1)
    (tendsto_add_atTop_nat 1) (fun _ => β) (fun _ => hβ)
    (hpow.eventually (eventually_ge_atTop (2400 * (β + 1))))

/-! ## Density thresholds: an explicit volume-uniform coupling -/

/-- Explicit density tail bound: for `0 < δ ≤ 96`,
`P(S ≥ ε L⁴) ≤ exp (-L⁴ (β (ε - δ) - 8 log (2400 / δ)))` on every torus. -/
theorem haarWilsonMeasure_density_tail_le_explicit {L : ℕ} [NeZero L] {β δ ε : ℝ} (hβ : 0 ≤ β)
    (hδ : 0 < δ) (hδ96 : δ ≤ 96) :
    (wilsonMeasure (gaugeHaarMeasure L) β).real {U | ε * (L : ℝ) ^ 4 ≤ wilsonAction 1 U} ≤
      Real.exp (-((L : ℝ) ^ 4 * (β * (ε - δ) - 8 * Real.log (2400 / δ)))) := by
  have hV : 0 < (L : ℝ) ^ 4 := pow_pos (Nat.cast_pos.mpr (NeZero.pos L)) _
  have hm := haarVacuumSublevelMass_density_ge L (δ := δ / 6) (by positivity) (by linarith)
  have he1 : 6 * (L : ℝ) ^ 4 * (δ / 6) = δ * (L : ℝ) ^ 4 := by ring
  rw [he1] at hm
  have hpos : 0 < ((δ / 6 / 400) ^ 2) ^ (4 * L ^ 4) := by positivity
  have hc := haarVacuumSublevelMass_pos (L := L) (mul_pos hδ hV)
  have hlog := Real.log_le_log hpos hm
  rw [Real.log_pow, Real.log_pow] at hlog
  have hinv : Real.log (δ / 6 / 400) = -Real.log (2400 / δ) := by
    rw [← Real.log_inv, inv_div, div_div]
    norm_num
  rw [hinv] at hlog
  push_cast at hlog
  calc _ ≤ Real.exp (-(β * (ε * (L : ℝ) ^ 4 - δ * (L : ℝ) ^ 4))) /
        haarVacuumSublevelMass L (δ * (L : ℝ) ^ 4) :=
      haarWilsonMeasure_action_tail hβ (mul_pos hδ hV)
    _ = Real.exp (-(β * (ε * (L : ℝ) ^ 4 - δ * (L : ℝ) ^ 4)) -
        Real.log (haarVacuumSublevelMass L (δ * (L : ℝ) ^ 4))) := by
      rw [Real.exp_sub, Real.exp_log hc]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- Explicit volume-uniform coupling threshold for action densities. Quantifier order: fix
`0 < δ < ε` with `δ ≤ 96`; fix any `β > 8 log (2400 / δ) / (ε - δ)`; then for every torus the tail
is at most `exp (-(β (ε - δ) - 8 log (2400 / δ)))`, and it tends to zero as `L → ∞` at this fixed
`β`. -/
theorem haarWilsonMeasure_density_tail_uniform_explicit {ε δ β : ℝ} (hδ : 0 < δ) (hδε : δ < ε)
    (hδ96 : δ ≤ 96) (hβ : 8 * Real.log (2400 / δ) / (ε - δ) < β) :
    (∀ (L : ℕ) [NeZero L], (wilsonMeasure (gaugeHaarMeasure L) β).real
      {U | ε * (L : ℝ) ^ 4 ≤ wilsonAction 1 U} ≤
        Real.exp (-(β * (ε - δ) - 8 * Real.log (2400 / δ)))) ∧
    Tendsto (fun n : ℕ => (wilsonMeasure (gaugeHaarMeasure (n + 1)) β).real
      {U | ε * ((n + 1 : ℕ) : ℝ) ^ 4 ≤ wilsonAction 1 U}) atTop (𝓝 0) := by
  have hεδ : 0 < ε - δ := sub_pos.mpr hδε
  have hlog0 : 0 ≤ Real.log (2400 / δ) :=
    Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith))
  have hgap : 0 < β * (ε - δ) - 8 * Real.log (2400 / δ) := by
    have := (div_lt_iff₀ hεδ).mp hβ
    linarith
  have hβ0 : 0 ≤ β := by
    have h1 : 0 ≤ 8 * Real.log (2400 / δ) / (ε - δ) := by positivity
    linarith
  refine ⟨fun L _ => ?_, ?_⟩
  · have h1 := haarWilsonMeasure_density_tail_le_explicit (L := L) (ε := ε) hβ0 hδ hδ96
    refine h1.trans (Real.exp_le_exp.mpr ?_)
    have hL : (1 : ℝ) ≤ L := by exact_mod_cast (NeZero.one_le : 1 ≤ L)
    have hV : (1 : ℝ) ≤ (L : ℝ) ^ 4 := one_le_pow₀ hL
    nlinarith
  · have hV : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 4) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hV.atTop_mul_const hgap)
    exact squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
      (Filter.Eventually.of_forall fun n =>
        haarWilsonMeasure_density_tail_le_explicit (L := n + 1) (ε := ε) hβ0 hδ hδ96) hexp

#assert_zfc_axioms

end JesseMath.Physics
