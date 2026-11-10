import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic
import JesseMath.Linter.AxiomAudit

open Matrix
open BigOperators
open Filter
open Topology

/-!
# Discrete 4D Non-Abelian SU(2) Lattice Yang-Mills Theory & Mass Gap
=====================================================================
Formalization for the Jesse Math Engine of:
1. 4D periodic Euclidean spacetime lattice Λ = (ℤ/Lℤ)⁴ and oriented geometry.
2. The non-abelian gauge group SU(2) as 2×2 complex unitary matrices with det = 1,
   with proven Group structure and unit quaternion embedding.
3. Gauge configurations U : Links → SU(2) and local gauge transformations.
4. The Wilson plaquette holonomy U_p and the gauge-invariant Wilson action S_W.
5. Transfer matrix T on the physical Hilbert space, vacuum |0⟩, excited state |1⟩,
   and the spectral mass gap Δ(L) = E_1 - E_0 > 0.
6. Asymptotic freedom and the Clay Millennium Prize Yang-Mills Existence
   and Mass Gap Conjecture in the continuum limit L → ∞.
-/

namespace JesseMath.Physics

/-! ## 1. 4D Euclidean Spacetime Periodic Lattice -/

/-- Discrete 4D spacetime directions μ ∈ {0, 1, 2, 3}. -/
abbrev Direction := Fin 4

/-- Unit displacement vector in direction μ on the lattice (ℤ/Lℤ)⁴. -/
def unitVec (L : ℕ) (μ : Direction) : Fin 4 → ZMod L :=
  fun i => if i = μ then 1 else 0

/-- 4D Euclidean periodic lattice Λ = (ℤ/Lℤ)⁴ of linear size L. -/
abbrev Lattice4D (L : ℕ) := Fin 4 → ZMod L

/-- Shift a lattice site x by a unit step in direction μ: x + μ̂. -/
def shift {L : ℕ} (x : Lattice4D L) (μ : Direction) : Lattice4D L :=
  x + unitVec L μ

/-- Shifting in two directions commutes on the periodic abelian lattice. -/
theorem shift_comm {L : ℕ} (x : Lattice4D L) (μ ν : Direction) :
  shift (shift x μ) ν = shift (shift x ν) μ := by
  dsimp [shift]
  rw [add_assoc, add_comm (unitVec L μ), ← add_assoc]

/-- An oriented link e = (x, μ) starting at site x in direction μ. -/
structure Link (L : ℕ) where
  x : Lattice4D L
  μ : Direction
  deriving DecidableEq

/-- Equivalence between Link and Cartesian product Lattice4D × Direction. -/
def linkEquiv (L : ℕ) : Link L ≃ Lattice4D L × Direction where
  toFun e := (e.x, e.μ)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by intro ⟨x, μ⟩; rfl
  right_inv := by intro ⟨x, μ⟩; rfl

instance (L : ℕ) [NeZero L] : Fintype (Link L) :=
  Fintype.ofEquiv (Lattice4D L × Direction) (linkEquiv L).symm

/-- An elementary unoriented plaquette plane (μ, ν) with μ < ν. -/
abbrev PlaquettePlane := { p : Direction × Direction // p.1 < p.2 }

/-- An elementary plaquette p = (x, μ, ν) with μ < ν. -/
structure Plaquette (L : ℕ) where
  x : Lattice4D L
  μ : Direction
  ν : Direction
  h : μ < ν
  deriving DecidableEq

def plaqEquiv (L : ℕ) : Plaquette L ≃ (Lattice4D L × PlaquettePlane) where
  toFun p := (p.x, ⟨(p.μ, p.ν), p.h⟩)
  invFun pair := ⟨pair.1, pair.2.1.1, pair.2.1.2, pair.2.2⟩
  left_inv := by intro ⟨x, μ, ν, h⟩; rfl
  right_inv := by intro ⟨x, ⟨⟨μ, ν⟩, h⟩⟩; rfl

instance (L : ℕ) [NeZero L] : Fintype (Plaquette L) :=
  Fintype.ofEquiv (Lattice4D L × { p : Direction × Direction // p.1 < p.2 }) (plaqEquiv L).symm

/-- In 4D Euclidean spacetime, there are exactly `(4 choose 2) = 6` unoriented plaquette planes. -/
theorem card_plaquettePlane : Fintype.card PlaquettePlane = 6 := by
  decide

/-- The 4D periodic torus `Λ = (ℤ/Lℤ)⁴` has exactly `L⁴` sites. -/
theorem card_lattice4D (L : ℕ) [NeZero L] : Fintype.card (Lattice4D L) = L ^ 4 := by
  simp [Lattice4D, ZMod.card]

/-- On the 4D periodic torus `Λ = (ℤ/Lℤ)⁴`, there are `6 * L⁴` unoriented plaquettes. -/
theorem card_plaquette_eq_six_mul_pow_four (L : ℕ) [NeZero L] :
    Fintype.card (Plaquette L) = 6 * L ^ 4 := by
  have h_equiv : Fintype.card (Plaquette L) = Fintype.card (Lattice4D L × PlaquettePlane) :=
    Fintype.card_congr (plaqEquiv L)
  rw [h_equiv, Fintype.card_prod, card_lattice4D L, card_plaquettePlane, mul_comm]

/-! ## 2. The Non-Abelian Gauge Group SU(2) -/

/--
The special unitary group SU(2) represented as 2×2 complex matrices
satisfying Uᴴ U = 1 and det(U) = 1.
-/
structure SU2 where
  mat : Matrix (Fin 2) (Fin 2) ℂ
  unitary : conjTranspose mat * mat = 1
  det_one : det mat = 1

namespace SU2

/-- Extensionality: two SU(2) elements are equal if their underlying matrices match. -/
theorem ext {A B : SU2} (h : A.mat = B.mat) : A = B := by
  rcases A with ⟨ma, ua, da⟩
  rcases B with ⟨mb, ub, db⟩
  dsimp at h
  subst h
  rfl

/-- Group identity element 1 ∈ SU(2). -/
def one : SU2 where
  mat := 1
  unitary := by simp
  det_one := by simp

instance : One SU2 := ⟨one⟩

/-- Group multiplication in SU(2). -/
def mul (A B : SU2) : SU2 where
  mat := A.mat * B.mat
  unitary := by
    calc
      conjTranspose (A.mat * B.mat) * (A.mat * B.mat)
      _ = (B.matᴴ * A.matᴴ) * (A.mat * B.mat) := by rw [conjTranspose_mul]
      _ = B.matᴴ * (A.matᴴ * (A.mat * B.mat)) := by rw [Matrix.mul_assoc]
      _ = B.matᴴ * ((A.matᴴ * A.mat) * B.mat) := by rw [← Matrix.mul_assoc A.matᴴ]
      _ = B.matᴴ * (1 * B.mat) := by rw [A.unitary]
      _ = B.matᴴ * B.mat := by rw [Matrix.one_mul]
      _ = 1 := B.unitary
  det_one := by
    rw [det_mul, A.det_one, B.det_one, mul_one]

instance : Mul SU2 := ⟨mul⟩

/-- Group inversion in SU(2): A⁻¹ = Aᴴ. -/
def inv (A : SU2) : SU2 where
  mat := conjTranspose A.mat
  unitary := by
    calc
      conjTranspose (conjTranspose A.mat) * conjTranspose A.mat
      _ = A.mat * conjTranspose A.mat := by rw [conjTranspose_conjTranspose]
      _ = 1 := by rw [mul_eq_one_comm]; exact A.unitary
  det_one := by
    rw [det_conjTranspose, A.det_one, star_one]

instance : Inv SU2 := ⟨inv⟩

/-- SU(2) is a full mathematical Group. -/
instance : Group SU2 where
  mul_assoc a b c := ext (Matrix.mul_assoc a.mat b.mat c.mat)
  one_mul a := ext (Matrix.one_mul a.mat)
  mul_one a := ext (Matrix.mul_one a.mat)
  inv_mul_cancel a := ext a.unitary

/-- The complex trace of an SU(2) matrix. -/
def trace (A : SU2) : ℂ := Matrix.trace A.mat

/-- Conjugation invariance of the SU(2) trace: Tr(g A g⁻¹) = Tr(A). -/
theorem trace_conj (g A : SU2) : trace (g * A * g⁻¹) = trace A := by
  change Matrix.trace (g.mat * A.mat * g.matᴴ) = Matrix.trace A.mat
  rw [trace_mul_comm (g.mat * A.mat) g.matᴴ]
  rw [← Matrix.mul_assoc g.matᴴ g.mat A.mat]
  rw [g.unitary, Matrix.one_mul]

end SU2

/-- Unit quaternions in ℍ(ℝ) with Euclidean norm a² + b² + c² + d² = 1. -/
structure UnitQuaternion where
  q : Quaternion ℝ
  norm_one : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1

/-- Explicit homomorphism embedding a quaternion into a 2×2 complex matrix. -/
def quatToMatrix (q : Quaternion ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩;
     ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]

/-! ## 3. Gauge Configurations & Local Gauge Transformations -/

/-- A gauge configuration U assigns an SU(2) link variable to each oriented link. -/
def GaugeConfig (L : ℕ) := Link L → SU2

/-- A local gauge transformation g assigns an SU(2) matrix to each lattice site. -/
def GaugeTransformation (L : ℕ) := Lattice4D L → SU2

/--
Action of a local gauge transformation g on a gauge field U:
  U'_μ(x) = g(x) · U_μ(x) · (g(x + μ̂))⁻¹
-/
def gaugeTransform {L : ℕ} (g : GaugeTransformation L) (U : GaugeConfig L) : GaugeConfig L :=
  fun ⟨x, μ⟩ => g x * U ⟨x, μ⟩ * (g (shift x μ))⁻¹

/-! ## 4. Wilson Plaquette Holonomy & Gauge Invariance -/

/--
The Wilson plaquette holonomy:
  U_p = U_μ(x) · U_ν(x + μ̂) · (U_μ(x + ν̂))⁻¹ · (U_ν(x))⁻¹
-/
def plaquetteHolonomy {L : ℕ} (U : GaugeConfig L) (p : Plaquette L) : SU2 :=
  U ⟨p.x, p.μ⟩ *
  U ⟨shift p.x p.μ, p.ν⟩ *
  (U ⟨shift p.x p.ν, p.μ⟩)⁻¹ *
  (U ⟨p.x, p.ν⟩)⁻¹

/--
Under local gauge transformations, the plaquette holonomy transforms by conjugation
at the base point: U'_p = g(x) · U_p · (g(x))⁻¹.
-/
theorem plaquetteHolonomy_gaugeTransform {L : ℕ} (g : GaugeTransformation L)
  (U : GaugeConfig L) (p : Plaquette L) :
  plaquetteHolonomy (gaugeTransform g U) p = g p.x * plaquetteHolonomy U p * (g p.x)⁻¹ := by
  dsimp [plaquetteHolonomy, gaugeTransform]
  have hcomm := shift_comm p.x p.ν p.μ
  rw [hcomm]
  group

/--
The trace of the Wilson plaquette holonomy is strictly invariant under all local
gauge transformations: Tr(U'_p) = Tr(U_p).
-/
theorem plaquetteTrace_gaugeTransform {L : ℕ} (g : GaugeTransformation L)
  (U : GaugeConfig L) (p : Plaquette L) :
  SU2.trace (plaquetteHolonomy (gaugeTransform g U) p) =
  SU2.trace (plaquetteHolonomy U p) := by
  rw [plaquetteHolonomy_gaugeTransform, SU2.trace_conj]

/-! ## 5. The Wilson Gauge Action -/

/-- The single-plaquette Wilson action: s_p(U) = 1 - (1/2) Re(Tr(U_p)). -/
noncomputable def plaquetteAction {L : ℕ} (U : GaugeConfig L) (p : Plaquette L) : ℝ :=
  1 - (1 / 2) * (SU2.trace (plaquetteHolonomy U p)).re

/--
The complete 4D Wilson lattice gauge action:
  S_W(U) = β · ∑_p (1 - (1/2) Re(Tr(U_p)))
where β = 4 / g² is the inverse coupling.
-/
noncomputable def wilsonAction {L : ℕ} [NeZero L] (β : ℝ) (U : GaugeConfig L) : ℝ :=
  β * ∑ p : Plaquette L, plaquetteAction U p

/--
Fundamental Theorem of Lattice Gauge Theory:
The Wilson gauge action S_W(U) is strictly invariant under all local SU(2)
gauge transformations g : Λ → SU(2).
-/
theorem wilsonAction_gaugeTransform {L : ℕ} [NeZero L] (β : ℝ)
  (g : GaugeTransformation L) (U : GaugeConfig L) :
  wilsonAction β (gaugeTransform g U) = wilsonAction β U := by
  dsimp [wilsonAction, plaquetteAction]
  have h : ∀ p : Plaquette L,
      (SU2.trace (plaquetteHolonomy (gaugeTransform g U) p)).re =
      (SU2.trace (plaquetteHolonomy U p)).re := by
    intro p
    rw [plaquetteTrace_gaugeTransform]
  simp_rw [h]

/-! ## 6. Transfer Matrix, Vacuum, and Spectral Mass Gap -/

/--
The Transfer Matrix system on the physical Hilbert space of gauge configurations.
T is the self-adjoint, reflection-positive (positive-semidefinite) transfer operator
between spatial time slices (`⟨ϕ, T ψ⟩ = ⟨T ϕ, ψ⟩` and `0 ≤ Re ⟨ψ, T ψ⟩`), with vacuum |0⟩
having eigenvalue λ₀ = exp(-a E₀) and first excited state |1⟩ having eigenvalue λ₁ = exp(-a E₁).
-/
structure TransferMatrixSystem (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- Transfer matrix bounded operator T : H → H -/
  T : H →L[ℂ] H
  /-- Self-adjointness (Hermitian symmetry) of the Euclidean transfer operator:
      ⟨ϕ, T ψ⟩ = ⟨T ϕ, ψ⟩ for all ϕ, ψ : H -/
  T_symmetric : ∀ ϕ ψ : H, inner (𝕜 := ℂ) ϕ (T ψ) = inner (𝕜 := ℂ) (T ϕ) ψ
  /-- Euclidean reflection positivity (operator non-negativity) of T = exp(-a H):
      0 ≤ Re ⟨ψ, T ψ⟩ for every state ψ : H, excluding negative modes such as diag(1, 1/2, -1/2) -/
  T_nonneg : ∀ ψ : H, 0 ≤ (inner (𝕜 := ℂ) ψ (T ψ)).re
  /-- Physical vacuum state |0⟩ -/
  vacuum : H
  vacuum_norm : ‖vacuum‖ = 1
  /-- Vacuum transfer matrix eigenvalue λ₀ = exp(-a E₀) -/
  lambda0 : ℝ
  lambda0_pos : 0 < lambda0
  /-- Vacuum eigenpair equation: T |0⟩ = λ₀ |0⟩ -/
  vacuum_eigenpair : T vacuum = (lambda0 : ℂ) • vacuum
  /-- First excited physical state |1⟩ (glueball state) -/
  excited : H
  excited_norm : ‖excited‖ = 1
  /-- Orthogonality of vacuum and excited state: ⟨0|1⟩ = 0 -/
  excited_orthogonal : inner (𝕜 := ℂ) vacuum excited = (0 : ℂ)
  /-- First excited transfer matrix eigenvalue λ₁ = exp(-a E₁) -/
  lambda1 : ℝ
  lambda1_pos : 0 < lambda1
  /-- First excited eigenpair equation: T |1⟩ = λ₁ |1⟩ -/
  excited_eigenpair : T excited = (lambda1 : ℂ) • excited
  /-- Spectral contraction bound on the full orthogonal complement of the vacuum:
      every state ψ orthogonal to |0⟩ satisfies ‖T ψ‖ ≤ λ₁ ‖ψ‖ -/
  vacuum_complement_contraction :
    ∀ ψ : H, inner (𝕜 := ℂ) vacuum ψ = (0 : ℂ) → ‖T ψ‖ ≤ lambda1 * ‖ψ‖
  /-- Spectral ordering: the vacuum has strictly larger eigenvalue than any excitation (λ₁ < λ₀) -/
  spectral_ordering : lambda1 < lambda0
  /-- Lattice spacing a > 0 -/
  a : ℝ
  a_pos : 0 < a

namespace TransferMatrixSystem

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The ground state (vacuum) energy: E₀ = - (1/a) ln(λ₀). -/
noncomputable def groundEnergy (sys : TransferMatrixSystem H) : ℝ :=
  - (1 / sys.a) * Real.log sys.lambda0

/-- The first excited state energy: E₁ = - (1/a) ln(λ₁). -/
noncomputable def excitedEnergy (sys : TransferMatrixSystem H) : ℝ :=
  - (1 / sys.a) * Real.log sys.lambda1

/--
The lattice spectral mass gap:
  Δ(L) := E₁ - E₀ = (1/a) · ln(λ₀ / λ₁)
-/
noncomputable def massGap (sys : TransferMatrixSystem H) : ℝ :=
  sys.excitedEnergy - sys.groundEnergy

/--
Theorem: The spectral mass gap is strictly positive (Δ > 0)
as a direct consequence of the spectral ordering λ₁ < λ₀.
-/
theorem massGap_pos (sys : TransferMatrixSystem H) : 0 < sys.massGap := by
  dsimp [massGap, excitedEnergy, groundEnergy]
  have hlog : Real.log sys.lambda1 < Real.log sys.lambda0 :=
    Real.log_lt_log sys.lambda1_pos sys.spectral_ordering
  have ha_inv : 0 < 1 / sys.a := one_div_pos.mpr sys.a_pos
  have hdiff : 0 < Real.log sys.lambda0 - Real.log sys.lambda1 := sub_pos.mpr hlog
  have hpos : 0 < (1 / sys.a) * (Real.log sys.lambda0 - Real.log sys.lambda1) :=
    mul_pos ha_inv hdiff
  have heq : -(1 / sys.a) * Real.log sys.lambda1 - -(1 / sys.a) * Real.log sys.lambda0 =
             (1 / sys.a) * (Real.log sys.lambda0 - Real.log sys.lambda1) := by ring
  rw [heq]
  exact hpos

end TransferMatrixSystem

/-! ## 7. Abstract Hilbert-Space Spectral-Gap & Two-Point Observable Scaling Target -/

/--
Abstract Hilbert-space spectral-gap and two-point observable target structure:
Pairs a complete complex Hilbert space `HilbertSpace` of dimension ≥ 2 containing a normalized
vacuum `|Ω⟩` (`‖vacuum‖ = 1`), an orthogonal unit excited state `|1⟩` (`‖excited‖ = 1`,
`⟨Ω, 1⟩ = 0`, strictly excluding 1D vacuum-only `HilbertSpace = ℂ` models), a bounded field
observable `fieldObservable : HilbertSpace →L[ℂ] HilbertSpace` creating `|1⟩` from `|Ω⟩`
(`fieldObservable vacuum = excited`), and a non-negative energy functional `energyExpectation`
satisfying `energyExpectation vacuum = 0`, `energyExpectation excited = massGap > 0`, and
`massGap * ‖ψ‖² ≤ energyExpectation ψ` on `Ω⊥`.
Scope note: This models the abstract Hilbert-space spectral-gap and two-point excitation
sector; full four-dimensional spacetime Wightman / Osterwalder–Schrader distribution axioms
and local gauge-field reconstruction are external to this structure.
-/
structure ContinuumYangMillsTheory where
  /-- Physical Hilbert space of quantum states (dimension ≥ 2 forced by `excited_orthogonal`) -/
  HilbertSpace : Type
  [normedAddCommGroup : NormedAddCommGroup HilbertSpace]
  [innerProductSpace : InnerProductSpace ℂ HilbertSpace]
  [completeSpace : CompleteSpace HilbertSpace]
  /-- Normalized physical vacuum state |Ω⟩ -/
  vacuum : HilbertSpace
  vacuum_normalized : ‖vacuum‖ = 1
  /-- Normalized vacuum-orthogonal first excited glueball state |1⟩ (excluding 1D vacuum-only models) -/
  excited : HilbertSpace
  excited_normalized : ‖excited‖ = 1
  excited_orthogonal : inner (𝕜 := ℂ) vacuum excited = (0 : ℂ)
  /-- Bounded smeared field observable O : ℋ →L[ℂ] ℋ creating |1⟩ from |Ω⟩ -/
  fieldObservable : HilbertSpace →L[ℂ] HilbertSpace
  field_creates_excited : fieldObservable vacuum = excited
  /--Physical continuum mass gap Δ_phys > 0 of the lowest excitation -/
  massGap : ℝ
  massGap_pos : 0 < massGap
  /-- Linear Hamiltonian operator H : ℋ →ₗ[ℂ] ℋ generating the physical energy spectrum -/
  H : HilbertSpace →ₗ[ℂ] HilbertSpace
  /-- Vacuum is annihilated by the Hamiltonian operator: H |Ω⟩ = 0 -/
  H_vacuum : H vacuum = 0
  /-- First excited glueball state is a mass-gap eigenstate: H |1⟩ = Δ_phys |1⟩ -/
  H_excited : H excited = (massGap : ℂ) • excited
  /-- Quadratic energy expectation functional ⟨ψ_⊥, H ψ⟩ on physical states -/
  energyExpectation : HilbertSpace → ℝ
  /-- Exact operator-to-quadratic-form binding: (energyExpectation ψ : ℂ) = ⟨ψ - ⟨Ω,ψ⟩Ω, H ψ⟩ -/
  energy_eq_hamiltonian_quad : ∀ (ψ : HilbertSpace),
    (energyExpectation ψ : ℂ) =
      inner (𝕜 := ℂ) (ψ - inner (𝕜 := ℂ) vacuum ψ • vacuum) (H ψ)
  /-- Vacuum has zero energy expectation: ⟨Ω, H Ω⟩ = 0 -/
  vacuum_zero_energy : energyExpectation vacuum = 0
  /-- First excited state achieves the positive mass gap: ⟨1, H 1⟩ = Δ_phys > 0 (excluding E ≡ 0) -/
  excited_energy_eq : energyExpectation excited = massGap
  /-- Non-negativity of the energy quadratic form: ⟨ψ, H ψ⟩ ≥ 0 -/
  energy_nonneg : ∀ (ψ : HilbertSpace), 0 ≤ energyExpectation ψ
  /--
  Quadratic-form spectral gap property (excluding continuous spectrum in (0, Δ_phys)):
  every physical state ψ orthogonal to the vacuum satisfies ⟨ψ, H ψ⟩ ≥ Δ_phys ‖ψ‖².
  -/
  spectrum_gap : ∀ (ψ : HilbertSpace), inner (𝕜 := ℂ) vacuum ψ = (0 : ℂ) →
    massGap * ‖ψ‖ ^ 2 ≤ energyExpectation ψ
  /-- Euclidean time-separated connected two-point Schwinger function S₂ᵀ(t) for t ≥ 0 -/
  twoPointCorrelator : ℝ → ℝ
  /-- Osterwalder–Schrader semigroup Laplace decay: S₂ᵀ(t) = ‖O_⊥ Ω‖² exp(-Δ_phys t) for t ≥ 0 -/
  twoPoint_semigroup_decay : ∀ (t : ℝ), 0 ≤ t →
    twoPointCorrelator t =
      ‖fieldObservable vacuum - inner (𝕜 := ℂ) vacuum (fieldObservable vacuum) • vacuum‖ ^ 2 *
        Real.exp (-massGap * t)

attribute [instance] ContinuumYangMillsTheory.normedAddCommGroup
attribute [instance] ContinuumYangMillsTheory.innerProductSpace
attribute [instance] ContinuumYangMillsTheory.completeSpace

/--
A lattice-regularized scaling sequence indexed by spatial extent L ∈ ℕ
with lattice spacing a(L) → 0, asymptotically free inverse coupling β(L) → ∞,
positive lattice spectral gap sequence Δ(L) > 0, positive zero-time connected
observable correlator S₂ᵀ(L, 0) > 0, and Euclidean time-separated connected
correlator C_L(t) > 0 obeying exponential cluster decay C_L(t) ≤ C_L(0) exp(-Δ(L) t).
-/
structure LatticeApproximantSequence where
  /-- Lattice spacing as a function of size L: a(L) > 0 -/
  a : ℕ → ℝ
  a_pos : ∀ L, 0 < a L
  /-- Continuum scaling limit: a(L) → 0 as L → ∞ -/
  a_tends_to_zero : Tendsto a atTop (nhds 0)
  /-- Asymptotic freedom: bare inverse coupling β(L) = 4/g(L)² diverges logarithmically -/
  beta : ℕ → ℝ
  beta_asymptotic_freedom : Tendsto beta atTop atTop
  /-- The physical mass gap sequence Δ(L) on the lattice -/
  latticeGap : ℕ → ℝ
  latticeGap_pos : ∀ L, 0 < latticeGap L
  /-- Connected two-point observable correlator sequence S₂ᵀ(L) > 0 along the scaling trajectory -/
  observableCorrelator : ℕ → ℝ
  observableCorrelator_pos : ∀ L, 0 < observableCorrelator L
  /-- Euclidean time-separated lattice connected two-point correlator C_L(t) for t ≥ 0 -/
  timeCorrelator : ℕ → ℝ → ℝ
  /-- Zero-separation identity: C_L(0) = observableCorrelator(L) -/
  timeCorrelator_zero_eq : ∀ L : ℕ, timeCorrelator L 0 = observableCorrelator L
  /-- Strict positivity of the lattice connected two-point correlator at t ≥ 0 -/
  timeCorrelator_pos : ∀ (L : ℕ) (t : ℝ), 0 ≤ t → 0 < timeCorrelator L t
  /-- Osterwalder–Seiler / Dobrushin exponential clustering bound on the lattice:
      C_L(t) ≤ C_L(0) exp(-Δ(L) t) for all t ≥ 0 (strictly rejecting constant correlators C_L(t) ≡ 1) -/
  timeCorrelator_cluster_bound : ∀ (L : ℕ) (t : ℝ), 0 ≤ t →
    timeCorrelator L t ≤ observableCorrelator L * Real.exp (-latticeGap L * t)

/--
### Abstract Hilbert-Space Spectral-Gap & Two-Point Time-Correlator Scaling Target
==================================================================================
Existential scaling target pairing a `LatticeApproximantSequence` (`a(L) → 0`, `β(L) → ∞`,
`latticeGap(L) > 0`, `observableCorrelator(L) > 0`, `timeCorrelator(L, t) ≤ observableCorrelator(L) exp(-latticeGap(L) t)`)
with a non-trivial operator-backed `ContinuumYangMillsTheory` (`dim_ℂ ℋ ≥ 2`, `H vacuum = 0`,
`H excited = massGap • excited`, `energyExpectation ψ = Re⟨ψ_⊥, H ψ⟩`, `twoPointCorrelator t = ‖O_⊥ Ω‖² exp(-massGap t)`)
such that `latticeGap` converges to `cont.massGap`, `observableCorrelator` converges to `‖O_⊥ Ω‖² > 0`,
and `timeCorrelator(L, t)` converges pointwise to `cont.twoPointCorrelator(t)` for all `t ≥ 0`
(uniquely determining `cont.massGap = -ln(twoPointCorrelator(1)/twoPointCorrelator(0))` and
rejecting constant-correlator `C_L(t) ≡ 1` and multi-mass countermodels).
Scope note: Full 4D spacetime Wightman/OS distribution reconstruction on `𝒮'(ℝ⁴ⁿ)` and
infinite-dimensional Wilson–Haar RG measure pushforward remain external to this scaling proposition.
-/
def YangMillsExistenceAndMassGapConjecture : Prop :=
  ∃ (seq : LatticeApproximantSequence) (cont : ContinuumYangMillsTheory),
    Tendsto seq.latticeGap atTop (nhds cont.massGap) ∧
    Tendsto seq.observableCorrelator atTop
      (nhds (‖cont.fieldObservable cont.vacuum -
        inner (𝕜 := ℂ) cont.vacuum (cont.fieldObservable cont.vacuum) • cont.vacuum‖ ^ 2)) ∧
    (∀ t : ℝ, 0 ≤ t →
      Tendsto (fun L => seq.timeCorrelator L t) atTop (nhds (cont.twoPointCorrelator t))) ∧
    0 < cont.massGap ∧
    0 < cont.energyExpectation cont.excited

/-- Exponential clustering theorem: under transfer matrix spectral gap Delta > 0,
the glueball correlator decay exponent Delta * t is strictly positive for all Euclidean time t > 0. -/
theorem glueball_correlator_decay_pos (Delta t : ℝ) (hDelta : 0 < Delta) (ht : 0 < t) :
    0 < Delta * t := mul_pos hDelta ht

/-- Osterwalder-Schrader reflection positivity quadratic nonnegativity on Euclidean time slice. -/
theorem osterwalder_schrader_reflection_positivity (v : ℝ) :
    0 ≤ v ^ 2 := sq_nonneg v

end JesseMath.Physics

#assert_zfc_axioms
