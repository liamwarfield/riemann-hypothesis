module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KernelsLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding Matrix Real
open scoped ComplexOrder nonZeroDivisors

noncomputable section

def genIndex {G : Type*} [AddCommGroup G] (A B : AddSubgroup G) : ℝ :=
  (B.relIndex A : ℝ) / (A.relIndex B : ℝ)

variable {K : Type*} [Field K]

def embVec (σ : K →+* ℂ) {n : ℕ} (v : Fin n → K) : Fin n → ℂ := fun j => σ (v j)

def gramAt {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*} (u : ι → Fin n → K) :
    Matrix ι ι ℂ :=
  fun a b => star (embVec σ (u a)) ⬝ᵥ (h *ᵥ embVec σ (u b))

variable [NumberField K]

structure HermLattice (K : Type*) [Field K] [NumberField K] (n : ℕ) where

  lattice : Submodule (𝓞 K) (Fin n → K)
  fg : lattice.FG
  span_eq : Submodule.span K (lattice : Set (Fin n → K)) = ⊤

  metric : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ
  posDef : ∀ σ, (metric σ).PosDef
  conj : ∀ σ, metric (conjugate σ) = (metric σ).map (starRingEnd ℂ)

def subDegree {n : ℕ} (L : Submodule (𝓞 K) (Fin n → K)) (h : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K) : ℝ :=
  log (genIndex (L ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K)).toAddSubgroup
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup) -
    1 / 2 * ∑ σ : K →+* ℂ, log (gramAt (h σ) σ u).det.re


variable (K) in
def normalise (x : ℝ) : ℝ := x / Module.finrank ℚ K

namespace HermLattice

variable {n : ℕ}

def degree (F : HermLattice K n) : ℝ :=
  subDegree F.lattice F.metric (fun j : Fin n => (Pi.single j 1 : Fin n → K))

def slope (F : HermLattice K n) : ℝ := normalise (K := K) F.degree / n

def lineDegree (F : HermLattice K n) (K' : Type*) [Field K'] [NumberField K'] [Algebra K K']
    (v : Fin n → K') : ℝ :=
  normalise (K := K') (subDegree
    (Submodule.span (𝓞 K') ((fun w : Fin n → K => fun j => algebraMap K K' (w j)) '' F.lattice))
    (fun σ' => F.metric (σ'.comp (algebraMap K K'))) (fun _ : Fin 1 => v))

end HermLattice

def idealLattice {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.pi Set.univ fun x => (a x : Submodule (𝓞 K) K)

def diagMetric {n : ℕ} (d : (K →+* ℂ) → Fin n → ℝ) : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ :=
  fun σ => Matrix.diagonal fun x => (d σ x : ℂ)

def LineOfLargeDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ), 1 ≤ i → ∀ (F : HermLattice K i) (ε : ℝ), 0 < ε →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (v : Fin i → K'),
      v ≠ 0 ∧ F.slope - 1 / 2 * log i - ε ≤ F.lineDegree K' v

def HermLattice.standard (K : Type*) [Field K] [NumberField K] (n : ℕ) : HermLattice K n where
  lattice := Submodule.span (𝓞 K) (Set.range fun j : Fin n => (Pi.single j 1 : Fin n → K))
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq := by
    rw [Submodule.span_span_of_tower]
    have h : (Set.range fun j : Fin n => (Pi.single j 1 : Fin n → K)) =
        Set.range (Pi.basisFun K (Fin n)) := by
      congr 1; funext j; exact (Pi.basisFun_apply _ _ _).symm
    rw [h]
    exact (Pi.basisFun K (Fin n)).span_eq
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory

noncomputable section

def qf {ι : Type*} [Fintype ι] (Y : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ (Y *ᵥ v)

def intVec {ι : Type*} (v : ι → ℤ) : ι → ℝ := fun i => (v i : ℝ)

def SymplecticReduction.Statement : Prop :=
  ∀ (g : ℕ) [NeZero g] (G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ),
    G ∈ symplecticGroup (Fin g) ℝ → G.PosDef →
    ∃ ρsq : ℝ, IsLeast {t | ∃ v : Fin g ⊕ Fin g → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} ρsq ∧
      ρsq ≤ 2 * g ∧
      ∃ P ∈ symplecticGroup (Fin g) ℤ,
        (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ) (Sum.inl 0) (Sum.inl 0) = ρsq ∧
        (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ).toBlocks₁₁.det ≤
          ρsq * (2 * g) ^ (g - 1)

def siegelGram {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) :
    Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks Y⁻¹ (Y⁻¹ * X) (X * Y⁻¹) (Y + X * Y⁻¹ * X)

def SiegelCoordinates.Statement : Prop :=
  ∀ g : ℕ,
    (∀ X Y : Matrix (Fin g) (Fin g) ℝ, X.IsSymm → Y.PosDef →
      siegelGram X Y ∈ symplecticGroup (Fin g) ℝ ∧ (siegelGram X Y).PosDef) ∧
    ∀ G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ,
      G ∈ symplecticGroup (Fin g) ℝ → G.PosDef →
      ∃! XY : Matrix (Fin g) (Fin g) ℝ × Matrix (Fin g) (Fin g) ℝ,
        XY.1.IsSymm ∧ XY.2.PosDef ∧ G = siegelGram XY.1 XY.2

def GaussianSum.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ), Y.PosDef → 0 < ρ →
    (∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)) →
    ∀ u : Fin g → ℝ,
      Summable (fun k : Fin g → ℤ => exp (-(π / 2) * qf Y (intVec k + u))) ∧
      ∑' k : Fin g → ℤ, exp (-(π / 2) * qf Y (intVec k + u)) ≤
        (C * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g

def periodMatrix {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g) (Fin g) ℂ :=
  X.map (↑) + Complex.I • Y.map (↑)

def thetaChar {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (z : Fin g → ℂ) : ℂ :=
  ∑' k : Fin g → ℤ,
    Complex.exp (π * Complex.I *
        ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ
          (periodMatrix X Y *ᵥ fun i => ((intVec k i + a i : ℝ) : ℂ))) +
      2 * π * Complex.I * ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ (z + fun i => (b i : ℂ))))

def thetaNorm {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (u₁ u₂ : Fin g → ℝ) : ℝ :=
  ‖thetaChar X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ))‖ *
    exp (-π * qf Y u₁)

structure IsReducedImaginaryPart {g : ℕ} [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) :
    Prop where
  pos : 0 < ρ
  sq_le : ρ ^ 2 ≤ 2 * g
  first : Y⁻¹ 0 0 = ρ ^ 2
  min : ∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)
  det_le : Y⁻¹.det ≤ ρ ^ 2 * (2 * g) ^ (g - 1)

def ThetaBound.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ) [NeZero g] (X Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ)
    (a b : Fin g → ℝ), X.IsSymm → Y.PosDef → IsReducedImaginaryPart Y ρ →
    (∀ i, ∃ m : ℤ, a i = m / 2) → (∀ i, ∃ m : ℤ, b i = m / 2) →
    (∫ u₁ in Set.Icc (0 : Fin g → ℝ) 1, ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1,
        thetaNorm X Y a b u₁ u₂ ^ 2) = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 2 : ℝ)) ∧
    ∀ u₁ u₂ : Fin g → ℝ,
      thetaNorm X Y a b u₁ u₂ ≤ ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ)) *
        exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2 +
          (g * log (1 + 1 / ρ) + C * g * log (2 * g)))

def finMean {S : Type*} [Fintype S] (f : S → ℝ) : ℝ := (∑ s, f s) / Fintype.card S

def WeakMatrixArithmetic.Statement : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 < C ∧
    ∀ (g : ℕ) [NeZero g] (S : Type) [Fintype S] [Nonempty S] (ρ : S → ℝ) (Φ : ℝ),
      (∀ s, 0 < ρ s ∧ ρ s ≤ √(2 * g)) → 0 ≤ Φ →
      finMean (fun s => π / 96 * (ρ s ^ 2)⁻¹ - (g * log (1 + 1 / ρ s) + C₀ * g * log (2 * g))) ≤ Φ →
      finMean (fun s => (ρ s ^ 2)⁻¹) ≤ C * (Φ + g ^ 2 * log (2 * g)) ∧
      finMean (fun s => g * log (1 + 1 / ρ s) + C₀ * g * log (2 * g)) ≤
        C * (Φ + g ^ 2 * log (2 * g)) ∧
      finMean (fun s => posLog (1 / ρ s)) ≤ 1 / 2 * log (1 + finMean (fun s => (ρ s ^ 2)⁻¹))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KernelsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix Real

noncomputable section

def alternant {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) : MvPolynomial ι ℚ :=
  (Matrix.of fun i i' : ι => (X i : MvPolynomial ι ℚ) ^ e i').det

def antisym {ι : Type*} [Fintype ι] [DecidableEq ι] (H : MvPolynomial ι ℚ) : MvPolynomial ι ℚ :=
  ∑ w : Equiv.Perm ι, ((Equiv.Perm.sign w : ℤ) : ℚ) • rename w H

def frobDim {r : ℕ} (la : Fin r → ℕ) : ℚ :=
  ((∑ a, la a).factorial : ℚ) *
      (∏ a : Fin r, ∏ b : Fin r,
        if a < b then ((la a + (r - 1 - a) : ℕ) : ℚ) - ((la b + (r - 1 - b) : ℕ) : ℚ) else 1) /
    ∏ a : Fin r, ((la a + (r - 1 - a)).factorial : ℚ)

def FrobeniusRectangleBound.Statement : Prop :=
  ∀ (r s : ℕ) (ν : Fin r → ℕ), Antitone ν →
    frobDim (fun a => s + ν a) ≤
      ((r * s + ∑ a, ν a).choose (∑ a, ν a) : ℚ) * frobDim (fun _ : Fin r => s) * frobDim ν

abbrev RootPoly (f j k : ℕ) : Type := MvPolynomial (Fin f × (Fin j ⊕ Fin k)) ℝ

variable (f j k : ℕ)

def flagDim : ℕ := f * ((j + k) * (j + k - 1) / 2)

def rootPsum (m : ℕ) (τ : Fin f) : RootPoly f j k := ∑ i, X (τ, i) ^ m

def lieClass (m : ℕ) : Fin f × Bool → RootPoly f j k
  | (τ, false) => ∑ a : Fin j, X (τ, Sum.inl a) ^ m
  | (τ, true) => (-1) ^ m * ∑ b : Fin k, X (τ, Sum.inr b) ^ m

def vandermonde {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) : R :=
  (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))).det

def fibre : RootPoly f j k :=
  ∏ τ : Fin f, if k ≤ j then
      vandermonde (fun b : Fin k => (X (τ, Sum.inr b) : RootPoly f j k)) *
        vandermonde (fun a : Fin j => (X (τ, Sum.inl a) : RootPoly f j k))
    else
      vandermonde (fun a : Fin j => -(X (τ, Sum.inl a) : RootPoly f j k)) *
        vandermonde (fun b : Fin k => (X (τ, Sum.inr b) : RootPoly f j k))

structure IsFlagIntegral (I : RootPoly f j k →ₗ[ℝ] ℝ) : Prop where
  kills : ∀ (m : ℕ) (τ : Fin f) (G : RootPoly f j k), 1 ≤ m → m ≤ flagDim f j k →
    G.IsHomogeneous (flagDim f j k - m) → I (rootPsum f j k m τ * G) = 0
  ne_zero : ∃ G : RootPoly f j k, G.IsHomogeneous (flagDim f j k) ∧ I G ≠ 0

def IsPowerSumDecomposition (F : RootPoly f j k) (Q : Fin f → ℕ → RootPoly f j k) : Prop :=
  (∀ τ m, 1 ≤ m → m ≤ j + k → (Q τ m).IsHomogeneous (flagDim f j k + 1 - m)) ∧
    F = ∑ τ : Fin f, ∑ m ∈ Finset.Icc 1 (j + k), rootPsum f j k m τ * Q τ m

def restAt (I : RootPoly f j k →ₗ[ℝ] ℝ) (vol : ℝ) (φ : ℕ → ℕ → Fin f → Fin f × Bool)
    (Q : Fin f → ℕ → RootPoly f j k) (p : ℕ) : ℝ :=
  log p * vol * ∑ τ : Fin f, ∑ m ∈ Finset.Icc 2 (j + k), ∑' n : ℕ,
    (((p : ℝ) ^ ((n + 1) * m))⁻¹ * m * I (lieClass f j k (m - 1) (φ p (n + 1) τ) * Q τ m))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.CovolumeGram
namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix Module

theorem covolume_eq_sqrt_det_gram {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    ZLattice.covolume L = Real.sqrt (gram ℝ fun i ↦ (b i : V)).det := by
  have hcard : Fintype.card ι = finrank ℝ V := by
    rw [← ZLattice.rank ℝ L, finrank_eq_card_basis b]
  let o : OrthonormalBasis ι ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivFinOfCardEq hcard).symm
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis,
    measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    OrthonormalBasis.coe_toBasis, measureReal_def, o.volume_parallelepiped, ENNReal.toReal_one,
    mul_one, gram_eq_conjTranspose_mul o, det_mul, det_conjTranspose, star_trivial,
    ← sq, Real.sqrt_sq_eq_abs, Basis.det_apply]
  congr 2

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HermitianLattice
namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct

noncomputable section

def ComplexAt {K : Type*} [Field K] (_σ : K →+* ℂ) : Type := ℂ

namespace ComplexAt

variable {K : Type*} {_ : Field K} (σ : K →+* ℂ)

instance : CommRing (ComplexAt σ) := inferInstanceAs (CommRing ℂ)

instance : Algebra ℂ (ComplexAt σ) := inferInstanceAs (Algebra ℂ ℂ)

def ofComplex : ℂ ≃ₐ[ℂ] ComplexAt σ := AlgEquiv.refl

instance : Algebra (𝓞 K) (ComplexAt σ) :=
  ((ofComplex σ).toRingHom.comp (σ.comp (algebraMap (𝓞 K) K))).toAlgebra

theorem smul_def (a : 𝓞 K) (z : ComplexAt σ) : a • z = ofComplex σ (σ (a : K)) * z := rfl

theorem complex_smul_def (c : ℂ) (z : ComplexAt σ) : c • z = ofComplex σ c * z := rfl

instance : SMulCommClass (𝓞 K) ℂ (ComplexAt σ) where
  smul_comm a c z := by
    rw [smul_def, complex_smul_def, complex_smul_def, smul_def, mul_left_comm]

def conj : ComplexAt σ →+* ComplexAt (conjugate σ) :=
  (ofComplex (conjugate σ)).toRingHom.comp ((starRingEnd ℂ).comp (ofComplex σ).symm.toRingHom)

theorem conj_ofComplex (z : ℂ) :
    conj σ (ofComplex σ z) = ofComplex (conjugate σ) (starRingEnd ℂ z) := rfl

def conjLinear : ComplexAt σ →ₗ[𝓞 K] ComplexAt (conjugate σ) where
  toFun := conj σ
  map_add' := map_add _
  map_smul' a z := by
    rw [smul_def, map_mul, RingHom.id_apply, smul_def, conj_ofComplex]
    rfl

theorem conj_smul (c : ℂ) (z : ComplexAt σ) : conj σ (c • z) = starRingEnd ℂ c • conj σ z := by
  rw [complex_smul_def, map_mul, conj_ofComplex, complex_smul_def]

end ComplexAt

open ComplexAt

variable {K : Type*} [Field K]

abbrev Fibre (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E] : Type _ :=
  ComplexAt σ ⊗[𝓞 K] E

section Fibre

variable (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]

def conjMap : Fibre σ E →ₗ[𝓞 K] Fibre (conjugate σ) E :=
  TensorProduct.map (conjLinear σ) LinearMap.id

variable {σ E}

@[simp]
theorem conjMap_tmul (z : ComplexAt σ) (e : E) : conjMap σ E (z ⊗ₜ e) = conj σ z ⊗ₜ e := rfl

theorem conjMap_smul (c : ℂ) (x : Fibre σ E) :
    conjMap σ E (c • x) = starRingEnd ℂ c • conjMap σ E x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul z e => rw [smul_tmul', conjMap_tmul, conjMap_tmul, smul_tmul', conj_smul]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

end Fibre

structure HermitianMetric (K : Type*) [Field K] [NumberField K] (E : Type*) [AddCommGroup E]
    [Module (𝓞 K) E] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] where

  form : ∀ σ : K →+* ℂ, InnerProductSpace.Core ℂ (Fibre σ E)

  form_conj : ∀ (σ : K →+* ℂ) (x y : Fibre σ E),
    (form (conjugate σ)).inner (conjMap σ E x) (conjMap σ E y) = starRingEnd ℂ ((form σ).inner x y)

structure HermitianBundle.{u} (K : Type*) [Field K] [NumberField K] where

  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module (𝓞 K) carrier]
  [instFinite : Module.Finite (𝓞 K) carrier]
  [instProjective : Module.Projective (𝓞 K) carrier]

  metric : HermitianMetric K carrier

attribute [instance] HermitianBundle.instAddCommGroup HermitianBundle.instModule
  HermitianBundle.instFinite HermitianBundle.instProjective

@[instance_reducible]
def coreOfInjective {𝕜 V W : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] (f : V →ₗ[𝕜] W)
    (hf : Function.Injective f) : InnerProductSpace.Core 𝕜 V where
  inner x y := inner 𝕜 (f x) (f y)
  conj_inner_symm x y := inner_conj_symm (f x) (f y)
  re_inner_nonneg x := inner_self_nonneg
  add_left x y z := by simp only [map_add (f := _), inner_add_left]
  smul_left x y r := by simp only [map_smul, inner_smul_left]
  definite x h := hf (by rw [map_zero]; exact inner_self_eq_zero.mp h)

theorem coreOfInjective_inner {𝕜 V W : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] (f : V →ₗ[𝕜] W)
    (hf : Function.Injective f) (x y : V) :
    (coreOfInjective f hf).inner x y = inner 𝕜 (f x) (f y) := rfl

section Examples

variable (K : Type*) [Field K] [NumberField K]

def integersCoord (σ : K →+* ℂ) : Fibre σ (𝓞 K) ≃ₗ[ℂ] ℂ :=
  ((AlgebraTensorModule.rid (𝓞 K) (ComplexAt σ) (ComplexAt σ)).restrictScalars ℂ).trans
    (ofComplex σ).symm.toLinearEquiv

variable {K}

omit [NumberField K] in
theorem integersCoord_tmul (σ : K →+* ℂ) (z : ComplexAt σ) (a : 𝓞 K) :
    integersCoord K σ (z ⊗ₜ a) = σ (a : K) * (ofComplex σ).symm z := rfl

omit [NumberField K] in
theorem integersCoord_conjMap (σ : K →+* ℂ) (x : Fibre σ (𝓞 K)) :
    integersCoord K (conjugate σ) (conjMap σ (𝓞 K) x) = starRingEnd ℂ (integersCoord K σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z a =>
    rw [conjMap_tmul, integersCoord_tmul, integersCoord_tmul, map_mul]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

variable (K)

def HermitianMetric.integers : HermitianMetric K (𝓞 K) where
  form σ := coreOfInjective (integersCoord K σ).toLinearMap (integersCoord K σ).injective
  form_conj σ x y := by
    simp only [coreOfInjective_inner, LinearEquiv.coe_coe, integersCoord_conjMap,
      RCLike.inner_apply, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]

theorem HermitianMetric.integers_inner (σ : K →+* ℂ) (z w : ComplexAt σ) (a b : 𝓞 K) :
    ((HermitianMetric.integers K).form σ).inner (z ⊗ₜ a) (w ⊗ₜ b) =
      starRingEnd ℂ (σ (a : K) * (ofComplex σ).symm z) * (σ (b : K) * (ofComplex σ).symm w) := by
  rw [mul_comm]; rfl

def standardCoord (σ : K →+* ℂ) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Fibre σ (ι → 𝓞 K) ≃ₗ[ℂ] EuclideanSpace ℂ ι :=
  ((piScalarRight (𝓞 K) (ComplexAt σ) (ComplexAt σ) ι).restrictScalars ℂ).trans
    ((LinearEquiv.piCongrRight fun _ ↦ (ofComplex σ).symm.toLinearEquiv).trans
      (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm)

variable {K}

omit [NumberField K] in
theorem standardCoord_tmul (σ : K →+* ℂ) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (z : ComplexAt σ) (v : ι → 𝓞 K) (i : ι) :
    standardCoord K σ ι (z ⊗ₜ v) i = σ (v i : K) * (ofComplex σ).symm z := rfl

omit [NumberField K] in
theorem standardCoord_conjMap (σ : K →+* ℂ) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (x : Fibre σ (ι → 𝓞 K)) (i : ι) :
    standardCoord K (conjugate σ) ι (conjMap σ (ι → 𝓞 K) x) i =
      starRingEnd ℂ (standardCoord K σ ι x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, PiLp.zero_apply]
  | tmul z v =>
    rw [conjMap_tmul, standardCoord_tmul, standardCoord_tmul, map_mul]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), PiLp.add_apply, hx, hy, map_add (f := _), PiLp.add_apply, map_add (f := _)]

variable (K)

def HermitianMetric.standard (ι : Type*) [Fintype ι] [DecidableEq ι] :
    HermitianMetric K (ι → 𝓞 K) where
  form σ := coreOfInjective (standardCoord K σ ι).toLinearMap (standardCoord K σ ι).injective
  form_conj σ x y := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [coreOfInjective_inner, LinearEquiv.coe_coe, PiLp.inner_apply, RCLike.inner_apply,
      standardCoord_conjMap, map_sum, map_mul, Complex.conj_conj]

theorem HermitianMetric.standard_inner (ι : Type*) [Fintype ι] [DecidableEq ι] (σ : K →+* ℂ)
    (x y : Fibre σ (ι → 𝓞 K)) :
    ((HermitianMetric.standard K ι).form σ).inner x y =
      ∑ i, starRingEnd ℂ (standardCoord K σ ι x i) * standardCoord K σ ι y i := by
  change inner ℂ (standardCoord K σ ι x) (standardCoord K σ ι y) = _
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

def HermitianBundle.integers : HermitianBundle K := ⟨𝓞 K, HermitianMetric.integers K⟩

def HermitianBundle.standard (n : ℕ) : HermitianBundle K :=
  ⟨Fin n → 𝓞 K, HermitianMetric.standard K (Fin n)⟩

end Examples

abbrev GaussianField : Type := CyclotomicField 4 ℚ

def ratIntegers : HermitianBundle ℚ := HermitianBundle.integers ℚ

def ratStandard (n : ℕ) : HermitianBundle ℚ := HermitianBundle.standard ℚ n

def gaussianIntegers : HermitianBundle GaussianField := HermitianBundle.integers GaussianField

def gaussianStandard (n : ℕ) : HermitianBundle GaussianField :=
  HermitianBundle.standard GaussianField n

theorem HermitianMetric.standard_inner_single (K : Type*) [Field K] [NumberField K] (n : ℕ)
    (σ : K →+* ℂ) (i : Fin n) :
    ((HermitianMetric.standard K (Fin n)).form σ).inner (1 ⊗ₜ Pi.single i 1) (1 ⊗ₜ Pi.single i 1)
      = 1 := by
  rw [HermitianMetric.standard_inner, Finset.sum_eq_single i]
  · simp only [standardCoord_tmul, Pi.single_eq_same, map_one]
    show starRingEnd ℂ (1 * 1) * (1 * 1) = 1
    simp
  · intro j _ hj
    simp [standardCoord_tmul, Pi.single_eq_of_ne hj]
  · simp

def ratEmbedding : ℚ →+* ℂ := Rat.castHom ℂ

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ProjTopology
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]

instance : TopologicalSpace (ℙ K V) :=
  TopologicalSpace.coinduced (Projectivization.mk' K) inferInstance

namespace ProjTopology

lemma continuous_mk' : Continuous (Projectivization.mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  continuous_coinduced_rng

lemma isOpen_iff {s : Set (ℙ K V)} :
    IsOpen s ↔ IsOpen ((Projectivization.mk' K) ⁻¹' s : Set {v : V // v ≠ 0}) :=
  isOpen_coinduced

lemma continuous_iff {Y : Type*} [TopologicalSpace Y] {g : ℙ K V → Y} :
    Continuous g ↔ Continuous (g ∘ Projectivization.mk' K) :=
  continuous_coinduced_dom

end ProjTopology

instance compactSpace_projectivization_complex (N : ℕ) : CompactSpace (ℙ ℂ (Fin (N + 1) → ℂ)) := by
  have hS : IsCompact (Metric.sphere (0 : Fin (N + 1) → ℂ) 1) := isCompact_sphere 0 1
  have : CompactSpace (Metric.sphere (0 : Fin (N + 1) → ℂ) 1) := isCompact_iff_compactSpace.mp hS
  have hne : ∀ w : Metric.sphere (0 : Fin (N + 1) → ℂ) 1, (w : Fin (N + 1) → ℂ) ≠ 0 := by
    intro w h
    have := w.2
    rw [h, mem_sphere_iff_norm, sub_zero, norm_zero] at this
    exact zero_ne_one this
  let g : Metric.sphere (0 : Fin (N + 1) → ℂ) 1 → ℙ ℂ (Fin (N + 1) → ℂ) := fun w =>
    Projectivization.mk' ℂ ⟨w.1, hne w⟩
  have hg : Continuous g :=
    ProjTopology.continuous_mk'.comp (Continuous.subtype_mk continuous_subtype_val _)
  have hsurj : Function.Surjective g := by
    intro v
    induction v using Projectivization.ind with
    | h w hw =>
      have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      refine ⟨⟨(‖w‖⁻¹ : ℂ) • w, ?_⟩, ?_⟩
      · rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, Complex.norm_real, norm_norm,
          inv_mul_cancel₀ hn]
      · change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ w hw
        rw [Projectivization.mk_eq_mk_iff]
        exact ⟨Units.mk0 (‖w‖⁻¹ : ℂ) (inv_ne_zero (by exact_mod_cast hn)), rfl⟩
  refine ⟨?_⟩
  rw [← hsurj.range_eq]
  exact isCompact_range hg

end GroundTheory.Heights₂.Heights
end
