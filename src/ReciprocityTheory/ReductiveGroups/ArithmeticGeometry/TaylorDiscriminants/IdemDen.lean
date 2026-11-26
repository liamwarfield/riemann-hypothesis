module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.IdemDen
noncomputable section

open NumberField TensorProduct

namespace ReciprocityTheory.ChartRestriction.G.TB

def trDual {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) :
    Module.Basis ι ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b

def idemOf {E : Type} [Field E] [NumberField E] {C : Type} [Field C] [Algebra ℚ C] {ι : Type} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℚ E) (τ : E →+* C) : E ⊗[ℚ] C :=
  ∑ i, trDual b i ⊗ₜ[ℚ] τ (b i)

def evAt {E : Type} [Field E] {C : Type} [Field C] [Algebra ℚ E] [Algebra ℚ C] (σ : E →+* C) :
    E ⊗[ℚ] C →ₐ[ℚ] C :=
  Algebra.TensorProduct.productMap (σ.toRatAlgHom) (AlgHom.id ℚ C)


open Classical in
def IdemEvalSt : Prop := by
  classical
  exact ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] [IsAlgClosed C] (ι : Type)
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (τ σ : E →+* C),
    evAt σ (idemOf b τ) = if σ = τ then 1 else 0

def DualDiffSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E),
    (∀ i, IsIntegral ℤ (b i)) →
    (∀ x : 𝓞 E, ∃ c : ι → ℤ, (x : E) = ∑ i, (c i : ℚ) • b i) →
    ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ i, IsIntegral ℤ ((δ : E) * trDual b i)

end ReciprocityTheory.ChartRestriction.G.TB
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GaugeRatio
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace ReciprocityTheory.ChartRestriction.G.TB

abbrev GLet (T : Type) (rk : T → ℕ) : Type := Σ σ : T, Fin (rk σ)

def scaleBy {O k T : Type} [CommRing O] [CommRing k] {rk : T → ℕ} (χ : T → O →+* k) (a : O) :
    MvPowerSeries (GLet T rk) k →+* MvPowerSeries (GLet T rk) k :=
  MvPowerSeries.rescale (fun l => χ l.1 a)

def GaugeRatioSt : Prop :=
  ∀ (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] (T : Type) [Fintype T]
    (rk : T → ℕ) (χ : T → O →+* k) (cc : T → T),
    (∀ σ a, χ (cc σ) a = χ σ (star a)) →
    (∀ σ τ, σ ≠ τ → ∃ a, IsUnit (χ σ a - χ τ a)) →
    ∀ r : MvPowerSeries (GLet T rk) k, constantCoeff r = 1 →
    (∀ a : O, scaleBy χ (1 + a * star a) r = scaleBy χ a r ^ 2 * r * scaleBy χ (a * star a) r) →
    ∃ q : MvPowerSeries (GLet T rk) k, constantCoeff q = 0 ∧
      (∀ m, coeff m q ≠ 0 → m.degree = 2) ∧
      (∀ l l' : GLet T rk, coeff (Finsupp.single l 1 + Finsupp.single l' 1) q ≠ 0 → l'.1 = cc l.1) ∧
      r = PowerSeries.subst q (PowerSeries.exp k)

end ReciprocityTheory.ChartRestriction.G.TB
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.PerpVecPerpSt
namespace ReciprocityTheory.ChartRestriction.G.TB

open MvPolynomial

variable {R : Type} [CommRing R]

noncomputable def xForm {p q n : ℕ} (e : Fin p → Fin n → R) (a b : Fin p) :
    MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R :=
  ∑ k, X (Sum.inl (a, k)) * C (e b k)

noncomputable def yForm {p q n : ℕ} (f : Fin q → Fin n → R) (a b : Fin q) :
    MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R :=
  ∑ k, X (Sum.inr (a, k)) * C (f b k)

noncomputable def leadMinor {S : Type} [CommRing S] {m : ℕ} (M : Matrix (Fin m) (Fin m) S) (i : Fin (m + 1)) : S :=
  (M.submatrix (Fin.castLE (Nat.lt_succ_iff.mp i.isLt)) (Fin.castLE (Nat.lt_succ_iff.mp i.isLt)) :
    Matrix (Fin i) (Fin i) S).det

section Perp

variable {V : Type} [AddCommGroup V] [Module R V]

def hMat {p : ℕ} (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) : Matrix (Fin p) (Fin p) R :=
  Matrix.of fun a' a => h (e' a') (e a)

def perpVec {p : ℕ} (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) : V :=
  (hMat h e e').det • g - ∑ a, ∑ a', ((hMat h e e').adjugate a a' * h g (e a)) • e' a'

end Perp

def PerpVecSt : Prop :=
  ∀ (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) (c : Fin p), h (perpVec h e e' g) (e c) = 0

def PerpVecPerpSt : Prop :=
  ∀ (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V),
    (∀ a, h g (e a) = 0) → perpVec h e e' g = (hMat h e e').det • g

end ReciprocityTheory.ChartRestriction.G.TB
end
