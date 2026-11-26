module

public import Development.WeilBound.CoreStatements.SesquilinearFractions.SesqSesquilinearSkewHermitian
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqSesquilinearSkewHermitian
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqSesquilinearSkewHermitian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.Sesq

theorem form_of_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∀ (a : 𝓞 E) x y, Algebra.trace ℚ E ((a : E) * sesq D x y) = (D.EF (a • x) y : ℚ)) ∧ (∀ x x' y, sesq D (x + x') y = sesq D x y + sesq D x' y) ∧ (∀ x y y', sesq D x (y + y') = sesq D x y + sesq D x y') ∧ (∀ (a : 𝓞 E) x y, sesq D (a • x) y = a * sesq D x y) ∧ (∀ (a : 𝓞 E) x y, sesq D x (a • y) = IsCMField.complexConj E (a : E) * sesq D x y) ∧ (∀ x y, sesq D y x = -IsCMField.complexConj E (sesq D x y)) ∧ ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x y, ∃ b : 𝓞 E, (δ : E) * sesq D x y = b := by
  intro E _ _ _ H D
  exact PositivityTheory.Xgf.sesq_sesquilinear_skew_hermitian E H D

end GlobalTheory.CompanionTheory.Ar.Fl.Sesq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqSesquilinearSkewHermitianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sesq_sesquilinear_skew_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∀ (a : 𝓞 E) x y, Algebra.trace ℚ E ((a : E) * sesq D x y) = (D.EF (a • x) y : ℚ)) ∧ (∀ x x' y, sesq D (x + x') y = sesq D x y + sesq D x' y) ∧ (∀ x y y', sesq D x (y + y') = sesq D x y + sesq D x y') ∧ (∀ (a : 𝓞 E) x y, sesq D (a • x) y = a * sesq D x y) ∧ (∀ (a : 𝓞 E) x y, sesq D x (a • y) = IsCMField.complexConj E (a : E) * sesq D x y) ∧ (∀ x y, sesq D y x = -IsCMField.complexConj E (sesq D x y)) ∧ ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x y, ∃ b : 𝓞 E, (δ : E) * sesq D x y = b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.Sesq.form_of_datum | exact GlobalTheory.CompanionTheory.Ar.Fl.Sesq.form_of_datum | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.Sesq.form_of_datum <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.FreeQuotProof

def HasAffineChart {P X : Scheme.{0}} (a b : P ⟶ X) (V : X.Opens) : Prop :=
  a ⁻¹ᵁ V = b ⁻¹ᵁ V ∧
    ∃ (Y : Scheme.{0}) (q : V.toScheme ⟶ Y) (a' : (b ⁻¹ᵁ V).toScheme ⟶ V.toScheme),
      IsAffine Y ∧ IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
        a' ≫ V.ι = (b ⁻¹ᵁ V).ι ≫ a ∧ IsPullback a' (b ∣_ V) q q

end GlobalTheory.CompanionTheory.FreeQuotProof
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqUnimodularDual
section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.TraceIntegralOfCodifferent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem trace_integral_of_codifferent {z : E} (hz : ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∃ b : 𝓞 E, (δ : E) * z = b) (c : 𝓞 E) :
    ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ E (z * (c : E)) := by
  have hne : (differentIdeal ℤ (𝓞 E) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
    rw [coeIdeal_differentIdeal ℤ ℚ]
    exact inv_ne_zero (FractionalIdeal.dual_ne_zero ℤ ℚ (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 E)) E) _ _ _))
  have hinv : z ∈ (differentIdeal ℤ (𝓞 E) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hne]
    intro y hy
    obtain ⟨δ, hδ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    obtain ⟨b, hb⟩ := hz δ hδ
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨b, by rw [mul_comm]; exact hb.symm⟩
  rw [coeIdeal_differentIdeal ℤ ℚ, inv_inv] at hinv
  rw [FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 E)) E) _ _ _)] at hinv
  obtain ⟨n, hn⟩ := hinv (c : E) ((FractionalIdeal.mem_one_iff _).2 ⟨c, rfl⟩)
  exact ⟨n, by rw [← Algebra.traceForm_apply, ← hn]; simp⟩

theorem sesq_unimodular (D : Datum H) :
    (∀ y, (∀ x, sesq D x y = 0) → y = 0) ∧ ∀ f : D.La →ₗ[𝓞 E] E,
      (∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x, ∃ b : 𝓞 E, (δ : E) * f x = b) → ∃ y, ∀ x, f x = sesq D x y := by
  refine ⟨fun y hy => ?_, fun f hf => ?_⟩
  · apply D.unimod.1
    ext x
    have h1 := trace_mul_sesq_eq_form D 1 x y
    rw [hy x, mul_zero, map_zero, one_smul] at h1
    rw [map_zero, LinearMap.zero_apply, Datum_EF_antisymm, neg_eq_zero]
    exact_mod_cast h1.symm
  · choose n hn using fun x => trace_integral_of_codifferent (hf · · x) 1
    have hadd : ∀ x x', n (x + x') = n x + n x' := by
      intro x x'
      have := hn (x + x')
      rw [map_add (f := _), add_mul, map_add (f := _), ← hn x, ← hn x'] at this
      exact_mod_cast this
    let φ : D.La →+ ℤ := AddMonoidHom.mk' n hadd
    obtain ⟨w, hw⟩ := D.unimod.2 φ.toIntLinearMap
    refine ⟨-w, fun x => eq_of_trace_pairing_eq fun c => ?_⟩
    rw [trace_mul_sesq_eq_form, map_neg, Datum_EF_antisymm, neg_neg]
    have hwx : D.EF w (c • x) = n (c • x) := by rw [hw]; rfl
    rw [hwx, hn, map_smul]
    simp [Algebra.smul_def]

end GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

theorem sesq_unimodular_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∀ y, (∀ x, sesq D x y = 0) → y = 0) ∧ ∀ f : D.La →ₗ[𝓞 E] E, (∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x, ∃ b : 𝓞 E, (δ : E) * f x = b) → ∃ y, ∀ x, f x = sesq D x y :=
  fun _ _ _ _ _ D => GlobalTheory.CompanionTheory.Ar.Fl.sesq_unimodular D

end PositivityTheory.Xgf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqUnimodularDual
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem unimodularity_sesq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∀ y, (∀ x, sesq D x y = 0) → y = 0) ∧ ∀ f : D.La →ₗ[𝓞 E] E, (∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x, ∃ b : 𝓞 E, (δ : E) * f x = b) → ∃ y, ∀ x, f x = sesq D x y :=
  PositivityTheory.Xgf.sesq_unimodular_dual

end GlobalTheory.CompanionTheory.Ar.Fl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqUnimodularDualStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sesq_unimodular_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∀ y, (∀ x, sesq D x y = 0) → y = 0) ∧ ∀ f : D.La →ₗ[𝓞 E] E, (∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x, ∃ b : 𝓞 E, (δ : E) * f x = b) → ∃ y, ∀ x, f x = sesq D x y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.unimodularity_sesq | exact GlobalTheory.CompanionTheory.Ar.Fl.unimodularity_sesq | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.unimodularity_sesq <;> assumption)
end
end
