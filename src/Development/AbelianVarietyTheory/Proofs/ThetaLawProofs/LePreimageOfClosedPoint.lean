module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMulDotProductLeOfIsCompactThetaDomain
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LePreimageOfClosedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.FormalChart

section Alg

variable {O : Type} [CommRing O] {B : Type} [CommRing B] [Algebra O B] {g : ℕ}

theorem ext_of_isHausdorff (π : MvPolynomial (Fin g) O →ₐ[O] B) (hπ : π.toRingHom.Etale)
    {A : Type} [CommRing A] [Algebra O A] (J : Ideal A) [IsHausdorff J A] (φ₁ φ₂ : B →ₐ[O] A)
    (h : ∀ b, φ₁ b - φ₂ b ∈ J)
    (hs : ∀ j : Fin g, φ₁ (π (MvPolynomial.X j)) = φ₂ (π (MvPolynomial.X j))) : φ₁ = φ₂ := by
  letI : Algebra (MvPolynomial (Fin g) O) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin g) O) B := hπ
  let ρ : MvPolynomial (Fin g) O →ₐ[O] A := φ₁.comp π
  have hρ2 : φ₂.comp π = ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    exact (hs j).symm
  letI : Algebra (MvPolynomial (Fin g) O) A := ρ.toRingHom.toAlgebra
  let ψ₁ : B →ₐ[MvPolynomial (Fin g) O] A :=
    { φ₁.toRingHom with commutes' := fun p => rfl }
  let ψ₂ : B →ₐ[MvPolynomial (Fin g) O] A :=
    { φ₂.toRingHom with commutes' := fun p => AlgHom.congr_fun hρ2 p }
  have hJ : ⨅ i, J ^ i = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact GlobalTheory.eq_of_forall_sub_mem_ideal_pow J fun n => by
      rw [sub_zero]
      exact Ideal.mem_iInf.1 hx n
  have : ψ₁ = ψ₂ := Algebra.FormallyUnramified.ext_of_iInf J hJ fun b => Ideal.Quotient.eq.2 (h b)
  ext x
  exact AlgHom.congr_fun this x

theorem exists_expansion (π : MvPolynomial (Fin g) O →ₐ[O] B) (hπ : π.toRingHom.Etale)
    (e : B →ₐ[O] O) :
    ∃ φ : B →ₐ[O] MvPowerSeries (Fin g) O, (∀ b, MvPowerSeries.constantCoeff (φ b) = e b) ∧
      ∀ j, φ (π (MvPolynomial.X j) - algebraMap O B (e (π (MvPolynomial.X j)))) = MvPowerSeries.X j := by
  letI : Algebra (MvPolynomial (Fin g) O) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin g) O) B := hπ
  let A := MvPowerSeries (Fin g) O
  let ρ : MvPolynomial (Fin g) O →ₐ[O] A :=
    MvPolynomial.aeval (fun j => algebraMap O A (e (π (MvPolynomial.X j))) + MvPowerSeries.X j)
  letI : Algebra (MvPolynomial (Fin g) O) A := ρ.toRingHom.toAlgebra
  let J : Ideal A := Ideal.span (Set.range MvPowerSeries.X)
  have hf₀ : ((Ideal.Quotient.mkₐ O J).comp ((Algebra.ofId O A).comp e)).comp π =
      (Ideal.Quotient.mkₐ O J).comp ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ρ,
      MvPolynomial.aeval_X, Algebra.ofId_apply]
    rw [eq_comm, Ideal.Quotient.eq, add_sub_cancel_left]
    exact Ideal.subset_span ⟨j, rfl⟩
  let f₀ : B →ₐ[MvPolynomial (Fin g) O] A ⧸ J :=
    { ((Ideal.Quotient.mkₐ O J).comp ((Algebra.ofId O A).comp e)).toRingHom with
      commutes' := fun p => AlgHom.congr_fun hf₀ p }
  obtain ⟨φ', hφ'⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := J) f₀
  have hc : ∀ p, φ' (π p) = ρ p := fun p => φ'.commutes p
  let φ : B →ₐ[O] A := { φ'.toRingHom with
    commutes' := fun r => by
      show φ' (algebraMap O B r) = _
      rw [← π.commutes, hc, ρ.commutes] }
  have hφ : ∀ b, φ b = φ' b := fun _ => rfl
  have hJ : J ≤ RingHom.ker (MvPowerSeries.constantCoeff) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact MvPowerSeries.constantCoeff_X i
  refine ⟨φ, fun b => ?_, fun j => ?_⟩
  · have e1 : Ideal.Quotient.mk J (φ' b) = Ideal.Quotient.mk J (algebraMap O A (e b)) :=
      AlgHom.congr_fun hφ' b
    rw [Ideal.Quotient.eq] at e1
    have e2 := hJ e1
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at e2
    exact e2.trans (MvPowerSeries.constantCoeff_C _)
  · rw [map_sub, AlgHom.commutes, hφ, hc]
    simp [ρ]

theorem exists_factor (π : MvPolynomial (Fin g) O →ₐ[O] B) (hπ : π.toRingHom.Etale)
    (e : B →ₐ[O] O) (φ : B →ₐ[O] MvPowerSeries (Fin g) O)
    (h₁ : ∀ b, MvPowerSeries.constantCoeff (φ b) = e b)
    (h₂ : ∀ j, φ (π (MvPolynomial.X j) - algebraMap O B (e (π (MvPolynomial.X j)))) = MvPowerSeries.X j)
    {T : Type} [CommRing T] [Algebra O T] (J : Ideal T) [IsAdicComplete J T] (ψ : B →ₐ[O] T)
    (hψ : ∀ b, ψ b - algebraMap O T (e b) ∈ J) :
    ∃ v : MvPowerSeries (Fin g) O →ₐ[O] T, (∀ i, v (MvPowerSeries.X i) ∈ J) ∧ v.comp φ = ψ := by
  let v := GlobalTheory.mvEvalAdic O J (fun j => ψ (π (MvPolynomial.X j)) - algebraMap O T (e (π (MvPolynomial.X j))))
    (fun j => hψ _)
  have hv : ∀ j, v (MvPowerSeries.X j) =
      ψ (π (MvPolynomial.X j)) - algebraMap O T (e (π (MvPolynomial.X j))) := fun j =>
    GlobalTheory.mvEvalAdic_X _ _ _ j
  have hv' : ∀ j, v (MvPowerSeries.X j) ∈ J := fun j => hv j ▸ hψ _
  refine ⟨v, hv', ext_of_isHausdorff π hπ J _ _ (fun b => ?_) (fun j => ?_)⟩
  · have := GlobalTheory.algHom_sub_constantCoeff_mem v hv' (φ b)
    rw [h₁] at this
    have h3 := sub_mem this (hψ b)
    rwa [sub_sub_sub_cancel_right] at h3
  · have := hv j
    rw [← h₂, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj] at this
    exact this

end Alg

section Geo
open GlobalTheory.KeyKa.EtBaseChange

variable {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {T : Type} [CommRing T]

theorem spMap_valH (w : Sp T ⟶ X) (hw : ⊤ ≤ w ⁻¹ᵁ V) :
    spMap (R := Γ(X, V)) (valH w V hw) ≫ hV.fromSpec = w := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec w hV (isAffineOpen_top (Spec (CommRingCat.of T))) hw
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  show Spec.map (w.appLE V ⊤ hw ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom) ≫ hV.fromSpec = w
  rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem le_preimage (φ : Γ(X, V) →+* T) : ⊤ ≤ (spMap (R := Γ(X, V)) φ ≫ hV.fromSpec) ⁻¹ᵁ V :=
  fun _ _ => hV.range_fromSpec.subset (Set.mem_range_self _)

theorem valH_spMap (φ : Γ(X, V) →+* T) :
    valH (spMap (R := Γ(X, V)) φ ≫ hV.fromSpec) V (le_preimage hV φ) = φ := by
  have h := spMap_valH hV _ (le_preimage hV φ)
  rw [cancel_mono] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (f' : R' →+* R'') : spMap (f'.comp f) = spMap f' ≫ spMap f := by
  rw [← Spec.map_comp]
  rfl

theorem fromSpec_comp {O : Type} [CommRing O] (h : X ⟶ Sp O) :
    hV.fromSpec ≫ h = spMap (R' := Γ(X, V))
      ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ h.appLE ⊤ V le_top).hom := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec h (isAffineOpen_top (Spec (CommRingCat.of O))) hV
    (le_top : V ≤ h ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  rw [← e, ← Spec.map_comp]
  rfl

theorem le_preimage_of_closedPoint [IsLocalRing T] (w : Sp T ⟶ X)
    (hw : w (IsLocalRing.closedPoint T) ∈ V) : ⊤ ≤ w ⁻¹ᵁ V := fun p _ =>
  ((IsLocalRing.specializes_closedPoint p).map w.continuous).mem_open V.isOpen hw

end Geo

open GlobalTheory.KeyKa.EtBaseChange in
theorem exists_formal_chart : ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Scheme.{0}) (h : X ⟶ Sp O) (g : ℕ) (z : Sp O ⟶ X), SmoothOfRelativeDimension g h → z ≫ h = 𝟙 _ → ∃ θ : Sp (MvPowerSeries (Fin g) O) ⟶ X, θ (IsLocalRing.closedPoint (MvPowerSeries (Fin g) O)) = z (IsLocalRing.closedPoint O) ∧ θ ≫ h = spMap (algebraMap O (MvPowerSeries (Fin g) O)) ∧ (∃ (V : X.Opens) (t : Fin g → Γ(X, V)), ⊤ ≤ θ ⁻¹ᵁ V ∧ ∀ i, valT (T := (MvPowerSeries (Fin g) O)) θ V (t i) = MvPowerSeries.X i) ∧ (∀ (T : Type) [CommRing T] [IsLocalRing T] [Algebra O T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T] (w : Sp T ⟶ X), w ≫ h = spMap (algebraMap O T) → w (IsLocalRing.closedPoint T) = θ (IsLocalRing.closedPoint (MvPowerSeries (Fin g) O)) → ∃ e : (MvPowerSeries (Fin g) O) →ₐ[O] T, (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal T) ∧ spMap e.toRingHom ≫ θ = w) := by
  intro O _ _ X h g z hG hz
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ :=
    hG.exists_isStandardSmoothOfRelativeDimension (z (IsLocalRing.closedPoint O))
  have hU' : U = ⊤ := by
    have h1 : (z ≫ h) (IsLocalRing.closedPoint O) ∈ U :=
      (Scheme.Hom.comp_apply z h (IsLocalRing.closedPoint O)).symm ▸ e hx
    have h2 := le_preimage_of_closedPoint (z ≫ h) h1
    rw [hz] at h2
    exact eq_top_iff.2 h2
  subst hU'
  let a : O →+* Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ h.appLE ⊤ V le_top).hom
  have ha : hV.fromSpec ≫ h = spMap (R' := Γ(X, V)) a := fromSpec_comp hV h
  have h2 : RingHom.IsStandardSmoothOfRelativeDimension g a :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv hs
  obtain ⟨π₀, hπ1, hπ⟩ := h2.exists_etale_mvPolynomial
  clear_value a
  letI : Algebra O Γ(X, V) := a.toAlgebra
  let π : MvPolynomial (Fin g) O →ₐ[O] Γ(X, V) := { π₀ with commutes' := fun r => RingHom.congr_fun hπ1 r }
  have hpt : ∀ (T : Type) [CommRing T] [Algebra O T] (w : Sp T ⟶ X), ⊤ ≤ w ⁻¹ᵁ V →
      w ≫ h = spMap (algebraMap O T) →
      ∃ ψ : Γ(X, V) →ₐ[O] T, spMap (R := Γ(X, V)) ψ.toRingHom ≫ hV.fromSpec = w := by
    intro T _ _ w hw hw'
    have e1 := spMap_valH hV w hw
    have e2 : spMap ((valH w V hw).comp a) = spMap (algebraMap O T) := by
      rw [spMap_comp, ← ha, ← Category.assoc, e1, hw']
    have e3 : (valH w V hw).comp a = algebraMap O T :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
    exact ⟨⟨valH w V hw, fun r => RingHom.congr_fun e3 r⟩, e1⟩
  obtain ⟨ε, rfl⟩ := hpt O z (le_preimage_of_closedPoint z hx) (hz.trans (Spec.map_id _).symm)
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists_expansion π hπ ε
  have hcl : (spMap (R := Γ(X, V)) φ.toRingHom ≫ hV.fromSpec)
      (IsLocalRing.closedPoint (MvPowerSeries (Fin g) O)) =
      (spMap (R := Γ(X, V)) ε.toRingHom ≫ hV.fromSpec) (IsLocalRing.closedPoint O) := by
    refine congrArg hV.fromSpec (PrimeSpectrum.ext (Ideal.ext fun b => ?_))
    show φ b ∈ IsLocalRing.maximalIdeal _ ↔ ε b ∈ IsLocalRing.maximalIdeal _
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff, hφ₁]
  refine ⟨spMap (R := Γ(X, V)) φ.toRingHom ≫ hV.fromSpec, hcl, ?_,
    ⟨V, fun j => π (MvPolynomial.X j) - algebraMap O _ (ε (π (MvPolynomial.X j))), le_preimage hV _,
      fun j => ?_⟩, ?_⟩
  · rw [Category.assoc, ha, ← spMap_comp]
    exact congrArg spMap φ.comp_algebraMap
  · rw [valT_eq _ _ (le_preimage hV _), valH_spMap]
    exact hφ₂ j
  · intro T _ _ _ _ w hw hw'
    rw [hcl] at hw'
    obtain ⟨ψ, rfl⟩ := hpt T w (le_preimage_of_closedPoint w (hw' ▸ hx)) hw
    have h3 := congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective hw')
    obtain ⟨v, hv, rfl⟩ := exists_factor π hπ ε φ hφ₁ hφ₂ (IsLocalRing.maximalIdeal T) ψ fun b => by
      have h4 : b - algebraMap O _ (ε b) ∈ (IsLocalRing.maximalIdeal O).comap ε.toRingHom := by
        show ε (b - algebraMap O _ (ε b)) ∈ IsLocalRing.maximalIdeal O
        simp
      have h5 : ψ (b - algebraMap O _ (ε b)) ∈ IsLocalRing.maximalIdeal T := h3.ge h4
      rwa [map_sub, AlgHom.commutes] at h5
    refine ⟨v, hv, ?_⟩
    rw [← Category.assoc, ← spMap_comp]
    rfl

end GlobalTheory.FormalChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLevelIffAut
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.SimilTheta
open Matrix

variable {g : ℕ}

def lat (τ : Matrix (Fin g) (Fin g) ℂ) (k n : Fin g → ℤ) : Fin g → ℂ :=
  (fun i => (k i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))

def aut (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (k n : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a ⬝ᵥ (fun i => (k i : ℂ)) - b ⬝ᵥ (fun i => (n i : ℂ)) -
    ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ))) / 2 - (fun i => (n i : ℂ)) ⬝ᵥ z))

def tors (τ : Matrix (Fin g) (Fin g) ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (r : Fin 4) :
    Fin g → ℂ := (m : ℂ)⁻¹ • ∑ c, al r c • lat τ (k c) (n c)

def simTheta (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ)
    (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ) : ℂ :=
  (∏ r, thetaChar τ a b (∑ c, al r c • y c + tors τ al m k n r)) *
    Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c)

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.SimilTheta.aut_ne_zero (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (k n : Fin g → ℤ) (z : Fin g → ℂ) :
    _root_.GlobalTheory.SimilTheta.aut τ a b k n z ≠ 0 :=
  Complex.exp_ne_zero _

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.SimilTheta.isLevel_iff_aut (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (l : ℕ) (F : (Fin g → ℂ) → ℂ) :
    _root_.GlobalTheory.KeyKa.IsLevel τ a b l F ↔ Differentiable ℂ F ∧ ∀ k n z, F (z + _root_.GlobalTheory.SimilTheta.lat τ k n) = _root_.GlobalTheory.SimilTheta.aut τ a b k n z ^ l * F z :=
  Iff.rfl

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.SimilTheta.lat_add (τ : Matrix (Fin g) (Fin g) ℂ) (k n k' n' : Fin g → ℤ) :
    _root_.GlobalTheory.SimilTheta.lat τ (k + k') (n + n') = _root_.GlobalTheory.SimilTheta.lat τ k n + _root_.GlobalTheory.SimilTheta.lat τ k' n' := by
  have h : (fun i => ((n + n') i : ℂ)) = (fun i => (n i : ℂ)) + fun i => (n' i : ℂ) := by
    ext i; simp
  unfold _root_.GlobalTheory.SimilTheta.lat
  rw [h, Matrix.mulVec_add]
  ext i
  simp only [Pi.add_apply, Int.cast_add]
  ring

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.SimilTheta.lat_zsmul (τ : Matrix (Fin g) (Fin g) ℂ) (s : ℤ) (k n : Fin g → ℤ) :
    _root_.GlobalTheory.SimilTheta.lat τ (s • k) (s • n) = s • _root_.GlobalTheory.SimilTheta.lat τ k n := by
  have h : (fun i => ((s • n) i : ℂ)) = (s : ℂ) • fun i => (n i : ℂ) := by
    ext i; simp
  unfold _root_.GlobalTheory.SimilTheta.lat
  rw [h, Matrix.mulVec_smul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_mul]
  ring

attribute [local instance] Over.cartesianMonoidalCategory in
private theorem lat_zero_zero (τ : Matrix (Fin g) (Fin g) ℂ) :
    _root_.GlobalTheory.SimilTheta.lat τ 0 0 = 0 := by
  have h : (fun i : Fin g => (((0 : Fin g → ℤ) i : ℤ) : ℂ)) = 0 := by
    ext i; simp
  unfold _root_.GlobalTheory.SimilTheta.lat
  rw [h, Matrix.mulVec_zero]
  ext i
  simp

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.SimilTheta.lat_sum (τ : Matrix (Fin g) (Fin g) ℂ) {K : Type} (s : Finset K) (k n : K → Fin g → ℤ) :
    _root_.GlobalTheory.SimilTheta.lat τ (∑ c ∈ s, k c) (∑ c ∈ s, n c) = ∑ c ∈ s, _root_.GlobalTheory.SimilTheta.lat τ (k c) (n c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lat_zero_zero τ
  | insert c s hc ih =>
    rw [Finset.sum_insert hc, Finset.sum_insert hc, Finset.sum_insert hc, _root_.GlobalTheory.SimilTheta.lat_add, ih]

end GlobalTheory.SimilTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SignInsert
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KeyKa.KoszulCx
section Alg
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}

theorem sign_insert (I : Finset (Fin g)) {i i' : Fin g} (hi : i ∉ I) :
    ((-1 : R)) ^ ((insert i I).filter (· < i')).card =
      (if i < i' then -1 else 1) * (-1) ^ (I.filter (· < i')).card := by
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun h' => hi (Finset.mem_filter.1 h').1), pow_succ']
  · rw [_root_.one_mul]

theorem kosD_deg (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (p q : KIx g d N) (h : kdeg q ≠ kdeg p + 1) : kosD m ev p q = 0 := by
  rcases p with p | p <;> rcases q with q | q
  · simp only [kosD]
    refine Finset.sum_eq_zero fun i _ => if_neg ?_
    rintro ⟨hi, hq⟩
    apply h
    simp [kdeg, hq, Finset.card_insert_of_notMem hi]
  · rfl
  · simp only [kosD]
    refine if_neg fun hq => h ?_
    simp [kdeg, hq]
  · rfl

theorem isCx_kosD (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (hc : ∀ i i' j, j + 2 ≤ g → m i j (j + 1) * m i' (j + 1) (j + 2) = m i' j (j + 1) * m i (j + 1) (j + 2))
    (he : ∀ i, ev 0 * m i 0 (0 + 1) = 0) : IsCx kdeg (kosD m ev) := by
  have hc' : ∀ i i' j j₁ j₁' j₂, j₁ = j + 1 → j₁' = j + 1 → j₂ = j + 2 → j₂ ≤ g →
      m i j j₁ * m i' j₁ j₂ = m i' j j₁' * m i j₁' j₂ := by
    rintro i i' j _ _ _ rfl rfl rfl h
    exact hc i i' j h
  have he' : ∀ i j j₁, j = 0 → j₁ = 0 + 1 → ev j * m i j j₁ = 0 := by
    rintro i _ _ rfl rfl
    exact he i
  refine ⟨kosD_deg m ev, ?_⟩
  ext p r
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.zero_apply]
  rcases r with ⟨K, c⟩ | r
  swap
  · rcases p with p | p <;> simp [kosD]
  rcases p with ⟨I, a⟩ | a
  · have h2 : ∑ q : Fin d, kosD m ev (.inl ⟨I, a⟩) (.inr q) * kosD m ev (.inr q) (.inl ⟨K, c⟩) = 0 := by
      simp [kosD]
    rw [h2, add_zero, Fintype.sum_sigma]
    let T : Fin g → Fin g → R := fun i i' =>
      if i ∉ I ∧ i' ∉ insert i I ∧ K = insert i' (insert i I) then
        (-1) ^ (I.filter (· < i)).card * (-1) ^ ((insert i I).filter (· < i')).card *
          (m i I.card (insert i I).card * m i' (insert i I).card K.card) a c else 0
    have h3 : ∀ J : Finset (Fin g), ∑ k : Fin (N J.card),
        kosD m ev (.inl ⟨I, a⟩) (.inl ⟨J, k⟩) * kosD m ev (.inl ⟨J, k⟩) (.inl ⟨K, c⟩) =
        ∑ i, if J = insert i I then ∑ i', T i i' else 0 := by
      intro J
      simp only [kosD, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hJ : J = insert i I
      · subst hJ
        rw [if_pos rfl]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i' _ => ?_
        by_cases hi : i ∉ I
        · by_cases hi' : i' ∉ insert i I ∧ K = insert i' (insert i I)
          · simp only [T]
            rw [if_pos ⟨hi, hi'⟩, Matrix.mul_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [if_pos ⟨hi, trivial⟩, if_pos hi']
            ring
          · simp only [T]
            rw [if_neg (fun h => hi' h.2)]
            exact Finset.sum_eq_zero fun k _ => by rw [if_neg hi', mul_zero]
        · simp only [T]
          rw [if_neg (fun h => hi h.1)]
          exact Finset.sum_eq_zero fun k _ => by rw [if_neg (fun h => hi h.1), zero_mul]
      · rw [if_neg hJ]
        exact Finset.sum_eq_zero fun k _ => by rw [if_neg (fun h => hJ h.2), zero_mul]
    rw [Finset.sum_congr rfl fun J _ => h3 J, Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Fintype.sum_prod_type']
    have hT : ∀ i i', T i i' + T i' i = 0 := by
      intro i i'
      by_cases h : i ∉ I ∧ i' ∉ insert i I ∧ K = insert i' (insert i I)
      · obtain ⟨h1, h2, h3⟩ := h
        have hne : i' ≠ i := fun e => h2 (e ▸ Finset.mem_insert_self _ _)
        have h4 : i' ∉ I := fun e => h2 (Finset.mem_insert_of_mem e)
        have h5 : i ∉ insert i' I := by simp [h1, hne.symm]
        have h6 : K = insert i (insert i' I) := h3.trans (Finset.insert_comm _ _ _)
        have hK : K.card = I.card + 2 := by
          rw [h3, Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1]
        have hg : K.card ≤ g := by simpa using Finset.card_le_univ K
        simp only [T]
        rw [if_pos ⟨h1, h2, h3⟩, if_pos ⟨h4, h5, h6⟩, sign_insert I h1, sign_insert I h4,
          hc' i i' _ _ _ _ (Finset.card_insert_of_notMem h1) (Finset.card_insert_of_notMem h4) hK hg]
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · rw [if_pos hlt, if_neg hlt.not_gt]; ring
        · rw [if_pos hlt, if_neg hlt.not_gt]; ring
      · have h' : ¬ (i' ∉ I ∧ i ∉ insert i' I ∧ K = insert i (insert i' I)) := by
          rintro ⟨h1, h2, h3⟩
          have hne : i ≠ i' := fun e => h2 (e ▸ Finset.mem_insert_self _ _)
          exact h ⟨fun e => h2 (Finset.mem_insert_of_mem e), by simp [h1, hne.symm],
            h3.trans (Finset.insert_comm _ _ _)⟩
        simp only [T]
        rw [if_neg h, if_neg h', add_zero]
    refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => hT p.1 p.2) ?_ (fun _ _ => Finset.mem_univ _)
      (fun p _ => Prod.swap_swap p)
    rintro ⟨i, i'⟩ _ h e
    apply h
    obtain rfl : i' = i := congrArg Prod.fst e
    exact if_neg fun h => h.2.1 (Finset.mem_insert_self _ _)
  · have h2 : ∑ q : Fin d, kosD m ev (.inr a) (.inr q) * kosD m ev (.inr q) (.inl ⟨K, c⟩) = 0 := by
      simp [kosD]
    rw [h2, add_zero, Fintype.sum_sigma]
    refine Finset.sum_eq_zero fun J _ => ?_
    simp only [kosD]
    by_cases hJ : J = ∅
    · simp only [if_pos hJ, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h : i ∉ J ∧ K = insert i J
      · simp only [if_pos h]
        have e := congrFun (congrFun (he' i J.card K.card (by simp [hJ]) (by simp [h.2, hJ])) a) c
        rw [Matrix.mul_apply, Matrix.zero_apply] at e
        rw [← mul_zero ((-1 : R) ^ (J.filter (· < i)).card), ← e, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      · simp only [if_neg h, mul_zero, Finset.sum_const_zero]
    · simp only [if_neg hJ, zero_mul, Finset.sum_const_zero]

end Alg

section Geo
variable {R : Type} [CommRing R]

def mulSec {X : Scheme.{0}} (L : LB X) {a b c : ℤ} (h : c = a + b) (s : LB.Sec (pw L a)) (t : LB.Sec (pw L b)) :
    LB.Sec (pw L c) where
  f := fun i => (show Γ(X, L.U i) from s.f i) * (show Γ(X, L.U i) from t.f i)
  compat := fun i j => by
    have hs : rs X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (s.f i) =
      ((L.g i j ^ a : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) * rs X inf_le_right (s.f j) := s.compat i j
    have ht : rs X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (t.f i) =
      ((L.g i j ^ b : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) * rs X inf_le_right (t.f j) := t.compat i j
    change rs X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (_ * _) =
      ((L.g i j ^ c : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) * rs X (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (_ * _)
    rw [map_mul, map_mul]
    erw [hs, ht]
    rw [h, zpow_add, Units.val_mul]
    exact mul_mul_mul_comm _ _ _ _

theorem valH_cst (x : KeyIn R) (z : Pt x) (U : x.P.A.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ U) (c : R) :
    valT (T := R) z.left U (cst x.P.A.hom U c) = c := by
  have h0 : valT (T := R) z.left U (cst x.P.A.hom U c) =
      valT (T := R) z.left U ((x.P.A.hom.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := rfl
  refine h0.trans ((EtBaseChange.valT_appLE (T := R) z.left x.P.A.hom (U := ⊤) le_top h _).trans ?_)
  have hz : z.left ≫ x.P.A.hom = 𝟙 (Sp R) := Over.w z
  erw [hz]
  rw [EtBaseChange.valT_eq _ _ le_top]
  have e3 : Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ le_top = 𝟙 _ := by
    rw [← Scheme.Hom.id_appTop]; exact Scheme.Hom.appLE_eq_app _
  unfold EtBaseChange.valH
  erw [e3]
  simp

theorem cast_step {g n l j : ℕ} (h : g * n < l) (hj : j < g) :
    ((l - j * n : ℕ) : ℤ) = (n : ℤ) + ((l - (j + 1) * n : ℕ) : ℤ) := by
  have : (j + 1) * n ≤ g * n := Nat.mul_le_mul_right _ hj
  have h2 : (j + 1) * n = j * n + n := Nat.succ_mul _ _
  omega

theorem ring_coords {A S₀ S₁ : Type} [CommRing A] [Fintype S₀] [Fintype S₁] (φ : R →+* A) (b₀ : S₀ → A) (b₁ : S₁ → A)
    (M : Matrix S₀ S₁ R) (u f : A) (c : S₁ → R) (h2 : ∀ k, u * b₁ k = ∑ k', φ (M k' k) * b₀ k')
    (h1 : f = ∑ k, φ (c k) * b₁ k) : u * f = ∑ k', φ (∑ k, M k' k * c k) * b₀ k' := by
  rw [h1, Finset.mul_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h2 k, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k' _ => by ring

theorem ring_eval {A S : Type} [CommRing A] [Fintype S] (φ : R →+* A) (v : A → R) (ψ : A →+* R) (hv : ∀ a, v a = ψ a)
    (hc : ∀ c, v (φ c) = c) (b : S → A) (u f : A) (c : S → R) (hu : v u = 0) (h : u * f = ∑ k, φ (c k) * b k) :
    ∑ k, v (b k) * c k = 0 := by
  obtain rfl : v = ψ := funext hv
  have e := congrArg ψ h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_sum, hu, zero_mul] at e
  simp only [map_mul, hc] at e
  exact Eq.trans (Finset.sum_congr rfl fun k' _ => mul_comm _ _) e.symm

theorem coords_mul (x : KeyIn R) {l₀ l₁ N₀ N₁ : ℕ} (b₀ : Fin N₀ → RR x l₀) (b₁ : Fin N₁ → RR x l₁)
    (M : Matrix (Fin N₀) (Fin N₁) R) (u f : ∀ i, Γ(x.P.A.left, x.P.L.U i)) (c : Fin N₁ → R)
    (hM : ∀ k, Coords x b₀ (fun k' => M k' k) (fun i => u i * (show Γ(x.P.A.left, x.P.L.U i) from (b₁ k).f i)))
    (hc : Coords x b₁ c f) : Coords x b₀ (fun k' => ∑ k, M k' k * c k) (fun i => u i * f i) := by
  exact fun i => ring_coords (cst x.P.A.hom (x.P.L.U i)) _ _ M (u i) (f i) c (fun k => hM k i) (hc i)

theorem koszul_isCx : ∀ (R : Type) [CommRing R] (x : KeyIn R) (n l d : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → (∃ m, IsMul x l s b m) ∧ ∀ m, IsMul x l s b m → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := R) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → IsCx kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m (fun j => Matrix.of fun a k => valT (T := R) (z a).left (x.P.L.U (ch a)) ((b j k).f (ch a)))) := by
  intro R _ x n l d s b z ch hl hb
  refine ⟨?_, fun m hm hz hs => ?_⟩
  · have h1 : ∀ i j, ∀ k : Fin ((l - (j + 1) * n) ^ x.P.g), ∃ c : Fin ((l - j * n) ^ x.P.g) → R, j < x.P.g →
        Coords x (b j) c (fun c => (show Γ(x.P.A.left, x.P.L.U c) from (s i).f c) *
          (show Γ(x.P.A.left, x.P.L.U c) from (b (j + 1) k).f c)) := by
      intro i j k
      by_cases hj : j < x.P.g
      · obtain ⟨c, hc, -⟩ := hb j hj.le (mulSec x.P.L (cast_step hl hj) (s i) (b (j + 1) k))
        exact ⟨c, fun _ => hc⟩
      · exact ⟨0, fun h => absurd h hj⟩
    choose c hc using h1
    refine ⟨fun i j j' => if h : j' = j + 1 then Matrix.of fun k' k => c i j (h ▸ k) k' else 0, fun i j hj k => ?_⟩
    simp only [dif_pos, Matrix.of_apply]
    exact hc i j k hj
  · refine isCx_kosD (N := fun j => (l - j * n) ^ x.P.g) m _ (fun i i' j hj => ?_) (fun i => ?_)
    · ext k' k
      have hj0 : j < x.P.g := by omega
      have hj1 : j + 1 < x.P.g := by omega
      have e₁ := coords_mul x (b j) (b (j + 1)) (m i j (j + 1)) _ _ _ (hm i j hj0) (hm i' (j + 1) hj1 k)
      have e₂ := coords_mul x (b j) (b (j + 1)) (m i' j (j + 1)) _ _ _ (hm i' j hj0) (hm i (j + 1) hj1 k)
      have hu := hb j hj0.le (mulSec x.P.L (cast_step hl hj0) (s i)
        (mulSec x.P.L (cast_step hl hj1) (s i') (b (j + 2) k)))
      have e₃ := hu.unique e₁ (fun c => (mul_left_comm _ _ _).trans (e₂ c))
      exact congrFun e₃ k'
    · ext a k
      exact ring_eval (cst x.P.A.hom (x.P.L.U (ch a))) (valT (T := R) (z a).left (x.P.L.U (ch a))) _
        (EtBaseChange.valT_eq (T := R) (z a).left _ (hz a)) (valH_cst x (z a) _ (hz a)) _ _ _ _ (hs a i)
        (hm i 0 i.pos k (ch a))

end Geo
end GlobalTheory.KeyKa.KoszulCx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalAtIffWit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KeyKa

theorem normalAt_iff_wit : ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin g → ℂ), NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 ↔ ∃ u : HolUnif x.P.A x.P.L g, Wit x h u (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm)) a b := by
  intro g x h τ a b
  subst h
  exact normalAt_one_iff ..

end GlobalTheory.KeyKa
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsLevBasisReal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa.LevelBasis

section Real
open ReciprocityTheory.PTheta Matrix

theorem isLevel_iff {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (l : ℕ) (F : (Fin g → ℂ) → ℂ) :
    IsLevel τ (ofRealVec a) (ofRealVec b) l F ↔ F ∈ thetaLevelChar a b l τ := by
  have key : ∀ (m n : Fin g → ℤ) (z : Fin g → ℂ),
      Complex.exp (2 * Real.pi * Complex.I * (ofRealVec a ⬝ᵥ (fun i => (m i : ℂ)) - ofRealVec b ⬝ᵥ (fun i => (n i : ℂ)) -
        ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ))) / 2 - (fun i => (n i : ℂ)) ⬝ᵥ z)) ^ l =
      eC ((l : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec m - ofRealVec b ⬝ᵥ ofIntVec n)) *
        eC (-(l : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) := by
    intro m n z
    unfold eC
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    unfold ofIntVec
    ring
  have e : ∀ (m n : Fin g → ℤ) (z : Fin g → ℂ),
      z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) = z + τ *ᵥ ofIntVec n + ofIntVec m := by
    intro m n z
    unfold ofIntVec
    abel
  rw [mem_thetaLevelChar]
  refine and_congr Iff.rfl ⟨fun h n m z => ?_, fun h m n z => ?_⟩
  · rw [← key, ← e]; exact h m n z
  · rw [key, e]; exact h n m z

theorem holFam_levelTheta {g : ℕ} (a b : Fin g → ℝ) {l : ℕ} (hl : 0 < l) (c : Fin g → ℤ) :
    HolFam (Key.phDom g) (fun p => levelTheta a b l (per p) c) := by
  have H := thetaHolo_of_domainOpen_of_mTest siegelSubDomain_and_domainOpen.2 thetaMTest_holds (Fin g)
    ((fun i => (c i : ℝ) / l) + a) ((l : ℝ) • b)
  have hd : Differentiable ℂ (fun q : (Fin g → Fin g → ℂ) × (Fin g → ℂ) =>
      (((l : ℂ) • q.2, fun i j => (l : ℂ) * ((1 / 2 : ℂ) * (q.1 i j + q.1 j i))) :
        (Fin g → ℂ) × (Fin g → Fin g → ℂ))) := by
    fun_prop
  refine (H.comp hd.differentiableOn fun q hq => ?_).congr fun q _ => rfl
  exact siegelSubDomain_and_domainOpen.1 _ (smul_mem_siegelH hq.1 hl)

theorem exists_levBasis_real (g : ℕ) (a b : Fin g → ℝ) {l : ℕ} (hl : 0 < l) :
    ∃ Th : Fin (l ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ, LevBasis (ofRealVec a) (ofRealVec b) l Th := by
  let e : Fin (l ^ g) ≃ (Fin g → Fin l) := finFunctionFinEquiv.symm
  let r : Fin (l ^ g) → Fin g → ℤ := fun k i => ((e k i : ℕ) : ℤ)
  have hr : Function.Bijective fun k i => (r k i : ZMod l) := (@GlobalTheory.bijective_fin_zmod (Fin g) l hl).comp e.bijective
  refine ⟨fun k p => levelTheta a b l (per p) (r k), fun k => holFam_levelTheta a b hl _, fun p hp =>
    ⟨fun k => (isLevel_iff _ _ _ _ _).2 (levelTheta_mem hp hl _), fun F hF => ?_⟩⟩
  let B := thetaLevelCharBasis a b (τ := per p) hp hl hr
  have hF' := (isLevel_iff _ _ _ _ _).1 hF
  have hB : ∀ (c : Fin (l ^ g) → ℂ) z, ((∑ k, c k • B k : thetaLevelChar a b l (per p)) : (Fin g → ℂ) → ℂ) z =
      ∑ k, c k * levelTheta a b l (per p) (r k) z := fun c z => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact congrArg _ (congrFun (thetaLevelCharBasis_apply (τ := per p) hp hl hr k) z)
  refine ⟨fun k => B.repr ⟨F, hF'⟩ k, fun z => ?_, fun c hc => ?_⟩
  · rw [← hB, B.sum_repr]
  · have : (⟨F, hF'⟩ : thetaLevelChar a b l (per p)) = ∑ k, c k • B k := Subtype.ext (funext fun z => by
      rw [hB]; exact hc z)
    funext k
    rw [this, B.repr_sum_self]

end Real

theorem exists_levBasis : ∀ (g : ℕ) (a b : Fin g → ℂ) (l : ℕ), charHalf g a b → 1 ≤ l → ∃ Th : Fin (l ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ, LevBasis a b l Th := by
  intro g a b l h hl
  have := exists_levBasis_real g (fun i => (a i).re) (fun i => (b i).re) (l := l) hl
  rwa [TorusAlg.ofRealVec_re h.1, TorusAlg.ofRealVec_re h.2] at this

end GlobalTheory.KeyKa.LevelBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.UnifValueJacZeros
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.UnifJac

theorem valT_comp {T : Type} [CommRing T] {X Y : Scheme.{0}} (w : Sp T ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (f : Γ(Y, U)) : valT (w ≫ φ) U f = valT w (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  unfold valT
  by_cases h : ⊤ ≤ w ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [dif_pos h, dif_pos (show ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U from h)]
    rfl
  · rw [dite_eq_right h, dite_eq_right (show ¬ ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U from h)]

variable {A : Over (Sp ℂ)} [GrpObj A]

theorem translate_left {T : Over (Sp ℂ)} (z : 𝟙_ (Over (Sp ℂ)) ⟶ A) (v : T ⟶ A) :
    ((toUnit T ≫ z) * v).left = v.left ≫ ((toUnit A ≫ z) * 𝟙 A).left := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem le_of_isTangent {v : epsR ℂ ⟶ A} (hv : IsTangent v) (U : A.left.Opens)
    (h : ⊤ ≤ η[A].left ⁻¹ᵁ U) : ⊤ ≤ v.left ⁻¹ᵁ U := by
  intro p _
  have hp : p = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (IsLocalRing.closedPoint ℂ) := by
    have : Subsingleton (PrimeSpectrum (DualNumber ℂ)) := by
      refine ⟨fun a b => ?_⟩
      have hn : ∀ c : PrimeSpectrum (DualNumber ℂ), c.asIdeal = IsLocalRing.maximalIdeal _ := fun c => by
        refine le_antisymm (IsLocalRing.le_maximalIdeal c.isPrime.ne_top) ?_
        rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_le_iff_mem]
        exact c.isPrime.mem_of_pow_mem 2 (by rw [sq, DualNumber.eps_mul_eps]; exact zero_mem _)
      exact PrimeSpectrum.ext ((hn a).trans (hn b).symm)
    exact Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) _ _
  have h1 : η[A].left (IsLocalRing.closedPoint ℂ) ∈ U := h (show _ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  rw [← hv] at h1
  rw [hp]
  exact h1

variable {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

theorem ex_translate (z w : Fin g → ℂ) :
    (u.ex w).left ≫ ((toUnit A ≫ u.ex z) * 𝟙 A).left = (u.ex (z + w)).left := by
  rw [← translate_left, u.ex_add, toUnit_unique (toUnit (𝟙_ (Over (Sp ℂ)))) (𝟙 _), Category.id_comp]

theorem snd_valT_translate {v : epsR ℂ ⟶ A} (hv : IsTangent v) {w : Fin g → ℂ} (hd : u.IsDiff w v)
    (z : Fin g → ℂ) (U : A.left.Opens) (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    TrivSqZeroExt.snd (valT (T := DualNumber ℂ) ((toUnit (epsR ℂ) ≫ u.ex z) * v).left U f) =
      fderiv ℂ (fun y => valAt' (u.ex y).left U f) z w := by
  have h0 : ⊤ ≤ η[A].left ⁻¹ᵁ (((toUnit A ≫ u.ex z) * 𝟙 A).left ⁻¹ᵁ U) := by
    have e := ex_translate u z 0
    rw [add_zero, ex_zero] at e
    rw [← e] at hz
    have e1 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) = η[A] := by
      rw [Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over (Sp ℂ)))) (𝟙 _), Category.id_comp]
    rw [e1] at hz
    exact hz
  have h1 := le_of_isTangent hv _ h0
  rw [translate_left]
  refine (congrArg _ (valT_comp _ _ _ _)).trans ?_
  refine (congrArg TrivSqZeroExt.snd (dif_pos h1)).trans ((hd _ h1 _).trans ?_)
  have e : (fun y => valAt' (u.ex y).left (((toUnit A ≫ u.ex z) * 𝟙 A).left ⁻¹ᵁ U)
      ((((toUnit A ≫ u.ex z) * 𝟙 A).left.app U).hom f)) = fun y => valAt' (u.ex (z + y)).left U f := by
    funext y
    rw [← ex_translate]
    exact (valT_comp (T := ℂ) _ _ _ _).symm
  rw [e, fderiv_comp_add_left (f := fun y => valAt' (u.ex y).left U f), add_zero]

theorem fderiv_val (c : L.ι) (f : Γ(A.left, L.U c)) (F : (Fin g → ℂ) → ℂ) (hF : Differentiable ℂ F) (n : ℕ)
    (hf : ∀ y, ⊤ ≤ (u.ex y).left ⁻¹ᵁ L.U c → valAt' (u.ex y).left (L.U c) f = F y * u.fr c y ^ n)
    (z : Fin g → ℂ) (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U c) (h0 : F z = 0) (w : Fin g → ℂ) :
    fderiv ℂ (fun y => valAt' (u.ex y).left (L.U c) f) z w = u.fr c z ^ n * fderiv ℂ F z w := by
  have hn := (u.hol (L.U c) f).1.mem_nhds hz
  have e : (fun y => valAt' (u.ex y).left (L.U c) f) =ᶠ[nhds z] fun y => F y * u.fr c y ^ n :=
    Filter.eventually_of_mem hn hf
  have hd : DifferentiableAt ℂ (fun y => u.fr c y ^ n) z := ((u.fr_hol c).differentiableAt hn).pow n
  rw [e.fderiv_eq, fderiv_fun_mul (hF z) hd, h0]
  simp

end GlobalTheory.UnifJac

namespace GlobalTheory

open UnifJac in
theorem unif_value_jac_zeros : ThetaUnifAV → ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (n : ℕ) (s : Fin x.P.g → RR x n) (F : Fin x.P.g → (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) (c : x.P.L.ι), Wit x h u τ a b → (∀ i, Differentiable ℂ (F i) ∧ FnPw x u (s i) (F i)) → ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U c → (∀ i, valT (T := ℂ) (u.ex z).left (x.P.L.U c) ((s i).f c) = F i z * u.fr c z ^ n) ∧ ((∀ i, F i z = 0) → jac x s (u.ex z) c = u.fr c z ^ (g * n) * (Matrix.of fun i k : Fin x.P.g => (2 * Real.pi * Complex.I)⁻¹ * fderiv ℂ (F i) z (Pi.single (k.cast h) 1)).det) ∧ ∀ (d : ℕ) (zs : Fin d → Fin g → ℂ), (∀ y, (∀ i, F i y = 0) → ∃ a, ∃ e ∈ u.Λ, y = zs a + e) → ∀ y : x.P.A.left, (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp ℂ, (u.ex (zs a)).left p = y := by
  intro _ g x h u τ a b n s F z c hW hF hz
  refine ⟨fun i => (hF i).2 c z hz, fun h0 => ?_, fun d zs hzs y hy => ?_⟩
  · subst h
    unfold jac
    rw [mul_comm x.P.g n, pow_mul, show (u.fr c z ^ n) ^ x.P.g = (u.fr c z ^ n) ^ Fintype.card (Fin x.P.g) by
      rw [Fintype.card_fin], ← Matrix.det_smul]
    congr 1
    ext i k
    have hd := hW.2.2.2.2.2 k
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    refine (snd_valT_translate u (x.basis.1 k) hd z _ hz _).trans ?_
    refine (fderiv_val u c _ (F i) (hF i).1 n ((hF i).2 c) z hz (h0 i) _).trans ?_
    rw [show (Pi.single k (2 * Real.pi * Complex.I)⁻¹ : Fin x.P.g → ℂ) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • Pi.single k 1 by rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one], map_smul]
    rfl
  · haveI := x.P.isAb.smooth
    by_contra hne
    have hcl : IsClosed {y : x.P.A.left | ∃ a, ∃ p : Sp ℂ, (u.ex (zs a)).left p = y} := by
      have : {y : x.P.A.left | ∃ a, ∃ p : Sp ℂ, (u.ex (zs a)).left p = y} =
          ⋃ a, Set.range (u.ex (zs a)).left := by
        ext y; simp
      rw [this]
      refine isClosed_iUnion_of_finite fun a => ?_
      haveI := x.P.isAb.proper
      have : IsClosedImmersion (u.ex (zs a)).left := by
        have hw : (u.ex (zs a)).left ≫ x.P.A.hom = 𝟙 _ := Over.w _
        have : IsClosedImmersion ((u.ex (zs a)).left ≫ x.P.A.hom) := by rw [hw]; infer_instance
        exact IsClosedImmersion.of_comp _ x.P.A.hom
      exact (u.ex (zs a)).left.isClosedEmbedding.isClosed_range
    have hcz : IsClosed {y : x.P.A.left | ∀ i, y ∉ Out.nonzeroLocus (s i)} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun i => (Out.nonzeroLocus (s i)).isOpen.isClosed_compl
    obtain ⟨q, hq, hqZ⟩ := ComplexPoints.exists_point_mem x.P.A.hom
      (hcz.isLocallyClosed.inter hcl.isOpen_compl.isLocallyClosed) ⟨y, hy, hne⟩
    obtain ⟨w, hw⟩ := u.ex_onto (Over.homMk q hq)
    have hw' : (u.ex w).left = q := congrArg (fun φ => φ.left) hw
    let p : Sp ℂ := IsLocalRing.closedPoint ℂ
    obtain ⟨j, hj⟩ : ∃ j, q p ∈ x.P.L.U j :=
      TopologicalSpace.Opens.mem_iSup.1 (by rw [x.P.isLB.cover]; trivial)
    have hj' : ⊤ ≤ q ⁻¹ᵁ x.P.L.U j := (ComplexPoints.top_le_preimage_iff q _ p).2 hj
    obtain ⟨a', e, he, hwe⟩ := hzs w fun i => by
      by_contra hi
      refine (hqZ p).1 i (TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩)
      refine (ComplexPoints.top_le_preimage_iff q _ p).1
        ((ComplexPoints.top_le_preimage_basicOpen_iff q _ hj' _).2 ?_)
      have hv := (hF i).2 j w (by rw [hw']; exact hj')
      rw [hw'] at hv
      exact ((dif_pos hj').symm.trans hv).trans_ne (mul_ne_zero hi (pow_ne_zero _ (u.fr_ne j w (by rw [hw']; exact hj'))))
    refine (hqZ p).2 ⟨a', p, ?_⟩
    rw [← hw', hwe, u.ex_add, (u.ker e).2 he, _root_.mul_one]

end GlobalTheory

end
end
