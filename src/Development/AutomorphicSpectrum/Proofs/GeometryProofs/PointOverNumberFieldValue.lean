module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBoundedSectionTransfer
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointFactorsOpen
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductOnSpan

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointOverNumberFieldValue
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointOverNumberFieldValue
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LiesOver

open GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer

section Values

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X}

theorem valAt_add {a b : Ω} {r s : ℂ} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) :
    ValAt ξ z (a + b) (r + s) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  obtain ⟨_, t', rfl, rfl⟩ := h'
  exact ⟨hz, t + t', map_add _ _ _, map_add _ _ _⟩

theorem valAt_int (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : ℂ) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ _, map_intCast _ _⟩

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {w : (Σ k, J k) → ℂ}

theorem evC_xpow (w : (Σ k, J k) → ℂ) (c : ∀ k, J k) (e : K → ℕ) :
    evC w (ArakelovGeometry.xpow c e) = ∏ k, w ⟨k, c k⟩ ^ e k := by
  simp [evC, ArakelovGeometry.xpow, map_prod]

theorem exists_form_valAt (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (c : ∀ k, J k)
    (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) {x : Ω} (hx : x ∈ chartRingZ y c) :
    ∃ (δ : K → ℕ) (G : MRing J), IsMultiHomog G δ ∧ aeval y G = x * ∏ k, y ⟨k, c k⟩ ^ δ k ∧
      ValAt ξ z x (evC w G / ∏ k, w ⟨k, c k⟩ ^ δ k) := by
  classical
  have hc0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have hW : ∀ δ : K → ℕ, (∏ k, w ⟨k, c k⟩ ^ δ k) ≠ 0 := fun δ =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc0 k)
  have hpow : ∀ δ₁ δ₂ : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hpowC : ∀ δ₁ δ₂ : K → ℕ, ∏ k, w ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, w ⟨k, c k⟩ ^ δ₁ k) * ∏ k, w ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  rw [chartRingZ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hx
    refine ⟨Pi.single k 1, MvPolynomial.X ⟨k, i⟩, ArakelovGeometry.isMultiHomog_X' k i, ?_, ?_⟩
    · rw [aeval_X, Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (by simp)]
      simp [div_mul_cancel₀ _ (hy k)]
    · obtain ⟨r, hr, e⟩ := (hw.2 k (c k) (hc k)).2 i
      have e1 : (∏ k', w ⟨k', c k'⟩ ^ (Pi.single k 1 : K → ℕ) k') = w ⟨k, c k⟩ := by
        rw [Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (by simp)]
        simp
      have e2 : evC w (MvPolynomial.X ⟨k, i⟩ : MRing J) = w ⟨k, i⟩ := by simp [evC]
      rw [e1, e2, e, mul_div_cancel_right₀ _ (hc0 k)]
      exact hr
  | algebraMap r =>
    refine ⟨0, C r, isMultiHomog_C r, by simp, ?_⟩
    have e : evC w (C r : MRing J) = (r : ℂ) := by simp [evC]
    simp only [e, Pi.zero_apply, pow_zero, Finset.prod_const_one, div_one]
    simpa using valAt_int hz r
  | add a b _ _ ha hb =>
    obtain ⟨δ₁, e₁, h₁, v₁, u₁⟩ := ha
    obtain ⟨δ₂, e₂, h₂, v₂, u₂⟩ := hb
    refine ⟨δ₁ + δ₂, e₁ * ArakelovGeometry.xpow c δ₂ + e₂ * ArakelovGeometry.xpow c δ₁,
      isMultiHomog_add (ArakelovGeometry.isMultiHomog_mul h₁ (ArakelovGeometry.isMultiHomog_xpow c δ₂)) ?_, ?_, ?_⟩
    · rw [add_comm δ₁]
      exact ArakelovGeometry.isMultiHomog_mul h₂ (ArakelovGeometry.isMultiHomog_xpow c δ₁)
    · rw [map_add (f := _), map_mul, map_mul, v₁, v₂, aeval_xpow, aeval_xpow, hpow]
      ring
    · convert valAt_add u₁ u₂ using 1
      have e : evC w (e₁ * ArakelovGeometry.xpow c δ₂ + e₂ * ArakelovGeometry.xpow c δ₁) =
          evC w e₁ * evC w (ArakelovGeometry.xpow c δ₂) + evC w e₂ * evC w (ArakelovGeometry.xpow c δ₁) := by
        simp only [evC, map_add (f := _), map_mul]
      rw [e, evC_xpow, evC_xpow, hpowC]
      have := hW δ₁
      have := hW δ₂
      field_simp
  | mul a b _ _ ha hb =>
    obtain ⟨δ₁, e₁, h₁, v₁, u₁⟩ := ha
    obtain ⟨δ₂, e₂, h₂, v₂, u₂⟩ := hb
    refine ⟨δ₁ + δ₂, e₁ * e₂, ArakelovGeometry.isMultiHomog_mul h₁ h₂, ?_, ?_⟩
    · rw [map_mul, v₁, v₂, hpow]
      ring
    · convert CoordModel.valAt_mul u₁ u₂ using 1
      have e : evC w (e₁ * e₂) = evC w e₁ * evC w e₂ := by simp only [evC, map_mul]
      rw [e, hpowC]
      have := hW δ₁
      have := hW δ₂
      field_simp

end Values

theorem valAt_cst : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (σ : F' →+* ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), NormalCpt ξ → (CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordsAt ξ y z w → PtOver y ψ σ w → genPt ξ ⤳ centre z → ∀ a : F', ValAt ξ z (ψ a) (σ a) := by
  intro X Ω _ ξ K _ J _ y F' _ _ ψ σ z w hN ht hw hp hz a
  classical
  choose c hc using hw.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (hc k)).1
  have hO : OverInt y ψ := overInt_of_normalCpt ht hN ψ
  have hint : ∀ b : 𝓞 F', ValAt ξ z (ψ (b : F')) (σ (b : F')) := by
    intro b
    obtain ⟨δ, G, hG, hv, hu⟩ := exists_form_valAt hz hw c hy hc (hO.2 c hy b)
    have h1 := hp.2 (b : F') δ G (ArakelovGeometry.xpow c δ) hG (ArakelovGeometry.isMultiHomog_xpow c δ) (by
      rw [hv, GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.aeval_xpow])
    rw [evC_xpow] at h1
    have hW : (∏ k, w ⟨k, c k⟩ ^ δ k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k).ne_zero
    rwa [h1, mul_div_cancel_right₀ _ hW] at hu
  have halg : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ F').2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨n, hn, hi⟩ := halg.exists_integral_multiple
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have h1 := hint (⟨n • a, hi⟩ : 𝓞 F')
  have h2 : ValAt ξ z (n : Ω) ((Units.mk0 (n : ℂ) hnC : ℂˣ) : ℂ) := valAt_int hz n
  obtain ⟨hn0, h3⟩ := CoordModel.valAt_inv h2
  have h4 := CoordModel.valAt_mul h3 h1
  convert h4 using 1
  · show ψ a = (n : Ω)⁻¹ * ψ (n • a)
    rw [zsmul_eq_mul, map_mul, map_intCast, inv_mul_cancel_left₀ hn0]
  · show σ a = ((Units.mk0 (n : ℂ) hnC)⁻¹ : ℂˣ) * σ (n • a)
    rw [zsmul_eq_mul, map_mul, map_intCast, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel_left₀ hnC]

end GlobalTheory.CompanionTheory.Ar.Flat.LiesOver
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointOverNumberFieldValueStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_over_number_field_value : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (σ : F' →+* ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), NormalCpt ξ → (CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordsAt ξ y z w → PtOver y ψ σ w → genPt ξ ⤳ centre z → ∀ a : F', ValAt ξ z (ψ a) (σ a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LiesOver.valAt_cst | exact GlobalTheory.CompanionTheory.Ar.Flat.LiesOver.valAt_cst | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LiesOver.valAt_cst <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianBundleFibreTangent
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianBundleFibreTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeBC


open GroundTheory.Heights₂.Heights in
theorem span_one_tmul {L : Type} [Field L] (e : L →+* ℂ) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] :
    Submodule.span ℂ {w : Fibre e V | ∃ y : V, w = (1 : ComplexAt e) ⊗ₜ[𝓞 L] y} = ⊤ := by
  rw [eq_top_iff]
  rintro w -
  change ComplexAt e ⊗[𝓞 L] V at w
  induction w using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul c y =>
    have h : (c ⊗ₜ[𝓞 L] y : ComplexAt e ⊗[𝓞 L] V) = c • ((1 : ComplexAt e) ⊗ₜ[𝓞 L] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  | add a b ha hb => exact Submodule.add_mem _ ha hb

private theorem isGrpPullback_one_left {S : Scheme.{0}} {G : Over S} [GrpObj G] (A : Over S) :
    (1 : A ⟶ G).left = A.hom ≫ (1 : Over.mk (𝟙 S) ⟶ G).left := by
  have h := LieSigma.comp_one_over (M := G) (Over.homMk A.hom (by simp) : A ⟶ Over.mk (𝟙 S))
  calc (1 : A ⟶ G).left
      = ((Over.homMk A.hom (by simp) : A ⟶ Over.mk (𝟙 S)) ≫ (1 : Over.mk (𝟙 S) ⟶ G)).left := by rw [h]
    _ = A.hom ≫ (1 : Over.mk (𝟙 S) ⟶ G).left := by rw [Over.comp_left]; rfl

private theorem one_left_comp_eq_comp_one_of_isGrpPullback {X X' : Scheme.{0}} (G' : Over X') [GrpObj G'] (G : Over X) [GrpObj G]
    (f : X' ⟶ X) (φ : G'.left ⟶ G.left) (hφ : IsGrpPullback G' G f φ) :
    (1 : Over.mk (𝟙 X') ⟶ G').left ≫ φ = f ≫ (1 : Over.mk (𝟙 X) ⟶ G).left := by
  have hε : (1 : Over.mk (𝟙 X') ⟶ G').left ≫ G'.hom = 𝟙 X' := Over.w (1 : Over.mk (𝟙 X') ⟶ G')
  have hw : ((1 : Over.mk (𝟙 X') ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk ((Over.mk (𝟙 X')).hom ≫ f)).hom := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, hε]
    simp
  let x₀ : Over.mk ((Over.mk (𝟙 X')).hom ≫ f) ⟶ G := Over.homMk ((1 : Over.mk (𝟙 X') ⟶ G').left ≫ φ) hw
  have hmul := hφ.2 (Over.mk (𝟙 X')) 1 1 x₀ x₀ rfl rfl
  have hx : x₀ * x₀ = x₀ * 1 := by
    rw [_root_.mul_one]
    apply Over.OverMorphism.ext
    rw [hmul, _root_.mul_one]
    rfl
  have h1 : x₀ = 1 := _root_.mul_left_cancel hx
  have h2 : x₀.left = (1 : Over.mk ((Over.mk (𝟙 X')).hom ≫ f) ⟶ G).left := by rw [h1]
  rw [isGrpPullback_one_left] at h2
  simpa [x₀] using h2

private theorem exists_tanAt_comp_of_sabMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}}
    {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f) (z : Sp ℂ ⟶ X')
    (v : epsAt z ⟶ t'.G) (hv : IsTanAt t'.G z v) :
    ∃ w : epsAt (z ≫ f) ⟶ t.G, w.left = v.left ≫ m.φ ∧ IsTanAt t.G (z ≫ f) w := by
  have hsq : m.φ ≫ t.G.hom = t'.G.hom ≫ f := m.cart.1.w
  refine ⟨Over.homMk (v.left ≫ m.φ) ?_, rfl, ?_⟩
  · rw [Category.assoc, hsq, ← Category.assoc, Over.w v]
    simp [epsAt]
  · have hv' : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v.left
        = (1 : Over.mk z ⟶ t'.G).left := hv
    show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ (v.left ≫ m.φ)
        = (1 : Over.mk (z ≫ f) ⟶ t.G).left
    have h1 : (1 : Over.mk z ⟶ t'.G).left = (Over.mk z).hom ≫ (1 : Over.mk (𝟙 X') ⟶ t'.G).left :=
      isGrpPullback_one_left _
    have h2 : (1 : Over.mk (z ≫ f) ⟶ t.G).left = (Over.mk (z ≫ f)).hom ≫ (1 : Over.mk (𝟙 X) ⟶ t.G).left :=
      isGrpPullback_one_left _
    rw [h2, ← Category.assoc, hv', h1, Category.assoc, one_left_comp_eq_comp_one_of_isGrpPullback t'.G t.G f m.φ m.cart]
    simp [epsAt]


open LieMove in
theorem hodge_along {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X₀ X₁ X₂ : Scheme.{0}}
    {t₀ : SAB H X₀} {t₁ : SAB H X₁} {t₂ : SAB H X₂} {f₀ : X₀ ⟶ X₁} {f₁ : X₁ ⟶ X₂} (m₀ : SABMap t₀ t₁ f₀)
    (m₁ : SABMap t₁ t₂ f₁) (z : Sp ℂ ⟶ X₀) (p : Sp ℂ ⟶ X₂) (hp : p = (z ≫ f₀) ≫ f₁)
    {V : Type} [AddCommGroup V] [Module ℂ V] (Mp : LieModel t₂.G p V) (core : InnerProductSpace.Core ℂ V) (W : Set V)
    (h0 : (0 : V) ∈ W) (hs : Submodule.span ℂ W = ⊤)
    (hW : ∀ a ∈ W, ∀ b ∈ W, HodgeIP t₂.G t₂.PP.L p (Mp.pt a) (Mp.pt b) (core.inner a b))
    {V' : Type} (Tn : V' → (epsAt z ⟶ t₀.G)) (hT : ∀ x, IsTanAt t₀.G z (Tn x)) :
    ∃ D : V' → V, (∀ x x', HodgeIP t₀.G t₀.PP.L z (Tn x) (Tn x') (core.inner (D x) (D x'))) ∧
      ∀ x a, (Tn x).left ≫ m₀.φ ≫ m₁.φ = (Mp.pt a).left → D x = a := by
  subst hp
  have hall : ∀ a b : V, HodgeIP t₂.G t₂.PP.L ((z ≫ f₀) ≫ f₁) (Mp.pt a) (Mp.pt b) (core.inner a b) :=
    GlobalTheory.T.hodge_inner_product_on_span E H X₁ X₂ t₁ t₂ f₁ m₁ (z ≫ f₀) V Mp core W h0 hs hW
  have key : ∀ x, ∃ w₁ : epsAt (z ≫ f₀) ⟶ t₁.G, w₁.left = (Tn x).left ≫ m₀.φ ∧
      ∃ a : V, (Mp.pt a).left = w₁.left ≫ m₁.φ := by
    intro x
    obtain ⟨w₁, hw₁, ht₁⟩ := exists_tanAt_comp_of_sabMap m₀ z (Tn x) (hT x)
    obtain ⟨w₂, hw₂, ht₂⟩ := exists_tanAt_comp_of_sabMap m₁ (z ≫ f₀) w₁ ht₁
    obtain ⟨a, ha⟩ := Mp.onto w₂ ht₂
    exact ⟨w₁, hw₁, a, by rw [ha, hw₂]⟩
  choose w₁ hw₁ D hD using key
  refine ⟨D, fun x x' => ?_, fun x a h => ?_⟩
  · rw [GlobalTheory.T.hodge_inner_product_map_iff E H X₁ t₁ X₀ t₀ f₀ m₀ z (Tn x) (Tn x') (w₁ x) (w₁ x') _ (hw₁ x) (hw₁ x'),
      GlobalTheory.T.hodge_inner_product_map_iff E H X₂ t₂ X₁ t₁ f₁ m₁ (z ≫ f₀) (w₁ x) (w₁ x') (Mp.pt (D x)) (Mp.pt (D x')) _ (hD x) (hD x')]
    exact hall _ _
  · apply Mp.inj
    apply Over.OverMorphism.ext
    rw [hD x, hw₁ x]
    exact (Category.assoc _ _ _).trans h

theorem lifts_left {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G x V) (c : R →+* R') (a : V)
    (v : epsAt (spMap c ≫ x) ⟶ G) (h : (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt a).left)) :
    v.left = spMap (dualMap c) ≫ (M.pt a).left := by
  have h' : v.left ≫ 𝟙 G.left = spMap (dualMap c) ≫ (M.pt a).left := h
  simpa using h'


open GroundTheory.Heights₂.Heights in
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t' : SAB H (Sp (𝓞 L))) (tB : SAB H (Sp L)) (tC : SAB H (Sp ℂ)) (e : L →+* ℂ) (m' : SABMap tB t' (spMap (algebraMap (𝓞 L) L))) (mB : SABMap tC tB (spMap e)) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t'.G (𝟙 _) B.carrier), IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB → ∀ (V' : Type) (Tn : V' → (epsAt (𝟙 (Sp ℂ)) ⟶ tC.G)), (∀ x, IsTanAt tC.G (𝟙 _) (Tn x)) → ∃ hb : V' → V' → ℂ, (∀ x x', HodgeIP tC.G tC.PP.L (𝟙 _) (Tn x) (Tn x') (hb x x')) ∧ ∀ (x x' : V') (y y' : B.carrier), (Tn x).left ≫ mB.φ ≫ m'.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt y).left → (Tn x').left ≫ mB.φ ≫ m'.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt y').left → hb x x' = (B.metric.form e).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] y) ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] y') := by
  intro E _ _ _ H L _ _ t' tB tC e m' mB B MB hF V' Tn hT
  haveI : Smooth t'.G.hom := @ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian.smooth _ _ _ t'.semi
  obtain ⟨Mσ, hMσ⟩ := LieSigma.lieModel_fibre (Sp (𝓞 L)) t'.G L (𝟙 _) B.carrier MB e
  have hp : spMap (e.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))
      = (𝟙 (Sp ℂ) ≫ spMap e) ≫ spMap (algebraMap (𝓞 L) L) := by
    simp only [Category.comp_id, Category.id_comp]
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨D, hD1, hD2⟩ := hodge_along mB m' (𝟙 _) _ hp Mσ (B.metric.form e)
    {w | ∃ y : B.carrier, w = (1 : ComplexAt e) ⊗ₜ[𝓞 L] y} ⟨0, by simp⟩ (span_one_tmul e B.carrier)
    (by
      rintro a ⟨y, rfl⟩ b ⟨y', rfl⟩
      exact hF e y y' _ _ (hMσ y) (hMσ y'))
    Tn hT
  refine ⟨fun x x' => (B.metric.form e).inner (D x) (D x'), hD1, ?_⟩
  intro x x' y y' hx hx'
  have e1 : D x = (1 : ComplexAt e) ⊗ₜ[𝓞 L] y :=
    hD2 x _ (hx.trans (lifts_left MB _ _ _ (hMσ y)).symm)
  have e2 : D x' = (1 : ComplexAt e) ⊗ₜ[𝓞 L] y' :=
    hD2 x' _ (hx'.trans (lifts_left MB _ _ _ (hMσ y')).symm)
  simp only [e1, e2]

end GlobalTheory.CompanionTheory.Ar.HodgeBC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianBundleFibreTangentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_bundle_fibre_tangent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t' : SAB H (Sp (𝓞 L))) (tB : SAB H (Sp L)) (tC : SAB H (Sp ℂ)) (e : L →+* ℂ) (m' : SABMap tB t' (spMap (algebraMap (𝓞 L) L))) (mB : SABMap tC tB (spMap e)) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t'.G (𝟙 _) B.carrier), IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB → ∀ (V' : Type) (Tn : V' → (epsAt (𝟙 (Sp ℂ)) ⟶ tC.G)), (∀ x, IsTanAt tC.G (𝟙 _) (Tn x)) → ∃ hb : V' → V' → ℂ, (∀ x x', HodgeIP tC.G tC.PP.L (𝟙 _) (Tn x) (Tn x') (hb x x')) ∧ ∀ (x x' : V') (y y' : B.carrier), (Tn x).left ≫ mB.φ ≫ m'.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt y).left → (Tn x').left ≫ mB.φ ≫ m'.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt y').left → hb x x' = (B.metric.form e).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] y) ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] y') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeBC.main | exact GlobalTheory.CompanionTheory.Ar.HodgeBC.main | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeBC.main <;> assumption)
end
end
