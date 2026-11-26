module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsAbelianPartExtension
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLieSignature
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieSignatureNumberField
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricHeightBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianLieMetricHeight
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianBundleQuotientDegreeBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianPullbackTorusExtension
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductOnSpan

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartMapsCompatibleRight
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartMapsCompatibleLeft
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartMapsCompatibleLeft
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TanCompare

theorem grp_mul {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} (a : T ⟶ S') (b : T ⟶ S) (hb : b = a ≫ f)
    (x y : Over.mk a ⟶ G') (x₀ y₀ : Over.mk b ⟶ G) (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hb
  exact h.2 (Over.mk a) x y x₀ y₀ hx hy

theorem exists_lift {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} (a : T ⟶ S') (w : T ⟶ G.left) (hw : w ≫ G.hom = a ≫ f) :
    ∃ v : Over.mk a ⟶ G', v.left ≫ φ = w :=
  ⟨Over.homMk (h.lift w a hw) (by simp), by simp⟩

theorem lift_unique {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {a : T ⟶ S'} (v v' : Over.mk a ⟶ G')
    (e : v.left ≫ φ = v'.left ≫ φ) : v = v' :=
  Over.OverMorphism.ext (h.hom_ext e (by rw [Over.w, Over.w]))

theorem spMap_dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [← spMap_comp]
  congr 1
  refine RingHom.ext fun a => ?_
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap]

def scale {S : Scheme.{0}} {Y : Over S} (a : Sp ℂ ⟶ S) (c : ℂ) (v : epsAt a ⟶ Y) : epsAt a ⟶ Y :=
  Over.homMk (spMap (epsMul c) ≫ v.left) (by
    have h := Over.w v
    simp only [Over.mk_left, Over.mk_hom, Category.assoc] at h ⊢
    rw [h, ← Category.assoc, LieTangent.spec_eps_alg])

@[simp] theorem scale_left {S : Scheme.{0}} {Y : Over S} (a : Sp ℂ ⟶ S) (c : ℂ) (v : epsAt a ⟶ Y) :
    (scale a c v).left = spMap (epsMul c) ≫ v.left := rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem abPart_mul {S : Scheme.{0}} {t : SAB H S} {K : Type} [Field K] {z : Sp K ⟶ S} (P : AbPart t z) {T : Over (Sp K)}
    (x y : T ⟶ P.tK.G) :
    (x * y) ≫ P.τ.q ≫ P.e.hom = (x ≫ P.τ.q ≫ P.e.hom) * (y ≫ P.τ.q ≫ P.e.hom) := by
  letI := P.τ.grpB
  haveI := P.τ.q_hom
  haveI : IsMonHom P.e.hom := P.e_hom
  rw [← Category.assoc, mul_comp, mul_comp, Category.assoc, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.TanCompare

namespace GlobalTheory.CompanionTheory.Ar.TanCompare

theorem tan_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (V₁ V₂ : Type) [AddCommGroup V₁] [Module (𝓞 L) V₁] [AddCommGroup V₂] [Module (𝓞 L) V₂] (MB : LieModel t.G z V₁) (MB' : LieModel t'.G (𝟙 _) V₂) (f : V₁ →ₗ[𝓞 L] V₂) (hf : ∀ (e : V₁) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), (v.left ≫ P₂.m.φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt e).left) → ((v ≫ P₂.τ.q).left ≫ (P₂.e.hom.left ≫ w ≫ m'.φ) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB'.pt (f e)).left)) (σ : L →+* ℂ) (Pσ : AbPart t (spMap (σ.comp e₂) ≫ z₁)) (mKσ : SABMap Pσ.tK P₁.tK (spMap (σ.comp e₂))) (mBσ : SABMap Pσ.tB P₁.tB (spMap (σ.comp e₂))) (d1 : mKσ.φ ≫ P₁.m.φ = Pσ.m.φ) (d2 : mKσ.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ) (Mσ : LieModel t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (GroundTheory.Heights₂.Heights.Fibre σ V₁)) (hMσ : ∀ e : V₁, ((Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ≫ (𝟙 t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt e).left)) (Mσ' : LieModel t'.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) (GroundTheory.Heights₂.Heights.Fibre σ V₂)) (hMσ' : ∀ e : V₂, ((Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ≫ (𝟙 t'.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB'.pt e).left)) (x : GroundTheory.Heights₂.Heights.Fibre σ V₁) (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G), v.left ≫ Pσ.m.φ = (Mσ.pt x).left → u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x)).left → u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
  intro E _ _ _ H X t L₁ L _ _ _ e₂ z₁ z hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' V₁ V₂ _ _ _ _ MB MB' f hf σ Pσ mKσ mBσ
    d1 d2 Mσ hMσ Mσ' hMσ' x v u hv hu
  have spec_dual_alg {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') :
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) =
        spMap (algebraMap R' (DualNumber R')) ≫ spMap φ := by
    rw [← spMap_comp, ← spMap_comp]
    congr 1
    ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hbase : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z = spMap (σ.comp e₂) ≫ z₁ := by
    rw [spMap_comp (algebraMap (𝓞 L) L) σ, spMap_comp e₂ σ, Category.assoc, Category.assoc, hz]
  have hb1 : spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _) ≫ spMap (σ.comp e₂) ≫ z₁ := by
    rw [hbase, Category.comp_id]
  have hb2 : spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap (algebraMap (𝓞 L) L) := by
    rw [spMap_comp (algebraMap (𝓞 L) L) σ, Category.comp_id, Category.assoc]
  have hb3 : (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _) ≫ spMap (σ.comp e₂) =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂ := by
    rw [spMap_comp e₂ σ, Category.comp_id, Category.assoc]
  have base : ∀ e : V₁, ∃ (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G),
      v.left ≫ Pσ.m.φ = (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ∧
      u.left ≫ m'.φ = (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e)).left ∧
      u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
    intro e
    obtain ⟨vL, hvL⟩ := exists_lift P₂.m.cart.1 (spMap (algebraMap L (DualNumber L)) ≫ 𝟙 _)
      (spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt e).left) (by
        have hMe : (MB.pt e).left ≫ t.G.hom = spMap (algebraMap (𝓞 L) (DualNumber (𝓞 L))) ≫ z := Over.w (MB.pt e)
        rw [Category.assoc, hMe, ← Category.assoc, spec_dual_alg, Category.assoc, hz, Category.comp_id])
    have hfe : (vL ≫ P₂.τ.q).left ≫ P₂.e.hom.left ≫ w ≫ m'.φ =
        spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (MB'.pt (f e)).left := hf e vL hvL
    obtain ⟨v, hv⟩ := exists_lift Pσ.m.cart.1 (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _)
      (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left
      ((Over.w (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e))).trans hb1)
    obtain ⟨u, hu⟩ := exists_lift m'.cart.1 (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ)
      (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e)).left
      ((Over.w (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e))).trans hb2)
    refine ⟨v, u, hv, hu, ?_⟩
    have hde : spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) =
        spMap (dualMap σ) ≫ spMap (dualMap (algebraMap (𝓞 L) L)) := spMap_dual_comp _ _
    have hd : spMap (dualMap σ) ≫ spMap (algebraMap L (DualNumber L)) =
        spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := spec_dual_alg σ
    have h1 : (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left =
        spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt e).left :=
      (Category.comp_id _).symm.trans (hMσ e)
    have h1' : (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e)).left =
        spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB'.pt (f e)).left :=
      (Category.comp_id _).symm.trans (hMσ' (f e))
    have hvd : v.left ≫ Pσ.m.φ = spMap (dualMap σ) ≫ vL.left ≫ P₂.m.φ := by
      rw [hv, h1, hde, Category.assoc, hvL]
    have wv : v.left ≫ Pσ.tK.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _ := Over.w v
    have wvL : vL.left ≫ P₂.tK.G.hom = spMap (algebraMap L (DualNumber L)) ≫ 𝟙 _ := Over.w vL
    have star : v.left ≫ mKσ.φ = spMap (dualMap σ) ≫ vL.left ≫ mK2.φ := by
      refine P₁.m.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, d1, hvd, Category.assoc, Category.assoc, c1]
      · rw [Category.assoc, mKσ.cart.1.w, ← Category.assoc, wv, hb3]
        simp only [Category.assoc]
        rw [mK2.cart.1.w, ← Category.assoc vL.left, wvL, Category.comp_id]
        have hd2 : spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ ≫ spMap e₂ =
            spMap (dualMap σ) ≫ spMap (algebraMap L (DualNumber L)) ≫ spMap e₂ := by
          rw [← Category.assoc, ← hd, Category.assoc]
        exact hd2
    have wu : u.left ≫ tK.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := Over.w u
    have wq : (vL ≫ P₂.τ.q).left ≫ P₂.τ.B.hom = spMap (algebraMap L (DualNumber L)) ≫ 𝟙 _ := Over.w (vL ≫ P₂.τ.q)
    have we : P₂.e.hom.left ≫ P₂.tB.G.hom = P₂.τ.B.hom := Over.w P₂.e.hom
    have hu2 : u.left = spMap (dualMap σ) ≫ (vL ≫ P₂.τ.q).left ≫ P₂.e.hom.left ≫ w := by
      refine m'.cart.1.hom_ext ?_ ?_
      · rw [hu, h1', hde]
        simp only [Category.assoc]
        rw [hfe]
      · rw [wu]
        simp only [Category.assoc]
        rw [hw', we, wq, Category.comp_id, hd]
    have e1 : (vL ≫ P₂.τ.q).left ≫ P₂.e.hom.left ≫ mB2.φ = vL.left ≫ (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ := by
      simp only [Over.comp_left, Category.assoc]
    have e2 : (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ = v.left ≫ (Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
      rw [Over.comp_left, Category.assoc]
    rw [hu2, e2, ← d2, ← Category.assoc v.left, star]
    simp only [Category.assoc]
    rw [hw, e1, ← c2]
  have tm : ∀ (c : GroundTheory.Heights₂.Heights.ComplexAt σ) (e : V₁), ∃ (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G),
      v.left ≫ Pσ.m.φ = (Mσ.pt (c ⊗ₜ[𝓞 L] e)).left ∧
      u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) (c ⊗ₜ[𝓞 L] e))).left ∧
      u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
    intro c e
    obtain ⟨v, u, h, k, l⟩ := base e
    let c' : ℂ := c
    have hs : c' • (1 : GroundTheory.Heights₂.Heights.ComplexAt σ) = c := by
      rw [GroundTheory.Heights₂.Heights.ComplexAt.complex_smul_def, _root_.mul_one]
      rfl
    have hc : ∀ (W : Type) [AddCommGroup W] [Module (𝓞 L) W] (a : W),
        c ⊗ₜ[𝓞 L] a = c' • ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] a) := by
      intro W _ _ a
      rw [TensorProduct.smul_tmul', hs]
    refine ⟨scale _ c' v, scale _ c' u, ?_, ?_, ?_⟩
    · rw [hc, Mσ.smul, scale_left, Category.assoc, h]
    · rw [LinearMap.lTensor_tmul, hc, Mσ'.smul, scale_left, Category.assoc, k]
    · rw [scale_left, Category.assoc, l]
      simp only [Over.comp_left, scale_left, Category.assoc]
  have hx0 : ∀ u : epsAt (spMap σ) ⟶ tK.G, (u.left ≫ mP.φ) ≫ P₁.tB.G.hom =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂ := by
    intro u
    have wu : u.left ≫ tK.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := Over.w u
    rw [Category.assoc, mP.cart.1.w, ← Category.assoc, wu]
  have key : ∀ x : GroundTheory.Heights₂.Heights.Fibre σ V₁, ∃ (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G),
      v.left ≫ Pσ.m.φ = (Mσ.pt x).left ∧
      u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x)).left ∧
      u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      have h0 := tm 0 0
      rwa [TensorProduct.zero_tmul] at h0
    | tmul c e => exact tm c e
    | add x y hx hy =>
      obtain ⟨v₁, u₁, h₁, k₁, l₁⟩ := hx
      obtain ⟨v₂, u₂, h₂, k₂, l₂⟩ := hy
      refine ⟨v₁ * v₂, u₁ * u₂, ?_, ?_, ?_⟩
      · rw [Mσ.add]
        exact (grp_mul Pσ.m.cart _ _ hb1 v₁ v₂ (Mσ.pt x) (Mσ.pt y) h₁.symm h₂.symm).symm
      · rw [map_add (f := _), Mσ'.add]
        exact (grp_mul m'.cart _ _ hb2 u₁ u₂ _ _ k₁.symm k₂.symm).symm
      · rw [abPart_mul]
        let x₀ : Over.mk ((spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂) ⟶ P₁.tB.G :=
          Over.homMk (u₁.left ≫ mP.φ) (hx0 u₁)
        let y₀ : Over.mk ((spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂) ⟶ P₁.tB.G :=
          Over.homMk (u₂.left ≫ mP.φ) (hx0 u₂)
        rw [← grp_mul mP.cart _ _ rfl u₁ u₂ x₀ y₀ rfl rfl]
        exact grp_mul mBσ.cart _ _ hb3.symm _ _ x₀ y₀ l₁ l₂
  obtain ⟨v₀, u₀, h₀, k₀, l₀⟩ := key x
  have hv' : v = v₀ := lift_unique Pσ.m.cart.1 _ _ (hv.trans h₀.symm)
  have hu' : u = u₀ := lift_unique m'.cart.1 _ _ (hu.trans k₀.symm)
  rw [hv', hu']
  exact l₀

end GlobalTheory.CompanionTheory.Ar.TanCompare
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartMapsCompatibleLeftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_maps_compatible_left : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (V₁ V₂ : Type) [AddCommGroup V₁] [Module (𝓞 L) V₁] [AddCommGroup V₂] [Module (𝓞 L) V₂] (MB : LieModel t.G z V₁) (MB' : LieModel t'.G (𝟙 _) V₂) (f : V₁ →ₗ[𝓞 L] V₂) (hf : ∀ (e : V₁) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), (v.left ≫ P₂.m.φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt e).left) → ((v ≫ P₂.τ.q).left ≫ (P₂.e.hom.left ≫ w ≫ m'.φ) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB'.pt (f e)).left)) (σ : L →+* ℂ) (Pσ : AbPart t (spMap (σ.comp e₂) ≫ z₁)) (mKσ : SABMap Pσ.tK P₁.tK (spMap (σ.comp e₂))) (mBσ : SABMap Pσ.tB P₁.tB (spMap (σ.comp e₂))) (d1 : mKσ.φ ≫ P₁.m.φ = Pσ.m.φ) (d2 : mKσ.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ) (Mσ : LieModel t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (GroundTheory.Heights₂.Heights.Fibre σ V₁)) (hMσ : ∀ e : V₁, ((Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ≫ (𝟙 t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt e).left)) (Mσ' : LieModel t'.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) (GroundTheory.Heights₂.Heights.Fibre σ V₂)) (hMσ' : ∀ e : V₂, ((Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ≫ (𝟙 t'.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB'.pt e).left)) (x : GroundTheory.Heights₂.Heights.Fibre σ V₁) (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G), v.left ≫ Pσ.m.φ = (Mσ.pt x).left → u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x)).left → u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TanCompare.tan_compare | exact GlobalTheory.CompanionTheory.Ar.TanCompare.tan_compare | (intros; apply GlobalTheory.CompanionTheory.Ar.TanCompare.tan_compare <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartMapsCompatibleRight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SlopeNorm

open GroundTheory.Heights₂.Heights

theorem core_left {V : Type} [AddCommGroup V] [Module ℂ V] (c₁ c₂ : InnerProductSpace.Core ℂ V) (W : Set V)
    (hW : Submodule.span ℂ W = ⊤) (a : V) (h : ∀ b ∈ W, c₁.inner b a = c₂.inner b a) (b : V) :
    c₁.inner b a = c₂.inner b a := by
  have hb : b ∈ Submodule.span ℂ W := hW ▸ Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have e₁ := c₁.smul_left 0 a 0
    have e₂ := c₂.smul_left 0 a 0
    simp only [smul_zero, map_zero, zero_mul] at e₁ e₂
    rw [e₁, e₂]
  | add x y _ _ hx hy => rw [c₁.add_left, c₂.add_left, hx, hy]
  | smul r x _ hx => rw [c₁.smul_left, c₂.smul_left, hx]

theorem core_eq {V : Type} [AddCommGroup V] [Module ℂ V] (c₁ c₂ : InnerProductSpace.Core ℂ V) (W : Set V)
    (hW : Submodule.span ℂ W = ⊤) (h : ∀ a ∈ W, ∀ b ∈ W, c₁.inner a b = c₂.inner a b) (a b : V) :
    c₁.inner a b = c₂.inner a b := by
  refine core_left c₁ c₂ W hW b (fun x hx => ?_) a
  have e := core_left c₁ c₂ W hW x (fun y hy => h y hy x hx) b
  rw [← c₁.conj_inner_symm, ← c₂.conj_inner_symm, e]

variable {L : Type} [Field L]

theorem span_tmul (σ : L →+* ℂ) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] :
    Submodule.span ℂ (Set.range fun e : V => (1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) = ⊤ := by
  refine (Submodule.eq_top_iff'.2 fun x => ?_)
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul c e =>
    have hc : c ⊗ₜ[𝓞 L] e = ((ComplexAt.ofComplex σ).symm c : ℂ) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) := by
      rw [TensorProduct.smul_tmul', ComplexAt.complex_smul_def]
      simp
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  | add a b ha hb => exact Submodule.add_mem _ ha hb

theorem spComp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (d : A →+* B) (c : B →+* C) :
    spMap c ≫ spMap d = spMap (c.comp d) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

def lf {S : Scheme.{0}} {G : Over S} {R : Type} [CommRing R] {x : Sp R ⟶ S} (v : epsAt x ⟶ G) :
    Sp (DualNumber R) ⟶ G.left :=
  v.left

theorem exists_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x x' : Sp R ⟶ S}
    (h : x = x') {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G x V) :
    ∃ M' : LieModel G x' V, ∀ e, lf (M'.pt e) = lf (M.pt e) := by
  subst h
  exact ⟨M, fun _ => rfl⟩

theorem exists_lift {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] (x' : Sp R ⟶ S') {b : Sp R ⟶ S}
    (hb : x' ≫ f = b) {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G b V) :
    ∃ M' : LieModel G' x' V, ∀ e, lf (M'.pt e) ≫ φ = lf (M.pt e) := by
  subst hb
  exact (LiePull.lieModel_pullback S S' G G' f φ h R x' V).1 M

theorem exists_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] (x' : Sp R ⟶ S')
    (v : epsAt x' ⟶ G') : ∃ u : epsAt (x' ≫ f) ⟶ G, lf v ≫ φ = lf u :=
  ⟨LiePull.tanPts h x' v, rfl⟩

theorem hodge_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] (Lb : LB G.left) {z z' : Sp ℂ ⟶ S} (h : z = z')
    {v w : epsAt z ⟶ G} {v' w' : epsAt z' ⟶ G} (hv : lf v = lf v') (hw : lf w = lf w') {c : ℂ}
    (hc : HodgeIP G Lb z v w c) : HodgeIP G Lb z' v' w' c := by
  subst h
  obtain rfl : v = v' := Over.OverMorphism.ext hv
  obtain rfl : w = w' := Over.OverMorphism.ext hw
  exact hc

theorem ip_congr {S : Scheme.{0}} {G : Over S}
    (ip : ∀ z : Sp ℂ ⟶ S, (epsAt z ⟶ G) → (epsAt z ⟶ G) → ℂ) {z z' : Sp ℂ ⟶ S} (h : z = z')
    {v w : epsAt z ⟶ G} {v' w' : epsAt z' ⟶ G} (hv : lf v = lf v') (hw : lf w = lf w') :
    ip z v w = ip z' v' w' := by
  subst h
  obtain rfl : v = v' := Over.OverMorphism.ext hv
  obtain rfl : w = w' := Over.OverMorphism.ext hw
  rfl

end GlobalTheory.CompanionTheory.Ar.SlopeNorm


open GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.SlopeNorm GlobalTheory.CompanionTheory.Ar.LiePull in
theorem GlobalTheory.CompanionTheory.Ar.SlopeNorm.sqAt_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M₀ y) (K₀ : ℝ) (hQ : ∀ (zc : Sp ℂ ⟶ X) (P : AbPart t zc) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt zc ⟶ t.G) (c : ℂ), IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K₀ * (h.ip zc v₀ v₀).re) (B B' : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t.G z B.carrier) (MB' : LieModel t'.G (𝟙 _) B'.carrier) (hB : IsFibre (fun z v w c => c = h.ip z v w) z B MB) (hB' : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B' MB') (f : B.carrier →ₗ[𝓞 L] B'.carrier) (hf : ∀ (e : B.carrier) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), (v.left ≫ P₂.m.φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt e).left) → ((v ≫ P₂.τ.q).left ≫ (P₂.e.hom.left ≫ w ≫ m'.φ) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB'.pt (f e)).left)) (σ : L →+* ℂ) (x : GroundTheory.Heights₂.Heights.Fibre σ B.carrier), sqAt B' σ (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x) ≤ K₀ * sqAt B σ x := by
  intro E _ _ _ H X t L₁ L _ _ _ e₂ z₁ z hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' Ω _ ξ Li _ _ M₀ K J y h K₀ hQ
    B B' MB MB' hB hB' f hf σ x
  haveI : Smooth t.G.hom := t.semi.smooth
  haveI : Smooth t'.G.hom := t'.semi.smooth
  obtain ⟨Pσ, mKσ, mBσ, d1, d2⟩ := GlobalTheory.T.abelian_part_base_change E H X t L₁ ℂ z₁ P₁ (σ.comp e₂)
  obtain ⟨Mσ, hMσ⟩ := GlobalTheory.T.lie_model_complex_base_change X t.G L z B.carrier MB σ
  obtain ⟨Mσ', hMσ'⟩ := GlobalTheory.T.lie_model_complex_base_change (Sp (𝓞 L)) t'.G L (𝟙 _) B'.carrier MB' σ
  have hb : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z = spMap (σ.comp e₂) ≫ z₁ := by
    rw [← spComp (algebraMap (𝓞 L) L) σ, ← spComp e₂ σ, Category.assoc, Category.assoc, hz]
  have hb' : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ = spMap σ ≫ spMap (algebraMap (𝓞 L) L) := by
    rw [Category.comp_id, spComp]
  have hb2 : spMap σ ≫ spMap e₂ = 𝟙 _ ≫ spMap (σ.comp e₂) := by
    rw [Category.id_comp, spComp]

  obtain ⟨core₁, hcore₁⟩ := h.herm _ (Fibre σ B.carrier) Mσ
  have h1 : ∀ a b, (B.metric.form σ).inner a b = h.ip _ (Mσ.pt a) (Mσ.pt b) := by
    intro a b
    rw [← hcore₁]
    refine core_eq _ _ _ (span_tmul σ _) ?_ a b
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    rw [hcore₁]
    exact hB σ e e' _ _ (hMσ e) (hMσ e')

  obtain ⟨Mz, hMz⟩ := exists_transport hb' Mσ'
  have h2 : ∀ a b, HodgeIP t'.G t'.PP.L (spMap σ ≫ spMap (algebraMap (𝓞 L) L)) (Mz.pt a) (Mz.pt b)
      ((B'.metric.form σ).inner a b) := by
    refine GlobalTheory.T.hodge_inner_product_on_span E H (Sp L) (Sp (𝓞 L)) tK t' (spMap (algebraMap (𝓞 L) L)) m' (spMap σ)
      (Fibre σ B'.carrier) Mz (B'.metric.form σ) (Set.range fun e => (1 : ComplexAt σ) ⊗ₜ[𝓞 L] e)
      ⟨0, TensorProduct.tmul_zero _ _⟩ (span_tmul σ _) ?_
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    exact hodge_congr t'.PP.L hb' (hMz _).symm (hMz _).symm (hB' σ e e' _ _ (hMσ' e) (hMσ' e'))

  obtain ⟨Mc, hMc⟩ := exists_transport hb Mσ
  obtain ⟨Mv, hMv⟩ := exists_lift Pσ.m.cart (𝟙 _) (by rw [Category.id_comp]; exact hb.symm) Mσ
  obtain ⟨Mu, hMu⟩ := exists_lift m'.cart (spMap σ) hb'.symm Mσ'
  have hv₀ : lf (Mv.pt x) ≫ Pσ.m.φ = lf (Mc.pt x) := (hMv x).trans (hMc x).symm
  have h3 := GlobalTheory.T.abelian_part_maps_compatible_left E H X t L₁ L e₂ z₁ z hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' B.carrier B'.carrier
    MB MB' f hf σ Pσ mKσ mBσ d1 d2 Mσ hMσ Mσ' hMσ' x (Mv.pt x) (Mu.pt (f.lTensor (ComplexAt σ) x)) (hMv x) (hMu _)

  have hUz : lf (Mu.pt (f.lTensor (ComplexAt σ) x)) ≫ m'.φ = lf (Mz.pt (f.lTensor (ComplexAt σ) x)) :=
    (hMu _).trans (hMz _).symm
  have a1 := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp L) (Sp (𝓞 L)) tK t' (spMap (algebraMap (𝓞 L) L)) m' (spMap σ)
    (Mu.pt (f.lTensor (ComplexAt σ) x)) (Mu.pt (f.lTensor (ComplexAt σ) x))
    (Mz.pt (f.lTensor (ComplexAt σ) x)) (Mz.pt (f.lTensor (ComplexAt σ) x)) hUz hUz).1 _).2
    (h2 (f.lTensor (ComplexAt σ) x) (f.lTensor (ComplexAt σ) x))
  obtain ⟨U, hU⟩ := exists_push mP.cart (spMap σ) (Mu.pt (f.lTensor (ComplexAt σ) x))
  obtain ⟨Vv, hV⟩ := exists_push mBσ.cart (𝟙 _) (Mv.pt x ≫ Pσ.τ.q ≫ Pσ.e.hom)
  have a2 := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp L) (Sp L₁) tK P₁.tB (spMap e₂) mP (spMap σ)
    (Mu.pt (f.lTensor (ComplexAt σ) x)) (Mu.pt (f.lTensor (ComplexAt σ) x)) U U hU hU).1 _).1 a1
  have hUV : lf U = lf Vv := hU.symm.trans (Eq.trans h3 hV)
  have a3 := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp ℂ) (Sp L₁) Pσ.tB P₁.tB (spMap (σ.comp e₂)) mBσ (𝟙 _)
    (Mv.pt x ≫ Pσ.τ.q ≫ Pσ.e.hom) (Mv.pt x ≫ Pσ.τ.q ≫ Pσ.e.hom) Vv Vv hV hV).1 _).2
    (hodge_congr P₁.tB.PP.L hb2 hUV hUV a2)
  have h5 := hQ (spMap (σ.comp e₂) ≫ z₁) Pσ (Mv.pt x) (Mc.pt x) _ (Mv.tan x) hv₀ a3
  have h6 : h.ip _ (Mc.pt x) (Mc.pt x) = (B.metric.form σ).inner x x := by
    rw [h1]
    exact ip_congr h.ip hb.symm (hMc x) (hMc x)
  rw [h6] at h5
  exact h5
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartMapsCompatibleRightStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_maps_compatible_right : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M₀ y) (K₀ : ℝ) (hQ : ∀ (zc : Sp ℂ ⟶ X) (P : AbPart t zc) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt zc ⟶ t.G) (c : ℂ), IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K₀ * (h.ip zc v₀ v₀).re) (B B' : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t.G z B.carrier) (MB' : LieModel t'.G (𝟙 _) B'.carrier) (hB : IsFibre (fun z v w c => c = h.ip z v w) z B MB) (hB' : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B' MB') (f : B.carrier →ₗ[𝓞 L] B'.carrier) (hf : ∀ (e : B.carrier) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), (v.left ≫ P₂.m.φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt e).left) → ((v ≫ P₂.τ.q).left ≫ (P₂.e.hom.left ≫ w ≫ m'.φ) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB'.pt (f e)).left)) (σ : L →+* ℂ) (x : GroundTheory.Heights₂.Heights.Fibre σ B.carrier), sqAt B' σ (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x) ≤ K₀ * sqAt B σ x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SlopeNorm.sqAt_le | exact GlobalTheory.CompanionTheory.Ar.SlopeNorm.sqAt_le | (intros; apply GlobalTheory.CompanionTheory.Ar.SlopeNorm.sqAt_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLieMetricBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SlopeUnif

theorem isGrpPullback_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] :
    IsGrpPullback A B (𝟙 S) e.hom.left := by
  refine ⟨?_, fun T x y x₀ y₀ hx hy => ?_⟩
  · haveI : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · have e₁ : (x * y) ≫ e.hom = (x ≫ e.hom) * (y ≫ e.hom) := by
      first | exact Hom.mul_comp _ _ _ | exact MonObj.mul_comp _ _ _ | exact CategoryTheory.Hom.mul_comp _ _ _
    have : (x * y).left ≫ e.hom.left = ((x ≫ e.hom) * (y ≫ e.hom)).left := by
      rw [← e₁]; rfl
    rw [this]
    exact mul_left_congr (Category.comp_id _) _ _ _ _ hx hy

theorem exists_compare {S S₁ : Scheme.{0}} {f : S₁ ⟶ S} {A A' : Over S₁} {C : Over S} [GrpObj A] [GrpObj A'] [GrpObj C]
    {a : A.left ⟶ C.left} {a' : A'.left ⟶ C.left} (hA : IsGrpPullback A C f a) (hA' : IsGrpPullback A' C f a') :
    ∃ w : A.left ⟶ A'.left, w ≫ a' = a ∧ w ≫ A'.hom = A.hom ∧ IsGrpPullback A A' (𝟙 S₁) w := by
  refine ⟨hA'.1.lift a A.hom hA.1.w, hA'.1.lift_fst _ _ _, hA'.1.lift_snd _ _ _, ?_⟩
  refine IsGrpPullback.cancel hA' ?_ ?_
  · rw [hA'.1.lift_fst, Category.id_comp]; exact hA
  · rw [hA'.1.lift_snd, Category.comp_id]

theorem slope_unif : N1ab → PartI → Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → SlopeBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), 1 ≤ D.p + D.q → ∃ C : ℝ, 0 ≤ C ∧ ∀ (L₀ : Type) [Field L₀] [NumberField L₀] (z₀ : Sp (𝓞 L₀) ⟶ 𝔐.X), ∃ (L : Type) (_ : Field L) (_ : NumberField L) (e : L₀ →+* L), ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G (spMap (RingOfIntegers.mapRingHom e) ≫ z₀) B.carrier), IsFibre (fun z v w c => c = h.ip z v w) _ B MB → B.slopeMax ≤ ((C * Real.log (2 + C + max (-B.normDegree ⊤) 0) + C : ℝ) : EReal) := by
  intro hN hP hR hH hS E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 h hpq
  obtain ⟨K₀, hK₀, hQ⟩ := GlobalTheory.T.lie_metric_height_bound hR E H D l Xo c Y S Ω K J y 𝔐 h hpq
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  obtain ⟨C₁, hC₁, hT⟩ := GlobalTheory.T.semiabelian_lie_metric_height hH 𝔐.X Ω K J y 𝔐.ξ inferInstance 𝔐.all 𝔐.tie 𝔐.t.G 𝔐.t.semi 𝔐.Li 𝔐.M h
  obtain ⟨C₀, hC₀, hSl⟩ := hS
  obtain ⟨Cc, hCc1, hCcK, hCc₁, hCc₀⟩ : ∃ Cc : ℝ, 1 ≤ Cc ∧ K₀ ≤ Cc ∧ C₁ ≤ Cc ∧ C₀ ≤ Cc :=
    ⟨max (max K₀ C₁) (max C₀ 1), by simp, by simp, by simp, by simp⟩
  obtain ⟨C', hC', hPB⟩ := GlobalTheory.T.hermitian_bundle_quotient_degree_bound (Module.finrank Ω 𝔐.Li) Cc hCc1
  refine ⟨C', hC', fun L₀ _ _ z₀ => ?_⟩
  obtain ⟨L₁, _, _, e₁, ⟨P₁⟩⟩ := GlobalTheory.T.exists_abelian_part_extension E H 𝔐.X 𝔐.t L₀ (spMap (algebraMap (𝓞 L₀) L₀) ≫ z₀)
  obtain ⟨σ₁⟩ : Nonempty (L₁ →+* ℂ) := inferInstance
  obtain ⟨P₁c, _, mBc, _, _⟩ := GlobalTheory.T.abelian_part_base_change E H 𝔐.X 𝔐.t L₁ ℂ _ P₁ σ₁
  have hpr : IsPrincipal P₁.tB := (GlobalTheory.T.isPrincipal_base_change_iff E H L₁ ℂ σ₁ P₁.tB P₁c.tB mBc).1 (hQ _ P₁c).1
  obtain ⟨L, _, _, e₂, t', tK, ⟨m'⟩, ⟨mP⟩⟩ := GlobalTheory.T.lie_signature_number_field hN hP E H L₁ P₁.tB hpr
    (GlobalTheory.T.abelian_part_lie_signature E H D l Xo c Y S Ω K J y 𝔐 L₁ _ P₁)
  have hprK : IsPrincipal tK := (GlobalTheory.T.isPrincipal_base_change_iff E H L₁ L e₂ P₁.tB tK mP).2 hpr
  refine ⟨L, inferInstance, inferInstance, e₂.comp e₁, fun B MB hB => ?_⟩
  have hz : spMap (algebraMap (𝓞 L) L) ≫ (spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) ≫ z₀) =
      spMap e₂ ≫ (spMap e₁ ≫ spMap (algebraMap (𝓞 L₀) L₀) ≫ z₀) := by
    have e : spMap (algebraMap (𝓞 L) L) ≫ spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) =
        spMap e₂ ≫ spMap e₁ ≫ spMap (algebraMap (𝓞 L₀) L₀) := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    rw [← Category.assoc, e]
    simp only [Category.assoc]
  obtain ⟨B', MB', hB'⟩ := GlobalTheory.T.principal_hermitian_fibre E H L t' tK m' hprK
  have hslope := hSl E H L t' tK m' hprK B' MB' hB'
  obtain ⟨P₂, mK2, mB2, c1, c2⟩ := GlobalTheory.T.abelian_part_base_change E H 𝔐.X 𝔐.t L₁ L _ P₁ e₂
  obtain ⟨w, hw, hw', hwp⟩ := exists_compare mB2.cart mP.cart
  letI := P₂.τ.addCommGroup
  letI := P₂.τ.grpB
  haveI := P₂.e_hom
  have hφ' : IsGrpPullback P₂.τ.B t'.G (spMap (algebraMap (𝓞 L) L)) (P₂.e.hom.left ≫ w ≫ m'.φ) := by
    have := (isGrpPullback_iso P₂.e).comp (hwp.comp m'.cart)
    simpa using this
  obtain ⟨MT, hMT⟩ := GlobalTheory.T.exists_cocharacter_lie_model (Sp L) P₂.τ.X L (𝟙 _)
  have hcart : IsGrpPullback P₂.tK.G 𝔐.t.G (spMap (algebraMap (𝓞 L) L) ≫ (spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) ≫ z₀)) P₂.m.φ := by
    rw [hz]; exact P₂.m.cart
  obtain ⟨r, bs, hbs⟩ := hT L _ P₂.tK.G P₂.m.φ P₂.τ hcart
  obtain ⟨ε, f, hε, hf, hli, hker, hsur⟩ := GlobalTheory.T.semi_abelian_pullback_torus_extension 𝔐.X 𝔐.t.G 𝔐.t.semi L _ P₂.tK.G P₂.m.φ P₂.τ t'.G _ t'.semi hcart hφ'
    MT hMT B.carrier B'.carrier MB MB' r bs
  have hbd := hbs MT hMT B MB hB ε hε
  have hnb := GlobalTheory.T.abelian_part_maps_compatible_right E H 𝔐.X 𝔐.t L₁ L e₂ _ _ hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' Ω 𝔐.ξ 𝔐.Li 𝔐.M K J y h K₀
    (fun zc P v v₀ c => (hQ zc P).2 v v₀ c) B B' MB MB' hB hB' f hf
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  have hrk := GlobalTheory.T.lie_model_rank_eq_generic 𝔐.X Ω 𝔐.ξ 𝔐.all 𝔐.t.G 𝔐.Li 𝔐.M L _ B.carrier MB
  have hC₁0 : (0 : ℝ) < C₁ := by linarith
  have hCc0 : (0 : ℝ) < Cc := by linarith
  refine hPB L B B' r ε f hrk hli hker hsur ?_ ?_ ?_
  · intro σ u
    have hs : 0 ≤ ∑ a, ‖u a‖ ^ 2 := Finset.sum_nonneg fun a _ => by positivity
    obtain ⟨h₁, h₂⟩ := hbd σ u
    refine ⟨le_trans (mul_le_mul_of_nonneg_right ?_ hs) h₁, h₂.trans (mul_le_mul_of_nonneg_right hCc₁ hs)⟩
    exact inv_anti₀ hC₁0 hCc₁
  · intro σ x
    have h0 : 0 ≤ sqAt B σ x := by
      have := (B.metric.form σ).re_inner_nonneg x
      simpa [sqAt] using this
    exact (hnb σ x).trans (mul_le_mul_of_nonneg_right hCcK h0)
  · refine hslope.trans (EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_right hCc₀ (Real.log_nonneg ?_)))
    have : (0 : ℝ) ≤ max (-B'.normDegree ⊤) 0 := le_max_right _ _
    have h' : (0 : ℝ) ≤ Module.finrank (𝓞 L) B'.carrier := Nat.cast_nonneg _
    linarith

end GlobalTheory.CompanionTheory.Ar.SlopeUnif
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLieMetricBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_lie_metric_bound : N1ab → PartI → Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → SlopeBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), 1 ≤ D.p + D.q → ∃ C : ℝ, 0 ≤ C ∧ ∀ (L₀ : Type) [Field L₀] [NumberField L₀] (z₀ : Sp (𝓞 L₀) ⟶ 𝔐.X), ∃ (L : Type) (_ : Field L) (_ : NumberField L) (e : L₀ →+* L), ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G (spMap (RingOfIntegers.mapRingHom e) ≫ z₀) B.carrier), IsFibre (fun z v w c => c = h.ip z v w) _ B MB → B.slopeMax ≤ ((C * Real.log (2 + C + max (-B.normDegree ⊤) 0) + C : ℝ) : EReal) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SlopeUnif.slope_unif | exact GlobalTheory.CompanionTheory.Ar.SlopeUnif.slope_unif | (intros; apply GlobalTheory.CompanionTheory.Ar.SlopeUnif.slope_unif <;> assumption)
end
