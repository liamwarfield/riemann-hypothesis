module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.DCoord
noncomputable section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.G

section Alg
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {D : ℕ}

private def shear (u : Fin D → B) : MvPolynomial (Fin D) B ≃ₐ[B] MvPolynomial (Fin D) B :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval fun k => MvPolynomial.X k - MvPolynomial.C (u k))
    (MvPolynomial.aeval fun k => MvPolynomial.X k + MvPolynomial.C (u k))
    (by ext k; simp) (by ext k; simp)

private theorem shear_X (u : Fin D → B) (k : Fin D) :
    shear u (MvPolynomial.X k) = MvPolynomial.X k - MvPolynomial.C (u k) := by
  simp [shear]

private theorem shear_C (u : Fin D → B) (b : B) : shear u (MvPolynomial.C b) = MvPolynomial.C b :=
  (shear u).commutes b

private theorem etale_diff (u : Fin D → B)
    (h : (MvPolynomial.aeval u : MvPolynomial (Fin D) R →ₐ[R] B).toRingHom.Etale) :
    (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B)
      (fun k => (1 : B) ⊗ₜ[R] u k - u k ⊗ₜ[R] (1 : B))).Etale := by
  classical
  letI algA : Algebra (MvPolynomial (Fin D) R) B := (MvPolynomial.aeval u).toRingHom.toAlgebra
  letI algP : Algebra (MvPolynomial (Fin D) R) (MvPolynomial (Fin D) B) :=
    MvPolynomial.algebraMvPolynomial
  letI smP : SMul (MvPolynomial (Fin D) R) (MvPolynomial (Fin D) B) := algP.toSMul
  letI modP : Module (MvPolynomial (Fin D) R) (MvPolynomial (Fin D) B) := algP.toModule
  have t1 : IsScalarTower R (MvPolynomial (Fin D) R) B :=
    IsScalarTower.of_algebraMap_eq fun r => by
      simp [RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
  let hm : MvPolynomial (Fin D) B →+* B ⊗[R] B :=
    MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B).toRingHom
      (fun k => u k ⊗ₜ[R] (1 : B))
  letI algPT : Algebra (MvPolynomial (Fin D) B) (B ⊗[R] B) := hm.toAlgebra
  have t2 : IsScalarTower (MvPolynomial (Fin D) R) B (B ⊗[R] B) := inferInstance
  have hcomp : (algebraMap (MvPolynomial (Fin D) R) (B ⊗[R] B)) =
      hm.comp (MvPolynomial.map (algebraMap R B)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [hm, Algebra.TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra,
        Algebra.TensorProduct.tmul_one_eq_one_tmul]
    · intro i
      simp [hm, Algebra.TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra]
  have t3 : IsScalarTower (MvPolynomial (Fin D) R) (MvPolynomial (Fin D) B) (B ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun p => by
      have := congrArg (fun f => f p) hcomp
      simpa [RingHom.algebraMap_toAlgebra] using this
  have t4 : IsScalarTower R (MvPolynomial (Fin D) R) (B ⊗[R] B) := inferInstance
  have hf : IsBaseChange (MvPolynomial (Fin D) R)
      (IsScalarTower.toAlgHom R B (MvPolynomial (Fin D) B)).toLinearMap :=
    (inferInstance : Algebra.IsPushout R (MvPolynomial (Fin D) R) B (MvPolynomial (Fin D) B)).out
  have hpush : Algebra.IsPushout (MvPolynomial (Fin D) R) B (MvPolynomial (Fin D) B) (B ⊗[R] B) := by
    constructor
    refine IsBaseChange.of_comp (T := B) hf ?_
    convert TensorProduct.isBaseChange R B B using 1
    all_goals try rfl
    all_goals try (apply LinearMap.ext; intro b; simp [hm, RingHom.algebraMap_toAlgebra])
  have hE : hm.Etale :=
    RingHom.Etale.isStableUnderBaseChange (MvPolynomial (Fin D) R) B (MvPolynomial (Fin D) B)
      (B ⊗[R] B) h
  have heq : MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B)
      (fun k => (1 : B) ⊗ₜ[R] u k - u k ⊗ₜ[R] (1 : B)) =
      (Algebra.TensorProduct.comm R B B).toAlgHom.toRingHom.comp
        (hm.comp (shear u).toAlgHom.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp [hm, shear_C]
    · intro i
      simp [hm, shear_X]
  rw [heq]
  refine RingHom.Etale.stableUnderComposition _ _ ?_ (RingHom.Etale.of_bijective
    (Algebra.TensorProduct.comm R B B).bijective)
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective
    (shear u).bijective) hE
end Alg

section Geo
variable {R : Type} [CommRing R]

private theorem fromSpec_hom (Z : Sch R) {U : Z.left.Opens} (hU : IsAffineOpen U) :
    (show Spec (CommRingCat.of (Sec Z U)) ⟶ Z.left from hU.fromSpec) ≫ Z.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (Sec Z U))) := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec Z.hom (isAffineOpen_top (Spec (CommRingCat.of R))) hU
    (by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at e
  show hU.fromSpec ≫ Z.hom = _
  rw [← e]
  rfl

private theorem etale_prod (Z : Sch R) {U : Z.left.Opens} (hU : IsAffineOpen U) {N : (XX Z).left.Opens}
    (hN : IsAffineOpen N) (h1 : N ≤ (p1 Z).left ⁻¹ᵁ U) (h2 : N ≤ (p2 Z).left ⁻¹ᵁ U) :
    (Algebra.TensorProduct.productMap (secMap (p1 Z) h1) (secMap (p2 Z) h2)).toRingHom.Etale := by
  let sA : Spec (CommRingCat.of (Sec Z U)) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Sec Z U)))
  let a : Spec (CommRingCat.of (Sec Z U)) ⟶ Z.left := hU.fromSpec
  have ha : a ≫ Z.hom = sA := fromSpec_hom Z hU
  haveI : IsOpenImmersion a := IsAffineOpen.isOpenImmersion_fromSpec hU
  let m : pullback sA sA ⟶ pullback Z.hom Z.hom :=
    pullback.map sA sA Z.hom Z.hom a a (𝟙 _) (by rw [Category.comp_id, ha])
      (by rw [Category.comp_id, ha])
  let fN : Spec Γ((XX Z).left, N) ⟶ pullback Z.hom Z.hom := hN.fromSpec
  let g1 : Spec Γ((XX Z).left, N) ⟶ Spec (CommRingCat.of (Sec Z U)) :=
    Spec.map ((p1 Z).left.appLE U N h1)
  let g2 : Spec Γ((XX Z).left, N) ⟶ Spec (CommRingCat.of (Sec Z U)) :=
    Spec.map ((p2 Z).left.appLE U N h2)
  have e1 : g1 ≫ a = fN ≫ pullback.fst Z.hom Z.hom :=
    IsAffineOpen.SpecMap_appLE_fromSpec (p1 Z).left hU hN h1
  have e2 : g2 ≫ a = fN ≫ pullback.snd Z.hom Z.hom :=
    IsAffineOpen.SpecMap_appLE_fromSpec (p2 Z).left hU hN h2
  have w : g1 ≫ sA = g2 ≫ sA := by
    rw [← ha, ← Category.assoc, e1, ← Category.assoc, e2, Category.assoc, Category.assoc,
      pullback.condition]
  let g : Spec Γ((XX Z).left, N) ⟶ pullback sA sA := pullback.lift g1 g2 w
  have hgm : g ≫ m = fN := by
    apply pullback.hom_ext
    · simp only [g, m, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, e1]
    · simp only [g, m, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, e2]
  haveI : IsOpenImmersion fN := IsAffineOpen.isOpenImmersion_fromSpec hN
  haveI : Etale (g ≫ m) := by rw [hgm]; infer_instance
  haveI : Etale g := Etale.of_comp g m
  let φ : Sec Z U ⊗[R] Sec Z U →+* Sec (XX Z) N :=
    (Algebra.TensorProduct.productMap (secMap (p1 Z) h1) (secMap (p2 Z) h2)).toRingHom
  let g' : Spec (CommRingCat.of (Sec (XX Z) N)) ⟶ pullback sA sA := g
  haveI : Etale g' := inferInstanceAs (Etale g)
  have key : Spec.map (CommRingCat.ofHom φ) ≫ (pullbackSpecIso R (Sec Z U) (Sec Z U)).inv = g' := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      refine Eq.trans ?_ (pullback.lift_fst g1 g2 w).symm
      congr 1
      ext x
      simp [φ, secMap]
      rfl
    · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
      refine Eq.trans ?_ (pullback.lift_snd g1 g2 w).symm
      congr 1
      ext x
      simp [φ, secMap]
      rfl
  have key' : Spec.map (CommRingCat.ofHom φ) = g' ≫ (pullbackSpecIso R (Sec Z U) (Sec Z U)).hom := by
    rw [← key, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hE : Etale (Spec.map (CommRingCat.ofHom φ)) := by rw [key']; infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp hE
end Geo

theorem dCoord : DCoord := by
  intro R _ Z D c
  have h := etale_diff (R := R) c.u c.coord.2
  have h' := etale_prod Z c.coord.1 c.aff c.h1 c.h2
  have h3 := RingHom.Etale.stableUnderComposition _ _ h h'
  convert h3 using 1
  refine MvPolynomial.ringHom_ext (fun b => ?_) fun k => ?_
  · simp [MvPolynomial.coe_eval₂Hom]
  · simp [DChart.s, MvPolynomial.coe_eval₂Hom]

end UpperTheory.Gal.KunnethLefschetz.G
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.CoordEx
noncomputable section
open CategoryTheory AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections

namespace UpperTheory.Gal.KunnethLefschetz.G

theorem coordEx : CoordEx := by
  intro R _ Z D _ z
  obtain ⟨-, -, V, hV, hzV, -, -⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := D) (f := Z.hom) z
  obtain ⟨s, hs, hsQ⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) Z.hom inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (by simp)
  have hz : z ∈ ⨆ f : s, Z.left.basicOpen f.1 := (hV.self_le_iSup_basicOpen_iff.mpr hs) hzV
  rw [TopologicalSpace.Opens.mem_iSup] at hz
  obtain ⟨⟨t, ht⟩, hzt⟩ := hz
  have hQ : RingHom.IsStandardSmoothOfRelativeDimension D _ := hsQ t ht
  have hle : Z.left.basicOpen t ≤ Z.hom ⁻¹ᵁ ⊤ := by simp
  have hVle : V ≤ Z.hom ⁻¹ᵁ ⊤ := by simp
  have key : RingHom.IsStandardSmoothOfRelativeDimension D
      (Z.hom.appLE ⊤ (Z.left.basicOpen t) hle).hom := by
    have := hV.isLocalization_basicOpen t
    let e := IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t)
      Γ(Z.left, Z.left.basicOpen t)
    have h1 : (Z.hom.appLE ⊤ (Z.left.basicOpen t) hle).hom =
        (e : Localization.Away t ≃+* Γ(Z.left, Z.left.basicOpen t)).toRingHom.comp
          ((algebraMap _ (Localization.Away t)).comp (Z.hom.appLE ⊤ V hVle).hom) := by
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
      rw [RingHom.algebraMap_toAlgebra]
      show _ = (Z.hom.appLE ⊤ V hVle ≫
        Z.left.presheaf.map (homOfLE (Z.left.basicOpen_le t)).op).hom x
      rw [Scheme.Hom.appLE_map]
    rw [h1]
    exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ _ hQ
  have hR : RingHom.IsStandardSmoothOfRelativeDimension D
      (algebraMap R (Sec Z (Z.left.basicOpen t))) :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv key
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hR
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial D R
    (Sec Z (Z.left.basicOpen t))
  refine ⟨Z.left.basicOpen t, fun i ↦ g (MvPolynomial.X i), hzt, hV.basicOpen t, ?_⟩
  rwa [← Function.comp_def g MvPolynomial.X, ← MvPolynomial.aeval_unique]

end UpperTheory.Gal.KunnethLefschetz.G
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ExChart
noncomputable section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections
open FunctorialResolution.Blowup

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem mem_map_ker_app_of_pullback_fst_app_eq_zero {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) [IsClosedImmersion g]
    {N : S.Opens} (hN : IsAffineOpen N) {V : X.Opens} (hV : IsAffineOpen V)
    (hVN : V ≤ f ⁻¹ᵁ N) (a : Γ(X, V)) (ha : (pullback.fst f g).app V a = 0) :
    a ∈ Ideal.map (f.appLE N V hVN).hom (RingHom.ker (g.app N).hom) := by
  have hM : IsAffineOpen (g ⁻¹ᵁ N) := hN.preimage g
  set J := Ideal.map (f.appLE N V hVN).hom (RingHom.ker (g.app N).hom) with hJ
  have hδ : Function.Surjective (g.app N).hom := g.app_surjective N hN
  have hker : RingHom.ker (g.app N).hom ≤
      RingHom.ker ((Ideal.Quotient.mk J).comp (f.appLE N V hVN).hom) := by
    intro x hx
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hx
  let ψ : Γ(Y, g ⁻¹ᵁ N) →+* Γ(X, V) ⧸ J :=
    (Ideal.Quotient.lift _ _ hker).comp (RingHom.quotientKerEquivOfSurjective hδ).symm.toRingHom
  have hψ : ∀ b, ψ ((g.app N).hom b) = Ideal.Quotient.mk J ((f.appLE N V hVN).hom b) := by
    intro b
    have e : (RingHom.quotientKerEquivOfSurjective hδ).symm ((g.app N).hom b) =
        Ideal.Quotient.mk _ b := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
      Ideal.Quotient.lift_mk]
    exact Ideal.Quotient.lift_mk _ _ _
  let t : Spec (CommRingCat.of (Γ(X, V) ⧸ J)) ⟶ X :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hV.fromSpec
  let u : Spec (CommRingCat.of (Γ(X, V) ⧸ J)) ⟶ Y :=
    Spec.map (CommRingCat.ofHom ψ) ≫ hM.fromSpec
  have hring : f.appLE N V hVN ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) =
      g.appLE N (g ⁻¹ᵁ N) le_rfl ≫ CommRingCat.ofHom ψ := by
    ext b
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    rw [← Scheme.Hom.app_eq_appLE, hψ]
  have hcond : t ≫ f = u ≫ g := by
    simp only [t, u, Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hN hV hVN,
      ← IsAffineOpen.SpecMap_appLE_fromSpec g hN hM le_rfl, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc, hring]
  let ℓ := pullback.lift t u hcond
  have hℓ : ℓ ≫ pullback.fst f g = t := pullback.lift_fst _ _ _
  have e0 : (⊤ : (Spec (CommRingCat.of (Γ(X, V) ⧸ J))).Opens) ≤ t ⁻¹ᵁ V := by
    intro x _
    show t x ∈ (V : Set X)
    rw [← hV.range_fromSpec]
    simp only [t, Scheme.Hom.comp_apply]
    exact Set.mem_range_self _
  have key : ∀ (m : Spec (CommRingCat.of (Γ(X, V) ⧸ J)) ⟶ X) (hm : m = t)
      (e : ⊤ ≤ m ⁻¹ᵁ V), (m.appLE V ⊤ e).hom a = (t.appLE V ⊤ e0).hom a := by
    rintro m rfl e; rfl
  have h1 : (t.appLE V ⊤ e0).hom a = 0 := by
    rw [← key _ hℓ (by rw [hℓ]; exact e0), Scheme.Hom.comp_appLE]
    simp [ha]
  have h2 : t.appLE V ⊤ e0 = CommRingCat.ofHom (Ideal.Quotient.mk J) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, V) ⧸ J))).inv := by
    simp only [t, Scheme.Hom.comp_appLE, IsAffineOpen.fromSpec_app_self, Category.assoc,
      Scheme.Hom.map_appLE]
    rw [Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [h2] at h1
  have h3 : Ideal.Quotient.mk J a = 0 := by
    rw [CommRingCat.comp_apply] at h1
    change (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, V) ⧸ J))).inv.hom (Ideal.Quotient.mk J a) = 0 at h1
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, V) ⧸ J))).hom.hom h1
    rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h3

theorem exChart : ExChart := by
  intro R _ Z W _ π D c b j
  have hdg : IsClosedImmersion (dg Z).left := by
    change IsClosedImmersion (pullback.diagonal (Over.hom Z)); infer_instance
  have hexI : IsClosedImmersion (exI π).left := by
    change IsClosedImmersion (pullback.fst π.left (dg Z).left); infer_instance
  have hM : IsAffineOpen ((dg Z).left ⁻¹ᵁ c.N) := c.aff.preimage _
  have hE : IsAffineOpen ((exI π).left ⁻¹ᵁ b.V j) := (b.aff j).preimage _
  have hsq : (exG π).left ≫ (dg Z).left = (exI π).left ≫ π.left := by
    change pullback.snd π.left (dg Z).left ≫ _ = pullback.fst π.left (dg Z).left ≫ _
    exact pullback.condition.symm
  have hle : (exI π).left ⁻¹ᵁ b.V j ≤ (exG π).left ⁻¹ᵁ (dg Z).left ⁻¹ᵁ c.N := by
    intro x hx
    have h1 : ((exI π).left ≫ π.left) x ∈ c.N := b.le j hx
    rw [← hsq] at h1
    exact h1
  refine ⟨hM, hE, ?_, hle, ?_⟩
  all_goals
    set φ := (secMap π (b.le j)).toRingHom with hφ
    set δ := (secMap (dg Z) (le_refl ((dg Z).left ⁻¹ᵁ c.N))).toRingHom with hδ
    set α := (secMap (exI π) (le_refl ((exI π).left ⁻¹ᵁ b.V j))).toRingHom with hα
    set γ := (secMap (exG π) hle).toRingHom with hγ
    have hδsurj : Function.Surjective δ := by
      have := (dg Z).left.app_surjective c.N c.aff
      rwa [Scheme.Hom.app_eq_appLE] at this
    have hαsurj : Function.Surjective α := by
      have := (exI π).left.app_surjective (b.V j) (b.aff j)
      rwa [Scheme.Hom.app_eq_appLE] at this
    have hkerδ : RingHom.ker δ = Ideal.span (Set.range c.s) := c.ker
    have hmemker : ∀ p, p ∈ Ideal.span (insert (MvPolynomial.X j - 1)
        (Set.range fun k ↦ MvPolynomial.C (c.s k) - MvPolynomial.C (c.s j) * MvPolynomial.X k)) →
        MvPolynomial.eval₂Hom φ (b.y j) p = 0 := by
      intro p hp
      rw [← b.ker j] at hp
      exact hp
    have hyk : ∀ k, φ (c.s k) = φ (c.s j) * b.y j k := by
      intro k
      have := hmemker _ (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩))
      simp only [map_sub, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X'] at this
      exact sub_eq_zero.mp this
    have hyj : b.y j j = 1 := by
      have := hmemker _ (Ideal.subset_span (Set.mem_insert _ _))
      simp only [map_sub, map_one, MvPolynomial.eval₂Hom_X'] at this
      exact sub_eq_zero.mp this
    have hcomm : ∀ x, α (φ x) = γ (δ x) := by
      intro x
      have key : ∀ (m : (Ex π).left ⟶ (XX Z).left) (hm : m = (exG π).left ≫ (dg Z).left)
          (e : (exI π).left ⁻¹ᵁ b.V j ≤ m ⁻¹ᵁ c.N),
          (m.appLE c.N _ e).hom x =
            (((exG π).left ≫ (dg Z).left).appLE c.N _ (hm ▸ e)).hom x := by
        rintro m rfl e; rfl
      change ((π.left.appLE c.N (b.V j) (b.le j)) ≫
          (exI π).left.appLE (b.V j) _ le_rfl).hom x =
        (((dg Z).left.appLE c.N _ le_rfl) ≫ (exG π).left.appLE _ _ hle).hom x
      rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, key _ hsq.symm]
    have hsk : ∀ k, δ (c.s k) = 0 := fun k ↦ by
      rw [← RingHom.mem_ker, hkerδ]; exact Ideal.subset_span ⟨k, rfl⟩
    have hKer : RingHom.ker α = Ideal.span {φ (c.s j)} := by
      apply le_antisymm
      · intro a ha
        have := mem_map_ker_app_of_pullback_fst_app_eq_zero π.left (dg Z).left c.aff (b.aff j) (b.le j) a (by
          rw [Scheme.Hom.app_eq_appLE]; exact ha)
        have e1 : Ideal.map (π.left.appLE c.N (b.V j) (b.le j)).hom
            (RingHom.ker ((dg Z).left.app c.N).hom) = Ideal.map φ (RingHom.ker δ) := by
          rw [Scheme.Hom.app_eq_appLE]; rfl
        rw [e1, hkerδ, Ideal.map_span] at this
        refine (Ideal.span_le.mpr ?_) this
        rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
        rw [SetLike.mem_coe, hyk k]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, hcomm,
          hsk, map_zero]
    have hBij : Function.Bijective
        (MvPolynomial.eval₂Hom γ fun k : {k // k ≠ j} ↦ α (b.y j k)) := by
      set P := MvPolynomial.eval₂Hom γ fun k : {k // k ≠ j} ↦ α (b.y j k) with hP
      set ev := MvPolynomial.eval₂Hom φ (b.y j) with hev
      let ρ : MvPolynomial (Fin D) _ →+* MvPolynomial {k // k ≠ j} _ :=
        MvPolynomial.eval₂Hom (MvPolynomial.C.comp δ)
          (fun k ↦ if h : k = j then 1 else MvPolynomial.X ⟨k, h⟩)
      have hPρ : P.comp ρ = α.comp ev := by
        apply MvPolynomial.ringHom_ext
        · intro x
          show P (ρ (MvPolynomial.C x)) = α (ev (MvPolynomial.C x))
          simp only [ρ, hP, hev, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
          exact (hcomm x).symm
        · intro k
          by_cases h : k = j
          · subst h; simp [ρ, P, ev, hyj]
          · simp [ρ, P, ev, h]
      have hρren : ρ.comp (MvPolynomial.rename Subtype.val).toRingHom = MvPolynomial.map δ := by
        apply MvPolynomial.ringHom_ext
        · intro x
          simp [ρ]
        · intro k
          simp [ρ, k.2]
      have hPmap : P.comp (MvPolynomial.map δ) =
          α.comp (ev.comp (MvPolynomial.rename Subtype.val).toRingHom) := by
        apply MvPolynomial.ringHom_ext
        · intro x
          simp [P, ev, hcomm]
        · intro k
          simp [P, ev]
      constructor
      · rw [injective_iff_map_eq_zero]
        intro q hq
        obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective δ hδsurj q
        have h1 : α (ev (MvPolynomial.rename Subtype.val q)) = 0 := by
          rw [← hq]; exact (RingHom.congr_fun hPmap q).symm
        have h2 : ev (MvPolynomial.rename Subtype.val q) ∈ Ideal.span {φ (c.s j)} := by
          rw [← hKer, RingHom.mem_ker]; exact h1
        obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp h2
        obtain ⟨p, rfl⟩ := b.surj j r
        have h3 : MvPolynomial.rename Subtype.val q - MvPolynomial.C (c.s j) * p ∈
            RingHom.ker ev := by
          rw [RingHom.mem_ker, map_sub, map_mul, ← hr, hev, MvPolynomial.eval₂Hom_C]
          ring
        rw [b.ker j] at h3
        have h4 : ρ (MvPolynomial.rename Subtype.val q - MvPolynomial.C (c.s j) * p) = 0 := by
          have hle' : Ideal.span (insert (MvPolynomial.X j - 1)
              (Set.range fun k ↦ MvPolynomial.C (c.s k) - MvPolynomial.C (c.s j) *
                MvPolynomial.X k)) ≤ RingHom.ker ρ := by
            rw [Ideal.span_le]
            rintro _ (rfl | ⟨k, rfl⟩)
            · simp [ρ]
            · simp [ρ, hsk]
          exact hle' h3
        rw [map_sub, map_mul] at h4
        simp only [ρ, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, hsk, map_zero, zero_mul,
          sub_zero] at h4
        rw [← RingHom.congr_fun hρren q]
        exact h4
      · intro e
        obtain ⟨a, rfl⟩ := hαsurj e
        obtain ⟨p, rfl⟩ := b.surj j a
        exact ⟨ρ p, RingHom.congr_fun hPρ p⟩
    first
    | exact hKer
    | exact hBij

end UpperTheory.Gal.KunnethLefschetz.G
end
end
