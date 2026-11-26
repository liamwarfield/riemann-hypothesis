module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibrePullbackSiegelTraitModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibrePullbackSiegelTraitModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.GenFibre

theorem exists_generic_pullback : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (W : Type) [CommRing W] [IsDomain W] (f : T.V →+* W) (fK : FractionRing T.V →+* FractionRing W), (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) → ∃ κ : ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).left ⟶ T.A.A.left, IsGrpPullback ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)) T.A.A (spMap fK) κ ∧ κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f) := by
  intro g n o _ ζ F T W _ _ f fK hfK
  have hsq : spMap fK ≫ jK T.V = jK W ≫ spMap f := by
    have h : fK.comp (algebraMap T.V (FractionRing T.V)) = (algebraMap W (FractionRing W)).comp f := RingHom.ext hfK
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, h]
  have gB := ((isGrpPullback_pullback ((Over.pullback (spMap f)).obj T.G) (jK W)).comp
    (isGrpPullback_pullback T.G (spMap f))).congr hsq.symm rfl
  have he := isGrpPullback_pullback T.G (jK T.V)
  set B := (Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)
  have w : (pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f)) ≫ T.G.hom =
      (B.hom ≫ spMap fK) ≫ jK T.V := by
    rw [Category.assoc B.hom]; exact gB.1.w
  obtain ⟨α, h₁, h₂⟩ : ∃ α : B.left ⟶ ((Over.pullback (jK T.V)).obj T.G).left,
      α ≫ pullback.fst T.G.hom (jK T.V) =
        pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f) ∧
      α ≫ ((Over.pullback (jK T.V)).obj T.G).hom = B.hom ≫ spMap fK :=
    ⟨he.1.lift _ _ w, he.1.lift_fst _ _ _, he.1.lift_snd _ _ _⟩
  have gα := he.cancel (gB.congr rfl h₁.symm) h₂
  haveI := T.U.gen_hom
  refine ⟨α ≫ T.U.gen.hom.left, (gα.comp (isGrpPullback_of_iso T.U.gen)).congr (Category.comp_id _) rfl, ?_⟩
  rw [Category.assoc, ← Category.assoc T.U.gen.hom.left, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp]
  exact h₁

end GlobalTheory.Poinc.GenFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibrePullbackSiegelTraitModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericFibre_pullback_siegelTrait_model : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (W : Type) [CommRing W] [IsDomain W] (f : T.V →+* W) (fK : FractionRing T.V →+* FractionRing W), (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) → ∃ κ : ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).left ⟶ T.A.A.left, IsGrpPullback ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)) T.A.A (spMap fK) κ ∧ κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f) := by
  first | exact @GlobalTheory.Poinc.GenFibre.exists_generic_pullback | exact GlobalTheory.Poinc.GenFibre.exists_generic_pullback | (intros; apply GlobalTheory.Poinc.GenFibre.exists_generic_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleTraitFibreEqUniversal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleTraitFibreEqUniversal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc


open GlobalTheory.CechPic in
theorem lam_trait_fibre_eq_univ : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (W : Type) [CommRing W] [IsDomain W] (fK : FractionRing T.V →+* FractionRing W) (G'' : Over (Sp W)) [GrpObj G''] (β : G''.left ⟶ T.G.left) (κ : ((Over.pullback (jK W)).obj G'').left ⟶ T.A.A.left), IsGrpPullback ((Over.pullback (jK W)).obj G'') T.A.A (spMap fK) κ → κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst G''.hom (jK W) ≫ β → ∀ (α₂ : (G2 ((Over.pullback (jK W)).obj G'')).left ⟶ (G2 F.univ.A).left), IsSquare (κ ≫ T.α) α₂ → LBIso (abelian₂ ((Over.pullback (jK W)).obj G'') (T.U.LG.L.pull (pullback.fst G''.hom (jK W) ≫ β))) (F.univ.P.pull α₂) := by
  intro g n o _ ζ F T W _ _ fK G'' _ β κ hκ hκβ α₂ hα₂
  have hL := T.U.LG.isLB
  have hA := T.A.isLB
  have hP := F.univ.isLB
  have hLβ := pull_isLB hL (pullback.fst G''.hom (jK W) ≫ β)
  have hB₁ : (abelian₂ ((Over.pullback (jK W)).obj G'') (T.U.LG.L.pull (pullback.fst G''.hom (jK W) ≫ β))).IsLB :=
    LB.isLB_linComb hLβ _ _
  refine (cls_eq_iff hB₁ (pull_isLB hP α₂)).1 ?_
  have c₂ : cls _ hB₁ = lam (CechPic.pull (pullback.fst G''.hom (jK W) ≫ β) (cls _ hL))
      (fst ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G''))
      (snd ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')) := by
    rw [← cls_pull hL _ hLβ]; exact cls_cube_two hLβ _ _ hB₁
  have hext : CechPic.pull T.U.gen.hom.left (cls _ hA) =
      CechPic.pull (pullback.fst T.G.hom (jK T.V)) (cls _ hL) := by
    have := (cls_eq_iff (pull_isLB hA T.U.gen.hom.left) (pull_isLB hL (pullback.fst T.G.hom (jK T.V)))).2 T.U.ext
    rwa [cls_pull hA, cls_pull hL] at this
  have hΛ : lam (cls _ hA) (fst T.A.A T.A.A) (snd T.A.A T.A.A) = CechPic.pull T.α₂ (cls _ hP) := by
    have hl : (abelian₂ T.A.A T.A.L).IsLB := LB.isLB_linComb hA _ _
    have := (cls_eq_iff hl (pull_isLB hP T.α₂)).2 T.lb
    rw [cls_pull hP] at this
    exact (cls_cube_two hA _ _ hl).symm.trans this
  have hgi : T.U.gen.inv.left ≫ T.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have e₁ : CechPic.pull (pullback.fst G''.hom (jK W) ≫ β) (cls _ hL) = CechPic.pull κ (cls _ hA) := by
    rw [← hκβ, pull_comp, pull_comp, ← hext, ← pull_comp T.U.gen.inv.left, hgi, pull_id]
  rw [c₂, e₁, lam_pull_of_isGrpPullback hκ, cls_pull hP]
  set Q := lift (pushHom hκ _ (fst ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')))
    (pushHom hκ _ (snd ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G''))) with hQdef
  have e₃ : lam (cls _ hA) (pushHom hκ _ (fst ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')))
      (pushHom hκ _ (snd ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G''))) =
      CechPic.pull Q.left (lam (cls _ hA) (fst T.A.A T.A.A) (snd T.A.A T.A.A)) := by
    rw [pull_lam, lift_fst, lift_snd]
  have hQ : Q.left ≫ T.α₂ = α₂ := by
    refine GlobalTheory.UnifLamFibre.isSquare_unique (φ := κ ≫ T.α) ⟨?_, ?_⟩ hα₂
    · rw [Category.assoc, T.sq.1, ← Category.assoc, ← Over.comp_left, lift_fst]
      show ((fst ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')).left ≫ κ) ≫ T.α = _
      rw [Category.assoc]
    · rw [Category.assoc, T.sq.2, ← Category.assoc, ← Over.comp_left, lift_snd]
      show ((snd ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')).left ≫ κ) ≫ T.α = _
      rw [Category.assoc]
  rw [e₃, hΛ, ← pull_comp, hQ]

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleTraitFibreEqUniversalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_trait_fibre_eq_universal : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (W : Type) [CommRing W] [IsDomain W] (fK : FractionRing T.V →+* FractionRing W) (G'' : Over (Sp W)) [GrpObj G''] (β : G''.left ⟶ T.G.left) (κ : ((Over.pullback (jK W)).obj G'').left ⟶ T.A.A.left), IsGrpPullback ((Over.pullback (jK W)).obj G'') T.A.A (spMap fK) κ → κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst G''.hom (jK W) ≫ β → ∀ (α₂ : (G2 ((Over.pullback (jK W)).obj G'')).left ⟶ (G2 F.univ.A).left), IsSquare (κ ≫ T.α) α₂ → LBIso (abelian₂ ((Over.pullback (jK W)).obj G'') (T.U.LG.L.pull (pullback.fst G''.hom (jK W) ≫ β))) (F.univ.P.pull α₂) := by
  first | exact @GlobalTheory.Poinc.lam_trait_fibre_eq_univ | exact GlobalTheory.Poinc.lam_trait_fibre_eq_univ | (intros; apply GlobalTheory.Poinc.lam_trait_fibre_eq_univ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamification
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TraitUniq

theorem form_of_assoc {V V' W : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [CommRing W] [IsDomain W]
    {Dg : DegPre V} {Dg' : DegPre V'} {ϖ : V} {ϖ' : V'} {β : LinearMap.BilinForm ℤ Dg.X}
    {β' : LinearMap.BilinForm ℤ Dg'.X} (hβ : ∀ a b, β a b = β b a) (hβ' : ∀ a b, β' a b = β' b a)
    (hm : IsMonomial Dg ![ϖ] ![β]) (hm' : IsMonomial Dg' ![ϖ'] ![β']) (f : V →+* W) (f' : V' →+* W)
    (ε : Dg.X ≃+ Dg'.X) {w : W} (hw : Irreducible w) {m m' : ℕ} (h : Associated (f ϖ) (w ^ m))
    (h' : Associated (f' ϖ') (w ^ m'))
    (hε : ∀ y r r', PsiCoord Dg y r → PsiCoord Dg' (ε y) r' → Associated (f r ^ 2) (f' r' ^ 2)) :
    ∀ a b, (m : ℤ) * β a b = m' * β' (ε a) (ε b) := by
  have key : ∀ a, (m : ℤ) * β a a = m' * β' (ε a) (ε a) := by
    intro a
    obtain ⟨u₁, n₁, hn₁, c₁⟩ := hm a
    obtain ⟨u₂, n₂, hn₂, c₂⟩ := hm' (ε a)
    have a₁ : Associated (f (u₁ * ∏ i, ![ϖ] i ^ n₁ i)) (w ^ (m * n₁ 0)) := by
      rw [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow, pow_mul]
      exact (associated_unit_mul_left _ _ (u₁.isUnit.map f)).trans h.pow_pow
    have a₂ : Associated (f' (u₂ * ∏ i, ![ϖ'] i ^ n₂ i)) (w ^ (m' * n₂ 0)) := by
      rw [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow, pow_mul]
      exact (associated_unit_mul_left _ _ (u₂.isUnit.map f')).trans h'.pow_pow
    have a₃ := (a₁.pow_pow (n := 2)).symm.trans ((hε a _ _ c₁ c₂).trans (a₂.pow_pow (n := 2)))
    rw [← pow_mul, ← pow_mul] at a₃
    have e := GlobalTheory.SiegLoc.TraitOrd.eq_of_associated_pow hw a₃
    have h₀ : β a a = 2 * n₁ 0 := by simpa using hn₁ 0
    have h₀' : β' (ε a) (ε a) = 2 * n₂ 0 := by simpa using hn₂ 0
    rw [h₀, h₀']
    have e' := congrArg (fun x : ℕ => (x : ℤ)) e
    push_cast at e'
    linarith
  intro a b
  have k := key (a + b)
  have ka := key a
  have kb := key b
  simp only [map_add (f := _), LinearMap.add_apply] at k
  rw [hβ b a, hβ' (ε b) (ε a)] at k
  simp only [mul_add] at k
  linarith

theorem extIso {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {G₁ G₂ : Over (Sp W)} [GrpObj G₁]
    [GrpObj G₂] (h₁ : IsSemiAbelian G₁) (h₂ : IsSemiAbelian G₂)
    (e : (Over.pullback (jK W)).obj G₁ ≅ (Over.pullback (jK W)).obj G₂) (he : IsMonHom e.hom) :
    ∃ E : G₁ ≅ G₂, IsMonHom E.hom ∧ (Over.pullback (jK W)).map E.hom = e.hom := by
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W (FractionRing W) G₁ G₂ h₁ h₂ e.hom he
  obtain ⟨F₁, ⟨hF₁, hF₁'⟩, -⟩ :=
    GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W (FractionRing W) G₂ G₁ h₂ h₁ e.inv inferInstance
  refine ⟨⟨F, F₁, ?_, ?_⟩, hF, hF'⟩
  · exact (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W (FractionRing W) G₁ G₁ h₁ h₁ (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, hF', hF₁', e.hom_inv_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
  · exact (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W (FractionRing W) G₂ G₂ h₂ h₂ (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, hF₁', hF', e.inv_hom_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩

end GlobalTheory.Poinc.TraitUniq

namespace GlobalTheory.Poinc.TraitUniq

variable {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ}

theorem genFib (T : Trait F) {W : Type} [CommRing W] [IsDomain W] (f : T.V →+* W)
    (fK : FractionRing T.V →+* FractionRing W) (hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) :
    ∃ κ : ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).left ⟶ T.A.A.left,
      IsGrpPullback ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)) T.A.A (spMap fK) κ ∧
      κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) =
        pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f) :=
  GlobalTheory.T.exists_genericFibre_pullback_siegelTrait_model g n o ζ F T W f fK hfK

theorem lamPull (T : Trait F) {W : Type} [CommRing W] [IsDomain W] (fK : FractionRing T.V →+* FractionRing W)
    (G'' : Over (Sp W)) [GrpObj G''] (β : G''.left ⟶ T.G.left)
    (κ : ((Over.pullback (jK W)).obj G'').left ⟶ T.A.A.left)
    (hκ : IsGrpPullback ((Over.pullback (jK W)).obj G'') T.A.A (spMap fK) κ)
    (hκβ : κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst G''.hom (jK W) ≫ β)
    (α₂ : (G2 ((Over.pullback (jK W)).obj G'')).left ⟶ (G2 F.univ.A).left) (hα₂ : IsSquare (κ ≫ T.α) α₂) :
    LBIso (abelian₂ ((Over.pullback (jK W)).obj G'') (T.U.LG.L.pull (pullback.fst G''.hom (jK W) ≫ β)))
      (F.univ.P.pull α₂) :=
  GlobalTheory.T.mumfordBundle_trait_fibre_eq_universal g n o ζ F T W fK G'' β κ hκ hκβ α₂ hα₂

end GlobalTheory.Poinc.TraitUniq

namespace GlobalTheory.Poinc.TraitUniq

variable {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ}

theorem isCN (T : Trait F) : GlobalTheory.TorRef.IsCN T.V := ⟨inferInstance, inferInstance, T.complete, T.char⟩

theorem isCN_of_base {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (h : GlobalTheory.Mum.Base W) : GlobalTheory.TorRef.IsCN W :=
  ⟨h.1.1, h.1.2.2.1, h.1.2.2.2, h.2⟩

theorem pull (T : Trait F) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.TorRef.IsCN W) (f : T.V →+* W)
    (hf : Function.Injective f) (hl : IsLocalHom f) (fK : FractionRing T.V →+* FractionRing W)
    (G'' : Over (Sp W)) [GrpObj G''] [IsCommMonObj G''] (β : G''.left ⟶ T.G.left)
    (hβ : IsGrpPullback G'' T.G (spMap f) β) (κ : ((Over.pullback (jK W)).obj G'').left ⟶ T.A.A.left)
    (hκ : IsGrpPullback ((Over.pullback (jK W)).obj G'') T.A.A (spMap fK) κ)
    (hκβ : κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst G''.hom (jK W) ≫ β)
    (α₂ : (G2 ((Over.pullback (jK W)).obj G'')).left ⟶ (G2 F.univ.A).left) (hα₂ : IsSquare (κ ≫ T.α) α₂) :
    ∃ (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G'')
      (ε : D'.toPre.X ≃+ T.D.toPre.X) (L : LB ((Over.pullback (jK W)).obj G'').left), L.IsLB ∧
      LBIso L (U'.LG.L.pull (pullback.fst G''.hom (jK W))) ∧
      LBIso (abelian₂ ((Over.pullback (jK W)).obj G'') L) (F.univ.P.pull α₂) ∧
      ∀ y r, PsiCoord T.D.toPre (ε y) r → ∃ u : Wˣ, PsiCoord D'.toPre y (u * f r) := by
  have pull_isLB {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) : (L.pull F).IsLB := by
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have hΛ := lamPull T fK G'' β κ hκ hκβ α₂ hα₂
  have gB := (isGrpPullback_pullback G'' (jK W)).comp hβ
  obtain ⟨hr, hs⟩ := GlobalTheory.T.rigidified_symmetric_lineBundle_groupPullback _ _ _ T.G _ _ gB T.U.LG T.U.symG T.U.symG_gen
  have hα := hκ.comp T.cart
  obtain ⟨ha, hamp, hkt⟩ := GlobalTheory.T.principalPolarization_of_mumfordBundle_siegelFibre o ζ g n F _ (spMap fK ≫ T.y) _ (κ ≫ T.α) α₂ hα hα₂ _
    (pull_isLB T.U.LG.isLB _) hr hs hΛ
  have hϖ : f T.ϖ ≠ 0 := fun h => T.irr.ne_zero (hf (h.trans (map_zero f).symm))
  obtain ⟨D', A', U', ε, hL, hc⟩ := GlobalTheory.T.exists_uniformisation_baseChange_with_coordinates T.V W (isCN T) hW f hl T.G T.semi T.D T.A T.U
    {p | T.ϖ ∉ p.asIdeal} (PrimeSpectrum.isOpen_basicOpen (a := T.ϖ))
    (fun y => T.mono.psiUnitOn y fun p hp => by simpa using hp) (fun h => hϖ (RingHom.mem_ker.1 h)) G'' β hβ ha hr hs
    hamp hkt
  exact ⟨D', A', U', ε, _, pull_isLB T.U.LG.isLB _, hL, hΛ, hc⟩

end GlobalTheory.Poinc.TraitUniq

namespace GlobalTheory.Poinc.TraitUniq

theorem traitUniq : TraitUniqSt := by
  intro g n o _ ζ F T T' W _ _ _ f f' fK fK' hW hdvr hf hf' hl hl' hK hK' hy w m m' hw hm hm'
  have pull_isLB {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) : (L.pull F).IsLB := by
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have semiPull {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G]
      (h : IsSemiAbelian G) : IsSemiAbelian ((Over.pullback f).obj G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := h.comm; infer_instance
    · have := h.smooth; change Smooth (pullback.snd G.hom f); infer_instance
    · have := h.separated; change IsSeparated (pullback.snd G.hom f); infer_instance
    · have := h.quasiCompact; change QuasiCompact (pullback.snd G.hom f); infer_instance
    · have := h.geomConnected; change GeometricallyConnected (pullback.snd G.hom f); infer_instance
    · intro Ω _ _ q
      obtain ⟨E⟩ := h.fibres Ω (q ≫ f)
      exact ⟨torusExtOfIso (pullCompIso q f G) E⟩
  haveI := hdvr
  have hWC := isCN_of_base hW
  have hs₁ : IsSemiAbelian ((Over.pullback (spMap f)).obj T.G) := semiPull (spMap f) T.G T.semi
  have hs₂ : IsSemiAbelian ((Over.pullback (spMap f')).obj T'.G) := semiPull (spMap f') T'.G T'.semi
  obtain ⟨κ₁, hκ₁, hκβ₁⟩ := genFib T f fK hK
  obtain ⟨κ₂, hκ₂, hκβ₂⟩ := genFib T' f' fK' hK'
  have hα₁ := hκ₁.comp T.cart
  have hα₂ := (hκ₂.comp T'.cart).congr hy.symm rfl
  obtain ⟨e, he, heα⟩ := grpPullback_iso hα₁ hα₂
  obtain ⟨E, hE, hEe⟩ := extIso hs₁ hs₂ e he
  have w₁ := hα₁.1.w
  let α₂ := pullback.map ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).hom
    ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).hom F.univ.A.hom F.univ.A.hom
    (κ₁ ≫ T.α) (κ₁ ≫ T.α) (spMap fK ≫ T.y) w₁.symm w₁.symm
  have hsq : IsSquare (κ₁ ≫ T.α) α₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hβ' : IsGrpPullback ((Over.pullback (spMap f)).obj T.G) T'.G (spMap f')
      (E.hom.left ≫ pullback.fst T'.G.hom (spMap f')) :=
    ((isGrpPullback_of_iso E).comp (isGrpPullback_pullback T'.G (spMap f'))).congr (Category.id_comp _) rfl
  have hκ' := ((isGrpPullback_of_iso e).comp hκ₂).congr (Category.id_comp _) rfl
  have hκβ' : (e.hom.left ≫ κ₂) ≫ T'.U.gen.inv.left ≫ pullback.fst T'.G.hom (jK T'.V) =
      pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ E.hom.left ≫ pullback.fst T'.G.hom (spMap f') := by
    rw [Category.assoc, hκβ₂, ← Category.assoc, ← Category.assoc, ← hEe]
    congr 1
    exact pullback.lift_fst _ _ _
  have hsq' : IsSquare ((e.hom.left ≫ κ₂) ≫ T'.α) α₂ := by rw [Category.assoc, heα]; exact hsq
  obtain ⟨E₁, A₁, U₁, ε₁, L₁, l₁, i₁, m₁, c₁⟩ := pull T hWC f hf hl fK _ _ (isGrpPullback_pullback T.G (spMap f))
    κ₁ hκ₁ hκβ₁ α₂ hsq
  obtain ⟨E₂, A₂, U₂, ε₂, L₂, l₂, i₂, m₂, c₂⟩ := pull T' hWC f' hf' hl' fK' _ _ hβ' _ hκ' hκβ' α₂ hsq'
  have hΛ : LBIso (abelian₂ _ L₂) (abelian₂ _ L₁) :=
    LBIso.trans (DVR.linComb_isLB _ l₂ _ _) (pull_isLB F.univ.isLB _) (DVR.linComb_isLB _ l₁ _ _) m₂ m₁.symm
  obtain ⟨ε, hε⟩ := GlobalTheory.SqUnifCoord.main W hWC _ hs₁ E₂ E₁ A₂ A₁ U₂ U₁
    (GlobalTheory.squares_iso_of_lam_generic W hWC _ hs₁ E₂ E₁ A₂ A₁ U₂ U₁ L₂ L₁ l₂ l₁ i₂ i₁ hΛ)
  let ε₀ : T.D.toPre.X ≃+ T'.D.toPre.X := (ε₁.symm.trans ε).trans ε₂
  have hε₀ : ∀ z r₁ r₂, PsiCoord T.D.toPre z r₁ → PsiCoord T'.D.toPre (ε₀ z) r₂ →
      Associated (f r₁ ^ 2) (f' r₂ ^ 2) := by
    intro z r₁ r₂ h₁ h₂
    obtain ⟨u₁, k₁⟩ := c₁ (ε₁.symm z) r₁ (by rwa [AddEquiv.apply_symm_apply])
    obtain ⟨u₂, k₂⟩ := c₂ (ε (ε₁.symm z)) r₂ h₂
    have := hε _ _ _ k₂ k₁
    rw [mul_pow, mul_pow] at this
    exact ((associated_unit_mul_left _ _ (u₁.isUnit.pow 2)).symm.trans this.symm).trans
      (associated_unit_mul_left _ _ (u₂.isUnit.pow 2))
  exact ⟨ε₀, form_of_assoc T.symm T'.symm T.mono T'.mono f f' ε₀ hw hm hm' hε₀⟩

end GlobalTheory.Poinc.TraitUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trait_lattices_iso_forms_proportional_ramification : TraitUniqSt := by
  first | exact @GlobalTheory.Poinc.TraitUniq.traitUniq | exact GlobalTheory.Poinc.TraitUniq.traitUniq | (intros; apply GlobalTheory.Poinc.TraitUniq.traitUniq <;> assumption)
end
