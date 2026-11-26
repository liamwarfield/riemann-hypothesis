module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsMultiplicative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsDiagMemMaximal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegDataFromLowerBaseAfterMonomialExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRelationPullbackMonomialConstants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRelationPullbackMonomialConstants
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodPull

open GlobalTheory.TChart

theorem gm_unitOn_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (u : Rˣ) (z : Sp R') :
    gm (𝟙 (Sp R')) z ⊤ (unitOn (Units.map f.toMonoidHom u)) =
      Units.map ((spMap f).stalkMap z).hom.toMonoidHom (gm (𝟙 (Sp R)) (spMap f z) ⊤ (unitOn u)) := by
  rw [← GlobalTheory.ConstFam.gm_comp_stalkMap (spMap f) (𝟙 _) z ⊤ trivial, Category.comp_id]
  apply Units.ext
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial]
  have e := congrArg (fun g => g.hom (u : R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [unitOn, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [e]
  simp [Scheme.Hom.appTop]
  rfl

theorem periods_pull : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.X) {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (f₁ : V →+* V₁) (κ₁ : W →+* V₁) (e : (Fin T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β₂ : (G2 B').left ⟶ (G2 D.P.A).left) (β₂' : (G2 B').left ⟶ (G2 T.B).left) (x : (Fin T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')) (w₁ : LB.Iso ((abelian₂ D.P.A D.P.L).pull β₂) ((abelian₂ T.B T.M.L).pull β₂')) (q : (Fin T.r → ℤ) → (Fin T.r → ℤ) → (FractionRing V₁)ˣ), Function.Injective f₁ → PeriodRel D T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegPre V₂) (hD : IsPullDeg (f₂.comp f₁) D D') (Φ : D'.P.A.left ⟶ B'.left) (gΦ : IsGrpPullback D'.P.A B' (spMap f₂) Φ), (∀ a, (D'.c a).left ≫ Φ = spMap f₂ ≫ (x (hD.xe.trans (e₀.symm.trans e.symm) a)).left) → ∀ (w : LB.Iso (abelian₂ D'.P.A D'.P.L) ((abelian₂ T.B T.M.L).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂'))), (∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D'.P.A).left) (z : Z) (J : (Z ⟶ T.B.left) → T.M.L.ι) (J₁ : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good T.M.L z J → Good D.P.L z J₁ → Good D'.P.L z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw hD.w (p ≫ lamφ D'.P.A I) z (J₁ ((p ≫ lamφ D'.P.A I) ≫ GlobalTheory.PsiEvenPull.proj hD)) (J' (p ≫ lamφ D'.P.A I)) ^ lamε I) → ∀ a b : D'.X, ∃ k : (FractionRing V₂)ˣ, (k : FractionRing V₂) = ∏ i, algebraMap V₂ (FractionRing V₂) (s i) ^ ((n : ℤ) * ε i (hD.xe.trans (e₀.symm.trans e.symm) a) (hD.xe.trans (e₀.symm.trans e.symm) b)) ∧ ∀ z J J', Good T.M.L z J → Good D'.P.L z J' → val (D'.tau a b) (𝟙 _) z J' = gm (𝟙 (TK V₂).left) z ⊤ (unitOn k) * (lamVal w (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left z J J' * val (T.τ₀ ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) a) ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J) := by
  intro n V _ _ D r e₀ o W _ _ _ T V₁ _ _ f₁ κ₁ e B' _ β₂ β₂' x w₁ q hf₁ hP V₂ _ _ f₂ fK I _ s ε hfK hq D' hD Φ gΦ hc w hw a b
  refine ⟨Units.map fK.toMonoidHom (q (hD.xe.trans (e₀.symm.trans e.symm) a) (hD.xe.trans (e₀.symm.trans e.symm) b)),
    hq _ _, ?_⟩
  intro z J J' hJ hJ'
  set E := hD.xe.trans (e₀.symm.trans e.symm) with hE
  obtain ⟨κK, hκK, -⟩ := GlobalTheory.HalfBC.exists_kappa f₁ f₂ fK hfK hf₁
  let g₀ : (TK V₂).left ⟶ (TK V₁).left := spMap fK
  have sg : g₀ ≫ jK V₁ = jK V₂ ≫ spMap f₂ := GlobalTheory.HalfBC.gam_comm f₂ fK hfK
  choose J₁ hJ₀ using fun χ : (TK V₂).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  have hJ₁ : Good D.P.L z J₁ := hJ₀
  have cE : ∀ a, (e.trans e₀) (E a) = hD.xe a := fun a => by simp [E]
  have t₁ := hP κK hκK (E a) (E b) (g₀ z) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => J₁ (g₀ ≫ ψ))
    (fun ψ => hJ (g₀ ≫ ψ)) (fun ψ => hJ₁ (g₀ ≫ ψ))
  rw [cE, cE] at t₁
  have t₂ := (congrArg (Units.map (g₀.stalkMap z).hom.toMonoidHom) t₁).trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (map_mul _ _ _)))
  have n₁ : val (D.tau (hD.xe a) (hD.xe b)) (g₀ ≫ κK) z J₁ = Units.map (g₀.stalkMap z).hom.toMonoidHom
      (val (D.tau (hD.xe a) (hD.xe b)) κK (g₀ z) (fun ψ => J₁ (g₀ ≫ ψ))) :=
    Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ κK g₀ z J₁ hJ₁).2.2.1 _)
  have h0 : g₀ ≫ (TK V₁).hom ≫ spMap κ₁ = (TK V₂).hom ≫ spMap (f₂.comp κ₁) := by
    show g₀ ≫ jK V₁ ≫ spMap κ₁ = jK V₂ ≫ spMap (f₂.comp κ₁)
    rw [← Category.assoc, sg, Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap']
  have n₀ : val (T.τ₀ ((n : ℤ) • E a) ((n : ℤ) • E b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J =
      Units.map (g₀.stalkMap z).hom.toMonoidHom (val (T.τ₀ ((n : ℤ) • E a) ((n : ℤ) • E b))
        ((TK V₁).hom ≫ spMap κ₁) (g₀ z) (fun ψ => J (g₀ ≫ ψ))) := by
    rw [← h0]; exact Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ _ g₀ z J hJ).2.2.1 _)
  have nC : gm (𝟙 (TK V₂).left) z ⊤ (unitOn (Units.map fK.toMonoidHom (q (E a) (E b)))) =
      Units.map (g₀.stalkMap z).hom.toMonoidHom (gm (𝟙 (TK V₁).left) (g₀ z) ⊤ (unitOn (q (E a) (E b)))) :=
    gm_unitOn_map fK _ z
  have ni : isoVal w₁ (g₀ ≫ (lift (toUnit (TK V₁) ≫ x (E a)) (toUnit (TK V₁) ≫ x (E b))).left) z J J₁ =
      Units.map (g₀.stalkMap z).hom.toMonoidHom (isoVal w₁ (lift (toUnit (TK V₁) ≫ x (E a))
        (toUnit (TK V₁) ≫ x (E b))).left (g₀ z) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => J₁ (g₀ ≫ ψ))) := by
    unfold isoVal
    simp only [Category.assoc]
    refine GlobalTheory.ConstFam.gm_comp_stalkMap g₀ _ z _ ?_ _
    exact ⟨mem_pull.2 (Set.mem_iInter.2 fun I => hJ _), mem_pull.2 (Set.mem_iInter.2 fun I => hJ₁ _)⟩
  have hr : 𝟙 _ ≫ jK V₂ ≫ spMap (f₂.comp f₁) = (g₀ ≫ κK) ≫ jK V := by
    rw [Category.id_comp, Category.assoc, hκK, ← Category.assoc, sg, Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap' f₁ f₂]
  have tv := GlobalTheory.ArcPull.tau_val hD (g₀ ≫ κK) (𝟙 _) hr hJ₁ hJ' a b
  have A : val (D.tau (hD.xe a) (hD.xe b)) (g₀ ≫ κK) z J₁ =
      gm (𝟙 (TK V₂).left) z ⊤ (unitOn (Units.map fK.toMonoidHom (q (E a) (E b)))) *
        (isoVal w₁ (g₀ ≫ (lift (toUnit (TK V₁) ≫ x (E a)) (toUnit (TK V₁) ≫ x (E b))).left) z J J₁ *
          val (T.τ₀ ((n : ℤ) • E a) ((n : ℤ) • E b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J) := by
    rw [n₁, t₂, nC, ni, n₀]
  have hx : ∀ χ, (toUnit (TK V₂) ≫ D'.c χ).left ≫ Φ = g₀ ≫ (toUnit (TK V₁) ≫ x (E χ)).left := fun χ => by
    show (jK V₂ ≫ (D'.c χ).left) ≫ Φ = spMap fK ≫ jK V₁ ≫ (x (E χ)).left
    rw [Category.assoc, hc, ← Category.assoc, ← sg, Category.assoc]
  have hPq : (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left ≫ GlobalTheory.HalfBC.sqOf gΦ =
      g₀ ≫ (lift (toUnit (TK V₁) ≫ x (E a)) (toUnit (TK V₁) ≫ x (E b))).left := by
    have sq1 : GlobalTheory.HalfBC.sqOf gΦ ≫ (fst B' B').left = (fst D'.P.A D'.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_fst (pushPt gΦ.1.w (fst D'.P.A D'.P.A)) (pushPt gΦ.1.w (snd D'.P.A D'.P.A)))
    have sq2 : GlobalTheory.HalfBC.sqOf gΦ ≫ (snd B' B').left = (snd D'.P.A D'.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_snd (pushPt gΦ.1.w (fst D'.P.A D'.P.A)) (pushPt gΦ.1.w (snd D'.P.A D'.P.A)))
    apply pullback.hom_ext
    · show _ ≫ (fst B' B').left = _ ≫ (fst B' B').left
      rw [Category.assoc, sq1, ← Category.assoc, ← Over.comp_left, lift_fst,
        Category.assoc, ← Over.comp_left, lift_fst]
      exact hx a
    · show _ ≫ (snd B' B').left = _ ≫ (snd B' B').left
      rw [Category.assoc, sq2, ← Category.assoc, ← Over.comp_left, lift_snd,
        Category.assoc, ← Over.comp_left, lift_snd]
      exact hx b
  let h : ((TK V₂).left ⟶ D'.P.A.left) → ((TK V₂).left.presheaf.stalk z)ˣ :=
    fun q => gw hD.w q z (J₁ (q ≫ GlobalTheory.PsiEvenPull.proj hD)) (J' q)
  have K := (hw _ (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left z J J₁ J' hJ hJ₁ hJ').trans
    (congrArg₂ (· * ·) (congrArg (fun q => isoVal w₁ q z J J₁) hPq)
      (prod_lam (DVR.cP D' (TK V₂) a) (DVR.cP D' (TK V₂) b) h))
  rw [← DVR.cPoint_add] at K
  have c₀ : ∀ χ, GlobalTheory.ArcPull.om hD.w z J₁ J' (𝟙 _ ≫ D'.xK χ) = h (DVR.cP D' (TK V₂) χ).left := fun χ => by
    rw [Category.id_comp]; rfl
  have c₁ : GlobalTheory.ArcPull.om hD.w z J₁ J' (𝟙 _ ≫ (1 : TK V₂ ⟶ D'.P.A).left) = h (1 : TK V₂ ⟶ D'.P.A).left := by
    rw [Category.id_comp]; rfl
  rw [c₀, c₀, c₀, c₁] at tv
  rw [K]
  have F := tv.symm.trans A
  generalize val (D'.tau a b) (𝟙 _) z J' = X at F ⊢
  generalize h (DVR.cP D' (TK V₂) (a + b)).left = Y₀ at F ⊢
  generalize h (DVR.cP D' (TK V₂) a).left = Y₁ at F ⊢
  generalize h (DVR.cP D' (TK V₂) b).left = Y₂ at F ⊢
  generalize h (1 : TK V₂ ⟶ D'.P.A).left = Y₃ at F ⊢
  have F' := congrArg Additive.ofMul F
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at F' ⊢
  linear_combination (norm := abel) F'

end GlobalTheory.PeriodPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRelationPullbackMonomialConstantsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_relation_pullback_monomial_constants : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.X) {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (f₁ : V →+* V₁) (κ₁ : W →+* V₁) (e : (Fin T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β₂ : (G2 B').left ⟶ (G2 D.P.A).left) (β₂' : (G2 B').left ⟶ (G2 T.B).left) (x : (Fin T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')) (w₁ : LB.Iso ((abelian₂ D.P.A D.P.L).pull β₂) ((abelian₂ T.B T.M.L).pull β₂')) (q : (Fin T.r → ℤ) → (Fin T.r → ℤ) → (FractionRing V₁)ˣ), Function.Injective f₁ → PeriodRel D T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegPre V₂) (hD : IsPullDeg (f₂.comp f₁) D D') (Φ : D'.P.A.left ⟶ B'.left) (gΦ : IsGrpPullback D'.P.A B' (spMap f₂) Φ), (∀ a, (D'.c a).left ≫ Φ = spMap f₂ ≫ (x (hD.xe.trans (e₀.symm.trans e.symm) a)).left) → ∀ (w : LB.Iso (abelian₂ D'.P.A D'.P.L) ((abelian₂ T.B T.M.L).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂'))), (∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D'.P.A).left) (z : Z) (J : (Z ⟶ T.B.left) → T.M.L.ι) (J₁ : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good T.M.L z J → Good D.P.L z J₁ → Good D'.P.L z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw hD.w (p ≫ lamφ D'.P.A I) z (J₁ ((p ≫ lamφ D'.P.A I) ≫ GlobalTheory.PsiEvenPull.proj hD)) (J' (p ≫ lamφ D'.P.A I)) ^ lamε I) → ∀ a b : D'.X, ∃ k : (FractionRing V₂)ˣ, (k : FractionRing V₂) = ∏ i, algebraMap V₂ (FractionRing V₂) (s i) ^ ((n : ℤ) * ε i (hD.xe.trans (e₀.symm.trans e.symm) a) (hD.xe.trans (e₀.symm.trans e.symm) b)) ∧ ∀ z J J', Good T.M.L z J → Good D'.P.L z J' → val (D'.tau a b) (𝟙 _) z J' = gm (𝟙 (TK V₂).left) z ⊤ (unitOn k) * (lamVal w (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left z J J' * val (T.τ₀ ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) a) ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J) := by
  first | exact @GlobalTheory.PeriodPull.periods_pull | exact GlobalTheory.PeriodPull.periods_pull | (intros; apply GlobalTheory.PeriodPull.periods_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCompGroupPullbackIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCompGroupPullbackIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LamPullComp

section Iso

variable {S S₁ S₂ : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {B' : Over S₁} [GrpObj B']
  {G' : Over S₂} [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left} {β₂ : (G2 B').left ⟶ (G2 G).left}
  {sq : (G2 G').left ⟶ (G2 B').left} {L : LB G.left} {L' : LB G'.left}

theorem pt_eq (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (I : ULift.{0} (Finset (Fin 2))) (x : (G2 G').left) :
    lamφ G I (β₂ (sq x)) = φ (lamφ G' I x) :=
  congrArg (fun g => g x) (h I)

theorem iso_le (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ)
    (p : (((abelian₂ G L).pull β₂).pull sq).ι × (abelian₂ G' L').ι) (I : ULift.{0} (Finset (Fin 2))) :
    (((abelian₂ G L).pull β₂).pull sq).U p.1 ⊓ (abelian₂ G' L').U p.2 ≤
      lamφ G' I ⁻¹ᵁ ((L.pull φ).U (fun _ => p.1 PUnit.unit PUnit.unit I) ⊓ L'.U (p.2 I)) := fun x hx =>
  ⟨mem_pull.2 (by
    have := Set.mem_iInter.1 (mem_pull.1 (mem_pull.1 hx.1)) I
    show φ (lamφ G' I x) ∈ _
    rw [← pt_eq h I x]; exact this), Set.mem_iInter.1 hx.2 I⟩

def iso2 (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (v : LB.Iso L' (L.pull φ)) :
    LB.Iso (abelian₂ G' L') (((abelian₂ G L).pull β₂).pull sq) :=
  ⟨fun p => ∏ I, (res (iso_le h p I)
    (pullU (lamφ G' I) _ (v.s (fun _ => p.1 PUnit.unit PUnit.unit I, p.2 I)))) ^ lamε I⟩

theorem mumfordBundle_pullback_composite_germ_iso (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (v : LB.Iso L' (L.pull φ)) {Y : Scheme.{0}}
    (r : Y ⟶ (G2 G').left) (y : Y) (j : PUnit → ULift.{0} (Finset (Fin 2)) → L.ι)
    (k : ULift.{0} (Finset (Fin 2)) → L'.ι)
    (hj : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j PUnit.unit I)) (hk : ∀ I, lamφ G' I (r y) ∈ L'.U (k I)) :
    gw (iso2 h v) r y j k = ∏ I, gw v (r ≫ lamφ G' I) y (j PUnit.unit I) (k I) ^ lamε I := by
  have hm : r y ∈ (((abelian₂ G L).pull β₂).pull sq).U (fun _ => j) ⊓ (abelian₂ G' L').U k :=
    ⟨mem_pull.2 (mem_pull.2 (Set.mem_iInter.2 fun I => by
      show lamφ G I (β₂ (sq (r y))) ∈ L.U (j PUnit.unit I)
      rw [pt_eq h]; exact hj I)), Set.mem_iInter.2 hk⟩
  unfold gw
  dsimp only [iso2]
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun I _ => (map_zpow _ _ _).trans (congrArg (· ^ lamε I) ?_))
  exact (gm_res r y _ hm _).trans (gm_pull r (lamφ G' I) y ((L.pull φ).U (fun _ => j PUnit.unit I) ⊓ L'.U (k I))
    ⟨mem_pull.2 (hj I), hk I⟩ _)

theorem mumfordBundle_pullback_composite_isGen (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (v : LB.Iso L' (L.pull φ)) (hv : PGen v) :
    PGen (iso2 h v) := by
  intro Y r y j j' k k' hj hj' hk hk'
  have bj := mem_pull.1 hj
  have bj' := mem_pull.1 hj'
  have aj : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j PUnit.unit I) := fun I => by
    rw [← pt_eq h I]; exact Set.mem_iInter.1 bj I
  have aj' : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j' PUnit.unit I) := fun I => by
    rw [← pt_eq h I]; exact Set.mem_iInter.1 bj' I
  have ak : ∀ I, lamφ G' I (r y) ∈ L'.U (k I) := fun I => Set.mem_iInter.1 hk I
  have ak' : ∀ I, lamφ G' I (r y) ∈ L'.U (k' I) := fun I => Set.mem_iInter.1 hk' I
  rw [mumfordBundle_pullback_composite_germ_iso h v r y j k aj ak, mumfordBundle_pullback_composite_germ_iso h v r y j' k' aj' ak']
  have e₀ := gm_pull_g (abelian₂ G L) β₂ (r ≫ sq) y j j' hj hj'
  have e₁ := gm_linComb L (lamφ G) lamε ((r ≫ sq) ≫ β₂) y (j PUnit.unit) (j' PUnit.unit) bj bj'
  have e₂ := gm_linComb L' (lamφ G') lamε r y k k' hk hk'
  erw [e₀, e₁, e₂]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun I _ => ?_
  rw [hv Y (r ≫ lamφ G' I) y (j PUnit.unit I) (j' PUnit.unit I) (k I) (k' I) (aj I) (aj' I) (ak I) (ak' I),
    Category.assoc, Category.assoc, Category.assoc, h, mul_zpow, mul_zpow, inv_zpow]

end Iso

theorem lamIso_comp_pull : ∀ {S S₁ S₂ S₀ : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (B' : Over S₁) [GrpObj B'] (G' : Over S₂) [GrpObj G'] [IsCommMonObj G'] (T : Over S₀) [GrpObj T] [IsCommMonObj T] (f₁ : S₁ ⟶ S) (f₂ : S₂ ⟶ S₁) (β' : B'.left ⟶ G.left) (Φ : G'.left ⟶ B'.left) (φ : G'.left ⟶ G.left) (β₂ : (G2 B').left ⟶ (G2 G).left) (β₂' : (G2 B').left ⟶ (G2 T).left) (L : LB G.left) (L' : LB G'.left) (M : LB T.left) (gp' : IsGrpPullback B' G f₁ β') (gΦ : IsGrpPullback G' B' f₂ Φ), IsSquare β' β₂ → Φ ≫ β' = φ → L.IsLB → L'.IsLB → M.IsLB → ∀ (v : LB.Iso L' (L.pull φ)) (w₁ : LB.Iso ((abelian₂ G L).pull β₂) ((abelian₂ T M).pull β₂')), v.IsGen → w₁.IsGen → ∃ w : LB.Iso (abelian₂ G' L') ((abelian₂ T M).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂')), w.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 G').left) (z : Z) (J : (Z ⟶ T.left) → M.ι) (J₁ : (Z ⟶ G.left) → L.ι) (J' : (Z ⟶ G'.left) → L'.ι), Good M z J → Good L z J₁ → Good L' z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw v (p ≫ lamφ G' I) z (J₁ ((p ≫ lamφ G' I) ≫ φ)) (J' (p ≫ lamφ G' I)) ^ lamε I := by
  intro S S₁ S₂ S₀ G _ _ B' _ G' _ _ T _ _ f₁ f₂ β' Φ φ β₂ β₂' L L' M gp' gΦ hsq hΦ hL hL' hM v w₁ hv hw₁
  have gp : IsGrpPullback G' G (f₂ ≫ f₁) φ := (IsGrpPullback.comp gΦ gp').congr rfl hΦ
  have e1 : GlobalTheory.HalfBC.sqOf gΦ ≫ β₂ = GlobalTheory.HalfBC.sqOf gp := by
    apply pullback.hom_ext
    · show _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, hsq.1, ← Category.assoc]
      unfold GlobalTheory.HalfBC.sqOf
      rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
      show ((fst G' G').left ≫ Φ) ≫ β' = (fst G' G').left ≫ φ
      rw [Category.assoc, hΦ]
    · show _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, hsq.2, ← Category.assoc]
      unfold GlobalTheory.HalfBC.sqOf
      rw [← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]
      show ((snd G' G').left ≫ Φ) ≫ β' = (snd G' G').left ≫ φ
      rw [Category.assoc, hΦ]
  have h : ∀ I, GlobalTheory.HalfBC.sqOf gΦ ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ := fun I => by
    rw [← Category.assoc, e1, GlobalTheory.HalfBC.sqOf_lamφ]
  have hΛT : (abelian₂ T M).IsLB := DVR.linComb_isLB _ hM _ _
  have hΛG : ((abelian₂ G L).pull β₂).IsLB := LB.isLB_pull (DVR.linComb_isLB _ hL _ _) _
  have hΛ' : (abelian₂ G' L').IsLB := DVR.linComb_isLB _ hL' _ _
  obtain ⟨w, Tw⟩ := exists_comp hΛG w₁ (iso2 h v) ((isGen_iff _).1 hw₁) (mumfordBundle_pullback_composite_isGen h v ((isGen_iff v).1 hv)) hΛT hΛ'
  refine ⟨w, (isGen_iff _).2 (Tw.pgen_comp hΛG ((isGen_iff _).1 hw₁) (mumfordBundle_pullback_composite_isGen h v ((isGen_iff v).1 hv))), ?_⟩
  intro Z p z J J₁ J' hJ hJ₁ hJ'
  have t := Tw Z p z (fun I => J (p ≫ (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ lamφ T I))
    (fun _ I => J₁ ((p ≫ lamφ G' I) ≫ φ)) (fun I => J' (p ≫ lamφ G' I))
    (Set.mem_iInter.2 fun I => hJ (p ≫ (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ lamφ T I))
    (mem_pull.2 (Set.mem_iInter.2 fun I => by
      show lamφ G I (β₂ (GlobalTheory.HalfBC.sqOf gΦ (p z))) ∈ L.U (J₁ ((p ≫ lamφ G' I) ≫ φ))
      rw [pt_eq h]; exact hJ₁ ((p ≫ lamφ G' I) ≫ φ)))
    (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ G' I))
  refine t.trans (congrArg₂ (· * ·) ?_ ?_)
  · show _ = gw w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z (fun I => J ((p ≫ GlobalTheory.HalfBC.sqOf gΦ) ≫ β₂' ≫ lamφ T I))
      (fun _ I => J₁ ((p ≫ GlobalTheory.HalfBC.sqOf gΦ) ≫ β₂ ≫ lamφ G I))
    simp only [Category.assoc, h]
  · exact mumfordBundle_pullback_composite_germ_iso h v p z _ _ (fun I => hJ₁ ((p ≫ lamφ G' I) ≫ φ)) (fun I => hJ' (p ≫ lamφ G' I))

end GlobalTheory.LamPullComp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCompGroupPullbackIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundleIso_comp_group_pullback_iso : ∀ {S S₁ S₂ S₀ : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (B' : Over S₁) [GrpObj B'] (G' : Over S₂) [GrpObj G'] [IsCommMonObj G'] (T : Over S₀) [GrpObj T] [IsCommMonObj T] (f₁ : S₁ ⟶ S) (f₂ : S₂ ⟶ S₁) (β' : B'.left ⟶ G.left) (Φ : G'.left ⟶ B'.left) (φ : G'.left ⟶ G.left) (β₂ : (G2 B').left ⟶ (G2 G).left) (β₂' : (G2 B').left ⟶ (G2 T).left) (L : LB G.left) (L' : LB G'.left) (M : LB T.left) (gp' : IsGrpPullback B' G f₁ β') (gΦ : IsGrpPullback G' B' f₂ Φ), IsSquare β' β₂ → Φ ≫ β' = φ → L.IsLB → L'.IsLB → M.IsLB → ∀ (v : LB.Iso L' (L.pull φ)) (w₁ : LB.Iso ((abelian₂ G L).pull β₂) ((abelian₂ T M).pull β₂')), v.IsGen → w₁.IsGen → ∃ w : LB.Iso (abelian₂ G' L') ((abelian₂ T M).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂')), w.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 G').left) (z : Z) (J : (Z ⟶ T.left) → M.ι) (J₁ : (Z ⟶ G.left) → L.ι) (J' : (Z ⟶ G'.left) → L'.ι), Good M z J → Good L z J₁ → Good L' z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw v (p ≫ lamφ G' I) z (J₁ ((p ≫ lamφ G' I) ≫ φ)) (J' (p ≫ lamφ G' I)) ^ lamε I := by
  first | exact @GlobalTheory.LamPullComp.lamIso_comp_pull | exact GlobalTheory.LamPullComp.lamIso_comp_pull | (intros; apply GlobalTheory.LamPullComp.lamIso_comp_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegDataFromLowerBaseAfterMonomialExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullFrom

theorem exists_cart_of_pullDeg : ∀ {V V₁ V₂ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [CommRing V₂] [IsDomain V₂] (D : DegPre V) (f₁ : V →+* V₁) (f₂ : V₁ →+* V₂) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.P.A.left) (D' : DegPre V₂) (hD : IsPullDeg (f₂.comp f₁) D D'), IsGrpPullback B' D.P.A (spMap f₁) β' → ∃ Φ : D'.P.A.left ⟶ B'.left, IsGrpPullback D'.P.A B' (spMap f₂) Φ ∧ Φ ≫ β' = hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (f₂.comp f₁)) ∧ ∀ (a : D'.X) (y : 𝟙_ (Over (Sp V₁)) ⟶ B'), y.left ≫ β' = spMap f₁ ≫ (D.c (hD.xe a)).left → (D'.c a).left ≫ Φ = spMap f₂ ≫ y.left := by
  intro V V₁ V₂ _ _ _ _ _ _ D f₁ f₂ B' _ β' D' hD gp'
  have gp := pull_grp hD
  have hsp : spMap f₂ ≫ spMap f₁ = spMap (f₂.comp f₁) := GlobalTheory.HalfBC.spMap_comp_spMap' f₁ f₂
  have w₀ : (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (f₂.comp f₁))) ≫ D.P.A.hom =
      (D'.P.A.hom ≫ spMap f₂) ≫ spMap f₁ := by
    rw [gp.1.w, Category.assoc, hsp]
  refine ⟨gp'.1.lift _ _ w₀, ?_, gp'.1.lift_fst _ _ w₀, fun a y hy => ?_⟩
  · exact IsGrpPullback.cancel gp' (gp.congr hsp.symm (gp'.1.lift_fst _ _ w₀).symm) (gp'.1.lift_snd _ _ w₀)
  · apply gp'.1.hom_ext
    · rw [Category.assoc, gp'.1.lift_fst, Category.assoc, hy, ← Category.assoc (spMap f₂), hsp]
      exact hD.c_pr a
    · rw [Category.assoc, gp'.1.lift_snd, Category.assoc, Over.w y, ← Category.assoc, Over.w (D'.c a)]
      rfl

theorem degFrom_of_periodRel : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)), IsCN V₂ → Function.Injective f₂ → f₂.Finite → IsLocalHom f₂ → (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegData V₂ (maximalIdeal V₂)) (hD : IsPullDeg (f₂.comp f₁) D.toPre D'.toPre), DegFrom L.T (f₂.comp κ₁) s ε n D'.toPre (hD.xe.trans (e₀.symm.trans e.symm)) := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' hV hVd hV₁ hV₁d hf₁i hf₁f hf₁l hκ₁l gp' gp'' sq' sq'' x hx w₁ q hw₁ hPR V₂ _ _ _ f₂ fK I _ s ε hV₂ hf₂i hf₂f hf₂l hfK hq D' hD
  obtain ⟨Φ, gΦ, hΦ, hc₀⟩ := exists_cart_of_pullDeg D.toPre f₁ f₂ B' β' D'.toPre hD gp'
  have hc : ∀ a, (D'.toPre.c a).left ≫ Φ = spMap f₂ ≫ (x (hD.xe.trans (e₀.symm.trans e.symm) a)).left := fun a =>
    hc₀ a _ (by
      have := (hx (hD.xe.trans (e₀.symm.trans e.symm) a)).1
      simpa using this)
  have hΛD : (abelian₂ D.toPre.P.A D.toPre.P.L).IsLB := DVR.linComb_isLB _ D.toPre.P.isLB _ _
  obtain ⟨w, hw, hval⟩ := GlobalTheory.T.mumfordBundleIso_comp_group_pullback_iso D.toPre.P.A B' D'.toPre.P.A L.T.B (spMap f₁) (spMap f₂) β' Φ (GlobalTheory.PsiEvenPull.proj hD) β₂ β₂'
    D.toPre.P.L D'.toPre.P.L L.T.M.L gp' gΦ sq' hΦ D.toPre.P.isLB D'.toPre.P.isLB L.T.M.isLB hD.w w₁ hD.w_gen hw₁
  have hsp : spMap f₂ ≫ spMap κ₁ = spMap (f₂.comp κ₁) := GlobalTheory.HalfBC.spMap_comp_spMap' κ₁ f₂
  refine ⟨Wit.ofDeg D'.toPre D'.tau_bimult, AddEquiv.refl _, Wit.refines_ofDeg _ _, Φ ≫ β'', GlobalTheory.HalfBC.sqOf gΦ ≫ β₂', w,
    (IsGrpPullback.comp gΦ gp'').congr hsp rfl, ⟨?_, ?_⟩, hw, fun a => ?_, fun a b => ?_⟩
  · have e₁ : GlobalTheory.HalfBC.sqOf gΦ ≫ (fst B' B').left = (fst D'.toPre.P.A D'.toPre.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_fst (pushPt gΦ.1.w (fst D'.toPre.P.A D'.toPre.P.A)) (pushPt gΦ.1.w (snd D'.toPre.P.A D'.toPre.P.A)))
    show (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ (fst L.T.B L.T.B).left = (fst D'.toPre.P.A D'.toPre.P.A).left ≫ Φ ≫ β''
    rw [Category.assoc, sq''.1, ← Category.assoc, e₁, Category.assoc]
  · have e₂ : GlobalTheory.HalfBC.sqOf gΦ ≫ (snd B' B').left = (snd D'.toPre.P.A D'.toPre.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_snd (pushPt gΦ.1.w (fst D'.toPre.P.A D'.toPre.P.A)) (pushPt gΦ.1.w (snd D'.toPre.P.A D'.toPre.P.A)))
    show (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ (snd L.T.B L.T.B).left = (snd D'.toPre.P.A D'.toPre.P.A).left ≫ Φ ≫ β''
    rw [Category.assoc, sq''.2, ← Category.assoc, e₂, Category.assoc]
  · refine (congrArg (· ≫ β'') (hc a)).trans ?_
    rw [Category.assoc, (hx _).2, ← Category.assoc, hsp]
    rfl
  · obtain ⟨k, hk, hk'⟩ := GlobalTheory.T.period_relation_pullback_monomial_constants n V D.toPre r e₀ L.T V₁ f₁ κ₁ e B' β₂ β₂' x w₁ q hf₁i hPR V₂ f₂ fK s ε hfK hq D'.toPre hD Φ gΦ hc w hval a b
    refine ⟨k, hk, fun z J J' hJ hJ' => ?_⟩
    refine ((Wit.exists_tau D'.toPre a b).choose_spec.2 _ _ z J' hJ').trans ?_
    exact hk' z J J' hJ hJ'

end GlobalTheory.PullFrom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegDataFromLowerBaseAfterMonomialExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degData_from_lowerBase_after_monomial_extension : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)), IsCN V₂ → Function.Injective f₂ → f₂.Finite → IsLocalHom f₂ → (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegData V₂ (maximalIdeal V₂)) (hD : IsPullDeg (f₂.comp f₁) D.toPre D'.toPre), DegFrom L.T (f₂.comp κ₁) s ε n D'.toPre (hD.xe.trans (e₀.symm.trans e.symm)) := by
  first | exact @GlobalTheory.PullFrom.degFrom_of_periodRel | exact GlobalTheory.PullFrom.degFrom_of_periodRel | (intros; apply GlobalTheory.PullFrom.degFrom_of_periodRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsSymmetric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsSymmetric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart.SwapIso

open GlobalTheory.LamBiext GlobalTheory.LamRigid

variable {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B]
  [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B']


variable (B') in
abbrev sw2 : Fin 2 → ((G2 B').left ⟶ (G2 B').left) :=
  ![(lift (fst B' B') (snd B' B')).left, (lift (snd B' B') (fst B' B')).left]

theorem lift_comp_squareFactorIdentity_eq_lift {T : Over S'} (a b : T ⟶ B') : (lift a b).left ≫ sw2 B' 0 = (lift a b).left := by
  show (lift a b).left ≫ (lift (fst B' B') (snd B' B')).left = _
  rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]

theorem lift_comp_squareFactorSwap_eq_lift_swap {T : Over S'} (a b : T ⟶ B') : (lift a b).left ≫ sw2 B' 1 = (lift b a).left := by
  show (lift a b).left ≫ (lift (snd B' B') (fst B' B')).left = _
  rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]

theorem formEq_sw {f : S' ⟶ S} {β : B'.left ⟶ B.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (hβ : IsGrpPullback B' B f β) (hsq : IsSquare β β₂) :
    FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => sw2 B' k ≫ β₂) (flatε lamε ![1, -1]) := by
  have hw₀ : β ≫ B.hom = B'.hom ≫ f := hβ.1.w
  have β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'),
      (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left := fun a b => square_over_hom_ext
    (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl)
    (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)
  intro U _ h
  rw [GlobalTheory.LamBiext.prod_flat, Fin.prod_univ_two, Fintype.prod_empty]
  show 1 = (∏ i, h (((lift (fst B' B') (snd B' B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ) *
    (∏ i, h (((lift (snd B' B') (fst B' B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (-1 : ℤ)
  rw [β₂_lift, β₂_lift, GlobalTheory.LamBiext.prod_lam, GlobalTheory.LamBiext.prod_lam, _root_.mul_comm (toBase hw₀ (snd B' B'))]
  apply Additive.ofMul.injective
  simp only [zpow_neg, zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem exists_gen_sw {f : S' ⟶ S} {β : B'.left ⟶ B.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (hβ : IsGrpPullback B' B f β) (hsq : IsSquare β β₂) {M : LB B.left} (hM : M.IsLB) :
    ∃ t : LB.Gen (LB.LinComb (abelian₂ B M) (fun k => sw2 B' k ≫ β₂) ![1, -1]), t.IsGen ∧
      ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z : Z) (J : (Z ⟶ B.left) → M.ι), Good M z J →
        val (L := abelian₂ B M) t r z (ind B J) = 1 := by
  obtain ⟨g, hg, hv⟩ := exists_gen hM (formEq_sw hβ hsq) (LB.oneGen M) (oneGen_isGen _)
  refine ⟨GlobalTheory.LamBiext.nest M (lamφ B) lamε (fun k => sw2 B' k ≫ β₂) ![1, -1] g, nest_isGen hg,
    fun r z J hJ => ?_⟩
  refine (val_nest hg r (good_ind hJ) hJ).trans ?_
  simp only [adj_ind hM hJ, one_zpow, Finset.prod_const_one, _root_.one_mul]
  exact (hv _ r z J hJ).trans (val_one r)

end GlobalTheory.TChart.SwapIso

namespace GlobalTheory.TChart.SwapIso

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.Mum.Two

variable {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B]
  [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B']

theorem isoVal_swap (hB' : IsAbelianScheme B') {M : LB B.left} {M₁ : LB B₁.left} (hM : M.IsLB) (hM₁ : M₁.IsLB)
    {f : S' ⟶ S} {f₁ : S' ⟶ S₁} {β : B'.left ⟶ B.left} {β₁ : B'.left ⟶ B₁.left}
    {β₂ : (G2 B').left ⟶ (G2 B).left} {β₂' : (G2 B').left ⟶ (G2 B₁).left}
    (hβ : IsGrpPullback B' B f β) (hβ₁ : IsGrpPullback B' B₁ f₁ β₁) (hsq : IsSquare β β₂) (hsq₁ : IsSquare β₁ β₂')
    (w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂')) (hw : w.IsGen) {T : Over S'} (x y : T ⟶ B')
    (z : T.left) (J : (T.left ⟶ B₁.left) → M₁.ι) (J' : (T.left ⟶ B.left) → M.ι) (hJ : Good M₁ z J)
    (hJ' : Good M z J') :
    isoVal w (lift x y).left z J J' = isoVal w (lift y x).left z J J' := by
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B₁ M₁).IsLB := DVR.linComb_isLB _ hM₁ _ _
  have hL' : ((abelian₂ B M).pull β₂).IsLB := DVR.linComb_isLB _ (DVR.linComb_isLB _ hM _ _) _ _
  obtain ⟨t, ht, hvt⟩ := exists_gen_sw hβ₁ hsq₁ hM₁
  obtain ⟨g, hg, hvg⟩ := exists_gen_sw hβ hsq hM
  let c := chartPullLinComb (abelian₂ B M) β₂ (sw2 B') (fun k => sw2 B' k ≫ β₂) ![1, -1] (𝟙 _)
    (fun k => (Category.id_comp _).symm)
  have ha : (cGen c g).IsGen := cGen_isGen c hg
  have good_P : ∀ {Z : Scheme.{0}} {z₀ : Z} {J₀ : (Z ⟶ B.left) → M.ι}, Good M z₀ J₀ →
      Good ((abelian₂ B M).pull β₂) z₀ (fun q _ => ind B J₀ (q ≫ β₂)) :=
    fun hJ₀ q => mem_pull.2 (good_ind hJ₀ (q ≫ β₂))
  have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z₀ : Z) (J₀ : (Z ⟶ B.left) → M.ι), Good M z₀ J₀ →
      val (cGen c g) r z₀ (fun q _ => ind B J₀ (q ≫ β₂)) = 1 := by
    intro Z r z₀ J₀ hJ₀
    rw [← hvg r z₀ J₀ hJ₀, val_of g r z₀ (ind B J₀) (fun k => ind B J₀ ((r ≫ sw2 B' k) ≫ β₂))
      (fun k => by rw [Category.assoc])]
    exact gm_res r z₀ _ ((good_P hJ₀).mem _ r) _
  have gw_iso : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (φ : (G2 B').left ⟶ (G2 B').left) (z₀ : Z)
      (J₀ : (Z ⟶ B₁.left) → M₁.ι) (J₀' : (Z ⟶ B.left) → M.ι),
      gw w (r ≫ φ) z₀ (ind B₁ J₀ (r ≫ φ ≫ β₂')) (fun _ => ind B J₀' ((r ≫ φ) ≫ β₂)) =
        isoVal w (r ≫ φ) z₀ J₀ J₀' := by
    intro Z r φ z₀ J₀ J₀'
    have e₁ : ind B₁ J₀ (r ≫ φ ≫ β₂') = fun I => J₀ ((r ≫ φ) ≫ β₂' ≫ (psum B₁ (x2 B₁) I.down).left) :=
      funext fun I => congrArg J₀ (by simp only [Category.assoc])
    have e₂ : ind B J₀' ((r ≫ φ) ≫ β₂) = fun I => J₀' ((r ≫ φ) ≫ β₂ ≫ (psum B (x2 B) I.down).left) :=
      funext fun I => congrArg J₀' (by simp only [Category.assoc])
    rw [e₁, e₂]; rfl
  have Fp : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z₀ : Z) (J₀ : (Z ⟶ B₁.left) → M₁.ι)
      (J₀' : (Z ⟶ B.left) → M.ι),
      pw w (sw2 B') ![1, -1] r z₀ (fun k => ind B₁ J₀ (r ≫ sw2 B' k ≫ β₂'))
        (fun k => (fun (q : Z ⟶ (G2 B').left) (_ : PUnit) => ind B J₀' (q ≫ β₂)) (r ≫ sw2 B' k)) =
        isoVal w (r ≫ sw2 B' 0) z₀ J₀ J₀' * (isoVal w (r ≫ sw2 B' 1) z₀ J₀ J₀')⁻¹ := by
    intro Z r z₀ J₀ J₀'
    unfold pw
    rw [Fin.prod_univ_two]
    rw [gw_iso r (sw2 B' 0) z₀ J₀ J₀', gw_iso r (sw2 B' 1) z₀ J₀ J₀']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zpow_one, zpow_neg]
  have he2 : (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (snd B' B').left ≫ B'.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S') ⟶ B') 1)
  have E := rigid_pw w hw hL hL' (sw2 B') ![1, -1] ha ht _ _ he2
    (surj_comp (surj_snd hG hB' _) (hG _ _ hB').2) (fun y₀ => by
      obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM₁ y₀
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM y₀
      refine ⟨ind B₁ J₁, fun q _ => ind B J₁' (q ≫ β₂), good_ind hJ₁, good_P hJ₁', ?_⟩
      rw [hvt _ y₀ J₁ hJ₁, Fp, Fa _ y₀ J₁' hJ₁', lift_comp_squareFactorIdentity_eq_lift, lift_comp_squareFactorSwap_eq_lift_swap, mul_inv_cancel, _root_.mul_one])
    T.left (lift x y).left z (ind B₁ J) (fun q _ => ind B J' (q ≫ β₂)) (good_ind hJ) (good_P hJ')
  rw [hvt _ z J hJ, Fp, Fa _ z J' hJ', lift_comp_squareFactorIdentity_eq_lift, lift_comp_squareFactorSwap_eq_lift_swap, _root_.mul_one] at E
  exact mul_inv_eq_one.1 E.symm

end GlobalTheory.TChart.SwapIso

namespace GlobalTheory.TChart

theorem periodConst_symm : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → IsNormIso w₁ → ∀ a b, q a b = q b a := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' hV hVd hV₁ hV₁d hf₁ hfin hloc hκ hpb hpb' hsq hsq'
    x hx w₁ q hgen hper hnorm a b
  have hAb : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback D.toPre.P.isAb hpb
  obtain ⟨κK, hκK⟩ : ∃ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁ := by
    have hi : Function.Injective ((algebraMap V₁ (FractionRing V₁)).comp f₁) :=
      (IsFractionRing.injective V₁ (FractionRing V₁)).comp hf₁
    obtain ⟨g, eg⟩ : ∃ g : FractionRing V →+* FractionRing V₁,
        g.comp (algebraMap V (FractionRing V)) = (algebraMap V₁ (FractionRing V₁)).comp f₁ :=
      ⟨IsLocalization.lift (M := nonZeroDivisors V) (g := (algebraMap V₁ (FractionRing V₁)).comp f₁) fun y =>
        IsUnit.mk0 _ ((map_ne_zero_iff _ hi).2 (nonZeroDivisors.coe_ne_zero y)), IsLocalization.lift_comp _⟩
    refine ⟨spMap g, ?_⟩
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, eg]
  let z : (TK V₁).left := (⊥ : PrimeSpectrum (FractionRing V₁))
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt L.T.M.isLB z
  obtain ⟨J', hJ'⟩ := GlobalTheory.UU.exists_good_pt D.toPre.P.isLB z
  have h₁ := hper κK hκK a b z J J' hJ hJ'
  have h₂ := hper κK hκK b a z J J' hJ hJ'
  rw [GlobalTheory.Mum.RosatiSymmetry.val_tau_symm D.toPre hJ' κK,
    val_corr hJ (corr_of_val L.T.M.isLB (L.T.τ₀_symm ((n : ℤ) • b) ((n : ℤ) • a))),
    GlobalTheory.TChart.SwapIso.isoVal_swap hAb D.toPre.P.isLB L.T.M.isLB hpb hpb' hsq hsq' w₁ hgen
      (toUnit (TK V₁) ≫ x b) (toUnit (TK V₁) ≫ x a) z J J' hJ hJ'] at h₂
  have hq := mul_right_cancel (h₁.symm.trans h₂)
  have hs : Subsingleton (TK V₁).left := (inferInstance : Subsingleton (PrimeSpectrum (FractionRing V₁)))
  have eu : unitOn (q a b) = unitOn (q b a) := unit_ext fun y _ => by rw [Subsingleton.elim y z]; exact hq
  exact Units.map_injective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V₁))).inv).1 eu

end GlobalTheory.TChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsSymmetricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledBack_period_constants_symmetric : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → IsNormIso w₁ → ∀ a b, q a b = q b a := by
  first | exact @GlobalTheory.TChart.periodConst_symm | exact GlobalTheory.TChart.periodConst_symm | (intros; apply GlobalTheory.TChart.periodConst_symm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedIsoPulledBackPeriodRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedIsoPulledBackPeriodRelation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart.Ratio

section General

variable {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B₁]
  [IsCommMonObj B₁] [GrpObj B']

def tr (M : LB B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z)
    (J J₀ : (Z ⟶ B.left) → M.ι) : (Z.presheaf.stalk z)ˣ :=
  ∏ I : ULift.{0} (Finset (Fin 2)), (fun q => gm q z (M.U (J q) ⊓ M.U (J₀ q)) (M.g (J q) (J₀ q)))
    ((p ≫ β₂) ≫ (psum B (x2 B) I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card))

omit [GrpObj B'] in
theorem mem_chart {M : LB B.left} (β₂ : (G2 B').left ⟶ (G2 B).left) {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) {z : Z}
    {J : (Z ⟶ B.left) → M.ι} (hJ : Good M z J) :
    β₂ (p z) ∈ (abelian₂ B M).U (fun I => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) :=
  Set.mem_iInter.2 fun I => hJ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)

omit [GrpObj B'] in
theorem gm_lam {M : LB B.left} (β₂ : (G2 B').left ⟶ (G2 B).left) {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) {z : Z}
    {J J₀ : (Z ⟶ B.left) → M.ι} (hJ : Good M z J) (hJ₀ : Good M z J₀) :
    gm (p ≫ β₂) z _ ((abelian₂ B M).g (fun I => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left))
      (fun I => J₀ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left))) = tr M β₂ p z J J₀ :=
  (gm_linComb M _ _ (p ≫ β₂) z _ _ (mem_chart β₂ p hJ) (mem_chart β₂ p hJ₀)).trans
    (Finset.prod_congr rfl fun I _ => congrArg (· ^ _) (congrArg (fun q => gm ((p ≫ β₂) ≫ (psum B (x2 B) I.down).left) z
      (M.U (J q) ⊓ M.U (J₀ q)) (M.g (J q) (J₀ q))) (Category.assoc _ _ _).symm))

theorem isoVal_trans {M : LB B.left} {M₁ : LB B₁.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    {β₂' : (G2 B').left ⟶ (G2 B₁).left} {w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂')} (hw : w.IsGen)
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) {z : Z} {J J₀ : (Z ⟶ B₁.left) → M₁.ι} {J' J₀' : (Z ⟶ B.left) → M.ι}
    (hJ : Good M₁ z J) (hJ₀ : Good M₁ z J₀) (hJ' : Good M z J') (hJ₀' : Good M z J₀') :
    isoVal w p z J J' = tr M₁ β₂' p z J J₀ * (tr M β₂ p z J' J₀')⁻¹ * isoVal w p z J₀ J₀' := by
  have m := mem_chart β₂ p hJ'
  have m₀ := mem_chart β₂ p hJ₀'
  have h := (isGen_iff w).1 hw Z p z _ _ (fun _ I => J' (p ≫ β₂ ≫ (psum B (x2 B) I.down).left))
    (fun _ I => J₀' (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) (mem_chart β₂' p hJ) (mem_chart β₂' p hJ₀)
    (mem_pull.2 m) (mem_pull.2 m₀)
  refine h.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (gm_lam β₂' p hJ hJ₀) (congrArg (·⁻¹) ?_)) rfl)
  refine (gm_linComb (abelian₂ B M) (K := PUnit) (fun _ => β₂) (fun _ => 1) p z _ _ (mem_pull.2 m) (mem_pull.2 m₀)).trans ?_
  rw [Fintype.prod_unique, zpow_one]
  exact gm_lam β₂ p hJ' hJ₀'

omit [GrpObj B] [IsCommMonObj B] [GrpObj B'] in
theorem lift_sq {β : B'.left ⟶ B.left} {β₂ : (G2 B').left ⟶ (G2 B).left} (hs : IsSquare β β₂) {T : Over S'}
    (x y : T ⟶ B') {g : T.left ⟶ S} (x₀ y₀ : Over.mk g ⟶ B) (hx : x₀.left = x.left ≫ β) (hy : y₀.left = y.left ≫ β) :
    (lift x y).left ≫ β₂ = (lift x₀ y₀).left := by
  have e₁ : (lift x y).left ≫ (fst B' B').left = x.left := congrArg (·.left) (lift_fst x y)
  have e₂ : (lift x y).left ≫ (snd B' B').left = y.left := congrArg (·.left) (lift_snd x y)
  have e₃ : (lift x₀ y₀).left ≫ (fst B B).left = x₀.left := congrArg (·.left) (lift_fst x₀ y₀)
  have e₄ : (lift x₀ y₀).left ≫ (snd B B).left = y₀.left := congrArg (·.left) (lift_snd x₀ y₀)
  refine pullback.hom_ext (f := B.hom) (g := B.hom) ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hs.1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ β) e₁).trans (hx.symm.trans e₃.symm))))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hs.2).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ β) e₂).trans (hy.symm.trans e₄.symm))))


omit [GrpObj B'] in
theorem val_trans {M : LB B.left} {β : B'.left ⟶ B.left} {β₂ : (G2 B').left ⟶ (G2 B).left} (hs : IsSquare β β₂)
    {T : Over S'} (x y : T ⟶ B') {T₀ : Over S} {x₁ y₁ : T₀ ⟶ B} {t : LB.Gen (LB.LinComb M (lamPts x₁ y₁) negε)}
    (ht : t.IsGen) (r : T.left ⟶ T₀.left) (hx : x.left ≫ β = r ≫ x₁.left) (hy : y.left ≫ β = r ≫ y₁.left)
    {z : T.left} {J J₀ : (T.left ⟶ B.left) → M.ι} (hJ : Good M z J) (hJ₀ : Good M z J₀) :
    val t r z J = (tr M β₂ (lift x y).left z J J₀)⁻¹ * val t r z J₀ := by
  let ρ : Over.mk (r ≫ T₀.hom) ⟶ T₀ := Over.homMk r rfl
  refine (gen_trans ht r z (hJ.mem _ _) (hJ₀.mem _ _)).trans (congrArg (· * _) ?_)
  unfold tr
  rw [lift_sq hs x y (ρ ≫ x₁) (ρ ≫ y₁) hx.symm hy.symm]
  refine Eq.trans ?_ (congrArg (·⁻¹) (GlobalTheory.PrimCocycle.prod_lam (ρ ≫ x₁) (ρ ≫ y₁)
    (fun q => gm q z (M.U (J q) ⊓ M.U (J₀ q)) (M.g (J q) (J₀ q))))).symm
  rw [← MonObj.comp_mul, ← MonObj.comp_one ρ]
  have key : ∀ H : (T.left ⟶ B.left) → (T.left.presheaf.stalk z)ˣ, ∏ k, H (r ≫ lamPts x₁ y₁ k) ^ negε k =
      (H (ρ ≫ (x₁ * y₁)).left * (H (ρ ≫ x₁).left)⁻¹ * (H (ρ ≫ y₁).left)⁻¹ * H (ρ ≫ 1).left)⁻¹ := fun H => by
    rw [Fin.prod_univ_four]
    show H (ρ ≫ (x₁ * y₁)).left ^ (-1 : ℤ) * H (ρ ≫ x₁).left ^ (1 : ℤ) * H (ρ ≫ y₁).left ^ (1 : ℤ) *
      H (ρ ≫ 1).left ^ (-1 : ℤ) = _
    simp only [zpow_neg, zpow_one, mul_inv, inv_inv]
  exact key (fun q => gm q z (M.U (J q) ⊓ M.U (J₀ q)) (M.g (J q) (J₀ q)))

theorem one_push {f : S' ⟶ S} {β : B'.left ⟶ B.left} (h : IsGrpPullback B' B f β) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ B).left = (1 : T ⟶ B').left ≫ β := by
  let x₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk ((1 : T ⟶ B').left ≫ β) (by
    have := h.1.w
    have e := Over.w (1 : T ⟶ B')
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) this).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) e))))
  have e := h.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at e
  have : x₀ = 1 := mul_eq_left.1 (Over.OverMorphism.ext e)
  rw [← this]; rfl

theorem psum_one {T T' : Over S} (ρ : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ B)) (hx : ∀ k, ρ ≫ x k = 1) (I : Finset (Fin n)) :
    ρ ≫ psum B x I = 1 := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact MonObj.comp_one ρ
  | cons k l ih =>
    refine (MonObj.comp_mul ρ (x k) _).trans ?_
    exact (congrArg₂ (· * ·) (hx k) ih).trans (_root_.mul_one _)

theorem origin_pts {f : S' ⟶ S} {β : B'.left ⟶ B.left} (h : IsGrpPullback B' B f β)
    {β₂ : (G2 B').left ⟶ (G2 B).left} (hs : IsSquare β β₂) (T : Over S') (I : Finset (Fin 2)) :
    (lift (1 : T ⟶ B') (1 : T ⟶ B')).left ≫ β₂ ≫ (psum B (x2 B) I).left = (1 : T ⟶ B').left ≫ β := by
  rw [← Category.assoc, lift_sq hs 1 1 (1 : Over.mk (T.hom ≫ f) ⟶ B) 1 (one_push h T) (one_push h T), ← one_push h T]
  refine congrArg (·.left) (psum_one (lift (1 : Over.mk (T.hom ≫ f) ⟶ B) 1) (x2 B) (fun k => ?_) I)
  fin_cases k
  · exact lift_fst _ _
  · exact lift_snd _ _

theorem tr_origin {M : LB B.left} {f : S' ⟶ S} {β : B'.left ⟶ B.left} (h : IsGrpPullback B' B f β)
    {β₂ : (G2 B').left ⟶ (G2 B).left} (hs : IsSquare β β₂) (T : Over S') (z : T.left) (J J₀ : (T.left ⟶ B.left) → M.ι) :
    tr M β₂ (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J₀ = 1 := by
  unfold tr
  rw [lift_sq hs 1 1 (1 : Over.mk (T.hom ≫ f) ⟶ B) 1 (one_push h T) (one_push h T)]
  refine (GlobalTheory.PrimCocycle.prod_lam (1 : Over.mk (T.hom ≫ f) ⟶ B) 1
    (fun q => gm q z (M.U (J q) ⊓ M.U (J₀ q)) (M.g (J q) (J₀ q)))).trans ?_
  rw [_root_.mul_one, mul_inv_cancel, _root_.one_mul, inv_mul_cancel]

end General

def scale {X : Scheme.{0}} {N : LB X} (t : N.Gen) (u : Γ(X, ⊤)ˣ) : N.Gen := ⟨fun i => t.s i * res le_top u⟩

theorem scale_isGen {X : Scheme.{0}} {N : LB X} {t : N.Gen} (ht : t.IsGen) (u : Γ(X, ⊤)ˣ) : (scale t u).IsGen := by
  intro i j
  refine unit_ext fun x hx => ?_
  have := congrArg (gm (𝟙 X) x (N.U i ⊓ N.U j)) (ht i j)
  rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx] at this
  rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx]
  show gm _ _ _ (_ * _) = _ * gm _ _ _ (_ * _)
  rw [map_mul, map_mul, gm_res _ x _ hx.1, gm_res _ x _ hx.2, this, _root_.mul_assoc]

theorem exists_norm {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {S S₁ : Scheme.{0}} {B : Over S} {B₁ : Over S₁}
    {B' : Over (Sp R)} [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B'] {M : LB B.left}
    {M₁ : LB B₁.left} (hM : M.IsLB) (hM₁ : M₁.IsLB) {f : Sp R ⟶ S} {f₁ : Sp R ⟶ S₁} {β : B'.left ⟶ B.left}
    {β₁ : B'.left ⟶ B₁.left} (h : IsGrpPullback B' B f β) (h₁ : IsGrpPullback B' B₁ f₁ β₁)
    {β₂ : (G2 B').left ⟶ (G2 B).left} {β₂' : (G2 B').left ⟶ (G2 B₁).left} (hs : IsSquare β β₂) (hs₁ : IsSquare β₁ β₂')
    (H : LBIso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂')) :
    ∃ w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂'), w.IsGen ∧ IsNormIso w := by
  obtain ⟨w, hw⟩ := H
  let T : Over (Sp R) := Over.mk (𝟙 (Sp R))
  let ρ : TK R ⟶ T := Over.homMk (jK R) (Category.comp_id _)
  let e : Sp R ⟶ (G2 B').left := (lift (1 : T ⟶ B') (1 : T ⟶ B')).left
  have he : jK R ≫ e = (lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')).left := by
    have : ρ ≫ lift (1 : T ⟶ B') (1 : T ⟶ B') = lift (1 : TK R ⟶ B') (1 : TK R ⟶ B') := by
      rw [comp_lift, MonObj.comp_one]
    exact congrArg (·.left) this
  let m : Sp R := closedPoint R
  obtain ⟨i, hi⟩ := exists_chart hM (((1 : T ⟶ B').left ≫ β) m)
  obtain ⟨i₁, hi₁⟩ := exists_chart hM₁ (((1 : T ⟶ B').left ≫ β₁) m)
  let P : (LB.div ((abelian₂ B₁ M₁).pull β₂') ((abelian₂ B M).pull β₂)).ι := (fun _ _ => i₁, fun _ _ => i)
  have hm : e m ∈ (LB.div ((abelian₂ B₁ M₁).pull β₂') ((abelian₂ B M).pull β₂)).U P :=
    ⟨mem_pull.2 (Set.mem_iInter.2 fun I => by
        have := congrArg (fun q => q m) (origin_pts h₁ hs₁ T I.down)
        exact (congrArg (· ∈ M₁.U i₁) this).mpr hi₁),
      mem_pull.2 (Set.mem_iInter.2 fun I => by
        have := congrArg (fun q => q m) (origin_pts h hs T I.down)
        exact (congrArg (· ∈ M.U i) this).mpr hi)⟩
  have htop : (⊤ : (Sp R).Opens) ≤ e ⁻¹ᵁ (LB.div ((abelian₂ B₁ M₁).pull β₂') ((abelian₂ B M).pull β₂)).U P :=
    ((IsLocalRing.closedPoint_mem_iff _).1 hm).ge
  let u : Γ(Sp R, ⊤)ˣ := res htop (pullU e _ (w.s P))
  refine ⟨scale w (pullU (G2 B').hom ⊤ u)⁻¹, scale_isGen hw _, fun z J J' hJ hJ' => ?_⟩
  have hz : (lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')).left z ∈
      (LB.div ((abelian₂ B₁ M₁).pull β₂') ((abelian₂ B M).pull β₂)).U P := by
    rw [← he]; exact htop (Set.mem_univ (jK R z))
  obtain ⟨J₀, hJ₀, e₀⟩ := exists_good M₁ hM₁ z (K := PUnit) (fun _ => (1 : TK R ⟶ B').left ≫ β₁) (fun _ => i₁)
    (fun _ _ _ => rfl) (fun _ => by
      have := congrArg (fun q => q z) (origin_pts h₁ hs₁ (TK R) ∅)
      exact (congrArg (· ∈ M₁.U i₁) this).mp (Set.mem_iInter.1 (mem_pull.1 hz.1) ⟨∅⟩))
  obtain ⟨J₀', hJ₀', e₀'⟩ := exists_good M hM z (K := PUnit) (fun _ => (1 : TK R ⟶ B').left ≫ β) (fun _ => i)
    (fun _ _ _ => rfl) (fun _ => by
      have := congrArg (fun q => q z) (origin_pts h hs (TK R) ∅)
      exact (congrArg (· ∈ M.U i) this).mp (Set.mem_iInter.1 (mem_pull.1 hz.2) ⟨∅⟩))
  rw [isoVal_trans (scale_isGen hw _) _ hJ hJ₀ hJ' hJ₀', tr_origin h hs, tr_origin h₁ hs₁, inv_one, _root_.mul_one,
    _root_.one_mul]
  have hP : ((fun _ I => J₀ ((lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')).left ≫ β₂' ≫ (psum B₁ (x2 B₁) I.down).left),
      fun _ I => J₀' ((lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')).left ≫ β₂ ≫ (psum B (x2 B) I.down).left)) :
        (LB.div ((abelian₂ B₁ M₁).pull β₂') ((abelian₂ B M).pull β₂)).ι) = P :=
    Prod.ext (funext fun _ => funext fun I => (congrArg J₀ (origin_pts h₁ hs₁ (TK R) I.down)).trans (e₀ PUnit.unit))
      (funext fun _ => funext fun I => (congrArg J₀' (origin_pts h hs (TK R) I.down)).trans (e₀' PUnit.unit))
  refine (congrArg (fun Q => gm (lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')).left z _
    ((scale w (pullU (G2 B').hom ⊤ u)⁻¹).s Q)) hP).trans ?_
  refine (map_mul _ _ _).trans (mul_eq_one_iff_eq_inv.2 ?_)
  refine Eq.symm ((congrArg (·⁻¹) ((gm_res _ z _ hz _).trans (map_inv _ _))).trans ((inv_inv _).trans ?_))
  refine (gm_pull _ (G2 B').hom z ⊤ trivial u).trans ?_
  refine (congrArg (fun q => gm q z ⊤ u) (Over.w (lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')))).trans ?_
  refine (gm_res (jK R) z htop trivial _).trans ((gm_pull (jK R) e z _ (htop (Set.mem_univ _)) _).trans ?_)
  exact congrArg (fun q => gm q z _ (w.s P)) he

theorem exists_const {K : Type} [Field K] (z : Sp K) (s : ((Sp K).presheaf.stalk z)ˣ) :
    ∃ k : Kˣ, gm (𝟙 (Sp K)) z ⊤ (unitOn k) = s := by
  obtain ⟨U, hU, a, ha⟩ := (Sp K).presheaf.germ_exist s.val
  have htop : (⊤ : (Sp K).Opens) ≤ U := fun y _ => by
    have : y = z := Subsingleton.elim (α := PrimeSpectrum K) y z
    exact this ▸ hU
  let φ : K →+* (Sp K).presheaf.stalk z :=
    ((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have e : φ ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (((Sp K).presheaf.map (homOfLE htop).op).hom a)) = s.val := by
    show ((Sp K).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom _)) = _
    rw [Iso.hom_inv_id_apply]
    exact (TopCat.Presheaf.germ_res_apply (Sp K).presheaf (homOfLE htop) z trivial _).trans ha
  obtain ⟨k, hk⟩ : ∃ k : K, φ k = s.val := ⟨_, e⟩
  refine ⟨Units.mk0 k (fun h0 => s.ne_zero (by rw [← hk, h0, map_zero])), Units.ext ?_⟩
  exact (gm_val _ z ⊤ trivial _).trans hk

theorem exists_normIso_periodRel : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → LBIso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∃ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen ∧ IsNormIso w₁ ∧ PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' _ _ _ _ _ _ _ _ h h₁ hs hs₁ H x hx
  obtain ⟨w, hw, hn⟩ := exists_norm D.toPre.P.isLB L.T.M.isLB h h₁ hs hs₁ H
  have key : ∀ a b, ∃ k : (FractionRing V₁)ˣ, ∀ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁ →
      ∀ z J J', Good L.T.M.L z J → Good D.toPre.P.L z J' →
      val (D.toPre.tau (e₀ (e a)) (e₀ (e b))) κK z J' = gm (𝟙 (TK V₁).left) z ⊤ (unitOn k) *
        (isoVal w (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x b)).left z J J' *
          val (L.T.τ₀ ((n : ℤ) • a) ((n : ℤ) • b)) ((TK V₁).hom ≫ spMap κ₁) z J) := by
    intro a b
    by_cases hκ : ∃ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁
    swap
    · exact ⟨1, fun κK h => (hκ ⟨κK, h⟩).elim⟩
    obtain ⟨κ, hκ⟩ := hκ
    let z : (TK V₁).left := (⊥ : PrimeSpectrum (FractionRing V₁))
    choose J₀ hJ₀ using fun χ : (TK V₁).left ⟶ L.T.B.left => exists_chart L.T.M.isLB (χ z)
    choose J₀' hJ₀' using fun χ : (TK V₁).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ z)
    obtain ⟨t, ht, et⟩ := Wit.exists_tau D.toPre (e₀ (e a)) (e₀ (e b))
    obtain ⟨k, hk⟩ := exists_const (K := FractionRing V₁) z (val t κ z J₀' *
      (isoVal w (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x b)).left z J₀ J₀' *
          val (L.T.τ₀ ((n : ℤ) • a) ((n : ℤ) • b)) ((TK V₁).hom ≫ spMap κ₁) z J₀)⁻¹)
    refine ⟨k, fun κK hK z' J J' hJ hJ' => ?_⟩
    obtain rfl : κK = κ := by
      have : Mono (jK V) := Wit.mono_jK
      exact (cancel_mono (jK V)).1 (hK.trans hκ.symm)
    obtain rfl : z = z' := Subsingleton.elim (α := PrimeSpectrum (FractionRing V₁)) _ _
    have p₁ : ∀ a, (toUnit (TK V₁) ≫ x a).left ≫ β' = κK ≫ (toUnit (TK V) ≫ D.toPre.c (e₀ (e a))).left := fun a =>
      (Category.assoc (jK V₁) (x a).left β').trans ((congrArg (jK V₁ ≫ ·) (hx a).1).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hK.symm).trans (Category.assoc _ _ _))))
    have p₂ : ∀ a, (toUnit (TK V₁) ≫ x a).left ≫ β'' = ((TK V₁).hom ≫ spMap κ₁) ≫ (L.T.c₀ ((n : ℤ) • a)).left :=
      fun a => (Category.assoc (jK V₁) (x a).left β'').trans ((congrArg (jK V₁ ≫ ·) (hx a).2).trans
        (Category.assoc _ _ _).symm)
    have e₁ := val_trans hs _ _ ht κK (p₁ a) (p₁ b) hJ' hJ₀'
    have e₂ := val_trans hs₁ _ _ (L.T.τ₀_gen ((n : ℤ) • a) ((n : ℤ) • b)) ((TK V₁).hom ≫ spMap κ₁) (p₂ a) (p₂ b) hJ hJ₀
    have e₃ := isoVal_trans hw (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x b)).left hJ hJ₀ hJ' hJ₀'
    have alg : ∀ {U : Type} [CommGroup U] (A C p q s : U), A⁻¹ * p = p * (q * s)⁻¹ * (C * A⁻¹ * q * (C⁻¹ * s)) := by
      intro U _ A C p q s
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    have hk' : gm (𝟙 (TK V₁).left) z ⊤ (unitOn k) = _ := hk
    exact (et _ κK z J' hJ').symm.trans (e₁.trans ((alg _ _ _ _ _).trans
      (congrArg₂ (fun u v : ((TK V₁).left.presheaf.stalk z)ˣ => u * v) hk' (congrArg₂ (· * ·) e₃ e₂)).symm))
  choose q hq using key
  exact ⟨w, q, hw, hn, fun κK hK a b z J J' hJ hJ' => hq a b κK hK z J J' hJ hJ'⟩

end GlobalTheory.TChart.Ratio
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedIsoPulledBackPeriodRelationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalised_iso_pulledBack_period_relation : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → LBIso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∃ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen ∧ IsNormIso w₁ ∧ PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q := by
  first | exact @GlobalTheory.TChart.Ratio.exists_normIso_periodRel | exact GlobalTheory.TChart.Ratio.exists_normIso_periodRel | (intros; apply GlobalTheory.TChart.Ratio.exists_normIso_periodRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPulledBackPeriodsBasePeriodsConstForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem exists_periods_of_pull : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → LBIso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') → (∀ a : Fin L.T.r → ℤ, ∃ x : Sp V₁ ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ x ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∃ q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ, (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V₁, w ≠ 0 ∧ (q a a : FractionRing V₁) = algebraMap V₁ _ w) ∧ ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)), IsCN V₂ → Function.Injective f₂ → f₂.Finite → IsLocalHom f₂ → (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegData V₂ (maximalIdeal V₂)) (hD : IsPullDeg (f₂.comp f₁) D.toPre D'.toPre), DegFrom L.T (f₂.comp κ₁) s ε n D'.toPre (hD.xe.trans (e₀.symm.trans e.symm)) := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ lb pts
  choose x hx using pts
  let y : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B') := fun a => Over.homMk (x a) (hx a).1
  have hy : ∀ a, (y a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧
      (y a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left := fun a => ⟨(hx a).2.1, (hx a).2.2⟩
  obtain ⟨w₁, q, hg, hn, hP⟩ :=
    GlobalTheory.T.exists_normalised_iso_pulledBack_period_relation n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ lb y hy
  exact ⟨q, GlobalTheory.T.pulledBack_period_constants_symmetric n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ y hy w₁ q hg hP hn,
    GlobalTheory.T.pulledBack_period_constants_multiplicative n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ y hy w₁ q hg hP hn,
    GlobalTheory.T.pulled_back_period_constants_diag_mem_maximal n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ y hy w₁ q hg hP,
    GlobalTheory.T.degData_from_lowerBase_after_monomial_extension n V D r e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV hVd h1 h1d hi hf hl hκ p₁ p₂ s₁ s₂ y hy w₁ q hg hP⟩

end GlobalTheory.TChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPulledBackPeriodsBasePeriodsConstFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pulledBack_periods_basePeriods_constForm : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → LBIso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') → (∀ a : Fin L.T.r → ℤ, ∃ x : Sp V₁ ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ x ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∃ q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ, (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V₁, w ≠ 0 ∧ (q a a : FractionRing V₁) = algebraMap V₁ _ w) ∧ ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)), IsCN V₂ → Function.Injective f₂ → f₂.Finite → IsLocalHom f₂ → (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegData V₂ (maximalIdeal V₂)) (hD : IsPullDeg (f₂.comp f₁) D.toPre D'.toPre), DegFrom L.T (f₂.comp κ₁) s ε n D'.toPre (hD.xe.trans (e₀.symm.trans e.symm)) := by
  first | exact @GlobalTheory.TChart.exists_periods_of_pull | exact GlobalTheory.TChart.exists_periods_of_pull | (intros; apply GlobalTheory.TChart.exists_periods_of_pull <;> assumption)
end
