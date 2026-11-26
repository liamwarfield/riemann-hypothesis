module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsNilpotentOfRd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsFOfIntegral
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaSpecialise

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange

theorem gs_pullOver {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of R')}
    {f : R →+* R'} {p : Y' ⟶ Y} (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) {φ' : K → (Y' ⟶ X)}
    (hφ : ∀ k, φ' k = p ≫ φ k) (s : SecOver π (LB.LinComb L φ ε)) (r : Z ⟶ Y') (z : Z) (j : K → L.ι)
    (hj : ∀ k, φ' k (r z) ∈ L.U (j k)) :
    gs r z (LB.wchart L φ' j) (LB.Sec.f (pullOver L ε hp hφ s) j) = gs (r ≫ p) z (LB.wchart L φ j) (LB.Sec.f s j) :=
  gs_pullFn hp _ _ r z (mem_wchart.2 hj)

section Act

variable {S₀ : Scheme.{0}} {A : Over S₀} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S₀}
  {S : Type} [CommRing S]

theorem lpow_ext (hL : L.IsLB) {s s' : LB.Sec (LPow A L k T)}
    (h : ∀ y J, Good L y J → secVal s (𝟙 _) y J = secVal s' (𝟙 _) y J) : s = s' :=
  sec_ext' (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) hL h

theorem secVal_add' (π : (T ⊗ A).left ⟶ Spec (CommRingCat.of S)) (s t : SecOver π (LPow A L k T))
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    secVal (s + t : SecOver π _) r z J = secVal s r z J + secVal t r z J :=
  sval_add' (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) (π := π) hJ r s t

theorem secVal_smul' (π : (T ⊗ A).left ⟶ Spec (CommRingCat.of S)) (c : S) (s : SecOver π (LPow A L k T))
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    secVal (c • s : SecOver π _) r z J = constVal (r ≫ π) z c * secVal s r z J :=
  sval_smul' (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) (π := π) hJ r c s

theorem exists_actMap (hL : L.IsLB) (θ : ThetaGrp A L k T) (q : T.left ⟶ Spec (CommRingCat.of S))
    (π : (T ⊗ A).left ⟶ Spec (CommRingCat.of S)) (hπ : π = (fst T A).left ≫ q) :
    ∃ a : SecOver π (LPow A L k T) →ₗ[S] SecOver π (LPow A L k T), Function.Injective a ∧
      ∀ s s', IsActOf A L k θ s s' ↔ a s = s' := by
  choose a ha using fun s : SecOver π (LPow A L k T) => exists_actVal hL θ s
  have e : (𝟙 _ ≫ (translT A θ.pt).left) ≫ π = 𝟙 _ ≫ π := by
    rw [hπ, Category.assoc, ← Category.assoc (translT A θ.pt).left, ← Over.comp_left, translT, lift_fst]
  refine ⟨{ toFun := a
            map_add' := fun s t => lpow_ext hL fun y J hJ => ?_
            map_smul' := fun c s => lpow_ext hL fun y J hJ => ?_ }, fun s t h => lpow_ext hL fun y J hJ => ?_,
    fun s s' => ⟨fun H => lpow_ext hL fun y J hJ => (ha s _ _ y J hJ).trans (actVal_of_isActOf H _ _ y J hJ).symm,
      fun H => H ▸ (ha s).isActOf hL⟩⟩
  · refine (ha _ _ _ y J hJ).trans (Eq.trans ?_ (secVal_add' π _ _ _ y hJ).symm)
    rw [secVal_add' π _ _ _ y hJ, mul_add]
    exact (congrArg₂ (· + ·) (ha s _ _ y J hJ) (ha t _ _ y J hJ)).symm
  · refine (ha _ _ _ y J hJ).trans (Eq.trans ?_ (secVal_smul' π _ _ _ y hJ).symm)
    rw [secVal_smul' π _ _ _ y hJ, mul_left_comm, e]
    exact (congrArg _ (ha s _ _ y J hJ)).symm
  · have h : a s = a t := h
    have r : (translT A θ.pt⁻¹).left ≫ (translT A θ.pt).left = 𝟙 _ := by
      rw [← Over.comp_left, translT_mul, mul_inv_cancel, translT_one, Over.id_left]
    have e₁ := ha s _ (translT A θ.pt⁻¹).left y J hJ
    have e₂ := ha t _ (translT A θ.pt⁻¹).left y J hJ
    rw [r] at e₁ e₂
    rw [h] at e₁
    exact (Units.mul_right_inj _).1 (e₁.symm.trans e₂)

theorem exists_act_ratio (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {F : Type} [Field F]
    {t : Spec (CommRingCat.of F) ⟶ S₀} (θ θ' : ThetaGrp A L k (Over.mk t)) (h : θ.pt = θ'.pt)
    (π : (Over.mk t ⊗ A).left ⟶ Spec (CommRingCat.of F)) (hπ : π = (fst (Over.mk t) A).left) :
    ∃ c : F, c ≠ 0 ∧ ∀ s s₁ s₂ : SecOver π (LPow A L k (Over.mk t)), IsActOf A L k θ s s₁ →
      IsActOf A L k θ' s s₂ → s₂ = c • s₁ := by
  obtain ⟨u, hu⟩ := ThetaAct.exists_ratio hG hA hL θ θ' h
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 u.val
  refine ⟨c, ?_, fun s s₁ s₂ h₁ h₂ => lpow_ext hL fun y J hJ => ?_⟩
  · rintro rfl
    have : Nontrivial Γ((Over.mk t).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    exact u.ne_zero (hc.symm.trans (map_zero _))
  · refine (actVal_of_isActOf h₂ _ _ y J hJ).trans (Eq.trans ?_ (secVal_smul' π _ _ _ y hJ).symm)
    rw [actVal_of_isActOf h₁ _ _ y J hJ, ← _root_.mul_assoc, h]
    refine congrArg (· * _) ((hu _ _ y J hJ).trans (congrArg (· * _) ?_))
    rw [hπ, ← hc]; rfl

end Act

section Side

variable {S₀ S₁ : Scheme.{0}} {G : Over S₀} [GrpObj G] {A : Over S₁} [GrpObj A]
  {f : S₁ ⟶ S₀} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S₁} {T₀ : Over S₀} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}


include hp hτ in
theorem exists_psi : ∃ ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left, IsPullback ψ (fst T A).left (fst T₀ G).left τ ∧
    ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ ∧ ψ = (psiO hp τ hτ).left := by
  refine ⟨(psiO hp τ hτ).left, ?_, psi_snd hp τ hτ, rfl⟩
  have h₀ : IsPullback (snd T₀ G).left (fst T₀ G).left G.hom T₀.hom := (IsPullback.of_hasPullback _ _).flip
  have h₁ : IsPullback (snd T A).left (fst T A).left A.hom T.hom := (IsPullback.of_hasPullback _ _).flip
  refine IsPullback.of_right ?_ (psi_fst hp τ hτ) h₀
  rw [psi_snd, hτ]
  exact h₁.paste_horiz hp.1

theorem exists_theta_side (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) (k : ℤ)
    (x : T ⟶ A) (θ₀ : ThetaGrp G L₀ k T₀) (hx : τ ≫ θ₀.pt.left = x.left ≫ φ)
    {ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left} (hψ : ψ = (psiO hp τ hτ).left) :
    ∃ θ : ThetaGrp A L₁ k T, θ.pt = x ∧ ∀ (s₀ s₀' : LB.Sec (LPow G L₀ k T₀)) (s s' : LB.Sec (LPow A L₁ k T)),
      PSec w (fun _ : Fin 1 => (snd T A).left) (fun _ => (snd T₀ G).left) (fun _ => k) ψ s s₀ →
      PSec w (fun _ : Fin 1 => (snd T A).left) (fun _ => (snd T₀ G).left) (fun _ => k) ψ s' s₀' →
      IsActOf G L₀ k θ₀ s₀ s₀' → IsActOf A L₁ k θ s s' := by
  obtain ⟨θ, rfl, hm⟩ := exists_theta_move hp τ hτ hL₀ hL₁ w hw k x θ₀ hx
  have hm : PMaps w ![(snd T A).left, (translPt A θ.pt).left] ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![k, -k]
      θ.φ θ₀.φ ψ := hψ ▸ hm
  have c₁ : (snd T A).left ≫ φ = ψ ≫ (snd T₀ G).left := hψ ▸ (psi_snd hp τ hτ).symm
  have c₂ : (translPt A θ.pt).left ≫ φ = ψ ≫ (translPt G θ₀.pt).left := hψ ▸ (psi_tr hp τ hτ _ _ hx).symm
  have c₃ : (translT A θ.pt).left ≫ ψ = ψ ≫ (translT G θ₀.pt).left := hψ ▸ psi_transl hp τ hτ _ _ hx
  refine ⟨θ, rfl, fun s₀ s₀' s s' m m' H => (ThetaAct.isActOf_iff hL₁ θ s s').2 fun y J hJ => ?_⟩
  choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
  have hJ₀ : Good L₀ y J₀ := hJ₀
  have c : ∀ _ : Fin 1, (snd T A).left ≫ φ = ψ ≫ (snd T₀ G).left := fun _ => c₁
  have a := actVal_of_isActOf H _ (𝟙 _ ≫ ψ) y J₀ hJ₀
  have b := ExpTrans.gen_val w _ _ _ _ (fun i => by
    fin_cases i
    · exact c₁
    · exact c₂) _ _ hm y hJ₀ hJ
  have d := ExpTrans.sec_val w _ _ _ _ c _ _ (𝟙 _) y (m' _ (𝟙 _) y) hJ₀ hJ
  have e := ExpTrans.sec_val w _ _ _ _ c _ _ (𝟙 _ ≫ (translT A θ.pt).left) y (m _ _ y) hJ₀ hJ
  have g : (𝟙 _ ≫ ψ) ≫ (translT G θ₀.pt).left =
      (𝟙 _ ≫ (translT A θ.pt).left) ≫ ψ := by
    rw [Category.assoc, Category.assoc, c₃]
  rw [g] at a
  rw [Fin.prod_univ_one] at d e
  rw [Fin.prod_univ_two] at b
  rw [Category.assoc _ _ (snd T A).left, translT_snd_left, Category.id_comp (translPt A θ.pt).left] at e
  rw [Category.id_comp (snd T A).left] at d
  have b' : thetaVal θ₀ (𝟙 _ ≫ ψ) y J₀ = ExpTrans.om w y J₀ J (snd T A).left ^ k *
      ExpTrans.om w y J₀ J (translPt A θ.pt).left ^ (-k) * thetaVal θ (𝟙 _) y J := by
    rw [Category.id_comp]; exact b
  have z := d.symm.trans (a.trans (congrArg₂ (· * ·) (congrArg Units.val b') e))
  refine (ExpTrans.om w y J₀ J (snd T A).left ^ k).mul_right_inj.1 (z.trans ?_)
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, zpow_neg, mul_right_comm _ _⁻¹,
    inv_mul_cancel_right]
  rfl

end Side

section Phi

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem eq_zero_of_phiVal {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (s : Fam D F k)
    (h : PhiVal p w s.s (0 : Fam D F k).s) : s = 0 := by
  have := D.P.isAb.comm
  have r : DegPre.trPt D F p.g.b⁻¹ ≫ DegPre.trPt D F p.g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, tr_fst, Category.id_comp]
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D F _)).trans ?_)
      rw [MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, _root_.mul_assoc, ← MonObj.comp_mul, inv_mul_cancel,
        MonObj.comp_one, _root_.mul_one, Category.id_comp]
  refine fam_ext fun α j => sec_ext_val D.P.isLB (fun y J hJ => ?_) j
  have e := h α _ rfl _ (DegPre.trPt D F p.g.b⁻¹) y J hJ
  rw [r] at e
  have z : ∀ β (r : (DegPre.BF D F).left ⟶ (DegPre.BF D F).left), sval ((0 : Fam D F k).s β) r y J = 0 := fun β r =>
    sval_zero' (π := famBase D F) hJ r
  rw [z] at e ⊢
  exact (Units.mul_left_eq_zero _).1 e.symm

end Phi

section Expand

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem expandsF_of_integral {k : ℕ}
    {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))}
    {u : LB.Iso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R)))}
    (hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ A.A.left) (z : Z) (j : U.LG.L.ι) (i : A.L.ι),
      (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) (f z) ∈ U.LG.L.U j → f z ∈ A.L.U i →
      gw u f z j i = isoVal w (f ≫ U.gen.inv.left) z j i)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hE : ∀ e, U.ExpandsAt e k σ f) (s : Fam D.toPre F k)
    (hs : ∀ α y J, Good D.toPre.P.L y J →
      sval (s.s α) (𝟙 _) y J = sval (f α) (𝟙 _ ≫ (DegPre.prB D.toPre F).left) y J)
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)))
    (ht : PSec u (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))
      ((snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) t σ) :
    U.ExpandsF F k w t s := by
  have h₂ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)
  have n₃ : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left]
  have h₃ : ((𝟙 _ ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left) ≫ U.gen.inv.left =
      𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
    rw [Category.id_comp, Category.id_comp, h₂, Category.assoc, n₃, Category.comp_id]
  have h₄ : (𝟙 _ ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      (𝟙 _ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R) := by
    rw [← h₃]; simp only [Category.assoc]
  have one : ∀ {Y : Scheme.{0}} (π : Y ⟶ Spec (CommRingCat.of F)) (y : Y), gs (𝟙 Y) y ⊤ (scal π (1 : F)) = 1 :=
    fun π y => by simp only [gs_eq _ y ⊤ trivial, scal, map_one]
  refine ⟨extendSec U F k (genericSec U k σ), (isoRelM_iff w _ k _ h₂ _ (Category.id_comp _) _ _).2
    fun y i₂ i₁ a₂ a₁ => ?_, 1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE,
    (secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => ?_,
    fun α => (secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_⟩
  · have b₂ := (congrArg (fun q : _ ⟶ G.left => q y ∈ U.LG.L.U i₂) h₄).mpr a₂
    have b₁ := (congrArg (fun q : _ ⟶ A.A.left => q y ∈ A.L.U i₁) h₂).mpr a₁
    have e := ht _ (𝟙 _ ≫ (U.genF F).left) y (fun _ => i₂) (fun _ => i₁) (fun _ => b₂) (fun _ => b₁)
    rw [Fin.prod_univ_one, hu _ ((𝟙 _ ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left) y i₂ i₁ b₂ b₁, h₃, h₄] at e
    refine Eq.trans ?_ e
    rw [Category.id_comp (𝟙 _)]
    exact (gs_pullOver (isPullback_groupBase F).w (fun _ => rfl) (genericSec U k σ) (𝟙 _) y (fun _ => i₂)
      (fun _ => a₂)).trans (gs_pullOver (p := pullback.fst G.hom (jK R)) pullback.condition
        (fun _ => (Category.comp_id _).symm) σ _ y (fun _ => i₂) (fun _ => a₂))
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
      (congrArg (fun q => sval σ q y J) (Category.assoc _ _ _)))
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact hs α y J hJ

end Expand

end GlobalTheory.ThetaSpecialise
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KerAppEqMapAppLEOfIsPullback
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem ker_app_eq_map_appLE_of_isPullback {Y Z : Scheme.{0}} {A C : CommRingCat.{0}}
    {β : A ⟶ C} (hβ : Function.Surjective β) {f : Y ⟶ Spec A} {i : Z ⟶ Y} {f' : Z ⟶ Spec C}
    (h : IsPullback i f' f (Spec.map β)) {U : Y.Opens} (hU : IsAffineOpen U) :
    RingHom.ker (i.app U).hom =
      (RingHom.ker β.hom).map ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top).hom := by
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := i ⁻¹ᵁ U) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top) β (i.app U)
      ((Scheme.ΓSpecIso C).inv ≫ f'.appLE ⊤ (i ⁻¹ᵁ U) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  exact PrimeSection.ker_eq_map_of_isPushout hpo' hβ

theorem isPullback_red_of_ker_app_le_map (A : Type) [CommRing A] (J : Ideal A)
    (B₀ B : Scheme.{0}) (j : B₀ ⟶ B) (s₀ : B₀ ⟶ Spec (CommRingCat.of (A ⧸ J)))
    (s : B ⟶ Spec (CommRingCat.of A)) (hj : IsClosedImmersion j) (w : j ≫ s = s₀ ≫ red J)
    (hloc : ∀ b : B, ∃ V : B.Opens, b ∈ V ∧ IsAffineOpen V ∧ RingHom.ker (j.app V).hom ≤
      J.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ s.appLE ⊤ V le_top).hom) :
    IsPullback j s₀ s (red J) := by
  have hr : IsClosedImmersion (red J) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hp : IsClosedImmersion (pullback.fst s (red J)) := inferInstance
  have hl : pullback.lift j s₀ w ≫ pullback.fst s (red J) = j := pullback.lift_fst _ _ _
  have hker : j.ker = (pullback.fst s (red J)).ker := by
    refine le_antisymm ?_ ?_
    · choose V hb hV hle using hloc
      have hcov : ⨆ b, ((⟨V b, hV b⟩ : B.affineOpens) : B.Opens) = ⊤ :=
        eq_top_iff.2 fun b _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨b, hb b⟩
      refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun b ↦ ⟨V b, hV b⟩) hcov fun b ↦ ?_
      rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
      have e := ker_app_eq_map_appLE_of_isPullback
        (β := CommRingCat.ofHom (Ideal.Quotient.mk J)) Ideal.Quotient.mk_surjective
        (IsPullback.of_hasPullback s (red J)) (hV b)
      rw [CommRingCat.hom_ofHom, Ideal.mk_ker] at e
      exact (hle b).trans e.ge
    · have := (pullback.lift j s₀ w).le_ker_comp (pullback.fst s (red J))
      rwa [hl] at this
  have := IsClosedImmersion.isIso_of_ker_eq j (pullback.fst s (red J)) _ hl hker
  exact .of_iso_pullback ⟨w⟩ (asIso (pullback.lift j s₀ w)) hl (pullback.lift_snd _ _ _)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LbIsoPwPullPowLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LbIsoPwPullPowLocal
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

theorem lbIso_pw_pull_of_hasGen {X : Scheme.{0}} {L : LB X} (F : X ⟶ X) (t : ℤ)
    (h : MulPull.HasGen L (K := Fin 2) ![F, 𝟙 X] ![1, -t]) : LBIso (pw L t) (L.pull F) := by
  obtain ⟨a, ha⟩ := h
  have mem : ∀ (x : X) (j k : L.ι), F x ∈ L.U j → x ∈ L.U k → x ∈ LB.wchart L ![F, 𝟙 X] ![j, k] :=
    fun x j k hj hk => Set.mem_iInter.2 fun i => by
      fin_cases i
      · exact hj
      · exact hk
  have le : ∀ p : (L.pull F).ι × L.ι,
      (L.pull F).U p.1 ⊓ L.U p.2 ≤ LB.wchart L ![F, 𝟙 X] ![p.1 PUnit.unit, p.2] :=
    fun p x hx => mem x _ _ (mem_pull.1 hx.1) hx.2
  let w : LB.Iso (pw L t) (L.pull F) := ⟨fun p => res (le p) (a.s _)⟩
  refine ⟨w, (isGen_iff w).2 fun Y r y j j' k k' hj hj' hk hk' => ?_⟩
  have e : ∀ j k, F (r y) ∈ L.U j → r y ∈ L.U k →
      gw w r y j k = gm r y (LB.wchart L ![F, 𝟙 X] ![j, k]) (a.s ![j, k]) := fun j k hj hk =>
    gm_res r y (le (fun _ => j, k)) ⟨mem_pull.2 hj, hk⟩ _
  rw [e j k hj hk, e j' k' hj' hk', gen_trans ha r y (mem _ _ _ hj hk) (mem _ _ _ hj' hk'), trF, Fin.prod_univ_two]
  congr 1
  show gm (r ≫ F) y _ (L.g j j') ^ (1 : ℤ) * gm (r ≫ 𝟙 X) y _ (L.g k k') ^ (-t) =
    gm (r ≫ F) y _ (L.g j j') * (gm r y (L.U k ⊓ L.U k') (L.g k k' ^ t))⁻¹
  rw [zpow_one, Category.comp_id, map_zpow, zpow_neg]

theorem CP.lbIso_pw_pull_pow {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] (M : CP B) (n : ℕ) :
    LBIso (pw M.L.L ((n : ℤ) ^ 2)) (M.L.L.pull (𝟙 B ^ n).left) := by
  have hL := M.L.isLB
  have hcube : MulPull.HasGen M.L.L (thφ B (x3 B)) thε := ⟨M.c.t, M.c.isGen⟩
  have hrig : MulPull.HasGen M.L.L (K := PUnit) (fun _ => eSec B) (fun _ => 1) := ⟨M.L.rig, M.L.rigGen⟩
  have hsym : MulPull.HasGen M.L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1] := ⟨M.sym, M.sym_gen⟩
  have h := MulPull.hasGen_pow hL hcube (𝟙 B) ((hrig.pull B.hom).of_formEq hL (fun U _ h => by
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one, one_left]
      rfl))
    (hsym.inv.of_formEq hL (fun U _ h => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two, Hom.inv_def, Category.id_comp, mul_comm]
      rfl)) n
  refine lbIso_pw_pull_of_hasGen _ _ (h.inv.of_formEq hL fun U _ h => ?_)
  rw [Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]
  rfl

theorem lbIso_pw_pull_pow_local : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B] (M : CP B) (n : ℕ), LBIso (pw M.L.L ((n : ℤ) ^ 2)) (M.L.L.pull (𝟙 B ^ n).left) :=
  fun _ _ _ _ _ _ M n => M.lbIso_pw_pull_pow n

end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LbIsoPwPullPowLocalStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.lbIso_pw_sq_pull_pow_of_isLocalRing : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B] (M : CP B) (n : ℕ), LBIso (pw M.L.L ((n : ℤ) ^ 2)) (M.L.L.pull (𝟙 B ^ n).left) := by
  first | exact @GlobalTheory.UU.lbIso_pw_pull_pow_local | exact GlobalTheory.UU.lbIso_pw_pull_pow_local | (intros; apply GlobalTheory.UU.lbIso_pw_pull_pow_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitRatio
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.BiTrivUniq

variable {X Y : Scheme.{0}} {M : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem exists_unit_ratio (hM : M.IsLB) {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      val u r z J = gm r z ⊤ a * val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← mul_inv_eq_iff_eq_mul, ← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (gm_res r z le trivial _).symm

theorem gen_eq_of_val (hM : M.IsLB) {t t' : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    (h : ∀ y J, Good M y J → val t (𝟙 Y) y J = val t' (𝟙 Y) y J) : t = t' := by
  obtain ⟨s⟩ := t
  obtain ⟨s'⟩ := t'
  congr 1
  funext j
  refine unit_ext (V := LB.wchart M φ j) fun y hy => ?_
  obtain ⟨I, hI⟩ := exists_good_pt hM y
  exact (gen_trans ht (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).trans ((congrArg _ (h y I hI)).trans
    (gen_trans ht' (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).symm)

end GlobalTheory.UU.BiTrivUniq

namespace GlobalTheory.UU
open BiTrivUniq

theorem biTriv_unique : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    [ConnectedSpace G.left] (L : RigLB G) (c : CubicalStr G L) (i : splitTorus S X ⟶ G), IsMonHom i →
    ∀ s s' : BiTriv c i, s = s' := by
  intro S X _ G _ _ _ L c i _ s s'
  obtain ⟨ρ, hρ⟩ := exists_unit_ratio L.isLB s.gen s'.gen
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.existsUnique_character_of_mul S X G ρ fun Z t t' y => by
    have e : Units.map (lift (t * t') y).left.appTop.hom.toMonoidHom ρ =
        Units.map (lift t y).left.appTop.hom.toMonoidHom ρ * Units.map (lift t' y).left.appTop.hom.toMonoidHom ρ := by
      refine unit_ext fun z _ => ?_
      obtain ⟨J, hJ⟩ := exists_good_pt L.isLB z
      have a := s.law1 Z t t' y z J hJ
      rw [hρ _ _ z J hJ, hρ _ _ z J hJ, hρ _ _ z J hJ, s'.law1 Z t t' y z J hJ] at a
      rw [map_mul, ← gm_top, ← gm_top, ← gm_top]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      simp only [ofMul_mul] at a' ⊢
      linear_combination (norm := abel) a'
    exact congrArg Units.val e
  have key : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (x : Z ⟶ G) (z : Z.left),
      gm (lift t x).left z ⊤ ρ = gm (𝟙 Z.left) z ⊤ (chV t χ) := fun Z t x z => by
    rw [gm_top]
    congr 1
    refine Units.ext ?_
    rw [chV_val]
    show (lift t x).left.appTop.hom ρ.val = _
    rw [hχ, Rosenlicht.over_appTop_comp, lift_fst]
  have hs : s.s = s'.s := gen_eq_of_val L.isLB s.gen s'.gen fun y J hJ => by
    have a := hρ _ (lift (fst (splitTorus S X) G) (1 : _ ⟶ G)).left y J hJ
    rw [s.val_one_right hJ, s'.val_one_right hJ, key, _root_.mul_one, ← key _ _ (snd _ _), lift_fst_snd,
      Over.id_left] at a
    rw [hρ _ _ y J hJ, ← a, _root_.one_mul]
  obtain ⟨s, _, _, _⟩ := s
  obtain ⟨s', _, _, _⟩ := s'
  obtain rfl : s = s' := hs
  rfl

end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTermBasis
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamDim

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_class_reps (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : ℕ)
    (hk : 1 ≤ k) : ∃ ρ : (Fin (Module.finrank ℤ X) → Fin k) → X,
      (∀ q q' mu, ρ q + k • mu = ρ q' → q = q') ∧ (∀ β, ∃ q mu, ρ q + k • mu = β) ∧
      ∀ a b : X, k • a = k • b → a = b := by
  let B := (Module.finBasis ℤ X).equivFun
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨fun q => B.symm (fun i => ((q i : ℕ) : ℤ)), fun q q' mu h => ?_, fun β => ?_, fun a b h => ?_⟩
  · funext i
    have e := congrFun (congrArg B h) i
    simp only [map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, Pi.smul_apply] at e
    rw [nsmul_eq_mul] at e
    have e2 := congrArg (· % (k : ℤ)) e
    simp only [Int.add_mul_emod_self_left] at e2
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (q i).2),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (q' i).2)] at e2
    exact Fin.ext (by exact_mod_cast e2)
  · refine ⟨fun i => ⟨(B β i % k).toNat, ?_⟩, B.symm (fun i => B β i / k), ?_⟩
    · have := Int.emod_lt_of_pos (B β i) hk'
      have := Int.emod_nonneg (B β i) hk'.ne'
      omega
    · apply B.injective
      funext i
      simp only [map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, Pi.smul_apply]
      rw [nsmul_eq_mul, Int.toNat_of_nonneg (Int.emod_nonneg _ hk'.ne')]
      exact Int.emod_add_mul_ediv _ _
  · apply B.injective
    funext i
    have e := congrFun (congrArg B h) i
    simp only [map_nsmul, Pi.smul_apply, nsmul_eq_mul] at e
    exact mul_left_cancel₀ hk'.ne' e

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
  [Algebra (FractionRing R) F] {k : ℕ}

theorem fam_term_eq (hG : GlobalFnsSt) {s t : Fam D F k} {ρ : D.X} (h : s.s ρ = t.s ρ) (mu : D.X) (j) :
    (s.s (ρ + k • mu)).f j = (t.s (ρ + k • mu)).f j := by
  have hL := D.P.isLB
  obtain ⟨u, hu, hc⟩ := (gen_fe (D := D) (F := F) hG k mu ρ).1
  refine sec_ext_val hL (fun y J hJ => ?_) j
  rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (s.fe mu ρ u hu hc) _ _ y J hJ,
    (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (t.fe mu ρ u hu hc) _ _ y J hJ, h]

theorem sum_smul_f {I : Type} (S : Finset I) (c : I → F) (e : I → Fam D F k) (α : D.X) (j) :
    ((∑ x ∈ S, c x • e x).s α).f j = ∑ x ∈ S, resTop _ (gF D F (c x)) * ((e x).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, smul_f, ih]

theorem famφ_eq (α : D.X) :
    DegPre.famφ D F α = fun i => (snd (TF (R := R) F) D.P.A).left ≫ DegPre.famφB D α i := by
  funext i
  fin_cases i
  · exact (Category.comp_id _).symm
  · show (padd D.P.A _ _).left = (snd (TF (R := R) F) D.P.A ≫ padd D.P.A _ _).left
    congr 1
    simp only [padd, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
  · show (toUnit (DegPre.BF D F) ≫ D.c α).left = (snd (TF (R := R) F) D.P.A ≫ toUnit _ ≫ D.c α).left
    rw [comp_toUnit_assoc]
  · show (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left = (snd (TF (R := R) F) D.P.A ≫ toUnit _ ≫ η[D.P.A]).left
    rw [comp_toUnit_assoc]

theorem exists_term_basis (hG : GlobalFnsSt) (hP : PolBaseChangeSt) (hT : TwistBaseChangeStatement)
    [IsNoetherianRing R]
    (hW : ∃ W : (Spec (CommRingCat.of R)).Opens, genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W))
    (hk : 1 ≤ k) (α : D.X) :
    ∃ b : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)),
      ∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)),
        ∃! c : Fin (k ^ D.P.g) → F, ∀ j, s.f j = ∑ i, resTop _ (gF D F (c i)) * (b i).f j := by
  let f : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have key : ∀ (t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)), t = Spec.map (CommRingCat.ofHom f) →
      ∀ φ : Fin 4 → ((Over.mk t ⊗ D.P.A).left ⟶ D.P.A.left),
        φ = (fun i => (snd (Over.mk t) D.P.A).left ≫ DegPre.famφB D α i) →
      ∃ b : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L φ (DegPre.famε k)),
        IsSecBasis (T := Over.mk t) (A := D.P.A) _ b := by
    rintro t rfl φ rfl
    obtain ⟨b, hb⟩ := GlobalTheory.T.exists_twist_basis_off_prime hP hG hT R D hW ⊥ k hk α
    let b' := fun i => DVR.pullSec (L := D.P.L) (DegPre.famφB D α) (DegPre.famε k) (b i)
      (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left
    refine ⟨b', hb F f (fun s hs => ?_) b' (fun i j => rfl)⟩
    refine IsUnit.mk0 _ fun h0 => hs ?_
    have h1 : algebraMap R (FractionRing R) s = 0 := (algebraMap (FractionRing R) F).injective (h0.trans (map_zero _).symm)
    exact (IsFractionRing.to_map_eq_zero_iff (K := FractionRing R)).1 h1
  obtain ⟨b, hb⟩ := key (jFK (R := R) F ≫ jK R) (by
    simp only [jFK, jK, f, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) _ (famφ_eq α)
  refine ⟨b, fun s => ?_⟩
  obtain ⟨r, hr, hu⟩ := hb s
  let e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
  refine ⟨fun i => e (r i), fun j => (hr j).trans (Finset.sum_congr rfl fun i _ => ?_), fun c hc => ?_⟩
  · congr 2
    show _ = (fst (TF (R := R) F) D.P.A).left.appTop.hom (e.symm (e (r i)))
    rw [e.symm_apply_apply]
  · have := hu (fun i => e.symm (c i)) hc
    funext i
    rw [← this]
    exact (e.apply_symm_apply _).symm

theorem finrank_fam : GlobalFnsSt → PolBaseChangeSt → DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), D.TauBimult → (∃ W : (Spec (CommRingCat.of R)).Opens, genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W)) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Module.Finite F (Fam D F k) ∧ Module.finrank F (Fam D F k) = k ^ (D.rank + D.P.g) := by
  intro hG hP hT R _ _ _ D hB hW F _ _ k hk
  classical
  obtain ⟨ρ, hρ, hsurj, hcan⟩ := exists_class_reps D.X k hk
  choose b hb using fun α => exists_term_basis (D := D) (F := F) hG hP hT hW hk α
  choose e he he0 using fun x : (Fin D.rank → Fin k) × Fin (k ^ D.P.g) =>
    UUA.exists_fam_rep (F := F) hG hB k (ρ x.1) (fun a c h => hcan a c (add_left_cancel h)) (b (ρ x.1) x.2)
  have ev : ∀ (c : (Fin D.rank → Fin k) × Fin (k ^ D.P.g) → F) q j,
      ((∑ x, c x • e x).s (ρ q)).f j = ∑ i, resTop _ (gF D F (c (q, i))) * (b (ρ q) i).f j := by
    intro c q j
    rw [sum_smul_f, Fintype.sum_prod_type, Finset.sum_eq_single q]
    · exact Finset.sum_congr rfl fun i _ => by rw [he (q, i)]
    · intro q' _ hq
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [he0 (q', i) (ρ q) (fun mu h => hq (hρ _ _ _ h)) j, mul_zero]
    · intro h; exact absurd (Finset.mem_univ q) h
  have hli : LinearIndependent F e := by
    rw [Fintype.linearIndependent_iff]
    rintro c hc ⟨q, i⟩
    have h1 := (hb (ρ q) SecOps.secZero).unique (y₁ := fun i => c (q, i)) (y₂ := fun _ => 0)
      (fun j => by rw [← ev, hc]; rfl)
      (fun j => by simp only [map_zero, resTop, zero_mul, Finset.sum_const_zero]; rfl)
    exact congrFun h1 i
  have hsp : ⊤ ≤ Submodule.span F (Set.range e) := by
    intro s _
    choose c hc using fun q => (hb (ρ q) (s.s (ρ q))).exists
    refine (Submodule.mem_span_range_iff_exists_fun F).2 ⟨fun x => c x.1 x.2, fam_ext fun β j => ?_⟩
    obtain ⟨q, mu, rfl⟩ := hsurj β
    refine fam_term_eq hG (SecOps.sec_ext fun j' => ?_) mu j
    rw [ev (fun x => c x.1 x.2) q j', hc q j']
  let B := Module.Basis.mk hli hsp
  refine ⟨Module.Finite.of_basis B, ?_⟩
  rw [Module.finrank_eq_card_basis B, pow_add]
  simp

end GlobalTheory.FamDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvSurjective
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.CubeLift

open SplitTorus (ev univPt ptOf pull bcMap ofVal valHom)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (chi torusFst)

section Expand

variable {S S' : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {R : CommRingCat.{0}}

private theorem app_global_comp_apply {U V W' : Scheme.{0}} (f : U ⟶ V) (g : V ⟶ W') (u : Γ(W', ⊤)) :
    (f ≫ g).appTop.hom u = f.appTop.hom (g.appTop.hom u) := by
  rfl

private theorem splitTorus_pull_comp {B : CommRingCat.{0}} {s : Spec B ⟶ S}
    (g : Over.mk s ⟶ splitTorus S Y) (h : splitTorus S Y ⟶ splitTorus S X) (u : Γ((splitTorus S X).left, ⊤)) :
    pull (g ≫ h) u = pull g (h.left.appTop.hom u) := by
  simp only [SplitTorus.pull, RingHom.comp_apply, Over.comp_left, app_global_comp_apply]

theorem ev_torusMap (t : Spec R ⟶ S) (φ : X →+ Y) (u : Γ((splitTorus S X).left, ⊤)) :
    ev t ((SplitTorus.torusMap S φ).left.appTop.hom u) = mv φ (ev t u) := by
  have key : ∀ hs, univPt Y t ≫ SplitTorus.torusMap S φ =
      ptOf (B := CommRingCat.of (AddMonoidAlgebra R Y)) t (mv φ) hs := by
    intro hs
    refine SplitTorus.pull_ext fun a => ?_
    rw [SplitTorus.pull_ptOf, splitTorus_pull_comp, SplitTorus.torusMap_appTop_chi]
    change ev t _ = _
    rw [SplitTorus.ev_chi, SplitTorus.ev_chi, mv_single]
  have hs : Spec.map (CommRingCat.ofHom ((mv φ : AddMonoidAlgebra R X →+* AddMonoidAlgebra R Y).comp
      (algebraMap R (AddMonoidAlgebra R X)))) ≫ t =
      Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R Y))) ≫ t := by
    congr 3
    ext r
    simp [mv]
  change pull (univPt Y t) _ = _
  rw [← splitTorus_pull_comp, key hs, SplitTorus.pull_ptOf]

theorem ev_bcMap (f : S' ⟶ S) (t : Spec R ⟶ S') (u : Γ((splitTorus S X).left, ⊤)) :
    ev t ((bcMap f X).appTop.hom u) = ev (t ≫ f) u := by
  have e : (univPt X t).left ≫ bcMap f X = (univPt X (t ≫ f)).left := by
    refine splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
    · simp [SplitTorus.bcMap_hom]
    · have h0 : (Scheme.ΓSpecIso _).hom.hom (SplitTorus.val (univPt X t) χ) =
          (Scheme.ΓSpecIso _).hom.hom (SplitTorus.val (univPt X (t ≫ f)) χ) := by
        rw [← SplitTorus.pull_chi, ← SplitTorus.pull_chi]
        exact (SplitTorus.ev_chi t χ).trans (SplitTorus.ev_chi (t ≫ f) χ).symm
      have h1 := congrArg (Scheme.ΓSpecIso _).inv.hom h0
      simp only [Iso.hom_inv_id_apply] at h1
      rw [SplitTorus.val_eq, SplitTorus.val_eq] at h1
      rw [app_global_comp_apply, SplitTorus.charUnit_val, SplitTorus.bcMap_appTop_chi]
      exact h1
  change pull (univPt X t) _ = pull (univPt X (t ≫ f)) u
  simp only [SplitTorus.pull, RingHom.comp_apply, ← e, app_global_comp_apply]

theorem ev_injective : Function.Injective (ev (X := X) (𝟙 (Spec R))) := by
  intro u v h
  refine SplitTorus.eq_of_ev fun B t => ?_
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ ≫ 𝟙 _ = t := ⟨Spec.preimage t, by simp⟩
  rw [SplitTorus.ev_comp, SplitTorus.ev_comp, h]

private theorem ev_base_apply (r : R) :
    ev (X := X) (𝟙 (Spec R)) ((splitTorus (Spec R) X).hom.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r)) =
      AddMonoidAlgebra.single 0 r := by
  change pull (univPt X _) _ = _
  have hw := Over.w (univPt X (𝟙 (Spec R)))
  simp only [SplitTorus.pull, RingHom.comp_apply]
  rw [← app_global_comp_apply, hw]
  erw [Category.comp_id]
  erw [SplitTorus.specMap_appTop_apply, Iso.inv_hom_id_apply]
  rfl

theorem ev_surjective : Function.Surjective (ev (X := X) (𝟙 (Spec R))) := by
  intro w
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | single x r =>
    refine ⟨(splitTorus (Spec R) X).hom.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) * chi X x, ?_⟩
    rw [map_mul, SplitTorus.ev_chi, ev_base_apply, AddMonoidAlgebra.single_mul_single, zero_add, _root_.mul_one]

end Expand

section Points

variable {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {Z Z' V : Over S}

abbrev app {Z V : Scheme.{0}} (r : Z ⟶ V) : Γ(V, ⊤)ˣ →* Γ(Z, ⊤)ˣ := Units.map r.appTop.hom.toMonoidHom

theorem app_app {Z Z' V : Scheme.{0}} (r : Z' ⟶ Z) (s : Z ⟶ V) (u : Γ(V, ⊤)ˣ) : app r (app s u) = app (r ≫ s) u := by
  ext
  exact (app_global_comp_apply r s u.val).symm

def pt (x y u : Z ⟶ splitTorus S X) : Z ⟶ splitTorus S (X × X × X) :=
  ofVal ((valHom x).coprod ((valHom y).coprod (valHom u)))

theorem pt_p₁ (x y u : Z ⟶ splitTorus S X) : pt x y u ≫ SplitTorus.torusMap S p₁ = x := by
  refine SplitTorus.hom_ext fun a => ?_
  rw [SplitTorus.val_comp_torusMap, pt, SplitTorus.val_ofVal]
  simp

theorem pt_p₂ (x y u : Z ⟶ splitTorus S X) : pt x y u ≫ SplitTorus.torusMap S p₂ = y := by
  refine SplitTorus.hom_ext fun a => ?_
  rw [SplitTorus.val_comp_torusMap, pt, SplitTorus.val_ofVal]
  simp

theorem pt_p₃ (x y u : Z ⟶ splitTorus S X) : pt x y u ≫ SplitTorus.torusMap S p₃ = u := by
  refine SplitTorus.hom_ext fun a => ?_
  rw [SplitTorus.val_comp_torusMap, pt, SplitTorus.val_ofVal]
  simp

theorem pt_torusMap (a b c : X →+ Y) : pt (SplitTorus.torusMap S a) (SplitTorus.torusMap S b) (SplitTorus.torusMap S c) = SplitTorus.torusMap S (tri a b c) := by
  refine SplitTorus.hom_ext fun p => ?_
  obtain ⟨x, y, z⟩ := p
  rw [pt, SplitTorus.val_ofVal, SplitTorus.val_torusMap]
  simp only [AddMonoidHom.coprod_apply, toMul_add, Units.val_mul, SplitTorus.valHom_apply,
    SplitTorus.val_torusMap, tri]
  rw [← SplitTorus.val_id, ← SplitTorus.val_id, ← SplitTorus.val_id, ← SplitTorus.val_id,
    SplitTorus.val_add, SplitTorus.val_add]

def dif [GrpObj V] (g : Γ(V.left, ⊤)ˣ) (x y u : Z ⟶ V) : Γ(Z.left, ⊤)ˣ :=
  app (x * y * u).left g * app x.left g * app y.left g * app u.left g / app (x * y).left g / app (x * u).left g /
    app (y * u).left g

theorem app_dif [GrpObj V] (g : Γ(V.left, ⊤)ˣ) (r : Z' ⟶ Z) (x y u : Z ⟶ V) :
    app r.left (dif g x y u) = dif g (r ≫ x) (r ≫ y) (r ≫ u) := by
  simp only [dif, map_mul, map_div, app_app, ← Over.comp_left, Hom.mul_def, comp_lift_assoc]

end Points

section Affine

variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

abbrev ex : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ →* (AddMonoidAlgebra A X)ˣ :=
  Units.map (ev (X := X) (𝟙 (Spec (CommRingCat.of A)))).toMonoidHom

theorem ex_bijective : Function.Bijective (ex (A := A) (X := X)) := by
  have hi := ev_injective (R := CommRingCat.of A) (X := X)
  have hs := ev_surjective (R := CommRingCat.of A) (X := X)
  refine ⟨fun u v h => Units.ext (hi (congrArg Units.val h)), fun w => ?_⟩
  obtain ⟨a, ha⟩ := hs w.val
  obtain ⟨b, hb⟩ := hs w.inv
  have hab : a * b = 1 := hi (by rw [map_mul, ha, hb, w.val_inv, map_one])
  exact ⟨⟨a, b, hab, by rw [_root_.mul_comm, hab]⟩, Units.ext ha⟩

theorem ex_app (φ : X →+ Y) (u : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ) :
    ex (app (SplitTorus.torusMap _ φ).left u) = um φ (ex u) := Units.ext (ev_torusMap (𝟙 _) φ u.val)

theorem ex_dif (a b c : X →+ Y) (g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ) :
    ex (dif g (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b) (SplitTorus.torusMap _ c)) = del (ex g) a b c := by
  simp only [dif, del, map_mul, map_div, ← SplitTorus.torusMap_add, ex_app]

theorem ex_mem_cong (J : Ideal A) (u : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ) :
    ex u ∈ cong J ↔ app (bcMap (red J) X) u = 1 := by
  have key : ev (𝟙 _) ((bcMap (red J) X).appTop.hom u.val) = rd J (ev (𝟙 _) u.val) := by
    rw [ev_bcMap, Category.id_comp,
      show red J = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ 𝟙 _ from (Category.comp_id _).symm,
      SplitTorus.ev_comp]
    rfl
  rw [mem_cong, Units.ext_iff, Units.val_one]
  change rd J (ev (𝟙 _) u.val) = 1 ↔ (bcMap (red J) X).appTop.hom u.val = 1
  constructor
  · intro h
    apply ev_injective
    rw [key, h, map_one]
  · intro h
    rw [← key, h, map_one]

variable {J : Ideal A}

theorem exists_dif (hJ : IsNilpotent J) (D : Γ((splitTorus (Spec (CommRingCat.of A)) (X × X × X)).left, ⊤)ˣ)
    (s₁ : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X),
      app (pt x y u).left D = app (pt y x u).left D)
    (s₂ : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X),
      app (pt x y u).left D = app (pt x u y).left D)
    (co : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u v : Z ⟶ splitTorus _ X),
      app (pt (x * y) u v).left D * app (pt x y v).left D = app (pt x (y * u) v).left D * app (pt y u v).left D)
    (h : app (bcMap (red J) _) D = 1) :
    ∃ g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ, app (bcMap (red J) X) g = 1 ∧
      ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X), app (pt x y u).left D = dif g x y u := by
  have hcub : Cub (ex (A := A) (X := X × X × X) D) := by
    refine ⟨fun Y _ a b c => ?_, fun Y _ a b c => ?_, fun Y _ a b c d => ?_⟩
    · have h1 := congrArg ex (s₁ (splitTorus _ Y) (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b)
        (SplitTorus.torusMap _ c))
      simpa only [pt_torusMap, ex_app] using h1
    · have h1 := congrArg ex (s₂ (splitTorus _ Y) (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b)
        (SplitTorus.torusMap _ c))
      simpa only [pt_torusMap, ex_app] using h1
    · have h1 := congrArg ex (co (splitTorus _ Y) (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b)
        (SplitTorus.torusMap _ c) (SplitTorus.torusMap _ d))
      simpa only [← SplitTorus.torusMap_add, pt_torusMap, map_mul, ex_app] using h1
  obtain ⟨g', hg', hD⟩ := hcub.exists_del hJ ((ex_mem_cong J D).2 h)
  obtain ⟨g, rfl⟩ := (ex_bijective (A := A) (X := X)).2 g'
  have hD' : D = dif g (SplitTorus.torusMap _ p₁) (SplitTorus.torusMap _ p₂) (SplitTorus.torusMap _ p₃) := by
    apply (ex_bijective (A := A) (X := X × X × X)).1
    rw [hD, ex_dif]
  refine ⟨g, (ex_mem_cong J g).1 hg', fun Z x y u => ?_⟩
  rw [hD', app_dif, pt_p₁, pt_p₂, pt_p₃]

theorem eq_one_of_dif (hJ : IsNilpotent J) (g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ)
    (h : app (bcMap (red J) X) g = 1)
    (hg : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X), dif g x y u = 1) : g = 1 := by
  have h1 : ex g ∈ cong J := (ex_mem_cong J g).2 h
  have h2 : del (ex g) p₁ p₂ p₃ = 1 := by
    rw [← ex_dif, hg, map_one]
  apply (ex_bijective (A := A) (X := X)).1
  rw [eq_one_of_del hJ h1 h2, map_one]

end Affine

end GlobalTheory.CubeLift
end
end
