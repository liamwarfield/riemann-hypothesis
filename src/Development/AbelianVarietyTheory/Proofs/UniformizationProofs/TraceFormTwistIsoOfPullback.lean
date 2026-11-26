module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TraceFormTwistIsoOfPullback
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PsiWZeroPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull GlobalTheory.DegPull

section OnW

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem rel_on (ψW : PsiOn D W) (hW : (W : Set (Spec (CommRingCat.of R))).Nonempty) {K : Type} [Fintype K]
    {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb D.P.L φ ε)) (a b : D.X)
    (h : LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (D.tau a b) (LB.pullGen D.P.L _ _ u (D.xK a)))
      (LB.mulGen D.P.L _ _ _ _ (D.psi a) D.rigK)) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (ψW.tau a b) (LB.pullGen D.P.L _ _ u (cP D (TW W) a).left))
      (LB.mulGen D.P.L _ _ _ _ (ψW.psi a) (D.rigW W)) := by
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨lam, hl⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact jK_mem y W hW), IsOpenImmersion.lift_fac _ _ _⟩
  have hκ : (lam ≫ jK R ∣_ W) ≫ W.ι = jK R := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl, Category.id_comp]
  let κ : TK R ⟶ TW W := Over.homMk (lam ≫ jK R ∣_ W) hκ
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have red : IsReduced (TW W).left := inferInstanceAs (IsReduced W.toScheme)
  refine corr_of_dense D.P.isLB κ.left z (fun V hV => ?_) fun J hJ => ?_
  · have h₁ : jK R z ∈ W.ι ''ᵁ V := jK_mem z _ (hV.image _)
    obtain ⟨y, hy, e⟩ := h₁
    have e' : W.ι y = W.ι (κ.left z) := e.trans (congrArg (fun q => q z) hκ).symm
    rw [← W.ι.isOpenEmbedding.injective e']
    exact hy
  · have vψ : ∀ χ, val (ψW.psi χ) κ.left z J = val (D.psi χ) (𝟙 _) z J := fun χ => by
      have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq χ) lam).trans (val_pull hJ _ _ _))
      rw [hl] at this
      exact this
    have vρ : val (D.rigW W) κ.left z J = val D.rigK (𝟙 _) z J := by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [Category.id_comp]
      exact congrArg (fun q => val D.rig q z J) hκ
    have vτ : ∀ a b, val (ψW.tau a b) κ.left z J = val (D.tau a b) (𝟙 _) z J := fun a b => by
      rw [val_tauW ψW _ hJ, val_tau _ hJ, vψ, vψ, vψ, vρ]
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ h (𝟙 _)).trans (val_mul hJ _ _ _))
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    rw [vτ, vψ, vρ, ← e]
    refine congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
    refine congrArg (fun q => val u q z J) ?_
    rw [Category.id_comp]
    exact congrArg (fun q => q.left) (comp_cP D κ a)

end OnW

theorem prod_four {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (f : A ⟶ A) (x : T ⟶ A) {U : Type}
    [CommGroup U] (k : (T.left ⟶ A.left) → U) :
    ∏ i : Fin 4, k (x.left ≫ (![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] : Fin 4 → _) i) ^
      (![1, -2, -1, 2] : Fin 4 → ℤ) i =
      k (x * (x ≫ f)).left * (k x.left ^ 2)⁻¹ * (k (x ≫ f).left)⁻¹ * k (1 : T ⟶ A).left ^ 2 := by
  rw [Fin.prod_univ_four]
  show k (x ≫ (𝟙 A * f)).left ^ (1 : ℤ) * k (x ≫ 𝟙 A).left ^ (-2 : ℤ) * k (x ≫ f).left ^ (-1 : ℤ) *
    k (x ≫ 1).left ^ (2 : ℤ) = _
  rw [MonObj.comp_mul, MonObj.comp_one, Category.comp_id, zpow_one, zpow_neg_one, zpow_neg, zpow_ofNat, zpow_ofNat]

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

set_option maxHeartbeats 1000000 in
theorem traceFormTwistIso_of_pullback (hD : IsPullDeg φ D D') {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X]
    (ιD : D.OAct O) (ιD' : D'.OAct O) (hx : ∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y)
    (hact : ∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a))
    (w0 : O) (h : TraceFormTwistIso D ιD w0) : TraceFormTwistIso D' ιD' w0 := by
  obtain ⟨u, hu, hn, hrel⟩ := h
  have gp := pull_grp hD
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  have ha : (ιD'.onB.act w0).left ≫ Φ = Φ ≫ (ιD.onB.act w0).left := by
    have a₂ : ((Over.pullback (specOf φ)).map (ιD.onB.act w0)).left ≫ pullback.fst D.P.A.hom (specOf φ) =
        pullback.fst _ _ ≫ (ιD.onB.act w0).left := pullback.lift_fst _ _ _
    show _ ≫ hD.e.hom.left ≫ _ = (hD.e.hom.left ≫ _) ≫ _
    rw [← Category.assoc, ← Over.comp_left, hact, Over.comp_left, Category.assoc, a₂, Category.assoc]
  have hψ : ∀ k : Fin 4, (![(padd D'.P.A (𝟙 _) (ιD'.onB.act w0)).left, 𝟙 D'.P.A.left, (ιD'.onB.act w0).left,
      (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → _) k ≫ Φ =
      Φ ≫ (![(padd D.P.A (𝟙 _) (ιD.onB.act w0)).left, 𝟙 D.P.A.left, (ιD.onB.act w0).left,
      (toUnit D.P.A ≫ η[D.P.A]).left] : Fin 4 → _) k := by
    have p1 : (pushPt gp.1.w (𝟙 D'.P.A)).left = Φ := Category.id_comp _
    intro k
    fin_cases k
    · have m : pushPt gp.1.w (𝟙 D'.P.A * ιD'.onB.act w0) =
          pushPt gp.1.w (𝟙 D'.P.A) * pushPt gp.1.w (ιD'.onB.act w0) := map_mul (pushHom gp D'.P.A) _ _
      have q : pushPt gp.1.w (ιD'.onB.act w0) = pushPt gp.1.w (𝟙 D'.P.A) ≫ ιD.onB.act w0 :=
        Over.OverMorphism.ext (by rw [Over.comp_left, p1]; exact ha)
      have m' : pushPt gp.1.w (𝟙 D'.P.A * ιD'.onB.act w0) =
          pushPt gp.1.w (𝟙 D'.P.A) ≫ (𝟙 D.P.A * ιD.onB.act w0) := by
        rw [m, q, MonObj.comp_mul, Category.comp_id]
      have := congrArg (fun q => q.left) m'
      simp only [Over.comp_left, p1] at this
      exact this
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact ha
    · have m : pushPt gp.1.w (1 : D'.P.A ⟶ D'.P.A) = pushPt gp.1.w (𝟙 D'.P.A) ≫ (1 : D.P.A ⟶ D.P.A) := by
        rw [MonObj.comp_one]; exact map_one (pushHom gp D'.P.A)
      have := congrArg (fun q => q.left) m
      simp only [Over.comp_left, p1] at this
      exact this
  obtain ⟨u', hu', pmu⟩ := exists_pmaps ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB Φ hψ u hu
  have vu : ∀ {T : Over (Spec (CommRingCat.of R'))} (x : T ⟶ D'.P.A) (z : T.left) J J', Good D.P.L z J →
      Good D'.P.L z J' → ∀ Ω : (T ⟶ D'.P.A) → (T.left.presheaf.stalk z)ˣ,
      (∀ x, Ω x = gw hD.w x.left z (J (x.left ≫ Φ)) (J' x.left)) → val u (x.left ≫ Φ) z J =
        Ω (x * (x ≫ ιD'.onB.act w0)) * (Ω x ^ 2)⁻¹ * (Ω (x ≫ ιD'.onB.act w0))⁻¹ * Ω 1 ^ 2 * val u' x.left z J' :=
    fun x z J J' hJ hJ' Ω hΩ => by
      rw [hΩ, hΩ, hΩ, hΩ]
      exact (pmaps_val hψ pmu x.left z hJ hJ').trans (congrArg₂ (· * ·)
        (prod_four (ιD'.onB.act w0) x (fun q => gw hD.w q z (J (q ≫ Φ)) (J' q))) rfl)
  refine ⟨u', hu', corr_of_val D'.P.isLB fun y J' hJ' => ?_, fun a => corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
    have := ιD'.onB.hom w0
    have e := vu (1 : 𝟙_ _ ⟶ D'.P.A) y J J' hJ hJ' _ (fun _ => rfl)
    have e₁ : (1 : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ D'.P.A).left = eSec D'.P.A := Category.id_comp _
    have b := val_corr hJ hn (specOf φ)
    rw [val_pull hJ, val_one, ← hD.he] at b
    rw [MonObj.one_comp, _root_.mul_one, e₁] at e
    rw [val_pull hJ', val_one, Category.id_comp]
    have e' := congrArg Additive.ofMul (b.symm.trans e)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
    let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ :=
      fun x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)
    have vψ : ∀ χ, val (hD.psiW.psi (hD.xe χ)) hD.g y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) (𝟙 _) y J' :=
      fun χ => val_psiW hD hJ hJ' χ
    have vρ : val (D.rigW hD.W) hD.g y J = Ω 1 * val D'.rigK (𝟙 _) y J' := by
      have pm := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
        (rigPull_le Φ (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
      have a₂ : ((TK R').hom ≫ specOf φ) ≫ eSec D.P.A = (1 : TK R' ⟶ D'.P.A).left ≫ Φ :=
        congrArg (fun q => q.left) (map_one (pushHom gp (TK R'))).symm
      have e := pm _ (TK R').hom y (fun _ => J ((1 : TK R' ⟶ D'.P.A).left ≫ Φ))
        (fun _ => J' (1 : TK R' ⟶ D'.P.A).left) (fun _ => hJ _) (fun _ => hJ' _)
      rw [Fintype.prod_unique, zpow_one] at e
      have b₁ : hD.g ≫ (toUnit (TW hD.W)).left = (TK R').hom ≫ specOf φ := hD.g_comm
      have b₂ : 𝟙 _ ≫ (toUnit (TK R')).left = (TK R').hom := Category.id_comp _
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
      rw [b₁, b₂]
      exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans e
    have cW : hD.g ≫ (cP D (TW hD.W) (hD.xe a)).left = (cP D' (TK R') a).left ≫ Φ := by
      have hx : (cP D' (TK R') a).left ≫ Φ = jK R' ≫ specOf φ ≫ (D.c (hD.xe a)).left := by
        rw [← hD.c_pr a, ← Category.assoc]; rfl
      rw [hx, ← Category.assoc (jK R'), ← hD.g_comm, Category.assoc]; rfl
    have cl : cP D' (TK R') a ≫ ιD'.onB.act w0 = cP D' (TK R') (w0 • a) := by
      rw [cP, cP, ιD'.c_lin, Category.assoc]
    have key := (val_mul hJ _ _ _).symm.trans ((val_corr hJ
      (rel_on hD.psiW ⟨_, (hD.g y).2⟩ u _ _ (hrel (hD.xe a))) hD.g).trans (val_mul hJ _ _ _))
    rw [val_pull hJ, cW, vu (cP D' (TK R') a) y J J' hJ hJ' Ω (fun _ => rfl), cl, val_tauW _ _ hJ, ← hx, ← map_add (f := _),
      vψ, vψ, vψ, vρ, cPoint_add] at key
    refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
    have b : val (LB.pullGen D'.P.L _ _ u' (D'.xK a)) (𝟙 _) y J' = val u' (cP D' (TK R') a).left y J' := by
      rw [val_pull hJ', Category.id_comp]; rfl
    rw [b, val_tau _ hJ']
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul key
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ⊢
    linear_combination (norm := abel) e'

end Pull

end PsiWZeroPull

theorem traceFormTwistIso_of_overPullback : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R')
    (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X]
    [Module O D'.X] (ιD : D.OAct O) (ιD' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) →
    (∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a)) →
    ∀ w0 : O, Geo.Tor.TraceFormTwistIso D ιD w0 → Geo.Tor.TraceFormTwistIso D' ιD' w0 :=
  fun _ _ _ _ _ _ _ _ _ hD _ _ _ _ _ ιD ιD' hx hact w0 h => PsiWZeroPull.traceFormTwistIso_of_pullback hD ιD ιD' hx hact w0 h

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalOfIsPullDeg
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace TauBalPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull

section OnW

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem tauW_bal_corr (ψW : PsiOn D W) (hW : (W : Set (Spec (CommRingCat.of R))).Nonempty)
    {K : Type} [Fintype K] {φ : K → ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left)} {ε : K → ℤ}
    (u : LB.Gen (LB.LinComb D.P.L φ ε)) (a b a' b' y y' : D.X)
    (h : LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau a b) (LB.pullGen D.P.L _ _ u (D.pt2 y y'))) (D.tau a' b')) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (ψW.tau a b)
        (LB.pullGen D.P.L _ _ u (lift (cP D (TW W) y) (cP D (TW W) y')).left)) (ψW.tau a' b') := by
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨lam, hl⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact jK_mem y W hW), IsOpenImmersion.lift_fac _ _ _⟩
  have hκ : (lam ≫ jK R ∣_ W) ≫ W.ι = jK R := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl, Category.id_comp]
  let κ : TK R ⟶ TW W := Over.homMk (lam ≫ jK R ∣_ W) hκ
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have red : IsReduced (TW W).left := inferInstanceAs (IsReduced W.toScheme)
  refine corr_of_dense D.P.isLB κ.left z (fun V hV => ?_) fun J hJ => ?_
  · have h₁ : jK R z ∈ W.ι ''ᵁ V := jK_mem z _ (hV.image _)
    obtain ⟨y, hy, e⟩ := h₁
    have e' : W.ι y = W.ι (κ.left z) := e.trans (congrArg (fun q => q z) hκ).symm
    rw [← W.ι.isOpenEmbedding.injective e']
    exact hy
  · have vψ : ∀ χ, val (ψW.psi χ) κ.left z J = val (D.psi χ) (𝟙 _) z J := fun χ => by
      have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq χ) lam).trans (val_pull hJ _ _ _))
      rw [hl] at this
      exact this
    have vρ : val (D.rigW W) κ.left z J = val D.rigK (𝟙 _) z J := by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [Category.id_comp]
      exact congrArg (fun q => val D.rig q z J) hκ
    have vτ : ∀ a b, val (ψW.tau a b) κ.left z J = val (D.tau a b) (𝟙 _) z J := fun a b => by
      rw [val_tauW ψW _ hJ, val_tau _ hJ, vψ, vψ, vψ, vρ]
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ h (𝟙 _))
    refine (val_mul hJ _ _ _).trans ?_
    rw [vτ, vτ, ← e]
    refine congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
    rw [Category.id_comp, ← Over.comp_left, comp_lift, comp_cP, comp_cP]
    rfl

theorem tauW_bal (ψW : PsiOn D W)
    {K : Type} [Fintype K] {φ : K → ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left)} {ε : K → ℤ}
    (u : LB.Gen (LB.LinComb D.P.L φ ε)) (a b a' b' y y' : D.X)
    (h : LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau a b) (LB.pullGen D.P.L _ _ u (D.pt2 y y'))) (D.tau a' b'))
    {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TW W) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (ψW.tau a b) κ.left z J * val₂ u z J (cP D T y) (cP D T y') = val (ψW.tau a' b') κ.left z J := by
  have := (val_mul hJ _ _ _).symm.trans (val_corr hJ (tauW_bal_corr ψW ⟨_, (κ.left z).2⟩ u a b a' b' y y' h) κ.left)
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
  refine Eq.trans ?_ (val_pull hJ _ _ _).symm
  rw [← Over.comp_left, comp_lift, comp_cP, comp_cP]
  rfl

end OnW

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem push_comp (hD : IsPullDeg φ D D') {f : D.P.A ⟶ D.P.A} {f' : D'.P.A ⟶ D'.P.A}
    (hf : f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f) {T : Over (Sp R')} (x : T ⟶ D'.P.A) :
    pushPt (pull_grp hD).1.w (x ≫ f') = pushPt (pull_grp hD).1.w x ≫ f := by
  refine Over.OverMorphism.ext ?_
  have h₁ : f'.left ≫ hD.e.hom.left = hD.e.hom.left ≫ ((Over.pullback (specOf φ)).map f).left :=
    congrArg (fun q => q.left) hf
  have h₂ : ((Over.pullback (specOf φ)).map f).left ≫ pullback.fst D.P.A.hom (specOf φ) =
      pullback.fst D.P.A.hom (specOf φ) ≫ f.left := pullback.lift_fst _ _ _
  show (x.left ≫ f'.left) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
    (x.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ f.left
  rw [Category.assoc, ← Category.assoc f'.left, h₁]
  simp only [Category.assoc]
  exact congrArg (fun q => x.left ≫ hD.e.hom.left ≫ q) h₂

theorem push_inj (hD : IsPullDeg φ D D') {T : Over (Sp R')} {x y : T ⟶ D'.P.A}
    (h : pushPt (pull_grp hD).1.w x = pushPt (pull_grp hD).1.w y) : x = y :=
  Over.OverMorphism.ext ((pull_grp hD).1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))

theorem val₂_one {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {K : Type} [Fintype K]
    {ψ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb L ψ ε))
    (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (lift η[A] η[A]).left) (LB.oneGen L))
    {T : Over S} {z : T.left} {J} (hJ : Good L z J) : val u (lift (1 : T ⟶ A) (1 : T ⟶ A)).left z J = 1 := by
  have e : lift (1 : T ⟶ A) (1 : T ⟶ A) = toUnit T ≫ lift η[A] η[A] := by rw [comp_lift]; rfl
  have := val_corr hJ h₀ (toUnit T).left
  rw [val_pull hJ, val_one] at this
  rw [e]; exact this

theorem ros_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {f g : D.P.A ⟶ D.P.A} {f' g' : D'.P.A ⟶ D'.P.A}
    [IsMonHom f] [IsMonHom g]
    (hf : f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f)
    (hg : g' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map g)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L))
    (u' : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A f' g') rosatiε)) (hu' : u'.IsGen)
    (h₀' : LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ u' (zero2 D'.P.A)) (LB.oneGen D'.P.L))
    {T : Over (Sp R')} {z : T.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (x y : T ⟶ D'.P.A) :
    val u (lift (pushPt (pull_grp hD).1.w x) (pushPt (pull_grp hD).1.w y)).left z J =
      (∏ i, gw hD.w ((lift x y).left ≫ rosatiφ D'.P.A f' g' i) z
        (J (((lift x y).left ≫ rosatiφ D'.P.A f' g' i) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
        (J' ((lift x y).left ≫ rosatiφ D'.P.A f' g' i)) ^ rosatiε i) * val u' (lift x y).left z J' := by
  have gp := pull_grp hD
  have pm : ∀ {T : Over (Sp R')} (x y : T ⟶ D'.P.A), pushPt gp.1.w (x * y) = pushPt gp.1.w x * pushPt gp.1.w y :=
    fun x y => map_mul (pushHom gp _) x y
  have p1 : ∀ {T : Over (Sp R')}, pushPt gp.1.w (1 : T ⟶ D'.P.A) = 1 := map_one (pushHom gp _)
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB u' hu'
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (D'.P.A ⊗ D'.P.A).left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J = (∏ i, gw hD.w (r ≫ rosatiφ D'.P.A f' g' i) z
        (J ((r ≫ rosatiφ D'.P.A f' g' i) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
        (J' (r ≫ rosatiφ D'.P.A f' g' i)) ^ rosatiε i) * val u' r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
    rw [Category.assoc]
  let m : (D'.P.A ⊗ D'.P.A).left ⟶ (D.P.A ⊗ D.P.A).left :=
    (lift (pushPt gp.1.w (fst D'.P.A D'.P.A)) (pushPt gp.1.w (snd D'.P.A D'.P.A))).left
  have hm : ∀ {T : Over (Sp R')} (x y : T ⟶ D'.P.A),
      (lift x y).left ≫ m = (lift (pushPt gp.1.w x) (pushPt gp.1.w y)).left := fun {T} x y => by
    let ρ : Over.mk (T.hom ≫ spMap φ) ⟶ Over.mk ((D'.P.A ⊗ D'.P.A).hom ≫ spMap φ) :=
      Over.homMk (lift x y).left (by
        show (lift x y).left ≫ (D'.P.A ⊗ D'.P.A).hom ≫ spMap φ = T.hom ≫ spMap φ
        rw [← Category.assoc, Over.w])
    have r : ∀ q : D'.P.A ⊗ D'.P.A ⟶ D'.P.A, ρ ≫ pushPt gp.1.w q = pushPt gp.1.w (lift x y ≫ q) := fun q =>
      Over.OverMorphism.ext (Category.assoc _ _ _).symm
    have : ρ ≫ lift (pushPt gp.1.w (fst D'.P.A D'.P.A)) (pushPt gp.1.w (snd D'.P.A D'.P.A)) =
        lift (pushPt gp.1.w x) (pushPt gp.1.w y) := by rw [comp_lift, r, r, lift_fst, lift_snd]
    exact congrArg (fun q => q.left) this
  let e : 𝟙_ (Over (Sp R')) ⟶ D'.P.A ⊗ D'.P.A := lift 1 1
  have sj : Function.Surjective ((snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2
  have he : e.left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w e
  have key := gen_unique' D.P.isLB (φ := fun i => m ≫ rosatiφ D.P.A f g i) (ε := rosatiε)
    (fun V _ k => by
      have p₁ := prod_ros f g (pushPt gp.1.w (fst D'.P.A D'.P.A)) (pushPt gp.1.w (snd D'.P.A D'.P.A)) k
      have p₂ := prod_ros f' g' (fst D'.P.A D'.P.A) (snd D'.P.A D'.P.A)
        (fun q => k (q ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
      rw [lift_fst_snd, Over.id_left] at p₂
      simp only [Category.id_comp] at p₂
      rw [← push_comp hD hf, ← push_comp hD hg, ← pm, ← pm] at p₁
      exact p₂.trans p₁.symm)
    _ e.left he sj (pullGen_isGen _ _ _ _ hu m) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over (Sp R'))).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
      have p := prod_ros f' g' (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) 1
        (fun q => gw hD.w q y (I (q ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) (I' q))
      have f₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) ≫ f' = 1 :=
        push_inj hD (by rw [push_comp hD hf, p1, MonObj.one_comp])
      have g₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) ≫ g' = 1 :=
        push_inj hD (by rw [push_comp hD hg, p1, MonObj.one_comp])
      rw [f₁, g₁, _root_.mul_one] at p
      refine Eq.trans ?_ ((hv' _ e.left y I I' hI hI').trans (congrArg₂ (· * ·) p (val₂_one u' h₀' hI'))).symm
      refine (val_pull hI _ _ _).trans ?_
      rw [hm, p1]
      refine (val₂_one u h₀ (T := Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ)) hI).trans ?_
      simp) _ (lift x y).left z J hJ
  rw [← hm]
  exact (val_pull hJ _ _ _).symm.trans (key.trans (hv' _ _ z J J' hJ hJ'))

set_option maxHeartbeats 1000000 in
theorem tauBal_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {f g : D.P.A ⟶ D.P.A} {f' g' : D'.P.A ⟶ D'.P.A}
    [IsMonHom f] [IsMonHom g] (hr : RosatiAdj D.P.A D.P.L f g)
    (hf : f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f)
    (hg : g' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map g)
    {a b : D.X → D.X} {a' b' : D'.X → D'.X} (ha : ∀ y, hD.xe (a' y) = a (hD.xe y))
    (hb : ∀ y, hD.xe (b' y) = b (hD.xe y)) (ca : ∀ y, D.c (a y) = D.c y ≫ f) (cb : ∀ y, D.c (b y) = D.c y ≫ g)
    (hB : D.TauBal f g a b) : D'.TauBal f' g' a' b' := by
  intro u' hu' h₀' s s'
  obtain ⟨u, hu, h₀⟩ := exists_ros hG D.P.isAb D.P.isLB f g hr
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  choose J hJ₀ using fun χ : (TK R').left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ : Good D.P.L y J := hJ₀
  have gp := pull_grp hD
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((TK R').hom ≫ spMap φ)
  let κ : T ⟶ TW hD.W := Over.homMk hD.g hD.g_comm
  let β : (TK R' ⟶ D'.P.A) → (T ⟶ D.P.A) := fun x => pushPt gp.1.w x
  have βc : ∀ χ, β (cP D' _ χ) = cP D _ (hD.xe χ) := fun χ => Over.OverMorphism.ext (by
    show ((TK R').hom ≫ (D'.c χ).left) ≫ Φ = ((TK R').hom ≫ spMap φ) ≫ (D.c (hD.xe χ)).left
    rw [Category.assoc, hD.c_pr, Category.assoc])
  have ca' : cP D' (TK R') (a' s) = cP D' (TK R') s ≫ f' := push_inj hD (by
    rw [push_comp hD hf]
    refine (βc _).trans (Eq.trans ?_ (congrArg (· ≫ f) (βc s)).symm)
    rw [ha, cP, ca]; exact (Category.assoc _ _ _).symm)
  have cb' : cP D' (TK R') (b' s') = cP D' (TK R') s' ≫ g' := push_inj hD (by
    rw [push_comp hD hg]
    refine (βc _).trans (Eq.trans ?_ (congrArg (· ≫ g) (βc s')).symm)
    rw [hb, cP, cb]; exact (Category.assoc _ _ _).symm)
  let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ := fun x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)
  let υ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → ((TK R').left.presheaf.stalk y)ˣ := val₂ u (T := T) y J
  have ros : ∀ p q : TK R' ⟶ D'.P.A, υ (β p) (β q) =
      Ω ((p ≫ f') * q) * (Ω (p ≫ f'))⁻¹ * (Ω q)⁻¹ * (Ω (p * (q ≫ g')))⁻¹ * Ω p * Ω (q ≫ g') * val₂ u' y J' p q :=
    fun p q => (ros_pull hG hD hf hg u hu h₀ u' hu' h₀' (T := TK R') hJ hJ' p q).trans
      (congrArg₂ (· * ·) (prod_ros f' g' p q (fun q => gw hD.w q y (J (q ≫ Φ)) (J' q))) rfl)
  have vψ : ∀ χ, val (hD.psiW.psi (hD.xe χ)) hD.g y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) (𝟙 _) y J' :=
    fun χ => val_psiW hD hJ hJ' χ
  have key : val (hD.psiW.tau (a (hD.xe s)) (hD.xe s')) hD.g y J * υ (cP D T (hD.xe s)) (cP D T (hD.xe s')) =
      val (hD.psiW.tau (hD.xe s) (b (hD.xe s'))) hD.g y J :=
    tauW_bal hD.psiW u _ _ _ _ _ _ (hB u hu h₀ _ _) κ hJ
  rw [← βc, ← βc, ros, ← ha, ← hb, val_tauW _ _ hJ, val_tauW _ _ hJ, ← map_add (f := _), ← map_add (f := _),
    vψ, vψ, vψ, vψ, vψ, vψ, cPoint_add, cPoint_add, ca', cb'] at key
  refine (val_mul hJ' _ _ _).trans ?_
  have vu : val (LB.pullGen D'.P.L _ _ u' (D'.pt2 s s')) (𝟙 _) y J' =
      val₂ u' (T := TK R') y J' (cP D' _ s) (cP D' _ s') := by
    rw [val_pull hJ', Category.id_comp]; rfl
  rw [vu, val_tau _ hJ', val_tau _ hJ']
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end Pull

end TauBalPull

theorem tauBal_of_isPullDeg : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (f g : D.P.A ⟶ D.P.A) (f' g' : D'.P.A ⟶ D'.P.A), IsMonHom f → IsMonHom g → RosatiAdj D.P.A D.P.L f g → f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f → g' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map g → ∀ (a b : D.X → D.X) (a' b' : D'.X → D'.X), (∀ y, hD.xe (a' y) = a (hD.xe y)) → (∀ y, hD.xe (b' y) = b (hD.xe y)) → (∀ y, D.c (a y) = D.c y ≫ f) → (∀ y, D.c (b y) = D.c y ≫ g) → D.TauBal f g a b → D'.TauBal f' g' a' b' :=
  fun hG _ _ _ _ _ _ _ _ _ hD _ _ _ _ _ _ hr hf hg _ _ _ _ ha hb ca cb hB =>
    TauBalPull.tauBal_pull hG hD hr hf hg ha hb ca cb hB

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMoveMap
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaSpecialise

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange

section Algebra

variable {S F F' N V V' : Type} [CommRing S] [IsDomain S] [ValuationRing S] [Field F] [Field F']
  [AddCommGroup N] [Module S N] [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F' V']

theorem exists_ratio {fS : S →+* F} {π : S →+* F'} (hf : Function.Injective fS) (mv : N →ₛₗ[fS] V) (mv' : N →ₛₗ[π] V')
    (ind : ∀ (n : ℕ) (c : Fin n → F), (∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) →
      ∀ a : Fin n → N, ∑ i, c i • mv (a i) = 0 → ∀ i, a i = 0)
    {I : Type} (a b : I → N) (l : F) (h : ∀ i, mv (a i) = l • mv (b i)) (ha : ∃ i, mv' (a i) ≠ 0)
    (hb : ∃ i, mv' (b i) ≠ 0) : ∃ l' : F', l' ≠ 0 ∧ ∀ i, mv' (a i) = l' • mv' (b i) := by
  have inj : ∀ x y, mv x = mv y → x = y := fun x y e => sub_eq_zero.1 (ind 1 (fun _ => 1) (fun a ha i => by
    rw [Fin.sum_univ_one, _root_.mul_one] at ha
    rw [Subsingleton.elim i 0]; exact hf (ha.trans (map_zero _).symm)) (fun _ => x - y)
    (by rw [Fin.sum_univ_one, one_smul, map_sub, e, sub_self]) 0)
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  by_cases H : ∀ a : Fin 2 → S, ∑ i, fS (a i) * ![1, -l] i = 0 → ∀ i, a i = 0
  · refine absurd ?_ hi
    have e : a i = 0 := ind 2 _ H ![a i, b i] (by simp [Fin.sum_univ_two, h]) 0
    rw [e, map_zero]
  · push_neg at H
    obtain ⟨u, hu, m, hm⟩ := H
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one, mul_neg] at hu
    have inj' : ∀ x, fS x = 0 → x = 0 := fun x e => hf (e.trans (map_zero _).symm)
    have h1 : u 1 ≠ 0 := fun e => by
      rw [e, map_zero, zero_mul, neg_zero, add_zero] at hu
      fin_cases m
      exacts [hm (inj' _ hu), hm e]
    have h1' : fS (u 1) ≠ 0 := fun e => h1 (inj' _ e)
    obtain ⟨t, ht | ht⟩ := ValuationRing.cond (u 0) (u 1)
    · have h0 : fS (u 0) ≠ 0 := fun e => h1' (by rw [← ht, map_mul, e, zero_mul])
      have e : fS t * l = 1 := mul_left_cancel₀ h0 (by rw [← ht, map_mul] at hu; linear_combination -hu)
      have k : ∀ i, mv' (b i) = π t • mv' (a i) := fun i => by
        rw [← map_smulₛₗ]
        exact congrArg mv' (inj _ _ (by rw [map_smulₛₗ, h, smul_smul, e, one_smul]))
      have p : π t ≠ 0 := fun e => hj (by rw [k, e, zero_smul])
      exact ⟨(π t)⁻¹, inv_ne_zero p, fun i => by rw [k, smul_smul, inv_mul_cancel₀ p, one_smul]⟩
    · have e : fS t = l := mul_left_cancel₀ h1' (by rw [← ht, map_mul] at hu; linear_combination hu)
      have k : ∀ i, mv' (a i) = π t • mv' (b i) := fun i => by
        rw [← map_smulₛₗ]
        exact congrArg mv' (inj _ _ (by rw [map_smulₛₗ, h, e]))
      exact ⟨π t, fun e => hi (by rw [k, e, zero_smul]), k⟩

end Algebra

section Flat

variable {S F : Type} [CommRing S] [CommRing F] {fS : S →+* F} {X Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of S)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom fS))) [Flat π]

theorem fn_indep {U : Y.Opens} (hU : IsAffineOpen U) {n : ℕ} (c : Fin n → F)
    (hc : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) (a : Fin n → FnOver π U)
    (h : ∑ i, c i • pullFn H.w (le_refl (p ⁻¹ᵁ U)) (a i) = 0) (i : Fin n) : a i = 0 := by
  let : Algebra S F := fS.toAlgebra
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := p ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have po' : IsPushout (CommRingCat.ofHom (constHom π U)) (CommRingCat.ofHom fS) (p.app U)
      (CommRingCat.ofHom (constHom π' (p ⁻¹ᵁ U))) := by
    refine po.of_iso (Scheme.ΓSpecIso (.of S)) (Iso.refl _) (Scheme.ΓSpecIso (.of F)) (Iso.refl _) ?_ ?_ ?_ ?_
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
  let : Algebra (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) := (p.app U).hom.toAlgebra
  let : Algebra S (FnOver π' (p ⁻¹ᵁ U)) := ((constHom π' (p ⁻¹ᵁ U)).comp fS).toAlgebra
  have : IsScalarTower S F (FnOver π' (p ⁻¹ᵁ U)) := .of_algebraMap_eq fun r ↦ rfl
  have : IsScalarTower S (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) :=
    .of_algebraMap_eq fun r ↦ (congrArg (fun q => q.hom r) po'.w).symm
  have hpo : Algebra.IsPushout S (FnOver π U) F (FnOver π' (p ⁻¹ᵁ U)) :=
    CommRingCat.isPushout_iff_isPushout.mp po'
  have fl : Module.Flat S (FnOver π U) := by
    have f₁ : RingHom.Flat (π.appLE ⊤ U le_top).hom :=
      HasRingHomProperty.appLE (P := @Flat) π inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    have f₂ : RingHom.Flat (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
    exact f₂.comp f₁
  have li : LinearIndependent S c := Fintype.linearIndependent_iff.2 fun g hg => hc g hg
  have li' := Fintype.linearIndependent_iff.1 (Module.Flat.linearIndependent_one_tmul (S := FnOver π U) li)
  refine li' a (hpo.out.equiv.injective ?_) i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, ← h, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hpo.out.equiv_tmul, one_smul, Algebra.smul_def, Algebra.smul_def, mul_comm]
  congr 1
  show _ = (Y'.presheaf.map (𝟙 _)).hom _
  rw [CategoryTheory.Functor.map_id]; rfl

theorem sec_indep {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} (ε : K → ℤ) {φ' : K → (Y' ⟶ X)}
    (hφ : ∀ k, φ' k = p ≫ φ k) {n : ℕ} (c : Fin n → F)
    (hc : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) (a : Fin n → SecOver π (LB.LinComb L φ ε))
    (h : ∑ i, c i • pullOver L ε H.w hφ (a i) = 0) (i : Fin n) : a i = 0 := by
  refine SecOver.ext _ _ fun (j : K → L.ι) => fn_ext fun y hy => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy (LB.wchart L φ j).isOpen
  have hle : U ≤ LB.wchart L φ j := hle
  have hle' : p ⁻¹ᵁ U ≤ LB.wchart L φ' j := fun z hz => (wchart_eq hφ j).ge (hle hz)
  have e := fn_indep H hU c hc (fun i => resFn π hle (chartLin π (LB.LinComb L φ ε) j (a i))) (by
    have := congrArg (resFn π' hle' ∘ₗ chartLin π' (LB.LinComb L φ' ε) j) h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
    rw [map_smul]
    refine congrArg (c i • ·) (fn_ext fun z hz => ?_)
    exact ((gs_pullFn H.w _ _ _ z hz).trans (gs_res (𝟙 Y' ≫ p) z hle hz _)).trans
      ((gs_res _ z hle' hz _).trans (gs_pullFn H.w _ _ _ z (hle' hz))).symm) i
  exact ((gs_res (𝟙 Y) y hle hyU _).symm.trans ((congrArg (gs (𝟙 Y) y U) e).trans (gs_zero' _ y U hyU))).trans
    (gs_zero' _ y _ hy).symm

end Flat

section Move

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]

def PSec (w : LB.Iso L' (L.pull Φ)) (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (s' : LB.Sec (LB.LinComb L' φ' ε)) (s : LB.Sec (LB.LinComb L φ ε)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
    (∀ κ, Φ (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
    gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
      (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) (s'.f q)

variable {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
  {S F : Type} [CommRing S] [CommRing F] {fS : S →+* F}
  {π : Y ⟶ Spec (CommRingCat.of S)} {π' : Y' ⟶ Spec (CommRingCat.of F)}

theorem exists_moveMap (hL : L.IsLB) (hL' : L'.IsLB) (hw : w.IsGen) (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ)
    (hp : h ≫ π = π' ≫ Spec.map (CommRingCat.ofHom fS)) :
    ∃ mv : SecOver π (LB.LinComb L φ ε) →ₛₗ[fS] SecOver π' (LB.LinComb L' φ' ε),
      ∀ s s', PSec w φ' φ ε h s' s ↔ mv s = s' := by
  have ex := SecPull.existsUnique_secPull _ _ _ _ _ _ _ hL hL' w hw K φ' φ ε h hc
  choose mv hmv using fun s : SecOver π (LB.LinComb L φ ε) => (ex s).exists
  have m : ∀ {Z : Scheme.{0}} {r : Z ⟶ Y'} {z : Z} {p : K → L.ι}, (∀ κ, Φ (φ' κ (r z)) ∈ L.U (p κ)) →
      (r ≫ h) z ∈ LB.wchart L φ p := fun hp => SecPull.mem_wchart_comp hc (Set.mem_iInter.2 hp)
  refine ⟨{ toFun := mv
            map_add' := fun a b => (ex _).unique (hmv _) fun Z r z p q hp hq => ?_
            map_smul' := fun c a => (ex _).unique (hmv _) fun Z r z p q hp₁ hq => ?_ },
    fun s s' => ⟨fun H => (ex s).unique (hmv s) H, fun H => H ▸ hmv s⟩⟩
  · refine (gs_add _ z _ (m hp) _ _).trans (Eq.trans ?_ (congrArg _ (gs_add r z _ (mem_wchart.2 hq) _ _)).symm)
    rw [mul_add]
    exact congrArg₂ (· + ·) (hmv a Z r z p q hp hq) (hmv b Z r z p q hp hq)
  · refine (gs_smul π _ z _ (m hp₁) _ _).trans
      (Eq.trans ?_ (congrArg _ (gs_smul π' r z _ (mem_wchart.2 hq) _ _)).symm)
    rw [mul_left_comm, Category.assoc, hp, ← Category.assoc, constVal_specMap]
    exact congrArg _ (hmv a Z r z p q hp₁ hq)

theorem move_indep (hL : L.IsLB) (hL' : L'.IsLB) (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ)
    (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom fS))) [Flat π]
    (mv : SecOver π (LB.LinComb L φ ε) → SecOver π' (LB.LinComb L' φ' ε)) (hmv : ∀ s, PSec w φ' φ ε h (mv s) s)
    (n : ℕ) (c : Fin n → F) (hi : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0)
    (a : Fin n → SecOver π (LB.LinComb L φ ε)) (e : ∑ i, c i • mv (a i) = 0) (i : Fin n) : a i = 0 := by
  refine sec_indep H ε (φ' := fun κ => h ≫ φ κ) (fun _ => rfl) c hi a (sec_ext' hL fun y J hJ => ?_) i
  choose J' hJ' using fun ψ : Y' ⟶ X' => exists_chart hL' (ψ y)
  have hJ' : Good L' y J' := hJ'
  have e' := congrArg (fun t => sval t (𝟙 _) y J') e
  beta_reduce at e'
  rw [sval_sum' hJ', sval_zero' hJ'] at e'
  rw [sval_sum' hJ, sval_zero' hJ, ← mul_zero (∏ κ, ExpTrans.om w y J J' (𝟙 _ ≫ φ' κ) ^ ε κ).val, ← e',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sval_smul' hJ, sval_smul' hJ', sval_pullOver _ _ _ _ hJ,
    ExpTrans.sec_val w φ' φ ε h hc _ _ (𝟙 _) y (hmv (a i) _ (𝟙 _) y) hJ hJ', mul_left_comm]

end Move

end GlobalTheory.ThetaSpecialise
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkPairingExistsUniqueTorus
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkPairingExistsUniqueTorus
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.QkPairing

theorem cub_comm {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (k : ℕ) (a m b x : A)
    (Sa Sy Say τa τy τay ζ : U) (h₁ : Say * θ a (m ^ k) b = Sa * Sy) (h₂ : τay * θ a (b ^ k) m = τa * τy)
    (h₃ : τy * cubN θ k 1 b m = ζ * (Sy * cubN θ k 1 m b)) :
    cubN θ k a b (x * m) * (θ a (x * m) b)⁻¹ * Sa * (cubN θ k (a * b ^ k) m x * (θ (a * b ^ k) x m)⁻¹ * τay) =
      ζ * (cubN θ k a m (x * b) * (θ a (x * b) m)⁻¹ * τa * (cubN θ k (a * m ^ k) b x * (θ (a * m ^ k) x b)⁻¹ * Say)) := by
  have e₀ := h.N_split k a m b
  have e₁ := h.N_add k a m x b
  have e₂ := h.N_add k a b x m
  have e₃ := h.N_split k (a * m ^ k) b x
  have e₄ := h.N_split k (a * b ^ k) m x
  have e₅ := h.N_split k a m x
  have e₆ := h.N_split k a b x
  have e₇ := h.N_split k a b m
  have e₈ := h.coc a (m ^ k) (b ^ k) x
  have e₉ := h.coc a (b ^ k) (m ^ k) x
  rw [mul_comm (b ^ k), h.s01 (b ^ k)] at e₉
  have f₁ := h.coc x b m a
  have f₂ := h.coc x m b a
  rw [mul_comm m b, h.s01 m b a] at f₂
  rw [h.s12 (x * b), h.s01 (x * b), h.s12 x b a, h.s01 x a b] at f₁
  rw [h.s12 (x * m), h.s01 (x * m), h.s12 x m a, h.s01 x a m] at f₂
  have f₃ : θ b x m = θ m x b := by rw [h.s01 b, h.s12 x, h.s01 x]
  rw [f₃] at e₂
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₀ := E e₀
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄; have a₅ := E e₅; have a₆ := E e₆
  have a₇ := E e₇; have a₈ := E e₈; have a₉ := E e₉; have b₁ := E f₁; have b₂ := E f₂
  have c₁ := E h₁; have c₂ := E h₂; have c₃ := E h₃
  simp only [ofMul_mul, ofMul_inv] at *
  linear_combination (norm := abel) -(a₁ - a₂ + a₃ - a₄ + a₅ - a₆ - a₇ + a₈ - a₉ - b₁ + b₂ + c₁ - c₂ - c₃ + a₀)

theorem exists_const {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {F : Type} [Field F] {K : Type} [Fintype K]
    {φ : K → (Spec (CommRingCat.of F) ⟶ X)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb M φ ε)) (hu : u.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : (Spec (CommRingCat.of F) ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1) :
    ∃ ζ : Fˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ.val) := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => (hF U h).trans (Fintype.prod_empty _).symm) u hu
  have le : (⊤ : (Spec (CommRingCat.of F)).Opens) ≤
      LB.wchart M (PEmpty.elim : PEmpty → (Spec (CommRingCat.of F) ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom (res le (t.s PEmpty.elim)),
    fun Z r z J hJ => ?_⟩
  rw [← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  refine (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
    (congrArg (gs r z ⊤) ?_))
  exact ((Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _).symm

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

def IsRatio (p p' : QkPt D F k) (ζ : F) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) F) (z : T.left) (J), Good D.P.L z J →
    (val (p.g.s p'.y) σ.left z J * cubN (th D z J) k 1 (σ ≫ p'.g.b) (σ ≫ p.g.b)).val =
      gs σ.left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) *
        (val (p'.g.s p.y) σ.left z J * cubN (th D z J) k 1 (σ ≫ p.g.b) (σ ≫ p'.g.b)).val

theorem exists_ratio (p p' : QkPt D F k) : ∃ ζ : Fˣ, IsRatio p p' ζ.val := by
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub 1 p'.g.b p.g.b k
  obtain ⟨N', hN', vN'⟩ := exists_cubN D.cub 1 p.g.b p'.g.b k
  obtain ⟨ζ, hζ⟩ := exists_const D.P.isLB (F := F)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (p.g.s p'.y) N)
      (LB.invGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (p'.g.s p.y) N')))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (p.g.isGen _) hN)
      (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (p'.g.isGen _) hN'))) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 4 ⊕ Fin 8) (K' := Fin 4 ⊕ Fin 8) (U := U) _
        (prod_sum₂ (K := Fin 4) (K' := Fin 8) (U := U) _ (prod_gt p.g.b p'.y h) rfl)
        (prod_neg _ _ (prod_sum₂ (K := Fin 4) (K' := Fin 8) (U := U) _ (prod_gt p'.g.b p.y h) rfl))).trans ?_
      rw [cPoint_y, cPoint_y]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, mul_comm p.g.b p'.g.b]
      module)
  refine ⟨ζ, fun T σ z J hJ => ?_⟩
  have e := hζ _ σ.left z J hJ
  rw [val_mul hJ, val_inv, val_mul hJ, val_mul hJ, vN T σ z J hJ, vN' T σ z J hJ, MonObj.comp_one] at e
  rw [← e, ← Units.val_mul, inv_mul_cancel_right]

theorem weil_of_ratio (hG : GlobalFnsSt) (p p' : QkPt D F k) {ζ : Fˣ} (H : IsRatio p p' ζ.val) :
    WeilQkIs D F k p p' ζ.val := by
  intro w w' hw hw' s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄
  rw [phiRel_iff hG _ _ hw'] at r₁ r₄
  rw [phiRel_iff hG _ _ hw] at r₂ r₃
  rw [isSmul_iff]
  refine fam_ext fun β j => sec_ext_val D.P.isLB (fun y J hJ => ?_) j
  obtain ⟨α, rfl⟩ : ∃ α, α + p'.y + p.y = β := ⟨β - p.y - p'.y, by abel⟩
  have C : IsCub (th D (T := DegPre.BF D F) y J) := isCub_cubV D.cub hJ
  have hy : ∀ q : QkPt D F k, cP D (DegPre.BF D F) q.y = (fst (TF (R := R) F) D.P.A ≫ q.g.b) ^ k := fun q => by
    rw [← comp_cP D (fst (TF (R := R) F) D.P.A), cPoint_y]; exact map_pow (preHom (fst (TF (R := R) F) D.P.A)) _ _
  have e₂ := r₂ (α + p'.y) _ rfl _ (𝟙 _) y J hJ
  have e₁ := r₁ α _ rfl _ (DegPre.trPt D F p.g.b) y J hJ
  have e₄ := r₄ (α + p.y) _ (add_right_comm α p.y p'.y) _ (𝟙 _) y J hJ
  have e₃ := r₃ α _ rfl _ (DegPre.trPt D F p'.g.b) y J hJ
  rw [Category.id_comp, Category.id_comp, Over.id_left, e₁, tr_fst, uVal_tr, uVal_id, val_mul hJ, val_mul hJ,
    cPoint_add, hy] at e₂
  rw [Category.id_comp, Category.id_comp, Over.id_left, e₃, tr_fst, uVal_tr, uVal_id, val_mul hJ, val_mul hJ,
    cPoint_add, hy, tr_comm] at e₄
  have t₁ := gt_mul (fst (TF (R := R) F) D.P.A) hJ p'.g α p.y
  have t₂ := gt_mul (fst (TF (R := R) F) D.P.A) hJ p.g α p'.y
  rw [hy] at t₁ t₂
  have t₃ := H _ (fst (TF (R := R) F) D.P.A) y J hJ
  obtain ⟨c, hc⟩ : ∃ c : ((DegPre.BF D F).left.presheaf.stalk y)ˣ, c.val =
      gs (fst (TF (R := R) F) D.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ.val) :=
    ⟨_, (gs_unit _ y ⊤ trivial (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom ζ)).symm⟩
  rw [← hc, ← Units.val_mul] at t₃
  have key := cub_comm C k _ _ _ (DegPre.prB D F) _ _ _ _ _ _ _ t₁ t₂ (Units.ext t₃)
  rw [sval_smul _ _ _ _ y hJ, Category.id_comp, ← hc, e₂, e₄, _root_.mul_assoc (sval _ _ _ _), _root_.mul_assoc (sval _ _ _ _),
    ← Units.val_mul, ← Units.val_mul, mul_left_comm c.val, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  have key' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at key' ⊢
  linear_combination (norm := abel) key'

theorem tr_inv (m : TF (R := R) F ⟶ D.P.A) : DegPre.trPt D F m⁻¹ ≫ DegPre.trPt D F m = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, tr_fst, Category.id_comp]
  · show (DegPre.trPt D F m⁻¹ ≫ DegPre.trPt D F m) ≫ DegPre.prB D F = 𝟙 _ ≫ DegPre.prB D F
    rw [Category.assoc, tr_pr, MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, _root_.mul_assoc, ← MonObj.comp_mul,
      inv_mul_cancel, MonObj.comp_one, _root_.mul_one, Category.id_comp]

theorem zero_of_phi {p : QkPt D F k} {w : Frm D F k p.g.b} {s t : Fam D F k} (h : PhiVal p w s.s t.s)
    (ht : ∀ β j, (t.s β).f j = 0) (α : D.X) (j) : (s.s α).f j = 0 := by
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  have e := h α _ rfl _ (DegPre.trPt D F p.g.b⁻¹) y J hJ
  rw [tr_inv, UUA.sval_zero_of (ht _) _ y J (hJ.mem _ _)] at e
  rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]
  exact (Units.mul_left_eq_zero _).1 e.symm

theorem weil_unique (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) (hk : 1 ≤ k) (p p' : QkPt D F k) {ζ ζ' : F}
    (h : WeilQkIs D F k p p' ζ) (h' : WeilQkIs D F k p p' ζ') : ζ = ζ' := by
  obtain ⟨w, hw⟩ : ∃ w : Frm D F k p.g.b, w.IsGen := H1.ClosedPointWeilPower.gen_local_linComb D.P.L D.P.isLB _ _
  obtain ⟨w', hw'⟩ : ∃ w : Frm D F k p'.g.b, w.IsGen := H1.ClosedPointWeilPower.gen_local_linComb D.P.L D.P.isLB _ _
  obtain ⟨s, hs⟩ := FamFree.exists_fam_support (D := D) (F := F) hG hT hB hk 0
  obtain ⟨s₁, r₁⟩ := exists_phi hG p' w' hw' hB s
  obtain ⟨s₂, r₂⟩ := exists_phi hG p w hw hB s₁
  obtain ⟨s₃, r₃⟩ := exists_phi hG p w hw hB s
  obtain ⟨s₄, r₄⟩ := exists_phi hG p' w' hw' hB s₃
  have a := fun {c : F} (h : WeilQkIs D F k p p' c) => (isSmul_iff _ _ _).1 (h w w' hw hw' s s₁ s₂ s₃ s₄
    ((phiRel_iff hG _ _ hw' _ _).2 r₁) ((phiRel_iff hG _ _ hw _ _).2 r₂) ((phiRel_iff hG _ _ hw _ _).2 r₃)
    ((phiRel_iff hG _ _ hw' _ _).2 r₄))
  have hne : s₄ ≠ 0 := fun h0 => (hs 0).2 ⟨0, by simp⟩
    (zero_of_phi r₃ (zero_of_phi r₄ fun β j => by rw [h0]; rfl) 0)
  exact smul_left_injective F hne ((a h).symm.trans (a h'))

theorem ratio_tor (p p' : QkPt D F k) (t : Multiplicative D.X →* Fˣ) (hy : p.y = 0) (ht : IsTor t p.g) {ζ : F}
    (H : IsRatio p p' ζ) : ζ = (t (Multiplicative.ofAdd p'.y)).val := by
  let z : (TF (R := R) F).left := (⊥ : PrimeSpectrum F)
  choose J hJ using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
  have e := H _ (𝟙 _) z J hJ
  have e₀ : val (p'.g.s p.y) (𝟙 _) z J = 1 := by
    rw [hy]; exact (val_corr hJ p'.g.s_zero _).trans (val_one _)
  have e₁ : cubN (th D (T := TF (R := R) F) z J) k 1 (𝟙 _ ≫ p'.g.b) (𝟙 _ ≫ p.g.b) = 1 := by
    rw [Category.id_comp p.g.b, ht.1]; exact C.N_one _ _ _
  have e₂ : cubN (th D (T := TF (R := R) F) z J) k 1 (𝟙 _ ≫ p.g.b) (𝟙 _ ≫ p'.g.b) = 1 := by
    rw [Category.id_comp p.g.b, ht.1]; exact Finset.prod_eq_one fun _ _ => C.face₂ _ _
  rw [e₁, e₂, Over.id_left, e₀, _root_.mul_one, _root_.mul_one, Units.val_one, _root_.mul_one, ht.2 _ z J hJ, UT.cst,
    gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial] at e
  exact ((((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙 (TF (R := R) F).left :
    (TF (R := R) F).left ⟶ _).app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)).injective e).symm

end GlobalTheory.QkPairing

theorem GlobalTheory.weilQk_existsUnique : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D.toPre F k, (∃! ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ) ∧ ∀ t, p.y = 0 → IsTor t p.g → WeilQkIs D.toPre F k p p' (t (Multiplicative.ofAdd p'.y)).val := by
  intro hL R _ _ _ I _ D F _ _ _ k hk p p'
  obtain ⟨ζ, hζ⟩ := GlobalTheory.QkPairing.exists_ratio p p'
  have hW := GlobalTheory.QkPairing.weil_of_ratio hL.1.globalFns p p' hζ
  refine ⟨⟨ζ, hW, fun ζ' h => Units.ext (GlobalTheory.QkPairing.weil_unique hL.1.globalFns hL.2.1.secTwist D.tau_bimult hk p p' h hW)⟩,
    fun t hy ht => ?_⟩
  rw [← GlobalTheory.QkPairing.ratio_tor p p' t hy ht hζ]; exact hW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkPairingExistsUniqueTorusStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.weilQk_pairing_existsUnique_torus : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D.toPre F k, (∃! ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ) ∧ ∀ t, p.y = 0 → IsTor t p.g → WeilQkIs D.toPre F k p p' (t (Multiplicative.ofAdd p'.y)).val := by
  first | exact @GlobalTheory.weilQk_existsUnique | exact GlobalTheory.weilQk_existsUnique | (intros; apply GlobalTheory.weilQk_existsUnique <;> assumption)
end
end
