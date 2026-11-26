module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfAppellHumbert
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionDescendsGaloisCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionDescendsGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.RosatiDescent

open GlobalTheory.CechPic

theorem lift_left_fst {S : Scheme.{0}} {A T : Over S} (f g : T ⟶ A) :
    (lift f g).left ≫ (fst A A).left = f.left :=
  congrArg (fun q => q.left) (lift_fst f g)

theorem lift_left_snd {S : Scheme.{0}} {A T : Over S} (f g : T ⟶ A) :
    (lift f g).left ≫ (snd A A).left = g.left :=
  congrArg (fun q => q.left) (lift_snd f g)

theorem eSec_comp_of_isMonHom {S : Scheme.{0}} {A : Over S} [GrpObj A] (u : A ⟶ A) [IsMonHom u] :
    eSec A ≫ u.left = eSec A := by
  show (η[A] ≫ u).left = η[A].left
  rw [IsMonHom.one_hom]

theorem lbIso_act_descent : ∀ (O : Type) [Ring O] (star : O → O) (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (act : OActN O A) (act₀ : OActN O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ c, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ act.act (star c))).left)) → ∀ c, LBIso (P₀.pull (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left) (P₀.pull (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left) := by
  intro O _ star X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ act act₀ hG hA hA₀ gp hsq hP hP₀ iP _ hact hros c
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have hB : IsAbelianScheme (G2 A₀) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA₀ hA₀
  have h₁ := pull_isLB hP₀ (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left
  have h₂ := pull_isLB hP₀ (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left
  have hN := LB.isLB_div h₂ h₁
  have cN := cls_div h₂ h₁ hN
  rw [cls_pull hP₀, cls_pull hP₀] at cN
  have m₀ := act₀.hom c
  have m₀' := act₀.hom (star c)
  have c₁ : φ₂ ≫ (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left =
      (lift (fst A A ≫ act.act c) (snd A A)).left ≫ φ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = (_ ≫ _) ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst, Category.assoc, hsq.1, ← Category.assoc, lift_left_fst]
      show φ₂ ≫ (fst A₀ A₀).left ≫ (act₀.act c).left = (fst A A).left ≫ (act.act c).left ≫ φ
      rw [reassoc_of% hsq.1, hact]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = (_ ≫ _) ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd, Category.assoc, hsq.2, ← Category.assoc, lift_left_snd]
  have c₂ : φ₂ ≫ (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left =
      (lift (fst A A) (snd A A ≫ act.act (star c))).left ≫ φ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = (_ ≫ _) ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst, Category.assoc, hsq.1, ← Category.assoc, lift_left_fst]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = (_ ≫ _) ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd, Category.assoc, hsq.2, ← Category.assoc, lift_left_snd]
      show φ₂ ≫ (snd A₀ A₀).left ≫ (act₀.act (star c)).left = (snd A A).left ≫ (act.act (star c)).left ≫ φ
      rw [reassoc_of% hsq.2, hact]
  have e₁ : eSec (G2 A₀) ≫ (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left = eSec (G2 A₀) := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = _ ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst, GlobalTheory.SquareDescent.eSec_fst]
      show eSec (G2 A₀) ≫ (fst A₀ A₀).left ≫ (act₀.act c).left = _
      rw [reassoc_of% GlobalTheory.SquareDescent.eSec_fst, eSec_comp_of_isMonHom]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = _ ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd]
  have e₂ : eSec (G2 A₀) ≫ (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left = eSec (G2 A₀) := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = _ ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = _ ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd, GlobalTheory.SquareDescent.eSec_snd]
      show eSec (G2 A₀) ≫ (snd A₀ A₀).left ≫ (act₀.act (star c)).left = _
      rw [reassoc_of% GlobalTheory.SquareDescent.eSec_snd, eSec_comp_of_isMonHom]
  have hPφ : pull φ₂ (cls _ hP₀) = cls _ hP := ((cls_eq_iff hP (pull_isLB hP₀ φ₂)).2 iP).symm
  have hR : pull (lift (fst A A ≫ act.act c) (snd A A)).left (cls _ hP) =
      pull (lift (fst A A) (snd A A ≫ act.act (star c))).left (cls _ hP) :=
    (cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).2 (hros c)
  have hpb := GlobalTheory.SiegelDescent.isPullback_square gp.1 φ₂ hsq
  have z₁ : pull (eSec (G2 A₀)) (cls _ hN) = 0 := by
    rw [cN, map_sub, ← pull_comp, ← pull_comp, e₁, e₂, sub_self]
  have z₂ : pull (pullback.fst (G2 A₀).hom π) (cls _ hN) = 0 := by
    rw [cN, ← hpb.isoPullback_inv_fst, pull_comp, map_sub, ← pull_comp φ₂, ← pull_comp φ₂, c₁, c₂,
      pull_comp, pull_comp, hPφ, hR, sub_self, map_zero]
  obtain ⟨t, ht⟩ := GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns Y X π (G2 A₀) _ hB hN
    inferInstance inferInstance inferInstance
    ((cls_eq_zero_iff (pull_isLB hN _)).1 ((cls_pull hN _ _).trans z₁))
    ((cls_eq_zero_iff (pull_isLB hN _)).1 ((cls_pull hN _ _).trans z₂))
  have h0 : cls _ hN = 0 := (cls_eq_zero_iff hN).2 ⟨t, ht⟩
  rw [cN, sub_eq_zero, ← cls_pull hP₀ _ h₁, ← cls_pull hP₀ _ h₂] at h0
  exact (cls_eq_iff h₁ h₂).1 h0.symm

end GlobalTheory.RosatiDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionDescendsGaloisCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosati_condition_descends_galois_cover : ∀ (O : Type) [Ring O] (star : O → O) (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (act : OActN O A) (act₀ : OActN O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ c, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ act.act (star c))).left)) → ∀ c, LBIso (P₀.pull (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left) (P₀.pull (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left) := by
  first | exact @GlobalTheory.RosatiDescent.lbIso_act_descent | exact GlobalTheory.RosatiDescent.lbIso_act_descent | (intros; apply GlobalTheory.RosatiDescent.lbIso_act_descent; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleTrivialOnAxes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleTrivialOnAxes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

open GlobalTheory.CechPic

namespace GlobalTheory.DescGalRig

variable {S : Scheme.{0}}

theorem one_left (A : Over S) [GrpObj A] : (1 : A ⟶ A).left = A.hom ≫ eSec A := by
  have hu : (toUnit A).left = A.hom := (Category.comp_id _).symm.trans (Over.w (toUnit A))
  show (toUnit A ≫ η[A]).left = _
  rw [Over.comp_left, hu]
  rfl

theorem eSec_lift_one' (A : Over S) [GrpObj A] : eSec A ≫ (lift (𝟙 A) (1 : A ⟶ A)).left = eSec (A ⊗ A) := by
  apply pullback.hom_ext
  · change eSec A ≫ (lift (𝟙 A) (1 : A ⟶ A)).left ≫ (fst A A).left = eSec (A ⊗ A) ≫ (fst A A).left
    show (η[A] ≫ lift (𝟙 A) (1 : A ⟶ A) ≫ fst A A).left = (η[A ⊗ A] ≫ fst A A).left
    simp [Hom.one_def]
  · change eSec A ≫ (lift (𝟙 A) (1 : A ⟶ A)).left ≫ (snd A A).left = eSec (A ⊗ A) ≫ (snd A A).left
    show (η[A] ≫ lift (𝟙 A) (1 : A ⟶ A) ≫ snd A A).left = (η[A ⊗ A] ≫ snd A A).left
    simp [Hom.one_def]

variable {X Y : Scheme.{0}}

theorem one_left_comm {π : X ⟶ Y} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    (gp : IsGrpPullback A A₀ π φ) : (1 : A ⟶ A).left ≫ φ = φ ≫ (1 : A₀ ⟶ A₀).left := by
  rw [one_left, one_left, Category.assoc, GlobalTheory.PolBaseChange.eSec_comm gp, ← Category.assoc, ← gp.1.w,
    Category.assoc]

theorem lift_one_comm {π : X ⟶ Y} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left} (gp : IsGrpPullback A A₀ π φ) (sq : IsSquare φ φ₂) :
    (lift (1 : A ⟶ A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left := by
  have a₁ := congrArg (fun q => q.left) (lift_fst (1 : A ⟶ A) (𝟙 A))
  have a₂ := congrArg (fun q => q.left) (lift_snd (1 : A ⟶ A) (𝟙 A))
  have b₁ := congrArg (fun q => q.left) (lift_fst (1 : A₀ ⟶ A₀) (𝟙 A₀))
  have b₂ := congrArg (fun q => q.left) (lift_snd (1 : A₀ ⟶ A₀) (𝟙 A₀))
  simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
  apply GlobalTheory.SquareDescent.square_hom_ext A₀
  · rw [Category.assoc, sq.1, ← Category.assoc, a₁, Category.assoc, b₁, one_left_comm gp]
  · rw [Category.assoc, sq.2, ← Category.assoc, a₂, Category.assoc, b₂, Category.id_comp, Category.comp_id]

theorem lift_one_comm' {π : X ⟶ Y} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left} (gp : IsGrpPullback A A₀ π φ) (sq : IsSquare φ φ₂) :
    (lift (𝟙 A) (1 : A ⟶ A)).left ≫ φ₂ = φ ≫ (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left := by
  have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 A) (1 : A ⟶ A))
  have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 A) (1 : A ⟶ A))
  have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 A₀) (1 : A₀ ⟶ A₀))
  have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 A₀) (1 : A₀ ⟶ A₀))
  simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
  apply GlobalTheory.SquareDescent.square_hom_ext A₀
  · rw [Category.assoc, sq.1, ← Category.assoc, a₁, Category.assoc, b₁, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, sq.2, ← Category.assoc, a₂, Category.assoc, b₂, one_left_comm gp]

theorem exists_gen_of_side {π : X ⟶ Y} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {A : Over X} [GrpObj A]
    {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left} {φ₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left}
    {P : LB (A ⊗ A).left} {P₀ : LB (A₀ ⊗ A₀).left} (hG : GlobalTheory.ZM.IsGaloisCover Ga ρ π) (hA₀ : IsAbelianScheme A₀)
    (gp : IsGrpPullback A A₀ π φ) (hP : P.IsLB) (hP₀ : P₀.IsLB) (i : LBIso P (P₀.pull φ₂))
    (h0 : ∃ t : (P₀.pull (eSec (A₀ ⊗ A₀))).Gen, t.IsGen)
    (k : A.left ⟶ (A ⊗ A).left) (k₀ : A₀.left ⟶ (A₀ ⊗ A₀).left) (hk : k ≫ φ₂ = φ ≫ k₀)
    (he : eSec A₀ ≫ k₀ = eSec (A₀ ⊗ A₀)) (hgen : ∃ t : (P.pull k).Gen, t.IsGen) :
    ∃ t : (P₀.pull k₀).Gen, t.IsGen := by
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have hN := LB.isLB_pull hP₀ k₀
  refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns Y X π A₀ _ hA₀ hN
    inferInstance inferInstance inferInstance ?_ ?_
  · obtain ⟨t, ht⟩ := h0
    exact gen_chartPull (chartPullOut P₀ (fun _ : PUnit => k₀) (fun _ => 1) (eSec A₀)
      (fun _ => eSec (A₀ ⊗ A₀)) (fun _ => he.symm)) t ht
  · have hiso : LBIso (P.pull k) ((P₀.pull φ₂).pull k) :=
      i.chartPull (chartPullPull P k) (chartPullPull (P₀.pull φ₂) k)
    have htrans : ∀ {U : Scheme.{0}} {L M : LB U}, L.IsLB → M.IsLB → LBIso L M →
        (∃ t : L.Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen := by
      intro U L M hL hM h H
      obtain ⟨w, hw⟩ := h.chartPull (chartPullId L) (chartPullPull M (𝟙 U))
      obtain ⟨t, ht⟩ := H
      obtain ⟨a, ha⟩ := gen_chartPull (chartPullPull L (𝟙 U)) t ht
      obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hM hL a ha
      exact gen_chartPull (chartPullUnpull M _ (Category.id_comp _)) c hc
    obtain ⟨t, ht⟩ := htrans (LB.isLB_pull hP k) (LB.isLB_pull (LB.isLB_pull hP₀ φ₂) k) hiso hgen
    obtain ⟨u, hu⟩ := gen_chartPull (chartPullIn P₀ (fun _ : PUnit => φ₂) (fun _ => 1) k) t ht
    have hc : pullback.fst A₀.hom π ≫ k₀ = (gp.1.isoPullback.inv ≫ k) ≫ φ₂ := by
      rw [Category.assoc, hk, ← Category.assoc, gp.1.isoPullback_inv_fst]
    apply gen_chartPull (chartPullOut P₀ (fun _ : PUnit => k₀) (fun _ => 1) (pullback.fst A₀.hom π)
      (fun _ => gp.1.isoPullback.inv ≫ (k ≫ φ₂)) (fun _ => by rw [← Category.assoc, ← hc]))
      (LB.pullGen P₀ (fun _ : PUnit => k ≫ φ₂) (fun _ => 1) u gp.1.isoPullback.inv)
    exact DVR.pullGen_isGen _ _ _ u hu _

end GlobalTheory.DescGalRig

theorem GlobalTheory.DescGalRig.exists_gen_lift_of_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → (∃ t : (P₀.pull (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left).Gen, t.IsGen) ∧ (∃ t : (P₀.pull (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left).Gen, t.IsGen) := by
  intro X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ hG _ hA₀ gp sq hP hP₀ i h0 h₁ h₂
  exact ⟨GlobalTheory.DescGalRig.exists_gen_of_side hG hA₀ gp hP hP₀ i h0 _ _ (GlobalTheory.DescGalRig.lift_one_comm gp sq)
      (GlobalTheory.SquareDescent.eSec_lift_one A₀) h₁,
    GlobalTheory.DescGalRig.exists_gen_of_side hG hA₀ gp hP hP₀ i h0 _ _ (GlobalTheory.DescGalRig.lift_one_comm' gp sq)
      (GlobalTheory.DescGalRig.eSec_lift_one' A₀) h₂⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleTrivialOnAxesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_birigidified_bundle_trivial_on_axes : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → (∃ t : (P₀.pull (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left).Gen, t.IsGen) ∧ (∃ t : (P₀.pull (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left).Gen, t.IsGen) := by
  first | exact @GlobalTheory.DescGalRig.exists_gen_lift_of_descent | exact GlobalTheory.DescGalRig.exists_gen_lift_of_descent | (intros; apply GlobalTheory.DescGalRig.exists_gen_lift_of_descent; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedEighthPowerBundleClassEqSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedEighthPowerBundleClassEqSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.SharpBundle

open GlobalTheory.ZH.EndoExtend GlobalTheory.SquareOfGeneric

theorem prod_left_ext {S : Scheme.{0}} {X Y : Over S} {Z : Scheme.{0}} (f g : Z ⟶ (X ⊗ Y).left)
    (h₁ : f ≫ (fst X Y).left = g ≫ (fst X Y).left) (h₂ : f ≫ (snd X Y).left = g ≫ (snd X Y).left) : f = g := by
  apply pullback.hom_ext
  · simpa using h₁
  · simpa using h₂

theorem cls_eq_sum_lam : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : GlobalTheory.ZM.SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀) (y : Sp (FractionRing R) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → ∀ pr : Fin 8 → (A.A ⟶ c.A), LBIso A.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK R)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → cls U.LG.L U.LG.isLB = ∑ a, ∑ b, W a b • lam (cls U₀.LG.L U₀.LG.isLB) (q a) (q b) := by
  intro g n o _ ζ F W R _ _ _ hR D D₀ A A₀ G G₀ _ _ _ _ hG U U₀ y α α₂ hα hαs hαL c φc φ₂ hφ hφs hφL pr hP q hq hqg
  obtain ⟨hno, -, hic, -⟩ := hR.1
  have hS : IsSemiAbelian G := hG
  have := hS.smooth
  have := hS.geomConnected
  have := geometricallyIntegral_of_smooth G.hom
  have := U₀.gen_hom
  have hL := U.LG.isLB
  have hL₀ := U₀.LG.isLB
  have hA := A.isLB
  have hA₀ := A₀.isLB
  have hcP := c.isLB
  have hUP := F.univ.isLB
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have h₃ : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have hn : Geo.Tor.IsNormalScheme (Sp R) := (GlobalTheory.isNormalScheme_iff_pred _).1 inferInstance

  have key : ∀ a b, CechPic.pull U.gen.hom.left (CechPic.pull (lift (pr a) (pr b)).left (cls c.P hcP)) =
      CechPic.pull (pullback.fst G.hom (jK R)) (lam (cls U₀.LG.L hL₀) (q a) (q b)) := by
    intro a b
    have eP : cls c.P hcP = CechPic.pull φ₂ (cls F.univ.P hUP) := (cls_eq_iff hcP (pull_isLB hUP _)).2 hφL
    have eΛ : CechPic.pull α₂ (cls F.univ.P hUP) = lam (cls A₀.L hA₀) (fst A₀.A A₀.A) (snd A₀.A A₀.A) :=
      ((cls_eq_iff (LB.isLB_linComb hA₀ _ _) (pull_isLB hUP _)).2 hαL).symm.trans (cls_cube_two hA₀ _ _ _)
    have eK : (U.gen.hom ≫ lift (pr a) (pr b)).left ≫ φ₂ =
        (lift ((Over.pullback (jK R)).map (q a) ≫ U₀.gen.hom) ((Over.pullback (jK R)).map (q b) ≫ U₀.gen.hom)).left ≫ α₂ := by
      apply GlobalTheory.SharpBundle.prod_left_ext
      · rw [Category.assoc, hφs.1, Category.assoc, hαs.1, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
          ← Over.comp_left, Category.assoc, lift_fst, lift_fst]
        exact (hqg a).symm
      · rw [Category.assoc, hφs.2, Category.assoc, hαs.2, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
          ← Over.comp_left, Category.assoc, lift_snd, lift_snd]
        exact (hqg b).symm
    have hext₀ : CechPic.pull U₀.gen.hom.left (cls A₀.L hA₀) =
        CechPic.pull (pullback.fst G₀.hom (jK R)) (cls U₀.LG.L hL₀) := by
      obtain ⟨w, hw⟩ := U₀.ext
      rw [← cls_pull hL₀ _ (pull_isLB hL₀ _), ← cls_pull hA₀ _ (pull_isLB hA₀ _)]
      exact (cls_eq_iff _ _).2 ⟨w, hw⟩
    rw [← pull_comp, ← Over.comp_left, eP, ← pull_comp, eK, pull_comp, eΛ, pull_lam, lift_fst, lift_snd, ← lam_pull,
      hext₀, lam_pull_fst]
    let hh : Over.mk (((Over.pullback (jK R)).obj G).hom ≫ jK R) ⟶ G :=
      Over.homMk (pullback.fst G.hom (jK R)) pullback.condition
    show _ = CechPic.pull hh.left _
    rw [pull_lam]
    congr 1 <;> ext1 <;> exact pullback.lift_fst _ _ _
  refine pic_ext (jK R) hn G (eSec G) (Over.w η[G]) ?_ ?_
  · have h0 : CechPic.pull (eSec G) (cls U.LG.L hL) = 0 :=
      (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨U.LG.rig, U.LG.rigGen⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h0, map_sum]
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    have := hq a
    have := hq b
    have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ G₀) = η[G₀] := by rw [Hom.one_def]; simp
    rw [map_zsmul]
    show _ • CechPic.pull η[G].left _ = 0
    rw [pull_lam, IsMonHom.one_hom, IsMonHom.one_hom, ← e₁, lam_one_left, smul_zero]
  · have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
        CechPic.pull U.gen.hom.left (cls A.L hA) := by
      obtain ⟨w, hw⟩ := U.ext
      rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
      exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc', (cls_eq_iff hA (LB.isLB_linComb hcP _ _)).2 hP, cls_linComb hcP, map_sum, map_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_zsmul, map_zsmul, key]

end GlobalTheory.SharpBundle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedEighthPowerBundleClassEqSumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedEighthPower_bundleClass_eq_sum : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : GlobalTheory.ZM.SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀) (y : Sp (FractionRing R) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → ∀ pr : Fin 8 → (A.A ⟶ c.A), LBIso A.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK R)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → cls U.LG.L U.LG.isLB = ∑ a, ∑ b, W a b • lam (cls U₀.LG.L U₀.LG.isLB) (q a) (q b) := by
  exact @GlobalTheory.SharpBundle.cls_eq_sum_lam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianVarietyOfHalvedPeriodMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianVarietyOfHalvedPeriodMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HalvedPeriod

open GlobalTheory.CechPic GlobalTheory.Models GlobalTheory.ZM

theorem exists_abelian_of_isPeriod : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D' : PLat O bar) (Q : D'.La →+ (Fin g → ℂ)) (E₁ : LinearMap.BilinForm ℤ D'.La), IsPeriod D' ρ Q → D'.EF = (2 : ℤ) • E₁ → ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (_ : IsCommMonObj A) (act : OActN O A) (P : LB (G2 A).left) (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) ∧ IsExp (𝟙 (Sp ℂ)) e ∧ (∀ z, e z = 1 ↔ z ∈ Q.range) ∧ (∀ (a : O) z, e (ρ a *ᵥ z) = e z ≫ act.act a) ∧ (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) := by
  intro O _ bar g ρ D' Q E₁ hP hE
  obtain ⟨hlin, -, hdisc, hspan, Hm, hHm, hpos, him⟩ := hP
  let Λ : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Q.range
  have hmem : ∀ z, z ∈ Λ ↔ z ∈ Q.range := fun z => Iff.rfl
  have hΛd : DiscreteTopology Λ := hdisc
  have hΛs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ := by
    have e : (Λ : Set (Fin g → ℂ)) = Set.range Q := by
      ext z; exact AddMonoidHom.mem_range
    rw [e]; exact hspan
  let H₁ : Matrix (Fin g) (Fin g) ℂ := (2⁻¹ : ℂ) • Hm
  have hH₁ : H₁.IsHermitian := by
    unfold Matrix.IsHermitian at hHm ⊢
    simp only [H₁, Matrix.conjTranspose_smul, hHm, star_inv₀, star_ofNat]
  have hH₁v : ∀ z w : Fin g → ℂ, z ⬝ᵥ H₁ *ᵥ star w = 2⁻¹ * hermForm Hm z w := fun z w => by
    simp only [H₁, hermForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hH₁pos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁ *ᵥ star z).re := fun z hz => by
    rw [hH₁v]
    have := hpos z hz
    have h2 : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [h2, Complex.re_ofReal_mul]
    positivity
  have hH₁int : ∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ H₁ *ᵥ star l').im = n := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    refine ⟨E₁ x y, ?_⟩
    have h := him x y
    rw [hE] at h
    rw [hH₁v]
    have h2 : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [h2, Complex.im_ofReal_mul, h]
    simp
  obtain ⟨A, _, hA, hdim, M, u, χ, hM, hu, hAH⟩ :=
    GlobalTheory.riemann_polarised_torus g Λ H₁ hΛd hΛs hH₁ hH₁pos hH₁int
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  have hker : ∀ z, u.ex z = 1 ↔ z ∈ Q.range := fun z => (u.ker z).trans (hu z)
  obtain ⟨u', χ', hex, hF'⟩ := GlobalTheory.TorusRM.exists_isFactorAH_lam_diag g A hA M u H₁ χ hM
    (GlobalTheory.TorusRM.isFactorAH_of_isAH hAH)
  have h2H : (2 : ℂ) • H₁ = Hm := by simp only [H₁, smul_smul]; norm_num
  rw [h2H] at hF'
  have hAH' : u'.IsAH Hm χ' := GlobalTheory.TorusRM.isAH_of_isFactorAH hF' (fun z hz => hpos z hz)
  have hker' : ∀ z, z ∈ u'.Λ ↔ z ∈ Q.range := fun z => by rw [← u'.ker, hex, hker]
  have hPLB := GlobalTheory.FullSiegel.isLB_lam hM
  have hΔLB := pull_isLB hPLB (lift (𝟙 A) (𝟙 A)).left

  have hid : IsGrpPullback A A (𝟙 _) (𝟙 A.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl A) (inferInstanceAs (IsMonHom (𝟙 A)))
  have htb := GlobalTheory.TorusTransfer.tangent_bijective u hdim
  have hexp : IsExp (𝟙 (Sp ℂ)) u.ex :=
    GlobalTheory.PointUnif.isExp_push hid u htb.1 htb.2 (MulEquiv.refl _) (fun x => (Category.comp_id _).symm)

  have hρΛ : ∀ a, ∀ x ∈ u.Λ, Matrix.mulVecLin (ρ a) x ∈ u.Λ := by
    intro a x hx
    rw [hu, hmem] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    exact ⟨a • y, by rw [Matrix.mulVecLin_apply, hlin]⟩
  choose ψ hψ hlift using fun a =>
    GlobalTheory.HolUnifEnd.exists_isMonHom_of_map_lattice A g hA hdim M u (Matrix.mulVecLin (ρ a)) (hρΛ a)
  haveI : IsReduced A.left := isReduced_of_smooth_complex _ A.hom hA.smooth
  have hext : ∀ f f' : A ⟶ A, (∀ z, u.ex z ≫ f = u.ex z ≫ f') → f = f' := fun f f' h =>
    GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => by
      obtain ⟨z, rfl⟩ := u.ex_onto x
      exact h z
  let act : OActN O A :=
    { act := ψ
      hom := hψ
      one := hext _ _ fun z => by
        rw [← hlift, map_one, Matrix.mulVecLin_one, LinearMap.id_apply, Category.comp_id]
      mul := fun a b => hext _ _ fun z => by
        rw [← hlift, ← Category.assoc, ← hlift, ← hlift]
        congr 1
        simp only [Matrix.mulVecLin_apply, map_mul, Matrix.mulVec_mulVec]
      add := fun a b => hext _ _ fun z => by
        rw [← hlift, comp_mul, ← hlift, ← hlift, ← u.ex_add]
        congr 1
        simp [Matrix.add_mulVec] }
  refine ⟨A, inferInstance, inferInstance, act, abelian₂ A M, u.ex, hA, hdim, hPLB, ?_, ?_, GlobalTheory.FullSiegel.lam_symm hM,
    GlobalTheory.LefschetzAmple.relAmple_of_isAH g A hA _ u' Hm χ' hΔLB hAH', hexp, hker, fun a z => ?_, ?_⟩
  · exact (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hPLB _)).1
      ((GlobalTheory.FullSiegel.cls_lam_pull hM _ _).trans (lam_one_left _ _))
  · exact (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hPLB _)).1
      ((GlobalTheory.FullSiegel.cls_lam_pull hM _ _).trans (lam_one_right _ _))
  · rw [← Matrix.mulVecLin_apply]; exact hlift a z
  · intro k a b c hk hc
    have h := GlobalTheory.AHWeilAny.weilIs_exp_riemannForm A hA _ hΔLB g u' Hm χ' hAH' k (Q a) (Q b) c hk
      ((hker' _).2 ⟨a, rfl⟩) ((hker' _).2 ⟨b, rfl⟩) (by
        rw [hc]
        have e : (Q a ⬝ᵥ Hm *ᵥ star (Q b)).im = (D'.EF a b : ℝ) := him a b
        rw [e]; push_cast; rfl)
    rw [hex] at h
    exact h

end GlobalTheory.HalvedPeriod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianVarietyOfHalvedPeriodMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianVariety_of_halved_periodMap : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D' : PLat O bar) (Q : D'.La →+ (Fin g → ℂ)) (E₁ : LinearMap.BilinForm ℤ D'.La), IsPeriod D' ρ Q → D'.EF = (2 : ℤ) • E₁ → ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (_ : IsCommMonObj A) (act : OActN O A) (P : LB (G2 A).left) (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) ∧ IsExp (𝟙 (Sp ℂ)) e ∧ (∀ z, e z = 1 ↔ z ∈ Q.range) ∧ (∀ (a : O) z, e (ρ a *ᵥ z) = e z ≫ act.act a) ∧ (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) := by
  first | exact @GlobalTheory.HalvedPeriod.exists_abelian_of_isPeriod | exact GlobalTheory.HalvedPeriod.exists_abelian_of_isPeriod | (intros; apply GlobalTheory.HalvedPeriod.exists_abelian_of_isPeriod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPoincareKernelComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPoincareKernelComplex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.KerPoincare

open GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem lift_mul_lift {T : Over S} (u v u' v' : T ⟶ A) : lift u v * lift u' v' = lift (u * u') (v * v') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.mul_comp, lift_fst, lift_fst, lift_fst]
  · rw [MonObj.mul_comp, lift_snd, lift_snd, lift_snd]

theorem one_eq_lift {T : Over S} : (1 : T ⟶ A ⊗ A) = lift (1 : T ⟶ A) 1 := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.one_comp, lift_fst]
  · rw [MonObj.one_comp, lift_snd]

theorem lam_diag (p : Pic (A ⊗ A).left)
    (hmul : ∀ {T : Over S} (X X' Y : T ⟶ A ⊗ A), lam p (X * X') Y = lam p X Y + lam p X' Y)
    (r₁ : ∀ {T : Over S} (v : T ⟶ A), pull (lift (1 : T ⟶ A) v).left p = 0)
    (r₂ : ∀ {T : Over S} (u : T ⟶ A), pull (lift u (1 : T ⟶ A)).left p = 0)
    {T : Over S} (a b : T ⟶ A) :
    lam (pull (lift (𝟙 A) (𝟙 A)).left p) a b = pull (lift a b).left p + pull (lift b a).left p := by
  rw [lam_pull, comp_lift, comp_lift]
  simp only [Category.comp_id]
  have ha : lift a a = lift a (1 : T ⟶ A) * lift 1 a := by rw [lift_mul_lift, _root_.mul_one, _root_.one_mul]
  have hb : lift b b = lift b (1 : T ⟶ A) * lift 1 b := by rw [lift_mul_lift, _root_.mul_one, _root_.one_mul]
  have hmul' : ∀ (X Y Y' : T ⟶ A ⊗ A), lam p X (Y * Y') = lam p X Y + lam p X Y' := fun X Y Y' ↦ by
    rw [lam_comm, hmul, lam_comm, lam_comm p Y']
  rw [ha, hb, hmul, hmul', hmul']
  simp only [lam, lift_mul_lift, one_eq_lift, _root_.mul_one, _root_.one_mul, r₁, r₂]
  abel

end GlobalTheory.KerPoincare

namespace GlobalTheory.KerPoincare

open GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_pow_eq_one_of_kernel : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB →
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ))
      (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q →
    Submodule.span ℝ (Set.range Q) = ⊤ → (∀ z, e z = 1 ↔ z ∈ Q.range) →
    (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) →
    ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A,
      (∃ t : (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left).Gen, t.IsGen) →
      ∃ k : ℕ, 0 < k ∧ x ^ k = 1 := by
  intro A _ _ g hA hsm P hP hr₁ hr₂ hsym hamp e La _ Q EF he _ _ _ _ x hx
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  obtain ⟨Λ, hd, hf, hk⟩ := GlobalTheory.ExpKernel.kernel_isFullLattice (Sp ℂ) A g hA hsm (𝟙 _) e he
  obtain ⟨L₀, u₀, -⟩ := GlobalTheory.exists_holUnif_of_isExp A g e Λ he hd hf hk
  obtain ⟨u, Hm, χ, -, hAH⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ _ hL
  have pos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ hL hamp g u Hm χ hAH.1 hAH.2.1 hAH.2.2
  obtain ⟨PP, ψ, ρ, N, hN, hψ, hρ, h₁, h₂, h₃⟩ := GlobalTheory.PosAHIsog.exists_isog_principal_lam g A hA _ u Hm χ hL
    (GlobalTheory.TorusRM.isAH_of_isFactorAH hAH pos)
  refine ⟨N * N, Nat.mul_pos hN hN,
    GlobalTheory.KillSquare.pow_sq_eq_one_of_lam_trivial A hA _ hL PP ψ ρ N hψ hρ h₁ h₂ h₃ _ x ?_⟩
  have hG : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hΘ := GlobalTheory.exists_gen_theta_of_isAbelianScheme ℂ (A ⊗ A) hG P hP
  have r₁ : ∀ {T : Over (Sp ℂ)} (v : T ⟶ A), pull (lift (1 : T ⟶ A) v).left (cls P hP) = 0 := fun {T} v ↦ by
    have hv : lift (1 : T ⟶ A) v = v ≫ lift (1 : A ⟶ A) (𝟙 A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    rw [hv, Over.comp_left, pull_comp, ← cls_pull hP _ (pull_isLB hP _),
      (cls_eq_zero_iff (pull_isLB hP _)).2 hr₁, map_zero]
  have r₂ : ∀ {T : Over (Sp ℂ)} (v : T ⟶ A), pull (lift v (1 : T ⟶ A)).left (cls P hP) = 0 := fun {T} v ↦ by
    have hv : lift v (1 : T ⟶ A) = v ≫ lift (𝟙 A) (1 : A ⟶ A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    rw [hv, Over.comp_left, pull_comp, ← cls_pull hP _ (pull_isLB hP _),
      (cls_eq_zero_iff (pull_isLB hP _)).2 hr₂, map_zero]
  have e₀ : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) := by
    rw [← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_iff hP (pull_isLB hP _)).2 hsym
  have hsymm : ∀ {T : Over (Sp ℂ)} (u v : T ⟶ A),
      pull (lift u v).left (cls P hP) = pull (lift v u).left (cls P hP) := fun {T} u v ↦ by
    conv_lhs => rw [e₀]
    rw [← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  have hxA : pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left (cls P hP) = 0 := by
    rw [← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_zero_iff _).2 hx
  refine (cls_eq_zero_iff (pull_isLB (LB.isLB_linComb hL _ _) _)).1
    ((GlobalTheory.RealMult.Elliptic.cls_pull_lam hL _ _ _).trans ?_)
  rw [cls_pull hP _ hL,
    lam_diag (cls P hP) (fun X X' Y ↦ lam_mul_left hP hΘ X X' Y) r₁ r₂, hsymm, hxA, add_zero]

end GlobalTheory.KerPoincare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPoincareKernelComplexStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_one_of_poincareKernel_complex : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB →
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ))
      (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q →
    Submodule.span ℝ (Set.range Q) = ⊤ → (∀ z, e z = 1 ↔ z ∈ Q.range) →
    (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) →
    ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A,
      (∃ t : (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left).Gen, t.IsGen) →
      ∃ k : ℕ, 0 < k ∧ x ^ k = 1 := by
  first | exact @GlobalTheory.KerPoincare.exists_pow_eq_one_of_kernel | exact GlobalTheory.KerPoincare.exists_pow_eq_one_of_kernel | (intros; apply GlobalTheory.KerPoincare.exists_pow_eq_one_of_kernel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionMatchOfCharacterMapOnTorus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionMatchOfCharacterMapOnTorus
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.HomTorChar

theorem eq_torusMap_of_torusHomOf {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' →+ X)
    (t : splitTorus S X ⟶ splitTorus S X') (ht : GlobalTheory.Mum.Two.TorusHomOf h t) : t = GlobalTheory.SplitTorus.torusMap S h := by
  refine (GlobalTheory.SplitTorus.eq_torusMap_iff t h).2 fun b => ?_
  have e := congrArg Units.val (ht b)
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' b)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' b).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [this, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val] at e
  exact e

theorem torMatch_of_onTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (p : G ⟶ G₀), IsMonHom p → ∀ h : D₀.toPre.X →+ D.toPre.X, GlobalTheory.Mum.Two.OnTorus U.toUnifPre U₀.toUnifPre p h → GlobalTheory.Poinc.Eq8.TorMatch U₀ U (RingHom.id R) p.left h := by
  intro R _ _ _ hR D' D A' A G' G _ _ _ _ hG' hG U' U p hpm ρ hon
  have hr : ∀ x ∈ maximalIdeal R ^ (0 + 1), residue R x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hp := isGrpPullback_pullback G (spMap (residue R))
  have hp' := isGrpPullback_pullback G' (spMap (residue R))
  have e : ((Over.pullback (spMap (residue R))).map p).left ≫ pullback.fst G.hom (spMap (residue R)) =
      pullback.fst G'.hom (spMap (residue R)) ≫ p.left := pullback.lift_fst _ _ _
  have hρ : GlobalTheory.TorusPart.gtTorus (U'.gt 0) hr hp' ≫ (Over.pullback (spMap (residue R))).map p =
      GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hr hp := by
    obtain ⟨t, ht, hi⟩ := hon 0
    have htm := eq_torusMap_of_torusHomOf ρ t ht
    have k := GlobalTheory.TorusPart.isGrpPullback_thickLift hr hp
    have k' := GlobalTheory.TorusPart.isGrpPullback_thickLift hr hp'
    have e' : ((Over.pullback (spMap (residue R))).map p).left ≫ GlobalTheory.TorusPart.thickLift hr hp =
        GlobalTheory.TorusPart.thickLift hr hp' ≫ ((Over.pullback (thick R (maximalIdeal R) 0)).map p).left := by
      apply pullback.hom_ext
      · rw [Category.assoc, GlobalTheory.TorusPart.thickLift_fst, e, Category.assoc]
        simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left, ← Category.assoc, pullback.lift_fst]
      · have w := Over.w ((Over.pullback (spMap (residue R))).map p)
        simp only [GlobalTheory.TorusPart.thickLift]
        rw [Category.assoc, pullback.lift_snd, Category.assoc, ← Category.assoc _ _ (GlobalTheory.TorusPart.thickPt 0 hr), w]
        simp only [Over.pullback_map_left]
        rw [pullback.lift_snd, pullback.lift_snd]
    have hc := GlobalTheory.TorusPart.pullTorus_comp k' k _ _ e' (U'.gt 0).i
    unfold GlobalTheory.TorusPart.gtTorus
    rw [← hc, hi, htm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]
  intro F _ _ i₁ i₂ hF k hk τ τ' q q' a a' hτ'k hττ' hqy hq hq'y hq' ha ha'
  have hi : i₁ = i₂ := Algebra.algebra_ext _ _ fun x =>
    RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors R)
      (j := @algebraMap _ _ _ _ i₁) (k := @algebraMap _ _ _ _ i₂) (RingHom.ext hF)) x
  subst hi
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk
    · exact h
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k hk1
  obtain ⟨s', s1', s2', s3', s4'⟩ := GlobalTheory.ToricTorsionUnif.main R hR G' hG' D' A' U' k hk1
  let ρm := AddMonoidHom.toMultiplicative ρ
  have powc : ∀ {H : Type} [CommGroup H] (f : Multiplicative D'.toPre.X →* H), f ^ k = 1 → (f.comp ρm) ^ k = 1 :=
    fun f hf => MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hf]; rfl
  have hτ : τ = τ'.comp ρm := MonoidHom.ext fun x => hττ' (Multiplicative.toAdd x)
  have hτk : τ ^ k = 1 := by
    rw [hτ]; exact powc τ' hτ'k
  let c : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  rw [s4 F c τ hτk q a rfl hqy hq ha, ← Category.assoc, s4' F c τ' hτ'k q' a' rfl hq'y hq' ha']
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing c
  let φ : R →+* O := c.codRestrict O.toSubring hO
  haveI : IsLocalHom φ := hloc
  have hc : c = O.subtype.comp φ := rfl
  obtain ⟨τO, hτO⟩ := GlobalTheory.ToricTorsionCompare.units_of_pow_eq_one F O _ k hk1 τ' hτ'k
  have hτOk : τO ^ k = 1 := by
    refine MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)
    have := congrArg (fun f => ((f x : Fˣ) : F)) hτ'k
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢
    rw [SubmonoidClass.coe_pow, hτO, this]; rfl
  let τR := τO.comp ρm
  have hτR : τR ^ k = 1 := powc τO hτOk
  have hkO : IsUnit (k : O) := by simpa using hk.map φ
  have hxy : s O φ τR hτR = s' O φ τO hτOk ≫ p := by
    refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hG.smooth O (spMap φ) k hkO _ _ ?_
      (ResidueField O) (residue O) inferInstance ?_
    · rw [s1, ← GlobalTheory.Poinc.HomTor.pow_comp_monHom, s1', MonObj.one_comp]
    · let τ₀ : Multiplicative D'.toPre.X →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp τO
      have h₀ : τ₀ ^ k = 1 := by
        rw [show τ₀ ^ k = (Units.map (residue O).toMonoidHom).comp (τO ^ k) by ext x; simp [τ₀]]
        rw [hτOk]; ext; simp
      let τ₁ := τ₀.comp ρm
      have h₁ : τ₁ ^ k = 1 := powc τ₀ h₀
      let z : Over.mk (spMap (ResidueField.map φ)) ⟶ splitTorus (Sp (ResidueField R)) D'.toPre.X :=
        (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
          ((Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom.toMonoidHom).comp τ₀)
      have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ₀ (Multiplicative.ofAdd χ)) := fun χ => by
        simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]; rfl
      have hz₁ : ∀ χ, GlobalTheory.UU.chV (z ≫ GlobalTheory.SplitTorus.torusMap _ ρ) χ = unitOn (τ₁ (Multiplicative.ofAdd χ)) :=
        fun χ => by
          apply Units.ext
          rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq,
            GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val,
            ← GlobalTheory.UU.chV_val, hz]
          rfl
      have hres : (residue O).comp φ = (ResidueField.map φ).comp (residue R) := by
        ext r; simp [ResidueField.map_residue]
      rw [Over.comp_left, ← Category.assoc,
        ← s2 O _ φ ((residue O).comp φ) (residue O) τR hτR τ₁ h₁ rfl (fun χ => rfl),
        ← s2' O _ φ ((residue O).comp φ) (residue O) τO hτOk τ₀ h₀ rfl (fun χ => rfl),
        s3 _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp τ₁ h₁ _ hres hz₁,
        s3' _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp' τ₀ h₀ z hres hz,
        Category.assoc z, ← hρ, Category.assoc _ _ p.left, ← e]
      simp only [Over.comp_left, Category.assoc]
  rw [s2 O F φ c O.subtype τR hτR τ hτk hc (fun χ => by simp [τR, hτ, hτO]),
    s2' O F φ c O.subtype τO hτOk τ' hτ'k hc (fun χ => by simp [hτO]), hxy, Over.comp_left, Category.assoc]

end GlobalTheory.Poinc.HomTorChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionMatchOfCharacterMapOnTorusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricTorsionMatch_of_characterMap_on_torus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (p : G ⟶ G₀), IsMonHom p → ∀ h : D₀.toPre.X →+ D.toPre.X, OnTorus U.toUnifPre U₀.toUnifPre p h → GlobalTheory.Poinc.Eq8.TorMatch U₀ U (RingHom.id R) p.left h := by
  first | exact @GlobalTheory.Poinc.HomTorChar.torMatch_of_onTorus | exact GlobalTheory.Poinc.HomTorChar.torMatch_of_onTorus | (intros; apply GlobalTheory.Poinc.HomTorChar.torMatch_of_onTorus <;> assumption)
end
end
