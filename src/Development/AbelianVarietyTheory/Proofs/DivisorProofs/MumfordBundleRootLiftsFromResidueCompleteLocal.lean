module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftSquareZeroOfMumfordBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxisTrivialLineBundleGroupPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxisTrivialLineBundleGroupPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AxisTriv

theorem lift_comp_sq {S T : Scheme.{0}} {A : Over S} {B : Over T} {β : B.left ⟶ A.left}
    {β₂ : (B ⊗ B).left ⟶ (A ⊗ A).left} (hs : IsSquare β β₂) (a b : B ⟶ B) (a' b' : A ⟶ A)
    (ha : a.left ≫ β = β ≫ a'.left) (hb : b.left ≫ β = β ≫ b'.left) :
    (lift a b).left ≫ β₂ = β ≫ (lift a' b').left := by
  have k₁ : (lift a b).left ≫ (fst B B).left = a.left := congrArg (fun z => z.left) (lift_fst a b)
  have k₂ : (lift a' b').left ≫ (fst A A).left = a'.left := congrArg (fun z => z.left) (lift_fst a' b')
  have l₁ : (lift a b).left ≫ (snd B B).left = b.left := congrArg (fun z => z.left) (lift_snd a b)
  have l₂ : (lift a' b').left ≫ (snd A A).left = b'.left := congrArg (fun z => z.left) (lift_snd a' b')
  apply pullback.hom_ext
  · change ((lift a b).left ≫ β₂) ≫ (fst A A).left = (β ≫ (lift a' b').left) ≫ (fst A A).left
    rw [Category.assoc, hs.1, ← Category.assoc, k₁, Category.assoc, k₂, ha]
  · change ((lift a b).left ≫ β₂) ≫ (snd A A).left = (β ≫ (lift a' b').left) ≫ (snd A A).left
    rw [Category.assoc, hs.2, ← Category.assoc, l₁, Category.assoc, l₂, hb]

theorem exists_gen_pull {S T : Scheme.{0}} {A : Over S} {B : Over T} {β : B.left ⟶ A.left}
    {β₂ : (B ⊗ B).left ⟶ (A ⊗ A).left} {P : LB (A ⊗ A).left} (hP : P.IsLB) (a : B ⟶ B ⊗ B) (a' : A ⟶ A ⊗ A)
    (e : a.left ≫ β₂ = β ≫ a'.left) (h : ∃ u : (P.pull a'.left).Gen, u.IsGen) :
    ∃ u : ((P.pull β₂).pull a.left).Gen, u.IsGen := by
  obtain ⟨u, hu⟩ := h
  have i₁ : LBIso ((P.pull β₂).pull a.left) (P.pull (a.left ≫ β₂)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (LB.isLB_pull hP β₂)) a.left
  have i₂ : LBIso ((P.pull a'.left).pull β) (P.pull (β ≫ a'.left)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (LB.isLB_pull hP a'.left)) β
  rw [e] at i₁
  have i := LBIso.trans (LB.isLB_pull (LB.isLB_pull hP _) _) (LB.isLB_pull hP _) (LB.isLB_pull (LB.isLB_pull hP _) _) i₁ i₂.symm
  obtain ⟨w, hw⟩ := i.symm
  obtain ⟨v, hv, -⟩ := GlobalTheory.WtTower.exists_gen_of_iso (LB.isLB_pull (LB.isLB_pull hP _) _) (LB.isLB_pull (LB.isLB_pull hP _) _)
    w hw (pullGenLB u β) (pullGenLB_isGen hu β)
  exact ⟨v, hv⟩

theorem axes_pull : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (G2 A).left), P.IsLB → (∃ u : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, u.IsGen) → (∃ u : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, u.IsGen) → ∀ (t : T ⟶ S) (B : Over T) [GrpObj B] (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left), IsGrpPullback B A t β → IsSquare β β₂ → (∃ u : ((P.pull β₂).pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen) ∧ (∃ u : ((P.pull β₂).pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen) := by
  intro S T A _ P hP h₁ h₂ t B _ β β₂ h hs
  have e₁ := GlobalTheory.PPAS.one_comp_of_isGrpPullback h
  exact ⟨exists_gen_pull hP _ _ (lift_comp_sq hs _ _ _ _ e₁ rfl) h₁,
    exists_gen_pull hP _ _ (lift_comp_sq hs _ _ _ _ rfl e₁) h₂⟩

end GlobalTheory.AxisTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxisTrivialLineBundleGroupPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.axisTrivial_lineBundle_groupPullback : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (G2 A).left), P.IsLB → (∃ u : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, u.IsGen) → (∃ u : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, u.IsGen) → ∀ (t : T ⟶ S) (B : Over T) [GrpObj B] (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left), IsGrpPullback B A t β → IsSquare β β₂ → (∃ u : ((P.pull β₂).pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen) ∧ (∃ u : ((P.pull β₂).pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen) := by
  first | exact @GlobalTheory.AxisTriv.axes_pull | exact GlobalTheory.AxisTriv.axes_pull | (intros; apply GlobalTheory.AxisTriv.axes_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleThickeningSquareTheorem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleThickeningSquareTheorem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

namespace GlobalTheory.TowerStep
variable (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (e : ℕ)

theorem isGrpPullback_thickMap_factor : IsGrpPullback (thickObj R (maximalIdeal R) e B) (thickObj R (maximalIdeal R) (e + 1) B)
    (spMap (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
      R ⧸ maximalIdeal R ^ (e + 1 + 1) →+* R ⧸ maximalIdeal R ^ (e + 1))) (thickMap R (maximalIdeal R) e B) :=
  GlobalTheory.WtTower.isGrpPullback_thickMap (maximalIdeal R) B e

theorem thickMap_fst : thickMap R (maximalIdeal R) e B ≫ pullback.fst B.hom (thick R (maximalIdeal R) (e + 1)) =
    pullback.fst B.hom (thick R (maximalIdeal R) e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem isAbelianScheme_thickObj (hB : IsAbelianScheme B) : IsAbelianScheme (thickObj R (maximalIdeal R) (e + 1) B) :=
  GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B (thick R (maximalIdeal R) (e + 1)))

theorem exists_isSquare_thickMap : ∃ i₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left,
    IsSquare (thickMap R (maximalIdeal R) e B) i₂ :=
  GlobalTheory.ZM.SiegPull.exists_isSquare (G := thickObj R (maximalIdeal R) (e + 1) B) (G' := thickObj R (maximalIdeal R) e B)
    (f := thickTrans R (maximalIdeal R) e) (pullback.lift_snd _ _ _)

theorem ker_factor_sq {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ^ 2 = 0 := by
  have hle : RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ≤
      (I ^ (e + 1)).map (Ideal.Quotient.mk _) := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.mem_map_of_mem _ hx
  refine le_bot_iff.1 ((Ideal.pow_right_mono hle _).trans ?_)
  rw [← Ideal.map_pow, ← pow_mul, le_bot_iff, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact Ideal.pow_le_pow_right (by omega)

theorem isSquare_fst_comp {i₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left}
    {b₂' : (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left ⟶ (G2 B).left}
    (si : IsSquare (thickMap R (maximalIdeal R) e B) i₂)
    (sb : IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) (e + 1))) b₂') :
    IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) e)) (i₂ ≫ b₂') := by
  have h := GlobalTheory.ZM.SiegPull.isSquare_comp si sb
  rwa [thickMap_fst] at h

end GlobalTheory.TowerStep


open GlobalTheory.TowerStep in
theorem GlobalTheory.TowerStep.step : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (P : LB (G2 B).left), P.IsLB → (∃ u : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen) → (∃ u : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen) → ∀ (e : ℕ) (L : LB (thickObj R (maximalIdeal R) e B).left), L.IsLB → (∀ b₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 B).left, IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) e)) b₂ → LBIso (abelian₂ (thickObj R (maximalIdeal R) e B) L) (P.pull b₂)) → ∃ L' : LB (thickObj R (maximalIdeal R) (e + 1) B).left, L'.IsLB ∧ (∀ b₂ : (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left ⟶ (G2 B).left, IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) (e + 1))) b₂ → LBIso (abelian₂ (thickObj R (maximalIdeal R) (e + 1) B) L') (P.pull b₂)) ∧ LBIso (L'.pull (thickMap R (maximalIdeal R) e B)) L := by
  intro R _ _ B _ _ hB P hP h₁ h₂ e L hL hyp
  haveI := GlobalTheory.WtTower.isLocalRing_quotient_pow R e
  haveI := GlobalTheory.WtTower.isLocalRing_quotient_pow R (e + 1)
  have hπ := Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) :
    maximalIdeal R ^ (e + 1 + 1) ≤ maximalIdeal R ^ (e + 1))
  have gp₁ := isGrpPullback_pullback B (thick R (maximalIdeal R) (e + 1))
  have hab₁ := isAbelianScheme_thickObj R B e hB
  have hgp := isGrpPullback_thickMap_factor R B e
  obtain ⟨b₂', sb⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare gp₁.1.w
  obtain ⟨i₂, si⟩ := exists_isSquare_thickMap R B e
  have s₀ := isSquare_fst_comp R B e si sb
  have hP' : (P.pull b₂').IsLB := pull_isLB hP _
  have hLam : (abelian₂ (thickObj R (maximalIdeal R) e B) L).IsLB := DVR.linComb_isLB _ hL _ _
  have k : LBIso (abelian₂ (thickObj R (maximalIdeal R) e B) L) ((P.pull b₂').pull i₂) :=
    LBIso.trans hLam (pull_isLB hP _) (pull_isLB hP' _) (hyp _ s₀)
      (GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GtBaseChange.lbIso_refl hP') i₂).symm
  obtain ⟨L', hL', hLL⟩ := GlobalTheory.T.exists_lineBundle_lift_squareZero_of_mumfordBundle _ _ _ hπ (ker_factor_sq (maximalIdeal R) e) (thickObj R (maximalIdeal R) (e + 1) B)
    (thickObj R (maximalIdeal R) e B) (thickMap R (maximalIdeal R) e B) i₂ hab₁ hgp si (P.pull b₂') L hP' hL k
  obtain ⟨a₁, a₂⟩ := GlobalTheory.T.axisTrivial_lineBundle_groupPullback _ _ B P hP h₁ h₂ (thick R (maximalIdeal R) (e + 1)) (thickObj R (maximalIdeal R) (e + 1) B) _ b₂' gp₁ sb
  have rig := GlobalTheory.T.lineBundleIso_mumfordLambda_of_local_quotient _ _ _ hπ (thickObj R (maximalIdeal R) (e + 1) B) (thickObj R (maximalIdeal R) e B)
    (thickMap R (maximalIdeal R) e B) i₂ hab₁ hgp si (P.pull b₂') hP' a₁ a₂ L' L hL' hL hLL k
  refine ⟨L', hL', fun b₂ hb => ?_, hLL⟩
  rw [GlobalTheory.ZM.SiegPull.isSquare_unique hb sb rfl]
  exact rig
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleThickeningSquareTheoremStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_thickening_square_theorem : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (P : LB (G2 B).left), P.IsLB → (∃ u : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen) → (∃ u : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen) → ∀ (e : ℕ) (L : LB (thickObj R (maximalIdeal R) e B).left), L.IsLB → (∀ b₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 B).left, IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) e)) b₂ → LBIso (abelian₂ (thickObj R (maximalIdeal R) e B) L) (P.pull b₂)) → ∃ L' : LB (thickObj R (maximalIdeal R) (e + 1) B).left, L'.IsLB ∧ (∀ b₂ : (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left ⟶ (G2 B).left, IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) (e + 1))) b₂ → LBIso (abelian₂ (thickObj R (maximalIdeal R) (e + 1) B) L') (P.pull b₂)) ∧ LBIso (L'.pull (thickMap R (maximalIdeal R) e B)) L := by
  first | exact @GlobalTheory.TowerStep.step | exact GlobalTheory.TowerStep.step | (intros; apply GlobalTheory.TowerStep.step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfReductions
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBAlgComplete

open GlobalTheory.CechPic GlobalTheory.ZV

theorem exists_lineBundle_of_reductions : GlobalTheory.Published.FormalAlgebraisation → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProjBy X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → (∀ e, LBIso (N e) ((N (e + 1)).pull (β e))) → ∃ M : LB X.left, M.IsLB ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro hP R _ _ I hI X hX Y β b hb hc N hN hv
  have hpr : IsProper X.hom := isProper_of_isProjBy R _ _ hX
  obtain ⟨H, hH, m, σ, hσ⟩ := hX
  have hA : IsAmpleLB H := isAmpleLB_of_veryAmpleBy hσ
  have hY : ∀ e, IsProper (Y e).hom := fun e => MorphismProperty.of_isPullback (P := @IsProper) (hb e) hpr
  have hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e) := fun e => by
    refine IsPullback.of_right (h₁₂ := b (e + 1)) (h₂₂ := thick R I (e + 1)) (v₁₃ := X.hom) ?_ ?_ (hb (e + 1))
    · rw [hc, thickTrans_comp]
      exact hb e
    · have : Mono (thick R I (e + 1)) := by
        have : IsClosedImmersion (thick R I (e + 1)) :=
          IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
        infer_instance
      rw [← cancel_mono (thick R I (e + 1)), Category.assoc, Category.assoc, thickTrans_comp, ← (hb (e + 1)).w,
        ← Category.assoc, hc, (hb e).w]
  have hL : ∀ e, (H.pull (b e)).IsLB := fun e => LB.isLB_pull hH _
  have hA₀ : IsAmpleLB (H.pull (b 0)) := by
    have : IsClosedImmersion (thick R I 0) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : IsClosedImmersion (b 0) :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hb 0).flip this
    exact hA.pull_of_isClosedImmersion _
  have := hY 0
  obtain ⟨t, ht⟩ := (AmpleDominates.eventually_isAmpleLB (Y 0).hom hA₀ (hN 0)).exists
  have hT : ∀ e, (LB.div (lbPow (H.pull (b e)) t) (N e)).IsLB := fun e =>
    LB.isLB_div (isLB_lbPow (hL e) t) (hN e)
  have eT : ∀ e, cls _ (hT e) = t • CechPic.pull (b e) (cls H hH) - cls _ (hN e) := fun e => by
    rw [cls_div (isLB_lbPow (hL e) t) (hN e), cls_lbPow (hL e), cls_pull hH]
  obtain ⟨X', M, b', hX', hM, -, hb', hc', hM'⟩ := hP.2 R I hI Y β hβ hY
    (fun e => LB.div (lbPow (H.pull (b e)) t) (N e)) hT
    (fun e => (cls_eq_iff (hT e) (LB.isLB_pull (hT (e + 1)) _)).1 (by
      rw [cls_pull (hT (e + 1)), eT, eT, (cls_eq_iff (hN e) (LB.isLB_pull (hN (e + 1)) _)).2 (hv e),
        cls_pull (hN (e + 1)), map_sub, map_nsmul, ← CechPic.pull_comp, hc]))
    ((relAmple_iff_isAmpleLB_of_isAffine (Y 0) (hT 0)).2 ht)
  obtain ⟨g, hg, -⟩ := hP.1.exists_iso hI hb hc hb' hc'
  have hMg : (M.pull g.hom.left).IsLB := LB.isLB_pull hM _
  have hF : (LB.div (lbPow H t) (M.pull g.hom.left)).IsLB := LB.isLB_div (isLB_lbPow hH t) hMg
  refine ⟨_, hF, fun e => (cls_eq_iff (hN e) (LB.isLB_pull hF _)).1 ?_⟩
  have e₁ := (cls_eq_iff (hT e) (LB.isLB_pull hM _)).2 (hM' e)
  rw [eT, cls_pull hM] at e₁
  rw [cls_pull hF, cls_div (isLB_lbPow hH t) hMg, cls_lbPow hH, cls_pull hM, map_sub, map_nsmul,
    ← CechPic.pull_comp, hg, ← e₁, sub_sub_cancel]

end GlobalTheory.LBAlgComplete
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRootLiftsFromResidueCompleteLocal
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

namespace GlobalTheory.PolRootComplete

theorem root_given {S T : Scheme.{0}} {A : Over S} [GrpObj A] {P : LB (G2 A).left} (hP : P.IsLB) {t : T ⟶ S}
    (h : Root A P t) {B : Over T} [GrpObj B] [IsCommMonObj B] {β : B.left ⟶ A.left}
    {β₂ : (G2 B).left ⟶ (G2 A).left} (hβ : IsGrpPullback B A t β) (hsq : IsSquare β β₂) :
    ∃ L : LB B.left, L.IsLB ∧ LBIso (abelian₂ B L) (P.pull β₂) := by
  obtain ⟨C, _, _, c, c₂, hc, hsqc, L, hL, H⟩ := h
  let φ : B.left ⟶ C.left := hc.1.lift β B.hom hβ.1.w
  have hφc : φ ≫ c = β := hc.1.lift_fst _ _ _
  have hφw : φ ≫ C.hom = B.hom ≫ 𝟙 T := (hc.1.lift_snd _ _ _).trans (Category.comp_id _).symm
  have hφ : IsGrpPullback B C (𝟙 T) φ := hc.cancel (hβ.congr (Category.id_comp t).symm hφc.symm) hφw
  obtain ⟨φ₂, hφ₂⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare hφw
  have e : φ₂ ≫ c₂ = β₂ :=
    GlobalTheory.ZM.SiegPull.isSquare_unique (GlobalTheory.ZM.SiegPull.isSquare_comp hφ₂ hsqc) hsq hφc
  have hLφ : (L.pull φ).IsLB := pull_isLB hL φ
  refine ⟨L.pull φ, hLφ, ?_⟩
  have h1 : LBIso (abelian₂ B (L.pull φ)) ((abelian₂ C L).pull φ₂) :=
    GlobalTheory.ZM.SiegPull.lbIso_lam_pull hφ (GlobalTheory.GtBaseChange.lbIso_refl hLφ) hφ₂
  have h2 : LBIso ((abelian₂ C L).pull φ₂) (P.pull (φ₂ ≫ c₂)) := GlobalTheory.ZM.SiegPull.lbIso_pull_comp H φ₂
  rw [e] at h2
  exact LBIso.trans (LB.isLB_linComb hLφ _ _) (pull_isLB (LB.isLB_linComb hL _ _) _) (pull_isLB hP _) h1 h2

theorem root_of_closedFibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (maximalIdeal R) R) (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) (P : LB (G2 B).left) (hP : P.IsLB)
    (g1 : ∃ u : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen)
    (g2 : ∃ u : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen)
    (gamp : RelAmple B (P.pull (lift (𝟙 B) (𝟙 B)).left))
    (h0 : ∃ L₀ : LB (thickObj R (maximalIdeal R) 0 B).left, L₀.IsLB ∧
      ∀ b₂ : (G2 (thickObj R (maximalIdeal R) 0 B)).left ⟶ (G2 B).left,
        IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) 0)) b₂ →
          LBIso (abelian₂ (thickObj R (maximalIdeal R) 0 B) L₀) (P.pull b₂)) :
    ∃ L : LB B.left, L.IsLB ∧ LBIso (abelian₂ B L) P := by
  let Q : ∀ e, LB (thickObj R (maximalIdeal R) e B).left → Prop := fun e L => L.IsLB ∧
    ∀ b₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 B).left,
      IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) e)) b₂ →
        LBIso (abelian₂ (thickObj R (maximalIdeal R) e B) L) (P.pull b₂)
  have step : ∀ e (L : {L // Q e L}), ∃ L' : {L' // Q (e + 1) L'},
      LBIso (L'.1.pull (thickMap R (maximalIdeal R) e B)) L.1 := fun e L => by
    obtain ⟨L', h1', h2', h3'⟩ := GlobalTheory.T.line_bundle_thickening_square_theorem R B hB P hP g1 g2 e L.1 L.2.1 L.2.2
    exact ⟨⟨L', h1', h2'⟩, h3'⟩
  choose F hF using step
  obtain ⟨L₀, hL₀⟩ := h0
  let N : ∀ e, {L // Q e L} := fun e => Nat.rec ⟨L₀, hL₀⟩ (fun e L => F e L) e
  have hN : ∀ e, LBIso ((N (e + 1)).1.pull (thickMap R (maximalIdeal R) e B)) (N e).1 := fun e => hF e (N e)
  have hproj : GlobalTheory.AbLaw.IsProjBy B.hom := GlobalTheory.WtTower.isProjBy_of_relAmple B (pull_isLB hP _) gamp
  obtain ⟨M, hM, HM⟩ := GlobalTheory.LBAlgComplete.exists_lineBundle_of_reductions GlobalTheory.formalAlgebraisation R
    (maximalIdeal R) hR B hproj (fun e => thickObj R (maximalIdeal R) e B)
    (fun e => thickMap R (maximalIdeal R) e B) (fun e => pullback.fst B.hom (thick R (maximalIdeal R) e))
    (fun e => (isGrpPullback_pullback B (thick R (maximalIdeal R) e)).1)
    (fun e => (pullback.lift_fst _ _ _).trans (Category.comp_id _)) (fun e => (N e).1) (fun e => (N e).2.1)
    (fun e => (hN e).symm)
  haveI := GlobalTheory.WtTower.isLocalRing_quotient_pow R 0
  obtain ⟨b₂, hb₂⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare (isGrpPullback_pullback B (thick R (maximalIdeal R) 0)).1.w
  exact ⟨M, hM, GlobalTheory.T.lineBundleIso_mumfordLambda_of_local_quotient R (R ⧸ maximalIdeal R ^ (0 + 1)) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective B (thickObj R (maximalIdeal R) 0 B) (pullback.fst _ _) b₂ hB
    (isGrpPullback_pullback B _) hb₂ P hP g1 g2 M (N 0).1 hM (N 0).2.1 (HM 0).symm ((N 0).2.2 b₂ hb₂)⟩

theorem root_of_residue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ t : Sp R ⟶ S, Root A P (spMap (residue R) ≫ t) → Root A P t := by
  intro S A _ _ hA P hP h1 h2 hamp R _ _ _ hR t hroot
  obtain ⟨B, _, β, hβ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A t
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hβ
  haveI : IsCommMonObj B := hB.comm
  obtain ⟨β₂, hsq⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare hβ.1.w
  obtain ⟨g1, g2⟩ := GlobalTheory.T.axisTrivial_lineBundle_groupPullback S (Sp R) A P hP h1 h2 t B β β₂ hβ hsq
  have gamp := GlobalTheory.T.relAmple_diagonal_pullback_baseChange S (Sp R) A hA P hP hamp t B β β₂ hβ.1 hsq
  have le : maximalIdeal R ≤ maximalIdeal R ^ (0 + 1) := by rw [zero_add, pow_one]
  have ethick : thick R (maximalIdeal R) 0 =
      spMap (Ideal.Quotient.factor le) ≫ spMap (residue R) := by
    simp only [thick, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hres : Root A P (thick R (maximalIdeal R) 0 ≫ t) := by
    rw [ethick, Category.assoc]
    exact hroot.comp hA _
  have hY := isGrpPullback_pullback B (thick R (maximalIdeal R) 0)
  obtain ⟨b₂, hb₂⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare hY.1.w
  obtain ⟨L₀, hL₀, H₀⟩ := root_given hP hres (hY.comp hβ) (GlobalTheory.ZM.SiegPull.isSquare_comp hb₂ hsq)
  obtain ⟨L, hL, HL⟩ := root_of_closedFibre R hR B hB (P.pull β₂) (pull_isLB hP _) g1 g2 gamp
    ⟨L₀, hL₀, fun b₂' hb₂' => by
      have e : b₂' = b₂ := GlobalTheory.ZM.SiegPull.isSquare_unique hb₂' hb₂ rfl
      subst e
      exact LBIso.trans (LB.isLB_linComb hL₀ _ _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) H₀
        (GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.GtBaseChange.lbIso_refl (pull_isLB hP β₂)) b₂').symm⟩
  exact ⟨B, inferInstance, inferInstance, β, β₂, hβ, hsq, L, hL, HL⟩

end GlobalTheory.PolRootComplete
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRootLiftsFromResidueCompleteLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_root_lifts_from_residue_complete_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ t : Sp R ⟶ S, Root A P (spMap (residue R) ≫ t) → Root A P t := by
  first | exact @GlobalTheory.PolRootComplete.root_of_residue | exact GlobalTheory.PolRootComplete.root_of_residue | (intros; apply GlobalTheory.PolRootComplete.root_of_residue <;> assumption)
end
