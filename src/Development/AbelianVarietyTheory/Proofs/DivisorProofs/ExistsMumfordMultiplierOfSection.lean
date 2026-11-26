module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordFormalSectionCoefficientFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplierPowerMulPullbackSmallFamily

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackIntegralExpansionFormalEndomorphis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionPullbackFormalEndomorphismTermwise
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalEndomorphismPullsTorusCoordinateNormalised
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalEndomorphismPullsTorusCoordinateNormalised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem coord_of_formalEnd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (α : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α (h' α))), IsIota u → ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J), Good D.toPre.P.L z J → val ((U.gt e).t α) (x ≫ (b e).left) z J = val ((U.gt e).t (h' α)) x z J * val u (x ≫ (U.gt e).pG.left) z J := by
  intro R _ _ _ _ D a a' h h' hE A G _ _ _ U b ⟨hb, _, hq, ht⟩ α u ⟨hu, hu1⟩ e Z x z J hJ
  obtain ⟨t, ht, hi⟩ := ht e
  have := hb e
  have := (U.gt e).q_hom
  obtain ⟨v, hv, vv⟩ := GlobalTheory.gtCoord_end_ratio_descends R (maximalIdeal R) D.toPre e G (U.gt e) (b e) a h' t
    (hb e) ht hi (hq e) α
  have hA : IsAbelianScheme (thickObj R (maximalIdeal R) e D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  have key := gen_unique D.toPre.P.isLB (thickObj R (maximalIdeal R) e D.toPre.P.A).hom
    (η[thickObj R (maximalIdeal R) e D.toPre.P.A]).left (Over.w _) (GlobalTheory.globalFns_holds _ _ hA).2 hv
    (DVR.pullGen_isGen _ _ _ _ hu (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)))
    (fun y J hJ => by
      have k := vv _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ hJ,
        TorusCoord.val_unit _ _ hJ, _root_.one_mul] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
          thickObj R (maximalIdeal R) e D.toPre.P.A) = η[thickObj R (maximalIdeal R) e D.toPre.P.A] := by
        simp [Hom.one_def]
      rw [o] at k
      exact k.symm.trans ((hu1 _ (thick R (maximalIdeal R) e) y J hJ).symm.trans
        ((congrArg (fun p => val u p y J)
          (UnitValue.eSec_pullback_fst (thick R (maximalIdeal R) e) D.toPre.P.A).symm).trans
          (val_pull hJ _ _ _).symm)))
  refine (vv Z x z J hJ).trans (congrArg (_ * ·) ((key Z _ z J hJ).trans ((val_pull hJ _ _ _).trans ?_)))
  exact congrArg (fun p => val u p z J) (Category.assoc _ _ _)

end GlobalTheory.TwFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalEndomorphismPullsTorusCoordinateNormalisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalEndomorphism_pulls_torusCoordinate_normalisedGenerator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (α : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α (h' α))), IsIota u → ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J), Good D.toPre.P.L z J → val ((U.gt e).t α) (x ≫ (b e).left) z J = val ((U.gt e).t (h' α)) x z J * val u (x ≫ (U.gt e).pG.left) z J := by
  first | exact @GlobalTheory.TwFam.coord_of_formalEnd | exact GlobalTheory.TwFam.coord_of_formalEnd | (intros; apply GlobalTheory.TwFam.coord_of_formalEnd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionPullbackFormalEndomorphismTermwise
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem texp_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (k e : ℕ) (σ : H0 U.LG.L k) (f : ∀ α, D.toPre.SecB k α) (u : ∀ α, LB.Gen (IotaLB D.toPre a α (h' α))) (s : ∀ α, SecT D.toPre a 0 k (h' α)) (τ : SecE U.toUnifPre (b e) 0 k), U.ExpandsAt e k σ f → (∀ α, IsIota (u α)) → (∀ α, IsPullT (u α) (f α) (s α)) → (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J') → TExp U.toUnifPre τ s := by
  intro R _ _ _ hR D a a' h h' hE A G _ _ hG U b hb k e σ f u s τ hσ hu hs hτ S hS Z x z J J' hJ hJ'
  classical
  obtain ⟨S₀, hS₀⟩ := DVR.expandsAt_val U.toUnifPre e k σ f hσ
  have hp : (U.gt e).pG.left = (U.gt e).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) := rfl
  have hc : (b e).left ≫ (U.gt e).pG.left = (U.gt e).pG.left ≫ a.left := by
    have h₁ := congrArg (fun m => m.left) (hb.2.2.1 e)
    have h₂ : ((Over.pullback (thick R (maximalIdeal R) e)).map a).left ≫
        pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
        pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) ≫ a.left := pullback.lift_fst _ _ _
    rw [hp]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))
  have hx : (x ≫ (b e).left) ≫ (U.gt e).pG.left = (x ≫ (U.gt e).pG.left) ≫ a.left := by
    rw [Category.assoc, hc, Category.assoc]
  obtain ⟨z₀, e₀⟩ := hS₀ Z (x ≫ (b e).left) z J hJ
  have e₁ := e₀ (J' (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left)) (hJ' (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left))
  have term : ∀ α, sval (f α) ((x ≫ (b e).left) ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t α) (x ≫ (b e).left) z J).val =
      sval (s α) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (h' α)) x z J).val := fun α => by
    rw [hs α Z _ z J hJ, GlobalTheory.T.formalEndomorphism_pulls_torusCoordinate_normalisedGenerator R hR D a a' h h' hE A G hG U b hb α (u α) (hu α) e Z x z J hJ, hx, Units.val_mul]
    ring
  have l : evalE U.toUnifPre τ x z J J' = ∑ α ∈ S₀, sval (s α) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (h' α)) x z J).val := by
    refine Eq.trans ?_ (e₁.trans (Finset.sum_congr rfl fun α _ => term α))
    rw [evalE, hτ Z x z J' hJ', zpow_zero, _root_.one_mul, zpow_natCast, Category.assoc, Category.assoc,
      sval_of σ _ z J' (fun _ => J' (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left))
        (fun _ => congrArg J' (Category.comp_id _))]
    rfl
  rw [l]
  refine (Finset.sum_subset (Finset.subset_union_left (s₂ := S)) fun α _ hα => ?_).trans
    (Finset.sum_subset (Finset.subset_union_right (s₁ := S₀)) fun α _ hα => ?_).symm
  · rw [← term α, z₀ α hα, zero_mul]
  · have := hS α hα Z (x ≫ (U.gt e).q.left) z J hJ
    rw [hp, ← Category.assoc, this, zero_mul]

end GlobalTheory.TwFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionPullbackFormalEndomorphismTermwiseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_pullback_formal_endomorphism_termwise : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (k e : ℕ) (σ : H0 U.LG.L k) (f : ∀ α, D.toPre.SecB k α) (u : ∀ α, LB.Gen (IotaLB D.toPre a α (h' α))) (s : ∀ α, SecT D.toPre a 0 k (h' α)) (τ : SecE U.toUnifPre (b e) 0 k), U.ExpandsAt e k σ f → (∀ α, IsIota (u α)) → (∀ α, IsPullT (u α) (f α) (s α)) → (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J') → TExp U.toUnifPre τ s := by
  first | exact @GlobalTheory.TwFam.texp_pull | exact GlobalTheory.TwFam.texp_pull | (intros; apply GlobalTheory.TwFam.texp_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackTwistedSectionVanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackTwistedSectionVanishing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem formEq_pull {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (k : ℕ) (α δ : D.X) :
    FormEq (Sum.elim (fun i => a.left ≫ D.famφB α i) (Sum.elim (D.Oφ (𝟙 D.P.A) δ) (D.Oφ a α)))
      (Sum.elim (DegPre.famε k) (Sum.elim Oε Oinvε)) (tφ D a δ) (tε 0 k) := by
  intro U _ h
  have e₁ : a.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left = (padd D.P.A a (toUnit _ ≫ D.c α)).left := by
    rw [← Over.comp_left, padd, padd, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  have e₂ : a.left ≫ (toUnit D.P.A ≫ D.c α).left = (toUnit D.P.A ≫ D.c α).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  have e₃ : a.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (toUnit D.P.A ≫ η[D.P.A]).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, DegPre.famφB,
    DegPre.Oφ, tφ, tε, DegPre.famε, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_succ, e₁, e₂, e₃,
    Category.comp_id, Over.id_left]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_one]
  module

theorem exists_isPullT : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (k : ℕ) (α δ : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α δ)) (f : D.toPre.SecB k α), u.IsGen → ∃ s : SecT D.toPre a 0 k δ, IsPullT u f s ∧ ∀ e, VanMod (maximalIdeal R) f e → Van (maximalIdeal R) s e := by
  intro R _ _ _ _ D a k α δ u f hu
  obtain ⟨s, hs⟩ := exists_sec D.toPre.P.isLB (formEq_pull D.toPre a k α δ) (pullMulSec f a.left u hu)
  have hp : IsPullT u f s := fun Z x z J hJ => (hs Z x z J hJ).trans (sval_pullMulSec f a.left u hu x z hJ)
  refine ⟨s, hp, fun e hb Z x z J hJ => ?_⟩
  obtain ⟨h, hh⟩ : ∃ h : Z ⟶ pullback D.toPre.P.A.hom (thick R (maximalIdeal R) e),
      h ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
        (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) ≫ a.left :=
    ⟨pullback.lift _ (x ≫ pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) e)) (by
      rw [Category.assoc, Over.w, Category.assoc, Category.assoc, pullback.condition]), pullback.lift_fst _ _ _⟩
  have z₁ : sval f ((x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) ≫ a.left) z J = 0 := by
    rw [← hh]
    have hm := hJ.mem (D.toPre.famφB α) (h ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e))
    exact (gs_pull h _ z _ hm _).symm.trans ((congrArg (gs h z _) (hb _)).trans (DVR.gs_zero h z _ hm))
  rw [hp Z _ z J hJ, z₁, zero_mul]

end GlobalTheory.TwFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackTwistedSectionVanishingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullbackTwistedSection_vanishing : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (k : ℕ) (α δ : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α δ)) (f : D.toPre.SecB k α), u.IsGen → ∃ s : SecT D.toPre a 0 k δ, IsPullT u f s ∧ ∀ e, VanMod (maximalIdeal R) f e → Van (maximalIdeal R) s e := by
  first | exact @GlobalTheory.TwFam.exists_isPullT | exact GlobalTheory.TwFam.exists_isPullT | (intros; apply GlobalTheory.TwFam.exists_isPullT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRelationPullbackOfIntegralThetaFunctional
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRelationPullbackOfIntegralThetaFunctional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam.PullRel

variable {R : Type} [CommRing R] [IsDomain R]

theorem prod_tφ (D : DegPre R) (a : D.P.A ⟶ D.P.A) {T : Over (Sp R)} (ρ : T ⟶ D.P.A) (β : D.X) (n j : ℤ)
    {U : Type} [CommGroup U] (hh : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, hh (ρ.left ≫ tφ D a β i) ^ tε n j i = hh ρ.left ^ (n - 1) * hh (DVR.cP D T β * ρ).left *
      (hh (DVR.cP D T β).left)⁻¹ * hh (1 : T ⟶ D.P.A).left * hh (ρ ≫ a).left ^ j := by
  have e₁ : ρ.left ≫ tφ D a β 1 = (DVR.cP D T β * ρ).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (𝟙 D.P.A) (toUnit _ ≫ D.c β)).trans (by
      rw [Category.comp_id, ← DVR.cP, DVR.comp_cP, mul_comm]))
  have e₂ : ρ.left ≫ tφ D a β 2 = (DVR.cP D T β).left := congrArg (fun q => q.left) (DVR.comp_cP D ρ β)
  have e₃ : ρ.left ≫ tφ D a β 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  have e₀ : ρ.left ≫ tφ D a β 0 = ρ.left := Category.comp_id _
  have e₄ : ρ.left ≫ tφ D a β 4 = (ρ ≫ a).left := rfl
  rw [Fin.prod_univ_five, e₀, e₁, e₂, e₃, e₄]
  show _ ^ (n - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ j = _
  rw [zpow_one, zpow_one, zpow_neg_one]

end GlobalTheory.TwFam.PullRel

namespace GlobalTheory.TwFam.PullRel

variable {R : Type} [CommRing R] [IsDomain R]

theorem iota_c (D : DegPre R) (a a' : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X) (hE : EndData D a a' h h') (α mu : D.X)
    (u : LB.Gen (IotaLB D a α (h' α))) (hu : IsIota u) (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J)
    (hJ : Good D.P.L z J) :
    val (D.tau (h mu) α) r z J = val (D.tau mu (h' α)) r z J * val u (r ≫ D.xK mu) z J := by
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨hma, hma', hr, -, hc, hB⟩ := hE
  obtain ⟨t, ht, t₀⟩ := exists_ros hG D.P.isAb D.P.isLB a a' hr
  have cf : ∀ T, DVR.cP D T (h' α) = DVR.cP D T α ≫ a' := fun T => by
    rw [DVR.cP, hc, ← Category.assoc]; rfl
  have key := gen_unique' D.P.isLB (φ := Sum.elim (D.Oφ (𝟙 _) (h' α)) (D.Oφ a α)) (ε := Sum.elim Oε Oinvε)
    (u' := LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ t (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left))
    (fun U _ h => by
      refine (DVR.prod_neg _ _ (prod_ros a a' (𝟙 D.P.A) (DVR.cP D _ α) h)).trans (Eq.symm ?_)
      refine (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) _ h)
        (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D a α h)).trans ?_
      rw [cf, Category.id_comp, _root_.mul_comm (DVR.cP D _ α) a, _root_.mul_comm (DVR.cP D _ α ≫ a') (𝟙 _)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2 hu.1
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)) (fun y I hI => by
      let T : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 _)
      have C : IsCub (cubV D.cub (T := T) y I) := isCub_cubV D.cub hI
      have e := (ros_add D.cub hG D.P.isAb a a' t ht t₀ (T := T) hI 1 1 (DVR.cP D _ α)).1
      rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
      have e' : val₂ t (T := T) y I 1 (DVR.cP D _ α) = 1 := mul_eq_left.1 e.symm
      have o : (1 : T ⟶ D.P.A).left = eSec D.P.A := Category.id_comp _
      have k : eSec D.P.A ≫ (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left = (lift (1 : T ⟶ D.P.A) (DVR.cP D T α)).left := by
        rw [← o, ← Over.comp_left, comp_lift, DVR.comp_cP, Category.comp_id]
      have n := hu.2 _ (𝟙 _) y I hI
      rw [Category.id_comp] at n
      rw [val_inv, val_pull hI, k]
      exact n.trans (inv_eq_one.2 e').symm) Z (r ≫ D.xK mu) z J hJ
  have m : D.xK mu ≫ (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left = D.pt2 mu α := by
    rw [← Over.comp_left, comp_lift, DVR.comp_cP, Category.comp_id]; rfl
  have b := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hB t ht t₀ mu α) r)
  rw [val_pull hJ] at b
  rw [val_inv, val_pull hJ, Category.assoc, m] at key
  rw [key, ← b, mul_inv_cancel_right]

end GlobalTheory.TwFam.PullRel

namespace GlobalTheory.TwFam.PullRel

variable {R : Type} [CommRing R] [IsDomain R]

theorem formEq_pull (D : DegPre R) (a : D.P.A ⟶ D.P.A) (k : ℕ) (mu ν α β β' : D.X)
    (aK : DegPre.BF D (FractionRing R) ⟶ DegPre.BF D (FractionRing R))
    (h₁ : aK ≫ DegPre.prB D (FractionRing R) = DegPre.prB D (FractionRing R) ≫ a)
    (h₂ : aK ≫ DegPre.trF D (FractionRing R) ν ≫ DegPre.prB D (FractionRing R) =
      DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R) ≫ a) :
    FormEq (Sum.elim (Sum.elim (fun i => aK.left ≫ DegPre.deltaφ D (FractionRing R) k α ν i)
        (fun i => (DegPre.prB D (FractionRing R)).left ≫
          Sum.elim (D.Oφ (𝟙 D.P.A) β') (D.Oφ a (α + k • ν)) i))
        (fun i => (DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)).left ≫
          Sum.elim (D.Oφ (𝟙 D.P.A) β) (D.Oφ a α) i))
      (Sum.elim (Sum.elim (DegPre.deltaε k) (Sum.elim Oε Oinvε)) (fun i => - Sum.elim Oε Oinvε i))
      (dφ D a mu β β') (dε 0 k) := by
  intro U _ hh
  have io : ∀ (ρ : DegPre.BF D (FractionRing R) ⟶ D.P.A) (ξ δ : D.X),
      ∏ i, hh (ρ.left ≫ Sum.elim (D.Oφ (𝟙 D.P.A) δ) (D.Oφ a ξ) i) ^ Sum.elim Oε Oinvε i =
        (hh (DVR.cP D _ δ * ρ).left * (hh (DVR.cP D _ δ).left)⁻¹ * (hh ρ.left)⁻¹ *
          hh (1 : DegPre.BF D (FractionRing R) ⟶ D.P.A).left) *
        ((hh (DVR.cP D _ ξ * (ρ ≫ a)).left)⁻¹ * hh (DVR.cP D _ ξ).left * hh (ρ ≫ a).left *
          (hh (1 : DegPre.BF D (FractionRing R) ⟶ D.P.A).left)⁻¹) := fun ρ ξ δ => by
    refine DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ ?_ ?_
    · simp only [Sum.elim_inl, WeightPf.Oφ_comp, Category.comp_id]
      exact GlobalTheory.UT.OLinEnd.prod_Oφ D ρ δ hh
    · simp only [Sum.elim_inr, WeightPf.Oφ_comp]
      exact GlobalTheory.UT.OLinEnd.prod_Oφ_inv D (ρ ≫ a) ξ hh
  have p₁ := DVR.prod_fam D (FractionRing R) aK (α + k • ν) k hh
  have p₂ := DVR.prod_fam D (FractionRing R) (aK ≫ DegPre.trF D (FractionRing R) ν) α k hh
  have q₁ := prod_tφ D a (DegPre.prB D (FractionRing R)) β' 0 k hh
  have q₂ := prod_tφ D a (DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)) β 0 k hh
  rw [h₁] at p₁
  rw [Category.assoc, h₂, ← Category.assoc] at p₂
  simp only [Over.comp_left, Category.assoc] at p₂ q₂
  refine (DVR.prod_sum₂ (K := (Fin 4 ⊕ Fin 4) ⊕ (Fin 4 ⊕ Fin 4)) (K' := Fin 4 ⊕ Fin 4) (U := U) _
    (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
      (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₁ (DVR.prod_neg _ _ p₂)) (io _ _ _))
    (DVR.prod_neg _ _ (io _ _ _))).trans
    (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5) (U := U) _ q₁ (DVR.prod_neg _ _ q₂)).symm)
  simp only [Over.comp_left, Category.assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end GlobalTheory.TwFam.PullRel

namespace GlobalTheory.TwFam.PullRel

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k) (mu α : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α (h' α))) (u' : LB.Gen (IotaLB D.toPre a (α + k • h mu) (h' (α + k • h mu)))) (s : SecT D.toPre a 0 k (h' α)) (s' : SecT D.toPre a 0 k (h' (α + k • h mu))), IsIota u → IsIota u' → IsPullT u (F.f α) s → IsPullT u' (F.f (α + k • h mu)) s' → TRel h mu s s' := by
  intro R _ _ _ _ D a a' h h' hE k F mu α u u' s s' hu hu' hs hs'
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨hma, -, -, hch, -, -⟩ := id hE
  have hL := D.toPre.P.isLB
  obtain ⟨⟨uF, huF, hcF⟩, -⟩ := DVR.gen_fe (D := D.toPre) (F := FractionRing R) hG k (h mu) α
  have feF := (secRel_iff hL _ _ _ _ _ _ _ _ _ uF).1 (F.F.fe (h mu) α uF huF hcF)
  have h1 : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by unfold scal; rw [map_one, map_one]
  have ext : ∀ β (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J →
      sval (F.F.s β) r z J = sval (F.f β) (r ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J := by
    intro β Z r z J hJ
    have e := F.ext β
    rw [h1] at e
    exact (DVR.SectionScalarValuation.secScal_sval e r z hJ).symm
  let aK : DegPre.BF D.toPre (FractionRing R) ⟶ DegPre.BF D.toPre (FractionRing R) :=
    lift (fst _ _) (DegPre.prB D.toPre (FractionRing R) ≫ a)
  have aK_pr : aK ≫ DegPre.prB D.toPre (FractionRing R) = DegPre.prB D.toPre (FractionRing R) ≫ a := lift_snd _ _
  have aK_fst : aK ≫ fst _ _ = fst _ _ := lift_fst _ _
  have cPh : ∀ T, DVR.cP D.toPre T (h mu) = DVR.cP D.toPre T mu ≫ a := fun T => by
    rw [DVR.cP, hch, ← Category.assoc]; rfl
  have trpr : ∀ ν, DegPre.trF D.toPre (FractionRing R) ν ≫ DegPre.prB D.toPre (FractionRing R) =
      DegPre.prB D.toPre (FractionRing R) * DVR.cP D.toPre _ ν := fun ν => by
    rw [DVR.trF_eq, DVR.tr_pr, DVR.comp_cP]
  have M1 : aK ≫ DegPre.trF D.toPre (FractionRing R) (h mu) ≫ DegPre.prB D.toPre (FractionRing R) =
      DegPre.trF D.toPre (FractionRing R) mu ≫ DegPre.prB D.toPre (FractionRing R) ≫ a := by
    haveI := hma
    rw [trpr, MonObj.comp_mul, aK_pr, DVR.comp_cP, ← Category.assoc, trpr, MonObj.mul_comp, cPh]
  haveI := hma
  have z₁ : DegPre.zF D.toPre (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D.toPre (FractionRing R) ≫ DegPre.prB D.toPre (FractionRing R) = 1 := lift_snd _ _
  have M2 : DegPre.zF D.toPre (FractionRing R) ≫ aK = DegPre.zF D.toPre (FractionRing R) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, aK_fst]
    · rw [Category.assoc, aK_pr, ← Category.assoc, z₂, MonObj.one_comp]
  have M3 : DegPre.zF D.toPre (FractionRing R) ≫ DegPre.trF D.toPre (FractionRing R) mu ≫
      DegPre.prB D.toPre (FractionRing R) = DVR.cP D.toPre _ mu := by
    rw [trpr, MonObj.comp_mul, z₂, DVR.comp_cP, _root_.one_mul]
  intro v hv Z x z J hJ
  have wv : ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J →
      val (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ uF aK.left)
        (LB.pullGen _ _ _ u' (DegPre.prB D.toPre (FractionRing R)).left)) (LB.invGen _ _ _ (LB.pullGen _ _ _ u
          (DegPre.trF D.toPre (FractionRing R) mu ≫ DegPre.prB D.toPre (FractionRing R)).left))) x z J =
      val uF (x ≫ aK.left) z J * val u' (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J *
        (val u (x ≫ (DegPre.trF D.toPre (FractionRing R) mu ≫ DegPre.prB D.toPre (FractionRing R)).left) z J)⁻¹ :=
    fun Z x z J hJ => by rw [val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ]
  have key := (gen_unique' hL (formEq_pull D.toPre a k mu (h mu) α (h' α) (h' (α + k • h mu)) aK aK_pr M1)
    (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left (DegPre.zF D.toPre (FractionRing R)).left
    (congrArg (fun q => q.left) z₁) (DVR.surj_appTop D.toPre _ hG) hv.1
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ huF _)
      (DVR.pullGen_isGen _ _ _ _ hu'.1 _)) (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu.1 _)))
    (fun y I hI => by
      have e₁ := val_corr hI hcF (𝟙 _)
      rw [val_pull hI, Category.id_comp] at e₁
      have e₂ := DVR.val_famMult (D := D.toPre) (F := FractionRing R) (𝟙 _) hI k (h mu) α
      rw [Over.id_left, Category.id_comp, DVR.TWM.val_powGen, DVR.TWM.val_powGen] at e₂
      have e₃ : val u' (1 : TF (R := R) (FractionRing R) ⟶ D.toPre.P.A).left y I = 1 :=
        hu'.2 _ (TF (R := R) (FractionRing R)).hom y I hI
      have e₄ := iota_c D.toPre a a' h h' hE α mu u hu _ (jFK (R := R) (FractionRing R)) y I hI
      have e₅ : jFK (R := R) (FractionRing R) ≫ D.toPre.xK mu = (DVR.cP D.toPre (TF (R := R) (FractionRing R)) mu).left :=
        (Category.assoc _ _ _).symm
      rw [wv _ _ y I hI, hv.2 y I hI, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, M2, z₂, M3, e₁, e₂, e₃, e₄, e₅]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module) Z x z J hJ).trans (wv Z x z J hJ)
  have f₁ : (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) ≫ a.left =
      (x ≫ aK.left) ≫ (DegPre.prB D.toPre (FractionRing R)).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, aK_pr]
  have f₂ : ((x ≫ aK.left) ≫ (DegPre.trF D.toPre (FractionRing R) (h mu)).left) ≫ (DegPre.prB D.toPre (FractionRing R)).left =
      (x ≫ (DegPre.trF D.toPre (FractionRing R) mu).left ≫ (DegPre.prB D.toPre (FractionRing R)).left) ≫ a.left := by
    have := congrArg (fun q => x ≫ q.left) M1
    simpa only [Over.comp_left, Category.assoc] using this
  rw [hs' _ _ z J hJ, hs _ _ z J hJ, key, f₁, ← ext _ _ _ z J hJ, feF _ _ z J hJ, ext _ _ _ z J hJ, f₂, Over.comp_left,
    _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_comm (val u _ z J), inv_mul_cancel_right]

end GlobalTheory.TwFam.PullRel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRelationPullbackOfIntegralThetaFunctionalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedRelation_pullback_of_integralThetaFunctionalEquation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k) (mu α : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α (h' α))) (u' : LB.Gen (IotaLB D.toPre a (α + k • h mu) (h' (α + k • h mu)))) (s : SecT D.toPre a 0 k (h' α)) (s' : SecT D.toPre a 0 k (h' (α + k • h mu))), IsIota u → IsIota u' → IsPullT u (F.f α) s → IsPullT u' (F.f (α + k • h mu)) s' → TRel h mu s s' := by
  first | exact @GlobalTheory.TwFam.PullRel.main | exact GlobalTheory.TwFam.PullRel.main | (intros; apply GlobalTheory.TwFam.PullRel.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackIntegralExpansionFormalEndomorphis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem exists_pull_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (k : ℕ) (σ : H0 U.LG.L k) (f : IntFam (maximalIdeal R) D.toPre k), (∀ e, U.ExpandsAt e k σ f.f) → ∃ ρ : ∀ β, SecT D.toPre a 0 k β, Small (maximalIdeal R) (w := id) ρ ∧ TFE h h' ρ ∧ ∀ e, ∃ τ : SecE U.toUnifPre (b e) 0 k, (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J') ∧ TExp U.toUnifPre τ (w := id) ρ := by
  intro R _ _ _ hR D a a' h h' hE A G _ _ hG U b hb k σ f hσ
  choose u hu using GlobalTheory.T.exists_normalisedTwistedIotaGenerator R hR D a a' h h' hE
  choose s hs hv using fun α => GlobalTheory.T.exists_pullbackTwistedSection_vanishing R hR D a k α (h' α) (u α) (f.f α) (hu α).1
  have hsm : Small (maximalIdeal R) (w := fun α => h' α) s := fun e =>
    (f.small e).subset fun α hα hf => hα (hv α e hf)
  obtain ⟨ρ, hρ, hρs⟩ := GlobalTheory.T.exists_adicSum_twistedSectionFamily_tendsToZero R hR D a 0 k _ (fun α => h' α) s hsm
  refine ⟨ρ, hρs, GlobalTheory.T.twistedFunctionalEquation_of_adicSum_termwise R hR D a a' h h' hE 0 k _ (fun α => h' α) s ρ
    (fun mu => Equiv.addRight (k • h mu)) hsm hρ (fun mu i => by simp [shift])
    (fun mu i => GlobalTheory.T.twistedRelation_pullback_of_integralThetaFunctionalEquation R hR D a a' h h' hE k f mu i _ _ _ _ (hu _) (hu _) (hs _) (hs _)), fun e => ?_⟩
  have hL : U.LG.L.IsLB := U.LG.isLB
  have h1 : (LB.oneGen U.LG.L (Y := (thickObj R (maximalIdeal R) e G).left)).IsGen := fun _ _ =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  obtain ⟨τ, hτ⟩ := exists_sec hL (K' := Fin 2)
    (φ' := ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left]) (ε' := ![(0 : ℤ), (k : ℤ)])
    (fun V _ g => by simp [Fintype.prod_sum_type, Fin.prod_univ_two])
    (pullMulSec σ ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (LB.oneGen U.LG.L) h1)
  have key : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' →
      sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J' := fun Z x z J hJ => by
    rw [hτ Z x z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, val_one, Units.val_one, _root_.mul_one]
  exact ⟨τ, key, GlobalTheory.T.twistedExpansion_adicSums_admissibleBase R hR D a A G hG U e (b e) 0 k τ _ (fun α => h' α) s ρ hsm hρ
    (GlobalTheory.T.expansion_pullback_formal_endomorphism_termwise R hR D a a' h h' hE A G hG U b hb k e σ f.f u s τ (hσ e) hu hs key)⟩

end GlobalTheory.TwFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackIntegralExpansionFormalEndomorphisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_integralExpansion_formalEndomorphism : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (k : ℕ) (σ : H0 U.LG.L k) (f : IntFam (maximalIdeal R) D.toPre k), (∀ e, U.ExpandsAt e k σ f.f) → ∃ ρ : ∀ β, SecT D.toPre a 0 k β, Small (maximalIdeal R) (w := id) ρ ∧ TFE h h' ρ ∧ ∀ e, ∃ τ : SecE U.toUnifPre (b e) 0 k, (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J') ∧ TExp U.toUnifPre τ (w := id) ρ := by
  first | exact @GlobalTheory.TwFam.exists_pull_expansion | exact GlobalTheory.TwFam.exists_pull_expansion | (intros; apply GlobalTheory.TwFam.exists_pull_expansion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFam
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwBack

variable {R : Type} [CommRing R] [IsDomain R]

theorem prod_tw (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n : ℕ) (β : D.X) {U : Type} [CommGroup U]
    (g : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ k, g (tφ D a β k) ^ tε n 0 k = ∏ k, g (D.famφB β k) ^ DegPre.famε n k := by
  rw [Fin.prod_univ_castSucc (n := 4)]
  show (∏ k : Fin 4, _) * g a.left ^ (0 : ℤ) = _
  rw [zpow_zero, _root_.mul_one]
  refine Finset.prod_congr rfl fun k _ => ?_
  fin_cases k <;> rfl

theorem vanMod_of_van (I : Ideal R) {D : DegPre R} {k : ℕ} {α : D.X} (b : D.SecB k α) (e : ℕ) (h : Van I b e) :
    VanMod I b e := by
  intro j
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : (thickObj R I e D.P.A).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (DVR.gs_zero _ y _ hy).symm)
  refine (sec_trans b _ y hy (Good.mem hJ (D.famφB α) _)).trans ?_
  exact (congrArg _ (h _ (𝟙 _) y J hJ)).trans (mul_zero _)

theorem shift_zero {X : Type} [AddCommGroup X] (h h' : X →+ X) (n : ℕ) (mu : X) :
    shift h h' n 0 mu = n • mu := by
  rw [shift, zero_smul, add_zero, natCast_zsmul]

theorem famFE_of_tfe (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X) (n : ℕ) (F : ∀ β, SecT D a n 0 β)
    (hF : TFE h h' F)
    (s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε n)))
    (hs : ∀ α (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J →
      sval (s α) x z J = sval (F α) (x ≫ (DegPre.prB D (FractionRing R)).left) z J) :
    DegPre.FamFE D (FractionRing R) n s := by
  intro mu α u hu hc
  have hT : TRel h mu (F α) (F (α + n • mu)) := by
    have := hF mu α
    rwa [shift_zero] at this
  obtain ⟨u', hu', hv⟩ := exists_gen D.P.isLB (φ' := dφ D a mu α (α + n • mu)) (ε' := dε n 0) (fun U _ g => by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, DegPre.deltaφ, DegPre.deltaε, dφ, dε, zpow_neg,
      Finset.prod_inv_distrib, DVR.GC.famφ_eq]
    rw [prod_tw D a n _ (fun ψ => g ((DegPre.prB D (FractionRing R)).left ≫ ψ)),
      prod_tw D a n _ (fun ψ => g ((DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left ≫ ψ))])
    u hu
  have hfac : IsFac D a h n 0 mu α (α + n • mu) u' := by
    refine ⟨hu', fun z J hJ => ?_⟩
    have e := val_corr hJ hc (𝟙 _)
    rw [val_pull hJ, Category.id_comp, DegPre.famMult, val_pull hJ, val_mul hJ, val_mul hJ, Category.id_comp] at e
    rw [hv _ _ z J hJ, zpow_zero, _root_.mul_one, add_zero, zpow_natCast, zpow_natCast]
    exact e.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (map_pow _ _ _) rfl) (map_pow _ _ _))
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  rw [hs _ _ _ y J hJ, hs _ _ _ y J hJ, ← hv _ _ y J hJ, Category.assoc]
  exact hT u' hfac _ (𝟙 _) y J hJ

theorem exists_intFam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (h h' : D.toPre.X →+ D.toPre.X) (n : ℕ) (F : ∀ β, SecT D.toPre a n 0 β), Small (maximalIdeal R) (w := id) F → TFE h h' F → ∃ Φ : IntFam (maximalIdeal R) D.toPre n, ∀ β, (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (Φ.f β) x z J = sval (F β) x z J) := by
  intro R _ _ _ _ D a h h' n F hS hF
  have hL := D.toPre.P.isLB
  choose f hf using fun β => exists_sec hL (φ' := D.toPre.famφB β) (ε' := DegPre.famε n)
    (fun U _ g => prod_tw D.toPre a n β g) (F β)
  choose s hs using fun β => exists_sec hL (φ' := DegPre.famφ D.toPre (FractionRing R) β) (ε' := DegPre.famε n)
    (fun U _ g => Finset.prod_congr rfl fun i _ => by rw [DVR.GC.famφ_eq])
    (DVR.pullSec D.toPre.P.L _ _ (f β) (DegPre.prB D.toPre (FractionRing R)).left)
  have hs' : ∀ β (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J),
      Good D.toPre.P.L z J → sval (s β) x z J = sval (f β) (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J :=
    fun β Z x z J hJ => (hs β Z x z J hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ x z hJ)
  have h1 : Out.scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by
    unfold Out.scal; rw [map_one, map_one]
  refine ⟨⟨⟨s, famFE_of_tfe D.toPre a h h' n F hF s fun β Z x z J hJ => (hs' β Z x z J hJ).trans (hf β Z _ z J hJ)⟩,
    f, fun β => ?_, fun e => (hS e).subset fun β hβ hv => hβ (vanMod_of_van _ _ e fun Z x z J hJ =>
      (hf β Z _ z J hJ).trans (hv Z x z J hJ))⟩, hf⟩
  rw [h1]
  exact DVR.SectionScalarValuation.secScal_of_sval hL fun y J hJ => (hs' β _ _ y J hJ).symm

end GlobalTheory.TwBack
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOnOfTExpGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.MumMult

theorem chartExpOn_of_tExp_gen {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {a : D.toPre.P.A ⟶ D.toPre.P.A} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (e : ℕ) (b : thickObj R I e G ⟶ thickObj R I e G) (n : ℕ)
    (F : ∀ β, SecT D.toPre a n 0 β) (f : ∀ β, D.toPre.SecB n β) (τ : SecE U b n 0) (hF : Small I (w := id) F)
    (hf : ∀ β, ∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      sval (f β) x z J = sval (F β) x z J)
    (hτ : TExp U τ (w := id) F) (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R I e G).left.Opens)
    (g : Γ((thickObj R I e G).left, W))
    (hg : ∀ (z : (thickObj R I e G).left) (J'), z ∈ W → Good U.LG.L z J' → J' (𝟙 _ ≫ (fstG I e G).left) = i' 0 →
      gs (𝟙 _) z W g = sval τ (𝟙 _) z J') : ChartExpOn U e n i' W g f := by
  classical
  let S : Finset D.toPre.X := (hF e).toFinset
  have hS : ∀ α ∉ S, Van I (F α) e := fun α hα => by_contra fun h => hα ((hF e).mem_toFinset.2 h)
  refine ⟨S, fun α hα j => fn_ext fun y hy => ?_, ?_⟩
  · choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
    refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (DVR.gs_zero (𝟙 _) y _ hy).symm)
    rw [Category.id_comp]
    have h0 : sval (f α) (DVR.pGl U e) y J = 0 := (hf α _ _ y J hJ).trans (hS α hα _ (U.gt e).q.left y J hJ)
    exact (sec_trans (f α) _ y hy (Good.mem hJ _ _)).trans ((congrArg _ h0).trans (mul_zero _))
  · rintro ⟨p₁, p₂⟩ jf jt hj hc
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, eJ⟩ := exists_good D.toPre.P.L D.toPre.P.isLB y _ _ hc (by
      rintro (a | a | a)
      exacts [mem_pull.1 hy.1.1.1.1, Set.mem_iInter.1 (U.expW_le_f e _ _ jf jt a.1.2 hy.1) a.2,
        Set.mem_iInter.1 (U.expWeight_le_chart_weight e _ _ jf jt a.1.2 hy.1) a.2])
    obtain ⟨J', hJ', eJ'⟩ := exists_good U.LG.L U.LG.isLB y (K := PUnit.{1}) (fun _ => 𝟙 _ ≫ (fstG I e G).left)
      (fun _ => p₂ PUnit.unit) (fun _ _ _ => rfl) (fun _ => mem_pull.1 hy.1.1.1.2)
    have e₀ : J (𝟙 _ ≫ (U.gt e).pG.left) = p₁ PUnit.unit := by rw [Category.id_comp]; exact eJ (.inl PUnit.unit)
    have e₁ : J' (𝟙 _ ≫ (fstG I e G).left) = p₂ PUnit.unit := eJ' PUnit.unit
    have H := hτ S hS _ (𝟙 _) y J J' hJ hJ'
    rw [evalE, zpow_zero, _root_.mul_one, zpow_natCast, e₀, e₁] at H
    refine ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) ?_ ((gs_res (𝟙 _) y inf_le_right hy g).trans
      (hg y J' hy.2 hJ' (e₁.trans hj.symm))))).trans
      (H.trans (Eq.symm ?_))
    · rw [← Units.val_pow_eq_pow_val, gs_unit (𝟙 _) y _ hy, map_pow]
      exact congrArg (fun u => (u ^ n).val) (gm_res (𝟙 _) y _ hy _)
    · refine (DVR.gs_fsum (𝟙 _) y _ hy _ _).trans (Eq.trans (Finset.sum_congr rfl fun α _ => ?_) (Finset.sum_attach S _))
      have l₁ : U.expW e (p₁, p₂) i' S jf jt ⊓ W ≤ _ := inf_le_left.trans (U.expW_le_f e (p₁, p₂) i' jf jt α.2)
      have l₂ : U.expW e (p₁, p₂) i' S jf jt ⊓ W ≤ _ := inf_le_left.trans (U.expWeight_le_chart_weight e (p₁, p₂) i' jf jt α.2)
      have a₁ := (gs_res (𝟙 _) y l₁ hy (((DVR.pGl U e).app _).hom ((f α.1).f (jf α.1)))).trans
        (gs_pull (𝟙 _) (DVR.pGl U e) y (LB.wchart D.toPre.P.L (D.toPre.famφB α.1) (jf α.1)) (l₁ hy) ((f α.1).f (jf α.1)))
      have a₂ := (gs_unit (𝟙 _) y _ hy (res l₂ ((DVR.tG U e α.1).s (jt α.1)))).trans
        (congrArg Units.val (gm_res (𝟙 _) y l₂ hy _))
      have b₁ := sval_of (f α.1) (𝟙 _ ≫ DVR.pGl U e) y J (jf α.1)
        (fun a => by rw [Category.id_comp]; exact eJ (.inr (.inl (α, a))))
      have b₂ := val_of (DVR.tG U e α.1) (𝟙 _) y J (jt α.1)
        (fun a => by rw [Category.id_comp]; exact eJ (.inr (.inr (α, a))))
      exact (gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) (a₁.trans (b₁.symm.trans (hf α.1 _ _ y J hJ)))
        (a₂.trans (congrArg Units.val b₂.symm)))

theorem chartExpOn_of_tExp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n : ℕ) (F : ∀ β, SecT D.toPre a n 0 β) (f : ∀ β, D.toPre.SecB n β) (τ : SecE U.toUnifPre b n 0), Small (maximalIdeal R) (w := id) F → (∀ β, (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (f β) x z J = sval (F β) x z J)) → TExp U.toUnifPre τ (w := id) F → ∀ (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R (maximalIdeal R) e G).left.Opens) (g : Γ((thickObj R (maximalIdeal R) e G).left, W)), (∀ (z : (thickObj R (maximalIdeal R) e G).left) (J'), z ∈ W → Good U.LG.L z J' → J' (𝟙 _ ≫ (fstG (maximalIdeal R) e G).left) = i' 0 → gs (𝟙 _) z W g = sval τ (𝟙 _) z J') → GlobalTheory.MumMult.ChartExpOn U.toUnifPre e n i' W g f :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ U e b n F f τ hF hf hτ i' W g hg =>
    chartExpOn_of_tExp_gen U.toUnifPre e b n F f τ hF hf hτ i' W g hg

end GlobalTheory.MumMult
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoGermTrans
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFamGlue

section General

variable {X₁ X₂ Y T : Scheme.{0}} {L : LB X₁} {M : LB X₂} {a : Y ⟶ X₁} {b : Y ⟶ X₂} {K : Type} [Fintype K]

def isoGerm (w : LB.Iso (L.pull a) (M.pull b)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : M.ι) (q : L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm r z ((M.pull b).U (fun _ => p) ⊓ (L.pull a).U (fun _ => q)) (w.s (fun _ => p, fun _ => q))

theorem isoGerm_trans {w : LB.Iso (L.pull a) (M.pull b)} (hw : w.IsGen) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    {p p' : M.ι} {q q' : L.ι}
    (hp : b (r z) ∈ M.U p) (hp' : b (r z) ∈ M.U p') (hq : a (r z) ∈ L.U q) (hq' : a (r z) ∈ L.U q') :
    isoGerm w r z p q = gm (r ≫ b) z _ (M.g p p') * (gm (r ≫ a) z _ (L.g q q'))⁻¹ * isoGerm w r z p' q' := by
  have hm : r z ∈ (M.pull b).U (fun _ => p) ⊓ (L.pull a).U (fun _ => q) ⊓
      ((M.pull b).U (fun _ => p') ⊓ (L.pull a).U (fun _ => q')) :=
    ⟨⟨mem_pull.2 hp, mem_pull.2 hq⟩, mem_pull.2 hp', mem_pull.2 hq'⟩
  refine (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _)
    (hw (fun _ => p, fun _ => q) (fun _ => p', fun _ => q'))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ((gm_div (L.pull a) (M.pull b) r z (fun _ => p, fun _ => q) (fun _ => p', fun _ => q') hm).trans ?_)
      (gm_res r z _ hm _))))
  exact congrArg₂ (· * ·) (gm_pull_g M b r z _ _ hm.1.1 hm.2.1) (congrArg (·⁻¹) (gm_pull_g L a r z _ _ hm.1.2 hm.2.2))

theorem prod_trans {w : LB.Iso (L.pull a) (M.pull b)} (hw : w.IsGen) (ψ : K → (T ⟶ Y)) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ T) (z : Z) {p p' : K → M.ι} {q q' : K → L.ι}
    (hp : r z ∈ LB.wchart M (fun k => ψ k ≫ b) p) (hp' : r z ∈ LB.wchart M (fun k => ψ k ≫ b) p')
    (hq : r z ∈ LB.wchart L (fun k => ψ k ≫ a) q) (hq' : r z ∈ LB.wchart L (fun k => ψ k ≫ a) q') :
    ∏ k, isoGerm w (r ≫ ψ k) z (p k) (q k) ^ ε k = trF (fun k => ψ k ≫ b) ε r z p p' *
      (trF (fun k => ψ k ≫ a) ε r z q q')⁻¹ * ∏ k, isoGerm w (r ≫ ψ k) z (p' k) (q' k) ^ ε k := by
  rw [trF, trF, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [isoGerm_trans hw (r ≫ ψ k) z (Set.mem_iInter.1 hp k) (Set.mem_iInter.1 hp' k) (Set.mem_iInter.1 hq k)
    (Set.mem_iInter.1 hq' k), mul_zpow, mul_zpow, inv_zpow]
  simp only [Category.assoc]

theorem exists_down (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso (L.pull a) (M.pull b)} (hw : w.IsGen) (ψ : K → (T ⟶ Y))
    (ε : K → ℤ) (σ : LB.Sec (LB.LinComb M (fun k => ψ k ≫ b) ε)) :
    ∃ τ : LB.Sec (LB.LinComb L (fun k => ψ k ≫ a) ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) (p : K → M.ι) (q : K → L.ι),
      r z ∈ LB.wchart M (fun k => ψ k ≫ b) p → r z ∈ LB.wchart L (fun k => ψ k ≫ a) q →
      (∏ k, isoGerm w (r ≫ ψ k) z (p k) (q k) ^ ε k).val * gs r z (LB.wchart L (fun k => ψ k ≫ a) q) (τ.f q) =
        gs r z (LB.wchart M (fun k => ψ k ≫ b) p) (σ.f p) := by
  have cov : ∀ y : T, ∃ p, y ∈ LB.wchart M (fun k => ψ k ≫ b) p := fun y => by
    choose I hI using fun k => exists_chart hM ((ψ k ≫ b) y)
    exact ⟨I, Set.mem_iInter.2 hI⟩
  have glue : ∀ q : K → L.ι, ∃ c : Γ(T, LB.wchart L (fun k => ψ k ≫ a) q), ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z)
      (p : K → M.ι), r z ∈ LB.wchart M (fun k => ψ k ≫ b) p → r z ∈ LB.wchart L (fun k => ψ k ≫ a) q →
      gs r z _ c = (∏ k, isoGerm w (r ≫ ψ k) z (p k) (q k) ^ ε k)⁻¹.val *
        gs r z (LB.wchart M (fun k => ψ k ≫ b) p) (σ.f p) := by
    intro q
    let V : (K → M.ι) → T.Opens := fun p => LB.wchart M (fun k => ψ k ≫ b) p ⊓ LB.wchart L (fun k => ψ k ≫ a) q
    have h₃ : ∀ p k, V p ≤ ψ k ⁻¹ᵁ ((M.pull b).U (fun _ => p k) ⊓ (L.pull a).U (fun _ => q k)) := fun p k y hy =>
      ⟨mem_pull.2 (Set.mem_iInter.1 hy.1 k), mem_pull.2 (Set.mem_iInter.1 hy.2 k)⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ p, Γ(T, V p), ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) p, r z ∈ V p →
        gs r z (V p) (u p) = (∏ k, isoGerm w (r ≫ ψ k) z (p k) (q k) ^ ε k)⁻¹.val *
          gs r z (LB.wchart M (fun k => ψ k ≫ b) p) (σ.f p) :=
      ⟨fun p => (∏ k, res (h₃ p k) (pullU (ψ k) _ (w.s (fun _ => p k, fun _ => q k))) ^ ε k)⁻¹.val *
          (T.presheaf.map (homOfLE (inf_le_left : V p ≤ LB.wchart M (fun k => ψ k ≫ b) p)).op).hom (σ.f p),
        fun Z r z p hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans
          (congrArg Units.val ((map_inv _ _).trans (congrArg (·⁻¹) ((map_prod _ _ _).trans
            (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
              ((gm_res r z (h₃ p k) hz _).trans (gm_pull r (ψ k) z _ (h₃ p k hz) _))))))))) (gs_res r z _ hz _))⟩
    obtain ⟨c, hc, -⟩ := T.sheaf.existsUnique_gluing' V (LB.wchart L (fun k => ψ k ≫ a) q)
      (fun p => homOfLE inf_le_right) (fun y hy => by
        obtain ⟨p, hp⟩ := cov y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hp, hy⟩) u
      (fun p p' => fn_ext (V := V p ⊓ V p') fun y hy => by
        refine (gs_res (𝟙 T) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 T) y inf_le_right hy _).symm)
        rw [hu _ _ y p hy.1, hu _ _ y p' hy.2, sec_trans σ (𝟙 T) y hy.1.1 hy.2.1,
          prod_trans hw ψ ε (𝟙 T) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          mul_eq_left.1 (trF_trans hL _ ε (𝟙 T) y hy.1.2 hy.1.2 hy.1.2), ← _root_.mul_assoc, ← Units.val_mul]
        congr 2
        rw [inv_one, _root_.mul_one, mul_inv_rev, inv_mul_cancel_right])
    refine ⟨c, fun Z r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ V p := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_right hz c).symm.trans ((congrArg (gs r z (V p)) (hc p)).trans (hu Z r z p hz))
  choose c hc using glue
  refine ⟨⟨c, fun q q' => fn_ext fun y hy => ?_⟩, fun Z r z p q hp hq => ?_⟩
  · obtain ⟨p, hp⟩ := cov y
    refine (gs_res (𝟙 T) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 T) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 T) y _ hy _).trans (congrArg Units.val (gm_linComb L _ ε (𝟙 T) y q q' hy.1 hy.2)))
      (gs_res (𝟙 T) y _ hy _))).symm)
    refine (hc q _ (𝟙 T) y p hp hy.1).trans (Eq.trans ?_ (congrArg _ (hc q' _ (𝟙 T) y p hp hy.2)).symm)
    rw [prod_trans hw ψ ε (𝟙 T) y hp hp hy.1 hy.2, mul_eq_left.1 (trF_trans hM _ ε (𝟙 T) y hp hp hp),
      ← _root_.mul_assoc, ← Units.val_mul, _root_.one_mul, mul_inv_rev, inv_inv, _root_.mul_comm _⁻¹]
    rfl
  · exact (congrArg _ (hc q Z r z p hp hq)).trans (Units.mul_inv_cancel_left _ _)

def sumSec {N : LB Y} {A : Type} (S : Finset A) (s : A → N.Sec) : N.Sec where
  f i := ∑ x ∈ S, (s x).f i
  compat i j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => (s x).compat i j

theorem sval_sumSec {φ : K → (Y ⟶ X₁)} {ε : K → ℤ} {A : Type} (S : Finset A) (s : A → (LB.LinComb L φ ε).Sec)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (sumSec S s) r z J = ∑ x ∈ S, sval (s x) r z J := DVR.gs_fsum r z _ (hJ.mem φ r) S _

end General

section Main

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ)

theorem formEq_term (a : D.toPre.P.A ⟶ D.toPre.P.A) (b : thickObj R I e G ⟶ thickObj R I e G)
    (hb : b.left ≫ DVR.pGl U e = DVR.pGl U e ≫ a.left) (n j : ℤ) (β : D.toPre.X) :
    FormEq (Sum.elim (fun k => DVR.pGl U e ≫ tφ D.toPre a β k) (DVR.Oφl U e β)) (Sum.elim (tε n j) Oinvε)
      (fun k => (![𝟙 _, b.left] : Fin 2 → _) k ≫ DVR.pGl U e) ![n, j] := by
  intro V _ h
  have a₀ : DVR.pGl U e ≫ tφ D.toPre a β 0 = DVR.pGl U e := Category.comp_id _
  have a₁ : DVR.pGl U e ≫ tφ D.toPre a β 1 = DVR.Oφl U e β 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul (U.gt e).pG (𝟙 _) (DVR.cP D.toPre _ β)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (DVR.comp_cP D.toPre _ β)))
  have a₂ : DVR.pGl U e ≫ tφ D.toPre a β 2 = DVR.Oφl U e β 1 :=
    congrArg (fun z => z.left) (DVR.comp_cP D.toPre (U.gt e).pG β)
  have a₃ : DVR.pGl U e ≫ tφ D.toPre a β 3 = DVR.Oφl U e β 3 :=
    congrArg (fun z : _ ⟶ D.toPre.P.A => z.left) (MonObj.comp_one (M := D.toPre.P.A) (U.gt e).pG)
  have a₄ : DVR.Oφl U e β 2 = DVR.pGl U e := rfl
  have a₅ : DVR.pGl U e ≫ tφ D.toPre a β 4 = b.left ≫ DVR.pGl U e := hb.symm
  have a₆ : (![𝟙 _, b.left] : Fin 2 → _) 0 ≫ DVR.pGl U e = DVR.pGl U e := Category.id_comp _
  have a₇ : (![𝟙 _, b.left] : Fin 2 → _) 1 ≫ DVR.pGl U e = b.left ≫ DVR.pGl U e := rfl
  rw [Fintype.prod_sum_type, Fin.prod_univ_five, Fin.prod_univ_four, Fin.prod_univ_two]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, tε, Oinvε, Matrix.cons_val]
  module

theorem exists_texp (a : D.toPre.P.A ⟶ D.toPre.P.A) (b : thickObj R I e G ⟶ thickObj R I e G)
    (hb : b ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map a) (n j : ℤ) {Ix : Type}
    {w : Ix → D.toPre.X} (s : ∀ i, SecT D.toPre a n j (w i)) (hs : Small I s) :
    ∃ τ : SecE U b n j, TExp U τ s := by
  classical
  have hb' : b.left ≫ DVR.pGl U e = DVR.pGl U e ≫ a.left := by
    have h₁ : b.left ≫ (U.gt e).q.left = (U.gt e).q.left ≫ ((Over.pullback (thick R I e)).map a).left :=
      congrArg (fun f => f.left) hb
    have h₂ : ((Over.pullback (thick R I e)).map a).left ≫ pullback.fst D.toPre.P.A.hom (thick R I e) =
        pullback.fst D.toPre.P.A.hom (thick R I e) ≫ a.left := pullback.lift_fst _ _ _
    show b.left ≫ (U.gt e).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R I e) =
      ((U.gt e).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R I e)) ≫ a.left
    rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]
  choose σ hσ using fun i => exists_sec D.toPre.P.isLB (formEq_term U e a b hb' n j (w i))
    (pullMulSec (s i) (DVR.pGl U e) (DVR.tG U e (w i)) ((U.gt e).t_gen (w i)))
  obtain ⟨τ₀, h₀⟩ := exists_down U.LG.isLB D.toPre.P.isLB (U.w_gen e) (![𝟙 _, b.left] : Fin 2 → _) ![n, j]
    (sumSec (hs e).toFinset σ)
  obtain ⟨τ, hτ⟩ := exists_sec U.LG.isLB (φ' := ![(fstG I e G).left, b.left ≫ (fstG I e G).left]) (ε' := ![n, j])
    (fun V _ h => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      exact congrArg (fun f => h f ^ n * _) (Category.id_comp _)) τ₀
  refine ⟨τ, fun S hS Z x z J J' hJ hJ' => ?_⟩
  have H := h₀ Z x z _ _ (hJ.mem _ x) (hJ'.mem _ x)
  have van : ∀ i, Van I (s i) e → sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val = 0 :=
    fun i hi => by
      have := hi Z (x ≫ (U.gt e).q.left) z J hJ
      rw [Category.assoc] at this
      exact (congrArg (· * _) this).trans (zero_mul _)
  have H₂ : sval (sumSec (hs e).toFinset σ) x z J =
      ∑ i ∈ S, sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val := by
    rw [sval_sumSec _ _ x z hJ]
    refine (Finset.sum_congr rfl fun i _ => (hσ i Z x z J hJ).trans (sval_pullMulSec _ _ _ _ x z hJ)).trans ?_
    refine Finset.sum_subset (fun i hi => by_contra fun h => (hs e).mem_toFinset.1 hi (hS i h)) fun i _ hi => ?_
    exact van i (by_contra fun h => hi ((hs e).mem_toFinset.2 h))
  refine Eq.trans ?_ (H.trans H₂)
  refine congrArg₂ (· * ·) (congrArg Units.val ?_) (hτ Z x z J' hJ')
  rw [Fin.prod_univ_two]
  show _ = DVR.wv U e (x ≫ 𝟙 _) z (J (x ≫ 𝟙 _ ≫ _)) (J' (x ≫ 𝟙 _ ≫ _)) ^ n * _
  rw [Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

end Main

theorem glue : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), b ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R (maximalIdeal R) e)).map a → ∀ (n j : ℤ) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)), Small (maximalIdeal R) s → ∃ τ : SecE U.toUnifPre b n j, TExp U.toUnifPre τ s :=
  fun _ _ _ _ _ _ a _ _ _ _ _ U e b hb n j _ _ s hs => exists_texp U.toUnifPre e a b hb n j s hs

end GlobalTheory.TwFamGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordMultiplierOfSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.MumMult

theorem gs_pow_mul_pull {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (v u : Y ⟶ X) (N k : ℕ)
    (τ : LB.Sec (LB.LinComb L (K := Fin 2) ![v, u] ![(N : ℤ), -1])) (s : H0 L k) (i i' : Fin 1 → L.ι)
    (hle : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ LB.wchart L ![v, u] ![i' 0, i 0])
    (z : Y) (J' : (Y ⟶ X) → L.ι) (hz : z ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i') (hJ : Good L z J')
    (hv : J' (𝟙 Y ≫ v) = i' 0) :
    gs (𝟙 Y) z (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')
      ((Y.presheaf.map (homOfLE hle).op).hom (τ.f ![i' 0, i 0]) ^ k *
        (Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤
          u ⁻¹ᵁ secChart L i)).op).hom ((u.app (secChart L i)).hom (s.f i))) =
      sval τ (𝟙 Y) z J' ^ k * sval s (𝟙 Y ≫ u) z J' := by
  have hm : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart L ![v, u] ![i' 0, i 0] := hle hz
  have hu : (𝟙 Y ≫ u) z ∈ secChart L i := hz.1
  have hv' : (𝟙 Y ≫ v) z ∈ L.U (i' 0) := Set.mem_iInter.1 hz.2 0
  have a0 : ∀ x y : Γ(Y, u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i'),
      gs (𝟙 Y) z _ (x ^ k * y) = gs (𝟙 Y) z _ x ^ k * gs (𝟙 Y) z _ y := fun x y => by
    rw [gs_eq _ _ _ hz, gs_eq _ _ _ hz, gs_eq _ _ _ hz, map_mul, map_mul, map_pow, map_pow]
  have a1 := gs_res (𝟙 Y) z hle hz (τ.f ![i' 0, i 0])
  have a2 := (gs_res (𝟙 Y) z (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤
          u ⁻¹ᵁ secChart L i) hz ((u.app (secChart L i)).hom (s.f i))).trans (gs_pull (𝟙 Y) u z _ hu (s.f i))
  rw [a0, a1, a2, sec_trans τ (𝟙 Y) z hm (hJ.mem _ (𝟙 Y)), sec_trans s (𝟙 Y ≫ u) z hu (hJ.mem _ _)]
  have e1 : trF (L := L) ![v, u] ![(N : ℤ), -1] (𝟙 Y) z ![i' 0, i 0] (fun k => J' (𝟙 Y ≫ (![v, u] : Fin 2 → _) k)) =
      (gm (𝟙 Y ≫ u) z _ (L.g (i 0) (J' (𝟙 Y ≫ u))))⁻¹ := by
    rw [trF, Fin.prod_univ_two]
    change gm (𝟙 Y ≫ v) z (L.U (i' 0) ⊓ L.U (J' (𝟙 Y ≫ v))) (L.g (i' 0) (J' (𝟙 Y ≫ v))) ^ (N : ℤ) *
      gm (𝟙 Y ≫ u) z (L.U (i 0) ⊓ L.U (J' (𝟙 Y ≫ u))) (L.g (i 0) (J' (𝟙 Y ≫ u))) ^ (-1 : ℤ) = _
    have gself : ∀ c : L.ι, c = i' 0 → gm (𝟙 Y ≫ v) z (L.U (i' 0) ⊓ L.U c) (L.g (i' 0) c) = 1 := by
      rintro c rfl; exact gm_self hL _ _ hv'
    rw [gself _ hv, one_zpow, _root_.one_mul, zpow_neg, zpow_one]
  have e2 : trF (L := L) (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) (𝟙 Y ≫ u) z i
      (fun k => J' ((𝟙 Y ≫ u) ≫ (fun _ : Fin 1 => 𝟙 X) k)) =
      (gm (𝟙 Y ≫ u) z _ (L.g (i 0) (J' (𝟙 Y ≫ u)))) ^ k := by
    simp only [trF, Fin.prod_univ_one]
    have gid : ∀ f : Y ⟶ X, f = 𝟙 Y ≫ u →
        gm f z (L.U (i 0) ⊓ L.U (J' f)) (L.g (i 0) (J' f)) = gm (𝟙 Y ≫ u) z _ (L.g (i 0) (J' (𝟙 Y ≫ u))) := by
      rintro f rfl; rfl
    rw [gid _ (Category.comp_id _), zpow_natCast]
  rw [e1, e2]
  unfold sval
  generalize gm (𝟙 Y ≫ u) z _ (L.g (i 0) (J' (𝟙 Y ≫ u))) = A
  have hA : ((A⁻¹ : _ˣ) : Y.presheaf.stalk z) ^ k * ((A ^ k : _ˣ) : Y.presheaf.stalk z) = 1 := by
    rw [Units.val_pow_eq_pow_val, ← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow]
  rw [mul_pow, _root_.mul_mul_mul_comm, hA, _root_.one_mul]

private theorem isUnit_gs_iff_mem {X Y : Scheme.{0}} (r : Y ⟶ X) (z : Y) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h]
  refine ((Y.mem_basicOpen ((r.app U).hom a) z h).symm).trans ?_
  rw [← Scheme.Hom.preimage_basicOpen]
  rfl

theorem exists_mult_of_posN : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])) (x : D.toPre.P.A.left), D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) → GlobalTheory.MumMult.NonzeroAt D a N σ₀ x → ∃ m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, GlobalTheory.MumMult.multW U b e i i'), GlobalTheory.MumMult.MultAct U b N m ∧ GlobalTheory.MumMult.LeadPt U b m := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' hE b hb N hN hP σ₀ x hx hnz
  obtain ⟨g, gsm, gtfe, gvan, g0⟩ := GlobalTheory.T.exists_mumford_formal_section_coefficient_family R hR.1 D a a' h h' hE N hN hP σ₀
  choose τ hτ using fun e => GlobalTheory.TwFamGlue.glue R hR.1 D a A G hG U e (b e) (hb.2.2.1 e) (N : ℤ) (-1) D.toPre.X id g gsm
  have hle : ∀ e (i i' : Fin 1 → U.LG.L.ι), multW U b e i i' ≤ LB.wchart U.LG.L
      ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left] ![i' 0, i 0] := by
    intro e i i' y hy
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · simpa using Set.mem_iInter.1 hy.2 0
    · simpa using Set.mem_iInter.1 hy.1 0
  refine ⟨fun e i i' => ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hle e i i')).op).hom
    ((τ e).f ![i' 0, i 0]), ?_, ?_⟩
  · intro k hk f s hs
    obtain ⟨ρ, ρsm, ρtfe, hρ⟩ := GlobalTheory.T.exists_pullback_integralExpansion_formalEndomorphism R hR.1 D a a' h h' hE A G hG U b hb k s f hs
    obtain ⟨F, Fsm, Ftfe, hF⟩ := GlobalTheory.T.multiplier_power_mul_pullback_small_family R hR.1 D a a' h h' hE A G hG U b hb N k g ρ gsm ρsm gtfe ρtfe
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.TwBack.exists_intFam R hR.1 D a h h' (N * k) F Fsm Ftfe
    refine ⟨Φ, fun e i i' => ?_⟩
    obtain ⟨τ', hτ'1, hτ'2⟩ := hρ e
    obtain ⟨τ'', h1, h2⟩ := hF e (τ e) τ' (hτ e) hτ'2
    refine GlobalTheory.MumMult.chartExpOn_of_tExp R hR.1 D a A G hG U e (b e) (N * k) F Φ.f τ'' Fsm hΦ h2 i' _ _ ?_
    intro z J' hz hJ' hv
    rw [h1 _ _ z J' hJ', hτ'1 _ _ z J' hJ']
    exact gs_pow_mul_pull U.LG.isLB _ _ N k (τ e) s i i' (hle e i i') z J' hz hJ' hv
  · refine ⟨x, hx, fun y hy i i' hyW => ?_⟩
    choose J hJ using fun χ : (thickObj R (maximalIdeal R) 0 G).left ⟶ D.toPre.P.A.left =>
      exists_chart D.toPre.P.isLB (χ y)
    choose J' hJ' using fun χ : (thickObj R (maximalIdeal R) 0 G).left ⟶ G.left => exists_chart U.LG.isLB (χ y)
    have hx0 : IsUnit (sval σ₀ (𝟙 _ ≫ (U.gt 0).pG.left) y J) := by
      have hm := Good.mem (L := D.toPre.P.L) hJ
        (![𝟙 D.toPre.P.A.left, a.left] : Fin 2 → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (𝟙 _ ≫ (U.gt 0).pG.left)
      have hyx : (𝟙 _ ≫ (U.gt 0).pG.left : (thickObj R (maximalIdeal R) 0 G).left ⟶ D.toPre.P.A.left) y = x := hy
      refine (isUnit_gs_iff_mem _ y _ hm _).2 ?_
      rw [hyx] at hm ⊢
      exact hnz _ hm
    have hg0 : sval (g 0) (𝟙 _ ≫ (U.gt 0).pG.left) y J = sval σ₀ (𝟙 _ ≫ (U.gt 0).pG.left) y J :=
      g0 _ (𝟙 _ ≫ (U.gt 0).q.left) y J hJ
    have hexp := hτ 0 {0} (fun β hβ => gvan β (by simpa using hβ)) _ (𝟙 _) y J J' hJ hJ'
    rw [Finset.sum_singleton] at hexp
    have hu : IsUnit (evalE U.toUnifPre (τ 0) (𝟙 _) y J J') := by
      rw [hexp]
      exact (hg0 ▸ hx0 : IsUnit (sval (g 0) (𝟙 _ ≫ (U.gt 0).pG.left) y J)).mul (Units.isUnit _)
    have hs : IsUnit (sval (τ 0) (𝟙 _) y J') := isUnit_of_mul_isUnit_right hu
    refine (isUnit_gs_iff_mem (𝟙 _) y _ hyW _).1 ?_
    have e := (gs_res (𝟙 _) y (hle 0 i i') hyW ((τ 0).f ![i' 0, i 0])).trans
      (sec_trans (τ 0) (𝟙 _) y (hle 0 i i' hyW) (Good.mem (L := U.LG.L) hJ' _ (𝟙 _)))
    exact e ▸ (Units.isUnit _).mul hs

end GlobalTheory.MumMult
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordMultiplierOfSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mumfordMultiplier_of_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])) (x : D.toPre.P.A.left), D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) → GlobalTheory.MumMult.NonzeroAt D a N σ₀ x → ∃ m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, GlobalTheory.MumMult.multW U b e i i'), GlobalTheory.MumMult.MultAct U b N m ∧ GlobalTheory.MumMult.LeadPt U b m := by
  first | exact @GlobalTheory.MumMult.exists_mult_of_posN | exact GlobalTheory.MumMult.exists_mult_of_posN | (intros; apply GlobalTheory.MumMult.exists_mult_of_posN <;> assumption)
end
