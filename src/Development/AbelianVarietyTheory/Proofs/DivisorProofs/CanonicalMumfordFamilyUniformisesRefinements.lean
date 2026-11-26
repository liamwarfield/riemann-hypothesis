module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageUniformisedByFactorData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinementIsFactorBaseChangeCanonicalMumfordFami
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedIdempotentFactorPullbackRefinement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoSquarePassesSecondIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoSquarePassesSecondIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.FactorPull

theorem lam_down_gen : ∀ {S S' : Scheme.{0}} {f : S' ⟶ S} {B C : Over S} {B₁ C₁ : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj C]
  [IsCommMonObj C] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj C₁] [IsCommMonObj C₁] {δ : C₁.left ⟶ C.left} {M : LB B.left} {N : LB C.left} {M₁ : LB B₁.left} {N₁ : LB C₁.left}
  (gC : IsGrpPullback C₁ C f δ), M.IsLB → N.IsLB → M₁.IsLB → N₁.IsLB → ∀ (β₂ : (G2 B₁).left ⟶ (G2 B).left) (u : LB.Iso (abelian₂ B₁ M₁) ((abelian₂ B M).pull β₂)), u.IsGen →
  ∀ (v' : LB.Iso N₁ (N.pull δ)), v'.IsGen → ∀ {m : (G2 B).left ⟶ (G2 C).left} {m₁ : (G2 B₁).left ⟶ (G2 C₁).left},
    m₁ ≫ sqOf gC = β₂ ≫ m → ∀ (w : LB.Iso (abelian₂ B M) ((abelian₂ C N).pull m)), w.IsGen →
    ∃ w₁ : LB.Iso (abelian₂ B₁ M₁) ((abelian₂ C₁ N₁).pull m₁), w₁.IsGen ∧
      ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 B₁).left) (z : Z) I J I₁ J₁, Good N z I → Good M z J → Good N₁ z I₁ →
        Good M₁ z J₁ → (∏ k, om v' z I I₁ ((p ≫ m₁) ≫ lamφ C₁ k) ^ lamε k) * lamVal w₁ p z I₁ J₁ =
          lamVal w (p ≫ β₂) z I J * lamVal u p z J J₁ := by
  intro S S' f B C B₁ C₁ _ _ _ _ _ _ _ _ δ M N M₁ N₁ gC hM hN hM₁ hN₁ β₂ u hu v' hv' m m₁ hm w hw
  have lM : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have lN : (abelian₂ C N).IsLB := DVR.linComb_isLB _ hN _ _
  have lM₁ : (abelian₂ B₁ M₁).IsLB := DVR.linComb_isLB _ hM₁ _ _
  have lN₁ : (abelian₂ C₁ N₁).IsLB := DVR.linComb_isLB _ hN₁ _ _
  have pw := (isGen_iff _).1 hw
  have pu := (isGen_iff u).1 hu
  have pv' := pgen_lamIso gC v' ((isGen_iff v').1 hv')
  obtain ⟨w₂, T⟩ := exists_comp lM w u pw pu lN lM₁
  have p₂ := pgen_pullCongr hm.symm (T.pgen_comp lM pw pu)
  obtain ⟨w₁, T'⟩ := exists_cancel lN (lamIso gC v') (pullCongr hm.symm w₂) pv' p₂ lN₁ lM₁
  refine ⟨w₁, (isGen_iff _).2 (T'.pgen_cancel lN pv' p₂), fun Z p z I J I₁ J₁ hI hJ hI₁ hJ₁ => ?_⟩
  have e : (p ≫ m₁) ≫ sqOf gC = (p ≫ β₂) ≫ m := by rw [Category.assoc, hm, Category.assoc]
  have t := T Z p z (fun k => I (((p ≫ β₂) ≫ m) ≫ lamφ C k))
    (fun k => J ((p ≫ β₂) ≫ lamφ B k)) (fun k => J₁ (p ≫ lamφ B₁ k))
    (Set.mem_iInter.2 fun k => hI (((p ≫ β₂) ≫ m) ≫ lamφ C k))
    (Set.mem_iInter.2 fun k => hJ ((p ≫ β₂) ≫ lamφ B k))
    (Set.mem_iInter.2 fun k => hJ₁ (p ≫ lamφ B₁ k))
  have t' := T' Z p z (fun k => I (((p ≫ m₁) ≫ sqOf gC) ≫ lamφ C k))
    (fun k => I₁ ((p ≫ m₁) ≫ lamφ C₁ k)) (fun k => J₁ (p ≫ lamφ B₁ k))
    (Set.mem_iInter.2 fun k => hI (((p ≫ m₁) ≫ sqOf gC) ≫ lamφ C k))
    (Set.mem_iInter.2 fun k => hI₁ ((p ≫ m₁) ≫ lamφ C₁ k))
    (Set.mem_iInter.2 fun k => hJ₁ (p ≫ lamφ B₁ k))
  replace t' := (gw_pullCongr _ _ _ _ _ _).symm.trans (t'.trans (congrArg₂ (· * ·) (gw_lam gC v' (p ≫ m₁) z hI hI₁) rfl))
  rw [e] at t'
  replace t' := t.symm.trans t'
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) (t'.symm.trans (congrArg₂ (· * ·) ?_ ?_))
  · show Geo.Tor.gw w₁ p z (fun k => I₁ (p ≫ m₁ ≫ lamφ C₁ k)) (fun k => J₁ (p ≫ lamφ B₁ k)) = _
    simp only [Category.assoc]
  · show _ = Geo.Tor.gw w (p ≫ β₂) z (fun k => I ((p ≫ β₂) ≫ m ≫ lamφ C k))
      (fun k => J ((p ≫ β₂) ≫ lamφ B k))
    simp only [Category.assoc]
  · show _ = Geo.Tor.gw u p z (fun k => J (p ≫ β₂ ≫ lamφ B k)) (fun k => J₁ (p ≫ lamφ B₁ k))
    simp only [Category.assoc]

end GlobalTheory.FactorPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoSquarePassesSecondIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundleIso_square_passes_second_iso : ∀ {S S' : Scheme.{0}} {f : S' ⟶ S} {B C : Over S} {B₁ C₁ : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj C]
  [IsCommMonObj C] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj C₁] [IsCommMonObj C₁] {δ : C₁.left ⟶ C.left} {M : LB B.left} {N : LB C.left} {M₁ : LB B₁.left} {N₁ : LB C₁.left}
  (gC : IsGrpPullback C₁ C f δ), M.IsLB → N.IsLB → M₁.IsLB → N₁.IsLB → ∀ (β₂ : (G2 B₁).left ⟶ (G2 B).left) (u : LB.Iso (abelian₂ B₁ M₁) ((abelian₂ B M).pull β₂)), u.IsGen →
  ∀ (v' : LB.Iso N₁ (N.pull δ)), v'.IsGen → ∀ {m : (G2 B).left ⟶ (G2 C).left} {m₁ : (G2 B₁).left ⟶ (G2 C₁).left},
    m₁ ≫ sqOf gC = β₂ ≫ m → ∀ (w : LB.Iso (abelian₂ B M) ((abelian₂ C N).pull m)), w.IsGen →
    ∃ w₁ : LB.Iso (abelian₂ B₁ M₁) ((abelian₂ C₁ N₁).pull m₁), w₁.IsGen ∧
      ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 B₁).left) (z : Z) I J I₁ J₁, Good N z I → Good M z J → Good N₁ z I₁ →
        Good M₁ z J₁ → (∏ k, om v' z I I₁ ((p ≫ m₁) ≫ lamφ C₁ k) ^ lamε k) * lamVal w₁ p z I₁ J₁ =
          lamVal w (p ≫ β₂) z I J * lamVal u p z J J₁ := by
  first | exact @GlobalTheory.FactorPull.lam_down_gen | exact GlobalTheory.FactorPull.lam_down_gen | (intros; apply GlobalTheory.FactorPull.lam_down_gen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedIdempotentFactorPullbackRefinement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FactorPull

section PFactorPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B C : Over S} {B₁ C₁ : Over S'} [GrpObj B] [GrpObj C]
  [GrpObj B₁] [GrpObj C₁] [IsCommMonObj C] [IsCommMonObj C₁] {β : B₁.left ⟶ B.left} {δ : C₁.left ⟶ C.left}

theorem lift_sq_of (β₂ : (G2 B₁).left ⟶ (G2 B).left) (hsq : IsSquare β β₂) (gC : IsGrpPullback C₁ C f δ)
    {u v : B ⟶ C} {u₁ v₁ : B₁ ⟶ C₁} (hu : u₁.left ≫ δ = β ≫ u.left) (hv : v₁.left ≫ δ = β ≫ v.left) :
    (lift (fst B₁ B₁ ≫ u₁) (snd B₁ B₁ ≫ v₁) : G2 B₁ ⟶ G2 C₁).left ≫ sqOf gC =
      β₂ ≫ (lift (fst B B ≫ u) (snd B B ≫ v) : G2 B ⟶ G2 C).left := by
  apply pullback.hom_ext
  · show _ ≫ (fst C C).left = _ ≫ (fst C C).left
    rw [Category.assoc, (isSquare_sqOf gC).1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
      ← Over.comp_left, lift_fst, Over.comp_left, Over.comp_left, Category.assoc, hu, ← Category.assoc β₂,
      hsq.1, Category.assoc]
  · show _ ≫ (snd C C).left = _ ≫ (snd C C).left
    rw [Category.assoc, (isSquare_sqOf gC).2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
      ← Over.comp_left, lift_snd, Over.comp_left, Over.comp_left, Category.assoc, hv, ← Category.assoc β₂,
      hsq.2, Category.assoc]

end PFactorPull


set_option maxHeartbeats 800000 in
theorem pfactor_pull : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ →
  ∀ (Q : Data R) (D' : DegPre R) (F : PFactor Q D') (D : DegPre R') (ε : D.X ≃+ Q.X), Refines Q ρ D ε →
  ∀ (D₁' : DegPre R') (hD' : IsPullDeg ρ D' D₁') [Module F.O D₁'.X] (o₁ : D₁'.OAct F.O),
    (∀ (a : F.O) (y : D₁'.X), hD'.xe (a • y) = a • hD'.xe y) →
    (∀ a, (o₁.onB.act a).left ≫ proj hD' = proj hD' ≫ (F.o.onB.act a).left) →
    ∃ (inc : D.P.A ⟶ D₁'.P.A) (pr : D₁'.P.A ⟶ D.P.A) (xi : D.X →+ D₁'.X) (xp : D₁'.X →+ D.X)
      (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D₁'.P.A D₁'.P.L).pull
        (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o₁.onB.act F.f) : G2 D.P.A ⟶ G2 D₁'.P.A).left)),
      IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o₁.onB.act F.e ∧ (∀ y, xp (xi y) = y) ∧
      (∀ z, xi (xp z) = F.e • z) ∧ (∀ y, D₁'.c (xi y) = D.c y ≫ inc) ∧
      (Function.Injective fun y => star F.e • F.f • xi y) ∧ (∀ z : D₁'.X, ∃ y, star F.e • z = star F.e • F.f • xi y) ∧
      w.IsGen ∧ ∀ a b z J J', Good D₁'.P.L z J → Good D.P.L z J' →
        val (D.tau a b) (𝟙 _) z J' =
          lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' *
            val (D₁'.tau (xi a) (F.f • xi b)) (𝟙 _) z J := by
  intro R R' _ _ _ _ ρ hρ Q D' F D ε hR D₁' hD' _ o₁ hx ho
  obtain ⟨β, β₂, wR, gB, hsq, hwR, hcR, htR⟩ := hR
  have gC := pull_grp hD'
  obtain ⟨inc, mi, hi⟩ := hom_pull gB gC F.inc F.inc_hom
  obtain ⟨pr, mp, hp⟩ := hom_pull gC gB F.pr F.pr_hom
  obtain ⟨xi, hxi⟩ : ∃ xi : D.X →+ D₁'.X, ∀ y, hD'.xe (xi y) = F.xi (ε y) :=
    ⟨hD'.xe.symm.toAddMonoidHom.comp (F.xi.comp ε.toAddMonoidHom), fun y => hD'.xe.apply_symm_apply _⟩
  obtain ⟨xp, hxp⟩ : ∃ xp : D₁'.X →+ D.X, ∀ y, ε (xp y) = F.xp (hD'.xe y) :=
    ⟨ε.symm.toAddMonoidHom.comp (F.xp.comp hD'.xe.toAddMonoidHom), fun y => ε.apply_symm_apply _⟩
  have hf : (inc ≫ o₁.onB.act F.f).left ≫ proj hD' = β ≫ (F.inc ≫ F.o.onB.act F.f).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ho, ← Category.assoc, hi, Category.assoc]
  have hm := lift_sq_of β₂ hsq gC hi hf
  obtain ⟨w, hw, vw⟩ := GlobalTheory.T.mumfordBundleIso_square_passes_second_iso gC Q.M.isLB D'.P.isLB D.P.isLB D₁'.P.isLB β₂ wR hwR hD'.w hD'.w_gen hm F.w F.w_gen
  have hc : ∀ y, D₁'.c (xi y) = D.c y ≫ inc := fun y => ext_pull gC (by
    rw [hD'.c_pr, hxi, F.c_xi, Over.comp_left, Over.comp_left, Category.assoc, hi, ← Category.assoc (D.c y).left,
      hcR, Category.assoc])
  refine ⟨inc, pr, xi, xp, w, mi, mp, ext_pull gB ?_, ext_pull gC ?_, fun y => ε.injective ?_,
    fun y => hD'.xe.injective ?_, hc, fun y y' h => ?_, fun z => ?_, hw, fun a b z I₁ J₁ hI₁ hJ₁ => ?_⟩
  · rw [Over.comp_left, Category.assoc, hp, ← Category.assoc, hi, Category.assoc, ← Over.comp_left, F.inc_pr,
      Over.id_left, Over.id_left, Category.comp_id, Category.id_comp]
  · rw [Over.comp_left, Category.assoc, hi, ← Category.assoc, hp, Category.assoc, ← Over.comp_left, F.pr_inc, ho]
  · rw [hxp, hxi, F.xp_xi]
  · rw [hxi, hxp, F.xi_xp, hx]
  · have h' := congrArg hD'.xe h
    simp only [hx, hxi] at h'
    exact ε.injective (F.inj h')
  · obtain ⟨y, hy⟩ := F.onto (hD'.xe z)
    refine ⟨ε.symm y, hD'.xe.injective ?_⟩
    rw [hx, hx, hx, hxi, ε.apply_symm_apply, hy]
  · obtain ⟨J, hJ⟩ := GlobalTheory.DegPull.exists_good' Q.M.isLB z
    obtain ⟨I, hI⟩ := GlobalTheory.DegPull.exists_good' D'.P.isLB z
    let g₀ := genMap hρ
    have sq : (TK R').hom ≫ spMap ρ = g₀ ≫ (TK R).hom := (Category.id_comp _).symm.trans (fracMap_sq hρ)
    have hκ : g₀ ≫ jK R = jK R' ≫ spMap ρ := (fracMap_sq hρ).symm.trans (Category.id_comp _)
    have cQ : ∀ y, (toUnit (TK R') ≫ D.c y).left ≫ β = g₀ ≫ (toUnit (TK R) ≫ Q.c (ε y)).left := fun y => by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hcR, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ (Q.c (ε y)).left) sq
    have hP : (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left ≫ β₂ =
        g₀ ≫ (lift (toUnit (TK R) ≫ Q.c (ε a)) (toUnit (TK R) ≫ Q.c (ε b))).left := by
      apply pullback.hom_ext
      · show _ ≫ (fst Q.B Q.B).left = _ ≫ (fst Q.B Q.B).left
        rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
          ← Over.comp_left, lift_fst]
        exact cQ a
      · show _ ≫ (snd Q.B Q.B).left = _ ≫ (snd Q.B Q.B).left
        rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
          ← Over.comp_left, lift_snd]
        exact cQ b
    have hQ : (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left ≫
        (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o₁.onB.act F.f) : G2 D.P.A ⟶ G2 D₁'.P.A).left =
        (lift (toUnit (TK R') ≫ D₁'.c (xi a)) (toUnit (TK R') ≫ D₁'.c (F.f • xi b))).left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, o₁.c_lin, hc, hc]
      simp only [Category.assoc]
    have R₁ := htR g₀ hκ a b z J J₁ hJ hJ₁
    have t₁ := F.tau (ε a) (ε b) (g₀ z) (fun ψ => I (g₀ ≫ ψ)) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => hI (g₀ ≫ ψ))
      (fun ψ => hJ (g₀ ≫ ψ))
    have t₂ := (congrArg (Units.map (g₀.stalkMap z).hom.toMonoidHom) t₁).trans (map_mul _ _ _)
    have n₁ : val (Q.tau (ε a) (ε b)) (g₀ ≫ 𝟙 _) z J = Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (Q.tau (ε a) (ε b)) (𝟙 _) (g₀ z) (fun ψ => J (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) g₀ z J hJ).2.2.1 _)
    have n₂ : val (D'.tau (F.xi (ε a)) (F.f • F.xi (ε b))) (g₀ ≫ 𝟙 _) z I =
        Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (D'.tau (F.xi (ε a)) (F.f • F.xi (ε b))) (𝟙 _) (g₀ z) (fun ψ => I (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) g₀ z I hI).2.2.1 _)
    rw [Category.comp_id] at n₁ n₂
    have E := n₁.trans (t₂.trans (congrArg₂ (· * ·) (lamVal_comp F.w g₀ _ z I J hI hJ).symm n₂.symm))
    have K := vw _ (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z I J I₁ J₁ hI hJ hI₁ hJ₁
    rw [hP, hQ] at K
    have a₂ := tau_lam hD' hρ (xi a) (F.f • xi b) hI hI₁
    rw [hx, hxi, hxi] at a₂
    rw [R₁, ← a₂, E, ← _root_.mul_assoc, ← _root_.mul_assoc, mul_comm (lamVal w _ z I₁ J₁), K,
      mul_comm (lamVal F.w _ z I J)]

end GlobalTheory.FactorPull

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedIdempotentFactorPullbackRefinementStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedIdempotentFactor_pullback_refinement : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ →
  ∀ (Q : Data R) (D' : DegPre R) (F : PFactor Q D') (D : DegPre R') (ε : D.X ≃+ Q.X), Refines Q ρ D ε →
  ∀ (D₁' : DegPre R') (hD' : IsPullDeg ρ D' D₁') [Module F.O D₁'.X] (o₁ : D₁'.OAct F.O),
    (∀ (a : F.O) (y : D₁'.X), hD'.xe (a • y) = a • hD'.xe y) →
    (∀ a, (o₁.onB.act a).left ≫ proj hD' = proj hD' ≫ (F.o.onB.act a).left) →
    ∃ (inc : D.P.A ⟶ D₁'.P.A) (pr : D₁'.P.A ⟶ D.P.A) (xi : D.X →+ D₁'.X) (xp : D₁'.X →+ D.X)
      (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D₁'.P.A D₁'.P.L).pull
        (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o₁.onB.act F.f) : G2 D.P.A ⟶ G2 D₁'.P.A).left)),
      IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o₁.onB.act F.e ∧ (∀ y, xp (xi y) = y) ∧
      (∀ z, xi (xp z) = F.e • z) ∧ (∀ y, D₁'.c (xi y) = D.c y ≫ inc) ∧
      (Function.Injective fun y => star F.e • F.f • xi y) ∧ (∀ z : D₁'.X, ∃ y, star F.e • z = star F.e • F.f • xi y) ∧
      w.IsGen ∧ ∀ a b z J J', Good D₁'.P.L z J → Good D.P.L z J' →
        val (D.tau a b) (𝟙 _) z J' =
          lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' *
            val (D₁'.tau (xi a) (F.f • xi b)) (𝟙 _) z J := by
  first | exact @GlobalTheory.FactorPull.pfactor_pull | exact GlobalTheory.FactorPull.pfactor_pull | (intros; apply GlobalTheory.FactorPull.pfactor_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinementIsFactorBaseChangeCanonicalMumfordFami
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumBC


open GlobalTheory.HalfBC GlobalTheory.PullLinear GlobalTheory.FactorPull in
set_option maxHeartbeats 1600000 in
theorem refine_factor_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsSemiAbelian G → Canon Q G P → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε → ∃ (D' : DegData R' (maximalIdeal R')) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal R') D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (inc : G₁ ⟶ G') (pr : G' ⟶ G₁) (π : G₁.left ⟶ G.left) (π₂ : (G2 G₁).left ⟶ (G2 G).left), IsSemiAbelian G' ∧ U'.toUnifPre.OLinear F.O F.o oA oG ∧ IsSemiAbelian G₁ ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 G₁ ∧ pr ≫ inc = oG.act F.e ∧ IsGrpPullback G₁ G (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso ((abelian₂ G' U'.LG.L).pull (lift (fst G₁ G₁ ≫ inc) (snd G₁ G₁ ≫ inc ≫ oG.act F.f) : G2 G₁ ⟶ G2 G').left) (P.pull π₂) := by
  intro R _ _ _ hCN Q G _ _ P hG hC R' _ _ _ ρ hCN' hρ hfin D ε hRef
  obtain ⟨hPL, D', F, A', G', _, _, U', oA, oG, inc, pr, hG', hlin, mi, mp, hip, hpi, hP⟩ := hC
  have hR := admissibleBase_of_completeNormalLocalCharZero hCN
  have hR' := admissibleBase_of_completeNormalLocalCharZero hCN'
  have hloc : IsLocalHom ρ := by
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ρ
      (RingHom.IsIntegral.of_finite hfin) (maximalIdeal R')
    have hc : (maximalIdeal R').comap ρ = maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ (maximalIdeal R').comap ρ := hc.symm ▸ (mem_maximalIdeal a).2 hna
    exact (mem_maximalIdeal _).1 this ha
  obtain ⟨D₁', hD', A₁', U₁', hU, oG₁, oA₁, h₁, h₂⟩ :=
    unif_pull hR hR' ρ hρ (map_maximalIdeal_le ρ) hG' U' F.O F.o oA oG hlin
  obtain ⟨m, o₁, hx, ho⟩ := degAct_pull GlobalTheory.firstFiveLaws.1.globalFns R R' ρ _ _ hD' F.O F.o
  have lin := oLinear_pull R R' _ _ ρ D' D₁' hD' A' A₁' G' _ (Iso.refl _) (by show IsMonHom (𝟙 _); infer_instance) U' U₁' hU
    F.O F.o o₁ oA oA₁ oG oG₁ hlin h₁ h₂ hx ho
  obtain ⟨inc', pr', xi, xp, w, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, b₉, b₁₀, b₁₁⟩ :=
    GlobalTheory.T.polarisedIdempotentFactor_pullback_refinement ρ hρ Q D'.toPre F D.toPre ε hRef D₁'.toPre hD' o₁ hx fun a => act_proj _ hD'.e.hom (ho a)
  let F₁ : Factor D.toPre D₁'.toPre :=
    { O := F.O, o := o₁, e := F.e, f := F.f, inc := inc', pr := pr', xi := xi, xp := xp, w := w, idem := F.idem,
      inc_hom := b₁, pr_hom := b₂, inc_pr := b₃, pr_inc := b₄, xp_xi := b₅, xi_xp := b₆, c_xi := b₇, inj := b₈,
      onto := b₉, w_gen := b₁₀, tau := b₁₁ }
  have alg : F₁.Alg := F.alg
  have ha : ∀ a, oG₁.act a = (Over.pullback (specOf ρ)).map (oG.act a) := fun a =>
    (Category.comp_id _).symm.trans ((h₁ a).trans (Category.id_comp _))
  have gG := isGrpPullback_pullback G (specOf ρ)
  have gG' := (isGrpPullback_pullback G' (specOf ρ)).congr rfl (Category.id_comp _).symm
  obtain ⟨wL, hwL, -⟩ := hU.lg
  refine ⟨D₁', F₁, alg, A₁', _, _, _, U₁', oA₁, oG₁, (Over.pullback (specOf ρ)).obj G, inferInstance, inferInstance,
    (Over.pullback (specOf ρ)).map inc, (Over.pullback (specOf ρ)).map pr, _, sqOf gG,
    IsSemiAbelian.pullback _ G' hG', lin, IsSemiAbelian.pullback _ G hG, inferInstance, inferInstance, ?_, ?_, gG,
    isSquare_sqOf gG, ?_⟩
  · rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id]
  · rw [← CategoryTheory.Functor.map_comp, hpi, ha]
  · have hm := lift_sq gG gG' (u := inc) (v := inc ≫ oG.act F.f) (u₁ := (Over.pullback (specOf ρ)).map inc)
      (v₁ := (Over.pullback (specOf ρ)).map inc ≫ oG₁.act F.f)
      ((congrArg (_ ≫ ·) (Category.id_comp _)).trans (map_left_fst _ _))
      ((congrArg (_ ≫ ·) (Category.id_comp _)).trans (by
        rw [ha, ← CategoryTheory.Functor.map_comp]; exact map_left_fst _ _))
    have H : LBIso _ _ := ⟨lamIso gG' wL, isGen_lamIso gG' wL hwL⟩
    have H1 : LBIso ((abelian₂ ((Over.pullback (specOf ρ)).obj G') U₁'.LG.L).pull
        (lift (fst _ _ ≫ (Over.pullback (specOf ρ)).map inc) (snd _ _ ≫ (Over.pullback (specOf ρ)).map inc ≫ oG₁.act F.f) :
          G2 ((Over.pullback (specOf ρ)).obj G) ⟶ G2 ((Over.pullback (specOf ρ)).obj G')).left)
        (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull (sqOf gG)) :=
      H.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullLinComb (abelian₂ G' U'.LG.L) _ (fun _ => sqOf gG) (fun _ => sqOf gG') _ _ fun _ => hm.symm)
    have H2 : LBIso (P.pull (sqOf gG))
        (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull (sqOf gG)) :=
      hP.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl)
    exact LBIso.trans (pull_isLB (DVR.linComb_isLB _ U₁'.LG.isLB _ _) _)
      (pull_isLB (pull_isLB (DVR.linComb_isLB _ U'.LG.isLB _ _) _) _) (pull_isLB hPL _) H1 (LBIso.symm H2)

end GlobalTheory.MumBC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinementIsFactorBaseChangeCanonicalMumfordFamiStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refinement_isFactor_baseChange_canonicalMumfordFamily : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsSemiAbelian G → Canon Q G P → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε → ∃ (D' : DegData R' (maximalIdeal R')) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal R') D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (inc : G₁ ⟶ G') (pr : G' ⟶ G₁) (π : G₁.left ⟶ G.left) (π₂ : (G2 G₁).left ⟶ (G2 G).left), IsSemiAbelian G' ∧ U'.toUnifPre.OLinear F.O F.o oA oG ∧ IsSemiAbelian G₁ ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 G₁ ∧ pr ≫ inc = oG.act F.e ∧ IsGrpPullback G₁ G (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso ((abelian₂ G' U'.LG.L).pull (lift (fst G₁ G₁ ≫ inc) (snd G₁ G₁ ≫ inc ≫ oG.act F.f) : G2 G₁ ⟶ G2 G').left) (P.pull π₂) := by
  first | exact @GlobalTheory.MumBC.refine_factor_baseChange | exact GlobalTheory.MumBC.refine_factor_baseChange | (intros; apply GlobalTheory.MumBC.refine_factor_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyUniformisesRefinements
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.CanonFam

theorem gm_iso {X : Scheme.{0}} {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (x : X) (p q : B.ι × A.ι)
    (hp : x ∈ B.U p.1 ⊓ A.U p.2) (hq : x ∈ B.U q.1 ⊓ A.U q.2) :
    gm (𝟙 X) x _ (w.s p) =
      gm (𝟙 X) x _ (B.g p.1 q.1) * (gm (𝟙 X) x _ (A.g p.2 q.2))⁻¹ * gm (𝟙 X) x _ (w.s q) := by
  have hm : (𝟙 X : X ⟶ X) x ∈ B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2) := ⟨hp, hq⟩
  have e := congrArg (gm (𝟙 X) x (B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2))) (hw p q)
  exact (gm_res _ x _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) x p q hm) (gm_res _ x _ hm _))))

theorem lbIso_trans {X : Scheme.{0}} {A B C : LB X} (hA : A.IsLB) (hB : B.IsLB) (H : LBIso A B) (H' : LBIso B C) :
    LBIso A C := by
  obtain ⟨w, hw⟩ := H
  obtain ⟨w', hw'⟩ := H'

  have cself : ∀ (x : X) (r : C.ι) (p : B.ι), x ∈ C.U r → x ∈ B.U p →
      gm (𝟙 X) x (C.U r ⊓ C.U r) (C.g r r) = 1 := by
    intro x r p hr hp
    have e := gm_iso hw' x (r, p) (r, p) ⟨hr, hp⟩ ⟨hr, hp⟩
    rw [gm_self hB (𝟙 X) x hp, inv_one, _root_.mul_one] at e
    exact mul_eq_right.1 e.symm
  have glue : ∀ (r : C.ι) (i : A.ι), ∃ s : Γ(X, C.U r ⊓ A.U i)ˣ, ∀ (x : X) (p : B.ι), x ∈ C.U r → x ∈ B.U p →
      x ∈ A.U i → gm (𝟙 X) x _ s = gm (𝟙 X) x _ (w'.s (r, p)) * gm (𝟙 X) x _ (w.s (p, i)) := by
    intro r i
    let W : B.ι → X.Opens := fun p => C.U r ⊓ B.U p ⊓ A.U i
    have l₀ : ∀ p, W p ≤ C.U r ⊓ A.U i := fun p x hx => ⟨hx.1.1, hx.2⟩
    have l₁ : ∀ p, W p ≤ C.U r ⊓ B.U p := fun p x hx => hx.1
    have l₂ : ∀ p, W p ≤ B.U p ⊓ A.U i := fun p x hx => ⟨hx.1.2, hx.2⟩
    let u : ∀ p, Γ(X, W p)ˣ := fun p => res (l₁ p) (w'.s (r, p)) * res (l₂ p) (w.s (p, i))
    have hu : ∀ (x : X) (p : B.ι) (hx : x ∈ W p), gm (𝟙 X) x (W p) (u p) =
        gm (𝟙 X) x _ (w'.s (r, p)) * gm (𝟙 X) x _ (w.s (p, i)) := fun x p hx =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x (l₁ p) hx _) (gm_res _ x (l₂ p) hx _))
    obtain ⟨s, hs⟩ := glue_unit (C.U r ⊓ A.U i) W l₀ (fun x hx => by
        obtain ⟨p, hp⟩ := exists_chart hB x
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, ⟨⟨hx.1, hp⟩, hx.2⟩⟩) u (fun p p' x hx => by
        rw [hu x p hx.1, hu x p' hx.2]
        have hr : x ∈ C.U r := hx.1.1.1
        have hp : x ∈ B.U p := hx.1.1.2
        have hp' : x ∈ B.U p' := hx.2.1.2
        have hi : x ∈ A.U i := hx.1.2
        rw [gm_iso hw' x (r, p) (r, p') ⟨hr, hp⟩ ⟨hr, hp'⟩, gm_iso hw x (p, i) (p', i) ⟨hp, hi⟩ ⟨hp', hi⟩]
        simp only []
        rw [cself x r p hr hp, gm_self hA (𝟙 X) x hi, inv_one]
        simp only [_root_.one_mul, _root_.mul_one]
        rw [_root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun x p hr hp hi => ?_⟩
    have hx : x ∈ W p := ⟨⟨hr, hp⟩, hi⟩
    exact (gm_res _ x (l₀ p) hx s).symm.trans ((congrArg (gm (𝟙 X) x (W p)) (hs p)).trans (hu x p hx))
  choose s hs using glue
  refine ⟨⟨fun q => s q.1 q.2⟩, fun q q' => unit_ext fun x hx => ?_⟩
  obtain ⟨p, hp⟩ := exists_chart hB x
  have hr : x ∈ C.U q.1 := hx.1.1
  have hi : x ∈ A.U q.2 := hx.1.2
  have hr' : x ∈ C.U q'.1 := hx.2.1
  have hi' : x ∈ A.U q'.2 := hx.2.2
  have hm : (𝟙 X : X ⟶ X) x ∈ C.U q.1 ⊓ A.U q.2 ⊓ (C.U q'.1 ⊓ A.U q'.2) := hx
  refine (gm_res _ x _ hx _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A C (𝟙 X) x q q' hm) (gm_res _ x _ hx _))).symm)
  show gm (𝟙 X) x _ (s q.1 q.2) = _ * _ * gm (𝟙 X) x _ (s q'.1 q'.2)
  rw [hs q.1 q.2 x p hr hp hi, hs q'.1 q'.2 x p hr' hp hi',
    gm_iso hw' x (q.1, p) (q'.1, p) ⟨hr, hp⟩ ⟨hr', hp⟩, gm_iso hw x (p, q.2) (p, q'.2) ⟨hp, hi⟩ ⟨hp, hi'⟩]
  simp only []
  rw [gm_self hB (𝟙 X) x hp, inv_one]
  simp only [_root_.one_mul, _root_.mul_one]
  ac_rfl

theorem base_of_isCN {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h : IsCN R) : Base R :=
  ⟨⟨h.1, inferInstance, h.2.1, h.2.2.1⟩, h.2.2.2⟩

end GlobalTheory.Mum.CanonFam


open GlobalTheory.Mum.CanonFam in
theorem GlobalTheory.Mum.CanonFam.exists_unif_refines : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsSemiAbelian G → Canon Q G P → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε → ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G.left) (π₂ : (G2 G').left ⟶ (G2 G).left) (A : PolAV (Sp (FractionRing R'))) (U : Unif (maximalIdeal R') D A G'), IsGrpPullback G' G (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  intro R _ _ _ hR Q G _ _ P hG hC R' _ _ _ ρ hR' hinj hfin D ε hRef
  obtain ⟨D', F, hF, A', G', _, _, U', oA, oG, G₁, _, _, inc, pr, π, π₂, hG', hlin, hG₁, hinc, hpr, hip, hpi, hpb, hsq,
    hlb⟩ := GlobalTheory.T.refinement_isFactor_baseChange_canonicalMumfordFamily R hR Q G P hG hC R' ρ hR' hinj hfin D ε hRef
  obtain ⟨A, U, hU⟩ := GlobalTheory.T.idempotent_image_uniformised_by_factor_data R' (base_of_isCN hR') D D' F hF A' G' hG' U' oA oG hlin G₁ hG₁ inc pr hinc hpr hip hpi
  refine ⟨G₁, inferInstance, inferInstance, π, π₂, A, U, hpb, hsq, ?_⟩
  have l1 : (abelian₂ G₁ U.LG.L).IsLB := DVR.linComb_isLB _ U.LG.isLB _ _
  have l2 : (abelian₂ G' U'.LG.L).IsLB := DVR.linComb_isLB _ U'.LG.isLB _ _
  exact lbIso_trans l1 (pull_isLB l2 _) hU hlb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyUniformisesRefinementsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_mumford_family_uniformises_refinements : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsSemiAbelian G → Canon Q G P → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε → ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G.left) (π₂ : (G2 G').left ⟶ (G2 G).left) (A : PolAV (Sp (FractionRing R'))) (U : Unif (maximalIdeal R') D A G'), IsGrpPullback G' G (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  first | exact @GlobalTheory.Mum.CanonFam.exists_unif_refines | exact GlobalTheory.Mum.CanonFam.exists_unif_refines | (intros; apply GlobalTheory.Mum.CanonFam.exists_unif_refines <;> assumption)
end
