module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombPullbackTransportIsoWithValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeClsPullHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProd.GAdjFst

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem psum_comp_hom {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H) [IsMonHom f]
    {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    psum G x I ≫ f = psum H (fun i => x i ≫ f) I :=
  psum_hom (MonoidHom.mk' (fun z : T ⟶ G => z ≫ f) fun a b => MonObj.mul_comp a b f) x I

theorem cubeCls_pull_hom {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H)
    [IsMonHom f] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic H.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G x (pull f.left c) = GlobalTheory.ZH.EndoExtend.cubeCls H (fun i => x i ≫ f) c := by
  unfold GlobalTheory.ZH.EndoExtend.cubeCls
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← pull_comp, ← Over.comp_left, psum_comp_hom]

theorem cubeCls_add {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G))
    (a b : Pic G.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G x (a + b) = GlobalTheory.ZH.EndoExtend.cubeCls G x a + GlobalTheory.ZH.EndoExtend.cubeCls G x b := by
  unfold GlobalTheory.ZH.EndoExtend.cubeCls
  simp only [map_add (f := _), smul_add, Finset.sum_add_distrib]

theorem cubeCls_one_left {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (y : T ⟶ G) (c : Pic G.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G ![1, y] c = 0 := by
  classical
  unfold GlobalTheory.ZH.EndoExtend.cubeCls
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum G ![1, y] I).left c) (fun _ => rfl)).trans ?_
  have u : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have p₀ : psum G ![1, y] ∅ = 1 := rfl
  have p₁ : psum G ![1, y] {0} = 1 := _root_.mul_one 1
  have p₂ : psum G ![1, y] {1} = y := _root_.mul_one y
  have p₄ : psum G ![1, y] {0, 1} = 1 * y := congrArg (1 * ·) (_root_.mul_one y)
  rw [u, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, p₀, p₁, p₂, p₄, _root_.one_mul]
  have c₁ : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  simp only [c₁, Finset.card_singleton, Finset.card_empty]
  norm_num

end GlobalTheory.MumProd.GAdjFst

theorem GlobalTheory.MumProd.gAdj_prod_fst : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hU
  obtain ⟨w, hw⟩ := hU.wL
  have hL := U.LG.isLB
  have hL₁ := U₁.LG.isLB
  have hL₂ := U₂.LG.isLB
  have hE : (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left).IsLB :=
    GlobalTheory.CechPic.isLB_tens (pull_isLB hL₁ _) (pull_isLB hL₂ _)
  have e0 : GlobalTheory.CechPic.cls _ hL = GlobalTheory.CechPic.pull (fst G₁ G₂).left (GlobalTheory.CechPic.cls _ hL₁) +
      GlobalTheory.CechPic.pull (snd G₁ G₂).left (GlobalTheory.CechPic.cls _ hL₂) :=
    (GlobalTheory.CechPic.cls_eq_iff hL hE).2 ⟨w, hw⟩
  unfold GAdj
  refine (GlobalTheory.CechPic.cls_eq_iff _ _).1 ((GlobalTheory.ZH.EndoExtend.cls_cubeLB (G₁ ⊗ G₂) _ hL).trans
    (Eq.trans ?_ (GlobalTheory.ZH.EndoExtend.cls_cubeLB G₁ _ hL₁).symm))
  rw [e0,
    GlobalTheory.MumProd.GAdjFst.cubeCls_add, GlobalTheory.MumProd.GAdjFst.cubeCls_pull_hom,
    GlobalTheory.MumProd.GAdjFst.cubeCls_pull_hom]
  have h₁ : (fun i => (![fst G₁ (G₁ ⊗ G₂) ≫ lift (𝟙 G₁) 1, snd G₁ (G₁ ⊗ G₂)] : Fin 2 → _) i ≫ fst G₁ G₂) =
      ![fst G₁ (G₁ ⊗ G₂), snd G₁ (G₁ ⊗ G₂) ≫ fst G₁ G₂] := by
    funext i; fin_cases i <;> simp
  have h₂ : (fun i => (![fst G₁ (G₁ ⊗ G₂) ≫ lift (𝟙 G₁) 1, snd G₁ (G₁ ⊗ G₂)] : Fin 2 → _) i ≫ snd G₁ G₂) =
      ![1, snd G₁ (G₁ ⊗ G₂) ≫ snd G₁ G₂] := by
    funext i; fin_cases i <;> simp
  rw [h₁, h₂, GlobalTheory.MumProd.GAdjFst.cubeCls_one_left, add_zero]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTauLineBundleCoordinateEqExp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTauLineBundleCoordinateEqExp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.TauNorm

theorem valF_id {F : Type} [Field F] (U : (Sp F).Opens) (h : ⊤ ≤ U) (f : Γ(Sp F, U)) :
    valF (𝟙 (Sp F)) U f =
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
        (((Sp F).presheaf.map (homOfLE h).op).hom f) := by
  have h' : ⊤ ≤ (𝟙 (Sp F) : Sp F ⟶ Sp F) ⁻¹ᵁ U := h
  unfold valF
  rw [dite_eq_left h']
  congr 1

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
  {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p}

theorem norm_psiCoord (u : ρ.UTest p y₀) (l : u.Lab) (χ : u.D.toPre.X)
    (x : (FractionRing u.V)ˣ) (hx : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord u.D.toPre χ x) :
    ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (x : FractionRing u.V)‖ =
      Real.exp (-l.q χ) := by
  obtain ⟨j, h, hj, rfl⟩ := hx
  have := l.q_eq χ j hj
  rw [valF_id _ h] at this
  exact this

theorem norm_unit (u : ρ.UTest p y₀) (w : (u.V)ˣ) :
    ‖algebraMap (FractionRing u.V) (PadicAlgCl p)
      (algebraMap u.V (FractionRing u.V) (w : u.V))‖ = 1 := by
  have h1 := (u.norm_le (algebraMap u.V (FractionRing u.V) (w : u.V))).2 ⟨_, rfl⟩
  have h2 := (u.norm_le (algebraMap u.V (FractionRing u.V) ((w⁻¹ : (u.V)ˣ) : u.V))).2 ⟨_, rfl⟩
  have h3 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p)
      (algebraMap u.V (FractionRing u.V) (w : u.V))‖ *
      ‖algebraMap (FractionRing u.V) (PadicAlgCl p)
      (algebraMap u.V (FractionRing u.V) ((w⁻¹ : (u.V)ˣ) : u.V))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = _ := h3.symm
    _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) h2

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (a b : u.D.toPre.X) (x : (FractionRing u.V)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord u.D.toPre a b x → ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (x : FractionRing u.V)‖ = Real.exp (-(l.q (a + b) - l.q a - l.q b)) := by
  intro o Ω _ _ _ S ρ p _ y₀ u l a b x hx
  obtain ⟨x₁, h₁⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord u.D.toPre (a + b)
  obtain ⟨x₂, h₂⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord u.D.toPre a
  obtain ⟨x₃, h₃⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord u.D.toPre b
  obtain ⟨w, hw⟩ := GlobalTheory.TauCoordQuot.main u.V u.D.toPre a b x x₁ x₂ x₃ hx h₁ h₂ h₃
  rw [hw, map_mul, map_mul, map_mul, map_inv₀, map_inv₀, norm_mul, norm_mul, norm_mul,
    norm_inv, norm_inv, norm_unit, norm_psiCoord u l _ _ h₁, norm_psiCoord u l _ _ h₂,
    norm_psiCoord u l _ _ h₃, _root_.one_mul, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  ring

end GlobalTheory.Poinc.TauNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTauLineBundleCoordinateEqExpStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_tauLineBundleCoordinate_eq_exp : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (a b : u.D.toPre.X) (x : (FractionRing u.V)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord u.D.toPre a b x → ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (x : FractionRing u.V)‖ = Real.exp (-(l.q (a + b) - l.q a - l.q b)) := by
  first | exact @GlobalTheory.Poinc.TauNorm.main | exact GlobalTheory.Poinc.TauNorm.main | (intros; apply GlobalTheory.Poinc.TauNorm.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoGenericOriginOneTautologicalBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoGenericOriginOneTautologicalBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem degPre_c_zero {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) : D.c 0 = 1 := by
  have h : D.c 0 * D.c 0 = D.c 0 := by
    have := D.c_add 0 0
    rw [add_zero] at this
    exact this.symm
  exact mul_eq_left.1 h

theorem val_tau_zero_zero {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (hT : D.TauBimult)
    (z : (TK V).left) (J : ((TK V).left ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) :
    val (D.tau 0 0) (𝟙 _) z J = 1 := by
  have h := (val_mul hJ _ _ (𝟙 _)).symm.trans ((val_corr hJ (hT 0 0 0) (𝟙 _)).trans (val_mul hJ _ _ (𝟙 _)))
  have e : ∀ a : D.X, a = 0 → val (D.tau a 0) (𝟙 _) z J = val (D.tau 0 0) (𝟙 _) z J := by
    rintro a rfl; rfl
  rw [e _ (add_zero 0)] at h
  have f : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 0 0 0)) (𝟙 _) z J = 1 := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp]
    show cubV D.cub z J (toUnit (TK V) ≫ D.c 0) (toUnit (TK V) ≫ D.c 0) (toUnit (TK V) ≫ D.c 0) = 1
    rw [degPre_c_zero, MonObj.comp_one]
    exact (isCub_cubV D.cub hJ).face _ _
  rw [f, _root_.mul_one] at h
  exact mul_eq_left.1 h.symm

theorem tautBase_c₀_zero {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) : T.c₀ 0 = 1 :=
  mul_eq_left.1 ((T.c₀_add 0 0).symm.trans (by rw [add_zero]))

theorem val_τ₀_zero_zero {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W)
    (z : (𝟙_ (Over (Sp W))).left) (J) (hJ : Good T.M.L z J) : val (T.τ₀ 0 0) (𝟙 _) z J = 1 := by
  have h := T.τ₀_add 0 0 0 z J hJ
  have f : cubV T.cub z J (T.c₀ 0) (T.c₀ 0) (T.c₀ 0) = 1 := by
    rw [tautBase_c₀_zero]; exact (isCub_cubV T.cub hJ).face _ _
  rw [f, _root_.mul_one, add_zero] at h
  exact mul_eq_left.1 h.symm

theorem val_τ₀_zero_at {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {Z : Scheme.{0}}
    (r : Z ⟶ (𝟙_ (Over (Sp W))).left) (z : Z) (J : (Z ⟶ T.B.left) → T.M.L.ι) (hJ : Good T.M.L z J) :
    val (T.τ₀ 0 0) r z J = 1 := by
  have c : LB.Gen.Corr T.M.L _ _ _ _ (T.τ₀ 0 0) (LB.oneGen T.M.L) :=
    corr_of_val T.M.isLB fun y J' hJ' => (val_τ₀_zero_zero T y J' hJ').trans (val_one _).symm
  exact (val_corr hJ c r).trans (val_one r)

theorem lamVal_origin_of_from : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (z : (TK V).left) (J : ((TK V).left ⟶ T.B.left) → T.M.L.ι) (J' : ((TK V).left ⟶ D.P.A.left) → D.P.L.ι), Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (1 : TK V ⟶ D.P.A) (1 : TK V ⟶ D.P.A)).left z J J' = 1 := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hT hF z J J' hJ hJ'
  obtain ⟨k, hk, hv⟩ := hF.2.2.2.2 0 0
  have h := hv z J J' hJ hJ'
  have k1 : k = 1 := by
    ext
    rw [hk]
    simp
  have e0 : ((n : ℤ) • e 0) = 0 := by rw [map_zero, smul_zero]
  rw [k1, val_tau_zero_zero D hT z J' hJ', e0, val_τ₀_zero_at T _ z J hJ, degPre_c_zero, MonObj.comp_one] at h
  have u1 : unitOn (1 : (FractionRing V)ˣ) = 1 := map_one _
  simp only [u1, map_one, _root_.one_mul, _root_.mul_one] at h
  exact h.symm

end GlobalTheory.TInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoGenericOriginOneTautologicalBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundleIso_generic_origin_one_tautologicalBase : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (z : (TK V).left) (J : ((TK V).left ⟶ T.B.left) → T.M.L.ι) (J' : ((TK V).left ⟶ D.P.A.left) → D.P.L.ι), Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (1 : TK V ⟶ D.P.A) (1 : TK V ⟶ D.P.A)).left z J J' = 1 := by
  first | exact @GlobalTheory.TInj.lamVal_origin_of_from | exact GlobalTheory.TInj.lamVal_origin_of_from | (intros; apply GlobalTheory.TInj.lamVal_origin_of_from <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumFractionFieldEqMulIntegralCongr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumFractionFieldEqMulIntegralCongr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.Poinc.AdicTerm

theorem eq_zero_of_mem_pow_smul {V E : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    [AddCommGroup E] [Module V E] (N : Submodule V E) (hN : N.FG) (w : E)
    (h : ∀ n : ℕ, w ∈ maximalIdeal V ^ n • N) : w = 0 := by
  have hw : w ∈ N := Submodule.smul_le_right (h 0)
  haveI : Module.Finite V N := Module.Finite.iff_fg.mpr hN
  have hb := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N) (maximalIdeal V)
    (maximalIdeal.isMaximal V).ne_top
  have hm : (⟨w, hw⟩ : N) ∈ (⨅ n : ℕ, maximalIdeal V ^ n • ⊤ : Submodule V N) := by
    rw [Submodule.mem_iInf]
    intro n
    exact (Submodule.mem_smul_top_iff _ N _).mpr (h n)
  rw [hb, Submodule.mem_bot] at hm
  exact congrArg Subtype.val hm

theorem sumI_smul {V E : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    [AddCommGroup E] [Module V E] {Ix : Type} (i₀ : Ix) (x : Ix → E) (y : Ix → V) (k v : E)
    (hx : ∀ i, x i = y i • k) (hy : ∀ i, i ≠ i₀ → y i ∈ maximalIdeal V)
    (hs : SumI (maximalIdeal V) x v) :
    ∃ S : V, v = S • k ∧ S - y i₀ ∈ maximalIdeal V := by
  classical
  obtain ⟨N, hN, -, -, hS⟩ := hs
  let P : Submodule V E := Submodule.map (LinearMap.toSpanSingleton V E k) (maximalIdeal V)
  have key : P.mkQ (v - y i₀ • k) = 0 := by
    refine eq_zero_of_mem_pow_smul (N.map P.mkQ) (hN.map _) _ fun n => ?_
    obtain ⟨S, hS⟩ := hS n
    have h1 := hS (insert i₀ S) (Finset.subset_insert _ _)
    have h2 : P.mkQ (v - ∑ i ∈ insert i₀ S, x i) ∈ maximalIdeal V ^ n • N.map P.mkQ := by
      rw [← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem h1
    have h3 : ∑ i ∈ (insert i₀ S).erase i₀, x i ∈ P := by
      refine Submodule.sum_mem _ fun i hi => ?_
      exact ⟨y i, hy i (Finset.ne_of_mem_erase hi), by simp [hx i]⟩
    have h4 : P.mkQ (∑ i ∈ (insert i₀ S).erase i₀, x i) = 0 :=
      (Submodule.Quotient.mk_eq_zero P).mpr h3
    have h5 : v - y i₀ • k =
        (v - ∑ i ∈ insert i₀ S, x i) + ∑ i ∈ (insert i₀ S).erase i₀, x i := by
      rw [← Finset.add_sum_erase _ x (Finset.mem_insert_self i₀ S), hx i₀]
      abel
    rw [h5, map_add (f := _), h4, add_zero]
    exact h2
  obtain ⟨a, ha, hak⟩ := (Submodule.Quotient.mk_eq_zero P).mp key
  refine ⟨y i₀ + a, ?_, by simpa using ha⟩
  have hak' : a • k = v - y i₀ • k := by simpa using hak
  rw [add_smul, hak']
  abel

theorem sumF_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (Ix : Type) (i₀ : Ix) (x : Ix → FractionRing V) (y : Ix → V) (κ v : FractionRing V), (∀ i, x i = κ * algebraMap V (FractionRing V) (y i)) → (∀ i, i ≠ i₀ → y i ∈ maximalIdeal V) → SumF (maximalIdeal V) (FractionRing V) x v → ∃ S : V, v = κ * algebraMap V (FractionRing V) S ∧ S - y i₀ ∈ maximalIdeal V := by
  intro V _ _ _ _ Ix i₀ x y κ v hx hy hs
  have h := @sumI_smul V (FractionRing V) _ _ _ _
    (Module.compHom (FractionRing V) (algebraMap V (FractionRing V))) Ix i₀ x y κ v
    (fun i => (hx i).trans (mul_comm _ _)) hy hs
  obtain ⟨S, h1, h2⟩ := h
  exact ⟨S, h1.trans (mul_comm _ _), h2⟩

end GlobalTheory.Poinc.AdicTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumFractionFieldEqMulIntegralCongrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicSum_fractionField_eq_mul_integral_congr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (Ix : Type) (i₀ : Ix) (x : Ix → FractionRing V) (y : Ix → V) (κ v : FractionRing V), (∀ i, x i = κ * algebraMap V (FractionRing V) (y i)) → (∀ i, i ≠ i₀ → y i ∈ maximalIdeal V) → SumF (maximalIdeal V) (FractionRing V) x v → ∃ S : V, v = κ * algebraMap V (FractionRing V) S ∧ S - y i₀ ∈ maximalIdeal V := by
  first | exact @GlobalTheory.Poinc.AdicTerm.sumF_mul | exact GlobalTheory.Poinc.AdicTerm.sumF_mul | (intros; apply GlobalTheory.Poinc.AdicTerm.sumF_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterMapOfIntegralMatrixAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterMapOfIntegralMatrixAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.MatChar

theorem charMap_matrix : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (A₀ : PolAV (Sp (FractionRing V₁))) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → ∀ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (f : G ⟶ G) (m : D.toPre.X →+ D.toPre.X), IsMonHom f → EndChar U f m → (∀ u, f ≫ q u = (List.ofFn fun v => q v ^ a u v).prod) → ∀ u χ, m (c u χ) = ∑ v, a u v • c v χ := by
  intro V₁ _ _ _ hCN D₀ A₀ G₀ _ _ hG₀ U₀ D P G _ _ hG U q hq c hc a f m hf hm hfq u χ
  have hB : GlobalTheory.Mum.Base V₁ := ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hCN.2.2.2⟩
  obtain ⟨-, hone, hmul⟩ := GlobalTheory.Poinc.Eq8.torMatch_id_one_mul V₁ hB G₀ hG₀ D₀ A₀ U₀ G hG D P U
  have huniq : ∀ (β : G.left ⟶ G₀.left) (ρ ρ' : D₀.toPre.X →+ D.toPre.X), TorMatch U₀ U (RingHom.id V₁) β ρ →
      TorMatch U₀ U (RingHom.id V₁) β ρ' → ρ = ρ' := fun β ρ ρ' =>
    GlobalTheory.Poinc.Eq8.torMatch_unique V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G hG D P U (RingHom.id V₁) β Function.injective_id ρ ρ'
  have hinv : ∀ (p : G ⟶ G₀) [IsMonHom p] (ρ : D₀.toPre.X →+ D.toPre.X), TorMatch U₀ U (RingHom.id V₁) p.left ρ →
      TorMatch U₀ U (RingHom.id V₁) (p⁻¹).left (-ρ) := by
    intro p _ ρ hp
    obtain ⟨ρ', hρ'⟩ := GlobalTheory.Poinc.HomTor.exists_torMatch V₁ hB G₀ hG₀ D₀ A₀ U₀ G hG D P U p⁻¹ inferInstance
    have h1 := hmul p p⁻¹ ρ ρ' hp hρ'
    rw [mul_inv_cancel] at h1
    have h2 : ρ + ρ' = 0 := huniq _ _ _ h1 hone
    have h3 : ρ' = -ρ := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h2
    rwa [← h3]
  have hnpow : ∀ (p : G ⟶ G₀) (ρ : D₀.toPre.X →+ D.toPre.X) (n : ℕ), TorMatch U₀ U (RingHom.id V₁) p.left ρ →
      TorMatch U₀ U (RingHom.id V₁) (p ^ n).left (n • ρ) := by
    intro p ρ n hp
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact hone
    | succ n ih => rw [pow_succ, succ_nsmul]; exact hmul _ _ _ _ ih hp
  have hzpow : ∀ (p : G ⟶ G₀) [IsMonHom p] (ρ : D₀.toPre.X →+ D.toPre.X) (k : ℤ),
      TorMatch U₀ U (RingHom.id V₁) p.left ρ → TorMatch U₀ U (RingHom.id V₁) (p ^ k).left (k • ρ) := by
    intro p _ ρ k hp
    cases k with
    | ofNat n => rw [Int.ofNat_eq_coe, zpow_natCast, natCast_zsmul]; exact hnpow p ρ n hp
    | negSucc n =>
      rw [zpow_negSucc, ← inv_pow, negSucc_zsmul, ← smul_neg]
      exact hnpow _ _ (n + 1) (hinv p ρ hp)
  have hprod : ∀ (n : ℕ) (g : Fin n → (G ⟶ G₀)) (r : Fin n → (D₀.toPre.X →+ D.toPre.X)),
      (∀ i, TorMatch U₀ U (RingHom.id V₁) (g i).left (r i)) →
      TorMatch U₀ U (RingHom.id V₁) (List.ofFn g).prod.left (∑ i, r i) := by
    intro n
    induction n with
    | zero => intro g r _; rw [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]; exact hone
    | succ n ih =>
      intro g r h
      rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
      exact hmul _ _ _ _ (h 0) (ih _ _ fun i => h i.succ)
  have hright : TorMatch U₀ U (RingHom.id V₁) (f ≫ q u).left (∑ v, a u v • c v) := by
    rw [hfq u]
    exact hprod 8 _ _ fun v => haveI := hq v; hzpow (q v) (c v) (a u v) (hc v)
  have hleft := GlobalTheory.Poinc.Eq8.torMatch_comp V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G hG D P U (RingHom.id V₁) (q u).left
    V₁ hB G hG D P U (RingHom.id V₁) f.left Function.injective_id (fun _ hk => hk) (c u) m (hc u)
    (GlobalTheory.Poinc.TorEnd.torMatch_of_endChar V₁ hB G hG D P U f hf m hm)
  rw [RingHom.id_comp, ← Over.comp_left] at hleft
  have e := huniq _ _ _ hleft hright
  have e' := DFunLike.congr_fun e χ
  simpa using e'

end GlobalTheory.Poinc.MatChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterMapOfIntegralMatrixActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterMap_of_integral_matrix_action : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (A₀ : PolAV (Sp (FractionRing V₁))) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → ∀ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (f : G ⟶ G) (m : D.toPre.X →+ D.toPre.X), IsMonHom f → EndChar U f m → (∀ u, f ≫ q u = (List.ofFn fun v => q v ^ a u v).prod) → ∀ u χ, m (c u χ) = ∑ v, a u v • c v χ := by
  first | exact @GlobalTheory.Poinc.MatChar.charMap_matrix | exact GlobalTheory.Poinc.MatChar.charMap_matrix | (intros; apply GlobalTheory.Poinc.MatChar.charMap_matrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnReprPullbackComplexFormFderiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnReprPullbackComplexFormFderiv
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.PullSmooth

theorem repr_mul {m : ℕ} (a b : Alt m) (S : Finset (Fin (m + m))) :
    (bas m).repr (a * b) S = ∑ S₁, ∑ S₂, (bas m).repr a S₁ * (bas m).repr b S₂ *
      (bas m).repr (bas m S₁ * bas m S₂) S := by
  conv_lhs => rw [← (bas m).sum_repr a, ← (bas m).sum_repr b]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul]
  simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]

theorem entries_smooth {m n : ℕ} {τ : V m → V n} {U : Set (V m)} (hU : IsOpen U) (hτ : DifferentiableOn ℂ τ U)
    (v : V m) (a : Fin n) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℂ τ x v a) U ∧ ContDiffOn ℝ ∞ (fun x => conj (fderiv ℂ τ x v a)) U := by
  have h₁ : ContDiffOn ℂ ∞ (fun x => fderiv ℂ τ x) U :=
    ContDiffOn.fderiv_of_isOpen (n := ω) (m := ∞)
      (((GlobalTheory.SCV.analyticOnNhd_iff_differentiableOn hU).2 hτ).contDiffOn hU.uniqueDiffOn) hU le_top
  have h₂ : ContDiffOn ℂ ∞ (fun x => fderiv ℂ τ x v a) U :=
    (EuclideanSpace.proj a : V n →L[ℂ] ℂ).contDiff.comp_contDiffOn (h₁.clm_apply contDiffOn_const)
  have h₃ : ContDiffOn ℝ ∞ (fun x => fderiv ℂ τ x v a) U := h₂.restrict_scalars ℝ
  exact ⟨h₃, Complex.conjCLE.contDiff.comp_contDiffOn h₃⟩

theorem contDiffOn_repr_pull_fderiv : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (γ : Alt n), IsOpen U →
    DifferentiableOn ℂ τ U → ∀ S, ContDiffOn ℝ ∞ (fun x => (bas m).repr (pull (fderiv ℂ τ x) γ) S) U := by
  intro m n τ U γ hU hτ
  induction γ using ExteriorAlgebra.induction with
  | algebraMap r =>
    intro S
    simp only [AlgHom.commutes]
    exact contDiffOn_const
  | ι u =>
    intro S
    have hcoef : ∀ x, (bas m).repr (pull (fderiv ℂ τ x) (ExteriorAlgebra.ι ℂ u)) S =
        ((bas m).coord S ∘ₗ ExteriorAlgebra.ι ℂ)
          (Matrix.toLin' (Matrix.fromBlocks (Matrix.of fun b a => fderiv ℂ τ x (coordVec b) a) 0 0
            (Matrix.of fun b a => conj (fderiv ℂ τ x (coordVec b) a))) u) := by
      intro x
      simp [pull, ExteriorAlgebra.map_apply_ι]
    simp_rw [hcoef]
    refine (LinearMap.toContinuousLinearMap ((bas m).coord S ∘ₗ ExteriorAlgebra.ι ℂ)).contDiff.restrict_scalars ℝ
      |>.comp_contDiffOn ?_
    refine contDiffOn_pi.2 fun i => ?_
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    refine ContDiffOn.sum fun j _ => ContDiffOn.mul ?_ contDiffOn_const
    rcases i with i | i <;> rcases j with j | j
    · simp only [Matrix.fromBlocks_apply₁₁, Matrix.of_apply]; exact (entries_smooth hU hτ _ _).1
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]; exact contDiffOn_const
    · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]; exact contDiffOn_const
    · simp only [Matrix.fromBlocks_apply₂₂, Matrix.of_apply]; exact (entries_smooth hU hτ _ _).2
  | mul a b ha hb =>
    intro S
    have e : (fun x => (bas m).repr (pull (fderiv ℂ τ x) (a * b)) S) = fun x => ∑ S₁, ∑ S₂,
        (bas m).repr (pull (fderiv ℂ τ x) a) S₁ * (bas m).repr (pull (fderiv ℂ τ x) b) S₂ *
          (bas m).repr (bas m S₁ * bas m S₂) S := funext fun x => by rw [map_mul, repr_mul]
    rw [e]
    exact ContDiffOn.sum fun S₁ _ => ContDiffOn.sum fun S₂ _ =>
      ((ha S₁).mul (hb S₂)).mul contDiffOn_const
  | add a b ha hb =>
    intro S
    simp only [map_add (f := _), Finsupp.add_apply]
    exact (ha S).add (hb S)

end GlobalTheory.PullSmooth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnReprPullbackComplexFormFderivStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_repr_pullbackComplexForm_fderiv : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (γ : Alt n), IsOpen U → DifferentiableOn ℂ τ U →
    ∀ S, ContDiffOn ℝ ∞ (fun x => (bas m).repr (pull (fderiv ℂ τ x) γ) S) U := by
  first | exact @GlobalTheory.PullSmooth.contDiffOn_repr_pull_fderiv | exact GlobalTheory.PullSmooth.contDiffOn_repr_pull_fderiv | (intros; apply GlobalTheory.PullSmooth.contDiffOn_repr_pull_fderiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupOfPointEqAlongModelHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupOfPointEqAlongModelHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.HHFibre

open GlobalTheory.ZH GlobalTheory.ZH.RatModel

theorem isHom_of_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M Y : RatModel o Ω} {q : Y.Z ⟶ M.Z}
    (hq : Y.pt ≫ q = M.pt) : M.IsHom Y (AlgHom.id o Ω) q := by
  show Y.pt ≫ q = spMap (AlgHom.id o Ω).toRingHom ≫ M.pt
  rw [hq]
  have : spMap (AlgHom.id o Ω).toRingHom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 _
    rw [← Spec.map_id]; rfl
  rw [this, Category.id_comp]

theorem exists_pt (X : Scheme.{0}) (w : X) : ∃ (K : Type) (_ : Field K) (y : Sp K ⟶ X),
    y (IsLocalRing.closedPoint K) = w :=
  ⟨X.residueField w, inferInstance, X.fromSpecResidueField w, Scheme.fromSpecResidueField_apply _ _⟩

theorem isUnit_of_isUnit_comap {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M Y : RatModel o Ω}
    {q : Y.Z ⟶ M.Z} (hq : M.IsHom Y (AlgHom.id o Ω) q) (w : Y.Z) {a : Ω} (ha : a ∈ M.O (q w))
    (ha' : a ∈ Y.O w) (hu : IsUnit (⟨a, ha'⟩ : Y.O w)) : IsUnit (⟨a, ha⟩ : M.O (q w)) := by
  obtain ⟨K, _, y, hy0⟩ := exists_pt Y.Z w
  have hy : Set.range y = {w} := hy0 ▸ range_eq_singleton y (IsLocalRing.closedPoint K)
  have hyq : Set.range (y ≫ q) = {q w} := by
    have := range_eq_singleton (y ≫ q) (IsLocalRing.closedPoint K)
    refine this.trans ?_
    rw [← hy0]
    rfl
  rw [← val_ne_zero_iff hyq]
  rw [← val_ne_zero_iff hy] at hu
  have ha2 : a ∈ M.O (q (y (IsLocalRing.closedPoint K))) := by rw [hy0]; exact ha
  have e := hq.val_comp y (IsLocalRing.closedPoint K) ha2
  simp only [AlgHom.id_apply] at e
  show M.val (y ≫ q) a ≠ 0
  rw [e]
  exact hu

theorem HH_eq_of_hom : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M Y : RatModel o Ω)
    (q : Y.Z ⟶ M.Z), Y.pt ≫ q = M.pt → M.HasDiv S.th → ∀ w : Y.Z, S.HH Y w = S.HH M (q w) := by
  intro o Ω _ _ _ S M Y q hq hdiv w
  have hh := isHom_of_pt hq
  unfold ThetaSys.HH
  congr 1
  ext x
  simp only [ThetaSys.supI, Set.mem_setOf_eq]
  constructor
  · intro hx
    obtain ⟨x₀, h₀⟩ := hdiv (q w)
    have h₀' : Y.Div S.th x₀ w := by simpa using hh.div h₀
    rw [h₀.div_iff_isUnit]
    exact isUnit_of_isUnit_comap hh w _ _ ((h₀'.div_iff_isUnit x).1 hx)
  · intro hx
    simpa using hh.div hx

end GlobalTheory.Poinc.HHFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupOfPointEqAlongModelHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroupOfPoint_eq_along_modelHom : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M Y : RatModel o Ω) (q : Y.Z ⟶ M.Z), Y.pt ≫ q = M.pt → M.HasDiv S.th → ∀ w : Y.Z, S.HH Y w = S.HH M (q w) := by
  first | exact @GlobalTheory.Poinc.HHFibre.HH_eq_of_hom | exact GlobalTheory.Poinc.HHFibre.HH_eq_of_hom | (intros; apply GlobalTheory.Poinc.HHFibre.HH_eq_of_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackSemiAbelianDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackSemiAbelianDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.FibLat

theorem exists_common_pullback_dvr : ∀ (Y : Scheme.{0}) (G : Over Y) [GrpObj G], IsSemiAbelian G → ∀ (V : Type) [CommRing V] [IsDomain V] (Gu : Over (Sp V)) [GrpObj Gu], IsSemiAbelian Gu → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (fV : V →+* V') (ξ : Sp V' ⟶ Y) (AK : Over (Sp (FractionRing V'))) [GrpObj AK] (α : AK.left ⟶ Gu.left) (Ψ : AK.left ⟶ G.left), IsGrpPullback AK Gu (spMap ((algebraMap V' (FractionRing V')).comp fV)) α → IsGrpPullback AK G (spMap (algebraMap V' (FractionRing V')) ≫ ξ) Ψ → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (β : G'.left ⟶ Gu.left) (β' : G'.left ⟶ G.left) (ω : AK.left ⟶ G'.left), IsGrpPullback G' Gu (spMap fV) β ∧ IsGrpPullback G' G ξ β' ∧ ω ≫ G'.hom = AK.hom ≫ spMap (algebraMap V' (FractionRing V')) ∧ ω ≫ β = α ∧ ω ≫ β' = Ψ ∧ ∀ (F : Gu ⟶ Gu) (f : G ⟶ G) (eK : AK ⟶ AK), eK.left ≫ α = α ≫ F.left → eK.left ≫ Ψ = Ψ ≫ f.left → ∃ F' : G' ⟶ G', F'.left ≫ β = β ≫ F.left ∧ F'.left ≫ β' = β' ≫ f.left := by
  intro Y G _ hG V _ _ Gu _ hGu V' _ _ _ fV ξ AK _ α Ψ hα hΨ
  let j : Sp (FractionRing V') ⟶ Sp V' := spMap (algebraMap V' (FractionRing V'))
  have hα' : IsGrpPullback AK Gu (j ≫ spMap fV) α := by
    have := hα; rwa [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp] at this
  have hG'p := isGrpPullback_pullback Gu (spMap fV)
  have hG''p := isGrpPullback_pullback G ξ
  let ω : AK.left ⟶ ((Over.pullback (spMap fV)).obj Gu).left :=
    pullback.lift α (AK.hom ≫ j) (by rw [hα'.1.w, Category.assoc])
  have hωf : ω ≫ pullback.fst Gu.hom (spMap fV) = α := pullback.lift_fst _ _ _
  have hωs : ω ≫ ((Over.pullback (spMap fV)).obj Gu).hom = AK.hom ≫ j := pullback.lift_snd _ _ _
  have hω : IsGrpPullback AK ((Over.pullback (spMap fV)).obj Gu) j ω :=
    IsGrpPullback.cancel hG'p (IsGrpPullback.congr hα' rfl hωf.symm) hωs
  let ω'' : AK.left ⟶ ((Over.pullback ξ).obj G).left :=
    pullback.lift Ψ (AK.hom ≫ j) (by rw [hΨ.1.w, Category.assoc])
  have hω''f : ω'' ≫ pullback.fst G.hom ξ = Ψ := pullback.lift_fst _ _ _
  have hω''s : ω'' ≫ ((Over.pullback ξ).obj G).hom = AK.hom ≫ j := pullback.lift_snd _ _ _
  have hω'' : IsGrpPullback AK ((Over.pullback ξ).obj G) j ω'' :=
    IsGrpPullback.cancel hG''p (IsGrpPullback.congr hΨ rfl hω''f.symm) hω''s
  have hG' : IsSemiAbelian ((Over.pullback (spMap fV)).obj Gu) := IsSemiAbelian.pullback _ _ hGu
  have hG'' : IsSemiAbelian ((Over.pullback ξ).obj G) := IsSemiAbelian.pullback _ _ hG
  obtain ⟨E, ⟨hE, hEω⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec V')
    (GlobalTheory.IsGenericPointHom.fractionField V' (FractionRing V')) hG' hG'' hω hω''
  haveI := hE
  let β' := E.hom.left ≫ pullback.fst G.hom ξ
  have hβ' : IsGrpPullback ((Over.pullback (spMap fV)).obj Gu) G ξ β' :=
    IsGrpPullback.congr ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso E).comp hG''p) (Category.id_comp _) rfl
  have hωβ' : ω ≫ β' = Ψ := by
    show ω ≫ E.hom.left ≫ pullback.fst G.hom ξ = Ψ
    rw [← Category.assoc, hEω, hω''f]
  refine ⟨(Over.pullback (spMap fV)).obj Gu, inferInstance, pullback.fst _ _, β', ω, hG'p, hβ', hωs, hωf, hωβ', ?_⟩
  intro F f eK hF hf
  let F' := (Over.pullback (spMap fV)).map F
  have hF'f : F'.left ≫ pullback.fst Gu.hom (spMap fV) = pullback.fst Gu.hom (spMap fV) ≫ F.left :=
    pullback.lift_fst _ _ _
  refine ⟨F', hF'f, ?_⟩
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ hG'
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ hG
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V' (FractionRing V')
  haveI : IsSchemeTheoreticallyDominant ω := .of_isPullback hω.1.flip
  have key : ω ≫ F'.left = eK.left ≫ ω := by
    apply pullback.hom_ext
    · rw [Category.assoc, hF'f, ← Category.assoc, hωf, Category.assoc, hωf, hF]
    · have e1 : F'.left ≫ ((Over.pullback (spMap fV)).obj Gu).hom = ((Over.pullback (spMap fV)).obj Gu).hom := Over.w F'
      have e2 : eK.left ≫ AK.hom = AK.hom := Over.w eK
      show (ω ≫ F'.left) ≫ ((Over.pullback (spMap fV)).obj Gu).hom = (eK.left ≫ ω) ≫ ((Over.pullback (spMap fV)).obj Gu).hom
      rw [Category.assoc, e1, hωs, Category.assoc, hωs, ← Category.assoc, e2]
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ ω ?_
  · have e1 : F'.left ≫ ((Over.pullback (spMap fV)).obj Gu).hom = ((Over.pullback (spMap fV)).obj Gu).hom := Over.w F'
    have e2 : f.left ≫ G.hom = G.hom := Over.w f
    rw [Category.assoc, hβ'.1.w, ← Category.assoc, e1, Category.assoc, e2, hβ'.1.w]
  · rw [← Category.assoc, key, Category.assoc, hωβ', ← Category.assoc, hωβ', hf]

end GlobalTheory.Poinc.FibLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackSemiAbelianDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_pullback_semiAbelian_dvr : ∀ (Y : Scheme.{0}) (G : Over Y) [GrpObj G], IsSemiAbelian G → ∀ (V : Type) [CommRing V] [IsDomain V] (Gu : Over (Sp V)) [GrpObj Gu], IsSemiAbelian Gu → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (fV : V →+* V') (ξ : Sp V' ⟶ Y) (AK : Over (Sp (FractionRing V'))) [GrpObj AK] (α : AK.left ⟶ Gu.left) (Ψ : AK.left ⟶ G.left), IsGrpPullback AK Gu (spMap ((algebraMap V' (FractionRing V')).comp fV)) α → IsGrpPullback AK G (spMap (algebraMap V' (FractionRing V')) ≫ ξ) Ψ → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (β : G'.left ⟶ Gu.left) (β' : G'.left ⟶ G.left) (ω : AK.left ⟶ G'.left), IsGrpPullback G' Gu (spMap fV) β ∧ IsGrpPullback G' G ξ β' ∧ ω ≫ G'.hom = AK.hom ≫ spMap (algebraMap V' (FractionRing V')) ∧ ω ≫ β = α ∧ ω ≫ β' = Ψ ∧ ∀ (F : Gu ⟶ Gu) (f : G ⟶ G) (eK : AK ⟶ AK), eK.left ≫ α = α ≫ F.left → eK.left ≫ Ψ = Ψ ≫ f.left → ∃ F' : G' ⟶ G', F'.left ≫ β = β ≫ F.left ∧ F'.left ≫ β' = β' ≫ f.left := by
  first | exact @GlobalTheory.Poinc.FibLat.exists_common_pullback_dvr | exact GlobalTheory.Poinc.FibLat.exists_common_pullback_dvr | (intros; apply GlobalTheory.Poinc.FibLat.exists_common_pullback_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftSemiabelianExtensionModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftSemiabelianExtensionModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.TraitLift

theorem exists_point_finite_ext {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f]
    (K : Type) [Field K] (y : Sp K ⟶ Y) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (x : Sp L ⟶ X),
      x ≫ f = spMap (algebraMap K L) ≫ y := by
  let P := pullback f y
  haveI : Nonempty (Sp K) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨p, -⟩ := (pullback.snd f y).surjective (Classical.arbitrary (Sp K))
  obtain ⟨R, e, he, ⟨q, -⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := P) (x := p) (U := ⊤) trivial
  let g' : Spec R ⟶ Sp K := e ≫ pullback.snd f y
  haveI : LocallyOfFiniteType g' := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g'
  have hφf : φ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hφ]
    infer_instance
  haveI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨q⟩
  obtain ⟨I, hI⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  letI : Algebra K (R ⧸ I) := ((Ideal.Quotient.mk I).comp φ.hom).toAlgebra
  haveI hft : Algebra.FiniteType K (R ⧸ I) :=
    RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective) hφf
  refine ⟨R ⧸ I, inferInstance, inferInstance, finite_of_finite_type_of_isJacobsonRing _ _,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ e ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e]
  change _ ≫ g' ≫ y = _
  rw [← hφ, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem exists_lift_of_proper {X Y : Scheme.{0}} (f : X ⟶ Y) [IsProper f] [Surjective f]
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (hV : IsCN V) (y : Sp V ⟶ Y) :
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (ξ : Sp V' ⟶ X),
      IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ ξ ≫ f = spMap j ≫ y := by
  haveI := hV.2.2.1
  haveI := hV.2.2.2
  obtain ⟨L, _, _, _, x, hx⟩ :=
    exists_point_finite_ext f (FractionRing V) (spMap (algebraMap V (FractionRing V)) ≫ y)
  obtain ⟨V', _, _, _, hc, _, _, _, hcomp, -, hinj, hloc, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  have hv : ValuativeCriterion f := by
    have h : IsProper f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hsq : x ≫ f = spMap (algebraMap V' L) ≫ spMap (algebraMap V V') ≫ y := by
    rw [hx, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hcomp]
  let S : ValuativeCommSq f := { R := V', K := L, i₁ := x, i₂ := spMap (algebraMap V V') ≫ y, commSq := ⟨hsq⟩ }
  obtain ⟨l, -, hl⟩ := (hv S).some.default
  exact ⟨V', inferInstance, inferInstance, inferInstance, algebraMap V V', l,
    ⟨inferInstance, inferInstance, hc, charZero_of_injective_ringHom hinj⟩, hinj, hloc, hl⟩

theorem surjective_of_isHom_id {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M Y : RatModel o Ω} {f : Y.Z ⟶ M.Z}
    (hf : M.IsHom Y (AlgHom.id o Ω) f) [IsProper f] : Surjective f := by
  have h : Y.pt ≫ f = M.pt := by
    rw [hf]
    exact (congrArg (· ≫ M.pt) (Spec.map_id _)).trans (Category.id_comp _)
  haveI : IsDominant (Y.pt ≫ f) := h ▸ inferInstance
  haveI : IsDominant f := IsDominant.of_comp Y.pt f
  infer_instance

theorem exists_lift : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsLocalHom ev → IsCN V → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (ξ : Sp V' ⟶ Y.Z), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ ξ ≫ πY = spMap (j.comp ev) ≫ X₁.M.Z.fromSpecStalk z₁ := by
  intro g n F W Z i X₁ z₁ Y πY h V _ _ _ _ ev _ hV
  obtain ⟨U₀, EE, -, -, -, hf, hp⟩ := h
  haveI := surjective_of_isHom_id hf
  obtain ⟨V', _, _, _, j, ξ, h1, h2, h3, h4⟩ := exists_lift_of_proper πY V hV (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)
  refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, j, ξ, h1, h2, h3, ?_⟩
  rw [h4, ← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.Poinc.Sep.TraitLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftSemiabelianExtensionModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_lift_semiabelianExtensionModel : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsLocalHom ev → IsCN V → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (ξ : Sp V' ⟶ Y.Z), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ ξ ≫ πY = spMap (j.comp ev) ≫ X₁.M.Z.fromSpecStalk z₁ := by
  first | exact @GlobalTheory.Poinc.Sep.TraitLift.exists_lift | exact GlobalTheory.Poinc.Sep.TraitLift.exists_lift | (intros; apply GlobalTheory.Poinc.Sep.TraitLift.exists_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOActNDescend
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.GaloisActDesc

theorem exists_oActN_descend : ∀ (O : Type) [Ring O] (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (act : OActN O A), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → GlobalTheory.ZM.IsGaloisCover Ga ν φ → (∀ a, IsGrpPullback A A (ρ a) (ν a)) → (∀ a c, (act.act c).left ≫ ν a = ν a ≫ (act.act c).left) → ∃ act₀ : OActN O A₀, ∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left := by
  intro O _ X Y π Ga _ ρ A _ _ A₀ _ _ φ ν act hπ _ _ hp hφ _ hcomm
  have : Flat π := by have := hπ.etale; infer_instance
  have : Surjective π := hπ.onto
  have eφ : Epi φ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hφ
  have hi : ∀ c, ∃ f : A₀ ⟶ A₀, (act.act c).left ≫ φ = φ ≫ f.left := by
    intro c
    obtain ⟨g, hg, -⟩ := hφ.existsUnique_desc ((act.act c).left ≫ φ) (fun a ↦ by
      rw [← Category.assoc, ← hcomm, Category.assoc, hφ.inv])
    have hw : g ≫ A₀.hom = A₀.hom := by
      rw [← cancel_epi φ, reassoc_of% hg, hp.1.w, Over.w_assoc]
    exact ⟨Over.homMk g hw, hg.symm⟩
  choose f hf using hi
  refine ⟨⟨f, fun x ↦ ?_, ?_, fun x y ↦ ?_, fun x y ↦ ?_⟩, hf⟩
  · have := act.hom x
    exact GlobalTheory.ActDescent.isMonHom_descend hp hp (act.act x) (f x) (hf x)
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    rw [← hf, act.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    rw [← hf, act.mul, Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    let φ₀ : Over.mk (A.hom ≫ π) ⟶ A₀ := Over.homMk φ hp.1.w
    have h := hp.2 A (act.act x) (act.act y) (φ₀ ≫ f x) (φ₀ ≫ f y) (hf x).symm (hf y).symm
    rw [← MonObj.comp_mul] at h
    rw [← hf, act.add, ← h]
    rfl

end GlobalTheory.GaloisActDesc
end
end
