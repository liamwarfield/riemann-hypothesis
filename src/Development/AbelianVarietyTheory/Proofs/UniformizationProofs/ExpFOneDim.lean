module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOneDim
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOneDim
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.OneDim

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  by_cases h : f y ∈ U
  · rw [gs_eq f y U h, map_zero, map_zero]
  · exact dif_neg h

def zeroSec {Y : Scheme.{0}} (M : LB Y) : LB.Sec M :=
  ⟨fun _ => 0, fun i j => by rw [map_zero, map_zero, mul_zero]⟩

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem expF_zero (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) :
    U.ExpF F k (zeroSec _) (fun _ => zeroSec _) := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, ?_, ?_⟩
  · intro Z rA y rG _ _ z JA JG _ _
    rw [Fin.sum_univ_zero]
    exact (congrArg (_ * ·) (gs_zero _ _ _)).trans (mul_zero _)
  · intro α Z rF rB _ z J _
    rw [Fin.sum_univ_zero]
    exact gs_zero _ _ _

theorem appTop_injective (F : Type) [Field F] [Algebra (FractionRing R) F] :
    Function.Injective (toUnit (TF (R := R) F)).left.appTop.hom := by
  have e₂ : (toUnit (TF (R := R) F)).left =
      Spec.map (CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
    have a := Over.w (toUnit (TF (R := R) F))
    exact ((Category.comp_id _).symm.trans a).trans (Spec.map_comp _ _).symm
  rw [e₂]
  have n := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))
  have i : Function.Injective ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
      CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))).hom :=
    ((algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R (FractionRing R))).comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
  rw [← n] at i
  exact Function.Injective.of_comp (f := (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom) i

theorem eq_zero_of_pullG (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
    (σ : U.SecGT (𝟙_ _) k) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)))
    (h : U.PullG F (toUnit _) k σ t) (ht : ∀ j, t.f j = 0) (j) : σ.f j = 0 := by
  have hs : Smooth G.hom := U.semi.smooth
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (TF (R := R) F).left := inferInstanceAs (IsAffine (Spec _))
  refine GlobalTheory.sec_eq_zero_of_sval_whiskerRight_eq_zero _ G (𝟙_ _) (TF (R := R) F) (toUnit _) (appTop_injective F)
    _ U.P.L.L U.P.L.isLB _ _ _ σ (fun z J hJ => ?_) j
  have w : (snd (TF (R := R) F) G).left ≫ G.hom =
      ((fst (TF (R := R) F) G).left ≫ jFK (R := R) F) ≫ jK R :=
    (Over.w (snd (TF (R := R) F) G)).trans ((Over.w (fst (TF (R := R) F) G)).symm.trans (Category.assoc _ _ _).symm)
  let y : (TF (R := R) F ⊗ G).left ⟶ ((Over.pullback (jK R)).obj G).left := pullback.lift _ _ w
  have e₄ : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
  have w' : (fst (TF (R := R) F) G).left ≫ jFK (R := R) F = (y ≫ U.gen.hom.left) ≫ A.A.hom := by
    rw [Category.assoc, e₄]
    exact (pullback.lift_snd _ _ _).symm
  let rA : (TF (R := R) F ⊗ G).left ⟶ (TFK (R := R) F ⊗ A.A).left := pullback.lift _ _ w'
  obtain ⟨JA, hJA⟩ := exists_good_pt A.isLB z
  refine (h _ rA y (toUnit (TF (R := R) F) ▷ G).left (pullback.lift_snd _ _ _) ?_ ?_ z JA J hJA hJ).symm.trans ?_
  · exact (congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := R) F)) G)).trans
      (pullback.lift_fst _ _ w).symm
  · refine (congrArg CommaMorphism.left (whiskerRight_fst (toUnit (TF (R := R) F)) G)).trans ?_
    rw [← Category.assoc]
    exact congrArg (· ≫ (toUnit (TF (R := R) F)).left) (pullback.lift_fst _ _ w').symm
  · exact (congrArg (_ * ·) ((congrArg (gs rA z _) (ht _)).trans (gs_zero _ _ _))).trans (mul_zero _)

end

theorem exists_smul_of_finrank_one {F B M : Type} [Field F] [CommRing B] [AddCommGroup M] [Module B M]
    (e : F ≃+* B) (h : Module.finrank B M = 1) {v : M} (hv : v ≠ 0) (w : M) : ∃ c : F, e c • v = w := by
  letI : Field B := (e.symm.toMulEquiv.isField (Field.toIsField F)).toField
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := B) v hv).1 h w
  exact ⟨e.symm c, by rw [e.apply_symm_apply]; exact hc⟩

theorem expF_one_dim : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s₀ : Raw D (Kbar V) 1), U.PullG (Kbar V) (toUnit _) 1 θ th → PullB D (Kbar V) (toUnit _) 1 f s₀ → (∃ j, th.f j ≠ 0) ∧ U.ExpF (Kbar V) 1 th s₀ ∧ ∀ t s, U.ExpF (Kbar V) 1 t s → ∃ c : (Kbar V), ∀ α j, (s α).f j = DegPre.constBF D (Kbar V) c _ * (s₀ α).f j) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ th s₀ hG hB
  have hne : ∃ j, th.f j ≠ 0 := by
    by_contra hn
    obtain ⟨j, hj⟩ := hθ.2
    exact hj (eq_zero_of_pullG U (Kbar V) 1 θ th hG (fun j => by_contra fun h => hn ⟨j, h⟩) j)
  have hE := GlobalTheory.expF_of_pull V D _ A G U (Kbar V) 1 θ f th s₀ hθ.1 hG hB
  refine ⟨hne, hE, fun t s hts => ?_⟩
  obtain ⟨-, -, hr, -⟩ := GlobalTheory.ThetaRep.exists_projective_rep hL hL2 _ A (Kbar V) (jFK (R := V) (Kbar V)) 1
    (by rw [Nat.cast_one]; exact one_ne_zero)
  rw [one_pow] at hr
  have hv : SecM.ofSec A.A th ≠ 0 := fun h => by
    obtain ⟨j, hj⟩ := hne
    exact hj (congrFun (congrArg Subtype.val h) j)
  obtain ⟨c, hc⟩ := exists_smul_of_finrank_one
    (Scheme.ΓSpecIso (CommRingCat.of (Kbar V))).symm.commRingCatIsoToRingEquiv hr hv (SecM.ofSec A.A t)
  let s' : Raw D (Kbar V) 1 := fun α =>
    ⟨fun j => DegPre.constBF D (Kbar V) c _ * (s₀ α).f j, fun i j => by
      rw [map_mul, map_mul, (s₀ α).compat i j, mul_left_comm]
      congr 2
      exact fn_ext fun x hx => (gs_res _ x _ hx _).trans ((gs_res _ x _ hx.1 _).trans
        ((gs_res _ x _ hx _).trans (gs_res _ x _ hx.2 _)).symm)⟩
  have hs' : U.ExpF (Kbar V) 1 t s' :=
    GlobalTheory.UU.ExpLin.expF_linear V hV D A G U (Kbar V) 1 th (zeroSec _) t s₀ (fun _ => zeroSec _) s' c hE
      (expF_zero U _ 1) (fun j => ((congrFun (congrArg Subtype.val hc) j).symm).trans (add_zero _).symm)
      (fun α j => (add_zero _).symm)
  have e : s = s' := (GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D A G U (Kbar V) 1 t t s s' hts hs').1 rfl
  exact ⟨c, fun α j => by rw [e]⟩

end GlobalTheory.UU.OneDim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOneDimStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expF_of_theta_degree_one : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s₀ : Raw D (Kbar V) 1), U.PullG (Kbar V) (toUnit _) 1 θ th → PullB D (Kbar V) (toUnit _) 1 f s₀ → (∃ j, th.f j ≠ 0) ∧ U.ExpF (Kbar V) 1 th s₀ ∧ ∀ t s, U.ExpF (Kbar V) 1 t s → ∃ c : (Kbar V), ∀ α j, (s α).f j = DegPre.constBF D (Kbar V) c _ * (s₀ α).f j) := by
  first | exact @GlobalTheory.UU.OneDim.expF_one_dim | exact GlobalTheory.UU.OneDim.expF_one_dim | (intros; apply GlobalTheory.UU.OneDim.expF_one_dim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralThetaSectionWithExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralThetaSectionWithExpansion
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ThetaIntegral

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J) : sval s r z J = 0 := by
  refine (congrArg (gs r z _) (h _)).trans ?_
  unfold gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

theorem exists_sec_ne_zero (h1 : Laws) (h2 : Laws2) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type)
    [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) :
    ∃ v : SecM P.A P.L ((1 : ℕ) : ℤ) (Over.mk p), v ≠ 0 := by
  obtain ⟨-, -, hr, -⟩ := GlobalTheory.ThetaRep.exists_projective_rep h1 h2 S P F p 1 (by simp)
  have : Nontrivial Γ((Over.mk p).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have : Nontrivial (SecM P.A P.L ((1 : ℕ) : ℤ) (Over.mk p)) :=
    Module.nontrivial_of_finrank_pos (R := Γ((Over.mk p).left, ⊤)) (by rw [hr]; simp)
  exact exists_ne 0

theorem exists_theta : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∃ θ f, U.Theta θ f) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U
  obtain ⟨v, hv⟩ := exists_sec_ne_zero h1 h2 _ A (Kbar V) (jFK (R := V) (Kbar V))
  obtain ⟨s, n, c, σ, f, hE, hA, -⟩ := GlobalTheory.T.exists_fourierJacobi_expansion_over_field h1 h2 V hV D A G U (Kbar V) 1 le_rfl (SecM.toSec A.A v)
  by_contra hn
  have hz : ∀ i j, (σ i).f j = 0 := fun i j => by
    by_contra h
    exact hn ⟨σ i, f i, hE i, j, h⟩
  refine hv (Subtype.ext (funext fun j => ?_))
  refine sec_ext_val (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := V) (Kbar V)) A.A).left)
    (ε := fun _ => ((1 : ℕ) : ℤ)) A.isLB (s := SecM.toSec A.A v) (s' := SecM.toSec A.A 0) (fun z JA hJA => ?_) j
  obtain ⟨JG, hJG⟩ := exists_good_pt U.P.L.isLB z
  let y := (snd (TFK (R := V) (Kbar V)) A.A).left ≫ U.gen.inv.left
  let T : Over (Spec (CommRingCat.of V)) := Over.mk ((y ≫ pullback.fst G.hom (jK V)) ≫ G.hom)
  let x : T ⟶ G := Over.homMk (y ≫ pullback.fst G.hom (jK V)) rfl
  have e := hA _ (𝟙 _) y (lift (toUnit T) x).left
    (by rw [Category.id_comp, Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id])
    (congrArg (fun q => q.left) (lift_snd (toUnit T) x)) z JA JG hJA hJG
  rw [Finset.sum_eq_zero fun i _ => by rw [sval_eq_zero (σ i) (hz i), mul_zero], ← Units.val_pow_eq_pow_val,
    Units.mul_right_eq_zero] at e
  exact e.trans (sval_eq_zero _ (fun _ => rfl) _ _ _).symm

end GlobalTheory.ThetaIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralThetaSectionWithExpansionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_theta_section_with_expansion : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∃ θ f, U.Theta θ f) := by
  first | exact @GlobalTheory.ThetaIntegral.exists_theta | exact GlobalTheory.ThetaIntegral.exists_theta | (intros; apply GlobalTheory.ThetaIntegral.exists_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsActValue
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.EvalLevel
open GlobalTheory.UT.CoefBasic

section
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem powFrame_isGen (z : T ⟶ A)
    (e : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => 1)))
    (he : e.IsGen) (k : ℤ) : (powFrame A L z e k).IsGen := by
  intro i j
  have h := congrArg (· ^ k) (he i j)
  simp only [mul_zpow, ← map_zpow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl

theorem rigT_isGen {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ) : (rigT A L ρ T k).IsGen := by
  intro i j
  refine unit_ext fun y hy => ?_
  have v : ∀ i : Fin 1 → L.ι, y ∈ LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i →
      gm (𝟙 T.left) y (LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i) ((rigT A L ρ T k).s i) =
        gm T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => i 0)) (ρ.s fun _ => i 0) ^ k := fun i hi =>
    (map_zpow _ _ _).trans (congrArg (· ^ k) (gm_rp₁ T.hom y _ _ (rigT_le A L i) hi _))
  have e := gen_trans (L := L) (φ := fun _ : PUnit.{1} => eSec A) (ε := fun _ => 1) hρ T.hom y
    (j := fun _ => i 0) (j' := fun _ => j 0) (rigT_le A L (T := T) i hy.1) (rigT_le A L (T := T) j hy.2)
  rw [trF, Fintype.prod_unique, zpow_one] at e
  refine ((gm_res (𝟙 _) y _ hy _).trans (v i hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L (fun _ : Fin 1 => T.hom ≫ eSec A) (fun _ => k) (𝟙 _) y i j hy.1 hy.2)
    ((gm_res (𝟙 _) y _ hy _).trans (v j hy.2)))).symm)
  rw [Fin.prod_univ_one, Category.id_comp, ← mul_zpow]
  exact congrArg (· ^ k) e

theorem ptSec_translPt (x : T ⟶ A) : ptSecT A (1 : T ⟶ A) ≫ translPt A x = x := by
  rw [ptSecT, translPt, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp, ← Hom.mul_def, _root_.mul_one]

theorem ptSec_translT (x : T ⟶ A) : (ptSecT A (1 : T ⟶ A)).left ≫ (translT A x).left = (ptSecT A x).left := by
  rw [← Over.comp_left, translT, comp_lift, ptSec_translPt, ptSecT, lift_fst]; rfl

end

theorem sumV_mul {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s c : F}
    (h : SumV v x s) (hc : c ≠ 0) : SumV v (fun i => c * x i) (c * s) := by
  intro q
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc)
  obtain ⟨S, hS⟩ := h (q - r)
  refine ⟨S, fun T hT => ?_⟩
  rw [← Finset.mul_sum, ← mul_sub, v.map_mul, ← hr, show q = r + (q - r) by ring, WithTop.coe_add]
  exact add_le_add le_rfl (hS T hT)

theorem sumV_equiv {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix Ix' : Type} (e : Ix' ≃ Ix) {x : Ix → F} {s : F}
    (h : SumV v x s) : SumV v (fun i => x (e i)) s := by
  intro q
  obtain ⟨S, hS⟩ := h q
  refine ⟨S.map e.symm.toEmbedding, fun T hT => ?_⟩
  have := hS (T.map e.toEmbedding) fun i hi => by
    simpa using hT (Finset.mem_map_of_mem e.symm.toEmbedding hi)
  rwa [Finset.sum_map] at this

theorem exists_act_value {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {ρ : LB.Gen (A.L.pull (eSec A.A))} (hρ : ρ.IsGen) (N : ℕ)
    (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F))
    (e : LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => θ.pt.left) (fun _ => 1)))
    (he : e.IsGen) : ∃ u : F, u ≠ 0 ∧ ∀ (t t' : SecA A F N) (c : F), IsActOf A.A A.L (N : ℤ) θ t t' →
      (∀ z J, Good A.L z J → sA t (ptSecT A.A θ.pt).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z)
        (cst (R := R) F z c) * (val (powFrame A.A A.L θ.pt e N) (𝟙 _) z J).val) →
      ∀ z J, Good A.L z J → sA t' (ptSecT A.A 1).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z)
        (cst (R := R) F z (u * c)) * (val (rigT A.A A.L ρ (TFK (R := R) F) (N : ℤ)) (𝟙 _) z J).val := by
  have e₀ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left =
      (TFK (R := R) F).hom ≫ eSec A.A := by
    rw [← Over.comp_left, ptSecT, lift_snd]; rfl
  have e₁ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (translPt A.A θ.pt).left = θ.pt.left := by
    rw [← Over.comp_left, ptSec_translPt]
  obtain ⟨u, hu, hv⟩ := TWM.exists_ratio (F := F) A.isLB
    (LB.mulGen A.L _ _ _ _ (LB.pullGen A.L _ _ θ.φ (ptSecT A.A 1).left) (powFrame A.A A.L θ.pt e N))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _) (powFrame_isGen θ.pt e he N))
    (rigT A.A A.L ρ (TFK (R := R) F) (N : ℤ)) (rigT_isGen hρ N) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
      exact (congrArg₂ (fun a b => h a ^ (N : ℤ) * (h b ^ (N : ℤ))⁻¹ * h θ.pt.left ^ (N : ℤ)) e₀ e₁).trans
        (inv_mul_cancel_right _ _))
  refine ⟨u, hu, fun t t' c ha ht z J hJ => ?_⟩
  have a₁ := GlobalTheory.BoxTheta.act_val θ t t' ha (ptSecT A.A 1).left z hJ
  rw [ptSec_translT] at a₁
  have a₀ := (val_pull (L := A.L) (K := Fin 2) (φ := ![(snd (TFK (R := R) F) A.A).left, (translPt A.A θ.pt).left])
    (ε := ![(N : ℤ), -(N : ℤ)]) hJ θ.φ (ptSecT A.A 1).left (𝟙 _)).trans
    (congrArg (fun r => val (L := A.L) (K := Fin 2) (φ := ![(snd (TFK (R := R) F) A.A).left, (translPt A.A θ.pt).left])
      (ε := ![(N : ℤ), -(N : ℤ)]) θ.φ r z J) (Category.id_comp _))
  have a₂ := ((Units.val_mul _ _).symm.trans (congrArg Units.val ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) a₀ rfl)).symm)).trans (hv _ (𝟙 _) z J hJ)
  have a₃ := ht z J hJ
  have a₄ : cst (R := R) F z (u * c) = cst (R := R) F z u * cst (R := R) F z c := by
    rw [cst_eq, cst_eq, cst_eq, map_mul]
  refine a₁.trans ((congrArg _ a₃).trans ?_)
  rw [a₄]
  refine (mul_left_comm _ _ _).trans ((congrArg _ a₂).trans ?_)
  exact (_root_.mul_assoc _ _ _).symm.trans (congrArg₂ (fun a b : (TFK (R := R) F).left.presheaf.stalk z => a * b) (_root_.mul_comm _ _) rfl)

theorem value_at_level : LL → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (N : ℕ), 1 ≤ N → ∀ (q : QkPt D.toPre F N) (x : TFK (R := V) F ⟶ A.A), QkToAkU U.toUnifPre F N q x → ∀ e : LB.Gen (LB.LinComb A.L (Y := (TFK (R := V) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)), e.IsGen → ∀ w : Frm D.toPre F N q.g.b, w.IsGen → ∃ κ : F, κ ≠ 0 ∧ ∀ (t : SecA A F N) s (c : F), U.ExpandsF F N w₀ t s → (∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) * (val (powFrame A.A A.L x e N) (𝟙 _) z J).val) → SumV v (coef s q.g w) (κ * c) := by
  intro hL V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN N hN1 q x hx e he w hw
  have hB : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  haveI : Subsingleton (TFK (R := V) F).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  haveI : Nonempty (TFK (R := V) F).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of F)))
  obtain ⟨hxN, hθ⟩ := hx w₀ hN.1
  obtain ⟨θ, rfl⟩ := GlobalTheory.BoxTheta.exists_theta hL.1.kerPow A hN1 (T := TFK (R := V) F) x hxN
  obtain ⟨w', hw', hΦ⟩ := hθ θ rfl
  obtain ⟨u, hu, hval⟩ := exists_act_value hN.2.1 N θ e he
  obtain ⟨o, ho⟩ := exists_zero_gt (D := D.toPre) (F := F)
  obtain ⟨w₁, hw₁⟩ := (coef_basic V D.toPre F N o).2.1 ho.1
  have hadd : o.IsAdd q.g q.g := by
    rw [GlobalTheory.TorusExt.isZero_unique ho GlobalTheory.TorusExt.isZero_gtZero]
    have := GlobalTheory.TorusExt.isAdd_gtAdd (GlobalTheory.TorusExt.gtZero D.toPre F) q.g
    rwa [GlobalTheory.TorusExt.gtZero_add] at this
  obtain ⟨ω, hω, -, hc⟩ := GlobalTheory.UT.CoefPhi.coef_phi hL V _ hB D F N hN1 q w' hw' o q.g hadd w₁ hw₁.1
  obtain ⟨d, hd, -, hdc⟩ := ((coef_basic V D.toPre F N q.g).2.2 ω hω).2.2.1 w hw
  refine ⟨d * u, mul_ne_zero hd hu, fun t s c hts hc' => ?_⟩
  obtain ⟨t', ht'⟩ := GlobalTheory.VVRank.exists_isTwistPull A.A (ψ := translT A.A θ.pt) (m := translPt A.A θ.pt)
    (hm := lift_snd _ _) (a := N) (b := N) (α := θ.φ) A.isLB θ.isGen t
  obtain ⟨s', hs', -⟩ := ((GlobalTheory.UT.expBijF_and_expandsF_lin hL V _ hB D A G hG U).1 F N hN1 w₀ hN.1).1 t'
  have h₁ := (GlobalTheory.UT.EvalZero.value_at_origin hL V _ hB D A G hG U F).2.2 w₀ ρ hN N t' s' hs' o w₁ ho hw₁ (u * c)
    (hval t t' c ht' hc')
  have h₂ := sumV_equiv (Equiv.addRight q.y) (GlobalTheory.UT.AdicValSum.main V ϖ hϖ F v hv _ _ _ h₁).1
  have h₃ := hc 1 N le_rfl (Nat.mul_one N).symm q (one_nsmul _).symm rfl w' w₁ ω ⟨hw', fun _ _ _ => (pow_one _).symm⟩
    ⟨hw₁.1, fun _ _ _ => (pow_one _).symm⟩ ⟨hω, fun _ _ _ => (pow_one _).symm⟩ s s' (hΦ t t' s s' hts hs' ht')
  have h₄ := sumV_mul h₂ hd
  simp only [Equiv.coe_addRight, h₃, ← hdc] at h₄
  rw [_root_.mul_assoc]
  exact h₄

end GlobalTheory.UT.EvalLevel
end
end
