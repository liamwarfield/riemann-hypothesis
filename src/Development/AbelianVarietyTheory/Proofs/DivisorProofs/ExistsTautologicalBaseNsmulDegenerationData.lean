module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinomialFlagDimensionDegreeBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff

@[expose] public section

local instance (priority := high) : IsEmpty Empty := ⟨Empty.elim⟩

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalBaseNsmulDegenerationData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalBaseNsmulDegenerationData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TInjBase

theorem val_eq_of_injective {X Y Y₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    (e : Y₀ ⟶ Y) (he : Function.Injective e.appTop.hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u e y J = val u' e y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ : ∃ a, a = (res le (t.s PEmpty.elim)).val := ⟨_, rfl⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ a := by
    intro Z r z J hJ
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      (congrArg (gs r z ⊤) ha.symm))
  have a1 : a = 1 := he ((fn_ext (V := ⊤) fun y _ => by
    choose I hI using fun χ : Y₀ ⟶ X => exists_chart hM (χ y)
    have := key _ e y I hI
    rw [h y I hI, mul_inv_cancel] at this
    refine (gs_pull (𝟙 Y₀) e y ⊤ trivial a).trans ?_
    rw [Category.id_comp, ← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]).trans (map_one _).symm)
  have := key Z r z J hJ
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

theorem exists_gens {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult)
    (hU : ∀ y, PsiUnitOn D y Set.univ) :
    ∃ τ : ∀ a b : D.X, LB.Gen (LB.LinComb D.P.L (lamPts (D.c a) (D.c b)) negε), (∀ a b, (τ a b).IsGen) ∧
      (∀ a b z J, Good D.P.L z J → val (τ a b) (𝟙 _) z J = val (τ b a) (𝟙 _) z J) ∧
      (∀ a a' b z J, Good D.P.L z J → val (τ (a + a') b) (𝟙 _) z J * cubV D.cub z J (D.c a) (D.c a') (D.c b) =
        val (τ a b) (𝟙 _) z J * val (τ a' b) (𝟙 _) z J) ∧
      ∀ a b z J, Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (τ a b) (toUnit (TK R)).left z J := by
  obtain ⟨τ₀, h₀⟩ := GlobalTheory.DDataGens.main R D hB hU
  have cadd : ∀ a b, D.c (a + b) = D.c a * D.c b := D.c_add
  have c0 : D.c 0 = 1 := mul_eq_left.1 ((cadd 0 0).symm.trans (by rw [add_zero]))
  have ex : ∀ a b : D.X, ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (D.c a) (D.c b)) negε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good D.P.L z J → val t r z J = val (τ₀ a b) r z J := fun a b =>
    exists_gen D.P.isLB (fun U _ h => by
      simp [lamPts, negε, Fin.prod_univ_four, cadd, c0]) (τ₀ a b) (h₀ a b).1
  choose τ hτ hv using ex
  have hK : ∀ a b z J, Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (τ a b) (toUnit (TK R)).left z J :=
    fun a b z J hJ => ((h₀ a b).2 z J hJ).trans (hv a b _ _ z J hJ).symm
  have inj : Function.Injective (toUnit (TK R)).left.appTop.hom := by
    rw [GlobalTheory.DDataGens.toUnit_TK_left]
    have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    intro x y hxy
    refine (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
      (IsFractionRing.injective R (FractionRing R) ?_)
    exact (congrArg (fun g => g.hom x) nat).symm.trans
      ((congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom hxy).trans (congrArg (fun g => g.hom y) nat))
  refine ⟨τ, hτ, fun a b z J hJ => ?_, fun a a' b z J hJ => ?_, hK⟩
  · refine val_eq_of_injective D.P.isLB (fun U _ h => ?_) _ inj (hτ a b) (hτ b a) (fun y J hJ => ?_) _ _ z J hJ
    · simp only [Fin.prod_univ_four, lamPts, negε, mul_comm (D.c b) (D.c a)]
      simp [mul_right_comm]
    · exact (hK a b y J hJ).symm.trans ((GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a b).trans (hK b a y J hJ))
  · have key := val_eq_of_injective D.P.isLB (fun U _ h => ?_) _ inj
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hτ (a + a') b)
        (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (D.c a) (lift (D.c a') (D.c b))).left))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hτ a b) (hτ a' b)) (fun y J hJ => ?_) _ (𝟙 _) z J hJ
    · refine Eq.trans ?_ (key.trans (val_mul hJ _ _ _))
      refine Eq.trans ?_ (val_mul hJ _ _ _).symm
      refine congrArg (_ * ·) ?_
      have := val_cub D.cub (𝟙 (𝟙_ (Over (Sp R)))) hJ (D.c a) (D.c a') (D.c b)
      simp only [Category.id_comp] at this
      exact this.symm
    · refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl (prod_cub (D.c a) (D.c a') (D.c b) h))).trans ?_
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, lamPts, negε, cadd]
      apply Additive.ofMul.injective
      simp [ofMul_mul, ofMul_inv]
      abel
    · refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
      rw [← hK _ _ y J hJ, ← hK _ _ y J hJ, ← hK _ _ y J hJ]
      exact (congrArg (_ * ·) (val_cub D.cub (toUnit (TK R)) hJ _ _ _)).trans
        (GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hJ hB a a' b)

theorem val_trans {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : LB B.left} (hL : L.IsLB) {T T' : Over S}
    (ρ : T' ⟶ T) (x y : T ⟶ B) {t : LB.Gen (LB.LinComb L (lamPts x y) negε)} (ht : t.IsGen) (z : T'.left) {J J'}
    (hJ : Good L z J) (hJ' : Good L z J') :
    val t ρ.left z J' = lamVal (Wit.idPull (abelian₂ B L)) (lift (ρ ≫ x) (ρ ≫ y)).left z J J' * val t ρ.left z J := by
  refine (gen_trans ht ρ.left z (hJ'.mem _ _) (hJ.mem _ _)).trans (congrArg (· * _) ?_)
  have hm : ∀ {J}, Good L z J → (lift (ρ ≫ x) (ρ ≫ y)).left z ∈ (abelian₂ B L).U
    (fun I => J ((lift (ρ ≫ x) (ρ ≫ y)).left ≫ (psum B (x2 B) I.down).left)) := fun hJ => hJ.mem _ _
  refine Eq.trans ?_ (Wit.gw_idPull (abelian₂ B L) _ z _ _ (hm hJ) (hm hJ')).symm
  refine Eq.trans ?_ (gm_linComb L _ _ _ z _ _ (hm hJ) (hm hJ')).symm
  refine Eq.trans ?_ (GlobalTheory.PrimCocycle.prod_lam (ρ ≫ x) (ρ ≫ y) (fun q => gm q z _ (L.g (J q) (J' q)))).symm
  have inv : ∀ q, gm q z _ (L.g (J' q) (J q)) = (gm q z _ (L.g (J q) (J' q)))⁻¹ := fun q =>
    eq_inv_of_mul_eq_one_left ((gm_cocycle hL q z (hJ' q) (hJ q) (hJ' q)).trans (gm_self hL q z (hJ' q)))
  refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ negε k) (inv (_ ≫ _))).trans ?_
  refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_)
    (Wit.prod_neg_lamPts _ _ (fun q => gm q z _ (L.g (J q) (J' q))))
  have : ρ.left ≫ lamPts x y k = 𝟙 _ ≫ lamPts (ρ ≫ x) (ρ ≫ y) k := by
    rw [Category.id_comp]
    fin_cases k
    · exact congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_mul ρ _ _)
    · rfl
    · rfl
    · exact congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_one ρ)
  exact congrArg (fun q => (gm q z _ (L.g (J q) (J' q)))⁻¹ ^ negε k) this

theorem main : ∀ {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (b : o →+* W) (D : DegPre W), D.TauBimult → (∀ y, PsiUnitOn D y Set.univ) → ∀ n : ℕ, ∃ (T : TautBase o W) (ib : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), From T (RingHom.id W) (fun _ : Empty => (1 : W)) (fun _ => 0) n (mulDeg D n) ib β ββ w := by
  intro o W _ _ _ _ b D hB hU n
  obtain ⟨τ, hg, hs, ha, hK⟩ := exists_gens D hB hU
  obtain ⟨ib⟩ : Nonempty (D.X ≃+ (Fin (Module.finrank ℤ D.X) → ℤ)) := ⟨(Module.finBasis ℤ D.X).equivFun.toAddEquiv⟩
  have hid : spMap (RingHom.id W) = 𝟙 (Sp W) := Spec.map_id _
  have hn : ∀ a : D.X, ib.symm ((n : ℤ) • ib a) = n • a := fun a => by
    rw [map_zsmul, ib.symm_apply_apply, natCast_zsmul]
  let T : TautBase o W :=
    { b := b
      B := D.P.A
      comm := D.P.isAb.comm
      isAb := D.P.isAb
      g := D.P.g
      smoothDim := D.P.smoothDim
      M := ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩
      cub := D.cub
      ample := D.P.ample
      ktriv := D.P.ktriv
      r := Module.finrank ℤ D.X
      c₀ := fun a => D.c (ib.symm a)
      c₀_add := fun a a' => by rw [map_add (f := _)]; exact D.c_add _ _
      τ₀ := fun a a' => τ (ib.symm a) (ib.symm a')
      τ₀_gen := fun a a' => hg _ _
      τ₀_symm := fun a a' => hs _ _
      τ₀_add := fun a a' a'' z J hJ => (congrArg (fun x => val (τ x (ib.symm a'')) (𝟙 _) z J * _) (map_add ib.symm a a')).trans
        (ha _ _ _ z J hJ) }
  refine ⟨T, ib, 𝟙 _, 𝟙 _, Wit.idPull _, ?_, ⟨(Category.id_comp _).trans (Category.comp_id _).symm,
    (Category.id_comp _).trans (Category.comp_id _).symm⟩, Wit.idPull_isGen (DVR.linComb_isLB _ D.P.isLB _ _), fun a => ?_,
    fun (a b : D.X) => ⟨1, by simp, fun z J J' hJ hJ' => ?_⟩⟩
  · rw [hid]
    exact Wit.grpPullback_id D.P.A
  · rw [hid]
    exact (Category.comp_id _).trans ((congrArg (fun x => (D.c x).left) (hn a).symm).trans (Category.id_comp _).symm)
  · have e₁ : val ((mulDeg D n).tau a b) (𝟙 _) z J' = val (D.tau (n • a) (n • b)) (𝟙 _) z J' := by
      refine (GlobalTheory.TauTwist.val_tau (mulDeg D n) a b _ hJ').trans (Eq.trans ?_ (GlobalTheory.TauTwist.val_tau D _ _ _ hJ').symm)
      rw [← nsmul_add]
      rfl
    have e₂ : val (T.τ₀ ((n : ℤ) • ib a) ((n : ℤ) • ib b)) ((TK W).hom ≫ spMap (RingHom.id W)) z J =
        val (τ (n • a) (n • b)) (toUnit (TK W)).left z J := by
      rw [hid, Category.comp_id, GlobalTheory.DDataGens.toUnit_TK_left]
      exact congrArg₂ (fun x y => val (τ x y) (jK W) z J) (hn a) (hn b)
    have e₃ : gm (𝟙 (TK W).left) z ⊤ (unitOn (1 : (FractionRing W)ˣ)) = 1 := (congrArg (gm (𝟙 (TK W).left) z ⊤) (map_one _)).trans (map_one _)
    refine e₁.trans ((hK _ _ z J' hJ').trans (Eq.trans ?_ (congrArg₂ (· * ·) e₃ (congrArg (_ * ·) e₂)).symm))
    rw [_root_.one_mul]
    exact val_trans D.P.isLB (toUnit (TK W)) _ _ (hg (n • a) (n • b)) z hJ hJ'

end GlobalTheory.TInjBase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalBaseNsmulDegenerationDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tautologicalBase_nsmul_degenerationData : ∀ {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (b : o →+* W) (D : DegPre W), D.TauBimult → (∀ y, PsiUnitOn D y Set.univ) → ∀ n : ℕ, ∃ (T : TautBase o W) (ib : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), From T (RingHom.id W) (fun _ : Empty => (1 : W)) (fun _ => 0) n (mulDeg D n) ib β ββ w := by
  first | exact @GlobalTheory.TInjBase.main | exact GlobalTheory.TInjBase.main | (intros; apply GlobalTheory.TInjBase.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackCompleteDVROfGenericCompat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackCompleteDVROfGenericCompat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.UPoinc.exists_grpPullback_of_generic_compat : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (ξ : Sp V ⟶ S) (GK : Over (Sp (FractionRing V))) [GrpObj GK] (φ : GK.left ⟶ G₁.left) (γ : GK.left ⟶ G.left), IsGrpPullback GK G₁ (jK V) φ → IsGrpPullback GK G (jK V ≫ ξ) γ → ∃ β : G₁.left ⟶ G.left, IsGrpPullback G₁ G ξ β ∧ φ ≫ β = γ ∧ ∀ (f₁ : G₁ ⟶ G₁) (f : G ⟶ G) (fK : GK ⟶ GK), fK.left ≫ φ = φ ≫ f₁.left → fK.left ≫ γ = γ ≫ f.left → f₁.left ≫ β = β ≫ f.left := by
  intro V _ _ _ hV G₁ _ _ hG₁ S G _ _ hG ξ GK _ φ γ hφ hγ
  haveI : IsDiscreteValuationRing V := hV.1
  haveI : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  have hid : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := isGrpPullback_of_iso (Iso.refl G)
  obtain ⟨β, hβ, e⟩ := GlobalTheory.SemiAbDesc.exists_grpPullback_map V (𝟙 S) G G (𝟙 G.left) hG hid G₁ hG₁ ξ
    (jK V ≫ ξ) (Category.comp_id _) GK φ γ hφ hγ
  rw [Category.comp_id] at e
  refine ⟨β, hβ, e, fun f₁ f fK h₁ h₂ => ?_⟩
  have hj : GlobalTheory.IsGenericPointHom (S := Sp V) (ReciprocityTheory.ChartRestriction.G.Out.jK V) := .fractionField V (FractionRing V)
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  obtain ⟨_, -⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G₁ hG₁
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  have : IsSchemeTheoreticallyDominant φ := .of_isPullback hφ.1.flip
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ φ ?_
  · rw [Category.assoc, hβ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w, hβ.1.w]
  · rw [← Category.assoc, ← h₁, Category.assoc, e, h₂, ← Category.assoc, e]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackCompleteDVROfGenericCompatStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grpPullback_completeDVR_of_generic_compat : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (ξ : Sp V ⟶ S) (GK : Over (Sp (FractionRing V))) [GrpObj GK] (φ : GK.left ⟶ G₁.left) (γ : GK.left ⟶ G.left), IsGrpPullback GK G₁ (jK V) φ → IsGrpPullback GK G (jK V ≫ ξ) γ → ∃ β : G₁.left ⟶ G.left, IsGrpPullback G₁ G ξ β ∧ φ ≫ β = γ ∧ ∀ (f₁ : G₁ ⟶ G₁) (f : G ⟶ G) (fK : GK ⟶ GK), fK.left ≫ φ = φ ≫ f₁.left → fK.left ≫ γ = γ ≫ f.left → f₁.left ≫ β = β ≫ f.left := by
  first | exact @GlobalTheory.UPoinc.exists_grpPullback_of_generic_compat | exact GlobalTheory.UPoinc.exists_grpPullback_of_generic_compat | (intros; apply GlobalTheory.UPoinc.exists_grpPullback_of_generic_compat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapUniqueOfNilpotentNilradical
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidAnyBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem obj_rigid_any_base : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ :=
  fun hL => obj_rigid_of_pol hL obj_isAbelianScheme_dim_rigidified_sym

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapUniqueOfNilpotentNilradical
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ObjMapUnique

theorem objMap_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {o : Obj D l b s} {o' : Obj D l b' s'} {f : S' ⟶ S}
    (m₁ m₂ : ObjMap o' o f) : m₁.toSABMap.φ = m₂.toSABMap.φ :=
  GlobalTheory.obj_rigid_any_base GlobalTheory.lawsAndExpansions.1.1 E H D l B B' b b' S S' s s' o o' f m₁.toSABMap m₂.toSABMap
    fun a ↦ ⟨_, m₁.eta a, m₂.eta a⟩

theorem objMap_unique_of_nilpotent_nilradical :
    ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} (A : Type) [CommRing A], IsNilpotent (nilradical A) → ∀ {S : Scheme.{0}} (s' : Sp A ⟶ Sp (KA l)) (s : S ⟶ Sp (KA l)) (o' : Obj D l (baseKA l) s') (o : Obj D l (baseKA l) s) (f : Sp A ⟶ S) (m₁ m₂ : ObjMap o' o f), m₁.toSABMap.φ = m₂.toSABMap.φ := by
  intro E _ _ _ H D l A _ _ S s' s o' o f m₁ m₂
  exact objMap_unique m₁ m₂

end GlobalTheory.ObjMapUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapUniqueOfNilpotentNilradicalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.objMap_unique_of_nilpotent_nilradical' : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} (A : Type) [CommRing A], IsNilpotent (nilradical A) → ∀ {S : Scheme.{0}} (s' : Sp A ⟶ Sp (KA l)) (s : S ⟶ Sp (KA l)) (o' : Obj D l (baseKA l) s') (o : Obj D l (baseKA l) s) (f : Sp A ⟶ S) (m₁ m₂ : ObjMap o' o f), m₁.toSABMap.φ = m₂.toSABMap.φ := by
  first | exact @GlobalTheory.ObjMapUnique.objMap_unique_of_nilpotent_nilradical | exact GlobalTheory.ObjMapUnique.objMap_unique_of_nilpotent_nilradical | (intros; apply GlobalTheory.ObjMapUnique.objMap_unique_of_nilpotent_nilradical <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationOrderStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationOrderStable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

theorem primPull_constMorV_pull {k : Type} [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V]
    [IsCentralScalar k V] (A₀ : Over (Sp k)) [GrpObj A₀] (g : A₀ ⟶ A₀) [IsMonHom g] (q : primDR A₀) :
    primPull (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g
        ((GlobalTheory.FODef.constMorV k V A₀).pull q) =
      (GlobalTheory.FODef.constMorV k V A₀).pull (primPull (dp0 k) (𝟙 _) g q) := by
  apply Subtype.ext
  have K := (homMor (dp0 k) (𝟙 _) g).isMor.comp (GlobalTheory.FODef.constMorV k V A₀).isMor
  have e1 := IsMor.pullback1_comp (GlobalTheory.FODef.constMorV k V A₀).isMor
    (homMor (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g).isMor K
    (fun _ ↦ rfl) (by simp) q.1
  have e2 := IsMor.pullback1_comp (homMor (dp0 k) (𝟙 _) g).isMor (GlobalTheory.FODef.constMorV k V A₀).isMor K
    (fun _ ↦ rfl) rfl q.1
  exact e1.trans e2.symm

theorem push_mem_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ (c : D.O), ∀ e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (c)) (e)) ∈ (GlobalTheory.HTGlue.glueFil o₀.A f)) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ _ d f hf c e he
  haveI := o₀.act.hom c
  obtain ⟨x, hx, z, hz, hxz⟩ := he
  let g : HdR o₀.A →ₗ[k] HdR o₀.A := GlobalTheory.HTCount.crysAct o₀ c
  have hg : ∀ h, g h = push (dp0 k) (𝟙 _) (o₀.act.act c) h := fun _ ↦ rfl
  refine ⟨g x, push_mem_Fil _ hx, fun j ↦ g (z j) - (f j (g x) - g (f j x)),
    fun j ↦ sub_mem (push_mem_Fil _ (hz j)) ((hf j).1 c x hx), fun q ↦ ?_⟩
  rw [push_apply, primPull_constMorV_pull, hxz]
  congr 2
  funext j
  rw [← push_apply, ← hg]
  simp only [map_add (f := _), LinearMap.add_apply, LinearMap.sub_apply, map_sub]
  abel

end GlobalTheory.HTGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationOrderStableStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalGluedHodgeGraphFiltration_order_stable : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ (c : D.O), ∀ e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (c)) (e)) ∈ (GlobalTheory.HTGlue.glueFil o₀.A f)) := by
  first | exact @GlobalTheory.HTGlue.push_mem_glueFil | exact GlobalTheory.HTGlue.push_mem_glueFil | (intros; apply GlobalTheory.HTGlue.push_mem_glueFil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRelAmpleKTrivOfTrivialisationsGenerate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRelAmpleKTrivOfTrivialisationsGenerate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.Principal

theorem of_isEmpty {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Type} [CommRing S]
    [IsEmpty (Sp S)] (t : SAB H (Sp S)) :
    IsProper t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  refine ⟨inferInstance, ?_, fun T _ s x _ => ?_⟩
  · have := t.semi.quasiCompact
    have := t.semi.separated
    exact GlobalTheory.AmpleLocal.relAmple_of_locally (Sp S) t.G t.PP.L t.PP.isLB inferInstance inferInstance
      fun q => isEmptyElim q
  · have : IsEmpty (Over.mk s).left := ⟨fun p => isEmptyElim (s p)⟩
    exact Over.OverMorphism.ext ((isInitialOfIsEmpty (X := (Over.mk s).left)).hom_ext _ _)

theorem isProper_relAmple_kTriv_of_psiUnitOn : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (f : R), (∀ y, PsiUnitOn P.D.toPre y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) → ∀ tO : SAB H (Sp (Localization.Away f)), SABMap tO t (spMap (algebraMap R (Localization.Away f))) → IsProper tO.G.hom ∧ Out.RelAmple tO.G tO.PP.L ∧ Out.KTriv tO.G tO.PP.L := by
  intro E _ _ _ H R _ _ _ hR t P f hψ tf mf
  let Rf := Localization.Away f
  have hrange : Set.range (spMap (algebraMap R Rf)) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range Rf f
  by_cases hf : f = 0
  · have : IsEmpty (Sp Rf) := ⟨fun z => by
      have hz : f ∉ (spMap (algebraMap R Rf) z).asIdeal := hrange.le ⟨z, rfl⟩
      exact hz ((congrArg (· ∈ (spMap (algebraMap R Rf) z).asIdeal) hf).mpr (Ideal.zero_mem _))⟩
    exact of_isEmpty tf
  obtain ⟨hab, -⟩ := GlobalTheory.Mum.abelian_and_proper_of_psiUnitOn R hR P.D P.A t.G t.semi P.U
    (PrimeSpectrum.basicOpen f) hψ
  have : IsNoetherianRing R := hR.1.1
  have : CharZero R := hR.2
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hi : Function.Injective (algebraMap R Rf) := IsLocalization.injective Rf hle
  have : IsDomain Rf := IsLocalization.isDomain_localization hle
  have : CharZero Rf := charZero_of_injective_algebraMap hi
  have habf : abLocus tf.G = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne t.semi mf.cart.1 z).1 (hab (hrange.le ⟨z, rfl⟩))
  have hg : GlobalTheory.LN.PolAt tf (Out.jK Rf) := GlobalTheory.PolNormal.polAt_generic_pull _ hi mf (GlobalTheory.DatUniq.polAt_of_unif P)
  have hpf : IsProper tf.G.hom := GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus E H Rf tf hg habf
  exact ⟨hpf, GlobalTheory.AbLocusPol.relAmple_kTriv_of_generic tf hpf hg⟩

end GlobalTheory.UCanon.Principal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRelAmpleKTrivOfTrivialisationsGenerateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_relAmple_kTriv_of_trivialisations_generate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (f : R), (∀ y, PsiUnitOn P.D.toPre y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) → ∀ tO : SAB H (Sp (Localization.Away f)), SABMap tO t (spMap (algebraMap R (Localization.Away f))) → IsProper tO.G.hom ∧ Out.RelAmple tO.G tO.PP.L ∧ Out.KTriv tO.G tO.PP.L := by
  first | exact @GlobalTheory.UCanon.Principal.isProper_relAmple_kTriv_of_psiUnitOn | exact GlobalTheory.UCanon.Principal.isProper_relAmple_kTriv_of_psiUnitOn | (intros; apply GlobalTheory.UCanon.Principal.isProper_relAmple_kTriv_of_psiUnitOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameIdentityOfGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameIdentityOfGenericPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.Poinc.Sep.FrameInt

theorem kap_of_generic : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (N : ℕ) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), b ^ N = 1 → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → ∀ (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)), Normd κ → (∀ z J, Good D.P.L z J → val t (toUnit (TF (R := V) (FractionRing V))).left z J ^ (N ^ 2) * val κ ((toUnit (TF (R := V) (FractionRing V))).left ≫ b.left) z J = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J → val t r z J ^ (N ^ 2) * val κ (r ≫ b.left) z J = 1 := by
  intro V _ _ D N b hbN t ht κ hκn hgen Z r z J hJ
  have G := ((SymFrame.grep_gen t ht (𝟙 _)).pow (N ^ 2)).mul (SymFrame.grep_kap κ hκn.1 b)
  obtain ⟨s, hs, vs⟩ := G.out D.P.isLB (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun U _ h => Eq.trans (by
      rw [Fin.prod_univ_two, hbN, ← SymFrame.eta_eq]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, DegPre.lineε, Category.comp_id,
        Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      rw [← natCast_zsmul]
      push_cast
      module) (Fintype.prod_empty _).symm)
  obtain ⟨ρ, hρ⟩ := exists_ratio D.P.isLB rfl s (LB.oneGen D.P.L) hs (oneGen_gen _)
  have hρ1 : ρ = 1 := by
    obtain ⟨z₀⟩ := exists_pt (R := V) (F := FractionRing V)
    obtain ⟨J₀, hJ₀⟩ := exists_good' D.P.isLB z₀
    have a := vs _ (toUnit (TF (R := V) (FractionRing V))) z₀ J₀ hJ₀
    rw [hρ _ _ z₀ J₀ hJ₀, val_one, _root_.mul_one] at a
    simp only [Category.comp_id] at a
    have a1 : gm (toUnit (TF (R := V) (FractionRing V))).left z₀ ⊤ ρ = 1 := a.trans (hgen z₀ J₀ hJ₀)
    have c := gm_top_eq ρ z₀
    rw [a1, Units.val_one, cst_eq, ← map_one (cstH z₀)] at c
    have d := cstH_inj z₀ c
    rw [← map_one (algebraMap V (FractionRing V))] at d
    have e := IsFractionRing.injective V (FractionRing V) d
    apply Units.ext
    have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom :=
      (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.injective
    apply hinj
    rw [Units.val_one, map_one]
    exact e.symm
  have a := vs (Over.mk r) (toUnit _) z J hJ
  rw [hρ _ _ z J hJ, val_one, _root_.mul_one, hρ1, map_one] at a
  simp only [Category.comp_id] at a
  exact a.symm

end GlobalTheory.Poinc.Sep.FrameInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameIdentityOfGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFrame_identity_of_genericPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (N : ℕ) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), b ^ N = 1 → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → ∀ (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)), Normd κ → (∀ z J, Good D.P.L z J → val t (toUnit (TF (R := V) (FractionRing V))).left z J ^ (N ^ 2) * val κ ((toUnit (TF (R := V) (FractionRing V))).left ≫ b.left) z J = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J → val t r z J ^ (N ^ 2) * val κ (r ≫ b.left) z J = 1 := by
  first | exact @GlobalTheory.Poinc.Sep.FrameInt.kap_of_generic | exact GlobalTheory.Poinc.Sep.FrameInt.kap_of_generic | (intros; apply GlobalTheory.Poinc.Sep.FrameInt.kap_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackUniformisingGroupSameGenericFib
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackUniformisingGroupSameGenericFib
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem endU_genMap {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D : DegData V (maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G)
    (E : EndU U.toUnifPre) : E.aA.left ≫ genMap U = genMap U ≫ E.aG.left := by
  have h1 : E.aA ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK V)).map E.aG := by
    rw [Iso.comp_inv_eq, Category.assoc, E.ext, Iso.inv_hom_id_assoc]
  have h1' : E.aA.left ≫ U.gen.inv.left = U.gen.inv.left ≫ ((Over.pullback (jK V)).map E.aG).left := by
    have := congrArg CommaMorphism.left h1
    simpa only [Over.comp_left] using this
  have h2 : ((Over.pullback (jK V)).map E.aG).left ≫ pullback.fst G.hom (jK V) = pullback.fst G.hom (jK V) ≫ E.aG.left :=
    pullback.lift_fst _ _ _
  unfold genMap
  rw [← Category.assoc, h1', Category.assoc, h2, Category.assoc]

theorem exists_ext : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (gm : A.A.left ⟶ H.left), IsGrpPullback A.A H (jK V ≫ ξ) gm → ∃ β : G.left ⟶ H.left, IsGrpPullback G H ξ β ∧ genMap U ≫ β = gm ∧ ∀ (E : EndU U.toUnifPre) (Fm : H ⟶ H), E.aA.left ≫ gm = gm ≫ Fm.left → E.aG.left ≫ β = β ≫ Fm.left := by
  intro B H _ _ hH V _ _ _ hV G _ _ hG D A U ξ gm hgm
  obtain ⟨⟨hN, -, hIC, -⟩, -⟩ := hV
  haveI := hN
  haveI := hIC
  have gpA : IsGrpPullback A.A G (jK V) (genMap U) := by
    have := U.gen_hom
    have : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK V))).congr
      (Category.id_comp _) rfl
  have : IsMonHom (Iso.refl H).hom := by show IsMonHom (𝟙 H); infer_instance
  have hHH : IsGrpPullback H H (𝟙 B) (𝟙 H.left) := isGrpPullback_of_iso (Iso.refl H)
  obtain ⟨β, hβ, hβg⟩ := GlobalTheory.SemiAbDesc.exists_grpPullback_map V (𝟙 B) H H (𝟙 _) hH hHH G hG ξ (jK V ≫ ξ)
    (Category.comp_id _) A.A (genMap U) gm gpA hgm
  have hβg' : genMap U ≫ β = gm := by simpa using hβg
  refine ⟨β, hβ, hβg', ?_⟩
  intro E Fm hE
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian H hH
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  haveI : IsSchemeTheoreticallyDominant (genMap U) := .of_isPullback gpA.1.flip
  have key := endU_genMap U E
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant H.hom ?_ (genMap U) ?_
  · rw [Category.assoc, Category.assoc, Over.w Fm, hβ.1.w, ← Category.assoc, Over.w E.aG]
  · rw [← Category.assoc, ← key, Category.assoc, hβg', hE, ← Category.assoc, hβg']

end GlobalTheory.Poinc.Sep.Spz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackUniformisingGroupSameGenericFibStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grpPullback_uniformisingGroup_sameGenericFibre : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (gm : A.A.left ⟶ H.left), IsGrpPullback A.A H (jK V ≫ ξ) gm → ∃ β : G.left ⟶ H.left, IsGrpPullback G H ξ β ∧ genMap U ≫ β = gm ∧ ∀ (E : EndU U.toUnifPre) (Fm : H ⟶ H), E.aA.left ≫ gm = gm ≫ Fm.left → E.aG.left ≫ β = β ≫ Fm.left := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.exists_ext | exact GlobalTheory.Poinc.Sep.Spz.exists_ext | (intros; apply GlobalTheory.Poinc.Sep.Spz.exists_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfIsometryApply
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La}

theorem IsOpp.proj_unique (h : IsOpp D Z Z') {a b b' : D.La} (hb : b ∈ Z') (hb' : b' ∈ Z')
    (h1 : a - b ∈ perp D Z) (h2 : a - b' ∈ perp D Z) : b = b' := by
  have := h.eq_zero (sub_mem hb hb') (by
    have := sub_mem h2 h1
    rwa [sub_sub_sub_cancel_left] at this)
  exact sub_eq_zero.1 this

def IsOpp.proj (h : IsOpp D Z Z') : D.La →ₗ[𝓞 E] Z' where
  toFun a := ⟨(h.exists_sub_mem_perp a).choose, (h.exists_sub_mem_perp a).choose_spec.1⟩
  map_add' a b := by
    have ha := (h.exists_sub_mem_perp a).choose_spec
    have hb := (h.exists_sub_mem_perp b).choose_spec
    have hab := (h.exists_sub_mem_perp (a + b)).choose_spec
    apply Subtype.ext
    refine h.proj_unique hab.1 (add_mem ha.1 hb.1) hab.2 ?_
    have := add_mem ha.2 hb.2
    simpa [sub_add_sub_comm] using this
  map_smul' c a := by
    have ha := (h.exists_sub_mem_perp a).choose_spec
    have hca := (h.exists_sub_mem_perp (c • a)).choose_spec
    apply Subtype.ext
    refine h.proj_unique hca.1 (Z'.smul_mem c ha.1) hca.2 ?_
    have := (perp D Z).smul_mem c ha.2
    simpa [smul_sub] using this

theorem IsOpp.sub_proj_mem (h : IsOpp D Z Z') (a : D.La) : a - h.proj a ∈ perp D Z :=
  (h.exists_sub_mem_perp a).choose_spec.2

theorem IsOpp.proj_eq (h : IsOpp D Z Z') {a b : D.La} (hb : b ∈ Z') (hab : a - b ∈ perp D Z) : (h.proj a : D.La) = b :=
  h.proj_unique (h.proj a).2 hb (h.sub_proj_mem a) hab

theorem IsOpp.proj_of_mem (h : IsOpp D Z Z') {b : D.La} (hb : b ∈ Z') : (h.proj b : D.La) = b :=
  h.proj_eq hb (by simp)

theorem IsOpp.proj_of_perp (h : IsOpp D Z Z') {a : D.La} (ha : a ∈ perp D Z) : (h.proj a : D.La) = 0 :=
  h.proj_eq Z'.zero_mem (by simpa using ha)

variable (D)

theorem exists_adjoint (σ : D.La →ₗ[𝓞 E] D.La) : ∃ w : D.La →ₗ[𝓞 E] D.La, ∀ a b, D.EF (w a) b = D.EF a (σ b) := by
  choose w hw using fun a => D.unimod.2 ((D.EF a).comp (σ.restrictScalars ℤ))
  refine ⟨{ toFun := w, map_add' := fun a b => D.unimod.1 ?_, map_smul' := fun c a => D.unimod.1 ?_ }, fun a b => ?_⟩
  · ext x; simp [hw]
  · ext x
    simp only [hw, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, RingHom.id_apply, D.adj]
    rw [← σ.map_smul]
  · exact congrArg (fun f => f b) (hw a)

theorem bijective_of_isometry (g : D.La →ₗ[𝓞 E] D.La) (hg : ∀ a b, D.EF (g a) (g b) = D.EF a b) :
    Function.Bijective g := by
  obtain ⟨w, hw⟩ := exists_adjoint D g
  have hwg : ∀ a, w (g a) = a := fun a => D.unimod.1 (LinearMap.ext fun b => by rw [hw, hg])
  have hws : Function.Surjective w := fun a => ⟨g a, hwg a⟩
  haveI := D.fin
  have hwi : Function.Injective w := OrzechProperty.injective_of_surjective_endomorphism w hws
  refine ⟨fun a b hab => by rw [← hwg a, ← hwg b, hab], fun a => ⟨w a, hwi (by rw [hwg])⟩⟩

def equivOfIsometry (g : D.La →ₗ[𝓞 E] D.La) (hg : ∀ a b, D.EF (g a) (g b) = D.EF a b) : D.La ≃ₗ[𝓞 E] D.La :=
  LinearEquiv.ofBijective g (bijective_of_isometry D g hg)

@[simp] theorem equivOfIsometry_apply (g : D.La →ₗ[𝓞 E] D.La) (hg : ∀ a b, D.EF (g a) (g b) = D.EF a b) (a : D.La) :
    equivOfIsometry D g hg a = g a := rfl

end GlobalTheory.LowFilt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceLeHodgeFiltration
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceLeHodgeFiltration
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTCount

theorem crysAct_mem_Fil {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    {b : GlobalTheory.UPel.HT.Base D R} {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R} (o₀ : GlobalTheory.UPel.HT.Obj b N t)
    (x : D.O) {h : HdR o₀.A} (hh : h ∈ Fil o₀.A) : crysAct o₀ x h ∈ Fil o₀.A := by
  haveI := o₀.act.hom x
  exact push_mem_Fil (o₀.act.act x) hh

theorem crysAct_intCast {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    {b : GlobalTheory.UPel.HT.Base D R} {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R} (o₀ : GlobalTheory.UPel.HT.Obj b N t)
    (n : ℤ) (h : HdR o₀.A) : crysAct o₀ (algebraMap (𝓞 D.F) D.O (n : 𝓞 D.F)) h = (n : k) • h := by
  rw [map_intCast, map_intCast, Int.cast_smul_eq_zsmul]
  rfl

theorem lieZ_le_Fil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (β : R →+* k) (s : Sp k ⟶ Sp R), s = spMap β →
    ∀ o₀ : GlobalTheory.UPel.HT.Obj b N s, GlobalTheory.HTCount.lieZ o₀ β ≤ Fil o₀.A := by
  intro p _ D R _ b N k _ β s hs o₀
  rw [lieZ, Submodule.span_le]
  rintro z ⟨r, lam, c, y, ⟨x, rfl⟩, hlam, rfl⟩
  set T := crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) with hT

  have hω : D.ω * D.ω = (D.tr : 𝓞 D.F) * D.ω - (D.nm : 𝓞 D.F) := by
    rw [← D.nm_eq, ← D.tr_eq]; ring
  have hT2 : T (T x) = (D.tr : k) • T x - (D.nm : k) • x := by
    have := congrArg (fun u => crysAct o₀ (algebraMap (𝓞 D.F) D.O u) x) hω
    simp only [map_mul, map_sub, Module.End.mul_apply, LinearMap.sub_apply] at this
    rw [crysAct_intCast, crysAct_intCast] at this
    exact this

  have hρ : β b.ρ * ((D.tr : k) - β b.ρ) = (D.nm : k) := by
    have := congrArg β b.ρ_root
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_intCast, map_zero] at this
    linear_combination -this

  have hy0 : T ((T - ((D.tr : k) - β b.ρ) • 1) x) - β b.ρ • (T - ((D.tr : k) - β b.ρ) • 1) x = 0 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hT2]
    rw [← hρ]
    module
  obtain ⟨w, hw, hyw⟩ := GlobalTheory.HTSummand.lie_mod_fil p D R b N k β s hs o₀ _ (hy0 ▸ zero_mem _)
  set y := (T - ((D.tr : k) - β b.ρ) • 1) x
  set q := (Fil o₀.A).mkQ
  have key : ∀ c' : 𝓞 D.F, q (crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y) = ∑ i, β (b.t i c') • q (w i) := by
    intro c'
    have h1 : crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y - ∑ i, crysAct o₀ (algebraMap (𝓞 D.F) D.O c') (w i) ∈ Fil o₀.A := by
      have := crysAct_mem_Fil o₀ (algebraMap (𝓞 D.F) D.O c') hyw
      rwa [map_sub, map_sum] at this
    have e1 : q (crysAct o₀ (algebraMap (𝓞 D.F) D.O c') y) = q (∑ i, crysAct o₀ (algebraMap (𝓞 D.F) D.O c') (w i)) :=
      (Submodule.Quotient.eq _).2 h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_smul]
    exact (Submodule.Quotient.eq _).2 (hw i c')
  rw [SetLike.mem_coe, ← Submodule.Quotient.mk_eq_zero]
  change q _ = 0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, key, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hlam, zero_smul, Finset.sum_const_zero]

end GlobalTheory.HTCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceLeHodgeFiltrationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieConditionHodgeSubspace_le_hodgeFiltration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (β : R →+* k) (s : Sp k ⟶ Sp R), s = spMap β → ∀ o₀ : GlobalTheory.UPel.HT.Obj b N s, GlobalTheory.HTCount.lieZ o₀ β ≤ Fil o₀.A := by
  first | (exact @GlobalTheory.HTCount.lieZ_le_Fil) | (exact GlobalTheory.HTCount.lieZ_le_Fil) | (intros; apply GlobalTheory.HTCount.lieZ_le_Fil  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFormFactorThroughTraceGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFormFactorThroughTraceGenerator
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_int_eq_mul_of_ne_zero {E : Type} [Field E] [NumberField E] (t : 𝓞 E) (ht : t ≠ 0) :
    ∃ (N : ℤ) (c : 𝓞 E), N ≠ 0 ∧ (N : 𝓞 E) = t * c := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {t}))
  refine ⟨(Ideal.absNorm (Ideal.span {t}) : ℤ), c, ?_, ?_⟩
  · have : Ideal.absNorm (Ideal.span {t}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ht
    exact_mod_cast this
  · rw [Int.cast_natCast, ← hc, mul_comm]

theorem eq_zero_of_forall_theta_mul {E : Type} [Field E] [NumberField E] {θ : 𝓞 E →+ ℤ} (hθ : θ ≠ 0)
    {t : 𝓞 E} (h : ∀ u, θ (t * u) = 0) : t = 0 := by
  by_contra ht
  obtain ⟨N, c, hN, hc⟩ := exists_int_eq_mul_of_ne_zero t ht
  apply hθ
  ext v
  have := h (c * v)
  rw [← mul_assoc, ← hc, ← zsmul_eq_mul, map_zsmul, smul_eq_mul] at this
  simpa [hN] using this

theorem exists_linear_theta_factor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    (Z' : Submodule (𝓞 E) D.La) (θ : 𝓞 E →+ ℤ) (s : 𝓞 E) (hs : s ≠ 0)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u)) (w : D.La),
    ∃ ℓ : Z' →ₗ[𝓞 E] 𝓞 E, ∀ x : Z', θ (ℓ x) = D.EF x (H.bar s • w) := by
  intro E _ _ _ H D Z' θ s hs hgen w
  have hθ : θ ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ : ∃ i, (Module.Free.chooseBasis ℤ (𝓞 E)).repr s i ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hs ((Module.Free.chooseBasis ℤ (𝓞 E)).repr.injective (by ext i; simp [hne i]))
    obtain ⟨t, ht⟩ := hgen ((Module.Free.chooseBasis ℤ (𝓞 E)).coord i).toAddMonoidHom
    have := ht 1
    simp [h0] at this
    exact hi this
  have uniq : ∀ t t' : 𝓞 E, (∀ u, θ (t * u) = θ (t' * u)) → t = t' := fun t t' h =>
    sub_eq_zero.1 (eq_zero_of_forall_theta_mul hθ fun u => by rw [sub_mul, map_sub, h, sub_self])
  let ψ : D.La → 𝓞 E →+ ℤ := fun x => AddMonoidHom.mk' (fun u => D.EF (u • x) w) (fun a b => by simp [add_smul])
  choose T hT using fun x : Z' => hgen (ψ x)
  refine ⟨{ toFun := T, map_add' := ?_, map_smul' := ?_ }, fun x => ?_⟩
  · intro x y
    apply uniq
    intro u
    rw [← hT (x + y) u, add_mul, map_add (f := _), ← hT x u, ← hT y u]
    simp [ψ, smul_add]
  · intro c x
    show T (c • x) = c * T x
    apply uniq
    intro u
    rw [← hT (c • x) u, show c * T x * u = T x * (c * u) by ring, ← hT x (c * u)]
    simp only [ψ, AddMonoidHom.mk'_apply, Submodule.coe_smul, smul_smul]
    rw [show s * u * c = s * (c * u) by ring]
  · show θ (T x) = _
    have := hT x 1
    rw [mul_one, mul_one] at this
    rw [← this]
    simp only [ψ, AddMonoidHom.mk'_apply]
    exact D.adj s x w

end GlobalTheory.LowFilt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFormFactorThroughTraceGeneratorStatement
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearForm_factor_through_traceGenerator : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    (Z' : Submodule (𝓞 E) D.La) (θ : 𝓞 E →+ ℤ) (s : 𝓞 E) (hs : s ≠ 0)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u)) (w : D.La),
    ∃ ℓ : Z' →ₗ[𝓞 E] 𝓞 E, ∀ x : Z', θ (ℓ x) = D.EF x (H.bar s • w) := by
  first | exact @GlobalTheory.LowFilt.exists_linear_theta_factor | exact GlobalTheory.LowFilt.exists_linear_theta_factor | (intros; apply GlobalTheory.LowFilt.exists_linear_theta_factor <;> assumption)
end
end
end
