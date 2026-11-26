module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfWeightSum
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpansionSectionLineBundlePower

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianDim

theorem exists_relDim_of_connected {S : Scheme.{0}} [ConnectedSpace S] (B : Over S) [GrpObj B]
    (hB : IsAbelianScheme B) : ∃ g, SmoothOfRelativeDimension g B.hom := by
  have := hB.smooth
  have := hB.geomConnected
  have : ConnectedSpace B.left := (GroupConn.connectedSpace_group S B).1
  obtain ⟨x⟩ : Nonempty B.left := inferInstance
  exact exists_dim_of_preconnected B.hom x

theorem connectedSpace_spec_of_isLocalRing (A : Type) [CommRing A] [IsLocalRing A] :
    ConnectedSpace (Spec (CommRingCat.of A)) := by
  show ConnectedSpace (PrimeSpectrum A)
  rw [connectedSpace_iff_univ]
  refine ⟨⟨IsLocalRing.closedPoint A, trivial⟩, ?_⟩
  intro u v hu hv huv ⟨x, _, hx⟩ ⟨y, _, hy⟩
  have hc : IsLocalRing.closedPoint A ∈ u ∪ v := huv trivial
  rcases hc with h | h
  · exact ⟨y, trivial, (IsLocalRing.specializes_closedPoint y).mem_open hu h, hy⟩
  · exact ⟨x, trivial, hx, (IsLocalRing.specializes_closedPoint x).mem_open hv h⟩

theorem exists_relDim : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B], IsAbelianScheme B → ∃ g, SmoothOfRelativeDimension g B.hom := by
  intro A _ _ B _ hB
  have := connectedSpace_spec_of_isLocalRing A
  exact exists_relDim_of_connected B hB

end GlobalTheory.AbelianDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PtEqOfProportional
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionImage

open FieldBaseChange

theorem translT_translPt {S : Scheme.{0}} {A T : Over S} [GrpObj A] (x y : T ⟶ A) :
    translT A x ≫ translPt A y = translPt A (y * x) := by
  show lift (fst T A) ((fst T A ≫ x) * snd T A) ≫ ((fst T A ≫ y) * snd T A) = (fst T A ≫ (y * x)) * snd T A
  simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd, _root_.mul_assoc]

theorem translPt_one {S : Scheme.{0}} {A : Over S} [GrpObj A] (T : Over S) :
    translPt A (1 : T ⟶ A) = snd T A := by
  show (fst T A ≫ 1) * snd T A = _
  rw [MonObj.comp_one, _root_.one_mul]

theorem translT_inv {S : Scheme.{0}} {A T : Over S} [GrpObj A] (x : T ⟶ A) :
    translT A x⁻¹ ≫ translT A x = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · rw [Category.assoc, Category.id_comp]
    exact (congrArg (_ ≫ ·) (lift_snd _ _)).trans
      ((translT_translPt _ _).trans (by rw [mul_inv_cancel, translPt_one]))

theorem eq_of_gen {S : Scheme.{0}} (P : PolAV S) {F : Type} [CommRing F] (q : Spec (CommRingCat.of F) ⟶ S)
    (x x' : Over.mk q ⟶ P.A)
    (r : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(translPt P.A x).left, (translPt P.A x').left] ![1, -1]))
    (hr : r.IsGen) : x = x' := by
  refine mul_inv_eq_one.1 (P.ktriv F q (x * x'⁻¹) fun p => ⟨⊤, trivial, ?_⟩)
  obtain ⟨w, hw, -⟩ := VVRank.exists_gen_pullTo
    (φ' := ![(translPt P.A (x * x'⁻¹)).left, (snd (Over.mk q) P.A).left]) r hr (translT P.A x'⁻¹).left (fun i => by
      fin_cases i
      · exact congrArg (fun q => q.left) (translT_translPt x'⁻¹ x)
      · exact congrArg (fun q => q.left) ((translT_translPt x'⁻¹ x').trans
          (by rw [mul_inv_cancel, translPt_one])))
  exact exists_isGen_pull (translDiff P.A P.L (x * x'⁻¹)) w hw _

theorem exists_smul_of_phiVal {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (p : QkPt D F k)
    (w w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ s t t' : Fam D F k, DVR.PhiVal p w s.s t.s → DVR.PhiVal p w' s.s t'.s → t' = c • t := by
  obtain ⟨a, ha⟩ := H1.exists_const D.P.L D.P.isLB (𝟙 _) (fun a => ⟨a, rfl⟩)
    (LB.mulGen D.P.L _ _ _ _ w' (LB.invGen D.P.L _ _ w))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hw' (DVR.invGen_isGen _ _ _ _ hw)) (fun U _ h => by
      refine (DVR.prod_sum₂ _ (c := ∏ i, h (DegPre.lineφ D F p.g.b i) ^ DegPre.lineε k i) rfl
        (DVR.prod_neg _ _ rfl)).trans ?_
      exact mul_inv_cancel _)
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  refine ⟨c, ?_, fun s t t' h h' => DVR.phi_unique p w' h' fun α β e' T ρ z J hJ => ?_⟩
  · rintro rfl
    let z : (TF (R := R) F).left := (default : PrimeSpectrum F)
    choose J hJ using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    refine Units.ne_zero _ ((ha _ (𝟙 _) z J hJ).trans ?_)
    exact (congrArg _ (map_zero _)).trans (gs_zero' _ z ⊤ trivial)
  · have e := ha _ (ρ ≫ fst _ _).left z J hJ
    rw [val_mul hJ, val_inv, Category.comp_id] at e
    refine (DVR.sval_smul c t β ρ.left z hJ).trans ?_
    rw [h α β e' T ρ z J hJ, val_mul hJ, val_mul hJ]
    refine (congrArg (· * _) e.symm).trans ?_
    rw [mul_left_comm, ← Units.val_mul]
    congr 2
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem pt_eq_of_proportional (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Spec (CommRingCat.of K)))
    {F : Type} [Field F] (q : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K)) {n : ℕ} (hn : 1 ≤ n)
    (θ θ' : ThetaGrp P.A P.L (n : ℤ) (Over.mk q)) (c : Γ((Over.mk q).left, ⊤)ˣ)
    (H : ∀ t u u', IsActOf P.A P.L (n : ℤ) θ t u → IsActOf P.A P.L (n : ℤ) θ' t u' → ∀ y J, Good P.L y J →
      VVRank.sv P.A u' (𝟙 _) y J =
        (gm (𝟙 _ ≫ (fst (Over.mk q) P.A).left) y ⊤ c).val * VVRank.sv P.A u (𝟙 _) y J) : θ.pt = θ'.pt := by
  have hL := P.isLB
  let T := Over.mk q
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ P.A
  have : IsIntegral (T ⊗ P.A).left :=
    pullback_of_geometrically' GeometricallyIntegral.geometrically_isIntegral F _
  have hN : ∀ y : (T ⊗ P.A).left, IsIntegrallyClosed ((T ⊗ P.A).left.presheaf.stalk y) := fun y =>
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ (fst T P.A).left
      (inferInstanceAs (Smooth (pullback.fst q P.A.hom)))).2.1.2 y
  obtain ⟨b, hb, -⟩ := BoxSpan.exists_basis hS P 1 le_rfl F q
  have : Nontrivial Γ(T.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hne := hb.ne_zero ⟨0, by simp⟩
  let th : LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => (snd T P.A).left) (fun _ => ((1 : ℕ) : ℤ))) :=
    SecM.toSec P.A (b ⟨0, by simp⟩)
  have tr : ∀ x : T ⟶ P.A, ∃ s : LB.Sec (LB.LinComb P.L (K := PUnit) (fun _ => (translPt P.A x).left) (fun _ => 1)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ P.A).left) (z : Z) (J), Good P.L z J →
        sval s r z J = sval th (r ≫ (translT P.A x).left) z J := fun x => by
    have e : (translT P.A x).left ≫ (snd T P.A).left = (translPt P.A x).left :=
      congrArg (fun q => q.left) (lift_snd _ _ : translT P.A x ≫ snd T P.A = _)
    obtain ⟨s, hs⟩ := exists_sec hL (φ' := fun _ : PUnit => (translPt P.A x).left) (ε' := fun _ => 1)
      (fun U _ h => by simp only [e, Fintype.prod_unique, Nat.cast_one]) (H1.SectionArithmetic.pullSec th (translT P.A x).left)
    exact ⟨s, fun Z r z J hJ => (hs Z r z J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ r z hJ)⟩
  obtain ⟨s, hs⟩ := tr θ.pt
  obtain ⟨s', hs'⟩ := tr θ'.pt
  obtain ⟨t, ht⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T P.A).left) (ε' := fun _ => (n : ℤ))
    (fun U _ h => by simp) (H1.SectionArithmetic.powSec fun _ : Fin n => th)
  have ht' : ∀ (r : (T ⊗ P.A).left ⟶ (T ⊗ P.A).left) y J, Good P.L y J → sval t r y J = sval th r y J ^ n :=
    fun r y J hJ => by
      rw [ht _ r y J hJ, H1.SectionArithmetic.sval_powSec _ r y hJ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  obtain ⟨u, hu⟩ : ∃ u, IsActOf P.A P.L (n : ℤ) θ t u := VVRank.exists_isTwistPull P.A hL θ.isGen t
  obtain ⟨u', hu'⟩ : ∃ u, IsActOf P.A P.L (n : ℤ) θ' t u := VVRank.exists_isTwistPull P.A hL θ'.isGen t
  have hc : (constGen P.A P.L c).IsGen := isGen_of_gm _ fun y j j' _ _ => by
    obtain rfl : j = j' := Subsingleton.elim _ _
    rw [trF, Fintype.prod_empty, _root_.one_mul]
  obtain ⟨v, hv, hv'⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(translPt P.A θ'.pt).left, (translPt P.A θ.pt).left])
    (ε' := ![(n : ℤ), -(n : ℤ)]) (fun U _ h => by
      simp [Fintype.prod_sum_type, Fin.prod_univ_two])
    (LB.mulGen P.L _ _ _ _ (LB.invGen P.L ![(snd T P.A).left, (translPt P.A θ'.pt).left] ![(n : ℤ), -(n : ℤ)] θ'.φ)
      (LB.mulGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(n : ℤ), -(n : ℤ)] _ _ θ.φ
        (constGen P.A P.L c)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ θ'.isGen)
      (DVR.mulGen_isGen _ _ _ _ _ _ _ θ.isGen hc))
  obtain ⟨r, hr, -⟩ := RootUnit.exists_gen_of_pow _ _ hN P.L hL _ _ n hn s' s v hv (by
    by_contra h0
    have h0' : ∀ j, s.f j = 0 := fun j => by_contra fun hj => h0 ⟨j, hj⟩
    refine hne (Subtype.ext (funext fun j => sec_ext_val (s := th) (s' := H1.SectionArithmetic.secZero _) hL
      (fun y J hJ => ?_) j))
    have e := hs _ (translT P.A θ.pt⁻¹).left y J hJ
    rw [← Over.comp_left, translT_inv, Over.id_left] at e
    refine e.symm.trans (Eq.trans ?_ (gs_zero' _ y _ (hJ.mem _ _)).symm)
    exact (congrArg (gs _ y _) (h0' _)).trans (gs_zero' _ y _ (hJ.mem _ _))) (fun y J hJ => by
    have e := H t u u' hu hu' y J hJ
    rw [VVRank.sv_of_isTwistPull P.A hu _ y hJ, VVRank.sv_of_isTwistPull P.A hu' _ y hJ] at e
    have e₁ := (ht' _ y J hJ).trans (congrArg (· ^ n) (hs _ (𝟙 _) y J hJ).symm)
    have e₂ := (ht' _ y J hJ).trans (congrArg (· ^ n) (hs' _ (𝟙 _) y J hJ).symm)
    have e₃ := (congrArg _ e₂).symm.trans (e.trans (congrArg _ (congrArg _ e₁)))
    have e₄ := (hv' _ (𝟙 _) y J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_inv _ _)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (H1.val_constGen _ c _ y J)))))
    rw [e₄, Units.val_mul, _root_.mul_assoc, Units.eq_inv_mul_iff_mul_eq, Units.val_mul, _root_.mul_assoc]
    exact e₃.trans (mul_left_comm _ _ _))
  exact (eq_of_gen P q _ _ r hr).symm

theorem qkToAkU_unique : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p : QkPt D.toPre F n) (x x' : TFK (R := R) F ⟶ A.A), QkToAkU U.toUnifPre F n p x → QkToAkU U.toUnifPre F n p x' → x = x' := by
  intro hL _ R _ _ I _ D A G _ _ _ U F _ _ n hn p x x' hx hx'
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨θ, rfl, -⟩ := TorsionTheta.exists_theta_acts hL.kerPow _ A F _ n hn x (hx w₀ hw₀).1
  obtain ⟨θ', rfl, -⟩ := TorsionTheta.exists_theta_acts hL.kerPow _ A F _ n hn x' (hx' w₀ hw₀).1
  obtain ⟨w, hw, h⟩ := (hx w₀ hw₀).2 θ rfl
  obtain ⟨w', hw', h'⟩ := (hx' w₀ hw₀).2 θ' rfl
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hL.globalFns U F hn w₀ hw₀
  obtain ⟨c, hc, hcs⟩ := exists_smul_of_phiVal p w w' hw hw'
  refine pt_eq_of_proportional hL.secBaseChange A _ hn θ θ'
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc))
    fun t u u' hu hu' y J hJ => ?_
  have a := hcs _ _ _
    ((DVR.phiRel_iff hL.globalFns p w hw _ _).1 (h t u _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) hu))
    ((DVR.phiRel_iff hL.globalFns p w' hw' _ _).1 (h' t u' _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) hu'))
  obtain rfl := e.injective (a.trans (e.map_smul c u).symm)
  exact (sval_smul' hJ _ c _).trans (congrArg (· * _) (gs_unit _ y ⊤ trivial
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc))))

end GlobalTheory.TorsionImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInIffScalarMem
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory

namespace PsiScalIn

open PsiInPull PsiInPow

variable {R : Type} [CommRing R] [IsDomain R]

def sig (z : Spec (CommRingCat.of (FractionRing R))) :
    FractionRing R →+* (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z :=
  ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ z trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom

theorem gs_scal_id (z : Spec (CommRingCat.of (FractionRing R))) (c : FractionRing R) :
    gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing R)))) c) = sig z c := by
  rw [gs_eq _ z ⊤ trivial]; rfl

theorem gs_toOpen (z : Spec (CommRingCat.of (FractionRing R))) (V : (Spec (CommRingCat.of R)).Opens)
    (hz : jK R z ∈ V) (r : R) : gs (jK R) z V (DegPre.toOpen V r) = sig z (algebraMap R _ r) := by
  have nat := congrArg (fun g => g.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  refine (gs_res (jK R) z (le_top : V ≤ ⊤) hz _).trans ((gs_eq (jK R) z ⊤ trivial _).trans ?_)
  simp only [sig, RingHom.comp_apply]
  rw [nat]
  rfl

theorem key (D : DegPre R)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing R)ˣ) (h : PsiScal D ga a) (χ : D.X) (q : D.P.L.ι)
    (V : (Spec (CommRingCat.of R)).Opens) (hle : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q)
    (z : Spec (CommRingCat.of (FractionRing R))) (hz : jK R z ∈ V) :
    ∃ u : Γ(Spec (CommRingCat.of R), V)ˣ,
      (gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => q)) ((D.psi χ).s (fun _ => q))).val =
        sig z (a χ).val * gs (jK R) z V u.val := by
  have hle' : V ≤ LB.wchart D.P.L (fun _ : PUnit => (D.c χ).left) (fun _ => q) := fun y hy =>
    mem_wchart _ _ _ _ (hle hy)
  obtain ⟨J, hJ, e⟩ := exists_good D.P.L D.P.isLB (Z := (TK R).left) z (K := PUnit) (fun _ => D.xK χ) (fun _ => q)
    (fun _ _ _ => rfl) (fun _ => hle hz)
  have e0 : J (D.xK χ) = q := e PUnit.unit
  have v := (h χ).2 (TK R) (𝟙 _) z J hJ
  have v1 := val_of (D.psi χ) (𝟙 _) z J (fun _ => q) (fun _ => (congrArg J (Category.id_comp _)).trans e0)
  have v2 := val_of (ga χ) (toUnit (TK R)).left z J (fun _ => q) (fun _ => e0)
  refine ⟨res hle' ((ga χ).s (fun _ => q)), (congrArg Units.val v1).symm.trans (v.trans ?_)⟩
  refine congrArg₂ (· * ·) (gs_scal_id z _) ?_
  refine (congrArg Units.val v2).trans ?_
  exact ((gs_unit _ _ _ hz _).trans (congrArg Units.val (gm_res _ _ hle' hz _))).symm

theorem main_local [IsLocalRing R] (D : DegPre R)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing R)ˣ) (h : PsiScal D ga a) (χ : D.X) (J : Ideal R) :
    D.PsiIn χ J ↔ ∃ r ∈ J, algebraMap R (FractionRing R) r = (a χ).val := by
  constructor
  · intro H
    obtain ⟨q, hq⟩ := exists_chart D.P.isLB ((D.c χ).left (IsLocalRing.closedPoint R))
    have hle : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q := fun y _ =>
      (IsLocalRing.specializes_closedPoint y).mem_open ((D.c χ).left ⁻¹ᵁ D.P.L.U q).isOpen hq
    obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
    obtain ⟨r, hr, e⟩ := gs_of_psiIn D χ J H q ⊤ (isAffineOpen_top _) hle z trivial
    obtain ⟨u, hu⟩ := key D ga a h χ q ⊤ hle z trivial
    have hs : Function.Surjective (DegPre.toOpen (R := R) ⊤) := by
      intro b
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b, ?_⟩
      simp [DegPre.toOpen]
    obtain ⟨s, hsJ, es⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 (Ideal.mul_mem_right (u⁻¹).val _ hr)
    refine ⟨s, hsJ, (sig z).injective ?_⟩
    have hz : jK R z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
    rw [← gs_toOpen z ⊤ hz, es, gs_mul _ _ _ hz, e.trans hu, _root_.mul_assoc,
      ← gs_mul _ _ _ hz, Units.mul_inv, gs_eq _ _ _ hz, map_one, map_one, _root_.mul_one]
  · rintro ⟨r, hr, e⟩
    refine psiIn_of_gs D χ J fun q V _ hle z hz => ?_
    obtain ⟨u, hu⟩ := key D ga a h χ q V hle z hz
    refine ⟨DegPre.toOpen V r * u.val, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr), ?_⟩
    rw [gs_mul _ _ _ hz, gs_toOpen z V hz, e]
    exact hu.symm

end PsiScalIn

theorem psiIn_iff_scalar_mem : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegPre V) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a → ∀ (χ : D.X) (J : Ideal V), J ≠ ⊥ → (D.PsiIn χ J ↔ ∃ r ∈ J, algebraMap V (FractionRing V) r = (a χ).val) :=
  fun _ _ _ _ D ga a h χ J _ => PsiScalIn.main_local D ga a h χ J

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FourierJacobiExpansionOverFieldInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FourierJacobiExpansionOverFieldInjective
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ExpFUniq

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep GlobalTheory.ExpansionSingleValued

theorem split_iff {R F : Type} [CommRing R] [CommRing F] [Algebra R F] {X X₀ : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] {L : LB X₀} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (X ⟶ X₀)}
    {ε : K → ℤ} {Λ κ : Type} [Fintype Λ] [Fintype κ] (b : κ → F) (hb : LinearIndependent R b) (a : Λ → κ → R)
    (σ : Λ → LB.Sec (LB.LinComb L φ ε)) (τ : κ → LB.Sec (LB.LinComb L φ ε)) (τ₀ : LB.Sec (LB.LinComb L φ ε))
    (hτ : ∀ l (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J → sval (τ l) r z J =
      ∑ i, gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a i l)) * sval (σ i) r z J)
    (h₀ : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J → sval τ₀ r z J = 0) :
    (∀ l, τ l = τ₀) ↔ ∀ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Z ⟶ X),
      r ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) → ∀ (z : Z) (J), Good L z J →
        ∑ i, germOf q z (∑ l, a i l • b l) * sval (σ i) r z J = 0 := by
  replace hτ : ∀ l (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J → sval (τ l) r z J =
      ∑ i, germOf (r ≫ p) z (a i l) * sval (σ i) r z J := fun l Z r z J hJ =>
    (hτ l Z r z J hJ).trans (Finset.sum_congr rfl fun i _ => congrArg (· * _) (germOf_apply _ _ _).symm)
  constructor
  · intro h Z q r e z J hJ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    have h₁ := (hτ l Z r z J hJ).symm.trans ((congrArg (fun s => sval s r z J) (h l)).trans (h₀ Z r z J hJ))
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ((Finset.mul_sum _ _ (germOf q z (b l))).symm.trans
      ((congrArg _ h₁).trans (mul_zero _)))
    rw [Algebra.smul_def, map_mul, e, germOf_map, mul_comm (germOf q z _), _root_.mul_assoc]
    rfl
  · intro H l
    refine SecOps.sec_ext (sec_ext_val hL fun y J hJ => ?_)
    rw [h₀ _ _ y J hJ, hτ l _ _ y J hJ, Category.id_comp]
    refine split_relation p y (hJ.mem φ (𝟙 X)) b hb a (fun i => (σ i).f fun k => J (𝟙 X ≫ φ k))
      (fun Z q r e z hz => ?_) l
    obtain ⟨J', hJ'⟩ := exists_good_pt hL z
    have h₁ := congrArg ((trF φ ε r z (fun k => J (𝟙 X ≫ φ k)) (fun k => J' (r ≫ φ k))).val * ·) (H Z q r e z J' hJ')
    simp only [mul_zero, Finset.mul_sum] at h₁
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h₁
    rw [mul_left_comm]
    exact congrArg _ (sec_trans (σ i) r z hz (hJ'.mem φ r))

theorem expT_unit_iff : AllPre fun {_} _ _ _ {_} {_} {_} _ _ U => ∀ k σ σ' f f',
    U.ExpT (𝟙_ _) k σ f → U.ExpT (𝟙_ _) k σ' f' → (σ = σ' ↔ f = f') := by
  intro V _ _ _ hV D A G _ _ U
  have key : ∀ T, TA V V = T → ∀ k σ σ' f f', U.ExpT T k σ f → U.ExpT T k σ' f' → (σ = σ' ↔ f = f') := by
    rintro _ rfl
    refine GlobalTheory.expT_eq_iff V hV D A G U V ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    rw [Algebra.algebraMap_self, Ideal.map_id]
    exact hV.2.1
  exact key _ (congrArg Over.mk (Spec.map_id _))


set_option maxHeartbeats 400000 in
theorem main : (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) t t' s s', U.ExpF F k t s → U.ExpF F k t' s' → (t = t' ↔ s = s')) := by
  intro V _ _ _ hV D A G _ _ U F _ _ k t t' s s' ⟨n, c, σ, f, hE, hG, hB⟩ ⟨n', c', σ', f', hE', hG', hB'⟩
  classical
  let : Algebra V F := ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))).toAlgebra
  have : IsScalarTower V (FractionRing V) F := IsScalarTower.of_algebraMap_eq' rfl
  have hj : jFK (R := V) F ≫ jK V = Spec.map (CommRingCat.ofHom (algebraMap V F)) :=
    (Spec.map_comp _ _).symm
  obtain ⟨κ, _, b, a, hb, ha⟩ := exists_indep_coords V F (Fin.append c (-c'))
  have hEE : ∀ i, U.ExpT (𝟙_ _) k (Fin.append σ σ' i) (Fin.append f f' i) := fun i => by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.append_left] using hE i
    · simpa only [Fin.append_right] using hE' i
  choose τ g hτg hτ hg using fun l => ExpLin.expT_linear V _ D A G U (𝟙_ _) k _
    (fun i => (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom (a i l)) _ _ hEE
  obtain ⟨τ₀, g₀, h₀, hτ₀, hg₀⟩ := ExpLin.expT_linear V _ D A G U (𝟙_ _) k 0 Fin.elim0 Fin.elim0 Fin.elim0
    (fun i => i.elim0)
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at hτ₀ hg₀
  have := U.semi.smooth
  have := D.P.isAb.smooth
  let pG : (𝟙_ _ ⊗ G).left ⟶ Spec (CommRingCat.of V) := (fst (𝟙_ _) G).left
  let pB : (𝟙_ _ ⊗ D.P.A).left ⟶ Spec (CommRingCat.of V) := (fst (𝟙_ _) D.P.A).left
  have : Flat pG := inferInstanceAs (Flat (pullback.fst _ G.hom))
  have : Flat pB := inferInstanceAs (Flat (pullback.fst _ D.P.A.hom))
  have eG : (snd (𝟙_ _) G).left ≫ G.hom = pG :=
    (Over.w (snd (𝟙_ _) G)).trans ((Over.w (fst (𝟙_ _) G)).symm.trans (Category.comp_id _))
  have eB : (snd (𝟙_ _) D.P.A).left ≫ D.P.A.hom = pB :=
    (Over.w (snd (𝟙_ _) D.P.A)).trans ((Over.w (fst (𝟙_ _) D.P.A)).symm.trans (Category.comp_id _))
  have SG := split_iff pG U.P.L.isLB b hb a (Fin.append σ σ') τ τ₀ hτ hτ₀
  have SB := fun α => split_iff pB D.P.isLB b hb a (fun i => Fin.append f f' i α) (fun l => g l α) (g₀ α)
    (fun l => hg l α) (hg₀ α)
  simp only [← ha] at SG SB
  simp only [gs_scal] at hG hG' hB hB'
  have M : (∀ l, τ l = τ₀) ↔ ∀ α l, g l α = g₀ α := by
    rw [forall_comm]
    exact forall_congr' fun l => (expT_unit_iff V hV D A G U k _ _ _ _ (hτg l) h₀).trans funext_iff
  have NG : t = t' ↔ ∀ l, τ l = τ₀ := by
    rw [SG]
    constructor
    · rintro rfl Z q r e z J hJ
      let y : Z ⟶ pullback G.hom (jK V) := pullback.lift (r ≫ (snd (𝟙_ _) G).left) (q ≫ jFK (R := V) F)
        (by rw [Category.assoc, eG, e, Category.assoc, hj])
      let rA : Z ⟶ (TFK (R := V) F ⊗ A.A).left := pullback.lift q (y ≫ U.gen.hom.left)
        ((pullback.lift_snd _ _ _).symm.trans ((congrArg (y ≫ ·) (Over.w U.gen.hom).symm).trans
          (Category.assoc _ _ _).symm))
      have e₁ : rA ≫ (fst (TFK (R := V) F) A.A).left = q := pullback.lift_fst _ _ _
      obtain ⟨JA, hJA⟩ := exists_good_pt A.isLB z
      have h₁ := hG Z rA y r (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _).symm z JA J hJA hJ
      have h₂ := hG' Z rA y r (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _).symm z JA J hJA hJ
      refine (sum_append (germOf q z) c c' σ σ' (fun t => sval t r z J)).trans (sub_eq_zero.2 ?_)
      rw [← e₁]
      exact h₁.symm.trans h₂
    · intro H
      refine SecOps.sec_ext (sec_ext_val (φ := fun _ : Fin 1 => (snd (TFK (R := V) F) A.A).left)
        (ε := fun _ => (k : ℤ)) A.isLB fun z JA hJA => ?_)
      let y : (TFK (R := V) F ⊗ A.A).left ⟶ pullback G.hom (jK V) := (snd (TFK (R := V) F) A.A).left ≫ U.gen.inv.left
      let r : (TFK (R := V) F ⊗ A.A).left ⟶ (𝟙_ _ ⊗ G).left :=
        pullback.lift ((y ≫ pullback.fst G.hom (jK V)) ≫ G.hom) (y ≫ pullback.fst G.hom (jK V)) (Category.comp_id _)
      have e₁ : r ≫ (snd (𝟙_ _) G).left = y ≫ pullback.fst G.hom (jK V) := pullback.lift_snd _ _ _
      have e₂ : 𝟙 _ ≫ (snd (TFK (R := V) F) A.A).left = y ≫ U.gen.hom.left :=
        (Category.id_comp _).trans ((Category.comp_id _).symm.trans ((congrArg (_ ≫ ·)
          (congrArg CommaMorphism.left U.gen.inv_hom_id).symm).trans (Category.assoc _ _ _).symm))
      obtain ⟨J, hJ⟩ := exists_good_pt U.P.L.isLB z
      have h₁ := hG _ (𝟙 _) y r e₂ e₁ z JA J hJA hJ
      have h₂ := hG' _ (𝟙 _) y r e₂ e₁ z JA J hJA hJ
      have e₃ : y ≫ pullback.snd G.hom (jK V) = (𝟙 _ ≫ (fst (TFK (R := V) F) A.A).left) ≫ jFK (R := V) F :=
        (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w U.gen.inv)).trans
          ((Over.w (snd (TFK (R := V) F) A.A)).trans ((Over.w (fst (TFK (R := V) F) A.A)).symm.trans
            (congrArg (· ≫ _) (Category.id_comp _).symm))))
      have h₃ := H _ (𝟙 _ ≫ (fst (TFK (R := V) F) A.A).left) r (by
        rw [← eG, ← Category.assoc, e₁, Category.assoc, pullback.condition, ← Category.assoc, e₃, ← hj]
        exact Category.assoc _ _ _) z J hJ
      have h₄ := sub_eq_zero.1 ((sum_append (germOf (B := CommRingCat.of F) (𝟙 _ ≫ (fst (TFK (R := V) F) A.A).left) z)
        c c' σ σ' (fun t => sval t r z J)).symm.trans h₃)
      exact (IsUnit.mul_right_inj ((Units.isUnit _).pow k)).1 (h₁.trans (h₄.trans h₂.symm))
  have NB : s = s' ↔ ∀ α l, g l α = g₀ α := by
    rw [funext_iff]
    refine forall_congr' fun α => ?_
    rw [SB α]
    constructor
    · intro h Z q r e z J hJ
      let rF : Z ⟶ (DegPre.BF D F).left := pullback.lift q (r ≫ (snd (𝟙_ _) D.P.A).left)
        (by rw [Category.assoc, eB, e, ← hj]; rfl)
      have e₁ : rF ≫ (fst (TF (R := V) F) D.P.A).left = q := pullback.lift_fst _ _ _
      have h₁ := hB α Z rF r (pullback.lift_snd _ _ _).symm z J hJ
      have h₂ := hB' α Z rF r (pullback.lift_snd _ _ _).symm z J hJ
      refine (sum_append (germOf q z) c c' f f' (fun t => sval (t α) r z J)).trans (sub_eq_zero.2 ?_)
      rw [← e₁]
      exact h₁.symm.trans ((congrArg (fun u => sval u rF z J) h).trans h₂)
    · intro H
      refine SecOps.sec_ext (sec_ext_val D.P.isLB fun z J hJ => ?_)
      let r : (DegPre.BF D F).left ⟶ (𝟙_ _ ⊗ D.P.A).left :=
        pullback.lift ((DegPre.prB D F).left ≫ D.P.A.hom) (DegPre.prB D F).left (Category.comp_id _)
      have e₁ : r ≫ (snd (𝟙_ _) D.P.A).left = 𝟙 _ ≫ (DegPre.prB D F).left :=
        (pullback.lift_snd _ _ _).trans (Category.id_comp _).symm
      have h₃ := H _ (𝟙 _ ≫ (fst (TF (R := V) F) D.P.A).left) r (by
        rw [← eB, ← Category.assoc, e₁, Category.assoc, Category.assoc, Over.w, ← hj]
        exact congrArg _ (Over.w (fst (TF (R := V) F) D.P.A)).symm) z J hJ
      have h₄ := sub_eq_zero.1 ((sum_append (germOf (B := CommRingCat.of F) (𝟙 _ ≫ (fst (TF (R := V) F) D.P.A).left) z)
        c c' f f' (fun t => sval (t α) r z J)).symm.trans h₃)
      exact (hB α _ (𝟙 _) r e₁ z J hJ).trans (h₄.trans (hB' α _ (𝟙 _) r e₁ z J hJ).symm)
  exact NG.trans (M.trans NB.symm)

end GlobalTheory.UU.ExpFUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FourierJacobiExpansionOverFieldInjectiveStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiExpansion_overField_injective : (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) t t' s s', U.ExpF F k t s → U.ExpF F k t' s' → (t = t' ↔ s = s')) := by
  first | exact @GlobalTheory.UU.ExpFUniq.main | exact GlobalTheory.UU.ExpFUniq.main | (intros; apply GlobalTheory.UU.ExpFUniq.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourierJacobiExpansionOverField
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourierJacobiExpansionOverField
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.ExpTotal
open GlobalTheory.TwistLoc (gc gc_mul)

section General
variable {X X' W Y Z : Scheme.{0}}

theorem gs_scal {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (a : R) :
    gs r z ⊤ (scal p a) = gc (r ≫ p) z a := gs_pull r p z ⊤ trivial _

theorem gc_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (q : Z ⟶ Spec (CommRingCat.of S)) (z : Z) (a : R) :
    gc (q ≫ Spec.map (CommRingCat.ofHom f)) z a = gc q z (f a) := by
  refine (gs_pull q _ z ⊤ trivial _).symm.trans (congrArg (gs q z ⊤) ?_)
  exact (congrArg (fun g => g.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem exists_comb {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ} (c : Fin n → Γ(Y, ⊤))
    (t : Fin n → LB.Sec (LB.LinComb L φ ε)) : ∃ s : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval s r z J = ∑ i, gs r z ⊤ (c i) * sval (t i) r z J :=
  ⟨⟨fun j => ∑ i, (IndivisibleSection.smulSec (c i) (t i)).f j, fun i j => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (IndivisibleSection.smulSec (c l) (t l)).compat i j⟩,
    fun Z r z J hJ => DVR.SectionScalarValuation.sval_lin c t (fun _ => rfl) r z hJ⟩

theorem exists_inv {L : LB X} {L' : LB X'} {F : W ⟶ X} {F' : W ⟶ X'}
    (w : LB.Iso (L'.pull F') (L.pull F)) (hw : w.IsGen) : ∃ v : LB.Iso (L.pull F) (L'.pull F'), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ W) (z : Z) (i : L.ι) (j : L'.ι), F (r z) ∈ L.U i → F' (r z) ∈ L'.U j →
        gw v r z j (fun _ => i) = (gw w r z i (fun _ => j))⁻¹ := by
  let v : LB.Iso (L.pull F) (L'.pull F') := ⟨fun p => (res (le_inf inf_le_right inf_le_left :
    (L'.pull F').U p.1 ⊓ (L.pull F).U p.2 ≤ (L.pull F).U p.2 ⊓ (L'.pull F').U p.1) (w.s (p.2, p.1)))⁻¹⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ W) (z : Z) (i : L.ι) (j : L'.ι), F (r z) ∈ L.U i → F' (r z) ∈ L'.U j →
      gw v r z j (fun _ => i) = (gw w r z i (fun _ => j))⁻¹ := fun Z r z i j hi hj =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _
      (show r z ∈ (L'.pull F').U (fun _ => j) ⊓ (L.pull F).U (fun _ => i) from ⟨mem_pull.2 hj, mem_pull.2 hi⟩) _))
  refine ⟨v, (isGen_iff v).2 fun Z r z j j' i i' hj hj' hi hi' => ?_, hv⟩
  have e := (isGen_iff w).1 hw Z r z (i PUnit.unit) (i' PUnit.unit) (fun _ => j) (fun _ => j') (mem_pull.1 hi)
    (mem_pull.1 hi') (mem_pull.2 hj) (mem_pull.2 hj')
  rw [gm_pull_g L' F' r z (fun _ => j) (fun _ => j') (mem_pull.2 hj) (mem_pull.2 hj')] at e
  refine (hv Z r z (i PUnit.unit) j (mem_pull.1 hi) hj).trans ?_
  rw [e, gm_pull_g L F r z i i' hi hi']
  refine Eq.trans ?_ (congrArg _ (hv Z r z (i' PUnit.unit) j' (mem_pull.1 hi') hj')).symm
  rw [mul_inv, mul_inv, inv_inv, mul_comm _⁻¹]

end General

theorem exists_span (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ)
    (hn : 1 ≤ n) (F : Type) [Field F] (q : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K))
    (s : LB.Sec (LB.LinComb P.L (fun _ : Fin 1 => (snd (Over.mk q) P.A).left) (fun _ => (n : ℤ)))) :
    ∃ (m : ℕ) (c : Fin m → F) (a : Fin m → LB.Sec (LB.LinComb P.L (fun _ : Fin 1 => 𝟙 P.A.left) (fun _ => (n : ℤ)))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk q ⊗ P.A).left) (z : Z) (J), Good P.L z J →
        sval s r z J = ∑ i, gc (R := F) (r ≫ (fst (Over.mk q) P.A).left) z (c i) *
          sval (a i) (r ≫ (snd (Over.mk q) P.A).left) z J := by
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of K)) P n hn (IsLocalRing.closedPoint K)
  obtain rfl : U = ⊤ := DVR.eq_top_of_closedPoint_mem U hU
  have hi : (Spec (CommRingCat.of K)).topIso.inv ≫
      (overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤).hom = 𝟙 _ :=
    (congrArg (_ ≫ ·) (Category.comp_id _)).trans (Spec (CommRingCat.of K)).topIso.inv_hom_id
  have hi' : (overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤).hom ≫ (Spec (CommRingCat.of K)).topIso.inv
      = 𝟙 _ :=
    (congrArg (· ≫ _) (Category.comp_id _)).trans (Spec (CommRingCat.of K)).topIso.hom_inv_id
  obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of F) ⟶ (overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤).left,
      t ≫ (overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤).hom = q :=
    ⟨q ≫ (Spec (CommRingCat.of K)).topIso.inv, (Category.assoc _ _ _).trans
      ((congrArg (q ≫ ·) hi).trans (Category.comp_id q))⟩
  let T₀ := overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤
  let e : P.A ⟶ T₀ ⊗ P.A := lift (Over.homMk (P.A.hom ≫ (Spec (CommRingCat.of K)).topIso.inv)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hi).trans (Category.comp_id _)))) (𝟙 _)
  have he : snd (baseAt t) P.A ≫ e = homAt t ▷ P.A := by
    refine CartesianMonoidalCategory.hom_ext _ _ (Over.OverMorphism.ext ?_) ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (lift_snd _ _)).trans
      ((Category.comp_id _).trans (whiskerRight_snd (homAt t) P.A).symm)))
    have : IsIso T₀.hom := ⟨_, hi', hi⟩
    rw [← cancel_mono T₀.hom, Over.w, Over.w]
  choose a ha using fun i => PullSec.exists_pullSec P.isLB (φ' := fun _ : Fin 1 => 𝟙 P.A.left) e.left
    (fun _ => (congrArg CommaMorphism.left (lift_snd _ _ : e ≫ snd _ _ = _)).symm) (b i)
  choose b' hb' using fun i => IndivisibleSection.exists_pull_chart (K := Fin 1) (b i) (homAt t ▷ P.A).left
      (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))
  have hsp := (hb F t b' fun i j => hb' i j _).2
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
  choose c hc using fun i => (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 (d i)
  refine ⟨_, c, a, fun Z r z J hJ => ?_⟩
  refine (DVR.SectionScalarValuation.sval_lin (s := s) (fun i => scal (R := F) (fst (baseAt t) P.A).left (c i)) b' (fun j => ?_) r z hJ).trans
    (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (gs_scal _ r z _) ?_)
  · refine (congrFun (congrArg Subtype.val hd) j).symm.trans ?_
    refine (congrFun (Submodule.coe_sum _ _ _) j).trans ((Finset.sum_apply _ _ _).trans
      (Finset.sum_congr rfl fun i _ => ?_))
    rw [← hc i]
    rfl
  · have e₁ : (r ≫ (snd (baseAt t) P.A).left) ≫ e.left = r ≫ (homAt t ▷ P.A).left :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (congrArg CommaMorphism.left he))
    have e₂ : (r ≫ (homAt t ▷ P.A).left) ≫ (snd T₀ P.A).left = r ≫ (snd (baseAt t) P.A).left :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A)))
    refine Eq.trans ?_ (ha i Z _ z J hJ).symm
    rw [e₁, sval_of (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (b i) _ z J
      (fun _ => J (r ≫ (snd (baseAt t) P.A).left)) (fun _ => congrArg J e₂)]
    have hm := hJ.mem (fun _ : Fin 1 => (snd (baseAt t) P.A).left) r
    have le := chart_le_res P.A P.L (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) n
      (fun _ => J (r ≫ (snd (baseAt t) P.A).left))
    exact (congrArg (gs r z _) (hb' i _ le)).trans ((gs_res r z le hm _).trans (gs_pull r (homAt t ▷ P.A).left z _ (le hm) _))

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_integral (U : PreU I D A G) (k : ℕ)
    (a : LB.Sec (LB.LinComb A.L (fun _ : Fin 1 => 𝟙 A.A.left) (fun _ => (k : ℤ)))) :
    ∃ t : R, t ≠ 0 ∧ ∃ σ : U.SecGT (𝟙_ _) k, ∀ (Z : Scheme.{0}) (y : Z ⟶ ((Over.pullback (jK R)).obj G).left)
      (rG : Z ⟶ (𝟙_ _ ⊗ G).left), rG ≫ (snd _ G).left = y ≫ pullback.fst G.hom (jK R) →
      ∀ (z : Z) (JA) (JG), Good A.L z JA → Good U.P.L.L z JG →
        sval σ rG z JG = gc (y ≫ pullback.fst G.hom (jK R) ≫ G.hom) z t *
          ((gw U.wA y z (JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => JA (y ≫ U.gen.hom.left))).val ^ k *
            sval a (y ≫ U.gen.hom.left) z JA) := by
  have := U.semi.quasiCompact
  have := U.semi.separated
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  obtain ⟨v, hv, hvw⟩ := exists_inv U.wA U.wA_gen
  obtain ⟨s', hs'⟩ := PullSec.exists_sec_of_iso A.isLB U.P.L.isLB v hv (𝟙 _) U.gen.hom.left
    (pullback.fst G.hom (jK R) ≫ 𝟙 G.left) (𝟙 A.A.left) ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm) k a
  obtain ⟨t, ht, σ₀, hσ₀⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors R)
    (IsPullback.of_hasPullback G.hom (jK R)) U.P.L.isLB (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) s'
  obtain ⟨σ, hσ⟩ := PullSec.exists_pullSec U.P.L.isLB (φ' := fun _ : Fin 1 => (snd (𝟙_ _) G).left)
    (snd (𝟙_ _) G).left (fun _ => (Category.comp_id _).symm) σ₀
  refine ⟨t, nonZeroDivisors.ne_zero ht, σ, fun Z y rG e z JA JG hA hG => (hσ Z rG z JG hG).trans ?_⟩
  have mA := hA (y ≫ U.gen.hom.left)
  have mG := hG (y ≫ pullback.fst G.hom (jK R))
  rw [e, sval_of σ₀ _ z JG (fun _ => JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => congrArg JG (Category.comp_id _)),
    sval_of a _ z JA (fun _ => JA (y ≫ U.gen.hom.left)) (fun _ => congrArg JA (Category.comp_id _))]
  refine (hσ₀ Z y z _ (Set.mem_iInter.2 fun _ => mG)).trans (congrArg _ ?_)
  have h := hs' Z y z _ _ mA mG
  rw [Category.comp_id y, hvw Z y z _ _ mG mA] at h
  refine Eq.trans ?_ (congrArg _ h)
  rw [← _root_.mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow, _root_.one_mul]

theorem exists_pullB (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (α : D.X)
    (f : SecBT D (𝟙_ _) k α) : ∃ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (rF : Z ⟶ (DegPre.BF D F).left) (rB : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
        rB ≫ (snd _ D.P.A).left = rF ≫ (DegPre.prB D F).left → ∀ (z : Z) (J), Good D.P.L z J →
          sval s rF z J = sval f rB z J := by
  let φ := toUnit (TF (R := R) F)
  have a₀ : snd (TF (R := R) F) D.P.A = φ ▷ D.P.A ≫ snd (𝟙_ _) D.P.A := (whiskerRight_snd _ _).symm
  have hc : ∀ i : Fin 4, DegPre.famφ D F α i = (φ ▷ D.P.A).left ≫ famφT D (𝟙_ _) α i := fun i => by
    have u : φ ▷ D.P.A ≫ toUnit (𝟙_ _ ⊗ D.P.A) = toUnit _ := toUnit_unique _ _
    have a₂ : ∀ c : 𝟙_ _ ⟶ D.P.A, toUnit (DegPre.BF D F) ≫ c = φ ▷ D.P.A ≫ toUnit (𝟙_ _ ⊗ D.P.A) ≫ c := fun c => by
      rw [← Category.assoc, u]
    fin_cases i
    · exact congrArg (fun q => q.left) a₀
    · exact congrArg (fun q => q.left) ((congrArg₂ (· * ·) a₀ (a₂ (D.c α))).trans (MonObj.comp_mul _ _ _).symm)
    · exact congrArg (fun q => q.left) (a₂ (D.c α))
    · exact congrArg (fun q => q.left) (a₂ η[D.P.A])
  obtain ⟨s, hs⟩ := PullSec.exists_pullSec D.P.isLB (φ ▷ D.P.A).left hc f
  refine ⟨s, fun Z rF rB e z J hJ => (hs Z rF z J hJ).trans (congrArg (sval f · z J) ?_)⟩
  have : IsIso (snd (𝟙_ _) D.P.A) := by rw [← leftUnitor_hom]; infer_instance
  have : IsIso (snd (𝟙_ _) D.P.A).left := inferInstanceAs (IsIso ((Over.forget _).map (snd (𝟙_ _) D.P.A)))
  rw [← cancel_mono (snd (𝟙_ _) D.P.A).left, e]
  exact (Category.assoc _ _ _).trans (congrArg (rF ≫ ·) (congrArg CommaMorphism.left a₀).symm)

theorem exists_expF (hS : SecBaseChangeSt) (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (k : ℕ) (hk : 1 ≤ k) (hb : ∀ σ, ∃ f, U.ExpT (𝟙_ _) k σ f)
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) : ∃ s, U.ExpF F k t s := by
  obtain ⟨n, c, a, ha⟩ := exists_span hS A k hk F (jFK (R := R) F) t
  choose d hd σ hσ using fun i => exists_integral U k (a i)
  choose f hf using fun i => hb (σ i)
  choose g hg using fun i α => exists_pullB D F k α (f i α)
  let ψ : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have hψ : ∀ i, ψ (d i) ≠ 0 := fun i => (map_ne_zero (algebraMap (FractionRing R) F)).2
    ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hd i))
  choose s hs using fun α => exists_comb
    (fun i => scal (R := F) (fst (TF (R := R) F) D.P.A).left (c i * (ψ (d i))⁻¹)) (fun i => g i α)
  refine ⟨s, n, fun i => c i * (ψ (d i))⁻¹, σ, f, hf, fun Z rA y rG e₁ e₂ z JA JG hA hG => ?_,
    fun α Z rF rB e z J hJ => (hs α Z rF z J hJ).trans
      (Finset.sum_congr rfl fun i _ => congrArg _ (hg i α Z rF rB e z J hJ))⟩
  refine (congrArg _ (ha Z rA z JA hA)).trans ((Finset.mul_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => ?_))
  have e₃ : y ≫ pullback.fst G.hom (jK R) ≫ G.hom =
      ((rA ≫ (fst (TFK (R := R) F) A.A).left) ≫ jFK (R := R) F) ≫ jK R := by
    have w₁ : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
    have w₂ : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (snd (TFK (R := R) F) A.A).left ≫ A.A.hom :=
      (Over.w (fst (TFK (R := R) F) A.A)).trans (Over.w (snd (TFK (R := R) F) A.A)).symm
    refine (congrArg (y ≫ ·) pullback.condition).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) ?_))
    exact (congrArg (y ≫ ·) w₁.symm).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ A.A.hom) e₁.symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (rA ≫ ·) w₂.symm).trans (Category.assoc _ _ _).symm))))
  have e₄ : gc (y ≫ pullback.fst G.hom (jK R) ≫ G.hom) z (d i) =
      gc (R := F) (rA ≫ (fst (TFK (R := R) F) A.A).left) z (ψ (d i)) :=
    (congrArg (gc · z (d i)) e₃).trans ((gc_map _ _ z _).trans (gc_map _ _ z _))
  refine Eq.trans ?_ (congrArg₂ (· * ·) (gs_scal (R := F) _ rA z _) (hσ i Z y rG e₂ z JA JG hA hG)).symm
  rw [e₄, ← _root_.mul_assoc (gc _ _ _) (gc _ _ _), ← gc_mul, inv_mul_cancel_right₀ (hψ i)]
  exact (mul_left_comm _ _ _).trans (congrArg (fun q => _ * (_ * sval (a i) q z JA)) e₁)

theorem expF_total : Laws → Laws2 → (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ t, ∃ s, U.ExpF F k t s) :=
  fun h h₂ V _ _ _ hV D A G _ _ U F _ _ k hk t =>
    exists_expF h.secBaseChange U F k hk (GlobalTheory.T.exists_expansion_section_lineBundle_power h h₂ V hV D A G U k hk) t

end GlobalTheory.UU.ExpTotal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourierJacobiExpansionOverFieldStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fourierJacobi_expansion_over_field : Laws → Laws2 → (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ t, ∃ s, U.ExpF F k t s) := by
  first | exact @GlobalTheory.UU.ExpTotal.expF_total | exact GlobalTheory.UU.ExpTotal.expF_total | (intros; apply GlobalTheory.UU.ExpTotal.expF_total <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothOfRelativeDimensionOfGeneric
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericDim

theorem smoothOfRelativeDimension_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (g : ℕ), SmoothOfRelativeDimension g (pullback.snd G.hom (jK R)) → SmoothOfRelativeDimension g G.hom := by
  intro R _ _ G _ _ _ g hg
  have hdense := (ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK (V := R)).denseRange
  have hloc : ∀ x : G.left, ∃ W : G.left.Opens, x ∈ W ∧
      SmoothOfRelativeDimension g (W.ι ≫ G.hom) := by
    intro x
    obtain ⟨n, W, hxW, hW⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom x
    refine ⟨W, hxW, ?_⟩
    have hopen : IsOpen (G.hom '' (W : Set G.left)) := G.hom.isOpenMap _ W.isOpen
    obtain ⟨y, w, hwW, hwy⟩ := hdense.exists_mem_open hopen ⟨G.hom x, x, hxW, rfl⟩
    obtain ⟨z, hz, -⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := jK R) w y hwy
    have hzW : pullback.fst G.hom (jK R) z ∈ W := by rw [hz]; exact hwW
    have hng : n = g :=
      ReciprocityTheory.ChartRestriction.G.H1.dim_base (IsPullback.of_hasPullback G.hom (jK R)) hW hg z hzW
    exact hng ▸ hW
  have i1 : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension g)
  choose W hxW hW using hloc
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩) hW

end GlobalTheory.GenericDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.TowerEx

section Levels
variable {V : Type} [CommRing V] [IsLocalRing V] (e : ℕ)

instance nontrivial_level : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) :=
  Ideal.Quotient.nontrivial_iff.2 fun h => (IsLocalRing.maximalIdeal.isMaximal V).ne_top
    (top_le_iff.1 (h.ge.trans (Ideal.pow_le_self (Nat.succ_ne_zero e))))

instance isLocalRing_level : IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem isNilpotent_max : IsNilpotent (IsLocalRing.maximalIdeal (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1))) := by
  refine ⟨e + 1, ?_⟩
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (e + 1)))
    Ideal.Quotient.mk_surjective, ← Ideal.map_pow, Ideal.map_quotient_self, Ideal.zero_eq_bot]

end Levels

theorem thickMap_w {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ (thickObj R I (e + 1) G).hom = (thickObj R I e G).hom ≫ thickTrans R I e :=
  pullback.lift_snd _ _ _

theorem isGrpPullback_thickMap {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] : IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (thickTrans_comp R I e).symm
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm) (pullback.lift_snd _ _ _)

theorem exists_isCPMap_thickMap {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {P : CP G} {P₀ : CP (thickObj R I e G)}
    {P₁ : CP (thickObj R I (e + 1) G)} (h₀ : IsLevelCP I e P₀ P) (h₁ : IsLevelCP I (e + 1) P₁ P) :
    ∃ w, IsCPMap P₀ P₁ (thickTrans R I e) (thickMap R I e G) (thickMap_w I e G) w := by
  obtain ⟨_, h₀⟩ := h₀
  obtain ⟨_, h₁⟩ := h₁
  exact exists_cancel h₁ h₀ (isGrpPullback_thickMap I e G) (thickTrans_comp R I e)
    ((pullback.lift_fst _ _ _).trans (Category.comp_id _))

theorem exists_levelMap {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {G : Over (Spec (CommRingCat.of V))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) {P : CP G} {X : Type} [AddCommGroup X] [Module.Free ℤ X] {e : ℕ}
    (l : Lev (IsLocalRing.maximalIdeal V) P X e) (l' : Lev (IsLocalRing.maximalIdeal V) P X (e + 1))
    (h : TorusCompat (thickTrans V _ e) (thickMap V _ e G) l.Q.i l'.Q.i) :
    ∃ β : l.Q.B.left ⟶ l'.Q.B.left, IsCPPullback l.D.M l'.D.M (thickTrans V _ e) β ∧
      l.Q.q.left ≫ β = thickMap V _ e G ≫ l'.Q.q.left := by
  have := hG.smooth
  have := hG.geomConnected
  have : Smooth (thickObj V (IsLocalRing.maximalIdeal V) e G).hom := by
    show Smooth (pullback.snd _ _); infer_instance
  have : GeometricallyConnected (thickObj V (IsLocalRing.maximalIdeal V) e G).hom := by
    show GeometricallyConnected (pullback.snd _ _); infer_instance
  have : ConnectedSpace (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)))) :=
    SplitTorus.connectedSpace_of_isLocalRing _
  have := (GroupConn.connectedSpace_group _ (thickObj V (IsLocalRing.maximalIdeal V) e G)).1
  obtain ⟨_, hP⟩ := exists_isCPMap_thickMap l.lev l'.lev
  exact exists_transition (isGrpPullback_thickMap _ e G) hP h l'.D l.D

theorem nonempty_tower : (AllSet fun s => Nonempty (Tower s)) := by
  intro V _ _ _ A G _ _ s
  have := s.semi.smooth
  have := s.semi.geomConnected
  have hs : ∀ e, Smooth (thickObj V (IsLocalRing.maximalIdeal V) e G).hom := fun e => by
    show Smooth (pullback.snd _ _); infer_instance
  have hc : ∀ e, GeometricallyConnected (thickObj V (IsLocalRing.maximalIdeal V) e G).hom := fun e => by
    show GeometricallyConnected (pullback.snd _ _); infer_instance
  let L : ℕ → Type 1 := fun e => {l : Lev (IsLocalRing.maximalIdeal V) s.P s.X e // ∃ σ : CubTriv l.Pe.c l.Q.i, σ.Even}
  have step : ∀ (e : ℕ) (l : L e), ∃ l' : L (e + 1),
      TorusCompat (thickTrans V _ e) (thickMap V _ e G) l.1.Q.i l'.1.Q.i := fun e l => by
    obtain ⟨P₁, h₁⟩ := exists_isLevelCP (IsLocalRing.maximalIdeal V) (e + 1) s.P
    obtain ⟨_, hP⟩ := exists_isCPMap_thickMap l.1.lev h₁
    obtain ⟨Q, hQ, hσ⟩ := exists_lift (isNilpotent_max (e + 1)) _ (Ideal.Quotient.factor_surjective _) _ _
      (isGrpPullback_thickMap _ e G) hP l.1.Q l.2
    obtain ⟨D⟩ := nonempty_desc _ (isNilpotent_max (e + 1)) _ P₁ Q hσ
    exact ⟨⟨⟨Q, P₁, h₁, D⟩, hσ⟩, hQ⟩
  choose nxt hnxt using step
  obtain ⟨D₀⟩ := nonempty_desc _ (isNilpotent_max 0) _ s.P₀ s.Q₀ s.even₀
  let l : ∀ e, L e := fun e => Nat.rec (motive := L) ⟨⟨s.Q₀, s.P₀, s.lev₀, D₀⟩, s.even₀⟩ nxt e
  have tor : ∀ e, TorusCompat (thickTrans V _ e) (thickMap V _ e G) (l e).1.Q.i (l (e + 1)).1.Q.i :=
    fun e => hnxt e (l e)
  choose β hβ hq using fun e => exists_levelMap s.semi (l e).1 (l (e + 1)).1 (tor e)
  exact ⟨⟨fun e => (l e).1, tor, β, hβ, hq⟩⟩

end GlobalTheory.UU.TowerEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTowerStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_mumfordTorusQuotientTower : (AllSet fun s => Nonempty (Tower s)) := by
  first | exact @GlobalTheory.UU.TowerEx.nonempty_tower | exact GlobalTheory.UU.TowerEx.nonempty_tower | (intros; apply GlobalTheory.UU.TowerEx.nonempty_tower <;> assumption)
end
end
