module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenericFibreIsoOfCompatibleThickenings
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumDHomDegenerationValuesFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumDHomDegenerationValuesFieldExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.GaugeHom
open GlobalTheory.TorusExt GlobalTheory.ArcExt

section Val
variable {F : Type} [Field F] {X : Scheme.{0}} {L : LB X}
  {J J' : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (hJ' : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J' ψ))
include hJ hJ'

theorem exists_trans : ∃ T : (Sp F ⟶ X) → Fˣ, ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y), sF s r J = (∏ k, T (r ≫ φ k) ^ ε k : Fˣ) * sF s r J' := by
  let y : Sp F := IsLocalRing.closedPoint F
  have hm : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ (L.U (J ψ) ⊓ L.U (J' ψ)) := fun ψ z hz => ⟨hJ ψ hz, hJ' ψ hz⟩
  have hv : ∀ ψ : Sp F ⟶ X, (gm ψ y (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ))).val =
      stalkConst y (valF ψ (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ)).val) := fun ψ =>
    (gs_unit ψ y _ (hm ψ trivial) _).symm.trans (gs_eq_stalkConst ψ y (hm ψ) _)
  have hne : ∀ ψ : Sp F ⟶ X, valF ψ (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ)).val ≠ 0 := fun ψ h =>
    (((Units.isUnit _).map _).map _).ne_zero ((dif_pos (hm ψ)).symm.trans h)
  refine ⟨fun ψ => Units.mk0 _ (hne ψ), fun Y K _ φ ε s r => (stalkConst y).injective ?_⟩
  have e : ∀ ψ : Sp F ⟶ X, gm ψ y (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ)) =
      Units.map (stalkConst y).toMonoidHom (Units.mk0 _ (hne ψ)) := fun ψ => Units.ext (hv ψ)
  have a := sec_trans s r y (top_le_chart hJ φ r trivial) (top_le_chart hJ' φ r trivial)
  rw [map_mul]
  refine (gs_eq_stalkConst r y (top_le_chart hJ φ r) _).symm.trans
    (a.trans (congrArg₂ (· * ·) ?_ (gs_eq_stalkConst r y (top_le_chart hJ' φ r) _)))
  show _ = (Units.map (stalkConst y).toMonoidHom _).val
  rw [map_prod, trF]
  refine congrArg Units.val (Finset.prod_congr rfl fun k _ => ?_)
  rw [map_zpow, e]

end Val

theorem exists_trans_ext {F F' : Type} [Field F] [Field F'] (f : F →+* F') {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {J : (Sp F ⟶ X) → L.ι} {J' : (Sp F' ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
    (hJ' : ∀ ψ : Sp F' ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J' ψ)) : ∃ T : (Sp F ⟶ X) → F'ˣ,
    (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
      (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y),
      sF s (spMap f ≫ r) J' = (∏ k, T (r ≫ φ k) ^ ε k : F'ˣ) * f (sF s r J)) ∧
    ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen → ∀ r : Sp F ⟶ Y,
      vF t (spMap f ≫ r) J' = (∏ k, T (r ≫ φ k) ^ ε k : F'ˣ) * f (vF t r J) := by
  obtain ⟨J₀, h₀, e₀⟩ := exists_gauge f hL hJ
  obtain ⟨T, hT⟩ := exists_trans hJ' h₀
  have k : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
      (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y),
      sF s (spMap f ≫ r) J' = (∏ k, T (spMap f ≫ r ≫ φ k) ^ ε k : F'ˣ) * f (sF s r J) := fun Y K _ φ ε s r => by
    rw [hT, sF_ext f hJ e₀]
    simp only [Category.assoc]
  exact ⟨fun ψ => T (spMap f ≫ ψ), k, fun Y K _ φ ε t ht r => k Y K φ ε (genSec t ht) r⟩

theorem exists_hom (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F]
    [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') (N : NumD F) (N' : NumD F')
    (ν : NumOf D F N) (ν' : NumOf D F' N') (hth : ν'.th = ν.th) :
    ∃ I : NumD.Hom f N N', I.lam = 1 ∧ (∀ y, ν'.eX (I.e y) = ν.eX y) ∧
      ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D F' k) (q : N.QT k) (q' : N'.QT k), QkExt f p p' → ν.QPt p q →
        ν'.QPt p' q' → q'.1.1.toAdd = I.e q.1.1.toAdd ∧ I.Rel q.1.2 q'.1.2 := by
  obtain ⟨T, hs, hg⟩ := exists_trans_ext f D.P.isLB ν.good ν'.good
  have hr : rigVal ν' = T (1 : TF (R := R) F ⟶ D.P.A).left * f (rigVal ν) := by
    have := hg _ _ (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.rig_gen (TF (R := R) F).hom
    rw [Fintype.prod_unique, zpow_one] at this
    refine Eq.trans ?_ this
    exact congrArg (fun r => vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig r ν'.J)
      (Over.w (extMap (R := R) f hf)).symm
  have h0 : rigVal ν ≠ 0 := vF_ne_zero ν.good _ _
  let I : NumD.Hom f N N' :=
    { φ := ptHom f hf ν ν'
      h := fun x => T (ν.eA x).left / T (1 : TF (R := R) F ⟶ D.P.A).left
      h_one := by rw [map_one, div_self']
      θ_eq := fun x y u => by
        have e : N'.θ (ptHom f hf ν ν' x) (ptHom f hf ν ν' y) (ptHom f hf ν ν' u) =
            (∏ I : thK, T ((lift (ν.eA x) (lift (ν.eA y) (ν.eA u))).left ≫ thφ D.P.A (x3 D.P.A) I) ^ thε I) *
              Units.map f.toMonoidHom (N.θ x y u) := by
          refine Units.ext ?_
          show _ = _ * f (N.θ x y u : F)
          rw [ν'.θ_eq, ν.θ_eq, eA_ptHom, eA_ptHom, eA_ptHom, ← comp_lift, ← comp_lift]
          exact hg _ _ _ _ _ D.cub.isGen _
        rw [e, prod_cub]
        simp only [map_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel
      σ_eq := fun x => by
        have e : N'.σ (ptHom f hf ν ν' x) = (T (ν.eA x)⁻¹.left * (T (ν.eA x).left)⁻¹) *
            Units.map f.toMonoidHom (N.σ x) := by
          refine Units.ext ?_
          show _ = _ * f (N.σ x : F)
          rw [ν'.σ_eq, ν.σ_eq, eA_ptHom]
          refine (hg _ _ _ _ _ D.sym_gen _).trans (congrArg (fun z : F'ˣ => z.val * _) ?_)
          rw [Fin.prod_univ_two]
          show T ((ν.eA x)⁻¹).left ^ (1 : ℤ) * T ((ν.eA x).left ≫ 𝟙 _) ^ (-1 : ℤ) = _
          rw [Category.comp_id, zpow_one, zpow_neg, zpow_one]
        rw [e, map_inv]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel
      lam := 1
      th_eq := fun x => by
        have a : N'.th (ptHom f hf ν ν' x) * rigVal ν' = _ := ν'.th_eq _
        have b : N.th x * rigVal ν = _ := ν.th_eq _
        have c := hs _ _ _ _ ν.th (ν.eA x).left
        rw [Fintype.prod_unique, Category.comp_id, ← b, zpow_natCast, pow_one, map_mul] at c
        rw [eA_ptHom, hth, hr] at a
        have d := a.trans c
        have h1 : f (rigVal ν) ≠ 0 := (map_ne_zero f).2 h0
        rw [← _root_.mul_assoc, ← _root_.mul_assoc] at d
        have d' := mul_right_cancel₀ h1 d
        rw [_root_.one_mul, Units.val_div_eq_div_val, div_mul_eq_mul_div, ← d', mul_div_cancel_right₀ _ (Units.ne_zero _)]
      e := ν.eX.trans ν'.eX.symm
      c_eq := fun χ => ν'.eA.injective (by
        rw [ν'.c_eq, eA_ptHom, ν.c_eq, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
        exact (DVR.comp_cP D (extMap f hf) _).symm)
      ψ_eq := fun χ => by
        have e : N'.ψ (ν.eX.trans ν'.eX.symm χ) = ((T (ν.eA (N.c χ)).left)⁻¹ * T (1 : TF (R := R) F ⟶ D.P.A).left) *
            Units.map f.toMonoidHom (N.ψ χ) := by
          refine Units.ext ?_
          show _ = ((T (ν.eA (N.c χ)).left)⁻¹).val * (T (1 : TF (R := R) F ⟶ D.P.A).left).val * f (N.ψ χ : F)
          rw [ν'.ψ_eq, ν.ψ_eq, map_mul, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, _root_.mul_mul_mul_comm]
          refine congrArg₂ (· * ·) ?_ hr
          have c := hg _ _ _ _ _ (D.psi_gen (ν.eX χ)) (jFK (R := R) F)
          rw [Fintype.prod_unique, zpow_neg, zpow_one] at c
          refine (congrArg (fun r => vF (D.psi (ν.eX χ)) r ν'.J)
            ((extMap_jFK f hf).trans (Category.id_comp _)).symm).trans (c.trans ?_)
          refine congrArg (fun z => ((T z)⁻¹).val * _) ?_
          rw [ν.c_eq]
          exact congrArg (fun z => z.left) (DVR.comp_cP D
            (Over.homMk (jFK (R := R) F) rfl : TF (R := R) F ⟶ TK R) _)
        rw [e]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel }
  have hX : ∀ y, ν'.eX (I.e y) = ν.eX y := fun y => ν'.eX.apply_symm_apply _
  refine ⟨I, rfl, hX, fun k p p' q q' h hq hq' => ⟨ν'.eX.injective (hq'.1.trans (h.1.trans (hq.1.symm.trans (hX _).symm))),
    ν'.eA.injective (hq'.2.1.trans (Over.OverMorphism.ext ?_)), fun χ => ?_⟩⟩
  · rw [h.2.1, ← hq.2.1]
    exact (congrArg (fun z => z.left) (eA_ptHom f hf ν ν' _)).symm
  · have e : q'.1.2.s (I.e χ) = (∏ i, T (DegPre.gtφ D F p.g.b (ν.eX χ) i) ^ DegPre.gtε i) *
        Units.map f.toMonoidHom (q.1.2.s χ) := by
      refine Units.ext ?_
      show _ = _ * f (q.1.2.s χ : F)
      rw [hq'.2.2, hq.2.2, hX]
      have c := hg _ _ _ _ _ (p.g.isGen (ν.eX χ)) (𝟙 (Sp F))
      simp only [Category.id_comp, Category.comp_id] at c
      refine Eq.trans ?_ c
      let y : Sp F' := IsLocalRing.closedPoint F'
      have hJ : Good D.P.L y ν'.J := fun ψ => ν'.good ψ trivial
      refine (stalkConst y).injective ((val_eq_vF ν'.good _ _ y).symm.trans (Eq.trans ?_ (val_eq_vF ν'.good _ _ y)))
      refine congrArg Units.val ((val_corr hJ (h.2.2 _) _).trans ((val_pull hJ _ _ _).trans ?_))
      rw [Category.id_comp]
    rw [e, prod_gt]
    show _ * (T (ν.eA (N.c χ * q.1.2.b)).left / _) = _ * (T (ν.eA (N.c χ)).left / _) * (T (ν.eA q.1.2.b).left / _)
    rw [map_mul, hq.2.1, ν.c_eq]
    show _ * (T (DVR.cP D (TF (R := R) F) (ν.eX χ) * p.g.b).left / _) =
      _ * (T (DVR.cP D (TF (R := R) F) (ν.eX χ)).left / _) * _
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel

end GlobalTheory.GaugeHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumDHomDegenerationValuesFieldExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numDHom_degenerationValues_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ (N : NumD F) (N' : NumD F') (ν : NumOf D F N) (ν' : NumOf D F' N'), ν'.th = ν.th → ∃ I : NumD.Hom f N N', I.lam = 1 ∧ (∀ y, ν'.eX (I.e y) = ν.eX y) ∧ ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D F' k) (q : N.QT k) (q' : N'.QT k), QkExt f p p' → ν.QPt p q → ν'.QPt p' q' → q'.1.1.toAdd = I.e q.1.1.toAdd ∧ I.Rel q.1.2 q'.1.2 := by
  first | exact @GlobalTheory.GaugeHom.exists_hom | exact GlobalTheory.GaugeHom.exists_hom | (intros; apply GlobalTheory.GaugeHom.exists_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericRel
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericIso


open GlobalTheory.RigidGeneric GlobalTheory.SecRingIso ReciprocityTheory.ChartRestriction.G.DVR in
theorem exists_genericRel : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), GlobalTheory.GenericIso.LevelIso U.toUnifPre U'.toUnifPre hD j → GlobalTheory.GenericIso.Enough U.toUnifPre U'.toUnifPre hD j → ∃ (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))), GlobalTheory.GenericIso.GenericRel U.toUnifPre U'.toUnifPre hD j Φ w := by
  intro hL R _ _ I hI D D' A A' G G' _ _ _ _ hG hG' U U' hD j _ en
  obtain ⟨w, v, hw, hv, -, lf⟩ := exists_compare U
  obtain ⟨w', v', hw', hv', e', lf'⟩ := exists_compare U'
  have jac : I ≤ Ideal.jacobson ⊥ := by
    have := hI.2.2.2
    exact IsAdicComplete.le_jacobson_bot I
  have := hI.1
  have := hG.smooth
  have := hG'.smooth
  have := hG.geomConnected
  have := hG'.geomConnected
  let Ag : ∀ k, H0 U'.LG.L k → H0 U.LG.L k → Prop := fun k σ' σ => ∀ e,
    Agr (W := (thickObj R I e G').left) (Idx := D.toPre.P.L.ι × D'.toPre.P.L.ι)
      ((j e).hom.left ≫ (fstG I e G).left) (fstG I e G').left
      (fun y i => (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y) ∈
        D.toPre.P.L.U i.1 ∧ (U'.gt e).pG.left y ∈ D'.toPre.P.L.U i.2)
      (fun Z r z i jL => Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z i.1 (fun _ => jL))
      (fun Z r z i jL => Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z i.1 i.2 * Geo.Tor.gw (U'.w e) r z i.2 (fun _ => jL))
      σ σ'
  have ov : ∀ e, ((j e).hom.left ≫ (fstG I e G).left) ≫ G.hom = (fstG I e G').left ≫ G'.hom := fun e =>
    (Category.assoc _ _ _).trans ((congrArg ((j e).hom.left ≫ ·) (Over.w (fstG I e G))).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ thick R I e) (Over.w (j e).hom))).trans
        (Over.w (fstG I e G')).symm))
  have cov : ∀ e (y : (thickObj R I e G').left), ∃ i : D.toPre.P.L.ι × D'.toPre.P.L.ι,
      (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y) ∈
        D.toPre.P.L.U i.1 ∧ (U'.gt e).pG.left y ∈ D'.toPre.P.L.U i.2 := fun e y => by
    obtain ⟨a, ha⟩ := exists_chart D.toPre.P.isLB
      ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y))
    obtain ⟨b, hb⟩ := exists_chart D'.toPre.P.isLB ((U'.gt e).pG.left y)
    exact ⟨(a, b), ha, hb⟩
  obtain ⟨Φ, w₀, h₀, H⟩ := exists_iso_of_rel hL G.hom G'.hom U.LG.isLB U'.LG.isLB A A' (gen_over' U) (gen_over' U')
    (gen_injective U) (gen_injective U') hv hv' lf lf' Ag
    (fun k c s' s t' t d' d h h' f' f e => (h e).comb (ov e) (h' e) f f')
    (fun n m s' s t' t d' d h h' f' f e => (h e).mul (h' e) f f')
    (fun k s' s h => ⟨fun f => funext ((sec_eq_zero_and_hom_eq_of_thickenings R I jac G).1 _
        (linComb_isLB _ U.LG.isLB _ _) s fun e J => by
          have : IsIso (j e).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (j e).hom))
          exact (ConcreteCategory.bijective_of_isIso ((j e).hom.left.app _)).1
            (((h e).zero U'.LG.isLB (cov e) f J).trans (map_zero _).symm)),
      fun f => funext ((sec_eq_zero_and_hom_eq_of_thickenings R I jac G').1 _
        (linComb_isLB _ U'.LG.isLB _ _) s' fun e J => (h e).symm.zero U.LG.isLB (cov e) f J)⟩)
    (fun k hk s => by
      obtain ⟨c, t', t, hc, h₁, h₂⟩ := (en k hk).1 s
      exact ⟨c, hc, t', t, fun e Z r z i a b hC => h₂ e Z r z i.1 i.2 a b hC.1 hC.2, funext h₁⟩)
    (fun k hk s => by
      obtain ⟨c, t', t, hc, h₁, h₂⟩ := (en k hk).2 s
      exact ⟨c, hc, t', t, fun e Z r z i a b hC => h₂ e Z r z i.1 i.2 a b hC.1 hC.2, funext h₁⟩)
  obtain ⟨u, hu, K⟩ := exists_move U.LG.isLB U'.LG.isLB A.isLB A'.isLB (gen_inv U') hv h₀ hw' e'
    ((U'.gen ≪≫ Φ ≪≫ U.gen.symm).hom.left ≫ pullback.fst G.hom (jK R))
    ((Category.assoc _ _ _).trans (congrArg (U'.gen.hom.left ≫ ·) (Category.assoc _ _ _)))
  refine ⟨U'.gen ≪≫ Φ ≪≫ U.gen.symm, u, hu, fun k hk σ' σ h => ?_⟩
  obtain ⟨a, ha⟩ := exists_pulls U.LG.isLB A.isLB hv σ
  obtain ⟨a', ha'⟩ := exists_pulls U'.LG.isLB A'.isLB hv' σ'
  exact K k σ σ' a a' ha
    (H k hk σ' σ a' a (fun e Z r z i a b hC => h e Z r z i.1 i.2 a b hC.1 hC.2) ha' ha) ha'

end GlobalTheory.GenericIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionsBasisBaseChangeH1Vanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionsBasisBaseChangeH1Vanishing
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecBasis

theorem exists_sec_of_ker {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)}
    {M : LB Y} (P : Perf f M) (v : Fin P.a → R) (hv : P.D₀.mulVec v = 0) :
    ∃ s : LB.Sec M, ∀ i, rs Y (P.le i) (s.f (P.ch i)) = Seesaw.loc₀ P v i := by
  have h : IsPullback (𝟙 Y) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E, hE⟩ := P.sec R (RingHom.id R) Y (𝟙 Y) f h
  let t := E ⟨v, hv⟩
  have le : ∀ j, M.U j ≤ (M.pull (𝟙 Y)).U (fun _ => j) := fun j => le_pull M (𝟙 Y) le_rfl
  refine ⟨⟨fun j => rs Y (le j) (t.f fun _ => j), fun i j => ?_⟩, fun i => ?_⟩
  · have e := GlobalTheory.LB.sec_rel t (fun _ => i) (fun _ => j) (inf_le_left.trans (le i))
      (inf_le_right.trans (le j)) (inf_le_inf (le i) (le j))
    have e' := (GlobalTheory.LB.resG_pull_g (L := M) (𝟙 Y) (fun _ => i) (fun _ => j)
      (inf_le_inf (le i) (le j))).trans (rs_self _ _)
    exact (rs_rs _ _ _).trans (e.trans (congrArg₂ (· * ·) e' (rs_rs _ _ _).symm))
  · exact (rs_rs _ _ _).trans (hE ⟨v, hv⟩ i)

theorem exists_sec_iso {X X' : Scheme.{0}} {β : X' ⟶ X} {M : LB X} {M' : LB X'} (hM : M.IsLB) (hM' : M'.IsLB)
    (w : LB.Iso M' (M.pull β)) (hw : w.IsGen) (s : LB.Sec M') :
    ∃ t : LB.Sec (M.pull β), ∀ z k k', β z ∈ M.U k → z ∈ M'.U k' →
      gs (𝟙 X') z _ (t.f fun _ => k) = (Geo.Tor.gw w (𝟙 _) z k k').val * gs (𝟙 X') z _ (s.f k') := by
  refine ⟨SecOn.topEquiv _ (SecOn.congr hM' (LB.isLB_pull hM β) w hw ⊤ ((SecOn.topEquiv M').symm s)),
    fun z k k' hk hk' => ?_⟩
  have hz : z ∈ (M.pull β).U (fun _ => k) ⊓ M'.U k' := ⟨mem_pull.2 hk, hk'⟩
  have e := congrArg (gs (𝟙 X') z _) (SecOn.coord_congr hM' (LB.isLB_pull hM β) w hw
    ((SecOn.topEquiv M').symm s) (fun _ => k) k' (le_inf le_top inf_le_left) (le_inf le_top inf_le_right) le_rfl)
  rw [gs_mul _ _ _ hz, gs_res _ _ _ hz, gs_res _ _ _ hz, gs_res _ _ _ hz] at e
  refine (gs_res _ _ _ hz.1 _).trans (e.trans (congrArg₂ (· * ·) (gs_unit _ _ _ hz _) ?_))
  exact gs_res (𝟙 X') z (inf_le_right : ⊤ ⊓ M'.U k' ≤ _) ⟨trivial, hk'⟩ (s.f k')

theorem gs_comb {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (z : X)
    {U : X.Opens} (h : z ∈ U) {n : ℕ} (c : Fin n → R) (x : Fin n → Γ(X, U)) :
    gs (𝟙 X) z U (∑ j, AbLaw.cst f U (c j) * x j) = ∑ j, gs (𝟙 X) z ⊤ (AbLaw.cst f ⊤ (c j)) * gs (𝟙 X) z U (x j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [gs_eq _ _ _ h, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← gs_eq _ _ _ h, gs_mul _ _ _ h, ← rs_cst f (le_top : U ≤ ⊤), gs_res _ _ _ h]

theorem loc_mulVec {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (P : Perf f M) (π : X' ⟶ X)
    (f' : X' ⟶ Spec (CommRingCat.of R')) {n : ℕ} (B : Matrix (Fin P.a) (Fin n) R') (c : Fin n → R') (i : P.I) :
    Seesaw.loc P π f' (B.mulVec c) i = ∑ j, AbLaw.cst f' _ (c j) * Seesaw.loc P π f' (fun k => B k j) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Seesaw.loc, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem exists_basis : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → IsProjBy f → ∀ M : LB X, M.IsLB → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (M₀ : LB X₀) (w₀ : LB.Iso M₀ (M.pull π)), M₀.IsLB → w₀.IsGen → FirstCohomologyVanishes M₀ → ∃ (n : ℕ) (τ : Fin n → LB.Sec M), ∀ (A' : Type) [CommRing A'] (g : A →+* A') (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (M' : LB X') (w : LB.Iso M' (M.pull β)) (τ' : Fin n → LB.Sec M'), M'.IsLB → w.IsGen → (∀ i, (∀ z (k : (M).ι) (k' : (M').ι), (β) z ∈ (M).U k → z ∈ (M').U k' → gs (β) z _ ((τ i).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((τ' i).f k'))) → ∀ s' : LB.Sec M', ∃! c : Fin n → A', ∀ k : M'.ι, s'.f k = ∑ i, AbLaw.cst f' (M'.U k) (c i) * (τ' i).f k := by
  intro A _ _ _ X f hf hp M hM K _ g₀ hg₀ X₀ π f₀ h₀ M₀ w₀ hM₀ hw₀ hH
  obtain ⟨P⟩ := nonempty_perf_of_noetherian A X f hf hp M hM
  obtain ⟨w₁, hw₁⟩ := LBIso.symm (⟨w₀, hw₀⟩ : LBIso _ _)
  obtain ⟨r, n, B, hr, hB, hu⟩ := exists_matrix_basis_ker_of_exact_at_point A K g₀ _ _ _ P.D₀ P.D₁
    P.comp (P.exact K g₀ X₀ π f₀ h₀ (H1Iso.firstCohomologyVanishes_of_iso_of_isGen hM₀.cover (LB.isLB_pull hM π) w₁ hw₁ hH))
  have hru : IsUnit r := by
    by_contra hn
    have := IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g₀ hg₀)
    exact hr ((RingHom.mem_ker).1 (this ▸ (show r ∈ IsLocalRing.maximalIdeal A from hn)))
  choose τ hτ using fun j => exists_sec_of_ker P (fun k => B k j) (funext fun l => congrFun₂ hB l j)
  refine ⟨n, τ, fun A' _ g X' β f' h M' w τ' hM' hw hτ' s' => ?_⟩
  obtain ⟨E, hE⟩ := P.sec A' g X' β f' h
  obtain ⟨t, ht⟩ := exists_sec_iso hM hM' w hw s'
  obtain ⟨v, rfl⟩ := E.surjective t
  have hA : ∀ z i k', β z ∈ P.W i → z ∈ M'.U k' → gs (𝟙 X') z _ (Seesaw.loc P β f' v.1 i) =
      (Geo.Tor.gw w (𝟙 _) z (P.ch i) k').val * gs (𝟙 X') z _ (s'.f k') := fun z i k' hi hk' =>
    (congrArg (gs (𝟙 X') z _) (hE v i).symm).trans ((gs_res (𝟙 X') z (le_pull M β (P.le i)) hi _).trans (ht z _ k' (P.le i hi) hk'))
  have hC : ∀ (c : Fin n → A') z i k', β z ∈ P.W i → z ∈ M'.U k' →
      gs (𝟙 X') z _ (Seesaw.loc P β f' ((B.map g).mulVec c) i) =
      (Geo.Tor.gw w (𝟙 _) z (P.ch i) k').val *
        gs (𝟙 X') z _ (∑ j, AbLaw.cst f' (M'.U k') (c j) * (τ' j).f k') := fun c z i k' hi hk' => by
    rw [loc_mulVec, gs_comb f' z (show z ∈ β ⁻¹ᵁ P.W i from hi), gs_comb f' z hk', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm, ← hτ' j z _ k' (P.le i hi) hk']
    refine congrArg (_ * ·) ?_
    refine (congrArg (gs (𝟙 X') z _) (Seesaw.loc_comp P h (fun k => B k j) i)).trans ?_
    rw [← hτ j i]
    refine (gs_pull (𝟙 X') β z _ hi _).trans ?_
    rw [Category.id_comp]
    exact gs_res β z _ hi _
  refine (existsUnique_congr fun c => ⟨fun hc k' => fn_ext fun z hz => ?_, fun hc => ?_⟩).1
    (hu A' g (hru.map g) v.1 v.2)
  · obtain ⟨i, hi⟩ := Seesaw.exists_mem P (β z)
    have e := hC c z i k' hi hz
    rw [hc, hA z i k' hi hz] at e
    exact (Units.mul_right_inj _).1 e
  · have hk : (P.D₀.map g).mulVec ((B.map g).mulVec c) = 0 := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hB, Matrix.map_zero _ (map_zero g), Matrix.zero_mulVec]
    refine congrArg Subtype.val (E.injective (a₁ := ⟨_, hk⟩) (a₂ := v) ?_)
    refine Seesaw.sec_ext _ _ (fun i => β ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull M β (P.le i))
      (fun y => Seesaw.exists_mem P (β y)) fun i => ?_
    refine (hE ⟨_, hk⟩ i).trans (Eq.trans (fn_ext fun z hz => ?_) (hE v i).symm)
    obtain ⟨k', hk'⟩ := exists_chart hM' z
    exact (hC c z i k' hz hk').trans ((congrArg (fun x => _ * gs (𝟙 X') z _ x) (hc k').symm).trans
      (hA z i k' hz hk').symm)

end GlobalTheory.SecBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionsBasisBaseChangeH1VanishingStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_basis_baseChange_h1Vanishing : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → IsProjBy f → ∀ M : LB X, M.IsLB → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (M₀ : LB X₀) (w₀ : LB.Iso M₀ (M.pull π)), M₀.IsLB → w₀.IsGen → FirstCohomologyVanishes M₀ → ∃ (n : ℕ) (τ : Fin n → LB.Sec M), ∀ (A' : Type) [CommRing A'] (g : A →+* A') (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (M' : LB X') (w : LB.Iso M' (M.pull β)) (τ' : Fin n → LB.Sec M'), M'.IsLB → w.IsGen → (∀ i, (∀ z (k : (M).ι) (k' : (M').ι), (β) z ∈ (M).U k → z ∈ (M').U k' → gs (β) z _ ((τ i).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((τ' i).f k'))) → ∀ s' : LB.Sec M', ∃! c : Fin n → A', ∀ k : M'.ι, s'.f k = ∑ i, cst f' (M'.U k) (c i) * (τ' i).f k := by
  first | exact @GlobalTheory.SecBasis.exists_basis | exact GlobalTheory.SecBasis.exists_basis | (intros; apply GlobalTheory.SecBasis.exists_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasSumOfAdicSumUnitBallExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasSumOfAdicSumUnitBallExtension
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.AdicNormSum

open Filter Topology in
private lemma exists_norm_le_mul_of_mem_ideal_smul_fg {R C : Type} [CommRing R] [NormedField C]
    [IsUltrametricDist C] {_ : Module R C} (φ : R →+* C) (hφ : ∀ r, ‖φ r‖ ≤ 1)
    (hsmul : ∀ (r : R) (y : C), r • y = φ r * y) {N : Submodule R C} (hN : N.FG) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (J : Ideal R) (t : ℝ), 0 ≤ t → (∀ r ∈ J, ‖φ r‖ ≤ t) →
      ∀ y ∈ J • N, ‖y‖ ≤ t * M := by
  obtain ⟨G, rfl⟩ := hN
  have hbound : ∀ y ∈ Submodule.span R (G : Set C), ‖y‖ ≤ (G.sup fun g => ‖g‖₊ : NNReal) := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro g hg
      exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun g => ‖g‖₊) hg)
    · simp
    · intro a b _ _ ha hb
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    · intro a b _ hb
      rw [hsmul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hφ a)).trans hb
  refine ⟨(G.sup fun g => ‖g‖₊ : NNReal), NNReal.coe_nonneg _, ?_⟩
  intro J t ht hJ y hy
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro r hr z hz
    rw [hsmul, norm_mul]
    exact mul_le_mul (hJ r hr) (hbound z hz) (norm_nonneg _) ht
  · intro a b ha hb
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

open Filter Topology in
private lemma exists_uniform_norm_bound_lt_one_of_fg {R C : Type} [CommRing R] [NormedField C]
    [IsUltrametricDist C] (φ : R →+* C) (hφ : ∀ r, ‖φ r‖ ≤ 1) {I : Ideal R} (hfg : I.FG)
    (hI : ∀ r ∈ I, ‖φ r‖ < 1) : ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ r ∈ I, ‖φ r‖ ≤ c := by
  obtain ⟨G, rfl⟩ := hfg
  refine ⟨(G.sup fun g => ‖φ g‖₊ : NNReal), NNReal.coe_nonneg _, ?_, ?_⟩
  · have h : G.sup (fun g => ‖φ g‖₊) < 1 := by
      rw [Finset.sup_lt_iff (by simp)]
      intro g hg
      have hg' := hI g (Ideal.subset_span hg)
      exact_mod_cast hg'
    exact_mod_cast h
  · intro r hr
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hr
    · intro g hg
      exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun g => ‖φ g‖₊) hg)
    · simp
    · intro a b _ _ ha hb
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    · intro a b _ hb
      rw [smul_eq_mul, map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hφ a)).trans hb

open Filter Topology in
private lemma hasSum_of_norm_sub_le_geometric {Ix E : Type} [NormedAddCommGroup E]
    {x : Ix → E} {s : E} {c M : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (h : ∀ n : ℕ, ∃ S : Finset Ix, ∀ T : Finset Ix, S ⊆ T → ‖s - ∑ i ∈ T, x i‖ ≤ c ^ n * M) :
    HasSum x s := by
  show Tendsto (fun T : Finset Ix => ∑ i ∈ T, x i) atTop (𝓝 s)
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hlim : Tendsto (fun n : ℕ => c ^ n * M) atTop (𝓝 (0 * M)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const M
  rw [zero_mul] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  obtain ⟨S, hS⟩ := h n
  refine Filter.eventually_atTop.2 ⟨S, fun T hT => ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact (hS T hT).trans_lt hn

open Filter Topology in
private lemma norm_le_pow_of_mem_ideal_pow {R C : Type} [CommRing R] [NormedField C]
    [IsUltrametricDist C] (φ : R →+* C) (hφ : ∀ r, ‖φ r‖ ≤ 1) {I : Ideal R} {c : ℝ}
    (hc0 : 0 ≤ c) (hI : ∀ r ∈ I, ‖φ r‖ ≤ c) : ∀ n : ℕ, ∀ r ∈ I ^ n, ‖φ r‖ ≤ c ^ n := by
  intro n
  induction n with
  | zero => intro r _; simpa using hφ r
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro a ha b hb
      rw [map_mul, norm_mul, pow_succ]
      exact mul_le_mul (ih a ha) (hI b hb) (norm_nonneg _) (pow_nonneg hc0 n)
    · intro a b ha hb
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)


open Filter Topology in
theorem _root_.GlobalTheory.Ex.AdicNormSum.main : ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (I : Ideal R) (C : Type) [NormedField C] [IsUltrametricDist C]
    [Algebra (FractionRing R) C], _root_.GlobalTheory.Ex.CExt R I C → ∀ (Ix : Type) (x : Ix → C)
    (s : C), _root_.GlobalTheory.UT.SumF I C x s → HasSum x s := by
  intro R _ _ _ I C _ _ _ hC Ix x s hs
  obtain ⟨hle, hlt⟩ := hC
  letI : Module R C := Module.compHom C (algebraMap R (FractionRing R))
  have hs' : _root_.GlobalTheory.UT.SumI I x s := hs
  unfold _root_.GlobalTheory.UT.SumI at hs'
  obtain ⟨N, hNfg, -, -, hconv⟩ := hs'
  let φ : R →+* C := (algebraMap (FractionRing R) C).comp (algebraMap R (FractionRing R))
  have hφ : ∀ r, ‖φ r‖ ≤ 1 := hle
  obtain ⟨M, -, hM⟩ := exists_norm_le_mul_of_mem_ideal_smul_fg (N := N) φ hφ
    (fun r y => Algebra.smul_def (algebraMap R (FractionRing R) r) y) hNfg
  obtain ⟨c, hc0, hc1, hcI⟩ := exists_uniform_norm_bound_lt_one_of_fg φ hφ (IsNoetherian.noetherian I) hlt
  exact hasSum_of_norm_sub_le_geometric hc0 hc1 fun n => (hconv n).imp fun S hS T hT =>
    hM (I ^ n) (c ^ n) (pow_nonneg hc0 n) (norm_le_pow_of_mem_ideal_pow φ hφ hc0 hcI n) _ (hS T hT)

end GlobalTheory.Ex.AdicNormSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasSumOfAdicSumUnitBallExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_of_adicSum_unitBallExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing R) C], CExt R I C → ∀ (Ix : Type) (x : Ix → C) (s : C), GlobalTheory.UT.SumF I C x s → HasSum x s := by
  first | exact @GlobalTheory.Ex.AdicNormSum.main | exact GlobalTheory.Ex.AdicNormSum.main | (intros; apply GlobalTheory.Ex.AdicNormSum.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedPointMemRange
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.TowerAlg

theorem closedPoint_mem_range {R : Type} [CommRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤) (e : ℕ) :
    IsLocalRing.closedPoint R ∈ Set.range (thick R I e) := by
  have h := range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := I ^ (e + 1)))
  refine h.ge ?_
  rw [Ideal.mk_ker]
  exact (Ideal.pow_le_self (Nat.succ_ne_zero e)).trans (IsLocalRing.le_maximalIdeal hI)

theorem triv_of_forall_thick (hG : GlobalFnsSt) (hS : SecAlgSt) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    {I : Ideal V} (hI : I ≠ ⊤) (hV : IsAdicComplete I V) (B : Over (Spec (CommRingCat.of V))) [GrpObj B]
    (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) (N : LB B.left) (hN : N.IsLB)
    (ht : ∀ e, Triv (N.pull (fstG I e B).left)) : Triv N := by
  let o : Spec (CommRingCat.of V) ⟶ B.left := (η[B]).left
  have ho : o ≫ B.hom = 𝟙 _ := Over.w η[B]
  obtain ⟨c, hc⟩ := DVR.exists_gen_of_local N hN (K := PUnit) (fun _ => o) (fun _ => 1)
  have pb : ∀ e, IsPullback (fstG I e B).left (thickObj V I e B).hom B.hom (thick V I e) :=
    fun e => IsPullback.of_hasPullback B.hom (thick V I e)
  choose t tg tv using fun e => AbTriv.exists_normalised hN ho c hc (pb e) (ht e)
  have tm : ∀ e, thickMap V I e B ≫ (fstG I (e + 1) B).left = (fstG I e B).left := fun e =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have compat : ∀ e z J, Good N z J → val (t (e + 1)) (thickMap V I e B) z J = val (t e) (𝟙 _) z J := by
    intro e z J hJ
    let a := (pb e).lift (thick V I e ≫ o) (𝟙 _) (by rw [Category.assoc, ho, Category.comp_id, Category.id_comp])
    have a₁ : a ≫ (fstG I e B).left = thick V I e ≫ o := (pb e).lift_fst _ _ _
    have key := gen_unique' hN (fun U _ k => by simp only [tm e]) (thickObj V I e B).hom a ((pb e).lift_snd _ _ _)
      (hG _ _ (TLinPf.isAb_pullback (thick V I e) B hB)).2 (tg e)
      (DVR.pullGen_isGen _ _ _ _ (tg (e + 1)) (thickMap V I e B))
      (fun y J hJ => (tv e _ a _ y J hJ a₁).trans ((val_pull hJ _ _ _).trans
        (tv (e + 1) _ _ _ y J hJ (by rw [Category.assoc, tm e, a₁]))).symm) _ (𝟙 _) z J hJ
    rw [val_pull hJ, Category.id_comp] at key
    exact key.symm
  obtain ⟨s, hs, -⟩ := hS V I hV B hB.smooth hp N hN (fun e => genSec (t e) (tg e))
    (fun e z J hJ => (sval_genSec _ _ _ z hJ).trans
      ((congrArg Units.val (compat e z J hJ)).trans (sval_genSec _ _ _ z hJ).symm))
  have := hB.proper
  have top : nonzeroLocus s = ⊤ := AbTriv.eq_top_of_closed_fibre B.hom _ fun x hx => by
    have hm : x ∈ Set.range (pullback.fst B.hom (thick V I 0)) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hx]
      exact closedPoint_mem_range hI 0
    obtain ⟨z, rfl⟩ := hm
    choose J hJ using fun ψ : ((Over.map (thick V I 0)).obj (thickObj V I 0 B)).left ⟶ B.left =>
      exists_chart hN (ψ z)
    refine (TwistZero.mem_nonzeroLocus_iff s (fstG I 0 B).left z hJ).2 ?_
    rw [hs 0 z J hJ, sval_genSec _ _ _ z hJ]
    exact Units.isUnit _
  refine AbTriv.triv_of_pull_id (TwistZero.triv_of_sec hN s fun y J hJ => ?_)
  exact (TwistZero.mem_nonzeroLocus_iff s (𝟙 _) y hJ).1 (by rw [top]; trivial)

theorem triv_pull_of_gen {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull F)) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {ε : K → ℤ}
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (r : Z ⟶ Y') (π : Z ⟶ Y)
    (hc : ∀ k, (r ≫ φ' k) ≫ F = π ≫ φ k) : Triv ((LB.LinComb L φ ε).pull π) := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨t, ht, -⟩ := exists_up ((isGen_iff w).1 hw) hL hL' _ (DVR.pullGen_isGen _ _ _ _ ha r)
  refine (KerPow.pull_iff φ ε π).2 ?_
  rw [← (funext hc : (fun k => (r ≫ φ' k) ≫ F) = fun k => π ≫ φ k)]
  exact ⟨t, ht⟩

section Level
variable {S S' Z : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
  {f : S' ⟶ S} {F : B'.left ⟶ B.left}


omit [IsCommMonObj B] [IsCommMonObj B'] in
theorem toBase_mul (h : IsGrpPullback B' B f F) (T : Over S') (x y : T ⟶ B') :
    toBase h.1.w (x * y) = toBase h.1.w x * toBase h.1.w y :=
  Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem triv_theta (h : IsGrpPullback B' B f F) (M' : CP B') {L : LB B.left} (hL : L.IsLB)
    (hw : LBIso M'.L.L (L.pull F)) (π : Z ⟶ (G3 B).left) (z : Z ⟶ S') (hz : π ≫ (G3 B).hom = z ≫ f) :
    Triv ((Theta B L).pull π) := by
  let ρ : Over.mk ((Over.mk z).hom ≫ f) ⟶ G3 B := Over.homMk π hz
  let x : Fin 3 → (Over.mk z ⟶ B') := fun i =>
    Over.homMk (h.1.lift (ρ ≫ x3 B i).left z (Over.w (ρ ≫ x3 B i))) (h.1.lift_snd _ _ _)
  let β := toBaseHom (toBase_mul h) (Over.mk z)
  have hx : ∀ i, β (x i) = ρ ≫ x3 B i := fun i => Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  let r : Over.mk z ⟶ G3 B' := lift (x 0) (lift (x 1) (x 2))
  have hr : ∀ i, r ≫ x3 B' i = x i := fun i => by fin_cases i <;> simp [r, x3]
  refine triv_pull_of_gen hL M'.L.isLB hw (φ := thφ B (x3 B)) (φ' := thφ B' (x3 B')) (ε := thε) M'.c.t M'.c.isGen
    r.left π fun I => ?_
  have e : β (r ≫ psum B' (x3 B') I.down) = ρ ≫ psum B (x3 B) I.down :=
    (psum_hom (β.comp (preHom r)) (x3 B') I.down).trans ((congrArg (fun q => psum B q I.down) (funext fun i =>
      (congrArg β (hr i)).trans (hx i))).trans (psum_hom (preHom ρ) (x3 B) I.down).symm)
  exact congrArg (fun q => q.left) e

theorem triv_sym (h : IsGrpPullback B' B f F) (M' : CP B') {L : LB B.left} (hL : L.IsLB)
    (hw : LBIso M'.L.L (L.pull F)) (π : Z ⟶ B.left) (z : Z ⟶ S') (hz : π ≫ B.hom = z ≫ f) :
    Triv ((LB.LinComb L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]).pull π) := by
  let x : Over.mk z ⟶ B' := Over.homMk (h.1.lift π z hz) (h.1.lift_snd _ _ _)
  have hx : x.left ≫ F = π := h.1.lift_fst _ _ _
  refine triv_pull_of_gen hL M'.L.isLB hw M'.sym M'.sym_gen x.left π fun k => ?_
  fin_cases k
  · exact (inv_left_comp (toBase_mul h) x).trans (congrArg (· ≫ _) hx)
  · exact ((congrArg (· ≫ F) (Category.comp_id _)).trans hx).trans (Category.comp_id _).symm

end Level

section Pack
variable (hG : GlobalFnsSt) (hS : SecAlgSt) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  (hI : I ≠ ⊤) (hc : IsAdicComplete I R) {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
  [∀ e, GrpObj (Y e)] [∀ e, IsCommMonObj (Y e)] (N : ∀ e, CP (Y e)) {B : Over (Spec (CommRingCat.of R))} [GrpObj B]
  [IsCommMonObj B] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {b : ∀ e, (Y e).left ⟶ B.left}
  (hg : ∀ e, IsGrpPullback (Y e) B (thick R I e) (b e)) {M : LB B.left} (hM : M.IsLB)
  (hiso : ∀ e, LBIso (N e).L.L (M.pull (b e)))
include hG hS hI hc hB hp hg hM hiso

theorem triv_theta_alg : Triv (Theta B M) :=
  triv_of_forall_thick hG hS hI hc (G3 B)
    (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB hB))
    (isProjBy_tensor R _ _ hp (isProjBy_tensor R _ _ hp hp)) (Theta B M) (LB.isLB_linComb hM _ _) fun e =>
      triv_theta (hg e) (N e) hM (hiso e) (fstG I e (G3 B)).left (pullback.snd (G3 B).hom (thick R I e))
        (pullback.condition (f := (G3 B).hom) (g := thick R I e))

theorem triv_sym_alg : Triv (LB.LinComb M (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]) :=
  triv_of_forall_thick hG hS hI hc B hB hp _ (LB.isLB_linComb hM _ _) fun e =>
    triv_sym (hg e) (N e) hM (hiso e) (fstG I e B).left (pullback.snd B.hom (thick R I e))
      (pullback.condition (f := B.hom) (g := thick R I e))

theorem exists_cp_alg (hY : ∀ e, IsAbelianScheme (Y e)) :
    ∃ Q : CP B, Q.L.L = M ∧ ∀ e, IsCPPullback (N e) Q (thick R I e) (b e) := by
  obtain ⟨r, hr⟩ := DVR.exists_gen_of_local M hM (K := PUnit) (fun _ => eSec B) (fun _ => 1)
  obtain ⟨Q, hQ⟩ := AbPackage.exists_cp hG hB ⟨M, r, hM, hr⟩ (triv_theta_alg hG hS hI hc N hB hp hg hM hiso)
    (triv_sym_alg hG hS hI hc N hB hp hg hM hiso)
  have e₀ : Q.L.L = M := congrArg (fun q => q.L) hQ
  refine ⟨Q, e₀, fun e => ⟨hg e, ?_⟩⟩
  obtain ⟨w, hw⟩ : LBIso (N e).L.L (Q.L.L.pull (b e)) := by rw [e₀]; exact hiso e
  exact AbPackage.exists_isCPMap_of_iso hG (hY e) Q (N e) (toBase_mul (hg e)) w hw

end Pack

end GlobalTheory.TowerAlg
end
end
