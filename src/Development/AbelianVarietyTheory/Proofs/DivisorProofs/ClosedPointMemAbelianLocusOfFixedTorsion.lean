module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingConditionLocusIsClopen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsAmpleHermLineBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisResidueFieldUniformiserCons

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationExtensionLocalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerSemiAbelianScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem exists_eighthPower_semiAbelianScheme : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∃ (G₈ : Over (Sp R)) (_ : GrpObj G₈) (prG : Fin 8 → (G₈ ⟶ G)), IsSemiAbelian G₈ ∧ (∀ u, IsMonHom (prG u)) ∧ ∀ (T : Over (Sp R)) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ G₈, ∀ u, x ≫ prG u = y u := by
  intro R _ G _ hG
  haveI : IsCommMonObj G := hG.comm
  refine ⟨powObj G 8, inferInstance, powPr G, ?_, fun u => inferInstance, fun T y => ?_⟩
  · exact GlobalTheory.PowGrp.isSemiAbelian_pow _ (powObj G 8) G 8 (powIsPowGrp G 8) hG
  · refine ⟨(powIsLimit G 8).lift (Fan.mk T y), fun u => (powIsLimit G 8).fac (Fan.mk T y) ⟨u⟩, ?_⟩
    intro x hx
    apply (powIsLimit G 8).hom_ext
    rintro ⟨u⟩
    exact (hx u).trans ((powIsLimit G 8).fac (Fan.mk T y) ⟨u⟩).symm

end GlobalTheory.MBLow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerEvenUnimodularCharZero
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.PowEightField

open GlobalTheory.EighthPowerFactor GlobalTheory.CechPic

theorem exists_eighthPower_evenUnimodular_charZero : ∃ d : ℕ, 1 ≤ d ∧ ∀ (K : Type) [Field K] [CharZero K] (P : PolAV (Sp K)), ∃ (Q : PolAV (Sp K)) (pr : Fin 8 → (Q.A ⟶ P.A)) (inc : P.A ⟶ Q.A), Q.g = 8 * P.g ∧ (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) ∧ IsPow8 P Q d pr inc := by
  obtain ⟨W, hW, hbas⟩ := ZM.exists_isE8_isSharpBasis
  have hW0 : 0 < W 0 0 := by
    have h := hW.1.diag_pos (i := 0)
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_add] at h
    have : (0 : ℝ) < (W 0 0 : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨(2 * W 0 0).toNat, by omega, ?_⟩
  intro K _ _ P
  have := P.isAb.comm
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  obtain ⟨bas, hb⟩ := hbas P.g
  obtain ⟨a, w, w', hw, hw', hs⟩ := exists_matrices hW.2
  let b : ZM.TBase K 1 := ⟨1, by simp, fun K _ β => by simp⟩
  have hc : (siegOne L₁.globalFns P.isAb P.isLB P.g).Principal :=
    ⟨relAmple_diag_lam P.isAb P.isLB (Moduli.cube_of_isLB _ P P.L P.isLB) P.ample,
      fun T x hx => SiegelOfPolarised.eq_one_of_lam P.isLB P.ktriv x hx⟩
  obtain ⟨t, ⟨pr, hpr, hu, hL, -⟩, h₁, h₂, h₃⟩ := exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB P.g _ W _ a w w'
    bas hW hb hw hw' hs 1 K b _ (𝟙 _) (siegOne L₁.globalFns P.isAb P.isLB P.g) (one_pow _) odd_one hc P.smoothDim
  obtain ⟨inc, hinc, -⟩ := hu P.A fun u => if u = 0 then 𝟙 P.A else 1
  refine ⟨t.pol, pr, inc, rfl, ⟨t.act w, t.act w', t.hom w, t.hom w', h₁, h₃, h₂⟩, hpr, ?_, hu, hinc, ?_⟩
  · refine isMonHom_of_coord hpr hu fun u => ?_
    rw [hinc u]
    by_cases h : u = 0
    · subst h; simp only [↓reduceIte]; exact inferInstanceAs (IsMonHom (𝟙 P.A))
    · simp only [h, ↓reduceIte]; exact inferInstanceAs (IsMonHom (toUnit P.A ≫ η[P.A]))
  ·
    have hP : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
    have hQ : t.pol.L.IsLB := t.pol.isLB
    have hlam : cls _ hP = lam (cls P.L P.isLB) (fst P.A P.A) (snd P.A P.A) := cls_cube_two P.isLB _ _ hP
    have hdiag := (cls_eq_iff (LB.isLB_linComb P.isLB _ _) (pull_isLB hP _)).2 (SiegelOfPolarised.lbIso_diag L₁ P)
    rw [cls_lbPow P.isLB, cls_pull hP, hlam, pull_lam, lift_fst, lift_snd] at hdiag
    have e1 := ((cls_eq_iff hQ (LB.isLB_linComb hP _ _)).2 hL).trans (cls_linComb hP _ _ _)
    refine (cls_eq_iff (pull_isLB hQ _) (LB.isLB_linComb P.isLB _ _)).1 ?_
    refine ((congrArg (pull inc.left) e1).trans ?_).trans (cls_lbPow P.isLB _ _).symm
    rw [hlam]
    erw [map_sum]
    rw [Fintype.sum_eq_single ((0 : Fin 8), (0 : Fin 8))]
    · erw [map_zsmul]
      erw [CechPic.pull_lam, CechPic.pull_lam]
      erw [lift_fst, lift_snd]
      dsimp only
      erw [hinc]
      simp only [↓reduceIte]
      rw [← hdiag, ← natCast_zsmul, ← natCast_zsmul, smul_smul, Int.toNat_of_nonneg (by omega)]
      congr 1
      push_cast
      ring
    · rintro ⟨u, v⟩ huv
      erw [map_zsmul]
      erw [CechPic.pull_lam, CechPic.pull_lam]
      erw [lift_fst, lift_snd]
      dsimp only
      have hi1 : ∀ u : Fin 8, u ≠ 0 → inc ≫ pr u = 1 := fun u h => (hinc u).trans (if_neg h)
      by_cases hu0 : u = 0
      · subst hu0
        have hv0 : v ≠ 0 := fun h => huv (by rw [h])
        erw [hi1 v hv0, lam_one_right, smul_zero]
      · erw [hi1 u hu0, lam_one_left, smul_zero]

end GlobalTheory.MBLow.PowEightField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationExtensionLocalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.SplitPowEight

def isPowGrpOfUnique {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (pr : Fin j → (G' ⟶ G))
    (hpr : ∀ u, IsMonHom (pr u))
    (hu : ∀ (T : Over S) (y : Fin j → (T ⟶ G)), ∃! x : T ⟶ G', ∀ u, x ≫ pr u = y u) : IsPowGrp G' G j :=
  ⟨pr, hpr, Fan.IsLimit.mk _ (fun s => (hu s.pt s.proj).choose) (fun s u => (hu s.pt s.proj).choose_spec.1 u)
    fun s m hm => (hu s.pt s.proj).choose_spec.2 m hm⟩

def powPullback {S S' : Scheme.{0}} (f : S' ⟶ S) {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G' G j) : IsPowGrp ((Over.pullback f).obj G') ((Over.pullback f).obj G) j :=
  ⟨fun u => (Over.pullback f).map (p.pr u), fun u => by have := p.hom u; infer_instance,
    isLimitFanMkObjOfIsLimit (Over.pullback f) _ _ p.lim⟩

theorem exists_unif_pow8 : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ ψ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) ψ → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (io : V →+* W) (em : W →+* AlgebraicClosure (FractionRing V)) (D : DegData W (maximalIdeal W)) (Q : PolAV (Sp (FractionRing W))) (H : Over (Sp W)) (_ : GrpObj H) (_ : IsCommMonObj H) (U : Unif (maximalIdeal W) D Q H) (i : (Over.pullback (spMap io)).obj G ⟶ H) (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), GlobalTheory.LN.CDvr W ∧ io.Finite ∧ Function.Injective io ∧ Function.Injective em ∧ (∀ v, em (io v) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ IsSemiAbelian H ∧ GlobalTheory.LN.ToATotal U.toUnifPre ∧ (∀ k, IsMonHom (r k)) ∧ i ≫ r 0 = 𝟙 _ ∧ ∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y := by
  intro V _ _ _ hV A G _ _ hG ψ hψ
  obtain ⟨hd, hc, hch⟩ := hV
  obtain ⟨gen, hgen, -⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V)) hψ
  obtain ⟨G8, _, prG, hG8, hprG, huG⟩ := GlobalTheory.MBLow.exists_eighthPower_semiAbelianScheme V G hG
  have : IsCommMonObj G8 := hG8.comm
  let p8 : IsPowGrp G8 G 8 := isPowGrpOfUnique prG hprG huG
  let F := AlgebraicClosure (FractionRing V)
  have : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective V F).2 (by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V) F]
    exact (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _))
  have : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := FractionRing V) (C := F)).2 inferInstance
  obtain ⟨W, hWd, hWc, hWf, hsplit⟩ := GlobalTheory.Ex.UnifModel.exists_split V F G8 hG8
  have : CharZero F := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective V F)
  have : CharZero W := RingHom.charZero (algebraMap W F)
  have hio : Function.Injective (algebraMap V W) := fun a b h =>
    FaithfulSMul.algebraMap_injective V F (congrArg Subtype.val h)
  let io : V →+* W := algebraMap V W
  let H := (Over.pullback (spMap io)).obj G8
  let pH : IsPowGrp H ((Over.pullback (spMap io)).obj G) 8 := powPullback (spMap io) p8
  have hH : IsSemiAbelian H := IsSemiAbelian.pullback _ G8 hG8
  obtain ⟨A', ψ', hψ'⟩ := GlobalTheory.UnifProperOpen.exists_polGeneric_pullback V A G gen hgen W io hio
  obtain ⟨d, -, hQ⟩ := GlobalTheory.MBLow.PowEightField.exists_eighthPower_evenUnimodular_charZero
  obtain ⟨Q, pr, inc, -, hS, hP⟩ := hQ (FractionRing W) A'
  let pQ : IsPowGrp Q.A A'.A 8 := isPowGrpOfUnique pr hP.1 hP.2.2.1
  obtain ⟨φ₀, hφ₀, -⟩ := GlobalTheory.PowFibre.exists_pow_pullback pH pQ hψ'
  obtain ⟨genH, hgenH, -⟩ := grpPullback_iso (isGrpPullback_pullback H (jK W)) hφ₀
  obtain ⟨L₁, -⟩ := GlobalTheory.abelianSchemeLaws_all
  have hE : ∃ E : SplitExt (Sp (ResidueField W)), E.IsGt ((Over.pullback (spMap (residue W))).obj H) := hsplit
  obtain ⟨s, -⟩ := GlobalTheory.ZH.exists_setting_of_hypS L₁ GlobalTheory.homExtension_semiAbelian_dvr_unconditional W hWc Q H hH hE
    hS genH hgenH
  obtain ⟨D, U, -, -, hU⟩ := GlobalTheory.uniformisation_dvr_unconditional W Q H s
  obtain ⟨i₀, hi₀, -⟩ := huG G (fun _ => 𝟙 G)
  refine ⟨W, inferInstance, inferInstance, inferInstance, io, algebraMap W F, D, Q, H, inferInstance, inferInstance, U,
    (Over.pullback (spMap io)).map i₀, pH.pr, ⟨hWd, hWc, inferInstance⟩, RingHom.finite_algebraMap.2 hWf, hio,
    Subtype.val_injective, fun v => ?_, hH, hU, pH.hom, ?_, fun T x y h => Fan.IsLimit.hom_ext pH.lim _ _ h⟩
  · exact IsScalarTower.algebraMap_apply V (FractionRing V) F v
  · show (Over.pullback (spMap io)).map i₀ ≫ (Over.pullback (spMap io)).map (prG 0) = _
    rw [← CategoryTheory.Functor.map_comp, hi₀ 0, CategoryTheory.Functor.map_id]

end GlobalTheory.SplitPowEight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationExtensionLocalDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degeneration_extension_local_domain : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ ψ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) ψ → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (io : V →+* W) (em : W →+* AlgebraicClosure (FractionRing V)) (D : DegData W (maximalIdeal W)) (Q : PolAV (Sp (FractionRing W))) (H : Over (Sp W)) (_ : GrpObj H) (_ : IsCommMonObj H) (U : Unif (maximalIdeal W) D Q H) (i : (Over.pullback (spMap io)).obj G ⟶ H) (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), GlobalTheory.LN.CDvr W ∧ io.Finite ∧ Function.Injective io ∧ Function.Injective em ∧ (∀ v, em (io v) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ IsSemiAbelian H ∧ GlobalTheory.LN.ToATotal U.toUnifPre ∧ (∀ k, IsMonHom (r k)) ∧ i ≫ r 0 = 𝟙 _ ∧ ∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y := by
  first | exact @GlobalTheory.SplitPowEight.exists_unif_pow8 | exact GlobalTheory.SplitPowEight.exists_unif_pow8 | (intros; apply GlobalTheory.SplitPowEight.exists_unif_pow8 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedTorsionTransferJointlyMonicHoms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedTorsionTransferJointlyMonicHoms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TorsionTransfer

theorem pow_left_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (x' : Over.mk b ⟶ G) (hx : x.left = x'.left) (m : ℕ) :
    (x ^ m).left = (x' ^ m).left := by
  subst h
  rw [Over.OverMorphism.ext hx]

set_option synthInstance.maxHeartbeats 400000 in
theorem fixed_of_jointlyMonic : ∀ (V W : Type) [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (io : V →+* W) (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra (FractionRing W) F], (∀ v, algebraMap (FractionRing W) F (algebraMap W _ (io v)) = algebraMap (FractionRing V) F (algebraMap V _ v)) → ∀ (G : Over (Sp V)) [GrpObj G] (H : Over (Sp W)) [GrpObj H] (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), (∀ k, IsMonHom (r k)) → (∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y) → ∀ σ : F ≃+* F, (∀ w : W, σ (algebraMap (FractionRing W) F (algebraMap W _ w)) = algebraMap (FractionRing W) F (algebraMap W _ w)) → ∀ m : ℕ, (∀ y : TF (R := V) F ⟶ G, y ^ m = 1 → spMap σ.toRingHom ≫ y.left = y.left) → ∀ x : TF (R := W) F ⟶ H, x ^ m = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro V W _ _ _ _ io F _ _ _ hF G _ H _ r hr hmono σ hσ m hfix x hx
  have hT : spMap σ.toRingHom ≫ (TF (R := W) F).hom = (TF (R := W) F).hom := by
    show Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp]
    congr 1
    ext w
    exact hσ w
  have hV : (TF (R := W) F).hom ≫ spMap io = (TF (R := V) F).hom := by
    show (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp]
    congr 1
    ext v
    exact hF v
  have hpb := isGrpPullback_pullback G (spMap io)
  let x' : TF (R := W) F ⟶ H := Over.homMk (spMap σ.toRingHom ≫ x.left) (by
    rw [Category.assoc, Over.w x]; exact hT)
  have key : ∀ k, x' ≫ r k = x ≫ r k := by
    intro k
    have hk := hr k
    let z := x ≫ r k
    have hs : z.left ≫ pullback.snd G.hom (spMap io) = (TF (R := W) F).hom := Over.w z
    let y : TF (R := V) F ⟶ G := Over.homMk (z.left ≫ pullback.fst G.hom (spMap io)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hs]; exact hV)
    let ρ : (TF (R := W) F ⟶ H) →* (TF (R := W) F ⟶ (Over.pullback (spMap io)).obj G) :=
      MonoidHom.mk' (fun u => u ≫ r k) fun u v => MonObj.mul_comp u v (r k)
    have hzm : z ^ m = 1 := by
      have e := map_pow ρ x m
      rw [hx, map_one] at e
      exact e.symm
    have hym : y ^ m = 1 := by
      apply Over.OverMorphism.ext
      have e1 := pow_left_congr hV.symm y (pushHom hpb _ z) rfl m
      rw [← map_pow, hzm, map_one] at e1
      have e0 := pow_left_congr hV.symm y (pushHom hpb _ z) rfl 0
      simp only [pow_zero] at e0
      rw [e1, e0]
    have hfy := hfix y hym
    apply Over.OverMorphism.ext
    show (spMap σ.toRingHom ≫ x.left) ≫ (r k).left = x.left ≫ (r k).left
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      exact hfy
    · rw [Category.assoc, Category.assoc]
      change spMap σ.toRingHom ≫ z.left ≫ _ = z.left ≫ _
      rw [hs, hT]
  exact congrArg (fun u => u.left) (hmono _ x' x key)

end GlobalTheory.TorsionTransfer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedTorsionTransferJointlyMonicHomsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedTorsion_transfer_jointlyMonic_homs : ∀ (V W : Type) [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (io : V →+* W) (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra (FractionRing W) F], (∀ v, algebraMap (FractionRing W) F (algebraMap W _ (io v)) = algebraMap (FractionRing V) F (algebraMap V _ v)) → ∀ (G : Over (Sp V)) [GrpObj G] (H : Over (Sp W)) [GrpObj H] (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), (∀ k, IsMonHom (r k)) → (∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y) → ∀ σ : F ≃+* F, (∀ w : W, σ (algebraMap (FractionRing W) F (algebraMap W _ w)) = algebraMap (FractionRing W) F (algebraMap W _ w)) → ∀ m : ℕ, (∀ y : TF (R := V) F ⟶ G, y ^ m = 1 → spMap σ.toRingHom ≫ y.left = y.left) → ∀ x : TF (R := W) F ⟶ H, x ^ m = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  first | exact @GlobalTheory.TorsionTransfer.fixed_of_jointlyMonic | exact GlobalTheory.TorsionTransfer.fixed_of_jointlyMonic | (intros; apply GlobalTheory.TorsionTransfer.fixed_of_jointlyMonic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrAlgClosureOverFiniteDvrExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationLeCardOfSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationLeCardOfSpan
namespace GlobalTheory

theorem eq_zero_of_sum_eq_zero_of_unit_mul_pow {R : Type*} [CommRing R] [IsDomain R] {ϖ : R}
    (hϖ : Irreducible ϖ) {e : ℕ} (c : Fin e → R)
    (hc : ∀ i, c i ≠ 0 → ∃ (n : ℕ) (w : R), IsUnit w ∧ c i = w * ϖ ^ (i.val + e * n))
    (hsum : ∑ i, c i = 0) : ∀ i, c i = 0 := by
  classical
  by_contra hne
  push_neg at hne
  choose! n w hw hcw using hc
  set S := Finset.univ.filter (fun i => c i ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [hS, hi]⟩
  obtain ⟨i0, hi0S, hmin⟩ := S.exists_min_image (fun i => i.val + e * n i) hSne
  have hi0 : c i0 ≠ 0 := (Finset.mem_filter.1 hi0S).2
  have hdvd : ∀ i ∈ Finset.univ.erase i0, ϖ ^ (i0.val + e * n i0 + 1) ∣ c i := by
    intro i hi
    have hii0 : i ≠ i0 := Finset.ne_of_mem_erase hi
    by_cases hci : c i = 0
    · rw [hci]; exact dvd_zero _
    · have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hci⟩
      have hle : i0.val + e * n i0 ≤ i.val + e * n i := hmin i hiS
      have hne' : i.val + e * n i ≠ i0.val + e * n i0 := by
        intro heq
        apply hii0
        apply Fin.ext
        have h1 : (i.val + e * n i) % e = i.val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
        have h2 : (i0.val + e * n i0) % e = i0.val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i0.isLt]
        rw [← h1, ← h2, heq]
      rw [hcw i hci]
      exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
  obtain ⟨X, hX⟩ := Finset.dvd_sum hdvd
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), hX, hcw i0 hi0] at hsum
  have h0 : ϖ ^ (i0.val + e * n i0) * (w i0 + ϖ * X) = 0 := by rw [← hsum]; ring
  have h1 : w i0 + ϖ * X = 0 :=
    (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hϖ.ne_zero)
  have h2 : ϖ ∣ w i0 := ⟨-X, by linear_combination h1⟩
  exact hϖ.not_isUnit (isUnit_of_dvd_unit h2 (hw i0 hi0))

theorem ramification_le_card_of_span :
    ∀ (F : Type) [Field F] (T' T'' : Subring F), IsDiscreteValuationRing T' →
      IsDiscreteValuationRing T'' → ∀ (h : T' ≤ T''),
      (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) → ∀ (s : Finset F),
      (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) →
      ∀ π : T', Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ ∃ e : ℕ, 1 ≤ e ∧ e ≤ s.card ∧
        Associated (Subring.inclusion h π) (ϖ ^ e) := by
  intro F _ T' T'' h1 h2 h hdom s hspan π hπ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T''
  have hπ0 : Subring.inclusion h π ≠ 0 := by
    intro h0
    apply hπ.ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h0
    simpa using this
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hπ0 hϖ
  refine ⟨ϖ, hϖ, e, ?_, ?_, he⟩
  · rcases Nat.eq_zero_or_pos e with rfl | hpos
    · exfalso
      rw [pow_zero] at he
      have hu : IsUnit (Subring.inclusion h π) := he.isUnit_iff.2 isUnit_one
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      obtain ⟨z, hzT', hz⟩ := hdom (π : F) π.2
        ⟨(y : F), y.2, by simpa using congrArg Subtype.val hy⟩
      exact hπ.not_isUnit (isUnit_iff_exists_inv.2 ⟨⟨z, hzT'⟩, Subtype.ext hz⟩)
    · exact hpos
  ·
    choose d hdT hd0 hdspan using
      fun i : Fin e => hspan ((ϖ ^ (i : ℕ) : T'') : F) (ϖ ^ (i : ℕ)).2
    set D : F := ∏ i, d i with hDdef
    have hDT : D ∈ T' := Subring.prod_mem _ (fun i _ => hdT i)
    have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => hd0 i)
    let f : Fin e → F := fun i => D * ((ϖ ^ (i : ℕ) : T'') : F)
    have hfspan : ∀ i, f i ∈ Submodule.span T' (s : Set F) := by
      intro i
      have hmem : (∏ j ∈ Finset.univ.erase i, d j) ∈ T' :=
        Subring.prod_mem _ (fun j _ => hdT j)
      have := Submodule.smul_mem (Submodule.span T' (s : Set F))
        (⟨∏ j ∈ Finset.univ.erase i, d j, hmem⟩ : T') (hdspan i)
      rw [Subring.smul_def] at this
      have heq : f i = (∏ j ∈ Finset.univ.erase i, d j) * (d i * ((ϖ ^ (i : ℕ) : T'') : F)) := by
        simp only [f, hDdef]
        rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)]
        ring
      rw [heq]
      exact this
    have hli : LinearIndependent T' f := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      obtain ⟨v, hv⟩ := he.symm
      let c : Fin e → T'' := fun i =>
        Subring.inclusion h (g i * ⟨D, hDT⟩) * ϖ ^ (i : ℕ)
      have hcsum : ∑ i, c i = 0 := by
        apply Subtype.ext
        have hcs : ((∑ i, c i : T'') : F) = ∑ i, g i • f i := by
          simp [c, f, Subring.smul_def, mul_assoc]
        rw [hcs, hg]
        rfl
      have hc : ∀ i, c i ≠ 0 → ∃ (n : ℕ) (w : T''), IsUnit w ∧ c i = w * ϖ ^ (i.val + e * n) := by
        intro i hci
        have ha : g i * ⟨D, hDT⟩ ≠ 0 := by
          intro h0; apply hci; simp only [c, h0, map_zero, zero_mul]
        obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
        refine ⟨m, Subring.inclusion h (u : T') * (v : T'') ^ m,
          (u.isUnit.map (Subring.inclusion h)).mul (v.isUnit.pow m), ?_⟩
        simp only [c]
        rw [hu, map_mul, map_pow, ← hv]
        ring
      have hc0 := eq_zero_of_sum_eq_zero_of_unit_mul_pow hϖ c hc hcsum
      intro i
      have := hc0 i
      simp only [c, mul_eq_zero, pow_eq_zero_iff', hϖ.ne_zero, false_and, or_false] at this
      have h3 : g i * ⟨D, hDT⟩ = 0 := by
        apply Subtype.ext
        have := congrArg Subtype.val this
        simpa using this
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h4
      · exact absurd (congrArg Subtype.val h4) hD0
    let f' : Fin e → Submodule.span T' (s : Set F) := fun i => ⟨f i, hfspan i⟩
    have hli' : LinearIndependent T' f' :=
      LinearIndependent.of_comp (Submodule.span T' (s : Set F)).subtype hli
    have hcard := hli'.cardinal_le_rank.trans (rank_span_finset_le s)
    simpa using hcard

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationLeCardOfSpanStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_pow_associated_le_card_of_span : ∀ (F : Type) [Field F] (T' T'' : Subring F), IsDiscreteValuationRing T' → IsDiscreteValuationRing T'' → ∀ (h : T' ≤ T''), (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) → ∀ (s : Finset F), (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) → ∀ π : T', Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ ∃ e : ℕ, 1 ≤ e ∧ e ≤ s.card ∧ Associated (Subring.inclusion h π) (ϖ ^ e) := by
  first | exact @GlobalTheory.ramification_le_card_of_span | exact GlobalTheory.ramification_le_card_of_span | (intros; apply GlobalTheory.ramification_le_card_of_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominatingDvrContainingFinset
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominatingDvrContainingFinset
open IsLocalRing

namespace GlobalTheory.DomDVR


set_option maxHeartbeats 1000000 in
theorem exists_dominating_dvr : ∀ (F : Type) [Field F] [CharZero F] (T' : Subring F), IsDiscreteValuationRing T' → ∀ (s : Finset F), (1 : F) ∈ Submodule.span T' (s : Set F) → (∀ x ∈ s, ∀ y ∈ s, x * y ∈ Submodule.span T' (s : Set F)) → ∃ T'' : Subring F, IsDiscreteValuationRing T'' ∧ T' ≤ T'' ∧ (∀ x ∈ s, x ∈ T'') ∧ (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) ∧ (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) := by
  intro F _ _ T' hT s h1 hmul
  classical
  haveI := hT
  set A := Submodule.span T' (s : Set F) with hA
  have hAmul : ∀ x y, x ∈ A → y ∈ A → x * y ∈ A := by
    intro x y hx hy
    have : A * A ≤ A := by
      rw [hA, Submodule.span_mul_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact hmul a ha b hb
    exact this (Submodule.mul_mem_mul hx hy)
  have hsm : ∀ d ∈ T', ∀ a ∈ A, d * a ∈ A := fun d hd a ha => A.smul_mem ⟨d, hd⟩ ha
  let Asub : Subalgebra T' F := A.toSubalgebra h1 hAmul
  have hint : ∀ x ∈ s, IsIntegral T' x := fun x hx =>
    IsIntegral.of_mem_of_fg Asub (Submodule.fg_span s.finite_toSet) x (Submodule.subset_span hx)
  let K := FractionRing T'
  have hι : Function.Injective (T'.subtype) := Subtype.val_injective
  letI : Algebra K F := (IsFractionRing.lift (K := K) hι).toAlgebra
  haveI : IsScalarTower T' K F :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsFractionRing.lift_algebraMap (K := K) hι x).symm)
  have hintK : ∀ x ∈ (s : Set F), IsIntegral K x := fun x hx => (hint x hx).tower_top
  let L := IntermediateField.adjoin K (s : Set F)
  haveI : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin hintK
  haveI : CharZero K := (algebraMap K F).charZero
  haveI : Algebra.IsSeparable K L := inferInstance
  let C := integralClosure T' L
  haveI : IsDedekindDomain C := IsIntegralClosure.isDedekindDomain T' K L C

  have hLF : ∀ a : T', ((algebraMap T' L a : L) : F) = a := by
    intro a
    rw [IsScalarTower.algebraMap_apply T' K L]
    show algebraMap K F (algebraMap T' K a) = a
    exact IsFractionRing.lift_algebraMap (K := K) hι a
  have hcoe : ∀ a : T', (((algebraMap T' C a : C) : L) : F) = a := by
    intro a
    rw [← hLF a, IsScalarTower.algebraMap_apply T' C L]
    rfl
  have hinjC : Function.Injective (algebraMap T' C) := fun a b h => Subtype.val_injective (by
    have := congrArg (fun c : C => ((c : L) : F)) h
    simpa only [hcoe] using this)
  obtain ⟨P, hPmax, hPm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := C) (maximalIdeal T')
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinjC]; exact bot_le)
  haveI : P.IsPrime := hPmax.isPrime
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    apply IsDiscreteValuationRing.not_a_field T'
    rw [← hPm, (show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinjC)]
  let Loc := Localization.AtPrime P
  haveI : IsDiscreteValuationRing Loc :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hPbot Loc
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap C L y) := fun y =>
    isUnit_iff_ne_zero.2 fun h => y.2 (by
      rw [show (y : C) = 0 from Subtype.ext (by simpa using h)]; exact P.zero_mem)
  let ψ : Loc →+* L := IsLocalization.lift (M := P.primeCompl) hunit
  have hψ : Function.Injective ψ := (IsLocalization.lift_injective_iff hunit).2 fun x y =>
    ⟨fun h => by rw [IsLocalization.injective Loc P.primeCompl_le_nonZeroDivisors h], fun h => by rw [Subtype.val_injective h]⟩
  let φ : Loc →+* F := (algebraMap L F).comp ψ
  have hφ : Function.Injective φ := fun a b h => hψ ((algebraMap L F).injective h)
  have hφc : ∀ c : C, φ (algebraMap C Loc c) = ((c : L) : F) := by
    intro c
    show ((ψ (algebraMap C Loc c) : L) : F) = _
    rw [IsLocalization.lift_eq]
    rfl
  let T'' := φ.range
  let e : Loc ≃+* T'' := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun a b h => hφ (by simpa only [RingHom.coe_rangeRestrict] using congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  refine ⟨T'', IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact RingHom.mem_range.2 ⟨algebraMap C Loc (algebraMap T' C ⟨x, hx⟩), by rw [hφc, hcoe]⟩
  · intro x hx
    have hxL : x ∈ L := IntermediateField.subset_adjoin K _ hx
    have hxC : (⟨x, hxL⟩ : L) ∈ C := by
      rw [mem_integralClosure_iff]
      let f : L →ₐ[T'] F := { toRingHom := algebraMap L F, commutes' := fun a => hLF a }
      exact (isIntegral_algHom_iff f (algebraMap L F).injective).1 (hint x hx)
    exact RingHom.mem_range.2 ⟨algebraMap C Loc ⟨⟨x, hxL⟩, hxC⟩, by rw [hφc]⟩
  · rintro x hx ⟨y, hy, hxy⟩
    by_contra hne
    have hnu : (⟨x, hx⟩ : T') ∈ maximalIdeal T' := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      exact hne ⟨b, b.2, congrArg Subtype.val hb⟩
    have hP : algebraMap T' C ⟨x, hx⟩ ∈ P := by
      rw [← hPm] at hnu; exact hnu
    have hmax : algebraMap C Loc (algebraMap T' C ⟨x, hx⟩) ∈ maximalIdeal Loc :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff Loc P _).2 hP
    obtain ⟨z, rfl⟩ := RingHom.mem_range.1 hy
    apply (IsLocalRing.mem_maximalIdeal _).1 hmax
    refine isUnit_iff_exists_inv.2 ⟨z, hφ ?_⟩
    rw [map_mul, map_one, hφc, hcoe]; exact hxy
  · let M : Subalgebra K F :=
      { carrier := {y | ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ A}
        mul_mem' := by
          rintro a b ⟨d1, hd1, hd1', ha⟩ ⟨d2, hd2, hd2', hb⟩
          exact ⟨d1 * d2, T'.mul_mem hd1 hd2, mul_ne_zero hd1' hd2', by
            rw [show d1 * d2 * (a * b) = (d1 * a) * (d2 * b) by ring]; exact hAmul _ _ ha hb⟩
        add_mem' := by
          rintro a b ⟨d1, hd1, hd1', ha⟩ ⟨d2, hd2, hd2', hb⟩
          exact ⟨d1 * d2, T'.mul_mem hd1 hd2, mul_ne_zero hd1' hd2', by
            rw [show d1 * d2 * (a + b) = d2 * (d1 * a) + d1 * (d2 * b) by ring]
            exact A.add_mem (hsm _ hd2 _ ha) (hsm _ hd1 _ hb)⟩
        algebraMap_mem' := by
          intro k
          obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors T') k
          have hb : ((b : T') : F) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero b (Subtype.ext h)
          refine ⟨(b : T'), (b : T').2, hb, ?_⟩
          have e1 : algebraMap K F (IsLocalization.mk' K a b) = (a : F) / ((b : T') : F) :=
            IsFractionRing.lift_mk' hι a b
          have e2 : ((b : T') : F) * ((a : F) / ((b : T') : F)) = a := by field_simp
          rw [e1, e2]
          simpa using hsm _ a.2 _ h1 }
    have hLM : ∀ y ∈ L, y ∈ M := by
      intro y hy
      have e := IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := K) (S := (s : Set F))
        (fun x hx => (hintK x hx).isAlgebraic)
      have hy' : y ∈ Algebra.adjoin K (s : Set F) := by rw [← e]; exact hy
      refine (Algebra.adjoin_le ?_ : Algebra.adjoin K (s : Set F) ≤ M) hy'
      intro x hx
      exact ⟨1, T'.one_mem, one_ne_zero, by rw [one_mul]; exact Submodule.subset_span hx⟩
    intro y hy
    obtain ⟨z, rfl⟩ := RingHom.mem_range.1 hy
    exact hLM _ (ψ z).2
end GlobalTheory.DomDVR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominatingDvrContainingFinsetStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominating_dvr_containing_finset : ∀ (F : Type) [Field F] [CharZero F] (T' : Subring F), IsDiscreteValuationRing T' → ∀ (s : Finset F), (1 : F) ∈ Submodule.span T' (s : Set F) → (∀ x ∈ s, ∀ y ∈ s, x * y ∈ Submodule.span T' (s : Set F)) → ∃ T'' : Subring F, IsDiscreteValuationRing T'' ∧ T' ≤ T'' ∧ (∀ x ∈ s, x ∈ T'') ∧ (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) ∧ (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) := by
  first | exact @GlobalTheory.DomDVR.exists_dominating_dvr | exact GlobalTheory.DomDVR.exists_dominating_dvr | (intros; apply GlobalTheory.DomDVR.exists_dominating_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrAlgClosureOverFiniteDvrExtension
open IsLocalRing

namespace GlobalTheory

theorem exists_dvr_over_finite_ext : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr V → GlobalTheory.LN.CDvr W → ∀ io : V →+* W, io.Finite → Function.Injective io → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] [Algebra (FractionRing W) F], (∀ v, algebraMap (FractionRing W) F (algebraMap W _ (io v)) = algebraMap (FractionRing V) F (algebraMap V _ v)) → ∃ N : ℕ, ∀ (T' : Subring F) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v, (f v : F) = algebraMap (FractionRing V) F (algebraMap V _ v)) → (∀ π, Irreducible π → Irreducible (f π)) → ∃ (T'' : Subring F) (_ : IsDiscreteValuationRing T'') (g : W →+* T'') (e : ℕ), T' ≤ T'' ∧ (∀ w, (g w : F) = algebraMap (FractionRing W) F (algebraMap W _ w)) ∧ 1 ≤ e ∧ e ≤ N ∧ ∀ π, Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ Associated (g π) (ϖ ^ e) := by
  classical
  intro V W _ _ _ _ _ _ hV hW io hio hinj F _ _ _ _ hcomp
  obtain ⟨hVd, -, hV0⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  obtain ⟨hWd, -, -⟩ := (GlobalTheory.LN.cDvr_iff W).1 hW
  set φV : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V _) with hφV
  set φW : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W _) with hφW
  have hφWinj : Function.Injective φW :=
    (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _)
  have hφVinj : Function.Injective φV :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _)
  haveI : CharZero F := (RingHom.charZero_iff hφVinj).1 hV0
  have hc : ∀ v, φW (io v) = φV v := hcomp
  letI := io.toAlgebra
  haveI : Module.Finite V W := hio
  obtain ⟨n, gens, hspan⟩ := Module.Finite.exists_fin (R := V) (M := W)
  refine ⟨n, ?_⟩
  intro T' hT' f hf hirr
  set s : Finset F := Finset.univ.image (fun i => φW (gens i)) with hs
  have hcard : s.card ≤ n := by
    calc s.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  have K1 : ∀ w : W, φW w ∈ Submodule.span T' (s : Set F) := by
    intro w
    have hw : w ∈ Submodule.span V (Set.range gens) := by rw [hspan]; trivial
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span (by simp [hs])
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul v x _ hx =>
      have : φW (v • x) = (f v) • φW x := by
        rw [Algebra.smul_def, map_mul, Subring.smul_def, smul_eq_mul, hf]
        exact congrArg (· * φW x) (hc v)
      rw [this]; exact Submodule.smul_mem _ _ hx
  have h1 : (1 : F) ∈ Submodule.span T' (s : Set F) := by simpa using K1 1
  have hmul : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ Submodule.span T' (s : Set F) := by
    intro x hx y hy
    simp only [hs, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx; obtain ⟨j, rfl⟩ := hy
    rw [← map_mul]; exact K1 _
  obtain ⟨T'', hT'', hle, hsT, hdom, hden⟩ := GlobalTheory.T.exists_dominating_dvr_containing_finset F T' hT' s h1 hmul
  have K2 : ∀ x ∈ Submodule.span T' (s : Set F), x ∈ T'' := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hsT x hx
    | zero => exact T''.zero_mem
    | add x y _ _ hx hy => exact T''.add_mem hx hy
    | smul t x _ hx => rw [Subring.smul_def, smul_eq_mul]; exact T''.mul_mem (hle t.2) hx
  let g : W →+* T'' := φW.codRestrict T'' (fun w => K2 _ (K1 w))
  have hg : ∀ w, (g w : F) = φW w := fun w => rfl
  have hginj : Function.Injective g := fun a b h => hφWinj (by simpa [hg] using congrArg Subtype.val h)
  haveI := hT''
  obtain ⟨πV, hπV⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hfπ := hirr πV hπV
  obtain ⟨ϖ, hϖ, e', he1, he2, hassoc⟩ := GlobalTheory.T.exists_irreducible_pow_associated_le_card_of_span F T' T'' hT' hT'' hle hdom s hden (f πV) hfπ
  obtain ⟨πW, hπW⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hioπ : io πV ≠ 0 := fun h => hπV.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.associated_pow_irreducible hioπ hπW
  have hgπ : g πW ≠ 0 := fun h => hπW.ne_zero (hginj (by rw [h, map_zero]))
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hgπ hϖ
  have hgio : g (io πV) = Subring.inclusion hle (f πV) := by
    apply Subtype.ext
    rw [hg, hc]
    exact (hf πV).symm
  have hA : Associated (ϖ ^ e') (ϖ ^ (k * a)) := by
    have h2 : Associated (g (io πV)) ((g πW) ^ a) := by
      rw [← map_pow]; exact ha.map g
    rw [hgio] at h2
    rw [pow_mul]
    exact hassoc.symm.trans (h2.trans hk.pow_pow)
  have hka : e' = k * a := by
    apply le_antisymm
    · exact (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 hA.dvd
    · exact (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 hA.symm.dvd
  have hk0 : k ≠ 0 := by rintro rfl; simp at hka; omega
  have ha0 : a ≠ 0 := by rintro rfl; simp at hka; omega
  refine ⟨T'', hT'', g, k, hle, fun w => rfl, Nat.one_le_iff_ne_zero.2 hk0, ?_, ?_⟩
  · calc k ≤ k * a := Nat.le_mul_of_pos_right k (Nat.pos_of_ne_zero ha0)
      _ = e' := hka.symm
      _ ≤ s.card := he2
      _ ≤ n := hcard
  · intro π hπ
    exact ⟨ϖ, hϖ, ((IsDiscreteValuationRing.associated_of_irreducible W hπ hπW).map g).trans hk⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrAlgClosureOverFiniteDvrExtensionStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_algClosure_over_finite_dvr_extension : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr V → GlobalTheory.LN.CDvr W → ∀ io : V →+* W, io.Finite → Function.Injective io → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] [Algebra (FractionRing W) F], (∀ v, algebraMap (FractionRing W) F (algebraMap W _ (io v)) = algebraMap (FractionRing V) F (algebraMap V _ v)) → ∃ N : ℕ, ∀ (T' : Subring F) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v, (f v : F) = algebraMap (FractionRing V) F (algebraMap V _ v)) → (∀ π, Irreducible π → Irreducible (f π)) → ∃ (T'' : Subring F) (_ : IsDiscreteValuationRing T'') (g : W →+* T'') (e : ℕ), T' ≤ T'' ∧ (∀ w, (g w : F) = algebraMap (FractionRing W) F (algebraMap W _ w)) ∧ 1 ≤ e ∧ e ≤ N ∧ ∀ π, Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ Associated (g π) (ϖ ^ e) := by
  first | exact @GlobalTheory.exists_dvr_over_finite_ext | exact GlobalTheory.exists_dvr_over_finite_ext | (intros; apply GlobalTheory.exists_dvr_over_finite_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointMemAbelianLocusOfFixedTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FixedTorsionTrait

theorem abLocus_of_retract {S : Scheme.{0}} (G H : Over S) (i : G ⟶ H) (r : H ⟶ G) (h : i ≫ r = 𝟙 G) :
    ∀ x ∈ abLocus H, x ∈ abLocus G := by
  intro x hx K _ _ t ht
  have hp : IsProper ((Over.pullback t).obj H).hom := hx K t ht
  exact GlobalTheory.Mum.RetractGeneric.isProper_of_retract ((Over.pullback t).map i) ((Over.pullback t).map r)
    (by rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]) hp

theorem closedPoint_mem_abLocus_of_fixedTorsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → (∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left) → closedPoint V ∈ abLocus ((Over.pullback (spMap φ)).obj G) := by
  intro R _ _ _ hR D A G _ _ hG U V _ _ _ φ hV hφ n hn hu H
  obtain ⟨l₁, l₂, -⟩ := GlobalTheory.firstFiveLaws
  have hG' : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := IsSemiAbelian.pullback (spMap φ) G hG
  have : IsCommMonObj ((Over.pullback (spMap φ)).obj G) := Functor.isCommMonObj_obj
  obtain ⟨A', ψ, hψ⟩ := GlobalTheory.UnifProperOpen.exists_polGeneric_pullback R A G U.gen U.gen_hom V φ hφ
  obtain ⟨W, _, _, _, io, em, D₈, Q, H₈, _, _, U₈, i, r, hW, hfin, hinj, hem, hc, hH₈, htot, hr, hir, hmono⟩ :=
    GlobalTheory.T.degeneration_extension_local_domain V hV A' _ hG' ψ hψ
  have hem' : ∀ w : W, w ≠ 0 → IsUnit (em w) := fun w hw =>
    IsUnit.mk0 _ ((map_ne_zero_iff em hem).2 hw)
  letI : Algebra (FractionRing W) (AlgebraicClosure (FractionRing V)) :=
    (IsFractionRing.lift (A := W) (K := FractionRing W) (g := em) hem).toAlgebra
  have hlift : ∀ w : W, algebraMap (FractionRing W) (AlgebraicClosure (FractionRing V)) (algebraMap W _ w) = em w :=
    fun w => IsFractionRing.lift_algebraMap _ _
  have hcompat : ∀ v, algebraMap (FractionRing W) (AlgebraicClosure (FractionRing V)) (algebraMap W _ (io v)) =
      algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v) := fun v => (hlift _).trans (hc v)
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_dvr_algClosure_over_finite_dvr_extension V W hV hW io hfin hinj (AlgebraicClosure (FractionRing V)) hcompat
  have hsub : Subsingleton D₈.toPre.X := by
    refine GlobalTheory.T.characterGroup_subsingleton_of_bounded_ramification W hW D₈ Q H₈ hH₈ U₈ htot (AlgebraicClosure (FractionRing V)) n N hn fun j => ?_
    obtain ⟨T', hT', f, hf, hirr, hfix⟩ := H j
    obtain ⟨T'', hT'', g, e, hle, hg, he1, heN, hπ⟩ := hN T' hT' f hf hirr
    refine ⟨T'', hT'', g, e, hg, he1, heN, hπ, fun σ hσ x hx => ?_⟩
    exact GlobalTheory.T.fixedTorsion_transfer_jointlyMonic_homs V W io _ hcompat _ H₈ r hr hmono σ (fun w => hσ _ (by rw [← hg w]; exact (g w).2)) (n ^ j)
      (fun y hy => hfix σ (fun z hz => hσ z (hle hz)) y hy) x hx
  have := hW.1
  have := hW.2.2
  have hab : IsAbelianScheme H₈ := GlobalTheory.isAbelianScheme_of_unif_of_subsingleton l₁ l₂ W hW.2.1 D₈ Q H₈ hH₈ U₈ hsub
  have h₈ : closedPoint W ∈ abLocus H₈ := fun K _ _ t _ => by
    have := hab.proper
    infer_instance
  have h₁ : closedPoint W ∈ abLocus ((Over.pullback (spMap io)).obj ((Over.pullback (spMap φ)).obj G)) :=
    abLocus_of_retract _ H₈ i (r 0) hir _ h₈
  have h₂ := (abLocus_pullback (G' := (Over.pullback (spMap io)).obj ((Over.pullback (spMap φ)).obj G)) abLocusOne hG'
    (IsPullback.of_hasPullback ((Over.pullback (spMap φ)).obj G).hom (spMap io)) (closedPoint W)).2 h₁
  letI : Algebra V W := io.toAlgebra
  have : Algebra.IsIntegral V W := ⟨fun w => hfin.to_isIntegral w⟩
  have hm : (maximalIdeal W).comap io = maximalIdeal V :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := V) (algebraMap _ _) hfin.to_isIntegral (maximalIdeal W))
  have : IsLocalHom io := ((IsLocalRing.local_hom_tfae io).out 5 1).1 hm
  have e : spMap io (closedPoint W) = closedPoint V := by
    have h : ⇑(spMap io) = PrimeSpectrum.comap io := by
      ext x : 1
      simp [spMap, Spec.map_base]
      rfl
    rw [h]
    exact IsLocalRing.comap_closedPoint io
  rw [← e]
  exact h₂

end GlobalTheory.FixedTorsionTrait

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointMemAbelianLocusOfFixedTorsionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedPoint_mem_abelianLocus_of_fixedTorsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → (∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left) → closedPoint V ∈ abLocus ((Over.pullback (spMap φ)).obj G) := by
  first | exact @GlobalTheory.FixedTorsionTrait.closedPoint_mem_abLocus_of_fixedTorsion | exact GlobalTheory.FixedTorsionTrait.closedPoint_mem_abLocus_of_fixedTorsion | (intros; apply GlobalTheory.FixedTorsionTrait.closedPoint_mem_abLocus_of_fixedTorsion <;> assumption)
end
