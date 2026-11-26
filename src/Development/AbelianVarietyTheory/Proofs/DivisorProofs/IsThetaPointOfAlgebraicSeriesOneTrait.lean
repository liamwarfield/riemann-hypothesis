module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeometricValuesIsoOfIdentificationDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationBirigidifiedPowerIsotropicSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPointOfAlgebraicSeriesOneTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPointOfAlgebraicSeriesOneTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.OneTraitTheta

open GlobalTheory GlobalTheory.Ex GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.ArcTransport GlobalTheory.ValuesPullIso GlobalTheory.LabTrans
open GlobalTheory.PsiEvenPull (proj)

theorem exists_values_iso (hL : Laws) {R R' : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') {F : Type} [Field F]
    [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (hF : Compat φ F) {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') : ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧
      ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' →
        IsPullGtF φ hD F g g' → I.Rel c' c := by
  let z : Sp F := IsLocalRing.closedPoint F
  obtain ⟨th', h₁, h₂⟩ := GeneratorPull.exists_generator_pull hL R R' φ D.P D'.P _ hD.w (pull_grp hD) hD.w_gen ν.th ν.th_gen
  obtain ⟨c, hc⟩ := ν'.th_gen th'
  obtain ⟨c', hc'⟩ := h₁ ν'.th
  have key : ∀ x : TF (R := R') F ⟶ D'.P.A, sval (Z := Sp F) ν.th (x.left ≫ proj hD) z ν.J =
      (om hD.w z ν.J ν'.J x.left).val * sval (Z := Sp F) th' x.left z ν'.J := fun x =>
    h₂ (Sp F) x.left z ν.J ν'.J (good ν z) (good ν' z)
  have k₁ := fun x : TF (R := R') F ⟶ D'.P.A =>
    IndivisibleSection.sval_of_secIsMul (p := D'.P.A.hom) hc (show Sp F ⟶ _ from x.left) z (good ν' z)
  have k₂ := fun x : TF (R := R') F ⟶ D'.P.A =>
    IndivisibleSection.sval_of_secIsMul (p := D'.P.A.hom) hc' (show Sp F ⟶ _ from x.left) z (good ν' z)
  by_cases h : c = 0
  · subst h
    refine exists_iso_of_th hD hL.globalFns hF ν ν' z 1 fun x => ?_
    have e₁ := k₁ x
    rw [GenSecField.cst_zero', zero_mul] at e₁
    have e₂ := k₂ x
    rw [e₁, mul_zero] at e₂
    exact ((key x).trans ((congrArg _ e₁).trans (mul_zero _))).trans ((congrArg _ e₂).trans (mul_zero _)).symm
  · let u : (FractionRing R')ˣ := Units.mk0 (algebraMap R' _ c) fun e =>
      h (IsFractionRing.injective R' (FractionRing R') (e.trans (map_zero _).symm))
    refine exists_iso_of_th hD hL.globalFns hF ν ν' z (TauTwist.unitAt (Z := Sp F) (jFK (R := R') F) z u) fun x => ?_
    refine ((key x).trans (congrArg _ (k₁ x))).trans ((_root_.mul_assoc _ _ _).symm.trans (congrArg₂ (· * ·) ?_ rfl))
    rw [Units.val_mul, TauTwist.unitAt_val]
    refine (_root_.mul_comm _ _).trans (congrArg₂ (· * ·) ?_ rfl)
    exact (congrArg (fun q => cst (Z := Sp F) q z c) (Over.w x)).trans
      (cst_comp (Z := Sp F) (jFK (R := R') F) (algebraMap R' (FractionRing R')) z c)

theorem exists_scalar {K C I : Type} [Field K] [Field C] (f : K →+* C) {v t : I → K} (s : Cˣ)
    (h : ∀ i, f (v i) = s * f (t i)) : ∃ c : K, c ≠ 0 ∧ ∀ i, v i = c * t i := by
  by_cases h₀ : ∀ i, t i = 0
  · exact ⟨1, one_ne_zero, fun i => f.injective (by rw [h, h₀]; simp)⟩
  · obtain ⟨i, hi⟩ := not_forall.1 h₀
    have hi' : f (t i) ≠ 0 := (map_ne_zero f).2 hi
    have e : f (v i / t i) = s := by rw [map_div₀, h, mul_div_cancel_right₀ _ hi']
    exact ⟨v i / t i, fun h₁ => s.ne_zero (by rw [← e, h₁, map_zero]), fun l => f.injective (by rw [map_mul, e, h])⟩

theorem isThetaPt_descend (hL : Laws) (hL₂ : Laws2) {S S' : Scheme.{0}} [IsLocallyNoetherian S] [IsLocallyNoetherian S']
    {P : PolAV S} {P' : PolAV S'} {f : S' ⟶ S} {a : P'.A.left ⟶ P.A.left} (hp : IsGrpPullback P'.A P.A f a)
    (hw : LBIso P'.L (P.L.pull a)) {K C : Type} [Field K] [Field C] [IsAlgClosed C] (em : K →+* C) (s : Sp K ⟶ S)
    (s' : Sp C ⟶ S') (hs : spMap em ≫ s = s' ≫ f) {m : ℕ} (hm : Odd m) (hmK : (m : K) ≠ 0) {I : Type}
    (x : I → (Over.mk s ⟶ P.A)) (x' : I → (Over.mk s' ⟶ P'.A)) (hx : ∀ i, (x' i).left ≫ a = spMap em ≫ (x i).left)
    (hk : ∀ i, x' i ^ m ^ 2 = 1) {w : I → C} (hw' : IsThetaPt P' m x' fun i => fnOf (w i)) {v : I → K} (c : Cˣ)
    (hv : ∀ i, em (v i) = c * w i) : IsThetaPt P m x fun i => fnOf (v i) := by
  have hmC : (m : C) ≠ 0 := by rw [← map_natCast em]; exact (map_ne_zero em).2 hmK
  let U : Over.mk (s' ≫ f) ⟶ Over.mk s := Over.homMk (spMap em) hs
  obtain ⟨e, he⟩ : ∃ e : (Over.mk s' ⟶ P'.A) ≃* (Over.mk (s' ≫ f) ⟶ P.A), ∀ y, (e y).left = y.left ≫ a :=
    LiePull.exists_pushEquiv hp (Over.mk s') _ rfl
  have hU : ∀ i, U ≫ x i = e (x' i) := fun i => Over.OverMorphism.ext ((hx i).symm.trans (he _).symm)
  have hkU : ∀ i, (U ≫ x i) ^ m ^ 2 = 1 := fun i => by rw [hU, ← map_pow, hk, map_one]
  have hkx : ∀ i, x i ^ m ^ 2 = 1 := fun i => by
    letI := em.toAlgebra
    haveI : Flat (spMap em) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact (inferInstance : Module.Flat K C)
    haveI : Surjective (spMap em) := ⟨fun p => ⟨(⊥ : PrimeSpectrum C), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
    haveI : Epi (spMap em) := Flat.epi_of_flat_of_surjective (spMap em)
    have E : U ≫ (x i ^ m ^ 2) = U ≫ 1 := by rw [MonObj.comp_pow, hkU, MonObj.comp_one]
    exact Over.OverMorphism.ext ((cancel_epi (spMap em)).1 (congrArg (fun q => q.left) E))
  obtain ⟨t, ht⟩ := Specialise.exists_isThetaPt_local hL hL₂ P s hm (IsUnit.mk0 _ hmK) x hkx
  have T₁ := Specialise.isThetaPt_map hL₂ P em hs ht
  have T₂ := ((CoordSep.coord_exists_unique_separate hL C _ P (s' ≫ f) m hm hmC I (fun i => U ≫ x i) hkU).2.2.1
    fun i => em (t i)).1 T₁
  let τ : (Over.mk s').left ⟶ (Over.mk (s' ≫ f)).left := 𝟙 (Sp C)
  have : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp C)))
  have T₃ : IsCoordPt P' m x' 1 fun i => fnOf (em (t i)) :=
    FullExtend.isCoordPt_move τ hp hw τ (𝟙 _) (Category.comp_id _) (Category.id_comp _) (fun th h s => by
      obtain ⟨c, hc⟩ := h s
      have e := VVRank.pullM_id P.A P.isLB 1 (SecM.ofSec P.A th)
      exact ⟨c, fun j => (hc j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e).symm)⟩)
      (fun i => (Category.id_comp _).trans (hx i).symm) hk (z := 1)
      ((Category.id_comp _).trans (by rw [← he, map_one])) T₂
  obtain ⟨-, h₂, h₃, -⟩ := CoordSep.coord_exists_unique_separate hL C _ P' s' m hm hmC I x' hk
  obtain ⟨d, hd⟩ := (h₂ 1 _ w T₃).1 ((h₃ w).1 hw')
  obtain ⟨c', hc', hv'⟩ := exists_scalar em (v := v) (t := t) (c * d) fun i => by
    rw [hv, hd, Units.val_mul, _root_.mul_assoc]; rfl
  rw [show v = fun i => c' * t i from funext hv']
  exact Specialise.isThetaPt_mul P ht hc'

theorem isThetaPt_of_series : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → ∀ (j : ℕ) (v : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → Kb R), (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → QkPt D.toPre C ((n ^ j) ^ 2)) (q : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → N.QT ((n ^ j) ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx (n ^ j) (q i)) → IsThetaPt A (n ^ j) (lab ((n ^ j) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p)) := by
  intro R _ _ _ hR D A lab n hn ho _ hT j v hv
  obtain ⟨W, _, _, _, φ, G, _, _, D', A', U', hD, a, _, em₀, hW, iφ, lφ, hG, ⟨ga, hga, gp, lb⟩, c₀, H₀⟩ := hT
  have hV := GlobalTheory.lawsAndExpansions
  have hL : Laws := hV.1.1
  have hL₂ : Laws2 := hV.1.2.1
  have hGF := hL.globalFns
  have := hR.2
  have := hR.1.1
  have := hW.1
  have := hW.2.2
  have hB := D.tau_bimult
  have b₀ : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hm : Odd (n ^ j) := ho.pow
  have hk : 1 ≤ (n ^ j) ^ 2 := pow_pos hm.pos 2
  generalize n ^ j = m at *
  obtain ⟨C, _, _, _, _, _, gam, hgam, hC⟩ := exists_complete_isAlgClosed_cExt W (Kb W)
  have : CharZero C := (RingHom.charZero_iff (algebraMap (FractionRing W) C).injective).1 inferInstance
  letI : Algebra (FractionRing R) C := ((algebraMap (FractionRing W) C).comp ga).toAlgebra
  have cC : Compat φ C := fun r => congrArg (algebraMap (FractionRing W) C) (hga r)
  have a₀K : algebraMap (FractionRing R) (Kb W) = (algebraMap (FractionRing W) (Kb W)).comp ga :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c₀ r).trans
      (congrArg (algebraMap (FractionRing W) (Kb W)) (hga r).symm))
  let jW : Kb W →ₐ[FractionRing W] C := ⟨gam, hgam⟩
  let jR : Kb W →ₐ[FractionRing R] C := ⟨gam, fun t => by rw [a₀K]; exact hgam (ga t)⟩
  have hCR : CExt R (maximalIdeal R) C :=
    ⟨fun r => (cC r).symm ▸ hC.1 _, fun r hr => (cC r).symm ▸ hC.2 _ (map_nonunit φ r hr)⟩
  obtain ⟨N, ν, -⟩ := ValuesExist.exists_integral_values hL R D.toPre D.psi_even hB C ⊤ fun _ => trivial
  obtain ⟨N', ν', -⟩ := ValuesExist.exists_integral_values hL W D'.toPre D'.psi_even D'.tau_bimult C ⊤ fun _ => trivial
  obtain ⟨J, hJX, hJ⟩ := exists_values_iso hL hD cC ν ν'
  obtain ⟨f, hf, hf'⟩ := GlobalTheory.TorsionIso.torsion_clause W _ b₀ D' A' G hG U' C (m ^ 2) hk
  have ex : ∀ i : QkPt D.toPre (Kb R) (m ^ 2), ∃ (p₁ : QkPt D.toPre C (m ^ 2)) (p' : QkPt D'.toPre C (m ^ 2))
      (x' : TFK (R := W) C ⟶ A'.A), QkExt (jR.comp em₀).toRingHom i p₁ ∧ p'.y = hD.xe.symm p₁.y ∧
      IsPullGtF φ hD C p₁.g p'.g ∧ x'.left ≫ a = spMap (jR.comp em₀).toRingHom ≫ (lab _ i).left ∧
      QkToAkU U'.toUnifPre C (m ^ 2) p' x' := fun i => by
    obtain ⟨q₁, hq₁⟩ := exists_ext hB em₀ i
    obtain ⟨r, hr⟩ := exists_ext hB jR q₁
    let q₀ := pullQk hD hGF c₀ hB D'.tau_bimult q₁
    obtain ⟨x₀, hx₀⟩ := exists_lift_pt gp.1 em₀.toRingHom (em₀.comp_algebraMap.trans a₀K) (lab _ i)
    have t₀ := H₀ _ hk i q₁ q₀ x₀ hq₁ rfl (isPullGtF_pullGt hD hGF c₀ _) hx₀
    obtain ⟨⟨q₀', hq₀'⟩, hx, hgal⟩ := GlobalTheory.UT.Cl.galois_holds W _ b₀ D' A' G hG U' _ C jW _ hk q₀
    obtain ⟨x₀', hx₀'⟩ := hx x₀
    refine ⟨r, q₀', x₀', qkExt_trans hq₁ hr, ?_,
      isPullGtF_ext hD cC jW.toRingHom jW.comp_algebraMap (isPullGtF_pullGt hD hGF c₀ _) hr hq₀', ?_,
      (hgal q₀' x₀ x₀' hq₀' hx₀').1 t₀⟩
    · rw [hq₀'.1, hr.1]; rfl
    · rw [hx₀', Category.assoc, hx₀, ← Category.assoc, ← Geo.Tor.spMap_comp]; rfl
  choose p₁ p' x' e₁ e₂ e₃ e₄ e₅ using ex
  have hGt := GlobalTheory.T.torus_torsion_points_correspond_values
  choose q hq using fun i => (((hGt R D.toPre D.psi_even hB C N ν).2.2.2.2 _).1 (p₁ i)).exists
  choose q' hq' using fun i => (((hGt W D'.toPre D'.psi_even D'.tau_bimult C N' ν').2.2.2.2 _).1 (p' i)).exists
  obtain ⟨s, hs⟩ := hv C hCR (jR.comp em₀) N ν p₁ q e₁ hq
  have Q := GlobalTheory.T.theta_constants_eq_degeneration_series hV hGt (GlobalTheory.T.families_values_correspond hL hL₂) W _ hW rfl D' A' G hG U' C hC N' ν' m hm _ p' q' x' e₅ hq'
  have : CharZero (Kb R) := (RingHom.charZero_iff (algebraMap (FractionRing R) (Kb R)).injective).1 inferInstance
  refine isThetaPt_descend hL hL₂ gp lb (jR.comp em₀).toRingHom (jFK (R := R) (Kb R)) (jFK (R := W) C) ?_ hm
    (Nat.cast_ne_zero.2 hm.pos.ne') (lab _) x' e₄ (fun i => ?_) Q (s * J.lam) fun i => ?_
  · exact (Geo.Tor.spMap_comp _ _).symm.trans ((congrArg spMap (jR.comp em₀).comp_algebraMap).trans (Geo.Tor.spMap_comp _ _))
  · rw [(hf.1 _ _).1 (e₅ i)]; exact hf' _
  · have e := (RelabelCoords.series_iso J hm (p := q' i) (p' := q i) (ν.eX.injective (by
      rw [hJX, (hq i).1, (hq' i).1, e₂, AddEquiv.apply_symm_apply])) (hJ _ _ _ _ (hq i).2 (hq' i).2 (e₃ i))).1
    rw [e, Units.val_mul, _root_.mul_assoc, Units.mul_inv_cancel_left]
    exact hs i

end GlobalTheory.Mum.OneTraitTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPointOfAlgebraicSeriesOneTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaPoint_of_algebraic_series_one_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → ∀ (j : ℕ) (v : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → Kb R), (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → QkPt D.toPre C ((n ^ j) ^ 2)) (q : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → N.QT ((n ^ j) ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx (n ^ j) (q i)) → IsThetaPt A (n ^ j) (lab ((n ^ j) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p)) := by
  first | exact @GlobalTheory.Mum.OneTraitTheta.isThetaPt_of_series | exact GlobalTheory.Mum.OneTraitTheta.isThetaPt_of_series | (intros; apply GlobalTheory.Mum.OneTraitTheta.isThetaPt_of_series <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegOfSameTorusTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegOfSameTorusTwist
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Uniq

section General

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {J : Type} [Fintype J]

theorem exists_cancel_linComb (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB) (pr : J → (X' ⟶ X)) (ε : J → ℤ)
    (F : X'' ⟶ X') (pr'' : J → (X'' ⟶ X)) (hpr : ∀ i, pr'' i = F ≫ pr i)
    (w : LB.Iso L' (LB.LinComb L pr ε)) (hw : w.IsGen) (w'' : LB.Iso L'' (LB.LinComb L pr'' ε)) (hw'' : w''.IsGen) :
    ∃ w' : LB.Iso L'' (L'.pull F), PGen w' ∧ ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : J → L.ι) (i : L'.ι) (k : L''.ι),
      f y ∈ LB.wchart L pr'' j → F (f y) ∈ L'.U i → f y ∈ L''.U k →
      gv w'' f y j k = gv w (f ≫ F) y j i * gw w' f y i k := by
  obtain rfl : pr'' = fun i => F ≫ pr i := funext hpr
  have hN := DVR.linComb_isLB L hL pr ε
  have up : ∀ (x : X'') (j : J → L.ι), F x ∈ LB.wchart L pr j → x ∈ LB.wchart L (fun i => F ≫ pr i) j :=
    fun x j h => Set.mem_iInter.2 fun i => Set.mem_iInter.1 h i
  have down : ∀ (x : X'') (j : J → L.ι), x ∈ LB.wchart L (fun i => F ≫ pr i) j → F x ∈ LB.wchart L pr j :=
    fun x j h => Set.mem_iInter.2 fun i => Set.mem_iInter.1 h i
  let v : LB.Iso L'' ((LB.LinComb L pr ε).pull (F ≫ 𝟙 X')) :=
    ⟨fun p => res (fun y hy => ⟨up y _ (mem_pull₂.1 hy.1), hy.2⟩ :
      ((LB.LinComb L pr ε).pull (F ≫ 𝟙 X')).U p.1 ⊓ L''.U p.2 ≤
        LB.wchart L (fun i => F ≫ pr i) (p.1 PUnit.unit) ⊓ L''.U p.2) (w''.s (p.1 PUnit.unit, p.2))⟩
  have hv : ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : J → L.ι) (k : L''.ι), F (f y) ∈ LB.wchart L pr j →
      f y ∈ L''.U k → gw v f y j k = gv w'' f y j k := fun Y f y j k hj hk =>
    gm_res f y _ (show f y ∈ ((LB.LinComb L pr ε).pull (F ≫ 𝟙 X')).U (fun _ => j) ⊓ L''.U k from
      ⟨mem_pull₂.2 hj, hk⟩) _
  have gv' : PGen v := by
    intro Y f y j j' k k' hj hj' hk hk'
    have hj₀ : F (f y) ∈ LB.wchart L pr j := hj
    have hj₀' : F (f y) ∈ LB.wchart L pr j' := hj'
    rw [hv Y f y j k hj₀ hk, hv Y f y j' k' hj₀' hk']
    refine (gm_isGen hw'' f y j j' k k' (up _ _ hj₀) (up _ _ hj₀') hk hk').trans ?_
    refine congrArg (fun a => a * _ * _) ?_
    refine (gm_linComb L _ ε f y j j' (up _ _ hj₀) (up _ _ hj₀')).trans
      (Eq.trans ?_ (gm_linComb L pr ε (f ≫ F ≫ 𝟙 X') y j j' hj₀ hj₀').symm)
    simp only [Category.comp_id, Category.assoc]
  obtain ⟨w', T⟩ := exists_cancel hN (isoPullId w rfl) v (isoPullId_pgen hw rfl) gv' hL' hL''
  refine ⟨w', T.pgen_cancel hN (isoPullId_pgen hw rfl) gv', fun Y f y j i k hj hi hk => ?_⟩
  have e := T Y f y j i k (down _ _ hj) hi hk
  rwa [hv Y f y j k (down _ _ hj) hk, gw_isoPullId w rfl (f ≫ F) y j i (down _ _ hj) hi] at e

theorem gm_mapsAtExp {Y : Scheme.{0}} {pr : J → (X' ⟶ X)} {ε : J → ℤ} {w : LB.Iso L' (LB.LinComb L pr ε)} {p : Y ⟶ X'}
    {n : ℤ} {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n))}
    {b : LB.Gen (LB.LinComb L (K := J) (fun i => p ≫ pr i) (fun i => n * ε i))} (h : MapsAtExp L L' pr ε w p n a b)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (j : J → L.ι) (i : L'.ι) (hj : p (r z) ∈ LB.wchart L pr j)
    (hi : p (r z) ∈ L'.U i) :
    gm r z (LB.wchart L (fun i => p ≫ pr i) j) (b.s j) =
      gv w (r ≫ p) z j i ^ n * gm r z (LB.wchart L' (fun _ : PUnit => p) (fun _ => i)) (a.s (fun _ => i)) := by
  have hm : r z ∈ p ⁻¹ᵁ (LB.div (LB.LinComb L pr ε) L').U (j, i) := ⟨hj, hi⟩
  have e := congrArg (gm r z _) (h j i)
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  exact (map_zpow _ _ _).trans (congrArg (· ^ n) (gm_pull r p z _ hm _))

theorem pmaps_of_mapsAtExp (hL : L.IsLB) {pr : J → (X' ⟶ X)} {ε : J → ℤ} {F : X'' ⟶ X'} {pr'' : J → (X'' ⟶ X)}
    (hpr : ∀ i, pr'' i = F ≫ pr i) {w : LB.Iso L' (LB.LinComb L pr ε)} {w'' : LB.Iso L'' (LB.LinComb L pr'' ε)}
    {w' : LB.Iso L'' (L'.pull F)}
    (T : ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : J → L.ι) (i : L'.ι) (k : L''.ι),
      f y ∈ LB.wchart L pr'' j → F (f y) ∈ L'.U i → f y ∈ L''.U k →
      gv w'' f y j k = gv w (f ≫ F) y j i * gw w' f y i k)
    {Y : Scheme.{0}} {p : Y ⟶ X'} {p'' : Y ⟶ X''} (hp : p'' ≫ F = p) {n : ℤ}
    {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n))}
    {a'' : LB.Gen (LB.LinComb L'' (K := PUnit) (fun _ => p'') (fun _ => n))}
    {b : LB.Gen (LB.LinComb L (K := J) (fun i => p ≫ pr i) (fun i => n * ε i))}
    {b'' : LB.Gen (LB.LinComb L (K := J) (fun i => p'' ≫ pr'' i) (fun i => n * ε i))}
    (h : MapsAtExp L L' pr ε w p n a b) (h'' : MapsAtExp L L'' pr'' ε w'' p'' n a'' b'')
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Z ⟶ X) → L.ι), Good L z I → val b r z I = val b'' r z I) :
    PMaps w' (K := PUnit) (fun _ => p'') (fun _ => p) (fun _ => n) a'' a (𝟙 Y) := by
  obtain rfl : pr'' = fun i => F ≫ pr i := funext hpr
  subst hp
  intro Z r z P Q hP hQ
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have e := H Z r z I hI
  rw [val_of b r z I (fun i => I (r ≫ p'' ≫ F ≫ pr i)) (fun i => by rw [Category.assoc]),
    val_of b'' r z I (fun i => I (r ≫ p'' ≫ F ≫ pr i)) (fun i => rfl)] at e
  have m : ∀ i, pr i (F (p'' (r z))) ∈ L.U (I (r ≫ p'' ≫ F ≫ pr i)) := fun i => hI (r ≫ p'' ≫ F ≫ pr i)
  rw [gm_mapsAtExp h r z _ (P PUnit.unit) (Set.mem_iInter.2 m) (hP PUnit.unit),
    gm_mapsAtExp h'' r z _ (Q PUnit.unit) (Set.mem_iInter.2 m) (hQ PUnit.unit),
    T Z (r ≫ p'') z _ (P PUnit.unit) (Q PUnit.unit) (Set.mem_iInter.2 m) (hP PUnit.unit) (hQ PUnit.unit),
    mul_zpow, Category.assoc, _root_.mul_assoc] at e
  rw [Category.comp_id, Fintype.prod_unique]
  exact mul_left_cancel e

theorem pmaps_of_dense {Y Z₀ : Scheme.{0}} [IsReduced Y] (h : Z₀ ⟶ Y) (z₀ : Z₀)
    (hd : ∀ V : Y.Opens, (V : Set Y).Nonempty → h z₀ ∈ V) {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} {φ' : Y ⟶ X'}
    {φ : Y ⟶ X} (hφ : φ' ≫ F = φ) {a : LB.Gen (L'.pull φ')} {t : LB.Gen (L.pull φ)}
    (H : ∀ (p : L.ι) (q : L'.ι), φ (h z₀) ∈ L.U p → φ' (h z₀) ∈ L'.U q →
      gm h z₀ (LB.wchart L (fun _ : PUnit => φ) (fun _ => p)) (t.s (fun _ => p)) =
        gw w (h ≫ φ') z₀ p q * gm h z₀ (LB.wchart L' (fun _ : PUnit => φ') (fun _ => q)) (a.s (fun _ => q))) :
    PMaps w (K := PUnit) (fun _ => φ') (fun _ => φ) (fun _ => 1) a t (𝟙 Y) := by
  subst hφ
  intro Z r z P Q hP hQ
  let V : Y.Opens := LB.wchart L (fun _ : PUnit => φ' ≫ F) P ⊓ LB.wchart L' (fun _ : PUnit => φ') Q
  have l : V ≤ φ' ⁻¹ᵁ ((L.pull F).U (fun _ => P PUnit.unit) ⊓ L'.U (Q PUnit.unit)) := fun y hy =>
    ⟨mem_pull.2 (Set.mem_iInter.1 hy.1 PUnit.unit), Set.mem_iInter.1 hy.2 PUnit.unit⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ V →
      gm r z V (res (inf_le_left : V ≤ _) (t.s P)) = gm r z (LB.wchart L (fun _ : PUnit => φ' ≫ F) P) (t.s P) ∧
      gm r z V (res l (pullU φ' _ (w.s (fun _ => P PUnit.unit, Q PUnit.unit))) * res (inf_le_right : V ≤ _) (a.s Q)) =
        gw w (r ≫ φ') z (P PUnit.unit) (Q PUnit.unit) * gm r z (LB.wchart L' (fun _ : PUnit => φ') Q) (a.s Q) :=
    fun Z r z hz => ⟨gm_res r z _ hz _, (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z l hz _).trans (gm_pull r φ' z _ (l hz) _)) (gm_res r z _ hz _))⟩
  have hz : r z ∈ V := ⟨Set.mem_iInter.2 hP, Set.mem_iInter.2 hQ⟩
  have hz₀ : h z₀ ∈ V := hd V ⟨_, hz⟩
  have e := TauPull.gm_injective_of_dense h z₀ hd V hz₀ ((key _ h z₀ hz₀).1.trans
    ((H (P PUnit.unit) (Q PUnit.unit) (Set.mem_iInter.1 hz₀.1 PUnit.unit) (Set.mem_iInter.1 hz₀.2 PUnit.unit)).trans
      (key _ h z₀ hz₀).2.symm))
  rw [Category.comp_id, Fintype.prod_unique, zpow_one]
  exact (key _ r z hz).1.symm.trans ((congrArg (gm r z V) e).trans (key _ r z hz).2)

end General

variable {R : Type} [CommRing R] [IsDomain R]

theorem xK_zero (D : DegPre R) : D.xK 0 = jK R ≫ eSec D.P.A := by
  have c0 : (D.c 0).left = eSec D.P.A := by
    have := PsiZero.cPoint_zero' D (𝟙_ _)
    rw [DVR.cP, toUnit_unit, Category.id_comp, Hom.one_def, toUnit_unit, Category.id_comp] at this
    rw [this]; rfl
  rw [← c0]; rfl

theorem gm_psi_zero {D : DegPre R} (hB : D.TauBimult) (χ : D.X) (hχ : χ = 0) (y : (TK R).left) (j : D.P.L.ι)
    (hj : eSec D.P.A (jK R y) ∈ D.P.L.U j) :
    gm (𝟙 _) y (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => j)) ((D.psi χ).s (fun _ => j)) =
      (gm (jK R) y (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => j)) (D.rig.s (fun _ => j)))⁻¹ := by
  subst hχ
  have hx := xK_zero D
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB y (K := PUnit) (fun _ => D.xK 0) (fun _ => j) (fun _ _ _ => rfl)
    (fun k => by rw [hx]; exact hj)
  have e := PsiZero.val_psi_zero hB hJ
  rwa [val_of (D.psi 0) _ y J (fun _ => j) (fun k => (congrArg J (Category.id_comp (D.xK 0))).trans (eJ k)),
    val_of D.rig _ y J (fun _ => j) (fun k => (congrArg J hx.symm).trans (eJ k))] at e

theorem twφ_comp (D₀ D₂ D : DegPre R) (Φ : D₂.P.A ⟶ D₀.P.A) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (i : Fin 3) : twφ D₂ D (Φ ≫ β) b i = Φ.left ≫ twφ D₀ D β b i := by
  have hu : Φ ≫ toUnit D₀.P.A = toUnit D₂.P.A := toUnit_unique _ _
  fin_cases i
  · show (padd D.P.A (Φ ≫ β) (toUnit D₂.P.A ≫ b)).left = (Φ ≫ padd D.P.A β (toUnit D₀.P.A ≫ b)).left
    rw [padd, padd, ← Category.assoc Φ, comp_lift, ← Category.assoc Φ, hu]
  · show (toUnit D₂.P.A ≫ b).left = (Φ ≫ toUnit D₀.P.A ≫ b).left
    rw [← hu, Category.assoc]
  · show (toUnit D₂.P.A ≫ η[D.P.A]).left = (Φ ≫ toUnit D₀.P.A ≫ η[D.P.A]).left
    rw [← hu, Category.assoc]

theorem nonempty_isPullDeg_of_isTwist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D₂ D : DegData R (maximalIdeal R)) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g → GlobalTheory.MumCmp.IsTwist D₂.toPre D.toPre g → Nonempty (IsPullDeg (RingHom.id R) D₀.toPre D₂.toPre) := by
  intro R _ _ _ hR D₀ D₂ D g ⟨β₀, x₀, m₀, c₀, w₀, g₀, ψ₀⟩ ⟨β₂, x₂, m₂, c₂, w₂, g₂, ψ₂⟩
  let Φ : D₂.toPre.P.A ≅ D₀.toPre.P.A := β₂ ≪≫ β₀.symm
  have mΦ : IsMonHom Φ.hom := inferInstanceAs (IsMonHom (β₂.hom ≫ β₀.inv))
  have hβ : β₂.hom = Φ.hom ≫ β₀.hom := by simp [Φ]
  have gp : IsGrpPullback D₂.toPre.P.A D₀.toPre.P.A (specOf (RingHom.id R)) Φ.hom.left :=
    (isGrpPullback_of_iso Φ).congr (specOf_id R).symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D₀.toPre.P.A (specOf (RingHom.id R)))
  have hF' : e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R)) = Φ.hom.left := hF
  have hpr : ∀ i, twφ D₂.toPre D.toPre β₂.hom g.b i =
      (e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R))) ≫ twφ D₀.toPre D.toPre β₀.hom g.b i :=
    fun i => by rw [hF', hβ]; exact twφ_comp _ _ _ _ _ _ i
  obtain ⟨w, gw', T⟩ := exists_cancel_linComb D.toPre.P.isLB D₀.toPre.P.isLB D₂.toPre.P.isLB _ twε _ _ hpr w₀ g₀ w₂ g₂
  let xe : D₂.toPre.X ≃+ D₀.toPre.X := x₂.trans x₀.symm
  have hxe : ∀ χ, x₀ (xe χ) = x₂ χ := fun χ => x₀.apply_symm_apply _
  have hc : ∀ χ, D₂.toPre.c χ ≫ Φ.hom = D₀.toPre.c (xe χ) := fun χ => by
    rw [← cancel_mono β₀.hom, Category.assoc, ← hβ, c₂, c₀, hxe]
  have hc' : ∀ χ, (D₂.toPre.c χ).left ≫ e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R)) =
      (D₀.toPre.c (xe χ)).left := fun χ => by rw [hF', ← Over.comp_left, hc]
  have hx : ∀ χ, D₂.toPre.xK χ ≫ e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R)) =
      D₀.toPre.xK (xe χ) := fun χ => by
    show (jK R ≫ (D₂.toPre.c χ).left) ≫ _ = jK R ≫ (D₀.toPre.c (xe χ)).left
    rw [Category.assoc, hc']
  have hE : eSec D₂.toPre.P.A ≫ e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R)) =
      eSec D₀.toPre.P.A := by
    rw [hF', eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  have hψ : ∀ χ, PMaps w (K := PUnit) (fun _ => D₂.toPre.xK χ) (fun _ => D₀.toPre.xK (xe χ)) (fun _ => -1)
      (D₂.toPre.psi χ) (D₀.toPre.psi (xe χ)) (𝟙 _) := fun χ => by
    obtain ⟨t₀, a₀, b₀⟩ := ψ₀ (xe χ)
    obtain ⟨t₂, a₂, b₂⟩ := ψ₂ χ
    refine pmaps_of_mapsAtExp D.toPre.P.isLB hpr T (hx χ) a₀ a₂ fun Z r z I hI => ?_
    rw [val_corr hI b₀ r, val_corr hI b₂ r]
    have : ∀ a b : D.toPre.X, a = b →
        val (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi a) (LB.pullGen D.toPre.P.L _ _ (g.s a) (toUnit (TK R)).left)) r z I =
        val (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi b) (LB.pullGen D.toPre.P.L _ _ (g.s b) (toUnit (TK R)).left)) r z I := by
      rintro a b rfl; rfl
    exact this _ _ (hxe χ)
  obtain ⟨z₀⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have red : IsReduced (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of R)))
  have hr : PMaps w (K := PUnit) (fun _ => eSec D₂.toPre.P.A) (fun _ => eSec D₀.toPre.P.A) (fun _ => 1)
      D₂.toPre.rig D₀.toPre.rig (𝟙 _) := by
    refine pmaps_of_dense (Z₀ := (TK R).left) (jK R) z₀ (TauPull.jK_mem z₀) hE fun p q hp hq => ?_
    have e := hψ 0 _ (𝟙 _) z₀ (fun _ => p) (fun _ => q)
      (fun _ => by
        show (D₂.toPre.xK 0 ≫ e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R))) z₀ ∈ _
        rw [hx, map_zero, xK_zero]; exact hp)
      (fun _ => by rw [xK_zero]; exact hq)
    rw [Category.id_comp, Fintype.prod_unique, gm_psi_zero D₀.tau_bimult _ (map_zero xe) z₀ p hp,
      gm_psi_zero D₂.tau_bimult _ rfl z₀ q hq, Category.id_comp, xK_zero, zpow_neg, zpow_one, ← mul_inv, inv_inj] at e
    exact e
  obtain ⟨W, hW, ⟨ψW⟩⟩ := psiOnExists R _ hR.1 D₀
  obtain ⟨hD, -⟩ := UnifUniq.exists_isPullDeg_id D₀.toPre D₂.toPre W hW ψW e me w ((isGen_iff _).2 gw') hE hr xe hc' hψ
  exact ⟨hD⟩

end GlobalTheory.MumCmp.Uniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegOfSameTorusTwistStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_isPullDeg_of_same_torus_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D₂ D : DegData R (maximalIdeal R)) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g → GlobalTheory.MumCmp.IsTwist D₂.toPre D.toPre g → Nonempty (IsPullDeg (RingHom.id R) D₀.toPre D₂.toPre) := by
  first | exact @GlobalTheory.MumCmp.Uniq.nonempty_isPullDeg_of_isTwist | exact GlobalTheory.MumCmp.Uniq.nonempty_isPullDeg_of_isTwist | (intros; apply GlobalTheory.MumCmp.Uniq.nonempty_isPullDeg_of_isTwist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkHomStalkMapEqFunctionFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkHomStalkMapEqFunctionFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.ZH.RatModel

theorem stalkHom_stalkMap_algebraMap : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (p : M₂.Z ⟶ M₁.Z), M₂.pt ≫ p = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (z₂ : M₂.Z) (x : M₁.Z.presheaf.stalk (p z₂)), M₂.stalkHom z₂ ((p.stalkMap z₂).hom x) = algebraMap Ω₁ Ω₂ (M₁.stalkHom (p z₂) x) := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ p hp z₂ x
  obtain ⟨U, hU, f, rfl⟩ := M₁.Z.presheaf.germ_exist x
  rw [Scheme.Hom.germ_stalkMap_apply, RatModel.stalkHom_germ, RatModel.stalkHom_germ (M := M₂) (show z₂ ∈ p ⁻¹ᵁ U from hU)]
  rw [GlobalTheory.Points.valF_eq_valR, GlobalTheory.Points.valF_eq_valR, ← GlobalTheory.Points.valR_comp, hp,
    GlobalTheory.Points.valR_spMap_comp _ _ _ (M₁.top_le_preimage_pt ⟨_, hU⟩)]

end GlobalTheory.ZH.RatModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkHomStalkMapEqFunctionFieldExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalkHom_stalkMap_eq_functionFieldExtension : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (p : M₂.Z ⟶ M₁.Z), M₂.pt ≫ p = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (z₂ : M₂.Z) (x : M₁.Z.presheaf.stalk (p z₂)), M₂.stalkHom z₂ ((p.stalkMap z₂).hom x) = algebraMap Ω₁ Ω₂ (M₁.stalkHom (p z₂) x) := by
  first | exact @GlobalTheory.ZH.RatModel.stalkHom_stalkMap_algebraMap | exact GlobalTheory.ZH.RatModel.stalkHom_stalkMap_algebraMap | (intros; apply GlobalTheory.ZH.RatModel.stalkHom_stalkMap_algebraMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRLocalEmbeddingNormal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRLocalEmbeddingNormal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.CompleteNormalDvr

theorem exists_dvr_isCN : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V'), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j := by
  intro R _ _ _ hR
  obtain ⟨h1, h2, h3, h4⟩ := hR
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating R
  obtain ⟨g1, g2, g3⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  refine ⟨V, inferInstance, inferInstance, inferInstance, g1, φ, ?_, hφ, hloc⟩
  exact ⟨inferInstance, inferInstance, g2, g3⟩

end GlobalTheory.CompleteNormalDvr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRLocalEmbeddingNormalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_local_embedding_normal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V'), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j := by
  first | exact @GlobalTheory.CompleteNormalDvr.exists_dvr_isCN | exact GlobalTheory.CompleteNormalDvr.exists_dvr_isCN | (intros; apply GlobalTheory.CompleteNormalDvr.exists_dvr_isCN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCoordsInStandardChartRatio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCoordsInStandardChartRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CrdChart

theorem pCrd_chart : ∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K) (a : Fin (n + 1)), PCrd x v → ⊤ ≤ x ⁻¹ᵁ ProjSpace.chart o n a → v a ≠ 0 ∧ ∀ b, valR x (ProjSpace.chart o n a) (ProjSpace.ratio o n a b) = v b / v a := by
  intro o K _ _ n x v a hx ha
  obtain ⟨c, hc⟩ := CrdUniq.exists_spMap' (x ≫ PSpace.str o n)
  obtain ⟨hv, e⟩ := (CrdUniq.pCrd_iff x c hc.symm v).1 hx
  subst e
  have hu : IsUnit (v a) := (Points.le_pt_preimage_chart_iff c v hv a).1 ha
  refine ⟨hu.ne_zero, fun b => ?_⟩
  rw [Points.valR_pt_ratio c v hv hu b, Ring.inverse_eq_inv', div_eq_mul_inv]

end GlobalTheory.UMin.CrdChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCoordsInStandardChartRatioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousCoords_in_standardChart_ratio : ∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K) (a : Fin (n + 1)), PCrd x v → ⊤ ≤ x ⁻¹ᵁ ProjSpace.chart o n a → v a ≠ 0 ∧ ∀ b, valR x (ProjSpace.chart o n a) (ProjSpace.ratio o n a b) = v b / v a := by
  first | exact @GlobalTheory.UMin.CrdChart.pCrd_chart | exact GlobalTheory.UMin.CrdChart.pCrd_chart | (intros; apply GlobalTheory.UMin.CrdChart.pCrd_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIsOfHeckeLbPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.BiextPairing

open GlobalTheory.UPel.HT

theorem lbIso_lbPow_hecke {X : Scheme.{0}} {P : LB X} (hP : P.IsLB) (k : ℕ) :
    LBIso (lbPow P k) ((Hecke.lbPow P k).pull (𝟙 X)) := by
  have hQ : (Hecke.lbPow P k).IsLB := LB.isLB_linComb hP _ _
  have h₁ : LBIso (lbPow P k) (Hecke.lbPow P k) := by
    unfold Hecke.lbPow lbPow
    apply (GlobalTheory.PrimNorm.lbIso_iff hP _ _ _ _).2
    simp
  exact h₁.trans (LB.isLB_linComb hP _ _) hQ (pull_isLB hQ _) (GlobalTheory.DescendedPrincipal.lbIso_pull_id hQ).symm

theorem weilIs_of_hecke_lbPow {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {P : LB A.left} (hP : P.IsLB) (k : ℕ) {T : Over S} {X Y : T ⟶ A} {u : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs A (Hecke.lbPow P k) 1 X Y u) : Out.WeilIs A P k X Y u := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hQ : (Hecke.lbPow P k).IsLB := LB.isLB_linComb hP _ _
  have := (GlobalTheory.weilIs_along_hom hG S A A (𝟙 _) P (Hecke.lbPow P k) k 1 T X Y u u hA hA hP hQ inferInstance
    (lbIso_lbPow_hecke hP k) (by simpa using h)).1
  simpa using this

end GlobalTheory.BiextPairing

namespace GlobalTheory.BiextPairing

open GlobalTheory.UPel.HT

end GlobalTheory.BiextPairing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoPullbackCommSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoPullbackCommSquare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.SquareIso

theorem lbIso_pull_further {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem iso_pull_of_square : ∀ {X Y Z Y' : Scheme.{0}} (LA' : LB X) (LA : LB Y) (L₁ : LB Z) (L₂ : LB Y') (ψ : X ⟶ Y) (φ₁ : Y ⟶ Z) (φ₂ : X ⟶ Y') (τ : Y' ⟶ Z), LA'.IsLB → LA.IsLB → L₁.IsLB → L₂.IsLB → ψ ≫ φ₁ = φ₂ ≫ τ → (∃ w : LB.Iso LA' (LA.pull ψ), w.IsGen) → (∃ w : LB.Iso LA (L₁.pull φ₁), w.IsGen) → LBIso L₂ (L₁.pull τ) → ∃ w : LB.Iso LA' (L₂.pull φ₂), w.IsGen := by
  intro X Y Z Y' LA' LA L₁ L₂ ψ φ₁ φ₂ τ hA' hA h₁ h₂ e w₁ w₂ w₃
  have a : LBIso (LA.pull ψ) (L₁.pull (φ₂ ≫ τ)) := lbIso_pull_further w₂ ψ e.symm
  have b : LBIso (L₂.pull φ₂) (L₁.pull (φ₂ ≫ τ)) := lbIso_pull_further w₃ φ₂ rfl
  exact LBIso.trans hA' (pull_isLB h₁ _) (pull_isLB h₂ _) (LBIso.trans hA' (pull_isLB hA _) (pull_isLB h₁ _) w₁ a) b.symm

end GlobalTheory.Poinc.SquareIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoPullbackCommSquareStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleIso_pullback_commSquare : ∀ {X Y Z Y' : Scheme.{0}} (LA' : LB X) (LA : LB Y) (L₁ : LB Z) (L₂ : LB Y') (ψ : X ⟶ Y) (φ₁ : Y ⟶ Z) (φ₂ : X ⟶ Y') (τ : Y' ⟶ Z), LA'.IsLB → LA.IsLB → L₁.IsLB → L₂.IsLB → ψ ≫ φ₁ = φ₂ ≫ τ → (∃ w : LB.Iso LA' (LA.pull ψ), w.IsGen) → (∃ w : LB.Iso LA (L₁.pull φ₁), w.IsGen) → LBIso L₂ (L₁.pull τ) → ∃ w : LB.Iso LA' (L₂.pull φ₂), w.IsGen := by
  first | exact @GlobalTheory.Poinc.SquareIso.iso_pull_of_square | exact GlobalTheory.Poinc.SquareIso.iso_pull_of_square | (intros; apply GlobalTheory.Poinc.SquareIso.iso_pull_of_square <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSameGenericProjectiveCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSameGenericProjectiveCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegCrd

theorem eq_of_generic_pCrd : ∀ (o : Type) [CommRing o] (n : ℕ) (X : Scheme.{0}) [IsIntegral X] [IsReduced X] (s : X ⟶ Sp o) (h h' : X ⟶ PSpace o n) (K : Type) [Field K] (x : Sp K ⟶ X) (c : Fin (n + 1) → K), h ≫ PSpace.str o n = s → h' ≫ PSpace.str o n = s → Set.range x = {genericPoint X} → PCrd (x ≫ h) c → PCrd (x ≫ h') c → h = h' := by
  intro o _ n X _ _ s h h' K _ x c hs hs' hx hc hc'
  have : IsSeparated (PSpace.str o n) := by
    have := isProper_str o n
    infer_instance
  have hd : IsDominant x := by
    refine ⟨?_⟩
    change Dense (Set.range x.base)
    have e : Set.range x.base = {genericPoint X} := hx
    rw [e, dense_iff_closure_eq]
    exact genericPoint_closure X
  have he : x ≫ h = x ≫ h' :=
    CrdUniq.eq_of_pCrd (by rw [Category.assoc, Category.assoc, hs, hs']) hc hc'
  exact ext_of_isDominant_of_isSeparated (PSpace.str o n) (hs.trans hs'.symm) x he

end GlobalTheory.SiegCrd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSameGenericProjectiveCoordsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_same_generic_projective_coords : ∀ (o : Type) [CommRing o] (n : ℕ) (X : Scheme.{0}) [IsIntegral X] [IsReduced X] (s : X ⟶ Sp o) (h h' : X ⟶ PSpace o n) (K : Type) [Field K] (x : Sp K ⟶ X) (c : Fin (n + 1) → K), h ≫ PSpace.str o n = s → h' ≫ PSpace.str o n = s → Set.range x = {genericPoint X} → PCrd (x ≫ h) c → PCrd (x ≫ h') c → h = h' := by
  first | exact @GlobalTheory.SiegCrd.eq_of_generic_pCrd | exact GlobalTheory.SiegCrd.eq_of_generic_pCrd | (intros; apply GlobalTheory.SiegCrd.eq_of_generic_pCrd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointGenericFibreMemberHasLabel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointGenericFibreMemberHasLabel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

theorem torsion_has_label : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), xb ^ (X₁.S.r * X₁.S.N) = 1 → ∃ a : X₁.S.Gam, xb.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt a).left := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 xb hxb
  let T := TFK (R := V) (AlgebraicClosure (FractionRing V))
  obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) (T.hom ≫ spMap 𝔪.yK) (pushHom 𝔪.cart T xb)
    (by rw [← map_pow, hxb, map_one])
  refine ⟨a, ?_⟩
  have h1 : (T.hom ≫ spMap 𝔪.yK) ≫ (X₁.ρ.pt a).left = xb.left ≫ 𝔪.φ := congrArg (fun z => z.left) ha
  rw [← h1]
  congr 1
  exact (Spec.map_comp (CommRingCat.ofHom 𝔪.yK)
    (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))))).symm

end GlobalTheory.Poinc.IntTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointGenericFibreMemberHasLabelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricTorsionPoint_genericFibre_member_has_label : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), xb ^ (X₁.S.r * X₁.S.N) = 1 → ∃ a : X₁.S.Gam, xb.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt a).left := by
  first | exact @GlobalTheory.Poinc.IntTerm.torsion_has_label | exact GlobalTheory.Poinc.IntTerm.torsion_has_label | (intros; apply GlobalTheory.Poinc.IntTerm.torsion_has_label <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackUniformisationCharacterMapConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackUniformisationCharacterMapConjugate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.EndPullChar

theorem pull_char_eq : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R'), Function.Injective φ → I.map φ ≤ I' → ∀ (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing R'))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I' D' A' G') (bc : G' ≅ (Over.pullback (spMap φ)).obj G), IsMonHom bc.hom → IsPullUnif φ hD bc U U' → ∀ (E : EndU U.toUnifPre) (E' : EndU U'.toUnifPre), E'.aG.left ≫ bc.hom.left ≫ pullback.fst G.hom (spMap φ) = bc.hom.left ≫ pullback.fst G.hom (spMap φ) ≫ E.aG.left → ∀ χ, hD.xe (E'.h χ) = E.h (hD.xe χ) := by
  intro R R' _ _ _ _ I I' hR hR' φ _hφ _hI D D' hD A A' G _ _ G' _ _ _hG _hG' U U' bc _hbc hU E E' hE
  have hG : E'.aG ≫ bc.hom = bc.hom ≫ (Over.pullback (spMap φ)).map E.aG := by
    refine GlobalTheory.PullLinear.ext_of_pullback (spMap φ) ?_
    rw [Over.comp_left, Over.comp_left, Category.assoc, hE, Category.assoc,
      GlobalTheory.PullLinear.map_left_fst]
  have := E'.homG
  obtain ⟨E'', h₁, h₂, -⟩ := GlobalTheory.UT.EndBaseChange.exists_end hD hU E E'.aG hG
  have h₃ := (GlobalTheory.EndCalc.congr_data hR' E'' E' h₁).2
  intro χ
  rw [← h₂ χ, h₃]

end GlobalTheory.EndPullChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackUniformisationCharacterMapConjugateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackUniformisation_characterMap_conjugate : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R'), Function.Injective φ → I.map φ ≤ I' → ∀ (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing R'))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I' D' A' G') (bc : G' ≅ (Over.pullback (spMap φ)).obj G), IsMonHom bc.hom → IsPullUnif φ hD bc U U' → ∀ (E : EndU U.toUnifPre) (E' : EndU U'.toUnifPre), E'.aG.left ≫ bc.hom.left ≫ pullback.fst G.hom (spMap φ) = bc.hom.left ≫ pullback.fst G.hom (spMap φ) ≫ E.aG.left → ∀ χ, hD.xe (E'.h χ) = E.h (hD.xe χ) := by
  first | exact @GlobalTheory.EndPullChar.pull_char_eq | exact GlobalTheory.EndPullChar.pull_char_eq | (intros; apply GlobalTheory.EndPullChar.pull_char_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisFixesQuotientPointsOfRational
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisFixesQuotientPointsOfRational
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalFixQ

open GlobalTheory.TorusExt

theorem qkExt_equiv_of_rational : ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (D₂ : DegData R₂ (maximalIdeal R₂)) (n : ℕ), (∀ p : QkPt D₂.toPre (Kb R₂) n, ∃ (p₀ : QkPt D₂.toPre (FractionRing R₂) n) (p₁ : QkPt D₂.toPre (Kb R₂) n), QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ ∧ QkPt.Equiv D₂.toPre (Kb R₂) p₁ p) → ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, ∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p' := by
  intro R₂ _ _ _ D₂ n hrat σ p p' hpp'
  have hB := D₂.tau_bimult
  have hf : σ.toRingHom.comp (algebraMap (FractionRing R₂) (Kb R₂)) = algebraMap (FractionRing R₂) (Kb R₂) :=
    σ.comp_algebraMap
  have ha : (algebraMap (FractionRing R₂) (Kb R₂)).comp (algebraMap (FractionRing R₂) (FractionRing R₂)) =
      algebraMap (FractionRing R₂) (Kb R₂) := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  obtain ⟨p₀, p₁, e₁, h₁⟩ := hrat p
  have hq : QkExt σ.toRingHom p₁ (qkExt hB σ.toRingHom hf p₁) := (qkExt_iff hB _ hf _ _).2 rfl
  have e₂ := GlobalTheory.LabTrans.qkExt_trans e₁ hq
  rw [hf] at e₂
  have hfix : qkExt hB σ.toRingHom hf p₁ = p₁ :=
    ((qkExt_iff hB _ ha _ _).1 e₂).trans ((qkExt_iff hB _ ha _ _).1 e₁).symm
  rw [hfix] at hq
  exact equiv_trans hB (equiv_symm hB h₁) (equiv_of_qkExt hB σ.toRingHom hf hq hpp' h₁)

end GlobalTheory.Mum.GalFixQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisFixesQuotientPointsOfRationalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_fixes_quotientPoints_of_rational : ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (D₂ : DegData R₂ (maximalIdeal R₂)) (n : ℕ), (∀ p : QkPt D₂.toPre (Kb R₂) n, ∃ (p₀ : QkPt D₂.toPre (FractionRing R₂) n) (p₁ : QkPt D₂.toPre (Kb R₂) n), QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ ∧ QkPt.Equiv D₂.toPre (Kb R₂) p₁ p) → ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, ∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p' := by
  first | exact @GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational | exact GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational | (intros; apply GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStalkGermQuotientIntegralUnitDenominator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStalkGermQuotientIntegralUnitDenominator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem GlobalTheory.Poinc.finite_stalk_quot_integral : ∀ (X Y : Scheme.{0}) (p : Y ⟶ X), IsFinite p → ∀ (y : Y) (a : Y.presheaf.stalk y), ∃ b s : Y.presheaf.stalk y, IsUnit s ∧ a * s = b ∧ (∃ P : Polynomial (X.presheaf.stalk (p y)), P.Monic ∧ P.eval₂ (p.stalkMap y).hom b = 0) ∧ ∃ Q : Polynomial (X.presheaf.stalk (p y)), Q.Monic ∧ Q.eval₂ (p.stalkMap y).hom s = 0 := by
  intro X Y p hp y a
  obtain ⟨U, hU', hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := p y) trivial
  have hV : IsAffineOpen (p ⁻¹ᵁ U) := hU'.preimage p
  have hyV : y ∈ p ⁻¹ᵁ U := hyU
  letI : Algebra Γ(Y, p ⁻¹ᵁ U) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk ⟨y, hyV⟩
  haveI := hV.isLocalization_stalk ⟨y, hyV⟩
  obtain ⟨⟨c, t⟩, hct⟩ := IsLocalization.mk'_surjective (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl a
  have hfin : (p.app U).hom.Finite := p.finite_app U hU'
  have hint := hfin.to_isIntegral
  have key : ∀ z : Γ(Y, p ⁻¹ᵁ U), ∃ P : Polynomial (X.presheaf.stalk (p y)), P.Monic ∧
      P.eval₂ (p.stalkMap y).hom (algebraMap Γ(Y, p ⁻¹ᵁ U) (Y.presheaf.stalk y) z) = 0 := by
    intro z
    obtain ⟨P', hm, hP'⟩ := hint z
    refine ⟨P'.map (X.presheaf.germ U (p y) hyU).hom, hm.map _, ?_⟩
    have hc : (p.stalkMap y).hom.comp (X.presheaf.germ U (p y) hyU).hom
        = (Y.presheaf.germ (p ⁻¹ᵁ U) y hyV).hom.comp (p.app U).hom := by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap]
    rw [Polynomial.eval₂_map, hc]
    change Polynomial.eval₂ _ ((Y.presheaf.germ (p ⁻¹ᵁ U) y hyV).hom z) P' = 0
    rw [← Polynomial.hom_eval₂, hP', map_zero]
  refine ⟨algebraMap _ _ c, algebraMap _ _ (t : Γ(Y, p ⁻¹ᵁ U)), IsLocalization.map_units _ t, ?_, key c, key t⟩
  rw [← hct]
  exact IsLocalization.mk'_spec _ c t
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStalkGermQuotientIntegralUnitDenominatorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_stalk_germ_quotient_integral_unit_denominator : ∀ (X Y : Scheme.{0}) (p : Y ⟶ X), IsFinite p → ∀ (y : Y) (a : Y.presheaf.stalk y), ∃ b s : Y.presheaf.stalk y, IsUnit s ∧ a * s = b ∧ (∃ P : Polynomial (X.presheaf.stalk (p y)), P.Monic ∧ P.eval₂ (p.stalkMap y).hom b = 0) ∧ ∃ Q : Polynomial (X.presheaf.stalk (p y)), Q.Monic ∧ Q.eval₂ (p.stalkMap y).hom s = 0 := by
  first | exact @GlobalTheory.Poinc.finite_stalk_quot_integral | exact GlobalTheory.Poinc.finite_stalk_quot_integral | (intros; apply GlobalTheory.Poinc.finite_stalk_quot_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionsDescend
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LevelSecDesc

theorem levelSections_descend : ∀ (O : Type) [Ring O] (La : Type) [AddCommGroup La] [Module O La] (N : ℕ) (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (act : OActN O A) (act₀ : OActN O A₀) (eta : La → (𝟙_ (Over X) ⟶ A)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsGrpPullback A A₀ π φ → GlobalTheory.ZM.IsGaloisCover Ga ν φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ a y, (eta y).left ≫ ν a = ρ a ≫ (eta y).left) → (∀ x y, eta (x + y) = eta x * eta y) → (∀ (c : O) x, eta (c • x) = eta x ≫ act.act c) → (∀ x, eta (N • x) = 1) → ∃ eta₀ : La → (𝟙_ (Over Y) ⟶ A₀), (∀ x y, eta₀ (x + y) = eta₀ x * eta₀ y) ∧ (∀ (c : O) x, eta₀ (c • x) = eta₀ x ≫ act₀.act c) ∧ (∀ x, eta₀ (N • x) = 1) ∧ ∀ y, (eta y).left ≫ φ = π ≫ (eta₀ y).left := by
  intro O _ La _ _ N X Y π Ga _ ρ A _ _ A₀ _ _ φ ν act act₀ eta hπ gp hφ hact heq hadd hlin htor
  have := hπ.etale
  have := hπ.onto
  have : Epi π := Flat.epi_of_flat_of_surjective π
  have desc : ∀ y, ∃ e : 𝟙_ (Over Y) ⟶ A₀, (eta y).left ≫ φ = π ≫ e.left := fun y => by
    obtain ⟨g, hg, -⟩ := (GlobalTheory.ZM.galoisCover_descent X Y π Ga ρ hπ).1 A₀.left ((eta y).left ≫ φ) fun a => by
      rw [← Category.assoc, ← heq a y, Category.assoc, hφ.inv a]
    exact GlobalTheory.ObjDesc.exists_sec gp (eta y) g hg
  choose eta₀ heta using desc
  have hse : ∀ y, GlobalTheory.ObjPull.secPull gp (eta₀ y) = eta y := fun y => GlobalTheory.ObjDesc.secPull_eq gp (heta y)
  refine ⟨eta₀, fun x y => GlobalTheory.ObjDesc.secPull_injective gp (by rw [map_mul, hse, hse, hse, hadd]),
    fun c x => ?_, fun x => GlobalTheory.ObjDesc.secPull_injective gp (by rw [map_one, hse, htor]), heta⟩
  apply Over.OverMorphism.ext
  rw [← cancel_epi π, ← heta, hlin, Over.comp_left, Over.comp_left, Category.assoc, hact c, ← Category.assoc,
    heta, Category.assoc]

end GlobalTheory.LevelSecDesc

end
end
