module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulMemAdjoinOfMemPowRange
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimQuotientLeOne
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsSectionRing
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.CardZerosOnTorsionCosetLe
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.TorsionZeroCountTwist
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SqIsPowGrp
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SvalEqZeroOfExpandsAt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelSplitSpecialFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedFibreThroughIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedFibreThroughIso
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open FrameMove ConstFam ThetaPtMove

theorem exists_frames_move_through {S S' : Scheme.{0}} {f : S' ⟶ S} {P : PolAV S} {P' : PolAV S'}
    {φ : P'.A.left ⟶ P.A.left} {w : LB.Iso P'.L (P.L.pull φ)} {T : Over S} {T' : Over S'} {h : T'.left ⟶ T.left}
    (gp : IsGrpPullback P'.A P.A f φ) (hw : w.IsGen)
    {rig : LB.Gen (P.L.pull (eSec P.A))} (hrig : rig.IsGen) {I : Type} {x : I → (T ⟶ P.A)} {x' : I → (T' ⟶ P'.A)}
    (hx : ∀ i, (x' i).left ≫ φ = h ≫ (x i).left) {n : ℕ}
    {τ : ∀ i, LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (x i).left) (fun _ => 1))}
    (H : ∀ i, IsTorsFrame P rig n (x i) (τ i)) :
    ∃ (rig' : LB.Gen (P'.L.pull (eSec P'.A)))
      (τ' : ∀ i, LB.Gen (LB.LinComb P'.L (Y := T'.left) (K := Fin 1) (fun _ => (x' i).left) (fun _ => 1))),
      rig'.IsGen ∧ GenThrough w (fun _ : PUnit => eSec P'.A) (fun _ : PUnit => eSec P.A) (fun _ => 1) rig' rig f ∧
        ∀ i, IsTorsFrame P' rig' n (x' i) (τ' i) ∧
          GenThrough w (fun _ : Fin 1 => (x' i).left) (fun _ : Fin 1 => (x i).left) (fun _ => 1) (τ' i) (τ i) h := by
  obtain ⟨rig', hrig', Hr⟩ := exists_gen_through (K := PUnit) (φ' := fun _ => eSec P'.A) (φ := fun _ => eSec P.A)
    (ε := fun _ => 1) (h := f) hw P.isLB P'.isLB (fun _ => PolBaseChange.eSec_comm gp) rig hrig
  choose τ' hτ' Hτ using fun i => exists_gen_through (φ' := fun _ : Fin 1 => (x' i).left) (h := h) hw P.isLB P'.isLB
    (fun _ => hx i) (τ i) (H i).2.1
  have ht : ∀ i (z : T'.left) J J', Good P.L z J → Good P'.L z J' →
      val (τ i) h z J = wVal w z J J' (x' i).left * val (τ' i) (𝟙 _) z J' := fun i z J J' hJ hJ' => by
    have := Hτ i _ (𝟙 _) z J J' hJ hJ'
    rwa [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at this
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S')).left) (z : Z) J J', Good P.L z J → Good P'.L z J' →
      rval rig (r ≫ f) z J = wVal w z J J' (r ≫ eSec P'.A) * rval rig' r z J' := fun Z r z J J' hJ hJ' =>
    (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))
  exact ⟨rig', τ', hrig', Hr, fun i => ⟨isTorsFrame_move gp hw hr (hx i) (H i) (hτ' i) (ht i), Hτ i⟩⟩

theorem exists_frames_on_fibre_through : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∀ w : LB.Iso u.A.L (ρ.P.L.pull u.φ), w.IsGen → ∃ (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrAt (x a)), rig.IsGen ∧ GlobalTheory.ThetaPtMove.GenThrough w (fun _ : PUnit => eSec u.A.A) (fun _ : PUnit => eSec ρ.P.A) (fun _ => 1) rig ρ.rig (spMap u.yK) ∧ ∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a) ∧ GlobalTheory.ThetaPtMove.GenThrough w (fun _ : Fin 1 => (x a).left) (fun _ : Fin 1 => (ρ.pt a).left) (fun _ => 1) (e a) (ρ.fr a) (spMap y₀) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u x hx w hw
  exact exists_frames_move_through (T := baseOver (Sp S.R)) (T' := TFK (R := u.V) (PadicAlgCl p))
    u.cart hw ρ.rig_gen hx ρ.fr_tors

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedFibreThroughIsoStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frames_on_uniformised_fibre_through_iso : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∀ w : LB.Iso u.A.L (ρ.P.L.pull u.φ), w.IsGen → ∃ (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrAt (x a)), rig.IsGen ∧ GlobalTheory.ThetaPtMove.GenThrough w (fun _ : PUnit => eSec u.A.A) (fun _ : PUnit => eSec ρ.P.A) (fun _ => 1) rig ρ.rig (spMap u.yK) ∧ ∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a) ∧ GlobalTheory.ThetaPtMove.GenThrough w (fun _ : Fin 1 => (x a).left) (fun _ : Fin 1 => (ρ.pt a).left) (fun _ => 1) (e a) (ρ.fr a) (spMap y₀) := by
  first | exact @GlobalTheory.exists_frames_on_fibre_through | exact GlobalTheory.exists_frames_on_fibre_through | (intros; apply GlobalTheory.exists_frames_on_fibre_through <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChange
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

noncomputable section
namespace GlobalTheory.ZH.LinFrame
open GlobalTheory.ProjSpace

variable {o : Type} [CommRing o] {m : ℕ} {T : Scheme.{0}}

def chartLB (p : T ⟶ PSpace o m) : LB T :=
  ⟨Fin (m + 1), fun i => p ⁻¹ᵁ chart o m i, fun i j =>
    ⟨pullRatio p _ i inf_le_left j, pullRatio p _ j inf_le_right i,
      pullRatio_mul_pullRatio.trans pullRatio_self, pullRatio_mul_pullRatio.trans pullRatio_self⟩⟩

theorem lin_compat (p : T ⟶ PSpace o m) (b : Fin (m + 1) → Γ(T, ⊤)) (i j : Fin (m + 1)) :
    resG T (inf_le_left : p ⁻¹ᵁ chart o m i ⊓ p ⁻¹ᵁ chart o m j ≤ _)
        (∑ k, resG T le_top (b k) * pullRatio p (p ⁻¹ᵁ chart o m i) i le_rfl k) =
      pullRatio p (p ⁻¹ᵁ chart o m i ⊓ p ⁻¹ᵁ chart o m j) i inf_le_left j *
        resG T (inf_le_right : p ⁻¹ᵁ chart o m i ⊓ p ⁻¹ᵁ chart o m j ≤ _)
          (∑ k, resG T le_top (b k) * pullRatio p (p ⁻¹ᵁ chart o m j) j le_rfl k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, resG_pullRatio, resG_pullRatio, mul_left_comm, pullRatio_mul_pullRatio]
  congr 1
  exact (DVR.SecOps.resTop_res _ _).trans (DVR.SecOps.resTop_res _ _).symm

def linSec (p : T ⟶ PSpace o m) (b : Fin (m + 1) → Γ(T, ⊤)) : (chartLB p).Sec where
  f l := ∑ k, resG T le_top (b k) * pullRatio p (p ⁻¹ᵁ chart o m l) l le_rfl k
  compat i j := lin_compat p b i j

variable {K : Type} [Field K]

theorem crd_iff (x : Sp K ⟶ PSpace o m) (v : Fin (m + 1) → K) : Crd (O1 o m) (coord o m) x v ↔
    ∃ (l : Fin (m + 1)) (c : Kˣ), ⊤ ≤ x ⁻¹ᵁ chart o m l ∧
      ∀ j, v j = (c : K) * valR x (chart o m l) (ratio o m l j) := Iff.rfl

theorem valR_pullRatio (x : Sp K ⟶ T) (p : T ⟶ PSpace o m) {W : T.Opens} {l : Fin (m + 1)}
    (hl : W ≤ p ⁻¹ᵁ chart o m l) (h : ⊤ ≤ x ⁻¹ᵁ W) (k : Fin (m + 1)) :
    valR x W (pullRatio p W l hl k) = valR (x ≫ p) (chart o m l) (ratio o m l k) :=
  Points.valR_appLE x p hl h _

theorem valR_linSec (x : Sp K ⟶ T) (p : T ⟶ PSpace o m) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T, ⊤))
    {l : Fin (m + 1)} (h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l) (i : Fin (m + 1)) :
    valR x (p ⁻¹ᵁ chart o m l) ((linSec p (b i)).f l) =
      (b.map (valR x ⊤)).mulVec (fun k => valR (x ≫ p) (chart o m l) (ratio o m l k)) i := by
  change valR x (p ⁻¹ᵁ chart o m l) (∑ k, resG T le_top (b i k) * pullRatio p (p ⁻¹ᵁ chart o m l) l le_rfl k) =
    ∑ k, valR x ⊤ (b i k) * valR (x ≫ p) (chart o m l) (ratio o m l k)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [CrdCalc.valR_eq x _ h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← CrdCalc.valR_eq x _ h, CrdCalc.valR_mul x _ h, CrdCalc.valR_res x _ h, valR_pullRatio x p _ h]

theorem valR_ratio_self (x : Sp K ⟶ PSpace o m) {l : Fin (m + 1)} (h : ⊤ ≤ x ⁻¹ᵁ chart o m l) :
    valR x (chart o m l) (ratio o m l l) = 1 := by
  rw [ratio, ratioOn_self, Points.valR_one x _ h]

theorem exists_isUnit_valR_linSec (x : Sp K ⟶ T) (p : T ⟶ PSpace o m)
    {b : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T, ⊤)} (hb : IsUnit b.det)
    {l : Fin (m + 1)} (h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l) :
    ∃ i, IsUnit (valR x (p ⁻¹ᵁ chart o m l) ((linSec p (b i)).f l)) := by
  by_contra hn
  have e : b.map (valR x ⊤) = (CrdCalc.valHom x ⊤ le_top).mapMatrix b := by
    ext i j
    exact CrdCalc.valR_eq x ⊤ le_top _
  have hd : (b.map (valR x ⊤)).det ≠ 0 := by
    rw [e, ← RingHom.map_det]
    exact (hb.map _).ne_zero
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hd
    (v := fun k => valR (x ≫ p) (chart o m l) (ratio o m l k)) (funext fun i => by
      rw [← valR_linSec x p b h]
      by_contra hi
      exact hn ⟨i, Ne.isUnit hi⟩)
  have h1 := congrFun h0 l
  rw [valR_ratio_self (x ≫ p) h] at h1
  exact one_ne_zero h1

theorem iSup_nonzeroLocus_linSec (p : T ⟶ PSpace o m)
    {b : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T, ⊤)} (hb : IsUnit b.det) :
    ⨆ i, nonzeroLocus (linSec p (b i)) = ⊤ := by
  refine top_le_iff.1 fun y _ => ?_
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 ((iSup_chart o m).ge (Set.mem_univ (p y)))
  let x : Sp (T.residueField y) ⟶ T := T.fromSpecResidueField y
  have hx : ∀ z, x z = y := fun z => T.fromSpecResidueField_apply y z
  have h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l := fun z _ => by
    change p (x z) ∈ chart o m l
    rw [hx]; exact hl
  obtain ⟨i, hi⟩ := exists_isUnit_valR_linSec x p hb h
  have h2 : x (IsLocalRing.closedPoint _) ∈ T.basicOpen ((linSec p (b i)).f l) :=
    (CrdCalc.isUnit_valR_iff x _ h _).1 hi (Set.mem_univ _)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨l, (congrArg (· ∈ T.basicOpen ((linSec p (b i)).f l)) (hx _)).mp h2⟩⟩

theorem crd_toProj_linSec {A : Type} [CommRing A] (c : T ⟶ Sp A) (p : T ⟶ PSpace o m)
    {b : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T, ⊤)} (hb : IsUnit b.det) (x : Sp K ⟶ T) {v : Fin (m + 1) → K}
    (hv : Crd (O1 o m) (coord o m) (x ≫ p) v) :
    Crd (O1 A m) (coord A m) (x ≫ toProj c (fun i => linSec p (b i)) (iSup_nonzeroLocus_linSec p hb))
      ((b.map (valR x ⊤)).mulVec v) := by
  obtain ⟨l, u, hl, hv⟩ := (crd_iff _ _).1 hv
  have h : ⊤ ≤ x ⁻¹ᵁ p ⁻¹ᵁ chart o m l := hl
  obtain ⟨i, hi⟩ := exists_isUnit_valR_linSec x p hb h
  set g := toProj c (fun i => linSec p (b i)) (iSup_nonzeroLocus_linSec p hb) with hg
  have h₁ : ⊤ ≤ x ⁻¹ᵁ g ⁻¹ᵁ chart A m i := by
    rw [hg, toProj_preimage_chart]
    exact ((CrdCalc.isUnit_valR_iff x _ h _).1 hi).trans
      (x.preimage_mono (le_iSup (fun k => T.basicOpen ((linSec p (b i)).f k)) l))
  have h₂ : ⊤ ≤ x ⁻¹ᵁ (g ⁻¹ᵁ chart A m i ⊓ p ⁻¹ᵁ chart o m l) := fun z hz => ⟨h₁ hz, h hz⟩
  refine (crd_iff _ _).2 ⟨i, u * hi.unit, h₁, fun j => ?_⟩
  have e := congrArg (valR x _) (sec_eq_pullRatio_toProj_mul c (fun i => linSec p (b i))
    (iSup_nonzeroLocus_linSec p hb) i j l (W := g ⁻¹ᵁ chart A m i ⊓ p ⁻¹ᵁ chart o m l) inf_le_left inf_le_right)
  have r : ∀ t : (chartLB p).Sec, _ = valR x (p ⁻¹ᵁ chart o m l) (t.f l) := fun t =>
    CrdCalc.valR_res x inf_le_right h₂ (t.f l)
  replace e := (r _).symm.trans (e.trans ((CrdCalc.valR_mul x _ h₂ _ _).trans
    (congrArg₂ (· * ·) (valR_pullRatio x _ _ h₂ _) (r _))))
  have ev : v = (u : K) • fun k => valR (x ≫ p) (chart o m l) (ratio o m l k) := funext hv
  rw [ev, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← valR_linSec x p b h, Units.val_mul, IsUnit.unit_spec,
    _root_.mul_assoc]
  exact congrArg (_ * ·) (e.trans (mul_comm _ _))

theorem eq_of_crd {x x' : Sp K ⟶ PSpace o m} (hs : x ≫ PSpace.str o m = x' ≫ PSpace.str o m)
    {w : Fin (m + 1) → K} (h : Crd (O1 o m) (coord o m) x w) (h' : Crd (O1 o m) (coord o m) x' w) : x = x' := by
  obtain ⟨l, c, hl, hw⟩ := (crd_iff _ _).1 h
  obtain ⟨l', c', hl', hw'⟩ := (crd_iff _ _).1 h'
  have h1 : w l = c := by rw [hw, valR_ratio_self x hl, mul_one]
  have h2 : ⊤ ≤ x' ⁻¹ᵁ chart o m l := by
    have hu : IsUnit (valR x' (chart o m l') (ratio o m l' l)) :=
      (Units.isUnit_units_mul c' _).1 ((hw' l).symm.trans h1 ▸ c.isUnit)
    refine ((CrdCalc.isUnit_valR_iff x' _ hl' _).1 hu).trans (x'.preimage_mono ?_)
    rw [ratio, basicOpen_ratioOn]
    exact inf_le_right
  obtain ⟨u, hu⟩ := CrdCalc.exists_unit_charts (O1 o m) x' l' l hl' h2
  have hw'' : ∀ j, w j = (c' : K) * u * valR x' (chart o m l) (ratio o m l j) := fun j => by
    rw [hw', _root_.mul_assoc]
    exact congrArg (_ * ·) (hu (coord o m j))
  have h3 : (c' : K) * u = c := by rw [← h1, hw'', valR_ratio_self x' h2, mul_one]
  refine hom_ext hs fun _ => ⟨⊤, trivial, l, hl, h2, fun j => ?_⟩
  have e := (hw j).symm.trans (hw'' j)
  rw [h3, Units.mul_right_inj, CrdCalc.valR_eq x _ hl, CrdCalc.valR_eq x' _ h2] at e
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective e

theorem isImmersion_lift_of_linear_change : ∀ (o : Type) [CommRing o] (Y Z : Scheme.{0}) [IsReduced Y] (s : Z ⟶ Sp o) (f : Y ⟶ Z) (m : ℕ) (π : Y ⟶ PSpace o m) (h : π ≫ PSpace.str o m = f ≫ s), (∀ y : Y, ∃ (W : Z.Opens) (A : Type) (_ : CommRing A) (c : W.toScheme ⟶ Sp A) (ψ : (f ⁻¹ᵁ W).toScheme ⟶ PSpace A m) (a : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(Z, W)) (K : Type) (_ : Field K) (η : Sp K ⟶ (f ⁻¹ᵁ W).toScheme) (v : Fin (m + 1) → K), f y ∈ W ∧ IsImmersion ψ ∧ ψ ≫ PSpace.str A m = (f ∣_ W) ≫ c ∧ IsUnit a.det ∧ IsDominant η ∧ Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (η ≫ (f ⁻¹ᵁ W).ι ≫ π) v ∧ Crd (ProjSpace.O1 A m) (ProjSpace.coord A m) (η ≫ ψ) ((a.map (valF (η ≫ (f ⁻¹ᵁ W).ι ≫ f) W)).mulVec v)) → IsImmersion (pullback.lift π f h) := by
  intro o _ Y Z _ s f m π h H
  choose W A iA c ψ a K iK η v hy hψ hc ha hη h₁ h₂ using H
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun i hi g hg => by
      have : IsOpenImmersion i := hi
      have : IsImmersion g := hg
      infer_instance⟩
  have hj : pullback.lift π f h ≫ pullback.snd (PSpace.str o m) s = f := pullback.lift_snd _ _ _
  have hπ : pullback.lift π f h ≫ pullback.fst (PSpace.str o m) s = π := pullback.lift_fst _ _ _
  generalize pullback.lift π f h = j at hj hπ ⊢
  generalize pullback.fst (PSpace.str o m) s = q at hπ
  generalize pullback.snd (PSpace.str o m) s = r at hj
  subst hj hπ
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (fun y => r ⁻¹ᵁ W y) ?_ fun y => ?_
  · rintro _ ⟨y, rfl⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩
  have := hψ y
  have := hη y
  have hT : (⊤ : (r ⁻¹ᵁ W y).toScheme.Opens) ≤ ((r ⁻¹ᵁ W y).ι ≫ r) ⁻¹ᵁ W y := (r ⁻¹ᵁ W y).ι_preimage_self.ge
  let b := (((r ⁻¹ᵁ W y).ι ≫ r).appLE (W y) ⊤ hT).hom.mapMatrix (a y)
  have hb : IsUnit b.det := by
    rw [← RingHom.map_det]
    exact (ha y).map _
  let j' : ((j ≫ r) ⁻¹ᵁ W y).toScheme ⟶ (r ⁻¹ᵁ W y).toScheme := j ∣_ (r ⁻¹ᵁ W y)
  have hj' : j' ≫ (r ⁻¹ᵁ W y).ι = ((j ≫ r) ⁻¹ᵁ W y).ι ≫ j := morphismRestrict_ι j _
  let g := toProj ((r ∣_ W y) ≫ c y) (fun i => linSec ((r ⁻¹ᵁ W y).ι ≫ q) (b i)) (iSup_nonzeroLocus_linSec _ hb)
  have hs : (j' ≫ g) ≫ PSpace.str (A y) m = ψ y ≫ PSpace.str (A y) m := by
    rw [Category.assoc, toProj_str, hc, morphismRestrict_comp]
    exact (Category.assoc _ _ _).symm
  have e : j' ≫ g = ψ y := by
    refine ext_of_isDominant_of_isSeparated _ hs (η y) (eq_of_crd ?_ ?_ (h₂ y))
    · rw [Category.assoc, hs, Category.assoc]
    · have k := crd_toProj_linSec ((r ∣_ W y) ≫ c y) ((r ⁻¹ᵁ W y).ι ≫ q) hb (η y ≫ j') (v := v y) (by
        rw [Category.assoc, reassoc_of% hj']
        exact h₁ y)
      have eb : b.map (valR (η y ≫ j') ⊤) = (a y).map (valF (η y ≫ ((j ≫ r) ⁻¹ᵁ W y).ι ≫ j ≫ r) (W y)) := by
        ext i k
        refine (Points.valR_appLE (η y ≫ j') _ hT le_top (a y i k)).trans ?_
        rw [Category.assoc, reassoc_of% hj']
        rfl
      rw [eb, Category.assoc] at k
      exact k
  have : IsImmersion (j' ≫ g) := e ▸ hψ y
  exact IsImmersion.of_comp j' g

end GlobalTheory.ZH.LinFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChangeStatement
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isImmersion_projSpace_of_local_linearChange : ∀ (o : Type) [CommRing o] (Y Z : Scheme.{0}) [IsReduced Y] (s : Z ⟶ Sp o) (f : Y ⟶ Z) (m : ℕ) (π : Y ⟶ PSpace o m) (h : π ≫ PSpace.str o m = f ≫ s), (∀ y : Y, ∃ (W : Z.Opens) (A : Type) (_ : CommRing A) (c : W.toScheme ⟶ Sp A) (ψ : (f ⁻¹ᵁ W).toScheme ⟶ PSpace A m) (a : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(Z, W)) (K : Type) (_ : Field K) (η : Sp K ⟶ (f ⁻¹ᵁ W).toScheme) (v : Fin (m + 1) → K), f y ∈ W ∧ IsImmersion ψ ∧ ψ ≫ PSpace.str A m = (f ∣_ W) ≫ c ∧ IsUnit a.det ∧ IsDominant η ∧ Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (η ≫ (f ⁻¹ᵁ W).ι ≫ π) v ∧ Crd (ProjSpace.O1 A m) (ProjSpace.coord A m) (η ≫ ψ) ((a.map (valF (η ≫ (f ⁻¹ᵁ W).ι ≫ f) W)).mulVec v)) → IsImmersion (pullback.lift π f h) := by
  first | exact @GlobalTheory.ZH.LinFrame.isImmersion_lift_of_linear_change | exact GlobalTheory.ZH.LinFrame.isImmersion_lift_of_linear_change | (intros; apply GlobalTheory.ZH.LinFrame.isImmersion_lift_of_linear_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperHomOfRelAmple
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem isProper_hom_of_relAmple {T : Scheme.{0}} {A : Over T} [GrpObj A] {B : LB A.left} (h : RelAmple A B) :
    IsProper A.hom := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) (fun U : T.affineOpens => U.1)
    (iSup_affineOpens_eq_top T) fun U => ?_
  have h₁ := projProper _ _ _ (GlobalTheory.ProjSpace.isProjOver_morphismRestrict_of_relAmple h U.2)
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsProper) _ U.2.isoSpec.hom).1 h₁

theorem abOpen_of_isOpen_abLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → IsOpen (abLocus Z.G) → GlobalTheory.Models.AbOpen Z.G := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Z _ hO
  letI := Z.grp
  let W : M.Z.Opens := ⟨abLocus Z.G, hO⟩
  refine ⟨W, rfl, ?_⟩
  have h : IsProper (pullback.snd Z.G.hom W.ι) := isProper_hom_of_relAmple (Z.pol W le_rfl).1
  unfold morphismRestrict
  infer_instance

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByOfSpans
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem immBy_of_spans (hA : AmpleSt) {R : Type} [CommRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) {N : ℕ}
    (hN : 4 ≤ N) {J : Type} [Fintype J] (s : J → LB.Sec (LPow P.A P.L N (baseOver (Sp R))))
    (hs : ∀ σ : LB.Sec (LPow P.A P.L N (baseOver (Sp R))), ∃ c : J → Γ((baseOver (Sp R)).left, ⊤),
      ∀ j, σ.f j = ∑ i, liftFun P.A _ (c i) * (s i).f j) :
    ImmBy (baseOver (Sp R) ⊗ P.A).hom (LPow P.A P.L N (baseOver (Sp R))) s Set.univ := by
  have := P.isAb.proper
  have hT : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  have hL : IsLocallyNoetherian (Sp R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
  have key := (AmpleSpan.embedsBy_of_isPullback P.A P.isLB (hA _ P N hN).2 (isAffineOpen_top (Sp R))
    (g := (baseOver (Sp R)).hom ≫ (Sp R).topIso.inv) (φ := (snd (baseOver (Sp R)) P.A).left)
    (f' := (fst (baseOver (Sp R)) P.A).left) (K := Fin 1) (ε := fun _ => (N : ℤ))
    (by rw [AmpleSpan.comp_topIso_inv_ι]; exact (IsPullback.of_hasPullback _ P.A.hom).flip) (by simp) s
    (fun σ => hs σ)).1
  have e : (baseOver (Sp R) ⊗ P.A).hom = (fst (baseOver (Sp R)) P.A).left :=
    (Over.w (fst (baseOver (Sp R)) P.A)).symm.trans (Category.comp_id _)
  rw [SpanImm.immBy_iff, e]
  exact key

theorem ThetaSys.Real.immBy_basis : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), ImmBy (baseOver (Sp S.R) ⊗ ρ.P.A).hom (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))) ρ.s Set.univ := by
  intro hL o Ω _ _ _ _ S ρ
  have := ArithBase.ded (o := o) (Ω := Ω)
  have : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  have : IsNoetherianRing S.R := Algebra.FiniteType.isNoetherianRing o S.R
  have hN : 4 ≤ S.N := by
    have h : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]
    exact Nat.pow_le_pow_left h 2
  exact immBy_of_spans hL.1.ample ρ.P hN ρ.s fun σ => (ρ.s_basis σ).exists

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionZerosTwistLe
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem card_torsion_zeros_twist_le :
    Out.Laws → Out.Laws2 → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N d k : ℕ) (c : Out.baseOver (Sp K) ⟶ P.A), 1 ≤ P.g → 4 ≤ N → 1 ≤ d → (k : K) ≠ 0 → ∀ s : LB.Sec (Out.twistLB P.A P.L (N * d) c), (∃ j, s.f j ≠ 0) → Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ k = 1 ∧ ¬ ⊤ ≤ (Out.ptSecT P.A x).left ⁻¹ᵁ Out.nonzeroLocus s} ≤ N ^ P.g * P.g.factorial * d * k ^ (2 * P.g - 2)) :=
  fun h _ => torsion_zero_count_twist h.mulN h.square
    (card_zeros_on_torsion_coset_le h.mulN SectionRing.exists_sectionRing
      (PowSec.exists_basis_sections h.globalSectionsRank) (veryAmple_lbPow h.ample) (exists_mulPull_sec h.mulPull)
      SmoothDim.ringKrullDim_affineOpen polAV_isIntegral_of_isAlgClosed isIntegral_adjoin_of_mul_pow_mem
      graded_bezout_bound)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionProjSpaceOfSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionProjSpaceOfSections
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

namespace GlobalTheory.ZH.ImmProj

theorem exists_closedImmersion_of_immBy : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) (s : J → H.Sec) (m : ℕ) (e : Fin (m + 1) ≃ J), ImmBy p H s Set.univ → ∃ φ : X ⟶ PSpace k m, IsClosedImmersion φ ∧ φ ≫ PSpace.str k m = p ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd (ProjSpace.O1 k m) (ProjSpace.coord k m) (x ≫ φ) (fun i => v (e i)) := by
  intro k _ X p H J s m e ⟨hc, hi⟩
  have hs : ⨆ i, nonzeroLocus (s (e i)) = ⊤ := by
    rw [e.iSup_comp (g := fun j => nonzeroLocus (s j))]
    simpa only [Set.mem_univ, iSup_pos] using hc
  refine ⟨ProjSpace.toProj p (fun i => s (e i)) hs, ?_, ProjSpace.toProj_str _ _ _, ?_⟩
  · refine (ProjSpace.isClosedImmersion_toProj_iff p _ hs).2 fun i => ⟨(hi (e i) trivial).1, ?_⟩
    obtain ⟨r, hr, hcl⟩ := (hi (e i) trivial).2
    obtain rfl : r = fun j => ProjSpace.secRatio (s (e i)) (s j) :=
      funext fun j => ProjSpace.eq_secRatio _ _ (hr j)
    rw [← SpanImm.closure_eq_top_iff, ← hcl]
    congr 2
    exact e.surjective.range_comp (fun j => ProjSpace.secRatio (s (e i)) (s j))
  · intro K _ x v hv
    obtain ⟨i, hx⟩ := Points.exists_le_preimage_of_iSup_eq_top x hs
    have hu := (CrdCalc.crd_isUnit_iff (e i) hv).2 hx
    have hle := (ProjSpace.toProj_preimage_chart p (fun i => s (e i)) hs i).ge
    refine ⟨i, hu.unit, hx.trans (x.preimage_mono hle), fun j => ?_⟩
    have h1 := CrdCalc.crd_ratio (i := e i) (j := e j) hv (ProjSpace.secRatio_spec (s (e i)) (s (e j))) hx
    beta_reduce
    rw [h1, IsUnit.unit_spec, mul_comm, ← ProjSpace.pullRatio_toProj p (fun i => s (e i)) hs i j]
    exact congrArg _ (Points.valR_appLE x _ hle hx _)

end GlobalTheory.ZH.ImmProj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionProjSpaceOfSectionsStatement
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedImmersion_projSpace_of_sections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) (s : J → H.Sec) (m : ℕ) (e : Fin (m + 1) ≃ J), ImmBy p H s Set.univ → ∃ φ : X ⟶ PSpace k m, IsClosedImmersion φ ∧ φ ≫ PSpace.str k m = p ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd (ProjSpace.O1 k m) (ProjSpace.coord k m) (x ≫ φ) (fun i => v (e i)) := by
  first | exact @GlobalTheory.ZH.ImmProj.exists_closedImmersion_of_immBy | exact GlobalTheory.ZH.ImmProj.exists_closedImmersion_of_immBy | (intros; apply GlobalTheory.ZH.ImmProj.exists_closedImmersion_of_immBy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGenerators
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section

namespace GlobalTheory.RosatiDescent

theorem exists_gen_of_rosatiAdj {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    {f g : A ⟶ A} (h : RosatiAdj A L f g) : ∃ t : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε), t.IsGen := by
  obtain ⟨U, hU, t, ht⟩ := h (default : PrimeSpectrum k)
  obtain rfl : U = ⊤ := eq_top_iff.2 fun x _ => by
    rwa [Subsingleton.elim (α := PrimeSpectrum k) x default]
  have e : rosatiφ A f g = fun i => (A ⊗ A).left.topIso.inv ≫ ((A ⊗ A).hom ⁻¹ᵁ ⊤).ι ≫ rosatiφ A f g i :=
    funext fun i => ((A ⊗ A).left.topIso.inv_hom_id_assoc _).symm
  rw [e]
  exact ⟨_, DVR.pullGen_isGen _ _ _ _ ht _⟩

theorem rosatiAdj_descend {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) {A₀ : Over (Sp K₀)} {A : Over (Sp K)}
    [GrpObj A₀] [IsCommMonObj A₀] [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A₀) {Φ : A.left ⟶ A₀.left}
    (h : IsGrpPullback A A₀ (spMap i) Φ) {L₀ : LB A₀.left} {L : LB A.left} (hL₀ : L₀.IsLB) (hL : L.IsLB)
    (hw : LBIso L (L₀.pull Φ)) {f g : A ⟶ A} {f₀ g₀ : A₀ ⟶ A₀} (hf : f.left ≫ Φ = Φ ≫ f₀.left)
    (hg : g.left ≫ Φ = Φ ≫ g₀.left) (hr : RosatiAdj A L f g) : RosatiAdj A₀ L₀ f₀ g₀ := by
  have A₂ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ hA hA
  let U₂ := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
  have u₁ : U₂.left ≫ (fst A₀ A₀).left = (fst A A).left ≫ Φ := TripleDescent.lift_left_fst _ _
  have u₂ : U₂.left ≫ (snd A₀ A₀).left = (snd A A).left ≫ Φ := TripleDescent.lift_left_snd _ _
  have P₂ : IsPullback U₂.left (A ⊗ A).hom (A₀ ⊗ A₀).hom (spMap i) :=
    TripleDescent.isPullback_tensor h.1 h.1 _ u₁ u₂
  have v₁ : (fst A A ≫ f).left ≫ Φ = U₂.left ≫ (fst A₀ A₀ ≫ f₀).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, ← u₁, Category.assoc]
  have v₂ : (snd A A ≫ g).left ≫ Φ = U₂.left ≫ (snd A₀ A₀ ≫ g₀).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hg, ← Category.assoc, ← u₂, Category.assoc]
  have hψ : ∀ k, rosatiφ A f g k ≫ Φ = U₂.left ≫ rosatiφ A₀ f₀ g₀ k := fun k => by
    fin_cases k
    exacts [ArcPull.mul_push h U₂.left v₁ u₂.symm, v₁, u₂.symm, ArcPull.mul_push h U₂.left u₁.symm v₂, u₁.symm, v₂]
  obtain ⟨t, ht⟩ := exists_gen_of_rosatiAdj hr
  obtain ⟨w, hw⟩ := hw
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hL₀ hL t ht
  obtain ⟨u, hu⟩ := (lb_gen_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀).hom _ _ A₂.smooth A₂.proper A₂.geomConnected P₂).1
    (LB.LinComb L₀ (rosatiφ A₀ f₀ g₀) rosatiε) (DVR.linComb_isLB _ hL₀ _ _)
    (gen_chartPull (chartPullOut L₀ _ _ U₂.left _ hψ) c hc)
  exact fun s => ⟨⊤, trivial, _, DVR.pullGen_isGen _ _ _ _ hu _⟩

end GlobalTheory.RosatiDescent

theorem GlobalTheory.polOAct_descend_of_generators : ∀ (O : Type) [CommRing O] [StarRing O] (J : Type) (gen : J → O), Subring.closure (Set.range gen) = ⊤ → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (P₀ : PolAV (Sp K₀)) (P : PolAV (Sp K)) (Φ : P.A.left ⟶ P₀.A.left), IsGrpPullback P.A P₀.A (spMap i) Φ → LBIso P.L (P₀.L.pull Φ) → ∀ (oa : P.OAct O) (a₀ : J → (P₀.A ⟶ P₀.A)), (∀ j, (oa.act (gen j)).left ≫ Φ = Φ ≫ (a₀ j).left) → ∃ oa₀ : P₀.OAct O, ∀ c, (oa.act c).left ≫ Φ = Φ ≫ (oa₀.act c).left := by
  intro O _ _ J gen hgen K₀ K _ _ i P₀ P Φ h hw oa a₀ ha
  have := P₀.isAb.comm
  have := P.isAb.comm
  obtain ⟨r, -, hr⟩ := oAct_descend_of_generators O J gen K₀ K i P₀.A P.A Φ (ofRingAct oa.toRingAct) a₀ hgen h ha
  exact ⟨⟨r.toRingAct, fun a => RosatiDescent.rosatiAdj_descend i P₀.isAb h P₀.isLB P.isLB hw (hr a) (hr (star a))
    (oa.rosati a)⟩, hr⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGeneratorsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedRingAction_descend_of_generators : ∀ (O : Type) [CommRing O] [StarRing O] (J : Type) (gen : J → O), Subring.closure (Set.range gen) = ⊤ → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (P₀ : PolAV (Sp K₀)) (P : PolAV (Sp K)) (Φ : P.A.left ⟶ P₀.A.left), IsGrpPullback P.A P₀.A (spMap i) Φ → LBIso P.L (P₀.L.pull Φ) → ∀ (oa : P.OAct O) (a₀ : J → (P₀.A ⟶ P₀.A)), (∀ j, (oa.act (gen j)).left ≫ Φ = Φ ≫ (a₀ j).left) → ∃ oa₀ : P₀.OAct O, ∀ c, (oa.act c).left ≫ Φ = Φ ≫ (oa₀.act c).left := by
  first | exact @GlobalTheory.polOAct_descend_of_generators | exact GlobalTheory.polOAct_descend_of_generators | (intros; apply GlobalTheory.polOAct_descend_of_generators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecScalIffPullAb
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZH.AdaptedSpan

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBaseChange GlobalTheory.PullbackValuation GlobalTheory.IntegralCombination

variable {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
  [IsCommMonObj G]

abbrev SecGen (U : UnifPre I D A G) (k : ℕ) : Type :=
  SecOver (R := FractionRing V) (pullback.snd G.hom (jK V))
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)))

def toGen (U : UnifPre I D A G) (k : ℕ) : SecG U k →ₛₗ[algebraMap V (FractionRing V)] SecGen U k :=
  pullOver U.LG.L (fun _ : Fin 1 => (k : ℤ)) (pullback.condition : pullback.fst G.hom (jK V) ≫ G.hom = _)
    (fun _ => (Category.comp_id _).symm)

def famAt (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (α : D.X) :
    Fam D F k →ₗ[F] SecAbF D F k α where
  toFun s := s.s α
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem secScal_iff_pullAb (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] {k : ℕ} {α : D.X}
    (s : SecAbF D F k α) (g : SecAb D k α) (r : V) :
    GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) s (D.famφB α) (DegPre.famε k) g (DegPre.prB D F).left
      (scal (DegPre.BF D F).hom r) ↔ pullAb D F k α g = toF V F r • s :=
  secScal_iff (prB_over D F) (GC.famφ_eq D F α) D.P.isLB s g _ (toF V F)
    ((Over.w (DegPre.prB D F)).symm.trans (prB_over D F)) r

theorem expandsAt_sum (U : UnifPre I D A G) (e k : ℕ) {J : Type} [Fintype J] (σ : J → SecG U k)
    (f : J → ∀ α, SecAb D.toPre k α) (h : ∀ p, U.ExpandsAt e k (σ p) (f p)) (b : J → V) :
    U.ExpandsAt e k (∑ p, b p • σ p : SecG U k) (fun α => (∑ p, b p • f p α : SecAb D.toPre k α)) := by
  have E := (Fintype.equivFin J).symm
  have H := expandsAt_comb U e k (fun p => σ (E p)) (fun p => f (E p)) (fun p => h (E p)) (fun p => b (E p))
  rw [E.sum_comp (fun p => b p • σ p)] at H
  exact (congrArg (U.ExpandsAt e k _) (funext fun α => E.sum_comp (fun p => b p • f p α))).mp H

theorem expands_toGen (U : UnifPre I D A G) (k : ℕ) (τ : SecG U k) (g : ∀ α, SecAb D.toPre k α)
    (s : Fam D.toPre (FractionRing V) k) (hτ : ∀ e, U.ExpandsAt e k τ g)
    (hs : ∀ α, pullAb D.toPre _ k α (g α) = famAt D.toPre _ k α s) : U.Expands k (toGen U k τ) s := by
  refine ⟨1, one_ne_zero, τ, g, ?_, fun α => ?_, hτ⟩
  · exact (secScal_iff pullback.condition _ U.LG.isLB _ _ _ (algebraMap V (FractionRing V)) rfl 1).2
      (by rw [map_one, one_smul]; rfl)
  · exact (secScal_iff_pullAb _ _ (famAt D.toPre _ k α s) _ 1).2 (by rw [map_one, one_smul]; exact hs α)


open Classical in
theorem exists_comb (hG : GlobalFnsSt) (U : Unif I D A G) {k : ℕ} (hk : 1 ≤ k) {J : Type} [Fintype J]
    (σ : J → SecG U.toUnifPre k) (cls : J → D.toPre.X) (f : J → ∀ α, SecAb D.toPre k α)
    (h₂ : ∀ i i', (∃ m, cls i = cls i' + k • m) → cls i = cls i') (h₃ : ∀ α, ∃ i m, α = cls i + k • m)
    (h₄ : ∀ i e, U.toUnifPre.ExpandsAt e k (σ i) (f i))
    (h₅ : ∀ i, ∃ s : Fam D.toPre (FractionRing V) k, FamOf D.toPre _ (f i) s)
    (h₆ : ∀ i α, (∀ m, α ≠ cls i + k • m) → ∀ j, LB.Sec.f (f i α) j = 0)
    (h₇ : ∀ i₀, IsBasisB D.toPre (fun i : {i // cls i = cls i₀} => f i (cls i₀)))
    (s : SecGen U.toUnifPre k) : ∃ a : J → FractionRing V, s = ∑ i, a i • toGen U.toUnifPre k (σ i) := by
  obtain ⟨F, ⟨r, hr, τ, g, hτ, hg, hE⟩, -⟩ := (U.expand k hk).1 s
  have hτ' : toGen U.toUnifPre k τ = algebraMap V (FractionRing V) r • s :=
    (secScal_iff pullback.condition _ U.LG.isLB s τ _ (algebraMap V (FractionRing V)) rfl r).1 hτ
  have hg' : ∀ α, pullAb D.toPre _ k α (g α) = famAt D.toPre _ k α (toF V (FractionRing V) r • F) := fun α => by
    rw [map_smul]; exact (secScal_iff_pullAb _ _ _ _ r).1 (hg α)
  choose t ht using h₅
  have ht' : ∀ i α, pullAb D.toPre _ k α (f i α) = famAt D.toPre _ k α (t i) := fun i α => by
    have := (secScal_iff_pullAb _ _ (famAt D.toPre _ k α (t i)) (f i α) 1).1 (by
      have e : scal (DegPre.BF D.toPre (FractionRing V)).hom (1 : V) = 1 := by
        unfold scal; rw [map_one, map_one]
      rw [e]; exact ht i α)
    rwa [map_one, one_smul] at this
  have hb : ∀ c : D.toPre.X, ∃ b : J → V, (∃ i₀, cls i₀ = c) →
      (show SecAb D.toPre k c from g c) = ∑ i, (if cls i = c then b i else 0) • f i c := fun c => by
    by_cases hc : ∃ i₀, cls i₀ = c
    · obtain ⟨i₀, rfl⟩ := hc
      obtain ⟨a, ha, -⟩ := h₇ i₀ (g (cls i₀))
      refine ⟨fun i => if h : cls i = cls i₀ then a ⟨i, h⟩ else 0, fun _ => ?_⟩
      have e : (show SecAb D.toPre k (cls i₀) from g (cls i₀)) =
          ∑ i : {i // cls i = cls i₀}, a i • f i (cls i₀) :=
        SecOver.ext _ _ fun j => (ha j).trans
          (map_sum (chartLin D.toPre.P.A.hom _ j) (fun i : {i // cls i = cls i₀} => a i • f i (cls i₀)) _).symm
      rw [e, ← Fintype.sum_subtype_add_sum_subtype (fun i => cls i = cls i₀),
        Finset.sum_eq_zero (s := (Finset.univ : Finset {i // ¬ cls i = cls i₀}))
          (fun i _ => by rw [if_neg i.2, zero_smul]), add_zero]
      exact Finset.sum_congr rfl fun i _ => by rw [if_pos i.2]; beta_reduce; rw [dite_eq_left i.2]
    · exact ⟨0, fun h => absurd h hc⟩
  choose b hb using hb
  have key : toF V (FractionRing V) r • F = ∑ i, toF V (FractionRing V) (b (cls i) i) • t i := by
    refine fam_ext fun α j => ?_
    obtain ⟨i₀, m, rfl⟩ := h₃ α
    refine congrArg (LB.Sec.f · j) (GlobalTheory.FamFree.eq_of_eq_add_nsmul hG _ _ ⟨m, rfl⟩ ?_)
    refine (hg' _).symm.trans (Eq.trans ?_ (map_sum (famAt D.toPre _ k (cls i₀)) _ _).symm)
    refine (congrArg (pullAb D.toPre _ k (cls i₀)) (hb _ ⟨i₀, rfl⟩)).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, map_smul, ← ht']
    split_ifs with h
    · rw [h]
    · have z : f i (cls i₀) = 0 := SecOver.ext _ _ (h₆ i _ fun m e => h (h₂ i₀ i ⟨m, e⟩).symm)
      rw [z, map_zero (pullAb D.toPre _ k (cls i₀)), smul_zero, smul_zero]
  have E₁ := expands_toGen U.toUnifPre k τ g _ hE hg'
  have E₂ := expands_toGen U.toUnifPre k _ _ (∑ i, toF V (FractionRing V) (b (cls i) i) • t i)
    (fun e => expandsAt_sum U.toUnifPre e k σ f (fun i => h₄ i e) (fun i => b (cls i) i)) (fun α => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, map_smul, ← ht'])
  rw [key] at E₁
  have e : toGen U.toUnifPre k τ = toGen U.toUnifPre k (∑ i, b (cls i) i • σ i) :=
    ((U.expand k hk).2 _).unique E₁ E₂
  have hr' : algebraMap V (FractionRing V) r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V _)).2 hr
  refine ⟨fun i => (algebraMap V (FractionRing V) r)⁻¹ * algebraMap V _ (b (cls i) i), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hτ', map_sum] at e
  rw [← inv_smul_smul₀ hr' s, e, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, smul_smul]

end GlobalTheory.ZH.AdaptedSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegreeFormsDimensionGenericFibreLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegreeFormsDimensionGenericFibreLe
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.FormCount

section Values
variable {F : Type} [CommRing F] {X Y : Scheme.{0}}

theorem valR_appLE (x : Sp F ⟶ Y) (φ : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ φ ⁻¹ᵁ U)
    (f : Γ(X, U)) (hx : ⊤ ≤ x ⁻¹ᵁ V) : valR x V ((φ.appLE U V h).hom f) = valR (x ≫ φ) U f := by
  have hx' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := le_trans hx (x.preimage_mono h)
  rw [CrdCalc.valR_eq _ _ hx, CrdCalc.valR_eq _ _ hx', CrdCalc.valHom, CrdCalc.valHom,
    ← Scheme.Hom.appLE_comp_appLE x φ U V ⊤ h hx]
  rfl

theorem valR_scal {K : Type} [CommRing K] (ψ : K →+* F) (x : Sp F ⟶ Y) (q : Y ⟶ Sp K) (hq : x ≫ q = spMap ψ)
    (V : Y.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ V) (c : K) : valR x V (resTop V (scal q c)) = ψ c := by
  have e : valR x V (resTop V (scal q c)) =
      valR (x ≫ q) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) :=
    valR_appLE x q ⊤ V le_top _ hx
  have e' := (CrdCalc.valR_spMap ψ (𝟙 (Sp K)) ⊤ le_rfl).2 ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)
  rw [Category.comp_id] at e'
  rw [e, hq, e', CrdCalc.valR_eq _ _ le_top]
  have h : (𝟙 (Sp K) : Sp K ⟶ Sp K).appLE ⊤ ⊤ le_top = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
  congr 1
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    (((𝟙 (Sp K) : Sp K ⟶ Sp K).appLE ⊤ ⊤ le_top).hom _) = c
  rw [h]
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id_apply c

theorem wchart_le (L : LB X) (φ : Y ⟶ X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => φ) j ≤ φ ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

theorem exists_monomial (L : LB X) (φ : Y ⟶ X) (N d : ℕ) {J : Type} [Fintype J]
    (σ : J → (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (N : ℤ))).Sec) (α : J → ℕ) (hα : ∑ i, α i = d) :
    ∃ s : (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => ((N * d : ℕ) : ℤ))).Sec,
      ∀ j, s.f j = ∏ i, (φ.appLE _ _ (wchart_le L φ j)).hom ((σ i).f j) ^ α i := by
  have pull_restrict {U U' : X.Opens} {V V' : Y.Opens} (hu : U' ≤ U) (hv : V' ≤ V)
      (h : V ≤ φ ⁻¹ᵁ U) (h' : V' ≤ φ ⁻¹ᵁ U') (a : Γ(X, U)) :
      (Y.presheaf.map (homOfLE hv).op).hom ((φ.appLE U V h).hom a) =
        (φ.appLE U' V' h').hom ((X.presheaf.map (homOfLE hu).op).hom a) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have transition {Z : Scheme.{0}} (f : Z ⟶ X) (j j' : Fin 1 → L.ι) (n : ℕ) :
      ((L.LinComb (fun _ : Fin 1 => f) (fun _ => (n : ℤ))).g j j').val =
        ((f.appLE _ _ (le_inf
          (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => f) j 0))
          (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => f) j' 0)))).hom
          (L.g (j 0) (j' 0)).val) ^ n := by
    simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
    rfl
  let A (j : Fin 1 → L.ι) := L.wchart (fun _ : Fin 1 => 𝟙 X) j
  let B (j : Fin 1 → L.ι) := L.wchart (fun _ : Fin 1 => φ) j
  let s (i : J) (j : Fin 1 → L.ι) : Γ(X, A j) := (σ i).f j
  let m (j : Fin 1 → L.ι) : Γ(Y, B j) := ∏ i, (φ.appLE (A j) (B j) (wchart_le L φ j)).hom (s i j) ^ α i
  refine ⟨⟨m, ?_⟩, fun _ => rfl⟩
  rintro (j : Fin 1 → L.ι) (j' : Fin 1 → L.ι)
  let U := A j ⊓ A j'
  let V := B j ⊓ B j'
  have h : V ≤ φ ⁻¹ᵁ U := fun _ hy => ⟨wchart_le L φ j hy.1, wchart_le L φ j' hy.2⟩
  let p := (φ.appLE U V h).hom
  let gX : Γ(X, U) := ((L.LinComb (fun _ : Fin 1 => 𝟙 X) (fun _ => (N : ℤ))).g j j').val
  let gY : Γ(Y, V) := ((L.LinComb (fun _ : Fin 1 => φ) (fun _ => ((N * d : ℕ) : ℤ))).g j j').val
  have hg : p gX ^ d = gY := by
    dsimp only [p, gX, gY]
    rw [transition (𝟙 X) j j' N, transition φ j j' (N * d), map_pow, ← pow_mul,
      ← CommRingCat.comp_apply]
    erw [Scheme.Hom.appLE_comp_appLE φ (𝟙 X)]
    rfl
  let leftX := (X.presheaf.map (homOfLE (inf_le_left : U ≤ A j)).op).hom
  let rightX := (X.presheaf.map (homOfLE (inf_le_right : U ≤ A j')).op).hom
  have hc (i : J) : p (leftX (s i j)) = p gX * p (rightX (s i j')) := by
    rw [← map_mul]
    exact congrArg p ((σ i).compat j j')
  change (Y.presheaf.map (homOfLE (inf_le_left : V ≤ B j)).op).hom (m j) =
    gY * (Y.presheaf.map (homOfLE (inf_le_right : V ≤ B j')).op).hom (m j')
  simp only [m, map_prod, map_pow,
    pull_restrict (inf_le_left : U ≤ A j) (inf_le_left : V ≤ B j) (wchart_le L φ j) h,
    pull_restrict (inf_le_right : U ≤ A j') (inf_le_right : V ≤ B j') (wchart_le L φ j') h]
  change (∏ i, p (leftX (s i j)) ^ α i) = gY * ∏ i, p (rightX (s i j')) ^ α i
  simp only [hc, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hα, hg]

end Values

theorem hilb_le {k J : Type} [Field k] [Fintype J] (C : Set (J → k)) (d m : ℕ) (β : Fin m → C → k)
    (h : ∀ α : J → ℕ, ∑ i, α i = d → ∃ c : Fin m → k, ∀ v : C, ∏ i, v.1 i ^ α i = ∑ l, c l * β l v) :
    hilb C d ≤ m := by
  have le : (MvPolynomial.homogeneousSubmodule J k d).map
      (LinearMap.pi fun v : C => (MvPolynomial.aeval (R := k) v.1).toLinearMap) ≤ Submodule.span k (Set.range β) := by
    rintro _ ⟨P, hP, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [P.as_sum, map_sum]
    refine Submodule.sum_mem _ fun α hα => ?_
    have hd : ∑ i, α i = d := by
      have := MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hP hα
      rw [this]
      exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => Finsupp.notMem_support_iff.1 hi).symm
    obtain ⟨c, hc⟩ := h α hd
    refine (Submodule.mem_span_range_iff_exists_fun k).2 ⟨fun l => P.coeff α * c l, funext fun v => ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.pi_apply, AlgHom.toLinearMap_apply,
      MvPolynomial.aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), hc v, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => _root_.mul_assoc _ _ _
  have := Module.Finite.span_of_finite k (Set.finite_range β)
  exact (Submodule.finrank_mono le).trans ((finrank_range_le_card β).trans (Fintype.card_fin m).le)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

theorem dim_eq (u : ρ.UTest p y₀) : u.A.g = S.g :=
  (ReciprocityTheory.ChartRestriction.G.H1.dim_unique u.A.A.hom u.A.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback u.cart.1 ρ.P.smoothDim)
    (eSec u.A.A (IsLocalRing.closedPoint _))).trans ρ.g_eq

theorem gPt_j (u : ρ.UTest p y₀) :
    gPt p ≫ spMap u.j = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem hilb_generic_le : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (J : Type) [Fintype J] (σ : J → (u.H S.N).Sec) (d : ℕ), 1 ≤ d → hilb {w : J → PadicAlgCl p | ∃ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j ∧ Crd (u.H S.N) σ a w} d ≤ (S.N * d) ^ S.g := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u J _ σ d hd
  have hN : 1 ≤ S.N * d := by
    rw [ρ.N_eq]
    exact Nat.mul_pos (pow_pos (pow_pos ρ.n_prime.pos _) _) hd
  obtain ⟨b, -, hb⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis hL.1.secBaseChange u.V _ u.D u.A u.G
    u.U.toUnifPre (S.N * d) hN
  rw [← dim_eq u]
  let C := {w : J → PadicAlgCl p | ∃ a : Sp (PadicAlgCl p) ⟶ u.G.left,
    a ≫ u.G.hom = gPt p ≫ spMap u.j ∧ Crd (u.H S.N) σ a w}
  have hC : ∀ w : C, ∃ (x : Sp (PadicAlgCl p) ⟶ pullback u.G.hom (jK u.V)) (l : Fin 1 → u.U.LG.L.ι)
      (c : PadicAlgCl p), x ≫ pullback.snd _ _ = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ∧
      ⊤ ≤ x ⁻¹ᵁ LB.wchart u.U.LG.L (fun _ : Fin 1 => pullback.fst u.G.hom (jK u.V)) l ∧
      ∀ i, w.1 i = c * valR (x ≫ pullback.fst _ _) _ ((σ i).f l) := by
    rintro ⟨w, a, ha, l, c, hl, hw⟩
    obtain ⟨x, rfl, hx⟩ : ∃ x : Sp (PadicAlgCl p) ⟶ pullback u.G.hom (jK u.V), x ≫ pullback.fst _ _ = a ∧
        x ≫ pullback.snd _ _ = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) :=
      ⟨pullback.lift a _ (ha.trans (gPt_j u)), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    exact ⟨x, l, c, hx, fun y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hl hy) k, hw⟩
  choose x l c hx hl hw using hC
  refine hilb_le C d _ (fun n w => c w ^ d * valR (x w) _ ((b n).f (l w))) fun α hα => ?_
  obtain ⟨s, hs⟩ := exists_monomial u.U.LG.L (pullback.fst u.G.hom (jK u.V)) S.N d σ α hα
  obtain ⟨e, he, -⟩ := hb s
  refine ⟨fun n => algebraMap _ _ (e n), fun w => ?_⟩
  have h := congrArg (CrdCalc.valHom (x w) _ (hl w)) ((hs (l w)).symm.trans (he (l w)))
  replace h := (map_prod _ _ _).symm.trans (h.trans (map_sum _ _ _))
  simp only [hw w, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hα]
  refine Eq.trans ?_ ((congrArg (c w ^ d * ·) h).trans ?_)
  · refine congrArg (c w ^ d * ·) (Finset.prod_congr rfl fun i _ => Eq.symm ((map_pow _ _ _).trans ?_))
    exact congrArg (· ^ α i) ((CrdCalc.valR_eq _ _ (hl w) _).symm.trans (valR_appLE _ _ _ _ _ _ (hl w)))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => Eq.trans (congrArg (c w ^ d * ·) ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (CrdCalc.valR_eq _ _ (hl w) _).symm))) (mul_left_comm _ _ _)
  exact (CrdCalc.valR_eq _ _ (hl w) _).symm.trans (valR_scal _ (x w) _ (hx w) _ (hl w) (e n))

end GlobalTheory.ZH.FormCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegreeFormsDimensionGenericFibreLeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degreeFormsDimension_genericFibre_le : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (J : Type) [Fintype J] (σ : J → (u.H S.N).Sec) (d : ℕ), 1 ≤ d → hilb {w : J → PadicAlgCl p | ∃ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j ∧ Crd (u.H S.N) σ a w} d ≤ (S.N * d) ^ S.g := by
  first | exact @GlobalTheory.ZH.FormCount.hilb_generic_le | exact GlobalTheory.ZH.FormCount.hilb_generic_le | (intros; apply GlobalTheory.ZH.FormCount.hilb_generic_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreEqSpecialFibreOfReductionIndep
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreEqSpecialFibreOfReductionIndep
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.fib_of_indep : ∀ C : Core, C.Indep → C.Fib := by
  intro C hI p _ y τ x hx
  obtain ⟨-, hlft, -, hint, hflat, -, -, -, -, -, -, hdom, htest⟩ := GlobalTheory.T.abelianSchemeProperClosureData_basic_properties C
  have := C.lft
  have hne : ((C.GG.hom ⁻¹ᵁ C.U : C.G.toScheme.Opens) : Set C.G.toScheme).Nonempty := by
    obtain ⟨w, hw⟩ := hdom.denseRange.exists_mem_open C.U.isOpen C.ne
    exact ⟨w, hw⟩
  have hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π) := inferInstance
  obtain ⟨b', hb'x, hb'U⟩ :=
    (@GlobalTheory.T.exists_classical_point_lifting_residue_point C.G.toScheme hint (C.GG.hom ≫ C.π) hflat hlft' (C.GG.hom ⁻¹ᵁ C.U) hne p _).1 x
  have hcl : C.Cl (b' ≫ C.GG.hom) := by
    rintro _ ⟨s, rfl⟩
    have := hb'U ⟨s, rfl⟩
    rw [← Category.assoc, Scheme.Hom.comp_apply]
    exact this
  obtain ⟨b, hby, hbx⟩ := hI p (b' ≫ C.GG.hom) y hcl (htest p y τ).1
    (by rw [← Category.assoc, hb'x, hx]) b' rfl
  obtain ⟨c, hc, hcb⟩ := τ.lift b hby
  refine ⟨rPt p ≫ c, by rw [Category.assoc, hc], ?_⟩
  rw [Category.assoc, hcb, hbx, hb'x]

end GlobalTheory.ZJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreEqSpecialFibreOfReductionIndepStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_eq_specialFibre_of_reduction_indep : ∀ C : Core, C.Indep → C.Fib := by
  first | exact @GlobalTheory.ZJ.Core.fib_of_indep | exact GlobalTheory.ZJ.Core.fib_of_indep | (intros; apply GlobalTheory.ZJ.Core.fib_of_indep <;> assumption)
end
end
