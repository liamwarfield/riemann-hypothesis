module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsAmpleHermLineBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerPresentationCotangentPullbackResRigi

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDef
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDef
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RosatiTens

open GlobalTheory.CechPic

section Bilinear

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Over S}
variable {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen)
include hΘ

def lamLeft (z : X ⟶ G) : (X ⟶ G) →* Multiplicative (Pic X.left) where
  toFun x := Multiplicative.ofAdd (lam (cls L hL) x z)
  map_one' := by rw [lam_one_left]; rfl
  map_mul' x y := by rw [lam_mul_left hL hΘ]; rfl

theorem lam_prod_left {κ : Type} [Fintype κ] (x : κ → (X ⟶ G)) (n : κ → ℤ) (z : X ⟶ G) :
    lam (cls L hL) (∏ i, x i ^ n i) z = ∑ i, n i • lam (cls L hL) (x i) z := by
  have h := congrArg Multiplicative.toAdd (map_prod (lamLeft hL hΘ z) (fun i => x i ^ n i) Finset.univ)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  exact h

theorem lam_prod_right {κ : Type} [Fintype κ] (x : X ⟶ G) (z : κ → (X ⟶ G)) (n : κ → ℤ) :
    lam (cls L hL) x (∏ i, z i ^ n i) = ∑ i, n i • lam (cls L hL) x (z i) := by
  rw [lam_comm, lam_prod_left hL hΘ]
  simp only [lam_comm _ (z _) x]

theorem lam_mul_right (x y z : X ⟶ G) :
    lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm _ y, lam_comm _ z]

end Bilinear

section Tensor

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def pairP (T : Tens D D' W) (M : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    Pic X.left :=
  ∑ i, ∑ j, M i j • lam (cls D.P.L D.P.isLB) (u ≫ T.pr i) (v ≫ T.pr j)

theorem cls_tens (T : Tens D D' W) :
    cls D'.P.L D'.P.isLB = ∑ i, ∑ j, W i j • lam (cls D.P.L D.P.isLB) (T.pr i) (T.pr j) := by
  have hC := LB.isLB_linComb D.P.isLB (tensφ T.pr) (tensε W)
  refine ((cls_eq_iff D'.P.isLB hC).2 ⟨T.w, T.w_gen⟩).trans ?_
  rw [cls_linComb D.P.isLB, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, lam, mul_smul, ← smul_add]
  congr 1
  simp
  abel

theorem pull_tens (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} (h : X ⟶ D'.P.A) :
    pull h.left (cls D'.P.L D'.P.isLB) = pairP T W h h := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cls_tens T, pairP, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, pull_lam]

end Tensor

end GlobalTheory.Mum.RosatiTens

namespace GlobalTheory.Mum.RosatiTens

open GlobalTheory.CechPic

section Tensor2

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem pairP_mul (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    pairP T W (u * v) (u * v) = pairP T W u u + pairP T W v v + pairP T (W + W.transpose) u v := by
  have hm : ∀ i, (u * v) ≫ T.pr i = u ≫ T.pr i * v ≫ T.pr i := fun i => by
    haveI := T.pr_hom i
    exact MonObj.mul_comp _ _ _
  have hΘ : ∃ t : LB.Gen (Theta D.P.A D.P.L), t.IsGen := ⟨D.cub.t, D.cub.isGen⟩
  have e : ∑ i, ∑ j, W i j • lam (cls D.P.L D.P.isLB) (v ≫ T.pr i) (u ≫ T.pr j) =
      ∑ i, ∑ j, W.transpose i j • lam (cls D.P.L D.P.isLB) (u ≫ T.pr i) (v ≫ T.pr j) := by
    rw [Finset.sum_comm]
    simp only [Matrix.transpose_apply, lam_comm _ (v ≫ _)]
  simp only [pairP, hm, lam_mul_left D.P.isLB hΘ, lam_mul_right D.P.isLB hΘ, smul_add, Finset.sum_add_distrib,
    Matrix.add_apply, add_smul]
  rw [e]
  abel

def pre {X Y Z : Over (Spec (CommRingCat.of R))} [GrpObj Z] (u : X ⟶ Y) : (Y ⟶ Z) →* (X ⟶ Z) where
  toFun f := u ≫ f
  map_one' := by simp [Hom.one_def]
  map_mul' f g := MonObj.comp_mul u f g

theorem comp_act_pr (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} (u : X ⟶ D'.P.A)
    (m : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    (u ≫ T.act m) ≫ T.pr i = ∏ k, (u ≫ T.pr k) ^ m i k := by
  rw [Category.assoc, Tens.act_pr]
  exact (map_prod (pre (Z := D.P.A) u) _ _).trans (Finset.prod_congr rfl fun k _ => map_zpow (pre (Z := D.P.A) u) _ _)

theorem pairP_act_left (T : Tens D D' W) (M m : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) : pairP T M (u ≫ T.act m) v = pairP T (m.transpose * M) u v := by
  have hΘ : ∃ t : LB.Gen (Theta D.P.A D.P.L), t.IsGen := ⟨D.cub.t, D.cub.isGen⟩
  simp only [pairP, comp_act_pr, lam_prod_left D.P.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem pairP_act_right (T : Tens D D' W) (M m : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) : pairP T M u (v ≫ T.act m) = pairP T (M * m) u v := by
  have hΘ : ∃ t : LB.Gen (Theta D.P.A D.P.L), t.IsGen := ⟨D.cub.t, D.cub.isGen⟩
  simp only [pairP, comp_act_pr, lam_prod_right D.P.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

end Tensor2

end GlobalTheory.Mum.RosatiTens

namespace GlobalTheory.Mum.RosatiTens

open GlobalTheory.CechPic

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem symUnit_mul_star (h : IsUnit (W + W.transpose).det) (a : TensO (symUnitOf W h)) :
    (W + W.transpose) * TensO.mat _ (star a) = (TensO.mat _ a).transpose * (W + W.transpose) := by
  have hb : (((symUnitOf W h).1 : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose := rfl
  rw [TensO.star_def]
  show (W + W.transpose) * ((((symUnitOf W h).1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
    (TensO.mat _ a).transpose * (((symUnitOf W h).1 : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ)) = _
  rw [← hb, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem rosatiAdj_core (T : Tens D D' W) (h : IsUnit (W + W.transpose).det) (a : TensO (symUnitOf W h)) :
    RosatiAdj D'.P.A D'.P.L (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) := by
  intro s
  refine ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb D'.P.isLB _ _)).1 ?_⟩
  rw [cls_linComb D'.P.isLB]
  let f := T.act (TensO.mat _ a)
  let g := T.act (TensO.mat _ (star a))
  let H : Fin 6 → (D'.P.A ⊗ D'.P.A ⟶ D'.P.A) := ![fst _ _ ≫ f * snd _ _, fst _ _ ≫ f, snd _ _,
    fst _ _ * snd _ _ ≫ g, fst _ _, snd _ _ ≫ g]
  have hH : rosatiφ D'.P.A f g = fun k => (H k).left := by
    funext k
    fin_cases k <;> simp [rosatiφ, H, padd, Hom.mul_def]
  have key : ∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB) = 0 := by
    simp only [hH, pull_tens T]
    simp only [Fin.sum_univ_six, H, rosatiε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
    rw [pairP_mul, pairP_mul]
    rw [pairP_act_left T (W + W.transpose) (TensO.mat _ a) (fst _ _) (snd _ _),
      pairP_act_right T (W + W.transpose) (TensO.mat _ (star a)) (fst _ _) (snd _ _), symUnit_mul_star]
    simp only [one_smul, neg_smul]
    abel
  calc ∑ k, rosatiε k • pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι ≫ rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)
      = pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι)
          (∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [pull_comp, map_sum, map_zsmul]
    _ = 0 := by rw [key, map_zero]

end GlobalTheory.Mum.RosatiTens


open GlobalTheory.Mum.RosatiTens in
theorem GlobalTheory.Mum.rosatiAdj_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W) (a : TensO (symUnitOf W h)), RosatiAdj D'.toPre.P.A D'.toPre.P.L (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) := by
  intro R _ _ _ _ D D' r W h _ T a
  exact rosatiAdj_core T h a
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDefStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiAdj_mumfordTensorPower_of_posDef : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W) (a : TensO (symUnitOf W h)), RosatiAdj D'.toPre.P.A D'.toPre.P.L (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) := by
  first | exact @GlobalTheory.Mum.rosatiAdj_tens | exact GlobalTheory.Mum.rosatiAdj_tens | (intros; apply GlobalTheory.Mum.rosatiAdj_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAndIsRelParam
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingOfFlatOfMapComapMaximalIdeal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem isRegularLocalRing_of_flat_of_map_comap_maximalIdeal (V : Type) [CommRing V]
    [IsRegularLocalRing V] (I : Type) [Fintype I] (S : Type) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (φ : MvPolynomial I V →+* S) (hflat : φ.Flat)
    (hmap : ((maximalIdeal S).comap φ).map φ = maximalIdeal S) : IsRegularLocalRing S := by
  haveI : IsRegularRing V := GlobalTheory.isRegularRing_of_isRegularLocalRing V
  set q : Ideal (MvPolynomial I V) := (maximalIdeal S).comap φ with hq
  haveI : q.IsPrime := Ideal.comap_isPrime φ (maximalIdeal S)
  let L := Localization.AtPrime q
  haveI : IsRegularLocalRing L := IsRegularRing.isRegularLocalRing_localization q
  have hu : ∀ y : q.primeCompl, IsUnit (φ y) := by
    intro y
    by_contra h
    exact y.2 ((mem_maximalIdeal _).2 h)
  let χ : L →+* S := IsLocalization.lift (M := q.primeCompl) hu
  letI : Algebra (MvPolynomial I V) S := φ.toAlgebra
  letI : Algebra L S := χ.toAlgebra
  haveI : IsScalarTower (MvPolynomial I V) L S := IsScalarTower.of_algebraMap_eq (fun a => by
    change φ a = χ (algebraMap _ L a)
    exact (IsLocalization.lift_eq (M := q.primeCompl) hu a).symm)
  haveI : Module.Flat (MvPolynomial I V) S := hflat
  haveI : IsLocalizedModule q.primeCompl (LinearMap.id : S →ₗ[MvPolynomial I V] S) :=
    isLocalizedModule_id q.primeCompl S L
  haveI : Module.Flat L S :=
    Module.Flat.of_isLocalizedModule L q.primeCompl (LinearMap.id : S →ₗ[MvPolynomial I V] S)
  have hm : maximalIdeal S = (maximalIdeal L).map (algebraMap L S) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact hmap.symm
  exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal L S (maximalIdeal L) hm

theorem isRegularLocalRing_quotient_of_isComplAt :
    ∀ (W : Type) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] (I : Type) [Fintype I] (R : Type) [CommRing R]
      [IsLocalRing R] (ψ : MvPolynomial I W →+* R), IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) →
      ∀ 𝔭 : Ideal W, 𝔭 ≠ ⊤ → IsRegularLocalRing (W ⧸ 𝔭) →
        IsRegularLocalRing (R ⧸ 𝔭.map (ψ.comp MvPolynomial.C)) := by
  intro W _ _ _ I _ R _ _ ψ hψ hloc 𝔭 h𝔭 hreg
  obtain ⟨hnoeth, -, hflat, hmap, -⟩ := hψ
  haveI : IsNoetherianRing R := hnoeth
  haveI : IsRegularLocalRing (W ⧸ 𝔭) := hreg
  rw [← Ideal.map_map]
  set J : Ideal R := (Ideal.map MvPolynomial.C 𝔭).map ψ with hJ
  have hJm : J ≤ maximalIdeal R := by
    rw [hJ, Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact h𝔭 (Ideal.eq_top_of_isUnit_mem _ hx (isUnit_of_map_unit _ _ hu))
  haveI : Nontrivial (R ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJm)
  haveI : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let e := MvPolynomial.quotientEquivQuotientMvPolynomial (σ := I) 𝔭
  have heC : ∀ a : W, e (MvPolynomial.C (Ideal.Quotient.mk 𝔭 a)) = Ideal.Quotient.mk _ (MvPolynomial.C a) := by
    intro a; simp [e, MvPolynomial.quotientEquivQuotientMvPolynomial]
  have heX : ∀ i : I, e (MvPolynomial.X i) = Ideal.Quotient.mk _ (MvPolynomial.X i) := by
    intro i; simp [e, MvPolynomial.quotientEquivQuotientMvPolynomial]
  let ψ' : MvPolynomial I (W ⧸ 𝔭) →+* R ⧸ J :=
    (Ideal.quotientMap J ψ Ideal.le_comap_map).comp e.toRingEquiv.toRingHom
  have hflat' : ψ'.Flat :=
    (RingHom.Flat.of_bijective e.bijective).comp (GlobalTheory.Pat.flat_quotientMap_map ψ hflat _)
  let π : MvPolynomial I W →+* MvPolynomial I (W ⧸ 𝔭) := MvPolynomial.map (Ideal.Quotient.mk 𝔭)
  have hcomm : ψ'.comp π = (Ideal.Quotient.mk J).comp ψ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, π, MvPolynomial.map_C, ψ']
      change Ideal.quotientMap J ψ Ideal.le_comap_map (e (MvPolynomial.C (Ideal.Quotient.mk 𝔭 a))) = _
      rw [heC, Ideal.quotientMap_mk]
    · intro i
      simp only [RingHom.comp_apply, π, MvPolynomial.map_X, ψ']
      change Ideal.quotientMap J ψ Ideal.le_comap_map (e (MvPolynomial.X i)) = _
      rw [heX, Ideal.quotientMap_mk]
  have hmax : maximalIdeal (R ⧸ J) = (maximalIdeal R).map (Ideal.Quotient.mk J) := by
    exact (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
  refine isRegularLocalRing_of_flat_of_map_comap_maximalIdeal (W ⧸ 𝔭) I (R ⧸ J) ψ' hflat' ?_
  refine le_antisymm Ideal.map_comap_le ?_
  have h1 : maximalIdeal (R ⧸ J) = (((maximalIdeal R).comap ψ).map π).map ψ' := by
    rw [hmax, Ideal.map_map, hcomm, ← Ideal.map_map, hmap]
  refine h1.le.trans (Ideal.map_mono ?_)
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hcomm, ← Ideal.comap_comap]
  apply Ideal.comap_mono
  rw [hmax]
  exact Ideal.le_comap_map

end GlobalTheory.TChart
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart


set_option backward.isDefEq.respectTransparency false in
theorem Taut.isRegularLocalRing_and_isRelParam : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → ∀ C : Taut (zetaAway n) g n φ, IsRegularLocalRing C.R ∧ CharZero C.R ∧ Function.Injective C.b ∧ C.b.Flat ∧ IsRelParam C.b C.t ∧ IsRegularLocalRing (C.R ⧸ ((maximalIdeal C.R).comap C.b).map C.b) := by
  intro g n φ _ C
  haveI : IsNoetherianRing C.W := C.noeth
  haveI : IsLocalHom C.iw := C.ψ_loc
  set X := (LowChart.powA C.F C.T.r).left with hX
  set π := LowChart.toO C.F C.T.r with hπ
  set y := C.u (closedPoint C.W) with hy
  let φ₀ : X.presheaf.stalk y →+* C.W := (Scheme.stalkClosedPointTo C.u).hom
  let σ := (π.stalkMap y).hom
  let L := Localization.AtPrime (π y).asIdeal
  let e := Spec.stalkIso (CommRingCat.of (cycAway n)) (π y)
  let ρ : cycAway n →+* X.presheaf.stalk y := σ.comp (e.inv.hom.comp (algebraMap (cycAway n) L))
  have h3 : (Sp (cycAway n)).fromSpecStalk (π y) = Spec.map e.inv ≫ spMap (algebraMap (cycAway n) L) := by
    refine (Spec.fromSpecStalk_eq (CommRingCat.of _) (π y)).trans ?_
    rw [spMap, ← Spec.map_comp]
    exact congrArg Spec.map (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of _) (x := π y)).symm
  have hb : C.T.b = φ₀.comp ρ := by
    have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk C.u
    have h2 := Scheme.SpecMap_stalkMap_fromSpecStalk π (x := y)
    have key : spMap C.T.b = spMap (φ₀.comp ρ) := by
      rw [← C.u_base, ← h1, Category.assoc, ← h2, h3]
      simp only [spMap, ρ, φ₀, σ, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  have hq : (π y).asIdeal = (maximalIdeal C.W).comap C.T.b := by
    have : π y = spMap C.T.b (closedPoint C.W) := by
      rw [hy, ← C.u_base, Scheme.Hom.comp_apply]
    rw [this]; rfl
  haveI : IsRegularLocalRing (X.presheaf.stalk y) := LowChart.isRegularLocalRing_stalk C.F y
  have het := C.u_et
  haveI hW : IsRegularLocalRing C.W := by
    letI : Algebra (X.presheaf.stalk y) C.W := φ₀.toAlgebra
    haveI : Module.Flat (X.presheaf.stalk y) C.W := het.1
    exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal _ _ (maximalIdeal _) het.2.1.symm
  obtain ⟨hRreg, hRdom⟩ := isRegularLocalRing_and_isDomain_of_isComplAt C.W (Fin C.m ⊕ Fin C.N) C.R C.ψ C.compl C.ψ_loc
  have hρspec : spMap ρ = X.fromSpecStalk y ≫ π := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk π (x := y), h3]
    simp only [spMap, ρ, σ, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
  have hflatρ : ρ.Flat := by
    haveI := GlobalTheory.SmoothStalkNormal.flat_fromSpecStalk' X y
    have h : Flat (spMap ρ) := by rw [hρspec]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).1 h
  have hiwflat : C.iw.Flat :=
    (show (algebraMap C.W (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W)).Flat from
      RingHom.flat_algebraMap_iff.mpr inferInstance).comp C.compl.2.2.1
  have hbeq : C.b = C.iw.comp (φ₀.comp ρ) := by rw [← hb]; rfl
  have hbflat : C.b.Flat := by rw [hbeq]; exact (hflatρ.comp het.1).comp hiwflat
  have hinj : Function.Injective C.b := GlobalTheory.SmoothStalkNormal.injective_of_flat_of_isDomain C.b hbflat
  have hmW : (maximalIdeal C.R).comap C.iw = maximalIdeal C.W := IsLocalRing.maximalIdeal_comap C.iw
  have h𝔮 : (maximalIdeal C.R).comap C.b = (π y).asIdeal := by
    rw [hq, show C.b = C.iw.comp C.T.b from rfl, ← Ideal.comap_comap, hmW]
  have hle : ((maximalIdeal C.R).comap C.b).map C.b ≤ (maximalIdeal C.W).map (C.ψ.comp MvPolynomial.C) := by
    rw [show C.b = C.iw.comp C.T.b from rfl, ← Ideal.map_map]
    refine Ideal.map_mono (Ideal.map_le_iff_le_comap.2 ?_)
    rw [← Ideal.comap_comap, hmW]
  refine ⟨hRreg, charZero_of_injective_ringHom hinj, hinj, hbflat, ⟨fun k => C.bd k, fun c hc k =>
    cotangent_indep_of_isComplAt C.W _ C.R C.ψ C.compl C.ψ_loc C.m ⟨Sum.inl, Sum.inl_injective⟩ (fun k => C.bd k) c
      (sup_le_sup_left hle (maximalIdeal C.R ^ 2) hc) k⟩, ?_⟩
  have hfib := GlobalTheory.FibreRegular.isRegularLocalRing_stalk_quot_maximalIdeal (Sp (cycAway n)) X π y
  set I := (maximalIdeal ((Sp (cycAway n)).presheaf.stalk (π y))).map σ with hIdef
  have hI : I = (π y).asIdeal.map ρ := by
    have hsurj : Function.Surjective e.inv.hom := e.commRingCatIsoToRingEquiv.symm.surjective
    have hmL : maximalIdeal ((Sp (cycAway n)).presheaf.stalk (π y)) = (maximalIdeal L).map e.inv.hom :=
      (IsLocalRing.map_maximalIdeal_of_surjective _ hsurj).symm
    rw [hIdef, hmL, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map]
    rfl
  set 𝔭 := I.map φ₀ with h𝔭def
  have h𝔭 : 𝔭.map C.iw = ((maximalIdeal C.R).comap C.b).map C.b := by
    rw [h𝔭def, hI, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, ← hbeq, h𝔮]
  have hIm : I ≤ maximalIdeal (X.presheaf.stalk y) :=
    Ideal.map_le_iff_le_comap.2 (IsLocalRing.maximalIdeal_comap σ).ge
  have h𝔭m : 𝔭 ≤ maximalIdeal C.W := het.2.1 ▸ Ideal.map_mono hIm
  have h𝔭ne : 𝔭 ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top h𝔭m
  haveI : Nontrivial (C.W ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.2 h𝔭ne
  haveI : IsLocalRing (C.W ⧸ 𝔭) := IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔭) Ideal.Quotient.mk_surjective
  have hreg𝔭 : IsRegularLocalRing (C.W ⧸ 𝔭) := by
    let χ : (X.presheaf.stalk y ⧸ I) →+* (C.W ⧸ 𝔭) := Ideal.quotientMap 𝔭 φ₀ Ideal.le_comap_map
    have hχflat : χ.Flat := GlobalTheory.Pat.flat_quotientMap_map φ₀ het.1 I
    letI : Algebra (X.presheaf.stalk y ⧸ I) (C.W ⧸ 𝔭) := χ.toAlgebra
    haveI : Module.Flat (X.presheaf.stalk y ⧸ I) (C.W ⧸ 𝔭) := hχflat
    have hcomm : (Ideal.Quotient.mk 𝔭).comp φ₀ = χ.comp (Ideal.Quotient.mk I) := by
      ext a; simp [χ]
    have hmax : maximalIdeal (C.W ⧸ 𝔭) = (maximalIdeal (X.presheaf.stalk y ⧸ I)).map (algebraMap _ _) := by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk 𝔭) Ideal.Quotient.mk_surjective, ← het.2.1,
        ← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, Ideal.map_map,
        Ideal.map_map, hcomm]
      rfl
    exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal _ _ _ hmax
  have hfin := isRegularLocalRing_quotient_of_isComplAt C.W _ C.R C.ψ C.compl C.ψ_loc 𝔭 h𝔭ne hreg𝔭
  rwa [show C.ψ.comp MvPolynomial.C = C.iw from rfl, h𝔭] at hfin

end GlobalTheory.TChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsumLeftPull
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam.AdjComp

section Iso

variable {X : Scheme.{0}}

theorem gm_iso {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z)
    (i j : B.ι × A.ι) (hi : f z ∈ B.U i.1 ⊓ A.U i.2) (hj : f z ∈ B.U j.1 ⊓ A.U j.2) :
    gm f z (B.U i.1 ⊓ A.U i.2) (w.s i) =
      gm f z (B.U i.1 ⊓ B.U j.1) (B.g i.1 j.1) * (gm f z (A.U i.2 ⊓ A.U j.2) (A.g i.2 j.2))⁻¹ *
        gm f z (B.U j.1 ⊓ A.U j.2) (w.s j) := by
  have hm : f z ∈ B.U i.1 ⊓ A.U i.2 ⊓ (B.U j.1 ⊓ A.U j.2) := ⟨hi, hj⟩
  have e := congrArg (gm f z (B.U i.1 ⊓ A.U i.2 ⊓ (B.U j.1 ⊓ A.U j.2))) (hw i j)
  exact (gm_res f z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div A B f z i j hm) (gm_res f z _ hm _))))

variable {A B C : LB X}

theorem exists_comp (hA : A.IsLB) (hB : B.IsLB) (hC : C.IsLB) (w₁ : LB.Iso A B) (hw₁ : w₁.IsGen)
    (w₂ : LB.Iso B C) (hw₂ : w₂.IsGen) :
    ∃ w : LB.Iso A C, w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (r : C.ι) (p : B.ι) (q : A.ι),
      f z ∈ C.U r → f z ∈ B.U p → f z ∈ A.U q →
      gm f z (C.U r ⊓ A.U q) (w.s (r, q)) =
        gm f z (C.U r ⊓ B.U p) (w₂.s (r, p)) * gm f z (B.U p ⊓ A.U q) (w₁.s (p, q)) := by
  have glue : ∀ (r : C.ι) (q : A.ι), ∃ s : Γ(X, C.U r ⊓ A.U q)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z)
      (p : B.ι), f z ∈ C.U r → f z ∈ B.U p → f z ∈ A.U q →
      gm f z _ s = gm f z (C.U r ⊓ B.U p) (w₂.s (r, p)) * gm f z (B.U p ⊓ A.U q) (w₁.s (p, q)) := by
    intro r q
    let W : B.ι → X.Opens := fun p => C.U r ⊓ A.U q ⊓ B.U p
    have l₀ : ∀ p, W p ≤ C.U r ⊓ A.U q := fun p => inf_le_left
    have l₂ : ∀ p, W p ≤ C.U r ⊓ B.U p := fun p x hx => ⟨hx.1.1, hx.2⟩
    have l₁ : ∀ p, W p ≤ B.U p ⊓ A.U q := fun p x hx => ⟨hx.2, hx.1.2⟩
    let u : ∀ p, Γ(X, W p)ˣ := fun p => res (l₂ p) (w₂.s (r, p)) * res (l₁ p) (w₁.s (p, q))
    have hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (p : B.ι) (hz : f z ∈ W p),
        gm f z (W p) (u p) = gm f z (C.U r ⊓ B.U p) (w₂.s (r, p)) * gm f z (B.U p ⊓ A.U q) (w₁.s (p, q)) :=
      fun Z f z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z (l₂ p) hz _) (gm_res f z (l₁ p) hz _))
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨p, hp⟩ := exists_chart hB x
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hx, hp⟩) u (fun p p' x hx => by
        rw [hu _ (𝟙 X) x p hx.1, hu _ (𝟙 X) x p' hx.2]
        have a₂ := gm_iso hw₂ (𝟙 X) x (r, p) (r, p') ⟨hx.1.1.1, hx.1.2⟩ ⟨hx.2.1.1, hx.2.2⟩
        have a₁ := gm_iso hw₁ (𝟙 X) x (p, q) (p', q) ⟨hx.1.2, hx.1.1.2⟩ ⟨hx.2.2, hx.2.1.2⟩
        rw [a₂, a₁, gm_self hC (𝟙 X) x hx.1.1.1, gm_self hA (𝟙 X) x hx.1.1.2]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
    refine ⟨s, fun Z f z p hr hp hq => ?_⟩
    have hy : f z ∈ W p := ⟨⟨hr, hq⟩, hp⟩
    exact (gm_res f z (l₀ p) hy s).symm.trans ((congrArg (gm f z (W p)) (hs p)).trans (hu Z f z p hy))
  choose s hs using glue
  refine ⟨⟨fun rq => s rq.1 rq.2⟩, fun i j => unit_ext fun x hx => ?_, fun Z f z r p q hr hp hq => hs r q Z f z p hr hp hq⟩
  obtain ⟨p, hp⟩ := exists_chart hB x
  have e₁ := hs i.1 i.2 _ (𝟙 X) x p hx.1.1 hp hx.1.2
  have e₂ := hs j.1 j.2 _ (𝟙 X) x p hx.2.1 hp hx.2.2
  have a₂ := gm_iso hw₂ (𝟙 X) x (i.1, p) (j.1, p) ⟨hx.1.1, hp⟩ ⟨hx.2.1, hp⟩
  have a₁ := gm_iso hw₁ (𝟙 X) x (p, i.2) (p, j.2) ⟨hp, hx.1.2⟩ ⟨hp, hx.2.2⟩
  refine (gm_res (𝟙 X) x _ hx _).trans (e₁.trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  refine (congrArg₂ (· * ·) (gm_div A C (𝟙 X) x i j hx) ((gm_res (𝟙 X) x _ hx _).trans e₂)).trans ?_
  rw [a₂, a₁, gm_self hB (𝟙 X) x hp]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

end Iso

section Pull

variable {Y Y' : Scheme.{0}} {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y}

theorem pullIso_le (a : ChartPull A' A h) (b : ChartPull B' B h) (p : B'.ι × A'.ι) :
    B'.U p.1 ⊓ A'.U p.2 ≤ h ⁻¹ᵁ (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) :=
  fun _ hy => ⟨b.le _ hy.1, a.le _ hy.2⟩

def pullIso (a : ChartPull A' A h) (b : ChartPull B' B h) (w : LB.Iso A B) : LB.Iso A' B' :=
  ⟨fun p => res (pullIso_le a b p) (pullU h _ (w.s (b.idx p.1, a.idx p.2)))⟩

theorem gm_pullIso (a : ChartPull A' A h) (b : ChartPull B' B h) (w : LB.Iso A B) {Z : Scheme.{0}} (r : Z ⟶ Y')
    (z : Z) (p : B'.ι × A'.ι) (hp : r z ∈ B'.U p.1 ⊓ A'.U p.2) :
    gm r z (B'.U p.1 ⊓ A'.U p.2) ((pullIso a b w).s p) =
      gm (r ≫ h) z (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (w.s (b.idx p.1, a.idx p.2)) :=
  (gm_res r z (pullIso_le a b p) hp _).trans (gm_pull r h z (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (pullIso_le a b p hp) _)

theorem pullIso_isGen (a : ChartPull A' A h) (b : ChartPull B' B h) {w : LB.Iso A B} (hw : w.IsGen) :
    (pullIso a b w).IsGen := fun p q => unit_ext fun y hy => by
  have hp : (𝟙 Y' ≫ h) y ∈ B.U (b.idx p.1) ⊓ A.U (a.idx p.2) := ⟨b.le _ hy.1.1, a.le _ hy.1.2⟩
  have hq : (𝟙 Y' ≫ h) y ∈ B.U (b.idx q.1) ⊓ A.U (a.idx q.2) := ⟨b.le _ hy.2.1, a.le _ hy.2.2⟩
  have l := gm_iso hw (𝟙 Y' ≫ h) y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2) hp hq
  have e₁ := (gm_res (𝟙 Y') y inf_le_left hy _).trans (gm_pullIso a b w (𝟙 Y') y p hy.1)
  have e₂ := (gm_res (𝟙 Y') y inf_le_right hy _).trans (gm_pullIso a b w (𝟙 Y') y q hy.2)
  refine e₁.trans (l.trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  refine (congrArg₂ (· * ·) (gm_div A' B' (𝟙 Y') y p q hy) e₂).trans ?_
  rw [b.g y _ _ hy.1.1 hy.2.1, a.g y _ _ hy.1.2 hy.2.2, Category.id_comp]

end Pull

end GlobalTheory.MumFam.AdjComp

namespace GlobalTheory.MumFam.AdjComp

theorem psum_left_pull {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (m : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (hx : ∀ i, x' i = m ≫ x i) (I : ULift (Finset (Fin n))) :
    (psum G x' I.down).left = m.left ≫ (psum G x I.down).left := by
  obtain rfl : x' = fun i => m ≫ x i := funext hx
  rw [← Over.comp_left, comp_psum]

def cubePull {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (L : LB G.left) (m : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (hx : ∀ i, x' i = m ≫ x i) :
    ChartPull (cubeLB G x' L) (cubeLB G x L) m.left :=
  chartPullSame L _ _ _ m.left (psum_left_pull m x x' hx)

theorem adjVal_of {S : Scheme.{0}} {T G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} {x₁ : Fin 2 → (T ⟶ G₁)} {x₂ : Fin 2 → (T ⟶ G₂)}
    (w : LB.Iso (cubeLB G₂ x₂ L₂) (cubeLB G₁ x₁ L₁)) {Z : Scheme.{0}} (p : Z ⟶ T.left) (z : Z)
    (J₁ : (Z ⟶ G₁.left) → L₁.ι) (J₂ : (Z ⟶ G₂.left) → L₂.ι) (j₁ : ULift (Finset (Fin 2)) → L₁.ι)
    (j₂ : ULift (Finset (Fin 2)) → L₂.ι) (h₁ : ∀ I, J₁ (p ≫ (psum G₁ x₁ I.down).left) = j₁ I)
    (h₂ : ∀ I, J₂ (p ≫ (psum G₂ x₂ I.down).left) = j₂ I) :
    adjVal w p z J₁ J₂ = gm p z ((cubeLB G₁ x₁ L₁).U j₁ ⊓ (cubeLB G₂ x₂ L₂).U j₂) (w.s (j₁, j₂)) := by
  obtain rfl : (fun I : ULift (Finset (Fin 2)) => J₁ (p ≫ (psum G₁ x₁ I.down).left)) = j₁ := funext h₁
  obtain rfl : (fun I : ULift (Finset (Fin 2)) => J₂ (p ≫ (psum G₂ x₂ I.down).left)) = j₂ := funext h₂
  rfl

end GlobalTheory.MumFam.AdjComp

namespace GlobalTheory.MumFam


open AdjComp in
theorem Adj.comp : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ Q₃ : Data R) (a : Q₁.B ⟶ Q₂.B) (a' : Q₂.B ⟶ Q₁.B)
    (h : Q₁.X →+ Q₂.X) (h' : Q₂.X →+ Q₁.X) (b : Q₂.B ⟶ Q₃.B) (b' : Q₃.B ⟶ Q₂.B) (k : Q₂.X →+ Q₃.X)
    (k' : Q₃.X →+ Q₂.X), Adj Q₁ Q₂ a a' h h' → Adj Q₂ Q₃ b b' k k' →
      Adj Q₁ Q₃ (a ≫ b) (b' ≫ a') (k.comp h) (h'.comp k') := by
  intro R _ _ Q₁ Q₂ Q₃ a a' h h' b b' k k' H₁ H₂
  obtain ⟨ma, ma', ca, ca', w₁₂, g₁₂, V₁₂⟩ := H₁
  obtain ⟨mb, mb', cb, cb', w₂₃, g₂₃, V₂₃⟩ := H₂
  let m₁ : Q₁.B ⊗ Q₃.B ⟶ Q₂.B ⊗ Q₃.B := lift (fst _ _ ≫ a) (snd _ _)
  let m₂ : Q₁.B ⊗ Q₃.B ⟶ Q₁.B ⊗ Q₂.B := lift (fst _ _) (snd _ _ ≫ b')
  have xA : ∀ i, (![fst Q₁.B Q₃.B ≫ a ≫ b, snd Q₁.B Q₃.B] : Fin 2 → _) i = m₁ ≫ (![fst Q₂.B Q₃.B ≫ b, snd Q₂.B Q₃.B] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₁]
  have xB₁ : ∀ i, (![fst Q₁.B Q₃.B ≫ a, snd Q₁.B Q₃.B ≫ b'] : Fin 2 → _) i = m₁ ≫ (![fst Q₂.B Q₃.B, snd Q₂.B Q₃.B ≫ b'] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₁]
  have xB₂ : ∀ i, (![fst Q₁.B Q₃.B ≫ a, snd Q₁.B Q₃.B ≫ b'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  have xC : ∀ i, (![fst Q₁.B Q₃.B, snd Q₁.B Q₃.B ≫ b' ≫ a'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  let cA := cubePull Q₃.M.L m₁ _ _ xA
  let cB₁ := cubePull Q₂.M.L m₁ _ _ xB₁
  let cB₂ := cubePull Q₂.M.L m₂ _ _ xB₂
  let cC := cubePull Q₁.M.L m₂ _ _ xC
  have lA : (cubeLB Q₃.B ![fst Q₁.B Q₃.B ≫ a ≫ b, snd Q₁.B Q₃.B] Q₃.M.L).IsLB := DVR.linComb_isLB _ Q₃.M.isLB _ _
  have lB : (cubeLB Q₂.B ![fst Q₁.B Q₃.B ≫ a, snd Q₁.B Q₃.B ≫ b'] Q₂.M.L).IsLB := DVR.linComb_isLB _ Q₂.M.isLB _ _
  have lC : (cubeLB Q₁.B ![fst Q₁.B Q₃.B, snd Q₁.B Q₃.B ≫ b' ≫ a'] Q₁.M.L).IsLB := DVR.linComb_isLB _ Q₁.M.isLB _ _
  obtain ⟨w, gw, hw⟩ := exists_comp lA lB lC (pullIso cA cB₁ w₂₃) (pullIso_isGen cA cB₁ g₂₃)
    (pullIso cB₂ cC w₁₂) (pullIso_isGen cB₂ cC g₁₂)
  refine ⟨inferInstance, inferInstance, fun y => ?_, fun y => ?_, w, gw, fun y y' z J₁ J₃ hJ₁ hJ₃ => ?_⟩
  · rw [AddMonoidHom.comp_apply, cb, ca, Category.assoc]
  · rw [AddMonoidHom.comp_apply, ca', cb', Category.assoc]
  · obtain ⟨J₂, hJ₂⟩ := GlobalTheory.ChartCmp.CarryCalc.exists_good' Q₂.M.isLB z
    have e₂₃ := V₂₃ (h y) y' z J₂ J₃ hJ₂ hJ₃
    have e₁₂ := V₁₂ y (k' y') z J₁ J₂ hJ₁ hJ₂
    have hP₂₃ : (lift (toUnit (TK R) ≫ Q₂.c (h y)) (toUnit (TK R) ≫ Q₃.c y')).left =
        (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₃.c y')).left ≫ m₁.left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd, ca, Category.assoc]
    have hP₁₂ : (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c (k' y'))).left =
        (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₃.c y')).left ≫ m₂.left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, cb', Category.assoc]
    rw [hP₂₃] at e₂₃
    rw [hP₁₂] at e₁₂
    generalize (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₃.c y')).left = P at e₂₃ e₁₂ ⊢
    have mC := Good.mem hJ₁ (fun I : ULift (Finset (Fin 2)) => (psum Q₁.B ![fst Q₁.B Q₃.B, snd Q₁.B Q₃.B ≫ b' ≫ a'] I.down).left) P
    have mB := Good.mem hJ₂ (fun I : ULift (Finset (Fin 2)) => (psum Q₂.B ![fst Q₁.B Q₃.B ≫ a, snd Q₁.B Q₃.B ≫ b'] I.down).left) P
    have mA := Good.mem hJ₃ (fun I : ULift (Finset (Fin 2)) => (psum Q₃.B ![fst Q₁.B Q₃.B ≫ a ≫ b, snd Q₁.B Q₃.B] I.down).left) P
    have K : adjVal w P z J₁ J₃ = adjVal w₂₃ (P ≫ m₁.left) z J₂ J₃ * adjVal w₁₂ (P ≫ m₂.left) z J₁ J₂ := by
      refine ((adjVal_of w P z J₁ J₃ _ _ (fun _ => rfl) (fun _ => rfl)).trans ((hw _ P z _ _ _ mC mB mA).trans
        (congrArg₂ (· * ·) (gm_pullIso cB₂ cC w₁₂ P z (_, _) ⟨mC, mB⟩) (gm_pullIso cA cB₁ w₂₃ P z (_, _) ⟨mB, mA⟩)))).trans ?_
      rw [mul_comm]
      refine congrArg₂ (· * ·) (adjVal_of w₂₃ (P ≫ m₁.left) z J₂ J₃ _ _ (fun I => ?_) (fun I => ?_)).symm
        (adjVal_of w₁₂ (P ≫ m₂.left) z J₁ J₂ _ _ (fun I => ?_) (fun I => ?_)).symm
      · show J₂ _ = J₂ _
        rw [Category.assoc, ← psum_left_pull m₁ _ _ xB₁ I]
      · show J₃ _ = J₃ _
        rw [Category.assoc, ← psum_left_pull m₁ _ _ xA I]
      · show J₁ _ = J₁ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xC I]
      · show J₂ _ = J₂ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xB₂ I]
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, e₂₃, e₁₂, K]
    exact (_root_.mul_assoc _ _ _).symm

end GlobalTheory.MumFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralProjectiveClosureOfLinearSystemPoi
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

private theorem exists_toField {Ω : Type} [Field Ω] {Y : Scheme.{0}} [IsIntegral Y] (g : Sp Ω ⟶ Y) [IsDominant g] :
    ∃ φ : Y.functionField →+* Ω, (∀ U : Y.Opens, genericPoint Y ∈ U → ⊤ ≤ g ⁻¹ᵁ U) ∧
      (∀ U : Y.Opens, ⊤ ≤ g ⁻¹ᵁ U → genericPoint Y ∈ U) ∧
      ∀ (U : Y.Opens) (h : genericPoint Y ∈ U) (e : ⊤ ≤ g ⁻¹ᵁ U) (s : Γ(Y, U)),
        ProjSpace.fnOn ⊤ (φ (Cartier.fnOf U h s)) = (g.appLE U ⊤ e).hom s := by
  have hI : IsIntegral (Sp Ω) := inferInstanceAs (IsIntegral (Spec (CommRingCat.of Ω)))
  have hS : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  let η := genericPoint (Sp Ω)
  have hb : Function.Bijective (Cartier.fnOf (X := Sp Ω) ⊤ trivial) := by
    refine ⟨fnOf_injective _ _, fun a => ?_⟩
    obtain ⟨U, hU, s, hs⟩ := (Sp Ω).presheaf.germ_exist (x := η) a
    obtain rfl : U = ⊤ := top_unique fun x _ => (Subsingleton.elim η x) ▸ hU
    exact ⟨s, hs⟩
  let e₁ := RingEquiv.ofBijective _ hb
  let e₂ := RingEquiv.ofBijective _ (ProjSpace.fnOn_top_bijective (A := Ω))
  refine ⟨(e₂.symm.toRingHom.comp e₁.symm.toRingHom).comp (functionFieldMap g), fun U hU x _ => ?_,
    fun U hU => gen_mem (x := g η) (hU trivial), fun U h e s => ?_⟩
  · obtain ⟨_, hz, z, rfl⟩ := g.denseRange.inter_open_nonempty U U.isOpen ⟨_, hU⟩
    exact (Subsingleton.elim z x) ▸ hz
  · change e₂ (e₂.symm (e₁.symm (functionFieldMap g _))) = _
    rw [RingEquiv.apply_symm_apply, RingEquiv.symm_apply_eq]
    have hx : η ∈ g ⁻¹ᵁ U := e trivial
    change _ = Cartier.fnOf ⊤ trivial (resG _ e (g.app U s))
    refine Eq.trans ?_ (fnOf_resG e _ _).symm
    rw [← Cartier.algebraMap_germ (show g η ∈ U from hx), functionFieldMap_algebraMap,
      ← Cartier.algebraMap_germ hx]
    congr 1
    exact Scheme.Hom.germ_stalkMap_apply g U η hx s

private theorem dim_of_trdeg {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {Y : Scheme.{0}} [IsIntegral Y]
    (q : Y ⟶ Sp K) [LocallyOfFiniteType q] (e : Y.functionField ≃+* Ω)
    (he : ∀ a, e (toFunctionField q a) = algebraMap K Ω a) {D : ℕ} (hD : Algebra.trdeg K Ω = D) :
    topologicalKrullDim Y = D := by
  letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ q)).hom.toAlgebra
  have hc : Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ q) = CommRingCat.ofHom (toFunctionField q) :=
    Spec.map_injective ((Spec.map_preimage _).trans (genericFieldPoint_over q))
  let e' : Y.functionField ≃ₐ[K] Ω := { e with
    commutes' := fun a => (congrArg (fun f => e (CommRingCat.Hom.hom f a)) hc).trans (he a) }
  have ht : Algebra.trdeg K Y.functionField = D :=
    (le_antisymm (trdeg_le_of_injective e'.toAlgHom e'.injective)
      (trdeg_le_of_injective e'.symm.toAlgHom e'.symm.injective)).trans hD
  have h1 := GlobalTheory.topologicalKrullDim_preimage_genericPoint_eq q ht
  have h2 : (q ⁻¹' {genericPoint (Spec (CommRingCat.of K))} : Set Y) = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim _ _
  rwa [h2, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph] at h1

private theorem eq_top_of_span {K V Ω ι : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) (u : ι → V) (hu : Submodule.span K (Set.range u) = ⊤) (hg : GlobalTheory.DegVal.GenRatios ev)
    (L : Subfield Ω) (hc : ∀ a, algebraMap K Ω a ∈ L) (hr : ∀ k l, ev (u l) ≠ 0 → ev (u k) / ev (u l) ∈ L) :
    L = ⊤ := by
  obtain ⟨l, hl⟩ : ∃ l, ev (u l) ≠ 0 := by
    by_contra! h0
    exact hg.1 (LinearMap.ext_on_range hu fun k => by simpa using h0 k)
  have key : ∀ v, ev v / ev (u l) ∈ L := fun v => by
    have hv : v ∈ Submodule.span K (Set.range u) := hu ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hr k l hl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), add_div]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul, Algebra.smul_def, mul_div_assoc]; exact mul_mem (hc a) hx
  have h : GlobalTheory.DegVal.ratioField ev ≤ L.toIntermediateField hc := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨v, w, rfl⟩
    rw [← div_div_div_cancel_right₀ hl]
    exact div_mem (key v) (key w)
  rw [hg.2] at h
  exact top_unique fun x _ => h (IntermediateField.mem_top (x := x))


open MvPolynomial in
private theorem trdeg_eq {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) (D : ℕ) (hg : GlobalTheory.DegVal.GenRatios ev) (hD : 0 < imageDeg ev D) :
    Algebra.trdeg K Ω = D := by
  obtain ⟨N, b, F, hF⟩ := (imageDeg_pos_iff ev D).1 hD
  set y : Fin N → Ω := fun j => ev (b j) with hy
  have hy0 : y ≠ 0 := fun h0 => hg.1 (b.ext fun k => by simpa using congrFun h0 k)
  have hr : Subfield.closure (Set.range (algebraMap K Ω) ∪ {r | ∃ i j, r = y i / y j}) = ⊤ :=
    eq_top_of_span ev b b.span_eq hg _ (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
      fun k l _ => Subfield.subset_closure (Or.inr ⟨k, l, rfl⟩)
  have := isPrime_coneIdeal (K := K) y
  have hk : ringKrullDim (MvPolynomial (Fin N) K ⧸ coneIdeal K y) = (D + 1 : ℕ) :=
    GlobalTheory.ChowExists.ringKrullDim_of_isChowFormInt (P := coneIdeal K y) (fun g hg n =>
      (mem_coneIdeal_of_isHomogeneous y (homogeneousComponent_isHomogeneous n g)).2
        ((mem_coneIdeal_iff y g).1 hg n)) hF
  obtain ⟨d, hd, hd'⟩ := exists_ringKrullDim_eq_and_trdeg_eq K (MvPolynomial (Fin N) K ⧸ coneIdeal K y)
  obtain rfl : d = D + 1 := by exact_mod_cast hd.symm.trans hk
  let f := Ideal.kerLiftAlg (coneMap K y)
  have hf : Function.Injective f := Ideal.kerLiftAlg_injective _
  let A := f.range
  let e := AlgEquiv.ofInjective f hf
  have hQA : Algebra.trdeg K (MvPolynomial (Fin N) K ⧸ coneIdeal K y) = Algebra.trdeg K A :=
    le_antisymm (trdeg_le_of_injective e.toAlgHom e.injective)
      (trdeg_le_of_injective e.symm.toAlgHom e.symm.injective)
  have hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A := fun i => by
    have := AlgHom.mem_range_self f (Ideal.Quotient.mk _ (X i))
    rw [Ideal.kerLiftAlg_mk] at this
    simp only [coneMap, aeval_X] at this
    exact this
  have := GlobalTheory.Adelic.ConeDim.isAlgebraic_of_closure_eq_top y hy0 hr A hXy
  have : FaithfulSMul K A := (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul A (Polynomial Ω) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  rw [hQA, ← GlobalTheory.trdeg_eq_of_isAlgebraic_top K A (Polynomial Ω), ← trdeg_add_eq K Ω (A := Polynomial Ω),
    Polynomial.trdeg_of_isDomain] at hd'
  exact Cardinal.add_one_inj.1 (by exact_mod_cast hd')

theorem _root_.GlobalTheory.T.exists_integral_projective_closure_of_linearSystem_point : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (D m : ℕ) (u : Fin (m + 1) → V),
    Submodule.span K (Set.range u) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (q : Y ⟶ Sp K) (B : LB Y) (_ : B.IsLB) (t : Fin (m + 1) → B.Sec) (ψ : Ω →+* Y.functionField),
      IsProjOver q ∧ topologicalKrullDim Y = D ∧ (⨆ k, nonzeroLocus (t k) = ⊤) ∧ Function.Bijective ψ ∧
      (∀ a : K, ψ (algebraMap K Ω a) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX q ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : B.ι) (h : genericPoint Y ∈ B.U i),
        ψ (ev (u k)) * fnOf _ h ((t l).f i) = ψ (ev (u l)) * fnOf _ h ((t k).f i) := by
  intro K V Ω _ _ _ _ _ ev D m u hu hg hD
  set y : Fin (m + 1) → Ω := fun k => ev (u k) with hy_def
  have hy : Ideal.span (Set.range y) = ⊤ := by
    obtain ⟨l, hl⟩ : ∃ l, ev (u l) ≠ 0 := by
      by_contra! h0
      exact hg.1 (LinearMap.ext_on_range hu fun k => by simpa using h0 k)
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨l, rfl⟩) (Ne.isUnit hl)
  let p := ProjSpace.pt (algebraMap K Ω) y hy
  have hI : IsIntegral (Sp Ω) := inferInstanceAs (IsIntegral (Spec (CommRingCat.of Ω)))
  have hS : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have hqc : QuasiCompact p := ⟨fun U _ _ => (Set.toFinite _).isCompact⟩
  obtain ⟨Y, hY, g, j, hdom, hj, hgj⟩ : ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (g : Sp Ω ⟶ Y) (j : Y ⟶ PSpace K m),
      IsDominant g ∧ IsClosedImmersion j ∧ g ≫ j = p :=
    ⟨p.image, isIntegral_image p, p.toImage, p.imageι, inferInstance, inferInstance, p.toImage_imageι⟩
  obtain ⟨φ, hm₁, hm₂, hφ⟩ := exists_toField g
  let B := (ProjSpace.O1 K m).pull j
  let t : Fin (m + 1) → B.Sec := fun k => Cartier.secPull (ProjSpace.coord K m k) j
  have hU : ∀ i : PUnit → Fin (m + 1), g ⁻¹ᵁ B.U i = ProjSpace.spOpen (y (i ⟨⟩)) := fun i => by
    rw [← ProjSpace.pt_preimage_chart (algebraMap K Ω) y hy]
    refine (congrArg (g ⁻¹ᵁ ·) (pull_U (ProjSpace.O1 K m) j i)).trans ?_
    exact (Scheme.Hom.comp_preimage g j _).symm.trans (congrArg (· ⁻¹ᵁ _) hgj)
  have hmem : ∀ i : PUnit → Fin (m + 1), genericPoint Y ∈ B.U i ↔ y (i ⟨⟩) ≠ 0 := fun i => by
    constructor
    · intro h h0
      have := (hm₁ _ h).trans (hU i).le (show genericPoint (Sp Ω) ∈ (⊤ : (Sp Ω).Opens) from trivial)
      rw [ProjSpace.mem_spOpen, h0] at this
      exact this (zero_mem _)
    · intro h
      refine hm₂ _ (le_of_le_of_eq (fun x _ => ?_) (hU i).symm)
      exact fun hx => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (Ne.isUnit h))
  have hrat : ∀ (i : PUnit → Fin (m + 1)) (h : genericPoint Y ∈ B.U i) (l : Fin (m + 1)),
      φ (Cartier.fnOf _ h ((t l).f i)) * y (i ⟨⟩) = y l := fun i h l => by
    refine ProjSpace.fnOn_top_bijective.1 ?_
    have e₁ := (resG_self _ _).symm.trans (ProjSpace.resG_secPull_coord j l i le_rfl)
    have h' : ⊤ ≤ p ⁻¹ᵁ ProjSpace.chart K m (i ⟨⟩) :=
      (hm₁ _ h).trans ((hU i).trans (ProjSpace.pt_preimage_chart (algebraMap K Ω) y hy _).symm).le
    rw [map_mul, hφ _ h (hm₁ _ h), ← ProjSpace.pullRatio_pt_mul (algebraMap K Ω) y hy (i ⟨⟩) l h']
    congr 1
    refine (congrArg _ e₁).trans ?_
    rw [ProjSpace.appLE_pullRatio]
    exact ProjSpace.pullRatio_of_eq hgj _ _
  have hconst : ∀ a, φ (toFunctionField (j ≫ PSpace.str K m) a) = algebraMap K Ω a := fun a => by
    refine ProjSpace.fnOn_top_bijective.1 ?_
    refine (hφ ⊤ trivial le_top (((Scheme.ΓSpecIso (.of K)).inv ≫ (j ≫ PSpace.str K m).appTop).hom a)).trans ?_
    have e : g ≫ j ≫ PSpace.str K m = spMap (algebraMap K Ω) := by
      rw [reassoc_of% hgj]
      change ProjSpace.pt (algebraMap K Ω) y hy ≫ PSpace.str K m = _
      rw [ProjSpace.pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
      congr 1
      ext1
      exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C (algebraMap K Ω) y r
    have e' : (j ≫ PSpace.str K m).appTop ≫ g.appTop = (spMap (algebraMap K Ω)).appTop := by
      rw [← Scheme.Hom.comp_appTop, e]
    have e'' := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K Ω))
    rw [← e'] at e''
    exact congrArg (resG (Sp Ω) le_top) (congrArg (fun f => f.hom a) e'').symm
  have hsurj : Function.Surjective φ := by
    rw [← RingHom.fieldRange_eq_top_iff]
    refine eq_top_of_span ev u hu hg _ (fun a => ⟨_, hconst a⟩) fun k l hl => ?_
    exact ⟨_, eq_div_of_mul_eq hl (hrat (fun _ => l) ((hmem (fun _ => l)).2 hl) k)⟩
  let e : Y.functionField ≃+* Ω := RingEquiv.ofBijective φ ⟨RingHom.injective _, hsurj⟩
  have hft : LocallyOfFiniteType (j ≫ PSpace.str K m) := inferInstance
  refine ⟨Y, hY, j ≫ PSpace.str K m, B, LB.isLB_pull (ProjSpace.O1_isLB K m) _, t,
    e.symm.toRingHom, ⟨m, j, hj, rfl⟩, dim_of_trdeg _ e hconst (trdeg_eq ev D hg hD),
    ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord K m) _, e.symm.bijective, fun a => ?_,
    fun k l i h => ?_⟩
  · apply e.injective
    change e (e.symm _) = φ _
    rw [RingEquiv.apply_symm_apply, ← hconst]
    simp [toFunctionField, Cartier.fnOf, algX, Scheme.Hom.appLE]
  · apply e.injective
    have hi := (hmem i).1 h
    change e (e.symm (y k) * _) = e (e.symm (y l) * _)
    rw [map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    change y k * φ _ = y l * φ _
    rw [eq_div_of_mul_eq hi (hrat i h l), eq_div_of_mul_eq hi (hrat i h k)]
    ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCanForm
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R] {A : Over (Sp R)}

theorem fv_form (β : Form (A.hom ≫ 𝟙 _)) {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt A D) : fv β.1 D D' φ x = 0 := by
  simpa only [fv, GlobalTheory.Cris.ev] using β.2 (trivMap φ x) rfl rfl

variable [GrpObj A] {p : ℕ} {G : PDivGroup p R}

def formDat (t : G.TorsionTower A) (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A) : Dat t ⟨_, hβ⟩ where
  f := β.1
  cl := rfl
  g := fun _ _ _ _ _ ↦ 0
  add := fun _ _ _ _ _ _ φ _ _ ↦ by simp [fv_form]
  h := 0
  res := fun n ↦ by simp [fv_form]

theorem isCan_form : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A),
    ∃ w : G.omega, (∀ n, w.1 n = cotVal β.1 (t.y n)) ∧ IsCan t ⟨_, hβ⟩ (G.rigOfOmega w) := by
  intro R _ A _ p G t β hβ
  refine ⟨⟨(formDat t β hβ).om, fun n ↦ GlobalTheory.T.torsionTowerPresentation_cotangentPullback_res_rigidification R A p G t _ (formDat t β hβ) n⟩, fun n ↦ ?_,
    formDat t β hβ, 0, _, fun n ↦ ?_, fun _ ↦ rfl, rfl⟩
  · change cotVal β.1 (t.y n) - dUnit (R := R) (0 : G.A n) = _
    rw [dUnit, map_zero, sub_zero]
  · change (0 : _) = 0 - (fv β.1 _ _ _ _ - fv β.1 _ _ _ _ - fv β.1 _ _ _ _) - cobOne R (G.A n) 0
    simp [fv_form]

end GlobalTheory.PtExt
end
end
