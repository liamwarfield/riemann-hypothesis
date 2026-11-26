module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpFamilyMatrixRelationsDense
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyMorphismFromVeryDenseGraphs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingDiagonalBundleOfEighthPowerForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfBiadditiveSliceTrivialEighthPower
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfBiadditiveSliceTrivialEighthPower
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.FormBundleKer


open GlobalTheory.CechPic in
theorem eq_one_of_slice_trivial : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → Out.KTriv G L → ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  intro W S G A _ _ _ _ pr L P hpr huniv hL hP hsym hbi hLP hK T x hx
  let p : ∀ {T' : Over S}, (T' ⟶ A) → (T' ⟶ A) → Pic T'.left := fun a b => pull (lift a b).left (cls P hP)
  have padd : ∀ {T' : Over S} (a a' b : T' ⟶ A), p (a * a') b = p a b + p a' b := fun {T'} a a' b => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hbi T' a a' b).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    simp only [p]
    abel
  have psym : ∀ {T' : Over S} (a b : T' ⟶ A), p a b = p b a := fun {T'} a b => by
    have e : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) :=
      (cls_eq_iff hP (pull_isLB hP _)).2 hsym
    have k : (lift b a).left ≫ (lift (snd A A) (fst A A)).left = (lift a b).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]
    show pull (lift a b).left (cls P hP) = pull (lift b a).left (cls P hP)
    rw [← k, pull_comp, ← e]
  have pone : ∀ {T' : Over S} (b : T' ⟶ A), p 1 b = 0 := fun b => by
    have := padd 1 1 b
    rw [_root_.mul_one] at this
    exact left_eq_add.1 this
  have px : ∀ {T' : Over S} (τ : T' ⟶ T) (y : T' ⟶ A), p (τ ≫ x) y = 0 := fun τ y => by
    have e := (cls_eq_zero_iff (pull_isLB hP _)).2 hx
    rw [cls_pull hP] at e
    have k : (lift y τ).left ≫ (lift (snd A T ≫ x) (fst A T)).left = (lift (τ ≫ x) y).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
    show pull (lift (τ ≫ x) y).left (cls P hP) = 0
    rw [← k, pull_comp, e, map_zero]
  have hl : ∀ {T' : Over S} (z : T' ⟶ G), pull z.left (cls L hL) =
      ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • p (z ≫ pr uv.1) (z ≫ pr uv.2) := fun z => by
    have e := (cls_eq_iff hL (LB.isLB_linComb hP _ _)).2 hLP
    rw [cls_linComb hP] at e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift]
  obtain ⟨x', hx', -⟩ := huniv T fun v => if v = 0 then x else 1
  have pz : ∀ u (y : T ⊗ G ⟶ A), p ((fst T G ≫ x') ≫ pr u) y = 0 := fun u y => by
    rw [Category.assoc, hx']
    split_ifs
    · exact px _ _
    · rw [MonObj.comp_one]; exact pone _
  have key : pull (Out.translPt G x').left (cls L hL) = pull (snd T G).left (cls L hL) := by
    have e : Out.translPt G x' = (fst T G ≫ x') * snd T G := rfl
    rw [hl, hl, e]
    refine Finset.sum_congr rfl fun uv _ => ?_
    have := hpr uv.1
    have := hpr uv.2
    rw [MonObj.mul_comp, MonObj.mul_comp, padd, pz, zero_add, psym, padd, pz, zero_add, psym]
  have H : KerPow.HasGen L (K := Fin 2) ![(Out.translPt G x').left, (snd T G).left] ![1, -1] := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
    rw [cls_linComb hL, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, key, one_smul, neg_smul, add_neg_cancel]
  have h1 : x' = 1 := KerPow.eq_one_of_locGen hK x' fun _ => ⟨⊤, trivial, H.pull _ fun _ => rfl⟩
  have h0 := hx' 0
  have := hpr 0
  rw [h1, MonObj.one_comp, if_pos rfl] at h0
  exact h0.symm

end GlobalTheory.FormBundleKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfBiadditiveSliceTrivialEighthPowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_biadditive_slice_trivial_eighthPower : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → Out.KTriv G L → ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  first | exact @GlobalTheory.FormBundleKer.eq_one_of_slice_trivial | exact GlobalTheory.FormBundleKer.eq_one_of_slice_trivial | (intros; apply GlobalTheory.FormBundleKer.eq_one_of_slice_trivial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CommutatorPairingE8SharpLevelPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CommutatorPairingE8SharpLevelPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SharpWeil

section Abstract
variable {G C : Type} [CommGroup G] [CommGroup C] {k : ℕ}

private theorem rel_one_one {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) : R 1 1 := by
  obtain ⟨c, hc, hu⟩ := hex 1 (one_pow k)
  have hcc : c * c = c := hu _ (by simpa using hmul 1 1 c c hc hc)
  have hc1 : c = 1 := by simpa using hcc
  rwa [hc1] at hc

private theorem rel_inv_of_rel {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) {x : G} {c : C} (hx : x ^ k = 1)
    (h : R x c) : R x⁻¹ c⁻¹ := by
  obtain ⟨d, hd, -⟩ := hex x⁻¹ (by rw [inv_pow, hx, inv_one])
  have h1 : R 1 (c * d) := by simpa using hmul _ _ _ _ h hd
  obtain ⟨e, -, hu⟩ := hex 1 (one_pow k)
  have hcd : c * d = 1 := (hu _ h1).trans (hu _ (rel_one_one hex hmul)).symm
  rwa [eq_inv_of_mul_eq_one_right hcd] at hd

private theorem rel_pow_of_rel {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) {x : G} {c : C} (h : R x c) (n : ℕ) :
    R (x ^ n) (c ^ n) := by
  induction n with
  | zero => simpa using rel_one_one hex hmul
  | succ n ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ ih h

private theorem rel_zpow_of_rel {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) {x : G} {c : C} (hx : x ^ k = 1)
    (h : R x c) (n : ℤ) : R (x ^ n) (c ^ n) := by
  cases n with
  | ofNat n => simpa using rel_pow_of_rel hex hmul h n
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc]
    exact rel_inv_of_rel hex hmul (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]) (rel_pow_of_rel hex hmul h (n + 1))

theorem rel_prod {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) {I : Type} (s : Finset I) (q : I → G) (c : I → C)
    (hq : ∀ i, q i ^ k = 1) (h : ∀ i, R (q i) (c i)) (a : I → ℤ) :
    R (∏ i ∈ s, q i ^ a i) (∏ i ∈ s, c i ^ a i) := by
  classical
  refine Finset.induction_on s (by simpa using rel_one_one hex hmul) ?_
  intro i s hi ih
  rw [Finset.prod_insert hi, Finset.prod_insert hi]
  exact hmul _ _ _ _ (rel_zpow_of_rel hex hmul (hq i) (h i) (a i)) ih

theorem prod_zpow_pow {I : Type} [Fintype I] (q : I → G) (hq : ∀ i, q i ^ k = 1) (a : I → ℤ) :
    (∏ i, q i ^ a i) ^ k = 1 := by
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm (a i), zpow_mul, zpow_natCast, hq i, one_zpow]

theorem zpow_sum' {I : Type} (s : Finset I) (ζ : C) (a : I → ℤ) : ζ ^ (∑ i ∈ s, a i) = ∏ i ∈ s, ζ ^ a i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem rel_biprod {R : G → G → C → Prop} (hex : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, R x y c)
    (hmul : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c'))
    (hsymm : ∀ x y c, R x y c → R y x c⁻¹) {I : Type} [Fintype I] (q : I → G) (ζ : C) (ω : I → I → ℤ)
    (hq : ∀ i, q i ^ k = 1) (h : ∀ i j, R (q i) (q j) (ζ ^ ω i j)) (a b : I → ℤ) :
    R (∏ i, q i ^ a i) (∏ i, q i ^ b i) (ζ ^ ∑ i, ∑ j, a i * b j * ω i j) := by
  have hy : (∏ j, q j ^ b j) ^ k = 1 := prod_zpow_pow q hq b
  have hrow : ∀ i, R (q i) (∏ j, q j ^ b j) (ζ ^ ∑ j, b j * ω i j) := by
    intro i
    have H : R (∏ j, q j ^ b j) (q i) (∏ j, ((ζ ^ ω i j)⁻¹) ^ b j) :=
      rel_prod (R := fun x c => R x (q i) c) (fun x hx => hex x (q i) hx (hq i))
        (fun x x' c c' h1 h2 => hmul x x' (q i) c c' h1 h2) Finset.univ q (fun j => (ζ ^ ω i j)⁻¹) hq
        (fun j => hsymm _ _ _ (h i j)) b
    have e : ζ ^ ∑ j, b j * ω i j = (∏ j, ((ζ ^ ω i j)⁻¹) ^ b j)⁻¹ := by
      rw [zpow_sum', ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [inv_zpow, inv_inv, ← zpow_mul, mul_comm (b j)]
    rw [e]
    exact hsymm _ _ _ H
  have H : R (∏ i, q i ^ a i) (∏ j, q j ^ b j) (∏ i, (ζ ^ ∑ j, b j * ω i j) ^ a i) :=
    rel_prod (R := fun x c => R x (∏ j, q j ^ b j) c) (fun x hx => hex x _ hx hy)
      (fun x x' c c' h1 h2 => hmul x x' _ c c' h1 h2) Finset.univ q (fun i => ζ ^ ∑ j, b j * ω i j) hq hrow a
  have e : ζ ^ ∑ i, ∑ j, a i * b j * ω i j = ∏ i, (ζ ^ ∑ j, b j * ω i j) ^ a i := by
    rw [zpow_sum']
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  exact H

end Abstract

theorem eq_sum_basis {n : ℕ} {M : Type} [AddCommGroup M] (bas : (Fin n → ℤ) ≃ₗ[ℤ] M) (X : M) :
    X = ∑ i, bas.symm X i • bas (Pi.single i 1) := by
  apply bas.symm.injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_zsmul, LinearEquiv.symm_apply_apply]
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

def omegaLin (h : ℕ) : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ omegaStd
    (fun a a' b => by simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring)
    (fun c a b => by simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring)
    (fun a b b' => by simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring)
    (fun c a b => by simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring)

theorem form_eq {h g : ℕ} {W : Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} (hb : IsSharpBasis W bas)
    (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) :
    ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v) =
      ∑ i, ∑ j, bas.symm X i * bas.symm Y j * Out.stdSymp g i j := by
  have hω : ∀ a b : Fin h ⊕ Fin h → ℤ, omegaStd a b = omegaLin h a b := fun a b => by simp [omegaLin]
  have hX : ∀ u, X u = ∑ i, bas.symm X i • bas (Pi.single i 1) u := fun u => by
    conv_lhs => rw [eq_sum_basis bas X]
    simp [Finset.sum_apply]
  have hY : ∀ v, Y v = ∑ j, bas.symm Y j • bas (Pi.single j 1) v := fun v => by
    conv_lhs => rw [eq_sum_basis bas Y]
    simp [Finset.sum_apply]
  have hs : ∀ i j, Out.stdSymp g i j = ∑ u, ∑ v, (W + W.transpose) u v *
      omegaLin h (bas (Pi.single i 1) u) (bas (Pi.single j 1) v) := fun i j => by
    rw [← hb i j]; simp only [hω]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hs, hω, hX, hY, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine (Finset.sum_congr rfl fun u _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun i _ =>
    (Finset.sum_congr rfl fun u _ => Finset.sum_comm).trans Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

theorem pull_unitS {o K : Type} [CommRing o] [CommRing K] {S : Scheme.{0}} (s : S ⟶ Sp o) (p : Sp K ⟶ S)
    (β : o →+* K) (u : oˣ) (z : Kˣ) (hp : p ≫ s = spMap β) (hz : (z : K) = β u) :
    Units.map p.appTop.hom.toMonoidHom (unitS s u) = unitOn z := by
  apply Units.ext
  have hc := congrArg (fun f : Sp K ⟶ Sp o => f.appTop.hom (unitOn u).val) hp
  simp only [unitS, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.comp_apply] at hc ⊢
  rw [hc]
  unfold unitOn spMap Sp
  have hn := congrArg (fun φ => φ.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  simp only [Units.coe_map, hz]
  exact hn.symm

end GlobalTheory.SharpWeil

namespace GlobalTheory


open SharpWeil in
theorem weilIs_sharp_levelPoints : Out.Laws → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp o) (t : TObj g k J b s) (A : Over S) [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (t.A ⟶ A)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)), IsSharpBasis W bas → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left) → ∀ (K : Type) [Field K] (p : Sp K ⟶ S) (β : o →+* K) (z : Kˣ), p ≫ s = spMap β → (z : K) = β b.ζ → ∀ (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) (y y' : Over.mk p ⟶ t.A), (∀ u, y ≫ pr u = toUnit _ ≫ lev (X u)) → (∀ u, y' ≫ pr u = toUnit _ ≫ lev (Y u)) → Out.WeilIs t.A t.L k y y' (unitOn z ^ ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v)) := by
  intro hL h g W J bas k o _ b S _ s t A _ _ pr lev hb hpr huniv hlev hpt K _ p β z hps hz X Y y y' hy hy'
  have := t.ab.comm
  let e : Over.mk p ⟶ Out.baseOver S := Over.homMk p (by simp)
  let q : Fin (2 * g) → (Over.mk p ⟶ t.A) := fun i => e ≫ t.pt i
  obtain ⟨hex, hmul, -, -⟩ := hL.weil S t.pol k (Over.mk p)
  have hq : ∀ i, q i ^ k = 1 := fun i => by
    simp only [q]
    rw [← MonObj.comp_pow, t.torsion i, MonObj.comp_one]
  have hpair : ∀ i j, Out.WeilIs t.A t.L k (q i) (q j) (unitOn z ^ Out.stdSymp g i j) := fun i j => by
    have H := CommPairing.weilIs_pull hL.globalFns t.ab t.isLB e (t.pairing i j)
    have e1 : Units.map e.left.appTop.hom.toMonoidHom (unitS s b.ζ) = unitOn z := pull_unitS s p β b.ζ z hps hz
    rwa [map_zpow, e1] at H
  have htu : (toUnit (Over.mk p)).left = e.left :=
    congrArg Over.Hom.left (toUnit_unique (toUnit (Over.mk p)) (Over.homMk p (by simp) : Over.mk p ⟶ 𝟙_ (Over S)))
  have hqlev : ∀ i u, q i ≫ pr u = toUnit (Over.mk p) ≫ lev (bas (Pi.single i 1) u) := fun i u => by
    apply Over.OverMorphism.ext
    simp only [q]
    rw [Category.assoc, Over.comp_left, hpt i u, Over.comp_left, htu]
  let levHom : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (𝟙_ (Over S) ⟶ A) :=
    MonoidHom.mk' (fun a => lev a.toAdd) (fun a c => hlev _ _)
  let ψ : (𝟙_ (Over S) ⟶ A) →* (Over.mk p ⟶ A) :=
    MonoidHom.mk' (fun f => toUnit (Over.mk p) ≫ f) (fun f f' => MonObj.comp_mul _ f f')
  have hprod : ∀ (V : Fin 8 → Fin h ⊕ Fin h → ℤ) (w : Over.mk p ⟶ t.A),
      (∀ u, w ≫ pr u = toUnit (Over.mk p) ≫ lev (V u)) → w = ∏ i, q i ^ bas.symm V i := by
    intro V w hw
    obtain ⟨x0, -, hu⟩ := huniv (Over.mk p) (fun u => w ≫ pr u)
    refine (hu w fun u => rfl).trans (hu _ fun u => ?_).symm
    have := hpr u
    let φ : (Over.mk p ⟶ t.A) →* (Over.mk p ⟶ A) :=
      MonoidHom.mk' (fun x => x ≫ pr u) (fun a c => MonObj.mul_comp a c (pr u))
    have hV : V u = ∑ i, bas.symm V i • bas (Pi.single i 1) u := by
      conv_lhs => rw [eq_sum_basis bas V]
      simp [Finset.sum_apply]
    have h1 : (∏ i, q i ^ bas.symm V i) ≫ pr u = ∏ i, (q i ≫ pr u) ^ bas.symm V i := by
      change φ (∏ i, q i ^ bas.symm V i) = ∏ i, (φ (q i)) ^ bas.symm V i
      simp only [map_prod, map_zpow]
    have h2 : toUnit (Over.mk p) ≫ lev (V u) =
        ∏ i, (toUnit (Over.mk p) ≫ lev (bas (Pi.single i 1) u)) ^ bas.symm V i := by
      change ψ (levHom (Multiplicative.ofAdd (V u))) =
        ∏ i, (ψ (levHom (Multiplicative.ofAdd (bas (Pi.single i 1) u)))) ^ bas.symm V i
      rw [hV, ofAdd_sum]
      simp only [ofAdd_zsmul, map_prod, map_zpow]
    rw [h1, hw u, h2]
    exact Finset.prod_congr rfl fun i _ => by rw [hqlev i u]
  rw [form_eq hb X Y, hprod X y hy, hprod Y y' hy']
  exact rel_biprod (R := fun a c d => Out.WeilIs t.A t.L k a c d) (fun a c ha hc => hex a c ha hc)
    (fun a a' c d d' h1 h2 => hmul a a' c d d' h1 h2) (fun a c d H => CommPairing.weilIs_symm t.isLB H)
    q (unitOn z) (Out.stdSymp g) hq hpair (bas.symm X) (bas.symm Y)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CommutatorPairingE8SharpLevelPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_e8Sharp_levelPoints : Out.Laws → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp o) (t : TObj g k J b s) (A : Over S) [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (t.A ⟶ A)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)), IsSharpBasis W bas → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left) → ∀ (K : Type) [Field K] (p : Sp K ⟶ S) (β : o →+* K) (z : Kˣ), p ≫ s = spMap β → (z : K) = β b.ζ → ∀ (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) (y y' : Over.mk p ⟶ t.A), (∀ u, y ≫ pr u = toUnit _ ≫ lev (X u)) → (∀ u, y' ≫ pr u = toUnit _ ≫ lev (Y u)) → Out.WeilIs t.A t.L k y y' (unitOn z ^ ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v)) := by
  first | exact @GlobalTheory.weilIs_sharp_levelPoints | exact GlobalTheory.weilIs_sharp_levelPoints | (intros; apply GlobalTheory.weilIs_sharp_levelPoints <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeEighthPowerOfMatrixAction
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeEighthPowerOfMatrixAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.MatrixPower

section General

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

@[reducible] def retractGrpObj {G A : C} [GrpObj G] (i : A ⟶ G) (r : G ⟶ A) (hir : i ≫ r = 𝟙 A)
    [he : IsMonHom (r ≫ i)] : GrpObj A :=
  haveI : Mono i := (SplitMono.mk r hir).mono
  have h1 : ∀ {T : C}, ((1 : T ⟶ G) ≫ r) ≫ i = 1 := fun {T} => by
    rw [Category.assoc, MonObj.one_comp]
  have h2 : ∀ {T : C} (a b : T ⟶ A), ((a ≫ i * b ≫ i) ≫ r) ≫ i = a ≫ i * b ≫ i := fun a b => by
    rw [Category.assoc, MonObj.mul_comp]; simp [reassoc_of% hir]
  have h3 : (i⁻¹ ≫ r) ≫ i = i⁻¹ := by
    rw [Category.assoc, GrpObj.inv_comp]; simp [reassoc_of% hir]
  { one := (1 : 𝟙_ C ⟶ G) ≫ r
    mul := (fst A A ≫ i * snd A A ≫ i) ≫ r
    inv := i⁻¹ ≫ r
    one_mul := by
      rw [← cancel_mono i, Category.assoc, h2, MonObj.comp_mul, whiskerRight_fst_assoc,
        whiskerRight_snd_assoc, h1]
      simp [leftUnitor_hom]
    mul_one := by
      rw [← cancel_mono i, Category.assoc, h2, MonObj.comp_mul, whiskerLeft_fst_assoc,
        whiskerLeft_snd_assoc, h1]
      simp [rightUnitor_hom]
    mul_assoc := by
      rw [← cancel_mono i, Category.assoc, h2, Category.assoc, Category.assoc, h2,
        MonObj.comp_mul, whiskerRight_fst_assoc, whiskerRight_snd_assoc, h2,
        MonObj.comp_mul (A ◁ _), whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, h2]
      simp [MonObj.comp_mul, _root_.mul_assoc]
    left_inv := by
      rw [← cancel_mono i, Category.assoc, h2, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
        h3, Category.assoc, h1]
      simp
    right_inv := by
      rw [← cancel_mono i, Category.assoc, h2, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
        h3, Category.assoc, h1]
      simp }

private theorem isMonHom_of_one_comp_of_mul_comp {M N : C} [MonObj M] [MonObj N] (f : M ⟶ N)
    (h1 : (1 : 𝟙_ C ⟶ M) ≫ f = 1)
    (h2 : (fst M M * snd M M) ≫ f = fst M M ≫ f * snd M M ≫ f) : IsMonHom f :=
  { one_hom := by rw [MonObj.one_eq_one M, MonObj.one_eq_one N, h1]
    mul_hom := by
      rw [MonObj.mul_eq_mul M, MonObj.mul_eq_mul N, h2, MonObj.comp_mul, tensorHom_fst,
        tensorHom_snd] }

theorem exists_grpObj_retract {G A : C} [GrpObj G] (i : A ⟶ G) (r : G ⟶ A) (hir : i ≫ r = 𝟙 A)
    [he : IsMonHom (r ≫ i)] : ∃ _ : GrpObj A, IsMonHom i ∧ IsMonHom r := by
  let gA : GrpObj A := retractGrpObj i r hir
  have hm : ∀ {T : C} (a b : T ⟶ A), a * b = (a ≫ i * b ≫ i) ≫ r := by
    intro T a b
    rw [Hom.mul_def]
    change lift a b ≫ (fst A A ≫ i * snd A A ≫ i) ≫ r = _
    rw [← Category.assoc, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  have ho : ∀ {T : C}, (1 : T ⟶ A) = (1 : T ⟶ G) ≫ r := by
    intro T
    rw [Hom.one_def]
    change toUnit T ≫ (1 : 𝟙_ C ⟶ G) ≫ r = _
    rw [← Category.assoc, MonObj.comp_one]
  refine ⟨gA, ?_, ?_⟩
  · refine isMonHom_of_one_comp_of_mul_comp i ?_ ?_
    · rw [ho, Category.assoc, MonObj.one_comp]
    · rw [hm, Category.assoc, MonObj.mul_comp]
      simp only [Category.assoc, reassoc_of% hir]
  · refine isMonHom_of_one_comp_of_mul_comp r ho.symm ?_
    rw [hm]
    calc (fst G G * snd G G) ≫ r = ((fst G G * snd G G) ≫ (r ≫ i)) ≫ r := by
          simp only [Category.assoc, hir, Category.comp_id]
      _ = _ := by rw [MonObj.mul_comp]; simp only [Category.assoc]

variable [BraidedCategory C]

theorem comp_prod {n : Type*} (s : Finset n) {T X G : C} [GrpObj G] [IsCommMonObj G]
    (f : T ⟶ X) (g : n → (X ⟶ G)) : f ≫ ∏ u ∈ s, g u = ∏ u ∈ s, f ≫ g u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, MonObj.comp_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

theorem prod_comp {n : Type*} (s : Finset n) {T G H : C} [GrpObj G] [IsCommMonObj G]
    [GrpObj H] [IsCommMonObj H] (g : n → (T ⟶ G)) (f : G ⟶ H) [IsMonHom f] :
    (∏ u ∈ s, g u) ≫ f = ∏ u ∈ s, g u ≫ f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, MonObj.one_comp]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

theorem exists_power [HasEqualizers C] {n : Type*} [Fintype n] [DecidableEq n] (o : n)
    (G : C) [GrpObj G] [IsCommMonObj G] (ρ : Matrix n n ℤ → (G ⟶ G))
    (hρ : ∀ m, IsMonHom (ρ m)) (hmul : ∀ m m', ρ (m * m') = ρ m' ≫ ρ m)
    (hadd : ∀ m m', ρ (m + m') = ρ m * ρ m') (hone : ρ 1 = 𝟙 G) :
    ∃ (A : C) (_ : GrpObj A) (_ : IsCommMonObj A) (_ : Retract A G) (pr : n → (G ⟶ A)),
      (∀ u, IsMonHom (pr u)) ∧
      (∀ (T : C) (y : n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) ∧
      ∀ m u, ρ m ≫ pr u = ∏ v, pr v ^ m u v := by
  have : ∀ m, IsMonHom (ρ m) := hρ
  have hc : ∀ a b : Matrix n n ℤ, ρ a ≫ ρ b = ρ (b * a) := fun a b => (hmul b a).symm
  have h0 : ρ 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hneg : ∀ a, ρ (-a) = (ρ a)⁻¹ := fun a =>
    eq_inv_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
  have hsum : ∀ (s : Finset n) (f : n → Matrix n n ℤ), ρ (∑ v ∈ s, f v) = ∏ v ∈ s, ρ (f v) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty, h0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]
  have hzs : ∀ (k : ℤ) (a : Matrix n n ℤ), ρ (k • a) = ρ a ^ k := by
    intro k a
    refine Int.induction_on k ?_ ?_ ?_
    · rw [zero_smul, h0, zpow_zero]
    · intro j ih
      rw [add_smul, one_smul, hadd, ih, zpow_add_one]
    · intro j ih
      rw [sub_smul, one_smul, sub_eq_add_neg, hadd, ih, hneg, zpow_sub_one]
  have hidem : ρ (Matrix.single o o 1) ≫ ρ (Matrix.single o o 1) =
      ρ (Matrix.single o o 1) ≫ 𝟙 G := by
    rw [Category.comp_id, hc, Matrix.single_mul_single_same, _root_.mul_one]
  obtain ⟨A, i, r, hir, hri⟩ : ∃ (A : C) (i : A ⟶ G) (r : G ⟶ A),
      i ≫ r = 𝟙 A ∧ r ≫ i = ρ (Matrix.single o o 1) := by
    refine ⟨equalizer (ρ (Matrix.single o o 1)) (𝟙 G), equalizer.ι _ _, equalizer.lift _ hidem,
      ?_, equalizer.lift_ι _ _⟩
    apply equalizer.hom_ext
    rw [Category.assoc, equalizer.lift_ι, Category.id_comp]
    exact (equalizer.condition _ _).trans (Category.comp_id _)
  have hmono : Mono i := (SplitMono.mk r hir).mono
  have : IsMonHom (r ≫ i) := by rw [hri]; infer_instance
  obtain ⟨gA, hi, hr⟩ := exists_grpObj_retract i r hir
  have hcA : IsCommMonObj A :=
    (isCommMonObj_iff_isMulCommutative _).2 fun X => ⟨⟨fun a b => by
      show a * b = b * a
      rw [← cancel_mono i, MonObj.mul_comp, MonObj.mul_comp, mul_comm]⟩⟩
  refine ⟨A, gA, hcA, ⟨i, r, hir⟩,
    fun u => ρ (Matrix.single o u 1) ≫ r, fun u => inferInstance, ?_, ?_⟩
  · intro T y
    refine ⟨∏ v, y v ≫ i ≫ ρ (Matrix.single v o 1), fun u => ?_, fun x hx => ?_⟩
    · dsimp only
      rw [prod_comp, Finset.prod_eq_single u]
      · have h3 : ρ (Matrix.single u o 1) ≫ ρ (Matrix.single o u 1) ≫ r = r ≫ i ≫ r := by
          rw [← Category.assoc, hc, Matrix.single_mul_single_same, _root_.mul_one, ← hri,
            Category.assoc]
        simp only [Category.assoc]
        rw [h3, reassoc_of% hir, hir, Category.comp_id]
      · intro v _ hv
        have h3 : ρ (Matrix.single v o 1) ≫ ρ (Matrix.single o u 1) ≫ r = 1 := by
          have h5 : Matrix.single o u (1 : ℤ) * Matrix.single v o 1 = 0 := by
            simp [Ne.symm hv]
          rw [← Category.assoc, hc, h5, h0, MonObj.one_comp]
        simp only [Category.assoc]
        rw [h3, MonObj.comp_one, MonObj.comp_one]
      · intro h
        exact absurd (Finset.mem_univ u) h
    · dsimp only at hx
      have h1 : (1 : Matrix n n ℤ) = ∑ v, Matrix.single v v 1 := by
        ext a b
        by_cases hab : a = b
        · subst hab
          simp [Matrix.sum_apply, Matrix.single_apply]
        · rw [Matrix.sum_apply, Finset.sum_eq_zero]
          · exact Matrix.one_apply_ne hab
          · intro v _
            rw [Matrix.single_apply]
            split_ifs with h
            · exact absurd (h.1.symm.trans h.2) hab
            · rfl
      calc x = x ≫ ρ 1 := by rw [hone, Category.comp_id]
        _ = ∏ v, x ≫ ρ (Matrix.single v v 1) := by rw [h1, hsum, comp_prod]
        _ = _ := by
          refine Finset.prod_congr rfl fun v _ => ?_
          rw [← hx v]
          have h4 : ρ (Matrix.single o v 1) ≫ r ≫ i ≫ ρ (Matrix.single v o 1) =
              ρ (Matrix.single v v 1) := by
            rw [reassoc_of% hri, hc, Matrix.single_mul_single_same, hc,
              Matrix.single_mul_single_same]
            simp only [_root_.mul_one]
          simp only [Category.assoc, h4]
  · intro m u
    dsimp only
    have hrow : Matrix.single o u (1 : ℤ) * m = ∑ v, m u v • Matrix.single o v 1 := by
      ext a b
      by_cases ha : a = o
      · subst ha
        simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply]
      · simp [Matrix.mul_apply, Matrix.sum_apply, Ne.symm ha]
    have := hcA
    rw [← Category.assoc, hc, hrow, hsum, prod_comp]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hzs, GrpObj.zpow_comp]

end General

theorem abelianScheme_matrix_power : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (ρ : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G)), IsAbelianScheme G → (∀ m, IsMonHom (ρ m)) → (∀ m m', ρ (m * m') = ρ m' ≫ ρ m) → (∀ m m', ρ (m + m') = ρ m * ρ m') → ρ 1 = 𝟙 G → ∃ (A : Over S) (_ : GrpObj A) (pr : Fin 8 → (G ⟶ A)), IsAbelianScheme A ∧ (∀ u, IsMonHom (pr u)) ∧ (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) ∧ ∀ m u, ρ m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod := by
  intro S G _ ρ hab hρ hmul hadd hone
  obtain ⟨hcomm, hsmooth, hproper, hgeo⟩ := hab
  obtain ⟨A, gA, hcA, R, pr, hpr, huniv, hact⟩ := exists_power (0 : Fin 8) G ρ hρ hmul hadd hone
  obtain ⟨-, -, -, hsm, -, -, -, -, hpro, -, hgc, -, -⟩ := GlobalTheory.Retract.over_properties R
  refine ⟨A, gA, pr, ⟨hcA, hsm hsmooth, hpro hproper, hgc hgeo⟩, hpr, huniv, fun m u => ?_⟩
  rw [hact, List.prod_ofFn]

end GlobalTheory.MatrixPower
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeEighthPowerOfMatrixActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_eighth_power_of_matrix_action : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (ρ : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G)), IsAbelianScheme G → (∀ m, IsMonHom (ρ m)) → (∀ m m', ρ (m * m') = ρ m' ≫ ρ m) → (∀ m m', ρ (m + m') = ρ m * ρ m') → ρ 1 = 𝟙 G → ∃ (A : Over S) (_ : GrpObj A) (pr : Fin 8 → (G ⟶ A)), IsAbelianScheme A ∧ (∀ u, IsMonHom (pr u)) ∧ (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) ∧ ∀ m u, ρ m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod := by
  first | exact @GlobalTheory.MatrixPower.abelianScheme_matrix_power | exact GlobalTheory.MatrixPower.abelianScheme_matrix_power | (intros; apply GlobalTheory.MatrixPower.abelianScheme_matrix_power <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseE8SharpAfterAdjoiningAllMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseE8SharpAfterAdjoiningAllMatrices
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SharpExt

variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}

theorem isMonHom_prod {G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj H] {I : Type} (T : Finset I)
    (f : I → (G ⟶ H)) (hf : ∀ i, IsMonHom (f i)) : IsMonHom (∏ i ∈ T, f i) :=
  Finset.prod_induction f (fun x => IsMonHom x) (fun x y _ _ => GlobalTheory.Serre.isMonHom_mul x y) GlobalTheory.Serre.isMonHom_one
    fun i _ => hf i

def matEnd (e : Fin 8 → Fin 8 → J) (t : TObj g k J b s) (m : Matrix (Fin 8) (Fin 8) ℤ) : t.A ⟶ t.A :=
  letI := t.ab.comm
  ∏ u, ∏ v, t.act (e u v) ^ m u v

theorem isMonHom_matEnd (e : Fin 8 → Fin 8 → J) (t : TObj g k J b s) (m : Matrix (Fin 8) (Fin 8) ℤ) :
    IsMonHom (matEnd e t m) :=
  letI := t.ab.comm
  isMonHom_prod _ _ fun u => isMonHom_prod _ _ fun v =>
    haveI := t.hom (e u v)
    GlobalTheory.Serre.isMonHom_zpow _ _

def ext (e : Fin 8 → Fin 8 → J) (t : TObj g k J b s) : TObj g k (J ⊕ Matrix (Fin 8) (Fin 8) ℤ) b s :=
  { t with
    act := Sum.elim t.act (matEnd e t)
    hom := fun j => match j with
      | .inl j => t.hom j
      | .inr m => isMonHom_matEnd e t m }

theorem tMap_ext (e : Fin 8 → Fin 8 → J) {t : TObj g k J b s} {t' : TObj g k J b s'} {f : S' ⟶ S}
    (H : TMap t' t f) : TMap (ext e t') (ext e t) f := by
  obtain ⟨φ, h, hL, hpt, hact⟩ := H
  refine ⟨φ, h, hL, hpt, ?_⟩
  rintro (j | m)
  · exact hact j
  · letI := t.ab.comm
    letI := t'.ab.comm
    let U : Over.mk (t'.A.hom ≫ f) ⟶ t.A := Over.homMk φ h.1.w
    have key : pushHom h t'.A (matEnd e t' m) = preHom (G := t.A) U (matEnd e t m) := by
      simp only [matEnd, map_prod, map_zpow]
      refine Finset.prod_congr rfl fun u _ => Finset.prod_congr rfl fun v _ => congrArg (· ^ m u v) ?_
      exact Over.OverMorphism.ext (hact _)
    exact congrArg (fun q => q.left) key

theorem isSharp_ext {h : ℕ} {W : Matrix (Fin 8) (Fin 8) ℤ} {a : J → Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} {e : Fin 8 → Fin 8 → J}
    (he : ∀ u v, a (e u v) = Matrix.single u v 1) {t : TObj g k J b s} {c : SiegPre h k (b.ζ : o) s}
    (H : IsSharp W a bas t c) : IsSharp W (Sum.elim a id) bas (ext e t) c := by
  obtain ⟨pr, hmon, huniv, hL, hmat, hpt⟩ := H
  refine ⟨pr, hmon, huniv, hL, ?_, hpt⟩
  have hpr : ∀ u v w, t.act (e u v) ≫ pr w = if w = u then pr v else 1 := by
    intro u v w
    rw [hmat, he, List.prod_ofFn]
    split_ifs with hw
    · subst hw
      rw [Finset.prod_eq_single v] <;> simp +contextual [Matrix.single_apply, eq_comm]
    · refine Finset.prod_eq_one fun i _ => ?_
      simp [Ne.symm hw]
  rintro (j | m) w
  · exact hmat j w
  · letI := t.ab.comm
    haveI := hmon w
    let P : (t.A ⟶ t.A) →* (t.A ⟶ c.A) := MonoidHom.mk' (· ≫ pr w) fun x y => MonObj.mul_comp x y (pr w)
    have hP : ∀ x, P x = x ≫ pr w := fun _ => rfl
    have key : P (matEnd e t m) = (List.ofFn fun v => pr v ^ m w v).prod := by
      simp only [matEnd, map_prod, map_zpow]
      simp only [hP, hpr]
      rw [List.prod_ofFn, Finset.prod_eq_single w]
      · simp
      · intro u _ hu
        simp [Ne.symm hu]
      · simp
    exact key

end GlobalTheory.SharpExt

namespace GlobalTheory

open SharpExt

theorem exists_dense_sharp_all_matrices : ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s), (∀ u v, ∃ j, a j = Matrix.single u v 1) → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ t' : TObj g k (J ⊕ Matrix (Fin 8) (Fin 8) ℤ) b s, Dense (fromSet em (SharpClass (b := b) W (Sum.elim a id) bas em) t') ∧ ∀ c : SiegPre h k (b.ζ : o) s, IsSharp W (Sum.elim a id) bas t' c → IsSharp W a bas t c := by
  intro h g W J a bas k o _ b em S s t he hd
  choose e he using he
  refine ⟨SharpExt.ext e t, hd.mono ?_, ?_⟩
  · rintro p ⟨K, _, x, hp, K₀, _, β, i, j, t₀, tx, tc, h₁, h₂, h₃, h₄, h₅, c, hc, hs⟩
    exact ⟨K, _, x, hp, K₀, _, β, i, j, SharpExt.ext e t₀, SharpExt.ext e tx, SharpExt.ext e tc, h₁, h₂,
      tMap_ext e h₃, tMap_ext e h₄, tMap_ext e h₅, c, hc, isSharp_ext he hs⟩
  · rintro c ⟨pr, hmon, huniv, hL, hmat, hpt⟩
    exact ⟨pr, hmon, huniv, hL, fun j u => hmat (.inl j) u, hpt⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseE8SharpAfterAdjoiningAllMatricesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_e8Sharp_after_adjoining_all_matrices : ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s), (∀ u v, ∃ j, a j = Matrix.single u v 1) → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ t' : TObj g k (J ⊕ Matrix (Fin 8) (Fin 8) ℤ) b s, Dense (fromSet em (SharpClass (b := b) W (Sum.elim a id) bas em) t') ∧ ∀ c : SiegPre h k (b.ζ : o) s, IsSharp W (Sum.elim a id) bas t' c → IsSharp W a bas t c := by
  first | exact @GlobalTheory.exists_dense_sharp_all_matrices | exact GlobalTheory.exists_dense_sharp_all_matrices | (intros; apply GlobalTheory.exists_dense_sharp_all_matrices <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelOnFactorOfEighthPowerAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelOnFactorOfEighthPowerAbelianScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem levelFactor_comp {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ}
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (c : Fin n → ℤ) (u : Fin m) : π u (∏ i, P i ^ c i) = L (bas c u) := by
  let φ : Λ →+ Additive H := AddMonoidHom.mk' (fun x => Additive.ofMul (L x)) hL
  have hφ : ∀ x, L x = Additive.toMul (φ x) := fun x => rfl
  have hc : bas c u = ∑ i, c i • bas (Pi.single i 1) u := by
    conv_lhs => rw [← Finset.univ_sum_single c]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs : (Pi.single i (c i) : Fin n → ℤ) = c i • (Pi.single i 1 : Fin n → ℤ) := by
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [hs, map_zsmul, Pi.smul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_prod, hc, hφ, map_sum, toMul_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow, hP, map_zsmul, toMul_zsmul]
  rfl

theorem levelFactor_torsion {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ} (u : Fin m)
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (k : ℕ) (ht : ∀ i, P i ^ k = 1) (x : Λ) : L x ^ k = 1 := by
  obtain ⟨c, hc⟩ : ∃ c, bas c = Pi.single u x := ⟨bas.symm (Pi.single u x), bas.apply_symm_apply _⟩
  have h1 := levelFactor_comp bas P π L hL hP c u
  rw [hc, Pi.single_eq_same] at h1
  have hk : ∀ i, (P i ^ c i) ^ k = 1 := fun i => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]
  rw [← h1, ← map_pow, ← Finset.prod_pow, Finset.prod_eq_one (fun i _ => hk i), map_one]

theorem levelFactor_bij {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ} (u : Fin m)
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (k : ℕ) (hk : 0 < k) (ht : ∀ i, P i ^ k = 1)
    (hπ : ∀ y : Fin m → H, ∃! x : G, ∀ u, π u x = y u)
    (hb : ∀ y : G, y ^ k = 1 → ∃! c : Fin n → ZMod k, (List.ofFn fun i => P i ^ (c i).val).prod = y) :
    (∀ x, L x = 1 ↔ ∃ y, x = k • y) ∧ ∀ y : H, y ^ k = 1 → ∃ x, L x = y := by
  have : NeZero k := ⟨hk.ne'⟩
  have hcomp := levelFactor_comp bas P π L hL hP
  have htor := levelFactor_torsion u bas P π L hL hP k ht
  have L0 : L 0 = 1 := mul_left_cancel (a := L 0) (by rw [← hL, add_zero, _root_.mul_one])
  have hsm : ∀ (j : ℕ) (x : Λ), L (j • x) = L x ^ j := by
    intro j x
    induction j with
    | zero => rw [zero_smul, L0, pow_zero]
    | succ j ih => rw [succ_nsmul, hL, ih, pow_succ]
  have hone : ∀ a : G, (∀ v, π v a = 1) → a = 1 := by
    intro a ha
    obtain ⟨x, -, hx⟩ := hπ (fun _ => 1)
    exact (hx a ha).trans (hx 1 (fun v => map_one _)).symm
  have hred : ∀ w : Fin n → ℤ,
      ∏ i, P i ^ w i = (List.ofFn fun i => P i ^ ((w i : ZMod k).val)).prod := by
    intro w
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [zpow_eq_zpow_emod (w i) (n := (k : ℤ)) (by rw [zpow_natCast]; exact ht i),
      ← ZMod.val_intCast, zpow_natCast]
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun y hy => ?_⟩
  · obtain ⟨w, hw⟩ : ∃ w, bas w = Pi.single u x := ⟨_, bas.apply_symm_apply _⟩
    have hg : ∏ i, P i ^ w i = 1 := hone _ fun v => by
      rw [hcomp, hw]
      by_cases hv : v = u
      · subst hv; rw [Pi.single_eq_same, hx]
      · rw [Pi.single_eq_of_ne hv, L0]
    obtain ⟨c0, -, huniq⟩ := hb 1 (one_pow _)
    have e1 := huniq (fun i => (w i : ZMod k)) ((hred w).symm.trans hg)
    have e2 := huniq 0 (by simp)
    have hdvd : ∀ i, (k : ℤ) ∣ w i := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun (e1.trans e2.symm) i)
    choose w' hw' using hdvd
    have hww : w = (k : ℤ) • w' := funext fun i => by rw [Pi.smul_apply, smul_eq_mul, hw' i]
    refine ⟨bas w' u, ?_⟩
    calc x = bas w u := by rw [hw, Pi.single_eq_same]
      _ = ((k : ℤ) • bas w') u := by rw [hww, map_zsmul]
      _ = k • bas w' u := by rw [Pi.smul_apply, natCast_zsmul]
  · rintro ⟨y, rfl⟩
    rw [hsm, htor]
  · obtain ⟨a, ha, -⟩ := hπ (Pi.mulSingle u y)
    have hak : a ^ k = 1 := hone _ fun v => by
      rw [map_pow, ha]
      by_cases hv : v = u
      · subst hv; rw [Pi.mulSingle_eq_same, hy]
      · rw [Pi.mulSingle_eq_of_ne hv, one_pow]
    obtain ⟨c, hc, -⟩ := hb a hak
    refine ⟨bas (fun i => ((c i).val : ℤ)) u, ?_⟩
    have hprod : ∏ i, P i ^ ((c i).val : ℤ) = a := by
      rw [← hc, List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => zpow_natCast _ _
    rw [← hcomp, hprod, ha, Pi.mulSingle_eq_same]

theorem level_on_factor_of_eighth_power : ∀ (h g : ℕ) (J : Type) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s) (A : Over S) [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (t.A ⟶ A)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)), 0 < k → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left) → (∀ x, lev x ^ k = 1) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ S), (∀ x, (toUnit (Over.mk p) ≫ lev x = 1 ↔ ∃ y, x = k • y)) ∧ ∀ y : Over.mk p ⟶ A, y ^ k = 1 → ∃ x, toUnit _ ≫ lev x = y := by
  intro h g J bas k o _ b S s t A _ _ pr lev hk hpr huniv hlev hpt
  have hcomp : ∀ i u, t.pt i ≫ pr u = lev (bas (Pi.single i 1) u) := fun i u =>
    Over.OverMorphism.ext (hpt i u)
  have hinj : ∀ (T : Over S) (x y : T ⟶ t.A), (∀ u, x ≫ pr u = y ≫ pr u) → x = y :=
    fun T x y hxy => (huniv T (fun u => y ≫ pr u)).unique hxy (fun u => rfl)
  let cg : ∀ T : Over S, CommGroup (T ⟶ t.A) := fun T =>
    { (inferInstance : Group (T ⟶ t.A)) with
      mul_comm := fun x y => hinj T _ _ fun u => by
        have := hpr u
        rw [MonObj.mul_comp, MonObj.mul_comp, _root_.mul_comm] }
  let π : ∀ T : Over S, Fin 8 → ((T ⟶ t.A) →* (T ⟶ A)) := fun T u =>
    MonoidHom.mk' (fun x => x ≫ pr u) (fun x y => by
      have := hpr u
      exact MonObj.mul_comp x y (pr u))
  refine ⟨?_, fun K _ _ p => ?_⟩
  · letI := cg (Out.baseOver S)
    exact levelFactor_torsion (G := Out.baseOver S ⟶ t.A) (H := Out.baseOver S ⟶ A)
      (0 : Fin 8) bas t.pt (π _) lev hlev hcomp k t.torsion
  let T := Over.mk p
  letI := cg T
  let q : T ⟶ Out.baseOver S := Over.homMk p (by simp [T])
  let ρ : (Out.baseOver S ⟶ t.A) →* (T ⟶ t.A) :=
    MonoidHom.mk' (fun x => q ≫ x) (fun x y => MonObj.comp_mul q x y)
  have hq : toUnit T = q := toUnit_unique _ _
  refine levelFactor_bij (G := T ⟶ t.A) (0 : Fin 8) bas (fun i => q ≫ t.pt i) (π T)
    (fun x => toUnit T ≫ lev x) (fun x y => by rw [hlev, MonObj.comp_mul]) (fun i u => ?_) k hk
    (fun i => by
      have h1 := map_pow ρ (t.pt i) k
      rw [t.torsion, map_one] at h1
      exact h1.symm)
    (fun y => huniv T y) (fun y hy => t.bij K p y hy)
  show (q ≫ t.pt i) ≫ pr u = toUnit T ≫ lev (bas (Pi.single i 1) u)
  rw [Category.assoc, hcomp, hq]

end GlobalTheory.ZM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelOnFactorOfEighthPowerAbelianSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_on_factor_of_eighth_power_abelianScheme : ∀ (h g : ℕ) (J : Type) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s) (A : Over S) [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (t.A ⟶ A)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)), 0 < k → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left) → (∀ x, lev x ^ k = 1) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ S), (∀ x, (toUnit (Over.mk p) ≫ lev x = 1 ↔ ∃ y, x = k • y)) ∧ ∀ y : Over.mk p ⟶ A, y ^ k = 1 → ∃ x, toUnit _ ≫ lev x = y := by
  first | exact @GlobalTheory.ZM.level_on_factor_of_eighth_power | exact GlobalTheory.ZM.level_on_factor_of_eighth_power | (intros; apply GlobalTheory.ZM.level_on_factor_of_eighth_power <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEighthPowerPrincipalSiegelOfDense
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SharpFamily

theorem exists_isSharp_of_dense : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsLocallyNoetherian S] [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Odd k → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ c : SiegPre h k (b.ζ : o) s, c.Principal ∧ IsSharp W a bas t c := by
  intro laws _ cube h g W J a bas hW hbas hunit k o _ b em S _ _ s t₀ hk hd₀
  obtain ⟨t, hd, back⟩ := GlobalTheory.T.dense_e8Sharp_after_adjoining_all_matrices h g W J a bas k o b em S s t₀ hunit hd₀
  obtain ⟨rmul, radd, rone, rpt⟩ := GlobalTheory.T.dense_fromSet_sharpClass h g W _ _ bas k o b em S s t hd
  obtain ⟨adj, diag⟩ := GlobalTheory.T.thetaLevel_adjoint_primitive_of_dense_eighth_powers laws.globalFns cube h g W _ _ bas k o b em S s t hd
  letI := t.ab.comm
  let ρ : Matrix (Fin 8) (Fin 8) ℤ → (t.A ⟶ t.A) := fun m => t.act (Sum.inr m)
  obtain ⟨A, _, pr, hA, hpr, hprod, hρ⟩ := GlobalTheory.T.abelianScheme_eighth_power_of_matrix_action S t.A ρ t.ab (fun m => t.hom _)
    (fun m m' => rmul (Sum.inr m) (Sum.inr m') (Sum.inr _) rfl) (fun m m' => radd (Sum.inr m) (Sum.inr m') (Sum.inr _) rfl)
    (rone (Sum.inr 1) rfl)
  letI := hA.comm
  obtain ⟨P, hP, r₁, r₂, hsym, hbi, hiso⟩ := GlobalTheory.T.exists_symmetric_biadditive_bundle_eighthPower W S t.A A pr t.L ρ hW hpr hprod t.isLB
    (cube S t.pol t.L t.isLB) hρ (fun m m' e => adj (Sum.inr m) (Sum.inr m') e) (fun m e => diag (Sum.inr m) e)
  let pt : Fin (2 * g) → (𝟙_ (Over S) ⟶ t.A) := fun i => Over.homMk (t.pt i).left (Over.w (t.pt i))
  let lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A) := fun x =>
    (∏ i, pt i ^ bas.symm (Pi.single 0 x) i) ≫ pr 0
  have hadd : ∀ x y, lev (x + y) = lev x * lev y := fun x y => by
    have := hpr 0
    simp only [lev, Pi.single_add, map_add (f := _), Pi.add_apply, zpow_add, Finset.prod_mul_distrib, MonObj.mul_comp]
  have hpt : ∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left := fun i u => by
    have e₁ : ρ (Matrix.single 0 u 1) ≫ pr 0 = pr u := by
      rw [hρ, List.prod_ofFn, Finset.prod_eq_single u] <;> simp +contextual [Matrix.single_apply, eq_comm]
    have e₂ := rpt (Sum.inr (Matrix.single 0 u 1)) i
    have e₃ : (fun u' => ∑ v, (Sum.elim a id (Sum.inr (Matrix.single 0 u 1)) : Matrix (Fin 8) (Fin 8) ℤ) u' v •
        bas (Pi.single i 1) v) = Pi.single 0 (bas (Pi.single i 1) u) := by
      funext u'
      by_cases hu : u' = 0
      · subst hu
        simp [Matrix.single_apply]
      · simp [Matrix.single_apply, hu, Ne.symm hu]
    rw [e₃, List.prod_ofFn] at e₂
    rw [← e₁, ← Category.assoc, e₂]
    rfl
  obtain ⟨htor, hgeo⟩ := GlobalTheory.T.level_on_factor_of_eighth_power_abelianScheme h g _ bas k o b S s t A pr lev hk.pos hpr hprod hadd hpt
  refine ⟨{ A := A, ab := hA, P := P, isLB := hP, rig₁ := r₁, rig₂ := r₂, symm := hsym, lev := lev, lev_add := hadd,
            lev_tors := htor, geom := fun K _ _ p β z hp hz => ⟨(hgeo K p).1, (hgeo K p).2, fun x y => ?_⟩ },
    ⟨GlobalTheory.T.relAmple_diagonal_biadditive_of_e8Form W S t.A A pr t.L P hW t.ab hA hpr hprod t.isLB hP hbi hiso t.ample,
      GlobalTheory.T.eq_one_of_biadditive_slice_trivial_eighthPower W S t.A A pr t.L P hpr hprod t.isLB hP hsym hbi hiso t.ktriv⟩,
    back _ ⟨pr, hpr, hprod, hiso, fun j u => ?_, hpt⟩⟩
  · have e : unitOn (z ^ (2 * omegaStd x y)) = unitOn z ^ (2 * omegaStd x y) := map_zpow (Units.map _) _ _
    rw [e]
    exact GlobalTheory.T.weilPairing_diagonal_bundle_of_eighthPower_form laws.globalFns h k W S t.A A pr t.L P K p (fun x => toUnit _ ≫ lev x) (unitOn z) hW t.ab hA
      hpr hprod t.isLB hP hsym hbi hiso (fun x y => by rw [hadd, MonObj.comp_mul])
      (fun x => by rw [← MonObj.comp_pow, htor, MonObj.comp_one])
      (GlobalTheory.T.commutatorPairing_e8Sharp_levelPoints laws h g W _ bas k o b S s t A pr lev hbas hpr hprod hadd hpt K p β z hp hz) x y
  · rw [rmul (Sum.inr (Sum.elim a id j)) (Sum.inr 1) j (_root_.mul_one _).symm, rone (Sum.inr 1) rfl, Category.id_comp]
    exact hρ _ u

end GlobalTheory.SharpFamily
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEighthPowerPrincipalSiegelOfDenseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eighthPower_principalSiegel_of_dense : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsLocallyNoetherian S] [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Odd k → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ c : SiegPre h k (b.ζ : o) s, c.Principal ∧ IsSharp W a bas t c := by
  first | exact @GlobalTheory.SharpFamily.exists_isSharp_of_dense | exact GlobalTheory.SharpFamily.exists_isSharp_of_dense | (intros; apply GlobalTheory.SharpFamily.exists_isSharp_of_dense <;> assumption)
end
