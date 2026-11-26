module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLPowerTorsionKernelEqLPartIsogenyDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDegreeIntegerCombinationIsHomogeneous

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicNormDegreeEqPadicNormDetTateModule
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleMapInjectiveCardCokerOfIsogeny
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleMapCokerCardEqKerTorsionCard
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleMapCokerCardEqKerTorsionCard
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TateCoker

variable {l : ℕ} [hl : Fact l.Prime] {M N : Type} [CommGroup M] [CommGroup N] (φ : M →* N)

def lker (l : ℕ) : Subgroup M where
  carrier := {x | φ x = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1}
  mul_mem' := by
    rintro a b ⟨ha, m, hm⟩ ⟨hb, m', hm'⟩
    refine ⟨by rw [map_mul, ha, hb, _root_.one_mul], m + m', ?_⟩
    rw [mul_pow, pow_add, pow_mul, hm, one_pow, mul_comm (l ^ m), pow_mul, hm', one_pow, _root_.one_mul]
  one_mem' := ⟨map_one φ, 0, one_pow _⟩
  inv_mem' := by
    rintro a ⟨ha, m, hm⟩
    exact ⟨by rw [map_inv, ha, inv_one], m, by rw [inv_pow, hm, inv_one]⟩

theorem pow_pow_eq_one {x : M} {m : ℕ} (h : x ^ l ^ m = 1) (j : ℕ) : x ^ l ^ (m + j) = 1 := by
  rw [pow_add, pow_mul, h, one_pow]

variable {φ}

theorem kill [Finite φ.ker] {k : M} (hk : φ k = 1) {m : ℕ} (hm : k ^ l ^ m = 1) :
    k ^ l ^ Nat.card φ.ker = 1 := by
  have hp : l.Prime := hl.out
  have h1 : orderOf k ∣ Nat.card φ.ker := Subgroup.orderOf_dvd_natCard _ hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hm)
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos_iff.2 ⟨⟨⟨1, map_one φ⟩⟩, inferInstance⟩
  have h2 : j ≤ Nat.card φ.ker :=
    ((Nat.lt_pow_self hp.one_lt).trans_le (Nat.le_of_dvd hpos (hj ▸ h1))).le
  exact orderOf_dvd_iff_pow_eq_one.1 (hj ▸ pow_dvd_pow l h2)

theorem exists_lift (hs : Function.Surjective φ) [Finite φ.ker] (n : ℕ) (y : N) (hy : y ^ l ^ n = 1) :
    ∃ x : M, φ x = y ∧ ∃ m : ℕ, x ^ l ^ m = 1 := by
  have hp : l.Prime := hl.out
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, pow_one] at hy
    exact ⟨1, by rw [map_one, hy], 0, one_pow _⟩
  obtain ⟨x₀, rfl⟩ := hs y
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos_iff.2 ⟨⟨⟨1, map_one φ⟩⟩, inferInstance⟩
  have hk : x₀ ^ l ^ n ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, hy]
  have hc : (x₀ ^ l ^ n) ^ Nat.card φ.ker = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ hk)
  obtain ⟨e, u, hu, hcu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' l hp.one_lt.ne'
  have hcop : Nat.Coprime u (l ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hu))
  obtain ⟨w, -, hw⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (Nat.one_lt_pow hn.ne' hp.one_lt)
  refine ⟨x₀ ^ (u * w), ?_, n + e, ?_⟩
  · rw [map_pow, pow_eq_pow_mod _ hy, hw, pow_one]
  · rw [← pow_mul, show u * w * l ^ (n + e) = l ^ n * Nat.card φ.ker * w by rw [hcu, pow_add]; ring,
      pow_mul, pow_mul, hc, one_pow]

theorem indep [Finite φ.ker] {x x' : M} (h : φ x = φ x') {m m' : ℕ} (hx : x ^ l ^ m = 1)
    (hx' : x' ^ l ^ m' = 1) : x ^ l ^ Nat.card φ.ker = x' ^ l ^ Nat.card φ.ker := by
  have h1 : φ (x * x'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 : (x * x'⁻¹) ^ l ^ (m + m') = 1 := by
    rw [mul_pow, inv_pow, pow_pow_eq_one hx, add_comm, pow_pow_eq_one hx', inv_one, _root_.one_mul]
  have h3 := kill h1 h2
  rwa [mul_pow, inv_pow, mul_inv_eq_one] at h3

variable (hs : Function.Surjective φ) [Finite φ.ker]
include hs

def lift (t : Tate l N) (n : ℕ) : M := (exists_lift hs n (t.lev n) (t.lev_pow n)).choose

theorem lift_spec (t : Tate l N) (n : ℕ) : φ (lift hs t n) = t.lev n ∧ ∃ m : ℕ, lift hs t n ^ l ^ m = 1 :=
  (exists_lift hs n (t.lev n) (t.lev_pow n)).choose_spec

def del (t : Tate l N) : M := lift hs t (Nat.card φ.ker) ^ l ^ Nat.card φ.ker

theorem del_eq (t : Tate l N) {x : M} (hx : φ x = t.lev (Nat.card φ.ker)) {m : ℕ} (hm : x ^ l ^ m = 1) :
    del hs t = x ^ l ^ Nat.card φ.ker := by
  obtain ⟨h1, m', h2⟩ := lift_spec hs t (Nat.card φ.ker)
  exact indep (h1.trans hx.symm) h2 hm

theorem del_mem (t : Tate l N) : del hs t ∈ lker φ l := by
  obtain ⟨h1, m, h2⟩ := lift_spec hs t (Nat.card φ.ker)
  refine ⟨by rw [del, map_pow, h1, t.lev_pow], m, ?_⟩
  rw [del, ← pow_mul, mul_comm, pow_mul, h2, one_pow]

def delta : Tate l N →+ Additive (lker φ l) where
  toFun t := Additive.ofMul ⟨del hs t, del_mem hs t⟩
  map_zero' := by
    show Additive.ofMul _ = Additive.ofMul (1 : lker φ l)
    congr 1
    exact Subtype.ext ((del_eq hs 0 (x := 1) (m := 0) (by rw [map_one, Tate.lev_zero]) (one_pow _)).trans
      (one_pow _))
  map_add' s t := by
    show Additive.ofMul _ = Additive.ofMul (_ * _)
    congr 1
    apply Subtype.ext
    obtain ⟨hs1, m, hs2⟩ := lift_spec hs s (Nat.card φ.ker)
    obtain ⟨ht1, m', ht2⟩ := lift_spec hs t (Nat.card φ.ker)
    refine (del_eq hs (s + t) (x := lift hs s _ * lift hs t _) (m := m + m')
      (by rw [map_mul, hs1, ht1, Tate.lev_add]) ?_).trans ?_
    · rw [mul_pow, pow_pow_eq_one hs2, add_comm, pow_pow_eq_one ht2, _root_.one_mul]
    · rw [mul_pow]; rfl

theorem delta_surjective (hd : ∀ x : M, ∃ y, y ^ l = x) : Function.Surjective (delta (l := l) hs) := by
  intro k0
  set a := Nat.card φ.ker
  obtain ⟨⟨k, hk1, m, hm⟩, rfl⟩ : ∃ z : lker φ l, Additive.ofMul z = k0 := ⟨Additive.toMul k0, rfl⟩
  obtain ⟨s, hsa⟩ := GlobalTheory.Published.tate_lev_surj l M hd a k (kill hk1 hm)
  let t : Tate l N := Tate.mk (fun n => φ (s.lev (n + a))) fun n =>
    ⟨by rw [← map_pow, add_comm, s.lev_add_pow, hsa, hk1], by rw [← map_pow, add_right_comm, s.lev_succ]⟩
  refine ⟨t, ?_⟩
  show Additive.ofMul _ = Additive.ofMul _
  congr 1
  apply Subtype.ext
  exact (del_eq hs t (x := s.lev (a + a)) (m := a + a) rfl (s.lev_pow _)).trans
    ((s.lev_add_pow a a).trans hsa)

theorem delta_ker : (delta hs).ker = (LinearMap.range (Tate.map l φ)).toAddSubgroup := by
  set a := Nat.card φ.ker
  ext t
  have e0 : t ∈ (delta hs).ker ↔ del hs t = 1 := by
    rw [AddMonoidHom.mem_ker]
    constructor
    · intro h; exact congrArg Subtype.val (congrArg Additive.toMul h)
    · intro h
      show Additive.ofMul _ = Additive.ofMul (1 : lker φ l)
      exact congrArg Additive.ofMul (Subtype.ext h)
  rw [e0, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  constructor
  · intro h
    have lv : ∀ n, (lift hs t (n + a) ^ l ^ n) ^ l ^ a = 1 := fun n => by
      obtain ⟨h1, m, h2⟩ := lift_spec hs t (n + a)
      rw [← h, del_eq hs t (x := lift hs t (n + a) ^ l ^ n) (m := m)
        (by rw [map_pow, h1, add_comm, t.lev_add_pow]) (by rw [← pow_mul, mul_comm, pow_mul, h2, one_pow])]
    let y : Tate l M := Tate.mk (fun n => lift hs t (n + a) ^ l ^ a) fun n => by
      refine ⟨by rw [← pow_mul, mul_comm, pow_mul]; exact lv n, ?_⟩
      obtain ⟨h1, m, h2⟩ := lift_spec hs t (n + 1 + a)
      obtain ⟨h1', m', h2'⟩ := lift_spec hs t (n + a)
      rw [← pow_mul, mul_comm, pow_mul]
      refine indep (m := m) (m' := m') ?_ (by rw [← pow_mul, mul_comm, pow_mul, h2, one_pow]) h2'
      rw [map_pow, h1, h1', show n + 1 + a = (n + a) + 1 by omega, t.lev_succ]
    refine ⟨y, Tate.ext fun n => ?_⟩
    rw [Tate.lev_map, Tate.lev_mk, map_pow, (lift_spec hs t (n + a)).1, t.lev_add_pow]
  · rintro ⟨y, rfl⟩
    exact (del_eq hs _ (x := y.lev a) (m := a) rfl (y.lev_pow a)).trans (y.lev_pow a)

omit hs in
theorem map_injective' : Function.Injective (Tate.map l φ) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => Tate.ext fun n => ?_
  have h1 : ∀ k, φ (y.lev k) = 1 := fun k => congrArg (·.lev k) hy
  rw [Tate.lev_zero, ← y.lev_add_pow n (Nat.card φ.ker)]
  exact kill (h1 _) (y.lev_pow _)

end GlobalTheory.TateCoker

namespace GlobalTheory


open GlobalTheory.TateCoker in
theorem tate_map_coker_card : ∀ (l : ℕ) [Fact l.Prime] (M N : Type) [CommGroup M] [CommGroup N] (φ : M →* N), (∀ x : M, ∃ y, y ^ l = x) → Function.Surjective φ → Finite φ.ker → Function.Injective (Tate.map l φ) ∧ Nat.card (Tate l N ⧸ LinearMap.range (Tate.map l φ)) = Nat.card {x : M // φ x = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} := by
  intro l _ M N _ _ φ hd hs hf
  refine ⟨map_injective', ?_⟩
  have e1 : (Tate l N ⧸ LinearMap.range (Tate.map l φ)) ≃
      (Tate l N ⧸ (LinearMap.range (Tate.map l φ)).toAddSubgroup) := Equiv.refl _
  rw [Nat.card_congr e1, Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq (delta_ker hs)).symm.toEquiv,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ (delta_surjective hs hd)).toEquiv]
  exact Nat.card_congr (Additive.toMul.trans (Equiv.refl _))

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleMapCokerCardEqKerTorsionCardStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateModuleMap_coker_card_eq_kerTorsion_card : ∀ (l : ℕ) [Fact l.Prime] (M N : Type) [CommGroup M] [CommGroup N] (φ : M →* N), (∀ x : M, ∃ y, y ^ l = x) → Function.Surjective φ → Finite φ.ker → Function.Injective (Tate.map l φ) ∧ Nat.card (Tate l N ⧸ LinearMap.range (Tate.map l φ)) = Nat.card {x : M // φ x = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} := by
  first | exact @GlobalTheory.tate_map_coker_card | exact GlobalTheory.tate_map_coker_card | (intros; apply GlobalTheory.tate_map_coker_card <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleMapInjectiveCardCokerOfIsogeny
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem tmap_injective_card_coker_of_isIsogeny : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
    ∀ (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → Function.Injective (tmap l A B f) ∧
      Nat.card (Tl l B ⧸ LinearMap.range (tmap l A B f)) = l ^ padicValNat l (deg f) := by
  intro K _ l _ hl A B f hf
  have hsurj : Function.Surjective (ptMap f) := (surjective_iff_ptMap_surjective K A B f).1 hf.2
  have hfin : Finite (ptMap f).ker := (isFinite_iff_finite_ker K A B f).1 hf.1
  have hdiv : ∀ x : A.Pt, ∃ y, y ^ l = x := pt_divisible K A l (Fact.out : l.Prime).ne_zero
  obtain ⟨h1, h2⟩ := GlobalTheory.T.tateModuleMap_coker_card_eq_kerTorsion_card l A.Pt B.Pt (ptMap f) hdiv hsurj hfin
  exact ⟨h1, h2.trans (GlobalTheory.T.card_lPowerTorsion_kernel_eq_lPart_isogenyDegree K l hl A B f hf)⟩

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleMapInjectiveCardCokerOfIsogenyStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateModuleMap_injective_card_coker_of_isogeny : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → Function.Injective (tmap l A B f) ∧ Nat.card (Tl l B ⧸ LinearMap.range (tmap l A B f)) = l ^ padicValNat l (deg f) := by
  first | (exact @GlobalTheory.AV.AbVar.tmap_injective_card_coker_of_isIsogeny) | (exact GlobalTheory.AV.AbVar.tmap_injective_card_coker_of_isIsogeny) | (intros; apply GlobalTheory.AV.AbVar.tmap_injective_card_coker_of_isIsogeny  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffTateModuleMapInjectiveAndIsogenyIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffTateModuleMapInjectiveAndIsogenyIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.IsogTate

variable {K : Type} [Field K] (l : ℕ) [Fact l.Prime]

theorem vmap_comp' {A B C : AbVar K} (f : A ⟶ B) (g : B ⟶ C) :
    vmap l (f ≫ g) = vmap l g ∘ₗ vmap l f := by
  simp only [vmap, tmap_comp, LinearMap.baseChange_comp]

theorem vmap_nsmul_id (A : AbVar K) (n : ℕ) (x : Vl l A) :
    vmap l (n • 𝟙 A) x = (n : ℚ_[l]) • x := by
  have h1 : tmap l A A (n • 𝟙 A) = (n : ℤ_[l]) • LinearMap.id := by
    rw [map_nsmul, tmap_id, Nat.cast_smul_eq_nsmul]
  rw [vmap, h1, LinearMap.baseChange_smul, LinearMap.baseChange_id]
  rw [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem tmap_injective_of_finite_ker {A B : AbVar K} (f : A ⟶ B) (hG : Finite (ptMap f).ker) :
    Function.Injective (tmap l A B f) := by
  have hp : l.Prime := Fact.out
  set N := Nat.card (ptMap f).ker with hN
  have hN0 : 0 < N := Nat.card_pos
  have hx : ∀ x ∈ (ptMap f).ker, x ^ N = 1 := fun x hx => by
    have := pow_card_eq_one' (G := (ptMap f).ker) (x := ⟨x, hx⟩)
    exact congrArg Subtype.val this
  refine (injective_iff_map_eq_zero _).2 fun t ht => Tate.ext fun n => ?_
  have hmem : ∀ m, t.lev m ∈ (ptMap f).ker := fun m => by
    rw [MonoidHom.mem_ker, ptMap_apply, ← lev_tmap l f t m, ht]
    rfl
  have h1 : t.lev (n + N) ^ l ^ (n + N) = 1 := t.lev_pow _
  have h2 : t.lev (n + N) ^ N = 1 := hx _ (hmem _)
  have h3 : t.lev (n + N) ^ Nat.gcd (l ^ (n + N)) N = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_left (l ^ (n + N)) N)
  have h4 : l ^ j ≤ N := hj' ▸ Nat.le_of_dvd hN0 (Nat.gcd_dvd_right _ _)
  have h5 : j < N := lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) h4
  have h6 : t.lev (n + N) ^ l ^ N = 1 := by
    obtain ⟨c, hc⟩ := pow_dvd_pow l h5.le
    rw [hc, pow_mul, ← hj', h3, one_pow]
  show t.lev n = 1
  rw [← t.lev_add_pow n N]
  exact h6

theorem isFinite_of_tmap_injective (hl : (l : K) ≠ 0) {A B : AbVar K} (f : A ⟶ B)
    (hf : Function.Injective (tmap l A B f)) : IsFinite f.hom.left := by
  obtain ⟨C, p, i, hp, hi, rfl⟩ := GlobalTheory.T.exists_factorisation_through_abelianSubvariety K A B f
  have hpi : Function.Injective (tmap l A C p) := by
    rw [tmap_comp, LinearMap.coe_comp] at hf
    exact hf.of_comp
  obtain ⟨hA1, hA2, hA3, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  obtain ⟨hC1, hC2, hC3, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl C
  have h1 : 2 * A.dim ≤ 2 * C.dim := by
    rw [← hA3, ← hC3]
    exact LinearMap.finrank_le_finrank_of_injective hpi
  have h2 : C.dim ≤ A.dim := (GlobalTheory.T.abelianVariety_dim_le_of_finite_and_of_surjective K A C p).2 hp
  have h3 : A.dim = C.dim := le_antisymm (by omega) h2
  have hpf : IsFinite p.hom.left := GlobalTheory.T.isFinite_of_surjective_of_dim_eq' K A C p h3 hp
  haveI := hi
  rw [comp_hom, Over.comp_left]
  infer_instance

theorem tmap_injective_of_vmap_injective (hl : (l : K) ≠ 0) {A B : AbVar K} (f : A ⟶ B)
    (hv : Function.Injective (vmap l f)) : Function.Injective (tmap l A B f) := by
  obtain ⟨hA1, -, -, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  obtain ⟨hB1, -, -, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl B
  have hinj : ∀ (X : AbVar K) [Module.Free ℤ_[l] (Tl l X)],
      Function.Injective (fun t : Tl l X => (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] t) := by
    intro X _
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := Tl l X)
      (Algebra.linearMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
    intro s t hst
    apply (TensorProduct.lid ℤ_[l] (Tl l X)).symm.injective
    apply h
    simpa using hst
  intro s t hst
  apply hinj A
  apply hv
  simp only [vmap, LinearMap.baseChange_tmul, hst]

theorem vmap_bijective_of_isIsogeny {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) :
    Function.Bijective (vmap l f) := by
  obtain ⟨n, g, hn, -, hfg, hgf⟩ := GlobalTheory.T.exists_quasiInverse_isogeny' K A B f hf
  have hn' : (n : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hb : ∀ (X : AbVar K), Function.Bijective (vmap l (n • 𝟙 X)) := fun X => by
    constructor
    · intro x y h
      rw [vmap_nsmul_id, vmap_nsmul_id] at h
      exact smul_right_injective _ hn' h
    · intro y
      exact ⟨(n : ℚ_[l])⁻¹ • y, by rw [vmap_nsmul_id, smul_smul, mul_inv_cancel₀ hn', one_smul]⟩
  refine ⟨?_, ?_⟩
  · have h := (hb A).1
    rw [← hfg, vmap_comp', LinearMap.coe_comp] at h
    exact h.of_comp
  · have h := (hb B).2
    rw [← hgf, vmap_comp', LinearMap.coe_comp] at h
    exact h.of_comp

end GlobalTheory.AV.AbVar.IsogTate

namespace GlobalTheory.AV.AbVar


open IsogTate in
theorem isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime],
    (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B),
    (IsFinite f.hom.left ↔ Function.Injective (tmap l A B f)) ∧ (IsIsogeny f ↔ Function.Bijective (vmap l f)) := by
  intro K _ l _ hl A B f
  have h1 : IsFinite f.hom.left ↔ Function.Injective (tmap l A B f) :=
    ⟨fun h => tmap_injective_of_finite_ker l f ((GlobalTheory.T.isFinite_iff_finite_ker' K A B f).1 h), isFinite_of_tmap_injective l hl f⟩
  refine ⟨h1, fun h => vmap_bijective_of_isIsogeny l f h, fun h => ?_⟩
  have hfin := h1.2 (tmap_injective_of_vmap_injective l hl f h.1)
  obtain ⟨-, -, -, hA4, hA5⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  obtain ⟨-, -, -, hB4, hB5⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl B
  have hd : 2 * A.dim = 2 * B.dim := by
    rw [← hA5, ← hB5]
    exact (LinearEquiv.ofBijective _ h).finrank_eq
  exact ⟨hfin, GlobalTheory.T.surjective_of_isFinite_of_dim_eq_abelianVarietyHom K A B f (by omega) hfin⟩

end GlobalTheory.AV.AbVar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffTateModuleMapInjectiveAndIsogenyIffStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_iff_tateModuleMap_injective_and_isogeny_iff : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B), (IsFinite f.hom.left ↔ Function.Injective (tmap l A B f)) ∧ (IsIsogeny f ↔ Function.Bijective (vmap l f)) := by
  first | exact @GlobalTheory.AV.AbVar.isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective | exact GlobalTheory.AV.AbVar.isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective | (intros; apply GlobalTheory.AV.AbVar.isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetEqInvCardCoker
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetEqInvCardCoker
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory
namespace DetIndexPadic

theorem norm_card_quot_span (l : ℕ) [Fact l.Prime] {x : ℤ_[l]} (hx : x ≠ 0) :
    ‖((Nat.card (ℤ_[l] ⧸ Ideal.span {x}) : ℕ) : ℚ_[l])‖ = ‖x‖ := by
  have h1 : Ideal.span {x} = RingHom.ker (PadicInt.toZModPow (p := l) x.valuation) := by
    rw [PadicInt.ker_toZModPow]
    conv_lhs => rw [PadicInt.unitCoeff_spec hx]
    exact Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff hx).isUnit _
  have h2 : Nat.card (ℤ_[l] ⧸ Ideal.span {x}) = l ^ x.valuation := by
    rw [h1, Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow (p := l) x.valuation))).toEquiv, Nat.card_zmod]
  rw [h2, PadicInt.norm_eq_zpow_neg_valuation hx]
  push_cast
  rw [Padic.norm_p_pow]

theorem det_ne_zero_of_finite_coker (l : ℕ) [Fact l.Prime] {T : Type} [AddCommGroup T]
    [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (φ : T →ₗ[ℤ_[l]] T)
    (hc : Nat.card (T ⧸ LinearMap.range φ) ≠ 0) : LinearMap.det φ ≠ 0 := by
  classical
  set n := Nat.card (T ⧸ LinearMap.range φ)
  have hk : ∀ x : T, ∃ y, φ y = ((n : ℤ_[l])) • x := by
    intro x
    have h0 := card_nsmul_eq_zero' (G := T ⧸ LinearMap.range φ)
      (x := Submodule.Quotient.mk x)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨y, hy⟩ := h0
    exact ⟨y, by rw [hy, Nat.cast_smul_eq_nsmul]⟩
  let b := Module.Free.chooseBasis ℤ_[l] T
  choose c hc' using fun i => hk (b i)
  let ψ : T →ₗ[ℤ_[l]] T := b.constr ℤ_[l] c
  have hcomp : φ ∘ₗ ψ = (n : ℤ_[l]) • LinearMap.id := by
    refine b.ext fun i => ?_
    simp [ψ, hc']
  have hd := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_id, _root_.mul_one] at hd
  intro h0
  rw [h0, zero_mul] at hd
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 hc) hd.symm

theorem norm_det_eq_of_card_coker : ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T]
    [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (φ : T →ₗ[ℤ_[l]] T) (a : ℕ),
    Nat.card (T ⧸ LinearMap.range φ) = l ^ a → ‖LinearMap.det φ‖ = (l : ℝ) ^ (-(a : ℤ)) := by
  intro l _ T _ _ _ _ φ a hcard
  classical
  have hl := (Fact.out : l.Prime)
  have hdet : LinearMap.det φ ≠ 0 := det_ne_zero_of_finite_coker l φ
    (by rw [hcard]; exact pow_ne_zero _ hl.ne_zero)
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.2 h)
  set N := LinearMap.range φ with hN
  let e : T ≃ₗ[ℤ_[l]] N := LinearEquiv.ofInjective φ hinj
  let b := Module.Free.chooseBasis ℤ_[l] T
  have h : Module.finrank ℤ_[l] N = Module.finrank ℤ_[l] T := e.symm.finrank_eq
  let c := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let cb := Submodule.smithNormalFormBotBasis b h
  have cb_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : T ≃ₗ[ℤ_[l]] N := b'.equiv cb (Equiv.refl _)
  let f : T →ₗ[ℤ_[l]] T := N.subtype ∘ₗ (e' : T →ₗ[ℤ_[l]] N)
  have hc : ∀ i, f (b' i) = c i • b' i := by
    intro i
    have : f (b' i) = b'.equiv cb (Equiv.refl _) (b' i) := rfl
    rw [this, b'.equiv_apply, Equiv.refl_apply]
    exact cb_eq i
  have hm : LinearMap.toMatrix b' b' f = Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix_apply, hc, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, _root_.mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hass := LinearMap.associated_det_comp_equiv N.subtype e e'
  have h0 : N.subtype ∘ₗ (e : T →ₗ[ℤ_[l]] N) = φ := by
    ext x; rfl
  rw [h0] at hass
  have h1 : LinearMap.det f = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix b', hm, Matrix.det_diagonal]
  change Associated (LinearMap.det φ) (LinearMap.det f) at hass
  rw [h1] at hass
  have hcq : Nat.card (T ⧸ N) = ∏ i, Nat.card (ℤ_[l] ⧸ Ideal.span {c i}) := by
    rw [← Nat.card_pi]
    exact Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv
  have hne : ∏ i, c i ≠ 0 := fun h0 => hdet (hass.eq_zero_iff.2 h0)
  obtain ⟨u, hu⟩ := hass
  have h2 : ‖LinearMap.det φ‖ = ‖∏ i, c i‖ := by
    rw [← hu, norm_mul, PadicInt.norm_units, _root_.mul_one]
  have h3 : ‖∏ i, c i‖ = ‖((Nat.card (T ⧸ N) : ℕ) : ℚ_[l])‖ := by
    rw [hcq, Nat.cast_prod, norm_prod, norm_prod]
    exact Finset.prod_congr rfl fun i hi =>
      (norm_card_quot_span l (Finset.prod_ne_zero_iff.1 hne i hi)).symm
  rw [h2, h3, hcard]
  push_cast
  rw [Padic.norm_p_pow]

end DetIndexPadic
end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetEqInvCardCokerStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_det_eq_inv_card_coker : ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (φ : T →ₗ[ℤ_[l]] T) (a : ℕ), Nat.card (T ⧸ LinearMap.range φ) = l ^ a → ‖LinearMap.det φ‖ = (l : ℝ) ^ (-(a : ℤ)) := by
  first | (exact @GlobalTheory.DetIndexPadic.norm_det_eq_of_card_coker) | (exact GlobalTheory.DetIndexPadic.norm_det_eq_of_card_coker) | (intros; apply GlobalTheory.DetIndexPadic.norm_det_eq_of_card_coker  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicNormDegreeEqPadicNormDetTateModule
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem norm_natCast_padicInt (l : ℕ) [Fact l.Prime] {n : ℕ} (hn : n ≠ 0) :
    ‖((n : ℕ) : ℤ_[l])‖ = (l : ℝ) ^ (-(padicValNat l n : ℤ)) := by
  rw [PadicInt.norm_def]
  push_cast
  have h := Padic.eq_padicNorm (p := l) (n : ℚ)
  push_cast at h
  rw [h, padicNorm.eq_zpow_of_ne_zero (by exact_mod_cast hn)]
  push_cast
  rw [Nat.padicValNat_def, padicValRat_of_nat]

theorem norm_deg_eq_norm_det : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A),
    ‖((deg (A := A) (B := A) f.asHom : ℕ) : ℤ_[l])‖ = ‖LinearMap.det (tend l A f)‖ := by
  intro K _ l _ hl A f
  obtain ⟨hfree, hfin, -, hVfin, -⟩ := tl_free_finrank K l hl A
  by_cases hf : IsIsogeny (A := A) (B := A) f.asHom
  · obtain ⟨-, -, hpos, -⟩ := isogeny_flat_finrank K A A f.asHom hf
    obtain ⟨-, hcard⟩ := GlobalTheory.T.tateModuleMap_injective_card_coker_of_isogeny K l hl A A f.asHom hf
    have hdet := GlobalTheory.T.norm_det_eq_inv_card_coker l (Tl l A)
      (tmap l A A f.asHom) (padicValNat l (deg f.asHom)) hcard
    change _ = ‖LinearMap.det (tmap l A A f.asHom)‖
    rw [hdet, norm_natCast_padicInt l hpos.ne']
  · have hdeg : deg (A := A) (B := A) f.asHom = 0 := by rw [deg, ite_eq_right hf]
    rw [hdeg, Nat.cast_zero, norm_zero, eq_comm, norm_eq_zero]
    by_contra hne
    apply hf
    rw [(GlobalTheory.T.isFinite_iff_tateModuleMap_injective_and_isogeny_iff K l hl A A f.asHom).2]
    have hu : IsUnit (LinearMap.det (vmap l f.asHom)) := by
      rw [vmap, LinearMap.det_baseChange]
      exact (isUnit_iff_ne_zero).2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])).2 hne)
    rw [← LinearMap.isUnit_iff_isUnit_det] at hu
    exact (Module.End.isUnit_iff _).1 hu

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicNormDegreeEqPadicNormDetTateModuleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicNorm_degree_eq_padicNorm_det_tateModule : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A), ‖((deg (A := A) (B := A) f.asHom : ℕ) : ℤ_[l])‖ = ‖LinearMap.det (tend l A f)‖ := by
  intro K _ l _ hl A f
  obtain ⟨hfree, hfin, -, hVfin, -⟩ := tl_free_finrank K l hl A
  by_cases hf : IsIsogeny (A := A) (B := A) f.asHom
  · obtain ⟨-, -, hpos, -⟩ := isogeny_flat_finrank K A A f.asHom hf
    obtain ⟨-, hcard⟩ :=
      GlobalTheory.T.tateModuleMap_injective_card_coker_of_isogeny K l hl A A f.asHom hf
    have hdet := GlobalTheory.T.norm_det_eq_inv_card_coker l (Tl l A)
      (tmap l A A f.asHom) (padicValNat l (deg f.asHom)) hcard
    have hnorm : ‖((deg f.asHom : ℕ) : ℤ_[l])‖ =
        (l : ℝ) ^ (-(padicValNat l (deg f.asHom) : ℤ)) := by
      rw [PadicInt.norm_def]
      push_cast
      have h := Padic.eq_padicNorm (p := l) (deg f.asHom : ℚ)
      push_cast at h
      rw [h, padicNorm.eq_zpow_of_ne_zero (by exact_mod_cast hpos.ne'), padicValRat.of_nat,
        Rat.cast_zpow, Rat.cast_natCast, Nat.padicValNat_def]
    change _ = ‖LinearMap.det (tmap l A A f.asHom)‖
    rw [hdet, hnorm]
  · have hdeg : deg (A := A) (B := A) f.asHom = 0 := by rw [deg, ite_eq_right hf]
    rw [hdeg, Nat.cast_zero, norm_zero, eq_comm, norm_eq_zero]
    by_contra hne
    apply hf
    rw [(GlobalTheory.T.isFinite_iff_tateModuleMap_injective_and_isogeny_iff K l hl A A f.asHom).2]
    have hu : IsUnit (LinearMap.det (vmap l f.asHom)) := by
      rw [vmap, LinearMap.det_baseChange]
      exact (isUnit_iff_ne_zero).2
        ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])).2 hne)
    rw [← LinearMap.isUnit_iff_isUnit_det] at hu
    exact (Module.End.isUnit_iff _).1 hu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDegreePolynomialMapEqCharpolyRatio
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AV.AbVar

theorem map_eq_charpoly_vmap : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
    ∀ (A : AbVar K) [Module.Finite ℚ_[l] (Vl l A)] (f : End A) (P : Polynomial ℚ),
    P.Monic → P.natDegree = 2 * A.dim →
    (∀ n : ℤ, P.eval (n : ℚ) = (deg (A := A) (B := A) ((n : End A) - f).asHom : ℚ)) →
    P.map (algebraMap ℚ ℚ_[l]) = (vmap l (A := A) (B := A) f.asHom).charpoly := by
  intro K _ l _ hl A _ f P hPm hPd hP
  obtain ⟨hfree, hfin, -, -, hrkV⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  let δ : Polynomial ℤ → ℚ := fun F => (deg (A := A) (B := A) (Polynomial.aeval f F).asHom : ℚ)
  have hmul : ∀ F G, δ (F * G) = δ F * δ G := by
    intro F G
    simp only [δ, map_mul]
    rw [End.mul_asHom, (GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K A A A _ _ rfl rfl).2]
    push_cast
    exact mul_comm _ _
  have hpoly : ∀ (n : ℕ) (u : Fin n → Polynomial ℤ), ∃ Φ : MvPolynomial (Fin n) ℚ, Φ.IsHomogeneous (2 * A.dim) ∧
      ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) Φ = δ (∑ i, m i • u i) := by
    intro n u
    obtain ⟨Φ, hΦ, hΦe⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl n (fun i => (Polynomial.aeval f (u i)).asHom)
    refine ⟨Φ, hΦ, fun m => ?_⟩
    rw [hΦe m]
    have hz (k : ℤ) (g : End A) : (k • g).asHom = k • g.asHom :=
      map_zsmul End.addEquiv k g
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [δ, map_sum, map_zsmul, End.sum_asHom, hz]
  have hPn : ∀ n : ℤ, P.eval (n : ℚ) = δ (Polynomial.C n - Polynomial.X) := by
    intro n
    rw [hP n]
    simp only [δ, map_sub, map_intCast, Polynomial.aeval_X, eq_intCast]
  have hroots := GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm (PadicAlgCl l) A.dim δ P hmul hpoly hPm hPd hPn
  apply GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq l
  · exact hPm.map _
  · exact LinearMap.charpoly_monic _
  · rw [Polynomial.natDegree_map, hPd, LinearMap.charpoly_natDegree, hrkV]
  · intro F
    have h1 : (P.map (algebraMap ℚ ℚ_[l])).aroots (PadicAlgCl l) = P.aroots (PadicAlgCl l) := by
      simp only [Polynomial.aroots, Polynomial.map_map]
      congr 2
    rw [h1]
    refine (congrArg norm (hroots F)).symm.trans ?_
    have h2 := GlobalTheory.T.det_aeval_eq_prod_aroots_charpoly' ℚ_[l] (PadicAlgCl l) (Vl l A) (vmap l f.asHom) (F.map (algebraMap ℤ ℚ_[l]))
    simp only [Polynomial.aeval_map_algebraMap] at h2
    rw [← h2]
    let t : End A →+* Module.End ℤ_[l] (Tl l A) :=
      { toFun := fun g => tmap l A A g.asHom
        map_one' := tmap_id l A
        map_mul' := fun g h => tmap_comp l h.asHom g.asHom
        map_zero' := map_zero (tmap l A A)
        map_add' := fun g h => map_add (tmap l A A) g.asHom h.asHom }
    let ψ : End A →+* Module.End ℚ_[l] (Vl l A) :=
      (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)).toRingHom.comp t
    have hψ : vmap l (A := A) (B := A) f.asHom = ψ f := rfl
    have hev : ∀ G : Polynomial ℤ, Polynomial.aeval (ψ f) G = ψ (Polynomial.aeval f G) := by
      intro G
      induction G using Polynomial.induction_on with
      | C a => simp
      | add p q hp hq => simp only [map_add (f := _), hp, hq]
      | monomial n a _ => simp only [map_mul, map_pow, Polynomial.aeval_X, eq_intCast, map_intCast]
    rw [hψ, hev F]
    have h3 : ψ (Polynomial.aeval f F) = (tmap l A A (Polynomial.aeval f F).asHom).baseChange ℚ_[l] := rfl
    rw [h3, LinearMap.det_baseChange, PadicAlgCl.norm_extends]
    have h4 (g : A ⟶ A) : ‖(deg g : ℤ_[l])‖ = ‖LinearMap.det (tmap l A A g)‖ := by
      by_cases hg : IsIsogeny g
      · obtain ⟨-, -, hpos, -⟩ := isogeny_flat_finrank K A A g hg
        obtain ⟨-, hcard⟩ := GlobalTheory.T.tateModuleMap_injective_card_coker_of_isogeny K l hl A A g hg
        rw [GlobalTheory.T.norm_det_eq_inv_card_coker l (Tl l A) (tmap l A A g) _ hcard,
          norm_natCast_padicInt l hpos.ne']
      · have hdeg : deg g = 0 := by simp [deg, hg]
        rw [hdeg, Nat.cast_zero, norm_zero, eq_comm, norm_eq_zero]
        by_contra hne
        apply hg
        rw [(GlobalTheory.T.isFinite_iff_tateModuleMap_injective_and_isogeny_iff K l hl A A g).2]
        have hu : IsUnit (LinearMap.det (vmap l g)) := by
          rw [vmap, LinearMap.det_baseChange]
          exact (isUnit_iff_ne_zero).2
            ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])).2 hne)
        rw [← LinearMap.isUnit_iff_isUnit_det] at hu
        exact (Module.End.isUnit_iff _).1 hu
    have h5 : algebraMap ℚ (PadicAlgCl l) (δ F) = algebraMap ℚ_[l] (PadicAlgCl l) ((deg (A := A) (B := A) (Polynomial.aeval f F).asHom : ℕ) : ℚ_[l]) := by
      simp only [δ, map_natCast]
    rw [h5, PadicAlgCl.norm_extends]
    simpa only [PadicInt.norm_def, PadicInt.coe_natCast, PadicInt.algebraMap_apply] using
      h4 (Polynomial.aeval f F).asHom

end GlobalTheory.AV.AbVar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDegreePolynomialMapEqCharpolyRatioStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate :
    ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
      ∀ (A : AbVar K) [Module.Finite ℚ_[l] (Vl l A)] (f : End A) (P : Polynomial ℚ),
        P.Monic → P.natDegree = 2 * A.dim →
          (∀ n : ℤ, P.eval (n : ℚ) = (deg ((n : End A) - f).asHom : ℚ)) →
            P.map (algebraMap ℚ ℚ_[l]) = (vmap l f.asHom).charpoly := by
  intro K _ l _ hl A _ f P hPm hPd hP
  have hCharpoly : P.map (algebraMap ℚ ℚ_[l]) = (vmap l f.asHom).charpoly := by
    obtain ⟨hfree, hfin, -, -, hrkV⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
    let δ : Polynomial ℤ → ℚ := fun F => (deg (A := A) (B := A) (Polynomial.aeval f F).asHom : ℚ)
    have hmul : ∀ F G, δ (F * G) = δ F * δ G := by
      intro F G
      simp only [δ, map_mul]
      rw [End.mul_asHom, (GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K A A A _ _ rfl rfl).2]
      push_cast
      exact mul_comm _ _
    have hpoly : ∀ (n : ℕ) (u : Fin n → Polynomial ℤ), ∃ Φ : MvPolynomial (Fin n) ℚ, Φ.IsHomogeneous (2 * A.dim) ∧
        ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) Φ = δ (∑ i, m i • u i) := by
      intro n u
      obtain ⟨Φ, hΦ, hΦe⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl n (fun i => (Polynomial.aeval f (u i)).asHom)
      refine ⟨Φ, hΦ, fun m => ?_⟩
      rw [hΦe m]
      have hz (k : ℤ) (g : End A) : (k • g).asHom = k • g.asHom :=
        map_zsmul (End.addEquiv (X := A)) k g
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [δ, map_sum, map_zsmul, End.sum_asHom, hz]
    have hPn : ∀ n : ℤ, P.eval (n : ℚ) = δ (Polynomial.C n - Polynomial.X) := by
      intro n
      rw [hP n]
      simp only [δ, map_sub, map_intCast, Polynomial.aeval_X, eq_intCast]
    have hroots := GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm (PadicAlgCl l) A.dim δ P hmul hpoly hPm hPd hPn
    apply GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq l
    · exact hPm.map _
    · exact LinearMap.charpoly_monic _
    · rw [Polynomial.natDegree_map, hPd, LinearMap.charpoly_natDegree, hrkV]
    · intro F
      have h1 : (P.map (algebraMap ℚ ℚ_[l])).aroots (PadicAlgCl l) = P.aroots (PadicAlgCl l) := by
        simp only [Polynomial.aroots, Polynomial.map_map]
        congr 2
      rw [h1]
      refine (congrArg norm (hroots F)).symm.trans ?_
      have h2 := GlobalTheory.T.det_aeval_eq_prod_aroots_charpoly' ℚ_[l] (PadicAlgCl l) (Vl l A) (vmap l f.asHom) (F.map (algebraMap ℤ ℚ_[l]))
      simp only [Polynomial.aeval_map_algebraMap] at h2
      rw [← h2]
      let t : End A →+* Module.End ℤ_[l] (Tl l A) :=
        { toFun := fun g => tmap l A A g.asHom
          map_one' := tmap_id l A
          map_mul' := fun g h => tmap_comp l h.asHom g.asHom
          map_zero' := map_zero (tmap l A A)
          map_add' := fun g h => map_add (tmap l A A) g.asHom h.asHom }
      let ψ : End A →+* Module.End ℚ_[l] (Vl l A) :=
        (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)).toRingHom.comp t
      have hψ : vmap l f.asHom = ψ f := rfl
      have hev (G : Polynomial ℤ) : Polynomial.aeval (ψ f) G = ψ (Polynomial.aeval f G) := by
        induction G using Polynomial.induction_on with
        | C a => simp
        | add p q hp hq => simp only [map_add, hp, hq]
        | monomial n a _ => simp only [map_mul, map_pow, Polynomial.aeval_X, eq_intCast, map_intCast]
      rw [hψ, hev F]
      let g := (Polynomial.aeval f F).asHom
      have h3 : ψ (Polynomial.aeval f F) = (tmap l A A g).baseChange ℚ_[l] := rfl
      rw [h3, LinearMap.det_baseChange, PadicAlgCl.norm_extends]
      have hnorm : ‖(deg g : ℤ_[l])‖ = ‖LinearMap.det (tmap l A A g)‖ := by
        by_cases hg : IsIsogeny g
        · obtain ⟨-, -, hpos, -⟩ := isogeny_flat_finrank K A A g hg
          obtain ⟨-, hcard⟩ :=
            GlobalTheory.T.tateModuleMap_injective_card_coker_of_isogeny K l hl A A g hg
          have hdet := GlobalTheory.T.norm_det_eq_inv_card_coker l (Tl l A) (tmap l A A g)
            (padicValNat l (deg g)) hcard
          rw [hdet, norm_natCast_padicInt l hpos.ne']
        · have hdeg : deg g = 0 := by rw [deg, ite_eq_right hg]
          rw [hdeg, Nat.cast_zero, norm_zero, eq_comm, norm_eq_zero]
          by_contra hdet
          apply hg
          rw [(GlobalTheory.T.isFinite_iff_tateModuleMap_injective_and_isogeny_iff K l hl A A g).2]
          have hu : IsUnit (LinearMap.det (vmap l g)) := by
            rw [vmap, LinearMap.det_baseChange]
            exact (isUnit_iff_ne_zero).2
              ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])).2 hdet)
          rw [← LinearMap.isUnit_iff_isUnit_det] at hu
          exact (Module.End.isUnit_iff _).1 hu
      have hcast : algebraMap ℚ (PadicAlgCl l) (δ F) =
          algebraMap ℚ_[l] (PadicAlgCl l) (deg g : ℚ_[l]) := by
        simp only [δ, g, map_natCast]
      rw [hcast, PadicAlgCl.norm_extends]
      rw [PadicInt.norm_def] at hnorm
      simpa using hnorm
  exact hCharpoly
end
