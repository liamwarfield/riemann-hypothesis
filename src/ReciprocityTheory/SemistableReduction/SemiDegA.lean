module

public import ReciprocityTheory.SemistableReduction.SemiDegSt

@[expose] public section

section -- merged from ReciprocityTheory.SemistableReduction.SemiDegAB
section -- merged from ReciprocityTheory.SemistableReduction.SemiDegAA
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Module

def waR {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (x : Fin r → K) :
    (Fin r → K) →ₗ[K] K where
  toFun y := S.h x y
  map_add' y z := by
    simp only [HermForm.h, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a y := by
    simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem waR_apply {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : waR S x y = S.h x y := rfl

theorem wa_symm {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : S.h y x = S.c (S.h x y) := by
  unfold HermForm.h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, S.c_invol, S.G_herm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem wa_sub_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y z : Fin r → K) : S.h x (y - z) = S.h x y - S.h x z := by
  simp only [HermForm.h, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem wa_smul_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (x y : Fin r → K) : S.h x (a • y) = a * S.h x y := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem wa_zero_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x : Fin r → K) : S.h x 0 = 0 := by
  simp [HermForm.h]

theorem wa_sub_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y z : Fin r → K) : S.h (x - y) z = S.h x z - S.h y z := by
  simp only [HermForm.h, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem wa_smul_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (x y : Fin r → K) : S.h (a • x) y = S.c a * S.h x y := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem wa_sum_right {K : Type} [Field K] [NumberField K] {r n : ℕ} (S : HermForm K r)
    (x : Fin r → K) (t : Fin n → K) (b : Fin n → Fin r → K) :
    S.h x (∑ i, t i • b i) = ∑ i, t i * S.h x (b i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← waR_apply S x, map_sum]
  simp only [map_smul, smul_eq_mul, waR_apply]

theorem wa_sum_left {K : Type} [Field K] [NumberField K] {r n : ℕ} (S : HermForm K r)
    (y : Fin r → K) (t : Fin n → K) (b : Fin n → Fin r → K) :
    S.h (∑ i, t i • b i) y = ∑ i, S.c (t i) * S.h (b i) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [wa_symm S y, wa_sum_right, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← wa_symm S y (b i)]

theorem wa_finrank_inf_ker {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V) (f : V →ₗ[K] K) (z : V) (hz : z ∈ W)
    (hfz : f z ≠ 0) : finrank K ↥(W ⊓ LinearMap.ker f) + 1 = finrank K W := by
  have hsup : W ⊔ LinearMap.ker f = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = (f v / f z) • z + (v - (f v / f z) • z) := by abel
    rw [hv]
    refine Submodule.add_mem_sup (W.smul_mem _ hz) ?_
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfz, sub_self]
  have hker : finrank K (LinearMap.ker f) + 1 = finrank K V := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    have hr : LinearMap.range f = ⊤ := by
      rw [eq_top_iff]
      intro a _
      exact ⟨(a / f z) • z, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfz]⟩
    rw [hr, finrank_top, Module.finrank_self] at h
    omega
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker f)
  rw [hsup, finrank_top] at h
  omega

theorem wa_diag {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) :
    ∀ (n : ℕ) (W : Submodule K (Fin r → K)), finrank K W = n →
      (∀ x ∈ W, S.h x x = 0 → x = 0) →
      ∃ b : Fin n → Fin r → K, (∀ i, b i ∈ W) ∧ (∀ i, b i ≠ 0) ∧
        ∀ i j, i ≠ j → S.h (b i) (b j) = 0 := by
  intro n
  induction n with
  | zero =>
    intro W _ _
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro W hW han
    have hne : W ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hW
      omega
    obtain ⟨z, hzW, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hzz : S.h z z ≠ 0 := fun h => hz0 (han z hzW h)
    have hW' : finrank K ↥(W ⊓ LinearMap.ker (waR S z)) = n := by
      have h := wa_finrank_inf_ker W (waR S z) z hzW (by rw [waR_apply]; exact hzz)
      omega
    obtain ⟨b, hbW, hb0, hbo⟩ := ih (W ⊓ LinearMap.ker (waR S z)) hW' (fun x hx hxx => han x hx.1 hxx)
    have hk : ∀ k, S.h z (b k) = 0 := fun k => (hbW k).2
    refine ⟨Fin.cons z b, fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
    · cases i using Fin.cases with
      | zero => simpa using hzW
      | succ i => simpa using (hbW i).1
    · cases i using Fin.cases with
      | zero => simpa using hz0
      | succ i => simpa using hb0 i
    · cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using hk j
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.cons_succ, Fin.cons_zero]
          rw [wa_symm S z (b i), hk i, map_zero]
        | succ j =>
          simp only [Fin.cons_succ]
          exact hbo i j fun h => hij (by rw [h])

theorem wa_hyp {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (W : Submodule K (Fin r → K)) (hnd : ∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0)
    (x : Fin r → K) (hxW : x ∈ W) (hx0 : x ≠ 0) (hxx : S.h x x = 0) :
    ∃ y ∈ W, S.h x y = 1 ∧ S.h y y = 0 := by
  obtain ⟨w, hwW, hw⟩ : ∃ w ∈ W, S.h x w ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx0 (hnd x hxW hc)
  obtain ⟨u, hu⟩ : ∃ u, u = (S.h x w)⁻¹ • w := ⟨_, rfl⟩
  have huW : u ∈ W := hu ▸ W.smul_mem _ hwW
  have hxu : S.h x u = 1 := by rw [hu, wa_smul_right, inv_mul_cancel₀ hw]
  have hux : S.h u x = 1 := by rw [wa_symm S x u, hxu, map_one]
  have hcuu : S.c (S.h u u) = S.h u u := (wa_symm S u u).symm
  obtain ⟨t, ht⟩ : ∃ t, t = S.h u u / 2 := ⟨_, rfl⟩
  have hct : S.c t = t := by rw [ht, map_div₀, hcuu, map_ofNat]
  refine ⟨u - t • x, W.sub_mem huW (W.smul_mem _ hxW), ?_, ?_⟩
  · rw [wa_sub_right, hxu, wa_smul_right, hxx, mul_zero, sub_zero]
  · simp only [wa_sub_left, wa_sub_right, wa_smul_left, wa_smul_right, hux, hxu, hxx, hct]
    rw [ht]
    ring

theorem wa_perp_nondeg {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (W : Submodule K (Fin r → K)) (hnd : ∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0)
    (x y : Fin r → K) (hxW : x ∈ W) (hyW : y ∈ W) (hxx : S.h x x = 0) (hxy : S.h x y = 1)
    (hyy : S.h y y = 0) :
    ∀ z ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y),
      (∀ w ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y), S.h z w = 0) → z = 0 := by
  intro z hz hzo
  obtain ⟨⟨hzW, hzx⟩, hzy⟩ := hz
  have hzx : S.h x z = 0 := hzx
  have hzy : S.h y z = 0 := hzy
  apply hnd z hzW
  intro w hwW
  have hyx : S.h y x = 1 := by rw [wa_symm S x y, hxy, map_one]
  have hw' : w - S.h y w • x - S.h x w • y ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y) := by
    refine ⟨⟨W.sub_mem (W.sub_mem hwW (W.smul_mem _ hxW)) (W.smul_mem _ hyW), ?_⟩, ?_⟩
    · show S.h x _ = 0
      simp only [wa_sub_right, wa_smul_right, hxx, hxy]
      ring
    · show S.h y _ = 0
      simp only [wa_sub_right, wa_smul_right, hyx, hyy]
      ring
  have h1 := hzo _ hw'
  have hzx' : S.h z x = 0 := by rw [wa_symm S x z, hzx, map_zero]
  have hzy' : S.h z y = 0 := by rw [wa_symm S y z, hzy, map_zero]
  simp only [wa_sub_right, wa_smul_right, hzx', hzy', mul_zero, sub_zero] at h1
  exact h1

end ReciprocityTheory.MultiplicativeHeights
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Module

theorem wa_cases3 {n : ℕ} (i : Fin (n + 2)) :
    i = 0 ∨ i = Fin.last (n + 1) ∨ ∃ j : Fin n, i = (Fin.castSucc j).succ := by
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · exact Or.inl h
  · right
    induction j using Fin.lastCases with
    | last => left; simp
    | cast j => right; exact ⟨j, rfl⟩

def waExt {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) : Fin (n + 2) → α :=
  Fin.cons x (Fin.snoc f y : Fin (n + 1) → α)

@[simp] theorem waExt_zero {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) :
    waExt x y f 0 = x := by
  simp [waExt]

@[simp] theorem waExt_last {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) :
    waExt x y f (Fin.last (n + 1)) = y := by
  rw [waExt, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]

@[simp] theorem waExt_mid {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) (j : Fin n) :
    waExt x y f (Fin.castSucc j).succ = f j := by
  rw [waExt, Fin.cons_succ, Fin.snoc_castSucc]

theorem wa_witt_apply {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i j : Fin r) :
    wittMat r m g i j = if (i : ℕ) + j + 1 = r ∧ ((i : ℕ) < m ∨ (j : ℕ) < m) then 1
      else if (i : ℕ) = j ∧ m ≤ (i : ℕ) ∧ (i : ℕ) + m < r then g i else 0 := by
  unfold wittMat
  simp only [Matrix.of_apply, Fin.val_inj]

theorem wa_main {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) :
    ∀ (n : ℕ) (W : Submodule K (Fin r → K)), finrank K W = n →
      (∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0) →
      ∃ (m : ℕ) (b : Fin n → Fin r → K) (g : Fin n → K), (∀ i, b i ∈ W) ∧ 2 * m ≤ n ∧
        (∀ i j, S.h (b i) (b j) = wittMat n m g i j) ∧
        ∀ t : Fin n → K, (∀ i : Fin n, (i : ℕ) < m ∨ n ≤ (i : ℕ) + m → t i = 0) →
          ∑ i, S.c (t i) * g i * t i = 0 → t = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hW hnd
  by_cases hiso : ∃ x ∈ W, x ≠ 0 ∧ S.h x x = 0
  · obtain ⟨x, hxW, hx0, hxx⟩ := hiso
    obtain ⟨y, hyW, hxy, hyy⟩ := wa_hyp S W hnd x hxW hx0 hxx
    have hyx : S.h y x = 1 := by rw [wa_symm, hxy, map_one]
    have hf1 := wa_finrank_inf_ker W (waR S x) y hyW
      (by rw [waR_apply, hxy]; exact one_ne_zero)
    have hf2 := wa_finrank_inf_ker (W ⊓ LinearMap.ker (waR S x)) (waR S y) x
      (Submodule.mem_inf.mpr ⟨hxW, by rw [LinearMap.mem_ker, waR_apply, hxx]⟩)
      (by rw [waR_apply, hyx]; exact one_ne_zero)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 :=
      ⟨finrank K ↥(W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y)), by omega⟩
    obtain ⟨m', b', g', hb'W, hm', hgram', hani'⟩ := ih n' (by omega)
      (W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y)) (by omega)
      (wa_perp_nondeg S W hnd x y hxW hyW hxx hxy hyy)
    have hmem : ∀ j, b' j ∈ W ∧ S.h x (b' j) = 0 ∧ S.h y (b' j) = 0 := fun j => by
      have h := hb'W j
      rw [Submodule.mem_inf, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, waR_apply,
        waR_apply] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
    have hbx : ∀ j, S.h (b' j) x = 0 := fun j => by rw [wa_symm, (hmem j).2.1, map_zero]
    have hby : ∀ j, S.h (b' j) y = 0 := fun j => by rw [wa_symm, (hmem j).2.2, map_zero]
    refine ⟨m' + 1, waExt x y b', waExt 0 0 g', fun i => ?_, by omega, fun i j => ?_,
      fun t ht hsum => ?_⟩
    · rcases wa_cases3 i with rfl | rfl | ⟨j, rfl⟩
      · simpa using hxW
      · simpa using hyW
      · simpa using (hmem j).1
    · rw [wa_witt_apply]
      rcases wa_cases3 i with rfl | rfl | ⟨i, rfl⟩ <;>
        rcases wa_cases3 j with rfl | rfl | ⟨j, rfl⟩ <;>
        simp only [waExt_zero, waExt_last, waExt_mid, Fin.val_zero, Fin.val_last, Fin.val_succ,
          Fin.val_castSucc] <;>
        try simp only [true_and]
      · rw [hxx, if_neg (by omega), if_neg (by omega)]
      · rw [hxy, if_pos (by omega)]
      · have := j.2
        rw [(hmem j).2.1, if_neg (by omega), if_neg (by omega)]
      · rw [hyx, if_pos (by omega)]
      · rw [hyy, if_neg (by omega), if_neg (by omega)]
      · have := j.2
        rw [(hmem j).2.2, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        rw [hbx, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        rw [hby, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        have := j.2
        rw [hgram', wa_witt_apply]
        split_ifs <;> first | rfl | (exfalso; omega)
    · have ht0 : t 0 = 0 := ht 0 (Or.inl (by simp))
      have htl : t (Fin.last (n' + 1)) = 0 := ht _ (Or.inr (by simp only [Fin.val_last]; omega))
      have ht' : (fun j : Fin n' => t (Fin.castSucc j).succ) = 0 := by
        refine hani' _ (fun j hj => ht _ ?_) ?_
        · simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        · rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hsum
          simpa [ht0, htl, Fin.succ_last] using hsum
      funext i
      rcases wa_cases3 i with rfl | rfl | ⟨j, rfl⟩
      · exact ht0
      · exact htl
      · exact congrFun ht' j
  · have han : ∀ x ∈ W, S.h x x = 0 → x = 0 := fun x hx hxx => by
      by_contra h0
      exact hiso ⟨x, hx, h0, hxx⟩
    obtain ⟨b, hbW, hb0, hbo⟩ := wa_diag S n W hW han
    have hg : ∀ k, S.h (b k) (b k) ≠ 0 := fun k h => hb0 k (han _ (hbW k) h)
    refine ⟨0, b, fun k => S.h (b k) (b k), hbW, by omega, fun i j => ?_, fun t _ hsum => ?_⟩
    · rw [wa_witt_apply]
      have := i.2
      by_cases hij : i = j
      · subst hij
        rw [if_neg (by omega), if_pos ⟨rfl, by omega, by omega⟩]
      · rw [hbo i j hij, if_neg (by omega), if_neg (fun h => hij (Fin.ext h.1))]
    · have hz : ∀ k, S.h (b k) (∑ i, t i • b i) = t k * S.h (b k) (b k) := fun k => by
        rw [wa_sum_right, Finset.sum_eq_single k
          (fun i _ hik => by rw [hbo k i (Ne.symm hik), mul_zero]) (by simp)]
      have hzz : S.h (∑ i, t i • b i) (∑ i, t i • b i) = 0 := by
        rw [wa_sum_left]
        simp only [hz]
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
        beta_reduce
        ring
      have hz0 := han _ (W.sum_mem fun i _ => W.smul_mem _ (hbW i)) hzz
      funext k
      have h := hz k
      rw [hz0, wa_zero_right] at h
      exact (mul_eq_zero.mp h.symm).resolve_right (hg k)

end ReciprocityTheory.MultiplicativeHeights
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Module

theorem wa_witt_ker {K : Type} [Field K] (r m : ℕ) (g : Fin r → K)
    (hg : ∀ k : Fin r, m ≤ (k : ℕ) → (k : ℕ) + m < r → g k ≠ 0) (v : Fin r → K)
    (hv : ∀ p : Fin r, ∑ i, v i * wittMat r m g p i = 0) : v = 0 := by
  funext j
  have hj := j.isLt
  by_cases hmid : m ≤ (j : ℕ) ∧ (j : ℕ) + m < r
  · have h := hv j
    rw [Finset.sum_eq_single j] at h
    · simp only [wittMat, Matrix.of_apply] at h
      rw [if_neg (by omega), if_pos ⟨trivial, hmid.1, hmid.2⟩] at h
      exact (mul_eq_zero.1 h).resolve_right (hg j hmid.1 hmid.2)
    · intro i _ hij
      have hi := i.isLt
      simp only [wittMat, Matrix.of_apply]
      rw [if_neg, if_neg, mul_zero]
      · rintro ⟨h1, -⟩
        exact hij h1.symm
      · rintro ⟨h1, h2⟩
        rcases h2 with h2 | h2 <;> omega
    · intro h
      exact absurd (Finset.mem_univ j) h
  · set p : Fin r := ⟨r - 1 - j, by omega⟩ with hp
    have hpv : (p : ℕ) = r - 1 - j := rfl
    have h := hv p
    rw [Finset.sum_eq_single j] at h
    · simp only [wittMat, Matrix.of_apply] at h
      have hc : (p : ℕ) + j + 1 = r ∧ ((p : ℕ) < m ∨ (j : ℕ) < m) := by
        rw [hpv]
        omega
      rw [if_pos hc, mul_one] at h
      exact h
    · intro i _ hij
      have hi := i.isLt
      simp only [wittMat, Matrix.of_apply]
      rw [if_neg, if_neg, mul_zero]
      · rintro ⟨-, h2, h3⟩
        rw [hpv] at h2 h3
        omega
      · rintro ⟨h1, -⟩
        apply hij
        ext
        rw [hpv] at h1
        omega
    · intro h
      exact absurd (Finset.mem_univ j) h

theorem wittBasis_holds : WittBasisStatement := by
  intro K _ _ r S hdet
  have hnd : ∀ x ∈ (⊤ : Submodule K (Fin r → K)),
      (∀ y ∈ (⊤ : Submodule K (Fin r → K)), S.h x y = 0) → x = 0 := by
    intro x _ hx
    have hrow : Matrix.vecMul (fun a => S.c (x a)) S.G = 0 := by
      funext b'
      have h1 := hx (Pi.single b' 1) Submodule.mem_top
      simpa [HermForm.h, Pi.single_apply, Matrix.vecMul, dotProduct] using h1
    have h2 : (fun a => S.c (x a)) = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hrow
    funext a
    have h3 := congrFun h2 a
    simp only [Pi.zero_apply, map_eq_zero] at h3
    exact h3
  obtain ⟨m, bb, g, -, hm, hW, hg⟩ := wa_main S r ⊤ (by rw [finrank_top, Module.finrank_fin_fun]) hnd
  have hgmid : ∀ k : Fin r, m ≤ (k : ℕ) → (k : ℕ) + m < r → g k ≠ 0 := by
    intro k hk1 hk2 hgk
    have ht := hg (Pi.single k 1) (fun i hi => by
      rw [Pi.single_apply, if_neg]
      rintro rfl
      omega) (by
      rw [Finset.sum_eq_single k]
      · simp [hgk]
      · intro i _ hik
        simp [Pi.single_eq_of_ne hik]
      · intro h
        exact absurd (Finset.mem_univ k) h)
    have := congrFun ht k
    simp at this
  have hlin : ∀ (x v : Fin r → K), S.h x (fun a => ∑ i, bb i a * v i) = ∑ i, v i * S.h x (bb i) := by
    intro x v
    simp only [HermForm.h, Finset.mul_sum]
    calc ∑ a, ∑ b', ∑ i, S.c (x a) * S.G a b' * (bb i b' * v i)
        = ∑ a, ∑ i, ∑ b', S.c (x a) * S.G a b' * (bb i b' * v i) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b', S.c (x a) * S.G a b' * (bb i b' * v i) := Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b', v i * (S.c (x a) * S.G a b' * bb i b') :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b' _ => by ring
  refine ⟨Matrix.of fun a i => bb i a, m, g, ?_, hm, ?_, hg⟩
  · intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    apply hv0
    have hPv : Matrix.mulVec (Matrix.of fun a i => bb i a) v = fun a => ∑ i, bb i a * v i := by
      funext a
      simp [Matrix.mulVec, dotProduct]
    refine wa_witt_ker r m g hgmid v fun p => ?_
    have h1 : S.h (bb p) (fun a => ∑ i, bb i a * v i) = 0 := by
      rw [← hPv, hv]
      simp [HermForm.h]
    rw [hlin] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun i _ => by rw [hW p i]
  · ext i j
    rw [← hW i j]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, HermForm.h,
      Finset.sum_mul]
    exact Finset.sum_comm

end ReciprocityTheory.MultiplicativeHeights
