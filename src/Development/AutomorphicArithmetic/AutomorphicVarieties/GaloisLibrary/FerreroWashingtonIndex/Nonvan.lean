module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ThetaFull

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinMap
open UpperTheory.V.FW

theorem UpperTheory.V.FW.sinMap :
    ∀ (k A B ι : Type) [CommRing k] [AddCommGroup A] [AddCommGroup B] [Fintype ι] [DecidableEq ι] (φ : A →+ B) (η : ι → A) (N : ℕ) (P : ℕ → k), AddMonoidAlgebra.mapDomainRingHom k φ (sinE η N P) = sinE (fun i => φ (η i)) N P := by
  intro k A B ι _ _ _ _ _ φ η N P
  unfold sinE
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_prod, map_sub, map_one, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain_single, map_nsmul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Sinnott
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinLem
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Nzd
open UpperTheory.V.FW

theorem UpperTheory.V.FW.nzd :
    ∀ (k A : Type) [CommRing k] [AddCommGroup A] (a : A) (x : AddMonoidAlgebra k A), (∀ m : ℕ, m • a = 0 → m = 0) → (1 - AddMonoidAlgebra.single a 1) * x = 0 → x = 0 := by
  intro k A _ _ a x ha h
  have hx : AddMonoidAlgebra.single a (1:k) * x = x := by
    rw [sub_mul, one_mul, sub_eq_zero] at h; exact h.symm
  have step : ∀ c, x.coeff (c + a) = x.coeff c := by
    intro c
    conv_lhs => rw [← hx]
    rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul, add_comm c a, neg_add_cancel_left]
  have key : ∀ b (n : ℕ), x.coeff (b + n • a) = x.coeff b := by
    intro b n
    induction n with
    | zero => simp
    | succ n ih => rw [succ_nsmul, ← add_assoc, step, ih]
  by_contra hne
  obtain ⟨b, hb⟩ : ∃ b, x.coeff b ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (AddMonoidAlgebra.ext (Finsupp.ext fun c => by simp [hc c]))
  have hinj : Function.Injective fun n : ℕ => b + n • a := by
    intro n m hnm
    simp only [add_right_inj] at hnm
    rcases le_total n m with hle | hle
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [add_nsmul, left_eq_add] at hnm
      simp [ha d hnm]
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [add_nsmul, add_eq_left] at hnm
      simp [ha d hnm]
  exact Set.infinite_of_injective_forall_mem hinj
    (fun n => show b + n • a ∈ (x.coeff.support : Set A) by simp [key, hb])
    x.coeff.support.finite_toSet
end

open UpperTheory.V.FW

private theorem cancel_prod {k A ι : Type} [CommRing k] [AddCommGroup A] [DecidableEq ι] (a : ι → A)
    (S : Finset ι) (h : ∀ j ∈ S, ∀ m : ℕ, m • a j = 0 → m = 0) (x : AddMonoidAlgebra k A)
    (hx : x * ∏ j ∈ S, (1 - AddMonoidAlgebra.single (a j) (1 : k)) = 0) : x = 0 := by
  induction S using Finset.induction_on with
  | empty => simpa using hx
  | insert j S hj ih =>
    apply ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    apply nzd k A (a j) _ (h j (Finset.mem_insert_self _ _))
    rw [Finset.prod_insert hj] at hx
    rw [← hx]; ring

theorem UpperTheory.V.FW.sinLem :
    ∀ (k A ι : Type) [CommRing k] [AddCommGroup A] [Fintype ι] [DecidableEq ι] [Nonempty ι] (η : ι → A) (N : ℕ) (P : ℕ → k), N ≠ 0 → (∀ i (m : ℤ), m • η i = 0 → m = 0) → (∀ i j, i ≠ j → ∀ a b : ℤ, a • η i = b • η j → a = 0) → sinE η N P = 0 → ∀ s < N, P s = 0 := by
  intro k A ι _ _ _ _ _ η N P hN htor hpair hE s hs
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  let H : AddSubgroup A := AddSubgroup.zmultiples (N • η i0)
  let φ : A →+ A ⧸ H := QuotientAddGroup.mk' H
  have hmap := sinMap k A (A ⧸ H) ι φ η N P
  rw [hE, map_zero] at hmap
  simp only [sinE] at hmap
  rw [Finset.sum_eq_single i0] at hmap
  · have hF : (∑ t ∈ Finset.range N, AddMonoidAlgebra.single (t • φ (η i0)) (P t) : AddMonoidAlgebra k (A ⧸ H)) = 0 := by
      apply cancel_prod (fun j => N • φ (η j)) (Finset.univ.erase i0) _ _ hmap.symm
      intro j hj m hm
      have hji : j ≠ i0 := Finset.ne_of_mem_erase hj
      rw [← map_nsmul φ, ← map_nsmul φ] at hm
      have hm' : m • N • η j ∈ H := (QuotientAddGroup.eq_zero_iff _).mp hm
      obtain ⟨b, hb⟩ := AddSubgroup.mem_zmultiples_iff.mp hm'
      have e1 : ((m * N : ℕ) : ℤ) • η j = m • N • η j := by
        rw [natCast_zsmul, mul_smul]
      have e2 : (b * (N : ℤ)) • η i0 = b • N • η i0 := by
        rw [mul_smul, natCast_zsmul]
      have hz := hpair j i0 hji ((m * N : ℕ) : ℤ) (b * N) (by rw [e1, e2, hb])
      have hmN : m * N = 0 := by exact_mod_cast hz
      rcases Nat.mul_eq_zero.mp hmN with h | h
      · exact h
      · exact absurd h hN
    have hcoef := congrArg (fun f : AddMonoidAlgebra k (A ⧸ H) => f.coeff (s • φ (η i0))) hF
    simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_zero,
      Finsupp.finsetSum_apply, Finsupp.coe_zero, Pi.zero_apply] at hcoef
    rw [Finset.sum_eq_single s] at hcoef
    · simpa using hcoef
    · intro t ht hts
      rw [Finsupp.single_apply, if_neg]
      intro he
      rw [← map_nsmul φ, ← map_nsmul φ] at he
      have hmem := (QuotientAddGroup.eq (s := H)).mp he
      obtain ⟨b, hb⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
      have h0 : (b * N - ((s : ℤ) - t)) • η i0 = 0 := by
        rw [sub_smul, mul_smul, natCast_zsmul, hb, sub_smul, natCast_zsmul, natCast_zsmul]
        abel
      have h1 := htor i0 _ h0
      have htN := Finset.mem_range.mp ht
      have hts' : (t : ℤ) = s := by
        rcases lt_trichotomy b 0 with hb0 | hb0 | hb0
        · nlinarith
        · subst hb0
          omega
        · nlinarith
      exact hts (by exact_mod_cast hts')
    · intro h
      exact absurd (Finset.mem_range.mpr hs) h
  · intro i _ hi
    have hmem : i0 ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨fun h => hi h.symm, Finset.mem_univ _⟩
    rw [Finset.prod_eq_zero hmem, mul_zero]
    have hz : N • φ (η i0) = 0 := by
      rw [← map_nsmul φ]
      exact (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_zmultiples _)
    rw [hz, sub_eq_zero]
    rfl
  · intro h
    exact absurd (Finset.mem_univ i0) h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinSupp
open UpperTheory.V.FW

private theorem prod_single_eq_single_sum {k A ι : Type} [CommRing k] [AddCommGroup A] [DecidableEq ι]
    (T : Finset ι) (f : ι → A) (c : k) :
    ∏ j ∈ T, (AddMonoidAlgebra.single (f j) c : AddMonoidAlgebra k A)
      = AddMonoidAlgebra.single (∑ j ∈ T, f j) (∏ _j ∈ T, c) := by
  induction T using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert i T hi ih =>
    rw [Finset.prod_insert hi, ih, AddMonoidAlgebra.single_mul_single, Finset.sum_insert hi,
      Finset.prod_insert hi]

private theorem coeff_monic_poly_sum {k A ι : Type} [CommRing k] [AddCommGroup A]
    (T : Finset ι) (f : ι → AddMonoidAlgebra k A) (a : A) (h : (∑ j ∈ T, f j).coeff a ≠ 0) :
    ∃ j ∈ T, (f j).coeff a ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero hc

theorem UpperTheory.V.FW.sinSupp :
    ∀ (A ι : Type) [AddCommGroup A] [Fintype ι] [DecidableEq ι] (η : ι → A) (N : ℕ), ∃ S : Finset A, ∀ (k : Type) [CommRing k] (P : ℕ → k) (a : A), (sinE η N P).coeff a ≠ 0 → a ∈ S := by
  intro A ι _ _ _ η N
  classical
  refine ⟨(Finset.univ ×ˢ (Finset.range N ×ˢ (Finset.univ : Finset ι).powerset)).image
    (fun p : ι × ℕ × Finset ι => p.2.1 • η p.1 + ∑ j ∈ p.2.2, N • η j), ?_⟩
  intro k _ P a ha
  simp only [sinE] at ha
  obtain ⟨i, -, hi⟩ := coeff_monic_poly_sum _ _ a ha
  have hprod : ∏ j ∈ Finset.univ.erase i, (1 - AddMonoidAlgebra.single (N • η j) (1 : k))
      = ∑ t ∈ (Finset.univ.erase i).powerset,
          AddMonoidAlgebra.single (∑ j ∈ t, N • η j) (∏ _j ∈ t, (-1 : k)) := by
    have e : ∀ j, (1 - AddMonoidAlgebra.single (N • η j) (1 : k))
        = AddMonoidAlgebra.single (N • η j) (-1 : k) + 1 := by
      intro j
      rw [AddMonoidAlgebra.single_neg]
      abel
    simp_rw [e]
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.prod_const_one, mul_one, prod_single_eq_single_sum]
  rw [hprod, Finset.sum_mul] at hi
  obtain ⟨s, hs, hs2⟩ := coeff_monic_poly_sum _ _ a hi
  rw [Finset.mul_sum] at hs2
  obtain ⟨t, ht, ht2⟩ := coeff_monic_poly_sum _ _ a hs2
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single_apply] at ht2
  split_ifs at ht2 with hEq
  · rw [Finset.mem_image]
    refine ⟨(i, s, t), ?_, hEq⟩
    simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_powerset, true_and]
    exact ⟨hs, Finset.subset_univ _⟩
  · exact absurd rfl ht2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinFin
open UpperTheory.V.FW

theorem UpperTheory.V.FW.sinFin :
    ∀ (k ι : Type) [CommRing k] [Fintype ι] [DecidableEq ι] (m : ℕ) [NeZero m] (η : ι → (ZMod m)ˣ) (N : ℕ) (P : ℕ → k) (α : ZMod m → k), (∀ y, α y - α (y - N) = ∑ s ∈ Finset.range N, if (s : ZMod m) = y then P s else 0) → (∀ y, ∑ i, α (((η i)⁻¹ : (ZMod m)ˣ) * y) = 0) → sinE (fun i => (η i : ZMod m)) N P = 0 := by
  intro k ι _ _ _ m _ η N P α hα hsum
  have hsingSum : ∀ (z : ZMod m) (t : Finset ℕ) (g : ℕ → k),
      AddMonoidAlgebra.single z (∑ s ∈ t, g s) = ∑ s ∈ t, AddMonoidAlgebra.single z (g s) :=
    fun z t g => map_sum (AddMonoidAlgebra.singleAddHom z) g t
  have hsingSumι : ∀ (z : ZMod m) (g : ι → k),
      AddMonoidAlgebra.single z (∑ i, g i) = ∑ i, AddMonoidAlgebra.single z (g i) :=
    fun z g => map_sum (AddMonoidAlgebra.singleAddHom z) g Finset.univ
  have hsingSub : ∀ (z : ZMod m) (a b : k),
      AddMonoidAlgebra.single z (a - b) = AddMonoidAlgebra.single z a - AddMonoidAlgebra.single z b :=
    fun z a b => map_sub (AddMonoidAlgebra.singleAddHom z) a b
  set A : ι → AddMonoidAlgebra k (ZMod m) :=
    fun i => ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * y) (α y) with hA
  have hS : ∀ i, (∑ s ∈ Finset.range N, AddMonoidAlgebra.single (s • (η i : ZMod m)) (P s)) =
      (1 - AddMonoidAlgebra.single (N • (η i : ZMod m)) 1) * A i := by
    intro i
    have hone : ∀ s : ℕ, ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * y)
        (if (s : ZMod m) = y then P s else 0) = AddMonoidAlgebra.single (s • (η i : ZMod m)) (P s) := by
      intro s
      rw [Finset.sum_eq_single (s : ZMod m)]
      · simp [nsmul_eq_mul, mul_comm]
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    have e1 : ∑ s ∈ Finset.range N, AddMonoidAlgebra.single (s • (η i : ZMod m)) (P s) =
        ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * y) (α y - α (y - N)) := by
      simp_rw [hα, hsingSum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => (hone s).symm
    have e2 : ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * y) (α (y - N)) =
        ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * (y + N)) (α y) := by
      rw [← Equiv.sum_comp (Equiv.addRight (N : ZMod m))]
      simp
    have e3 : AddMonoidAlgebra.single (N • (η i : ZMod m)) (1 : k) * A i =
        ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * (y + N)) (α y) := by
      rw [hA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [AddMonoidAlgebra.single_mul_single, one_mul, nsmul_eq_mul]
      congr 1
      ring
    rw [e1, sub_mul, one_mul, e3, ← e2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => hsingSub _ _ _
  have hA0 : ∑ i, A i = 0 := by
    have hre : ∀ i, A i = ∑ z : ZMod m,
        AddMonoidAlgebra.single z (α (((η i)⁻¹ : (ZMod m)ˣ) * z)) := by
      intro i
      rw [hA, ← Equiv.sum_comp (Units.mulLeft (η i))]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp
    simp_rw [hre]
    rw [Finset.sum_comm]
    simp_rw [← hsingSumι, hsum]
    simp
  unfold sinE
  dsimp only
  rw [Finset.sum_congr rfl (fun i _ => by
    rw [hS i, mul_assoc, mul_left_comm, Finset.mul_prod_erase Finset.univ
      (fun j => 1 - AddMonoidAlgebra.single (N • (η j : ZMod m)) (1 : k)) (Finset.mem_univ i)])]
  rw [← Finset.sum_mul, hA0, zero_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SepPair
open UpperTheory.V.FW

private theorem sep_pair (l : ℕ) [Fact l.Prime] (x y : ℤ_[l]) :
    ∀ᶠ n in Filter.atTop, PadicInt.toZModPow n x = PadicInt.toZModPow n y → x = y := by
  by_cases h : x = y
  · exact Filter.Eventually.of_forall fun _ _ => h
  · obtain ⟨m, hm⟩ : ∃ m, PadicInt.toZModPow m x ≠ PadicInt.toZModPow m y := by
      by_contra hc
      push_neg at hc
      exact h (PadicInt.ext_of_toZModPow.mp hc)
    filter_upwards [Filter.eventually_ge_atTop m] with n hn heq
    exfalso
    apply hm
    rw [← PadicInt.cast_toZModPow m n hn x, ← PadicInt.cast_toZModPow m n hn y, heq]

theorem UpperTheory.V.FW.sep :
    ∀ (l : ℕ) [Fact l.Prime] (S : Finset ℤ_[l]), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Set.InjOn (PadicInt.toZModPow n : ℤ_[l] → ZMod (l ^ n)) S := by
  intro l _ S
  have h : ∀ᶠ n in Filter.atTop, ∀ p ∈ S ×ˢ S,
      PadicInt.toZModPow n p.1 = PadicInt.toZModPow n p.2 → p.1 = p.2 :=
    (Filter.eventually_all_finset _).mpr fun p _ => sep_pair l p.1 p.2
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp h
  exact ⟨n₀, fun n hn x hx y hy hxy => hn₀ n hn (x, y) (Finset.mk_mem_product hx hy) hxy⟩
end

open UpperTheory.V.FW

theorem UpperTheory.V.FW.sinnott :
    ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [Nonempty ι] (η : ι → ℤ_[l]ˣ) (N : ℕ), N ≠ 0 → (∀ i j, i ≠ j → ∀ a b : ℤ, (a : ℤ_[l]) * η i = (b : ℤ_[l]) * η j → a = 0) → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (k : Type) [CommRing k] (P : ℕ → k) (α : ZMod (l ^ n) → k), (∀ y, α y - α (y - N) = ∑ s ∈ Finset.range N, if (s : ZMod (l ^ n)) = y then P s else 0) → (∀ y, ∑ i, α (((redU l n (η i))⁻¹ : (ZMod (l ^ n))ˣ) * y) = 0) → ∀ s < N, P s = 0 := by
  intro l _ ι _ _ η N hN hind
  classical
  obtain ⟨S, hS⟩ := sinSupp ℤ_[l] ι (fun i => (η i : ℤ_[l])) N
  obtain ⟨n₀, hn₀⟩ := sep l S
  refine ⟨n₀, fun n hn k _ P α h1 h2 => ?_⟩
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have h3 := sinFin k ι (l ^ n) (fun i => redU l n (η i)) N P α h1 h2
  have h4 := sinMap k ℤ_[l] (ZMod (l ^ n)) ι
    (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)).toAddMonoidHom (fun i => (η i : ℤ_[l])) N P
  have h5 : AddMonoidAlgebra.mapDomainRingHom k
      (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)).toAddMonoidHom
      (sinE (fun i => (η i : ℤ_[l])) N P) = 0 := h4.trans h3
  have h6 : Finsupp.mapDomain (PadicInt.toZModPow n : ℤ_[l] → ZMod (l ^ n))
      (sinE (fun i => (η i : ℤ_[l])) N P).coeff = 0 := by
    have := congrArg AddMonoidAlgebra.coeff h5
    simpa using this
  have h7 : (sinE (fun i => (η i : ℤ_[l])) N P).coeff = 0 := by
    apply Finsupp.mapDomain_injOn (S : Set ℤ_[l]) (hn₀ n hn)
    · intro a ha
      exact hS k P a (Finsupp.mem_support_iff.mp ha)
    · simp
    · simpa using h6
  refine sinLem k ℤ_[l] ι (fun i => (η i : ℤ_[l])) N P hN ?_ ?_ ?_
  · intro i m hm
    simp only [zsmul_eq_mul] at hm
    have := (Units.mul_left_eq_zero (η i)).mp hm
    exact_mod_cast this
  · intro i j hij a b hab
    simp only [zsmul_eq_mul] at hab
    exact hind i j hij a b hab
  · ext a
    simp [h7]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwCoef
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.HalfSum
open UpperTheory.V.FW

theorem UpperTheory.V.FW.halfSum :
    ∀ (α k : Type) [AddCommMonoid k] (σ : α → α) (H H' : Finset α) (g : α → k), (∀ x, σ (σ x) = x) → (∀ x, g (σ x) = g x) → (∀ x ∈ H, σ x ∉ H) → (∀ x ∈ H', σ x ∉ H') → (∀ x ∈ H, x ∈ H' ∨ σ x ∈ H') → (∀ x ∈ H', x ∈ H ∨ σ x ∈ H) → ∑ x ∈ H, g x = ∑ x ∈ H', g x := by
  classical
  intro α k _ σ H H' g hσ hg hH hH' hHH' hH'H
  refine Finset.sum_bij' (fun x _ => if x ∈ H' then x else σ x) (fun y _ => if y ∈ H then y else σ y)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    by_cases h : x ∈ H'
    · simp [h]
    · simp only [h, if_false]
      exact (hHH' x hx).resolve_left h
  · intro y hy
    by_cases h : y ∈ H
    · simp [h]
    · simp only [h, if_false]
      exact (hH'H y hy).resolve_left h
  · intro x hx
    by_cases h : x ∈ H'
    · simp [h, hx]
    · simp [h, hH x hx, hσ]
  · intro y hy
    by_cases h : y ∈ H
    · simp [h, hy]
    · simp [h, hH' y hy, hσ]
  · intro x hx
    by_cases h : x ∈ H'
    · simp [h]
    · simp [h, hg]
end

open UpperTheory.V.FW

private theorem push_units {k : Type} [CommRing k] {M : ℕ} [NeZero M] {m : ℕ} (h : m ∣ M)
    (χ : (ZMod M)ˣ →* kˣ) (g : ZMod M → k) (z : ZMod m) :
    push h (fun s => g s * MulChar.ofUnitHom χ s) z =
      ∑ s : (ZMod M)ˣ with ((ZMod.unitsMap h s : (ZMod m)ˣ) : ZMod m) = z, g s * (χ s : k) := by
  classical
  unfold push
  symm
  refine Finset.sum_bij_ne_zero (fun (u : (ZMod M)ˣ) _ _ => (u : ZMod M)) ?_ ?_ ?_ ?_
  · intro u hu _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [← hu]
    rfl
  · intro u₁ _ _ u₂ _ _ h12
    exact Units.ext h12
  · intro s hs hne
    have hu : IsUnit s := by
      by_contra hn
      apply hne
      show g s * (MulChar.ofUnitHom χ) s = 0
      rw [MulChar.map_nonunit _ hn, mul_zero]
    refine ⟨hu.unit, ?_, ?_, hu.unit_spec⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [← hs]
      show (ZMod.castHom h (ZMod m)) (hu.unit : ZMod M) = _
      rw [hu.unit_spec]
    · have hne' : g s * (MulChar.ofUnitHom χ) s ≠ 0 := hne
      rwa [← hu.unit_spec, MulChar.ofUnitHom_coe] at hne'
  · intro u _ _
    show g u * (χ u : k) = g u * (MulChar.ofUnitHom χ) u
    rw [MulChar.ofUnitHom_coe]

private theorem half_val {M : ℕ} [NeZero M] (hM : 2 < M) (s : (ZMod M)ˣ) :
    2 * ((-s : (ZMod M)ˣ) : ZMod M).val < M ↔ ¬ 2 * (s : ZMod M).val < M := by
  haveI : Fact (1 < M) := ⟨by omega⟩
  have hs0 : (s : ZMod M) ≠ 0 := s.ne_zero
  have hv : (s : ZMod M).val < M := ZMod.val_lt _
  have hne : 2 * (s : ZMod M).val ≠ M := by
    intro h2
    have h3 : ((2 * (s : ZMod M).val : ℕ) : ZMod M) = 0 := by
      rw [h2]
      exact ZMod.natCast_self M
    push_cast at h3
    rw [ZMod.natCast_zmod_val] at h3
    have h4 : (2 : ZMod M) = 0 := by
      have := congrArg (· * ((s⁻¹ : (ZMod M)ˣ) : ZMod M)) h3
      simpa [mul_assoc] using this
    have h5 : ((2 : ℕ) : ZMod M) = 0 := by exact_mod_cast h4
    rw [ZMod.natCast_eq_zero_iff] at h5
    have := Nat.le_of_dvd (by norm_num) h5
    omega
  rw [Units.val_neg, ZMod.neg_val, if_neg hs0]
  omega

theorem UpperTheory.V.FW.twCoef :
    ∀ (l : ℕ) [Fact l.Prime] (M n₀ : ℕ) [NeZero M] (h : l ^ n₀ ∣ M) (k : Type) [CommRing k] (χ : (ZMod M)ˣ →* kˣ) (g : ZMod M → ℤ) (R : Finset ℤ_[l]ˣ), 2 ≤ n₀ → χ (-1) = -1 → (∀ s : (ZMod M)ˣ, g (-(s : ZMod M)) = -g s) → (∀ r ∈ R, r ∈ WW l) → (∀ r ∈ R, -r ∉ R) → (∀ w ∈ WW l, w ∈ R ∨ -w ∈ R) → tw χ (piQ l n₀ h) (toK k _ (∑ s ∈ Finset.univ.filter fun s : (ZMod M)ˣ => 2 * (s : ZMod M).val < M, MonoidAlgebra.single s (g s))) = 0 → ∀ y : ZMod (l ^ n₀), ∑ r : R, push h (fun s => (g s : k) * MulChar.ofUnitHom χ s) (((redU l n₀ r.1)⁻¹ : (ZMod (l ^ n₀))ˣ) * y) = 0 := by
  intro l _ M n₀ _ h k _ χ g R hn₀ hχ hg hRW hRneg hWR htw y
  classical
  have hl : l.Prime := Fact.out
  have hM : 2 < M := by
    have h4 : 4 ≤ l ^ n₀ :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ l ^ 2 := Nat.pow_le_pow_left hl.two_le 2
        _ ≤ l ^ n₀ := Nat.pow_le_pow_right hl.pos hn₀
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h
    omega
  have hneg1 : (-1 : ℤ_[l]ˣ) ∈ WW l := by
    show (-1 : ℤ_[l]ˣ) ∈ rootsOfUnity (l ^ ee l).totient ℤ_[l]
    rw [mem_rootsOfUnity]
    apply Even.neg_one_pow
    apply Nat.totient_even
    have h2 := hl.two_le
    unfold ee
    split_ifs with h2'
    · subst h2'
      norm_num
    · rw [pow_one]
      omega
  have hnegmem : ∀ v ∈ WW l, -v ∈ WW l := fun v hv => by
    rw [← neg_one_mul v]
    exact mul_mem hneg1 hv
  obtain ⟨-, -, -, -, -, -, -, hinj⟩ := reps l
  have hredneg : ∀ v : ℤ_[l]ˣ, redU l n₀ (-v) = -redU l n₀ v := fun v => by
    ext
    simp [redU]
  have hρneg : ∀ x : (ZMod M)ˣ, ZMod.unitsMap h (-x) = -ZMod.unitsMap h x := fun x => by
    ext
    simp [ZMod.unitsMap_def]
  have hredinj : ∀ v ∈ WW l, ∀ w ∈ WW l, redU l n₀ v = redU l n₀ w → v = w := by
    intro v hv w hw hvw
    have h1 : redU l n₀ (v * w⁻¹) = 1 := by rw [map_mul, map_inv, hvw, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hinj n₀ hn₀ _ (mul_mem hv (inv_mem hw)) h1)
  have hcoef : ∀ q, ∑ s ∈ (Finset.univ.filter fun s : (ZMod M)ˣ => 2 * (s : ZMod M).val < M).filter
      (fun s => piQ l n₀ h s = q), (g s : k) * (χ s : k) = 0 := by
    intro q
    have h1 := congrArg (fun x => MonoidAlgebra.coeff x q) htw
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, toK, MonoidAlgebra.mapRingHom_single, eq_intCast, tw_single,
      MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.single_apply,
      MonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
    rw [Finset.sum_filter]
    exact h1
  have hpu : ∀ z, push h (fun s => (g s : k) * MulChar.ofUnitHom χ s) z =
      ∑ s : (ZMod M)ˣ with ((ZMod.unitsMap h s : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) = z,
        (g s : k) * (χ s : k) := fun z => push_units h χ (fun s => (g s : k)) z
  simp only [hpu]
  by_cases hy : IsUnit y
  swap
  · apply Finset.sum_eq_zero
    intro r _
    apply Finset.sum_eq_zero
    intro s hs
    exfalso
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    apply hy
    have : y = ((redU l n₀ r.1 : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) *
        ((ZMod.unitsMap h s : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) := by
      rw [hs, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [this]
    exact (Units.isUnit _).mul (Units.isUnit _)
  obtain ⟨u, rfl⟩ := hy
  let t : R → Finset (ZMod M)ˣ := fun r =>
    Finset.univ.filter fun s => ZMod.unitsMap h s = (redU l n₀ r.1)⁻¹ * u
  have hgoal : ∀ r : R, ∑ s ∈ Finset.univ.filter (fun s : (ZMod M)ˣ =>
      ((ZMod.unitsMap h s : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) =
        (((redU l n₀ r.1)⁻¹ : (ZMod (l ^ n₀))ˣ) : ZMod (l ^ n₀)) * (u : ZMod (l ^ n₀))),
      (g s : k) * (χ s : k) = ∑ s ∈ t r, (g s : k) * (χ s : k) := fun r =>
    Finset.sum_congr (Finset.filter_congr (fun s _ => by rw [Units.ext_iff, Units.val_mul]))
      (fun _ _ => rfl)
  refine Eq.trans (Finset.sum_congr rfl (fun r _ => hgoal r)) ?_
  have hdisj : (↑(Finset.univ : Finset R) : Set R).PairwiseDisjoint t := by
    intro r₁ _ r₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hs1 hs2
    apply hne
    apply Subtype.ext
    apply hredinj _ (hRW _ r₁.2) _ (hRW _ r₂.2)
    have h12 := hs1.symm.trans hs2
    rw [mul_left_inj, inv_inj] at h12
    exact h12
  refine Eq.trans (Finset.sum_biUnion hdisj).symm ?_
  have hπ : ∀ v ∈ WW l, ∀ x : (ZMod M)ˣ, ZMod.unitsMap h x = (redU l n₀ v)⁻¹ * u →
      piQ l n₀ h x = QuotientGroup.mk' (Subgroup.map (redU l n₀) (WW l)) u := by
    intro v hv x hx
    have h1 : QuotientGroup.mk' (Subgroup.map (redU l n₀) (WW l)) (redU l n₀ v)⁻¹ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact inv_mem (Subgroup.mem_map_of_mem _ hv)
    show QuotientGroup.mk' _ (ZMod.unitsMap h x) = _
    rw [hx, map_mul, h1, one_mul]
  refine Eq.trans (halfSum (ZMod M)ˣ k Neg.neg _ _ (fun s => (g s : k) * (χ s : k))
    ?_ ?_ ?_ ?_ ?_ ?_) (hcoef (QuotientGroup.mk' (Subgroup.map (redU l n₀) (WW l)) u))
  · exact fun x => neg_neg x
  · intro x
    have hχx : (χ (-x) : k) = -(χ x : k) := by
      rw [← neg_one_mul x, map_mul, hχ, Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul]
    show ((g ((-x : (ZMod M)ˣ) : ZMod M)) : k) * (χ (-x) : k) = (g x : k) * (χ x : k)
    rw [hχx, Units.val_neg, hg x]
    push_cast
    ring
  · intro x hx hnx
    simp only [t, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and] at hx hnx
    obtain ⟨r, hr⟩ := hx
    obtain ⟨r', hr'⟩ := hnx
    rw [hρneg, hr, ← neg_mul] at hr'
    have h2 := mul_right_cancel hr'
    have h3 : redU l n₀ r'.1 = redU l n₀ (-r.1) := by
      rw [hredneg, ← inv_inj, ← h2, inv_neg]
    have h4 := hredinj _ (hRW _ r'.2) _ (hnegmem _ (hRW _ r.2)) h3
    exact hRneg _ r.2 (h4 ▸ r'.2)
  · intro x hx hnx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hnx
    exact ((half_val hM x).mp hnx.1) hx.1
  · intro x hx
    simp only [t, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and] at hx
    obtain ⟨r, hr⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hh : 2 * (x : ZMod M).val < M
    · exact Or.inl ⟨hh, hπ r.1 (hRW _ r.2) x hr⟩
    · refine Or.inr ⟨(half_val hM x).mpr hh, hπ (-r.1) (hnegmem _ (hRW _ r.2)) (-x) ?_⟩
      rw [hρneg, hr, hredneg, inv_neg, neg_mul]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨-, hq⟩ := hx
    have hq' : QuotientGroup.mk' (Subgroup.map (redU l n₀) (WW l)) (ZMod.unitsMap h x) =
        QuotientGroup.mk' _ u := hq
    rw [QuotientGroup.mk'_eq_mk'] at hq'
    obtain ⟨z, hz, hxz⟩ := hq'
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    have hx' : ZMod.unitsMap h x = (redU l n₀ w)⁻¹ * u :=
      eq_inv_mul_of_mul_eq ((mul_comm _ _).trans hxz)
    rcases hWR w hw with hR | hR
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨⟨w, hR⟩, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩⟩)
    · refine Or.inr (Finset.mem_biUnion.mpr ⟨⟨-w, hR⟩, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩)
      show ZMod.unitsMap h (-x) = (redU l n₀ (-w))⁻¹ * u
      rw [hρneg, hx', hredneg, inv_neg, neg_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GcShift
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GcDiff
open UpperTheory.V.FW

private theorem norm_index_count_bound (M a c : ℕ) :
    (((a + c) / M : ℕ) : ℤ) = ((a / M : ℕ) : ℤ) +
      ∑ j ∈ Finset.range c, if (j : ZMod M) = ((a + c : ℕ) : ZMod M) then 1 else 0 := by
  induction c with
  | zero => simp
  | succ c ih =>
    have e : a + (c + 1) = (a + c) + 1 := by omega
    have h1 : ∀ j : ℕ, (((j + 1 : ℕ) : ZMod M) = (((a + c + 1 : ℕ)) : ZMod M)) ↔
        ((j : ZMod M) = ((a + c : ℕ) : ZMod M)) := by
      intro j
      push_cast
      exact add_left_inj 1
    have h2 : ((0 : ℕ) : ZMod M) = ((a + c + 1 : ℕ) : ZMod M) ↔ M ∣ a + c + 1 := by
      rw [Nat.cast_zero, eq_comm]
      exact CharP.cast_eq_zero_iff (ZMod M) M _
    rw [e, Nat.succ_div, Finset.sum_range_succ']
    simp only [h1, h2]
    rw [Nat.cast_add, ih]
    split_ifs <;> push_cast <;> ring

theorem UpperTheory.V.FW.gcDiff :
    ∀ (M c : ℕ) [NeZero M] (s : ZMod M), c.Coprime M → gc M c s - gc M c (s - c) = (∑ j ∈ Finset.range c, if (j : ZMod M) = s then 1 else 0) - if s = 0 then (c : ℤ) else 0 := by
  intro M c _ s hc
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hinv : (c : ZMod M)⁻¹ * (c : ZMod M) = 1 := by
    rw [mul_comm]
    exact ZMod.coe_mul_inv_eq_one c hc
  have hts : (c : ZMod M)⁻¹ * (s - c) = (c : ZMod M)⁻¹ * s - 1 := by
    rw [mul_sub, hinv]
  unfold UpperTheory.V.FW.gc
  rw [hts]
  set t : ZMod M := (c : ZMod M)⁻¹ * s with ht
  have hs : s = (c : ZMod M) * t := by
    rw [ht, ← mul_assoc, ZMod.coe_mul_inv_eq_one c hc, one_mul]
  set w := (t - 1).val with hw
  have htw : t = ((w + 1 : ℕ) : ZMod M) := by
    rw [Nat.cast_add, Nat.cast_one, hw, ZMod.natCast_zmod_val]
    ring
  have key := norm_index_count_bound M (c * w) c
  have hcast : ((c * w + c : ℕ) : ZMod M) = s := by
    rw [hs, htw]
    push_cast
    ring
  rw [hcast] at key
  rcases Nat.lt_or_ge (w + 1) M with h | h
  · have hvt : t.val = w + 1 := by
      rw [htw, ZMod.val_natCast, Nat.mod_eq_of_lt h]
    have hs0 : s ≠ 0 := by
      intro h0
      have t0 : t = 0 := by rw [ht, h0, mul_zero]
      rw [t0, ZMod.val_zero] at hvt
      omega
    rw [hvt, if_neg hs0, sub_zero]
    have e : c * (w + 1) = c * w + c := by ring
    rw [e, key]
    ring
  · have hwe : w + 1 = M := by
      have := ZMod.val_lt (t - 1)
      omega
    have ht0 : t = 0 := by rw [htw, hwe, ZMod.natCast_self]
    have hs0 : s = 0 := by rw [hs, ht0, mul_zero]
    rw [ht0, ZMod.val_zero, if_pos hs0]
    have e : c * w + c = c * M := by rw [← hwe]; ring
    rw [e, Nat.mul_div_cancel _ hM] at key
    simp only [mul_zero, Nat.zero_div, Nat.cast_zero]
    linarith
end

open UpperTheory.V.FW

private theorem gauss_count_shift_eq_sum (M c : ℕ) [NeZero M] (s : ZMod M) (hc : c.Coprime M) (n : ℕ) :
    gc M c s - gc M c (s - ((c * n : ℕ) : ZMod M)) =
      ∑ j ∈ Finset.range (c * n), if (j : ZMod M) = s then (1 - if c ∣ j then (c : ℤ) else 0) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := gcDiff M c (s - ((c * n : ℕ) : ZMod M)) hc
    have e : s - ((c * (n + 1) : ℕ) : ZMod M) = s - ((c * n : ℕ) : ZMod M) - c := by
      push_cast; ring
    rw [e, Nat.mul_succ, Finset.sum_range_add, ← ih]
    have key : (∑ j ∈ Finset.range c, if ((c * n + j : ℕ) : ZMod M) = s then
        (1 - if c ∣ c * n + j then (c : ℤ) else 0) else 0) =
        (∑ j ∈ Finset.range c, if (j : ZMod M) = s - ((c * n : ℕ) : ZMod M) then 1 else 0) -
          if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0 := by
      rcases Nat.eq_zero_or_pos c with rfl | hpos
      · simp
      have h2 : (if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0) =
          ∑ j ∈ Finset.range c, if j = 0 then
            (if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0) else 0 := by
        rw [Finset.sum_ite_eq' (Finset.range c) 0]
        simp [hpos]
      rw [h2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.1 hj
      have h3 : (((c * n + j : ℕ) : ZMod M) = s) ↔ (j : ZMod M) = s - ((c * n : ℕ) : ZMod M) := by
        rw [Nat.cast_add, eq_sub_iff_add_eq']
      have h4 : c ∣ c * n + j ↔ j = 0 := by
        rw [Nat.dvd_add_right (dvd_mul_right c n)]
        exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hj', fun h => h ▸ dvd_zero c⟩
      simp only [h3, h4]
      generalize s - ((c * n : ℕ) : ZMod M) = t
      by_cases h0 : j = 0
      · subst h0
        by_cases ht : t = 0
        · simp [ht]
        · simp [ht, Ne.symm ht]
      · simp [h0]
    rw [key, ← h]
    ring

theorem UpperTheory.V.FW.gcShift :
    ∀ (M c F : ℕ) [NeZero M] (k : Type) [CommRing k] (Ψ : ZMod M → k) (s : ZMod M), c.Coprime M → (∀ x, Ψ (x + F) = Ψ x) → (gc M c s : k) * Ψ s - (gc M c (s - ((c * F : ℕ) : ZMod M)) : k) * Ψ (s - ((c * F : ℕ) : ZMod M)) = ∑ j ∈ Finset.range (c * F), if (j : ZMod M) = s then Ψ j * (1 - if c ∣ j then (c : k) else 0) else 0 := by
  intro M c F _ k _ Ψ s hc hΨ
  have hp : ∀ n : ℕ, Ψ (s - ((n * F : ℕ) : ZMod M)) = Ψ s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih, ← hΨ (s - (((n + 1) * F : ℕ) : ZMod M))]
      congr 1
      push_cast; ring
  rw [hp c, ← sub_mul, ← Int.cast_sub, gauss_count_shift_eq_sum M c s hc F, Int.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (j : ZMod M) = s
  · rw [if_pos h, if_pos h, h, mul_comm]
    by_cases h' : c ∣ j <;> simp [h']
  · simp [h]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CharPer
open UpperTheory.V.FW

theorem UpperTheory.V.FW.charPer :
    ∀ (l : ℕ) [Fact l.Prime] (f n : ℕ) [NeZero (f * l ^ n)] (k : Type) [Field k] [CharP k l] (χ : (ZMod (f * l ^ n))ˣ →* kˣ) (s : ZMod (f * l ^ n)), f.Coprime l → 1 ≤ n → MulChar.ofUnitHom χ (s + ((f * l : ℕ) : ZMod (f * l ^ n))) = MulChar.ofUnitHom χ s := by
  intro l hl f n _ k _ _ χ s hf hn
  set M : ZMod (f * l ^ n) := ((f * l : ℕ) : ZMod (f * l ^ n)) with hM
  have hnil : IsNilpotent M := by
    refine ⟨n, ?_⟩
    rw [hM, ← Nat.cast_pow, CharP.cast_eq_zero_iff (ZMod (f * l ^ n)) (f * l ^ n), mul_pow]
    exact Nat.mul_dvd_mul_right (dvd_pow_self f (by omega)) _
  by_cases hs : IsUnit s
  swap
  · have hs' : ¬ IsUnit (s + M) := by
      intro h
      apply hs
      simpa using hnil.neg.isUnit_add_right_of_commute h (Commute.all _ _)
    rw [MulChar.map_nonunit _ hs, MulChar.map_nonunit _ hs']
  obtain ⟨u, rfl⟩ := hs
  set t : ℤ := ((((u⁻¹ : (ZMod (f * l ^ n))ˣ) : ZMod (f * l ^ n)).val : ℕ) : ℤ) with ht
  set w : ZMod (f * l ^ n) := 1 + M * ((u⁻¹ : (ZMod (f * l ^ n))ˣ) : ZMod (f * l ^ n)) with hw
  have hsplit : (u : ZMod (f * l ^ n)) + M = u * w := by
    rw [hw, mul_add, mul_one, mul_left_comm, Units.mul_inv, mul_one]
  have hwint : w = ((1 + (f : ℤ) * l * t : ℤ) : ZMod (f * l ^ n)) := by
    rw [hw, hM, ht]
    push_cast
    rw [ZMod.natCast_zmod_val]
  have hdvd : ((f * l ^ n : ℕ) : ℤ) ∣ (1 + (f : ℤ) * l * t) ^ (l ^ (n - 1)) - 1 := by
    have h1 : ((l : ℕ) : ℤ) ^ (n - 1 + 1) ∣ (1 + (f : ℤ) * l * t) ^ (l ^ (n - 1)) - 1 ^ (l ^ (n - 1)) :=
      dvd_sub_pow_of_dvd_sub (by simp only [add_sub_cancel_left]; exact ⟨f * t, by ring⟩) _
    rw [Nat.sub_add_cancel hn, one_pow] at h1
    have h2 : (f : ℤ) ∣ (1 + (f : ℤ) * l * t) ^ (l ^ (n - 1)) - 1 := by
      have := sub_dvd_pow_sub_pow (1 + (f : ℤ) * l * t) 1 (l ^ (n - 1))
      rw [one_pow] at this
      exact dvd_trans ⟨l * t, by ring⟩ this
    have hcop : IsCoprime (f : ℤ) ((l : ℤ) ^ n) := by
      have := Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right n hf)
      simpa using this
    push_cast
    exact hcop.mul_dvd h2 h1
  have hwpow : w ^ (l ^ (n - 1)) = 1 := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd
    rw [hwint]
    push_cast at h0 ⊢
    linear_combination h0
  have hcw : MulChar.ofUnitHom χ w = 1 := by
    have hp : (MulChar.ofUnitHom χ w) ^ (l ^ (n - 1)) = 1 := by
      rw [← map_pow, hwpow, map_one]
    have : (MulChar.ofUnitHom χ w - 1) ^ (l ^ (n - 1)) = 0 := by
      rw [sub_pow_char_pow, hp, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ hl.out.ne_zero)).mp this)
  rw [hsplit, map_mul, hcw, mul_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.PushDiff
open UpperTheory.V.FW

theorem UpperTheory.V.FW.pushDiff :
    ∀ (k : Type) [CommRing k] (M m : ℕ) [NeZero M] (h : m ∣ M) (N : ℕ) (P : ℕ → k) (g : ZMod M → k), (∀ s, g s - g (s - N) = ∑ j ∈ Finset.range N, if (j : ZMod M) = s then P j else 0) → ∀ y : ZMod m, push h g y - push h g (y - N) = ∑ j ∈ Finset.range N, if (j : ZMod m) = y then P j else 0 := by
  intro k _ M m _ h N P g hg y
  simp only [push]
  have shift : (∑ s ∈ Finset.univ.filter (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y - N), g s)
      = ∑ s ∈ Finset.univ.filter (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y), g (s - N) := by
    apply Finset.sum_nbij' (fun s : ZMod M => s + (N : ZMod M)) (fun s : ZMod M => s - (N : ZMod M))
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [map_add (f := _), hs, map_natCast]
      ring
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [map_sub, hs, map_natCast]
    · intro s _
      ring
    · intro s _
      ring
    · intro s _
      congr 1
      ring
  rw [shift, ← Finset.sum_sub_distrib]
  simp_rw [hg]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_ite_eq]
  have key : (j : ZMod M) ∈ Finset.univ.filter
      (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y) ↔ (j : ZMod m) = y := by
    rw [Finset.mem_filter, ZMod.castHom_apply, ZMod.cast_natCast h]
    simp
  by_cases hj : (j : ZMod m) = y
  · rw [if_pos (key.mpr hj), if_pos hj]
  · rw [if_neg (fun t => hj (key.mp t)), if_neg hj]
end

open UpperTheory.V.FW

theorem UpperTheory.V.FW.nonvan :
    ∀ (l : ℕ) [Fact l.Prime] (f c : ℕ), f.Coprime l → Odd c → 1 < c → c.Coprime (f * l) → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ (n : ℕ) [NeZero (f * l ^ n)] (h : l ^ n₀ ∣ f * l ^ n), n₀ ≤ n → ∀ (k : Type) [Field k] [CharP k l] (χ : (ZMod (f * l ^ n))ˣ →* kˣ), χ (-1) = -1 → tw χ (piQ l n₀ h) (toK k _ (thetaH (f * l ^ n) c)) ≠ 0 := by
  intro l _ f c hf hc1 hc hcop
  obtain ⟨R, hRne, hRW, hRind, hRneg, hRcov, -, -⟩ := reps l
  have hl := (Fact.out : l.Prime)
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' (Nat.coprime_zero_left l |>.mp hf)
  have hN0 : c * (f * l) ≠ 0 :=
    Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero hf0 hl.ne_zero)
  haveI : Nonempty R := hRne.to_subtype
  obtain ⟨n₁, hn₁⟩ := sinnott l R (fun r => (r : ℤ_[l]ˣ)) (c * (f * l)) hN0
    (fun i j hij a b hab => hRind i i.2 j j.2 (fun e => hij (Subtype.ext e)) a b hab)
  refine ⟨max n₁ 2, le_max_right _ _, ?_⟩
  intro n _ h hn k _ _ χ hχ htw
  have hcf := Nat.coprime_mul_iff_right.mp hcop
  have hcM : c.Coprime (f * l ^ n) :=
    Nat.coprime_mul_iff_right.mpr ⟨hcf.1, Nat.Coprime.pow_right n hcf.2⟩
  have hn1 : 1 ≤ n := le_trans (by omega) (le_trans (le_max_right n₁ 2) hn)
  have hn2 : 2 ≤ n := le_trans (le_max_right n₁ 2) hn
  haveI : Fact (1 < f * l ^ n) := ⟨by
    have h1 : 1 < l ^ n := Nat.one_lt_pow (by omega) hl.one_lt
    have h2 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr hf0
    calc 1 < l ^ n := h1
      _ ≤ f * l ^ n := Nat.le_mul_of_pos_left _ h2⟩
  have hodd : ∀ s : (ZMod (f * l ^ n))ˣ,
      gc (f * l ^ n) c (-(s : ZMod (f * l ^ n))) = -gc (f * l ^ n) c s :=
    fun s => gcNeg _ c _ hcM hc1 s.ne_zero
  have hsum := twCoef l (f * l ^ n) (max n₁ 2) h k χ (gc (f * l ^ n) c) R
    (le_max_right _ _) hχ hodd hRW hRneg hRcov htw
  set Ψ : ZMod (f * l ^ n) → k := ⇑(MulChar.ofUnitHom χ) with hΨ
  have hper : ∀ x : ZMod (f * l ^ n), Ψ (x + ↑(f * l)) = Ψ x :=
    fun x => charPer l f n k χ x hf hn1
  have hshift := fun s => gcShift (f * l ^ n) c (f * l) k Ψ s hcM hper
  have hpush := pushDiff k (f * l ^ n) (l ^ max n₁ 2) h (c * (f * l))
    (fun j => Ψ ↑j * (1 - if c ∣ j then (c : k) else 0))
    (fun s => ((gc (f * l ^ n) c s : ℤ) : k) * Ψ s) hshift
  have hP := hn₁ (max n₁ 2) (le_max_left _ _) k
    (fun j => Ψ ↑j * (1 - if c ∣ j then (c : k) else 0))
    (push h fun s => ((gc (f * l ^ n) c s : ℤ) : k) * Ψ s) hpush hsum 1
    (by
      have : 1 ≤ f * l := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hf0 hl.ne_zero)
      nlinarith)
  have hndvd : ¬ c ∣ 1 := by
    intro hd
    have := Nat.le_of_dvd one_pos hd
    omega
  simp only [hndvd, if_false, sub_zero, mul_one, Nat.cast_one, hΨ, map_one] at hP
  exact one_ne_zero hP
