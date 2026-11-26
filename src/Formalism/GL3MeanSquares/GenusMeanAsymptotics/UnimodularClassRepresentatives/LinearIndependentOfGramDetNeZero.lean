module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOrthUnitFrame
open Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocF

open Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}

theorem exists_next_unit (hS : IsHermSemilocal S)
    (hloc : ∀ a ∈ S, ∀ b ∈ S, star a = a → star b = b → ¬ IsUnitIn S a → ¬ IsUnitIn S b →
      IsUnitIn S (a + b + 1))
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (hM : IsSelfDualMod S h M)
    {ι : Type*} [DecidableEq ι] (x : ι → V) (s : Finset ι) (hxM : ∀ i ∈ s, x i ∈ M)
    (hxo : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → h (x i) (x j) = 0)
    (hxu : ∀ i ∈ s, IsUnitIn S (h (x i) (x i)))
    (v : V) (hv : v ≠ 0) (hvo : ∀ i ∈ s, h (x i) v = 0) :
    ∃ z ∈ M, IsUnitIn S (h z z) ∧ ∀ i ∈ s, h (x i) z = 0 := by
  have hquad : ∀ (p q : V) (m : K), h (p + m • q) (p + m • q) =
      h p p + m * h p q + star m * h q p + star m * m * h q q := by
    intro p q m
    simp only [map_add (f := _), map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, map_smul, RingHom.id_apply]
    ring
  obtain ⟨hstar, -, hunram, hprinc, -⟩ := hS
  obtain ⟨hsm, hint, hdual, hspan⟩ := hM
  have hsym : ∀ a b : V, star (h a b) = h b a := fun a b => by
    rw [← starRingEnd_apply]
    exact hs.eq a b
  have hunit : ∀ a : K, IsUnitIn S a ↔ a ≠ 0 ∧ a ∈ S ∧ a⁻¹ ∈ S := fun a => by
    unfold IsUnitIn
    exact Iff.rfl

  obtain ⟨t, ht0, htM⟩ := hspan v
  have hv' : t • v ≠ 0 := smul_ne_zero ht0 hv
  have hvo' : ∀ i ∈ s, h (x i) (t • v) = 0 := fun i hi => by
    rw [map_smul, hvo i hi, smul_zero]

  obtain ⟨α, ⟨m0, hm0, rfl⟩, hα0, hα⟩ := hprinc
    { carrier := {a | ∃ m ∈ M, h m (t • v) = a}
      zero_mem' := ⟨0, M.zero_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨m1, hm1, rfl⟩ ⟨m2, hm2, rfl⟩
        exact ⟨m1 + m2, M.add_mem hm1 hm2, by simp [mul_add]⟩
      neg_mem' := by
        rintro _ ⟨m, hm, rfl⟩
        exact ⟨-m, M.neg_mem hm, by simp⟩ }
    (by
      rintro c hc _ ⟨m, hm, rfl⟩
      refine ⟨star c • m, hsm _ (hstar c hc) m hm, ?_⟩
      simp only [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul,
        RingHom.id_apply]
      try ring)
    ⟨h (t • v) (t • v), ⟨t • v, htM, rfl⟩, fun h0 => hv' (hd _ h0)⟩
    ⟨1, one_ne_zero, by
      rintro _ ⟨m, hm, rfl⟩
      rw [one_mul]
      exact hint m hm _ htM⟩
  set u := h m0 (t • v) with hu

  set w := u⁻¹ • (t • v) with hw
  have hwM : w ∈ M := by
    apply hdual
    intro m hm
    rw [hw, map_smul, smul_eq_mul, mul_comm]
    exact hα _ ⟨m, hm, rfl⟩
  have hm0w : h m0 w = 1 := by
    rw [hw, map_smul, smul_eq_mul, ← hu]
    exact inv_mul_cancel₀ hα0
  have hwo : ∀ i ∈ s, h (x i) w = 0 := fun i hi => by
    rw [hw, map_smul, hvo' i hi, smul_zero]

  set c : ι → K := fun i => h (x i) m0 * (h (x i) (x i))⁻¹ with hc
  set y := m0 - ∑ i ∈ s, c i • x i with hy
  have hcS : ∀ i ∈ s, c i ∈ S := fun i hi =>
    S.mul_mem (hint _ (hxM i hi) _ hm0) ((hunit _).mp (hxu i hi)).2.2
  have hyM : y ∈ M := by
    refine M.sub_mem hm0 (M.sum_mem fun i hi => ?_)
    exact hsm _ (hcS i hi) _ (hxM i hi)
  have hyo : ∀ j ∈ s, h (x j) y = 0 := by
    intro j hj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, map_sub, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · have hne : h (x j) (x j) ≠ 0 := ((hunit _).mp (hxu j hj)).1
      simp only [hc]
      rw [inv_mul_cancel_right₀ hne, sub_self]
    · intro i hi hij
      rw [hxo j hj i hi (Ne.symm hij), mul_zero]
    · intro hjs
      exact absurd hj hjs
  have hyw : h y w = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, map_sub, map_sum, LinearMap.sub_apply]
    first
      | rw [LinearMap.sum_apply]
      | rw [LinearMap.coe_fn_sum, Finset.sum_apply]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_zero (fun i hi => by rw [hwo i hi, mul_zero]), hm0w, sub_zero]
  have hwy : h w y = 1 := by
    rw [← hsym, hyw, star_one]

  obtain ⟨θ, hθ, hδ⟩ := hunram
  obtain ⟨hδ0, hδS, hδi⟩ := (hunit _).mp hδ
  set μ := θ * (θ - star θ)⁻¹ with hμ
  have hμS : μ ∈ S := S.mul_mem hθ hδi
  have e1 : μ * (θ - star θ) = θ := by
    rw [hμ]
    exact inv_mul_cancel_right₀ hδ0 θ
  have e2 : star μ * -(θ - star θ) = star θ := by
    have h' := congrArg star e1
    rw [star_mul', star_sub, star_star] at h'
    linear_combination h'
  have hμμ : μ + star μ = 1 := by
    have : (μ + star μ) * (θ - star θ) = 1 * (θ - star θ) := by
      linear_combination e1 - e2
    exact mul_right_cancel₀ hδ0 this
  by_cases ha : IsUnitIn S (h y y)
  · exact ⟨y, hyM, ha, hyo⟩
  by_cases hb : IsUnitIn S (h w w)
  · exact ⟨w, hwM, hb, hwo⟩
  refine ⟨y + μ • w, M.add_mem hyM (hsm _ hμS _ hwM), ?_, ?_⟩
  · have hzz : h (y + μ • w) (y + μ • w) = h y y + star μ * μ * h w w + 1 := by
      rw [hquad, hyw, hwy]
      linear_combination hμμ
    rw [hzz]
    have hwwS : h w w ∈ S := hint _ hwM _ hwM
    have hbS : star μ * μ * h w w ∈ S := S.mul_mem (S.mul_mem (hstar _ hμS) hμS) hwwS
    apply hloc _ (hint _ hyM _ hyM) _ hbS (hsym y y)
    · rw [star_mul', star_mul', star_star, hsym w w]
      ring
    · exact ha
    · intro hbu
      apply hb
      obtain ⟨hb0, -, hbi⟩ := (hunit _).mp hbu
      have hww0 : h w w ≠ 0 := fun h0 => hb0 (by rw [h0, mul_zero])
      have hμ0 : star μ * μ ≠ 0 := fun h0 => hb0 (by rw [h0, zero_mul])
      refine (hunit _).mpr ⟨hww0, hwwS, ?_⟩
      have : (h w w)⁻¹ = star μ * μ * (star μ * μ * h w w)⁻¹ := by
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hμ0, one_mul]
      rw [this]
      exact S.mul_mem (S.mul_mem (hstar _ hμS) hμS) hbi
  · intro i hi
    rw [map_add (f := _), map_smul, hyo i hi, hwo i hi, smul_zero, add_zero]

theorem exists_orth_unit_frame [FiniteDimensional K V] (hS : IsHermSemilocal S)
    (hloc : ∀ a ∈ S, ∀ b ∈ S, star a = a → star b = b → ¬ IsUnitIn S a → ¬ IsUnitIn S b →
      IsUnitIn S (a + b + 1))
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (hM : IsSelfDualMod S h M) :
    ∃ x : Fin (finrank K V) → V, (∀ i, x i ∈ M) ∧ (∀ i j, i ≠ j → h (x i) (x j) = 0) ∧
      ∀ i, IsUnitIn S (h (x i) (x i)) := by
  classical
  have P : ∀ k, k ≤ finrank K V → ∃ x : ℕ → V, (∀ i < k, x i ∈ M) ∧
      (∀ i < k, ∀ j < k, i ≠ j → h (x i) (x j) = 0) ∧ ∀ i < k, IsUnitIn S (h (x i) (x i)) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero _),
        fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨x, hxM, hxo, hxu⟩ := ih (by omega)
      set W : Submodule K V := Submodule.span K (((Finset.range k).image x : Finset V) : Set V)
        with hW
      have hWne : W ≠ ⊤ := by
        intro htop
        have h1 : finrank K W ≤ k :=
          (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans (by simp))
        rw [htop, finrank_top] at h1
        omega
      obtain ⟨u, hu⟩ : ∃ u, u ∉ W := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        exact hWne (eq_top_iff.mpr fun u _ => hcon u)
      have hxW : ∀ i ∈ Finset.range k, x i ∈ W := fun i hi =>
        Submodule.subset_span (by exact_mod_cast Finset.mem_image_of_mem x hi)
      have hsW : ∑ i ∈ Finset.range k, (h (x i) u * (h (x i) (x i))⁻¹) • x i ∈ W :=
        W.sum_mem fun i hi => W.smul_mem _ (hxW i hi)
      obtain ⟨z, hzM, hzu, hzo⟩ := exists_next_unit hS hloc hs hd hM x (Finset.range k)
        (fun i hi => hxM i (Finset.mem_range.mp hi))
        (fun i hi j hj => hxo i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj))
        (fun i hi => hxu i (Finset.mem_range.mp hi))
        (u - ∑ i ∈ Finset.range k, (h (x i) u * (h (x i) (x i))⁻¹) • x i)
        (fun h0 => hu (by rw [sub_eq_zero.mp h0]; exact hsW))
        (by
          intro j hj
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sub, map_sum, Finset.sum_eq_single j]
          · rw [map_smul, smul_eq_mul,
              inv_mul_cancel_right₀ (hxu j (Finset.mem_range.mp hj)).1, sub_self]
          · intro i hi hij
            rw [map_smul, hxo j (Finset.mem_range.mp hj) i (Finset.mem_range.mp hi)
              (Ne.symm hij), smul_zero]
          · exact fun hj' => absurd hj hj')
      have hzo' : ∀ i < k, h z (x i) = 0 := fun i hi => by
        rw [← hs.eq, hzo i (Finset.mem_range.mpr hi), map_zero]
      refine ⟨fun i => if i = k then z else x i, ?_, ?_, ?_⟩
      · intro i hi
        by_cases hik : i = k
        · simpa [hik] using hzM
        · simpa [hik] using hxM i (by omega)
      · intro i hi j hj hij
        by_cases hik : i = k
        · have hjk : j ≠ k := fun e => hij (hik.trans e.symm)
          simpa [hik, hjk] using hzo' j (by omega)
        · by_cases hjk : j = k
          · simpa [hik, hjk] using hzo i (Finset.mem_range.mpr (by omega))
          · simpa [hik, hjk] using hxo i (by omega) j (by omega) hij
      · intro i hi
        by_cases hik : i = k
        · simpa [hik] using hzu
        · simpa [hik] using hxu i (by omega)
  obtain ⟨x, h1, h2, h3⟩ := P _ le_rfl
  exact ⟨fun i => x i, fun i => h1 i i.isLt,
    fun i j hij => h2 i i.isLt j j.isLt (fun e => hij (Fin.ext e)), fun i => h3 i i.isLt⟩

end Formalism.HermitianLattices.Ext.L3.LocF
end
end

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocF

open Formalism.HermitianLattices.Ext.L3.WA

section Units

variable {K : Type*} [Field K] {S : Subring K}

theorem isUnitIn_mul {a b : K} (ha : IsUnitIn S a) (hb : IsUnitIn S b) : IsUnitIn S (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩

theorem isUnitIn_one : IsUnitIn S (1 : K) :=
  ⟨one_ne_zero, S.one_mem, by rw [inv_one]; exact S.one_mem⟩

theorem isUnitIn_prod {ι : Type*} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, IsUnitIn S (f i)) :
    IsUnitIn S (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IsUnitIn S) (fun _ _ => isUnitIn_mul) isUnitIn_one hf

end Units

section Ring

variable {K : Type} [Field K] [NumberField K] [StarRing K]

private lemma exists_int_algebraMap_eq_star (x : 𝓞 K) : ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = star (algebraMap (𝓞 K) K x) := by
  have hx : IsIntegral ℤ (algebraMap (𝓞 K) K x) := x.isIntegral_coe
  have : IsIntegral ℤ (star (algebraMap (𝓞 K) K x)) := hx.map (starRingEnd K).toIntAlgHom
  exact IsIntegralClosure.isIntegral_iff.mp this

private lemma hcompl_mem_prime_ideal_property {p : Ideal (𝓞 K)} (hp : p.IsPrime) {s : 𝓞 K} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    s ∉ p ∧ ∀ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K s) → t ∉ p := by
  induction hs using Submonoid.closure_induction with
  | mem x hx => exact hx
  | one =>
    refine ⟨fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr h), fun t ht h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr ?_)⟩
    have : t = 1 := IsFractionRing.injective (𝓞 K) K (by rw [ht, map_one, star_one])
    rwa [this] at h
  | mul x y _ _ hx hy =>
    refine ⟨fun h => (hp.mem_or_mem h).elim hx.1 hy.1, fun t ht h => ?_⟩
    obtain ⟨x', hx'⟩ := exists_int_algebraMap_eq_star x
    obtain ⟨y', hy'⟩ := exists_int_algebraMap_eq_star y
    have : t = x' * y' := IsFractionRing.injective (𝓞 K) K (by
      rw [ht, map_mul, map_mul, hx', hy', star_mul, mul_comm])
    rw [this] at h
    exact (hp.mem_or_mem h).elim (hx.2 x' hx') (hy.2 y' hy')

private lemma hcompl_unit_property_of_isPrime {p : Ideal (𝓞 K)} (hp : p.IsPrime) {N S : 𝓞 K} (hS : S ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p)
    (hN : N ∉ p) (hfix : star (algebraMap (𝓞 K) K N / algebraMap (𝓞 K) K S) =
      algebraMap (𝓞 K) K N / algebraMap (𝓞 K) K S) :
    IsUnitIn (locRing p) (algebraMap (𝓞 K) K N / algebraMap (𝓞 K) K S) := by
  have inj := IsFractionRing.injective (𝓞 K) K
  obtain ⟨hS1, hS2⟩ := hcompl_mem_prime_ideal_property hp hS
  have ne0 : ∀ {u : 𝓞 K}, u ∉ p → algebraMap (𝓞 K) K u ≠ 0 := fun hu h0 =>
    hu (by rw [(map_eq_zero_iff _ inj).mp h0]; exact p.zero_mem)
  obtain ⟨S', hS'⟩ := exists_int_algebraMap_eq_star S
  obtain ⟨N', hN'⟩ := exists_int_algebraMap_eq_star N
  have hS'p := hS2 S' hS'

  have key : N' * S = N * S' := inj (by
    have h := hfix
    rw [star_div₀, div_eq_div_iff (by rw [← hS']; exact ne0 hS'p) (ne0 hS1)] at h
    rw [map_mul, map_mul, hN', hS', h])
  have hN'p : N' ∉ p := fun h =>
    (hp.mem_or_mem (show N * S' ∈ p from key ▸ p.mul_mem_right S h)).elim hN hS'p
  have hNc : N ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p :=
    Submonoid.subset_closure ⟨hN, fun t ht => by rw [inj (ht.trans hN'.symm)]; exact hN'p⟩
  refine ⟨div_ne_zero (ne0 hN) (ne0 hS1), ?_, ?_⟩
  · show _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    exact ⟨S, hS, Submodule.mem_one.mpr ⟨N, by rw [mul_div_cancel₀ _ (ne0 hS1)]⟩⟩
  · show _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR, inv_div]
    exact ⟨N, hNc, Submodule.mem_one.mpr ⟨S, by rw [mul_div_cancel₀ _ (ne0 hN)]⟩⟩

theorem fixed_nonunit {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p)
    (hfix : star a = a) (hnu : ¬ IsUnitIn (locRing p) a) :
    ∃ r ∈ p, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
      a = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s := by
  have ha' : a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := ha
  rw [Formalism.HermitianLatticesTheory.locDual_mem_locR] at ha'
  obtain ⟨s, hs, hsa⟩ := ha'
  obtain ⟨t, ht⟩ := Submodule.mem_one.mp hsa
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := fun h0 => (hcompl_mem_prime_ideal_property hp hs).1
    (by rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mp h0]; exact p.zero_mem)
  have hat : a = algebraMap (𝓞 K) K t / algebraMap (𝓞 K) K s := by
    rw [ht, mul_div_cancel_left₀ a hs0]
  refine ⟨t, ?_, s, hs, hat⟩
  by_contra htp
  rw [hat] at hnu hfix
  exact hnu (hcompl_unit_property_of_isPrime hp hs htp hfix)

theorem locRing_local {p : Ideal (𝓞 K)} (hp : p.IsPrime) :
    ∀ a ∈ locRing p, ∀ b ∈ locRing p, star a = a → star b = b → ¬ IsUnitIn (locRing p) a →
      ¬ IsUnitIn (locRing p) b → IsUnitIn (locRing p) (a + b + 1) := by
  intro a ha b hb hfa hfb hna hnb
  have inj := IsFractionRing.injective (𝓞 K) K
  obtain ⟨r1, hr1, s1, hs1, rfl⟩ := fixed_nonunit hp ha hfa hna
  obtain ⟨r2, hr2, s2, hs2, rfl⟩ := fixed_nonunit hp hb hfb hnb
  have ne0 : ∀ {u : 𝓞 K}, u ∉ p → algebraMap (𝓞 K) K u ≠ 0 := fun hu h0 =>
    hu (by rw [(map_eq_zero_iff _ inj).mp h0]; exact p.zero_mem)
  have h1 := ne0 (hcompl_mem_prime_ideal_property hp hs1).1
  have h2 := ne0 (hcompl_mem_prime_ideal_property hp hs2).1
  have hS : s1 * s2 ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := Submonoid.mul_mem _ hs1 hs2
  have hN : r1 * s2 + r2 * s1 + s1 * s2 ∉ p := by
    intro h
    have : s1 * s2 ∈ p := by
      have := p.sub_mem h (p.add_mem (p.mul_mem_right s2 hr1) (p.mul_mem_right s1 hr2))
      simpa using this
    exact (hcompl_mem_prime_ideal_property hp hS).1 this
  have e : algebraMap (𝓞 K) K r1 / algebraMap (𝓞 K) K s1 + algebraMap (𝓞 K) K r2 / algebraMap (𝓞 K) K s2 + 1 =
      algebraMap (𝓞 K) K (r1 * s2 + r2 * s1 + s1 * s2) / algebraMap (𝓞 K) K (s1 * s2) := by
    simp only [map_add (f := _), map_mul]
    field_simp
  have hf := congrArg id (show star (algebraMap (𝓞 K) K r1 / algebraMap (𝓞 K) K s1 +
      algebraMap (𝓞 K) K r2 / algebraMap (𝓞 K) K s2 + 1) = _ by rw [star_add, star_add, star_one, hfa, hfb])
  rw [e] at hf ⊢
  exact hcompl_unit_property_of_isPrime hp hS hN hf

theorem isUnitIn_algebraMap_iff {p : Ideal (𝓞 K)} (hp : p.IsPrime) (r : 𝓞 K) :
    IsUnitIn (locRing p) (algebraMap (𝓞 K) K r) ↔ r ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  have inj := IsFractionRing.injective (𝓞 K) K
  constructor
  · rintro ⟨h0, -, hinv⟩
    have hinv' : (algebraMap (𝓞 K) K r)⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := hinv
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR] at hinv'
    obtain ⟨s, hs, hsr⟩ := hinv'
    obtain ⟨t, ht⟩ := Submodule.mem_one.mp hsr
    have hst : s = t * r := inj (by rw [map_mul, ht, mul_assoc, inv_mul_cancel₀ h0, mul_one])
    obtain ⟨hs1, hs2⟩ := hcompl_mem_prime_ideal_property hp hs
    refine Submonoid.subset_closure ⟨fun h => hs1 (hst ▸ p.mul_mem_left t h), fun u hu hup => ?_⟩
    obtain ⟨t', ht'⟩ := exists_int_algebraMap_eq_star t
    apply hs2 (t' * u) _ (p.mul_mem_left t' hup)
    rw [map_mul, ht', hu, hst, map_mul, star_mul, mul_comm]
  · intro hr
    obtain ⟨hr1, -⟩ := hcompl_mem_prime_ideal_property hp hr
    have h0 : algebraMap (𝓞 K) K r ≠ 0 := fun h0 =>
      hr1 (by rw [(map_eq_zero_iff _ inj).mp h0]; exact p.zero_mem)
    refine ⟨h0, ?_, ?_⟩
    · show _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
      rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
      exact ⟨1, Submonoid.one_mem _, Submodule.mem_one.mpr ⟨r, by rw [map_one, one_mul]⟩⟩
    · show _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
      rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
      exact ⟨r, hr, Submodule.mem_one.mpr ⟨1, by rw [map_one, mul_inv_cancel₀ h0]⟩⟩

end Ring

section Gram

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}

theorem gram_mulVec (x : Fin n → V) (c : Fin n → K) (i : Fin n) :
    ((Matrix.of fun i j => h (x i) (x j)) *ᵥ c) i = h (x i) (∑ j, c j • x j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, map_sum, map_smul, smul_eq_mul, mul_comm]

theorem linearIndependent_of_gram_det_ne_zero (x : Fin n → V)
    (hdet : (Matrix.of fun i j => h (x i) (x j)).det ≠ 0) : LinearIndependent K x := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hG : (Matrix.of fun i j => h (x i) (x j)) *ᵥ c = 0 := by
    funext i
    rw [gram_mulVec h x c i, hc, map_zero, Pi.zero_apply]
  exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hG) i

theorem gram_det_ne_zero (hd : ∀ x, h x x = 0 → x = 0) (x : Fin n → V)
    (hli : LinearIndependent K x) : (Matrix.of fun i j => h (x i) (x j)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have e : ∀ i, h (x i) (∑ j, v j • x j) = 0 := fun i => by
    rw [← gram_mulVec h x v i, hv, Pi.zero_apply]
  have e' : ∀ i, h (v i • x i) (∑ j, v j • x j) = 0 := fun i => by
    rw [map_smulₛₗ, LinearMap.smul_apply, e, smul_zero]
  have hy : h (∑ j, v j • x j) (∑ j, v j • x j) = 0 := by
    have hs : h (∑ j, v j • x j) = ∑ j, h (v j • x j) := map_sum h _ _
    rw [hs, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => e' i
  have := Fintype.linearIndependent_iff.mp hli v (hd _ hy)
  exact hv0 (funext this)

theorem star_gram_det (hs : h.IsSymm) (x : Fin n → V) :
    star (Matrix.of fun i j => h (x i) (x j)).det = (Matrix.of fun i j => h (x i) (x j)).det := by
  rw [← Matrix.det_conjTranspose]
  congr 1
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
  first
  | exact hs.eq (x j) (x i)
  | exact hs (x j) (x i)

end Gram

section Cramer

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}

theorem det_smul_mem {L : Submodule (𝓞 K) V} (x : Fin n → V) (hx : ∀ i, x i ∈ L)
    (hspan : Submodule.span K (Set.range x) = ⊤) (g : Matrix (Fin n) (Fin n) (𝓞 K))
    (hg : ∀ i j, algebraMap (𝓞 K) K (g i j) = h (x i) (x j)) (y : V)
    (hy : ∀ i, h (x i) y ∈ (1 : Submodule (𝓞 K) K)) : g.det • y ∈ L := by
  have hy' : y ∈ Submodule.span K (Set.range x) := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy'
  choose β hβ using fun i => Submodule.mem_one.mp (hy i)
  set G := Matrix.of fun i j => h (x i) (x j) with hGdef
  have hGg : (algebraMap (𝓞 K) K).mapMatrix g = G := by
    ext i j
    simp [RingHom.mapMatrix_apply, hg, hGdef]
  have hGc : G *ᵥ c = fun i => algebraMap (𝓞 K) K (β i) := by
    funext i
    rw [hGdef, gram_mulVec h x c i, hc, hβ]

  have hdetc : G.det • c = fun j => algebraMap (𝓞 K) K ((g.adjugate *ᵥ β) j) := by
    funext j
    have h1 : G.det • c = G.adjugate *ᵥ (G *ᵥ c) := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
      first
      | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      | simp
    rw [h1, hGc, RingHom.map_mulVec, ← hGg, ← RingHom.map_adjugate]
    rfl
  have hdet : algebraMap (𝓞 K) K g.det = G.det := by rw [RingHom.map_det, hGg]
  rw [← algebraMap_smul K g.det y, hdet, ← hc, Finset.smul_sum]
  have hj : ∀ j, G.det • (c j • x j) = (g.adjugate *ᵥ β) j • x j := by
    intro j
    have := congrFun hdetc j
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [smul_smul, this, algebraMap_smul]
  rw [Finset.sum_congr rfl fun j _ => hj j]
  exact L.sum_mem fun j _ => L.smul_mem _ (hx j)

end Cramer

end Formalism.HermitianLattices.Ext.L3.LocF
