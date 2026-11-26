module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PerpEqPerpNb
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitOfNotDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HfAlgSmulRight
open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ}

def hf (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (x y : Fin r → K) : K :=
  (fun i => cK (x i)) ⬝ᵥ (J.mulVec y)

theorem _root_.GlobalTheory.HermNbr.hf_add_right (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K)
    (x y z : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J x (y + z) =
      _root_.GlobalTheory.HermNbr.hf cK J x y + _root_.GlobalTheory.HermNbr.hf cK J x z := by
  simp only [_root_.GlobalTheory.HermNbr.hf, Matrix.mulVec_add, dotProduct, Pi.add_apply,
    mul_add, Finset.sum_add_distrib]

theorem _root_.GlobalTheory.HermNbr.hf_add_left (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K)
    (x y z : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J (x + y) z =
      _root_.GlobalTheory.HermNbr.hf cK J x z + _root_.GlobalTheory.HermNbr.hf cK J y z := by
  simp only [_root_.GlobalTheory.HermNbr.hf, dotProduct, Pi.add_apply, map_add (f := _), add_mul,
    Finset.sum_add_distrib]

theorem _root_.GlobalTheory.HermNbr.hf_smul_right (cK : K ≃+* K)
    (J : Matrix (Fin r) (Fin r) K) (a : K) (x y : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J x (a • y) = a * _root_.GlobalTheory.HermNbr.hf cK J x y := by
  simp only [_root_.GlobalTheory.HermNbr.hf, dotProduct, Matrix.mulVec_smul, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem _root_.GlobalTheory.HermNbr.hf_algSmul_right (cK : K ≃+* K)
    (J : Matrix (Fin r) (Fin r) K) (a : O)
    (x y : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J x (a • y) =
      algebraMap O K a * _root_.GlobalTheory.HermNbr.hf cK J x y := by
  rw [← algebraMap_smul K a y, _root_.GlobalTheory.HermNbr.hf_smul_right]

theorem _root_.GlobalTheory.HermNbr.hf_algSmul_left (cK : K ≃+* K)
    (J : Matrix (Fin r) (Fin r) K) (a : O)
    (x y : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J (a • x) y =
      cK (algebraMap O K a) * _root_.GlobalTheory.HermNbr.hf cK J x y := by
  simp only [_root_.GlobalTheory.HermNbr.hf, dotProduct, Pi.smul_apply, Algebra.smul_def,
    map_mul, Finset.mul_sum, mul_assoc]

theorem _root_.GlobalTheory.HermNbr.hf_sub_right (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K)
    (x y z : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J x (y - z) =
      _root_.GlobalTheory.HermNbr.hf cK J x y - _root_.GlobalTheory.HermNbr.hf cK J x z := by
  simp only [_root_.GlobalTheory.HermNbr.hf, Matrix.mulVec_sub, dotProduct, Pi.sub_apply,
    mul_sub, Finset.sum_sub_distrib]

theorem _root_.GlobalTheory.HermNbr.hf_sub_left (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K)
    (x y z : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J (x - y) z =
      _root_.GlobalTheory.HermNbr.hf cK J x z - _root_.GlobalTheory.HermNbr.hf cK J y z := by
  simp only [_root_.GlobalTheory.HermNbr.hf, dotProduct, Pi.sub_apply, map_sub, sub_mul,
    Finset.sum_sub_distrib]

theorem _root_.GlobalTheory.HermNbr.hf_conj (cK : K ≃+* K) (hc2 : ∀ x, cK (cK x) = x)
    (J : Matrix (Fin r) (Fin r) K)
    (hJ : J.transpose.map cK = J) (x y : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J y x = cK (_root_.GlobalTheory.HermNbr.hf cK J x y) := by
  have hJ' : ∀ i j, cK (J i j) = J j i := fun i j => by
    simpa using congrFun (congrFun hJ j) i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [_root_.GlobalTheory.HermNbr.hf, dotProduct, Matrix.mulVec, map_sum, map_mul, hc2,
    hJ', Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def perp (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (L : Submodule O (Fin r → K))
    (v : Fin r → K) : Submodule O (Fin r → K) where
  carrier := {x | x ∈ L ∧ hf cK J v x ∈ (algebraMap O K).range}
  add_mem' := fun {a b} ha hb => ⟨L.add_mem ha.1 hb.1, by
    rw [hf_add_right]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨L.zero_mem, by
    have := hf_smul_right cK J 0 v 0
    simp only [zero_smul, zero_mul] at this
    rw [this]; exact zero_mem _⟩
  smul_mem' := fun a x hx => ⟨L.smul_mem a hx.1, by
    rw [hf_algSmul_right]; exact mul_mem ⟨a, rfl⟩ hx.2⟩

theorem _root_.GlobalTheory.HermNbr.mem_perp {cK : K ≃+* K} {J : Matrix (Fin r) (Fin r) K}
    {L : Submodule O (Fin r → K)}
    {v x : Fin r → K} : x ∈ _root_.GlobalTheory.HermNbr.perp cK J L v ↔
      x ∈ L ∧ _root_.GlobalTheory.HermNbr.hf cK J v x ∈ (algebraMap O K).range :=
  Iff.rfl

def nb (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (L : Submodule O (Fin r → K))
    (v : Fin r → K) : Submodule O (Fin r → K) :=
  perp cK J L v ⊔ Submodule.span O {v}

def IsSD (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (L : Submodule O (Fin r → K)) : Prop :=
  ∀ x, x ∈ L ↔ ∀ y ∈ L, hf cK J x y ∈ (algebraMap O K).range

noncomputable def idx (ϖ : O) (L : Submodule O (Fin r → K)) : ℕ :=
  (L.map (ϖ • (LinearMap.id : (Fin r → K) →ₗ[O] (Fin r → K)))).toAddSubgroup.relIndex
    L.toAddSubgroup

def Good (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (ϖ : O) (N : ℕ)
    (L : Submodule O (Fin r → K)) : Prop :=
  IsSD cK J L ∧ (∀ x : Fin r → K, ∃ k : ℕ, (ϖ ^ k) • x ∈ L) ∧ idx ϖ L = N

def IsStep (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (ϖ : O)
    (L : Submodule O (Fin r → K)) (v : Fin r → K) : Prop :=
  v ∉ L ∧ ϖ • v ∈ L ∧ hf cK J v v ∈ (algebraMap O K).range

def Nbrs (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (ϖ : O)
    (L : Submodule O (Fin r → K)) : Set (Submodule O (Fin r → K)) :=
  {L' | ∃ v, IsStep cK J ϖ L v ∧ L' = nb cK J L v}

theorem _root_.GlobalTheory.HermNbr.graph_sum {X : Type} (S : Set X) (i : X → X → ℕ)
    (Nb : X → Set X) (Q : ℕ) (hQ : 2 ≤ Q)
    (s D : ℝ) (hs : 0 < s) (hD : 0 ≤ D)
    (hρ : D * (Q : ℝ) ^ (-s) < 1)
    (hself : ∀ L ∈ S, i L L = 1)
    (hstep : ∀ L ∈ S, ∀ Λ ∈ S, L ≠ Λ → i L Λ ≠ 0 →
      ∃ L' ∈ Nb L, L' ∈ S ∧ i L' Λ ≠ 0 ∧ Q * i L' Λ ≤ i L Λ)
    (hcard : ∀ L ∈ S, ∀ t : Finset X, (t : Set X) ⊆ Nb L → (t.card : ℝ) ≤ D)
    (L : X) (hL : L ∈ S) (C : Finset X) (hC : (C : Set X) ⊆ S) (hLC : L ∉ C) :
    ∑ Λ ∈ C, (i L Λ : ℝ) ^ (-s) ≤
      D * (Q : ℝ) ^ (-s) / (1 - D * (Q : ℝ) ^ (-s)) := by
  classical
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hq0 : 0 ≤ (Q : ℝ) ^ (-s) := Real.rpow_nonneg hQpos.le _
  generalize hq : (Q : ℝ) ^ (-s) = q at hρ hq0 ⊢
  obtain ⟨B, hBdef⟩ : ∃ B, B = D * q / (1 - D * q) := ⟨_, rfl⟩
  rw [← hBdef]
  have hne : (1 - D * q) ≠ 0 := (sub_pos.2 hρ).ne'
  have hB : 0 ≤ B := hBdef ▸ div_nonneg (mul_nonneg hD hq0) (sub_pos.2 hρ).le
  have hfix : D * q * (1 + B) = B := by
    rw [hBdef, one_add_div hne, sub_add_cancel, mul_div_assoc', mul_one]
  have hzero : (0 : ℝ) ^ (-s) = 0 := Real.zero_rpow (neg_ne_zero.2 hs.ne')
  have main : ∀ n : ℕ, ∀ L ∈ S, ∀ C : Finset X, (C : Set X) ⊆ S → L ∉ C →
      (∀ Λ ∈ C, i L Λ ≤ n) → ∑ Λ ∈ C, (i L Λ : ℝ) ^ (-s) ≤ B := by
    intro n
    induction n with
    | zero =>
      intro L hL C hC hLC hn
      have h0 : ∀ Λ ∈ C, (i L Λ : ℝ) ^ (-s) = 0 := fun Λ hΛ => by
        rw [Nat.le_zero.1 (hn Λ hΛ), Nat.cast_zero, hzero]
      rw [Finset.sum_eq_zero h0]
      exact hB
    | succ n ih =>
      intro L hL C hC hLC hn
      have key : ∀ Λ, ∃ L', Λ ∈ S → L ≠ Λ → i L Λ ≠ 0 →
          L' ∈ Nb L ∧ L' ∈ S ∧ i L' Λ ≠ 0 ∧ Q * i L' Λ ≤ i L Λ := by
        intro Λ
        by_cases h : Λ ∈ S ∧ L ≠ Λ ∧ i L Λ ≠ 0
        · obtain ⟨L', h1, h2, h3, h4⟩ := hstep L hL Λ h.1 h.2.1 h.2.2
          exact ⟨L', fun _ _ _ => ⟨h1, h2, h3, h4⟩⟩
        · exact ⟨L, fun a b c => absurd ⟨a, b, c⟩ h⟩
      choose f hf using key
      obtain ⟨C', hC'⟩ : ∃ C', C' = C.filter (fun Λ => i L Λ ≠ 0) := ⟨_, rfl⟩
      have hC'C : C' ⊆ C := hC' ▸ Finset.filter_subset _ _
      have hf' : ∀ Λ ∈ C', f Λ ∈ Nb L ∧ f Λ ∈ S ∧ i (f Λ) Λ ≠ 0 ∧ Q * i (f Λ) Λ ≤ i L Λ := by
        intro Λ hΛ
        rw [hC', Finset.mem_filter] at hΛ
        exact hf Λ (hC hΛ.1) (fun h => hLC (by rw [h]; exact hΛ.1)) hΛ.2
      have hsum : ∑ Λ ∈ C, (i L Λ : ℝ) ^ (-s) = ∑ Λ ∈ C', (i L Λ : ℝ) ^ (-s) := by
        rw [hC', Finset.sum_filter_of_ne]
        intro Λ _ h h0
        exact h (by rw [h0, Nat.cast_zero, hzero])
      have fibre : ∀ L1 ∈ S, ∀ Fb : Finset X, (∀ Λ ∈ Fb, Λ ∈ C' ∧ f Λ = L1) →
          ∑ Λ ∈ Fb, (i L Λ : ℝ) ^ (-s) ≤ q * (1 + B) := by
        intro L1 hL1 Fb hFb
        have hterm : ∀ Λ ∈ Fb, (i L Λ : ℝ) ^ (-s) ≤ q * (i L1 Λ : ℝ) ^ (-s) := by
          intro Λ hΛ
          obtain ⟨hΛC', hfΛ⟩ := hFb Λ hΛ
          obtain ⟨-, -, hne', hle⟩ := hf' Λ hΛC'
          rw [hfΛ] at hne' hle
          have h1 : (1 : ℝ) ≤ i L1 Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hne'
          have h2 : (Q : ℝ) * i L1 Λ ≤ i L Λ := by exact_mod_cast hle
          have h3 : 0 < (Q : ℝ) * i L1 Λ := mul_pos hQpos (by linarith)
          rw [← hq, ← Real.mul_rpow hQpos.le (by linarith), Real.rpow_neg (Nat.cast_nonneg _),
            Real.rpow_neg h3.le]
          exact inv_anti₀ (Real.rpow_pos_of_pos h3 _) (Real.rpow_le_rpow h3.le h2 hs.le)
        have hIH : ∑ Λ ∈ Fb.erase L1, (i L1 Λ : ℝ) ^ (-s) ≤ B := by
          refine ih L1 hL1 (Fb.erase L1) ?_ (Finset.notMem_erase L1 Fb) ?_
          · intro x hx
            exact hC (hC'C (hFb x (Finset.mem_of_mem_erase hx)).1)
          · intro Λ hΛ
            obtain ⟨hΛC', hfΛ⟩ := hFb Λ (Finset.mem_of_mem_erase hΛ)
            obtain ⟨-, -, hne', hle⟩ := hf' Λ hΛC'
            rw [hfΛ] at hne' hle
            have h1 := hn Λ (hC'C hΛC')
            have h2 : 1 ≤ i L1 Λ := Nat.one_le_iff_ne_zero.2 hne'
            have h3 : 2 * i L1 Λ ≤ Q * i L1 Λ := Nat.mul_le_mul_right _ hQ
            omega
        calc ∑ Λ ∈ Fb, (i L Λ : ℝ) ^ (-s) ≤ ∑ Λ ∈ Fb, q * (i L1 Λ : ℝ) ^ (-s) :=
              Finset.sum_le_sum hterm
          _ = q * ∑ Λ ∈ Fb, (i L1 Λ : ℝ) ^ (-s) := by rw [Finset.mul_sum]
          _ ≤ q * ∑ Λ ∈ insert L1 (Fb.erase L1), (i L1 Λ : ℝ) ^ (-s) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.subset_insert_iff.2 subset_rfl)
                (fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)) hq0
          _ = q * (1 + ∑ Λ ∈ Fb.erase L1, (i L1 Λ : ℝ) ^ (-s)) := by
              rw [Finset.sum_insert (Finset.notMem_erase L1 Fb), hself L1 hL1, Nat.cast_one,
                Real.one_rpow]
          _ ≤ q * (1 + B) := mul_le_mul_of_nonneg_left (by linarith) hq0
      rw [hsum, ← Finset.sum_fiberwise_of_maps_to (g := f) (t := C'.image f)
        (fun Λ hΛ => Finset.mem_image_of_mem f hΛ)]
      calc _ ≤ ∑ _L' ∈ C'.image f, q * (1 + B) := by
            refine Finset.sum_le_sum fun L' hL' => ?_
            obtain ⟨Λ0, hΛ0, rfl⟩ := Finset.mem_image.1 hL'
            exact fibre _ (hf' Λ0 hΛ0).2.1 _ fun Λ hΛ => Finset.mem_filter.1 hΛ
        _ = ((C'.image f).card : ℝ) * (q * (1 + B)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ D * (q * (1 + B)) := by
            refine mul_le_mul_of_nonneg_right (hcard L hL _ ?_) (mul_nonneg hq0 (by linarith))
            intro x hx
            obtain ⟨Λ, hΛ, rfl⟩ := Finset.mem_image.1 hx
            exact (hf' Λ hΛ).1
        _ = B := by rw [← mul_assoc]; exact hfix
  exact main (C.sup (i L)) L hL C hC hLC fun Λ hΛ => Finset.le_sup hΛ

end GlobalTheory.HermNbr
end

open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

theorem isUnit_of_not_dvd {ϖ b : O} (hϖ : Irreducible ϖ) (h : ¬ ϖ ∣ b) : IsUnit b := by
  by_contra hb
  have hm : b ∈ IsLocalRing.maximalIdeal O := hb
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
    Ideal.mem_span_singleton] at hm
  exact h hm

theorem alg_ne_zero {ϖ : O} (hϖ : Irreducible ϖ) : algebraMap O K ϖ ≠ 0 := by
  intro h
  exact hϖ.ne_zero (IsFractionRing.injective O K (by simpa using h))

theorem exists_unit_conj (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : Oˣ, cK (algebraMap O K ϖ) = algebraMap O K u * algebraMap O K ϖ := by
  have h1 : Irreducible (c ϖ) := (MulEquiv.irreducible_iff c.toMulEquiv).2 hϖ
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible O h1 hϖ
  refine ⟨u⁻¹, ?_⟩
  have e : c ϖ = ((u⁻¹ : Oˣ) : O) * ϖ := by
    calc c ϖ = c ϖ * u * ((u⁻¹ : Oˣ) : O) := by simp [mul_assoc]
      _ = ϖ * ((u⁻¹ : Oˣ) : O) := by rw [hu]
      _ = _ := mul_comm _ _
  rw [hcK, e, map_mul]

theorem exists_ratio {ϖ : O} (hϖ : Irreducible ϖ) {β γ : K}
    (hβ : β ∉ (algebraMap O K).range) (hβ' : algebraMap O K ϖ * β ∈ (algebraMap O K).range)
    (hγ : algebraMap O K ϖ * γ ∈ (algebraMap O K).range) :
    ∃ a : O, γ = algebraMap O K a * β := by
  obtain ⟨b, hb⟩ := hβ'
  obtain ⟨g, hg⟩ := hγ
  have h0 : algebraMap O K ϖ ≠ 0 := alg_ne_zero hϖ
  have hbu : IsUnit b := by
    apply isUnit_of_not_dvd hϖ
    rintro ⟨e, rfl⟩
    apply hβ
    refine ⟨e, ?_⟩
    rw [map_mul] at hb
    exact (mul_left_cancel₀ h0 hb)
  obtain ⟨u, rfl⟩ := hbu
  refine ⟨g * ((u⁻¹ : Oˣ) : O), ?_⟩
  apply mul_left_cancel₀ h0
  have e1 : algebraMap O K (u : O) * algebraMap O K ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul]; simp
  rw [← hg, map_mul]
  calc algebraMap O K g = algebraMap O K g * (algebraMap O K (u : O) * algebraMap O K ((u⁻¹ : Oˣ) : O)) := by
        rw [e1, mul_one]
    _ = algebraMap O K g * ((algebraMap O K ϖ * β) * algebraMap O K ((u⁻¹ : Oˣ) : O)) := by rw [hb]
    _ = _ := by ring

theorem ratio_mem_iff {ϖ : O} (hϖ : Irreducible ϖ) {β : K}
    (hβ : β ∉ (algebraMap O K).range) (hβ' : algebraMap O K ϖ * β ∈ (algebraMap O K).range)
    (a : O) : algebraMap O K a * β ∈ (algebraMap O K).range ↔ ϖ ∣ a := by
  constructor
  · intro h
    by_contra hd
    obtain ⟨u, rfl⟩ := isUnit_of_not_dvd hϖ hd
    apply hβ
    have e1 : algebraMap O K ((u⁻¹ : Oˣ) : O) * algebraMap O K (u : O) = 1 := by
      rw [← map_mul]; simp
    have : β = algebraMap O K ((u⁻¹ : Oˣ) : O) * (algebraMap O K (u : O) * β) := by
      rw [← mul_assoc, e1, one_mul]
    rw [this]
    exact mul_mem ⟨_, rfl⟩ h
  · rintro ⟨e, rfl⟩
    rw [map_mul, mul_comm (algebraMap O K ϖ), mul_assoc]
    exact mul_mem ⟨_, rfl⟩ hβ'

theorem mul_pair_mem (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x))
    {J : Matrix (Fin r) (Fin r) K} {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K} (hw : ϖ • v ∈ L)
    {l : Fin r → K} (hl : l ∈ L) :
    algebraMap O K ϖ * hf cK J v l ∈ (algebraMap O K).range := by
  obtain ⟨u, hu⟩ := exists_unit_conj c cK hcK (K := K) hϖ
  have h1 := (hSD _).1 hw l hl
  rw [hf_algSmul_left, hu] at h1
  have e1 : algebraMap O K ((u⁻¹ : Oˣ) : O) * algebraMap O K (u : O) = 1 := by
    rw [← map_mul]; simp
  have : algebraMap O K ϖ * hf cK J v l = algebraMap O K ((u⁻¹ : Oˣ) : O) *
      (algebraMap O K (u : O) * algebraMap O K ϖ * hf cK J v l) := by
    rw [mul_assoc, ← mul_assoc (algebraMap O K ((u⁻¹ : Oˣ) : O)), e1, one_mul]
  rw [this]
  exact mul_mem ⟨_, rfl⟩ h1

theorem perp_relIndex (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x))
    {J : Matrix (Fin r) (Fin r) K} {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K} (hv : v ∉ L)
    (hw : ϖ • v ∈ L) :
    (perp cK J L v).toAddSubgroup.relIndex L.toAddSubgroup =
      Nat.card (IsLocalRing.ResidueField O) := by
  classical
  obtain ⟨l0, hl0, hβ⟩ : ∃ l0 ∈ L, hf cK J v l0 ∉ (algebraMap O K).range := by
    by_contra hcon
    push_neg at hcon
    exact hv ((hSD v).2 hcon)
  set β := hf cK J v l0 with hβdef
  have hβ' : algebraMap O K ϖ * β ∈ (algebraMap O K).range :=
    mul_pair_mem c cK hcK hϖ hSD hw hl0
  have hβ0 : β ≠ 0 := by
    intro h0
    exact hβ (h0 ▸ zero_mem _)
  have hex : ∀ l : L.toAddSubgroup, ∃ a : O, hf cK J v (l : Fin r → K) = algebraMap O K a * β :=
    fun l => exists_ratio hϖ hβ hβ' (mul_pair_mem c cK hcK hϖ hSD hw l.2)
  choose a ha using hex
  have hadd : ∀ x y : L.toAddSubgroup, a (x + y) = a x + a y := by
    intro x y
    apply IsFractionRing.injective O K
    apply mul_right_cancel₀ hβ0
    rw [← ha, map_add (f := _), add_mul, ← ha, ← ha]
    simpa using hf_add_right cK J v (x : Fin r → K) y
  let ψ : L.toAddSubgroup →+ IsLocalRing.ResidueField O :=
    AddMonoidHom.mk' (fun l => IsLocalRing.residue O (a l)) (by
      intro x y; rw [hadd, map_add (f := _)])
  have hker : (perp cK J L v).toAddSubgroup.addSubgroupOf L.toAddSubgroup = ψ.ker := by
    ext l
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
    change (l : Fin r → K) ∈ perp cK J L v ↔ IsLocalRing.residue O (a l) = 0
    rw [mem_perp, IsLocalRing.residue_eq_zero_iff,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton,
      ← ratio_mem_iff hϖ hβ hβ', ← ha]
    exact ⟨fun h => h.2, fun h => ⟨l.2, h⟩⟩
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective z
    have hm : b • l0 ∈ L.toAddSubgroup := L.smul_mem b hl0
    refine ⟨⟨b • l0, hm⟩, ?_⟩
    have : a ⟨b • l0, hm⟩ = b := by
      apply IsFractionRing.injective O K
      apply mul_right_cancel₀ hβ0
      rw [← ha]
      exact hf_algSmul_right cK J b v l0
    change IsLocalRing.residue O (a ⟨b • l0, hm⟩) = _
    rw [this]
  rw [AddSubgroup.relIndex, hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj]
  exact Nat.card_congr AddSubgroup.topEquiv.toEquiv

theorem smul_injective {ϖ : O} (hϖ : Irreducible ϖ) :
    Function.Injective (fun x : Fin r → K => ϖ • x) := by
  intro x y h
  funext i
  have := congrFun h i
  simp only [Pi.smul_apply, Algebra.smul_def] at this
  exact mul_left_cancel₀ (alg_ne_zero hϖ) this

theorem idx_eq_of_le {ϖ : O} (hϖ : Irreducible ϖ) {M L : Submodule O (Fin r → K)} (h : M ≤ L)
    (hi : M.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) : idx ϖ M = idx ϖ L := by
  set f : (Fin r → K) →ₗ[O] (Fin r → K) := ϖ • LinearMap.id with hf'
  have hinj : Function.Injective f.toAddMonoidHom := smul_injective hϖ
  have e : ∀ P : Submodule O (Fin r → K),
      (P.map f).toAddSubgroup = P.toAddSubgroup.map f.toAddMonoidHom := fun P => by
    ext x; simp [Submodule.mem_map]
  have hsub : ∀ P : Submodule O (Fin r → K), (P.map f).toAddSubgroup ≤ P.toAddSubgroup := by
    intro P x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact P.smul_mem ϖ hy
  have hBA : (M.map f).toAddSubgroup ≤ (L.map f).toAddSubgroup :=
    fun x hx => Submodule.map_mono h hx
  have hML : M.toAddSubgroup ≤ L.toAddSubgroup := h
  have e1 : (M.map f).toAddSubgroup.relIndex (L.map f).toAddSubgroup =
      M.toAddSubgroup.relIndex L.toAddSubgroup := by
    rw [e, e, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
  have h1 := AddSubgroup.relIndex_mul_relIndex _ _ _ hBA (hsub L)
  have h2 := AddSubgroup.relIndex_mul_relIndex _ _ _ (hsub M) hML
  rw [e1] at h1
  have h3 : M.toAddSubgroup.relIndex L.toAddSubgroup * idx ϖ L =
      idx ϖ M * M.toAddSubgroup.relIndex L.toAddSubgroup := by
    simp only [idx]; rw [h1, h2]
  rw [mul_comm] at h3
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) h3).symm

end GlobalTheory.HermNbr
end

open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

theorem mem_nb {cK : K ≃+* K} {J : Matrix (Fin r) (Fin r) K} {L : Submodule O (Fin r → K)}
    {v x : Fin r → K} : x ∈ nb cK J L v ↔ ∃ m ∈ perp cK J L v, ∃ a : O, x = m + a • v := by
  unfold nb
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨m, hm, z, hz, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨m, hm, a, rfl⟩
  · rintro ⟨m, hm, a, rfl⟩
    exact ⟨m, hm, a • v, Submodule.mem_span_singleton.2 ⟨a, rfl⟩, rfl⟩

theorem conj_mem_range (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) {y : K}
    (hy : y ∈ (algebraMap O K).range) : cK y ∈ (algebraMap O K).range := by
  obtain ⟨a, rfl⟩ := hy
  exact ⟨c a, (hcK a).symm⟩

theorem nb_int (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K}
    (hvv : hf cK J v v ∈ (algebraMap O K).range) {x y : Fin r → K}
    (hx : x ∈ nb cK J L v) (hy : y ∈ nb cK J L v) :
    hf cK J x y ∈ (algebraMap O K).range := by
  obtain ⟨m, hm, a, rfl⟩ := mem_nb.1 hx
  obtain ⟨m', hm', a', rfl⟩ := mem_nb.1 hy
  rw [mem_perp] at hm hm'
  have h1 : hf cK J m m' ∈ (algebraMap O K).range := (hSD m).1 hm.1 m' hm'.1
  have h2 : hf cK J m v ∈ (algebraMap O K).range := by
    rw [hf_conj cK hc2 J hJ]; exact conj_mem_range c cK hcK hm.2
  rw [hf_add_left, hf_add_right, hf_add_right, hf_algSmul_right, hf_algSmul_left,
    hf_algSmul_left, hf_algSmul_right, hcK]
  refine add_mem (add_mem h1 (mul_mem ⟨_, rfl⟩ h2)) (add_mem (mul_mem ⟨_, rfl⟩ hm'.2) ?_)
  exact mul_mem ⟨_, rfl⟩ (mul_mem ⟨_, rfl⟩ hvv)

theorem nb_sd (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K}
    (hstep : IsStep cK J ϖ L v) : IsSD cK J (nb cK J L v) := by
  obtain ⟨hv, hw, hvv⟩ := hstep
  intro x
  refine ⟨fun hx y hy => nb_int c cK hcK hc2 hJ hϖ hSD hvv hx hy, fun hx => ?_⟩
  obtain ⟨l0, hl0, hβ⟩ : ∃ l0 ∈ L, hf cK J v l0 ∉ (algebraMap O K).range := by
    by_contra hcon
    push_neg at hcon
    exact hv ((hSD v).2 hcon)
  have hβ' : algebraMap O K ϖ * hf cK J v l0 ∈ (algebraMap O K).range :=
    mul_pair_mem c cK hcK hϖ hSD hw hl0
  have hvnb : v ∈ nb cK J L v := mem_nb.2 ⟨0, (perp cK J L v).zero_mem, 1, by simp⟩
  have hperp_nb : ∀ m ∈ perp cK J L v, m ∈ nb cK J L v := fun m hm =>
    mem_nb.2 ⟨m, hm, 0, by simp⟩
  have hl0p : ϖ • l0 ∈ perp cK J L v := by
    refine mem_perp.2 ⟨L.smul_mem ϖ hl0, ?_⟩
    rw [hf_algSmul_right]; exact hβ'
  have hxl0 : algebraMap O K ϖ * hf cK J x l0 ∈ (algebraMap O K).range := by
    have := hx _ (hperp_nb _ hl0p)
    rwa [hf_algSmul_right] at this
  obtain ⟨e, he⟩ := exists_ratio hϖ hβ hβ' hxl0
  set b := c.symm e with hb
  have hcb : cK (algebraMap O K b) = algebraMap O K e := by rw [hcK, hb, RingEquiv.apply_symm_apply]
  set x' := x - b • v with hx'
  have hx'l0 : hf cK J x' l0 = 0 := by
    rw [hx', hf_sub_left, hf_algSmul_left, hcb, he, sub_self]
  have hx'm : ∀ m ∈ perp cK J L v, hf cK J x' m ∈ (algebraMap O K).range := by
    intro m hm
    rw [hx', hf_sub_left, hf_algSmul_left]
    exact sub_mem (hx m (hperp_nb m hm)) (mul_mem (conj_mem_range c cK hcK ⟨_, rfl⟩) (mem_perp.1 hm).2)
  have hx'L : x' ∈ L := by
    refine (hSD x').2 fun l hl => ?_
    obtain ⟨a, ha⟩ := exists_ratio hϖ hβ hβ' (mul_pair_mem c cK hcK hϖ hSD hw hl)
    have hm : l - a • l0 ∈ perp cK J L v := by
      refine mem_perp.2 ⟨L.sub_mem hl (L.smul_mem a hl0), ?_⟩
      rw [hf_sub_right, hf_algSmul_right, ha, sub_self]
      exact zero_mem _
    have : l = (l - a • l0) + a • l0 := by abel
    rw [this, hf_add_right, hf_algSmul_right, hx'l0, mul_zero, add_zero]
    exact hx'm _ hm
  have hx'p : x' ∈ perp cK J L v := by
    refine mem_perp.2 ⟨hx'L, ?_⟩
    rw [hf_conj cK hc2 J hJ]
    apply conj_mem_range c cK hcK
    rw [hx', hf_sub_left, hf_algSmul_left]
    exact sub_mem (hx v hvnb) (mul_mem (conj_mem_range c cK hcK ⟨_, rfl⟩) hvv)
  exact mem_nb.2 ⟨x', hx'p, b, by rw [hx']; abel⟩

theorem perp_eq_perp_nb (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ)
    {L : Submodule O (Fin r → K)} (hSD : IsSD cK J L) {v : Fin r → K}
    (hstep : IsStep cK J ϖ L v) {l0 : Fin r → K} (hl0 : l0 ∈ L)
    (hβ : hf cK J v l0 ∉ (algebraMap O K).range) :
    perp cK J L v = perp cK J (nb cK J L v) l0 := by
  have hSDn := nb_sd c cK hcK hc2 hJ hϖ hSD hstep
  obtain ⟨hv, hw, hvv⟩ := hstep
  have hvnb : v ∈ nb cK J L v := mem_nb.2 ⟨0, (perp cK J L v).zero_mem, 1, by simp⟩
  ext x
  constructor
  · intro hx
    refine mem_perp.2 ⟨mem_nb.2 ⟨x, hx, 0, by simp⟩, (hSD l0).1 hl0 x (mem_perp.1 hx).1⟩
  · intro hx
    obtain ⟨hxn, hxl⟩ := mem_perp.1 hx
    obtain ⟨m, hm, a, rfl⟩ := mem_nb.1 hxn
    have hm' := mem_perp.1 hm
    have h1 : algebraMap O K a * hf cK J l0 v ∈ (algebraMap O K).range := by
      rw [hf_add_right, hf_algSmul_right] at hxl
      have := sub_mem hxl ((hSD l0).1 hl0 m hm'.1)
      simpa using this
    have hγ : hf cK J l0 v ∉ (algebraMap O K).range := by
      intro h
      apply hβ
      rw [hf_conj cK hc2 J hJ l0 v]
      exact conj_mem_range c cK hcK h
    have hγ' : algebraMap O K ϖ * hf cK J l0 v ∈ (algebraMap O K).range := by
      rw [← hf_algSmul_right]; exact (hSD l0).1 hl0 _ hw
    obtain ⟨e, rfl⟩ := (ratio_mem_iff hϖ hγ hγ' a).1 h1
    refine mem_perp.2 ⟨?_, (hSDn v).1 hvnb _ hxn⟩
    rw [mul_comm ϖ e, mul_smul]
    exact L.add_mem hm'.1 (L.smul_mem e hw)

theorem good_nb (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ) [Finite (IsLocalRing.ResidueField O)] {N : ℕ}
    {L : Submodule O (Fin r → K)} (hL : Good cK J ϖ N L) {v : Fin r → K}
    (hstep : IsStep cK J ϖ L v) : Good cK J ϖ N (nb cK J L v) := by
  obtain ⟨hSD, habs, hidx⟩ := hL
  have hSDn := nb_sd c cK hcK hc2 hJ hϖ hSD hstep
  obtain ⟨hv, hw, hvv⟩ := hstep
  obtain ⟨l0, hl0, hβ⟩ : ∃ l0 ∈ L, hf cK J v l0 ∉ (algebraMap O K).range := by
    by_contra hcon
    push_neg at hcon
    exact hv ((hSD v).2 hcon)
  have hβ' : algebraMap O K ϖ * hf cK J v l0 ∈ (algebraMap O K).range :=
    mul_pair_mem c cK hcK hϖ hSD hw hl0
  have hQ : Nat.card (IsLocalRing.ResidueField O) ≠ 0 := Nat.card_pos.ne'
  have hpL : perp cK J L v ≤ L := fun x hx => (mem_perp.1 hx).1
  have hpn : perp cK J L v ≤ nb cK J L v := fun x hx => mem_nb.2 ⟨x, hx, 0, by simp⟩
  have i1 := perp_relIndex c cK hcK hϖ hSD hv hw
  have hl0n : l0 ∉ nb cK J L v := by
    intro h
    have hvnb : v ∈ nb cK J L v := mem_nb.2 ⟨0, (perp cK J L v).zero_mem, 1, by simp⟩
    exact hβ ((hSDn v).1 hvnb l0 h)
  have hwl0 : ϖ • l0 ∈ nb cK J L v := by
    refine hpn (mem_perp.2 ⟨L.smul_mem ϖ hl0, ?_⟩)
    rw [hf_algSmul_right]; exact hβ'
  have i2 := perp_relIndex c cK hcK hϖ hSDn hl0n hwl0
  rw [← perp_eq_perp_nb c cK hcK hc2 hJ hϖ hSD ⟨hv, hw, hvv⟩ hl0 hβ] at i2
  refine ⟨hSDn, ?_, ?_⟩
  · intro x
    obtain ⟨k, hk⟩ := habs x
    refine ⟨k + 1, hpn (mem_perp.2 ⟨?_, ?_⟩)⟩
    · rw [pow_succ', mul_smul]; exact L.smul_mem ϖ hk
    · rw [pow_succ', mul_smul, hf_algSmul_right]
      exact mul_pair_mem c cK hcK hϖ hSD hw hk
  · rw [← idx_eq_of_le hϖ hpn (by rw [i2]; exact hQ), idx_eq_of_le hϖ hpL (by rw [i1]; exact hQ),
      hidx]

end GlobalTheory.HermNbr
end

open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

theorem step_exists (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ) [Finite (IsLocalRing.ResidueField O)] {N : ℕ}
    {L Λ : Submodule O (Fin r → K)} (hL : Good cK J ϖ N L) (hΛ : Good cK J ϖ N Λ) (hne : L ≠ Λ)
    (hi : Λ.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
    ∃ L' ∈ Nbrs cK J ϖ L, Good cK J ϖ N L' ∧ Λ.toAddSubgroup.relIndex L'.toAddSubgroup ≠ 0 ∧
      Nat.card (IsLocalRing.ResidueField O) * Λ.toAddSubgroup.relIndex L'.toAddSubgroup ≤
        Λ.toAddSubgroup.relIndex L.toAddSubgroup := by
  classical
  have hnle : ¬ Λ ≤ L := by
    intro hle
    apply hne
    refine le_antisymm (fun x hx => (hΛ.1 x).2 fun y hy => (hL.1 x).1 hx y (hle hy)) hle
  obtain ⟨x, hxΛ, hxL⟩ := Set.not_subset.1 hnle
  have hex : ∃ k : ℕ, (ϖ ^ k) • x ∈ L := hL.2.1 x
  set k0 := Nat.find hex with hk0
  have hk0m : (ϖ ^ k0) • x ∈ L := Nat.find_spec hex
  have hk0pos : k0 ≠ 0 := by
    intro h0
    rw [h0, pow_zero, one_smul] at hk0m
    exact hxL hk0m
  set v := (ϖ ^ (k0 - 1)) • x with hvdef
  have hvΛ : v ∈ Λ := Λ.smul_mem _ hxΛ
  have hvL : v ∉ L := Nat.find_min hex (by omega : k0 - 1 < k0)
  have hwL : ϖ • v ∈ L := by
    rw [hvdef, smul_smul, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0pos)]
    exact hk0m
  have hvv := (hΛ.1 v).1 hvΛ v hvΛ
  have hstep : IsStep cK J ϖ L v := ⟨hvL, hwL, hvv⟩
  have hgood := good_nb c cK hcK hc2 hJ hϖ hL hstep
  refine ⟨nb cK J L v, ⟨v, hstep, rfl⟩, hgood, ?_⟩

  set Q := Nat.card (IsLocalRing.ResidueField O)
  have hQ := perp_relIndex c cK hcK hϖ hL.1 hvL hwL
  set Ag := Λ.toAddSubgroup
  set large₂ := L.toAddSubgroup
  set L'g := (nb cK J L v).toAddSubgroup
  set Mpg := (perp cK J L v).toAddSubgroup
  set Mg := large₂ ⊓ Ag
  set Ng := Mg ⊔ (Submodule.span O {v}).toAddSubgroup
  have hMMp : Mg ≤ Mpg := fun y hy => mem_perp.2 ⟨hy.1, (hΛ.1 v).1 hvΛ y hy.2⟩
  have hMpL : Mpg ≤ large₂ := fun y hy => (mem_perp.1 hy).1
  have hMN : Mg ≤ Ng := le_sup_left
  have hspanΛ : (Submodule.span O {v}).toAddSubgroup ≤ Ag := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    exact Λ.smul_mem a hvΛ
  have hNA : Ng ≤ Ag := sup_le (fun y hy => hy.2) hspanΛ
  have hL'eq : L'g = Mpg ⊔ Ng := by
    apply le_antisymm
    · intro y hy
      obtain ⟨m, hm, a, rfl⟩ := mem_nb.1 hy
      exact AddSubgroup.add_mem_sup hm
        (AddSubgroup.mem_sup_right (Submodule.mem_span_singleton.2 ⟨a, rfl⟩))
    · refine sup_le (fun y hy => mem_nb.2 ⟨y, hy, 0, by simp⟩) (sup_le ?_ ?_)
      · intro y hy
        exact mem_nb.2 ⟨y, hMMp hy, 0, by simp⟩
      · intro y hy
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
        exact mem_nb.2 ⟨0, (perp cK J L v).zero_mem, a, by simp⟩
  have d1 : Ag.relIndex L'g ∣ Ng.relIndex L'g := AddSubgroup.relIndex_dvd_of_le_left (L := L'g) hNA
  have e1 : Ng.relIndex L'g = Ng.relIndex Mpg := by
    rw [hL'eq]; exact AddSubgroup.relIndex_sup_right (H := Mpg) (K := Ng)
  have d2 : Ng.relIndex Mpg ∣ Mg.relIndex Mpg := AddSubgroup.relIndex_dvd_of_le_left (L := Mpg) hMN
  have e2 : Ag.relIndex large₂ = Mg.relIndex Mpg * Q := by
    rw [← AddSubgroup.inf_relIndex_right, inf_comm, show Q = Mpg.relIndex large₂ from hQ.symm]
    exact (AddSubgroup.relIndex_mul_relIndex _ _ _ hMMp hMpL).symm
  rw [e1] at d1
  have d := dvd_trans d1 d2
  have hm0 : Mg.relIndex Mpg ≠ 0 := by
    intro h0; rw [e2, h0, zero_mul] at hi; exact hi rfl
  have ha0 : Ag.relIndex L'g ≠ 0 := by
    intro h0; rw [h0, zero_dvd_iff] at d; exact hm0 d
  refine ⟨ha0, ?_⟩
  rw [e2, mul_comm (Mg.relIndex Mpg)]
  exact Nat.mul_le_mul_left _ (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) d)

theorem unit_mul_mem_iff (u : Oˣ) (y : K) :
    algebraMap O K u * y ∈ (algebraMap O K).range ↔ y ∈ (algebraMap O K).range := by
  constructor
  · intro h
    have e1 : algebraMap O K ((u⁻¹ : Oˣ) : O) * algebraMap O K (u : O) = 1 := by
      rw [← map_mul]; simp
    have : y = algebraMap O K ((u⁻¹ : Oˣ) : O) * (algebraMap O K u * y) := by
      rw [← mul_assoc, e1, one_mul]
    rw [this]; exact mul_mem ⟨_, rfl⟩ h
  · intro h; exact mul_mem ⟨_, rfl⟩ h

theorem perp_congr {cK : K ≃+* K} {J : Matrix (Fin r) (Fin r) K} {L : Submodule O (Fin r → K)}
    (hSD : IsSD cK J L) {v v0 : Fin r → K} (h : v - v0 ∈ L) :
    perp cK J L v = perp cK J L v0 := by
  ext x
  rw [mem_perp, mem_perp]
  constructor
  · rintro ⟨hx, h1⟩
    refine ⟨hx, ?_⟩
    have h2 := (hSD _).1 h x hx
    rw [hf_sub_left] at h2
    have := sub_mem h1 h2
    simpa using this
  · rintro ⟨hx, h1⟩
    refine ⟨hx, ?_⟩
    have h2 := (hSD _).1 h x hx
    rw [hf_sub_left] at h2
    have := add_mem h1 h2
    simpa using this

theorem nb_congr {cK : K ≃+* K} {J : Matrix (Fin r) (Fin r) K} {L : Submodule O (Fin r → K)}
    {v1 v2 : Fin r → K} (hp : perp cK J L v1 = perp cK J L v2) (h : v2 - v1 ∈ perp cK J L v1) :
    nb cK J L v1 = nb cK J L v2 := by
  ext x
  rw [mem_nb, mem_nb]
  constructor
  · rintro ⟨m, hm, a, rfl⟩
    refine ⟨m - a • (v2 - v1), hp ▸ sub_mem hm (Submodule.smul_mem _ a h), a, ?_⟩
    rw [smul_sub]; abel
  · rintro ⟨m, hm, a, rfl⟩
    refine ⟨m + a • (v2 - v1), add_mem (hp ▸ hm) (Submodule.smul_mem _ a h), a, ?_⟩
    rw [smul_sub]; abel

theorem isStep_unit_smul (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x))
    {J : Matrix (Fin r) (Fin r) K} {ϖ : O} {L : Submodule O (Fin r → K)} {v : Fin r → K}
    (hs : IsStep cK J ϖ L v) {b : O} (hb : IsUnit b) : IsStep cK J ϖ L (b • v) := by
  obtain ⟨hv, hw, hvv⟩ := hs
  refine ⟨fun h => hv ?_, ?_, ?_⟩
  · obtain ⟨u, rfl⟩ := hb
    have := L.smul_mem ((u⁻¹ : Oˣ) : O) h
    rwa [smul_smul, Units.inv_mul, one_smul] at this
  · rw [smul_comm]; exact L.smul_mem b hw
  · rw [hf_algSmul_left, hf_algSmul_right, hcK]
    exact mul_mem ⟨_, rfl⟩ (mul_mem ⟨_, rfl⟩ hvv)

theorem nb_unit_smul (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x))
    {J : Matrix (Fin r) (Fin r) K} {L : Submodule O (Fin r → K)} {v : Fin r → K}
    {b : O} (hb : IsUnit b) : nb cK J L (b • v) = nb cK J L v := by
  have hp : perp cK J L (b • v) = perp cK J L v := by
    ext x
    rw [mem_perp, mem_perp, hf_algSmul_left, hcK]
    obtain ⟨u, hu⟩ := hb.map c
    rw [← hu, unit_mul_mem_iff]
  unfold nb
  rw [hp, Submodule.span_singleton_smul_eq hb]

theorem sub_mem_of_mk_eq {ϖ : O} (hϖ : Irreducible ϖ) {L : Submodule O (Fin r → K)}
    {v v0 : Fin r → K} (hw : ϖ • v ∈ L) (hw0 : ϖ • v0 ∈ L)
    (h : (QuotientAddGroup.mk (⟨ϖ • v, hw⟩ : L.toAddSubgroup) : L.toAddSubgroup ⧸
      (L.map (ϖ • (LinearMap.id : (Fin r → K) →ₗ[O] (Fin r → K)))).toAddSubgroup.addSubgroupOf
        L.toAddSubgroup) = QuotientAddGroup.mk (⟨ϖ • v0, hw0⟩ : L.toAddSubgroup)) :
    v - v0 ∈ L := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
  obtain ⟨y, hy, hy'⟩ := h
  have e : ϖ • y = ϖ • (v0 - v) := by
    rw [smul_sub]
    simpa [neg_add_eq_sub] using hy'
  have := smul_injective (K := K) (r := r) hϖ e
  rw [show v - v0 = -(v0 - v) by abel, ← this]
  exact L.neg_mem hy

theorem card_nbrs (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    {J : Matrix (Fin r) (Fin r) K} (hJ : J.transpose.map cK = J) {ϖ : O} (hϖ : Irreducible ϖ) [Finite (IsLocalRing.ResidueField O)] {N : ℕ}
    {L : Submodule O (Fin r → K)} (hL : Good cK J ϖ N L) (hN : N ≠ 0)
    (t : Finset (Submodule O (Fin r → K))) (ht : (t : Set _) ⊆ Nbrs cK J ϖ L) :
    t.card * (Nat.card (IsLocalRing.ResidueField O) - 1) ≤
      N * Nat.card (IsLocalRing.ResidueField O) := by
  classical
  letI := Fintype.ofFinite (IsLocalRing.ResidueField O)
  set Wg := (L.map (ϖ • (LinearMap.id : (Fin r → K) →ₗ[O] (Fin r → K)))).toAddSubgroup.addSubgroupOf
    L.toAddSubgroup with hWg
  have hcardW : Nat.card (L.toAddSubgroup ⧸ Wg) = N := hL.2.2
  haveI : Finite (L.toAddSubgroup ⧸ Wg) := Nat.finite_of_card_ne_zero (hcardW ▸ hN)
  letI := Fintype.ofFinite (L.toAddSubgroup ⧸ Wg)
  let rel : Submodule O (Fin r → K) → (L.toAddSubgroup ⧸ Wg) → Prop := fun L' u =>
    ∃ v, IsStep cK J ϖ L v ∧ L' = nb cK J L v ∧ ∃ hw : ϖ • v ∈ L,
      (QuotientAddGroup.mk (⟨ϖ • v, hw⟩ : L.toAddSubgroup) : L.toAddSubgroup ⧸ Wg) = u
  choose lift hlift using IsLocalRing.residue_surjective (R := O)
  have hunit : ∀ a : (IsLocalRing.ResidueField O)ˣ, IsUnit (lift a) := by
    intro a
    by_contra h
    apply a.ne_zero
    rw [← hlift (a : IsLocalRing.ResidueField O)]
    exact (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hm : ∀ L' ∈ t, Nat.card (IsLocalRing.ResidueField O) - 1 ≤
      (Finset.univ.filter (fun u => rel L' u)).card := by
    intro L' hL'
    obtain ⟨v, hs, rfl⟩ := ht hL'
    have hmem : ∀ a : (IsLocalRing.ResidueField O)ˣ, ϖ • (lift a • v) ∈ L := fun a => by
      rw [smul_comm]; exact L.smul_mem _ hs.2.1
    let f : (IsLocalRing.ResidueField O)ˣ → L.toAddSubgroup ⧸ Wg := fun a =>
      QuotientAddGroup.mk (⟨ϖ • (lift a • v), hmem a⟩ : L.toAddSubgroup)
    have hcu : Nat.card (IsLocalRing.ResidueField O) - 1 =
        (Finset.univ : Finset (IsLocalRing.ResidueField O)ˣ).card := by
      rw [Finset.card_univ, Fintype.card_units, Nat.card_eq_fintype_card]
    rw [hcu]
    refine Finset.card_le_card_of_injOn f (fun a _ => ?_) (fun a _ a' _ hf => ?_)
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, lift a • v,
        isStep_unit_smul c cK hcK hs (hunit a), (nb_unit_smul c cK hcK (hunit a)).symm,
        hmem a, rfl⟩
    · have h1 := sub_mem_of_mk_eq hϖ (hmem a) (hmem a') hf
      rw [← sub_smul] at h1
      by_contra hne
      have hne' : IsLocalRing.residue O (lift a - lift a') ≠ 0 := by
        rw [map_sub, hlift, hlift, sub_ne_zero]
        exact fun h => hne (Units.ext h)
      have hu : IsUnit (lift a - lift a') := by
        by_contra h
        exact hne' ((IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 h))
      obtain ⟨u, hu⟩ := hu
      apply hs.1
      have := L.smul_mem ((u⁻¹ : Oˣ) : O) h1
      rwa [← hu, smul_smul, Units.inv_mul, one_smul] at this
  have hn : ∀ u ∈ (Finset.univ : Finset (L.toAddSubgroup ⧸ Wg)),
      (t.filter (fun L' => rel L' u)).card ≤ Nat.card (IsLocalRing.ResidueField O) := by
    intro u _
    by_cases hE : t.filter (fun L' => rel L' u) = ∅
    · rw [hE]; simp
    obtain ⟨L0, hL0⟩ := Finset.nonempty_iff_ne_empty.2 hE
    obtain ⟨v0, hs0, -, hw0, hu0⟩ := (Finset.mem_filter.1 hL0).2
    set Wq := (perp cK J L v0).toAddSubgroup.addSubgroupOf L.toAddSubgroup with hWq
    have hcq : Nat.card (L.toAddSubgroup ⧸ Wq) = Nat.card (IsLocalRing.ResidueField O) :=
      perp_relIndex c cK hcK hϖ hL.1 hs0.1 hs0.2.1
    haveI : Finite (L.toAddSubgroup ⧸ Wq) := Nat.finite_of_card_ne_zero (by rw [hcq]; exact Nat.card_pos.ne')
    letI := Fintype.ofFinite (L.toAddSubgroup ⧸ Wq)
    have hch : ∀ L' ∈ t.filter (fun L' => rel L' u), ∃ z : L.toAddSubgroup ⧸ Wq, ∃ v,
        IsStep cK J ϖ L v ∧ L' = nb cK J L v ∧ ∃ h : v - v0 ∈ L,
          z = QuotientAddGroup.mk (⟨v - v0, h⟩ : L.toAddSubgroup) := by
      intro L' hL'
      obtain ⟨v, hs, hLv, hw, hu⟩ := (Finset.mem_filter.1 hL').2
      have h := sub_mem_of_mk_eq hϖ hw hw0 (hu.trans hu0.symm)
      exact ⟨_, v, hs, hLv, h, rfl⟩
    choose! g hg using hch
    have hinj : Set.InjOn g ↑(t.filter (fun L' => rel L' u)) := by
      intro L1 h1 L2 h2 he
      obtain ⟨v1, hs1, e1, hd1, z1⟩ := hg L1 h1
      obtain ⟨v2, hs2, e2, hd2, z2⟩ := hg L2 h2
      rw [z1, z2, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at he
      have hd : v2 - v1 ∈ perp cK J L v0 := by
        have : v2 - v1 = -(v1 - v0) + (v2 - v0) := by abel
        rw [this]; simpa using he
      have p1 := perp_congr hL.1 hd1
      have p2 := perp_congr hL.1 hd2
      rw [e1, e2]
      exact nb_congr (p1.trans p2.symm) (p1 ▸ hd)
    have hle := Finset.card_le_card_of_injOn (s := t.filter (fun L' => rel L' u))
      (t := (Finset.univ : Finset (L.toAddSubgroup ⧸ Wq))) g (fun _ _ => Finset.mem_univ _) hinj
    rw [Finset.card_univ, Fintype.card_eq_nat_card, hcq] at hle
    exact hle
  have key := Finset.card_mul_le_card_mul rel (s := t) (t := Finset.univ) hm hn
  rw [Finset.card_univ, Fintype.card_eq_nat_card, hcardW] at key
  exact key

end GlobalTheory.HermNbr
