module

public import ReciprocityTheory.DualLattices.TowerZeroSurjective

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.AvgFZero
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Lift1

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

variable {G : Type} [CommGroup G] [Fintype G] (β : G → O)

def avgF (H : HodgeTateDatum p g v R O σ cp) (U : UnramData p g v R O σ cp H) (i : Fin U.m) (c₀ : R)
    (F : Nb p g → C) (y : Nb p g) : C :=
  ∑ γ, algebraMap R C (c₀ * U.sg i (β γ⁻¹)) * F (nbAct H (β γ) y)

lemma avgF_mem {H : HodgeTateDatum p g v R O σ cp} (U : UnramData p g v R O σ cp H) (i : Fin U.m) (c₀ : R)
    {F : Nb p g → C} (hF : F ∈ H.AA.carrier) : avgF β H U i c₀ F ∈ H.AA.carrier := by
  have hsum : avgF β H U i c₀ F = ∑ γ, (c₀ * U.sg i (β γ⁻¹)) • (fun y => F (nbAct H (β γ) y)) := by
    funext y
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply]
    simp only [avgF, Algebra.smul_def]
  rw [hsum]
  exact Submodule.sum_mem _ fun γ _ => Submodule.smul_mem _ _ (comp_mem H _ hF)

lemma nbAct_mul {H : HodgeTateDatum p g v R O σ cp}
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (γ δ : G) (y : Nb p g) :
    nbAct H (β (γ * δ)) y = nbAct H (β γ) (nbAct H (β δ) y) := by
  rw [nbAct, nbAct, nbAct, hmul, Matrix.map_mul, Matrix.mulVec_mulVec]

private lemma smul_cancel_lemma (hS : HodgeTateSetting p v R O σ cp) {M : Matrix (Ix g) (Ix g) R}
    (hM : M ≠ 0) (s : R) (hs : s • M = 0) : s = 0 := by
  have hnz : NoZeroDivisors R := hS.integers.hom_inj.noZeroDivisors _ (map_zero _) (map_mul _)
  by_contra hne
  apply hM
  ext k l
  have h := congrFun (congrFun hs k) l
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' hne
  · simpa using h'

private lemma sg_mul_lemma_2 (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ'))
    {i : Fin U.m} (hi : U.εT i ≠ 0) (γ γ' : G) :
    U.sg i (β (γ * γ')) = U.sg i (β γ) * U.sg i (β γ') := by
  apply sub_eq_zero.mp
  apply smul_cancel_lemma hS hi
  have e1 := U.εT_eig (β (γ * γ')) i
  rw [hmul, Matrix.map_mul, Matrix.mul_assoc, U.εT_eig, Matrix.mul_smul, U.εT_eig, smul_smul] at e1
  rw [sub_smul, ← e1, mul_comm, sub_self]

private lemma sg_one_lemma_3 (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H) (h1 : H.ρ (β 1) = 1)
    {i : Fin U.m} (hi : U.εT i ≠ 0) : U.sg i (β 1) = 1 := by
  apply sub_eq_zero.mp
  apply smul_cancel_lemma hS hi
  have e1 := U.εT_eig (β 1) i
  rw [h1, Matrix.map_one (algebraMap ℤ_[p] R) (map_zero _) (map_one _), Matrix.one_mul] at e1
  rw [sub_smul, ← e1, one_smul, sub_self]

private lemma sg_inv_lemma_4 (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    {i : Fin U.m} (hi : U.εT i ≠ 0) (γ : G) : U.sg i (β γ) * U.sg i (β γ⁻¹) = 1 := by
  rw [← sg_mul_lemma_2 β hS U hmul hi, mul_inv_cancel, sg_one_lemma_3 β hS U h1 hi]

lemma avgF_eig (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    {i : Fin U.m} (hi : U.εT i ≠ 0) (c₀ : R) (F : Nb p g → C) (δ : G) (y : Nb p g) :
    avgF β H U i c₀ F (nbAct H (β δ) y) =
      algebraMap R C (U.sg i (β δ)) * avgF β H U i c₀ F y := by
  have hx : ∀ γ, F (nbAct H (β γ) (nbAct H (β δ) y)) = F (nbAct H (β (γ * δ)) y) := fun γ => by
    rw [nbAct_mul β hmul]
  simp only [avgF, hx]
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight δ) _ _ fun γ => ?_
  simp only [Equiv.coe_mulRight]
  rw [_root_.mul_inv_rev, sg_mul_lemma_2 β hS U hmul hi δ⁻¹ γ⁻¹, ← mul_assoc, ← map_mul]
  congr 2
  linear_combination (-(c₀ * U.sg i (β γ⁻¹))) * sg_inv_lemma_4 β hS U hmul h1 hi δ

lemma avgF_zero (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    {i : Fin U.m} (hi : U.εT i ≠ 0)
    (hnt : ∃ γ, v (algebraMap R C (U.sg i (β γ) - 1)) = 1) (c₀ : R) (F : Nb p g → C) :
    avgF β H U i c₀ F 0 = 0 := by
  obtain ⟨δ, hδ⟩ := hnt
  have he := avgF_eig β hS U hmul h1 hi c₀ F δ 0
  rw [show nbAct H (β δ) 0 = 0 from Matrix.mulVec_zero _] at he
  have hne : algebraMap R C (U.sg i (β δ)) - 1 ≠ 0 := by
    intro h0
    rw [map_sub, map_one, h0, map_zero] at hδ
    exact zero_ne_one hδ
  have hm : (algebraMap R C (U.sg i (β δ)) - 1) * avgF β H U i c₀ F 0 = 0 := by
    rw [sub_mul, ← he, one_mul, sub_self]
  exact (mul_eq_zero.mp hm).resolve_left hne

private lemma orth_lemma_5 (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    (hsep : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1)
    {i k : Fin U.m} (hi : U.εT i ≠ 0) (hk : U.εT k ≠ 0) (hik : i ≠ k) :
    ∑ γ, U.sg i (β γ⁻¹) * U.sg k (β γ) = 0 := by
  have hnz : NoZeroDivisors R := hS.integers.hom_inj.noZeroDivisors _ (map_zero _) (map_mul _)
  obtain ⟨δ, hδ⟩ := hsep i k hi hk hik
  have hne : U.sg i (β δ) - U.sg k (β δ) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hδ
    exact zero_ne_one hδ
  have hA := sg_inv_lemma_4 β hS U hmul h1 hi δ
  have hB := sg_inv_lemma_4 β hS U hmul h1 hk δ
  set S := ∑ γ, U.sg i (β γ⁻¹) * U.sg k (β γ) with hSdef
  have hshift : S = U.sg i (β δ⁻¹) * U.sg k (β δ) * S := by
    rw [hSdef, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft δ⁻¹) _ _ fun γ => ?_
    simp only [Equiv.coe_mulLeft, _root_.mul_inv_rev, inv_inv, sg_mul_lemma_2 β hS U hmul hi,
      sg_mul_lemma_2 β hS U hmul hk]
    linear_combination (-(U.sg i (β γ⁻¹) * U.sg k (β γ))) * hA +
      (-(U.sg i (β γ⁻¹) * U.sg k (β γ) * (U.sg i (β δ) * U.sg i (β δ⁻¹)))) * hB
  have hm : (U.sg i (β δ) - U.sg k (β δ)) * S = 0 := by
    linear_combination (U.sg i (β δ)) * hshift + (U.sg k (β δ) * S) * hA
  exact (mul_eq_zero.mp hm).resolve_left hne

private lemma proj_lemma_6 (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    (hsep : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1)
    (hcardG : IsUnit (Fintype.card G : R)) {i : Fin U.m} (hi : U.εT i ≠ 0) :
    ∑ γ, (((hcardG.unit⁻¹ : Rˣ) : R) * U.sg i (β γ⁻¹)) • (H.ρ (β γ)).map (algebraMap ℤ_[p] R) =
      U.εT i := by
  have hA : ∀ γ, (H.ρ (β γ)).map (algebraMap ℤ_[p] R) = ∑ j, U.sg j (β γ) • U.εT j := by
    intro γ
    have h := congrArg (fun M => (H.ρ (β γ)).map (algebraMap ℤ_[p] R) * M) U.εT_sum
    simp only [Matrix.mul_one, Matrix.mul_sum] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => U.εT_eig _ j
  simp_rw [hA, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, Finset.sum_eq_single i]
  · rw [← Finset.sum_smul]
    have hc : ∀ γ, U.sg i (β γ⁻¹) * U.sg i (β γ) = 1 := fun γ => by
      rw [mul_comm]
      exact sg_inv_lemma_4 β hS U hmul h1 hi γ
    have hsum : ∑ γ, ((hcardG.unit⁻¹ : Rˣ) : R) * U.sg i (β γ⁻¹) * U.sg i (β γ) = 1 := by
      simp_rw [mul_assoc, ← Finset.mul_sum, hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one]
      exact hcardG.val_inv_mul
    rw [hsum, one_smul]
  · intro j _ hji
    by_cases hj : U.εT j = 0
    · simp [hj]
    · rw [← Finset.sum_smul]
      have hsum : ∑ γ, ((hcardG.unit⁻¹ : Rˣ) : R) * U.sg i (β γ⁻¹) * U.sg j (β γ) = 0 := by
        simp_rw [mul_assoc, ← Finset.mul_sum]
        rw [orth_lemma_5 β hS U hmul h1 hsep hi hj (Ne.symm hji), mul_zero]
      rw [hsum, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma avgF_cong (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    (hsep : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1)
    (hcardG : IsUnit (Fintype.card G : R)) {i : Fin U.m} (hi : U.εT i ≠ 0) (Lr : Ix g → R)
    (F : Nb p g → C) (hF : ∀ t : TT p g, ∃ r : R,
      algebraMap R C (Lr ⬝ᵥ (algebraMap ℤ_[p] R ∘ t)) - F (red p g t) = algebraMap R C (p * r))
    (t : TT p g) : ∃ r : R, avgF β H U i (hcardG.unit⁻¹ : Rˣ) F (red p g t) -
      algebraMap R C ((Lr ᵥ* U.εT i) ⬝ᵥ (algebraMap ℤ_[p] R ∘ t)) = algebraMap R C (p * r) := by
  choose r hr using hF
  set c : R := ((hcardG.unit⁻¹ : Rˣ) : R) with hc
  set T : Ix g → R := algebraMap ℤ_[p] R ∘ t with hT
  have hF' : ∀ γ, F (nbAct H (β γ) (red p g t)) =
      algebraMap R C ((Lr ᵥ* (H.ρ (β γ)).map (algebraMap ℤ_[p] R)) ⬝ᵥ T) -
        algebraMap R C (p * r (H.ρ (β γ) *ᵥ t)) := by
    intro γ
    have h2 : (algebraMap ℤ_[p] R ∘ (H.ρ (β γ) *ᵥ t)) =
        (H.ρ (β γ)).map (algebraMap ℤ_[p] R) *ᵥ T := by
      funext k
      exact RingHom.map_mulVec _ _ _ k
    rw [← red_mulVec, ← Matrix.dotProduct_mulVec, ← h2]
    linear_combination -(hr (H.ρ (β γ) *ᵥ t))
  let L : Matrix (Ix g) (Ix g) R →ₗ[R] R :=
    { toFun := fun M => (Lr ᵥ* M) ⬝ᵥ T
      map_add' := fun M N => by simp only [Matrix.vecMul_add, add_dotProduct]
      map_smul' := fun a M => by simp only [Matrix.vecMul_smul, smul_dotProduct, RingHom.id_apply] }
  have hLε : (Lr ᵥ* U.εT i) ⬝ᵥ T =
      ∑ γ, (c * U.sg i (β γ⁻¹)) * ((Lr ᵥ* (H.ρ (β γ)).map (algebraMap ℤ_[p] R)) ⬝ᵥ T) := by
    have h := congrArg L (proj_lemma_6 β hS U hmul h1 hsep hcardG hi)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    exact h.symm
  refine ⟨-(∑ γ, c * U.sg i (β γ⁻¹) * r (H.ρ (β γ) *ᵥ t)), ?_⟩
  show ∑ γ, algebraMap R C (c * U.sg i (β γ⁻¹)) * F (nbAct H (β γ) (red p g t)) - _ = _
  simp only [hF']
  rw [hLε]
  have hmap : ∑ γ, algebraMap R C (c * U.sg i (β γ⁻¹)) *
      (algebraMap R C ((Lr ᵥ* (H.ρ (β γ)).map (algebraMap ℤ_[p] R)) ⬝ᵥ T) -
        algebraMap R C (p * r (H.ρ (β γ) *ᵥ t))) =
      algebraMap R C (∑ γ, c * U.sg i (β γ⁻¹) *
        ((Lr ᵥ* (H.ρ (β γ)).map (algebraMap ℤ_[p] R)) ⬝ᵥ T - p * r (H.ρ (β γ) *ᵥ t))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_sub]
  rw [hmap, ← map_sub]
  congr 1
  have e : ∑ γ, c * U.sg i (β γ⁻¹) * (p * r (H.ρ (β γ) *ᵥ t)) =
      (p : R) * ∑ γ, c * U.sg i (β γ⁻¹) * r (H.ρ (β γ) *ᵥ t) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [e]
  ring

lemma lift_one (hS : HodgeTateSetting p v R O σ cp) (hp2 : p ≠ 2) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    (hsep : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1)
    (hcardG : IsUnit (Fintype.card G : R)) {i : Fin U.m} (hi : U.εT i ≠ 0)
    (hnt : ∃ γ, v (algebraMap R C (U.sg i (β γ) - 1)) = 1) (e : R) (lam : Ix g → R)
    (hdiv : ∃ c, cp = e * c) (wH wB : Fin g → R)
    (hrow : (wH ᵥ* H.Ht + wB ᵥ* H.Bt) ᵥ* U.εT i = e • lam) :
    ∃ u : Nb p g → C, (∀ y, v (u y) ≤ 1) ∧
      (∀ y, v (u y - algebraMap R C (∑ k, lam k * ((y k).val : R))) < 1) ∧
      (fun y => algebraMap R C e * u y) ∈ augIdeal H.AA.carrier ∧
      (∀ δ t, u (red p g (H.ρ (β δ) *ᵥ t)) = algebraMap R C (U.sg i (β δ)) * u (red p g t)) := by
  classical
  obtain ⟨c', hc'⟩ := hdiv
  choose fH hfH hrH using fun k => (H.h4 k).1
  choose fB hfB hrB using fun k => (H.h4 k).2
  choose rH hrH' using hrH
  choose rB hrB' using hrB
  obtain ⟨F, hFdef⟩ : ∃ F : Nb p g → C, F = ∑ k, wH k • fH k + ∑ k, wB k • fB k := ⟨_, rfl⟩
  have hFmem : F ∈ H.AA.carrier := by
    rw [hFdef]
    exact H.AA.carrier.add_mem (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hfH k))
      (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hfB k))
  have hFcong : ∀ t : TT p g, ∃ r : R,
      algebraMap R C ((wH ᵥ* H.Ht + wB ᵥ* H.Bt) ⬝ᵥ (algebraMap ℤ_[p] R ∘ t)) - F (red p g t) =
        algebraMap R C (p * r) := by
    intro t
    refine ⟨∑ k, wH k * rH k t + ∑ k, wB k * rB k t, ?_⟩
    have hFt : F (red p g t) = ∑ k, algebraMap R C (wH k) * fH k (red p g t) +
        ∑ k, algebraMap R C (wB k) * fB k (red p g t) := by
      rw [hFdef, Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
      simp only [Pi.smul_apply]
      simp only [Algebra.smul_def]
    have hfH'' : ∀ k, fH k (red p g t) = algebraMap R C ((H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) -
        algebraMap R C (p * rH k t) := fun k => by linear_combination -(hrH' k t)
    have hfB'' : ∀ k, fB k (red p g t) = algebraMap R C ((H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) -
        algebraMap R C (p * rB k t) := fun k => by linear_combination -(hrB' k t)
    have hLT : (wH ᵥ* H.Ht + wB ᵥ* H.Bt) ⬝ᵥ (algebraMap ℤ_[p] R ∘ t) =
        ∑ k, wH k * (H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k +
          ∑ k, wB k * (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k := by
      rw [add_dotProduct, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec]
      rfl
    rw [hFt, hLT]
    simp only [hfH'', hfB'']
    have hmap : (∑ k, algebraMap R C (wH k) * (algebraMap R C ((H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) -
          algebraMap R C (p * rH k t)) +
        ∑ k, algebraMap R C (wB k) * (algebraMap R C ((H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) -
          algebraMap R C (p * rB k t))) =
        algebraMap R C (∑ k, wH k * ((H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k - p * rH k t) +
          ∑ k, wB k * ((H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k - p * rB k t)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_mul, map_sub]
    rw [hmap, ← map_sub]
    congr 1
    have e1 : ∑ k, wH k * (p * rH k t) = (p : R) * ∑ k, wH k * rH k t := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have e2 : ∑ k, wB k * (p * rB k t) = (p : R) * ∑ k, wB k * rB k t := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [e1, e2]
    ring
  have hAmem : avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F ∈ H.AA.carrier :=
    avgF_mem β U i _ hFmem
  have hA0 : avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F 0 = 0 :=
    avgF_zero β hS U hmul h1 hi hnt _ F
  have hAeig := avgF_eig β hS U hmul h1 hi ((hcardG.unit⁻¹ : Rˣ) : R) F
  have hAcong := avgF_cong β hS U hmul h1 hsep hcardG hi (wH ᵥ* H.Ht + wB ᵥ* H.Bt) F hFcong
  have hp2' : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hvcp : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    apply hS.p_ne
    rw [← hS.cp_val, h0, zero_pow (by omega)]
  have hve : v (algebraMap R C cp) ≤ v (algebraMap R C e) := by
    rw [hc', map_mul, map_mul]
    exact mul_le_of_le_one_right zero_le' (hS.integers.map_le_one c')
  have he0 : algebraMap R C e ≠ 0 := by
    intro h0
    have h := hve
    rw [h0, map_zero] at h
    exact hvcp (le_antisymm h zero_le')
  have hcp1 : v (algebraMap R C cp) < 1 := by
    rcases (hS.integers.map_le_one cp).lt_or_eq with h | h
    · exact h
    · exfalso
      have h' := hS.p_lt
      rw [← hS.cp_val, h, one_pow] at h'
      exact lt_irrefl _ h'
  have hpe : v (algebraMap R C (p : R)) < v (algebraMap R C e) := by
    rw [← hS.cp_val]
    have hp3 : 2 ≤ p - 1 := by omega
    calc v (algebraMap R C cp) ^ (p - 1) ≤ v (algebraMap R C cp) ^ 2 :=
          pow_le_pow_of_le_one zero_le' hcp1.le hp3
      _ < v (algebraMap R C cp) := by
          rw [sq]
          exact mul_lt_of_lt_one_right (pos_iff_ne_zero.mpr hvcp) hcp1
      _ ≤ _ := hve
  have hsmall : ∀ r : R, v (algebraMap R C (p * r) / algebraMap R C e) < 1 := by
    intro r
    have hve0 : 0 < v (algebraMap R C e) := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr he0)
    rw [map_div₀, div_lt_one hve0, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le' (hS.integers.map_le_one r)) hpe
  have hrep : ∀ y : Nb p g, ∃ r : R,
      avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F y / algebraMap R C e =
        algebraMap R C (∑ k, lam k * ((y k).val : R)) + algebraMap R C (p * r) / algebraMap R C e := by
    intro y
    obtain ⟨t, ht⟩ : ∃ t : TT p g, t = fun k => (((y k).val : ℕ) : ℤ_[p]) := ⟨_, rfl⟩
    have hy : red p g t = y := by
      funext k
      simp [red, ht, map_natCast, ZMod.natCast_zmod_val]
    have hT : (algebraMap ℤ_[p] R ∘ t) = fun k => ((y k).val : R) := by
      funext k
      rw [ht]
      simp only [Function.comp_apply]
      exact map_natCast _ _
    obtain ⟨r, hr⟩ := hAcong t
    refine ⟨r, ?_⟩
    have hdot : lam ⬝ᵥ (fun k => ((y k).val : R)) = ∑ k, lam k * ((y k).val : R) := rfl
    rw [hy, hrow, hT, smul_dotProduct, smul_eq_mul, hdot] at hr
    have hAy : avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F y =
        algebraMap R C e * algebraMap R C (∑ k, lam k * ((y k).val : R)) + algebraMap R C (p * r) := by
      rw [← map_mul]
      linear_combination hr
    rw [hAy, add_div, mul_div_cancel_left₀ _ he0]
  refine ⟨fun y => avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F y / algebraMap R C e, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨r, hr⟩ := hrep y
    dsimp only
    rw [hr]
    exact le_trans (Valuation.map_add v _ _) (max_le (hS.integers.map_le_one _) (hsmall r).le)
  · intro y
    obtain ⟨r, hr⟩ := hrep y
    dsimp only
    rw [hr, add_sub_cancel_left]
    exact hsmall r
  · have hmemA : avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F ∈ augIdeal H.AA.carrier :=
      Submodule.mem_inf.mpr ⟨hAmem, LinearMap.mem_ker.mpr hA0⟩
    convert hmemA using 1
    funext y
    rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ he0
  · intro δ t
    dsimp only
    rw [red_mulVec, hAeig δ (red p g t), mul_div_assoc]

end Lift1

end ReciprocityTheory.PGsh.Up
end
end

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section LiftR

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

private lemma eq_zero_of_iso_zero {n : Type} [Fintype n] {M : Matrix n n R}
    (e : LinearMap.range (Matrix.mulVecLin M) ≃ₗ[R] (Fin 0 → R)) : M = 0 := by
  classical
  have hsub : ∀ y : LinearMap.range (Matrix.mulVecLin M), y = 0 := fun y =>
    e.injective (Subsingleton.elim _ _)
  ext i j
  have h := hsub ⟨M *ᵥ Pi.single j 1, LinearMap.mem_range_self _ _⟩
  have h' := congrArg (fun y : LinearMap.range (Matrix.mulVecLin M) => (y : n → R) i) h
  simpa [Matrix.mulVec_single_one] using h'

private lemma row_decomp {H : HodgeTateDatum p g v R O σ cp} (U : UnramData p g v R O σ cp H) (i : Fin U.m)
    (c : Fin g ⊕ Fin g → R) :
    ∑ k, c k • (fromRows H.Ht (bt2 H U) * U.εT i) k =
      ((c ∘ Sum.inl) ᵥ* H.Ht + ((c ∘ Sum.inr) ᵥ* U.εL i) ᵥ* H.Bt) ᵥ* U.εT i := by
  have hb : bt2 H U * U.εT i = U.εL i * H.Bt * U.εT i := by
    unfold bt2
    rw [Matrix.sum_mul, Finset.sum_eq_single i]
    · rw [Matrix.mul_assoc, U.εT_orth, if_pos rfl]
    · intro x _ hx
      rw [Matrix.mul_assoc, U.εT_orth, if_neg hx, Matrix.mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have key : ∑ k, c k • (fromRows H.Ht (bt2 H U) * U.εT i) k =
      c ᵥ* (fromRows H.Ht (bt2 H U) * U.εT i) := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct]
  rw [key, Matrix.fromRows_mul, hb, Matrix.vecMul_fromRows]
  simp only [Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem lifts_of (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement) (hR : EigenRankStatement) :
    EigenLiftsStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U X hX
  obtain ⟨G, _, _, β, hmul, h1, hcard, hfrob, hsepG, hnt⟩ := hG p g C v R O σ cp hp2 hS H U
  obtain ⟨κ, Λ, ε, hΛdet, hΛblock, hεdiv, hεprod, hcard_n, hspan⟩ :=
    hE p g C v R O σ cp hS H U X hX
  obtain ⟨hrank, hrzero⟩ := hR p g C v R O σ cp hS H U
  haveI : Nontrivial R := ⟨⟨(p : R), 0, fun h => hS.p_ne (by rw [h, map_zero, map_zero])⟩⟩
  have hεT : ∀ j, U.εT (κ j) ≠ 0 := by
    intro j h0
    have hb := hΛblock j
    rw [h0, Matrix.vecMul_zero] at hb
    apply hΛdet.ne_zero
    exact Matrix.det_eq_zero_of_row_eq_zero j (fun k => by rw [← hb]; rfl)
  have hlift : ∀ j, ∃ u : Nb p g → C, (∀ y, v (u y) ≤ 1) ∧
      (∀ y, v (u y - algebraMap R C (∑ k, Λ j k * ((y k).val : R))) < 1) ∧
      (fun y => algebraMap R C (ε j) * u y) ∈ augIdeal H.AA.carrier ∧
      (∀ δ t, u (red p g (H.ρ (β δ) *ᵥ t)) = algebraMap R C (U.sg (κ j) (β δ)) * u (red p g t)) := by
    intro j
    have hmem : ε j • Λ j ∈ Submodule.span R
        (Set.range fun k => (fromRows H.Ht (bt2 H U) * U.εT (κ j)) k) := by
      rw [hspan (κ j)]
      exact Submodule.subset_span ⟨j, rfl, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
    rw [row_decomp U (κ j) c] at hc
    exact lift_one (hS := hS) (hp2 := hp2) (U := U) (hmul := hmul) (h1 := h1) (hsep := hsepG)
      (hcardG := hcard) (hi := hεT j) (hnt := hnt (κ j) (hεT j)) (e := ε j) (lam := Λ j)
      (hdiv := hεdiv j) (wH := c ∘ Sum.inl) (wB := (c ∘ Sum.inr) ᵥ* U.εL (κ j)) (hrow := hc)
  choose u hu1 hu2 hu3 hu4 using hlift
  exact ⟨{
    κ := κ
    card_phi := fun i => by
      obtain ⟨n, hn1, hn2⟩ := hrank i
      rw [hcard_n (U.φ i) n hn2, hcard_n i n hn1]
    r_zero := fun i hno => by
      obtain ⟨n, hn1, -⟩ := hrank i
      have hc := hcard_n i n hn1
      have h0 : (Finset.univ.filter fun j => κ j = i).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        exact fun j _ => hno j
      have hn : n = 0 := by omega
      subst hn
      exact hrzero i (eq_zero_of_iso_zero hn1.some)
    Λ := Λ
    Λ_det := hΛdet
    Λ_block := hΛblock
    ε := ε
    ε_ne := fun j h0 => by
      obtain ⟨c, hc⟩ := hεdiv j
      rw [h0, zero_mul] at hc
      have hv := hS.cp_val
      have hp1 : p - 1 ≠ 0 := by
        have := (Fact.out : p.Prime).two_le
        omega
      rw [hc, map_zero, map_zero, zero_pow hp1] at hv
      exact hS.p_ne hv.symm
    ε_prod := hεprod
    u := u
    u_int := hu1
    u_cong := hu2
    x_mem := hu3
    s := Fintype.card G
    b := fun k => β ((Fintype.equivFin G).symm k)
    eig := fun j k t => hu4 j _ t
    frobChar := fun j k => hfrob (κ j) _ (hεT j)
    sep := fun j j' hne => by
      obtain ⟨γ, hγ⟩ := hsepG (κ j) (κ j') (hεT j) (hεT j') hne
      exact ⟨Fintype.equivFin G γ, by simpa using hγ⟩ }⟩

end LiftR

end ReciprocityTheory.PGsh.Up
