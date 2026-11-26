module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnitriangularMulUpperTriangularOfIsUnitLead
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnitriangularMulUpperTriangularOfIsUnitLead
open Matrix

namespace GlobalTheory

theorem lowerUnitriangular_mul_upperTriangular_of_isUnit_leadingMinors :
    ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R),
      (∀ (k : ℕ) (hk : k ≤ n), IsUnit (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) →
      ∃ L U : Matrix (Fin n) (Fin n) R, (∀ i j : Fin n, i < j → L i j = 0) ∧ (∀ i, L i i = 1) ∧
        U.BlockTriangular id ∧ (∀ i, IsUnit (U i i)) ∧ M = L * U := by
  intro R _ n
  induction n with
  | zero =>
    intro M _
    exact ⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      Subsingleton.elim _ _⟩
  | succ n ih =>
    intro M hM
    set M' : Matrix (Fin n) (Fin n) R := M.submatrix Fin.castSucc Fin.castSucc with hM'
    have hM'min : ∀ (k : ℕ) (hk : k ≤ n),
        IsUnit (M'.submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
      intro k hk
      have := hM k (hk.trans n.le_succ)
      convert this using 2
      ext i j; rfl
    obtain ⟨L', U', hL'0, hL'1, hU't, hU'd, hLU'⟩ := ih M' hM'min
    have hL'det : L'.det = 1 := by
      rw [Matrix.det_of_lowerTriangular L' (fun i j hij => hL'0 i j hij)]
      simp [hL'1]
    have hL'u : IsUnit L'.det := by rw [hL'det]; exact isUnit_one
    have hM'u : IsUnit M'.det := by
      have := hM'min n le_rfl
      convert this using 2
      ext i j; rfl
    have hU'u : IsUnit U'.det := by
      rw [hLU', det_mul, hL'det, one_mul] at hM'u; exact hM'u
    let v : Fin n → R := fun i => M (Fin.castSucc i) (Fin.last n)
    let u : Fin n → R := fun j => M (Fin.last n) (Fin.castSucc j)
    let a : Fin n → R := u ᵥ* U'⁻¹
    let b : Fin n → R := L'⁻¹ *ᵥ v
    let e : R := M (Fin.last n) (Fin.last n) - a ⬝ᵥ b
    let L : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (motive := fun _ => R)
        (Fin.lastCases (motive := fun _ => R) 1 (fun j' => a j') j)
        (fun i' => Fin.lastCases (motive := fun _ => R) 0 (fun j' => L' i' j') j) i
    let U : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (motive := fun _ => R)
        (Fin.lastCases (motive := fun _ => R) e (fun _ => 0) j)
        (fun i' => Fin.lastCases (motive := fun _ => R) (b i') (fun j' => U' i' j') j) i
    have ha : a ᵥ* U' = u := by
      simp only [a]; rw [vecMul_vecMul, nonsing_inv_mul _ hU'u, vecMul_one]
    have hb : L' *ᵥ b = v := by
      simp only [b]; rw [mulVec_mulVec, mul_nonsing_inv _ hL'u, one_mulVec]
    have hL0 : ∀ i j : Fin (n+1), i < j → L i j = 0 := by
      intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [L] at *
      all_goals first
        | exact absurd hij (not_lt.2 (Fin.castSucc_lt_last _).le)
        | exact hL'0 _ _ hij
    have hL1 : ∀ i, L i i = 1 := by
      intro i
      induction i using Fin.lastCases <;> simp [L, hL'1]
    have hUt : U.BlockTriangular id := by
      intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [U] at *
      all_goals first
        | exact absurd hij (not_lt.2 (Fin.castSucc_lt_last _).le)
        | exact hU't hij
    have hLU : M = L * U := by
      ext i j
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          simp only [L, U, e, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply,
            Fin.lastCases_last, Fin.lastCases_castSucc, dotProduct]
          ring
        | cast j =>
          have hj := congrFun ha j
          simp only [vecMul, dotProduct, u] at hj
          simp only [L, U, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply,
            Fin.lastCases_last, Fin.lastCases_castSucc, hj]
          ring
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          have hi := congrFun hb i
          simp only [mulVec, dotProduct, v] at hi
          simp only [L, U, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply,
            Fin.lastCases_last, Fin.lastCases_castSucc, hi]
          ring
        | cast j =>
          have hij := congrFun (congrFun hLU' i) j
          simp only [M', Matrix.submatrix_apply, Matrix.mul_apply] at hij
          simp only [L, U, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply,
            Fin.lastCases_last, Fin.lastCases_castSucc, hij]
          ring
    have hdetL : L.det = 1 := by
      rw [Matrix.det_of_lowerTriangular L (fun i j hij => hL0 i j hij)]
      simp [hL1]
    have hMu : IsUnit M.det := by
      have := hM (n+1) le_rfl
      convert this using 2
      ext i j; rfl
    have he : IsUnit e := by
      rw [hLU, det_mul, hdetL, one_mul, Matrix.det_of_upperTriangular hUt,
        Fin.prod_univ_castSucc] at hMu
      have := isUnit_of_mul_isUnit_right hMu
      simpa [U] using this
    refine ⟨L, U, hL0, hL1, hUt, ?_, hLU⟩
    intro i
    induction i using Fin.lastCases with
    | last => simpa [U] using he
    | cast i => simpa [U] using hU'd i
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnitriangularMulUpperTriangularOfIsUnitLeadStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lu_of_isUnit_leading_minors : ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R), (∀ (k : ℕ) (hk : k ≤ n), IsUnit (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) → ∃ L U : Matrix (Fin n) (Fin n) R, (∀ i j : Fin n, i < j → L i j = 0) ∧ (∀ i, L i i = 1) ∧ U.BlockTriangular id ∧ (∀ i, IsUnit (U i i)) ∧ M = L * U := by
  first | exact @GlobalTheory.lowerUnitriangular_mul_upperTriangular_of_isUnit_leadingMinors | exact GlobalTheory.lowerUnitriangular_mul_upperTriangular_of_isUnit_leadingMinors | (intros; apply GlobalTheory.lowerUnitriangular_mul_upperTriangular_of_isUnit_leadingMinors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdCoordsOfDefiniteParallelogramForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdCoordsOfDefiniteParallelogramForm
namespace GlobalTheory

theorem parallelogram_zsmul {E : Type} [AddCommGroup E] (Q : E → ℤ)
    (hQ : ∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) (k : ℤ) (f : E) :
    Q (k • f) = k ^ 2 * Q f := by
  have h0 : Q 0 = 0 := by
    have := hQ 0 0
    simp only [add_zero, sub_zero] at this
    omega
  have hneg : ∀ g, Q (-g) = Q g := by
    intro g
    have := hQ 0 g
    simp only [zero_add, zero_sub, h0] at this
    omega
  have hnat : ∀ n : ℕ, Q ((n : ℤ) • f) = (n : ℤ) ^ 2 * Q f ∧
      Q (((n : ℤ) + 1) • f) = ((n : ℤ) + 1) ^ 2 * Q f := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      refine ⟨by push_cast; exact ih.2, ?_⟩
      have h := hQ (((n : ℤ) + 1) • f) f
      have e1 : ((n : ℤ) + 1) • f + f = (((n + 1 : ℕ) : ℤ) + 1) • f := by
        push_cast; module
      have e2 : ((n : ℤ) + 1) • f - f = (n : ℤ) • f := by module
      rw [e1, e2, ih.1, ih.2] at h
      push_cast at h ⊢
      linear_combination h
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · exact (hnat n).1
  · rw [neg_smul, hneg, (hnat n).1]; ring

theorem parallelogram_sum_le {E ι : Type} [AddCommGroup E] (Q : E → ℤ)
    (hQ : ∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) (hpos : ∀ f, 0 ≤ Q f)
    (u : ι → E) (s : Finset ι) :
    ∃ C : ℕ, ∀ (z : ι → ℤ) (M : ℤ), (∀ i, |z i| ≤ M) →
      Q (∑ i ∈ s, z i • u i) ≤ C * M ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, fun z M _ => ?_⟩
    have := parallelogram_zsmul Q hQ 0 0
    simp at this
    simp [this]
  | insert a s ha ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨2 * (Q (u a)).toNat + 2 * C, fun z M hz => ?_⟩
    rw [Finset.sum_insert ha]
    have h1 := hQ (z a • u a) (∑ i ∈ s, z i • u i)
    have h2 := hpos (z a • u a - ∑ i ∈ s, z i • u i)
    have h3 := hC z M hz
    have h4 := parallelogram_zsmul Q hQ (z a) (u a)
    have h5 : z a ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs (z a)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hz a) 2
    have h6 := mul_le_mul_of_nonneg_right h5 (hpos (u a))
    push_cast
    rw [Int.toNat_of_nonneg (hpos (u a))]
    nlinarith

theorem exists_dvd_coords_of_definite_form :
    ∀ (E : Type) [AddCommGroup E] (H : AddSubgroup E) (Q : E → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f ∈ H, Q f = 0 → f = 0) → ∀ (n : ℕ) (u : Fin n → E), (∀ i, u i ∈ H) → LinearIndependent ℤ u → ∃ e : ℕ, 0 < e ∧ ∀ (k : ℕ) (m : Fin n → ℤ) (h : E), h ∈ H → k • h = ∑ i, m i • u i → ∀ i, (k : ℤ) ∣ e * m i := by
  intro E _ H Q hQ hpos hdef n u hu hli
  obtain ⟨C, hC⟩ := parallelogram_sum_le Q hQ hpos u Finset.univ
  rw [Fintype.linearIndependent_iff] at hli
  set R : ℕ := C + 1 with hR
  refine ⟨(R ^ n).factorial, Nat.factorial_pos _, fun k m h hh hk => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · intro i
    have := hli m (by simpa using hk.symm) i
    simp [this]
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hR0 : (0 : ℤ) < R := by positivity
  obtain ⟨a, ha, b, hb, hab, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (R ^ n + 1))
    (t := Fintype.piFinset (fun _ : Fin n => Finset.Ico (0 : ℤ) R))
    (f := fun (j : ℕ) (i : Fin n) => ((R : ℤ) * (((j : ℤ) * m i) % k)) / k)
    (by simp [Fintype.card_piFinset])
    (by
      intro j _
      simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Ico]
      intro i
      have h1 := Int.emod_nonneg ((j : ℤ) * m i) hk0.ne'
      have h2 := Int.emod_lt_of_pos ((j : ℤ) * m i) hk0
      refine ⟨Int.ediv_nonneg (by positivity) hk0.le, ?_⟩
      apply Int.ediv_lt_of_lt_mul hk0
      exact mul_lt_mul_of_pos_left h2 hR0)
  set y : Fin n → ℤ := fun i => ((a : ℤ) * m i) % k - ((b : ℤ) * m i) % k with hy
  set q : Fin n → ℤ := fun i => ((a : ℤ) * m i) / k - ((b : ℤ) * m i) / k with hq
  have hyq : ∀ i, y i = ((a : ℤ) - b) * m i - k * q i := by
    intro i
    simp only [hy, hq, Int.emod_def]
    ring
  have hbound : ∀ i, |(R : ℤ) * y i| ≤ k := by
    intro i
    have e := congrFun hf i
    beta_reduce at e
    have a1 := Int.emod_nonneg ((R : ℤ) * (((a : ℤ) * m i) % k)) hk0.ne'
    have a2 := Int.emod_lt_of_pos ((R : ℤ) * (((a : ℤ) * m i) % k)) hk0
    have b1 := Int.emod_nonneg ((R : ℤ) * (((b : ℤ) * m i) % k)) hk0.ne'
    have b2 := Int.emod_lt_of_pos ((R : ℤ) * (((b : ℤ) * m i) % k)) hk0
    rw [Int.emod_def] at a1 a2 b1 b2
    rw [e] at a1 a2
    simp only [hy]
    rw [abs_le, mul_sub]
    constructor <;> linarith
  set w : E := ((a : ℤ) - b) • h - ∑ i, q i • u i with hw
  have hwH : w ∈ H := H.sub_mem (H.zsmul_mem hh _) (H.sum_mem fun i _ => H.zsmul_mem (hu i) _)
  have hkw : (k : ℤ) • w = ∑ i, y i • u i := by
    rw [hw, smul_sub, smul_comm, natCast_zsmul h k, hk, Finset.smul_sum, Finset.smul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hyq i, smul_smul, smul_smul, sub_smul]
  have hRkw : ((R : ℤ) * k) • w = ∑ i, ((R : ℤ) * y i) • u i := by
    rw [mul_smul, hkw, Finset.smul_sum]
    simp only [smul_smul]
  have hle := hC (fun i => (R : ℤ) * y i) k hbound
  rw [← hRkw, parallelogram_zsmul Q hQ] at hle
  have hQw : Q w = 0 := by
    by_contra hne
    have h1 : 1 ≤ Q w := by have := hpos w; omega
    have h2 : ((R : ℤ) * k) ^ 2 ≤ ((R : ℤ) * k) ^ 2 * Q w := le_mul_of_one_le_right (by positivity) h1
    have h3 : (C : ℤ) < (R : ℤ) ^ 2 := by
      rw [hR]; push_cast; nlinarith [Int.natCast_nonneg C]
    have h4 := mul_lt_mul_of_pos_right h3 (show (0 : ℤ) < (k : ℤ) ^ 2 by positivity)
    rw [mul_pow] at h2 hle
    linarith
  have hw0 := hdef w hwH hQw
  rw [hw0, smul_zero] at hkw
  intro i
  have hyi := hli y hkw.symm i
  have hd : (k : ℤ) ∣ ((a : ℤ) - b) * m i := ⟨q i, by have := hyq i; linarith⟩
  refine hd.trans (mul_dvd_mul_right ?_ _)
  rw [← Int.natAbs_dvd, Int.natCast_dvd_natCast]
  rw [Finset.mem_range] at ha hb
  apply Nat.dvd_factorial
  · omega
  · omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdCoordsOfDefiniteParallelogramFormStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvd_coords_of_definite_parallelogram_form : ∀ (E : Type) [AddCommGroup E] (H : AddSubgroup E) (Q : E → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f ∈ H, Q f = 0 → f = 0) → ∀ (n : ℕ) (u : Fin n → E), (∀ i, u i ∈ H) → LinearIndependent ℤ u → ∃ e : ℕ, 0 < e ∧ ∀ (k : ℕ) (m : Fin n → ℤ) (h : E), h ∈ H → k • h = ∑ i, m i • u i → ∀ i, (k : ℤ) ∣ e * m i := by
  first | exact @GlobalTheory.exists_dvd_coords_of_definite_form | exact GlobalTheory.exists_dvd_coords_of_definite_form | (intros; apply GlobalTheory.exists_dvd_coords_of_definite_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanEqTopOfFinrankFibreEq
open TensorProduct Module

namespace GlobalTheory

open TensorProduct Module in
variable {B A M : Type*} [CommRing B] [CommRing A] [Algebra B A] [Algebra.IsIntegral B A]
  [AddCommGroup M] [Module B M] {r : ℕ} in
private lemma finrank_fiber_eq (hinj : Function.Injective (algebraMap B A))
    (b : Basis (Fin r) A (A ⊗[B] M)) (P : Ideal B) [P.IsMaximal] :
    letI := Ideal.Quotient.field P
    finrank (B ⧸ P) ((B ⧸ P) ⊗[B] M) = r := by
  letI := Ideal.Quotient.field P
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) P
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  haveI : Q.LiesOver P := ⟨hQP.symm⟩
  letI := Ideal.Quotient.field Q
  have h1 : finrank (A ⧸ Q) ((A ⧸ Q) ⊗[A] (A ⊗[B] M)) = r := by
    rw [finrank_eq_card_basis (Algebra.TensorProduct.basis (A ⧸ Q) b), Fintype.card_fin]
  rw [← Module.finrank_baseChange (R := A ⧸ Q),
    (AlgebraTensorModule.cancelBaseChange B (B ⧸ P) (A ⧸ Q) (A ⧸ Q) M).finrank_eq,
    ← (AlgebraTensorModule.cancelBaseChange B A (A ⧸ Q) (A ⧸ Q) M).finrank_eq, h1]


open TensorProduct Module in
theorem _root_.GlobalTheory.nonempty_basis_of_basis_baseChange {B A M : Type*} [CommRing B] [CommRing A]
    [Finite (MaximalSpectrum B)] [Algebra B A] [Algebra.IsIntegral B A] [AddCommGroup M]
    [Module B M] [Module.Finite B M] {r : ℕ}
    (hinj : Function.Injective (algebraMap B A)) (b : Basis (Fin r) A (A ⊗[B] M)) :
    Nonempty (Basis (Fin r) B M) := by
  classical
  haveI := Fintype.ofFinite (MaximalSpectrum B)
  have hfib : ∀ P : MaximalSpectrum B, ∃ e : Fin r → M,
      Submodule.span (B ⧸ P.asIdeal) (Set.range fun j => (1 : B ⧸ P.asIdeal) ⊗ₜ[B] e j) = ⊤ := by
    intro P
    haveI := P.isMaximal
    letI := Ideal.Quotient.field P.asIdeal
    let β := Module.finBasisOfFinrankEq (B ⧸ P.asIdeal) _ (finrank_fiber_eq hinj b P.asIdeal)
    choose e he using fun j => TensorProduct.mk_surjective B M (B ⧸ P.asIdeal)
      Ideal.Quotient.mk_surjective (β j)
    refine ⟨e, ?_⟩
    have : (fun j => (1 : B ⧸ P.asIdeal) ⊗ₜ[B] e j) = β := funext he
    rw [this, β.span_eq]
  choose e he using hfib
  have hcrt : ∀ P : MaximalSpectrum B, ∃ c : B,
      ∀ P' : MaximalSpectrum B, c - (if P' = P then 1 else 0) ∈ P'.asIdeal := fun P =>
    Ideal.exists_forall_sub_mem_ideal (I := fun P' : MaximalSpectrum B => P'.asIdeal)
      (fun P₁ P₂ h => by
        haveI := P₁.isMaximal
        haveI := P₂.isMaximal
        exact Ideal.isCoprime_of_isMaximal fun h' => h (MaximalSpectrum.ext h')) _
  choose c hc using hcrt
  let x : Fin r → M := fun j => ∑ P, c P • e P j
  let N := Submodule.span B (Set.range x)
  have key : ∀ P : MaximalSpectrum B, (⊤ : Submodule B (M ⧸ N)) ≤ P.asIdeal • ⊤ := by
    intro P
    have hmk : ∀ P', Ideal.Quotient.mk P.asIdeal (c P') = if P = P' then 1 else 0 := by
      intro P'
      have := hc P' P
      split_ifs at this ⊢ with h
      · rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
        exact this
      · exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using this)
    have hsm : ∀ (a : B) (y : (B ⧸ P.asIdeal) ⊗[B] M),
        a • y = Ideal.Quotient.mk P.asIdeal a • y := fun a y =>
      (algebraMap_smul (B ⧸ P.asIdeal) a y).symm
    have hx : ∀ j, (1 : B ⧸ P.asIdeal) ⊗ₜ[B] x j = 1 ⊗ₜ e P j := by
      intro j
      simp only [x, tmul_sum, tmul_smul]
      simp only [hsm, hmk, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true]
    have h0 : N.mkQ.baseChange (B ⧸ P.asIdeal) = 0 := by
      apply LinearMap.ext_on_range (he P)
      intro j
      rw [← hx, LinearMap.baseChange_tmul, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨j, rfl⟩), tmul_zero,
        LinearMap.zero_apply]
    have hsurj : Function.Surjective (N.mkQ.baseChange (B ⧸ P.asIdeal)) :=
      LinearMap.lTensor_surjective (B ⧸ P.asIdeal) N.mkQ_surjective
    have hsub : Subsingleton ((B ⧸ P.asIdeal) ⊗[B] (M ⧸ N)) := ⟨fun y z => by
      obtain ⟨y', rfl⟩ := hsurj y
      obtain ⟨z', rfl⟩ := hsurj z
      simp [h0]⟩
    have hq := (TensorProduct.quotTensorEquivQuotSMul (M ⧸ N) P.asIdeal).symm.toEquiv.subsingleton
    rw [Submodule.Quotient.subsingleton_iff] at hq
    rw [hq]
  have hann : Module.annihilator B (M ⧸ N) = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨t, ht1, ht⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul P ⊤
      Module.Finite.fg_top (key ⟨P, hP⟩)
    have htP : t ∈ P := hle (Module.mem_annihilator.mpr fun q => ht q trivial)
    exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using P.sub_mem htP ht1))
  have hN : N = ⊤ := by
    rw [eq_top_iff]
    intro m _
    have h1 : (1 : B) ∈ Module.annihilator B (M ⧸ N) := hann ▸ Submodule.mem_top
    have := Module.mem_annihilator.mp h1 (N.mkQ m)
    simpa [Submodule.Quotient.mk_eq_zero] using this
  let f := Fintype.linearCombination B x
  have hfs : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hN
  let F := f.baseChange A
  have hFs : Function.Surjective F := LinearMap.lTensor_surjective A hfs
  let φ : (Fin r → A) →ₗ[A] (Fin r → A) := b.equivFun.toLinearMap ∘ₗ F ∘ₗ
    (TensorProduct.piScalarRight B A A (Fin r)).symm.toLinearMap
  have hφs : Function.Surjective φ := by
    simpa [φ] using b.equivFun.surjective.comp
      (hFs.comp (TensorProduct.piScalarRight B A A (Fin r)).symm.surjective)
  have hφi := OrzechProperty.injective_of_surjective_endomorphism φ hφs
  have hFi : Function.Injective F := by
    intro y z hyz
    have := @hφi (TensorProduct.piScalarRight B A A (Fin r) y)
      (TensorProduct.piScalarRight B A A (Fin r) z) (by
        simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hyz])
    exact (TensorProduct.piScalarRight B A A (Fin r)).injective this
  have hfi : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    have h1 : F ((1 : A) ⊗ₜ v) = F 0 := by
      rw [LinearMap.baseChange_tmul, LinearMap.mem_ker.mp hv, tmul_zero, map_zero]
    have h2 := congrArg (TensorProduct.piScalarRight B A A (Fin r)) (hFi h1)
    rw [Submodule.mem_bot]
    funext i
    exact hinj (by rw [Pi.zero_apply, map_zero, Algebra.algebraMap_eq_smul_one]; simpa using congrFun h2 i)
  exact ⟨Basis.ofEquivFun (LinearEquiv.ofBijective f ⟨hfi, hfs⟩).symm⟩


open TensorProduct Module in
theorem _root_.GlobalTheory.finrank_eq_mul_of_basis_tensor_self (k B A : Type) [Field k] [CommRing B] [CommRing A]
    [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Module.Finite k A] (r : ℕ)
    (hinj : Function.Injective (algebraMap B A))
    (hb : Nonempty (Module.Basis (Fin r) A (TensorProduct B A A))) :
    Module.finrank k A = r * Module.finrank k B := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · haveI : Subsingleton A := by
      refine subsingleton_of_zero_eq_one ?_
      rw [← map_zero (algebraMap B A), ← map_one (algebraMap B A), Subsingleton.elim (0 : B) 1]
    simp [Module.finrank_zero_of_subsingleton]
  haveI : Module.Finite k B :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom k B A).toLinearMap hinj
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  haveI : Module.Finite B A := Module.Finite.of_restrictScalars_finite k B A
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  obtain ⟨β⟩ := _root_.GlobalTheory.nonempty_basis_of_basis_baseChange (M := A) hinj hb.some
  haveI : Module.Free B A := Module.Free.of_basis β
  rw [← Module.finrank_mul_finrank k B A, finrank_eq_card_basis β, Fintype.card_fin, mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDataOfCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDataOfCompatible
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory.AffineIdealGlue

variable {X : Scheme.{0}}

lemma res_res {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom s) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

def glueIdeal (𝒜 : Set X.affineOpens) (k : ∀ W : X.affineOpens, Ideal Γ(X, W))
    (V : X.affineOpens) : Ideal Γ(X, V) :=
  ⨅ W ∈ 𝒜, ⨅ h : W ≤ V, (k W).comap (X.presheaf.map (homOfLE h).op).hom

lemma mem_glueIdeal {𝒜 : Set X.affineOpens} {k : ∀ W : X.affineOpens, Ideal Γ(X, W)}
    {V : X.affineOpens} {s : Γ(X, V)} :
    s ∈ glueIdeal 𝒜 k V ↔
      ∀ W ∈ 𝒜, ∀ h : W ≤ V, (X.presheaf.map (homOfLE h).op).hom s ∈ k W := by
  simp [glueIdeal, Submodule.mem_iInf]

section
variable {𝒜 : Set X.affineOpens} {k : ∀ W : X.affineOpens, Ideal Γ(X, W)}
  (hk : ∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W),
    (k W).map (X.presheaf.map (homOfLE h).op).hom = k W')
include hk

lemma res_mem {W W' : X.affineOpens} (hW : W ∈ 𝒜) (h : W' ≤ W) {s : Γ(X, W)} (hs : s ∈ k W) :
    (X.presheaf.map (homOfLE h).op).hom s ∈ k W' := by
  rw [← hk W hW W' h]; exact Ideal.mem_map_of_mem _ hs

lemma glueIdeal_eq {V : X.affineOpens} (hV : V ∈ 𝒜) : glueIdeal 𝒜 k V = k V := by
  apply le_antisymm
  · intro s hs
    have := mem_glueIdeal.1 hs V hV le_rfl
    erw [X.presheaf.map_id] at this
    exact this
  · intro s hs
    exact mem_glueIdeal.2 fun W hW h => res_mem hk hV h hs

lemma exists_pow_mul_mem {B : X.affineOpens} (hB : B ∈ 𝒜) (g x : Γ(X, B))
    (hx : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom x ∈ k (X.affineBasicOpen g)) :
    ∃ n : ℕ, g ^ n * x ∈ k B := by
  haveI := B.2.isLocalization_basicOpen g
  rw [← hk B hB (X.affineBasicOpen g) (X.affineBasicOpen_le g)] at hx
  change algebraMap Γ(X, B) Γ(X, X.basicOpen g) x ∈
    Ideal.map (algebraMap Γ(X, B) Γ(X, X.basicOpen g)) (k B) at hx
  obtain ⟨_, ⟨n, rfl⟩, h⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers g) Γ(X, X.basicOpen g) (k B) x).1 hx
  exact ⟨n, h⟩

lemma exists_pow_mul_mem_glueIdeal (h𝒜 : ∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜)
    (hcov : ∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) (U : X.affineOpens) (f a : Γ(X, U))
    (ha : ∀ W ∈ 𝒜, ∀ h : W.1 ≤ X.basicOpen f,
      (X.presheaf.map (homOfLE (h.trans (X.basicOpen_le f))).op).hom a ∈ k W) :
    ∃ m : ℕ, f ^ m * a ∈ glueIdeal 𝒜 k U := by
  classical
  have hloc : ∀ y : U.1, ∃ h : Γ(X, U), y.1 ∈ X.basicOpen h ∧ X.affineBasicOpen h ∈ 𝒜 ∧
      ∃ m : ℕ, (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (f ^ m * a) ∈
        k (X.affineBasicOpen h) := by
    intro y
    obtain ⟨W0, hW0, hyW0⟩ := hcov y.1
    obtain ⟨h, hhW0, hyh⟩ := U.2.exists_basicOpen_le (V := W0.1) ⟨y.1, hyW0⟩ y.2
    have hB : X.affineBasicOpen h ∈ 𝒜 := h𝒜 W0 hW0 _ hhW0
    refine ⟨h, hyh, hB, ?_⟩
    have hle : X.basicOpen ((X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom f) ≤
        X.basicOpen f := by
      rw [Scheme.basicOpen_res]; exact inf_le_right
    obtain ⟨m, hm⟩ := exists_pow_mul_mem hk hB
      ((X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom f)
      ((X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom a) (by
        have hmem := ha (X.affineBasicOpen _) (h𝒜 _ hB _ (X.affineBasicOpen_le _)) hle
        erw [res_res]; exact hmem)
    refine ⟨m, ?_⟩
    rw [map_mul, map_pow]; exact hm
  choose h hyh hB m hm using hloc
  obtain ⟨F, hF⟩ := U.2.isCompact.elim_finite_subcover (fun y => (X.basicOpen (h y) : Set X))
    (fun y => (X.basicOpen (h y)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyh ⟨y, hy⟩⟩)
  have hspan : Ideal.span (h '' ↑F) = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro z hz
    obtain ⟨y, hyF, hzy⟩ : ∃ y ∈ F, z ∈ X.basicOpen (h y) := by simpa using hF hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨h y, y, hyF, rfl⟩, hzy⟩
  refine ⟨∑ y ∈ F, m y, mem_glueIdeal.2 fun W hW hWU => ?_⟩
  set ρ := (X.presheaf.map (homOfLE (show W.1 ≤ U.1 from hWU)).op).hom with hρ
  have hspanW : Ideal.span (ρ '' (h '' ↑F)) = ⊤ := by
    rw [← Ideal.map_span, hspan, Ideal.map_top]
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (k W) _ hspanW _ ?_
  rintro ⟨_, _, ⟨y, hyF, rfl⟩, rfl⟩

  have hBy : (X.presheaf.map (homOfLE (X.basicOpen_le (h y))).op).hom
      (f ^ (∑ y ∈ F, m y) * a) ∈ k (X.affineBasicOpen (h y)) := by
    have hle : m y ≤ ∑ y ∈ F, m y := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hyF
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, map_mul]
    exact Ideal.mul_mem_left _ _ (hm y)
  obtain ⟨n, hn⟩ := exists_pow_mul_mem hk hW (ρ (h y)) (ρ (f ^ (∑ y ∈ F, m y) * a)) (by
    have hle : (X.affineBasicOpen (ρ (h y))) ≤ X.affineBasicOpen (h y) := by
      change X.basicOpen (ρ (h y)) ≤ X.basicOpen (h y)
      rw [hρ, Scheme.basicOpen_res]; exact inf_le_right
    have := res_mem hk (hB y) hle hBy
    erw [res_res] at this
    rw [hρ]
    erw [res_res]
    exact this)
  exact ⟨n, hn⟩

lemma glueIdeal_basicOpen (h𝒜 : ∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜)
    (hcov : ∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) (U : X.affineOpens) (f : Γ(X, U)) :
    (glueIdeal 𝒜 k U).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      glueIdeal 𝒜 k (X.affineBasicOpen f) := by
  haveI := U.2.isLocalization_basicOpen f
  have halg : ∀ y, algebraMap Γ(X, U) Γ(X, X.basicOpen f) y =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom y := fun _ => rfl
  apply le_antisymm
  · refine Ideal.map_le_of_le_comap ?_
    intro s hs
    have key : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom s ∈
        glueIdeal 𝒜 k (X.affineBasicOpen f) := by
      refine mem_glueIdeal.2 fun W hW hWf => ?_
      erw [res_res]
      exact mem_glueIdeal.1 hs W hW _
    exact key
  · intro t ht
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) t
    have hspec := IsLocalization.mk'_spec Γ(X, X.basicOpen f) a
      (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
    simp only at hspec
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_glueIdeal hk h𝒜 hcov U f a (by
      intro W hW hWf
      have e := res_res (X.basicOpen_le f) hWf a
      rw [← e, ← halg, ← hspec, map_mul]
      exact Ideal.mul_mem_right _ _ (mem_glueIdeal.1 ht W hW hWf))
    show _ ∈ Ideal.map (algebraMap Γ(X, U) Γ(X, X.basicOpen f)) (glueIdeal 𝒜 k U)
    rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f)]
    refine ⟨⟨⟨f ^ m * a, hm⟩, ⟨f ^ (m + n), m + n, rfl⟩⟩, ?_⟩
    simp only
    rw [pow_add, map_mul, map_mul]
    linear_combination (algebraMap Γ(X, U) Γ(X, X.basicOpen f) (f ^ m)) * hspec

end

theorem exists_idealSheafData_of_compatible :
    ∀ {X : Scheme.{0}} (𝒜 : Set X.affineOpens), (∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜) →
      (∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) → ∀ (k : ∀ W : X.affineOpens, Ideal Γ(X, W)),
      (∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W),
        (k W).map (X.presheaf.map (homOfLE h).op).hom = k W') →
      ∃ I : X.IdealSheafData, ∀ W ∈ 𝒜, I.ideal W = k W := by
  intro X 𝒜 h𝒜 hcov k hk
  exact ⟨{ ideal := glueIdeal 𝒜 k, map_ideal_basicOpen := glueIdeal_basicOpen hk h𝒜 hcov },
    fun W hW => glueIdeal_eq hk hW⟩

end GlobalTheory.AffineIdealGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDataOfCompatibleStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idealSheafData_of_compatible_ideals : ∀ {X : Scheme.{0}} (𝒜 : Set X.affineOpens), (∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜) → (∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) → ∀ (k : ∀ W : X.affineOpens, Ideal Γ(X, W)), (∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W), (k W).map (X.presheaf.map (homOfLE h).op).hom = k W') → ∃ I : X.IdealSheafData, ∀ W ∈ 𝒜, I.ideal W = k W := by
  first | (exact @GlobalTheory.AffineIdealGlue.exists_idealSheafData_of_compatible) | (exact GlobalTheory.AffineIdealGlue.exists_idealSheafData_of_compatible) | (intros; apply GlobalTheory.AffineIdealGlue.exists_idealSheafData_of_compatible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealSmulMemSpanRational
open NumberField

namespace GlobalTheory

theorem exists_trace_dual_system (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    ∃ (m : ℕ) (ω : Fin m → 𝓞 L) (η : Fin m → L),
      (∀ i, η i ∈ Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L)) ∧
      ∀ t : L, t = ∑ i, algebraMap K L (Algebra.trace K L (η i * t)) * (ω i : L) := by
  haveI : Module.FinitePresentation (𝓞 K) (𝓞 L) := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) (𝓞 L) := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, F, G, -, -, hFG⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) (𝓞 L)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 L) (nonZeroDivisors (𝓞 K))) L :=
    IsIntegralClosure.isLocalization (𝓞 K) K L (𝓞 L)
  have hbc : IsBaseChange K (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap :=
    IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 K)) K _
  let f : Fin m → Module.Dual K L := fun i =>
    hbc.lift ((Algebra.linearMap (𝓞 K) K) ∘ₗ (LinearMap.proj i) ∘ₗ G)
  have hf : ∀ i (a : 𝓞 L), f i (a : L) = algebraMap (𝓞 K) K (G a i) := fun i a =>
    hbc.lift_eq _ a
  let η : Fin m → L := fun i =>
    ((Algebra.traceForm K L).toDual (traceForm_nondegenerate K L)).symm (f i)
  have hη : ∀ i t, Algebra.trace K L (η i * t) = f i t := fun i t =>
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate K L) (f i) t
  refine ⟨m, fun i => F (Pi.single i 1), η, fun i => ?_, fun t => ?_⟩
  · rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
    refine ⟨G b i, ?_⟩
    rw [Algebra.traceForm_apply, hη]
    exact (hf i b).symm
  · simp_rw [hη]
    have h := hbc.algHom_ext (LinearMap.id : L →ₗ[K] L)
      (∑ i, (f i).smulRight ((F (Pi.single i 1) : 𝓞 L) : L)) (fun a => by
        have ha : a = ∑ i, G a i • F (Pi.single i 1) := by
          have h1 : a = F (G a) := (LinearMap.congr_fun hFG a).symm
          conv_lhs => rw [h1, LinearMap.pi_apply_eq_sum_univ]
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 2
          ext j
          simp [Pi.single_apply, eq_comm]
        change (a : L) = (∑ i, (f i).smulRight ((F (Pi.single i 1) : 𝓞 L) : L)) (a : L)
        simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, hf, algebraMap_smul]
        conv_lhs => rw [ha]
        change algebraMap (𝓞 L) L _ = _
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap.map_smul _ _)
    have h2 := LinearMap.congr_fun h t
    simpa [LinearMap.sum_apply, Algebra.smul_def] using h2

open NumberField in
private theorem exists_integral_traceDual_expansion (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    ∃ (N : ℕ) (e : Fin N → 𝓞 L) (c : Fin N → L),
      (∀ k, c k ∈ Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L)) ∧
      ∀ y : L, y = ∑ k, Algebra.trace K L (algebraMap (𝓞 L) L (e k) * y) • c k := by
  classical
  obtain ⟨N, F, hF⟩ := Module.Finite.exists_fin' (𝓞 K) (𝓞 L)
  have : Module.FinitePresentation (𝓞 K) (𝓞 L) := Module.finitePresentation_of_finite _ _
  have hP : Module.Projective (𝓞 K) (𝓞 L) := Module.Flat.projective_of_finitePresentation
  obtain ⟨h, hh⟩ := Module.projective_lifting_property F LinearMap.id hF
  obtain ⟨e, hdec⟩ : ∃ e : Fin N → 𝓞 L, ∀ b : 𝓞 L, b = ∑ k, h b k • e k := by
    refine ⟨fun k => F (Pi.single k 1), fun b => ?_⟩
    have hb := LinearMap.congr_fun hh b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hb
    conv_lhs => rw [← hb, ← Finset.univ_sum_single (h b)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (Pi.single k (h b k) : Fin N → 𝓞 K) = h b k • Pi.single k 1 by
      rw [← Pi.single_smul', smul_eq_mul, mul_one], map_smul]
  let φ : Fin N → (𝓞 L →ₗ[𝓞 K] 𝓞 K) := fun k => LinearMap.proj k ∘ₗ h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Fin N → Module.Dual K L,
      ∀ k (b : 𝓞 L), ψ k (algebraMap (𝓞 L) L b) = algebraMap (𝓞 K) K (h b k) :=
    ⟨fun k => IsLocalizedModule.mapExtendScalars (nonZeroDivisors (𝓞 K))
      (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap (Algebra.linearMap (𝓞 K) K) K
      (φ k), fun k b => IsLocalizedModule.map_apply (nonZeroDivisors (𝓞 K))
      (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap (Algebra.linearMap (𝓞 K) K)
      (φ k) b⟩
  have hB := traceForm_nondegenerate K L
  obtain ⟨c, hc⟩ : ∃ c : Fin N → L, ∀ k y, Algebra.trace K L (c k * y) = ψ k y :=
    ⟨fun k => ((Algebra.traceForm K L).toDual hB).symm (ψ k), fun k y => by
      rw [← Algebra.traceForm_apply]
      exact LinearMap.BilinForm.apply_toDual_symm_apply _ _⟩
  clear hh hF F this hP
  have hexpO : ∀ b : 𝓞 L,
      algebraMap (𝓞 L) L b = ∑ k, ψ k (algebraMap (𝓞 L) L b) • algebraMap (𝓞 L) L (e k) := by
    intro b
    conv_lhs => rw [hdec b]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hψ, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      IsScalarTower.algebraMap_apply (𝓞 K) K L, Algebra.smul_def]
  have hexp : ∀ y : L, y = ∑ k, ψ k y • algebraMap (𝓞 L) L (e k) := by
    intro y
    obtain ⟨⟨b, s⟩, hbs⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid (𝓞 L) (nonZeroDivisors (𝓞 K))) y
    obtain ⟨a, ha, has⟩ := s.2
    have ha0 : algebraMap (𝓞 K) K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
    have hy : y = (algebraMap (𝓞 K) K a)⁻¹ • algebraMap (𝓞 L) L b := by
      rw [← hbs, ← has, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        IsScalarTower.algebraMap_apply (𝓞 K) K L, mul_comm, ← Algebra.smul_def, smul_smul,
        inv_mul_cancel₀ ha0, one_smul]
    clear hbs has
    rw [hy]
    conv_lhs => rw [hexpO b]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_assoc]
  refine ⟨N, e, c, fun k => ?_, fun y => ?_⟩
  · rw [Submodule.mem_traceDual]
    rintro _ ⟨b, rfl⟩
    rw [Algebra.traceForm_apply]
    exact ⟨h b k, by simpa [hψ, Algebra.smul_def, mul_comm] using (hc k (algebraMap (𝓞 L) L b)).symm⟩
  · rw [← sub_eq_zero]
    refine hB.1 _ fun u => ?_
    have h1 : Algebra.trace K L (y * u) = ∑ k, Algebra.trace K L (algebraMap (𝓞 L) L (e k) * y) *
        Algebra.trace K L (c k * u) := by
      conv_lhs => rw [hexp u]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul, hc]
      exact Finset.sum_congr rfl fun k _ => by rw [mul_comm y]; ring
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, Algebra.traceForm_apply, smul_eq_mul, h1]
    rw [sub_eq_zero]


open NumberField in
theorem _root_.GlobalTheory.differentIdeal_smul_mem_span_rational :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (n : ℕ) (M : Submodule (𝓞 L) (Fin n → L)), (∀ (σ : L ≃ₐ[K] L), ∀ x ∈ M, (fun i => σ (x i)) ∈ M) → ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), ∀ x ∈ M, d • x ∈ Submodule.span (𝓞 L) {y : Fin n → L | y ∈ M ∧ ∃ y0 : Fin n → K, y = fun i => algebraMap K L (y0 i)} := by
  intro K L _ _ _ _ _ _ n M hM d hd x hx
  classical
  obtain ⟨N, e, c, hcD, hswap⟩ := exists_integral_traceDual_expansion K L
  have hdL : algebraMap (𝓞 L) L d ∈ (1 : Submodule (𝓞 L) L) / Submodule.traceDual (𝓞 K) K 1 := by
    rw [← coeSubmodule_differentIdeal (𝓞 K) K (𝓞 L)]
    exact (IsLocalization.mem_coeSubmodule _ _).mpr ⟨d, hd, rfl⟩
  have hdc : ∀ k, ∃ r : 𝓞 L, algebraMap (𝓞 L) L r = algebraMap (𝓞 L) L d * c k := fun k =>
    Submodule.mem_one.mp (Submodule.mem_div_iff_forall_mul_mem.mp hdL _ (hcD k))
  choose r hr using hdc
  set t : Fin N → Fin n → L :=
    fun k i => algebraMap K L (Algebra.trace K L (algebraMap (𝓞 L) L (e k) * x i)) with ht
  have htM : ∀ k, t k ∈ M := by
    intro k
    have : t k = ∑ σ : L ≃ₐ[K] L, fun i => σ ((e k • x) i) := by
      funext i
      simp only [ht, Finset.sum_apply, Pi.smul_apply, trace_eq_sum_automorphisms, Algebra.smul_def]
    rw [this]
    exact Submodule.sum_mem _ fun σ _ => hM σ _ (M.smul_mem _ hx)
  have hdx : d • x = ∑ k, r k • t k := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, ht, Algebra.smul_def, hr]
    conv_lhs => rw [hswap (x i)]
    simp only [Finset.mul_sum, Algebra.smul_def]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hdx]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨htM k, fun i => Algebra.trace K L (algebraMap (𝓞 L) L (e k) * x i), rfl⟩)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedAdjoin
namespace GlobalTheory.SepPoint

noncomputable def adjoinEquiv (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : AlgebraicIndependent k ((↑) : s → F)) :
    MvPolynomial s k ≃ₐ[k] Algebra.adjoin k (s : Set F) :=
  hs.aevalEquiv.trans (Subalgebra.equivOfEq _ _ (by rw [Subtype.range_coe]))

theorem isIntegrallyClosed_adjoin (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : AlgebraicIndependent k ((↑) : s → F)) :
    IsIntegrallyClosed (Algebra.adjoin k (s : Set F)) := by
  haveI : UniqueFactorizationMonoid (Algebra.adjoin k (s : Set F)) :=
    (adjoinEquiv k F s hs).toMulEquiv.uniqueFactorizationMonoid inferInstance
  infer_instance

theorem infinite_of_isSepClosed (Ω : Type) [Field Ω] [IsSepClosed Ω] : Infinite Ω := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  haveI : IsAlgClosed Ω := IsSepClosed.isAlgClosed_of_perfectField Ω
  exact h.false.elim

theorem exists_ev (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : AlgebraicIndependent k ((↑) : s → F)) (H : Algebra.adjoin k (s : Set F)) (hH : H ≠ 0) :
    ∃ ev : Algebra.adjoin k (s : Set F) →ₐ[k] SeparableClosure k, ev H ≠ 0 := by
  haveI := infinite_of_isSepClosed (SeparableClosure k)
  let e := adjoinEquiv k F s hs
  have hP : e.symm H ≠ 0 := by simpa using hH
  obtain ⟨a, ha⟩ : ∃ a : s → SeparableClosure k,
      MvPolynomial.eval a ((e.symm H).map (algebraMap k (SeparableClosure k))) ≠ 0 := by
    by_contra! h
    apply hP
    have := MvPolynomial.funext (p := (e.symm H).map (algebraMap k (SeparableClosure k)))
      (q := 0) (fun x => by simp [h x])
    exact MvPolynomial.map_injective _ (algebraMap k (SeparableClosure k)).injective
      (by simpa using this)
  refine ⟨(MvPolynomial.aeval a).comp e.symm.toAlgHom, ?_⟩
  simpa [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.eval_map] using ha

end GlobalTheory.SepPoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueNormalOfProfiniteInvariants
namespace GlobalTheory

attribute [local instance] Subgroup.finiteIndex_of_finite_quotient

attribute [local instance] Ideal.Quotient.field in
theorem Ideal.Quotient.normal_of_profinite
    {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
    [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B] [Algebra.IsInvariant A B G]
    (P : Ideal A) (Q : Ideal B) [Q.LiesOver P] [P.IsMaximal] [Q.IsMaximal] :
    Normal (A ⧸ P) (B ⧸ Q) := by
  have hint : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral_of_profinite (G := G)
  have hint' : Algebra.IsIntegral (A ⧸ P) (B ⧸ Q) := Ideal.Quotient.algebra_isIntegral_of_liesOver Q P
  refine normal_iff.2 fun ξ => ⟨Algebra.IsIntegral.isIntegral ξ, ?_⟩
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective ξ
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (stabilizer_isOpen G b) (one_mem _)
  let B' := FixedPoints.subalgebra A B N.1.1
  let b' : B' := ⟨b, fun g => hN g.2⟩
  let Q' : Ideal B' := Q.under B'
  have hintB : Algebra.IsIntegral B' B := Algebra.IsIntegral.tower_top A
  have hQ' : Q'.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q
  have : Q'.LiesOver P := ⟨by
    rw [Ideal.under_under (A := A) (B := B') (C := B)]
    exact Ideal.LiesOver.over⟩
  have hn : Normal (A ⧸ P) (B' ⧸ Q') := Ideal.Quotient.normal (G ⧸ N.1.1) P Q'
  let f : (B' ⧸ Q') →ₐ[A ⧸ P] B ⧸ Q :=
    { toRingHom := Ideal.quotientMap _ B'.val le_rfl,
      commutes' := Quotient.ind fun _ ↦ rfl }
  have hf : Function.Injective f := f.toRingHom.injective
  have hfb : f (Ideal.Quotient.mk Q' b') = Ideal.Quotient.mk Q b := rfl
  rw [← hfb, minpoly.algHom_eq f hf]
  have hs := hn.splits (Ideal.Quotient.mk Q' b')
  have := hs.map f.toRingHom
  rw [Polynomial.map_map] at this
  have hc : (f : (B' ⧸ Q') →+* B ⧸ Q).comp (algebraMap (A ⧸ P) (B' ⧸ Q')) = algebraMap (A ⧸ P) (B ⧸ Q) := f.comp_algebraMap
  simpa only [AlgHom.toRingHom_eq_coe, hc] using this

end GlobalTheory
end
