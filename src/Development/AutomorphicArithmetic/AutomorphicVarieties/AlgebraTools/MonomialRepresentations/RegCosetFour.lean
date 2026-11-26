module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.IdCompMat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.AdjugateCornerEqMinor

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Diagz
theorem UpperTheory.Reformulated.B.Qh2.diagz :
    ∀ {K : Type} [inst : Field K]
    (M : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K) (a : Fin (4 : ℕ) → K),
    Function.Injective a →
      M.charpoly = ∏ i : Fin (4 : ℕ), (Polynomial.X - (Polynomial.C : K → Polynomial K) (a i)) →
        ∃ (P : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K) (Q : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K),
          P * Q = (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K) ∧
            Q * P = (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K) ∧ Q * M * P = Matrix.diagonal a := by
  intro K _ M a ha hM
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' M) (a i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) a ha v hv
  let P : Matrix (Fin 4) (Fin 4) K := Matrix.of fun r c => v c r
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp hli
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hMP : M * P = P * Matrix.diagonal a := by
    ext r c
    have h := congrFun (hv c).apply_eq_smul r
    rw [Matrix.toLin'_apply] at h
    rw [Matrix.mul_diagonal, mul_comm]
    exact h
  refine ⟨P, P⁻¹, Matrix.mul_nonsing_inv P hdet, Matrix.nonsing_inv_mul P hdet, ?_⟩
  rw [Matrix.mul_assoc, hMP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.one_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.TorusTransfer
open Polynomial Matrix

private lemma torusTransfer_sep_iff {L : Type*} [Field L] (p : L[X]) (hp : p.Monic) (n : ℕ)
    (hn : p.natDegree = n) :
    p.Separable ↔ p.resultant (derivative p) n n ≠ 0 := by
  classical
  set q := p.map (algebraMap L p.SplittingField) with hq
  have hqm : q.Monic := hp.map _
  have hqd : q.natDegree = n := by
    rw [hq, hp.natDegree_map, hn]
  have hspl : q.Splits := SplittingField.splits p
  have hq0 : q ≠ 0 := hqm.ne_zero
  have hdeg : (derivative q).natDegree ≤ n :=
    (natDegree_derivative_le q).trans (by rw [hqd]; exact Nat.sub_le n 1)
  have hres : algebraMap L p.SplittingField (p.resultant (derivative p) n n) =
      (q.roots.map fun x => (derivative q).eval x).prod := by
    rw [← resultant_map_map, ← derivative_map, ← hq]
    have h := resultant_eq_prod_eval q (derivative q) n hdeg hspl
    rw [hqd, hqm.leadingCoeff, one_pow, one_mul] at h
    exact h
  rw [← separable_map (algebraMap L p.SplittingField), ← hq, ← nodup_roots_iff_of_splits hq0 hspl,
    ne_eq, ← map_eq_zero (algebraMap L p.SplittingField), hres, Multiset.prod_eq_zero_iff]
  constructor
  · intro hnd hz
    obtain ⟨α, hα, hα0⟩ := Multiset.mem_map.1 hz
    have hc := (Multiset.nodup_iff_count_le_one.1 hnd) α
    rw [count_roots] at hc
    have hlt : 1 < rootMultiplicity α q :=
      (one_lt_rootMultiplicity_iff_isRoot hq0).2 ⟨(mem_roots hq0).1 hα, hα0⟩
    omega
  · intro hne
    rw [Multiset.nodup_iff_count_le_one]
    intro α
    rw [count_roots]
    by_contra hlt
    push_neg at hlt
    obtain ⟨hr, hr'⟩ := (one_lt_rootMultiplicity_iff_isRoot hq0).1 hlt
    exact hne (Multiset.mem_map.2 ⟨α, (mem_roots hq0).2 hr, hr'⟩)

private lemma torusTransfer_fiber {K : Type*} [Field K] {σ : Type*} [DecidableEq K]
    (S : Finset σ) (c : σ → K) (v : σ → K) (h : ∀ m : ℕ, ∑ s ∈ S, c s * v s ^ m = 0) (j : K) :
    ∑ s ∈ S with v s = j, c s = 0 := by
  classical
  have hP : ∀ P : K[X], ∑ s ∈ S, c s * P.eval (v s) = 0 := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [eval_add, mul_add, Finset.sum_add_distrib, hp, hq, add_zero]
    | monomial n a =>
      simp only [eval_monomial]
      calc ∑ s ∈ S, c s * (a * v s ^ n) = a * ∑ s ∈ S, c s * v s ^ n := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun s _ => by ring
        _ = 0 := by rw [h n, mul_zero]
  set P : K[X] := ∏ j' ∈ (S.image v).erase j, (X - C j') with hPdef
  have hev : ∀ s ∈ S, P.eval (v s) = if v s = j then P.eval j else 0 := by
    intro s hs
    split_ifs with hsj
    · rw [hsj]
    · rw [hPdef, eval_prod]
      apply Finset.prod_eq_zero (i := v s)
      · exact Finset.mem_erase.2 ⟨hsj, Finset.mem_image_of_mem v hs⟩
      · simp
  have hPj : P.eval j ≠ 0 := by
    rw [hPdef, eval_prod]
    exact Finset.prod_ne_zero_iff.2 fun j' hj' => by
      rw [eval_sub, eval_X, eval_C]
      exact sub_ne_zero.2 (Finset.ne_of_mem_erase hj').symm
  have h0 := hP P
  have h1 : ∑ s ∈ S, c s * P.eval (v s) = ∑ s ∈ S, if v s = j then c s * P.eval j else 0 :=
    Finset.sum_congr rfl fun s hs => by rw [hev s hs, mul_ite, mul_zero]
  rw [h1, ← Finset.sum_filter, ← Finset.sum_mul] at h0
  exact (mul_eq_zero.1 h0).resolve_right hPj

private lemma torusTransfer_key {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (a : ι → Kˣ) (w : ι → ℤ)
    (hw : ∀ m : ι → ℤ, ∏ i, a i ^ m i = 1 → ∑ i, m i * w i = 0)
    (F : MvPolynomial ι K)
    (h : ∀ m : ℕ, MvPolynomial.eval (fun i => (a i : K) ^ m) F = 0) :
    MvPolynomial.eval₂Hom (algebraMap K (RatFunc K))
      (fun i => (RatFunc.X : RatFunc K) ^ w i) F = 0 := by
  classical
  set T : RatFunc K := RatFunc.X with hTdef
  have hT : T ≠ 0 := RatFunc.X_ne_zero
  have hpow : ∀ μ : ι →₀ ℕ, ∏ i, (T ^ w i) ^ μ i = T ^ (∑ i, (μ i : ℤ) * w i) := by
    intro μ
    have key : ∀ s : Finset ι, ∏ i ∈ s, (T ^ w i) ^ μ i = T ^ (∑ i ∈ s, (μ i : ℤ) * w i) := by
      intro s
      refine Finset.induction_on s (by simp) ?_
      intro i s hi ih
      rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ hT, ih, ← zpow_natCast,
        ← _root_.zpow_mul, mul_comm (w i)]
    exact key _
  have hfib : ∀ j : K, ∑ μ ∈ F.support with (∏ i, (a i : K) ^ μ i) = j, F.coeff μ = 0 := by
    intro j
    apply torusTransfer_fiber F.support (fun μ => F.coeff μ) (fun μ => ∏ i, (a i : K) ^ μ i)
    intro m
    have hm := h m
    rw [MvPolynomial.eval_eq'] at hm
    rw [← hm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.prod_pow]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by ring
  have hterm : ∀ μ : ι →₀ ℕ, algebraMap K (RatFunc K) (F.coeff μ) * ∏ i, (T ^ w i) ^ μ i =
      algebraMap K (RatFunc K) (F.coeff μ) * T ^ (∑ i, (μ i : ℤ) * w i) := fun μ => by rw [hpow]
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq', Finset.sum_congr rfl fun μ _ => hterm μ,
    ← Finset.sum_fiberwise_of_maps_to (t := F.support.image fun μ => ∏ i, (a i : K) ^ μ i)
      (g := fun μ => ∏ i, (a i : K) ^ μ i) (fun μ hμ => Finset.mem_image_of_mem _ hμ)
      (fun μ => algebraMap K (RatFunc K) (F.coeff μ) * T ^ (∑ i, (μ i : ℤ) * w i))]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hne : (F.support.filter fun μ => ∏ i, (a i : K) ^ μ i = j).Nonempty
  · obtain ⟨μ0, hμ0⟩ := hne
    have hsame : ∀ μ ∈ F.support.filter (fun μ => ∏ i, (a i : K) ^ μ i = j),
        algebraMap K (RatFunc K) (F.coeff μ) * T ^ (∑ i, (μ i : ℤ) * w i) =
          algebraMap K (RatFunc K) (F.coeff μ) * T ^ (∑ i, (μ0 i : ℤ) * w i) := by
      intro μ hμ
      rw [Finset.mem_filter] at hμ hμ0
      have hv : (∏ i, (a i : K) ^ μ i) = ∏ i, (a i : K) ^ μ0 i := hμ.2.trans hμ0.2.symm
      have hvU : ∏ i, a i ^ μ i = ∏ i, a i ^ μ0 i := by
        apply Units.ext
        push_cast
        exact hv
      have h1 : ∏ i, a i ^ ((μ i : ℤ) - μ0 i) = 1 := by
        simp only [_root_.zpow_sub, zpow_natCast]
        rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, hvU, mul_inv_cancel]
      have h2 := hw _ h1
      simp only [sub_mul, Finset.sum_sub_distrib] at h2
      rw [sub_eq_zero.1 h2]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl hsame, ← Finset.sum_mul, ← map_sum, hfib j, map_zero, zero_mul]
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]

private lemma torusTransfer_spec {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Matrix ι ι K) {L : Type*} [Field L] (f : K →+* L) (t : ι → L) :
    (x.map f * diagonal t).charpoly.Separable ↔
      MvPolynomial.eval₂Hom f t
        ((x.map (MvPolynomial.C : K →+* MvPolynomial ι K) * diagonal MvPolynomial.X).charpoly.resultant
          (derivative (x.map (MvPolynomial.C : K →+* MvPolynomial ι K)
            * diagonal MvPolynomial.X).charpoly) (Fintype.card ι) (Fintype.card ι)) ≠ 0 := by
  have hM : (x.map (MvPolynomial.C : K →+* MvPolynomial ι K) * diagonal MvPolynomial.X).map
      (MvPolynomial.eval₂Hom f t) = x.map f * diagonal t := by
    ext i j
    simp [Matrix.mul_diagonal]
  rw [← resultant_map_map, ← derivative_map, ← charpoly_map, hM]
  exact torusTransfer_sep_iff _ (charpoly_monic _) _ (charpoly_natDegree_eq_dim _)

theorem UpperTheory.V.AlgebraTools.torusTransfer :
    ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (x : Matrix ι ι K) (a : ι → Kˣ) (w : ι → ℤ),
      (∀ m : ι → ℤ, ∏ i, a i ^ m i = 1 → ∑ i, m i * w i = 0) →
      (x.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w i)).charpoly.Separable →
      ∃ m : ℕ, (x * diagonal (fun i => (a i : K) ^ m)).charpoly.Separable := by
  classical
  intro K _ ι _ _ x a w hw hsep
  have hne := (torusTransfer_spec x (algebraMap K (RatFunc K))
    (fun i => (RatFunc.X : RatFunc K) ^ w i)).1 hsep
  by_contra hall
  push_neg at hall
  apply hne
  apply torusTransfer_key a w hw
  intro m
  have hx : x.map (RingHom.id K) = x := by
    ext i j
    rfl
  have hs := torusTransfer_spec x (RingHom.id K) (fun i => (a i : K) ^ m)
  rw [hx] at hs
  exact not_not.1 (mt hs.2 (hall m))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.DiscSwap
open Polynomial Matrix

private theorem charpoly_fromBlocks_antidiagonal_fin_two {F : Type} [Field F] (P Q : Matrix (Fin 2) (Fin 2) F) :
    (fromBlocks 0 P Q 0).charpoly = X ^ 4 - C ((Q * P) 0 0 + (Q * P) 1 1) * X ^ 2
      + C ((Q * P) 0 0 * (Q * P) 1 1 - (Q * P) 0 1 * (Q * P) 1 0) := by
  unfold Matrix.charpoly
  rw [charmatrix_fromBlocks]
  have hcz : charmatrix (0 : Matrix (Fin 2) (Fin 2) F) = diagonal (fun _ : Fin 2 => (X : F[X])) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [charmatrix_apply]
    · simp [charmatrix_apply, diagonal_apply_ne _ h]
  rw [hcz]
  generalize hS : (diagonal (fun _ : Fin 2 => (X : F[X])) : Matrix (Fin 2) (Fin 2) F[X]) = S
  generalize hP' : P.map C = P'
  generalize hQ' : Q.map C = Q'
  have hcomm : S * P' = P' * S := by
    subst hS
    ext i j
    simp [mul_comm]
  have hprod : fromBlocks S (-P') (-Q') S * fromBlocks S P' 0 S
      = fromBlocks (S * S) 0 (-(Q' * S)) (S * S - Q' * P') := by
    rw [fromBlocks_multiply, fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · rw [hcomm, neg_mul, add_neg_cancel]
    · simp
    · rw [neg_mul, add_comm, sub_eq_add_neg]
  have hdet := congrArg det hprod
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] at hdet
  have hSd : det S = X ^ 2 := by
    subst hS
    simp [det_diagonal, Fin.prod_univ_two, sq]
  rw [det_mul, hSd] at hdet
  have hX : (X ^ 2 * X ^ 2 : F[X]) ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ X_ne_zero)
  have hG : det (fromBlocks S (-P') (-Q') S) = det (S * S - Q' * P') := by
    apply mul_right_cancel₀ hX
    rw [hdet]
    ring
  rw [hG, det_fin_two]
  subst hS hP' hQ'
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem separable_biquadratic_of_ne_zero_of_discrim_ne_zero {F : Type} [Field F] (a d : F) (h2 : (2 : F) ≠ 0) (hd : d ≠ 0)
    (he : a ^ 2 - 4 * d ≠ 0) : (X ^ 4 - C a * X ^ 2 + C d : F[X]).Separable := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hk : 4 * d * (8 * d - 2 * a ^ 2) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero h4 hd) ?_
    rw [show 8 * d - 2 * a ^ 2 = -2 * (a ^ 2 - 4 * d) by ring]
    exact mul_ne_zero (neg_ne_zero.2 h2) he
  have hder : derivative (X ^ 4 - C a * X ^ 2 + C d : F[X]) = 4 * X ^ 3 - 2 * C a * X := by
    rw [derivative_add, derivative_sub, derivative_X_pow, derivative_C_mul_X_pow, derivative_C]
    norm_num
    simp only [map_ofNat]
    ring
  have hCe : (C (8 * d - 2 * a ^ 2) : F[X]) = 8 * C d - 2 * C a ^ 2 := by
    simp only [map_mul, map_sub, map_pow, map_ofNat]
  have key : (4 * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2)) * (X ^ 4 - C a * X ^ 2 + C d)
      + (-X * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2) + 2 * C a ^ 2 * X) * (4 * X ^ 3 - 2 * C a * X)
      = C (4 * d * (8 * d - 2 * a ^ 2)) := by
    rw [map_mul, map_mul, hCe]
    simp only [map_ofNat]
    ring
  unfold Polynomial.Separable IsCoprime
  refine ⟨C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * (4 * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2)),
    C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * (-X * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2) + 2 * C a ^ 2 * X), ?_⟩
  rw [hder]
  calc _ = C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * C (4 * d * (8 * d - 2 * a ^ 2)) := by rw [← key]; ring
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hk, C_1]

private theorem discSwap_lemma_3 {K : Type} [Field K] (b c : Matrix (Fin 2) (Fin 2) K) (w₁ w₂ : Fin 2 → ℤ)
    (hw₁ : StrictAnti w₁) (hw₂ : StrictAnti w₂) (hb : b 0 0 ≠ 0) (hc : c 0 0 ≠ 0)
    (hbd : b.det ≠ 0) (hcd : c.det ≠ 0) :
    let N := (c.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₁ i)) *
      (b.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₂ i));
    N 0 0 * N 1 1 - N 0 1 * N 1 0 ≠ 0 ∧
      (N 0 0 + N 1 1) ^ 2 - 4 * (N 0 0 * N 1 1 - N 0 1 * N 1 0) ≠ 0 := by
  intro N
  have h01 : (0 : Fin 2) < 1 := by decide
  obtain ⟨n, hn, hn0⟩ : ∃ n : ℕ, w₁ 0 = w₁ 1 + n ∧ 0 < n :=
    ⟨(w₁ 0 - w₁ 1).toNat, by have := hw₁ h01; omega, by have := hw₁ h01; omega⟩
  obtain ⟨m, hm, hm0⟩ : ∃ m : ℕ, w₂ 0 = w₂ 1 + m ∧ 0 < m :=
    ⟨(w₂ 0 - w₂ 1).toNat, by have := hw₂ h01; omega, by have := hw₂ h01; omega⟩
  set f := algebraMap K (RatFunc K) with hf
  set Y : RatFunc K := RatFunc.X with hY
  have hY0 : Y ≠ 0 := RatFunc.X_ne_zero
  have hA : Y ^ w₁ 0 = Y ^ w₁ 1 * Y ^ n := by rw [hn, zpow_add₀ hY0, zpow_natCast]
  have hB : Y ^ w₂ 0 = Y ^ w₂ 1 * Y ^ m := by rw [hm, zpow_add₀ hY0, zpow_natCast]
  have hu : Y ^ w₁ 1 ≠ 0 := zpow_ne_zero _ hY0
  have hv : Y ^ w₂ 1 ≠ 0 := zpow_ne_zero _ hY0
  have e00 : N 0 0 = f (c 0 0) * Y ^ w₁ 0 * (f (b 0 0) * Y ^ w₂ 0)
      + f (c 0 1) * Y ^ w₁ 1 * (f (b 1 0) * Y ^ w₂ 0) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have e01 : N 0 1 = f (c 0 0) * Y ^ w₁ 0 * (f (b 0 1) * Y ^ w₂ 1)
      + f (c 0 1) * Y ^ w₁ 1 * (f (b 1 1) * Y ^ w₂ 1) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have e10 : N 1 0 = f (c 1 0) * Y ^ w₁ 0 * (f (b 0 0) * Y ^ w₂ 0)
      + f (c 1 1) * Y ^ w₁ 1 * (f (b 1 0) * Y ^ w₂ 0) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have e11 : N 1 1 = f (c 1 0) * Y ^ w₁ 0 * (f (b 0 1) * Y ^ w₂ 1)
      + f (c 1 1) * Y ^ w₁ 1 * (f (b 1 1) * Y ^ w₂ 1) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have hdet : N 0 0 * N 1 1 - N 0 1 * N 1 0
      = f (c.det * b.det) * (Y ^ w₁ 1) ^ 2 * (Y ^ w₂ 1) ^ 2 * Y ^ (n + m) := by
    rw [e00, e01, e10, e11, hA, hB, det_fin_two, det_fin_two]
    simp only [map_mul, map_sub]
    ring
  refine ⟨?_, ?_⟩
  · rw [hdet]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hu)) (pow_ne_zero _ hv)) (pow_ne_zero _ hY0)
    exact (map_ne_zero f).2 (mul_ne_zero hcd hbd)
  · set q : K[X] := C (c 0 0 * b 0 0) * X ^ (n + m)
      + (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1)) with hq
    set Pol : K[X] := q ^ 2 - C (4 * (c.det * b.det)) * X ^ (n + m) with hPol
    have hkey : (N 0 0 + N 1 1) ^ 2 - 4 * (N 0 0 * N 1 1 - N 0 1 * N 1 0)
        = (Y ^ w₁ 1 * Y ^ w₂ 1) ^ 2 * algebraMap K[X] (RatFunc K) Pol := by
      rw [hdet, e00, e11, hA, hB, hPol, hq]
      simp only [map_mul, map_sub, map_add (f := _), map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
        map_ofNat, hf, RatFunc.algebraMap_eq_C, hY]
      ring
    have hrest : (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1) : K[X]).natDegree
        < n + m := by
      have h1 : (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1) : K[X]).natDegree
          ≤ max n m := by
        refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
        · exact (natDegree_C_mul_X_pow_le _ _).trans (le_max_right _ _)
        · exact (natDegree_C_mul_X_pow_le _ _).trans (le_max_left _ _)
        · rw [natDegree_C]; exact Nat.zero_le _
      omega
    have hqd : q.natDegree = n + m := by
      rw [hq, natDegree_add_eq_left_of_natDegree_lt] <;> rw [natDegree_C_mul_X_pow _ _ (mul_ne_zero hc hb)]
      exact hrest
    have hPol0 : Pol ≠ 0 := by
      intro h0
      have hsq : q ^ 2 = C (4 * (c.det * b.det)) * X ^ (n + m) := sub_eq_zero.1 (hPol ▸ h0)
      have := congrArg natDegree hsq
      rw [natDegree_pow, hqd] at this
      have hle := natDegree_C_mul_X_pow_le (4 * (c.det * b.det)) (n + m)
      omega
    rw [hkey]
    refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero hu hv)) ?_
    exact (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).2 hPol0

theorem UpperTheory.V.AlgebraTools.discSwap :
    ∀ (K : Type) [Field K], (2 : K) ≠ 0 → ∀ (b c : Matrix (Fin 2) (Fin 2) K) (w₁ w₂ : Fin 2 → ℤ), StrictAnti w₁ → StrictAnti w₂ →
      b 0 0 ≠ 0 → c 0 0 ≠ 0 → b.det ≠ 0 → c.det ≠ 0 →
      ((fromBlocks 0 b c 0).map (algebraMap K (RatFunc K)) *
        diagonal (Sum.elim (fun i => (RatFunc.X : RatFunc K) ^ w₁ i) (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))).charpoly.Separable := by
  intro K _ h2 b c w₁ w₂ hw₁ hw₂ hb hc hbd hcd
  have hblk : (fromBlocks 0 b c 0).map (algebraMap K (RatFunc K)) *
      diagonal (Sum.elim (fun i => (RatFunc.X : RatFunc K) ^ w₁ i) (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))
      = fromBlocks 0 (b.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))
          (c.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₁ i)) 0 := by
    ext (i | i) (j | j) <;> simp [Matrix.mul_diagonal]
  have h2' : (2 : RatFunc K) ≠ 0 := by
    rw [show (2 : RatFunc K) = algebraMap K (RatFunc K) 2 from (map_ofNat _ 2).symm]
    exact (_root_.map_ne_zero _).2 h2
  obtain ⟨hd, he⟩ := discSwap_lemma_3 b c w₁ w₂ hw₁ hw₂ hb hc hbd hcd
  rw [hblk, charpoly_fromBlocks_antidiagonal_fin_two]
  exact separable_biquadratic_of_ne_zero_of_discrim_ne_zero _ _ h2' hd he
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.RelWeight
open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.relWeight :
    ∀ (A : Type) [CommGroup A] (ι : Type) [Fintype ι] (a : ι → A), (∀ i j, i ≠ j → ¬ IsOfFinOrder (a i / a j)) →
      ∃ w : ι → ℤ, Function.Injective w ∧ ∀ m : ι → ℤ, ∏ i, a i ^ m i = 1 → ∑ i, m i * w i = 0 := by
  intro A _ ι _ a ha
  classical
  obtain ⟨P, hP⟩ : ∃ P : (ι → ℤ) → A, ∀ m, P m = ∏ i, a i ^ m i := ⟨_, fun _ => rfl⟩
  have hPadd : ∀ m n, P (m + n) = P m * P n := by
    intro m n
    rw [hP, hP, hP, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.add_apply, _root_.zpow_add]
  have hPsmul : ∀ (c : ℤ) m, P (c • m) = P m ^ c := by
    intro c m
    rw [hP, hP, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, _root_.zpow_mul]
  have hPsub : ∀ m n, P (m - n) = P m / P n := by
    intro m n
    rw [eq_div_iff_mul_eq', ← hPadd, sub_add_cancel]
  have hPe : ∀ i, P (Pi.single i 1) = a i := by
    intro i
    rw [hP]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  let L : Submodule ℤ (ι → ℤ) :=
    { carrier := {m | ∃ k : ℤ, k ≠ 0 ∧ P (k • m) = 1}
      add_mem' := by
        rintro m n ⟨k, hk, hm⟩ ⟨l, hl, hn⟩
        refine ⟨k * l, mul_ne_zero hk hl, ?_⟩
        have e1 : P ((k * l) • m) = 1 := by rw [mul_comm, mul_smul, hPsmul, hm, _root_.one_zpow]
        have e2 : P ((k * l) • n) = 1 := by rw [mul_smul, hPsmul, hn, _root_.one_zpow]
        rw [smul_add, hPadd, e1, e2, one_mul]
      zero_mem' := ⟨1, one_ne_zero, by simp [hP]⟩
      smul_mem' := by
        rintro c m ⟨k, hk, hm⟩
        exact ⟨k, hk, by rw [smul_comm, hPsmul, hm, _root_.one_zpow]⟩ }
  haveI : Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ L) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x hx => by
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective L x
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨k, hk, h⟩ := hx
      by_cases hr : r = 0
      · exact Or.inl hr
      · right
        rw [Submodule.Quotient.mk_eq_zero]
        exact ⟨k * r, mul_ne_zero hk hr, by rw [mul_smul]; exact h⟩
  let q : ι → (ι → ℤ) ⧸ L := fun i => L.mkQ (Pi.single i 1)
  have hq : ∀ i j, i ≠ j → q i - q j ≠ 0 := by
    intro i j hij h
    rw [← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨k, hk, hk1⟩ := h
    apply ha i j hij
    rw [isOfFinOrder_iff_zpow_eq_one]
    refine ⟨k, hk, ?_⟩
    rw [hPsmul, hPsub, hPe, hPe] at hk1
    exact hk1
  have hex : ∃ f : Module.Dual ℤ ((ι → ℤ) ⧸ L), ∀ i j, i ≠ j → f (q i) ≠ f (q j) := by
    by_contra hno
    push_neg at hno
    let s : Finset (ι × ι) := Finset.univ.filter fun x => x.1 ≠ x.2
    let p : ι × ι → Submodule ℤ (Module.Dual ℤ ((ι → ℤ) ⧸ L)) :=
      fun x => LinearMap.ker (Module.Dual.eval ℤ _ (q x.1 - q x.2))
    have hc : ⋃ x ∈ s, (p x : Set (Module.Dual ℤ ((ι → ℤ) ⧸ L))) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro f
      obtain ⟨i, j, hij, h⟩ := hno f
      simp only [Set.mem_iUnion]
      refine ⟨(i, j), by simp [s, hij], ?_⟩
      simp [p, h]
    obtain ⟨⟨i, j⟩, hx, hfi⟩ := Submodule.exists_finiteIndex_of_cover hc
    have hij : i ≠ j := by simpa [s] using hx
    apply hq i j hij
    rw [← Module.forall_dual_apply_eq_zero_iff ℤ]
    intro f
    have h1 := AddSubgroup.nsmul_index_mem (p (i, j)).toAddSubgroup f
    have h2 : ((p (i, j)).toAddSubgroup.index • f) (q i - q j) = 0 := h1
    rw [LinearMap.smul_apply, smul_eq_zero] at h2
    exact h2.resolve_left hfi.index_ne_zero
  obtain ⟨f, hf⟩ := hex
  refine ⟨fun i => f (q i), fun i j h => ?_, fun m hm => ?_⟩
  · by_contra hij
    exact hf i j hij h
  · have hm0 : L.mkQ m = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨1, one_ne_zero, by rw [one_smul, hP]; exact hm⟩
    have hsum : m = ∑ i, m i • (Pi.single i 1 : ι → ℤ) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
    have h3 : ∑ i, m i • q i = 0 := by
      rw [← hm0]
      conv_rhs => rw [hsum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [q, map_sum, LinearMap.map_smul]
    calc ∑ i, m i * f (q i) = f (∑ i, m i • q i) := by simp [map_sum]
      _ = 0 := by rw [h3, map_zero]
end

open Polynomial Matrix

namespace UpperTheory.V.AlgebraTools.RegFour

private theorem diagz {K : Type} [Field K] (M : Matrix (Fin 4) (Fin 4) K) (a : Fin 4 → K)
    (ha : Function.Injective a) (h : M.charpoly = ∏ i, (X - C (a i))) :
    ∃ P Q : Matrix (Fin 4) (Fin 4) K, P * Q = 1 ∧ Q * P = 1 ∧ Q * M * P = diagonal a :=
  _root_.UpperTheory.Reformulated.B.Qh2.diagz M a ha h

private theorem sortw {n : ℕ} (w : Fin n → ℤ) (hw : Function.Injective w) :
    ∃ π : Equiv.Perm (Fin n), StrictAnti (fun i => w (π i)) := by
  refine ⟨Tuple.sort (fun i => - w i), ?_⟩
  have h1 := Tuple.monotone_sort (fun i => - w i)
  have h2 : StrictMono ((fun i => - w i) ∘ Tuple.sort (fun i => - w i)) :=
    h1.strictMono_of_injective ((neg_injective.comp hw).comp (Equiv.injective _))
  intro i j hij
  have := h2 hij
  simp only [Function.comp] at this
  simpa using this

private theorem sep_reindex {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin 4)
    (x : Matrix (Fin 4) (Fin 4) K) (w : Fin 4 → ℤ)
    (h : ((x.submatrix e e).map (algebraMap K (RatFunc K)) *
      diagonal (fun i => (RatFunc.X : RatFunc K) ^ w (e i))).charpoly.Separable) :
    (x.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w i)).charpoly.Separable := by
  rw [← Matrix.charpoly_reindex e.symm]
  convert h using 2
  ext i j
  simp [Matrix.mul_diagonal]

private theorem sepA {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (x : Matrix (Fin 4) (Fin 4) K) (w : Fin 4 → ℤ)
    (hw : Function.Injective w) (hx : ∀ i, x i i ≠ 0) (hy : ∀ i, x.adjugate i i ≠ 0) :
    (x.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w i)).charpoly.Separable := by
  obtain ⟨π, hπ⟩ := sortw w hw
  apply sep_reindex π
  apply UpperTheory.V.AlgebraTools.disc4 K h2 _ _ hπ
  · exact hx _
  · rw [Matrix.adjugate_submatrix_equiv_self]
    exact hy _

private theorem sepB {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (x : Matrix (Fin 4) (Fin 4) K) (w : Fin 4 → ℤ)
    (hw : Function.Injective w) (e : Fin 2 ⊕ Fin 2 ≃ Fin 4) (hd : x.det ≠ 0)
    (h11 : ∀ i j, x (e (.inl i)) (e (.inl j)) = 0) (h22 : ∀ i j, x (e (.inr i)) (e (.inr j)) = 0)
    (h12 : ∀ i j, x (e (.inl i)) (e (.inr j)) ≠ 0) (h21 : ∀ i j, x (e (.inr i)) (e (.inl j)) ≠ 0) :
    (x.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w i)).charpoly.Separable := by
  obtain ⟨p, hp⟩ := sortw (fun i => w (e (.inl i))) (hw.comp (e.injective.comp Sum.inl_injective))
  obtain ⟨q, hq⟩ := sortw (fun i => w (e (.inr i))) (hw.comp (e.injective.comp Sum.inr_injective))
  let e' : Fin 2 ⊕ Fin 2 ≃ Fin 4 := (Equiv.sumCongr p q).trans e
  let b : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => x (e (.inl (p i))) (e (.inr (q j)))
  let c : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => x (e (.inr (q i))) (e (.inl (p j)))
  have hx : x.submatrix e' e' = fromBlocks 0 b c 0 := by
    ext (i | i) (j | j) <;> simp [e', b, c, h11, h22]
  have hdet : (fromBlocks 0 b c 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).det ≠ 0 := by
    rw [← hx, Matrix.det_submatrix_equiv_self]; exact hd
  have hdet2 : b.det * c.det ≠ 0 := by
    intro h0
    apply hdet
    have h3 : (fromBlocks 0 b c 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks b 0 0 c * fromBlocks 0 1 1 0 := by
      simp [Matrix.fromBlocks_multiply]
    rw [h3, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, h0, zero_mul]
  apply sep_reindex e'
  rw [hx]
  have := UpperTheory.V.AlgebraTools.discSwap K h2 b c _ _ hp hq (h12 _ _) (h21 _ _) (left_ne_zero_of_mul hdet2) (right_ne_zero_of_mul hdet2)
  convert this using 4
  ext (i | i) <;> simp [e']

private theorem comb (E S : Fin 4 → Fin 4 → Prop) (rf : ∀ i, E i i) (sy : ∀ {i j}, E i j → E j i)
    (tr : ∀ {i j k}, E i j → E j k → E i k)
    (se : ∀ {i j k}, S i j → E j k → S i k) (es : ∀ {i j k}, E i j → S j k → S i k)
    (ss : ∀ {i j k}, S i k → S j k → E i j) (ex : ∀ i, ∃ j, S i j) (pa : ∀ i, ∃ j, j ≠ i ∧ E i j)
    (i0 : Fin 4) (h0 : ¬ S i0 i0) :
    ∃ e : Fin 2 ⊕ Fin 2 ≃ Fin 4, (∀ i j, ¬ S (e (.inl i)) (e (.inl j))) ∧ (∀ i j, ¬ S (e (.inr i)) (e (.inr j))) ∧
      (∀ i j, S (e (.inl i)) (e (.inr j))) ∧ (∀ i j, S (e (.inr i)) (e (.inl j))) := by
  obtain ⟨i1, hi, ei⟩ := pa i0
  obtain ⟨j0, s0⟩ := ex i0
  obtain ⟨j1, hj, ej⟩ := pa j0
  have hn : ¬ E i0 j0 := fun h => h0 (se s0 (sy h))
  let f : Fin 2 ⊕ Fin 2 → Fin 4 := Sum.elim ![i0, i1] ![j0, j1]
  have fl : ∀ a, E i0 (f (.inl a)) := by
    intro a; fin_cases a
    · exact rf _
    · exact ei
  have fr : ∀ a, E j0 (f (.inr a)) := by
    intro a; fin_cases a
    · exact rf _
    · exact ej
  have hlr : ∀ a b, f (.inl a) ≠ f (.inr b) := by
    intro a b h
    exact hn (tr (fl a) (h ▸ sy (fr b)))
  have finj : Function.Injective f := by
    rintro (a | a) (b | b) h
    · fin_cases a <;> fin_cases b <;> simp_all [f]
    · exact absurd h (hlr _ _)
    · exact absurd h.symm (hlr _ _)
    · fin_cases a <;> fin_cases b <;> simp_all [f]
  have fbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨finj, by simp⟩
  have hrr : ∀ a b, ¬ S (f (.inr a)) (f (.inr b)) := fun a b h =>
    hn (ss s0 (se (es (fr a) h) (sy (fr b))))
  refine ⟨Equiv.ofBijective f fbij, fun a b h => h0 (se (es (fl a) h) (sy (fl b))), hrr,
    fun a b => se (es (sy (fl a)) s0) (fr b), fun a b => ?_⟩
  obtain ⟨k, hk⟩ := ex (f (.inr a))
  obtain ⟨c | c, rfl⟩ := fbij.2 k
  · exact se hk (tr (sy (fl c)) (fl b))
  · exact absurd hk (hrr _ _)

private def Rel {K G : Type} [Field K] [Group G] (r : G →* Matrix (Fin 4) (Fin 4) K) (N : Subgroup G)
    (g : G) (i j : Fin 4) : Prop := ∃ n ∈ N, r (g * n) i j ≠ 0

section
variable {K G : Type} [Field K] [Group G] {r : G →* Matrix (Fin 4) (Fin 4) K} {N : Subgroup G}

private theorem rel_of (g : G) {i j : Fin 4} (h : r g i j ≠ 0) : Rel r N g i j :=
  ⟨1, N.one_mem, by simpa using h⟩

private theorem rel_comp [hN : N.Normal] {t : G} (ht : t ∈ N) {d : Fin 4 → K} (hd : Function.Injective d)
    (htd : r t = diagonal d) {g h : G} {i j k : Fin 4} (h1 : Rel r N g i j) (h2 : Rel r N h j k) :
    Rel r N (g * h) i k := by
  obtain ⟨n, hn, h1⟩ := h1
  obtain ⟨n', hn', h2⟩ := h2
  by_contra hc
  have h3 : (fun l => r (g * n) i l * r (h * n') l k) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hd
    intro m
    by_contra h4
    apply hc
    refine ⟨h⁻¹ * (n * t ^ (m : ℕ)) * h * n', N.mul_mem (hN.conj_mem' _ (N.mul_mem hn (N.pow_mem ht _)) _) hn', ?_⟩
    have h5 : g * h * (h⁻¹ * (n * t ^ (m : ℕ)) * h * n') = g * n * t ^ (m : ℕ) * (h * n') := by group
    rw [h5, map_mul r _ (h * n'), map_mul r (g * n), map_pow, htd, Matrix.diagonal_pow, Matrix.mul_apply]
    convert h4 using 2 with l
    rw [Matrix.mul_diagonal, Pi.pow_apply]; ring
  exact mul_ne_zero h1 h2 (congrFun h3 j)

private theorem rel_congr {g h : G} (hgh : g⁻¹ * h ∈ N) {i j : Fin 4} (h1 : Rel r N h i j) : Rel r N g i j := by
  obtain ⟨n, hn, h1⟩ := h1
  refine ⟨g⁻¹ * h * n, N.mul_mem hgh hn, ?_⟩
  rwa [show g * (g⁻¹ * h * n) = h * n by group]

private theorem rel_span (hs : Submodule.span K (Set.range r) = ⊤) (i j : Fin 4) : ∃ g, r g i j ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 : ∀ x ∈ Submodule.span K (Set.range r), x i j = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hc g
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have := h1 (Matrix.of fun _ _ => 1) (hs ▸ Submodule.mem_top)
  simp at this

private theorem rel_ex (g : G) (i : Fin 4) : ∃ j, r g i j ≠ 0 ∧ r g⁻¹ j i ≠ 0 := by
  have h1 : (r g * r g⁻¹) i i ≠ 0 := by rw [← map_mul]; simp
  rw [Matrix.mul_apply] at h1
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  exact ⟨j, left_ne_zero_of_mul hj, right_ne_zero_of_mul hj⟩

private theorem rel_symm [hN : N.Normal] [N.FiniteIndex] {t : G} (ht : t ∈ N) {d : Fin 4 → K}
    (hd : Function.Injective d) (htd : r t = diagonal d) (hs : Submodule.span K (Set.range r) = ⊤)
    {g : G} {i j : Fin 4} (h1 : Rel r N g i j) : Rel r N g⁻¹ j i := by
  obtain ⟨h, hh⟩ := rel_span hs j i
  have h2 : Rel r N h j i := rel_of h hh
  have h3 : Rel r N (g * h) i i := rel_comp ht hd htd h1 h2
  have h4 : ∀ m : ℕ, Rel r N (h * (g * h) ^ m) j i := by
    intro m
    induction m with
    | zero => simpa using h2
    | succ m ih => rw [pow_succ, ← mul_assoc]; exact rel_comp ht hd htd ih h3
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := N))
  refine rel_congr ?_ (h4 m)
  have := N.pow_index_mem (g * h)
  rw [hm, pow_succ'] at this
  rwa [inv_inv, ← mul_assoc]

private theorem rel_partner [hN : N.Normal] [N.FiniteIndex] {t : G} (ht : t ∈ N) {d : Fin 4 → K}
    (hd : Function.Injective d) (htd : r t = diagonal d) (hs : Submodule.span K (Set.range r) = ⊤)
    (hc : ∃ g ∈ N, ∃ h ∈ N, r g * r h ≠ r h * r g) (i : Fin 4) : ∃ j, j ≠ i ∧ Rel r N 1 i j := by
  have h0 : ∃ j k, j ≠ k ∧ Rel r N 1 j k := by
    by_contra h
    push Not at h
    have hdiag : ∀ n ∈ N, r n = diagonal (fun i => r n i i) := by
      intro n hn
      ext j k
      by_cases hjk : j = k
      · subst hjk; simp
      · rw [Matrix.diagonal_apply_ne _ hjk]
        by_contra h1
        exact h j k hjk ⟨n, hn, by simpa using h1⟩
    obtain ⟨g, hg, g', hg', hne⟩ := hc
    apply hne
    rw [hdiag g hg, hdiag g' hg', Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    simp only [mul_comm]
  obtain ⟨j, k, hjk, hE⟩ := h0
  by_contra h
  push Not at h
  obtain ⟨g, hg⟩ := rel_span hs j i
  have hj : Rel r N g j i := rel_of g hg
  have hk : Rel r N g k i := by
    have := rel_comp ht hd htd (rel_symm ht hd htd hs hE) hj
    simpa using this
  have key : ∀ a, Rel r N g a i → ∀ l, r g a l ≠ 0 → l = i := by
    intro a ha l hl
    by_contra hli
    have := rel_comp ht hd htd (rel_symm ht hd htd hs ha) (rel_of (N := N) g hl)
    exact h l hli (by simpa using this)
  obtain ⟨l, hl1, hl2⟩ := rel_ex (r := r) g k
  have hli := key k hk l hl1
  subst hli
  have h1 : (r g * r g⁻¹) j k = 0 := by rw [← map_mul]; simp [hjk]
  rw [Matrix.mul_apply, Finset.sum_eq_single l] at h1
  · exact mul_ne_zero hg hl2 h1
  · intro b _ hb
    have : r g j b = 0 := by
      by_contra h2
      exact hb (key j hj b h2)
    rw [this, zero_mul]
  · simp

private theorem rel_cases [hN : N.Normal] [N.FiniteIndex] {t : G} (ht : t ∈ N) {d : Fin 4 → K}
    (hd : Function.Injective d) (htd : r t = diagonal d) (hs : Submodule.span K (Set.range r) = ⊤)
    (hc : ∃ g ∈ N, ∃ h ∈ N, r g * r h ≠ r h * r g) (σ : G) :
    (∀ i, Rel r N σ i i) ∨ ∃ e : Fin 2 ⊕ Fin 2 ≃ Fin 4,
      (∀ i j, ¬ Rel r N σ (e (.inl i)) (e (.inl j))) ∧ (∀ i j, ¬ Rel r N σ (e (.inr i)) (e (.inr j))) ∧
      (∀ i j, Rel r N σ (e (.inl i)) (e (.inr j))) ∧ (∀ i j, Rel r N σ (e (.inr i)) (e (.inl j))) := by
  by_cases h : ∀ i, Rel r N σ i i
  · exact Or.inl h
  push Not at h
  obtain ⟨i0, h0⟩ := h
  refine Or.inr (comb (Rel r N 1) (Rel r N σ) (fun i => rel_of 1 (by simp)) ?_ ?_ ?_ ?_ ?_ ?_
    (rel_partner ht hd htd hs hc) i0 h0)
  · intro i j h; simpa using rel_symm ht hd htd hs h
  · intro i j k h h'; simpa using rel_comp ht hd htd h h'
  · intro i j k h h'; simpa using rel_comp ht hd htd h h'
  · intro i j k h h'; simpa using rel_comp ht hd htd h h'
  · intro i j k h h'; simpa using rel_comp ht hd htd h (rel_symm ht hd htd hs h')
  · intro i
    obtain ⟨j, hj, -⟩ := rel_ex (r := r) σ i
    exact ⟨j, rel_of σ hj⟩

end

private theorem det_ne {K G : Type} [Field K] [Group G] (r : G →* Matrix (Fin 4) (Fin 4) K) (g : G) :
    (r g).det ≠ 0 := by
  have h : (r g).det * (r g⁻¹).det = 1 := by rw [← Matrix.det_mul, ← map_mul]; simp
  exact left_ne_zero_of_mul_eq_one h

private theorem adj_eq {K G : Type} [Field K] [Group G] (r : G →* Matrix (Fin 4) (Fin 4) K) (g : G) :
    (r g).adjugate = (r g).det • r g⁻¹ := by
  have h : r g * r g⁻¹ = 1 := by rw [← map_mul]; simp
  calc (r g).adjugate = (r g).adjugate * (r g * r g⁻¹) := by rw [h, Matrix.mul_one]
    _ = (r g).det • r g⁻¹ := by rw [← Matrix.mul_assoc, Matrix.adjugate_mul]; simp

private theorem eval_adj {K : Type} [Field K] (x : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) :
    MvPolynomial.eval (fun p : Fin 4 × Fin 4 => x p.1 p.2)
      ((Matrix.mvPolynomialX (Fin 4) (Fin 4) K).adjugate i i) = x.adjugate i i := by
  have h := congrFun (congrFun (RingHom.map_adjugate (MvPolynomial.eval (fun p : Fin 4 × Fin 4 => x p.1 p.2))
    (Matrix.mvPolynomialX (Fin 4) (Fin 4) K)) i) i
  rw [Matrix.mvPolynomialX_mapMatrix_eval] at h
  exact h

private theorem core (K G : Type) [Field K] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (h2 : (2 : K) ≠ 0)
    (r : G →* Matrix (Fin 4) (Fin 4) K)
    (hcl : ∀ f : MvPolynomial (Fin 4 × Fin 4) K, IsClosed {g | MvPolynomial.eval (fun p => r g p.1 p.2) f = 0})
    (hs : Submodule.span K (Set.range r) = ⊤) (u : G) (a : Fin 4 → Kˣ) (hu : r u = diagonal fun i => (a i : K))
    (ha : ∀ i j, i ≠ j → ¬ IsOfFinOrder (a i / a j))
    (hc : ∀ N : Subgroup G, IsOpen (N : Set G) → N.Normal → N.FiniteIndex → ∃ g ∈ N, ∃ h ∈ N, r g * r h ≠ r h * r g)
    (U : Subgroup G) (hU : U.FiniteIndex) (σ : G) : ∃ g ∈ U, (r (σ * g)).charpoly.Separable := by
  classical
  obtain ⟨N, hN, hNf, ⟨I, hI⟩, hirr⟩ := UpperTheory.V.AlgebraTools.idCompMat K G (Fin 4) r
  have hclosed : IsClosed (N : Set G) := by
    have : (N : Set G) = ⋂ f ∈ I, {g | MvPolynomial.eval (fun p => r g p.1 p.2) f = 0} := by
      ext g; simp [hI]
    rw [this]
    exact isClosed_biInter fun f _ => hcl f
  have hcN := hc N (N.isOpen_of_isClosed_of_finiteIndex hclosed) hN hNf
  obtain ⟨k, hk0, -, hk⟩ := (U ⊓ N).exists_pow_mem_of_index_ne_zero Subgroup.FiniteIndex.index_ne_zero u
  have hb : ∀ i j, i ≠ j → ¬ IsOfFinOrder (a i ^ k / a j ^ k) := by
    intro i j hij h
    rw [← div_pow] at h
    exact ha i j hij (h.of_pow hk0.ne')
  have hd : Function.Injective fun i => ((a i ^ k : Kˣ) : K) := by
    intro i j hij
    by_contra h
    apply hb i j h
    rw [Units.ext hij, div_self']
    exact IsOfFinOrder.one
  have htd : r (u ^ k) = diagonal fun i => ((a i ^ k : Kˣ) : K) := by
    rw [map_pow, hu, Matrix.diagonal_pow]; congr 1
  obtain ⟨w, hw, hwr⟩ := UpperTheory.V.AlgebraTools.relWeight Kˣ (Fin 4) (fun i => a i ^ k) hb
  have main : ∃ g ∈ U, ((r (σ * g)).map (algebraMap K (RatFunc K)) *
      diagonal (fun i => (RatFunc.X : RatFunc K) ^ w i)).charpoly.Separable := by
    rcases rel_cases hk.2 hd htd hs hcN σ with h | ⟨e, h11, h22, h12, h21⟩
    · obtain ⟨g, hg, hf⟩ := hirr U hU σ
        (Finset.univ.image (fun i : Fin 4 => MvPolynomial.X (i, i)) ∪
          Finset.univ.image (fun i : Fin 4 => (Matrix.mvPolynomialX (Fin 4) (Fin 4) K).adjugate i i)) (by
        intro f hf
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hf
        rcases hf with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · obtain ⟨n, hn, h1⟩ := h i
          exact ⟨n, hn, by simpa using h1⟩
        · obtain ⟨n, hn, h1⟩ := rel_symm hk.2 hd htd hs (h i)
          refine ⟨σ⁻¹ * n⁻¹ * σ, hN.conj_mem' _ (N.inv_mem hn) σ, ?_⟩
          rw [eval_adj, adj_eq, show (σ * (σ⁻¹ * n⁻¹ * σ))⁻¹ = σ⁻¹ * n by group]
          exact mul_ne_zero (det_ne r _) h1)
      refine ⟨g, hg.1, sepA h2 _ w hw (fun i => ?_) (fun i => ?_)⟩
      · simpa using hf (MvPolynomial.X (i, i))
          (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      · rw [← eval_adj]
        exact hf _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    · obtain ⟨g, hg, hf⟩ := hirr U hU σ
        ((Finset.univ.filter fun p : Fin 4 × Fin 4 => Rel r N σ p.1 p.2).image MvPolynomial.X) (by
        intro f hf
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        obtain ⟨p, ⟨n, hn, h1⟩, rfl⟩ := hf
        exact ⟨n, hn, by simpa using h1⟩)
      have hf' : ∀ i j, Rel r N σ i j → r (σ * g) i j ≠ 0 := fun i j hij => by
        simpa using hf (MvPolynomial.X (i, j)) (Finset.mem_image_of_mem _ (by simpa using hij))
      have hf'' : ∀ i j, ¬ Rel r N σ i j → r (σ * g) i j = 0 := fun i j hij => by
        by_contra h; exact hij ⟨g, hg.2, h⟩
      exact ⟨g, hg.1, sepB h2 _ w hw e (det_ne r _) (fun i j => hf'' _ _ (h11 i j)) (fun i j => hf'' _ _ (h22 i j))
        (fun i j => hf' _ _ (h12 i j)) (fun i j => hf' _ _ (h21 i j))⟩
  obtain ⟨g, hg, hsep⟩ := main
  obtain ⟨m, hm⟩ := UpperTheory.V.AlgebraTools.torusTransfer K (Fin 4) _ (fun i => a i ^ k) w hwr hsep
  refine ⟨g * (u ^ k) ^ m, U.mul_mem hg (U.pow_mem hk.1 m), ?_⟩
  rw [← mul_assoc, map_mul, map_pow, htd, Matrix.diagonal_pow]
  exact hm

end UpperTheory.V.AlgebraTools.RegFour

theorem UpperTheory.V.AlgebraTools.regCosetFour :
    ∀ (K G : Type) [Field K] [IsAlgClosed K] [Group G] [TopologicalSpace G] [IsTopologicalGroup G], (2 : K) ≠ 0 →
      ∀ (r : G →* Matrix (Fin 4) (Fin 4) K),
      (∀ f : MvPolynomial (Fin 4 × Fin 4) K, IsClosed {g | MvPolynomial.eval (fun p => r g p.1 p.2) f = 0}) →
      Submodule.span K (Set.range r) = ⊤ →
      (∃ (u : G) (a : Fin 4 → Kˣ), (r u).charpoly = ∏ i, (X - C (a i : K)) ∧ ∀ i j, i ≠ j → ¬ IsOfFinOrder (a i / a j)) →
      (∀ N : Subgroup G, IsOpen (N : Set G) → N.Normal → N.FiniteIndex → ∃ g ∈ N, ∃ h ∈ N, r g * r h ≠ r h * r g) →
      ∀ U : Subgroup G, U.FiniteIndex → ∀ σ : G, ∃ g ∈ U, (r (σ * g)).charpoly.Separable := by
  intro K G _ _ _ _ _ h2 r hcl hs ⟨u, a, hu, ha⟩ hc U hU σ
  have hinj : Function.Injective fun i => (a i : K) := by
    intro i j hij
    by_contra h
    apply ha i j h
    rw [Units.ext hij, div_self']
    exact IsOfFinOrder.one
  obtain ⟨P, Q, hPQ, hQP, hD⟩ := RegFour.diagz (r u) _ hinj hu
  have hmul : ∀ x y : Matrix (Fin 4) (Fin 4) K, Q * (x * y) * P = Q * x * P * (Q * y * P) := by
    intro x y
    calc Q * (x * y) * P = Q * x * (P * Q) * y * P := by rw [hPQ]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hback : ∀ x : Matrix (Fin 4) (Fin 4) K, P * (Q * x * P) * Q = x := by
    intro x
    calc P * (Q * x * P) * Q = (P * Q) * x * (P * Q) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hPQ]; simp
  let r' : G →* Matrix (Fin 4) (Fin 4) K :=
    { toFun := fun g => Q * r g * P
      map_one' := by simp [hQP]
      map_mul' := fun g h => by rw [map_mul, hmul] }
  have hr' : ∀ g, r' g = Q * r g * P := fun _ => rfl
  refine Exists.imp ?_ (RegFour.core K G h2 r' ?_ ?_ u a hD ha ?_ U hU σ)
  · rintro g ⟨hg, hsep⟩
    refine ⟨hg, ?_⟩
    rwa [hr', Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hPQ, Matrix.one_mul] at hsep
  · intro f
    convert hcl (MvPolynomial.bind₁ (fun p : Fin 4 × Fin 4 =>
      ∑ l, (∑ k, MvPolynomial.C (Q p.1 k) * MvPolynomial.X (k, l)) * MvPolynomial.C (P l p.2)) f) using 4 with g
    rw [← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]
    simp only [RingHom.coe_coe, MvPolynomial.aeval_bind₁]
    congr 2
    funext p
    simp [hr', Matrix.mul_apply]
  · rw [eq_top_iff]
    intro x _
    have h1 : ∀ y ∈ Submodule.span K (Set.range r), Q * y * P ∈ Submodule.span K (Set.range r') := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => obtain ⟨g, rfl⟩ := hy; exact Submodule.subset_span ⟨g, rfl⟩
      | zero => simp
      | add y z _ _ hy hz => rw [Matrix.mul_add, Matrix.add_mul]; exact Submodule.add_mem _ hy hz
      | smul c y _ hy => rw [Matrix.mul_smul, Matrix.smul_mul]; exact Submodule.smul_mem _ c hy
    have h3 := h1 (P * x * Q) (hs ▸ Submodule.mem_top)
    rwa [show Q * (P * x * Q) * P = (Q * P) * x * (Q * P) by simp only [Matrix.mul_assoc], hQP,
      Matrix.one_mul, Matrix.mul_one] at h3
  · intro N h1 h3 h4
    obtain ⟨g, hg, h, hh, hne⟩ := hc N h1 h3 h4
    refine ⟨g, hg, h, hh, fun h5 => hne ?_⟩
    rw [hr', hr', ← hmul, ← hmul] at h5
    rw [← hback (r g * r h), h5, hback]
