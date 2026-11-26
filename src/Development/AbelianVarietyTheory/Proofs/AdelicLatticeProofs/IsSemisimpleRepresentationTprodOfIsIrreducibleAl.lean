module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsConjHarmOfSpan
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsConjHarmOfSpanStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompletelyReducibleKroneckerOfSpanEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsometryMatrixRange
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TraceLogLeLogDet
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.LogCompress

theorem jensen_exp {ι : Type} [Fintype ι] (w d : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (h1 : ∑ j, w j = 1) :
    0 < ∑ j, w j * Real.exp (d j) ∧ ∑ j, w j * d j ≤ Real.log (∑ j, w j * Real.exp (d j)) ∧
      (∑ j, w j * d j = Real.log (∑ j, w j * Real.exp (d j)) →
        ∀ j, w j ≠ 0 → Real.exp (d j) = ∑ j, w j * Real.exp (d j)) := by
  set m := ∑ j, w j * Real.exp (d j) with hm
  have hpos : 0 < m := by
    obtain ⟨j, -, hj⟩ : ∃ j ∈ (Finset.univ : Finset ι), w j ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [h1]; exact one_ne_zero)
    exact Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le)
      ⟨j, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hw j) hj.symm) (Real.exp_pos _)⟩
  have hexp : ∀ j, Real.exp (d j - Real.log m) = Real.exp (d j) / m := by
    intro j
    rw [Real.exp_sub, Real.exp_log hpos]
  have hnn : ∀ j ∈ (Finset.univ : Finset ι),
      0 ≤ w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1)) :=
    fun j _ => mul_nonneg (hw j) (sub_nonneg.2 (Real.add_one_le_exp _))
  have hsum : ∑ j, w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1))
      = Real.log m - ∑ j, w j * d j := by
    have : ∀ j, w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1))
        = w j * Real.exp (d j) / m - w j * d j + w j * (Real.log m - 1) := by
      intro j
      rw [hexp]; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
      ← Finset.sum_mul, h1, ← hm, div_self hpos.ne']
    ring
  refine ⟨hpos, ?_, ?_⟩
  · have := Finset.sum_nonneg hnn
    linarith
  · intro h j hj
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by rw [hsum, h, sub_self]) j
      (Finset.mem_univ _)
    have h2 := (mul_eq_zero.1 h0).resolve_left hj
    have h3 : d j - Real.log m = 0 := by
      by_contra hne
      have := Real.add_one_lt_exp hne
      linarith
    have h4 : d j = Real.log m := by linarith
    rw [h4, Real.exp_log hpos]

theorem compress_diag {ι κ : Type} [Fintype ι] [DecidableEq ι] (C : Matrix ι κ ℂ) (f : ι → ℝ) (k : κ) :
    (Cᴴ * diagonal (fun i => (f i : ℂ)) * C) k k = ((∑ j, Complex.normSq (C j k) * f j : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  ring

theorem exists_diag {κ : Type} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ ℂ) (hB : B.IsHermitian) :
    ∃ (V : Matrix κ κ ℂ) (m : κ → ℂ), V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧ Vᴴ * B * V = diagonal m := by
  refine ⟨hB.eigenvectorUnitary, RCLike.ofReal ∘ hB.eigenvalues, ?_, ?_, ?_⟩
  · exact (Matrix.mem_unitaryGroup_iff.1 hB.eigenvectorUnitary.2)
  · exact (Matrix.mem_unitaryGroup_iff'.1 hB.eigenvectorUnitary.2)
  · have := hB.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this

theorem trace_log_le_log_det : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (H A : Matrix ι ι ℂ) (Q : Matrix ι κ ℂ), IsLog H A → Qᴴ * Q = 1 → (Matrix.trace (Qᴴ * H * Q)).re ≤ Real.log (Qᴴ * A * Q).det.re ∧ ((Matrix.trace (Qᴴ * H * Q)).re = Real.log (Qᴴ * A * Q).det.re → ∃ N : Matrix κ κ ℂ, A * Q = Q * N) := by
  intro ι _ _ κ _ _ H A Q ⟨U, d, hU, hH, hA⟩ hQ
  have hAh : A.IsHermitian := by
    rw [hA]
    refine Matrix.isHermitian_mul_mul_conjTranspose _ ?_
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    exact Complex.conj_ofReal _
  obtain ⟨V, m, hV, hV', hm⟩ := exists_diag _ (Matrix.isHermitian_conjTranspose_mul_mul Q hAh)
  set C : Matrix ι κ ℂ := Uᴴ * Q * V with hC
  have hCH : Cᴴ = Vᴴ * Qᴴ * U := by
    simp [hC, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have key : ∀ D : Matrix ι ι ℂ, Cᴴ * D * C = Vᴴ * (Qᴴ * (U * D * Uᴴ) * Q) * V := by
    intro D
    rw [hCH, hC]
    simp only [Matrix.mul_assoc]
  have hw : ∀ k, ∑ j, Complex.normSq (C j k) = 1 := by
    intro k
    have h := compress_diag C (fun _ => 1) k
    have h1 : diagonal (fun _ : ι => ((1 : ℝ) : ℂ)) = 1 := by simp
    rw [key, h1, Matrix.mul_one, hU, Matrix.mul_one, hQ, Matrix.mul_one, hV'] at h
    simp only [Matrix.one_apply_eq, mul_one] at h
    exact_mod_cast h.symm
  have hmk : ∀ k, m k = ((∑ j, Complex.normSq (C j k) * Real.exp (d j) : ℝ) : ℂ) := by
    intro k
    rw [← compress_diag C (fun j => Real.exp (d j)) k, key, ← hA, hm, Matrix.diagonal_apply_eq]
  have hJ := fun k => jensen_exp (fun j => Complex.normSq (C j k)) d
    (fun j => Complex.normSq_nonneg _) (hw k)
  have hdet : (Qᴴ * A * Q).det.re = ∏ k, ∑ j, Complex.normSq (C j k) * Real.exp (d j) := by
    have h := congrArg Matrix.det hm
    rw [Matrix.det_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.det_diagonal] at h
    rw [h]
    simp only [hmk]
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  have htr : (Matrix.trace (Qᴴ * H * Q)).re = ∑ k, ∑ j, Complex.normSq (C j k) * d j := by
    have h : Matrix.trace (Cᴴ * diagonal (fun i => (d i : ℂ)) * C) = Matrix.trace (Qᴴ * H * Q) := by
      rw [key, ← hH, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]
    rw [← h, Matrix.trace]
    simp only [Matrix.diag_apply, compress_diag]
    rw [← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hdet, htr, Real.log_prod (fun k _ => (hJ k).1.ne')]
  refine ⟨Finset.sum_le_sum fun k _ => (hJ k).2.1, fun h => ?_⟩
  have heq := (Finset.sum_eq_sum_iff_of_le fun k _ => (hJ k).2.1).1 h
  have hDC : diagonal (fun i => (Real.exp (d i) : ℂ)) * C = C * diagonal m := by
    ext j k
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases h0 : C j k = 0
    · simp [h0]
    · have := (hJ k).2.2 (heq k (Finset.mem_univ _)) j (by simpa using h0)
      rw [hmk, ← this, mul_comm]
  refine ⟨V * diagonal m * Vᴴ, ?_⟩
  have h1 : A * Q = U * (diagonal (fun i => (Real.exp (d i) : ℂ)) * C) * Vᴴ := by
    rw [hA, hC]
    simp only [Matrix.mul_assoc, hV, Matrix.mul_one]
  rw [h1, hDC, hC]
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]

end GlobalTheory.LogCompress
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_isometry_matrix_range {ι : Type} [Fintype ι] [DecidableEq ι] (W : Submodule ℂ (ι → ℂ)) :
    ∃ (n : ℕ) (Q : Matrix ι (Fin n) ℂ), Qᴴ * Q = 1 ∧ ∀ v, v ∈ W ↔ ∃ x, v = Q *ᵥ x := by
  let W' : Submodule ℂ (EuclideanSpace ℂ ι) := W.comap (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap
  let b := stdOrthonormalBasis ℂ W'
  refine ⟨_, Matrix.of fun i j => (b j : EuclideanSpace ℂ ι) i, ?_, ?_⟩
  · ext j k
    have h := orthonormal_iff_ite.mp b.orthonormal j k
    rw [Submodule.coe_inner, PiLp.inner_apply] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  · intro v
    constructor
    · intro hv
      let w : W' := ⟨WithLp.toLp 2 v, hv⟩
      refine ⟨fun j => b.repr w j, ?_⟩
      ext i
      have h := congrArg (fun z : W' => (z : EuclideanSpace ℂ ι) i) (b.sum_repr w)
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
      have h2 : v i = (w : EuclideanSpace ℂ ι) i := rfl
      rw [h2, ← h]
      simp [Matrix.mulVec, dotProduct, mul_comm]
    · rintro ⟨x, rfl⟩
      have h : (Matrix.of fun i j => (b j : EuclideanSpace ℂ ι) i) *ᵥ x
          = ∑ j, x j • (b j : EuclideanSpace ℂ ι).ofLp := by
        ext i
        simp [Matrix.mulVec, dotProduct, mul_comm]
      rw [h]
      exact W.sum_mem fun j _ => W.smul_mem _ (b j).2

theorem ss_of_harm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (τ : σ ≃ σ)
    (g : σ → Matrix ι ι ℂ), (∀ s, g (τ s) * g s = 1) → Harm g → SS (Set.range g) := by
  intro ι _ _ σ _ τ g hτ hH W hW
  obtain ⟨H, hlog, hsum⟩ := hH
  obtain ⟨n, Q, hQ, hmem⟩ := exists_isometry_matrix_range W
  have hN : ∀ s, ∃ N : Matrix (Fin n) (Fin n) ℂ, g s * Q = Q * N := by
    intro s
    have : ∀ j : Fin n, ∃ x, g s *ᵥ (Q *ᵥ Pi.single j 1) = Q *ᵥ x := fun j =>
      (hmem _).1 (hW _ ⟨s, rfl⟩ _ ((hmem _).2 ⟨_, rfl⟩))
    choose x hx using this
    refine ⟨Matrix.of fun i j => x j i, ?_⟩
    ext i j
    have h := congrFun (hx j) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    exact h
  choose N hN using hN
  have hNinv : ∀ s, N (τ s) * N s = 1 := by
    intro s
    have h : Q * (N (τ s) * N s) = Q := by
      rw [← Matrix.mul_assoc, ← hN, Matrix.mul_assoc, ← hN, ← Matrix.mul_assoc, hτ, Matrix.one_mul]
    have h2 := congrArg (fun X => Qᴴ * X) h
    simpa only [← Matrix.mul_assoc, hQ, Matrix.one_mul] using h2
  have hdet : ∀ s, (Qᴴ * ((g s)ᴴ * g s) * Q).det.re = Complex.normSq (N s).det := by
    intro s
    have h : Qᴴ * ((g s)ᴴ * g s) * Q = (N s)ᴴ * N s := by
      calc Qᴴ * ((g s)ᴴ * g s) * Q = (g s * Q)ᴴ * (g s * Q) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (N s)ᴴ * (Qᴴ * Q) * N s := by
            rw [hN]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hQ, Matrix.mul_one]
    rw [h, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  set a : σ → ℝ := fun s => Real.log (Complex.normSq (N s).det) with ha
  have hpair : ∀ s, a (τ s) + a s = 0 := by
    intro s
    have h : Complex.normSq (N (τ s)).det * Complex.normSq (N s).det = 1 := by
      rw [← map_mul, ← Matrix.det_mul, hNinv, Matrix.det_one, map_one]
    simp only [ha]
    rw [← Real.log_mul (left_ne_zero_of_mul_eq_one h) (right_ne_zero_of_mul_eq_one h), h, Real.log_one]
  have hasum : ∑ s, a s = 0 := by
    have h : ∑ s, (a (τ s) + a s) = 0 := Finset.sum_eq_zero fun s _ => hpair s
    rw [Finset.sum_add_distrib, Equiv.sum_comp τ a] at h
    linarith
  have htsum : ∑ s, (Matrix.trace (Qᴴ * H s * Q)).re = 0 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, ← Matrix.mul_sum, hsum]
    simp
  have hJ := fun s => GlobalTheory.LogCompress.trace_log_le_log_det ι (Fin n) (H s) ((g s)ᴴ * g s) Q (hlog s) hQ
  have heq : ∀ s, (Matrix.trace (Qᴴ * H s * Q)).re = a s := by
    have h := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := fun s => (Matrix.trace (Qᴴ * H s * Q)).re) (g := a)
      (fun s _ => by have := (hJ s).1; rwa [hdet] at this)).1 (by rw [htsum, hasum])
    exact fun s => h s (Finset.mem_univ s)
  have hadj : ∀ s, ∃ M : Matrix (Fin n) (Fin n) ℂ, Qᴴ * g s = M * Qᴴ := by
    intro s
    obtain ⟨M, hM⟩ := (hJ s).2 (by rw [hdet]; exact heq s)
    have h1 : N s * N (τ s) = 1 := mul_eq_one_comm.1 (hNinv s)
    have h2 : (g s)ᴴ * Q = Q * (M * N (τ s)) := by
      rw [← Matrix.mul_assoc, ← hM, Matrix.mul_assoc (g s)ᴴ, hN, Matrix.mul_assoc, Matrix.mul_assoc, h1,
        Matrix.mul_one]
    refine ⟨(M * N (τ s))ᴴ, ?_⟩
    have h3 := congrArg Matrix.conjTranspose h2
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul Q] at h3
  refine ⟨LinearMap.ker (Matrix.mulVecLin Qᴴ), ?_, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩ v hv
    obtain ⟨M, hM⟩ := hadj s
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨x, rfl⟩ := (hmem v).1 hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec] at hv'
    rw [hv', Matrix.mulVec_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    refine Submodule.mem_sup.2 ⟨Q *ᵥ (Qᴴ *ᵥ v), (hmem _).2 ⟨_, rfl⟩, v - Q *ᵥ (Qᴴ *ᵥ v), ?_, by abel⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, Matrix.mulVec_mulVec (Qᴴ *ᵥ v), hQ,
      Matrix.one_mulVec, sub_self]

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsLogKronecker
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem isLog_kronecker {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} [Fintype κ] [DecidableEq κ]
    {H A : Matrix ι ι ℂ} {H' A' : Matrix κ κ ℂ} (h : IsLog H A) (h' : IsLog H' A') :
    IsLog (H ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ H') (A ⊗ₖ A') := by
  obtain ⟨U, d, hU, rfl, rfl⟩ := h
  obtain ⟨U', d', hU', rfl, rfl⟩ := h'
  refine ⟨U ⊗ₖ U', fun p => d p.1 + d' p.2, ?_, ?_, ?_⟩
  · rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU, hU', one_kronecker_one]
  · have e : (diagonal (fun p : ι × κ => ((d p.1 + d' p.2 : ℝ) : ℂ))) =
        diagonal (fun i => (d i : ℂ)) ⊗ₖ (1 : Matrix κ κ ℂ) +
          (1 : Matrix ι ι ℂ) ⊗ₖ diagonal (fun i => (d' i : ℂ)) := by
      rw [← diagonal_one, ← diagonal_one, diagonal_kronecker_diagonal, diagonal_kronecker_diagonal,
        diagonal_add]
      congr 1
      funext p
      rw [Complex.ofReal_add, mul_one, one_mul]
    rw [e, conjTranspose_kronecker, Matrix.mul_add, Matrix.add_mul, ← mul_kronecker_mul,
      ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.mul_one,
      hU, hU']
  · have e : (diagonal (fun p : ι × κ => ((Real.exp (d p.1 + d' p.2) : ℝ) : ℂ))) =
        diagonal (fun i => (Real.exp (d i) : ℂ)) ⊗ₖ diagonal (fun i => (Real.exp (d' i) : ℂ)) := by
      rw [diagonal_kronecker_diagonal]
      congr 1
      funext p
      rw [Real.exp_add, Complex.ofReal_mul]
    rw [e, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

theorem harm_kronecker : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ) (g' : σ → Matrix κ κ ℂ), Harm g → Harm g' → Harm (fun s => g s ⊗ₖ g' s) := by
  intro ι _ _ κ _ _ σ _ g g' ⟨H, hH, hs⟩ ⟨H', hH', hs'⟩
  refine ⟨fun s => H s ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ H' s, fun s => ?_, ?_⟩
  · have := isLog_kronecker (hH s) (hH' s)
    simpa only [conjTranspose_kronecker, ← mul_kronecker_mul] using this
  · ext ⟨i, k⟩ ⟨j, l⟩
    have h1 : ∑ s, H s i j = 0 := by
      have := congrFun (congrFun hs i) j
      simpa [Matrix.sum_apply] using this
    have h2 : ∑ s, H' s k l = 0 := by
      have := congrFun (congrFun hs' k) l
      simpa [Matrix.sum_apply] using this
    simp only [Matrix.sum_apply, Matrix.add_apply, kroneckerMap_apply, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, h1, h2, Matrix.zero_apply]
    simp

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SsTransfer
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem ss_transfer : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S Γ : Set (Matrix ι ι ℂ)), (S ⊆ Γ → Γ ⊆ (Submodule.span ℂ S : Set (Matrix ι ι ℂ)) → SS S → SS Γ) ∧ ∀ P : Matrix ι ι ℂ, IsUnit P.det → SS ((fun x => P * x * P⁻¹) '' S) → SS S := by
  intro ι _ _ S Γ
  refine ⟨fun h1 h2 hS W hW => ?_, fun P hP hS W hW => ?_⟩
  · obtain ⟨W', hW', hc⟩ := hS W (fun g hg => hW g (h1 hg))
    refine ⟨W', fun g hg v hv => ?_, hc⟩
    have hg' : g ∈ Submodule.span ℂ S := h2 hg
    clear hg
    induction hg' using Submodule.span_induction with
    | mem x hx => exact hW' x hx v hv
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact W'.add_mem hx hy
    | smul a x _ hx => rw [Matrix.smul_mulVec]; exact W'.smul_mem a hx
  · have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
    have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
    let e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ) :=
      { P.mulVecLin with
        invFun := fun v => P⁻¹ *ᵥ v
        left_inv := fun v => by simp [Matrix.mulVec_mulVec, h2]
        right_inv := fun v => by simp [Matrix.mulVec_mulVec, h1] }
    have he : ∀ v, e v = P *ᵥ v := fun v => rfl
    have key : ∀ (x : Matrix ι ι ℂ) (v : ι → ℂ), (P * x * P⁻¹) *ᵥ (P *ᵥ v) = P *ᵥ (x *ᵥ v) := by
      intro x v
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, h2, Matrix.mul_one]
    obtain ⟨W', hW', hc⟩ := hS (Submodule.orderIsoMapComap e W) (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨v, hv, rfl⟩
      exact ⟨x *ᵥ v, hW x hx v hv, (key x v).symm⟩)
    refine ⟨(Submodule.orderIsoMapComap e).symm W', fun g hg v hv => ?_, ?_⟩
    · have hv' : P *ᵥ v ∈ W' := hv
      have := hW' _ ⟨g, hg, rfl⟩ _ hv'
      rw [key] at this
      exact this
    · have := (Submodule.orderIsoMapComap e).symm.isCompl hc
      rwa [OrderIso.symm_apply_apply] at this

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompletelyReducibleKroneckerOfSpanEqTop
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_finset_span_image_eq {G V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : G → V) : ∃ T : Finset G, ∀ S : Set G, (T : Set G) ⊆ S →
      Submodule.span ℂ (f '' S) = Submodule.span ℂ (Set.range f) := by
  classical
  have h : (Submodule.span ℂ (Set.range f)).FG := Submodule.FG.of_finite
  obtain ⟨s, hs, hsp⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 h
  have hs' : (s : Set V) ⊆ f '' Set.univ := by simpa using hs
  obtain ⟨T, -, hT⟩ := Finset.subset_set_image_iff.1 hs'
  refine ⟨T, fun S hS => le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) ?_⟩
  rw [hsp, ← hT, Finset.coe_image]
  exact Submodule.span_mono (Set.image_mono hS)

theorem ss_kronecker_of_span_top : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Type) [Group G] (ρ : G →* Matrix ι ι ℂ) (ρ' : G →* Matrix κ κ ℂ), Submodule.span ℂ (Set.range ρ) = ⊤ → Submodule.span ℂ (Set.range ρ') = ⊤ → SS (Set.range fun g => ρ g ⊗ₖ ρ' g) := by
  intro ι _ _ κ _ _ G _ ρ ρ' h h'
  classical
  obtain ⟨T₁, h₁⟩ := exists_finset_span_image_eq (ρ : G → Matrix ι ι ℂ)
  obtain ⟨T₂, h₂⟩ := exists_finset_span_image_eq (ρ' : G → Matrix κ κ ℂ)
  obtain ⟨T₃, h₃⟩ := exists_finset_span_image_eq (fun g => ρ g ⊗ₖ ρ' g)
  set T : Finset G := T₁ ∪ T₂ ∪ T₃ with hT
  set S : Finset G := T ∪ T.image (fun g => g⁻¹) with hS
  have hinv : ∀ g ∈ S, g⁻¹ ∈ S := by
    intro g hg
    rw [hS, Finset.mem_union] at hg ⊢
    rcases hg with hg | hg
    · exact Or.inr (Finset.mem_image_of_mem _ hg)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hg
      exact Or.inl (by simpa using ha)
  let τ : S ≃ S :=
    { toFun := fun s => ⟨s.1⁻¹, hinv _ s.2⟩
      invFun := fun s => ⟨s.1⁻¹, hinv _ s.2⟩
      left_inv := fun s => Subtype.ext (inv_inv _)
      right_inv := fun s => Subtype.ext (inv_inv _) }
  have hτ : ∀ s : S, (τ s : G) = (s : G)⁻¹ := fun _ => rfl
  have e₁ := h₁ (S : Set G) (by intro x hx; simp [hS, hT, Finset.mem_coe.1 hx])
  have e₂ := h₂ (S : Set G) (by intro x hx; simp [hS, hT, Finset.mem_coe.1 hx])
  have e₃ := h₃ (S : Set G) (by intro x hx; simp [hS, hT, Finset.mem_coe.1 hx])
  rw [Set.image_eq_range] at e₁ e₂ e₃
  have i₁ : ∀ s : S, ρ (τ s : G) * ρ (s : G) = 1 := fun s => by
    rw [hτ, ← map_mul, inv_mul_cancel, map_one]
  have i₂ : ∀ s : S, ρ' (τ s : G) * ρ' (s : G) = 1 := fun s => by
    rw [hτ, ← map_mul, inv_mul_cancel, map_one]
  obtain ⟨P, hP, HP⟩ := GlobalTheory.T.exists_conj_harm_of_span' ι S τ (fun s => ρ (s : G)) i₁ (e₁.trans h)
  obtain ⟨Q, hQ, HQ⟩ := GlobalTheory.T.exists_conj_harm_of_span' κ S τ (fun s => ρ' (s : G)) i₂ (e₂.trans h')
  have HK := harm_kronecker ι κ S _ _ HP HQ
  have hPQ : IsUnit (P ⊗ₖ Q).det := by
    rw [det_kronecker]
    exact (hP.pow _).mul (hQ.pow _)
  have key : ∀ s : S, (P * ρ (s : G) * P⁻¹) ⊗ₖ (Q * ρ' (s : G) * Q⁻¹) =
      (P ⊗ₖ Q) * (ρ (s : G) ⊗ₖ ρ' (s : G)) * (P ⊗ₖ Q)⁻¹ := fun s => by
    rw [inv_kronecker, mul_kronecker_mul, mul_kronecker_mul]
  have conj : ∀ {n : Type} [Fintype n] [DecidableEq n] (A X Y : Matrix n n ℂ), IsUnit A.det → X * Y = 1 →
      (A * X * A⁻¹) * (A * Y * A⁻¹) = 1 := by
    intro n _ _ A X Y hA hXY
    calc (A * X * A⁻¹) * (A * Y * A⁻¹) = A * (X * (A⁻¹ * A) * Y) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul _ hA, Matrix.mul_one, hXY, Matrix.mul_one, mul_nonsing_inv _ hA]
  have hss := ss_of_harm (ι × κ) S τ _ (fun s => by
    show ((P * ρ (τ s : G) * P⁻¹) ⊗ₖ (Q * ρ' (τ s : G) * Q⁻¹)) *
      ((P * ρ (s : G) * P⁻¹) ⊗ₖ (Q * ρ' (s : G) * Q⁻¹)) = 1
    rw [← mul_kronecker_mul, conj _ _ _ hP (i₁ s), conj _ _ _ hQ (i₂ s), one_kronecker_one]) HK
  have hss' : SS (Set.range fun s : S => ρ (s : G) ⊗ₖ ρ' (s : G)) := by
    refine (ss_transfer (ι × κ) _ ∅).2 (P ⊗ₖ Q) hPQ ?_
    rw [← Set.range_comp]
    convert hss using 2
    funext s
    exact (key s).symm
  refine (ss_transfer (ι × κ) _ _).1 ?_ ?_ hss'
  · rintro _ ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  · intro x hx
    have : x ∈ Submodule.span ℂ (Set.range fun g => ρ g ⊗ₖ ρ' g) := Submodule.subset_span hx
    rw [← e₃] at this
    exact this

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompletelyReducibleKroneckerOfSpanEqTopStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompletelyReducible_kronecker_of_span_eq_top : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Type) [Group G] (ρ : G →* Matrix ι ι ℂ) (ρ' : G →* Matrix κ κ ℂ), Submodule.span ℂ (Set.range ρ) = ⊤ → Submodule.span ℂ (Set.range ρ') = ⊤ → SS (Set.range fun g => ρ g ⊗ₖ ρ' g) := by
  first | exact @GlobalTheory.ClassFin.ss_kronecker_of_span_top | exact GlobalTheory.ClassFin.ss_kronecker_of_span_top | (intros; apply GlobalTheory.ClassFin.ss_kronecker_of_span_top <;> assumption)
end
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem span_range_toMatrix_eq_top_of_isIrreducible {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (b : Module.Basis ι ℂ V) (h : ρ.IsIrreducible) :
    Submodule.span ℂ (Set.range
      ((LinearMap.toMatrixAlgEquiv b : Module.End ℂ V →* Matrix ι ι ℂ).comp ρ)) = ⊤ := by
  have : FiniteDimensional ℂ V := Module.Finite.of_basis b
  have h1 := span_range_eq_top_of_isIrreducible G V ρ h
  have h2 : Set.range ((LinearMap.toMatrixAlgEquiv b : Module.End ℂ V →* Matrix ι ι ℂ).comp ρ) =
      (LinearMap.toMatrix b b).toLinearMap '' Set.range ρ := by
    rw [← Set.range_comp]; rfl
  rw [h2, ← Submodule.map_span, h1, Submodule.map_top, LinearMap.range_eq_top]
  exact (LinearMap.toMatrix b b).surjective

theorem isSemisimpleRepresentation_tprod_of_isIrreducible :
    ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ G W) [FiniteDimensional ℂ V] [FiniteDimensional ℂ W], ρ.IsIrreducible → ρ'.IsIrreducible → (ρ.tprod ρ').IsSemisimpleRepresentation := by
  intro G _ V _ _ ρ W _ _ ρ' _ _ h h'
  let b := Module.finBasis ℂ V
  let b' := Module.finBasis ℂ W
  have key := GlobalTheory.T.isCompletelyReducible_kronecker_of_span_eq_top _ _ G _ _ (span_range_toMatrix_eq_top_of_isIrreducible ρ b h)
    (span_range_toMatrix_eq_top_of_isIrreducible ρ' b' h')
  rw [← ss_range_toMatrix_iff_isSemisimpleRepresentation _ G _ _ (b.tensorProduct b')]
  convert key using 3 with g
  rw [Representation.tprod_apply, TensorProduct.toMatrix_map]
  rfl

end GlobalTheory.ClassFin
