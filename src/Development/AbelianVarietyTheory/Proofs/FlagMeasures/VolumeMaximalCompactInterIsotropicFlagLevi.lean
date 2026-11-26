module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallBallAsymptoticsPiWeighted

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameOfFlag
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameOfFlag
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem starProjection_eq_add_inf_orthogonal {n : ℕ}
    (U V : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : U ≤ V) (x : EuclideanSpace ℂ (Fin n)) :
    V.starProjection x = U.starProjection x + (Uᗮ ⊓ V).starProjection x := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact V.add_mem (h (U.starProjection_apply_mem x))
      (((Uᗮ ⊓ V).starProjection_apply_mem x).2)
  · rw [← Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection h, ← Submodule.inf_orthogonal,
      Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection h]
    refine ⟨?_, ?_⟩
    · rw [← sub_sub]
      exact Uᗮ.sub_mem (U.sub_starProjection_mem_orthogonal x)
        (((Uᗮ ⊓ V).starProjection_apply_mem x).1)
    · rw [add_comm, ← sub_sub]
      refine (Uᗮ ⊓ V)ᗮ.sub_mem ((Uᗮ ⊓ V).sub_starProjection_mem_orthogonal x) ?_
      exact Submodule.orthogonal_le (inf_le_left (a := Uᗮ) (b := V))
        (U.le_orthogonal_orthogonal (U.starProjection_apply_mem x))

theorem starProjection_flag_eq_sum {n a : ℕ}
    (W : Fin (a + 1) → Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h0 : W 0 = ⊥) (hm : Monotone W)
    (l : Fin (a + 1)) (x : EuclideanSpace ℂ (Fin n)) :
    (W l).starProjection x = ∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val),
      ((W i.castSucc)ᗮ ⊓ W i.succ).starProjection x := by
  induction l using Fin.induction with
  | zero =>
    have := (W 0).starProjection_apply_mem x
    have h2 : (W 0).starProjection x = 0 := by
      have h3 : (W 0).starProjection x ∈ (⊥ : Submodule ℂ _) := h0 ▸ this
      simpa using h3
    simp [h2]
  | succ i ih =>
    have hf : univ.filter (fun k : Fin a => k.val < i.succ.val)
        = insert i (univ.filter (fun k : Fin a => k.val < i.castSucc.val)) := by
      ext k
      simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.val_succ, Fin.val_castSucc,
        Fin.ext_iff]
      omega
    rw [hf, Finset.sum_insert (by simp), ← ih, add_comm]
    exact starProjection_eq_add_inf_orthogonal _ _ (hm (Fin.castSucc_le_succ i)) x

theorem exists_orthonormal_frame_of_flag (n a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (h0 : W 0 = ⊥) (hm : Monotone W)
    (hj : ∀ i : Fin a, Module.finrank ℂ (W i.succ) = Module.finrank ℂ (W i.castSucc) + j i) :
    ∃ T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ, (∀ i, (T i)ᴴ * T i = 1) ∧
      (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) ∧ ∀ (l : Fin (a + 1)) (y : Fin n → ℂ),
        y ∈ W l ↔ (∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val), T i * (T i)ᴴ) *ᵥ y = y := by
  let e : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let V : Fin (a + 1) → Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    fun l => (W l).map e.toLinearMap
  have hV0 : V 0 = ⊥ := by simp [V, h0]
  have hVm : Monotone V := fun l k h => Submodule.map_mono (hm h)
  have hVr : ∀ l, Module.finrank ℂ (V l) = Module.finrank ℂ (W l) :=
    fun l => LinearEquiv.finrank_map_eq e (W l)
  let P : Fin a → Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    fun i => (V i.castSucc)ᗮ ⊓ V i.succ
  have hP : ∀ i, Module.finrank ℂ (P i) = j i := by
    intro i
    have h1 := Submodule.finrank_add_inf_finrank_orthogonal (hVm (Fin.castSucc_le_succ i))
    have h2 := hj i
    rw [hVr, hVr] at h1
    change Module.finrank ℂ ↥((V i.castSucc)ᗮ ⊓ V i.succ) = j i
    omega
  let b : ∀ i, OrthonormalBasis (Fin (j i)) ℂ (P i) :=
    fun i => (stdOrthonormalBasis ℂ (P i)).reindex (finCongr (hP i))
  let T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ :=
    fun i => Matrix.of fun r c => (b i c : EuclideanSpace ℂ (Fin n)) r
  have hT : ∀ i k c d, ((T i)ᴴ * T k) c d
      = inner ℂ (b i c : EuclideanSpace ℂ (Fin n)) (b k d : EuclideanSpace ℂ (Fin n)) := by
    intro i k c d
    simp only [Matrix.mul_apply, conjTranspose_apply, T, of_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  have hlt : ∀ i k : Fin a, i < k → ∀ c d,
      inner ℂ (b i c : EuclideanSpace ℂ (Fin n)) (b k d : EuclideanSpace ℂ (Fin n)) = 0 := by
    intro i k h c d
    have h1 : (b i c : EuclideanSpace ℂ (Fin n)) ∈ V k.castSucc :=
      hVm (Fin.succ_le_castSucc_iff.2 h) (b i c).2.2
    exact Submodule.inner_right_of_mem_orthogonal h1 (b k d).2.1
  have hproj : ∀ i y, (T i * (T i)ᴴ) *ᵥ y = ((P i).starProjection (e y)).ofLp := by
    intro i y
    rw [(b i).starProjection_eq_sum_rankOne, ← Matrix.mulVec_mulVec]
    ext r
    simp only [_root_.sum_apply, InnerProductSpace.rankOne_apply, WithLp.ofLp_sum,
      Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.mulVec, dotProduct, T, of_apply, conjTranspose_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  refine ⟨T, ?_, ?_, ?_⟩
  · intro i
    ext c d
    rw [hT, ← Submodule.coe_inner, orthonormal_iff_ite.1 (b i).orthonormal, Matrix.one_apply]
  · intro i k hik
    ext c d
    rw [hT, Matrix.zero_apply]
    rcases lt_or_gt_of_ne hik with h | h
    · exact hlt i k h c d
    · rw [inner_eq_zero_symm]
      exact hlt k i h d c
  · intro l y
    have h1 : y ∈ W l ↔ e y ∈ V l := by
      simp [V]
    rw [h1, ← Submodule.starProjection_eq_self_iff, starProjection_flag_eq_sum V hV0 hVm,
      Matrix.sum_mulVec]
    simp only [hproj]
    constructor
    · intro h
      have h2 := congrArg WithLp.ofLp h
      rw [WithLp.ofLp_sum] at h2
      exact h2
    · intro h
      apply WithLp.ofLp_injective 2
      rw [WithLp.ofLp_sum]
      exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameOfFlagStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_frame_of_flag_alt : ∀ (n a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ → Monotone W → (∀ i : Fin a, Module.finrank ℂ (W i.succ) = Module.finrank ℂ (W i.castSucc) + j i) → ∃ T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ, (∀ i, (T i)ᴴ * T i = 1) ∧ (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) ∧ ∀ (l : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W l ↔ (∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val), T i * (T i)ᴴ) *ᵥ y = y := by
  first | exact @GlobalTheory.exists_orthonormal_frame_of_flag | exact GlobalTheory.exists_orthonormal_frame_of_flag | (intros; apply GlobalTheory.exists_orthonormal_frame_of_flag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaxCompactInterLeviIffFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaxCompactInterLeviIffFrame
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagLeviRange

variable {n a : ℕ} {j : Fin a → ℕ}

noncomputable def proj (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (l : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ i ∈ univ.filter (fun i : Fin a => i.val < l), T i * (T i)ᴴ

theorem proj_conjTranspose (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (l : ℕ) : (proj T l)ᴴ = proj T l := by
  unfold proj
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem proj_mul (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (h1 : ∀ i, (T i)ᴴ * T i = 1)
    (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0) (l : ℕ) (k : Fin a) (hk : k.val < l) :
    proj T l * T k = T k := by
  unfold proj
  rw [Matrix.sum_mul, Finset.sum_eq_single k]
  · rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  · intro i _ hik
    rw [Matrix.mul_assoc, h2 i k hik, Matrix.mul_zero]
  · intro hk'
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ k, hk⟩) hk'

theorem proj_keep (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (h1 : ∀ i, (T i)ᴴ * T i = 1)
    (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0) (l : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (c : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (hA : ∀ i, A * T i = T i * c i) :
    proj T l * (A * proj T l) = A * proj T l := by
  have e : A * proj T l = ∑ i ∈ univ.filter (fun i : Fin a => i.val < l), T i * c i * (T i)ᴴ := by
    unfold proj
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Matrix.mul_assoc, hA i]
  rw [e, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, proj_mul T h1 h2 l i (Finset.mem_filter.1 hi).2]

theorem proj_idem (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (h1 : ∀ i, (T i)ᴴ * T i = 1)
    (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0) (l : ℕ) : proj T l * proj T l = proj T l := by
  calc proj T l * proj T l
      = proj T l * ∑ k ∈ univ.filter (fun i : Fin a => i.val < l), T k * (T k)ᴴ := rfl
    _ = ∑ k ∈ univ.filter (fun i : Fin a => i.val < l), proj T l * T k * (T k)ᴴ := by
        rw [Matrix.mul_sum]
        simp only [Matrix.mul_assoc]
    _ = ∑ k ∈ univ.filter (fun i : Fin a => i.val < l), T k * (T k)ᴴ :=
        Finset.sum_congr rfl fun k hk => by rw [proj_mul T h1 h2 l k (Finset.mem_filter.1 hk).2]
    _ = proj T l := rfl

theorem proj_succ (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (k : Fin a) :
    proj T (k.val + 1) = proj T k.val + T k * (T k)ᴴ := by
  have hs : univ.filter (fun i : Fin a => i.val < k.val + 1)
      = insert k (univ.filter (fun i : Fin a => i.val < k.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  unfold proj
  rw [hs, Finset.sum_insert (by simp), add_comm]

theorem Jm_allPos' (k : ℕ) : Formalism.REAL.Jm (allPos k) = 1 := by
  unfold Formalism.REAL.Jm allPos
  simp

theorem exists_compress {m : ℕ} (X : Matrix (Fin n) (Fin m) ℂ) (hX : Xᴴ * X = 1)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : gᴴ * g = 1) (hc : g * (X * Xᴴ) = X * Xᴴ * g) :
    ∃ k : Formalism.REAL.UJ (allPos m), g * (X * Xᴴ) = X * uMat k * Xᴴ := by
  have hgX : g * X = X * (Xᴴ * g * X) := by
    calc g * X = g * (X * (Xᴴ * X)) := by rw [hX, Matrix.mul_one]
      _ = g * (X * Xᴴ) * X := by simp only [Matrix.mul_assoc]
      _ = X * Xᴴ * g * X := by rw [hc]
      _ = X * (Xᴴ * g * X) := by simp only [Matrix.mul_assoc]
  have hkk : (Xᴴ * g * X)ᴴ * (Xᴴ * g * X) = 1 := by
    calc (Xᴴ * g * X)ᴴ * (Xᴴ * g * X) = Xᴴ * gᴴ * (X * (Xᴴ * g * X)) := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = Xᴴ * gᴴ * (g * X) := by rw [hgX]
      _ = Xᴴ * (gᴴ * g) * X := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, Matrix.mul_one, hX]
  refine ⟨⟨⟨Xᴴ * g * X, (Xᴴ * g * X)ᴴ, mul_eq_one_comm.1 hkk, hkk⟩, ?_⟩, ?_⟩
  · show (Xᴴ * g * X)ᴴ * Formalism.REAL.Jm (allPos m) * (Xᴴ * g * X) = Formalism.REAL.Jm (allPos m)
    rw [Jm_allPos', Matrix.mul_one, hkk]
  · show g * (X * Xᴴ) = X * (Xᴴ * g * X) * Xᴴ
    rw [← hgX, Matrix.mul_assoc]

theorem block_mul {p' q' : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ)
    (h1 : ∀ i, (T i)ᴴ * T i = 1) (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0)
    (h3 : ∀ i k, (T i)ᴴ * J * T k = 0) (h4 : ∀ i, (T i)ᴴ * P = 0) (h5 : ∀ i, (T i)ᴴ * Q = 0)
    (c : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (u : Matrix (Fin p') (Fin p') ℂ)
    (v : Matrix (Fin q') (Fin q') ℂ) (k : Fin a) :
    ((∑ i, (T i * c i * (T i)ᴴ + J * T i * c i * (T i)ᴴ * J)) + P * u * Pᴴ + Q * v * Qᴴ) * T k
      = T k * c k := by
  have hP : Pᴴ * T k = 0 := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose (h4 k)
  have hQ : Qᴴ * T k = 0 := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose (h5 k)
  have h3' : ∀ i k, (T i)ᴴ * (J * T k) = 0 := fun i k => by rw [← Matrix.mul_assoc]; exact h3 i k
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.sum_mul, Finset.sum_eq_single k]
  · simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h3', hP, hQ, Matrix.mul_zero, Matrix.mul_one,
      add_zero]
  · intro i _ hik
    simp only [Matrix.add_mul, Matrix.mul_assoc, h2 i k hik, h3', Matrix.mul_zero, add_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

private theorem unit_lemma_5 {m : ℕ} (x : Formalism.REAL.UJ (allPos m)) : (uMat x)ᴴ * uMat x = 1 := by
  have h : (uMat x)ᴴ * Formalism.REAL.Jm (allPos m) * uMat x = Formalism.REAL.Jm (allPos m) := x.2
  rwa [Jm_allPos', Matrix.mul_one] at h

private theorem block_sum_mul_J_mul_T {p' q' : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ)
    (h1 : ∀ i, (T i)ᴴ * T i = 1) (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0)
    (h3 : ∀ i k, (T i)ᴴ * J * T k = 0) (h4 : ∀ i, (T i)ᴴ * P = 0) (h5 : ∀ i, (T i)ᴴ * Q = 0)
    (hJJ : J * J = 1) (hPJ : Pᴴ * J = Pᴴ) (hQJ : Qᴴ * J = -Qᴴ)
    (c : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (u : Matrix (Fin p') (Fin p') ℂ)
    (v : Matrix (Fin q') (Fin q') ℂ) (k : Fin a) :
    ((∑ i, (T i * c i * (T i)ᴴ + J * T i * c i * (T i)ᴴ * J)) + P * u * Pᴴ + Q * v * Qᴴ) * (J * T k) = J * T k * c k := by
  have hPT : Pᴴ * T k = 0 := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose (h4 k)
  have hQT : Qᴴ * T k = 0 := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose (h5 k)
  have hPJT : Pᴴ * (J * T k) = 0 := by rw [← Matrix.mul_assoc, hPJ, hPT]
  have hQJT : Qᴴ * (J * T k) = 0 := by rw [← Matrix.mul_assoc, hQJ, Matrix.neg_mul, hQT, neg_zero]
  have h3' : ∀ i k, (T i)ᴴ * (J * T k) = 0 := fun i k => by rw [← Matrix.mul_assoc]; exact h3 i k
  have hJJ' : ∀ {r : ℕ} (X : Matrix (Fin n) (Fin r) ℂ), J * (J * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.sum_mul, Finset.sum_eq_single k]
  · simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h3', hJJ', hPJT, hQJT, Matrix.mul_zero,
      Matrix.mul_one, zero_add, add_zero]
  · intro i _ hik
    simp only [Matrix.add_mul, Matrix.mul_assoc, h2 i k hik, h3', hJJ', Matrix.mul_zero, add_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

private theorem block_sum_mul_P {p' q' : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ)
    (h4 : ∀ i, (T i)ᴴ * P = 0) (hJP : J * P = P) (hP1 : Pᴴ * P = 1) (hQP : Qᴴ * P = 0)
    (c : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (u : Matrix (Fin p') (Fin p') ℂ)
    (v : Matrix (Fin q') (Fin q') ℂ) :
    ((∑ i, (T i * c i * (T i)ᴴ + J * T i * c i * (T i)ᴴ * J)) + P * u * Pᴴ + Q * v * Qᴴ) * P = P * u := by
  simp only [Matrix.add_mul, Matrix.sum_mul, Matrix.mul_assoc, hJP, h4, hP1, hQP, Matrix.mul_zero,
    Matrix.mul_one, add_zero, zero_add, Finset.sum_const_zero]

private theorem block_sum_mul_Q {p' q' : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ)
    (h5 : ∀ i, (T i)ᴴ * Q = 0) (hJQ : J * Q = -Q) (hQ1 : Qᴴ * Q = 1) (hPQ : Pᴴ * Q = 0)
    (c : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (u : Matrix (Fin p') (Fin p') ℂ)
    (v : Matrix (Fin q') (Fin q') ℂ) :
    ((∑ i, (T i * c i * (T i)ᴴ + J * T i * c i * (T i)ᴴ * J)) + P * u * Pᴴ + Q * v * Qᴴ) * Q = Q * v := by
  simp only [Matrix.add_mul, Matrix.sum_mul, Matrix.mul_assoc, hJQ, Matrix.mul_neg, h5, hQ1, hPQ,
    neg_zero, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add, Finset.sum_const_zero]

private theorem conjTranspose_block_sum_eq {p' q' : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ)
    (hJH : Jᴴ = J) (c : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (u : Matrix (Fin p') (Fin p') ℂ)
    (v : Matrix (Fin q') (Fin q') ℂ) :
    ((∑ i, (T i * c i * (T i)ᴴ + J * T i * c i * (T i)ᴴ * J)) + P * u * Pᴴ + Q * v * Qᴴ)ᴴ = ((∑ i, (T i * (c i)ᴴ * (T i)ᴴ + J * T i * (c i)ᴴ * (T i)ᴴ * J)) + P * uᴴ * Pᴴ + Q * vᴴ * Qᴴ) := by
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hJH, Matrix.mul_assoc]

private theorem ext_of_frame_eq {p' q' : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ)
    (hc : (∑ i, (T i * (T i)ᴴ + J * T i * (T i)ᴴ * J)) + P * Pᴴ + Q * Qᴴ = 1)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i, A * T i = B * T i) (hJT : ∀ i, A * J * T i = B * J * T i)
    (hP : A * P = B * P) (hQ : A * Q = B * Q) : A = B := by
  calc A = A * ((∑ i, (T i * (T i)ᴴ + J * T i * (T i)ᴴ * J)) + P * Pᴴ + Q * Qᴴ) := by
        rw [hc, Matrix.mul_one]
    _ = B * ((∑ i, (T i * (T i)ᴴ + J * T i * (T i)ᴴ * J)) + P * Pᴴ + Q * Qᴴ) := by
        simp only [Matrix.mul_add, Matrix.mul_sum, ← Matrix.mul_assoc, hT, hJT, hP, hQ]
    _ = B := by rw [hc, Matrix.mul_one]

private theorem proj_mulVec_mulVec_eq_of_invariant (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (h1 : ∀ i, (T i)ᴴ * T i = 1)
    (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0) (l : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (c : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (hA : ∀ i, A * T i = T i * c i) (y : Fin n → ℂ)
    (hy : proj T l *ᵥ y = y) : proj T l *ᵥ (A *ᵥ y) = A *ᵥ y := by
  have e : proj T l *ᵥ (A *ᵥ (proj T l *ᵥ y)) = A *ᵥ (proj T l *ᵥ y) := by
    simp only [Matrix.mulVec_mulVec]
    rw [proj_keep T h1 h2 l A c hA]
  rwa [hy] at e

private theorem inv_of_eq_mul_inv_mul (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (h1 : ∀ i, (T i)ᴴ * T i = 1)
    (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0) (l : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ y, proj T l *ᵥ y = y → proj T l *ᵥ (A *ᵥ y) = A *ᵥ y)
    (hA' : ∀ y, proj T l *ᵥ y = y → proj T l *ᵥ (Aᴴ *ᵥ y) = Aᴴ *ᵥ y) :
    A * proj T l = proj T l * A := by
  have key : ∀ B : Matrix (Fin n) (Fin n) ℂ,
      (∀ y, proj T l *ᵥ y = y → proj T l *ᵥ (B *ᵥ y) = B *ᵥ y) →
        proj T l * (B * proj T l) = B * proj T l := by
    intro B hB
    refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
    simp only [Matrix.toLin'_apply]
    have hz : proj T l *ᵥ (proj T l *ᵥ y) = proj T l *ᵥ y := by
      rw [Matrix.mulVec_mulVec, proj_idem T h1 h2 l]
    simp only [← Matrix.mulVec_mulVec]
    exact hB _ hz
  have e1 := key A hA
  have e2 := key Aᴴ hA'
  have e3 : proj T l * A * proj T l = proj T l * A := by
    have h := congrArg Matrix.conjTranspose e2
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, proj_conjTranspose,
      Matrix.mul_assoc] using h
  calc A * proj T l = proj T l * (A * proj T l) := e1.symm
    _ = proj T l * A := by rw [← Matrix.mul_assoc, e3]

theorem mem_maxK_inter_flagM_iff : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (p' q' : ℕ) (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ), ((∀ i, (T i)ᴴ * T i = 1) ∧ (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) ∧ (∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0) ∧ (∀ i, (T i)ᴴ * P = 0) ∧ (∀ i, (T i)ᴴ * Q = 0) ∧ Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Formalism.REAL.Jm ε * P = P ∧ Formalism.REAL.Jm ε * Q = -Q ∧ (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * Pᴴ + Q * Qᴴ = 1 ∧ ∀ (l : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W l ↔ (∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val), T i * (T i)ᴴ) *ᵥ y = y) → ∀ g : Formalism.REAL.UJ ε, g ∈ maxK ε ∩ flagM ε W ↔ ∃ (k : ∀ i, Formalism.REAL.UJ (allPos (j i))) (u : Formalism.REAL.UJ (allPos p')) (v : Formalism.REAL.UJ (allPos q')), uMat g = (∑ i, (T i * uMat (k i) * (T i)ᴴ + Formalism.REAL.Jm ε * T i * uMat (k i) * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * uMat u * Pᴴ + Q * uMat v * Qᴴ := by
  rintro n ε a j W p' q' T P Q ⟨h1, h2, h3, h4, h5, hP1, hQ1, hJP, hJQ, hc, hW⟩ g
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJH : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hPJ : Pᴴ * Formalism.REAL.Jm ε = Pᴴ := by
    simpa [Matrix.conjTranspose_mul, hJH] using congrArg Matrix.conjTranspose hJP
  have hQJ : Qᴴ * Formalism.REAL.Jm ε = -Qᴴ := by
    simpa [Matrix.conjTranspose_mul, hJH] using congrArg Matrix.conjTranspose hJQ
  have hQP : Qᴴ * P = 0 := by
    have e : Qᴴ * P = -(Qᴴ * P) := by
      calc Qᴴ * P = Qᴴ * (Formalism.REAL.Jm ε * P) := by rw [hJP]
        _ = Qᴴ * Formalism.REAL.Jm ε * P := (Matrix.mul_assoc _ _ _).symm
        _ = -(Qᴴ * P) := by rw [hQJ, Matrix.neg_mul]
    ext x y
    have e' := congrFun (congrFun e x) y
    rw [Matrix.neg_apply] at e'
    rw [Matrix.zero_apply]
    linear_combination e' / 2
  have hPQ : Pᴴ * Q = 0 := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hQP
  constructor
  · rintro ⟨hK, hM⟩
    have hK' : (uMat g)ᴴ * uMat g = 1 := hK
    have hM' : ∀ (l : Fin (a + 1)), ∀ y ∈ W l, uMat g *ᵥ y ∈ W l ∧ (uMat g)ᴴ *ᵥ y ∈ W l := hM
    have hUJ : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
    have hgg : uMat g * (uMat g)ᴴ = 1 := mul_eq_one_comm.1 hK'
    have hgJ : uMat g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat g := by
      calc uMat g * Formalism.REAL.Jm ε = uMat g * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) := by rw [hUJ]
        _ = uMat g * (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g := by simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε * uMat g := by rw [hgg, Matrix.one_mul]
    have hcomm : ∀ l : Fin (a + 1), uMat g * proj T l.val = proj T l.val * uMat g := fun l =>
      inv_of_eq_mul_inv_mul T h1 h2 l.val (uMat g)
        (fun y hy => (hW l _).1 (hM' l y ((hW l y).2 hy)).1)
        (fun y hy => (hW l _).1 (hM' l y ((hW l y).2 hy)).2)
    have hTT : ∀ i : Fin a, uMat g * (T i * (T i)ᴴ) = T i * (T i)ᴴ * uMat g := by
      intro i
      have c1 := hcomm i.succ
      have c0 := hcomm i.castSucc
      rw [Fin.val_succ, proj_succ T i] at c1
      rw [Fin.val_castSucc] at c0
      have e : T i * (T i)ᴴ = (proj T i.val + T i * (T i)ᴴ) - proj T i.val := by abel
      rw [e, Matrix.mul_sub, Matrix.sub_mul, c1, c0]
    obtain ⟨S, hS⟩ : ∃ S, S = ∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε) := ⟨_, rfl⟩
    rw [← hS] at hc
    have hgS : uMat g * S = S * uMat g := by
      rw [hS, Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_add, Matrix.add_mul, hTT i]
      congr 1
      calc uMat g * (Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε) = uMat g * Formalism.REAL.Jm ε * (T i * (T i)ᴴ) * Formalism.REAL.Jm ε := by
            simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε * (uMat g * (T i * (T i)ᴴ)) * Formalism.REAL.Jm ε := by rw [hgJ]; simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε * (T i * (T i)ᴴ * uMat g) * Formalism.REAL.Jm ε := by rw [hTT i]
        _ = Formalism.REAL.Jm ε * T i * (T i)ᴴ * (uMat g * Formalism.REAL.Jm ε) := by simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε * uMat g := by rw [hgJ]; simp only [Matrix.mul_assoc]
    have hR : P * Pᴴ + Q * Qᴴ = 1 - S := by rw [← hc]; abel
    have hgR : uMat g * (P * Pᴴ + Q * Qᴴ) = (P * Pᴴ + Q * Qᴴ) * uMat g := by
      rw [hR, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hgS]
    have hRJ : (P * Pᴴ + Q * Qᴴ) * Formalism.REAL.Jm ε = P * Pᴴ - Q * Qᴴ := by
      simp only [Matrix.add_mul, Matrix.mul_assoc, hPJ, hQJ, Matrix.mul_neg, sub_eq_add_neg]
    have hgPP : uMat g * (P * Pᴴ) = P * Pᴴ * uMat g := by
      have e1 : ∀ R : Matrix (Fin n) (Fin n) ℂ, uMat g * R = R * uMat g →
          uMat g * (R + R * Formalism.REAL.Jm ε) = (R + R * Formalism.REAL.Jm ε) * uMat g := by
        intro R hR'
        calc uMat g * (R + R * Formalism.REAL.Jm ε) = uMat g * R + uMat g * R * Formalism.REAL.Jm ε := by
              rw [Matrix.mul_add, Matrix.mul_assoc]
          _ = R * uMat g + R * (uMat g * Formalism.REAL.Jm ε) := by rw [hR', Matrix.mul_assoc]
          _ = (R + R * Formalism.REAL.Jm ε) * uMat g := by rw [hgJ, Matrix.add_mul, Matrix.mul_assoc]
      have e2 := e1 _ hgR
      rw [hRJ] at e2
      have hsum : P * Pᴴ + Q * Qᴴ + (P * Pᴴ - Q * Qᴴ) = P * Pᴴ + P * Pᴴ := by abel
      have e3 : uMat g * (P * Pᴴ) + uMat g * (P * Pᴴ) = P * Pᴴ * uMat g + P * Pᴴ * uMat g := by
        rw [hsum, Matrix.mul_add, Matrix.add_mul] at e2
        exact e2
      ext x y
      have e4 := congrFun (congrFun e3 x) y
      simp only [Matrix.add_apply] at e4
      linear_combination e4 / 2
    have hgQQ : uMat g * (Q * Qᴴ) = Q * Qᴴ * uMat g := by
      have e : Q * Qᴴ = (P * Pᴴ + Q * Qᴴ) - P * Pᴴ := by abel
      rw [e, Matrix.mul_sub, Matrix.sub_mul, hgR, hgPP]
    choose k hk using fun i => exists_compress (T i) (h1 i) (uMat g) hK' (hTT i)
    obtain ⟨u, hu⟩ := exists_compress P hP1 (uMat g) hK' hgPP
    obtain ⟨v, hv⟩ := exists_compress Q hQ1 (uMat g) hK' hgQQ
    refine ⟨k, u, v, ?_⟩
    calc uMat g = uMat g * (S + P * Pᴴ + Q * Qᴴ) := by rw [hc, Matrix.mul_one]
      _ = uMat g * S + uMat g * (P * Pᴴ) + uMat g * (Q * Qᴴ) := by
          rw [Matrix.mul_add, Matrix.mul_add]
      _ = (∑ i, (T i * uMat (k i) * (T i)ᴴ + Formalism.REAL.Jm ε * T i * uMat (k i) * (T i)ᴴ * Formalism.REAL.Jm ε))
            + P * uMat u * Pᴴ + Q * uMat v * Qᴴ := by
          rw [hu, hv, hS, Matrix.mul_sum]
          congr 2
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.mul_add, hk i]
          congr 1
          calc uMat g * (Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε) = uMat g * Formalism.REAL.Jm ε * (T i * (T i)ᴴ) * Formalism.REAL.Jm ε := by
                simp only [Matrix.mul_assoc]
            _ = Formalism.REAL.Jm ε * (uMat g * (T i * (T i)ᴴ)) * Formalism.REAL.Jm ε := by rw [hgJ]; simp only [Matrix.mul_assoc]
            _ = Formalism.REAL.Jm ε * T i * uMat (k i) * (T i)ᴴ * Formalism.REAL.Jm ε := by rw [hk i]; simp only [Matrix.mul_assoc]
  · rintro ⟨k, u, v, hg⟩
    have hA : ∀ i, uMat g * T i = T i * uMat (k i) := fun i => by
      rw [hg]; exact block_mul _ T P Q h1 h2 h3 h4 h5 _ _ _ i
    have hgH : (uMat g)ᴴ = (∑ i, (T i * (uMat (k i))ᴴ * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (uMat (k i))ᴴ * (T i)ᴴ * Formalism.REAL.Jm ε))
        + P * (uMat u)ᴴ * Pᴴ + Q * (uMat v)ᴴ * Qᴴ := by
      rw [hg]; exact conjTranspose_block_sum_eq _ T P Q hJH _ _ _
    have hAH : ∀ i, (uMat g)ᴴ * T i = T i * (uMat (k i))ᴴ := fun i => by
      rw [hgH]; exact block_mul _ T P Q h1 h2 h3 h4 h5 _ _ _ i
    refine Set.mem_inter ?_ ?_
    · show (uMat g)ᴴ * uMat g = 1
      have hJA : ∀ i, uMat g * (Formalism.REAL.Jm ε * T i) = Formalism.REAL.Jm ε * T i * uMat (k i) := fun i => by
        rw [hg]; exact block_sum_mul_J_mul_T _ T P Q h1 h2 h3 h4 h5 hJJ hPJ hQJ _ _ _ i
      have hJAH : ∀ i, (uMat g)ᴴ * (Formalism.REAL.Jm ε * T i) = Formalism.REAL.Jm ε * T i * (uMat (k i))ᴴ := fun i => by
        rw [hgH]; exact block_sum_mul_J_mul_T _ T P Q h1 h2 h3 h4 h5 hJJ hPJ hQJ _ _ _ i
      have hPA : uMat g * P = P * uMat u := by
        rw [hg]; exact block_sum_mul_P _ T P Q h4 hJP hP1 hQP _ _ _
      have hPAH : (uMat g)ᴴ * P = P * (uMat u)ᴴ := by
        rw [hgH]; exact block_sum_mul_P _ T P Q h4 hJP hP1 hQP _ _ _
      have hQA : uMat g * Q = Q * uMat v := by
        rw [hg]; exact block_sum_mul_Q _ T P Q h5 hJQ hQ1 hPQ _ _ _
      have hQAH : (uMat g)ᴴ * Q = Q * (uMat v)ᴴ := by
        rw [hgH]; exact block_sum_mul_Q _ T P Q h5 hJQ hQ1 hPQ _ _ _
      refine ext_of_frame_eq _ T P Q hc _ _ ?_ ?_ ?_ ?_
      · intro i
        simp only [Matrix.mul_assoc, Matrix.one_mul]
        rw [hA i, ← Matrix.mul_assoc, hAH i, Matrix.mul_assoc (T i), unit_lemma_5, Matrix.mul_one]
      · intro i
        simp only [Matrix.mul_assoc, Matrix.one_mul]
        rw [hJA i, ← Matrix.mul_assoc, hJAH i, Matrix.mul_assoc (Formalism.REAL.Jm ε * T i), unit_lemma_5, Matrix.mul_one]
      · simp only [Matrix.mul_assoc, Matrix.one_mul]
        rw [hPA, ← Matrix.mul_assoc, hPAH, Matrix.mul_assoc P, unit_lemma_5, Matrix.mul_one]
      · simp only [Matrix.mul_assoc, Matrix.one_mul]
        rw [hQA, ← Matrix.mul_assoc, hQAH, Matrix.mul_assoc Q, unit_lemma_5, Matrix.mul_one]
    · show ∀ (l : Fin (a + 1)), ∀ y ∈ W l, uMat g *ᵥ y ∈ W l ∧ (uMat g)ᴴ *ᵥ y ∈ W l
      intro l y hy
      have hy' : proj T l.val *ᵥ y = y := (hW l y).1 hy
      exact ⟨(hW l _).2 (proj_mulVec_mulVec_eq_of_invariant T h1 h2 l.val _ _ hA y hy'),
        (hW l _).2 (proj_mulVec_mulVec_eq_of_invariant T h1 h2 l.val _ _ hAH y hy')⟩

end GlobalTheory.FlagLeviRange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaxCompactInterLeviIffFrameStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maxCompact_inter_levi_iff_frame : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (p' q' : ℕ) (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ), ((∀ i, (T i)ᴴ * T i = 1) ∧ (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) ∧ (∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0) ∧ (∀ i, (T i)ᴴ * P = 0) ∧ (∀ i, (T i)ᴴ * Q = 0) ∧ Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Formalism.REAL.Jm ε * P = P ∧ Formalism.REAL.Jm ε * Q = -Q ∧ (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * Pᴴ + Q * Qᴴ = 1 ∧ ∀ (l : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W l ↔ (∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val), T i * (T i)ᴴ) *ᵥ y = y) → ∀ g : Formalism.REAL.UJ ε, g ∈ maxK ε ∩ flagM ε W ↔ ∃ (k : ∀ i, Formalism.REAL.UJ (allPos (j i))) (u : Formalism.REAL.UJ (allPos p')) (v : Formalism.REAL.UJ (allPos q')), uMat g = (∑ i, (T i * uMat (k i) * (T i)ᴴ + Formalism.REAL.Jm ε * T i * uMat (k i) * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * uMat u * Pᴴ + Q * uMat v * Qᴴ := by
  first | exact @GlobalTheory.FlagLeviRange.mem_maxK_inter_flagM_iff | exact GlobalTheory.FlagLeviRange.mem_maxK_inter_flagM_iff | (intros; apply GlobalTheory.FlagLeviRange.mem_maxK_inter_flagM_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeMaximalCompactInterIsotropicFlagLevi
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas.LeviCompact

theorem continuous_hs_uMat {n : ℕ} (ε : Fin n → Bool) :
    Continuous fun g : Formalism.REAL.UJ ε => Formalism.REAL.hs (uMat g - 1) := by
  have hc : Continuous fun g : Formalism.REAL.UJ ε => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  unfold Formalism.REAL.hs
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun k _ => ?_
  exact ((continuous_apply k).comp ((continuous_apply i).comp (hc.sub continuous_const))).norm.pow 2

theorem compactSpace_allPos (N : ℕ) : CompactSpace (Formalism.REAL.UJ (allPos N)) := by
  obtain ⟨hE, hR⟩ := Formalism.REAL.uJEmb N (allPos N)
  have hJ : Formalism.REAL.Jm (allPos N) = 1 := by
    simp [Formalism.REAL.Jm, allPos, Matrix.diagonal_one]
  rw [← isCompact_univ_iff, hE.isCompact_iff, Set.image_univ, hR]
  have hcl : IsClosed {g : Matrix (Fin N) (Fin N) ℂ | Formalism.REAL.inUJ (allPos N) g} := by
    simp only [Formalism.REAL.inUJ]
    exact isClosed_eq (by fun_prop) continuous_const
  have hK : IsCompact (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset hcl ?_
  intro g hg i _ k _
  simp only [Formalism.REAL.inUJ, hJ, Matrix.mul_one] at hg
  have h := congrFun (congrFun hg k) k
  simp only [Matrix.one_apply_eq] at h
  have h2 : ∑ r, (Complex.normSq (g r k) : ℂ) = 1 := by
    rw [← h]; refine Finset.sum_congr rfl fun r _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  have h3 : ∑ r, Complex.normSq (g r k) = 1 := by exact_mod_cast h2
  have h4 : Complex.normSq (g i k) ≤ 1 :=
    h3 ▸ Finset.single_le_sum (fun r _ => Complex.normSq_nonneg (g r k)) (Finset.mem_univ i)
  rw [Metric.mem_closedBall, dist_zero_right]
  have h5 : ‖g i k‖ ^ 2 ≤ 1 := by rw [Complex.sq_norm]; exact h4
  nlinarith [norm_nonneg (g i k)]

theorem exists_eq_mul_preimage {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (ν : Measure G) [ν.IsHaarMeasure]
    (Φ : G →* H) (hc : Continuous Φ) (hi : Function.Injective Φ) (μ : Measure H) (h0 : μ (Set.range Φ)ᶜ = 0)
    (hinv : ∀ s ∈ Set.range Φ, μ.map (fun g => s * g) = μ) {U : Set H} (hU : IsOpen U) (h1 : (1 : H) ∈ U)
    (hfin : μ U ≠ ⊤) : ∃ α : NNReal, ∀ A, μ A = α * ν (Φ ⁻¹' A) := by
  have hemb : Topology.IsClosedEmbedding Φ := hc.isClosedEmbedding hi
  have hme : MeasurableEmbedding Φ := hemb.measurableEmbedding
  set ν' : Measure G := μ.comap Φ with hν'
  have hae : ∀ᵐ x ∂μ, x ∈ Set.range Φ := by rw [ae_iff]; exact h0
  have hres : μ.restrict (Set.range Φ) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have hkey : ∀ B, μ B = ν' (Φ ⁻¹' B) := by
    intro B
    rw [hν', ← hme.map_apply, hme.map_comap, hres]
  have hinvG : ν'.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs]
    have h1 : (fun x => g * x) ⁻¹' s = Φ ⁻¹' ((fun y => Φ g * y) ⁻¹' (Φ '' s)) := by
      ext x
      simp only [Set.mem_preimage, ← map_mul, hi.mem_set_image]
    have h2 : s = Φ ⁻¹' (Φ '' s) := (Set.preimage_image_eq s hi).symm
    rw [h1, ← hkey, ← Measure.map_apply (measurable_const_mul (Φ g)) (hme.measurableSet_image.2 hs),
      hinv _ ⟨g, rfl⟩, hkey, ← h2]
  have hV : IsOpen (Φ ⁻¹' U) := hU.preimage hc
  have hVfin : ν' (Φ ⁻¹' U) ≠ ⊤ := by rw [← hkey]; exact hfin
  have hfinU : ν' Set.univ < ⊤ := by
    refine isCompact_univ.measure_lt_top_of_nhdsWithin fun x _ => ⟨(fun y => x⁻¹ * y) ⁻¹' (Φ ⁻¹' U), ?_, ?_⟩
    · rw [nhdsWithin_univ]
      exact (hV.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [h1])
    · rw [measure_preimage_mul]; exact hVfin.lt_top
  have : IsFiniteMeasure ν' := ⟨hfinU⟩
  have heq := Measure.isMulLeftInvariant_eq_smul ν' ν
  refine ⟨Measure.haarScalarFactor ν' ν, fun A => ?_⟩
  have h3 := congrArg (fun m : Measure G => m (Φ ⁻¹' A)) heq
  rw [hkey A, h3, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

theorem volume_range : ∀ (n : ℕ) (ε : Fin n → Bool) (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ι → ℝ) (Φ : (∀ i, Formalism.REAL.UJ (allPos (m i))) →* Formalism.REAL.UJ ε), (∀ i, 0 < w i) → Continuous Φ → Function.Injective Φ → (∀ g, Formalism.REAL.hs (uMat (Φ g) - 1) = ∑ i, w i * Formalism.REAL.hs (uMat (g i) - 1)) → ∀ μ, IsGaugeSub (Set.range Φ) (∑ i, m i ^ 2) μ → μ Set.univ = ENNReal.ofReal (∏ i, volU (m i) * w i ^ (((m i : ℝ)) ^ 2 / 2)) := by
  intro n ε ι _ m w Φ hw hc hi hhs μ hμ
  obtain ⟨h0, hinv, hlim⟩ := hμ
  have hcpt : ∀ i, CompactSpace (Formalism.REAL.UJ (allPos (m i))) := fun i => compactSpace_allPos _
  choose c hcpos hcg _ using fun i => GlobalTheory.GaugeConst.gauge_exists_pos_unique (m i) (allPos (m i))
  set νi : ∀ i, Measure (Formalism.REAL.UJ (allPos (m i))) :=
    fun i => ENNReal.ofReal (c i) • Formalism.REAL.muG (allPos (m i)) with hνi
  have hfin : ∀ i, IsFiniteMeasure (νi i) := fun i => ⟨by
    simp only [hνi, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  have hhaar : ∀ i, (νi i).IsHaarMeasure := fun i =>
    Measure.IsHaarMeasure.smul _ (by simpa using hcpos i) ENNReal.ofReal_ne_top
  set ν : Measure (∀ i, Formalism.REAL.UJ (allPos (m i))) := Measure.pi νi with hν
  set V := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (∑ i, m i ^ 2))) 1) with hV
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos volume _ one_pos).ne'
  obtain ⟨r, hr0, hrfin⟩ : ∃ r : ℝ, 0 < r ∧ μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
    have e1 := hlim.eventually (gt_mem_nhds (show V < V + 1 from ENNReal.lt_add_right hVtop one_ne_zero))
    have e2 : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < r := self_mem_nhdsWithin
    obtain ⟨r, h1, h2⟩ := (e1.and e2).exists
    refine ⟨r, h2, fun htop => ?_⟩
    rw [htop, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at h1
    exact absurd h1 (not_lt.2 le_top)
  set U := {g : Formalism.REAL.UJ ε | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) < r} with hU
  have hUo : IsOpen U := isOpen_lt (Real.continuous_sqrt.comp (continuous_hs_uMat ε)) continuous_const
  have hu1 : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  have hU1 : (1 : Formalism.REAL.UJ ε) ∈ U := by simp [hU, Formalism.REAL.hs, hu1, hr0]
  have hUfin : μ U ≠ ⊤ := ne_top_of_le_ne_top hrfin (measure_mono fun g (hg : g ∈ U) => by
    simp only [hU, Set.mem_setOf_eq] at hg ⊢; exact hg.le)
  obtain ⟨α, hα⟩ := exists_eq_mul_preimage ν Φ hc hi μ h0 hinv hUo hU1 hUfin
  have hfac : ∀ i, Filter.Tendsto (fun r : ℝ => νi i {x | Real.sqrt (Formalism.REAL.hs (uMat x - 1)) ≤ r} /
      ENNReal.ofReal (r ^ (m i ^ 2))) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m i ^ 2))) 1))) := by
    intro i
    have hg := hcg i
    unfold GlobalTheory.Count.IsGauge at hg
    have h1 := ENNReal.tendsto_ofReal hg
    rw [ENNReal.ofReal_toReal measure_ball_lt_top.ne] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    simp only [hνi, Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_div_of_pos (pow_pos hr _), ENNReal.ofReal_mul (hcpos i).le,
      ENNReal.ofReal_toReal (measure_lt_top _ _).ne]
  have hprod := GlobalTheory.T.smallBall_asymptotics_pi_weighted ι (fun i => Formalism.REAL.UJ (allPos (m i))) νi (fun i x => Formalism.REAL.hs (uMat x - 1))
    (fun i => m i ^ 2) w (fun i => (continuous_hs_uMat _).measurable)
    (fun i x => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hw hfac
  set K : ℝ := ∏ i, w i ^ (-(((m i ^ 2 : ℕ) : ℝ) / 2)) with hK
  have hpre : ∀ r, Φ ⁻¹' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} =
      {x | Real.sqrt (∑ i, w i * Formalism.REAL.hs (uMat (x i) - 1)) ≤ r} := by
    intro r; ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, hhs]
  have hlim2 : Filter.Tendsto (fun r : ℝ => (α : ENNReal) * (ν {x | Real.sqrt (∑ i, w i * Formalism.REAL.hs (uMat (x i) - 1)) ≤ r} /
      ENNReal.ofReal (r ^ (∑ i, m i ^ 2)))) (nhdsWithin 0 (Set.Ioi 0)) (nhds V) := by
    refine hlim.congr' (Filter.Eventually.of_forall fun r => ?_)
    simp only
    rw [hα, hpre, mul_div_assoc]
  have hlim3 := ENNReal.Tendsto.const_mul hprod (Or.inr (ENNReal.coe_ne_top (r := α)))
  have heq : V = (α : ENNReal) * (ENNReal.ofReal K * V) := tendsto_nhds_unique hlim2 hlim3
  have h1 : (α : ENNReal) * ENNReal.ofReal K = 1 := by
    have e : V = ((α : ENNReal) * ENNReal.ofReal K) * V := by rw [mul_assoc]; exact heq
    calc _ = ((α : ENNReal) * ENNReal.ofReal K) * V / V := (ENNReal.mul_div_cancel_right hV0 hVtop).symm
      _ = V / V := by rw [← e]
      _ = 1 := ENNReal.div_self hV0 hVtop
  have hKpos : 0 < K := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hw i) _
  have hvol0 : ∀ i, 0 ≤ volU (m i) := fun i => by
    rw [← GlobalTheory.T.riemannianHaarGauge_volume_unitaryGroup_eq (m i) (c i) (hcg i)]; exact mul_nonneg (hcpos i).le ENNReal.toReal_nonneg
  have hνu : ν Set.univ = ∏ i, ENNReal.ofReal (volU (m i)) := by
    rw [hν, Measure.pi_univ]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hνi, Measure.smul_apply, smul_eq_mul]
    rw [← GlobalTheory.T.riemannianHaarGauge_volume_unitaryGroup_eq (m i) (c i) (hcg i), ENNReal.ofReal_mul (hcpos i).le,
      ENNReal.ofReal_toReal (measure_lt_top _ _).ne]
  rw [hα, Set.preimage_univ, hνu, ENNReal.eq_inv_of_mul_eq_one_left h1, ← ENNReal.ofReal_inv_of_pos hKpos,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => hvol0 i), ← ENNReal.ofReal_mul (inv_nonneg.2 hKpos.le)]
  congr 1
  rw [Finset.prod_mul_distrib, mul_comm, hK, ← Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.rpow_neg (hw i).le, inv_inv]
  push_cast
  ring_nf

private theorem fintype_sum_matrix_mul_eq_sum_mul {n m : ℕ} {ι : Type} [Fintype ι] (A : ι → Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin m) ℂ) : (∑ i, A i) * B = ∑ i, A i * B := by
  ext r c
  simp only [Matrix.mul_apply, Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem exists_frame : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∃ (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin (p - ∑ i, j i)) ℂ) (Q : Matrix (Fin n) (Fin (q - ∑ i, j i)) ℂ), (∀ i, (T i)ᴴ * T i = 1) ∧ (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) ∧ (∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0) ∧ (∀ i, (T i)ᴴ * P = 0) ∧ (∀ i, (T i)ᴴ * Q = 0) ∧ Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Formalism.REAL.Jm ε * P = P ∧ Formalism.REAL.Jm ε * Q = -Q ∧ (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * Pᴴ + Q * Qᴴ = 1 ∧ ∀ (l : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W l ↔ (∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val), T i * (T i)ᴴ) *ᵥ y = y := by
  intro n ε p q hp hq a j W hW
  obtain ⟨h0, hmono, hrk, hiso⟩ := hW
  obtain ⟨T, hTT, hTo, hmem⟩ := GlobalTheory.T.exists_orthonormal_frame_of_flag_alt n a j W h0 hmono hrk
  have hcol : ∀ k (d : Fin (j k)), (fun r => T k r d) ∈ W (Fin.last a) := by
    intro k d
    rw [hmem]
    have hf : (univ.filter fun i : Fin a => i.val < (Fin.last a).val) = univ :=
      Finset.filter_true_of_mem fun i _ => i.isLt
    rw [hf]
    have hs : (∑ i, T i * (T i)ᴴ) * T k = T k := by
      rw [fintype_sum_matrix_mul_eq_sum_mul, Finset.sum_eq_single k]
      · rw [Matrix.mul_assoc, hTT, Matrix.mul_one]
      · intro i _ hik; rw [Matrix.mul_assoc, hTo i k hik, Matrix.mul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    have hy : (fun r => T k r d) = T k *ᵥ Pi.single d 1 := by
      ext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hy, Matrix.mulVec_mulVec, hs]
  have hTJT : ∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0 := by
    intro i k
    ext c d
    have h := hiso _ (hcol i c) _ (hcol k d)
    rw [Matrix.zero_apply, ← h]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Pi.star_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
  obtain ⟨P, Q, h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.T.complete_isotropicFrame_signature_eigenvectors n ε p q hp hq a j T hTT hTo hTJT
  exact ⟨T, P, Q, hTT, hTo, hTJT, h1, h2, h3, h4, h5, h6, h7, hmem⟩

private theorem levi_lemma {n a p' q' : ℕ} {j : Fin a → ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ)
    (K : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (U : Matrix (Fin p') (Fin p') ℂ) (V : Matrix (Fin q') (Fin q') ℂ)
    (hJJ : J * J = 1) (hJP : J * P = P) (hJQ : J * Q = -Q) (e1 : Pᴴ * J = Pᴴ) (e2 : Qᴴ * J = -Qᴴ)
    (hJH : Jᴴ = J) :
    J * (∑ i, T i * K i * (T i)ᴴ + (∑ i, J * T i * K i * (J * T i)ᴴ + (P * U * Pᴴ + Q * V * Qᴴ))) =
      (∑ i, T i * K i * (T i)ᴴ + (∑ i, J * T i * K i * (J * T i)ᴴ + (P * U * Pᴴ + Q * V * Qᴴ))) * J := by
  have a1 : ∀ {r : ℕ} (X : Matrix (Fin n) (Fin r) ℂ), J * (J * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have a2 : ∀ {r : ℕ} (X : Matrix (Fin p') (Fin r) ℂ), J * (P * X) = P * X := fun X => by
    rw [← Matrix.mul_assoc, hJP]
  have a3 : ∀ {r : ℕ} (X : Matrix (Fin q') (Fin r) ℂ), J * (Q * X) = -(Q * X) := fun X => by
    rw [← Matrix.mul_assoc, hJQ, Matrix.neg_mul]
  simp only [Matrix.conjTranspose_mul, hJH, Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul,
    Matrix.mul_assoc, a1, a2, a3, e1, e2, hJJ, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
    Finset.sum_add_distrib]
  abel


set_option maxHeartbeats 1000000 in
theorem volume_maxK_inter_flagM : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ μ, IsGaugeSub (maxK ε ∩ flagM ε W) ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) μ → μ Set.univ = ENNReal.ofReal ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) * volU (p - ∑ i, j i) * volU (q - ∑ i, j i)) := by
  intro n ε p q hp hq a j W hW μ hμ
  obtain ⟨T, P, Q, hTT, hTo, hTJT, hTP, hTQ, hPP, hQQ, hJP, hJQ, hsum, hmem⟩ :=
    exists_frame n ε p q hp hq a j W hW
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJH : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hJJ' : ∀ {r : ℕ} (X : Matrix (Fin n) (Fin r) ℂ), Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * X) = X := by
    intro r X; rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hJP' : ∀ {r : ℕ} (X : Matrix (Fin (p - ∑ i, j i)) (Fin r) ℂ), Formalism.REAL.Jm ε * (P * X) = P * X := by
    intro r X; rw [← Matrix.mul_assoc, hJP]
  have hJQ' : ∀ {r : ℕ} (X : Matrix (Fin (q - ∑ i, j i)) (Fin r) ℂ), Formalism.REAL.Jm ε * (Q * X) = -(Q * X) := by
    intro r X; rw [← Matrix.mul_assoc, hJQ, Matrix.neg_mul]
  have e1 : Pᴴ * Formalism.REAL.Jm ε = Pᴴ := by
    rw [← hJH, ← Matrix.conjTranspose_mul, hJP]
  have e2 : Qᴴ * Formalism.REAL.Jm ε = -Qᴴ := by
    rw [← hJH, ← Matrix.conjTranspose_mul, hJQ, Matrix.conjTranspose_neg]
  have hPT : ∀ k, Pᴴ * T k = 0 := by
    intro k
    have h := congrArg Matrix.conjTranspose (hTP k)
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at h
  have hQT : ∀ k, Qᴴ * T k = 0 := by
    intro k
    have h := congrArg Matrix.conjTranspose (hTQ k)
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at h
  have hPQ : Pᴴ * Q = 0 := by
    have hx : Pᴴ * Q = -(Pᴴ * Q) := by
      calc Pᴴ * Q = Pᴴ * Formalism.REAL.Jm ε * Q := by rw [e1]
        _ = -(Pᴴ * Q) := by rw [Matrix.mul_assoc, hJQ, Matrix.mul_neg]
    ext c d
    have h := congrFun (congrFun hx c) d
    simp only [Matrix.neg_apply] at h
    rw [Matrix.zero_apply]
    linear_combination h / 2
  have hQP : Qᴴ * P = 0 := by
    have h := congrArg Matrix.conjTranspose hPQ
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at h
  let m : Fin a ⊕ (Unit ⊕ Unit) → ℕ := Sum.elim j (Sum.elim (fun _ => p - ∑ i, j i) (fun _ => q - ∑ i, j i))
  let π : Fin a ⊕ (Fin a ⊕ (Unit ⊕ Unit)) → Fin a ⊕ (Unit ⊕ Unit) := Sum.elim Sum.inl (Sum.elim Sum.inl Sum.inr)
  let S : ∀ s, Matrix (Fin n) (Fin (m (π s))) ℂ := fun s => match s with
    | Sum.inl i => T i
    | Sum.inr (Sum.inl i) => Formalism.REAL.Jm ε * T i
    | Sum.inr (Sum.inr (Sum.inl _)) => P
    | Sum.inr (Sum.inr (Sum.inr _)) => Q
  have hsurj : Function.Surjective π := by
    rintro (i | u)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr (Sum.inr u), rfl⟩
  have horth : ∀ s, (S s)ᴴ * S s = 1 := by
    rintro (i | i | u | u)
    · exact hTT i
    · show (Formalism.REAL.Jm ε * T i)ᴴ * (Formalism.REAL.Jm ε * T i) = 1
      rw [Matrix.conjTranspose_mul, hJH, Matrix.mul_assoc, hJJ', hTT]
    · exact hPP
    · exact hQQ
  have hcross : ∀ s t, s ≠ t → (S s)ᴴ * S t = 0 := by
    rintro (i | i | u | u) (k | k | v | v) hst
    · exact hTo i k fun h => hst (h ▸ rfl)
    · show (T i)ᴴ * (Formalism.REAL.Jm ε * T k) = 0
      rw [← Matrix.mul_assoc, hTJT]
    · exact hTP i
    · exact hTQ i
    · show (Formalism.REAL.Jm ε * T i)ᴴ * T k = 0
      rw [Matrix.conjTranspose_mul, hJH, hTJT]
    · show (Formalism.REAL.Jm ε * T i)ᴴ * (Formalism.REAL.Jm ε * T k) = 0
      rw [Matrix.conjTranspose_mul, hJH, Matrix.mul_assoc, hJJ', hTo i k fun h => hst (h ▸ rfl)]
    · show (Formalism.REAL.Jm ε * T i)ᴴ * P = 0
      rw [Matrix.conjTranspose_mul, hJH, Matrix.mul_assoc, hJP, hTP]
    · show (Formalism.REAL.Jm ε * T i)ᴴ * Q = 0
      rw [Matrix.conjTranspose_mul, hJH, Matrix.mul_assoc, hJQ, Matrix.mul_neg, hTQ, neg_zero]
    · exact hPT k
    · show Pᴴ * (Formalism.REAL.Jm ε * T k) = 0
      rw [← Matrix.mul_assoc, e1, hPT]
    · exact absurd (by rw [Subsingleton.elim u v]) hst
    · exact hPQ
    · exact hQT k
    · show Qᴴ * (Formalism.REAL.Jm ε * T k) = 0
      rw [← Matrix.mul_assoc, e2, Matrix.neg_mul, hQT, neg_zero]
    · exact hQP
    · exact absurd (by rw [Subsingleton.elim u v]) hst
  have hsumS : ∑ s, S s * (S s)ᴴ = 1 := by
    simp only [Fintype.sum_sum_type, Fintype.sum_unique]
    show ∑ i, T i * (T i)ᴴ + (∑ i, (Formalism.REAL.Jm ε * T i) * (Formalism.REAL.Jm ε * T i)ᴴ + (P * Pᴴ + Q * Qᴴ)) = 1
    rw [← hsum]
    simp only [Finset.sum_add_distrib, Matrix.conjTranspose_mul, hJH, Matrix.mul_assoc]
    abel
  have hcomm : ∀ k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ,
      Formalism.REAL.Jm ε * ∑ s, S s * k (π s) * (S s)ᴴ = (∑ s, S s * k (π s) * (S s)ᴴ) * Formalism.REAL.Jm ε := by
    intro k
    simp only [Fintype.sum_sum_type, Fintype.sum_unique]
    exact levi_lemma (Formalism.REAL.Jm ε) T P Q (fun i => k (Sum.inl i)) (k (Sum.inr (Sum.inl default)))
      (k (Sum.inr (Sum.inr default))) hJJ hJP hJQ e1 e2 hJH
  obtain ⟨Φ, hΦc, hΦi, hΦu, hΦhs⟩ := GlobalTheory.T.exists_blockDiag_unitary_product_hom n ε _ _ π m S hsurj horth hcross hsumS hcomm
  have hform : ∀ x : ∀ i, Formalism.REAL.UJ (allPos (m i)), uMat (Φ x) =
      (∑ i, (T i * (show Matrix (Fin (j i)) (Fin (j i)) ℂ from uMat (x (Sum.inl i))) * (T i)ᴴ +
        Formalism.REAL.Jm ε * T i * (show Matrix (Fin (j i)) (Fin (j i)) ℂ from uMat (x (Sum.inl i))) * (T i)ᴴ * Formalism.REAL.Jm ε)) +
      P * (show Matrix (Fin (p - ∑ i, j i)) (Fin (p - ∑ i, j i)) ℂ from uMat (x (Sum.inr (Sum.inl default)))) * Pᴴ + Q * (show Matrix (Fin (q - ∑ i, j i)) (Fin (q - ∑ i, j i)) ℂ from uMat (x (Sum.inr (Sum.inr default)))) * Qᴴ := by
    intro x
    rw [hΦu]
    simp only [Fintype.sum_sum_type, Fintype.sum_unique]
    show ∑ i, T i * (show Matrix (Fin (j i)) (Fin (j i)) ℂ from uMat (x (Sum.inl i))) * (T i)ᴴ + (∑ i, (Formalism.REAL.Jm ε * T i) * (show Matrix (Fin (j i)) (Fin (j i)) ℂ from uMat (x (Sum.inl i))) * (Formalism.REAL.Jm ε * T i)ᴴ +
        (P * (show Matrix (Fin (p - ∑ i, j i)) (Fin (p - ∑ i, j i)) ℂ from uMat (x (Sum.inr (Sum.inl default)))) * Pᴴ + Q * (show Matrix (Fin (q - ∑ i, j i)) (Fin (q - ∑ i, j i)) ℂ from uMat (x (Sum.inr (Sum.inr default)))) * Qᴴ)) = _
    simp only [Finset.sum_add_distrib, Matrix.conjTranspose_mul, hJH, Matrix.mul_assoc]
    abel
  have hrange : Set.range Φ = maxK ε ∩ flagM ε W := by
    ext g
    rw [GlobalTheory.T.mem_maxCompact_inter_levi_iff_frame n ε a j W _ _ T P Q ⟨hTT, hTo, hTJT, hTP, hTQ, hPP, hQQ, hJP, hJQ, hsum, hmem⟩ g]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨fun i => x (Sum.inl i), x (Sum.inr (Sum.inl default)), x (Sum.inr (Sum.inr default)), hform x⟩
    · rintro ⟨k, u, v, hg⟩
      let x : ∀ i, Formalism.REAL.UJ (allPos (m i)) := fun i => match i with
        | Sum.inl i => k i
        | Sum.inr (Sum.inl _) => u
        | Sum.inr (Sum.inr _) => v
      refine ⟨x, Subtype.ext (Units.ext ?_)⟩
      show uMat (Φ x) = uMat g
      rw [hform x, hg]
  have hd : (p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2 = ∑ i, m i ^ 2 := by
    simp only [Fintype.sum_sum_type, Fintype.sum_unique, m, Sum.elim_inl, Sum.elim_inr]
    ring
  have hμ' : IsGaugeSub (Set.range Φ) (∑ i, m i ^ 2) μ := by
    rw [hrange, ← hd]; exact hμ
  let w : Fin a ⊕ (Unit ⊕ Unit) → ℝ := Sum.elim (fun _ => 2) (fun _ => 1)
  have hw : ∀ i, 0 < w i := by
    rintro (i | u | u) <;> norm_num [w]
  have hhs : ∀ g, Formalism.REAL.hs (uMat (Φ g) - 1) = ∑ i, w i * Formalism.REAL.hs (uMat (g i) - 1) := by
    intro g
    rw [hΦhs]
    simp only [Fintype.sum_sum_type, Fintype.sum_unique]
    dsimp only [π, w, m, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.mul_sum, two_mul, one_mul, one_mul, add_assoc]
    rfl
  rw [volume_range n ε _ m w Φ hw hΦc hΦi hhs μ hμ']
  congr 1
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, m, w, Sum.elim_inl, Sum.elim_inr, Real.one_rpow,
    mul_one]
  ring

end GlobalTheory.FlagMeas.LeviCompact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeMaximalCompactInterIsotropicFlagLeviStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_maximalCompact_inter_isotropicFlagLevi : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ μ, IsGaugeSub (maxK ε ∩ flagM ε W) ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) μ → μ Set.univ = ENNReal.ofReal ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) * volU (p - ∑ i, j i) * volU (q - ∑ i, j i)) := by
  first | exact @GlobalTheory.FlagMeas.LeviCompact.volume_maxK_inter_flagM | exact GlobalTheory.FlagMeas.LeviCompact.volume_maxK_inter_flagM | (intros; apply GlobalTheory.FlagMeas.LeviCompact.volume_maxK_inter_flagM <;> assumption)
end
