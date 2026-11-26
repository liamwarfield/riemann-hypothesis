module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowerEvalTwoVarsRingHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowerEvalTwoVarsRingHom
open MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DPEval2

def bv (p : ℕ × ℕ) : MvPolynomial (Fin 2) ℚ :=
  ((p.1.factorial : ℚ)⁻¹ • (X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • X 1 ^ p.2)

def ex (p : ℕ × ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 p.1 + Finsupp.single 1 p.2

theorem ex_injective : Function.Injective ex := by
  intro p q h
  have h0 := congrArg (fun f : Fin 2 →₀ ℕ ↦ f 0) h
  have h1 := congrArg (fun f : Fin 2 →₀ ℕ ↦ f 1) h
  simp [ex] at h0 h1
  exact Prod.ext h0 h1

theorem bv_eq (p : ℕ × ℕ) :
    bv p = ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) • monomial (ex p) (1 : ℚ) := by
  rw [bv, ex, X_pow_eq_monomial, X_pow_eq_monomial, smul_monomial, smul_monomial,
    monomial_mul_monomial, smul_monomial]
  simp

theorem bv_li : LinearIndependent ℚ bv := by
  have h := ((basisMonomials (Fin 2) ℚ).linearIndependent.comp ex ex_injective).units_smul
    (fun p : ℕ × ℕ ↦ Units.mk0 ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) (by positivity))
  have e : bv = (fun p : ℕ × ℕ ↦ Units.mk0 ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) (by positivity)) •
      (⇑(basisMonomials (Fin 2) ℚ) ∘ ex) := by
    funext p
    simp [bv_eq, Units.smul_def, coe_basisMonomials]
  rw [e]; exact h

theorem ex_add (p q : ℕ × ℕ) : ex (p + q) = ex p + ex q := by
  simp only [ex, Prod.fst_add, Prod.snd_add, Finsupp.single_add]; abel

theorem bv_mul (p q : ℕ × ℕ) :
    bv p * bv q = ((p.1 + q.1).choose p.1 * (p.2 + q.2).choose p.2 : ℕ) • bv (p + q) := by
  rw [bv_eq, bv_eq, bv_eq, smul_mul_smul, monomial_mul_monomial, ← ex_add,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_one]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add, Nat.cast_mul, Nat.cast_add_choose]
  field_simp

def D : Submodule ℤ (MvPolynomial (Fin 2) ℚ) := Submodule.span ℤ (Set.range bv)

theorem bv_mem (p : ℕ × ℕ) : bv p ∈ D := Submodule.subset_span ⟨p, rfl⟩

def β : Module.Basis (ℕ × ℕ) ℤ D := Module.Basis.span (bv_li.restrict_scalars' ℤ)

theorem β_eq (p : ℕ × ℕ) : β p = ⟨bv p, bv_mem p⟩ :=
  Module.Basis.span_apply _ p

theorem mul_mem {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) : x * y ∈ D := by
  refine Submodule.span_induction₂ (p := fun x y _ _ ↦ x * y ∈ D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    rw [bv_mul]
    exact Submodule.smul_of_tower_mem _ _ (bv_mem _)
  · intro y _; simp
  · intro y _; simp
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro r x y _ _ h; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
  · intro r x y _ _ h; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h

variable {B : Type} [CommRing B] (u v : ℕ → B)

def ψ : D →ₗ[ℤ] B := β.constr ℤ fun p ↦ u p.1 * v p.2


open Classical in
def φ (q : MvPolynomial (Fin 2) ℚ) : B := by
  classical
  exact if h : q ∈ D then ψ u v ⟨q, h⟩ else 0

theorem φ_of_mem {q : MvPolynomial (Fin 2) ℚ} (h : q ∈ D) :
    φ u v q = ψ u v ⟨q, h⟩ := dite_eq_left h

theorem φ_bv (p : ℕ × ℕ) : φ u v (bv p) = u p.1 * v p.2 := by
  rw [φ_of_mem u v (bv_mem p), ← β_eq, ψ, Module.Basis.constr_basis]

theorem φ_add {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) :
    φ u v (x + y) = φ u v x + φ u v y := by
  rw [φ_of_mem u v hx, φ_of_mem u v hy, φ_of_mem u v (add_mem hx hy), ← map_add (f := _)]; rfl

theorem φ_zsmul (z : ℤ) {x : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) : φ u v (z • x) = z • φ u v x := by
  rw [φ_of_mem u v hx, φ_of_mem u v (Submodule.smul_mem _ z hx), ← map_zsmul]; rfl

theorem φ_nsmul (n : ℕ) {x : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) : φ u v (n • x) = n • φ u v x := by
  rw [← Nat.cast_smul_eq_nsmul ℤ n x, φ_zsmul u v _ hx, Nat.cast_smul_eq_nsmul]

theorem φ_zero : φ u v 0 = 0 := by
  rw [φ_of_mem u v (zero_mem _)]; exact map_zero (ψ u v)

theorem φ_mul (hu : ∀ m n, u m * u n = ((m + n).choose m : B) * u (m + n))
    (hv : ∀ m n, v m * v n = ((m + n).choose m : B) * v (m + n))
    {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) :
    φ u v (x * y) = φ u v x * φ u v y := by
  refine Submodule.span_induction₂ (p := fun x y hx hy ↦ φ u v (x * y) = φ u v x * φ u v y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    rw [bv_mul, φ_nsmul u v _ (bv_mem _), φ_bv, φ_bv, φ_bv, nsmul_eq_mul]
    calc ((((p.1 + q.1).choose p.1 * (p.2 + q.2).choose p.2 : ℕ)) : B) * (u (p + q).1 * v (p + q).2)
        = (((p.1 + q.1).choose p.1 : B) * u (p.1 + q.1)) * (((p.2 + q.2).choose p.2 : B) * v (p.2 + q.2)) := by
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_mul]; ring
      _ = u p.1 * v p.2 * (u q.1 * v q.2) := by rw [← hu, ← hv]; ring
  · intro y _; simp [φ_zero]
  · intro y _; simp [φ_zero]
  · intro x y z hx hy hz h1 h2
    rw [add_mul, φ_add u v (mul_mem hx hz) (mul_mem hy hz), φ_add u v hx hy, h1, h2, add_mul]
  · intro x y z hx hy hz h1 h2
    rw [mul_add, φ_add u v (mul_mem hx hy) (mul_mem hx hz), φ_add u v hy hz, h1, h2, mul_add]
  · intro r x y hx hy h
    rw [smul_mul_assoc, φ_zsmul u v r (mul_mem hx hy), φ_zsmul u v r hx, h, smul_mul_assoc]
  · intro r x y hx hy h
    rw [mul_smul_comm, φ_zsmul u v r (mul_mem hx hy), φ_zsmul u v r hy, h, mul_smul_comm]

end GlobalTheory.DPEval2

namespace GlobalTheory


open DPEval2 in
theorem dpEval_two :
    ∀ (B : Type) [CommRing B] (u v : ℕ → B), u 0 = 1 → v 0 = 1 →
    (∀ m n, u m * u n = ((m + n).choose m : B) * u (m + n)) →
    (∀ m n, v m * v n = ((m + n).choose m : B) * v (m + n)) →
    ∃ φ : MvPolynomial (Fin 2) ℚ → B,
      (∀ a c : ℕ, φ (((a.factorial : ℚ)⁻¹ • MvPolynomial.X 0 ^ a) * ((c.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ c)) = u a * v c) ∧
      (∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        ∀ e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
          φ (d + e) = φ d + φ e ∧
          d * e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)) ∧
          φ (d * e) = φ d * φ e) ∧
      (∀ z : ℤ, ∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        φ (z • d) = z • φ d) := by
  intro B _ u v _ _ hu hv
  refine ⟨DPEval2.φ u v, fun a c ↦ DPEval2.φ_bv u v (a, c), fun d hd e he ↦ ?_,
    fun z d hd ↦ DPEval2.φ_zsmul u v z hd⟩
  exact ⟨DPEval2.φ_add u v hd he, DPEval2.mul_mem hd he, DPEval2.φ_mul u v hu hv hd he⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowerEvalTwoVarsRingHomStatement
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dividedPowerEval_twoVars_ringHom : ∀ (B : Type) [CommRing B] (u v : ℕ → B), u 0 = 1 → v 0 = 1 →
    (∀ m n, u m * u n = ((m + n).choose m : B) * u (m + n)) →
    (∀ m n, v m * v n = ((m + n).choose m : B) * v (m + n)) →
    ∃ φ : MvPolynomial (Fin 2) ℚ → B,
      (∀ a c : ℕ, φ (((a.factorial : ℚ)⁻¹ • MvPolynomial.X 0 ^ a) * ((c.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ c)) = u a * v c) ∧
      (∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        ∀ e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
          φ (d + e) = φ d + φ e ∧
          d * e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)) ∧
          φ (d * e) = φ d * φ e) ∧
      (∀ z : ℤ, ∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        φ (z • d) = z • φ d) := by
  first | exact @GlobalTheory.dpEval_two | exact GlobalTheory.dpEval_two | (intros; apply GlobalTheory.dpEval_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixSqrtNearOneUltrametric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixSqrtNearOneUltrametric
open Matrix Filter Topology

namespace GlobalTheory.MatSqrtNearOne

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] {n : ℕ}

theorem norm_mul_le_ultra (A B : Matrix (Fin n) (Fin n) K) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ := by
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (norm_apply_le_norm A) (norm_apply_le_norm B)
    (norm_nonneg _) (norm_nonneg _)

theorem norm_add_le_max_ultra (A B : Matrix (Fin n) (Fin n) K) : ‖A + B‖ ≤ max ‖A‖ ‖B‖ := by
  rw [Matrix.norm_le_iff (le_max_of_le_left (norm_nonneg _))]
  intro i j
  rw [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le_max (norm_apply_le_norm A) (norm_apply_le_norm B))

theorem norm_sub_le_max_ultra (A B : Matrix (Fin n) (Fin n) K) : ‖A - B‖ ≤ max ‖A‖ ‖B‖ := by
  rw [sub_eq_add_neg, ← norm_neg B]
  exact norm_add_le_max_ultra A (-B)

noncomputable def iter (u : Matrix (Fin n) (Fin n) K) : ℕ → Matrix (Fin n) (Fin n) K
  | 0 => 0
  | k + 1 => u - iter u k * iter u k

theorem commute_iter {u a : Matrix (Fin n) (Fin n) K} (h : Commute a u) :
    ∀ k, Commute a (iter u k)
  | 0 => Commute.zero_right a
  | k + 1 => h.sub_right ((commute_iter h k).mul_right (commute_iter h k))

theorem norm_iter_le {u : Matrix (Fin n) (Fin n) K} (hc : ‖u‖ < 1) : ∀ k, ‖iter u k‖ ≤ ‖u‖ := by
  intro k
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    rw [iter]
    refine (norm_sub_le_max_ultra _ _).trans (max_le le_rfl ?_)
    calc ‖iter u k * iter u k‖ ≤ ‖iter u k‖ * ‖iter u k‖ := norm_mul_le_ultra _ _
      _ ≤ ‖u‖ * 1 := mul_le_mul ih (ih.trans hc.le) (norm_nonneg _) (norm_nonneg _)
      _ = ‖u‖ := mul_one _

theorem matrix_sub_mul_self_sub_eq_neg_mul_of_commute (u a b : Matrix (Fin n) (Fin n) K) (h : Commute a b) :
    (u - b * b) - (u - a * a) = -((b - a) * (a + b)) := by
  rw [sub_mul, mul_add, mul_add, ← h.eq]
  abel

theorem norm_iter_diff_le {u : Matrix (Fin n) (Fin n) K} (hc : ‖u‖ < 1) :
    ∀ k, ‖iter u (k + 1) - iter u k‖ ≤ ‖u‖ * ‖u‖ ^ k := by
  intro k
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    have hcomm : Commute (iter u k) (iter u (k + 1)) :=
      commute_iter (commute_iter (Commute.refl u) k).symm (k + 1)
    have hstep : iter u (k + 1 + 1) - iter u (k + 1) =
        (u - iter u (k + 1) * iter u (k + 1)) - (u - iter u k * iter u k) :=
      congrArg₂ (· - ·) (iter.eq_2 u (k + 1)) (iter.eq_2 u k)
    rw [hstep, matrix_sub_mul_self_sub_eq_neg_mul_of_commute u _ _ hcomm, norm_neg]
    have hab : ‖iter u k + iter u (k + 1)‖ ≤ ‖u‖ :=
      (norm_add_le_max_ultra _ _).trans (max_le (norm_iter_le hc k) (norm_iter_le hc (k + 1)))
    calc ‖(iter u (k + 1) - iter u k) * (iter u k + iter u (k + 1))‖
        ≤ ‖iter u (k + 1) - iter u k‖ * ‖iter u k + iter u (k + 1)‖ := norm_mul_le_ultra _ _
      _ ≤ (‖u‖ * ‖u‖ ^ k) * ‖u‖ :=
          mul_le_mul ih hab (norm_nonneg _) (by positivity)
      _ = ‖u‖ * ‖u‖ ^ (k + 1) := by ring

theorem tau_add (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    ((A + B).map σ)ᵀ = (A.map σ)ᵀ + (B.map σ)ᵀ := by
  ext i j; simp

theorem tau_sub (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    ((A - B).map σ)ᵀ = (A.map σ)ᵀ - (B.map σ)ᵀ := by
  ext i j; simp

theorem tau_mul (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    ((A * B).map σ)ᵀ = (B.map σ)ᵀ * (A.map σ)ᵀ := by
  rw [Matrix.map_mul, transpose_mul]

theorem tau_one (σ : K →+* K) : ((1 : Matrix (Fin n) (Fin n) K).map σ)ᵀ = 1 := by
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), transpose_one]

theorem tau_smul (σ : K →+* K) (c : K) (A : Matrix (Fin n) (Fin n) K) :
    ((c • A).map σ)ᵀ = σ c • (A.map σ)ᵀ := by
  ext i j; simp

theorem exists_sqrt [CompleteSpace K] [CharZero K] (σ : K →+* K) (hσ : Continuous σ)
    (s : Matrix (Fin n) (Fin n) K)
    (hs : ∀ i j, ‖s i j - (1 : Matrix (Fin n) (Fin n) K) i j‖ < ‖(4 : K)‖) :
    ∃ r : Matrix (Fin n) (Fin n) K, r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) K,
      a * s = s * a → a * r = r * a) ∧ ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
  have h4 : (4 : K) ≠ 0 := by norm_num
  have h4p : 0 < ‖(4 : K)‖ := norm_pos_iff.2 h4
  set u : Matrix (Fin n) (Fin n) K := (4 : K)⁻¹ • (s - 1) with hu
  have hs1 : ‖s - 1‖ < ‖(4 : K)‖ := (Matrix.norm_lt_iff h4p).2 fun i j => by simpa using hs i j
  have hc : ‖u‖ < 1 := by
    rw [hu, norm_smul, norm_inv, inv_mul_lt_iff₀ h4p, mul_one]
    exact hs1
  have hcs : CauchySeq (iter u) := cauchySeq_of_le_geometric ‖u‖ ‖u‖ hc fun k => by
    rw [dist_eq_norm, norm_sub_rev]; exact norm_iter_diff_le hc k
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcs
  have hfix : y + y * y = u := by
    have h1 : Tendsto (fun k => iter u (k + 1)) atTop (𝓝 y) := hy.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun k => iter u (k + 1)) atTop (𝓝 (u - y * y)) :=
      tendsto_const_nhds.sub (hy.mul hy)
    exact eq_sub_iff_add_eq.1 (tendsto_nhds_unique h1 h2)
  refine ⟨1 + (2 : K) • y, ?_, ?_, ?_⟩
  · calc (1 + (2 : K) • y) * (1 + (2 : K) • y) = 1 + (4 : K) • (y + y * y) := by
          rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm]
          module
      _ = s := by rw [hfix, hu, smul_inv_smul₀ h4]; abel
  · intro a ha
    have hau : Commute a u := ((Commute.sub_right ha (Commute.one_right a))).smul_right _
    have hay : a * y = y * a :=
      tendsto_nhds_unique (hy.const_mul a)
        ((hy.mul_const a).congr fun k => (commute_iter hau k).eq.symm)
    exact ((Commute.one_right a).add_right ((show Commute a y from hay).smul_right (2 : K))).eq
  · intro hsσ
    have hτu : (u.map σ)ᵀ = u := by
      rw [hu, tau_smul, tau_sub, tau_one, hsσ, map_inv₀, map_ofNat]
    have hτiter : ∀ k, ((iter u k).map σ)ᵀ = iter u k := by
      intro k
      induction k with
      | zero => ext i j; simp [iter]
      | succ k ih =>
        show ((u - iter u k * iter u k).map σ)ᵀ = u - iter u k * iter u k
        rw [tau_sub, tau_mul, ih, hτu]
    have hτc : Continuous fun M : Matrix (Fin n) (Fin n) K => (M.map σ)ᵀ :=
      (continuous_id.matrix_map hσ).matrix_transpose
    have hτy : (y.map σ)ᵀ = y :=
      tendsto_nhds_unique ((hτc.tendsto y).comp hy) (hy.congr fun k => (hτiter k).symm)
    rw [tau_add, tau_one, tau_smul, hτy, map_ofNat]

end GlobalTheory.MatSqrtNearOne

namespace GlobalTheory

theorem matrix_sqrt_near_one_ultrametric :
    ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] (n : ℕ) (σ : K →+* K), Continuous σ →
      ∃ W ∈ nhds (1 : Matrix (Fin n) (Fin n) K), ∀ s ∈ W, ∃ r : Matrix (Fin n) (Fin n) K,
        r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) K, a * s = s * a → a * r = r * a) ∧
        ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
  intro K _ _ _ _ n σ hσ
  have h4 : (4 : K) ≠ 0 := by norm_num
  refine ⟨{s | ∀ i j, ‖s i j - (1 : Matrix (Fin n) (Fin n) K) i j‖ < ‖(4 : K)‖}, ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ (by simp [h4])
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt ((continuous_id.matrix_elem i j).sub continuous_const).norm continuous_const
  · intro s hs
    exact MatSqrtNearOne.exists_sqrt σ hσ s hs

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixSqrtNearOneUltrametricStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrix_sqrt_near_one_ultrametric : ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] (n : ℕ) (σ : K →+* K), Continuous σ → ∃ W ∈ nhds (1 : Matrix (Fin n) (Fin n) K), ∀ s ∈ W, ∃ r : Matrix (Fin n) (Fin n) K, r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) K, a * s = s * a → a * r = r * a) ∧ ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
  first | exact @GlobalTheory.matrix_sqrt_near_one_ultrametric | exact GlobalTheory.matrix_sqrt_near_one_ultrametric | (intros; apply GlobalTheory.matrix_sqrt_near_one_ultrametric <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussUnitsNormSq
open ComplexConjugate Finset

namespace GlobalTheory

namespace GaussUnits

variable {R : Type} [CommRing R] [Fintype R]

theorem sum_ideal_of_exists (I : Ideal R) [DecidablePred (· ∈ I)] (ψ : AddChar R ℂ)
    (hψ : ∀ d : R, (∀ x, ψ (d * x) = 1) → d = 0) (b : R) (hb : ∃ x ∈ I, b * x ≠ 0) :
    ∑ x, (if x ∈ I then ψ (b * x) else 0) = 0 := by
  obtain ⟨x₀, hx₀I, hx₀⟩ := hb
  have hne : ¬ ∀ r, ψ (b * x₀ * r) = 1 := fun h => hx₀ (hψ _ h)
  push_neg at hne
  obtain ⟨r, hr⟩ := hne
  have hyI : x₀ * r ∈ I := I.mul_mem_right r hx₀I
  have hby : ψ (b * (x₀ * r)) ≠ 1 := by rwa [← mul_assoc]
  have hshift := Fintype.sum_equiv (Equiv.addRight (x₀ * r))
    (fun x => if x + x₀ * r ∈ I then ψ (b * (x + x₀ * r)) else 0)
    (fun x => if x ∈ I then ψ (b * x) else 0) (fun _ => rfl)
  have hS : ∑ x, (if x ∈ I then ψ (b * x) else 0)
      = ψ (b * (x₀ * r)) * ∑ x, (if x ∈ I then ψ (b * x) else 0) := by
    conv_lhs => rw [← hshift]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : x ∈ I
    · have h' : x + x₀ * r ∈ I := I.add_mem hx hyI
      rw [if_pos h', if_pos hx, mul_add, AddChar.map_add_eq_mul, mul_comm]
    · have h' : x + x₀ * r ∉ I := fun h => hx (by simpa using I.sub_mem h hyI)
      rw [if_neg h', if_neg hx, mul_zero]
  have h1 : (1 - ψ (b * (x₀ * r))) * ∑ x, (if x ∈ I then ψ (b * x) else 0) = 0 := by
    rw [sub_mul, one_mul, ← hS, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hby
  · exact h

theorem sum_ideal_of_forall (I : Ideal R) [DecidablePred (· ∈ I)] (ψ : AddChar R ℂ) (b : R)
    (hb : ∀ x ∈ I, b * x = 0) :
    ∑ x, (if x ∈ I then ψ (b * x) else 0) = ((univ.filter (· ∈ I)).card : ℂ) := by
  rw [← Finset.sum_filter, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.mem_filter] at hx
  rw [hb x hx.2, AddChar.map_zero_eq_one, Nat.cast_one]

theorem sum_units_eq (m : Ideal R) [DecidablePred (· ∈ m)] [Fintype Rˣ]
    (hm : ∀ x : R, IsUnit x ↔ x ∉ m) (f : R → ℂ) :
    ∑ u : Rˣ, f u = ∑ x, f x - ∑ x, (if x ∈ m then f x else 0) := by
  have h : ∑ u : Rˣ, f u = ∑ x ∈ univ.filter (fun x => ¬ x ∈ m), f x := by
    refine Finset.sum_bij (fun u _ => (u : R)) ?_ ?_ ?_ ?_
    · intro u _
      rw [Finset.mem_filter]
      exact ⟨mem_univ _, (hm u).mp u.isUnit⟩
    · intro a _ b _ h
      exact Units.ext h
    · intro x hx
      rw [Finset.mem_filter] at hx
      exact ⟨((hm x).mpr hx.2).unit, mem_univ _, rfl⟩
    · intro u _
      rfl
  rw [h, eq_sub_iff_add_eq, ← Finset.sum_filter, add_comm, Finset.sum_filter_add_sum_filter_not]

end GaussUnits


open GaussUnits in
theorem gauss_units_norm_sq : ∀ {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [Fintype Rˣ]
    (m : Ideal R), (∀ x : R, IsUnit x ↔ x ∉ m) → ∀ (ψ : AddChar R ℂ),
    (∀ d : R, (∀ x, ψ (d * x) = 1) → d = 0) → ∀ (χ : Rˣ → ℂ), (∀ u v, χ (u * v) = χ u * χ v) →
    (∀ u, ‖χ u‖ = 1) → ∀ (t₀ : Rˣ), (∀ x ∈ m, ((t₀ : R) - 1) * x = 0) → χ t₀ ≠ 1 →
    ‖∑ u : Rˣ, (χ u)⁻¹ * ψ u‖ ^ 2 = Fintype.card R := by
  intro R _ _ _ _ m hm ψ hψ χ hχ hχn t₀ ht₀ hχt₀
  classical
  have hχ0 : ∀ u, χ u ≠ 0 := fun u h => by simpa [h] using hχn u
  have hχ1 : χ 1 = 1 := by
    have h := hχ 1 1
    rw [mul_one] at h
    have h2 : χ 1 * (χ 1 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (hχ0 1)
    · exact sub_eq_zero.mp h3
  have hconj : conj (∑ u : Rˣ, (χ u)⁻¹ * ψ u) = ∑ z : Rˣ, χ z * ψ (-(z : R)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [map_mul, Complex.inv_eq_conj (hχn z), Complex.conj_conj, AddChar.map_neg_eq_conj]
  have hexp : (∑ u : Rˣ, (χ u)⁻¹ * ψ u) * conj (∑ u : Rˣ, (χ u)⁻¹ * ψ u)
      = ∑ t : Rˣ, (χ t)⁻¹ * ∑ z : Rˣ, ψ (((t : R) - 1) * z) := by
    rw [hconj, Finset.sum_mul_sum, Finset.sum_comm]
    have hz : ∀ z : Rˣ, ∑ y : Rˣ, (χ y)⁻¹ * ψ y * (χ z * ψ (-(z : R)))
        = ∑ t : Rˣ, (χ t)⁻¹ * ψ (((t : R) - 1) * z) := by
      intro z
      refine Fintype.sum_equiv (Equiv.mulRight z⁻¹) _ _ (fun y => ?_)
      have hzinv : χ z⁻¹ = (χ z)⁻¹ := by
        have h := hχ z z⁻¹
        rw [mul_inv_cancel, hχ1] at h
        exact eq_inv_of_mul_eq_one_right h.symm
      have harg : (((y * z⁻¹ : Rˣ) : R) - 1) * (z : R) = (y : R) + -(z : R) := by
        rw [sub_mul, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          mul_one, one_mul, sub_eq_add_neg]
      simp only [Equiv.coe_mulRight]
      rw [harg, AddChar.map_add_eq_mul, hχ, hzinv, mul_inv, inv_inv]
      ring
    rw [Finset.sum_congr rfl (fun z _ => hz z), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
  have hinner : ∀ t : Rˣ, ∑ z : Rˣ, ψ (((t : R) - 1) * z) =
      (if t = 1 then (Fintype.card R : ℂ) else 0) -
      (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then ((univ.filter (· ∈ m)).card : ℂ) else 0) := by
    intro t
    rw [sum_units_eq m hm (fun x => ψ (((t : R) - 1) * x))]
    congr 1
    · have htop : ∑ x, ψ (((t : R) - 1) * x)
          = ∑ x, (if x ∈ (⊤ : Ideal R) then ψ (((t : R) - 1) * x) else 0) := by simp
      rw [htop]
      split_ifs with h
      · subst h
        rw [sum_ideal_of_forall ⊤ ψ _ (by simp)]
        simp
      · apply sum_ideal_of_exists ⊤ ψ hψ
        refine ⟨1, Submodule.mem_top, ?_⟩
        rw [mul_one, sub_ne_zero]
        exact fun h' => h (Units.val_eq_one.mp h')
    · split_ifs with h
      · exact sum_ideal_of_forall m ψ _ h
      · push_neg at h
        exact sum_ideal_of_exists m ψ hψ _ h
  have hcond : ∀ t : Rˣ, (∀ x ∈ m, (((t₀ * t : Rˣ) : R) - 1) * x = 0) ↔
      (∀ x ∈ m, ((t : R) - 1) * x = 0) := by
    intro t
    constructor
    · intro h x hx
      have h1 := h x hx
      have h2 := ht₀ x hx
      rw [Units.val_mul] at h1
      have h3 : (t₀ : R) * (((t : R) - 1) * x) = 0 := by linear_combination h1 - h2
      exact t₀.isUnit.mul_right_eq_zero.mp h3
    · intro h x hx
      have h1 := h x hx
      have h2 := ht₀ x hx
      rw [Units.val_mul]
      linear_combination (t₀ : R) * h1 + h2
  have hS : ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) = 0 := by
    have e := Fintype.sum_equiv (Equiv.mulLeft t₀)
      (fun t => if (∀ x ∈ m, (((t₀ * t : Rˣ) : R) - 1) * x = 0) then (χ (t₀ * t))⁻¹ else 0)
      (fun t => if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) (fun _ => rfl)
    have hS' : ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0)
        = (χ t₀)⁻¹ * ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) := by
      conv_lhs => rw [← e]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      simp only [hcond t, hχ, mul_inv, mul_ite, mul_zero]
    have hne : (χ t₀)⁻¹ ≠ 1 := fun h => hχt₀ (inv_eq_one.mp h)
    have h1 : (1 - (χ t₀)⁻¹) *
        ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0) = 0 := by
      rw [sub_mul, one_mul, ← hS', sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  have hmain : (∑ u : Rˣ, (χ u)⁻¹ * ψ u) * conj (∑ u : Rˣ, (χ u)⁻¹ * ψ u)
      = (Fintype.card R : ℂ) := by
    rw [hexp]
    simp_rw [hinner, mul_sub, mul_ite, mul_zero]
    rw [Finset.sum_sub_distrib]
    have h2 : ∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then
        (χ t)⁻¹ * ((univ.filter (· ∈ m)).card : ℂ) else 0)
        = (∑ t : Rˣ, (if (∀ x ∈ m, ((t : R) - 1) * x = 0) then (χ t)⁻¹ else 0)) *
          ((univ.filter (· ∈ m)).card : ℂ) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs <;> simp
    rw [h2, hS, zero_mul, sub_zero]
    simp [hχ1]
  have hn : ((‖∑ u : Rˣ, (χ u)⁻¹ * ψ u‖ ^ 2 : ℝ) : ℂ) = (Fintype.card R : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hmain]
  exact_mod_cast hn

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafGlueOfOpenImmersions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafGlueOfOpenImmersions
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace GlobalTheory.IdealGlue

lemma res_bijective {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) (e : U = V) :
    Function.Bijective (X.presheaf.map (homOfLE h).op).hom := by
  subst e
  have : homOfLE h = 𝟙 U := Subsingleton.elim _ _
  rw [this, op_id, X.presheaf.map_id]
  exact Function.bijective_id

lemma app_bijective {Q X : Scheme.{u}} (f : Q ⟶ X) [IsOpenImmersion f] (W : X.Opens)
    (hW : W ≤ f.opensRange) : Function.Bijective (f.app W).hom := by
  have h2 : f.app W = X.presheaf.map (homOfLE (f.image_preimage_le W)).op ≫
      (f.appIso (f ⁻¹ᵁ W)).hom := by
    rw [← Category.comp_id (f.app W), ← Iso.inv_hom_id (f.appIso (f ⁻¹ᵁ W)), ← Category.assoc,
      f.app_appIso_inv]
    rfl
  rw [h2, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Bijective.comp (f.appIso (f ⁻¹ᵁ W)).commRingCatIsoToRingEquiv.bijective
    (res_bijective _ ?_)
  rw [f.image_preimage_eq_opensRange_inf]
  exact inf_eq_right.mpr hW

noncomputable def loc {P X : Scheme.{u}} (f : P ⟶ X) (J : P.IdealSheafData) (W : X.affineOpens)
    (h : IsAffineOpen (f ⁻¹ᵁ W.1)) : Ideal Γ(X, W) :=
  (J.ideal ⟨f ⁻¹ᵁ W.1, h⟩).comap (f.app W.1).hom

lemma loc_congr {P X : Scheme.{u}} {f f' : P ⟶ X} (hf : f = f') {J J' : P.IdealSheafData}
    (hJ : J = J') (W : X.affineOpens) (h : IsAffineOpen (f ⁻¹ᵁ W.1))
    (h' : IsAffineOpen (f' ⁻¹ᵁ W.1)) : loc f J W h = loc f' J' W h' := by
  subst hf hJ; rfl

lemma loc_comap {Q X : Scheme.{u}} (f : Q ⟶ X) [IsOpenImmersion f] (I : X.IdealSheafData)
    (W : X.affineOpens) (hW : W.1 ≤ f.opensRange) (h : IsAffineOpen (f ⁻¹ᵁ W.1)) :
    loc f (I.comap f) W h = I.ideal W := by
  unfold loc
  have hle : (⟨f ''ᵁ f ⁻¹ᵁ W.1, h.image_of_isOpenImmersion f⟩ : X.affineOpens) ≤ W :=
    f.image_preimage_le W.1
  have e1 := I.ideal_comap_of_isOpenImmersion f ⟨f ⁻¹ᵁ W.1, h⟩
  have e2 := I.map_ideal hle
  rw [e1, Ideal.comap_comap, ← CommRingCat.hom_comp, f.app_appIso_inv]
  refine Eq.trans ?_ (Ideal.comap_map_of_bijective _ (res_bijective (f.image_preimage_le W.1) (by
    rw [f.image_preimage_eq_opensRange_inf]; exact inf_eq_right.mpr hW)) (I := I.ideal W))
  exact congrArg _ e2.symm

lemma loc_comp {Q' Q X : Scheme.{u}} (g : Q' ⟶ Q) (f : Q ⟶ X) [IsOpenImmersion g]
    [IsOpenImmersion f] (J : Q.IdealSheafData) (W : X.affineOpens)
    (hW : W.1 ≤ (g ≫ f).opensRange) (h1 : IsAffineOpen ((g ≫ f) ⁻¹ᵁ W.1))
    (h2 : IsAffineOpen (f ⁻¹ᵁ W.1)) :
    loc (g ≫ f) (J.comap g) W h1 = loc f J W h2 := by
  have hle : f ⁻¹ᵁ W.1 ≤ g.opensRange := by
    intro y hy
    obtain ⟨z, hz⟩ := hW hy
    refine ⟨z, f.isOpenEmbedding.injective ?_⟩
    simpa using hz
  have := loc_comap g J ⟨f ⁻¹ᵁ W.1, h2⟩ hle
    (by simpa [Scheme.Hom.comp_preimage] using h1)
  unfold loc at this ⊢
  calc _ = (((J.comap g).ideal ⟨(g ≫ f) ⁻¹ᵁ W.1, h1⟩).comap
        (g.app (f ⁻¹ᵁ W.1)).hom).comap (f.app W.1).hom := by
          exact (congrArg (fun φ => Ideal.comap (CommRingCat.Hom.hom φ)
            ((J.comap g).ideal ⟨(g ≫ f) ⁻¹ᵁ W.1, h1⟩)) (Scheme.Hom.comp_app g f W.1)).trans rfl
    _ = _ := congrArg (Ideal.comap (f.app W.1).hom) this

end GlobalTheory.IdealGlue

namespace GlobalTheory.IdealGlue

lemma ideal_transfer {A A' B B' : CommRingCat.{u}} (φ : A ⟶ B) (φ' : A' ⟶ B') (ρ : A ⟶ A')
    (ρ' : B ⟶ B') (hc : ρ ≫ φ' = φ ≫ ρ') (hb : Function.Bijective φ.hom)
    (hb' : Function.Bijective φ'.hom) (𝔞 : Ideal B) :
    (𝔞.comap φ.hom).map ρ.hom = (𝔞.map ρ'.hom).comap φ'.hom := by
  calc (𝔞.comap φ.hom).map ρ.hom
      = (((𝔞.comap φ.hom).map ρ.hom).map φ'.hom).comap φ'.hom :=
        (Ideal.comap_map_of_bijective _ hb').symm
    _ = (((𝔞.comap φ.hom).map φ.hom).map ρ'.hom).comap φ'.hom := by
        rw [Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hc]
    _ = (𝔞.map ρ'.hom).comap φ'.hom := by rw [Ideal.map_comap_of_surjective _ hb.2]

lemma loc_map {P X : Scheme.{u}} (f : P ⟶ X) [IsOpenImmersion f] (J : P.IdealSheafData)
    (W W' : X.affineOpens) (hle : W' ≤ W) (hW : W.1 ≤ f.opensRange)
    (h : IsAffineOpen (f ⁻¹ᵁ W.1)) (h' : IsAffineOpen (f ⁻¹ᵁ W'.1)) :
    (loc f J W h).map (X.presheaf.map (homOfLE hle).op).hom = loc f J W' h' := by
  have hW' : W'.1 ≤ f.opensRange := (show W'.1 ≤ W.1 from hle).trans hW
  have hJ := J.map_ideal' (U := ⟨f ⁻¹ᵁ W'.1, h'⟩) (V := ⟨f ⁻¹ᵁ W.1, h⟩)
    ((TopologicalSpace.Opens.map f.base).map (homOfLE hle).op.unop).op
  exact (ideal_transfer _ _ _ _ (f.naturality (homOfLE hle).op) (app_bijective f W.1 hW)
    (app_bijective f W'.1 hW') _).trans (congrArg _ hJ)

lemma loc_indep {X : Scheme.{u}} {ι : Type*} (P : ι → Scheme.{u}) (e : ∀ i, P i ⟶ X)
    [∀ i, IsOpenImmersion (e i)] (K : ∀ i, (P i).IdealSheafData)
    (hK : ∀ i j (Q : Scheme.{u}) (a : Q ⟶ P i) (b : Q ⟶ P j), a ≫ e i = b ≫ e j →
      (K i).comap a = (K j).comap b)
    (i j : ι) (W : X.affineOpens) (hi : W.1 ≤ (e i).opensRange) (hj : W.1 ≤ (e j).opensRange)
    (h : IsAffineOpen ((e i) ⁻¹ᵁ W.1)) (h' : IsAffineOpen ((e j) ⁻¹ᵁ W.1)) :
    loc (e i) (K i) W h = loc (e j) (K j) W h' := by
  have hc := pullback.condition (f := e i) (g := e j)
  have hr : W.1 ≤ (pullback.fst (e i) (e j) ≫ e i).opensRange := by
    intro x hx
    have : x ∈ Set.range (pullback.fst (e i) (e j) ≫ e i) := by
      rw [IsOpenImmersion.range_pullback_to_base_of_left]
      exact ⟨hi hx, hj hx⟩
    exact this
  have hr' : W.1 ≤ (pullback.snd (e i) (e j) ≫ e j).opensRange := by
    intro x hx
    have : x ∈ Set.range (pullback.snd (e i) (e j) ≫ e j) := by
      rw [← hc]
      exact hr hx
    exact this
  rw [← loc_comp (pullback.fst (e i) (e j)) (e i) (K i) W hr
      (W.2.preimage_of_isOpenImmersion _ hr) h,
    ← loc_comp (pullback.snd (e i) (e j)) (e j) (K j) W hr'
      (W.2.preimage_of_isOpenImmersion _ hr') h']
  exact loc_congr hc (hK i j _ _ _ hc) _ _ _

theorem idealSheaf_glue_of_openImmersions :
    (∀ {X : Scheme.{0}} (𝒜 : Set X.affineOpens), (∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜) →
      (∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) → ∀ (k : ∀ W : X.affineOpens, Ideal Γ(X, W)),
      (∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W),
        (k W).map (X.presheaf.map (homOfLE h).op).hom = k W') →
      ∃ I : X.IdealSheafData, ∀ W ∈ 𝒜, I.ideal W = k W) →
    ∀ {X : Scheme.{0}} {ι : Type*} (P : ι → Scheme.{0}) (e : ∀ i, P i ⟶ X),
      (∀ i, IsOpenImmersion (e i)) → (∀ x : X, ∃ i, x ∈ Set.range (e i)) →
      ∀ (K : ∀ i, (P i).IdealSheafData),
      (∀ i j (Q : Scheme.{0}) (a : Q ⟶ P i) (b : Q ⟶ P j), a ≫ e i = b ≫ e j →
        (K i).comap a = (K j).comap b) →
      ∃ I : X.IdealSheafData, ∀ i, I.comap (e i) = K i := by
  intro hA X ι P e he hcov K hK
  classical
  have haff : ∀ i (W : X.affineOpens), W.1 ≤ (e i).opensRange → IsAffineOpen ((e i) ⁻¹ᵁ W.1) :=
    fun i W hW => W.2.preimage_of_isOpenImmersion (e i) hW
  let k : ∀ W : X.affineOpens, Ideal Γ(X, W) := fun W =>
    if hex : ∃ i, W.1 ≤ (e i).opensRange then
      loc (e hex.choose) (K hex.choose) W (haff _ W hex.choose_spec) else ⊤
  have hk : ∀ i (W : X.affineOpens) (hW : W.1 ≤ (e i).opensRange),
      k W = loc (e i) (K i) W (haff i W hW) := by
    intro i W hW
    have hex : ∃ i, W.1 ≤ (e i).opensRange := ⟨i, hW⟩
    simp only [k, dif_pos hex]
    exact loc_indep P e K hK _ _ W hex.choose_spec hW _ _
  have hcov' : ∀ x : X, ∃ W : X.affineOpens, ∃ i, W.1 ≤ (e i).opensRange ∧ x ∈ W.1 := by
    intro x
    obtain ⟨i, y, rfl⟩ := hcov x
    obtain ⟨W, hW, hxW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show e i y ∈ (e i).opensRange from ⟨y, rfl⟩)
    exact ⟨⟨W, hW⟩, i, hWle, hxW⟩
  obtain ⟨I, hI⟩ := hA {W | ∃ i, W.1 ≤ (e i).opensRange}
    (fun W ⟨i, hi⟩ W' hW' => ⟨i, (show W'.1 ≤ W.1 from hW').trans hi⟩)
    (fun x => by
      obtain ⟨W, i, hi, hx⟩ := hcov' x
      exact ⟨W, ⟨i, hi⟩, hx⟩)
    k
    (fun W ⟨i, hi⟩ W' hW' => by
      have hi' : W'.1 ≤ (e i).opensRange := (show W'.1 ≤ W.1 from hW').trans hi
      rw [hk i W hi, hk i W' hi']
      exact loc_map (e i) (K i) W W' hW' hi _ _)
  refine ⟨I, fun i => ?_⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := {W : X.affineOpens // W.1 ≤ (e i).opensRange})
    (fun W => ⟨(e i) ⁻¹ᵁ W.1.1, haff i W.1 W.2⟩) ?_ ?_
  · rw [eq_top_iff]
    intro y _
    obtain ⟨W, hW, hyW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show e i y ∈ (e i).opensRange from ⟨y, rfl⟩)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWle⟩, hyW⟩
  · intro W
    apply Ideal.comap_injective_of_surjective _ (app_bijective (e i) W.1.1 W.2).2
    have h1 := loc_comap (e i) I W.1 W.2 (haff i W.1 W.2)
    have h2 := hk i W.1 W.2
    have h3 := hI W.1 ⟨i, W.2⟩
    exact h1.trans (h3.trans h2)

end GlobalTheory.IdealGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafGlueOfOpenImmersionsStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idealSheafData_glue_of_openImmersions : (∀ {X : Scheme.{0}} (𝒜 : Set X.affineOpens), (∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜) → (∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) → ∀ (k : ∀ W : X.affineOpens, Ideal Γ(X, W)), (∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W), (k W).map (X.presheaf.map (homOfLE h).op).hom = k W') → ∃ I : X.IdealSheafData, ∀ W ∈ 𝒜, I.ideal W = k W) → ∀ {X : Scheme.{0}} {ι : Type*} (P : ι → Scheme.{0}) (e : ∀ i, P i ⟶ X), (∀ i, IsOpenImmersion (e i)) → (∀ x : X, ∃ i, x ∈ Set.range (e i)) → ∀ (K : ∀ i, (P i).IdealSheafData), (∀ i j (Q : Scheme.{0}) (a : Q ⟶ P i) (b : Q ⟶ P j), a ≫ e i = b ≫ e j → (K i).comap a = (K j).comap b) → ∃ I : X.IdealSheafData, ∀ i, I.comap (e i) = K i := by
  first | (exact @GlobalTheory.IdealGlue.idealSheaf_glue_of_openImmersions) | (exact GlobalTheory.IdealGlue.idealSheaf_glue_of_openImmersions) | (intros; apply GlobalTheory.IdealGlue.idealSheaf_glue_of_openImmersions  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomCompAlgebraMapEq
universe u_1 u_2 u_3

namespace GlobalTheory.InjectiveAlgebraHomExistence

theorem exists_algHom_of_injective {A : Type u_1} {B : Type u_2} {K : Type u_3}
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field K] [IsAlgClosed K]
    [Algebra A B] [Algebra A K] [Algebra.IsIntegral A B]
    (hB : Function.Injective (algebraMap A B)) (hK : Function.Injective (algebraMap A K)) :
    Nonempty (B →ₐ[A] K) := by
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).2 hB
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective _ _).2 hK
  exact ⟨IsAlgClosed.lift⟩

theorem exists_ringHom_comp_algebraMap_eq {R : Type u_1} {S : Type u_2} {K : Type u_3}
    [CommRing R] [CommRing S] [Field K] [IsAlgClosed K] [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) (ψ : R →+* K) :
    ∃ x : S →+* K, x.comp (algebraMap R S) = ψ := by
  have hp : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    (RingHom.ker ψ) ⊥ (by
      intro r hr
      have h0 : algebraMap R S r = 0 := by simpa using hr
      have : r = 0 := hinj (by simpa using h0)
      simp [this])
  let f : R ⧸ RingHom.ker ψ →+* S ⧸ Q := Ideal.quotientMap Q (algebraMap R S) hQp.ge
  have hf : Function.Injective f := Ideal.quotientMap_injective' hQp.le
  letI : Algebra (R ⧸ RingHom.ker ψ) (S ⧸ Q) := f.toAlgebra
  letI : Algebra (R ⧸ RingHom.ker ψ) K := (RingHom.kerLift ψ).toAlgebra
  haveI : Algebra.IsIntegral (R ⧸ RingHom.ker ψ) (S ⧸ Q) := by
    constructor
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨P, hP, hs⟩ := Algebra.IsIntegral.isIntegral (R := R) s
    refine ⟨P.map (Ideal.Quotient.mk _), hP.map _, ?_⟩
    have hc : (algebraMap (R ⧸ RingHom.ker ψ) (S ⧸ Q)).comp (Ideal.Quotient.mk _)
        = (Ideal.Quotient.mk Q).comp (algebraMap R S) := by
      ext r
      rfl
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, hs, map_zero]
  obtain ⟨g⟩ : Nonempty ((S ⧸ Q) →ₐ[R ⧸ RingHom.ker ψ] K) :=
    exists_algHom_of_injective hf (RingHom.kerLift_injective ψ)
  refine ⟨(g : (S ⧸ Q) →+* K).comp (Ideal.Quotient.mk Q), ?_⟩
  ext r
  have := g.commutes (Ideal.Quotient.mk _ r)
  exact this

end GlobalTheory.InjectiveAlgebraHomExistence
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMkOfComp
namespace GlobalTheory.QuotientMapComposition

theorem map_mk'_of_comp {A R LA LR : Type} [CommRing A] [CommRing R] [CommRing LA] [CommRing LR]
    [Algebra A LA] [Algebra R LR] (f : A →+* R) (F : LA →+* LR)
    (h : F.comp (algebraMap A LA) = (algebraMap R LR).comp f) (M : Submonoid A) [IsLocalization M LA]
    (N : Submonoid R) [IsLocalization N LR] (a : A) (m : M) (n : N) (hn : (n : R) = f m) :
    F (IsLocalization.mk' LA a m) = IsLocalization.mk' LR (f a) n := by
  have hx : ∀ x, F (algebraMap A LA x) = algebraMap R LR (f x) := fun x => RingHom.congr_fun h x
  rw [IsLocalization.eq_mk'_iff_mul_eq, hn, ← hx, ← hx, ← map_mul, IsLocalization.mk'_spec]

theorem main : ∀ {A R₀ A' B₀ : Type} [inst : CommRing A] [inst_1 : CommRing R₀] [inst_2 : CommRing A'] [inst_3 : CommRing B₀] (φ : A →+* R₀) (ψ : A →+* A') (α : R₀ →+* B₀) (κ : A' →+* B₀), RingHom.comp α φ = RingHom.comp κ ψ → (∀ (a : A), (φ : A → R₀) a = (0 : R₀) → (ψ : A → A') a = (0 : A') → a = (0 : A)) → (∀ (r : R₀) (c : A'), (α : R₀ → B₀) r = (κ : A' → B₀) c → ∃ (a : A), (φ : A → R₀) a = r ∧ (ψ : A → A') a = c) → ∀ (s : A) (LA LR LA' LB : Type) [inst_4 : CommRing LA] [inst_5 : CommRing LR] [inst_6 : CommRing LA'] [inst_7 : CommRing LB] [inst_8 : Algebra A LA] [inst_9 : Algebra R₀ LR] [inst_10 : Algebra A' LA'] [inst_11 : Algebra B₀ LB] [IsLocalization.Away s LA] [IsLocalization.Away ((φ : A → R₀) s) LR] [IsLocalization.Away ((ψ : A → A') s) LA'] [IsLocalization.Away ((α : R₀ → B₀) ((φ : A → R₀) s)) LB] (Φ : LA →+* LR) (Ψ : LA →+* LA') (Aα : LR →+* LB) (Kκ : LA' →+* LB), RingHom.comp Φ (Algebra.algebraMap A LA) = RingHom.comp (Algebra.algebraMap R₀ LR) φ → RingHom.comp Ψ (Algebra.algebraMap A LA) = RingHom.comp (Algebra.algebraMap A' LA') ψ → RingHom.comp Aα (Algebra.algebraMap R₀ LR) = RingHom.comp (Algebra.algebraMap B₀ LB) α → RingHom.comp Kκ (Algebra.algebraMap A' LA') = RingHom.comp (Algebra.algebraMap B₀ LB) κ → (∀ (t : LA), (Φ : LA → LR) t = (0 : LR) → (Ψ : LA → LA') t = (0 : LA') → t = (0 : LA)) ∧ ∀ (a : LR) (b : LA'), (Aα : LR → LB) a = (Kκ : LA' → LB) b → ∃ (t : LA), (Φ : LA → LR) t = a ∧ (Ψ : LA → LA') t = b := by
  intro A R₀ A' B₀ _ _ _ _ φ ψ α κ h0 hinj hsurj s LA LR LA' LB _ _ _ _ _ _ _ _ _ _ _ _ Φ Ψ Aα Kκ hΦ hΨ hA hK
  have hu : κ (ψ s) = α (φ s) := (RingHom.congr_fun h0 s).symm
  constructor
  · intro t ht1 ht2
    obtain ⟨⟨a, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) t
    rw [map_mk'_of_comp φ Φ hΦ (Submonoid.powers s) (Submonoid.powers (φ s)) a _ ⟨φ s ^ n, n, rfl⟩ (by simp),
      IsLocalization.mk'_eq_zero_iff] at ht1
    rw [map_mk'_of_comp ψ Ψ hΨ (Submonoid.powers s) (Submonoid.powers (ψ s)) a _ ⟨ψ s ^ n, n, rfl⟩ (by simp),
      IsLocalization.mk'_eq_zero_iff] at ht2
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := ht1
    obtain ⟨⟨_, l, rfl⟩, hl⟩ := ht2
    change φ s ^ k * φ a = 0 at hk
    change ψ s ^ l * ψ a = 0 at hl
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨s ^ (k + l), k + l, rfl⟩, hinj _ ?_ ?_⟩
    · change φ (s ^ (k + l) * a) = 0
      rw [map_mul, map_pow, pow_add, mul_right_comm, hk, zero_mul]
    · change ψ (s ^ (k + l) * a) = 0
      rw [map_mul, map_pow, pow_add, mul_assoc, hl, mul_zero]
  · intro a b hab
    obtain ⟨⟨r, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (φ s)) a
    obtain ⟨⟨c, _, m, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (ψ s)) b
    rw [map_mk'_of_comp α Aα hA (Submonoid.powers (φ s)) (Submonoid.powers (α (φ s))) r _
        ⟨α (φ s) ^ n, n, rfl⟩ (by simp),
      map_mk'_of_comp κ Kκ hK (Submonoid.powers (ψ s)) (Submonoid.powers (α (φ s))) c _
        ⟨α (φ s) ^ m, m, rfl⟩ (by simp [hu]),
      IsLocalization.mk'_eq_iff_eq, IsLocalization.eq_iff_exists (Submonoid.powers (α (φ s)))] at hab
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := hab
    change α (φ s) ^ k * (α (φ s) ^ m * α r) = α (φ s) ^ k * (α (φ s) ^ n * κ c) at hk
    obtain ⟨a0, ha1, ha2⟩ := hsurj (φ s ^ (k + m) * r) (ψ s ^ (k + n) * c) (by
      rw [map_mul, map_pow, map_mul, map_pow, hu, pow_add, pow_add, mul_assoc, mul_assoc]; exact hk)
    refine ⟨IsLocalization.mk' LA a0 (⟨s ^ (n + k + m), n + k + m, rfl⟩ : Submonoid.powers s), ?_, ?_⟩
    · rw [map_mk'_of_comp φ Φ hΦ (Submonoid.powers s) (Submonoid.powers (φ s)) a0 _
        ⟨φ s ^ (n + k + m), _, rfl⟩ (by simp), IsLocalization.mk'_eq_iff_eq]
      congr 1
      change φ s ^ n * φ a0 = φ s ^ (n + k + m) * r
      rw [ha1]; ring
    · rw [map_mk'_of_comp ψ Ψ hΨ (Submonoid.powers s) (Submonoid.powers (ψ s)) a0 _
        ⟨ψ s ^ (n + k + m), _, rfl⟩ (by simp), IsLocalization.mk'_eq_iff_eq]
      congr 1
      change ψ s ^ m * ψ a0 = ψ s ^ (n + k + m) * c
      rw [ha2]; ring

end GlobalTheory.QuotientMapComposition
end
