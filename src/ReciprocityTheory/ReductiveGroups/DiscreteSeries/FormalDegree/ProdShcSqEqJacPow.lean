module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPPos

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ShcAdC
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbC
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbA
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

theorem dpb_sylv (f : W →ₗ[ℝ] V) (g : V →ₗ[ℝ] W) :
    LinearMap.det (1 + f ∘ₗ g : V →ₗ[ℝ] V) = LinearMap.det (1 + g ∘ₗ f : W →ₗ[ℝ] W) := by
  classical
  let bV := Module.finBasis ℝ V
  let bW := Module.finBasis ℝ W
  rw [← LinearMap.det_toMatrix bV, ← LinearMap.det_toMatrix bW, map_add (f := _), map_add (f := _),
    LinearMap.toMatrix_comp bV bW bV, LinearMap.toMatrix_comp bW bV bW, LinearMap.toMatrix_one,
    LinearMap.toMatrix_one]
  exact Matrix.det_one_add_mul_comm _ _

theorem dpb_ring {R : Type*} [Ring R] (a p q : R) (h0 : p * q = 0) (hc : p * a = a * p) :
    (1 + a * p) * (1 + a * q) = 1 + a * (p + q) := by
  have h : a * p * (a * q) = 0 := by
    rw [mul_assoc, ← mul_assoc p a q, hc, mul_assoc, h0, mul_zero, mul_zero]
  calc (1 + a * p) * (1 + a * q) = 1 + a * p + a * q + a * p * (a * q) := by noncomm_ring
    _ = 1 + a * (p + q) := by rw [h, add_zero, mul_add, add_assoc]

theorem det_one_add_compression (a p q r s ι κ N C : Module.End ℝ V) (E : W →ₗ[ℝ] V) (P : V →ₗ[ℝ] W)
    (hpq : p + q = 1) (hpq0 : p * q = 0) (hpa : p * a = a * p)
    (hNC : N * C = a) (hCN : C * N = a) (hpN : p * N = N * q)
    (hrs : r + s = q) (hrs0 : r * s = 0) (hra : r * a = a * r)
    (hι : ι * κ = 1) (hιa : ι * a = a * ι) (hιr : ι * r = s * ι)
    (hEP : E ∘ₗ P = r) :
    LinearMap.det (1 + a) = LinearMap.det (1 + P ∘ₗ a ∘ₗ E : W →ₗ[ℝ] W) ^ 4 := by
  have hsy : ∀ X Y : Module.End ℝ V, LinearMap.det (1 + X * Y) = LinearMap.det (1 + Y * X) :=
    fun X Y => dpb_sylv X Y
  have hA : 1 + a = (1 + a * p) * (1 + a * q) := by rw [dpb_ring a p q hpq0 hpa, hpq, mul_one]
  have hq : q = 1 - p := eq_sub_of_add_eq' hpq
  have hqa : q * a = a * q := by rw [hq, sub_mul, mul_sub, one_mul, mul_one, hpa]
  have hB1 : a * p = N * (q * C) := by rw [← hpa, ← hNC, ← mul_assoc, hpN, mul_assoc]
  have hB2 : q * C * N = a * q := by rw [mul_assoc, hCN, hqa]
  have hB : LinearMap.det (1 + a * p) = LinearMap.det (1 + a * q) := by
    rw [hB1, hsy N (q * C), hB2]
  have hC : 1 + a * q = (1 + a * r) * (1 + a * s) := by rw [dpb_ring a r s hrs0 hra, hrs]
  have hs : s = ι * r * κ := by rw [hιr, mul_assoc, hι, mul_one]
  have hD1 : 1 + a * s = ι * (1 + a * r) * κ := by
    rw [hs, mul_add, add_mul, mul_one, hι, ← mul_assoc ι a r, hιa]
    simp only [mul_assoc]
  have hdet : LinearMap.det ι * LinearMap.det κ = 1 := by rw [← map_mul, hι, map_one]
  have hD : LinearMap.det (1 + a * s) = LinearMap.det (1 + a * r) := by
    rw [hD1, map_mul, map_mul]
    calc LinearMap.det ι * LinearMap.det (1 + a * r) * LinearMap.det κ
        = LinearMap.det (1 + a * r) * (LinearMap.det ι * LinearMap.det κ) := by ring
      _ = LinearMap.det (1 + a * r) := by rw [hdet, mul_one]
  have hE : LinearMap.det (1 + P ∘ₗ a ∘ₗ E : W →ₗ[ℝ] W) = LinearMap.det (1 + a * r) := by
    have h := dpb_sylv E (P ∘ₗ a)
    have h2 : E ∘ₗ (P ∘ₗ a) = a * r := by
      show (E ∘ₗ P) ∘ₗ a = a * r
      rw [hEP, ← hra]
      rfl
    rw [h2] at h
    exact h.symm
  rw [hA, map_mul, hB, hC, map_mul, hD, hE]
  ring

theorem dpb_abs (t θ α ι N C : Module.End ℝ V) (E : W →ₗ[ℝ] V) (P : V →ₗ[ℝ] W)
    (hθ : ∀ v, θ (θ v) = v) (hα : ∀ v, α (α v) = v) (hθα : ∀ v, θ (α v) = α (θ v))
    (htθ : ∀ v, θ (t v) = t (θ v)) (htα : ∀ v, α (t v) = t (α v))
    (hNC : ∀ v, N (C v) = t v - v) (hCN : ∀ v, C (N v) = t v - v) (hθN : ∀ v, θ (N v) = -N (θ v))
    (hι : ∀ v, ι (ι v) = -v) (hιt : ∀ v, ι (t v) = t (ι v)) (hιθ : ∀ v, θ (ι v) = ι (θ v))
    (hια : ∀ v, α (ι v) = -ι (α v))
    (hEP : ∀ v, E (P v) = (1 / 4 : ℝ) • (v + α v - θ v - α (θ v))) (hPE : ∀ w, P (E w) = w) :
    LinearMap.det t = LinearMap.det (P ∘ₗ t ∘ₗ E : W →ₗ[ℝ] W) ^ 4 := by
  have key := det_one_add_compression (t - 1) ((1 / 2 : ℝ) • (1 + θ)) ((1 / 2 : ℝ) • (1 - θ))
    ((1 / 4 : ℝ) • (1 + α - θ - α * θ)) ((1 / 4 : ℝ) • (1 - α - θ + α * θ)) ι (-ι) N C E P
    (by ext v; simp; module)
    (by ext v; simp [hθ]; try module)
    (by ext v; simp [htθ]; try module)
    (by ext v; simp [hNC]) (by ext v; simp [hCN])
    (by ext v; simp [hθN]; try module)
    (by ext v; simp; module)
    (by ext v; simp [hθ, hα, hθα]; try module)
    (by ext v; simp [htθ, htα]; try module)
    (by ext v; simp [hι])
    (by ext v; simp [hιt])
    (by ext v; simp [hιθ, hια]; try module)
    (by ext v; simp [hEP])
  have e1 : (1 : Module.End ℝ V) + (t - 1) = t := by abel
  have e2 : (1 + P ∘ₗ (t - 1) ∘ₗ E : W →ₗ[ℝ] W) = P ∘ₗ t ∘ₗ E := by
    ext w; simp [hPE]
  rwa [e1, e2] at key

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbB
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def dpbH (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) (W : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  U * Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) * Uᴴ

def dpbD (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => (x i : ℂ)

theorem dpbH_add (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) (W W' : Matrix (Fin n) (Fin n) ℂ) :
    dpbH U x h (W + W') = dpbH U x h W + dpbH U x h W' := by
  have key : Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * (W + W') * U) i j) =
      Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) +
        Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W' * U) i j) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, mul_add, add_mul]
  simp only [dpbH]
  rw [key, mul_add, add_mul]

theorem dpbH_smul (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) (c : ℂ)
    (W : Matrix (Fin n) (Fin n) ℂ) : dpbH U x h (c • W) = c • dpbH U x h W := by
  have key : Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * (c • W) * U) i j) =
      c • Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul]
    ring
  simp only [dpbH]
  rw [key, Matrix.mul_smul, Matrix.smul_mul]

def dpbL (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := dpbH U x h
  map_add' := dpbH_add U x h
  map_smul' c W := by
    have := dpbH_smul U x h (c : ℂ) W
    simpa only [Complex.coe_smul, RingHom.id_apply] using this

theorem dpbH_conjTranspose (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) (he : ∀ u, h (-u) = h u)
    (W : Matrix (Fin n) (Fin n) ℂ) : (dpbH U x h W)ᴴ = dpbH U x h Wᴴ := by
  have key : (Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j))ᴴ =
      Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * Wᴴ * U) i j) := by
    ext i j
    have h1 : (Uᴴ * Wᴴ * U) i j = star ((Uᴴ * W * U) j i) := by
      rw [← Matrix.conjTranspose_apply]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have h2 : h (x j - x i) = h (x i - x j) := by rw [← neg_sub, he]
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [h1, h2, star_mul']
    simp [Complex.conj_ofReal]
  rw [dpbH, dpbH, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, key]
  exact (Matrix.mul_assoc _ _ _).symm

theorem dpb_had_conj (Q M : Matrix (Fin n) (Fin n) ℂ) (F G : Fin n → Fin n → ℂ)
    (hFG : ∀ i j k l, Q i j ≠ 0 → Q l k ≠ 0 → F i l = G j k) :
    Matrix.of (fun i l => F i l * (Q * M * Qᴴ) i l) = Q * Matrix.of (fun j k => G j k * M j k) * Qᴴ := by
  ext i l
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h1 : Q i j = 0
  · simp [h1]
  by_cases h2 : Q l k = 0
  · simp [h2]
  rw [hFG i j k l h1 h2]
  ring

theorem dpbH_indep {U V : Matrix (Fin n) (Fin n) ℂ} {x x' : Fin n → ℝ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1) (hY : U * dpbD x * Uᴴ = V * dpbD x' * Vᴴ) (h : ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) : dpbH U x h W = dpbH V x' h W := by
  have hQ : dpbD x * (Uᴴ * V) = (Uᴴ * V) * dpbD x' := by
    calc dpbD x * (Uᴴ * V) = Uᴴ * (U * dpbD x * Uᴴ) * V := by
          simp only [Matrix.mul_assoc]
          rw [← mul_assoc Uᴴ U, hU, one_mul]
      _ = Uᴴ * (V * dpbD x' * Vᴴ) * V := by rw [hY]
      _ = (Uᴴ * V) * dpbD x' := by
          simp only [Matrix.mul_assoc]
          rw [hV, mul_one]
  have hx : ∀ i j, (Uᴴ * V) i j ≠ 0 → x i = x' j := by
    intro i j hne
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hQ
    simp only [dpbD, Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    have h2 : ((x i : ℂ) - x' j) * (Uᴴ * V) i j = 0 := by
      rw [sub_mul, h1]
      ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact_mod_cast sub_eq_zero.mp h3
    · exact absurd h3 hne
  have hQM : (Uᴴ * V) * (Vᴴ * W * V) * (Uᴴ * V)ᴴ = Uᴴ * W * U := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Uᴴ * V * (Vᴴ * W * V) * (Vᴴ * U) = Uᴴ * (V * Vᴴ) * W * (V * Vᴴ) * U := by
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * W * U := by rw [hV', mul_one, mul_one]
  have key := dpb_had_conj (Uᴴ * V) (Vᴴ * W * V) (fun i l => ((h (x i - x l) : ℝ) : ℂ))
    (fun j k => ((h (x' j - x' k) : ℝ) : ℂ)) (by
      intro i j k l h1 h2
      show ((h (x i - x l) : ℝ) : ℂ) = ((h (x' j - x' k) : ℝ) : ℂ)
      rw [hx i j h1, hx l k h2])
  try simp only at key
  rw [hQM] at key
  simp only [dpbH]
  rw [key, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [hU', mul_one, ← mul_assoc U Uᴴ, hU', one_mul]

theorem dpbH_theta {U J : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℝ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hJ : J * J = 1) (hJ' : Jᴴ = J) (hY : J * (U * dpbD x * Uᴴ) * J = -(U * dpbD x * Uᴴ)) (h : ℝ → ℝ)
    (he : ∀ u, h (-u) = h u) (W : Matrix (Fin n) (Fin n) ℂ) :
    J * dpbH U x h W * J = dpbH U x h (J * W * J) := by
  have hV : (J * U)ᴴ * (J * U) = 1 := by
    rw [Matrix.conjTranspose_mul, hJ']
    calc Uᴴ * J * (J * U) = Uᴴ * (J * J) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, mul_one, hU]
  have hV' : (J * U) * (J * U)ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul, hJ']
    calc J * U * (Uᴴ * J) = J * (U * Uᴴ) * J := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU', mul_one, hJ]
  have hD : dpbD (-x) = -dpbD x := by
    ext i j
    simp only [dpbD, Matrix.neg_apply, Matrix.diagonal_apply, Pi.neg_apply, Complex.ofReal_neg]
    split_ifs <;> simp
  have hY' : U * dpbD x * Uᴴ = (J * U) * dpbD (-x) * (J * U)ᴴ := by
    rw [hD, Matrix.conjTranspose_mul, hJ']
    calc U * dpbD x * Uᴴ = -(J * (U * dpbD x * Uᴴ) * J) := by rw [hY, neg_neg]
      _ = J * U * -dpbD x * (Uᴴ * J) := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hM : (J * U)ᴴ * (J * W * J) * (J * U) = Uᴴ * W * U := by
    rw [Matrix.conjTranspose_mul, hJ']
    calc Uᴴ * J * (J * W * J) * (J * U) = Uᴴ * (J * J) * W * (J * J) * U := by
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * W * U := by rw [hJ, mul_one, mul_one]
  have hA : Matrix.of (fun i j => ((h ((-x) i - (-x) j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) =
      Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) := by
    ext i j
    simp only [Matrix.of_apply, Pi.neg_apply]
    rw [neg_sub_neg, ← neg_sub, he]
  rw [dpbH_indep hU hU' hV hV' hY' h (J * W * J)]
  simp only [dpbH]
  rw [hM, hA, Matrix.conjTranspose_mul, hJ']
  simp only [Matrix.mul_assoc]

theorem dpb_comm_D (x : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (dpbD x * X - X * dpbD x) i j = ((x i - x j : ℝ) : ℂ) * X i j := by
  simp only [dpbD, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Complex.ofReal_sub]
  ring

theorem dpbH_sub_one {U : Matrix (Fin n) (Fin n) ℂ} (x : Fin n → ℝ) (hU' : U * Uᴴ = 1) (h : ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) : dpbH U x (fun u => h u - 1) W = dpbH U x h W - W := by
  have key : Matrix.of (fun i j => ((h (x i - x j) - 1 : ℝ) : ℂ) * (Uᴴ * W * U) i j) =
      Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) - Uᴴ * W * U := by
    ext i j
    simp only [Matrix.of_apply, Matrix.sub_apply, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  simp only [dpbH]
  rw [key, mul_sub, sub_mul]
  congr 1
  calc U * (Uᴴ * W * U) * Uᴴ = (U * Uᴴ) * W * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
    _ = W := by rw [hU', one_mul, mul_one]

private theorem unitary_conj_mul_unitary_conj_of_conjTranspose_mul_self {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1)
    (A B : Matrix (Fin n) (Fin n) ℂ) : U * A * Uᴴ * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
  calc U * A * Uᴴ * (U * B * Uᴴ) = U * A * (Uᴴ * U) * B * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = U * (A * B) * Uᴴ := by
        rw [hU, mul_one]
        simp only [Matrix.mul_assoc]

theorem dpbH_ad_left {U : Matrix (Fin n) (Fin n) ℂ} (x : Fin n → ℝ) (hU : Uᴴ * U = 1) (h : ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) :
    (U * dpbD x * Uᴴ) * dpbH U x h W - dpbH U x h W * (U * dpbD x * Uᴴ) = dpbH U x (fun u => u * h u) W := by
  simp only [dpbH]
  rw [unitary_conj_mul_unitary_conj_of_conjTranspose_mul_self hU, unitary_conj_mul_unitary_conj_of_conjTranspose_mul_self hU, ← sub_mul, ← mul_sub]
  congr 2
  ext i j
  rw [dpb_comm_D]
  simp only [Matrix.of_apply, Complex.ofReal_mul]
  ring

theorem dpbH_ad_right {U : Matrix (Fin n) (Fin n) ℂ} (x : Fin n → ℝ) (hU : Uᴴ * U = 1) (h : ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) :
    dpbH U x h ((U * dpbD x * Uᴴ) * W - W * (U * dpbD x * Uᴴ)) = dpbH U x (fun u => u * h u) W := by
  have e1 : Uᴴ * (U * dpbD x * Uᴴ * W) * U = dpbD x * (Uᴴ * W * U) := by
    calc Uᴴ * (U * dpbD x * Uᴴ * W) * U = (Uᴴ * U) * dpbD x * (Uᴴ * W * U) := by
          simp only [Matrix.mul_assoc]
      _ = dpbD x * (Uᴴ * W * U) := by rw [hU, one_mul]
  have e2 : Uᴴ * (W * (U * dpbD x * Uᴴ)) * U = (Uᴴ * W * U) * dpbD x * (Uᴴ * U) := by
    simp only [Matrix.mul_assoc]
  have key : Uᴴ * ((U * dpbD x * Uᴴ) * W - W * (U * dpbD x * Uᴴ)) * U =
      dpbD x * (Uᴴ * W * U) - (Uᴴ * W * U) * dpbD x := by
    rw [mul_sub, sub_mul, e1, e2, hU, mul_one]
  simp only [dpbH]
  rw [key]
  congr 2
  ext i j
  simp only [Matrix.of_apply]
  rw [dpb_comm_D, Complex.ofReal_mul]
  ring

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def dpbE (ε : Fin n → Bool) : (PCoord ε → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := pmat
  map_add' z w := by
    ext a b
    simp only [pmat, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c z := by
    ext a b
    simp only [pmat, Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def dpbP (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun W ab := (1 / 2 : ℝ) • (W ab.1.1 ab.1.2 + star (W ab.1.2 ab.1.1))
  map_add' W W' := by
    ext ab
    simp only [Matrix.add_apply, Pi.add_apply, star_add]
    module
  map_smul' c W := by
    ext ab
    simp only [Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply, star_smul, star_trivial]
    module

theorem dpbP_herm {ε : Fin n → Bool} {W : Matrix (Fin n) (Fin n) ℂ} (hW : Wᴴ = W) (ab : PCoord ε) :
    dpbP ε W ab = W ab.1.1 ab.1.2 := by
  have h : star (W ab.1.2 ab.1.1) = W ab.1.1 ab.1.2 := by
    have := congrFun (congrFun hW ab.1.1) ab.1.2
    simpa [Matrix.conjTranspose_apply] using this
  simp only [dpbP, LinearMap.coe_mk, AddHom.coe_mk]
  rw [h, Complex.real_smul]
  push_cast
  ring

theorem dpbP_E {ε : Fin n → Bool} (w : PCoord ε → ℂ) : dpbP ε (dpbE ε w) = w := by
  funext ab
  obtain ⟨⟨a, b⟩, hab, hne⟩ := ab
  have h1 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => absurd h.1 (not_lt.mpr hab.le)
  simp only [dpbP, dpbE, LinearMap.coe_mk, AddHom.coe_mk, pmat, dif_pos (And.intro hab hne), dif_neg h1,
    star_star]
  rw [Complex.real_smul]
  push_cast
  ring

theorem dpb_JWJ (ε : Fin n → Bool) (W : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Jm ε * W * Jm ε) a b = if ε a = ε b then W a b else -W a b := by
  simp only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal]
  cases ε a <;> cases ε b <;> simp

theorem dpbE_P {ε : Fin n → Bool} (W : Matrix (Fin n) (Fin n) ℂ) :
    dpbE ε (dpbP ε W) = (1 / 4 : ℝ) • (W + Wᴴ - Jm ε * W * Jm ε - (Jm ε * W * Jm ε)ᴴ) := by
  ext a b
  simp only [dpbE, dpbP, LinearMap.coe_mk, AddHom.coe_mk, pmat, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.conjTranspose_apply, dpb_JWJ]
  by_cases hε : ε a = ε b
  · have h1 : ¬ (b < a ∧ ε a ≠ ε b) := fun h => h.2 hε
    have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => h.2 hε.symm
    rw [dif_neg h1, dif_neg h2, if_pos hε, if_pos hε.symm]
    simp
  · rw [if_neg hε, if_neg (Ne.symm hε)]
    rcases lt_trichotomy a b with h | h | h
    · have h1 : ¬ (b < a ∧ ε a ≠ ε b) := fun h' => absurd h'.1 (not_lt.mpr h.le)
      rw [dif_neg h1, dif_pos (And.intro h (Ne.symm hε))]
      simp only [Complex.real_smul]
      push_cast
      simp only [star_add, star_mul', star_star, star_div₀, star_one, star_ofNat, star_neg]
      ring
    · exact absurd (h ▸ rfl) hε
    · rw [dif_pos (And.intro h hε)]
      simp only [star_neg, Complex.real_smul]
      push_cast
      ring

theorem dpb_JYJ {ε : Fin n → Bool} (y : PCoord ε → ℂ) : Jm ε * pmat y * Jm ε = -pmat y := by
  ext a b
  rw [dpb_JWJ]
  split_ifs with h
  · have : pmat y a b = 0 := by simp [pmat, h]
    rw [Matrix.neg_apply, this, neg_zero]
  · rw [Matrix.neg_apply]

theorem dpb_shc_neg (u : ℝ) : shc (-u) = shc u := by
  unfold shc
  by_cases h : u = 0
  · simp [h]
  · rw [if_neg (neg_ne_zero.mpr h), if_neg h, Real.sinh_neg, neg_div_neg_eq]

theorem dpb_shc_fac : (fun u : ℝ => u * ((shc u - 1) / u)) = fun u => shc u - 1 := by
  funext u
  unfold shc
  by_cases h : u = 0
  · simp [h]
  · rw [if_neg h]
    field_simp

theorem dpb_theta_ad {J Y : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (hY : J * Y * J = -Y)
    (W : Matrix (Fin n) (Fin n) ℂ) : J * (Y * W - W * Y) * J = -(Y * (J * W * J) - (J * W * J) * Y) := by
  have key : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (J * A * J) * (J * B * J) = J * (A * B) * J := by
    intro A B
    calc (J * A * J) * (J * B * J) = J * A * (J * J) * B * J := by simp only [Matrix.mul_assoc]
      _ = J * (A * B) * J := by rw [hJ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.sub_mul, ← key Y W, ← key W Y, hY]
  simp only [neg_mul, mul_neg]
  abel

theorem dpb_det {ε : Fin n → Bool} {U : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℝ} (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (hY : Jm ε * (U * dpbD x * Uᴴ) * Jm ε = -(U * dpbD x * Uᴴ)) :
    LinearMap.det (dpbL U x shc) = LinearMap.det (dpbP ε ∘ₗ dpbL U x shc ∘ₗ dpbE ε) ^ 4 := by
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJh : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    change star (if ε a then (1 : ℂ) else -1) = (if ε a then 1 else -1)
    split_ifs <;> simp
  have hJJv : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  let θ : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Jm ε * W * Jm ε
      map_add' := fun W W' => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c W => by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let α : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Wᴴ
      map_add' := fun W W' => Matrix.conjTranspose_add W W'
      map_smul' := fun c W => by simp [Matrix.conjTranspose_smul] }
  let ι : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => Complex.I • W
      map_add' := fun W W' => smul_add _ _ _
      map_smul' := fun c W => by simp only [RingHom.id_apply]; exact smul_comm _ _ _ }
  let N : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun W => (U * dpbD x * Uᴴ) * W - W * (U * dpbD x * Uᴴ)
      map_add' := fun W W' => by simp only [Matrix.mul_add, Matrix.add_mul]; abel
      map_smul' := fun c W => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_sub] }
  let C : Module.End ℝ (Matrix (Fin n) (Fin n) ℂ) := dpbL U x (fun u => (shc u - 1) / u)
  have hsub : dpbH U x (fun u => u * ((shc u - 1) / u)) = dpbH U x (fun u => shc u - 1) := by
    rw [dpb_shc_fac]
  refine dpb_abs (dpbL U x shc) θ α ι N C (dpbE ε) (dpbP ε) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro v
    show Jm ε * (Jm ε * v * Jm ε) * Jm ε = v
    simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one, hJJv]
  · intro v
    show (vᴴ)ᴴ = v
    exact Matrix.conjTranspose_conjTranspose v
  · intro v
    show Jm ε * vᴴ * Jm ε = (Jm ε * v * Jm ε)ᴴ
    simp only [Matrix.conjTranspose_mul, hJh, Matrix.mul_assoc]
  · intro v
    show Jm ε * dpbH U x shc v * Jm ε = dpbH U x shc (Jm ε * v * Jm ε)
    exact dpbH_theta hU hU' hJJ hJh hY shc dpb_shc_neg v
  · intro v
    show (dpbH U x shc v)ᴴ = dpbH U x shc vᴴ
    exact dpbH_conjTranspose U x shc dpb_shc_neg v
  · intro v
    show (U * dpbD x * Uᴴ) * dpbH U x (fun u => (shc u - 1) / u) v -
      dpbH U x (fun u => (shc u - 1) / u) v * (U * dpbD x * Uᴴ) = dpbH U x shc v - v
    rw [dpbH_ad_left x hU, hsub, dpbH_sub_one x hU']
  · intro v
    show dpbH U x (fun u => (shc u - 1) / u) ((U * dpbD x * Uᴴ) * v - v * (U * dpbD x * Uᴴ)) =
      dpbH U x shc v - v
    rw [dpbH_ad_right x hU, hsub, dpbH_sub_one x hU']
  · intro v
    show Jm ε * ((U * dpbD x * Uᴴ) * v - v * (U * dpbD x * Uᴴ)) * Jm ε =
      -((U * dpbD x * Uᴴ) * (Jm ε * v * Jm ε) - (Jm ε * v * Jm ε) * (U * dpbD x * Uᴴ))
    exact dpb_theta_ad hJJ hY v
  · intro v
    show Complex.I • (Complex.I • v) = -v
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  · intro v
    show Complex.I • dpbH U x shc v = dpbH U x shc (Complex.I • v)
    exact (dpbH_smul U x shc Complex.I v).symm
  · intro v
    show Jm ε * (Complex.I • v) * Jm ε = Complex.I • (Jm ε * v * Jm ε)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  · intro v
    show (Complex.I • v)ᴴ = -(Complex.I • vᴴ)
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, neg_smul]
  · intro v
    exact dpbE_P v
  · intro w
    exact dpbP_E w

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def shcAdC {ε : Fin n → Bool} (y : PCoord ε → ℂ) (w : PCoord ε → ℂ) : PCoord ε → ℂ :=
  fun ab => shcAd y (pmat w) ab.1.1 ab.1.2

theorem detPb {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAd y) 0 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) =
      (LinearMap.det ((fderiv ℝ (shcAdC y) 0 : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
        (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))) ^ 4 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
    with hUdef
  have hU : Uᴴ * U = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.1
  have hU' : U * Uᴴ = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.2
  have hY : U * dpbD (pev y) * Uᴴ = pmat y := (pmat_isHermitian y).spectral_theorem.symm
  have e1 : shcAd y = LinearMap.toContinuousLinearMap (dpbL U (pev y) shc) := rfl
  have e2 : shcAdC y = LinearMap.toContinuousLinearMap (dpbP ε ∘ₗ dpbL U (pev y) shc ∘ₗ dpbE ε) := by
    funext w ab
    refine (dpbP_herm (W := dpbH U (pev y) shc (pmat w)) ?_ ab).symm
    rw [dpbH_conjTranspose U _ shc dpb_shc_neg, (pmat_isHermitian w).eq]
  rw [e1, e2, ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact dpb_det hU hU' (by rw [hY]; exact dpb_JYJ y)

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPaHadApply
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def detPaCj (P Q : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun W := P * W * Q
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp

def detPaRow (t : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi (fun j => (t j • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).comp (LinearMap.proj j))

def detPaHad (s : Fin n → Fin n → ℂ) : (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
  LinearMap.pi (fun i => (detPaRow (s i)).comp (LinearMap.proj i))

theorem detPaRow_det (t : Fin n → ℂ) : LinearMap.det (detPaRow t) = ∏ j, t j := by
  unfold detPaRow
  rw [LinearMap.det_pi]
  simp

theorem detPaHad_det (s : Fin n → Fin n → ℂ) : LinearMap.det (detPaHad s) = ∏ i, ∏ j, s i j := by
  unfold detPaHad
  rw [LinearMap.det_pi]
  simp [detPaRow_det]

theorem detPa {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAd y) 0 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) =
      ∏ i, ∏ j, shc (pev y i - pev y j) ^ 2 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hmem : U ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := ((pmat_isHermitian y).eigenvectorUnitary).2
  have hU2 : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hmem
  set s : Fin n → Fin n → ℂ := fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) with hs
  let H : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ := detPaHad s
  let T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    (detPaCj U Uᴴ).comp (H.comp (detPaCj Uᴴ U))
  have hT : ∀ W, T W = shcAd y W := by
    intro W
    simp only [T, H, LinearMap.comp_apply, detPaCj, LinearMap.coe_mk, AddHom.coe_mk, shcAd]
    congr 2
  have hC : shcAd y = ⇑(LinearMap.toContinuousLinearMap (T.restrictScalars ℝ)) := by
    funext W; exact (hT W).symm
  rw [hC, ContinuousLinearMap.fderiv, LinearMap.coe_toContinuousLinearMap, LinearMap.det_restrictScalars]
  have hAB : LinearMap.det (detPaCj U Uᴴ) * LinearMap.det (detPaCj Uᴴ U) = 1 := by
    rw [← LinearMap.det_comp]
    have : (detPaCj U Uᴴ).comp (detPaCj Uᴴ U) = LinearMap.id := by
      ext W : 1
      simp only [LinearMap.comp_apply, detPaCj, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU2, Matrix.one_mul, Matrix.mul_assoc, hU2, Matrix.mul_one]
    rw [this, LinearMap.det_id]
  have hdet : LinearMap.det T = ∏ i, ∏ j, s i j := by
    simp only [T]
    rw [LinearMap.det_comp, LinearMap.det_comp]
    have hH : LinearMap.det H = ∏ i, ∏ j, s i j := detPaHad_det s
    rw [hH, mul_left_comm, hAB, mul_one]
  rw [hdet, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Algebra.norm_complex_apply, hs, Complex.normSq_ofReal, sq]

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PolarJacobianDeterminant

theorem prod_shc_sq_eq_Jac_pow {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    ∏ i, ∏ j, shc (pev z i - pev z j) ^ 2 = Jac z ^ 4 := by
  set f : Fin n → Fin n → ℝ := fun i j => shc (pev z i - pev z j) with hf
  have hsym : ∀ i j, f i j = f j i := by
    intro i j; simp only [hf]; rw [← neg_sub, PolarJacobianDeterminant.shc_neg]
  have hpt : ∀ i j, f i j = (if i < j then f i j else 1) * (if j < i then f i j else 1) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst h; simp [hf, shc]
    · simp [h, not_lt_of_gt h]
  have hswap : ∏ i, ∏ j, (if j < i then f i j else 1) = ∏ i, ∏ j, (if i < j then f i j else 1) := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    rw [hsym]
  have hJ : Jac z = ∏ i, ∏ j, (if i < j then f i j else 1) := by
    simp only [Jac, Finset.prod_filter, hf]
  have hall : ∏ i, ∏ j, f i j = Jac z ^ 2 := by
    calc ∏ i, ∏ j, f i j
          = ∏ i, ∏ j, ((if i < j then f i j else 1) * (if j < i then f i j else 1)) :=
          Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => hpt i j
      _ = (∏ i, ∏ j, (if i < j then f i j else 1)) * ∏ i, ∏ j, (if j < i then f i j else 1) := by
          simp only [Finset.prod_mul_distrib]
      _ = Jac z ^ 2 := by rw [hswap, ← hJ, sq]
  have : ∏ i, ∏ j, shc (pev z i - pev z j) ^ 2 = (∏ i, ∏ j, f i j) ^ 2 := by
    simp only [hf, Finset.prod_pow]
  rw [this, hall, ← pow_mul]

theorem fderiv_shcAdC {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    fderiv ℝ (shcAdC y) 0 = LinearMap.toContinuousLinearMap (PolarJacobianDeterminant.shcAdCL y) := by
  have : shcAdC y = ⇑(LinearMap.toContinuousLinearMap (PolarJacobianDeterminant.shcAdCL y)) := by
    funext w; rfl
  rw [this]
  exact ContinuousLinearMap.fderiv _

end PolarJacobianDeterminant

theorem detP {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAdC y) 0 : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
      (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ)) = Jac y := by
  have h4 := (detPb y).symm.trans ((detPa y).trans (PolarJacobianDeterminant.prod_shc_sq_eq_Jac_pow y))
  have hpos : 0 < LinearMap.det ((fderiv ℝ (shcAdC y) 0 : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
      (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ)) := by
    rw [PolarJacobianDeterminant.fderiv_shcAdC, LinearMap.coe_toContinuousLinearMap]
    exact PolarJacobianDeterminant.det_shcAdCL_pos y
  have hJ : 0 ≤ Jac y := Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b _ =>
    (PolarJacobianDeterminant.shc_pos _).le
  exact (pow_left_inj₀ hpos.le hJ (by norm_num)).mp h4

end ReciprocityTheory.ChartRestriction.DS
