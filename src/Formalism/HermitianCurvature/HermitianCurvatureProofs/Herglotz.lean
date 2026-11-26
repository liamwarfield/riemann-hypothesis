module

public import Mathlib

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.Herglotz
namespace Formalism.FourierDecayAlt.P.Herglotz

open Real Filter Topology Finset

variable {d : ℕ}

noncomputable def ee (x : Fin d → ℝ) (σ : Fin d → ℤ) : ℂ :=
  Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ))

lemma ee_eq (x : Fin d → ℝ) (σ : Fin d → ℤ) :
    ee x σ = Complex.exp (((2 * π * ∑ j, (σ j : ℝ) * x j : ℝ) : ℂ) * Complex.I) := by
  unfold ee
  congr 1
  push_cast
  ring

lemma norm_ee (x : Fin d → ℝ) (σ : Fin d → ℤ) : ‖ee x σ‖ = 1 := by
  rw [ee_eq]
  exact Complex.norm_exp_ofReal_mul_I _

lemma ee_mul_conj (x : Fin d → ℝ) (σ σ' : Fin d → ℤ) :
    ee x σ * starRingEnd ℂ (ee x σ') = ee x (σ - σ') := by
  rw [ee_eq, ee_eq, ee_eq, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.sub_apply, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib]
  push_cast
  ring

end Formalism.FourierDecayAlt.P.Herglotz

namespace Formalism.FourierDecayAlt.P

open Real Filter Topology Finset Formalism.FourierDecayAlt.P.Herglotz

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSumLeOfForm
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Finset
open scoped ComplexConjugate InnerProductSpace

noncomputable section

section hilbert

variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_sum_smul (k : ι → ι → ℂ) (v : ι → H) (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ) (J : Finset κ)
    (a : κ → ℂ) (P : κ → ι) :
    ⟪∑ j ∈ J, a j • v (P j), ∑ l ∈ J, a l • v (P l)⟫_ℂ =
      ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * k (P j) (P l) := by
  rw [sum_inner]
  refine sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_sum, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [inner_smul_right, hv]
  ring

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem form_sum_conj (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (J : Finset κ) (a : κ → ℂ) (y : κ → V) :
    B (∑ j ∈ J, conj (a j) • y j) (∑ l ∈ J, conj (a l) • y l) =
      ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * B (y j) (y l) := by
  rw [LinearMap.map_sum₂]
  refine sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, LinearMap.smul_apply, map_sum, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [map_smulₛₗ, smul_eq_mul, Complex.conj_conj]
  ring

theorem norm_sq_sum_eq_form (k : ι → ι → ℂ) (v : ι → H) (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ)
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (J : Finset κ) (a : κ → ℂ) (P : κ → ι) (y : κ → V)
    (hy : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = B (y j) (y l)) :
    ‖∑ j ∈ J, a j • v (P j)‖ ^ 2 = (B (∑ j ∈ J, conj (a j) • y j) (∑ j ∈ J, conj (a j) • y j)).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_sum_smul k v hv, form_sum_conj, RCLike.re_to_complex]
  congr 1
  refine sum_congr rfl fun j hj => sum_congr rfl fun l hl => ?_
  rw [hy j hj l hl]

theorem norm_sum_le_of_form {W : Type*} [SeminormedAddCommGroup W] [Module ℂ W] (k : ι → ι → ℂ) (v : ι → H)
    (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ) (B : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (Cp : ℝ) (hCp : 0 ≤ Cp)
    (hB : ∀ x, (B x x).re ≤ (Cp * ‖x‖) ^ 2) (J : Finset κ) (a : κ → ℂ) (P : κ → ι) (y : κ → W)
    (hy : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = B (y j) (y l)) :
    ‖∑ j ∈ J, a j • v (P j)‖ ≤ Cp * ‖∑ j ∈ J, conj (a j) • y j‖ := by
  have h := norm_sq_sum_eq_form k v hv B J a P y hy
  have h2 := hB (∑ j ∈ J, conj (a j) • y j)
  rw [← h] at h2
  exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2 |> fun h3 => by
    simpa [abs_of_nonneg (norm_nonneg _)] using (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

end hilbert

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSumLeOfGram
namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Finset
open scoped ComplexConjugate InnerProductSpace

theorem norm_sq_comb {κ : Type} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (J : Finset κ) (b : κ → ℂ)
    (y : κ → W) :
    ((‖∑ j ∈ J, b j • y j‖ ^ 2 : ℝ) : ℂ) = ∑ j ∈ J, ∑ l ∈ J, conj (b j) * b l * ⟪y j, y l⟫_ℂ := by
  rw [show ((‖∑ j ∈ J, b j • y j‖ ^ 2 : ℝ) : ℂ) = ⟪∑ j ∈ J, b j • y j, ∑ j ∈ J, b j • y j⟫_ℂ by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast, sum_inner]
  refine sum_congr rfl fun j _ => ?_
  rw [inner_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

theorem sum_sq_le_sq_sum {I : Type} [Fintype I] (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, x i ^ 2 ≤ (∑ i, x i) ^ 2 := by
  rw [sq, sum_mul]
  refine sum_le_sum fun i _ => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (single_le_sum (fun j _ => hx j) (mem_univ i)) (hx i)

theorem norm_sum_le_of_gram {ι κ I : Type} [Fintype I] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (k : ι → ι → ℂ) (v : ι → H)
    (hv : ∀ P Q, k P Q = ⟪v P, v Q⟫_ℂ) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (Y : I → ι → W) (J : Finset κ) (P : κ → ι)
    (hk : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = ∑ i, (c i : ℂ) * ⟪Y i (P l), Y i (P j)⟫_ℂ) (a : κ → ℂ) :
    ‖∑ j ∈ J, a j • v (P j)‖ ≤ ∑ i, √(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ := by
  have h1 : ((‖∑ j ∈ J, a j • v (P j)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ((c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_sq_comb]
    calc ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * ⟪v (P j), v (P l)⟫_ℂ
        = ∑ j ∈ J, ∑ l ∈ J, ∑ i, (c i : ℂ) * (conj (a j) * a l * ⟪Y i (P l), Y i (P j)⟫_ℂ) := by
          refine sum_congr rfl fun j hj => sum_congr rfl fun l hl => ?_
          rw [← hv, hk j hj l hl, mul_sum]
          refine sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ j ∈ J, ∑ l ∈ J, (c i : ℂ) * (conj (a j) * a l * ⟪Y i (P l), Y i (P j)⟫_ℂ) := by
          exact (sum_congr rfl fun j _ => sum_comm).trans sum_comm
      _ = ∑ i, ((c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 : ℝ) : ℂ) := by
          refine sum_congr rfl fun i _ => ?_
          rw [Complex.ofReal_mul, norm_sq_comb, mul_sum, sum_comm]
          refine sum_congr rfl fun l _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun j _ => ?_
          rw [Complex.conj_conj]
          ring
  have h2 : ‖∑ j ∈ J, a j • v (P j)‖ ^ 2 = ∑ i, c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 := by
    exact_mod_cast h1
  have h3 : ‖∑ j ∈ J, a j • v (P j)‖ ^ 2 ≤ (∑ i, √(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖) ^ 2 := by
    rw [h2]
    have : ∑ i, c i * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ ^ 2 =
        ∑ i, (√(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖) ^ 2 := by
      refine sum_congr rfl fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (hc i)]
    rw [this]
    exact sum_sq_le_sq_sum _ fun i => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hb : 0 ≤ ∑ i, √(c i) * ‖∑ j ∈ J, conj (a j) • Y i (P j)‖ :=
    sum_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (∑ j ∈ J, a j • v (P j))]

end Formalism.FourierDecayAlt.P.GermRateSplit
end
