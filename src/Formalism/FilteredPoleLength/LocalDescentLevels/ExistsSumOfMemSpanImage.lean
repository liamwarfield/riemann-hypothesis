module

public import Formalism.FilteredPoleLength.ReducedBasisBounds.TransvectionIsometry

@[expose] public section

section -- merged from Formalism.FilteredPoleLength.LocalDescentLevels.ExistsSumOfMemSpanImage
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Finset

section aux

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem exists_orth_decomp_of_finiteDimensional (K : Submodule ℝ V) [FiniteDimensional ℝ K]
    (a : V) : ∃ w ∈ K, ∃ z : V, (∀ p ∈ K, inner ℝ p z = 0) ∧ a = w + z := by
  have : CompleteSpace K := FiniteDimensional.complete ℝ K
  obtain ⟨w, hw, z, hz, h⟩ : ∃ w ∈ K, ∃ z ∈ K.orthogonal, a = w + z := by
    exact K.exists_add_mem_mem_orthogonal a
  refine ⟨w, hw, z, fun p hp => ?_, h⟩
  exact Submodule.inner_right_of_mem_orthogonal hp hz

theorem exists_orth_split {ι : Type*} (v : ι → V) (T : Finset ι) (a : V) :
    ∃ w ∈ Submodule.span ℝ (v '' (T : Set ι)), ∃ z : V,
      (∀ p ∈ Submodule.span ℝ (v '' (T : Set ι)), inner ℝ p z = 0) ∧ a = w + z ∧
        ‖z‖ ^ 2 ≤ ‖a‖ ^ 2 := by
  have : FiniteDimensional ℝ (Submodule.span ℝ (v '' (T : Set ι))) :=
    FiniteDimensional.span_of_finite ℝ (T.finite_toSet.image v)
  obtain ⟨w, hw, z, hz, hwz⟩ :=
    exists_orth_decomp_of_finiteDimensional (Submodule.span ℝ (v '' (T : Set ι))) a
  refine ⟨w, hw, z, hz, hwz, ?_⟩
  rw [hwz, norm_add_sq_real, hz w hw]
  nlinarith [sq_nonneg ‖w‖]

private theorem exists_sum_repr_of_mem_span_image {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (v : ι → M) (T : Finset ι) (x : M) (hx : x ∈ Submodule.span R (v '' (T : Set ι))) :
    ∃ r : ι → R, x = ∑ i ∈ T, r i • v i := by
  classical
  let S : Submodule R M :=
    { carrier := {y | ∃ r : ι → R, y = ∑ i ∈ T, r i • v i}
      add_mem' := by
        rintro y₁ y₂ ⟨r₁, rfl⟩ ⟨r₂, rfl⟩
        exact ⟨r₁ + r₂, by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c y ⟨r, rfl⟩
        exact ⟨c • r, by simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]⟩ }
  have hle : Submodule.span R (v '' (T : Set ι)) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    show ∃ r : ι → R, v j = ∑ i ∈ T, r i • v i
    refine ⟨fun i => if i = j then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · intro hjT
      exact absurd (Finset.mem_coe.mp hj) hjT
  exact hle hx

theorem nearestPlane_finset {ι : Type*} [DecidableEq ι] (v : ι → V) (T : Finset ι) :
    ∀ x ∈ Submodule.span ℝ (v '' (T : Set ι)),
      ∃ c : ι → ℤ, ‖x - ∑ i ∈ T, (c i : ℝ) • v i‖ ^ 2 ≤ (1 / 4) * ∑ i ∈ T, ‖v i‖ ^ 2 := by
  refine Finset.induction_on T ?_ ?_
  · intro x hx
    refine ⟨0, ?_⟩
    simp at hx
    subst hx
    simp
  · intro a s ha ih x hx
    obtain ⟨r, hr⟩ := exists_sum_repr_of_mem_span_image v (insert a s) x hx
    rw [Finset.sum_insert ha] at hr
    obtain ⟨w, hw, z, hz, hwz, hzle⟩ := exists_orth_split v s (v a)
    have hyK : (∑ i ∈ s, r i • v i) ∈ Submodule.span ℝ (v '' (s : Set ι)) :=
      Submodule.sum_mem _ (fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩))
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = round (r a) := ⟨_, rfl⟩
    have hy'K : (∑ i ∈ s, r i • v i) + (r a - k) • w ∈ Submodule.span ℝ (v '' (s : Set ι)) :=
      Submodule.add_mem _ hyK (Submodule.smul_mem _ _ hw)
    obtain ⟨c', hc'⟩ := ih _ hy'K
    have hSK : (∑ i ∈ s, (c' i : ℝ) • v i) ∈ Submodule.span ℝ (v '' (s : Set ι)) :=
      Submodule.sum_mem _ (fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩))
    have heK := Submodule.sub_mem _ hy'K hSK
    refine ⟨fun i => if i = a then k else c' i, ?_⟩
    have hsum : ∑ i ∈ s, (((if i = a then k else c' i : ℤ)) : ℝ) • v i
        = ∑ i ∈ s, (c' i : ℝ) • v i := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hia : i ≠ a := fun h => ha (by rw [← h]; exact hi)
      rw [if_neg hia]
    show ‖x - ∑ i ∈ insert a s, (((if i = a then k else c' i : ℤ)) : ℝ) • v i‖ ^ 2
      ≤ (1 / 4) * ∑ i ∈ insert a s, ‖v i‖ ^ 2
    rw [Finset.sum_insert ha, Finset.sum_insert ha, if_pos rfl, hsum]
    have hdecomp : x - ((k : ℝ) • v a + ∑ i ∈ s, (c' i : ℝ) • v i) =
        (r a - k) • z + ((∑ i ∈ s, r i • v i) + (r a - k) • w - ∑ i ∈ s, (c' i : ℝ) • v i) := by
      rw [hr, hwz]
      module
    have horth : inner ℝ ((r a - k) • z)
        ((∑ i ∈ s, r i • v i) + (r a - k) • w - ∑ i ∈ s, (c' i : ℝ) • v i) = 0 := by
      rw [real_inner_smul_left, real_inner_comm, hz _ heK, mul_zero]
    have hround : (r a - k) ^ 2 ≤ 1 / 4 := by
      have h1 : |r a - k| ≤ 1 / 2 := by
        rw [hk]
        exact abs_sub_round (r a)
      nlinarith [sq_abs (r a - k), abs_nonneg (r a - k),
        mul_le_mul_of_nonneg_left h1 (abs_nonneg (r a - k))]
    rw [hdecomp, norm_add_sq_real, horth, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h2 := mul_le_mul_of_nonneg_right hround (sq_nonneg ‖z‖)
    have h3 := mul_le_mul_of_nonneg_left hzle (by norm_num : (0 : ℝ) ≤ 1 / 4)
    linarith

end aux

theorem nearestPlane : NearestPlane := by
  unfold NearestPlane
  intro V _ _ n v _ x hx
  have hx' : x ∈ Submodule.span ℝ (v '' ((Finset.univ : Finset (Fin n)) : Set (Fin n))) := by
    rwa [Finset.coe_univ, Set.image_univ]
  exact nearestPlane_finset v Finset.univ x hx'

end Formalism.LatticeBaseChangeAlt
end
end

section -- merged from Formalism.FilteredPoleLength.LocalDescentLevels.IntegralMulExpNegSq
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Finset MeasureTheory Filter Topology Set

private theorem pow_le_pow_left_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    x ^ n ≤ y ^ n := by
  exact pow_le_pow_left₀ hx hxy n

theorem ballVolume : BallVolume := by
  intro D rr hr
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    show volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) rr) = _
    have hb : Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) rr = Set.univ := by
      ext z
      simp only [mem_ball_zero_iff, Set.mem_univ, iff_true]
      have hz : ‖z‖ = 0 := by
        rw [EuclideanSpace.norm_eq]
        simp
      rw [hz]
      exact hr
    have hpar : parallelepiped (EuclideanSpace.basisFun (Fin 0) ℝ) = Set.univ := by
      ext z
      simp only [Set.mem_univ, iff_true]
      have hz : z = 0 := by
        rw [← norm_eq_zero, EuclideanSpace.norm_eq]
        simp
      rw [hz, mem_parallelepiped_iff]
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
    rw [hb, ← hpar, OrthonormalBasis.volume_parallelepiped]
    simp
  have : Nonempty (Fin (2 * D)) := ⟨⟨0, by omega⟩⟩
  rw [EuclideanSpace.volume_ball, Fintype.card_fin]
  have hg : Real.Gamma (((2 * D : ℕ) : ℝ) / 2 + 1) = (D.factorial : ℝ) := by
    rw [show ((2 * D : ℕ) : ℝ) / 2 + 1 = (D : ℝ) + 1 by push_cast; ring]
    exact Real.Gamma_nat_eq_factorial D
  have hs : Real.sqrt Real.pi ^ (2 * D) = Real.pi ^ D := by
    rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
  rw [hg, hs, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

private theorem exp_neg_sq_div_sixteen_antitone {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Real.exp (-t ^ 2 / 16) ≤ Real.exp (-s ^ 2 / 16) :=
  Real.exp_le_exp.mpr (by nlinarith)

private theorem gaussian_tail_pow_mul_exp_le {g : ℕ} {R0 s t : ℝ} (hR0 : 0 < R0)
    (hg : 16 * (2 * (g : ℝ) + 1) ≤ R0 ^ 2) (hs : R0 ≤ s) (hst : s ≤ t) :
    (2 * (3 * t / R0) ^ (2 * g) - (3 * s / R0) ^ (2 * g)) * Real.exp (-t ^ 2 / 16) ≤
      (3 * s / R0) ^ (2 * g) * Real.exp (-s ^ 2 / 16) := by
  have hs0 : 0 < s := lt_of_lt_of_le hR0 hs
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (t ^ 2 - s ^ 2) / 16 := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; nlinarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (u / 2) := ⟨_, rfl⟩
  have hE2 : E ^ 2 = Real.exp u := by
    rw [show E ^ 2 = E * E by ring, hE, ← Real.exp_add]
    congr 1
    ring
  have hfs : Real.exp (-s ^ 2 / 16) = Real.exp (-t ^ 2 / 16) * E ^ 2 := by
    rw [hE2, ← Real.exp_add]
    congr 1
    rw [hu]
    ring
  have hK : 0 < 2 * (g : ℝ) + 1 := by positivity
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = u / (2 * (g : ℝ) + 1) := ⟨_, rfl⟩
  have hv0 : 0 ≤ v := by rw [hv]; exact div_nonneg hu0 hK.le
  have hvK : v * (2 * (g : ℝ) + 1) = u := by rw [hv]; field_simp
  have hR2 : R0 ^ 2 ≤ s ^ 2 := by nlinarith
  have ht2 : t ^ 2 ≤ s ^ 2 * (1 + v) := by
    have h16 : 16 * (2 * (g : ℝ) + 1) ≤ s ^ 2 := le_trans hg hR2
    have htu : t ^ 2 = s ^ 2 + 16 * u := by rw [hu]; ring
    nlinarith [mul_le_mul_of_nonneg_left h16 hv0]
  have hP : ∀ x : ℝ, (3 * x / R0) ^ (2 * g) = ((3 / R0) ^ 2 * x ^ 2) ^ g := by
    intro x
    rw [pow_mul]
    congr 1
    ring
  have hBt : (3 * t / R0) ^ (2 * g) ≤ (3 * s / R0) ^ (2 * g) * E := by
    rw [hP t, hP s]
    have h1 : (3 / R0) ^ 2 * t ^ 2 ≤ ((3 / R0) ^ 2 * s ^ 2) * (1 + v) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ht2 (sq_nonneg _)
    have h2 : ((3 / R0) ^ 2 * t ^ 2) ^ g ≤ (((3 / R0) ^ 2 * s ^ 2) * (1 + v)) ^ g :=
      pow_le_pow_left_of_nonneg (by positivity) h1 g
    have h3 : (1 + v) ^ g ≤ E := by
      have hexp : (1 + v) ^ g ≤ (Real.exp v) ^ g :=
        pow_le_pow_left_of_nonneg (by linarith) (by linarith [Real.add_one_le_exp v]) g
      have hnat : (Real.exp v) ^ g = Real.exp (g * v) := by
        exact (Real.exp_nat_mul v g).symm
      have hle : Real.exp (g * v) ≤ E := by
        rw [hE]
        apply Real.exp_le_exp.mpr
        nlinarith
      linarith
    calc ((3 / R0) ^ 2 * t ^ 2) ^ g ≤ (((3 / R0) ^ 2 * s ^ 2) * (1 + v)) ^ g := h2
      _ = ((3 / R0) ^ 2 * s ^ 2) ^ g * (1 + v) ^ g := mul_pow _ _ _
      _ ≤ ((3 / R0) ^ 2 * s ^ 2) ^ g * E := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hft : 0 ≤ Real.exp (-t ^ 2 / 16) := (Real.exp_pos _).le
  have hBs : 0 ≤ (3 * s / R0) ^ (2 * g) := by rw [hP s]; positivity
  rw [hfs]
  nlinarith [mul_le_mul_of_nonneg_right hBt hft, mul_nonneg (mul_nonneg hBs hft) (sq_nonneg (E - 1))]

theorem gaussian_tail_bound : GaussianTailBound := by
  intro ι h g R0 hR0 hg hlow hcount
  classical
  have claim : ∀ S : Finset ι, ∀ M : ℝ, R0 ≤ M → (∀ i ∈ S, h i ≤ M) →
      ∑ i ∈ S, Real.exp (-(h i) ^ 2 / 16) ≤
        2 * (3 * R0 / R0) ^ (2 * g) * Real.exp (-R0 ^ 2 / 16)
          - 2 * (3 * M / R0) ^ (2 * g) * Real.exp (-M ^ 2 / 16)
          + (S.card : ℝ) * Real.exp (-M ^ 2 / 16) := by
    intro S
    refine Finset.induction_on_max_value h S ?_ ?_
    · intro M hM _
      have k := gaussian_tail_pow_mul_exp_le hR0 hg le_rfl hM
      have hfa : Real.exp (-M ^ 2 / 16) ≤ Real.exp (-R0 ^ 2 / 16) :=
        exp_neg_sq_div_sixteen_antitone hR0.le hM
      have hB0 : 0 ≤ (3 * R0 / R0) ^ (2 * g) :=
        pow_nonneg (div_nonneg (by linarith) hR0.le) _
      simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_mul, add_zero]
      nlinarith [mul_le_mul_of_nonneg_left hfa hB0]
    · intro a S haS hmax ih M hM hSM
      have hxR : R0 ≤ h a := hlow a
      have hxM : h a ≤ M := hSM a (Finset.mem_insert_self a S)
      have ih' := ih (h a) hxR hmax
      have hins : ∀ i ∈ insert a S, h i ≤ h a := by
        intro i hi
        rcases Finset.mem_insert.mp hi with hia | hi'
        · rw [hia]
        · exact hmax i hi'
      have hcard := hcount (h a) hxR (insert a S) hins
      have hc : (insert a S).card = S.card + 1 := by
        exact Finset.card_insert_of_notMem haS
      rw [hc] at hcard
      rw [Finset.sum_insert haS, hc]
      push_cast at hcard ⊢
      have k := gaussian_tail_pow_mul_exp_le hR0 hg hxR hxM
      have hfa : Real.exp (-M ^ 2 / 16) ≤ Real.exp (-(h a) ^ 2 / 16) :=
        exp_neg_sq_div_sixteen_antitone (hR0.le.trans hxR) hxM
      nlinarith [mul_le_mul_of_nonneg_right hcard (sub_nonneg.mpr hfa)]
  have hG0 : (3 * R0 / R0) ^ (2 * g) = (9 : ℝ) ^ g := by
    rw [show 3 * R0 / R0 = (3 : ℝ) by field_simp, pow_mul]
    norm_num
  have hpos : ∀ i, 0 ≤ h i := fun i => hR0.le.trans (hlow i)
  have hsum : ∀ S : Finset ι, ∑ i ∈ S, Real.exp (-(h i) ^ 2 / 16) ≤
      2 * 9 ^ g * Real.exp (-R0 ^ 2 / 16) := by
    intro S
    have hM0 : R0 ≤ R0 + ∑ j ∈ S, h j :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hpos j)
    have hMi : ∀ i ∈ S, h i ≤ R0 + ∑ j ∈ S, h j := fun i hi =>
      (Finset.single_le_sum (fun j _ => hpos j) hi).trans (le_add_of_nonneg_left hR0.le)
    have c1 := claim S _ hM0 hMi
    have c2 := hcount _ hM0 S hMi
    have hBM : 0 ≤ (3 * (R0 + ∑ j ∈ S, h j) / R0) ^ (2 * g) :=
      pow_nonneg (div_nonneg (by linarith) hR0.le) _
    have hfM := (Real.exp_pos (-(R0 + ∑ j ∈ S, h j) ^ 2 / 16)).le
    rw [hG0] at c1
    nlinarith [mul_le_mul_of_nonneg_right c2 hfM, mul_nonneg hBM hfM]
  have hnn : ∀ i, 0 ≤ Real.exp (-(h i) ^ 2 / 16) := fun i => (Real.exp_pos _).le
  have hsm : Summable (fun i => Real.exp (-(h i) ^ 2 / 16)) := summable_of_sum_le hnn hsum
  refine ⟨hsm, ?_⟩
  exact Real.tsum_le_of_sum_le hnn hsum

end Formalism.LatticeBaseChangeAlt
end
end
