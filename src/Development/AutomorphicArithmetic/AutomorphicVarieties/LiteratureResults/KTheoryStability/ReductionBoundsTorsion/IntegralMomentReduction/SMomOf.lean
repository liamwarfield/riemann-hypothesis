module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.SetLIntegralPreimageMulLeft
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.DiscreteSpecialLinearGroupRingOfIntegers
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.PhMemUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.AbsLeA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.ConeStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.PrimalPlace

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.LocalDecomp
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.DdMemUnitary
noncomputable section

open Matrix

namespace PositivityTheory.KB.MomentRationality.Cz.Red

def dd {R : Type*} [CommRing R] (N : ℕ) (u : R) : Matrix (Fin N) (Fin N) R :=
  diagonal fun i => if (i : ℕ) = 0 then u else 1

theorem dd_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) (u : R) :
    (dd N u).map f = dd N (f u) := by
  unfold dd
  rw [diagonal_map (map_zero f)]
  congr 1
  funext i
  split_ifs <;> simp

theorem dd_mul {R : Type*} [CommRing R] (N : ℕ) (u v : R) : dd N u * dd N v = dd N (u * v) := by
  unfold dd
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem dd_one {R : Type*} [CommRing R] (N : ℕ) : dd N (1 : R) = 1 := by
  unfold dd
  simp

theorem det_dd {R : Type*} [CommRing R] {N : ℕ} (hN : 1 ≤ N) (u : R) : (dd N u).det = u := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  unfold dd
  rw [det_diagonal, Fin.prod_univ_succ]
  simp [Fin.val_succ]

def ddGL {R : Type*} [CommRing R] (N : ℕ) (u : Rˣ) : GL (Fin N) R :=
  ⟨dd N (u : R), dd N ((u⁻¹ : Rˣ) : R), by rw [dd_mul, Units.mul_inv, dd_one],
    by rw [dd_mul, Units.inv_mul, dd_one]⟩

theorem exists_root {N : ℕ} (hN : N ≠ 0) {d : ℂ} (hd : d ≠ 0) : ∃ z : ℂ, z ≠ 0 ∧ z ^ N * d = 1 := by
  refine ⟨d⁻¹ ^ ((N : ℂ)⁻¹), ?_, ?_⟩
  · intro h
    have := Complex.cpow_nat_inv_pow d⁻¹ hN
    rw [h, zero_pow hN] at this
    exact inv_ne_zero hd this.symm
  · rw [Complex.cpow_nat_inv_pow _ hN, inv_mul_cancel₀ hd]

theorem cancel_left {N : ℕ} {A X B : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) {z c : ℂ} (hz : z ≠ 0)
    (h : (z • A) * X = c • (A * B)) : X = (z⁻¹ * c) • B := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have h2 : A * (z • X) = A * (c • B) := by
    rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.smul_mul, h]
  have h3 : z • X = c • B := by
    have := congrArg (fun Y => A⁻¹ * Y) h2
    simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu] using this
  rw [mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hz, one_smul]

open NumberField in
theorem units_fin {L : Type*} [Field L] [NumberField L] (N : ℕ) (hN : 0 < N) :
    ∃ S : Finset (𝓞 L)ˣ, ∀ u : (𝓞 L)ˣ, ∃ v : (𝓞 L)ˣ, ∃ u0 ∈ S, u = v ^ N * u0 := by
  classical
  let f : Units.torsion L × (Fin (Units.rank L) → Fin N) → (𝓞 L)ˣ :=
    fun p => (p.1 : (𝓞 L)ˣ) * ∏ i, Units.fundSystem L i ^ ((p.2 i : ℕ) : ℤ)
  refine ⟨(Set.finite_range f).toFinset, fun u => ?_⟩
  obtain ⟨⟨ζ, e⟩, hu, -⟩ := Units.exist_unique_eq_mul_prod L u
  have h1 : ∀ i, 0 ≤ e i % N := fun i => Int.emod_nonneg (e i) (by omega)
  have h2 : ∀ i, e i % N < N := fun i => Int.emod_lt_of_pos (e i) (by omega)
  refine ⟨∏ i, Units.fundSystem L i ^ (e i / N), f (ζ, fun i => ⟨(e i % N).toNat, by
    have := h2 i; have := h1 i; omega⟩), by simp, ?_⟩
  have hsplit : ∀ i, Units.fundSystem L i ^ e i =
      (Units.fundSystem L i ^ (e i / N)) ^ N * Units.fundSystem L i ^ (((e i % N).toNat : ℕ) : ℤ) := by
    intro i
    rw [Int.toNat_of_nonneg (h1 i), ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_add]
    congr 1
    linarith [Int.mul_ediv_add_emod (e i) N]
  rw [hu]
  simp only [f]
  rw [Finset.prod_congr rfl (fun i _ => hsplit i), Finset.prod_mul_distrib, Finset.prod_pow]
  ac_rfl

end PositivityTheory.KB.MomentRationality.Cz.Red
end
end

noncomputable section

open Matrix

namespace PositivityTheory.KB.MomentRationality.Cz.Red

theorem local_decomp {ι : Type*} [Fintype ι] [Nonempty ι] {N : ℕ} (hN : 1 ≤ N) {M t : ℝ} (hM : 0 < M)
    (ht : 0 < t) {r : Fin N → ℝ} (hr : ∀ i, 0 < r i) (hrt : ∀ i j : Fin N, (j : ℕ) = i + 1 → t * r j ≤ r i)
    (a : ι → ℂ) (b k : ι → Matrix (Fin N) (Fin N) ℂ) (hb : ∀ w, (b w).BlockTriangular id)
    (hbM : ∀ w i j, ‖b w i j‖ ≤ M) (hbm : ∀ w i, M⁻¹ ≤ ‖b w i i‖)
    (hk : ∀ w, k w ∈ unitaryGroup (Fin N) ℂ)
    (hdet : ∀ w, (a w • (b w * diagonal (fun i => ((r i : ℝ) : ℂ)) * k w)).det = 1) :
    ∃ (p k' : ι → Matrix (Fin N) (Fin N) ℂ) (s : Fin N → ℝ), ∑ i, s i = 0 ∧
      (∀ i j : Fin N, (j : ℕ) = i + 1 → s j ≤ s i + (4 * Real.log M - Real.log t)) ∧
      (∀ w, (p w).BlockTriangular id) ∧ (∀ w i j, ‖p w i j‖ ≤ Real.exp (4 * Real.log M)) ∧
      (∀ w i, Real.exp (-(4 * Real.log M)) ≤ ‖p w i i‖) ∧ (∀ i, ∏ w, ‖p w i i‖ = 1) ∧
      (∀ w, (p w).det = 1) ∧ (∀ w, k' w ∈ unitaryGroup (Fin N) ℂ) ∧ (∀ w, (k' w).det = 1) ∧
      ∀ w, a w • (b w * diagonal (fun i => ((r i : ℝ) : ℂ)) * k w) =
        p w * diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) * k' w := by
  classical
  have hM1 : 1 ≤ M := by
    obtain ⟨w⟩ := ‹Nonempty ι›
    have h1 := hbM w ⟨0, hN⟩ ⟨0, hN⟩
    have h2 := hbm w ⟨0, hN⟩
    by_contra h
    push_neg at h
    have h3 : 1 < M⁻¹ := (one_lt_inv₀ hM).mpr h
    linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hbpos : ∀ w i, 0 < ‖b w i i‖ := fun w i => lt_of_lt_of_le (inv_pos.mpr hM) (hbm w i)
  have hBle : ∀ w i, Real.log ‖b w i i‖ ≤ Real.log M := fun w i =>
    Real.log_le_log (hbpos w i) (hbM w i i)
  have hBge : ∀ w i, -Real.log M ≤ Real.log ‖b w i i‖ := by
    intro w i
    rw [← Real.log_inv]
    exact Real.log_le_log (inv_pos.mpr hM) (hbm w i)
  have hnorm : ∀ w, ‖a w‖ ^ N * ((∏ i, ‖b w i i‖) * ∏ i, r i) = 1 := by
    intro w
    have h := congrArg norm (hdet w)
    have hk1 : ‖(k w).det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary (hk w))
    rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_of_upperTriangular (hb w),
      Matrix.det_diagonal] at h
    simp only [norm_mul, norm_pow, norm_prod, Fintype.card_fin, hk1, mul_one, norm_one,
      Complex.norm_real, Real.norm_eq_abs] at h
    rw [Finset.prod_congr rfl (fun i _ => abs_of_pos (hr i))] at h
    simpa [mul_assoc] using h
  have hapos : ∀ w, 0 < ‖a w‖ := by
    intro w
    rcases (norm_nonneg (a w)).lt_or_eq with h | h
    · exact h
    · have h1 := hnorm w
      rw [← h, zero_pow (by omega), zero_mul] at h1
      exact absurd h1 zero_ne_one
  have hsumlog : ∀ w, (N : ℝ) * Real.log ‖a w‖ + ∑ i, Real.log ‖b w i i‖ + ∑ i, Real.log (r i) = 0 := by
    intro w
    have h := congrArg Real.log (hnorm w)
    rw [Real.log_one, Real.log_mul (pow_ne_zero _ (hapos w).ne')
      (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => (hbpos w i).ne')
        (Finset.prod_ne_zero_iff.mpr fun i _ => (hr i).ne')),
      Real.log_mul (Finset.prod_ne_zero_iff.mpr fun i _ => (hbpos w i).ne')
        (Finset.prod_ne_zero_iff.mpr fun i _ => (hr i).ne'),
      Real.log_pow, Real.log_prod (fun i _ => (hbpos w i).ne'),
      Real.log_prod (fun i _ => (hr i).ne')] at h
    linarith
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiff : ∀ w w', Real.log ‖a w‖ - Real.log ‖a w'‖ ≤ 2 * Real.log M := by
    intro w w'
    have h1 := hsumlog w
    have h2 := hsumlog w'
    have hle : ∑ i, (Real.log ‖b w' i i‖ - Real.log ‖b w i i‖) ≤ ∑ i : Fin N, 2 * Real.log M :=
      Finset.sum_le_sum (fun i _ => by linarith [hBle w' i, hBge w i])
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_sub_distrib] at hle
    have h3 : (N : ℝ) * (Real.log ‖a w‖ - Real.log ‖a w'‖) ≤ N * (2 * Real.log M) := by nlinarith
    exact le_of_mul_le_mul_left h3 hNpos
  have avg_le : ∀ (f : ι → ℝ) (c : ℝ), (∀ w, f w ≤ c) → (∑ w, f w) / Fintype.card ι ≤ c := by
    intro f c h
    rw [div_le_iff₀ hn]
    have := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => h w)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using this
  have le_avg : ∀ (f : ι → ℝ) (c : ℝ), (∀ w, c ≤ f w) → c ≤ (∑ w, f w) / Fintype.card ι := by
    intro f c h
    rw [le_div_iff₀ hn]
    have := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => h w)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using this
  obtain ⟨s, hs⟩ : ∃ s : Fin N → ℝ, s = fun j =>
      (∑ w, (Real.log ‖a w‖ + Real.log ‖b w j j‖)) / Fintype.card ι + Real.log (r j) := ⟨_, rfl⟩
  have hs_sum : ∑ j, s j = 0 := by
    have h1 : ∀ w, ∑ j, (Real.log ‖a w‖ + Real.log ‖b w j j‖) = -∑ j, Real.log (r j) := by
      intro w
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      linarith [hsumlog w]
    rw [hs]
    simp only
    rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_comm, Finset.sum_congr rfl (fun w _ => h1 w),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  have hs_step : ∀ i j : Fin N, (j : ℕ) = i + 1 → s j ≤ s i + (4 * Real.log M - Real.log t) := by
    intro i j hij
    have hr' : Real.log (r j) ≤ Real.log (r i) - Real.log t := by
      have h := Real.log_le_log (mul_pos ht (hr j)) (hrt i j hij)
      rw [Real.log_mul ht.ne' (hr j).ne'] at h
      linarith
    have hB : (∑ w, (Real.log ‖b w j j‖ - Real.log ‖b w i i‖)) / Fintype.card ι ≤ 2 * Real.log M :=
      avg_le _ _ (fun w => by linarith [hBle w j, hBge w i])
    have hsplit : ∑ w, (Real.log ‖b w j j‖ - Real.log ‖b w i i‖) =
        ∑ w, (Real.log ‖a w‖ + Real.log ‖b w j j‖) - ∑ w, (Real.log ‖a w‖ + Real.log ‖b w i i‖) := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      funext w
      ring
    rw [hsplit, sub_div] at hB
    rw [hs]
    simp only
    linarith
  have he_up : ∀ w j, Real.log ‖a w‖ + Real.log (r j) - s j ≤ 3 * Real.log M := by
    intro w j
    have h : Real.log ‖a w‖ + Real.log (r j) - s j =
        (∑ w', (Real.log ‖a w‖ - Real.log ‖a w'‖ - Real.log ‖b w' j j‖)) / Fintype.card ι := by
      rw [hs]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      field_simp
      ring
    rw [h]
    exact avg_le _ _ (fun w' => by linarith [hdiff w w', hBge w' j])
  have hd_low : ∀ w i, -(4 * Real.log M) ≤
      Real.log ‖b w i i‖ + (Real.log ‖a w‖ + Real.log (r i) - s i) := by
    intro w i
    have h : Real.log ‖b w i i‖ + (Real.log ‖a w‖ + Real.log (r i) - s i) =
        (∑ w', (Real.log ‖a w‖ - Real.log ‖a w'‖ + Real.log ‖b w i i‖ - Real.log ‖b w' i i‖)) /
          Fintype.card ι := by
      rw [hs]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      field_simp
      ring
    rw [h]
    exact le_avg _ _ (fun w' => by linarith [hdiff w' w, hBge w i, hBle w' i])
  have hprod0 : ∀ i, ∑ w, (Real.log ‖b w i i‖ + (Real.log ‖a w‖ + Real.log (r i) - s i)) = 0 := by
    intro i
    rw [hs]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    field_simp
    ring
  have hz : ∀ w j, 0 < ‖a w * b w j j‖ := fun w j => by
    rw [norm_mul]
    exact mul_pos (hapos w) (hbpos w j)
  obtain ⟨φ, hφ⟩ : ∃ φ : ι → Fin N → ℂ, φ = fun w j =>
      (a w * b w j j) / ((‖a w * b w j j‖ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hφnorm : ∀ w j, ‖φ w j‖ = 1 := by
    intro w j
    rw [hφ]
    simp only
    rw [norm_div, Complex.norm_real, norm_norm, div_self (hz w j).ne']
  have hφn : ∀ w j, star (φ w j) * φ w j = 1 := by
    intro w j
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hφnorm]
    simp
  have hφz : ∀ w j, a w * b w j j * star (φ w j) = ((‖a w * b w j j‖ : ℝ) : ℂ) := by
    intro w j
    have hne : ((‖a w * b w j j‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hz w j).ne'
    rw [hφ]
    simp only
    simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
    rw [← mul_div_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    field_simp
    push_cast
    ring
  obtain ⟨d, hd⟩ : ∃ d : ι → Fin N → ℂ, d = fun w j =>
      a w * ((r j * Real.exp (-s j) : ℝ) : ℂ) * star (φ w j) := ⟨_, rfl⟩
  have hdnorm : ∀ w j, ‖d w j‖ = Real.exp (Real.log ‖a w‖ + Real.log (r j) - s j) := by
    intro w j
    rw [hd]
    simp only
    rw [norm_mul, norm_mul, norm_star, hφnorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (hr j) (Real.exp_pos _)), Real.exp_sub, Real.exp_add,
      Real.exp_log (hapos w), Real.exp_log (hr j), Real.exp_neg]
    field_simp
  have hpn : ∀ w i j, ‖(b w * diagonal (d w)) i j‖ =
      ‖b w i j‖ * Real.exp (Real.log ‖a w‖ + Real.log (r j) - s j) := by
    intro w i j
    rw [Matrix.mul_diagonal, norm_mul, hdnorm]
  have hpdiag : ∀ w i, ‖(b w * diagonal (d w)) i i‖ =
      Real.exp (Real.log ‖b w i i‖ + (Real.log ‖a w‖ + Real.log (r i) - s i)) := by
    intro w i
    rw [hpn, Real.exp_add, Real.exp_log (hbpos w i)]
  have hdetp : ∀ w, (b w * diagonal (d w)).det = 1 := by
    intro w
    rw [Matrix.det_mul, Matrix.det_of_upperTriangular (hb w), Matrix.det_diagonal,
      ← Finset.prod_mul_distrib]
    have h1 : ∀ j, b w j j * d w j = ((‖a w‖ * ‖b w j j‖ * (r j * Real.exp (-s j)) : ℝ) : ℂ) := by
      intro j
      rw [hd]
      simp only
      have h2 := hφz w j
      rw [norm_mul] at h2
      push_cast at h2 ⊢
      linear_combination ((r j : ℂ) * Complex.exp (-(s j : ℂ))) * h2
    rw [Finset.prod_congr rfl (fun j _ => h1 j), ← Complex.ofReal_prod]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← Real.exp_sum, Finset.sum_neg_distrib, hs_sum, neg_zero,
      Real.exp_zero, mul_one]
    rw [mul_assoc, hnorm w, Complex.ofReal_one]
  have hdiagu : ∀ w, diagonal (φ w) ∈ unitaryGroup (Fin N) ℂ := by
    intro w
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    rw [Pi.star_apply, mul_comm]
    exact hφn w j
  have hmain : ∀ w, a w • (b w * diagonal (fun i => ((r i : ℝ) : ℂ)) * k w) =
      b w * diagonal (d w) * diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) *
        (diagonal (φ w) * k w) := by
    intro w
    have hfun : (fun j => d w j * ((Real.exp (s j) : ℝ) : ℂ) * φ w j) =
        fun j => a w * ((r j : ℝ) : ℂ) := by
      funext j
      have he : ((Real.exp (-s j) : ℝ) : ℂ) * ((Real.exp (s j) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.exp_add]
        simp
      rw [hd]
      simp only
      rw [Complex.ofReal_mul]
      linear_combination (a w * (r j : ℂ) * ((Real.exp (-s j) : ℝ) : ℂ) * ((Real.exp (s j) : ℝ) : ℂ)) *
        hφn w j + a w * (r j : ℂ) * he
    conv_rhs => rw [← Matrix.mul_assoc, Matrix.mul_assoc (b w), Matrix.mul_assoc (b w),
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, hfun]
    have hsm : (diagonal fun j => a w * ((r j : ℝ) : ℂ)) = a w • diagonal (fun j => ((r j : ℝ) : ℂ)) := by
      ext i j
      simp [Matrix.diagonal_apply]
    rw [hsm, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨fun w => b w * diagonal (d w), fun w => diagonal (φ w) * k w, s, hs_sum, hs_step,
    fun w => (hb w).mul (Matrix.blockTriangular_diagonal _), ?_, ?_, ?_, hdetp,
    fun w => Submonoid.mul_mem _ (hdiagu w) (hk w), ?_, hmain⟩
  · intro w i j
    rw [hpn]
    calc ‖b w i j‖ * Real.exp (Real.log ‖a w‖ + Real.log (r j) - s j)
        ≤ M * Real.exp (3 * Real.log M) :=
          mul_le_mul (hbM w i j) (Real.exp_le_exp.mpr (he_up w j)) (Real.exp_pos _).le hM.le
      _ = Real.exp (4 * Real.log M) := by
          rw [show 4 * Real.log M = Real.log M + 3 * Real.log M by ring, Real.exp_add, Real.exp_log hM]
  · intro w i
    rw [hpdiag]
    exact Real.exp_le_exp.mpr (hd_low w i)
  · intro i
    simp only [hpdiag]
    rw [← Real.exp_sum, hprod0, Real.exp_zero]
  · intro w
    have h := congrArg Matrix.det (hmain w)
    rw [hdet w, Matrix.det_mul, Matrix.det_mul, hdetp, Matrix.det_diagonal, ← Complex.ofReal_prod,
      ← Real.exp_sum, hs_sum, Real.exp_zero, Complex.ofReal_one, one_mul, one_mul] at h
    exact h.symm

end PositivityTheory.KB.MomentRationality.Cz.Red
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.PrimalY
noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.TwSMInt2

open MomentRationality MomentRationality.Ht

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem primal_y (hL : IsTotallyComplex L) (hN : 1 ≤ N) {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, MomentRationality.mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding) {d : ℤ} (hd : d ≠ 0)
    (hdi : ∀ i j, IsIntegral ℤ ((d : L) * gi g i j))
    {M : ℝ} {p : Sp L N} (hp : p ∈ Om L N M) {s : Fin N → ℝ} (hs : ∑ i, s i = 0) {k : Sp L N} (hk : k ∈ KS L N)
    {imax : Fin N} (himax : ∀ i, s i ≤ s imax) (y : Lat L N) (hy : y ≠ 0) :
    (M⁻¹) ^ 2 * (∑ w : InfinitePlace L, ‖z w‖ ^ 2 + 1)⁻¹ * ((d : ℝ) ^ 2)⁻¹ * Real.exp (-s imax) ^ 2 ≤
      q (actL (ofS L N (c * (p * dg L N s hs * k))) (one L N).1) y := by
  classical
  rw [q_actL]
  set v := gi g *ᵥ toL y with hv
  have hv0 : v ≠ 0 := gi_ne g hy
  have hne : (Finset.univ.filter fun i => v i ≠ 0).Nonempty := by
    by_contra hcon
    apply hv0
    funext i
    by_contra hi
    exact hcon ⟨i, by simpa using hi⟩
  have hi0mem : v ((Finset.univ.filter fun i => v i ≠ 0).max' hne) ≠ 0 := by
    have := Finset.max'_mem _ hne
    simpa using this
  set i0 := (Finset.univ.filter fun i => v i ≠ 0).max' hne with hi0
  have hzero : ∀ j, i0 < j → v j = 0 := by
    intro j hj
    by_contra hjne
    have : j ≤ i0 := Finset.le_max' _ j (by simpa using hjne)
    exact absurd hj (not_lt.mpr this)
  have hplace := fun w => primal_place hN hc hp hs hk y hzero w
  set Z := ∑ w : InfinitePlace L, ‖z w‖ ^ 2 + 1 with hZdef
  have hZ : 0 < Z := by positivity
  have hsum := sum_sq_ge hL hd hi0mem (int_d hdi y i0)
  have he : Real.exp (-s imax) ≤ Real.exp (-s i0) := Real.exp_le_exp.mpr (by linarith [himax i0])
  have hterm : ∀ w, (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 * ‖w.embedding (v i0)‖ ^ 2 ≤
      ∑ i, ‖(MomentRationality.mt (c * (p * dg L N s hs * k))⁻¹ w *ᵥ toR y w) i‖ ^ 2 := by
    intro w
    refine le_trans ?_ (hplace w)
    have hzpos : 0 < ‖z w‖ := norm_pos_iff.mpr (z_ne hN hc w)
    have hzle : ‖z w‖ ^ 2 ≤ Z := by
      have := Finset.single_le_sum (f := fun w => ‖z w‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ w)
      linarith
    have hZinv : Z⁻¹ ≤ (‖z w‖⁻¹) ^ 2 := by
      rw [inv_pow]
      exact inv_anti₀ (by positivity) hzle
    calc (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 * ‖w.embedding (v i0)‖ ^ 2
        ≤ (M⁻¹) ^ 2 * (‖z w‖⁻¹) ^ 2 * Real.exp (-s i0) ^ 2 * ‖w.embedding (v i0)‖ ^ 2 := by
          gcongr
      _ = _ := by ring
  have hA : 0 ≤ (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 := by positivity
  calc (M⁻¹) ^ 2 * Z⁻¹ * ((d : ℝ) ^ 2)⁻¹ * Real.exp (-s imax) ^ 2
      = (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 * ((d : ℝ) ^ 2)⁻¹ := by ring
    _ ≤ (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 * ∑ w : InfinitePlace L, ‖w.embedding (v i0)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsum hA
    _ = ∑ w, (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 * ‖w.embedding (v i0)‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun w _ => hterm w

theorem dual_y (hL : IsTotallyComplex L) (hN : 1 ≤ N) {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, MomentRationality.mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding) {d : ℤ} (hd : d ≠ 0)
    (hdg : ∀ i j, IsIntegral ℤ ((d : L) * ((g : Matrix (Fin N) (Fin N) L)ᵀ) i j))
    {M : ℝ} {p : Sp L N} (hp : p ∈ Om L N M) {s : Fin N → ℝ} (hs : ∑ i, s i = 0) {k : Sp L N} (hk : k ∈ KS L N)
    {imin : Fin N} (himin : ∀ i, s imin ≤ s i) (y : Lat L N) (hy : y ≠ 0) :
    (M⁻¹) ^ 2 * (∑ w : InfinitePlace L, ‖z w‖⁻¹ ^ 2 + 1)⁻¹ * ((d : ℝ) ^ 2)⁻¹ * Real.exp (s imin) ^ 2 ≤
      q (dualH (actL (ofS L N (c * (p * dg L N s hs * k))) (one L N).1)) y := by
  classical
  rw [q_dual]
  set v := (g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y with hv
  have hv0 : v ≠ 0 := gT_ne g hy
  have hne : (Finset.univ.filter fun i => v i ≠ 0).Nonempty := by
    by_contra hcon
    apply hv0
    funext i
    by_contra hi
    exact hcon ⟨i, by simpa using hi⟩
  have hi1mem : v ((Finset.univ.filter fun i => v i ≠ 0).min' hne) ≠ 0 := by
    have := Finset.min'_mem _ hne
    simpa using this
  set i1 := (Finset.univ.filter fun i => v i ≠ 0).min' hne with hi1
  have hzero : ∀ j, j < i1 → v j = 0 := by
    intro j hj
    by_contra hjne
    have : i1 ≤ j := Finset.min'_le _ j (by simpa using hjne)
    exact absurd hj (not_lt.mpr this)
  have hplace := fun w => dual_place hc hp hs hk y hzero w
  set Z := ∑ w : InfinitePlace L, ‖z w‖⁻¹ ^ 2 + 1 with hZdef
  have hZ : 0 < Z := by positivity
  have hsum := sum_sq_ge hL hd hi1mem (int_d hdg y i1)
  have he : Real.exp (s imin) ≤ Real.exp (s i1) := Real.exp_le_exp.mpr (himin i1)
  have hterm : ∀ w, (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 * ‖w.embedding (v i1)‖ ^ 2 ≤
      ∑ i, ‖((MomentRationality.mt (c * (p * dg L N s hs * k)) w)ᵀ *ᵥ toR y w) i‖ ^ 2 := by
    intro w
    refine le_trans ?_ (hplace w)
    have hzpos : 0 < ‖z w‖ := norm_pos_iff.mpr (z_ne hN hc w)
    have hzle : ‖z w‖⁻¹ ^ 2 ≤ Z := by
      have := Finset.single_le_sum (f := fun w => ‖z w‖⁻¹ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ w)
      linarith
    have hZinv : Z⁻¹ ≤ ‖z w‖ ^ 2 := by
      have := inv_anti₀ (by positivity) hzle
      rwa [inv_pow, inv_inv] at this
    calc (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 * ‖w.embedding (v i1)‖ ^ 2
        ≤ (M⁻¹) ^ 2 * ‖z w‖ ^ 2 * Real.exp (s i1) ^ 2 * ‖w.embedding (v i1)‖ ^ 2 := by
          gcongr
      _ = _ := by ring
  have hA : 0 ≤ (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 := by positivity
  calc (M⁻¹) ^ 2 * Z⁻¹ * ((d : ℝ) ^ 2)⁻¹ * Real.exp (s imin) ^ 2
      = (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 * ((d : ℝ) ^ 2)⁻¹ := by ring
    _ ≤ (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 * ∑ w : InfinitePlace L, ‖w.embedding (v i1)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsum hA
    _ = ∑ w, (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 * ‖w.embedding (v i1)‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun w _ => hterm w

theorem sHtB : SHtB := by
  intro L _ _ hL N hN c hrat M
  obtain ⟨g, z, hc⟩ := hrat
  classical
  obtain ⟨d, hd, hint⟩ := exists_den
    ((Finset.univ.image fun ij : Fin N × Fin N => gi g ij.1 ij.2) ∪
      (Finset.univ.image fun ij : Fin N × Fin N => ((g : Matrix (Fin N) (Fin N) L)ᵀ) ij.1 ij.2))
  have hdi : ∀ i j, IsIntegral ℤ ((d : L) * gi g i j) := fun i j =>
    hint _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
  have hdg : ∀ i j, IsIntegral ℤ ((d : L) * ((g : Matrix (Fin N) (Fin N) L)ᵀ) i j) := fun i j =>
    hint _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
  set A1 := (M⁻¹) ^ 2 * (∑ w : InfinitePlace L, ‖z w‖ ^ 2 + 1)⁻¹ * ((d : ℝ) ^ 2)⁻¹ with hA1def
  set A2 := (M⁻¹) ^ 2 * (∑ w : InfinitePlace L, ‖z w‖⁻¹ ^ 2 + 1)⁻¹ * ((d : ℝ) ^ 2)⁻¹ with hA2def
  refine ⟨(A1 * A2)⁻¹, ?_⟩
  intro p hp s hs k hk
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨imax, himax⟩ := Finite.exists_max s
  obtain ⟨imin, himin⟩ := Finite.exists_min s
  have hM : M ≠ 0 := by
    rintro rfl
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace L))
    have h1 := hp.2.2.2 ⟨0, hN⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ w0)] at h1
    · exact zero_ne_one h1
    · exact le_antisymm (hp.2.1 w0 _ _) (norm_nonneg _)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hA1 : 0 < A1 := by positivity
  have hA2 : 0 < A2 := by positivity
  have h1 := lam_ge hN (fun y hy => primal_y hL hN hc hd hdi hp hs hk himax y hy)
  have h2 := lam_ge hN (fun y hy => dual_y hL hN hc hd hdg hp hs hk himin y hy)
  set e1 := Real.exp (-s imax) ^ 2
  set e2 := Real.exp (s imin) ^ 2
  set X := Real.exp (2 * (s imax - s imin))
  have he1 : 0 < e1 := by positivity
  have he2 : 0 < e2 := by positivity
  have hprod : e1 * e2 * X = 1 := by
    simp only [e1, e2, X, sq, ← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  have hX : X = (e1 * e2)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hprod)
  show (lam _ * lam _)⁻¹ ≤ _
  calc (lam _ * lam _)⁻¹ ≤ (A1 * e1 * (A2 * e2))⁻¹ := by
        apply inv_anti₀ (by positivity)
        exact mul_le_mul h1 h2 (by positivity) (le_trans (by positivity) h1)
    _ = (A1 * A2)⁻¹ * X := by rw [hX]; ring
    _ ≤ (A1 * A2)⁻¹ * Real.exp (2 * W s) := by
        gcongr
        show Real.exp (2 * (s imax - s imin)) ≤ Real.exp (2 * W s)
        apply Real.exp_le_exp.mpr
        have hW := sub_le_sum_abs_consecutive_diff s imax imin
        unfold W
        linarith

end PositivityTheory.KB.TwSMInt2
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.SRedOf
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.TwSMInt2

open MomentRationality MomentRationality.Cz.Red

theorem sRed_of (hG : SRedGL) : SRed := by
  intro L _ _ hL N hN
  classical
  obtain ⟨R, M, t, hM, ht, H⟩ := hG L hL N hN
  obtain ⟨S, hS⟩ := units_fin (L := L) N (by omega)
  let G : (↥R) × (↥S) → GL (Fin N) L := fun j =>
    ddGL N (Units.map (algebraMap (𝓞 L) L).toMonoidHom ((j.2 : (𝓞 L)ˣ)⁻¹)) * (j.1 : GL (Fin N) L)
  have hGm : ∀ j (w : InfinitePlace L), ((G j : Matrix (Fin N) (Fin N) L).map w.embedding) =
      dd N (embO w (((j.2 : (𝓞 L)ˣ)⁻¹ : (𝓞 L)ˣ) : 𝓞 L)) *
        ((j.1 : GL (Fin N) L) : Matrix (Fin N) (Fin N) L).map w.embedding := by
    intro j w
    have e : (G j : Matrix (Fin N) (Fin N) L) =
        dd N (algebraMap (𝓞 L) L (((j.2 : (𝓞 L)ˣ)⁻¹ : (𝓞 L)ˣ) : 𝓞 L)) *
          ((j.1 : GL (Fin N) L) : Matrix (Fin N) (Fin N) L) := rfl
    rw [e, Matrix.map_mul, dd_map]
    rfl
  have hGd : ∀ j (w : InfinitePlace L), ((G j : Matrix (Fin N) (Fin N) L).map w.embedding).det ≠ 0 := by
    intro j w
    have h := (RingHom.map_det w.embedding (G j : Matrix (Fin N) (Fin N) L)).symm
    rw [RingHom.mapMatrix_apply] at h
    rw [h]
    exact (_root_.map_ne_zero _).2 (G j).det_ne_zero
  choose z hz0 hz using fun j w => exists_root (N := N) (by omega) (hGd j w)
  let c : (↥R) × (↥S) → Sp L N := fun j w => ⟨z j w • (G j : Matrix (Fin N) (Fin N) L).map w.embedding, by
    rw [det_smul, Fintype.card_fin, hz]⟩
  refine ⟨(↥R) × (↥S), inferInstance, c, Real.exp (4 * Real.log M), 4 * Real.log M - Real.log t,
    fun j => ⟨G j, z j, fun w => rfl⟩, fun x => ?_⟩
  obtain ⟨δ, g, hg, r, hr, hrt, hw⟩ := H (ofS L N x)
  choose b hb hbM hbm k hk hbk using hw
  obtain ⟨v, u0, hu0, hu⟩ := hS (GeneralLinearGroup.det δ)
  have hu' : (δ : Matrix (Fin N) (Fin N) (𝓞 L)).det = (v : 𝓞 L) ^ N * u0 := by
    have := congrArg (fun u : (𝓞 L)ˣ => (u : 𝓞 L)) hu
    simpa using this
  let σ : SpecialLinearGroup (Fin N) (𝓞 L) :=
    ⟨((v⁻¹ : (𝓞 L)ˣ) : 𝓞 L) • (dd N ((u0⁻¹ : (𝓞 L)ˣ) : 𝓞 L) * (δ : Matrix (Fin N) (Fin N) (𝓞 L))), by
      rw [det_smul, Fintype.card_fin, det_mul, det_dd hN, hu']
      calc ((v⁻¹ : (𝓞 L)ˣ) : 𝓞 L) ^ N * (((u0⁻¹ : (𝓞 L)ˣ) : 𝓞 L) * ((v : 𝓞 L) ^ N * u0)) =
          (((v⁻¹ : (𝓞 L)ˣ) : 𝓞 L) * v) ^ N * (((u0⁻¹ : (𝓞 L)ˣ) : 𝓞 L) * u0) := by ring
        _ = 1 := by rw [Units.inv_mul, Units.inv_mul, one_pow, one_mul]⟩
  let γ : Sp L N := fun w => SpecialLinearGroup.map (n := Fin N) (embO w) σ
  let j : (↥R) × (↥S) := (⟨g, hg⟩, ⟨u0, hu0⟩)
  refine ⟨γ, ⟨σ, rfl⟩, j, ?_⟩
  obtain ⟨y, hy⟩ : ∃ y : Sp L N, y = (c j)⁻¹ * (γ * x) := ⟨_, rfl⟩
  rw [← hy]
  have hcy : c j * y = γ * x := by rw [hy, mul_inv_cancel_left]
  have hY : ∀ w, MomentRationality.mt y w = ((z j w)⁻¹ * embO w ((v⁻¹ : (𝓞 L)ˣ) : 𝓞 L)) •
      (b w * diagonal (fun i => ((r i : ℝ) : ℂ)) * k w) := by
    intro w
    refine cancel_left (hGd j w) (hz0 j w) ?_
    have h1 : (z j w • (G j : Matrix (Fin N) (Fin N) L).map w.embedding) * MomentRationality.mt y w =
        (((v⁻¹ : (𝓞 L)ˣ) : 𝓞 L) • (dd N ((u0⁻¹ : (𝓞 L)ˣ) : 𝓞 L) *
          (δ : Matrix (Fin N) (Fin N) (𝓞 L)))).map (embO w) * MomentRationality.mt x w :=
      congrArg (fun a => MomentRationality.mt a w) hcy
    have h2 : (δ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) * MomentRationality.mt x w =
        (g : Matrix (Fin N) (Fin N) L).map w.embedding * b w * diagonal (fun i => ((r i : ℝ) : ℂ)) * k w := hbk w
    have h3 : (((v⁻¹ : (𝓞 L)ˣ) : 𝓞 L) • (dd N ((u0⁻¹ : (𝓞 L)ˣ) : 𝓞 L) *
          (δ : Matrix (Fin N) (Fin N) (𝓞 L)))).map (embO w) = embO w ((v⁻¹ : (𝓞 L)ˣ) : 𝓞 L) •
          (dd N (embO w ((u0⁻¹ : (𝓞 L)ˣ) : 𝓞 L)) * (δ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w)) := by
      rw [← dd_map, ← Matrix.map_mul]
      ext i l
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rw [h1, h3, Matrix.smul_mul, Matrix.mul_assoc, h2, hGm]
    simp only [Matrix.mul_assoc]
    rfl
  obtain ⟨p, k', s, hssum, hsieg, hpT, hpM, hpm, hpP, hpd, hk'U, hk'd, hdec⟩ :=
    local_decomp hN hM ht hr hrt (fun w => (z j w)⁻¹ * embO w ((v⁻¹ : (𝓞 L)ˣ) : 𝓞 L)) b k hb hbM hbm hk
      (fun w => by rw [← hY w]; exact (y w).2)
  refine ⟨fun w => ⟨p w, hpd w⟩, ⟨hpT, hpM, ?_, hpP⟩, s, hssum, hsieg, fun w => ⟨k' w, hk'd w⟩, hk'U, ?_⟩
  · intro w i
    rw [← Real.exp_neg]
    exact hpm w i
  · funext w
    apply Subtype.ext
    show MomentRationality.mt y w = p w * diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) * k' w
    rw [hY w, hdec w]

end PositivityTheory.KB.TwSMInt2

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.SIntB
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.SetLIntegralLeOfMul
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.TwSMInt2

open PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem setLIntegral_le_of_mul {α : Type*} [MeasurableSpace α] (μ : Measure α) {X : Set α} (hX : MeasurableSet X)
    (f : α → ℝ≥0∞) (D : ℝ≥0∞) (h : ∀ x ∈ X, f x * μ X ≤ D) : ∫⁻ x in X, f x ∂μ ≤ D := by
  rcases eq_or_ne (μ X) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.mpr h0]
  rcases eq_or_ne D ⊤ with hD | hD
  · simp [hD]
  rcases eq_or_ne (μ X) ⊤ with htop | htop
  · have hz : ∀ x ∈ X, f x = 0 := by
      intro x hx
      by_contra hne
      have := h x hx
      rw [htop, ENNReal.mul_top hne] at this
      exact hD (top_le_iff.mp this)
    calc ∫⁻ x in X, f x ∂μ = ∫⁻ _ in X, 0 ∂μ := setLIntegral_congr_fun hX hz
      _ = 0 := lintegral_zero
      _ ≤ D := bot_le
  · have hle : ∀ x ∈ X, f x ≤ D / μ X := fun x hx =>
      (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl htop)).mpr (h x hx)
    calc ∫⁻ x in X, f x ∂μ ≤ ∫⁻ _ in X, D / μ X ∂μ := setLIntegral_mono' hX hle
      _ = D / μ X * μ X := setLIntegral_const X _
      _ = D := ENNReal.div_mul_cancel h0 htop

theorem main_of_pack (hN : 2 ≤ N) [Fintype ι] [Nonempty ι] [MeasurableSpace (G ι N)] [BorelSpace (G ι N)]
    (μ : Measure (G ι N)) [μ.IsHaarMeasure] {P : Set (G ι N)} (hPc : IsCompact P)
    (T B : ℝ) (hpk : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (m : Fin N → ℤ) (s0 : Fin N → ℝ), ∑ i, s0 i = 0 → Cone T s0 →
      (∀ i, (m i : ℝ) ≤ s0 i ∧ s0 i ≤ m i + 1) →
      μ (Xb P T m) ≤ K * ENNReal.ofReal (Real.exp (-2 * Phi s0))) (hB : B < 2 * ((N : ℝ) - 1)) (C : ℝ≥0∞) (hC : C ≠ ⊤) (f : G ι N → ℝ≥0∞)
    (hf : ∀ p ∈ P, ∀ (s : Fin N → ℝ) (hs : ∑ i, s i = 0), Cone T s → ∀ k ∈ KS,
      f (p * dg s hs * k) ≤ C * ENNReal.ofReal (Real.exp (B * W s))) :
    ∫⁻ x in Sg P T, f x ∂μ < ⊤ := by
  obtain ⟨K, hK, hμ⟩ := hpk
  obtain ⟨c, ε, hε, hexp⟩ := ineq hN T B hB
  set D : (Fin N → ℤ) → ℝ≥0∞ := fun m => C * K * (ENNReal.ofReal (Real.exp (c + ε * N)) *
    ENNReal.ofReal (Real.exp (-(ε * ∑ i, |((m i : ℤ) : ℝ)|)))) with hD
  have hcov : Sg P T ⊆ ⋃ m, Xb P T m := by
    rintro x ⟨p, hp, s, hs, hcone, k, hk, rfl⟩
    refine Set.mem_iUnion.mpr ⟨fun i => ⌊s i⌋, p, hp, s, hs, hcone, fun i => ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩, k, hk, rfl⟩
  have hpiece : ∀ m, ∫⁻ x in Xb P T m, f x ∂μ ≤ D m := by
    intro m
    refine setLIntegral_le_of_mul μ (cpt_X hPc T m).measurableSet f (D m) ?_
    rintro x ⟨p, hp, s, hs, hcone, hb, k, hk, rfl⟩
    have h1 := hf p hp s hs hcone k hk
    have h2 := hμ m s hs hcone hb
    have habs : ∑ i, |((m i : ℤ) : ℝ)| ≤ ∑ i, |s i| + N := by
      have : ∀ i, |((m i : ℤ) : ℝ)| ≤ |s i| + 1 := by
        intro i
        have := (hb i).1
        have := (hb i).2
        calc |((m i : ℤ) : ℝ)| = |s i - (s i - m i)| := by ring_nf
          _ ≤ |s i| + |s i - m i| := abs_sub _ _
          _ ≤ |s i| + 1 := by
            gcongr
            rw [abs_le]
            constructor <;> linarith
      calc ∑ i, |((m i : ℤ) : ℝ)| ≤ ∑ i, (|s i| + 1) := Finset.sum_le_sum fun i _ => this i
        _ = ∑ i, |s i| + N := by simp [Finset.sum_add_distrib]
    have hreal : Real.exp (B * W s) * Real.exp (-2 * Phi s) ≤
        Real.exp (c + ε * N) * Real.exp (-(ε * ∑ i, |((m i : ℤ) : ℝ)|)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := hexp s hs hcone
      nlinarith
    calc f (p * dg s hs * k) * μ (Xb P T m)
        ≤ (C * ENNReal.ofReal (Real.exp (B * W s))) * (K * ENNReal.ofReal (Real.exp (-2 * Phi s))) :=
          mul_le_mul' h1 h2
      _ = C * K * ENNReal.ofReal (Real.exp (B * W s) * Real.exp (-2 * Phi s)) := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
          ring
      _ ≤ C * K * ENNReal.ofReal (Real.exp (c + ε * N) * Real.exp (-(ε * ∑ i, |((m i : ℤ) : ℝ)|))) := by
          gcongr
      _ = D m := by
          rw [hD, ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hsum : ∑' m, D m ≠ ⊤ := by
    simp only [hD]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hC hK)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (summ ε hε))
  calc ∫⁻ x in Sg P T, f x ∂μ ≤ ∫⁻ x in ⋃ m, Xb P T m, f x ∂μ := lintegral_mono_set hcov
    _ ≤ ∑' m, ∫⁻ x in Xb P T m, f x ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' m, D m := ENNReal.tsum_le_tsum hpiece
    _ < ⊤ := lt_top_iff_ne_top.mpr hsum

end PositivityTheory.KB.TwSMInt2

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.MtInvUpper
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.TwSMInt2

open PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem sum_meas_le {α β : Type*} [MeasurableSpace α] (μ : Measure α) (F : Finset β) (A : β → Set α)
    (hA : ∀ b, MeasurableSet (A b)) {Y : Set α} (hY : MeasurableSet Y) (hsub : ∀ b ∈ F, A b ⊆ Y) (R : ℕ)
    (hR : ∀ x, ∀ S : Finset β, S ⊆ F → (∀ b ∈ S, x ∈ A b) → S.card ≤ R) : ∑ b ∈ F, μ (A b) ≤ R * μ Y := by
  classical
  have e1 : ∑ b ∈ F, μ (A b) = ∫⁻ x, ∑ b ∈ F, (A b).indicator (1 : α → ℝ≥0∞) x ∂μ := by
    rw [lintegral_finsetSum _ fun b _ => measurable_one.indicator (hA b)]
    exact Finset.sum_congr rfl fun b _ => (lintegral_indicator_one (hA b)).symm
  have e2 : (R : ℝ≥0∞) * μ Y = ∫⁻ x, Y.indicator (fun _ => (R : ℝ≥0∞)) x ∂μ := (lintegral_indicator_const hY _).symm
  rw [e1, e2]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ Y
  · rw [Set.indicator_of_mem hx]
    have : ∑ b ∈ F, (A b).indicator (1 : α → ℝ≥0∞) x = ((F.filter fun b => x ∈ A b).card : ℝ≥0∞) := by
      simp [Set.indicator_apply]
    rw [this]
    exact Nat.cast_le.2 (by
      convert hR x (F.filter fun b => x ∈ A b) (Finset.filter_subset _ _) fun b hb => (Finset.mem_filter.1 hb).2)
  · rw [Set.indicator_of_notMem hx]
    refine (Finset.sum_eq_zero fun b hb => Set.indicator_of_notMem (fun h => hx (hsub b hb h)) _).le

theorem mt_mul' (a b : G ι N) (w : ι) : mt (a * b) w = mt a w * mt b w := rfl

theorem mt_nu_same (w0 : ι) (c : SpecialLinearGroup (Fin N) GaussianInt) :
    mt (nu w0 c) w0 = (c : Matrix (Fin N) (Fin N) GaussianInt).map GaussianInt.toComplex := by
  classical
  simp only [MomentRationality.Cz.Pk.mt, nu, MonoidHom.comp_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
  rfl

theorem mt_nu_ne {w0 w : ι} (h : w ≠ w0) (c : SpecialLinearGroup (Fin N) GaussianInt) :
    mt (nu w0 c) w = 1 := by
  classical
  simp only [MomentRationality.Cz.Pk.mt, nu, MonoidHom.comp_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h]
  rfl

theorem mt_inv_upper {a : G ι N} {w : ι} (h : (mt a w).BlockTriangular id) : (mt a⁻¹ w).BlockTriangular id := by
  have h1 : mt a⁻¹ w * mt a w = 1 := by rw [← mt_mul', inv_mul_cancel]; rfl
  haveI : Invertible (mt a w) := invertibleOfLeftInverse _ _ h1
  rw [← Matrix.inv_eq_left_inv h1]
  exact blockTriangular_inv_of_blockTriangular h

theorem mt_inv_unit {a : G ι N} {w : ι} (h : mt a w ∈ unitaryGroup (Fin N) ℂ) : mt a⁻¹ w ∈ unitaryGroup (Fin N) ℂ := by
  have h1 : mt a⁻¹ w * mt a w = 1 := by rw [← mt_mul', inv_mul_cancel]; rfl
  rw [← Matrix.inv_eq_left_inv h1, Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.1 h)]
  exact Unitary.star_mem h

theorem pack [Fintype ι] [Nonempty ι] [MeasurableSpace (G ι N)] [BorelSpace (G ι N)] (μ : Measure (G ι N))
    [μ.IsHaarMeasure] {P : Set (G ι N)} (hPc : IsCompact P) (M T : ℝ) (hP : P ⊆ PB M) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (m : Fin N → ℤ) (s0 : Fin N → ℝ), ∑ i, s0 i = 0 → Cone T s0 →
      (∀ i, (m i : ℝ) ≤ s0 i ∧ s0 i ≤ m i + 1) →
      μ (Xb P T m) ≤ K * ENNReal.ofReal (Real.exp (-2 * Phi s0)) := by
  classical
  obtain ⟨w0⟩ := ‹Nonempty ι›
  obtain ⟨R0, hR0⟩ := tri (N := N) M
  obtain ⟨R, hR⟩ := fin_bdd (N := N) R0
  obtain ⟨R1, hR1⟩ := env (N := N) M T
  refine ⟨R * μ (Zb R1), ENNReal.mul_ne_top (ENNReal.natCast_ne_top R) (cpt_Z R1).measure_lt_top.ne, ?_⟩
  intro m s0 hs0 hc0 hm0
  obtain ⟨F, hF, hcard⟩ := count s0
  have hs0' : ∑ i, (-s0 i) = 0 := by rw [Finset.sum_neg_distrib, hs0, neg_zero]
  have hXm : MeasurableSet (Xb P T m) := (cpt_X hPc T m).measurableSet
  have hZm : MeasurableSet (Zb (ι := ι) (N := N) R1) := (cpt_Z R1).measurableSet
  have hclose : ∀ s s' : Fin N → ℝ, (∀ i, (m i : ℝ) ≤ s i ∧ s i ≤ m i + 1) →
      (∀ i, (m i : ℝ) ≤ s' i ∧ s' i ≤ m i + 1) → ∀ i, |s i - s' i| ≤ 1 := by
    intro s s' h h' i
    have := h i; have := h' i
    rw [abs_le]; constructor <;> linarith
  have key := sum_meas_le μ F (fun c => (fun x => (nu w0 c)⁻¹ * x) ⁻¹' Xb P T m)
    (fun c => measurable_const_mul _ hXm)
    (Y := (fun x => (dg (fun i => -s0 i) hs0' : G ι N) * x) ⁻¹' Zb R1) (measurable_const_mul _ hZm) ?_ R ?_
  · simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul] at key
    have h1 : ENNReal.ofReal (Real.exp (2 * Phi s0)) * μ (Xb P T m) ≤ R * μ (Zb R1) :=
      (mul_le_mul' hcard le_rfl).trans key
    have h2 : ENNReal.ofReal (Real.exp (2 * Phi s0)) * ENNReal.ofReal (Real.exp (-2 * Phi s0)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      simp
    calc μ (Xb P T m) = (ENNReal.ofReal (Real.exp (2 * Phi s0)) * μ (Xb P T m)) *
          ENNReal.ofReal (Real.exp (-2 * Phi s0)) := by rw [mul_right_comm, h2, one_mul]
      _ ≤ _ := mul_le_mul' h1 le_rfl
  · rintro c hc x ⟨p, hp, s, hs, -, hm, k, hk, hx⟩ w i j
    have hx' : x = nu w0 c * p * dg s hs * k := by
      have : x = nu w0 c * ((nu w0 c)⁻¹ * x) := by group
      rw [this]; dsimp only at hx; rw [hx]; simp only [mul_assoc]
    rw [hx']
    have hn : (mt (nu w0 c) w).BlockTriangular id ∧
        ∀ i j, i ≤ j → ‖mt (nu w0 c) w i j‖ ≤ 2 * Real.exp (s0 i - s0 j) := by
      by_cases hw : w = w0
      · subst hw; rw [mt_nu_same]; exact hF c hc
      · rw [mt_nu_ne hw]
        refine ⟨blockTriangular_one, fun i j _ => ?_⟩
        by_cases hij : i = j
        · subst hij; simp
        · rw [one_apply_ne hij, norm_zero]; positivity
    exact hR1 _ _ _ s0 s hc0 (hclose _ _ hm hm0) hn.1 hn.2 (hP hp w).1 (hP hp w).2 (hk w) i j
  · intro x S hS hx
    refine hR S fun c hc c' hc' i j => ?_
    obtain ⟨p, hp, s, hs, -, hm, k, hk, e⟩ := hx c hc
    obtain ⟨p', hp', s', hs', -, hm', k', hk', e'⟩ := hx c' hc'
    dsimp only at e e'
    have hE : nu w0 (c⁻¹ * c') * p' * dg s' hs' = p * dg s hs * (k * k'⁻¹) := by
      have a1 : p' * dg s' hs' = (nu w0 c')⁻¹ * x * k'⁻¹ := by rw [e']; group
      rw [mul_assoc, a1, ← mul_assoc (p * dg s hs), ← e, map_mul, map_inv]; group
    have hup : (mt (nu w0 (c⁻¹ * c')) w0).BlockTriangular id := by
      rw [map_mul, map_inv, mt_mul']
      refine (mt_inv_upper ?_).mul ?_
      · rw [mt_nu_same]; exact (hF c (hS hc)).1
      · rw [mt_nu_same]; exact (hF c' (hS hc')).1
    have := hR0 (mt (nu w0 (c⁻¹ * c')) w0) (mt p' w0) (mt p w0) (mt (k * k'⁻¹) w0) s' s (hclose _ _ hm' hm) hup
      (hP hp' w0).1 (hP hp w0).1 (hP hp' w0).2 (hP hp w0).2 (p' w0).2 (p w0).2
      (by rw [mt_mul']; exact mul_mem (hk w0) (mt_inv_unit (hk' w0))) (congrArg (fun y => mt y w0) hE) i j
    rw [mt_nu_same] at this
    exact this

end PositivityTheory.KB.TwSMInt2

end
end

noncomputable section

open NumberField MeasureTheory

namespace PositivityTheory.KB.TwSMInt2

theorem sIntB : PositivityTheory.KB.SIntB := by
  intro L _ _ _ N hN μ _ M T B hB C hC f hf
  exact main_of_pack (ι := InfinitePlace L) hN μ (MomentRationality.Cz.Pk.cpt_Om M) T B
    (pack μ (MomentRationality.Cz.Pk.cpt_Om M) M T fun p hp w => ⟨hp.1 w, hp.2.1 w⟩) hB C hC f hf

end PositivityTheory.KB.TwSMInt2

end
end

namespace PositivityTheory.KB.TwSMInt2

theorem sMom_of (h : SHt) : SMom :=
  sMom_of_parts discrete_specialLinearGroup_ringOfIntegers sHtB sIntB (sRed_of sRedGL2) h

end PositivityTheory.KB.TwSMInt2
