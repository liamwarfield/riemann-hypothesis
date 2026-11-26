module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ProductBoundOfFactorBounds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.DecDeriv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ContinuousBlkWConj

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ProductBoundThreeFactors
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.FinBFrobConjGe
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.CayleyConjInvMemHermitianGroup
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem conj_inv_mul_conj {m : ℕ} (P Y g : Matrix (Fin m) (Fin m) ℂ) (hP : IsUnit P.det) :
    P * ((P⁻¹ * Y * P)⁻¹ * g) * P⁻¹ = Y⁻¹ * (P * g * P⁻¹) := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hP]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hP]

theorem unitary_hermitian_form_mul_mem {k r : ℕ} {s x : Mat k r} (hs : s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : s * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  show (s * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (s * x) = Formalism.QuantumDeterminants.Hpk k r
  have hs' : sᴴ * Formalism.QuantumDeterminants.Hpk k r * s = Formalism.QuantumDeterminants.Hpk k r := hs
  have hx' : xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r := hx
  calc (s * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (s * x) = xᴴ * (sᴴ * Formalism.QuantumDeterminants.Hpk k r * s) * x := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hs', hx']

theorem conjTranspose_inv_mul_conjTranspose {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : IsUnit P.det) : P⁻¹ᴴ * Pᴴ = 1 := by
  rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv P hP, Matrix.conjTranspose_one]

theorem cayley_conj_mem_unitary_group {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {g : Mat k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : P * g * P⁻¹ ∈ UJset ε := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hJ : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.2
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  show inUJ ε (P * g * P⁻¹)
  rw [← mir_inUJ_iff]
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  have e1 := conjTranspose_inv_mul_conjTranspose P hd
  have e2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = P⁻¹ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = P⁻¹ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hJ, hg']
    _ = (P⁻¹ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]

theorem cayley_conj_inv_mem_hermitian_group {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {Y : Mat k r} (hY : Y ∈ UJset ε) : P⁻¹ * Y * P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hJ : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.2
  have hY' : Yᴴ * Formalism.REAL.Jm ε * Y = Formalism.REAL.Jm ε := (mir_inUJ_iff ε Y).2 hY
  show (P⁻¹ * Y * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (P⁻¹ * Y * P) = Formalism.QuantumDeterminants.Hpk k r
  have e1 := conjTranspose_inv_mul_conjTranspose P hd
  have e2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  rw [← hJ]
  calc (P⁻¹ * Y * P)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * (P⁻¹ * Y * P)
      = Pᴴ * (Yᴴ * ((P⁻¹ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹)) * Y) * P := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * Formalism.REAL.Jm ε * P := by
        rw [e1, e2, Matrix.one_mul, Matrix.mul_one, hY']

theorem ae_mem_unitary_nilpotent_product {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  haveI : SigmaFinite μN := hN.1
  rw [ae_iff]
  have hsub : {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r |
      ¬(Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r)} ⊆
      ({x | Matrix.of x ∉ Formalism.QuantumDeterminants.UWset k r z} ×ˢ Set.univ) ∪
        (Set.univ ×ˢ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) := by
    intro p hp
    simp only [Set.mem_ofPred_eq, not_and_or] at hp
    rcases hp with hp | hp
    · exact Or.inl ⟨hp, trivial⟩
    · exact Or.inr ⟨trivial, hp⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.prod_prod, hW.2.2.1, zero_mul]
  · rw [Measure.prod_prod, hN.2.2.1, mul_zero]

theorem finB_frob_eq {k r : ℕ} (g : Mat k r) : frob g = Formalism.FourierDecayAlt.B.gN g := by
  unfold frob Formalism.FourierDecayAlt.B.gN
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq]

theorem finB_Jct {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

theorem finB_inv_eq {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {g : Mat k r} (hg : g ∈ UJset ε) :
    g⁻¹ = Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε := by
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := (mir_inUJ_iff ε g).2 hg
  apply Matrix.inv_eq_left_inv
  calc Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, signature_matrix_sq]

theorem finB_mul_inv {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {g : Mat k r} (hg : g ∈ UJset ε) :
    g * g⁻¹ = 1 := by
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := (mir_inUJ_iff ε g).2 hg
  have h1 : g⁻¹ * g = 1 := by
    rw [finB_inv_eq hg]
    calc Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, signature_matrix_sq]
  exact mul_eq_one_comm.mp h1

theorem finB_frob_inv {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {g : Mat k r} (hg : g ∈ UJset ε) :
    frob g⁻¹ = frob g := by
  have hJ : (Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε = 1 := by rw [finB_Jct, signature_matrix_sq]
  rw [finB_frob_eq, finB_frob_eq, finB_inv_eq hg, S0.DecA.gN_right _ hJ, S0.DecA.gN_left _ hJ, S0.DecA.gN_conjT]

theorem finB_frob_mul_le {k r : ℕ} (a b : Mat k r) : frob (a * b) ≤ frob a * frob b := by
  rw [finB_frob_eq, finB_frob_eq, finB_frob_eq]
  exact S0.DecA.gN_mul_le' a b

theorem finB_one_le {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {g : Mat k r} (hg : g ∈ UJset ε) :
    1 ≤ frob g := by
  have h0 : (1 : ℝ) ≤ frob (1 : Mat k r) := by
    rw [finB_frob_eq]
    have := S0.DecA.gN_entry (1 : Mat k r) ⟨0, by omega⟩ ⟨0, by omega⟩
    simpa using this
  have h1 : frob (1 : Mat k r) ≤ frob g * frob g := by
    have := finB_frob_mul_le g g⁻¹
    rwa [finB_mul_inv hg, finB_frob_inv hg] at this
  nlinarith [Real.sqrt_nonneg (∑ i, ∑ j, ‖g i j‖ ^ 2), show frob g = Real.sqrt (∑ i, ∑ j, ‖g i j‖ ^ 2) from rfl]

theorem finB_le_mul {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Y : Mat k r} (hY : Y ∈ UJset ε) (g : Mat k r) :
    frob g ≤ frob Y * frob (Y⁻¹ * g) := by
  have := finB_frob_mul_le Y (Y⁻¹ * g)
  rwa [← Matrix.mul_assoc, finB_mul_inv hY, Matrix.one_mul] at this

theorem finB_intJ {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (hq : 1 ≤ S7.q0 ε) (b : ℝ)
    (hb : 2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) < b) :
    Integrable (fun y : Formalism.REAL.UJ ε => frob (Formalism.MainNotions.S.umat y) ^ (-b)) (Formalism.REAL.muG ε) := by
  refine integrable_muG_of_haar ε (fun g => frob g ^ (-b)) (fun ν _ => ?_)
  obtain ⟨s, hs⟩ := S7.exists_signVG ε
  have hb0 : 0 ≤ b := by
    have : (0 : ℝ) ≤ 2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := by positivity
    linarith
  have hmem : ∀ g : S7.UJ ε, S7.toM g ∈ UJset ε := fun g => unitary_matrix_mem_set ε g
  have hone : ∀ g : S7.UJ ε, 1 ≤ frob (S7.toM g) := fun g => finB_one_le (hmem g)
  have hfr : ∀ g : Mat k r, frob g = Real.sqrt (S7.hs g) := fun g => rfl
  have hcont : Continuous (fun g : S7.UJ ε => frob (S7.toM g) ^ (-b)) := by
    have h1 : Continuous (fun g : S7.UJ ε => frob (S7.toM g)) := by
      have : Continuous (fun g : Mat k r => frob g) := by
        simp only [hfr]; exact Real.continuous_sqrt.comp S7.hs_contVG
      exact this.comp (S7.continuous_toM ε)
    exact h1.rpow_const (fun g => Or.inl (by linarith [hone g]))
  refine S7.integrable_of_decayVG ε s ν _ hcont.aestronglyMeasurable 1 (fun g _ => ?_) b ?_ (fun g hg => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hone g]) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (hone g) (by linarith)
  · rw [hs]; push_cast at hb ⊢; linarith
  · set H := S7.hs (S7.toM g) with hH
    have hn : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
    have hn0 : (0 : ℝ) < ((2 * r + k + 1 : ℕ) : ℝ) := by linarith
    have hH0 : 0 < H := by
      have : (0 : ℝ) < ((2 * r + k + 1 : ℕ) : ℝ) * Real.exp 2 + 1 := by positivity
      linarith
    have hq0 : 0 < H / ((2 * r + k + 1 : ℕ) : ℝ) := div_pos hH0 hn0
    refine ⟨Real.log (H / ((2 * r + k + 1 : ℕ) : ℝ)) / 2, ?_, ?_⟩
    · rw [show 2 * (Real.log (H / ((2 * r + k + 1 : ℕ) : ℝ)) / 2) = Real.log (H / ((2 * r + k + 1 : ℕ) : ℝ)) by ring,
        Real.exp_log hq0, mul_div_cancel₀ _ hn0.ne']
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hone g]) _), one_mul, hfr,
        ← hH, Real.sqrt_eq_rpow, ← Real.rpow_mul hH0.le]
      have e : -(b * (Real.log (H / ((2 * r + k + 1 : ℕ) : ℝ)) / 2)) =
          Real.log (H / ((2 * r + k + 1 : ℕ) : ℝ)) * (-(b / 2)) := by ring
      rw [e, ← Real.rpow_def_of_pos hq0, Real.div_rpow hH0.le hn0.le, show (1 / 2 : ℝ) * -b = -(b / 2) by ring]
      have h1 : (1 : ℝ) ≤ (((2 * r + k + 1 : ℕ) : ℝ) ^ (-(b / 2)))⁻¹ := by
        rw [Real.rpow_neg hn0.le, inv_inv]
        exact Real.one_le_rpow hn (by linarith)
      rw [div_eq_mul_inv]
      have h2 : 0 ≤ H ^ (-(b / 2)) := Real.rpow_nonneg hH0.le _
      exact le_mul_of_one_le_right h2 h1

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem finB_umat_inv {n : ℕ} {ε : Fin n → Bool} (y : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.umat y⁻¹ = (Formalism.MainNotions.S.umat y)⁻¹ := by
  show ((y⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val = _
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]

theorem finB_umat_mul {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.umat (a * b) = Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b := rfl

theorem finB_intJ_shift {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (b : ℝ)
    (hI : Integrable (fun y : Formalism.REAL.UJ ε => frob (Formalism.MainNotions.S.umat y) ^ (-b)) (Formalism.REAL.muG ε))
    (γ : Formalism.REAL.UJ ε) :
    Integrable (fun y : Formalism.REAL.UJ ε => frob ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat γ) ^ (-b)) (Formalism.REAL.muG ε) ∧
    ∫ y, frob ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat γ) ^ (-b) ∂(Formalism.REAL.muG ε) =
      ∫ y, frob (Formalism.MainNotions.S.umat y) ^ (-b) ∂(Formalism.REAL.muG ε) := by
  have e : (fun y : Formalism.REAL.UJ ε => frob ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat γ) ^ (-b)) =
      fun y => (fun y' : Formalism.REAL.UJ ε => frob (Formalism.MainNotions.S.umat y') ^ (-b)) (γ⁻¹ * y) := by
    funext y
    have h1 : (Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat γ = (Formalism.MainNotions.S.umat (γ⁻¹ * y))⁻¹ := by
      rw [← finB_umat_inv, ← finB_umat_inv, ← finB_umat_mul, _root_.mul_inv_rev, inv_inv]
    simp only
    rw [h1, finB_frob_inv (unitary_matrix_mem_set ε _)]
  rw [e]
  exact ⟨hI.comp_mul_left γ⁻¹,
    integral_mul_left_eq_self (μ := Formalism.REAL.muG ε) (fun y' : Formalism.REAL.UJ ε => frob (Formalism.MainNotions.S.umat y') ^ (-b)) γ⁻¹⟩

theorem finB_pair {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} (β : ℝ) (hβ : 0 ≤ β) {Y g : Mat k r}
    (hY : Y ∈ UJset ε) (hg : g ∈ UJset ε) (hYg : Y⁻¹ * g ∈ UJset ε) :
    frob Y ^ (-β) * frob (Y⁻¹ * g) ^ (-β) ≤
      frob g ^ (-(β / 4)) * (frob Y ^ (-(β / 2)) + frob (Y⁻¹ * g) ^ (-(β / 2))) := by
  have hA := finB_one_le hY
  have hB := finB_one_le hYg
  have hG := finB_one_le hg
  have hle := finB_le_mul hY g
  have hAh : 0 ≤ frob Y ^ (-(β / 2)) := Real.rpow_nonneg (by linarith) _
  have hBh : 0 ≤ frob (Y⁻¹ * g) ^ (-(β / 2)) := Real.rpow_nonneg (by linarith) _
  have hGq : 0 ≤ frob g ^ (-(β / 4)) := Real.rpow_nonneg (by linarith) _
  rcases le_total (frob Y) (frob (Y⁻¹ * g)) with h | h
  · calc _ ≤ frob g ^ (-(β / 4)) * frob (Y⁻¹ * g) ^ (-(β / 2)) :=
          S0.DecA.pb_real β _ _ _ hβ hA hB (by linarith) (le_of_le_of_eq hle (mul_comm _ _)) h
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hAh) hGq
  · have := S0.DecA.pb_real β (frob (Y⁻¹ * g)) (frob Y) (frob g) hβ hB hA (by linarith) hle h
    rw [mul_comm] at this
    calc _ ≤ frob g ^ (-(β / 4)) * frob Y ^ (-(β / 2)) := this
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hBh) hGq

theorem finB_one_UH (k r : ℕ) : (1 : Mat k r) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  show (1 : Mat k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

theorem finB_frob_conj_ge {k r : ℕ} {P : Mat k r} (hP : IsUnit P.det) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : Mat k r, c * Formalism.FourierDecayAlt.B.gN g ≤ frob (P * g * P⁻¹) := by
  letI : NormedAddCommGroup (Mat k r) := Matrix.frobeniusNormedAddCommGroup
  have hg : ∀ A : Mat k r, Formalism.FourierDecayAlt.B.gN A = ‖A‖ := by
    intro A
    rw [Matrix.frobenius_norm_def, Formalism.FourierDecayAlt.B.gN, Real.sqrt_eq_rpow]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_norm_sq, Real.rpow_two]
  have hf : ∀ A : Mat k r, frob A = ‖A‖ := by
    intro A
    rw [Matrix.frobenius_norm_def, frob, Real.sqrt_eq_rpow]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Real.rpow_two]
  refine ⟨1 / (‖P⁻¹‖ * ‖P‖ + 1), by positivity, fun g => ?_⟩
  have e : g = P⁻¹ * (P * g * P⁻¹) * P := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hP, Matrix.nonsing_inv_mul _ hP,
      Matrix.mul_one]
  have h1 : ‖g‖ ≤ ‖P⁻¹‖ * ‖P * g * P⁻¹‖ * ‖P‖ := by
    conv_lhs => rw [e]
    calc ‖P⁻¹ * (P * g * P⁻¹) * P‖ ≤ ‖P⁻¹ * (P * g * P⁻¹)‖ * ‖P‖ := Matrix.frobenius_norm_mul _ _
      _ ≤ ‖P⁻¹‖ * ‖P * g * P⁻¹‖ * ‖P‖ :=
        mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _)
  rw [hg, hf, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (P * g * P⁻¹), norm_nonneg P⁻¹, norm_nonneg P,
    mul_nonneg (norm_nonneg P⁻¹) (norm_nonneg P)]

theorem finB_intS (hIS : S0.IntSStatement) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (x : Mat k r) (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (b : ℝ) (hb : S0.bS k r < b) :
    Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (-b)) (μW.prod μN) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hb0 : 0 ≤ b := by
    have : 0 ≤ S0.bS k r := by unfold S0.bS S0.nS; positivity
    linarith
  obtain ⟨c0, hc0, hcg⟩ := finB_frob_conj_ge hd
  have h1 := hIS k r z μW μN hz hT hW hN 1 (finB_one_UH k r) x hx b hb
  simp only [inv_one, Matrix.one_mul] at h1
  have hae := ae_mem_unitary_nilpotent_product z μW μN hW hN
  have hof : Continuous (fun g : Formalism.QuantumDeterminants.Mt k r => (Matrix.of g : Mat k r)) := S0.Dec.of_cont k r
  have hfc : Continuous (fun M : Mat k r => frob M) := by
    have : (fun M : Mat k r => frob M) = fun M => Formalism.FourierDecayAlt.B.gN M := funext finB_frob_eq
    rw [this]; exact S0.Dec.gN_cont k r
  have hgc : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) :=
    (continuous_const.matrix_mul (((hof.comp continuous_fst).matrix_mul (hof.comp continuous_snd)).matrix_mul
      continuous_const)).matrix_mul continuous_const
  refine Integrable.mono' (h1.const_mul (c0 ^ (-b))) ((hfc.comp hgc).measurable.pow_const _).aestronglyMeasurable ?_
  filter_upwards [hae] with p hp
  have hM : Matrix.of p.1 * Matrix.of p.2 * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    unitary_hermitian_form_mul_mem (unitary_hermitian_form_mul_mem hp.1.1 hp.2.1) hx
  have hg1 := S0.DecA.one_le_gN' hM
  have hge := hcg (Matrix.of p.1 * Matrix.of p.2 * x)
  have hpos : 0 < c0 * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * x) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  calc frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (-b)
      ≤ (c0 * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * x)) ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos hpos hge (by linarith)
    _ = c0 ^ (-b) * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * x) ^ (-b) :=
        Real.mul_rpow hc0.le (by linarith)

theorem finB_UJ_mul {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {a b : Mat k r} (ha : a ∈ UJset ε)
    (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := (mir_inUJ_iff ε a).2 ha
  have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := (mir_inUJ_iff ε b).2 hb
  show inUJ ε (a * b)
  rw [← mir_inUJ_iff]
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hb']

theorem finB_UJ_closed {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) : IsClosed (UJset ε : Set (Mat k r)) :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem finB_gap {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {h : ℝ} (hgap : StepGap ε r h) :
    1 ≤ S7.q0 ε ∧ 0 < h ∧
      4 * max (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) <
        aExp ε h - 1 := by
  obtain ⟨h1, h2⟩ := hgap
  have e : min (pOf ε : ℝ) (qOf ε : ℝ) = (S7.q0 ε : ℝ) := by unfold S7.q0; push_cast; rfl
  rw [e] at h2
  have hn : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmax0 : 0 ≤ max (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) :=
    le_max_of_le_left (by positivity)
  refine ⟨?_, ?_, h2⟩
  · by_contra hq
    have hq0 : S7.q0 ε = 0 := by omega
    rw [hq0] at h2
    simp at h2
    have : (0 : ℝ) ≤ max 0 (2 * (r : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1) ^ 2) := le_max_left _ _
    linarith
  · have : 0 ≤ 3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2 := by positivity
    have := le_max_left (3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2) (1 + ((2 * r + k + 1 : ℕ) : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
    linarith

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

def finKer {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T' : S7.KType ε Λ)
    (μ' : Fin (2 * r + k + 1) → ℤ) (v₁ v₂ : T'.V) (P : Mat k r) (x : Mat k r) (y : Mat k r)
    (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) : ℂ :=
  ⟪v₂, S7.PsiM T' μ' (y⁻¹ * (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹)) v₁⟫_ℂ

theorem finB_frob_nonneg {k r : ℕ} (g : Mat k r) : 0 ≤ frob g := Real.sqrt_nonneg _

theorem product_bound_three_factors (A B X p1 p2 Φ C0 C1 V : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hX : 0 ≤ X)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hV : 0 ≤ V) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2)
    (h1 : A ≤ C0 * p1) (h2 : B ≤ C1 * V * p2) (h3 : p1 * p2 ≤ Φ) :
    A * (B * X) ≤ C0 * C1 * V * X * Φ := by
  have e1 : A * (B * X) ≤ (C0 * p1) * ((C1 * V * p2) * X) :=
    mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 hX) (mul_nonneg hB hX) (by positivity)
  have e2 : (C0 * p1) * ((C1 * V * p2) * X) = C0 * C1 * V * X * (p1 * p2) := by ring
  have e3 : C0 * C1 * V * X * (p1 * p2) ≤ C0 * C1 * V * X * Φ :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith

theorem finFub_int' (hIS : S0.IntSStatement) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ)
    (lam' : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r) (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hB : IsBData z c u π μW μN)
    (hgap : StepGap ε r h) (hlam : S7.IsHCParam lam')
    (hgl : GapAtLeast ε lam' h) (T' : S7.KType ε (lowK ε lam')) (μ' : Fin (2 * r + k + 1) → ℤ)
    (hμ : S7.IsMu lam' μ') (v₁ v₂ : T'.V) (ξ : Vp) (F : Mat k r → ℂ) (C : ℝ)
    (hFc : ContinuousOn F (UJset ε)) (hFb : ∀ g ∈ UJset ε, ‖F g‖ ≤ C * frob g ^ (1 - aExp ε h))
    (x : Mat k r) (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    Integrable (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      F (Formalism.MainNotions.S.umat q.1) • (finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat q.1) q.2 •
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of q.2.1) (Matrix.of q.2.2) ξ))
      ((Formalism.REAL.muG ε).prod (μW.prod μN)) := by
  obtain ⟨hz, hT, -, hπW, hHW, hHN⟩ := hB
  haveI : SigmaFinite μW := hHW.1
  haveI : SigmaFinite μN := hHN.1
  obtain ⟨hq0, hh, hmax⟩ := finB_gap hgap
  set a := aExp ε h with ha
  set β := a - 1 with hβ
  have hm1 := le_max_left (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2)
  have hm2 := le_max_right (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2)
  have hpos1 : (0 : ℝ) ≤ 2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := by positivity
  have hβ0 : 0 ≤ β := by linarith
  have hIJ := finB_intJ ε hq0 (β / 2) (by linarith)
  have hIS' := finB_intS hIS hP z μW μN hz hT hHW hHN x hx (β / 4) (by unfold S0.bS S0.nS; linarith)
  obtain ⟨C', hC'⟩ := S0.DecDeriv.psiM_frob_dec ε lam' h T' μ' hlam hgl hh hq0 hμ
  have hπU := hcTypeW_uRep k r z u Vp π hz hT hπW
  have hPae := ae_mem_unitary_nilpotent_product z μW μN hHW hHN
  have hQae : ∀ᵐ q ∂((Formalism.REAL.muG ε).prod (μW.prod μN)),
      Matrix.of q.2.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of q.2.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae hPae
  have hgpJ : ∀ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r →
        P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ ∈ UJset ε := fun p hp =>
    cayley_conj_mem_unitary_group hP (unitary_hermitian_form_mul_mem (unitary_hermitian_form_mul_mem hp.1.1 hp.2.1) hx)

  have hof := S0.Dec.of_cont k r
  have hfc : Continuous (fun M : Mat k r => frob M) := by
    have : (fun M : Mat k r => frob M) = fun M => Formalism.FourierDecayAlt.B.gN M := funext finB_frob_eq
    rw [this]; exact S0.Dec.gN_cont k r
  have hgpc : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) :=
    (continuous_const.matrix_mul (((hof.comp continuous_fst).matrix_mul (hof.comp continuous_snd)).matrix_mul
      continuous_const)).matrix_mul continuous_const
  have humc := continuous_unitary_matrix ε
  have hinvc : Continuous (fun y : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.umat y)⁻¹) := by
    have : (fun y : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.umat y)⁻¹) = fun y => Formalism.MainNotions.S.umat y⁻¹ :=
      funext fun y => (finB_umat_inv y).symm
    rw [this]; exact humc.comp continuous_inv
  have hmc : Continuous (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) :=
    (hinvc.comp continuous_fst).matrix_mul (hgpc.comp continuous_snd)

  have hT2m : Measurable (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      frob (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ^ (-(β / 4)) *
        frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-(β / 2))) :=
    ((hfc.comp (hgpc.comp continuous_snd)).measurable.pow_const _).mul ((hfc.comp hmc).measurable.pow_const _)
  have hT1 : Integrable (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      frob (Formalism.MainNotions.S.umat q.1) ^ (-(β / 2)) * frob (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ^ (-(β / 4)))
      ((Formalism.REAL.muG ε).prod (μW.prod μN)) := hIJ.mul_prod hIS'
  have hT2 : Integrable (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      frob (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ^ (-(β / 4)) *
        frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-(β / 2)))
      ((Formalism.REAL.muG ε).prod (μW.prod μN)) := by
    rw [integrable_prod_iff' hT2m.aestronglyMeasurable]
    constructor
    · filter_upwards [hPae] with p hp
      obtain ⟨γ, hγ⟩ := exists_unitary_preimage ε (hgpJ p hp)
      have h1 := (finB_intJ_shift ε (β / 2) hIJ γ).1
      rw [hγ] at h1
      exact h1.const_mul _
    · refine (hIS'.mul_const (∫ y, frob (Formalism.MainNotions.S.umat y) ^ (-(β / 2)) ∂(Formalism.REAL.muG ε))).congr ?_
      filter_upwards [hPae] with p hp
      obtain ⟨γ, hγ⟩ := exists_unitary_preimage ε (hgpJ p hp)
      have h2 := (finB_intJ_shift ε (β / 2) hIJ γ).2
      rw [hγ] at h2
      have hnn : ∀ y : Formalism.REAL.UJ ε,
          ‖frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (-(β / 4)) *
            frob ((Formalism.MainNotions.S.umat y)⁻¹ * (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹)) ^ (-(β / 2))‖ =
          frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (-(β / 4)) *
            frob ((Formalism.MainNotions.S.umat y)⁻¹ * (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹)) ^ (-(β / 2)) := by
        intro y
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (finB_frob_nonneg _) _)
          (Real.rpow_nonneg (finB_frob_nonneg _) _))]
      simp only [hnn]
      rw [integral_const_mul, h2]
  have hΦ : Integrable (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      frob (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ^ (-(β / 4)) *
        (frob (Formalism.MainNotions.S.umat q.1) ^ (-(β / 2)) +
          frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-(β / 2))))
      ((Formalism.REAL.muG ε).prod (μW.prod μN)) := by
    refine (hT1.add hT2).congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.add_apply]; ring
  set S3 : Set (Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) :=
    {q | Matrix.of q.2.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹ ∈ UJset ε}
    with hS3
  have hScl : IsClosed S3 :=
    ((S0.Dec.UW_closed k r z).preimage (hof.comp (continuous_fst.comp continuous_snd))).inter
      ((finB_UJ_closed ε).preimage (hgpc.comp continuous_snd))
  have hSae : ∀ᵐ q ∂((Formalism.REAL.muG ε).prod (μW.prod μN)), q ∈ S3 := by
    filter_upwards [hQae] with q hq
    exact ⟨hq.1, hgpJ q.2 hq⟩
  have hE1 : ContinuousOn (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      F (Formalism.MainNotions.S.umat q.1)) S3 :=
    (hFc.comp_continuous (humc.comp continuous_fst) (fun q => unitary_matrix_mem_set ε _)).continuousOn
  have hE2 : ContinuousOn (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat q.1) q.2) S3 := by
    unfold finKer
    have hmaps : Set.MapsTo (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) S3 {g | inUJ ε g} := by
      intro q hq
      show (Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ∈ UJset ε
      rw [← finB_umat_inv]
      exact finB_UJ_mul (unitary_matrix_mem_set ε _) hq.2
    have h := (S7.psiM_continuousOn T' μ' hμ).comp hmc.continuousOn hmaps
    exact continuousOn_const.inner (h.clm_apply continuousOn_const)
  have hE3 : ContinuousOn (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of q.2.1) (Matrix.of q.2.2) ξ) S3 := by
    show ContinuousOn (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      star (Formalism.MainNotions.S.psiGen k r z c (Matrix.of q.2.2)) • π (Matrix.of q.2.1)⁻¹ ξ) S3
    have hq21 : Continuous (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) => Matrix.of q.2.1) :=
      hof.comp (continuous_fst.comp continuous_snd)
    have hinvc' : ContinuousOn (fun q : Formalism.REAL.UJ ε × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of q.2.1)⁻¹) S3 :=
      (((continuous_const.matrix_mul hq21.matrix_conjTranspose).matrix_mul continuous_const).continuousOn).congr
        (fun q hq => S0.DecA.inv_eq hq.1.1)
    have h := (hπU.2.2 ξ).comp hinvc' (fun q hq => S0.Dec.UW_inv_mem hq.1)
    exact (continuous_star.comp ((S0.Dec.psiGen_cont k r z c).comp
      (hof.comp (continuous_snd.comp continuous_snd)))).continuousOn.smul h
  refine Integrable.mono' (hΦ.const_mul (max C 0 * max C' 0 * (‖v₁‖ * ‖v₂‖) * ‖ξ‖)) ?_ ?_
  · rw [← Measure.restrict_eq_self_of_ae_mem hSae]
    exact (hE1.smul (hE2.smul hE3)).aestronglyMeasurable hScl.measurableSet
  filter_upwards [hQae] with q hq
  have hY := unitary_matrix_mem_set ε q.1
  have hg := hgpJ q.2 hq
  have hYg : (Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹) ∈ UJset ε := by
    rw [← finB_umat_inv]; exact finB_UJ_mul (unitary_matrix_mem_set ε _) hg
  have hψ : ‖Formalism.MainNotions.S.psiGen k r z c (Matrix.of q.2.2)‖ = 1 := by
    unfold Formalism.MainNotions.S.psiGen; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hπ' : ‖π (Matrix.of q.2.1)⁻¹ ξ‖ = ‖ξ‖ := hπU.2.1 _ (S0.Dec.UW_inv_mem hq.1) ξ
  have hchi : ‖chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of q.2.1) (Matrix.of q.2.2) ξ‖ = ‖ξ‖ := by
    simp only [chiInv, norm_smul, norm_star, hψ, hπ', one_mul]
  have hF1 : ‖F (Formalism.MainNotions.S.umat q.1)‖ ≤ max C 0 * frob (Formalism.MainNotions.S.umat q.1) ^ (-β) := by
    have h1 := hFb _ hY
    rw [show 1 - a = -β by rw [hβ]; ring] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (finB_frob_nonneg _) _))
  have hK1 : ‖finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat q.1) q.2‖ ≤ max C' 0 * (‖v₁‖ * ‖v₂‖) *
      frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-β) := by
    unfold finKer
    have h1 := hC' _ hYg
    have ea : h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))) = a := rfl
    rw [ea] at h1
    have hle : frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-a) ≤
        frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-β) :=
      Real.rpow_le_rpow_of_exponent_le (finB_one_le hYg) (by rw [hβ]; linarith)
    have h2 : ‖S7.PsiM T' μ' ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹))‖ ≤
        max C' 0 * frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-β) :=
      h1.trans (mul_le_mul (le_max_left _ _) hle (Real.rpow_nonneg (finB_frob_nonneg _) _) (le_max_right _ _))
    calc _ ≤ ‖v₂‖ * ‖S7.PsiM T' μ' ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) v₁‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖v₂‖ * (‖S7.PsiM T' μ' ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹))‖ * ‖v₁‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖v₂‖ * ((max C' 0 * frob ((Formalism.MainNotions.S.umat q.1)⁻¹ * (P * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * P⁻¹)) ^ (-β)) * ‖v₁‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hpair := finB_pair β hβ0 hY hg hYg
  rw [norm_smul, norm_smul, hchi]
  exact product_bound_three_factors _ _ _ _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (le_max_right _ _)
    (le_max_right _ _) (by positivity) (Real.rpow_nonneg (finB_frob_nonneg _) _)
    (Real.rpow_nonneg (finB_frob_nonneg _) _) hF1 hK1 hpair

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem finFub (hIS : S0.IntSStatement) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ) (lam' : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r) (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hB : IsBData z c u π μW μN)
    (hp : pOf ε = k + r) (hq : qOf ε = r + 1) (hgap : StepGap ε r h) (hlam : S7.IsHCParam lam')
    (hgl : GapAtLeast ε lam' h) (T' : S7.KType ε (lowK ε lam')) (μ' : Fin (2 * r + k + 1) → ℤ)
    (hμ : S7.IsMu lam' μ') (v₁ v₂ : T'.V) (ξ : Vp) (F : Mat k r → ℂ) (C : ℝ)
    (hFc : ContinuousOn F (UJset ε)) (hFb : ∀ g ∈ UJset ε, ‖F g‖ ≤ C * frob g ^ (1 - aExp ε h))
    (hrep : ∀ x ∈ UJset ε, F x = ∫ y, F (Formalism.MainNotions.S.umat y) *
        ⟪v₂, S7.PsiM T' μ' ((Formalism.MainNotions.S.umat y)⁻¹ * x) v₁⟫_ℂ ∂(Formalism.REAL.muG ε))
    (x : Mat k r) (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hne : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x ≠ 0) :
    ∃ x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      aaFun T' μ' P μW μN (Formalism.MainNotions.S.psiGen k r z c) π v₁ v₂ ξ x₀ x ≠ 0 := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hHW := hB.2.2.2.2.1
  have hHN := hB.2.2.2.2.2
  haveI : SigmaFinite μW := hHW.1
  haveI : SigmaFinite μN := hHN.1
  let integrand (y : Formalism.REAL.UJ ε)
      (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) : Vp :=
    F (Formalism.MainNotions.S.umat y) • (finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat y) p •
      chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ)
  have hint : Integrable (Function.uncurry integrand) ((Formalism.REAL.muG ε).prod (μW.prod μN)) :=
    finFub_int' hIS k r ε u lam' h z c Vp π μW μN P hP hB hgap hlam hgl T' μ' hμ v₁ v₂ ξ F C hFc hFb x hx
  by_contra hall
  push Not at hall
  apply hne
  have hae := ae_mem_unitary_nilpotent_product z μW μN hHW hHN
  have step1 : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x =
      ∫ p, ∫ y, integrand y p ∂(Formalism.REAL.muG ε) ∂(μW.prod μN) := by
    delta per sInt
    apply integral_congr_ae
    filter_upwards [hae] with p hp'
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      unitary_hermitian_form_mul_mem hp'.1.1 hp'.2.1
    have hJ := cayley_conj_mem_unitary_group hP (unitary_hermitian_form_mul_mem hs hx)
    show F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) • _ = _
    rw [hrep _ hJ, ← integral_smul_const]
    congr 1
    funext y
    exact mul_smul _ _ _
  rw [step1, ← integral_integral_swap hint]
  have hz : ∀ y, ∫ p, integrand y p ∂(μW.prod μN) = 0 := by
    intro y
    dsimp only [integrand]
    rw [integral_smul]
    have hy := unitary_matrix_mem_set ε y
    have h0 := hall _ (cayley_conj_inv_mem_hermitian_group hP hy)
    unfold aaFun sInt psiCoef at h0
    have hfun : (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
        finKer T' μ' v₁ v₂ P x (Formalism.MainNotions.S.umat y) p •
          chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) =
        fun p => ⟪v₂, S7.PsiM T' μ' (P * ((P⁻¹ * Formalism.MainNotions.S.umat y * P)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) * P⁻¹) v₁⟫_ℂ •
          chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ := by
      funext p
      delta finKer
      rw [conj_inv_mul_conj _ _ _ hd]
    rw [hfun, h0, smul_zero]
  simp only [hz, integral_zero]

end ReciprocityTheory.ChartRestriction.DS.Lap
