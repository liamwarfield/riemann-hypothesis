module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.QRHaar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.ChartWR
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.LintegralGaussTri
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.GaussB
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.GaussA
noncomputable section

section
open Finset MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS

theorem gaussA_lint_pi_ofReal {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : ∀ i, E i → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (h0 : ∀ i x, 0 ≤ f i x) :
    ∫⁻ x, ENNReal.ofReal (∏ i, f i (x i)) ∂(Measure.pi μ) = ∏ i, ENNReal.ofReal (∫ x, f i x ∂(μ i)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod_dep hf)
    (ae_of_all _ fun x => Finset.prod_nonneg fun i _ => h0 i _), integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (h0 i))]

theorem gaussA_real_int : Integrable (fun x : ℝ => Real.exp (-x ^ 2)) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

theorem gaussA_cfun_eq : (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) =
    (fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2)) ∘ Complex.measurableEquivRealProd := by
  funext z
  simp only [Function.comp_apply, Complex.measurableEquivRealProd_apply, ← Real.exp_add]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem gaussA_cint : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) := by
  rw [gaussA_cfun_eq, Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding]
  exact Integrable.mul_prod gaussA_real_int gaussA_real_int

theorem gaussA_cintegral : ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := Complex.volume_preserving_equiv_real_prod.integral_comp
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2))
  have h2 : ∫ p : ℝ × ℝ, Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2) = Real.pi := by
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      integral_prod_mul (fun x : ℝ => Real.exp (-x ^ 2)) (fun x : ℝ => Real.exp (-x ^ 2))]
    have hg : ∫ x : ℝ, Real.exp (-x ^ 2) = Real.sqrt Real.pi := by
      simpa using integral_gaussian 1
    rw [hg, Real.mul_self_sqrt Real.pi_pos.le]
  rw [gaussA_cfun_eq]
  simpa [Function.comp_def] using h.trans h2

theorem gaussA_rad (a : ℕ) :
    ∫ r in Ioi (0:ℝ), Real.exp (-r ^ 2) * |r| ^ (2 * a + 1) = (a.factorial : ℝ) / 2 := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := ((2 * a + 1 : ℕ) : ℝ)) two_pos (by have := (Nat.cast_nonneg (2*a+1) : (0:ℝ) ≤ _); linarith)
  have hc : ∫ r in Ioi (0:ℝ), Real.exp (-r ^ 2) * |r| ^ (2 * a + 1) =
      ∫ x in Ioi (0:ℝ), x ^ (((2 * a + 1 : ℕ) : ℝ)) * Real.exp (-x ^ (2:ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Real.rpow_natCast, abs_of_pos (mem_Ioi.mp hx)]
    rw [show x ^ (2:ℝ) = x ^ (2:ℕ) by exact_mod_cast Real.rpow_natCast x 2, mul_comm]
  rw [hc, h]
  have : ((((2 * a + 1 : ℕ) : ℝ)) + 1) / 2 = (a : ℝ) + 1 := by push_cast; ring
  rw [this, Real.Gamma_nat_eq_factorial]
  ring

theorem gaussA_rad_int (a : ℕ) :
    IntegrableOn (fun r : ℝ => Real.exp (-r ^ 2) * |r| ^ (2 * a + 1)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := ((2 * a + 1 : ℕ) : ℝ)) (by have := (Nat.cast_nonneg (2*a+1) : (0:ℝ) ≤ _); linarith)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, abs_of_pos (mem_Ioi.mp hx)]
  ring_nf

end ReciprocityTheory.ChartRestriction.DS

end

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem gaussB_hs_eq_re_trace (M : Matrix (Fin N) (Fin N) ℂ) : hs M = (trace (Mᴴ * M)).re := by
  simp only [hs, trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

theorem gaussB_hs_unitary_mul (k : UNgrp N) (M : Matrix (Fin N) (Fin N) ℂ) : hs (toM k * M) = hs M := by
  have hk : inUJ (fun _ : Fin N => true) (toM k) := k.2
  have hJ : Jm (fun _ : Fin N => true) = 1 := by
    unfold Jm; simp
  unfold inUJ at hk
  rw [hJ, Matrix.mul_one] at hk
  rw [gaussB_hs_eq_re_trace, gaussB_hs_eq_re_trace, conjTranspose_mul,
    show Mᴴ * (toM k)ᴴ * (toM k * M) = Mᴴ * ((toM k)ᴴ * toM k) * M by simp only [Matrix.mul_assoc],
    hk, Matrix.mul_one]

theorem gaussB_card_lt : Fintype.card {ab : Fin N × Fin N // ab.1 < ab.2} = N * (N - 1) / 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
  have h1 : ∀ i : Fin N, (∑ j : Fin N, if i < j then 1 else 0) = N - 1 - i := by
    intro i
    rw [← Finset.card_filter, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  simp_rw [h1]
  have h2 : (∑ i : Fin N, (N - 1 - (i : ℕ))) = ∑ i : Fin N, (i : ℕ) := by
    refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  rw [h2, Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

theorem gaussB_prod_fact :
    (∏ j : Fin N, (((N - 1 - (j : ℕ)).factorial : ℝ) / 2)) = (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N := by
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun i => (i.factorial : ℝ)) N]
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  exact congrArg (fun m : ℕ => ((m.factorial : ℕ) : ℝ)) (by omega)

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem gaussC_mat :
    ∫⁻ Z : Fin N → Fin N → ℂ, ENNReal.ofReal (Real.exp (-hs (Matrix.of Z))) =
      ENNReal.ofReal (Real.pi ^ (N ^ 2)) := by
  have hpt : ∀ Z : Fin N → Fin N → ℂ, ENNReal.ofReal (Real.exp (-hs (Matrix.of Z))) =
      ENNReal.ofReal (∏ i, (fun (_ : Fin N) (row : Fin N → ℂ) => ∏ j, Real.exp (-‖row j‖ ^ 2)) i (Z i)) := by
    intro Z
    congr 1
    simp only [hs, Matrix.of_apply, ← Real.exp_sum, ← Finset.sum_neg_distrib]
  have hrow : Integrable (fun row : Fin N → ℂ => ∏ j, Real.exp (-‖row j‖ ^ 2)) :=
    Integrable.fintype_prod (fun _ => gaussA_cint)
  have hrowi : ∫ row : Fin N → ℂ, ∏ j, Real.exp (-‖row j‖ ^ 2) = Real.pi ^ N := by
    rw [integral_fintype_prod_volume_eq_prod (fun (_ : Fin N) (z : ℂ) => Real.exp (-‖z‖ ^ 2))]
    simp only [gaussA_cintegral, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [hpt]
  rw [show (volume : Measure (Fin N → Fin N → ℂ)) = Measure.pi (fun _ => volume) from rfl,
    gaussA_lint_pi_ofReal _ (fun _ => hrow)
      (fun _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]
  simp only [hrowi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (pow_nonneg Real.pi_pos.le _), ← pow_mul, sq]

theorem gaussC_hs_upMat (t : TriCo N) :
    hs (upMat t) = ∑ j, t.1 j ^ 2 + ∑ ab : {ab : Fin N × Fin N // ab.1 < ab.2}, ‖t.2 ab‖ ^ 2 := by
  have hp : ∀ a b : Fin N, ‖upMat t a b‖ ^ 2 = (if a = b then t.1 a ^ 2 else 0) +
      (if h : a < b then ‖t.2 ⟨(a, b), h⟩‖ ^ 2 else 0) := by
    intro a b
    unfold upMat
    by_cases hab : a = b
    · subst hab; simp [Complex.norm_real, sq_abs]
    · by_cases h : a < b
      · simp [hab, h]
      · simp [hab, h]
  unfold hs
  simp_rw [hp, Finset.sum_add_distrib]
  congr 1
  · simp [Finset.sum_ite_eq]
  · rw [← Finset.sum_product' (f := fun a b => if h : a < b then ‖t.2 ⟨(a, b), h⟩‖ ^ 2 else 0),
      Finset.univ_product_univ,
      ← (Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)).sum_comp, Fintype.sum_sum_type]
    have h1 : ∀ a : {p : Fin N × Fin N // p.1 < p.2},
        (fun p : Fin N × Fin N => if h : p.1 < p.2 then ‖t.2 ⟨(p.1, p.2), h⟩‖ ^ 2 else 0)
          ((Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)) (Sum.inl a)) = ‖t.2 a‖ ^ 2 := by
      intro a; obtain ⟨⟨x, y⟩, h⟩ := a; simp [h]
    have h2 : ∀ b : {p : Fin N × Fin N // ¬ p.1 < p.2},
        (fun p : Fin N × Fin N => if h : p.1 < p.2 then ‖t.2 ⟨(p.1, p.2), h⟩‖ ^ 2 else 0)
          ((Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)) (Sum.inr b)) = 0 := by
      intro b; obtain ⟨⟨x, y⟩, h⟩ := b; simp [h]
    simp only [h1, h2, Finset.sum_const_zero, add_zero]

def gaussRadW (N : ℕ) (j : Fin N) (r : ℝ) : ℝ := Real.exp (-r ^ 2) * |r| ^ (2 * (N - 1 - (j : ℕ)) + 1)

theorem gaussD_integrand (t : TriCo N) (ht : t ∈ triPos N) :
    ENNReal.ofReal (Real.exp (-hs (upMat t))) * ENNReal.ofReal (qrWt t) =
      ENNReal.ofReal (∏ j, gaussRadW N j (t.1 j)) *
        ENNReal.ofReal (∏ ab : {ab : Fin N × Fin N // ab.1 < ab.2}, Real.exp (-‖t.2 ab‖ ^ 2)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul' (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]
  congr 1
  rw [gaussC_hs_upMat, neg_add, Real.exp_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    Real.exp_sum, Real.exp_sum]
  have hw : ∀ j : Fin N, t.1 j ^ (2 * (N - (j : ℕ)) - 1) = |t.1 j| ^ (2 * (N - 1 - (j : ℕ)) + 1) := by
    intro j
    rw [abs_of_pos (ht j)]
    congr 1
    have := j.2
    omega
  unfold qrWt gaussRadW
  simp_rw [hw, Finset.prod_mul_distrib]
  ring

theorem gaussD_triPos_eq : triPos N = (Set.univ.pi fun _ : Fin N => Set.Ioi (0:ℝ)) ×ˢ Set.univ := by
  ext t
  simp [triPos]

theorem gaussD_tri :
    ∫⁻ t in triPos N, ENNReal.ofReal (Real.exp (-hs (upMat t))) * ENNReal.ofReal (qrWt t) =
      ENNReal.ofReal (Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N) := by
  have hms : MeasurableSet (triPos N) := by
    rw [gaussD_triPos_eq]
    exact (MeasurableSet.univ_pi fun _ => measurableSet_Ioi).prod MeasurableSet.univ
  rw [setLIntegral_congr_fun hms (fun t ht => gaussD_integrand t ht), gaussD_triPos_eq,
    show (volume : Measure (TriCo N)) = (volume : Measure (Fin N → ℝ)).prod
      (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)) from rfl,
    ← Measure.prod_restrict, Measure.restrict_univ,
    show (volume : Measure (Fin N → ℝ)) = Measure.pi (fun _ => volume) from rfl,
    Measure.restrict_pi_pi]
  rw [lintegral_prod_mul (f := fun x : Fin N → ℝ => ENNReal.ofReal (∏ j, gaussRadW N j (x j)))
    (g := fun y : {ab : Fin N × Fin N // ab.1 < ab.2} → ℂ =>
      ENNReal.ofReal (∏ ab, Real.exp (-‖y ab‖ ^ 2)))
    (by unfold gaussRadW; fun_prop)
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun y : {ab : Fin N × Fin N // ab.1 < ab.2} → ℂ =>
      ∏ ab, Real.exp (-‖y ab‖ ^ 2)).measurable).aemeasurable]
  rw [gaussA_lint_pi_ofReal (fun j => gaussRadW N j) (fun j => gaussA_rad_int _)
      (fun j r => mul_nonneg (Real.exp_pos _).le (pow_nonneg (abs_nonneg _) _)),
    show (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)) = Measure.pi (fun _ => volume) from rfl,
    gaussA_lint_pi_ofReal (fun (_ : {ab : Fin N × Fin N // ab.1 < ab.2}) (z : ℂ) => Real.exp (-‖z‖ ^ 2))
      (fun _ => gaussA_cint) (fun _ _ => (Real.exp_pos _).le)]
  simp only [gaussRadW, gaussA_rad, gaussA_cintegral, Finset.prod_const, Finset.card_univ, gaussB_card_lt]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity),
    ← ENNReal.ofReal_pow Real.pi_pos.le, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => by positivity),
    gaussB_prod_fact]
  congr 1
  ring

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem gaussE_pow_odd (n : ℕ) : (∏ i ∈ range n, Real.pi ^ (2 * i + 1)) = Real.pi ^ (n ^ 2) := by
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem gaussE_volU_mul :
    volU N * (Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N) =
      Real.pi ^ (N ^ 2) := by
  have hX : Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N =
      ∏ i ∈ range N, (Real.pi ^ i * (i.factorial : ℝ) / 2) := by
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finset.sum_range_id, Finset.prod_const, Finset.card_range]
  rw [hX, volU, ← Finset.prod_mul_distrib, ← gaussE_pow_odd N]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hf : (i.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)
  field_simp
  ring

theorem gaussE_qr_const (μ : Measure (UNgrp N)) [IsProbabilityMeasure μ] (C : ℝ)
    (hC : ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = ENNReal.ofReal C * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ) :
    C = volU N := by
  have hcont : Continuous fun Z : Fin N → Fin N → ℂ => hs (Matrix.of Z) := by
    unfold hs
    simp only [Matrix.of_apply]
    fun_prop
  have h := hC (fun Z => ENNReal.ofReal (Real.exp (-hs (Matrix.of Z))))
    (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hcont.neg).measurable)
  have hin : ∀ k : UNgrp N, (∫⁻ t in triPos N, ENNReal.ofReal (Real.exp (-hs (Matrix.of (qrMap (k, t))))) *
      ENNReal.ofReal (qrWt t)) =
      ENNReal.ofReal (Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N) := by
    intro k
    simp only [qrMap, Equiv.apply_symm_apply, gaussB_hs_unitary_mul]
    exact gaussD_tri
  simp only [hin, lintegral_const, measure_univ, mul_one, gaussC_mat] at h
  set X := Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N with hXdef
  have hXpos : 0 < X := by
    rw [hXdef]
    have : 0 < ∏ i ∈ range N, (i.factorial : ℝ) :=
      Finset.prod_pos fun i _ => Nat.cast_pos.2 (Nat.factorial_pos i)
    positivity
  have hPpos : 0 < Real.pi ^ (N ^ 2) := pow_pos Real.pi_pos _
  have hCpos : 0 < C := by
    by_contra hc
    rw [ENNReal.ofReal_of_nonpos (not_lt.mp hc), zero_mul, ENNReal.ofReal_eq_zero] at h
    linarith
  rw [← ENNReal.ofReal_mul hCpos.le, ENNReal.ofReal_eq_ofReal_iff hPpos.le (by positivity)] at h
  have h2 := gaussE_volU_mul (N := N)
  rw [← hXdef] at h2
  exact mul_right_cancel₀ hXpos.ne' (h.symm.trans h2.symm)

theorem qr_const (μ : Measure (UNgrp N)) [IsProbabilityMeasure μ] (C : ℝ)
    (hC : ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = ENNReal.ofReal C * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ) :
    C = volU N :=
  gaussE_qr_const μ C hC

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.VolUSetMeasurable
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.VolUMeasurableSetTriPos
noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem volU_pos' (M : ℕ) : 0 < volU M := by
  unfold volU
  exact Finset.prod_pos fun i _ => by positivity

theorem volU_skMat_conjTranspose (x : UCo N) : (skMat x)ᴴ = -skMat x := by
  ext a b
  simp only [conjTranspose_apply, Matrix.neg_apply, skMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, h.ne', h, not_lt.2 h.le]
  · simp
  · simp [h.ne, h.ne', h, not_lt.2 h.le]

theorem volU_exp_inUJ (x : UCo N) :
    inUJ (fun _ : Fin N => true) (NormedSpace.exp (skMat x)) := by
  have hJ : Jm (fun _ : Fin N => true) = 1 := by simp [Jm]
  unfold inUJ
  rw [hJ, Matrix.mul_one, ← Matrix.exp_conjTranspose, volU_skMat_conjTranspose,
    ← Matrix.exp_add_of_commute (-skMat x) (skMat x) (Commute.refl (skMat x)).neg_left,
    neg_add_cancel, NormedSpace.exp_zero]

theorem volU_continuous_skMat : Continuous (skMat (N := N)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [skMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp only [h.ne, h, not_lt.2 h.le, if_false, dif_neg, dif_pos, not_false_eq_true]
    fun_prop
  · simp only [if_true]
    fun_prop
  · simp only [h.ne', h, not_lt.2 h.le, if_false, dif_neg, dif_pos, not_false_eq_true]
    fun_prop

theorem volU_skMat_injective : Function.Injective (skMat (N := N)) := by
  intro x y h
  have h1 : ∀ a b, skMat x a b = skMat y a b := fun a b => by rw [h]
  refine Prod.ext (funext fun a => ?_) (funext fun ab => ?_)
  · simpa [skMat, Complex.I_ne_zero] using h1 a a
  · obtain ⟨⟨a, b⟩, hab⟩ := ab
    simpa [skMat, hab.ne', hab] using h1 a b

theorem volU_skMat_zero : skMat (0 : UCo N) = 0 := by
  ext a b
  simp [skMat]

theorem volU_exp_injOn : ∃ δ > 0, Set.InjOn (fun x : UCo N => NormedSpace.exp (skMat x))
    (Metric.ball 0 δ) := by
  obtain ⟨ℓ, -, -, hℓ⟩ := lcA_exists_log (n := N)
  have hc : Tendsto (skMat (N := N)) (𝓝 0) (𝓝 0) := by
    have := (volU_continuous_skMat (N := N)).tendsto 0
    rwa [volU_skMat_zero] at this
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (hc.eventually hℓ)
  refine ⟨δ, hδ, fun x hx y hy hxy => volU_skMat_injective ?_⟩
  have ex := hδ' (Metric.mem_ball.1 hx)
  have ey := hδ' (Metric.mem_ball.1 hy)
  simp only at hxy ex ey
  rw [← ex, ← ey, hxy]

def volUOne (N : ℕ) : TriCo N := (fun _ => 1, 0)

theorem volU_upMat_add (t : TriCo N) : upMat (t + volUOne N) = 1 + upMat t := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [upMat, volUOne, add_comm]
  · simp [upMat, volUOne, h]

theorem volU_qrWt_one : qrWt (volUOne N) = 1 := by
  simp [qrWt, volUOne]

theorem volU_continuous_qrWt : Continuous (qrWt (N := N)) :=
  continuous_finsetProd _ fun j _ => ((continuous_apply j).comp continuous_fst).pow _

theorem volU_ball_sub_triPos {ρ : ℝ} (hρ : ρ ≤ 1) : Metric.ball (volUOne N) ρ ⊆ triPos N := by
  intro t ht j
  rw [Metric.mem_ball, dist_eq_norm] at ht
  have h1 : ‖(t - volUOne N).1 j‖ ≤ ‖t - volUOne N‖ :=
    (norm_le_pi_norm _ j).trans (norm_fst_le _)
  have h2 : (t - volUOne N).1 j = t.1 j - 1 := by simp [volUOne]
  rw [h2, Real.norm_eq_abs] at h1
  linarith [neg_le_abs (t.1 j - 1)]

theorem volU_measurableSet_triPos : MeasurableSet (triPos N) := by
  simp only [triPos, Set.ofPred_forall]
  exact MeasurableSet.iInter fun j =>
    measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_fst)

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem volU_real {V η ε a b e i : ℝ} (hV : 0 < V) (he : 0 < e) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hη : 0 < η) (hkey : (1 - ε) * (1 + η) = 1 + ε)
    (h1 : V * (i * a) ≤ (1 + ε) * (b * e)) (h2 : (1 - ε) * (b * e) ≤ V * (i * a))
    (h3 : (1 - ε) * e ≤ i) (h4 : i ≤ (1 + ε) * e) :
    a ≤ (1 + η) / V * b ∧ (1 - η) / V * b ≤ a := by
  have hε' : 0 < 1 - ε := by linarith
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ hV]
    have k1 : V * a * ((1 - ε) * e) ≤ V * a * i :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg hV.le ha)
    have k2 : (1 + ε) * (b * e) = (1 - ε) * (1 + η) * (b * e) := by rw [hkey]
    have k3 : (1 - ε) * e * (a * V) ≤ (1 - ε) * e * ((1 + η) * b) := by
      linarith [k1, h1, k2]
    exact le_of_mul_le_mul_left k3 (mul_pos hε' he)
  · rw [div_mul_eq_mul_div, div_le_iff₀ hV]
    have k1 : V * a * i ≤ V * a * ((1 + ε) * e) :=
      mul_le_mul_of_nonneg_left h4 (mul_nonneg hV.le ha)
    have k2 : (1 + ε) * (1 - η) * (b * e) = (1 - ε) * (1 + η) * (1 - η) * (b * e) := by
      rw [hkey]
    have k3 : 0 ≤ (1 - ε) * η ^ 2 * (b * e) :=
      mul_nonneg (mul_nonneg hε'.le (sq_nonneg η)) (mul_nonneg hb he.le)
    have k4 : (1 + ε) * e * ((1 - η) * b) ≤ (1 + ε) * e * (a * V) := by
      linarith [k1, h2, k2, k3]
    exact le_of_mul_le_mul_left k4 (mul_pos (by linarith) he)

def volUSet (B : Set (UCo N)) : Set (UNgrp N) := {k | ∃ x ∈ B, toM k = NormedSpace.exp (skMat x)}

theorem volUSet_measurable {δ : ℝ}
    (hinj : Set.InjOn (fun x : UCo N => NormedSpace.exp (skMat x)) (Metric.ball 0 δ))
    {B : Set (UCo N)} (hB : MeasurableSet B) (hBs : B ⊆ Metric.ball 0 δ) :
    MeasurableSet (volUSet B) := by
  set F : UCo N → (Fin N → Fin N → ℂ) := fun x => Matrix.of.symm (NormedSpace.exp (skMat x)) with hF
  set G : UNgrp N → (Fin N → Fin N → ℂ) := fun k => Matrix.of.symm (toM k) with hG
  have hS : volUSet B = G ⁻¹' (F '' B) := by
    ext k
    simp only [volUSet, Set.mem_preimage, Set.mem_image, hF, hG]
    constructor
    · rintro ⟨x, hx, hk⟩
      exact ⟨x, hx, by rw [hk]⟩
    · rintro ⟨x, hx, hk⟩
      exact ⟨x, hx, (Matrix.of.symm.injective hk).symm⟩
  have hGc : Continuous G := continuous_toM _
  have hexp : Continuous (fun X : Matrix (Fin N) (Fin N) ℂ => NormedSpace.exp X) := by
    let _ : NormedRing (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedRing
    let _ : NormedAlgebra ℚ (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedAlgebra
    exact @NormedSpace.exp_continuous (Matrix (Fin N) (Fin N) ℂ) _ _
      (inferInstanceAs (CompleteSpace (Fin N → Fin N → ℂ)))
  have hFc : Continuous F := hexp.comp volU_continuous_skMat
  rw [hS]
  refine hGc.measurable ?_
  refine MeasurableSet.image_of_continuousOn_injOn hB hFc.continuousOn ?_
  intro x hx y hy hxy
  exact hinj (hBs hx) (hBs hy) (Matrix.of.symm.injective hxy)

theorem volU_image_eq (B : Set (UCo N)) (ρ : ℝ) :
    chartWR '' (B ×ˢ Metric.ball 0 ρ) = qrMap '' (volUSet B ×ˢ Metric.ball (volUOne N) ρ) := by
  ext Z
  constructor
  · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    have hmem : NormedSpace.exp (skMat x) ∈ Set.range (fun g : UNgrp N => toM g) := by
      rw [range_toM]
      exact volU_exp_inUJ x
    obtain ⟨k, hk⟩ := hmem
    have hk' : toM k = NormedSpace.exp (skMat x) := hk
    refine ⟨(k, t + volUOne N), ⟨⟨x, hx, hk'⟩, ?_⟩, ?_⟩
    · show dist (t + volUOne N) (volUOne N) < ρ
      rw [dist_eq_norm, add_sub_cancel_right, ← dist_zero_right]
      exact ht
    · simp only [qrMap, chartWR, volU_upMat_add, hk']
  · rintro ⟨⟨k, t⟩, ⟨⟨x, hx, hk⟩, ht⟩, rfl⟩
    refine ⟨(x, t - volUOne N), ⟨hx, ?_⟩, ?_⟩
    · show dist (t - volUOne N) 0 < ρ
      rw [dist_zero_right, ← dist_eq_norm]
      exact ht
    · have ht' : upMat t = 1 + upMat (t - volUOne N) := by
        rw [← volU_upMat_add, sub_add_cancel]
      have hk' : toM k = NormedSpace.exp (skMat x) := hk
      simp only [qrMap, chartWR, ht']
      rw [hk']

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem volU_density (μ : Measure (UNgrp N)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ B : Set (UCo N), MeasurableSet B → (∀ x ∈ B, ‖x‖ < δ) →
      μ {k : UNgrp N | ∃ x ∈ B, toM k = NormedSpace.exp (skMat x)} ≤ ENNReal.ofReal ((1 + η) / volU N) * volume B ∧
        ENNReal.ofReal ((1 - η) / volU N) * volume B ≤ μ {k : UNgrp N | ∃ x ∈ B, toM k = NormedSpace.exp (skMat x)} := by
  obtain ⟨C, -, hC⟩ := qr_lintegral μ
  have hCV : C = volU N := qr_const μ C hC
  subst hCV
  have hV := volU_pos' N
  obtain ⟨ε, hε0, hε1, hkey⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (1 - ε) * (1 + η) = 1 + ε :=
    ⟨η / (2 + η), by positivity, by rw [div_lt_one (by linarith)]; linarith,
      by field_simp; ring⟩
  obtain ⟨δ1, hδ1, hchart⟩ := chartWR_vol (N := N) ε hε0
  obtain ⟨δ2, hδ2, hinj⟩ := volU_exp_injOn (N := N)
  obtain ⟨ρw, hρw, hw⟩ := Metric.continuousAt_iff.1
    (volU_continuous_qrWt (N := N)).continuousAt ε hε0
  obtain ⟨ρ, hρ0, hρ1, hρ2, hρ3⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ δ1 ∧ ρ ≤ ρw ∧ ρ ≤ 1 :=
    ⟨min δ1 (min ρw 1), lt_min hδ1 (lt_min hρw one_pos), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun B hB hBs => ?_⟩
  show μ (volUSet B) ≤ _ ∧ _ ≤ μ (volUSet B)
  have hBsub : B ⊆ Metric.ball 0 δ2 := fun x hx =>
    mem_ball_zero_iff.2 ((hBs x hx).trans_le (min_le_right _ _))
  have hA : MeasurableSet (volUSet B) := volUSet_measurable hinj hB hBsub
  have hE'pos : Metric.ball (volUOne N) ρ ⊆ triPos N := volU_ball_sub_triPos hρ3
  set S := qrMap '' (volUSet B ×ˢ Metric.ball (volUOne N) ρ) with hSdef
  have hS : MeasurableSet S := qrMap_measurableSet_image _ (hA.prod Metric.isOpen_ball.measurableSet)
    (fun p hp => ⟨Set.mem_univ _, hE'pos hp.2⟩)
  set I := ∫⁻ t in Metric.ball (volUOne N) ρ, ENNReal.ofReal (qrWt t) with hIdef
  have hmem : ∀ k (t : TriCo N), t ∈ triPos N →
      (qrMap (k, t) ∈ S ↔ k ∈ volUSet B ∧ t ∈ Metric.ball (volUOne N) ρ) := by
    intro k t ht
    constructor
    · rintro ⟨⟨k', t'⟩, ⟨hk', ht'⟩, heq⟩
      have := qrMap_injOn ⟨Set.mem_univ _, hE'pos ht'⟩ ⟨Set.mem_univ _, ht⟩ heq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj this
      exact ⟨hk', ht'⟩
    · rintro ⟨hk, ht'⟩
      exact ⟨(k, t), ⟨hk, ht'⟩, rfl⟩
  have hin : ∀ k, (∫⁻ t in triPos N, S.indicator 1 (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) =
      (volUSet B).indicator (fun _ => I) k := by
    intro k
    by_cases hk : k ∈ volUSet B
    · rw [Set.indicator_of_mem hk, hIdef,
        ← Set.inter_eq_left.2 hE'pos, ← setLIntegral_indicator Metric.isOpen_ball.measurableSet]
      refine setLIntegral_congr_fun volU_measurableSet_triPos (fun t ht => ?_)
      by_cases ht' : t ∈ Metric.ball (volUOne N) ρ
      · rw [Set.indicator_of_mem ((hmem k t ht).2 ⟨hk, ht'⟩), Set.indicator_of_mem ht', Pi.one_apply,
          one_mul]
      · rw [Set.indicator_of_notMem (fun h => ht' ((hmem k t ht).1 h).2), Set.indicator_of_notMem ht',
          zero_mul]
    · rw [Set.indicator_of_notMem hk]
      rw [setLIntegral_congr_fun volU_measurableSet_triPos (g := fun _ => 0) (fun t ht => by
        simp only
        rw [Set.indicator_of_notMem (fun h => hk ((hmem k t ht).1 h).1), zero_mul])]
      simp
  have hSeq : volume S = ENNReal.ofReal (volU N) * (I * μ (volUSet B)) := by
    have h := hC (S.indicator 1) (measurable_one.indicator hS)
    rw [lintegral_indicator_one hS] at h
    rw [h, lintegral_congr hin, lintegral_indicator_const hA]
  have : Measure.IsAddHaarMeasure (volume : Measure (TriCo N)) := by
    show Measure.IsAddHaarMeasure ((volume : Measure (Fin N → ℝ)).prod
      (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)))
    exact Measure.prod.instIsAddHaarMeasure _ _
  have : Measure.IsAddHaarMeasure (volume : Measure (UCo N)) := by
    show Measure.IsAddHaarMeasure ((volume : Measure (Fin N → ℝ)).prod
      (volume : Measure ({ab : Fin N × Fin N // ab.2 < ab.1} → ℂ)))
    exact Measure.prod.instIsAddHaarMeasure _ _
  have hE : volume (Metric.ball (volUOne N) ρ) = volume (Metric.ball (0 : TriCo N) ρ) :=
    Measure.addHaar_ball_center _ _ _
  have hIlo : ENNReal.ofReal (1 - ε) * volume (Metric.ball (0 : TriCo N) ρ) ≤ I := by
    rw [← hE, ← setLIntegral_const]
    refine setLIntegral_mono' Metric.isOpen_ball.measurableSet (fun t ht => ENNReal.ofReal_le_ofReal ?_)
    have := hw (lt_of_lt_of_le (Metric.mem_ball.1 ht) hρ2)
    rw [volU_qrWt_one, Real.dist_eq] at this
    linarith [neg_abs_le (qrWt t - 1)]
  have hIhi : I ≤ ENNReal.ofReal (1 + ε) * volume (Metric.ball (0 : TriCo N) ρ) := by
    rw [← hE, ← setLIntegral_const]
    refine setLIntegral_mono' Metric.isOpen_ball.measurableSet (fun t ht => ENNReal.ofReal_le_ofReal ?_)
    have := hw (lt_of_lt_of_le (Metric.mem_ball.1 ht) hρ2)
    rw [volU_qrWt_one, Real.dist_eq] at this
    linarith [le_abs_self (qrWt t - 1)]
  obtain ⟨hup, hlo⟩ := hchart B (Metric.ball 0 ρ) hB Metric.isOpen_ball.measurableSet
    (fun x hx => (hBs x hx).trans_le (min_le_left _ _))
    (fun t ht => (mem_ball_zero_iff.1 ht).trans_le hρ1)
  rw [volU_image_eq, ← hSdef, hSeq] at hup hlo

  have hEpos : 0 < volume (Metric.ball (0 : TriCo N) ρ) := Metric.measure_ball_pos _ _ hρ0
  have hEfin : volume (Metric.ball (0 : TriCo N) ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hBfin : volume B ≠ ⊤ := ((measure_mono hBsub).trans_lt measure_ball_lt_top).ne
  have hAfin : μ (volUSet B) ≠ ⊤ := measure_ne_top μ _
  have hIfin : I ≠ ⊤ := (hIhi.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hEfin.lt_top)).ne
  set a := (μ (volUSet B)).toReal
  set b := (volume B).toReal
  set e := (volume (Metric.ball (0 : TriCo N) ρ)).toReal
  set i := I.toReal
  have ha' : μ (volUSet B) = ENNReal.ofReal a := (ENNReal.ofReal_toReal hAfin).symm
  have hb' : volume B = ENNReal.ofReal b := (ENNReal.ofReal_toReal hBfin).symm
  have he' : volume (Metric.ball (0 : TriCo N) ρ) = ENNReal.ofReal e := (ENNReal.ofReal_toReal hEfin).symm
  have hi' : I = ENNReal.ofReal i := (ENNReal.ofReal_toReal hIfin).symm
  have he0 : 0 < e := ENNReal.toReal_pos hEpos.ne' hEfin
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hi0 : 0 ≤ i := ENNReal.toReal_nonneg
  rw [ha', hb', he', hi'] at hup hlo
  rw [he', hi'] at hIlo hIhi
  rw [← ENNReal.ofReal_mul hi0, ← ENNReal.ofReal_mul hV.le] at hup hlo
  rw [← ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_mul (by linarith)] at hup
  rw [← ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_mul' (by positivity)] at hlo
  rw [← ENNReal.ofReal_mul (by linarith)] at hIhi
  rw [← ENNReal.ofReal_mul' he0.le] at hIlo
  have h1 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hup
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hlo
  have h3 := (ENNReal.ofReal_le_ofReal_iff hi0).1 hIlo
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hIhi
  obtain ⟨r1, r2⟩ := volU_real hV he0 ha0 hb0 hε0 hε1 hη hkey h1 h2 h3 h4
  rw [ha', hb']
  constructor
  · rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal r1
  · rw [← ENNReal.ofReal_mul' hb0]
    exact ENNReal.ofReal_le_ofReal r2

end ReciprocityTheory.ChartRestriction.DS
