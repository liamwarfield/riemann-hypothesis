module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergFactsOfInductiveInput

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.AStepFin
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ExponentShiftEqLevelExponent
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InnerCLe
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section chain
variable (k r' : ℕ)

def mw (c : ℂ) : ℝ := min (‖c‖ ^ (-((4 * r' + 2 * k + 3 : ℕ) : ℝ))) ‖c‖⁻¹

theorem mw_nonneg (c : ℂ) : 0 ≤ mw k r' c :=
  le_min (Real.rpow_nonneg (norm_nonneg _) _) (inv_nonneg.mpr (norm_nonneg _))

theorem mw_meas : Measurable (mw k r') := by
  unfold mw
  exact (measurable_norm.pow_const _).min measurable_norm.inv

theorem weight_eq (s : Fin (1 + r' + 1) → ℝ) (c : ℂ) (hc : c ≠ 0) :
    ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1))) * ∏ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l) =
      ENNReal.ofReal (‖c‖ ^ (2 * ((2 * r' + k + 1 : ℕ) : ℝ) - ∑ l, s l)) := by
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h1 : ∀ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l) = ENNReal.ofReal (‖c‖ ^ (-s l)) := fun l => by
    have e : (‖c‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖c‖ := by rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
    rw [e, ENNReal.ofReal_rpow_of_pos hpos]
  simp only [h1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (norm_nonneg _) _),
    ← ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _)]
  congr 1
  rw [← Real.rpow_sum_of_pos hpos, ← Real.rpow_natCast, ← Real.rpow_add hpos]
  congr 1
  push_cast
  rw [Finset.sum_neg_distrib]; ring

theorem Qf_le (A C0 : ℝ)
    (hC0 : ∀ c : ℂ, c ≠ 0 → ∀ g ∈ GV k r', EInt k r' A c g ≤ ENNReal.ofReal (C0 * mw k r' c *
        gN g ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A)))
    (s1 : Fin (r' + 1) → ℝ) (μ₁ : Measure (Mt k r')) (hμ₁ : IsHaarOn (GV k r') μ₁) (c : ℂ) (hc : c ≠ 0) :
    Qf k r' A s1 μ₁ c ≤
      ENNReal.ofReal (|C0| * mw k r' c) * JInt μ₁ (A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)) s1 := by
  unfold Qf JInt
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  have hconc : ∀ᵐ g ∂μ₁, Matrix.of g ∈ GV k r' := by rw [ae_iff]; exact hμ₁.conc
  filter_upwards [hconc] with g hg
  rw [← mul_assoc]
  gcongr ?_ * _
  refine (hC0 c hc _ hg).trans ?_
  have hG : 0 ≤ gN (Matrix.of g) ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A) :=
    Real.rpow_nonneg (by unfold gN; exact Real.sqrt_nonneg _) _
  rw [← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (mw_nonneg k r' c)),
    show -(A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)) = ((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A by ring]
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (mw_nonneg k r' c)) hG

theorem scale_c (aw D : ℝ) (hD : 0 < D) :
    ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' (c * (D : ℂ))) =
      ENNReal.ofReal (D ^ (-(aw + 2))) * ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c) := by
  have hF : Measurable fun c : ℂ => ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c) :=
    (measurable_norm.pow_const _).ennreal_ofReal.mul (mw_meas k r').ennreal_ofReal
  have h1 : ∀ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' (c * (D : ℂ))) =
      ENNReal.ofReal (D ^ (-aw)) * (ENNReal.ofReal (‖D • c‖ ^ aw) * ENNReal.ofReal (mw k r' (D • c))) := by
    intro c
    have e : c * (D : ℂ) = D • c := by rw [Complex.real_smul, mul_comm]
    rw [e, norm_smul, Real.norm_of_nonneg hD.le, Real.mul_rpow hD.le (norm_nonneg _), ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _), ← mul_assoc, ← Real.rpow_add hD, neg_add_cancel,
      Real.rpow_zero, one_mul]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h2 : ∫⁻ c : ℂ, ENNReal.ofReal (‖D • c‖ ^ aw) * ENNReal.ofReal (mw k r' (D • c)) =
      ENNReal.ofReal (D ^ (-2 : ℝ)) * ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c) := by
    rw [← lintegral_map hF (measurable_const_smul D), Measure.map_addHaar_smul volume hD.ne',
      lintegral_smul_measure]
    congr 2
    rw [Complex.finrank_real_complex, abs_of_pos (inv_pos.mpr (pow_pos hD 2)), Real.rpow_neg hD.le,
      Real.rpow_two]
  rw [h2, ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _), ← Real.rpow_add hD]
  congr 3; ring

theorem inner_c_le (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hT : TLeft) (hk : 1 ≤ k) (A C0 : ℝ)
    (hC0 : ∀ c : ℂ, c ≠ 0 → ∀ g ∈ GV k r', EInt k r' A c g ≤ ENNReal.ofReal (C0 * mw k r' c *
        gN g ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A)))
    (s : Fin (1 + r' + 1) → ℝ) (μ₁ : Measure (Mt k r')) [SFinite μ₁] (hμ₁ : IsHaarOn (GV k r') μ₁)
    (c : ℂ) (hc : c ≠ 0) :
    ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1))) *
      ∫⁻ p : (HPar k r' × HPar k r') × Mt k r',
        ENNReal.ofReal (gN (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2)) ^ (-A)) *
          FsE k (1 + r') s (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2))
        ∂((volume : Measure (HPar k r' × HPar k r')).prod μ₁) ≤
    ENNReal.ofReal (‖c‖ ^ (2 * ((2 * r' + k + 1 : ℕ) : ℝ) - ∑ l, s l)) *
      ∫⁻ x, ENNReal.ofReal (Psi k r' s x) *
        (ENNReal.ofReal (|C0| * mw k r' (c * (Dx k r' x : ℂ))) *
          JInt μ₁ (A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)) (fun l => s (sc r' l))) := by
  obtain ⟨-, -, -, hHI, hHM, -, -, hHA, -, -, -⟩ := heisenbergFacts_of_inductiveInput hB2
  have hos : ∀ (x : HPar k r') (g : Mat k r') (x' : HPar k r'),
      oneStep k r' x c g x' = heis0 k r' (-x.1, -x.2) * w0 k r' c * ιLev k 1 r' g * heis0 k r' x' := by
    intro x g x'; unfold oneStep; rw [hHI]
  have hK : (∏ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l)) ≠ ⊤ := ENNReal.prod_ne_top fun l _ => by
    rw [← ENNReal.coe_rpow_of_ne_zero (nnnorm_ne_zero_iff.mpr hc)]; exact ENNReal.coe_ne_top
  obtain ⟨H, hHdef⟩ : ∃ H : (HPar k r' × HPar k r') × Mt k r' → ℝ≥0∞, H = fun p =>
      ENNReal.ofReal (gN (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2) ^ (-A)) *
        FsE k r' (fun l => s (sc r' l)) (Matrix.of p.2) := ⟨_, rfl⟩
  have h3 := gN_cont k (1 + r')
  have h2 := lev_cont k r'
  have h1 := heisenberg_map_continuous k r'
  have hHm : Measurable H := by
    have hc1 : Continuous fun p : (HPar k r' × HPar k r') × Mt k r' =>
        gN (heis0 k r' (-p.1.1.1, -p.1.1.2) * w0 k r' c * ιLev k 1 r' (Matrix.of p.2) * heis0 k r' p.1.2) := by
      fun_prop
    have e : H = fun p => ENNReal.ofReal (gN (heis0 k r' (-p.1.1.1, -p.1.1.2) * w0 k r' c *
        ιLev k 1 r' (Matrix.of p.2) * heis0 k r' p.1.2) ^ (-A)) *
          FsE k r' (fun l => s (sc r' l)) (Matrix.of p.2) := by
      rw [hHdef]; funext p; rw [hos]
    rw [e]
    exact (hc1.measurable.pow_const _).ennreal_ofReal.mul ((FsE_meas k r' _).comp measurable_snd)
  have hstep1 : ∀ p : (HPar k r' × HPar k r') × Mt k r',
      ENNReal.ofReal (gN (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2)) ^ (-A)) *
        FsE k (1 + r') s (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2)) =
          (∏ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l)) * H p := by
    intro p
    have hf : FsE k (1 + r') s (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2) =
        (∏ l, (‖c‖₊ : ℝ≥0∞) ^ (-s l)) * FsE k r' (fun l => s (sc r' l)) (Matrix.of p.2) :=
      FsE_oneStep k r' hHA hHM p.1.1 p.1.2 c (Matrix.of p.2) s
    show ENNReal.ofReal (gN (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2) ^ (-A)) *
        FsE k (1 + r') s (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2) = _
    rw [hf, hHdef]
    ring
  simp_rw [hstep1]
  rw [lintegral_const_mul' _ _ hK, ← mul_assoc, weight_eq k r' s c hc]
  gcongr
  rw [lintegral_prod _ hHm.aemeasurable,
    show (volume : Measure (HPar k r' × HPar k r')) = (volume : Measure (HPar k r')).prod volume from rfl,
    lintegral_prod _ hHm.lintegral_prod_right'.aemeasurable]
  refine lintegral_mono fun x => ?_
  have hsw : Measurable (Function.uncurry fun (x' : HPar k r') (g : Mt k r') => H ((x, x'), g)) :=
    hHm.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  rw [lintegral_lintegral_swap hsw.aemeasurable]
  have hmx : ∀ g : Mt k r', Measurable fun x' : HPar k r' =>
      ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A)) := by
    intro g
    have e : (fun x' : HPar k r' => ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A))) =
        fun x' => ENNReal.ofReal (gN (heis0 k r' (-x.1, -x.2) * w0 k r' c * ιLev k 1 r' (Matrix.of g) *
          heis0 k r' x') ^ (-A)) := by
      funext x'; rw [hos]
    rw [e]
    exact ((by fun_prop : Continuous fun x' : HPar k r' => gN (heis0 k r' (-x.1, -x.2) * w0 k r' c *
      ιLev k 1 r' (Matrix.of g) * heis0 k r' x')).measurable.pow_const _).ennreal_ofReal
  have hin : ∀ g : Mt k r', ∫⁻ x', H ((x, x'), g) =
      (∫⁻ x', ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A))) *
        FsE k r' (fun l => s (sc r' l)) (Matrix.of g) := by
    intro g; simp only [hHdef]; exact lintegral_mul_const _ (hmx g)
  simp_rw [hin]
  rw [inner_eq k r' hB2 hIW hT hk A s μ₁ hμ₁ x c hc]
  gcongr
  have hG0 := (yx_ga hB2 hIW k r' hk x).1
  have hD : 0 < Dx k r' x := Real.sqrt_pos.mpr hG0
  exact Qf_le k r' A C0 hC0 _ μ₁ hμ₁ _ (mul_ne_zero hc (Complex.ofReal_ne_zero.mpr hD.ne'))

end chain

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem chcond_of {p : ℕ} (ν e : Fin (p + 1) → ℝ) (he : ∀ l, 0 < e l)
    (h0 : ν 0 = e 0 + 2 * ∑ l ∈ Finset.univ.erase 0, e l) (hl : ∀ l, l ≠ 0 → ν l = -e l) : CHCond p ν := by
  have key : ∀ S : Finset (Fin (p + 1)), 0 ∉ S → ∑ j ∈ S, ν j = -∑ j ∈ S, e j := fun S hS => by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j hj => hl j (fun h => hS (h ▸ hj))
  have hsplit : ∀ l : Fin (p + 1), ∑ j ∈ Finset.Iic l, ν j = ν 0 + ∑ j ∈ (Finset.Iic l).erase 0, ν j :=
    fun l => (Finset.add_sum_erase _ _ (Finset.mem_Iic.mpr (by simp))).symm
  have hE : ∀ l : Fin (p + 1), ∑ j ∈ (Finset.Iic l).erase 0, e j ≤ ∑ j ∈ Finset.univ.erase 0, e j :=
    fun l => Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset_erase _ (Finset.subset_univ _))
      (fun j _ _ => (he j).le)
  have hX : ∀ l : Fin (p + 1), 0 ≤ ∑ j ∈ (Finset.Iic l).erase 0, e j :=
    fun l => Finset.sum_nonneg fun j _ => (he j).le
  have h0S : ∀ l : Fin (p + 1), (0 : Fin (p + 1)) ∉ (Finset.Iic l).erase 0 := fun l => by simp
  refine ⟨fun l => ?_, fun l _ => ?_⟩
  · rw [hsplit, key _ (h0S l), h0]
    linarith [hE l, hX l, he 0]
  · have hIoi : (0 : Fin (p + 1)) ∉ Finset.Ioi l := by simp
    have hpart : ∑ j ∈ Finset.univ.erase 0, e j =
        ∑ j ∈ (Finset.Iic l).erase 0, e j + ∑ j ∈ Finset.Ioi l, e j := by
      rw [← Finset.sum_union]
      · congr 1
        ext j
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_Iic, Finset.mem_Ioi, Finset.mem_univ, and_true]
        constructor
        · intro h
          by_cases hjl : j ≤ l
          · exact Or.inl ⟨h, hjl⟩
          · exact Or.inr (not_le.mp hjl)
        · rintro (⟨h, _⟩ | h)
          · exact h
          · exact (lt_of_le_of_lt (by simp : (0 : Fin (p + 1)) ≤ l) h).ne'
      · rw [Finset.disjoint_left]
        intro j hj1 hj2
        simp only [Finset.mem_erase, Finset.mem_Iic, Finset.mem_Ioi] at hj1 hj2
        exact absurd hj1.2 (not_le.mpr hj2)
    rw [hsplit, key _ (h0S l), key _ hIoi, h0]
    linarith [hpart, hX l, he 0]

section fin
variable (k r' : ℕ)

theorem sum_sc (f : Fin (1 + r' + 1) → ℝ) : ∑ l, f l = f 0 + ∑ l : Fin (r' + 1), f (sc r' l) := by
  rw [Fin.sum_univ_succ]
  have e : ∀ i : Fin (1 + r'), Fin.succ i = sc r' (Fin.cast (by omega) i) := fun i => Fin.ext (by simp [sc])
  simp only [e]
  rw [Fin.sum_congr' (fun j => f (sc r' j)) (by omega : 1 + r' = r' + 1)]

theorem sum_erase0 (f : Fin (1 + r' + 1) → ℝ) : ∑ l ∈ Finset.univ.erase 0, f l = ∑ l : Fin (r' + 1), f (sc r' l) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), sum_sc]; ring

theorem sum_levelExponents_shifted : ∑ l : Fin (r' + 1), s0 k (1 + r') (sc r' l) = 2 * (r' : ℝ) + k := by
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ i : Fin r', s0 k (1 + r') (sc r' (Fin.castSucc i)) = 2 := fun i => by
    have := i.isLt
    exact if_pos (by simp only [sc, Fin.val_castSucc]; omega)
  have h2 : s0 k (1 + r') (sc r' (Fin.last r')) = k := by
    exact if_neg (by simp only [sc, Fin.val_last]; omega)
  simp only [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem levelExponent_first_eq_two : s0 k (1 + r') 0 = 2 := by
  exact if_pos (by simp)

theorem exponentShift_eq_levelExponent (hk : 1 ≤ k) (l : Fin (1 + r' + 1)) : s0N (1 + r') (k - 1) l = s0 k (1 + r') l := by
  unfold s0N s0
  split_ifs
  · rfl
  · rw [Nat.cast_sub hk]; push_cast; ring

theorem sc_ne_zero (l : Fin (r' + 1)) : sc r' l ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp [sc] at this

theorem th_ident (s : Fin (1 + r' + 1) → ℝ) (aw : ℝ) (x : HPar k r') (hG0 : 0 < Ga k (1 + r') 0 (Yx k r' x))
    (hGl : ∀ l, 0 ≤ Ga k (1 + r') l (Yx k r' x)) :
    ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (Dx k r' x ^ (-(aw + 2))) =
      ∏ l, ENNReal.ofReal (Ga k (1 + r') l (Yx k r' x) ^
        (-(if l = 0 then aw + 2 - ∑ l' : Fin (r' + 1), s (sc r' l') else s l) / 2)) := by
  have hPsi : 0 ≤ Psi k r' s x := Finset.prod_nonneg fun l _ => Real.rpow_nonneg (div_nonneg (hGl _) hG0.le) _
  rw [← ENNReal.ofReal_mul hPsi, ← ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (hGl l) _)]
  congr 1
  rw [Fin.prod_univ_succ, if_pos rfl]
  have e : ∀ i : Fin (1 + r'), Fin.succ i = sc r' (Fin.cast (by omega) i) := fun i => Fin.ext (by simp [sc])
  simp only [e, sc_ne_zero, if_false]
  rw [Fin.prod_congr' (fun j => Ga k (1 + r') (sc r' j) (Yx k r' x) ^ (-s (sc r' j) / 2)) (by omega : 1 + r' = r' + 1)]
  unfold Psi Dx
  have hP : ∏ l : Fin (r' + 1), (Ga k (1 + r') (sc r' l) (Yx k r' x) / Ga k (1 + r') 0 (Yx k r' x)) ^ (-s (sc r' l) / 2)
      = (∏ l : Fin (r' + 1), Ga k (1 + r') (sc r' l) (Yx k r' x) ^ (-s (sc r' l) / 2)) *
        Ga k (1 + r') 0 (Yx k r' x) ^ (∑ l : Fin (r' + 1), s (sc r' l) / 2) := by
    rw [Real.rpow_sum_of_pos hG0, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [Real.div_rpow (hGl _) hG0.le, div_eq_mul_inv, ← Real.rpow_neg hG0.le]
    congr 2; ring
  have hD : Real.sqrt (Ga k (1 + r') 0 (Yx k r' x)) ^ (-(aw + 2)) = Ga k (1 + r') 0 (Yx k r' x) ^ (-(aw + 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hG0.le]; congr 1; ring
  rw [hP, hD, mul_assoc, ← Real.rpow_add hG0, mul_comm]
  congr 2
  rw [← Finset.sum_div]; ring

end fin

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

noncomputable section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem aStep_fin (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hT : TLeft) (hF : FormulaF) (hCH : CH) (k r' : ℕ) (hk : 1 ≤ k)
    (hA' : AAt k r') : AAt k (1 + r') := by
  intro s hs μG hμG A hA
  obtain ⟨hOSI, -, hHCL, hHI, -, -, hHGE, hHA, hGNL, hHC, hHCLM⟩ := heisenbergFacts_of_inductiveInput hB2
  obtain ⟨μ₁, hμ₁⟩ := hHGE k r'
  have : IsFiniteMeasureOnCompacts μ₁ := ⟨fun K hK => hμ₁.finite_compact K hK⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : (0 : ℝ) ≤ r' := Nat.cast_nonneg r'
  have hs1 : SAdm k r' (fun l => s (sc r' l)) := fun l => by
    have h := hs (sc r' l)
    have e : s0 k (1 + r') (sc r' l) = s0 k r' l := by
      unfold s0 sc; split_ifs <;> first | rfl | (exfalso; simp_all; omega)
    rw [e] at h; exact h
  have hAB : AB k r' ≤ A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ) := by
    unfold AB at hA ⊢; push_cast at hA ⊢; nlinarith
  have hdA : ((4 * r' + 2 * k + 3 : ℕ) : ℝ) < A := by
    unfold AB at hA; push_cast at hA ⊢; nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hr0]
  have hJ1 := hA' _ hs1 μ₁ hμ₁ _ hAB
  obtain ⟨J1, hJ1d⟩ : ∃ J1, J1 = JInt μ₁ (A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)) (fun l => s (sc r' l)) := ⟨_, rfl⟩
  rw [← hJ1d] at hJ1
  obtain ⟨C0, hC0⟩ := eInt_bound hGNL hHA hHC hHCL hHCLM k r' hk A hdA
  obtain ⟨C, -, hOS⟩ := hOSI k r' μG μ₁ hμG hμ₁
  have hfm : Measurable (fun g : Mt k (1 + r') =>
      ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k (1 + r') s (Matrix.of g)) :=
    ((by unfold gN; fun_prop : Continuous fun g : Mt k (1 + r') => gN (Matrix.of g)).measurable.pow_const
      _).ennreal_ofReal.mul (FsE_meas k (1 + r') s)
  unfold JInt
  rw [hOS _ hfm]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  obtain ⟨aw, haw⟩ : ∃ aw : ℝ, aw = 2 * ((2 * r' + k + 1 : ℕ) : ℝ) - ∑ l, s l := ⟨_, rfl⟩
  have hc0 : ∀ᵐ c : ℂ, c ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]; exact measure_singleton 0
  have hYc : Continuous fun x : HPar k r' => Yx k r' x := by
    have e : (fun x : HPar k r' => Yx k r' x) = fun x a => heis0 k r' (-x.1, -x.2) *ᵥ phi2 k r' a := by
      funext x a; unfold Yx; rw [hHI]
    rw [e]; have := heisenberg_map_continuous k r'; fun_prop
  have hGac : ∀ l, Continuous fun x : HPar k r' => Ga k (1 + r') l (Yx k r' x) := by
    intro l; unfold Ga; fun_prop
  have hDm : Measurable fun x => Dx k r' x := by unfold Dx; exact (hGac 0).sqrt.measurable
  have hPm : Measurable fun x => Psi k r' s x := by
    unfold Psi
    exact Finset.measurable_prod _ fun l _ => ((hGac _).measurable.div (hGac 0).measurable).pow_const _
  have hFm : Measurable (Function.uncurry fun (c : ℂ) (x : HPar k r') => ENNReal.ofReal (‖c‖ ^ aw) *
      (ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (mw k r' (c * (Dx k r' x : ℂ))))) :=
    ((measurable_norm.comp measurable_fst).pow_const _).ennreal_ofReal.mul
      ((hPm.comp measurable_snd).ennreal_ofReal.mul ((mw_meas k r').comp
        (measurable_fst.mul (Complex.measurable_ofReal.comp (hDm.comp measurable_snd)))).ennreal_ofReal)
  have hS0 : ∑ l, s0 k (1 + r') l = 2 * (1 + (r' : ℝ)) + k := by
    rw [sum_sc, levelExponent_first_eq_two, sum_levelExponents_shifted]; ring
  have hlt : ∑ l, s l < ∑ l, s0 k (1 + r') l :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun l _ => by linarith [(hs l).1]
  have hge : ∑ l, (s0 k (1 + r') l - 1 / 10) ≤ ∑ l, s l := Finset.sum_le_sum fun l _ => by linarith [(hs l).2]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hge
  push_cast at hge
  have hK1 : ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c) < ⊤ := by
    have h := cInt_fin (2 * r' + k + 1) (∑ l, s l) (by linarith) (by push_cast; linarith)
    have e : (4 * r' + 2 * k + 3 : ℕ) = 2 * (2 * r' + k + 1) + 1 := by ring
    unfold mw; rw [e, haw]; exact h
  have hCHc : CHCond (1 + r') fun l =>
      (if l = 0 then aw + 2 - ∑ l' : Fin (r' + 1), s (sc r' l') else s l) - s0N (1 + r') (k - 1) l := by
    refine chcond_of _ (fun l => s0 k (1 + r') l - s l) (fun l => by linarith [(hs l).1]) ?_ ?_
    · simp only [if_pos rfl]
      rw [sum_erase0, exponentShift_eq_levelExponent k r' hk, levelExponent_first_eq_two, Finset.sum_sub_distrib, sum_levelExponents_shifted, haw, sum_sc r' s]
      push_cast; ring
    · intro l hl0
      simp only [if_neg hl0]
      rw [exponentShift_eq_levelExponent k r' hk]; ring
  have hTh : ∫⁻ x, ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (Dx k r' x ^ (-(aw + 2))) < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) (th_fin hB2 hF hCH k r' hk _ hCHc)
    have hg := yx_ga hB2 hIW k r' hk x
    exact th_ident k r' s aw x hg.1 hg.2
  calc ∫⁻ c, ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1))) *
        ∫⁻ p : (HPar k r' × HPar k r') × Mt k r',
          ENNReal.ofReal (gN (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2)) ^ (-A)) *
            FsE k (1 + r') s (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2))
          ∂((volume : Measure (HPar k r' × HPar k r')).prod μ₁)
      ≤ ∫⁻ c, ENNReal.ofReal (‖c‖ ^ aw) * ∫⁻ x, ENNReal.ofReal (Psi k r' s x) *
          (ENNReal.ofReal (|C0| * mw k r' (c * (Dx k r' x : ℂ))) * J1) := by
        refine lintegral_mono_ae (hc0.mono fun c hc => ?_)
        have h := inner_c_le k r' hB2 hIW hT hk A C0 hC0 s μ₁ hμ₁ c hc
        rw [← hJ1d, ← haw] at h; exact h
    _ = ENNReal.ofReal |C0| * J1 * ∫⁻ x, ∫⁻ c, ENNReal.ofReal (‖c‖ ^ aw) *
          (ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (mw k r' (c * (Dx k r' x : ℂ)))) := by
        rw [← lintegral_lintegral_swap hFm.aemeasurable,
          ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ1.ne)]
        refine lintegral_congr fun c => ?_
        rw [← lintegral_const_mul' (ENNReal.ofReal (‖c‖ ^ aw)) _ ENNReal.ofReal_ne_top,
          ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ1.ne)]
        refine lintegral_congr fun x => ?_
        rw [ENNReal.ofReal_mul (abs_nonneg _)]; ring
    _ = ENNReal.ofReal |C0| * J1 * ∫⁻ x, ENNReal.ofReal (Psi k r' s x) *
          (ENNReal.ofReal (Dx k r' x ^ (-(aw + 2))) *
            ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c)) := by
        congr 1
        refine lintegral_congr fun x => ?_
        have hD : 0 < Dx k r' x := Real.sqrt_pos.mpr (yx_ga hB2 hIW k r' hk x).1
        rw [← scale_c k r' aw _ hD, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun c => ?_; ring
    _ = ENNReal.ofReal |C0| * J1 * ((∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c)) *
          ∫⁻ x, ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (Dx k r' x ^ (-(aw + 2)))) := by
        congr 1
        rw [← lintegral_const_mul' _ _ hK1.ne]
        refine lintegral_congr fun x => ?_; ring
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ1) (ENNReal.mul_lt_top hK1 hTh)

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

namespace ReciprocityTheory.ChartRestriction.DS.Xi

theorem aStepSucc_of (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hT : TLeft) (hF : FormulaF) (hCH : CH) : AStepSucc := by
  intro k r r' hr hk hA
  subst hr
  exact StepA.aStep_fin hB2 hIW hT hF hCH k r' hk hA

end ReciprocityTheory.ChartRestriction.DS.Xi
