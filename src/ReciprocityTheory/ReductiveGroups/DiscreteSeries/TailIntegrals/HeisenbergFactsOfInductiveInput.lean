module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergRankOneDecomposition
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HpkNegMp

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ScaleInt
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities

theorem scale_int {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {r : ℝ}
    (hr : (Module.finrank ℝ E : ℝ) < r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 < a → 0 < b →
      ∫⁻ x, ENNReal.ofReal ((a + b * ‖x‖) ^ (-r)) ∂μ ≤
        ENNReal.ofReal (K * a ^ (-r) * (a / b) ^ (Module.finrank ℝ E : ℝ)) := by
  have hg := integrable_one_add_norm (μ := μ) hr
  refine ⟨∫ x, (1 + ‖x‖) ^ (-r) ∂μ, integral_nonneg fun x => by positivity, fun a b ha hb => ?_⟩
  have ht : 0 < a / b := div_pos ha hb
  have ha' := ha.ne'
  have hb' := hb.ne'
  have hpt : ∀ x : E, (a + b * ‖x‖) ^ (-r) = a ^ (-r) * (1 + ‖(a / b)⁻¹ • x‖) ^ (-r) := by
    intro x
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le),
      ← Real.mul_rpow ha.le (by positivity : (0 : ℝ) ≤ 1 + (a / b)⁻¹ * ‖x‖)]
    congr 1
    first | (field_simp; done) | (field_simp; ring)
  have hF : Integrable (fun x => a ^ (-r) * (1 + ‖(a / b)⁻¹ • x‖) ^ (-r)) μ :=
    (hg.comp_smul (inv_ne_zero ht.ne')).const_mul (a ^ (-r))
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hF (Filter.Eventually.of_forall fun x =>
    mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (by positivity) _))]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_const_mul, Measure.integral_comp_smul (μ := μ) (f := fun y => (1 + ‖y‖) ^ (-r)) (R := (a / b)⁻¹),
    smul_eq_mul, inv_pow, inv_inv, abs_of_pos (pow_pos ht _), Real.rpow_natCast]
  exact le_of_eq (by ring)

end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.RankOneLeviComm
noncomputable section

set_option linter.unusedSimpArgs false

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section grp
variable (k r' : ℕ)

theorem mat_ext_lev {A B : Mat k (1 + r')} (h0 : A *ᵥ e0 k r' = B *ᵥ e0 k r')
    (h1 : A *ᵥ es0 k r' = B *ᵥ es0 k r') (h2 : ∀ v, A *ᵥ liftVec k 1 r' v = B *ᵥ liftVec k 1 r' v) : A = B := by
  have key : ∀ q : Fin (2 * (1 + r') + k + 1), A *ᵥ Pi.single q 1 = B *ᵥ Pi.single q 1 := by
    intro q
    by_cases hq0 : q.val = 0
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) = e0 k r' := by
        have hq : q = eI k (1 + r') (a0 r') := Fin.ext (by simp [eI, a0, hq0])
        rw [hq]
        rfl
      rw [he, h0]
    by_cases hql : q.val = 2 * (1 + r') + k
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) = es0 k r' := by
        have hq : q = esI k (1 + r') (a0 r') := Fin.ext (by simp [esI, a0, hql])
        rw [hq]
        rfl
      rw [he, h1]
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) =
          liftVec k 1 r' (Pi.single ⟨q.val - 1, by omega⟩ 1) := by
        funext p
        simp only [liftVec, Pi.single_apply, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [he, h2]
  ext p q
  have h := congrFun (key q) p
  simpa [Matrix.mulVec_single_one, Matrix.transpose_apply] using h

theorem lev_mul (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift]

theorem lev_one : ιLev k 1 r' (1 : Mat k r') = 1 := by
  apply mat_ext_lev
  · simp only [levi_fixes_base_vector, Matrix.one_mulVec]
  · simp only [levi_fixes_last_basis, Matrix.one_mulVec]
  · intro v
    simp only [lev_lift, Matrix.one_mulVec]

theorem lev_conjT (g : Mat k r') : (ιLev k 1 r' g)ᴴ = ιLev k 1 r' gᴴ := by
  ext p q
  simp only [Matrix.conjTranspose_apply, ιLev]
  split_ifs <;> (try subst_vars) <;> simp_all [Matrix.conjTranspose_apply]

theorem lev_mem {g : Mat k r'} (hg : g ∈ GV k r') : ιLev k 1 r' g ∈ GV k (1 + r') := by
  have hg' : gᴴ * Hpk k r' * g = Hpk k r' := hg
  show (ιLev k 1 r' g)ᴴ * Hpk k (1 + r') * ιLev k 1 r' g = Hpk k (1 + r')
  rw [lev_conjT]
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector, Hpk_mulVec_e0, levi_fixes_last_basis]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis, hermMatrix_last_basis, levi_fixes_base_vector]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift, Hpk_lift]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

theorem rankOne_levi_comm (c : ℂ) (g : Mat k r') : w0 k r' c * ιLev k 1 r' g = ιLev k 1 r' g * w0 k r' c := by
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector, long_weyl_sends_base_to_dual, Matrix.mulVec_smul, levi_fixes_last_basis]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis, rankOneMatrix_last_basis, Matrix.mulVec_smul, levi_fixes_base_vector]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift, rankOneMatrix_lift]

theorem lev_K {κ : Mat k r'} (hκ : κ ∈ Kset k r') : ιLev k 1 r' κ ∈ Kset k (1 + r') := by
  refine ⟨lev_mem k r' hκ.1, ?_⟩
  rw [lev_conjT, ← lev_mul, hκ.2, lev_one]

end grp

section gn
variable {n : ℕ}

theorem normSq_sum_eq_trace (Y : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i, ∑ j, Complex.normSq (Y i j) : ℝ) : ℂ) = (Yᴴ * Y).trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

theorem gN_unitary (k r : ℕ) {κ : Mat k r} (hκ : κᴴ * κ = 1) (X : Mat k r) : gN (κ * X) = gN X := by
  unfold gN
  congr 1
  have h1 := normSq_sum_eq_trace (κ * X)
  have h2 := normSq_sum_eq_trace X
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul] at h1
  exact_mod_cast h1.trans h2.symm

theorem gN_cont (k r : ℕ) : Continuous (fun g : Mat k r => gN g) := by
  unfold gN
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _
    fun j _ => Complex.continuous_normSq.comp (continuous_id.matrix_elem i j))

end gn

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.EIntBound
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergMapContinuous
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergDualBaseVectorFormulaAlt
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section entries
variable (k r' : ℕ)

theorem entry_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) : M p q = (M *ᵥ bvec q) p := by
  rw [bvec, mulVec_single_one]; rfl

theorem dual_base_vector_eq_single : es0 k r' = bvec (⟨2 * (1 + r') + k, by omega⟩ : Fin (2 * (1 + r') + k + 1)) := by
  funext p
  rw [last_basis_apply, bvec, Pi.single_apply]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; exact h2 (Fin.ext h1)) | (exfalso; exact h1 (congrArg Fin.val h2))

theorem heis_liftVec (hHA : HeisAct) (x : HPar k r') (z : Fin (2 * r' + k + 1) → ℂ) :
    heis0 k r' x *ᵥ liftVec k 1 r' z =
      liftVec k 1 r' z - herm (Hpk k (1 + r')) (liftVec k 1 r' z) (liftVec k 1 r' x.1) • e0 k r' := by
  rw [show heis0 k r' x = heisG k r' (liftVec k 1 r' x.1) (hb k r' x.1 x.2) from rfl, hHA, hermitian_form_base_vector_right,
    liftVec_out k r' z _ (Or.inr rfl), zero_smul, add_zero]

theorem heisenberg_dual_base_vector_formula (hHA : HeisAct) (x : HPar k r') :
    heis0 k r' x *ᵥ es0 k r' = es0 k r' + liftVec k 1 r' x.1 + hb k r' x.1 x.2 • e0 k r' := by
  rw [show heis0 k r' x = heisG k r' (liftVec k 1 r' x.1) (hb k r' x.1 x.2) from rfl, hHA, hermitian_dual_base_vector_left,
    liftVec_out k r' x.1 _ (Or.inl rfl), star_zero, zero_smul, sub_zero, hermitian_form_base_vector_right, last_basis_apply, if_pos rfl,
    one_smul]
  exact (add_assoc _ _ _).symm

variable (c : ℂ) (g : Mat k r') (x : HPar k r')

theorem conj_gg (hHA : HeisAct) (i j : Fin (2 * r' + k + 1)) :
    (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) (levPos k 1 r' i) (levPos k 1 r' j) = g i j := by
  rw [entry_eq (w0 k r' c * heis0 k r' x * ιLev k 1 r' g), ← mulVec_mulVec, ← mulVec_mulVec, bvec_lev, ιLev_liftVec, heis_liftVec k r' hHA,
    reflection_mulVec_levelPos, Pi.sub_apply, Pi.smul_apply, liftVec_lev, goodRowsProjector_apply_eq_sum, if_neg (by rw [levPos_val]; omega),
    smul_zero, sub_zero, bvec, mulVec_single_one]
  rfl

theorem conj_y (hHA : HeisAct) (i : Fin (2 * r' + k + 1)) :
    (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) (levPos k 1 r' i) ⟨2 * (1 + r') + k, by omega⟩ = x.1 i := by
  rw [entry_eq (w0 k r' c * heis0 k r' x * ιLev k 1 r' g), ← mulVec_mulVec, ← mulVec_mulVec, ← dual_base_vector_eq_single, levelEmbedding_mulVec_es0, heisenberg_dual_base_vector_formula k r' hHA, reflection_mulVec_levelPos,
    Pi.add_apply, Pi.add_apply, Pi.smul_apply, liftVec_lev, goodRowsProjector_apply_eq_sum, last_basis_apply,
    if_neg (by rw [levPos_val]; omega), if_neg (by rw [levPos_val]; omega)]
  simp

theorem conj_cb (hHA : HeisAct) :
    (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ⟨2 * (1 + r') + k, by omega⟩ ⟨2 * (1 + r') + k, by omega⟩ =
      c * hb k r' x.1 x.2 := by
  rw [entry_eq (w0 k r' c * heis0 k r' x * ιLev k 1 r' g), ← mulVec_mulVec, ← mulVec_mulVec, ← dual_base_vector_eq_single, levelEmbedding_mulVec_es0, heisenberg_dual_base_vector_formula k r' hHA, rankOneMatrix_last_coord,
    Pi.add_apply, Pi.add_apply, Pi.smul_apply, liftVec_out k r' x.1 _ (Or.inl rfl), goodRowsProjector_apply_eq_sum, last_basis_apply,
    if_neg (by simp only; omega), if_pos rfl]
  simp

theorem un_col (hHA : HeisAct) (j : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g *ᵥ (heis0 k r' x *ᵥ bvec (levPos k 1 r' j)) =
      liftVec k 1 r' (g *ᵥ bvec j) -
        herm (Hpk k (1 + r')) (bvec (levPos k 1 r' j)) (liftVec k 1 r' x.1) • e0 k r' := by
  rw [bvec_lev, heis_liftVec k r' hHA, mulVec_sub, mulVec_smul, ιLev_liftVec, levi_embedding_mulVec_e0]

theorem un_gg (hHA : HeisAct) (i j : Fin (2 * r' + k + 1)) :
    (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) (levPos k 1 r' i) (levPos k 1 r' j) = g i j := by
  rw [entry_eq (w0 k r' c * ιLev k 1 r' g * heis0 k r' x), ← mulVec_mulVec, ← mulVec_mulVec, un_col k r' g x hHA, reflection_mulVec_levelPos, Pi.sub_apply,
    Pi.smul_apply, liftVec_lev, goodRowsProjector_apply_eq_sum, if_neg (by rw [levPos_val]; omega), smul_zero, sub_zero, bvec,
    mulVec_single_one]
  rfl

theorem un_row (hHA : HeisAct) (j : Fin (2 * r' + k + 1)) :
    (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ⟨2 * (1 + r') + k, by omega⟩ (levPos k 1 r' j) =
      -(c * herm (Hpk k (1 + r')) (bvec (levPos k 1 r' j)) (liftVec k 1 r' x.1)) := by
  rw [entry_eq (w0 k r' c * ιLev k 1 r' g * heis0 k r' x), ← mulVec_mulVec, ← mulVec_mulVec, un_col k r' g x hHA, rankOneMatrix_last_coord, Pi.sub_apply,
    Pi.smul_apply, liftVec_out k r' _ _ (Or.inl rfl), goodRowsProjector_apply_eq_sum, if_pos rfl]
  simp

theorem un_cb (hHA : HeisAct) :
    (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ⟨2 * (1 + r') + k, by omega⟩ ⟨2 * (1 + r') + k, by omega⟩ =
      c * hb k r' x.1 x.2 := by
  have hv : ιLev k 1 r' g *ᵥ (heis0 k r' x *ᵥ es0 k r') =
      es0 k r' + liftVec k 1 r' (g *ᵥ x.1) + hb k r' x.1 x.2 • e0 k r' := by
    rw [heisenberg_dual_base_vector_formula k r' hHA, mulVec_add, mulVec_add, mulVec_smul, levelEmbedding_mulVec_es0, ιLev_liftVec, levi_embedding_mulVec_e0]
  rw [entry_eq (w0 k r' c * ιLev k 1 r' g * heis0 k r' x), ← mulVec_mulVec, ← mulVec_mulVec, ← dual_base_vector_eq_single, hv,
    rankOneMatrix_last_coord, Pi.add_apply, Pi.add_apply, Pi.smul_apply,
    liftVec_out k r' _ _ (Or.inl rfl), goodRowsProjector_apply_eq_sum, last_basis_apply, if_neg (by simp only; omega), if_pos rfl]
  simp

end entries

section bounds
variable (k r' : ℕ)

theorem exists_perm (y : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) :
    ∃ j : Fin (2 * r' + k + 1),
      ‖herm (Hpk k (1 + r')) (bvec (levPos k 1 r' j)) (liftVec k 1 r' y)‖ = ‖y i‖ := by
  by_cases hA : i.val + 1 < 1 + r' ∨ 1 + r' + k < i.val + 1
  · refine ⟨⟨2 * (1 + r') + k - (i.val + 1) - 1, by omega⟩, ?_⟩
    rw [herm_bvec, norm_star, hpk_mulVec', if_pos (by rw [levPos_val]; simp only; omega), liftVec_apply,
      dite_eq_left (by simp only [levPos_val]; omega)]
    exact congrArg (fun t => ‖y t‖) (Fin.ext (by simp only [levPos_val]; omega))
  · refine ⟨i, ?_⟩
    rw [herm_bvec, norm_star, hpk_mulVec', if_neg (by rw [levPos_val]; omega)]
    split_ifs <;> simp [liftVec_lev]

theorem gN_nonneg' {n : ℕ} (M : Mat k n) : 0 ≤ gN M := Real.sqrt_nonneg _

theorem gN_entry {n : ℕ} (M : Mat k n) (p q : Fin (2 * n + k + 1)) : ‖M p q‖ ≤ gN M := by
  rw [← Real.sqrt_sq (norm_nonneg (M p q)), Complex.sq_norm]
  unfold gN
  apply Real.sqrt_le_sqrt
  calc Complex.normSq (M p q) ≤ ∑ j, Complex.normSq (M p j) :=
        Finset.single_le_sum (f := fun j => Complex.normSq (M p j)) (fun j _ => Complex.normSq_nonneg _)
          (Finset.mem_univ q)
    _ ≤ ∑ i, ∑ j, Complex.normSq (M i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (M i j))
          (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ p)

theorem gN_sub (M : Mat k (1 + r')) (g : Mat k r')
    (h : ∀ i j, M (levPos k 1 r' i) (levPos k 1 r' j) = g i j) : gN g ≤ gN M := by
  unfold gN
  apply Real.sqrt_le_sqrt
  calc ∑ i, ∑ j, Complex.normSq (g i j)
      = ∑ i, ∑ j, Complex.normSq (M (levPos k 1 r' i) (levPos k 1 r' j)) := by simp only [h]
    _ ≤ ∑ i, ∑ q, Complex.normSq (M (levPos k 1 r' i) q) :=
        Finset.sum_le_sum fun i _ => sum_lev_le k r' (fun q => Complex.normSq (M (levPos k 1 r' i) q))
          fun q => Complex.normSq_nonneg _
    _ ≤ ∑ p, ∑ q, Complex.normSq (M p q) :=
        sum_lev_le k r' (fun p => ∑ q, Complex.normSq (M p q))
          fun p => Finset.sum_nonneg fun q _ => Complex.normSq_nonneg _

theorem hb_im (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) : (hb k r' y s).im = s := by simp [hb]

theorem cs_le (c : ℂ) (x : HPar k r') (M : Mat k (1 + r'))
    (h : M ⟨2 * (1 + r') + k, by omega⟩ ⟨2 * (1 + r') + k, by omega⟩ = c * hb k r' x.1 x.2) :
    ‖c‖ * |x.2| ≤ gN M := by
  calc ‖c‖ * |x.2| ≤ ‖c‖ * ‖hb k r' x.1 x.2‖ := by
        gcongr
        have := Complex.abs_im_le_norm (hb k r' x.1 x.2)
        rwa [hb_im] at this
    _ = ‖M ⟨2 * (1 + r') + k, by omega⟩ ⟨2 * (1 + r') + k, by omega⟩‖ := by rw [h, norm_mul]
    _ ≤ gN M := gN_entry k _ _ _

variable (c : ℂ) (g : Mat k r') (x : HPar k r')

theorem pt_conj (hHA : HeisAct) :
    gN g ≤ gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ∧
      ‖x.1‖ ≤ gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ∧
      ‖c‖ * |x.2| ≤ gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) := by
  refine ⟨gN_sub k r' _ g (conj_gg k r' c g x hHA), ?_, cs_le k r' c x _ (conj_cb k r' c g x hHA)⟩
  refine (pi_norm_le_iff_of_nonneg (gN_nonneg' k _)).2 fun i => ?_
  rw [← conj_y k r' c g x hHA i]
  exact gN_entry k _ _ _

theorem pt_un (hHA : HeisAct) :
    gN g ≤ gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ∧
      ‖c‖ * ‖x.1‖ ≤ gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ∧
      ‖c‖ * |x.2| ≤ gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) := by
  refine ⟨gN_sub k r' _ g (un_gg k r' c g x hHA), ?_, cs_le k r' c x _ (un_cb k r' c g x hHA)⟩
  rw [← norm_smul]
  refine (pi_norm_le_iff_of_nonneg (gN_nonneg' k _)).2 fun i => ?_
  obtain ⟨j, hj⟩ := exists_perm k r' x.1 i
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, ← hj, ← norm_mul, ← norm_neg, ← un_row k r' c g x hHA j]
  exact gN_entry k _ _ _

end bounds

end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem pt_bound {N a u v p q : ℝ} (ha : 0 < a) (hu : 0 ≤ u) (hv : 0 ≤ v) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h1 : a ≤ N) (h2 : u ≤ N) (h3 : v ≤ N) :
    N ^ (-(p + q)) ≤ 2 ^ (p + q) * ((a + u) ^ (-p) * (a + v) ^ (-q)) := by
  have hN : 0 < N := lt_of_lt_of_le ha h1
  have hau : 0 < a + u := by linarith
  have hav : 0 < a + v := by linarith
  have hmono : ∀ {x e : ℝ}, 0 < x → x ≤ 2 * N → 0 ≤ e → (2 * N) ^ (-e) ≤ x ^ (-e) := by
    intro x e hx hxN he
    rw [Real.rpow_neg (by linarith), Real.rpow_neg hx.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hx e) (Real.rpow_le_rpow hx.le hxN he)
  have e1 : (2 * N) ^ (-p) ≤ (a + u) ^ (-p) := hmono hau (by linarith) hp
  have e2 : (2 * N) ^ (-q) ≤ (a + v) ^ (-q) := hmono hav (by linarith) hq
  have key : 2 ^ (p + q) * ((2 * N) ^ (-p) * (2 * N) ^ (-q)) = N ^ (-(p + q)) := by
    rw [← Real.rpow_add (by positivity : (0:ℝ) < 2 * N), Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hN.le,
      ← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2), show p + q + (-p + -q) = (0:ℝ) by ring,
      Real.rpow_zero, one_mul, neg_add]
  rw [← key]
  exact mul_le_mul_of_nonneg_left (mul_le_mul e1 e2 (by positivity) (by positivity)) (by positivity)

theorem liftVec_cont (k r' : ℕ) : Continuous fun y : Fin (2 * r' + k + 1) → ℂ => liftVec k 1 r' y := by
  apply continuous_pi
  intro p
  simp only [liftVec]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

def heisM (k r' : ℕ) : HPar k r' → Mt k (1 + r') := fun x => heis0 k r' x

theorem heisenberg_map_continuous (k r' : ℕ) : Continuous (heisM k r') := by
  have hl := liftVec_cont k r'
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [heisM, heis0, heisG, hb, herm, Matrix.add_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec, Pi.star_apply]
  fun_prop

theorem heisenberg_at_zero (k r' : ℕ) : heis0 k r' (0, 0) = 1 := by
  have hz : liftVec k 1 r' 0 = 0 := by
    funext p
    simp only [liftVec, Pi.zero_apply]
    split_ifs <;> rfl
  ext i j
  simp [heis0, heisG, hb, herm, hz, Matrix.vecMulVec]

theorem ιLev_inv_mul (hCL : HeisConjLev) (k r' : ℕ) (g : Mat k r') (hg : g ∈ GV k r') :
    (ιLev k 1 r' g)⁻¹ * ιLev k 1 r' g = 1 := by
  have h := hCL k r' g hg (0, 0)
  simp only [heisenberg_at_zero, mul_one, Matrix.mulVec_zero] at h
  first
  | exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse h)
  | exact mul_eq_one_comm.mp h
  | exact (Matrix.mul_eq_one_comm).1 h

theorem gN_cont (k n : ℕ) : Continuous fun M : Mat k n => gN M := by
  simp only [gN]
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))

theorem int_conj (hCL : HeisConjLev) (hCM : HeisConjLevMeas) (k r' : ℕ) (A : ℝ) (c : ℂ) (g : Mat k r')
    (hg : g ∈ GV k r') :
    ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A)) =
      ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ^ (-A)) := by
  have hinv : (ιLev k 1 r' g)⁻¹ * ιLev k 1 r' g = 1 := ιLev_inv_mul hCL k r' g hg
  have hgN := gN_cont k (1 + r')
  have hcm : Continuous fun M : Mt k (1 + r') => w0 k r' c * Matrix.of M * ιLev k 1 r' g :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hH : Measurable fun M : Mt k (1 + r') =>
      ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)) :=
    ((hgN.comp hcm).measurable.pow_const _).ennreal_ofReal
  have hcc : Continuous (conjM (ιLev k 1 r' g) : Mt k (1 + r') → Mt k (1 + r')) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hconj : Measurable (conjM (ιLev k 1 r' g) : Mt k (1 + r') → Mt k (1 + r')) := hcc.measurable
  have hheis : Measurable (heisM k r') := (heisenberg_map_continuous k r').measurable
  have hL : ∀ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A)) =
      (fun M : Mt k (1 + r') => ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)))
        (conjM (ιLev k 1 r' g) (heis0 k r' x)) := by
    intro x
    have e : w0 k r' c * Matrix.of (conjM (ιLev k 1 r' g) (heis0 k r' x)) * ιLev k 1 r' g =
        w0 k r' c * ιLev k 1 r' g * heis0 k r' x := by
      change w0 k r' c * (ιLev k 1 r' g * heis0 k r' x * (ιLev k 1 r' g)⁻¹) * ιLev k 1 r' g =
        w0 k r' c * ιLev k 1 r' g * heis0 k r' x
      simp only [mul_assoc, hinv, mul_one]
    simp only [e]
  calc ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A))
      = ∫⁻ x : HPar k r', (fun M : Mt k (1 + r') =>
          ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)))
            (conjM (ιLev k 1 r' g) (heis0 k r' x)) := lintegral_congr fun x => hL x
    _ = ∫⁻ M, (fun M : Mt k (1 + r') =>
          ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)))
            (conjM (ιLev k 1 r' g) M) ∂(μHeis k r') := (lintegral_map (hH.comp hconj) hheis).symm
    _ = ∫⁻ M, ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A))
          ∂((μHeis k r').map (conjM (ιLev k 1 r' g))) := (lintegral_map hH hconj).symm
    _ = ∫⁻ M, ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)) ∂(μHeis k r') := by
          rw [hCM k r' g hg]
    _ = ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * Matrix.of (heis0 k r' x : Mt k (1 + r')) * ιLev k 1 r' g) ^ (-A)) :=
          lintegral_map hH hheis
    _ = _ := rfl

theorem int_prod (k r' : ℕ) {A p q K₁ K₂ e₁ e₂ : ℝ} (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (hK₁ : ∀ a b : ℝ, 0 < a → 0 < b → ∫⁻ y : Fin (2 * r' + k + 1) → ℂ, ENNReal.ofReal ((a + b * ‖y‖) ^ (-p)) ≤
      ENNReal.ofReal (K₁ * a ^ (-p) * (a / b) ^ e₁))
    (hK₂ : ∀ a b : ℝ, 0 < a → 0 < b → ∫⁻ s : ℝ, ENNReal.ofReal ((a + b * ‖s‖) ^ (-q)) ≤
      ENNReal.ofReal (K₂ * a ^ (-q) * (a / b) ^ e₂))
    (F : HPar k r' → ℝ≥0∞) {a b₁ b₂ : ℝ} (ha : 0 < a) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hF : ∀ x : HPar k r', F x ≤
      ENNReal.ofReal (2 ^ A * ((a + b₁ * ‖x.1‖) ^ (-p) * (a + b₂ * ‖x.2‖) ^ (-q)))) :
    ∫⁻ x, F x ≤ ENNReal.ofReal (2 ^ A * (K₁ * a ^ (-p) * (a / b₁) ^ e₁) * (K₂ * a ^ (-q) * (a / b₂) ^ e₂)) := by
  have hf₁ : Measurable fun y : Fin (2 * r' + k + 1) → ℂ => ENNReal.ofReal ((a + b₁ * ‖y‖) ^ (-p)) :=
    ((measurable_const.add (measurable_const.mul measurable_norm)).pow_const _).ennreal_ofReal
  have hf₂ : Measurable fun s : ℝ => ENNReal.ofReal ((a + b₂ * ‖s‖) ^ (-q)) :=
    ((measurable_const.add (measurable_const.mul measurable_norm)).pow_const _).ennreal_ofReal
  have hX : 0 ≤ K₁ * a ^ (-p) * (a / b₁) ^ e₁ :=
    mul_nonneg (mul_nonneg hK₁0 (Real.rpow_nonneg ha.le _)) (Real.rpow_nonneg (div_pos ha hb₁).le _)
  have h2A : (0 : ℝ) ≤ 2 ^ A := by positivity
  calc ∫⁻ x, F x ≤ ∫⁻ x : HPar k r', ENNReal.ofReal (2 ^ A) *
        (ENNReal.ofReal ((a + b₁ * ‖x.1‖) ^ (-p)) * ENNReal.ofReal ((a + b₂ * ‖x.2‖) ^ (-q))) := by
        refine lintegral_mono fun x => (hF x).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul h2A, ENNReal.ofReal_mul (Real.rpow_nonneg
          (add_nonneg ha.le (mul_nonneg hb₁.le (norm_nonneg _))) _)]
    _ = ENNReal.ofReal (2 ^ A) * ((∫⁻ y : Fin (2 * r' + k + 1) → ℂ, ENNReal.ofReal ((a + b₁ * ‖y‖) ^ (-p))) *
          ∫⁻ s : ℝ, ENNReal.ofReal ((a + b₂ * ‖s‖) ^ (-q))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_prod_mul (μ := (volume : Measure (Fin (2 * r' + k + 1) → ℂ)))
          (ν := (volume : Measure ℝ)) hf₁.aemeasurable hf₂.aemeasurable
    _ ≤ ENNReal.ofReal (2 ^ A) * (ENNReal.ofReal (K₁ * a ^ (-p) * (a / b₁) ^ e₁) *
          ENNReal.ofReal (K₂ * a ^ (-q) * (a / b₂) ^ e₂)) := by
        gcongr
        · exact hK₁ a b₁ ha hb₁
        · exact hK₂ a b₂ ha hb₂
    _ = _ := by
        rw [← ENNReal.ofReal_mul hX, ← ENNReal.ofReal_mul h2A]
        congr 1
        ring

theorem eInt_bound' (hGL : GNLower) (hHA : HeisAct) (hCL : HeisConjLev) (hCM : HeisConjLevMeas)
    (k r' : ℕ) (A : ℝ) (hA : ((4 * r' + 2 * k + 3 : ℕ) : ℝ) < A) :
    ∃ C : ℝ, ∀ c : ℂ, c ≠ 0 → ∀ g ∈ GV k r',
      ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A)) ≤
        ENNReal.ofReal (C * min (‖c‖ ^ (-((4 * r' + 2 * k + 3 : ℕ) : ℝ))) ‖c‖⁻¹ *
          gN g ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A)) := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = ((4 * r' + 2 * k + 3 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hd] at hA ⊢
  have hd3 : (3 : ℝ) ≤ d := by rw [hd]; norm_cast; omega
  have hE : (Module.finrank ℝ (Fin (2 * r' + k + 1) → ℂ) : ℝ) = d - 1 := by
    rw [Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    rw [hd]; push_cast; ring
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = d - 1 + (A - d) / 2 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 + (A - d) / 2 := ⟨_, rfl⟩
  have hpq : p + q = A := by rw [hp, hq]; ring
  have hp0 : 0 ≤ p := by rw [hp]; linarith
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  obtain ⟨K₁, hK₁0, hK₁⟩ := scale_int (volume : Measure (Fin (2 * r' + k + 1) → ℂ)) (r := p)
    (by rw [hE, hp]; linarith)
  obtain ⟨K₂, hK₂0, hK₂⟩ := scale_int (volume : Measure ℝ) (r := q)
    (by simp only [Module.finrank_self, Nat.cast_one]; rw [hq]; linarith)
  rw [hE] at hK₁
  simp only [Module.finrank_self, Nat.cast_one] at hK₂
  refine ⟨2 ^ A * K₁ * K₂, fun c hc g hg => ?_⟩
  have ha : 0 < gN g := lt_of_lt_of_le zero_lt_one (hGL k r' g hg)
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  have B1 := int_prod k r' hK₁0 hK₂0 hK₁ hK₂
    (fun x => ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A))) ha hc0 hc0
    (fun x => by
      obtain ⟨h1, h2, h3⟩ := pt_un k r' c g x hHA
      rw [← Real.norm_eq_abs] at h3
      have := pt_bound ha (mul_nonneg hc0.le (norm_nonneg _)) (mul_nonneg hc0.le (norm_nonneg _))
        hp0 hq0 h1 h2 h3
      rw [hpq] at this
      exact ENNReal.ofReal_le_ofReal this)
  have B2 := int_prod k r' hK₁0 hK₂0 hK₁ hK₂
    (fun x => ENNReal.ofReal (gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ^ (-A))) ha one_pos hc0
    (fun x => by
      obtain ⟨h1, h2, h3⟩ := pt_conj k r' c g x hHA
      rw [← Real.norm_eq_abs] at h3
      rw [← one_mul ‖x.1‖] at h2
      have := pt_bound ha (by positivity) (mul_nonneg hc0.le (norm_nonneg _)) hp0 hq0 h1 h2 h3
      rw [hpq] at this
      exact ENNReal.ofReal_le_ofReal this)
  rw [← int_conj hCL hCM k r' A c g hg] at B2
  have ea : gN g ^ (d - A) = gN g ^ (-p) * gN g ^ (d - 1) * gN g ^ (-q) * gN g ^ (1 : ℝ) := by
    rw [← Real.rpow_add ha, ← Real.rpow_add ha, ← Real.rpow_add ha]
    congr 1
    linarith
  have E1 : 2 ^ A * (K₁ * gN g ^ (-p) * (gN g / ‖c‖) ^ (d - 1)) * (K₂ * gN g ^ (-q) * (gN g / ‖c‖) ^ (1 : ℝ)) =
      2 ^ A * K₁ * K₂ * ‖c‖ ^ (-d) * gN g ^ (d - A) := by
    have ec : ‖c‖ ^ (-d) = ‖c‖ ^ (-(d - 1)) * ‖c‖ ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; ring
    rw [Real.div_rpow ha.le hc0.le, Real.div_rpow ha.le hc0.le, ea, ec, Real.rpow_neg hc0.le,
      Real.rpow_neg hc0.le]
    ring
  have E2 : 2 ^ A * (K₁ * gN g ^ (-p) * (gN g / 1) ^ (d - 1)) * (K₂ * gN g ^ (-q) * (gN g / ‖c‖) ^ (1 : ℝ)) =
      2 ^ A * K₁ * K₂ * ‖c‖⁻¹ * gN g ^ (d - A) := by
    rw [div_one, Real.div_rpow ha.le hc0.le, ea, Real.rpow_one, Real.rpow_one]
    ring
  rcases le_total (‖c‖ ^ (-d)) ‖c‖⁻¹ with h | h
  · rw [min_eq_left h, ← E1]; exact B1
  · rw [min_eq_right h, ← E2]; exact B2

end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def EInt (k r' : ℕ) (A : ℝ) (c : ℂ) (g : Mat k r') : ℝ≥0∞ :=
  ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A))

theorem eInt_bound (hGL : GNLower) (hHA : HeisAct) (hHC : HeisClosed) (hCL : HeisConjLev) (hCM : HeisConjLevMeas)
    (k r' : ℕ) (hk : 1 ≤ k) (A : ℝ) (hA : ((4 * r' + 2 * k + 3 : ℕ) : ℝ) < A) :
    ∃ C : ℝ, ∀ c : ℂ, c ≠ 0 → ∀ g ∈ GV k r',
      EInt k r' A c g ≤ ENNReal.ofReal (C * min (‖c‖ ^ (-((4 * r' + 2 * k + 3 : ℕ) : ℝ))) ‖c‖⁻¹ *
        gN g ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A)) := by
  exact ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.eInt_bound' hGL hHA hCL hCM k r' A hA

theorem cInt_fin (n : ℕ) (σ : ℝ) (h1 : 1 < σ) (h2 : σ < 2 * (n : ℝ) + 1) :
    (∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (n : ℝ) - σ)) *
      ENNReal.ofReal (min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹)) < ∞ := by
  have hF0 : IntegrableOn (fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)) (Set.Ioc 0 1) := by
    refine Integrable.mono'
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := 2 * (n : ℝ) - σ)
        (by linarith)).1 ?_ ?_
    · first
        | exact (by measurability : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
        | exact (by fun_prop : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun y hy => ?_)
      have hy0 : 0 < y := hy.1
      have hA : 0 ≤ y ^ (2 * (n : ℝ) - σ) := Real.rpow_nonneg hy0.le _
      have hmin : 0 ≤ min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹ := le_min (Real.rpow_nonneg hy0.le _) (inv_nonneg.2 hy0.le)
      rw [Real.norm_of_nonneg (mul_nonneg hy0.le (mul_nonneg hA hmin))]
      calc y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹) ≤ y * (y ^ (2 * (n : ℝ) - σ) * y⁻¹) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_right _ _) hA) hy0.le
        _ = y ^ (2 * (n : ℝ) - σ) := by rw [mul_comm, mul_assoc, inv_mul_cancel₀ hy0.ne', mul_one]
  have hF1 : IntegrableOn (fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)) (Set.Ioi 1) := by
    refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := -σ) (by linarith) zero_lt_one) ?_ ?_
    · first
        | exact (by measurability : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
        | exact (by fun_prop : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun y hy => ?_)
      have hy0 : 0 < y := zero_lt_one.trans hy
      have hA : 0 ≤ y ^ (2 * (n : ℝ) - σ) := Real.rpow_nonneg hy0.le _
      have hmin : 0 ≤ min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹ := le_min (Real.rpow_nonneg hy0.le _) (inv_nonneg.2 hy0.le)
      rw [Real.norm_of_nonneg (mul_nonneg hy0.le (mul_nonneg hA hmin))]
      calc y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹) ≤ y * (y ^ (2 * (n : ℝ) - σ) * y ^ (-((2 * n + 1 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_left _ _) hA) hy0.le
        _ = y ^ (-σ) := by
          rw [← mul_assoc, mul_comm y, ← Real.rpow_add_one hy0.ne', ← Real.rpow_add hy0]
          congr 1
          push_cast
          ring
  have hY : IntegrableOn (fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)) (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact hF0.union hF1
  have hI : Integrable (fun c : ℂ => ‖c‖ ^ (2 * (n : ℝ) - σ) *
      min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹) volume := by
    first
      | exact (integrable_fun_norm_addHaar volume
          (f := fun y : ℝ => (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹))).2 (hY.congr_fun (fun y _ => by simp) measurableSet_Ioi)
      | exact (integrable_fun_norm_addHaar (μ := volume)
          (f := fun y : ℝ => (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹))).2 (hY.congr_fun (fun y _ => by simp) measurableSet_Ioi)
  calc (∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (n : ℝ) - σ)) *
        ENNReal.ofReal (min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹))
      = ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (n : ℝ) - σ) *
          min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹) :=
        lintegral_congr fun c => (ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)).symm
    _ < ∞ := hI.lintegral_lt_top

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem heisenbergFacts_of_inductiveInput (h : InductiveHeisenbergInputs) : OneStepInt ∧ OneStepCoord ∧ HeisConjLev ∧ HeisInv ∧ HeisMem ∧ HeisHaar ∧
    HaarGExists ∧ HeisAct ∧ GNLower ∧ HeisClosed ∧ HeisConjLevMeas := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27⟩ := h
  exact ⟨h1, h2, h6, h8, h10, h12, h26, h27, h16, h11, h7⟩

section cont
variable (k r' : ℕ)

theorem lift_cont : Continuous (liftVec k 1 r') := by
  refine continuous_pi fun p => ?_
  unfold liftVec
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · simp only [dif_pos hp]; exact continuous_apply _
  · simp only [dif_neg hp]; exact continuous_const

theorem heisenberg_map_continuous : Continuous (heis0 k r') := by
  have h1 : Continuous fun x : HPar k r' => liftVec k 1 r' x.1 := (lift_cont k r').comp continuous_fst
  unfold heis0 heisG hb herm
  fun_prop

theorem lev_cont : Continuous (fun g : Mat k r' => ιLev k 1 r' g) := by
  refine continuous_matrix fun p q => ?_
  unfold ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
    · simp only [dif_pos hp, dif_pos hq]; exact continuous_id.matrix_elem _ _
    · simp only [dif_pos hp, dif_neg hq]; exact continuous_const
  · simp only [dif_neg hp]; exact continuous_const

theorem Dl_cont (r : ℕ) (l : Fin (r + 1)) : Continuous (fun g : Mt k r => Dl k r l (Matrix.of g)) := by
  unfold Dl herm
  fun_prop

theorem FsE_meas (r : ℕ) (s : Fin (r + 1) → ℝ) : Measurable (fun g : Mt k r => FsE k r s (Matrix.of g)) := by
  unfold FsE
  exact Finset.measurable_prod _ fun l _ =>
    ((Dl_cont k r l).measurable.nnnorm.coe_nnreal_ennreal).pow_const _

theorem EInt_meas (A : ℝ) (c : ℂ) : Measurable (fun g : Mt k r' => EInt k r' A c (Matrix.of g)) := by
  unfold EInt
  have h1 := heisenberg_map_continuous k r'
  have h2 := lev_cont k r'
  have h3 := gN_cont k (1 + r')
  refine Measurable.lintegral_prod_right'
    (f := fun p : Mt k r' × HPar k r' =>
      ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' (Matrix.of p.1) * heis0 k r' p.2) ^ (-A))) ?_
  exact ((by fun_prop : Continuous fun p : Mt k r' × HPar k r' =>
    gN (w0 k r' c * ιLev k 1 r' (Matrix.of p.1) * heis0 k r' p.2)).measurable.pow_const _).ennreal_ofReal

theorem heis_left (hHH : HeisHaar) (F : Mt k (1 + r') → ℝ≥0∞) (hF : Measurable F) (z : HPar k r') :
    ∫⁻ x, F (heis0 k r' z * heis0 k r' x) = ∫⁻ x, F (heis0 k r' x) := by
  have hc : @Continuous (HPar k r') (Mt k (1 + r')) _ _ (fun x => heis0 k r' x) := heisenberg_map_continuous k r'
  have hm : @Measurable (HPar k r') (Mt k (1 + r')) _ _ (fun x => heis0 k r' x) := hc.measurable
  have hl : Measurable (lmulM (heis0 k r' z) : Mt k (1 + r') → Mt k (1 + r')) :=
    (by unfold lmulM; fun_prop : Continuous (lmulM (heis0 k r' z) : Mt k (1 + r') → Mt k (1 + r'))).measurable
  calc ∫⁻ x, F (heis0 k r' z * heis0 k r' x) = ∫⁻ n, F (lmulM (heis0 k r' z) n) ∂(μHeis k r') := by
        rw [μHeis]; exact (lintegral_map (hF.comp hl) hm).symm
    _ = ∫⁻ n, F n ∂((μHeis k r').map (lmulM (heis0 k r' z))) := (lintegral_map hF hl).symm
    _ = ∫⁻ n, F n ∂(μHeis k r') := by rw [(hHH k r').left _ ⟨z, rfl⟩]
    _ = ∫⁻ x, F (heis0 k r' x) := by rw [μHeis]; exact lintegral_map hF hm

theorem EInt_K (A : ℝ) (c : ℂ) {κ : Mat k r'} (hκ : κ ∈ Kset k r') (g : Mat k r') :
    EInt k r' A c (κ * g) = EInt k r' A c g := by
  unfold EInt
  refine lintegral_congr fun x => ?_
  have e : w0 k r' c * ιLev k 1 r' (κ * g) * heis0 k r' x =
      ιLev k 1 r' κ * (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) := by
    rw [lev_mul, ← Matrix.mul_assoc (w0 k r' c), rankOne_levi_comm]; simp only [Matrix.mul_assoc]
  rw [e, gN_unitary k (1 + r') (lev_K k r' hκ).2]

end cont

section inner
variable (k r' : ℕ)

def Dx (x : HPar k r') : ℝ := Real.sqrt (Ga k (1 + r') 0 (Yx k r' x))

def Psi (s : Fin (1 + r' + 1) → ℝ) (x : HPar k r') : ℝ :=
  ∏ l : Fin (r' + 1), (Ga k (1 + r') (sc r' l) (Yx k r' x) / Ga k (1 + r') 0 (Yx k r' x)) ^ (-s (sc r' l) / 2)

def Qf (A : ℝ) (s1 : Fin (r' + 1) → ℝ) (μ₁ : Measure (Mt k r')) (c : ℂ) : ℝ≥0∞ :=
  ∫⁻ g, EInt k r' A c (Matrix.of g) * FsE k r' s1 (Matrix.of g) ∂μ₁

theorem inner_eq (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hT : TLeft) (hk : 1 ≤ k) (A : ℝ) (s : Fin (1 + r' + 1) → ℝ)
    (μ₁ : Measure (Mt k r')) (hμ₁ : IsHaarOn (GV k r') μ₁) (x : HPar k r') (c : ℂ) (hc : c ≠ 0) :
    ∫⁻ g, (∫⁻ x', ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A))) *
        FsE k r' (fun l => s (sc r' l)) (Matrix.of g) ∂μ₁ =
      ENNReal.ofReal (Psi k r' s x) * Qf k r' A (fun l => s (sc r' l)) μ₁ (c * (Dx k r' x : ℂ)) := by
  obtain ⟨-, -, hHCL, -, -, hHH, -, -, -, -, -⟩ := heisenbergFacts_of_inductiveInput hB2
  obtain ⟨κ, hκ, m, hm, z, hdec, hga⟩ := heisenberg_rankOne_decomposition hB2 hIW k r' hk x c hc
  have hG0 := (yx_ga hB2 hIW k r' hk x).1
  have hdec' : (heis0 k r' x)⁻¹ * w0 k r' c =
      κ * w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' m * heis0 k r' z := hdec
  have hpt : ∀ g : Mt k r', Matrix.of g ∈ GV k r' →
      ∫⁻ x', ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A)) =
        EInt k r' A (c * (Dx k r' x : ℂ)) (m * Matrix.of g) := by
    intro g hg
    obtain ⟨z2, hz2⟩ : ∃ z2 : HPar k r', z2 = ((Matrix.of g)⁻¹ *ᵥ z.1, z.2) := ⟨_, rfl⟩
    have hcomm : heis0 k r' z * ιLev k 1 r' (Matrix.of g) = ιLev k 1 r' (Matrix.of g) * heis0 k r' z2 := by
      have h1 := hHCL k r' (Matrix.of g) hg z2
      have h2 : ((Matrix.of g *ᵥ z2.1, z2.2) : HPar k r') = z := by
        rw [hz2]; dsimp only; rw [mulVec_mulVec, UH_mul_inv k r' hg, one_mulVec]
      rw [h2] at h1
      rw [← h1, Matrix.mul_assoc, UH_inv_mul k (1 + r') (lev_mem k r' hg), Matrix.mul_one]
    have hmat : ∀ x', oneStep k r' x c (Matrix.of g) x' =
        κ * (w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' (m * Matrix.of g) * (heis0 k r' z2 * heis0 k r' x')) := by
      intro x'
      unfold oneStep
      rw [hdec', Matrix.mul_assoc (κ * w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' m) (heis0 k r' z)
        (ιLev k 1 r' (Matrix.of g)), hcomm, lev_mul]
      simp only [Matrix.mul_assoc]
    simp only [hmat, gN_unitary k (1 + r') hκ.2]
    have h3 := gN_cont k (1 + r')
    have hF : Measurable fun n : Mt k (1 + r') =>
        ENNReal.ofReal (gN (w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' (m * Matrix.of g) * Matrix.of n) ^ (-A)) :=
      ((by fun_prop : Continuous fun n : Mt k (1 + r') =>
        gN (w0 k r' (c * (Dx k r' x : ℂ)) * ιLev k 1 r' (m * Matrix.of g) * Matrix.of n)).measurable.pow_const
          _).ennreal_ofReal
    exact heis_left k r' hHH _ hF z2
  have hconc : ∀ᵐ g ∂μ₁, Matrix.of g ∈ GV k r' := by
    rw [ae_iff]; exact hμ₁.conc
  have hl : Measurable (lmulM m : Mt k r' → Mt k r') :=
    (by unfold lmulM; fun_prop : Continuous (lmulM m : Mt k r' → Mt k r')).measurable
  have hli : Measurable (lmulM m⁻¹ : Mt k r' → Mt k r') :=
    (by unfold lmulM; fun_prop : Continuous (lmulM m⁻¹ : Mt k r' → Mt k r')).measurable
  have hG : Measurable (fun g : Mt k r' => EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of g) *
      FsE k r' (fun l => s (sc r' l)) (m⁻¹ * Matrix.of g)) :=
    (EInt_meas k r' A _).mul ((FsE_meas k r' (fun l => s (sc r' l))).comp hli)
  have e : ∀ g : Mt k r', m⁻¹ * (m * Matrix.of g) = Matrix.of g := fun g => by
    rw [← Matrix.mul_assoc, UH_inv_mul k r' hm, Matrix.one_mul]
  calc ∫⁻ g, (∫⁻ x', ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A))) *
        FsE k r' (fun l => s (sc r' l)) (Matrix.of g) ∂μ₁
      = ∫⁻ g, EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of (lmulM m g)) *
          FsE k r' (fun l => s (sc r' l)) (m⁻¹ * Matrix.of (lmulM m g)) ∂μ₁ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hconc] with g hg
        rw [hpt g hg]
        show _ = EInt k r' A (c * (Dx k r' x : ℂ)) (m * Matrix.of g) *
          FsE k r' (fun l => s (sc r' l)) (m⁻¹ * (m * Matrix.of g))
        rw [e]
    _ = ∫⁻ g, EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of g) *
          FsE k r' (fun l => s (sc r' l)) (m⁻¹ * Matrix.of g) ∂(μ₁.map (lmulM m)) := (lintegral_map hG hl).symm
    _ = ∫⁻ g, EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of g) *
          FsE k r' (fun l => s (sc r' l)) (m⁻¹ * Matrix.of g) ∂μ₁ := by rw [hμ₁.left m hm]
    _ = ENNReal.ofReal (fsR k r' (fun l => s (sc r' l)) m) *
          Qf k r' A (fun l => s (sc r' l)) μ₁ (c * (Dx k r' x : ℂ)) :=
        hT k r' (fun l => s (sc r' l)) μ₁ (fun g => EInt k r' A (c * (Dx k r' x : ℂ)) (Matrix.of g)) hk hμ₁
          (EInt_meas k r' A _) (fun κ' hκ' g => EInt_K k r' A _ hκ' (Matrix.of g)) m hm
    _ = ENNReal.ofReal (Psi k r' s x) * Qf k r' A (fun l => s (sc r' l)) μ₁ (c * (Dx k r' x : ℂ)) := by
        congr 1; congr 1
        unfold fsR Psi
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [eq_div_of_mul_eq hG0.ne' (hga l)]

end inner

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
