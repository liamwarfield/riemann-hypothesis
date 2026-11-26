module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilpotentChartRightInverse
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.OpnContinuous

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerShearHaar.MeasurePreservingOfCard
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerShearHaar.TriShear
open MeasureTheory

namespace PI.LowSplitHaarW

def TriShear : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (r : ι → ℕ) (g : ι → (ι → ℂ) → ℂ),
    (∀ i, Measurable (g i)) →
    (∀ i (x y : ι → ℂ), (∀ j, r j < r i → x j = y j) → g i x = g i y) →
    MeasurePreserving (fun x : ι → ℂ => fun i => x i + g i x) volume volume

end PI.LowSplitHaarW
end

open MeasureTheory

noncomputable section

namespace PI.LowSplitHaarW

def extNe {ι : Type} [DecidableEq ι] (a : ι) (y : {i // i ≠ a} → ℂ) : ι → ℂ :=
  fun j => if h : j ≠ a then y ⟨j, h⟩ else 0

theorem measurable_extNe {ι : Type} [DecidableEq ι] (a : ι) : Measurable (extNe a) := by
  refine Measurable.of_eval fun j => ?_
  by_cases h : j ≠ a
  · simp only [extNe, dif_pos h]
    exact measurable_pi_apply _
  · simp only [extNe, dif_neg h]
    exact measurable_const

theorem measurePreserving_of_card (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ (r : ι → ℕ) (g : ι → (ι → ℂ) → ℂ), (∀ i, Measurable (g i)) →
    (∀ i (x y : ι → ℂ), (∀ j, r j < r i → x j = y j) → g i x = g i y) →
    MeasurePreserving (fun x : ι → ℂ => fun i => x i + g i x) volume volume := by
  induction n with
  | zero =>
    intro ι _ _ hcard r g _ _
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.1 hcard
    have : (fun x : ι → ℂ => fun i => x i + g i x) = id := by
      funext x i
      exact isEmptyElim i
    rw [this]
    exact MeasurePreserving.id _
  | succ n ih =>
    intro ι _ _ hcard r g hg hdep
    haveI : Nonempty ι := Fintype.card_pos_iff.1 (by omega)

    obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
    have hja : ∀ i j, r j < r i → j ≠ a := by
      rintro i j hj rfl
      exact absurd (ha i (Finset.mem_univ _)) (not_le.2 hj)
    have hext : ∀ (x : ι → ℂ) (i : ι), g i x = g i (extNe a (fun j : {j // j ≠ a} => x j)) := by
      intro x i
      refine hdep i _ _ fun j hj => ?_
      simp [extNe, hja i j hj]
    have hcard' : Fintype.card {j // j ≠ a} = n := by
      simp [Fintype.card_subtype_compl, hcard]

    have hF := ih {j // j ≠ a} hcard' (fun j => r j) (fun j y => g j (extNe a y))
      (fun j => (hg j).comp (measurable_extNe a)) (by
        intro j y z hyz
        refine hdep j _ _ fun l hl => ?_
        by_cases h : l ≠ a
        · simp only [extNe, dif_pos h]
          exact hyz ⟨l, h⟩ hl
        · simp only [extNe, dif_neg h])
    let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun j => j ≠ a)
    have he : MeasurePreserving e volume volume :=
      volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun j => j ≠ a)

    have hG := hF.skew_product (g := fun y (z : {j // ¬ j ≠ a} → ℂ) => fun q => z q + g a (extNe a y))
      (by
        refine Measurable.of_eval fun q => ?_
        exact ((measurable_pi_apply q).comp measurable_snd).add
          ((hg a).comp ((measurable_extNe a).comp measurable_fst)))
      (Filter.Eventually.of_forall fun y =>
        (measurePreserving_add_right (volume : Measure ({j // ¬ j ≠ a} → ℂ))
          (fun _ => g a (extNe a y))).map_eq)
    have key : (fun x : ι → ℂ => fun i => x i + g i x) =
        e.symm ∘ (fun p => ((fun i : {j // j ≠ a} => p.1 i + g i (extNe a p.1)),
          fun q : {j // ¬ j ≠ a} => p.2 q + g a (extNe a p.1))) ∘ e := by
      funext x i
      by_cases h : i ≠ a
      · simp [e, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hext x i]
      · have h' : i = a := not_not.1 h
        subst h'
        simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hext x i]
    rw [key]
    exact he.symm.comp (hG.comp he)

theorem triShear : TriShear := by
  intro ι _ _ r g hg hdep
  exact measurePreserving_of_card (Fintype.card ι) ι rfl r g hg hdep

end PI.LowSplitHaarW
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NShear
open Matrix Formalism.QuantumDeterminants MeasureTheory

noncomputable section

namespace WlocSk.NB

variable {k r : ℕ}

def rk : CI k r → ℕ
  | Sum.inl p => r - p.1.1.val
  | Sum.inr (Sum.inl q) => r - q.1.val
  | Sum.inr (Sum.inr _) => r + 1

def dlt (m₀ : Mx k r) (x : CI k r → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  (cF x)ᴴ * ((bF m₀)ᴴ * (bB m₀ * cE x + bC m₀ * cF x))

def shG (m₀ : Mx k r) (x : CI k r → ℂ) : CI k r → ℂ
  | Sum.inl p => ∑ c, if p.1.1 < c then bA m₀ p.1.1 c * cA x c p.1.2 else 0
  | Sum.inr (Sum.inl q) => (∑ c, if q.1 < c then bA m₀ q.1 c * cB x c q.2 else 0) + bB m₀ q.1 q.2
  | Sum.inr (Sum.inr p) => (dlt m₀ x p.1.1 p.1.2 - star (dlt m₀ x p.1.2 p.1.1)) / 2

def shH (m₀ : Mx k r) (x : CI k r → ℂ) : Fin r → ℝ := fun a => (dlt m₀ x a a).im

theorem split_low {A : Matrix (Fin r) (Fin r) ℂ} (hA : LowId A) (v : Fin r → ℂ) (a : Fin r) :
    ∑ c, A a c * v c = v a + ∑ c, if a < c then A a c * v c else 0 := by
  have : ∀ c, A a c * v c = (if a = c then v c else 0) + (if a < c then A a c * v c else 0) := by
    intro c
    rcases lt_trichotomy a c with h | rfl | h
    · rw [if_neg (ne_of_lt h), if_pos h, zero_add]
    · rw [if_pos rfl, if_neg (lt_irrefl a), add_zero, hA a a le_rfl, if_pos rfl, one_mul]
    · rw [if_neg (ne_of_gt h), if_neg (not_lt.2 h.le), add_zero, hA a c h.le, if_neg (ne_of_gt h),
        zero_mul]
  rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_add_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ _)]

theorem lowId_bA {g : Mx k r} (hc : ColB g) : LowId (bA g) := fun a b h => hc.aa a b h

theorem mof_mul {m₀ g : Mx k r} (h0 : m₀ ∈ Nset k r) (hg : g ∈ Nset k r) :
    mof (m₀ * g) = mof g + (bF g)ᴴ * ((bF m₀)ᴴ * (bB m₀ * bE g + bC m₀ * bF g)) := by
  have hc0 := colB_of_mem h0
  have hF0 := rel_F hc0 h0.1
  rw [mof, mof, bF_mul hc0, bC_mul, conjTranspose_mul]
  rw [add_assoc, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add]
  have : (bF g)ᴴ * (bF m₀)ᴴ * (bA m₀ * bC g) = (bF g)ᴴ * bC g := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (bF m₀)ᴴ, hF0, Matrix.one_mul]
  rw [this]
  simp only [Matrix.mul_assoc, Matrix.mul_add]

theorem lmul_coord {m₀ : Mx k r} (h0 : m₀ ∈ Nset k r) (x : CI k r → ℂ) (s : Fin r → ℝ) :
    psiC (m₀ * phi0 x s) = x + shG m₀ x ∧ psiR (m₀ * phi0 x s) = s + shH m₀ x := by
  have hg := test_vector_mem_schwartz_bruhat x s
  have hcg := colB_of_mem hg
  have hc0 := colB_of_mem h0
  have hps := nilpotent_chart_right_inverse x s
  have hM : mof (m₀ * phi0 x s) = mof (phi0 x s) + dlt m₀ x := by
    rw [mof_mul h0 hg, dlt, phi0, bF_mk, bE_mk]
  constructor
  · funext i
    rcases i with ⟨⟨a, b⟩, h⟩ | ⟨a, j⟩ | ⟨⟨a, b⟩, h⟩
    · show bA (m₀ * phi0 x s) a b = _
      rw [bA_mul hcg, Matrix.mul_apply, phi0, bA_mk, split_low (lowId_bA hc0)]
      simp only [Pi.add_apply, shG, cA, dif_pos h]
    · show bB (m₀ * phi0 x s) a j = _
      rw [bB_mul hcg, Matrix.add_apply, Matrix.mul_apply, phi0, bB_mk, split_low (lowId_bA hc0)]
      simp only [Pi.add_apply, shG, cB]
      ring
    · show kof (m₀ * phi0 x s) a b = _
      have e1 : kof (phi0 x s) a b = x (Sum.inr (Sum.inr ⟨(a, b), h⟩)) :=
        congrFun hps.1 (Sum.inr (Sum.inr ⟨(a, b), h⟩))
      simp only [kof, hM, Matrix.add_apply, Pi.add_apply, shG, star_add] at e1 ⊢
      rw [← e1]
      ring
  · funext a
    have e1 : (mof (phi0 x s) a a).im = s a := congrFun hps.2 a
    show (mof (m₀ * phi0 x s) a a).im = _
    rw [hM, Matrix.add_apply, Complex.add_im, e1]
    rfl

theorem shG_dep (m₀ : Mx k r) (i : CI k r) (x y : CI k r → ℂ)
    (hxy : ∀ j, rk j < rk i → x j = y j) : shG m₀ x i = shG m₀ y i := by
  have hAB : (∀ j, rk j ≤ r → x j = y j) → cA x = cA y ∧ cB x = cB y := by
    intro h
    refine ⟨?_, ?_⟩
    · ext a b; unfold cA; split_ifs with h1
      · exact h _ (by simp only [rk]; omega)
      · rfl
      · rfl
    · ext a j; exact h _ (by simp only [rk]; omega)
  rcases i with ⟨⟨a, b⟩, h⟩ | ⟨a, j⟩ | ⟨⟨a, b⟩, h⟩
  · simp only [shG]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hac
    · congr 1
      unfold cA
      split_ifs with hcb
      · exact hxy _ (by simp only [rk]; have := c.isLt; have : a.val < c.val := hac; omega)
      · rfl
      · rfl
    · rfl
  · simp only [shG]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hac
    · congr 1
      exact hxy _ (by simp only [rk]; have := c.isLt; have : a.val < c.val := hac; omega)
    · rfl
  · obtain ⟨hA, hB⟩ := hAB fun j hj => hxy j (by show rk j < r + 1; omega)
    simp only [shG, dlt, cF, cE, hA, hB]

theorem continuous_dlt (m₀ : Mx k r) : Continuous (dlt m₀) :=
  continuous_cF.matrix_conjTranspose.matrix_mul (continuous_const.matrix_mul
    ((continuous_const.matrix_mul continuous_cE).add (continuous_const.matrix_mul continuous_cF)))

theorem continuous_shG (m₀ : Mx k r) (i : CI k r) : Continuous fun x => shG m₀ x i := by
  rcases i with ⟨⟨a, b⟩, h⟩ | ⟨a, j⟩ | ⟨⟨a, b⟩, h⟩
  · simp only [shG]
    refine continuous_finsetSum _ fun c _ => ?_
    split_ifs
    · exact continuous_const.mul (continuous_cA.matrix_elem _ _)
    · exact continuous_const
  · simp only [shG]
    refine (continuous_finsetSum _ fun c _ => ?_).add continuous_const
    split_ifs
    · exact continuous_const.mul (continuous_cB.matrix_elem _ _)
    · exact continuous_const
  · simp only [shG]
    exact (((continuous_dlt m₀).matrix_elem _ _).sub ((continuous_dlt m₀).matrix_elem _ _).star).div_const _

theorem continuous_shH (m₀ : Mx k r) : Continuous (shH m₀) :=
  continuous_pi fun a => Complex.continuous_im.comp ((continuous_dlt m₀).matrix_elem a a)

theorem shear_mp {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (rkf : ι → ℕ) (G : (ι → ℂ) → ι → ℂ)
    (H : (ι → ℂ) → Fin d → ℝ) (hG : ∀ i, Measurable fun x => G x i)
    (hdep : ∀ i (x y : ι → ℂ), (∀ j, rkf j < rkf i → x j = y j) → G x i = G y i)
    (hH : Measurable H) :
    MeasurePreserving (fun t : (ι → ℂ) × (Fin d → ℝ) => (t.1 + G t.1, t.2 + H t.1)) volume volume := by
  have h1 : MeasurePreserving (fun x : ι → ℂ => fun i => x i + G x i) volume volume :=
    PI.LowSplitHaarW.triShear ι rkf (fun i x => G x i) hG hdep
  have h2 := h1.skew_product (μc := (volume : Measure (Fin d → ℝ))) (μd := volume)
    (g := fun x s => s + H x) (measurable_snd.add (hH.comp measurable_fst))
    (Filter.Eventually.of_forall fun x => map_add_right_eq_self volume (H x))
  exact h2

end WlocSk.NB
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilpotentChartNormBound
open Matrix Formalism.QuantumDeterminants

noncomputable section

namespace WlocSk.NB

variable {k r : ℕ}

theorem opn_nonneg' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.L2.SG.WuDecay.opn M :=
  norm_nonneg _

theorem entry_le_opn {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖M i j‖ ≤ Formalism.L2.SG.WuDecay.opn M := by
  unfold Formalism.L2.SG.WuDecay.opn
  have h1 := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M).le_opNorm
    (EuclideanSpace.single j (1 : ℂ))
  rw [PiLp.norm_single, norm_one, mul_one] at h1
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ i).trans h1)
  rw [Matrix.ofLp_toEuclideanCLM, PiLp.ofLp_single, Matrix.mulVec_single_one, Matrix.col_apply]

theorem one_le_opn {g : Mx k r} (hg : g ∈ Nset k r) : 1 ≤ Formalism.L2.SG.WuDecay.opn g := by
  have h := entry_le_opn g (wI k r 0) (wI k r 0)
  rw [(colB_of_mem hg).ww 0 0, if_pos rfl, norm_one] at h
  exact h

theorem mof_le (g : Mx k r) (a b : Fin r) :
    ‖mof g a b‖ ≤ r * Formalism.L2.SG.WuDecay.opn g ^ 2 := by
  rw [mof, Matrix.mul_apply]
  calc ‖∑ c, (bF g)ᴴ a c * bC g c b‖ ≤ ∑ c, ‖(bF g)ᴴ a c * bC g c b‖ := norm_sum_le _ _
    _ ≤ ∑ _c : Fin r, Formalism.L2.SG.WuDecay.opn g ^ 2 := Finset.sum_le_sum fun c _ => by
        rw [norm_mul, conjTranspose_apply, norm_star, sq]
        exact mul_le_mul (entry_le_opn g (esI k r c) (esI k r a)) (entry_le_opn g (eI k r c) (esI k r b))
          (norm_nonneg _) (opn_nonneg' _)
    _ = r * Formalism.L2.SG.WuDecay.opn g ^ 2 := by simp

theorem kof_le (g : Mx k r) (a b : Fin r) :
    ‖kof g a b‖ ≤ r * Formalism.L2.SG.WuDecay.opn g ^ 2 := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [kof, norm_div, h2]
  have := norm_sub_le (mof g a b) (star (mof g b a))
  rw [norm_star] at this
  have h1 := mof_le g a b
  have h3 := mof_le g b a
  linarith

theorem psiC_le {g : Mx k r} (hg : g ∈ Nset k r) (i : CI k r) :
    ‖psiC g i‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 := by
  set o := Formalism.L2.SG.WuDecay.opn g with ho
  have h1 : 1 ≤ o := one_le_opn hg
  have hoo : o ≤ o ^ 2 := by nlinarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have ho2 : 0 ≤ o ^ 2 := sq_nonneg o
  rcases i with p | q | p
  · have := entry_le_opn g (eI k r p.1.1) (eI k r p.1.2)
    show ‖g _ _‖ ≤ _
    nlinarith
  · have := entry_le_opn g (eI k r q.1) (wI k r q.2)
    show ‖g _ _‖ ≤ _
    nlinarith
  · have := kof_le g p.1.1 p.1.2
    show ‖kof g _ _‖ ≤ _
    nlinarith

theorem psiR_le (g : Mx k r) (a : Fin r) :
    ‖psiR g a‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 := by
  have h := mof_le g a a
  have h' : ‖psiR g a‖ ≤ ‖mof g a a‖ := by
    rw [psiR, Real.norm_eq_abs]; exact Complex.abs_im_le_norm _
  have ho2 : 0 ≤ Formalism.L2.SG.WuDecay.opn g ^ 2 := sq_nonneg _
  nlinarith

theorem growth (g : Mx k r) (hg : g ∈ Nset k r) :
    1 + ‖(psiC g, psiR g)‖ ≤ ((r : ℝ) + 2) * Formalism.L2.SG.WuDecay.opn (Matrix.of g) ^ 2 := by
  show 1 + ‖(psiC g, psiR g)‖ ≤ ((r : ℝ) + 2) * Formalism.L2.SG.WuDecay.opn g ^ 2
  have h1 : 1 ≤ Formalism.L2.SG.WuDecay.opn g := one_le_opn hg
  have hB : 0 ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 := by positivity
  have hC : ‖psiC g‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 :=
    (pi_norm_le_iff_of_nonneg hB).2 fun i => psiC_le hg i
  have hR : ‖psiR g‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 :=
    (pi_norm_le_iff_of_nonneg hB).2 fun a => psiR_le g a
  have hP : ‖(psiC g, psiR g)‖ ≤ ((r : ℝ) + 1) * Formalism.L2.SG.WuDecay.opn g ^ 2 := by
    rw [Prod.norm_def]; exact max_le hC hR
  nlinarith

theorem nilpotent_chart_norm_bound (x : CI k r → ℂ) (s : Fin r → ℝ) :
    1 + ‖(x, s)‖ ≤ ((r : ℝ) + 2) * Formalism.L2.SG.WuDecay.opn (Matrix.of (phi0 x s)) ^ 2 := by
  have h := growth (phi0 x s) (test_vector_mem_schwartz_bruhat x s)
  rw [(nilpotent_chart_right_inverse x s).1, (nilpotent_chart_right_inverse x s).2] at h
  exact h

end WlocSk.NB

end
end

open MeasureTheory Formalism.QuantumDeterminants Formalism.L2.SG.SplitPrimeNormLemmas Matrix

noncomputable section

namespace WlocSk

theorem card_CI_le (k r : ℕ) : Fintype.card (NB.CI k r) ≤ r * r + r * (k + 1) + r * r := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have h : Fintype.card (NB.UP r) ≤ Fintype.card (Fin r × Fin r) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  omega

theorem dim_lt (k r : ℕ) :
    (((2 * (2 * Fintype.card (NB.CI k r) + r)) : ℕ) : ℝ) < N1H k r := by
  have hc := card_CI_le k r
  have h1 : 2 * (2 * Fintype.card (NB.CI k r) + r) < 4 * (2 * r + k + 1) ^ 2 := by
    have : 2 * (2 * Fintype.card (NB.CI k r) + r) ≤ 2 * (2 * (r * r + r * (k + 1) + r * r) + r) := by
      omega
    refine lt_of_le_of_lt this ?_
    nlinarith
  have h2 : (1 : ℝ) ≤ Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) := by
    rw [Real.one_le_sqrt]
    have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    push_cast; linarith
  unfold N1H
  have h1' : (((2 * (2 * Fintype.card (NB.CI k r) + r)) : ℕ) : ℝ) < 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast h1
  have hp : (0 : ℝ) ≤ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  nlinarith

theorem nilpotent_chart_exists : NChart := by
  intro k r
  let eC := Fintype.equivFin (NB.CI k r)
  let Φ : CSp (Fintype.card (NB.CI k r)) r → Mt k r := fun t => NB.phi0 (t.1 ∘ eC) t.2
  let ψ : Mt k r → CSp (Fintype.card (NB.CI k r)) r := fun x => (NB.psiC x ∘ eC.symm, NB.psiR x)
  have hcomp : Continuous fun t : CSp (Fintype.card (NB.CI k r)) r => (t.1 ∘ eC, t.2) :=
    (continuous_pi fun i => (continuous_apply (eC i)).comp continuous_fst).prodMk continuous_snd
  have hΦc : Continuous Φ := NB.continuous_nilpotent_chart.comp hcomp
  have hψc : Continuous ψ :=
    (continuous_pi fun j => (continuous_apply (eC.symm j)).comp NB.continuous_psiC).prodMk
      NB.continuous_psiR
  have hleft : Function.LeftInverse ψ Φ := by
    intro t
    obtain ⟨h1, h2⟩ := NB.nilpotent_chart_right_inverse (t.1 ∘ eC) t.2
    show (NB.psiC (NB.phi0 (t.1 ∘ eC) t.2) ∘ eC.symm, NB.psiR (NB.phi0 (t.1 ∘ eC) t.2)) = t
    rw [h1, h2]
    ext j <;> simp
  have hright : ∀ x : Mt k r, Matrix.of x ∈ Nset k r → Φ (ψ x) = x := by
    intro x hx
    show NB.phi0 ((NB.psiC x ∘ eC.symm) ∘ eC) (NB.psiR x) = x
    have : (NB.psiC x ∘ eC.symm) ∘ eC = NB.psiC x := by funext i; simp
    rw [this]
    exact NB.nilpotent_chart_left_inverse hx
  have hrange : Set.range Φ = {x | Matrix.of x ∈ Nset k r} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact NB.test_vector_mem_schwartz_bruhat _ _
    · intro hx
      exact ⟨ψ x, hright x hx⟩
  refine ⟨Fintype.card (NB.CI k r), r, 2, Φ, (r : ℝ) + 2, by norm_num, dim_lt k r, by positivity,
    ?_, hrange, ?_, ?_⟩
  ·
    refine MeasurableEmbedding.of_measurable_inverse hΦc.measurable ?_ hψc.measurable hleft
    have : Set.range Φ = {x | Φ (ψ x) = x} := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        show Φ (ψ (Φ t)) = Φ t
        rw [hleft t]
      · intro hx
        exact ⟨ψ x, hx⟩
    rw [this]
    exact (isClosed_eq (hΦc.comp hψc) continuous_id).measurableSet
  ·
    intro m₀ h0
    let G : (Fin (Fintype.card (NB.CI k r)) → ℂ) → Fin (Fintype.card (NB.CI k r)) → ℂ :=
      fun y j => NB.shG m₀ (y ∘ eC) (eC.symm j)
    let H : (Fin (Fintype.card (NB.CI k r)) → ℂ) → Fin r → ℝ := fun y => NB.shH m₀ (y ∘ eC)
    have hyc : Continuous fun y : Fin (Fintype.card (NB.CI k r)) → ℂ => y ∘ eC :=
      continuous_pi fun i => continuous_apply (eC i)
    refine ⟨fun t => (t.1 + G t.1, t.2 + H t.1), ?_, ?_⟩
    · refine NB.shear_mp (fun j => NB.rk (eC.symm j)) G H
        (fun j => ((NB.continuous_shG m₀ (eC.symm j)).comp hyc).measurable) ?_
        ((NB.continuous_shH m₀).comp hyc).measurable
      intro j y y' hyy
      refine NB.shG_dep m₀ (eC.symm j) (y ∘ eC) (y' ∘ eC) fun i hi => ?_
      exact hyy (eC i) (by simpa using hi)
    · intro t
      obtain ⟨h1, h2⟩ := NB.lmul_coord h0 (t.1 ∘ eC) t.2
      have hmem : m₀ * NB.phi0 (t.1 ∘ eC) t.2 ∈ Nset k r := UnitaryGroupBasics.mem_n_mul h0 (NB.test_vector_mem_schwartz_bruhat _ _)
      show m₀ * NB.phi0 (t.1 ∘ eC) t.2 = NB.phi0 ((t.1 + G t.1) ∘ eC) (t.2 + H t.1)
      have e1 : (t.1 + G t.1) ∘ eC = t.1 ∘ eC + NB.shG m₀ (t.1 ∘ eC) := by
        funext i; simp [G]
      rw [e1, ← h1]
      show _ = NB.phi0 (NB.psiC (m₀ * NB.phi0 (t.1 ∘ eC) t.2)) (t.2 + NB.shH m₀ (t.1 ∘ eC))
      rw [← h2]
      exact (NB.nilpotent_chart_left_inverse hmem).symm
  ·
    intro t
    have hg := NB.nilpotent_chart_norm_bound (t.1 ∘ eC) t.2
    have hn : ‖t‖ ≤ ‖(t.1 ∘ eC, t.2)‖ := by
      rw [Prod.norm_def, Prod.norm_def]
      refine max_le_max ?_ le_rfl
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
      have := norm_le_pi_norm (t.1 ∘ eC) (eC.symm j)
      simpa using this
    calc 1 + ‖t‖ ≤ 1 + ‖(t.1 ∘ eC, t.2)‖ := by linarith
      _ ≤ _ := hg

end WlocSk
