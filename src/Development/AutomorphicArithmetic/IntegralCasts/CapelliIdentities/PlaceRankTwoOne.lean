module

public import Mathlib

@[expose] public section

/-!
# Polynomial Haar-Volume Growth of Hilbert–Schmidt Balls in `U(p, q)`

For any sign signature `ε : Fin n → Bool`, let `UJ ε ≤ GL_n(ℂ)` be the
indefinite unitary group preserving `Jm ε = diag(±1)`, equipped with its left
Haar measure `muG ε` and squared Hilbert–Schmidt norm
`hsG g = ∑ i, ∑ j, ‖g i j‖ ^ 2`.

The main theorem `volume_growth : VolGrowth` establishes a polynomial upper
bound on the Haar measure of Hilbert–Schmidt balls: for each `n, ε`, there
exists `C : ℝ` such that for all `R ≥ 1`,
`muG ε {g : UJ ε | hsG g ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (2 * n ^ 2))`.

The proof uses a Fubini double-counting argument on the volume-preserving left
action of `UJ ε` on `ℂ^{n × n} ≅ ℝ^{2 n²}` (since `|det g| = 1` for `g ∈ UJ ε`),
bounding each fiber over `x ∈ ℂ^{n × n}` by a translate of a compact entry-bounded
ball in `UJ ε`.
-/

namespace UpperTheory.Reformulated.B.placeRankTwoOne

noncomputable def Jm {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a : Fin n => if ε a = true then 1 else -1

noncomputable def inUJ {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  g.conjTranspose * Jm ε * g = Jm ε

noncomputable def UJ {n : ℕ} (ε : Fin n → Bool) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {g | inUJ ε g.val}
  one_mem' := by simp [inUJ]
  mul_mem' {g h} hg hh := by
    have hg' : g.val.conjTranspose * Jm ε * g.val = Jm ε := hg
    have hh' : h.val.conjTranspose * Jm ε * h.val = Jm ε := hh
    change (g.val * h.val).conjTranspose * Jm ε * (g.val * h.val) = Jm ε
    calc (g.val * h.val).conjTranspose * Jm ε * (g.val * h.val)
        = h.val.conjTranspose * (g.val.conjTranspose * Jm ε * g.val) * h.val := by
            simp only [Matrix.conjTranspose_mul, mul_assoc]
      _ = Jm ε := by rw [hg', hh']
  inv_mem' {g} hg := by
    have hg' : g.val.conjTranspose * Jm ε * g.val = Jm ε := hg
    change (g⁻¹).val.conjTranspose * Jm ε * (g⁻¹).val = Jm ε
    calc (g⁻¹).val.conjTranspose * Jm ε * (g⁻¹).val
        = (g⁻¹).val.conjTranspose * (g.val.conjTranspose * Jm ε * g.val) * (g⁻¹).val := by
            rw [hg']
      _ = (g.val * (g⁻¹).val).conjTranspose * Jm ε * (g.val * (g⁻¹).val) := by
            simp only [Matrix.conjTranspose_mul, mul_assoc]
      _ = Jm ε := by rw [Units.mul_inv]; simp

@[reducible] noncomputable def instMeasurableSpaceUJ (n : ℕ) (ε : Fin n → Bool) :
    MeasurableSpace (UJ ε) :=
  borel (UJ ε)

attribute [local instance] instMeasurableSpaceUJ

section JLemmas
open Matrix

private theorem Jm_sq {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

private theorem normSq_det {n : ℕ} {ε : Fin n → Bool}
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : Complex.normSq g.det = 1 := by
  have hJ : (Jm ε).det ≠ 0 := fun h => by
    have := congrArg Matrix.det (Jm_sq ε)
    simp [h] at this
  have h := congrArg Matrix.det (show gᴴ * Jm ε * g = Jm ε from hg)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, mul_right_comm,
    mul_eq_right₀ hJ] at h
  have h2 := Complex.normSq_eq_conj_mul_self (z := g.det)
  exact_mod_cast h2.trans h

private theorem norm_inv_entry {n : ℕ} {ε : Fin n → Bool}
    {g : (Matrix (Fin n) (Fin n) ℂ)ˣ} (hg : inUJ ε g.val) (i j : Fin n) :
    ‖(g⁻¹).val i j‖ = ‖g.val j i‖ := by
  have h : (g⁻¹).val = Jm ε * g.valᴴ * Jm ε := by
    apply Units.inv_eq_of_mul_eq_one_left
    have h0 : g.valᴴ * Jm ε * g.val = Jm ε := hg
    rw [mul_assoc (Jm ε), mul_assoc (Jm ε), h0, Jm_sq]
  rw [h]
  unfold Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  split_ifs <;> simp

end JLemmas

private theorem isClosed_UJ {n : ℕ} (ε : Fin n → Bool) :
    IsClosed (UJ ε : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) :=
  isClosed_eq (f := fun g : (Matrix (Fin n) (Fin n) ℂ)ˣ => g.val.conjTranspose * Jm ε * g.val)
    ((Units.continuous_val.matrix_conjTranspose.mul continuous_const).mul Units.continuous_val)
    continuous_const

private theorem isCompact_bdd {n : ℕ} (ε : Fin n → Bool) (r : ℝ) :
    IsCompact {g : UJ ε | ∀ i j, ‖g.val.val i j‖ ≤ r} := by
  have hC := (isCompact_closedBall (0 : ℂ) r).matrix (m := Fin n) (n := Fin n)
  have he := Units.isClosedEmbedding_embedProduct.comp (isClosed_UJ ε).isClosedEmbedding_subtypeVal
  refine (he.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))).of_isClosed_subset
    ?_ fun g hg => ⟨fun i j => ?_, (g.val⁻¹).val, fun i j => ?_, rfl⟩
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le
      ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i j).norm continuous_const
  · exact mem_closedBall_zero_iff.2 (hg i j)
  · exact mem_closedBall_zero_iff.2 ((norm_inv_entry g.2 i j).trans_le (hg j i))

theorem laurent_T_neg_one_mul_T_one (n : ℕ) (ε : Fin n → Bool) :
    LocallyCompactSpace (UJ ε) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact (isClosed_UJ ε).locallyCompactSpace

attribute [local instance] laurent_T_neg_one_mul_T_one

noncomputable def muG {n : ℕ} (ε : Fin n → Bool) : MeasureTheory.Measure (UJ ε) :=
  letI : BorelSpace (UJ ε) := ⟨rfl⟩
  MeasureTheory.Measure.haar

noncomputable def hs {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ‖g i j‖ ^ 2

noncomputable def hsG {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : ℝ :=
  hs g.val.val

noncomputable def VolGrowth : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      muG ε {g : UJ ε | hsG g ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (2 * n ^ 2))

section Helpers
open MeasureTheory Matrix

private theorem fub {G E : Type*} [MeasurableSpace G] [MeasurableSpace E]
    (μ : Measure G) (ν : Measure E) [SFinite μ] [SFinite ν] {S : Set (G × E)} (hS : MeasurableSet S)
    {B : Set G} (hB : MeasurableSet B) {V : Set E} (hV : MeasurableSet V) {c k : ENNReal}
    (h1 : ∀ g ∈ B, c ≤ ν (Prod.mk g ⁻¹' S)) (h2 : ∀ x, μ ((fun g => (g, x)) ⁻¹' S) ≤ k)
    (h3 : ∀ g x, (g, x) ∈ S → x ∈ V) : c * μ B ≤ k * ν V := by
  calc c * μ B = ∫⁻ g, B.indicator (fun _ => c) g ∂μ := by
        rw [lintegral_indicator_const hB]
    _ ≤ ∫⁻ g, ν (Prod.mk g ⁻¹' S) ∂μ := by
        refine lintegral_mono fun g => ?_
        by_cases hg : g ∈ B
        · simpa [hg] using h1 g hg
        · simp [hg]
    _ = ∫⁻ x, μ ((fun g => (g, x)) ⁻¹' S) ∂ν := by
        rw [← Measure.prod_apply hS, Measure.prod_apply_symm hS]
    _ ≤ ∫⁻ x, V.indicator (fun _ => k) x ∂ν := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ V
        · simpa [hx] using h2 x
        · have : (fun g => (g, x)) ⁻¹' S = ∅ :=
            Set.eq_empty_of_forall_notMem fun g hg => hx (h3 g x hg)
          simp [this]
    _ = k * ν V := by rw [lintegral_indicator_const hV]

private def act {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → Fin n → ℂ) :
    Fin n → Fin n → ℂ := fun j => g *ᵥ x j

private theorem act_mul {n : ℕ} (g h : Matrix (Fin n) (Fin n) ℂ)
    (x : Fin n → Fin n → ℂ) : act (g * h) x = act g (act h x) := by
  funext j
  simp [act, Matrix.mulVec_mulVec]

private theorem act_one {n : ℕ} (x : Fin n → Fin n → ℂ) : act 1 x = x := by
  funext j
  simp [act]

private theorem act_sub {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ)
    (x y : Fin n → Fin n → ℂ) : act g (x - y) = act g x - act g y := by
  funext j
  simp [act, Matrix.mulVec_sub]

private theorem norm_act_le {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) {r : ℝ}
    (hr : 0 ≤ r) (hg : ∀ i j, ‖g i j‖ ≤ r) (x : Fin n → Fin n → ℂ) :
    ‖act g x‖ ≤ n * r * ‖x‖ := by
  have h0 : 0 ≤ n * r * ‖x‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun j => (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
  calc ‖act g x j i‖ = ‖∑ k, g i k * x j k‖ := rfl
    _ ≤ ∑ _k : Fin n, r * ‖x‖ := by
        refine norm_sum_le_of_le _ fun k _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hg i k) ((norm_le_pi_norm (x j) k).trans (norm_le_pi_norm x j))
          (norm_nonneg _) hr
    _ = n * r * ‖x‖ := by simp [mul_assoc]

private theorem vol_act {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : Complex.normSq g.det = 1) (ν : Measure (Fin n → Fin n → ℂ)) [ν.IsAddHaarMeasure]
    (s : Set (Fin n → Fin n → ℂ)) : ν (act g ⁻¹' s) = ν s := by
  let f : (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    LinearMap.pi fun j => ((Matrix.toLin' g).restrictScalars ℝ).comp (LinearMap.proj j)
  have hf : LinearMap.det f = 1 := by
    simp only [f]
    rw [LinearMap.det_pi]
    simp [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, hg]
  have : act g = f := rfl
  rw [this, Measure.addHaar_preimage_linearMap _ (by rw [hf]; exact one_ne_zero), hf]
  simp

private theorem entry_le {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → Fin n → ℂ)
    (hv : v ∈ Metric.ball (fun j : Fin n => (Pi.single j 1 : Fin n → ℂ)) (1 / (2 * n + 2)))
    (hw : ‖act h v‖ ≤ 2) (i j : Fin n) : ‖h i j‖ ≤ 4 := by
  set e : Fin n → Fin n → ℂ := fun j : Fin n => (Pi.single j 1 : Fin n → ℂ) with he
  have h1 : ∀ i j, ‖h i j‖ ≤ ‖act h e‖ := fun i j => by
    have : h i j = act h e j i := by simp [act, he]
    rw [this]
    exact (norm_le_pi_norm _ i).trans (norm_le_pi_norm _ j)
  have h2 := norm_act_le h (norm_nonneg _) h1 (e - v)
  rw [act_sub] at h2
  have h3 : ‖e - v‖ < 1 / (2 * n + 2) := by rwa [mem_ball_iff_norm'] at hv
  have h4 : (n : ℝ) * ‖e - v‖ ≤ 1 / 2 := by
    rw [lt_div_iff₀ (by positivity)] at h3
    nlinarith [norm_nonneg (e - v)]
  have h5 := norm_sub_norm_le (act h e) (act h v)
  have h6 := mul_le_mul_of_nonneg_left h4 (norm_nonneg (act h e))
  have := h1 i j
  nlinarith

private theorem norm_le_two {n : ℕ} (v : Fin n → Fin n → ℂ)
    (hv : v ∈ Metric.ball (fun j : Fin n => (Pi.single j 1 : Fin n → ℂ)) (1 / (2 * n + 2))) :
    ‖v‖ ≤ 2 := by
  set e : Fin n → Fin n → ℂ := fun j : Fin n => (Pi.single j 1 : Fin n → ℂ) with he
  have h1 : ‖e‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
    simp [he, Pi.norm_single]
  have h3 : ‖v - e‖ < 1 / (2 * n + 2) := by rwa [mem_ball_iff_norm] at hv
  have h4 : (1 : ℝ) / (2 * n + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  have h5 := norm_sub_norm_le v e
  linarith

end Helpers

theorem volume_growth : VolGrowth := by
  intro n ε
  have : BorelSpace (UJ ε) := ⟨rfl⟩
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have hμ : (muG ε).IsHaarMeasure := by
    unfold muG
    infer_instance
  have : SecondCountableTopology (UJ ε) := TopologicalSpace.Subtype.secondCountableTopology _
  have : SigmaCompactSpace (UJ ε) := inferInstance
  have : MeasureTheory.SigmaFinite (muG ε) := inferInstance
  let ν : MeasureTheory.Measure (Fin n → Fin n → ℂ) := MeasureTheory.Measure.addHaar
  let V : Set (Fin n → Fin n → ℂ) :=
    Metric.ball (fun j : Fin n => (Pi.single j 1 : Fin n → ℂ)) (1 / (2 * n + 2))
  let K : Set (UJ ε) := {g | ∀ i j, ‖g.val.val i j‖ ≤ 4}
  have hK : muG ε K ≠ ⊤ := (isCompact_bdd ε 4).measure_lt_top.ne
  have hV0 : ν V ≠ 0 := (Metric.measure_ball_pos ν _ (by positivity)).ne'
  have hV1 : ν V ≠ ⊤ := MeasureTheory.measure_ball_lt_top.ne
  have hB1 : ν (Metric.ball 0 1) ≠ ⊤ := MeasureTheory.measure_ball_lt_top.ne
  have hA : muG ε K * ν (Metric.ball 0 1) / ν V ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top hK hB1) hV0
  refine ⟨(muG ε K * ν (Metric.ball 0 1) / ν V).toReal * (2 * n) ^ (2 * n ^ 2), fun R hR => ?_⟩
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hval : Continuous fun g : UJ ε => g.val.val :=
    Units.continuous_val.comp continuous_subtype_val
  have hB : IsClosed {g : UJ ε | hsG g ≤ R ^ 2} :=
    isClosed_le (f := fun g : UJ ε => ∑ i, ∑ j, ‖g.val.val i j‖ ^ 2)
      (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        (hval.matrix_elem i j).norm.pow 2) continuous_const
  have hact : Continuous fun p : UJ ε × (Fin n → Fin n → ℂ) => act (p.1⁻¹).val.val p.2 :=
    continuous_pi fun j => (hval.comp continuous_fst.inv).matrix_mulVec
      ((continuous_apply j).comp continuous_snd)
  have hcancel : ∀ (g : UJ ε) x, act g.val.val (act (g⁻¹).val.val x) = x := fun g x => by
    rw [← act_mul, Subgroup.coe_inv, Units.mul_inv, act_one]
  have key := fub (muG ε) ν
    (S := {p | hsG p.1 ≤ R ^ 2 ∧ act (p.1⁻¹).val.val p.2 ∈ V})
    ((hB.preimage continuous_fst).measurableSet.inter
      (Metric.isOpen_ball.preimage hact).measurableSet)
    hB.measurableSet (V := Metric.closedBall 0 (2 * n * R)) measurableSet_closedBall
    (c := ν V) (k := muG ε K) ?_ ?_ ?_
  · have hd : Module.finrank ℝ (Fin n → Fin n → ℂ) = 2 * n ^ 2 := by
      simp [Module.finrank_pi_fintype]
      ring
    rw [MeasureTheory.Measure.addHaar_closedBall ν _ (by positivity), hd] at key
    rw [mul_assoc, ← mul_pow, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hA,
      ← ENNReal.mul_div_right_comm, ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hV1), mul_comm,
      mul_right_comm, mul_assoc]
    exact key
  · intro g hg
    rw [← vol_act (g⁻¹).val.val (normSq_det (g⁻¹).2) ν V]
    exact MeasureTheory.measure_mono fun x hx => ⟨hg, hx⟩
  · intro x
    rcases Set.eq_empty_or_nonempty ((fun g : UJ ε => (g, x)) ⁻¹'
      {p | hsG p.1 ≤ R ^ 2 ∧ act (p.1⁻¹).val.val p.2 ∈ V}) with h | ⟨g₀, hg₀⟩
    · rw [h]
      simp
    · rw [← MeasureTheory.measure_preimage_mul (muG ε) g₀⁻¹ K]
      refine MeasureTheory.measure_mono fun g hg => entry_le _ _ hg.2 ?_
      have : act (g₀⁻¹ * g).val.val (act (g⁻¹).val.val x) = act (g₀⁻¹).val.val x := by
        rw [Subgroup.coe_mul, Units.val_mul, act_mul, hcancel]
      rw [this]
      exact norm_le_two _ hg₀.2
  · intro g x hg
    have h1 : ∀ i j, ‖g.val.val i j‖ ≤ R := fun i j => by
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) hR0 two_ne_zero).1 (le_trans ?_ hg.1)
      exact (Finset.single_le_sum (f := fun j => ‖g.val.val i j‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ j)).trans (Finset.single_le_sum
          (f := fun i => ∑ j, ‖g.val.val i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i))
    have h2 := norm_act_le _ hR0 h1 (act (g⁻¹).val.val x)
    rw [hcancel] at h2
    have h3 := mul_le_mul_of_nonneg_left (norm_le_two _ hg.2) (show 0 ≤ n * R by positivity)
    rw [mem_closedBall_zero_iff]
    linarith

end UpperTheory.Reformulated.B.placeRankTwoOne
