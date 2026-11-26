module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselBigCellCoordinatesUnique
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataBothAmplitudeSides
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellChartDifferentialSkewAndFrobenius

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellChartDifferentialSurjectiveSkew
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellChartDifferentialSurjectiveSkew
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens.Onto

open Formalism.QuantumDeterminants.GBasic

lemma wC_eq (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    wC k r i j = if j = sig k r i then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  have hs := sig_val k r i
  unfold wC bigCell esI
  simp only [Fin.ext_iff, Matrix.one_apply, star_one, inv_one]
  split_ifs at * <;> first | rfl | (exfalso; omega)

lemma conj_apply (k r : ℕ) (M : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (wC k r * M * wC k r) i j = M (sig k r i) (sig k r j) := by
  simp only [Matrix.mul_apply, wC_eq k r i, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [wC_eq, eq_sig_iff k r j, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

lemma skew_apply (k r : ℕ) (M : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (Mᴴ * Hpk k r + Hpk k r * M) i j =
      star (M (sig k r j) i) * sgn k r j + sgn k r i * M (sig k r i) j := by
  simp only [Matrix.add_apply, Matrix.mul_apply, conjTranspose_apply, Hpk_eq k r i, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Hpk_eq, eq_sig_iff k r j, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sgn_sig]

lemma skew_iff (k r : ℕ) (M : Mat k r) :
    Mᴴ * Hpk k r + Hpk k r * M = 0 ↔
      ∀ i j, star (M (sig k r j) i) * sgn k r j + sgn k r i * M (sig k r i) j = 0 := by
  rw [← Matrix.ext_iff]
  simp only [skew_apply, Matrix.zero_apply]

lemma lev_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : lev k r (sig k r i) + lev k r i = 2 * r := by
  have hi := i.isLt
  have hs := sig_val k r i
  unfold lev
  split_ifs at * <;> omega

lemma unre {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, realifyFun]

lemma exists_N (k r : ℕ) (M : Mat k r) (h : Mᴴ * Hpk k r + Hpk k r * M = 0) :
    ∃ X : lieE (Nset k r), um X = Matrix.of fun i j => if lev k r i < lev k r j then M i j else 0 := by
  refine ⟨⟨(WithLp.equiv 2 _).symm (realifyFun
    (Matrix.of fun i j => if lev k r i < lev k r j then M i j else 0)), ?_⟩, unre _⟩
  rw [(GlobalTheory.T.lieEntries_unipotentBesselN_characterization k r _).1, unre]
  refine ⟨?_, fun i j hij => by simp [not_lt.2 hij]⟩
  rw [skew_iff] at h ⊢
  intro i j
  have h1 := lev_sig k r i
  have h2 := lev_sig k r j
  simp only [Matrix.of_apply]
  by_cases c : lev k r (sig k r j) < lev k r i
  · rw [if_pos c, if_pos (by omega)]; exact h i j
  · rw [if_neg c, if_neg (by omega)]; simp

lemma exists_lieElement_middleBlockPart (k r : ℕ) (M : Mat k r) (h : Mᴴ * Hpk k r + Hpk k r * M = 0) :
    ∃ Y : lieE (Formalism.FourierDecayAlt.B2.UWb k r), um Y = Matrix.of fun i j =>
      if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then M i j else 0 := by
  refine ⟨⟨(WithLp.equiv 2 _).symm (realifyFun (Matrix.of fun i j =>
      if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then M i j else 0)), ?_⟩, unre _⟩
  rw [(GlobalTheory.T.lieAlgebra_besselModel_middleUnitary_entries k r _).2.1, unre]
  refine ⟨?_, fun i j hij => by simp only [Matrix.of_apply, if_neg hij]⟩
  rw [skew_iff] at h ⊢
  intro i j
  have h1 := sig_val k r i
  have h2 := sig_val k r j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Matrix.of_apply]
  by_cases c : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
  · rw [if_pos (by split_ifs at h1 h2 <;> omega), if_pos (by split_ifs at h1 h2 <;> omega)]
    exact h i j
  · rw [if_neg (by split_ifs at h1 h2 <;> omega), if_neg (by split_ifs at h1 h2 <;> omega)]
    simp

theorem dchart_onto : ∀ (k r : ℕ) (Z : Mat k r), Zᴴ * Hpk k r + Hpk k r * Z = 0 →
    ∃ v : EE k r, dchart k r v = Z := by
  intro k r Z hZ
  have hZ' := (skew_iff k r Z).1 hZ
  obtain ⟨X', hX'⟩ := exists_N k r Z hZ
  obtain ⟨Y, hY⟩ := exists_lieElement_middleBlockPart k r Z hZ
  obtain ⟨X, hX⟩ := exists_N k r (Matrix.of fun i j => -Z (sig k r i) (sig k r j)) (by
    rw [skew_iff]
    intro i j
    have := hZ' (sig k r i) (sig k r j)
    simp only [sig_sig, sgn_sig] at this
    simp only [Matrix.of_apply, sig_sig, star_neg]
    linear_combination -this)
  refine ⟨((X, X'), (fun a => Z (eI k r a) (eI k r a), Y)), ?_⟩
  ext i j
  have h1 := lev_sig k r i
  have h2 := lev_sig k r j
  have hi := i.isLt
  have hj := j.isLt
  simp only [dchart, Matrix.add_apply, Matrix.neg_apply, conj_apply, hX, hX', hY, Matrix.of_apply,
    sig_sig, torD, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp only [lt_irrefl, if_false, if_true, neg_zero, zero_add, add_zero, and_self]
    by_cases c : i.val < r
    · rw [dite_eq_left c, if_neg (by omega), add_zero]; rfl
    · rw [dite_eq_right c]
      by_cases c' : r + k < i.val
      · rw [dite_eq_left c', if_neg (by omega), add_zero]
        have e : eI k r ⟨2 * r + k - i.val, by omega⟩ = sig k r i :=
          Fin.ext (by rw [sig_hi k r i c']; rfl)
        rw [e]
        have := hZ' (sig k r i) i
        rw [sgn_sig, sig_sig] at this
        have hs : sgn k r i = 1 := by unfold sgn; rw [if_neg (by omega)]
        rw [hs] at this
        linear_combination -this
      · rw [dite_eq_right c', if_pos (by omega), zero_add]
  · rw [if_neg hij, add_zero]
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have l1 : lev k r i = if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k := rfl
    have l2 : lev k r j = if j.val < r then j.val else if j.val ≤ r + k then r else j.val - k := rfl
    rcases lt_trichotomy (lev k r i) (lev k r j) with c | c | c
    · rw [if_neg (by omega), if_neg (by split_ifs at l1 l2 <;> omega), if_pos c]; simp
    · rw [if_neg (by omega), if_pos (by split_ifs at l1 l2 <;> omega), if_neg (by omega)]; simp
    · rw [if_pos (by omega), if_neg (by split_ifs at l1 l2 <;> omega), if_neg (by omega)]; simp

end GlobalTheory.CellDens.Onto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellChartDifferentialSurjectiveSkewStatement
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigCellChartDifferential_surjective_skew : ∀ (k r : ℕ) (Z : Mat k r), Zᴴ * Hpk k r + Hpk k r * Z = 0 → ∃ v : EE k r, dchart k r v = Z := by
  first | exact @GlobalTheory.CellDens.Onto.dchart_onto | exact GlobalTheory.CellDens.Onto.dchart_onto | (intros; apply GlobalTheory.CellDens.Onto.dchart_onto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeImageOfSqrtTwoIsometricLinearEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeImageOfSqrtTwoIsometricLinearEquiv
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellDens.ScaledVol

theorem measurePreserving_inv_sqrt_two_smul (r : ℕ) :
    MeasurePreserving (fun y : Fin r → ℂ => (√2 : ℝ)⁻¹ • y) volume
      (((2 : ℝ≥0∞) ^ r) • volume) := by
  have hs : (√2 : ℝ)⁻¹ ≠ 0 := by positivity
  have hfin : Module.finrank ℝ (Fin r → ℂ) = 2 * r := by
    rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex]; ring
  refine ⟨by fun_prop, ?_⟩
  rw [Measure.map_addHaar_smul _ hs, hfin, inv_pow, inv_inv, pow_mul, Real.sq_sqrt (by norm_num),
    abs_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp

theorem volume_image_eq (A B F : Type) [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] [MeasurableSpace B] [BorelSpace B]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] (r : ℕ) (L : ((A × A) × ((Fin r → ℂ) × B)) ≃L[ℝ] F)
    (hL : ∀ v, ‖L v‖ ^ 2 =
      ‖v.1.1‖ ^ 2 + ‖v.1.2‖ ^ 2 + 2 * (∑ a, ‖v.2.1 a‖ ^ 2) + ‖v.2.2‖ ^ 2)
    (s : Set ((A × A) × ((Fin r → ℂ) × B))) (hs : MeasurableSet s) :
    volume (L '' s) = 2 ^ r * volume s := by
  have hc : (√2 : ℝ)⁻¹ ≠ 0 := by positivity
  let Ψ : WithLp 2 (WithLp 2 (A × A) × WithLp 2 (EuclideanSpace ℂ (Fin r) × B)) ≃ₗ[ℝ]
      ((A × A) × ((Fin r → ℂ) × B)) :=
    (WithLp.linearEquiv 2 ℝ _).trans
      (LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ (A × A))
        ((WithLp.linearEquiv 2 ℝ _).trans
          (LinearEquiv.prodCongr
            ((WithLp.linearEquiv 2 ℝ (Fin r → ℂ)).trans
              (LinearEquiv.smulOfNeZero ℝ (Fin r → ℂ) (√2 : ℝ)⁻¹ hc))
            (LinearEquiv.refl ℝ B))))
  have hΨ : ∀ x, Ψ x = (x.ofLp.1.ofLp, ((√2 : ℝ)⁻¹ • x.ofLp.2.ofLp.1.ofLp, x.ofLp.2.ofLp.2)) :=
    fun _ => rfl
  let G : WithLp 2 (WithLp 2 (A × A) × WithLp 2 (EuclideanSpace ℂ (Fin r) × B)) ≃ₗᵢ[ℝ] F :=
    { Ψ.trans L.toLinearEquiv with
      norm_map' := fun x => by
        change ‖L (Ψ x)‖ = ‖x‖
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hL, hΨ, WithLp.prod_norm_sq_eq_of_L2,
          WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
        simp [norm_smul, mul_pow, Finset.mul_sum, ← mul_assoc, add_assoc] }
  have h0 := (measurePreserving_inv_sqrt_two_smul r).comp
    (GlobalTheory.volume_preserving_ofLp_complex (Fin r))
  haveI : SFinite (((2 : ℝ≥0∞) ^ r) • (volume : Measure (Fin r → ℂ))) := inferInstance
  have h1 := (h0.prod (MeasurePreserving.id (volume : Measure B))).comp
    (WithLp.volume_preserving_ofLp (EuclideanSpace ℂ (Fin r)) B)
  have h2 := ((WithLp.volume_preserving_ofLp A A).prod h1).comp
    (WithLp.volume_preserving_ofLp (WithLp 2 (A × A)) (WithLp 2 (EuclideanSpace ℂ (Fin r) × B)))
  have h3 := h2.measure_preimage hs.nullMeasurableSet
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.smul_apply, smul_eq_mul,
    ← Measure.volume_eq_prod, ← Measure.volume_eq_prod] at h3
  have hm : MeasurableSet (L '' s) :=
    L.toHomeomorph.toMeasurableEquiv.measurableEmbedding.measurableSet_image.2 hs
  rw [← h3, ← G.measurePreserving.measure_preimage hm.nullMeasurableSet]
  congr 1
  ext x
  change L (Ψ x) ∈ L '' s ↔ Ψ x ∈ s
  exact L.injective.mem_set_image

end GlobalTheory.CellDens.ScaledVol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeImageOfSqrtTwoIsometricLinearEquivStatement
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_image_of_sqrt_two_isometric_linearEquiv : ∀ (A B F : Type) [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A] [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] [MeasurableSpace B] [BorelSpace B] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (r : ℕ) (L : ((A × A) × ((Fin r → ℂ) × B)) ≃L[ℝ] F), (∀ v, ‖L v‖ ^ 2 = ‖v.1.1‖ ^ 2 + ‖v.1.2‖ ^ 2 + 2 * (∑ a, ‖v.2.1 a‖ ^ 2) + ‖v.2.2‖ ^ 2) → ∀ s : Set ((A × A) × ((Fin r → ℂ) × B)), MeasurableSet s → volume (L '' s) = 2 ^ r * volume s := by
  first | exact @GlobalTheory.CellDens.ScaledVol.volume_image_eq | exact GlobalTheory.CellDens.ScaledVol.volume_image_eq | (intros; apply GlobalTheory.CellDens.ScaledVol.volume_image_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellExponentialChartStrictDifferentiableSumma
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellExponentialChartStrictDifferentiableSumma
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens.Deriv

def dg (k r : ℕ) (c : Fin r → ℂ) (j : Fin (2 * r + k + 1)) : ℂ :=
  if hj : j.val < r then c ⟨j.val, hj⟩
  else if hj2 : j.val ≤ r + k then 1
  else (star (c ⟨2 * r + k - j.val, by omega⟩))⁻¹

theorem bigCell_eq (k r : ℕ) (c : Fin r → ℂ) :
    bigCell k r c 1 = wC k r * Matrix.diagonal (dg k r c) := by
  ext i j
  rw [Matrix.mul_diagonal]
  simp only [wC, bigCell, dg]
  split_ifs <;> simp

def sg (k r : ℕ) (j : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if j.val < r ∨ r + k < j.val then ⟨2 * r + k - j.val, by omega⟩ else j

theorem sg_sg (k r : ℕ) (j : Fin (2 * r + k + 1)) : sg k r (sg k r j) = j := by
  have := j.isLt
  have hv : ∀ i : Fin (2 * r + k + 1), (sg k r i).val =
      if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := by
    intro i; simp only [sg]; split_ifs <;> rfl
  apply Fin.ext
  rw [hv, hv]
  split_ifs <;> omega

theorem wC_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    wC k r i j = if i = sg k r j then 1 else 0 := by
  have := j.isLt
  have := i.isLt
  have hv : (sg k r j).val =
      if j.val < r ∨ r + k < j.val then 2 * r + k - j.val else j.val := by
    simp only [sg]; split_ifs <;> rfl
  simp only [wC, bigCell, esI, Matrix.one_apply, Fin.ext_iff, hv, star_one, inv_one]
  split_ifs <;> first | rfl | omega

theorem wC_mul_wC (k r : ℕ) : wC k r * wC k r = 1 := by
  ext i j
  simp only [Matrix.mul_apply, wC_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (sg k r j)]
  · simp [sg_sg]
  · intro b _ hb; simp [hb]
  · simp

def umL {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : lieE S →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun := um
  map_add' X Y := by ext i j; apply Complex.ext <;> simp [um, unrealify]
  map_smul' a X := by ext i j; apply Complex.ext <;> simp [um, unrealify]

theorem dg_one (k r : ℕ) : dg k r (fun a => 1 + (0 : Fin r → ℂ) a) = fun _ => 1 := by
  funext j; simp only [dg]; split_ifs <;> simp

theorem dg_contOn (k r : ℕ) (j : Fin (2 * r + k + 1)) :
    ContinuousOn (fun x : Fin r → ℂ => dg k r (fun a => 1 + x a) j) (Metric.ball 0 1) := by
  simp only [dg]
  split_ifs with h1 h2
  · fun_prop
  · fun_prop
  · apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    rw [mem_ball_zero_iff] at hx
    have h3 := (norm_le_pi_norm x ⟨2 * r + k - j.val, by omega⟩).trans_lt hx
    rw [star_ne_zero]
    intro h
    have : x ⟨2 * r + k - j.val, by omega⟩ = -1 := by linear_combination h
    rw [this] at h3
    simp at h3

theorem dg_deriv (k r : ℕ) (j : Fin (2 * r + k + 1)) :
    ∃ D : (Fin r → ℂ) →L[ℝ] ℂ,
      HasStrictFDerivAt (fun x : Fin r → ℂ => dg k r (fun a => 1 + x a) j) D 0 ∧
      ∀ x, D x = torD k r x j j := by
  simp only [dg, torD, Matrix.diagonal_apply_eq]
  by_cases h1 : j.val < r
  · simp only [dif_pos h1]
    exact ⟨_, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ)
      ⟨j.val, h1⟩).hasStrictFDerivAt.const_add 1, fun x => rfl⟩
  · by_cases h2 : j.val ≤ r + k
    · simp only [dif_neg h1, dif_pos h2, dif_neg (not_lt.2 h2)]
      exact ⟨0, hasStrictFDerivAt_const _ _, fun x => rfl⟩
    · simp only [dif_neg h1, dif_neg h2, dif_pos (not_le.1 h2)]
      set a : Fin r := ⟨2 * r + k - j.val, by omega⟩
      let L : (Fin r → ℂ) →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) a)
      have hL : HasStrictFDerivAt (fun x : Fin r → ℂ => 1 + L x) L 0 := L.hasStrictFDerivAt.const_add 1
      have hi : HasStrictDerivAt (fun z : ℂ => z⁻¹) (-((1 + L 0) ^ 2)⁻¹) (1 + L 0) :=
        hasStrictDerivAt_inv (by simp)
      have := (hi.hasStrictFDerivAt.restrictScalars ℝ).comp (0 : Fin r → ℂ) hL
      refine ⟨_, this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_), fun x => ?_⟩
      · simp [L]
      · simp [L]

theorem torD_eq (k r : ℕ) (x : Fin r → ℂ) : torD k r x = Matrix.diagonal fun j => torD k r x j j := by
  simp only [torD, Matrix.diagonal_apply_eq]

theorem um_zero {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : um (0 : lieE S) = 0 := (umL S).map_zero

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_um_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ}
    (L : E →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) :
    HasStrictFDerivAt (fun v => NormedSpace.exp (L v)) (LinearMap.toContinuousLinearMap L) 0 := by
  have h1 : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin m) (Fin m) ℂ → _)
      (1 : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ)
      (LinearMap.toContinuousLinearMap L 0) := by
    rw [map_zero]; exact hasStrictFDerivAt_exp_zero
  exact h1.comp 0 (LinearMap.toContinuousLinearMap L).hasStrictFDerivAt

theorem exp_um_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ}
    (L : E →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) :
    Continuous (fun v => NormedSpace.exp (L v)) :=
  NormedSpace.exp_continuous.comp (LinearMap.toContinuousLinearMap L).continuous

theorem diag_deriv (k r : ℕ) :
    ∃ D : (Fin r → ℂ) →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      HasStrictFDerivAt (fun x : Fin r → ℂ => Matrix.diagonal (dg k r (fun a => 1 + x a))) D 0 ∧
      ∀ x, D x = torD k r x := by
  choose D hD hD' using dg_deriv k r
  have h1 : HasStrictFDerivAt (fun x : Fin r → ℂ => dg k r (fun a => 1 + x a))
      (ContinuousLinearMap.pi D) 0 := hasStrictFDerivAt_pi.2 hD
  let L : (Fin (2 * r + k + 1) → ℂ) →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.diagonalLinearMap (Fin (2 * r + k + 1)) ℝ ℂ)
  refine ⟨_, L.hasStrictFDerivAt.comp 0 h1, fun x => ?_⟩
  rw [torD_eq]
  change Matrix.diagonal (fun j => D j x) = _
  simp only [hD']

theorem chart_deriv_mat (k r : ℕ) :
    ∃ D : EE k r →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      HasStrictFDerivAt (chart k r) D 0 ∧ ∀ v, D v = dchart k r v := by
  obtain ⟨D, hD, hD'⟩ := diag_deriv k r
  let P : EE k r →L[ℝ] (Fin r → ℂ) := (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
  have h2 : HasStrictFDerivAt (fun v : EE k r => Matrix.diagonal (dg k r (fun a => 1 + v.2.1 a)))
      (D.comp P) 0 :=
    HasStrictFDerivAt.comp (0 : EE k r) (f := P) (by rw [map_zero]; exact hD) P.hasStrictFDerivAt
  have h1 := exp_um_deriv (E := EE k r)
    (-((umL (Nset k r)).comp ((LinearMap.fst ℝ _ _).comp (LinearMap.fst ℝ _ _))))
  have h3 := exp_um_deriv (E := EE k r)
    ((umL (Formalism.FourierDecayAlt.B2.UWb k r)).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _)))
  have h4 := exp_um_deriv (E := EE k r)
    ((umL (Nset k r)).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.fst ℝ _ _)))
  have h := (((h1.mul' (h2.const_mul (wC k r))).mul' h3).mul' h4).const_mul (wC k r)
  refine ⟨_, h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_), fun v => ?_⟩
  · simp only [chart, bigCell_eq]
    rfl
  · have e : dg k r (fun _ => 1) = fun _ => 1 := by simpa using dg_one k r
    simp [e, P, dchart, umL, um_zero]
    change wC k r * (wC k r * um v.1.2) + (wC k r * (wC k r * um v.2.2) +
      (wC k r * (wC k r * D v.2.1) + wC k r * (-um v.1.1 * wC k r))) = _
    simp only [hD', ← mul_assoc, wC_mul_wC, one_mul, mul_neg, neg_mul]
    abel

theorem chart_deriv (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ∃ D : EE k r →L[ℝ] ℂ, HasStrictFDerivAt (fun v => chart k r v i j) D 0 ∧
      ∀ v, D v = dchart k r v i j := by
  obtain ⟨D, hD, hD'⟩ := chart_deriv_mat k r
  let L : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  refine ⟨_, L.hasStrictFDerivAt.comp 0 hD, fun v => ?_⟩
  change D v i j = _
  rw [hD']

theorem chart_contOn (k r : ℕ) : ContinuousOn (chart k r) (Metric.ball 0 1) := by
  have h1 := exp_um_cont (E := EE k r)
    (-((umL (Nset k r)).comp ((LinearMap.fst ℝ _ _).comp (LinearMap.fst ℝ _ _))))
  have h3 := exp_um_cont (E := EE k r)
    ((umL (Formalism.FourierDecayAlt.B2.UWb k r)).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _)))
  have h4 := exp_um_cont (E := EE k r)
    ((umL (Nset k r)).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.fst ℝ _ _)))
  have h5 : ContinuousOn (fun x : Fin r → ℂ => dg k r (fun a => 1 + x a)) (Metric.ball 0 1) :=
    continuousOn_pi.2 (dg_contOn k r)
  have h6 : ContinuousOn (fun v : EE k r => dg k r (fun a => 1 + v.2.1 a)) (Metric.ball 0 1) := by
    refine h5.comp (f := fun v : EE k r => v.2.1) (by fun_prop) fun v hv => ?_
    rw [mem_ball_zero_iff] at hv ⊢
    exact ((norm_fst_le v.2).trans (norm_snd_le v)).trans_lt hv
  have h2 : ContinuousOn (fun v : EE k r => Matrix.diagonal (dg k r (fun a => 1 + v.2.1 a)))
      (Metric.ball 0 1) :=
    (Continuous.matrix_diagonal continuous_id).comp_continuousOn h6
  have h := (continuousOn_const (c := wC k r)).mul
    (((h1.continuousOn.mul ((continuousOn_const (c := wC k r)).mul h2)).mul h3.continuousOn).mul
      h4.continuousOn)
  refine h.congr fun v _ => ?_
  simp only [chart, bigCell_eq]
  rfl

end

theorem chart_zero (k r : ℕ) : chart k r 0 = 1 := by
  have e : dg k r (fun _ => 1) = fun _ => 1 := by simpa using dg_one k r
  simp [chart, bigCell_eq, um_zero, e, wC_mul_wC]

theorem chart_strict : ∀ (k r : ℕ), chart k r 0 = 1 ∧ ContinuousOn (chart k r) (Metric.ball 0 1) ∧
    ∀ i j, ∃ D : EE k r →L[ℝ] ℂ, HasStrictFDerivAt (fun v => chart k r v i j) D 0 ∧
      ∀ v, D v = dchart k r v i j :=
  fun k r => ⟨chart_zero k r, chart_contOn k r, chart_deriv k r⟩

end GlobalTheory.CellDens.Deriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellExponentialChartStrictDifferentiableSummaStatement
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigCellExponentialChart_strictDifferentiable_summary : ∀ (k r : ℕ), chart k r 0 = 1 ∧ ContinuousOn (chart k r) (Metric.ball 0 1) ∧ ∀ i j, ∃ D : EE k r →L[ℝ] ℂ, HasStrictFDerivAt (fun v => chart k r v i j) D 0 ∧ ∀ v, D v = dchart k r v i j := by
  first | exact @GlobalTheory.CellDens.Deriv.chart_strict | exact GlobalTheory.CellDens.Deriv.chart_strict | (intros; apply GlobalTheory.CellDens.Deriv.chart_strict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoBallMeanBigCellWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoBallMeanBigCellWeight
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens

theorem tendsto_mean_ball_of_continuousAt {r : ℕ} (c : Fin r → ℂ) (f : (Fin r → ℂ) → ℝ≥0∞)
    (hf : ContinuousAt f c) (h1 : f c = 1) :
    Tendsto (fun ρ : ℝ => (∫⁻ x in Metric.ball c ρ, f x) / volume (Metric.ball (0 : Fin r → ℂ) ρ))
      (𝓝[>] 0) (𝓝 1) := by
  rw [ENNReal.tendsto_nhds ENNReal.one_ne_top]
  intro ε hε
  have hfc : Tendsto f (𝓝 c) (𝓝 1) := by rw [← h1]; exact hf
  have hev := (ENNReal.tendsto_nhds ENNReal.one_ne_top).1 hfc ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
  have hV : volume (Metric.ball c ρ) = volume (Metric.ball (0 : Fin r → ℂ) ρ) :=
    Measure.addHaar_ball_center volume c ρ
  have hpos : volume (Metric.ball c ρ) ≠ 0 := (Metric.measure_ball_pos volume c hρ.1).ne'
  have hfin : volume (Metric.ball c ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hsub : ∀ x ∈ Metric.ball c ρ, f x ∈ Set.Icc (1 - ε) (1 + ε) := fun x hx =>
    hball x (Metric.ball_subset_ball hρ.2.le hx)
  have hlo : (1 - ε) * volume (Metric.ball c ρ) ≤ ∫⁻ x in Metric.ball c ρ, f x := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hsub x hx).1
  have hhi : ∫⁻ x in Metric.ball c ρ, f x ≤ (1 + ε) * volume (Metric.ball c ρ) := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hsub x hx).2
  rw [← hV]
  constructor
  · calc 1 - ε = (1 - ε) * volume (Metric.ball c ρ) / volume (Metric.ball c ρ) :=
          (ENNReal.mul_div_cancel_right hpos hfin).symm
      _ ≤ _ := ENNReal.div_le_div_right hlo _
  · calc _ ≤ (1 + ε) * volume (Metric.ball c ρ) / volume (Metric.ball c ρ) :=
          ENNReal.div_le_div_right hhi _
      _ = 1 + ε := ENNReal.mul_div_cancel_right hpos hfin

theorem tendsto_mean_cWeight : ∀ (k r : ℕ), Tendsto (fun ρ : ℝ => (∫⁻ x in Metric.ball (fun _ => 1 : Fin r → ℂ) ρ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x)) / volume (Metric.ball (0 : Fin r → ℂ) ρ)) (𝓝[>] 0) (𝓝 1) := by
  intro k r
  apply tendsto_mean_ball_of_continuousAt
  · refine (ENNReal.continuous_ofReal.comp ?_).continuousAt
    unfold Formalism.FourierDecayAlt.B2.cWeight
    fun_prop
  · unfold Formalism.FourierDecayAlt.B2.cWeight
    simp

end GlobalTheory.CellDens
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoBallMeanBigCellWeightStatement
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_ball_mean_bigCellWeight : ∀ (k r : ℕ), Tendsto (fun ρ : ℝ => (∫⁻ x in Metric.ball (fun _ => 1 : Fin r → ℂ) ρ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x)) / volume (Metric.ball (0 : Fin r → ℂ) ρ)) (𝓝[>] 0) (𝓝 1) := by
  first | exact @GlobalTheory.CellDens.tendsto_mean_cWeight | exact GlobalTheory.CellDens.tendsto_mean_cWeight | (intros; apply GlobalTheory.CellDens.tendsto_mean_cWeight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBigCellHaarDensityConstant
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens

variable {k r : ℕ}

theorem matGroup_of {U : Set (Mat k r)} (h : Formalism.FourierDecayAlt.B2.IsClosedSubgroup U) : PI.IsMatGroup U :=
  ⟨h.closed, h.one_mem, h.mul_mem, fun a ha => ⟨h.inv_mem a ha, Matrix.mul_nonsing_inv _ (h.unit a ha)⟩⟩

def umL (m : ℕ) : EuclideanSpace ℝ (Fin m × Fin m × Bool) ≃ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun := unrealify
  invFun X := WithLp.toLp 2 (realifyFun X)
  map_add' x y := by ext i j; apply Complex.ext <;> simp [unrealify]
  map_smul' c x := by ext i j; apply Complex.ext <;> simp [unrealify]
  left_inv x := by
    ext ⟨i, j, b⟩
    cases b <;> simp [unrealify, realifyFun]
  right_inv X := by ext i j; apply Complex.ext <;> simp [unrealify, realifyFun]

theorem norm_sq_um {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    ‖x‖ ^ 2 = ∑ i, ∑ j, ‖unrealify x i j‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp only [unrealify]; ring

theorem torD_add (x y : Fin r → ℂ) : torD k r (x + y) = torD k r x + torD k r y := by
  unfold torD
  rw [Matrix.diagonal_add]
  congr 1; funext i
  split_ifs <;> simp [add_comm]

theorem torD_smul (c : ℝ) (x : Fin r → ℂ) : torD k r (c • x) = c • torD k r x := by
  unfold torD
  rw [← Matrix.diagonal_smul]
  congr 1; funext i
  simp only [Pi.smul_apply]
  split_ifs <;> simp

theorem um_add {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (X Y : lieE S) : um (X + Y) = um X + um Y :=
  (umL m).map_add _ _

theorem um_smul {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (c : ℝ) (X : lieE S) : um (c • X) = c • um X :=
  (umL m).map_smul _ _

def dL (k r : ℕ) : EE k r →ₗ[ℝ] lieE (GG k r) where
  toFun v := ⟨(umL _).symm (dchart k r v), (GlobalTheory.T.lieAlgebra_besselModel_middleUnitary_entries k r _).1.2 (by
    have : unrealify ((umL _).symm (dchart k r v)) = dchart k r v := (umL _).apply_symm_apply _
    rw [this]; exact (GlobalTheory.T.bigCellChartDifferential_skew_and_frobenius k r v).1)⟩
  map_add' v v' := by
    apply Subtype.ext
    show (umL _).symm _ = (umL _).symm _ + (umL _).symm _
    rw [← map_add (f := _)]; congr 1
    simp only [dchart, Prod.fst_add, Prod.snd_add, um_add, torD_add, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c v := by
    apply Subtype.ext
    show (umL _).symm _ = c • (umL _).symm _
    rw [← map_smul]; congr 1
    simp only [dchart, Prod.smul_fst, Prod.smul_snd, um_smul, torD_smul, Matrix.mul_smul, Matrix.smul_mul,
      smul_add, smul_neg]

theorem um_dL (v : EE k r) : um (dL k r v) = dchart k r v := (umL _).apply_symm_apply _

theorem norm_dL (v : EE k r) :
    ‖dL k r v‖ ^ 2 = ‖v.1.1‖ ^ 2 + ‖v.1.2‖ ^ 2 + 2 * (∑ a, ‖v.2.1 a‖ ^ 2) + ‖v.2.2‖ ^ 2 := by
  rw [← (GlobalTheory.T.bigCellChartDifferential_skew_and_frobenius k r v).2, ← um_dL]
  exact norm_sq_um _

theorem dL_bij : Function.Bijective (dL k r) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    have h := norm_dL v
    rw [hv, norm_zero] at h
    have h0 : 0 ≤ ∑ a, ‖v.2.1 a‖ ^ 2 := by positivity
    have h1 := sq_nonneg ‖v.1.1‖
    have h2 := sq_nonneg ‖v.1.2‖
    have h3 := sq_nonneg ‖v.2.2‖
    have e1 : v.1.1 = 0 := by rw [← norm_eq_zero, ← sq_eq_zero_iff]; nlinarith
    have e2 : v.1.2 = 0 := by rw [← norm_eq_zero, ← sq_eq_zero_iff]; nlinarith
    have e3 : v.2.2 = 0 := by rw [← norm_eq_zero, ← sq_eq_zero_iff]; nlinarith
    have e4 : ∑ a, ‖v.2.1 a‖ ^ 2 = 0 := by nlinarith
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at e4
    have e5 : v.2.1 = 0 := funext fun a => by simpa using e4 a (Finset.mem_univ _)
    exact Prod.ext (Prod.ext e1 e2) (Prod.ext e5 e3)
  · intro Z
    obtain ⟨v, hv⟩ := GlobalTheory.T.bigCellChartDifferential_surjective_skew k r (um Z) ((GlobalTheory.T.lieAlgebra_besselModel_middleUnitary_entries k r _).1.1 Z.2)
    refine ⟨v, Subtype.ext ((umL _).injective ?_)⟩
    exact (um_dL v).trans hv

def dE (k r : ℕ) : EE k r ≃L[ℝ] lieE (GG k r) := (LinearEquiv.ofBijective (dL k r) dL_bij).toContinuousLinearEquiv

theorem meas_img {E F : Type} [MetricSpace E] [ProperSpace E] [TopologicalSpace F] [T2Space F] [MeasurableSpace F]
    [OpensMeasurableSpace F] {f : E → F} {x : E} {ρ : ℝ} (hf : ContinuousOn f (Metric.ball x ρ)) :
    MeasurableSet (f '' Metric.ball x ρ) := by
  have h : IsSigmaCompact (Metric.ball x ρ) := by
    have := (Metric.isOpen_ball (x := x) (ε := ρ)).locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance
  obtain ⟨K, hK, hU⟩ := h.image_of_continuousOn hf
  rw [← hU]
  exact MeasurableSet.iUnion fun n => (hK n).isClosed.measurableSet

theorem continuous_expE {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) :
    Continuous fun X : lieE S => NormedSpace.exp (um X) := by
  have h1 : Continuous fun X : lieE S => um X :=
    (umL m).toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val
  have h2 : Continuous (NormedSpace.exp : Matrix (Fin m) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ) := by
    let : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
    let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
    have : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℂ _
    exact @NormedSpace.exp_continuous (Matrix (Fin m) (Fin m) ℂ) _ _ this
  exact h2.comp h1

theorem meas_expSet {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) (ρ : ℝ) :
    MeasurableSet (expSet S (Metric.ball 0 ρ)) :=
  meas_img (F := Fin m → Fin m → ℂ) (continuous_expE S).continuousOn

theorem lev_mono {i j : Fin (2 * r + k + 1)} (h : j ≤ i) : lev k r j ≤ lev k r i := by
  have : j.val ≤ i.val := h
  unfold lev; split_ifs <;> omega

theorem haarLie_expSet (ρ : ℝ) :
    haarLie (Nset k r) 1 (expSet (Nset k r) (Metric.ball 0 ρ)) = volume (Metric.ball (0 : lieE (Nset k r)) ρ) := by
  unfold haarLie
  rw [one_smul]
  refine (Measure.map_apply (Continuous.measurable (γ := Mt k r) (continuous_expE (Nset k r)))
    (meas_expSet _ ρ)).trans ?_
  congr 1
  refine Set.preimage_image_eq _ fun X Y h => Subtype.ext ((umL _).injective ?_)
  exact GlobalTheory.T.exp_injective_strictUpperTriangular _ _ _ (fun i j h => ((GlobalTheory.T.lieEntries_unipotentBesselN_characterization k r _).1.1 X.2).2 i j (lev_mono h))
    (fun i j h => ((GlobalTheory.T.lieEntries_unipotentBesselN_characterization k r _).1.1 Y.2).2 i j (lev_mono h)) h

theorem exp_N (X : lieE (Nset k r)) : NormedSpace.exp (um X) ∈ Nset k r := (GlobalTheory.T.lieEntries_unipotentBesselN_characterization k r _).2 X.2

theorem exp_lieElementFrobeniusMatrix_mem_besselUWb (X : lieE (Formalism.FourierDecayAlt.B2.UWb k r)) : NormedSpace.exp (um X) ∈ Formalism.FourierDecayAlt.B2.UWb k r :=
  (GlobalTheory.T.lieAlgebra_besselModel_middleUnitary_entries k r _).2.2 X.2

theorem bc_mem {x : Fin r → ℂ} (hx : ∀ a, x a ≠ 0) : bigCell k r x 1 ∈ GG k r :=
  Formalism.QuantumDeterminants.bigCellMem k r x 1 hx (by simp)

theorem wC_mem : wC k r ∈ GG k r := bc_mem fun _ => one_ne_zero

theorem one_add_ne {x : Fin r → ℂ} (hx : ‖x‖ < 1) (a : Fin r) : 1 + x a ≠ 0 := by
  intro h
  have h1 : x a = -1 := by linear_combination h
  have := norm_le_pi_norm x a
  rw [h1] at this
  simp at this
  linarith

theorem chart_mem {v : EE k r} (hv : v ∈ Metric.ball (0 : EE k r) 1) : chart k r v ∈ GG k r := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have hx : ‖v.2.1‖ < 1 := lt_of_le_of_lt ((norm_fst_le _).trans (norm_snd_le _)) (mem_ball_zero_iff.1 hv)
  unfold chart
  rw [Matrix.exp_neg]
  exact hG.mul_mem _ wC_mem _ (hG.mul_mem _ (hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem _ (exp_N _).1) _
    (bc_mem (one_add_ne hx))) _ (exp_lieElementFrobeniusMatrix_mem_besselUWb _).1) _ (exp_N _).1)

def UU (k r : ℕ) (ρ : ℝ) : Set (Mt k r) := (fun x => Matrix.of.symm (chart k r x)) '' Metric.ball 0 ρ

theorem meas_UU {ρ : ℝ} (hρ : ρ ≤ 1) : MeasurableSet (UU k r ρ) :=
  meas_img (F := Mt k r) ((GlobalTheory.T.bigCellExponentialChart_strictDifferentiable_summary k r).2.1.mono (Metric.ball_subset_ball hρ))

theorem mem_UU {ρ : ℝ} (hρ : ρ ≤ 1) {x : Fin r → ℂ} (hx : ∀ a, x a ≠ 0) {n n' m : Mt k r}
    (hn : Matrix.of n ∈ Nset k r) (hn' : Matrix.of n' ∈ Nset k r) (hm : Matrix.of m ∈ Formalism.FourierDecayAlt.B2.UWb k r) :
    lmulM (wC k r) ((Matrix.of n)⁻¹ * bigCell k r x 1 * Matrix.of m * Matrix.of n') ∈ UU k r ρ ↔
      x ∈ Metric.ball (fun _ => 1 : Fin r → ℂ) ρ ∧ ((n, n'), m) ∈ (expSet (Nset k r) (Metric.ball 0 ρ) ×ˢ
        expSet (Nset k r) (Metric.ball 0 ρ)) ×ˢ expSet (Formalism.FourierDecayAlt.B2.UWb k r) (Metric.ball 0 ρ) := by
  have hw : IsUnit (wC k r).det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ wC_mem
  constructor
  · rintro ⟨v, hv, h⟩
    have hv' := hv
    rw [← Prod.mk_zero_zero, ← ball_prod_same, ← Prod.mk_zero_zero, ← ball_prod_same, ← Prod.mk_zero_zero,
      ← ball_prod_same] at hv'
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hv'
    have h' : chart k r v = wC k r * ((Matrix.of n)⁻¹ * bigCell k r x 1 * Matrix.of m * Matrix.of n') := h
    unfold chart at h'
    rw [Matrix.exp_neg] at h'
    have h'' := (Matrix.isUnit_iff_isUnit_det _).2 hw |>.mul_left_cancel h'
    obtain ⟨e1, e2, e3, e4⟩ := GlobalTheory.T.besselBigCell_coordinates_unique k r _ _ (one_add_ne ((mem_ball_zero_iff.1 h3).trans_le hρ)) hx
      _ (exp_N _) _ hn _ (exp_N _) _ hn' _ (exp_lieElementFrobeniusMatrix_mem_besselUWb _) _ hm h''
    refine ⟨?_, ⟨⟨_, h1, e1⟩, ⟨_, h2, e4⟩⟩, ⟨_, h4, e3⟩⟩
    rw [← e2, mem_ball_iff_norm]
    have : ((fun a => 1 + v.2.1 a) - fun _ => 1 : Fin r → ℂ) = v.2.1 := by funext a; simp
    rw [this]; exact mem_ball_zero_iff.1 h3
  · rintro ⟨hx1, ⟨⟨X, h1, e1⟩, ⟨X', h2, e2⟩⟩, ⟨Y, h3, e3⟩⟩
    refine ⟨((X, X'), (x - fun _ => 1, Y)), ?_, ?_⟩
    · rw [← Prod.mk_zero_zero, ← ball_prod_same, ← Prod.mk_zero_zero, ← ball_prod_same, ← Prod.mk_zero_zero,
        ← ball_prod_same]
      exact ⟨⟨h1, h2⟩, mem_ball_zero_iff.2 (mem_ball_iff_norm.1 hx1), h3⟩
    · have e1' : NormedSpace.exp (um X) = Matrix.of n := e1
      have e2' : NormedSpace.exp (um X') = Matrix.of n' := e2
      have e3' : NormedSpace.exp (um Y) = Matrix.of m := e3
      show chart k r _ = wC k r * ((Matrix.of n)⁻¹ * bigCell k r x 1 * Matrix.of m * Matrix.of n')
      unfold chart
      rw [Matrix.exp_neg]
      simp only [e1', e2', e3', Pi.sub_apply, add_sub_cancel]

theorem ne_zero_of_weight {x : Fin r → ℂ} (h : Formalism.FourierDecayAlt.B2.cWeight k r x ≠ 0) (a : Fin r) : x a ≠ 0 := by
  intro h0
  apply h
  refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
  have : 2 * (Mdim k r a - 2) ≠ 0 := by
    have := a.isLt
    unfold Mdim; omega
  rw [h0, norm_zero, zero_pow this]

theorem meas_formula (μG μN μb : Measure (Mt k r)) (hG : IsHaarOn (GG k r) μG) (hN : IsHaarOn (Nset k r) μN)
    (hb : IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) μb) (C : ℝ≥0∞)
    (hC : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG = C * ∫⁻ x : Fin r → ℂ,
      ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f ((Matrix.of p.1.1)⁻¹ * bigCell k r x 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂((μN.prod μN).prod μb))
    {ρ : ℝ} (hρ : ρ ≤ 1) :
    μG (UU k r ρ) = C * ((∫⁻ x in Metric.ball (fun _ => 1 : Fin r → ℂ) ρ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x)) *
      (μN (expSet (Nset k r) (Metric.ball 0 ρ)) * μN (expSet (Nset k r) (Metric.ball 0 ρ)) *
        μb (expSet (Formalism.FourierDecayAlt.B2.UWb k r) (Metric.ball 0 ρ)))) := by
  have := hN.1
  have := hb.1
  have hl : Measurable (lmulM (wC k r) : Mt k r → Mt k r) :=
    Continuous.measurable (α := Mt k r) (γ := Mt k r)
      ((continuous_const (y := wC k r)).matrix_mul (continuous_id (X := Mat k r)))
  have hwm : Measurable fun x : Fin r → ℂ => ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x) := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    unfold Formalism.FourierDecayAlt.B2.cWeight
    fun_prop
  have hU := hl (meas_UU (k := k) (r := r) hρ)
  have h1 := hC _ (measurable_one.indicator hU)
  rw [lintegral_indicator_one hU, ← Measure.map_apply hl (meas_UU hρ), hG.2.2.2 _ wC_mem] at h1
  rw [h1, ← Measure.prod_prod, ← Measure.prod_prod, ← lintegral_mul_const _ hwm,
    ← lintegral_indicator Metric.isOpen_ball.measurableSet]
  congr 1
  refine lintegral_congr fun x => ?_
  by_cases hw : Formalism.FourierDecayAlt.B2.cWeight k r x = 0
  · simp [hw, Set.indicator]
  have hx := ne_zero_of_weight hw
  have hae : ∀ᵐ p ∂((μN.prod μN).prod μb), (Matrix.of p.1.1 ∈ Nset k r ∧ Matrix.of p.1.2 ∈ Nset k r) ∧
      Matrix.of p.2 ∈ Formalism.FourierDecayAlt.B2.UWb k r := by
    have a1 : ∀ᵐ n ∂μN, Matrix.of n ∈ Nset k r := hN.2.2.1
    have a2 : ∀ᵐ n ∂μb, Matrix.of n ∈ Formalism.FourierDecayAlt.B2.UWb k r := hb.2.2.1
    exact (Measure.quasiMeasurePreserving_fst.ae ((Measure.quasiMeasurePreserving_fst.ae a1).and
      (Measure.quasiMeasurePreserving_snd.ae a1))).and (Measure.quasiMeasurePreserving_snd.ae a2)
  have hS := ((meas_expSet (Nset k r) ρ).prod (meas_expSet (Nset k r) ρ)).prod
    (meas_expSet (Formalism.FourierDecayAlt.B2.UWb k r) ρ)
  by_cases hx1 : x ∈ Metric.ball (fun _ => 1 : Fin r → ℂ) ρ
  · rw [Set.indicator_of_mem hx1, ← lintegral_indicator_one hS]
    congr 1
    refine lintegral_congr_ae (hae.mono fun p hp => ?_)
    have := mem_UU hρ hx hp.1.1 hp.1.2 hp.2
    simp only [hx1, true_and] at this
    classical
    simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
    exact if_congr this rfl rfl
  · rw [Set.indicator_of_notMem hx1]
    refine mul_eq_zero_of_right _ ?_
    rw [← lintegral_zero (μ := (μN.prod μN).prod μb)]
    refine lintegral_congr_ae (hae.mono fun p hp => ?_)
    have := mem_UU hρ hx hp.1.1 hp.1.2 hp.2
    simp only [hx1, false_and, iff_false] at this
    exact Set.indicator_of_notMem (s := lmulM (wC k r) ⁻¹' UU k r ρ) this _

theorem vol_ball (ρ : ℝ) : volume (dE k r '' Metric.ball (0 : EE k r) ρ) =
    2 ^ r * (volume (Metric.ball (0 : lieE (Nset k r)) ρ) * volume (Metric.ball (0 : lieE (Nset k r)) ρ) *
      (volume (Metric.ball (0 : Fin r → ℂ) ρ) * volume (Metric.ball (0 : lieE (Formalism.FourierDecayAlt.B2.UWb k r)) ρ))) := by
  rw [GlobalTheory.T.volume_image_of_sqrt_two_isometric_linearEquiv _ _ _ r (dE k r) norm_dL _ Metric.isOpen_ball.measurableSet, ← Prod.mk_zero_zero,
    ← ball_prod_same, ← Prod.mk_zero_zero, ← ball_prod_same, ← Prod.mk_zero_zero, ← ball_prod_same,
    Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod,
    Measure.prod_prod]

theorem mul_ringHom_units_ratio {C I a m b c d : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ⊤) (hb' : b ≠ ⊤) (hc' : c ≠ ⊤) (hd' : d ≠ ⊤) :
    C * (I * (a * a * m)) / (d * (a * a * (b * c))) = C / d * (I / b * (m / c)) := by
  have h : a * a ≠ 0 := mul_ne_zero ha ha
  have h' : a * a ≠ ⊤ := ENNReal.mul_ne_top ha' ha'
  rw [show C * (I * (a * a * m)) = (a * a) * (C * (I * m)) by ring,
    show d * (a * a * (b * c)) = (a * a) * (d * (b * c)) by ring, ENNReal.mul_div_mul_left _ _ h h',
    div_eq_mul_inv, ENNReal.mul_inv (Or.inr (ENNReal.mul_ne_top hb' hc')) (Or.inl hd'),
    ENNReal.mul_inv (Or.inr hc') (Or.inl hb')]
  simp only [div_eq_mul_inv]; ring

theorem bigCell_integral : ∀ (k r : ℕ) (μG μb : Measure (Mt k r)) (c cb : ℝ), 0 < c → 0 < cb → IsHaarOn (GG k r) μG → HasDens (GG k r) μG (ENNReal.ofReal c) → IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) μb → HasDens (Formalism.FourierDecayAlt.B2.UWb k r) μb (ENNReal.ofReal cb) → ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG = ENNReal.ofReal (c / cb * 2 ^ r) * ∫⁻ x : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r, f ((Matrix.of p.1.1)⁻¹ * bigCell k r x 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂(((haarLie (Nset k r) 1).prod (haarLie (Nset k r) 1)).prod μb) := by
  intro k r μG μb c cb hc hcb hG hdG hb hdb
  have hN : IsHaarOn (Nset k r) (haarLie (Nset k r) 1) := GlobalTheory.T.haarLie_isHaarOn_unipotentRadical k r 1 one_pos ENNReal.one_lt_top
  obtain ⟨C, -, hC⟩ := Formalism.FourierDecayAlt.P.iterated_integration_formula k r μG (haarLie (Nset k r) 1) μb
    ((GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μG).1.1 hG)
    ((GlobalTheory.HaarNotions.isHaarOn_iff_groups k r _).2.1.1 hN)
    ((GlobalTheory.HaarNotions.isHaarOn_iff (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r) (Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r) μb).1 hb)
  suffices h : (C : ℝ≥0∞) = ENNReal.ofReal (c / cb * 2 ^ r) by rw [← h]; exact hC
  have t1 := GlobalTheory.T.tendsto_measure_image_ball_div_volume _ (GG k r) μG _ (matGroup_of (Formalism.FourierDecayAlt.P.unitary_group_closed k r)) hG hdG (EE k r)
    (chart k r) (dE k r) (GlobalTheory.T.bigCellExponentialChart_strictDifferentiable_summary k r).1
    (Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) fun v hv => chart_mem hv) (fun i j => by
      obtain ⟨D, h1, h2⟩ := (GlobalTheory.T.bigCellExponentialChart_strictDifferentiable_summary k r).2.2 i j
      exact ⟨D, h1, fun v => by rw [h2, ← um_dL]; rfl⟩)
  have h2r : (2 : ℝ≥0∞) ^ r ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have h2r0 : (2 : ℝ≥0∞) ^ r ≠ 0 := pow_ne_zero _ two_ne_zero
  have hcb0 : ENNReal.ofReal cb ≠ 0 := by simpa using hcb
  have t2 := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞) / 2 ^ r)
    (ENNReal.Tendsto.mul (GlobalTheory.T.tendsto_ball_mean_bigCellWeight k r) (Or.inl one_ne_zero) hdb (Or.inr ENNReal.one_ne_top))
    (Or.inr (ENNReal.div_ne_top ENNReal.coe_ne_top h2r0))
  have t3 : ENNReal.ofReal c = (C : ℝ≥0∞) / 2 ^ r * (1 * ENNReal.ofReal cb) := by
    refine tendsto_nhds_unique (t1.congr' ?_) t2
    filter_upwards [Ioc_mem_nhdsGT (one_pos (α := ℝ))] with ρ hρ
    have := meas_formula μG _ μb hG hN hb C hC hρ.2
    unfold UU at this
    rw [this, vol_ball, haarLie_expSet]
    exact mul_ringHom_units_ratio (Metric.measure_ball_pos _ _ hρ.1).ne' measure_ball_lt_top.ne measure_ball_lt_top.ne
      measure_ball_lt_top.ne h2r
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos hcb, t3, one_mul,
    ENNReal.mul_div_cancel_right hcb0 ENNReal.ofReal_ne_top, ENNReal.ofReal_pow (by norm_num)]
  simp only [ENNReal.ofReal_ofNat]
  rw [ENNReal.div_mul_cancel h2r0 h2r]

end GlobalTheory.CellDens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBigCellHaarDensityConstantStatement
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_bigCell_haar_density_constant : ∀ (k r : ℕ) (μG μb : Measure (Mt k r)) (c cb : ℝ), 0 < c → 0 < cb → IsHaarOn (GG k r) μG → HasDens (GG k r) μG (ENNReal.ofReal c) → IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) μb → HasDens (Formalism.FourierDecayAlt.B2.UWb k r) μb (ENNReal.ofReal cb) → ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG = ENNReal.ofReal (c / cb * 2 ^ r) * ∫⁻ x : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r, f ((Matrix.of p.1.1)⁻¹ * bigCell k r x 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂(((haarLie (Nset k r) 1).prod (haarLie (Nset k r) 1)).prod μb) := by
  first | exact @GlobalTheory.CellDens.bigCell_integral | exact GlobalTheory.CellDens.bigCell_integral | (intros; apply GlobalTheory.CellDens.bigCell_integral <;> assumption)
end
