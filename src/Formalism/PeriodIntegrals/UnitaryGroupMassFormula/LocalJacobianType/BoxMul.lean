module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulAlt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulA

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.GoodTransvection
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.FactorOneOfDiscrete
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace PI.NglqJacSplitW

section Mod

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  [LocallyCompactSpace F]

theorem modF_of_ne {a : F} (h : a ≠ 0) :
    modF F a = ((distribHaarChar F (Units.mk0 a h) : ℝ≥0) : ℝ≥0∞) := by
  rw [modF.eq_1]
  simp [h]

theorem modF_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : modF F (a * b) = modF F a * modF F b := by
  rw [modF_of_ne (mul_ne_zero ha hb), modF_of_ne ha, modF_of_ne hb,
    show Units.mk0 (a * b) (mul_ne_zero ha hb) = Units.mk0 a ha * Units.mk0 b hb from Units.ext rfl, map_mul]
  push_cast
  rfl

end Mod

end PI.NglqJacSplitW
end
end

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace PI.NglqJacSplitW

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

def phiM (M : Matrix ι ι F) (hM : IsUnit M.det) : (ι → F) ≃ₜ+ (ι → F) where
  toFun x := M *ᵥ x
  invFun x := M⁻¹ *ᵥ x
  left_inv x := by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM]
  right_inv x := by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM]
  map_add' x y := Matrix.mulVec_add M x y
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

def chiM (M : Matrix ι ι F) (hM : IsUnit M.det) : ℝ≥0 :=
  letI := borel (ι → F)
  haveI : BorelSpace (ι → F) := ⟨rfl⟩
  addEquivAddHaarChar (phiM M hM)

theorem chiM_spec [mF : MeasurableSpace (ι → F)] [hB : BorelSpace (ι → F)] (M : Matrix ι ι F)
    (hM : IsUnit M.det) (ν : Measure (ι → F)) [ν.IsAddHaarMeasure] (S : Set (ι → F)) :
    ν ((fun x => M *ᵥ x) '' S) = chiM M hM * ν S := by
  obtain rfl : mF = borel (ι → F) := hB.measurable_eq
  let _ : MeasurableSpace (ι → F) := borel _
  have _ : BorelSpace (ι → F) := ⟨rfl⟩
  have e : chiM M hM = addEquivAddHaarChar (phiM M hM) := rfl
  have himg : (fun x => M *ᵥ x) '' S = (phiM M hM).symm ⁻¹' S := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : (phiM M hM).symm ((phiM M hM) x) = x := (phiM M hM).symm_apply_apply x
      rw [show M *ᵥ x = (phiM M hM) x from rfl, this]
      exact hx
    · intro hy
      exact ⟨(phiM M hM).symm y, hy, (phiM M hM).apply_symm_apply y⟩
  have key := addEquivAddHaarChar_smul_preimage ν (X := S) (phiM M hM).symm
  rw [addEquivAddHaarChar_symm, ENNReal.smul_def, smul_eq_mul] at key
  rw [himg, e, ← key, ← mul_assoc, ← ENNReal.coe_mul,
    mul_inv_cancel₀ (addEquivAddHaarChar_pos (phiM M hM)).ne', ENNReal.coe_one, one_mul]

theorem chiM_mul (A B : Matrix ι ι F) (hA : IsUnit A.det) (hB : IsUnit B.det)
    (hAB : IsUnit (A * B).det) : chiM (A * B) hAB = chiM A hA * chiM B hB := by
  let _ : MeasurableSpace (ι → F) := borel _
  have _ : BorelSpace (ι → F) := ⟨rfl⟩
  have e : ∀ (N : Matrix ι ι F) (hN : IsUnit N.det), chiM N hN = addEquivAddHaarChar (phiM N hN) :=
    fun _ _ => rfl
  rw [e, e, e, show phiM (A * B) hAB = (phiM B hB).trans (phiM A hA) from
    ContinuousAddEquiv.ext fun x => (Matrix.mulVec_mulVec x A B).symm, addEquivAddHaarChar_trans, mul_comm]

theorem chiM_one (h : IsUnit (1 : Matrix ι ι F).det) : chiM (1 : Matrix ι ι F) h = 1 := by
  let _ : MeasurableSpace (ι → F) := borel _
  have _ : BorelSpace (ι → F) := ⟨rfl⟩
  have e : chiM (1 : Matrix ι ι F) h = addEquivAddHaarChar (phiM 1 h) := rfl
  rw [e, show phiM 1 h = ContinuousAddEquiv.refl _ from
    ContinuousAddEquiv.ext fun x => Matrix.one_mulVec x, addEquivAddHaarChar_refl]

theorem chiM_congr {A B : Matrix ι ι F} (e : A = B) (hA : IsUnit A.det) (hB : IsUnit B.det) :
    chiM A hA = chiM B hB := by
  subst e
  rfl

theorem chiM_pos (M : Matrix ι ι F) (hM : IsUnit M.det) : 0 < chiM M hM := by
  let _ : MeasurableSpace (ι → F) := borel _
  have _ : BorelSpace (ι → F) := ⟨rfl⟩
  exact addEquivAddHaarChar_pos (phiM M hM)

theorem exists_test_set [MeasurableSpace (ι → F)] [BorelSpace (ι → F)] (ν : Measure (ι → F))
    [ν.IsAddHaarMeasure] : ∃ K : Set (ι → F), MeasurableSet K ∧ ν K ≠ 0 ∧ ν K ≠ ∞ := by
  obtain ⟨K, hKc, hK0⟩ := exists_compact_mem_nhds (0 : ι → F)
  exact ⟨K, hKc.isClosed.measurableSet, (MeasureTheory.Measure.measure_pos_of_mem_nhds (μ := ν) hK0).ne', hKc.measure_lt_top.ne⟩

theorem chiM_diagOne (hD : DiagOne) (i : ι) (a : F) (ha : a ≠ 0)
    (h : IsUnit (diagonal (Function.update (1 : ι → F) i a)).det) :
    (chiM (diagonal (Function.update (1 : ι → F) i a)) h : ℝ≥0∞) = modF F a := by
  let _ : MeasurableSpace (ι → F) := borel _
  have _ : BorelSpace (ι → F) := ⟨rfl⟩
  obtain ⟨K, hKm, hK0, hKt⟩ := exists_test_set (Measure.addHaar : Measure (ι → F))
  have h1 := chiM_spec _ h (Measure.addHaar : Measure (ι → F)) K
  have h2 := hD F ι i a ha (Measure.addHaar : Measure (ι → F)) inferInstance K hKm
  have hfun : (fun x => diagonal (Function.update (1 : ι → F) i a) *ᵥ x) = fun x => Function.update x i (a * x i) := by
    funext x j
    by_cases hj : j = i
    · subst hj
      simp [Matrix.mulVec_diagonal]
    · simp [Matrix.mulVec_diagonal, Function.update_of_ne hj]
  rw [hfun] at h1
  rw [h1] at h2
  exact (ENNReal.mul_left_inj hK0 hKt).mp h2

def Good (M : Matrix ι ι F) : Prop :=
  ∀ h : IsUnit M.det, (chiM M h : ℝ≥0∞) = modF F M.det

theorem good_mul {A B : Matrix ι ι F} (hA0 : A.det ≠ 0) (hB0 : B.det ≠ 0)
    (hA : Good A) (hB : Good B) : Good (A * B) := by
  intro h
  rw [chiM_mul A B (isUnit_iff_ne_zero.mpr hA0) (isUnit_iff_ne_zero.mpr hB0) h, ENNReal.coe_mul,
    hA, hB, det_mul, modF_mul hA0 hB0]

theorem good_one : Good (1 : Matrix ι ι F) := by
  intro h
  rw [chiM_one, det_one, modF_of_ne (one_ne_zero : (1 : F) ≠ 0)]
  simp

theorem good_diagonal (hD : DiagOne) (D : ι → F) (hD0 : ∀ i, D i ≠ 0) : Good (diagonal D) := by
  classical
  have key : ∀ s : Finset ι, ∀ D : ι → F, (∀ i, D i ≠ 0) → (∀ i ∉ s, D i = 1) → Good (diagonal D) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro D _ h1
      have : D = 1 := funext fun i => h1 i (Finset.notMem_empty i)
      rw [this, show diagonal (1 : ι → F) = 1 from diagonal_one]
      exact good_one
    | @insert i s hi ih =>
      intro D hD0 h1
      have hsplit : diagonal D = diagonal (Function.update D i 1) * diagonal (Function.update (1 : ι → F) i (D i)) := by
        rw [diagonal_mul_diagonal]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Function.update_of_ne hj]
      have hdet1 : (diagonal (Function.update (1 : ι → F) i (D i))).det = D i := by
        rw [det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
        simp
      have hne : ∀ j, Function.update D i 1 j ≠ 0 := fun j => by
        by_cases hj : j = i
        · subst hj
          simp
        · rw [Function.update_of_ne hj]
          exact hD0 j
      rw [hsplit]
      refine good_mul ?_ (by rw [hdet1]; exact hD0 i) (ih _ hne fun j hj => ?_) fun h => ?_
      · rw [det_diagonal]
        exact Finset.prod_ne_zero_iff.mpr fun j _ => hne j
      · by_cases hji : j = i
        · subst hji
          simp
        · rw [Function.update_of_ne hji]
          exact h1 j (by simp [hji, hj])
      · rw [chiM_diagOne hD i (D i) (hD0 i) h, hdet1]
  exact key Finset.univ D hD0 fun i hi => absurd (Finset.mem_univ i) hi

theorem transvection_conj {i j : ι} (hij : i ≠ j) {c : F} (hc : c ≠ 0) :
    transvection i j c = diagonal (Function.update (1 : ι → F) i c) * transvection i j 1 *
      diagonal (Function.update (1 : ι → F) i c⁻¹) := by
  ext k l
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hk : k = i <;> by_cases hl : l = i <;> simp_all <;>
    split_ifs <;> simp_all [eq_comm]

theorem good_transvection (i j : ι) (hij : i ≠ j) (c : F) : Good (transvection i j c) := by
  have hT : ∀ c : F, IsUnit (transvection i j c).det := fun c => by
    rw [Matrix.det_transvection_of_ne (i := i) (j := j) hij c]
    exact isUnit_one
  have h1u : IsUnit (1 : Matrix ι ι F).det := by
    rw [det_one]
    exact isUnit_one
  have hdd : ∀ c : F, (diagonal (Function.update (1 : ι → F) i c)).det = c := fun c => by
    rw [det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  have hDu : ∀ c : F, c ≠ 0 → IsUnit (diagonal (Function.update (1 : ι → F) i c)).det := fun c hc => by
    rw [hdd]
    exact isUnit_iff_ne_zero.mpr hc
  have hmod1 : modF F 1 = 1 := by
    have := good_one h1u
    rw [chiM_one, det_one] at this
    simpa using this.symm
  have hconst : ∀ c : F, c ≠ 0 →
      chiM (transvection i j c) (hT c) = chiM (transvection i j 1) (hT 1) := by
    intro c hc
    have hDD : diagonal (Function.update (1 : ι → F) i c) * diagonal (Function.update (1 : ι → F) i c⁻¹) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext k
      by_cases hk : k = i
      · subst hk
        simp [hc]
      · simp [Function.update_of_ne hk]
    have hprod : chiM (diagonal (Function.update (1 : ι → F) i c)) (hDu c hc) * chiM (diagonal (Function.update (1 : ι → F) i c⁻¹)) (hDu _ (inv_ne_zero hc)) = 1 := by
      rw [← chiM_mul _ _ _ _ (by rw [hDD]; exact h1u), chiM_congr hDD _ h1u, chiM_one]
    have hu1 : IsUnit (diagonal (Function.update (1 : ι → F) i c) * transvection i j 1).det := by
      rw [det_mul]
      exact (hDu c hc).mul (hT 1)
    have hu2 : IsUnit (diagonal (Function.update (1 : ι → F) i c) * transvection i j 1 * diagonal (Function.update (1 : ι → F) i c⁻¹)).det := by
      rw [← transvection_conj hij hc]
      exact hT c
    rw [chiM_congr (transvection_conj hij hc) (hT c) hu2,
      chiM_mul _ _ hu1 (hDu _ (inv_ne_zero hc)) hu2, chiM_mul _ _ (hDu c hc) (hT 1) hu1]
    calc chiM (diagonal (Function.update (1 : ι → F) i c)) (hDu c hc) * chiM (transvection i j 1) (hT 1) *
          chiM (diagonal (Function.update (1 : ι → F) i c⁻¹)) (hDu _ (inv_ne_zero hc))
        = chiM (transvection i j 1) (hT 1) * (chiM (diagonal (Function.update (1 : ι → F) i c)) (hDu c hc) *
          chiM (diagonal (Function.update (1 : ι → F) i c⁻¹)) (hDu _ (inv_ne_zero hc))) := by ring
      _ = chiM (transvection i j 1) (hT 1) := by rw [hprod, mul_one]
  have hc1 : chiM (transvection i j c) (hT c) = 1 := by
    by_cases hc : c = 0
    · subst hc
      rw [chiM_congr (Matrix.transvection_zero (i := i) (j := j)) (hT 0) h1u, chiM_one]
    · have hsq : chiM (transvection i j c) (hT c) * chiM (transvection i j c) (hT c) =
          chiM (transvection i j (c + c)) (hT (c + c)) := by
        rw [← chiM_mul _ _ (hT c) (hT c)
          (by rw [Matrix.transvection_mul_transvection_same (i := i) (j := j) hij]; exact hT _)]
        exact chiM_congr (Matrix.transvection_mul_transvection_same (i := i) (j := j) hij c c) _ _
      have hx0 := (chiM_pos _ (hT c)).ne'
      by_cases h2 : c + c = 0
      · have h0 : chiM (transvection i j (c + c)) (hT (c + c)) = 1 := by
          rw [chiM_congr (show transvection i j (c + c) = 1 by rw [h2, Matrix.transvection_zero])
            (hT (c + c)) h1u, chiM_one]
        rw [h0] at hsq
        exact (pow_left_inj₀ (chiM_pos _ (hT c)).le zero_le_one two_ne_zero).mp (by rw [sq, hsq, one_pow])
      · rw [hconst (c + c) h2, ← hconst c hc] at hsq
        exact mul_left_cancel₀ hx0 (hsq.trans (mul_one _).symm)
  intro h
  rw [chiM_congr rfl h (hT c), hc1, Matrix.det_transvection_of_ne (i := i) (j := j) hij c, hmod1]
  simp

theorem linModulus_of (hD : DiagOne) : LinModulus := by
  intro F _ _ _ _ _ _ ι _ _ _ _ M hM ν hν S _
  have hG : Good M := Matrix.diagonal_transvection_induction_of_det_ne_zero Good M hM
    (fun D hD0 => good_diagonal hD D fun i => by
      rw [det_diagonal] at hD0
      exact Finset.prod_ne_zero_iff.mp hD0 i (Finset.mem_univ i))
    (fun t => good_transvection t.i t.j t.hij t.c)
    (fun A B hA hB gA gB => good_mul hA hB gA gB)
  rw [chiM_spec M (isUnit_iff_ne_zero.mpr hM) ν S, hG]

end PI.NglqJacSplitW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.DiagonalOneJacobian
noncomputable section

open MeasureTheory Set Function Topology
open scoped ENNReal NNReal Pointwise

namespace PI.NglqJacSplitW

section Diag

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

def scaleAt (i : ι) (a : F) (ha : a ≠ 0) : (ι → F) ≃ₜ+ (ι → F) where
  toFun x := update x i (a * x i)
  invFun x := update x i (a⁻¹ * x i)
  left_inv x := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [inv_mul_cancel_left₀ ha]
    · simp [update_of_ne hj]
  right_inv x := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [mul_inv_cancel_left₀ ha]
    · simp [update_of_ne hj]
  map_add' x y := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [mul_add]
    · simp [update_of_ne hj]
  continuous_toFun := continuous_id.update i (continuous_const.mul (continuous_apply i))
  continuous_invFun := continuous_id.update i (continuous_const.mul (continuous_apply i))

theorem image_update_pi (i : ι) (a : F) (_ha : a ≠ 0) (s : ι → Set F) :
    (fun x => update x i (a * x i)) '' (univ.pi s) =
      univ.pi (update s i ((fun y => a * y) '' s i)) := by
  ext y
  simp only [Set.mem_image, Set.mem_univ_pi]
  constructor
  · rintro ⟨x, hx, rfl⟩ j
    by_cases hj : j = i
    · subst hj
      simp only [update_self]
      exact ⟨x j, hx j, rfl⟩
    · simp only [update_of_ne hj]
      exact hx j
  · intro hy
    have hyi := hy i
    simp only [update_self, Set.mem_image] at hyi
    obtain ⟨t, ht, hti⟩ := hyi
    refine ⟨update y i t, fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj
        simpa using ht
      · have := hy j
        simpa [update_of_ne hj] using this
    · funext j
      by_cases hj : j = i
      · subst hj
        simp [hti]
      · simp [update_of_ne hj]

end Diag

theorem diagonal_one_jacobian : DiagOne := by
  intro F _ _ _ _ _ _ ι _ _ mι bι i a ha ν hν S hS
  have hpi : mι = @MeasurableSpace.pi ι (fun _ => F) (fun _ => borel F) := by
    letI : MeasurableSpace F := borel F
    haveI : BorelSpace F := ⟨rfl⟩
    rw [bι.measurable_eq]
    exact (Pi.borelSpace (ι := ι) (X := fun _ => F)).measurable_eq.symm
  subst hpi
  letI mF : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  haveI := hν
  set μ : Measure F := Measure.addHaar with hμ
  set P : Measure (ι → F) := Measure.pi fun _ => μ with hP
  set m' : ℝ≥0 := distribHaarChar F (Units.mk0 a ha) with hm'
  have hmod : modF F a = (m' : ℝ≥0∞) := by
    rw [modF, dif_neg ha, hm']
  set φ := scaleAt i a ha with hφ
  have himg : ∀ T : Set (ι → F), φ '' T = φ.symm ⁻¹' T := fun T => by
    rw [Set.image_eq_preimage_of_inverse (fun x => φ.symm_apply_apply x)
      (fun x => φ.apply_symm_apply x)]
  have hφm : Measurable φ.symm := φ.symm.continuous.measurable
  have hscal : ∀ t : Set F, μ ((fun y => a * y) '' t) = m' * μ t := fun t => by
    rw [distribHaarChar_mul μ (Units.mk0 a ha) t, ← Set.image_smul]
    rfl
  set μs : ι → Measure F := update (fun _ => μ) i (m' • μ) with hμs
  have hsf : ∀ j, SigmaFinite (μs j) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [hμs, update_self]
      infer_instance
    · simp only [hμs, update_of_ne hj]
      infer_instance
  have hA : Measure.pi μs = Measure.map φ.symm P := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hφm (MeasurableSet.univ_pi hs), ← himg]
    rw [show ((φ : (ι → F) → (ι → F)) '' univ.pi s) =
        (fun x => update x i (a * x i)) '' univ.pi s from rfl, image_update_pi i a ha s, hP,
      Measure.pi_pi]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj
      simp only [hμs, update_self, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hscal]
    · simp only [hμs, update_of_ne hj]
  have hB : Measure.pi μs = m' • P := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, hP, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul,
      ← Finset.mul_prod_erase Finset.univ (fun j => μs j (s j)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ (fun j => μ (s j)) (Finset.mem_univ i)]
    have herase : ∏ j ∈ Finset.univ.erase i, μs j (s j) = ∏ j ∈ Finset.univ.erase i, μ (s j) :=
      Finset.prod_congr rfl fun j hj => by
        simp only [hμs, update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [herase]
    simp only [hμs, update_self, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    ring
  have hmap : Measure.map φ.symm P = m' • P := hA.symm.trans hB
  have hPS : P (φ '' S) = m' * P S := by
    rw [himg, ← Measure.map_apply hφm hS, hmap, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul]
  have hνP : ν = ν.addHaarScalarFactor P • P := Measure.isAddLeftInvariant_eq_smul ν P
  show ν (φ '' S) = modF F a * ν S
  rw [hmod, hνP, Measure.smul_apply, Measure.smul_apply, hPS, ENNReal.smul_def, ENNReal.smul_def,
    smul_eq_mul, smul_eq_mul]
  ring

end PI.NglqJacSplitW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.Transport
noncomputable section

open MeasureTheory Set Matrix
open scoped ENNReal NNReal Pointwise

namespace PI.NglqJacSplitW

theorem linModulusV_of (h : LinModulus) : LinModulusV := by
  intro F _ _ _ _ _ _ V _ _ _ _ _ ι _ _ ⟨e⟩ f hf ν hν S hS
  haveI := hν
  letI : MeasurableSpace (ι → F) := borel (ι → F)
  haveI : BorelSpace (ι → F) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup V :=
    Topology.IsInducing.topologicalAddGroup e e.toHomeomorph.isInducing
  let E : V ≃ᵐ (ι → F) := e.toHomeomorph.toMeasurableEquiv
  have hE : ∀ x, E x = e x := fun x => rfl
  haveI : (ν.map E).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map ν e.toLinearEquiv.toAddEquiv e.continuous e.symm.continuous
  let g : (ι → F) →ₗ[F] (ι → F) :=
    (e.toLinearEquiv : V →ₗ[F] (ι → F)) ∘ₗ f ∘ₗ (e.toLinearEquiv.symm : (ι → F) →ₗ[F] V)
  have hdet : (LinearMap.toMatrix' g).det = LinearMap.det f := by
    rw [LinearMap.det_toMatrix']
    exact LinearMap.det_conj f e.toLinearEquiv
  have hmv : ∀ x, (LinearMap.toMatrix' g) *ᵥ x = g x := fun x => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have himg : (fun x => (LinearMap.toMatrix' g) *ᵥ x) '' (E '' S) = E '' (f '' S) := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext x
    rw [hmv, hE, hE]
    simp [g]
  have hES : MeasurableSet (E '' S) := E.measurableSet_image.mpr hS
  have key := h F ι (LinearMap.toMatrix' g) (by rw [hdet]; exact hf) (ν.map E) inferInstance
    (E '' S) hES
  rw [himg, hdet, MeasurableEquiv.map_apply, MeasurableEquiv.map_apply,
    E.preimage_image, E.preimage_image] at key
  exact key

end PI.NglqJacSplitW
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.BM

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp
open scoped TensorProduct ENNReal NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def mulL {ι : Type} (z : ι → Fv F v ⊗[F] E) :
    (ι → Fv F v ⊗[F] E) →ₗ[Fv F v] (ι → Fv F v ⊗[F] E) :=
  LinearMap.pi fun i => (Algebra.lmul (Fv F v) (Fv F v ⊗[F] E) (z i)).comp (LinearMap.proj i)

theorem mulL_apply {ι : Type} (z : ι → Fv F v ⊗[F] E) (c : ι → Fv F v ⊗[F] E) (i : ι) :
    mulL v z c i = z i * c i := rfl

theorem det_mulL {ι : Type} [Fintype ι] [DecidableEq ι] (z : ι → Fv F v ⊗[F] E) :
    LinearMap.det (mulL v z) = ∏ i, Algebra.norm (Fv F v) (z i) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  unfold mulL
  rw [LinearMap.det_pi]
  simp only [Algebra.norm_apply]

private theorem absV_mul_lemma (x y : Fv F v) : absV v (x * y) = absV v x * absV v y := by
  have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
  by_cases hx : Valued.v x = 0
  · have hxy : Valued.v (x * y) = 0 := by rw [map_mul, hx, zero_mul]
    simp [absV, hx, hxy]
  by_cases hy : Valued.v y = 0
  · have hxy : Valued.v (x * y) = 0 := by rw [map_mul, hy, mul_zero]
    simp [absV, hy, hxy]
  have hxy : Valued.v (x * y) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hx hy
  unfold absV
  rw [dite_eq_right hx, dite_eq_right hy, dite_eq_right hxy, ← zpow_add₀ hq, ← toAdd_mul]
  congr 2
  rw [← WithZero.coe_inj, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero,
    WithZero.coe_unzero, map_mul]

private theorem absV_one_lemma_2 : absV v (1 : Fv F v) = 1 := by
  have h1 : Valued.v (1 : Fv F v) ≠ 0 := by
    rw [map_one]
    exact one_ne_zero
  unfold absV
  rw [dite_eq_right h1]
  have h2 : WithZero.unzero h1 = 1 := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, map_one, WithZero.coe_one]
  rw [h2, toAdd_one, zpow_zero]

theorem absV_prod {ι : Type} [Fintype ι] (a : ι → Fv F v) :
    absV v (∏ i, a i) = ∏ i, absV v (a i) := by
  let f : Fv F v →* ℝ :=
    { toFun := absV v, map_one' := absV_one_lemma_2 v, map_mul' := absV_mul_lemma v }
  exact map_prod f a Finset.univ

theorem box_measure_mul : BoxMul (E := E) v := by
  classical
  intro ι _ μ _ y hy
  haveI := locallyCompact_Fv v
  haveI := secondCountable_Fv v
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  let b := Module.finBasis (Fv F v) (Fv F v ⊗[F] E)
  let eR : (Fv F v ⊗[F] E) ≃L[Fv F v] (Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    { b.equivFun with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eR.toHomeomorph.secondCountableTopology
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (ι → Fv F v ⊗[F] E) := Pi.borelSpace
  let e0 : (ι → Fv F v ⊗[F] E) ≃ₗ[Fv F v]
      (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    (LinearEquiv.piCongrRight fun _ : ι => b.equivFun).trans
      (LinearEquiv.curry (Fv F v) (Fv F v) ι (Fin _)).symm
  let eV : (ι → Fv F v ⊗[F] E) ≃L[Fv F v]
      (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    { e0 with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }
  let u : ι → (Fv F v ⊗[F] E)ˣ := fun i => (hy i).unit
  let z : ι → Fv F v ⊗[F] E := fun i => ((u i)⁻¹ : (Fv F v ⊗[F] E)ˣ)
  let h : (ι → Fv F v ⊗[F] E) ≃ₜ (ι → Fv F v ⊗[F] E) :=
    { toFun := mulL v y
      invFun := mulL v z
      left_inv := fun c => by
        funext i
        simp only [mulL_apply, z, ← mul_assoc]
        rw [show ((u i)⁻¹ : (Fv F v ⊗[F] E)ˣ).1 * y i = 1 from (u i).inv_mul, one_mul]
      right_inv := fun c => by
        funext i
        simp only [mulL_apply, z, ← mul_assoc]
        rw [show y i * ((u i)⁻¹ : (Fv F v ⊗[F] E)ˣ).1 = 1 from (u i).mul_inv, one_mul]
      continuous_toFun := IsModuleTopology.continuous_of_linearMap (mulL v y)
      continuous_invFun := IsModuleTopology.continuous_of_linearMap (mulL v z) }
  let Em := h.toMeasurableEquiv
  have hNz : ∀ i, Algebra.norm (Fv F v) (z i) * Algebra.norm (Fv F v) (y i) = 1 := fun i => by
    rw [← map_mul, show z i * y i = 1 from (u i).inv_mul, map_one]
  have hdet0 : (∏ i, Algebra.norm (Fv F v) (z i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => left_ne_zero_of_mul_eq_one (hNz i)
  have hLM := PI.NglqJacSplitW.linModulusV_of
    (PI.NglqJacSplitW.linModulus_of PI.NglqJacSplitW.diagonal_one_jacobian)
  set c := PI.NglqJacSplitW.modF (Fv F v) (∏ i, Algebra.norm (Fv F v) (z i)) with hc
  have hmap : μ.map Em = c • μ := by
    ext X hX
    rw [MeasurableEquiv.map_apply, Measure.smul_apply, smul_eq_mul]
    have hpre : Em ⁻¹' X = mulL v z '' X := by
      ext x
      constructor
      · intro hx
        exact ⟨h x, hx, h.left_inv x⟩
      · rintro ⟨w, hw, rfl⟩
        show h (h.symm w) ∈ X
        rw [h.apply_symm_apply]; exact hw
    rw [hpre, hLM (Fv F v) (ι → Fv F v ⊗[F] E) (ι × Fin _) ⟨eV⟩ (mulL v z)
      (by rw [det_mulL]; exact hdet0) μ inferInstance X hX, det_mulL]
  have hS : (Set.univ.pi fun i => {c | y i * c ∈ OEv (E := E) v}) = Em ⁻¹' Obox (E := E) v ι := by
    ext x
    simp [Obox, Em, h, mulL_apply]
  rw [hS, ← MeasurableEquiv.map_apply, hmap, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    hc, modF_Fv v _ hdet0, absV_prod, ENNReal.toReal_ofReal
      (Finset.prod_nonneg fun i _ => (absV_pos v (left_ne_zero_of_mul_eq_one (hNz i))).le),
    mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [eq_inv_of_mul_eq_one_left (hNz i), absV_inv]

end PI.UnitaryGroupMassFormula.LocJacTyp.BM
