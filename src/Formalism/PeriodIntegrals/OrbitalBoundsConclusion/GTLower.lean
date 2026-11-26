module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.DetPowUnitriB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.ConstructionC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.GTLowerOf

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.SchurFockOf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.ConstructionA
noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial MeasureTheory

theorem evA_weight_rowW {N : ℕ} (d : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d a = Formalism.GradedWeylDivisibility.rowDeg d a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype d (fun i c => c • Formalism.GradedWeylDivisibility.rowW N N i) (fun i => zero_smul _ _),
    Finset.sum_apply,
    Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [Formalism.GradedWeylDivisibility.rowW, Formalism.GradedWeylDivisibility.rowDeg]
  · intro b _ hb
    simp [Formalism.GradedWeylDivisibility.rowW, Pi.single_apply, Ne.symm hb]
  · simp

theorem evA_dom {N : ℕ} (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν) : ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin N with a.val < k, Formalism.GradedWeylDivisibility.rowDeg m a) ≤ ∑ t : Fin N with t.val < k, ν t) ∧
      ∑ a : Fin N, Formalism.GradedWeylDivisibility.rowDeg m a = ∑ t : Fin N, ν t := by
  classical
  rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ N N ν] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := Formalism.GradedWeylDivisibility.bidetDominance ℂ N N K sz hsz I m hm
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

theorem evA_ht_eq {N : ℕ} (μ : Fin N → ℕ) :
    ∑ a : Fin N, (a.val : ℤ) * (μ a : ℤ) =
      ∑ k : Fin N, ((∑ a : Fin N, (μ a : ℤ)) - ∑ a : Fin N with a.val < k.val + 1, (μ a : ℤ)) := by
  have h1 : ∀ k : Fin N, (∑ a : Fin N, (μ a : ℤ)) - ∑ a : Fin N with a.val < k.val + 1, (μ a : ℤ) =
      ∑ a : Fin N, if k.val < a.val then (μ a : ℤ) else 0 := by
    intro k
    rw [sub_eq_iff_eq_add, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> omega
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hI : (Finset.univ.filter fun k : Fin N => k.val < a.val) = Finset.Iio a := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_iff_val_lt_val]
  rw [hI, Fin.card_Iio]

theorem evA_ht {N : ℕ} (μ ν : Fin N → ℕ)
    (h1 : ∀ k : ℕ, (∑ a : Fin N with a.val < k, μ a) ≤ ∑ a : Fin N with a.val < k, ν a)
    (h2 : ∑ a : Fin N, μ a = ∑ a : Fin N, ν a) :
    ∑ a : Fin N, (a.val : ℤ) * (ν a : ℤ) ≤ ∑ a : Fin N, (a.val : ℤ) * (μ a : ℤ) := by
  rw [evA_ht_eq ν, evA_ht_eq μ]
  apply Finset.sum_le_sum
  intro k _
  have hs : (∑ a : Fin N, (μ a : ℤ)) = ∑ a : Fin N, (ν a : ℤ) := by exact_mod_cast h2
  have hk : (∑ a : Fin N with a.val < k.val + 1, (μ a : ℤ)) ≤
      ∑ a : Fin N with a.val < k.val + 1, (ν a : ℤ) := by exact_mod_cast h1 (k.val + 1)
  linarith

theorem evA_fock_right {σ : Type*} (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f g = ∑ m ∈ g.support,
      f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  classical
  unfold Formalism.REAL.fockF
  rw [Finset.sum_subset (Finset.subset_union_left : f.support ⊆ f.support ∪ g.support),
    Finset.sum_subset (Finset.subset_union_right : g.support ⊆ f.support ∪ g.support)]
  · intro m _ hm
    simp only [MvPolynomial.mem_support_iff, not_not] at hm
    simp [hm]
  · intro m _ hm
    simp only [MvPolynomial.mem_support_iff, not_not] at hm
    simp [hm]

theorem evA_diag {N : ℕ} (d : Fin N × Fin N →₀ ℕ)
    (h : (∏ v ∈ d.support, ((1 : Matrix (Fin N) (Fin N) ℂ) v.1 v.2) ^ d v) ≠ 0) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d = Finsupp.weight (Formalism.GradedWeylDivisibility.colW N N) d := by
  have hdiag : ∀ v ∈ d.support, v.1 = v.2 := by
    intro v hv
    by_contra hne
    apply h
    apply Finset.prod_eq_zero hv
    rw [Matrix.one_apply_ne hne]
    exact zero_pow (Finsupp.mem_support_iff.mp hv)
  rw [Finsupp.weight_apply, Finsupp.weight_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun v hv => ?_
  simp [Formalism.GradedWeylDivisibility.rowW, Formalism.GradedWeylDivisibility.colW, hdiag v hv]

theorem evA_hw_one {N : ℕ} (ν : Fin N → ℕ) : evalM 1 (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) = 1 := by
  have key : ∀ (k : ℕ) (h1 : k ≤ N) (h2 : k ≤ N),
      MvPolynomial.eval (fun v : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) v.1 v.2)
        (Formalism.GradedWeylDivisibility.lpMinor ℂ k h1 h2) = 1 := by
    intro k h1 h2
    unfold Formalism.GradedWeylDivisibility.lpMinor
    rw [RingHom.map_det]
    have hM : (MvPolynomial.eval fun v : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) v.1 v.2).mapMatrix
        (Matrix.of fun p q : Fin k =>
          (X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin N × Fin N) ℂ)) = 1 := by
      ext p q
      simp [Matrix.one_apply]
    rw [hM, Matrix.det_one]
  unfold evalM Formalism.GradedWeylDivisibility.hw
  rw [map_prod]
  exact Finset.prod_eq_one fun s _ => by rw [map_pow, key, one_pow]

theorem evaluation_at_one : EvalOne := by
  intro N lam s hs
  classical
  set ν := lam.natW with hνdef
  have hν : Antitone ν := fun i j hij => by
    simp only [hνdef, Formalism.BasicNotions.DomWeight.natW]
    exact Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)
  have hs' : s ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν := hs
  have hscol : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW N N) s ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hs').1
  set P := weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) ν s with hP
  have hPmem : P ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν := Formalism.GradedWeylDivisibility.dualWeylRowGraded ℂ N N ν ν s hs'
  have hPht : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.lhwinHt N N) P
      (∑ a : Fin N, (a.val : ℤ) * (ν a : ℤ)) := by
    intro d hd
    rw [hP, coeff_weightedHomogeneousComponent] at hd
    split_ifs at hd with hw
    · rw [Formalism.GradedWeylDivisibility.lhwin_weight_ht, hw]
    · exact absurd rfl hd
  have hkill : ∀ a b : Fin N, a < b → ∀ k : ℕ, 1 ≤ k → Formalism.GradedWeylDivisibility.rowDiv ℂ a b k P = 0 := by
    intro a b hab k hk
    by_contra hne
    have hQ := Formalism.GradedWeylDivisibility.lhwin_rowDiv_shift ℂ _ a b k P hPht
    have hQmem := Formalism.GradedWeylDivisibility.rowDivStable ℂ N N ν a b k P hPmem
    obtain ⟨d, hd⟩ := ne_zero_iff.mp hne
    obtain ⟨h1, h2⟩ := evA_dom ν _ hQmem d (mem_support_iff.mpr hd)
    have hge := evA_ht (Formalism.GradedWeylDivisibility.rowDeg d) ν h1 h2
    have hwt := hQ hd
    rw [Formalism.GradedWeylDivisibility.lhwin_weight_ht] at hwt
    simp only [evA_weight_rowW] at hwt
    have hab' : (a.val : ℤ) < b.val := by exact_mod_cast (Fin.lt_def.mp hab)
    have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
    nlinarith
  obtain ⟨c, hc⟩ := Formalism.GradedWeylDivisibility.hwLine ℂ N N le_rfl ν hν P hPmem hkill
  have he : extremal ℂ N lam = Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν := rfl
  have heRow : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) ν := by
    have h := Formalism.GradedWeylDivisibility.hwRowWeight ℂ N N le_rfl ν hν
    have hr : (Formalism.GradedWeylDivisibility.rowNu (r := N) ν) = ν := by
      funext a; simp [Formalism.GradedWeylDivisibility.rowNu, a.isLt]
    rwa [hr] at h
  have hsub : P.support ⊆ s.support := fun d hd => by
    rw [mem_support_iff] at hd ⊢
    rw [hP, coeff_weightedHomogeneousComponent] at hd
    split_ifs at hd with h
    · exact hd
    · exact absurd rfl hd
  have hev : evalM 1 s = evalM 1 P := by
    unfold evalM
    rw [eval_eq, eval_eq]
    symm
    rw [Finset.sum_subset hsub (fun d _ hd => by rw [mem_support_iff, not_not] at hd; simp [hd])]
    refine Finset.sum_congr rfl fun d hd => ?_
    by_cases hw : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d = ν
    · rw [hP, coeff_weightedHomogeneousComponent, if_pos hw]
    · have hcol : Finsupp.weight (Formalism.GradedWeylDivisibility.colW N N) d = ν := hscol (mem_support_iff.mp hd)
      have hz : (∏ v ∈ d.support, ((1 : Matrix (Fin N) (Fin N) ℂ) v.1 v.2) ^ d v) = 0 := by
        by_contra hne
        exact hw ((evA_diag d hne).trans hcol)
      rw [hz, mul_zero, mul_zero]
  have hfse : Formalism.REAL.fockF s (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) =
      Formalism.REAL.fockF P (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) := by
    rw [evA_fock_right s, evA_fock_right P]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hw : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) m = ν := heRow (mem_support_iff.mp hm)
    rw [hP, coeff_weightedHomogeneousComponent, if_pos hw]
  have hfce : ∀ e : MvPolynomial (Fin N × Fin N) ℂ,
      Formalism.REAL.fockF (c • e) e = c * Formalism.REAL.fockF e e := by
    intro e
    rw [evA_fock_right, evA_fock_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_smul, smul_eq_mul]; ring
  have hFne : Formalism.REAL.fockF (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) ≠ 0 := by
    have h := (Formalism.GradedWeylDivisibility.fockPos (Fin N × Fin N) _ (Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl ν)).1
    intro h0; rw [h0] at h; simp at h
  unfold normFock
  rw [he, hev, hfse, hc, hfce, mul_div_assoc, div_self hFne, mul_one]
  unfold evalM
  rw [smul_eq_C_mul, eval_mul, eval_C]
  have h1 := evA_hw_one ν
  unfold evalM at h1
  rw [h1, mul_one]

end PI.WSF
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.ConstructionB
noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial MeasureTheory Measure TopologicalSpace Matrix

theorem isCompact_unitaryGroup (N : ℕ) :
    IsCompact ((Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ))) := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hK.of_isClosed_subset ?_ ?_
  · have e : (Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) =
        {A : Matrix (Fin N) (Fin N) ℂ | A * star A = 1} := by
      ext A
      exact Matrix.mem_unitaryGroup_iff
    rw [e]
    exact isClosed_eq (continuous_id.matrix_mul continuous_star) continuous_const
  · intro A hA
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact entry_norm_bound_of_unitary hA i j

instance compactSpace_unitaryGroup (N : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin N) ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryGroup N)

theorem isMulRightInvariant_of_compact {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsHaarMeasure μ] : IsMulRightInvariant μ := by
  constructor
  intro g
  haveI : (Measure.map (fun x => x * g) μ).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right μ g
  have huniv : Measure.map (fun x => x * g) μ Set.univ = μ Set.univ := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have hfin : μ Set.univ ≠ ⊤ := measure_ne_top μ _
  have hpos : μ Set.univ ≠ 0 := (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
  have hc : (Measure.map (fun x => x * g) μ).haarScalarFactor μ = 1 := by
    have h1 := Measure.measure_isHaarMeasure_eq_smul_of_isOpen (Measure.map (fun x => x * g) μ) μ
      isOpen_univ
    rw [huniv, ENNReal.smul_def] at h1
    have h2 : ((((Measure.map (fun x => x * g) μ).haarScalarFactor μ : NNReal) : ENNReal)) = 1 := by
      have h3 : (((Measure.map (fun x => x * g) μ).haarScalarFactor μ : NNReal) : ENNReal) * μ Set.univ =
          1 * μ Set.univ := by
        rw [one_mul]
        exact h1.symm
      exact (ENNReal.mul_left_inj hpos hfin).mp h3
    exact_mod_cast h2
  refine MeasureTheory.ext_of_generate_finite {s : Set G | IsOpen s}
    BorelSpace.measurable_eq isPiSystem_isOpen ?_ huniv
  intro s hs
  rw [Measure.measure_isHaarMeasure_eq_smul_of_isOpen _ μ hs, hc, one_smul]

theorem unitary_haar_measure : HaarU := by
  intro N
  haveI : CompactSpace (Matrix.unitaryGroup (Fin N) ℂ) := compactSpace_unitaryGroup N
  let μG : Measure (Matrix.unitaryGroup (Fin N) ℂ) := Measure.haarMeasure ⊤
  haveI : μG.IsMulRightInvariant := isMulRightInvariant_of_compact μG
  have hm : Measurable (Subtype.val : Matrix.unitaryGroup (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ) :=
    measurable_subtype_coe
  refine ⟨Measure.map Subtype.val μG, ?_, ?_, ?_, ?_⟩
  · constructor
    rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ]
    have h1 := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup (Fin N) ℂ)))
    simpa using h1
  · have hmeas : MeasurableSet {x : Matrix (Fin N) (Fin N) ℂ | x ∈ Matrix.unitaryGroup (Fin N) ℂ} :=
      (isCompact_unitaryGroup N).isClosed.measurableSet
    rw [ae_map_iff hm.aemeasurable hmeas]
    exact Filter.Eventually.of_forall fun y => y.2
  · intro u hu f hf
    have hs : AEStronglyMeasurable (fun x => f (x * u)) (Measure.map Subtype.val μG) :=
      (hf.comp (continuous_mul_const u)).aestronglyMeasurable
    rw [integral_map hm.aemeasurable hs, integral_map hm.aemeasurable hf.aestronglyMeasurable]
    have h1 := integral_mul_right_eq_self (μ := μG)
      (fun y : Matrix.unitaryGroup (Fin N) ℂ => f (y : Matrix (Fin N) (Fin N) ℂ)) ⟨u, hu⟩
    simpa using h1
  · intro u hu f hf
    have hs : AEStronglyMeasurable (fun x => f (u * x)) (Measure.map Subtype.val μG) :=
      (hf.comp (continuous_const_mul u)).aestronglyMeasurable
    rw [integral_map hm.aemeasurable hs, integral_map hm.aemeasurable hf.aestronglyMeasurable]
    have h1 := integral_mul_left_eq_self (μ := μG)
      (fun y : Matrix.unitaryGroup (Fin N) ℂ => f (y : Matrix (Fin N) (Fin N) ℂ)) ⟨u, hu⟩
    simpa using h1

end PI.WSF
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.Assembly
noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial MeasureTheory

theorem schurFock_of_steps (hB : HaarU) (hC : SchurOrth) : PI.SchurFock := by
  intro N lam s hs hbd
  obtain ⟨μ, hμ⟩ := hB N
  have hprob := hμ.1
  have hae := hμ.2.1
  rw [hC N lam μ hμ s hs]
  have hint : ∫ x, ‖evalM x s‖ ^ 2 ∂μ ≤ 1 := by
    calc ∫ x, ‖evalM x s‖ ^ 2 ∂μ ≤ ∫ _x, (1 : ℝ) ∂μ := by
          apply integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) (integrable_const 1)
          filter_upwards [hae] with x hx
          exact pow_le_one₀ (norm_nonneg _) (hbd x hx)
      _ = 1 := by simp
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) hint

end PI.WSF
end
end

noncomputable section

namespace PI.WSF

theorem schurFock_of (h : PI.HwIrred) : PI.SchurFock :=
  schurFock_of_steps unitary_haar_measure (schurOrth_of h evaluation_at_one)

end PI.WSF
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionB
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.RenameTauHomogB
noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

def swapM {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if σ i = j then 1 else 0

theorem swapM_sq {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) : swapM σ * swapM σ = 1 := by
  ext i j
  simp only [swapM, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ i)]
  · simp [hσ]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), zero_mul]
  · simp

def swapGL {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) : GL (Fin n) ℂ :=
  ⟨swapM σ, swapM σ, swapM_sq σ hσ, swapM_sq σ hσ⟩

def tauB {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (a : Fin N) : Fin N :=
  if ha : a.1 < n then ⟨(σ ⟨a.1, ha⟩).1, by have := (σ ⟨a.1, ha⟩).isLt; omega⟩ else a

theorem tauB_val {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (a : Fin N) (ha : a.1 < n) :
    (tauB h σ a).1 = (σ ⟨a.1, ha⟩).1 := by
  unfold tauB; rw [dif_pos ha]

theorem tauB_of_not {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (a : Fin N) (ha : ¬ a.1 < n) :
    tauB h σ a = a := by
  unfold tauB; rw [dif_neg ha]

theorem tauB_invol {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) (a : Fin N) :
    tauB h σ (tauB h σ a) = a := by
  by_cases ha : a.1 < n
  · have h2 : (tauB h σ a).1 < n := by rw [tauB_val h σ a ha]; exact (σ _).isLt
    apply Fin.ext
    rw [tauB_val h σ _ h2]
    have e : (⟨(tauB h σ a).1, h2⟩ : Fin n) = σ ⟨a.1, ha⟩ := Fin.ext (tauB_val h σ a ha)
    rw [e, hσ]
  · rw [tauB_of_not h σ a ha, tauB_of_not h σ a ha]

theorem swap_entry_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) (a b : Fin N) :
    ((embGL ℂ n N h (swapGL σ hσ) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) b a =
      if b = tauB h σ a then 1 else 0 := by
  have ha2 := a.2
  have hb2 := b.2
  rw [embGL_apply_B]
  by_cases hb : b.1 < n <;> by_cases ha : a.1 < n
  · rw [dif_pos hb, dif_pos ha]
    show swapM σ ⟨b.1, hb⟩ ⟨a.1, ha⟩ = _
    simp only [swapM, Matrix.of_apply]
    have key : σ ⟨b.1, hb⟩ = ⟨a.1, ha⟩ ↔ b = tauB h σ a := by
      constructor
      · intro e
        apply Fin.ext
        rw [tauB_val h σ a ha, ← e, hσ]
      · intro e
        have e2 : (⟨b.1, hb⟩ : Fin n) = σ ⟨a.1, ha⟩ := Fin.ext (by
          show b.1 = (σ ⟨a.1, ha⟩).1
          rw [← tauB_val h σ a ha, e])
        rw [e2, hσ]
    by_cases hk : b = tauB h σ a
    · rw [if_pos hk, if_pos (key.mpr hk)]
    · rw [if_neg hk, if_neg (fun e => hk (key.mp e))]
  · rw [dif_pos hb, dif_neg ha, tauB_of_not h σ a ha, if_neg (fun e : b = a => ha (e ▸ hb))]
  · have hne : b ≠ tauB h σ a := by
      intro e
      apply hb
      rw [e, tauB_val h σ a ha]
      exact (σ _).isLt
    rw [dif_neg hb, if_pos ha, if_neg hne]
  · have hab : b = a := Fin.ext (by omega)
    rw [dif_neg hb, if_neg ha, tauB_of_not h σ a ha, if_pos hab]

theorem rowAct_swap_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
              (((embGL ℂ n N h (swapGL σ hσ) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose) =
      rename (fun v : Fin N × Fin N => (tauB h σ v.1, v.2)) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [rowAct_X_B, rename_X]
  rw [Finset.sum_eq_single (tauB h σ v.1)]
  · rw [Matrix.transpose_apply, swap_entry_B, if_pos rfl, map_one, one_mul]
  · intro b _ hb
    rw [Matrix.transpose_apply, swap_entry_B, if_neg hb, map_zero, zero_mul]
  · simp

theorem wnB_tau {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j)
    (v : Fin N × Fin N) : wnB n N (tauB h σ v.1, v.2) = fun j => wnB n N v (σ j) := by
  funext j
  by_cases ha : v.1.1 < n
  · have h2 : (tauB h σ v.1).1 < n := by rw [tauB_val h σ _ ha]; exact (σ _).isLt
    dsimp only [wnB]
    rw [dif_pos h2, dif_pos ha]
    have e : (⟨(tauB h σ v.1).1, h2⟩ : Fin n) = σ ⟨v.1.1, ha⟩ := Fin.ext (tauB_val h σ _ ha)
    rw [e, Pi.single_apply, Pi.single_apply]
    by_cases hj : σ j = ⟨v.1.1, ha⟩
    · rw [if_pos hj, if_pos (by rw [← hj, hσ])]
    · rw [if_neg hj, if_neg (fun e => hj (by rw [e, hσ]))]
  · have h2 : ¬ (tauB h σ v.1).1 < n := by rw [tauB_of_not h σ _ ha]; exact ha
    dsimp only [wnB]
    rw [dif_neg h2, dif_neg ha]
    rfl

theorem weight_tau_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j)
    (u : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (wnB n N) (Finsupp.mapDomain (fun v : Fin N × Fin N => (tauB h σ v.1, v.2)) u) =
      fun j => Finsupp.weight (wnB n N) u (σ j) := by
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) => c • wnB n N i) (fun _ => zero_smul _ _)
    (fun _ _ _ => add_smul _ _ _)]
  funext j
  rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.smul_apply, wnB_tau h σ hσ]

theorem rename_tau_homog_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j)
    (g : MvPolynomial (Fin N × Fin N) ℂ) (m : Fin n → ℕ) (hg : IsWeightedHomogeneous (wnB n N) g m) :
    IsWeightedHomogeneous (wnB n N) (rename (fun v : Fin N × Fin N => (tauB h σ v.1, v.2)) g)
      (fun j => m (σ j)) := by
  intro d hd
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ hd
  rw [weight_tau_B h σ hσ, hg hu]

theorem rename_tau_inj_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) :
    Function.Injective (rename (R := ℂ) (fun v : Fin N × Fin N => (tauB h σ v.1, v.2))) := by
  apply rename_injective
  intro v w e
  have e1 := congrArg Prod.fst e
  have e2 := congrArg Prod.snd e
  simp only at e1 e2
  have e3 : v.1 = w.1 := by
    rw [← tauB_invol h σ hσ v.1, e1, tauB_invol h σ hσ w.1]
  exact Prod.ext e3 e2

theorem swap_mem_B {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hW : IsStable h lam W) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) (g : MvPolynomial (Fin N × Fin N) ℂ)
    (hg : g ∈ W) : rename (fun v : Fin N × Fin N => (tauB h σ v.1, v.2)) g ∈ W := by
  have h1 := hW (swapGL σ hσ) g hg
  unfold sqAct at h1
  rw [rowAct_swap_B] at h1
  have hu : detPow ℂ N (embGL ℂ n N h (swapGL σ hσ)) lam.detShift ≠ 0 := Units.ne_zero _
  have := W.smul_mem (detPow ℂ N (embGL ℂ n N h (swapGL σ hσ)) lam.detShift)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hu, one_smul] at this

theorem PsiB_swap_B {n : ℕ} (m : Fin n → ℕ) (i : ℕ) (hi : i + 1 < n)
    (hlt : m ⟨i, by omega⟩ < m ⟨i + 1, hi⟩) :
    PsiB n m < PsiB n (fun j => m (Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩ j)) := by
  set a : Fin n := ⟨i, by omega⟩ with ha
  set b : Fin n := ⟨i + 1, hi⟩ with hb
  have hab : a ≠ b := by
    intro e
    have := congrArg Fin.val e
    simp [ha, hb] at this
  have split : ∀ f : Fin n → ℕ, ∑ j, f j = f a + f b + ∑ j ∈ (Finset.univ.erase a).erase b, f j := by
    intro f
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩)]
    ring
  rw [PsiB_apply, PsiB_apply, split, split]
  have hrest : ∑ j ∈ (Finset.univ.erase a).erase b, (n - j.1) * m (Equiv.swap a b j) =
      ∑ j ∈ (Finset.univ.erase a).erase b, (n - j.1) * m j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjb := Finset.ne_of_mem_erase hj
    have hja := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
    rw [Equiv.swap_apply_of_ne_of_ne hja hjb]
  rw [hrest, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have e1 : n - a.1 = (n - b.1) + 1 := by simp only [ha, hb]; omega
  rw [e1]
  nlinarith

theorem antitone_of_succ_B {n : ℕ} (m : Fin n → ℕ)
    (hdom : ∀ (i : ℕ) (hi : i + 1 < n), m ⟨i + 1, hi⟩ ≤ m ⟨i, by omega⟩) : Antitone m := by
  let M : ℕ → ℕ := fun k => if hk : k < n then m ⟨k, hk⟩ else 0
  have hM : Antitone M := by
    refine antitone_nat_of_succ_le fun k => ?_
    by_cases hk1 : k + 1 < n
    · simp only [M, dif_pos hk1, dif_pos (show k < n by omega)]
      exact hdom k hk1
    · simp only [M, dif_neg hk1]
      exact Nat.zero_le _
  intro a b hab
  have := hM (Fin.le_def.mp hab)
  simp only [M, dif_pos a.2, dif_pos b.2] at this
  exact this

theorem torus_fix_B {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (g : MvPolynomial (Fin N × Fin N) ℂ)
    (m : Fin n → ℕ) (hm : IsWeightedHomogeneous (wnB n N) g m) (t : Fin n → ℂˣ) :
    sqAct ℂ N lam (embGL ℂ n N h (diagGL ℂ n t)) g =
      ((∏ j, t j ^ ((m j : ℤ) + lam.detShift) : ℂˣ) : ℂ) • g := by
  unfold sqAct
  rw [embGL_diag_B, Matrix.diagonal_transpose, rowAct_diag_homog _ _ _ hm, smul_smul]
  congr 1
  have hdet : Matrix.GeneralLinearGroup.det (embGL ℂ n N h (diagGL ℂ n t)) = ∏ j, t j := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, embGL_diag_B, Matrix.det_diagonal, Units.coe_prod]
    subst h
    rw [Fin.prod_univ_castSucc]
    simp [dB]
  unfold detPow
  rw [hdet]
  have hchi : chiB (fun j => ((t j : ℂˣ) : ℂ)) m = ((∏ j, t j ^ (m j) : ℂˣ) : ℂ) := by
    simp [chiB, Units.coe_prod]
  rw [hchi, ← Units.val_mul]
  congr 1
  simp only [zpow_add, Finset.prod_mul_distrib, zpow_natCast, Finset.prod_zpow]
  rw [mul_comm]

theorem highestVec_B : HighestVec := by
  classical
  intro n N h lam W hWle hW hne
  let Pk : ℕ → Prop := fun k =>
    ∃ g ∈ W, g ≠ 0 ∧ ∃ m, IsWeightedHomogeneous (wnB n N) g m ∧ PsiB n m = k
  have hex : ∃ k, Pk k := by
    obtain ⟨f, hfW, hf0⟩ := (Submodule.ne_bot_iff W).mp hne
    by_contra hno
    push_neg at hno
    apply hf0
    rw [← comp_sum_B (wnB n N) f (f.support.image (Finsupp.weight (wnB n N)))
      (fun e he => Finset.mem_image_of_mem _ he)]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_contra hc
    exact hno _ ⟨_, graded_B h lam W hW f hfW m, hc, m, weightedHomogeneousComponent_isWeightedHomogeneous _ _, rfl⟩
  obtain ⟨k0, hk0⟩ := hex
  have hPb : ∀ k, Pk k → k ≤ n * ∑ s, lam.natW s := by
    rintro k ⟨g, hgW, hg0, m, hm, rfl⟩
    exact bound_B lam g (hWle hgW) hg0 m hm
  have hK : Pk (Nat.findGreatest Pk (n * ∑ s, lam.natW s)) := Nat.findGreatest_spec (hPb k0 hk0) hk0
  have hmax : ∀ g ∈ W, g ≠ 0 → ∀ m, IsWeightedHomogeneous (wnB n N) g m →
      PsiB n m ≤ Nat.findGreatest Pk (n * ∑ s, lam.natW s) := by
    intro g hgW hg0 m hm
    exact Nat.le_findGreatest (hPb _ ⟨g, hgW, hg0, m, hm, rfl⟩) ⟨g, hgW, hg0, m, hm, rfl⟩
  obtain ⟨g, hgW, hg0, m, hm, hmK⟩ := hK
  have hfix : ∀ u : GL (Fin n) ℂ, (∀ i j, j < i → u i j = 0) → (∀ i, u i i = 1) →
      sqAct ℂ N lam (embGL ℂ n N h u) g = g := by
    intro u hl hd
    obtain ⟨h1, h2, _⟩ := embGL_unitri_B h u hl hd
    have hs : sqAct ℂ N lam (embGL ℂ n N h u) g = Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
        (((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose) g := by
      unfold sqAct
      rw [detPow_unitri_B h u hl hd, one_smul]
    rw [hs]
    have hR : Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
        (((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose) g - g = 0 := by
      refine high_zero_B h lam W hW _ hmax _ ?_ ?_
      · refine W.sub_mem ?_ hgW
        rw [← hs]
        exact hW u g hgW
      · have := GoodB_homog (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
          (((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose)) (psiB n N)
          (fun v => GoodB_X_tri _ (fun a => by rw [Matrix.transpose_apply]; exact h1 a)
            (fun a b hab hne => h2 a b hab (by rwa [Matrix.transpose_apply] at hne)) v) g (PsiB n m)
          (homog_psi_B g m hm)
        rwa [hmK] at this
    exact sub_eq_zero.mp hR
  have hdom : ∀ (i : ℕ) (hi : i + 1 < n), m ⟨i + 1, hi⟩ ≤ m ⟨i, by omega⟩ := by
    intro i hi
    by_contra hlt
    push_neg at hlt
    let σ := Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩
    have hσ : ∀ j, σ (σ j) = j := fun j => Equiv.swap_apply_self _ _ j
    have hgt := PsiB_swap_B m i hi hlt
    have hle := hmax _ (swap_mem_B h lam W hW σ hσ g hgW)
      (fun e => hg0 (rename_tau_inj_B h σ hσ (by rw [e, map_zero])))
      _ (rename_tau_homog_B h σ hσ g m hm)
    rw [← hmK] at hle
    exact absurd hle (not_le.mpr hgt)
  have hanti : Antitone m := antitone_of_succ_B m hdom
  let mu : DomWeight n := ⟨fun j => (m j : ℤ) + lam.detShift, fun a b hab => by
    have := hanti hab
    simp only
    omega⟩
  exact ⟨g, hgW, hg0, mu, hfix, fun t => torus_fix_B h lam g m hm t⟩

end PI.WGB
end
end

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

theorem stable_complement_exists : StableCompl := stableCompl_B

theorem highest_weight_vector_exists : HighestVec := highestVec_B

end PI.WGB
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionD
noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

theorem natW_anti_D {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)

theorem extremal_mem_D (n : ℕ) (mu : DomWeight n) : extremal ℂ n mu ∈ nablaSq ℂ n mu :=
  Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl mu.natW (natW_anti_D mu)

theorem extremal_ne_D (n : ℕ) (mu : DomWeight n) : extremal ℂ n mu ≠ 0 :=
  Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl mu.natW

def sqLinD (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ) :
    MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ where
  toFun := sqAct ℂ N lam g
  map_add' x y := by simp only [sqAct, map_add (f := _), smul_add]
  map_smul' c x := by
    simp only [sqAct, RingHom.id_apply, map_smul]
    rw [smul_comm]

theorem sqLinD_apply (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqLinD N lam g f = sqAct ℂ N lam g f := rfl

theorem isEqv_zero_D {n N : ℕ} (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N) :
    IsEqv h mu lam 0 := by
  refine ⟨fun s _ => by
    simp only [LinearMap.zero_apply]
    exact Submodule.zero_mem _, fun g s _ => ?_⟩
  simp only [LinearMap.zero_apply]
  rw [← sqLinD_apply, map_zero]

theorem isEqv_smul_D {n N : ℕ} (h : n + 1 = N) {mu : DomWeight n} {lam : DomWeight N}
    {φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ} (hφ : IsEqv h mu lam φ) (c : ℂ) :
    IsEqv h mu lam (c • φ) := by
  refine ⟨fun s hs => ?_, fun g s hs => ?_⟩
  · rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ c (hφ.1 s hs)
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hφ.2 g s hs, ← sqLinD_apply, ← sqLinD_apply, map_smul]

theorem eq_on_of_extremal_D (hI : PI.HwIrred) (he : ExtremalFacts) {n N : ℕ} (h : n + 1 = N)
    {mu : DomWeight n} {lam : DomWeight N}
    {φ ψ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ}
    (hφ : IsEqv h mu lam φ) (hψ : IsEqv h mu lam ψ)
    (hext : φ (extremal ℂ n mu) = ψ (extremal ℂ n mu)) : ∀ s ∈ nablaSq ℂ n mu, φ s = ψ s := by
  let U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) := nablaSq ℂ n mu ⊓ LinearMap.ker (φ - ψ)
  have hU : U ≤ nablaSq ℂ n mu := inf_le_left
  have hstab : ∀ (g : GL (Fin n) ℂ), ∀ f ∈ U, sqAct ℂ n mu g f ∈ U := by
    rintro g f ⟨hf1, hf2⟩
    refine ⟨(he n mu).2.2 g f hf1, ?_⟩
    have hf2' : φ f = ψ f := by
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hf2
      exact hf2
    show sqAct ℂ n mu g f ∈ LinearMap.ker (φ - ψ)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hφ.2 g f hf1, hψ.2 g f hf1, hf2']
  rcases (hI n mu).2.1 U hU hstab with hbot | htop
  · exfalso
    have he_mem : extremal ℂ n mu ∈ U :=
      ⟨extremal_mem_D n mu, by
        show extremal ℂ n mu ∈ LinearMap.ker (φ - ψ)
        rw [LinearMap.mem_ker, LinearMap.sub_apply, hext, sub_self]⟩
    rw [hbot] at he_mem
    exact extremal_ne_D n mu ((Submodule.mem_bot ℂ).mp he_mem)
  · intro s hs
    have hsU : s ∈ U := by rw [htop]; exact hs
    have h2 : s ∈ LinearMap.ker (φ - ψ) := hsU.2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h2
    exact h2

theorem fixed_of_eqv_D (he : ExtremalFacts) {n N : ℕ} (h : n + 1 = N) {mu : DomWeight n} {lam : DomWeight N}
    {φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ} (hφ : IsEqv h mu lam φ) :
    IsFixedW h lam mu (φ (extremal ℂ n mu)) := by
  have hmem := extremal_mem_D n mu
  refine ⟨fun g hg1 hg2 => ?_, fun t => ?_⟩
  · rw [← hφ.2 g _ hmem, (he n mu).1 g hg1 hg2]
  · rw [← hφ.2 _ _ hmem, (he n mu).2.1 t, map_smul]

theorem equivariant_map_interlacing_unique (hI : PI.HwIrred) (he : ExtremalFacts) (ha : FixedLine) {n N : ℕ} (h : n + 1 = N)
    (lam : DomWeight N) (mu : DomWeight n)
    (φ φ' : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (hφ : IsEqv h mu lam φ) (hφ' : IsEqv h mu lam φ') (hne : ∃ s ∈ nablaSq ℂ n mu, φ' s ≠ 0) :
    Interlace h lam mu ∧ ∃ c : ℂ, ∀ s ∈ nablaSq ℂ n mu, φ s = c • φ' s := by
  have hmem := extremal_mem_D n mu
  have hne' : φ' (extremal ℂ n mu) ≠ 0 := by
    intro h0
    obtain ⟨s, hs, hs0⟩ := hne
    apply hs0
    have h3 := eq_on_of_extremal_D hI he h hφ' (isEqv_zero_D h mu lam) (by rw [h0, LinearMap.zero_apply]) s hs
    rw [h3, LinearMap.zero_apply]
  obtain ⟨⟨c, hc⟩, hint⟩ := ha n N h lam mu (φ (extremal ℂ n mu)) (φ' (extremal ℂ n mu)) (hφ.1 _ hmem)
    (hφ'.1 _ hmem) (fixed_of_eqv_D he h hφ) (fixed_of_eqv_D he h hφ') hne'
  refine ⟨hint, c, fun s hs => ?_⟩
  have h3 := eq_on_of_extremal_D hI he h hφ (isEqv_smul_D h hφ' c) (by rw [LinearMap.smul_apply, hc]) s hs
  rw [h3, LinearMap.smul_apply]

def brSupD {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  ⨆ (mu : DomWeight n) (_ : Interlace h lam mu)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (_ : IsEqv h mu lam φ), (nablaSq ℂ n mu).map φ

theorem branching_rule_decomposition (he : ExtremalFacts) (ha : FixedLine) (hb : StableCompl) (hc : HighestVec) (hd : Realize)
    {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) : nablaSq ℂ N lam = brSupD h lam := by
  have hmemS : ∀ (mu : DomWeight n) (hint : Interlace h lam mu)
      (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ),
      (nablaSq ℂ n mu).map φ ≤ brSupD h lam :=
    fun mu hint φ hφ => le_iSup_of_le mu (le_iSup_of_le hint (le_iSup_of_le φ (le_iSup_of_le hφ le_rfl)))
  have hle : brSupD h lam ≤ nablaSq ℂ N lam := by
    refine iSup_le fun mu => iSup_le fun hint => iSup_le fun φ => iSup_le fun hφ => ?_
    rintro _ ⟨s, hs, rfl⟩
    exact hφ.1 s hs
  have hstab : IsStable h lam (brSupD h lam) := by
    intro g
    have key : brSupD h lam ≤ (brSupD h lam).comap (sqLinD N lam (embGL ℂ n N h g)) := by
      refine iSup_le fun mu => iSup_le fun hint => iSup_le fun φ => iSup_le fun hφ => ?_
      rintro _ ⟨s, hs, rfl⟩
      rw [Submodule.mem_comap, sqLinD_apply, ← hφ.2 g s hs]
      exact hmemS mu hint φ hφ ⟨_, (he n mu).2.2 g s hs, rfl⟩
    intro f hf
    exact key hf
  obtain ⟨W', hW'le, hW'st, hsup, hinf⟩ := hb n N h lam (brSupD h lam) hle hstab
  by_cases hW' : W' = ⊥
  · rw [hW', sup_bot_eq] at hsup
    exact hsup.symm
  · exfalso
    obtain ⟨f, hfW, hf0, mu, hfix⟩ := hc n N h lam W' hW'le hW'st hW'
    obtain ⟨φ, hφ, hφe⟩ := hd n N h lam mu f (hW'le hfW) hfix hf0
    have hint : Interlace h lam mu := (ha n N h lam mu f f (hW'le hfW) (hW'le hfW) hfix hfix hf0).2
    have hfS : f ∈ brSupD h lam := hmemS mu hint φ hφ ⟨_, extremal_mem_D n mu, hφe⟩
    have hfI : f ∈ brSupD h lam ⊓ W' := ⟨hfS, hfW⟩
    rw [hinf] at hfI
    exact hf0 ((Submodule.mem_bot ℂ).mp hfI)

theorem gTBranch_of_steps (h : PI.HwIrred) (he : ExtremalFacts) (ha : FixedLine) (hb : StableCompl)
    (hc : HighestVec) (hd : Realize) : PI.GTBranch := by
  intro n N hnN lam
  refine ⟨fun mu φ φ' hψ hne => ?_, branching_rule_decomposition he ha hb hc hd hnN lam⟩
  have hφ : IsEqv hnN mu lam φ := hψ φ (by simp)
  have hφ' : IsEqv hnN mu lam φ' := hψ φ' (by simp)
  exact equivariant_map_interlacing_unique h he ha hnN lam mu φ φ' hφ hφ' hne

end PI.WGB
end
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GTBranch
theorem gelfand_tsetlin_branching : PI.GTBranch :=
  PI.WGB.gTBranch_of_steps highest_weight_irreducible (PI.WGB.extremalFacts_of_A highest_weight_irreducible) PI.WGB.fixed_line_exists
    PI.WGB.stable_complement_exists PI.WGB.highest_weight_vector_exists
    (PI.WGB.realize_of highest_weight_irreducible (PI.WGB.extremalFacts_of_A highest_weight_irreducible) PI.WGB.fixed_line_exists
      PI.WGB.stable_complement_exists PI.WGB.highest_weight_vector_exists)
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SchurFock
theorem schur_fock : PI.SchurFock := PI.WSF.schurFock_of highest_weight_irreducible
end

theorem gTLower_of (h2 : Formalism.BasicNotions.FactDelDualNabla) : PI.GTLower :=
  PI.WGL.gTLower_of h2 highest_weight_irreducible gelfand_tsetlin_branching schur_fock
