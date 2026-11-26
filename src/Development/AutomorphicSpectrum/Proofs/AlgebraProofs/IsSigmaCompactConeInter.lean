module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelRootIndep
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelValueIndependent

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsSigmaCompactConeInter
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix

open scoped ENNReal

theorem chowGroups_le {n e δ : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {g : MvPolynomial (Fin (e + 1) × Fin n) ℂ} (hW : IsProjPrime W) (hg : IsChowForm W (e + 1) g)
    (hδ : IsMultiHomog δ g) : e + 1 ≤ n := by
  by_contra hn
  have hfib := ConeFibreDegree.full n e δ (HermNorm.std n) W g hW hg hδ
  have hpos := ChowDegreePos.proof n (e + 1) δ W g (Nat.succ_pos e) hW hg hδ
  have : (volume : Measure (Fin (e + 1) → Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have : (ae (volume : Measure (Fin (e + 1) → Fin n → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
  have : (ae (volume : Measure (EuclideanSpace ℂ (Fin (e + 1))))).NeBot :=
    ae_neBot.2 (NeZero.ne _)
  obtain ⟨π, hπ⟩ := hfib.exists
  obtain ⟨w, hw1, hw2⟩ := (hπ.and (ae_fibreCount_eq_zero (by omega) (HermNorm.std n) W π)).exists
  rw [hw1] at hw2
  have h0 : δ = 0 := by exact_mod_cast hw2
  omega

theorem isSigmaCompact_cone_inter {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    {A : Set (EuclideanSpace ℂ (Fin n))} (hA : IsOpen A) : IsSigmaCompact (coneSet h J ∩ A) := by
  have hcl : IsClosed (coneSet h J) := isClosed_coneSet h J
  obtain ⟨F, hF, -, hU, -⟩ := hA.exists_iUnion_isClosed
  rw [← hU, Set.inter_iUnion]
  exact isSigmaCompact_iUnion _ fun i =>
    IsSigmaCompact.of_isClosed_subset isSigmaCompact_univ (hcl.inter (hF i)) (Set.subset_univ _)

theorem isScaleStable_coneSet {n : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hJ : IsProjPrime J) : IsScaleStable (coneSet h J) := by
  intro y hy t _ q hq
  rw [HermNorm.pointOf_smul']
  exact PointLine.smul_mem_zeroSet hJ.isHomog hy t q hq

theorem IsScaleStable.inter {n : ℕ} {S T : Set (EuclideanSpace ℂ (Fin n))} (hS : IsScaleStable S)
    (hT : IsScaleStable T) : IsScaleStable (S ∩ T) :=
  fun y hy t ht => ⟨hS y hy.1 t ht, hT y hy.2 t ht⟩

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianMatrixMeasurePosFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianMatrixMeasurePosFinite
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix

open scoped ENNReal

noncomputable section

def entryGauss (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-‖z‖ ^ 2))

theorem measurable_entryGauss : Measurable entryGauss := by
  unfold entryGauss
  exact ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.comp ((continuous_norm.pow 2).neg)).measurable

theorem lintegral_entryGauss_lt_top : ∫⁻ z, entryGauss z < ⊤ := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp ((continuous_pow 2).neg)).measurable
  have h1 : ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x ^ 2)) < ⊤ := by
    simpa using (integrable_exp_neg_mul_sq one_pos).lintegral_lt_top
  have he : ∀ z : ℂ, entryGauss z =
      (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-p.1 ^ 2)) * ENNReal.ofReal (Real.exp (-p.2 ^ 2)))
        (Complex.measurableEquivRealProd z) := by
    intro z
    show ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) =
      ENNReal.ofReal (Real.exp (-z.re ^ 2)) * ENNReal.ofReal (Real.exp (-z.im ^ 2))
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    congr 2
    ring
  calc ∫⁻ z, entryGauss z
      = ∫⁻ z, (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-p.1 ^ 2)) * ENNReal.ofReal (Real.exp (-p.2 ^ 2)))
          (Complex.measurableEquivRealProd z) := lintegral_congr he
    _ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.exp (-p.1 ^ 2)) * ENNReal.ofReal (Real.exp (-p.2 ^ 2)) :=
        Complex.volume_preserving_equiv_real_prod.lintegral_comp
          ((hm.comp measurable_fst).mul (hm.comp measurable_snd))
    _ = (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x ^ 2))) * ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x ^ 2)) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_mul hm.aemeasurable hm.aemeasurable
    _ < ⊤ := ENNReal.mul_lt_top h1 h1

theorem lintegral_entryGauss_pos : 0 < ∫⁻ z, entryGauss z := by
  rw [pos_iff_ne_zero, Ne, lintegral_eq_zero_iff measurable_entryGauss]
  intro h
  obtain ⟨z, hz⟩ := h.exists
  have : entryGauss z ≠ 0 := by
    simp [entryGauss, Real.exp_pos]
  exact this hz

theorem gaussM_univ_eq (m n : ℕ) :
    gaussM m n Set.univ = ∏ _i : Fin m, ∏ _j : Fin n, ∫⁻ z, entryGauss z := by
  have hx : ∀ x : Fin m → Fin n → ℂ, matGauss x = ∏ i, ∏ j, entryGauss (x i j) := by
    intro x
    simp only [matGauss, entryGauss, ← Finset.sum_neg_distrib, Real.exp_sum]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]
  rw [gaussM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp_rw [hx]
  have hmeas : ∀ _i : Fin m, Measurable (fun y : Fin n → ℂ => ∏ j, entryGauss (y j)) := fun _ =>
    Finset.measurable_prod _ fun j _ => measurable_entryGauss.comp (measurable_pi_apply j)
  have hin : ∫⁻ y : Fin n → ℂ, ∏ j, entryGauss (y j) = ∏ _j : Fin n, ∫⁻ z, entryGauss z := by
    rw [volume_pi]
    exact LeadBlockGaussTail.lintegral_pi_prod (volume : Measure ℂ) n (fun _ => entryGauss)
      fun _ => measurable_entryGauss
  have hout := LeadBlockGaussTail.lintegral_pi_prod (volume : Measure (Fin n → ℂ)) m
    (fun _ y => ∏ j, entryGauss (y j)) hmeas
  rw [volume_pi]
  rw [hout]
  exact Finset.prod_congr rfl fun _ _ => hin

theorem gaussM_univ_pos_lt_top : ∀ m n : ℕ, 0 < gaussM m n Set.univ ∧ gaussM m n Set.univ < ⊤ := by
  intro m n
  rw [gaussM_univ_eq]
  constructor
  · exact CanonicallyOrderedAdd.prod_pos.2 fun i _ =>
      CanonicallyOrderedAdd.prod_pos.2 fun j _ => lintegral_entryGauss_pos
  · exact ENNReal.prod_lt_top fun i _ => ENNReal.prod_lt_top fun j _ => lintegral_entryGauss_lt_top

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianMatrixMeasurePosFiniteStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_matrix_measure_pos_finite : ∀ m n : ℕ, 0 < gaussM m n Set.univ ∧ gaussM m n Set.univ < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.gaussM_univ_pos_lt_top | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.gaussM_univ_pos_lt_top | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.gaussM_univ_pos_lt_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MeasurableFibreCountOver
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MeasurableFibreCountOver
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open TopologicalSpace

variable {m n : ℕ}

theorem isClosed_linProj_meets_compact {K : Set (EuclideanSpace ℂ (Fin n))} (hK : IsCompact K) :
    IsClosed {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) | ∃ y ∈ K, linProj p.1 y = p.2} := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun q : ((Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m)) × K =>
      linProj q.1.1 (q.2 : EuclideanSpace ℂ (Fin n))) := by
    unfold linProj
    fun_prop
  have hC : IsClosed {q : ((Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m)) × K |
      linProj q.1.1 (q.2 : EuclideanSpace ℂ (Fin n)) = q.1.2} :=
    isClosed_eq hc (continuous_snd.comp continuous_fst)
  have h2 := isClosedMap_fst_of_compactSpace _ hC
  convert h2 using 1
  ext p
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨(p, ⟨y, hy⟩), h, rfl⟩
  · rintro ⟨⟨p', y⟩, h, rfl⟩
    exact ⟨y, y.2, h⟩

theorem isSigmaCompact_of_isOpen_euclidean {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) :
    IsSigmaCompact U := by
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance

theorem measurableSet_linProj_meets {S U : Set (EuclideanSpace ℂ (Fin n))} (hS : IsSigmaCompact S)
    (hU : IsOpen U) :
    MeasurableSet {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
      ∃ y ∈ S ∩ U, linProj p.1 y = p.2} := by
  obtain ⟨K, hK, hKS⟩ := hS
  obtain ⟨L, hL, hLU⟩ := isSigmaCompact_of_isOpen_euclidean hU
  have hEq : {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) | ∃ y ∈ S ∩ U, linProj p.1 y = p.2} =
      ⋃ k, ⋃ l, {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
        ∃ y ∈ K k ∩ L l, linProj p.1 y = p.2} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨y, ⟨hyS, hyU⟩, h⟩
      rw [← hKS, Set.mem_iUnion] at hyS
      rw [← hLU, Set.mem_iUnion] at hyU
      obtain ⟨k, hk⟩ := hyS
      obtain ⟨l, hl⟩ := hyU
      exact ⟨k, l, y, ⟨hk, hl⟩, h⟩
    · rintro ⟨k, l, y, ⟨hk, hl⟩, h⟩
      refine ⟨y, ⟨?_, ?_⟩, h⟩
      · rw [← hKS]; exact Set.mem_iUnion.mpr ⟨k, hk⟩
      · rw [← hLU]; exact Set.mem_iUnion.mpr ⟨l, hl⟩
  rw [hEq]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun l =>
    (isClosed_linProj_meets_compact ((hK k).inter (hL l))).measurableSet

theorem natCast_le_encard_ptsOver_iff (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin m → Fin n → ℂ)
    (w : EuclideanSpace ℂ (Fin m)) (N : ℕ) :
    (N : ℕ∞) ≤ (ptsOver S π w).encard ↔
      ∃ f : Fin N → countableBasis (EuclideanSpace ℂ (Fin n)),
        (∀ i j, i ≠ j → Disjoint (f i : Set (EuclideanSpace ℂ (Fin n))) (f j)) ∧
        ∀ i, ∃ y ∈ S ∩ (f i : Set (EuclideanSpace ℂ (Fin n))), linProj π y = w := by
  constructor
  · intro hN
    obtain ⟨t, htS, htN⟩ := Set.exists_subset_encard_eq hN
    have htf : t.Finite := Set.finite_of_encard_eq_coe htN
    have hcard : htf.toFinset.card = N := by
      have := htf.encard_eq_coe_toFinset_card
      rw [htN] at this
      exact_mod_cast this.symm
    let e : Fin N ≃ {x // x ∈ htf.toFinset} := (htf.toFinset.equivFinOfCardEq hcard).symm
    let g : Fin N → EuclideanSpace ℂ (Fin n) := fun i => (e i : EuclideanSpace ℂ (Fin n))
    have hg_mem : ∀ i, g i ∈ t := fun i => htf.mem_toFinset.mp (e i).2
    have hg_inj : Function.Injective g := by
      intro i j hij
      exact e.injective (Subtype.ext hij)
    obtain ⟨V, hV, hVd⟩ := (Set.finite_range g).t2_separation
    have hB : ∀ i, ∃ v ∈ countableBasis (EuclideanSpace ℂ (Fin n)), g i ∈ v ∧ v ⊆ V (g i) := fun i =>
      (isBasis_countableBasis (EuclideanSpace ℂ (Fin n))).exists_subset_of_mem_open (hV (g i)).1 (hV (g i)).2
    choose v hvB hgv hvV using hB
    refine ⟨fun i => ⟨v i, hvB i⟩, ?_, ?_⟩
    · intro i j hij
      have hne : g i ≠ g j := fun h => hij (hg_inj h)
      exact (hVd (Set.mem_range_self i) (Set.mem_range_self j) hne).mono (hvV i) (hvV j)
    · intro i
      have := htS (hg_mem i)
      exact ⟨g i, ⟨this.1, hgv i⟩, this.2⟩
  · rintro ⟨f, hfd, hf⟩
    choose y hy hyw using hf
    have hinj : Function.Injective y := by
      intro i j hij
      by_contra hne
      have hd := hfd i j hne
      exact Set.disjoint_left.mp hd (hy i).2 (hij ▸ (hy j).2)
    have hsub : Set.range y ⊆ ptsOver S π w := by
      rintro _ ⟨i, rfl⟩
      exact ⟨(hy i).1, hyw i⟩
    calc (N : ℕ∞) = (Set.range y).encard := by
          rw [← Set.image_univ, hinj.encard_image, Set.encard_univ]; simp
      _ ≤ (ptsOver S π w).encard := Set.encard_le_encard hsub

theorem measurableSet_natCast_le_encard_ptsOver {S : Set (EuclideanSpace ℂ (Fin n))}
    (hS : IsSigmaCompact S) (N : ℕ) :
    MeasurableSet {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
      (N : ℕ∞) ≤ (ptsOver S p.1 p.2).encard} := by
  haveI : Countable (countableBasis (EuclideanSpace ℂ (Fin n))) :=
    (countable_countableBasis (EuclideanSpace ℂ (Fin n))).to_subtype
  have hEq : {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
      (N : ℕ∞) ≤ (ptsOver S p.1 p.2).encard} =
      ⋃ f : Fin N → countableBasis (EuclideanSpace ℂ (Fin n)),
        ({_p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
          ∀ i j, i ≠ j → Disjoint (f i : Set (EuclideanSpace ℂ (Fin n))) (f j)} ∩
        ⋂ i, {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
          ∃ y ∈ S ∩ (f i : Set (EuclideanSpace ℂ (Fin n))), linProj p.1 y = p.2}) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
    exact natCast_le_encard_ptsOver_iff S p.1 p.2 N
  rw [hEq]
  exact MeasurableSet.iUnion fun f => (MeasurableSet.const _).inter
    (MeasurableSet.iInter fun i => measurableSet_linProj_meets hS (isOpen_of_mem_countableBasis (f i).2))

theorem measurable_cntOver : ∀ (n m : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsSigmaCompact S →
    Measurable (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) => cntOver S p.1 p.2) := by
  intro n m S hS
  have h : (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) => cntOver S p.1 p.2) =
      fun p => ⨆ N : ℕ, {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
        (N : ℕ∞) ≤ (ptsOver S p.1 p.2).encard}.indicator (fun _ => (N : ℝ≥0∞)) p := by
    funext p
    simp only [cntOver, Set.indicator_apply, Set.mem_setOf_eq]
    generalize (ptsOver S p.1 p.2).encard = e
    induction e using ENat.recTopCoe with
    | top => simp [ENNReal.iSup_natCast]
    | coe k =>
      apply le_antisymm
      · exact le_iSup_of_le k (by simp)
      · refine iSup_le fun N => ?_
        split_ifs with hN
        · have : N ≤ k := by exact_mod_cast hN
          simpa using this
        · exact zero_le
  rw [h]
  exact Measurable.iSup fun N => measurable_const.indicator (measurableSet_natCast_le_encard_ptsOver hS N)

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MeasurableFibreCountOverStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_fibre_count_over : ∀ (n m : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsSigmaCompact S →
  Measurable (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) => cntOver S p.1 p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.measurable_cntOver | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.measurable_cntOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.measurable_cntOver <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelRootIndependent
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelRootIndependent
namespace GlobalTheory.CompanionTheory.Ar.RootIndep

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelRootIndependence.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelRootIndependence.proof GlobalTheory.T.flag_model_value_independent

end GlobalTheory.CompanionTheory.Ar.RootIndep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelRootIndependentStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_root_independent : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelRootIndependence.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootIndep.main | exact GlobalTheory.CompanionTheory.Ar.RootIndep.main | (intros; apply GlobalTheory.CompanionTheory.Ar.RootIndep.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RandomSetSumExpectation
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RandomSetSumExpectation
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton.LayerCake

noncomputable def lay (x : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' l : ℕ, if ((l : ℝ≥0∞) + 1) < x then (1 : ℝ≥0∞) else 0

theorem lay_le (x : ℝ≥0∞) : lay x ≤ x := by
  have key : ∀ N : ℕ,
      ∑ l ∈ Finset.range N, (if ((l : ℝ≥0∞) + 1) < x then (1 : ℝ≥0∞) else 0) ≤ x ∧
      ∑ l ∈ Finset.range N, (if ((l : ℝ≥0∞) + 1) < x then (1 : ℝ≥0∞) else 0) ≤ N := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases h : ((n : ℝ≥0∞) + 1) < x
      · simp only [h, if_true]
        have h1 := add_le_add_left ih.2 (1 : ℝ≥0∞)
        exact ⟨h1.trans h.le, by push_cast; exact h1⟩
      · simp only [h, if_false, add_zero]
        exact ⟨ih.1, ih.2.trans (by exact_mod_cast Nat.le_succ n)⟩
  rw [lay, ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun N => (key N).1

theorem nat_le_lay {x : ℝ≥0∞} {N : ℕ} (h : (N : ℝ≥0∞) < x) : (N : ℝ≥0∞) ≤ lay x := by
  have h1 : ∑ l ∈ Finset.range N, (if ((l : ℝ≥0∞) + 1) < x then (1 : ℝ≥0∞) else 0) = N := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
    · simp
    · intro l hl
      have hl' : l + 1 ≤ N := Finset.mem_range.1 hl
      have : ((l : ℝ≥0∞) + 1) ≤ N := by exact_mod_cast hl'
      simp [this.trans_lt h]
  rw [← h1]
  exact ENNReal.sum_le_tsum _

theorem le_lay_add_one (x : ℝ≥0∞) : x ≤ lay x + 1 := by
  by_cases top : x = ∞
  · subst top
    have : lay ∞ = ∞ := by
      by_contra hne
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hne
      exact absurd (nat_le_lay (N := n) (ENNReal.natCast_lt_top n)) (not_le.2 hn)
    simp [this]
  · lift x to NNReal using top
    have hx : x ≤ (⌈x⌉₊ : NNReal) := Nat.le_ceil x
    have hx' : (x : ℝ≥0∞) ≤ (⌈x⌉₊ : ℝ≥0∞) := by exact_mod_cast hx
    rcases hm : ⌈x⌉₊ with _ | n
    · rw [hm] at hx'
      exact hx'.trans (by simp)
    · have hn : (n : NNReal) < x := Nat.lt_ceil.1 (by omega)
      have hn' : (n : ℝ≥0∞) < x := by exact_mod_cast hn
      rw [hm] at hx'
      refine hx'.trans ?_
      push_cast
      exact add_le_add_left (nat_le_lay hn') 1

theorem two_lt_two {a b : ℝ≥0∞} (h : a < b) : 2 * a < 2 * b :=
  (ENNReal.mul_lt_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).2 h

theorem two_mul_lay_le (x : ℝ≥0∞) : 2 * lay x ≤ lay (2 * x) := by
  have e : lay (2 * x) =
      (∑' l : ℕ, if (((2 * l : ℕ) : ℝ≥0∞) + 1) < 2 * x then (1 : ℝ≥0∞) else 0) +
      ∑' l : ℕ, if (((2 * l + 1 : ℕ) : ℝ≥0∞) + 1) < 2 * x then (1 : ℝ≥0∞) else 0 := by
    rw [lay]
    exact (tsum_even_add_odd ENNReal.summable ENNReal.summable).symm
  rw [two_mul, e, lay]
  refine add_le_add (ENNReal.tsum_le_tsum fun l => ?_) (ENNReal.tsum_le_tsum fun l => ?_)
  · by_cases h : ((l : ℝ≥0∞) + 1) < x
    · have h2 := two_lt_two h
      have h3 : (((2 * l : ℕ) : ℝ≥0∞) + 1) < 2 * x := by
        refine lt_of_le_of_lt ?_ h2
        push_cast
        rw [mul_add]
        gcongr
        norm_num
      rw [if_pos h, if_pos h3]
    · simp [h]
  · by_cases h : ((l : ℝ≥0∞) + 1) < x
    · have h2 := two_lt_two h
      have h3 : (((2 * l + 1 : ℕ) : ℝ≥0∞) + 1) < 2 * x := by
        refine lt_of_le_of_lt (le_of_eq ?_) h2
        push_cast
        ring
      rw [if_pos h, if_pos h3]
    · simp [h]

noncomputable def dy (k : ℕ) (x : ℝ≥0∞) : ℝ≥0∞ := (2 ^ k : ℝ≥0∞)⁻¹ * lay (2 ^ k * x)

theorem two_pow_ne_zero' (k : ℕ) : (2 ^ k : ℝ≥0∞) ≠ 0 := by simp
theorem two_pow_ne_top' (k : ℕ) : (2 ^ k : ℝ≥0∞) ≠ ∞ := by simp

theorem dy_le_succ (k : ℕ) (x : ℝ≥0∞) : dy k x ≤ dy (k + 1) x := by
  have e : (2 ^ k : ℝ≥0∞)⁻¹ = (2 ^ (k + 1) : ℝ≥0∞)⁻¹ * 2 := by
    rw [pow_succ, ENNReal.mul_inv (Or.inl (two_pow_ne_zero' k)) (Or.inl (two_pow_ne_top' k)),
      mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
  have e2 : (2 ^ (k + 1) : ℝ≥0∞) * x = 2 * (2 ^ k * x) := by rw [pow_succ]; ring
  rw [dy, dy, e, e2, mul_assoc]
  gcongr
  exact two_mul_lay_le _

theorem dy_mono (x : ℝ≥0∞) : Monotone fun k => dy k x :=
  monotone_nat_of_le_succ fun k => dy_le_succ k x

theorem inv_mul_cancel_two_pow (k : ℕ) (x : ℝ≥0∞) : (2 ^ k : ℝ≥0∞)⁻¹ * (2 ^ k * x) = x := by
  rw [← mul_assoc, ENNReal.inv_mul_cancel (two_pow_ne_zero' k) (two_pow_ne_top' k), one_mul]

theorem iSup_dy (x : ℝ≥0∞) : ⨆ k, dy k x = x := by
  refine le_antisymm (iSup_le fun k => ?_) ?_
  · calc dy k x ≤ (2 ^ k : ℝ≥0∞)⁻¹ * (2 ^ k * x) := by
          rw [dy]; gcongr; exact lay_le _
      _ = x := inv_mul_cancel_two_pow k x
  · have hb : ∀ k : ℕ, x ≤ (⨆ j, dy j x) + (2 : ℝ≥0∞)⁻¹ ^ k := by
      intro k
      calc x = (2 ^ k : ℝ≥0∞)⁻¹ * (2 ^ k * x) := (inv_mul_cancel_two_pow k x).symm
        _ ≤ (2 ^ k : ℝ≥0∞)⁻¹ * (lay (2 ^ k * x) + 1) := by
            gcongr; exact le_lay_add_one _
        _ = dy k x + (2 : ℝ≥0∞)⁻¹ ^ k := by rw [mul_add, mul_one, ENNReal.inv_pow, dy, ENNReal.inv_pow]
        _ ≤ _ := by gcongr; exact le_iSup (fun j => dy j x) k
    have ht : Filter.Tendsto (fun k : ℕ => (⨆ j, dy j x) + (2 : ℝ≥0∞)⁻¹ ^ k) Filter.atTop
        (nhds ((⨆ j, dy j x) + 0)) :=
      tendsto_const_nhds.add (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (ENNReal.inv_lt_one.2 (by norm_num)))
    rw [add_zero] at ht
    exact ge_of_tendsto' ht hb

theorem lt_pow_mul_iff (k : ℕ) (b x : ℝ≥0∞) :
    b < 2 ^ k * x ↔ (2 ^ k : ℝ≥0∞)⁻¹ * b < x := by
  constructor
  · intro h
    have := (ENNReal.mul_lt_mul_iff_right (ENNReal.inv_ne_zero.2 (two_pow_ne_top' k))
      (ENNReal.inv_ne_top.2 (two_pow_ne_zero' k))).2 h
    rwa [inv_mul_cancel_two_pow] at this
  · intro h
    have := (ENNReal.mul_lt_mul_iff_right (two_pow_ne_zero' k) (two_pow_ne_top' k)).2 h
    rwa [← mul_assoc, ENNReal.mul_inv_cancel (two_pow_ne_zero' k) (two_pow_ne_top' k),
      one_mul] at this

theorem dy_eq_tsum (k : ℕ) (x : ℝ≥0∞) :
    dy k x = ∑' l : ℕ, (2 ^ k : ℝ≥0∞)⁻¹ *
      (if (2 ^ k : ℝ≥0∞)⁻¹ * ((l : ℝ≥0∞) + 1) < x then (1 : ℝ≥0∞) else 0) := by
  rw [dy, lay, ENNReal.tsum_mul_left]
  simp only [lt_pow_mul_iff]

theorem tsum_ite_lt {Y : Type} (S : Set Y) (φ : Y → ℝ≥0∞) (s : ℝ≥0∞) :
    ∑' y : S, (if s < φ y then (1 : ℝ≥0∞) else 0) =
      (((S ∩ {y | s < φ y}).encard : ℕ∞) : ℝ≥0∞) := by
  rw [← ENNReal.tsum_set_one, tsum_subtype S (fun y => if s < φ y then (1 : ℝ≥0∞) else 0),
    tsum_subtype (S ∩ {y | s < φ y}) (fun _ => (1 : ℝ≥0∞))]
  refine tsum_congr fun y => ?_
  by_cases h1 : y ∈ S <;> by_cases h2 : s < φ y <;> simp [Set.indicator, h1, h2]

theorem tsum_iSup_of_mono {ι : Type} (f : ℕ → ι → ℝ≥0∞) (hf : ∀ i, Monotone fun k => f k i) :
    ∑' i, ⨆ k, f k i = ⨆ k, ∑' i, f k i := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  rw [iSup_comm]
  refine iSup_congr fun s => ?_
  exact ENNReal.finsetSum_iSup_of_monotone hf

theorem measurable_lintegral_tsum_of_level_counts
    {Ω Y : Type} [MeasurableSpace Ω] [MeasurableSpace Y] (P : Measure Ω) (ν : Measure Y)
    (L : Ω → Set Y) (φ : Y → ℝ≥0∞) (c : ℝ≥0∞) (hφ : Measurable φ)
    (hN : ∀ s : ℝ≥0∞, Measurable fun ω => (((L ω ∩ {y | s < φ y}).encard : ℕ∞) : ℝ≥0∞))
    (hI : ∀ s : ℝ≥0∞, ∫⁻ ω, (((L ω ∩ {y | s < φ y}).encard : ℕ∞) : ℝ≥0∞) ∂P = c * ν {y | s < φ y}) :
    Measurable (fun ω => ∑' y : L ω, φ y) ∧ ∫⁻ ω, ∑' y : L ω, φ y ∂P = c * ∫⁻ y, φ y ∂ν := by

  have hG : ∀ k ω, ∑' y : L ω, dy k (φ y) = ∑' l : ℕ, (2 ^ k : ℝ≥0∞)⁻¹ *
      (((L ω ∩ {y | (2 ^ k : ℝ≥0∞)⁻¹ * ((l : ℝ≥0∞) + 1) < φ y}).encard : ℕ∞) : ℝ≥0∞) := by
    intro k ω
    simp_rw [dy_eq_tsum]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun l => ?_
    rw [ENNReal.tsum_mul_left, tsum_ite_lt]
  have hGm : ∀ k, Measurable fun ω => ∑' y : L ω, dy k (φ y) := by
    intro k
    simp_rw [hG]
    exact Measurable.tsum fun l => (hN _).const_mul _
  have hGi : ∀ k, ∫⁻ ω, ∑' y : L ω, dy k (φ y) ∂P = c * ∫⁻ y, dy k (φ y) ∂ν := by
    intro k
    have hlev : ∀ s : ℝ≥0∞, Measurable fun y => if s < φ y then (1 : ℝ≥0∞) else 0 := fun s =>
      Measurable.ite (measurableSet_lt measurable_const hφ) measurable_const measurable_const
    have hone : ∀ s : ℝ≥0∞, ∫⁻ y, (if s < φ y then (1 : ℝ≥0∞) else 0) ∂ν = ν {y | s < φ y} := by
      intro s
      rw [← lintegral_indicator_one (measurableSet_lt measurable_const hφ)]
      refine lintegral_congr fun y => ?_
      by_cases h : s < φ y <;> simp [Set.indicator, h]
    simp_rw [hG, dy_eq_tsum]
    rw [lintegral_tsum fun l => ((hN _).const_mul _).aemeasurable,
      lintegral_tsum fun l => ((hlev _).const_mul _).aemeasurable, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun l => ?_
    rw [lintegral_const_mul _ (hN _), hI, lintegral_const_mul _ (hlev _), hone, mul_left_comm]
  have hmono : ∀ ω (y : L ω), Monotone fun k => dy k (φ y) := fun _ y => dy_mono _
  have hS : (fun ω => ∑' y : L ω, φ y) = fun ω => ⨆ k, ∑' y : L ω, dy k (φ y) := by
    funext ω
    rw [← tsum_iSup_of_mono (fun k (y : L ω) => dy k (φ y)) (hmono ω)]
    exact tsum_congr fun y => (iSup_dy _).symm
  have hGmono : Monotone fun k ω => ∑' y : L ω, dy k (φ y) := by
    intro j k hjk ω
    exact ENNReal.tsum_le_tsum fun y => dy_mono _ hjk
  have hdm : ∀ k, Measurable fun y => dy k (φ y) := by
    intro k
    simp_rw [dy_eq_tsum]
    exact Measurable.tsum fun l => (Measurable.ite
      (measurableSet_lt measurable_const hφ) measurable_const measurable_const).const_mul _
  refine ⟨?_, ?_⟩
  · rw [hS]
    exact Measurable.iSup hGm
  · rw [hS, lintegral_iSup hGm hGmono]
    simp_rw [hGi]
    rw [← ENNReal.mul_iSup, ← lintegral_iSup hdm (fun j k hjk y => dy_mono _ hjk)]
    simp_rw [iSup_dy]

end GlobalTheory.CompanionTheory.Ar.Short.Crofton.LayerCake
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RandomSetSumExpectationStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.random_set_sum_expectation : ∀ {Ω Y : Type} [MeasurableSpace Ω] [MeasurableSpace Y] (P : Measure Ω) (ν : Measure Y)
  (L : Ω → Set Y) (φ : Y → ℝ≥0∞) (c : ℝ≥0∞), Measurable φ →
  (∀ s : ℝ≥0∞, Measurable fun ω => (((L ω ∩ {y | s < φ y}).encard : ℕ∞) : ℝ≥0∞)) →
  (∀ s : ℝ≥0∞, ∫⁻ ω, (((L ω ∩ {y | s < φ y}).encard : ℕ∞) : ℝ≥0∞) ∂P = c * ν {y | s < φ y}) →
    Measurable (fun ω => ∑' y : L ω, φ y) ∧ ∫⁻ ω, ∑' y : L ω, φ y ∂P = c * ∫⁻ y, φ y ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.LayerCake.measurable_lintegral_tsum_of_level_counts | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.LayerCake.measurable_lintegral_tsum_of_level_counts | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.LayerCake.measurable_lintegral_tsum_of_level_counts <;> assumption)
end
end
