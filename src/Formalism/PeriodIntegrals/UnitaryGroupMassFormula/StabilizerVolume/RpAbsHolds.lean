module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdSt

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.KapIntegral
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ESSymmApply
noncomputable section

namespace PI.VolStabS.RPA

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable (m : ∀ i, Measure (W i)) (L : ∀ i, Set (W i))

def am (i : ι) : ℝ≥0 := (m i (L i)).toNNReal

def tl (S : Finset ι) : ℝ≥0 := ∏' i : {i // i ∉ S}, am m L i.1

def TailH : Prop :=
  ∀ S : Finset ι, ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ HasProd (fun i : {i // i ∉ S} => m i.1 (L i.1)) c

variable {m L}

lemma hasProd_tl (hT : TailH m L) (S : Finset ι) :
    HasProd (fun i : {i // i ∉ S} => am m L i.1) (tl m L S) := by
  obtain ⟨c, hc, hP⟩ := hT S
  have h2 : HasProd (fun i : {i // i ∉ S} => am m L i.1) c.toNNReal := by
    unfold HasProd at hP ⊢
    have h3 := (ENNReal.tendsto_toNNReal hc).comp hP
    refine h3.congr (fun s => ?_)
    simp only [Function.comp, am, ENNReal.toNNReal_prod]
  rw [tl, h2.tprod_eq]
  exact h2

lemma hasProd_ind (hT : TailH m L) (S : Finset ι) :
    HasProd (({i | i ∉ S} : Set ι).mulIndicator (am m L)) (tl m L S) := by
  exact hasProd_subtype_iff_mulIndicator.mp (hasProd_tl hT S)

lemma tl_split [DecidableEq ι] (hT : TailH m L) {S T : Finset ι} (h : S ⊆ T) :
    tl m L S = (∏ i ∈ T \ S, am m L i) * tl m L T := by
  have hS := hasProd_ind hT S
  have hT' := hasProd_ind hT T
  have hfin : HasProd ((↑(T \ S) : Set ι).mulIndicator (am m L)) (∏ i ∈ T \ S, am m L i) := by
    have h := hasProd_prod_of_ne_finset_one (f := (↑(T \ S) : Set ι).mulIndicator (am m L)) (s := T \ S)
      (L := SummationFilter.unconditional ι)
      (fun b hb => Set.mulIndicator_of_notMem (by simpa using hb) _)
    rwa [Finset.prod_congr rfl (fun b hb => Set.mulIndicator_of_mem (by simpa using hb) (am m L))] at h
  have hmul := hfin.mul hT'
  have heq : (fun b => (↑(T \ S) : Set ι).mulIndicator (am m L) b * ({i | i ∉ T} : Set ι).mulIndicator (am m L) b) =
      ({i | i ∉ S} : Set ι).mulIndicator (am m L) := by
    funext b
    by_cases hbT : b ∈ T <;> by_cases hbS : b ∈ S
    · simp [Set.mulIndicator, hbT, hbS]
    · simp [Set.mulIndicator, hbT, hbS]
    · exact absurd (h hbS) hbT
    · simp [Set.mulIndicator, hbT, hbS]
  rw [heq] at hmul
  exact hS.unique hmul

lemma tl_zero [DecidableEq ι] (hT : TailH m L) {S : Finset ι} {i : ι} (hi : i ∉ S)
    (h0 : am m L i = 0) : tl m L S = 0 := by
  have h := tl_split hT (Finset.subset_insert i S)
  rw [Finset.insert_sdiff_of_notMem _ hi, Finset.sdiff_self, insert_empty_eq, Finset.prod_singleton, h0,
    zero_mul] at h
  exact h

variable (m L)

def Pn (i : ι) : Measure (W i) := (m i (L i))⁻¹ • (m i).restrict (L i)

lemma Pn_prob {i : ι} (h : m i (L i) ≠ 0 ∧ m i (L i) ≠ ⊤) : IsProbabilityMeasure (Pn m L i) := by
  constructor
  simp only [Pn, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h.1 h.2


open Classical in
def Qm (S : Finset ι) : Measure (∀ i : {i // i ∉ S}, W i) :=
  if h : ∀ i, i ∉ S → m i (L i) ≠ 0 ∧ m i (L i) ≠ ⊤ then
    haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) := fun i => Pn_prob m L (h i.1 i.2)
    tl m L S • Measure.infinitePi (fun i : {i // i ∉ S} => Pn m L i.1)
  else 0

instance Qm_fin (S : Finset ι) : IsFiniteMeasure (Qm m L S) := by
  unfold Qm; split_ifs with h
  · haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) :=
      fun i => Pn_prob m L (h i.1 i.2)
    infer_instance
  · infer_instance

def Rm (S : Finset ι) : Measure (∀ i : {i // i ∈ S}, W i) :=
  Measure.pi (fun i : {i // i ∈ S} => (m i.1).restrict (L i.1)ᶜ)


open Classical in
def eS (S : Finset ι) : (∀ i, W i) ≃ᵐ (∀ i : {i // i ∈ S}, W i) × (∀ i : {i // i ∉ S}, W i) :=
  MeasurableEquiv.piEquivPiSubtypeProd W (fun i => i ∈ S)

def kap [∀ i, SigmaFinite (m i)] (S : Finset ι) : Measure (∀ i, W i) :=
  ((Rm m L S).prod (Qm m L S)).map (eS S).symm


open Classical in
def mu (S : Finset ι) (i : ι) : Measure (W i) :=
  if i ∈ S then (m i).restrict (L i)ᶜ else (m i).restrict (L i)

open Classical in
lemma eS_symm_apply (S : Finset ι) (p : (∀ i : {i // i ∈ S}, W i) × (∀ i : {i // i ∉ S}, W i))
    (i : ι) : (eS S).symm p i = if h : i ∈ S then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩ := by
  rfl

variable [∀ i, SigmaFinite (m i)]

instance kap_sfin (S : Finset ι) : SFinite (kap m L S) := by unfold kap Rm; infer_instance

variable {m L}

lemma kap_eval_null {S : Finset ι} {i : ι} {A : Set (W i)} (hA : MeasurableSet A)
    (h : mu m L S i A = 0) : kap m L S {x | x i ∈ A} = 0 := by
  classical
  have hmeas : MeasurableSet {x : ∀ i, W i | x i ∈ A} := measurable_pi_apply i hA
  rw [kap, Measure.map_apply (eS S).symm.measurable hmeas]
  by_cases hi : i ∈ S
  · have hmu : (m i).restrict (L i)ᶜ A = 0 := by simpa [mu, hi] using h
    have hpre : (eS S).symm ⁻¹' {x | x i ∈ A} =
        (Function.eval (⟨i, hi⟩ : {i // i ∈ S}) ⁻¹' A) ×ˢ Set.univ := by
      ext p
      simp [eS_symm_apply, hi]
    rw [hpre, Measure.prod_prod]
    have h0 : Rm m L S (Function.eval (⟨i, hi⟩ : {i // i ∈ S}) ⁻¹' A) = 0 :=
      Measure.pi_eval_preimage_null _ hmu
    rw [h0, zero_mul]
  · have hmu : (m i).restrict (L i) A = 0 := by simpa [mu, hi] using h
    have hpre : (eS S).symm ⁻¹' {x | x i ∈ A} =
        Set.univ ×ˢ (Function.eval (⟨i, hi⟩ : {i // i ∉ S}) ⁻¹' A) := by
      ext p
      simp [eS_symm_apply, hi]
    rw [hpre, Measure.prod_prod]
    have h0 : Qm m L S (Function.eval (⟨i, hi⟩ : {i // i ∉ S}) ⁻¹' A) = 0 := by
      unfold Qm
      split_ifs with hc
      · rw [Measure.smul_apply]
        haveI hprob : ∀ j : {j // j ∉ S}, IsProbabilityMeasure (Pn m L j.1) :=
          fun j => Pn_prob m L (hc j.1 j.2)
        have e := Measure.infinitePi_map_eval (fun j : {j // j ∉ S} => Pn m L j.1) ⟨i, hi⟩
        have e2 : Measure.infinitePi (fun j : {j // j ∉ S} => Pn m L j.1)
            (Function.eval (⟨i, hi⟩ : {i // i ∉ S}) ⁻¹' A) = Pn m L i A := by
          rw [← e]
          exact (Measure.map_apply (measurable_pi_apply (⟨i, hi⟩ : {j // j ∉ S})) hA).symm
        rw [e2]
        simp [Pn, hmu]
      · rfl
    rw [h0, mul_zero]

lemma kap_ae [Countable ι] (hLm : ∀ i, MeasurableSet (L i)) (S : Finset ι) :
    ∀ᵐ x ∂kap m L S, ∀ i, (i ∈ S → x i ∉ L i) ∧ (i ∉ S → x i ∈ L i) := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  by_cases hi : i ∈ S
  · have h0 : kap m L S {x | x i ∈ L i} = 0 :=
      kap_eval_null (hLm i) (by simp [mu, hi, Measure.restrict_apply (hLm i)])
    refine measure_mono_null ?_ h0
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    by_contra hxL
    exact hx ⟨fun _ => hxL, fun h => absurd hi h⟩
  · have h0 : kap m L S {x | x i ∈ (L i)ᶜ} = 0 :=
      kap_eval_null (hLm i).compl (by simp [mu, hi, Measure.restrict_apply (hLm i).compl])
    refine measure_mono_null ?_ h0
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff] at hx ⊢
    intro hxL
    exact hx ⟨fun h => absurd h hi, fun _ => hxL⟩

end PI.VolStabS.RPA
end
end

noncomputable section

namespace PI.VolStabS.RPA

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable {m : ∀ i, Measure (W i)} {L : ∀ i, Set (W i)} [∀ i, SigmaFinite (m i)]

instance Rm_sf (S : Finset ι) : SigmaFinite (Rm m L S) := by unfold Rm; infer_instance

lemma Qm_integral [DecidableEq ι] (hfin : ∀ i, m i (L i) ≠ ⊤) (hT : TailH m L)
    {S T : Finset ι} (hST : S ⊆ T) (g : ∀ i, W i → ℂ) (hg : ∀ i, Integrable (g i) (m i)) :
    Integrable (fun z => ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z j)) (Qm m L S) ∧
    ∫ z, ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z j) ∂Qm m L S =
      (∏ i ∈ T \ S, ∫ w, g i w ∂(mu m L S i)) * (tl m L T : ℂ) := by
  classical
  by_cases h : ∀ i ∉ S, m i (L i) ≠ 0 ∧ m i (L i) ≠ ∞
  · haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) :=
      fun i => Pn_prob m L (h i.1 i.2)
    have hQ : Qm m L S = tl m L S • Measure.infinitePi (fun i : {i // i ∉ S} => Pn m L i.1) := by
      unfold Qm
      rw [dite_eq_left h]
    set J := T.subtype (fun i => i ∉ S) with hJ
    have hgP : ∀ j : J, Integrable (g j.1.1) (Pn m L j.1.1) := by
      intro j
      exact ((hg _).restrict).smul_measure (ENNReal.inv_ne_top.mpr (h _ j.1.2).1)
    have hF : Integrable (fun y : (j : J) → W j.1.1 => ∏ j : J, g j.1.1 (y j))
        (Measure.pi fun j : J => Pn m L j.1.1) := Integrable.fintype_prod_dep hgP
    have hmap : (Measure.infinitePi (fun i : {i // i ∉ S} => Pn m L i.1)).map J.restrict
        = Measure.pi fun j : J => Pn m L j.1.1 := Measure.infinitePi_map_restrict _
    have hfun : (fun z : (i : {i // i ∉ S}) → W i.1 => ∏ j ∈ J, g j.1 (z j))
        = (fun y : (j : J) → W j.1.1 => ∏ j : J, g j.1.1 (y j)) ∘ J.restrict := by
      funext z
      simp only [Function.comp_apply, Finset.restrict]
      exact (Finset.prod_coe_sort J (fun j => g j.1 (z j))).symm
    have hmeas : AEMeasurable (J.restrict : ((i : {i // i ∉ S}) → W i.1) → _)
        (Measure.infinitePi (fun i : {i // i ∉ S} => Pn m L i.1)) :=
      (Finset.measurable_restrict J).aemeasurable
    have hF' := hF
    rw [← hmap] at hF'
    have hint : Integrable (fun z : (i : {i // i ∉ S}) → W i.1 => ∏ j ∈ J, g j.1 (z j))
        (Measure.infinitePi (fun i : {i // i ∉ S} => Pn m L i.1)) := by
      rw [hfun]
      exact (integrable_map_measure hF'.aestronglyMeasurable hmeas).mp hF'
    have hI : ∫ z, ∏ j ∈ J, g j.1 (z j) ∂(Measure.infinitePi (fun i : {i // i ∉ S} => Pn m L i.1))
        = ∫ y, ∏ j : J, g j.1.1 (y j) ∂(Measure.pi fun j : J => Pn m L j.1.1) := by
      rw [hfun, ← hmap]
      exact (integral_map hmeas hF'.aestronglyMeasurable).symm
    refine ⟨by rw [hQ]; exact hint.smul_measure_nnreal, ?_⟩
    have hJprod : ∀ f : ι → ℂ, ∏ j : J, f j.1.1 = ∏ i ∈ T \ S, f i := by
      intro f
      rw [Finset.prod_coe_sort J (fun j => f j.1), Finset.sdiff_eq_filter, ← Finset.subtype_map]
      exact (Finset.prod_subtype_map_embedding (fun _ _ => rfl)).symm
    have key : ∀ i ∈ T \ S, ((am m L i : ℝ) : ℂ) * ∫ w, g i w ∂(Pn m L i)
        = ∫ w, g i w ∂(mu m L S i) := by
      intro i hi
      have hiS : i ∉ S := (Finset.mem_sdiff.mp hi).2
      obtain ⟨h0, htop⟩ := h i hiS
      have hone : ((am m L i : ℝ) : ℂ) * (((m i (L i))⁻¹).toReal : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, am, ENNReal.coe_toNNReal_eq_toReal, ← ENNReal.toReal_mul,
          ENNReal.mul_inv_cancel h0 htop, ENNReal.toReal_one, Complex.ofReal_one]
      rw [show Pn m L i = (m i (L i))⁻¹ • (m i).restrict (L i) from rfl,
        show mu m L S i = (m i).restrict (L i) by simp [mu, hiS],
        integral_smul_measure, Complex.real_smul, ← mul_assoc, hone, one_mul]
    rw [hQ, integral_smul_nnreal_measure, hI, integral_fintype_prod_eq_prod]
    rw [hJprod (fun i => ∫ w, g i w ∂(Pn m L i))]
    rw [tl_split hT hST, NNReal.smul_def, Complex.real_smul, NNReal.coe_mul, NNReal.coe_prod,
      Complex.ofReal_mul, Complex.ofReal_prod, ← Finset.prod_congr rfl key, Finset.prod_mul_distrib]
    ring
  · have hQ : Qm m L S = 0 := by
      unfold Qm
      rw [dite_eq_right h]
    rw [hQ]
    refine ⟨integrable_zero_measure, ?_⟩
    rw [integral_zero_measure]
    push_neg at h
    obtain ⟨i, hiS, hi⟩ := h
    have h0 : m i (L i) = 0 := by
      by_contra h0
      exact hfin i (hi h0)
    by_cases hiT : i ∈ T
    · rw [Finset.prod_eq_zero (i := i) (Finset.mem_sdiff.mpr ⟨hiT, hiS⟩)]
      · simp
      · have hz : mu m L S i = 0 := by simp [mu, hiS, Measure.restrict_eq_zero.mpr h0]
        rw [hz, integral_zero_measure]
    · rw [tl_zero hT hiT (by simp [am, h0])]
      simp

lemma kap_integral [DecidableEq ι] (hfin : ∀ i, m i (L i) ≠ ⊤) (hT : TailH m L)
    {S T : Finset ι} (hST : S ⊆ T) (g : ∀ i, W i → ℂ) (hg : ∀ i, Integrable (g i) (m i)) :
    Integrable (fun x => ∏ i ∈ T, g i (x i)) (kap m L S) ∧
    ∫ x, ∏ i ∈ T, g i (x i) ∂kap m L S =
      (∏ i ∈ T, ∫ w, g i w ∂(mu m L S i)) * (tl m L T : ℂ) := by
  classical
  obtain ⟨hQi, hQe⟩ := Qm_integral hfin hT hST g hg
  have hRi : Integrable (fun p : (j : S) → W j.1 => ∏ j : S, g j.1 (p j)) (Rm m L S) := by
    unfold Rm
    exact Integrable.fintype_prod_dep (fun j => (hg j.1).restrict)
  have hRe : ∫ p, ∏ j : S, g j.1 (p j) ∂(Rm m L S) = ∏ i ∈ S, ∫ w, g i w ∂(mu m L S i) := by
    unfold Rm
    rw [integral_fintype_prod_eq_prod, ← Finset.prod_coe_sort S]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp [mu, j.2]
  have hfun : (fun x : (i : ι) → W i => ∏ i ∈ T, g i (x i)) ∘ (eS S).symm
      = fun z => (∏ j : S, g j.1 (z.1 j)) * ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z.2 j) := by
    funext z
    simp only [Function.comp_apply]
    rw [← Finset.prod_sdiff hST]
    refine (mul_comm _ _).trans (congrArg₂ (· * ·) ?_ ?_)
    · rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [eS_symm_apply, dite_eq_left j.2]
    · rw [Finset.sdiff_eq_filter, ← Finset.subtype_map]
      refine Finset.prod_subtype_map_embedding (fun j _ => ?_)
      rw [eS_symm_apply, dite_eq_right j.2]
  have hprod := hRi.mul_prod hQi
  refine ⟨?_, ?_⟩
  · unfold kap
    rw [integrable_map_equiv, hfun]
    exact hprod
  · unfold kap
    rw [integral_map_equiv]
    rw [show (fun z => ∏ i ∈ T, g i ((eS S).symm z i))
        = fun z => (∏ j : S, g j.1 (z.1 j)) * ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z.2 j)
        from hfun]
    rw [integral_prod_mul (f := fun p : (j : S) → W j.1 => ∏ j : S, g j.1 (p j))
      (g := fun q : (i : {i // i ∉ S}) → W i.1 => ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (q j))]
    rw [hRe, hQe, ← mul_assoc, mul_comm (∏ i ∈ S, _), Finset.prod_sdiff hST]

end PI.VolStabS.RPA
end
end

noncomputable section

namespace PI.VolStabS

open MeasureTheory Filter Finset PI.VolStabS.RPA
open scoped NNReal ENNReal

theorem rpAbs_holds : RPAbs := by
  intro ι _ W _ m _ L hL hLfin hTail
  classical
  refine ⟨Measure.sum fun S : Finset ι => kap m L S, inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.sum_apply_eq_zero]
    intro S
    refine measure_mono_null ?_ (ae_iff.1 (kap_ae hL S))
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro h
    apply hx
    refine Filter.eventually_cofinite.2 ((S.finite_toSet).subset ?_)
    intro i hi
    by_contra hiS
    exact hi ((h i).2 hiS)
  · intro i C hC hCm
    rw [Measure.sum_apply_eq_zero]
    intro S
    apply kap_eval_null hC.compl
    by_cases hi : i ∈ S <;> simp only [mu, hi, if_true, if_false] <;>
      exact Measure.restrict_le_self.absolutelyContinuous hCm
  · intro f hfi hf
    obtain ⟨T0, hT0⟩ : ∃ T0 : Finset ι, ∀ i ∉ T0, f i = (L i).indicator 1 :=
      ⟨(Filter.eventually_cofinite.1 hf).toFinset, fun i hi => by simpa using hi⟩
    have hsub : ∀ (S : Finset ι) (x : (i : ι) → W i), (∀ i, i ∉ S → x i ∈ L i) →
        Function.mulSupport (fun i => f i (x i)) ⊆ ↑(S ∪ T0) := by
      intro S x hx i hi
      by_contra hni
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hni
      apply hi
      show f i (x i) = 1
      rw [hT0 i hni.2]
      simp [hx i hni.1]
    have hA : ∀ S : Finset ι, (fun x : (i : ι) → W i => ∏ᶠ i, f i (x i)) =ᵐ[kap m L S]
        fun x => ∏ i ∈ S ∪ T0, f i (x i) := by
      intro S
      filter_upwards [kap_ae hL S] with x hx
      exact finprod_eq_prod_of_mulSupport_subset _ (hsub S x fun i hi => (hx i).2 hi)
    have hZ : ∀ S : Finset ι, ¬ S ⊆ T0 →
        (fun x : (i : ι) → W i => ∏ᶠ i, f i (x i)) =ᵐ[kap m L S] 0 := by
      intro S hS
      obtain ⟨j, hjS, hjT⟩ := Finset.not_subset.1 hS
      filter_upwards [kap_ae hL S] with x hx
      refine finprod_eq_zero (fun i => f i (x i)) j ?_
        ((S ∪ T0).finite_toSet.subset (hsub S x fun i hi => (hx i).2 hi))
      rw [hT0 j hjT]
      simp [(hx j).1 hjS]
    have hint : ∀ S : Finset ι, Integrable (fun x : (i : ι) → W i => ∏ᶠ i, f i (x i)) (kap m L S) :=
      fun S => (kap_integral hLfin hTail Finset.subset_union_left f hfi).1.congr (hA S).symm
    have hI : ∀ S : Finset ι, ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S =
        if S ⊆ T0 then (∏ i ∈ T0, ∫ w, f i w ∂mu m L S i) * ((tl m L T0 : ℝ) : ℂ) else 0 := by
      intro S
      split_ifs with h
      · rw [integral_congr_ae (hA S), Finset.union_eq_right.2 h]
        exact (kap_integral hLfin hTail h f hfi).2
      · rw [integral_congr_ae (hZ S h)]
        simp
    have hρint : Integrable (fun x : (i : ι) → W i => ∏ᶠ i, f i (x i))
        (Measure.sum fun S => kap m L S) := by
      refine integrable_sum_measure hint (summable_of_ne_finset_zero (s := T0.powerset) ?_)
      intro S hS
      rw [Finset.mem_powerset] at hS
      have h0 : (fun x : (i : ι) → W i => ‖∏ᶠ i, f i (x i)‖) =ᵐ[kap m L S] fun _ => (0 : ℝ) :=
        (hZ S hS).mono fun x hx => by simp only [Pi.zero_apply] at hx; simp [hx]
      rw [integral_congr_ae h0, integral_zero]
    have hsum : HasSum (fun S : Finset ι => ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S)
        (∑ S ∈ T0.powerset, (∏ i ∈ T0, ∫ w, f i w ∂mu m L S i) * ((tl m L T0 : ℝ) : ℂ)) := by
      have h : HasSum (fun S : Finset ι => ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S)
          (∑ S ∈ T0.powerset, ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S) :=
        hasSum_sum_of_ne_finset_zero (fun S hS => by rw [hI S, if_neg (by simpa using hS)])
      convert h using 1
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [hI S, if_pos (Finset.mem_powerset.1 hS)]
    have hval : ∫ x, ∏ᶠ i, f i (x i) ∂(Measure.sum fun S => kap m L S) =
        (∏ i ∈ T0, ∫ w, f i w ∂m i) * ((tl m L T0 : ℝ) : ℂ) := by
      rw [(hasSum_integral_measure hρint).unique hsum, ← Finset.sum_mul]
      congr 1
      rw [show (∏ i ∈ T0, ∫ w, f i w ∂m i) =
          ∏ i ∈ T0, ((∫ w in (L i)ᶜ, f i w ∂m i) + ∫ w in L i, f i w ∂m i) from
        Finset.prod_congr rfl fun i _ => by rw [add_comm, integral_add_compl (hL i) (hfi i)],
        Finset.prod_add]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [Finset.mem_powerset] at hS
      rw [← Finset.prod_sdiff hS, mul_comm]
      congr 1
      · exact Finset.prod_congr rfl fun i hi => by simp [mu, hi]
      · exact Finset.prod_congr rfl fun i hi => by simp [mu, (Finset.mem_sdiff.1 hi).2]
    refine ⟨hρint, ?_⟩
    rw [hval]
    have h1 : HasProd (fun i => if i ∈ T0 then ∫ w, f i w ∂m i else 1)
        (∏ i ∈ T0, ∫ w, f i w ∂m i) := by
      convert hasProd_prod_of_ne_finset_one (s := T0)
        (f := fun i => if i ∈ T0 then ∫ w, f i w ∂m i else 1) (fun i hi => if_neg hi) using 1
      all_goals first | infer_instance | exact Finset.prod_congr rfl fun i hi => (if_pos hi).symm
    have h2 : HasProd (fun i => (((({i | i ∉ T0} : Set ι).mulIndicator (am m L) i : ℝ≥0) : ℝ) : ℂ))
        ((tl m L T0 : ℝ) : ℂ) :=
      (hasProd_ind hTail T0).map ((Complex.ofRealHom.toMonoidHom).comp NNReal.toRealHom.toMonoidHom)
        (Complex.continuous_ofReal.comp NNReal.continuous_coe)
    convert h1.mul h2 using 1
    funext i
    by_cases hi : i ∈ T0
    · simp [hi, Set.mulIndicator_apply]
    · have hind : ∫ w, (L i).indicator (1 : W i → ℂ) w ∂m i = (((m i) (L i)).toReal : ℂ) := by
        rw [show (1 : W i → ℂ) = fun _ => (1 : ℂ) from rfl, integral_indicator_const _ (hL i)]
        simp [Measure.real]
      rw [hT0 i hi, hind]
      simp only [hi, if_false, one_mul, Set.mulIndicator_apply, Set.mem_setOf_eq, not_false_eq_true,
        if_true, am, ENNReal.coe_toNNReal_eq_toReal]

end PI.VolStabS
