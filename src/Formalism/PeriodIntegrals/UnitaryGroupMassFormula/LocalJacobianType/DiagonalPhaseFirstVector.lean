module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ContinuousTrESymm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ComponentsOfD1EqZero
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ChiZeroRight
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ContinuousPsiVOf
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def piu : Fv F v := (PI.VolStabSW.exists_unif_Fv v).choose

theorem piu_ne : piu v ≠ 0 := (PI.VolStabSW.exists_unif_Fv v).choose_spec.1

theorem piu_tendsto : Tendsto (fun k : ℕ => piu v ^ k) atTop (𝓝 0) :=
  (PI.VolStabSW.exists_unif_Fv v).choose_spec.2.1

theorem tube {X : Type} [AddCommGroup X] [Module (Fv F v) X] [TopologicalSpace X]
    [ContinuousSMul (Fv F v) X] {C : Set X} (hC : IsCompact C) {U : Set X}
    (hU : U ∈ 𝓝 (0 : X)) : ∀ᶠ k : ℕ in atTop, ∀ c ∈ C, piu v ^ k • c ∈ U := by
  have hP : ∀ c ∈ C, ∀ᶠ z : Fv F v × X in 𝓝 ((0 : Fv F v), c), z.1 • z.2 ∈ U := by
    intro c _
    have hc : Continuous fun z : Fv F v × X => z.1 • z.2 := continuous_fst.smul continuous_snd
    exact (hc.tendsto ((0 : Fv F v), c)).eventually_mem (by simpa using hU)
  have hev := hC.eventually_forall_of_forall_eventually (P := fun s c => s • c ∈ U) hP
  exact (piu_tendsto v).eventually hev

variable (ψ : AddChar (AF F) ℂ)

theorem singleV_zero : singleV F v 0 = 0 := by
  have h := PI.VolStabSW.SdUniqW.singleV_add v (0 : Fv F v) 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

theorem psiV_zero : psiV F ψ v 0 = 1 := by
  simp only [psiV, singleV_zero]
  exact AddChar.map_zero_eq_one ψ

theorem psiV_add' (r s : Fv F v) : psiV F ψ v (r + s) = psiV F ψ v r * psiV F ψ v s :=
  PI.VolStabSW.SdUniqW.psiV_add ψ v r s

theorem psiV_neg_mul (r : Fv F v) : psiV F ψ v (-r) * psiV F ψ v r = 1 := by
  rw [← psiV_add', neg_add_cancel, psiV_zero]

theorem psiV_sum {ι : Type} (s : Finset ι) (f : ι → Fv F v) :
    psiV F ψ v (∑ i ∈ s, f i) = ∏ i ∈ s, psiV F ψ v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [psiV_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, psiV_add', ih]

theorem psiV_nsmul (n : ℕ) (r : Fv F v) : psiV F ψ v (n • r) = psiV F ψ v r ^ n := by
  induction n with
  | zero => simp [psiV_zero]
  | succ n ih => rw [succ_nsmul, psiV_add', ih, pow_succ]

def OpenKer : Prop :=
  ∃ k : ℕ, ∀ c ∈ v.adicCompletionIntegers F, psiV F ψ v (piu v ^ k * c) = 1

def ballK (k : ℕ) : Set (Fv F v) := {t | (piu v ^ k)⁻¹ * t ∈ v.adicCompletionIntegers F}

theorem ballK_mem_nhds (k : ℕ) : ballK v k ∈ 𝓝 (0 : Fv F v) := by
  have ho : IsOpen (ballK v k) :=
    (Valued.isOpen_valuationSubring _).preimage (continuous_const.mul continuous_id)
  exact ho.mem_nhds (by simp [ballK, zero_mem])

theorem psiV_ballK {k : ℕ} (hk : ∀ c ∈ v.adicCompletionIntegers F, psiV F ψ v (piu v ^ k * c) = 1)
    {t : Fv F v} (ht : t ∈ ballK v k) : psiV F ψ v t = 1 := by
  have h := hk _ ht
  rwa [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero k (piu_ne v)), one_mul] at h

theorem continuous_psiV_of (h : OpenKer v ψ) : Continuous (psiV F ψ v) := by
  obtain ⟨k, hk⟩ := h
  refine continuous_iff_continuousAt.2 fun r => ?_
  have hev : ∀ᶠ t in 𝓝 r, psiV F ψ v t = psiV F ψ v r := by
    have h1 : Tendsto (fun t => t - r) (𝓝 r) (𝓝 0) := tendsto_sub_nhds_zero_iff.2 tendsto_id
    filter_upwards [h1 (ballK_mem_nhds v k)] with t ht
    have := psiV_add' v ψ r (t - r)
    rw [add_sub_cancel, psiV_ballK v ψ hk ht, mul_one] at this
    exact this
  exact continuousAt_const.congr (hev.mono fun t ht => ht.symm)

theorem norm_psiV_of (h : OpenKer v ψ) (r : Fv F v) : ‖psiV F ψ v r‖ = 1 := by
  have hc := continuous_psiV_of v ψ h

  have hbd : ∀ x : Fv F v, ∃ B : ℝ, ∀ n : ℕ, ‖psiV F ψ v x‖ ^ n ≤ B := by
    intro x
    obtain ⟨j, hj⟩ := ((piu_tendsto v).mul_const x).eventually
      ((Valued.isOpen_valuationSubring (Fv F v)).mem_nhds (by simp [zero_mem]) :
        ((v.adicCompletionIntegers F : Set (Fv F v))) ∈ 𝓝 (0 * x)) |>.exists
    set H : Set (Fv F v) := {t | piu v ^ j * t ∈ v.adicCompletionIntegers F}
    have hHc : IsCompact H := by
      have e : H = (fun t => (piu v ^ j)⁻¹ * t) '' (v.adicCompletionIntegers F : Set (Fv F v)) := by
        ext t
        constructor
        · intro ht
          refine ⟨piu v ^ j * t, ht, ?_⟩
          simp [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j (piu_ne v))]
        · rintro ⟨s, hs, rfl⟩
          simpa [H, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero j (piu_ne v))] using hs
      rw [e]
      exact (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image (continuous_const.mul continuous_id)
    obtain ⟨B, hB⟩ := hHc.exists_bound_of_continuousOn (hc.norm.continuousOn)
    refine ⟨B, fun n => ?_⟩
    have hn : (n • x) ∈ H := by
      show piu v ^ j * (n • x) ∈ v.adicCompletionIntegers F
      rw [mul_smul_comm]
      exact (v.adicCompletionIntegers F).toAddSubgroup.nsmul_mem hj n
    have h2 := hB _ hn
    rw [psiV_nsmul, norm_norm, norm_pow] at h2
    exact h2
  have hle : ∀ x : Fv F v, ‖psiV F ψ v x‖ ≤ 1 := by
    intro x
    obtain ⟨B, hB⟩ := hbd x
    by_contra hgt
    push Not at hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hgt
    exact absurd (hB n) (not_le.2 hn)
  have h1 := hle r
  have h2 := hle (-r)
  have h3 : ‖psiV F ψ v (-r)‖ * ‖psiV F ψ v r‖ = 1 := by rw [← norm_mul, psiV_neg_mul, norm_one]
  nlinarith [norm_nonneg (psiV F ψ v r), norm_nonneg (psiV F ψ v (-r))]

theorem openKer_of (t : Fv F v) (ht : t ≠ 0)
    (h : ∀ c ∈ v.adicCompletionIntegers F, psiV F ψ v (c * t) = 1) : OpenKer v ψ := by
  have hU : {s : Fv F v | t⁻¹ * s ∈ v.adicCompletionIntegers F} ∈ 𝓝 (0 : Fv F v) :=
    ((Valued.isOpen_valuationSubring _).preimage (continuous_const.mul continuous_id)).mem_nhds
      (by simp [zero_mem])
  obtain ⟨k, hk⟩ := (tube v (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v) hU).exists
  refine ⟨k, fun c hc => ?_⟩
  have h1 := h _ (hk c hc)
  simp only [smul_eq_mul] at h1
  have e : t⁻¹ * (piu v ^ k * c) * t = piu v ^ k * c := by field_simp
  rwa [e] at h1

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)

def chi (ι : Type) [Fintype ι] (x y : ι → Fv F v ⊗[F] E) : ℂ :=
  psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i))

open Classical in
theorem sdE_eq (ι : Type) [Fintype ι] :
    sdE (E := E) ψ v ι = if h : ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (chi (E := E) v ψ ι)
      then h.choose else 0 := rfl

theorem chi_add_left (ι : Type) [Fintype ι] (x t y : ι → Fv F v ⊗[F] E) :
    chi (E := E) v ψ ι (t + x) y = chi (E := E) v ψ ι t y * chi (E := E) v ψ ι x y := by
  simp only [chi, Pi.add_apply, add_mul, map_add (f := _), Finset.sum_add_distrib, psiV_add']

theorem chi_symm (ι : Type) [Fintype ι] (x y : ι → Fv F v ⊗[F] E) :
    chi (E := E) v ψ ι x y = chi (E := E) v ψ ι y x := by
  simp only [chi, mul_comm]

theorem chi_zero_right (ι : Type) [Fintype ι] (x : ι → Fv F v ⊗[F] E) :
    chi (E := E) v ψ ι x 0 = 1 := by
  simp [chi, psiV_zero]

theorem chi_smul (ι : Type) [Fintype ι] (c : Fv F v) (x y : ι → Fv F v ⊗[F] E) :
    chi (E := E) v ψ ι (c • x) y = chi (E := E) v ψ ι x (c • y) := by
  simp only [chi, Pi.smul_apply, smul_mul_assoc, mul_smul_comm]

def D1 : Set (Fv F v ⊗[F] E) :=
  {y | ∀ x ∈ OEv (E := E) v, psiV F ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y)) = 1}

def Dbox (ι : Type) : Set (ι → Fv F v ⊗[F] E) := Set.univ.pi fun _ => D1 (E := E) v ψ

theorem ann_obox (ι : Type) [Fintype ι] :
    ann (chi (E := E) v ψ ι) (Obox (E := E) v ι) = Dbox (E := E) v ψ ι := by
  classical
  ext y
  constructor
  · intro hy i _ x hx
    have h := hy (Pi.single i x) (fun j _ => by
      by_cases hj : j = i
      · subst hj; simpa using hx
      · simpa [Pi.single_apply, hj] using oev_zero v)
    have hs : ∑ j, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((Pi.single i x : ι → Fv F v ⊗[F] E) j * y j) =
        Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y i) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_apply, hj]
      · simp
    simp only [chi] at h
    rwa [hs] at h
  · intro hy x hx
    simp only [chi]
    rw [psiV_sum]
    exact Finset.prod_eq_one fun i _ => hy i trivial (x i) (hx i trivial)

def ObS (ι : Type) : AddSubgroup (ι → Fv F v ⊗[F] E) := AddSubgroup.pi Set.univ fun _ => Osub (E := E) v

theorem coe_ObS (ι : Type) : (ObS (E := E) v ι : Set (ι → Fv F v ⊗[F] E)) = Obox (E := E) v ι := by
  simp [ObS, AddSubgroup.coe_pi, Obox, Osub]

theorem isCompact_obox (ι : Type) [Fintype ι] : IsCompact (Obox (E := E) v ι) :=
  isCompact_univ_pi fun _ => isCompact_oev v

theorem isOpen_obox (ι : Type) [Fintype ι] : IsOpen (Obox (E := E) v ι) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_oev v

theorem zero_mem_obox (ι : Type) : (0 : ι → Fv F v ⊗[F] E) ∈ Obox (E := E) v ι :=
  fun _ _ => oev_zero v

variable [SecondCountableTopology (Fv F v ⊗[F] E)]

theorem sd_test (ι : Type) [Fintype ι] (μ : Measure (ι → Fv F v ⊗[F] E))
    (hμ : SelfDual μ (chi (E := E) v ψ ι)) (hA : MeasurableSet (Dbox (E := E) v ψ ι))
    (hfin : μ (Dbox (E := E) v ψ ι) < ⊤) :
    μ.real (Obox (E := E) v ι) * μ.real (Dbox (E := E) v ψ ι) = 1 := by
  have := hμ.1
  set L := ObS (E := E) v ι
  have hLo : IsOpen (L : Set (ι → Fv F v ⊗[F] E)) := by rw [coe_ObS]; exact isOpen_obox v ι
  have hLc : IsCompact (L : Set (ι → Fv F v ⊗[F] E)) := by rw [coe_ObS]; exact isCompact_obox v ι
  have hcl : IsClopen (L : Set (ι → Fv F v ⊗[F] E)) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set Φ : (ι → Fv F v ⊗[F] E) → ℂ := (L : Set (ι → Fv F v ⊗[F] E)).indicator (fun _ => (1 : ℂ))
  have hΦc : Continuous Φ := by
    classical
    rw [show Φ = (L : Set _).piecewise (fun _ => (1 : ℂ)) (fun _ => 0) from
      (Set.piecewise_eq_indicator).symm]
    exact continuous_const.piecewise (by simp [hcl.frontier_eq]) continuous_const
  have hΦs : HasCompactSupport Φ := HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _
  have hχ : ∀ x t y, chi (E := E) v ψ ι (t + x) y = chi (E := E) v ψ ι t y * chi (E := E) v ψ ι x y :=
    chi_add_left v ψ ι
  have hT : ∀ y, ∫ x, Φ x * chi (E := E) v ψ ι x y ∂μ =
      (Dbox (E := E) v ψ ι).indicator (fun _ => ((μ.real (Obox (E := E) v ι) : ℝ) : ℂ)) y := by
    intro y
    have h := PI.VolStabSW.SdUniqW.transform_indicator μ (chi (E := E) v ψ ι) hχ L hLo y
    rw [coe_ObS, ann_obox] at h
    exact h
  have hI : Integrable (fun y => ∫ x, Φ x * chi (E := E) v ψ ι x y ∂μ) μ := by
    simp only [hT]
    rw [integrable_indicator_iff hA]
    exact integrableOn_const hfin.ne
  have h := hμ.2 Φ hΦc hΦs hI 0
  simp only [hT] at h
  simp only [chi_zero_right, mul_one, neg_zero] at h
  rw [integral_indicator_const _ hA] at h
  have h0 : Φ 0 = 1 := by simp [Φ, L.zero_mem]
  rw [h0] at h
  have h2 : ((μ.real (Dbox (E := E) v ψ ι) * μ.real (Obox (E := E) v ι) : ℝ) : ℂ) = 1 := by
    rw [← h]; simp [Complex.real_smul]
  have h3 : μ.real (Dbox (E := E) v ψ ι) * μ.real (Obox (E := E) v ι) = 1 := by exact_mod_cast h2
  linarith

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

theorem piu_inv_not_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (piu v)⁻¹ ∉ v.adicCompletionIntegers F := by
  intro h
  have hU : {x : Fv F v | x ≠ 1} ∈ 𝓝 (0 : Fv F v) := isOpen_ne.mem_nhds zero_ne_one
  obtain ⟨k, hk⟩ := (tube v (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v) hU).exists
  have hm : (piu v)⁻¹ ^ k ∈ v.adicCompletionIntegers F := pow_mem h k
  apply hk _ hm
  simp [smul_eq_mul, mul_inv_cancel₀ (pow_ne_zero k (piu_ne v))]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)

theorem finrank_pos' : 0 < Module.finrank F E := Module.finrank_pos

theorem exists_not_mem_oev : ∃ t0 : Fv F v ⊗[F] E, t0 ∉ OEv (E := E) v := by
  classical
  set i0 : Fin (Module.finrank F E) := ⟨0, finrank_pos'⟩
  set P : Set (Fv F v) := (fun y => trE (E := E) v y i0) '' OEv (E := E) v
  have hP : IsCompact P :=
    (isCompact_oev v).image ((continuous_apply i0).comp (continuous_trE v))
  have hU : (v.adicCompletionIntegers F : Set (Fv F v)) ∈ 𝓝 (0 : Fv F v) :=
    (Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _)
  obtain ⟨k, hk⟩ := (tube v hP hU).exists
  refine ⟨(trE (E := E) v).symm (Pi.single i0 (piu v ^ (k + 1))⁻¹), fun h => ?_⟩
  have hp : (piu v ^ (k + 1))⁻¹ ∈ P :=
    ⟨_, h, by simp⟩
  have h2 := hk _ hp
  have e : piu v ^ k • (piu v ^ (k + 1))⁻¹ = (piu v)⁻¹ := by
    have := piu_ne v
    rw [smul_eq_mul, pow_succ]
    field_simp
  rw [e] at h2
  exact piu_inv_not_mem v h2

variable [SecondCountableTopology (Fv F v ⊗[F] E)]

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)

theorem continuous_tr : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) :=
  PI.VolStabSW.SdUniqW.continuous_trace_tens (F := F) (E := E) (Fv F v)

theorem diagonal_phase_first_vector : (0 : Fv F v ⊗[F] E) ∈ D1 (E := E) v ψ := by
  intro x _; simp [psiV_zero]

theorem conductor_add_mem {y y' : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) (hy' : y' ∈ D1 (E := E) v ψ) :
    y + y' ∈ D1 (E := E) v ψ := by
  intro x hx
  rw [mul_add, map_add (f := _), psiV_add', hy x hx, hy' x hx, mul_one]

theorem conductor_neg_mem {y : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) : -y ∈ D1 (E := E) v ψ := by
  intro x hx
  have h := psiV_neg_mul v ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y))
  rw [hy x hx, mul_one] at h
  rwa [mul_neg, map_neg]

def D1sub : AddSubgroup (Fv F v ⊗[F] E) where
  carrier := D1 (E := E) v ψ
  add_mem' := conductor_add_mem v ψ
  zero_mem' := diagonal_phase_first_vector v ψ
  neg_mem' := conductor_neg_mem v ψ

theorem trE_mem_Aset {y : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) (j : Fin (Module.finrank F E)) :
    trE (E := E) v y j ∈ PI.OmFibreUniq.W.SdChar.Aset v (psiV F ψ v) := by
  intro c hc
  have e : c * trE (E := E) v y j =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((c • bas (E := E) v j) * y) := by
    rw [trE_apply, trC_apply, smul_mul_assoc, map_smul, smul_eq_mul]
  rw [e]
  exact hy _ (smul_bas_mem v hc j)

variable (hK : OpenKer v ψ)
include hK

theorem conductor_isClosed : IsClosed (D1 (E := E) v ψ) := by
  have e : D1 (E := E) v ψ = ⋂ x ∈ OEv (E := E) v,
      {y | psiV F ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y)) = 1} := by
    ext y; simp [D1]
  rw [e]
  exact isClosed_biInter fun x _ => isClosed_eq ((continuous_psiV_of v ψ hK).comp
    ((continuous_tr v).comp (continuous_const.mul continuous_id))) continuous_const

theorem conductor_isCompact (hnt : ∃ r, psiV F ψ v r ≠ 1) : IsCompact (D1 (E := E) v ψ) := by
  obtain ⟨y0, -, hy0⟩ := PI.OmFibreUniq.W.SdChar.Aset_bdd v (psiV F ψ v) (psiV_add' v ψ)
    (norm_psiV_of v ψ hK) hnt
  set C : Set (Fin (Module.finrank F E) → Fv F v) :=
    Set.univ.pi fun _ => (fun s => y0 * s) '' (v.adicCompletionIntegers F : Set (Fv F v))
  have hC : IsCompact C := isCompact_univ_pi fun _ =>
    (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image (continuous_const.mul continuous_id)
  refine (hC.image (continuous_trE_symm (E := E) v)).of_isClosed_subset (conductor_isClosed v ψ hK) ?_
  intro y hy
  refine ⟨trE (E := E) v y, fun j _ => ?_, by simp⟩
  obtain ⟨s, hs, e⟩ := hy0 _ (trE_mem_Aset v ψ hy j)
  exact ⟨s, hs, e.symm⟩

theorem conductor_mem_nhds : D1 (E := E) v ψ ∈ 𝓝 (0 : Fv F v ⊗[F] E) := by
  obtain ⟨m, w, hw, hgen⟩ := exists_gens (E := E) v
  have hA := PI.OmFibreUniq.W.SdChar.Aset_mem_nhds v (psiV F ψ v) (continuous_psiV_of v ψ hK)
    (psiV_add' v ψ) (norm_psiV_of v ψ hK)
  have hN : (⋂ k, {y : Fv F v ⊗[F] E | Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (w k * y) ∈
      PI.OmFibreUniq.W.SdChar.Aset v (psiV F ψ v)}) ∈ 𝓝 (0 : Fv F v ⊗[F] E) := by
    refine Filter.iInter_mem.2 fun k => ?_
    have hc : Continuous fun y : Fv F v ⊗[F] E => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (w k * y) :=
      (continuous_tr v).comp (continuous_const.mul continuous_id)
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hA)
  refine Filter.mem_of_superset hN fun y hy x hx => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hy
  obtain ⟨c, hc, rfl⟩ := hgen x hx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum, psiV_sum]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]
  exact hy k (c k) (hc k)

theorem conductor_isOpen : IsOpen (D1 (E := E) v ψ) :=
  AddSubgroup.isOpen_of_mem_nhds (D1sub (E := E) v ψ) (conductor_mem_nhds v ψ hK)

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
