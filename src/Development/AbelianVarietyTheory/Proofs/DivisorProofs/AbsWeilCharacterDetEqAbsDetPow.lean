module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntIndMemSB
open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
def intInd (n d : ℕ) : Matrix (Fin n) (Fin d) k → ℂ := Set.indicator {Y | ∀ i j, Y i j ∈ 𝒪[k]} 1

def diagAt {n : ℕ} (x : kˣ) (i0 : Fin n) : GL (Fin n) k := SplitFlip.diagGL fun i => if i = i0 then x else 1

def cosetRep {n d : ℕ} (ϖ : kˣ) (i0 : Fin n) (T : Fin d → SplitFlip.Res (k := k) 1) : Matrix (Fin n) (Fin d) k :=
  Matrix.of fun i j => if i = i0 then -((ϖ : k)⁻¹ * ((Quotient.out (T j) : 𝒪[k]) : k)) else 0

theorem intInd_mem_SB (n d : ℕ) : intInd k n d ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := SplitFlip.isCompact_intMatrix
  have ho : IsOpen {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := SplitFlip.isOpen_intMatrix
  have hW : IsClopen {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := ⟨hc.isClosed, ho⟩
  refine ⟨?_, HasCompactSupport.intro' hc hW.isClosed fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]}
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp only [Set.mem_setOf_eq] at hx
    simp [intInd, Set.indicator_apply, hy, hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hx hy
    simp [intInd, Set.indicator_apply, hy, hx]

theorem intInd_zero (n d : ℕ) : intInd k n d 0 = 1 :=
  Set.indicator_of_mem (show (0 : Matrix (Fin n) (Fin d) k) ∈ {Y | ∀ i j, Y i j ∈ 𝒪[k]} from
    fun _ _ => zero_mem _) _

theorem det_diagAt {n : ℕ} (x : kˣ) (i0 : Fin n) : Matrix.GeneralLinearGroup.det (diagAt x i0) = x := by
  rw [diagAt, SplitFlip.det_diagGL, Fintype.prod_eq_single i0 (fun i hi => if_neg hi), if_pos rfl]

theorem diagAt_val {n : ℕ} (x : kˣ) (i0 : Fin n) :
    (diagAt x i0).val = Matrix.diagonal fun i => if i = i0 then (x : k) else 1 := by
  rw [diagAt, SplitFlip.diagGL_val]
  congr 1; funext i; split_ifs <;> simp

end GlobalTheory.HeisUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLintegralSqNeTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLintegralSqNeTop
open MeasureTheory Matrix ValuativeRel

namespace GlobalTheory.SBNorm

theorem schwartzBruhat_memL2_inner_self : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (μ : @Measure (Fin n × Fin d → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k),
      ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ ∧
      ∫ y, f y * (starRingEnd ℂ) (f y) ∂μ = (((∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) ∧
      (f ≠ 0 → ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ 0) ∧
      ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
  intro k _ _ _ _ n d μ hμ f hf
  letI : MeasurableSpace (Fin n × Fin d → k) := borel _
  haveI : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hfc : Continuous f := hf.1.continuous
  have hint : ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
    intro g hg
    have hgc : Continuous g := hg.1.continuous
    exact (hfc.mul (Complex.continuous_conj.comp hgc)).integrable_of_hasCompactSupport
      (hf.2.mul_right (f' := fun y => (starRingEnd ℂ) (g y)))
  have hpt : ∀ y, ‖f y * (starRingEnd ℂ) (f y)‖ₑ = ‖f y‖ₑ ^ 2 := by
    intro y
    rw [enorm_mul, pow_two]
    congr 1
    simp [enorm_eq_nnnorm]
  have hfin : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have := (hint f hf).2
    unfold HasFiniteIntegral at this
    simp_rw [hpt] at this
    exact this.ne
  refine ⟨hfin, ?_, ?_, hint⟩
  · have h1 : ∀ y, f y * (starRingEnd ℂ) (f y) = (((‖f y‖ ^ 2 : ℝ)) : ℂ) := by
      intro y
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [h1]
    rw [integral_complex_ofReal]
    congr 1
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun y => ‖f y‖ ^ 2)
      (Filter.Eventually.of_forall fun y => by positivity)
      ((hfc.norm.pow 2).aestronglyMeasurable)]
    congr 1
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  · intro hne
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    have hmeas : Measurable fun y => ‖f y‖ₑ ^ 2 := (hfc.measurable.enorm).pow_const 2
    rw [← pos_iff_ne_zero, lintegral_pos_iff_support hmeas]
    have hsupp : Function.support (fun y => ‖f y‖ₑ ^ 2) = f ⁻¹' {0}ᶜ := by
      ext y
      simp
    rw [hsupp]
    exact (hf.1 ({0}ᶜ)).measure_pos μ ⟨x, hx⟩

end GlobalTheory.SBNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLintegralSqNeTopStatement
open MeasureTheory Matrix ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (μ : @Measure (Fin n × Fin d → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k),
      ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ ∧
      ∫ y, f y * (starRingEnd ℂ) (f y) ∂μ = (((∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) ∧
      (f ≠ 0 → ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ 0) ∧
      ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
  first | exact @GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self | exact GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self | (intros; apply GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCosetRepTranslatesOrthogonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAndSeparates
open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.CharSep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_le_one (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) (x : k) : ‖ψ0 x‖ ≤ 1 := by
  obtain ⟨B, hB⟩ := (SplitWeil.isCompact_int k).exists_bound_of_continuousOn
    (f := fun y => ψ0 (x * y)) (hc.comp (continuous_const.mul continuous_id)).continuousOn
  have hpow : ∀ m : ℕ, ‖ψ0 x‖ ^ m ≤ B := fun m => by
    have hm : ((m : k)) ∈ 𝒪[k] := by
      simpa using (Subring.natCast_mem (𝒪[k]) m)
    have := hB _ hm
    rwa [show x * (m : k) = m • x by rw [nsmul_eq_mul, mul_comm], AddChar.map_nsmul_eq_pow, norm_pow] at this
  by_contra h
  push_neg at h
  obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop B |>.exists
  exact absurd (hpow m) (not_le.mpr hm)

theorem norm_eq_one (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) (x : k) : ‖ψ0 x‖ = 1 := by
  have h1 := norm_le_one ψ0 hc x
  have h2 := norm_le_one ψ0 hc (-x)
  have hm : ψ0 x * ψ0 (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hn : ‖ψ0 x‖ * ‖ψ0 (-x)‖ = 1 := by rw [← norm_mul, hm, norm_one]
  by_contra hne
  have hlt : ‖ψ0 x‖ < 1 := lt_of_le_of_ne h1 hne
  have : ‖ψ0 x‖ * ‖ψ0 (-x)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hlt
  linarith

def toCircle (ψ0 : AddChar k ℂ) (h : ∀ x, ‖ψ0 x‖ = 1) : AddChar k Circle where
  toFun x := ⟨ψ0 x, mem_sphere_zero_iff_norm.2 (h x)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (show ψ0 (a + b) = ψ0 a * ψ0 b from AddChar.map_add_eq_mul ψ0 a b)

theorem toCircle_apply (ψ0 : AddChar k ℂ) (h : ∀ x, ‖ψ0 x‖ = 1) (x : k) :
    ((toCircle ψ0 h x : Circle) : ℂ) = ψ0 x := rfl

theorem unitary_and_separates : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    (∀ x, ‖ψ0 x‖ = 1) ∧ ∀ a : k, a ∉ 𝒪[k] → ∃ c : k, (∀ y ∈ 𝒪[k], ψ0 (c * y) = 1) ∧ ψ0 (c * a) ≠ 1 := by
  intro k _ _ _ _ ψ0 hc h1
  have hu := norm_eq_one ψ0 hc
  refine ⟨hu, fun a ha => ?_⟩
  set ψ := toCircle ψ0 hu
  have hψc : Continuous ψ := Continuous.subtype_mk hc _
  have hψ1 : ψ ≠ 1 := by
    intro h
    apply h1
    ext x
    have := congrArg (fun χ : AddChar k Circle => ((χ x : Circle) : ℂ)) h
    simpa [ψ, toCircle_apply] using this
  obtain ⟨c₀, hc₀⟩ := SplitWeil.exists_hasConductor_of_continuous ψ hψc hψ1
  have hx : a ∉ SplitWeil.cball (c₀ * c₀⁻¹) := by
    rw [mul_inv_cancel]
    intro h
    exact ha ((Valuation.mem_integer_iff _ _).mpr (by simpa [SplitWeil.cball] using h))
  obtain ⟨t, ht, hne⟩ := hc₀.exists_ne_one c₀ hx
  refine ⟨t, fun y hy => ?_, fun h => hne (Circle.ext (by simpa [ψ, toCircle_apply] using h))⟩
  have hy' : valuation k y ≤ 1 := hy
  have : t * y ∈ SplitWeil.cball c₀ := by
    simp only [SplitWeil.cball, Set.mem_setOf_eq, map_mul] at ht ⊢
    exact (mul_le_mul' le_rfl hy').trans (by rw [mul_one]; exact ht)
  have := hc₀.eq_one this
  simpa [ψ, toCircle_apply] using congrArg (fun z : Circle => (z : ℂ)) this

end GlobalTheory.CharSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCosetRepTranslatesOrthogonal
open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

def entryForm (c : k) (i0 : Fin n) (j : Fin d) : Matrix (Fin n) (Fin d) k →ₗ[k] k where
  toFun Y := c * Y i0 j
  map_add' Y Y' := by simp [mul_add]
  map_smul' a Y := by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem mu_tr_eq_smul (ψ0 : AddChar k ℂ)
    (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ))
    (hι : Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _))
    (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hTr : ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C))
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMu : ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y)
    (φ0 : (Fin n × Fin d → k) → ℂ) (hφ0 : φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k)) (hι0 : ι φ0 = intInd (k := k) n d)
    (l : Matrix (Fin n) (Fin d) k →ₗ[k] k)
    (hl : ∀ Y : Matrix (Fin n) (Fin d) k, (∀ i j, Y i j ∈ 𝒪[k]) → ψ0 (l Y) = 1)
    (C : Matrix (Fin n) (Fin d) k) :
    Mu l (Tr C φ0) = ψ0 (l (-C)) • Tr C φ0 := by
  obtain ⟨hT, hTι⟩ := hTr C φ0 hφ0
  obtain ⟨hM, hMι⟩ := hMu l _ hT
  refine hι hM ((GlobalTheory.WeilM.SB _).smul_mem _ hT) ?_
  rw [map_smul, hMι, hTι, hι0]
  funext Y
  simp only [Pi.smul_apply, smul_eq_mul, intInd]
  by_cases h : ∀ i j, (Y + C) i j ∈ 𝒪[k]
  · have e : ψ0 (l Y) = ψ0 (l (-C)) := by
      calc ψ0 (l Y) = ψ0 (l (Y + C) + l (-C)) := by rw [← map_add (f := _)]; congr 2; abel
        _ = ψ0 (l (-C)) := by rw [AddChar.map_add_eq_mul, hl _ h, one_mul]
    rw [e]
  · rw [Set.indicator_of_notMem (show Y + C ∉ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} from h)]
    simp

theorem inner_eq_mul_inner (ψ0 : AddChar k ℂ)
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMuI : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ)
    (μ : @Measure (Fin n × Fin d → k) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (l : Matrix (Fin n) (Fin d) k →ₗ[k] k) (f f' : (Fin n × Fin d → k) → ℂ)
    (hf : f ∈ GlobalTheory.WeilM.SB _) (hf' : f' ∈ GlobalTheory.WeilM.SB _) (a b : ℂ) (ha : Mu l f = a • f) (hb : Mu l f' = b • f') :
    ∫ y, f y * (starRingEnd ℂ) (f' y) ∂μ = a * (starRingEnd ℂ) b * ∫ y, f y * (starRingEnd ℂ) (f' y) ∂μ := by
  rw [← integral_const_mul, ← hMuI μ hμ l f hf f' hf', ha, hb]
  congr 1; funext y
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring

end GlobalTheory.HeisUnit

namespace GlobalTheory.HeisUnit

theorem cosetRep_sub_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n d : ℕ} (ϖ : kˣ) (i0 : Fin n) (T T' : Fin d → SplitFlip.Res (k := k) 1) (j : Fin d) :
    (cosetRep ϖ i0 T' - cosetRep ϖ i0 T) i0 j =
      (ϖ : k)⁻¹ * (((Quotient.out (T j) : 𝒪[k]) : k) - ((Quotient.out (T' j) : 𝒪[k]) : k)) := by
  simp [cosetRep]; ring

theorem not_mem_int_of_ne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (hϖ : SplitFlip.IsUnif ϖ) (t t' : SplitFlip.Res (k := k) 1) (h : t ≠ t') :
    (ϖ : k)⁻¹ * (((Quotient.out t : 𝒪[k]) : k) - ((Quotient.out t' : 𝒪[k]) : k)) ∉ 𝒪[k] := by
  intro ha
  apply h
  rw [← Ideal.Quotient.mk_out t, ← Ideal.Quotient.mk_out t', Ideal.Quotient.eq]
  have hs : Quotient.out t - Quotient.out t' ∈ Ideal.span {(⟨ϖ, hϖ.mem⟩ : 𝒪[k])} := by
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, ha⟩, Subtype.ext ?_⟩
    simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub]
    field_simp
  convert hs using 1
  exact (pow_one _).trans hϖ.maximalIdeal_eq

theorem orth_of_charsep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ)
    (hcs : (∀ x, ‖ψ0 x‖ = 1) ∧ ∀ a : k, a ∉ 𝒪[k] → ∃ c : k, (∀ y ∈ 𝒪[k], ψ0 (c * y) = 1) ∧ ψ0 (c * a) ≠ 1)
    (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ))
    (hι : Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _))
    (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hTr : ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C))
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMu : ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y)
    (hMuI : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ)
    (φ0 : (Fin n × Fin d → k) → ℂ) (hφ0 : φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k)) (hι0 : ι φ0 = intInd (k := k) n d)
    (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (i0 : Fin n) (T T' : Fin d → GlobalTheory.SplitFlip.Res (k := k) 1) (hTT : T ≠ T')
    (μ : @Measure (Fin n × Fin d → k) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∫ y, Tr (cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y) ∂μ = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hTT
  set C := cosetRep ϖ i0 T
  set C' := cosetRep ϖ i0 T'
  have hna := not_mem_int_of_ne ϖ hϖ (T j) (T' j) hj
  rw [← cosetRep_sub_apply ϖ i0 T T' j] at hna
  obtain ⟨c, hc1, hc2⟩ := hcs.2 _ hna
  have hl : ∀ Y : Matrix (Fin n) (Fin d) k, (∀ i j, Y i j ∈ 𝒪[k]) → ψ0 (entryForm c i0 j Y) = 1 :=
    fun Y hY => hc1 _ (hY i0 j)
  have e1 := mu_tr_eq_smul ψ0 ι hι Tr hTr Mu hMu φ0 hφ0 hι0 _ hl C
  have e2 := mu_tr_eq_smul ψ0 ι hι Tr hTr Mu hMu φ0 hφ0 hι0 _ hl C'
  have hI := inner_eq_mul_inner ψ0 Mu hMuI μ hμ (entryForm c i0 j) _ _ (hTr C φ0 hφ0).1 (hTr C' φ0 hφ0).1 _ _ e1 e2
  have hA : ψ0 (entryForm c i0 j (-C)) * (starRingEnd ℂ) (ψ0 (entryForm c i0 j (-C'))) ≠ 1 := by
    rw [← Complex.inv_eq_conj (hcs.1 _), ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul, ← map_neg, ← map_add (f := _),
      neg_neg, neg_add_eq_sub]
    exact hc2
  set I := ∫ y, Tr C φ0 y * (starRingEnd ℂ) (Tr C' φ0 y) ∂μ
  have h0 : (1 - ψ0 (entryForm c i0 j (-C)) * (starRingEnd ℂ) (ψ0 (entryForm c i0 j (-C')))) * I = 0 := by
    linear_combination hI
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 (Ne.symm hA))

end GlobalTheory.HeisUnit

namespace GlobalTheory.HeisUnit

theorem tr_cosetRep_orth {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ) (hψc : Continuous ψ0) (hψ1 : ψ0 ≠ 1)
    (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ))
    (hι : Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _))
    (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hTr : ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C))
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMu : ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y)
    (hMuI : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ)
    (φ0 : (Fin n × Fin d → k) → ℂ) (hφ0 : φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k)) (hι0 : ι φ0 = intInd (k := k) n d)
    (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (i0 : Fin n) (T T' : Fin d → GlobalTheory.SplitFlip.Res (k := k) 1) (hTT : T ≠ T')
    (μ : @Measure (Fin n × Fin d → k) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∫ y, Tr (cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y) ∂μ = 0 :=
  orth_of_charsep ψ0 (GlobalTheory.CharSep.unitary_and_separates ψ0 hψc hψ1) ι hι Tr hTr Mu hMu hMuI φ0 hφ0 hι0 ϖ hϖ i0 T T'
    hTT μ hμ

end GlobalTheory.HeisUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCosetRepTranslatesOrthogonalStatement
open MeasureTheory Matrix ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCosetRepTranslates_orthogonal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    ∀ (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd (k := k) n d →
    ∀ (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n) (T T' : Fin d → GlobalTheory.SplitFlip.Res (k := k) 1), T ≠ T' →
    ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫ y, Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T') φ0 y) ∂μ = 0 := by
  exact @GlobalTheory.HeisUnit.tr_cosetRep_orth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqUniformizerCharacterMulResidueCardPowEqOneStatement
open MeasureTheory Matrix ValuativeRel

open GlobalTheory GlobalTheory.HeisUnit in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normSq_uniformizer_character_mul_residueCard_pow_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ},
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd k n d → φ0 ≠ 0 →
    ∀ (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n),
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ T T' : Fin d → GlobalTheory.SplitFlip.Res (k := k) 1, T ≠ T' →
      ∫ y, Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T') φ0 y) ∂μ = 0) →
    ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 := by
  intro k _ _ _ _ n d ι hinj Tr hTr hTrIso S hS hSiso χ hχ φ0 hφ0 hι0 hne ϖ hϖ i0 horth
  classical
  set F := ∑ T : Fin d → SplitFlip.Res (k := k) 1, Tr (cosetRep ϖ i0 T) φ0 with hF
  have hFSB : F ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k) := Submodule.sum_mem _ fun T _ => (hTr _ φ0 hφ0).1
  have hSg : S (diagAt ϖ i0) φ0 = (χ ϖ : ℂ) • F := by
    apply hinj (hS _ φ0 hφ0) (Submodule.smul_mem _ _ hFSB)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hχ _ φ0 hφ0, map_smul, map_sum, det_diagAt, hι0]
    funext Y
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, (hTr _ φ0 hφ0).2, hι0]
    have hIntInd (M : Matrix (Fin n) (Fin d) k) :
        intInd k n d M = if ∀ i j, M i j ∈ 𝒪[k] then 1 else 0 := by
      simp only [intInd, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    have hSubMem (y : k) (t : SplitFlip.Res (k := k) 1) :
        y - (ϖ : k)⁻¹ * ((Quotient.out t : 𝒪[k]) : k) ∈ 𝒪[k] ↔
          ∃ h : (ϖ : k) * y ∈ 𝒪[k], t = Ideal.Quotient.mk _ ⟨(ϖ : k) * y, h⟩ := by
      have ht : t = Ideal.Quotient.mk _ (Quotient.out t) := (Quotient.out_eq t).symm
      set a := Quotient.out t
      have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
      constructor
      · intro hc
        have hy : (ϖ : k) * y = ϖ * (y - (ϖ : k)⁻¹ * a) + a := by field_simp; ring
        have hmem : (ϖ : k) * y ∈ 𝒪[k] := hy ▸ add_mem (mul_mem hϖ.mem hc) a.2
        refine ⟨hmem, ?_⟩
        rw [ht, Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton']
        refine ⟨-⟨_, hc⟩, Subtype.ext ?_⟩
        push_cast
        field_simp
        ring
      · rintro ⟨h, e⟩
        have e' := ht.symm.trans e
        rw [Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at e'
        obtain ⟨c, hc⟩ := e'
        have hc' : (c : k) * ϖ = a - ϖ * y := by simpa using congrArg Subtype.val hc
        have hinv : (ϖ : k)⁻¹ * ϖ = 1 := inv_mul_cancel₀ hϖ0
        have : y - (ϖ : k)⁻¹ * a = -(c : k) := by
          linear_combination (ϖ : k)⁻¹ * hc' - (y + c) * hinv
        rw [this]
        exact neg_mem c.2
    have hDiag :
        intInd k n d ((diagAt ϖ i0).valᵀ * Y) =
          ∑ T : Fin d → SplitFlip.Res (k := k) 1, intInd k n d (Y + cosetRep ϖ i0 T) := by
      have hL : ∀ i j, ((diagAt ϖ i0).valᵀ * Y) i j = (if i = i0 then (ϖ : k) else 1) * Y i j := by
        intro i j
        rw [diagAt_val, diagonal_transpose, diagonal_mul]
      have hR : ∀ (T : Fin d → SplitFlip.Res (k := k) 1) i j, (Y + cosetRep ϖ i0 T) i j =
          if i = i0 then Y i j - (ϖ : k)⁻¹ * ((Quotient.out (T j) : 𝒪[k]) : k) else Y i j := by
        intro T i j
        simp only [cosetRep, Matrix.add_apply, Matrix.of_apply]
        split_ifs <;> ring
      by_cases hQR : (∀ i j, i ≠ i0 → Y i j ∈ 𝒪[k]) ∧ ∀ j, (ϖ : k) * Y i0 j ∈ 𝒪[k]
      · obtain ⟨hQ, hRR⟩ := hQR
        let T0 : Fin d → SplitFlip.Res (k := k) 1 := fun j => Ideal.Quotient.mk _ ⟨_, hRR j⟩
        have hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 1 := by
          rw [hIntInd, ite_eq_left]
          intro i j
          rw [hL]
          split_ifs with h
          · subst h; exact hRR j
          · rw [one_mul]; exact hQ i j h
        have hs : ∀ T, intInd k n d (Y + cosetRep ϖ i0 T) = if T = T0 then 1 else 0 := by
          intro T
          rw [hIntInd]
          by_cases hT : T = T0
          · rw [ite_eq_left hT, ite_eq_left]
            intro i j
            rw [hR]
            split_ifs with h
            · subst h; exact (hSubMem _ _).2 ⟨hRR j, by rw [hT]⟩
            · exact hQ i j h
          · rw [ite_eq_right hT, ite_eq_right]
            intro hm
            apply hT
            funext j
            have := hm i0 j
            rw [hR, ite_eq_left rfl] at this
            obtain ⟨_, e⟩ := (hSubMem _ _).1 this
            exact e
        rw [hl, Finset.sum_congr rfl (fun T _ => hs T), Finset.sum_ite_eq']
        simp
      · have hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 0 := by
          rw [hIntInd, ite_eq_right]
          intro hm
          refine hQR ⟨fun i j h => ?_, fun j => ?_⟩
          · have := hm i j; rwa [hL, ite_eq_right h, one_mul] at this
          · have := hm i0 j; rwa [hL, ite_eq_left rfl] at this
        rw [hl]
        symm
        apply Finset.sum_eq_zero
        intro T _
        rw [hIntInd, ite_eq_right]
        intro hm
        refine hQR ⟨fun i j h => ?_, fun j => ?_⟩
        · have := hm i j; rwa [hR, ite_eq_right h] at this
        · have := hm i0 j
          rw [hR, ite_eq_left rfl] at this
          exact ((hSubMem _ _).1 this).1
    rw [hDiag]

  let _ : MeasurableSpace (Fin n × Fin d → k) := borel _
  have _ : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → k) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  have hiso := hSiso (diagAt ϖ i0) φ0 hφ0 μ hμ
  rw [hSg] at hiso
  simp only [Pi.smul_apply, smul_eq_mul, eNorm_mul, mul_pow] at hiso
  rw [lintegral_const_mul' _ _ (by simp [eNorm_eq_nnNorm])] at hiso
  obtain ⟨hFtop, hFint, -, hFi⟩ := GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ F hFSB
  obtain ⟨h0top, h0int, h0ne, -⟩ := GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ φ0 hφ0
  have hN0 : (∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0ne hne, h0top⟩
  have hint : ∀ T T' : Fin d → SplitFlip.Res (k := k) 1, Integrable (fun y => Tr (cosetRep ϖ i0 T) φ0 y *
      (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y)) μ := fun T T' =>
    (GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ _ (hTr _ φ0 hφ0).1).2.2.2 _ (hTr _ φ0 hφ0).1
  have hsum : ∫ y, F y * (starRingEnd ℂ) (F y) ∂μ =
      (Fintype.card (Fin d → SplitFlip.Res (k := k) 1) : ℂ) * ∫ y, φ0 y * (starRingEnd ℂ) (φ0 y) ∂μ := by
    have hpt : ∀ y, F y * (starRingEnd ℂ) (F y) = ∑ T : Fin d → SplitFlip.Res (k := k) 1, ∑ T' : Fin d → SplitFlip.Res (k := k) 1,
        Tr (cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y) := by
      intro y
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hF, Finset.sum_apply, map_sum, Finset.sum_mul_sum]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun T _ => integrable_finsetSum _ fun T' _ => hint T T']
    simp_rw [integral_finsetSum _ fun T' _ => hint _ T']
    rw [Finset.card_univ.symm, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.sum_eq_single T (fun T' _ hT' => horth μ hμ T T' (Ne.symm hT')) (fun h => absurd (Finset.mem_univ _) h)]
    exact hTrIso μ hμ _ φ0 hφ0 φ0 hφ0
  rw [hFint, h0int] at hsum
  have hLF : (∫⁻ y, ‖F y‖ₑ ^ 2 ∂μ).toReal =
      (Fintype.card (Fin d → SplitFlip.Res (k := k) 1) : ℝ) * (∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ).toReal := by
    exact_mod_cast hsum
  have hiso' := congrArg ENNReal.toReal hiso
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_eNorm, hLF] at hiso'
  have hcard : (Fintype.card (Fin d → SplitFlip.Res (k := k) 1) : ℝ) = (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_eq_nat_card]
    have : Nat.card (SplitFlip.Res (k := k) 1) = GlobalTheory.SplitWeil.resCard k :=
      Nat.card_congr (Ideal.quotEquivOfEq (pow_one 𝓂[k])).toEquiv
    rw [this]; push_cast; ring
  rw [hcard] at hiso'
  apply mul_right_cancel₀ hN0
  linear_combination hiso'
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMulNormalisedAbsPowHalfEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMulNormalisedAbsPowHalfEqOne
open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.CharNormHalf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def normTwist (d : ℕ) (χ : kˣ →* ℂˣ) : kˣ →* ℂˣ where
  toFun x := Units.mk0 (((‖(χ x : ℂ)‖ : ℝ) : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2)))
    (mul_ne_zero (by exact_mod_cast (norm_ne_zero_iff.2 (χ x).ne_zero)) (GlobalTheory.SplitFlip.apow_ne_zero _ _))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [map_mul, Units.val_mul, norm_mul, Complex.ofReal_mul, Units.val_mk0, GlobalTheory.SplitFlip.apow_mul]
    ring

theorem normTwist_apply (d : ℕ) (χ : kˣ →* ℂˣ) (x : kˣ) :
    (normTwist d χ x : ℂ) = ((‖(χ x : ℂ)‖ : ℝ) : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2)) := rfl

theorem norm_mul_apow_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (χ : kˣ →* ℂˣ), (∀ u : kˣ, valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1) →
    ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 →
    ∀ x : kˣ, ‖(χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))‖ = 1 := by
  intro k _ _ _ _ d χ hu ϖ hϖ hn x
  set B := normTwist d χ
  have hunr : ∀ y : kˣ, valuation k (y : k) = 1 → B y = 1 := by
    intro y hy
    ext
    rw [normTwist_apply, hu y hy, GlobalTheory.SplitFlip.apow_of_valuation_eq_one hy]
    simp
  have hq : (1 : ℝ) < (GlobalTheory.SplitWeil.resCard k : ℝ) := by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard (k := k)
  set q : ℝ := (GlobalTheory.SplitWeil.resCard k : ℝ) with hqdef
  have hq0 : 0 < q := by linarith
  have hnabs : GlobalTheory.SplitWeil.nabs k ϖ = q⁻¹ := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.SmGL.ord_eq_one (k := k) hϖ]
    simp [hqdef]
  have hap : GlobalTheory.SplitFlip.apow ϖ (-((d : ℂ) / 2)) = ((q ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
    rw [GlobalTheory.SplitFlip.apow, hnabs, show (-((d : ℂ) / 2)) = ((-((d : ℝ) / 2) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (inv_nonneg.2 hq0.le), Real.inv_rpow hq0.le, ← Real.rpow_neg hq0.le, neg_neg]
  have hBϖ : B ϖ = 1 := by
    ext
    rw [normTwist_apply, hap, Units.val_one, ← Complex.ofReal_mul]
    have hb0 : 0 ≤ ‖(χ ϖ : ℂ)‖ * q ^ ((d : ℝ) / 2) := by positivity
    have hsq : (‖(χ ϖ : ℂ)‖ * q ^ ((d : ℝ) / 2)) ^ 2 = 1 := by
      rw [mul_pow, ← Real.rpow_natCast (q ^ ((d : ℝ) / 2)) 2, ← Real.rpow_mul hq0.le]
      rw [show (d : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      exact hn
    have := (pow_eq_one_iff_of_nonneg hb0 two_ne_zero).1 hsq
    rw [this]; simp
  have hB := GlobalTheory.SmGL.eq_unrChar (k := k) (χ := B) hunr hϖ
  have hx : B x = 1 := by
    rw [hB, hBϖ, GlobalTheory.SmGL.unrChar_apply, _root_.one_zpow]
  have hx' : ‖(B x : ℂ)‖ = 1 := by rw [hx]; simp
  rw [normTwist_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm] at hx'
  rw [norm_mul]; exact hx'

end GlobalTheory.CharNormHalf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMulNormalisedAbsPowHalfEqOneStatement
open MeasureTheory Matrix ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_mul_normalisedAbsPow_half_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (χ : kˣ →* ℂˣ), (∀ u : kˣ, valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1) →
    ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 →
    ∀ x : kˣ, ‖(χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))‖ = 1 := by
  first | exact @GlobalTheory.CharNormHalf.norm_mul_apow_eq_one | exact GlobalTheory.CharNormHalf.norm_mul_apow_eq_one | (intros; apply GlobalTheory.CharNormHalf.norm_mul_apow_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCharacterUnitEqOneHeisenbergStatement
open MeasureTheory Matrix ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_character_unit_eq_one_heisenberg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ},
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd (k := k) n d →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ 0 ∧ ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ ⊤) →
    ∀ (_i0 : Fin n) (u : kˣ), valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1 := by
  intro k _ _ _ _ n d ι hinj S hS hiso χ hι φ0 hφ0 hι0 hfin i0 u hu
  let g := GlobalTheory.HeisUnit.diagAt u i0
  have hdet : Matrix.GeneralLinearGroup.det g = u := GlobalTheory.HeisUnit.det_diagAt u i0
  have hInd (Y : Matrix (Fin n) (Fin d) k) :
      GlobalTheory.HeisUnit.intInd (k := k) n d (g.valᵀ * Y) =
        GlobalTheory.HeisUnit.intInd (k := k) n d Y := by
    have hEntry (i : Fin n) (j : Fin d) : (g.valᵀ * Y) i j ∈ 𝒪[k] ↔ Y i j ∈ 𝒪[k] := by
      change ((GlobalTheory.HeisUnit.diagAt u i0).valᵀ * Y) i j ∈ 𝒪[k] ↔ Y i j ∈ 𝒪[k]
      rw [GlobalTheory.HeisUnit.diagAt_val, diagonal_transpose, diagonal_mul]
      by_cases hi : i = i0
      · rw [if_pos hi]
        simp only [Valuation.mem_integer_iff, map_mul, hu, one_mul]
      · rw [if_neg hi, one_mul]
    let L : Set (Matrix (Fin n) (Fin d) k) := {Z | ∀ i j, Z i j ∈ 𝒪[k]}
    have hL : g.valᵀ * Y ∈ L ↔ Y ∈ L :=
      forall_congr' fun i => forall_congr' fun j => hEntry i j
    change L.indicator 1 (g.valᵀ * Y) = L.indicator 1 Y
    by_cases hY : Y ∈ L
    · rw [Set.indicator_of_mem (hL.mpr hY), Set.indicator_of_mem hY]
      rfl
    · rw [Set.indicator_of_notMem (mt hL.mp hY), Set.indicator_of_notMem hY]
  have hmem : (χ u : ℂ) • φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k) :=
    Submodule.smul_mem _ _ hφ0
  have heq : S g φ0 = (χ u : ℂ) • φ0 := by
    refine hinj (hS g φ0 hφ0) hmem ?_
    rw [hι g φ0 hφ0, map_smul, hι0, hdet]
    funext Y
    rw [hInd Y]
    rfl
  letI : MeasurableSpace (Fin n × Fin d → k) := borel _
  haveI : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  have hμ : Measure.IsAddHaarMeasure (Measure.addHaar : Measure (Fin n × Fin d → k)) :=
    inferInstance
  have h := hiso g φ0 hφ0 Measure.addHaar hμ
  rw [heq] at h
  exact GlobalTheory.WeilM.norm_eq_one_of_lintegral_eq h (hfin _ hμ).1 (hfin _ hμ).2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsWeilCharacterDetEqAbsDetPow
open MeasureTheory Matrix

namespace GlobalTheory.HeisUnit

theorem exists_unitary_factor : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
      (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∃ ν : kˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧ ∀ g : GL (Fin n) k,
      (χ (Matrix.GeneralLinearGroup.det g) : ℂ) = ν (Matrix.GeneralLinearGroup.det g) * GlobalTheory.SplitFlip.apow (Matrix.GeneralLinearGroup.det g) ((d : ℂ) / 2) := by
  intro k _ _ _ _ n d ψ0 hψc hψ1 ι hι Tr Mu hTr hMu hTrI hMuI S hS hSI χ hχ
  let ν : kˣ →* ℂˣ := χ *
    { toFun := fun x => Units.mk0 (GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))) (GlobalTheory.SplitFlip.apow_ne_zero _ _)
      map_one' := Units.ext (GlobalTheory.SplitFlip.apow_one _)
      map_mul' := fun x y => Units.ext (GlobalTheory.SplitFlip.apow_mul x y _) }
  have hν : ∀ x : kˣ, (ν x : ℂ) = (χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2)) := fun x => rfl
  have hfac : ∀ x : kˣ, (χ x : ℂ) = ν x * GlobalTheory.SplitFlip.apow x ((d : ℂ) / 2) := fun x => by
    rw [hν, mul_assoc, ← GlobalTheory.SplitFlip.apow_add, neg_add_cancel, GlobalTheory.SplitFlip.apow_zero, mul_one]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, fun x => by simp, fun g => ?_⟩
    have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    simp
  · refine ⟨ν, fun x => ?_, fun g => hfac _⟩
    let i0 : Fin n := ⟨0, hn⟩
    obtain ⟨φ0, hφ0, hιφ0⟩ := hι.surjOn (GlobalTheory.HeisUnit.intInd_mem_SB (k := k) n d)
    have hne : φ0 ≠ 0 := by
      rintro rfl
      have h := congrFun hιφ0 0
      rw [map_zero, GlobalTheory.HeisUnit.intInd_zero] at h
      exact zero_ne_one h
    have hN : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ 0 ∧ ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ ⊤ := fun μ hμ =>
      ⟨(GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ φ0 hφ0).2.2.1 hne, (GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ φ0 hφ0).1⟩
    have hU := GlobalTheory.T.norm_character_unit_eq_one_heisenberg ι hι.injOn S hS hSI χ hχ φ0 hφ0 hιφ0 hN i0
    obtain ⟨ϖ, hϖ⟩ := GlobalTheory.SplitFlip.exists_isUnif (k := k)
    have hP := GlobalTheory.T.normSq_uniformizer_character_mul_residueCard_pow_eq_one ι hι.injOn Tr hTr hTrI S hS hSI χ hχ φ0 hφ0 hιφ0 hne ϖ hϖ i0
      (fun μ hμ T T' h => GlobalTheory.T.heisenbergCosetRepTranslates_orthogonal ψ0 hψc hψ1 ι hι.injOn Tr hTr Mu hMu hMuI φ0 hφ0 hιφ0 ϖ hϖ i0 T T' h μ hμ)
    rw [hν]
    exact GlobalTheory.T.norm_mul_normalisedAbsPow_half_eq_one d χ hU ϖ hϖ hP x

end GlobalTheory.HeisUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsWeilCharacterDetEqAbsDetPowStatement
open MeasureTheory Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_weilCharacter_det_eq_abs_det_pow : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
      (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∃ ν : kˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧ ∀ g : GL (Fin n) k,
      (χ (Matrix.GeneralLinearGroup.det g) : ℂ) = ν (Matrix.GeneralLinearGroup.det g) * GlobalTheory.SplitFlip.apow (Matrix.GeneralLinearGroup.det g) ((d : ℂ) / 2) := by
  first | exact @GlobalTheory.HeisUnit.exists_unitary_factor | exact GlobalTheory.HeisUnit.exists_unitary_factor | (intros; apply GlobalTheory.HeisUnit.exists_unitary_factor <;> assumption)
end
