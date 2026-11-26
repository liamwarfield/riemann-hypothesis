module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.SetIntegralCharEqZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.PsiVTrPairAddLeft

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.ContinuousLatticeNorm
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {n : ℕ} {ψ : AddChar (AF F) ℂ}
  {v : HeightOneSpectrum (𝓞 F)} {μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)} {νv : Measure (HermR (Fv F v) σ n)}
  {lam : Measure (Fin n → Fv F v ⊗[F] E)} {L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)}
  {Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ} {g : HermR (Fv F v) σ n → ℂ} {T : HermR (Fv F v) σ n}

theorem isClosed_herm (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed ((HermR (Fv F v) σ n : AddSubgroup (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) :
      Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) :=
  isClosed_hermSet v σ n

theorem isCompact_ballH (R : ℝ) : IsCompact {b : HermR (Fv F v) σ n | nM v b.1 ≤ R} :=
  (isClosed_herm (v := v) σ n).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_ballM (v := v) (p := n) (q := n) R)

theorem measurableSet_ballH (R : ℝ) : MeasurableSet {b : HermR (Fv F v) σ n | nM v b.1 ≤ R} := by
  have hc : IsClosed {b : HermR (Fv F v) σ n | nM v b.1 ≤ R} :=
    isClosed_le ((continuous_nM (v := v) (p := n) (q := n)).comp continuous_subtype_val) continuous_const
  exact hc.measurableSet

theorem lattice_norm_ge_one (h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T) (b : HermR (Fv F v) σ n) :
    1 ≤ nu2 lam L₁ L₂ b.1 := by
  have := h.haar
  unfold nu2
  set S : Set (Fin n → Fv F v ⊗[F] E) := {x | ∃ y ∈ L₁, ∃ y' ∈ L₂, x = y + b.1.mulVec y'} with hS
  have hsub : (L₁ : Set (Fin n → Fv F v ⊗[F] E)) ⊆ S := fun y hy =>
    ⟨y, hy, 0, L₂.zero_mem, by simp⟩
  have hpos : lam L₁ ≠ 0 := (h.co₁.1.measure_pos lam ⟨0, L₁.zero_mem⟩).ne'
  have hfin1 : lam L₁ ≠ ⊤ := h.co₁.2.measure_lt_top.ne
  have hcS : IsCompact S := by
    have e : S = (fun p : (Fin n → Fv F v ⊗[F] E) × (Fin n → Fv F v ⊗[F] E) => p.1 + b.1.mulVec p.2) ''
        ((L₁ : Set (Fin n → Fv F v ⊗[F] E)) ×ˢ (L₂ : Set (Fin n → Fv F v ⊗[F] E))) := by
      ext x
      constructor
      · rintro ⟨y, hy, y', hy', rfl⟩
        exact ⟨(y, y'), ⟨hy, hy'⟩, rfl⟩
      · rintro ⟨⟨y, y'⟩, ⟨hy, hy'⟩, rfl⟩
        exact ⟨y, hy, y', hy', rfl⟩
    rw [e]
    exact (h.co₁.2.prod h.co₂.2).image (continuous_fst.add (continuous_const.matrix_mulVec continuous_snd))
  have hfinS : lam S ≠ ⊤ := hcS.measure_lt_top.ne
  have h1 : 1 ≤ lam S / lam L₁ := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin1), one_mul]
    exact measure_mono hsub
  have h2 := ENNReal.toReal_mono (ENNReal.div_ne_top hfinS hpos) h1
  rwa [ENNReal.toReal_one] at h2

theorem continuous_lattice_norm (h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T) :
    Continuous fun b : HermR (Fv F v) σ n => nu2 lam L₁ L₂ b.1 := by
  have hev : ∀ᶠ d in 𝓝 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)),
      ∀ y' ∈ (L₂ : Set (Fin n → Fv F v ⊗[F] E)), d.mulVec y' ∈ L₁ := by
    refine h.co₂.2.eventually_forall_of_forall_eventually fun y' _ => ?_
    have hc : Continuous fun p : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) × (Fin n → Fv F v ⊗[F] E) =>
        p.1.mulVec p.2 := continuous_fst.matrix_mulVec continuous_snd
    have h0 : (fun p : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) × (Fin n → Fv F v ⊗[F] E) => p.1.mulVec p.2)
        ((0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)), y') ∈ (L₁ : Set (Fin n → Fv F v ⊗[F] E)) := by
      simp only [Matrix.zero_mulVec]
      exact L₁.zero_mem
    exact hc.continuousAt.preimage_mem_nhds (h.co₁.1.mem_nhds h0)
  have key : ∀ b c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
      (∀ y' ∈ (L₂ : Set (Fin n → Fv F v ⊗[F] E)), (c - b).mulVec y' ∈ L₁) →
      nu2 lam L₁ L₂ c = nu2 lam L₁ L₂ b := by
    intro b c hcb
    have e : ∀ x : Fin n → Fv F v ⊗[F] E, (∃ y ∈ L₁, ∃ y' ∈ L₂, x = y + c.mulVec y') ↔
        (∃ y ∈ L₁, ∃ y' ∈ L₂, x = y + b.mulVec y') := by
      intro x
      constructor
      · rintro ⟨y, hy, y', hy', rfl⟩
        refine ⟨y + (c - b).mulVec y', L₁.add_mem hy (hcb y' hy'), y', hy', ?_⟩
        rw [Matrix.sub_mulVec]
        abel
      · rintro ⟨y, hy, y', hy', rfl⟩
        refine ⟨y - (c - b).mulVec y', L₁.sub_mem hy (hcb y' hy'), y', hy', ?_⟩
        rw [Matrix.sub_mulVec]
        abel
    simp only [nu2, e]
  refine continuous_iff_continuousAt.2 fun b => ?_
  have ht : Tendsto (fun c : HermR (Fv F v) σ n => c.1 - b.1) (𝓝 b) (𝓝 0) := by
    have h1 : Tendsto (fun c : HermR (Fv F v) σ n => c.1) (𝓝 b) (𝓝 b.1) := continuous_subtype_val.tendsto b
    have h2 := h1.sub_const b.1
    rwa [sub_self] at h2
  have hb := ht.eventually hev
  exact (continuousAt_const (y := nu2 lam L₁ L₂ b.1)).congr (hb.mono fun c hc => (key b.1 c.1 hc).symm)

theorem uu_bound (h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T) :
    ∃ C, ∀ b, ‖uu σ J ψ v μv Φv T b‖ ≤ C := by
  refine ⟨∫ Y, ‖Φv Y‖ ∂μv, fun b => ?_⟩
  unfold uu jtR
  rw [norm_mul, norm_psiV h.chr, mul_one]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext Y
  rw [norm_mul, norm_psiV h.chr, mul_one]

private theorem auxc_trPair {α : Type*} [TopologicalSpace α] {f g : α → Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => trPair (Fv F v) (f a) (g a) := by
  unfold trPair
  refine continuous_const.mul ((IsModuleTopology.continuous_of_linearMap
    (Algebra.trace (Fv F v) (Fv F v ⊗[F] E))).comp ?_)
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply j).comp ((continuous_apply i).comp hf)).mul
    ((continuous_apply i).comp ((continuous_apply j).comp hg))

private theorem auxc_gramR (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous (fun X : Fin n → Fin M → Fv F v ⊗[F] E => gramR (Fv F v) σ J X) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [gramR, hR, hform]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((continuous_sigR v σ).comp ((continuous_apply i).comp (continuous_apply a))).mul
    continuous_const).mul ((continuous_apply j).comp (continuous_apply b))

theorem continuous_uu (h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T) :
    Continuous (uu σ J ψ v μv Φv T) := by
  have : μv.IsAddHaarMeasure := h.sdW.1
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Fv F v ⊗[F] E))
  have : SecondCountableTopology (HermR (Fv F v) σ n) :=
    TopologicalSpace.Subtype.secondCountableTopology
      (HermR (Fv F v) σ n : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)))
  have hψc : Continuous (psiV F ψ v) := continuous_psiV h.chr
  have hΦc : Continuous Φv := h.sb.1.continuous
  have hgram := auxc_gramR (v := v) (n := n) σ J
  have hjt : Continuous fun b : HermR (Fv F v) σ n => jtR (Fv F v) σ J (psiV F ψ v) μv Φv b := by
    unfold jtR
    refine continuous_of_dominated (bound := fun Y => ‖Φv Y‖) (fun b => ?_) (fun b => ?_) ?_ ?_
    · exact (hΦc.mul (hψc.comp (auxc_trPair continuous_const hgram))).aestronglyMeasurable
    · exact Eventually.of_forall fun Y => by rw [norm_mul, norm_psiV h.chr, mul_one]
    · exact hΦc.norm.integrable_of_hasCompactSupport h.sb.2.norm
    · exact Eventually.of_forall fun Y =>
        continuous_const.mul (hψc.comp (auxc_trPair continuous_subtype_val continuous_const))
  unfold uu
  exact hjt.mul (hψc.comp (auxc_trPair continuous_const continuous_subtype_val).neg)

end PositivityTheory.SiegelWeilFormula.SwLocFin
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.ExistsLatticeNormGePow
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin.LatticeCovolumeGrowth

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open PositivityTheory.SiegelWeilFormula.SwLocFin
open scoped TensorProduct Matrix ENNReal NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {v : HeightOneSpectrum (𝓞 F)}

def digits (ϖ : Fv F v) : (m : ℕ) → (Fin m → Bool) → Fv F v
  | 0, _ => 0
  | m + 1, δ => (if δ 0 then 1 else 0) + ϖ * digits ϖ m (Fin.tail δ)

theorem norm_ite_le (b : Bool) : ‖(if b then (1 : Fv F v) else 0)‖ ≤ 1 := by
  cases b <;> simp

theorem norm_digits_le {ϖ : Fv F v} (hϖ : ‖ϖ‖ ≤ 1) : ∀ (m : ℕ) (δ : Fin m → Bool), ‖digits ϖ m δ‖ ≤ 1
  | 0, _ => by simp [digits]
  | m + 1, δ => by
    show ‖(if δ 0 then 1 else 0) + ϖ * digits ϖ m (Fin.tail δ)‖ ≤ 1
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_ite_le _) ?_)
    rw [norm_mul]
    exact mul_le_one₀ hϖ (norm_nonneg _) (norm_digits_le hϖ m _)

theorem norm_sub_le_one {a b : Fv F v} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rw [norm_neg]; exact hb))

theorem digits_sep {ϖ : Fv F v} (hϖ1 : ‖ϖ‖ < 1) :
    ∀ (m : ℕ) (δ δ' : Fin m → Bool), δ ≠ δ' → ‖ϖ‖ ^ m ≤ ‖digits ϖ m δ - digits ϖ m δ'‖
  | 0, δ, δ', h => absurd (funext fun i => i.elim0) h
  | m + 1, δ, δ', h => by
    show ‖ϖ‖ ^ (m + 1) ≤ ‖((if δ 0 then 1 else 0) + ϖ * digits ϖ m (Fin.tail δ)) -
      ((if δ' 0 then 1 else 0) + ϖ * digits ϖ m (Fin.tail δ'))‖
    by_cases h0 : δ 0 = δ' 0
    · have ht : Fin.tail δ ≠ Fin.tail δ' := by
        intro ht; apply h; rw [← Fin.cons_self_tail δ, ← Fin.cons_self_tail δ', h0, ht]
      rw [h0, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, pow_succ']
      exact mul_le_mul_of_nonneg_left (digits_sep hϖ1 m _ _ ht) (norm_nonneg _)
    · have hone : ‖((if δ 0 then 1 else 0 : Fv F v)) - (if δ' 0 then 1 else 0)‖ = 1 := by
        cases hδ : δ 0 <;> cases hδ' : δ' 0 <;> simp_all
      have hsmall : ‖ϖ * (digits ϖ m (Fin.tail δ) - digits ϖ m (Fin.tail δ'))‖ < 1 := by
        rw [norm_mul]
        have htail := norm_sub_le_one (norm_digits_le hϖ1.le m (Fin.tail δ))
          (norm_digits_le hϖ1.le m (Fin.tail δ'))
        exact (mul_le_of_le_one_right (norm_nonneg _) htail).trans_lt hϖ1
      have hre : ((if δ 0 then (1 : Fv F v) else 0) + ϖ * digits ϖ m (Fin.tail δ)) -
          ((if δ' 0 then 1 else 0) + ϖ * digits ϖ m (Fin.tail δ')) =
          ((if δ 0 then 1 else 0) - (if δ' 0 then 1 else 0)) +
            ϖ * (digits ϖ m (Fin.tail δ) - digits ϖ m (Fin.tail δ')) := by ring
      rw [hre, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hone]; exact hsmall.ne'), hone]
      exact (pow_le_one₀ (norm_nonneg _) hϖ1.le).trans (le_max_left _ _)

variable {n : ℕ}

theorem card_le_lattice_norm {ι : Type} [Fintype ι] (lam : Measure (Fin n → Fv F v ⊗[F] E)) [lam.IsAddHaarMeasure]
    {L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)} (h1 : IsCO L₁) (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hb : 1 ≤ nu2 lam L₁ L₂ b) (y : ι → Fin n → Fv F v ⊗[F] E) (hy : ∀ i, y i ∈ L₂)
    (hsep : ∀ i j, i ≠ j → b.mulVec (y i) - b.mulVec (y j) ∉ L₁) :
    (Fintype.card ι : ℝ) ≤ nu2 lam L₁ L₂ b := by
  classical
  unfold nu2 at hb ⊢
  set G : Set (Fin n → Fv F v ⊗[F] E) := {x | ∃ y ∈ L₁, ∃ y' ∈ L₂, x = y + b.mulVec y'} with hG
  have hL1m : MeasurableSet (L₁ : Set (Fin n → Fv F v ⊗[F] E)) := h1.1.measurableSet
  set T : ι → Set (Fin n → Fv F v ⊗[F] E) := fun i => (fun x => -b.mulVec (y i) + x) ⁻¹' (L₁ : Set _) with hT
  have hTm : ∀ i, MeasurableSet (T i) := fun i => (measurable_const_add _) hL1m
  have hTv : ∀ i, lam (T i) = lam L₁ := fun i => measure_preimage_add lam _ _
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hxi hxj
    apply hsep j i (Ne.symm hij)
    have hxi' : -b.mulVec (y i) + x ∈ L₁ := hxi
    have hxj' : -b.mulVec (y j) + x ∈ L₁ := hxj
    have heq : b.mulVec (y j) - b.mulVec (y i) = (-b.mulVec (y i) + x) - (-b.mulVec (y j) + x) := by abel
    rw [heq]; exact L₁.sub_mem hxi' hxj'
  have hsubG : (⋃ i, T i) ⊆ G := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact ⟨-b.mulVec (y i) + x, hi, y i, hy i, by abel⟩
  have hmeas : (Fintype.card ι : ℝ≥0∞) * lam L₁ ≤ lam G := by
    calc (Fintype.card ι : ℝ≥0∞) * lam L₁ = ∑ i, lam (T i) := by
          rw [Finset.sum_congr rfl (fun i _ => hTv i), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = lam (⋃ i, T i) := by rw [measure_iUnion hdisj hTm, tsum_fintype]
      _ ≤ lam G := measure_mono hsubG
  have hpos : lam L₁ ≠ 0 := (h1.1.measure_pos lam ⟨0, L₁.zero_mem⟩).ne'
  have hfin : lam L₁ ≠ ⊤ := h1.2.measure_lt_top.ne
  have hle : (Fintype.card ι : ℝ≥0∞) ≤ lam G / lam L₁ :=
    (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin)).2 hmeas
  have hne : lam G / lam L₁ ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hb
    linarith
  have := ENNReal.toReal_mono hne hle
  rwa [ENNReal.toReal_natCast] at this

theorem nV_single_le (k : Fin n) : nV v (Pi.single k (1 : Fv F v ⊗[F] E)) ≤ nA v (1 : Fv F v ⊗[F] E) := by
  classical
  rw [nV_le_iff (nA_nonneg _)]
  intro i
  by_cases hik : i = k
  · subst hik; simp
  · rw [Pi.single_eq_of_ne hik, nA_zero]; exact nA_nonneg _

theorem exists_entry_ge {p q : ℕ} (x : Fin p → Fin q → Fv F v ⊗[F] E) (hx : 0 < nM v x) :
    ∃ i j, nM v x ≤ nA v (x i j) := by
  rcases (Finset.univ : Finset (Fin p × Fin q)).eq_empty_or_nonempty with he | hne
  · exfalso
    have : nM v x ≤ 0 := (nM_le_iff le_rfl).2 fun i j =>
      absurd (Finset.mem_univ (i, j)) (by rw [he]; exact Finset.notMem_empty _)
    linarith
  · obtain ⟨⟨i, j⟩, -, hmax⟩ := Finset.exists_max_image _ (fun ij : Fin p × Fin q => nA v (x ij.1 ij.2)) hne
    exact ⟨i, j, (nM_le_iff (nA_nonneg _)).2 fun i' j' => hmax (i', j') (Finset.mem_univ _)⟩

theorem exists_lattice_norm_ge_pow {ϖ : Fv F v} (hϖ0 : 0 < ‖ϖ‖) (hϖ1 : ‖ϖ‖ < 1)
    (lam : Measure (Fin n → Fv F v ⊗[F] E)) [lam.IsAddHaarMeasure]
    {L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)} (h1 : IsCO L₁) (h2 : IsCO L₂) :
    ∃ R₀ > 0, ∀ (m : ℕ) (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)), 1 ≤ nu2 lam L₁ L₂ b →
      R₀ * ‖ϖ‖⁻¹ ^ m ≤ nM v b → (2 : ℝ) ^ m ≤ nu2 lam L₁ L₂ b := by
  classical
  obtain ⟨ε, hε, hsub⟩ := exists_ballV_subset (v := v) (U := (L₂ : Set (Fin n → Fv F v ⊗[F] E)))
    (h2.1.mem_nhds L₂.zero_mem)
  obtain ⟨ρ, hρ⟩ := exists_bound_nV (v := v) h1.2
  set C := nA v (1 : Fv F v ⊗[F] E) with hC
  have hC0 : 0 ≤ C := nA_nonneg _
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : (0 : ℝ) < C + 1)) hϖ1
  set t0 : Fv F v := ϖ ^ N with ht0
  have ht0n : ‖t0‖ = ‖ϖ‖ ^ N := norm_pow _ _
  have ht0p : 0 < ‖t0‖ := by rw [ht0n]; exact pow_pos hϖ0 _
  have ht0C : ‖t0‖ * C ≤ ε := by
    rw [ht0n]
    have h' : ‖ϖ‖ ^ N * (C + 1) < ε := (lt_div_iff₀ (by linarith)).1 hN
    nlinarith [pow_pos hϖ0 N]
  refine ⟨(|ρ| + 1) / ‖t0‖, div_pos (by positivity) ht0p, fun m b hb hR => ?_⟩
  have hq : 0 < ‖ϖ‖⁻¹ ^ m := pow_pos (inv_pos.2 hϖ0) _
  have hbpos : 0 < nM v b := lt_of_lt_of_le (mul_pos (div_pos (by positivity) ht0p) hq) hR
  obtain ⟨i, k, hik⟩ := exists_entry_ge (v := v) b hbpos
  set e : Fin n → Fv F v ⊗[F] E := Pi.single k 1 with he
  set w : Fin n → Fv F v ⊗[F] E := b.mulVec e with hw
  have hwi : nM v b ≤ nV v w := by
    refine hik.trans ?_
    have : w i = b i k := by rw [hw, he, Matrix.mulVec_single_one]; rfl
    rw [← this]; exact nA_le_nV _ _
  let y : (Fin m → Bool) → Fin n → Fv F v ⊗[F] E := fun δ => (digits ϖ m δ * t0) • e
  have hy : ∀ δ, y δ ∈ L₂ := by
    intro δ
    apply hsub
    show nV v ((digits ϖ m δ * t0) • e) ≤ ε
    rw [nV_smul, norm_mul]
    calc ‖digits ϖ m δ‖ * ‖t0‖ * nV v e ≤ 1 * ‖t0‖ * C := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (norm_digits_le hϖ1.le m δ) (norm_nonneg _))
            (nV_single_le k) (by unfold nV; exact norm_nonneg _) (by positivity)
      _ ≤ ε := by rw [one_mul]; exact ht0C
  have hsep : ∀ δ δ', δ ≠ δ' → b.mulVec (y δ) - b.mulVec (y δ') ∉ L₁ := by
    intro δ δ' hne hmem
    have hval : b.mulVec (y δ) - b.mulVec (y δ') = ((digits ϖ m δ - digits ϖ m δ') * t0) • w := by
      simp only [y, Matrix.mulVec_smul, hw, ← sub_smul, ← sub_mul]
    have h3 := hρ _ hmem
    rw [hval, nV_smul, norm_mul] at h3
    have h4 : ‖ϖ‖ ^ m * ‖t0‖ * ((|ρ| + 1) / ‖t0‖ * ‖ϖ‖⁻¹ ^ m) ≤
        ‖digits ϖ m δ - digits ϖ m δ'‖ * ‖t0‖ * nV v w := by
      gcongr
      · exact digits_sep hϖ1 m δ δ' hne
      · exact hR.trans hwi
    have h5 : ‖ϖ‖ ^ m * ‖t0‖ * ((|ρ| + 1) / ‖t0‖ * ‖ϖ‖⁻¹ ^ m) = |ρ| + 1 := by
      rw [inv_pow]
      field_simp
    rw [h5] at h4
    have := le_abs_self ρ
    linarith
  have := card_le_lattice_norm lam h1 b hb y hy hsep
  simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using this

theorem cvSigR_smul (σ : E →ₐ[F] E) (t : Fv F v) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (t • x) = t • sigR (Fv F v) σ x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp [sigR, Algebra.TensorProduct.map_tmul]

theorem smul_mem_herm (σ : E →ₐ[F] E) (t : Fv F v) {S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (hS : S ∈ HermR (Fv F v) σ n) : t • S ∈ HermR (Fv F v) σ n := by
  have hS' : ∀ a b, sigR (Fv F v) σ (S b a) = S a b := hS
  show ∀ a b, sigR (Fv F v) σ ((t • S) b a) = (t • S) a b
  intro a b
  simp only [Matrix.smul_apply]
  rw [cvSigR_smul, hS' a b]

def scH (σ : E →ₐ[F] E) (n : ℕ) {t : Fv F v} (ht : t ≠ 0) : HermR (Fv F v) σ n ≃+ HermR (Fv F v) σ n where
  toFun b := ⟨t • b.1, smul_mem_herm σ t b.2⟩
  invFun b := ⟨t⁻¹ • b.1, smul_mem_herm σ t⁻¹ b.2⟩
  left_inv b := Subtype.ext (by simp [smul_smul, inv_mul_cancel₀ ht])
  right_inv b := Subtype.ext (by simp [smul_smul, mul_inv_cancel₀ ht])
  map_add' a b := Subtype.ext (by simp [smul_add])

theorem scH_val (σ : E →ₐ[F] E) {t : Fv F v} (ht : t ≠ 0) (b : HermR (Fv F v) σ n) :
    (scH σ n ht b).1 = t • b.1 := rfl

theorem continuous_scH (σ : E →ₐ[F] E) {t : Fv F v} (ht : t ≠ 0) : Continuous (scH σ n ht) :=
  Continuous.subtype_mk (continuous_subtype_val.const_smul t) _

theorem continuous_scH_symm (σ : E →ₐ[F] E) {t : Fv F v} (ht : t ≠ 0) : Continuous (scH σ n ht).symm :=
  Continuous.subtype_mk (continuous_subtype_val.const_smul t⁻¹) _

instance secondCountable_HermCv (σ : E →ₐ[F] E) (n : ℕ) : SecondCountableTopology (HermR (Fv F v) σ n) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Fv F v ⊗[F] E))
  TopologicalSpace.Subtype.secondCountableTopology _

theorem exists_scale (σ : E →ₐ[F] E) (n : ℕ) (ν : Measure (HermR (Fv F v) σ n)) [ν.IsAddHaarMeasure]
    {t : Fv F v} (ht : t ≠ 0) :
    ∃ k : ℝ≥0, ∀ A, MeasurableSet A → ν ((scH σ n ht) ⁻¹' A) = k * ν A := by
  haveI : (ν.map (scH σ n ht)).IsAddHaarMeasure :=
    (scH σ n ht).isAddHaarMeasure_map ν (continuous_scH σ ht) (continuous_scH_symm σ ht)
  refine ⟨Measure.addHaarScalarFactor (ν.map (scH σ n ht)) ν, fun A hA => ?_⟩
  have hk := Measure.isAddLeftInvariant_eq_smul (ν.map (scH σ n ht)) ν
  have := congrArg (fun μ : Measure (HermR (Fv F v) σ n) => μ A) hk
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
  rw [← Measure.map_apply (continuous_scH σ ht).measurable hA]
  exact this

end PositivityTheory.SiegelWeilFormula.SwLocFin.LatticeCovolumeGrowth

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open PositivityTheory.SiegelWeilFormula.SwLocFin.LatticeCovolumeGrowth
open scoped TensorProduct Matrix ENNReal NNReal

theorem convP : ConvP := by
  intro F E _ _ _ _ _ σ M J n ψ v μv νv lam L₁ L₂ Φv g T h
  haveI : lam.IsAddHaarMeasure := h.haar
  haveI : νv.IsAddHaarMeasure := h.sdH.1
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_norm_lt_one (F := F) v
  have hϖne : ϖ ≠ 0 := norm_pos_iff.1 hϖ0
  obtain ⟨R₀, hR₀, hKL⟩ := exists_lattice_norm_ge_pow hϖ0 hϖ1 lam h.co₁ h.co₂
  obtain ⟨k, hk⟩ := exists_scale σ n νv hϖne
  obtain ⟨C, hC⟩ := uu_bound h
  have hnu1 := lattice_norm_ge_one h
  set q : ℝ := ‖ϖ‖⁻¹ with hq
  have hq1 : 1 < q := (one_lt_inv₀ hϖ0).2 hϖ1
  set V := νv {b : HermR (Fv F v) σ n | nM v b.1 ≤ R₀} with hVdef
  have hV : V ≠ ⊤ := (isCompact_ballH R₀).measure_lt_top.ne
  have hstep : ∀ r : ℝ, νv {b : HermR (Fv F v) σ n | nM v b.1 ≤ r * q} =
      k * νv {b : HermR (Fv F v) σ n | nM v b.1 ≤ r} := by
    intro r
    rw [← hk _ (measurableSet_ballH r)]
    refine congrArg νv (Set.ext fun b => ?_)
    show nM v b.1 ≤ r * q ↔ nM v (scH σ n hϖne b).1 ≤ r
    have hs : nM v (scH σ n hϖne b).1 = ‖ϖ‖ * nM v b.1 := by
      rw [scH_val]; exact nM_smul ϖ b.1
    rw [hs, hq, ← div_eq_mul_inv, le_div_iff₀ hϖ0, mul_comm]
  have hball : ∀ j : ℕ, νv {b : HermR (Fv F v) σ n | nM v b.1 ≤ R₀ * q ^ j} = (k : ℝ≥0∞) ^ j * V := by
    intro j
    induction j with
    | zero => simp only [pow_zero, mul_one, one_mul]; exact hVdef.symm
    | succ j ih => rw [pow_succ, ← mul_assoc, hstep, ih, pow_succ]; ring
  set σs : ℝ := Real.logb 2 (2 * k + 2) with hσs
  have hσs0 : 0 ≤ σs := Real.logb_nonneg one_lt_two (by linarith [NNReal.coe_nonneg k])
  refine ⟨((M : ℝ) - n) / 2 + σs, fun z hz => ?_⟩
  set s : ℝ := z.re - ((M : ℝ) - n) / 2 with hs
  have hsσ : σs < s := by rw [hs]; linarith
  have hs0 : 0 ≤ s := by linarith
  have h2s : 2 * (k : ℝ) + 2 ≤ 2 ^ s := by
    calc 2 * (k : ℝ) + 2 = 2 ^ σs := (Real.rpow_logb two_pos (by norm_num) (by positivity)).symm
      _ ≤ 2 ^ s := Real.rpow_le_rpow_of_exponent_le one_le_two hsσ.le
  set r : ℝ := (2 : ℝ) ^ (-s) with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hrk : r * k < 1 := by
    have h2pos : 0 < (2 : ℝ) ^ s := by positivity
    rw [hrdef, Real.rpow_neg zero_le_two, inv_mul_eq_div, div_lt_one h2pos]
    linarith [NNReal.coe_nonneg k]
  set H : HermR (Fv F v) σ n → ℝ := fun b => nu2 lam L₁ L₂ b.1 ^ (-s) with hH
  have hHc : Continuous H := (continuous_lattice_norm h).rpow_const fun b => Or.inl (by linarith [hnu1 b])
  have hH0 : ∀ b, 0 ≤ H b := fun b => Real.rpow_nonneg (by linarith [hnu1 b]) _
  have hH1 : ∀ b, H b ≤ 1 := fun b => Real.rpow_le_one_of_one_le_of_nonpos (hnu1 b) (by linarith)
  set A : ℕ → Set (HermR (Fv F v) σ n) :=
    fun j => {b | R₀ * q ^ j ≤ nM v b.1 ∧ nM v b.1 ≤ R₀ * q ^ (j + 1)} with hA
  have hm : Measurable fun b : HermR (Fv F v) σ n => nM v b.1 :=
    (show Continuous fun b : HermR (Fv F v) σ n => nM v b.1 from continuous_nM.comp continuous_subtype_val).measurable
  have hAm : ∀ j, MeasurableSet (A j) := fun j =>
    (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)
  have hHA : ∀ j, ∀ b ∈ A j, H b ≤ r ^ j := by
    intro j b hb
    have h2 : (2 : ℝ) ^ j ≤ nu2 lam L₁ L₂ b.1 := hKL j b.1 (hnu1 b) hb.1
    calc H b ≤ ((2 : ℝ) ^ j) ^ (-s) := Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
      _ = r ^ j := by
        rw [hrdef, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two,
          ← Real.rpow_mul zero_le_two, mul_comm]
  have hcov : (Set.univ : Set (HermR (Fv F v) σ n)) ⊆ {b | nM v b.1 ≤ R₀} ∪ ⋃ j, A j := by
    intro b _
    by_cases hb : nM v b.1 ≤ R₀
    · exact Or.inl hb
    · push_neg at hb
      obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near (x := nM v b.1 / R₀) (y := q) ((one_le_div hR₀).2 hb.le) hq1
      refine Or.inr (Set.mem_iUnion.2 ⟨j, ?_, ?_⟩)
      · rw [mul_comm]; exact (le_div_iff₀ hR₀).1 hj1
      · rw [mul_comm]; exact ((div_lt_iff₀ hR₀).1 hj2).le
  have hBint : ∫⁻ b in {b : HermR (Fv F v) σ n | nM v b.1 ≤ R₀}, ENNReal.ofReal (H b) ∂νv ≤ V := by
    calc _ ≤ ∫⁻ _ in {b : HermR (Fv F v) σ n | nM v b.1 ≤ R₀}, 1 ∂νv :=
          lintegral_mono fun b => ENNReal.ofReal_le_one.2 (hH1 b)
      _ = V := by rw [setLIntegral_const, one_mul]
  have hAint : ∀ j, ∫⁻ b in A j, ENNReal.ofReal (H b) ∂νv ≤ (k : ℝ≥0∞) * V * ENNReal.ofReal (r * k) ^ j := by
    intro j
    calc ∫⁻ b in A j, ENNReal.ofReal (H b) ∂νv ≤ ∫⁻ _ in A j, ENNReal.ofReal (r ^ j) ∂νv :=
          lintegral_mono_ae (ae_restrict_of_forall_mem (hAm j) fun b hb => ENNReal.ofReal_le_ofReal (hHA j b hb))
      _ = ENNReal.ofReal (r ^ j) * νv (A j) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (r ^ j) * ((k : ℝ≥0∞) ^ (j + 1) * V) := by
          gcongr
          rw [← hball (j + 1)]
          exact measure_mono fun b hb => hb.2
      _ = (k : ℝ≥0∞) * V * ENNReal.ofReal (r * k) ^ j := by
          rw [ENNReal.ofReal_pow hr0, ENNReal.ofReal_mul hr0, ENNReal.ofReal_coe_nnreal]; ring
  have hx : ENNReal.ofReal (r * k) < 1 := by rw [ENNReal.ofReal_lt_one]; exact hrk
  have hHint : Integrable H νv := by
    refine ⟨hHc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hH0)]
    calc ∫⁻ b, ENNReal.ofReal (H b) ∂νv = ∫⁻ b in Set.univ, ENNReal.ofReal (H b) ∂νv := by rw [Measure.restrict_univ]
      _ ≤ ∫⁻ b in {b | nM v b.1 ≤ R₀} ∪ ⋃ j, A j, ENNReal.ofReal (H b) ∂νv := lintegral_mono_set hcov
      _ ≤ ∫⁻ b in {b : HermR (Fv F v) σ n | nM v b.1 ≤ R₀}, ENNReal.ofReal (H b) ∂νv +
            ∫⁻ b in ⋃ j, A j, ENNReal.ofReal (H b) ∂νv := lintegral_union_le _ _ _
      _ ≤ ∫⁻ b in {b : HermR (Fv F v) σ n | nM v b.1 ≤ R₀}, ENNReal.ofReal (H b) ∂νv +
            ∑' j, ∫⁻ b in A j, ENNReal.ofReal (H b) ∂νv := add_le_add le_rfl (lintegral_iUnion_le _ _)
      _ ≤ V + ∑' j, (k : ℝ≥0∞) * V * ENNReal.ofReal (r * k) ^ j := add_le_add hBint (ENNReal.tsum_le_tsum hAint)
      _ = V + (k : ℝ≥0∞) * V * (1 - ENNReal.ofReal (r * k))⁻¹ := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hV.lt_top, ENNReal.mul_lt_top
          (ENNReal.mul_lt_top ENNReal.coe_lt_top hV.lt_top) (ENNReal.inv_lt_top.2 (tsub_pos_iff_lt.2 hx))⟩
  have hf : whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z =
      fun b => ((nu2 lam L₁ L₂ b.1 : ℝ) : ℂ) ^ (-(z - ((M : ℂ) - n) / 2)) * uu σ J ψ v μv Φv T b := by
    funext b; simp only [whI, uu, mul_assoc]
  rw [hf]
  refine (hHint.const_mul C).mono' ?_ (Eventually.of_forall fun b => ?_)
  · exact (((Complex.continuous_ofReal.comp (continuous_lattice_norm h)).cpow continuous_const fun b =>
      Complex.ofReal_mem_slitPlane.2 (by linarith [hnu1 b])).mul (continuous_uu h)).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hnu1 b])]
    have hre : (-(z - ((M : ℂ) - n) / 2)).re = -s := by
      rw [hs]; simp [Complex.sub_re, Complex.div_ofNat_re]
    rw [hre, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC b) (hH0 b)

end PositivityTheory.SiegelWeilFormula.SwLocFin
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.LocFin2OfX
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.DifferentiableSetIntegralFz
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open MeasureTheory Filter Topology Set

variable {H : Type*} [MeasurableSpace H]

def fz (r : H → ℝ) (u : H → ℂ) (s₀ z : ℂ) (b : H) : ℂ := (r b : ℂ) ^ (-(z - s₀)) * u b

theorem norm_cpow_le {x : ℝ} (hx : 1 ≤ x) {R : ℝ} (hR : x ≤ R) (w : ℂ) :
    ‖(x : ℂ) ^ w‖ ≤ R ^ max w.re 0 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  calc x ^ w.re ≤ x ^ max w.re 0 := Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
    _ ≤ R ^ max w.re 0 := Real.rpow_le_rpow (by linarith) hR (le_max_right _ _)

theorem integrableOn_fz {ν : Measure H} {r : H → ℝ} {u : H → ℂ} {s₀ : ℂ} (hr1 : ∀ b, 1 ≤ r b) (hrm : Measurable r)
    (hum : AEStronglyMeasurable u ν) {C : ℝ} (hub : ∀ b, ‖u b‖ ≤ C) {S : Set H} (hS : MeasurableSet S)
    (hSf : ν S < ⊤) {Rm : ℝ} (hRm : ∀ b ∈ S, r b ≤ Rm) (z : ℂ) : IntegrableOn (fz r u s₀ z) S ν := by
  have hmeas : Measurable fun b => (r b : ℂ) ^ (-(z - s₀)) :=
    (Complex.measurable_ofReal.comp hrm).pow_const _
  refine Measure.integrableOn_of_bounded (M := Rm ^ max (-(z - s₀)).re 0 * C) hSf.ne
    (hmeas.aestronglyMeasurable.mul hum) ?_
  filter_upwards [ae_restrict_mem hS] with b hb
  show ‖(r b : ℂ) ^ (-(z - s₀)) * u b‖ ≤ Rm ^ max (-(z - s₀)).re 0 * C
  rw [norm_mul]
  exact mul_le_mul (PositivityTheory.SiegelWeilFormula.SwLocFin.norm_cpow_le (hr1 b) (hRm b hb) _) (hub b)
    (norm_nonneg _) (Real.rpow_nonneg (by linarith [hr1 b, hRm b hb]) _)

theorem differentiable_setIntegral_fz {ν : Measure H} {r : H → ℝ} {u : H → ℂ} {s₀ : ℂ} (hr1 : ∀ b, 1 ≤ r b)
    (hrm : Measurable r) (hum : AEStronglyMeasurable u ν) {C : ℝ} (hub : ∀ b, ‖u b‖ ≤ C) {S : Set H}
    (hS : MeasurableSet S) (hSf : ν S < ⊤) {Rm : ℝ} (hRm : ∀ b ∈ S, r b ≤ Rm) :
    Differentiable ℂ (fun z => ∫ b in S, fz r u s₀ z b ∂ν) := by
  intro z₀
  haveI : IsFiniteMeasure (ν.restrict S) := isFiniteMeasure_restrict.mpr hSf.ne
  have hofr : Measurable fun b => (r b : ℂ) := Complex.measurable_ofReal.comp hrm
  have hmeas : ∀ z : ℂ, Measurable fun b => (r b : ℂ) ^ (-(z - s₀)) := fun z => hofr.pow_const _
  set R' := max Rm 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right _ _
  have hR'0 : 0 ≤ R' := by linarith
  set E := max (s₀.re - z₀.re + 1) 0 with hE
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν.restrict S)
    (F := fun z b => PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b)
    (F' := fun z b => -(Complex.log (r b) * (r b : ℂ) ^ (-(z - s₀)) * u b))
    (bound := fun _ => R' * R' ^ E * C) (x₀ := z₀)
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => ((hmeas z).aestronglyMeasurable.mul hum).restrict)
    (PositivityTheory.SiegelWeilFormula.SwLocFin.integrableOn_fz hr1 hrm hum hub hS hSf hRm z₀)
    ((((Complex.measurable_log.comp hofr).mul (hmeas z₀)).aestronglyMeasurable.mul hum).neg.restrict)
    ?_ (integrable_const _) ?_
  · exact key.2.differentiableAt
  · filter_upwards [ae_restrict_mem hS] with b hb z hz
    show ‖-(Complex.log (r b) * (r b : ℂ) ^ (-(z - s₀)) * u b)‖ ≤ R' * R' ^ E * C
    have hb1 := hr1 b
    have hbR : r b ≤ R' := (hRm b hb).trans (le_max_left _ _)
    have hlog : ‖Complex.log (r b)‖ ≤ R' := by
      rw [← Complex.ofReal_log (by linarith), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg hb1)]
      linarith [Real.log_le_sub_one_of_pos (show 0 < r b by linarith)]
    have hre : (-(z - s₀)).re ≤ s₀.re - z₀.re + 1 := by
      have h1 : dist z z₀ < 1 := Metric.mem_ball.mp hz
      rw [Complex.dist_eq] at h1
      have h2 := Complex.abs_re_le_norm (z - z₀)
      rw [Complex.sub_re, abs_le] at h2
      rw [Complex.neg_re, Complex.sub_re]
      linarith [h2.1]
    have hcp : ‖(r b : ℂ) ^ (-(z - s₀))‖ ≤ R' ^ E :=
      (PositivityTheory.SiegelWeilFormula.SwLocFin.norm_cpow_le hb1 hbR _).trans
        (Real.rpow_le_rpow_of_exponent_le hR'1 (max_le_max hre le_rfl))
    rw [norm_neg, norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul hlog hcp (norm_nonneg _) hR'0) (hub b) (norm_nonneg _)
      (mul_nonneg hR'0 (Real.rpow_nonneg hR'0 _))
  · refine Eventually.of_forall fun b z _ => ?_
    have hne : (r b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hr1 b])
    have h0 := (((hasDerivAt_id' z).sub_const s₀).neg.const_cpow (c := (r b : ℂ)) (Or.inl hne)).mul_const (u b)
    show HasDerivAt (fun x => (r b : ℂ) ^ (-(x - s₀)) * u b)
      (-(Complex.log (r b) * (r b : ℂ) ^ (-(z - s₀)) * u b)) z
    have e : (r b : ℂ) ^ (-(z - s₀)) * Complex.log (r b) * -1 * u b =
        -(Complex.log (r b) * (r b : ℂ) ^ (-(z - s₀)) * u b) := by ring
    exact h0.congr_deriv e

theorem core (ν : Measure H) (r : H → ℝ) (u : H → ℂ) (s₀ w₀ : ℂ) (B : ℕ → Set H)
    (hBm : ∀ j, MeasurableSet (B j)) (hmono : Monotone B) (hcov : ⋃ j, B j = univ)
    (hfin : ∀ j, ν (B j) < ⊤) (hr1 : ∀ b, 1 ≤ r b) (hrm : Measurable r) (hrb : ∀ j, ∃ Rm, ∀ b ∈ B j, r b ≤ Rm)
    (hum : AEStronglyMeasurable u ν) (hub : ∃ C, ∀ b, ‖u b‖ ≤ C)
    (hshell : ∀ z j, ∫ b in B (j + 1) \ B j, fz r u s₀ z b ∂ν = 0)
    (hint : ∃ t : ℝ, ∀ z : ℂ, t < z.re → Integrable (fz r u s₀ z) ν)
    (hval : Tendsto (fun j => ∫ b in B j, u b ∂ν) atTop (𝓝 w₀)) :
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ W s₀ = w₀ ∧ ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (fz r u s₀ z) ν ∧ W z = ∫ b, fz r u s₀ z b ∂ν := by
  obtain ⟨C, hC⟩ := hub
  have hon : ∀ z j, IntegrableOn (PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z) (B j) ν := fun z j => by
    obtain ⟨Rm, hRm⟩ := hrb j
    exact PositivityTheory.SiegelWeilFormula.SwLocFin.integrableOn_fz hr1 hrm hum hC (hBm j) (hfin j) hRm z
  have hG : ∀ z j, ∫ b in B j, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν =
      ∫ b in B 0, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν := by
    intro z j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← ih]
      have hsub : B j ⊆ B (j + 1) := hmono (Nat.le_succ j)
      rw [← Set.union_diff_cancel hsub, setIntegral_union Set.disjoint_sdiff_right
        ((hBm _).diff (hBm _)) (hon z j) ((hon z (j + 1)).mono_set diff_subset), hshell, add_zero]
  obtain ⟨R0, hR0⟩ := hrb 0
  refine ⟨fun z => ∫ b in B 0, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν,
    PositivityTheory.SiegelWeilFormula.SwLocFin.differentiable_setIntegral_fz hr1 hrm hum hC (hBm 0) (hfin 0) hR0, ?_, ?_⟩
  · have hfs : ∀ j, ∫ b in B j, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ s₀ b ∂ν = ∫ b in B j, u b ∂ν := by
      intro j
      simp only [PositivityTheory.SiegelWeilFormula.SwLocFin.fz, sub_self, neg_zero, Complex.cpow_zero, one_mul]
    have e : (fun j => ∫ b in B j, u b ∂ν) =
        fun _ => ∫ b in B 0, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ s₀ b ∂ν := by
      funext j
      rw [← hfs j, hG]
    rw [e] at hval
    exact tendsto_nhds_unique tendsto_const_nhds hval
  · obtain ⟨t, ht⟩ := hint
    refine ⟨t, fun z hz => ⟨ht z hz, ?_⟩⟩
    have hlim := tendsto_setIntegral_of_monotone hBm hmono (ht z hz).integrableOn
    rw [hcov, Measure.restrict_univ] at hlim
    have e : (fun j => ∫ b in B j, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν) =
        fun _ => ∫ b in B 0, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν := funext (hG z)
    rw [e] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim

end PositivityTheory.SiegelWeilFormula.SwLocFin
end
end

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct Matrix

theorem whI_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (lam : Measure (Fin n → Fv F v ⊗[F] E))
    (L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)) (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (T : HermR (Fv F v) σ n) (z : ℂ) (b : HermR (Fv F v) σ n) :
    whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z b =
      fz (fun b : HermR (Fv F v) σ n => nu2 lam L₁ L₂ b.1) (uu σ J ψ v μv Φv T) (((M : ℂ) - n) / 2) z b := by
  simp only [whI, fz, uu, mul_assoc]

theorem locFinX_of (hS : ShellP) (hC : ConvP) (hD : DualP) : LocFinX := by
  intro F E _ _ _ _ _ σ hcm M J hJ n ψ hψ v μv νv lam L₁ L₂ hμ hν hlam h₁ h₂ Φv hΦ g hg T hT
  have h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T := ⟨hcm, hJ, hψ, hμ, hν, hlam, h₁, h₂, hΦ, hg, hT⟩
  haveI : νv.IsAddHaarMeasure := hν.1
  obtain ⟨R₀, hR₀⟩ := hS F E σ M J n ψ v μv νv lam L₁ L₂ Φv g T h 2 one_lt_two
  set R₁ : ℝ := max R₀ 1 with hR₁
  have hR₁pos : 0 < R₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set B : ℕ → Set (HermR (Fv F v) σ n) := fun j => {b | nM v b.1 ≤ R₁ * 2 ^ j} with hB
  have hWeq : ∀ z, whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z =
      fz (fun b : HermR (Fv F v) σ n => nu2 lam L₁ L₂ b.1) (uu σ J ψ v μv Φv T) (((M : ℂ) - n) / 2) z :=
    fun z => funext fun b => whI_eq σ J ψ v μv lam L₁ L₂ Φv T z b
  obtain ⟨W, hWd, hW0, t, hWt⟩ := core νv (fun b : HermR (Fv F v) σ n => nu2 lam L₁ L₂ b.1) (uu σ J ψ v μv Φv T)
    (((M : ℂ) - n) / 2) (g T) B
    (fun j => measurableSet_ballH _)
    (fun i j hij => by
      intro b hb
      simp only [hB, Set.mem_setOf_eq] at hb ⊢
      exact hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_two hij) hR₁pos.le))
    (by
      refine Set.eq_univ_of_forall fun b => ?_
      obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (nM v b.1 / R₁) one_lt_two
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      simp only [hB, Set.mem_setOf_eq]
      rw [div_lt_iff₀ hR₁pos] at hj
      linarith)
    (fun j => (isCompact_ballH _).measure_lt_top)
    (lattice_norm_ge_one h)
    (continuous_lattice_norm h).measurable
    (fun j => by
      obtain ⟨C, hC⟩ := (isCompact_ballH (σ := σ) (n := n) (v := v) (R₁ * 2 ^ j)).exists_bound_of_continuousOn
        (continuous_lattice_norm h).continuousOn
      exact ⟨C, fun b hb => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC b hb)⟩)
    (continuous_uu h).aestronglyMeasurable
    (uu_bound h)
    (fun z j => by
      have hset : B (j + 1) \ B j = {b : HermR (Fv F v) σ n | R₁ * 2 ^ j < nM v b.1 ∧ nM v b.1 ≤ 2 * (R₁ * 2 ^ j)} := by
        ext b
        simp only [hB, Set.mem_diff, Set.mem_setOf_eq, not_le, pow_succ]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
      rw [hset, ← hWeq z]
      exact hR₀ _ ((le_max_left _ _).trans (le_mul_of_one_le_right hR₁pos.le (one_le_pow₀ one_le_two))) z)
    (by
      obtain ⟨t, ht⟩ := hC F E σ M J n ψ v μv νv lam L₁ L₂ Φv g T h
      exact ⟨t, fun z hz => by rw [← hWeq z]; exact ht z hz⟩)
    ((hD F E σ M J n ψ v μv νv lam L₁ L₂ Φv g T h).comp
      (Tendsto.const_mul_atTop hR₁pos (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)))
  refine ⟨W, hWd, hW0, t, fun z hz => ?_⟩
  rw [hWeq z]
  exact hWt z hz

theorem locFin2_of_X (h : LocFinX) : LocFin2 := by
  intro F E _ _ _ _ _ σ hcm M J hJ n _ ψ hψ v μv νv lam L₁ L₂ hμ hν hlam h₁ h₂ Φv hΦ g hg T hT
  exact h F E σ hcm M J hJ n ψ hψ v μv νv lam L₁ L₂ hμ hν hlam h₁ h₂ Φv hΦ g hg T hT

end PositivityTheory.SiegelWeilFormula.SwLocFin
end
end

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

theorem locFinX : PositivityTheory.SiegelWeilFormula.Gen.LocFinX := locFinX_of shellP convP dualP

theorem locFin2 : PositivityTheory.SiegelWeilFormula.Gen.LocFin2 := locFin2_of_X locFinX

end PositivityTheory.SiegelWeilFormula.SwLocFin
