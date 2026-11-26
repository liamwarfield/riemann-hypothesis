module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnimodularPlaneSplitAlongVector
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardUnimodularGluingsTwoLinesLe
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPositiveAdd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsShortVectorUnimodularHermitianLatticeRankT

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardRealGeneratedIdealsLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardAbsNormLePowPred
open NumberField Finset

namespace GlobalTheory.IdealBoundedNorm

theorem finite_setOf_absNorm_le (K : Type) [Field K] [NumberField K] (Y : ℝ) :
    {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}.Finite := by
  refine ((Finset.range (⌊Y⌋₊ + 1) : Set ℕ).toFinite.biUnion
    fun n _ => Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).subset ?_
  rintro I ⟨-, hI⟩
  refine Set.mem_biUnion (x := Ideal.absNorm I) ?_ rfl
  simpa [Nat.lt_succ_iff] using Nat.le_floor hI

theorem ncard_absNorm_le_pow_pred (K : Type) [Field K] [NumberField K] (Y : ℝ) (hY : 1 ≤ Y) :
    ((({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}).ncard : ℕ) : ℝ)
      ≤ Y * (1 + Real.log Y) ^ (Module.finrank ℚ K - 1) := by
  classical
  have hS := finite_setOf_absNorm_le K Y

  have key : ({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}).ncard
      ≤ ∑ n ∈ Ioc 0 ⌊Y⌋₊, (ArithmeticFunction.zeta ^ Module.finrank ℚ K : ArithmeticFunction ℕ) n := by
    rw [← hS.coe_toFinset, Set.ncard_coe_finset]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun I => Ideal.absNorm I) (t := Ioc 0 ⌊Y⌋₊) ?_]
    · refine Finset.sum_le_sum fun n hn => ?_
      refine le_trans ?_ (GlobalTheory.ncard_ideal_absNorm_eq_le K (Finset.mem_Ioc.1 hn).1.ne')
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard ?_ (Ideal.finite_setOfPred_absNorm_eq n)
      intro I hI
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hI ⊢
      exact hI.2
    · intro I hI
      simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq] at hI
      simp only [Finset.coe_Ioc, Set.mem_Ioc]
      exact ⟨Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 hI.1), Nat.le_floor hI.2⟩
  have hm : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  calc ((({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}).ncard : ℕ) : ℝ)
      ≤ ((∑ n ∈ Ioc 0 ⌊Y⌋₊,
          (ArithmeticFunction.zeta ^ Module.finrank ℚ K : ArithmeticFunction ℕ) n : ℕ) : ℝ) := by
        exact_mod_cast key
    _ ≤ Y * (1 + Real.log Y) ^ (Module.finrank ℚ K - 1) := GlobalTheory.sum_zeta_pow_le hm hY

theorem ncard_absNorm_le : ∀ (K : Type) [Field K] [NumberField K] (Y : ℝ), 1 ≤ Y →
    ((({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}).ncard : ℕ) : ℝ)
      ≤ Y * (1 + Real.log Y) ^ Module.finrank ℚ K := by
  intro K _ _ Y hY
  refine (ncard_absNorm_le_pow_pred K Y hY).trans ?_
  have hl : 1 ≤ 1 + Real.log Y := by linarith [Real.log_nonneg hY]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hl (Nat.sub_le _ _)) (by linarith)

end GlobalTheory.IdealBoundedNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardRealGeneratedIdealsLe
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.RealIdealCount

theorem eq_map_comap {E : Type} [Field E] [NumberField E] [StarRing E]
    (hs : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {𝔫 : Ideal (𝓞 E)}
    (h : 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t}) :
    𝔫 = (𝔫.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by
  refine le_antisymm ?_ Ideal.map_comap_le
  conv_lhs => rw [h]
  refine Ideal.span_le.mpr ?_
  rintro t ⟨ht, hst⟩
  have hreal : (t : E) ∈ maximalRealSubfield E := by
    intro φ
    have key := hs φ (t : E)
    rw [hst, starRingEnd_apply] at key
    exact key.symm
  have hint : IsIntegral ℤ (⟨(t : E), hreal⟩ : maximalRealSubfield E) := by
    have ht' : IsIntegral ℤ (t : E) := t.isIntegral_coe
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)
      (algebraMap (maximalRealSubfield E) E).injective).mp ht'
  let s : 𝓞 (maximalRealSubfield E) := ⟨⟨(t : E), hreal⟩, hint⟩
  have hs' : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s = t := by
    apply RingOfIntegers.ext
    rfl
  rw [← hs']
  refine Ideal.mem_map_of_mem _ ?_
  rw [Ideal.mem_comap, hs']
  exact ht

private theorem isCMField_of_star_compat {E : Type} [Field E] [NumberField E] [StarRing E]
    [hTC : _root_.NumberField.IsTotallyComplex E]
    (hs : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) : IsCMField E := by
  refine GlobalTheory.LeastExponentCompare.isCMField_of_conj E (fun z => star z)
    (fun φ z => by rw [hs, starRingEnd_apply]) ?_
  by_contra hne
  push_neg at hne
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  have hreal : w.IsReal := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext z
    simp only [ComplexEmbedding.conjugate_coe_eq]
    have := hs w.embedding z
    rw [hne z, starRingEnd_apply] at this
    exact this.symm
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w)) hreal

private theorem finrank_maximalRealSubfield_eq_fDeg (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Module.finrank ℚ (maximalRealSubfield E) = Formalism.HermitianLatticesTheory.fDeg E := by
  have h1 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E,
    IsTotallyComplex.finrank (K := E)] at h1
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
  rw [IsTotallyComplex.nrRealPlaces_eq_zero E, zero_add] at h2
  unfold Formalism.HermitianLatticesTheory.fDeg
  omega

theorem ncard_real_ideals_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ Y : ℝ, 1 ≤ Y → {𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2}.Finite ∧ (({𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2}.ncard : ℕ) : ℝ) ≤ Y * (1 + Real.log Y) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  intro E _ _ _ hE Y hY
  obtain ⟨hTC, hs, -⟩ := hE
  haveI := hTC
  haveI : IsCMField E := isCMField_of_star_compat hs
  set F := maximalRealSubfield E
  set S : Set (Ideal (𝓞 E)) := {𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧
    (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2} with hSdef
  set T : Set (Ideal (𝓞 F)) := {𝔞 : Ideal (𝓞 F) | 𝔞 ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ Y} with hTdef
  let g : Ideal (𝓞 E) → Ideal (𝓞 F) := fun 𝔫 => 𝔫.comap (algebraMap (𝓞 F) (𝓞 E))
  have hmap : ∀ 𝔫 ∈ S, 𝔫 = (g 𝔫).map (algebraMap (𝓞 F) (𝓞 E)) := fun 𝔫 h𝔫 =>
    eq_map_comap hs h𝔫.2.1
  have hdeg : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact Algebra.IsQuadraticExtension.finrank_eq_two F E
  have hinj : Set.InjOn g S := by
    intro 𝔫₁ h₁ 𝔫₂ h₂ heq
    rw [hmap 𝔫₁ h₁, hmap 𝔫₂ h₂, heq]
  have hmaps : Set.MapsTo g S T := by
    intro 𝔫 h𝔫
    have hn := hmap 𝔫 h𝔫
    refine ⟨?_, ?_⟩
    · intro hbot
      apply h𝔫.1
      rw [hn, hbot, Ideal.map_bot]
    · have hnorm : Ideal.absNorm 𝔫 = Ideal.absNorm (g 𝔫) ^ 2 := by
        conv_lhs => rw [hn]
        rw [Ideal.absNorm_algebraMap, hdeg]
      have hle := h𝔫.2.2
      rw [hnorm] at hle
      push_cast at hle
      exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by linarith) two_ne_zero).mp hle
  have hT : T.Finite := GlobalTheory.IdealBoundedNorm.finite_setOf_absNorm_le F Y
  refine ⟨Set.Finite.of_injOn hmaps hinj hT, ?_⟩
  have hcard : S.ncard ≤ T.ncard := Set.ncard_le_ncard_of_injOn g hmaps hinj hT
  have hTb := GlobalTheory.IdealBoundedNorm.ncard_absNorm_le F Y hY
  rw [finrank_maximalRealSubfield_eq_fDeg E] at hTb
  calc ((S.ncard : ℕ) : ℝ) ≤ (T.ncard : ℝ) := by exact_mod_cast hcard
    _ ≤ Y * (1 + Real.log Y) ^ Formalism.HermitianLatticesTheory.fDeg E := hTb

end GlobalTheory.RealIdealCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardRealGeneratedIdealsLeStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_realGenerated_ideals_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ Y : ℝ, 1 ≤ Y → {𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2}.Finite ∧ (({𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2}.ncard : ℕ) : ℝ) ≤ Y * (1 + Real.log Y) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  first | exact @GlobalTheory.RealIdealCount.ncard_real_ideals_le | exact GlobalTheory.RealIdealCount.ncard_real_ideals_le | (intros; apply GlobalTheory.RealIdealCount.ncard_real_ideals_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardRankOneHermitianLatticeClassesLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardRankOneHermitianLatticeClassesLe
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.RankOneClasses

open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [StarRing E]

omit [StarRing E] in
theorem ne_bot_of_isLattice {L : Submodule (𝓞 E) E} (h : Submodule.IsFullLattice E L) : L ≠ ⊥ := by
  intro hb
  let : Submodule.IsFullLattice E L := h
  have : Submodule.span E (L : Set E) = ⊤ := Submodule.IsFullLattice.span_eq_top
  rw [hb] at this
  simp at this

noncomputable def latUnit (L : Submodule (𝓞 E) E) (h : Submodule.IsFullLattice E L) :
    (FractionalIdeal (𝓞 E)⁰ E)ˣ :=
  Units.mk0 (⟨L, FractionalIdeal.isFractional_of_fg h.fg⟩ : FractionalIdeal (𝓞 E)⁰ E) (by
    intro h0
    exact ne_bot_of_isLattice h (FractionalIdeal.coeToSubmodule_eq_bot.mpr h0))

omit [StarRing E] in
theorem exists_scale {L M : Submodule (𝓞 E) E} (hL : Submodule.IsFullLattice E L)
    (hM : Submodule.IsFullLattice E M)
    (h : (QuotientGroup.mk (latUnit L hL) :
      (FractionalIdeal (𝓞 E)⁰ E)ˣ ⧸ (toPrincipalIdeal (𝓞 E) E).range) =
      QuotientGroup.mk (latUnit M hM)) :
    ∃ a : E, a ≠ 0 ∧ ∀ y, a * y ∈ M ↔ y ∈ L := by
  obtain ⟨a, ha⟩ := QuotientGroup.eq.mp h
  have h1 : latUnit M hM = toPrincipalIdeal (𝓞 E) E a * latUnit L hL := by
    rw [ha, mul_comm, mul_inv_cancel_left]
  have h2 : ((latUnit M hM : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (a : E) * (latUnit L hL : (FractionalIdeal (𝓞 E)⁰ E)ˣ) := by
    rw [h1, Units.val_mul, coe_toPrincipalIdeal]
  refine ⟨a, a.ne_zero, fun y => ?_⟩
  have h3 : (a : E) * y ∈ M ↔ (a : E) * y ∈
      ((latUnit M hM : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) := Iff.rfl
  rw [h3, h2, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨z, hz, he⟩
    rw [mul_left_cancel₀ a.ne_zero he]
    exact hz
  · intro hy
    exact ⟨y, hy, rfl⟩

def idealOf (β : E) (L : Submodule (𝓞 E) E) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {t | ∃ x ∈ L, ∃ y ∈ L, t = star x * β * y}

theorem idealOf_fg (β : E) {L : Submodule (𝓞 E) E} (h : Submodule.IsFullLattice E L) :
    (idealOf β L).FG := by
  obtain ⟨d, hd, hdL⟩ : IsFractional (𝓞 E)⁰ L := FractionalIdeal.isFractional_of_fg h.fg
  have hd0 : (d : E) ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hd
  have hs0 : star (d : E) ≠ 0 := by simpa using hd0
  have hle : idealOf β L ≤ Submodule.span (𝓞 E) {(star (d : E))⁻¹ * β * (d : E)⁻¹} := by
    refine Submodule.span_le.mpr ?_
    rintro t ⟨x, hx, y, hy, rfl⟩
    obtain ⟨p, hp⟩ := hdL x hx
    obtain ⟨q, hq⟩ := hdL y hy
    have hi : IsIntegral ℤ (star (p : E)) :=
      p.isIntegral_coe.map (starRingEnd E).toIntAlgHom
    let p' : 𝓞 E := ⟨star (p : E), hi⟩
    refine Submodule.mem_span_singleton.mpr ⟨p' * q, ?_⟩
    have hp' : (p : E) = d * x := hp
    have hq' : (q : E) = d * y := hq
    change (star (p : E) * (q : E)) * _ = _
    rw [hp', hq', star_mul']
    field_simp
  exact Submodule.FG.of_le (Submodule.fg_span_singleton _) hle

theorem idealOf_ne_bot {β : E} (hβ : β ≠ 0) {L : Submodule (𝓞 E) E}
    (h : Submodule.IsFullLattice E L) : idealOf β L ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff L).mp (ne_bot_of_isLattice h)
  refine (Submodule.ne_bot_iff _).mpr ⟨star x * β * x, Submodule.subset_span ⟨x, hx, x, hx, rfl⟩, ?_⟩
  simp [hx0, hβ]

theorem mul_mem_idealOf {β γ t a : E} {L M : Submodule (𝓞 E) E}
    (h : ∀ y ∈ L, a * y ∈ M) (ht : star a * γ * a = t * β) :
    ∀ z ∈ idealOf β L, t • z ∈ idealOf γ M := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    refine Submodule.subset_span ⟨a * x, h x hx, a * y, h y hy, ?_⟩
    rw [smul_eq_mul, star_mul']
    linear_combination (-(star x * y)) * ht
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

theorem exists_unit {β γ a : E} (hβ : β ≠ 0) (hγ : γ ≠ 0) {L M : Submodule (𝓞 E) E}
    (hL : Submodule.IsFullLattice E L) (ha : a ≠ 0) (h : ∀ y, a * y ∈ M ↔ y ∈ L)
    (hN : idealOf β L = idealOf γ M) :
    ∃ u : (𝓞 E)ˣ, star a * γ * a * ((u : 𝓞 E) : E) = β := by
  have hs : star a ≠ 0 := by simpa using ha
  have h1 : ∀ z ∈ idealOf β L, (star a * γ * a / β) • z ∈ idealOf β L := by
    intro z hz
    have := mul_mem_idealOf (γ := γ) (t := star a * γ * a / β) (fun y hy => (h y).mpr hy)
      (by field_simp) z hz
    rwa [← hN] at this
  have h2 : ∀ z ∈ idealOf β L, (β / (star a * γ * a)) • z ∈ idealOf β L := by
    intro z hz
    rw [hN] at hz
    exact mul_mem_idealOf (a := a⁻¹) (fun y hy => (h _).mp (by rwa [mul_inv_cancel_left₀ ha]))
      (by rw [star_inv₀]; field_simp) z hz
  have i1 := isIntegral_trans (R := ℤ) _ (isIntegral_of_smul_mem_submodule _ (idealOf_ne_bot hβ hL)
    (idealOf_fg β hL) _ h1)
  have i2 := isIntegral_trans (R := ℤ) _ (isIntegral_of_smul_mem_submodule _ (idealOf_ne_bot hβ hL)
    (idealOf_fg β hL) _ h2)
  refine ⟨⟨⟨_, i2⟩, ⟨_, i1⟩, ?_, ?_⟩, ?_⟩
  · apply RingOfIntegers.ext
    change β / (star a * γ * a) * (star a * γ * a / β) = 1
    field_simp
  · apply RingOfIntegers.ext
    change (star a * γ * a / β) * (β / (star a * γ * a)) = 1
    field_simp
  · change star a * γ * a * (β / (star a * γ * a)) = β
    field_simp

noncomputable def even_im_hermitian_sub (u : (𝓞 E)ˣ) : Fin (Units.rank E) → ZMod 2 :=
  fun i => (((Units.basisModTorsion E).repr (Additive.ofMul (u : (𝓞 E)ˣ ⧸ Units.torsion E)) i : ℤ) : ZMod 2)

omit [StarRing E] in
theorem exists_sq_of_parity {u w : (𝓞 E)ˣ} (h : even_im_hermitian_sub u = even_im_hermitian_sub w) :
    ∃ (ζ : (𝓞 E)ˣ) (v : (𝓞 E)ˣ), ζ ∈ Units.torsion E ∧ u = w * ζ * v ^ 2 := by
  have hd : ∀ i, ∃ k : ℤ,
      (Units.basisModTorsion E).repr (Additive.ofMul (u : (𝓞 E)ˣ ⧸ Units.torsion E)) i -
      (Units.basisModTorsion E).repr (Additive.ofMul (w : (𝓞 E)ˣ ⧸ Units.torsion E)) i = 2 * k := by
    intro i
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 2).mp (congrFun h i).symm
  choose k hk using hd
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective
    (Additive.toMul ((Units.basisModTorsion E).equivFun.symm k))
  have hv' : Additive.ofMul (v : (𝓞 E)ˣ ⧸ Units.torsion E) =
      (Units.basisModTorsion E).equivFun.symm k := by rw [hv]; rfl
  have he : Additive.ofMul (u : (𝓞 E)ˣ ⧸ Units.torsion E) =
      Additive.ofMul (w : (𝓞 E)ˣ ⧸ Units.torsion E) +
        (2 : ℤ) • Additive.ofMul (v : (𝓞 E)ˣ ⧸ Units.torsion E) := by
    apply (Units.basisModTorsion E).equivFun.injective
    rw [map_add (f := _), map_smul, hv', LinearEquiv.apply_symm_apply]
    funext i
    simp only [Module.Basis.equivFun_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hk i
  have he' : ((w * v ^ 2 : (𝓞 E)ˣ) : (𝓞 E)ˣ ⧸ Units.torsion E) = u := by
    apply Additive.ofMul.injective
    rw [he, QuotientGroup.mk_mul, QuotientGroup.mk_pow, ofMul_mul, ofMul_pow, two_nsmul, two_zsmul]
  refine ⟨(w * v ^ 2)⁻¹ * u, v, QuotientGroup.eq.mp he', ?_⟩
  rw [mul_right_comm, mul_inv_cancel_left]

theorem eq_of_norm_eq (φ : E →+* ℂ) (hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a)) {A B : E}
    (hA : star A = A) (hB : star B = B) (pA : 0 < (φ A).re) (pB : 0 < (φ B).re)
    (h : ‖φ A‖ = ‖φ B‖) : A = B := by
  apply φ.injective
  have a1 : ((φ A).re : ℂ) = φ A := Complex.conj_eq_iff_re.mp (by rw [← hφ, hA])
  have b1 : ((φ B).re : ℂ) = φ B := Complex.conj_eq_iff_re.mp (by rw [← hφ, hB])
  rw [← a1, ← b1, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg pA.le,
    Real.norm_of_nonneg pB.le] at h
  rw [← a1, ← b1, h]

theorem card_classes_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ N : Submodule (𝓞 E) E, ENat.card (Quot (fun X Y : {X : E × Submodule (𝓞 E) E // star X.1 = X.1 ∧ (∀ φ : E →+* ℂ, 0 < (φ X.1).re) ∧ Submodule.IsFullLattice E X.2 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ X.2, ∃ y ∈ X.2, t = star x * X.1 * y} = N} => ∃ c : E, c ≠ 0 ∧ star c * Y.1.1 * c = X.1.1 ∧ ∀ y, c * y ∈ Y.1.2 ↔ y ∈ X.1.2)) ≤ ((classNumber E * 2 ^ Formalism.HermitianLatticesTheory.fDeg E : ℕ) : ENat) := by
  intro E _ _ _ hE N
  classical
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hφ := hE.2.1 φ
  set S := {X : E × Submodule (𝓞 E) E // star X.1 = X.1 ∧ (∀ φ : E →+* ℂ, 0 < (φ X.1).re) ∧ Submodule.IsFullLattice E X.2 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ X.2, ∃ y ∈ X.2, t = star x * X.1 * y} = N} with hS
  have hne : ∀ X : S, X.1.1 ≠ 0 := by
    intro X h0
    have := X.2.2.1 φ
    rw [h0] at this
    simp at this
  let cls : S → (FractionalIdeal (𝓞 E)⁰ E)ˣ ⧸ (toPrincipalIdeal (𝓞 E) E).range :=
    fun X => QuotientGroup.mk (latUnit X.1.2 X.2.2.2.1)
  let base : S → S := fun X => Classical.choose (⟨X, rfl⟩ : ∃ B, cls B = cls X)
  have hbase : ∀ X, cls (base X) = cls X := fun X =>
    Classical.choose_spec (⟨X, rfl⟩ : ∃ B, cls B = cls X)
  have hbase' : ∀ X Y, cls X = cls Y → base X = base Y := by
    intro X Y h
    simp only [base, h]
  have hex : ∀ X : S, ∃ (a : E) (u : (𝓞 E)ˣ), a ≠ 0 ∧ (∀ y, a * y ∈ (base X).1.2 ↔ y ∈ X.1.2) ∧
      star a * (base X).1.1 * a * ((u : 𝓞 E) : E) = X.1.1 := by
    intro X
    obtain ⟨a, ha, h⟩ := exists_scale X.2.2.2.1 (base X).2.2.2.1 (hbase X).symm
    obtain ⟨u, hu⟩ := exists_unit (hne X) (hne (base X)) X.2.2.2.1 ha h
      (X.2.2.2.2.trans (base X).2.2.2.2.symm)
    exact ⟨a, u, ha, h, hu⟩
  choose a u ha hm hu using hex
  have key : ∀ X Y : S, cls X = cls Y → even_im_hermitian_sub (u X) = even_im_hermitian_sub (u Y) →
      ∃ c : E, c ≠ 0 ∧ star c * Y.1.1 * c = X.1.1 ∧ ∀ y, c * y ∈ Y.1.2 ↔ y ∈ X.1.2 := by
    intro X Y hc hp
    obtain ⟨ζ, v, hζ, hv⟩ := exists_sq_of_parity hp
    have hb := hbase' X Y hc
    have hv0 : ((v : 𝓞 E) : E) ≠ 0 := by simp
    have haY := ha Y
    have hsY : star (a Y) ≠ 0 := by simpa using haY
    have hc0 : a X * ((v : 𝓞 E) : E) / a Y ≠ 0 := div_ne_zero (mul_ne_zero (ha X) hv0) haY
    refine ⟨a X * ((v : 𝓞 E) : E) / a Y, hc0, ?_, fun y => ?_⟩
    · apply eq_of_norm_eq φ hφ _ X.2.1 _ (X.2.2.1 φ)
      · have e1 : star (a X * ((v : 𝓞 E) : E) / a Y) * Y.1.1 * (a X * ((v : 𝓞 E) : E) / a Y) =
            star (a X) * (base X).1.1 * a X * ((u Y : 𝓞 E) : E) *
              (star ((v : 𝓞 E) : E) * ((v : 𝓞 E) : E)) := by
          rw [← hu Y, hb, star_div₀, star_mul']
          field_simp
        have e2 : X.1.1 = star (a X) * (base X).1.1 * a X * ((u Y : 𝓞 E) : E) *
              (((ζ : 𝓞 E) : E) * (((v : 𝓞 E) : E) * ((v : 𝓞 E) : E))) := by
          rw [← hu X, hv]
          push_cast
          ring
        have e3 : ‖φ ((ζ : 𝓞 E) : E)‖ = 1 := by
          have := (Units.mem_torsion E).mp hζ (InfinitePlace.mk φ)
          rwa [InfinitePlace.apply] at this
        rw [e1, e2]
        simp only [map_mul, norm_mul, hφ, e3, Complex.norm_conj, one_mul]
      · rw [star_mul', star_mul', star_star, Y.2.1]; ring
      · have : φ (star (a X * ((v : 𝓞 E) : E) / a Y) * Y.1.1 * (a X * ((v : 𝓞 E) : E) / a Y)) =
            (Complex.normSq (φ (a X * ((v : 𝓞 E) : E) / a Y)) : ℂ) * φ Y.1.1 := by
          rw [map_mul, map_mul, hφ, Complex.normSq_eq_conj_mul_self]; ring
        rw [this, Complex.re_ofReal_mul]
        exact mul_pos (Complex.normSq_pos.mpr ((map_ne_zero φ).mpr hc0)) (Y.2.2.1 φ)
    · rw [← hm Y, ← hm X, hb]
      have : a Y * (a X * ((v : 𝓞 E) : E) / a Y * y) = v • (a X * y) := by
        change _ = ((v : 𝓞 E) : E) * _
        field_simp
      rw [this]
      exact Submodule.smul_mem_iff_of_isUnit _ v.isUnit
  let g : Quot (fun X Y : S => ∃ c : E, c ≠ 0 ∧ star c * Y.1.1 * c = X.1.1 ∧
      ∀ y, c * y ∈ Y.1.2 ↔ y ∈ X.1.2) → ClassGroup (𝓞 E) × (Fin (Units.rank E) → ZMod 2) :=
    fun q => ((ClassGroup.equiv E).symm (cls q.out), even_im_hermitian_sub (u q.out))
  have hg : Function.Injective g := by
    intro q r h
    rw [← q.out_eq, ← r.out_eq]
    exact Quot.sound (key _ _ ((ClassGroup.equiv E).symm.injective (congrArg Prod.fst h))
      (congrArg Prod.snd h))
  refine (ENat.card_le_card_of_injective hg).trans ?_
  rw [ENat.card_eq_coe_fintype_card, Nat.cast_le, Fintype.card_prod, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))

end GlobalTheory.RankOneClasses
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardRankOneHermitianLatticeClassesLeStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_rankOne_hermitian_lattice_classes_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ N : Submodule (𝓞 E) E, ENat.card (Quot (fun X Y : {X : E × Submodule (𝓞 E) E // star X.1 = X.1 ∧ (∀ φ : E →+* ℂ, 0 < (φ X.1).re) ∧ Submodule.IsFullLattice E X.2 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ X.2, ∃ y ∈ X.2, t = star x * X.1 * y} = N} => ∃ c : E, c ≠ 0 ∧ star c * Y.1.1 * c = X.1.1 ∧ ∀ y, c * y ∈ Y.1.2 ↔ y ∈ X.1.2)) ≤ ((classNumber E * 2 ^ Formalism.HermitianLatticesTheory.fDeg E : ℕ) : ENat) := by
  first | exact @GlobalTheory.RankOneClasses.card_classes_le | exact GlobalTheory.RankOneClasses.card_classes_le | (intros; apply GlobalTheory.RankOneClasses.card_classes_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassNumberLeMinkowskiCount
open NumberField

namespace GlobalTheory

theorem classNumber_le_minkowski_count :
    ∀ (K : Type) [Field K] [NumberField K], (classNumber K : ℝ) ≤
      Real.sqrt |(discr K : ℝ)| * (1 + Real.log (Real.sqrt |(discr K : ℝ)|)) ^ Module.finrank ℚ K :=
  fun K _ _ => classNumber_le_sqrt_discr_mul_pow K

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankTwoDefiniteUnimodularHermitianClassBound
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.RankTwoCount

theorem enat_card_sigma_le {α : Type*} {β : α → Type*} (a b : ℕ) (ha : ENat.card α ≤ a)
    (hb : ∀ i, ENat.card (β i) ≤ b) : ENat.card (Σ i, β i) ≤ ((a * b : ℕ) : ENat) := by
  classical
  haveI : Finite α := ENat.card_lt_top.1 (lt_of_le_of_lt ha (ENat.coe_lt_top a))
  haveI : ∀ i, Finite (β i) := fun i => ENat.card_lt_top.1 (lt_of_le_of_lt (hb i) (ENat.coe_lt_top b))
  haveI := Fintype.ofFinite α
  rw [ENat.card_eq_coe_natCard] at ha ⊢
  have ha' : Nat.card α ≤ a := by exact_mod_cast ha
  have hb' : ∀ i, Nat.card (β i) ≤ b := fun i => by
    have := hb i
    rw [ENat.card_eq_coe_natCard] at this
    exact_mod_cast this
  rw [Nat.card_sigma]
  have h1 : ∑ i, Nat.card (β i) ≤ Fintype.card α * b := by
    simpa using Finset.sum_le_card_nsmul Finset.univ (fun i => Nat.card (β i)) b (fun i _ => hb' i)
  rw [← Nat.card_eq_fintype_card] at h1
  exact_mod_cast h1.trans (Nat.mul_le_mul_right b ha')

theorem enat_card_le_of_rel {α β : Type*} (P : α → β → Prop) (h : ∀ a, ∃ b, P a b)
    (hu : ∀ a a' b, P a b → P a' b → a = a') : ENat.card α ≤ ENat.card β := by
  choose f hf using h
  exact ENat.card_le_card_of_injective (f := f) fun a a' e => hu a a' (f a) (hf a) (e ▸ hf a')

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def LineRel (X Y : E × Submodule (𝓞 E) E) : Prop :=
  ∃ c : E, c ≠ 0 ∧ star c * Y.1 * c = X.1 ∧ ∀ y, c * y ∈ Y.2 ↔ y ∈ X.2

theorem lineRel_equivalence : Equivalence (LineRel (E := E)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X
    exact ⟨1, one_ne_zero, by simp, by simp⟩
  · rintro X Y ⟨c, hc, h1, h2⟩
    have hs : star c ≠ 0 := by simpa using hc
    refine ⟨c⁻¹, inv_ne_zero hc, ?_, fun y => ?_⟩
    · rw [← h1, star_inv₀]; field_simp
    · rw [← h2, mul_inv_cancel_left₀ hc]
  · rintro X Y Z ⟨c, hc, h1, h2⟩ ⟨d, hd, k1, k2⟩
    refine ⟨d * c, mul_ne_zero hd hc, ?_, fun y => ?_⟩
    · rw [← h1, ← k1, star_mul]; ring
    · rw [← h2, ← k2, mul_assoc]

theorem lineRel_out {p : E × Submodule (𝓞 E) E → Prop} (Y : {X // p X}) :
    LineRel (Quot.out (Quot.mk (fun X Y : {X // p X} => LineRel X.1 Y.1) Y)).1 Y.1 := by
  have he : Equivalence (fun X Y : {X // p X} => LineRel X.1 Y.1) :=
    ⟨fun X => lineRel_equivalence.refl _, fun h => lineRel_equivalence.symm h,
      fun h k => lineRel_equivalence.trans h k⟩
  exact he.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq _))

theorem form_transport {r : ℕ} (J g : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    star y ⬝ᵥ ((gᴴ * J * g) *ᵥ x) = star (g *ᵥ y) ⬝ᵥ (J *ᵥ (g *ᵥ x)) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

def pull {r : ℕ} (γ : GL (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) : Submodule (𝓞 E) (Fin r → E) :=
  Λ.comap ((Matrix.mulVecLin (γ : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E))

theorem mem_pull {r : ℕ} (γ : GL (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (y : Fin r → E) :
    y ∈ pull γ Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ y ∈ Λ := Iff.rfl

theorem mulVec_inv_cancel {r : ℕ} (γ : GL (Fin r) E) (y : Fin r → E) :
    (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y) = y := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem inv_mulVec_cancel {r : ℕ} (γ : GL (Fin r) E) (y : Fin r → E) :
    ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = y := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem pull_isLattice {r : ℕ} (γ : GL (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (h : Submodule.IsLattice E Λ) : Submodule.IsLattice E (pull γ Λ) := by
  have hm : pull γ Λ = Λ.map ((Matrix.mulVecLin
      ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E)) := by
    ext y
    rw [mem_pull, Submodule.mem_map]
    constructor
    · intro hy
      exact ⟨_, hy, inv_mulVec_cancel γ y⟩
    · rintro ⟨x, hx, rfl⟩
      change (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x) ∈ Λ
      rwa [mulVec_inv_cancel]
  refine ⟨hm ▸ h.fg.map _, ?_⟩
  intro s hs hli
  exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem pull_unimodular {r : ℕ} (γ : GL (Fin r) E) (J : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E))
    (h : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) (x : Fin r → E) :
    x ∈ pull γ Λ ↔ ∀ y ∈ pull γ Λ, star y ⬝ᵥ (((γ : Matrix (Fin r) (Fin r) E)ᴴ * J *
      (γ : Matrix (Fin r) (Fin r) E)) *ᵥ x) ∈ (algebraMap (𝓞 E) E).range := by
  rw [mem_pull, h]
  constructor
  · intro H y hy
    rw [form_transport]
    exact H _ hy
  · intro H y hy
    have := H (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y)
      (by rw [mem_pull, mulVec_inv_cancel]; exact hy)
    rwa [form_transport, mulVec_inv_cancel] at this

theorem pull_pos {r : ℕ} (γ : GL (Fin r) E) (J : Matrix (Fin r) (Fin r) E)
    (h : ∀ (φ : E →+* ℂ) (y : Fin r → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (J *ᵥ y))).re)
    (φ : E →+* ℂ) (y : Fin r → E) (hy : y ≠ 0) :
    0 < (φ (star y ⬝ᵥ (((γ : Matrix (Fin r) (Fin r) E)ᴴ * J *
      (γ : Matrix (Fin r) (Fin r) E)) *ᵥ y))).re := by
  rw [form_transport]
  refine h φ _ fun h0 => hy ?_
  rw [← inv_mulVec_cancel γ y, h0, mulVec_zero]

noncomputable def diagGL (c d : E) (hc : c ≠ 0) (hd : d ≠ 0) : GL (Fin 2) E :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![c, d]) (by simp [Fin.prod_univ_two, hc, hd])

theorem diag_conj (c d b e : E) :
    (Matrix.diagonal ![c, d])ᴴ * Matrix.diagonal ![b, e] * Matrix.diagonal ![c, d] =
      Matrix.diagonal ![star c * b * c, star d * e * d] := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp

theorem diag_mulVec (c d s t : E) : Matrix.diagonal ![c, d] *ᵥ ![s, t] = ![c * s, d * t] := by
  ext i
  fin_cases i <;> simp [mulVec_diagonal]

abbrev Lines (N : Submodule (𝓞 E) E) : Type :=
  {X : E × Submodule (𝓞 E) E // star X.1 = X.1 ∧ (∀ φ : E →+* ℂ, 0 < (φ X.1).re) ∧
    Submodule.IsLattice E X.2 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ X.2, ∃ y ∈ X.2, t = star x * X.1 * y} = N}

abbrev LineCls (N : Submodule (𝓞 E) E) : Type := Quot (fun X Y : Lines N => LineRel X.1 Y.1)

abbrev Glued (X₁ X₂ : E × Submodule (𝓞 E) E) : Type :=
  {M : Submodule (𝓞 E) (Fin 2 → E) // Submodule.IsLattice E M ∧
    (∀ x, x ∈ M ↔ ∀ y ∈ M, star y ⬝ᵥ ((Matrix.diagonal ![X₁.1, X₂.1]) *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) ∧
    (∀ t, t ∈ X₁.2 ↔ ![t, 0] ∈ M) ∧ ∀ t, t ∈ X₂.2 ↔ ![0, t] ∈ M}


variable (E) in
def realIdeals (Y : ℝ) : Set (Ideal (𝓞 E)) :=
  {𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2}


variable (E) in
abbrev GlueData (Y : ℝ) : Type :=
  Σ 𝔫 : realIdeals E Y,
    Σ q₁ : LineCls (Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫.1),
      Σ q₂ : LineCls (Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫.1),
        Glued (Quot.out q₁).1 (Quot.out q₂).1

theorem card_glueData_le (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) (Y : ℝ) (hY : 1 ≤ Y) :
    ENat.card (GlueData E Y) ≤ (((realIdeals E Y).ncard * ((classNumber E * 2 ^ Formalism.HermitianLatticesTheory.fDeg E) *
      ((classNumber E * 2 ^ Formalism.HermitianLatticesTheory.fDeg E) * ⌊Y ^ 2⌋₊)) : ℕ) : ENat) := by
  have hline (𝔫 : realIdeals E Y) : ENat.card (LineCls (Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫.1)) ≤
      ((classNumber E * 2 ^ Formalism.HermitianLatticesTheory.fDeg E : ℕ) : ENat) := by
    let N := Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫.1
    have hN : N ≠ ⊥ := by
      intro h
      apply 𝔫.2.1
      apply Submodule.map_injective_of_injective (f := Algebra.linearMap (𝓞 E) E) (FaithfulSMul.algebraMap_injective (𝓞 E) E)
      simpa [N] using h
    have hfull (X : Lines N) : Submodule.IsFullLattice E X.1.2 := by
      have hne : X.1.2 ≠ ⊥ := by
        intro hbot
        apply hN
        rw [← X.2.2.2.2, hbot]
        simp
      obtain ⟨x, hx, hx0⟩ := X.1.2.ne_bot_iff.mp hne
      letI : Submodule.IsLattice E X.1.2 := X.2.2.2.1
      refine { span_eq_top := ?_ }
      apply top_unique
      intro y hy
      have hx' : x ∈ Submodule.span E (X.1.2 : Set E) := Submodule.subset_span hx
      have := (Submodule.span E (X.1.2 : Set E)).smul_mem (y * x⁻¹) hx'
      simpa [smul_eq_mul, mul_assoc, hx0] using this
    let FullLines := {X : E × Submodule (𝓞 E) E // star X.1 = X.1 ∧ (∀ φ : E →+* ℂ, 0 < (φ X.1).re) ∧
      Submodule.IsFullLattice E X.2 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ X.2, ∃ y ∈ X.2, t = star x * X.1 * y} = N}
    let f : Quot (fun X Y : FullLines => LineRel X.1 Y.1) → LineCls N :=
      Quot.map (fun X => ⟨X.1, X.2.1, X.2.2.1, X.2.2.2.1.toIsLattice, X.2.2.2.2⟩) (fun _ _ h => h)
    have hs : Function.Surjective f := by
      intro q
      induction q using Quot.inductionOn with
      | _ X =>
        exact ⟨Quot.mk _ ⟨X.1, X.2.1, X.2.2.1, hfull X, X.2.2.2.2⟩, rfl⟩
    exact (enat_card_le_of_rel (fun q p => f p = q) (fun q => hs q) (by intros; subst_vars; rfl)).trans
      (GlobalTheory.T.card_rankOne_hermitian_lattice_classes_le E hE N)
  refine enat_card_sigma_le _ _ ?_ fun 𝔫 => enat_card_sigma_le _ _ (hline 𝔫) fun q₁ =>
    enat_card_sigma_le _ _ (hline 𝔫) fun q₂ => ?_
  · have hf : (realIdeals E Y).Finite := (GlobalTheory.T.ncard_realGenerated_ideals_le E hE Y hY).1
    rw [hf.cast_ncard_eq]
    exact le_rfl
  · obtain ⟨a1, a2, a3, a4⟩ := (Quot.out q₁).2
    obtain ⟨b1, b2, b3, b4⟩ := (Quot.out q₂).2
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have ha : (Quot.out q₁).1.1 ≠ 0 := fun h => by simpa [h] using a2 φ
    have hb : (Quot.out q₂).1.1 ≠ 0 := fun h => by simpa [h] using b2 φ
    refine (GlobalTheory.T.card_unimodular_gluings_two_lines_le E hE _ _ _ _ 𝔫.1 a1 b1 ha hb a3 b3 a4).trans ?_
    exact_mod_cast Nat.le_floor 𝔫.2.2.2

theorem defClassNum_le_card (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) :
    defClassNum E 2 ≤ ENat.card (GlueData E ((2 * Formalism.HermitianLatticesTheory.vInv E) ^ Formalism.HermitianLatticesTheory.fDeg E)) := by
  unfold defClassNum
  refine enat_card_le_of_rel (fun c t => ∃ X, Quot.mk _ X = c ∧
    X.1 = (Matrix.diagonal ![(Quot.out t.2.1).1.1, (Quot.out t.2.2.1).1.1], t.2.2.2.1)) ?_ ?_
  · intro c
    obtain ⟨⟨⟨J, Λ⟩, hJ, hpos, hlat, huni⟩, rfl⟩ := Quot.exists_rep c
    obtain ⟨u, hu, hu0, hub⟩ := GlobalTheory.T.exists_short_vector_unimodular_hermitian_lattice_rank_two E hE J hJ hpos Λ hlat huni
    obtain ⟨γ, β₁, β₂, N₁, N₂, 𝔫, hγ, s₁, s₂, hp, l₁, l₂, m₁, m₂, e₁, e₂, n0, nr, nb⟩ :=
      GlobalTheory.T.definiteUnimodularPlane_split_along_vector E hE J hJ hpos Λ hlat huni u hu hu0 _ hub
    have h𝔫 : 𝔫 ∈ realIdeals E ((2 * Formalism.HermitianLatticesTheory.vInv E) ^ Formalism.HermitianLatticesTheory.fDeg E) :=
      ⟨n0, nr, by rwa [← pow_mul, mul_comm _ 2]⟩
    let Y₁ : Lines (Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫) := ⟨(β₁, N₁), s₁, fun φ => (hp φ).1, l₁, e₁⟩
    let Y₂ : Lines (Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫) := ⟨(β₂, N₂), s₂, fun φ => (hp φ).2, l₂, e₂⟩
    obtain ⟨c₁, hc₁, k₁, j₁⟩ := lineRel_out Y₁
    obtain ⟨c₂, hc₂, k₂, j₂⟩ := lineRel_out Y₂
    set q₁ : LineCls (Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫) := Quot.mk _ Y₁ with hq₁
    set q₂ : LineCls (Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫) := Quot.mk _ Y₂ with hq₂
    let δ : GL (Fin 2) E := γ * diagGL c₁ c₂ hc₁ hc₂
    have hδv : (δ : Matrix (Fin 2) (Fin 2) E) = γ * Matrix.diagonal ![c₁, c₂] := rfl
    have hδ : (δ : Matrix (Fin 2) (Fin 2) E)ᴴ * J * (δ : Matrix (Fin 2) (Fin 2) E) =
        Matrix.diagonal ![(Quot.out q₁).1.1, (Quot.out q₂).1.1] := by
      rw [← k₁, ← k₂, ← diag_conj, ← hγ, hδv, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have hu' := pull_unimodular δ J Λ huni
    have hp' := pull_pos δ J hpos
    have hh : ((δ : Matrix (Fin 2) (Fin 2) E)ᴴ * J * (δ : Matrix (Fin 2) (Fin 2) E))ᴴ =
        (δ : Matrix (Fin 2) (Fin 2) E)ᴴ * J * (δ : Matrix (Fin 2) (Fin 2) E) := by
      have hJ' : Jᴴ = J := hJ
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, hJ', Matrix.mul_assoc]
    rw [hδ] at hu' hp' hh
    have hl' := pull_isLattice δ Λ hlat
    refine ⟨⟨⟨𝔫, h𝔫⟩, q₁, q₂, pull δ Λ, hl', hu', fun t => ?_, fun t => ?_⟩,
      ⟨(_, pull δ Λ), hh, hp', hl', hu'⟩, Quot.sound ⟨δ, hδ, fun y => Iff.rfl⟩, rfl⟩
    · rw [mem_pull, hδv, ← mulVec_mulVec, diag_mulVec, mul_zero, ← m₁]
      exact (j₁ t).symm
    · rw [mem_pull, hδv, ← mulVec_mulVec, diag_mulVec, mul_zero, ← m₂]
      exact (j₂ t).symm
  · rintro _ _ t ⟨X, rfl, hX⟩ ⟨X', rfl, hX'⟩
    rw [Subtype.ext (hX.trans hX'.symm)]

theorem rankTwoClasses : RankTwoClasses := by
  intro E _ _ _ hE
  obtain ⟨hdeg, -, hrd, hsq⟩ := GlobalTheory.T.rootDiscr_ge_three_halves_of_isTotallyComplex E hE.1
  set f := Formalism.HermitianLatticesTheory.fDeg E with hf
  set ρ := 2 * Formalism.HermitianLatticesTheory.vInv E with hρ
  have hρ1 : 1 ≤ ρ := by linarith
  have hY : 1 ≤ ρ ^ f := one_le_pow₀ hρ1
  have h1 := (defClassNum_le_card hE).trans (card_glueData_le hE _ hY)
  have h2 : ((realIdeals E (ρ ^ f)).ncard : ℝ) ≤ ρ ^ f * (1 + Real.log (ρ ^ f)) ^ f :=
    (GlobalTheory.T.ncard_realGenerated_ideals_le E hE _ hY).2
  have h3 := GlobalTheory.classNumber_le_minkowski_count E
  rw [← hf, ← hρ] at h1
  rw [hsq, hdeg] at h3
  rw [Real.log_pow] at h2 h3
  have h4 : ((⌊(ρ ^ f) ^ 2⌋₊ : ℕ) : ℝ) ≤ (ρ ^ f) ^ 2 := Nat.floor_le (by positivity)
  have hL : 0 ≤ 1 + f * Real.log ρ := by
    have := Real.log_nonneg hρ1
    positivity
  refine (ENat.toENNReal_le.2 h1).trans ?_
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  set L := 1 + f * Real.log ρ
  calc _ ≤ (ρ ^ f * L ^ f) * ((ρ ^ f * L ^ (2 * f) * 2 ^ f) * ((ρ ^ f * L ^ (2 * f) * 2 ^ f) * (ρ ^ f) ^ 2)) := by
        gcongr
    _ = _ := by
        have h44 : (4 : ℝ) ^ f = 2 ^ f * 2 ^ f := by rw [← mul_pow]; norm_num
        rw [h44]
        clear_value L ρ f
        ring

end GlobalTheory.RankTwoCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankTwoDefiniteUnimodularHermitianClassBoundStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_two_definite_unimodular_hermitian_class_bound : RankTwoClasses := by
  first | exact @GlobalTheory.RankTwoCount.rankTwoClasses | exact GlobalTheory.RankTwoCount.rankTwoClasses | (intros; apply GlobalTheory.RankTwoCount.rankTwoClasses <;> assumption)
end
