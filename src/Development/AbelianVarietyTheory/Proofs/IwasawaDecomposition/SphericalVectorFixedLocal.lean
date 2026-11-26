module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLeOneIffOfContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLeOneIffOfContinuous
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.IsoInteg

open ValuativeRel Filter Topology

section Val

variable {K K' : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem tendsto_pow_zero_of_lt_one {x : K} (h : valuation K x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_of_continuous (i : K →+* K') (hi : Continuous i) {x : K} (h : valuation K x < 1) :
    valuation K' (i x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => i x ^ n) atTop (𝓝 0) := by
    have := (hi.tendsto 0).comp (tendsto_pow_zero_of_lt_one h)
    simpa [Function.comp_def, map_pow] using this
  have hU : {y : K' | valuation K' y < 1} ∈ 𝓝 (0 : K') :=
    (IsValuativeTopology.hasBasis_nhds_zero' K').mem_iff.2 ⟨1, one_ne_zero, fun y hy => hy⟩
  obtain ⟨N, hN⟩ := (h1.eventually hU).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ valuation K' (i x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_one_of_map_le_one (i : K →+* K') (hi : Continuous i) {y : K} (h : valuation K' (i y) ≤ 1) :
    valuation K y ≤ 1 := by
  by_contra hc
  push_neg at hc
  have hy : y ≠ 0 := fun h0 => by simp [h0] at hc
  have h1 : valuation K y⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have h2 := lt_one_of_continuous i hi h1
  rw [map_inv₀, map_inv₀] at h2
  have h0 : (0 : ValueGroupWithZero K') < valuation K' (i y) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact (map_ne_zero i).2 hy
  exact absurd h (not_le.2 ((inv_lt_one₀ h0).1 h2))

theorem map_le_one (i : K →+* K') (hi : Continuous i) {y : K} (h : valuation K y ≤ 1) :
    valuation K' (i y) ≤ 1 := by
  by_contra hc
  push_neg at hc
  have hy : y ≠ 0 := fun h0 => by simp [h0] at hc
  obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
  have hx : x ≠ 0 := fun h0 => hx0 (by simp [h0])
  have hγ : valuation K' (i x) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact (map_ne_zero i).2 hx
  have hpos : (0 : ValueGroupWithZero K') < valuation K' (i y) := zero_lt_one.trans hc
  have hinv : valuation K' (i y)⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have ht := tendsto_pow_zero_of_lt_one hinv
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K').tendsto_right_iff] at ht
  obtain ⟨n, hn⟩ := (ht _ hγ).exists
  have hxy : valuation K (x * y ^ n) < 1 := by
    rw [map_mul, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' h n)) hx1
  have h2 := lt_one_of_continuous i hi hxy
  rw [map_mul, map_pow, map_mul, map_pow] at h2
  simp only [Set.mem_setOf_eq, map_pow, map_inv₀] at hn
  have hpn : (0 : ValueGroupWithZero K') < valuation K' (i y) ^ n := pow_pos hpos n
  rw [inv_pow] at hn
  have := (inv_lt_iff_one_lt_mul₀ hpn).1 hn
  exact absurd h2 (not_lt.2 this.le)

end Val

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem valued_le_one_iff_of_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E),
    Continuous i → ∀ a : v.adicCompletion F, Valued.v (i a) ≤ 1 ↔ Valued.v a ≤ 1 := by
  intro F E _ _ _ _ v w i hi a
  rw [← GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff w, ← GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff v]
  exact ⟨le_one_of_map_le_one i.toRingHom hi, map_le_one i.toRingHom hi⟩

end GlobalTheory.IsoInteg

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLeOneIffOfContinuousStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valued_le_one_iff_of_continuous_ringEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 F))
    (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E), Continuous i →
    ∀ a : v.adicCompletion F, Valued.v (i a) ≤ 1 ↔ Valued.v a ≤ 1 := by
  first | exact @GlobalTheory.IsoInteg.valued_le_one_iff_of_continuous | exact GlobalTheory.IsoInteg.valued_le_one_iff_of_continuous | (intros; apply GlobalTheory.IsoInteg.valued_le_one_iff_of_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceHeckeOperatorEigenvalueConjSpherical
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeOperatorInverseConjugatePlaceCosetSum
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeOperatorInverseConjugatePlaceCosetSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeEigCoset

open GlobalTheory.LFun.ConjPlace

theorem heckeVec_Tj_inv_conj_eq_sum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ (k : ℕ), k ≤ n →
    ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L), Continuous i →
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L)) V)
    (R : Finset (GAf L n)), (∀ γ ∈ R, γ ∈ tSet L n s ϖ k) → (∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) →
    ∀ e ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n),
      GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)
                   (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) e =
        ∑ γ ∈ R, ρ (Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n γ)) e := by
  intro L _ _ _ n s ϖ hϖ k hk i hi V _ _ ρ R hR1 hR2 e he
  classical
  have hO : ∀ a, i a ∈ Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w ↔
      a ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
    intro a
    have h := GlobalTheory.T.valued_le_one_iff_of_continuous_ringEquiv _ _ s.v (GlobalTheory.HeckeFrob.conjSplit s).w i hi a
    exact h.trans (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    have h0 : Valued.v (0 : s.v.adicCompletion (maximalRealSubfield L)) = WithZero.exp (-1 : ℤ) := hϖ
    rw [map_zero] at h0
    exact WithZero.exp_ne_zero h0.symm
  set ϖu : (s.v.adicCompletion (maximalRealSubfield L))ˣ := Units.mk0 ϖ hϖ0 with hϖu
  have ha : invT i n (dGL n ϖu k) = (dGL n (Units.map (i : _ →* _) ϖu) k)⁻¹ := by
    rw [← invT_dGL, map_inv, inv_inv]
  have h1 : (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) =
      Formalism.UG.dosetInd ℂ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n) (invT i n (dGL n ϖu k)) := by
    funext g
    have hiϖ : i ϖ = ((Units.map (i : s.v.adicCompletion (maximalRealSubfield L) →* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) ϖu :
        ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L)ˣ) : (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) := by
      rw [Units.coe_map, hϖu, Units.val_mk0]
      rfl
    rw [hiϖ, Tj_apply, Formalism.UG.dosetInd, Set.indicator_apply, Pi.one_apply]
    refine if_congr ?_ rfl rfl
    rw [DoubleCoset.mem_doubleCoset, ha]
    constructor
    · rintro ⟨x, hx, y, hy, h⟩
      exact ⟨y⁻¹, inv_mem hy, x⁻¹, inv_mem hx, by rw [← inv_inv g, h]; group⟩
    · rintro ⟨x, hx, y, hy, h⟩
      exact ⟨y⁻¹, inv_mem hy, x⁻¹, inv_mem hx, by rw [h]; group⟩
  have hK : ∀ x : GAf L n, TrivOutside {s.v} x → (x ∈ tSet L n s ϖ k ↔ invT i n (s.loc n x) ∈
      DoubleCoset.doubleCoset (invT i n (dGL n ϖu k)) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _)
        (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)) := by
    intro x hx
    rw [tSet, Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨-, A, hA, B, hB, h⟩
      refine ⟨invT i n A, (mem_iff_invT i hO A).1 hA, invT i n B, (mem_iff_invT i hO B).1 hB, ?_⟩
      have : s.loc n x = A * dGL n ϖu k * B := Units.ext (by rw [Units.val_mul, Units.val_mul, h]; rfl)
      rw [this, map_mul, map_mul]
    · rintro ⟨A', hA', B', hB', h⟩
      obtain ⟨A, rfl⟩ := (invT i n).surjective A'
      obtain ⟨B, rfl⟩ := (invT i n).surjective B'
      rw [← map_mul, ← map_mul, (invT i n).apply_eq_iff_eq] at h
      refine ⟨hx, A, (mem_iff_invT i hO A).2 hA', B, (mem_iff_invT i hO B).2 hB', ?_⟩
      rw [h]
      rfl
  have hφK : ∀ x : GAf L n, TrivOutside {s.v} x →
      (invT i n (s.loc n x) ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n ↔ x ∈ Umax L n) :=
    fun x hx => (mem_iff_invT i hO _).symm.trans (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hx)
  have hRa : ∀ γ' ∈ R.image (fun γ => invT i n (s.loc n γ)), γ' ∈ DoubleCoset.doubleCoset (invT i n (dGL n ϖu k))
      (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n) := by
    intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hγ'
    exact (hK γ (hR1 γ hγ).1).1 (hR1 γ hγ)
  have hRb : ∀ g ∈ DoubleCoset.doubleCoset (invT i n (dGL n ϖu k))
      (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n),
      ∃! γ', γ' ∈ R.image (fun γ => invT i n (s.loc n γ)) ∧ γ'⁻¹ * g ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n := by
    intro g hg
    obtain ⟨-, -, hlift⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
    obtain ⟨x, ⟨hx, hxg⟩, -⟩ := hlift ((invT i n).symm g)
    have hgx : g = invT i n (s.loc n x) := by rw [hxg]; simp
    have hxT : x ∈ tSet L n s ϖ k := (hK x hx).2 (hgx ▸ hg)
    obtain ⟨γ, ⟨hγ, hγx⟩, huniq⟩ := hR2 x hxT
    have key : ∀ δ ∈ R, (invT i n (s.loc n δ))⁻¹ * g ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n ↔
        δ⁻¹ * x ∈ Umax L n := by
      intro δ hδ
      rw [hgx, ← map_inv, ← map_inv, ← map_mul, ← map_mul]
      exact hφK _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hR1 δ hδ).1) hx)
    refine ⟨invT i n (s.loc n γ), ⟨Finset.mem_image_of_mem _ hγ, (key γ hγ).2 hγx⟩, ?_⟩
    rintro γ' ⟨hγ', hγ'g⟩
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ'
    rw [huniq δ ⟨hδ, (key δ hδ).1 hγ'g⟩]
  have hinj : Set.InjOn (fun γ => invT i n (s.loc n γ)) R := by
    intro γ₁ h₁ γ₂ h₂ heq
    have hγ₂ := hR1 γ₂ h₂
    obtain ⟨γ, -, huniq⟩ := hR2 γ₂ hγ₂
    have e1 : γ₁⁻¹ * γ₂ ∈ Umax L n := by
      rw [← hφK _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hR1 γ₁ h₁).1) hγ₂.1), map_mul, map_mul,
        map_inv, map_inv]
      simp only at heq
      rw [heq, inv_mul_cancel]
      exact one_mem _
    exact (huniq γ₁ ⟨h₁, e1⟩).trans (huniq γ₂ ⟨h₂, by rw [inv_mul_cancel]; exact one_mem _⟩).symm
  rw [h1, GlobalTheory.LFun.heckeVec_dosetInd he hRa hRb, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [GlobalTheory.HeckeEigConj.map_loc_conjSplit]

end GlobalTheory.HeckeEigCoset
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeOperatorInverseConjugatePlaceCosetSumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitHeckeOperator_inverse_conjugatePlace_cosetSum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ (k : ℕ), k ≤ n →
    ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L), Continuous i →
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L)) V)
    (R : Finset (GAf L n)), (∀ γ ∈ R, γ ∈ tSet L n s ϖ k) → (∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) →
    ∀ e ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n),
      GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)
                   (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) e =
        ∑ γ ∈ R, ρ (Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n γ)) e := by
  first | exact @GlobalTheory.HeckeEigCoset.heckeVec_Tj_inv_conj_eq_sum | exact GlobalTheory.HeckeEigCoset.heckeVec_Tj_inv_conj_eq_sum | (intros; apply GlobalTheory.HeckeEigCoset.heckeVec_Tj_inv_conj_eq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAdicCompletionEquivUniformiser
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAdicCompletionEquivUniformiser
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnifMap

theorem unif_to_unif : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 F))
    (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E), Continuous i →
    ∀ ϖ : v.adicCompletion F, Valued.v ϖ = WithZero.exp (-1 : ℤ) → Valued.v (i ϖ) = WithZero.exp (-1 : ℤ) := by
  intro F E _ _ _ _ v w i hi ϖ hϖ
  have hle := GlobalTheory.T.valued_le_one_iff_of_continuous_ringEquiv F E v w i hi
  have key : ∀ x : WithZero (Multiplicative ℤ), x ≠ 0 → x < 1 → x ≤ WithZero.exp (-1 : ℤ) := by
    intro x hx h1
    rw [← WithZero.exp_log hx] at h1 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [WithZero.exp_le_exp]; omega
  have hlt : ∀ y, Valued.v (i y) < 1 ↔ Valued.v y < 1 := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · have hiy : i y ≠ 0 := by simpa using hy
      have e1 := (Valued.v (R := w.adicCompletion E)).one_lt_val_iff (inv_ne_zero hiy)
      have e2 := (Valued.v (R := v.adicCompletion F)).one_lt_val_iff (inv_ne_zero hy)
      rw [inv_inv] at e1 e2
      rw [← e1, ← e2, ← not_le, ← not_le, ← map_inv₀ i, hle]
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hiϖ0 : i ϖ ≠ 0 := by simpa using hϖ0
  have hϖ1 : Valued.v ϖ < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hup : Valued.v (i ϖ) < 1 := (hlt ϖ).2 hϖ1
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E w
  set z : w.adicCompletion E := (π : w.adicCompletion E)
  have hz : Valued.v z = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hπ
  set y := i.symm z
  have hy1 : Valued.v y < 1 := by
    rw [← hlt, RingEquiv.apply_symm_apply, hz, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy1
    have : z = 0 := by simpa [y] using h
    rw [this, map_zero] at hz; exact WithZero.exp_ne_zero hz.symm
  have hdiv : Valued.v (y / ϖ) ≤ 1 := by
    rw [map_div₀, hϖ, div_le_one₀ (by simp)]
    exact key _ (by simpa using hy0) hy1
  have h2 := (hle _).2 hdiv
  rw [map_div₀, map_div₀, RingEquiv.apply_symm_apply, hz] at h2
  have hlow : WithZero.exp (-1 : ℤ) ≤ Valued.v (i ϖ) := by
    rwa [div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hiϖ0))] at h2
  exact le_antisymm (key _ (by simpa using hiϖ0) hup) hlow

end GlobalTheory.UnifMap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAdicCompletionEquivUniformiserStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_adicCompletion_equiv_uniformiser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 F))
    (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E), Continuous i →
    ∀ ϖ : v.adicCompletion F, Valued.v ϖ = WithZero.exp (-1 : ℤ) → Valued.v (i ϖ) = WithZero.exp (-1 : ℤ) := by
  first | exact @GlobalTheory.UnifMap.unif_to_unif | exact GlobalTheory.UnifMap.unif_to_unif | (intros; apply GlobalTheory.UnifMap.unif_to_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SatakeEigenvalueInvNormalisedEqEsymm
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SatakeEigenvalueInvNormalisedEqEsymm
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SatEigArith

theorem esymm_map_mul_const' (c : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (s.map (· * c)).esymm k = c ^ k * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, Function.comp_def]
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun t ht => ?_)
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    (Multiset.mem_powersetCard.1 ht).2, Multiset.map_id', mul_comm]

theorem exponent_eq (q n k : ℕ) (hq : 0 < q) (hk : k ≤ n) :
    (q : ℂ) ^ (k * (k - 1) / 2) * ((q : ℂ) ^ (k * (n - 1)))⁻¹ * (q : ℂ) ^ (((k : ℂ) * ((n : ℂ) - k)) / 2) =
      ((q : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)) ^ k := by
  have hQ : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp
  have h2 : ((k * (k - 1) / 2 : ℕ) : ℂ) = (k : ℂ) * ((k : ℂ) - 1) / 2 := by
    have h0 := Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_pred_self k))
    have e : ((k * (k - 1) / 2 * 2 : ℕ) : ℂ) = ((k * (k - 1) : ℕ) : ℂ) := by rw [h0]
    simp only [Nat.cast_mul, Nat.cast_ofNat] at e
    rw [eq_div_iff two_ne_zero, e, Nat.cast_sub (show 1 ≤ k from hk1)]
    push_cast
    ring
  have h3 : ((k * (n - 1) : ℕ) : ℂ) = (k : ℂ) * ((n : ℂ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ n by omega)]
    push_cast
    ring
  rw [← Complex.cpow_natCast, ← Complex.cpow_natCast, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hQ,
    ← Complex.cpow_add _ _ hQ, ← Complex.cpow_mul_nat, h2, h3]
  congr 1
  push_cast
  ring

theorem satEig_inv_normalised : ∀ (q n k : ℕ), 0 < q → k ≤ n → ∀ (α : Fin n → ℂˣ),
    (q : ℂ) ^ (k * (k - 1) / 2) * (((q : ℂ) ^ (k * (n - 1)))⁻¹ *
        GlobalTheory.LFun.satEig q n ((Finset.univ.val.map α).map (·⁻¹)) k) =
      ((Finset.univ.val.map fun i => ((α i : ℂ))⁻¹).map (· * (q : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))).esymm k := by
  intro q n k hq hk α
  rw [esymm_map_mul_const', GlobalTheory.LFun.satEig, ← mul_assoc, ← mul_assoc, exponent_eq q n k hq hk]
  congr 2
  simp [Multiset.map_map, Function.comp_def, Units.val_inv_eq_inv_val]

end GlobalTheory.SatEigArith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SatakeEigenvalueInvNormalisedEqEsymmStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeEigenvalue_inv_normalised_eq_esymm : ∀ (q n k : ℕ), 0 < q → k ≤ n → ∀ (α : Fin n → ℂˣ),
    (q : ℂ) ^ (k * (k - 1) / 2) * (((q : ℂ) ^ (k * (n - 1)))⁻¹ *
        GlobalTheory.LFun.satEig q n ((Finset.univ.val.map α).map (·⁻¹)) k) =
      ((Finset.univ.val.map fun i => ((α i : ℂ))⁻¹).map (· * (q : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))).esymm k := by
  first | exact @GlobalTheory.SatEigArith.satEig_inv_normalised | exact GlobalTheory.SatEigArith.satEig_inv_normalised | (intros; apply GlobalTheory.SatEigArith.satEig_inv_normalised <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceHeckeOperatorEigenvalueConjSpherical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeEigConj
open GlobalTheory.HeckeEigConj

theorem tN_eig : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ J : Subgroup (GAf L n),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) →
    ∀ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L))) (α : Fin n → ℂˣ),
    GlobalTheory.SmGL.HasSatake σ.ρ α →
    ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L), Continuous i →
    (∀ x : L, i ((GlobalTheory.HeckeFrob.conjSplit s).i x) = algebraMap L ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) x) →
    ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (T : σ.V →ₗ[ℂ] (GAf L n → W)),
    GlobalTheory.HeckeFrob.IsLocMap (GlobalTheory.HeckeFrob.conjSplit s) σ i T →
    ∀ e ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) (Fin n)),
    ∀ k, 1 ≤ k → k ≤ n →
      ((normV (GlobalTheory.HeckeFrob.conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) • NG.tN J s ϖ k (T e) =
        (GlobalTheory.HeckeFrob.twEig (GlobalTheory.HeckeFrob.conjSplit s).w α).esymm k • T e := by
  intro L _ _ _ n s ϖ hϖ J hJ σ α hα i hi hiL W _ _ T hT e he k hk1 hkn
  classical
  have hK : ∀ a, i a ∈ Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w ↔
      a ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun a =>
    GlobalTheory.IsoInteg.valued_le_one_iff_of_continuous (maximalRealSubfield L) L s.v _ i hi a
  have heK : e ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n) := by
    rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL L (GlobalTheory.HeckeFrob.conjSplit s).w n]; exact he
  have hφK : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ →
      Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n κ) ∈
        GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n := fun κ hκ ht => by
    rw [GlobalTheory.HeckeEigConj.map_loc_conjSplit L n s i κ]
    exact (GlobalTheory.LFun.ConjPlace.mem_iff_invT i hK _).1 ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s ht).2 hκ)
  obtain ⟨α0, -, hT0⟩ := GlobalTheory.HeckeScalarSph.exists_tSet_eq (n := n) s ϖ k hϖ
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.HeckeScalarSph.exists_repsU (n := n) s.v α0
  have hR1' : ∀ γ ∈ R, γ ∈ tSet L n s ϖ k := fun γ hγ => (hT0 γ).2 (hR1 γ hγ)
  have hR2' : ∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n := fun x hx => hR2 x ((hT0 x).1 hx)
  have hD : ∀ x ∈ tSet L n s ϖ k, TrivOutside {s.v} x := fun x hx => hx.1
  have hrt : ∀ x, TrivOutside {s.v} x → NG.rt L n x (T e) =
      T (σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n x)) e) :=
    fun x hx => (hT x hx e).symm
  have hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ (T e) = T e := fun κ hκ ht => by
    rw [hrt κ ht, GlobalTheory.LGrp.mem_fixed.1 heK _ (hφK κ hκ ht)]
  have hsum := heckeD_eq_sum_of_agree J hJ hD hR1' hR2' hfix
  have hloc := GlobalTheory.T.splitHeckeOperator_inverse_conjugatePlace_cosetSum L n s ϖ hϖ k hkn i hi σ.ρ R hR1' hR2' e heK
  have key : NG.heckeD J (tSet L n s ϖ k) (T e) = T (GlobalTheory.LFun.heckeVec σ.ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)
      (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) e) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, hloc, map_sum]
    exact Finset.sum_congr rfl fun γ hγ => hrt γ (hD γ (hR1' γ hγ))
  obtain ⟨hq1, hq2⟩ := norms_eq s
  by_cases he0 : e = 0
  · subst he0
    simp only [map_zero, smul_zero]
    funext g
    simp [NG.tN, NG.heckeD]
  have hSat := (GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake L (GlobalTheory.HeckeFrob.conjSplit s).w n σ.V σ.ρ α hα).2 e heK he0
  have hU : Formalism.UG.IsUnifV L (GlobalTheory.HeckeFrob.conjSplit s).w (i ϖ) :=
    GlobalTheory.T.continuous_adicCompletion_equiv_uniformiser (maximalRealSubfield L) L s.v _ i hi ϖ hϖ
  have hinv := (GlobalTheory.ChainOnto.SatInv.satVec_iff_inv L (GlobalTheory.HeckeFrob.conjSplit s).w n σ.V σ.ρ e _ he0 heK
    (by simp)).1 hSat (i ϖ) hU k hkn
  rw [NG.tN, key, hinv, map_smul, smul_smul, smul_smul, hq1, hq2]
  congr 1
  rw [mul_assoc]
  exact GlobalTheory.T.satakeEigenvalue_inv_normalised_eq_esymm (normV (GlobalTheory.HeckeFrob.conjSplit s).w) n k
    (Nat.pos_of_ne_zero (hq1 ▸ GlobalTheory.LFun.qV_ne_zero (GlobalTheory.HeckeFrob.conjSplit s).w)) hkn α

end GlobalTheory.HeckeEigConj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceHeckeOperatorEigenvalueConjSphericalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_hecke_operator_eigenvalue_conj_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ J : Subgroup (GAf L n),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) →
    ∀ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L))) (α : Fin n → ℂˣ),
    GlobalTheory.SmGL.HasSatake σ.ρ α →
    ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L), Continuous i →
    (∀ x : L, i ((GlobalTheory.HeckeFrob.conjSplit s).i x) = algebraMap L ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) x) →
    ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (T : σ.V →ₗ[ℂ] (GAf L n → W)),
    GlobalTheory.HeckeFrob.IsLocMap (GlobalTheory.HeckeFrob.conjSplit s) σ i T →
    ∀ e ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) (Fin n)),
    ∀ k, 1 ≤ k → k ≤ n →
      ((normV (GlobalTheory.HeckeFrob.conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) • NG.tN J s ϖ k (T e) =
        (GlobalTheory.HeckeFrob.twEig (GlobalTheory.HeckeFrob.conjSplit s).w α).esymm k • T e := by
  first | exact @GlobalTheory.HeckeEigConj.tN_eig | exact GlobalTheory.HeckeEigConj.tN_eig | (intros; apply GlobalTheory.HeckeEigConj.tN_eig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceFixedVectorSumSphericalImages
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceFixedVectorSumSphericalImages
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SphAvg

open GlobalTheory.SplitWeil

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem exists_lift {n : ℕ} (s : SplitPlace L)
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hi : Continuous i)
    (y : GL (Fin n) (s.w.adicCompletion L)) (hy : y ∈ KO (s.w.adicCompletion L) (Fin n)) :
    ∃ κ : GAf L n, κ ∈ Umax L n ∧ TrivOutside {s.v} κ ∧
      Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n κ) = y := by
  have hE := GlobalTheory.ConjParahoric.isEquiv_of_continuous i hi
  have hle : ∀ x, ValuativeRel.valuation (s.w.adicCompletion L) x ≤ 1 → Valued.v (i.symm x) ≤ 1 :=
    fun x hx => (Valuation.isEquiv_iff_val_le_one.1 hE).2 hx
  obtain ⟨u, rfl⟩ := hy
  set M := Matrix.GeneralLinearGroup.map i.symm.toRingHom
    (Matrix.GeneralLinearGroup.map (algebraMap _ (s.w.adicCompletion L)) u) with hM
  obtain ⟨κ, hκ, hloc⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s M
  have mem_Umax_of_loc (s : SplitPlace L) (x : GAf L n) (hx : TrivOutside {s.v} x)
      (h1 : ∀ i j, Valued.v (((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) ≤ 1)
      (h2 : ∀ i j, Valued.v (((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) ≤ 1) :
      x ∈ Umax L n := by
    obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
    intro i j
    have hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
        (((x⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
      rw [GlobalTheory.FinTypCount.inv_val]
      rfl
    have hz : (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
      apply GlobalTheory.mem_ALint_of_supported_at_split L s e he he'
      · intro w hw
        have := congrFun (congrFun (hx w (by simpa using hw)) i) j
        simp only [Matrix.map_apply] at this
        rw [map_sub, this]
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      · have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
            ((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := rfl
        rw [map_sub, e1]
        refine (Valuation.map_sub _ _ _).trans (max_le (h1 i j) ?_)
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      · have e1 : s.proj ((((x⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
            ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) j i := rfl
        rw [map_sub, map_sub, hconj, e1]
        refine (Valuation.map_sub _ _ _).trans (max_le (h2 j i) ?_)
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    have := add_mem hz (show (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem])
    simpa using this
  refine ⟨κ, mem_Umax_of_loc s κ hκ ?_ ?_, hκ, ?_⟩
  · intro a b
    rw [hloc]
    exact hle _ (u.val a b).2
  · intro a b
    rw [map_inv, hloc, hM, ← map_inv, ← map_inv]
    exact hle _ ((u⁻¹).val a b).2
  · rw [hloc, hM]
    ext a b
    simp

theorem exists_fixed_of_sum {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hi : Continuous i)
    {ι : Type} [Fintype ι] (T : ι → σ.V →ₗ[ℂ] (GAf L n → W))
    (hT : ∀ j, GlobalTheory.HeckeFrob.IsLocMap s σ i (T j)) (u : ι → σ.V) (f : GAf L n → W)
    (hf : f = ∑ j, T j (u j)) (hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) :
    ∃ e : ι → σ.V, (∀ j, e j ∈ GlobalTheory.PRep.fixed σ.ρ (KO (s.w.adicCompletion L) (Fin n))) ∧
      f = ∑ j, T j (e j) := by
  classical
  let H : Subgroup (GL (Fin n) (s.w.adicCompletion L)) :=
    { carrier := {g | ∀ j, σ.ρ g (u j) = u j}
      mul_mem' := fun {a b} ha hb j => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb j, ha j]
      one_mem' := fun j => by simp
      inv_mem' := fun {a} ha j => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        conv_lhs => rw [← ha j]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hHo : IsOpen (H : Set (GL (Fin n) (s.w.adicCompletion L))) := by
    have : (H : Set (GL (Fin n) (s.w.adicCompletion L))) = ⋂ j, {g | σ.ρ g (u j) = u j} := by
      ext g; simp [H]
    rw [this]
    exact isOpen_iInter_of_finite fun j => σ.smooth (u j)
  set K := KO (s.w.adicCompletion L) (Fin n) with hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp GlobalTheory.SplitFlip.isCompact_KO
  haveI : Finite (K ⧸ H.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hHo.preimage continuous_subtype_val)
  letI : Fintype (K ⧸ H.subgroupOf K) := Fintype.ofFinite _
  set N : ℂ := (Fintype.card (K ⧸ H.subgroupOf K) : ℂ) with hNdef
  have hN : N ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let e : ι → σ.V := fun j => N⁻¹ • ∑ q : K ⧸ H.subgroupOf K, σ.ρ ((q.out : K) : GL (Fin n) _) (u j)
  refine ⟨e, fun j => ?_, ?_⟩
  · intro k
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e, map_smul, map_sum]
    congr 1
    have hstep : ∀ q : K ⧸ H.subgroupOf K, σ.ρ (k : GL (Fin n) _) (σ.ρ ((q.out : K) : GL (Fin n) _) (u j)) =
        σ.ρ (((k • q).out : K) : GL (Fin n) _) (u j) := by
      intro q
      have hq : (QuotientGroup.mk ((k • q).out) : K ⧸ H.subgroupOf K) = QuotientGroup.mk (k * q.out) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have hmem := QuotientGroup.eq.1 hq
      rw [Subgroup.mem_subgroupOf] at hmem
      have h1 : ((k * q.out : K) : GL (Fin n) (s.w.adicCompletion L)) =
          (((k • q).out : K) : GL (Fin n) (s.w.adicCompletion L)) *
            ((((k • q).out)⁻¹ * (k * q.out) : K) : GL (Fin n) (s.w.adicCompletion L)) := by
        rw [← Subgroup.coe_mul, mul_inv_cancel_left]
      rw [← Module.End.mul_apply, ← map_mul]
      change σ.ρ ((k * q.out : K) : GL (Fin n) _) (u j) = _
      rw [h1, map_mul, Module.End.mul_apply, hmem j]
    simp_rw [hstep]
    exact Equiv.sum_comp (MulAction.toPerm k) (fun (q : K ⧸ H.subgroupOf K) => σ.ρ ((q.out : K) : GL (Fin n) (s.w.adicCompletion L)) (u j))
  · choose κ hκU hκT hκ using fun (q : K ⧸ H.subgroupOf K) => exists_lift s i hi ((q.out : K) : GL (Fin n) _) q.out.2
    have key : ∀ q : K ⧸ H.subgroupOf K, ∑ j, T j (σ.ρ ((q.out : K) : GL (Fin n) _) (u j)) = f := by
      intro q
      rw [← hκ q]
      simp_rw [hT _ (κ q) (hκT q)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← hf, hfix _ (hκU q) (hκT q)]
    calc f = N⁻¹ • ∑ _q : K ⧸ H.subgroupOf K, f := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← hNdef,
            inv_mul_cancel₀ hN, one_smul]
      _ = N⁻¹ • ∑ q : K ⧸ H.subgroupOf K, ∑ j, T j (σ.ρ ((q.out : K) : GL (Fin n) _) (u j)) := by
          simp_rw [key]
      _ = ∑ j, T j (e j) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [e, map_smul, map_sum, ← Finset.smul_sum]
          rw [Finset.sum_comm]

end GlobalTheory.SphAvg

namespace GlobalTheory.SphAvg

theorem exists_sum_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i →
    (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) →
    ∀ f, f ∈ ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 →
    (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
    ∃ (m : ℕ) (T : Fin m → σ.V →ₗ[ℂ] (GAf L n → π.W)) (e : Fin m → σ.V),
      (∀ j, GlobalTheory.HeckeFrob.IsLocMap s σ i (T j)) ∧
      (∀ j, e j ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n))) ∧ f = ∑ j, T j (e j) := by
  intro L _ _ _ n π s σ i hi _ f hf hfix
  classical
  obtain ⟨c, hc, hcf⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ f).1 hf
  choose u hu using hc
  have hsum : f = ∑ t : c.support, t.1.1 (u t.1) := by
    rw [← hcf, Finsupp.sum, ← Finset.sum_coe_sort]
    exact Finset.sum_congr rfl fun t _ => (hu t.1).symm
  obtain ⟨e, he, hfe⟩ := exists_fixed_of_sum s σ i hi (ι := c.support) (fun t => t.1.1)
    (fun t => t.1.2.2) (fun t => u t.1) f hsum hfix
  · refine ⟨c.support.card, fun j => (c.support.equivFin.symm j).1.1,
      fun j => e (c.support.equivFin.symm j), fun j => (c.support.equivFin.symm j).1.2.2,
      fun j => he _, ?_⟩
    rw [hfe]
    exact (Equiv.sum_comp c.support.equivFin.symm (fun t => t.1.1 (e t))).symm

end GlobalTheory.SphAvg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceFixedVectorSumSphericalImagesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_fixed_vector_sum_spherical_images : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i →
    (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) →
    ∀ f, f ∈ ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 →
    (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
    ∃ (m : ℕ) (T : Fin m → σ.V →ₗ[ℂ] (GAf L n → π.W)) (e : Fin m → σ.V),
      (∀ j, GlobalTheory.HeckeFrob.IsLocMap s σ i (T j)) ∧
      (∀ j, e j ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n))) ∧ f = ∑ j, T j (e j) := by
  first | exact @GlobalTheory.SphAvg.exists_sum_fixed | exact GlobalTheory.SphAvg.exists_sum_fixed | (intros; apply GlobalTheory.SphAvg.exists_sum_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutRepIsotypicSplitPlaceLocalComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutRepIsotypicSplitPlaceLocalComponent
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeFrob

theorem rt_mul_apply {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (a b : GAf L n) (f : GAf L n → W) :
    NG.rt L n (a * b) f = NG.rt L n a (NG.rt L n b f) := by
  funext g; simp [NG.rt, mul_assoc]

theorem exists_ne_zero_of_irrRep {G : Type} [Group G] [TopologicalSpace G] (σ : GlobalTheory.SmGL.IrrRep G) :
    ∃ a : σ.V, a ≠ 0 := by
  by_contra hne
  push Not at hne
  have h := σ.irr
  have : Subsingleton σ.V := ⟨fun a b => by rw [hne a, hne b]⟩
  exact (bot_ne_top : (⊥ : Subrepresentation σ.ρ) ≠ ⊤)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem mem_iSup_range_locMap : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : σ.V →ₗ[ℂ] (GAf L n → π.W)),
    Function.Injective T → (∀ a, T a ∈ π.S) → GlobalTheory.HeckeFrob.IsLocMap s σ i T →
    ∀ g ∈ π.S, g ∈ ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 := by
  intro L _ _ _ n π s σ i T hTi hTS hT g hg
  set I : Submodule ℂ (GAf L n → π.W) :=
    ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 with hIdef
  have hIS : I ≤ π.S := iSup_le fun T' => by
    rintro _ ⟨a, rfl⟩
    exact T'.2.1 a
  have hsub : NG.IsSubrep π.ρ I := by
    refine ⟨hIS.trans π.irrS.1.le, ?_⟩
    intro h f hf
    obtain ⟨x, y, hx, hy, rfl⟩ := (GlobalTheory.SplitAdelic.main L n s).1 h
    have hcomm := (GlobalTheory.SplitAdelic.main L n s).2.1
    refine Submodule.iSup_induction (motive := fun f => NG.rt L n (x * y) f ∈ I) _ hf ?_ ?_ ?_
    · rintro T' _ ⟨a, rfl⟩
      let T'' : σ.V →ₗ[ℂ] (GAf L n → π.W) := (NG.rt L n y).comp T'.1
      have hT'' : (∀ a, T'' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'' := by
        refine ⟨fun a => π.irrS.1.stable y _ (T'.2.1 a), fun z hz a => ?_⟩
        change NG.rt L n y (T'.1 _) = NG.rt L n z (NG.rt L n y (T'.1 a))
        rw [T'.2.2 z hz a, ← rt_mul_apply, ← rt_mul_apply, (hcomm z y hz hy).eq]
      have key : NG.rt L n (x * y) (T'.1 a) =
          T'' (σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) := by
        rw [hT''.2 x hx a, rt_mul_apply]
        rfl
      rw [key]
      exact Submodule.mem_iSup_of_mem ⟨T'', hT''⟩ ⟨_, rfl⟩
    · rw [map_zero]; exact zero_mem _
    · intro f₁ f₂ h₁ h₂
      rw [map_add]; exact add_mem h₁ h₂
  rcases π.irrS.2.2 I hsub hIS with hbot | htop
  · exfalso
    obtain ⟨a, ha⟩ := exists_ne_zero_of_irrRep σ
    have hmem : T a ∈ I := Submodule.mem_iSup_of_mem ⟨T, hTS, hT⟩ ⟨a, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact ha (hTi (hmem.trans (map_zero T).symm))
  · rw [htop]; exact hg

end GlobalTheory.HeckeFrob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutRepIsotypicSplitPlaceLocalComponentStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autRep_isotypic_splitPlace_localComponent : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : σ.V →ₗ[ℂ] (GAf L n → π.W)),
    Function.Injective T → (∀ a, T a ∈ π.S) → GlobalTheory.HeckeFrob.IsLocMap s σ i T →
    ∀ g ∈ π.S, g ∈ ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 := by
  first | exact @GlobalTheory.HeckeFrob.mem_iSup_range_locMap | exact GlobalTheory.HeckeFrob.mem_iSup_range_locMap | (intros; apply GlobalTheory.HeckeFrob.mem_iSup_range_locMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteHeckeDoubleCosetCosetsAtSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteHeckeDoubleCosetCosetsAtSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TSetFinLoc

open GlobalTheory.TSetFin

theorem finite_image_tSet_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ J : Subgroup (GAf L n),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) → ∀ k : ℕ,
    ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' tSet L n s ϖ k).Finite := by
  intro L _ _ _ n s ϖ hϖ J hJ k
  classical
  obtain ⟨c, hc⟩ := approx_class s.v
  haveI : Finite (𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ s.v.ne_bot
  let κ : GAf L n → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := fun x =>
    if h : x ∈ tSet L n s ϖ k then
      fun i j => c (((h.2.choose : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j)
    else 0
  have key : ∀ x ∈ tSet L n s ϖ k, ∀ x' ∈ tSet L n s ϖ k, κ x = κ x' →
      (x : GAf L n ⧸ J) = x' := by
    intro x hx x' hx' hκ
    simp only [κ, dif_pos hx, dif_pos hx'] at hκ
    obtain ⟨ha, b, hb, hg⟩ := hx.2.choose_spec
    obtain ⟨ha', b', hb', hg'⟩ := hx'.2.choose_spec
    set a := hx.2.choose
    set a' := hx'.2.choose
    have ia := glint_int ha
    have ia' := glint_int ha'
    have ib := glint_int hb
    have ib' := glint_int hb'
    have hcl : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j -
        (a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1 := fun i j =>
      hc _ _ (ia.1 i j) (ia'.1 i j) (congrFun (congrFun hκ i) j)
    have hcl' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j -
        (a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1 := fun i j => by
      rw [← Valuation.map_neg, neg_sub]; exact hcl i j
    have hunif : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
    have h1 := local_int s.v ϖ k hunif a a' b b' _ _ ia'.1 ia.2 ib.2 ib'.1 hcl hg hg'
    have h2 := local_int s.v ϖ k hunif a' a b' b _ _ ia.1 ia'.2 ib'.2 ib.1 hcl' hg' hg
    rw [QuotientGroup.eq]
    have htriv : TrivOutside {s.v} (x⁻¹ * x') := triv_mul (triv_inv hx.1) hx'.1
    refine (hJ _ htriv).2 ?_
    exact mem_Umax_of_loc s _ htriv (fun i j => by
      rw [map_mul, map_inv]; exact h1 i j) (fun i j => by
      rw [mul_inv_rev, inv_inv, map_mul, map_inv]; exact h2 i j)
  let g : GAf L n ⧸ J → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := fun q =>
    if h : ∃ x ∈ tSet L n s ϖ k, (x : GAf L n ⧸ J) = q then κ h.choose else 0
  refine Set.Finite.of_finite_image (f := g) (Set.toFinite _) ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ hgg
  have h : ∃ y ∈ tSet L n s ϖ k, (y : GAf L n ⧸ J) = x := ⟨x, hx, rfl⟩
  have h' : ∃ y ∈ tSet L n s ϖ k, (y : GAf L n ⧸ J) = x' := ⟨x', hx', rfl⟩
  simp only [g, dif_pos h, dif_pos h'] at hgg
  show (x : GAf L n ⧸ J) = x'
  rw [← h.choose_spec.2, ← h'.choose_spec.2]
  exact key _ h.choose_spec.1 _ h'.choose_spec.1 hgg

end GlobalTheory.TSetFinLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteHeckeDoubleCosetCosetsAtSplitPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_heckeDoubleCoset_cosets_at_splitPlace : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ J : Subgroup (GAf L n),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) → ∀ k : ℕ,
    ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' tSet L n s ϖ k).Finite := by
  first | exact @GlobalTheory.TSetFinLoc.finite_image_tSet_loc | exact GlobalTheory.TSetFinLoc.finite_image_tSet_loc | (intros; apply GlobalTheory.TSetFinLoc.finite_image_tSet_loc <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeckeFrob

theorem conjSplit_w (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host) (h : IsConjPl D.host w s.w) :
    (conjSplit s).w = w := by
  have hc : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun x => by
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact Formalism.HC.HostAx.conjE_apply _ _ _
  apply HeightOneSpectrum.ext
  ext x
  have hy : ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [hc]; rfl
  rw [h x _ hy]
  exact Iff.rfl

theorem heckeD_add (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) (f f' : GAf L n → W) :
    NG.heckeD J Dset (f + f') = NG.heckeD J Dset f + NG.heckeD J Dset f' := by
  classical
  funext g
  have hsub : ∀ F : GAf L n → W,
      Function.support (fun cc : GAf L n ⧸ J =>
        if hc : ∃ x ∈ Dset, (x : GAf L n ⧸ J) = cc then F (g * hc.choose) else 0) ⊆
        (hfin.toFinset : Set (GAf L n ⧸ J)) := by
    intro F cc hcc
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    apply hcc
    dsimp only
    rw [dite_eq_right]
    rintro ⟨x, hx, rfl⟩
    exact hn ⟨x, hx, rfl⟩
  rw [Pi.add_apply]
  simp only [NG.heckeD]
  rw [finsum_eq_sum_of_support_subset _ (hsub _), finsum_eq_sum_of_support_subset _ (hsub _),
    finsum_eq_sum_of_support_subset _ (hsub _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun cc _ => ?_
  split_ifs <;> simp

theorem heckeD_zero (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) (Dset : Set (GAf L n)) :
    NG.heckeD J Dset (0 : GAf L n → W) = 0 := by
  funext g
  simp [NG.heckeD]

theorem tN_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' tSet L n s ϖ k).Finite) {m : ℕ} (F : Fin m → GAf L n → W) :
    NG.tN J s ϖ k (∑ j, F j) = ∑ j, NG.tN J s ϖ k (F j) := by
  classical
  have key : ∀ t : Finset (Fin m), NG.tN J s ϖ k (∑ j ∈ t, F j) = ∑ j ∈ t, NG.tN J s ϖ k (F j) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp [NG.tN, heckeD_zero]
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      simp only [NG.tN]
      rw [heckeD_add L n J _ hfin, smul_add]
  exact key Finset.univ

theorem prod_eq_vieta (n : ℕ) (β : Multiset ℂ) (hn : Multiset.card β = n) :
    (β.map fun a => X - C a).prod = X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * β.esymm k) * X ^ (n - k) := by
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, hn, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [pow_zero, Multiset.esymm, Multiset.powersetCard_zero_left, Multiset.map_singleton,
    Multiset.prod_zero, Multiset.sum_singleton, map_one, one_mul, Nat.sub_zero]
  congr 1
  refine Finset.sum_congr (by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega) fun k _ => ?_
  rw [map_mul, map_pow, map_neg, map_one, mul_assoc]

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem cls_heq {E : Type} [Field E] [NumberField E] {n : ℕ} {a b : HeightOneSpectrum (𝓞 E)} (h : a = b)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (a.adicCompletion E))) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (b.adicCompletion E)))
    (he : HEq σ.cl τ.cl) : HEq (GlobalTheory.LocLanglands.cls σ) (GlobalTheory.LocLanglands.cls τ) := by
  subst h
  exact heq_of_eq (congrArg (Sigma.mk n) (eq_of_heq he))

end

end GlobalTheory.HeckeFrob

end
