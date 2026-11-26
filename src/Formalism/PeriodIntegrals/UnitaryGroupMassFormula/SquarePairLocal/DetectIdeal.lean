module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.MemFixSub
public import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.PowerSeriesExpansionImageDenseWithDenominator
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SigKApply
noncomputable section
open NumberField IsDedekindDomain HeightOneSpectrum WithZero IsLocalRing Topology Filter

namespace PI.SqPairLocal.Mdl

open PI.SqPairLocal Formalism.BasicNotions.Examples₂

theorem wz_le_of {a b : ℤᵐ⁰} (hb : b ≤ 1)
    (h : ∀ n : ℕ, b ≤ exp (-(n : ℤ)) → a ≤ exp (-(n : ℤ))) : a ≤ b := by
  rcases eq_or_ne b 0 with rfl | h0
  · have : a = 0 := by
      by_contra ha0
      obtain ⟨N, hN⟩ := wz_exists_nat_lt a ha0
      exact absurd (h N (by simp)) (not_le.2 hN)
    simp [this]
  · have hl : log b ≤ 0 := by
      rw [← exp_le_exp, exp_log h0, exp_zero]; exact hb
    have e : b = exp (-(((-(log b)).toNat : ℕ) : ℤ)) := by
      rw [Int.toNat_of_nonneg (by omega), neg_neg, exp_log h0]
    have := h ((-(log b)).toNat) (le_of_eq e)
    rwa [← e] at this

theorem wz_eq_of {a b : ℤᵐ⁰} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ exp (-(n : ℤ)) ↔ b ≤ exp (-(n : ℤ))) : a = b :=
  le_antisymm (wz_le_of hb fun n hn => (h n).2 hn) (wz_le_of ha fun n hn => (h n).1 hn)

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem cj_coe (x : 𝓞 E) : ((cj E x : 𝓞 E) : E) = star (x : E) := rfl

theorem cj_cj (x : 𝓞 E) : cj E (cj E x) = x := by
  ext; rw [cj_coe, cj_coe, star_star]

theorem mem_pow_cj {Q : Ideal (𝓞 E)} (hQ : Q.comap (cj E) = Q) (n : ℕ) (r : 𝓞 E) :
    cj E r ∈ Q ^ n ↔ r ∈ Q ^ n := by
  have h1 : ∀ r, r ∈ Q ^ n → cj E r ∈ Q ^ n := by
    intro r hr
    have : Q ^ n ≤ (Q ^ n).comap (cj E) := by
      calc Q ^ n = (Q.comap (cj E)) ^ n := by rw [hQ]
        _ ≤ _ := Ideal.le_comap_pow _ n
    exact this hr
  exact ⟨fun h => by simpa [cj_cj] using h1 _ h, h1 r⟩

section Val

variable (v : HeightOneSpectrum (𝓞 E)) (hv : v.asIdeal.comap (cj E) = v.asIdeal)
include hv

theorem intVal_cj (r : 𝓞 E) : v.intValuation (cj E r) = v.intValuation r :=
  wz_eq_of (v.intValuation_le_one _) (v.intValuation_le_one _) fun n => by
    rw [intValuation_le_pow_iff_mem, intValuation_le_pow_iff_mem, mem_pow_cj hv]

theorem val_star (a : E) : v.valuation E (star a) = v.valuation E a := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
  have hs : ∀ r : 𝓞 E, star (algebraMap (𝓞 E) E r) = algebraMap (𝓞 E) E (cj E r) := fun r => rfl
  rw [star_div₀, hs, hs, map_div₀, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
    valuation_of_algebraMap, valuation_of_algebraMap, intVal_cj v hv, intVal_cj v hv]


omit hv in
def tau : WithVal (v.valuation E) →+* WithVal (v.valuation E) :=
  WithVal.map (v.valuation E) (v.valuation E) (starRingEnd E)

omit hv in
theorem tau_apply (x : WithVal (v.valuation E)) :
    tau v x = WithVal.toVal (v.valuation E) (star (WithVal.ofVal x)) := rfl

omit hv in
theorem tau_tau (x : WithVal (v.valuation E)) : tau v (tau v x) = x := by
  rw [tau_apply, tau_apply, WithVal.ofVal_toVal, star_star, WithVal.toVal_ofVal]

theorem v_tau (x : WithVal (v.valuation E)) : Valued.v (tau v x) = Valued.v x := by
  rw [tau_apply, WithVal.valued_toVal, val_star v hv, WithVal.apply_ofVal]

theorem tau_cont : Continuous (tau v) := by
  apply continuous_of_continuousAt_zero (tau v)
  rw [ContinuousAt, map_zero]
  refine ((Valued.hasBasis_nhds_zero _ _).tendsto_iff (Valued.hasBasis_nhds_zero _ _)).2
    fun γ _ => ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  rwa [v_tau v hv]

def sigC : (v.valuation E).Completion →+* (v.valuation E).Completion :=
  UniformSpace.Completion.mapRingHom (tau v) (tau_cont v hv)

theorem sigC_coe (x : WithVal (v.valuation E)) :
    sigC v hv (x : (v.valuation E).Completion) = (tau v x : (v.valuation E).Completion) :=
  UniformSpace.Completion.mapRingHom_coe _ x

theorem sigC_cont : Continuous (sigC v hv) := by
  rw [sigC, UniformSpace.Completion.coe_mapRingHom]
  exact UniformSpace.Completion.continuous_map

theorem sigC_sigC (y : (v.valuation E).Completion) : sigC v hv (sigC v hv y) = y := by
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq ((sigC_cont v hv).comp (sigC_cont v hv)) continuous_id
  | ih a => rw [sigC_coe, sigC_coe, tau_tau]

def sigK : v.adicCompletion E →+* v.adicCompletion E :=
  (adicCompletion.equiv E v).symm.toRingHom.comp ((sigC v hv).comp (adicCompletion.equiv E v).toRingHom)

theorem sigK_apply (x : v.adicCompletion E) :
    sigK v hv x = adicCompletion.ofCompletion (sigC v hv x.toCompletion) := rfl

theorem sigK_sigK (x : v.adicCompletion E) : sigK v hv (sigK v hv x) = x := by
  rw [sigK_apply, sigK_apply, adicCompletion.toCompletion_ofCompletion, sigC_sigC]

theorem sigK_cont : Continuous (sigK v hv) := by
  have : (sigK v hv : v.adicCompletion E → v.adicCompletion E) =
      adicCompletion.ofCompletion ∘ (sigC v hv) ∘ adicCompletion.toCompletion := rfl
  rw [this]
  exact (adicCompletion.continuous_ofCompletion E v).comp ((sigC_cont v hv).comp
    (adicCompletion.continuous_toCompletion E v))

theorem sigK_alg (a : E) :
    sigK v hv (algebraMap E (v.adicCompletion E) a) = algebraMap E (v.adicCompletion E) (star a) := by
  show adicCompletion.ofCompletion (sigC v hv _) = _
  erw [sigC_coe]
  rfl

end Val

end PI.SqPairLocal.Mdl
end
end

noncomputable section
open NumberField IsDedekindDomain HeightOneSpectrum WithZero IsLocalRing Topology Filter
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

namespace PI.SqPairLocal.Mdl

open PI.SqPairLocal Formalism.BasicNotions.Examples₂

variable {E : Type} [Field E] [NumberField E] [StarRing E] (v : HeightOneSpectrum (𝓞 E))

theorem ball_sub (x : v.adicCompletion E) {s : Set (v.adicCompletion E)} (hs : s ∈ 𝓝 x) :
    ∃ K : ℕ, ∀ z : v.adicCompletion E, Valued.v (z - x) ≤ exp (-(K : ℤ)) → z ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hs
  have h0 : embedding γ.1 ≠ 0 := fun h =>
    γ.ne_zero (embedding_injective (h.trans (map_zero _).symm))
  obtain ⟨K, hK⟩ := wz_exists_nat_lt _ h0
  refine ⟨K, fun z hz => hγ ?_⟩
  show Valued.v.restrict (z - x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hz hK

theorem exists_val_pow (K : ℕ) :
    ∃ π : E, v.valuation E π = exp (-(K : ℤ)) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer E
  refine ⟨π ^ K, ?_⟩
  rw [map_pow, hπ, ← WithZero.exp_nsmul]
  congr 1
  simp

theorem nhds_lt (x : v.adicCompletion E) (K : ℕ) :
    {z : v.adicCompletion E | Valued.v (z - x) < exp (-(K : ℤ))} ∈ 𝓝 x := by
  obtain ⟨π, hπ⟩ := exists_val_pow v K
  have hv : Valued.v (algebraMap E (v.adicCompletion E) π) = exp (-(K : ℤ)) := by
    change Valued.v (π : v.adicCompletion E) = _
    rw [valuedAdicCompletion_eq_valuation', hπ]
  have hr : Valued.v.restrict (algebraMap E (v.adicCompletion E) π) ≠ 0 := by
    intro h
    have := congrArg embedding h
    rw [Valuation.embedding_restrict, hv, map_zero] at this
    exact exp_ne_zero this
  refine Valued.mem_nhds.2 ⟨Units.mk0 _ hr, fun z hz => ?_⟩
  have hz' : Valued.v.restrict (z - x) < Valued.v.restrict (algebraMap E (v.adicCompletion E) π) := hz
  rw [Valuation.restrict_lt_iff_lt_embedding, Valuation.embedding_restrict, hv] at hz'
  exact hz'

theorem powerSeries_expansion_image_dense_with_denominator (x : v.adicCompletion E) (hx : x ∈ v.adicCompletionIntegers E) (K : ℕ) :
    ∃ y : 𝓞 E, Valued.v (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y) - x) <
      exp (-(K : ℤ)) := by
  obtain ⟨_, hz, ⟨a, rfl⟩⟩ := mem_closure_iff_nhds.1
    (denseRange_algebraMap (R := 𝓞 E) (K := E) (v := v) x) _ (nhds_lt v x K)
  have hz' : Valued.v (algebraMap E (v.adicCompletion E) a - x) < exp (-(K : ℤ)) := hz
  have hK1 : exp (-(K : ℤ)) ≤ 1 := by
    rw [← exp_zero, exp_le_exp]; omega
  have hx1 : Valued.v x ≤ 1 := hx
  have ha : v.valuation E a ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation']
    change Valued.v (algebraMap E (v.adicCompletion E) a) ≤ 1
    have e : algebraMap E (v.adicCompletion E) a = (algebraMap E (v.adicCompletion E) a - x) + x := by
      ring
    rw [e]
    exact Valuation.map_add_le _ (hz'.le.trans hK1) hx1
  obtain ⟨y, hy⟩ := exists_valuation_sub_lt_of_integer (K := E) v ha
    (Units.mk0 (exp (-(K : ℤ))) exp_ne_zero)
  refine ⟨y, ?_⟩
  have e2 : algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y) - x =
      algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y - a) +
        (algebraMap E (v.adicCompletion E) a - x) := by
    rw [map_sub]; ring
  rw [e2]
  refine Valuation.map_add_lt _ ?_ hz'
  change Valued.v ((algebraMap (𝓞 E) E y - a : E) : v.adicCompletion E) < _
  rw [valuedAdicCompletion_eq_valuation']
  exact hy

section Sig

variable (hv : v.asIdeal.comap (cj E) = v.asIdeal)
include hv

theorem sigK_int (y : 𝓞 E) :
    sigK v hv (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y)) =
      algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E (cj E y)) := by
  rw [sigK_alg v hv]; rfl

theorem alg_int_mem (y : 𝓞 E) :
    algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y) ∈ v.adicCompletionIntegers E := by
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (𝓞 E) E v y

theorem sigK_mem (x : v.adicCompletion E) (hx : x ∈ v.adicCompletionIntegers E) :
    sigK v hv x ∈ v.adicCompletionIntegers E := by
  have hT : {z : v.adicCompletion E | sigK v hv (x - z) ∈ v.adicCompletionIntegers E} ∈ 𝓝 x := by
    have hc : Continuous fun z : v.adicCompletion E => sigK v hv (x - z) :=
      (sigK_cont v hv).comp (continuous_const.sub continuous_id)
    have ho : IsOpen ((v.adicCompletionIntegers E : Set (v.adicCompletion E))) :=
      Valued.isOpen_valuationSubring _
    refine hc.continuousAt.preimage_mem_nhds (ho.mem_nhds ?_)
    rw [sub_self, map_zero]
    exact (v.adicCompletionIntegers E).zero_mem
  obtain ⟨K, hK⟩ := ball_sub v x hT
  obtain ⟨y, hy⟩ := powerSeries_expansion_image_dense_with_denominator v x hx K
  have h1 := hK _ hy.le
  have e : sigK v hv x = sigK v hv (x - algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y)) +
      algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E (cj E y)) := by
    rw [map_sub, sigK_int v hv]; ring
  rw [e]
  exact add_mem h1 (alg_int_mem v hv _)

end Sig

end PI.SqPairLocal.Mdl
end
end

noncomputable section
open NumberField IsDedekindDomain HeightOneSpectrum WithZero IsLocalRing Topology Filter

namespace PI.SqPairLocal.Mdl

open PI.SqPairLocal Formalism.BasicNotions.Examples₂

variable {E : Type} [Field E] [NumberField E] [StarRing E] (v : HeightOneSpectrum (𝓞 E))

theorem intVal_unif {ϖ : 𝓞 E} (h1 : ϖ ∈ v.asIdeal) (h2 : ϖ ∉ v.asIdeal ^ 2) :
    v.intValuation ϖ = exp (-1 : ℤ) := by
  have a1 : v.intValuation ϖ ≤ exp (-((1 : ℕ) : ℤ)) :=
    (intValuation_le_pow_iff_mem v ϖ 1).2 (by rw [pow_one]; exact h1)
  have a2 : ¬ v.intValuation ϖ ≤ exp (-((2 : ℕ) : ℤ)) := fun h =>
    h2 ((intValuation_le_pow_iff_mem v ϖ 2).1 h)
  have h0 : v.intValuation ϖ ≠ 0 := by
    intro h; apply a2; rw [h]; simp
  rw [← exp_log h0] at a1 a2 ⊢
  rw [exp_le_exp] at a1 a2
  congr 1; push_cast at a1 a2; omega

theorem coe_j (r : 𝓞 E) :
    ((algebraMap (𝓞 E) (v.adicCompletionIntegers E) r : v.adicCompletionIntegers E) :
      v.adicCompletion E) = algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E r) := rfl

theorem v_j (r : 𝓞 E) :
    Valued.v ((algebraMap (𝓞 E) (v.adicCompletionIntegers E) r : v.adicCompletionIntegers E) :
      v.adicCompletion E) = v.intValuation r := by
  rw [coe_j]
  have h := v.valuedAdicCompletion_eq_valuation' (algebraMap (𝓞 E) E r)
  rw [v.valuation_of_algebraMap] at h
  exact h

theorem detect_ideal {Q : Ideal (𝓞 E)} [Q.IsPrime] {ϖ : 𝓞 E} (h1 : ϖ ∈ Q) (h2 : ϖ ∉ Q ^ 2)
    (x : 𝓞 E) (K : ℕ) (hx : x ∈ Q ^ K) : ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * x = ϖ ^ K * w := by
  obtain ⟨I, hI⟩ := Ideal.dvd_span_singleton.2 h1
  have hIQ : ¬ I ≤ Q := by
    intro h
    apply h2
    have : Ideal.span {ϖ} ≤ Q ^ 2 := by rw [hI, pow_two]; exact Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self ϖ)
  have hIK : ¬ I ^ K ≤ Q := fun h => hIQ (Ideal.IsPrime.le_of_pow_le h)
  obtain ⟨s, hsI, hsQ⟩ := Set.not_subset.1 hIK
  have hm : s * x ∈ Ideal.span {ϖ ^ K} := by
    rw [← Ideal.span_singleton_pow, hI, mul_pow, mul_comm]
    exact Ideal.mul_mem_mul hsI hx
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hm
  exact ⟨s, hsQ, w, by rw [← hw, mul_comm]⟩

section Sig

variable (hv : v.asIdeal.comap (cj E) = v.asIdeal)

def sigR : v.adicCompletionIntegers E →+* v.adicCompletionIntegers E :=
  (sigK v hv).restrict (v.adicCompletionIntegers E) (v.adicCompletionIntegers E)
    (fun x hx => sigK_mem v hv x hx)

theorem sigR_coe (x : v.adicCompletionIntegers E) :
    ((sigR v hv x : v.adicCompletionIntegers E) : v.adicCompletion E) = sigK v hv x := rfl

theorem sigR_sigR (x : v.adicCompletionIntegers E) : sigR v hv (sigR v hv x) = x :=
  Subtype.ext (by rw [sigR_coe, sigR_coe, sigK_sigK])

def sigO : v.adicCompletionIntegers E ≃+* v.adicCompletionIntegers E :=
  RingEquiv.ofRingHom (sigR v hv) (sigR v hv)
    (RingHom.ext fun x => sigR_sigR v hv x) (RingHom.ext fun x => sigR_sigR v hv x)

theorem sigO_apply (x : v.adicCompletionIntegers E) : sigO v hv x = sigR v hv x := rfl

theorem sigO_sigO (x : v.adicCompletionIntegers E) : sigO v hv (sigO v hv x) = x := by
  rw [sigO_apply, sigO_apply]
  exact sigR_sigR v hv x

theorem j_cj (x : 𝓞 E) :
    algebraMap (𝓞 E) (v.adicCompletionIntegers E) (cj E x) =
      sigO v hv (algebraMap (𝓞 E) (v.adicCompletionIntegers E) x) :=
  Subtype.ext (by rw [sigO_apply, sigR_coe, coe_j, coe_j, sigK_int v hv])

end Sig

theorem modelEx_of (hF : FixedDVR) (hU : RealUnif) : ModelEx := by
  intro E _ _ _ hE Q hQ hcj
  have hQ0 : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQ (RingOfIntegers.not_isField E)
  let v : HeightOneSpectrum (𝓞 E) := ⟨Q, hQ.isPrime, hQ0⟩
  have hv : v.asIdeal.comap (cj E) = v.asIdeal := hcj
  obtain ⟨ϖ, hϖc, hϖQ, hϖ2⟩ := hU E hE Q hQ hcj
  have : v.asIdeal.IsMaximal := hQ
  have : Finite (ResidueField (v.adicCompletionIntegers E)) := adicInt_residue_finite (K := E) v
  have hval : Valued.v ((algebraMap (𝓞 E) (v.adicCompletionIntegers E) ϖ :
      v.adicCompletionIntegers E) : v.adicCompletion E) = exp (-1 : ℤ) := by
    rw [v_j, intVal_unif v hϖQ hϖ2]
  have hirr : Irreducible (algebraMap (𝓞 E) (v.adicCompletionIntegers E) ϖ) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 (adicInt_max_eq_span v _ hval)
  have hσϖ : sigO v hv (algebraMap (𝓞 E) (v.adicCompletionIntegers E) ϖ) =
      algebraMap (𝓞 E) (v.adicCompletionIntegers E) ϖ := by
    rw [← j_cj v hv, hϖc]
  obtain ⟨hd, hh, hf, hirr0⟩ := hF _ (sigO v hv) (sigO_sigO v hv) _ hirr hσϖ
  have hmem : algebraMap (𝓞 E) (v.adicCompletionIntegers E) ϖ ∈ fixSub (sigO v hv) := hσϖ
  obtain ⟨θ, t, ht, hθt⟩ := hE.2.2 Q hQ
  have hθ : cj E θ = t := RingOfIntegers.ext (by rw [cj_coe]; exact ht.symm)
  exact ⟨{
    R := v.adicCompletionIntegers E
    σ := sigO v hv
    σσ := sigO_sigO v hv
    R₀ := fixSub (sigO v hv)
    mem₀ := mem_fixSub _
    dvr := hd
    hens := hh
    fin := hf
    unram := ⟨algebraMap (𝓞 E) (v.adicCompletionIntegers E) θ, by
      rw [← j_cj v hv, ← map_sub, hθ]
      exact adicInt_isUnit_of_not_mem v _ hθt⟩
    j := algebraMap (𝓞 E) (v.adicCompletionIntegers E)
    j_cj := j_cj v hv
    ϖ := ϖ
    ϖ_cj := hϖc
    ϖ_Q := hϖQ
    ϖ_mem := hmem
    ϖ_irr := hirr0 hmem
    unit_of := fun s hs => adicInt_isUnit_of_not_mem v s hs
    dense := by
      intro x K
      obtain ⟨y, hy⟩ := powerSeries_expansion_image_dense_with_denominator v x x.2 K
      have hle : Valued.v ((x - algebraMap (𝓞 E) (v.adicCompletionIntegers E) y :
          v.adicCompletionIntegers E) : v.adicCompletion E) ≤
          Valued.v (((algebraMap (𝓞 E) (v.adicCompletionIntegers E) ϖ) ^ K :
          v.adicCompletionIntegers E) : v.adicCompletion E) := by
        rw [SubmonoidClass.coe_pow, map_pow, hval, ← exp_nsmul, AddSubgroupClass.coe_sub, coe_j,
          Valuation.map_sub_swap]
        refine le_of_lt (lt_of_lt_of_eq hy ?_)
        congr 1; simp
      obtain ⟨z, hz⟩ := (adicInt_dvd_iff v _ _).2 hle
      exact ⟨y, z, hz⟩
    detect := by
      intro x K ⟨z, hz⟩
      have h1 : v.intValuation x ≤ exp (-(K : ℤ)) := by
        rw [← v_j, hz, MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hval]
        calc exp (-1 : ℤ) ^ K * Valued.v (z : v.adicCompletion E)
            ≤ exp (-1 : ℤ) ^ K * 1 := by gcongr; exact z.2
          _ = exp (-(K : ℤ)) := by rw [mul_one, ← exp_nsmul]; congr 1; simp
      have : Q.IsPrime := hQ.isPrime
      exact detect_ideal hϖQ hϖ2 x K ((intValuation_le_pow_iff_mem v x K).1 h1) }⟩

end PI.SqPairLocal.Mdl

namespace PI.SqPairLocal

theorem modelEx_of (hF : FixedDVR) (hU : RealUnif) : ModelEx := Mdl.modelEx_of hF hU

end PI.SqPairLocal
