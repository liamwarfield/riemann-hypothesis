module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatCongrOfAbsNormPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits
open scoped Pointwise

namespace GlobalTheory.Mem.Chr

section General

variable {L : Type} [Field L] [NumberField L]

theorem liesOver_span_of_natCast_mem {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 L)) [P.IsPrime] (h : ((p : ℕ) : 𝓞 L) ∈ P) :
    P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have : Fact p.Prime := ⟨hp⟩
  have hm : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  refine ⟨hm.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  show algebraMap ℤ (𝓞 L) (p : ℤ) ∈ P
  simpa using h

theorem ncard_places_eq_primesOver {p : ℕ} (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal}.ncard =
      ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard := by
  rw [← Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h :
    Function.Injective (HeightOneSpectrum.asIdeal (R := 𝓞 L)))]
  congr 1
  ext P
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, liesOver_span_of_natCast_mem hp _ hv⟩
  · rintro ⟨h1, h2⟩
    have hm : ((p : ℕ) : 𝓞 L) ∈ P := by
      have : (p : ℤ) ∈ P.under ℤ := by rw [← h2.over]; exact Ideal.mem_span_singleton_self _
      simpa using (show algebraMap ℤ (𝓞 L) (p : ℤ) ∈ P from this)
    refine ⟨⟨P, h1, ?_⟩, hm, rfl⟩
    rintro rfl
    exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hm))

theorem splitsC_place [IsGalois ℚ L] {p : ℕ} (hp : p.Prime) (hs : SplitsC L p) (v : HeightOneSpectrum (𝓞 L))
    (hv : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal) :
    Ideal.absNorm v.asIdeal = p ∧ ((p : ℕ) : 𝓞 L) ∉ v.asIdeal ^ 2 ∧
      ∀ σ : L ≃ₐ[ℚ] L, σ • v.asIdeal = v.asIdeal → σ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have := v.isPrime
  have := liesOver_span_of_natCast_mem hp _ hv
  have hm : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have h0 : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by simpa using hp.ne_zero
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 L) (L ≃ₐ[ℚ] L)
  unfold SplitsC at hs
  rw [← ncard_places_eq_primesOver hp, hs, IsGalois.card_aut_eq_finrank] at h1
  have h2 : (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 L) * (Ideal.span {(p : ℤ)}).inertiaDegIn (𝓞 L) = 1 :=
    (mul_eq_left₀ Module.finrank_pos.ne').1 h1
  have h3 := Ideal.card_stabilizer_eq (G := L ≃ₐ[ℚ] L) (Ideal.span {(p : ℤ)}) v.asIdeal
  rw [h2] at h3
  have he := Nat.eq_one_of_mul_eq_one_right h2
  have hf := Nat.eq_one_of_mul_eq_one_left h2
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ v.asIdeal (L ≃ₐ[ℚ] L),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) v.asIdeal h0] at he
  rw [Ideal.inertiaDegIn_eq_inertiaDeg _ v.asIdeal (L ≃ₐ[ℚ] L)] at hf
  refine ⟨?_, ?_, ?_⟩
  · rw [← Ideal.pow_inertiaDeg p v.asIdeal, hf, pow_one]
  · intro h
    refine (Ideal.ramificationIdx'_ne_one_iff ?_).2 ?_ he
    · simpa [Ideal.map_span] using hv
    · simpa [Ideal.map_span] using h
  · intro σ hσ
    have : (MulAction.stabilizer (L ≃ₐ[ℚ] L) v.asIdeal) = ⊥ := Subgroup.card_eq_one.1 h3
    exact Subgroup.mem_bot.1 (this ▸ hσ)

theorem conjPl_iff_smul (σ : L ≃ₐ[ℚ] L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl σ.toRingEquiv v v' ↔ σ • v.asIdeal = v'.asIdeal := by
  rw [conjPl_iff_mem]
  constructor
  · intro h
    ext y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    exact h _ _ (σ.apply_symm_apply (y : L)).symm
  · intro h x y hxy
    have e : y = σ • x := RingOfIntegers.ext hxy
    rw [e, ← h, Ideal.smul_mem_pointwise_smul_iff]

theorem under_smul_of_fix (b : L) (σ : L ≃ₐ[ℚ] L) (h : σ b = b) (P : Ideal (𝓞 L)) :
    (σ • P).under (𝓞 (IntermediateField.adjoin ℚ {b})) = P.under (𝓞 (IntermediateField.adjoin ℚ {b})) := by
  have hfix : ∀ x ∈ IntermediateField.adjoin ℚ {b}, σ x = x := by
    intro x hx
    have : IntermediateField.adjoin ℚ {b} ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
      rintro _ hτ
      have : Subgroup.zpowers σ ≤ MulAction.stabilizer _ b := (Subgroup.zpowers_le).2 h
      exact this hτ
    exact (IntermediateField.mem_fixedField_iff _ _).1 (this hx) σ (Subgroup.mem_zpowers σ)
  ext a
  have e : σ • algebraMap _ (𝓞 L) a = algebraMap _ (𝓞 L) a := RingOfIntegers.ext (hfix _ (a : IntermediateField.adjoin ℚ {b}).2)
  rw [Ideal.mem_under, Ideal.mem_under]
  conv_lhs => rw [← e]
  rw [Ideal.smul_mem_pointwise_smul_iff]

theorem exists_smul_fix_of_under_eq [IsGalois ℚ L] (b : L) (P P' : Ideal (𝓞 L)) [P.IsPrime] [P'.IsPrime]
    (h : P.under (𝓞 (IntermediateField.adjoin ℚ {b})) = P'.under (𝓞 (IntermediateField.adjoin ℚ {b}))) :
    ∃ σ : L ≃ₐ[ℚ] L, σ b = b ∧ σ • P = P' := by
  set K := IntermediateField.adjoin ℚ {b} with hK
  have : P'.LiesOver (P.under (𝓞 K)) := ⟨h⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (P.under (𝓞 K)) P P' (L ≃ₐ[K] L)
  refine ⟨τ.restrictScalars ℚ, τ.commutes (⟨b, IntermediateField.mem_adjoin_simple_self ℚ b⟩ : K), ?_⟩
  rw [← hτ]
  ext y
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem under_eq_iff_under_ne [IsGalois ℚ L] {p : ℕ} (hp : p.Prime) (hs : SplitsC L p) (b : L) (hb0 : b ≠ 0)
    (hb : ∀ σ : L ≃ₐ[ℚ] L, σ b = b ∨ σ b = -b) (c : L ≃ₐ[ℚ] L) (hc : c b = -b)
    (v v' : HeightOneSpectrum (𝓞 L)) (hv : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal) (hvv : c • v.asIdeal = v'.asIdeal)
    (Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin ℚ {b})))
    (hQ : ((p : ℕ) : 𝓞 (IntermediateField.adjoin ℚ {b})) ∈ Q.asIdeal) :
    v.under (𝓞 (IntermediateField.adjoin ℚ {b})) = Q ↔ v'.under (𝓞 (IntermediateField.adjoin ℚ {b})) ≠ Q := by
  have := v.isPrime
  have := v'.isPrime
  constructor
  · rintro rfl h
    obtain ⟨σ, hσb, hσ⟩ := exists_smul_fix_of_under_eq b v.asIdeal v'.asIdeal
      (congrArg HeightOneSpectrum.asIdeal h).symm
    have h1 : σ⁻¹ * c = 1 := (splitsC_place hp hs v hv).2.2 _ (by rw [mul_smul, hvv, ← hσ, inv_smul_smul])
    rw [inv_mul_eq_one] at h1
    rw [h1, hc] at hσb
    exact hb0 (by linear_combination (-1 / 2 : L) * hσb)
  · intro h
    have := Q.isPrime
    obtain ⟨⟨W, hW, hWQ⟩⟩ := (inferInstance : Nonempty (Q.asIdeal.primesOver (𝓞 L)))
    have hpW : ((p : ℕ) : 𝓞 L) ∈ W := by
      rw [hWQ.over, Ideal.mem_under] at hQ
      simpa using hQ
    have := liesOver_span_of_natCast_mem hp _ hv
    have := liesOver_span_of_natCast_mem hp _ hpW
    obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) v.asIdeal W (L ≃ₐ[ℚ] L)
    rcases hb σ with h1 | h1
    · apply HeightOneSpectrum.ext
      rw [hWQ.over, ← hσ, under_smul_of_fix b σ h1]
      rfl
    · exfalso
      apply h
      apply HeightOneSpectrum.ext
      have h2 : (σ * c⁻¹) b = b := by
        have : c⁻¹ b = -b := by
          have h3 : c⁻¹ (c b) = b := c.symm_apply_apply b
          rw [hc, map_neg] at h3
          exact neg_eq_iff_eq_neg.1 h3
        rw [AlgEquiv.mul_apply, this, map_neg, h1, neg_neg]
      have h4 : (σ * c⁻¹) • v'.asIdeal = W := by rw [← hvv, mul_smul, inv_smul_smul, hσ]
      rw [hWQ.over, ← h4, under_smul_of_fix b _ h2]
      rfl

end General


open Classical in
theorem splitsC_main : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → SplitsC H.E p → ∀ v : HeightOneSpectrum (𝓞 H.E), OverP H p v → Ideal.absNorm v.asIdeal = p ∧ ((p : ℕ) : 𝓞 H.E) ∉ v.asIdeal ^ 2 ∧ IsSplitPl H v ∧ ∀ (Q : HeightOneSpectrum (𝓞 H.K)), ((p : ℕ) : 𝓞 H.K) ∈ Q.asIdeal → ∀ v', ConjPl H.conj.toRingEquiv v v' → OverP H p v' ∧ (v.under (𝓞 H.K) = Q ↔ v'.under (𝓞 H.K) ≠ Q) := by
  intro R H p hp hs v hv
  have hG : IsGalois ℚ H.E := H.hostE_isGalois
  have hsq := H.sqrtMinusD_sq
  have hc := H.conj_sqrtMinusD
  have hb0 : H.sqrtMinusD ≠ 0 := by
    intro h
    rw [h] at hsq
    have : (H.d : H.E) = 0 := by linear_combination hsq
    have h1 : H.d = 0 := by exact_mod_cast this
    have := H.qd_big.2
    omega
  have hb : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ H.sqrtMinusD = H.sqrtMinusD ∨ σ H.sqrtMinusD = -H.sqrtMinusD := by
    intro σ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [← map_pow, hsq, map_neg, map_natCast]
  obtain ⟨h1, h2, h3⟩ := splitsC_place hp hs v hv
  refine ⟨h1, h2, ?_, fun Q hQ v' hvv => ⟨?_, ?_⟩⟩
  · by_contra hn
    unfold IsSplitPl at hn
    push Not at hn
    have hle : H.conj • v.asIdeal ≤ v.asIdeal := by
      intro y hy
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
      obtain ⟨z, hz, hzv⟩ := hn _ hy
      have e : z = y := RingOfIntegers.ext (hz.trans (H.conj.apply_symm_apply (y : H.E)))
      exact e ▸ hzv
    obtain ⟨w, hw, -⟩ := existsUnique_conjPl H.conj.toRingEquiv v
    have hw' := (conjPl_iff_smul H.conj v w).1 hw
    have heq : H.conj • v.asIdeal = v.asIdeal := by
      rw [hw'] at hle ⊢
      exact w.isMaximal.eq_of_le v.isPrime.ne_top hle
    rw [h3 _ heq] at hc
    have hc' : H.sqrtMinusD = -H.sqrtMinusD := hc
    exact hb0 (by linear_combination (1 / 2 : H.E) * hc')
  · exact ((conjPl_iff_mem _ v v').1 hvv _ _ (by simp)).1 hv
  · exact under_eq_iff_under_ne hp hs H.sqrtMinusD hb0 hb H.conj hc v v' hv ((conjPl_iff_smul H.conj v v').1 hvv) Q hQ

end GlobalTheory.Mem.Chr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlacePropertiesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
open Neutral.B1 hiding localIdele Ideles diagUnits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completelySplitPrime_host_place_properties : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → SplitsC H.E p → ∀ v : HeightOneSpectrum (𝓞 H.E), OverP H p v → Ideal.absNorm v.asIdeal = p ∧ ((p : ℕ) : 𝓞 H.E) ∉ v.asIdeal ^ 2 ∧ IsSplitPl H v ∧ ∀ (Q : HeightOneSpectrum (𝓞 H.K)), ((p : ℕ) : 𝓞 H.K) ∈ Q.asIdeal → ∀ v', ConjPl H.conj.toRingEquiv v v' → OverP H p v' ∧ (v.under (𝓞 H.K) = Q ↔ v'.under (𝓞 H.K) ≠ Q) := by
  first | exact @GlobalTheory.Mem.Chr.splitsC_main | exact GlobalTheory.Mem.Chr.splitsC_main | (intros; apply GlobalTheory.Mem.Chr.splitsC_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Filter Topology

namespace GlobalTheory.FrobDense

variable {E : Type} [Field E] [NumberField E]

def abv (S : Finset (HeightOneSpectrum (𝓞 E))) : S ⊕ InfinitePlace E → AbsoluteValue E ℝ
  | Sum.inl v => GlobalTheory.LocalQuad.Approx.abv S (Sum.inl v)
  | Sum.inr w => w.1

theorem abv_isNontrivial (S : Finset (HeightOneSpectrum (𝓞 E))) (i : S ⊕ InfinitePlace E) :
    (abv S i).IsNontrivial := by
  rcases i with v | w
  · exact GlobalTheory.LocalQuad.Approx.abv_isNontrivial S (Sum.inl v)
  · exact InfinitePlace.isNontrivial _

theorem abv_not_isEquiv (S : Finset (HeightOneSpectrum (𝓞 E))) (v : S) (w : InfinitePlace E) :
    ¬ (abv S (Sum.inl v)).IsEquiv (abv S (Sum.inr w)) := by
  intro h
  have h1 : abv S (Sum.inl v) ((2 : ℕ) : E) ≤ 1 :=
    NumberField.HeightOneSpectrum.adicAbv_natCast_le_one E v.1 2
  rw [h.le_one_iff] at h1
  have h2 : abv S (Sum.inr w) ((2 : ℕ) : E) = 2 := by
    show w ((2 : ℕ) : E) = 2
    rw [← w.norm_embedding_eq, map_natCast]
    simp
  rw [h2] at h1
  norm_num at h1

theorem abv_pairwise (S : Finset (HeightOneSpectrum (𝓞 E))) :
    Pairwise fun i j ↦ ¬(abv S i).IsEquiv (abv S j) := by
  rintro (v | σ) (w | τ) hne h
  · exact GlobalTheory.LocalQuad.Approx.abv_pairwise S (i := Sum.inl v) (j := Sum.inl w)
      (fun e => hne (congrArg Sum.inl (Sum.inl_injective e))) h
  · exact abv_not_isEquiv S v τ h
  · exact abv_not_isEquiv S w σ h.symm
  · exact hne (congrArg Sum.inr (InfinitePlace.eq_iff_isEquiv.2 h))

abbrev Loc (S : Finset (HeightOneSpectrum (𝓞 E))) : Type :=
  ((w : InfinitePlace E) → w.Completion) × ((v : S) → v.1.adicCompletion E)

def proj (S : Finset (HeightOneSpectrum (𝓞 E))) : AdeleRing (𝓞 E) E →* Loc S where
  toFun a := (fun w => a.1 w, fun v => a.2 v.1)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem denseRange_inf (w : InfinitePlace E) : DenseRange (algebraMap E w.Completion) := by
  refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
  rintro _ ⟨a, rfl⟩
  refine ⟨WithAbs.equiv w.1 a, ?_⟩
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
  simp

theorem norm_inf (w : InfinitePlace E) (x : E) : ‖algebraMap E w.Completion x‖ = w x := by
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
  simpa using InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm x)

theorem denseRange_proj (S : Finset (HeightOneSpectrum (𝓞 E))) :
    DenseRange fun x : E => proj S (algebraMap E (AdeleRing (𝓞 E) E) x) := by
  refine Metric.denseRange_iff.2 fun y ε hε => ?_
  have hε2 : 0 < ε / 2 := half_pos hε
  choose a ha using fun v : S =>
    Metric.denseRange_iff.1 (HeightOneSpectrum.denseRange_algebraMap E v.1) (y.2 v) _ hε2
  choose b hb using fun w : InfinitePlace E =>
    Metric.denseRange_iff.1 (denseRange_inf w) (y.1 w) _ hε2
  obtain ⟨x, hx⟩ := GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt (abv_isNontrivial S) (abv_pairwise S)
    (Sum.elim a b) hε2
  refine ⟨x, ?_⟩
  rw [Prod.dist_eq, max_lt_iff, dist_pi_lt_iff hε, dist_pi_lt_iff hε]
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have h1 : w (b w - x) < ε / 2 := hx (Sum.inr w)
    rw [← norm_inf, map_sub, ← dist_eq_norm] at h1
    have h2 := dist_triangle (y.1 w) (algebraMap E _ (b w)) (algebraMap E _ x)
    have h3 := hb w
    change dist (y.1 w) (algebraMap E _ x) < ε
    linarith
  · have h1 : GlobalTheory.LocalQuad.Approx.abv S (Sum.inl v) (a v - x) < ε / 2 := hx (Sum.inl v)
    rw [GlobalTheory.LocalQuad.Approx.abv_inl, map_sub, ← dist_eq_norm] at h1
    have h2 := dist_triangle (y.2 v) (algebraMap E _ (a v)) (algebraMap E _ x)
    have h3 := ha v
    change dist (y.2 v) (algebraMap E _ x) < ε
    linarith

theorem denseRange_units (S : Finset (HeightOneSpectrum (𝓞 E))) :
    DenseRange fun k : Eˣ => Units.map (proj S) (diagUnits E k) := by
  have hg : IsOpenEmbedding (Units.val : (Loc S)ˣ → Loc S) := Units.isOpenEmbedding_val
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ := (denseRange_proj S).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    exact left_ne_zero_of_mul_eq_one (congrArg (fun y : Loc S => y.1 w) v.mul_inv)
      (congrArg (fun y : Loc S => y.1 w) hk)
  exact ⟨v, hv, Units.mk0 k hk0, Units.ext hk.symm⟩

def incl (S : Finset (HeightOneSpectrum (𝓞 E))) : Loc S →* AdeleRing (𝓞 E) E :=
  MonoidHom.prodMap (MonoidHom.id (InfiniteAdeleRing E))
    (∏ v : S, (Neutral.B1.finiteSingle E v.1).comp (Pi.evalMonoidHom (fun v : S => v.1.adicCompletion E) v))

theorem incl_snd (S : Finset (HeightOneSpectrum (𝓞 E))) (y : Loc S) :
    (incl S y).2 = ∏ v : S, Neutral.B1.finiteSingle E v.1 (y.2 v) :=
  MonoidHom.finsetProd_apply _ _ _

theorem continuous_incl (S : Finset (HeightOneSpectrum (𝓞 E))) : Continuous (incl S) := by
  refine Continuous.prodMk continuous_fst (?_ : Continuous fun y => (incl S y).2)
  simp only [incl_snd]
  exact continuous_finsetProd _ fun v _ =>
    (GlobalTheory.Mem.UnrAe.continuous_finSingle v.1).comp ((continuous_apply v).comp continuous_snd)

theorem incl_apply (S : Finset (HeightOneSpectrum (𝓞 E))) (y : Loc S) (v : S) : (incl S y).2 v.1 = y.2 v := by
  classical
  let e : FiniteAdeleRing (𝓞 E) E →* v.1.adicCompletion E :=
    (GlobalTheory.Mem.LocTriv.ev v.1).comp (MonoidHom.inr (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
  show e (incl S y).2 = _
  rw [incl_snd, map_prod, Finset.prod_eq_single_of_mem v (Finset.mem_univ v)]
  · exact Function.update_self v.1 (y.2 v) (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E))
  · intro w _ hw
    exact Function.update_of_ne (fun h => hw (Subtype.ext h.symm)) (y.2 w)
      (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E))

theorem proj_incl (S : Finset (HeightOneSpectrum (𝓞 E))) (y : Loc S) : proj S (incl S y) = y :=
  Prod.ext rfl (funext fun v => incl_apply S y v)

variable {B : Type} [CommGroup B] [TopologicalSpace B] [T2Space B]


open GlobalTheory.Mem.LocTriv GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.IdlFact in
theorem eq_one_of_local (ψ : Mem.Chr.Ideles E →* B) (hψ : Continuous ψ) (a : Mem.Chr.Ideles E)
    (h1 : (a : AdeleRing (𝓞 E) E).1 = 1) (hl : ∀ v, ψ (Mem.Chr.localIdele E v (Units.map (ev v) a)) = 1) : ψ a = 1 := by
  have hp : ∀ (c : Mem.Chr.Ideles E) T, (∀ v, ψ (Mem.Chr.localIdele E v (Units.map (ev v) c)) = 1) → ψ (part c T) = 1 :=
    fun c T hc => by
      rw [part, map_prod]
      exact Finset.prod_eq_one fun v _ => hc v
  let T := (finite_valAt_ne_one a).toFinset
  let b := part a⁻¹ T * a
  have hb1 : ∀ v ∈ T, ev v (b : AdeleRing (𝓞 E) E) = 1 := fun v hv => by
    simp only [b]
    rw [Units.val_mul, map_mul, ev_part_mem _ hv, ← map_mul, Units.inv_mul, map_one]
  have hb2 : ∀ v ∉ T, ev v (b : AdeleRing (𝓞 E) E) = ev v (a : AdeleRing (𝓞 E) E) := fun v hv => by
    simp only [b]
    rw [Units.val_mul, map_mul, ev_part_not_mem _ hv, one_mul]
  have hbu : b ∈ unitIdl E := fun v => by
    show Valued.v (ev v (b : AdeleRing (𝓞 E) E)) = 1
    by_cases hv : v ∈ T
    · rw [hb1 v hv, map_one]
    · rw [hb2 v hv]
      have h : valAt v a = 1 := by simpa [T] using hv
      exact h
  have hbi : (b : AdeleRing (𝓞 E) E).1 = 1 := by
    show (part a⁻¹ T : AdeleRing (𝓞 E) E).1 * (a : AdeleRing (𝓞 E) E).1 = 1
    rw [part_fst, h1, one_mul]
  have hbl : ∀ v, ψ (Mem.Chr.localIdele E v (Units.map (ev v) b)) = 1 := fun v => by
    by_cases hv : v ∈ T
    · rw [show Units.map (ev v) b = 1 from Units.ext (hb1 v hv), map_one, map_one]
    · rw [show Units.map (ev v) b = Units.map (ev v) a from Units.ext (hb2 v hv), hl]
  have t := (hψ.tendsto b).comp (tendsto_part hbu fun w => congrFun hbi w)
  rw [show ψ ∘ part b = fun _ => 1 from funext fun S => hp b S hbl] at t
  have hb : ψ b = 1 := tendsto_nhds_unique t tendsto_const_nhds
  simp only [b] at hb
  rwa [← part_inv, map_mul, map_inv, hp a T hl, inv_one, one_mul] at hb


open GlobalTheory.Mem.LocTriv in
theorem eq_one_of_away (ψ : Ideles E →* B) (hψ : Continuous ψ) (hd : ∀ k, ψ (diagUnits E k) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ v ∉ S, ∀ x, ψ (localIdele E v x) = 1) : ψ = 1 := by
  have h0 : ∀ a : Ideles E, Units.map (proj S) a = 1 → ψ a = 1 := fun a ha => by
    have e : proj S (a : AdeleRing (𝓞 E) E) = 1 := congrArg Units.val ha
    refine eq_one_of_local ψ hψ a (congrArg Prod.fst e) fun v => ?_
    by_cases hv : v ∈ S
    · rw [show Units.map (ev v) a = 1 from Units.ext (congrFun (congrArg Prod.snd e) ⟨v, hv⟩), map_one, map_one]
    · exact hS v hv _
  have h1 : ∀ a : Ideles E, ψ (Units.map (incl S) (Units.map (proj S) a)) = ψ a := fun a => by
    rw [← div_eq_one, ← map_div]
    refine h0 _ ?_
    rw [map_div, div_eq_one]
    exact Units.ext (proj_incl S _)
  have h2 : ∀ y, ψ (Units.map (incl S) y) = 1 := fun y =>
    (denseRange_units S).induction_on (p := fun y => ψ (Units.map (incl S) y) = 1) y
      (isClosed_eq (hψ.comp ((continuous_incl S).units_map _)) continuous_const) fun k => (h1 _).trans (hd k)
  ext a
  rw [← h1, h2, MonoidHom.one_apply]


omit [TopologicalSpace B] [T2Space B] in
theorem eq_one_of_unif {v : HeightOneSpectrum (𝓞 E)} (θ : (v.adicCompletion E)ˣ →* B)
    (h : ∀ x, IsUnifAt v x → θ x = 1) (x : (v.adicCompletion E)ˣ) : θ x = 1 := by
  obtain ⟨k, hk⟩ := exists_unif v
  generalize atFin v k = p at hk
  have hk' : Valued.v (p : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := hk
  have hx : Valued.v (x : v.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
  have hu : IsUnifAt v (x * p ^ (WithZero.log (Valued.v (x : v.adicCompletion E)) + 1)) := by
    show Valued.v _ = _
    rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hk', ← WithZero.exp_zsmul]
    nth_rewrite 1 [← WithZero.exp_log hx]
    rw [← WithZero.exp_add]
    congr 1
    simp
  have := h _ hu
  rwa [map_mul, map_zpow, h p hk, one_zpow, mul_one] at this

theorem eq_one_of_frob : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (B : Type) [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B] (φ : G E Ω →* B), Continuous φ → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), (∀ v, v ∉ S → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ : G E Ω, IsFrob (F := E) A (normV v) σ → φ σ = 1) → φ = 1 := by
  intro E Ω _ _ _ _ _ art ha B _ _ _ _ φ hφ S hS
  have h : (liftAb φ hφ).comp art = 1 := by
    refine eq_one_of_away _ ((continuous_liftAb φ hφ).comp ha.quot.continuous) (fun k => ?_) S fun v hv => ?_
    · have hk : diagUnits E k ∈ art.ker := by
        rw [ha.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
      rw [MonoidHom.comp_apply, MonoidHom.mem_ker.mp hk, map_one]
    · refine eq_one_of_unif (((liftAb φ hφ).comp art).comp (localIdele E v)) fun x hx => ?_
      obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
      obtain ⟨σ, hσ, e⟩ := (ha.frob v A hA _).mp ⟨x, hx, rfl⟩
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← e, liftAb_toAb, map_inv, hS v hv A hA σ hσ, inv_one]
  ext σ
  obtain ⟨x, hx⟩ := ha.quot.surjective (toAb E Ω σ)
  rw [← liftAb_toAb φ hφ, ← hx]
  exact DFunLike.congr_fun h x

end GlobalTheory.FrobDense
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem.FieldsLaws

open Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} (H : Host R)

theorem galE_sigmaOf (g : R.GG) : H.galE (H.sigmaOf g) = g :=
  (H.gal).apply_symm_apply g

theorem sigmaOf_galE (σ : H.E ≃ₐ[ℚ] H.E) : H.sigmaOf (H.galE σ) = σ :=
  (H.gal).symm_apply_apply σ

theorem gal_comm (s t : H.E ≃ₐ[ℚ] H.E) : s * t = t * s := by
  apply (H.gal).injective
  rw [map_mul, map_mul, mul_comm]

theorem mem_K_iff (x : H.E) : x ∈ H.K ↔ ∀ τ : R.Psi, H.sigmaOf τ x = x := by
  have hG : IsGalois ℚ H.E := H.hostE_isGalois
  have key : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ H.K.fixingSubgroup ↔ H.galE σ ∈ R.Psi := by
    intro σ
    rw [H.galE_mem_Psi_iff, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h
      exact h _ (IntermediateField.mem_adjoin_simple_self ℚ _)
    · intro h y hy
      have hle : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
        refine IntermediateField.adjoin_simple_le_iff.2 ?_
        rw [IntermediateField.mem_fixedField_iff]
        intro f hf
        have : Subgroup.zpowers σ ≤ MulAction.stabilizer _ (H.sqd) := by
          rw [Subgroup.zpowers_le]
          exact h
        exact this hf
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hy) σ (Subgroup.mem_zpowers σ)
  constructor
  · intro hx τ
    have h : H.sigmaOf τ ∈ H.K.fixingSubgroup := by
      rw [key, galE_sigmaOf]
      exact τ.2
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 h x hx
  · intro hx
    rw [← IsGalois.fixedField_fixingSubgroup H.K, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have := hx ⟨_, (key σ).1 hσ⟩
    rwa [sigmaOf_galE] at this

theorem unram (P : HeightOneSpectrum (𝓞 H.E)) :
    ¬ (P.asIdeal.comap (algebraMap (𝓞 H.F) (𝓞 H.E))).map (algebraMap (𝓞 H.F) (𝓞 H.E)) ≤ P.asIdeal ^ 2 := by
  have hcm : IsCMField H.E := H.isCMField_hostE
  intro hle
  obtain ⟨π, hπ⟩ := (P.under (𝓞 H.F)).intValuation_exists_uniformizer
  have hmem : π ∈ (P.under (𝓞 H.F)).asIdeal := by
    have := ((P.under (𝓞 H.F)).intValuation_le_pow_iff_mem π 1).1 (by rw [hπ]; simp)
    rwa [pow_one] at this
  have h2 : algebraMap (𝓞 H.F) (𝓞 H.E) π ∈ P.asIdeal ^ 2 := hle (Ideal.mem_map_of_mem _ hmem)
  have h3 := (P.intValuation_le_pow_iff_mem _ 2).2 h2
  have h4 := HostCM.valuation_eq_of_unram H.E (fun P hP h0 h =>
    H.der.unramEF P hP h0 fun x => by
      have hx : H.conj • x = IsCMField.complexConj H.E • x :=
        RingOfIntegers.ext (H.φ₀.injective ((H.conjE_apply H.φ₀ x).trans
          (IsCMField.complexEmbedding_complexConj H.E H.φ₀ x).symm))
      rw [hx]
      exact h x) P (π : H.F)
  have h5 : P.valuation H.E (algebraMap (𝓞 H.E) H.E (algebraMap (𝓞 H.F) (𝓞 H.E) π)) =
      (P.under (𝓞 H.F)).valuation H.F (algebraMap (𝓞 H.F) H.F π) := h4
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hπ] at h5
  rw [h5, WithZero.exp_le_exp] at h3
  omega

end Host

variable (B : Base)

theorem embLL_comp_embBar (τ : Tau B.R) :
    B.embLL.comp (B.fields.embBar τ) = B.host.emb ((τ : B.R.GG) * B.R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp, ← B.fields_embC]
  refine RingHom.ext fun x => ?_
  exact congrArg (fun y => B.embLL (B.tauLL τ y)) (B.fields_sig x)

theorem embLL_comp_emb (τ : Tau B.R) : B.embLL.comp (B.fields.emb τ) = B.host.emb (τ : B.R.GG) :=
  B.fields_embC τ

theorem mem_Kq_iff (x : B.host.E) : x ∈ B.fields.Kq ↔ x ∈ B.host.K := by
  rw [mem_K_iff]
  constructor
  · intro h τ
    have h1 := B.embE.injective (h τ (1 : B.R.Psi))
    have h2 : B.host.sigmaOf ((1 : B.R.Psi) : B.R.GG) = 1 := map_one (B.host.gal).symm
    have h3 : B.host.sigmaOf τ x = B.host.sigmaOf ((1 : B.R.Psi) : B.R.GG) x := h1
    rw [h3, h2]
    rfl
  · intro h τ τ'
    rw [B.fields_emb_apply, B.fields_emb_apply, h τ, h τ']

theorem fields_ok : B.fields.Ok := by
  have hcm : IsCMField B.host.E := B.host.isCMField_hostE
  letI := B.host.cmStar
  have cm := host_cmData B.R B.host
  have hinj : ∀ {φ ψ : B.host.E →+* B.LL}, B.embLL.comp φ = B.embLL.comp ψ → φ = ψ := fun h =>
    RingHom.ext fun x => B.embLL.injective (RingHom.congr_fun h x)
  refine
    { realF := cm.totReal
      rankE := cm.deg2
      star_F := fun x => (cm.fixed _).2 ⟨x, rfl⟩
      conjE := fun φ x => ?_
      cplxE := inferInstanceAs (IsTotallyComplex B.host.E)
      emb_star := fun τ x => ?_
      card_Tau := ?_
      emb_inj := fun τ τ' h => ?_
      emb_ne := fun τ τ' h => ?_
      emb_all := fun φ => ?_
      cplxK := ?_
      normalK := inferInstanceAs (Normal ℚ B.LL)
      conjK := ⟨B.embLL, B.starLL_cx⟩
      quad := ?_ }
  · exact (congrArg φ (B.fields_star x)).trans (B.host.conjE_apply φ x)
  · apply B.embLL.injective
    rw [B.starLL_cx]
    exact (congrArg (B.embLL.comp (B.tauLL τ)) (B.fields_star x)).trans (B.host.conjE_apply (B.embLL.comp (B.tauLL τ)) x)
  · refine (card_Tau B.host).trans (Eq.trans ?_ (B.host.finrank_hostF).symm)
    rfl
  · have h1 := congrArg B.embLL.comp h
    rw [embLL_comp_emb, embLL_comp_emb] at h1
    exact Subtype.ext ((factEmb B.R B.host).1.1 h1)
  · have h1 := congrArg B.embLL.comp h
    rw [embLL_comp_emb, embLL_comp_embBar] at h1
    have h2 := (factEmb B.R B.host).1.1 h1
    exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 τ'.2 (h2 ▸ τ.2)
  · obtain ⟨g, hg⟩ := (factEmb B.R B.host).1.2 (B.embLL.comp φ)
    by_cases h : g ∈ B.R.Psi
    · exact ⟨⟨g, h⟩, Or.inl (hinj (by rw [← hg]; exact (embLL_comp_emb B ⟨g, h⟩).symm))⟩
    · have hcc : B.R.cc * B.R.cc = 1 := B.R.cc_mul_cc
      have h' : g * B.R.cc ∈ B.R.Psi := by
        rw [Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem, mul_assoc, hcc, mul_one]
        exact h
      refine ⟨⟨_, h'⟩, Or.inr (hinj ?_)⟩
      rw [← hg, embLL_comp_embBar B ⟨_, h'⟩]
      show _ = B.host.emb (g * B.R.cc * B.R.cc)
      rw [mul_assoc, hcc, mul_one]
  · letI : Algebra B.host.E B.LL := B.embE.toAlgebra
    exact isTotallyComplex_of_algebra B.host.E B.LL
  · let e : B.fields.Kq ≃+* B.host.K :=
      RingEquiv.subringCongr (s := B.fields.Kq.toSubring) (t := B.host.K.toSubfield.toSubring)
        (Subring.ext fun x => mem_Kq_iff B x)
    rw [← SplitK.finrank_K B.host.hyp.2.1.pos B.host.sqrtMinusD_sq]
    exact (AlgEquiv.ofRingEquiv (R := ℚ) (f := e) (fun r => map_ratCast e r)).toLinearEquiv.finrank_eq

theorem fields_satisfy_definite_laws : ∀ B : Base, B.fields.AbelianUnramifiedExtensionConditions ∧ B.fields.f = B.R.f := by
  intro B
  refine ⟨⟨fields_ok B, ?_, B.host.hostE_isGalois, gal_comm B.host, unram B.host⟩, B.fields_f⟩
  rw [B.fields_f]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le B.host.two_le_e
  obtain ⟨m, hm⟩ := B.R.two_pow_dvd_ord
  refine ⟨2 ^ k * m, ?_⟩
  show 2 * B.R.ord = _
  rw [hm, hk]
  ring

end GlobalTheory.Mem.FieldsLaws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLawsStatement
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_fields_definite_laws : ∀ B : Base, B.fields.AbelianUnramifiedExtensionConditions ∧ B.fields.f = B.R.f := by
  first | exact @GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws | exact GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws | (intros; apply GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqOfMapEq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits

namespace GlobalTheory.Mem.GoodPlace

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem plc_eq_absNorm (v : HeightOneSpectrum (𝓞 F)) (h : (Ideal.absNorm v.asIdeal).Prime) :
    Formalism.EigenvalueLevelCeiling.plc v = Ideal.absNorm v.asIdeal := by
  have := v.isPrime
  have : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top
  unfold Formalism.EigenvalueLevelCeiling.plc
  apply CharP.ringChar_of_prime_eq_zero h
  rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.absNorm_mem _

theorem absNorm_map (h2 : Module.finrank F E = 2) (I : Ideal (𝓞 F)) :
    Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) I) = Ideal.absNorm I ^ 2 := by
  rw [Ideal.absNorm_algebraMap, ← h2]
  congr 1
  exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E).symm

theorem absNorm_under_dvd (P : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm (P.under (𝓞 F)).asIdeal ∣ Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact AddSubgroup.card_dvd_of_injective
    (Ideal.quotientMap P.asIdeal (algebraMap (𝓞 F) (𝓞 E)) le_rfl).toAddMonoidHom Ideal.quotientMap_injective

theorem of_split (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hv : Formalism.L2.DIV.DegOne v)
    {Q Q' : HeightOneSpectrum (𝓞 E)} (hne : Q ≠ Q')
    (hm : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * Q'.asIdeal) (hQ : Q.under (𝓞 F) = v) :
    Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 := by
  have hN : Ideal.absNorm Q.asIdeal * Ideal.absNorm Q'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← map_mul, ← hm, absNorm_map h2]
  have h1 : Ideal.absNorm Q.asIdeal ≠ 1 := fun h => Q.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h1' : Ideal.absNorm Q'.asIdeal ≠ 1 := fun h => Q'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  refine ⟨((Nat.Prime.mul_eq_prime_sq_iff hv.1 h1 h1').1 hN).1, ?_⟩
  intro hmem
  have hqv : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
  obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)} :=
    Ideal.dvd_span_singleton.2 hqv
  have hd : Q.asIdeal ^ 2 ∣ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)}) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact Ideal.dvd_span_singleton.2 hmem
  rw [hI, Ideal.map_mul, hm, pow_two, mul_assoc, mul_dvd_mul_iff_left Q.ne_bot] at hd
  rcases (Ideal.prime_of_isPrime Q.ne_bot Q.isPrime).dvd_or_dvd hd with h | h
  · exact hne (HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le Q.isPrime.ne_top (Ideal.le_of_dvd h)).symm)
  · have hle : I ≤ v.asIdeal := by
      rw [← hQ]
      exact Ideal.map_le_iff_le_comap.1 (Ideal.le_of_dvd h)
    apply hv.2
    rw [← Ideal.span_singleton_le_iff_mem, hI, pow_two]
    exact Ideal.mul_mono_right hle

theorem under_eq_of_map_eq {v : HeightOneSpectrum (𝓞 F)} {Q : HeightOneSpectrum (𝓞 E)} {J : Ideal (𝓞 E)}
    (hm : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * J) : Q.under (𝓞 F) = v := by
  refine (HeightOneSpectrum.ext (v.isMaximal.eq_of_le (Q.under (𝓞 F)).isPrime.ne_top ?_)).symm
  exact Ideal.map_le_iff_le_comap.1 (hm ▸ Ideal.mul_le_left)

theorem map_eq_mul (h2 : Module.finrank F E = 2) {P P' : HeightOneSpectrum (𝓞 E)} (hne : P ≠ P')
    (hu : P'.under (𝓞 F) = P.under (𝓞 F)) :
    Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal = P.asIdeal * P'.asIdeal := by
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal ≤ P.asIdeal * P'.asIdeal := by
    rw [Ideal.mul_eq_inf_of_isCoprime (HeightOneSpectrum.isCoprime_of_ne P P' hne)]
    refine le_inf Ideal.map_comap_le ?_
    rw [← hu]
    exact Ideal.map_comap_le
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hN := absNorm_map h2 (P.under (𝓞 F)).asIdeal
  obtain ⟨a, ha⟩ := absNorm_under_dvd (F := F) P
  obtain ⟨b, hb⟩ := absNorm_under_dvd (F := F) P'
  rw [hu] at hb
  have h0 : Ideal.absNorm (P.under (𝓞 F)).asIdeal ≠ 0 := fun h => (P.under (𝓞 F)).ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  rw [hJ, map_mul, map_mul, ha, hb] at hN
  have h3 : (a * b) * Ideal.absNorm J = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 h0)
    rw [mul_one]
    refine Eq.trans ?_ hN
    ring
  rw [hJ, Ideal.absNorm_eq_one_iff.1 (Nat.eq_one_of_mul_eq_one_left h3), Ideal.mul_top]

theorem goodPl_iff (h2 : Module.finrank F E = 2) (S : Set ℕ) (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.L2.DIV.GoodPl E S (P.under (𝓞 F)) ↔ ((∃ P', P ≠ P' ∧ P'.under (𝓞 F) = P.under (𝓞 F)) ∧
      (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 ∧
      Ideal.absNorm P.asIdeal ∉ S) := by
  constructor
  · rintro ⟨⟨Q, Q', hne, hm⟩, hv, hS⟩
    obtain ⟨P', hne', hm'⟩ : ∃ P', P ≠ P' ∧
        Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal = P.asIdeal * P'.asIdeal := by
      have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
        rw [← hm]
        exact Ideal.map_comap_le
      rcases P.isPrime.mul_le.1 hle with h | h
      · obtain rfl : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)
        exact ⟨Q', hne, hm⟩
      · obtain rfl : Q' = P := HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le P.isPrime.ne_top h)
        exact ⟨Q, hne.symm, by rw [hm, mul_comm]⟩
    obtain ⟨e, hn⟩ := of_split h2 hv hne' hm' rfl
    rw [plc_eq_absNorm _ hv.1] at hS
    rw [e]
    exact ⟨⟨P', hne', under_eq_of_map_eq (hm'.trans (mul_comm _ _))⟩, hv.1, hn, hS⟩
  · rintro ⟨⟨P', hne, hu⟩, hp, hn, hS⟩
    have e : Ideal.absNorm (P.under (𝓞 F)).asIdeal = Ideal.absNorm P.asIdeal :=
      ((Nat.dvd_prime hp).1 (absNorm_under_dvd P)).resolve_left fun h =>
        (P.under (𝓞 F)).isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    refine ⟨⟨P, P', hne, map_eq_mul h2 hne hu⟩, ⟨e ▸ hp, fun h => hn ?_⟩, ?_⟩
    · rw [e] at h
      have h3 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h
      rw [map_natCast, Ideal.map_pow] at h3
      exact Ideal.pow_right_mono Ideal.map_comap_le 2 h3
    · rw [plc_eq_absNorm _ (e ▸ hp), e]
      exact hS

end General

theorem isSplitPl_iff {R : Ranks} (H : Formalism.BasicNotions.Host R) (P : HeightOneSpectrum (𝓞 H.E)) :
    IsSplitPl H P ↔ ∃ P', P ≠ P' ∧ P'.under (𝓞 H.F) = P.under (𝓞 H.F) := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨P', hP', -⟩ := existsUnique_conjPl c.toRingEquiv P
    refine ⟨P', ?_, (under_eq_iff_conjPl c hcm.rank hcm.ne P P').2 (Or.inr hP')⟩
    rintro rfl
    exact hy (RingOfIntegers.mapRingEquiv c.toRingEquiv x) (hc x) (((conjPl_iff_mem _ P P).1 hP' x _ rfl).1 hx)
  · rintro ⟨P', hne, hu⟩
    have hP' := ((under_eq_iff_conjPl c hcm.rank hcm.ne P P').1 hu).resolve_left hne.symm
    rw [conjPl_iff_mem] at hP'
    by_contra hn
    unfold IsSplitPl at hn
    push Not at hn
    refine hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top fun y hy => ?_).symm)
    have hxy : (y : H.E) = c.toRingEquiv ((RingOfIntegers.mapRingEquiv c.toRingEquiv).symm y : 𝓞 H.E) :=
      congrArg (fun z : 𝓞 H.E => (z : H.E)) ((RingOfIntegers.mapRingEquiv c.toRingEquiv).apply_symm_apply y).symm
    obtain ⟨z, hz, hzP⟩ := hn _ ((hP' _ y hxy).2 hy)
    have e : z = y := RingOfIntegers.ext (hz.trans ((hc _).symm.trans hxy.symm))
    exact e ▸ hzP


open Classical in
theorem goodPl_under_iff : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (S : Set ℕ) (P : HeightOneSpectrum (𝓞 H.E)), Formalism.L2.DIV.GoodPl H.E S (P.under (𝓞 H.F)) ↔ (IsSplitPl H P ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 H.E) ∉ P.asIdeal ^ 2 ∧ Ideal.absNorm P.asIdeal ∉ S) := by
  intro R H S P
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  rw [isSplitPl_iff]
  exact goodPl_iff hcm.rank S P

end GlobalTheory.Mem.GoodPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LPrjSurjective
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory.Mem.LiftProjOnto

theorem lPrj_surjective : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (k : Fin D.R.m) (t : T) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : (Fin (lDim D A P ψ k t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] W) (op : W →ₗ[ℂ] W), A.fam.Ok 1 → FormsTie D.what₂.embLL j (lH D A P ψ k t) (lE D A P ψ k t) op → Function.Surjective (lPrj D A P ψ Zs k t).mulVec := by
  intro D G _ _ Pl0 T A P ψ Zs k t W _ _ j op hOk _
  have hB : BlockHyp (A.fam.L k t) (A.fam.lvlA P ψ) A.v0 1 := ⟨hOk.conj, hOk.irr, hOk.lifts k t⟩
  exact BlockDat.lf_lPr_surj (Z := Zs.Zl k t) hB

end GlobalTheory.Mem.LiftProjOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPowUnitsOfUnderEq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
open Neutral.B1 hiding localIdele Ideles diagUnits

namespace GlobalTheory.Mem.Chr

theorem twist_pow_units_of_under_eq : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (S : Set ℕ) (ξ : HChar H.E), IsTwist H S ξ → ∀ (Q Q' : HeightOneSpectrum (𝓞 H.E)), Q.under (𝓞 H.F) = Q'.under (𝓞 H.F) → ∀ n : ℕ, (∀ x, IsUnitAt Q' x → ξ.loc Q' x ^ n = 1) → ∀ x, IsUnitAt Q x → ξ.loc Q x ^ n = 1 := by
  intro R H S ξ hξ Q Q' hu n hn x hx
  by_cases hQ : Q = Q'
  · subst hQ
    exact hn x hx
  by_cases hur : ξ.UnrAt Q
  · rw [hur x hx, one_pow]
  obtain ⟨-, htriv, htame, hram⟩ := hξ
  obtain ⟨-, hq, -, -⟩ := hram Q hur
  obtain ⟨a, k, hcop, hk, hcong⟩ := (GlobalTheory.localUnit_congr_global H.E Q x hx).2 _ hq rfl
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hqQ : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.E) ∈ Q.asIdeal := Ideal.absNorm_mem Q.asIdeal
  have hqQ' : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.E) ∈ Q'.asIdeal := by
    have h1 : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.F) ∈ (Q.under (𝓞 H.F)).asIdeal := by
      show algebraMap (𝓞 H.F) (𝓞 H.E) _ ∈ Q.asIdeal
      rw [map_natCast]
      exact hqQ
    rw [hu] at h1
    have h2 : algebraMap (𝓞 H.F) (𝓞 H.E) ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.F) ∈ Q'.asIdeal := h1
    rwa [map_natCast] at h2
  have hkQ : IsUnitAt Q (atFin Q k) := isUnitAt_nat (H := H) hqQ hcop hk
  have hkQ' : IsUnitAt Q' (atFin Q' k) := isUnitAt_nat (H := H) hqQ' hcop hk
  have hxk : IsUnitAt Q (x * (atFin Q k)⁻¹) := by
    unfold IsUnitAt at hx hkQ ⊢
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, hkQ, inv_one, one_mul]
  have h1 : ξ.loc Q (x * (atFin Q k)⁻¹) = 1 := htame Q _ hxk (by simpa using hcong)
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  have ha0 : (a : H.F) ≠ 0 := by
    intro h
    have h0 : a = 0 := by exact_mod_cast h
    apply k.ne_zero
    rw [hk, h0, Nat.cast_zero]
  have hup : upF H.F (Units.mk0 (a : H.F) ha0) = k := by
    apply Units.ext
    rw [hk]
    exact map_natCast (algebraMap H.F H.E) a
  have hab : aboveF (L := H.E) H.F (Q.under (𝓞 H.F)) = {Q, Q'} := by
    have hc' : ConjPl c.toRingEquiv Q Q' :=
      ((under_eq_iff_conjPl c hcm.rank hcm.ne Q Q').1 hu.symm).resolve_left (Ne.symm hQ)
    ext P
    have hm : P ∈ aboveF (L := H.E) H.F (Q.under (𝓞 H.F)) ↔ P.under (𝓞 H.F) = Q.under (𝓞 H.F) := by
      unfold aboveF
      rw [Set.Finite.mem_toFinset]
      rfl
    rw [hm, under_eq_iff_conjPl c hcm.rank hcm.ne Q P, Finset.mem_insert, Finset.mem_singleton]
    refine or_congr Iff.rfl ⟨fun h => (existsUnique_conjPl _ Q).unique h hc', ?_⟩
    rintro rfl
    exact hc'
  have h2 := htriv.1 (Q.under (𝓞 H.F)) (Units.mk0 (a : H.F) ha0)
  rw [HChar.resFin_apply, hab, Finset.prod_pair hQ, hup] at h2
  have h3 : ξ.loc Q (atFin Q k) * ξ.loc Q' (atFin Q' k) = 1 := h2
  have h4 := congrArg (· ^ n) h3
  simp only [mul_pow, hn _ hkQ', mul_one, one_pow] at h4
  rw [h1, h4]

end GlobalTheory.Mem.Chr
end
