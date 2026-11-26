module

public import ReciprocityTheory.GaloisValuations.ArithOfA
public import ReciprocityTheory.ResidueCardinality.ArtinOntoB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplit

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LocDegOneBelow
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ValNatCastOf
noncomputable section

namespace MassDataIdxRes

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem val_natCast_of (g : ℕ) (hg1 : (g : 𝓞 F) ∈ v.asIdeal) (hg2 : (g : 𝓞 F) ∉ v.asIdeal ^ 2) :
    Valued.v (((g : v.adicCompletionIntegers F) : v.adicCompletion F)) = WithZero.exp (-1 : ℤ) := by
  have h0 : (g : 𝓞 F) ≠ 0 := fun h => hg2 (by rw [h]; exact zero_mem _)
  have key := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (g : 𝓞 F)
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] at key
  have e : (((g : v.adicCompletionIntegers F) : v.adicCompletion F)) =
      algebraMap (𝓞 F) (v.adicCompletion F) (g : 𝓞 F) := by
    rw [map_natCast]
    simp
  rw [e, show Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (g : 𝓞 F)) = v.intValuation (g : 𝓞 F) from key]
  have h1 : v.intValuation (g : 𝓞 F) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hg1)
  have h2 : ¬ v.intValuation (g : 𝓞 F) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => hg2 ((v.intValuation_le_pow_iff_mem _ 2).1 h)
  have hne : v.intValuation (g : 𝓞 F) ≠ 0 := by
    exact v.intValuation_ne_zero _ h0
  rw [← WithZero.exp_log hne] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  push_cast at h1 h2
  omega

theorem resZ_of (g : ℕ) [hgp : Fact g.Prime] (hcard : Nat.card (𝓞 F ⧸ v.asIdeal) = g)
    (hg1 : (g : 𝓞 F) ∈ v.asIdeal) (hg2 : (g : 𝓞 F) ∉ v.asIdeal ^ 2) :
    ∃ π : v.adicCompletionIntegers F →+* ZMod g, Function.Surjective π ∧
      RingHom.ker π = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} := by
  have hv := val_natCast_of v g hg1 hg2
  have hmax := ReciprocityTheory.Aut.maxIdeal_eq_span (F := F) (v := v)
    (π := ((g : ℕ) : v.adicCompletionIntegers F)) hv
  have hc : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = g := by
    rw [ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue, hcard]
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact hgp.out.ne_zero)
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers F))
  let e := ZMod.ringEquivOfPrime (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) hgp.out
    (by rw [← Nat.card_eq_fintype_card]; exact hc)
  refine ⟨(e.symm : IsLocalRing.ResidueField (v.adicCompletionIntegers F) →+* ZMod g).comp
    (IsLocalRing.residue _), e.symm.surjective.comp IsLocalRing.residue_surjective, ?_⟩
  ext x
  rw [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.coe_toRingHom, EmbeddingLike.map_eq_zero_iff,
    IsLocalRing.residue_eq_zero_iff, hmax]

end MassDataIdxRes

namespace MassDataIdxSteps

open NumberField Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting

def ResArith {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : Prop :=
  Nat.card (𝓞 X.B.I.F ⧸ p.1.asIdeal) = gOf p ∧ ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal ∧
    ((gOf p : ℕ) : 𝓞 X.B.I.F) ∉ p.1.asIdeal ^ 2

theorem stResZ_of {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) (h : ResArith X p) : StResZ X p := by
  obtain ⟨hc, h1, h2⟩ := h
  have hg0 : gOf p ≠ 0 := by
    intro h0
    apply h2
    rw [h0, Nat.cast_zero]
    exact zero_mem _
  haveI := p.1.isMaximal
  haveI : Finite (𝓞 X.B.I.F ⧸ p.1.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hg0)
  letI : Fintype (𝓞 X.B.I.F ⧸ p.1.asIdeal) := Fintype.ofFinite _
  letI : Field (𝓞 X.B.I.F ⧸ p.1.asIdeal) := Ideal.Quotient.field _
  obtain ⟨n, hl, hcard⟩ := FiniteField.card (𝓞 X.B.I.F ⧸ p.1.asIdeal) (ringChar (𝓞 X.B.I.F ⧸ p.1.asIdeal))
  rw [← Nat.card_eq_fintype_card, hc] at hcard
  have hlP : ((ringChar (𝓞 X.B.I.F ⧸ p.1.asIdeal) : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  have hn : (n : ℕ) = 1 := by
    by_contra hne
    have h2n : 2 ≤ (n : ℕ) := by
      have := n.pos
      omega
    apply h2
    rw [hcard, Nat.cast_pow]
    exact Ideal.pow_le_pow_right h2n (Ideal.pow_mem_pow hlP n)
  haveI : Fact (gOf p).Prime := ⟨by rw [hcard, hn, pow_one]; exact hl⟩
  exact MassDataIdxRes.resZ_of p.1 (gOf p) hc h1 h2

end MassDataIdxSteps
end
end

noncomputable section

namespace MassDataIdxRes

open NumberField IsDedekindDomain Ideal

section K

variable {K : Type} [Field K] [NumberField K]

theorem locDeg_one (l : ℕ) [hl : Fact l.Prime]
    (h : {w : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ w.asIdeal}.ncard = Module.finrank ℚ K)
    (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    w.asIdeal.ramificationIdx ℤ = 1 ∧ w.asIdeal.inertiaDeg ℤ = 1 := by
  have hfin := Formalism.L2.SG.TypedSets.finite_over K l hl.out.ne_zero
  set T := hfin.toFinset with hTdef
  have hT : ∀ v, v ∈ T ↔ ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := fun v => by
    rw [hTdef, Set.Finite.mem_toFinset]; rfl
  have hsum := ReciprocityTheory.Gal.sum_locDegree l T hT
  have hcard : T.card = Module.finrank ℚ K := by rw [← h, Set.ncard_eq_toFinset_card _ hfin]
  have hpos : ∀ v ∈ T, (fun _ => 1) v ≤ ReciprocityTheory.Gal.locDegree v := fun v _ =>
    Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) v.asIdeal) (Ideal.inertiaDeg_pos v.asIdeal ℤ)
  have hall := (Finset.sum_eq_sum_iff_of_le hpos).1 (by
    simp only [Finset.sum_const, smul_eq_mul, mul_one]; rw [hsum, hcard])
  have hm : w.asIdeal.ramificationIdx ℤ * w.asIdeal.inertiaDeg ℤ = 1 := (hall w ((hT w).2 hw)).symm
  exact ⟨Nat.eq_one_of_mul_eq_one_right hm, Nat.eq_one_of_mul_eq_one_left hm⟩

end K

section FE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locDeg_one_below (l : ℕ) [hl : Fact l.Prime]
    (h : {w : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E)
    (p : HeightOneSpectrum (𝓞 F)) (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) :
    p.asIdeal.ramificationIdx ℤ = 1 ∧ p.asIdeal.inertiaDeg ℤ = 1 := by
  have := p.isMaximal
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) p.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot Q
  let w : HeightOneSpectrum (𝓞 E) := ⟨Q, hQm.isPrime, hQ0⟩
  have hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    have := (Ideal.mem_of_liesOver Q p.asIdeal ((l : ℕ) : 𝓞 F)).1 hp
    simpa using this
  obtain ⟨he, hf⟩ := locDeg_one l h w hw
  have hQp : Q.IsPrime := hQm.isPrime
  have h1 : p.asIdeal.ramificationIdx ℤ ≤ Q.ramificationIdx ℤ :=
    Ideal.ramificationIdx_below_le (R := ℤ) (q := p.asIdeal) (r := Q)
  have h2 : p.asIdeal.inertiaDeg ℤ ≤ Q.inertiaDeg ℤ :=
    Ideal.inertiaDeg_below_le (R := ℤ) (q := p.asIdeal) (r := Q)
  have h3 := Ideal.ramificationIdx_pos (R := ℤ) p.asIdeal
  have h4 := Ideal.inertiaDeg_pos p.asIdeal ℤ
  change Q.ramificationIdx ℤ = 1 at he
  change Q.inertiaDeg ℤ = 1 at hf
  omega

end FE

section Arith

variable {F : Type} [Field F] [NumberField F]

theorem arith_of_loc (l : ℕ) [hl : Fact l.Prime] (p : HeightOneSpectrum (𝓞 F))
    (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) (he : p.asIdeal.ramificationIdx ℤ = 1)
    (hf : p.asIdeal.inertiaDeg ℤ = 1) :
    Nat.card (𝓞 F ⧸ p.asIdeal) = l ∧ ((l : ℕ) : 𝓞 F) ∉ p.asIdeal ^ 2 := by
  have hlo : p.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := (ReciprocityTheory.Gal.liesOver_span_iff l p.asIdeal).2 hp
  constructor
  · have := Ideal.pow_inertiaDeg l p.asIdeal
    rw [hf, pow_one] at this
    rw [this, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · intro h2
    have hmap : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 F)) = Ideal.span {((l : ℕ) : 𝓞 F)} := by
      rw [Ideal.map_span, Set.image_singleton]; simp
    have hne : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 F)) ≠ ⊥ := by
      rw [hmap, Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hl.out.ne_zero
    have hm := IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {(l : ℤ)}) p.asIdeal hne
    rw [he, hmap] at hm
    have hdvd : p.asIdeal ^ 2 ∣ Ideal.span {((l : ℕ) : 𝓞 F)} := Ideal.dvd_span_singleton.2 h2
    have hfin : FiniteMultiplicity p.asIdeal (Ideal.span {((l : ℕ) : 𝓞 F)}) := by
      apply FiniteMultiplicity.of_not_isUnit
      · rw [Ideal.isUnit_iff]; exact p.isPrime.ne_top
      · rw [Ne, Ideal.zero_eq_bot, ← hmap]; exact hne
    have := hfin.le_multiplicity_of_pow_dvd hdvd
    omega

end Arith

end MassDataIdxRes
end
end

noncomputable section

namespace MassDataIdxRes

open NumberField IsDedekindDomain Ideal

private theorem comap_ringEquiv_ne_bot {A B : Type} [CommRing A] [CommRing B] (f : A ≃+* B)
    (I : Ideal B) (hI : I ≠ ⊥) : I.comap (f : A →+* B) ≠ ⊥ := by
  intro h
  apply hI
  ext y
  constructor
  · intro hy
    have h1 : f.symm y ∈ I.comap (f : A →+* B) := by
      rw [Ideal.mem_comap]
      simpa using hy
    rw [h, Ideal.mem_bot] at h1
    simpa using h1
  · intro hy
    rw [Ideal.mem_bot] at hy
    rw [hy]
    exact I.zero_mem

theorem split_transport {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L)
    (l : ℕ) (h : {w : HeightOneSpectrum (𝓞 L) | ((l : ℕ) : 𝓞 L) ∈ w.asIdeal}.ncard = Module.finrank ℚ L) :
    {w : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ w.asIdeal}.ncard = Module.finrank ℚ K := by
  classical
  have hrk : Module.finrank ℚ K = Module.finrank ℚ L :=
    (e.toRatAlgEquiv.toLinearEquiv).finrank_eq
  rw [hrk, ← h]
  let g : 𝓞 K ≃+* 𝓞 L := NumberField.RingOfIntegers.mapRingEquiv e
  refine Set.ncard_congr
    (fun w _ => (⟨w.asIdeal.comap (g.symm : 𝓞 L →+* 𝓞 K),
      (by haveI := w.isPrime; infer_instance),
      comap_ringEquiv_ne_bot g.symm w.asIdeal w.ne_bot⟩ : HeightOneSpectrum (𝓞 L))) ?_ ?_ ?_
  · intro w hw
    simp only [Set.mem_setOf_eq, Ideal.mem_comap] at hw ⊢
    simpa using hw
  · intro a b _ _ hab
    have h1 := congrArg HeightOneSpectrum.asIdeal hab
    apply HeightOneSpectrum.ext
    ext x
    have h2 := SetLike.ext_iff.mp h1 (g x)
    simpa [Ideal.mem_comap] using h2
  · intro w hw
    refine ⟨⟨w.asIdeal.comap (g : 𝓞 K →+* 𝓞 L), (by haveI := w.isPrime; infer_instance),
      comap_ringEquiv_ne_bot g w.asIdeal w.ne_bot⟩, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, Ideal.mem_comap] at hw ⊢
      simpa using hw
    · apply HeightOneSpectrum.ext
      ext x
      rw [Ideal.mem_comap, Ideal.mem_comap]
      simp

end MassDataIdxRes

namespace MassDataIdxSteps

open NumberField Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting

theorem resArith_holds {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : ResArith X p := by
  have hgp : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  have hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
    have hty := (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
      (D.host.g_prime 1).ne_zero p.1).1 p.2
    unfold gOf
    split_ifs with h
    · exact h
    · exact hty.resolve_left h
  have hsplit : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) |
      ((gOf p : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
    unfold gOf
    split_ifs
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 0)
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 1)
  obtain ⟨he, hf⟩ := MassDataIdxRes.locDeg_one_below (F := X.B.I.F) (E := X.B.I.E) (gOf p) hsplit p.1 hmem
  obtain ⟨hc, hn⟩ := MassDataIdxRes.arith_of_loc (gOf p) p.1 hmem he hf
  exact ⟨hc, hmem, hn⟩

theorem stResZ_holds {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : StResZ X p :=
  stResZ_of X p (resArith_holds X p)

end MassDataIdxSteps
