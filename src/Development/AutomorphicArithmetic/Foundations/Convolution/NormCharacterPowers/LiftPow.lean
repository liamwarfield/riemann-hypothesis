module

public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.BcSumD

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.LiftSum
open UpperTheory.ConvolutionTheory.R

theorem UpperTheory.ConvolutionTheory.R.liftSum :
    LiftSum := by
  intro K M _ _ _ _ _ _ _ _ _ ι _ κ _ n m π P h
  have h' := Filter.eventually_all.2 h
  refine h'.mono fun w hw f hf => ?_
  choose B hB C hC e using fun i => hw i f hf
  refine ⟨∑ i, B i, ⟨B, hB, rfl⟩, fun a => C a.1 a.2, fun a => hC a.1 a.2, ?_⟩
  rw [Fintype.sum_sigma]
  have : (∑ i, B i).map (· ^ f) = ∑ i, (B i).map (· ^ f) :=
    map_sum (Multiset.mapAddMonoidHom (· ^ f)) B Finset.univ
  rw [this]
  exact Finset.sum_congr rfl fun i _ => e i
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.PartBOfDecomposition
section -- merged from Development.WeilBound.RepresentationTheoryGL.TwistedFactors.GaloisGenerators.LocRoots
section -- merged from Development.WeilBound.RepresentationTheoryGL.TwistedFactors.GaloisGenerators.IsGalGen
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep PositivityTheory.RgJS

namespace PositivityTheory.Rg.Tf.ChR

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E]

def IsIso {n : ℕ} (P : CG E n) {ι : Type} [Fintype ι] {m : ι → ℕ} (Ps : ∀ i, CG E (m i)) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ (C : Multiset ℂˣ) (B : ι → Multiset ℂˣ),
    P.HasSat w C ∧ (∀ i, (Ps i).HasSat w (B i)) ∧ ∑ i, B i = C

end PositivityTheory.Rg.Tf.ChR
end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep PositivityTheory.RgJS

namespace PositivityTheory.Rg.Tf.ChR

def PartA : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (P : CG E n) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (Ps : ∀ i, CG E (m i)), 1 ≤ n → (∀ i, 1 ≤ m i) → 2 ≤ Fintype.card ι → ¬ IsIso P Ps

end PositivityTheory.Rg.Tf.ChR
end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep PositivityTheory.RgJS PositivityTheory.Rg.Tf.ChR

namespace UpperTheory.ConvolutionTheory.R

namespace Pb2

theorem val_pow {E : Type} [Field E] [NumberField E] (η : HChar E) (j : ℕ) (v : HeightOneSpectrum (𝓞 E)) :
    (η ^ j).val v = η.val v ^ j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, pow_succ, ← ih]; rfl

end Pb2

open Pb2

end UpperTheory.ConvolutionTheory.R
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.Decomp
open UpperTheory.ConvolutionTheory.R
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual

section

variable (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

private theorem normV_inertia (w : HeightOneSpectrum (𝓞 M)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have norm_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
      normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [norm_eq, norm_eq]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem unram_ae : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
    ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  have hfin : {w : HeightOneSpectrum (𝓞 M) | w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 M)}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  refine Filter.eventually_cofinite.2 ((hfin.image fun w => w.under (𝓞 K)).subset ?_)
  intro v hv
  by_contra hn
  refine hv fun w hw => ?_
  have := w.isPrime
  have hnd : ¬ w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 M) := fun h => hn ⟨w, h, hw⟩
  exact Ideal.ramificationIdx_eq_one_iff.2 (not_dvd_differentIdeal_iff.1 hnd)

private theorem card_fibre (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} = (v.asIdeal.primesOver (𝓞 M)).ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.ofBijective
    (fun w => ⟨w.1.asIdeal, w.1.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩⟩) ⟨fun a b h => ?_, fun P => ?_⟩)
  · exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · obtain ⟨P, hP, hPv⟩ := P
    exact ⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩,
      HeightOneSpectrum.ext hPv.over.symm⟩, rfl⟩

end

theorem UpperTheory.ConvolutionTheory.R.decomp :
    Decomp := by
  intro K M _ _ _ _ _ _ _ _ hl
  filter_upwards [unram_ae K M] with v hv
  have := v.isPrime
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 M) Gal(M/K)
  obtain ⟨⟨P, hP, hPv⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 M)))
  have he : v.asIdeal.ramificationIdxIn (𝓞 M) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P Gal(M/K)]
    exact hv ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩ (HeightOneSpectrum.ext hPv.over.symm)
  have hn : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v →
      normV w = normV v ^ v.asIdeal.inertiaDegIn (𝓞 M) := by
    rintro w rfl
    have := w.isPrime
    have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
    rw [Ideal.inertiaDegIn_eq_inertiaDeg _ w.asIdeal Gal(M/K)]
    exact normV_inertia K M w
  rw [he, one_mul, IsGalois.card_aut_eq_finrank, ← card_fibre] at hfund
  rcases hl.eq_one_or_self_of_dvd _ (Dvd.intro_left _ hfund) with h | h
  · rw [h, mul_one] at hfund
    exact Or.inl ⟨hfund, fun w hw => by rw [hn w hw, h, pow_one]⟩
  · rw [h] at hfund
    exact Or.inr ⟨Nat.eq_of_mul_eq_mul_right hl.pos (hfund.trans (one_mul _).symm),
      fun w hw => by rw [hn w hw, h]⟩
end
