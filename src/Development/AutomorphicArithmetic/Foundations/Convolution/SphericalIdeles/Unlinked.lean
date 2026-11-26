module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamDefs
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Unlinked
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.CBC

theorem UpperTheory.ConvolutionTheory.Sph.unlinked :
    UpperTheory.ConvolutionTheory.Sph.Unlinked := by
  intro K _ _ _ n hn π v B hB a ha b hb hab
  have hB' : (CG.mk π).HasSat v B := hB
  obtain ⟨ν, hν, h⟩ := PositivityTheory.RgJS.unit_exponent_holds K
  obtain ⟨π₀, t, hu, he⟩ := h n (CG.mk π) hn
  have hχ : ((ν t)⁻¹).UnrAt v := fun x hx => by
    change ((ν t).loc v x)⁻¹ = 1
    rw [(hν t).1 v x hx, inv_one]
  have e0 : (CG.mk π).twist (ν t)⁻¹ = π₀ := by
    rw [he, ← CG.twist_mul, mul_inv_cancel, CG.twist_one]
  have hS : π₀.HasSat v (B.map (· * ((ν t)⁻¹).val v)) :=
    e0 ▸ PositivityTheory.RgJS.satake_twist_holds K n (CG.mk π) (ν t)⁻¹ v B hχ hB'
  have hJ := PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound K n π₀ hu v _ hS
  have h1 := (hJ _ (Multiset.mem_map_of_mem _ ha)).2
  have h2 := (hJ _ (Multiset.mem_map_of_mem _ hb)).1
  have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < Ideal.absNorm v.asIdeal := by linarith
  simp only [Units.val_mul, norm_mul] at h1 h2
  have ha' : ‖(a : ℂ)‖ = (Ideal.absNorm v.asIdeal : ℝ) * ‖(b : ℂ)‖ := by
    rw [hab, norm_mul]
    simp
  rw [ha', mul_assoc] at h1
  have h3 : (Ideal.absNorm v.asIdeal : ℝ) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) := by
    nth_rewrite 1 [← Real.rpow_one (Ideal.absNorm v.asIdeal : ℝ)]
    rw [← Real.rpow_add hq0]
    norm_num
  have h4 := mul_lt_mul_of_pos_left h2 hq0
  rw [h3] at h4
  exact absurd h1 (not_lt.2 h4.le)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.NormRam
noncomputable section
attribute [local instance 10000] DivisionSemiring.to_moduleIsTorsionFree Module.Free.of_divisionRing

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.ConvolutionTheory.Sph

private theorem one_of_ramified {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (hp : (Module.finrank K M).Prime) (w : HeightOneSpectrum (𝓞 M))
    (hram : ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    w.asIdeal.inertiaDeg (𝓞 K) = 1 ∧ ((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard = 1 := by
  have := w.isPrime
  haveI : Module.Finite K M := Module.finite_of_finrank_pos hp.pos
  have k := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (w.asIdeal.under (𝓞 K)) (𝓞 M) Gal(M/K)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal Gal(M/K), Ideal.inertiaDegIn_eq_inertiaDeg _ w.asIdeal Gal(M/K),
    IsGalois.card_aut_eq_finrank] at k
  have he : w.asIdeal.ramificationIdx (𝓞 K) ≠ 1 := fun h => hram (Ideal.ramificationIdx_eq_one_iff.1 h)
  have hd : w.asIdeal.ramificationIdx (𝓞 K) ∣ Module.finrank K M :=
    ⟨((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * w.asIdeal.inertiaDeg (𝓞 K), by rw [← k]; ring⟩
  have hel := (Nat.dvd_prime hp).1 hd |>.resolve_left he
  rw [hel] at k
  have h1 : ((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    refine Nat.eq_of_mul_eq_mul_left hp.pos ?_
    calc Module.finrank K M * (((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * w.asIdeal.inertiaDeg (𝓞 K))
        = ((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * (Module.finrank K M * w.asIdeal.inertiaDeg (𝓞 K)) := by ring
      _ = Module.finrank K M * 1 := by rw [k, mul_one]
  exact ⟨Nat.eq_one_of_mul_eq_one_left h1, Nat.eq_one_of_mul_eq_one_right h1⟩

end UpperTheory.ConvolutionTheory.Sph

open UpperTheory.ConvolutionTheory.Sph in
theorem UpperTheory.ConvolutionTheory.Sph.normRam :
    UpperTheory.ConvolutionTheory.Sph.NormRam := by
  intro K M _ _ _ _ _ _ hp w hram
  obtain ⟨hf, hg⟩ := one_of_ramified hp w hram
  refine ⟨?_, fun w' hw' => ?_, fun η hη hu => ?_⟩
  · have h := GlobalTheory.QuadNormChar.normV_under (K := K) w
    rwa [hf, pow_one] at h
  · obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 hg
    have h1 : w.asIdeal ∈ (w.asIdeal.under (𝓞 K)).primesOver (𝓞 M) := ⟨w.isPrime, ⟨rfl⟩⟩
    have h2 : w'.asIdeal ∈ (w.asIdeal.under (𝓞 K)).primesOver (𝓞 M) :=
      ⟨w'.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal hw'.symm⟩⟩
    rw [ha] at h1 h2
    exact HeightOneSpectrum.ext (h2.trans h1.symm)
  · let Ω := AlgebraicClosure M
    haveI : Module.Finite K M := Module.finite_of_finrank_pos hp.pos
    haveI : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
    haveI : Algebra.IsAlgebraic M Ω := IsAlgClosure.isAlgebraic
    haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩
    obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
    have hAv : IsPlaceOver A (w.under (𝓞 K)) := fun x => by
      rw [IsScalarTower.algebraMap_apply K M Ω]
      exact hA (algebraMap (𝓞 K) (𝓞 M) x)
    have hmove : ∃ s ∈ Ine (F := K) A, ¬ UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes M s := by
      by_contra hfix
      push_neg at hfix
      obtain ⟨hlo, he⟩ := GlobalTheory.InertFixVal.ramificationIdx_eq_one A (w.under (𝓞 K)) w hAv hA hfix
      exact hram (Ideal.ramificationIdx_eq_one_iff.1 he)
    exact UpperTheory.Gal.UnramifiedFromSplittingCriterion.normRam K M Ω hp η hη A _ hAv hmove hu
end
end
