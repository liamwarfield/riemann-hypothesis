module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientParIndProductsFlattened
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockWeilActionThetaUnfolding
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.GrowForms
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmConjugationProperties
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmConjugationProperties
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

theorem isCMExt_conj_fixed_integers : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x, σ (σ x) = x) ∧
      (∀ x, σ x = x → ∃ y : F, algebraMap F E y = x) ∧
      (∀ (o : 𝓞 E), ((sO σ o : 𝓞 E) : E) = σ (o : E)) ∧
      (∀ I : Ideal (𝓞 E), Ideal.absNorm (I.map (sO σ)) = Ideal.absNorm I) := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hval : ∀ o : 𝓞 E, ((sO σ o : 𝓞 E) : E) = σ (o : E) := fun o => rfl
  have hmoved : ∃ θ : E, σ θ ≠ θ := by
    by_contra hc
    push_neg at hc
    have hc' := h.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext y
    have := h.2.2.2 τ y
    rw [hc y] at this
    simpa using this.symm
  refine ⟨hinv, ?_, hval, ?_⟩
  · intro x hx
    by_contra hne
    haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
    have hli : LinearIndependent F ![(1 : E), x] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        refine ⟨?_, rfl⟩
        simpa using hst
      · exfalso
        apply hne
        refine ⟨-s / t, ?_⟩
        have h1 : algebraMap F E s + algebraMap F E t * x = 0 := by
          simpa [Algebra.smul_def] using hst
        have ht' : algebraMap F E t ≠ 0 := by simpa using ht
        rw [map_div₀, map_neg, div_eq_iff ht']
        linear_combination -h1
    have hspan : Submodule.span F (Set.range ![(1 : E), x]) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by rw [h.2.2.1]; simp)
    have hid : σ.toLinearMap = LinearMap.id := by
      refine LinearMap.ext_on_range hspan ?_
      intro i
      fin_cases i
      · simp
      · simpa using hx
    obtain ⟨θ, hθ⟩ := hmoved
    exact hθ (by simpa using LinearMap.congr_fun hid θ)
  · intro I
    have hs : ∀ o : 𝓞 E, sO σ (sO σ o) = o := by
      intro o
      apply RingOfIntegers.ext
      rw [hval, hval, hinv]
    let e : 𝓞 E ≃+* 𝓞 E := RingEquiv.ofRingHom (sO σ) (sO σ)
      (RingHom.ext hs) (RingHom.ext hs)
    exact GlobalTheory.absNorm_map_ringEquiv_self e I

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmConjugationPropertiesStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_conjugation_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x, σ (σ x) = x) ∧ (∀ x, σ x = x → ∃ y : F, algebraMap F E y = x) ∧ (∀ (o : 𝓞 E), ((sO σ o : 𝓞 E) : E) = σ (o : E)) ∧ (∀ I : Ideal (𝓞 E), Ideal.absNorm (I.map (sO σ)) = Ideal.absNorm I) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isCMExt_conj_fixed_integers | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isCMExt_conj_fixed_integers | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isCMExt_conj_fixed_integers <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorNormQuadraticExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorNormQuadraticExtension
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix nonZeroDivisors

theorem mem_den_iff {K : Type} [Field K] [NumberField K] (x : K) (a : 𝓞 K) :
    a ∈ HS.den K x ↔ ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K a * x := by
  rw [HS.den, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  show (∀ i : Fin 1, ∃ o, algebraMap (𝓞 K) K o = (a • fun _ : Fin 1 => x) i) ↔ _
  simp only [Pi.smul_apply, Algebra.smul_def]
  exact ⟨fun h => h 0, fun h _ => h⟩

theorem exists_bezout {K : Type} [Field K] [NumberField K] (x : K) :
    ∃ a ∈ HS.den K x, ∃ c ∈ HS.den K x,
      algebraMap (𝓞 K) K a + algebraMap (𝓞 K) K c * x = 1 := by
  classical
  obtain ⟨S, hSdef⟩ : ∃ S : FractionalIdeal (𝓞 K)⁰ K,
      S = FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) ⊔ FractionalIdeal.spanSingleton (𝓞 K)⁰ x :=
    ⟨_, rfl⟩
  have h1S : (1 : K) ∈ S := by
    rw [hSdef]; exact (le_sup_left : FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) ≤ _)
      (FractionalIdeal.mem_spanSingleton_self _ _)
  have hxS : x ∈ S := by
    rw [hSdef]; exact (le_sup_right : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≤ _)
      (FractionalIdeal.mem_spanSingleton_self _ _)
  have hS : S ≠ 0 := by
    intro h
    rw [h] at h1S
    exact one_ne_zero ((FractionalIdeal.mem_zero_iff _).1 h1S)
  have hden : ∀ t ∈ S⁻¹, ∃ a ∈ HS.den K x, algebraMap (𝓞 K) K a = t := by
    intro t ht
    rw [FractionalIdeal.mem_inv_iff hS] at ht
    have ht1 : t ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
      have := ht 1 h1S
      rwa [mul_one] at this
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).1 ht1
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).1 (ht x hxS)
    exact ⟨a, (mem_den_iff x a).2 ⟨o, by rw [ho, ha]⟩, ha⟩
  have hsplit : ∀ T : FractionalIdeal (𝓞 K)⁰ K, S * T = FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) * T ⊔
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x * T := by
    intro T
    rw [hSdef, FractionalIdeal.sup_eq_add, FractionalIdeal.sup_eq_add, add_mul]
  have h1 : (1 : K) ∈ S * S⁻¹ := by
    rw [mul_inv_cancel₀ hS]; exact FractionalIdeal.one_mem_one _
  rw [hsplit S⁻¹, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_sup, Submodule.mem_sup] at h1
  obtain ⟨u, hu, v, hv, huv⟩ := h1
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul] at hu hv
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  obtain ⟨a, ha, ha'⟩ := hden u' hu'
  obtain ⟨c, hc, hc'⟩ := hden v' hv'
  refine ⟨a, ha, c, hc, ?_⟩
  rw [ha', hc', ← huv]
  ring

theorem den_algebraMap (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (x : F) :
    HS.den E (algebraMap F E x) = Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (HS.den F x) := by
  have tower : ∀ o : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) o) =
      algebraMap F E (algebraMap (𝓞 F) F o) := by
    intro o
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  apply le_antisymm
  · intro b hb
    obtain ⟨a, ha, c, hc, hac⟩ := exists_bezout x
    obtain ⟨o, ho⟩ := (mem_den_iff _ b).1 hb
    have key : b = algebraMap (𝓞 F) (𝓞 E) a * b + algebraMap (𝓞 F) (𝓞 E) c * o := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      have hac' := congrArg (algebraMap F E) hac
      simp only [map_add (f := _), map_mul, map_one] at hac'
      simp only [map_add (f := _), map_mul, tower, ho]
      linear_combination (-(algebraMap (𝓞 E) E b)) * hac'
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha))
      (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc))
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_den_iff]
    obtain ⟨o, ho⟩ := (mem_den_iff x a).1 ha
    exact ⟨algebraMap (𝓞 F) (𝓞 E) o, by rw [tower, tower, ho, map_mul]⟩

theorem absNorm_den_algebraMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], Module.finrank F E = 2 → ∀ x : F,
      Ideal.absNorm (HS.den E (algebraMap F E x)) = Ideal.absNorm (HS.den F x) ^ 2 := by
  intro F E _ _ _ _ _ h2 x
  rw [den_algebraMap, Ideal.absNorm_algebraMap]
  congr 1
  rw [← h2]
  exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorNormQuadraticExtensionStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.denominator_norm_quadratic_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ x : F, Ideal.absNorm (den E (algebraMap F E x)) = Ideal.absNorm (den F x) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap.absNorm_den_algebraMap | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap.absNorm_den_algebraMap | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap.absNorm_den_algebraMap <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLattice
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermPoisson

variable {D : D7} {r : ℕ}


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem poisson_herm : ∀ (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)), IsCovolOneH lam 𝓖 → ∀ f : hermA D r → ℂ, Continuous f → (∀ K : Set (hermA D r), IsCompact K → ∃ u : ratHerm D r → ℝ, Summable u ∧ ∀ c : ratHerm D r, ∀ b ∈ K, ‖f (b + c.1)‖ ≤ u c) → Integrable f lam ∧ (Summable (fun t : ratHerm D r => ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) → ∑' c : ratHerm D r, f c.1 = ∑' t : ratHerm D r, ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) := by
  intro D r ψ hψ lam 𝓖 h𝓖 f hf hu
  obtain ⟨hH, hD, hD1⟩ := h𝓖
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : LocallyCompactSpace (Mx D r r) := i2
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : T2Space (Mx D r r) := i4
  haveI : SecondCountableTopology (hermA D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D r) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : LocallyCompactSpace (hermA D r) :=
    (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := r)).locallyCompactSpace
  haveI : Countable D.host.E := GlobalTheory.CompanionTheory.FourierComplete.countable_numberField D.host.E
  haveI : Countable (Matrix (Fin r) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin r → Fin r → D.host.E))
  have hmem : ∀ q : ratHerm D r, q.1.1 ∈ ratMx D r r := fun q => AddSubgroup.mem_comap.1 q.2
  haveI : Countable (ratHerm D r) := by
    choose g hg using fun q : ratHerm D r => mem_ratMx.1 (hmem q)
    exact Function.Injective.countable (f := g) fun a b h =>
      Subtype.ext (Subtype.ext (by rw [← hg a, ← hg b, h]))
  haveI := hH
  obtain ⟨-, K, hK, hKx⟩ := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := r)
  let ι : ratHerm D r →+ hermA D r := (ratHerm D r).subtype
  have hι : Function.Injective ι := Subtype.val_injective
  have hr : ι.range = ratHerm D r := AddSubgroup.range_subtype _
  have hD' : IsAddFundamentalDomain ι.range 𝓖 lam := by
    rw [hr]
    exact hD
  have hc : ∀ x : hermA D r, ∃ l ∈ ratHerm D r, x - l ∈ K := fun x => by
    obtain ⟨γ, hγ, h⟩ := hKx x
    refine ⟨-γ, neg_mem hγ, ?_⟩
    rwa [sub_neg_eq_add, add_comm]
  have hx : ∀ x : hermA D r, ∃ a, x - ι a ∈ K := fun x => by
    obtain ⟨l, hl, h⟩ := hc x
    exact ⟨⟨l, hl⟩, h⟩
  let Eh : ratHerm D r → hermA D r → ℂ := fun t b => chi ψ t.1.1 b
  have hEc : ∀ t, Continuous (Eh t) := fun t => continuous_chi hψ t.1.1
  have hEn : ∀ t b, ‖Eh t b‖ = 1 := fun t b => hψ.2.1 _
  have hEp : ∀ t x c, Eh t (x + ι c) = Eh t x := fun t x c => by
    show chi ψ t.1.1 (x + c.1) = chi ψ t.1.1 x
    rw [chi_add_right, chi_rat hψ (hmem t) c, mul_one]
  have hE0 : ∀ t, Eh t 0 = 1 := fun t => chi_zero_right ψ t.1.1
  have hself : ∀ t x, Eh t x * Eh (-t) x = 1 := fun t x => by
    show chi ψ t.1.1 x * chi ψ (-t.1.1) x = 1
    rw [← chi_add_left, add_neg_cancel, chi_zero_left]
  have horth : ∀ s t, t ≠ s → ∫ x in 𝓖, Eh t x * Eh (-s) x ∂lam = 0 := fun s t hts => by
    obtain ⟨a, ha⟩ := exists_chi_ne hψ (t - s) (sub_ne_zero.2 hts)
    have hm : t.1.1 + -s.1.1 = (t - s).1.1 := by
      rw [← sub_eq_add_neg]
      rfl
    have he : ∀ x, Eh t x * Eh (-s) x = chi ψ (t - s).1.1 x := fun x => by
      rw [← hm, chi_add_left]
      rfl
    simp only [he]
    exact Formalism.IndefR.Tow.fd_setIntegral_char_eq_zero hD (a := a)
      (fun x y => chi_add_right ψ _ x y) (fun g hg => chi_rat hψ (hmem (t - s)) ⟨g, hg⟩) ha
  have hcomp : ∀ g : hermA D r → ℂ, Continuous g → (∀ x c, g (x + ι c) = g x) →
      (∀ t, ∫ b in 𝓖, g b * Eh (-t) b ∂lam = 0) → ∀ x, g x = 0 := fun g hg hp hz x => by
    refine GlobalTheory.CompanionTheory.FourierComplete.eq_zero_of_coeffs_vanish (ratHerm D r) lam hD hK hc (T := ratHerm D r)
      Eh hEc (fun t x l hl => hEp t x ⟨l, hl⟩) (fun y => chi_zero_left ψ y) (fun s t y => chi_add_left ψ _ _ y)
      (fun t y => ?_) (fun a b hab => ?_) g hg (fun y l hl => hp y ⟨l, hl⟩) hz x
    · show star (ψ _) = chi ψ (-t.1.1) y
      rw [star_psi' hψ, chi_neg_left]
    · refine rat_of_chi hψ _ fun t => ?_
      have h1 := chi_add_right ψ t.1.1 (-a) b
      have h2 := chi_add_right ψ t.1.1 (-a) a
      rw [neg_add_cancel, chi_zero_right] at h2
      have h3 : chi ψ t.1.1 a = chi ψ t.1.1 b := hab t
      rw [h1, ← h3, ← h2]
  have hu' : GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.UnifSummable ι f := hu
  have main := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.poisson_gen (V := hermA D r) (C := ratHerm D r) (ι := ι) hι
    (μ := lam) hD' hD1 hK hx (E := Eh) hEc hEn hEp hE0 hself horth hcomp hf hu'
  have hneg : ∀ (t : ratHerm D r) b, Eh (-t) b =
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) := fun t b => chi_neg_left ψ t.1.1 b
  simp only [hneg] at main
  exact main

end GlobalTheory.CompanionTheory.HermPoisson
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLatticeStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poisson_summation_hermitian_lattice : ∀ (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)), IsCovolOneH lam 𝓖 → ∀ f : hermA D r → ℂ, Continuous f → (∀ K : Set (hermA D r), IsCompact K → ∃ u : ratHerm D r → ℝ, Summable u ∧ ∀ c : ratHerm D r, ∀ b ∈ K, ‖f (b + c.1)‖ ≤ u c) → Integrable f lam ∧ (Summable (fun t : ratHerm D r => ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) → ∑' c : ratHerm D r, f c.1 = ∑' t : ratHerm D r, ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) := by
  first | exact @GlobalTheory.CompanionTheory.HermPoisson.poisson_herm | exact GlobalTheory.CompanionTheory.HermPoisson.poisson_herm | (intros; apply GlobalTheory.CompanionTheory.HermPoisson.poisson_herm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeOfDualPairing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeOfDualPairing
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

theorem exists_extend {K : Type} [Field K] [NumberField K] {m : ℕ}
    (L : Submodule (𝓞 K) (Fin m → K))
    (hs : Submodule.span K (L : Set (Fin m → K)) = ⊤) (φ : L →ₗ[𝓞 K] 𝓞 K) :
    ∃ G : (Fin m → K) →ₗ[K] K, ∀ x : L, G x = algebraMap (𝓞 K) K (φ x) := by
  classical
  have hs' : ⊤ ≤ Submodule.span K (L : Set (Fin m → K)) := hs.ge
  obtain ⟨ι, b, hb⟩ : ∃ (ι : Type) (b : Module.Basis ι K (Fin m → K)), ∀ i, b i ∈ L :=
    ⟨_, Module.Basis.ofSpan hs', fun i => Module.Basis.ofSpan_subset hs' ⟨i, rfl⟩⟩
  haveI := Module.Finite.finite_basis b
  haveI := Fintype.ofFinite ι
  let G : (Fin m → K) →ₗ[K] K := b.constr K (fun i => algebraMap (𝓞 K) K (φ ⟨b i, hb i⟩))
  have hGb : ∀ i, G (b i) = algebraMap (𝓞 K) K (φ ⟨b i, hb i⟩) := fun i => b.constr_basis _ _ _
  refine ⟨G, fun x => ?_⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
    (fun i => b.repr (x : Fin m → K) i) (S := K)
  choose e he using hd
  have hx : ((d : 𝓞 K) • (x : Fin m → K)) = ∑ i, e i • b i := by
    conv_lhs => rw [← b.sum_repr (x : Fin m → K)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (e i) (b i), he i, smul_assoc]
  have hxL : (d : 𝓞 K) • x = ∑ i, e i • (⟨b i, hb i⟩ : L) := by
    apply Subtype.ext
    simpa using hx
  have h1 : (d : 𝓞 K) * φ x = ∑ i, e i * φ ⟨b i, hb i⟩ := by
    have h := congrArg φ hxL
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, smul_eq_mul] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  have h2 : algebraMap (𝓞 K) K (d : 𝓞 K) * G x = algebraMap (𝓞 K) K ((d : 𝓞 K) * φ x) := by
    have h3 : algebraMap (𝓞 K) K (d : 𝓞 K) * G x = G ((d : 𝓞 K) • (x : Fin m → K)) := by
      rw [← algebraMap_smul K (d : 𝓞 K) (x : Fin m → K), map_smul, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h3, hx, h1, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (e i) (b i), map_smul, hGb, smul_eq_mul, map_mul]
  have hd0 : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 := by
    have := nonZeroDivisors.ne_zero d.2
    simpa using this
  rw [map_mul] at h2
  exact mul_left_cancel₀ hd0 h2

theorem mem_of_dot_integral : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ v : Fin m → K,
    (∀ a : Fin m → K, (∀ x ∈ L, a ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) →
      a ⬝ᵥ v ∈ (1 : Submodule (𝓞 K) K)) → v ∈ L := by
  intro K _ _ m L hL v hv
  obtain ⟨hfg, hspan⟩ := hL
  haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.IsTorsionFree (𝓞 K) L := inferInstance
  haveI : Module.FinitePresentation (𝓞 K) L := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 K) L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let φ : Fin n → L →ₗ[𝓞 K] 𝓞 K := fun i => (LinearMap.proj i).comp s
  let l : Fin n → L := fun i => f (fun j => if i = j then 1 else 0)
  have hdual : ∀ x : L, x = ∑ i, φ i x • l i := by
    intro x
    have h1 : f (s x) = x := LinearMap.congr_fun hs x
    have h2 := LinearMap.pi_apply_eq_sum_univ f (s x)
    rw [h1] at h2
    exact h2
  choose G hG using fun i => exists_extend L hspan (φ i)
  let a : Fin n → Fin m → K := fun i j => G i (fun k => if j = k then 1 else 0)
  have ha : ∀ i w, a i ⬝ᵥ w = G i w := by
    intro i w
    rw [LinearMap.pi_apply_eq_sum_univ (G i) w]
    simp [dotProduct, a, mul_comm]
  have hid : ∀ w : Fin m → K, w = ∑ i, G i w • (l i : Fin m → K) := by
    let T : (Fin m → K) →ₗ[K] (Fin m → K) := ∑ i, (G i).smulRight (l i : Fin m → K)
    have hT : T = LinearMap.id := by
      refine LinearMap.ext_on hspan ?_
      intro x hx
      have h1 := congrArg (Subtype.val) (hdual ⟨x, hx⟩)
      simp only [T, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      have h2 : ∀ i, G i x • (l i : Fin m → K) = φ i ⟨x, hx⟩ • (l i : Fin m → K) := by
        intro i
        rw [show G i x = algebraMap (𝓞 K) K (φ i ⟨x, hx⟩) from hG i ⟨x, hx⟩, algebraMap_smul]
      simp only [h2]
      simpa using h1.symm
    intro w
    have h := LinearMap.congr_fun hT w
    simpa [T, LinearMap.sum_apply] using h.symm
  have hint : ∀ i, ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = a i ⬝ᵥ v := by
    intro i
    have h := hv (a i) (fun x hx => by
      rw [(ha i x).trans (hG i ⟨x, hx⟩)]
      exact Submodule.mem_one.mpr ⟨_, rfl⟩)
    exact Submodule.mem_one.mp h
  choose o ho using hint
  rw [hid v]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h3 : G i v • (l i : Fin m → K) = o i • (l i : Fin m → K) := by
    rw [← ha, ← ho, algebraMap_smul]
  rw [h3]
  exact L.smul_mem _ (l i).2

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeOfDualPairingStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_lattice_of_dual_pairing : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ v : Fin m → K, (∀ a : Fin m → K, (∀ x ∈ L, a ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) → a ⬝ᵥ v ∈ (1 : Submodule (𝓞 K) K)) → v ∈ L := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt.mem_of_dot_integral | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt.mem_of_dot_integral | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt.mem_of_dot_integral <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursIrreducibleSubquotient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursIrreducibleSubquotient
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.WordIrr

theorem exists_lift_twKer {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G V} {τ : Representation ℂ G W} (f : σ.IntertwiningMap τ)
    (hf : Function.Surjective f) {H : Subgroup G} {y : W} (hy : y ∈ twKer τ H 1) :
    ∃ x ∈ twKer σ H 1, f x = y := by
  have hint : ∀ (g : G) (u : V), f.toLinearMap (σ g u) = τ g (f.toLinearMap u) :=
    fun g u => LinearMap.congr_fun (f.isIntertwining' g) u
  have hfL : ∀ x, f x = f.toLinearMap x := fun _ => rfl
  have hy' : y ∈ Submodule.span ℂ {w | ∃ (n : H) (v : W), w = τ ↑n v - ↑((1 : H →* ℂˣ) n) • v} := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, v, rfl⟩ := hw
    obtain ⟨u, rfl⟩ := hf v
    refine ⟨σ ↑n u - ↑((1 : H →* ℂˣ) n) • u, Submodule.subset_span ⟨n, u, rfl⟩, ?_⟩
    simp only [hfL, map_sub, Units.smul_def, map_smul, hint]
  | zero =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [hfL]
    exact map_zero _
  | add a b _ _ ha hb =>
    obtain ⟨x1, hx1, rfl⟩ := ha
    obtain ⟨x2, hx2, rfl⟩ := hb
    refine ⟨x1 + x2, add_mem hx1 hx2, ?_⟩
    simp only [hfL, map_add (f := _)]
  | smul c a _ ha =>
    obtain ⟨x1, hx1, rfl⟩ := ha
    refine ⟨c • x1, Submodule.smul_mem _ c hx1, ?_⟩
    simp only [hfL, map_smul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N s : ℕ} {d : Fin s → ℕ} {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

theorem jhMult_jac_of_le (e : (Σ a, Fin (d a)) ≃ Fin N)
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) U} (hσ : σ.IsIrreducible)
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) {S T : Subrepresentation π} (h : T ≤ S) :
    jhMult σ (GlobalTheory.SmGL.jac e S.toRepresentation) =
      jhMult σ (GlobalTheory.SmGL.jac e T.toRepresentation) + jhMult σ (GlobalTheory.SmGL.jac e (subQuot S T)) := by
  let j : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have hS : IsSmooth S.toRepresentation := (IsSubquotient.of_injective j Subtype.val_injective).isSmooth hπ
  let ι : T.toRepresentation.IntertwiningMap S.toRepresentation := ⟨Submodule.inclusion h, fun _ => rfl⟩
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hp : ∀ v, p v = 0 ↔ v.1 ∈ T.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
  have hps : Function.Surjective p := Submodule.Quotient.mk_surjective _
  refine jhMult_exact (jacMap e ι) (jacMap e p) hσ
    (GlobalTheory.JacquetExact.jacMap_injective e hS ι (Submodule.inclusion_injective h))
    (GlobalTheory.JacquetExact.jacMap_surjective e p hps) (fun u => ?_) (fun v hv => ?_)
  · obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have h0 : p (ι t) = 0 := (hp _).2 t.2
    show Submodule.Quotient.mk (p (ι t)) = 0
    rw [h0]
    rfl
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    have h1 : p x ∈ twKer (subQuot S T) (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 hv
    obtain ⟨y, hy, hxy⟩ := exists_lift_twKer p hps h1
    have h2 : (x - y).1 ∈ T.toSubmodule := (hp _).1 (by rw [map_sub, hxy, sub_self])
    refine ⟨Submodule.Quotient.mk ⟨(x - y).1, h2⟩, ?_⟩
    show Submodule.Quotient.mk (x - y) = Submodule.Quotient.mk x
    refine (Submodule.Quotient.eq _).2 ?_
    rw [sub_sub_cancel_left]
    exact neg_mem hy

theorem exists_irrRep_of_subrep (e : (Σ a, Fin (d a)) ≃ Fin N)
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) U} (hσ : σ.IsIrreducible)
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) (hl : HasFiniteLength π)
    (S : Subrepresentation π) (hS : jhMult σ (GlobalTheory.SmGL.jac e S.toRepresentation) ≠ 0) :
    ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ S.toRepresentation ∧ jhMult σ (GlobalTheory.SmGL.jac e τ.ρ) ≠ 0 := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hl
  have : WellFoundedGT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedLT
  induction S using WellFoundedLT.induction with
  | ind S ih =>
  rcases eq_or_ne S ⊥ with rfl | hne
  · exfalso
    apply hS
    have h0 : Subsingleton (⊥ : Subrepresentation π).toSubmodule :=
      inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
    have h1 : Subsingleton (Jacquet (⊥ : Subrepresentation π).toRepresentation (unipRad k e)) :=
      (Submodule.Quotient.mk_surjective _).subsingleton
    exact jhMult_of_subsingleton hσ _
  obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hne)
  let ι : T.toRepresentation.IntertwiningMap S.toRepresentation := ⟨Submodule.inclusion hT.le, fun _ => rfl⟩
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  let j : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  rw [jhMult_jac_of_le e hσ hπ hT.le] at hS
  by_cases h0 : jhMult σ (GlobalTheory.SmGL.jac e T.toRepresentation) = 0
  · rw [h0, zero_add] at hS
    have hq : IsSubquotient (subQuot S T) S.toRepresentation :=
      .of_surjective p (Submodule.Quotient.mk_surjective _)
    have hsm : IsSmooth (subQuot S T) :=
      (hq.trans (.of_injective j Subtype.val_injective)).isSmooth hπ
    exact ⟨⟨_, subQuot S T, hsm, isIrreducible_subQuot hT⟩, hq, hS⟩
  · obtain ⟨τ, h1, h2⟩ := ih T hT.lt h0
    exact ⟨τ, h1.trans (.of_injective ι (Submodule.inclusion_injective hT.le)), h2⟩

theorem exists_irrRep_wd : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ w : List (IrrGL (k := k)), Wd π w → ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ π ∧ Wd τ.ρ w := by
  intro k _ _ _ _ hA N V _ _ π hπ hl w ⟨hd, hw⟩
  have hσ : (piTensor fun a => (w.get a).rep).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (w.get a).2.rep.irr) fun a φ hφ =>
      GlobalTheory.SchurAdm.schur_admissible _ (KO k (Fin (w.get a).1)) GlobalTheory.SplitFlip.isOpen_KO
        GlobalTheory.SplitFlip.isCompact_KO _ _ (w.get a).2.rep.irr
        (hA k _ _ _ (w.get a).2.rep.smooth (w.get a).2.rep.irr) φ hφ
  have hT1 : IsSubquotient π (⊤ : Subrepresentation π).toRepresentation :=
    .of_surjective (topEquiv π).toIntertwiningMap (topEquiv π).surjective
  have hT2 : IsSubquotient (⊤ : Subrepresentation π).toRepresentation π :=
    .of_injective (topEquiv π).toIntertwiningMap (topEquiv π).injective
  have h1 : jhMult (piTensor fun a => (w.get a).rep)
      (GlobalTheory.SmGL.jac (stdBlocks (fun a => (w.get a).1) hd) (⊤ : Subrepresentation π).toRepresentation) ≠ 0 :=
    jhMult_ne_zero_iff.2 ((jhMult_ne_zero_iff.1 hw).trans
      (GlobalTheory.JacquetExact.isSubquotient_jac _ (hT2.isSmooth hπ) hT1))
  obtain ⟨τ, h2, h3⟩ := exists_irrRep_of_subrep _ hσ hπ hl ⊤ h1
  exact ⟨τ, h2.trans hT2, hd, h3⟩

end GlobalTheory.CompanionTheory.WordIrr

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursIrreducibleSubquotientStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_occurs_irreducible_subquotient : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ w : List (IrrGL (k := k)), Wd π w → ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ π ∧ Wd τ.ρ w := by
  first | exact @GlobalTheory.CompanionTheory.WordIrr.exists_irrRep_wd | exact GlobalTheory.CompanionTheory.WordIrr.exists_irrRep_wd | (intros; apply GlobalTheory.CompanionTheory.WordIrr.exists_irrRep_wd <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapProductSegments
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZSwap

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prodIrr_congr {r r' N : ℕ} (hr : r = r') (v : Fin r → IrrGL (k := k)) (w : Fin r' → IrrGL (k := k))
    (hvw : ∀ i, v i = w (Fin.cast hr i)) (hv : ∑ a, (v a).1 = N) (hw : ∑ a, (w a).1 = N) :
    Nonempty ((prodIrr v hv).Equiv (prodIrr w hw)) := by
  subst hr
  have e : v = w := funext fun i => (hvw i).trans (congrArg w (Fin.ext rfl))
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem flatten {s h N : ℕ} (t : Fin s → ℕ) (u : ∀ a, Fin (t a) → IrrGL (k := k)) (d : Fin s → ℕ)
    (hd : ∀ a, ∑ b, (u a b).1 = d a) (hN : ∑ a, d a = N) (F : Fin h ≃o Σₗ a, Fin (t a))
    (x : Fin h → IrrGL (k := k)) (hx : ∀ c, u (ofLex (F c)).1 (ofLex (F c)).2 = x c) (hxN : ∑ a, (x a).1 = N) :
    Nonempty ((multiProd (stdBlocks d hN) fun a => prodIrr (u a) (hd a)).Equiv (prodIrr x hxN)) := by
  have e : (fun c => u (ofLex (F c)).1 (ofLex (F c)).2) = x := funext hx
  subst e
  have hS := GlobalTheory.SmGL.Stages.stages_equiv (k := k) s d t (fun a b => (u a b).1)
    (fun a => stdBlocks (fun b => (u a b).1) (hd a)) (fun a b => (u a b).2.rep.V) (fun a b => (u a b).rep)
    (Fin N) (stdBlocks d hN)
  refine Exists.elim hS fun E0 hχ => ?_
  let E : (Σ c : Fin h, Fin (u (ofLex (F c)).1 (ofLex (F c)).2).1) ≃ Fin N :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (u (ofLex c).1 (ofLex c).2).1) F.toEquiv).trans E0
  have hω := GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv (k := k) F F.strictMono F.surjective E0 E
    (fun _ _ => rfl) fun c => (u (ofLex c).1 (ofLex c).2).rep
  refine hχ.elim fun χ => hω.elim fun ω => ?_
  refine (GlobalTheory.ProdReorder.multiProd_placing (k := k) E (stdBlocks (fun c => (u (ofLex (F c)).1 (ofLex (F c)).2).1) hxN)
    fun c => (u (ofLex (F c)).1 (ofLex (F c)).2).rep).elim fun p => ?_
  exact ⟨(χ.trans ω).trans p⟩

def grp (h j : ℕ) : Fin 3 → ℕ := ![j, 2, h - (j + 2)]

def off (j : ℕ) : Fin 3 → ℕ := ![0, j, j + 2]

theorem off_add_grp_le {h j : ℕ} (hj : j + 1 < h) (a : Fin 3) : off j a + grp h j a ≤ h := by
  fin_cases a <;> simp [off, grp] <;> omega

theorem off_add_grp_le_off {h j : ℕ} (hj : j + 1 < h) {a a' : Fin 3} (haa : a < a') :
    off j a + grp h j a ≤ off j a' := by
  fin_cases a <;> fin_cases a' <;> simp [off, grp] at haa ⊢

def place {h j : ℕ} (hj : j + 1 < h) (c : Σₗ a, Fin (grp h j a)) : Fin h :=
  ⟨off j (ofLex c).1 + (ofLex c).2, by
    have := off_add_grp_le hj (ofLex c).1
    have := (ofLex c).2.2
    omega⟩

theorem place_strictMono {h j : ℕ} (hj : j + 1 < h) : StrictMono (place hj) := by
  intro c c' hc
  obtain ⟨a, b⟩ := c
  obtain ⟨a', b'⟩ := c'
  rcases Sigma.Lex.lt_def.1 hc with hlt | ⟨e, hlt⟩
  · have h1 : off j a + grp h j a ≤ off j a' := off_add_grp_le_off hj hlt
    have h2 : (b : ℕ) < grp h j a := b.2
    show off j a + b < off j a' + b'
    omega
  · obtain rfl : a = a' := e
    have : (b : ℕ) < b' := hlt
    show off j a + b < off j a + b'
    omega

theorem card_lex {h j : ℕ} (hj : j + 1 < h) : Fintype.card (Σₗ a, Fin (grp h j a)) = h := by
  rw [Fintype.card_lex, Fintype.card_sigma]
  simp only [Fintype.card_fin, Fin.sum_univ_three]
  show j + 2 + (h - (j + 2)) = h
  omega

theorem place_bijective {h j : ℕ} (hj : j + 1 < h) : Function.Bijective (place hj) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨(place_strictMono hj).injective, by simp [card_lex hj]⟩

def order {h j : ℕ} (hj : j + 1 < h) : Fin h ≃o Σₗ a, Fin (grp h j a) :=
  ((place_strictMono hj).orderIsoOfSurjective _ (place_bijective hj).2).symm

theorem place_order {h j : ℕ} (hj : j + 1 < h) (c : Fin h) : place hj (order hj c) = c :=
  ((place_strictMono hj).orderIsoOfSurjective _ (place_bijective hj).2).apply_symm_apply c

theorem sum_place {h j : ℕ} (hj : j + 1 < h) (g : Fin h → ℕ) :
    ∑ a, ∑ b : Fin (grp h j a), g (place hj (toLex ⟨a, b⟩)) = ∑ c, g c := by
  rw [← Fintype.sum_sigma (fun p : Σ a, Fin (grp h j a) => g (place hj (toLex p)))]
  exact Equiv.sum_comp (toLex.trans (Equiv.ofBijective _ (place_bijective hj))) g

theorem fin_three_forall {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (a : Fin 3) : P a := by
  fin_cases a
  exacts [h0, h1, h2]

section Main

variable {h N j M : ℕ} (hj : j + 1 < h) (x : Fin h → IrrGL (k := k))

def fac (a : Fin 3) (b : Fin (grp h j a)) : IrrGL (k := k) := x (place hj (toLex ⟨a, b⟩))

def fac' (a : Fin 3) (b : Fin (grp h j a)) : IrrGL (k := k) :=
  x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ (place hj (toLex ⟨a, b⟩)))

theorem fac'_zero : fac' hj x 0 = fac hj x 0 := by
  funext b
  have hb : (b : ℕ) < j := b.2
  refine congrArg x (Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne ?_) (Fin.ne_of_val_ne ?_))
  · show off j 0 + b ≠ j
    simp [off]; omega
  · show off j 0 + b ≠ j + 1
    simp [off]; omega

theorem fac'_two : fac' hj x 2 = fac hj x 2 := by
  funext b
  refine congrArg x (Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne ?_) (Fin.ne_of_val_ne ?_))
  · show off j 2 + b ≠ j
    simp [off]; omega
  · show off j 2 + b ≠ j + 1
    simp [off]; omega

theorem place_one_zero : place hj (toLex ⟨1, (0 : Fin 2)⟩) = ⟨j, by omega⟩ := Fin.ext (by
  show off j 1 + 0 = j
  simp [off])

theorem place_one_one : place hj (toLex ⟨1, (1 : Fin 2)⟩) = ⟨j + 1, hj⟩ := Fin.ext (by
  show off j 1 + 1 = j + 1
  simp [off])

theorem fac_one : (fac hj x 1 : Fin 2 → IrrGL (k := k)) = ![x ⟨j, by omega⟩, x ⟨j + 1, hj⟩] := by
  funext b
  fin_cases b
  · exact congrArg x (place_one_zero hj)
  · exact congrArg x (place_one_one hj)

theorem fac'_one : (fac' hj x 1 : Fin 2 → IrrGL (k := k)) = ![x ⟨j + 1, hj⟩, x ⟨j, by omega⟩] := by
  funext b
  fin_cases b
  · refine congrArg x ?_
    refine (congrArg _ (place_one_zero hj)).trans (Equiv.swap_apply_left _ _)
  · refine congrArg x ?_
    refine (congrArg _ (place_one_one hj)).trans (Equiv.swap_apply_right _ _)

end Main

end GlobalTheory.CompanionTheory.BZSwap
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatFiniteSumOfProducts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatFiniteSumOfProducts
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem schwartzBruhat_eq_sum_pureTuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), IsSchwartzBruhat Φ → ∃ (N : ℕ) (φ : Fin N → (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : Fin N → (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))) (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ i, IsSchwartzArch (φ i)) ∧ (∀ i v, IsCompact (A i v) ∧ IsOpen (A i v)) ∧ (∀ i v, v ∉ S → A i v = latV b v) ∧ ∀ X, Φ X = ∑ i, pureN (φ i) (A i) X := by
  intro F E _ _ _ _ _ σ _ M J _ n _ d b Φ hΦ
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨k, Φinf, Φf, hinf, hf, hsum⟩ := hΦ
  choose s A S hA hAS hdec using fun i => GlobalTheory.CompanionTheory.WhitFree.DecN.exists_box_combN b (Φf i) (hf i)
  let e := Fintype.equivFin (Σ i : Fin k, (s i))
  refine ⟨Fintype.card (Σ i : Fin k, (s i)),
    fun j Z => Φinf (e.symm j).1 Z * Φf (e.symm j).1 (e.symm j).2,
    fun j => A (e.symm j).1 (e.symm j).2, Finset.univ.biUnion S, ?_, ?_, ?_, ?_⟩
  · intro j
    exact GlobalTheory.CompanionTheory.WhitFree.DecN.isSchwartzArch_const_mulN (hinf _) _
  · intro j v
    exact hA _ _ v
  · intro j v hv
    exact hAS _ _ (e.symm j).2.2 v
      (fun h => hv (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, h⟩))
  · intro X
    rw [hsum X]
    symm
    refine (Equiv.sum_comp e.symm (fun p : (Σ i : Fin k, (s i)) =>
      pureN (fun Z => Φinf p.1 Z * Φf p.1 p.2) (A p.1 p.2) X)).trans ?_
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hdec i (projFin X), Finset.mul_sum, ← Finset.sum_coe_sort (s i)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    unfold GlobalTheory.CompanionTheory.SiegelND.Coef.pureN
    exact mul_assoc _ _ _

end GlobalTheory.CompanionTheory.SiegelND.Coef
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatFiniteSumOfProductsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_finite_sum_of_products : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), IsSchwartzBruhat Φ → ∃ (N : ℕ) (φ : Fin N → (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : Fin N → (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))) (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ i, IsSchwartzArch (φ i)) ∧ (∀ i v, IsCompact (A i v) ∧ IsOpen (A i v)) ∧ (∀ i v, v ∉ S → A i v = latV b v) ∧ ∀ X, Φ X = ∑ i, pureN (φ i) (A i) X := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.schwartzBruhat_eq_sum_pureTuples | exact GlobalTheory.CompanionTheory.SiegelND.Coef.schwartzBruhat_eq_sum_pureTuples | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.schwartzBruhat_eq_sum_pureTuples <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHalfHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHalfHolds
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CompanionTheory.SiegelEisHalf

theorem eisHalf : EisHalf := by
  unfold SiegelEisensteinSeries.EisHalf
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY χ hχ c hc b K a hb hK ha s₁ f hf
  obtain ⟨Ê, t₁, hsum, hdiff⟩ := GlobalTheory.T.eisenstein_series_continuation F E σ B n Y r s hB hn hY b K a hb hK ha χ s₁ f hf
  obtain ⟨t₀, h23⟩ := GlobalTheory.T.eisenstein_vertical_bound F E σ B n Y r s hB hn hY b K a hb hK ha χ s₁ f hf
  obtain ⟨t, ht₀, ht₁⟩ : ∃ t : ℝ, t₀ ≤ t ∧ t₁ ≤ t := ⟨max t₀ t₁, le_max_left _ _, le_max_right _ _⟩
  have hsum' : ∀ z : ℂ, t < z.re → ∀ x : GlobalTheory.ThK.Dbl.G2 σ Y,
      HasSum (GlobalTheory.ThK.Dbl.eisTerm (GlobalTheory.ThK.Dbl.flat a f s₁ z) x) (Ê z x) :=
    fun z hz x => hsum z (lt_of_le_of_lt ht₁ hz) x
  obtain ⟨hmod, hcont, hbd⟩ := h23 t Ê ht₀ hsum'
  let v : ℂ → ↥(GlobalTheory.ThK.Dbl.modFun σ Y) := fun z =>
    if hz : t < z.re then ⟨fun x => Ê z x, hmod z hz⟩ else 0
  have hv : ∀ z : ℂ, t < z.re → ∀ x : GlobalTheory.ThK.Dbl.G2 σ Y,
      (↑(v z) : GlobalTheory.ThK.Dbl.G2 σ Y → ℂ) x = Ê z x := by
    intro z hz x
    simp only [v]
    rw [dite_eq_left hz]
  refine ⟨t, v, fun z hz x => by rw [hv z hz x]; exact hsum' z hz x, ?_⟩
  have hS : IsOpen {z : ℂ | t < z.re} := isOpen_lt continuous_const Complex.continuous_re
  apply GlobalTheory.CompanionTheory.WeakHolo.wholo_growForms v hS
  · intro x
    exact ((hdiff x).mono fun z hz => lt_of_le_of_lt ht₁ hz).congr fun z hz => hv z hz x
  · exact hcont.congr fun y hy => hv y.1 hy.1 y.2
  · intro Q hQS hQ
    rcases Q.eq_empty_or_nonempty with hQe | hne
    · exact ⟨0, 0, fun z hz => by simp [hQe] at hz⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := hQ.exists_isMinOn hne Complex.continuous_re.continuousOn
      obtain ⟨z₁, _, hmax⟩ := hQ.exists_isMaxOn hne Complex.continuous_re.continuousOn
      obtain ⟨C, N, hC⟩ := hbd z₀.re z₁.re (hQS hz₀)
      refine ⟨C, N, fun z hz x => ?_⟩
      rw [hv z (hQS hz) x]
      exact hC z (isMinOn_iff.mp hmin z hz) (isMaxOn_iff.mp hmax z hz) x

end GlobalTheory.CompanionTheory.SiegelEisHalf

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHalfHoldsStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_half_holds : EisHalf := by
  first | exact @GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf | exact GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf | (intros; apply GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf <;> assumption)
end
end
