module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.AlgCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.RibetLat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TeichmullerCharacterSpec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

theorem UpperTheory.teichmuller_character_spec :
    UpperTheory.V.Sd.S3.Teich := by
  intro l _ c x m hcop hx hres
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨-, -, -, -, -, -, -, -, hunit⟩ := dvrFacts l c.O
  have hnd : ¬ l ∣ m := fun h =>
    (Nat.Prime.one_lt (Fact.out : l.Prime)).ne' (Nat.Coprime.eq_one_of_dvd hcop h)
  have hm := hunit m hnd
  have hX : (x : c.O) ^ m = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  have hgeom : (∑ i ∈ Finset.range m, (x : c.O) ^ i) * ((x : c.O) - 1) = 0 := by
    rw [geom_sum_mul, hX, sub_self]
  have hres' : residue c.O (∑ i ∈ Finset.range m, (x : c.O) ^ i) = residue c.O (m : c.O) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_pow, hres]
  have hS : IsUnit (∑ i ∈ Finset.range m, (x : c.O) ^ i) := by
    rw [← isUnit_map_iff (residue c.O), hres', isUnit_map_iff]
    exact hm
  have h0 : (x : c.O) - 1 = 0 := hS.mul_right_eq_zero.mp hgeom
  exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h0)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticCharacterOfSubgroupIndexTwo
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.Ws UpperTheory.V.Sd.S2

private theorem exists_sign_character_index_two {Γ R : Type} [Group Γ] [CommRing R] (H : Subgroup Γ) (h : H.index = 2) :
    ∃ φ : Γ →* Rˣ, (∀ g ∈ H, φ g = 1) ∧ ∀ g ∉ H, φ g = -1 := by
  classical
  refine ⟨MonoidHom.mk' (fun g => if g ∈ H then 1 else -1) fun a b => ?_, fun g hg => if_pos hg, fun g hg => if_neg hg⟩
  by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [Subgroup.mul_mem_iff_of_index_two h, ha, hb]

theorem UpperTheory.exists_quadratic_character_of_subgroup_index_two :
    UpperTheory.V.Sd.S2.HypEx := by
  intro Ω _ _ _ l _ c D T hg hok htwo hdeep
  obtain ⟨k₀, hdeg, hreal, hsp, hps⟩ := htwo.quad
  haveI : FiniteDimensional ℚ k₀ := Module.finite_of_finrank_pos (by omega)
  haveI hnf : NumberField k₀ := {}
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) k₀⟩
  obtain ⟨hE, hO, hI⟩ := galEmbTop ℚ k₀ Ω
  have hfix : galOf ℚ k₀ Ω = k₀.fixingSubgroup := by
    ext σ
    rw [mem_galOf, IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x.1 x.2⟩
  have hr : (resQ k₀).range = k₀.fixingSubgroup := (range_galEmb ℚ k₀ Ω).trans hfix
  have hidx : k₀.fixingSubgroup.index = 2 := by rw [← hfix, hI, hdeg]
  obtain ⟨φ, h1, h2⟩ := exists_sign_character_index_two (R := PadicAlgCl l) k₀.fixingSubgroup hidx
  refine ⟨k₀, hnf, hreal, φ, ⟨hg, hok, htwo, hdeep, hdeg, ?_, ?_, hps, h1, h2⟩, hr, hidx, hE, ?_⟩
  · exact hsp 2 (by simp)
  · exact hsp l (by simp)
  · rw [← MonoidHom.coe_range, hr, ← hfix]
    exact hO
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricCubeRootMem
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

theorem UpperTheory.symmetric_cube_root_mem :
    UpperTheory.V.Sd.S3.RootMem := by
  intro l _ E a b c d x ha hb hc hd hb1 had hx hrel
  have hn : ∀ (σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l) (y : Qbar l), ‖σ y‖ = ‖y‖ := by
    intro σ y
    show spectralNorm ℚ_[l] (PadicAlgCl l) (σ y) = spectralNorm ℚ_[l] (PadicAlgCl l) y
    unfold spectralNorm
    rw [minpoly.algEquiv_eq]
  rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  have hrel' : c + d * σ x = (a + b * σ x) * σ x := by
    have h := congrArg σ hrel
    simpa only [map_add (f := _), map_mul, hσ a ha, hσ b hb, hσ c hc, hσ d hd] using h
  by_contra hne
  have hyn : ‖σ x‖ ≤ 1 := by rw [hn]; exact hx
  have key : (σ x - x) * (b * (x + σ x) - (d - a)) = 0 := by linear_combination hrel - hrel'
  have hsub : σ x - x ≠ 0 := sub_ne_zero.mpr hne
  have heq : b * (x + σ x) = d - a := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hsub)
  have hlt : ‖a - d‖ < 1 := by
    rw [← norm_neg, neg_sub, ← heq, norm_mul]
    have hxy : ‖x + σ x‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max x (σ x)).trans (max_le hx hyn)
    calc ‖b‖ * ‖x + σ x‖ ≤ ‖b‖ * 1 := mul_le_mul_of_nonneg_left hxy (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hb1
  rw [had] at hlt
  exact lt_irrefl _ hlt
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsSplitPrimeCmDatum
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

theorem UpperTheory.exists_splitPrime_cmDatum :
    UpperTheory.V.Sd.S3.SplitPrime := by
  intro Ω _ _ _ U hU hc M hM
  obtain ⟨N, hN, hNU⟩ := UpperTheory.V.CF.kwAbs Ω U hU hc
  obtain ⟨w, hw, hMw, hmod⟩ := Nat.exists_prime_gt_modEq_one M (Nat.mul_ne_zero hM.ne' hN.ne')
  have hwM : w ≡ 1 [MOD M] := Nat.ModEq.of_dvd (Dvd.intro N rfl) hmod
  have hwN : w ≡ 1 [MOD N] := Nat.ModEq.of_dvd (Dvd.intro_left M rfl) hmod
  refine ⟨w, hw, hMw, hwM, ?_⟩
  intro A hA g hg
  haveI : Fact (Nat.Prime w) := ⟨hw⟩
  have hcop : N.Coprime w := by
    have h := Nat.ModEq.gcd_eq hwN
    rw [Nat.gcd_one_left] at h
    exact Nat.Coprime.symm h
  obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω w A hA N hcop g hg
  apply hNU
  intro ζ hζ
  rw [hk ζ hζ]
  have hpow : w ^ k % N = 1 % N := by
    have h := Nat.ModEq.pow k hwN
    rwa [one_pow] at h
  rw [← Nat.div_add_mod (w ^ k) N, pow_add, pow_mul, hζ, one_pow, one_mul, hpow]
  rcases Nat.lt_or_ge 1 N with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_one]
  · have hN1 : N = 1 := by omega
    subst hN1
    simp only [pow_one] at hζ
    simp [hζ]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ComplexConjPlaceUnderEq
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem cPl_asIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (cPl w).asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E) :=
  (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)

private theorem conj_algebraMap {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsCMField K] [IsCMField M] (x : K) :
    IsCMField.complexConj M (algebraMap K M x) = algebraMap K M (IsCMField.complexConj K x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K M)) x).symm

theorem UpperTheory.complexConj_place_under_eq :
    UpperTheory.V.Af.Sol.ConjUnder := by
  intro K M _ _ _ _ _ _ _ w
  refine ⟨?_, ?_, ?_⟩
  · apply HeightOneSpectrum.ext
    rw [cPl_asIdeal]
    change (cPl w).asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = (w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M))).comap _
    rw [cPl_asIdeal, Ideal.comap_comap, Ideal.comap_comap]
    congr 1
    ext x
    exact conj_algebraMap (x : K)
  · show Nat.card (𝓞 M ⧸ (cPl w).asIdeal) = Nat.card (𝓞 M ⧸ w.asIdeal)
    refine Nat.card_congr (Ideal.quotientEquiv _ _
      (RingOfIntegers.mapRingEquiv (IsCMField.complexConj M).toRingEquiv) ?_).toEquiv
    rw [cPl_asIdeal]
    exact (Ideal.map_comap_of_surjective
      (RingOfIntegers.mapRingEquiv (IsCMField.complexConj M).toRingEquiv : 𝓞 M →+* 𝓞 M)
      (RingOfIntegers.mapRingEquiv _).surjective w.asIdeal).symm
  · apply HeightOneSpectrum.ext
    rw [cPl_asIdeal, cPl_asIdeal, Ideal.comap_comap]
    convert Ideal.comap_id w.asIdeal
    ext x
    exact IsCMField.complexConj_apply_apply M (x : M)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRibetLattice
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

theorem UpperTheory.exists_ribet_lattice :
    UpperTheory.V.Sd.S2.RibOf := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r hyp hch hd u hu
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  haveI : IsGalois k₀ Ω := {}
  have hc : Continuous (resQ k₀ : G k₀ Ω →* G ℚ Ω) := by
    have h := (galEmbTop ℚ k₀ Ω).1.continuous
    have e : (resQ k₀ : G k₀ Ω →* G ℚ Ω) = galEmb ℚ k₀ Ω := by
      ext σ x
      rw [galEmb_apply]; rfl
    rw [e]; exact h
  let H : Subgroup (G k₀ Ω) := T.F.fixingSubgroup.comap (resQ k₀)
  have hHo : IsOpen (H : Set (G k₀ Ω)) := T.F.fixingSubgroup_isOpen.preimage hc
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 (H.isClosed_of_isOpen hHo).isCompact
  have hg : resQ T.F T.g0 ∈ T.F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact T.g0.commutes ⟨x, hx⟩
  have huH : u ∈ H := by
    show resQ k₀ u ∈ T.F.fixingSubgroup
    rw [hu]; exact mul_mem hg hg
  obtain ⟨ρ', ⟨g, hρ⟩, q1, q2, q3, s, q4⟩ := ribetLat l H (r.comp H.subtype) 1 (((up D.ξ).comp (resQ k₀)).comp H.subtype)
    (hd.cont.comp continuous_subtype_val) (hd.irr H hHo) (fun s => ⟨by simp, hch.unit _ _⟩)
    (fun s i => by
      have := hd.res s i
      simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.comp_apply, MonoidHom.one_apply,
        Subgroup.coe_subtype] using this) ⟨u, huH⟩ (by
      have := hch.sq
      rw [← hu] at this
      exact this)
  have e : ∀ s : H, ((MulAut.conj g).toMonoidHom.comp r) s = ρ' s := fun s => (hρ s).symm
  refine ⟨(MulAut.conj g).toMonoidHom.comp r, ⟨g, fun _ => rfl⟩, ?_, ?_, fun h hh => ?_, s, s.2, ?_⟩
  · rw [e ⟨u, huH⟩]; exact q1
  · rw [e ⟨u, huH⟩]; exact q2
  · rw [e ⟨h, hh⟩]; exact q3 ⟨h, hh⟩
  · rw [e s]; exact q4
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DualBaseChangeOfFrobeniusDualityOfConjUnder
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.dualBaseChange_of_frobeniusDuality_of_conjUnder :
    UpperTheory.V.Af.Sol.FrobDualC → UpperTheory.V.Af.Sol.ConjUnder → UpperTheory.V.Af.Sol.DualBcC := by
  intro hF hU K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r π sat' huniq hbc hatt μ χ c P hL hc hpair
  obtain ⟨j, hj⟩ := hc
  let c' : G (maximalRealSubfield M) Ω := AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap M Ω))
  have hpair' : IsPairing c' (r.comp (resG K M Ω)) (cycBar M Ω l ^ (1 - (n : ℤ)) *
      (μ.comp (resG (maximalRealSubfield K) K Ω)).comp (resG K M Ω)) P := fun s s' hs =>
    hpair (resG K M Ω s) (resG K M Ω s') (AlgEquiv.ext fun x => DFunLike.congr_fun hs x)
  have h0 : Ideal.span {((l : ℕ) : 𝓞 M)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ((l : ℕ) : 𝓞 M) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have ht := (conjSrc_injective (IsCMField.complexConj M).toRingEquiv).tendsto_cofinite
  filter_upwards [hbc, ht.eventually hbc, hatt.2, ht.eventually hatt.2, hl,
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually (Bc.normGal K Ω l ι χ μ hL)]
    with w h1 h2 ⟨C, hC, hE⟩ ⟨C', hC', hE'⟩ hw ⟨hu, he⟩ f hf
  obtain ⟨e1, e2, -⟩ := hU K M w
  obtain ⟨-, e3, -⟩ := hU K K (w.under (𝓞 K))
  obtain ⟨B, hB, hs⟩ := h1 f hf
  obtain ⟨B', hB', hs'⟩ := h2 f (by
    change normV (cPl w) = normV ((cPl w).under (𝓞 K)) ^ f
    rw [e2, e1, e3, hf])
  obtain rfl := huniq _ _ _ hs hC
  obtain rfl := huniq _ _ _ hs' hC'
  have he' := (UpperTheory.frobenius_power_compatibility K M Ω l ι w f hf).2 _ _ he
  rw [← Units.val_pow_eq_pow_val] at he'
  have key := hF M Ω l ι n _ _ c' P ⟨j, hj⟩ hpair' w hw _ _ _ hE hE' he'
  have hB'' : (CG.mk π).HasSat (cPl (w.under (𝓞 K))) B' := e1 ▸ hB'
  have hT := UpperTheory.theta_satake_parameters_inverse K n π _ _ hB''
  rw [CG.hasSat_mk] at hT
  refine ⟨_, (CG.hasSat_mk ..).2 (GlobalTheory.SphGal.hasSatGL_twist K n _ (compNorm K χ) _ _ hu hT), ?_⟩
  convert hs using 1
  have k2 := congrArg (Multiset.map (· * (compNorm K χ).val (w.under (𝓞 K)) ^ f)) key
  simp only [Multiset.map_map, Function.comp_def, inv_mul_cancel_right] at k2 ⊢
  rw [← k2]
  simp only [mul_pow, inv_pow]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ContinuousMixFamily
noncomputable section

open UpperTheory.V.Sd.S2 ReciprocityTheory.Gal

namespace UpperTheory

private theorem mix_cont {k X : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [TopologicalSpace X] (γ : kˣ)
    {A B : X → Matrix (Fin 2) (Fin 2) k} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => mix γ (A x) (B x) := by
  have a : ∀ i j, Continuous fun x => A x i j := fun i j => hA.matrix_elem i j
  have b : ∀ i j, Continuous fun x => B x i j := fun i j => hB.matrix_elem i j
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [mix, div_eq_mul_inv] <;> fun_prop

theorem continuous_mix_family : UpperTheory.V.Sd.S2.MixCont := by
  intro l _ Γ₀ Γ _ _ _ _ _ j t α β ρ R hM hj hρ
  haveI hN : j.range.Normal := Subgroup.normal_of_index_eq_two hM.index
  have hc : ∀ h : Γ₀, ∃ h', j h' = t⁻¹ * j h * t := fun h => by
    have := hN.conj_mem (j h) ⟨h, rfl⟩ t⁻¹
    simpa using this
  choose c hc using hc
  have cc : Continuous c := by
    rw [hj.isInducing.continuous_iff]
    have : (j ∘ c) = fun h => t⁻¹ * j h * t := funext hc
    rw [this]
    have := hj.continuous
    fun_prop
  have ci : Continuous fun h : Γ₀ => h⁻¹ := by
    rw [hj.isInducing.continuous_iff]
    have : (j ∘ fun h : Γ₀ => h⁻¹) = fun h => (j h)⁻¹ := funext fun h => by simp
    rw [this]
    exact hj.continuous.inv
  have hv : Continuous fun h => (ρ h).val := Units.continuous_val.comp hρ
  have h1 : Continuous fun h => (R (j h)).val := by
    have : (fun h => (R (j h)).val) = fun h => mix (β / α) (ρ h) (ρ (c h)) :=
      funext fun h => hM.on h (c h) (hc h)
    rw [this]
    exact mix_cont _ hv (hv.comp cc)
  have h2 : Continuous (R ∘ j) := by
    rw [Units.continuous_iff]
    refine ⟨h1, ?_⟩
    have := h1.comp ci
    refine this.congr fun h => ?_
    simp only [Function.comp, map_inv]
  refine continuous_of_continuousAt_one R ?_
  have := (hj.continuousAt_iff (g := R) (x := 1)).1 h2.continuousAt
  rwa [map_one] at this

end UpperTheory
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsThetaCharacterCmDatum
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Af

private theorem exists_nontrivial_l_torsion_character {A C : Type} [Group A] [Finite A] [IsCyclic A] [CommGroup C] {l : ℕ} (hl : l ∣ Nat.card A)
    {z : C} (hz : z ≠ 1) (hzl : z ^ l = 1) : ∃ φ : A →* C, φ ≠ 1 ∧ ∀ a, φ a ^ l = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  have ho : orderOf z ∣ orderOf g := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    exact (orderOf_dvd_of_pow_eq_one hzl).trans hl
  have e : monoidHomOfForallMemZpowers hg ho g = z := monoidHomOfForallMemZpowers_apply_gen hg ho
  refine ⟨monoidHomOfForallMemZpowers hg ho, fun h => hz (by rw [← e, h, MonoidHom.one_apply]), fun a => ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  rw [map_zpow, e, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzl, one_zpow]

theorem UpperTheory.exists_theta_character_cmDatum : UpperTheory.V.Sd.S3.ThetaEx := by
  unfold UpperTheory.V.Sd.S3.ThetaEx
  intro Ω _ _ _ l _ w hw hwl
  unfold KillsMu
  haveI : Fact w.Prime := ⟨hw⟩
  have hlp : Nat.Prime l := Fact.out
  have hdvd : l ∣ Nat.card (ZMod w)ˣ := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hw]
    exact (Nat.modEq_iff_dvd' hw.one_lt.le).1 hwl.symm
  haveI : IsAlgClosed (Qbar l) := inferInstance
  haveI : NeZero (l : Qbar l) := ⟨by exact_mod_cast hlp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Qbar l) l
  let z : (Qbar l)ˣ := (hζ.isUnit hlp.ne_zero).unit
  have hz : z ≠ 1 := by
    intro h
    apply hζ.ne_one hlp.one_lt
    simpa [z] using congrArg Units.val h
  have hzl : z ^ l = 1 := by
    ext
    simp [z, hζ.pow_eq_one]
  obtain ⟨φ, hφ, hφl⟩ := exists_nontrivial_l_torsion_character (A := (ZMod w)ˣ) hdvd hz hzl
  refine ⟨φ.comp (UpperTheory.V.Chr.cls ℚ Ω w), ?_, ?_, ?_⟩
  · intro h
    apply hφ
    ext u
    obtain ⟨s, rfl⟩ := (UpperTheory.V.Chr.clsOnto Ω w).1 u
    have := DFunLike.congr_fun h s
    simpa using this
  · ext s
    simp [hφl]
  · intro s hs
    haveI : Fact (1 < w) := ⟨hw.one_lt⟩
    have h1 : UpperTheory.V.Chr.cls ℚ Ω w s = 1 :=
      (UpperTheory.V.Chr.clsFacts ℚ Ω w).2.2.1 s 1 (fun ζ hζ => by
        rw [Units.val_one, ZMod.val_one, pow_one]
        exact hs ζ hζ)
    rw [MonoidHom.comp_apply, h1, map_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharPowNTrivial
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem cls_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (s : G ℚ Ω)
    (hs : ∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ) : UpperTheory.V.Chr.cls ℚ Ω N s = 1 := by
  have hcs := UpperTheory.V.Chr.cls_spec (k := ℚ) (Ω := Ω) N s
  rcases Nat.lt_or_ge 1 N with hN | hN
  · haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : NeZero (N : Ω) := ⟨by exact_mod_cast NeZero.ne N⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
    have h1 : ζ ^ 1 = ζ ^ (UpperTheory.V.Chr.cls ℚ Ω N s : ZMod N).val := by
      rw [pow_one, ← hcs ζ hζ.pow_eq_one, hs ζ hζ.pow_eq_one]
    have hv := hζ.pow_inj hN (ZMod.val_lt _) h1
    haveI : Fact (1 < N) := ⟨hN⟩
    apply Units.ext
    rw [Units.val_one]
    apply ZMod.val_injective
    rw [ZMod.val_one, ← hv]
  · have hN1 : N = 1 := by
      have := NeZero.pos N
      omega
    subst hN1
    exact Subsingleton.elim _ _

theorem UpperTheory.cyclotomicChar_pow_N_trivial :
    UpperTheory.V.Sd.S3.KillsN := by
  intro Ω _ _ _ l _ c D hD
  unfold Ctx3 at hD
  obtain ⟨hg, h, t, e, ψ, hb, he0, het, hX, hIII, hA⟩ := hD
  cases hA with
  | mk he hpsi hS hxi =>
  obtain ⟨x, ξ', ξ₀, -, -, -, hξ⟩ := hxi
  have hl2 : l ≠ 2 := UpperTheory.V.GradeZeroInterpolatingElement.Raw.Good.l_odd hg
  have hlp : Nat.Prime l := Fact.out
  unfold Host.CaseIII at hIII
  have hne : l ≠ UpperTheory.V.pOne h.chi :=
    ((UpperTheory.V.HV.bchiFacts h t hb).2.2.2.2 l hlp hl2 hIII.1).2.2.2.2.2.1
  have hP : Nat.Prime (UpperTheory.V.pOne h.chi) := (UpperTheory.V.pK_pOne_prime_conditions h.chi).2.1.1
  refine ⟨UpperTheory.V.pOne h.chi * 2 ^ h.nIII l ψ, Nat.mul_pos hP.pos (by positivity), ?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hlp).1 hd with h1 | h1
    · exact hne ((Nat.prime_dvd_prime_iff_eq hlp hP).1 h1)
    · exact hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 (hlp.dvd_of_dvd_pow h1))
  · unfold KillsMu
    intro s hs
    have key : ∀ (M : ℕ) [NeZero M], M ∣ UpperTheory.V.pOne h.chi * 2 ^ h.nIII l ψ →
        UpperTheory.V.Chr.cls ℚ Ω M s = 1 := by
      intro M _ hM
      refine cls_one M s (fun ζ hζ => hs ζ ?_)
      obtain ⟨k, hk⟩ := hM
      rw [hk, pow_mul, hζ, one_pow]
    rw [hξ, MonoidHom.mul_apply]
    simp only [UpperTheory.V.Chr.dirG, MonoidHom.comp_apply]
    rw [key _ (dvd_mul_right _ _), key _ (dvd_mul_left _ _), map_one, map_one, mul_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricCubeLineExists
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem col_eq {k : Type} [Field k] (g r : GL (Fin 2) k) (a b : k) (h10 : (g * r * g⁻¹ : GL (Fin 2) k) 1 0 = 0)
    (h00 : (g * r * g⁻¹ : GL (Fin 2) k) 0 0 = a) (h11 : (g * r * g⁻¹ : GL (Fin 2) k) 1 1 = b) :
    r 0 0 * g⁻¹ 0 0 + r 0 1 * g⁻¹ 1 0 = a * g⁻¹ 0 0 ∧ r 1 0 * g⁻¹ 0 0 + r 1 1 * g⁻¹ 1 0 = a * g⁻¹ 1 0 ∧
      r 0 0 + r 1 1 = a + b := by
  have e : ((r : Matrix (Fin 2) (Fin 2) k) * (g⁻¹ : GL (Fin 2) k)) =
      ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g * r * g⁻¹ : GL (Fin 2) k) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have e0 := congrFun (congrFun e 0) 0
  have e1 := congrFun (congrFun e 1) 0
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at e0 e1
  have t : Matrix.trace ((g * r * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      Matrix.trace (r : Matrix (Fin 2) (Fin 2) k) := by
    rw [Units.val_mul, Matrix.trace_mul_comm, ← Units.val_mul, inv_mul_cancel_left]
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two] at t
  rw [h10, h00] at e0 e1
  rw [h00, h11] at t
  refine ⟨?_, ?_, t.symm⟩
  · rw [e0]; ring
  · rw [e1]; ring

theorem UpperTheory.symmetric_cube_line_exists :
    UpperTheory.V.Sd.S3.LineEx := by
  intro l _ Γ _ H ρ ξ κ hρ ⟨g, hg⟩ hκ ⟨s₀, hs₀, hne⟩
  have key := fun s : H => col_eq g (ρ s) _ _ ((hg s).1 1 0 (by decide)) ((hg s).2 0) ((hg s).2 1)
  have hdet : (g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 1 -
      (g⁻¹ : GL (Fin 2) (Qbar l)) 0 1 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 ≠ 0 := by
    have := (g⁻¹).det_ne_zero
    rwa [Matrix.det_fin_two] at this
  generalize (g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 = p at key hdet
  generalize (g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 = q at key hdet
  have hge : 1 ≤ ‖(κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1‖ := by
    by_contra hlt
    apply hne
    have h1 : ‖(κ 0 ⟨s₀, hs₀⟩ : Qbar l) - (ξ s₀ : Qbar l)‖ < 1 := hκ ⟨s₀, hs₀⟩
    rw [norm_sub_rev] at h1
    have e : (ξ s₀ : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) = ((ξ s₀ : Qbar l) - (κ 0 ⟨s₀, hs₀⟩ : Qbar l)) +
        (((κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1) + (ρ s₀ 1 1 - 1)) := by
      rw [Units.val_one]; ring
    unfold Cong
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 ?_)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (not_le.mp hlt) (hρ s₀).1)
  have hqp : ‖q‖ ≤ ‖p‖ := by
    have e : ((κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1) * q = ρ s₀ 1 0 * p := by
      have := (key ⟨s₀, hs₀⟩).2.1
      simp only at this
      linear_combination -this
    calc ‖q‖ ≤ ‖(κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1‖ * ‖q‖ := le_mul_of_one_le_left (norm_nonneg _) hge
      _ = ‖ρ s₀ 1 0‖ * ‖p‖ := by rw [← norm_mul, e, norm_mul]
      _ ≤ ‖p‖ := mul_le_of_le_one_left (norm_nonneg _) (hρ s₀).2
  have hp : p ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_le_zero_iff] at hqp
    simp [hqp] at hdet
  refine ⟨q / p, ?_, fun s => ?_⟩
  · rw [norm_div]
    exact div_le_one_of_le₀ hqp (norm_nonneg _)
  · obtain ⟨k1, k2, k3⟩ := key s
    have a1 : ρ s 0 0 + ρ s 0 1 * (q / p) = κ 0 s := by
      field_simp
      linear_combination k1
    refine ⟨a1, ?_, ?_⟩
    · field_simp
      linear_combination k2
    · linear_combination k3 - a1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsSquareRootOfCharacterNearOne
section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

private theorem add_lt {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)

private theorem sub_eq (h2 : ‖(2 : K)‖ = 1) {a b : K} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1) :
    ‖a - b‖ = ‖a ^ 2 - b ^ 2‖ := by
  have h := add_lt ha hb
  have h1 : ‖a + b‖ = 1 := by
    have e : a + b = 2 + ((a - 1) + (b - 1)) := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h2]; exact h.ne'), h2]
    exact max_eq_left h.le
  have e : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by ring
  rw [e, norm_mul, h1, one_mul]

private theorem mul_lt {a b : K} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1) : ‖a * b - 1‖ < 1 := by
  have e : a * b - 1 = (a - 1) * (b - 1) + ((a - 1) + (b - 1)) := by ring
  rw [e]
  refine add_lt ?_ (add_lt ha hb)
  rw [norm_mul]
  nlinarith [norm_nonneg (a - 1), norm_nonneg (b - 1)]

omit [IsUltrametricDist K] in
private theorem ex_root [IsAlgClosed K] (y : Kˣ) (hy : ‖(y : K) - 1‖ < 1) :
    ∃ x : Kˣ, x ^ 2 = y ∧ ‖(x : K) - 1‖ < 1 := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (y : K) (n := 2) (by norm_num)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact y.ne_zero (by rw [← hx]; ring)
  by_cases h : ‖x - 1‖ < 1
  · exact ⟨Units.mk0 x hx0, Units.ext (by simpa using hx), h⟩
  · refine ⟨Units.mk0 (-x) (neg_ne_zero.mpr hx0), Units.ext (by simpa using hx), ?_⟩
    have e : (y : K) - 1 = -((x - 1) * (-x - 1)) := by rw [← hx]; ring
    rw [e, norm_neg, norm_mul] at hy
    simp only [Units.val_mk0]
    by_contra h'
    push Not at h h'
    nlinarith

end

theorem UpperTheory.exists_square_root_of_character_near_one :
    UpperTheory.V.Sd.S2.SqrtChar := by
  intro l _ hl Γ _ _ η hη hc
  have h2 : ‖(2 : PadicAlgCl l)‖ = 1 := by
    have e : (2 : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) ((2 : ℕ) : ℚ_[l]) := by
      rw [map_natCast]; norm_num
    rw [e]
    erw [PadicAlgCl.norm_extends]
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes Fact.out Nat.prime_two).mpr hl
  have hc' : ∀ g, ‖((η g : (PadicAlgCl l)ˣ) : PadicAlgCl l) - 1‖ < 1 := fun g => by
    simpa [UpperTheory.V.Sd.Cong] using hc g
  choose d hd hd1 using fun g => ex_root (η g) (hc' g)
  have hv : ∀ g, ((d g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ^ 2 = η g := fun g => by
    rw [← hd g]; simp
  have hmul : ∀ g h, d (g * h) = d g * d h := fun g h => by
    apply Units.ext
    have := sub_eq h2 (hd1 (g * h)) (mul_lt (hd1 g) (hd1 h))
    rw [mul_pow, hv, hv, hv, map_mul, Units.val_mul, sub_self, norm_zero, norm_eq_zero, sub_eq_zero] at this
    simpa using this
  refine ⟨MonoidHom.mk' d hmul, ?_, hd, fun g => ?_⟩
  · rw [Units.isEmbedding_val₀.continuous_iff]
    have hη' : Continuous fun g => ((η g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := Units.continuous_val.comp hη
    rw [continuous_iff_continuousAt]
    intro g
    have h1 := (hη'.continuousAt (x := g))
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero] at h1 ⊢
    refine h1.congr fun x => ?_
    simp only [Function.comp, MonoidHom.mk'_apply]
    rw [sub_eq h2 (hd1 x) (hd1 g), hv, hv]
  · simpa [UpperTheory.V.Sd.Cong] using hd1 g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsSquareRootCharacter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem sqrt_ex {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O] (h2 : IsUnit (2 : O))
    (a : O) (ha : residue O a = 1) : ∃ x : O, x ^ 2 = a ∧ residue O x = 1 := by
  haveI : HenselianRing O (maximalIdeal O) := IsAdicComplete.henselianRing O (maximalIdeal O)
  have hev : eval 1 (X ^ 2 - C a) ∈ maximalIdeal O := by
    simp only [eval_sub, eval_pow, eval_X, eval_C, one_pow]
    rw [← residue_eq_zero_iff, map_sub, map_one, ha, sub_self]
  have hd : eval 1 (derivative (X ^ 2 - C a)) = (2 : O) := by
    simp
    exact one_add_one_eq_two
  obtain ⟨x, hx, hx1⟩ := HenselianRing.is_henselian (X ^ 2 - C a) (monic_X_pow_sub_C a two_ne_zero) 1 hev
    (by rw [hd]; exact h2.map _)
  refine ⟨x, ?_, ?_⟩
  · simpa [sub_eq_zero] using hx
  · rw [← sub_eq_zero, ← map_one (residue O), ← map_sub, residue_eq_zero_iff]
    exact hx1

private theorem add_unit {O : Type} [CommRing O] [IsLocalRing O] (h2 : IsUnit (2 : O)) {x y : O}
    (hx : residue O x = 1) (hy : residue O y = 1) : IsUnit (x + y) := by
  rw [← residue_ne_zero_iff_isUnit, map_add (f := _), hx, hy]
  have h2' : residue O (2 : O) = 1 + 1 := by
    rw [← map_one (residue O), ← map_add (f := _), one_add_one_eq_two]
  rw [← h2']
  exact (residue_ne_zero_iff_isUnit (2 : O)).mpr h2

private theorem sqrt_uniq {O : Type} [CommRing O] [IsLocalRing O] (h2 : IsUnit (2 : O)) {x y : O}
    (hx : residue O x = 1) (hy : residue O y = 1) (h : x ^ 2 = y ^ 2) : x = y := by
  have hu := add_unit h2 hx hy
  have hz : (x - y) * (x + y) = 0 := by linear_combination h
  exact sub_eq_zero.mp (hu.mul_left_eq_zero.mp hz)

theorem UpperTheory.exists_square_root_character :
    UpperTheory.V.Sd.S3.SqrtChar := by
  intro O _ _ _ h2 Γ _ _ μ hμ hc
  have ex : ∀ g, ∃ x : O, x ^ 2 = (μ g : O) ∧ residue O x = 1 := fun g => sqrt_ex h2 _ (hμ g)
  choose s hs1 hs2 using ex
  have hsu : ∀ g, IsUnit (s g) := fun g =>
    (residue_ne_zero_iff_isUnit _).mp (by rw [hs2 g]; exact one_ne_zero)
  let η : Γ →* Oˣ :=
    { toFun := fun g => (hsu g).unit
      map_one' := by
        apply Units.ext
        show s 1 = 1
        exact sqrt_uniq h2 (hs2 1) (map_one _) (by rw [hs1, map_one, Units.val_one, one_pow])
      map_mul' := by
        intro g k
        apply Units.ext
        show s (g * k) = s g * s k
        refine sqrt_uniq h2 (hs2 _) (by rw [map_mul, hs2, hs2, one_mul]) ?_
        rw [mul_pow, hs1, hs1, hs1, map_mul, Units.val_mul] }
  refine ⟨η, ?_, ?_, ?_, ?_⟩
  · intro g
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact hs1 g
  · intro g
    exact hs2 g
  · intro N
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    rw [isOpen_iff_forall_mem_open]
    intro g0 hg0
    refine ⟨_, ?_, (hc N).isOpen_fiber (Ideal.Quotient.mk _ (μ g0 : O)), rfl⟩
    intro g hg
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] at hg hg0 ⊢
    rw [← hg0]
    show Ideal.Quotient.mk (maximalIdeal O ^ N) (s g) = Ideal.Quotient.mk (maximalIdeal O ^ N) (s g0)
    rw [Ideal.Quotient.eq] at hg ⊢
    obtain ⟨w, hw⟩ := (add_unit h2 (hs2 g) (hs2 g0)).exists_right_inv
    have hd : s g - s g0 = ((μ g : O) - μ g0) * w := by
      rw [← hs1 g, ← hs1 g0]
      linear_combination (-(s g - s g0)) * hw
    rw [hd]
    exact Ideal.mul_mem_right _ _ hg
  · intro g hg
    apply Units.ext
    show s g = 1
    exact sqrt_uniq h2 (hs2 g) (map_one _) (by rw [hs1, hg, Units.val_one, one_pow])
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RayClassGroupFinite
open UpperTheory.V.Sd.Eis
open NumberField IsDedekindDomain Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V

private theorem idele_split (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : Ideles F) :
    TR.infId F (Units.map (TR.pInf F).toMonoidHom x) * finId F (Units.map (pFin F).toMonoidHom x) = x := by
  have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
  have h2 : ∀ x, TR.pInf F (sFin F x) = 0 := fun x => map_zero (TR.infEq F).symm
  have h3 : ∀ x, pFin F (TR.sInf F x) = 0 := fun x => rfl
  have h4 : ∀ x, pFin F (sFin F x) = x := fun x => rfl
  refine Units.ext (TR.ad_ext ?_ ?_)
  · change TR.pInf F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F x.val)) * (1 - sFin F 1 + sFin F (pFin F x.val))) = _
    simp [h, h2]
  · change pFin F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F x.val)) * (1 - sFin F 1 + sFin F (pFin F x.val))) = _
    simp [h3, h4]

private theorem cont_pInf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) :
    Continuous fun x : Ad F => TR.pInf F x v :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).continuous.comp
    ((continuous_apply v).comp continuous_fst)

open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic.Reduction in
theorem UpperTheory.ray_class_group_finite :
    UpperTheory.V.Sd.Eis.RayFin := by
  intro F _ _ _ H hK hR hf
  have hopen : IsOpen (H : Set (Ideles F)) := by
    apply H.isOpen_of_mem_nhds (g := 1)
    have c1 : Continuous (Units.map (pFin F).toMonoidHom : Ideles F → (Af F)ˣ) :=
      Continuous.units_map _ continuous_snd
    have h1 : ∀ᶠ x : Ideles F in 𝓝 1, finId F (Units.map (pFin F).toMonoidHom x) ∈ H := by
      have := c1.continuousAt (x := 1)
      rw [ContinuousAt, map_one] at this
      exact this hf
    have h2 : ∀ᶠ x : Ideles F in 𝓝 1, ∀ v, 0 < TR.pInf F x.val v := by
      rw [Filter.eventually_all]
      intro v
      have c : Continuous fun x : Ideles F => TR.pInf F x.val v := (cont_pInf F v).comp Units.continuous_val
      refine c.continuousAt.eventually (lt_mem_nhds ?_)
      simp
    filter_upwards [h1, h2] with x hx1 hx2
    rw [← idele_split F x]
    exact H.mul_mem (hR _ hx2) hx1
  refine ⟨hopen, ?_⟩
  have hsq : ∀ (ρ : ℝ) (hρ : 0 < ρ), ((posIdele ρ hρ : IdeleGroup F) : Ideles F) ^ 2 ∈ H := by
    intro ρ hρ
    set z : Ideles F := (posIdele ρ hρ : IdeleGroup F) with hz
    have e : Units.map (pFin F).toMonoidHom z = 1 := by
      refine Units.ext ?_
      ext v
      exact congrArg _ (posIdele_finite ρ hρ v)
    have e2 := idele_split F z
    rw [e, map_one, mul_one] at e2
    rw [← e2, ← map_pow]
    refine hR _ fun v => ?_
    set y := Units.map (TR.pInf F).toMonoidHom z
    have hy : y.val v ≠ 0 := by
      have := congrFun y.mul_inv v
      exact left_ne_zero_of_mul_eq_one this
    rw [Units.val_pow_eq_pow_val, Pi.pow_apply]
    positivity
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) one_pos 1
  have hcov : ∀ t : Ideles F, ∃ s ∈ S, s⁻¹ * t ∈ H := by
    intro t
    have hn : 2 * Module.finrank ℚ F ≠ 0 := mul_ne_zero two_ne_zero Module.finrank_pos.ne'
    have ht : 0 < (ideleModule F t : ℝ) := (ideleModule F t).2
    set ρ : ℝ := (ideleModule F t : ℝ) ^ (((2 * Module.finrank ℚ F : ℕ) : ℝ)⁻¹) with hρdef
    have hρ : 0 < ρ := Real.rpow_pos_of_pos ht _
    have hρn : ρ ^ (2 * Module.finrank ℚ F) = (ideleModule F t : ℝ) := Real.rpow_inv_natCast_pow ht.le hn
    have hzH := hsq ρ hρ
    have hzt : ideleModule F (posIdele ρ hρ ^ 2) = ideleModule F t := by
      refine Subtype.ext ?_
      rw [sq, map_mul, ← hρn, two_mul, pow_add, ← ideleModule_posIdele ρ hρ]
      rfl
    generalize (posIdele ρ hρ : IdeleGroup F) ^ 2 = z at hzH hzt
    have h1 : (ideleModule F (t * z⁻¹) : ℝ) = 1 := by
      rw [map_mul, map_inv, hzt, mul_inv_cancel]; rfl
    obtain ⟨c, hcS⟩ := hSm (t * z⁻¹) h1.ge h1.le
    refine ⟨_, hcS, ?_⟩
    have e : (diagonal F c * (t * z⁻¹))⁻¹ * t = z * (diagonal F c)⁻¹ := by
      rw [mul_inv, mul_inv, inv_inv, mul_assoc, mul_right_comm, inv_mul_cancel, one_mul, mul_comm]
    rw [e]
    exact H.mul_mem hzH (H.inv_mem (hK c))
  haveI : DiscreteTopology (Ideles F ⧸ H) := QuotientGroup.discreteTopology hopen
  have hfin : ((QuotientGroup.mk : Ideles F → Ideles F ⧸ H) '' S).Finite :=
    (hS.image QuotientGroup.continuous_mk).finite_of_discrete
  haveI : Finite (Ideles F ⧸ H) := by
    refine Set.finite_univ_iff.1 (hfin.subset fun q _ => ?_)
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨s, hs, hst⟩ := hcov t
    exact ⟨s, hs, QuotientGroup.eq.2 hst⟩
  exact Subgroup.finiteIndex_of_finite_quotient
end
