module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ThruBad
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PlainAtRTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.OrdExT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.PropEC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.HalfOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Rwwd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleResidualOfHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SharedDedup_Chars_of_red

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ROrdIrr
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Sd

private theorem inf_places (K : Type) [Field K] [NumberField K] : Infinite (HeightOneSpectrum (𝓞 K)) := by
  have : Infinite (HeightOneSpectrum (𝓞 ℚ)) :=
    Infinite.of_surjective _ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).surjective
  refine Infinite.of_surjective (fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 ℚ)) fun v => ?_
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) v.asIdeal
  exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

private theorem hom_or {Γ C : Type} [Group Γ] [CommGroup C] (I : Subgroup Γ) (f g h : Γ →* C)
    (H : ∀ s ∈ I, f s = g s ∨ f s = h s) : (∀ s ∈ I, f s = g s) ∨ ∀ s ∈ I, f s = h s := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨s, hs, e1⟩, t, ht, e2⟩ := hc
  have a := (H s hs).resolve_left e1
  have b := (H t ht).resolve_right e2
  rcases H _ (I.mul_mem hs ht) with e | e <;> simp only [map_mul] at e
  · exact e1 (mul_right_cancel (b ▸ e))
  · exact e2 (mul_left_cancel (a ▸ e))

private theorem chars_of_red {Γ : Type} [Group Γ] [TopologicalSpace Γ] {k : Type} [NormedField k] (r : Γ →* GL (Fin 2) k)
    (hc : Continuous r) (h : ¬ IsIrr r) : ∃ c d : Γ →* kˣ, Continuous c ∧ Continuous d ∧
      ∀ s, (r s : Matrix (Fin 2) (Fin 2) k).charpoly = (X - C (c s : k)) * (X - C (d s : k)) := _root_.DedupShared.dedup_chars_of_red_1 (Γ := Γ) (k := k) r hc h

private theorem charpoly_tri {K : Type} [Field K] (g r : GL (Fin 2) K)
    (h : ∀ i j, j < i → (g * r * g⁻¹ : GL (Fin 2) K) i j = 0) :
    (r : Matrix (Fin 2) (Fin 2) K).charpoly =
      (X - C ((g * r * g⁻¹ : GL (Fin 2) K) 0 0)) * (X - C ((g * r * g⁻¹ : GL (Fin 2) K) 1 1)) := by
  have e : ((g * r * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly =
      (r : Matrix (Fin 2) (Fin 2) K).charpoly := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj g _
  rw [← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => h i j hij), Fin.prod_univ_two]

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

private theorem cyc_ine {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)
    (hA : IsPlaceOver A v) {n : ℤ} (hn : n ≠ 0) : ∃ g ∈ Ine (F := F) A, cycBar F Ω l g ^ n ≠ 1 := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hv : A.valuation (l : Ω) < 1 := by
    simpa using (hA _).2 hl
  obtain ⟨u, hu⟩ := GlobalTheory.CycDec.exists_unit_infinite_order l
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ F Ω).fieldRange
  have : FiniteDimensional ℚ K :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F Ω)).toLinearEquiv.finiteDimensional
  have : Finite ((Ω ≃ₐ[ℚ] Ω) ⧸ K.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ K.fixingSubgroup_isOpen
  have : K.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := K.fixingSubgroup)) σ
  let g : G F Ω := { (σ ^ N).toRingEquiv with
    commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }
  have hD : σ ^ N ∈ Ine (F := ℚ) A := (Ine (F := ℚ) A).pow_mem hσ N
  have hc : cycZ F Ω l g = cycZ ℚ Ω l (σ ^ N) := rfl
  have hinj : Function.Injective
      (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) :=
    Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)
  refine ⟨g, hD, fun h => hu (N * n) (mul_ne_zero (by exact_mod_cast hN.ne') hn) (hinj ?_)⟩
  rw [map_one, ← h, cycBar, MonoidHom.comp_apply, hc, map_pow, hσu, zpow_mul, zpow_natCast, map_zpow]

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.ordIrr_n :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Sd.OrdIrr := by
  intro P F Ω _ _ _ _ _ _ l _ hl2 hs ι ξ s c m a π r hr
  by_contra hirr
  obtain ⟨c₁, c₂, hc₁, hc₂, hch⟩ := chars_of_red r hr.cont hirr

  have hI : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ A, IsPlaceOver A w →
      ∃ d : ℤ, d ≠ 0 ∧ ∀ g ∈ Ine (F := F) A, (c₁ / c₂) g = cycBar F Ω l g ^ d := by
    intro w hw A hA
    obtain ⟨κ, ⟨g, hg⟩, hκ, -⟩ := ordAbove P F Ω l hl2 hs ι ξ s c m a π r hr w hw A hA
    have hm := (hr.above w hw).2.1
    have key : ∀ t ∈ Ine (F := F) A, (X - C (c₁ t : Qbar l)) * (X - C (c₂ t : Qbar l)) =
        (X - C ((cycBar F Ω l t ^ m w 0 : (Qbar l)ˣ) : Qbar l)) * (X - C ((cycBar F Ω l t ^ m w 1 : (Qbar l)ˣ) : Qbar l)) := by
      intro t ht
      let t' : ↥(Dec (F := F) A) := ⟨t, Ine_le_Dec A ht⟩
      rw [← hch, charpoly_tri g _ (hg t').1, (hg t').2 0, (hg t').2 1, hκ 0 t' ht, hκ 1 t' ht]
    have hp : ∀ t ∈ Ine (F := F) A, c₁ t * c₂ t = cycBar F Ω l t ^ m w 0 * cycBar F Ω l t ^ m w 1 := fun t ht => by
      have := congrArg (eval 0) (key t ht)
      simp only [eval_mul, eval_sub, eval_X, eval_C, zero_sub, neg_mul_neg] at this
      exact Units.ext this
    rcases hom_or (Ine (F := F) A) c₁ (cycBar F Ω l ^ m w 0) (cycBar F Ω l ^ m w 1) (fun t ht => by
      have := congrArg (eval (c₁ t : Qbar l)) (key t ht)
      simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] at this
      exact (mul_eq_zero.1 this.symm).imp (fun e => Units.ext (sub_eq_zero.1 e)) fun e => Units.ext (sub_eq_zero.1 e)) with h | h
    · refine ⟨m w 0 - m w 1, by omega, fun t ht => ?_⟩
      have h1 := hp t ht
      rw [h t ht, MonoidHom.zpow_apply, mul_right_inj] at h1
      rw [MonoidHom.div_apply, h t ht, h1, MonoidHom.zpow_apply, zpow_sub, div_eq_mul_inv]
    · refine ⟨m w 1 - m w 0, by omega, fun t ht => ?_⟩
      have h1 := hp t ht
      rw [h t ht, MonoidHom.zpow_apply, mul_comm (_ ^ m w 0), mul_right_inj] at h1
      rw [MonoidHom.div_apply, h t ht, h1, MonoidHom.zpow_apply, zpow_sub, div_eq_mul_inv]
  obtain ⟨χ, -, art, n, hart, hn, hL⟩ := (algOfCyc P F Ω l ι).1 (c₁ / c₂) (hc₁.div' hc₂) fun w hw => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨d, -, hd⟩ := hI w hw A hA
    exact ⟨A, hA, d, 1, one_pos, fun t ht => by rw [hd t ht, zpow_neg, mul_inv_cancel, one_pow]⟩
  obtain ⟨χ₀, hχ₀⟩ := hr.pol
  obtain ⟨-, wt, HT, -, -, hG⟩ := UpperTheory.GalN.V.exRN (exR P) F Ω l ι 2 one_le_two π χ₀ hr.reg hχ₀
  have hG := hG r hr.cont hr.att
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  obtain rfl : n = 0 := by
    have hinf : Infinite (HeightOneSpectrum (𝓞 F)) := inf_places F
    obtain ⟨w, hw, ⟨B, hB, hF⟩, hu⟩ := (hl.and (hr.att.2.and (GlobalTheory.Mem.UnrAe.unr_ae_and_level F χ).1)).exists
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hR := UpperTheory.GalN.V.ratioW_of_hasSat P.toClassicalTheorems hG hw hA hB
    have r1 : ((r ((frob hA : Weil hA) : G F Ω)⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom).IsRoot
        (ι (c₁ (frob hA : G F Ω)⁻¹ : Qbar l)) := IsRoot.map (f := ι.toRingHom) (by rw [hch]; simp)
    have r2 : ((r ((frob hA : Weil hA) : G F Ω)⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom).IsRoot
        (ι (c₂ (frob hA : G F Ω)⁻¹ : Qbar l)) := IsRoot.map (f := ι.toRingHom) (by rw [hch]; simp)
    have e1 := UpperTheory.GalN.V.ratio_roots hr.cont hw hR r1 r2
    have e2 := UpperTheory.GalN.V.ratio_roots hr.cont hw hR r2 r1
    have e3 := hL.frob_unr hart (Or.inl hw) hu hA (isFrob_frob (h := hA))
    have e4 : ((χ.val w : ℂˣ) : ℂ) = ι (c₁ (frob hA : G F Ω)⁻¹) / ι (c₂ (frob hA : G F Ω)⁻¹) := by
      rw [← map_div₀, ← Units.val_div_eq_div_val, ← MonoidHom.div_apply, map_inv, Units.val_inv_eq_inv_val, e3, inv_inv,
        RingEquiv.apply_symm_apply]
    have p2 : 0 < ‖ι (c₂ (frob hA : G F Ω)⁻¹ : Qbar l)‖ := norm_pos_iff.2 ((map_ne_zero ι).2 (Units.ne_zero _))
    refine UpperTheory.GalN.V.type_zero_window χ n hn w ?_ ?_
    · rw [e4, norm_div, div_lt_iff₀ p2]; exact e1
    · rw [e4, norm_div, ← mul_div_assoc, lt_div_iff₀ p2, one_mul]; exact e2
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
    have hne : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ ⊤ := fun e => by
      have := congrArg Ideal.absNorm e
      rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top, pow_eq_one_iff] at this
      rcases this with h | h
      · exact (Fact.out : l.Prime).ne_one h
      · exact Module.finrank_pos.ne' h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact ⟨⟨M, hM.isPrime, fun e => h0 (le_bot_iff.1 (e ▸ hle))⟩, hle (Ideal.mem_span_singleton_self _)⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨d, hd0, hd⟩ := hI w hw A hA
  obtain ⟨N, hN, hu⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt F χ
  obtain ⟨g, hg, hne⟩ := cyc_ine hw hA (n := d * N) (mul_ne_zero hd0 (by exact_mod_cast hN.ne'))
  obtain ⟨x, hx, e⟩ := (hL.ine_image hart (Or.inr rfl) hA _).1 ⟨g, hg, rfl⟩
  have e2 : χ.loc w x ^ N = 1 := hu w x hx
  refine hne (Units.ext ?_)
  rw [zpow_mul, zpow_natCast, ← hd g hg, Units.val_pow_eq_pow_val, ← e, ← map_pow, ← Units.val_pow_eq_pow_val, e2]
  simp
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RwOfOrdForm
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Monosep
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Sd UpperTheory.GalN.V

theorem UpperTheory.GalN.V.L.monosep :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A w) (y : WD h) (g : ↥(Weil h)), deg g = 0 → (y.eig g).Nodup → y.mono0 := by
  intro F Ω _ _ _ _ _ A w h y g hg hnd
  induction y using WD.ind with
  | hP n a =>
    rw [WD.eig_mk] at hnd
    rw [WD.monodromyZero_ofWeilDeligneRepClass_iff]
    have key : ∀ β : ℂ, ∀ v ∈ Module.End.eigenspace (a.ρ g) β, a.N v = 0 := fun β v hv => by
      by_contra h0
      have hv0 : v ≠ 0 := by rintro rfl; exact h0 (map_zero _)
      have e := Module.End.mem_eigenspace_iff.1 hv
      have hNv : a.N v ∈ Module.End.eigenspace (a.ρ g) β := by
        refine Module.End.mem_eigenspace_iff.2 ?_
        have := LinearMap.congr_fun (a.comm g) v
        simpa [e, hg, smul_smul] using this
      have hle : Module.finrank ℂ (Module.End.eigenspace (a.ρ g) β) ≤ 1 := by
        have h1 : Module.finrank ℂ (Module.End.eigenspace (a.ρ g) β) ≤
            Module.finrank ℂ (Module.End.maxGenEigenspace (a.ρ g) β) :=
          Submodule.finrank_mono (by
            first
              | exact (Module.End.genEigenspace (a.ρ g) β).monotone le_top
              | exact Module.End.genEigenspace_le_maximal _ _ _
              | exact fun x hx => Module.End.mem_maxGenEigenspace _ _ _ |>.2 ⟨1, by simpa using hx⟩)
        rw [LinearMap.finrank_maxGenEigenspace_eq, ← Polynomial.count_roots] at h1
        exact h1.trans (Multiset.nodup_iff_count_le_one.1 hnd β)
      have hne : Module.End.eigenspace (a.ρ g) β ≠ ⊥ := fun hb => hv0 (by simpa [hb] using hv)
      have h1 : Module.finrank ℂ (Module.End.eigenspace (a.ρ g) β) = 1 :=
        le_antisymm hle (Submodule.one_le_finrank_iff.2 hne)
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.eigenspace (a.ρ g) β)
        (fun hz => hv0 (congrArg Subtype.val hz))).1 h1 ⟨a.N v, hNv⟩
      have hc' : a.N v = c • v := (congrArg Subtype.val hc).symm
      obtain ⟨k, hk⟩ := a.nilpotent
      have hpow : ∀ m : ℕ, (a.N ^ m) v = c ^ m • v := fun m => by
        induction m with
        | zero => simp
        | succ m ih => rw [pow_succ, Module.End.mul_apply, hc', map_smul, ih, smul_smul, pow_succ']
      have hz : c ^ k • v = 0 := by rw [← hpow k, hk]; rfl
      have hc0 : c = 0 := by
        rcases smul_eq_zero.1 hz with h2 | h2
        · first
            | exact pow_eq_zero_iff (by rintro rfl; simp at h2) |>.1 h2
            | exact eq_zero_of_pow_eq_zero h2
        · exact absurd h2 hv0
      exact h0 (by rw [hc', hc0, zero_smul])
    have top : ⨆ β : ℂ, Module.End.eigenspace (a.ρ g) β = ⊤ := (a.semisimple g).iSup_eigenspace_eq_top
    refine LinearMap.ker_eq_top.1 (top_le_iff.1 ?_)
    rw [← top]
    exact iSup_le fun β v hv => key β v hv
end

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.GalN.V.rw_of_ordForm (PH : HypothesesH) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ) (s c m a π r)
    (H : OrdForm ι ξ s c m a π r) : UpperTheory.GalN.V.RW ι r := by
  have P := PH.toClassicalTheorems
  refine UpperTheory.GalN.V.L.rwwd F Ω l ι 2 r H.cont fun w hl A h => ?_
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := UpperTheory.GalN.V.exRN (exR PH) F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F 2 π w
  obtain ⟨rc, hrc⟩ := P.exists_rec h
  refine hG.ratio w hl A h rc hrc σ hσ ?_
  by_cases hc : c w = 0
  · obtain ⟨v, hv, hf⟩ := H.sph w hc
    let τ := π.locRep w
    let R := MonoidAlgebra ℂ (GL (Fin 2) (w.adicCompletion F))
    have : IsSimpleModule R σ.ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule σ.ρ).1 σ.irred
    have htop : isotypicComponent R τ.asModule σ.ρ.asModule = ⊤ := by
      refine top_le_iff.1 fun y _ => ?_
      have hy : τ.asModuleEquiv y ∈ (⊤ : Submodule ℂ _) := trivial
      rw [← (hiso σ hσ).2] at hy
      rw [← τ.asModuleEquiv.symm_apply_apply y]
      refine Submodule.iSup_induction _ (motive := fun z => τ.asModuleEquiv.symm z ∈ _) hy ?_ ?_ ?_
      · rintro f _ ⟨x, rfl⟩
        let x' : σ.ρ.asModule := σ.ρ.asModuleEquiv.symm x
        let f' := Representation.IntertwiningMap.equivLinearMapAsModule σ.ρ τ
          ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
        change f' x' ∈ _
        rcases f'.injective_or_eq_zero with h | h
        · have hrange : LinearMap.range f' ≤ isotypicComponent R τ.asModule σ.ρ.asModule :=
            le_sSup ⟨(LinearEquiv.ofInjective f' h).symm⟩
          exact hrange ⟨x', rfl⟩
        · rw [h, LinearMap.zero_apply]
          exact Submodule.zero_mem _
      · rw [τ.asModuleEquiv.symm.map_zero]
        exact Submodule.zero_mem _
      · intro x y hx hy
        rw [τ.asModuleEquiv.symm.map_add]
        exact add_mem hx hy
    have : IsSemisimpleModule R τ.asModule :=
      IsSemisimpleModule.congr (M := isotypicComponent R τ.asModule σ.ρ.asModule)
        (LinearEquiv.ofTop _ htop).symm
    have hTv : ∃ T : τ.asModule →ₗ[R] σ.ρ.asModule, T v ≠ 0 := by
      obtain ⟨m, hm, hvm⟩ : ∃ m : Submodule R τ.asModule, IsCoatom m ∧ v ∉ m := by
        by_contra hn
        push Not at hn
        refine hv ((Submodule.mem_bot (M := τ.asModule) R).1 ?_)
        rw [← IsSemisimpleModule.jacobson_eq_bot R τ.asModule]
        exact Submodule.mem_sInf.2 hn
      obtain ⟨W, hW⟩ := exists_isCompl m
      have : IsSimpleModule R W := isSimpleModule_iff_isAtom.2 (hW.isCoatom_iff_isAtom.1 hm)
      obtain ⟨e⟩ := IsIsotypicOfType.of_isotypicComponent_eq_top htop W
      refine ⟨e.toLinearMap ∘ₗ W.projectionOnto m hW.symm, fun he => hvm ?_⟩
      apply (Submodule.projectionOnto_apply_eq_zero_iff hW.symm).1
      apply e.injective
      rw [e.map_zero]
      exact he
    obtain ⟨T, hTv⟩ := hTv
    let T' := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ.ρ).symm T
    obtain ⟨B, hB⟩ := (satLoc P F 2 w σ).1 ⟨T' v, hTv, fun u hu => by
      have hmem : u ∈ K1 w 0 := by
        obtain ⟨k, rfl⟩ := hu
        refine ⟨k, ?_, rfl⟩
        have : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
          Ideal.Quotient.subsingleton_iff.2 (by simp)
        exact Subsingleton.elim (α := Fin 2 → _) _ _
      exact (LinearMap.congr_fun (T'.2 u) v).symm.trans (congrArg T' (hf u hmem))⟩
    exact WD.unr_mono0 _ (UpperTheory.GalN.V.unr_algNorm hrc σ B hB)
  · have hA : ¬ A.valuation (l : Ω) < 1 := fun e => hl (((UpperTheory.V.Base.places F Ω l A).2.2.1 w h).1 e)
    obtain ⟨s₀, hs₀, h0⟩ := IsConcreteLE.not_le_iff_exists.1 fun e => ((H.ram w A h).1 e).elim hc hl
    obtain ⟨g, hg⟩ := UpperTheory.V.Sd.ordAway_n PH F Ω l ι ξ s c m a π r H A hA
    refine UpperTheory.GalN.V.L.monosep F Ω A w h _ (ineIncl h ⟨s₀, hs₀⟩) (deg_ineIncl _) ?_
    have k : UpperTheory.GalN.V.WDN ι r (rc (algNorm σ)) :=
      .of_aw hl H.cont ⟨(hG.away w hl A h rc hrc σ hσ).pol, (hG.away w hl A h rc hrc σ hσ).n0⟩
    have e : (r s₀ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C 1) * (X - C (ξ s₀ : Qbar l)) := by
      rw [← Matrix.charpoly_units_conj g, ← Matrix.coe_units_inv, ← Units.val_mul, ← Units.val_mul, hg s₀ hs₀,
        Matrix.charpoly_diagonal, Fin.prod_univ_two]
      rfl
    rw [WD.eig, ← k.charpoly hl, coe_ineIncl, e]
    have h1 : ι (ξ s₀ : Qbar l) ≠ 1 := fun e' => h0 (Units.ext (ι.injective (by simpa using e')))
    rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_sub, map_X, map_C, map_C]
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C, roots_X_sub_C]
    simpa using h1.symm
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.SplitTwo
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.GalN.V

private theorem ratio_ne {A B q x y : ℝ} (hA : 0 < A) (hB : 0 < B) (hq : 1 < q) (h1 : A < q * B) (h2 : B < q * A)
    (h3 : A ^ 2 ≠ q * B ^ 2) (h4 : B ^ 2 ≠ q * A ^ 2)
    (hx : x = A / B ∨ x = 1 ∨ x = B / A) (hy : y = A / B ∨ y = 1 ∨ y = B / A) : x ≠ q * y := by
  have hAn : A ≠ 0 := hA.ne'
  have hBn : B ≠ 0 := hB.ne'
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> intro h <;> field_simp at h
  all_goals first
    | nlinarith
    | exact h3 (by nlinarith)
    | exact h4 (by nlinarith)

private theorem split_two {K : Type} [Field K] [IsAlgClosed K] (g : GL (Fin 2) K) :
    ∃ a b : Kˣ, (g : Matrix (Fin 2) (Fin 2) K).charpoly = (X - C (a : K)) * (X - C (b : K)) := by
  set M : Matrix (Fin 2) (Fin 2) K := (g : Matrix (Fin 2) (Fin 2) K) with hM
  have hmon : M.charpoly.Monic := Matrix.charpoly_monic M
  have hsplit : M.charpoly.Splits := IsAlgClosed.splits _
  have hprod := hsplit.eq_prod_roots_of_monic hmon
  have hcard : M.charpoly.roots.card = 2 := by
    rw [← hsplit.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
  have hdet : M.det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det M).mp (Units.isUnit g)
    exact this.ne_zero
  have hnz : ∀ c ∈ M.charpoly.roots, c ≠ 0 := by
    intro c hc h0
    rw [Polynomial.mem_roots hmon.ne_zero, Polynomial.IsRoot, Matrix.eval_charpoly, h0] at hc
    apply hdet
    simpa [Matrix.det_neg] using hc
  have ha : a ≠ 0 := hnz a (by rw [hab]; simp)
  have hb : b ≠ 0 := hnz b (by rw [hab]; simp)
  refine ⟨Units.mk0 a ha, Units.mk0 b hb, ?_⟩
  rw [hprod, hab]
  simp

theorem UpperTheory.V.Z.Sym.Unl.adUnl :
    UpperTheory.V.Z.Sym.Unl.AdUnl := by
  intro F Ω _ _ _ _ _ l _ ι r hR hN w hw A hA _
  obtain ⟨s, hs⟩ := exists_isFrob hA
  refine ⟨s, 1, le_rfl, by simpa using hs, ?_⟩
  intro α β hα hβ k hk heq
  obtain ⟨a, b, hab⟩ := split_two (r s)
  have hc := (ad0Facts l (G F Ω) r).2.2.2.2.1 s a b hab
  have ra : (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot (a : Qbar l) := by
    rw [hab]; simp
  have rb : (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot (b : Qbar l) := by
    rw [hab]; simp
  have hA0 : 0 < ‖ι (a : Qbar l)‖ := norm_pos_iff.2 (by simp)
  have hB0 : 0 < ‖ι (b : Qbar l)‖ := norm_pos_iff.2 (by simp)
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by
    have := hR w hw A hA s hs _ _ ra ra
    by_contra h
    nlinarith [not_lt.mp h]
  have root : ∀ x : Qbar l, (ad0 r s : Matrix (Fin 3) (Fin 3) (Qbar l)).charpoly.IsRoot x →
      ‖ι x‖ = ‖ι (a : Qbar l)‖ / ‖ι (b : Qbar l)‖ ∨ ‖ι x‖ = 1 ∨ ‖ι x‖ = ‖ι (b : Qbar l)‖ / ‖ι (a : Qbar l)‖ := by
    intro x hx
    rw [hc] at hx
    simp only [IsRoot.def, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at hx
    rcases hx with (rfl | rfl) | rfl
    · left; simp
    · right; left; simp
    · right; right; simp
  have hn : ‖ι α‖ ^ k = (((normV w : ℕ) : ℝ) * ‖ι β‖) ^ k := by
    have := congrArg (fun z => ‖ι z‖) heq
    simpa [map_pow, map_mul, norm_pow, norm_mul, Complex.norm_natCast] using this
  have hn' : ‖ι α‖ = ((normV w : ℕ) : ℝ) * ‖ι β‖ :=
    (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (by omega)).1 hn
  exact ratio_ne hA0 hB0 hq (hR w hw A hA s hs _ _ ra rb) (hR w hw A hA s hs _ _ rb ra)
    (hN w hw A hA s hs _ _ ra rb) (hN w hw A hA s hs _ _ rb ra) (root α hα) (root β hβ) hn'
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.RootOfSmul
open UpperTheory.V.Af UpperTheory.GalN.V

private theorem root_of_smul {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (c : K) (hc : c ≠ 0) (α : K)
    (h : (c • M).charpoly.IsRoot α) : M.charpoly.IsRoot (c⁻¹ * α) := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly] at h ⊢
  have key : (Matrix.scalar (Fin n)) α - c • M = c • ((Matrix.scalar (Fin n)) (c⁻¹ * α) - M) := by
    rw [smul_sub, Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
    congr 2
    ext i
    simp [mul_inv_cancel_left₀ hc]
  rw [key, Matrix.det_smul] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd (pow_eq_zero_iff'.mp h1).1 hc
  · exact h1

theorem UpperTheory.V.Z.Sym.Unl.twOk :
    UpperTheory.V.Z.Sym.Unl.TwOk := by
  intro F Ω _ _ _ _ l _ n ι r δ
  have hc : ∀ s, ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l) ≠ 0 := fun s => Units.ne_zero _
  have hroot : ∀ s α, (↑((tw r δ) s) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.IsRoot α →
      (↑(r s) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.IsRoot (((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)⁻¹ * α) := by
    intro s α h
    rw [tw_val] at h
    exact root_of_smul _ _ (hc s) α h
  have hnorm : ∀ s α, ‖ι α‖ = ‖ι ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)‖ *
      ‖ι (((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)⁻¹ * α)‖ := by
    intro s α
    rw [← norm_mul, ← map_mul, mul_inv_cancel_left₀ (hc s)]
  have hpos : ∀ s, 0 < ‖ι ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)‖ := by
    intro s
    exact norm_pos_iff.mpr ((map_ne_zero ι).mpr (hc s))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · intro w hw A hA s hs α β hα hβ heq
    apply h w hw A hA s hs _ _ (hroot s α hα) (hroot s β hβ)
    have hp := hpos s
    rw [hnorm s α, hnorm s β, mul_pow, mul_pow] at heq
    have hp2 : 0 < ‖ι ((δ s : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l)‖ ^ 2 := by positivity
    have := heq
    rw [mul_left_comm] at this
    exact mul_left_cancel₀ hp2.ne' this
  · intro w hw A hA s hs α β hα hβ
    have key := h w hw A hA s hs _ _ (hroot s α hα) (hroot s β hβ)
    have hp := hpos s
    rw [hnorm s α, hnorm s β, mul_left_comm]
    exact mul_lt_mul_of_pos_left key hp
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published

namespace UpperTheory.V.Sd.EG

section Norm

variable {l : ℕ} [hl : Fact l.Prime]

variable (l) in
private def U : Subgroup (Qbar l)ˣ where
  carrier := {u | ‖(u : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    have e : ((u * v : (Qbar l)ˣ) : Qbar l) - 1 = u * (v - 1) + (u - 1) := by push_cast; ring
    show ‖_‖ < 1
    rw [e]
    refine small_add ?_ hu
    rw [norm_mul, norm_eq_one_of hu, one_mul]
    exact hv
  inv_mem' {u} hu := by
    have e : (u : Qbar l) * (((u⁻¹ : (Qbar l)ˣ) : Qbar l) - 1) = -(u - 1) := by rw [mul_sub, Units.mul_inv]; ring
    have := congrArg norm e
    rw [norm_mul, norm_eq_one_of hu, one_mul, norm_neg] at this
    show ‖_‖ < 1
    rw [this]
    exact hu

end Norm

section Gal

variable {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

end Gal

end UpperTheory.V.Sd.EG

open UpperTheory.V.Sd in
def UpperTheory.V.Z.Sym.W.PropEGc : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), UpperTheory.V.Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ UpperTheory.V.Z.Win.Birth.PR ι ρ ∧ UpperTheory.GalN.V.RW ι ρ ∧ UpperTheory.V.Z.Sym.Unl.NoHalf ι ρ
