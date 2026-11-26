module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupKummer

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedLocalInvariantExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBrauerRootsUnityEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBrauerRootsUnityEquiv
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.LocalInv

theorem nonempty_H2_muLoc_equiv_zmod : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → Nonempty (H2 (muLoc F l r A) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) := by
  intro F Ω _ _ _ _ _ l _ r hr A v hA
  exact (GlobalTheory.CompanionTheory.Hypotheses₂.localTateDuality F Ω l r (ZMod (l ^ r)) A (muLoc F l r A) v hr hA
    (GlobalTheory.TameQuot.contAction_muDec A l r)).1

end GlobalTheory.CompanionTheory.LocalInv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBrauerRootsUnityEquivStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_brauer_roots_unity_equiv : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → Nonempty (H2 (muLoc F l r A) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) := by
  first | exact @GlobalTheory.CompanionTheory.LocalInv.nonempty_H2_muLoc_equiv_zmod | exact GlobalTheory.CompanionTheory.LocalInv.nonempty_H2_muLoc_equiv_zmod | (intros; apply GlobalTheory.CompanionTheory.LocalInv.nonempty_H2_muLoc_equiv_zmod <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupUniformizer
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterContinuous
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterContinuous
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

namespace GlobalTheory.CompanionTheory.LocalUnram


open GroundTheory.LocalField.Abstract in
theorem continuous_of_additive_of_frobenius_eq_one :
    ∀ (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
      [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (n : ℕ) [NeZero n] (χ : Gal(Ω/K) → ZMod n),
      (∀ g h, χ (g * h) = χ g + χ h) →
      (∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1) → Continuous χ := by
  intro K Ω _ _ _ _ _ _ _ n _ χ hadd h1
  obtain ⟨hcont, hsurj, -⟩ := unramifiedDegree_spec (K := K) (Ω := Ω)
  obtain ⟨N, rfl⟩ : ∃ N : ℕ+, (N : ℕ) = n := ⟨⟨n, NeZero.pos n⟩, rfl⟩
  have hone : χ 1 = 0 := by
    have h := hadd 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  have hinv : ∀ g, χ g⁻¹ = -χ g := fun g => by
    have h := hadd g⁻¹ g
    rw [inv_mul_cancel, hone] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hpow : ∀ (g : Gal(Ω/K)) (k : ℕ), χ (g ^ k) = k • χ g := fun g k => by
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hadd, ih, succ_nsmul]
  obtain ⟨f, hf⟩ := hsurj (Multiplicative.ofAdd 1)
  have hχf : χ f = 1 := h1 f hf
  have hker : ∀ g, unramifiedDegree K Ω g = 1 → χ g = 0 := fun g hg => by
    have h := h1 (g * f) (by rw [map_mul, hg, one_mul, hf])
    rw [hadd, hχf] at h
    exact add_eq_right.mp h
  have key : ∀ g, χ g = ProfiniteInteger.proj N (Multiplicative.toAdd (unramifiedDegree K Ω g)) := by
    intro g
    set x := Multiplicative.toAdd (unramifiedDegree K Ω g) with hx
    set k : ℕ := (ProfiniteInteger.proj N x).val with hk
    have hkc : ((k : ℕ) : ZMod (N : ℕ)) = ProfiniteInteger.proj N x := ZMod.natCast_zmod_val _
    have hz : ProfiniteInteger.proj N (x - (k : ProfiniteInteger)) = 0 := by
      rw [map_sub, map_natCast, hkc, sub_self]
    obtain ⟨w, hw⟩ := ProfiniteInteger.exists_eq_nsmul_of_proj_eq_zero hz
    obtain ⟨t, ht⟩ := hsurj (Multiplicative.ofAdd w)
    have hdeg : unramifiedDegree K Ω (g * (f ^ k)⁻¹ * (t ^ (N : ℕ))⁻¹) = 1 := by
      simp only [_root_.map_mul, _root_.map_inv, _root_.map_pow, hf, ht]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_mul, toAdd_inv, toAdd_inv, toAdd_pow, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd,
        toAdd_one, ← hx, ← hw, nsmul_eq_mul, mul_one]
      ring
    have h0 := hker _ hdeg
    rw [hadd, hadd, hinv, hinv, hpow, hpow, hχf] at h0
    have hN : (N : ℕ) • χ t = 0 := by simp
    rw [hN, neg_zero, add_zero, nsmul_eq_mul, mul_one, hkc] at h0
    exact add_neg_eq_zero.mp h0
  have hχ : χ = fun g => ProfiniteInteger.proj N (Multiplicative.toAdd (unramifiedDegree K Ω g)) :=
    funext key
  rw [hχ]
  exact (ProfiniteInteger.continuous_proj N).comp (continuous_toAdd.comp hcont)

end GlobalTheory.CompanionTheory.LocalUnram
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterContinuousStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_character_continuous : ∀ (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (n : ℕ) [NeZero n] (χ : Gal(Ω/K) → ZMod n), (∀ g h, χ (g * h) = χ g + χ h) → (∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1) → Continuous χ := by
  first | exact @GlobalTheory.CompanionTheory.LocalUnram.continuous_of_additive_of_frobenius_eq_one | exact GlobalTheory.CompanionTheory.LocalUnram.continuous_of_additive_of_frobenius_eq_one | (intros; apply GlobalTheory.CompanionTheory.LocalUnram.continuous_of_additive_of_frobenius_eq_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerOrderEqOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerOrderEqOne
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

namespace GlobalTheory.CompanionTheory.Completion

theorem valuation_eq_exp_neg_one_of_mem_of_notMem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (ϖ : 𝓞 F) (h1 : ϖ ∈ v.asIdeal) (h2 : ϖ ∉ v.asIdeal ^ 2) :
    v.valuation F (ϖ : F) = WithZero.exp (-1 : ℤ) := by
  have hval : v.valuation F (ϖ : F) = v.intValuation ϖ := v.valuation_of_algebraMap ϖ
  rw [hval]
  have hle : v.intValuation ϖ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem ϖ 1).2 (by simpa using h1)
  have hnle : ¬ v.intValuation ϖ ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((v.intValuation_le_pow_iff_mem ϖ 2).1 h)
  have hne : v.intValuation ϖ ≠ 0 := by
    intro h
    apply hnle
    rw [h]
    exact zero_le
  rw [← WithZero.exp_log hne] at hle hnle ⊢
  rw [WithZero.exp_le_exp] at hle hnle
  congr 1
  push_cast at hle hnle
  omega

theorem ord_algebraMap_eq_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ord (algebraMap F (v.adicCompletion F) (ϖ : F)) = 1 := by
  intro F _ _ v ϖ h1 h2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion F]
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    GlobalTheory.adicCompletion_valuation_map_uniformiser F v (v.adicCompletion F) (RingEquiv.refl _)
      (fun a => by
        rw [GroundTheory.Global.mem_valuationInteger_iff]
        exact Iff.rfl) π hπ
  have hx : Valued.v (algebraMap F (v.adicCompletion F) (ϖ : F)) = WithZero.exp (-1 : ℤ) := by
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (ϖ : F)).trans
      (valuation_eq_exp_neg_one_of_mem_of_notMem F v ϖ h1 h2)
  have heq : valuation (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (ϖ : F)) =
      valuation (v.adicCompletion F) (π : v.adicCompletion F) :=
    le_antisymm
      ((ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v _ _).2
        (le_of_eq (hx.trans hv.symm)))
      ((ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v _ _).2
        (le_of_eq (hv.trans hx.symm)))
  have hn := (normalizedValuation_eq_iff (K := v.adicCompletion F)).2 heq
  rw [← ord_uniformizer hπ]
  simp only [ord, hn]

end GlobalTheory.CompanionTheory.Completion
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerOrderEqOneStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_order_eq_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ord (algebraMap F (v.adicCompletion F) (ϖ : F)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one | exact GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one | (intros; apply GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DecompositionGroupLocalGalois
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DecompositionGroupLocalGalois
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Dict

theorem isFrob_of_unramifiedDegree_eq_one : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) [IsSepClosure (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F))], IsPlaceOver A v → ∀ (ι : Ω →ₐ[F] AlgebraicClosure (v.adicCompletion F)) (σ : G F Ω) (g : Gal(AlgebraicClosure (v.adicCompletion F)/v.adicCompletion F)), σ ∈ Dec (F := F) A → (∀ x, ι (σ x) = g (ι x)) → unramifiedDegree (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) g = Multiplicative.ofAdd 1 → IsFrob (F := F) A (normV v) σ := by
  intro F Ω _ _ _ _ _ A v _ hA ι σ g hσ hι hg
  refine (GlobalTheory.FrobTeich.isFrob_iff_teichmuller F Ω A v hA σ).2 ⟨hσ, fun z m hm hz => ?_⟩
  have hcard : Nat.card 𝓀[v.adicCompletion F] = normV v := by
    rw [GroundTheory.Global.natCard_residueField_adicCompletion, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
    rfl
  have hfrob := (unramifiedDegree_eq_ofAdd_one_iff g).1 hg
  rw [hcard] at hfrob
  have hq : 1 < normV v := hcard ▸ one_lt_card_residueField (v.adicCompletion F)
  suffices h : ι (σ z) = ι (z ^ normV v) from (RingHom.injective ι.toRingHom) h
  rw [hι, map_pow]
  have hξ : (ι z) ^ normV v ^ m = ι z := by rw [← map_pow, hz]
  by_cases h0 : ι z = 0
  · rw [h0, map_zero, zero_pow (by omega)]
  · refine hfrob _ ⟨m, hm.ne', mul_right_cancel₀ h0 ?_⟩
    have e : normV v ^ m = (normV v ^ m - 1) + 1 :=
      (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm
    rw [hcard, ← pow_succ, ← e, hξ, one_mul]

end GlobalTheory.CompanionTheory.Dict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DecompositionGroupLocalGaloisStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_group_local_galois : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) [IsSepClosure (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F))], IsPlaceOver A v → ∀ (ι : Ω →ₐ[F] AlgebraicClosure (v.adicCompletion F)) (σ : G F Ω) (g : Gal(AlgebraicClosure (v.adicCompletion F)/v.adicCompletion F)), σ ∈ Dec (F := F) A → (∀ x, ι (σ x) = g (ι x)) → unramifiedDegree (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) g = Multiplicative.ofAdd 1 → IsFrob (F := F) A (normV v) σ := by
  first | exact @GlobalTheory.CompanionTheory.Dict.isFrob_of_unramifiedDegree_eq_one | exact GlobalTheory.CompanionTheory.Dict.isFrob_of_unramifiedDegree_eq_one | (intros; apply GlobalTheory.CompanionTheory.Dict.isFrob_of_unramifiedDegree_eq_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCharacterTameFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCharacterTameFormula
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.KummerCupInv

attribute [local instance 2000] Rep.hV2

theorem pow_identity {F : Type} [Field F] {n m p q r s : ℕ} {ζ y : F} (hy : y ≠ 0) (hζ : ζ ^ n = 1)
    (h : s + q = n * m + r) :
    (ζ ^ p * y) ^ q / y ^ r * y ^ s = ζ ^ ((p * q) % n) * (y ^ n) ^ m := by
  have e : y ^ s * y ^ q = (y ^ n) ^ m * y ^ r := by
    rw [← pow_add, ← pow_mul, ← pow_add, h]
  rw [mul_pow, ← pow_mul, ← pow_eq_pow_mod _ hζ]
  have hr : y ^ r ≠ 0 := pow_ne_zero _ hy
  field_simp
  linear_combination (ζ ^ (p * q)) * e

theorem kummer_key {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {n m p q r s k : ℕ} (ζ y u : Ωˣ)
    (g : Ω ≃ₐ[K] Ω) (hζ : ζ ^ n = 1) (hu : (u : Ω) = (y : Ω) ^ n)
    (hg : g (y : Ω) = (ζ : Ω) ^ p * y) (hk : k = (p * q) % n) (h : s + q = n * m + r) :
    (Additive.ofMul (ζ ^ k) + (m : ℤ) • Additive.ofMul u : Additive Ωˣ) =
      Additive.ofMul (galUnitsHom K Ω g (y ^ q)) - Additive.ofMul (y ^ r) +
        Additive.ofMul (y ^ s) := by
  apply Additive.toMul.injective
  simp only [natCast_zsmul, toMul_nsmul, toMul_add, toMul_sub, toMul_ofMul]
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_div_eq_div_val,
    coe_galUnitsHom_apply, map_pow, hg]
  rw [hu, pow_identity y.ne_zero (by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]) h, hk]

theorem unramifiedDegree_liftNormal_localArtinMap {K Ω : Type} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]
    {a : Kˣ} (ha : ord (a : K) = 1) :
    unramifiedDegree K Ω ((localArtinMap K Ω a).liftNormal Ω) = Multiplicative.ofAdd 1 := by
  rw [← restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff]
  ext y
  have h1 := AlgEquiv.restrictNormal_commutes ((localArtinMap K Ω a).liftNormal Ω)
    (maximalUnramifiedExtension K Ω) y
  have h2 := AlgEquiv.liftNormal_commutes (localArtinMap K Ω a) Ω
    ⟨(y : Ω), maximalUnramifiedExtension_le_maximalAbelianExtension y.2⟩
  have h3 := localArtinMap_uniformizer_apply (Ω := Ω) ha y.2
  simp only [IntermediateField.algebraMap_apply] at h1 h2
  rw [h1, h2]
  exact h3

theorem inv_kummerCup : ∀ (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] (n : ℕ) [NeZero n] (ζ y : Ωˣ) (a : Kˣ), ζ ^ n = 1 → ord (a : K) = 1 → (y : Ω) ^ n = algebraMap K Ω a → ∀ (κ χ : Gal(Ω/K) → ZMod n), (∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → Continuous χ → (∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1) → ∀ x : cocycles (galUnits.{0} K Ω) 2, (∀ s : Fin 2 → Gal(Ω/K), cochainOf _ (cocycleι _ 2 x) s = Additive.ofMul (ζ ^ (κ (s 0) * χ (s 1)).val)) → brauerInv K Ω (cohomologyπ _ 2 x) = - zmodToQZ n 1 := by
  intro K Ω _ _ _ _ _ _ _ _ _ _ _ n _ ζ y a hζ hord hy κ χ hκ hadd hcont hdeg x hx
  have hlc : IsLocallyConstant χ := (IsLocallyConstant.iff_continuous χ).2 hcont
  let ψ : Additive Gal(Ω/K) →ₜ+ QZ :=
    { toFun := fun σ => zmodToQZ n (χ (Additive.toMul σ))
      map_zero' := by
        have h1 : χ 1 = 0 := by simpa using hadd 1 1
        simp [h1]
      map_add' := fun σ τ => by simp [hadd]
      continuous_toFun :=
        ((hlc.comp_continuous continuous_toMul).comp (zmodToQZ n)).continuous }
  let z : cocycles (galUnitsZ K Ω) 2 := cocyclesULiftInt (galUnits.{0} K Ω) x
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf (galUnitsZ K Ω) ψ (unitsInvariant K Ω a)
  let f : Gal(Ω/K) → galUnitsZ K Ω := fun g => Additive.ofMul (y ^ (χ g).val)
  have hf : IsLocallyConstant f := hlc.comp fun c : ZMod n => (Additive.ofMul (y ^ c.val) : galUnitsZ K Ω)
  have hz : cohomologyπ (galUnitsZ K Ω) 2 (z + w) = 0 := by
    refine (cohomologyπ_two_eq_zero_iff _ _).2 ⟨f, hf, fun g h => ?_⟩
    have ez : cochainOf (galUnitsZ K Ω) (cocycleι _ 2 z) ![g, h] =
        Additive.ofMul (ζ ^ (κ g * χ h).val) :=
      (congrFun (cochainOf_cocycleι_cocyclesULiftInt (galUnits.{0} K Ω) x) ![g, h]).trans (hx _)
    set m : ℕ := ((χ g).val + (χ h).val) / n with hm
    have em : charCocycle (charAdd ψ) ((![g, h] : Fin 2 → Gal(Ω/K)) 0, (![g, h] : Fin 2 → Gal(Ω/K)) 1) =
        (m : ℤ) :=
      charCocycle_eq_bockInt χ (charAdd ψ) (fun _ => rfl) g h
    have hsum : (χ g).val + (χ h).val = n * m + (χ (g * h)).val := by
      rw [hadd, ZMod.val_add]
      exact (Nat.div_add_mod _ _).symm
    let u : Ωˣ := Units.map (algebraMap K Ω : K →* Ω) a
    have key := kummer_key ζ y u g hζ (show (u : Ω) = (y : Ω) ^ n from hy.symm) (hκ g)
      (show (κ g * χ h).val = ((κ g).val * (χ h).val) % n from ZMod.val_mul _ _) hsum
    rw [map_add (f := _), cochainOf_add, Pi.add_apply, ez, hwc, em]
    exact key
  have e1 : cohomologyULiftIntAddEquiv (galUnits.{0} K Ω) 2 (cohomologyπ _ 2 x) =
      cohomologyπ (galUnitsZ K Ω) 2 z :=
    cohomologyULiftIntAddEquiv_cohomologyπ' _ x
  have e2 : brauerInv K Ω (cohomologyπ _ 2 x) = brauerInvZ K Ω (cohomologyπ (galUnitsZ K Ω) 2 z) := by
    rw [← e1, brauerInvZ_cohomologyULiftIntAddEquiv]
  have e3 : cohomologyπ (galUnitsZ K Ω) 2 z + galCupClass K Ω ψ a = 0 := by
    rw [galCupClass, ← hw, ← map_add (f := _)]
    exact hz
  have e4 := brauerInvZ_galCupClass_liftNormal ψ a
  have e5 : ψ (Additive.ofMul ((localArtinMap K Ω a).liftNormal Ω)) = zmodToQZ n 1 := by
    change zmodToQZ n (χ ((localArtinMap K Ω a).liftNormal Ω)) = _
    rw [hdeg _ (unramifiedDegree_liftNormal_localArtinMap hord)]
  have e6 := congrArg (brauerInvZ K Ω) e3
  rw [map_add (f := _), map_zero, e4, e5] at e6
  rw [e2]
  exact eq_neg_of_add_eq_zero_left e6

end GlobalTheory.CompanionTheory.KummerCupInv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCharacterTameFormulaStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_character_tame_formula : ∀ (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] (n : ℕ) [NeZero n] (ζ y : Ωˣ) (a : Kˣ), ζ ^ n = 1 → ord (a : K) = 1 → (y : Ω) ^ n = algebraMap K Ω a → ∀ (κ χ : Gal(Ω/K) → ZMod n), (∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → Continuous χ → (∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1) → ∀ x : cocycles (galUnits.{0} K Ω) 2, (∀ s : Fin 2 → Gal(Ω/K), cochainOf _ (cocycleι _ 2 x) s = Additive.ofMul (ζ ^ (κ (s 0) * χ (s 1)).val)) → brauerInv K Ω (cohomologyπ _ 2 x) = - zmodToQZ n 1 := by
  first | exact @GlobalTheory.CompanionTheory.KummerCupInv.inv_kummerCup | exact GlobalTheory.CompanionTheory.KummerCupInv.inv_kummerCup | (intros; apply GlobalTheory.CompanionTheory.KummerCupInv.inv_kummerCup <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupUniformizer
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

namespace GlobalTheory.CompanionTheory.KummerCup

noncomputable def muEquiv {Ω : Type} [Field Ω] {n : ℕ} [NeZero n] (ζ : Ωˣ) (hζ : IsPrimitiveRoot ζ n) :
    ZMod n ≃+ Additive (rootsOfUnity n Ω) :=
  let ζ' : rootsOfUnity n Ω := ⟨ζ, (mem_rootsOfUnity _ _).2 hζ.pow_eq_one⟩
  have h1 : ζ' ^ n = 1 := Subtype.ext hζ.pow_eq_one
  let f : ZMod n →+ Additive (rootsOfUnity n Ω) :=
    { toFun := fun m => Additive.ofMul (ζ' ^ m.val)
      map_zero' := by simp
      map_add' := fun a b => by
        rw [ZMod.val_add, ← pow_eq_pow_mod _ h1, pow_add, ofMul_mul] }
  AddEquiv.ofBijective f (by
    have hinj : Function.Injective f := by
      intro a b hab
      have h2 : ζ ^ a.val = ζ ^ b.val := by
        have := congrArg (fun w => ((Additive.toMul w : rootsOfUnity n Ω) : Ωˣ)) hab
        simpa [f, ζ'] using this
      have h3 := hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h2
      exact ZMod.val_injective n h3
    refine ⟨hinj, fun w => ?_⟩
    have hζ' : IsPrimitiveRoot (ζ : Ω) n := IsPrimitiveRoot.coe_units_iff.2 hζ
    have hw : (((Additive.toMul w : rootsOfUnity n Ω) : Ωˣ) : Ω) ^ n = 1 := by
      have := (mem_rootsOfUnity _ _).1 (Additive.toMul w).2
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    obtain ⟨i, hi, hie⟩ := hζ'.eq_pow_of_pow_eq_one hw
    refine ⟨(i : ZMod n), ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    change (((ζ' ^ ((i : ZMod n)).val : rootsOfUnity n Ω) : Ωˣ) : Ω) = _
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi, ← hie]
    simp [ζ'])

theorem muEquiv_apply {Ω : Type} [Field Ω] {n : ℕ} [NeZero n] (ζ : Ωˣ) (hζ : IsPrimitiveRoot ζ n) (m : ZMod n) :
    (((Additive.toMul (muEquiv ζ hζ m) : rootsOfUnity n Ω) : Ωˣ)) = ζ ^ m.val := by
  simp [muEquiv]

attribute [local instance 2000] Rep.hV2

theorem cochainOf_cyclesMap {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B : Rep.{0} k G} [IsDiscreteRep A] [IsDiscreteRep B] (φ : A ⟶ B) (x : cocycles A 2) (s : Fin 2 → G) :
    cochainOf B (cocycleι B 2 ((HomologicalComplex.cyclesMap (cochainsMap φ) 2).hom x)) s =
      φ.hom (cochainOf A (cocycleι A 2 x) s) := by
  have e := congrArg (fun ψ => cochainOf B (ψ.hom x)) (HomologicalComplex.cyclesMap_i (cochainsMap φ) 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
  change cochainOf B (((cochainsComplex B).iCycles 2).hom _) s = _
  rw [e, cochainOf_cochainsMap_f]
  rfl

theorem inv_class (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [ValuativeRel Ω] [TopologicalSpace Ω]
    [IsValuativeTopology Ω] [ValuativeExtension K Ω] (n : ℕ) [NeZero n]
    (ζ y : Ωˣ) (a : Kˣ) (hζ : IsPrimitiveRoot ζ n)
    (ha : ord (a : K) = 1) (hy : (y : Ω) ^ n = algebraMap K Ω a)
    (κ χ : Gal(Ω/K) → ZMod n)
    (hκ : ∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ g).val * y)
    (hadd : ∀ g h, χ (g * h) = χ g + χ h) (hcont : Continuous χ)
    (hF : ∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1)
    (x : cocycles (galRootsOfUnity.{0} K Ω n) 2)
    (hx : ∀ s : Fin 2 → Gal(Ω/K), cochainOf _ (cocycleι _ 2 x) s = muEquiv ζ hζ (κ (s 0) * χ (s 1))) :
    brauerInv K Ω ((cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom (cohomologyπ _ 2 x)) = - zmodToQZ n 1 := by
  have hJx := ConcreteCategory.congr_hom (cohomologyπ_comp_cohomologyMap (rootsOfUnityToUnits K Ω n) 2) x
  have hJx' : (cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom (cohomologyπ _ 2 x) =
      cohomologyπ _ 2 ((HomologicalComplex.cyclesMap (cochainsMap (rootsOfUnityToUnits K Ω n)) 2).hom x) := hJx
  rw [hJx']
  refine GlobalTheory.T.kummer_character_tame_formula K Ω n ζ y a hζ.pow_eq_one ha hy κ χ hκ hadd hcont hF _ fun s => ?_
  rw [cochainOf_cyclesMap, hx, rootsOfUnityToUnits_hom_apply, muEquiv_apply]

theorem generates_of_inv {n : ℕ} [NeZero n] {H : Type} [AddCommGroup H] [Module (ZMod n) H] (T : H →+ QZ)
    (hT : Function.Injective T) (w : H) (h : T w = - zmodToQZ n 1) :
    Submodule.span (ZMod n) {w} = ⊤ := by
  have hTn : ∀ x, n • T x = 0 := by
    intro x
    rw [← map_nsmul]
    have : n • x = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
    rw [this, map_zero]
  rw [Submodule.eq_top_iff']
  intro x
  obtain ⟨b, hb⟩ := exists_zmodToQZ_eq (hTn x)
  have hx : x = (-b) • w := by
    apply hT
    rw [← hb]
    have : (-b) • w = ((-b).val) • w := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_zmod_val]
    rw [this, map_nsmul, h, ← map_neg, ← map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    simp
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem mu_equivariant (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (n : ℕ) [NeZero n]
    (c : Gal(Ω/K) →* (ZMod n)ˣ) (ζ : Ωˣ) (hζ : IsPrimitiveRoot ζ n)
    (hc : ∀ g : Gal(Ω/K), g (ζ : Ω) = (ζ : Ω) ^ ((c g : (ZMod n)ˣ) : ZMod n).val)
    (g : Gal(Ω/K)) (m : ZMod n) : muEquiv ζ hζ (charRep c g m) =
      (galRootsOfUnity.{0} K Ω n).ρ g (muEquiv ζ hζ m) := by
  rw [galRootsOfUnity_ρ_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change (((Additive.toMul (muEquiv ζ hζ (charRep c g m)) : rootsOfUnity n Ω) : Ωˣ) : Ω) =
    g (((Additive.toMul (muEquiv ζ hζ m) : rootsOfUnity n Ω) : Ωˣ) : Ω)
  rw [muEquiv_apply, muEquiv_apply, ReciprocityTheory.Gal.charRep_apply, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    map_pow, hc, ← pow_mul, ZMod.val_mul]
  have h1 : (ζ : Ω) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  rw [← pow_eq_pow_mod _ h1]

theorem core (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [ValuativeRel Ω] [TopologicalSpace Ω]
    [IsValuativeTopology Ω] [ValuativeExtension K Ω] (n : ℕ) [NeZero n] (hn : (n : K) ≠ 0)
    (c : Gal(Ω/K) →* (ZMod n)ˣ) (ζ y : Ωˣ) (a : Kˣ) (hζ : IsPrimitiveRoot ζ n)
    (hc : ∀ g : Gal(Ω/K), g (ζ : Ω) = (ζ : Ω) ^ ((c g : (ZMod n)ˣ) : ZMod n).val)
    (ha : ord (a : K) = 1) (hy : (y : Ω) ^ n = algebraMap K Ω a)
    (κ χ : Gal(Ω/K) → ZMod n)
    (hκ : ∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ g).val * y)
    (hadd : ∀ g h, χ (g * h) = χ g + χ h)
    (hF : ∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1)
    (z : Z2 (charRep c)) (hz : ∀ g h, z.1 (g, h) = κ g * χ h) :
    Submodule.span (ZMod n) {(Submodule.Quotient.mk z : H2 (charRep c))} = ⊤ := by
  have hcont := GlobalTheory.T.unramified_character_continuous K Ω n χ hadd hF
  have he := mu_equivariant K Ω n c ζ hζ hc
  obtain ⟨e2, hex, he2⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 Gal(Ω/K) (ZMod n) (ZMod n) (charRep c)
    (galRootsOfUnity.{0} K Ω n) (muEquiv ζ hζ) he
  have hJ : Function.Injective (cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom :=
    cohomologyMap_f_injective_of_subsingleton (kummerSequence_shortExact (K := K) (L := Ω) n hn) 1
      subsingleton_cohomology_one_galUnits
  let T : H2 (charRep c) →+ QZ := ((brauerInv K Ω).comp
    (cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom.toAddMonoidHom).comp e2.toAddMonoidHom
  have hTinj : Function.Injective T :=
    (brauerInv_bijective K Ω).1.comp (hJ.comp e2.injective)
  have hT1 : T (Submodule.Quotient.mk z) = - zmodToQZ n 1 := by
    obtain ⟨x, hx⟩ := hex z
    change brauerInv K Ω ((cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom (e2 (Submodule.Quotient.mk z))) = _
    rw [he2 z x hx]
    exact inv_class K Ω n ζ y a hζ ha hy κ χ hκ hadd hcont hF x fun s => by rw [hx, hz]
  exact generates_of_inv T hTinj _ hT1

theorem core_dec (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (n : ℕ) [NeZero n] (hn : (n : K) ≠ 0)
    (D : Type) [Group D] [TopologicalSpace D] (ε : Gal(Ω/K) ≃ₜ* D)
    (c : D →* (ZMod n)ˣ) (ζ y : Ωˣ) (a : Kˣ) (hζ : IsPrimitiveRoot ζ n)
    (hc : ∀ g : Gal(Ω/K), g (ζ : Ω) = (ζ : Ω) ^ ((c (ε g) : (ZMod n)ˣ) : ZMod n).val)
    (ha : ord (a : K) = 1) (hy : (y : Ω) ^ n = algebraMap K Ω a)
    (κ χ : D → ZMod n)
    (hκ : ∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ (ε g)).val * y)
    (hadd : ∀ g h, χ (g * h) = χ g + χ h)
    (hF : ∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ (ε g) = 1)
    (z : Z2 (charRep c)) (hz : ∀ g h, z.1 (g, h) = κ g * χ h) :
    Submodule.span (ZMod n) {(Submodule.Quotient.mk z : H2 (charRep c))} = ⊤ := by
  letI := algebraicValuativeRel K Ω
  letI := algebraicTopology K Ω
  haveI := algebraicValuativeRel_valuativeExtension K Ω
  haveI := algebraicTopology_isValuativeTopology K Ω
  let c' : Gal(Ω/K) →* (ZMod n)ˣ := c.comp (ε : Gal(Ω/K) →* D)
  let T := ReciprocityTheory.Neutral.Bridge.equivH2OfIso ε (charRep c) (charRep c') (fun _ _ => rfl)
  let z' : Z2 (charRep c') := ReciprocityTheory.Gal.compatiblePairCocycles2 (charRep c) (charRep c')
    (ε : Gal(Ω/K) →* D) (ReciprocityTheory.Neutral.Bridge.continuous_coe_iso ε) LinearMap.id continuous_id (fun _ _ => rfl) z
  have hspan := core K Ω n hn c' ζ y a hζ hc ha hy (fun g => κ (ε g)) (fun g => χ (ε g)) hκ
    (fun g h => by rw [map_mul, hadd]) hF z' (fun g h => hz _ _)
  rw [Submodule.eq_top_iff']
  intro x
  have hx : T x ∈ Submodule.span (ZMod n) {(Submodule.Quotient.mk z' : H2 (charRep c'))} := by
    rw [hspan]; trivial
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hx
  have : x = b • (Submodule.Quotient.mk z : H2 (charRep c)) := by
    apply T.injective
    rw [← hb, map_smul, show T (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' from
      ReciprocityTheory.Neutral.Bridge.equivH2OfIso_mk ε _ _ _ z]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem cyc_apply (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] [CharZero Ω] (l : ℕ)
    [Fact l.Prime] (r : ℕ) (ζ : Ω) (hζ : ζ ^ (l ^ r) = 1) (σ : G F Ω) :
    σ ζ = ζ ^ ((cycMod F Ω l r σ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
  haveI : ∀ i, NeZero (l ^ i) := fun i => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  exact cyclotomicCharacter.spec (L := Ω) l (σ : Ω ≃+* Ω) ζ hζ

theorem span_class_eq_top : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) → (∀ g h, z.1 (g, h) = κ g * χ h) → Submodule.span (ZMod (l ^ r)) {(Submodule.Quotient.mk z : H2 (muLoc F l r A))} = ⊤ := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8
  have hl0 : l ^ r ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ r) := ⟨hl0⟩
  obtain ⟨ι, e, hec, hes, hl⟩ := GlobalTheory.CompanionTheory.DecGal.exists_algHom_mulEquiv_dec F Ω A v hA
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  haveI : IsSepClosure (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) :=
    ⟨inferInstance, inferInstance⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hϖ0 : (ϖ : F) ≠ 0 := by
    intro h
    have : ϖ = 0 := by exact_mod_cast h
    exact h2 (this ▸ Ideal.zero_mem _)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hl0] at h3
    exact hϖ0 ((map_eq_zero_iff _ (algebraMap F Ω).injective).1 h3.symm)
  have hιζ : IsPrimitiveRoot (ι ζ) (l ^ r) := hζ.map_of_injective ι.injective
  have hιy : ι y ≠ 0 := (map_ne_zero_iff _ ι.injective).2 hy0
  have ha0 : algebraMap F (v.adicCompletion F) (ϖ : F) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap F (v.adicCompletion F)).injective).2 hϖ0
  refine core_dec (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) (l ^ r)
    (Nat.cast_ne_zero.2 hl0) (Dec (F := F) A) { e with continuous_toFun := hec, continuous_invFun := hes }
    ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) (Units.mk0 (ι ζ) (hιζ.ne_zero hl0)) (Units.mk0 (ι y) hιy)
    (Units.mk0 _ ha0) (IsPrimitiveRoot.coe_units_iff.1 hιζ) ?_ (GlobalTheory.T.uniformizer_order_eq_one F v ϖ h1 h2) ?_ κ χ ?_ h5 ?_ z h8
  · intro g
    change g (ι ζ) = (ι ζ) ^ _
    rw [← hl, cyc_apply F Ω l r ζ hζ.pow_eq_one, map_pow]
    rfl
  · change (ι y) ^ (l ^ r) = _
    rw [← map_pow, h3, ι.commutes]
    exact IsScalarTower.algebraMap_apply F _ _ _
  · intro g
    change g (ι y) = (ι ζ) ^ _ * ι y
    rw [← hl]
    refine (congrArg ι (h4 (e g))).trans ?_
    rw [map_mul, map_pow]
    rfl
  · intro g hg
    exact h7 _ (GlobalTheory.T.decomposition_group_local_galois F Ω A v hA ι _ g (e g).2 (hl g) hg)

end GlobalTheory.CompanionTheory.KummerCup
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupUniformizerStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_invariant_cup_uniformizer : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) → (∀ g h, z.1 (g, h) = κ g * χ h) → Submodule.span (ZMod (l ^ r)) {(Submodule.Quotient.mk z : H2 (muLoc F l r A))} = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.KummerCup.span_class_eq_top | exact GlobalTheory.CompanionTheory.KummerCup.span_class_eq_top | (intros; apply GlobalTheory.CompanionTheory.KummerCup.span_class_eq_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedLocalInvariantExists
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.LocalInvariant

theorem exists_bijective_isNormalised :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
      [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) →
      ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      ∃ f : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r),
        Function.Bijective f ∧ IsNormalised ζ A v f := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ A v hA
  obtain ⟨e⟩ := GlobalTheory.T.local_brauer_roots_unity_equiv F Ω l r hr A v hA
  by_cases hN : IsNormalised ζ A v (e : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  · exact ⟨e, e.bijective, hN⟩
  · simp only [IsNormalised, not_forall] at hN
    obtain ⟨ϖ, y, κ, χ, z, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hN
    have hgen := GlobalTheory.T.local_invariant_cup_uniformizer F Ω l r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8
    set c : H2 (muLoc F l r A) := Submodule.Quotient.mk z with hc

    obtain ⟨a, ha⟩ : ∃ a : ZMod (l ^ r), a * e c = 1 := by
      have hmem : e.symm 1 ∈ Submodule.span (ZMod (l ^ r)) {c} := by
        rw [hgen]; trivial
      obtain ⟨a, hac⟩ := Submodule.mem_span_singleton.1 hmem
      refine ⟨a, ?_⟩
      have := congrArg e hac
      simpa using this
    have ha' : e c * a = 1 := by rw [mul_comm]; exact ha
    refine ⟨a • (e : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), ⟨?_, ?_⟩, ?_⟩
    · intro x x' hxx
      have hxx' : a * e x = a * e x' := by simpa using hxx
      apply e.injective
      calc e x = e c * (a * e x) := by rw [← mul_assoc, ha', one_mul]
        _ = e c * (a * e x') := by rw [hxx']
        _ = e x' := by rw [← mul_assoc, ha', one_mul]
    · intro t
      refine ⟨e.symm (e c * t), ?_⟩
      simp [← mul_assoc, ha]
    · intro ϖ' y' κ' χ' z' g1 g2 g3 g4 g5 g6 g7 g8
      have hz := GlobalTheory.T.local_invariant_cup_kummer F Ω l r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8
        ϖ' y' κ' χ' z' g1 g2 g3 g4 g5 g6 g7 g8
      rw [← hz]
      simpa using ha

end GlobalTheory.CompanionTheory.LocalInvariant
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedLocalInvariantExistsStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalised_local_invariant_exists : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∃ f : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r), Function.Bijective f ∧ IsNormalised ζ A v f := by
  first | exact @GlobalTheory.CompanionTheory.LocalInvariant.exists_bijective_isNormalised | exact GlobalTheory.CompanionTheory.LocalInvariant.exists_bijective_isNormalised | (intros; apply GlobalTheory.CompanionTheory.LocalInvariant.exists_bijective_isNormalised <;> assumption)
end
end

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.PoitouTateInv

theorem exists_invFam_normalised : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω,
    IsPrimitiveRoot ζ (l ^ r) → ∃ inv : InvFam F Ω l r,
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      Function.Bijective (inv A) ∧ IsNormalised ζ A v (inv A) := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ
  classical
  have key := GlobalTheory.T.normalised_local_invariant_exists F Ω l r hr ζ hζ
  refine ⟨fun A => if h : ∃ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v then
    Classical.choose (key A h.choose h.choose_spec) else 0, fun A v hv => ?_⟩
  have h : ∃ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v := ⟨v, hv⟩
  have e : h.choose = v := eq_of_isPlaceOver h.choose_spec hv
  have spec := Classical.choose_spec (key A h.choose h.choose_spec)
  simp only [dif_pos h]
  generalize Classical.choose (key A h.choose h.choose_spec) = f at spec ⊢
  rw [e] at spec
  exact spec

end GlobalTheory.CompanionTheory.PoitouTateInv

end
