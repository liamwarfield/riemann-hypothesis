module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalInvariants
public import ReciprocityTheory.GaloisValuations.ArithOfA
public import GroundTheory.ProfiniteCohomology.LocalTateDuality.KummerCup

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DecompositionGroupFrobeniusFactor
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DecompositionGroupFrobeniusFactor
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.TameDecomp

theorem exists_frob_pow_mul_pow_mul_inertia : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ φ : Dec (F := F) A, IsFrob (F := F) A (normV v) (φ : G F Ω) → ∀ N : ℕ, 0 < N → ∀ g : Dec (F := F) A, ∃ a < N, ∃ t i : Dec (F := F) A, (i : G F Ω) ∈ Ine (F := F) A ∧ g = φ ^ a * t ^ N * i := by
  intro F Ω _ _ _ _ _ A v hA φ hφ N hN g
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  set I : Subgroup (Dec (F := F) A) := (Ine (F := F) A).subgroupOf (Dec (F := F) A) with hI
  have hIc : IsClosed (I : Set (Dec (F := F) A)) := (isClosed_Ine A).preimage continuous_subtype_val
  let P : Set (Dec (F := F) A) :=
    (fun x : Dec (F := F) A × Dec (F := F) A => x.1 ^ N * x.2) '' (Set.univ ×ˢ (I : Set _))
  have hP : IsCompact P := (isCompact_univ.prod hIc.isCompact).image (by fun_prop)
  let Wd : Set (Dec (F := F) A) := ⋃ a ∈ Finset.range N, (fun x => φ ^ a * x) '' P
  have hW : IsClosed Wd := by
    refine (Finset.isCompact_biUnion _ fun a _ => hP.image (by fun_prop)).isClosed
  have hsub : ((Subgroup.zpowers φ ⊔ I : Subgroup (Dec (F := F) A)) : Set (Dec (F := F) A)) ⊆ Wd := by
    intro x hx
    rw [Subgroup.mul_normal] at hx
    obtain ⟨h, hh, i, hi, rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hN' : (0 : ℤ) < N := by exact_mod_cast hN
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg m hN'.ne')
    have haN : a < N := by
      have := Int.emod_lt_of_pos m hN'
      omega
    have e : φ ^ m = φ ^ a * (φ ^ (m / (N : ℤ))) ^ N := by
      rw [← zpow_natCast (φ ^ (m / (N : ℤ))) N, ← zpow_mul, ← zpow_natCast φ a, ← zpow_add]
      congr 1
      have := Int.emod_add_mul_ediv m N
      rw [ha] at this
      rw [mul_comm (m / (N : ℤ))]
      omega
    refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 haN)) ?_
    exact ⟨_, ⟨(φ ^ (m / (N : ℤ)), i), ⟨Set.mem_univ _, hi⟩, rfl⟩, by
      simp only [e, mul_assoc]⟩
  have hg : g ∈ Wd := by
    have h1 := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hA φ hφ
    have h2 : g ∈ (Subgroup.zpowers φ ⊔ I).topologicalClosure := by rw [hI, h1]; trivial
    exact closure_minimal hsub hW h2
  simp only [Wd, Set.mem_iUnion] at hg
  obtain ⟨a, ha, y, ⟨⟨t, i⟩, ⟨-, hi⟩, rfl⟩, e⟩ := hg
  exact ⟨a, Finset.mem_range.1 ha, t, i, Subgroup.mem_subgroupOf.1 hi, by
    rw [← e, mul_assoc]⟩

end GlobalTheory.CompanionTheory.TameDecomp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DecompositionGroupFrobeniusFactorStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_group_frobenius_factor : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ φ : Dec (F := F) A, IsFrob (F := F) A (normV v) (φ : G F Ω) → ∀ N : ℕ, 0 < N → ∀ g : Dec (F := F) A, ∃ a < N, ∃ t i : Dec (F := F) A, (i : G F Ω) ∈ Ine (F := F) A ∧ g = φ ^ a * t ^ N * i := by
  first | exact @GlobalTheory.CompanionTheory.TameDecomp.exists_frob_pow_mul_pow_mul_inertia | exact GlobalTheory.CompanionTheory.TameDecomp.exists_frob_pow_mul_pow_mul_inertia | (intros; apply GlobalTheory.CompanionTheory.TameDecomp.exists_frob_pow_mul_pow_mul_inertia <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusPowerFixesRootUnique
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusPowerFixesRootUnique
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.TameAction


open GlobalTheory.TameQuot GlobalTheory.WeilDeligne in
theorem eq_zero_of_fixes_primitiveRoot : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ φ : Dec (F := F) A, IsFrob (F := F) A (normV v) (φ : G F Ω) → ∀ N : ℕ, 0 < N → ∀ ξ : Ω, IsPrimitiveRoot ξ (normV v ^ N - 1) → ∀ (a : ℕ) (t i : Dec (F := F) A), a < N → (i : G F Ω) ∈ Ine (F := F) A → ((φ ^ a * t ^ N * i : Dec (F := F) A) : G F Ω) ξ = ξ → a = 0 := by
  intro F Ω _ _ _ _ _ A v hA φ hφ N hN ξ hξ' a t i haN hi hfix
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hq := ReciprocityTheory.Gal.one_lt_normV v
  obtain ⟨n, hn⟩ : ∃ n, normV v ^ N = n + 1 :=
    ⟨_, (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm⟩
  have hn0 : n ≠ 0 := by
    have := one_lt_pow₀ hq hN.ne'
    omega
  have : NeZero n := ⟨hn0⟩
  have : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn0⟩
  have hξ : IsPrimitiveRoot ξ n := by
    have e : normV v ^ N - 1 = n := by omega
    rwa [e] at hξ'
  have hnv : ¬ A.valuation (n : Ω) < 1 := by
    intro h
    have h1 : ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← nsmul_one]
      exact card_nsmul_eq_zero'
    have h2 : ((n : ℕ) : 𝓞 F) ∈ v.asIdeal := (hA _).1 (by simpa using h)
    have h3 := v.asIdeal.sub_mem (v.asIdeal.pow_mem_of_mem h1 N hN) h2
    rw [← Nat.cast_pow, hn] at h3
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h3))
  have hξ1 : A.valuation ξ ≤ 1 := (valuation_eq_one_of_pow_eq_one A hn0 hξ.pow_eq_one).le
  let θ : Dec (F := F) A →* (ZMod n)ˣ := (hξ.autToPow F).comp (Dec (F := F) A).subtype
  have hθ : ∀ (g : Dec (F := F) A) (k : ℕ), (θ g : ZMod n) = k ↔ g.1 ξ = ξ ^ k := fun g k => by
    have hu : IsPrimitiveRoot (hξ.isUnit hn0).unit n :=
      IsPrimitiveRoot.coe_units_iff.mp (by simpa using hξ)
    rw [← hξ.autToPow_spec F g.1]
    change (θ g : ZMod n) = k ↔ ξ ^ (θ g : ZMod n).val = _
    conv_lhs => rw [← ZMod.natCast_zmod_val (θ g : ZMod n)]
    rw [ZMod.natCast_eq_natCast_iff]
    generalize (θ g : ZMod n).val = m
    conv_lhs => rw [hu.eq_orderOf, ← pow_eq_pow_iff_modEq, Units.ext_iff]
    simp
  have hθ' : ∀ (g : Dec (F := F) A) (k : ℕ), A.valuation (g.1 ξ - ξ ^ k) < 1 → (θ g : ZMod n) = k :=
    fun g k h => (hθ g k).2 (eq_of_pow_eq_one A hnv (by rw [← map_pow, hξ.pow_eq_one, map_one])
      (by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]) h)
  have hI : ∀ σ : Dec (F := F) A, σ.1 ∈ Ine (F := F) A → θ σ = 1 := fun σ hσ =>
    Units.ext (by simpa using hθ' σ 1 (by simpa using hσ.2 ξ hξ1))
  have hF : (θ φ : ZMod n) = (normV v : ℕ) := hθ' φ _ (hφ.2 ξ hξ1)
  have ho : IsOpen (θ.ker : Set (Dec (F := F) A)) := by
    have e : (θ.ker : Set (Dec (F := F) A)) = Subtype.val ⁻¹' {σ : G F Ω | σ ξ = ξ} := by
      ext g
      have := hθ g 1
      rw [pow_one, Nat.cast_one] at this
      exact Units.ext_iff.trans this
    rw [e]
    exact (isOpen_setOf_apply (F := F) ξ (fun t => t = ξ)).preimage continuous_subtype_val
  have h3 : θ φ ^ N = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hF, ← Nat.cast_pow, hn]; simp)
  have hr : ∀ g, θ g ∈ Subgroup.zpowers (θ φ) := by
    have h4 : ⊤ ≤ (Subgroup.zpowers (θ φ)).comap θ := by
      rw [← closure_frob_sup_Ine F Ω A v hA φ hφ]
      refine Subgroup.topologicalClosure_minimal _ (sup_le (Subgroup.zpowers_le.2
        (Subgroup.mem_zpowers _)) fun σ hσ => ?_) (Subgroup.isClosed_of_isOpen _
          (Subgroup.isOpen_mono (fun σ hσ => ?_) ho))
      · rw [Subgroup.mem_comap, hI σ hσ]
        exact one_mem _
      · rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hσ]
        exact one_mem _
    exact fun g => h4 (Subgroup.mem_top g)
  have ht : θ t ^ N = 1 := by
    obtain ⟨b, hb⟩ := hr t
    rw [← hb, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3, one_zpow]
  have h5 : θ φ ^ a = 1 := by
    have h6 : θ (φ ^ a * t ^ N * i) = 1 :=
      Units.ext (by simpa using (hθ (φ ^ a * t ^ N * i) 1).2 (by simpa using hfix))
    rwa [map_mul, map_mul, map_pow, map_pow, ht, hI i hi, mul_one, mul_one] at h6
  have h1 : ((θ φ ^ a : (ZMod n)ˣ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
    rw [Nat.cast_one]; exact congrArg Units.val h5
  rw [Units.val_pow_eq_pow_val, hF, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff] at h1
  have h2 := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).1 h1.symm
  have h4 := pow_lt_pow_right₀ hq haN
  have h7 := Nat.eq_zero_of_dvd_of_lt h2 (by
    have := Nat.one_le_pow a (normV v) (by omega)
    omega)
  by_contra h
  have := one_lt_pow₀ hq h
  omega

end GlobalTheory.CompanionTheory.TameAction
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusPowerFixesRootUniqueStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_power_fixes_root_unique : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ φ : Dec (F := F) A, IsFrob (F := F) A (normV v) (φ : G F Ω) → ∀ N : ℕ, 0 < N → ∀ ξ : Ω, IsPrimitiveRoot ξ (normV v ^ N - 1) → ∀ (a : ℕ) (t i : Dec (F := F) A), a < N → (i : G F Ω) ∈ Ine (F := F) A → ((φ ^ a * t ^ N * i : Dec (F := F) A) : G F Ω) ξ = ξ → a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TameAction.eq_zero_of_fixes_primitiveRoot | exact GlobalTheory.CompanionTheory.TameAction.eq_zero_of_fixes_primitiveRoot | (intros; apply GlobalTheory.CompanionTheory.TameAction.eq_zero_of_fixes_primitiveRoot <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFromKummerUnramifiedUnit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFromKummerUnramifiedUnit
open ValuativeRel IntermediateField

namespace GlobalTheory.CompanionTheory.LocalField

open GroundTheory.LocalField

theorem exists_norm_fixedField_ker_eq_unit :
    ∀ {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
      [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (N : ℕ), N ≠ 0 → ∀ ξ : Ω,
      IsPrimitiveRoot ξ (Nat.card 𝓀[K] ^ N - 1) →
      ∀ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N), IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω)) →
      (∀ g : Ω ≃ₐ[K] Ω, g ξ = ξ → ψ g = 1) → ∀ U : Kˣ, GroundTheory.LocalField.ord (U : K) = 0 →
      ∃ y : IntermediateField.fixedField ψ.ker, Algebra.norm K y = (U : K) := by
  intro K Ω _ _ _ _ _ _ _ N hN ξ hξ ψ hopen hψ U hU
  have hgal : IsGalois K Ω := inferInstance
  obtain ⟨hL, -⟩ := isUnramifiedSubextension_adjoin hN hξ
  have := hL.1
  have := hL.isGalois
  have hclosed : IsClosed (ψ.ker : Set (Ω ≃ₐ[K] Ω)) := Subgroup.isClosed_of_isOpen _ hopen
  let C : ClosedSubgroup (Ω ≃ₐ[K] Ω) := ⟨ψ.ker, hclosed⟩
  set M : IntermediateField K Ω := fixedField ψ.ker with hM
  have hMU : M.fixingSubgroup = ψ.ker := InfiniteGalois.fixingSubgroup_fixedField C
  have hML : M ≤ K⟮ξ⟯ := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup K⟮ξ⟯]
    intro x hx
    rw [mem_fixedField_iff]
    intro g hg
    have hgξ : g ξ = ξ := (mem_fixingSubgroup_iff _ _).1 hg ξ (mem_adjoin_simple_self K ξ)
    exact (mem_fixedField_iff _ _).1 hx g (hψ g hgξ)
  have : FiniteDimensional K M := FiniteDimensional.of_injective (IntermediateField.inclusion hML).toLinearMap
    (IntermediateField.inclusion hML).toRingHom.injective
  have : IsGalois K M := IsGalois.of_fixedField_normal_subgroup ψ.ker
  have : IsMulCommutative (M ≃ₐ[K] M) := ⟨⟨fun τ₁ τ₂ => by
    obtain ⟨g₁, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) τ₁
    obtain ⟨g₂, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) τ₂
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker,
      IntermediateField.restrictNormalHom_ker, hMU, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, mul_inv_rev]
    rw [mul_comm (ψ g₁) (ψ g₂)]
    group⟩⟩
  have : IsAbelianGalois K M := ⟨⟩
  have hle := hL.le_maximalUnramifiedExtension
  have h1 := restrictAb_localArtinMap_of_le_maximalUnramifiedExtension K⟮ξ⟯ hle U
  rw [hU, zpow_zero] at h1
  have h2 : restrictAb M (le_maximalAbelianExtension M) (localArtinMap K Ω U) = 1 := by
    ext x
    have e1 := restrictAb_apply M (le_maximalAbelianExtension M) (localArtinMap K Ω U) x
    have e2 := restrictAb_apply K⟮ξ⟯
      (hle.trans maximalUnramifiedExtension_le_maximalAbelianExtension) (localArtinMap K Ω U)
      ⟨x, hML x.2⟩
    rw [h1] at e2
    exact e1.trans e2.symm
  have h3 : U ∈ (normUnits K M).range := by
    rw [← ker_restrictAb_localArtinMap M, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact h2
  obtain ⟨y, hy⟩ := h3
  exact ⟨y, by simpa using congrArg Units.val hy⟩

end GlobalTheory.CompanionTheory.LocalField
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFromKummerUnramifiedUnitStatement
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_from_kummer_unramified_unit : ∀ {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (N : ℕ), N ≠ 0 → ∀ ξ : Ω, IsPrimitiveRoot ξ (Nat.card 𝓀[K] ^ N - 1) → ∀ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N), IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω)) → (∀ g : Ω ≃ₐ[K] Ω, g ξ = ξ → ψ g = 1) → ∀ U : Kˣ, GroundTheory.LocalField.ord (U : K) = 0 → ∃ y : IntermediateField.fixedField ψ.ker, Algebra.norm K y = (U : K) := by
  first | exact @GlobalTheory.CompanionTheory.LocalField.exists_norm_fixedField_ker_eq_unit | exact GlobalTheory.CompanionTheory.LocalField.exists_norm_fixedField_ker_eq_unit | (intros; apply GlobalTheory.CompanionTheory.LocalField.exists_norm_fixedField_ker_eq_unit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueFieldCardEqNorm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueFieldCardEqNorm
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel

namespace GlobalTheory.CompanionTheory.LocRes

theorem natCard_residueField_eq_normV : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)), Nat.card 𝓀[v.adicCompletion F] = normV v := by
  intro F _ _ v
  rw [GroundTheory.Global.natCard_residueField_adicCompletion v, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]
  rfl

end GlobalTheory.CompanionTheory.LocRes
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueFieldCardEqNormStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_field_card_eq_norm : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), Nat.card 𝓀[v.adicCompletion F] = normV v := by
  first | exact @GlobalTheory.CompanionTheory.LocRes.natCard_residueField_eq_normV | exact GlobalTheory.CompanionTheory.LocRes.natCard_residueField_eq_normV | (intros; apply GlobalTheory.CompanionTheory.LocRes.natCard_residueField_eq_normV <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerRatioValuationZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerRatioValuationZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel

namespace GlobalTheory.CompanionTheory.Uniformiser

theorem valued_eq_exp_neg_one {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) (h1 : a ∈ v.asIdeal) (h2 : a ∉ v.asIdeal ^ 2) :
    Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = WithZero.exp (-1 : ℤ) := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact h2 (Submodule.zero_mem _)
  rw [show algebraMap F (v.adicCompletion F) (a : F) = ((a : F) : v.adicCompletion F) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  have hle1 : v.intValuation a ≤ WithZero.exp (-(1 : ℕ) : ℤ) :=
    (HeightOneSpectrum.intValuation_le_pow_iff_mem v a 1).2 (by simpa using h1)
  have hnle2 : ¬ v.intValuation a ≤ WithZero.exp (-(2 : ℕ) : ℤ) := fun h =>
    h2 ((HeightOneSpectrum.intValuation_le_pow_iff_mem v a 2).1 h)
  have hne : v.intValuation a ≠ 0 := HeightOneSpectrum.intValuation_ne_zero v a ha0
  rw [← WithZero.exp_log hne] at hle1 hnle2 ⊢
  rw [WithZero.exp_le_exp] at hle1 hnle2
  congr 1
  omega

theorem ord_eq_zero_of_valued_eq_one {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {x : v.adicCompletion F} (hx : Valued.v x = 1) :
    GroundTheory.LocalField.ord x = 0 := by
  have heq : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsEquiv
      (ValuativeRel.valuation (v.adicCompletion F)) := ValuativeRel.isEquiv _ _
  have h1 : ValuativeRel.valuation (v.adicCompletion F) x = 1 := heq.eq_one_iff_eq_one.1 hx
  unfold GroundTheory.LocalField.ord
  rw [GroundTheory.LocalField.normalizedValuation_apply, h1, map_one, WithZero.log_one, neg_zero]

theorem ord_ratio_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ ϖ' : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ϖ' ∈ v.asIdeal → ϖ' ∉ v.asIdeal ^ 2 →
    ∀ U : (v.adicCompletion F)ˣ, (U : v.adicCompletion F) *
      algebraMap F (v.adicCompletion F) (ϖ : F) = algebraMap F (v.adicCompletion F) (ϖ' : F) →
    GroundTheory.LocalField.ord (U : v.adicCompletion F) = 0 := by
  intro F _ _ v ϖ ϖ' h1 h2 h1' h2' U hU
  apply ord_eq_zero_of_valued_eq_one v
  have e1 := valued_eq_exp_neg_one v ϖ h1 h2
  have e2 := valued_eq_exp_neg_one v ϖ' h1' h2'
  have h := congrArg Valued.v hU
  rw [map_mul, e1, e2] at h
  exact mul_right_cancel₀ WithZero.exp_ne_zero (h.trans (one_mul _).symm)

end GlobalTheory.CompanionTheory.Uniformiser
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerRatioValuationZeroStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_ratio_valuation_zero : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ ϖ' : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ϖ' ∈ v.asIdeal → ϖ' ∉ v.asIdeal ^ 2 → ∀ U : (v.adicCompletion F)ˣ, (U : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (ϖ : F) = algebraMap F (v.adicCompletion F) (ϖ' : F) → GroundTheory.LocalField.ord (U : v.adicCompletion F) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero | exact GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCocycleNormCriterion
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCocycleNormCriterion
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.KummerCup

open CategoryTheory GroundTheory.ProfCoh IntermediateField

attribute [local instance 2000] Rep.hV2

theorem isLocallyConstant_of_right_invariant {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G)) (φ : G → X)
    (h : ∀ g, ∀ v ∈ H, φ (g * v) = φ g) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (H : Set G)) := hH.preimage (continuous_const_mul x⁻¹)
  have hm : x ∈ (fun y => x⁻¹ * y) ⁻¹' (H : Set G) := by simp [H.one_mem]
  filter_upwards [ho.mem_nhds hm] with y hy
  have := h x _ hy
  simpa using this

section Coh

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [IsDiscreteRep A]

theorem exists_cocycle_of_cochain (n : ℕ) (c : (Fin n → G) → A) (hc : IsLocallyConstant c)
    (hd : (inhomogeneousCochains.d A n).hom c = 0) :
    ∃ x : cocycles A n, cochainOf A (cocycleι A n x) = c := by
  refine ⟨(cochainsComplex A).cyclesMk (mkCochain A c hc) (n + 1) (by simp) ?_, ?_⟩
  · apply cochainOf_injective (A := A)
    exact (cochainOf_d (A := A) _).trans hd
  · exact congrArg (cochainOf A) ((cochainsComplex A).i_cyclesMk _ _ _ _)

theorem cohomologyπ_succ_eq_zero_iff (n : ℕ) (x : cocycles A (n + 1)) :
    cohomologyπ A (n + 1) x = 0 ↔ ∃ w : (Fin n → G) → A, IsLocallyConstant w ∧
      (inhomogeneousCochains.d A n).hom w = cochainOf A (cocycleι A (n + 1) x) := by
  change ((cochainsComplex A).homologyπ (n + 1)).hom x = 0 ↔ _
  rw [homologyπ_eq_zero_iff, CochainComplex.prev_nat_succ]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨cochainOf A w, isLocallyConstant_cochainOf w, ?_⟩
    rw [← cochainOf_d]
    exact congrArg (cochainOf A) hw
  · rintro ⟨w, hw, h⟩
    refine ⟨mkCochain A w hw, ?_⟩
    apply cochainOf_injective (A := A)
    exact (cochainOf_d (A := A) _).trans h

end Coh

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem exists_eq_div_of_cocycle [IsGalois K Ω] (f : (Ω ≃ₐ[K] Ω) → Ωˣ) (hf : IsLocallyConstant f)
    (hc : ∀ g h, f (g * h) = galUnitsHom K Ω g (f h) * f g) :
    ∃ t : Ωˣ, ∀ g, f g = galUnitsHom K Ω g t / t := by
  let A := galUnits.{0} K Ω
  let c : (Fin 1 → (Ω ≃ₐ[K] Ω)) → A := fun v => Additive.ofMul (f (v 0))
  have hcl : IsLocallyConstant c :=
    (hf.comp_continuous (continuous_apply 0)).comp (fun u => (Additive.ofMul u : A))
  have hd : (inhomogeneousCochains.d A 1).hom c = 0 := by
    funext v
    rw [inhomogeneousCochains_d_one_apply]
    have e := hc (v 0) (v 1)
    show Additive.ofMul (galUnitsHom K Ω (v 0) (f (v 1))) - Additive.ofMul (f (v 0 * v 1)) +
      Additive.ofMul (f (v 0)) = (0 : Additive Ωˣ)
    rw [e]
    apply Additive.toMul.injective
    simp [toMul_add, toMul_sub]
  obtain ⟨x, hx⟩ := exists_cocycle_of_cochain A 1 c hcl hd
  have h0 : cohomologyπ A 1 x = 0 :=
    (subsingleton_cohomology_one_galUnits (K := K) (L := Ω)).elim _ _
  obtain ⟨w, hw, hwx⟩ := (cohomologyπ_succ_eq_zero_iff A 0 x).1 h0
  refine ⟨Additive.toMul (w Fin.elim0 : Additive Ωˣ), fun g => ?_⟩
  have e := congrFun (hwx.trans hx) (fun _ => g)
  simp only [inhomogeneousCochains.d_hom_apply] at e
  simp at e
  have hw0 : ∀ v : Fin 0 → (Ω ≃ₐ[K] Ω), w v = w Fin.elim0 := fun v => by
    rw [Subsingleton.elim v Fin.elim0]
  simp only [hw0 (fun _ => g), hw0 (Fin.contractNth 0 _ _)] at e
  have e' : (Additive.ofMul (galUnitsHom K Ω g (Additive.toMul (w Fin.elim0 : Additive Ωˣ))) +
      -(w Fin.elim0 : Additive Ωˣ) : Additive Ωˣ) = Additive.ofMul (f g) := e
  have e2 := congrArg (Additive.toMul (α := Ωˣ)) e'
  simp only [toMul_add, toMul_neg, toMul_ofMul] at e2
  rw [← e2, div_eq_mul_inv]
  rfl

theorem natCast_eq_of_pow_eq {N : ℕ} [NeZero N] {ζ : Ω} (hζ : IsPrimitiveRoot ζ N) {a b : ℕ}
    (h : ζ ^ a = ζ ^ b) : (a : ZMod N) = b := by
  have hz : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
  let z : Ωˣ := Units.mk0 ζ hz
  have hz' : IsPrimitiveRoot z N := (IsPrimitiveRoot.coe_units_iff).1 hζ
  have e : z ^ a = z ^ b := Units.ext (by simpa [z] using h)
  rw [ZMod.natCast_eq_natCast_iff, hz'.eq_orderOf]
  exact pow_eq_pow_iff_modEq.1 e

theorem exists_cochain_of_lift [IsGalois K Ω] [IsSepClosed Ω] (N : ℕ) [NeZero N] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ N) (c0 : (Ω ≃ₐ[K] Ω) → ZMod N) (hc0 : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ ^ (c0 g).val)
    (ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N)) (hψ : IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω)))
    (T : Ωˣ) (κ : (Ω ≃ₐ[K] Ω) → ZMod N) (hκ : ∀ g : Ω ≃ₐ[K] Ω, g (T : Ω) = ζ ^ (κ g).val * T)
    (b : (Ω ≃ₐ[K] Ω) → Ωˣ) (hb : IsLocallyConstant b) (w : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω) → ℕ)
    (hw : ∀ g h, (Multiplicative.toAdd (ψ g)).val + (Multiplicative.toAdd (ψ h)).val =
      N * w g h + (Multiplicative.toAdd (ψ (g * h))).val)
    (hbc : ∀ g h : Ω ≃ₐ[K] Ω, g (b h : Ω) * (b g : Ω) = ((T : Ω) ^ N) ^ w g h * (b (g * h) : Ω)) :
    ∃ c : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant c ∧ ∀ g h : Ω ≃ₐ[K] Ω,
      c0 g * c h - c (g * h) + c g = κ g * Multiplicative.toAdd (ψ h) := by
  have hN0 : N ≠ 0 := NeZero.ne N
  set p : (Ω ≃ₐ[K] Ω) → ℕ := fun g => (Multiplicative.toAdd (ψ g)).val with hp
  have hplc : IsLocallyConstant p :=
    isLocallyConstant_of_right_invariant ψ.ker hψ p fun g v hv => by
      simp [p, map_mul, MonoidHom.mem_ker.1 hv]
  let γu : (Ω ≃ₐ[K] Ω) → Ωˣ := fun h => T ^ p h * (b h)⁻¹
  have hγlc : IsLocallyConstant γu := (hplc.prodMk hb).comp fun q : ℕ × Ωˣ => T ^ q.1 * q.2⁻¹
  have hγv : ∀ h, (γu h : Ω) = (T : Ω) ^ p h / (b h : Ω) := fun h => by
    simp [γu, div_eq_mul_inv]
  have hγ : ∀ g h : Ω ≃ₐ[K] Ω,
      g (γu h : Ω) * (γu g : Ω) = ζ ^ ((κ g).val * p h) * (γu (g * h) : Ω) := by
    intro g h
    have hbg : g (b h : Ω) ≠ 0 := by simp
    have hbb : (b g : Ω) ≠ 0 := by simp
    have hbgh : (b (g * h) : Ω) ≠ 0 := by simp
    have hT0 : (T : Ω) ≠ 0 := by simp
    rw [hγv, hγv, hγv, map_div₀, map_pow, hκ]
    calc (ζ ^ (κ g).val * (T : Ω)) ^ p h / g (b h : Ω) * ((T : Ω) ^ p g / (b g : Ω))
        = ζ ^ ((κ g).val * p h) * (T : Ω) ^ (p g + p h) / (g (b h : Ω) * (b g : Ω)) := by
          rw [mul_pow, pow_add, ← pow_mul]
          field_simp
      _ = ζ ^ ((κ g).val * p h) * ((T : Ω) ^ (N * w g h) * (T : Ω) ^ p (g * h)) /
            (((T : Ω) ^ N) ^ w g h * (b (g * h) : Ω)) := by
          rw [hbc, show p g + p h = N * w g h + p (g * h) from hw g h, pow_add]
      _ = ζ ^ ((κ g).val * p h) * ((T : Ω) ^ p (g * h) / (b (g * h) : Ω)) := by
          rw [pow_mul (T : Ω) N]
          field_simp
  let f : (Ω ≃ₐ[K] Ω) → Ωˣ := fun g => γu g ^ N
  have hflc : IsLocallyConstant f := hγlc.comp fun x : Ωˣ => x ^ N
  have hζN : ζ ^ N = 1 := hζ.pow_eq_one
  have hfc : ∀ g h, f (g * h) = galUnitsHom K Ω g (f h) * f g := by
    intro g h
    apply Units.ext
    simp only [f, Units.val_mul, Units.val_pow_eq_pow_val, coe_galUnitsHom_apply, map_pow]
    rw [← mul_pow, hγ, mul_pow, ← pow_mul, mul_comm _ N, pow_mul, hζN, one_pow, one_mul]
  obtain ⟨t, ht⟩ := exists_eq_div_of_cocycle f hflc hfc
  have : NeZero ((N : ℕ) : Ω) := hζ.neZero'
  obtain ⟨s, hs⟩ := IsSepClosed.exists_pow_nat_eq (t : Ω) N
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0] at hs
    exact t.ne_zero hs.symm
  let su : Ωˣ := Units.mk0 s hs0
  have hsuN : su ^ N = t := Units.ext (by simpa [su] using hs)
  have hslc : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => galUnitsHom K Ω g su := by
    refine isLocallyConstant_of_right_invariant (MulAction.stabilizer (Ω ≃ₐ[K] Ω) s)
      (isOpen_of_forall_apply_eq_mem _ s fun σ h => h) _ fun g v hv => ?_
    have hv' : v s = s := hv
    apply Units.ext
    simp only [coe_galUnitsHom_apply, su, Units.val_mk0, AlgEquiv.mul_apply, hv']
  let d : (Ω ≃ₐ[K] Ω) → Ωˣ := fun g => γu g * su / galUnitsHom K Ω g su
  have hdlc : IsLocallyConstant d :=
    (hγlc.prodMk hslc).comp fun q : Ωˣ × Ωˣ => q.1 * su / q.2
  have hdN : ∀ g, d g ^ N = 1 := by
    intro g
    have h1 : γu g ^ N = galUnitsHom K Ω g t / t := ht g
    simp only [d, div_pow, mul_pow, h1, hsuN, ← map_pow]
    simp
  have hex : ∀ g, ∃ i : ℕ, i < N ∧ ζ ^ i = (d g : Ω) := fun g =>
    hζ.eq_pow_of_pow_eq_one (by rw [← Units.val_pow_eq_pow_val, hdN, Units.val_one])
  classical
  let F : Ωˣ → ZMod N := fun x =>
    if h : ∃ i : ℕ, i < N ∧ ζ ^ i = (x : Ω) then ((Classical.choose h : ℕ) : ZMod N) else 0
  have hF : ∀ g, ζ ^ (F (d g)).val = (d g : Ω) := by
    intro g
    have hs' := Classical.choose_spec (hex g)
    simp only [F, dif_pos (hex g)]
    rw [ZMod.val_cast_of_lt hs'.1]
    exact hs'.2
  refine ⟨fun g => F (d g), hdlc.comp F, fun g h => ?_⟩
  have hsg : ∀ g : Ω ≃ₐ[K] Ω, g s ≠ 0 := fun g => by simpa using hs0
  have hsg' : ∀ g h : Ω ≃ₐ[K] Ω, g (h s) ≠ 0 := fun g h => by simpa using hs0
  have hdv : ∀ g : Ω ≃ₐ[K] Ω, (d g : Ω) = (γu g : Ω) * s / g s := fun g => by
    simp [d, su, Units.val_div_eq_div_val]
  have hcoc : g (d h : Ω) * (d g : Ω) = ζ ^ ((κ g).val * p h) * (d (g * h) : Ω) := by
    rw [hdv, hdv, hdv, map_div₀, map_mul]
    have h1 := hsg g
    have h2 : g (h s) ≠ 0 := hsg' g h
    calc g (γu h : Ω) * g s / g (h s) * ((γu g : Ω) * s / g s)
        = (g (γu h : Ω) * (γu g : Ω)) * s / g (h s) := by field_simp
      _ = _ := by
          rw [hγ, AlgEquiv.mul_apply]
          field_simp
  rw [← hF h, ← hF g, ← hF (g * h), map_pow, hc0, ← pow_mul, ← pow_add, ← pow_add] at hcoc
  have hz := natCast_eq_of_pow_eq hζ hcoc
  push_cast at hz
  simp only [ZMod.natCast_zmod_val, p] at hz
  linear_combination hz

theorem exists_lift_of_norm [IsSepClosure K Ω] (N : ℕ) [NeZero N]
    (ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N)) (hψ : IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω))) (U : Kˣ)
    (hU : ∃ y : IntermediateField.fixedField ψ.ker, Algebra.norm K y = (U : K)) :
    ∃ b : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant b ∧ ∀ g h : Ω ≃ₐ[K] Ω,
      g (b h : Ω) * (b g : Ω) = (algebraMap K Ω (U : K)) ^
        (((Multiplicative.toAdd (ψ g)).val + (Multiplicative.toAdd (ψ h)).val) / N) *
        (b (g * h) : Ω) := by
  let ψa : (Ω ≃ₐ[K] Ω) → ZMod N := fun g => Multiplicative.toAdd (ψ g)
  have hlc : IsLocallyConstant ψa :=
    isLocallyConstant_of_right_invariant ψ.ker hψ ψa fun g v hv => by
      simp [ψa, map_mul, MonoidHom.mem_ker.1 hv]
  let χ : Additive (Ω ≃ₐ[K] Ω) →ₜ+ QZ :=
    { toFun := fun σ => zmodToQZ N (ψa (Additive.toMul σ))
      map_zero' := by simp [ψa]
      map_add' := fun σ τ => by simp [ψa, toAdd_mul]
      continuous_toFun :=
        ((hlc.comp_continuous continuous_toMul).comp (zmodToQZ N)).continuous }
  have hker : charKer (charAdd χ) = ψ.ker := by
    ext g
    rw [mem_charKer, charAdd_apply, AddEquiv.map_eq_zero_iff, MonoidHom.mem_ker]
    constructor
    · intro h
      have h' : ψa g = 0 := zmodToQZ_injective (h.trans (map_zero _).symm)
      exact h'
    · intro h
      show zmodToQZ N (Multiplicative.toAdd (ψ g)) = 0
      rw [h]
      simp
  have hz : galCupClass K Ω χ U = 0 :=
    (galCupClass_eq_zero_iff_of_isSepClosure χ U).2 (by rw [hker]; exact hU)
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf (galUnitsZ K Ω) χ (unitsInvariant K Ω U)
  rw [galCupClass, ← hw, cohomologyπ_two_eq_zero_iff] at hz
  obtain ⟨f, hf, hfc⟩ := hz
  refine ⟨fun g => Additive.toMul (f g : Additive Ωˣ), hf.comp _, fun g h => ?_⟩
  have e := hfc g h
  rw [hwc] at e
  have e1 : charCocycle (charAdd χ) (g, h) = bockInt ψa g h :=
    charCocycle_eq_bockInt ψa (charAdd χ) (fun _ => rfl) g h
  set m : ℕ := ((Multiplicative.toAdd (ψ g)).val + (Multiplicative.toAdd (ψ h)).val) / N with hm
  have e2 : charCocycle (charAdd χ) (![g, h] 0, ![g, h] 1) = (m : ℤ) := e1
  rw [e2] at e
  let B : (Ω ≃ₐ[K] Ω) → Ωˣ := fun g => Additive.toMul (f g : Additive Ωˣ)
  let u : Ωˣ := Units.map (algebraMap K Ω : K →* Ω) U
  have e3 : ((m : ℤ) • Additive.ofMul u : Additive Ωˣ) =
      Additive.ofMul (galUnitsHom K Ω g (B h)) - Additive.ofMul (B (g * h)) +
        Additive.ofMul (B g) := e
  have e4 := congrArg (Additive.toMul (α := Ωˣ)) e3
  simp only [natCast_zsmul, toMul_nsmul, toMul_add, toMul_sub, toMul_ofMul] at e4
  have e5 := congrArg (Units.val) e4
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_div_eq_div_val,
    coe_galUnitsHom_apply] at e5
  have hu : (u : Ω) = algebraMap K Ω (U : K) := rfl
  rw [hu] at e5
  show g (B h : Ω) * (B g : Ω) = _ * (B (g * h) : Ω)
  rw [e5]
  have hB : (B (g * h) : Ω) ≠ 0 := Units.ne_zero _
  field_simp

theorem kummerCup_eq_coboundary : ∀ {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (N : ℕ), 0 < N → ∀ ζ : Ω, IsPrimitiveRoot ζ N → ∀ c0 : (Ω ≃ₐ[K] Ω) → ZMod N,
    (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ ^ (c0 g).val) → ∀ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N),
    IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω)) → ∀ U : Kˣ,
    (∃ y : IntermediateField.fixedField ψ.ker, Algebra.norm K y = (U : K)) →
    ∀ (T : Ω) (κ : (Ω ≃ₐ[K] Ω) → ZMod N), T ^ N = algebraMap K Ω (U : K) →
    (∀ g : Ω ≃ₐ[K] Ω, g T = ζ ^ (κ g).val * T) →
    ∃ c : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant c ∧ ∀ g h : Ω ≃ₐ[K] Ω,
      c0 g * c h - c (g * h) + c g = κ g * Multiplicative.toAdd (ψ h) := by
  intro K Ω _ _ _ _ N hN ζ hζ c0 hc0 ψ hψ U hU T κ hTN hκ
  have : NeZero N := ⟨hN.ne'⟩
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨b, hb, hbc⟩ := exists_lift_of_norm N ψ hψ U hU
  have hT0 : T ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hTN
    exact (map_ne_zero _).2 U.ne_zero hTN.symm
  refine exists_cochain_of_lift N hζ c0 hc0 ψ hψ (Units.mk0 T hT0) κ hκ b hb
    (fun g h => ((Multiplicative.toAdd (ψ g)).val + (Multiplicative.toAdd (ψ h)).val) / N)
    (fun g h => ?_) (fun g h => ?_)
  · rw [map_mul, toAdd_mul, ZMod.val_add]
    exact (Nat.div_add_mod _ _).symm
  · rw [hbc, Units.val_mk0, hTN]

end GlobalTheory.CompanionTheory.KummerCup
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCocycleNormCriterionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_cocycle_norm_criterion : ∀ {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (N : ℕ), 0 < N → ∀ ζ : Ω, IsPrimitiveRoot ζ N → ∀ c0 : (Ω ≃ₐ[K] Ω) → ZMod N, (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ ^ (c0 g).val) → ∀ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N), IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω)) → ∀ U : Kˣ, (∃ y : IntermediateField.fixedField ψ.ker, Algebra.norm K y = (U : K)) → ∀ (T : Ω) (κ : (Ω ≃ₐ[K] Ω) → ZMod N), T ^ N = algebraMap K Ω (U : K) → (∀ g : Ω ≃ₐ[K] Ω, g T = ζ ^ (κ g).val * T) → ∃ c : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant c ∧ ∀ g h : Ω ≃ₐ[K] Ω, c0 g * c h - c (g * h) + c g = κ g * Multiplicative.toAdd (ψ h) := by
  first | exact @GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary | exact GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary | (intros; apply GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupKummer
set_option maxSynthPendingDepth 1

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open ValuativeRel

namespace GlobalTheory.CompanionTheory.KapChi

theorem pow_val_add {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {ζ : Ω} (hζ : ζ ^ N = 1) (a b : ZMod N) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) N, pow_add, pow_mul, hζ, one_pow, one_mul]

def addHom {D : Type} [Group D] {N : ℕ} (χ : D → ZMod N) (h : ∀ g k, χ (g * k) = χ g + χ k) :
    D →* Multiplicative (ZMod N) :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (χ g)) (fun g k => by rw [h]; rfl)

theorem chi_decomp {D : Type} [Group D] {N : ℕ} (χ : D → ZMod N) (h : ∀ g k, χ (g * k) = χ g + χ k)
    (φ t i : D) (a : ℕ) (hφ : χ φ = 1) (hi : χ i = 0) : χ (φ ^ a * t ^ N * i) = a := by
  have hp : ∀ (x : D) (n : ℕ), χ (x ^ n) = n * χ x := fun x n => by
    have := map_pow (addHom χ h) x n
    have e : Multiplicative.toAdd (addHom χ h (x ^ n)) = χ (x ^ n) := rfl
    rw [← e, this, toAdd_pow]
    simp [addHom]
  rw [h, h, hi, hp, hp, hφ]
  simp

section Dec

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} {N : ℕ}

theorem chi_unique (hA : IsPlaceOver A v) (hN : 0 < N) {χ χ' : Dec (F := F) A → ZMod N}
    (ha : ∀ g h, χ (g * h) = χ g + χ h)
    (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0)
    (hF : ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1)
    (ha' : ∀ g h, χ' (g * h) = χ' g + χ' h)
    (hI' : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ' g = 0)
    (hF' : ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ' g = 1) :
    χ = χ' := by
  obtain ⟨φ₁, hφ₁⟩ := exists_isFrob hA
  let φ : Dec (F := F) A := ⟨φ₁, hφ₁.1⟩
  funext g
  obtain ⟨a, -, t, i, hi, rfl⟩ := GlobalTheory.T.decomposition_group_frobenius_factor F Ω A v hA φ hφ₁ N hN g
  rw [chi_decomp χ ha φ t i a (hF φ hφ₁) (hI i hi), chi_decomp χ' ha' φ t i a (hF' φ hφ₁) (hI' i hi)]

theorem chi_eq_zero_of_fix (hA : IsPlaceOver A v) (hN : 0 < N) {χ : Dec (F := F) A → ZMod N}
    (ha : ∀ g h, χ (g * h) = χ g + χ h)
    (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0)
    (hF : ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1)
    {ξ : Ω} (hξ : IsPrimitiveRoot ξ (normV v ^ N - 1)) (g : Dec (F := F) A)
    (hg : (g : G F Ω) ξ = ξ) : χ g = 0 := by
  obtain ⟨φ₁, hφ₁⟩ := exists_isFrob hA
  let φ : Dec (F := F) A := ⟨φ₁, hφ₁.1⟩
  obtain ⟨a, haN, t, i, hi, rfl⟩ := GlobalTheory.T.decomposition_group_frobenius_factor F Ω A v hA φ hφ₁ N hN g
  have h0 := GlobalTheory.T.frobenius_power_fixes_root_unique F Ω A v hA φ hφ₁ N hN ξ hξ a t i haN hi hg
  rw [chi_decomp χ ha φ t i a (hF φ hφ₁) (hI i hi), h0, Nat.cast_zero]

end Dec

section Core

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem apply_eq_pow_cycMod (l : ℕ) [Fact l.Prime] (r : ℕ) (g : G F Ω) {ζ : Ω} (hζ : ζ ^ l ^ r = 1) :
    g ζ = ζ ^ ((cycMod F Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ

theorem exists_cochain_cup (l : ℕ) [Fact l.Prime] (r : ℕ) (hr : 0 < r) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (l ^ r)) {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) {ϖ ϖ' : 𝓞 F} (h1 : ϖ ∈ v.asIdeal) (h2 : ϖ ∉ v.asIdeal ^ 2)
    (h1' : ϖ' ∈ v.asIdeal) (h2' : ϖ' ∉ v.asIdeal ^ 2) {t : Ω}
    (ht : t ^ l ^ r * algebraMap F Ω (ϖ : F) = algebraMap F Ω (ϖ' : F))
    {κt χ : Dec (F := F) A → ZMod (l ^ r)}
    (hκ : ∀ g : Dec (F := F) A, (g : G F Ω) t = ζ ^ (κt g).val * t)
    (ha : ∀ g h, χ (g * h) = χ g + χ h)
    (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0)
    (hF : ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) :
    ∃ c : Dec (F := F) A → ZMod (l ^ r), Continuous c ∧ ∀ g h : Dec (F := F) A,
      ((cycMod F Ω l r (g : G F Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * c h - c (g * h) + c g =
        κt g * χ h := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hN : 0 < l ^ r := pow_pos hl r
  have : NeZero (l ^ r) := ⟨hN.ne'⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ι, hι⟩ := GlobalTheory.LocDict.exists_isLocEmb F Ω A v hA
  obtain ⟨θ, hθ, hθ', hlift⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc F Ω A v hA ι hι
  have hlift' : ∀ (σ : GlobalTheory.LocDict.GalLoc v) (x : Ω), σ (ι x) = ι ((θ.symm σ : G F Ω) x) := fun σ x => by
    have := hlift (θ.symm σ) x
    rwa [MulEquiv.apply_symm_apply] at this

  have hq : 1 < normV v := ReciprocityTheory.Gal.one_lt_normV v
  obtain ⟨n, hn⟩ : ∃ n, n = normV v ^ l ^ r - 1 := ⟨_, rfl⟩
  have hn0 : n ≠ 0 := by
    have := one_lt_pow₀ hq hN.ne'
    omega
  have : NeZero n := ⟨hn0⟩
  have : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn0⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  rw [hn] at hξ
  have hξv : IsPrimitiveRoot (ι ξ) (Nat.card 𝓀[v.adicCompletion F] ^ l ^ r - 1) := by
    rw [GlobalTheory.T.residue_field_card_eq_norm F v]
    exact hξ.map_of_injective ι.toRingHom.injective
  let ψ : GlobalTheory.LocDict.GalLoc v →* Multiplicative (ZMod (l ^ r)) :=
    (addHom χ ha).comp θ.symm.toMonoidHom
  have hfix : ∀ σ : GlobalTheory.LocDict.GalLoc v, σ (ι ξ) = ι ξ → ψ σ = 1 := fun σ hσ => by
    rw [hlift'] at hσ
    have e := chi_eq_zero_of_fix hA hN ha hI hF hξ (θ.symm σ) (ι.toRingHom.injective hσ)
    show Multiplicative.ofAdd (χ (θ.symm σ)) = 1
    rw [e]
    rfl
  have ho : IsOpen (ψ.ker : Set (GlobalTheory.LocDict.GalLoc v)) := by
    have : FiniteDimensional (v.adicCompletion F) (IntermediateField.adjoin (v.adicCompletion F) {ι ξ}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin (v.adicCompletion F) {ι ξ}).fixingSubgroup)
      (fun σ hσ => hfix σ ?_) (IntermediateField.fixingSubgroup_isOpen _)
    exact hσ ⟨ι ξ, IntermediateField.mem_adjoin_simple_self _ _⟩

  have hϖ0 : algebraMap F (v.adicCompletion F) (ϖ : F) ≠ 0 := by
    intro h
    have h0 : (ϖ : F) = 0 := (map_eq_zero _).1 h
    have h0' : ϖ = 0 := by exact_mod_cast h0
    exact h2 (h0' ▸ Ideal.zero_mem _)
  have hϖ0' : algebraMap F (v.adicCompletion F) (ϖ' : F) ≠ 0 := by
    intro h
    have h0 : (ϖ' : F) = 0 := (map_eq_zero _).1 h
    have h0' : ϖ' = 0 := by exact_mod_cast h0
    exact h2' (h0' ▸ Ideal.zero_mem _)
  let U : (v.adicCompletion F)ˣ := Units.mk0
    (algebraMap F (v.adicCompletion F) (ϖ' : F) / algebraMap F (v.adicCompletion F) (ϖ : F))
    (div_ne_zero hϖ0' hϖ0)
  have hU : (U : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (ϖ : F) =
      algebraMap F (v.adicCompletion F) (ϖ' : F) := div_mul_cancel₀ _ hϖ0
  have hord := GlobalTheory.T.uniformizer_ratio_valuation_zero F v ϖ ϖ' h1 h2 h1' h2' U hU
  have hnorm := GlobalTheory.T.norm_from_kummer_unramified_unit (K := v.adicCompletion F) (Ω := GlobalTheory.LocDict.Kbar v) (l ^ r) hN.ne' (ι ξ) hξv ψ ho hfix U hord
  have hcomm : ∀ x : F, ι (algebraMap F Ω x) =
      algebraMap (v.adicCompletion F) (GlobalTheory.LocDict.Kbar v) (algebraMap F (v.adicCompletion F) x) := fun x => by
    rw [ι.commutes, ← IsScalarTower.algebraMap_apply]
  have hT : ι t ^ l ^ r = algebraMap (v.adicCompletion F) (GlobalTheory.LocDict.Kbar v) (U : v.adicCompletion F) := by
    have e := congrArg ι ht
    rw [map_mul, map_pow, hcomm, hcomm, ← hU, map_mul] at e
    exact mul_right_cancel₀ ((map_ne_zero _).2 hϖ0) e
  have hc0 : ∀ σ : GlobalTheory.LocDict.GalLoc v, σ (ι ζ) = ι ζ ^
      ((cycMod F Ω l r (θ.symm σ : G F Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := fun σ => by
    rw [hlift', apply_eq_pow_cycMod l r _ hζ.pow_eq_one, map_pow]
  have hκ' : ∀ σ : GlobalTheory.LocDict.GalLoc v, σ (ι t) = ι ζ ^ (κt (θ.symm σ)).val * ι t := fun σ => by
    rw [hlift', hκ, map_mul, map_pow]
  obtain ⟨c, hc, hc2⟩ := GlobalTheory.T.kummer_cocycle_norm_criterion (K := v.adicCompletion F) (Ω := GlobalTheory.LocDict.Kbar v) (l ^ r) hN (ι ζ)
    (hζ.map_of_injective ι.toRingHom.injective) _ hc0 ψ ho U hnorm (ι t) (fun σ => κt (θ.symm σ)) hT hκ'
  refine ⟨fun g => c (θ g), hc.continuous.comp hθ, fun g h => ?_⟩
  have e := hc2 (θ g) (θ h)
  have hψ : Multiplicative.toAdd (ψ (θ h)) = χ h := by
    show χ (θ.symm (θ h)) = χ h
    rw [MulEquiv.symm_apply_apply]
  simp only [MulEquiv.symm_apply_apply, ← map_mul] at e
  rw [hψ] at e
  exact e

end Core

theorem cup_class_eq : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) → (∀ g h, z.1 (g, h) = κ g * χ h) → ∀ (ϖ' : 𝓞 F) (y' : Ω) (κ' χ' : Dec (F := F) A → ZMod (l ^ r)) (z' : Z2 (muLoc F l r A)), ϖ' ∈ v.asIdeal → ϖ' ∉ v.asIdeal ^ 2 → y' ^ (l ^ r) = algebraMap F Ω (ϖ' : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y' = ζ ^ (κ' g).val * y') → (∀ g h, χ' (g * h) = χ' g + χ' h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ' g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ' g = 1) → (∀ g h, z'.1 (g, h) = κ' g * χ' h) → (Submodule.Quotient.mk z : H2 (muLoc F l r A)) = Submodule.Quotient.mk z' := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ A v hA ϖ y κ χ z h1 h2 hy hκ hχa hχI hχF hz ϖ' y' κ' χ' z' h1' h2' hy'
    hκ' hχa' hχI' hχF' hz'
  have hN : 0 < l ^ r := pow_pos (Fact.out : l.Prime).pos r
  have : NeZero (l ^ r) := ⟨hN.ne'⟩
  obtain rfl : χ = χ' := chi_unique hA hN hχa hχI hχF hχa' hχI' hχF'
  have hϖ0 : algebraMap F Ω (ϖ : F) ≠ 0 := by
    intro h
    have h0 : (ϖ : F) = 0 := (map_eq_zero _).1 h
    have h0' : ϖ = 0 := by exact_mod_cast h0
    exact h2 (h0' ▸ Ideal.zero_mem _)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hy
    exact hϖ0 hy.symm
  have ht : (y' / y) ^ l ^ r * algebraMap F Ω (ϖ : F) = algebraMap F Ω (ϖ' : F) := by
    rw [div_pow, hy, hy', div_mul_cancel₀ _ hϖ0]
  have hκt : ∀ g : Dec (F := F) A, (g : G F Ω) (y' / y) = ζ ^ (κ' g - κ g).val * (y' / y) := fun g => by
    have e := pow_val_add hζ.pow_eq_one (κ' g - κ g) (κ g)
    rw [sub_add_cancel] at e
    have hgy : ζ ^ (κ g).val ≠ 0 := pow_ne_zero _ (hζ.ne_zero hN.ne')
    rw [map_div₀, hκ, hκ', e]
    field_simp
  obtain ⟨c, hc, hc2⟩ := exists_cochain_cup l r hr hζ hA h1 h2 h1' h2' ht hκt hχa hχI hχF
  refine ((Submodule.Quotient.eq _).2 ?_).symm
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c, hc, funext fun p => ?_⟩
  obtain ⟨g, h⟩ := p
  have e := hc2 g h
  rw [sub_mul] at e
  show _ = z'.1 (g, h) - z.1 (g, h)
  rw [hz, hz', ← e]
  rfl

end GlobalTheory.CompanionTheory.KapChi
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupKummerStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_invariant_cup_kummer : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) → (∀ g h, z.1 (g, h) = κ g * χ h) → ∀ (ϖ' : 𝓞 F) (y' : Ω) (κ' χ' : Dec (F := F) A → ZMod (l ^ r)) (z' : Z2 (muLoc F l r A)), ϖ' ∈ v.asIdeal → ϖ' ∉ v.asIdeal ^ 2 → y' ^ (l ^ r) = algebraMap F Ω (ϖ' : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y' = ζ ^ (κ' g).val * y') → (∀ g h, χ' (g * h) = χ' g + χ' h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ' g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ' g = 1) → (∀ g h, z'.1 (g, h) = κ' g * χ' h) → (Submodule.Quotient.mk z : H2 (muLoc F l r A)) = Submodule.Quotient.mk z' := by
  first | exact @GlobalTheory.CompanionTheory.KapChi.cup_class_eq | exact GlobalTheory.CompanionTheory.KapChi.cup_class_eq | (intros; apply GlobalTheory.CompanionTheory.KapChi.cup_class_eq <;> assumption)
end
