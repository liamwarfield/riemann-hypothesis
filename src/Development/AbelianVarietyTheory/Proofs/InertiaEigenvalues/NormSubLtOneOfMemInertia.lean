module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCongruenceFiltrationFiniteTowerBound
public import GroundTheory.PAdicHodge.AxLemma

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldIntegerIffAlgebraicClosureNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldIntegerIffAlgebraicClosureNorm
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

noncomputable section

namespace GlobalTheory.PMon.Ram

theorem padic_mem_integer_iff (l : ℕ) [Fact l.Prime] (a : ℚ_[l]) : a ∈ 𝒪[ℚ_[l]] ↔ ‖a‖ ≤ 1 := by
  change valuation ℚ_[l] a ≤ 1 ↔ _
  rw [← map_one (valuation ℚ_[l]), ← (valuation ℚ_[l]).vle_iff_le,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one]

theorem isIntegral_integer_iff_norm_le (l : ℕ) [Fact l.Prime] (y : Om l) :
    IsIntegral 𝒪[ℚ_[l]] y ↔ ‖y‖ ≤ 1 := by
  have hy : IsIntegral ℚ_[l] y := Algebra.IsIntegral.isIntegral y
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hy)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact (padic_mem_integer_iff l _).1 ((minpoly 𝒪[ℚ_[l]] y).coeff n).2
  · intro h
    have hl : minpoly ℚ_[l] y ∈ Polynomial.lifts (algebraMap 𝒪[ℚ_[l]] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      exact fun n => ⟨⟨_, (padic_mem_integer_iff l _).2 (h n)⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hy)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

end GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt (l : ℕ) [Fact l.Prime] (L : Type) [Field L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L]
    [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)]
    [IsScalarTower ℚ_[l] L (Om l)] (x : L) :
    (x ∈ 𝒪[L] ↔ ‖algebraMap L (Om l) x‖ ≤ 1) ∧ (valuation L x < 1 ↔ ‖algebraMap L (Om l) x‖ < 1) := by
  have key : ∀ z : L, z ∈ 𝒪[L] ↔ ‖algebraMap L (Om l) z‖ ≤ 1 := by
    intro z
    let f : L →ₐ[𝒪[ℚ_[l]]] Om l := (IsScalarTower.toAlgHom ℚ_[l] L (Om l)).restrictScalars 𝒪[ℚ_[l]]
    have hf : Function.Injective f := (algebraMap L (Om l)).injective
    rw [← isIntegral_integer_iff_norm_le]
    change valuation L z ≤ 1 ↔ IsIntegral 𝒪[ℚ_[l]] (f z)
    rw [isIntegral_algHom_iff f hf, GroundTheory.LocalField.isIntegral_iff ℚ_[l] L z]
  refine ⟨key x, ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hy : algebraMap L (Om l) x ≠ 0 := (map_ne_zero _).2 hx
  have hv : valuation L x ≠ 0 := by simpa using hx
  have h1 := key x⁻¹
  rw [map_inv₀, norm_inv, inv_le_one₀ (norm_pos_iff.2 hy)] at h1
  change valuation L x⁻¹ ≤ 1 ↔ _ at h1
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 hv)] at h1
  rw [← not_le, ← not_le, h1]

end GlobalTheory.PMon.Ram

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldIntegerIffAlgebraicClosureNormStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)] (x : L), (x ∈ 𝒪[L] ↔ ‖algebraMap L (Om l) x‖ ≤ 1) ∧ (valuation L x < 1 ↔ ‖algebraMap L (Om l) x‖ < 1) := by
  first | exact @GlobalTheory.PMon.Ram.mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt | exact GlobalTheory.PMon.Ram.mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt | (intros; apply GlobalTheory.PMon.Ram.mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDetectedSubgroupTowerRatProof
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrdIsEqCardInertia
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem ordIs_padic_self (l : ℕ) [Fact l.Prime] : OrdIs ℚ_[l] l 1 := by
  unfold OrdIs
  rw [IsDiscreteValuationRing.addVal_uniformizer (GroundTheory.LocalField.Padic.irreducible_natCast_integer l)]
  rfl

theorem ordIs_eq_card_inertia : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)],
    OrdIs L l (Nat.card ↥(lowerRamificationGroup ℚ_[l] L 0)) := by
  intro l _ L _ _ _ _ _ _ _ _ _ _
  have hlL : (l : L) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] L)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hne : ((l : 𝒪[L])) ≠ 0 := by
    intro h
    apply hlL
    have h2 : ((l : 𝒪[L]) : L) = 0 := by rw [h]; rfl
    simpa using h2
  have htop : IsDiscreteValuationRing.addVal 𝒪[L] (l : 𝒪[L]) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨E, hE⟩ := WithTop.ne_top_iff_exists.1 htop
  have hL : OrdIs L l E := by unfold OrdIs; rw [← hE]; rfl
  obtain ⟨e, he, hEe, hram⟩ := GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension ℚ_[l] L l E hL
  have h1 := ordIs_padic_self l
  unfold OrdIs at he h1
  have he1 : e = 1 := by
    have := he.symm.trans h1
    exact_mod_cast this
  subst he1
  rw [mul_one] at hEe
  unfold OrdIs
  rw [← hram, ← hEe, ← hE]
  rfl

end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictNormalHomMemLowerRamificationGroupZero
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem restrictNormalHom_mem_lowerRamificationGroup_zero : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)] (σ : GQ l), (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → AlgEquiv.restrictNormalHom L σ ∈ lowerRamificationGroup ℚ_[l] L 0 := by
  intro l _ L _ _ _ _ _ _ _ _ _ _ σ hσ
  rw [mem_lowerRamificationGroup_iff]
  intro x
  have h01 : ((0 : ℤ) + 1).toNat = 1 := rfl
  rw [h01, pow_one]
  have hx : ‖algebraMap L (Om l) (x : L)‖ ≤ 1 := ((GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L (x : L)).1).1 x.2
  have hc : algebraMap L (Om l) (AlgEquiv.restrictNormalHom L σ (x : L)) = σ (algebraMap L (Om l) (x : L)) :=
    AlgEquiv.restrictNormal_commutes σ L (x : L)
  have hlt : valuation L (AlgEquiv.restrictNormalHom L σ (x : L) - (x : L)) < 1 := by
    rw [(GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L _).2, map_sub, hc]
    exact hσ _ hx
  intro hu
  have h1 := (Valuation.integer.integers (valuation L)).isUnit_iff_valuation_eq_one.1 hu
  have h2 : ((((integerAlgEquiv ℚ_[l] L) ((AlgEquiv.restrictNormalHom L) σ)) x - x : 𝒪[L]) : L) =
      AlgEquiv.restrictNormalHom L σ (x : L) - (x : L) := rfl
  change valuation L ((((integerAlgEquiv ℚ_[l] L) ((AlgEquiv.restrictNormalHom L) σ)) x - x : 𝒪[L]) : L) = 1 at h1
  rw [h2] at h1
  exact hlt.ne h1

end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaFiniteGaloisPadic
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaFiniteGaloisPadic
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem norm_natCast_self_Om (l : ℕ) [Fact l.Prime] : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have h : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := (map_natCast _ _).symm
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

theorem axConstant_le_sq (l : ℕ) [hl : Fact l.Prime] : GroundTheory.PAdicHodge.axConstant l ≤ (l : ℝ) ^ 2 := by
  have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hexp : (l : ℝ) / ((l : ℝ) - 1) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  unfold GroundTheory.PAdicHodge.axConstant
  calc (l : ℝ) ^ ((l : ℝ) / ((l : ℝ) - 1) ^ 2) ≤ (l : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
    _ = (l : ℝ) ^ 2 := by norm_cast

theorem axIn_padic : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)], AxIn ℚ_[l] L l := by
  intro l _ L _ _ _ _ _ _ _ _ _ _
  intro J x hx
  have hO := GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L
  let φ : L →ₐ[ℚ_[l]] Om l := IsScalarTower.toAlgHom ℚ_[l] L (Om l)
  have hφ : ∀ y : L, φ y = algebraMap L (Om l) y := fun y => rfl
  let F : IntermediateField ℚ_[l] L := IntermediateField.fixedField J
  let E : IntermediateField ℚ_[l] (Om l) := F.map φ
  have hmove : ∀ g : Gal(Om l/E), ‖g (φ x) - φ x‖ ≤ 1 := by
    intro g
    let g' : Om l ≃ₐ[ℚ_[l]] Om l := g.restrictScalars ℚ_[l]
    let τ : L ≃ₐ[ℚ_[l]] L := AlgEquiv.restrictNormalHom L g'
    have hτ : ∀ y : L, φ (τ y) = g' (φ y) := fun y => AlgEquiv.restrictNormal_commutes g' L y
    have hτJ : τ ∈ J := by
      rw [← IntermediateField.fixingSubgroup_fixedField J]
      rintro ⟨y, hy⟩
      apply φ.toRingHom.injective
      change φ (τ y) = φ y
      rw [hτ]
      have hyE : φ y ∈ E := ⟨y, hy, rfl⟩
      exact g.commutes ⟨φ y, hyE⟩
    have h1 := (hO (τ x - x)).1.1 (hx τ hτJ)
    rw [map_sub, ← hφ, ← hφ, hτ] at h1
    exact h1
  obtain ⟨Y, hYE, hY⟩ := GroundTheory.PAdicHodge.ax_lemma (K := E) (φ x) hmove
  obtain ⟨y, hyF, rfl⟩ := hYE
  refine ⟨y, fun σ hσ => (IntermediateField.mem_fixedField_iff J y).1 hyF σ hσ, ?_⟩
  rw [(hO _).1, map_mul, map_pow, map_natCast, map_sub, norm_mul, norm_pow, norm_natCast_self_Om, ← hφ, ← hφ]
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hc := axConstant_le_sq l
  rw [mul_one] at hY
  calc ((l : ℝ)⁻¹) ^ 2 * ‖φ x - φ y‖ ≤ ((l : ℝ)⁻¹) ^ 2 * (l : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (hY.trans hc) (by positivity)
    _ = 1 := by rw [inv_pow, inv_mul_cancel₀ (by positivity)]

end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaFiniteGaloisPadicStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.axLemma_finiteGalois_padic : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)], AxIn ℚ_[l] L l := by
  first | exact @GlobalTheory.PMon.Ram.axIn_padic | exact GlobalTheory.PMon.Ram.axIn_padic | (intros; apply GlobalTheory.PMon.Ram.axIn_padic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharactersDetectRestrictNormalInfFiniteLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharactersDetectRestrictNormalInfFiniteLevel
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem detects_restrictNormal_inf : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)] (r : ℕ) (N N' : Subgroup (GQ l))
    (I : Subgroup (L ≃ₐ[ℚ_[l]] L)) (ι : Type) (x : ι → Om l) (a : ι → GQ l → ℤ),
    (∀ i, x i ∈ Set.range (algebraMap L (Om l))) →
    (∀ i, ∀ σ ∈ N, ‖σ (x i) - x i - (a i σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) →
    (∀ σ ∈ N, (∀ i, (l : ℤ) ^ r ∣ a i σ) → σ ∈ N') →
    Detects l r (N.map (AlgEquiv.restrictNormalHom L) ⊓ I) (N'.map (AlgEquiv.restrictNormalHom L) ⊓ I) := by
  intro l _ L _ _ _ _ _ _ _ _ _ _ r N N' I ι x a hx hN hN'
  classical
  intro σ₀ hσ₀ hσ₀B

  let lift : (L ≃ₐ[ℚ_[l]] L) → GQ l := fun s =>
    if h : ∃ σ ∈ N, AlgEquiv.restrictNormalHom L σ = s then h.choose else 1
  have hlift : ∀ s ∈ N.map (AlgEquiv.restrictNormalHom L),
      lift s ∈ N ∧ AlgEquiv.restrictNormalHom L (lift s) = s := by
    intro s hs
    have h : ∃ σ ∈ N, AlgEquiv.restrictNormalHom L σ = s := Subgroup.mem_map.mp hs
    simp only [lift, dif_pos h]
    exact h.choose_spec
  obtain ⟨hτN, hτ⟩ := hlift σ₀ hσ₀.1
  have hτN' : lift σ₀ ∉ N' := by
    intro h
    exact hσ₀B ⟨Subgroup.mem_map.mpr ⟨lift σ₀, h, hτ⟩, hσ₀.2⟩
  have hex : ∃ i, ¬ (l : ℤ) ^ r ∣ a i (lift σ₀) := by
    by_contra hc
    push_neg at hc
    exact hτN' (hN' _ hτN hc)
  obtain ⟨i, hi⟩ := hex
  obtain ⟨x', hx'⟩ := hx i
  have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlL : (l : L) ^ r ≠ 0 := by
    refine pow_ne_zero _ ?_
    rw [← map_natCast (algebraMap ℚ_[l] L)]
    exact (map_ne_zero _).mpr (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have hnorm_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
    have h : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
    rw [h, PadicAlgCl.norm_extends, Padic.norm_p]
  refine ⟨x', fun s => a i (lift s), ?_, hi⟩
  intro s hs
  obtain ⟨hσN, hσ⟩ := hlift s hs.1
  have key : algebraMap L (Om l) (s x') = lift s (x i) := by
    rw [← hx']
    conv_lhs => rw [← hσ]
    exact AlgEquiv.restrictNormal_commutes (lift s) L x'
  refine ⟨(s x' - x' - (a i (lift s) : L)) / (l : L) ^ r, ?_, ?_⟩
  · refine ((GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L _).1).mpr ?_
    rw [map_div₀, map_sub, map_sub, map_intCast, map_pow, map_natCast, key, hx', norm_div, norm_pow, hnorm_l]
    rw [div_le_one (by positivity)]
    exact hN i _ hσN
  · rw [mul_div_cancel₀ _ hlL]
    ring

end GlobalTheory.PMon.Ram
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharactersDetectRestrictNormalInfFiniteLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characters_detect_restrictNormal_inf_finiteLevel : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)] (r : ℕ) (N N' : Subgroup (GQ l)) (I : Subgroup (L ≃ₐ[ℚ_[l]] L)) (ι : Type) (x : ι → Om l) (a : ι → GQ l → ℤ), (∀ i, x i ∈ Set.range (algebraMap L (Om l))) → (∀ i, ∀ σ ∈ N, ‖σ (x i) - x i - (a i σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) → (∀ σ ∈ N, (∀ i, (l : ℤ) ^ r ∣ a i σ) → σ ∈ N') → Detects l r (N.map (AlgEquiv.restrictNormalHom L) ⊓ I) (N'.map (AlgEquiv.restrictNormalHom L) ⊓ I) := by
  first | exact @GlobalTheory.PMon.Ram.detects_restrictNormal_inf | exact GlobalTheory.PMon.Ram.detects_restrictNormal_inf | (intros; apply GlobalTheory.PMon.Ram.detects_restrictNormal_inf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisKerLeRange
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_galois_ker_le_range (l : ℕ) [Fact l.Prime] (U : Subgroup (GQ l)) (S : Set (Om l))
    (hU : IsOpen (U : Set (GQ l))) (hS : S.Finite) :
    ∃ (L : Type) (_ : Field L) (_ : ValuativeRel L) (_ : TopologicalSpace L) (_ : IsNonarchimedeanLocalField L)
      (_ : Algebra ℚ_[l] L) (_ : ValuativeExtension ℚ_[l] L) (_ : FiniteDimensional ℚ_[l] L)
      (_ : IsGalois ℚ_[l] L) (_ : Algebra L (Om l)) (_ : IsScalarTower ℚ_[l] L (Om l)),
      (AlgEquiv.restrictNormalHom L : GQ l →* (L ≃ₐ[ℚ_[l]] L)).ker ≤ U ∧
        S ⊆ Set.range (algebraMap L (Om l)) := by
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff ℚ_[l] (Om l) (U : Set (GQ l))).mp
    (hU.mem_nhds U.one_mem)
  haveI := hS.to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let F : IntermediateField ℚ_[l] (Om l) := E ⊔ IntermediateField.adjoin ℚ_[l] S
  let M : IntermediateField ℚ_[l] (Om l) := IntermediateField.normalClosure ℚ_[l] F (Om l)
  haveI : FiniteDimensional ℚ_[l] M := inferInstance
  haveI : Normal ℚ_[l] M := inferInstance
  haveI : IsGalois ℚ_[l] M := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have hFM : F ≤ M := IntermediateField.le_normalClosure F
  obtain ⟨vr, top, hloc, hext⟩ := exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] M
  refine ⟨M, inferInstance, vr, top, hloc, inferInstance, hext, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_⟩
  · rw [IntermediateField.restrictNormalHom_ker]
    intro σ hσ
    apply hEU
    exact (IntermediateField.fixingSubgroup_le (le_trans le_sup_left hFM)) hσ
  · intro x hx
    have : x ∈ M := hFM (le_sup_right (a := E) (IntermediateField.subset_adjoin ℚ_[l] S hx))
    exact ⟨⟨x, this⟩, rfl⟩

end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeIndexMulCardMapInf
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_le_index_mul_card_map_inf (G H : Type) [Group G] [Group H] [Finite H]
    (f : G →* H) (N : Subgroup G) (I : Subgroup H) (hf : Function.Surjective f)
    (hN : N.index ≠ 0) : Nat.card ↥I ≤ N.index * Nat.card ↥(N.map f ⊓ I) := by
  have h1 : (N.map f).relIndex I * Nat.card ↥(N.map f ⊓ I) = Nat.card I := by
    rw [Subgroup.relIndex, mul_comm, ← Subgroup.card_mul_index ((N.map f).subgroupOf I)]
    congr 1
    rw [← Subgroup.inf_subgroupOf_right]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  have h2 : (N.map f).relIndex I ≤ (N.map f).index := by
    rw [← Subgroup.relIndex_top_right]
    apply Subgroup.relIndex_le_of_le_right le_top
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  have h3 : (N.map f).index ≤ N.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Subgroup.index_map_dvd N hf)
  rw [← h1]
  exact Nat.mul_le_mul_right _ (h2.trans h3)

end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDetectedSubgroupTowerRatProof
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem noTowerQ_holds : NoTowerQ := by
  intro l _ N hanti hopen h1 h2 h3
  by_contra hcon
  push Not at hcon
  obtain ⟨k₀, hk₀⟩ := h3 8
  have hex : ∃ k ≥ k₀, ∃ σ ∈ N k, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) ∧ σ ∉ N (k + 1) := by
    by_contra hno
    push Not at hno
    obtain ⟨j, σ, hσ, hi, hj⟩ := hcon k₀
    have : ∀ i, σ ∈ N (k₀ + i) := by
      intro i
      induction i with
      | zero => exact hσ
      | succ i ih => exact hno (k₀ + i) (by omega) σ ih hi
    exact hj (hanti (by omega : j ≤ k₀ + j) (this j))
  obtain ⟨k, hk, σ₀, hσ₀, hi₀, hn₀⟩ := hex
  have hT : (N k).index ≠ 0 := by
    have : Finite (GQ l ⧸ N k) := Subgroup.quotient_finite_of_isOpen _ (hopen k)
    exact Subgroup.index_ne_zero_of_finite
  set T := (N k).index with hTdef
  choose ι hι x a hxa hdet using fun i : ℕ => hk₀ (k + i) (by omega)
  have hS : (⋃ i ∈ Set.Iic (2 * T), Set.range (x i)).Finite :=
    (Set.finite_Iic _).biUnion fun i _ => by have := hι i; exact Set.finite_range _
  obtain ⟨L, _, _, _, _, _, _, _, _, _, _, hker, hSL⟩ :=
    exists_galois_ker_le_range l (N (k + (2 * T + 8))) _ (hopen _) hS
  set res : GQ l →* (L ≃ₐ[ℚ_[l]] L) := AlgEquiv.restrictNormalHom L with hres
  set I := lowerRamificationGroup ℚ_[l] L 0 with hI
  have hlift : ∀ j ≤ 2 * T + 8, ∀ σ : GQ l, res σ ∈ (N (k + j)).map res → σ ∈ N (k + j) := by
    intro j hj σ ⟨τ, hτ, e⟩
    have h : τ⁻¹ * σ ∈ res.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
    have h' : τ⁻¹ * σ ∈ N (k + j) := hanti (by omega) (hker h)
    simpa using (N (k + j)).mul_mem hτ h'
  have hE : 0 < Nat.card I := Nat.card_pos
  have hfin := GlobalTheory.T.inertia_congruenceFiltration_finite_tower_bound ℚ_[l] L l (Nat.card I) T (fun j => (N (k + j)).map res ⊓ I) Fact.out hE
    (ordIs_eq_card_inertia l L) (GlobalTheory.T.axLemma_finiteGalois_padic l L)
    (fun i j hij => inf_le_inf_right _ (Subgroup.map_mono (hanti (by omega)))) inf_le_right
    (fun h => hn₀ (hlift 1 (by omega) σ₀
      (h ⟨⟨σ₀, hσ₀, rfl⟩, restrictNormalHom_mem_lowerRamificationGroup_zero l L σ₀ hi₀⟩).1))
    (by
      rintro _ ⟨⟨σ, hσ, rfl⟩, hσI⟩
      exact ⟨⟨σ ^ l, h1 k σ hσ, map_pow _ _ _⟩, I.pow_mem hσI l⟩)
    (by
      rintro j hj _ ⟨⟨σ, hσ, rfl⟩, hσI⟩ hp
      refine ⟨⟨σ, h2 (k + j) σ (hanti (Nat.zero_le _) hσ) (hlift (j + 1) hj _ ?_), rfl⟩, hσI⟩
      rw [map_pow]; exact hp.1)
    (by
      intro i hi
      have := GlobalTheory.T.characters_detect_restrictNormal_inf_finiteLevel l L 8 (N (k + i)) (N (k + i + 8)) I (ι i) (x i) (a i)
        (fun b => hSL (Set.mem_biUnion (show i ∈ Set.Iic (2 * T) from hi) ⟨b, rfl⟩)) (hxa i) (hdet i)
      simpa [add_assoc] using this)
  have hidx := card_le_index_mul_card_map_inf (GQ l) (L ≃ₐ[ℚ_[l]] L) res (N k) I
    (AlgEquiv.restrictNormalHom_surjective _) hT
  have hlt : T < 2 ^ T := Nat.lt_two_pow_self
  have hpos : 0 < Nat.card ↥((N k).map res ⊓ I) := Nat.card_pos
  simp only [add_zero] at hfin
  nlinarith

end GlobalTheory.PMon.Ram

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDetectedSubgroupTowerRatProofStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noDetectedSubgroupTowerRat_proof : NoTowerQ := by
  first | exact @GlobalTheory.PMon.Ram.noTowerQ_holds | exact GlobalTheory.PMon.Ram.noTowerQ_holds | (intros; apply GlobalTheory.PMon.Ram.noTowerQ_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproxComplexPadicCoboundaryAlgebraicInteger
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproxComplexPadicCoboundaryAlgebraicInteger
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem approx_algebraic_integer : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Set (GQ l)) (x : ℂ_[l]) (a : GQ l → ℤ_[l]), (∀ σ ∈ S, ‖Formalism.Per.σC σ x - x - algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r) → ∃ (y : Om l) (b : GQ l → ℤ), (∀ σ ∈ S, ‖σ y - y - (b σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧ ∀ σ, (l : ℤ) ^ r ∣ b σ → (l : ℤ_[l]) ^ r ∣ a σ := by
  intro l _ r S x a h
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hδ : (0 : ℝ) < ((l : ℝ)⁻¹) ^ r := by positivity
  obtain ⟨y, hy⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt x hδ
  have hdiff : ∀ σ : GQ l, (l : ℤ_[l]) ^ r ∣ a σ - (((a σ).appr r : ℕ) : ℤ_[l]) := by
    intro σ
    exact Ideal.mem_span_singleton.1 (PadicInt.appr_spec r (a σ))
  refine ⟨y, fun σ => (((a σ).appr r : ℕ) : ℤ), ?_, ?_⟩
  · intro σ hσ
    have hY : ‖(y : ℂ_[l]) - x‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      rw [← dist_eq_norm, dist_comm]; exact hy.le
    have hAB : ‖algebraMap ℚ_[l] ℂ_[l] ((a σ - (((a σ).appr r : ℕ) : ℤ_[l]) : ℤ_[l]) : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      rw [norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]
      obtain ⟨c, hc⟩ := hdiff σ
      rw [hc, norm_mul, norm_pow, PadicInt.norm_p]
      have := PadicInt.norm_le_one c
      have h0 : (0:ℝ) ≤ ((l : ℝ)⁻¹) ^ r := hδ.le
      calc ((l : ℝ)⁻¹) ^ r * ‖c‖ ≤ ((l : ℝ)⁻¹) ^ r * 1 := mul_le_mul_of_nonneg_left this h0
        _ = _ := mul_one _
    have key : (((σ y - y - ((((((a σ).appr r : ℕ) : ℤ)) : Om l))) : PadicAlgCl l) : ℂ_[l]) =
        (Formalism.Per.σC σ x - x - algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l])) +
        (Formalism.Per.σC σ ((y : ℂ_[l]) - x) - ((y : ℂ_[l]) - x)) +
        (algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) - ((((a σ).appr r : ℕ)) : ℂ_[l])) := by
      have h1 : ((σ y : PadicAlgCl l) : ℂ_[l]) = Formalism.Per.σC σ (y : ℂ_[l]) := (GlobalTheory.RingBasics.σC_coe σ y).symm
      generalize algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) = A
      rw [map_sub]
      push_cast
      rw [h1]
      ring
    have hAB' : ‖algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) - ((((a σ).appr r : ℕ)) : ℂ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      simpa only [PadicInt.coe_sub, PadicInt.coe_natCast, map_sub, map_natCast] using hAB
    rw [← PadicComplex.norm_extends, key]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h σ hσ) ?_)) hAB')
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [GlobalTheory.RingBasics.norm_σC]; exact hY
    · rw [norm_neg]; exact hY
  · intro σ _
    have : (a σ) = (a σ - (((a σ).appr r : ℕ) : ℤ_[l])) + (((a σ).appr r : ℕ) : ℤ_[l]) := by ring
    rw [this]
    refine dvd_add (hdiff σ) ?_
    have := map_dvd (Int.castRingHom ℤ_[l]) (by assumption : (l : ℤ) ^ r ∣ (((a σ).appr r : ℕ) : ℤ))
    simpa using this

end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproxComplexPadicCoboundaryAlgebraicIntegerStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approx_complexPadic_coboundary_algebraic_integer : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Set (GQ l)) (x : ℂ_[l]) (a : GQ l → ℤ_[l]), (∀ σ ∈ S, ‖Formalism.Per.σC σ x - x - algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r) → ∃ (y : Om l) (b : GQ l → ℤ), (∀ σ ∈ S, ‖σ y - y - (b σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧ ∀ σ, (l : ℤ) ^ r ∣ b σ → (l : ℤ_[l]) ^ r ∣ a σ := by
  first | exact @GlobalTheory.PMon.Ram.approx_algebraic_integer | exact GlobalTheory.PMon.Ram.approx_algebraic_integer | (intros; apply GlobalTheory.PMon.Ram.approx_algebraic_integer <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem norm_sub_lt_one_of_mem_inertia {l : ℕ} [Fact l.Prime] (K : FinExt l) (σ : ↥(GK K)) (hσ : σ ∈ IK K) :
    ∀ x : Om l, ‖x‖ ≤ 1 → ‖(σ : GQ l) x - x‖ < 1 := by
  unfold IK at hσ
  induction hσ using Subgroup.closure_induction with
  | mem σ h => exact h
  | one => intro x _; simp
  | mul σ τ _ _ hσ hτ =>
    intro x hx
    have h1 : ‖(τ : GQ l) x‖ ≤ 1 := by rw [GlobalTheory.RingBasics.norm_gal]; exact hx
    have e : ((σ * τ : ↥(GK K)) : GQ l) x - x
        = ((σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x) + ((τ : GQ l) x - x) := by
      rw [Subgroup.coe_mul, AlgEquiv.mul_apply]; ring
    rw [e]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hσ _ h1) (hτ _ hx))
  | inv σ _ hσ =>
    intro x hx
    have h1 : ‖((σ : GQ l)⁻¹) x‖ ≤ 1 := by rw [GlobalTheory.RingBasics.norm_gal]; exact hx
    have h2 := hσ _ h1
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, norm_sub_rev] at h2
    rw [Subgroup.coe_inv]
    exact h2

theorem noTower : NoTower := by
  classical
  intro l _ K N hanti hopen hpow hroot hchar
  have : FiniteDimensional ℚ_[l] (K : IntermediateField ℚ_[l] (Om l)) := K.2
  have hGK : IsOpen ((GK K : Subgroup (GQ l)) : Set (GQ l)) := IntermediateField.fixingSubgroup_isOpen _
  have hmem : ∀ k (σ : ↥(GK K)), (σ : GQ l) ∈ (N k).map (GK K).subtype ↔ σ ∈ N k := fun k σ =>
    Subgroup.mem_map_iff_mem (GK K).subtype_injective
  obtain ⟨k, hk⟩ := GlobalTheory.T.noDetectedSubgroupTowerRat_proof l (fun k => (N k).map (GK K).subtype)
    (fun i j hij => Subgroup.map_mono (hanti hij))
    (fun k => hGK.isOpenMap_subtype_val _ (hopen k))
    (by
      rintro k _ ⟨σ, hσ, rfl⟩
      exact ⟨σ ^ l, hpow k σ hσ, rfl⟩)
    (by
      rintro j _ ⟨σ, hσ, rfl⟩ h
      exact ⟨σ, hroot j σ hσ ((hmem _ (σ ^ l)).1 h), rfl⟩)
    (by
      intro r
      obtain ⟨k₀, hk₀⟩ := hchar r
      refine ⟨k₀, fun k hk => ?_⟩
      obtain ⟨ι, hι, x, a, h1, h2⟩ := hk₀ k hk
      have key := fun i => GlobalTheory.T.approx_complexPadic_coboundary_algebraic_integer l r ((N k).map (GK K).subtype : Subgroup (GQ l)) (x i)
        (fun σ => if h : σ ∈ GK K then a i ⟨σ, h⟩ else 0) (by
          rintro _ ⟨σ, hσ, rfl⟩
          have := h1 i σ hσ
          simpa using this)
      choose y b hy hb using key
      refine ⟨ι, hι, y, b, fun i σ hσ => hy i σ hσ, ?_⟩
      rintro _ ⟨σ, hσ, rfl⟩ h
      refine ⟨σ, h2 σ hσ fun i => ?_, rfl⟩
      have := hb i _ (h i)
      simpa using this)
  refine ⟨k, fun j σ hσ => ?_⟩
  exact (hmem j σ).1 (hk j _ ((hmem k σ).2 hσ.2) (norm_sub_lt_one_of_mem_inertia K σ hσ.1))

end GlobalTheory.PMon.Ram
