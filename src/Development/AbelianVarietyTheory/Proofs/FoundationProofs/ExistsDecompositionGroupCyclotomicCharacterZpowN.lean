module

public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassRootsNotDistinctLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassNotRootsAvoidLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassHasDivisorOfDegreeLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
public import Formalism.QuotientMetricDivisors.Statement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassNotRootsAvoidLeStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.CycDec

theorem exists_unit_infinite_order (l : ℕ) [Fact l.Prime] :
    ∃ u : ℤ_[l]ˣ, ∀ n : ℤ, n ≠ 0 → u ^ n ≠ 1 := by
  have hl : l.Prime := Fact.out
  have hu : IsUnit (1 + (l : ℤ_[l])) := by
    rw [← sub_neg_eq_add]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h =>
      PadicInt.irreducible_p.not_isUnit ((IsUnit.neg_iff _).1 h)
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, fun n hn h => ?_⟩
  have h1 : u ^ n.natAbs = 1 := by
    rcases Int.natAbs_eq n with e | e
    · rw [← zpow_natCast, ← e, h]
    · rw [e, zpow_neg, inv_eq_one, zpow_natCast] at h
      exact h
  have h2 : (((1 + l) ^ n.natAbs : ℕ) : ℤ_[l]) = ((1 : ℕ) : ℤ_[l]) := by
    push_cast
    rw [← hu, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
  have h3 := Nat.cast_injective h2
  rw [pow_eq_one_iff] at h3
  rcases h3 with h3 | h3
  · exact hl.ne_zero (by omega)
  · exact hn (Int.natAbs_eq_zero.1 h3)

theorem exists_mem_Dec_cycZ_zpow_ne_one : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F))
    (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∀ n : ℤ, n ≠ 0 →
    ∃ g : G F Ω, g ∈ Dec (F := F) A ∧ cycZ F Ω l g ^ n ≠ 1 := by
  intro F Ω _ _ _ _ _ l _ v A hl hA n hn
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hv : A.valuation (l : Ω) < 1 := by
    simpa using (hA _).2 hl
  obtain ⟨u, hu⟩ := exists_unit_infinite_order l
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
  have hD : σ ^ N ∈ Dec (F := ℚ) A := (Dec (F := ℚ) A).pow_mem (Ine_le_Dec A hσ) N
  have hc : cycZ F Ω l g = cycZ ℚ Ω l (σ ^ N) := rfl
  refine ⟨g, hD, ?_⟩
  rw [hc, map_pow, hσu, ← zpow_natCast, ← zpow_mul]
  exact hu _ (mul_ne_zero (by exact_mod_cast hN.ne') hn)

end GlobalTheory.CycDec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowNStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_decompositionGroup_cyclotomicCharacter_zpow_ne_one : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∀ n : ℤ, n ≠ 0 → ∃ g : G F Ω, g ∈ Dec (F := F) A ∧ cycZ F Ω l g ^ n ≠ 1 := by
  first | exact @GlobalTheory.CycDec.exists_mem_Dec_cycZ_zpow_ne_one | exact GlobalTheory.CycDec.exists_mem_Dec_cycZ_zpow_ne_one | (intros; apply GlobalTheory.CycDec.exists_mem_Dec_cycZ_zpow_ne_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OverAffineJLineComapSlGal
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OverAffineJLineComapSlGal
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ

theorem vs_mem_of_isIntegral {K : Type} [Field K] (W : ValuationSubring K) {x : K} (h : IsIntegral W x) : x ∈ W := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  rw [← hy]; exact y.2

theorem hs_coeff_algebraMap {Ω : Type} [Field Ω] (c : Ω) (r : ℚ) :
    (algebraMap Ω (HahnSeries ℚ Ω) c).coeff r = if r = 0 then c else 0 := by
  rw [HahnSeries.algebraMap_apply']
  have : algebraMap Ω (PowerSeries Ω) c = PowerSeries.C c := rfl
  rw [this, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single]
  simp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.gal_algebraMap (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  change (X.exp (X.gal s (algebraMap Ω X.K c))).coeff r = (X.exp (algebraMap Ω X.K (s c))).coeff r
  rw [X.gal_exp, AlgHom.commutes, AlgHom.commutes, hs_coeff_algebraMap, hs_coeff_algebraMap]
  split_ifs <;> simp

theorem Tower.gal_jK (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.gal s X.jK = X.jK := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  change (X.exp (X.gal s X.jK)).coeff r = (X.exp X.jK).coeff r
  rw [X.gal_exp]
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [hn, map_intCast]

theorem Tower.adjoin_le_of_overY (X : Tower Ω ε) (W : ValuationSubring X.K) (hW : X.OverY W) :
    ∀ x ∈ Algebra.adjoin Ω {X.jK}, x ∈ W := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff.mp hy]; exact hW.2
  | algebraMap c => exact hW.1 c
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem Tower.overY_comap_sl_gal : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ W : ValuationSubring X.K, X.OverY W →
      (∀ g : GQ, X.OverY (W.comap (X.sl g).toRingEquiv.toRingHom)) ∧
        ∀ s : Ω ≃ₐ[ℚ] Ω, X.OverY (W.comap (X.gal s).toRingHom) := by
  intro Ω _ _ _ ε X hε hj W hW
  refine ⟨fun g => ⟨fun c => ?_, ?_⟩, fun s => ⟨fun c => ?_, ?_⟩⟩
  · rw [ValuationSubring.mem_comap]
    change X.sl g (algebraMap Ω X.K c) ∈ W
    rw [AlgEquiv.commutes]; exact hW.1 c
  · rw [ValuationSubring.mem_comap]
    change X.sl g X.jK ∈ W
    have hint := GlobalTheory.T.isIntegral_modularTower_j_comp_glTwoPosRat ε X hε hj g
    let A := Algebra.adjoin Ω {X.jK}
    have hle : A.toSubring ≤ W.toSubring := fun x hx => X.adjoin_le_of_overY W hW x hx
    let ι : A →+* W := Subring.inclusion hle
    let _ : Algebra A W := ι.toAlgebra
    have : IsScalarTower A W X.K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    exact vs_mem_of_isIntegral W (hint.tower_top)
  · rw [ValuationSubring.mem_comap]
    change X.gal s (algebraMap Ω X.K c) ∈ W
    rw [X.gal_algebraMap]; exact hW.1 (s c)
  · rw [ValuationSubring.mem_comap]
    change X.gal s X.jK ∈ W
    rw [X.gal_jK]; exact hW.2

end GlobalTheory.KZ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OverAffineJLineComapSlGalStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.overAffineJLine_comap_sl_gal : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ W : ValuationSubring X.K, X.OverY W → (∀ g : GQ, X.OverY (W.comap (X.sl g).toRingEquiv.toRingHom)) ∧ ∀ s : Ω ≃ₐ[ℚ] Ω, X.OverY (W.comap (X.gal s).toRingHom) := by
  first | exact @GlobalTheory.KZ.Tower.overY_comap_sl_gal | exact GlobalTheory.KZ.Tower.overY_comap_sl_gal | (intros; apply GlobalTheory.KZ.Tower.overY_comap_sl_gal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerSlActionRowVector
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerSlActionRowVector
noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ.SiegelSL

theorem isOpen_Hs : IsOpen Hs := by
  show IsOpen {z : ℂ | 0 < z.im}
  exact isOpen_lt continuous_const Complex.continuous_im

theorem neBot_Hs : (Filter.codiscreteWithin Hs).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have hmem : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs := h ▸ Filter.mem_bot
  rw [mem_codiscreteWithin] at hmem
  have hI : Complex.I ∈ Hs := by
    show (0 : ℝ) < Complex.I.im
    simp
  have h1 := hmem Complex.I hI
  rw [Set.sdiff_empty, Filter.disjoint_principal_right] at h1
  have h2 : Hs ∈ nhdsWithin Complex.I {Complex.I}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hI)
  have h3 := Filter.inter_mem h1 h2
  rw [Set.compl_inter_self] at h3
  simpa using Filter.nonempty_of_mem h3

theorem germ_eq_of_eqOn {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) := by
  apply Filter.Germ.coe_eq.2
  filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
  exact h z hz

theorem sgC_coe (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : sgC c x τ = sg c x τ := by
  simp [sgC, UpperHalfPlane.ofComplex_apply]

theorem mob_ofSL (γ : SL(2, ℤ)) (τ : ℍ) : mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mob, ent, ofSL]

theorem an_injective {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) :
    Function.Injective T.an := by
  have := neBot_Hs
  exact T.an.injective

theorem siegel_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) {c : ℕ} {x : Fin 2 → ℚ} {f : T.K}
    (hf : T.an f = ((sgC c x : ℂ → ℂ) : Mero)) : siegel T c x = f := by
  have hex : ∃ g : T.K, T.an g = ((sgC c x : ℂ → ℂ) : Mero) := ⟨f, hf⟩
  apply an_injective T
  rw [siegel, dite_eq_left hex, hex.choose_spec, hf]

theorem sl_siegel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ)
    (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), GlobalTheory.Sieg.admitted c x → T.sl (ofSL γ) (siegel T c x) = siegel T c (act x γ) := by
  intro Ω _ _ _ ε T c x γ hx
  symm
  apply siegel_eq
  rw [T.an_sl _ _ _ (GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hx)]
  apply germ_eq_of_eqOn
  intro z hz
  have hτ : ((⟨z, hz⟩ : ℍ) : ℂ) = z := rfl
  rw [← hτ, mob_ofSL, sgC_coe, sgC_coe, GlobalTheory.T.siegel_function_transformation c x γ _ hx]

end GlobalTheory.KZ.SiegelSL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerSlActionRowVectorStatement
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelUnitInTower_sl_action_rowVector : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), GlobalTheory.Sieg.admitted c x → T.sl (ofSL γ) (siegel T c x) = siegel T c (act x γ) := by
  first | exact @GlobalTheory.KZ.SiegelSL.sl_siegel | exact GlobalTheory.KZ.SiegelSL.sl_siegel | (intros; apply GlobalTheory.KZ.SiegelSL.sl_siegel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitQExpansionCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitQExpansionCoefficients
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KExp

theorem norm_cexp_real (t : ℝ) (z : ℂ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * z)‖ = Real.exp (-2 * Real.pi * t * z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem uniq (d : ℚ → ℂ) (hwf : (Function.support d).IsWF) (S : Set ℂ)
    (hz : ∀ z ∈ S, HasSum (fun r : ℚ => d r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) 0)
    (z1 : ℂ) (h1 : Summable (fun r : ℚ => d r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z1)))
    (hS : ∀ y : ℝ, ∃ z ∈ S, y < z.im) : d = 0 := by
  by_contra hne
  have hnon : (Function.support d).Nonempty := by
    obtain ⟨r, hr⟩ := Function.ne_iff.mp hne
    exact ⟨r, hr⟩
  set r0 := hwf.min hnon with hr0def
  have hr0 : d r0 ≠ 0 := hwf.min_mem hnon
  have hle : ∀ r, d r ≠ 0 → r0 ≤ r := fun r hr => hwf.min_le hnon hr
  choose zs hzS hzim using fun j : ℕ => hS (max z1.im 0 + j)
  set y1 := z1.im with hy1
  have hnorm : ∀ (r : ℚ) (z : ℂ), ‖d r * Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) - r0) * z)‖
      = ‖d r‖ * Real.exp (-2 * Real.pi * ((r : ℝ) - r0) * z.im) := by
    intro r z
    rw [norm_mul]
    have := norm_cexp_real ((r : ℝ) - r0) z
    push_cast at this
    rw [this]
  let f : ℕ → ℚ → ℂ := fun j r => d r * Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) - r0) * zs j)
  let g : ℚ → ℂ := fun r => if r = r0 then d r0 else 0
  let bound : ℚ → ℝ := fun r => ‖d r‖ * Real.exp (-2 * Real.pi * ((r : ℝ) - r0) * y1)
  have hb : Summable bound := by
    have h2 := ((summable_norm_iff (E := ℂ)).mpr h1).mul_right (Real.exp (2 * Real.pi * r0 * y1))
    refine h2.congr fun r => ?_
    simp only [bound]
    have hn := norm_cexp_real (r : ℝ) z1
    rw [Complex.ofReal_ratCast] at hn
    rw [norm_mul, hn, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop) (f := f) (g := g) hb ?_ ?_
  · have hf0 : ∀ j, ∑' r, f j r = 0 := by
      intro j
      have h := (hz (zs j) (hzS j)).mul_left (Complex.exp (-(2 * Real.pi * Complex.I * (r0 : ℂ) * zs j)))
      rw [mul_zero] at h
      refine Eq.trans (tsum_congr fun r => ?_) h.tsum_eq
      simp only [f]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      ring
    have hg : ∑' r, g r = d r0 := by
      rw [tsum_eq_single r0 (fun r hr => by simp [g, hr])]
      simp [g]
    simp only [hf0, hg] at hlim
    exact hr0 (tendsto_nhds_unique hlim tendsto_const_nhds)
  · intro r
    by_cases hr : r = r0
    · subst hr
      simp only [f, g, if_pos rfl, sub_self, mul_zero, zero_mul, Complex.exp_zero, mul_one]
      exact tendsto_const_nhds
    by_cases hd : d r = 0
    · simp only [f, g, hd, zero_mul, if_neg hr]
      exact tendsto_const_nhds
    have hlt : (r0 : ℝ) < r := by exact_mod_cast lt_of_le_of_ne (hle r hd) (Ne.symm hr)
    simp only [g, if_neg hr]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hpos : 0 < 2 * Real.pi * ((r : ℝ) - r0) := by have := Real.pi_pos; nlinarith
    have hT : Filter.Tendsto (fun j : ℕ => ‖d r‖ * Real.exp (-(2 * Real.pi * ((r : ℝ) - r0) * j))) Filter.atTop (nhds 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop hpos)).const_mul ‖d r‖
      simpa using this
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hT
    simp only [f]
    rw [hnorm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have : (j : ℝ) ≤ (zs j).im := by
      have := hzim j
      have : (0 : ℝ) ≤ max y1 0 := le_max_right _ _
      linarith
    nlinarith
  · refine Filter.Eventually.of_forall fun j r => ?_
    simp only [f, bound]
    rw [hnorm]
    by_cases hd : d r = 0
    · simp [hd]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have h1 : (r0 : ℝ) ≤ r := by exact_mod_cast hle r hd
    have : y1 ≤ (zs j).im := by
      have := hzim j
      have : y1 ≤ max y1 0 := le_max_left _ _
      have : (0:ℝ) ≤ j := by positivity
      linarith
    have hp : 0 ≤ 2 * Real.pi * ((r : ℝ) - r0) := mul_nonneg (by positivity) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left this hp]

end GlobalTheory.KExp

namespace GlobalTheory.KExp

theorem siegel_exp : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (M a b : ℕ), 0 < M → a < M → GlobalTheory.Sieg.admitted c ![(a : ℚ) / M, (b : ℚ) / M] → ∃ (k : ℤ) (A : ℕ → Ω), GlobalTheory.QFam.HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => ε (A n)) ∧ (∀ n : ℕ, (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff (((k : ℚ) + n) / M) = A n) ∧ ∀ r : ℚ, (∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) → (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff r = 0 := by
  intro Ω _ _ _ ε T c M a b hM haM hadm
  classical
  set x : Fin 2 → ℚ := ![(a : ℚ) / M, (b : ℚ) / M] with hx
  obtain ⟨k, hk⟩ := GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral c M a hM haM
  obtain ⟨A', hA', -⟩ := hk b hadm
  have hmem := GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hadm
  set f := siegel T c x with hf
  obtain ⟨φ, C, hφ, hsum⟩ := T.an_exp f
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  let ι : ℕ → ℚ := fun n => ((k : ℚ) + n) / M
  have hι : Function.Injective ι := by
    intro n m h
    simp only [ι] at h
    rw [div_left_inj' hMq, add_right_inj] at h
    exact_mod_cast h
  let B : ℚ → ℂ := fun r => if h : ∃ n, ι n = r then A' h.choose else 0
  have hBι : ∀ n, B (ι n) = A' n := by
    intro n
    have h : ∃ m, ι m = ι n := ⟨n, rfl⟩
    simp only [B, dif_pos h]
    rw [hι h.choose_spec]
  have hB0 : ∀ r, r ∉ Set.range ι → B r = 0 := by
    intro r hr
    simp only [B]
    rw [dite_eq_right]
    exact hr
  have hBsum : ∀ z : ℂ, 0 < z.im →
      HasSum (fun r : ℚ => B r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (sgC c x z) := by
    intro z hz
    have h2 := (hA' ⟨z, hz⟩).mul_left (ee ((k : ℂ) / M * z))
    rw [← hι.hasSum_iff (fun r hr => by simp [hB0 r hr])]
    have e1 : ((fun r : ℚ => B r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) ∘ ι) = fun n : ℕ =>
        ee ((k : ℂ) / M * z) * (A' n * Complex.exp (2 * Real.pi * Complex.I * n * z / M)) := by
      funext n
      simp only [Function.comp_apply, hBι, ι, ee]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      field_simp
    have e2 : sgC c x z = ee ((k : ℂ) / M * z) * (sg c x ⟨z, hz⟩ * ee (-((k : ℂ) / M) * z)) := by
      simp only [sgC, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      rw [mul_left_comm, ee, ee, ← Complex.exp_add]
      have : 2 * Real.pi * Complex.I * ((k : ℂ) / M * z) + 2 * Real.pi * Complex.I * (-((k : ℂ) / M) * (z : ℂ)) = 0 := by
        ring
      rw [this, Complex.exp_zero, mul_one]
    rw [e1, e2]
    simpa using h2
  have hgerm : φ =ᶠ[Filter.codiscreteWithin Hs] sgC c x := by
    have := hφ.symm.trans hmem
    exact Filter.Germ.coe_eq.mp this
  let S : Set ℂ := {z | C < z.im ∧ 0 < z.im ∧ φ z = sgC c x z}
  have hS : ∀ y : ℝ, ∃ z ∈ S, y < z.im := by
    intro y
    set Y := max (max y C) 0 + 1 with hY
    set w : ℂ := Complex.I * Y
    have hwim : w.im = Y := by simp [w]
    have hw : w ∈ Hs := by
      show 0 < w.im
      rw [hwim]; have := le_max_right (max y C) 0; linarith
    have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hgerm w hw
    have h2 : Metric.ball w (1 / 2) ∈ nhdsWithin w {w}ᶜ :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds w (by norm_num))
    obtain ⟨z, hz1, hz2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
    have hdist : |z.im - Y| < 1 / 2 := by
      have := Complex.abs_im_le_norm (z - w)
      rw [Metric.mem_ball, dist_eq_norm] at hz2
      rw [Complex.sub_im, hwim] at this
      linarith
    have hyY : y ≤ max (max y C) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
    have hCY : C ≤ max (max y C) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
    have h0Y : 0 ≤ max (max y C) 0 := le_max_right _ _
    have hzim : max (max y C) 0 + 1 / 2 < z.im := by
      have := (abs_lt.mp hdist).1; linarith
    have hzH : z ∈ Hs := show 0 < z.im by linarith
    refine ⟨z, ⟨by linarith, by linarith, ?_⟩, by linarith⟩
    rcases hz1 with h | h
    · exact h
    · exact absurd hzH h
  let d : ℚ → ℂ := fun r => ε ((T.exp f).coeff r) - B r
  have hd : d = 0 := by
    refine GlobalTheory.KExp.uniq d ?_ S ?_ (Complex.I * (|C| + 1)) ?_ hS
    · have hR : (Set.range ι).IsWF := by
        have : Set.range ι = ι '' Set.univ := Set.image_univ.symm
        rw [this]
        refine (Set.IsPWO.image_of_monotone (Set.isPWO_of_wellQuasiOrderedLE _) ?_).isWF
        intro n m h
        simp only [ι]
        gcongr
      refine ((T.exp f).isWF_support.union hR).mono ?_
      · intro r hr
        by_contra hn
        simp only [Set.mem_union, not_or] at hn
        apply hr
        simp only [d, hB0 r hn.2]
        have : (T.exp f).coeff r = 0 := by simpa [HahnSeries.support] using hn.1
        simp [this]
    · intro z hz
      have := (hsum z hz.1).sub (hBsum z hz.2.1)
      rw [hz.2.2, sub_self] at this
      simpa [d, sub_mul] using this
    · have hzi : C < (Complex.I * (|C| + 1)).im := by
        simp; have := le_abs_self C; linarith
      have hzp : 0 < (Complex.I * (|C| + 1)).im := by simp; positivity
      have := ((hsum _ hzi).summable.sub (hBsum _ hzp).summable)
      simpa [d, sub_mul] using this
  have hdr : ∀ r, ε ((T.exp f).coeff r) = B r := fun r => sub_eq_zero.mp (congrFun hd r)
  refine ⟨k, fun n => (T.exp f).coeff (ι n), ?_, fun n => rfl, ?_⟩
  · have : (fun n => ε ((T.exp f).coeff (ι n))) = A' := funext fun n => by rw [hdr, hBι]
    rw [this]
    exact hA'
  · intro r hr
    have hr' : r ∉ Set.range ι := by
      rintro ⟨n, rfl⟩
      exact hr n rfl
    have := hdr r
    rw [hB0 r hr'] at this
    exact (map_eq_zero_iff ε ε.injective).mp this

end GlobalTheory.KExp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitQExpansionCoefficientsStatement
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_unit_q_expansion_coefficients : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (M a b : ℕ), 0 < M → a < M → GlobalTheory.Sieg.admitted c ![(a : ℚ) / M, (b : ℚ) / M] → ∃ (k : ℤ) (A : ℕ → Ω), GlobalTheory.QFam.HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => ε (A n)) ∧ (∀ n : ℕ, (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff (((k : ℚ) + n) / M) = A n) ∧ ∀ r : ℚ, (∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) → (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff r = 0 := by
  first | exact @GlobalTheory.KExp.siegel_exp | exact GlobalTheory.KExp.siegel_exp | (intros; apply GlobalTheory.KExp.siegel_exp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodSquarefreeLabelTuplesWeightGe
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodSquarefreeLabelTuplesWeightGe
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

variable (g : ℕ) [Fact g.Prime]

def tupleMass {ι : Type} [Fintype ι] (N : ℕ) (P : (ι → (ZMod g)[X]) → Prop) : ℝ :=
  ∑ F ∈ Fintype.piFinset fun _ : ι => sqSet g N, if P F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0

variable {g} {ι : Type} [Fintype ι] {N : ℕ}

theorem tupleWeight_nonneg (F : ι → (ZMod g)[X]) : 0 ≤ ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
  exact Finset.prod_nonneg fun v _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem tupleMass_le_add {P Q R : (ι → (ZMod g)[X]) → Prop}
    (h : ∀ F, (∀ v, F v ∈ sqSet g N) → P F → Q F ∨ R F) :
    tupleMass g N P ≤ tupleMass g N Q + tupleMass g N R := by
  unfold tupleMass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun F hF => ?_
  have hw := tupleWeight_nonneg F
  have hmem : ∀ v, F v ∈ sqSet g N := fun v => Fintype.mem_piFinset.mp hF v
  by_cases hP : P F
  · rw [if_pos hP]
    rcases h F hmem hP with hQ | hR
    · rw [if_pos hQ]; split_ifs <;> linarith
    · rw [if_pos hR]; split_ifs <;> linarith
  · rw [if_neg hP]; split_ifs <;> linarith

theorem tupleMass_exists_le {κ : Type} (s : Finset κ) (Q : κ → (ι → (ZMod g)[X]) → Prop) :
    tupleMass g N (fun F => ∃ i ∈ s, Q i F) ≤ ∑ i ∈ s, tupleMass g N (Q i) := by
  unfold tupleMass
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun F _ => ?_
  have hz : ∀ j ∈ s, 0 ≤ (if Q j F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0) := fun j _ => by
    split_ifs
    · exact tupleWeight_nonneg F
    · exact le_rfl
  split_ifs with h
  · obtain ⟨i, hi, hQ⟩ := h
    calc ∏ v, ((torusCard g (F v) : ℝ))⁻¹ = (if Q i F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0) := by rw [if_pos hQ]
      _ ≤ ∑ j ∈ s, if Q j F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0 :=
        Finset.single_le_sum (f := fun j => if Q j F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0) hz hi
  · exact Finset.sum_nonneg hz

theorem tupleMass_forall (A : ι → (ZMod g)[X] → Prop) :
    tupleMass g N (fun F => ∀ v, A v (F v)) = ∏ v, mass g N (A v) := by
  unfold tupleMass mass
  simp_rw [Finset.sum_filter]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  split_ifs with h
  · exact Finset.prod_congr rfl fun v _ => (if_pos (h v)).symm
  · push Not at h
    obtain ⟨v, hv⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)).symm

theorem tupleMass_single_le (h1 : (mass g N fun _ => True) ≤ 1) (v : ι) (A : (ZMod g)[X] → Prop) :
    tupleMass g N (fun F : ι → (ZMod g)[X] => A (F v)) ≤ mass g N A := by
  have hm : ∀ B : (ZMod g)[X] → Prop, 0 ≤ mass g N B := fun B => by
    unfold mass
    exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have key : tupleMass g N (fun F : ι → (ZMod g)[X] => A (F v)) =
      tupleMass g N (fun F => ∀ w, (if w = v then A else fun _ => True) (F w)) := by
    unfold tupleMass
    refine Finset.sum_congr rfl fun F _ => ?_
    have hiff : A (F v) ↔ ∀ w, (if w = v then A else fun _ => True) (F w) :=
      ⟨fun h w => by by_cases hw : w = v <;> simp_all, fun h => by simpa using h v⟩
    by_cases h : A (F v)
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (mt hiff.mpr h)]
  rw [key, tupleMass_forall, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), if_pos rfl]
  have hrest : ∏ w ∈ Finset.univ.erase v, mass g N (if w = v then A else fun _ => True) ≤ 1 := by
    apply Finset.prod_le_one₀
    · exact fun w _ => hm _
    · intro w hw
      rw [if_neg (Finset.ne_of_mem_erase hw)]
      exact h1
  calc mass g N A * _ ≤ mass g N A * 1 := mul_le_mul_of_nonneg_left hrest (hm A)
    _ = _ := mul_one _

theorem goodSet_weight_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ (N m q d : ℕ) (ι : Type) [Fintype ι] (ch : ι → Fin m → (ZMod g)ˣ), 100000 ≤ N → 2 ^ 12 ≤ g → (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → 1 - (badBound g (Fintype.card ι) m N ((min q d : ℕ) : ℝ) - (Fintype.card ι : ℝ) / g) ≤ ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
  intro g _ N m q d ι _ ch hN hg hqd
  have hm : ∀ B : (ZMod g)[X] → Prop, 0 ≤ mass g N B := fun B => by
    unfold mass
    exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have h1 : (mass g N fun _ => True) ≤ 1 := (GlobalTheory.T.squarefreeLabelTorusMass_divisor_bound g).1 N
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (Fact.out : g.Prime).pos
  have hg4 : (4096 : ℝ) ≤ g := by exact_mod_cast hg
  have hN' : (100000 : ℝ) ≤ N := by exact_mod_cast hN
  have hall : 1 - 2 * (Fintype.card ι : ℝ) / g ≤ tupleMass g N (fun _ : ι → (ZMod g)[X] => True) := by
    have e := tupleMass_forall (g := g) (N := N) (fun (_ : ι) (_ : (ZMod g)[X]) => True)
    simp only [implies_true] at e
    rw [e]
    have h2 : 0 ≤ 1 - 2 / (g : ℝ) := by
      rw [sub_nonneg, div_le_one hg0]; linarith
    have h3 : (-2 : ℝ) ≤ -2 / g := by
      rw [le_div_iff₀ hg0]; nlinarith
    calc 1 - 2 * (Fintype.card ι : ℝ) / g = 1 + (Fintype.card ι : ℝ) * (-2 / g) := by ring
      _ ≤ (1 + (-2 / (g : ℝ))) ^ Fintype.card ι := one_add_mul_le_pow h3 _
      _ = ∏ _v : ι, (1 - 2 / (g : ℝ)) := by rw [Finset.prod_const, Finset.card_univ]; ring
      _ ≤ ∏ _v : ι, mass g N (fun _ => True) :=
        Finset.prod_le_prod₀ (fun _ _ => h2) (fun _ _ => GlobalTheory.T.one_sub_two_div_le_squarefreeLabelMass g N)
  have hsq : ∀ f ∈ sqSet g N, (f.Monic ∧ f.natDegree = N ∧ f.coeff 0 ≠ 0) ∧ Squarefree f := by
    intro f hf
    unfold sqSet at hf
    rw [Finset.mem_filter, Finset.mem_image] at hf
    obtain ⟨⟨c, -, rfl⟩, hsf, hc0⟩ := hf
    have hdeg := degree_sum_fin_lt c
    refine ⟨⟨monic_X_pow_add hdeg, ?_, hc0⟩, hsf⟩
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have hE1 : tupleMass g N (fun F : ι → (ZMod g)[X] => ∃ v ∈ Finset.univ, ¬ RootsApart g N (F v)) ≤
      (Fintype.card ι : ℝ) * (23 * Real.log g / Real.sqrt g) := by
    calc _ ≤ ∑ v ∈ Finset.univ, tupleMass g N (fun F : ι → (ZMod g)[X] => ¬ RootsApart g N (F v)) :=
          tupleMass_exists_le (Finset.univ : Finset ι) (fun (v : ι) (F : ι → (ZMod g)[X]) => ¬ RootsApart g N (F v))
      _ ≤ ∑ _v ∈ (Finset.univ : Finset ι), (23 * Real.log g / Real.sqrt g) :=
          Finset.sum_le_sum fun v _ => (tupleMass_single_le h1 v _).trans (GlobalTheory.T.squarefreeLabelTorusMass_rootsNotDistinct_le g N hg)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hE2 : ∀ c : ι → Fin m → (ZMod g)ˣ,
      tupleMass g N (fun F : ι → (ZMod g)[X] =>
        ∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (c p.1 p.2) (F p.1)) ≤
      (Fintype.card ι : ℝ) * m * (1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1)) := by
    intro c
    calc _ ≤ ∑ p ∈ (Finset.univ : Finset (ι × Fin m)),
            tupleMass g N (fun F : ι → (ZMod g)[X] => ¬ RootsAvoid g (c p.1 p.2) (F p.1)) :=
          tupleMass_exists_le (Finset.univ : Finset (ι × Fin m))
            (fun (p : ι × Fin m) (F : ι → (ZMod g)[X]) => ¬ RootsAvoid g (c p.1 p.2) (F p.1))
      _ ≤ ∑ _p ∈ (Finset.univ : Finset (ι × Fin m)),
            (1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1)) :=
          Finset.sum_le_sum fun p _ => (tupleMass_single_le h1 p.1 _).trans (GlobalTheory.T.mass_not_rootsAvoid_le' g N q d _ hqd)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have hE4 : tupleMass g N (fun F : ι → (ZMod g)[X] => ∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ≤
      (N : ℝ) / 2 * (7 / 8) ^ Fintype.card ι := by
    calc _ ≤ ∑ a ∈ Finset.Icc 1 (N / 2), tupleMass g N (fun F : ι → (ZMod g)[X] => ∀ v, HasDiv g a (F v)) :=
          tupleMass_exists_le (Finset.Icc 1 (N / 2)) (fun (a : ℕ) (F : ι → (ZMod g)[X]) => ∀ v, HasDiv g a (F v))
      _ = ∑ a ∈ Finset.Icc 1 (N / 2), ∏ _v : ι, mass g N (HasDiv g a) :=
          Finset.sum_congr rfl fun a _ => tupleMass_forall (fun _ => HasDiv g a)
      _ ≤ ∑ _a ∈ Finset.Icc 1 (N / 2), ((7 : ℝ) / 8) ^ Fintype.card ι := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [Finset.mem_Icc] at ha
          calc ∏ _v : ι, mass g N (HasDiv g a) ≤ ∏ _v : ι, ((7 : ℝ) / 8) :=
                Finset.prod_le_prod₀ (fun _ _ => hm _) (fun _ _ => GlobalTheory.T.squarefreeLabelTorusMass_hasDivisorOfDegree_le g N a (by omega) (by omega))
            _ = _ := by rw [Finset.prod_const, Finset.card_univ]
      _ = ((N / 2 : ℕ) : ℝ) * (7 / 8) ^ Fintype.card ι := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
      _ ≤ _ := mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
  have hL : (1 : ℝ) ≤ 10 * Real.log N := by
    have : (1 : ℝ) ≤ Real.log N :=
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    linarith
  have hE5 : tupleMass g N (fun F : ι → (ZMod g)[X] => ∀ v, ¬ HasPrimeFactor g N (F v)) ≤
      Real.exp (-((Fintype.card ι : ℝ) / (10 * Real.log N))) := by
    calc _ = ∏ _v : ι, mass g N (fun f => ¬ HasPrimeFactor g N f) :=
          tupleMass_forall (fun _ f => ¬ HasPrimeFactor g N f)
      _ ≤ ∏ _v : ι, (1 - 1 / (10 * Real.log N)) :=
          Finset.prod_le_prod₀ (fun _ _ => hm _) (fun _ _ => GlobalTheory.T.squarefreeLabelTorusMass_no_large_prime_factor_le g N hN)
      _ = (1 + (-(1 / (10 * Real.log N)))) ^ Fintype.card ι := by
          rw [Finset.prod_const, Finset.card_univ]; ring
      _ ≤ (Real.exp (-(1 / (10 * Real.log N)))) ^ Fintype.card ι := by
          refine pow_le_pow_left₀ ?_ ?_ _
          · have : 1 / (10 * Real.log N) ≤ 1 := by rw [div_le_one (by linarith)]; exact hL
            linarith
          · linarith [Real.add_one_le_exp (-(1 / (10 * Real.log N)))]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hsplit : ∀ F : ι → (ZMod g)[X], (∀ v, F v ∈ sqSet g N) → True →
      Good g N ch F ∨
      ((∃ v ∈ Finset.univ, ¬ RootsApart g N (F v)) ∨
      ((∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (ch p.1 p.2) (F p.1)) ∨
      ((∃ p ∈ (Finset.univ : Finset (ι × Fin m)),
          ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)) ∨
      ((∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨
      (∀ v, ¬ HasPrimeFactor g N (F v)))))) := by
    intro F hF _
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨hG, h1', h2', h3', h4', h5'⟩ := hcon
    apply hG
    have hA : ∀ v, RootsApart g N (F v) := fun v =>
      Classical.byContradiction fun h => h1' ⟨v, Finset.mem_univ _, h⟩
    have hB : ∀ v j, RootsAvoid g (ch v j) (F v) := fun v j =>
      Classical.byContradiction fun h => h2' ⟨(v, j), Finset.mem_univ _, h⟩
    have hC : ∀ v j, RootsAvoid g (ch v j)⁻¹ (F v) := fun v j =>
      Classical.byContradiction fun h => h3' ⟨(v, j), Finset.mem_univ _, h⟩
    have hD : ∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ HasDiv g a (F v) := fun a ha1 ha2 => by
      by_contra h
      push Not at h
      exact h4' ⟨a, Finset.mem_Icc.mpr ⟨ha1, by omega⟩, h⟩
    have hE : ∃ v, HasPrimeFactor g N (F v) := by
      by_contra h
      push Not at h
      exact h5' h
    unfold Good Formalism.CyclotomicNorms.IsGood
    exact ⟨⟨fun v => (hsq _ (hF v)).1, fun v => (hsq _ (hF v)).2,
        fun l hl hl' v => hA v l hl hl', fun l hl hlg v j => hB v j l hl hlg, hD, hE⟩,
      ⟨fun v => (hsq _ (hF v)).1, fun v => (hsq _ (hF v)).2,
        fun l hl hl' v => hA v l hl hl', fun l hl hlg v j => hC v j l hl hlg, hD, hE⟩⟩
  have hor : ∀ {P Q : (ι → (ZMod g)[X]) → Prop},
      tupleMass g N (fun F => P F ∨ Q F) ≤ tupleMass g N P + tupleMass g N Q :=
    fun {_ _} => tupleMass_le_add fun _ _ h => h
  have hgood : tupleMass g N (Good g N ch) = ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
    unfold tupleMass goodSet
    rw [Finset.sum_filter]
  have s0 := tupleMass_le_add hsplit
  have s1 := hor (P := fun F => (∃ v ∈ Finset.univ, ¬ RootsApart g N (F v)))
    (Q := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (ch p.1 p.2) (F p.1)) ∨ ((∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)) ∨ ((∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨ (∀ v, ¬ HasPrimeFactor g N (F v)))))
  have s2 := hor (P := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (ch p.1 p.2) (F p.1)))
    (Q := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)) ∨ ((∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨ (∀ v, ¬ HasPrimeFactor g N (F v))))
  have s3 := hor (P := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)))
    (Q := fun F => (∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨ (∀ v, ¬ HasPrimeFactor g N (F v)))
  have s4 := hor (P := fun F => (∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)))
    (Q := fun F => (∀ v, ¬ HasPrimeFactor g N (F v)))
  beta_reduce at s0 s1 s2 s3 s4
  have b2 := hE2 ch
  have b3 := hE2 (fun v j => (ch v j)⁻¹)
  have hb4 := s4.trans (add_le_add hE4 hE5)
  have hb3 := s3.trans (add_le_add b3 hb4)
  have hb2 := s2.trans (add_le_add b2 hb3)
  have hb1 := s1.trans (add_le_add hE1 hb2)
  have hb0 := s0.trans (add_le_add le_rfl hb1)
  rw [← hgood]
  unfold badBound
  rw [Real.rpow_natCast]
  ring_nf at hall hb0 ⊢
  linarith only [hall, hb0]

end GlobalTheory.BadShare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodSquarefreeLabelTuplesWeightGeStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodSquarefreeLabelTuples_weight_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ (N m q d : ℕ) (ι : Type) [Fintype ι] (ch : ι → Fin m → (ZMod g)ˣ), 100000 ≤ N → 2 ^ 12 ≤ g → (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → 1 - (badBound g (Fintype.card ι) m N ((min q d : ℕ) : ℝ) - (Fintype.card ι : ℝ) / g) ≤ ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
  first | exact @GlobalTheory.BadShare.goodSet_weight_ge | exact GlobalTheory.BadShare.goodSet_weight_ge | (intros; apply GlobalTheory.BadShare.goodSet_weight_ge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaLeOfDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaLeOfDvd
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem gamma_le_of_dvd {N N' : ℕ} (hd : N ∣ N') :
    CongruenceSubgroup.Gamma N' ≤ CongruenceSubgroup.Gamma N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  have key : ∀ x : ℤ, (x : ZMod N) = ZMod.castHom hd (ZMod N) (x : ZMod N') := fun x => by
    rw [map_intCast]
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key, h1, map_one]
  · rw [key, h2, map_zero]
  · rw [key, h3, map_zero]
  · rw [key, h4, map_one]

theorem lv_mono : ∀ (E : Subring ℂ) (N N' w w' : ℕ) (f : ℍ → ℂ), 0 < N' → N ∣ N' → w ≤ w' →
    Lv E N w f → Lv E N' w' f := by
  intro E N N' w w' f hN' hd hw hf
  refine ⟨fun γ hγ τ => hf.1 γ (gamma_le_of_dvd hd hγ) τ, fun γ => ?_⟩
  have h1 : QAll (· ∈ E) N' fun τ => DD τ ^ w * f (γ • τ) :=
    QAll.of_dvd hN' hd E.zero_mem (hf.2 γ)
  have h2 : QAll (· ∈ E) N' fun τ => DD τ ^ (w' - w) :=
    QAllSubring.pow (w' - w) (eis_qAll N' hN' DD (Or.inr (Or.inr rfl)) E)
  have h3 := QAllSubring.mul h2 h1
  refine (congrArg (QAll (· ∈ E) N') (funext fun τ => ?_)).mp h3
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hw]

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaLeOfDvdStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lv_mono_of_dvd_of_le : ∀ (E : Subring ℂ) (N N' w w' : ℕ) (f : ℍ → ℂ), 0 < N' → N ∣ N' → w ≤ w' → Lv E N w f → Lv E N' w' f := by
  first | exact @GlobalTheory.FN.lv_mono | exact GlobalTheory.FN.lv_mono | (intros; apply GlobalTheory.FN.lv_mono <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerNeZero
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ

theorem codiscreteWithin_Hs_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  exact @_root_.GlobalTheory.KZ.SiegelSL.neBot_Hs

theorem siegel_ne_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (x : Fin 2 → ℚ), GlobalTheory.Sieg.admitted c x → siegel T c x ≠ 0 := by
  intro Ω _ _ _ ε T c x hx h0
  have han := GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hx
  rw [h0, map_zero] at han
  have hev : (fun z => sgC c x z) =ᶠ[Filter.codiscreteWithin Hs] (fun _ => (0 : ℂ)) :=
    (Filter.Germ.coe_eq.1 han.symm)
  have hne : ∀ᶠ z in Filter.codiscreteWithin Hs, sgC c x z ≠ 0 := by
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
    have hz' : 0 < z.im := hz
    simp only [sgC, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    exact sg_ne_zero c x _ hx
  haveI := codiscreteWithin_Hs_neBot
  obtain ⟨z, h1, h2⟩ := (hev.and hne).exists
  exact h2 h1

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerNeZeroStatement
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelUnitInTower_ne_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ), GlobalTheory.Sieg.admitted c x → siegel T c x ≠ 0 := by
  first | exact @GlobalTheory.KZ.siegel_ne_zero | exact GlobalTheory.KZ.siegel_ne_zero | (intros; apply GlobalTheory.KZ.siegel_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumRepSubgroupEqZero
noncomputable section

namespace GlobalTheory.NoFixedCharSum

theorem sum_rep_subgroup_eq_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ G V) (N : Subgroup G) [Fintype N]
    (h : ∀ v : V, (∀ n ∈ N, τ n v = v) → v = 0) : ∑ n : N, τ (n : G) = 0 := by
  ext v
  simp only [LinearMap.sum_apply, LinearMap.zero_apply]
  apply h
  intro m hm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨m, hm⟩ : N)) _ _ ?_
  intro n
  simp [map_mul]

theorem noFixedSum : Formalism.PacketSums.NoFixedSum := by
  intro G V _ _ _ _ τ N _ h x y
  have h0 := sum_rep_subgroup_eq_zero τ N h
  have : ∑ n : N, τ (x * (n : G) * y) = τ x * (∑ n : N, τ (n : G)) * τ y := by
    simp [Finset.mul_sum, Finset.sum_mul, map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, this, h0]
  simp

end GlobalTheory.NoFixedCharSum
end
end
