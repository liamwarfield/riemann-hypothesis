module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LaurentBlockInduction.LdDefs

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaIntegralLaurentExpansion
noncomputable section

open MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem UpperTheory.local_zeta_integral_laurent_expansion :
    UpperTheory.V.Z.Gam.LdLaurent := by
  intro F _ _ _ _ m _ _ _ μ _ α c hc hzero Φ hΦ
  obtain ⟨A, hA⟩ := hΦ.exists_ordDet_ge
  obtain ⟨K, hK, hKc⟩ := hc.exists_compact_tile
  obtain ⟨B, hB⟩ := exists_valBall_of_isCompact (hK.image Units.continuous_val)
  obtain ⟨J, hJ⟩ := hΦ.exists_eq_zero_of_small B
  have hm : (0 : ℤ) < m := by
    have := NeZero.pos m
    omega
  let sh : ℤ → Set (GL (Fin m) F) := fun k => {g | ordDet g = k}
  refine ⟨Finset.Icc (-((m : ℤ) * A)) (J * m), fun k => ∫ g in sh k, Φ g * c g ∂μ, ?_⟩
  intro s hs
  have hint := hc.integrable_zeta μ hΦ hs
  have hmeas : ∀ k, MeasurableSet (sh k) := fun k => (isClopen_shell F m k).isClosed.measurableSet
  have hdisj : Pairwise (fun i j => Disjoint (sh i) (sh j)) := by
    intro i j hij
    exact Set.disjoint_left.2 fun g hi hj => hij (hi.symm.trans hj)
  have huniv : (⋃ k, sh k) = Set.univ := Set.iUnion_eq_univ_iff.2 fun g => ⟨ordDet g, rfl⟩
  have hsplit := integral_iUnion hmeas hdisj hint.integrableOn
  rw [huniv, setIntegral_univ] at hsplit
  rw [hsplit]
  have hshell : ∀ k, ∫ g in sh k, Φ g * detPow g s * c g ∂μ = (∫ g in sh k, Φ g * c g ∂μ) * qs F s ^ k := by
    intro k
    rw [← integral_mul_const]
    refine setIntegral_congr_fun (hmeas k) fun g hg => ?_
    have hg' : ordDet g = k := hg
    rw [detPow_eq_qs_zpow, hg']
    ring
  simp_rw [hshell]
  apply tsum_eq_sum
  intro k hk
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  have hk0 : ∫ g in sh k, Φ g * c g ∂μ = 0 := by
    rcases hk with hk | hk
    · apply setIntegral_eq_zero_of_forall_eq_zero
      intro g hg
      have hg' : ordDet g = k := hg
      have hΦ0 : Φ g = 0 := by
        by_contra hne
        have := hA g hne
        linarith
      rw [hΦ0, zero_mul]
    · have hcongr : ∫ g in sh k, Φ g * c g ∂μ = ∫ g in sh k, Φ 0 * c g ∂μ := by
        refine setIntegral_congr_fun (hmeas k) fun g hg => ?_
        have hg' : ordDet g = k := hg
        by_cases hcg : c g = 0
        · simp [hcg]
        · congr 1
          have hgh : centralUnif F m ^ (k / (m : ℤ)) * (centralUnif F m ^ (-(k / (m : ℤ))) * g) = g := by
            rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
          have hordh : ordDet (centralUnif F m ^ (-(k / (m : ℤ))) * g) = k % m := by
            rw [ordDet_centralUnif_zpow_mul, hg', Int.emod_def]
            ring
          have htile : centralUnif F m ^ (-(k / (m : ℤ))) * g ∈ tile F m 0 := by
            simp only [tile, Set.mem_setOf_eq, zero_mul, zero_add]
            rw [hordh]
            exact ⟨Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm⟩
          have hch : c (centralUnif F m ^ (-(k / (m : ℤ))) * g) ≠ 0 := by
            rw [← hgh, hc.zpow_mul] at hcg
            exact right_ne_zero_of_mul hcg
          have hhK := hKc _ htile hch
          have hball := hB _ ⟨_, hhK, rfl⟩
          have hjJ : J ≤ k / (m : ℤ) := Int.le_ediv_of_mul_le hm hk.le
          rw [← hgh]
          exact hJ _ hjJ _ hball
      rw [hcongr, integral_const_mul, hzero k, mul_zero]
  rw [hk0, zero_mul]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaIntegralTateComparison
noncomputable section

open MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem integral_iff_one (g : GL (Fin 1) F) :
    (∀ i j, (g : Matrix (Fin 1) (Fin 1) F) i j ∈ 𝒪[F]) ↔ 0 ≤ ordDet g := by
  constructor
  · exact ordDet_nonneg_of_integral
  · intro h i j
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
    have hne : (g : Matrix (Fin 1) (Fin 1) F) 0 0 ≠ 0 := by
      simpa [Matrix.det_unique] using det_ne_zero g
    rw [← GroundTheory.LocalField.mem_valBall_zero_iff, GroundTheory.LocalField.mem_valBall_iff_le_ord hne]
    simpa [ordDet, Matrix.det_unique] using h

private theorem mem_tile_one (g : GL (Fin 1) F) : g ∈ tile F 1 0 ↔ ordDet g = 0 := by
  simp only [tile, Set.mem_ofPred_eq]
  push_cast
  omega

private theorem int_of_tile {g : GL (Fin 1) F} (hg : g ∈ tile F 1 0) : g ∈ integralGL F 1 := by
  have h0 := (mem_tile_one g).1 hg
  rw [mem_integralGL_iff]
  refine ⟨(integral_iff_one g).2 (by omega), (integral_iff_one g⁻¹).2 ?_⟩
  rw [ordDet_inv]
  omega

private theorem isCompact_tile_one : IsCompact (tile F 1 0) := by
  have h := isCompact_shell F 1 0 0
  convert h using 1
  ext g
  simp only [Set.mem_ofPred_eq, pow_zero, one_mul, mem_tile_one]
  exact ⟨fun h0 => ⟨(integral_iff_one g).2 h0.ge, h0⟩, fun h => h.2⟩

end SlopeTestRemainingChoices

theorem UpperTheory.local_zeta_integral_tate_comparison :
    UpperTheory.V.Z.Gam.LdTate := by
  intro F _ _ _ _ _ _ μ _
  refine ⟨integralIndicator F 1, isSchwartzBruhat_integralIndicator, ((μ.real (tile F 1 0) : ℝ) : ℂ), ?_, ?_⟩
  · have hpos : 0 < μ (tile F 1 0) := (isOpen_tile 0).measure_pos μ ⟨1, (mem_tile_one 1).2 ordDet_one⟩
    have hfin : μ (tile F 1 0) < ⊤ := isCompact_tile_one.measure_lt_top
    show (((μ (tile F 1 0)).toReal : ℝ) : ℂ) ≠ 0
    exact_mod_cast (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  · intro α c hc hcK s hs
    have hs1 : ‖α * qs F s‖ < 1 := by simpa using hs
    have hint := hc.integrable_zeta μ (isSchwartzBruhat_integralIndicator (F := F) (n := 1)) hs
    have h1 := hasSum_integral_tile μ hint
    have hterm : ∀ j : ℤ, (∫ g in tile F 1 0, integralIndicator F 1 ↑(centralUnif F 1 ^ j * g) *
        detPow (centralUnif F 1 ^ j * g) s * c (centralUnif F 1 ^ j * g) ∂μ) =
        if 0 ≤ j then (α * qs F s) ^ j * c 1 * ((μ.real (tile F 1 0) : ℝ) : ℂ) else 0 := by
      intro j
      have hEq : Set.EqOn (fun g => integralIndicator F 1 ↑(centralUnif F 1 ^ j * g) *
          detPow (centralUnif F 1 ^ j * g) s * c (centralUnif F 1 ^ j * g))
          (fun _ => if 0 ≤ j then (α * qs F s) ^ j * c 1 else 0) (tile F 1 0) := by
        intro g hg
        have hgK := int_of_tile hg
        have h0 := (mem_tile_one g).1 hg
        have hiff : ((↑(centralUnif F 1 ^ j * g) : Matrix (Fin 1) (Fin 1) F) ∈ integralMatrixSet F 1) ↔ 0 ≤ j := by
          rw [mem_integralMatrixSet, integral_iff_one, ordDet_centralUnif_zpow_mul, h0]
          push_cast
          omega
        have hind : integralIndicator F 1 ↑(centralUnif F 1 ^ j * g) = if 0 ≤ j then 1 else 0 := by
          unfold integralIndicator
          by_cases hj : 0 ≤ j
          · rw [Set.indicator_of_mem (hiff.2 hj), if_pos hj]
            rfl
          · rw [Set.indicator_of_notMem (fun h => hj (hiff.1 h)), if_neg hj]
        simp only
        rw [hind, detPow_centralUnif_zpow_mul, detPow_of_mem_integralGL hgK, hc.zpow_mul, hcK g hgK]
        split_ifs
        · push_cast
          rw [mul_one, mul_zpow]
          ring_nf
        · simp
      rw [setIntegral_congr_fun (measurableSet_tile 0) hEq, setIntegral_const, Complex.real_smul]
      split_ifs <;> ring
    have h2 := h1
    simp only [hterm] at h2
    have hgeo : HasSum (fun j : ℤ => if 0 ≤ j then (α * qs F s) ^ j * c 1 * ((μ.real (tile F 1 0) : ℝ) : ℂ) else 0)
        ((1 - α * qs F s)⁻¹ * (c 1 * ((μ.real (tile F 1 0) : ℝ) : ℂ))) := by
      have hn := (hasSum_geometric_of_norm_lt_one hs1).mul_right (c 1 * ((μ.real (tile F 1 0) : ℝ) : ℂ))
      rw [← Nat.cast_injective.hasSum_iff]
      · simpa [Function.comp_def, zpow_natCast, mul_assoc] using hn
      · intro j hj
        have hn' : ¬ 0 ≤ j := fun h => hj ⟨j.toNat, Int.toNat_of_nonneg h⟩
        simp [hn']
    rw [h2.unique hgeo, div_eq_mul_inv]
    ring
end
end
