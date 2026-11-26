module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxFrobeniusOrbitLengthDiffBoundsZmod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticUniformizerTraceNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticUniformizerTraceNorm
open ValuativeRel

namespace GlobalTheory


open GroundTheory.LocalField IsLocalRing in
theorem unramified_quadratic_uniformizer_trace_norm : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L], (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 → Module.finrank K L = 2 → ∃ ϖ : K, ϖ ≠ 0 ∧ ϖ ≤ᵥ 1 ∧ ¬ (1 : K) ≤ᵥ ϖ ∧ (¬ ∃ y : L, Algebra.norm K y = ϖ) ∧ (∀ y : L, y ≤ᵥ 1 → (∃ z : L, z ≤ᵥ 1 ∧ y = algebraMap K L ϖ * z) ∨ ∃ z : L, z ≤ᵥ 1 ∧ y * z = 1) ∧ (∀ s : K, s ≤ᵥ 1 → ∃ z : L, z ≤ᵥ 1 ∧ Algebra.trace K L z = s) ∧ ∀ s : K, s ≤ᵥ 1 → 1 ≤ᵥ s → ∃ w : L, w ≤ᵥ 1 ∧ Algebra.norm K w = s := by
  open GroundTheory.LocalField IsLocalRing in
  intro K L _ _ _ _ _ _ _ _ _ _ _ he h2
  haveI : IsUnramified K L := ⟨he⟩
  have memK : ∀ x : K, x ∈ 𝒪[K] ↔ x ≤ᵥ 1 := fun x ↦ by
    rw [Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation K), ← Valuation.vle_iff_le]
  have memL : ∀ x : L, x ∈ 𝒪[L] ↔ x ≤ᵥ 1 := fun x ↦ by
    rw [Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation L), ← Valuation.vle_iff_le]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  refine ⟨(ϖ : K), hϖ0, (memK _).1 ϖ.2, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro h1
    have hv : ValuativeRel.valuation K (ϖ : K) = 1 :=
      le_antisymm ((Valuation.vle_iff_le _).1 ((memK _).1 ϖ.2) |>.trans_eq (map_one _))
        ((map_one (ValuativeRel.valuation K)).symm.trans_le ((Valuation.vle_iff_le _).1 h1))
    exact hϖ.not_isUnit ((Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 hv)
  ·
    rintro ⟨y, hy⟩
    have h := ord_norm (K := K) y
    rw [hy, ord_uniformizer hϖ, IsUnramified.residueDegree_eq_finrank K L, h2] at h
    omega
  ·
    intro y hy
    have hπ := irreducible_algebraMap_of_isUnramified (L := L) hϖ
    set y' : 𝒪[L] := ⟨y, (memL y).2 hy⟩
    by_cases hu : IsUnit y'
    · right
      refine ⟨((hu.unit⁻¹ : 𝒪[L]ˣ) : 𝒪[L]), (memL _).1 (hu.unit⁻¹ : 𝒪[L]ˣ).1.2, ?_⟩
      have h := hu.unit.mul_inv
      rw [IsUnit.unit_spec] at h
      have := congrArg (fun u : 𝒪[L] ↦ (u : L)) h
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
      exact this
    · left
      have hm : y' ∈ maximalIdeal 𝒪[L] := (mem_maximalIdeal y').2 hu
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
      obtain ⟨c, hc⟩ := hm
      refine ⟨(c : L), (memL _).1 c.2, ?_⟩
      have := congrArg (fun u : 𝒪[L] ↦ (u : L)) hc
      simp only [y', MulMemClass.coe_mul, coe_algebraMap_integer] at this
      exact this
  ·
    intro s hs
    obtain ⟨a, ha⟩ := trace_integer_surjective (K := K) (L := L) ⟨s, (memK s).2 hs⟩
    refine ⟨(a : L), (memL _).1 a.2, ?_⟩
    rw [← coe_trace_integer, ha]
  ·
    intro s hs1 hs2
    set s' : 𝒪[K] := ⟨s, (memK s).2 hs1⟩
    have hv : ValuativeRel.valuation K s = 1 :=
      le_antisymm ((Valuation.vle_iff_le _).1 hs1 |>.trans_eq (map_one _))
        ((map_one (ValuativeRel.valuation K)).symm.trans_le ((Valuation.vle_iff_le _).1 hs2))
    have hu : IsUnit s' := (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 hv
    obtain ⟨w, hw⟩ := normIntegerUnits_surjective (K := K) (L := L) hu.unit
    refine ⟨((w : 𝒪[L]) : L), (memL _).1 (w : 𝒪[L]).2, ?_⟩
    have := congrArg (fun u : 𝒪[K]ˣ ↦ ((u : 𝒪[K]) : K)) hw
    simp only [coe_normIntegerUnits_eq, IsUnit.unit_spec] at this
    rw [← coe_norm_integer]
    exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticUniformizerTraceNormStatement
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_norm_trace_surjective : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L], (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 → Module.finrank K L = 2 → ∃ ϖ : K, ϖ ≠ 0 ∧ ϖ ≤ᵥ 1 ∧ ¬ (1 : K) ≤ᵥ ϖ ∧ (¬ ∃ y : L, Algebra.norm K y = ϖ) ∧ (∀ y : L, y ≤ᵥ 1 → (∃ z : L, z ≤ᵥ 1 ∧ y = algebraMap K L ϖ * z) ∨ ∃ z : L, z ≤ᵥ 1 ∧ y * z = 1) ∧ (∀ s : K, s ≤ᵥ 1 → ∃ z : L, z ≤ᵥ 1 ∧ Algebra.trace K L z = s) ∧ ∀ s : K, s ≤ᵥ 1 → 1 ≤ᵥ s → ∃ w : L, w ≤ᵥ 1 ∧ Algebra.norm K w = s := by
  first | exact @GlobalTheory.unramified_quadratic_uniformizer_trace_norm | exact GlobalTheory.unramified_quadratic_uniformizer_trace_norm | (intros; apply GlobalTheory.unramified_quadratic_uniformizer_trace_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationIndexEqOneOfAdjoinRangeEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationIndexEqOneOfAdjoinRangeEqTop
open ValuativeRel

namespace GlobalTheory

open GroundTheory.LocalField IntermediateField

theorem ramificationIndex_eq_one_of_adjoin_range_eq_top (F E K L : Type) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E]
    [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F E] [Algebra F K] [Algebra F L]
    [Algebra K L] [Algebra E L] [IsScalarTower F K L] [IsScalarTower F E L]
    [ValuativeExtension F E] [ValuativeExtension F K] [ValuativeExtension K L]
    [FiniteDimensional F E] [FiniteDimensional K L] :
    (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) = 1 →
      Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ →
        (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 := by
  intro he hadj
  obtain ⟨ζ, hζ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified F E he
  set m := Nat.card 𝓀[E] - 1 with hm_def
  have hmE : (m : 𝓀[E]) ≠ 0 := natCast_card_residueField_sub_one_ne_zero E
  have hmF : (m : 𝓀[F]) ≠ 0 := fun h0 ↦ hmE (by rw [← map_natCast (algebraMap 𝓀[F] 𝓀[E]), h0, map_zero])
  have hmK : (m : 𝓀[K]) ≠ 0 := fun h0 ↦ hmF ((algebraMap 𝓀[F] 𝓀[K]).injective (by rw [map_natCast, h0, map_zero]))
  have hζ' : IsPrimitiveRoot (algebraMap E L ζ) m := hζ.map_of_injective (algebraMap E L).injective
  have hE : Set.range (algebraMap E L) ⊆ Algebra.adjoin K {algebraMap E L ζ} := by
    rintro _ ⟨e, rfl⟩
    have he' : e ∈ Algebra.adjoin F {ζ} := by
      rw [algebra_adjoin_eq_top_of_adjoin_eq_top htop]; trivial
    have h1 : algebraMap E L e ∈ (Algebra.adjoin F {ζ}).map (IsScalarTower.toAlgHom F E L) :=
      ⟨e, he', rfl⟩
    rw [AlgHom.map_adjoin, Set.image_singleton] at h1
    have h2 : Algebra.adjoin F {(IsScalarTower.toAlgHom F E L) ζ} ≤
        (Algebra.adjoin K {algebraMap E L ζ}).restrictScalars F :=
      Algebra.adjoin_le (by simpa using Algebra.subset_adjoin (R := K) (s := {algebraMap E L ζ}))
    exact h2 h1
  have hadjK : Algebra.adjoin K {algebraMap E L ζ} = ⊤ := by
    rw [eq_top_iff, ← hadj]
    exact Algebra.adjoin_le hE
  have htopK : K⟮algebraMap E L ζ⟯ = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff (F := K) (E := L)).mpr hadjK
  exact ramificationIndex_eq_one_of_adjoin_eq_top hζ' hmK htopK

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationIndexEqOneOfAdjoinRangeEqTopStatement
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationIndex_eq_one_of_adjoin_range_eq_top_alt : ∀ (F E K L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F E] [Algebra F K] [Algebra F L] [Algebra K L] [Algebra E L] [IsScalarTower F K L] [IsScalarTower F E L] [ValuativeExtension F E] [ValuativeExtension F K] [ValuativeExtension K L] [FiniteDimensional F E] [FiniteDimensional K L], (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) = 1 → Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ → (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 := by
  first | exact @GlobalTheory.ramificationIndex_eq_one_of_adjoin_range_eq_top | exact GlobalTheory.ramificationIndex_eq_one_of_adjoin_range_eq_top | (intros; apply GlobalTheory.ramificationIndex_eq_one_of_adjoin_range_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpectralNormClosedBallIsOpenIsCompactNhdsBasisAl
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpectralNormClosedBallIsOpenIsCompactNhdsBasisAl
open Filter Topology

namespace GlobalTheory

theorem spectralNorm_closedBall_isOpen_isCompact_nhds_basis : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [LocallyCompactSpace F] (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [TopologicalSpace L] [IsModuleTopology F L], IsOpen {y : L | spectralNorm F L y ≤ 1} ∧ IsCompact {y : L | spectralNorm F L y ≤ 1} ∧ ∀ U ∈ 𝓝 (0 : L), ∃ r : ℝ, 0 < r ∧ ∀ y : L, spectralNorm F L y < r → y ∈ U := by
  intro F _ _ _ _ L _ _ _ τ _
  have hcs : ContinuousSMul F L := IsModuleTopology.toContinuousSMul F L
  have hca : ContinuousAdd L := IsModuleTopology.toContinuousAdd F L
  have htg : IsTopologicalAddGroup L :=
    { continuous_neg := by
        have : (fun x : L => -x) = fun x => (-1 : F) • x := by funext x; simp
        rw [this]; exact continuous_const.smul continuous_id }
  let N : NormedAddCommGroup L := spectralNorm.normedAddCommGroup F L
  let NS : NormedSpace F L := spectralNorm.normedSpace F L
  let τ' : TopologicalSpace L := N.toUniformSpace.toTopologicalSpace
  have h1 : τ ≤ τ' := by
    rw [← continuous_id_iff_le]
    exact @IsModuleTopology.continuous_of_linearMap F _ _ L _ _ τ _ L _ _ τ' inferInstance inferInstance LinearMap.id
  have h2 : τ' ≤ τ := by
    rw [← continuous_id_iff_le]
    exact @LinearMap.continuous_of_finiteDimensional F _ L _ _ τ' inferInstance inferInstance L _ _ τ htg hcs _ inferInstance _ (LinearMap.id)
  have hτ : τ = τ' := le_antisymm h1 h2
  subst hτ
  have hU : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (isNonarchimedean_spectralNorm (K := F) (L := L))
  have hPF : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have hPL : ProperSpace L := FiniteDimensional.proper F L
  have hd : ∀ y : L, dist y 0 = spectralNorm F L y := fun y => by
    rw [dist_zero_right]; rfl
  have hS : {y : L | spectralNorm F L y ≤ 1} = Metric.closedBall (0 : L) 1 := by
    ext y; simp only [Set.mem_setOf_eq, Metric.mem_closedBall, hd]
  refine ⟨?_, ?_, ?_⟩
  · rw [hS]; exact IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  · rw [hS]; exact isCompact_closedBall _ _
  · intro U hU0
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hU0
    exact ⟨ε, hε, fun y hy => hb (by rw [Metric.mem_ball, hd]; exact hy)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpectralNormClosedBallIsOpenIsCompactNhdsBasisAlStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spectralNorm_closedBall_isOpen_isCompact_nhds : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [LocallyCompactSpace F] (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [TopologicalSpace L] [IsModuleTopology F L], IsOpen {y : L | spectralNorm F L y ≤ 1} ∧ IsCompact {y : L | spectralNorm F L y ≤ 1} ∧ ∀ U ∈ 𝓝 (0 : L), ∃ r : ℝ, 0 < r ∧ ∀ y : L, spectralNorm F L y < r → y ∈ U := by
  first | exact @GlobalTheory.spectralNorm_closedBall_isOpen_isCompact_nhds_basis | exact GlobalTheory.spectralNorm_closedBall_isOpen_isCompact_nhds_basis | (intros; apply GlobalTheory.spectralNorm_closedBall_isOpen_isCompact_nhds_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsNonarchimedeanLocalFieldSpectralNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsNonarchimedeanLocalFieldSpectralNorm
open ValuativeRel

namespace GlobalTheory

theorem exists_isNonarchimedeanLocalField_spectralNorm :
    ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
      [LocallyCompactSpace F] (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K],
      ∃ (_ : ValuativeRel K) (_ : TopologicalSpace K), IsNonarchimedeanLocalField K ∧
        ∀ x y : K, x ≤ᵥ y ↔ spectralNorm F K x ≤ spectralNorm F K y := by
  intro F _ _ _ _ K _ _ _
  letI nK : NontriviallyNormedField K := spectralNorm.nontriviallyNormedField F K
  haveI : IsUltrametricDist K := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := F) (L := K))
  letI rel : ValuativeRel K := ValuativeRel.ofValuation (NormedField.valuation (K := K))
  refine ⟨rel, inferInstance, ?_, fun x y => Iff.rfl⟩
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have hc : (NormedField.valuation (K := K)).Compatible := Valuation.Compatible.ofValuation _
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := ?_, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := K))
      (fun {s} => (NormedField.toValued (K := K)).is_topological_valuation s)
  · letI : NormedSpace F K := spectralNorm.normedSpace F K
    haveI : ProperSpace K := FiniteDimensional.proper F K
    infer_instance
  · rw [isNontrivial_iff_isNontrivial (NormedField.valuation (K := K))]
    infer_instance

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsNonarchimedeanLocalFieldSpectralNormStatement
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localField_structure_spectralNorm : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [LocallyCompactSpace F] (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K], ∃ (_ : ValuativeRel K) (_ : TopologicalSpace K), IsNonarchimedeanLocalField K ∧ ∀ x y : K, x ≤ᵥ y ↔ spectralNorm F K x ≤ spectralNorm F K y := by
  first | exact @GlobalTheory.exists_isNonarchimedeanLocalField_spectralNorm | exact GlobalTheory.exists_isNonarchimedeanLocalField_spectralNorm | (intros; apply GlobalTheory.exists_isNonarchimedeanLocalField_spectralNorm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticExistsIntegersUniformiser
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.UnramInt
open ValuativeRel GroundTheory.LocalField

theorem alg_main : ∀ (F E K L : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    [LocallyCompactSpace F] [NontriviallyNormedField E] [NormedAlgebra F E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [Field K] [Field L] [Algebra F K] [Algebra F L] [Algebra K L] [Algebra E L]
    [IsScalarTower F K L] [IsScalarTower F E L] [FiniteDimensional F K] [FiniteDimensional F E]
    [FiniteDimensional K L],
    (∀ y : E, ∃ x : F, ‖y‖ = ‖x‖) → Module.finrank K L = 2 →
    Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ →
    ∃ (ϖ : Kˣ) (O : Subring L), (O : Set L) = {y | spectralNorm F L y ≤ 1} ∧
      (¬ ∃ y : L, Algebra.norm K y = (ϖ : K)) ∧ algebraMap K L (ϖ : K) ∈ O ∧
      (¬ ∃ z ∈ O, algebraMap K L (ϖ : K) * z = 1) ∧
      (∀ y ∈ O, (∃ z ∈ O, y = algebraMap K L (ϖ : K) * z) ∨ ∃ z ∈ O, y * z = 1) ∧
      (∀ s : K, algebraMap K L s ∈ O → ∃ z ∈ O, Algebra.trace K L z = s) ∧
      (∀ s : K, algebraMap K L s ∈ O → (∃ r ∈ O, algebraMap K L s * r = 1) → ∃ w ∈ O, Algebra.norm K w = s) ∧
      (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∀ z ∈ O, spectralNorm F L (algebraMap K L ((ϖ : K) ^ n) * z) < r) ∧
      ∀ y : L, ∃ n : ℕ, algebraMap K L ((ϖ : K) ^ n) * y ∈ O := by
  intro F E K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hunr h2 hgen
  haveI : FiniteDimensional F L := Module.Finite.trans K L
  have nmulL : ∀ x y : L, spectralNorm F L (x * y) = spectralNorm F L x * spectralNorm F L y :=
    fun x y => map_mul (spectralMulAlgNorm F L) x y
  have npowK : ∀ (x : K) (n : ℕ), spectralNorm F K (x ^ n) = spectralNorm F K x ^ n :=
    fun x n => map_pow (spectralMulAlgNorm F K) x n
  have ntow : ∀ a : K, spectralNorm F L (algebraMap K L a) = spectralNorm F K a :=
    fun a => (spectralNorm.eq_of_tower a).symm
  obtain ⟨vF, hFloc, hFv⟩ := NormSign.exists_valuativeRel_of_normed F
  obtain ⟨vE, hEloc, hEv⟩ := NormSign.exists_valuativeRel_of_normed E
  obtain ⟨vK, tK, hKloc, hKv⟩ := GlobalTheory.T.exists_localField_structure_spectralNorm F K
  obtain ⟨vL, tL, hLloc, hLv⟩ := GlobalTheory.T.exists_localField_structure_spectralNorm F L
  haveI : ValuativeExtension F E := ⟨fun {a b} => by rw [hEv, hFv, norm_algebraMap', norm_algebraMap']⟩
  haveI : ValuativeExtension F K := ⟨fun {a b} => by
    rw [hKv, hFv, spectralNorm_extends, spectralNorm_extends]⟩
  haveI : ValuativeExtension K L := ⟨fun {a b} => by rw [hLv, hKv, ntow, ntow]⟩
  have heF : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) = 1 := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
    obtain ⟨x, hx⟩ := hunr (ϖ : E)
    have h1 : (ϖ : E) ≤ᵥ algebraMap F E x := by rw [hEv, norm_algebraMap', hx]
    have h2 : algebraMap F E x ≤ᵥ (ϖ : E) := by rw [hEv, norm_algebraMap', hx]
    have hv : valuation E (ϖ : E) = valuation E (algebraMap F E x) :=
      le_antisymm ((Valuation.Compatible.vle_iff_le _ _).1 h1) ((Valuation.Compatible.vle_iff_le _ _).1 h2)
    have hord : ord (ϖ : E) = ord (algebraMap F E x) := by
      simp only [ord]
      rw [(normalizedValuation_eq_iff (K := E)).2 hv]
    rw [ord_uniformizer hϖ, ord_algebraMap] at hord
    have hd : (((_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) : ℕ) : ℤ) ∣ 1 := ⟨ord x, hord⟩
    exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hd
  have heKL := GlobalTheory.T.ramificationIndex_eq_one_of_adjoin_range_eq_top_alt F E K L heF hgen
  obtain ⟨ϖ, hϖ0, hϖ1, hϖ1', hN, hunif, htr, hnrm⟩ := GlobalTheory.T.unramified_quadratic_norm_trace_surjective K L heKL h2
  have hleL : ∀ y : L, y ≤ᵥ 1 ↔ spectralNorm F L y ≤ 1 := fun y => by rw [hLv, spectralNorm_one]
  have hleK : ∀ s : K, s ≤ᵥ 1 ↔ spectralNorm F K s ≤ 1 := fun s => by rw [hKv, spectralNorm_one]
  have hgeK : ∀ s : K, (1 : K) ≤ᵥ s ↔ 1 ≤ spectralNorm F K s := fun s => by rw [hKv, spectralNorm_one]
  have hϖlt : spectralNorm F K ϖ < 1 := lt_of_not_ge fun h => hϖ1' ((hgeK ϖ).2 h)
  let O : Subring L :=
    { carrier := {y | spectralNorm F L y ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [nmulL]
        exact mul_le_one₀ ha (spectralNorm_nonneg _) hb
      one_mem' := by simp [spectralNorm_one]
      add_mem' := fun {a b} ha hb => (isNonarchimedean_spectralNorm a b).trans (max_le ha hb)
      zero_mem' := by simp [spectralNorm_zero]
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        rwa [spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic a)] }
  have hmem : ∀ y : L, y ∈ O ↔ y ≤ᵥ 1 := fun y => (hleL y).symm
  refine ⟨Units.mk0 ϖ hϖ0, O, rfl, hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show spectralNorm F L _ ≤ 1
    rw [Units.val_mk0, ntow]
    exact hϖlt.le
  · rintro ⟨z, hz, hz1⟩
    have h := congrArg (spectralNorm F L) hz1
    rw [nmulL, spectralNorm_one, Units.val_mk0, ntow] at h
    have hz' : spectralNorm F L z ≤ 1 := hz
    have : spectralNorm F K ϖ * spectralNorm F L z < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (spectralNorm_nonneg _) hz') hϖlt
    linarith
  · intro y hy
    rcases hunif y ((hmem y).1 hy) with ⟨z, hz, hyz⟩ | ⟨z, hz, hyz⟩
    · exact Or.inl ⟨z, (hmem z).2 hz, by rw [Units.val_mk0]; exact hyz⟩
    · exact Or.inr ⟨z, (hmem z).2 hz, hyz⟩
  · intro s hs
    have hs' : s ≤ᵥ 1 := by
      rw [hleK, ← ntow]
      exact hs
    obtain ⟨z, hz, hzs⟩ := htr s hs'
    exact ⟨z, (hmem z).2 hz, hzs⟩
  · rintro s hs ⟨r, hr, hsr⟩
    have hs1 : spectralNorm F K s ≤ 1 := by rw [← ntow]; exact hs
    have hr1 : spectralNorm F L r ≤ 1 := hr
    have h := congrArg (spectralNorm F L) hsr
    rw [nmulL, spectralNorm_one, ntow] at h
    have hge : 1 ≤ spectralNorm F K s := by
      nlinarith [spectralNorm_nonneg (K := F) s, spectralNorm_nonneg (K := F) r]
    obtain ⟨w, hw, hws⟩ := hnrm s ((hleK s).2 hs1) ((hgeK s).2 hge)
    exact ⟨w, (hmem w).2 hw, hws⟩
  · intro r hr
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr hϖlt
    refine ⟨n, fun z hz => ?_⟩
    have hz' : spectralNorm F L z ≤ 1 := hz
    rw [nmulL, ntow, Units.val_mk0, npowK]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (pow_nonneg (spectralNorm_nonneg _) _) hz') hn
  · intro y
    by_cases hy : spectralNorm F L y ≤ 1
    · refine ⟨0, ?_⟩
      show spectralNorm F L _ ≤ 1
      simpa using hy
    · have hpos : 0 < spectralNorm F L y := lt_of_lt_of_le one_pos (le_of_not_ge hy)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hpos) hϖlt
      refine ⟨n, ?_⟩
      show spectralNorm F L _ ≤ 1
      rw [nmulL, ntow, Units.val_mk0, npowK]
      calc spectralNorm F K ϖ ^ n * spectralNorm F L y ≤ (spectralNorm F L y)⁻¹ * spectralNorm F L y :=
            mul_le_mul_of_nonneg_right hn.le (spectralNorm_nonneg _)
        _ = 1 := inv_mul_cancel₀ hpos.ne'

end GlobalTheory.JR.UnramInt

namespace GlobalTheory.JR.UnramInt

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∃ (ϖ : A.Kˣ) (O : Subring A.L), IsOpen (O : Set A.L) ∧ IsCompact (O : Set A.L) ∧ (∀ y ∈ O, star y ∈ O) ∧ (¬ ∃ y, A.NL y = (ϖ : A.K)) ∧ algebraMap A.K A.L (ϖ : A.K) ∈ O ∧ (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) ∧ (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) ∧ (∀ s : A.K, algebraMap A.K A.L s ∈ O → ∃ z ∈ O, Algebra.trace A.K A.L z = s) ∧ (∀ s : A.K, algebraMap A.K A.L s ∈ O → (∃ r ∈ O, algebraMap A.K A.L s * r = 1) → ∃ w ∈ O, A.NL w = s) ∧ (∀ U ∈ 𝓝 (0 : A.L), ∃ n : ℕ, ∀ z ∈ O, algebraMap A.K A.L ((ϖ : A.K) ^ n) * z ∈ U) ∧ ∀ y : A.L, ∃ n : ℕ, algebraMap A.K A.L ((ϖ : A.K) ^ n) * y ∈ O := by
  intro F E _ _ _ _ U A hK hL
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  haveI := U.ultraF
  haveI := U.ultraE
  haveI := U.lcF
  haveI := U.lcE
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : CompleteSpace F := complete_of_proper
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ U.finrank_eq
  have hKL : Module.finrank A.K A.L = 2 := by
    haveI := A.push.symm
    rw [← (Algebra.IsPushout.equiv F A.K E A.L).toLinearEquiv.finrank_eq, Module.finrank_baseChange,
      U.finrank_eq]
  haveI : FiniteDimensional A.K A.L := Module.finite_of_finrank_eq_succ hKL
  haveI : FiniteDimensional F A.L := Module.Finite.trans A.K A.L
  have hgen : Algebra.adjoin A.K (Set.range (algebraMap E A.L)) = ⊤ := by
    haveI := A.push.symm
    rw [eq_top_iff]
    intro y _
    obtain ⟨t, rfl⟩ := (Algebra.IsPushout.equiv F A.K E A.L).surjective y
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul k e =>
      rw [Algebra.IsPushout.equiv_tmul]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ k) (Algebra.subset_adjoin ⟨e, rfl⟩)
    | add a b ha hb =>
      rw [map_add (f := _)]
      exact Subalgebra.add_mem _ (ha trivial) (hb trivial)
  obtain ⟨ϖ, O, hO, hN, hϖO, hϖu, hunif, htr, hnrm, hsmall, hbig⟩ :=
    alg_main F E A.K A.L (fun y => U.unram y) hKL hgen
  obtain ⟨hop, hcp, hball⟩ := GlobalTheory.T.spectralNorm_closedBall_isOpen_isCompact_nhds F A.L
  have hmem : ∀ y : A.L, y ∈ O ↔ spectralNorm F A.L y ≤ 1 := fun y => by
    rw [← SetLike.mem_coe, hO]
    rfl
  refine ⟨ϖ, O, by rw [hO]; exact hop, by rw [hO]; exact hcp, ?_, hN, hϖO, hϖu, hunif, htr, hnrm, ?_, hbig⟩
  · intro y hy
    have hσ : ∀ x : F, starRingAut (algebraMap F A.L x) = algebraMap F A.L x := fun x => by
      rw [starRingAut_apply, IsScalarTower.algebraMap_apply F A.K A.L, A.star_K]
    let σ : A.L ≃ₐ[F] A.L := AlgEquiv.ofRingEquiv (f := starRingAut) hσ
    have h := spectralNorm_eq_of_equiv σ y
    rw [hmem] at hy ⊢
    have hs : σ y = star y := rfl
    rw [hs] at h
    rw [← h]
    exact hy
  · intro V hV
    obtain ⟨r, hr, hrV⟩ := hball V hV
    obtain ⟨n, hn⟩ := hsmall r hr
    exact ⟨n, fun z hz => hrV _ (hn z hz)⟩

end GlobalTheory.JR.UnramInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticExistsIntegersUniformiserStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedQuadratic_exists_integers_uniformiser : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∃ (ϖ : A.Kˣ) (O : Subring A.L), IsOpen (O : Set A.L) ∧ IsCompact (O : Set A.L) ∧ (∀ y ∈ O, star y ∈ O) ∧ (¬ ∃ y, A.NL y = (ϖ : A.K)) ∧ algebraMap A.K A.L (ϖ : A.K) ∈ O ∧ (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) ∧ (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) ∧ (∀ s : A.K, algebraMap A.K A.L s ∈ O → ∃ z ∈ O, Algebra.trace A.K A.L z = s) ∧ (∀ s : A.K, algebraMap A.K A.L s ∈ O → (∃ r ∈ O, algebraMap A.K A.L s * r = 1) → ∃ w ∈ O, A.NL w = s) ∧ (∀ U ∈ 𝓝 (0 : A.L), ∃ n : ℕ, ∀ z ∈ O, algebraMap A.K A.L ((ϖ : A.K) ^ n) * z ∈ U) ∧ ∀ y : A.L, ∃ n : ℕ, algebraMap A.K A.L ((ϖ : A.K) ^ n) * y ∈ O := by
  first | exact @GlobalTheory.JR.UnramInt.main | exact GlobalTheory.JR.UnramInt.main | (intros; apply GlobalTheory.JR.UnramInt.main <;> assumption)
end
