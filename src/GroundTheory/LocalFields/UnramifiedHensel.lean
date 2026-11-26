module

public import GroundTheory.LocalFields.UnramifiedDefs
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import GroundTheory.GlobalFields.KummerTheory.LocalIndex
public import GroundTheory.LocalFields.Eisenstein

@[expose] public section

section -- merged from GroundTheory.LocalFields.UnramifiedHensel
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField

section Base

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

instance henselianLocalRing_integer : HenselianLocalRing 𝒪[K] where
  toIsLocalRing := inferInstance
  is_henselian f hf a₀ h₁ h₂ := by
    have := isAdicComplete_integer K
    exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)

end Base

section Residue

variable (K M : Type*) [Field K] [ValuativeRel K] [Field M] [ValuativeRel M]
  [Algebra K M] [ValuativeExtension K M]

theorem residue_aeval [Algebra 𝓀[K] 𝓀[M]]
    (h : ∀ x : 𝒪[K], algebraMap 𝓀[K] 𝓀[M] (residue 𝒪[K] x) =
      residue 𝒪[M] (algebraMap 𝒪[K] 𝒪[M] x))
    (P : 𝒪[K][X]) (x : 𝒪[M]) :
    residue 𝒪[M] (aeval x P) = aeval (residue 𝒪[M] x) (P.map (residue 𝒪[K])) := by
  have hc : (algebraMap 𝓀[K] 𝓀[M]).comp (residue 𝒪[K]) =
      (residue 𝒪[M]).comp (algebraMap 𝒪[K] 𝒪[M]) := RingHom.ext h
  rw [aeval_def, aeval_def, eval₂_map, hc, hom_eval₂]

end Residue

theorem isScalarTower_residueField (K E L : Type*) [Field K] [ValuativeRel K] [Field E]
    [ValuativeRel E] [Field L] [ValuativeRel L] [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L] [ValuativeExtension K E] [ValuativeExtension E L]
    [ValuativeExtension K L] [Algebra 𝓀[K] 𝓀[E]] [Algebra 𝓀[E] 𝓀[L]] [Algebra 𝓀[K] 𝓀[L]]
    (h₁ : ∀ x : 𝒪[K], algebraMap 𝓀[K] 𝓀[E] (residue 𝒪[K] x) =
      residue 𝒪[E] (algebraMap 𝒪[K] 𝒪[E] x))
    (h₂ : ∀ x : 𝒪[E], algebraMap 𝓀[E] 𝓀[L] (residue 𝒪[E] x) =
      residue 𝒪[L] (algebraMap 𝒪[E] 𝒪[L] x))
    (h₃ : ∀ x : 𝒪[K], algebraMap 𝓀[K] 𝓀[L] (residue 𝒪[K] x) =
      residue 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x)) :
    IsScalarTower 𝓀[K] 𝓀[E] 𝓀[L] := by
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  obtain ⟨x, rfl⟩ := residue_surjective x
  rw [h₁, h₂, h₃, IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[E] 𝒪[L]]

section Extension

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem exists_lift_primitive :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧
      P.natDegree = ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) ∧ (P.map (residue 𝒪[K])).Separable ∧
      IntermediateField.adjoin 𝓀[K] {residue 𝒪[L] β} = ⊤ := by
  obtain ⟨b, hb⟩ := Field.exists_primitive_element 𝓀[K] 𝓀[L]
  have hbi : IsIntegral 𝓀[K] b := .of_finite _ _
  obtain ⟨P, hPmap, hPdeg, hPmon⟩ := lifts_and_natDegree_eq_and_monic
    (f := residue 𝒪[K]) (p := minpoly 𝓀[K] b)
    ((lifts_iff_coeff_lifts _).2 fun n ↦ residue_surjective _) (minpoly.monic hbi)
  have hsep : (minpoly 𝓀[K] b).Separable := Algebra.IsSeparable.isSeparable 𝓀[K] b
  obtain ⟨b0, rfl⟩ := residue_surjective (R := 𝒪[L]) b
  let Q := P.map (algebraMap 𝒪[K] 𝒪[L])
  have hQ : Q.Monic := hPmon.map _
  have h1 : Q.eval b0 ∈ 𝓂[L] := by
    rw [← residue_eq_zero_iff, eval_map_algebraMap, residue_aeval K L (fun _ ↦ rfl), hPmap, minpoly.aeval]
  have h2 : IsUnit (Q.derivative.eval b0) := by
    rw [← residue_ne_zero_iff_isUnit, derivative_map, eval_map_algebraMap, residue_aeval K L (fun _ ↦ rfl),
      ← derivative_map, hPmap]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  obtain ⟨β, hβ, hβb⟩ := HenselianLocalRing.is_henselian Q hQ b0 h1 h2
  have hres : residue 𝒪[L] β = residue 𝒪[L] b0 := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hβb
  refine ⟨β, P, hPmon, ?_, ?_, ?_, ?_⟩
  · rw [← eval_map_algebraMap]
    exact hβ
  · rw [hPdeg, residueDegree_eq_finrank, ← IntermediateField.adjoin.finrank hbi, hb,
      IntermediateField.finrank_top']
  · rw [hPmap]
    exact hsep
  · rw [hres]
    exact hb

theorem residueDegree_eq_one_iff_surjective (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F L] [ValuativeExtension F L]
    [FiniteDimensional F L] :
    ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[F])) = 1 ↔ Function.Surjective (algebraMap 𝓀[F] 𝓀[L]) := by
  rw [residueDegree_eq_finrank, ← Subalgebra.bot_eq_top_iff_finrank_eq_one]
  constructor
  · intro h y
    have : y ∈ (⊥ : Subalgebra 𝓀[F] 𝓀[L]) := h ▸ Algebra.mem_top
    exact Algebra.mem_bot.1 this
  · intro h
    refine eq_top_iff.2 fun y _ ↦ Algebra.mem_bot.2 (h y)

theorem exists_unramified_adjoin :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧ (P.map (residue 𝒪[K])).Separable ∧
      IsUnramified K K⟮(β : L)⟯ ∧ Module.finrank K K⟮(β : L)⟯ = ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) ∧
      ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K⟮(β : L)⟯])) = 1 := by
  obtain ⟨β, P, hPm, hβ, hdeg, hsep, hgen⟩ := exists_lift_primitive K L
  set T := K⟮(β : L)⟯ with hT
  have hβL : aeval (β : L) P = 0 := by
    have := aeval_algHom_apply (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L) β P
    rw [hβ, map_zero] at this
    exact this
  have hle : Module.finrank K T ≤ ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) := by
    have hi : IsIntegral K (β : L) := .of_finite K _
    rw [hT, IntermediateField.adjoin.finrank hi, ← hdeg]
    have hne : P.map (algebraMap 𝒪[K] K) ≠ 0 := (hPm.map _).ne_zero
    have hd := minpoly.dvd K (β : L) (p := P.map (algebraMap 𝒪[K] K))
      (by rw [aeval_map_algebraMap]; exact hβL)
    calc (minpoly K (β : L)).natDegree ≤ (P.map (algebraMap 𝒪[K] K)).natDegree :=
          natDegree_le_of_dvd hd hne
      _ = P.natDegree := hPm.natDegree_map _
  have hβT : (β : L) ∈ T := IntermediateField.mem_adjoin_simple_self K _
  let βT : 𝒪[T] := ⟨⟨β, hβT⟩, (algebraMap_mem_integer_iff T L _).1 β.2⟩
  have hsurj : Function.Surjective (algebraMap 𝓀[T] 𝓀[L]) := by
    have := isScalarTower_residueField K T L (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
    have hb : residue 𝒪[L] β ∈ (IsScalarTower.toAlgHom 𝓀[K] 𝓀[T] 𝓀[L]).range :=
      ⟨residue 𝒪[T] βT, rfl⟩
    have htop : Algebra.adjoin 𝓀[K] {residue 𝒪[L] β} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (IsAlgebraic.of_finite _ _), hgen, IntermediateField.top_toSubalgebra]
    have hr : (IsScalarTower.toAlgHom 𝓀[K] 𝓀[T] 𝓀[L]).range = ⊤ :=
      eq_top_iff.2 (htop ▸ Algebra.adjoin_le (Set.singleton_subset_iff.2 hb))
    intro y
    obtain ⟨z, hz⟩ := (hr ▸ Algebra.mem_top : y ∈ (IsScalarTower.toAlgHom 𝓀[K] 𝓀[T] 𝓀[L]).range)
    exact ⟨z, hz⟩
  have h1 : ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[T])) = 1 := (residueDegree_eq_one_iff_surjective L T).2 hsurj
  have htower := residueDegree_tower K T L
  rw [h1, mul_one] at htower
  have hfe : ((IsLocalRing.maximalIdeal 𝒪[T]).inertiaDeg (𝒪[K])) ≤ Module.finrank K T := by
    rw [← ramificationIndex_mul_residueDegree K T]
    exact Nat.le_mul_of_pos_left _ (ramificationIndex_pos K T)
  have heq : Module.finrank K T = ((IsLocalRing.maximalIdeal 𝒪[T]).inertiaDeg (𝒪[K])) := by omega
  exact ⟨β, P, hPm, hβ, hsep, (isUnramified_iff_residueDegree_eq_finrank K T).2 heq.symm,
    heq.trans htower.symm, h1⟩

theorem mem_of_residueDegree_eq_one (F : IntermediateField K L) (hF : ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[F])) = 1)
    (P : 𝒪[K][X]) (hP : P.Monic) (γ : 𝒪[L]) (hγ : aeval γ P = 0)
    (hd : IsUnit (aeval γ (derivative P))) : (γ : L) ∈ F := by
  have hsurj := (residueDegree_eq_one_iff_surjective L F).1 hF
  have hinj : Function.Injective (algebraMap 𝓀[F] 𝓀[L]) := (algebraMap 𝓀[F] 𝓀[L]).injective
  obtain ⟨c₀', hc₀'⟩ := hsurj (residue 𝒪[L] γ)
  obtain ⟨c₀, rfl⟩ := residue_surjective (R := 𝒪[F]) c₀'
  have hc₀ : residue 𝒪[L] (algebraMap 𝒪[F] 𝒪[L] c₀) = residue 𝒪[L] γ := hc₀'

  have key : ∀ Q : 𝒪[K][X], algebraMap 𝓀[F] 𝓀[L] (residue 𝒪[F] (aeval c₀ Q)) =
      residue 𝒪[L] (aeval γ Q) := by
    intro Q
    rw [show algebraMap 𝓀[F] 𝓀[L] (residue 𝒪[F] (aeval c₀ Q)) =
        residue 𝒪[L] (algebraMap 𝒪[F] 𝒪[L] (aeval c₀ Q)) from rfl, ← aeval_algebraMap_apply,
      residue_aeval K L (fun _ ↦ rfl), hc₀, ← residue_aeval K L (fun _ ↦ rfl)]
  let Q := P.map (algebraMap 𝒪[K] 𝒪[F])
  have h1 : Q.eval c₀ ∈ 𝓂[F] := by
    rw [← residue_eq_zero_iff, eval_map_algebraMap]
    apply hinj
    rw [key, hγ, map_zero, map_zero]
  have h2 : IsUnit (Q.derivative.eval c₀) := by
    rw [← residue_ne_zero_iff_isUnit, derivative_map, eval_map_algebraMap]
    intro h0
    have := key (derivative P)
    rw [h0, map_zero] at this
    exact (residue_ne_zero_iff_isUnit _).2 hd this.symm
  obtain ⟨c, hc, hcc₀⟩ := HenselianLocalRing.is_henselian Q (hP.map _) c₀ h1 h2
  have hcF : aeval c P = 0 := by
    rw [← eval_map_algebraMap]
    exact hc
  set c' := algebraMap 𝒪[F] 𝒪[L] c
  have hc' : aeval c' P = 0 := by
    rw [aeval_algebraMap_apply, hcF, map_zero]
  have hres : residue 𝒪[L] c' = residue 𝒪[L] γ := by
    rw [← hc₀]
    have : residue 𝒪[F] c = residue 𝒪[F] c₀ := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      exact hcc₀
    change algebraMap 𝓀[F] 𝓀[L] (residue 𝒪[F] c) = algebraMap 𝓀[F] 𝓀[L] (residue 𝒪[F] c₀)
    rw [this]
  have heq : γ = c' := by
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := P.map (algebraMap 𝒪[K] 𝒪[L]))
      (by rw [eval_map_algebraMap]; exact hγ) (by rw [eval_map_algebraMap]; exact hc') ?_ ?_
    · rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff, map_sub, hres, sub_self]
    · rw [derivative_map, eval_map_algebraMap]
      exact hd
  rw [heq]
  exact (c : F).2

end Extension

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.UnramifiedNormSurj
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Filter Polynomial
open GroundTheory.Global (filtrationComplete_unitFiltration filtrationSeparated_unitFiltration
  div_mem_unitFiltration_iff)

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FiniteDimensional K L] in
theorem coe_normIntegerUnits_eq (u : 𝒪[L]ˣ) :
    ((normIntegerUnits K L u : 𝒪[K]ˣ) : 𝒪[K]) = Algebra.norm 𝒪[K] (u : 𝒪[L]) :=
  rfl

theorem exists_norm_one_add_smul (r : 𝒪[K]) (a : 𝒪[L]) :
    ∃ c : 𝒪[K], Algebra.norm 𝒪[K] (1 + r • a) =
      1 + r * Algebra.trace 𝒪[K] 𝒪[L] a + r ^ 2 * c := by
  classical
  let b := Module.Free.chooseBasis 𝒪[K] 𝒪[L]
  refine ⟨(Matrix.det (1 + (X : 𝒪[K][X]) • (Algebra.leftMulMatrix b a).map C)).divX.divX.eval r,
    ?_⟩
  rw [Algebra.norm_eq_matrix_det b, map_add (f := _), map_one, map_smul, Matrix.det_one_add_smul,
    Algebra.trace_eq_matrix_trace b]
  ring

theorem residue_eq_sum_repr (y : 𝒪[L]) :
    residue 𝒪[L] y = ∑ i, residue 𝒪[K] ((Module.Free.chooseBasis 𝒪[K] 𝒪[L]).repr y i) •
      residue 𝒪[L] (Module.Free.chooseBasis 𝒪[K] 𝒪[L] i) := by
  conv_lhs => rw [← (Module.Free.chooseBasis 𝒪[K] 𝒪[L]).sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  rfl

section Residue

variable [IsUnramified K L]


variable (K L) in
def residueBasis : Module.Basis (Module.Free.ChooseBasisIndex 𝒪[K] 𝒪[L]) 𝓀[K] 𝓀[L] :=
  basisOfTopLeSpanOfCardEqFinrank (fun i ↦ residue 𝒪[L] (Module.Free.chooseBasis 𝒪[K] 𝒪[L] i))
    (by
      rintro z -
      obtain ⟨y, rfl⟩ := residue_surjective z
      rw [residue_eq_sum_repr (K := K)]
      exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, finrank_integer K L,
        IsUnramified.finrank_residueField K L])

theorem residueBasis_apply (i : Module.Free.ChooseBasisIndex 𝒪[K] 𝒪[L]) :
    residueBasis K L i = residue 𝒪[L] (Module.Free.chooseBasis 𝒪[K] 𝒪[L] i) := by
  simp [residueBasis]

theorem residueBasis_repr (y : 𝒪[L]) (i : Module.Free.ChooseBasisIndex 𝒪[K] 𝒪[L]) :
    (residueBasis K L).repr (residue 𝒪[L] y) i =
      residue 𝒪[K] ((Module.Free.chooseBasis 𝒪[K] 𝒪[L]).repr y i) := by
  have h : residue 𝒪[L] y = ∑ j, residue 𝒪[K] ((Module.Free.chooseBasis 𝒪[K] 𝒪[L]).repr y j) •
      residueBasis K L j := by
    simp only [residueBasis_apply]
    exact residue_eq_sum_repr y
  rw [h, (residueBasis K L).repr_sum_self]

theorem leftMulMatrix_residueBasis (y : 𝒪[L]) :
    Algebra.leftMulMatrix (residueBasis K L) (residue 𝒪[L] y) =
      (Algebra.leftMulMatrix (Module.Free.chooseBasis 𝒪[K] 𝒪[L]) y).map (residue 𝒪[K]) := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    residueBasis_apply, ← map_mul, residueBasis_repr]

theorem residue_norm (y : 𝒪[L]) :
    residue 𝒪[K] (Algebra.norm 𝒪[K] y) = Algebra.norm 𝓀[K] (residue 𝒪[L] y) := by
  classical
  rw [Algebra.norm_eq_matrix_det (Module.Free.chooseBasis 𝒪[K] 𝒪[L]),
    Algebra.norm_eq_matrix_det (residueBasis K L), leftMulMatrix_residueBasis, RingHom.map_det]
  rfl

theorem residue_trace (y : 𝒪[L]) :
    residue 𝒪[K] (Algebra.trace 𝒪[K] 𝒪[L] y) = Algebra.trace 𝓀[K] 𝓀[L] (residue 𝒪[L] y) := by
  rw [Algebra.trace_eq_matrix_trace (Module.Free.chooseBasis 𝒪[K] 𝒪[L]),
    Algebra.trace_eq_matrix_trace (residueBasis K L), leftMulMatrix_residueBasis]
  exact AddMonoidHom.map_trace (residue 𝒪[K]).toAddMonoidHom _

theorem irreducible_algebraMap_of_isUnramified {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap 𝒪[K] 𝒪[L] ϖ) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  have h := map_maximalIdeal K L
  rw [ramificationIndex, IsUnramified.ramificationIndex_eq_one, pow_one, hϖ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton] at h
  exact h.symm

theorem trace_integer_surjective : Function.Surjective (Algebra.trace 𝒪[K] 𝒪[L]) := by
  obtain ⟨t, ht⟩ := Algebra.trace_surjective 𝓀[K] 𝓀[L] 1
  obtain ⟨a, rfl⟩ := residue_surjective t
  have hu : IsUnit (Algebra.trace 𝒪[K] 𝒪[L] a) := by
    rw [← residue_ne_zero_iff_isUnit, residue_trace, ht]
    exact one_ne_zero
  intro c
  refine ⟨(((hu.unit⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * c) • a, ?_⟩
  rw [map_smul, smul_eq_mul]
  linear_combination c * Units.inv_mul hu.unit - (((hu.unit⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * c) * hu.unit_spec

theorem normIntegerUnits_mem_unitFiltration {n : ℕ} {u : 𝒪[L]ˣ} (hu : u ∈ unitFiltration L n) :
    normIntegerUnits K L u ∈ unitFiltration K n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖL := irreducible_algebraMap_of_isUnramified (L := L) hϖ
  obtain ⟨a, ha⟩ := (mem_maximalIdeal_pow_iff hϖL).mp (mem_unitFiltration.mp hu)
  have hu' : (u : 𝒪[L]) = 1 + ϖ ^ n • a := by
    rw [Algebra.smul_def, map_pow, ← ha]
    ring
  obtain ⟨c, hc⟩ := exists_norm_one_add_smul (ϖ ^ n) a
  rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ]
  refine ⟨Algebra.trace 𝒪[K] 𝒪[L] a + ϖ ^ n * c, ?_⟩
  rw [coe_normIntegerUnits_eq, hu', hc]
  ring

theorem exists_normIntegerUnits_div_mem_one (h : 𝒪[K]ˣ) :
    ∃ g : 𝒪[L]ˣ, h / normIntegerUnits K L g ∈ unitFiltration K 1 := by
  obtain ⟨ζ, hζ⟩ := FiniteField.unitsMap_norm_surjective 𝓀[K] 𝓀[L] (unitsToResidue K h)
  obtain ⟨g, rfl⟩ := unitsToResidue_surjective L ζ
  refine ⟨g, ?_⟩
  rw [← ker_unitsToResidue, MonoidHom.mem_ker, _root_.map_div, div_eq_one, ← hζ]
  ext
  simp [coe_normIntegerUnits_eq, residue_norm]

theorem exists_normIntegerUnits_div_mem_succ {n : ℕ} (hn : 1 ≤ n) {h : 𝒪[K]ˣ}
    (hh : h ∈ unitFiltration K n) :
    ∃ g ∈ unitFiltration L n, h / normIntegerUnits K L g ∈ unitFiltration K (n + 1) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖL := irreducible_algebraMap_of_isUnramified (L := L) hϖ
  obtain ⟨c, hc⟩ := (mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp hh)
  obtain ⟨t, ht⟩ := Algebra.trace_surjective 𝓀[K] 𝓀[L] (residue 𝒪[K] c)
  obtain ⟨a, rfl⟩ := residue_surjective t
  have hu := isUnit_one_add_mul hϖL hn a
  refine ⟨hu.unit, ?_, ?_⟩
  · rw [mem_unitFiltration, IsUnit.unit_spec, add_sub_cancel_left, mem_maximalIdeal_pow_iff hϖL]
    exact dvd_mul_right _ _
  · rw [div_mem_unitFiltration_iff]
    obtain ⟨d, hd⟩ := exists_norm_one_add_smul (ϖ ^ n) a
    have e1 : ((normIntegerUnits K L hu.unit : 𝒪[K]ˣ) : 𝒪[K]) =
        1 + ϖ ^ n * Algebra.trace 𝒪[K] 𝒪[L] a + (ϖ ^ n) ^ 2 * d := by
      rw [coe_normIntegerUnits_eq, IsUnit.unit_spec, ← hd, Algebra.smul_def, map_pow]
    have e2 : c - Algebra.trace 𝒪[K] 𝒪[L] a ∈ 𝓂[K] := by
      rw [← residue_eq_zero_iff, map_sub, residue_trace, ht, sub_self]
    obtain ⟨e, he⟩ := (mem_maximalIdeal_iff_dvd hϖ).mp e2
    have hh' : (h : 𝒪[K]) = 1 + ϖ ^ n * c := by
      rw [← hc]
      ring
    rw [mem_maximalIdeal_pow_iff hϖ]
    refine ⟨e - ϖ ^ (n - 1) * d, ?_⟩
    rw [e1, hh']
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    linear_combination (ϖ ^ (m + 1)) * he

theorem map_normIntegerUnits_unitFiltration (n : ℕ) :
    (unitFiltration L n).map (normIntegerUnits K L) = unitFiltration K n :=
  map_eq_of_graded_surjective (unitFiltration_antitone L) (unitFiltration_antitone K)
    filtrationComplete_unitFiltration filtrationSeparated_unitFiltration
    (normIntegerUnits K L) (φ := id) tendsto_id n
    (fun _ _ _ hg ↦ normIntegerUnits_mem_unitFiltration hg)
    (fun m _ h hh ↦ by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · obtain ⟨g, hg⟩ := exists_normIntegerUnits_div_mem_one (L := L) h
        exact ⟨g, by simp, hg⟩
      · exact exists_normIntegerUnits_div_mem_succ hm hh)

theorem normIntegerUnits_surjective : Function.Surjective (normIntegerUnits K L) := by
  intro h
  have e := map_normIntegerUnits_unitFiltration (K := K) (L := L) 0
  rw [unitFiltration_zero, unitFiltration_zero] at e
  have hh : h ∈ (⊤ : Subgroup 𝒪[L]ˣ).map (normIntegerUnits K L) := by
    rw [e]
    exact Subgroup.mem_top h
  obtain ⟨g, -, rfl⟩ := hh
  exact ⟨g, rfl⟩

end Residue

section NormGroup



variable [IsUnramified K L]

theorem mem_range_normUnits_iff (x : Kˣ) :
    x ∈ (normUnits K L).range ↔ (Module.finrank K L : ℤ) ∣ ord (x : K) := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [coe_normUnits, ord_norm, IsUnramified.residueDegree_eq_finrank K L]
    exact dvd_mul_right _ _
  · rintro ⟨k, hk⟩
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    obtain ⟨⟨m, u⟩, hx⟩ := (unitsOfIntProd_bijective hϖ).2 x
    have hm : m.toAdd = Module.finrank K L * k := by
      rw [← hk, ← hx, ord_unitsOfIntProd]
    obtain ⟨v, hv⟩ := normIntegerUnits_surjective (K := K) (L := L) u
    refine ⟨Units.map (algebraMap K L : K →* L) (uniformizerUnit hϖ) ^ k * unitsIncl L v, ?_⟩
    have hnv : normUnits K L (unitsIncl L v) = unitsIncl K (normIntegerUnits K L v) := by
      ext
      rw [coe_normUnits]
      change Algebra.norm K ((v : 𝒪[L]) : L) = _
      rw [← coe_norm_integer (K := K) (L := L) (v : 𝒪[L])]
      exact congrArg (algebraMap 𝒪[K] K) (coe_normIntegerUnits_eq v)
    rw [← hx, unitsOfIntProd_eq, map_mul, map_zpow, hnv, hv, hm, zpow_mul]
    congr 2
    ext
    simp [Algebra.norm_algebraMap]


end NormGroup

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.Monogenic
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial IsDiscreteValuationRing IsLocalRing

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem residue_aeval_integer (p : 𝒪[K][X]) (x : 𝒪[L]) :
    residue 𝒪[L] (aeval x p) = aeval (residue 𝒪[L] x) (p.map (residue 𝒪[K])) := by
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
  congr 1


variable (K) in
theorem adjoin_eq_top_of_residue_of_addVal_eq_one {x : 𝒪[L]}
    (hx : Algebra.adjoin 𝓀[K] {residue 𝒪[L] x} = ⊤) {π : 𝒪[L]}
    (hπA : π ∈ Algebra.adjoin 𝒪[K] {x}) (hπ : addVal 𝒪[L] π = 1) :
    Algebra.adjoin 𝒪[K] {x} = ⊤ := by
  set A := Algebra.adjoin 𝒪[K] {x}
  set e := (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K)))

  have hres : ∀ w : 𝒪[L], ∃ a ∈ A, ∃ w', w = a + π * w' := by
    intro w
    have hw : residue 𝒪[L] w ∈ Algebra.adjoin 𝓀[K] {residue 𝒪[L] x} := by
      rw [hx]; trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hw
    obtain ⟨p, hp⟩ := hw
    obtain ⟨p₀, rfl⟩ := Polynomial.map_surjective (residue 𝒪[K]) residue_surjective p
    refine ⟨aeval x p₀, ?_, ?_⟩
    · exact aeval_mem_adjoin_singleton 𝒪[K] x
    have hm : w - aeval x p₀ ∈ IsLocalRing.maximalIdeal 𝒪[L] := by
      rw [← residue_eq_zero_iff, map_sub, residue_aeval_integer]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hp
      rw [hp, sub_self]
    rw [← pow_one (IsLocalRing.maximalIdeal 𝒪[L]), mem_maximalIdeal_pow_iff_le_addVal, Nat.cast_one, ← hπ,
      addVal_le_iff_dvd] at hm
    obtain ⟨w', hw'⟩ := hm
    exact ⟨w', by rw [← hw']; ring⟩
  have step : ∀ k : ℕ, ∀ z : 𝒪[L], ∃ a ∈ A, ∃ w, z = a + π ^ k * w := by
    intro k
    induction k with
    | zero => exact fun z => ⟨0, zero_mem _, z, by simp⟩
    | succ k ih =>
      intro z
      obtain ⟨a, ha, w, rfl⟩ := ih z
      obtain ⟨b, hb, w', rfl⟩ := hres w
      refine ⟨a + π ^ k * b, add_mem ha (mul_mem (pow_mem hπA k) hb), w', ?_⟩
      ring
  obtain ⟨ϖK, hϖK⟩ := exists_irreducible 𝒪[K]
  have hassoc : Associated (algebraMap 𝒪[K] 𝒪[L] ϖK) (π ^ e) := by
    rw [← addVal_eq_iff_associated, addVal_algebraMap_integer, addVal_uniformizer hϖK,
      addVal_pow, hπ, mul_one, nsmul_eq_mul, mul_one]
  obtain ⟨u, hu⟩ := hassoc
  have hle : (⊤ : Submodule 𝒪[K] 𝒪[L]) ≤
      Subalgebra.toSubmodule A ⊔ IsLocalRing.maximalIdeal 𝒪[K] • ⊤ := by
    intro z _
    obtain ⟨a, ha, w, rfl⟩ := step e z
    refine Submodule.add_mem_sup ha ?_
    rw [← hu, mul_assoc, ← Algebra.smul_def]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [hϖK.maximalIdeal_eq]
    exact Ideal.subset_span rfl
  have hnak := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle
  rw [eq_top_iff]
  intro z _
  exact hnak Submodule.mem_top


variable (K L) in
theorem exists_integer_adjoin_eq_top : ∃ x : 𝒪[L], Algebra.adjoin 𝒪[K] {x} = ⊤ := by
  classical
  obtain ⟨ξ, hξ⟩ := Field.exists_primitive_element_of_finite_top 𝓀[K] 𝓀[L]
  have hadj : Algebra.adjoin 𝓀[K] {ξ} = ⊤ := IntermediateField.adjoin_eq_top_iff.mp hξ
  have hint : IsIntegral 𝓀[K] ξ := Algebra.IsIntegral.isIntegral ξ
  set P := minpoly 𝓀[K] ξ
  have hsep : P.Separable := PerfectField.separable_of_irreducible (minpoly.irreducible hint)
  obtain ⟨P₀, hP₀⟩ := Polynomial.map_surjective (residue 𝒪[K]) residue_surjective P
  obtain ⟨x₀, hx₀⟩ := residue_surjective ξ

  have hy₀ : aeval x₀ P₀ ∈ IsLocalRing.maximalIdeal 𝒪[L] := by
    rw [← residue_eq_zero_iff, residue_aeval_integer, hP₀, hx₀]
    exact minpoly.aeval _ _
  have hd₀ : IsUnit (aeval x₀ (derivative P₀)) := by
    rw [← not_not (a := IsUnit _), ← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff,
      residue_aeval_integer, ← derivative_map, hP₀, hx₀]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)

  obtain ⟨x, hxres, hxval⟩ : ∃ x : 𝒪[L], residue 𝒪[L] x = ξ ∧ addVal 𝒪[L] (aeval x P₀) = 1 := by
    by_cases hsq : aeval x₀ P₀ ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2
    · obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[L]
      have hϖ1 : addVal 𝒪[L] ϖ = 1 := addVal_uniformizer hϖ
      refine ⟨x₀ + ϖ, ?_, ?_⟩
      · rw [map_add (f := _), hx₀, (residue_eq_zero_iff ϖ).mpr hϖ.not_isUnit, add_zero]
      obtain ⟨k, hk⟩ := binomExpansion (P₀.map (algebraMap 𝒪[K] 𝒪[L])) x₀ ϖ
      rw [eval_map_algebraMap, eval_map_algebraMap, derivative_map, eval_map_algebraMap] at hk
      have hϖm : ϖ ∈ IsLocalRing.maximalIdeal 𝒪[L] := hϖ.not_isUnit
      have hϖsq : ϖ ^ 2 ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2 := Ideal.pow_mem_pow hϖm 2
      refine addVal_eq_one_of_mem_of_notMem_sq ?_ ?_
      · rw [hk]
        refine add_mem (add_mem hy₀ (Ideal.mul_mem_left _ _ hϖm)) ?_
        exact Ideal.mul_mem_left _ _ (Ideal.pow_le_self two_ne_zero hϖsq)
      · intro hmem
        have h1 : aeval x₀ (derivative P₀) * ϖ ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2 := by
          have : aeval x₀ (derivative P₀) * ϖ =
              aeval (x₀ + ϖ) P₀ - aeval x₀ P₀ - k * ϖ ^ 2 := by rw [hk]; ring
          rw [this]
          exact sub_mem (sub_mem hmem hsq) (Ideal.mul_mem_left _ _ hϖsq)
        obtain ⟨v, hv⟩ := hd₀
        have h2 : ϖ ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ 2 := by
          have := Ideal.mul_mem_left (IsLocalRing.maximalIdeal 𝒪[L] ^ 2) (↑v⁻¹ : 𝒪[L]) h1
          rwa [← hv, ← mul_assoc, Units.inv_mul, one_mul] at this
        rw [mem_maximalIdeal_pow_iff_le_addVal, hϖ1] at h2
        norm_num at h2
    · exact ⟨x₀, hx₀, addVal_eq_one_of_mem_of_notMem_sq hy₀ hsq⟩
  refine ⟨x, adjoin_eq_top_of_residue_of_addVal_eq_one K (π := aeval x P₀) ?_ ?_ hxval⟩
  · rw [hxres]; exact hadj
  · exact aeval_mem_adjoin_singleton 𝒪[K] x

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.HerbrandLocalBase
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global

section Galois

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

def unitsToTateZero : Kˣ →* TateZero (L ≃ₐ[K] L) Lˣ :=
  (QuotientGroup.mk' _).comp
    ((Units.map (algebraMap K L : K →* L)).codRestrict (invariants (L ≃ₐ[K] L) Lˣ) fun a g => by
      ext
      simp [AlgEquiv.smul_units_def])

theorem coe_tateNorm_units (x : Lˣ) :
    ((tateNorm (L ≃ₐ[K] L) Lˣ x : Lˣ) : L) = algebraMap K L (Algebra.norm K (x : L)) := by
  rw [algebraMap_norm_eq_prod, tateNorm_apply, Units.coe_prod]
  rfl

theorem unitsToTateZero_surjective : Function.Surjective (unitsToTateZero (K := K) (L := L)) := by
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hfix : ∀ y : L, (∀ g : L ≃ₐ[K] L, g y = y) → ∃ a : K, algebraMap K L a = y := fun y hy =>
    (IsGalois.mem_range_algebraMap_iff_fixed y).mpr hy
  obtain ⟨a, ha⟩ := hfix (x : L) fun g => congrArg Units.val (hx g)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact x.ne_zero ha.symm
  exact ⟨Units.mk0 a ha0, congrArg (QuotientGroup.mk' _) (Subtype.ext (Units.ext ha))⟩

theorem ker_unitsToTateZero : (unitsToTateZero (K := K) (L := L)).ker = (normUnits K L).range := by
  ext a
  rw [MonoidHom.mem_ker, unitsToTateZero, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, Units.ext ((algebraMap K L).injective ?_)⟩
    rw [coe_normUnits, ← coe_tateNorm_units, hy]
    rfl
  · rintro ⟨y, rfl⟩
    refine ⟨y, Units.ext ?_⟩
    rw [coe_tateNorm_units]
    rfl

theorem natCard_tateZero_units_eq :
    Nat.card (TateZero (L ≃ₐ[K] L) Lˣ) = Nat.card (Kˣ ⧸ (normUnits K L).range) := by
  rw [← ker_unitsToTateZero]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ unitsToTateZero_surjective).toEquiv.symm

end Galois

section Ord

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]


variable (L) in
def unitsOrd : Additive Lˣ →+ ℤ where
  toFun x := ord ((x.toMul : Lˣ) : L)
  map_zero' := by
    have := ord_unit (K := L) 1
    simpa using this
  map_add' x y := by
    change ord (((x.toMul * y.toMul : Lˣ)) : L) = _
    rw [Units.val_mul, ord_mul x.toMul.ne_zero y.toMul.ne_zero]

theorem unitsOrd_ofMul (x : Lˣ) : unitsOrd (L := L) (Additive.ofMul x) = ord (x : L) :=
  rfl

theorem unitsOrd_surjective : Function.Surjective (unitsOrd (L := L)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  intro n
  refine ⟨n • Additive.ofMul (uniformizerUnit hϖ), ?_⟩
  rw [map_zsmul, unitsOrd_ofMul, coe_uniformizerUnit, ord_uniformizer hϖ, smul_eq_mul, mul_one]

theorem ord_eq_zero_iff_mem_range_unitsIncl (x : Lˣ) :
    ord (x : L) = 0 ↔ x ∈ (unitsIncl L).range := by
  rw [ord_eq_zero_iff_mem, unitFiltrationUnits, unitFiltration_zero, ← MonoidHom.range_eq_map]

theorem exact_unitsIncl_unitsOrd :
    Function.Exact (MonoidHom.toAdditive (unitsIncl L)) (unitsOrd (L := L)) := by
  intro y
  change ord ((y.toMul : Lˣ) : L) = 0 ↔ _
  rw [ord_eq_zero_iff_mem_range_unitsIncl]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨Additive.ofMul u, Additive.toMul.injective hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.toMul, rfl⟩

end Ord

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem ord_algEquiv (σ : L ≃ₐ[K] L) (x : L) : ord (σ x) = ord x := by
  rw [ord, ord, normalizedValuation_apply, normalizedValuation_apply,
    valuation_algEquiv_apply K L σ x]

theorem unitsOrd_smul (σ : L ≃ₐ[K] L) (x : Lˣ) :
    unitsOrd (L := L) (Additive.ofMul (σ • x)) = unitsOrd (L := L) (Additive.ofMul x) := by
  rw [unitsOrd_ofMul, unitsOrd_ofMul, AlgEquiv.smul_units_def, Units.coe_map]
  exact ord_algEquiv σ x

theorem unitsOrd_cycSubOne (τ : L ≃ₐ[K] L) (x : Additive Lˣ) :
    unitsOrd (L := L) (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) τ x) =
      cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) τ (unitsOrd (L := L) x) := by
  rw [cycSubOne_apply, cycSubOne_apply, map_sub, Representation.ofMulDistribMulAction_apply_apply,
    unitsOrd_smul, Representation.trivial_apply]
  rfl

theorem unitsOrd_cycNorm (x : Additive Lˣ) :
    unitsOrd (L := L) (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) x) =
      cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) (unitsOrd (L := L) x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cycNorm_apply, cycNorm_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Representation.ofMulDistribMulAction_apply_apply, unitsOrd_smul, Representation.trivial_apply]
  rfl

variable {σ : L ≃ₐ[K] L}

theorem cycHerbrand_units_eq_mul (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (hA : HasHerbrandQuotient
      (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
      (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ))) :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ =
        cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ *
          Fintype.card (L ≃ₐ[K] L) := by
  have hi : Function.Injective (MonoidHom.toAdditive (unitsIncl L)) := unitsIncl_injective
  have hC : HasHerbrandQuotient (cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) σ)
      (cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) :=
    hasCyclicHerbrand_of_finite (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) hσ
  have hCv : herbrandQuotient (cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) σ)
      (cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) = Fintype.card (L ≃ₐ[K] L) :=
    cyclicHerbrand_trivial_int σ
  refine ⟨HasHerbrandQuotient.of_shortExact_left_right hi unitsOrd_surjective
    exact_unitsIncl_unitsOrd (toAdditive_cycSubOne _ unitsIncl_smul σ)
    (toAdditive_cycNorm _ unitsIncl_smul) (unitsOrd_cycSubOne σ) unitsOrd_cycNorm
    (cycSubOne_cycNorm _ σ) (cycNorm_cycSubOne _ σ) hA hC, ?_⟩
  rw [cycHerbrand, herbrandQuotient_eq_mul_of_shortExact hi unitsOrd_surjective
    exact_unitsIncl_unitsOrd (toAdditive_cycSubOne _ unitsIncl_smul σ)
    (toAdditive_cycNorm _ unitsIncl_smul) (unitsOrd_cycSubOne σ) unitsOrd_cycNorm
    (cycSubOne_cycNorm _ σ) (cycNorm_cycSubOne _ σ) hA hC, hCv]
  rfl

theorem cycHerbrand_integerUnits_eq_one_of_subgroup (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (V : Subgroup 𝒪[L]ˣ) [V.FiniteIndex] [MulDistribMulAction (L ≃ₐ[K] L) V]
    (hV : ∀ (g : L ≃ₐ[K] L) (v : V), ((g • v : V) : 𝒪[L]ˣ) = g • (v : 𝒪[L]ˣ))
    [Subsingleton (TateZero (L ≃ₐ[K] L) V)] [Subsingleton (TateNegOne (L ≃ₐ[K] L) V)] :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ = 1 := by
  have : V.subtype.range.FiniteIndex := by rw [Subgroup.range_subtype]; infer_instance
  obtain ⟨h1, h2⟩ := cycHerbrand_eq_of_injective V.subtype V.subtype_injective hV σ
  obtain ⟨h3, h4⟩ := cycHerbrand_eq_one_of_subsingleton (G := L ≃ₐ[K] L) (M := V) hσ
  exact ⟨h1.mp h3, h2.symm.trans h4⟩

end GroundTheory.LocalField
end
end
