module

public import GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
public import GroundTheory.AutomorphicForms.ContragredientTranspose.GelfandKazhdan
public import GroundTheory.AutomorphicForms.ContragredientTranspose.Character
public import GroundTheory.AutomorphicForms.CompactFormulaCountable

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.ReductionIdele
open NumberField Set
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

namespace Reduction

variable {K : Type*} [Field K] [NumberField K]

theorem exists_isCompact_mul_mem_of_ideleModule_mem_Icc {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∃ S : Set (IdeleGroup K), IsCompact S ∧ ∀ s : IdeleGroup K,
      a ≤ (ideleModule K s : ℝ) → (ideleModule K s : ℝ) ≤ b → ∃ c : Kˣ, diagonal K c * s ∈ S := by
  obtain ⟨D, hD, -, hxD⟩ := exists_isCompact_normOneSubgroup K
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  set I : Set {r : ℝ // 0 < r} := Subtype.val ⁻¹' Icc a b with hI
  have hIc : IsCompact I := by
    rw [Subtype.isCompact_iff]
    have : Subtype.val '' I = Icc a b := by
      ext r
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ht
      · intro hr
        exact ⟨⟨r, lt_of_lt_of_le ha hr.1⟩, hr, rfl⟩
    rw [this]
    exact isCompact_Icc
  refine ⟨(fun p : IdeleGroup K × {r : ℝ // 0 < r} => p.1 * moduleSection w₀ p.2) '' (D ×ˢ I),
    (hD.prod hIc).image (continuous_fst.mul ((continuous_moduleSection w₀).comp continuous_snd)),
    fun s has hsb => ?_⟩
  obtain ⟨c, hc⟩ := hxD _ (mul_inv_moduleSection_mem w₀ s)
  refine ⟨c, ⟨(diagonal K c * (s * (moduleSection w₀ (ideleModule K s))⁻¹), ideleModule K s),
    ⟨hc, has, hsb⟩, ?_⟩⟩
  simp only [mul_assoc, inv_mul_cancel, mul_one]

end Reduction

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.ContragredientTranspose
section -- merged from GroundTheory.PowerSubgroups.CountableNeighbourhoods.MapThetaTInvariant
namespace GroundTheory.Variant₂.N1

open MeasureTheory Topology Filter ValuativeRel

namespace MapThetaTInvariant

section LocalField

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

lemma countable_valueGroupWithZero : Countable (ValueGroupWithZero F) :=
  haveI : Countable (WithZero (Multiplicative ℤ)) := inferInstanceAs (Countable (Option ℤ))
  Countable.of_equiv _ (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toEquiv.symm

lemma nhds_zero_isCountablyGenerated : (𝓝 (0 : F)).IsCountablyGenerated := by
  have := countable_valueGroupWithZero F
  exact (IsValuativeTopology.hasBasis_nhds_zero' F).isCountablyGenerated

lemma sigmaCompactSpace : SigmaCompactSpace F := by
  have := countable_valueGroupWithZero F
  refine SigmaCompactSpace.of_countable
    (Set.range fun γ : ValueGroupWithZero F => {x : F | valuation F x ≤ γ})
    (Set.countable_range _) ?_ ?_
  · rintro _ ⟨γ, rfl⟩
    exact IsNonarchimedeanLocalField.isCompact_closedBall F γ
  · ext x
    simp only [Set.sUnion_range, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨_, le_rfl⟩

lemma metrizableSpace : TopologicalSpace.MetrizableSpace F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have := nhds_zero_isCountablyGenerated F
  have := IsUniformAddGroup.uniformity_countably_generated (α := F)
  exact UniformSpace.metrizableSpace

lemma secondCountableTopology : SecondCountableTopology F := by
  have := sigmaCompactSpace F
  have := metrizableSpace F
  infer_instance

end LocalField

section GeneralLinear

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

lemma secondCountableTopology_GL : SecondCountableTopology (GL (Fin n) F) := by
  have := secondCountableTopology F
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) F)).symm.isEmbedding.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology


open GroundTheory.Automorphic.ContragredientTranspose in
lemma continuous_transposeGL {F : Type*} [Field F] [TopologicalSpace F] {n : ℕ} :
    Continuous (transposeGL : GL (Fin n) F → GL (Fin n) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_transpose
  · exact Units.continuous_coe_inv.matrix_transpose


open GroundTheory.Automorphic.ContragredientTranspose in
noncomputable def thetaTContinuous : GL (Fin n) F ≃ₜ* GL (Fin n) F :=
  { (thetaT : GL (Fin n) F ≃* GL (Fin n) F) with
    continuous_toFun := continuous_transposeGL.inv
    continuous_invFun := continuous_transposeGL.inv }


open GroundTheory.Automorphic.ContragredientTranspose in
lemma thetaT_thetaT {F : Type*} [Field F] {n : ℕ} (g : GL (Fin n) F) :
    (thetaT : GL (Fin n) F ≃* GL (Fin n) F) (thetaT g) = g :=
  (thetaT : GL (Fin n) F ≃* GL (Fin n) F).symm_apply_apply g

end GeneralLinear

end MapThetaTInvariant

open MapThetaTInvariant


open GroundTheory.Automorphic.ContragredientTranspose in
theorem map_thetaT_eq_self {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n : ℕ} [MeasurableSpace (GL (Fin n) F)]
    [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    Measure.map (⇑thetaT) μ = μ := by
  have := secondCountableTopology_GL (F := F) (n := n)
  set θ : GL (Fin n) F ≃ₜ* GL (Fin n) F := thetaTContinuous
  have hθ : ⇑(thetaT : GL (Fin n) F ≃* GL (Fin n) F) = ⇑θ := rfl
  have hmeas : Measurable θ := θ.continuous.measurable
  rw [hθ]
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map θ) μ
  set c := Measure.haarScalarFactor (μ.map θ) μ

  have h2 : (μ.map θ).map θ = μ := by
    rw [Measure.map_map hmeas hmeas]
    convert Measure.map_id
    ext g : 1
    exact thetaT_thetaT g
  have hsq : (c * c) • μ = μ := by
    conv_rhs => rw [← h2, hc, Measure.map_smul c hmeas.aemeasurable, hc, smul_smul]

  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : GL (Fin n) F)
  have hpos : 0 < μ K := Measure.measure_pos_of_mem_nhds μ hK1
  have hfin : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have hcc : c * c = 1 := by
    have := congrArg (fun ν : Measure (GL (Fin n) F) => ν K) hsq
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    have h' : ((c * c : NNReal) : ENNReal) * μ K = 1 * μ K := by rw [one_mul]; exact this
    have := (ENNReal.mul_left_inj hpos.ne' hfin).1 h'
    exact_mod_cast this
  have hc1 : c = 1 := by
    have h0 : (0 : NNReal) ≤ c := c.2
    nlinarith [mul_self_nonneg (c - 1)]
  rw [hc, hc1, one_smul]

end GroundTheory.Variant₂.N1
end

namespace GroundTheory.Automorphic.ContragredientTranspose

open MeasureTheory Measure GroundTheory.Automorphic.Whittaker

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

def subrepCompOrderIso {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (α : G ≃* G) :
    Subrepresentation (ρ.comp α.toMonoidHom) ≃o Subrepresentation ρ where
  toFun W := ⟨W.toSubmodule, fun g v hv => by
    have := W.apply_mem_toSubmodule (α.symm g) hv
    simpa using this⟩
  invFun W := ⟨W.toSubmodule, fun g v hv => W.apply_mem_toSubmodule (α g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (α : G ≃* G) :
    Representation.IsIrreducible (ρ.comp α.toMonoidHom) :=
  (OrderIso.isSimpleOrder_iff (subrepCompOrderIso ρ α)).2 inferInstance

theorem map_thetaT_eq [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    μ.map (thetaT : GL (Fin n) F ≃* GL (Fin n) F) = μ :=
  _root_.GroundTheory.Variant₂.N1.map_thetaT_eq_self μ

theorem nonempty_equiv_contragredient {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V) (hπ : IsAdmissible π) [π.IsIrreducible] :
    Nonempty ((contragredient π).Equiv
      (π.comp (thetaT : GL (Fin n) F ≃* GL (Fin n) F).toMonoidHom)) := by
  let _ : MeasurableSpace (GL (Fin n) F) := _root_.borel _
  have : BorelSpace (GL (Fin n) F) := ⟨rfl⟩
  set μ : Measure (GL (Fin n) F) := haar
  have : μ.IsMulRightInvariant := Measures.isMulRightInvariant_GL F n μ
  have : μ.IsInvInvariant := ⟨Measures.inv_eq_self_GL F n μ⟩
  have hc : Continuous (thetaT : GL (Fin n) F ≃* GL (Fin n) F) := continuous_thetaT
  have hc' : Continuous (thetaT : GL (Fin n) F ≃* GL (Fin n) F).symm := continuous_thetaT
  have := isIrreducible_contragredient hπ
  have := isIrreducible_comp π (thetaT : GL (Fin n) F ≃* GL (Fin n) F)
  apply nonempty_equiv_of_distChar_eq (μ := μ) (isAdmissible_contragredient hπ)
    (isAdmissible_comp _ hc hc' hπ)
  refine LinearMap.ext fun f => ?_
  rw [distChar_contragredient, distChar_comp μ _ hc hc' (map_thetaT_eq μ) hπ]
  have e : compHomeoL (mulEquivHomeo (thetaT : GL (Fin n) F ≃* GL (Fin n) F) hc hc').symm f =
      compHomeoL transposeHomeo (compHomeoL (Homeomorph.inv (GL (Fin n) F)) f) :=
    Subtype.ext (funext fun x => rfl)
  rw [e, distribution_transpose_invariant (distChar μ π hπ) (fun g f => distChar_biTranslL μ hπ g f)]

noncomputable def longestWeyl : GL (Fin n) F := permGL F (Fin.revPerm (n := n))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem longestWeyl_mul_self : (longestWeyl : GL (Fin n) F) * longestWeyl = 1 := by
  rw [longestWeyl, ← map_mul]
  have : (Fin.revPerm (n := n)) * Fin.revPerm = 1 := Equiv.ext fun i => by simp
  rw [this, map_one]


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem thetaT_eq_longestWeyl (g : GL (Fin n) F) :
    thetaT g = longestWeyl * theta g * longestWeyl := by
  have hs : sigma g = longestWeyl * transposeGL g * longestWeyl :=
    Units.ext (by rw [coe_sigma, sigmaMat_eq, Units.val_mul, Units.val_mul, coe_transposeGL]; rfl)
  have hw : (longestWeyl : GL (Fin n) F)⁻¹ = longestWeyl :=
    inv_eq_of_mul_eq_one_right longestWeyl_mul_self
  rw [theta, hs, thetaT_apply]
  simp only [_root_.mul_inv_rev, hw, mul_assoc, longestWeyl_mul_self, mul_one]
  rw [← mul_assoc, longestWeyl_mul_self, one_mul]

theorem rank_whittaker_le_one (ψ₀ : AddChar F ℂ) (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V) (hπ : IsAdmissible π) [π.IsIrreducible] :
    Module.rank ℂ (equivariantFunctionals π
      (fun u : Iwasawa.unipotent F n => psiN ψ₀ (u : GL (Fin n) F))) ≤ 1 := by
  by_cases h0 : equivariantFunctionals π
      (fun u : Iwasawa.unipotent F n => psiN ψ₀ (u : GL (Fin n) F)) = ⊥
  · rw [h0, rank_bot]
    exact zero_le_one
  refine rank_whittaker_le_one_of_contragredient ψ₀ hψ hψ₁ π hπ ?_
  obtain ⟨ℓ, hℓ, hℓ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨E⟩ := nonempty_equiv_contragredient π hπ
  set w₀ : GL (Fin n) F := longestWeyl
  let ℓ' : Module.Dual ℂ (smoothVectors (Representation.dual π)) :=
    ℓ ∘ₗ π w₀ ∘ₗ E.toLinearEquiv.toLinearMap
  have hℓ' : ∀ x, ℓ' x = ℓ (π w₀ (E.toLinearEquiv x)) := fun _ => rfl
  have hmem : ℓ' ∈ equivariantFunctionals (contragredient π)
      (fun u : Iwasawa.unipotent F n => (psiN ψ₀ (u : GL (Fin n) F))⁻¹) := by
    intro u x
    rw [hℓ', hℓ', Representation.Equiv.toLinearEquiv_apply, E.toIntertwiningMap.isIntertwining,
      ← Representation.Equiv.toLinearEquiv_apply]
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [← Module.End.mul_apply, ← map_mul, thetaT_eq_longestWeyl]
    have e : w₀ * (longestWeyl * theta (u : GL (Fin n) F) * longestWeyl) =
        theta (u : GL (Fin n) F) * w₀ := by
      simp only [w₀, ← mul_assoc, longestWeyl_mul_self, one_mul]
    rw [e, map_mul, Module.End.mul_apply]
    have := hℓ ⟨theta (u : GL (Fin n) F), theta_mem_unipotent u.2⟩ (π w₀ (E.toLinearEquiv x))
    simp only at this
    rw [this, psiN_theta ψ₀ u.2]
  intro hbot
  rw [hbot] at hmem
  have h0' : ℓ' = 0 := (Submodule.mem_bot ℂ).1 hmem
  apply hℓ0
  refine LinearMap.ext fun v => ?_
  have := congrArg (fun φ : Module.Dual ℂ (smoothVectors (Representation.dual π)) =>
    φ (E.toLinearEquiv.symm (π w₀ v))) h0'
  simp only [hℓ', LinearEquiv.apply_symm_apply, LinearMap.zero_apply] at this
  rw [← Module.End.mul_apply, ← map_mul, longestWeyl_mul_self, map_one, Module.End.one_apply]
    at this
  rw [this, LinearMap.zero_apply]

end GroundTheory.Automorphic.ContragredientTranspose
end

section -- merged from GroundTheory.AutomorphicForms.CompactFormulaSums
open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

theorem ccToL1_add (f g : CompactlySupportedContinuousMap G ℂ) :
    ccToL1 μ (f + g) = ccToL1 μ f + ccToL1 μ g := by
  unfold ccToL1
  rw [← MemLp.toLp_add]
  rfl

end UnitaryRep

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

end RightCosetSpace

end

end GroundTheory.Automorphic
end
