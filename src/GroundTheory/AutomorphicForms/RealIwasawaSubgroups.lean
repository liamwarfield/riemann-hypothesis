module

public import GroundTheory.AutomorphicForms.TraceNormComp
public import GroundTheory.AutomorphicForms.RealGroupsIwasawa
public import GroundTheory.AutomorphicForms.RealGroupsHaar
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StrictlyUpperRank

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.RealGroups
section -- merged from GroundTheory.AutomorphicForms.RealGroupsIwasawaHaar
namespace GroundTheory.Automorphic

open Matrix Set
open scoped ComplexOrder

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]

theorem rclike_inv_pos {z : 𝕜} (hz : 0 < z) : 0 < z⁻¹ := by
  obtain ⟨hre, him⟩ := RCLike.pos_iff.1 hz
  have hz' : z = (RCLike.re z : 𝕜) := by rw [← RCLike.re_add_im z, him]; simp
  rw [hz', ← RCLike.ofReal_inv]
  exact RCLike.ofReal_pos.2 (inv_pos.2 hre)

def upperPosSubgroup (n 𝕜 : Type*) [RCLike 𝕜] [Fintype n] [LinearOrder n] : Subgroup (GL n 𝕜) where
  carrier := {g | (g : Matrix n n 𝕜).IsUpperTriangular ∧ ∀ i, 0 < (g : Matrix n n 𝕜) i i}
  mul_mem' {a b} ha hb := ⟨ha.1.mul hb.1, fun i => by
    rw [Units.val_mul, mul_apply_self_of_isUpperTriangular ha.1 hb.1]
    exact mul_pos (ha.2 i) (hb.2 i)⟩
  one_mem' := ⟨blockTriangular_one, fun i => by simp⟩
  inv_mem' {a} ha := by
    let : Invertible (a : Matrix n n 𝕜) :=
      invertibleOfIsUnitDet _ ((isUnit_iff_isUnit_det _).1 a.isUnit)
    have hinv : ((a⁻¹ : GL n 𝕜) : Matrix n n 𝕜) = (a : Matrix n n 𝕜)⁻¹ := coe_units_inv a
    have hU : ((a⁻¹ : GL n 𝕜) : Matrix n n 𝕜).IsUpperTriangular := by
      rw [hinv]; exact blockTriangular_inv_of_blockTriangular ha.1
    refine ⟨hU, fun i => ?_⟩
    have e0 : ((a⁻¹ : GL n 𝕜) : Matrix n n 𝕜) * (a : Matrix n n 𝕜) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e := congrFun (congrFun e0 i) i
    rw [mul_apply_self_of_isUpperTriangular hU ha.1, one_apply_eq] at e
    rw [eq_inv_of_mul_eq_one_left e]
    exact rclike_inv_pos (ha.2 i)

theorem mem_upperPosSubgroup {g : GL n 𝕜} :
    g ∈ upperPosSubgroup n 𝕜 ↔
      (g : Matrix n n 𝕜).IsUpperTriangular ∧ ∀ i, 0 < (g : Matrix n n 𝕜) i i := Iff.rfl

def kbMul (p : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜) : GL n 𝕜 :=
  Unitary.toUnits p.1 * p.2

section Split

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem conjTranspose_iwasawaK_mul_mem (g : GL n 𝕜) :
    (Unitary.toUnits (iwasawaK g))⁻¹ * g ∈ upperPosSubgroup n 𝕜 := by
  have e : (((Unitary.toUnits (iwasawaK g))⁻¹ * g : GL n 𝕜) : Matrix n n 𝕜) =
      ((iwasawaK g : Matrix n n 𝕜))ᴴ * g := rfl
  rw [mem_upperPosSubgroup, e, iwasawaK_conjTranspose_mul]
  refine ⟨(blockTriangular_diagonal _).mul (iwasawaEquiv.symm g).2.2.2.1, fun i => ?_⟩
  rw [diagonal_mul, (iwasawaEquiv.symm g).2.2.2.2 i, mul_one]
  exact RCLike.ofReal_pos.2 ((iwasawaEquiv.symm g).2.1.2 i)

noncomputable def kbSplit (g : GL n 𝕜) : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜 :=
  (iwasawaK g, ⟨_, conjTranspose_iwasawaK_mul_mem g⟩)

theorem iwasawaK_kbMul (p : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜) :
    iwasawaK (kbMul p) = p.1 := by
  symm
  apply eq_iwasawaK_of_mem
  have e : ((p.1 : Matrix n n 𝕜))ᴴ * (kbMul p : Matrix n n 𝕜) = ((p.2 : GL n 𝕜) : Matrix n n 𝕜) := by
    show ((p.1 : Matrix n n 𝕜))ᴴ * ((p.1 : Matrix n n 𝕜) * ((p.2 : GL n 𝕜) : Matrix n n 𝕜)) = _
    rw [← Matrix.mul_assoc, show ((p.1 : Matrix n n 𝕜))ᴴ * p.1 = 1 from p.1.2.1, Matrix.one_mul]
  refine ⟨?_, fun i => ?_⟩
  · rw [e]; exact p.2.2.1
  · rw [e]
    obtain ⟨hre, him⟩ := RCLike.pos_iff.1 (p.2.2.2 i)
    exact ⟨hre.le, him⟩

noncomputable def kbHomeomorph : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜 ≃ₜ GL n 𝕜 where
  toFun := kbMul
  invFun := kbSplit
  left_inv p := by
    ext : 1
    · exact iwasawaK_kbMul p
    · apply Subtype.ext
      show (Unitary.toUnits (iwasawaK (kbMul p)))⁻¹ * (Unitary.toUnits p.1 * p.2) = p.2
      rw [iwasawaK_kbMul, inv_mul_cancel_left]
  right_inv g := by
    show Unitary.toUnits (iwasawaK g) * ((Unitary.toUnits (iwasawaK g))⁻¹ * g) = g
    rw [mul_inv_cancel_left]
  continuous_toFun := by
    have ht : Continuous (fun k : unitaryGroup n 𝕜 => Unitary.toUnits k) :=
      Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩
    exact (ht.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have ht : Continuous (fun k : unitaryGroup n 𝕜 => Unitary.toUnits k) :=
      Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩
    refine continuous_iwasawaK.prodMk (Continuous.subtype_mk ?_ _)
    exact ((ht.comp continuous_iwasawaK).inv).mul continuous_id

theorem kbHomeomorph_apply (p : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜) :
    kbHomeomorph p = Unitary.toUnits p.1 * p.2 := rfl

end Split

section HaarKB

open MeasureTheory Measure
open scoped ENNReal NNReal Matrix.Norms.L2Operator

instance : SecondCountableTopology (Matrix n n ℝ) :=
  inferInstanceAs (SecondCountableTopology (n → n → ℝ))

instance : SecondCountableTopology (GL n ℝ) :=
  (Units.isOpenEmbedding_val (R := Matrix n n ℝ)).isEmbedding.secondCountableTopology

instance : LocallyCompactSpace (GL n ℝ) :=
  (Units.isOpenEmbedding_val (R := Matrix n n ℝ)).locallyCompactSpace

instance : SecondCountableTopology (upperPosSubgroup n ℝ) :=
  TopologicalSpace.Subtype.secondCountableTopology _

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem isClosed_upperPosSubgroup : IsClosed (upperPosSubgroup n ℝ : Set (GL n ℝ)) := by
  have e : (upperPosSubgroup n ℝ : Set (GL n ℝ)) =
      (⋂ i, ⋂ j, {g : GL n ℝ | j < i → (g : Matrix n n ℝ) i j = 0}) ∩
        ⋂ i, {g : GL n ℝ | 0 ≤ (g : Matrix n n ℝ) i i} := by
    ext g
    simp only [SetLike.mem_coe, mem_upperPosSubgroup, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    constructor
    · rintro ⟨hU, hpos⟩; exact ⟨fun i j h => hU h, fun i => (hpos i).le⟩
    · rintro ⟨hU, hnn⟩
      have hU' : (g : Matrix n n ℝ).IsUpperTriangular := fun i j h => hU i j h
      refine ⟨hU', fun i => lt_of_le_of_ne (hnn i) (Ne.symm ?_)⟩
      have hdet := ((isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
      rw [det_of_isUpperTriangular hU'] at hdet
      exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
    (isClosed_iInter fun i => ?_)
  · by_cases h : j < i
    · simp only [h, forall_const]
      exact isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
    · simp only [h, IsEmpty.forall_iff, ofPred_true, isClosed_univ]
  · exact isClosed_le continuous_const (Units.continuous_val.matrix_elem i i)

instance : LocallyCompactSpace (upperPosSubgroup n ℝ) :=
  isClosed_upperPosSubgroup.locallyCompactSpace

noncomputable def kbInvHomeomorph : GL n ℝ ≃ₜ unitaryGroup n ℝ × upperPosSubgroup n ℝ :=
  kbHomeomorph.symm.trans ((Homeomorph.refl _).prodCongr (Homeomorph.inv _))

theorem kbInvHomeomorph_equivariant (q : unitaryGroup n ℝ × upperPosSubgroup n ℝ) (g : GL n ℝ) :
    kbInvHomeomorph (Unitary.toUnits q.1 * g * ((q.2 : GL n ℝ))⁻¹) = q * kbInvHomeomorph g := by
  obtain ⟨p, rfl⟩ := kbHomeomorph.surjective g
  have e : Unitary.toUnits q.1 * kbHomeomorph p * ((q.2 : GL n ℝ))⁻¹ =
      kbHomeomorph (q.1 * p.1, p.2 * q.2⁻¹) := by
    simp only [kbHomeomorph_apply, map_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  rw [e]
  simp only [kbInvHomeomorph, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  refine Prod.ext rfl ?_
  show (p.2 * q.2⁻¹)⁻¹ = q.2 * p.2⁻¹
  rw [_root_.mul_inv_rev, inv_inv]

theorem haarGLReal_eq_smul_map_kbHomeomorph (μ₀ : Measure (Matrix n n ℝ)) [μ₀.IsAddHaarMeasure]
    (μK : Measure (unitaryGroup n ℝ)) [μK.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n ℝ)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧
      haarGLReal μ₀ = c • Measure.map kbHomeomorph (μK.prod μB.inv) := by
  set H := haarGLReal μ₀ with hHdef
  set f := kbInvHomeomorph (n := n)
  set ν := Measure.map f H with hνdef
  have hν : ν.IsMulLeftInvariant := ⟨fun q => by
    rw [hνdef, Measure.map_map (measurable_const_mul q) f.measurable]
    have e1 : (fun x => q * x) ∘ f =
        f ∘ (fun g => Unitary.toUnits q.1 * g * ((q.2 : GL n ℝ))⁻¹) :=
      funext fun g => (kbInvHomeomorph_equivariant q g).symm
    have e2 : (fun g : GL n ℝ => Unitary.toUnits q.1 * g * ((q.2 : GL n ℝ))⁻¹) =
        (fun g => g * ((q.2 : GL n ℝ))⁻¹) ∘ (fun g => Unitary.toUnits q.1 * g) := rfl
    have hmT : Measurable (fun g : GL n ℝ => Unitary.toUnits q.1 * g * ((q.2 : GL n ℝ))⁻¹) := by
      rw [e2]; exact (measurable_mul_const _).comp (measurable_const_mul _)
    rw [e1, ← Measure.map_map f.measurable hmT, e2,
      ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self,
      map_mul_right_eq_self]⟩
  have hνc : IsFiniteMeasureOnCompacts ν := IsFiniteMeasureOnCompacts.map H f
  obtain ⟨c, key⟩ : ∃ c : ℝ≥0, ν = c • μK.prod μB :=
    ⟨_, isMulLeftInvariant_eq_smul ν (μK.prod μB)⟩
  have hH : H = Measure.map f.symm ν := by
    rw [hνdef, Measure.map_map f.symm.measurable f.measurable]
    simp
  refine ⟨c, ?_, ?_⟩
  · intro hc
    rw [hc, zero_smul] at key
    have h0 : H Set.univ = 0 := by rw [hH, key, Measure.map_zero, Measure.coe_zero, Pi.zero_apply]
    exact (IsOpenPosMeasure.open_pos Set.univ isOpen_univ Set.univ_nonempty) h0
  · rw [hH, key, Measure.map_smul c f.symm.measurable.aemeasurable]
    congr 1
    have e3 : ⇑f.symm = kbHomeomorph ∘ Prod.map id (fun b : upperPosSubgroup n ℝ => b⁻¹) := by
      funext p; rfl
    rw [e3, ← Measure.map_map kbHomeomorph.measurable (measurable_id.prodMap measurable_inv),
      ← Measure.map_prod_map _ _ measurable_id measurable_inv, Measure.map_id, Measure.inv_def]

theorem lintegral_haarGLReal_iwasawa (μ₀ : Measure (Matrix n n ℝ)) [μ₀.IsAddHaarMeasure]
    (μK : Measure (unitaryGroup n ℝ)) [μK.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n ℝ)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂(haarGLReal μ₀) =
        c * ∫⁻ k, ∫⁻ b, f (Unitary.toUnits k * b) ∂μB.inv ∂μK := by
  obtain ⟨c, hc, h⟩ := haarGLReal_eq_smul_map_kbHomeomorph μ₀ μK μB
  refine ⟨c, hc, fun f hf => ?_⟩
  rw [h, lintegral_smul_measure, lintegral_map hf kbHomeomorph.measurable]
  have := lintegral_prod (μ := μK) (ν := μB.inv) _ (hf.comp kbHomeomorph.measurable).aemeasurable
  simp only [Function.comp_def] at this
  rw [this, ENNReal.smul_def, smul_eq_mul]
  rfl

end HaarKB

end GroundTheory.Automorphic
end

namespace GroundTheory.Automorphic

open Matrix Set
open scoped ComplexOrder

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [LinearOrder n]

section HaarKBComplex

open MeasureTheory Measure
open scoped ENNReal NNReal Matrix.Norms.L2Operator

instance : SecondCountableTopology (Matrix n n ℂ) :=
  inferInstanceAs (SecondCountableTopology (n → n → ℂ))

instance : SecondCountableTopology (GL n ℂ) :=
  (Units.isOpenEmbedding_val (R := Matrix n n ℂ)).isEmbedding.secondCountableTopology

instance : LocallyCompactSpace (GL n ℂ) :=
  (Units.isOpenEmbedding_val (R := Matrix n n ℂ)).locallyCompactSpace

instance : SecondCountableTopology (upperPosSubgroup n ℂ) :=
  TopologicalSpace.Subtype.secondCountableTopology _

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem isClosed_upperPosSubgroupC : IsClosed (upperPosSubgroup n ℂ : Set (GL n ℂ)) := by
  have e : (upperPosSubgroup n ℂ : Set (GL n ℂ)) =
      (⋂ i, ⋂ j, {g : GL n ℂ | j < i → (g : Matrix n n ℂ) i j = 0}) ∩
        ⋂ i, {g : GL n ℂ | 0 ≤ (g : Matrix n n ℂ) i i} := by
    ext g
    simp only [SetLike.mem_coe, mem_upperPosSubgroup, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    constructor
    · rintro ⟨hU, hpos⟩; exact ⟨fun i j h => hU h, fun i => (hpos i).le⟩
    · rintro ⟨hU, hnn⟩
      have hU' : (g : Matrix n n ℂ).IsUpperTriangular := fun i j h => hU i j h
      refine ⟨hU', fun i => lt_of_le_of_ne (hnn i) (Ne.symm ?_)⟩
      have hdet := ((isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
      rw [det_of_isUpperTriangular hU'] at hdet
      exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
    (isClosed_iInter fun i => ?_)
  · by_cases h : j < i
    · simp only [h, forall_const]
      exact isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
    · simp only [h, IsEmpty.forall_iff, ofPred_true, isClosed_univ]
  · exact isClosed_le continuous_const (Units.continuous_val.matrix_elem i i)

instance : LocallyCompactSpace (upperPosSubgroup n ℂ) :=
  isClosed_upperPosSubgroupC.locallyCompactSpace

noncomputable def kbInvHomeomorphC : GL n ℂ ≃ₜ unitaryGroup n ℂ × upperPosSubgroup n ℂ :=
  kbHomeomorph.symm.trans ((Homeomorph.refl _).prodCongr (Homeomorph.inv _))

theorem kbInvHomeomorphC_equivariant (q : unitaryGroup n ℂ × upperPosSubgroup n ℂ) (g : GL n ℂ) :
    kbInvHomeomorphC (Unitary.toUnits q.1 * g * ((q.2 : GL n ℂ))⁻¹) = q * kbInvHomeomorphC g := by
  obtain ⟨p, rfl⟩ := kbHomeomorph.surjective g
  have e : Unitary.toUnits q.1 * kbHomeomorph p * ((q.2 : GL n ℂ))⁻¹ =
      kbHomeomorph (q.1 * p.1, p.2 * q.2⁻¹) := by
    simp only [kbHomeomorph_apply, map_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  rw [e]
  simp only [kbInvHomeomorphC, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  refine Prod.ext rfl ?_
  show (p.2 * q.2⁻¹)⁻¹ = q.2 * p.2⁻¹
  rw [_root_.mul_inv_rev, inv_inv]

theorem haarGLComplex_eq_smul_map_kbHomeomorph (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure]
    (μK : Measure (unitaryGroup n ℂ)) [μK.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n ℂ)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧
      haarGLComplex μ₀ = c • Measure.map kbHomeomorph (μK.prod μB.inv) := by
  set H := haarGLComplex μ₀ with hHdef
  set f := kbInvHomeomorphC (n := n)
  set ν := Measure.map f H with hνdef
  have hν : ν.IsMulLeftInvariant := ⟨fun q => by
    rw [hνdef, Measure.map_map (measurable_const_mul q) f.measurable]
    have e1 : (fun x => q * x) ∘ f =
        f ∘ (fun g => Unitary.toUnits q.1 * g * ((q.2 : GL n ℂ))⁻¹) :=
      funext fun g => (kbInvHomeomorphC_equivariant q g).symm
    have e2 : (fun g : GL n ℂ => Unitary.toUnits q.1 * g * ((q.2 : GL n ℂ))⁻¹) =
        (fun g => g * ((q.2 : GL n ℂ))⁻¹) ∘ (fun g => Unitary.toUnits q.1 * g) := rfl
    have hmT : Measurable (fun g : GL n ℂ => Unitary.toUnits q.1 * g * ((q.2 : GL n ℂ))⁻¹) := by
      rw [e2]; exact (measurable_mul_const _).comp (measurable_const_mul _)
    rw [e1, ← Measure.map_map f.measurable hmT, e2,
      ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self,
      map_mul_right_eq_self]⟩
  have hνc : IsFiniteMeasureOnCompacts ν := IsFiniteMeasureOnCompacts.map H f
  obtain ⟨c, key⟩ : ∃ c : ℝ≥0, ν = c • μK.prod μB :=
    ⟨_, isMulLeftInvariant_eq_smul ν (μK.prod μB)⟩
  have hH : H = Measure.map f.symm ν := by
    rw [hνdef, Measure.map_map f.symm.measurable f.measurable]
    simp
  refine ⟨c, ?_, ?_⟩
  · intro hc
    rw [hc, zero_smul] at key
    have h0 : H Set.univ = 0 := by rw [hH, key, Measure.map_zero, Measure.coe_zero, Pi.zero_apply]
    exact (IsOpenPosMeasure.open_pos Set.univ isOpen_univ Set.univ_nonempty) h0
  · rw [hH, key, Measure.map_smul c f.symm.measurable.aemeasurable]
    congr 1
    have e3 : ⇑f.symm = kbHomeomorph ∘ Prod.map id (fun b : upperPosSubgroup n ℂ => b⁻¹) := by
      funext p; rfl
    rw [e3, ← Measure.map_map kbHomeomorph.measurable (measurable_id.prodMap measurable_inv),
      ← Measure.map_prod_map _ _ measurable_id measurable_inv, Measure.map_id, Measure.inv_def]

theorem lintegral_haarGLComplex_iwasawa (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure]
    (μK : Measure (unitaryGroup n ℂ)) [μK.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n ℂ)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂(haarGLComplex μ₀) =
        c * ∫⁻ k, ∫⁻ b, f (Unitary.toUnits k * b) ∂μB.inv ∂μK := by
  obtain ⟨c, hc, h⟩ := haarGLComplex_eq_smul_map_kbHomeomorph μ₀ μK μB
  refine ⟨c, hc, fun f hf => ?_⟩
  rw [h, lintegral_smul_measure, lintegral_map hf kbHomeomorph.measurable]
  have := lintegral_prod (μ := μK) (ν := μB.inv) _ (hf.comp kbHomeomorph.measurable).aemeasurable
  simp only [Function.comp_def] at this
  rw [this, ENNReal.smul_def, smul_eq_mul]
  rfl

end HaarKBComplex

end GroundTheory.Automorphic
end

namespace GroundTheory.Automorphic

open Matrix Set
open scoped ComplexOrder NNReal

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]

section StrictUpper

variable (n) in
abbrev StrictUpperIndex := {p : n × n // p.1 < p.2}

def strictUpperMatrix (v : StrictUpperIndex n → 𝕜) : Matrix n n 𝕜 :=
  Matrix.of fun i j => if h : i < j then v ⟨(i, j), h⟩ else 0

def strictUpperCoords (X : Matrix n n 𝕜) : StrictUpperIndex n → 𝕜 := fun p => X p.1.1 p.1.2

def IsStrictUpper (X : Matrix n n 𝕜) : Prop := ∀ i j, j ≤ i → X i j = 0

theorem strictUpperMatrix_apply (v : StrictUpperIndex n → 𝕜) (i j : n) :
    strictUpperMatrix v i j = if h : i < j then v ⟨(i, j), h⟩ else 0 := rfl

@[simp] theorem strictUpperCoords_strictUpperMatrix (v : StrictUpperIndex n → 𝕜) :
    strictUpperCoords (strictUpperMatrix v) = v := by
  funext p
  simp [strictUpperCoords, strictUpperMatrix_apply, p.2]

theorem isStrictUpper_strictUpperMatrix (v : StrictUpperIndex n → 𝕜) :
    IsStrictUpper (strictUpperMatrix v) := by
  intro i j h
  simp [strictUpperMatrix_apply, not_lt.2 h]

theorem strictUpperMatrix_strictUpperCoords {X : Matrix n n 𝕜} (hX : IsStrictUpper X) :
    strictUpperMatrix (strictUpperCoords X) = X := by
  ext i j
  by_cases h : i < j
  · simp [strictUpperMatrix_apply, strictUpperCoords, h]
  · simp [strictUpperMatrix_apply, h, hX i j (not_lt.1 h)]

theorem strictUpperMatrix_add (v w : StrictUpperIndex n → 𝕜) :
    strictUpperMatrix (v + w) = strictUpperMatrix v + strictUpperMatrix w := by
  ext i j
  by_cases h : i < j <;> simp [strictUpperMatrix_apply, h]

theorem strictUpperMatrix_smul (c : 𝕜) (v : StrictUpperIndex n → 𝕜) :
    strictUpperMatrix (c • v) = c • strictUpperMatrix v := by
  ext i j
  by_cases h : i < j <;> simp [strictUpperMatrix_apply, h]

theorem strictUpperCoords_add (X Y : Matrix n n 𝕜) :
    strictUpperCoords (X + Y) = strictUpperCoords X + strictUpperCoords Y := rfl

theorem strictUpperCoords_smul (c : 𝕜) (X : Matrix n n 𝕜) :
    strictUpperCoords (c • X) = c • strictUpperCoords X := rfl

@[simp] theorem strictUpperCoords_one : strictUpperCoords (1 : Matrix n n 𝕜) = 0 := by
  funext p
  simp [strictUpperCoords, p.2.ne]

theorem IsStrictUpper.isUpperTriangular {X : Matrix n n 𝕜} (hX : IsStrictUpper X) :
    X.IsUpperTriangular := fun _ _ h => hX _ _ h.le

theorem IsStrictUpper.mul_right {X Y : Matrix n n 𝕜} (hX : IsStrictUpper X)
    (hY : Y.IsUpperTriangular) : IsStrictUpper (X * Y) := by
  intro i j hji
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases le_or_gt k i with hki | hik
  · rw [hX i k hki, zero_mul]
  · rw [hY (lt_of_le_of_lt hji hik), mul_zero]

private def rankBelow (i : n) : ℕ := (Finset.univ.filter (· < i)).card

private theorem rankBelow_lt_card (j : n) : rankBelow j < Fintype.card n := by
  refine Finset.card_lt_card ⟨Finset.subset_univ _, fun hsub => ?_⟩
  have := hsub (Finset.mem_univ j)
  simp at this

private theorem rank_add_le_of_pow_ne_zero {X : Matrix n n 𝕜} (hX : IsStrictUpper X) :
    ∀ (k : ℕ) (i j : n), (X ^ k) i j ≠ 0 → rankBelow i + k ≤ rankBelow j :=
  _root_.UpperTheory.Reformulated.B.StrictlyUpperRank.rank_add_le_of_pow_ne_zero hX

theorem IsStrictUpper.pow_card_eq_zero {X : Matrix n n 𝕜} (hX : IsStrictUpper X) :
    X ^ Fintype.card n = 0 := by
  ext i j
  by_contra h
  have h1 := rank_add_le_of_pow_ne_zero hX _ i j h
  have h2 := rankBelow_lt_card j
  omega

theorem continuous_strictUpperMatrix :
    Continuous (strictUpperMatrix : (StrictUpperIndex n → 𝕜) → Matrix n n 𝕜) := by
  refine continuous_matrix fun i j => ?_
  by_cases h : i < j
  · simp only [strictUpperMatrix_apply, h, dite_true]
    exact continuous_apply _
  · simp only [strictUpperMatrix_apply, h, dite_false]
    exact continuous_const

end StrictUpper

section Unipotent

def upperUnipotentSubgroup (n 𝕜 : Type*) [RCLike 𝕜] [Fintype n] [LinearOrder n] :
    Subgroup (GL n 𝕜) where
  carrier := {g | (g : Matrix n n 𝕜).IsUpperTriangular ∧ ∀ i, (g : Matrix n n 𝕜) i i = 1}
  mul_mem' {a b} ha hb := ⟨ha.1.mul hb.1, fun i => by
    rw [Units.val_mul, mul_apply_self_of_isUpperTriangular ha.1 hb.1, ha.2 i, hb.2 i, mul_one]⟩
  one_mem' := ⟨blockTriangular_one, fun i => by simp⟩
  inv_mem' {a} ha := by
    let : Invertible (a : Matrix n n 𝕜) :=
      invertibleOfIsUnitDet _ ((isUnit_iff_isUnit_det _).1 a.isUnit)
    have hinv : ((a⁻¹ : GL n 𝕜) : Matrix n n 𝕜) = (a : Matrix n n 𝕜)⁻¹ := coe_units_inv a
    have hU : ((a⁻¹ : GL n 𝕜) : Matrix n n 𝕜).IsUpperTriangular := by
      rw [hinv]; exact blockTriangular_inv_of_blockTriangular ha.1
    refine ⟨hU, fun i => ?_⟩
    have e0 : ((a⁻¹ : GL n 𝕜) : Matrix n n 𝕜) * (a : Matrix n n 𝕜) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e := congrFun (congrFun e0 i) i
    rw [mul_apply_self_of_isUpperTriangular hU ha.1, one_apply_eq, ha.2 i, mul_one] at e
    exact e

theorem mem_upperUnipotentSubgroup {g : GL n 𝕜} :
    g ∈ upperUnipotentSubgroup n 𝕜 ↔
      (g : Matrix n n 𝕜).IsUpperTriangular ∧ ∀ i, (g : Matrix n n 𝕜) i i = 1 := Iff.rfl

theorem upperUnipotentSubgroup_le_upperPosSubgroup :
    upperUnipotentSubgroup n 𝕜 ≤ upperPosSubgroup n 𝕜 := fun g hg =>
  ⟨hg.1, fun i => by rw [hg.2 i]; exact one_pos⟩

theorem isStrictUpper_sub_one {g : GL n 𝕜} (hg : g ∈ upperUnipotentSubgroup n 𝕜) :
    IsStrictUpper ((g : Matrix n n 𝕜) - 1) := by
  intro i j hji
  rcases hji.lt_or_eq with h | h
  · rw [Matrix.sub_apply, hg.1 h, one_apply_ne h.ne', sub_zero]
  · subst h; rw [Matrix.sub_apply, hg.2, one_apply_eq, sub_self]

def unipotentOfCoords (v : StrictUpperIndex n → 𝕜) : GL n 𝕜 where
  val := 1 + strictUpperMatrix v
  inv := ∑ k ∈ Finset.range (Fintype.card n), (-strictUpperMatrix v) ^ k
  val_inv := by
    have := mul_neg_geom_sum (-strictUpperMatrix v) (Fintype.card n)
    rwa [sub_neg_eq_add, neg_pow, (isStrictUpper_strictUpperMatrix v).pow_card_eq_zero, mul_zero,
      sub_zero] at this
  inv_val := by
    have := geom_sum_mul_neg (-strictUpperMatrix v) (Fintype.card n)
    rwa [sub_neg_eq_add, neg_pow, (isStrictUpper_strictUpperMatrix v).pow_card_eq_zero, mul_zero,
      sub_zero] at this

@[simp] theorem coe_unipotentOfCoords (v : StrictUpperIndex n → 𝕜) :
    ((unipotentOfCoords v : GL n 𝕜) : Matrix n n 𝕜) = 1 + strictUpperMatrix v := rfl

theorem unipotentOfCoords_mem (v : StrictUpperIndex n → 𝕜) :
    unipotentOfCoords v ∈ upperUnipotentSubgroup n 𝕜 := by
  refine ⟨blockTriangular_one.add (isStrictUpper_strictUpperMatrix v).isUpperTriangular,
    fun i => ?_⟩
  rw [coe_unipotentOfCoords, Matrix.add_apply, isStrictUpper_strictUpperMatrix v i i le_rfl, add_zero,
    one_apply_eq]

theorem strictUpperCoords_one_add (v : StrictUpperIndex n → 𝕜) :
    strictUpperCoords (1 + strictUpperMatrix v) = v := by
  rw [strictUpperCoords_add, strictUpperCoords_one, zero_add, strictUpperCoords_strictUpperMatrix]

theorem unipotentOfCoords_strictUpperCoords {g : GL n 𝕜} (hg : g ∈ upperUnipotentSubgroup n 𝕜) :
    unipotentOfCoords (strictUpperCoords (g : Matrix n n 𝕜)) = g := by
  apply Units.ext
  have e : strictUpperCoords (g : Matrix n n 𝕜) = strictUpperCoords ((g : Matrix n n 𝕜) - 1) := by
    rw [sub_eq_add_neg, strictUpperCoords_add, ← neg_one_smul 𝕜 (1 : Matrix n n 𝕜),
      strictUpperCoords_smul, strictUpperCoords_one, smul_zero, add_zero]
  rw [coe_unipotentOfCoords, e, strictUpperMatrix_strictUpperCoords (isStrictUpper_sub_one hg),
    add_sub_cancel]

def unipotentCoordsHomeomorph : (StrictUpperIndex n → 𝕜) ≃ₜ upperUnipotentSubgroup n 𝕜 where
  toFun v := ⟨unipotentOfCoords v, unipotentOfCoords_mem v⟩
  invFun u := strictUpperCoords ((u : GL n 𝕜) : Matrix n n 𝕜)
  left_inv v := strictUpperCoords_one_add v
  right_inv u := Subtype.ext (unipotentOfCoords_strictUpperCoords u.2)
  continuous_toFun := by
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · exact continuous_const.add continuous_strictUpperMatrix
    · show Continuous fun v : StrictUpperIndex n → 𝕜 =>
        ∑ k ∈ Finset.range (Fintype.card n), (-strictUpperMatrix v) ^ k
      exact continuous_finsetSum _ fun k _ => ((continuous_strictUpperMatrix (𝕜 := 𝕜) (n := n)).neg).pow k
  continuous_invFun :=
    continuous_pi fun p => (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _

@[simp] theorem coe_unipotentCoordsHomeomorph (v : StrictUpperIndex n → 𝕜) :
    ((unipotentCoordsHomeomorph v : upperUnipotentSubgroup n 𝕜) : GL n 𝕜) = unipotentOfCoords v :=
  rfl

theorem unipotentOfCoords_mul (v w : StrictUpperIndex n → 𝕜) :
    unipotentOfCoords v * unipotentOfCoords w =
      unipotentOfCoords (v + w + strictUpperCoords (strictUpperMatrix v * strictUpperMatrix w)) := by
  apply Units.ext
  have hS : IsStrictUpper (strictUpperMatrix v * strictUpperMatrix w) :=
    (isStrictUpper_strictUpperMatrix v).mul_right
      (isStrictUpper_strictUpperMatrix w).isUpperTriangular
  rw [Units.val_mul, coe_unipotentOfCoords, coe_unipotentOfCoords, coe_unipotentOfCoords,
    strictUpperMatrix_add, strictUpperMatrix_add, strictUpperMatrix_strictUpperCoords hS]
  noncomm_ring

end Unipotent

section Diag

def diagPosSubgroup (n 𝕜 : Type*) [RCLike 𝕜] [Fintype n] [DecidableEq n] :
    Subgroup (GL n 𝕜) where
  carrier := {g | ∃ a : n → ℝ, (∀ i, 0 < a i) ∧ (g : Matrix n n 𝕜) = diagonal fun i => (a i : 𝕜)}
  mul_mem' {g h} hg hh := by
    obtain ⟨a, ha, hga⟩ := hg
    obtain ⟨b, hb, hhb⟩ := hh
    refine ⟨a * b, fun i => mul_pos (ha i) (hb i), ?_⟩
    rw [Units.val_mul, hga, hhb, diagonal_mul_diagonal]
    simp
  one_mem' := ⟨fun _ => 1, fun _ => one_pos, by simp⟩
  inv_mem' {g} hg := by
    obtain ⟨a, ha, hga⟩ := hg
    refine ⟨a⁻¹, fun i => inv_pos.2 (ha i), ?_⟩
    have e1 : (diagonal fun i => (a i : 𝕜)) * (diagonal fun i => ((a⁻¹) i : 𝕜)) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      rw [Pi.inv_apply, RCLike.ofReal_inv]
      exact mul_inv_cancel₀ (RCLike.ofReal_ne_zero.2 (ha i).ne')
    calc ((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜)
        = ((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜) * ((g : Matrix n n 𝕜) *
            (diagonal fun i => ((a⁻¹) i : 𝕜))) := by rw [hga, e1, Matrix.mul_one]
      _ = diagonal fun i => ((a⁻¹) i : 𝕜) := by
            rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
              Matrix.one_mul]

theorem diagPosSubgroup_le_upperPosSubgroup : diagPosSubgroup n 𝕜 ≤ upperPosSubgroup n 𝕜 := by
  rintro g ⟨a, ha, hga⟩
  refine ⟨?_, fun i => ?_⟩
  · rw [hga]; exact blockTriangular_diagonal _
  · rw [hga, diagonal_apply_eq]; exact RCLike.ofReal_pos.2 (ha i)

def diagPosOf (a : PosDiag (n := n)) : GL n 𝕜 where
  val := diagonal fun i => (a.1 i : 𝕜)
  inv := diagonal fun i => ((a.1 i)⁻¹ : 𝕜)
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    exact mul_inv_cancel₀ (by exact_mod_cast (a.2 i).ne')
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    exact inv_mul_cancel₀ (by exact_mod_cast (a.2 i).ne')

@[simp] theorem coe_diagPosOf (a : PosDiag (n := n)) :
    ((diagPosOf a : GL n 𝕜) : Matrix n n 𝕜) = diagonal fun i => (a.1 i : 𝕜) := rfl

theorem coe_diagPosOf_inv (a : PosDiag (n := n)) :
    (((diagPosOf a)⁻¹ : GL n 𝕜) : Matrix n n 𝕜) = diagonal fun i => ((a.1 i)⁻¹ : 𝕜) := rfl

theorem diagPosOf_mem (a : PosDiag (n := n)) : diagPosOf a ∈ diagPosSubgroup n 𝕜 := ⟨a.1, a.2, rfl⟩

theorem re_pos_of_pos {z : 𝕜} (hz : 0 < z) : 0 < RCLike.re z := (RCLike.pos_iff.1 hz).1

theorem ofReal_re_of_pos {z : 𝕜} (hz : 0 < z) : ((RCLike.re z : ℝ) : 𝕜) = z := by
  obtain ⟨-, him⟩ := RCLike.pos_iff.1 hz
  conv_rhs => rw [← RCLike.re_add_im z, him]
  simp

theorem diag_pos_of_mem_diagPos {g : GL n 𝕜} (hg : g ∈ diagPosSubgroup n 𝕜) (i : n) :
    0 < (g : Matrix n n 𝕜) i i :=
  (diagPosSubgroup_le_upperPosSubgroup hg).2 i

theorem eq_diagonal_of_mem_diagPos {g : GL n 𝕜} (hg : g ∈ diagPosSubgroup n 𝕜) :
    (g : Matrix n n 𝕜) = diagonal fun i => ((RCLike.re ((g : Matrix n n 𝕜) i i) : ℝ) : 𝕜) := by
  obtain ⟨a, ha, hga⟩ := hg
  rw [hga]
  congr 1; funext i
  simp

def diagPosHomeomorph : PosDiag (n := n) ≃ₜ diagPosSubgroup n 𝕜 where
  toFun a := ⟨diagPosOf a, diagPosOf_mem a⟩
  invFun g := ⟨fun i => RCLike.re (((g : GL n 𝕜) : Matrix n n 𝕜) i i),
    fun i => re_pos_of_pos (diag_pos_of_mem_diagPos g.2 i)⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    simp
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    exact (eq_diagonal_of_mem_diagPos g.2).symm
  continuous_toFun := by
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · exact Continuous.matrix_diagonal (continuous_pi fun i =>
        RCLike.continuous_ofReal.comp ((continuous_apply i).comp continuous_subtype_val))
    · refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
      exact (RCLike.continuous_ofReal.comp ((continuous_apply i).comp
        continuous_subtype_val)).inv₀ fun a => RCLike.ofReal_ne_zero.2 (a.2 i).ne'
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
    exact RCLike.continuous_re.comp
      ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i i)

@[simp] theorem coe_diagPosHomeomorph (a : PosDiag (n := n)) :
    ((diagPosHomeomorph a : diagPosSubgroup n 𝕜) : GL n 𝕜) = diagPosOf a := rfl

theorem conj_unipotentOfCoords (a : PosDiag (n := n)) (v : StrictUpperIndex n → 𝕜) :
    diagPosOf a * unipotentOfCoords v * (diagPosOf a)⁻¹ =
      unipotentOfCoords (fun p => ((a.1 p.1.1 / a.1 p.1.2 : ℝ) : 𝕜) * v p) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagPosOf, coe_diagPosOf_inv, coe_unipotentOfCoords,
    coe_unipotentOfCoords]
  ext i j
  rw [mul_diagonal, diagonal_mul, Matrix.add_apply, Matrix.add_apply, Matrix.one_apply,
    strictUpperMatrix_apply, strictUpperMatrix_apply]
  by_cases hij : i = j
  · subst hij
    have h0 : (a.1 i : 𝕜) ≠ 0 := by exact_mod_cast (a.2 i).ne'
    simp [h0]
  · by_cases h : i < j
    · simp only [hij, h, ite_false, dite_true, zero_add]
      push_cast
      ring
    · simp [hij, h]

end Diag

section Borel

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

def upperPosDiagPart (b : upperPosSubgroup n 𝕜) : diagPosSubgroup n 𝕜 :=
  diagPosHomeomorph ⟨fun i => RCLike.re (((b : GL n 𝕜) : Matrix n n 𝕜) i i),
    fun i => re_pos_of_pos (b.2.2 i)⟩

theorem continuous_upperPosDiagPart :
    Continuous (upperPosDiagPart : upperPosSubgroup n 𝕜 → diagPosSubgroup n 𝕜) :=
  diagPosHomeomorph.continuous.comp (Continuous.subtype_mk (continuous_pi fun i =>
    RCLike.continuous_re.comp ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i i))
    _)

theorem upperPosDiagPart_inv_mul_mem (b : upperPosSubgroup n 𝕜) :
    ((upperPosDiagPart b : GL n 𝕜))⁻¹ * (b : GL n 𝕜) ∈ upperUnipotentSubgroup n 𝕜 := by
  have e : ((((upperPosDiagPart b : GL n 𝕜))⁻¹ * (b : GL n 𝕜) : GL n 𝕜) : Matrix n n 𝕜) =
      (diagonal fun i => ((RCLike.re (((b : GL n 𝕜) : Matrix n n 𝕜) i i))⁻¹ : 𝕜)) *
        ((b : GL n 𝕜) : Matrix n n 𝕜) := rfl
  rw [mem_upperUnipotentSubgroup, e]
  refine ⟨(blockTriangular_diagonal _).mul b.2.1, fun i => ?_⟩
  rw [diagonal_mul]
  rw [ofReal_re_of_pos (b.2.2 i)]
  exact inv_mul_cancel₀ (b.2.2 i).ne'

def upperPosUnipotentPart (b : upperPosSubgroup n 𝕜) : upperUnipotentSubgroup n 𝕜 :=
  ⟨_, upperPosDiagPart_inv_mul_mem b⟩

theorem continuous_upperPosUnipotentPart :
    Continuous (upperPosUnipotentPart : upperPosSubgroup n 𝕜 → upperUnipotentSubgroup n 𝕜) :=
  Continuous.subtype_mk ((continuous_subtype_val.comp continuous_upperPosDiagPart).inv.mul
    continuous_subtype_val) _

def diagUnipotentMul (p : diagPosSubgroup n 𝕜 × upperUnipotentSubgroup n 𝕜) :
    upperPosSubgroup n 𝕜 :=
  ⟨(p.1 : GL n 𝕜) * p.2, (upperPosSubgroup n 𝕜).mul_mem
    (diagPosSubgroup_le_upperPosSubgroup p.1.2) (upperUnipotentSubgroup_le_upperPosSubgroup p.2.2)⟩

@[simp] theorem coe_diagUnipotentMul (p : diagPosSubgroup n 𝕜 × upperUnipotentSubgroup n 𝕜) :
    ((diagUnipotentMul p : upperPosSubgroup n 𝕜) : GL n 𝕜) = (p.1 : GL n 𝕜) * p.2 := rfl

theorem upperPosDiagPart_diagUnipotentMul (p : diagPosSubgroup n 𝕜 × upperUnipotentSubgroup n 𝕜) :
    upperPosDiagPart (diagUnipotentMul p) = p.1 := by
  obtain ⟨⟨g, hg⟩, ⟨u, hu⟩⟩ := p
  apply Subtype.ext
  apply Units.ext
  show diagonal (fun i => ((RCLike.re (((g * u : GL n 𝕜) : Matrix n n 𝕜) i i) : ℝ) : 𝕜)) = g
  have hd : ∀ i, ((g * u : GL n 𝕜) : Matrix n n 𝕜) i i = (g : Matrix n n 𝕜) i i := by
    intro i
    rw [Units.val_mul, mul_apply_self_of_isUpperTriangular
      (diagPosSubgroup_le_upperPosSubgroup hg).1 hu.1, hu.2 i, mul_one]
  simp_rw [hd]
  exact (eq_diagonal_of_mem_diagPos hg).symm

theorem diagUnipotentMul_parts (b : upperPosSubgroup n 𝕜) :
    diagUnipotentMul (upperPosDiagPart b, upperPosUnipotentPart b) = b := by
  apply Subtype.ext
  show ((upperPosDiagPart b : GL n 𝕜)) * (((upperPosDiagPart b : GL n 𝕜))⁻¹ * b) = b
  rw [mul_inv_cancel_left]

def diagUnipotentHomeomorph :
    diagPosSubgroup n 𝕜 × upperUnipotentSubgroup n 𝕜 ≃ₜ upperPosSubgroup n 𝕜 where
  toFun := diagUnipotentMul
  invFun b := (upperPosDiagPart b, upperPosUnipotentPart b)
  left_inv p := by
    have h1 := upperPosDiagPart_diagUnipotentMul p
    refine Prod.ext h1 (Subtype.ext ?_)
    show ((upperPosDiagPart (diagUnipotentMul p) : GL n 𝕜))⁻¹ * ((p.1 : GL n 𝕜) * p.2) = p.2
    rw [h1, inv_mul_cancel_left]
  right_inv := diagUnipotentMul_parts
  continuous_toFun := Continuous.subtype_mk
    ((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)) _
  continuous_invFun := continuous_upperPosDiagPart.prodMk continuous_upperPosUnipotentPart

@[simp] theorem diagUnipotentHomeomorph_apply
    (p : diagPosSubgroup n 𝕜 × upperUnipotentSubgroup n 𝕜) :
    diagUnipotentHomeomorph p = diagUnipotentMul p := rfl

end Borel

section Delta

noncomputable def iwasawaDelta (g : GL n 𝕜) : ℝ≥0 :=
  ∏ p : StrictUpperIndex n,
    (‖(g : Matrix n n 𝕜) p.1.1 p.1.1‖₊ / ‖(g : Matrix n n 𝕜) p.1.2 p.1.2‖₊) ^ Module.finrank ℝ 𝕜

theorem iwasawaDelta_ne_zero {g : GL n 𝕜} (hg : g ∈ upperPosSubgroup n 𝕜) :
    iwasawaDelta g ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun p _ => pow_ne_zero _ (div_ne_zero ?_ ?_)
  · exact nnNorm_ne_zero_iff.2 (hg.2 _).ne'
  · exact nnNorm_ne_zero_iff.2 (hg.2 _).ne'

theorem iwasawaDelta_diagPosOf (a : PosDiag (n := n)) :
    (iwasawaDelta (diagPosOf a : GL n 𝕜) : ℝ) =
      ∏ p : StrictUpperIndex n, (a.1 p.1.1 / a.1 p.1.2) ^ Module.finrank ℝ 𝕜 := by
  simp only [iwasawaDelta, coe_diagPosOf, diagonal_apply_eq, NNReal.coe_prod, NNReal.coe_pow,
    NNReal.coe_div, coe_nnNorm, RCLike.norm_ofReal]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [abs_of_pos (a.2 _), abs_of_pos (a.2 _)]

theorem continuous_iwasawaDelta_diagPos :
    Continuous (fun a : diagPosSubgroup n 𝕜 => iwasawaDelta (a : GL n 𝕜)) := by
  have e : (fun a : diagPosSubgroup n 𝕜 => iwasawaDelta (a : GL n 𝕜)) =
      (fun a : PosDiag (n := n) => iwasawaDelta (diagPosOf a : GL n 𝕜)) ∘ diagPosHomeomorph.symm := by
    funext a
    conv_lhs => rw [← diagPosHomeomorph.apply_symm_apply a]
    rfl
  rw [e]
  refine Continuous.comp ?_ diagPosHomeomorph.symm.continuous
  refine continuous_induced_rng.2 ?_
  show Continuous fun a : PosDiag (n := n) => (iwasawaDelta (diagPosOf a : GL n 𝕜) : ℝ)
  simp_rw [iwasawaDelta_diagPosOf]
  refine continuous_finsetProd _ fun p _ => (Continuous.div ?_ ?_ fun a => (a.2 _).ne').pow _
  · exact (continuous_apply _).comp continuous_subtype_val
  · exact (continuous_apply _).comp continuous_subtype_val

end Delta

end GroundTheory.Automorphic
