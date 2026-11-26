module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ResCharIff

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarBox
noncomputable section

set_option linter.style.haveILetI false

open MeasureTheory Measure ValuativeRel Topology Filter Module
open scoped NNReal ENNReal Pointwise

namespace PI.ProdFormulaE.HaarBox

section Field

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem secondCountable : SecondCountableTopology K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  open scoped Valued in
  exact secondCountable_of_proper

variable {K}

theorem isOpen_ball (γ : ValueGroupWithZero K) (hγ : γ ≠ 0) :
    IsOpen {x : K | valuation K x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hx hy ⊢
  have h := (valuation K).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact h.trans (max_le hy.le hx)

theorem isCompact_ball (γ : ValueGroupWithZero K) : IsCompact {x : K | valuation K x ≤ γ} :=
  IsNonarchimedeanLocalField.isCompact_closedBall K γ

end Field

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def box (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) : Set E :=
  {x | ∀ i, valuation K (b.repr x i) ≤ γ i}

theorem continuous_coord (b : Basis ι K E) (i : ι) : Continuous fun x : E => b.repr x i := by
  have h := IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.toLinearMap
  exact (continuous_apply i).comp h

theorem continuous_equivFun_symm (b : Basis ι K E) : Continuous b.equivFun.symm := by
  haveI := IsModuleTopology.toContinuousAdd K E
  exact IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.symm.toLinearMap

theorem isOpen_box (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) (hγ : ∀ i, γ i ≠ 0) :
    IsOpen (box b γ) := by
  have e : box b γ = ⋂ i, (fun x : E => b.repr x i) ⁻¹' {a : K | valuation K a ≤ γ i} := by
    ext x
    simp [box]
  rw [e]
  exact isOpen_iInter_of_finite fun i => (isOpen_ball (γ i) (hγ i)).preimage (continuous_coord b i)

theorem box_eq_image (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) :
    box b γ = b.equivFun.symm '' Set.univ.pi (fun i => {a : K | valuation K a ≤ γ i}) := by
  have hr : ∀ y : ι → K, b.repr (b.equivFun.symm y) = y := fun y => by
    have h1 := b.equivFun.apply_symm_apply y
    rw [Basis.equivFun_apply] at h1
    exact h1
  ext x
  simp only [box, Set.mem_setOf_eq, Set.mem_image, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro h
    exact ⟨b.equivFun x, fun i => by simpa [Basis.equivFun_apply] using h i, by simp⟩
  · rintro ⟨y, hy, rfl⟩ i
    rw [hr]
    exact hy i

theorem isCompact_box (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) : IsCompact (box b γ) := by
  rw [box_eq_image]
  exact (isCompact_univ_pi fun i => isCompact_ball (γ i)).image (continuous_equivFun_symm b)

theorem zero_mem_box (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) : (0 : E) ∈ box b γ := by
  intro i
  simp

theorem locallyCompact (b : Basis ι K E) : LocallyCompactSpace E := by
  let e : E ≃ₜ (ι → K) :=
    { toEquiv := b.equivFun.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.toLinearMap
      continuous_invFun := continuous_equivFun_symm b }
  exact e.isOpenEmbedding.locallyCompactSpace

def homeo (b : Basis ι K E) : E ≃ₜ (ι → K) where
  toEquiv := b.equivFun.toEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.toLinearMap
  continuous_invFun := continuous_equivFun_symm b

theorem secondCountableE (b : Basis ι K E) : SecondCountableTopology E := by
  haveI := secondCountable K
  exact (homeo b).isEmbedding.secondCountableTopology

def toCLE (T : E ≃ₗ[K] E) : E ≃L[K] E :=
  haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd K E
  { T with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (R := K) T.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap (R := K) T.symm.toLinearMap }

variable [MeasurableSpace E] [BorelSpace E]

theorem image_eq_smul (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[K] E) :
    ∃ c : ℝ≥0, ∀ S : Set E, μ (T '' S) = c * μ S := by
  haveI : IsTopologicalAddGroup E := IsModuleTopology.topologicalAddGroup K E
  haveI := locallyCompact b
  haveI := secondCountableE b
  let L := toCLE T
  haveI : (μ.map L.symm).IsAddHaarMeasure := L.symm.isAddHaarMeasure_map μ
  refine ⟨addHaarScalarFactor (μ.map L.symm) μ, fun S => ?_⟩
  have h := isAddLeftInvariant_eq_smul (μ.map L.symm) μ
  have h2 : (μ.map L.symm) S = μ (T '' S) := by
    have hm : (μ.map L.symm) = μ.map (L.symm.toHomeomorph.toMeasurableEquiv) := rfl
    rw [hm, MeasurableEquiv.map_apply]
    have hL : ∀ x, L.symm x = T.symm x := fun x => rfl
    congr 1
    ext x
    simp only [Set.mem_preimage, Homeomorph.toMeasurableEquiv_coe,
      ContinuousLinearEquiv.coe_toHomeomorph, hL, Set.mem_image]
    constructor
    · intro hx; exact ⟨T.symm x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  have h' : (μ.map L.symm) S = _ := DFunLike.congr_fun h S
  rw [← h2, h']
  first | rfl | exact (nnreal_smul_coe_apply _ _ _) | simp

theorem image_eq_of_box (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[K] E)
    (γ : ι → ValueGroupWithZero K) (hγ : ∀ i, γ i ≠ 0) (c : ℝ≥0∞)
    (hc : μ (T '' box b γ) = c * μ (box b γ)) (S : Set E) : μ (T '' S) = c * μ S := by
  obtain ⟨c', hc'⟩ := image_eq_smul b μ T
  have hpos : μ (box b γ) ≠ 0 := (isOpen_box b γ hγ).measure_ne_zero μ ⟨0, zero_mem_box b γ⟩
  have hfin : μ (box b γ) ≠ ⊤ := (isCompact_box b γ).measure_lt_top.ne
  rw [hc' (box b γ)] at hc
  have hcc : ((c' : ℝ≥0∞)) = c := (ENNReal.mul_left_inj hpos hfin).mp hc
  rw [hc' S, hcc]

end PI.ProdFormulaE.HaarBox
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarMain
noncomputable section

open MeasureTheory Measure ValuativeRel Topology Module
open scoped NNReal ENNReal Pointwise

namespace PI.ProdFormulaE.HaarBox

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem modF_nonneg' (a : K) : 0 ≤ modF K a := by
  rcases eq_or_ne a 0 with h | h
  · rw [h, modF_zero]
  · exact (modF_pos h).le

variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def equivOfDet (b : Basis ι K E) (A : Matrix ι ι K) (hA : A.det ≠ 0) : E ≃ₗ[K] E :=
  LinearEquiv.ofIsUnitDet (f := Matrix.toLin b b A) (v := b) (v' := b)
    (by rw [LinearMap.toMatrix_toLin]; exact hA.isUnit)

theorem coe_equivOfDet (b : Basis ι K E) (A : Matrix ι ι K) (hA : A.det ≠ 0) :
    ⇑(equivOfDet b A hA) = Matrix.toLin b b A := rfl

variable [MeasurableSpace E] [BorelSpace E]

def ScaleBox (b : Basis ι K E) (μ : Measure E) : Prop :=
  ∀ (i : ι) (a : K) (ha : a ≠ 0),
    μ (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a)) '' box b 1) =
      (distribHaarChar K (Units.mk0 a ha) : ℝ≥0∞) * μ (box b 1)

def TransvBox (b : Basis ι K E) : Prop :=
  ∀ t : Matrix.TransvectionStruct ι K, ∃ γ : ι → ValueGroupWithZero K, (∀ i, γ i ≠ 0) ∧
    Matrix.toLin b b t.toMatrix '' box b γ = box b γ

private theorem measure_toLin_mul_image_of_forall (b : Basis ι K E) (μ : Measure E) (A B : Matrix ι ι K)
    (hA : ∀ S : Set E, μ (Matrix.toLin b b A '' S) = ENNReal.ofReal (modF K A.det) * μ S)
    (hB : ∀ S : Set E, μ (Matrix.toLin b b B '' S) = ENNReal.ofReal (modF K B.det) * μ S)
    (S : Set E) :
    μ (Matrix.toLin b b (A * B) '' S) = ENNReal.ofReal (modF K (A * B).det) * μ S := by
  rw [Matrix.toLin_mul b b b, LinearMap.coe_comp, Set.image_comp, hA, hB, Matrix.det_mul, modF_mul,
    ENNReal.ofReal_mul (modF_nonneg' _), mul_assoc]

private theorem measure_toLin_transvection_image (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (htrans : TransvBox b) (t : Matrix.TransvectionStruct ι K) (S : Set E) :
    μ (Matrix.toLin b b t.toMatrix '' S) = ENNReal.ofReal (modF K t.toMatrix.det) * μ S := by
  obtain ⟨γ, hγ, himg⟩ := htrans t
  have hdet : t.toMatrix.det ≠ 0 := by rw [Matrix.TransvectionStruct.det]; exact one_ne_zero
  rw [Matrix.TransvectionStruct.det, modF_one, ENNReal.ofReal_one, one_mul]
  have h := image_eq_of_box b μ (equivOfDet b t.toMatrix hdet) γ hγ 1
    (by rw [coe_equivOfDet, himg, one_mul]) S
  rwa [coe_equivOfDet, one_mul] at h

private theorem measure_toLin_diagonal_update_image (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hscale : ScaleBox b μ) (i : ι) (a : K) (ha : a ≠ 0) (S : Set E) :
    μ (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a)) '' S) =
      ENNReal.ofReal (modF K (Matrix.diagonal (Function.update (1 : ι → K) i a)).det) * μ S := by
  have hdetv : (Matrix.diagonal (Function.update (1 : ι → K) i a)).det = a := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  have hdet : (Matrix.diagonal (Function.update (1 : ι → K) i a)).det ≠ 0 := by
    rw [hdetv]
    exact ha
  rw [hdetv, modF_of_ne ha, ENNReal.ofReal_coe_nnreal]
  have h := image_eq_of_box b μ (equivOfDet b _ hdet) 1 (fun _ => by simp) _
    (by rw [coe_equivOfDet]; exact hscale i a ha) S
  rwa [coe_equivOfDet] at h

private theorem measure_toLin_diagonal_image (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hscale : ScaleBox b μ) (D : ι → K) (hD : ∀ i, D i ≠ 0) (S : Set E) :
    μ (Matrix.toLin b b (Matrix.diagonal D) '' S) =
      ENNReal.ofReal (modF K (Matrix.diagonal D).det) * μ S := by
  classical
  suffices h : ∀ s : Finset ι, ∀ D : ι → K, (∀ i, D i ≠ 0) → (∀ i ∉ s, D i = 1) → ∀ S : Set E,
      μ (Matrix.toLin b b (Matrix.diagonal D) '' S) =
        ENNReal.ofReal (modF K (Matrix.diagonal D).det) * μ S from
    h Finset.univ D hD (fun i hi => absurd (Finset.mem_univ i) hi) S
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro D _ h1 S
    have hD1 : D = 1 := funext fun i => h1 i (by simp)
    subst hD1
    have h1' : Matrix.diagonal (1 : ι → K) = 1 := Matrix.diagonal_one
    rw [h1', Matrix.toLin_one, LinearMap.id_coe, Set.image_id, Matrix.det_one, modF_one,
      ENNReal.ofReal_one, one_mul]
  | insert j s hj ih =>
    intro D h0 h1 S
    have hsplit : Matrix.diagonal D = Matrix.diagonal (Function.update D j 1) *
        Matrix.diagonal (Function.update 1 j (D j)) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases h : i = j
      · subst h; simp
      · simp [Function.update_of_ne h]
    rw [hsplit]
    refine measure_toLin_mul_image_of_forall b μ _ _ (ih _ ?_ ?_) (measure_toLin_diagonal_update_image b μ hscale j (D j) (h0 j)) S
    · intro i
      by_cases h : i = j
      · subst h; simp
      · simp [Function.update_of_ne h, h0 i]
    · intro i hi
      by_cases h : i = j
      · subst h; simp
      · rw [Function.update_of_ne h]
        exact h1 i (by simp [h, hi])

theorem image_toLin (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hscale : ScaleBox b μ) (htrans : TransvBox b)
    (A : Matrix ι ι K) (hA : A.det ≠ 0) (S : Set E) :
    μ (Matrix.toLin b b A '' S) = ENNReal.ofReal (modF K A.det) * μ S := by
  classical
  revert S
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ S : Set E, μ (Matrix.toLin b b M '' S) = ENNReal.ofReal (modF K M.det) * μ S)
    A hA ?_ ?_ ?_
  · intro D hD S
    refine measure_toLin_diagonal_image b μ hscale D (fun i => ?_) S
    rw [Matrix.det_diagonal] at hD
    exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
  · intro t S
    exact measure_toLin_transvection_image b μ htrans t S
  · intro A B _ _ hA hB S
    exact measure_toLin_mul_image_of_forall b μ A B hA hB S

end PI.ProdFormulaE.HaarBox

namespace PI.ProdFormulaE.HaarAlgP

open HaarBox

theorem haarAlg_of
    (hscale : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K] (E : Type) [AddCommGroup E] [Module K E] [TopologicalSpace E]
      [IsModuleTopology K E] [MeasurableSpace E] [BorelSpace E] (n : ℕ) (b : Basis (Fin n) K E)
      (μ : Measure E) [μ.IsAddHaarMeasure], ScaleBox b μ)
    (htrans : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K] (E : Type) [AddCommGroup E] [Module K E] [TopologicalSpace E]
      [IsModuleTopology K E] (n : ℕ) (b : Basis (Fin n) K E), TransvBox b) :
    St.HaarAlg := by
  intro K _ _ _ _ A _ _ _ _ _ _ _ _ μ _ y hy S
  classical
  let b := Module.finBasis K A
  set M := LinearMap.toMatrix b b (LinearMap.mulLeft K y) with hM
  have hdet : M.det = Algebra.norm K y := by
    rw [hM, LinearMap.det_toMatrix, Algebra.norm_apply]
    rfl
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]
    exact (hy.map (Algebra.norm K)).ne_zero
  have h := image_toLin b μ (hscale K A _ b μ) (htrans K A _ b) M hdet0 S
  rw [hdet, hM, Matrix.toLin_toMatrix] at h
  exact h

end PI.ProdFormulaE.HaarAlgP
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarScale
noncomputable section

set_option linter.style.haveILetI false

open MeasureTheory Measure ValuativeRel Topology Filter Module
open scoped NNReal ENNReal Pointwise

namespace PI.ProdFormulaE.HaarBox

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_ball_of_isCompact {C : Set K} (hC : IsCompact C) :
    ∃ y : K, y ≠ 0 ∧ C ⊆ {x | valuation K x ≤ valuation K y} := by
  classical
  have hopen : ∀ y : K, y ≠ 0 → IsOpen {x : K | valuation K x ≤ valuation K y} := by
    intro y hy
    have h := isOpen_box (Basis.singleton Unit K) (fun _ => valuation K y)
      (fun _ => (Valuation.ne_zero_iff _).mpr hy)
    convert h using 1
    ext x
    simp [box, Basis.singleton_repr]
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun y : {y : K // y ≠ 0} => {x : K | valuation K x ≤ valuation K y.1})
    (fun y => hopen y.1 y.2) (by
      intro x _
      by_cases hx : x = 0
      · refine Set.mem_iUnion.mpr ⟨⟨1, one_ne_zero⟩, ?_⟩
        simp [hx]
      · exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, show valuation K x ≤ valuation K x from le_rfl⟩)
  rcases t.eq_empty_or_nonempty with h0 | hne
  · refine ⟨1, one_ne_zero, fun x hx => ?_⟩
    have h1 := ht hx
    simp [h0] at h1
  · obtain ⟨y, hy, hmax⟩ := t.exists_max_image (fun y => valuation K y.1) hne
    refine ⟨y.1, y.2, fun x hx => ?_⟩
    have hx' := ht hx
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨y', hy', hxy'⟩ := hx'
    have hxy'' : valuation K x ≤ valuation K y'.1 := hxy'
    exact le_trans hxy'' (hmax y' hy')

variable [MeasurableSpace E] [BorelSpace E]

theorem scale_box (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure] (i : ι) (a : K)
    (ha : a ≠ 0) :
    μ (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a)) '' box b 1) =
      (distribHaarChar K (Units.mk0 a ha) : ℝ≥0∞) * μ (box b 1) := by
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  haveI : IsTopologicalAddGroup E := IsModuleTopology.topologicalAddGroup K E
  haveI := locallyCompact b
  haveI := secondCountableE b
  haveI := secondCountable K
  obtain ⟨c, hc⟩ : ∃ c : E → K, c = fun x => b.repr x i := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Set E, P = {x | ∀ j, j ≠ i → valuation K (b.repr x j) ≤ 1} :=
    ⟨_, rfl⟩
  have hcc : Continuous c := by rw [hc]; exact continuous_coord b i
  have hcm : Measurable c := hcc.measurable
  have hPo : IsOpen P := by
    have h : P = ⋂ j ∈ (Finset.univ.filter (· ≠ i)),
        (fun x : E => b.repr x j) ⁻¹' {z : K | valuation K z ≤ 1} := by
      rw [hP]; ext x; simp
    rw [h]
    exact isOpen_biInter_finset
      (fun j _ => (isOpen_ball 1 one_ne_zero).preimage (continuous_coord b j))
  let ν : Measure K := (μ.restrict P).map c
  have hνA : ∀ A : Set K, MeasurableSet A → ν A = μ (P ∩ c ⁻¹' A) := by
    intro A hA
    show ((μ.restrict P).map c) A = _
    rw [Measure.map_apply hcm hA, Measure.restrict_apply (hcm hA), Set.inter_comm]
  have hrepr_add : ∀ (t : K) (x : E) (j : ι),
      b.repr (t • b i + x) j = (if i = j then t else 0) + b.repr x j := by
    intro t x j
    rw [map_add (f := _), map_smul, Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_apply]
    split_ifs <;> simp
  haveI : ν.IsAddLeftInvariant := by
    refine ⟨fun t => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_add t) hA, hνA _ hA,
      hνA _ (measurable_const_add t hA)]
    have hset : P ∩ c ⁻¹' ((fun x => t + x) ⁻¹' A) =
        (fun x : E => t • b i + x) ⁻¹' (P ∩ c ⁻¹' A) := by
      ext x
      rw [hP, hc]
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, hrepr_add]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun j hj => by rw [if_neg (Ne.symm hj), zero_add]; exact h1 j hj, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨fun j hj => ?_, h2⟩
        have := h1 j hj
        rwa [if_neg (Ne.symm hj), zero_add] at this
    rw [hset, measure_preimage_add]
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun C hC => ?_⟩
    obtain ⟨y, hy0, hCy⟩ := exists_ball_of_isCompact hC
    have hyv : valuation K y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
    have hB : IsOpen {x : K | valuation K x ≤ valuation K y} := isOpen_ball _ hyv
    calc ν C ≤ ν {x | valuation K x ≤ valuation K y} := measure_mono hCy
      _ = μ (P ∩ c ⁻¹' {x | valuation K x ≤ valuation K y}) := hνA _ hB.measurableSet
      _ ≤ μ (box b (Function.update 1 i (valuation K y))) := by
          apply measure_mono
          rintro x ⟨hx1, hx2⟩ j
          by_cases hj : j = i
          · subst hj
            rw [Function.update_self]
            rw [Set.mem_preimage, hc] at hx2
            exact hx2
          · rw [Function.update_of_ne hj]
            rw [hP] at hx1
            exact hx1 j hj
      _ < ⊤ := (isCompact_box b _).measure_lt_top
  haveI : IsOpenPosMeasure ν := by
    refine ⟨fun U hU hne => ?_⟩
    obtain ⟨u, hu⟩ := hne
    rw [hνA U hU.measurableSet]
    have hO : IsOpen (P ∩ c ⁻¹' U) := hPo.inter (hU.preimage hcc)
    refine hO.measure_ne_zero μ ⟨u • b i, ?_, ?_⟩
    · rw [hP]
      intro j hj
      rw [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
        if_neg (Ne.symm hj), smul_zero, map_zero]
      exact zero_le'
    · rw [Set.mem_preimage, hc]
      simpa using hu
  haveI : ν.IsAddHaarMeasure := { }
  let g : Kˣ := Units.mk0 a ha
  have hOo : IsOpen {x : K | valuation K x ≤ 1} := isOpen_ball 1 one_ne_zero
  have hgO : IsOpen (g • {x : K | valuation K x ≤ 1}) := hOo.smul g
  have hscale : ν (g • {x : K | valuation K x ≤ 1}) =
      (distribHaarChar K g : ℝ≥0∞) * ν {x | valuation K x ≤ 1} := by
    have h1 : (DomMulAct.mk g • ν) {x : K | valuation K x ≤ 1} =
        ν (g • {x : K | valuation K x ≤ 1}) := by
      simp [domSMul_apply]
    rw [← h1, measure_isAddHaarMeasure_eq_smul_of_isOpen _ ν hOo,
      addHaarScalarFactor_smul_eq_distribHaarChar, ENNReal.smul_def, smul_eq_mul]
  have hrepr : ∀ (d : ι → K) (x : E) (j : ι),
      b.repr (Matrix.toLin b b (Matrix.diagonal d) x) j = d j * b.repr x j := by
    intro d x j
    rw [Matrix.repr_toLin, Matrix.mulVec_diagonal]
  have hR : box b 1 = P ∩ c ⁻¹' {x : K | valuation K x ≤ 1} := by
    ext x
    rw [hP, hc]
    constructor
    · intro h
      exact ⟨fun j _ => h j, h i⟩
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; exact h2
      · exact h1 j hj
  have hL : (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a))) '' box b 1 =
      P ∩ c ⁻¹' (g • {x : K | valuation K x ≤ 1}) := by
    ext y
    rw [hP, hc]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨fun j hj => ?_, ?_⟩
      · show valuation K (b.repr _ j) ≤ 1
        rw [hrepr, Function.update_of_ne hj, Pi.one_apply, one_mul]
        exact hx j
      · show b.repr _ i ∈ g • {x : K | valuation K x ≤ 1}
        rw [hrepr, Function.update_self]
        exact Set.mem_smul_set.2 ⟨b.repr x i, hx i, rfl⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨z, hz, hzy⟩ := Set.mem_smul_set.1 h2
      have hzy' : a * z = b.repr y i := hzy
      let T' := Matrix.toLin b b (Matrix.diagonal (Function.update (1 : ι → K) i a⁻¹))
      refine ⟨T' y, fun j => ?_, ?_⟩
      · show valuation K (b.repr (T' y) j) ≤ 1
        rw [hrepr]
        by_cases hj : j = i
        · subst hj
          rw [Function.update_self, ← hzy', ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
          exact hz
        · rw [Function.update_of_ne hj, Pi.one_apply, one_mul]
          exact h1 j hj
      · show Matrix.toLin b b _ (Matrix.toLin b b _ y) = y
        rw [← LinearMap.comp_apply, ← Matrix.toLin_mul, Matrix.diagonal_mul_diagonal]
        have hdd : (fun k => Function.update (1 : ι → K) i a k * Function.update (1 : ι → K) i a⁻¹ k) =
            (1 : ι → K) := by
          funext k
          by_cases hk : k = i
          · subst hk; simp [ha]
          · simp [Function.update_of_ne hk]
        rw [hdd, Pi.one_def, Matrix.diagonal_one, Matrix.toLin_one, LinearMap.id_apply]
  rw [hL, hR, ← hνA _ hgO.measurableSet, ← hνA _ hOo.measurableSet, hscale]

end PI.ProdFormulaE.HaarBox
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarTransv
noncomputable section

open ValuativeRel Module Matrix

namespace PI.ProdFormulaE.HaarBox

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem repr_toLin (b : Basis ι K E) (A : Matrix ι ι K) (x : E) :
    b.repr (Matrix.toLin b b A x) = A *ᵥ b.repr x := by
  have h := LinearMap.toMatrix_mulVec_repr b b (Matrix.toLin b b A) x
  rw [LinearMap.toMatrix_toLin] at h
  exact h.symm

theorem transvection_mulVec (t : Matrix.TransvectionStruct ι K) (v : ι → K) (k : ι) :
    (t.toMatrix *ᵥ v) k = v k + if k = t.i then t.c * v t.j else 0 := by
  simp only [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_mulVec,
    Matrix.one_mulVec, Pi.add_apply, add_right_inj]
  by_cases hk : k = t.i
  · rw [if_pos hk, hk]
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply, ite_mul]
  · rw [if_neg hk]
    simp [Matrix.mulVec, dotProduct, Ne.symm hk]

def tγ (t : Matrix.TransvectionStruct ι K) : ι → ValueGroupWithZero K :=
  Function.update 1 t.i (max (valuation K t.c) 1)

theorem tγ_inv (t : Matrix.TransvectionStruct ι K) : tγ t.inv = tγ t := by
  simp [tγ, Matrix.TransvectionStruct.inv, Valuation.map_neg]

private theorem tGamma_apply_of_ne (t : Matrix.TransvectionStruct ι K) {k : ι}
    (hk : k ≠ t.i) : tγ t k = 1 := by
  simp [tγ, hk]

private theorem tGamma_apply_self (t : Matrix.TransvectionStruct ι K) :
    tγ t t.i = max (valuation K t.c) 1 := by
  simp [tγ]

theorem toLin_mem_box (b : Basis ι K E) (t : Matrix.TransvectionStruct ι K) (x : E)
    (hx : x ∈ box b (tγ t)) : Matrix.toLin b b t.toMatrix x ∈ box b (tγ t) := by
  change ∀ k, valuation K (b.repr x k) ≤ tγ t k at hx
  change ∀ k, valuation K (b.repr (Matrix.toLin b b t.toMatrix x) k) ≤ tγ t k
  intro k
  have e : b.repr (Matrix.toLin b b t.toMatrix x) k
      = b.repr x k + if k = t.i then t.c * b.repr x t.j else 0 := by
    rw [congrFun (repr_toLin b t.toMatrix x) k, transvection_mulVec]
  rw [e]
  by_cases hk : k = t.i
  · rw [if_pos hk]
    have hj : valuation K (b.repr x t.j) ≤ 1 := by
      have h := hx t.j
      rwa [tGamma_apply_of_ne t t.hij.symm] at h
    have hR : tγ t k = max (valuation K t.c) 1 := by
      rw [hk]; exact tGamma_apply_self t
    have hxi : valuation K (b.repr x k) ≤ max (valuation K t.c) 1 := by
      rw [← hR]; exact hx k
    rw [hR]
    refine (Valuation.map_add _ _ _).trans (max_le hxi ?_)
    rw [Valuation.map_mul]
    calc valuation K t.c * valuation K (b.repr x t.j) ≤ valuation K t.c * 1 := by
          first
          | exact mul_le_mul_left' hj _
          | gcongr
      _ = valuation K t.c := mul_one _
      _ ≤ max (valuation K t.c) 1 := le_max_left _ _
  · rw [if_neg hk, add_zero]
    exact hx k

theorem transvection_box (b : Basis ι K E) (t : Matrix.TransvectionStruct ι K) :
    ∃ γ : ι → ValueGroupWithZero K, (∀ i, γ i ≠ 0) ∧
      Matrix.toLin b b t.toMatrix '' box b γ = box b γ := by
  refine ⟨tγ t, ?_, ?_⟩
  · intro i
    have h1 : (1 : ValueGroupWithZero K) ≤ tγ t i := by
      by_cases hi : i = t.i
      · rw [hi, tGamma_apply_self]
        exact le_max_right _ _
      · rw [tGamma_apply_of_ne t hi]
    exact (lt_of_lt_of_le zero_lt_one h1).ne'
  · apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact toLin_mem_box b t x hx
    · intro y hy
      refine ⟨Matrix.toLin b b t.inv.toMatrix y, ?_, ?_⟩
      · have h := toLin_mem_box b t.inv y (by rwa [tγ_inv])
        rwa [tγ_inv] at h
      · show ((Matrix.toLin b b t.toMatrix).comp (Matrix.toLin b b t.inv.toMatrix)) y = y
        rw [← Matrix.toLin_mul, Matrix.TransvectionStruct.mul_inv, Matrix.toLin_one,
          LinearMap.id_apply]

end PI.ProdFormulaE.HaarBox

end
end

namespace PI.ProdFormulaE.HaarAlgP

theorem haarScaling : St.HaarAlg := by
  refine haarAlg_of ?_ ?_
  · intro K _ _ _ _ E _ _ _ _ _ _ n b μ _ i a ha
    exact PI.ProdFormulaE.HaarBox.scale_box b μ i a ha
  · intro K _ _ _ _ E _ _ _ _ n b t
    exact PI.ProdFormulaE.HaarBox.transvection_box b t

end PI.ProdFormulaE.HaarAlgP
