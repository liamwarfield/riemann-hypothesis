module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsOnVacuumByAlgebraicScalar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingColumnArgsMovedPointConjAtPlace

@[expose] public section

attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlOrbitIntegralDepthDatumMemSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeDepthCompFrameBlockBoundedPeriodic
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeDepthCompFrameBlockBoundedPeriodic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host
open Matrix

namespace GlobalTheory.DepthBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unit_bound {ι : Type} [Fintype ι] (f : ι → k) :
    ∃ R : kˣ, ∀ i, valuation k (f i) ≤ valuation k (R : k) := by
  classical
  let γ : ValueGroupWithZero k := ∏ i, max 1 (valuation k (f i))
  have h1 : 1 ≤ γ := Finset.one_le_prod' (fun i _ => le_max_left _ _)
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective γ
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact absurd (hx ▸ h1) (not_le.2 zero_lt_one)
  refine ⟨Units.mk0 x hx0, fun i => ?_⟩
  rw [Units.val_mk0, hx]
  exact (le_max_right _ _).trans
    (Finset.single_le_prod' (f := fun j => max 1 (valuation k (f j))) (fun j _ => le_max_left _ _) (Finset.mem_univ i))

theorem frameMatrixSecondColumnBlock_mul_transpose {A A' D : Type} [Fintype A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (σ : A ⊕ A' ≃ D) : Y0 k σ * (Y0 k σ)ᵀ = 1 := by
  ext i j
  rw [frameMatrixSecondColumnBlock_mul_apply]
  by_cases hij : i = j
  · subst hij; simp [Y0]
  · simp [Y0, Matrix.one_apply, hij, Ne.symm hij]

theorem latticeDepth_comp_frameBlock_bounded_periodic : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (σ : A ⊕ A' ≃ D) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → ∀ (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}, HasDepth ϖ e (diagLat c) Ψ → ∀ h : GL D k, ∃ R : kˣ, ∃ N : ℕ, (∀ g : Matrix A' A' k, Ψ (g * (Y0 k σ * h.val)) ≠ 0 → ∀ i j, valuation k (g i j) ≤ valuation k (R : k)) ∧ ∀ g Z : Matrix A' A' k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ N : kˣ) : k)) → Ψ ((g + Z) * (Y0 k σ * h.val)) = Ψ (g * (Y0 k σ * h.val)) := by
  intro k _ _ _ _ A A' D _ _ _ _ _ _ σ ϖ e hϖ c Ψ hΨ h
  set Y : Matrix A' D k := Y0 k σ * h.val with hYdef
  set W : Matrix D A' k := (h⁻¹).val * (Y0 k σ)ᵀ with hWdef
  have hYW : Y * W = 1 := by
    rw [hYdef, hWdef, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, frameMatrixSecondColumnBlock_mul_transpose]
  obtain ⟨R, hR⟩ := exists_unit_bound (fun p : D × A' => (c p.1 : k) * W p.1 p.2)
  obtain ⟨R', hR'⟩ := exists_unit_bound (fun p : A' × D => Y p.1 p.2 / (((ϖ ^ e) * c p.2 : kˣ) : k))
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hR'0 : valuation k (R' : k) ≠ 0 := by simp
  obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt (Units.mk0 (valuation k (R' : k))⁻¹ (inv_ne_zero hR'0))
  have hN' : valuation k (ϖ : k) ^ N * valuation k (R' : k) ≤ 1 := by
    have : valuation k (ϖ : k) ^ N ≤ (valuation k (R' : k))⁻¹ := by simpa using hN.le
    calc valuation k (ϖ : k) ^ N * valuation k (R' : k)
        ≤ (valuation k (R' : k))⁻¹ * valuation k (R' : k) := mul_le_mul' this le_rfl
      _ = 1 := inv_mul_cancel₀ hR'0
  refine ⟨R, N, ?_, ?_⟩
  · intro g hg i j
    have hmem : g * Y ∈ matLat A' (diagLat c) := by
      by_contra hc; exact hg (hΨ.1 _ hc)
    have hg' : g = (g * Y) * W := by rw [Matrix.mul_assoc, hYW, Matrix.mul_one]
    rw [hg', Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    calc valuation k ((g * Y) i l) * valuation k (W l j)
        ≤ valuation k (c l : k) * valuation k (W l j) := mul_le_mul' (mem_diagLat.1 (hmem i) l) le_rfl
      _ = valuation k ((c l : k) * W l j) := (map_mul _ _ _).symm
      _ ≤ valuation k (R : k) := hR (l, j)
  · intro g Z hZ
    rw [Matrix.add_mul]
    refine hΨ.2 _ _ fun i => ?_
    rw [smul_diagLat, mem_diagLat]
    intro m
    show valuation k ((Z * Y) i m) ≤ _
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    have hpos : 0 < valuation k ((((ϖ ^ e) * c m : kˣ)) : k) := zero_lt_iff.2 (by simp)
    have h1 := hR' (l, m)
    simp only at h1
    rw [map_div₀, div_le_iff₀ hpos] at h1
    have hz : valuation k (Z i l) ≤ valuation k (ϖ : k) ^ N := by
      simpa [Units.val_pow_eq_pow_val, map_pow] using hZ i l
    calc valuation k (Z i l) * valuation k (Y l m)
        ≤ valuation k (ϖ : k) ^ N * (valuation k (R' : k) * valuation k ((((ϖ ^ e) * c m : kˣ)) : k)) :=
          mul_le_mul' hz h1
      _ = (valuation k (ϖ : k) ^ N * valuation k (R' : k)) * valuation k ((((ϖ ^ e) * c m : kˣ)) : k) :=
          (mul_assoc _ _ _).symm
      _ ≤ 1 * valuation k ((((ϖ ^ e) * c m : kˣ)) : k) := mul_le_mul' hN' le_rfl
      _ = _ := one_mul _

end GlobalTheory.DepthBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeDepthCompFrameBlockBoundedPeriodicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuation_bound_and_periodic_frameBlock : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (σ : A ⊕ A' ≃ D) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → ∀ (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}, HasDepth ϖ e (diagLat c) Ψ → ∀ h : GL D k, ∃ R : kˣ, ∃ N : ℕ, (∀ g : Matrix A' A' k, Ψ (g * (Y0 k σ * h.val)) ≠ 0 → ∀ i j, valuation k (g i j) ≤ valuation k (R : k)) ∧ ∀ g Z : Matrix A' A' k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ N : kˣ) : k)) → Ψ ((g + Z) * (Y0 k σ * h.val)) = Ψ (g * (Y0 k σ * h.val)) := by
  first | exact @GlobalTheory.DepthBound.latticeDepth_comp_frameBlock_bounded_periodic | exact GlobalTheory.DepthBound.latticeDepth_comp_frameBlock_bounded_periodic | (intros; apply GlobalTheory.DepthBound.latticeDepth_comp_frameBlock_bounded_periodic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlOrbitIntegralDepthDatumMemSubfield
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

namespace GlobalTheory.SmallFInF

section Helpers
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_valLe (c : kˣ) : IsOpen {t : k | valuation k t ≤ valuation k (c : k)} := by
  have h0 : 0 < valuation k (c : k) := zero_lt_iff.2 (by simp)
  have e : {t : k | valuation k t ≤ valuation k (c : k)} = (fun t => t / (c : k)) ⁻¹' (𝒪[k] : Set k) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff, map_div₀,
      div_le_one₀ h0]
  rw [e]
  exact IsOpen.preimage (continuous_id.div_const _) Valuation.isOpen_integer

theorem isOpen_cosetM {n m : Type} [Fintype n] [Fintype m] (c : kˣ) (x : Matrix n m k) :
    IsOpen {y : Matrix n m k | ∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)} := by
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (isOpen_valLe c).preimage (f := fun y : Matrix n m k => y i j - x i j) (by fun_prop)

theorem isCompact_ballM {n : Type} [Fintype n] (R : kˣ) :
    IsCompact {y : Matrix n n k | ∀ i j, valuation k (y i j) ≤ valuation k (R : k)} := by
  have h0 : 0 < valuation k (R : k) := zero_lt_iff.2 (by simp)
  have e : {y : Matrix n n k | ∀ i j, valuation k (y i j) ≤ valuation k (R : k)} =
      (fun z : Matrix n n k => (R : k) • z) '' {A | ∀ i j, A i j ∈ 𝒪[k]} := by
    ext y
    constructor
    · intro hy
      refine ⟨(R : k)⁻¹ • y, fun i j => ?_, ?_⟩
      · rw [Valuation.mem_integer_iff]
        simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
        rw [inv_mul_le_iff₀ h0, mul_one]; exact hy i j
      · simp [smul_smul]
    · rintro ⟨z, hz, rfl⟩ i j
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
      exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hz i j))
  rw [e]
  exact isCompact_intMatrix.image (continuous_const_smul _)

end Helpers

theorem smallF_mem : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (F : Subfield ℂ) {J : Subgroup (GL A' k)}, IsOpen (J : Set (GL A' k)) → J ≤ KO k A' → ∀ (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → 1 ≤ e → CondLE ϖ e ν → ¬ IsUnram ν → (∀ u, (ν u : ℂ) ∈ F) → (∀ u : kˣ, apow u (1 / 2) ∈ F) → ∀ (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}, HasDepth ϖ e (diagLat c) Ψ → (∀ X, Ψ X ∈ F) → ∀ h : GL D k, smallF (haarVol J) ν Ψ (Y0 k σ * h.val) ∈ F := by
  intro k _ _ _ _ _ _ A A' D _ _ _ _ _ _ F J hJo hJK σ ν ϖ e hϖ he hcond hram hνF hapF c Ψ hΨ hΨF h
  haveI := isHaarMeasure_haarVol hJo hJK
  obtain ⟨R, N, hbd, hper⟩ := GlobalTheory.T.exists_valuation_bound_and_periodic_frameBlock σ hϖ c hΨ h
  set Y := Y0 k σ * h.val with hY
  set cN : kˣ := ϖ ^ N with hcN
  set z : ℂ := (Fintype.card D : ℂ) / 2 with hz
  have hzF : ∀ u : kˣ, apow u z ∈ F := fun u => by
    have : apow u z = (apow u (1 / 2)) ^ (Fintype.card D) := by
      simp only [apow, hz]
      rw [← Complex.cpow_nat_mul]; congr 1; ring
    rw [this]; exact pow_mem (hapF u) _
  let Cs : Matrix A' A' k → Set (GL A' k) :=
    fun x => {g | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (cN : k)}
  have hCs_meas : ∀ x, MeasurableSet (Cs x) := fun x =>
    ((isOpen_cosetM cN x).preimage Units.continuous_val).measurableSet
  have hCs_eq : ∀ x y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (cN : k)) →
      Cs x = Cs y := by
    intro x y hxy
    ext g
    simp only [Cs, Set.mem_setOf_eq]
    constructor
    · intro hg i j
      have := Valuation.map_add_le (valuation k) (hg i j) ((Valuation.map_sub_swap _ _ _).le.trans (hxy i j))
      simpa using this
    · intro hg i j
      have := Valuation.map_add_le (valuation k) (hg i j) (hxy i j)
      simpa using this
  have hcoset : ∀ x, ∫ g in Cs x, (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol J) ∈ F := by
    intro x
    by_cases hs : ∃ y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (cN : k)) ∧ y.det = 0
    · obtain ⟨y, hy, hy0⟩ := hs
      rw [hCs_eq x y hy]
      haveI : @MeasureTheory.Measure.IsMulLeftInvariant (GL A' k)
          (@Units.instMeasurableSpace (Matrix A' A' k) _
            GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix)
          _ (haarVol J) :=
        @MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant _ _ _ _ (haarVol J)
          (isHaarMeasure_haarVol hJo hJK)
      erw [GlobalTheory.T.integral_ramifiedChar_det_singularMatrixCoset_eq_zero (haarVol J) ν z hram cN y hy0]
      exact F.zero_mem
    · push_neg at hs
      exact GlobalTheory.T.integral_detChar_invertibleMatrixBall_mem_subfield F hJo hJK ν z hϖ hcond hνF hzF cN x hs

  let L : AddSubgroup (Matrix A' A' k) :=
    { carrier := {Z | ∀ i j, valuation k (Z i j) ≤ valuation k (cN : k)}
      add_mem' := fun ha hb i j => Valuation.map_add_le _ (ha i j) (hb i j)
      zero_mem' := fun i j => by simp
      neg_mem' := fun ha i j => by simpa using ha i j }
  let q : Matrix A' A' k → Matrix A' A' k ⧸ L := QuotientAddGroup.mk
  have hq : ∀ x y : Matrix A' A' k, q x = q y ↔ ∀ i j, valuation k (x i j - y i j) ≤ valuation k (cN : k) := by
    intro x y
    rw [QuotientAddGroup.eq]
    refine forall₂_congr fun i j => ?_
    show valuation k ((-x + y) i j) ≤ _ ↔ _
    rw [show (-x + y) i j = -(x i j - y i j) by simp; ring, Valuation.map_neg]

  obtain ⟨T0, hT0⟩ := (isCompact_ballM (n := A') R).elim_finite_subcover
    (fun y : Matrix A' A' k => {x : Matrix A' A' k | ∀ i j, valuation k (x i j - y i j) ≤ valuation k (cN : k)})
    (fun y => isOpen_cosetM cN y)
    (fun x _ => Set.mem_iUnion.2 ⟨x, fun i j => by simp⟩)
  classical
  let T : Finset (Matrix A' A' k ⧸ L) := T0.image q
  set f : GL A' k → ℂ := fun g => Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) z with hf
  have hdec : f = fun g => ∑ t ∈ T, ({g : GL A' k | q g.val = t}).indicator f g := by
    funext g
    by_cases h0 : f g = 0
    · rw [h0]; symm
      refine Finset.sum_eq_zero fun t _ => ?_
      simp [Set.indicator_apply, h0]
    · have hΨ0 : Ψ (g.val * Y) ≠ 0 := fun h1 => h0 (by simp [hf, h1])
      have hB := hbd g.val hΨ0
      obtain ⟨y, hyT, hy⟩ := Set.mem_iUnion₂.1 (hT0 hB)
      have hqt : q g.val ∈ T := Finset.mem_image.2 ⟨y, hyT, ((hq _ _).2 hy).symm⟩
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rw [Finset.sum_ite_eq]
      simp [hqt]
  show ∫ g, Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card D : ℂ) / 2) ∂(haarVol J) ∈ F
  change ∫ g, f g ∂(haarVol J) ∈ F
  by_cases hint : Integrable f (haarVol J)
  · have hmeas : ∀ t, MeasurableSet {g : GL A' k | q g.val = t} := by
      intro t
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective t
      have : {g : GL A' k | q g.val = q y} = Cs y := by
        ext g; simp only [Set.mem_setOf_eq, Cs]; exact hq _ _
      rw [this]; exact hCs_meas y
    rw [hdec, integral_finsetSum _ (fun t _ => hint.indicator (hmeas t))]
    refine sum_mem fun t _ => ?_
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective t
    have hset : {g : GL A' k | q g.val = q y} = Cs y := by
      ext g; simp only [Set.mem_setOf_eq, Cs]; exact hq _ _
    rw [integral_indicator (hmeas _), hset]
    have hc : ∫ g in Cs y, f g ∂(haarVol J) =
        ∫ g in Cs y, Ψ (y * Y) * ((ν (gdet g) : ℂ) * apow (gdet g) z) ∂(haarVol J) := by
      refine setIntegral_congr_fun (hCs_meas y) fun g hg => ?_
      have h1 : g.val = y + (g.val - y) := by abel
      have h2 : Ψ (g.val * Y) = Ψ (y * Y) := by
        rw [h1, hper y (g.val - y) (fun i j => hg i j)]
      simp only [hf, h2, mul_assoc]
    rw [hc, integral_const_mul]
    exact F.mul_mem (hΨF _) (hcoset y)
  · rw [integral_undef hint]; exact F.zero_mem

end GlobalTheory.SmallFInF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlOrbitIntegralDepthDatumMemSubfieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glOrbitIntegral_depthDatum_mem_subfield : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (F : Subfield ℂ) {J : Subgroup (GL A' k)}, IsOpen (J : Set (GL A' k)) → J ≤ KO k A' → ∀ (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → 1 ≤ e → CondLE ϖ e ν → ¬ IsUnram ν → (∀ u, (ν u : ℂ) ∈ F) → (∀ u : kˣ, apow u (1 / 2) ∈ F) → ∀ (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}, HasDepth ϖ e (diagLat c) Ψ → (∀ X, Ψ X ∈ F) → ∀ h : GL D k, smallF (haarVol J) ν Ψ (Y0 k σ * h.val) ∈ F := by
  first | exact @GlobalTheory.SmallFInF.smallF_mem | exact GlobalTheory.SmallFInF.smallF_mem | (intros; apply GlobalTheory.SmallFInF.smallF_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilTraceAddCharAtPlaceMemSubfieldOfRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilTraceAddCharAtPlaceMemSubfieldOfRoots
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

namespace GlobalTheory.FunObj

theorem psiAt_mem_subfield_of_roots : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Subfield ℂ) {W : G.Weil} {w : Pl D.host.E}, (∀ z : ℂ, z ^ (Ideal.absNorm w.asIdeal ^ depthAt G w) = 1 → z ∈ F) → HasConductor (psiAt W w) 1 → ∀ (x : Kw w), valuation (Kw w) ((((unifAt w) ^ depthAt G w : (Kw w)ˣ) : Kw w) * x) ≤ 1 → (psiAt W w x : ℂ) ∈ F := by
  intro D T L sc G F W w hF hc x hx
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
  set q := Ideal.absNorm w.asIdeal
  set n := depthAt G w
  have hq : Valued.v ((q : ℕ) : Kw w) ≤ WithZero.exp (-1 : ℤ) := by
    have hmem : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem w.asIdeal
    have h2 : Valued.v ((q : ℕ) : Kw w) = w.intValuation ((q:ℕ) : 𝓞 D.host.E) := by
      rw [← map_natCast (algebraMap (𝓞 D.host.E) (Kw w))]
      exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.E) w _).trans
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _)
    rw [h2]
    have := (w.intValuation_le_pow_iff_mem ((q:ℕ) : 𝓞 D.host.E) 1).2 hmem
    simpa using this
  have hu : Valued.v ((unifAt w : (Kw w)ˣ) : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  have hx' : Valued.v ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1 := by
    have := (e ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) 1).1 (by rw [map_one]; exact hx)
    rwa [map_one] at this
  have hNx : Valued.v (((q ^ n : ℕ) : Kw w) * x) ≤ 1 := by
    refine le_trans ?_ hx'
    rw [map_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Nat.cast_pow, map_pow, hu]
    gcongr
  have hNx2 : valuation (Kw w) (((q ^ n : ℕ) : Kw w) * x) ≤ valuation (Kw w) 1 :=
    (e (((q ^ n : ℕ) : Kw w) * x) 1).2 (by rw [map_one]; exact hNx)
  have h1 : psiAt W w ((q ^ n) • x) = 1 := by
    rw [nsmul_eq_mul]
    exact (hc 1).2 (by simp) _ hNx2
  apply hF
  rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, h1, Circle.coe_one]

end GlobalTheory.FunObj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilTraceAddCharAtPlaceMemSubfieldOfRootsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilTraceAddCharAtPlace_mem_subfield_of_roots : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Subfield ℂ) {W : G.Weil} {w : Pl D.host.E}, (∀ z : ℂ, z ^ (Ideal.absNorm w.asIdeal ^ depthAt G w) = 1 → z ∈ F) → HasConductor (psiAt W w) 1 → ∀ (x : Kw w), valuation (Kw w) ((((unifAt w) ^ depthAt G w : (Kw w)ˣ) : Kw w) * x) ≤ 1 → (psiAt W w x : ℂ) ∈ F := by
  first | exact @GlobalTheory.FunObj.psiAt_mem_subfield_of_roots | exact GlobalTheory.FunObj.psiAt_mem_subfield_of_roots | (intros; apply GlobalTheory.FunObj.psiAt_mem_subfield_of_roots <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedAbsComplexPowHalfMemSubfieldOfSqrtNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedAbsComplexPowHalfMemSubfieldOfSqrtNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

noncomputable section

namespace GlobalTheory.HalfPowField

theorem apow_half_mem_of_sqrt : ∀ {D : D7} (F : Subfield ℂ) (w : Pl D.host.E), ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ F → ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ F := by
  intro D F w hs u
  simpa using GlobalTheory.MovedField.apow_half_mem hs u 1

end GlobalTheory.HalfPowField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedAbsComplexPowHalfMemSubfieldOfSqrtNormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedAbsComplexPow_half_mem_subfield_of_sqrt_norm : ∀ {D : D7} (F : Subfield ℂ) (w : Pl D.host.E), ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ F → ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ F := by
  first | exact @GlobalTheory.HalfPowField.apow_half_mem_of_sqrt | exact GlobalTheory.HalfPowField.apow_half_mem_of_sqrt | (intros; apply GlobalTheory.HalfPowField.apow_half_mem_of_sqrt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathLocalTotalTensorMemCoefficientField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TflipField

section Generic

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]


omit [MeasurableSpace k] [BorelSpace k] in
theorem apow_nat_half_mem (F : Subfield ℂ) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F) (x : kˣ) (n : ℕ) :
    apow x ((n : ℂ) / 2) ∈ F := by
  have : apow x ((n : ℂ) / 2) = apow x (1 / 2) ^ n := by
    rw [apow, apow, ← Complex.cpow_nat_mul]; congr 1; ring
  rw [this]; exact F.pow_mem (habs x) n


omit [MeasurableSpace k] [BorelSpace k] in
theorem fourierSum_mem {A D : Type} [Fintype A] [DecidableEq A] [DecidableEq D] (F : Subfield ℂ) (ψ : AddChar k Circle)
    (ϖ : kˣ) (e : ℕ) (P : Finset D) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ F)
    {Φ : Matrix A D k → ℂ} (hΦ : ∀ X, Φ X ∈ F) (Y : Matrix A D k) : fourierSum ψ ϖ e P Φ Y ∈ F := by
  classical
  rw [fourierSum_apply]
  split_ifs with h
  · refine F.mul_mem (F.inv_mem (F.pow_mem (natCast_mem F _) _)) (F.sum_mem fun T _ => F.mul_mem (hΦ _) (hψ _ ?_))
    rw [← Valuation.mem_integer_iff]
    change _ ∈ 𝒪[k]
    rw [pairCols, Finset.mul_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Finset.mul_sum]
    refine Subring.sum_mem _ fun j _ => ?_
    rw [mul_left_comm]
    exact Subring.mul_mem _ (liftRes_mem T i j) (h i j j.2)
  · exact F.zero_mem


omit [MeasurableSpace k] [BorelSpace k] in
theorem invFourierSum_inv_mem {A D : Type} [Fintype A] [DecidableEq A] [DecidableEq D] (F : Subfield ℂ) (ψ : AddChar k Circle)
    (ϖ : kˣ) (e : ℕ) (P : Finset D) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ F)
    {Φ : Matrix A D k → ℂ} (hΦ : ∀ X, Φ X ∈ F) (T : Matrix A D k) : invFourierSum ψ⁻¹ ϖ e P Φ T ∈ F := by
  classical
  rw [invFourierSum_inv_apply]
  split_ifs with h
  · refine F.sum_mem fun S _ => F.mul_mem (hΦ _) (hψ _ ?_)
    rw [← Valuation.mem_integer_iff]
    change _ ∈ 𝒪[k]
    have e1 : ((ϖ ^ e : kˣ) : k) * pairCols P T ((ϖ ^ e)⁻¹ • liftRes S) = ∑ i, ∑ j : P, liftRes S i j * T i j := by
      rw [pairCols, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_apply, Units.smul_def, smul_eq_mul, ← mul_assoc, ← mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_mul]
    rw [e1]
    exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (liftRes_mem S i j) (h i j j.2)
  · exact F.zero_mem

theorem smallF_mem {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (F : Subfield ℂ) {J : Subgroup (GL A' k)} (hJo : IsOpen (J : Set (GL A' k))) (hJK : J ≤ KO k A')
    (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (he : 1 ≤ e) (hν : CondLE ϖ e ν) (hram : ¬ IsUnram ν)
    (hνF : ∀ u, (ν u : ℂ) ∈ F) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F) (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}
    (hΨ : HasDepth ϖ e (diagLat c) Ψ) (hΨF : ∀ X, Ψ X ∈ F) (h : GL D k) :
    smallF (haarVol J) ν Ψ (Y0 k σ * h.val) ∈ F :=
  GlobalTheory.T.glOrbitIntegral_depthDatum_mem_subfield F hJo hJK σ ν hϖ he hν hram hνF habs c hΨ hΨF h

theorem phiA_mem {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (F : Subfield ℂ) {J : Subgroup (GL A' k)} (hJo : IsOpen (J : Set (GL A' k))) (hJK : J ≤ KO k A')
    (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (he : 1 ≤ e) (hν : CondLE ϖ e ν) (hram : ¬ IsUnram ν)
    (hνF : ∀ u, (ν u : ℂ) ∈ F) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F) (c : D → kˣ) (Λ' : Submodule 𝒪[k] (D → k))
    {Ψ : Matrix A' D k → ℂ} (hΨ : HasDepth ϖ e (diagLat c) Ψ) (hΨF : ∀ X, Ψ X ∈ F) (X : Matrix A D k) :
    phiA (haarVol J) σ ν ϖ e Λ' Ψ X ∈ F := by
  classical
  unfold phiA
  split_ifs
  · unfold fFun
    split_ifs with hX
    · exact F.mul_mem (F.mul_mem (hνF _) (apow_nat_half_mem F habs _ _))
        (smallF_mem F hJo hJK σ ν hϖ he hν hram hνF habs c hΨ hΨF _)
    · exact F.zero_mem
  · exact F.zero_mem

theorem flipTensor_mem {G : Grid k} (F : Subfield ℂ) {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ)
    (hψc : HasConductor ψ 1) (he : 1 ≤ e) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F)
    (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ F) {i j : ℕ}
    (hν : CondLE ϖ e (G.nu i j)) (hram : ¬ IsUnram (G.nu i j)) (hνF : ∀ u, (G.nu i j u : ℂ) ∈ F) {J : G.Level}
    (hJ : IsOpen (J (i, j) : Set (GL (Fin (G.rank (i, j))) k))) (hK : J (i, j) ≤ KO k _) {γ : List Edge}
    (h1 : Edge.theta i j ∈ γ) (h2 : Edge.ex i j ∈ γ) {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) (hTF : ∀ x, T x ∈ F)
    (x : G.Args) : G.flipTensor .one ψ ϖ e i j J T x ∈ F := by
  have hJ' := isOpen_map_invT hJ hK
  unfold Grid.flipTensor squareFlip
  exact invFourierSum_inv_mem F ψ ϖ e _ hψ (fun X => phiA_mem F hJ'.1 hJ'.2 _ _ hϖ he hν hram hνF habs
    (blockUnits ϖ e _) _ ((FourierDepth.fourier_exchange k _ _ ψ ϖ e _ hϖ hψc).1 _ (isNatDatum_sliceB hT h1 h2 x))
    (fun Y => fourierSum_mem F ψ ϖ e _ hψ (fun Z => hTF _) Y) X) _

theorem flips_mem {G : Grid k} (F : Subfield ℂ) {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ)
    (hψc : HasConductor ψ 1) (he : 1 ≤ e) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F)
    (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ F) :
    ∀ (l : List (ℕ × ℕ)) (S : G.PiLocalization₂),
      (∀ x ∈ l, CondLE ϖ e (G.nu x.1 x.2) ∧ ¬ IsUnram (G.nu x.1 x.2) ∧ ∀ u, (G.nu x.1 x.2 u : ℂ) ∈ F) →
      CanFlip S.path l → (∀ X, IsOpen (S.level X : Set (GL (Fin (G.rank X)) k)) ∧ S.level X ≤ KO k _) →
      G.IsTensor ϖ e S.path S.tensor → (∀ z, S.tensor z ∈ F) → ∀ z, (S.flips .one ψ ϖ e l).tensor z ∈ F := by
  intro l
  induction l with
  | nil => intro S _ _ _ _ hF; exact hF
  | cons x l ih =>
    intro S hν hc hJ hT hF
    obtain _ | ⟨hp, hc'⟩ := hc
    have hsub := hp.subset
    have hx := hν x List.mem_cons_self
    refine ih (S.flip .one ψ ϖ e x) (fun y hy => hν y (List.mem_cons_of_mem _ hy)) hc' (fun X => ?_)
      (isTensor_flipTensor hϖ hψc he hx.1 (hJ _).1 (hJ _).2 (hsub (by simp)) (hsub (by simp)) hT)
      (flipTensor_mem F hϖ hψc he habs hψ hx.1 hx.2.1 hx.2.2 (hJ _).1 (hJ _).2 (hsub (by simp)) (hsub (by simp)) hT hF)
    change IsOpen (G.flipLevel x.1 x.2 S.level X : Set (GL (Fin (G.rank X)) k)) ∧ G.flipLevel x.1 x.2 S.level X ≤ _
    by_cases hX : X = (x.1 + 1, x.2 + 1)
    · subst hX; simp only [Grid.flipLevel, Function.update_self]; exact ⟨isOpen_KO, le_rfl⟩
    · simp only [Grid.flipLevel, Function.update_of_ne hX]; exact hJ X

end Generic

end GlobalTheory.TflipField

namespace GlobalTheory.TflipField

section Concrete

open ValuativeRel _root_.Formalism.L2.Host

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem givenStage_mem (F : Subfield ℂ) (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E)
    (hmu : ∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) (hxi : ∀ x, ((L.xiH t).loc w x : ℂ) ∈ F)
    (z : (locGrid G t w).Args) : (givenStage t w B Φ).tensor z ∈ F :=
  GlobalTheory.T.gridGivenPathTensor_mem_subfield F B t Φ w hmu hxi z

theorem nu_mem (F : Subfield ℂ) (t : T) (w : Pl D.host.E) (hmu : ∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F)
    (hxi : ∀ x, ((L.xiH t).loc w x : ℂ) ∈ F) (hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, ((G.ch.chiH i).loc w x : ℂ) ∈ F)
    {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) (u : (Kw w)ˣ) : ((locGrid G t w).nu i j u : ℂ) ∈ F := by
  have e1 : (((locGrid G t w).nu i j u : ℂˣ) : ℂ) =
      ((L.C.mu0 ⟨j, hj⟩).loc w u : ℂ) * ((L.xiH t).loc w u : ℂ) * (((G.ch.chiH (D.R.m - i)).loc w u : ℂ))⁻¹ := by
    simp only [Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Units.val_div_eq_div_val, div_eq_mul_inv]
    simp [HChar.loc]
  rw [e1]
  exact F.mul_mem (F.mul_mem (hmu _ _) (hxi _)) (F.inv_mem (hchi _ (by omega) (by omega) _))

theorem psiAt_mem (F : Subfield ℂ) {W : G.Weil} {w : Pl D.host.E}
    (hroots : ∀ z : ℂ, z ^ (Ideal.absNorm w.asIdeal ^ depthAt G w) = 1 → z ∈ F) (hcond : HasConductor (psiAt W w) 1)
    (x : Kw w) (hx : valuation (Kw w) ((((unifAt w) ^ depthAt G w : (Kw w)ˣ) : Kw w) * x) ≤ 1) :
    (psiAt W w x : ℂ) ∈ F :=
  GlobalTheory.T.weilTraceAddCharAtPlace_mem_subfield_of_roots F hroots hcond x hx

theorem apow_half_mem (F : Subfield ℂ) (w : Pl D.host.E)
    (hsq : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ F) (u : (Kw w)ˣ) : apow u (1 / 2) ∈ F :=
  GlobalTheory.T.normalisedAbsComplexPow_half_mem_subfield_of_sqrt_norm F w hsq u

end Concrete

end GlobalTheory.TflipField

namespace GlobalTheory.RowTest

theorem Tflip_mem_range : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D)
    (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum),
    ch.S.SumOK t Φ → ∀ w ∈ locPl ch.G t, ∀ z, Tflip ch.W ch.S.B t Φ w z ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS hch _ hF t Φ _ w hw z
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL ch.S.B t Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  let K : Subfield ℂ := D.what₂.embLL.fieldRange
  have hK : ∀ y, y ∈ Set.range D.what₂.embLL → y ∈ K := fun y hy => RingHom.mem_fieldRange.2 hy
  have hmu : ∀ j x, ((R.toLevCh.C.mu0 j).loc w x : ℂ) ∈ K := fun j x => hK _ (hF.chars.mu0 j w x)
  have hxi : ∀ x, ((R.toLevCh.xiH t).loc w x : ℂ) ∈ K := fun x => hK _ (hF.chars.xi t w x)
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, ((ch.G.ch.chiH i).loc w x : ℂ) ∈ K :=
    fun i a b x => hK _ (hF.chars.chi i a b w x)
  have habs : ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ K :=
    GlobalTheory.TflipField.apow_half_mem K w (hK _ (hF.sqrt w (.inr ⟨t, hw⟩)))
  have hψ := GlobalTheory.TflipField.psiAt_mem (W := ch.W) K (fun z hz => hK _ (hF.roots t w hw z hz)) h00.cond
  have hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G t w).nu x.1 x.2) ∧
      ¬ IsUnram ((locGrid ch.G t w).nu x.1 x.2) ∧ ∀ u, ((locGrid ch.G t w).nu x.1 x.2 u : ℂ) ∈ K := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    have hs := hg.square i hi j hj
    have e := (locGrid ch.G t w).alpha_div_beta i j
    refine ⟨by rw [← e]; exact hs.condν, by rw [← e]; exact hs.ram, GlobalTheory.TflipField.nu_mem K t w hmu hxi hchi hi hj⟩
  have key := GlobalTheory.TflipField.flips_mem K h00.unif h00.cond h00.one_le habs hψ (flipOrder D.R.m)
    (givenStage t w ch.S.B Φ) hν (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) hadm.tensor
    (GlobalTheory.TflipField.givenStage_mem K ch.S.B t Φ w hmu hxi) z
  exact RingHom.mem_fieldRange.1 key

end GlobalTheory.RowTest
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathLocalTotalTensorMemCoefficientFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oppositePathLocalTotalTensor_mem_coefficientField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ w ∈ locPl ch.G t, ∀ z, Tflip ch.W ch.S.B t Φ w z ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.RowTest.Tflip_mem_range | exact GlobalTheory.RowTest.Tflip_mem_range | (intros; apply GlobalTheory.RowTest.Tflip_mem_range <;> assumption)
end
