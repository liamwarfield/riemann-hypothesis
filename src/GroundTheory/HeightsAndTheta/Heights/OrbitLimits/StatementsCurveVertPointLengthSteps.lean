module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphMetric
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockMetric
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZeroCocycleSection

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertPointLengthSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

def CurveVertPointChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) →
        (curvePtIdeal y W).IsMaximal ∧
        (∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ curvePtIdeal y W ∧
          (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a) ∧
        ∀ (e : K → ℕ) (g : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e →
          (g ∈ W ↔ ∃ a b : curveRing y, a ∈ curvePtIdeal y W ∧ b ∉ curvePtIdeal y W ∧
            (b : Ω) * aeval y g = a * ∏ k, y ⟨k, c k⟩ ^ e k)

def CurveVertPointInj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      Set.InjOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s)

def CurveVertPointSurj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ m : Ideal (curveRing y), m.IsMaximal →
        locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) ≠ 0 →
          ∃ W ∈ divSupp (mCoordIdeal y) s, curvePtIdeal y W = m

def CurveVertPointMultChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) →
        ∀ a b : curveRing y, b ∉ curvePtIdeal y W →
          (b : Ω) * aeval y s = a * ∏ k, y ⟨k, c k⟩ ^ d k →
            multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
              locLen (curvePtIdeal y W) (curveRing y ⧸ Ideal.span {a})

def CurveSectionQuotLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ (m : Ideal (curveRing y)) (c : ∀ k, ι k), m.IsPrime → (∀ k, y ⟨k, c k⟩ ≠ 0) →
        (∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a) →
        ∀ a b : curveRing y, b ∉ m → (b : Ω) * aeval y s = a * ∏ k, y ⟨k, c k⟩ ^ d k →
          locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) =
            locLen m (curveRing y ⧸ Ideal.span {a})

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace CurveVerticalIndex

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem span_toAddSubgroup (y : (Σ k, ι k) → Ω) (x : Ω) :
    (Submodule.span (curveRing y) {x}).toAddSubgroup = curveMul y x := by
  ext z
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, curveMul, AddSubgroup.mem_map,
    AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, b.2, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩


omit [∀ k, Fintype (ι k)] in
theorem genIndex_eq_card (y : (Σ k, ι k) → Ω) (a : K → ℤ) {x : Ω} (hx : x ∈ curveSectionMod y a) :
    genIndex (chartLat y a 1) (curveMul y x) = Nat.card (curveSectionQuot y a x) := by
  have hle : curveMul y x ≤ chartLat y a 1 := by
    rw [← span_toAddSubgroup]
    intro z hz
    exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) hz
  rw [genIndex, AddSubgroup.relIndex_eq_one.mpr hle, Nat.cast_one, div_one, ← span_toAddSubgroup]
  rfl

end CurveVerticalIndex

theorem CurveVertIndex.proof (hF : CurveSectionQuotFinite.Statement) (hV : CurveVertPointLength.Statement)
    (hR : CurveVertPointResidue.Statement) : CurveVertIndex.Statement := by
  intro K _ ι _ Ω _ y s d hP hs hsP
  have := hF K ι Ω y s d hP hs hsP
  obtain ⟨hbij, hmult⟩ := hV K ι Ω y s d hP hs hsP
  rw [CurveVerticalIndex.genIndex_eq_card y _ (HilbertSamuel.LiftBirationalAmple.chartLat_form hs),
    LogCardLength.proof (curveRing y) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)), vertR]
  calc _ = ∑ᶠ W ∈ divSupp (mCoordIdeal y) s,
          (locLen (curvePtIdeal y W) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) : ℝ) *
            Real.log (Nat.card (curveRing y ⧸ curvePtIdeal y W)) := by
        refine finsum_mem_congr rfl fun W hW => ?_
        rw [if_neg (IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full K ι _ s d hP hs hsP W hW), hmult W hW,
          ← hR K ι Ω y s d hP hs hsP W hW]
        congr 3
    _ = ∑ᶠ m ∈ {m : Ideal (curveRing y) |
          m.IsMaximal ∧ locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) ≠ 0},
          (locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) : ℝ) *
            Real.log (Nat.card (curveRing y ⧸ m)) :=
        finsum_mem_eq_of_bijOn _ hbij fun _ _ => rfl
    _ = _ := by
        refine finsum_mem_inter_support_eq _ _ {m : Ideal (curveRing y) | m.IsMaximal} ?_
        ext m
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support]
        exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, fun h0 => h2 (by simp [h0])⟩, h2⟩⟩

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveFieldNumber
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

noncomputable section

theorem CurveFieldNumber.proof (hR1 : RegularityFunctionFieldNumber.Statement) : CurveFieldNumber.Statement := by
  intro K _ ι _ Ω _ y hA hB
  set P := mCoordIdeal y with hPdef
  have : P.IsPrime := hA.2.1.1
  obtain ⟨hF, hN⟩ := hR1 K ι P hA
  let L := FractionRing (MvPolynomial K Ω)

  let j : MRing ι ⧸ P →+* L :=
    (algebraMap (MvPolynomial K Ω) L).comp (RingHom.kerLift (mConeMap y : MRing ι →+* MvPolynomial K Ω))
  have hj : Function.Injective j :=
    (IsFractionRing.injective (MvPolynomial K Ω) L).comp (RingHom.kerLift_injective _)
  let Φ : FractionRing (MRing ι ⧸ P) →+* L := IsFractionRing.lift hj
  let c : Ω →+* L := (algebraMap (MvPolynomial K Ω) L).comp MvPolynomial.C
  have hΦ : ∀ f, Φ (algebraMap _ _ (Ideal.Quotient.mk P f)) = algebraMap _ L (mConeMap y f) := fun f =>
    (IsFractionRing.lift_algebraMap hj _).trans (congrArg (algebraMap (MvPolynomial K Ω) L)
      (RingHom.kerLift_mk (mConeMap y : MRing ι →+* MvPolynomial K Ω) f))

  have hform : ∀ {g : MRing ι} {a : K → ℕ}, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a →
      Φ (algebraMap _ _ (Ideal.Quotient.mk P g)) = c (aeval y g) * algebraMap _ L (∏ k, (X k : MvPolynomial K Ω) ^ a k) := by
    intro g a hg
    rw [hΦ, LowerBoundFree.mConeMap_of_isMultiHomog y hg, map_mul]; rfl
  have hT : ∀ a : K → ℕ, algebraMap (MvPolynomial K Ω) L (∏ k, (X k : MvPolynomial K Ω) ^ a k) ≠ 0 := fun a =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).2 (Finset.prod_ne_zero_iff.2 fun k _ =>
      pow_ne_zero _ (X_ne_zero k))

  have hmem : ∀ {g : MRing ι} {a : K → ℕ}, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a → aeval y g = 0 → g ∈ P := by
    intro g a hg h0
    show mConeMap y g = 0
    rw [LowerBoundFree.mConeMap_of_isMultiHomog y hg, h0, map_zero, zero_mul]

  have heq : (funField P).map Φ = c.range := by
    apply le_antisymm
    · rw [Subring.map_le_iff_le_comap, funField, Subring.closure_le]
      rintro x ⟨u, v, a, hv, hu, hvf, rfl⟩
      have hvP : v ∉ P := fun h => nonZeroDivisors.ne_zero hv ((Ideal.Quotient.eq_zero_iff_mem).2 h)
      have hvy : aeval y v ≠ 0 := fun h => hvP (hmem hvf h)
      refine ⟨aeval y u / aeval y v, ?_⟩
      have h1 := congrArg Φ (IsLocalization.mk'_spec (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hv⟩)
      rw [map_mul, hform hvf, hform hu] at h1
      have hcv : c (aeval y v) ≠ 0 := (map_ne_zero_iff _ c.injective).2 hvy
      rw [map_div₀, div_eq_iff hcv]
      exact mul_right_cancel₀ (hT a) (by rw [← h1]; ring)
    · rintro _ ⟨s, rfl⟩
      obtain ⟨d, g, h, hg, hh, hh0, hgs⟩ := hB s
      have hhP : h ∉ P := fun hP => by
        have : mConeMap y h = 0 := hP
        rw [LowerBoundFree.mConeMap_of_isMultiHomog y hh] at this
        exact mul_ne_zero ((map_ne_zero_iff _ (MvPolynomial.C_injective K Ω)).2 hh0)
          (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)) this
      obtain ⟨x, hx⟩ := exists_funField_mul_eq hg hh hhP
      refine ⟨x, x.2, ?_⟩
      have h1 := congrArg Φ hx
      rw [map_mul, hform hh, hform hg, hgs, map_mul] at h1
      have hch : c (aeval y h) ≠ 0 := (map_ne_zero_iff _ c.injective).2 hh0
      exact mul_right_cancel₀ (mul_ne_zero hch (hT d)) (by rw [h1]; ring)

  have hc : Function.Injective c.rangeRestrict := fun a b h => c.injective (congrArg Subtype.val h)
  let e : funField P ≃+* Ω :=
    ((Subring.equivMapOfInjective (funField P) Φ Φ.injective).trans (RingEquiv.subringCongr heq)).trans
      (RingEquiv.ofBijective c.rangeRestrict ⟨hc, c.rangeRestrict_surjective⟩).symm
  exact @NumberField.of_ringEquiv _ _ hF.toField _ e hN

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphFactor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

set_option linter.unusedSectionVars false

namespace LiftGraphFactor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blkNorm (w : (Σ k, ι k) → ℂ) (k : K) : ℝ := Real.sqrt (∑ i, ‖w ⟨k, i⟩‖ ^ 2)

theorem blkSq_pos {w : (Σ k, ι k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (k : K) :
    0 < ∑ i, ‖w ⟨k, i⟩‖ ^ 2 := by
  obtain ⟨i, hi⟩ := hw k
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2)
    (Finset.single_le_sum (f := fun i => ‖w ⟨k, i⟩‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i))

theorem blkNorm_pos {w : (Σ k, ι k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (k : K) : 0 < blkNorm w k :=
  Real.sqrt_pos.2 (blkSq_pos hw k)

theorem blkNorm_smul (c : K → ℂ) (w : (Σ k, ι k) → ℂ) (k : K) :
    blkNorm (fun p => c p.1 * w p) k = ‖c k‖ * blkNorm w k := by
  unfold blkNorm
  have : ∑ i, ‖c k * w ⟨k, i⟩‖ ^ 2 = ‖c k‖ ^ 2 * ∑ i, ‖w ⟨k, i⟩‖ ^ 2 := by
    simp only [norm_mul, mul_pow, Finset.mul_sum]
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem blkNorm_conj (w : (Σ k, ι k) → ℂ) (k : K) :
    blkNorm (fun p => (starRingEnd ℂ) (w p)) k = blkNorm w k := by
  simp [blkNorm]

def fsLineZ (n : K → ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι where
  a := n
  h w := ∏ k, blkNorm w k ^ n k
  pos w hw := Finset.prod_pos fun k _ => zpow_pos (blkNorm_pos hw k) _
  smul c w hc := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [blkNorm_smul, mul_zpow]

theorem contDiffAt_zpow_of_ne {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}
    {N : WithTop ℕ∞} (hf : ContDiffAt ℝ N f x) (hx : f x ≠ 0) (m : ℤ) :
    ContDiffAt ℝ N (fun y => f y ^ m) x := by
  cases m with
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv (pow_ne_zero _ hx)

theorem isSmoothHerm_fsLineZ (n : K → ℤ) : IsSmoothHerm (fsLineZ (ι := ι) n) := by
  intro w hw
  refine ContDiffAt.contDiffWithinAt ?_
  show ContDiffAt ℝ _ (fun x => ∏ k, blkNorm x k ^ n k) w
  refine contDiffAt_prod (t := Finset.univ) (f := fun k x => blkNorm x k ^ n k) fun k _ => ?_
  refine contDiffAt_zpow_of_ne (f := fun x => blkNorm x k) ?_ (blkNorm_pos hw k).ne' (n k)
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Σ k, ι k) → ℂ => ∑ i, ‖x ⟨k, i⟩‖ ^ 2) :=
    ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) _)
  exact hs.contDiffAt.sqrt (blkSq_pos hw k).ne'

theorem conj_fsLineZ (n : K → ℤ) : IsConjInvariantH (fsLineZ (ι := ι) n) := by
  intro w
  show ∏ k, blkNorm _ k ^ n k = ∏ k, blkNorm w k ^ n k
  simp only [blkNorm_conj]

end LiftGraphFactor


open LiftGraphFactor in
theorem LiftGraphFactor.proof (hExt : SectionNormSqExtension.Statement) : LiftGraphFactor.Statement := by
  intro K _ _ ι _ Ω _ y N a r v hv hgen
  classical
  let A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fsLineZ (a • N.a)
  have hA1 : ∀ j, v j ∈ chartLat y A.a 1 := hv
  have hgen' : KH.GeneratesOn y (fun k => ((1 : ℕ) : ℤ) * A.a k) v := by
    have e : (fun k => ((1 : ℕ) : ℤ) * A.a k) = a • N.a := by
      funext k
      simp [A, fsLineZ]
    rw [e]
    exact hgen
  obtain ⟨S, hSs, hSp, hSt, hSc, hSv, hSl⟩ :=
    hExt K ι Ω y A 1 r v (isSmoothHerm_fsLineZ _) (conj_fsLineZ _) hA1 hgen'
  let U0 : Set ((Σ k, ι k) → ℂ) := {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0}
  have hAs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h U0 := isSmoothHerm_fsLineZ _
  refine ⟨fun w => S w * A.h w ^ 2, hSs.mul (hAs.pow 2), fun w hw => mul_pos (hSp w hw) (pow_pos (A.pos w hw) 2),
    ?_, ?_, ?_, ?_⟩
  ·
    intro c w hc hw
    show S _ * A.h _ ^ 2 = _ * (S w * A.h w ^ 2)
    rw [hSt c w hc, A.smul c w hc]
    have hAa : A.a = a • N.a := rfl
    rw [hAa]
    ring
  ·
    intro w
    show S _ * A.h _ ^ 2 = S w * A.h w ^ 2
    rw [hSc w, conj_fsLineZ _ w]
  ·
    intro z hz j
    have hx := PowerBlockMetric.oldPart_mem hz
    obtain ⟨c, hc⟩ := PowerBlockMetric.graph_prop (A := A) (m := 1) hA1 hgen' hz
    have hvN : ∀ j, v j ∈ chartLat y N.a a := by
      intro j c' hc'
      have h := hv j c' hc'
      have e : ∀ k, -(((1 : ℕ) : ℤ) * (a • N.a) k) = -((a : ℤ) * N.a k) := fun k => by
        simp [Pi.smul_apply]
      simp only [e] at h
      exact h

    have key : ∀ j, secNormAt y N a (v j) (basePart₂ z) * N.h (basePart₂ z) ^ a =
        ‖PowerBlockMetric.val y A 1 (v j) (basePart₂ z)‖ * A.h (basePart₂ z) := by
      intro j
      obtain ⟨⟨g, h⟩, hr, hne⟩ := PowerBlockMetric.exists_rep_at (hA1 j) hx
      have hrN : PowerBlockMetric.IsRep y N.a a (v j) g h := by
        obtain ⟨dg, dh, hg, hh, hd, hy⟩ := hr
        refine ⟨dg, dh, hg, hh, fun k => ?_, hy⟩
        rw [hd k]
        simp [A, fsLineZ, Pi.smul_apply]
      have eA := PowerBlockMetric.val_spec (hA1 j) hx hr
      have eN := PowerBlockMetric.val_spec (hvN j) hx hrN
      have hNp : 0 < N.h (basePart₂ z) := N.pos _ hx.1
      have hAp : 0 < A.h (basePart₂ z) := A.pos _ hx.1
      have e2 : PowerBlockMetric.val y N a (v j) (basePart₂ z) * (N.h (basePart₂ z) : ℂ) ^ a =
          PowerBlockMetric.val y A 1 (v j) (basePart₂ z) * (A.h (basePart₂ z) : ℂ) := by
        apply mul_right_cancel₀ hne
        have := eN.symm.trans eA
        simp only [pow_one] at this
        linear_combination this
      rw [PowerBlockMetric.secNormAt_eq (hvN j) hx]
      have := congrArg norm e2
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hNp.le,
        Real.norm_of_nonneg hAp.le] at this
      exact this
    have hS : S (basePart₂ z) = ∑ i, ‖PowerBlockMetric.val y A 1 (v i) (basePart₂ z)‖ ^ 2 := by
      rw [hSv _ hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [PowerBlockMetric.secNormAt_eq (hA1 i) hx]
    have hN : ∑ i : Fin r, ‖z ⟨none, i⟩‖ ^ 2 = ‖c‖ ^ 2 * S (basePart₂ z) := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc i, norm_mul, mul_pow]
    have hSp' : 0 ≤ S (basePart₂ z) := (hSp _ hx.1).le
    have hAp : 0 < A.h (basePart₂ z) := A.pos _ hx.1
    rw [key j, hN, hc j, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_mul hSp', Real.sqrt_sq hAp.le, norm_mul]
    ring
  ·
    intro z hz ξ hξ
    have hx := PowerBlockMetric.oldPart_mem hz
    have hw : basePart₂ z ∈ U0 := hx.1
    have hU0o : IsOpen U0 := LiftGraphMetric.isOpen_allNZ
    have hUo : IsOpen {z : (Σ k, addIdx ι r k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := LiftGraphMetric.isOpen_allNZ
    have h2le : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
    have hoR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, addIdx ι r k) → ℂ => basePart₂ z) :=
      ((LiftGraphMetric.oldCLM (ι := ι) r).restrictScalars ℝ).contDiff
    have hSlog : ContDiffAt ℝ 2 (fun w => Real.log (S w)) (basePart₂ z) :=
      ((hSs.contDiffAt (hU0o.mem_nhds hw)).of_le h2le).log (hSp _ hw).ne'
    have hAlog : ContDiffAt ℝ 2 (fun w => Real.log (A.h w)) (basePart₂ z) :=
      ((hAs.contDiffAt (hU0o.mem_nhds hw)).of_le h2le).log (A.pos _ hw).ne'
    have hL1 : ContDiffAt ℝ 2 (fun x : (Σ k, addIdx ι r k) → ℂ => Real.log (∑ i : Fin r, ‖x ⟨none, i⟩‖ ^ 2)) z :=
      (PowerBlockMetric.contDiff_newSq.contDiffAt).log (PowerBlockMetric.newSq_pos hz.1).ne'
    have hL2 : ContDiffAt ℝ 2 (fun x : (Σ k, addIdx ι r k) → ℂ => Real.log (S (basePart₂ x))) z :=
      hSlog.comp z (hoR.contDiffAt.of_le h2le)
    have hL3 : ContDiffAt ℝ 2 (fun x : (Σ k, addIdx ι r k) → ℂ => Real.log (A.h (basePart₂ x))) z :=
      hAlog.comp z (hoR.contDiffAt.of_le h2le)
    have hcomp : ReciprocityTheory.AnForm.levi (fun x => Real.log (A.h (basePart₂ x))) z ξ =
        ReciprocityTheory.AnForm.levi (fun w => Real.log (A.h w)) (basePart₂ z) (basePart₂ ξ) := by
      have h := ReciprocityTheory.AnForm.levi_comp (φ := fun w => Real.log (A.h w))
        (τ := ⇑(LiftGraphMetric.oldCLM (ι := ι) r)) (z := z) ξ
        ((LiftGraphMetric.oldCLM (ι := ι) r).analyticAt z) hAlog
      rw [ContinuousLinearMap.fderiv] at h
      exact h
    have hev : (fun x : (Σ k, addIdx ι r k) → ℂ => Real.log (S (basePart₂ x) * A.h (basePart₂ x) ^ 2)) =ᶠ[𝓝 z]
        fun x => Real.log (S (basePart₂ x)) + (2 : ℝ) * Real.log (A.h (basePart₂ x)) := by
      filter_upwards [hUo.mem_nhds hz.1] with x hx'
      have hw' : basePart₂ x ∈ U0 := fun k => hx' (some k)
      rw [Real.log_mul (hSp _ hw').ne' (pow_pos (A.pos _ hw') 2).ne', Real.log_pow]
      norm_num
    have hgraph := hSl z hz ξ hξ
    have hsplit : (fun z' : (Σ k, addIdx ι r k) → ℂ =>
        Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) / 2 - Real.log (S (basePart₂ z')) / 2) =
        fun z' => (1 / 2 : ℝ) * Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) +
          (-1 / 2 : ℝ) * Real.log (S (basePart₂ z')) := by
      funext z'
      ring
    show ReciprocityTheory.AnForm.levi _ z ξ = ReciprocityTheory.AnForm.levi _ z ξ
    change ReciprocityTheory.AnForm.levi _ z ξ = (1 : ℕ) * ReciprocityTheory.AnForm.levi _ (basePart₂ z) (basePart₂ ξ) at hgraph
    rw [hsplit, ReciprocityTheory.AnForm.levi_add_smul (f := fun x : (Σ k, addIdx ι r k) → ℂ =>
        (1 / 2 : ℝ) * Real.log (∑ j, ‖x ⟨none, j⟩‖ ^ 2)) (-1 / 2 : ℝ) (contDiffAt_const.mul hL1) hL2 ξ,
      ] at hgraph
    have hhalf := LiftGraphMetric.levi_const_mul (1 / 2 : ℝ) hL1 ξ
    erw [hhalf] at hgraph
    rw [← hcomp] at hgraph
    rw [ReciprocityTheory.AnForm.levi_congr hev, ReciprocityTheory.AnForm.levi_add_smul (2 : ℝ) hL2 hL3 ξ]
    push_cast at hgraph
    linarith

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveBoxCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

theorem CurveBoxCount.proof (hS : CurveBoxSmall.Statement) (hL : CurveBoxLattice.Statement) :
    CurveBoxCount.Statement := by
  intro K _ ι _ Ω _ y A c R hP hB hA hc hR hRu
  obtain ⟨C, hC⟩ := hL K ι Ω y A c R hP hB hA hc hR hRu
  refine ⟨C, fun τ hτ => ?_⟩
  have e : smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) τ =
      Real.log (Nat.card {s : chartLat y A.a τ //
        ∀ σ : Ω →+* ℂ, ‖σ ((s : Ω) / chartUnit y c A.a τ)‖ ≤ chartRadius A c (fun p => σ (y p)) ^ τ}) := by
    unfold smallSectionCount
    rw [Nat.card_congr (Equiv.subtypeEquivRight (p := fun s : chartLat y A.a τ => IsSmallH (mCoordIdeal y) y A τ (s : Ω))
      fun s => hS K ι Ω y A c hP hB hc τ (s : Ω))]
  rw [e]
  exact hC τ hτ

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveEmbedOrbit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

namespace CurveEmbedOrbit

theorem sameOrbit_refl {K : Type} {ι : K → Type} (z : (Σ k, ι k) → ℂ) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩

theorem sameOrbit_symm {K : Type} {ι : K → Type} {z w : (Σ k, ι k) → ℂ} (h : SameOrbit z w) : SameOrbit w z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun p => ?_⟩
  rw [← mul_assoc, inv_mul_cancel₀ (hc p.1), one_mul]

theorem sameOrbit_trans {K : Type} {ι : K → Type} {z w u : (Σ k, ι k) → ℂ} (h1 : SameOrbit z w)
    (h2 : SameOrbit w u) : SameOrbit z u := by
  obtain ⟨c, hc, rfl⟩ := h1
  obtain ⟨d, hd, rfl⟩ := h2
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), funext fun p => by simp only; ring⟩

theorem eq_of_sameOrbit {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} (hB : Birational y) {σ τ : Ω →+* ℂ}
    (hst : SameOrbit (fun p => σ (y p)) (fun p => τ (y p))) : σ = τ := by
  obtain ⟨c, hc, hcy⟩ := hst
  ext s
  obtain ⟨d, g, h, hg, hh, hh0, hgs⟩ := hB s
  have key : ∀ ρ : Ω →+* ℂ, ρ s * eval (fun p => ρ (y p)) (map (Int.castRingHom ℂ) h) =
      eval (fun p => ρ (y p)) (map (Int.castRingHom ℂ) g) := fun ρ => by
    rw [CurveOrbit.eval_comp, CurveOrbit.eval_comp, hgs, map_mul]
  have e1 := key σ
  have e2 := key τ
  rw [hcy, CurveOrbit.eval_smul _ _ hh, CurveOrbit.eval_smul _ _ hg] at e1
  have hE : eval (fun p => τ (y p)) (map (Int.castRingHom ℂ) h) ≠ 0 := by
    rw [CurveOrbit.eval_comp]
    exact (map_ne_zero τ).mpr hh0
  have hC : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  apply mul_right_cancel₀ (mul_ne_zero hC hE)
  linear_combination e1 - (∏ k, c k ^ d k) * e2

end CurveEmbedOrbit


open CurveEmbedOrbit in
theorem CurveEmbedOrbit.proof : CurveEmbedOrbit.Statement := by
  intro K _ ι _ Ω _ y R hP hB hR hRu
  classical
  obtain ⟨j, -, hj⟩ := exists_chart hP
  have hex : ∀ t : R, ∃ σ : Ω →+* ℂ, SameOrbit (t : (Σ k, ι k) → ℂ) (fun p => σ (y p)) :=
    fun t => CurveOrbit.exists_sameOrbit hP hB (hR t t.2)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro t s hts
    have h1 : SameOrbit (t : (Σ k, ι k) → ℂ) s :=
      sameOrbit_trans (hf t) (by rw [hts]; exact sameOrbit_symm (hf s))
    exact Subtype.ext ((hRu t (hR t t.2)).unique ⟨t.2, sameOrbit_refl _⟩ ⟨s.2, h1⟩)
  have hsurj : Function.Surjective f := by
    intro τ
    obtain ⟨t, ⟨htR, hzt⟩, -⟩ := hRu _ (CurveOrbit.mem_mcPts τ y hj)
    exact ⟨⟨t, htR⟩, eq_of_sameOrbit hB
      (sameOrbit_trans (sameOrbit_symm (hf ⟨t, htR⟩)) (sameOrbit_symm hzt))⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveBoxSmall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

theorem CurveBoxSmall.zpow_mul_toNat_neg {F : Type} [Field F] {t : F} (ht : t ≠ 0) (n : ℤ) :
    t ^ n * t ^ (-n).toNat = t ^ n.toNat :=
  calc t ^ n * t ^ (-n).toNat = t ^ ((n.toNat : ℤ) - ((-n).toNat : ℤ)) * t ^ (-n).toNat := by
        rw [Int.toNat_sub_toNat_neg]
    _ = t ^ n.toNat := by
        rw [zpow_sub₀ ht, zpow_natCast, zpow_natCast, div_mul_cancel₀ _ (pow_ne_zero _ ht)]

theorem CurveBoxSmall.proof : CurveBoxSmall.Statement := by
  intro K _ ι _ Ω _ y A c hP hB hc τ s
  classical
  have hU : ∀ σ : Ω →+* ℂ, ‖σ (chartUnit y c A.a τ)‖ = (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ := fun σ => by
    rw [chartUnit, map_prod, norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow₀, norm_zpow, ← zpow_natCast (_ ^ A.a k), ← zpow_mul, mul_comm (A.a k)]
  have hQ : ∀ σ : Ω →+* ℂ, 0 < (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ := fun σ =>
    pow_pos (Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr ((map_ne_zero σ).mpr (hc k))) _) _
  constructor
  · intro hS σ
    obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hB (s / chartUnit y c A.a τ)
    let ap : K → ℕ := fun k => ((τ : ℤ) * A.a k).toNat
    let am : K → ℕ := fun k => (-((τ : ℤ) * A.a k)).toNat
    have hU0 : chartUnit y c A.a τ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
    have hu : chartUnit y c A.a τ * ∏ k, y ⟨k, c k⟩ ^ am k = ∏ k, y ⟨k, c k⟩ ^ ap k := by
      rw [chartUnit, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => CurveBoxSmall.zpow_mul_toNat_neg (hc k) _
    have hdeg : ∀ k, (((d + ap) k : ℕ) : ℤ) = ((d + am) k : ℕ) + τ * A.a k := fun k => by
      have := Int.toNat_sub_toNat_neg ((τ : ℤ) * A.a k)
      simp only [Pi.add_apply, Nat.cast_add, ap, am]
      omega
    have hval : aeval y (g * curveChartMono c ap) = s * aeval y (h * curveChartMono c am) := by
      simp only [map_mul, curveChartMono, map_prod, map_pow, aeval_X]
      rw [← hu, hgh]
      field_simp
    have hS' := hS _ _ _ _ _ (CurveOrbit.isMultiHomog_mul hg (isMultiHomog_curveChartMono c ap))
      (CurveOrbit.isMultiHomog_mul hh (isMultiHomog_curveChartMono c am)) hdeg hval (CurveOrbit.mem_mcPts σ y hc)
    rw [CurveOrbit.eval_comp, CurveOrbit.eval_comp] at hS'
    simp only [map_mul, curveChartMono, map_prod, map_pow, aeval_X, norm_mul, norm_prod, norm_pow] at hS'
    have hsu : s / chartUnit y c A.a τ = aeval y g / aeval y h := eq_div_of_mul_eq hh0 hgh.symm
    have hσh : 0 < ‖σ (aeval y h)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hh0)
    have ht : ∀ k, ‖σ (y ⟨k, c k⟩)‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr (hc k))
    have hR : (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ * ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k =
        ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ ap k := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast (_ ^ A.a k), ← zpow_mul, mul_comm (A.a k)]
      exact CurveBoxSmall.zpow_mul_toNat_neg (ht k) _
    have hRm : 0 < ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k :=
      Finset.prod_pos fun k _ => pow_pos (lt_of_le_of_ne (norm_nonneg _) (ht k).symm) _
    rw [hsu, map_div₀, norm_div, chartRadius, div_pow, div_le_div_iff₀ hσh (hQ σ)]
    refine le_of_mul_le_mul_right ?_ hRm
    calc ‖σ (aeval y g)‖ * (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ * ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k
        = ‖σ (aeval y g)‖ * ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ ap k := by rw [mul_assoc, hR]
      _ ≤ ‖σ (aeval y h)‖ * (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k) * A.h (fun p => σ (y p)) ^ τ := hS'
      _ = _ := by ring
  · intro hbox dg dh g h z hg hh hdeg hgs hz
    obtain ⟨σ, l, hl, rfl⟩ := CurveOrbit.exists_sameOrbit hP hB hz
    beta_reduce
    have hb := hbox σ
    rw [map_div₀, norm_div, chartRadius, div_pow, hU σ, div_le_div_iff_of_pos_right (hQ σ)] at hb
    have hlam : ‖∏ k, l k ^ dg k‖ = ‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ := by
      rw [norm_prod, norm_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hlk : ‖l k‖ ≠ 0 := norm_ne_zero_iff.mpr (hl k)
      rw [norm_pow, norm_pow, ← zpow_natCast (‖l k‖) (dg k), hdeg k, zpow_add₀ hlk, zpow_natCast,
        ← zpow_natCast (_ ^ A.a k), ← zpow_mul, mul_comm (A.a k)]
    rw [CurveOrbit.eval_smul _ l hg, CurveOrbit.eval_smul _ l hh, A.smul l _ hl, CurveOrbit.eval_comp,
      CurveOrbit.eval_comp, hgs, map_mul, norm_mul, norm_mul, norm_mul, hlam, mul_pow]
    calc ‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ * (‖σ s‖ * ‖σ (aeval y h)‖)
        = (‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ * ‖σ (aeval y h)‖) * ‖σ s‖ := by ring
      _ ≤ (‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ * ‖σ (aeval y h)‖) * A.h (fun p => σ (y p)) ^ τ :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartLatFull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ChartLatFull

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def ratSat [CharZero Ω] (R : Subalgebra ℤ Ω) : Subalgebra ℚ Ω where
  carrier := {t | ∃ n : ℕ, 0 < n ∧ (n : Ω) * t ∈ R}
  mul_mem' := by
    rintro t u ⟨n, hn, ht⟩ ⟨m, hm, hu⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (t * u) = ((n : Ω) * t) * ((m : Ω) * u) := by push_cast; ring
    rw [this]
    exact R.mul_mem ht hu
  one_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro t u ⟨n, hn, ht⟩ ⟨m, hm, hu⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (t + u) = (m : Ω) * ((n : Ω) * t) + (n : Ω) * ((m : Ω) * u) := by push_cast; ring
    rw [this]
    exact R.add_mem (R.mul_mem (R.natCast_mem m) ht) (R.mul_mem (R.natCast_mem n) hu)
  zero_mem' := ⟨1, one_pos, by simp⟩
  algebraMap_mem' := by
    intro q
    refine ⟨q.den, q.den_pos, ?_⟩
    have hd : (q.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    have : (q.den : Ω) * algebraMap ℚ Ω q = (q.num : Ω) := by
      rw [eq_ratCast, Rat.cast_def, mul_div_cancel₀ _ hd]
    rw [this]
    exact R.intCast_mem _

theorem exists_nat_mul_mem [NumberField Ω] {y : (Σ k, ι k) → Ω} (hy : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (t : Ω) : ∃ n : ℕ, 0 < n ∧ (n : Ω) * t ∈ chartRingZ y c := by
  obtain ⟨d, g, h, hg, hh, hh0, hgt⟩ := hy t
  have hX : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hG : aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k ∈ ratSat (chartRingZ y c) :=
    ⟨1, one_pos, by simpa using HilbertSamuel.ZeroCocycleSection.aeval_div_mem y c hg⟩
  have hH : aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k ∈ ratSat (chartRingZ y c) :=
    ⟨1, one_pos, by simpa using HilbertSamuel.ZeroCocycleSection.aeval_div_mem y c hh⟩
  have hinv : (aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k)⁻¹ ∈ ratSat (chartRingZ y c) :=
    Subalgebra.inv_mem_of_algebraic (A := ratSat (chartRingZ y c)) (x := ⟨_, hH⟩)
      (Algebra.IsAlgebraic.isAlgebraic _)
  have ht : t = (aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k) * (aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k)⁻¹ := by
    rw [hgt, inv_div, div_mul_div_comm, mul_comm (∏ k, y ⟨k, c k⟩ ^ d k), mul_assoc,
      mul_div_assoc, div_self (mul_ne_zero hh0 hX), mul_one]
  have := (ratSat (chartRingZ y c)).mul_mem hG hinv
  rw [← ht] at this
  exact this

end ChartLatFull

theorem ChartLatFull.proof : ChartLatFull.Statement := by
  intro K _ ι _ Ω _ _ y hy a τ s
  classical
  let t : (∀ k, ι k) → Ω := fun c => s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))
  let N : (∀ k, ι k) → ℕ := fun c =>
    if hc : ∀ k, y ⟨k, c k⟩ ≠ 0 then (ChartLatFull.exists_nat_mul_mem hy c hc (t c)).choose else 1
  have hNpos : ∀ c, 0 < N c := by
    intro c
    simp only [N]
    split_ifs with hc
    · exact (ChartLatFull.exists_nat_mul_mem hy c hc (t c)).choose_spec.1
    · exact one_pos
  refine ⟨∏ c, N c, Finset.prod_pos fun c _ => hNpos c, ?_⟩
  show ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → _
  intro c hc
  have hN : (N c : Ω) * t c ∈ chartRingZ y c := by
    simp only [N, dif_pos hc]
    exact (ChartLatFull.exists_nat_mul_mem hy c hc (t c)).choose_spec.2
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ c)
  have : ((∏ c, N c : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) = (m : Ω) * ((N c : Ω) * t c) := by
    rw [hm]; push_cast; simp only [t]; ring
  rw [this]
  exact (chartRingZ y c).mul_mem ((chartRingZ y c).natCast_mem m) hN

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveBoxLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

section Lemmas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem chartRadius_smul (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (d : K → ℂ) (hd : ∀ k, d k ≠ 0)
    (z : (Σ k, ι k) → ℂ) : chartRadius A c (fun p => d p.1 * z p) = chartRadius A c z := by
  unfold chartRadius
  rw [A.smul d z hd]
  have hX : (∏ k, ‖d k‖ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hd k))
  simp only [norm_mul, mul_zpow, Finset.prod_mul_distrib]
  rw [mul_div_mul_left _ _ hX]


omit [∀ k, Fintype (ι k)] in
theorem chartRadius_conj (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : IsConjInvariantH A) (c : ∀ k, ι k)
    (z : (Σ k, ι k) → ℂ) : chartRadius A c (fun p => (starRingEnd ℂ) (z p)) = chartRadius A c z := by
  unfold chartRadius
  rw [hA z]
  simp only [Complex.norm_conj]


omit [∀ k, Fintype (ι k)] in
theorem chartRadius_pos (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) : 0 < chartRadius A c z :=
  div_pos (A.pos z fun k => ⟨c k, hz k⟩)
    (Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hz k)) _)

end Lemmas

theorem genIndex_map_addEquiv {G : Type*} [AddCommGroup G] (m : G ≃+ G) (A B : AddSubgroup G) :
    genIndex (A.map m.toAddMonoidHom) (B.map m.toAddMonoidHom) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ m.injective,
    AddSubgroup.relIndex_map_map_of_injective _ _ m.injective]

theorem addSubgroup_fg_map {G H : Type*} [AddCommGroup G] [AddCommGroup H] {A : AddSubgroup G} (hA : A.FG)
    (f : G →+ H) : (A.map f).FG := by
  letI : A.FG := hA
  infer_instance

theorem CurveBoxLattice.proof (hF : CurveFieldNumber.Statement) (hE : CurveEmbedOrbit.Statement)
    (hL : ChartLatFull.Statement) (hN : NumberFieldBoxCount.Statement)
    (hG : HilbertSamuel.SectionLatticeFinite.Statement) : CurveBoxLattice.Statement := by
  intro K _ ι _ Ω _ y A c R hP hB hA hc hR hRu
  have : NumberField Ω := hF K ι Ω y hP hB
  obtain ⟨e, he⟩ := hE K ι Ω y R hP hB hR hRu
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  have hBeq : (curveRing y).toAddSubgroup = chartLat y 0 0 := by
    ext s
    simp [mem_curveRing, chartLat]
  have hBfg : (curveRing y).toAddSubgroup.FG := hBeq ▸ hG K ι Ω y 0 0 hy
  have hBfull : ∀ x : Ω, ∃ n : ℕ, 0 < n ∧ (n : Ω) * x ∈ (curveRing y).toAddSubgroup :=
    hBeq ▸ hL K ι Ω y hB 0 0
  obtain ⟨C, hC⟩ := hN Ω _ hBfg hBfull
  refine ⟨C, fun τ _ => ?_⟩
  have hu : chartUnit y c A.a τ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  set u := chartUnit y c A.a τ with hu_def
  let m : Ω ≃+ Ω :=
    { toFun := fun x => x / u
      invFun := fun x => x * u
      left_inv := fun x => div_mul_cancel₀ x hu
      right_inv := fun x => mul_div_cancel_right₀ x hu
      map_add' := fun x z => add_div x z u }
  set Λ := (chartLat y A.a τ).map m.toAddMonoidHom with hΛ
  have hΛfg : Λ.FG := addSubgroup_fg_map (hG K ι Ω y A.a τ hy) _
  have hΛfull : ∀ x : Ω, ∃ n : ℕ, 0 < n ∧ (n : Ω) * x ∈ Λ := by
    intro x
    obtain ⟨n, hn, hmem⟩ := hL K ι Ω y hB A.a τ (x * u)
    refine ⟨n, hn, ?_⟩
    have : (n : Ω) * x = m ((n : Ω) * (x * u)) := by
      show (n : Ω) * x = (n : Ω) * (x * u) / u
      rw [mul_div_assoc, mul_div_cancel_right₀ x hu]
    rw [this]
    exact AddSubgroup.mem_map_of_mem _ hmem
  have hBmap : (curveMul y u).map m.toAddMonoidHom = (curveRing y).toAddSubgroup := by
    rw [curveMul, AddSubgroup.map_map]
    convert AddSubgroup.map_id _ using 2
    ext x
    show u * x / u = x
    rw [mul_div_cancel_left₀ x hu]
  have hidx : genIndex Λ (curveRing y).toAddSubgroup = genIndex (chartLat y A.a τ) (curveMul y u) := by
    rw [← hBmap, hΛ, genIndex_map_addEquiv]
  let ρ : (Ω →+* ℂ) → ℝ := fun σ => chartRadius A c (fun p => σ (y p)) ^ τ
  have hρpos : ∀ σ, 0 < ρ σ := fun σ =>
    pow_pos (chartRadius_pos A c _ fun k => (map_ne_zero σ).mpr (hc k)) τ
  have hρconj : ∀ σ, ρ (NumberField.ComplexEmbedding.conjugate σ) = ρ σ := by
    intro σ
    simp only [ρ, NumberField.ComplexEmbedding.conjugate_coe_eq]
    rw [chartRadius_conj A hA c]
  have hcount := hC Λ hΛfg hΛfull ρ hρpos hρconj
  have hsum : ∑ t ∈ R, Real.log (chartRadius A c t) =
      ∑ σ : Ω →+* ℂ, Real.log (chartRadius A c (fun p => σ (y p))) := by
    rw [← Finset.sum_coe_sort R, ← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨d, hd, ht⟩ := he t
    rw [ht, chartRadius_smul A c d hd]
  have hρsum : ∑ σ : Ω →+* ℂ, Real.log (ρ σ) =
      (τ : ℝ) * ∑ σ : Ω →+* ℂ, Real.log (chartRadius A c (fun p => σ (y p))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => Real.log_pow _ _
  have hcard : Nat.card {s : chartLat y A.a τ //
        ∀ σ : Ω →+* ℂ, ‖σ ((s : Ω) / u)‖ ≤ chartRadius A c (fun p => σ (y p)) ^ τ} =
      Nat.card {x : Λ // ∀ σ : Ω →+* ℂ, ‖σ (x : Ω)‖ ≤ ρ σ} :=
    Nat.card_congr ((AddSubgroup.equivMapOfInjective _ m.toAddMonoidHom m.injective).toEquiv.subtypeEquiv
      fun s => Iff.rfl)
  rw [hcard, hsum, ← hρsum, chartIndexLog, ← hu_def, ← hidx]
  exact hcount

end GroundTheory.Heights₂.Heights.Targets
end
