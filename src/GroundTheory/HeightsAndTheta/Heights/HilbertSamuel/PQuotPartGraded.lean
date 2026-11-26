module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGraphChangeOfModel
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyIntegrable
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfInjOn

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace QuotPartGraded

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def blockWeight (ι : K → Type) : (Σ k, ι k) → (K → ℤ) := fun x => Pi.single x.1 1

theorem blockWeight_apply (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) d k = ∑ i, (d ⟨k, i⟩ : ℤ) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype d (fun i c => c • blockWeight ι i) (by intro i; simp),
    Finset.sum_apply, Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]

theorem isMultiHomog_iff (p : MRingOver S ι) (a : K → ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p a ↔ IsWeightedHomogeneous (blockWeight ι) p (fun k => (a k : ℤ)) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog
  constructor
  · intro h d hd
    funext k
    rw [blockWeight_apply]
    have := h d (mem_support_iff.2 hd) k
    exact_mod_cast this
  · intro h m hm k
    have := congrFun (h (mem_support_iff.1 hm)) k
    rw [blockWeight_apply] at this
    exact_mod_cast this

theorem nonneg_of_isWeightedHomogeneous {p : MRingOver S ι} {c : K → ℤ}
    (hp : IsWeightedHomogeneous (blockWeight ι) p c) (h0 : p ≠ 0) : ∀ k, 0 ≤ c k := by
  obtain ⟨d, hd⟩ := ne_zero_iff.1 h0
  intro k
  rw [← hp hd, blockWeight_apply]
  positivity

theorem span_eq (c : K → ℤ) :
    Submodule.span S {p : MRingOver S ι | (∀ k, 0 ≤ c k) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p (fun k => (c k).toNat)} =
      weightedHomogeneousSubmodule S (blockWeight ι) c := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro p ⟨hc, hp⟩
    rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule]
    have h' := (isMultiHomog_iff p _).1 hp
    have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
    rwa [hcc] at h'
  · intro p hp
    by_cases h0 : p = 0
    · rw [h0]; exact Submodule.zero_mem _
    · apply Submodule.subset_span
      have hc := nonneg_of_isWeightedHomogeneous hp h0
      refine ⟨hc, (isMultiHomog_iff p _).2 ?_⟩
      have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
      rw [hcc]
      exact hp

theorem quotPart_eq (V : Ideal (MRingOver S ι)) (c : K → ℤ) :
    KH.quotPart S V c =
      (weightedHomogeneousSubmodule S (blockWeight ι) c).map (Ideal.Quotient.mkₐ S V).toLinearMap := by
  rw [KH.quotPart, ← span_eq, Submodule.map_span]
  rfl

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isHomogeneous {V : Ideal (MRingOver S ι)} (hV : IsMultiHomogIdeal V) :
    V.IsHomogeneous (weightedHomogeneousSubmodule S (blockWeight ι)) := by
  obtain ⟨T, hT, rfl⟩ := hV
  apply Ideal.homogeneous_span
  intro f hf
  obtain ⟨a, ha⟩ := hT f hf
  exact ⟨fun k => (a k : ℤ), (isMultiHomog_iff f a).1 ha⟩

end QuotPartGraded

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem QuotPartGraded.proof : QuotPartGraded.Statement := by
  intro S _ K _ ι _ V hV
  have hq := QuotPartGraded.quotPart_eq (S := S) (ι := ι) V
  refine ⟨?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨?_, ?_⟩
    · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
      intro s v hv hsum
      have hlift : ∀ c, ∃ p : MRingOver S ι, c ∈ s →
          (p ∈ weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι) c ∧
            Ideal.Quotient.mk V p = v c) := by
        intro c
        by_cases hc : c ∈ s
        · have h1 := hv c hc
          rw [hq] at h1
          obtain ⟨y, hy, hyv⟩ := Submodule.mem_map.1 h1
          exact ⟨y, fun _ => ⟨hy, hyv⟩⟩
        · exact ⟨0, fun h => absurd h hc⟩
      choose p hp using hlift
      have hsumV : ∑ c ∈ s, p c ∈ V := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← hsum]
        exact Finset.sum_congr rfl fun c hc => (hp c hc).2
      intro c hc
      have hcomp := weightedHomogeneousComponent_mem_of_mem S (QuotPartGraded.blockWeight ι)
        (QuotPartGraded.isHomogeneous hV) hsumV c
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single c] at hcomp
      · rw [← (hp c hc).2, Ideal.Quotient.eq_zero_iff_mem]
        rwa [weightedHomogeneousComponent_eq_self (hp c hc).1] at hcomp
      · intro d hd hdc
        exact IsWeightedHomogeneous.weightedHomogeneousComponent_ne c (hp d hd).1 (Ne.symm hdc)
      · intro h
        exact absurd hc h
    · have htop := (DirectSum.Decomposition.isInternal
        (weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι))).submodule_iSup_eq_top
      rw [show KH.quotPart S V = fun c => (weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι) c).map
          (Ideal.Quotient.mkₐ S V).toLinearMap from funext hq]
      rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top]
      exact Ideal.Quotient.mkₐ_surjective S V
  · intro a c p m hp hm
    rw [hq] at hm ⊢
    obtain ⟨q, hq', rfl⟩ := Submodule.mem_map.1 hm
    refine Submodule.mem_map.2 ⟨p * q, ?_, ?_⟩
    · have := ((QuotPartGraded.isMultiHomog_iff p a).1 hp).mul hq'
      rw [mem_weightedHomogeneousSubmodule, add_comm]
      exact this
    · simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
      rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCoordArithOfFnField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.CoordinateConeArithVar

noncomputable section

namespace CoordArithOfFnField

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ratioField_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    CoordinateConeArithVar.ratioField y c = blockFnField y := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, q, hpq, rfl⟩
    have hp : y p / y ⟨p.1, c p.1⟩ ∈ CoordinateConeArithVar.ratioField y c :=
      IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩
    have hq : y q / y ⟨q.1, c q.1⟩ ∈ CoordinateConeArithVar.ratioField y c :=
      IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩
    have he : y p / y q = (y p / y ⟨p.1, c p.1⟩) / (y q / y ⟨q.1, c q.1⟩) := by
      rw [← hpq, div_div_div_cancel_right₀ (hc p.1)]
    rw [he]
    exact div_mem hp hq

theorem dim_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ringKrullDim (MRing ι ⧸ mCoordIdeal y) =
      (((Algebra.trdeg ℤ (blockFnField y)).toENat + Fintype.card K + 1 : ℕ∞) : WithBot ℕ∞) := by
  have hhor : IsHorizontal (mCoordIdeal y) := horizontal y
  have : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime _
  have htr := ConeTrdeg.proof K ι (CoordinateConeArithVar.ratioField y c) (ratioPtL y c) (birational y c hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL y c hc]; exact hhor)
  rw [mCoordIdeal_ratioPtL y c hc, ratioField_eq y c hc] at htr
  have hA := IntDomainDim.proof (MRing ι ⧸ mCoordIdeal y)
    (CoordinateConeArithVar.algebraMap_injective _ hhor)
  rw [hA, htr]
  simp only [map_add (f := _), map_natCast]


omit [Fintype K] [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem nonzero_of_relevant (y : (Σ k, ι k) → Ω) (h : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (mCoordIdeal y)) :
    ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using h
  refine ⟨c, fun k h0 ↦ hc k ?_⟩
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]

end CoordArithOfFnField


open CoordArithOfFnField in
theorem CoordArithOfFnField.proof : CoordArithOfFnField.Statement := by
  intro K _ ι _ K' _ ι' _ Ω _ _ y y' d hK' hy' hF hA
  obtain ⟨_, ⟨_, _, hrel⟩, _, hdim⟩ := hA
  obtain ⟨c, hc⟩ := nonzero_of_relevant y hrel
  choose c' hc' using hy'
  refine ⟨hK', ⟨RingHom.ker_isPrime _, isMultiHomogIdeal y', relevant y' c' hc'⟩, horizontal y', ?_⟩
  rw [dim_eq y c hc, hF] at hdim
  rw [dim_eq y' c' hc']
  generalize (Algebra.trdeg ℤ (blockFnField y')).toENat = e at hdim ⊢
  induction e using ENat.recTopCoe with
  | top =>
    exfalso
    simp only [top_add] at hdim
    norm_cast at hdim
  | coe n =>
    norm_cast at hdim ⊢
    omega

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem isProjVarF_map_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) :
    IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) D := by
  classical
  have h := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
  exact ⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mp h.1, h.2⟩

section Basis

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]


end Basis

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturbSemipos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace PerturbedSemipositivity

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem blocks_mem_nhds {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    {y : (Σ k, ι k) → ℂ | ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0} ∈ 𝓝 z := by
  have hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
      fun y hy => ⟨i, hy⟩
  exact Filter.eventually_all.mpr hopen

theorem contDiffAt_log_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z := by
  have h := hA.contDiffAt (blocks_mem_nhds hz)
  exact (h.of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)).log (A.pos z hz).ne'

theorem levi_const_mul {f : ((Σ k, ι k) → ℂ) → ℝ} {z : (Σ k, ι k) → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f z)
    (w : (Σ k, ι k) → ℂ) :
    ReciprocityTheory.AnForm.levi (fun y => c * f y) z w = c * ReciprocityTheory.AnForm.levi f z w := by
  have h := ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => (0 : ℝ)) (g := f) c contDiffAt_const hf w
  have h0 : ReciprocityTheory.AnForm.levi (fun _ : (Σ k, ι k) → ℂ => (0 : ℝ)) z w = 0 := by
    simp [ReciprocityTheory.AnForm.levi]
  simp only [zero_add] at h
  rw [h, h0, zero_add]

end PerturbedSemipositivity


open PerturbedSemipositivity in
theorem PerturbSemipos.proof : PerturbSemipos.Statement := by
  intro K _ ι _ P0 P M b a hM hb ha
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  have hH : IsSmoothHerm (fsH ι) := FsLineSmooth.proof K ι
  have hfun : (HermLine.zcomb M (fsH ι) m n).h = fun y => M.h y ^ m * (fsH ι).h y ^ n := by
    funext y
    simp [HermLine.zcomb]
  refine ⟨?_, fun z hz w hw => ?_⟩
  · have hMs : IsSmoothHerm M := hM.1
    unfold IsSmoothHerm at hMs hH ⊢
    rw [hfun]
    exact (hMs.pow m).mul (hH.pow n)
  · have hz' := hz.1
    have hev : (fun y => Real.log ((HermLine.zcomb M (fsH ι) m n).h y)) =ᶠ[𝓝 z]
        fun y => (m : ℝ) * Real.log (M.h y) + (n : ℝ) * Real.log ((fsH ι).h y) := by
      filter_upwards [blocks_mem_nhds hz'] with y hy
      rw [hfun, Real.log_mul (pow_ne_zero _ (M.pos y hy).ne') (pow_ne_zero _ ((fsH ι).pos y hy).ne'),
        Real.log_pow, Real.log_pow]
    have hfM := contDiffAt_log_h M hM.1 hz'
    have hfH := contDiffAt_log_h (fsH ι) hH hz'
    have hadd := ReciprocityTheory.AnForm.levi_add_smul (f := fun y => (m : ℝ) * Real.log (M.h y))
      (g := fun y => Real.log ((fsH ι).h y)) (n : ℝ) (contDiffAt_const.mul hfM) hfH w
    beta_reduce at hadd
    have h1 : 0 ≤ leviForm (fun y => Real.log (M.h y)) z w := hM.2 z hz w hw
    have h2 : 0 ≤ leviForm (fun y => Real.log ((fsH ι).h y)) z w := FsLineLevi.proof K ι z w hz'
    change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
    rw [ReciprocityTheory.AnForm.levi_congr hev, hadd, levi_const_mul (m : ℝ) hfM w]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg m) h1) (mul_nonneg (Nat.cast_nonneg n) h2)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreRepresentatives
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreRepresentatives

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] in
theorem isMultiHomog_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {f : MRingOver R ι}
    {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (map φ f : MRingOver S ι) a :=
  fun m hm => hf m (support_map_subset φ f hm)


omit [Fintype K] in
theorem isMultiHomog_lincomb {f g : MRingOver ℂ ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) (c d : ℂ) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C c * f - C d * g) a := by
  classical
  intro m hm
  rw [C_mul', C_mul'] at hm
  rcases Finset.mem_union.1 (support_sub _ _ _ hm) with h | h
  · exact hf m (support_smul h)
  · exact hg m (support_smul h)

theorem eval_smul {s : MRingOver ℂ ι} {a : K → ℕ} (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) (r : K → ℂ)
    (z : (Σ k, ι k) → ℂ) : eval (fun p => r p.1 * z p) s = (∏ k, r k ^ a k) * eval z s := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ p : (Σ k, ι k), r p.1 ^ d p) = ∏ k, r k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, r k ^ d ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem eval_eq_zero_of_homog {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ f ∈ mCoordIdeal y, (∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) → eval z (map (Int.castRingHom ℂ) f) = 0)
    (f : MRing ι) (hf : f ∈ mCoordIdeal y) : eval z (map (Int.castRingHom ℂ) f) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eq_sum_multihomogeneous_components f, map_sum, map_sum]
  refine Finset.sum_eq_zero fun b _ => hz _ ?_ ⟨b, isMultiHomog_i2comp b f⟩
  exact i2comp_mem (CoordinateConeArithVar.isMultiHomogIdeal y) b hf

end FibreRepresentatives


open FibreRepresentatives in
theorem FibreRepresentatives.proof (h : AvoidFormFinite.Statement) : FibreRepresentatives.Statement := by
  intro K _ ι _ Ω _ y D e L he hL hL0 ζ
  classical
  set Lc : Fin (D + 1) → MRingOver ℂ ι := fun j => map (Int.castRingHom ℂ) (L j) with hLc
  by_cases hζ : ζ = 0
  · refine ⟨∅, by simp, fun z hz ⟨t, ht⟩ => ?_⟩
    obtain ⟨j, hj⟩ := hL0 z hz
    exact absurd (by simpa [hζ] using ht j) hj
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ζ j₀ ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hζ (funext hne)
  let S : Set (MRingOver ℂ ι) :=
    {g | ∃ f ∈ mCoordIdeal y, (∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) ∧ g = map (Int.castRingHom ℂ) f} ∪
      Set.range fun j => C (ζ j₀) * Lc j - C (ζ j) * Lc j₀

  have key : ∀ z : (Σ k, ι k) → ℂ, ((∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ s ∈ S, eval z s = 0) ↔
      (z ∈ mcPts (mCoordIdeal y) ∧ ∃ t : ℂ, ∀ j, eval z (Lc j) = t * ζ j) := by
    intro z
    constructor
    · rintro ⟨hb, hS⟩
      refine ⟨⟨hb, eval_eq_zero_of_homog y z fun f hf ha => hS _ (Or.inl ⟨f, hf, ha, rfl⟩)⟩,
        eval z (Lc j₀) / ζ j₀, fun j => ?_⟩
      have h1 := hS _ (Or.inr ⟨j, rfl⟩)
      simp only [map_sub, map_mul, eval_C] at h1
      field_simp
      linear_combination h1
    · rintro ⟨hz, t, ht⟩
      refine ⟨hz.1, fun s hs => ?_⟩
      rcases hs with ⟨f, hf, -, rfl⟩ | ⟨j, rfl⟩
      · exact hz.2 f hf
      · simp only [map_sub, map_mul, eval_C, ht]
        ring
  have hSh : ∀ s ∈ S, ∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a := by
    rintro s (⟨f, -, ⟨a, ha⟩, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨a, isMultiHomog_map _ ha⟩
    · exact ⟨e, isMultiHomog_lincomb (isMultiHomog_map _ (hL j)) (isMultiHomog_map _ (hL j₀)) _ _⟩
  have hG : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ s ∈ S, eval z s = 0) →
      eval z (Lc j₀) ≠ 0 := by
    intro z hb hS h0
    obtain ⟨hz, t, ht⟩ := (key z).1 ⟨hb, hS⟩
    have ht0 : t = 0 := by
      have := ht j₀
      rw [h0] at this
      exact (mul_eq_zero.1 this.symm).resolve_right hj₀
    obtain ⟨j, hj⟩ := hL0 z hz
    exact hj (by simpa [hLc, ht0] using ht j)
  obtain ⟨T, hT⟩ := h K ι S (Lc j₀) e he (isMultiHomog_map _ (hL j₀)) hSh hG
  refine ⟨T.filter fun t => (∀ k, ∃ i, t ⟨k, i⟩ ≠ 0) ∧ ∀ s ∈ S, eval t s = 0, fun z hz => ?_,
    fun z hz hfib => ?_⟩
  · exact (key z).1 (Finset.mem_filter.1 hz).2
  · obtain ⟨hb, hS⟩ := (key z).2 ⟨hz, hfib⟩
    obtain ⟨t, htT, r, hr, rfl⟩ := hT z hb hS
    have hinv : t = fun p => (r p.1)⁻¹ * (r p.1 * t p) := by
      funext p
      rw [← mul_assoc, inv_mul_cancel₀ (hr p.1), one_mul]
    refine ⟨t, Finset.mem_filter.2 ⟨htT, fun k => ?_, fun s hs => ?_⟩, r, hr, rfl⟩
    · obtain ⟨i, hi⟩ := hb k
      exact ⟨i, fun h0 => hi (by simp [h0])⟩
    · obtain ⟨a, ha⟩ := hSh s hs
      rw [hinv, eval_smul ha (fun k => (r k)⁻¹), hS s hs, mul_zero]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUpperNormalisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Topology

noncomputable section

namespace UpperNormalisation

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem charZero_of_isArithVar {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (C (n : ℤ) : MRing ι) ∈ mCoordIdeal y := by
    show _ ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker, mConeMap, aeval_C]
    have e : (algebraMap ℤ (MvPolynomial K Ω) (n : ℤ)) = C ((n : ℕ) : Ω) := by simp
    rw [e, hn, C_0]
  have hh : (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ := h.2.2.1
  have : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := hmem
  rw [hh, Ideal.mem_bot] at this
  exact_mod_cast this

theorem exists_coord_ne_zero {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) (k : K) :
    ∃ i, y ⟨k, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := h.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  rw [mCoordIdeal, RingHom.mem_ker]
  simp [mConeMap, h0]

theorem secM_le_chartLat (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) {d : K → ℕ}
    (hd : ∀ k, (d k : ℤ) = τ * a k) : secM y d ≤ chartLat y a τ := by
  intro s hs
  have hle : Submodule.span ℤ {s | ∃ g : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d ∧ aeval y g = s} ≤
      (chartLat y a τ).toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩ c _
    have key : aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) =
        aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g := by
      conv_lhs => rw [g.as_sum]
      conv_rhs => rw [g.as_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      simp only [div_eq_mul_inv, mul_pow, Finset.prod_mul_distrib, mul_assoc]
      congr 2
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) = ∏ i, (y ⟨k, c k⟩)⁻¹ ^ m ⟨k, i⟩
      rw [Finset.prod_pow_eq_pow_sum, hg m hm k, ← hd k, zpow_neg, zpow_natCast, inv_pow]
    rw [key, chartRingZ, Algebra.adjoin_range_eq_range_aeval]
    exact ⟨g, rfl⟩
  exact hle hs

end UpperNormalisation


open UpperNormalisation Mono in
theorem UpperNormalisation.proof (h7 : G7.Statement) (hPack : PackingStatement) (hCond : KH.CondStatement) :
    UpperNormalisation.Statement := by
  intro K _ ι _ Ω _ y D B P0 II hD hII har hb hsg hconj hBa ε hε
  have : CharZero Ω := charZero_of_isArithVar har
  set F : ℝ := ((D + 1).factorial : ℝ) with hF
  have hFpos : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _

  set a : K → ℕ := fun k => (B.a k).toNat with hadef
  have ha : ∀ k, (a k : ℤ) = B.a k := fun k => Int.toNat_of_nonneg (by linarith [hBa k])
  have ha1 : ∀ k, 1 ≤ a k := fun k => by have := hBa k; have := ha k; omega
  have hBa' : B.a = fun k => (a k : ℤ) := funext fun k => (ha k).symm

  obtain ⟨k0, c, hc, hc0, hcs⟩ := hCond K ι Ω y a ha1 (exists_coord_ne_zero har) hb
  obtain ⟨q, w, hw, hgen, hwsm⟩ := hsg.gen
  have hcy : aeval y c ∈ chartLat y B.a k0 :=
    secM_le_chartLat y B.a k0 (d := fun κ => k0 * a κ) (fun κ => by push_cast; rw [ha])
      (Submodule.subset_span ⟨c, hc, rfl⟩)
  obtain ⟨Cc, hCc⟩ := SectionBounded.proof K ι Ω y B q w hw hgen hwsm k0 (aeval y c) hcy

  set Ib := II K ι (mCoordIdeal y) (D + 1) (fun _ => B) with hIb
  set G := geomDeg (mCoordIdeal y) B D with hG
  set η : ℝ := ε / (4 * (((D : ℝ) + 1) * (|G| + 1))) with hηdef
  have hη : 0 < η := by positivity
  set B' := HermLine.constShift B (-η) with hB'def
  have hB'a : B'.a = B.a := constShift_a B (-η)
  have hB'h : ∀ z, B'.h z = Real.exp η * B.h z := fun z => by
    show B.h z * Real.exp (-(-η)) = _
    rw [neg_neg, mul_comm]
  have hB'sm : IsSmoothHerm B' := (semipos_constShift hsg.semipos (-η)).1
  obtain ⟨hfin, Cp, hCp⟩ := hPack K ι Ω y D B' (chartLat y B'.a) har hb hB'sm
    (fun τ => chartLat_le_nm y B'.a τ)
  have hG7 := h7 K ι Ω y D B' P0 II hD hII har hb (smallGen_constShift hsg (by linarith))
    (conj_constShift hconj (-η))
  have hCS := ConstantShift.proof K ι (II K ι) (mCoordIdeal y) D B (-η) (hII K ι) har hsg.semipos.1
  have hI' : II K ι (mCoordIdeal y) (D + 1) (fun _ => B') ≤ Ib + ε / 4 := by
    rw [hCS]
    have h1 : ((D : ℝ) + 1) * η * G ≤ ((D : ℝ) + 1) * η * (|G| + 1) :=
      mul_le_mul_of_nonneg_left ((le_abs_self G).trans (by linarith)) (by positivity)
    have h2 : ((D : ℝ) + 1) * η * (|G| + 1) = ε / 4 := by
      rw [hηdef]; field_simp
    linarith

  set v : ℕ → ℝ := fun n => smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) n /
    ((n : ℝ) ^ (D + 1) / F) with hv
  have hv_bdd : ∀ n, v n ≤ |Cp| * F * 2 ^ (D + 1) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hv]
      simp only [Nat.cast_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow, zero_div, div_zero]
      positivity
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hnpos : (0 : ℝ) < (n : ℝ) ^ (D + 1) / F := by positivity
      rw [hv]
      dsimp only
      rw [div_le_iff₀ hnpos]
      have h1 := (hCp n).trans (mul_le_mul_of_nonneg_right (le_abs_self Cp) (by positivity))
      have h2 : ((n : ℝ) + 1) ^ (D + 1) ≤ (2 * n) ^ (D + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
      calc _ ≤ |Cp| * ((n : ℝ) + 1) ^ (D + 1) := h1
        _ ≤ |Cp| * (2 * n) ^ (D + 1) := mul_le_mul_of_nonneg_left h2 (abs_nonneg Cp)
        _ = |Cp| * F * 2 ^ (D + 1) * ((n : ℝ) ^ (D + 1) / F) := by
          rw [mul_pow]
          field_simp
  have hvB : IsBoundedUnder (· ≤ ·) atTop v := isBoundedUnder_of ⟨_, hv_bdd⟩
  have hev1 : ∀ᶠ m in atTop, v m < Ib + ε / 2 :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt (hG7.trans hI') (by linarith)) hvB

  have hcmp : ∀ n : ℕ, Cc ≤ Real.exp (η * ((n + k0 : ℕ) : ℝ)) →
      smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLatNm y B.a) n ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) (n + k0) := by
    intro n hCn
    refine smallSectionCount_le_of_injOn (Q := fun m => IsSmallH (mCoordIdeal y) y B' (m + k0))
      (La' := fun m => chartLat y B'.a (m + k0)) (fun s => aeval y c * s)
      (fun s _ t _ hst => mul_left_cancel₀ hc0 hst) (fun s hs hsm => ⟨?_, ?_⟩) (hfin (n + k0))
    · have hs' : s ∈ chartLatNm y (fun κ => (a κ : ℤ)) n := by rw [← hBa']; exact hs
      have := hcs n s hs'
      show aeval y c * s ∈ chartLat y B'.a (n + k0)
      rw [hB'a]
      exact secM_le_chartLat y B.a (n + k0) (fun κ => by push_cast; rw [ha]) this
    · intro dg dh g h z hg hh hd he hz
      rw [hB'a] at hd
      have hch : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (c * h) ((fun κ => k0 * a κ) + dh) := SectionBounded.homog_mul hc hh
      have h1 := hsm dg ((fun κ => k0 * a κ) + dh) g (c * h) z hg hch
        (fun κ => by simp only [Pi.add_apply]; push_cast; rw [hd κ, ha]; push_cast; ring)
        (by rw [he, map_mul]; ring) hz
      have h2 := hCc (fun κ => k0 * a κ) 0 c 1 z hc SectionBounded.homog_one
        (fun κ => by simp only [Pi.zero_apply]; push_cast; rw [ha]; ring) (by rw [map_one, mul_one]) hz
      rw [map_one, map_one, norm_one, mul_one] at h2
      have hBz : 0 ≤ B.h z := (B.pos z hz.1).le
      rw [map_mul, eval_mul, norm_mul] at h1
      rw [hB'h, mul_pow, ← Real.exp_nat_mul, pow_add]
      have hhn : 0 ≤ ‖eval z (map (Int.castRingHom ℂ) h)‖ * B.h z ^ n := by positivity
      calc ‖eval z (map (Int.castRingHom ℂ) g)‖
          ≤ ‖eval z (map (Int.castRingHom ℂ) c)‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ * B.h z ^ n := h1
        _ ≤ Cc * B.h z ^ k0 * ‖eval z (map (Int.castRingHom ℂ) h)‖ * B.h z ^ n := by
          rw [mul_assoc, mul_assoc (Cc * _)]
          exact mul_le_mul_of_nonneg_right h2 hhn
        _ ≤ Real.exp (η * ((n + k0 : ℕ) : ℝ)) * B.h z ^ k0 * ‖eval z (map (Int.castRingHom ℂ) h)‖ *
            B.h z ^ n := by
          gcongr
        _ = _ := by
          rw [show ((n + k0 : ℕ) : ℝ) * η = η * ((n + k0 : ℕ) : ℝ) from mul_comm _ _]
          ring

  have hlim : Tendsto (fun n : ℕ => (Ib + ε / 2) * (1 + (k0 : ℝ) / n) ^ (D + 1)) atTop (𝓝 (Ib + ε / 2)) := by
    have h0 : Tendsto (fun n : ℕ => (k0 : ℝ) / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h0).pow (D + 1) |>.const_mul (Ib + ε / 2)
  have hev3 : ∀ᶠ n : ℕ in atTop, (Ib + ε / 2) * (1 + (k0 : ℝ) / n) ^ (D + 1) < Ib + ε :=
    hlim.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ n : ℕ in atTop, v (n + k0) < Ib + ε / 2 :=
    (tendsto_add_atTop_nat k0).eventually hev1
  have hevC : ∀ᶠ n : ℕ in atTop, Cc ≤ Real.exp (η * ((n + k0 : ℕ) : ℝ)) := by
    filter_upwards [eventually_ge_atTop (⌈|Cc| / η⌉₊)] with n hn
    have h1 : |Cc| / η ≤ ((n + k0 : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈|Cc| / η⌉₊ ≤ n + k0 by omega))
    have h2 : |Cc| ≤ η * ((n + k0 : ℕ) : ℝ) := by rw [div_le_iff₀ hη] at h1; linarith
    have h3 := Real.add_one_le_exp (η * ((n + k0 : ℕ) : ℝ))
    linarith [le_abs_self Cc]
  filter_upwards [hev2, hev3, hevC, eventually_ge_atTop 1] with n h2 h3 hC hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmpos : (0 : ℝ) < ((n + k0 : ℕ) : ℝ) ^ (D + 1) / F := by
    have : (0 : ℝ) < ((n + k0 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n + k0 by omega)
    positivity
  have hcount : smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) (n + k0) ≤
      (Ib + ε / 2) * (((n + k0 : ℕ) : ℝ) ^ (D + 1) / F) := by
    have := h2
    rw [hv] at this
    dsimp only at this
    rw [div_lt_iff₀ hmpos] at this
    exact this.le
  have hratio : ((n + k0 : ℕ) : ℝ) ^ (D + 1) = (1 + (k0 : ℝ) / n) ^ (D + 1) * (n : ℝ) ^ (D + 1) := by
    rw [← mul_pow]
    congr 1
    push_cast
    field_simp
  calc smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLatNm y B.a) n
      ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) (n + k0) := hcmp n hC
    _ ≤ (Ib + ε / 2) * (((n + k0 : ℕ) : ℝ) ^ (D + 1) / F) := hcount
    _ = ((Ib + ε / 2) * (1 + (k0 : ℝ) / n) ^ (D + 1)) * ((n : ℝ) ^ (D + 1) / F) := by
      rw [hratio]; ring
    _ ≤ (Ib + ε) * ((n : ℝ) ^ (D + 1) / F) :=
      mul_le_mul_of_nonneg_right h3.le (by positivity)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockPieceCycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockPieceCycle.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a b : ℕ, a₀ ≤ a → a₀ ≤ b →
      |twoBlockStep x (matAct B x) a b -
          twoBlockVert x (matAct B x) c l (fun _ : Fin D => ![(a : ℤ), (b : ℤ)]) / (D.factorial : ℝ)| ≤
        C * ((a + b : ℝ) + 1) ^ D / ((a + b : ℝ) + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.TwoBlockModule
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section Module

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def modPieceCard (J₁ J₂ : Ideal (MRing ι)) (a : K → ℕ) : ℕ :=
  (J₂.restrictScalars ℤ ⊓ mHom ι a).toAddSubgroup.relIndex (J₁.restrictScalars ℤ ⊓ mHom ι a).toAddSubgroup

def topComps (J : Ideal (MRing ι)) (d : ℕ) : Set (Ideal (MRing ι)) :=
  {W | W ∈ J.minimalPrimes ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W ∧
    ringKrullDim (MRing ι ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)}

theorem modPieceCard_self (J : Ideal (MRing ι)) (a : K → ℕ) : modPieceCard J J a = 1 :=
  AddSubgroup.relIndex_self _

end Module

section TwoBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def twoBlockMOuter (x x' : Ix κ → Ω) (c : κ) : Ideal (MRing (FinTwoTypeFamily κ)) :=
  twoBlockIdeal x x' ⊔ Ideal.span (Set.range fun j : κ => twoBlockDen c * X ⟨1, j⟩)

def twoBlockMInner (x x' : Ix κ → Ω) (l : Ix κ → ℤ) : Ideal (MRing (FinTwoTypeFamily κ)) :=
  twoBlockIdeal x x' ⊔ Ideal.span (Set.range fun i : κ => twoBlockNum l * X ⟨0, i⟩)

end TwoBlock

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormDehomCharpoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

section Defs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def IsDehomNormForms (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) (j : Fin (D + 1)) (m : ℕ) (s : Ω)
    (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ) : Prop :=
  aeval y (L j) ≠ 0 ∧ ∃ _ : FiniteDimensional (pullField y L) Ω,
    c 0 = 1 ∧ (∀ i ≤ Module.finrank (pullField y L) Ω, (c i).IsHomogeneous (i * m)) ∧
    (LinearMap.charpoly (Algebra.lmul (pullField y L) Ω (s / aeval y (L j) ^ m))).map
        (algebraMap (pullField y L) Ω) =
      ∑ i ∈ Finset.range (Module.finrank (pullField y L) Ω + 1),
        Polynomial.C (aeval (fun i' => aeval y (L i') / aeval y (L j)) (c i)) *
          Polynomial.X ^ (Module.finrank (pullField y L) Ω - i)

end Defs

def FibreNormDehomCharpoly.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    FiniteDimensional (pullField y L) Ω ∧
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ j : Fin (D + 1), aeval y (L j) ≠ 0 →
        ∃ c : ℕ → MvPolynomial (Fin (D + 1)) ℚ, IsDehomNormForms y L j (q * τ) s c ∧
          (s ≠ 0 → c (Module.finrank (pullField y L) Ω) ≠ 0)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullRatiosAlgebraic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullRatiosAlgebraic.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ p q : Σ k, ι k, p.1 = q.1 → IsAlgebraic (pullField y L) (y p / y q)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockMeasure
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def PowerBlockMeasure.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m N D : ℕ) (v : Fin N → Ω) (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι N))
    (J : Ideal (MRing (addIdx ι N))) (R : AnRes (mCoordIdeal (addBlock y v)) J D) [MeasurableSpace R.X]
    [BorelSpace R.X] (dV : Measure R.X),
    IsSmoothHerm A → IsSmoothHerm B → B.a = unitDeg (none : Option K) → IsSmoothVolume R.A dV →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
      secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖) →
    ∃ μ : Measure ((Σ k, ι k) → ℂ), IsProbabilityMeasure μ ∧ μ (mcPts (mCoordIdeal y))ᶜ = 0 ∧
      IsZariskiDenseMeasure (mCoordIdeal y) μ ∧
      ∀ (q : ℕ) (F : MRing (addIdx ι N)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog F (blockDeg (none : Option K) q) →
        sectionL2Norm μ y A (m * q) (aeval (addBlock y v) F) =
          Real.sqrt ((1 / 2) *
            ((∫ x, (‖eval (R.lift x x) (map (Int.castRingHom ℂ) F)‖ / B.h (R.lift x x) ^ q) ^ 2 ∂dV) +
              ∫ x, (‖eval (conjPt (R.lift x x)) (map (Int.castRingHom ℂ) F)‖ /
                B.h (conjPt (R.lift x x)) ^ q) ^ 2 ∂dV))

namespace PowerBlockDiag

open ProjLine PowerBlockProjectiveLine

end PowerBlockDiag

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
