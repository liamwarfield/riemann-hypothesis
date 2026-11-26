module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConjInvariantHZcomb
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPacking
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersectionInt

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMixedIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

namespace BlockResolutionMixedIntegral

theorem proof (hB : BlockResolutionMixedBridge.Statement) (hI : BlockResolutionInterpIntegral.Statement) :
    BlockResolutionMixedIntegral.Statement := by
  intro D K _ _ ι _ Ω _ _ d A' hdeg hA'
  rw [hI D K ι Ω d A' hdeg hA']
  refine Finset.sum_congr rfl fun i _ => ?_
  have hL : ∀ j : Fin D, IsSmoothHerm (if j.val < i then A' else d.A) := fun j => by
    split_ifs
    · exact hA'
    · exact d.semipos.1
  have hpot : blockMixPot d.A A' D i = fun j z => Real.log ((if j.val < i then A' else d.A).h z) := by
    funext j z
    unfold blockMixPot
    split_ifs <;> rfl
  have hres : (fun j : Fin D => AnResBridge.potOf d.R (if j.val < i then A' else d.A)) =
      fun j : Fin D => if j.val < i then AnResBridge.potOf d.R A' else AnResBridge.potOf d.R d.A := by
    funext j
    split_ifs <;> rfl
  rw [hpot, hB D K ι Ω d (fun j => if j.val < i then A' else d.A) A' hL hdeg hA', hres]

end BlockResolutionMixedIntegral

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistMetric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory NumberField Filter Topology

theorem isOpen_multiconePts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem leviForm_eq_of_eventuallyEq_add_const {κ : Type*} [Fintype κ] (φ ψ : (κ → ℂ) → ℝ) (c : ℝ)
    (z w : κ → ℂ) (h : ψ =ᶠ[𝓝 z] fun x => φ x + c) : leviForm ψ z w = leviForm φ z w := by
  have h1 : fderiv ℝ ψ =ᶠ[𝓝 z] fderiv ℝ φ := by
    filter_upwards [h.eventuallyEq_nhds] with x hx
    rw [hx.fderiv_eq, fderiv_add_const]
  unfold leviForm
  rw [h1.fderiv_eq]

theorem TwistMetric.proof (hEW : EmbeddingWeight.Statement)
    (hTI : TwistIntersectionAnyDegree.Statement) : TwistMetric.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D A P0 II u hD hII hY hbir _ hsemi hconj hlies hu hsum
  refine ⟨((D + 1 : ℕ) : ℝ) * genDeg (mCoordIdeal y) D A.a, fun δ hδ => ?_⟩
  obtain ⟨B, hBa, hBs, hBc, hBloc⟩ := hEW K ι Ω F y (fun sg => Real.exp (u sg + δ))
    (fun _ => Real.exp_pos _) (fun sg => by simp only [hu]) hlies
  have hcard : (Fintype.card (F →+* ℂ) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (F →+* ℂ) :=
      Fintype.card_pos_iff.mpr ⟨(IsAlgClosed.lift (R := ℚ) (S := F) (M := ℂ)).toRingHom⟩
    exact_mod_cast this.ne'
  refine ⟨A.tensor B, ?_, ?_, ?_, fun z hz sg hsg => ?_, ?_⟩
  · change A.a + B.a = A.a
    rw [hBa, add_zero]
  · unfold IsSemipositiveRel
    refine ⟨ContDiffOn.mul hsemi.1 hBs, fun z hz w hw => ?_⟩
    obtain ⟨sg, hsg, -⟩ := hlies z hz
    have hzA : ∀ᶠ x in 𝓝 z, A.h x ≠ 0 := by
      filter_upwards [isOpen_multiconePts.mem_nhds hz.1] with x hx using (A.pos x hx).ne'
    have heq : (fun x => Real.log ((A.tensor B).h x)) =ᶠ[𝓝 z]
        fun x => Real.log (A.h x) + Real.log (Real.exp (u sg + δ)) := by
      filter_upwards [hzA, hBloc z hz sg hsg] with x hx hB
      change Real.log (A.h x * B.h x) = _
      rw [hB, Real.log_mul hx (Real.exp_pos _).ne']
    rw [leviForm_eq_of_eventuallyEq_add_const _ _ _ z w heq]
    exact hsemi.2 z hz w hw
  · intro z
    change A.h _ * B.h _ = A.h z * B.h z
    rw [hconj z, hBc z]
  · change A.h z * B.h z = _
    rw [(hBloc z hz sg hsg).self_of_nhds, mul_comm]
  · rw [hTI K ι Ω F y D A B II (fun sg => Real.exp (u sg + δ)) hD hII hY hbir hsemi.1 hBa hBs
      (fun _ => Real.exp_pos _) hlies hBloc]
    have hs : (∑ sg, Real.log ((fun sg => Real.exp (u sg + δ)) sg)) / Fintype.card (F →+* ℂ) = δ := by
      simp only [Real.log_exp, Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, zero_add]
      field_simp
    rw [hs]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionSupBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology

noncomputable section

namespace ResolutionSupBound

theorem eval_smul_homog {ι : Type*} {f : MvPolynomial ι ℂ} {n : ℕ} (hf : f.IsHomogeneous n) (c : ℂ)
    (z : ι → ℂ) : eval (c • z) f = c ^ n * eval z f := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : e.degree = n := by
    by_contra h
    exact (mem_support_iff.mp he) (hf.coeff_eq_zero h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hs : e.degree = ∑ i ∈ e.support, e i := rfl
  rw [← hdeg, hs]
  ring

theorem ptNorm_smul {ι : Type*} (m : ConeMetric ℂ ι) {n : ℕ} {f : MvPolynomial ι ℂ} (hf : f.IsHomogeneous n)
    {c : ℂ} (hc : c ≠ 0) (z : ι → ℂ) :
    ptNorm m (RingHom.id ℂ) n f (c • z) = ptNorm m (RingHom.id ℂ) n f z := by
  have hc' : (0 : ℝ) < ‖c‖ ^ n := pow_pos (norm_pos_iff.2 hc) n
  simp only [ptNorm, MvPolynomial.map_id, eval_smul_homog hf, m.smul, norm_mul, norm_pow, mul_pow]
  exact mul_div_mul_left _ _ hc'.ne'

theorem proof (hI : ResolutionImageSup.Statement) (hND : NonvanishingDense.Statement) :
    ResolutionSupBound.Statement := by
  intro D Ω _ _ κ _ d
  obtain ⟨C, hC⟩ := hI D Ω κ d
  refine ⟨C, fun n hn f hf z hz => ?_⟩
  set B := C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set S := {w | w ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) ∧ eval w (map (Int.castRingHom ℂ) g) ≠ 0}
  have hzm : z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) := by
    refine ⟨fun _ => ?_, hz.2⟩
    by_contra h
    simp only [not_exists, not_not] at h
    exact hz.1 (funext fun q => h q.2)
  have hzS : z ∈ closure S := hND Unit (GlobalTheory κ) (coordIdeal ℤ d.x) (D + 1) g d.arith hgP hzm
  have key : ∀ w ∈ S, ptNorm d.m (RingHom.id ℂ) n f w ≤ B := by
    rintro w ⟨hw, hwg⟩
    obtain ⟨y, c, hc, hyc⟩ := d.R.surj w hw fun h => hwg (h.2 g hgJ)
    have hy : resPt d y = c () • w := by
      rw [resPt, hyc]
      rfl
    rw [← ptNorm_smul d.m hf (hc ()), ← hy]
    exact hC n hn f hf y
  have hρ : ContinuousAt d.m.ρ z :=
    (d.smooth.continuousOn).continuousAt (isOpen_ne.mem_nhds hz.1)
  have hcont : ContinuousAt (ptNorm d.m (RingHom.id ℂ) n f) z := by
    unfold ptNorm
    simp only [MvPolynomial.map_id]
    exact ((MvPolynomial.continuous_eval f).norm.continuousAt).div (hρ.pow n)
      (pow_pos (d.m.pos z hz.1) n).ne'
  have := mem_closure_iff_nhdsWithin_neBot.1 hzS
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall key)

end ResolutionSupBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionRingFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem SectionRingFinite.proof (hL : SectionLatticeFinite.Statement) (hS : SectionSpanStep.Statement) :
    SectionRingFinite.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen
  classical
  obtain ⟨n₀, hn₀⟩ := hS K ι Ω y a q w hy hw hgen
  choose G hG using fun m : ℕ => _root_.AddSubgroup.isAddFG_iff.mp (hL K ι Ω y a m hy)
  set P : Finset (ℕ × Ω) :=
    (Finset.range (n₀ + 1)).biUnion fun m => (G m).image fun g => (m, g) with hP
  have memP : ∀ m g, m ≤ n₀ → g ∈ G m → (m, g) ∈ P := by
    intro m g hm hg
    rw [hP, Finset.mem_biUnion]
    exact ⟨m, Finset.mem_range.2 (Nat.lt_succ_of_le hm), Finset.mem_image.2 ⟨g, hg, rfl⟩⟩
  have ofP : ∀ x ∈ P, x.2 ∈ chartLat y a x.1 := by
    intro x hx
    rw [hP, Finset.mem_biUnion] at hx
    obtain ⟨m, _, hx⟩ := hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    rw [← hG m]
    exact AddSubgroup.subset_closure hg
  let f : Fin P.card → ℕ × Ω := fun i => (P.equivFin.symm i).1
  let T : ℕ → Set Ω := fun n =>
    {s | ∃ (i : Fin P.card) (μ : Fin q → ℕ), (f i).1 + ∑ j, μ j = n ∧ s = (f i).2 * ∏ j, w j ^ μ j}
  have base : ∀ n, n ≤ n₀ → chartLat y a n ≤ AddSubgroup.closure (T n) := by
    intro n hn
    rw [← hG n, AddSubgroup.closure_le]
    intro g hg
    apply AddSubgroup.subset_closure
    refine ⟨P.equivFin ⟨(n, g), memP n g hn hg⟩, 0, ?_, ?_⟩ <;> simp [f]
  have step : ∀ n (j : Fin q), ∀ s ∈ AddSubgroup.closure (T n),
      s * w j ∈ AddSubgroup.closure (T (n + 1)) := by
    intro n j s hs
    induction hs using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, μ, hdeg, rfl⟩ := hx
      apply AddSubgroup.subset_closure
      refine ⟨i, μ + Pi.single j 1, ?_, ?_⟩
      · simp only [Pi.add_apply, Finset.sum_add_distrib]
        rw [← hdeg, Finset.sum_pi_single']
        simp [add_assoc]
      · have hprod : ∏ k, w k ^ ((μ + Pi.single j 1 : Fin q → ℕ) k) = (∏ k, w k ^ μ k) * w j := by
          simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
          congr 1
          rw [Fintype.prod_eq_single j]
          · simp
          · intro k hk
            simp [hk]
        rw [hprod, mul_assoc]
    | zero => simp
    | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
    | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  refine ⟨P.card, fun i => (f i).1, fun i => (f i).2, fun i => ofP _ (P.equivFin.symm i).2, ?_⟩
  intro n
  induction n with
  | zero => exact base 0 (Nat.zero_le _)
  | succ n ih =>
    by_cases h : n + 1 ≤ n₀
    · exact base _ h
    · have hn : n₀ ≤ n := by omega
      refine (hn₀ n hn).trans ?_
      rw [AddSubgroup.closure_le]
      rintro t ⟨s, hs, j, rfl⟩
      exact step n j s (ih hs)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionSupBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology

noncomputable section

namespace BlockResolutionSupBound

section Invariance

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eval_torus {f : MRingOver ℂ ι} {k₀ : K} {n : ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg k₀ n))
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) f = c k₀ ^ n * eval z f := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hf m hm
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = c k₀ ^ n := by
    rw [Fintype.prod_sigma]
    simp_rw [Finset.prod_pow_eq_pow_sum, hdeg]
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [blockDeg, hk]]
    simp [blockDeg]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem normRatio_torus {f : MRingOver ℂ ι} {k₀ : K} {n : ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg k₀ n))
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : A.a = unitDeg k₀) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ‖eval z f‖ / A.h z ^ n = ‖eval z' f‖ / A.h z' ^ n := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [eval_torus hf, A.smul c z' hc, hA]
  have hprod : ∏ k, ‖c k‖ ^ unitDeg k₀ k = ‖c k₀‖ := by
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [unitDeg, hk]]
    simp [unitDeg]
  rw [hprod, norm_mul, norm_pow, mul_pow]
  have : ‖c k₀‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hc k₀))
  rw [mul_div_mul_left _ _ this]


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

end Invariance

theorem proof (hI : BlockResolutionImageSup.Statement) (hN : NonvanishingDense.Statement) :
    BlockResolutionSupBound.Statement := by
  intro D K _ _ ι _ Ω _ _ d
  obtain ⟨C, hC⟩ := hI D K ι Ω d
  refine ⟨C, fun n hn f hf z hz => ?_⟩
  set g : ((Σ k, ι k) → ℂ) → ℝ := fun w => ‖eval w f‖ / d.A.h w ^ n with hg
  set M := C * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2NormComplex d n f with hM

  have hoff : ∀ w ∈ mcPts (mCoordIdeal d.y), w ∉ mcPts d.J → g w ≤ M := by
    intro w hw hwJ
    obtain ⟨x, hx⟩ := d.R.surj w hw hwJ
    calc g w = g (blockPt d x) := (normRatio_torus hf d.A d.deg hx).symm
      _ ≤ M := hC n hn f hf x

  obtain ⟨F, hFJ, hFP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set S := {w | w ∈ mcPts (mCoordIdeal d.y) ∧ eval w (map (Int.castRingHom ℂ) F) ≠ 0} with hSdef
  have hcl : z ∈ closure S := hN K ι (mCoordIdeal d.y) (D + 1) F d.arith hFP hz
  have hSM : ∀ w ∈ S, g w ≤ M := fun w hw => hoff w hw.1 fun hJ => hw.2 (hJ.2 F hFJ)
  have hcont : ContinuousAt g z := by
    have hh : ContinuousAt d.A.h z :=
      d.semipos.1.continuousOn.continuousAt (isOpen_blockNonzero.mem_nhds hz.1)
    exact (continuous_norm.comp (MvPolynomial.continuous_eval _)).continuousAt.div (hh.pow n)
      (pow_ne_zero _ (d.A.pos z hz.1).ne')
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall hSM)

end BlockResolutionSupBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PScaledFSHProps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi (sqSum)
open GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi (levi_Phi leviForm_phi_nonneg isOpen_noZeroBlock blk)

namespace ScaledFSHProps

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isSmoothHerm : IsSmoothHerm (scaledFSH ι) :=
  (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs (ι := ι) 1).mul
    (contDiffOn_const (c := Real.exp (-(-1 : ℝ))))

theorem log_h_eventuallyEq {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (fun y => Real.log ((scaledFSH ι).h y)) =ᶠ[𝓝 z]
      fun y => (∑ k, Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩))) + 1 := by
  filter_upwards [isOpen_noZeroBlock.mem_nhds hz] with y hy
  have hρ : ∀ k, (fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩) ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hy k
    exact ((fsMetric (ι := ι k)).pos _ fun h0 => hi (congrFun h0 i)).ne'
  rw [scaledFSH_h, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => hρ k) (Real.exp_pos 1).ne',
    Real.log_exp, Real.log_prod fun k _ => hρ k]

theorem leviForm_log_h_nonneg {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    0 ≤ leviForm (fun y => Real.log ((scaledFSH ι).h y)) z w := by
  have hd : fderiv ℝ (fun y => Real.log ((scaledFSH ι).h y)) =ᶠ[𝓝 z]
      fderiv ℝ (fun y => ∑ k, Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩))) := by
    filter_upwards [(log_h_eventuallyEq hz).fderiv (𝕜 := ℝ)] with y hy
    rw [hy]
    exact fderiv_add_const (1 : ℝ)
  have hL : leviForm (fun y => Real.log ((scaledFSH ι).h y)) z w =
      leviForm (fun y => ∑ k, Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩))) z w := by
    unfold leviForm
    rw [hd.fderiv_eq]
  rw [hL, levi_Phi hz w]
  refine Finset.sum_nonneg fun k _ => leviForm_phi_nonneg ?_ _
  obtain ⟨i, hi⟩ := hz k
  refine (lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2) ?_).ne'
  exact Finset.single_le_sum (f := fun j => ‖blk k z j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem isSemipositiveRel (P0 P : Ideal (MRing ι)) : IsSemipositiveRel P0 P (scaledFSH ι) :=
  ⟨isSmoothHerm, fun _ hz w _ => leviForm_log_h_nonneg hz.1 w⟩

theorem isConjInvariantH : IsConjInvariantH (scaledFSH ι) := by
  intro z
  rw [scaledFSH_h, scaledFSH_h]
  simp [fsMetric, EuclideanSpace.norm_eq]

theorem norm_le_rho (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k) :
    ‖z ⟨k, i⟩‖ ≤ (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) := by
  show ‖z ⟨k, i⟩‖ ≤ ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖
  simpa using PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) i

theorem monomialsBounded (P : Ideal (MRing ι)) : MonomialsBounded P (scaledFSH ι) (fun _ => 1) := by
  intro z _ μ hμ
  rw [scaledFSH_h, norm_prod, Fintype.prod_sigma]
  have hρ : ∀ k, 0 ≤ (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) := fun k => norm_nonneg _
  have hblk : ∀ k, ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) := by
    intro k
    calc ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ ∏ i, (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) ^ μ ⟨k, i⟩ := by
          refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_rho z k i) _
      _ = (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) := by
          rw [Finset.prod_pow_eq_pow_sum, hμ k]
          exact pow_one _
  calc ∏ k, ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ ∏ k, (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) :=
        Finset.prod_le_prod₀ (fun k _ => Finset.prod_nonneg fun i _ => norm_nonneg _) fun k _ => hblk k
    _ ≤ (∏ k, (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩)) * Real.exp 1 :=
        le_mul_of_one_le_right (Finset.prod_nonneg fun k _ => hρ k) (Real.one_le_exp zero_le_one)

end ScaledFSHProps

theorem ScaledFSHProps.proof : ScaledFSHProps.Statement := fun _ _ _ _ P P0 =>
  ⟨ScaledFSHProps.isSemipositiveRel P0 P, ScaledFSHProps.isConjInvariantH, ScaledFSHProps.monomialsBounded P⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallPacking
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

theorem SmallPacking.proof (hR : NmSectionsRankBound.Statement) (hS : SmallSectionsSeparated.Statement) :
    SmallPacking.Statement := by
  classical
  intro K _ ι _ Ω _ y D A La hX hB hA hLa
  obtain ⟨hfin, C₁, hC₁, hrank⟩ := hR K ι Ω y D A.a hX hB
  obtain ⟨C, hC, hsep⟩ := hS K ι Ω y D A hX hB hA
  have key : ∀ (τ : ℕ) (T : Finset (La τ)), (∀ s ∈ T, IsSmallH (mCoordIdeal y) y A τ (s : Ω)) →
      Real.log T.card ≤ C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3) := by
    intro τ T hT
    obtain ⟨Z, ev, hZ, hrep, hsepτ⟩ := hsep τ
    have hpos : ∀ z : Z, 0 < A.h z := fun z => A.pos _ (hZ z z.2).1
    let φ : chartLatNm y A.a τ →+ (Z → ℂ) :=
      { toFun := fun s z => ev s z / ((A.h z : ℂ) ^ τ)
        map_zero' := by funext z; simp
        map_add' := by intro s t; funext z; simp [add_div] }
    have hφ : ∀ s z, ‖φ s z‖ = ‖ev s z‖ / A.h z ^ τ := fun s z => by
      simp [φ, norm_pow, abs_of_pos (hpos z)]
    have hnorm : ∀ s : chartLatNm y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) → ‖φ s‖ ≤ 1 := by
      intro s hs
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun z => ?_
      obtain ⟨dg, dh, g, h, hg, hh, hdeg, heq, hz0, hev⟩ := hrep s z
      have hle := hs dg dh g h z hg hh hdeg heq (hZ z z.2)
      rw [← hev, norm_mul] at hle
      rw [hφ, div_le_one (pow_pos (hpos z) τ)]
      exact le_of_mul_le_mul_right (by linarith) (norm_pos_iff.2 hz0)
    have hdist : ∀ s t : chartLatNm y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) →
        IsSmallH (mCoordIdeal y) y A τ (t : Ω) → s ≠ t →
        Real.exp (-(C * ((τ : ℝ) + 1))) ≤ ‖φ s - φ t‖ := by
      intro s t hs ht hst
      obtain ⟨z, hz⟩ := hsepτ s t hs ht hst
      refine le_trans ?_ (norm_le_pi_norm (φ s - φ t) z)
      rw [← map_sub φ, hφ, map_sub ev, Pi.sub_apply, le_div_iff₀ (pow_pos (hpos z) τ)]
      exact hz
    let ι' : La τ →+ chartLatNm y A.a τ := AddSubgroup.inclusion (hLa τ)
    have := hfin τ
    let L : Submodule ℤ (Z → ℂ) := LinearMap.range φ.toIntLinearMap
    have hsmall : ∀ s ∈ T, IsSmallH (mCoordIdeal y) y A τ ((ι' s : chartLatNm y A.a τ) : Ω) := hT
    have hinj : Set.InjOn (fun s => φ (ι' s)) T := by
      intro s hs t ht hst
      by_contra hne
      have hne' : ι' s ≠ ι' t := fun h => hne (Subtype.ext (by simpa [ι'] using congrArg Subtype.val h))
      have := hdist _ _ (hsmall s hs) (hsmall t ht) hne'
      simp only at hst
      rw [hst, sub_self, norm_zero] at this
      exact absurd this (not_le.2 (Real.exp_pos _))
    have hP := Packing.proof (Z → ℂ) L (T.image fun s => φ (ι' s)) (C * ((τ : ℝ) + 1)) (by positivity)
      (by intro v hv; obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hv; exact ⟨ι' s, rfl⟩)
      (by intro v hv; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv; exact hnorm _ (hsmall s hs))
      (by
        intro v hv w hw hvw
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hw
        exact hdist _ _ (hsmall s hs) (hsmall t ht) fun h => hvw (by rw [h]))
    rw [Finset.card_image_of_injOn hinj] at hP
    have hL : (Module.finrank ℤ L : ℝ) ≤ Module.finrank ℤ (chartLatNm y A.a τ) := by
      exact_mod_cast LinearMap.finrank_range_le φ.toIntLinearMap
    refine hP.trans (mul_le_mul_of_nonneg_right (hL.trans (hrank τ)) (by positivity))
  have hfinite : ∀ τ, {s : La τ | IsSmallH (mCoordIdeal y) y A τ (s : Ω)}.Finite := by
    intro τ
    by_contra hinf
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf
      (⌈Real.exp (C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3))⌉₊ + 1)
    have h1 := key τ T (fun s hs => hTsub hs)
    rw [hTcard, Real.log_le_iff_le_exp (by positivity)] at h1
    push_cast at h1
    linarith [Nat.le_ceil (Real.exp (C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3)))]
  refine ⟨hfinite, C₁ * (C + Real.log 3), fun τ => ?_⟩
  unfold smallSectionCount
  rw [show Nat.card {s : La τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} = (hfinite τ).toFinset.card from
    Nat.card_eq_card_finite_toFinset (hfinite τ)]
  refine (key τ _ fun s hs => (hfinite τ).mem_toFinset.1 hs).trans ?_
  have h1 : (1 : ℝ) ≤ (τ : ℝ) + 1 := by linarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ)]
  have hl : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  calc C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3)
      ≤ C₁ * ((τ : ℝ) + 1) ^ D * ((C + Real.log 3) * ((τ : ℝ) + 1)) := by gcongr; nlinarith
    _ = C₁ * (C + Real.log 3) * ((τ : ℝ) + 1) ^ (D + 1) := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CoeffLeOfEvalLeMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

namespace ArithmeticVolumeDegreeZero

theorem arithmeticVolume_nonneg {Ω : Type*} [CommRing Ω] (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (a D : ℕ) :
    0 ≤ arVolP P La a D := by
  unfold arVolP
  have hu : ∀ k : ℕ, 0 ≤ smallSectionCount P La (a * k) / (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) :=
    fun k => div_nonneg (Real.log_natCast_nonneg _) (by positivity)
  by_cases hb : IsBoundedUnder (· ≤ ·) atTop
      (fun k : ℕ => smallSectionCount P La (a * k) / (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)))
  · exact le_limsup_of_frequently_le (Frequently.of_forall hu) hb
  · rw [Real.limsup_of_not_isBoundedUnder hb]

theorem charZero_of_horizontal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (h : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (MvPolynomial.C (n : ℤ) : MRing ι) ∈ mCoordIdeal y := by
    show mConeMap y (MvPolynomial.C (n : ℤ)) = 0
    rw [mConeMap, MvPolynomial.aeval_C, eq_intCast, Int.cast_natCast,
      ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  have h' : (n : ℤ) ∈ (mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* MRing ι) := hmem
  rw [h] at h'
  exact_mod_cast (Submodule.mem_bot _).mp h'

theorem coeff_le_of_eval_le_mul {D : ℕ} (p r : Polynomial ℝ) {C : ℝ} (hC : 0 ≤ C) (hp : p.natDegree ≤ D + 1)
    (hr : r.natDegree ≤ D) (hrD : r.coeff D ≤ 0)
    (h : ∀ q : ℕ, 1 ≤ q → p.eval (q : ℝ) ≤ C * ((q : ℝ) + 1) * r.eval (q : ℝ)) : p.coeff (D + 1) ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  set g : Polynomial ℝ := p - Polynomial.C C * ((Polynomial.X + 1) * r) with hg
  have hr1 : r.coeff (D + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hgc : g.coeff (D + 1) = p.coeff (D + 1) - C * r.coeff D := by
    rw [hg, Polynomial.coeff_sub, Polynomial.coeff_C_mul, add_mul, one_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_mul, hr1, add_zero]
  have hgpos : 0 < g.coeff (D + 1) := by
    rw [hgc]; nlinarith
  have hgdeg : g.natDegree ≤ D + 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le hp ?_)
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_mul_le).trans ?_
    have : (Polynomial.X + 1 : Polynomial ℝ).natDegree ≤ 1 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le Polynomial.natDegree_X_le ?_)
      simp
    omega
  have hgnat : g.natDegree = D + 1 :=
    le_antisymm hgdeg (Polynomial.le_natDegree_of_ne_zero hgpos.ne')
  have hlead : 0 ≤ g.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hgnat]; exact hgpos.le
  have hdeg : 0 < g.degree := by
    rw [Polynomial.degree_eq_natDegree (fun h0 => by simp [h0] at hgpos), hgnat]
    exact_mod_cast Nat.succ_pos D
  have ht := (g.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlead).comp tendsto_natCast_atTop_atTop
  obtain ⟨q, hq1, hq⟩ := ((eventually_ge_atTop 1).and (ht.eventually (eventually_gt_atTop 0))).exists
  have hev : g.eval (q : ℝ) = p.eval (q : ℝ) - C * ((q : ℝ) + 1) * r.eval (q : ℝ) := by
    simp only [hg, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    ring
  have := h q hq1
  simp only [Function.comp_apply] at hq
  linarith

end ArithmeticVolumeDegreeZero

theorem ArithmeticVolumeDegreeZero.proof (hB : G6.StatementB) (hN : ShiftNefBig.Statement) (hV : ShiftVolumeBound.Statement)
    (hI : ShiftIntersectionPolynomial.Statement) (hG : ShiftDegreePolynomial.Statement) :
    ArithmeticVolumeDegreeZero.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hD hII har hb hP0 hs hnef hc hdeg
  have : CharZero Ω := ArithmeticVolumeDegreeZero.charZero_of_horizontal y har.2.2.1
  refine le_trans ?_ (ArithmeticVolumeDegreeZero.arithmeticVolume_nonneg _ _ _ _)
  obtain ⟨C, hC0, hC⟩ := hV K ι Ω y D A P0 hD har hb hP0 hs hnef hc
  obtain ⟨p, hpdeg, hpc, hp⟩ := hI K ι II (mCoordIdeal y) (D + 1) A (fsH ι) hII har hs.1
    (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1)
  obtain ⟨r, hrdeg, hrc, hr⟩ := hG K ι (mCoordIdeal y) D A.a ((1 : ℤ) • (fsH ι).a) har
  have hbound : ∀ q : ℕ, 1 ≤ q → p.eval (q : ℝ) ≤ C * ((q : ℝ) + 1) * r.eval (q : ℝ) := by
    intro q hq
    rw [← hp q, ← hr q]
    exact (hB K ι Ω y D _ P0 II hD hII har hb (hN K ι Ω y D A P0 hD har hb hP0 hs hnef hc q hq)).trans (hC q hq)
  rw [← hpc]
  exact ArithmeticVolumeDegreeZero.coeff_le_of_eval_le_mul p r hC0 hpdeg hrdeg (by rw [hrc]; exact_mod_cast hdeg) hbound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageMetrics
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ProjLine
open scoped Topology

noncomputable section

namespace BlockImageMetrics

theorem leviForm_comp_clm {E F : Type} [Fintype E] [Fintype F] (L : (E → ℂ) →L[ℂ] (F → ℂ))
    {φ : (F → ℂ) → ℝ} {z : E → ℂ} (hφ : ContDiffAt ℝ 2 φ (L z)) (w : E → ℂ) :
    leviForm (fun y => φ (L y)) z w = leviForm φ (L z) (L w) := by
  set Lr : (E → ℂ) →L[ℝ] (F → ℂ) := L.restrictScalars ℝ with hLr
  have hev : fderiv ℝ (fun y => φ (L y)) =ᶠ[𝓝 z] fun y => (fderiv ℝ φ (Lr y)).comp Lr := by
    have h1 : ∀ᶠ x in 𝓝 (L z), ContDiffAt ℝ 2 φ x := hφ.eventually (by simp)
    have h2 : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 φ (L y) := (L.continuous.tendsto z).eventually h1
    filter_upwards [h2] with y hy
    have hd : DifferentiableAt ℝ φ (Lr y) := hy.differentiableAt (by norm_num)
    exact (hd.hasFDerivAt.comp y Lr.hasFDerivAt).fderiv
  have hd2 : DifferentiableAt ℝ (fderiv ℝ φ) (Lr z) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD : HasFDerivAt (fun y => (fderiv ℝ φ (Lr y)).comp Lr)
      ((ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ (fderiv ℝ φ (Lr z))).comp 0 +
        ((ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ).flip Lr).comp
          ((fderiv ℝ (fderiv ℝ φ) (Lr z)).comp Lr)) z :=
    (hd2.hasFDerivAt.comp z Lr.hasFDerivAt).clm_comp (hasFDerivAt_const Lr z)
  have hIw : L (Complex.I • w) = Complex.I • L w := L.map_smul _ _
  unfold leviForm
  rw [hev.fderiv_eq, hD.fderiv]
  simp [hLr, hIw]

theorem isSemipositiveRel_of_linear {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {F : Type}
    [Fintype F] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (L : ((Σ k, ι k) → ℂ) →L[ℂ] (F → ℂ))
    (hA : A.h = fun z => (fsMetric (ι := F)).ρ (L z)) (hL : ∀ z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → L z ≠ 0)
    (P0 P : Ideal (MRing ι)) : IsSemipositiveRel P0 P A := by
  have hsm : ∀ z, L z ≠ 0 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fsMetric (ι := F)).ρ (L z) := fun z hz =>
    (isSmoothMetric_fs (J := F) (L z) hz).contDiffAt (isOpen_ne.mem_nhds hz)
  refine ⟨?_, fun z hz w _ => ?_⟩
  · unfold IsSmoothHerm
    rw [hA]
    intro z hz
    exact ((hsm z (hL z hz)).comp z (L.restrictScalars ℝ).contDiff.contDiffAt).contDiffWithinAt
  · have hz0 := hL z hz.1
    have hlog : ContDiffAt ℝ 2 (fun x => Real.log ((fsMetric (ι := F)).ρ x)) (L z) :=
      ((hsm z hz0).of_le (WithTop.coe_le_coe.2 le_top)).log ((fsMetric (ι := F)).pos _ hz0).ne'
    rw [show (fun z => Real.log (A.h z)) =
      fun y => (fun x => Real.log ((fsMetric (ι := F)).ρ x)) (L y) by rw [hA]]
    rw [leviForm_comp_clm L hlog w]
    exact leviForm_log_fs_nonneg hz0 _

def matCLM {κ J : Type} [Fintype κ] [Fintype J] (N : Matrix κ J ℤ) : (J → ℂ) →L[ℂ] (κ → ℂ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin (N.map (Int.cast : ℤ → ℂ)))

theorem matCLM_apply {κ J : Type} [Fintype κ] [Fintype J] (N : Matrix κ J ℤ) (u : J → ℂ) :
    matCLM N u = fun i => ∑ j, (N i j : ℂ) * u j := by
  funext i
  simp [matCLM, Matrix.mulVec, dotProduct]

def blockCLM {K : Type} {ι : K → Type} (k₀ : K) : ((Σ k, ι k) → ℂ) →L[ℂ] (ι k₀ → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (⟨k₀, i⟩ : Σ k, ι k)

theorem blockCLM_apply {K : Type} {ι : K → Type} (k₀ : K) (z : (Σ k, ι k) → ℂ) :
    blockCLM k₀ z = fun i => z ⟨k₀, i⟩ := rfl

theorem proof : BlockImageMetrics.Statement := by
  constructor
  · intro κ J _ _ N hN P
    refine isSemipositiveRel_of_linear _ (matCLM N) ?_ ?_ ⊥ P
    · funext u
      rw [matCLM_apply]
      rfl
    · intro z hz h0
      rw [matCLM_apply] at h0
      obtain ⟨i, hi⟩ := hz ()
      exact hi (congrFun (hN z h0) _)
  · intro K _ _ ι _ k₀ P
    refine isSemipositiveRel_of_linear _ (blockCLM k₀) ?_ ?_ ⊥ P
    · funext z
      rw [blockCLM_apply]
      simp only [ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics]
      rw [Finset.prod_eq_single k₀ (fun k _ hk => by simp [unitDeg, hk]) (by simp)]
      simp [unitDeg]
    · intro z hz h0
      obtain ⟨i, hi⟩ := hz k₀
      exact hi (congrFun h0 i)

end BlockImageMetrics

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSpanStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionSpanStep

variable {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]

theorem mul_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n j : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a j) : s * t ∈ chartLat y a (n + j) := by
  intro c hc
  have h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  rw [h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]
  exact MulMemClass.mul_mem (hs c hc) (ht c hc)

theorem prod_pow_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {q : ℕ} {w : Fin q → Ω}
    (hw : ∀ j, w j ∈ chartLat y a 1) (ν : Fin q → ℕ) (S : Finset (Fin q)) :
    ∏ j ∈ S, w j ^ ν j ∈ chartLat y a (∑ j ∈ S, ν j) := by
  have hpow : ∀ (j : Fin q) (e : ℕ), w j ^ e ∈ chartLat y a e := by
    intro j e
    induction e with
    | zero => intro c _; simp
    | succ e ih => rw [pow_succ]; exact mul_mem ih (hw j)
  refine Finset.induction_on S ?_ ?_
  · intro c _
    simp
  · intro j S hj ih
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact mul_mem (hpow j (ν j)) ih

end SectionSpanStep


open SectionSpanStep in
theorem SectionSpanStep.proof (hH : SpanStepHomog.Statement) (hS : SerreGraded.Statement) :
    SectionSpanStep.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen
  obtain ⟨m, r, t, ht, hloc⟩ := hH K ι Ω y a q w hy hw hgen
  have hne : ∃ j, w j ≠ 0 := by
    by_contra h
    push Not at h
    choose c hc using hy
    obtain ⟨u, -, hu⟩ := hgen c hc
    simp [h] at hu
  obtain ⟨n₀, hn₀⟩ := hS Ω q r w (fun _ => m) t hne
  refine ⟨max n₀ m, fun n hn s hs => ?_⟩
  have hs' : s ∈ gradedSpan w (fun _ => m) t (n + 1) :=
    hn₀ (n + 1) (by omega) s fun j hj => hloc (n + 1) s hs j hj
  refine (AddSubgroup.closure_le _).2 ?_ hs'
  rintro x ⟨l, μ, hdeg, rfl⟩
  have hdeg : m + ∑ i, μ i = n + 1 := hdeg
  obtain ⟨j, hj⟩ : ∃ j, 0 < μ j := by
    by_contra h
    push Not at h
    have h0 : ∑ i, μ i = 0 := Finset.sum_eq_zero fun i _ => Nat.le_zero.1 (h i)
    omega
  set μ' : Fin q → ℕ := μ - Pi.single j 1 with hμ'
  have hμ : μ = μ' + Pi.single j 1 := by
    funext i
    by_cases hij : i = j
    · subst hij
      simp [hμ']
      omega
    · simp [hμ', hij]
  have hsum : ∑ i, μ i = ∑ i, μ' i + 1 := by
    rw [hμ]
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
    simp
  have hprod : ∏ i, w i ^ μ i = (∏ i, w i ^ μ' i) * w j := by
    rw [hμ]
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_eq_single j]
    · simp
    · intro i hi
      simp [hi]
  apply AddSubgroup.subset_closure
  refine ⟨t l * ∏ i, w i ^ μ' i, ?_, j, by rw [hprod, mul_assoc]⟩
  have hmem := mul_mem (ht l) (prod_pow_mem hw μ' Finset.univ)
  have hdeg' : m + ∑ i, μ' i = n := by omega
  rwa [hdeg'] at hmem

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKleimanScheme
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem nefOnF_mono {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {I : IFamily F ι} {V Q : Ideal (MRingOver F ι)} {α : K → ℤ} (hN : KH.NefOnF I V α) (hVQ : V ≤ Q) :
    KH.NefOnF I Q α :=
  fun W hW hQW => hN W hW (hVQ.trans hQW)

theorem ampleV_of_nsmul {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {V : Ideal (MRingOver S ι)} {N : K → ℤ} {q : ℕ} (hq : 1 ≤ q)
    (h : KH.AmpleV S V (q • N)) : KH.AmpleV S V N := by
  obtain ⟨q₂, hq₂, hgen, hvan⟩ := h
  refine ⟨q₂ * q, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, fun e => ?_⟩
  · rwa [mul_smul]
  · obtain ⟨c₁, hc⟩ := hvan e
    refine ⟨c₁, fun c hc' => ?_⟩
    have := hc c hc'
    rwa [smul_smul, mul_assoc] at this

theorem KleimanScheme.proof (hVar : KleimanVarietyH1Generation.Statement) (hDev : H1GenerationDevissage.Statement)
    (hGen : GenerationOfH1GenAmple.Statement) (hAG : AmpleOfGenTwist.Statement) : KleimanScheme.Statement := by
  intro F _ K _ _ ι _ _ I V α b a hI hV hN hb ha

  have hamp : H1GenAmple F V (b • α + fun _ => (a : ℤ)) :=
    hDev F K ι V _ inferInstance fun P hP hVP => hVar F K ι I P α b a hI hP (nefOnF_mono hN hVP) hb ha

  obtain ⟨c₁, hc⟩ := hGen F K ι V _ hV hamp (fun _ => -1)
  have hg := hc (c₁ + 1) (Nat.le_succ c₁)

  have h := hAG F K ι V _ 1 1 hV hg le_rfl
  have e : ((1 : ℕ) : ℤ) • ((fun _ => (-1 : ℤ)) + (c₁ + 1) • (b • α + fun _ => (a : ℤ))) +
      (fun _ => ((1 : ℕ) : ℤ)) = (c₁ + 1) • (b • α + fun _ => (a : ℤ)) := by
    funext k
    simp only [Nat.cast_one, one_smul, Pi.add_apply]
    ring
  rw [e] at h
  exact ampleV_of_nsmul (Nat.le_add_left 1 c₁) h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
