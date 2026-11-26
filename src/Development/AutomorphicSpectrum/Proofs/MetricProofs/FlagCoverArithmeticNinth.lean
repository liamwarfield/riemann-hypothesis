module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesPullback
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesAtBasePoint

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointMapsToPoints
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointMapsToPoints
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem comp_v_mem_mcPts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ), zb ∈ mcPts (mCoordIdeal M'.x) → zb ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv zb hz
  have hb := Cv.block
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 (Cv.κ k)
    obtain ⟨p, hp⟩ := hb.2.2.2 ⟨Cv.κ k, i⟩ ⟨k, rfl⟩
    have hk : p.1 = k := hb.1 (by have h := hb.2.2.1 p; rw [hp] at h; exact h.symm)
    obtain ⟨k₀, i₀⟩ := p
    cases hk
    exact ⟨i₀, by simpa [Function.comp, hp] using hi⟩
  · have key : ∀ g, mConeMap (M'.x ∘ Cv.v) g = MvPolynomial.map Cv.φ (mConeMap M.x g) := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a => simp [mConeMap]
      | add p q hp hq => simp only [map_add (f := _), hp, hq]
      | mul_X p n hp =>
        simp only [map_mul, hp]
        congr 1
        simp [mConeMap, Cv.x_eq]
    have h0 : mConeMap M.x f = 0 := hf
    have h1 : f ∈ mCoordIdeal (M'.x ∘ Cv.v) := by
      show mConeMap (M'.x ∘ Cv.v) f = 0
      rw [key, h0, map_zero]
    have h2 : rename Cv.v f ∈ mCoordIdeal M'.x :=
      GlobalTheory.CompanionTheory.Ar.PB.FA.ImageIdeal.mCoordIdeal_comp_le_imageZ _ _ _ _ Cv.κ Cv.v _ M'.x hb h1
    have h3 := hz.2 _ h2
    rwa [map_rename, eval_rename] at h3

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointMapsToPointsStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_base_point_maps_to_points : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ), zb ∈ mcPts (mCoordIdeal M'.x) → zb ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.comp_v_mem_mcPts | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.comp_v_mem_mcPts | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.comp_v_mem_mcPts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBlockFieldEq
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionInBlockField
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionInBlockField
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField

private theorem aeval_mul_scale_of_homog {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {S : Type} [CommRing S] [Algebra ℤ S] (f : MvPolynomial (Σ k, ι k) ℤ) (d : K → ℕ)
    (hf : ∀ m ∈ f.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) (t : K → S) (w : (Σ k, ι k) → S) :
    MvPolynomial.aeval (fun q : Σ k, ι k => t q.1 * w q) f = (∏ k, t k ^ d k) * MvPolynomial.aeval w f := by
  conv_lhs => rw [MvPolynomial.as_sum f]
  conv_rhs => rw [MvPolynomial.as_sum f]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  have key : (m.prod fun q e => (t q.1 * w q) ^ e) = (∏ k, t k ^ d k) * m.prod fun q e => w q ^ e := by
    simp_rw [mul_pow]
    rw [Finsupp.prod_mul]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  rw [key]
  ring

private theorem mConeMap_eq_prod_X_pow_mul_C {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (h : MvPolynomial (Σ k, ι k) ℤ) (d : K → ℕ)
    (hh : ∀ m ∈ h.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) :
    mConeMap y h = (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) * MvPolynomial.C (MvPolynomial.aeval y h) := by
  have e : (fun p : Σ k, ι k => MvPolynomial.C (y p) * (MvPolynomial.X p.1 : MvPolynomial K Ω)) =
      fun p => (MvPolynomial.X p.1 : MvPolynomial K Ω) * MvPolynomial.C (y p) := by
    funext p
    ring
  show MvPolynomial.aeval _ h = _
  rw [e, aeval_mul_scale_of_homog h d hh (fun k => (MvPolynomial.X k : MvPolynomial K Ω))
    (fun p => MvPolynomial.C (y p))]
  congr 1
  exact MvPolynomial.aeval_algebraMap_apply (MvPolynomial K Ω) y h

theorem algebraMap_mem_blockFnField :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] [CharZero Φ]
      (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (s : M.Ω),
      zb ∈ mcPts (mCoordIdeal M.x) → RegAt M.x (mCoordIdeal zb) s → algebraMap M.Ω Φ s ∈ blockFnField y := by
  intro K _ ι _ Φ _ _ y Ψ N j M zb s hzb hreg
  obtain ⟨d, g, h, hg, hh, hQ, hgs⟩ := hreg
  obtain ⟨-, hzv⟩ := hzb
  have hxh : MvPolynomial.aeval M.x h ≠ 0 := by
    intro h0
    apply hQ
    have hker : h ∈ mCoordIdeal M.x := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap_eq_prod_X_pow_mul_C M.x h d hh, h0, map_zero, mul_zero]
    have hz := hzv h hker
    have hz' : MvPolynomial.aeval zb h = 0 := by
      rw [MvPolynomial.aeval_def, algebraMap_int_eq, ← MvPolynomial.eval_map]
      exact hz
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap_eq_prod_X_pow_mul_C zb h d hh, hz', map_zero, mul_zero]
  have hs : s = MvPolynomial.aeval M.x g / MvPolynomial.aeval M.x h := eq_div_of_mul_eq hxh hgs.symm
  rw [hs, map_div₀, ← MvPolynomial.aeval_algebraMap_apply, ← MvPolynomial.aeval_algebraMap_apply]
  have hne : ∀ k, ∃ i, (⇑(algebraMap M.Ω Φ) ∘ M.x) ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := M.x_ne k
    exact ⟨i, (map_ne_zero _).mpr hi⟩
  choose c hc using hne
  have hYy : ∀ q, (⇑(algebraMap M.Ω Φ) ∘ M.x) q = y ⟨q.1.val, q.2⟩ := fun q => (M.y_base q).symm
  generalize (⇑(algebraMap M.Ω Φ) ∘ M.x) = Y at hYy hc ⊢
  have hsc : ∀ p : MvPolynomial (Σ k, baseIdx ι M.blk k) ℤ, (∀ m ∈ p.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) →
      MvPolynomial.aeval Y p =
        (∏ k, Y ⟨k, c k⟩ ^ d k) * MvPolynomial.aeval (fun q => Y q / Y ⟨q.1, c q.1⟩) p := by
    intro p hp
    have eY : Y = fun q : Σ k, baseIdx ι M.blk k => Y ⟨q.1, c q.1⟩ * (Y q / Y ⟨q.1, c q.1⟩) := by
      funext q
      rw [mul_comm, div_mul_cancel₀ _ (hc q.1)]
    conv_lhs => rw [eY]
    exact aeval_mul_scale_of_homog p d hp (fun k => Y ⟨k, c k⟩) (fun q => Y q / Y ⟨q.1, c q.1⟩)
  have hP : (∏ k, Y ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  rw [hsc g hg, hsc h hh, mul_div_mul_left _ _ hP]
  have hw : ∀ q, Y q / Y ⟨q.1, c q.1⟩ ∈ blockFnField y := by
    intro q
    rw [hYy, hYy]
    apply IntermediateField.subset_adjoin
    exact ⟨⟨q.1.val, q.2⟩, ⟨q.1.val, c q.1⟩, rfl, rfl⟩
  have hmem : ∀ p : MvPolynomial (Σ k, baseIdx ι M.blk k) ℤ,
      MvPolynomial.aeval (fun q => Y q / Y ⟨q.1, c q.1⟩) p ∈ blockFnField y := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.aeval_C, algebraMap_int_eq, eq_intCast]
      exact intCast_mem _ a
    | add p q hp hq =>
      rw [map_add (f := _)]
      exact add_mem hp hq
    | mul_X p n hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact mul_mem hp (hw n)
  exact div_mem (hmem g) (hmem h)

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionInBlockFieldStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_function_in_block_field : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] [CharZero Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (s : M.Ω), zb ∈ mcPts (mCoordIdeal M.x) → RegAt M.x (mCoordIdeal zb) s → algebraMap M.Ω Φ s ∈ blockFnField y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField.algebraMap_mem_blockFnField | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField.algebraMap_mem_blockFnField | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField.algebraMap_mem_blockFnField <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBlockFieldEq
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

theorem x_chart_ne_of_pt (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk}
    {zb : (Σ k, baseIdx ι M.blk k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hF : M.GoodAt F (mCoordIdeal zb))
    (k : NonPluckerBlocks M.blk) : M.x ⟨k, F.c k⟩ ≠ 0 := fun h => hF.1 k (by
  have h1 : (X ⟨k, F.c k⟩ : MRing (baseIdx ι M.blk)) ∈ mCoordIdeal M.x := by
    show mConeMap M.x (X ⟨k, F.c k⟩) = 0
    rw [mConeMap, aeval_X, h, map_zero, zero_mul]
  have h2 : zb ⟨k, F.c k⟩ = 0 := by simpa using hz.2 _ h1
  show mConeMap zb (X ⟨k, F.c k⟩) = 0
  rw [mConeMap, aeval_X, h2, map_zero, zero_mul])

theorem transPt_ratio_base [CharZero Φ'] {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (k : K) (h : ∀ p, M.blk p ≠ some k) (i i₂ : ι k) :
    transPt Cv ⟨k, i⟩ / transPt Cv ⟨k, i₂⟩ ∈ blockFnField y' := by
  have e : ∀ m : ι k, transPt Cv ⟨k, m⟩ = y' ⟨(Cv.v ⟨⟨k, h⟩, m⟩).1.1, (Cv.v ⟨⟨k, h⟩, m⟩).2⟩ := fun m => by
    have h1 := transPt_base Cv ⟨⟨k, h⟩, m⟩
    rw [← Cv.x_eq, ← M'.y_base] at h1
    exact h1
  rw [e, e]
  refine IntermediateField.subset_adjoin _ _ ⟨_, _, ?_, rfl⟩
  show (Cv.v ⟨⟨k, h⟩, i⟩).1.1 = (Cv.v ⟨⟨k, h⟩, i₂⟩).1.1
  rw [Cv.block.2.2.1, Cv.block.2.2.1]

theorem transPt_ratio_step [CharZero Φ'] {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (hy : ∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) (p : Ψ × Fin N) (k : K) (hp : M.blk p = some k) (i i₂ : ι k) :
    transPt Cv ⟨k, i⟩ / transPt Cv ⟨k, i₂⟩ ∈ blockFnField y' := by
  obtain ⟨k', hk'⟩ : ∃ k', M'.blk p = some k' := by
    rcases e : M'.blk p with _ | k'
    · have h2 := (M.blk_none p).2 ((M'.blk_none p).1 e)
      rw [hp] at h2
      cases h2
    · exact ⟨k', rfl⟩
  obtain ⟨zb, hzb⟩ := GlobalTheory.T.multiprojective_points_nonempty _ _ _ M'.x M'.x_ne
  have hzv := GlobalTheory.T.flag_cover_base_point_maps_to_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb hzb
  obtain ⟨F', hF', hG'⟩ := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').2.1 zb hzb
  obtain ⟨F, hF, hG⟩ := (GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.1 _ hzv
  obtain ⟨c, hc, hcs⟩ := GlobalTheory.T.flag_cover_frames_pullback K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv F' F hF' hF
    (fun k => x_chart_ne_of_pt M' hzb hG' k) (fun k => x_chart_ne_of_pt M hzv hG k) p k k' hp hk'
  obtain ⟨c', hc'⟩ := hy k'
  have hreg : ∀ (q : Σ k, ι k) (r : Σ k, ι' k),
      algebraMap M'.Ω Φ' (coE Cv F' F p q r) ∈ blockFnField y' := fun q r =>
    GlobalTheory.T.regular_function_in_block_field K' ι' Φ' y' Ψ N j M' zb _ hzb
      (GlobalTheory.T.flag_cover_frames_at_base_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb F' F hzb hF' hF hG' hG p q r).1
  let S : ι k → Φ' := fun m =>
    ∑ m' : ι' k', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * (y' ⟨k', m'⟩ / y' ⟨k', c'⟩)
  have hS : ∀ m, S m ∈ blockFnField y' := fun m =>
    sum_mem fun m' _ => mul_mem (hreg _ _) (IntermediateField.subset_adjoin _ _ ⟨⟨k', m'⟩, ⟨k', c'⟩, rfl, rfl⟩)
  have e : ∀ m, transPt Cv ⟨k, m⟩ = (c * y' ⟨k', c'⟩) * S m := fun m => by
    rw [hcs m, mul_assoc]
    congr 1
    simp only [S]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    field_simp
  rw [e, e, mul_div_mul_left _ _ (mul_ne_zero hc hc')]
  exact div_mem (hS _) (hS _)

end

theorem blockFnField_pair_transPt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) [CharZero Φ'], (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → blockFnField y' = blockFnField (pairV (transPt Cv) y') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv _ hy
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro t ⟨p, q, h, rfl⟩
    exact IntermediateField.subset_adjoin _ _
      ⟨inrV p, inrV q, by simp only [inrV, h], rfl⟩
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro t ⟨⟨k | k, i⟩, ⟨k₂ | k₂, i₂⟩, h, rfl⟩
    · obtain rfl : k = k₂ := Sum.inl.inj h
      show transPt Cv ⟨k, i⟩ / transPt Cv ⟨k, i₂⟩ ∈ blockFnField y'
      by_cases hb : ∀ p, M.blk p ≠ some k
      · exact transPt_ratio_base Cv k hb i i₂
      · exact transPt_ratio_step Cv hy (stepOf M k hb) k (blk_stepOf M k hb) i i₂
    · cases h
    · cases h
    · obtain rfl : k = k₂ := Sum.inr.inj h
      exact IntermediateField.subset_adjoin _ _ ⟨⟨k, i⟩, ⟨k, i₂⟩, rfl, rfl⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBlockFieldEqStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_block_field_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) [CharZero Φ'], (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → blockFnField y' = blockFnField (pairV (transPt Cv) y') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.blockFnField_pair_transPt | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.blockFnField_pair_transPt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.blockFnField_pair_transPt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesLiftPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseFunctionValueAtPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseFunctionValueAtPoint
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem isValueAt_of_base : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (z : (Σ k, ι k) → ℂ) (s : M.Ω), z ∈ mcPts (mCoordIdeal y) → basePart M.blk z ∈ mcPts (mCoordIdeal M.x) → RegAt M.x (mCoordIdeal (basePart M.blk z)) s → IsValueAt y (algebraMap M.Ω Φ s) z (valAt M.x s (basePart M.blk z)) := by
  intro K _ ι _ Φ _ y Ψ N j M z s _ hb hs
  obtain ⟨v, hv⟩ := GlobalTheory.CompanionTheory.Ar.PB.ValRing.exists_isValueAt hb hs
  rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt_eq hb hv]
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  let f : (Σ k, baseIdx ι M.blk k) → (Σ k, ι k) := fun q => ⟨q.1.1, q.2⟩
  have ha : ∀ p : MRing (baseIdx ι M.blk), aeval y (rename f p) = algebraMap M.Ω Φ (aeval M.x p) := fun p => by
    have e : y ∘ f = algebraMap M.Ω Φ ∘ M.x := funext M.y_base
    rw [aeval_rename, e, aeval_algebraMap_apply]
  have hev : ∀ p : MRing (baseIdx ι M.blk), eval z (map (Int.castRingHom ℂ) (rename f p)) =
      eval (basePart M.blk z) (map (Int.castRingHom ℂ) p) := fun p => by
    rw [map_rename, eval_rename]
    rfl
  refine ⟨_, rename f g, rename f h, isMultiHomog_rename_base M.blk hg, isMultiHomog_rename_base M.blk hh, ?_, ?_, ?_, ?_⟩
  · rw [ha]
    exact (map_ne_zero _).2 hy
  · rw [ha, ha, heq, map_mul]
  · rw [hev]
    exact hz0
  · rw [hev, hev]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseFunctionValueAtPointStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_function_value_at_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (z : (Σ k, ι k) → ℂ) (s : M.Ω), z ∈ mcPts (mCoordIdeal y) → basePart M.blk z ∈ mcPts (mCoordIdeal M.x) → RegAt M.x (mCoordIdeal (basePart M.blk z)) s → IsValueAt y (algebraMap M.Ω Φ s) z (valAt M.x s (basePart M.blk z)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_of_base | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_of_base | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_of_base <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesLiftPoint
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.BStep

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem coord_ne (hz : z ∈ mcPts (mCoordIdeal x)) {q : Σ k, ι k} (hq : (X q : MRing ι) ∉ mCoordIdeal z) :
    x q ≠ 0 := fun h => hq (by
  have hm : (X q : MRing ι) ∈ mCoordIdeal x := by
    show mConeMap x (X q) = 0
    rw [mConeMap, aeval_X, h, map_zero, zero_mul]
  have h0 : z q = 0 := by simpa using hz.2 _ hm
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

theorem isValueAt_sum {α : Type} (S : Finset α) (f : α → Ω) (v : α → ℂ)
    (h : ∀ i ∈ S, IsValueAt x (f i) z (v i)) : IsValueAt x (∑ i ∈ S, f i) z (∑ i ∈ S, v i) := by
  induction S using Finset.induction_on with
  | empty => simpa using ValRing.isValueAt_zero_self x z
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ValRing.isValueAt_add (h a (Finset.mem_insert_self a S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isValueAt_valAt (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (hs : RegAt x (mCoordIdeal z) s) :
    IsValueAt x s z (valAt x s z) := by
  obtain ⟨v, hv⟩ := ValRing.exists_isValueAt hz hs
  rw [valAt_eq hz hv]
  exact hv

theorem valAt_sum_mul (hz : z ∈ mcPts (mCoordIdeal x)) {α : Type} (S : Finset α) (f g : α → Ω)
    (hf : ∀ i ∈ S, RegAt x (mCoordIdeal z) (f i)) (hg : ∀ i ∈ S, RegAt x (mCoordIdeal z) (g i)) :
    valAt x (∑ i ∈ S, f i * g i) z = ∑ i ∈ S, valAt x (f i) z * valAt x (g i) z :=
  valAt_eq hz (isValueAt_sum S _ _ fun i hi =>
    isValueAt_mul (isValueAt_valAt hz (hf i hi)) (isValueAt_valAt hz (hg i hi)))

end Values

theorem stepCols_ne {N j : ℕ} (i : Fin N) (hj : j ≤ N) : stepCols N j i ≠ ∅ := by
  intro e
  have hi := i.2
  by_cases c : (i : ℕ) + 1 ≤ j
  · have hlt : N - j < N := by omega
    have hm : (⟨N - j, hlt⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos c]
      omega
    rw [e] at hm
    simp at hm
  · have hm : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg c]
      omega
    rw [e] at hm
    simp at hm

theorem read_minor {κ : Type} [Fintype κ] {N : ℕ} (P : Finset (Fin N) → Prop)
    (A : Finset (Fin N) → κ → ℂ) (B : κ → Finset (Fin N) → ℂ)
    (hAB : ∀ I I', P I → P I' → ∑ m, A I m * B m I' = if I = I' then 1 else 0)
    (μ : Finset (Fin N) → ℂ) (hμ : ∀ I, ¬ P I → μ I = 0) (w : κ → ℂ) (a : ℂ)
    (hw : ∀ m, w m = a * ∑ I, B m I * μ I) (I' : Finset (Fin N)) (hI' : P I') :
    ∑ m, A I' m * w m = a * μ I' := by
  have e : ∑ m, A I' m * w m = a * ∑ I, (∑ m, A I' m * B m I) * μ I := by
    simp only [hw, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun m _ => by ring
  rw [e, Finset.sum_eq_single I']
  · rw [hAB I' I' hI' hI', if_pos rfl, one_mul]
  · intro I _ hne
    by_cases hI : P I
    · rw [hAB I' I hI' hI, if_neg hne.symm, zero_mul]
    · rw [hμ I hI, mul_zero]
  · simp

theorem move_minor {κ : Type} [Fintype κ] {N : ℕ} (P : Finset (Fin N) → Prop)
    (S : Finset (Finset (Fin N))) (hS : ∀ I, I ∈ S ↔ P I) (A : Finset (Fin N) → κ → ℂ)
    (D : Finset (Fin N) → ℂ) (Tm : Finset (Fin N) → Finset (Fin N) → ℂ)
    (μ : Finset (Fin N) → ℂ) (hμ : ∀ I, ¬ P I → μ I = 0) (w : κ → ℂ) (a : ℂ)
    (hA : ∀ I', P I' → ∑ m, A I' m * w m = a * μ I') :
    ∑ m, (∑ I, ∑ I' ∈ S, D I * Tm I I' * A I' m) * w m = a * ∑ I, D I * ∑ I', Tm I I' * μ I' := by
  have e : ∑ m, (∑ I, ∑ I' ∈ S, D I * Tm I I' * A I' m) * w m =
      ∑ I, ∑ I' ∈ S, D I * Tm I I' * ∑ m, A I' m * w m := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => by ring
  rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ S) fun I' _ h => by
    rw [hμ I' fun hp => h ((hS I').2 hp), mul_zero], Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun I' h => by rw [hA I' ((hS I').1 h)]; ring

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z₁ : (Σ k, ι' k) → ℂ) (z₀ : (Σ k, ι k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) (k : K), z₁ ∈ mcPts (mCoordIdeal y') → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z₁ ∘ Cv.v)) → M'.IsFlagOf F' z₁ h → M.IsFlagOf F z₀ (fun τ => Cv.trans F' F (basePart M'.blk z₁) τ * h τ) → SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) → M.blk p = some k → ∃ (e : Φ') (s : ι k → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ m, transPt Cv ⟨k, m⟩ = e * s m ∧ IsValueAt y' (s m) z₁ (t * z₀ ⟨k, m⟩) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z₁ z₀ F' F h p k hz₁ hF' hF hG' hG hfl' hfl horb hp
  set zb := basePart M'.blk z₁ with hzbdef
  have hzb : zb ∈ mcPts (mCoordIdeal M'.x) := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').1 z₁ hz₁
  have hzv := GlobalTheory.T.flag_cover_base_point_maps_to_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb hzb
  have hstep : IsProperStep N j p.2 := by
    by_contra hn
    rw [(M.blk_none p).2 hn] at hp
    exact absurd hp (by simp)
  obtain ⟨k', hk'⟩ : ∃ k', M'.blk p = some k' :=
    Option.ne_none_iff_exists'.1 fun e => (M'.blk_none p).1 e hstep
  obtain ⟨c', hc'⟩ := hz₁.1 k'
  obtain ⟨hy0, hratio⟩ := GlobalTheory.T.coordinate_ratio_value_at_point K' ι' Φ' y' z₁ k' c' hz₁ hc'
  have ch' : ∀ k, M'.x ⟨k, F'.c k⟩ ≠ 0 := fun k => coord_ne hzb (hG'.1 k)
  have ch : ∀ k, M.x ⟨k, F.c k⟩ ≠ 0 := fun k => coord_ne hzv (hG.1 k)
  obtain ⟨c, hc0, htr⟩ :=
    GlobalTheory.T.flag_cover_frames_pullback K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv F' F hF' hF ch' ch p k k' hp hk'
  obtain ⟨a', ha', hz1⟩ := hfl'.2.2 p k' hk'
  obtain ⟨a, ha, hz0⟩ := hfl.2.2 p k hp
  have hE := fun m m' =>
    GlobalTheory.T.flag_cover_frames_at_base_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb F' F hzb hF' hF hG' hG p ⟨k, m⟩ ⟨k', m'⟩
  have hmin := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have hne : stepCols N j p.2 ≠ ∅ := stepCols_ne p.2 M.j_le
  obtain ⟨cc, hcc, horbE⟩ := horb
  have hval : ∀ s, valAt M.x s (basePart M.blk z₀) = valAt M.x s (zb ∘ Cv.v) := fun s => by
    rw [horbE]
    exact ((StepW.TorusAct.main _ _ _ M.x (zb ∘ Cv.v) cc hcc).2 hzv).2 s
  have hμ : ∀ I, ¬ IsStepRows N j p.2 I → minorIJ (h p.1) I (stepCols N j p.2) = 0 := fun I hI =>
    (hmin.2.1 (h p.1) I (hfl'.2.1 p.1).1 hI).resolve_right hne
  have hAB : ∀ I I', IsStepRows N j p.2 I → IsStepRows N j p.2 I' →
      ∑ m, valAt M'.x (F'.u' I ⟨k', m⟩) zb * valAt M'.x (F'.u ⟨k', m⟩ I') zb =
        if I = I' then 1 else 0 := fun I I' hI hI' => by
    rw [← valAt_sum_mul hzb Finset.univ _ _ (fun m _ => (hG'.2.1 ⟨k', m⟩ I).2)
      (fun m _ => (hG'.2.1 ⟨k', m⟩ I').1), hF'.2.2.1 p k' hk' I I' hI hI']
    have h3 := ValRing.regAt_valAt_ring _ _ _ M'.x zb hzb
    split_ifs
    · exact h3.2.2.2.1
    · exact h3.2.2.1
  have hread := read_minor (IsStepRows N j p.2) _ _ hAB _ hμ (fun m => z₁ ⟨k', m⟩) a' hz1
  have key : ∀ m, ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * z₁ ⟨k', m'⟩ =
      a' * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (zb ∘ Cv.v) *
        minorIJ (Cv.trans F' F zb p.1 * h p.1) I (stepCols N j p.2) := fun m => by
    simp only [fun m' => (hE m m').2, hmin.1]
    exact move_minor (IsStepRows N j p.2) _ (fun I => by simp) _ _ _ _ hμ _ a' hread
  refine ⟨c * y' ⟨k', c'⟩, fun m => ∑ m', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) *
    (y' ⟨k', m'⟩ / y' ⟨k', c'⟩), a' / (a * z₁ ⟨k', c'⟩), mul_ne_zero hc0 hy0,
    div_ne_zero ha' (mul_ne_zero ha hc'), fun m => ⟨?_, ?_⟩⟩
  · show transPt Cv ⟨k, m⟩ = c * y' ⟨k', c'⟩ * ∑ m', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) *
      (y' ⟨k', m'⟩ / y' ⟨k', c'⟩)
    rw [htr m, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    field_simp
  · have hv := isValueAt_sum Finset.univ
      (fun m' => algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * (y' ⟨k', m'⟩ / y' ⟨k', c'⟩))
      (fun m' => valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩))
      fun m' _ => isValueAt_mul (GlobalTheory.T.base_function_value_at_point K' ι' Φ' y' Ψ N j M' z₁ _ hz₁ hzb (hE m m').1) (hratio m')
    have e : ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩) =
        a' / (a * z₁ ⟨k', c'⟩) * z₀ ⟨k, m⟩ := by
      have e1 : ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩) =
          (z₁ ⟨k', c'⟩)⁻¹ * ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * z₁ ⟨k', m'⟩ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m' _ => by ring
      rw [e1, key m, hz0 m]
      simp only [hval]
      field_simp
    rw [← e]
    exact hv

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.BStep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesLiftPointStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph GlobalTheory.CompanionTheory.Ar.PB.CovGraph.BStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_frames_lift_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z₁ : (Σ k, ι' k) → ℂ) (z₀ : (Σ k, ι k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) (k : K), z₁ ∈ mcPts (mCoordIdeal y') → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z₁ ∘ Cv.v)) → M'.IsFlagOf F' z₁ h → M.IsFlagOf F z₀ (fun τ => Cv.trans F' F (basePart M'.blk z₁) τ * h τ) → SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) → M.blk p = some k → ∃ (e : Φ') (s : ι k → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ m, transPt Cv ⟨k, m⟩ = e * s m ∧ IsValueAt y' (s m) z₁ (t * z₀ ⟨k, m⟩) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z₁ z₀ F' F h p k hz₁ hF' hF hG' hG hfl' hfl horb hp
  set zb := basePart M'.blk z₁ with hzbdef
  have hzb : zb ∈ mcPts (mCoordIdeal M'.x) := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').1 z₁ hz₁
  have hzv := GlobalTheory.T.flag_cover_base_point_maps_to_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb hzb
  have hstep : IsProperStep N j p.2 := by
    by_contra hn
    rw [(M.blk_none p).2 hn] at hp
    exact absurd hp (by simp)
  obtain ⟨k', hk'⟩ : ∃ k', M'.blk p = some k' :=
    Option.ne_none_iff_exists'.1 fun e => (M'.blk_none p).1 e hstep
  obtain ⟨c', hc'⟩ := hz₁.1 k'
  obtain ⟨hy0, hratio⟩ := GlobalTheory.T.coordinate_ratio_value_at_point K' ι' Φ' y' z₁ k' c' hz₁ hc'
  have ch' : ∀ k, M'.x ⟨k, F'.c k⟩ ≠ 0 := fun k => coord_ne hzb (hG'.1 k)
  have ch : ∀ k, M.x ⟨k, F.c k⟩ ≠ 0 := fun k => coord_ne hzv (hG.1 k)
  obtain ⟨c, hc0, htr⟩ :=
    GlobalTheory.T.flag_cover_frames_pullback K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv F' F hF' hF ch' ch p k k' hp hk'
  obtain ⟨a', ha', hz1⟩ := hfl'.2.2 p k' hk'
  obtain ⟨a, ha, hz0⟩ := hfl.2.2 p k hp
  have hcoeff (q : Σ k, ι k) (r : Σ k, ι' k) :
      RegAt M'.x (mCoordIdeal zb) (coE Cv F' F p q r) ∧
        valAt M'.x (coE Cv F' F p q r) zb =
          ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2),
            valAt M.x (F.u q I) (zb ∘ Cv.v) * minorIJ (Cv.trans F' F zb p.1) I I' *
              valAt M'.x (F'.u' I' r) zb := by
    have hT : ∀ a b, RegAt M'.x (mCoordIdeal zb) (trMat Cv F' F p.1 a b) := fun a b =>
      (Cv.agree zb hzb F' F hF' hF hG' hG p.1 a b).1
    have hminor := CovMap.LocImg.reg_minor hzb hT
    have hxv : M'.x ∘ Cv.v = Cv.φ ∘ M.x := funext Cv.x_eq
    have hu (I : Finset (Fin N)) :
        RegAt M'.x (mCoordIdeal zb) (Cv.φ (F.u q I)) ∧
          valAt M'.x (Cv.φ (F.u q I)) zb = valAt M.x (F.u q I) (zb ∘ Cv.v) := by
      obtain ⟨d, g, h, hg, hh, hn, he⟩ := (hG.2.1 q I).1
      have hg' := RegPhi.isMultiHomog_rename_block Cv.block hg
      have hh' := RegPhi.isMultiHomog_rename_block Cv.block hh
      have hn' := RegPhi.rename_notMem Cv.block hn
      have hae (f : MRing (baseIdx ι M.blk)) :
          aeval M'.x (rename Cv.v f) = Cv.φ (aeval M.x f) := by
        rw [aeval_rename, hxv, RegPhi.aeval_comp_ringHom]
      have he' : aeval M'.x (rename Cv.v g) = Cv.φ (F.u q I) * aeval M'.x (rename Cv.v h) := by
        rw [hae, hae, he, map_mul]
      refine ⟨⟨_, _, _, hg', hh', hn', he'⟩, ?_⟩
      let value := eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) g) /
        eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h)
      have hv : IsValueAt M.x (F.u q I) (zb ∘ Cv.v) value :=
        ⟨d, g, h, hg, hh, ValRing.aeval_ne_zero_of_notMem hzv hh hn, he,
          ValRing.eval_ne_zero_of_notMem hh hn, rfl⟩
      have hv' : IsValueAt M'.x (Cv.φ (F.u q I)) zb value := by
        refine ⟨_, _, _, hg', hh', ValRing.aeval_ne_zero_of_notMem hzb hh' hn', he',
          ValRing.eval_ne_zero_of_notMem hh' hn', ?_⟩
        rw [RegPhi.eval_rename_block, RegPhi.eval_rename_block]
      exact (valAt_eq hzb hv').trans (valAt_eq hzv hv).symm
    have hterm (I I' : Finset (Fin N)) :
        RegAt M'.x (mCoordIdeal zb) (Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r) ∧
          valAt M'.x (Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r) zb =
            valAt M.x (F.u q I) (zb ∘ Cv.v) * minorIJ (Cv.trans F' F zb p.1) I I' *
              valAt M'.x (F'.u' I' r) zb := by
      obtain ⟨hreg, hval⟩ := CovMap.LocImg.reg_mul hzb (hu I).1 (hminor I I').1
      obtain ⟨hreg', hval'⟩ := CovMap.LocImg.reg_mul hzb hreg (hG'.2.1 r I').2
      refine ⟨hreg', hval'.trans ?_⟩
      rw [hval, (hu I).2, (hminor I I').2]
      rfl
    have hin (I : Finset (Fin N)) := CovMap.LocImg.reg_sum hzb
      (Finset.univ.filter (IsStepRows N j p.2)) _ (fun I' _ => (hterm I I').1)
    have hout := CovMap.LocImg.reg_sum hzb Finset.univ _ (fun I _ => (hin I).1)
    refine ⟨hout.1, hout.2.trans (Finset.sum_congr rfl fun I _ => ?_)⟩
    rw [(hin I).2]
    exact Finset.sum_congr rfl fun I' _ => (hterm I I').2
  have hE (m : ι k) (m' : ι' k') := hcoeff ⟨k, m⟩ ⟨k', m'⟩
  have hmin := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have hne : stepCols N j p.2 ≠ ∅ := stepCols_ne p.2 M.j_le
  obtain ⟨cc, hcc, horbE⟩ := horb
  have hval : ∀ s, valAt M.x s (basePart M.blk z₀) = valAt M.x s (zb ∘ Cv.v) := fun s => by
    rw [horbE]
    exact ((StepW.TorusAct.main _ _ _ M.x (zb ∘ Cv.v) cc hcc).2 hzv).2 s
  have hμ : ∀ I, ¬ IsStepRows N j p.2 I → minorIJ (h p.1) I (stepCols N j p.2) = 0 := fun I hI =>
    (hmin.2.1 (h p.1) I (hfl'.2.1 p.1).1 hI).resolve_right hne
  have isValueAt_valAt (s : M'.Ω) (hs : RegAt M'.x (mCoordIdeal zb) s) :
      IsValueAt M'.x s zb (valAt M'.x s zb) := by
    obtain ⟨v, hv⟩ := ValRing.exists_isValueAt hzb hs
    rwa [valAt_eq hzb hv]
  have valAt_sum_mul {α : Type} (S : Finset α) (f g : α → M'.Ω)
      (hf : ∀ i ∈ S, RegAt M'.x (mCoordIdeal zb) (f i))
      (hg : ∀ i ∈ S, RegAt M'.x (mCoordIdeal zb) (g i)) :
      valAt M'.x (∑ i ∈ S, f i * g i) zb = ∑ i ∈ S, valAt M'.x (f i) zb * valAt M'.x (g i) zb :=
    valAt_eq hzb (isValueAt_sum S _ _ fun i hi =>
      isValueAt_mul (isValueAt_valAt (f i) (hf i hi)) (isValueAt_valAt (g i) (hg i hi)))
  have hAB : ∀ I I', IsStepRows N j p.2 I → IsStepRows N j p.2 I' →
      ∑ m, valAt M'.x (F'.u' I ⟨k', m⟩) zb * valAt M'.x (F'.u ⟨k', m⟩ I') zb =
        if I = I' then 1 else 0 := fun I I' hI hI' => by
    rw [← valAt_sum_mul Finset.univ _ _ (fun m _ => (hG'.2.1 ⟨k', m⟩ I).2)
      (fun m _ => (hG'.2.1 ⟨k', m⟩ I').1), hF'.2.2.1 p k' hk' I I' hI hI']
    have h3 := ValRing.regAt_valAt_ring _ _ _ M'.x zb hzb
    split_ifs
    · exact h3.2.2.2.1
    · exact h3.2.2.1
  have hread := read_minor (IsStepRows N j p.2) _ _ hAB _ hμ (fun m => z₁ ⟨k', m⟩) a' hz1
  have key : ∀ m, ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * z₁ ⟨k', m'⟩ =
      a' * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (zb ∘ Cv.v) *
        minorIJ (Cv.trans F' F zb p.1 * h p.1) I (stepCols N j p.2) := fun m => by
    simp only [fun m' => (hE m m').2, hmin.1]
    exact move_minor (IsStepRows N j p.2) _ (fun I => by simp) _ _ _ _ hμ _ a' hread
  have baseValue (s : M'.Ω) (hs : RegAt M'.x (mCoordIdeal zb) s) :
      IsValueAt y' (algebraMap M'.Ω Φ' s) z₁ (valAt M'.x s zb) := by
    obtain ⟨v, hv⟩ := GlobalTheory.CompanionTheory.Ar.PB.ValRing.exists_isValueAt hzb hs
    rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt_eq hzb hv]
    obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
    let f : (Σ k, baseIdx ι' M'.blk k) → (Σ k, ι' k) := fun q => ⟨q.1.1, q.2⟩
    have ha : ∀ p : MRing (baseIdx ι' M'.blk), aeval y' (rename f p) = algebraMap M'.Ω Φ' (aeval M'.x p) := fun p => by
      have e : y' ∘ f = algebraMap M'.Ω Φ' ∘ M'.x := funext M'.y_base
      rw [aeval_rename, e, aeval_algebraMap_apply]
    have hev : ∀ p : MRing (baseIdx ι' M'.blk), eval z₁ (map (Int.castRingHom ℂ) (rename f p)) =
        eval (basePart M'.blk z₁) (map (Int.castRingHom ℂ) p) := fun p => by
      rw [map_rename, eval_rename]
      rfl
    refine ⟨_, rename f g, rename f h, isMultiHomog_rename_base M'.blk hg, isMultiHomog_rename_base M'.blk hh, ?_, ?_, ?_, ?_⟩
    · rw [ha]
      exact (map_ne_zero _).2 hy
    · rw [ha, ha, heq, map_mul]
    · rw [hev]
      exact hz0
    · rw [hev, hev]
  refine ⟨c * y' ⟨k', c'⟩, fun m => ∑ m', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) *
    (y' ⟨k', m'⟩ / y' ⟨k', c'⟩), a' / (a * z₁ ⟨k', c'⟩), mul_ne_zero hc0 hy0,
    div_ne_zero ha' (mul_ne_zero ha hc'), fun m => ⟨?_, ?_⟩⟩
  · show transPt Cv ⟨k, m⟩ = c * y' ⟨k', c'⟩ * ∑ m', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) *
      (y' ⟨k', m'⟩ / y' ⟨k', c'⟩)
    rw [htr m, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    field_simp
  · have hv := isValueAt_sum Finset.univ
      (fun m' => algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * (y' ⟨k', m'⟩ / y' ⟨k', c'⟩))
      (fun m' => valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩))
      fun m' _ => isValueAt_mul (baseValue _ (hE m m').1) (hratio m')
    have e : ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩) =
        a' / (a * z₁ ⟨k', c'⟩) * z₀ ⟨k, m⟩ := by
      have e1 : ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩) =
          (z₁ ⟨k', c'⟩)⁻¹ * ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * z₁ ⟨k', m'⟩ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m' _ => by ring
      rw [e1, key m, hz0 m]
      simp only [hval]
      field_simp
    rw [← e]
    exact hv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBaseBlockValue
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBaseBlockValue
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem transPt_block_base : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z₁ : (Σ k, ι' k) → ℂ) (z₀ : (Σ k, ι k) → ℂ) (kb : NonPluckerBlocks M.blk), z₁ ∈ mcPts (mCoordIdeal y') → SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) → ∃ (e : Φ') (s : ι kb.1 → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ i, transPt Cv ⟨kb.1, i⟩ = e * s i ∧ IsValueAt y' (s i) z₁ (t * z₀ ⟨kb.1, i⟩) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z₁ z₀ kb hz hO
  obtain ⟨c₀, hc₀, e₀⟩ := hO
  obtain ⟨c, hc⟩ := hz.1 (Cv.κ kb).1
  obtain ⟨hy, hv⟩ := GlobalTheory.T.coordinate_ratio_value_at_point K' ι' Φ' y' z₁ (Cv.κ kb).1 c hz hc
  have hw : ∀ i : ι kb.1, ∃ m : ι' (Cv.κ kb).1, Cv.v ⟨kb, i⟩ = ⟨Cv.κ kb, m⟩ := fun i => by
    have h1 := Cv.block.2.2.1 ⟨kb, i⟩
    rcases hq : Cv.v ⟨kb, i⟩ with ⟨k, m⟩
    rw [hq] at h1
    obtain rfl : k = Cv.κ kb := h1
    exact ⟨m, rfl⟩
  choose w hw using hw
  refine ⟨y' ⟨(Cv.κ kb).1, c⟩, fun i => y' ⟨(Cv.κ kb).1, w i⟩ / y' ⟨(Cv.κ kb).1, c⟩,
    (c₀ kb * z₁ ⟨(Cv.κ kb).1, c⟩)⁻¹, hy, inv_ne_zero (mul_ne_zero (hc₀ kb) hc), fun i => ⟨?_, ?_⟩⟩
  · rw [mul_div_cancel₀ _ hy]
    have h1 := transPt_base Cv (⟨kb, i⟩ : Σ k, baseIdx ι M.blk k)
    rw [← Cv.x_eq, hw i, ← M'.y_base] at h1
    exact h1
  · have h2 : z₀ ⟨kb.1, i⟩ = c₀ kb * z₁ ⟨(Cv.κ kb).1, w i⟩ := by
      have h3 := congrFun e₀ (⟨kb, i⟩ : Σ k, baseIdx ι M.blk k)
      simp only [Function.comp, hw i] at h3
      exact h3
    have h4 : (c₀ kb * z₁ ⟨(Cv.κ kb).1, c⟩)⁻¹ * z₀ ⟨kb.1, i⟩ =
        (z₁ ⟨(Cv.κ kb).1, c⟩)⁻¹ * z₁ ⟨(Cv.κ kb).1, w i⟩ := by
      rw [h2]
      have := hc₀ kb
      field_simp
    rw [h4]
    exact hv (w i)

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBaseBlockValueStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_base_block_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z₁ : (Σ k, ι' k) → ℂ) (z₀ : (Σ k, ι k) → ℂ) (kb : NonPluckerBlocks M.blk), z₁ ∈ mcPts (mCoordIdeal y') → SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) → ∃ (e : Φ') (s : ι kb.1 → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ i, transPt Cv ⟨kb.1, i⟩ = e * s i ∧ IsValueAt y' (s i) z₁ (t * z₀ ⟨kb.1, i⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.transPt_block_base | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.transPt_block_base | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.transPt_block_base <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ScaledCoordinatesValueAtPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ScaledCoordinatesValueAtPoint
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec

theorem isValueAt_aeval {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]
    {y' : (Σ k, ι' k) → Ω} {z : (Σ k, ι' k) → ℂ} {σ : Type} {s : σ → Ω} {w : σ → ℂ}
    (hv : ∀ q, IsValueAt y' (s q) z (w q)) (f : MvPolynomial σ ℤ) :
    IsValueAt y' (aeval s f) z (eval w (map (Int.castRingHom ℂ) f)) := by
  induction f using MvPolynomial.induction_on with
  | C n => simpa using GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_intCast y' z n
  | add p q hp hq => simpa using GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_add hp hq
  | mul_X p i hp => simpa using GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_mul hp (hv i)

theorem mem_mcPts_of_specialise : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] (a : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (z : (Σ k, ι' k) → ℂ) (zt : (Σ k, ι k) → ℂ) (e : K → Ω) (s : (Σ k, ι k) → Ω) (t : K → ℂ), z ∈ mcPts (mCoordIdeal y') → (∀ k, ∃ i, zt ⟨k, i⟩ ≠ 0) → (∀ k, e k ≠ 0) → (∀ k, t k ≠ 0) → (∀ q, a q = e q.1 * s q) → (∀ q, IsValueAt y' (s q) z (t q.1 * zt q)) → zt ∈ mcPts (mCoordIdeal a) := by
  intro K _ ι _ K' _ ι' _ Ω _ a y' z zt e s t hz hzt he ht has hv
  refine ⟨hzt, fun f hf => ?_⟩
  obtain ⟨T, hT, hE⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal a
  rw [hE] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨d, hd⟩ := hT g hg
    have h0 : aeval a g = 0 :=
      (GlobalTheory.CompanionTheory.Ar.PB.form_mem_mCoordIdeal_iff a hd).1 (by rw [hE]; exact Ideal.subset_span hg)
    have ha : a = fun p => e p.1 * s p := funext has
    have h1 : aeval s g = 0 := by
      have h := GroundTheory.Heights₂.Heights.Inter.ChartNormPts.aeval_smul_homog g d hd e s
      rw [← ha, h0] at h
      have hne : (∏ k, e k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (he k)
      exact (mul_eq_zero.1 h.symm).resolve_left hne
    have hval := isValueAt_aeval (w := fun q => t q.1 * zt q) hv g
    rw [h1] at hval
    have h2 := GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_zero hz hval
    rw [ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_homog g d hd t zt] at h2
    have hne : (∏ k, t k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k)
    exact (mul_eq_zero.1 h2).resolve_left hne
  | zero => simp
  | add x y _ _ hx hy => simp [map_add (f := _), hx, hy]
  | smul r x _ hx => simp [smul_eq_mul, map_mul, hx]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ScaledCoordinatesValueAtPointStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_coordinates_value_at_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] (a : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (z : (Σ k, ι' k) → ℂ) (zt : (Σ k, ι k) → ℂ) (e : K → Ω) (s : (Σ k, ι k) → Ω) (t : K → ℂ), z ∈ mcPts (mCoordIdeal y') → (∀ k, ∃ i, zt ⟨k, i⟩ ≠ 0) → (∀ k, e k ≠ 0) → (∀ k, t k ≠ 0) → (∀ q, a q = e q.1 * s q) → (∀ q, IsValueAt y' (s q) z (t q.1 * zt q)) → zt ∈ mcPts (mCoordIdeal a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec.mem_mcPts_of_specialise | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec.mem_mcPts_of_specialise | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec.mem_mcPts_of_specialise <;> assumption)
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

section Pair

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K' : Type} [Fintype K']
  {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]

theorem mConeMap_pair_inl (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) (g : MRing ι) :
    mConeMap (pairV a b) (rename inlV g) = rename Sum.inl (mConeMap a g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, inlV, pairV]

theorem mConeMap_pair_inr (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) (g : MRing ι') :
    mConeMap (pairV a b) (rename inrV g) = rename Sum.inr (mConeMap b g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, inrV, pairV]

theorem imageZ_inl (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) :
    imageZ inlV (mCoordIdeal (pairV a b)) = mCoordIdeal a := by
  ext f
  show mConeMap (pairV a b) (rename inlV f) = 0 ↔ mConeMap a f = 0
  rw [mConeMap_pair_inl]
  exact (rename_injective _ Sum.inl_injective).eq_iff' (map_zero _)

theorem imageZ_inr (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) :
    imageZ inrV (mCoordIdeal (pairV a b)) = mCoordIdeal b := by
  ext f
  show mConeMap (pairV a b) (rename inrV f) = 0 ↔ mConeMap b f = 0
  rw [mConeMap_pair_inr]
  exact (rename_injective _ Sum.inr_injective).eq_iff' (map_zero _)

end Pair

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
