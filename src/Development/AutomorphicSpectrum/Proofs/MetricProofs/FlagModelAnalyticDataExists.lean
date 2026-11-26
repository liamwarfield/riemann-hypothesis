module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularization
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BoundedPshCorrectionLocallySmooth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroEqIffUnitary
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBundleMetricLine
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothFunctionAsDegreeZeroMetric
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalNeZeroOfNotMem

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsSmoothHermPullHerm
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.FA.StepLine

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

theorem pullDeg_zero {K K' : Type} (κ : K → K') : pullDeg κ (0 : K → ℤ) = 0 := by
  funext k
  by_cases h : ∃ a, κ a = k
  · simp [pullDeg, Function.extend_def, h]
  · simp [pullDeg, Function.extend_def, h]

theorem isSmoothHerm_pullHerm {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
    [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) {B : HermLine ι} (hB : IsSmoothHerm B) : IsSmoothHerm (pullHerm hv B) := by
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k', ι' k') → ℂ => fun q => z (v q)) :=
    contDiff_pi.2 fun q => contDiff_apply ℝ (fun _ => ℂ) (v q)
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B.h ∘ fun z : (Σ k', ι' k') → ℂ => fun q => z (v q))
    {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  refine ContDiffOn.comp hB hlin.contDiffOn ?_
  intro z hz k
  obtain ⟨i', hi'⟩ := hz (κ k)
  obtain ⟨q, hq⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : q.1 = k := hv.1 (by rw [← hv.2.2.1 q, hq])
  obtain ⟨k₀, m⟩ := q
  simp only at h2
  subst h2
  exact ⟨m, by simpa [hq] using hi'⟩

theorem exists_stepLine : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (p : Ψ × Fin N)
    (B : HermLine (stepIdx M p)), B.a = 0 → ∃ A : HermLine ι, A.a = M.dy p ∧ M.OnStep p A ∧
      (IsSmoothHerm B → IsSmoothHerm A) ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
        Real.log (A.h z) = Real.log ((fsHerm ι (M.dy p)).h z) + Real.log (B.h (z ∘ stepV M p)) := by
  intro K _ ι _ Φ _ y Ψ N j M p B hB
  have hdy : ∀ k, M.dy p k ≠ 0 → k ∈ Set.range (Subtype.val : PartialFlagBlocks M p → K) := by
    intro k hk
    by_cases h : ∀ p', M.blk p' ≠ some k
    · exact ⟨⟨k, Or.inl h⟩, rfl⟩
    · by_cases h' : M.blk p = some k
      · exact ⟨⟨k, Or.inr h'⟩, rfl⟩
      · exact absurd (show M.dy p k = 0 by unfold FlagModel.dy; rw [dite_eq_right h, if_neg h']) hk
  refine ⟨(fsHerm ι (M.dy p)).tensor (pullHerm (isBlockMap_stepV M p) B), ?_, ?_, ?_, ?_⟩
  · show M.dy p + pullDeg _ B.a = M.dy p
    rw [hB, pullDeg_zero, add_zero]
  · intro z z' hb hs
    have hc : z ∘ stepV M p = z' ∘ stepV M p := by
      funext ⟨⟨k, hk⟩, m⟩
      rcases hk with h | h
      · exact congrFun hb ⟨⟨k, h⟩, m⟩
      · exact hs k h m
    show (fsHerm ι (M.dy p)).h z * B.h (z ∘ stepV M p) = (fsHerm ι (M.dy p)).h z' * B.h (z' ∘ stepV M p)
    rw [StepW.fsHerm_h_blockMap K ι (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) (M.dy p) z
        (isBlockMap_stepV M p) hdy,
      StepW.fsHerm_h_blockMap K ι (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) (M.dy p) z'
        (isBlockMap_stepV M p) hdy, hc]
  · intro hS
    exact isSmoothHerm_tensor (FlagHeightMultilinear.isSmoothHerm_fsHerm _)
      (isSmoothHerm_pullHerm (isBlockMap_stepV M p) hS)
  · intro z hz
    have h1 := (fsHerm ι (M.dy p)).pos z hz
    have h2 := (pullHerm (isBlockMap_stepV M p) B).pos z hz
    exact Real.log_mul h1.ne' h2.ne'

end GlobalTheory.CompanionTheory.Ar.PB.FA.StepLine
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.NotMemMcPtsTop
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA.StepMap

theorem orbit_symm {K : Type} {ι : K → Type} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext q
  show z' q = (c q.1)⁻¹ * (c q.1 * z' q)
  rw [← mul_assoc, inv_mul_cancel₀ (hc q.1), one_mul]

theorem orbit_trans {K : Type} {ι : K → Type} {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z')
    (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext q
  show c q.1 * (c' q.1 * z'' q) = c q.1 * c' q.1 * z'' q
  rw [mul_assoc]

theorem not_mem_mcPts_top {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro hz
  have h1 := (show (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧
    ∀ f ∈ (⊤ : Ideal (MRing ι)), eval z (map (Int.castRingHom ℂ) f) = 0 from hz).2 1 Submodule.mem_top
  simp at h1

theorem factor : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (n e e' : ℕ)
    (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (R : AnLogRes (mCoordIdeal y) ⊤ e)
    (Rp : AnLogRes (mCoordIdeal (y ∘ stepV M p)) ⊤ e') (pr : R.X → Rb.X) (prp : Rp.X → Rb.X) (h : R.X → Rp.X),
    (∀ x, SameOrbit (basePart M.blk (R.lift x x)) (Rb.lift (pr x) (pr x))) →
    (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ stepV M p = Rp.lift x x ∧
      SameOrbit (basePart M.blk z) (Rb.lift (prp x) (prp x))) →
    (∀ x, SameOrbit (Rp.lift (h x) (h x)) (R.lift x x ∘ stepV M p)) →
    (∀ x, prp (h x) = pr x) ∧ ∀ x x', pr x = pr x' →
      (∀ k, M.blk p = some k → ∃ a : ℂ, ∀ m : ι k, R.lift x x ⟨k, m⟩ = a * R.lift x' x' ⟨k, m⟩) → h x = h x' := by
  intro K _ ι _ Φ _ y Ψ N j M p n e e' Rb R Rp pr prp hh H1 H2 H3
  have hnz : ∀ x k, ∃ i, R.lift x x ⟨k, i⟩ ≠ 0 := fun x => (R.mem x x (R.mem_U x)).1
  have hb : ∀ z w : (Σ k, ι k) → ℂ, SameOrbit (z ∘ stepV M p) (w ∘ stepV M p) →
      SameOrbit (basePart M.blk z) (basePart M.blk w) := by
    rintro z w ⟨c, hc, hzw⟩
    exact ⟨fun k => c ⟨k.1, Or.inl k.2⟩, fun k => hc _,
      funext fun q => congrFun hzw ⟨⟨q.1.1, Or.inl q.1.2⟩, q.2⟩⟩
  refine ⟨fun x => ?_, fun x x' hpr hsc => ?_⟩
  · obtain ⟨z, -, hz1, hz2⟩ := H2 (hh x)
    have o1 : SameOrbit (z ∘ stepV M p) (R.lift x x ∘ stepV M p) := by
      rw [hz1]
      exact H3 x
    exact Rb.inj _ _ (not_mem_mcPts_top _)
      (orbit_trans (orbit_trans (orbit_symm hz2) (hb _ _ o1)) (H1 x))
  · apply Rp.inj _ _ (not_mem_mcPts_top _)
    refine orbit_trans (H3 x) (orbit_trans ?_ (orbit_symm (H3 x')))
    have h1' := H1 x'
    rw [← hpr] at h1'
    obtain ⟨cb, hcb, hbeq⟩ := orbit_trans (H1 x) (orbit_symm h1')
    refine ⟨fun k => if hk : (∀ p', M.blk p' ≠ some k.1) then cb ⟨k.1, hk⟩
      else (hsc k.1 (k.2.resolve_left hk)).choose, fun k => ?_, ?_⟩
    · dsimp only
      split_ifs with hk
      · exact hcb _
      · intro h0
        obtain ⟨i, hi⟩ := hnz x k.1
        apply hi
        rw [(hsc k.1 (k.2.resolve_left hk)).choose_spec i, h0, zero_mul]
    · funext q
      show R.lift x x ⟨q.1.1, q.2⟩ = _ * R.lift x' x' ⟨q.1.1, q.2⟩
      dsimp only
      split_ifs with hk
      · exact congrFun hbeq ⟨⟨q.1.1, hk⟩, q.2⟩
      · exact (hsc q.1.1 (q.1.2.resolve_left hk)).choose_spec q.2

end GlobalTheory.CompanionTheory.Ar.PB.FA.StepMap
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightDescendsOfSameOrbit
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA

private theorem grading_map_coeff_eq_monomial {K σ : Type} (s : σ → K)
    (φ : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial K (MvPolynomial σ ℤ))
    (hφ : ∀ q, φ (MvPolynomial.X q) = MvPolynomial.C (MvPolynomial.X q) * MvPolynomial.X (s q))
    (g : MvPolynomial σ ℤ) : ∀ a : K →₀ ℕ,
    φ ((φ g).coeff a) = MvPolynomial.monomial a ((φ g).coeff a) := by
  classical
  induction g using MvPolynomial.induction_on
  · rename_i r
    intro a
    have h1 : φ (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
      simpa [MvPolynomial.algebraMap_apply] using φ.commutes r
    rw [h1, MvPolynomial.coeff_C]
    split_ifs with h
    · subst h
      rw [h1, MvPolynomial.C_apply]
    · simp
  · rename_i f1 f2 hf hg
    intro a
    simp only [map_add (f := _), MvPolynomial.coeff_add, hf, hg]
  · rename_i f n hf
    intro a
    rw [map_mul φ f (MvPolynomial.X n), hφ, mul_left_comm, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_mul_X']
    split_ifs with h
    · have he : Finsupp.single (s n) 1 ≤ a := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp h)
      have hX : (MvPolynomial.X (s n) : MvPolynomial K (MvPolynomial σ ℤ)) =
          MvPolynomial.monomial (Finsupp.single (s n) 1) 1 := rfl
      rw [map_mul, hφ, hf, mul_assoc, hX, MvPolynomial.monomial_mul, MvPolynomial.C_mul_monomial,
        one_mul, add_tsub_cancel_of_le he]
    · simp

private theorem smul_mem_lemma_2 {K : Type} {ι : K → Type} {Φ : Type} [Field Φ]
    (y : (Σ k, ι k) → Φ) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ f ∈ mCoordIdeal y, MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0)
    (c : K → ℂ) (f : MRing ι) (hf : f ∈ mCoordIdeal y) :
    MvPolynomial.eval (fun r : (Σ k, ι k) => c r.1 * z r) (MvPolynomial.map (Int.castRingHom ℂ) f) = 0 := by
  classical
  let φ : MvPolynomial ((k : K) × ι k) ℤ →ₐ[ℤ] MvPolynomial K (MvPolynomial ((k : K) × ι k) ℤ) :=
    MvPolynomial.aeval (fun q => MvPolynomial.C (MvPolynomial.X q) * MvPolynomial.X q.1)
  have hφ : ∀ q, φ (MvPolynomial.X q) = MvPolynomial.C (MvPolynomial.X q) * MvPolynomial.X q.1 :=
    fun q => MvPolynomial.aeval_X _ _
  have hA : ∀ g, mConeMap y g =
      MvPolynomial.map (MvPolynomial.aeval (R := ℤ) y).toRingHom (φ g) := by
    intro g
    have key : (mConeMap y : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial K Φ) =
        ((MvPolynomial.map (MvPolynomial.aeval (R := ℤ) y).toRingHom).toIntAlgHom).comp φ := by
      apply MvPolynomial.algHom_ext
      intro q
      show mConeMap y (MvPolynomial.X q) =
        MvPolynomial.map (MvPolynomial.aeval (R := ℤ) y).toRingHom (φ (MvPolynomial.X q))
      rw [hφ]
      simp [mConeMap]
    rw [key]
    rfl
  have hf' : mConeMap y f = 0 := RingHom.mem_ker.mp hf
  have hcomp : ∀ a, (φ f).coeff a ∈ mCoordIdeal y := by
    intro a
    have h1 : (MvPolynomial.aeval (R := ℤ) y).toRingHom ((φ f).coeff a) = 0 := by
      have := congrArg (AddMonoidAlgebra.coeff · a) (hA f)
      rw [hf', MvPolynomial.coeff_zero, MvPolynomial.coeff_map] at this
      exact this.symm
    show (φ f).coeff a ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker, hA, grading_map_coeff_eq_monomial Sigma.fst φ hφ f a, MvPolynomial.map_monomial, h1,
      map_zero]
  have hB : MvPolynomial.eval (fun r : (Σ k, ι k) => c r.1 * z r) (MvPolynomial.map (Int.castRingHom ℂ) f) =
      MvPolynomial.eval c (MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom (φ f)) := by
    rw [MvPolynomial.eval_map, ← algebraMap_int_eq, ← MvPolynomial.aeval_def]
    have key : (MvPolynomial.aeval (R := ℤ) (fun r : (Σ k, ι k) => c r.1 * z r)) =
        ((MvPolynomial.eval c).toIntAlgHom).comp
          (((MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom).toIntAlgHom).comp φ) := by
      apply MvPolynomial.algHom_ext
      intro q
      show MvPolynomial.aeval (R := ℤ) (fun r : (Σ k, ι k) => c r.1 * z r) (MvPolynomial.X q) =
        MvPolynomial.eval c (MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom (φ (MvPolynomial.X q)))
      rw [hφ]
      simp [mul_comm]
    rw [key]
    rfl
  rw [hB]
  have hzero : MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom (φ f) = 0 := by
    ext a
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
    have := hz _ (hcomp a)
    rwa [MvPolynomial.eval_map, ← algebraMap_int_eq, ← MvPolynomial.aeval_def] at this
  rw [hzero, map_zero]

theorem weight_descends_of_sameOrbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (e e' : ℕ)
    (R : AnLogRes (mCoordIdeal y) ⊤ e) (Rp : AnLogRes (mCoordIdeal (y ∘ stepV M p)) ⊤ e') (h : R.X → Rp.X)
    (A B : HermLine ι) (ph : Rp.X → ℝ) (W : Set Rp.X), A.a = B.a →
    (∀ x, SameOrbit (Rp.lift (h x) (h x)) (R.lift x x ∘ stepV M p)) →
    (∀ x ∈ W, ∀ z ∈ mcPts (mCoordIdeal y), z ∘ stepV M p = Rp.lift x x →
      Real.log (A.h z) = Real.log (B.h z) + ph x) →
    ∀ x, h x ∈ W → Real.log (A.h (R.lift x x)) = Real.log (B.h (R.lift x x)) + ph (h x) := by
  intro K _ ι _ Φ _ y Ψ N j M p e e' R Rp h A B ph W hab horb hW x hx
  classical
  obtain ⟨c, hc0, hceq⟩ := horb x
  have hwmem : R.lift x x ∈ mcPts (mCoordIdeal y) := R.mem x x (R.mem_U x)
  let c' : K → ℂ := fun k =>
    if hk : ((∀ p' : Ψ × Fin N, M.blk p' ≠ Option.some k) ∨ M.blk p = Option.some k) then c ⟨k, hk⟩ else 1
  have hc'0 : ∀ k, c' k ≠ 0 := by
    intro k
    by_cases hk : ((∀ p' : Ψ × Fin N, M.blk p' ≠ Option.some k) ∨ M.blk p = Option.some k)
    · simp only [c', dif_pos hk]
      exact hc0 _
    · simp only [c', dif_neg hk]
      exact one_ne_zero
  let z : (Σ k, ι k) → ℂ := fun r => c' r.1 * R.lift x x r
  have hzstep : z ∘ stepV M p = Rp.lift (h x) (h x) := by
    rw [hceq]
    funext q
    have hq : (∀ p' : Ψ × Fin N, M.blk p' ≠ Option.some q.1.1) ∨ M.blk p = Option.some q.1.1 := q.1.2
    show c' q.1.1 * R.lift x x ⟨q.1.1, q.2⟩ = c q.1 * R.lift x x ⟨q.1.1, q.2⟩
    congr 1
    simp only [c', dif_pos hq]
  have hzmem : z ∈ mcPts (mCoordIdeal y) := by
    refine ⟨fun k => ?_, fun f hf => ?_⟩
    · obtain ⟨i, hi⟩ := hwmem.1 k
      exact ⟨i, mul_ne_zero (hc'0 k) hi⟩
    · exact smul_mem_lemma_2 y (R.lift x x) hwmem.2 c' f hf
  have key := hW (h x) hx z hzmem hzstep
  have hAz : A.h z = (∏ k, ‖c' k‖ ^ A.a k) * A.h (R.lift x x) := A.smul c' _ hc'0
  have hBz : B.h z = (∏ k, ‖c' k‖ ^ A.a k) * B.h (R.lift x x) := by
    rw [hab]
    exact B.smul c' _ hc'0
  have hP : (∏ k, ‖c' k‖ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc'0 k)))
  have hApos := A.pos _ hwmem.1
  have hBpos := B.pos _ hwmem.1
  rw [hAz, hBz, Real.log_mul hP hApos.ne', Real.log_mul hP hBpos.ne'] at key
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.FA
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlatWeightExtends
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothExtensionAcrossClosedDense
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothExtensionAcrossClosedDense
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothGlue

theorem continuousAt_of_smoothOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {N : Set X} {E : X → ℝ} (hN : IsOpen N) (hS : A.SmoothOn N E) {p : X} (hp : p ∈ N) :
    ContinuousAt E p := by
  obtain ⟨j, hj⟩ := A.cover p
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' N) :=
    (A.chart j).isOpen_inter_preimage_symm hN
  have hz : A.chart j p ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' N := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simpa [Set.mem_preimage, (A.chart j).left_inv hj] using hp
  have h1 : ContinuousAt (E ∘ (A.chart j).symm) (A.chart j p) :=
    ((hS j).continuousOn).continuousAt (hopen.mem_nhds hz)
  have h2 : ContinuousAt (A.chart j) p := (A.chart j).continuousAt hj
  have h1' : ContinuousAt (E ∘ (A.chart j).symm) ((A.chart j) p) := h1
  have h3 : ContinuousAt ((E ∘ (A.chart j).symm) ∘ (A.chart j)) p :=
    ContinuousAt.comp h1' h2
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [Function.comp, (A.chart j).left_inv hy]

theorem eq_of_dense_compl {X : Type} [TopologicalSpace X] {B W : Set X} {f g : X → ℝ}
    (hD : Dense Bᶜ) (hW : IsOpen W) (hf : ∀ p ∈ W, ContinuousAt f p)
    (hg : ∀ p ∈ W, ContinuousAt g p) (hfg : ∀ y ∈ W, y ∉ B → f y = g y) :
    ∀ y ∈ W, f y = g y := by
  intro y hy
  by_contra hne
  have hc : ContinuousAt (fun w => f w - g w) y := (hf y hy).sub (hg y hy)
  have hev : ∀ᶠ w in 𝓝 y, f w - g w ≠ 0 := hc.eventually_ne (sub_ne_zero.mpr hne)
  obtain ⟨w, hwB, hw1, hw2⟩ := hD.inter_nhds_nonempty (hev.and (hW.mem_nhds hy))
  exact hw1 (sub_eq_zero.mpr (hfg w hw2 hwB))

theorem glue : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (u : X → ℝ), IsClosed B → Dense Bᶜ → (∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ B → E y = u y) → ∃ u' : X → ℝ, A.Smooth u' ∧ ∀ y ∉ B, u' y = u y := by
  intro e X _ A B u _ hD h
  classical
  choose N E hN hx hS hE using h
  have hagree : ∀ x y, ∀ w ∈ N x ∩ N y, E x w = E y w := by
    intro x y
    refine eq_of_dense_compl hD ((hN x).inter (hN y))
      (fun p hp => continuousAt_of_smoothOn A (hN x) (hS x) hp.1)
      (fun p hp => continuousAt_of_smoothOn A (hN y) (hS y) hp.2) ?_
    intro w hw hwB
    rw [hE x w hw.1 hwB, hE y w hw.2 hwB]
  refine ⟨fun y => if y ∈ B then E y y else u y, ?_, ?_⟩
  · have hu' : ∀ x, ∀ y ∈ N x, (if y ∈ B then E y y else u y) = E x y := by
      intro x y hy
      by_cases hB : y ∈ B
      · rw [if_pos hB]
        exact hagree y x y ⟨hx y, hy⟩
      · rw [if_neg hB]
        exact (hE x y hy hB).symm
    intro j z hz
    have hzt : z ∈ (A.chart j).target := hz.1
    set x := (A.chart j).symm z with hxdef
    have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' N x) :=
      (A.chart j).isOpen_inter_preimage_symm (hN x)
    have hzm : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' N x := ⟨hzt, hx x⟩
    have hc : ContDiffAt ℝ ∞ (E x ∘ (A.chart j).symm) z :=
      (hS x j).contDiffAt (hopen.mem_nhds hzm)
    refine (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hopen.mem_nhds hzm] with w hw
    exact hu' x _ hw.2
  · intro y hy
    simp [hy]

end GlobalTheory.CompanionTheory.SmoothGlue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothExtensionAcrossClosedDenseStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_extension_across_closed_dense : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (u : X → ℝ), IsClosed B → Dense Bᶜ → (∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ B → E y = u y) → ∃ u' : X → ℝ, A.Smooth u' ∧ ∀ y ∉ B, u' y = u y := by
  first | exact @GlobalTheory.CompanionTheory.SmoothGlue.glue | exact GlobalTheory.CompanionTheory.SmoothGlue.glue | (intros; apply GlobalTheory.CompanionTheory.SmoothGlue.glue <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PshExtensionAcrossClosedDense
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PshExtensionAcrossClosedDense
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.AnForm

theorem isPsh_of_dense_compl : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (Q Q' : LocPot X), IsClosed B → Dense Bᶜ → (∀ x, Q'.U x = Q.U x) → (∀ x, A.SmoothOn (Q'.U x) (Q'.φ x)) → (∀ x, ∀ y ∈ Q.U x, y ∉ B → Q'.φ x y = Q.φ x y) → IsPshOn A Bᶜ Q → IsPsh A Q' := by
  intro e X _ A B Q Q' hB hD hU hS hE hP x j y hy w
  by_contra hneg
  have hneg' : levi (Q'.φ x ∘ (A.chart j).symm) y w < 0 := not_le.mp hneg
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (Q'.isOpen_U x)
  have hf : ContDiffOn ℝ 2 (Q'.φ x ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) :=
    (hS x j).of_le ENat.LEInfty.out
  have hc := continuousOn_levi hO hf
  have hc' : ContinuousOn (fun y' => levi (Q'.φ x ∘ (A.chart j).symm) y' w)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) :=
    hc.comp (f := fun y' => (y', w)) (by fun_prop) (fun y' hy' => ⟨hy', Set.mem_univ _⟩)
  have hV := hc'.isOpen_inter_preimage hO (isOpen_Iio (a := (0 : ℝ)))
  set V := ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) ∩
    (fun y' => levi (Q'.φ x ∘ (A.chart j).symm) y' w) ⁻¹' Set.Iio 0 with hVdef
  have hVt : V ⊆ (A.chart j).target := fun z hz => hz.1.1
  have hVi : IsOpen ((A.chart j).symm '' V) :=
    (A.chart j).symm.isOpen_image_of_subset_source hV hVt
  have hne : ((A.chart j).symm '' V).Nonempty := ⟨_, y, ⟨hy, hneg'⟩, rfl⟩
  obtain ⟨z, ⟨y', hy'V, rfl⟩, hzB⟩ := hD.inter_open_nonempty _ hVi hne
  have hW : IsOpen (V ∩ (A.chart j).symm ⁻¹' Bᶜ) := by
    have h1 := (A.chart j).isOpen_inter_preimage_symm hB.isOpen_compl
    have : V ∩ (A.chart j).symm ⁻¹' Bᶜ =
        V ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Bᶜ) := by
      ext u
      exact ⟨fun h => ⟨h.1, hVt h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [this]
    exact hV.inter h1
  have hev : (Q'.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y'] (Q.φ x ∘ (A.chart j).symm) := by
    filter_upwards [hW.mem_nhds ⟨hy'V, hzB⟩] with u hu
    have huU : (A.chart j).symm u ∈ Q.U x := hU x ▸ hu.1.1.2
    exact hE x _ huU hu.2
  have h0 := hP x j y' ⟨hy'V.1.1, (hU x ▸ hy'V.1.2 : (A.chart j).symm y' ∈ Q.U x), hzB⟩ w
  rw [← levi_congr hev w] at h0
  exact absurd h0 (not_le.mpr hy'V.2)

end GlobalTheory.CompanionTheory.AnForm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PshExtensionAcrossClosedDenseStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psh_extension_across_closed_dense : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (Q Q' : LocPot X), IsClosed B → Dense Bᶜ → (∀ x, Q'.U x = Q.U x) → (∀ x, A.SmoothOn (Q'.U x) (Q'.φ x)) → (∀ x, ∀ y ∈ Q.U x, y ∉ B → Q'.φ x y = Q.φ x y) → IsPshOn A Bᶜ Q → IsPsh A Q' := by
  first | exact @GlobalTheory.CompanionTheory.AnForm.isPsh_of_dense_compl | exact GlobalTheory.CompanionTheory.AnForm.isPsh_of_dense_compl | (intros; apply GlobalTheory.CompanionTheory.AnForm.isPsh_of_dense_compl <;> assumption)
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem flat_weight_extends : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : LocPot X) (u : X → ℝ) (C₁ : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1)) → (∀ y ∉ bdry s, |u y| ≤ C₁ * Real.log (rW L s y)) → ∃ u' : X → ℝ, A.Smooth u' ∧ (∀ y ∉ bdry s, u' y = u y) ∧ IsPsh A (th + LocPot.ofFun u') ∧ IsPsh A ((th + LocPot.ofFun u').rsmul (-1)) := by
  intro e X _ _ _ A L s nb m W hL hs hsnc hn th u C₁ hth hu hp hp' hb
  have hthm : IsPotential A (th.rsmul (-1)) := isPotentialRsmul A (-1) th hth
  have hum : A.SmoothOn (bdry s)ᶜ (fun y => -u y) := fun j => (hu j).neg
  have hpm : IsPshOn A (bdry s)ᶜ (th.rsmul (-1) + LocPot.ofFun (fun y => -u y)) := by
    intro x j y hy w
    have hf : (((th.rsmul (-1) + LocPot.ofFun (fun y => -u y)).φ x) ∘ (A.chart j).symm) =
        (((th + LocPot.ofFun u).rsmul (-1)).φ x) ∘ (A.chart j).symm := by
      funext z
      simp only [Function.comp, LocPot.rsmul]
      show -1 * th.φ x _ + -u _ = -1 * (th.φ x _ + u _)
      ring
    rw [hf]
    exact hp' x j y hy w
  obtain ⟨C5, h5⟩ := GlobalTheory.T.singular_potential_log_growth_psh e X A L s nb m W hL hs hsnc hn th u C₁ hth hu hp hb
  obtain ⟨C6, h6⟩ := GlobalTheory.T.singular_potential_log_growth_psh e X A L s nb m W hL hs hsnc hn (th.rsmul (-1)) (fun y => -u y) C₁ hthm hum hpm
    (fun y hy => by simpa using hb y hy)
  have hM : ∀ y ∉ bdry s, |u y| ≤ max C5 C6 := by
    intro y hy
    have a := (h5.2.2.2 y hy).2
    have b := (h6.2.2.2 y hy).2
    rw [abs_le]
    constructor
    · have := le_max_right C5 C6; linarith
    · exact a.trans (le_max_left _ _)
  obtain ⟨hcl, hde⟩ := GlobalTheory.T.section_boundary_closed_and_codense e X A L s nb m W hs hsnc
  obtain ⟨u', hu', heq⟩ := GlobalTheory.T.smooth_extension_across_closed_dense e X A (bdry s) u hcl hde
    (GlobalTheory.T.bounded_psh_correction_locally_smooth e X A L s nb m W hs hsnc th u _ hth hu hp hp' hM)
  have hsm : ∀ x, A.SmoothOn ((th + LocPot.ofFun u').U x) ((th + LocPot.ofFun u').φ x) := by
    intro x j
    have h1 : ContDiffOn ℝ ∞ (th.φ x ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((th + LocPot.ofFun u').U x)) :=
      (hth.1 x j).mono fun y hy => ⟨hy.1, hy.2.1⟩
    have h2 : ContDiffOn ℝ ∞ (u' ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((th + LocPot.ofFun u').U x)) :=
      (hu' j).mono fun y hy => ⟨hy.1, trivial⟩
    exact h1.add h2
  refine ⟨u', hu', heq, ?_, ?_⟩
  · refine GlobalTheory.T.psh_extension_across_closed_dense e X A (bdry s) (th + LocPot.ofFun u) (th + LocPot.ofFun u') hcl hde
      (fun _ => rfl) hsm ?_ hp
    intro x y _ hy
    show th.φ x y + u' y = th.φ x y + u y
    rw [heq y hy]
  · refine GlobalTheory.T.psh_extension_across_closed_dense e X A (bdry s) ((th + LocPot.ofFun u).rsmul (-1))
      ((th + LocPot.ofFun u').rsmul (-1)) hcl hde (fun _ => rfl) ?_ ?_ hp'
    · intro x j
      have := (hsm x j).const_smul (-1 : ℝ)
      refine this.congr fun y _ => ?_
      simp [LocPot.rsmul]
    · intro x y _ hy
      show -1 * (th.φ x y + u' y) = -1 * (th.φ x y + u y)
      rw [heq y hy]

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelAnalyticDataExists
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

theorem central_regular {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {nb : ℕ} (m : Fin nb → ℕ) (W : Fin nb → Set X)
    (hL : IsPotential A L) (hs : IsSection A L s) (snc : IsSNC A L s m W) (hn : ∀ y, logNormSec L s y ≤ 0)
    (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ) (th : LocPot X) (u : X → ℝ) (C₅ : ℝ)
    (hsw : IsSingWeight A L s th u C₅) (hneg : IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1))) :
    ∃ (u' : X → ℝ) (C₀ : ℝ), A.Smooth u' ∧ (∀ y ∉ bdry s, u' y = u y) ∧ IsPsh A (th + LocPot.ofFun u') ∧
      IsPsh A ((th + LocPot.ofFun u').rsmul (-1)) ∧ IsSingWeight A L s th u' C₀ ∧
      IsRegFamily A Θ L s th u' (fun _ => u') C₀ (Real.exp (-Real.exp 1)) ∧
      IsRegFamilyC2 A s u' fun _ => u' := by
  obtain ⟨hth, hsm, hpsh, hb⟩ := hsw
  have hlog : ∀ y, 1 ≤ Real.log (rW L s y) := fun y => by
    have h1 : Real.exp 1 ≤ rW L s y := by
      have := hn y
      unfold rW
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) h1
  have hbd : ∀ y ∉ bdry s, |u y| ≤ |C₅| * Real.log (rW L s y) := fun y hy => by
    obtain ⟨h1, h2⟩ := hb y hy
    have h3 := hlog y
    have h4 : C₅ ≤ |C₅| := le_abs_self _
    have h5 : -|C₅| ≤ C₅ := neg_abs_le _
    have h6 : 0 ≤ |C₅| := abs_nonneg _
    rw [abs_le]
    constructor <;> nlinarith
  obtain ⟨u', hu', heq, hp1, hp2⟩ := GlobalTheory.CompanionTheory.Ar.PB.Flat.flat_weight_extends e X A L s nb m W hL hs snc hn th u |C₅| hth hsm hpsh hneg hbd
  obtain ⟨C₀, h1, h2, h3⟩ := (GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members e X A Θ L s nb m W hL hs snc hn hΘ hΘp).2.2 th u' hth hu' hp1
  exact ⟨u', C₀, hu', heq, hp1, hp2, h1, h2, h3⟩

theorem deg0_orbit {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)] (B : HermLine ρ) (hB : B.a = 0)
    {z z' : (Σ k, ρ k) → ℂ} (h : SameOrbit z z') : B.h z = B.h z' := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [B.smul c z' hc, hB]
  simp

theorem dy_eq_zero (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (k : K)
    (hk : k ∉ Set.range (Subtype.val : PartialFlagBlocks M p → K)) : M.dy p k = 0 := by
  have h1 : ¬ ∀ p', M.blk p' ≠ some k := fun h => hk ⟨⟨k, Or.inl h⟩, rfl⟩
  have h2 : M.blk p ≠ some k := fun h => hk ⟨⟨k, Or.inr h⟩, rfl⟩
  unfold FlagModel.dy
  rw [dite_eq_right h1, if_neg h2]

theorem step_member (hR : RegGlobalStatement) (hP : PullbackStatement) [Fintype Ψ] [DecidableEq Ψ]
    (M : FlagModel y Ψ N j) {n e : ℕ} (BM : BaseMetric M n) (R : AnLogRes (mCoordIdeal y) ⊤ e)
    (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr)
    (hdim : e = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2))
    (hb : ∀ x, SameOrbit (basePart M.blk (R.lift x x)) (BM.Rb.lift (pr x) (pr x)))
    (pL : IsPotential R.A (BM.L.pullback pr hp.1))
    (sL : IsSection R.A (BM.L.pullback pr hp.1) fun x y => BM.s (pr x) (pr y))
    (nL : IsSNC R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.m fun k => pr ⁻¹' BM.W k)
    (p : Ψ × Fin N) :
    ∃ (ph : R.X → ℝ) (phT : ℝ → R.X → ℝ) (line : ℝ → HermLine ι) (C₅ C t₀ : ℝ),
      IsStepMember BM R pr hp p ph phT line C₅ C t₀ := by
  have hv := isBlockMap_stepV M p
  obtain ⟨e', Rp, -, prp, hq, hpts, hch⟩ := GlobalTheory.T.flag_bundle_partial_block_map K ι Φ y Ψ N j M n e BM.Rb hdim (· = p) (PartialFlagBlocks M p)
    (stepIdx M p) Subtype.val (stepV M p) hv (mem_range_step M p)
  obtain ⟨pL', sL', nL', B, hB⟩ := GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection e' n Rp.X BM.Rb.X Rp.A BM.Rb.A BM.Bat prp hq BM.L BM.s BM.nb BM.m
    BM.W BM.potL BM.sec BM.snc BM.norm_le hch
  have hkeep : ∀ k, ((∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k) →
      k ∈ Set.range (Subtype.val : PartialFlagBlocks M p → K) := fun k hk => ⟨⟨k, hk⟩, rfl⟩
  obtain ⟨ph', C₅, hw1, -, hsw, hgb⟩ := GlobalTheory.T.partial_flag_bundle_metric_line K ι Φ y Ψ N j M n e BM p (PartialFlagBlocks M p) (stepIdx M p)
    Subtype.val (stepV M p) hv hkeep e' Rp prp hq B hpts pL' sL' nL' hB
  have hn' : ∀ x, logNormSec (BM.L.pullback prp hq.1) (fun x y => BM.s (prp x) (prp y)) x ≤ 0 :=
    fun x => BM.norm_le (prp x)
  have hn : ∀ x, logNormSec (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x ≤ 0 :=
    fun x => BM.norm_le (pr x)
  obtain ⟨hA', hfs', hΘ'⟩ := GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential (PartialFlagBlocks M p) (stepIdx M p) _ e' Rp
  obtain ⟨hA, hfs, hΘ⟩ := GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential K ι _ e R
  obtain ⟨h, hh, hso⟩ := GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj (PartialFlagBlocks M p) (stepIdx M p) K ι Subtype.val (stepV M p) _ _ ⊤ e' e Rp R hv
    (GlobalTheory.CompanionTheory.Ar.PB.FA.ImageIdeal.mCoordIdeal_comp_le_imageZ K ι (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) Φ y hv)
  obtain ⟨hfac, hinj⟩ := GlobalTheory.CompanionTheory.Ar.PB.FA.StepMap.factor K ι Φ y Ψ N j M p n e e' BM.Rb R Rp pr prp h hb hpts hso
  have hreg : ∃ (ph₂ : Rp.X → ℝ) (phT₂ : ℝ → Rp.X → ℝ) (C₅₂ C t₀ : ℝ),
      IsSingWeight Rp.A (BM.L.pullback prp hq.1) (fun x y => BM.s (prp x) (prp y))
        (potOf Rp (fsHerm (stepIdx M p) fun k => M.dy p k.1)) ph₂ C₅₂ ∧
      IsRegFamily Rp.A (potOf Rp (fsHerm (stepIdx M p) fun _ => 1)) (BM.L.pullback prp hq.1)
        (fun x y => BM.s (prp x) (prp y)) (potOf Rp (fsHerm (stepIdx M p) fun k => M.dy p k.1)) ph₂ phT₂ C t₀ ∧
      IsRegFamilyC2 Rp.A (fun x y => BM.s (prp x) (prp y)) ph₂ phT₂ ∧
      (∀ x, prp x ∉ bdry BM.s → ph₂ x = ph' x) ∧
      ((p.2 : ℕ) + 1 = N → Rp.A.Smooth ph₂ ∧ (∀ t, phT₂ t = ph₂) ∧
        IsPsh Rp.A (potOf Rp (fsHerm (stepIdx M p) (fun k => M.dy p k.1)) + LocPot.ofFun ph₂) ∧
        IsPsh Rp.A ((potOf Rp (fsHerm (stepIdx M p) (fun k => M.dy p k.1)) + LocPot.ofFun ph₂).rsmul (-1))) := by
    by_cases hc : (p.2 : ℕ) + 1 = N
    · have flat := GlobalTheory.CompanionTheory.Ar.PB.FA.Flat.flat_off_boundary K ι Φ y Ψ N j M n BM p hc (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) hv
        (fun k hk => hkeep k (Or.inl hk)) e' Rp prp hq ph' hpts hw1
      obtain ⟨u', C₀, hu', heq, p1, p2, s1, r1, c1⟩ := central_regular Rp.A
        (potOf Rp (fsHerm (stepIdx M p) fun _ => 1)) _ _ BM.m _ pL' sL' nL' hn' (hA' _ hfs') hΘ' _ ph' C₅ hsw flat.2
      exact ⟨u', fun _ => u', C₀, C₀, _, s1, r1, c1, heq, fun _ => ⟨hu', fun _ => rfl, p1, p2⟩⟩
    · obtain ⟨C, t₀, phT, r, c⟩ := hR Rp.A B (potOf Rp (fsHerm (stepIdx M p) fun _ => 1)) _ _ BM.m _ (hA' _ hfs') hΘ'
        pL' sL' nL' hn' hB _ ph' C₅ hsw hgb
      exact ⟨ph', phT, C₅, C, t₀, hsw, r, c, fun _ _ => rfl, fun h => absurd h hc⟩
  obtain ⟨ph₂, phT₂, C₅₂, C, t₀, s2, r2, c2, heq, hcen⟩ := hreg
  have hw := GlobalTheory.CompanionTheory.Ar.PB.FA.weight_descends_of_sameOrbit K ι Φ y Ψ N j M p e e' R Rp h (BM.hom p) (fsHerm ι (M.dy p)) ph'
    {x | prp x ∉ bdry BM.s} (BM.hom_deg p) hso hw1
  obtain rfl : pr = prp ∘ h := funext fun x => (hfac x).symm
  obtain ⟨C', t₀', h1, h2, h3⟩ := hP Rp.A R.A h hh (potOf Rp (fsHerm (stepIdx M p) fun _ => 1)) _
    (potOf R (fsHerm ι fun _ => 1)) _ BM.m _ BM.m _ (hA' _ hfs') hΘ' (hA _ hfs) hΘ pL' sL' nL' hn' nL _ ph₂ phT₂ C₅₂ C t₀
    s2 r2 c2
  have hfsd : IsPotential R.A (potOf R (fsHerm ι (M.dy p))) := hA _ (GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm _)
  have hsp := GlobalTheory.CompanionTheory.Ar.PB.FA.BlockPot.samePot_block K ι (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) _ _ _ _ e e' R Rp h hh (M.dy p) hv
    (dy_eq_zero M p) hso
  have tr := GlobalTheory.CompanionTheory.Ar.PB.Transport.singWeight_regFamily_transport e R.X R.A (potOf R (fsHerm ι fun _ => 1)) _ _ _ _ (ph₂ ∘ h) (fun t => phT₂ t ∘ h) C₅₂ C'
    t₀' (hA _ hfs) sL hfsd h1.1 hsp
  obtain ⟨T, hT⟩ : ∃ T, T = min (min t₀ t₀') (Real.exp (-1)) := ⟨_, rfl⟩
  have hT0 : 0 < T := by
    rw [hT]
    exact lt_min (lt_min r2.1 h2.1) (Real.exp_pos _)
  have hT1 : T ≤ t₀ := by rw [hT]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hT2 : T ≤ t₀' := by rw [hT]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hT3 : T ≤ Real.exp (-1) := by rw [hT]; exact min_le_right _ _
  have reg' := (GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members e R.X R.A _ _ _ BM.nb BM.m _ pL sL nL hn (hA _ hfs) hΘ).2.1 _ _ _ _ _ |C'| T le_rfl hT0 hT2
    hT3 (tr.2 h2) hfsd
  have hB2 : ∀ t, ∃ Bt : HermLine (stepIdx M p), Bt.a = 0 ∧ (0 < t → t ≤ T → IsSmoothHerm Bt ∧
      ∀ x, Real.log (Bt.h (Rp.lift x x)) = phT₂ t x) := by
    intro t
    by_cases ht : 0 < t ∧ t ≤ T
    · obtain ⟨Bt, a0, hs, hl⟩ := GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_log_eq_of_smooth _ _ _ e' Rp (phT₂ t) (r2.2.2 t ht.1 (ht.2.trans hT1)).1
      exact ⟨Bt, a0, fun _ _ => ⟨hs, hl⟩⟩
    · exact ⟨fsHerm _ 0, rfl, fun h1 h2 => absurd ⟨h1, h2⟩ ht⟩
  choose Bf hBa hBs using hB2
  choose line hla hlon hls hll using fun t => GlobalTheory.CompanionTheory.Ar.PB.FA.StepLine.exists_stepLine K ι Φ y Ψ N j M p (Bf t) (hBa t)
  refine ⟨ph₂ ∘ h, fun t => phT₂ t ∘ h, line, C₅₂, |C'|, T, tr.1 h1, reg', h3, hla, hlon, ?_, ?_, ?_, ?_⟩
  · intro t h0 ht
    obtain ⟨hs, hl⟩ := hBs t h0 ht
    refine ⟨hls t hs, fun x => ?_⟩
    rw [hll t _ (R.mem x x (R.mem_U x)).1, ← deg0_orbit (Bf t) (hBa t) (hso x), hl]
    rfl
  · intro x hx
    rw [hw x hx]
    simp only [Function.comp]
    rw [heq _ hx]
  · intro x x' hx hk
    have e1 := hinj x x' hx hk
    exact ⟨by simp only [Function.comp, e1], fun t => by simp only [Function.comp, e1]⟩
  · intro hc t
    obtain ⟨hsm, hc1, p1, p2⟩ := hcen hc
    have hpp := GlobalTheory.CompanionTheory.Ar.PB.PshPull.isPsh_pull e e' R.X Rp.X R.A Rp.A h hh _ _ ph₂ hfsd (hA' _ (GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm _)) hsm hsp
    refine ⟨?_, ?_, ?_⟩
    · show IsPsh R.A ((_ + LocPot.ofFun (phT₂ t ∘ h)).rsmul (-1))
      rw [hc1 t]
      exact hpp.2 p2
    · show IsPsh R.A (_ + LocPot.ofFun (phT₂ t ∘ h))
      rw [hc1 t]
      exact hpp.1 p1
    · show phT₂ t ∘ h = _
      rw [hc1 t]

open scoped ContDiff

theorem degree_id_self {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) : IsDegreeOff A A id 1 ∅ := by
  have hA : A.IsAnalyticSubset ∅ := fun x =>
    ⟨Set.univ, isOpen_univ, trivial, 1, fun _ _ => 1, fun _ _ _ _ => analyticAt_const, by ext; simp⟩
  refine ⟨hA, interior_empty, hA, interior_empty, fun x _ => by simp, fun j k y hy _ hk => ?_⟩
  set E := (A.chart j).symm.trans (A.chart k) with he
  have hs : y ∈ E.source := ⟨hy, hk⟩
  have hf : DifferentiableAt ℂ (A.chart k ∘ (A.chart j).symm) y := (A.holo j k y ⟨hy, hk⟩).differentiableAt
  have ht := E.map_source hs
  have hg : DifferentiableAt ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y) :=
    (A.holo k j _ ⟨ht.1, ht.2⟩).differentiableAt
  have hc := fderiv_comp y hg hf
  have hid : (A.chart j ∘ (A.chart k).symm) ∘ (A.chart k ∘ (A.chart j).symm) =ᶠ[𝓝 y] id := by
    filter_upwards [E.open_source.mem_nhds hs] with w hw
    exact E.left_inv hw
  rw [hid.fderiv_eq, fderiv_id] at hc
  intro h0
  have := congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => LinearMap.det (L : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) hc
  simp only [ContinuousLinearMap.coe_id, LinearMap.det_id] at this
  erw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp] at this
  have h0' : LinearMap.det (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := h0
  rw [h0', mul_zero] at this
  exact one_ne_zero this

theorem common_bound {σ : Type} [Finite σ] (f : σ → ℝ) : ∃ M : ℝ, ∀ a, f a ≤ M := by
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  exact ⟨M, fun a => hM ⟨a, rfl⟩⟩

theorem common_scale {σ : Type} [Finite σ] (f : σ → ℝ) (hf : ∀ a, 0 < f a) : ∃ t : ℝ, 0 < t ∧ ∀ a, t ≤ f a := by
  obtain ⟨M, hM⟩ := common_bound fun a => (f a)⁻¹
  by_cases he : Nonempty σ
  · obtain ⟨a₀⟩ := he
    have hM0 : 0 < M := lt_of_lt_of_le (inv_pos.2 (hf a₀)) (hM a₀)
    refine ⟨M⁻¹, inv_pos.2 hM0, fun a => ?_⟩
    exact inv_le_of_inv_le₀ (hf a) (hM a)
  · exact ⟨1, one_pos, fun a => absurd ⟨a⟩ he⟩

theorem IsStepMember.mono {M : FlagModel y Ψ N j} {n e : ℕ} {BM : BaseMetric M n}
    {R : AnLogRes (mCoordIdeal y) ⊤ e} {pr : R.X → BM.Rb.X} {hp : HoloMap R.A BM.Rb.A pr} {p : Ψ × Fin N}
    {ph : R.X → ℝ} {phT : ℝ → R.X → ℝ} {line : ℝ → HermLine ι} {C₅ C t₀ D₅ D T : ℝ}
    (m₁ : ∀ th ph C₅ C₅', C₅ ≤ C₅' → IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) th ph C₅ →
      IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) th ph C₅')
    (m₂ : ∀ th ph phT C t₀ C' t₀', |C| ≤ C' → 0 < t₀' → t₀' ≤ t₀ → t₀' ≤ Real.exp (-1) →
      IsRegFamily R.A (potOf R (fsHerm ι fun _ => 1)) (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) th ph phT C t₀ →
      IsPotential R.A th →
      IsRegFamily R.A (potOf R (fsHerm ι fun _ => 1)) (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) th ph phT C' t₀')
    (h : IsStepMember BM R pr hp p ph phT line C₅ C t₀) (h₅ : C₅ ≤ D₅) (hD : |C| ≤ D) (hT0 : 0 < T) (hT : T ≤ t₀)
    (hT1 : T ≤ Real.exp (-1)) : IsStepMember BM R pr hp p ph phT line D₅ D T := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  exact ⟨m₁ _ _ _ _ h₅ a1, m₂ _ _ _ _ _ _ _ hD hT0 hT hT1 a2 a1.1, a3, a4, a5, fun t h0 h1 => a6 t h0 (h1.trans hT), a7⟩

theorem flagAn_of_res (hR : RegGlobalStatement) (hP : PullbackStatement) [Fintype Ψ] [DecidableEq Ψ]
    (M : FlagModel y Ψ N j) {n : ℕ} (d : ℕ) (BM : BaseMetric M n) (R : AnLogRes (mCoordIdeal y) ⊤ (d + 1))
    (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr) (harith : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2))
    (hdim : d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2))
    (hb : ∀ x, SameOrbit (basePart M.blk (R.lift x x)) (BM.Rb.lift (pr x) (pr x)))
    (hch : ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin (d + 1) → ℂ)) (kb : Fin BM.Rb.A.n) (σ : Fin n ↪ Fin (d + 1)),
      IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (BM.Rb.A.chart kb).source ∧
        ∀ i, BM.Rb.A.chart kb (pr x') i = ψ x' (σ i))) :
    Nonempty (FlagAn BM d) := by
  obtain ⟨pL, sL, nL, B, hB⟩ := GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection (d + 1) n R.X BM.Rb.X R.A BM.Rb.A BM.Bat pr hp BM.L BM.s BM.nb BM.m BM.W
    BM.potL BM.sec BM.snc BM.norm_le hch
  have hn : ∀ x, logNormSec (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x ≤ 0 :=
    fun x => BM.norm_le (pr x)
  obtain ⟨hA, hfs, hΘ⟩ := GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential K ι _ (d + 1) R
  have hfsa : ∀ a : K → ℤ, IsSmoothHerm (fsHerm ι a) := GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm
  choose ph phT line C₅ C t₀ hm using fun p => step_member hR hP M BM R pr hp hdim hb pL sL nL p
  obtain ⟨m₁, m₂, m₃⟩ := GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members (d + 1) R.X R.A (potOf R (fsHerm ι fun _ => 1)) _ _ BM.nb BM.m _ pL sL nL hn
    (hA _ hfs) hΘ
  have hsm0 : R.A.Smooth (0 : R.X → ℝ) := fun jj => by
    show ContDiffOn ℝ ∞ (fun _ => (0 : ℝ)) _
    exact contDiffOn_const
  have hpsh0 : IsPsh R.A (potOf R (fsHerm ι fun _ => 1) + LocPot.ofFun (0 : R.X → ℝ)) := by
    intro x jj z hz w
    have e1 : (potOf R (fsHerm ι fun _ => 1) + LocPot.ofFun (0 : R.X → ℝ)).φ x ∘ (R.A.chart jj).symm =
        (potOf R (fsHerm ι fun _ => 1)).φ x ∘ (R.A.chart jj).symm := by
      funext u
      show (potOf R (fsHerm ι fun _ => 1)).φ x _ + (0 : ℝ) = _
      rw [add_zero]
      rfl
    rw [e1]
    by_cases hw : w = 0
    · rw [hw, levi_zero]
    · exact (hΘ x jj z ⟨hz.1, hz.2.1⟩ w hw).le
  obtain ⟨C₀, s0, r0, c0⟩ := m₃ _ 0 (hA _ hfs) hsm0 hpsh0
  obtain ⟨D₅, hD₅⟩ := common_bound fun o : Option (Ψ × Fin N) => o.elim C₀ C₅
  obtain ⟨D, hD⟩ := common_bound fun o : Option (Ψ × Fin N) => o.elim |C₀| fun p => |C p|
  obtain ⟨T, hT0, hT⟩ := common_scale (fun o : Option (Option (Ψ × Fin N)) =>
    o.elim (Real.exp (-1)) fun o' => o'.elim (Real.exp (-Real.exp 1)) t₀) (by
      rintro (_ | _ | p)
      · exact Real.exp_pos _
      · exact Real.exp_pos _
      · exact (hm p).2.1.1)
  have hT1 : T ≤ Real.exp (-1) := hT none
  have hm' : ∀ p, IsStepMember BM R pr hp p (ph p) (phT p) (line p) D₅ D T := fun p =>
    IsStepMember.mono m₁ m₂ (hm p) (hD₅ (some p)) (hD (some p)) hT0 (hT (some (some p))) hT1
  have s0' := m₁ _ _ _ _ (hD₅ none) s0
  have r0' := m₂ _ _ _ _ _ _ _ (hD none) hT0 (hT (some none)) hT1 r0 (hA _ hfs)
  let S : AnSys (d + 1) (Option (Ψ × Fin N)) :=
    { X := R.X
      A := R.A
      Θ := potOf R (fsHerm ι fun _ => 1)
      L := BM.L.pullback pr hp.1
      s := fun x y => BM.s (pr x) (pr y)
      nb := BM.nb
      m := BM.m
      W := fun k => pr ⁻¹' BM.W k
      potΘ := hA _ hfs
      posΘ := hΘ
      potL := pL
      sec := sL
      snc := nL
      norm_le := hn
      th := fun o => o.elim (potOf R (fsHerm ι fun _ => 1)) fun p => potOf R (fsHerm ι (M.dy p))
      ph := fun o => o.elim 0 ph
      phT := fun o => o.elim (fun _ => 0) phT
      C₅ := D₅
      C := D
      t₀ := T
      sing := by
        rintro (_ | p)
        · exact s0'
        · exact (hm' p).1
      reg := by
        rintro (_ | p)
        · exact r0'
        · exact (hm' p).2.1
      c2 := by
        rintro (_ | p)
        · exact c0
        · exact (hm' p).2.2.1 }
  let Re : Realis S (mCoordIdeal y) :=
    { arith := harith
      J := ⊤
      R := R
      π := id
      holo := ⟨continuous_id, fun jj k => R.A.holo jj k⟩
      deg := 1
      deg_pos := one_pos
      br := ∅
      degree := degree_id_self R.A
      ref := fun o => o.elim (fsHerm ι fun _ => 1) fun p => fsHerm ι (M.dy p)
      ref_smooth := by
        rintro (_ | p)
        · exact hfs
        · exact hfsa _
      ref_pot := by
        rintro (_ | p) <;>
        exact fun x _ => ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ => analyticOnNhd_const,
          fun z _ => (sub_self _).trans Complex.zero_re.symm⟩
      line := fun o t => o.elim (fsHerm ι fun _ => 1) fun p => line p t
      line_deg := by
        rintro (_ | p) t
        · rfl
        · exact (hm' p).2.2.2.1 t
      line_smooth := by
        rintro (_ | p) t h0 h1
        · exact hfs
        · exact ((hm' p).2.2.2.2.2.1 t h0 h1).1
      line_eq := by
        rintro (_ | p) t h0 h1 x
        · show _ = _ + (0 : ℝ)
          rw [add_zero]
          rfl
        · exact ((hm' p).2.2.2.2.2.1 t h0 h1).2 x }
  refine ⟨{ S := S, Re := Re, J_top := rfl, deg_one := rfl, br_empty := rfl, ref_some := fun _ => rfl, ref_none := rfl,
            line_none := fun _ => rfl, ph_none := ⟨rfl, fun _ => rfl⟩, pos_none := ?_, pr := pr, pr_holo := hp,
            pr_eq := hb, L_eq := rfl, s_eq := rfl, hom_eq := ?_, step := ?_, step_ph := ?_, flat := ?_ }⟩
  · refine ⟨1, one_pos, fun t x jj z _ w => ?_⟩
    have e1 : (S.potT none t + S.Θ.rsmul (-1)).φ x ∘ (S.A.chart jj).symm = fun _ => (0 : ℝ) := by
      funext u
      show ((potOf R (fsHerm ι fun _ => 1)).φ x _ + (0 : ℝ)) + (-1) * (potOf R (fsHerm ι fun _ => 1)).φ x _ = 0
      ring
    rw [e1]
    simp [levi]
  · exact fun p x hx => (hm' p).2.2.2.2.2.2.1 x hx
  · exact fun p t => (hm' p).2.2.2.2.1 t
  · exact fun p x x' h1 h2 => (hm' p).2.2.2.2.2.2.2.1 x x' h1 h2
  · exact fun p h1 t => (hm' p).2.2.2.2.2.2.2.2 h1 t

theorem flagAn_exists : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → Nonempty (FlagAn BM d) := by
  intro hI K _ ι _ Φ _ y Ψ _ _ N j M n d BM harith hd
  obtain ⟨e, R, he, pr, hp, hpts, hch⟩ := GlobalTheory.T.flag_bundle_partial_block_map K ι Φ y Ψ N j M n (d + 1) BM.Rb hd (fun _ => True) K ι id id
    isBlockMap_id (fun k => ⟨fun _ => by
      by_cases h : ∀ p', M.blk p' ≠ some k
      · exact Or.inl h
      · push_neg at h
        obtain ⟨p, hp⟩ := h
        exact Or.inr ⟨p, trivial, hp⟩, fun _ => ⟨k, rfl⟩⟩)
  obtain rfl := he fun _ => trivial
  refine flagAn_of_res hI.regGlobal hI.pullback M d BM R pr hp harith hd (fun x => ?_) hch
  obtain ⟨z, -, hz, ho⟩ := hpts x
  have hz' : z = R.lift x x := hz
  rw [← hz']
  exact ho

end GlobalTheory.CompanionTheory.Ar.PB.FA
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelAnalyticDataExistsStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_analytic_data_exists : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → Nonempty (FlagAn BM d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FA.flagAn_exists | exact GlobalTheory.CompanionTheory.Ar.PB.FA.flagAn_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FA.flagAn_exists <;> assumption)
end
