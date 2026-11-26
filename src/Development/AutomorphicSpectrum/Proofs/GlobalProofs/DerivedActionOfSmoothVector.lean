module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraOfExpLocal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionEqZeroIffCoeffsMem
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EqZeroOfFourierCoefficientsVanish

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVector
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVector
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothDeriv

open scoped Matrix.Norms.Operator

variable {n : ℕ}

def coord : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Matrix.of.symm A
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem coord_apply (A : Matrix (Fin n) (Fin n) ℂ) : coord A = Matrix.of.symm A := rfl

theorem hasDerivAt_coord_mul_exp (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => coord (g * NormedSpace.exp (t • X))) (coord (g * X)) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact coord.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (h.const_mul g)

theorem contDiff_mul_right (X : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun z : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of z * X)) := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  have e : (fun z : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of z * X) a b) =
      fun z => ∑ c, z a c * X c b := by
    funext z
    simp [Matrix.mul_apply]
  rw [e]
  refine ContDiff.sum fun c _ => ContDiff.mul ?_ contDiff_const
  exact (contDiff_apply ℝ (fun _ => ℂ) c).comp (contDiff_apply ℝ (fun _ => (Fin n → ℂ)) a)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothDeriv

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

open SmoothDeriv

theorem hasDerivAt_dRep_and_isSmoothVec : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G),
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧
      IsSmoothVec G π (dRep π X v) := by
  intro n G H _ _ π hG hrep v hv X hX
  obtain ⟨F, hF, hFG⟩ := hv
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)

  have key : ∀ g ∈ G, HasDerivAt (fun t : ℝ => π g (π (NormedSpace.exp (t • X)) v))
      (fderiv ℝ F (Matrix.of.symm g) (coord (g * X))) 0 := by
    intro g hg
    have h1 := ((hFd (Matrix.of.symm g)).hasFDerivAt)
    have h2 : HasFDerivAt F (fderiv ℝ F (Matrix.of.symm g)) (coord (g * NormedSpace.exp ((0 : ℝ) • X))) := by
      simpa [coord_apply] using h1
    have h3 := h2.comp_hasDerivAt (0 : ℝ) (hasDerivAt_coord_mul_exp g X)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have hm : g * NormedSpace.exp (t • X) ∈ G := hG.mul_mem g hg _ (hX t)
    have := hFG (Matrix.of.symm (g * NormedSpace.exp (t • X))) (by
      rw [Equiv.apply_symm_apply]
      exact hm)
    simp only [Equiv.apply_symm_apply] at this
    simp only [Function.comp, coord_apply]
    rw [← this, hrep.2 g hg _ (hX t)]
    rfl
  have h1 : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v)
      (fderiv ℝ F (Matrix.of.symm 1) (coord (1 * X))) 0 := by
    have := key 1 hG.one_mem
    simpa [hrep.1] using this
  have hd : dRep π X v = fderiv ℝ F (Matrix.of.symm 1) (coord (1 * X)) := h1.deriv
  have h1' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 := by
    rw [hd]; exact h1
  refine ⟨h1', fun z => fderiv ℝ F z (Matrix.of.symm (Matrix.of z * X)), ?_, ?_⟩
  · exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_mul_right X)
  · intro z hz
    have h2 := ((π (Matrix.of z)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1'
    exact h2.unique (key _ hz)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVectorStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derived_action_of_smooth_vector : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G), HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧ IsSmoothVec G π (dRep π X v) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosed
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosed
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem lieOf_isLieSubalgebra : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G),
    (∀ X Y, X ∈ HCSS.lieOf G → Y ∈ HCSS.lieOf G → X + Y ∈ HCSS.lieOf G) ∧
    (∀ (r : ℝ) X, X ∈ HCSS.lieOf G → r • X ∈ HCSS.lieOf G) ∧
    (∀ X Y, X ∈ HCSS.lieOf G → Y ∈ HCSS.lieOf G → X * Y - Y * X ∈ HCSS.lieOf G) ∧
    (∀ k ∈ G, ∀ X ∈ HCSS.lieOf G, k * X * k⁻¹ ∈ HCSS.lieOf G) := by
  intro n G hG
  obtain ⟨𝔤, h𝔤, -⟩ := GlobalTheory.CompanionTheory.LinRedLie.exists_lieAlgebra hG
  have hm : ∀ X, X ∈ HCSS.lieOf G ↔ X ∈ 𝔤 := fun X => (h𝔤 X).symm
  refine ⟨fun X Y hX hY => ?_, fun r X hX => ?_, fun X Y hX hY => ?_, fun k hk X hX => ?_⟩
  · exact (hm _).2 (𝔤.add_mem ((hm X).1 hX) ((hm Y).1 hY))
  · exact (hm _).2 (𝔤.smul_mem r ((hm X).1 hX))
  · exact (hm _).2 ((GlobalTheory.CompanionTheory.LieStable.lieAlg_stable hG 𝔤 h𝔤).2 X ((hm X).1 hX) Y ((hm Y).1 hY))
  · exact (hm _).2 (GlobalTheory.CompanionTheory.LieStable.conj_mem hG h𝔤 hk ((hm X).1 hX))

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosedStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_of_linear_group_closed : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G), (∀ X Y, X ∈ HCSS.lieOf G → Y ∈ HCSS.lieOf G → X + Y ∈ HCSS.lieOf G) ∧ (∀ (r : ℝ) X, X ∈ HCSS.lieOf G → r • X ∈ HCSS.lieOf G) ∧ (∀ X Y, X ∈ HCSS.lieOf G → Y ∈ HCSS.lieOf G → X * Y - Y * X ∈ HCSS.lieOf G) ∧ (∀ k ∈ G, ∀ X ∈ HCSS.lieOf G, k * X * k⁻¹ ∈ HCSS.lieOf G) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorsInvariantSubspace
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorsInvariantSubspace
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem contDiff_mulRight {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun z : Fin n → Fin n → ℂ => (fun i j => (Matrix.of z * g) i j : Fin n → Fin n → ℂ)) := by
  have e : (fun z : Fin n → Fin n → ℂ => (fun i j => (Matrix.of z * g) i j : Fin n → Fin n → ℂ)) =
      fun z i j => ∑ k, z i k * g k j := by
    ext z i j
    simp [Matrix.mul_apply]
  rw [e]
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  refine ContDiff.sum fun k _ => ?_
  exact ((contDiff_apply ℝ (fun _ => ℂ) k).comp (contDiff_apply ℝ (fun _ => (Fin n → ℂ)) i)).mul contDiff_const

theorem smooth_closed : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π),
    (∀ u v : H, IsSmoothVec G π u → IsSmoothVec G π v → IsSmoothVec G π (u + v)) ∧
    (∀ (c : ℂ) (v : H), IsSmoothVec G π v → IsSmoothVec G π (c • v)) ∧
    (∀ g ∈ G, ∀ v : H, IsSmoothVec G π v → IsSmoothVec G π (π g v)) := by
  intro n G H _ _ π hG hrep
  refine ⟨?_, ?_, ?_⟩
  · rintro u v ⟨Fu, hFu, hu⟩ ⟨Fv, hFv, hv⟩
    refine ⟨fun z => Fu z + Fv z, hFu.add hFv, fun z hz => ?_⟩
    rw [map_add (f := _), hu z hz, hv z hz]
  · rintro c v ⟨Fv, hFv, hv⟩
    refine ⟨fun z => c • Fv z, hFv.const_smul c, fun z hz => ?_⟩
    rw [map_smul, hv z hz]
  · rintro g hg v ⟨Fv, hFv, hv⟩
    refine ⟨fun z => Fv (fun i j => (Matrix.of z * g) i j), hFv.comp (contDiff_mulRight g),
      fun z hz => ?_⟩
    calc π (Matrix.of z) (π g v) = π (Matrix.of z * g) v := by
          rw [hrep.2 _ hz _ hg, ContinuousLinearMap.comp_apply]
      _ = Fv (fun i j => (Matrix.of z * g) i j) := hv _ (hG.mul_mem _ hz _ hg)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorsInvariantSubspaceStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vectors_invariant_subspace : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π), (∀ u v : H, IsSmoothVec G π u → IsSmoothVec G π v → IsSmoothVec G π (u + v)) ∧ (∀ (c : ℂ) (v : H), IsSmoothVec G π v → IsSmoothVec G π (c • v)) ∧ (∀ g ∈ G, ∀ v : H, IsSmoothVec G π v → IsSmoothVec G π (π g v)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.smooth_closed | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.smooth_closed | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.smooth_closed <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralEqTsumFd
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs

section Gen

variable {V C : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
  [T2Space V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup C] [Countable C]

def per (ι : C →+ V) (f : V → ℂ) (b : V) : ℂ := ∑' c, f (b + ι c)

def UnifSummable (ι : C →+ V) (f : V → ℂ) : Prop :=
  ∀ K : Set V, IsCompact K → ∃ u : C → ℝ, Summable u ∧ ∀ c : C, ∀ b ∈ K, ‖f (b + ι c)‖ ≤ u c

theorem continuous_per {ι : C →+ V} {f : V → ℂ} (hf : Continuous f) (h : UnifSummable ι f) :
    Continuous (per ι f) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  obtain ⟨u, hu, hb⟩ := h K hK
  have : ContinuousOn (per ι f) K :=
    continuousOn_tsum (fun c => (hf.comp (continuous_id.add continuous_const)).continuousOn) hu
      (fun c b hb' => hb c b hb')
  exact this.continuousAt hxK

theorem per_add (ι : C →+ V) (f : V → ℂ) (x : V) (c : C) : per ι f (x + ι c) = per ι f x := by
  unfold per
  rw [← (Equiv.addLeft c).tsum_eq (fun d => f (x + ι d))]
  refine tsum_congr fun d => ?_
  simp [add_assoc]

theorem per_bounded {ι : C →+ V} {f : V → ℂ} (h : UnifSummable ι f) {K : Set V} (hK : IsCompact K)
    (hx : ∀ x, ∃ a, x - ι a ∈ K) : ∃ M, ∀ x, ‖per ι f x‖ ≤ M := by
  obtain ⟨u, hu, hb⟩ := h K hK
  refine ⟨∑' c, u c, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hx x
  have e : per ι f x = per ι f (x - ι a) := by
    rw [← per_add ι f (x - ι a) a, sub_add_cancel]
  rw [e]
  exact tsum_of_norm_bounded hu.hasSum fun c => hb c _ ha

theorem integrableOn_bdd {μ : Measure V} {D : Set V} (hD : μ D ≠ ∞) {g : V → ℂ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) : IntegrableOn g D μ :=
  Measure.integrableOn_of_bounded hD hg.aestronglyMeasurable (Filter.Eventually.of_forall hM)

theorem integrable_of_unif {ι : C →+ V} {f : V → ℂ} (hf : Continuous f) (h : UnifSummable ι f)
    (μ : Measure V) [μ.IsAddHaarMeasure] {K : Set V} (hK : IsCompact K) (hx : ∀ x, ∃ a, x - ι a ∈ K) :
    Integrable f μ := by
  obtain ⟨u, hu, hb⟩ := h K hK
  obtain ⟨k, hk⟩ : K.Nonempty := by
    obtain ⟨a, ha⟩ := hx 0
    exact ⟨_, ha⟩
  have hu0 : ∀ a, 0 ≤ u a := fun a => (norm_nonneg _).trans (hb a k hk)
  let s : C → TopologicalSpace.Compacts V := fun a =>
    ⟨(fun y => y + ι a) '' K, hK.image (continuous_id.add continuous_const)⟩
  let G : C(V, ℂ) := ⟨f, hf⟩
  have hs : ⋃ a, (s a : Set V) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨a, ha⟩ := hx x
    exact ⟨a, x - ι a, ha, sub_add_cancel _ _⟩
  have hμ : ∀ a, μ.real (s a : Set V) = μ.real K := by
    intro a
    have : ((s a : TopologicalSpace.Compacts V) : Set V) = (fun y => y + -ι a) ⁻¹' K := by
      show (fun y => y + ι a) '' K = _
      rw [Set.image_add_right]
    rw [this, Measure.real, Measure.real, measure_preimage_add_right]
  have hn : ∀ a, ‖G.restrict (s a : Set V)‖ ≤ u a := by
    intro a
    rw [ContinuousMap.norm_le _ (hu0 a)]
    rintro ⟨y, b, hb', rfl⟩
    exact hb a b hb'
  refine integrable_of_summable_norm_restrict (f := G) (s := s) ?_ hs
  refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) measureReal_nonneg) (fun a => ?_)
    (hu.mul_right (μ.real K))
  rw [hμ]
  exact mul_le_mul_of_nonneg_right (hn a) measureReal_nonneg

theorem countable_range (ι : C →+ V) : Countable ι.range :=
  ι.rangeRestrict_surjective.countable

theorem summable_fd {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) {h : V → ℂ} (hh : Integrable h μ) :
    Summable fun c => ∫ x in D, ‖h (x + ι c)‖ ∂μ := by
  have := countable_range ι
  have hsum := hD.lintegral_eq_tsum'' (fun x => ‖h x‖ₑ)
  have hfin : ∑' g : ι.range, ∫⁻ x in D, ‖h (g +ᵥ x)‖ₑ ∂μ ≠ ∞ := by
    rw [← hsum]
    exact hh.2.ne
  have hs := ENNReal.summable_toReal hfin
  have h2 := ((ι.ofInjective hι).toEquiv.summable_iff).2 hs
  refine h2.congr fun c => ?_
  rw [integral_norm_eq_lintegral_enorm (hh.comp_add_right (ι c)).integrableOn.aestronglyMeasurable]
  have : ∀ x, ((ι.ofInjective hι).toEquiv c : ι.range) +ᵥ x = x + ι c := fun x => by
    show ι c + x = x + ι c
    exact add_comm _ _
  simp only [Function.comp, this]

theorem integral_eq_tsum_fd {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) {h : V → ℂ} (hh : Integrable h μ) :
    ∫ x, h x ∂μ = ∑' c, ∫ x in D, h (x + ι c) ∂μ := by
  have := countable_range ι
  rw [hD.integral_eq_tsum'' h hh, ← (ι.ofInjective hι).toEquiv.tsum_eq]
  refine tsum_congr fun c => ?_
  have : ∀ x, ((ι.ofInjective hι).toEquiv c : ι.range) +ᵥ x = x + ι c := fun x => by
    show ι c + x = x + ι c
    exact add_comm _ _
  simp only [this]

theorem setIntegral_tsum_fd {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) {h : V → ℂ} (hh : Integrable h μ) :
    ∫ x in D, ∑' c, h (x + ι c) ∂μ = ∫ x, h x ∂μ := by
  have hs := hasSum_integral_of_summable_integral_norm (μ := μ.restrict D)
    (F := fun c x => h (x + ι c))
    (fun c => (hh.comp_add_right (ι c)).integrableOn) (summable_fd hι hD hh)
  rw [integral_eq_tsum_fd hι hD hh]
  exact hs.tsum_eq.symm

theorem per_unfold {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) {f e : V → ℂ} (hfi : Integrable f μ)
    (he : Continuous e) (hen : ∀ x, ‖e x‖ = 1) (hep : ∀ x c, e (x + ι c) = e x) :
    ∫ b in D, per ι f b * e b ∂μ = ∫ b, f b * e b ∂μ := by
  have hh : Integrable (fun b => f b * e b) μ :=
    hfi.mono (hfi.aestronglyMeasurable.mul he.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by simp [hen])
  rw [← setIntegral_tsum_fd hι hD hh]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show per ι f x * e x = ∑' c, f (x + ι c) * e (x + ι c)
  simp only [hep]
  exact tsum_mul_right.symm

def ser (a : C → ℂ) (E : C → V → ℂ) (b : V) : ℂ := ∑' t, a t * E t b

theorem continuous_ser {a : C → ℂ} (ha : Summable fun t => ‖a t‖) {E : C → V → ℂ}
    (hEc : ∀ t, Continuous (E t)) (hEn : ∀ t b, ‖E t b‖ = 1) : Continuous (ser a E) :=
  continuous_tsum (fun t => continuous_const.mul (hEc t)) ha (fun t b => by simp [hEn])

theorem norm_ser_le {a : C → ℂ} (ha : Summable fun t => ‖a t‖) {E : C → V → ℂ}
    (hEn : ∀ t b, ‖E t b‖ = 1) (b : V) : ‖ser a E b‖ ≤ ∑' t, ‖a t‖ :=
  tsum_of_norm_bounded ha.hasSum fun t => by simp [hEn]

theorem coef_ser {a : C → ℂ} (ha : Summable fun t => ‖a t‖) {E : C → V → ℂ}
    (hEc : ∀ t, Continuous (E t)) (hEn : ∀ t b, ‖E t b‖ = 1) {μ : Measure V} {D : Set V}
    (hD1 : μ D = 1) (hself : ∀ t x, E t x * E (-t) x = 1)
    (horth : ∀ s t, t ≠ s → ∫ x in D, E t x * E (-s) x ∂μ = 0) (s : C) :
    ∫ x in D, ser a E x * E (-s) x ∂μ = a s := by
  classical
  have hDf : μ D ≠ ∞ := by rw [hD1]; exact ENNReal.one_ne_top
  have hr : μ.real D = 1 := by simp [Measure.real, hD1]
  have hint : ∀ t, IntegrableOn (fun x => a t * E t x * E (-s) x) D μ := fun t =>
    integrableOn_bdd hDf ((continuous_const.mul (hEc t)).mul (hEc (-s))) (M := ‖a t‖)
      (fun x => by simp [hEn])
  have hn : ∀ t, ∫ x in D, ‖a t * E t x * E (-s) x‖ ∂μ = ‖a t‖ := fun t => by
    simp [hEn, hr]
  have hs := hasSum_integral_of_summable_integral_norm (μ := μ.restrict D)
    (F := fun t x => a t * E t x * E (-s) x) hint (by simpa only [hn] using ha)
  have hval : ∀ t, t ≠ s → ∫ x in D, a t * E t x * E (-s) x ∂μ = 0 := fun t ht => by
    simp only [mul_assoc]
    rw [integral_const_mul, horth s t ht, mul_zero]
  have hs1 : ∫ x in D, a s * E s x * E (-s) x ∂μ = a s := by
    simp only [mul_assoc, hself]
    simp [hr]
  have h1 := hasSum_single (f := fun t => ∫ x in D, a t * E t x * E (-s) x ∂μ) s
    (fun t ht => hval t ht)
  have h2 := hs.unique h1
  rw [hs1] at h2
  rw [← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ser a E x * E (-s) x = ∑' t, a t * E t x * E (-s) x
  simp only [ser, tsum_mul_right]

theorem poisson_gen {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) (hD1 : μ D = 1) {K : Set V}
    (hK : IsCompact K) (hx : ∀ x, ∃ a, x - ι a ∈ K) {E : C → V → ℂ}
    (hEc : ∀ t, Continuous (E t)) (hEn : ∀ t b, ‖E t b‖ = 1) (hEp : ∀ t x c, E t (x + ι c) = E t x)
    (hE0 : ∀ t, E t 0 = 1) (hself : ∀ t x, E t x * E (-t) x = 1)
    (horth : ∀ s t, t ≠ s → ∫ x in D, E t x * E (-s) x ∂μ = 0)
    (hcomp : ∀ g : V → ℂ, Continuous g → (∀ x c, g (x + ι c) = g x) →
      (∀ t, ∫ b in D, g b * E (-t) b ∂μ = 0) → ∀ x, g x = 0)
    {f : V → ℂ} (hf : Continuous f) (h : UnifSummable ι f) :
    Integrable f μ ∧ (Summable (fun t => ∫ b, f b * E (-t) b ∂μ) →
      ∑' c, f (ι c) = ∑' t, ∫ b, f b * E (-t) b ∂μ) := by
  have hfi := integrable_of_unif hf h μ hK hx
  refine ⟨hfi, fun hsum => ?_⟩
  have hDf : μ D ≠ ∞ := by rw [hD1]; exact ENNReal.one_ne_top
  set a : C → ℂ := fun t => ∫ b, f b * E (-t) b ∂μ with hadef
  have ha : Summable fun t => ‖a t‖ := hsum.norm
  have hP := continuous_per hf h
  have hS := continuous_ser ha hEc hEn
  obtain ⟨M, hM⟩ := per_bounded h hK hx
  have hperS : ∀ x c, ser a E (x + ι c) = ser a E x := fun x c => by
    simp only [ser, hEp]
  have hz := hcomp (fun x => per ι f x - ser a E x) (hP.sub hS)
    (fun x c => by simp only [per_add, hperS]) (fun t => ?_) 0
  · have e1 : per ι f 0 = ∑' c, f (ι c) := by simp [per]
    have e2 : ser a E 0 = ∑' t, a t := by simp [ser, hE0]
    rw [← e1, ← e2]
    exact sub_eq_zero.1 hz
  · have i1 : IntegrableOn (fun b => per ι f b * E (-t) b) D μ :=
      integrableOn_bdd hDf (hP.mul (hEc _)) (M := M) (fun x => by simpa [hEn] using hM x)
    have i2 : IntegrableOn (fun b => ser a E b * E (-t) b) D μ :=
      integrableOn_bdd hDf (hS.mul (hEc _)) (M := ∑' t, ‖a t‖)
        (fun x => by simpa [hEn] using norm_ser_le ha hEn x)
    simp only [sub_mul]
    rw [integral_sub i1 i2, per_unfold hι hD hfi (hEc _) (hEn _) (hEp _),
      coef_ser ha hEc hEn hD1 hself horth t, sub_eq_zero]

end Gen

section Adelic

end Adelic
end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsIsotypicSum
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Isotypic

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def IsIrrK (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧ IsKStable G π S ∧
    ∀ S' : Submodule ℂ H, S' ≤ S → IsKStable G π S' → S' = ⊥ ∨ S' = S

def isoGens (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (S : Submodule ℂ H) : Set (Submodule ℂ H) :=
  {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k ∈ maxCpt G, ∀ w ∈ S, T (π k w) = π k (T w)}

theorem orthogonal_kstable (hG : IsLinRed G) (hA : IsAdmOn G π) {S : Submodule ℂ H}
    (hS : IsKStable G π S) : IsKStable G π Sᗮ := by
  intro k hk y hy
  rw [Submodule.mem_orthogonal]
  intro s hs
  have hk' : star k ∈ maxCpt G := ⟨hG.star_mem k hk.1, Unitary.star_mem hk.2⟩
  have h1 : π k (π (star k) s) = s := by
    have hm : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hk.2
    rw [← ContinuousLinearMap.comp_apply, ← hA.1.2 k hk.1 (star k) hk'.1, hm, hA.1.1]
    rfl
  let Lk : H →ₗᵢ[ℂ] H := ⟨(π k : H →ₗ[ℂ] H), hA.2.2.1 k hk⟩
  have h2 : inner ℂ (π k (π (star k) s)) (π k y) = inner ℂ (π (star k) s) y := Lk.inner_map_map _ _
  rw [← h1, h2]
  exact Submodule.inner_right_of_mem_orthogonal (hS _ hk' s hs) hy

theorem sSup_kstable {A : Set (Submodule ℂ H)} (hA : ∀ S ∈ A, IsKStable G π S) :
    IsKStable G π (sSup A) := by
  intro k hk w hw
  have h : sSup A ≤ (sSup A).comap (π k : H →ₗ[ℂ] H) :=
    sSup_le fun S hS x hx => Submodule.mem_comap.2 (le_sSup hS (hA S hS k hk x hx))
  exact h hw

theorem exists_irr_family (hG : IsLinRed G) (hA : IsAdmOn G π) (m : ℕ) :
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Module.finrank ℂ S = m → IsKStable G π S →
      ∃ F : Set (Submodule ℂ H), F.Finite ∧ (∀ I ∈ F, IsIrrK G π I) ∧ S ≤ sSup F := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S hfin hm hS
    by_cases hirr : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStable G π S' → S' = ⊥ ∨ S' = S
    · refine ⟨{S}, Set.finite_singleton S, ?_, ?_⟩
      · rintro I rfl
        exact ⟨hfin, hS, hirr⟩
      · simp
    · push_neg at hirr
      obtain ⟨S', hle, hS', hne0, hneS⟩ := hirr
      haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hle
      have hlt : S' < S := lt_of_le_of_ne hle hneS
      have hT : IsKStable G π (S ⊓ S'ᗮ) := fun k hk v hv =>
        ⟨hS k hk v hv.1, orthogonal_kstable hG hA hS' k hk v hv.2⟩
      haveI : FiniteDimensional ℂ (S ⊓ S'ᗮ : Submodule ℂ H) := Submodule.finiteDimensional_of_le inf_le_left
      have hltT : S ⊓ S'ᗮ < S := by
        refine lt_of_le_of_ne inf_le_left fun h => hne0 ?_
        have hSo : S ≤ S'ᗮ := inf_eq_left.1 h
        rw [eq_bot_iff]
        intro x hx
        have h0 : ⟪x, x⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hx (hSo (hle hx))
        exact (Submodule.mem_bot ℂ).2 (inner_self_eq_zero.1 h0)
      have hd₁ : Module.finrank ℂ S' < m := hm ▸ Submodule.finrank_lt_finrank_of_lt hlt
      have hd₂ : Module.finrank ℂ (S ⊓ S'ᗮ : Submodule ℂ H) < m :=
        hm ▸ Submodule.finrank_lt_finrank_of_lt hltT
      obtain ⟨F₁, hF₁, hI₁, hle₁⟩ := ih _ hd₁ S' inferInstance rfl hS'
      obtain ⟨F₂, hF₂, hI₂, hle₂⟩ := ih _ hd₂ (S ⊓ S'ᗮ) inferInstance rfl hT
      refine ⟨F₁ ∪ F₂, hF₁.union hF₂, ?_, ?_⟩
      · rintro I (hI | hI)
        · exact hI₁ I hI
        · exact hI₂ I hI
      · intro v hv
        have hp : ((S'.orthogonalProjection v : S') : H) ∈ S' := (S'.orthogonalProjection v).2
        have hq : v - (S'.orthogonalProjection v : H) ∈ S ⊓ S'ᗮ :=
          ⟨S.sub_mem hv (hle hp), Submodule.sub_starProjection_mem_orthogonal (K := S') v⟩
        have e : v = (S'.orthogonalProjection v : H) + (v - (S'.orthogonalProjection v : H)) := by abel
        rw [e, sSup_union]
        exact Submodule.add_mem _ (Submodule.mem_sup_left (hle₁ hp)) (Submodule.mem_sup_right (hle₂ hq))

theorem isoGens_kstable {S S' : Submodule ℂ H} (hS : IsKStable G π S) (h : S' ∈ isoGens G π S) :
    IsKStable G π S' := by
  obtain ⟨T, rfl, hT⟩ := h
  rintro k hk _ ⟨s, hs, rfl⟩
  exact ⟨π k s, hS k hk s hs, hT k hk s hs⟩

theorem le_sSup_isoGens (S : Submodule ℂ H) : S ≤ sSup (isoGens G π S) := by
  refine le_trans (le_of_eq ?_) (le_sSup (show S.map LinearMap.id ∈ isoGens G π S from
    ⟨LinearMap.id, rfl, fun k _ w _ => rfl⟩))
  simp

theorem map_mem_of_gen {Y S S' : Submodule ℂ H} (hSY : sSup (isoGens G π S) ≤ Y) (h : S' ∈ isoGens G π S)
    (D : Y →ₗ[ℂ] H) (hD : ∀ k ∈ maxCpt G, ∀ y y' : Y, (y' : H) = π k y → D y' = π k (D y))
    (hS : IsKStable G π S) {x : H} (hx : x ∈ S') (hxY : x ∈ Y) : D ⟨x, hxY⟩ ∈ Y := by
  obtain ⟨T, rfl, hT⟩ := h
  obtain ⟨s, hs, rfl⟩ := hx
  have hTY : ∀ w ∈ S, T w ∈ Y := fun w hw =>
    hSY (le_sSup (show S.map T ∈ isoGens G π S from ⟨T, rfl, hT⟩) ⟨w, hw, rfl⟩)
  let f : S →ₗ[ℂ] H := D ∘ₗ (T.domRestrict S).codRestrict Y (fun w => hTY w w.2)
  obtain ⟨T', hT'⟩ := LinearMap.exists_extend f
  have hval : ∀ w (hw : w ∈ S), T' w = D ⟨T w, hTY w hw⟩ := fun w hw =>
    LinearMap.congr_fun hT' ⟨w, hw⟩
  have hcomm : ∀ k ∈ maxCpt G, ∀ w ∈ S, T' (π k w) = π k (T' w) := by
    intro k hk w hw
    rw [hval _ (hS k hk w hw), hval w hw]
    exact hD k hk _ _ (hT k hk w hw)
  have hmem : S.map T' ∈ isoGens G π S := ⟨T', rfl, hcomm⟩
  have : T' s ∈ Y := hSY (le_sSup hmem ⟨s, hs, rfl⟩)
  rwa [hval s hs] at this

theorem exists_isotypic_sum : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hA : IsAdmOn G π) {v : H} (hv : IsKFinOn G π v), ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ IsKStable G π Y ∧ ∀ D : Y →ₗ[ℂ] H, (∀ k ∈ maxCpt G, ∀ y y' : Y, (y' : H) = π k y → D y' = π k (D y)) → ∀ y, D y ∈ Y := by
  intro n G H _ _ _ π hG hA v hv
  obtain ⟨S, hfin, hvS, hS⟩ := hv
  obtain ⟨F, hF, hI, hle⟩ := exists_irr_family hG hA _ S hfin rfl hS
  let iso : Submodule ℂ H → Submodule ℂ H := fun I => sSup (isoGens G π I)
  have hisoK : ∀ I ∈ F, IsKStable G π (iso I) := fun I hIF =>
    sSup_kstable fun S' h => isoGens_kstable (hI I hIF).2.1 h
  have hisoF : ∀ I ∈ F, FiniteDimensional ℂ (iso I) := fun I hIF =>
    hA.2.2.2 I (hI I hIF).1 (hI I hIF).2.1 (hI I hIF).2.2
  have hYle : ∀ I ∈ F, iso I ≤ sSup (iso '' F) := fun I hIF => le_sSup ⟨I, hIF, rfl⟩
  refine ⟨sSup (iso '' F), ?_, ?_, ?_, ?_⟩
  · rw [sSup_eq_iSup']
    haveI : Finite ↥(iso '' F) := (hF.image iso).to_subtype
    haveI : ∀ a : ↥(iso '' F), FiniteDimensional ℂ (a : Submodule ℂ H) := by
      rintro ⟨_, I, hIF, rfl⟩
      exact hisoF I hIF
    exact Submodule.finiteDimensional_iSup _
  · exact (sSup_le fun I hIF => (le_sSup_isoGens I).trans (hYle I hIF)) (hle hvS)
  · refine sSup_kstable ?_
    rintro _ ⟨I, hIF, rfl⟩
    exact hisoK I hIF
  · intro D hD y
    have hP : sSup (iso '' F) ≤ ((sSup (iso '' F)).comap D).map (sSup (iso '' F)).subtype := by
      refine sSup_le ?_
      rintro _ ⟨I, hIF, rfl⟩
      refine sSup_le fun S' hS' x hx => ?_
      have hxY : x ∈ sSup (iso '' F) := hYle I hIF (le_sSup hS' hx)
      exact ⟨⟨x, hxY⟩, map_mem_of_gen (hYle I hIF) hS' D hD (hI I hIF).2.1 hx hxY, rfl⟩
    obtain ⟨y', hy', he⟩ := hP y.2
    have hyy : y' = y := Subtype.ext he
    subst hyy
    exact hy'

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Isotypic

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RpowNegLeOfDichotomy
section -- merged from Development.AutomorphicSpectrum.Proofs.HermitianForms.OneAddHsInvPowLintegralLtTop
open MeasureTheory Matrix Finset PI.UpqRep
open scoped InnerProductSpace ENNReal ComplexOrder

namespace GlobalTheory.CompanionTheory.HolPQ

theorem muG_hs_ball_le (n : ℕ) (ε : Fin n → Bool) :
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      muG ε {g | hs (umat g) ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (2 * n ^ 2)) :=
  Formalism.REAL.volume_growth n ε

theorem continuous_hs_umat {n : ℕ} (ε : Fin n → Bool) :
    Continuous fun g : UJ ε => hs (umat g) := by
  have hc : Continuous (coeMatrixAlt ε) := continuous_coeMatrix ε
  unfold hs
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (Continuous.matrix_elem hc i j).norm.pow 2

theorem lintegral_one_add_inv_pow_lt_top {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (h : X → ℝ) (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x) (d : ℕ) (C : ℝ)
    (hC : ∀ k : ℕ, μ {x | h x ≤ (4 : ℝ) ^ k} ≤ ENNReal.ofReal (C * ((4 : ℝ) ^ k) ^ d))
    (s : ℕ) (hs' : d + 1 ≤ s) :
    ∫⁻ x, ENNReal.ofReal (((1 + h x)⁻¹) ^ s) ∂μ < ⊤ := by
  set c : ℕ → ℝ := fun k => (4 : ℝ) ^ s * (((4 : ℝ) ^ k)⁻¹) ^ s with hc
  have hc0 : ∀ k, 0 ≤ c k := fun k => by simp only [hc]; positivity
  set A : ℕ → Set X := fun k => {x | h x ≤ (4 : ℝ) ^ k} with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k => measurableSet_le hm measurable_const
  have point : ∀ x, ENNReal.ofReal (((1 + h x)⁻¹) ^ s) ≤
      ∑' k, (A k).indicator (fun _ => ENNReal.ofReal (c k)) x := by
    intro x
    have hex : ∃ k : ℕ, h x ≤ (4 : ℝ) ^ k := by
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (h x) (by norm_num : (1 : ℝ) < 4)
      exact ⟨k, hk.le⟩
    classical
    set k := Nat.find hex with hk
    have hxk : x ∈ A k := Nat.find_spec hex
    refine le_trans ?_ (ENNReal.le_tsum k)
    rw [Set.indicator_of_mem hxk]
    apply ENNReal.ofReal_le_ofReal
    have h4 : (4 : ℝ) ^ k ≤ 4 * (1 + h x) := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0]; have := h0 x; norm_num; linarith
      · have hmin : ¬ h x ≤ (4 : ℝ) ^ (k - 1) := Nat.find_min hex (by omega)
        have e : (4 : ℝ) ^ k = 4 * 4 ^ (k - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [e]; push Not at hmin; linarith
    have hpos : 0 < 1 + h x := by have := h0 x; linarith
    have h5 : (1 + h x)⁻¹ ≤ 4 * ((4 : ℝ) ^ k)⁻¹ := by
      rw [inv_le_comm₀ hpos (by positivity), mul_inv, inv_inv]
      have : (0 : ℝ) < 4 ^ k := by positivity
      nlinarith
    calc ((1 + h x)⁻¹) ^ s ≤ (4 * ((4 : ℝ) ^ k)⁻¹) ^ s :=
          pow_le_pow_left₀ (by positivity) h5 s
      _ = c k := by simp only [hc]; rw [mul_pow]
  set C' : ℝ := max C 0 with hC'
  have hterm : ∀ k, ENNReal.ofReal (c k) * μ (A k) ≤
      ENNReal.ofReal ((4 : ℝ) ^ s * C' * ((4 : ℝ)⁻¹) ^ k) := by
    intro k
    have h1 : μ (A k) ≤ ENNReal.ofReal (C' * ((4 : ℝ) ^ k) ^ d) :=
      (hC k).trans (ENNReal.ofReal_le_ofReal (by
        gcongr; exact le_max_left _ _))
    calc ENNReal.ofReal (c k) * μ (A k)
        ≤ ENNReal.ofReal (c k) * ENNReal.ofReal (C' * ((4 : ℝ) ^ k) ^ d) := by gcongr
      _ = ENNReal.ofReal (c k * (C' * ((4 : ℝ) ^ k) ^ d)) :=
          (ENNReal.ofReal_mul (hc0 k)).symm
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hC0 : 0 ≤ C' := le_max_right _ _
          have hq : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
          have key : (((4 : ℝ) ^ k)⁻¹) ^ s * ((4 : ℝ) ^ k) ^ d ≤ ((4 : ℝ)⁻¹) ^ k := by
            obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs'
            have e : (((4 : ℝ) ^ k)⁻¹) ^ (d + 1 + t) * ((4 : ℝ) ^ k) ^ d =
                ((4 : ℝ) ^ k)⁻¹ * (((4 : ℝ) ^ k)⁻¹) ^ t := by
              have : ((4 : ℝ) ^ k) ≠ 0 := by positivity
              rw [pow_add, pow_succ, inv_pow]
              field_simp
            have h7 : ((4 : ℝ)⁻¹) ^ k = ((4 : ℝ) ^ k)⁻¹ := inv_pow _ _
            have h8 : (((4 : ℝ) ^ k)⁻¹) ^ t ≤ 1 :=
              pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hq)
            have h6 : (0 : ℝ) < ((4 : ℝ) ^ k)⁻¹ := by positivity
            rw [e, h7]
            exact mul_le_of_le_one_right h6.le h8
          simp only [hc]
          calc (4 : ℝ) ^ s * (((4 : ℝ) ^ k)⁻¹) ^ s * (C' * ((4 : ℝ) ^ k) ^ d)
              = (4 : ℝ) ^ s * C' * ((((4 : ℝ) ^ k)⁻¹) ^ s * ((4 : ℝ) ^ k) ^ d) := by ring
            _ ≤ _ := by gcongr
  have hsum : Summable fun k : ℕ => (4 : ℝ) ^ s * C' * ((4 : ℝ)⁻¹) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc ∫⁻ x, ENNReal.ofReal (((1 + h x)⁻¹) ^ s) ∂μ
      ≤ ∫⁻ x, ∑' k, (A k).indicator (fun _ => ENNReal.ofReal (c k)) x ∂μ :=
        lintegral_mono point
    _ = ∑' k, ∫⁻ x, (A k).indicator (fun _ => ENNReal.ofReal (c k)) x ∂μ :=
        lintegral_tsum fun k => (measurable_const.indicator (hAm k)).aemeasurable
    _ = ∑' k, ENNReal.ofReal (c k) * μ (A k) := by
        congr 1; funext k
        rw [lintegral_indicator (hAm k), setLIntegral_const]
    _ ≤ ∑' k, ENNReal.ofReal ((4 : ℝ) ^ s * C' * ((4 : ℝ)⁻¹) ^ k) :=
        ENNReal.tsum_le_tsum hterm
    _ < ⊤ := hsum.tsum_ofReal_lt_top

theorem one_add_hs_inv_pow_lintegral_lt_top : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
    ∫⁻ g, ENNReal.ofReal (((1 + hs (umat g))⁻¹) ^ s) ∂(muG ε) < ⊤ := by
  intro n ε
  obtain ⟨C, hC⟩ := muG_hs_ball_le n ε
  refine ⟨n ^ 2 + 1, fun s hs' => ?_⟩
  refine lintegral_one_add_inv_pow_lt_top (muG ε) (fun g => hs (umat g))
    (continuous_hs_umat ε).measurable (fun g => ?_) (n ^ 2) C (fun k => ?_) s hs'
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  · have e : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h1 := hC ((2 : ℝ) ^ k) (one_le_pow₀ (by norm_num))
    have e2 : ((2 : ℝ) ^ k) ^ (2 * n ^ 2) = ((4 : ℝ) ^ k) ^ n ^ 2 := by
      rw [e]; exact pow_mul _ 2 (n ^ 2)
    rw [e2, ← e] at h1
    exact h1

end GlobalTheory.CompanionTheory.HolPQ
end

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Volume

open MeasureTheory

theorem wt_eq_hs {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : wt M = Formalism.REAL.hs M := by
  have key : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
    intro z
    have h : star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [h, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  unfold wt Formalism.REAL.hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, key]
  exact Finset.sum_comm

theorem one_le_hs_of_inUJ {n : ℕ} (hn : 0 < n) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ)
    (h : Formalism.REAL.inUJ ε g) : 1 ≤ Formalism.REAL.hs g := by
  set a : Fin n := ⟨0, hn⟩ with ha
  have hs1 : ∀ k : Fin n, ‖(if ε k = true then (1 : ℂ) else -1)‖ = 1 := by
    intro k; split_ifs <;> simp
  have e : ∑ k, star (g k a) * (if ε k = true then (1 : ℂ) else -1) * g k a =
      (if ε a = true then (1 : ℂ) else -1) := by
    have h2 := congrFun (congrFun h a) a
    simpa [Formalism.REAL.Jm, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal_apply] using h2
  have h3 : (1 : ℝ) ≤ ∑ k, ‖g k a‖ ^ 2 := by
    calc (1 : ℝ) = ‖∑ k, star (g k a) * (if ε k = true then (1 : ℂ) else -1) * g k a‖ := by
          rw [e, hs1]
      _ ≤ ∑ k, ‖star (g k a) * (if ε k = true then (1 : ℂ) else -1) * g k a‖ := norm_sum_le _ _
      _ = ∑ k, ‖g k a‖ ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, norm_mul, hs1, norm_star]; ring
  refine h3.trans ?_
  unfold Formalism.REAL.hs
  refine Finset.sum_le_sum fun k _ => ?_
  exact Finset.single_le_sum (f := fun j => ‖g k j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ a)

theorem rpow_neg_le_of_dichotomy {w b' : ℝ} {s : ℕ} (hw : w = 0 ∨ 1 ≤ w) (hb : (s : ℝ) ≤ b') :
    w ^ (-b') ≤ ((2 : ℝ) ^ b' + 1) * ((1 + w)⁻¹) ^ s := by
  have hb0 : 0 ≤ b' := (Nat.cast_nonneg s).trans hb
  have h2 : (0 : ℝ) < (2 : ℝ) ^ b' := Real.rpow_pos_of_pos (by norm_num) _
  rcases hw with rfl | hw
  · have h1 : (0 : ℝ) ^ (-b') ≤ 1 := Real.zero_rpow_le_one _
    simp only [add_zero, inv_one, one_pow, mul_one]
    linarith
  · have hw0 : 0 < w := by linarith
    have hu0 : 0 < (1 + w)⁻¹ := by positivity
    have hu1 : (1 + w)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have hwi : w⁻¹ ≤ 2 * (1 + w)⁻¹ := by
      rw [inv_le_comm₀ hw0 (by positivity), mul_inv, inv_inv]
      linarith
    calc w ^ (-b') = (w⁻¹) ^ b' := by rw [Real.rpow_neg hw0.le, Real.inv_rpow hw0.le]
      _ ≤ (2 * (1 + w)⁻¹) ^ b' := Real.rpow_le_rpow (by positivity) hwi hb0
      _ = (2 : ℝ) ^ b' * ((1 + w)⁻¹) ^ b' := Real.mul_rpow (by norm_num) hu0.le
      _ ≤ (2 : ℝ) ^ b' * ((1 + w)⁻¹) ^ (s : ℝ) := by
          gcongr ?_ * ?_
          exact Real.rpow_le_rpow_of_exponent_ge hu0 hu1 hb
      _ = (2 : ℝ) ^ b' * ((1 + w)⁻¹) ^ s := by rw [Real.rpow_natCast]
      _ ≤ _ := by
          have : 0 ≤ ((1 + w)⁻¹) ^ s := by positivity
          nlinarith

theorem integrable_wt_rpow_neg {n : ℕ} (ε : Fin n → Bool) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ b' : ℝ, b ≤ b' →
      MeasureTheory.Integrable (fun g : UJ ε => wt (uMat g) ^ (-b')) (Formalism.REAL.muG ε).inv := by
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.HolPQ.one_add_hs_inv_pow_lintegral_lt_top n ε
  have hfin : ∫⁻ g : UJ ε, ENNReal.ofReal (((1 + Formalism.REAL.hs (uMat g))⁻¹) ^ s) ∂(Formalism.REAL.muG ε) < ⊤ :=
    hs s le_rfl
  refine ⟨s, Nat.cast_nonneg s, fun b' hb' => ?_⟩
  have hinv : (Formalism.REAL.muG ε).inv = Formalism.REAL.muG ε := Formalism.REAL.invInvariant n ε
  rw [hinv]
  have hc : Continuous fun g : UJ ε => Formalism.REAL.hs (uMat g) := GlobalTheory.CompanionTheory.HolPQ.continuous_hs_umat ε
  have hnn : ∀ g : UJ ε, 0 ≤ Formalism.REAL.hs (uMat g) := fun g =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hI : Integrable (fun g : UJ ε => ((1 + Formalism.REAL.hs (uMat g))⁻¹) ^ s) (Formalism.REAL.muG ε) := by
    refine ⟨((measurable_const.add hc.measurable).inv.pow_const s).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun g => by
      have := hnn g
      positivity)]
    exact hfin
  have hw : ∀ g : UJ ε, wt (uMat g) = Formalism.REAL.hs (uMat g) := fun g => wt_eq_hs _
  have hmeas : Measurable fun g : UJ ε => wt (uMat g) ^ (-b') := by
    simp only [hw]
    exact hc.measurable.pow_const _
  refine (hI.const_mul ((2 : ℝ) ^ b' + 1)).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  have hdich : Formalism.REAL.hs (uMat g) = 0 ∨ 1 ≤ Formalism.REAL.hs (uMat g) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · left; simp [Formalism.REAL.hs]
    · right; exact one_le_hs_of_inUJ hn ε _ g.2
  rw [hw, Real.norm_of_nonneg (Real.rpow_nonneg (hnn g) _)]
  exact rpow_neg_le_of_dichotomy hdich hb'

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Volume

end
end
