module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2MatrixCoeffBoundedHolomorphicFormEqExtremalVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDetBlocks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandInvariantsActByScalarsHighestWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFormOfTwistedNormCharpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalityPreservedInClosure

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantMultilinearOfMatrixCoeffEqUnita
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantMultilinearOfMatrixCoeffEqUnita
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem eq_zero_of_mem_closure_span_of_inner_eq_zero {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] {s : Set K} {z : K} (hz : z ∈ closure (Submodule.span ℂ s : Set K))
    (h : ∀ w ∈ s, ⟪w, z⟫_ℂ = 0) : z = 0 := by
  have h1 : ∀ w ∈ Submodule.span ℂ s, ⟪w, z⟫_ℂ = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
  have h2 : closure (Submodule.span ℂ s : Set K) ⊆ {w | ⟪w, z⟫_ℂ = 0} :=
    closure_minimal h1 (isClosed_eq (by fun_prop) (by fun_prop))
  exact inner_self_eq_zero.1 (h2 hz)

theorem exists_vector_of_inner_eq_prod {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type}
    [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)]
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {A : ι → Type} (e : ∀ τ, A τ → H τ) (f : (∀ τ, A τ) → K) (c : ℝ)
    (hd : ∀ τ, Dense (Submodule.span ℂ (Set.range (e τ)) : Set (H τ)))
    (hf : ∀ a b, ⟪f a, f b⟫_ℂ = (c : ℂ) * ∏ τ, ⟪e τ (a τ), e τ (b τ)⟫_ℂ) (y : ∀ τ, H τ) :
    ∃ z ∈ closure (Submodule.span ℂ (Set.range f) : Set K),
      (∀ a, ⟪f a, z⟫_ℂ = (c : ℂ) * ∏ τ, ⟪e τ (a τ), y τ⟫_ℂ) ∧
        ⟪z, z⟫_ℂ = (c : ℂ) * ∏ τ, ⟪y τ, y τ⟫_ℂ := by
  classical
  let B : (∀ τ, H τ) → (∀ τ, H τ) → ℂ := fun p q => (c : ℂ) * ∏ τ, ⟪p τ, q τ⟫_ℂ
  have hBc : Continuous fun p : (∀ τ, H τ) × (∀ τ, H τ) => B p.1 p.2 := by
    simp only [B]; fun_prop
  let lin : (∀ τ, A τ →₀ ℂ) → (∀ τ, H τ) := fun x τ => Finsupp.linearCombination ℂ (e τ) (x τ)
  let P : (∀ τ, A τ →₀ ℂ) → K := fun x =>
    ∑ a ∈ Fintype.piFinset (fun τ => (x τ).support), (∏ τ, x τ (a τ)) • f a
  have hPmem : ∀ x, P x ∈ Submodule.span ℂ (Set.range f) := fun x =>
    Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h1 : ∀ x (z : K) (q : ∀ τ, H τ), (∀ a, ⟪f a, z⟫_ℂ = B (fun τ => e τ (a τ)) q) →
      ⟪P x, z⟫_ℂ = B (lin x) q := by
    intro x z q hz
    simp only [P, B, lin, sum_inner, inner_smul_left, hz, Finsupp.linearCombination_apply, Finsupp.sum]
    rw [Finset.prod_univ_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.prod_mul_distrib, map_prod]
    ring
  have hconj : ∀ p q, (starRingEnd ℂ) (B p q) = B q p := by
    intro p q
    simp only [B, map_mul, map_prod, inner_conj_symm, Complex.conj_ofReal]
  have h2 : ∀ x a, ⟪f a, P x⟫_ℂ = B (fun τ => e τ (a τ)) (lin x) := by
    intro x a
    rw [← inner_conj_symm, h1 x (f a) (fun τ => e τ (a τ)) (fun b => hf b a), hconj]
  have h3 : ∀ x x', ⟪P x, P x'⟫_ℂ = B (lin x) (lin x') := fun x x' => h1 x _ _ (h2 x')
  have hdl : DenseRange lin := by
    have : DenseRange (Pi.map fun τ => fun x : A τ →₀ ℂ => Finsupp.linearCombination ℂ (e τ) x) := by
      refine DenseRange.piMap fun τ => ?_
      have := hd τ
      rw [← Finsupp.range_linearCombination, LinearMap.coe_range] at this
      exact this
    exact this
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (hdl y)
  choose x hx using hu
  have hlim' : Filter.Tendsto (fun n => lin (x n)) Filter.atTop (nhds y) := by
    simpa only [hx] using hlim
  have hcau : CauchySeq fun n => P (x n) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    let G : (∀ τ, H τ) × (∀ τ, H τ) → ℝ := fun p =>
      Real.sqrt (B p.1 p.1 - B p.1 p.2 - B p.2 p.1 + B p.2 p.2).re
    have hG : Continuous G := by
      simp only [G, B]; fun_prop
    have hG0 : G (y, y) = 0 := by simp [G]
    have ht : Filter.Tendsto (fun n : ℕ × ℕ => (lin (x n.1), lin (x n.2))) Filter.atTop (nhds (y, y)) := by
      rw [← Filter.prod_atTop_atTop_eq]
      exact (hlim'.comp Filter.tendsto_fst).prodMk_nhds (hlim'.comp Filter.tendsto_snd)
    have := (hG.tendsto (y, y)).comp ht
    rw [hG0] at this
    refine this.congr fun n => ?_
    simp only [Function.comp, G]
    rw [dist_eq_norm, @norm_eq_sqrt_re_inner ℂ, inner_sub_sub_self, h3, h3, h3, h3]
    rfl
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcau
  have h4 : ∀ a, ⟪f a, z⟫_ℂ = B (fun τ => e τ (a τ)) y := by
    intro a
    have t1 : Filter.Tendsto (fun n => ⟪f a, P (x n)⟫_ℂ) Filter.atTop (nhds ⟪f a, z⟫_ℂ) :=
      Filter.Tendsto.inner tendsto_const_nhds hz
    have t2 := (hBc.tendsto (fun τ => e τ (a τ), y)).comp (tendsto_const_nhds.prodMk_nhds hlim')
    refine tendsto_nhds_unique t1 (t2.congr fun n => ?_)
    rw [h2]; rfl
  refine ⟨z, mem_closure_of_tendsto hz (Filter.Eventually.of_forall fun n => hPmem _), h4, ?_⟩
  have t1 : Filter.Tendsto (fun n => ⟪P (x n), z⟫_ℂ) Filter.atTop (nhds ⟪z, z⟫_ℂ) :=
    Filter.Tendsto.inner hz tendsto_const_nhds
  have t2 := (hBc.tendsto (y, y)).comp (hlim'.prodMk_nhds tendsto_const_nhds)
  refine tendsto_nhds_unique t1 (t2.congr fun n => ?_)
  rw [h1 _ _ _ h4]; rfl

theorem exists_continuousMultilinearMap_of_inner_eq_prod {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type}
    [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)]
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {A : ι → Type} (e : ∀ τ, A τ → H τ) (f : (∀ τ, A τ) → K) (c : ℝ)
    (hd : ∀ τ, Dense (Submodule.span ℂ (Set.range (e τ)) : Set (H τ)))
    (hf : ∀ a b, ⟪f a, f b⟫_ℂ = (c : ℂ) * ∏ τ, ⟪e τ (a τ), e τ (b τ)⟫_ℂ) :
    ∃ Φ : ContinuousMultilinearMap ℂ H K, ∀ y, Φ y ∈ closure (Submodule.span ℂ (Set.range f) : Set K) ∧
      ∀ a, ⟪f a, Φ y⟫_ℂ = (c : ℂ) * ∏ τ, ⟪e τ (a τ), y τ⟫_ℂ := by
  choose F hF1 hF2 hF3 using exists_vector_of_inner_eq_prod e f c hd hf
  let L : (∀ τ, A τ) → MultilinearMap (RingHom.id ℂ) H ℂ := fun a =>
    (c : ℂ) • (MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap fun τ => innerₛₗ ℂ (e τ (a τ))
  have hL : ∀ a y, ⟪f a, F y⟫_ℂ = L a y := by
    intro a y
    rw [hF2]; simp [L]
  have hmem : ∀ y, F y ∈ (Submodule.span ℂ (Set.range f)).topologicalClosure := hF1
  let M : MultilinearMap (RingHom.id ℂ) H K :=
    { toFun := F
      map_update_add' := by
        intro _ m i p q
        rw [← sub_eq_zero]
        refine eq_zero_of_mem_closure_span_of_inner_eq_zero (s := Set.range f)
          (Submodule.sub_mem _ (hmem _) (Submodule.add_mem _ (hmem _) (hmem _))) ?_
        rintro _ ⟨a, rfl⟩
        rw [inner_sub_right, inner_add_right, hL, hL, hL, MultilinearMap.map_update_add, sub_self]
      map_update_smul' := by
        intro _ m i r p
        rw [← sub_eq_zero]
        refine eq_zero_of_mem_closure_span_of_inner_eq_zero (s := Set.range f)
          (Submodule.sub_mem _ (hmem _) (Submodule.smul_mem _ _ (hmem _))) ?_
        rintro _ ⟨a, rfl⟩
        rw [inner_sub_right, inner_smul_right, hL, hL, MultilinearMap.map_update_smul, smul_eq_mul, sub_self] }
  refine ⟨M.mkContinuous (Real.sqrt |c|) fun y => ?_, fun y => ⟨hF1 y, hF2 y⟩⟩
  change ‖F y‖ ≤ _
  have h := congrArg norm (hF3 y)
  simp only [inner_self_eq_norm_sq_to_K, norm_mul, norm_prod, norm_pow, Complex.coe_algebraMap,
    Complex.norm_real, norm_norm, Real.norm_eq_abs, Finset.prod_pow] at h
  refine le_of_eq ?_
  refine (pow_left_inj₀ (n := 2) (by positivity) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt (abs_nonneg c)]
  simpa using h


set_option maxHeartbeats 800000 in
theorem exists_equivariant_multilinear_of_matrixCoeff_eq :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (H : ι → Type) [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)] [∀ τ, CompleteSpace (H τ)] (σ : ∀ τ, Mt n → (H τ →L[ℂ] H τ)) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : (ι → Mt n) → (K →L[ℂ] K)) (v : ∀ τ, H τ) (k : K), (∀ τ, (Hm τ).det ≠ 0 ∧ IsURepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ) ∧ IsIrredOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ) ∧ ‖v τ‖ = 1) → ρ 1 = 1 → (∀ u ∈ UG Hm, ∀ u' ∈ UG Hm, ρ (u * u') = ρ u * ρ u') → (∀ u ∈ UG Hm, ∀ y, ‖ρ u y‖ = ‖y‖) → (∀ u ∈ UG Hm, ⟪k, ρ u k⟫_ℂ = ((‖k‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ) → ∃ Φ : ContinuousMultilinearMap ℂ H K, Φ v = k ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (Hm τ), ∀ y, Φ (Function.update y τ (σ τ g (y τ))) = ρ (Pi.mulSingle τ g) (Φ y)) ∧ ∀ y, Φ y ∈ closure (Submodule.span ℂ {z | ∃ u ∈ UG Hm, z = ρ u k} : Set K) := by
  intro n ι _ _ Hm H _ _ _ σ K _ _ _ ρ v k hσ hρ1 hρm hρn hco
  have hone : ∀ τ, (1 : Mt n) ∈ Formalism.QuantumDeterminants.UH (Hm τ) := fun τ => by simp [Formalism.QuantumDeterminants.UH]
  have hmul : ∀ τ, ∀ a ∈ Formalism.QuantumDeterminants.UH (Hm τ), ∀ b ∈ Formalism.QuantumDeterminants.UH (Hm τ), a * b ∈ Formalism.QuantumDeterminants.UH (Hm τ) := by
    intro τ a ha b hb
    simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at ha hb ⊢
    rw [conjTranspose_mul]
    calc bᴴ * aᴴ * Hm τ * (a * b) = bᴴ * (aᴴ * Hm τ * a) * b := by simp only [Matrix.mul_assoc]
      _ = Hm τ := by rw [ha, hb]
  have hinv : ∀ τ, ∀ a ∈ Formalism.QuantumDeterminants.UH (Hm τ), ∃ b ∈ Formalism.QuantumDeterminants.UH (Hm τ), a * b = 1 := by
    intro τ a ha
    simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at ha ⊢
    have hd : IsUnit a.det := by
      have := congrArg Matrix.det ha
      rw [det_mul, det_mul] at this
      refine isUnit_iff_ne_zero.2 fun h => (hσ τ).1 ?_
      rw [← this, h, mul_zero]
    refine ⟨a⁻¹, ?_, Matrix.mul_nonsing_inv a hd⟩
    calc a⁻¹ᴴ * Hm τ * a⁻¹ = a⁻¹ᴴ * (aᴴ * Hm τ * a) * a⁻¹ := by rw [ha]
      _ = (a * a⁻¹)ᴴ * Hm τ * (a * a⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Hm τ := by rw [Matrix.mul_nonsing_inv a hd]; simp
  have hσ1 : ∀ τ, σ τ 1 = 1 := fun τ => (hσ τ).2.1.1.1
  have hσm : ∀ τ, ∀ a ∈ Formalism.QuantumDeterminants.UH (Hm τ), ∀ b ∈ Formalism.QuantumDeterminants.UH (Hm τ), σ τ (a * b) = σ τ a * σ τ b :=
    fun τ => (hσ τ).2.1.1.2
  have hσi : ∀ τ, ∀ a ∈ Formalism.QuantumDeterminants.UH (Hm τ), ∀ p q, ⟪σ τ a p, σ τ a q⟫_ℂ = ⟪p, q⟫_ℂ := fun τ a ha =>
    (LinearMap.norm_map_iff_inner_map_map (σ τ a)).1 ((hσ τ).2.1.2.1 a ha)
  have hρi : ∀ a ∈ UG Hm, ∀ p q, ⟪ρ a p, ρ a q⟫_ℂ = ⟪p, q⟫_ℂ := fun a ha =>
    (LinearMap.norm_map_iff_inner_map_map (ρ a)).1 (hρn a ha)

  have hdiv : ∀ a ∈ UG Hm, ∀ b ∈ UG Hm, ∃ d ∈ UG Hm, a * d = b := by
    intro a ha b hb
    choose a' h1 h2 using fun τ => hinv τ (a τ) (ha τ)
    refine ⟨a' * b, fun τ => hmul τ _ (h1 τ) _ (hb τ), funext fun τ => ?_⟩
    simp only [Pi.mul_apply]
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  let e : ∀ τ, Formalism.QuantumDeterminants.UH (Hm τ) → H τ := fun τ g => σ τ g (v τ)
  let f : (∀ τ, Formalism.QuantumDeterminants.UH (Hm τ)) → K := fun a => ρ (fun τ => a τ) k
  have hrange : Set.range f = {z | ∃ u ∈ UG Hm, z = ρ u k} := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨fun τ => a τ, fun τ => (a τ).2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun τ => ⟨u τ, hu τ⟩, rfl⟩
  have hd : ∀ τ, Dense (Submodule.span ℂ (Set.range (e τ)) : Set (H τ)) := by
    intro τ
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    have hst : ∀ g ∈ Formalism.QuantumDeterminants.UH (Hm τ), ∀ w ∈ (Submodule.span ℂ (Set.range (e τ))).topologicalClosure,
        σ τ g w ∈ (Submodule.span ℂ (Set.range (e τ))).topologicalClosure := by
      intro g hg w hw
      refine map_mem_closure (σ τ g).continuous hw fun p hp => ?_
      have : Submodule.span ℂ (Set.range (e τ)) ≤
          (Submodule.span ℂ (Set.range (e τ))).comap (σ τ g).toLinearMap := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        refine Submodule.subset_span ⟨⟨g * b, hmul τ _ hg _ b.2⟩, ?_⟩
        simp only [e]
        rw [hσm τ _ hg _ b.2]; rfl
      exact this hp
    refine ((hσ τ).2.2.1 _ (Submodule.isClosed_topologicalClosure _) hst).resolve_left fun h => ?_
    have hv : v τ ∈ (Submodule.span ℂ (Set.range (e τ))).topologicalClosure :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨1, hone τ⟩, by simp [e, hσ1]⟩)
    rw [h, Submodule.mem_bot] at hv
    have := (hσ τ).2.2.2
    rw [hv, norm_zero] at this
    exact zero_ne_one this
  have hf : ∀ a b, ⟪f a, f b⟫_ℂ = ((‖k‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪e τ (a τ), e τ (b τ)⟫_ℂ := by
    intro a b
    have ha : (fun τ => (a τ : Mt n)) ∈ UG Hm := fun τ => (a τ).2
    obtain ⟨d, hdm, hd⟩ := hdiv _ ha (fun τ => (b τ : Mt n)) (fun τ => (b τ).2)
    simp only [f, e]
    rw [← hd, hρm _ ha _ hdm, ContinuousLinearMap.mul_apply, hρi _ ha, hco d hdm]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    have : (b τ : Mt n) = a τ * d τ := (congrFun hd τ).symm
    rw [this, hσm τ _ (a τ).2 _ (hdm τ), ContinuousLinearMap.mul_apply, hσi τ _ (a τ).2]
  obtain ⟨Φ, hΦ⟩ := exists_continuousMultilinearMap_of_inner_eq_prod e f _ hd hf
  have hmem : ∀ y, Φ y ∈ (Submodule.span ℂ (Set.range f)).topologicalClosure := fun y => (hΦ y).1
  have hk : f (fun τ => ⟨1, hone τ⟩) = k := by
    change ρ 1 k = k
    rw [hρ1]; rfl
  refine ⟨Φ, ?_, fun τ g hg y => ?_, fun y => hrange ▸ (hΦ y).1⟩
  · rw [← sub_eq_zero]
    refine eq_zero_of_mem_closure_span_of_inner_eq_zero (s := Set.range f)
      (Submodule.sub_mem _ (hmem _) (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, hk⟩))) ?_
    rintro _ ⟨a, rfl⟩
    rw [inner_sub_right, (hΦ v).2, ← hk, hf, hk]
    simp [e, hσ1]
  · have hs : (Pi.mulSingle τ g : ι → Mt n) ∈ UG Hm := by
      intro τ'
      by_cases h : τ' = τ
      · subst h; simpa using hg
      · rw [Pi.mulSingle_eq_of_ne h]; exact hone τ'
    have hst : ρ (Pi.mulSingle τ g) (Φ y) ∈ (Submodule.span ℂ (Set.range f)).topologicalClosure := by
      refine map_mem_closure (ρ _).continuous (hmem y) fun p hp => ?_
      have : Submodule.span ℂ (Set.range f) ≤
          (Submodule.span ℂ (Set.range f)).comap (ρ (Pi.mulSingle τ g)).toLinearMap := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        have hb : (fun τ => (b τ : Mt n)) ∈ UG Hm := fun τ => (b τ).2
        refine Submodule.subset_span ?_
        rw [hrange]
        have hsb : ((Pi.mulSingle τ g : ι → Mt n) * fun τ => (b τ : Mt n)) ∈ UG Hm := by
          intro τ'
          rw [Pi.mul_apply]
          exact hmul τ' _ (hs τ') _ (hb τ')
        refine ⟨_, hsb, ?_⟩
        rw [hρm _ hs _ hb]; rfl
      exact this hp
    rw [← sub_eq_zero]
    refine eq_zero_of_mem_closure_span_of_inner_eq_zero (s := Set.range f)
      (Submodule.sub_mem _ (hmem _) hst) ?_
    rintro _ ⟨a, rfl⟩
    have ha : (fun τ => (a τ : Mt n)) ∈ UG Hm := fun τ => (a τ).2
    obtain ⟨d, hdm, hd⟩ := hdiv _ hs _ ha
    have h1 : f a = ρ (Pi.mulSingle τ g) (f fun τ => ⟨d τ, hdm τ⟩) := by
      simp only [f]
      rw [← hd, hρm _ hs _ hdm]; rfl
    rw [inner_sub_right, (hΦ _).2, h1, hρi _ hs, (hΦ _).2, sub_eq_zero]
    congr 1
    refine Finset.prod_congr rfl fun τ' _ => ?_
    have h2 : (a τ' : Mt n) = (Pi.mulSingle τ g : ι → Mt n) τ' * d τ' := (congrFun hd τ').symm
    simp only [e]
    rw [h2]
    by_cases h : τ' = τ
    · subst h
      rw [Pi.mulSingle_eq_same, Function.update_self, hσm _ _ hg _ (hdm _), ContinuousLinearMap.mul_apply, hσi _ _ hg]
    · rw [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h, Matrix.one_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantMultilinearOfMatrixCoeffEqUnitaStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_multilinear_of_matrixCoeff_eq_unitaryProduct : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (H : ι → Type) [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)] [∀ τ, CompleteSpace (H τ)] (σ : ∀ τ, Mt n → (H τ →L[ℂ] H τ)) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : (ι → Mt n) → (K →L[ℂ] K)) (v : ∀ τ, H τ) (k : K), (∀ τ, (Hm τ).det ≠ 0 ∧ IsURepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ) ∧ IsIrredOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ) ∧ ‖v τ‖ = 1) → ρ 1 = 1 → (∀ u ∈ UG Hm, ∀ u' ∈ UG Hm, ρ (u * u') = ρ u * ρ u') → (∀ u ∈ UG Hm, ∀ y, ‖ρ u y‖ = ‖y‖) → (∀ u ∈ UG Hm, ⟪k, ρ u k⟫_ℂ = ((‖k‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ) → ∃ Φ : ContinuousMultilinearMap ℂ H K, Φ v = k ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (Hm τ), ∀ y, Φ (Function.update y τ (σ τ g (y τ))) = ρ (Pi.mulSingle τ g) (Φ y)) ∧ ∀ y, Φ y ∈ closure (Submodule.span ℂ {z | ∃ u ∈ UG Hm, z = ρ u k} : Set K) := by
  first | exact @GlobalTheory.exists_equivariant_multilinear_of_matrixCoeff_eq | exact GlobalTheory.exists_equivariant_multilinear_of_matrixCoeff_eq | (intros; apply GlobalTheory.exists_equivariant_multilinear_of_matrixCoeff_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularRepresentationOfFinitePair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularRepresentationOfFinitePair
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal symmDiff Topology Pointwise

namespace GlobalTheory.QuotRegular

section General

variable {G : Type} [Group G] (Γ : Subgroup G)

abbrev cl (g : G) : Quotient (QuotientGroup.rightRel Γ) := Quotient.mk _ g

theorem cl_mul (γ : Γ) (x : G) : cl Γ ((γ : G) * x) = cl Γ x := by
  refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
  simp

def tr (g : G) : Quotient (QuotientGroup.rightRel Γ) → Quotient (QuotientGroup.rightRel Γ) :=
  Quotient.map' (fun x => x * g) fun a b h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_assoc] using h

theorem tr_cl (g x : G) : tr Γ g (cl Γ x) = cl Γ (x * g) := rfl

theorem tr_one : tr Γ 1 = id := by
  funext q
  induction q using Quotient.inductionOn with
  | h x => exact congrArg (cl Γ) (mul_one x)

theorem tr_mul (g h : G) : tr Γ (g * h) = tr Γ h ∘ tr Γ g := by
  funext q
  induction q using Quotient.inductionOn with
  | h x => exact congrArg (cl Γ) (mul_assoc x g h).symm

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
theorem measurable_cl : Measurable (cl Γ) := measurable_quotient_mk''

theorem measurable_tr (g : G) : Measurable (tr Γ g) := by
  rw [measurable_from_quotient]
  exact (measurable_cl Γ).comp (measurable_mul_const g)

variable {Γ} {μ : Measure G} [μ.IsMulLeftInvariant] [Countable Γ] {𝓕 : Set G}

theorem ae_of_ae_quot (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {p : Quotient (QuotientGroup.rightRel Γ) → Prop}
    (hp : ∀ᵐ q ∂((μ.restrict 𝓕).map (cl Γ)), p q) : ∀ᵐ x ∂μ, p (cl Γ x) := by
  have h1 := ae_of_ae_map (measurable_cl Γ).aemeasurable hp
  rw [ae_restrict_iff'₀ h𝓕.nullMeasurableSet] at h1
  have h2 : ∀ᵐ y ∂μ, ∀ γ : Γ, (γ : G) * y ∈ 𝓕 → p (cl Γ ((γ : G) * y)) :=
    ae_all_iff.2 fun γ => (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae h1
  filter_upwards [h2, h𝓕.ae_covers] with y hy hc
  obtain ⟨γ, hγ⟩ := hc
  simpa only [cl_mul] using hy γ hγ

variable [μ.IsMulRightInvariant]

theorem measurePreserving_tr (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) :
    MeasurePreserving (tr Γ g) ((μ.restrict 𝓕).map (cl Γ)) ((μ.restrict 𝓕).map (cl Γ)) := by
  refine ⟨measurable_tr Γ g, Measure.ext fun A hA => ?_⟩
  have hA' : MeasurableSet (cl Γ ⁻¹' A) := measurable_cl Γ hA
  rw [Measure.map_apply (measurable_tr Γ g) hA, Measure.map_apply (measurable_cl Γ) hA,
    Measure.map_apply (measurable_cl Γ) (measurable_tr Γ g hA), Measure.restrict_apply hA',
    Measure.restrict_apply (measurable_cl Γ (measurable_tr Γ g hA))]
  have hD' : IsFundamentalDomain Γ ((fun x => x * g⁻¹) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ x => by
        change ((γ : G) * x) * g⁻¹ = (γ : G) * (x * g⁻¹)
        rw [mul_assoc]
  have hinv : ∀ γ : Γ, (fun x => γ • x) ⁻¹' (cl Γ ⁻¹' A) = cl Γ ⁻¹' A := by
    intro γ
    ext x
    change cl Γ ((γ : G) * x) ∈ A ↔ cl Γ x ∈ A
    rw [cl_mul]
  rw [← hD'.measure_set_eq h𝓕 hA' hinv, ← measure_preimage_mul_right μ g (_ ∩ (fun x => x * g⁻¹) ⁻¹' 𝓕)]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, tr_cl, mul_inv_cancel_right]

theorem measure_symmDiff_le (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {A : Set (Quotient (QuotientGroup.rightRel Γ))}
    (hA : MeasurableSet A) (g g₀ : G) :
    ((μ.restrict 𝓕).map (cl Γ)) ((tr Γ g ⁻¹' A) ∆ (tr Γ g₀ ⁻¹' A)) ≤
      μ (((fun x => x * g) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)) ∆ ((fun x => x * g₀) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕))) := by
  set S := ((fun x => x * g) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)) ∆ ((fun x => x * g₀) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)) with hS
  have hU : μ.restrict 𝓕 (⋃ γ : Γ, γ • S) ≤ μ S := by
    rw [h𝓕.measure_eq_tsum S]
    refine (measure_iUnion_le _).trans (le_of_eq (tsum_congr fun γ => ?_))
    rw [Measure.restrict_apply₀' h𝓕.nullMeasurableSet]
  rw [Measure.map_apply (measurable_cl Γ) ((measurable_tr Γ g hA).symmDiff (measurable_tr Γ g₀ hA))]
  refine le_trans (measure_mono_ae ?_) hU
  have key : ∀ a b x : G, (∃ γ : Γ, γ • (x * a) ∈ 𝓕) → cl Γ (x * a) ∈ A → cl Γ (x * b) ∉ A →
      ∃ γ : Γ, (γ : G) * x * a ∈ cl Γ ⁻¹' A ∩ 𝓕 ∧ (γ : G) * x * b ∉ cl Γ ⁻¹' A ∩ 𝓕 := by
    rintro a b x ⟨γ, hγ⟩ h2 h3
    refine ⟨γ, ?_, fun h => h3 ?_⟩
    · rw [mul_assoc]
      exact ⟨by rw [mem_preimage, cl_mul]; exact h2, hγ⟩
    · have := h.1
      rwa [mem_preimage, mul_assoc, cl_mul] at this
  filter_upwards [ae_restrict_of_ae ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h𝓕.ae_covers),
    ae_restrict_of_ae ((measurePreserving_mul_right μ g₀).quasiMeasurePreserving.ae h𝓕.ae_covers)] with x e1 e2 hx
  rcases hx with ⟨a, b⟩ | ⟨a, b⟩
  · obtain ⟨γ, k1, k2⟩ := key g g₀ x e1 a b
    exact mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inl ⟨k1, k2⟩)⟩
  · obtain ⟨γ, k1, k2⟩ := key g₀ g x e2 a b
    exact mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inr ⟨k1, k2⟩)⟩

def reg (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    G →* (Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ)) →L[ℂ] Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) where
  toFun g := (Lp.compMeasurePreservingₗᵢ ℂ (tr Γ g) (measurePreserving_tr h𝓕 g)).toContinuousLinearMap
  map_one' := by
    refine ContinuousLinearMap.ext fun F => Lp.ext ?_
    refine (Lp.coeFn_compMeasurePreserving F (measurePreserving_tr h𝓕 1)).trans ?_
    rw [tr_one]
    rfl
  map_mul' g h := by
    refine ContinuousLinearMap.ext fun F => Lp.ext ?_
    refine (Lp.coeFn_compMeasurePreserving F (measurePreserving_tr h𝓕 (g * h))).trans ?_
    refine EventuallyEq.trans ?_ (Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (tr Γ h) (measurePreserving_tr h𝓕 h) F) (measurePreserving_tr h𝓕 g)).symm
    rw [tr_mul]
    exact ((measurePreserving_tr h𝓕 g).quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_compMeasurePreserving F (measurePreserving_tr h𝓕 h))).symm

theorem reg_apply (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) (F : Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) :
    reg h𝓕 g F = Lp.compMeasurePreserving (tr Γ g) (measurePreserving_tr h𝓕 g) F := rfl

theorem reg_val (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) (F : Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) :
    ∀ᵐ x ∂μ, reg h𝓕 g F (cl Γ x) = F (cl Γ (x * g)) :=
  ae_of_ae_quot h𝓕 (p := fun q => reg h𝓕 g F q = F (tr Γ g q))
    (Lp.coeFn_compMeasurePreserving F (measurePreserving_tr h𝓕 g))

theorem norm_reg (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) (F : Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) :
    ‖reg h𝓕 g F‖ = ‖F‖ := Lp.norm_compMeasurePreserving F (measurePreserving_tr h𝓕 g)

theorem continuous_reg [LocallyCompactSpace G] [SecondCountableTopology G] [IsFiniteMeasureOnCompacts μ]
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) :
    Continuous fun g => reg h𝓕 g F := by
  refine Lp.induction (p := 2) ENNReal.ofNat_ne_top (fun F => Continuous fun g => reg h𝓕 g F)
    ?_ ?_ ?_ F
  · intro c A hA hμA
    rw [Lp.simpleFunc.coe_indicatorConst]
    simp only [reg_apply, Lp.indicatorConstLp_compMeasurePreserving]
    refine continuous_indicatorConstLp_set ENNReal.ofNat_ne_top fun g₀ => ?_
    let m : C(G, C(G, G)) := ContinuousMap.curry ⟨fun p : G × G => p.2 * p.1, by fun_prop⟩
    have ht : Tendsto (fun g => μ (((fun x => x * g) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)) ∆
        ((fun x => x * g₀) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)))) (𝓝 g₀) (𝓝 0) :=
      tendsto_measure_symmDiff_preimage_nhds_zero (μ := μ) (ν := μ) (f := m) (g := m g₀)
        (m.continuous.tendsto g₀) (Eventually.of_forall fun g => measurePreserving_mul_right μ g)
        (measurePreserving_mul_right μ g₀)
        ((measurable_cl Γ hA).nullMeasurableSet.inter h𝓕.nullMeasurableSet)
        (by
          rw [Measure.map_apply (measurable_cl Γ) hA, Measure.restrict_apply (measurable_cl Γ hA)] at hμA
          exact hμA.ne)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
      fun g => measure_symmDiff_le h𝓕 hA g g₀
  · intro f g hf hg _ h1 h2
    simp only [map_add (f := _)]
    exact h1.add h2
  · refine isClosed_of_closure_subset fun F hF => ?_
    refine TendstoUniformly.continuous (F := fun F' g => reg h𝓕 g F') (p := 𝓝 F) ?_
      (mem_closure_iff_frequently.1 hF)
    refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
    filter_upwards [Metric.ball_mem_nhds F hε] with F' h g
    rw [dist_eq_norm, ← map_sub, norm_reg, ← dist_eq_norm, dist_comm]
    exact h

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.HolDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isReg : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
    FinPair V μ 𝓕 → ∃ ρ, IsReg V μ 𝓕 ρ := by
  intro D V μ 𝓕 h
  obtain ⟨h1, h2, -, h4, h5, -, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have := h.haar
  have := h.right
  exact ⟨reg h.fd, reg_val h.fd, norm_reg h.fd, continuous_reg h.fd⟩

end GlobalTheory.QuotRegular
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularRepresentationOfFinitePairStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_representation_of_finite_pair : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), FinPair V μ 𝓕 → ∃ ρ, IsReg V μ 𝓕 ρ := by
  first | exact @GlobalTheory.QuotRegular.exists_isReg | exact GlobalTheory.QuotRegular.exists_isReg | (intros; apply GlobalTheory.QuotRegular.exists_isReg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValue
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.BackForm

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem coe_update (y : M.Vec) (τ : D.what₂.Tau) (w : M.sm τ) :
    (fun ρ => ((Function.update y τ w ρ : M.sm ρ) : M.H ρ)) = Function.update (fun ρ => (y ρ : M.H ρ)) τ (w : M.H τ) := by
  funext ρ
  by_cases h : ρ = τ
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem word_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (l : List (D.what₂.Tau × Mt V.rank)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (y : M.Vec) :
    ∃ y', l.foldr (fun p f => Rder θ V p.1 p.2 f) (T y) = T y' := by
  induction l with
  | nil => exact ⟨y, rfl⟩
  | cons p l ih =>
    obtain ⟨y', h⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p List.mem_cons_self
    exact ⟨_, by rw [List.foldr_cons, h]; exact hT y' p.1 p.2 hp ⟨_, hsm _ _ hp (y' p.1)⟩ rfl⟩

theorem rderC_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (y : M.Vec) (τ : D.what₂.Tau) (Z : Mt V.rank) (w : M.sm τ) :
    ∃ w' : M.sm τ, (w' : M.H τ) = dRepC (gramAt D V τ) (M.rep τ) Z w ∧
      RderC θ V τ Z (T (Function.update y τ w)) = T (Function.update y τ w') := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  refine ⟨⟨_, hsm τ _ h1 w⟩ + Complex.I • ⟨_, hsm τ _ h2 w⟩, rfl, ?_⟩
  rw [T.map_update_add, T.map_update_smul, RderC,
    hT (Function.update y τ w) τ _ h1 ⟨_, hsm τ _ h1 w⟩ (by simp),
    hT (Function.update y τ w) τ _ h2 ⟨_, hsm τ _ h2 w⟩ (by simp), Function.update_idem, Function.update_idem]
  simp only [RingHom.id_apply]

theorem wordC_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (y : M.Vec) (τ : D.what₂.Tau) (Zs : List (Mt V.rank)) (w : M.sm τ) :
    ∃ w' : M.sm τ, (w' : M.H τ) = (Zs.map (dRepC (gramAt D V τ) (M.rep τ))).foldr (fun f acc => f acc) (w : M.H τ) ∧
      (Zs.map (RderC θ V τ)).foldr (fun f acc => f acc) (T (Function.update y τ w)) = T (Function.update y τ w') := by
  induction Zs with
  | nil => exact ⟨w, rfl, rfl⟩
  | cons Z Zs ih =>
    obtain ⟨w', h1, h2⟩ := ih
    obtain ⟨w'', h3, h4⟩ := rderC_value T hsm hT y τ Z w'
    refine ⟨w'', ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1, h3]
    · rw [List.map_cons, List.foldr_cons, h2, h4]

theorem gelf_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (y : M.Vec) (τ : D.what₂.Tau) (k : ℕ) (c : ℂ) (w : M.sm τ)
    (hc : gelfRep (gramAt D V τ) (M.rep τ) k (w : M.H τ) = c • (w : M.H τ)) :
    gelf θ V τ k (T (Function.update y τ w)) = c • T (Function.update y τ w) := by
  choose W h1 h2 using fun idx : Fin (k + 1) → Fin V.rank =>
    wordC_value T hsm hT y τ (List.ofFn fun a : Fin (k + 1) => (Matrix.single (idx a) (idx (a + 1)) 1 : Mt V.rank)) w
  simp only [List.map_ofFn] at h1 h2
  have e : ∑ idx, W idx = c • w := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_smul, ← hc, gelfRep]
    exact Finset.sum_congr rfl fun idx _ => h1 idx
  have hs := T.map_update_smul y τ c w
  simp only [RingHom.id_apply] at hs
  rw [← hs, ← e, T.map_update_sum, gelf]
  exact Finset.sum_congr rfl fun idx _ => h2 idx

theorem zfin_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (hc : ∀ τ k, ∃ c : ℂ, ∀ w : M.sm τ, gelfRep (gramAt D V τ) (M.rep τ) k (w : M.H τ) = c • (w : M.H τ))
    (y : M.Vec) :
    ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ T y ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W := by
  refine ⟨Submodule.span ℂ {T y}, inferInstance, Submodule.mem_span_singleton_self _, fun τ k f hf => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
  obtain ⟨c, hc⟩ := hc τ k
  have e : a • T y = T (Function.update y τ (a • y τ)) := by
    rw [T.map_update_smul, Function.update_eq_self]
    simp only [RingHom.id_apply]
  have := gelf_value T hsm hT y τ k c (a • y τ) (hc _)
  rw [← e] at this
  rw [this]
  exact Submodule.smul_mem _ _ hf

def lettersAt (τ : D.what₂.Tau) (l : List (D.what₂.Tau × Mt V.rank)) : List (Mt V.rank) :=
  (l.filter fun p => p.1 = τ).map Prod.snd

theorem lettersAt_mem {τ : D.what₂.Tau} {l : List (D.what₂.Tau × Mt V.rank)} (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) :
    ∀ X ∈ lettersAt τ l, X ∈ lieAt V τ := by
  intro X hX
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hX
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hp
  have h3 : p.1 = τ := by simpa using h2
  exact h3 ▸ hl p h1

theorem word_mem (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    {τ : D.what₂.Tau} (l : List (Mt V.rank)) (hl : ∀ X ∈ l, X ∈ lieAt V τ) (w : M.sm τ) :
    l.foldr (dRep (M.rep τ)) (w : M.H τ) ∈ M.sm τ := by
  induction l with
  | nil => exact w.2
  | cons X l ih => exact hsm τ X (hl X List.mem_cons_self) ⟨_, ih fun q hq => hl q (List.mem_cons_of_mem _ hq)⟩

theorem word_map {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (Φ : ContinuousMultilinearMap ℂ M.H K)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hΦ : ∀ (v : M.Vec) τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) =
      Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))))
    (l : List (D.what₂.Tau × Mt V.rank)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (y : M.Vec) :
    l.foldr (dL2 θ V ρ) (Φ fun τ => (y τ : M.H τ)) =
      Φ fun τ => (lettersAt τ l).foldr (dRep (M.rep τ)) (y τ : M.H τ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hl' : ∀ q ∈ l, q.2 ∈ lieAt V q.1 := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    rw [List.foldr_cons, ih hl']
    have := hΦ (fun τ => ⟨_, word_mem hsm _ (lettersAt_mem hl') (y τ)⟩) p.1 p.2 (hl p List.mem_cons_self)
    refine this.trans ?_
    congr 1
    funext τ
    by_cases h : τ = p.1
    · subst h; simp [lettersAt]
    · have h' : ¬ p.1 = τ := fun e => h e.symm
      simp [lettersAt, Function.update_of_ne h, List.filter_cons, h']

theorem sum_bound {α β : Type} (a b : α → β → ℝ) (hb : ∀ l w, 0 ≤ b l w) (L : List α)
    (h : ∀ l ∈ L, ∃ c, ∀ w, a l w ≤ c * b l w) :
    ∃ C, 0 ≤ C ∧ ∀ w, (L.map fun l => a l w).sum ≤ C * (L.map fun l => b l w).sum := by
  induction L with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons l L ih =>
    obtain ⟨C, hC, ih⟩ := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    obtain ⟨c, hc⟩ := h l List.mem_cons_self
    refine ⟨max c C, le_max_of_le_right hC, fun w => ?_⟩
    have h0 : 0 ≤ (L.map fun l => b l w).sum := List.sum_nonneg (by
      intro x hx
      obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
      exact hb q w)
    simp only [List.map_cons, List.sum_cons, mul_add]
    exact add_le_add ((hc w).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hb l w)))
      ((ih w).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) h0))

theorem cont_value {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (Φ : ContinuousMultilinearMap ℂ M.H K) (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hΦ : ∀ (v : M.Vec) τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) =
      Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))))
    (L : List (List (D.what₂.Tau × Mt V.rank))) (hL : ∀ l ∈ L, ∀ p ∈ l, p.2 ∈ lieAt V p.1) (x : GA D V) (C : ℝ)
    (hC : ∀ y : M.Vec, ‖T y x‖ ≤ C * (L.map fun l => ‖l.foldr (dL2 θ V ρ) (Φ fun τ => (y τ : M.H τ))‖).sum)
    (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x := by
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ((LinearMap.proj x : (GA D V → ℂ) →ₗ[ℂ] ℂ) ∘ₗ T.toLinearMap v τ)
  have hℓ' : ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x := fun w => LinearMap.congr_fun hℓ w
  refine ⟨ℓ, ?_, hℓ'⟩
  obtain ⟨C', hC', hb⟩ := sum_bound
    (fun l (w : M.sm τ) => ‖l.foldr (dL2 θ V ρ) (Φ fun σ => ((Function.update v τ w σ : M.sm σ) : M.H σ))‖)
    (fun l (w : M.sm τ) => ‖(lettersAt τ l).foldr (dRep (M.rep τ)) (w : M.H τ)‖) (fun _ _ => norm_nonneg _) L (by
      intro l hl
      refine ⟨‖Φ.toContinuousLinearMap (fun σ => (lettersAt σ l).foldr (dRep (M.rep σ)) (v σ : M.H σ)) τ‖, fun w => ?_⟩
      refine le_trans (le_of_eq ?_) (ContinuousLinearMap.le_opNorm _ _)
      rw [word_map ρ Φ hsm hΦ l (hL l hl), ContinuousMultilinearMap.toContinuousLinearMap_apply]
      congr 2
      funext σ
      by_cases h : σ = τ
      · subst h; simp
      · simp [Function.update_of_ne h])
  refine ⟨L.map (lettersAt τ), |C| * C', ?_, fun w hw => ?_⟩
  · intro l hl
    obtain ⟨l', h', rfl⟩ := List.mem_map.1 hl
    exact lettersAt_mem (hL l' h')
  · have hw' : w ∈ M.sm τ := Submodule.subset_span hw
    have h1 := hℓ' ⟨w, hw'⟩
    have h2 := hb ⟨w, hw'⟩
    have h3 := hC (Function.update v τ ⟨w, hw'⟩)
    rw [List.map_map, mul_assoc]
    simp only at h1
    rw [h1]
    refine h3.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (List.sum_nonneg ?_)).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))
    intro x hx
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _

theorem continuous_rTr (k : GA D V) {f : GA D V → ℂ} (hf : Continuous f) : Continuous (rTr V k f) := by
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact hf.comp (continuous_mul_const k)

section L2

variable {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))}

theorem repr_add (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ) {F F' ψ ψ'} (h : Repr V μ 𝓕 F ψ) (h' : Repr V μ 𝓕 F' ψ') :
    Repr V μ 𝓕 (F + F') (ψ + ψ') := by
  simpa using (GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ).2.2.2.2.1 F F' ψ ψ' 1 h h'

theorem repr_smul (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ) (a : ℂ) {F ψ} (h : Repr V μ 𝓕 F ψ) :
    Repr V μ 𝓕 (a • F) (a • ψ) := by
  have := (GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ).2.2.2.2.1 F F ψ ψ (a - 1) h h
  rwa [sub_smul, one_smul, sub_add_cancel, sub_smul, one_smul, sub_add_cancel] at this

theorem eig_closure {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (A : Set K) (k : GA D V) (c : ℂ) (hA : ∀ z ∈ A, ρ k z = c • z) {F : K}
    (hF : F ∈ closure (Submodule.span ℂ A : Set K)) : ρ k F = c • F := by
  have h1 : (Submodule.span ℂ A : Set K) ⊆ {z | ρ k z = c • z} := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hA x hx
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      rw [map_add (f := _), hx, hy, smul_add]
    | smul a x _ hx =>
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [map_smul, hx, smul_comm]
  exact closure_minimal h1 (isClosed_eq (ρ k).continuous (continuous_const_smul c)) hF

theorem exists_map_abs {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (ρ : GA D V →* (K →L[ℂ] K)) {v : M.Vec} (hθ : IsInfFam θ) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1)
    (hiso : ∀ g F, ‖ρ g F‖ = ‖F‖) (F₀ : K)
    (hco : ∀ u ∈ GinfC V, ⟪F₀, ρ u F₀⟫_ℂ =
      ((‖F₀‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (archM V (θ τ) u) (v τ : M.H τ)⟫_ℂ) :
    ∃ Φ : ContinuousMultilinearMap ℂ M.H K, (Φ fun τ => (v τ : M.H τ)) = F₀ ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
        Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) ∧
      (∀ y, Φ y ∈ closure (Submodule.span ℂ {z | ∃ u : GA D V, z = ρ u F₀} : Set K)) ∧
      ∀ k ∈ GfC V, ∀ c : ℂ, ρ k F₀ = c • F₀ → ∀ y, ρ k (Φ y) = c • Φ y := by
  obtain ⟨L, hL1, hL2, -, -, -, hL3, -, hL4, hL5⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).1
  have h1 : (1 : D.what₂.Tau → Mt V.rank) ∈ UG (gramAt D V) := fun τ => by simp [Formalism.QuantumDeterminants.UH]
  have hone : L 1 = 1 := by
    have := hL2 1 h1 1 h1
    rw [mul_one] at this
    exact mul_eq_left.1 this.symm
  have a1 : ρ (L 1) = 1 := by rw [hone, map_one]
  have a2 : ∀ u ∈ UG (gramAt D V), ∀ u' ∈ UG (gramAt D V), ρ (L (u * u')) = ρ (L u) * ρ (L u') :=
    fun u hu u' hu' => by rw [hL2 u hu u' hu', map_mul]
  have a3 : ∀ u ∈ UG (gramAt D V), ⟪F₀, ρ (L u) F₀⟫_ℂ =
      ((‖F₀‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ := fun u hu => by
    rw [hco (L u) (hL1 u hu).1]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => by rw [(hL1 u hu).2 τ]
  obtain ⟨Φ, e1, e2, e3⟩ := GlobalTheory.T.exists_equivariant_multilinear_of_matrixCoeff_eq_unitaryProduct V.rank D.what₂.Tau (gramAt D V) M.H M.rep K
    (fun u => ρ (L u)) (fun τ => (v τ : M.H τ)) F₀
    (fun τ => ⟨(hL5 τ).2, (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1, (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.2.1, hv τ⟩)
    a1 a2 (fun u _ y => hiso _ y) a3
  refine ⟨Φ, e1, fun τ g hg y => ?_, fun y => ?_, fun k hk c h0 y => ?_⟩
  · rw [hL3 τ g hg]; exact e2 τ g hg y
  · refine closure_mono (Submodule.span_mono ?_) (e3 y)
    rintro z ⟨u, -, hz⟩
    exact ⟨_, hz⟩
  · refine eig_closure ρ _ k c ?_ (e3 y)
    rintro z ⟨u, hu, hz⟩
    have : ρ k (ρ (L u) F₀) = ρ (L u) (ρ k F₀) := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, hL4 k hk _ (hL1 u hu).1, map_mul, ContinuousLinearMap.mul_apply]
    rw [hz, this, h0, map_smul]

theorem eig_class (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ) {φ : GA D V → ℂ}
    {F₀ : Lp ℂ 2 (nuQ V μ 𝓕)} (hF : Repr V μ 𝓕 F₀ φ) (k : GA D V) (c : ℂ) (hc : ∀ g, φ (g * k) = c * φ g) :
    ρ k F₀ = c • F₀ := by
  have hr := GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ
  have h := hr.2.2.2.1 F₀ φ k hF
  have e : rTr V k φ = c • φ := funext hc
  rw [e] at h
  have h3 := hr.2.2.1 _ _ _ h (repr_smul hp hρ c hF)
  exact h3

theorem exists_map {w : D.what₂.Tau → Fin V.rank → ℤ} {v : M.Vec} (hθ : IsInfFam θ) (hs : HolShape M) (hw : WtIs M w)
    (hv : IsExtVec M v) (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ) {J : Set (GA D V)} {χ φ : GA D V → ℂ}
    (hφ : HolForm θ M w J χ φ) {F₀ : Lp ℂ 2 (nuQ V μ 𝓕)} (hF : Repr V μ 𝓕 F₀ φ) :
    ∃ Φ : ContinuousMultilinearMap ℂ M.H (Lp ℂ 2 (nuQ V μ 𝓕)), (Φ fun τ => (v τ : M.H τ)) = F₀ ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
        Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) ∧
      (∀ y, Φ y ∈ closure (Submodule.span ℂ {z | ∃ u : GA D V, z = ρ u F₀} : Set (Lp ℂ 2 (nuQ V μ 𝓕)))) ∧
      ∀ k ∈ GfC V, ∀ c : ℂ, (∀ g, φ (g * k) = c * φ g) → ∀ y, ρ k (Φ y) = c • Φ y := by
  have h1 := GlobalTheory.T.inner_rho_eq_normSq_mul_prod_of_holForm D θ V S M w v hθ hs hw hv μ 𝓕 ρ hp hρ J χ φ F₀ hφ hF
  have h2 := exists_map_abs (K := Lp ℂ 2 (nuQ V μ 𝓕)) (M := M) (v := v) ρ hθ (fun τ => (hv τ).1) hρ.iso F₀
  have h3 := h2 h1
  refine h3.imp fun Φ h => ⟨h.1, h.2.1, h.2.2.1, fun k hk c hc => ?_⟩
  have h4 := eig_class hp hρ hF k c hc
  exact h.2.2.2 k hk c h4

end L2


set_option maxHeartbeats 1000000 in
theorem exists_multMap : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → (∃ μ 𝓕, FinPair V μ 𝓕) → ∀ (J : Set (GA D V)) (χ φ : GA D V → ℂ), J ⊆ (GfC V : Set (GA D V)) → HolForm θ M w J χ φ → ZCusp V φ → ∃ T : MMap M, IsMultMap θ M J χ T ∧ T v = φ := by
  rintro D θ V S M w v hθ hs hw hv ⟨μ, 𝓕, hp⟩ J χ φ hJ hφ hZ
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.regular_representation_of_finite_pair D V μ 𝓕 hp
  obtain ⟨r1, r2, -, r4, -, -⟩ := GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ
  obtain ⟨F₀, hF⟩ := r1 φ hφ.aut.cont hφ.aut.left hφ.bdd
  obtain ⟨Φ, e1, e2, e3, e4⟩ := exists_map hθ hs hw hv hp hρ hφ hF
  obtain ⟨U, hU, hUφ⟩ := hφ.aut.level
  have hfix : ∀ y, ∀ k ∈ U, k ∈ GfC V → ρ k (Φ y) = Φ y := fun y k hk hk' => by
    simpa using e4 k hk' 1 (fun g => by rw [hUφ k hk hk', one_mul]) y
  have hsmM := GlobalTheory.T.equivariantMultilinear_maps_smoothVectors_intertwines D θ V hθ S M _ ρ Φ e2
  choose ψ p1 p2 p3 p4 using fun y : M.Vec =>
    GlobalTheory.T.smooth_vector_automorphic_derivatives D θ V hθ μ 𝓕 ρ hp hρ U hU (Φ fun τ => (y τ : M.H τ)) (hsmM y).1 (hfix _)
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).1
  have hH : ∀ τ, (gramAt D V τ).IsHermitian := GlobalTheory.SmoothAutCheck.gramAt_herm V
  have hdet : ∀ τ, (gramAt D V τ).det ≠ 0 := fun τ => (GlobalTheory.SmoothAutCheck.gramAt_unit V τ).ne_zero
  have hsv := fun τ => GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv V.rank (gramAt D V τ) (M.H τ) (M.rep τ) (hH τ) (hdet τ) (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1
  have hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ := fun τ X hX w =>
    Submodule.subset_span (((hsv τ).2 w ((hsv τ).1 w w.2)).2.1 X hX).1
  have uniq : ∀ (y : M.Vec) f, Continuous f → Repr V μ 𝓕 (Φ fun τ => (y τ : M.H τ)) f → ψ y = f :=
    fun y f hf h => r2 _ _ _ (p2 y).cont hf (p1 y) h
  let T : MMap M := MultilinearMap.mk' ψ
    (fun y τ a b => by
      refine uniq _ _ ((p2 _).cont.add (p2 _).cont) ?_
      have := repr_add hp hρ (p1 (Function.update y τ a)) (p1 (Function.update y τ b))
      rw [coe_update, coe_update, ← Φ.map_update_add] at this
      rw [coe_update]
      exact this)
    (fun y τ c a => by
      refine uniq _ _ ((p2 _).cont.const_smul c) ?_
      have := repr_smul hp hρ c (p1 (Function.update y τ a))
      rw [coe_update, ← Φ.map_update_smul] at this
      rw [coe_update]
      exact this)
  have hTψ : ∀ y, T y = ψ y := fun _ => rfl
  have hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w) := by
    intro y τ X hX w hw
    obtain ⟨q1, q2⟩ := p4 y [(τ, X)] (by simpa using hX)
    simp only [List.foldr_cons, List.foldr_nil] at q1 q2
    refine (uniq _ _ q1 ?_).symm
    rw [coe_update, hw, ← (hsmM y).2 τ X hX]
    exact q2
  obtain ⟨N, L, hL, hgr⟩ := GlobalTheory.T.sobolev_bound_for_smooth_vectors D θ V hθ μ 𝓕 ρ hp hρ U hU
  refine ⟨T, ⟨fun y => ⟨p2 y, p3 y, ?_, N, fun l hl x => ?_⟩, fun y => ?_, fun y k hk g => ?_, fun τ g hg y z hz => ?_,
    fun τ y x => ?_⟩, uniq v φ hφ.aut.cont (e1 ▸ hF)⟩
  · refine zfin_value T hsm hT (fun τ k => ?_) y
    obtain ⟨-, m1, m2, m3⟩ := GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ
    obtain ⟨k1, k2⟩ := GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hs hw hv τ
    obtain ⟨c, hc⟩ := GlobalTheory.T.gelfand_invariants_act_by_scalars_highest_weight V.rank (gramAt D V τ) _ _ (w τ) (M.H τ) (M.rep τ) (m3 hs).1 m1 m2 (v τ)
      (by rw [← norm_ne_zero_iff, (hv τ).1]; exact one_ne_zero) k1 k2 k
    exact ⟨c, fun z => hc z ((hsv τ).1 z z.2)⟩
  · obtain ⟨y', hy'⟩ := word_value T hsm hT l hl y
    obtain ⟨C, hC⟩ := hgr x
    refine ⟨C * (L.map fun l => ‖l.foldr (dL2 θ V ρ) (Φ fun τ => (y' τ : M.H τ))‖).sum, fun g hg => ?_⟩
    rw [hy', mul_right_comm]
    exact hC _ _ (hsmM y').1 (hfix _) (p2 y').cont (p1 y') g hg
  · exact GlobalTheory.T.isCuspFun_of_transvection_constantTerms_zero D θ V hθ _ (p2 y)
      (GlobalTheory.T.cuspidality_preserved_in_closure D θ V hθ μ 𝓕 ρ hp hρ φ (ψ y) F₀ _ hφ.aut hZ hF (p2 y) (p1 y) (e3 _))
  · have h1 := r4 _ _ k (p1 y)
    rw [e4 k (hJ hk) (χ k) (hφ.lev k hk)] at h1
    have h2 := r2 _ _ _ (continuous_rTr k (p2 y).cont) ((p2 y).cont.const_smul (χ k)) h1
      (repr_smul hp hρ (χ k) (p1 y))
    exact congrFun h2 g
  · refine uniq _ _ (continuous_rTr (atTau θ V τ g) (p2 y).cont) ?_
    rw [coe_update, hz, e2 τ g hg]
    exact r4 _ _ _ (p1 y)
  · obtain ⟨C, hC⟩ := hgr x
    refine cont_value ρ Φ T hsm (fun y => (hsmM y).2) L hL x (C * normInf θ V 1 ^ N) (fun y => ?_) τ y
    have := hC _ _ (hsmM y).1 (hfix _) (p2 y).cont (p1 y) 1 (one_mem _)
    rwa [mul_one] at this

end GlobalTheory.BackForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValueStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedHolomorphicForm_eq_multiplicitySpace_value : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → (∃ μ 𝓕, FinPair V μ 𝓕) → ∀ (J : Set (GA D V)) (χ φ : GA D V → ℂ), J ⊆ (GfC V : Set (GA D V)) → HolForm θ M w J χ φ → ZCusp V φ → ∃ T : MMap M, IsMultMap θ M J χ T ∧ T v = φ := by
  first | exact @GlobalTheory.BackForm.exists_multMap | exact GlobalTheory.BackForm.exists_multMap | (intros; apply GlobalTheory.BackForm.exists_multMap <;> assumption)
end
