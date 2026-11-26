module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SacSuccAbove
public import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormPtsB
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial MeasureTheory

theorem countable_numberField (K : Type) [Field K] [NumberField K] : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem ST_scale (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ) (y : Fin (d.N + 1 + d.D) → ℂ)
    (hy : ∀ i, y (Fin.natAdd (d.N + 1) i) ≠ 0) :
    d.ST c sg (fun i j => NPB.gpt (fun q => t q.1 q.2) y (i.succ, j)) = d.ST c sg t := by
  ext P
  simp only [ST, Set.mem_setOf_eq, NPB.gpt, Fin.cases_succ]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, mul_eq_zero]
  simp [hy i]

theorem gpt_one (t : Fin d.D → Fin (d.N + 1) → ℂ) (t0 : Fin (d.N + 1) → ℂ) :
    NPB.gpt (fun q => t q.1 q.2) (Fin.addCases t0 (fun _ => (1 : ℂ))) =
      fun v : TVar d.D d.N => Fin.cases (motive := fun _ => ℂ) (t0 v.2) (fun i => t i v.2) v.1 := by
  funext v
  rcases v with ⟨a, j⟩
  refine Fin.cases ?_ (fun i => ?_) a <;> simp [NPB.gpt]

theorem fib (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ)
    (y : Fin (d.N + 1 + d.D) → ℂ)
    (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 →
      eval₂ sg (NPB.gpt (fun q => t q.1 q.2) y) q ≠ 0) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    (d.ST c sg t).Finite ∧ (d.ST c sg t).ncard = d.delc c ∧
      (∀ g : Ω c, tauPev sg _ hpt (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g))
        = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), P g) ∧
      tauPev sg _ hpt (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)) =
        ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t),
          ∑ j, y (Fin.castAdd d.D j) * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) := by
  letI iA : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI iB : Algebra (KTf K d.D d.N) ℂ := (tauPev sg _ hpt).toAlgebra
  obtain ⟨hfd, hrank⟩ := d.omS_finite hd h c
  haveI := hfd
  haveI : CharZero (KTf K d.D d.N) := inferInstance
  haveI : Algebra.IsIntegral (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := Algebra.IsSeparable.of_integral _ _
  have hy : ∀ i, y (Fin.natAdd (d.N + 1) i) ≠ 0 := by
    intro i h0
    apply hpt (MvPolynomial.X (i.succ, 0)) (MvPolynomial.X_ne_zero _)
    simp [NPB.gpt, h0]
  have hST : d.ST c sg (fun i j => NPB.gpt (fun q => t q.1 q.2) y (i.succ, j)) = d.ST c sg t :=
    d.ST_scale c sg t y hy
  obtain ⟨hinj, hrange⟩ := d.fibre_core (hd := hd) (h := h) (c := c) (sg := sg)
    (pt := NPB.gpt (fun q => t q.1 q.2) y) (hpt := hpt)
  rw [hST] at hrange
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hrange]
    exact Set.finite_range _
  · rw [← hrange, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, AlgHom.card, hrank]
  · intro g
    have h1 := Algebra.norm_eq_prod_embeddings (KTf K d.D d.N) ℂ
      (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g)
    rw [← hrange, finprod_mem_range hinj, finprod_eq_prod_of_fintype]
    exact h1
  · have h1 := Algebra.norm_eq_prod_embeddings (KTf K d.D d.N) ℂ (d.rationalBaseRow c)
    rw [← hrange, finprod_mem_range hinj, finprod_eq_prod_of_fintype]
    refine h1.trans (Finset.prod_congr rfl fun σ _ => ?_)
    have hσ : (σ : OmS (Ω c) d.D d.N →+* ℂ).comp (d.KTtoS h c) = tauPev sg _ hpt :=
      RingHom.ext fun x => σ.commutes x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [rationalBaseRow, map_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have he := d.emb_sH (h := h) (c := c) (sg := sg)
      (pt := NPB.gpt (fun q => t q.1 q.2) y) (hpt := hpt) (σ : OmS (Ω c) d.D d.N →+* ℂ) hσ
      (MvPolynomial.X (0, j))
    simp only [AlgHom.coe_toRingHom] at he
    rw [he]
    simp [NPB.gpt]

theorem norm_at_sg_B (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      (d.ST c sg (d.tOf z)).Finite ∧ (d.ST c sg (d.tOf z)).ncard = d.delc c ∧
      (∀ (g : Ω c) (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), g ≠ 0 → b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) *
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), P g) ∧
      (∀ (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
          ∑ j, t0 j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  have := countable_numberField K
  filter_upwards [NPB.ae_gen (K := K) (D := d.D) (N := d.N) sg] with z hz
  have hG : ∀ (a : Fin d.D → ℕ) (p : MvPolynomial (Fin d.D × Fin (d.N + 1)) K),
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a p → p ≠ 0 →
        eval₂ sg (fun q => d.tOf z q.1 q.2) p ≠ 0 := hz
  obtain ⟨y1, -, hpt1⟩ := NPB.exists_gen sg (fun q => d.tOf z q.1 q.2) hG 1 one_ne_zero
  obtain ⟨hfin, hcard, -, -⟩ := d.fib hd h c sg (d.tOf z) y1 hpt1
  refine ⟨hfin, hcard, ?_, ?_⟩
  · intro g a b t0 _ _ hab hbt
    have hQ : NPB.psi sg (fun q => d.tOf z q.1 q.2) a -
        C (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), P g) *
          NPB.psi sg (fun q => d.tOf z q.1 q.2) b = 0 := by
      by_contra hQ
      obtain ⟨y, hy, hpt⟩ := NPB.exists_gen sg _ hG _ hQ
      obtain ⟨-, -, hn, -⟩ := d.fib hd h c sg (d.tOf z) y hpt
      apply hy
      have h1 := congrArg (tauPev sg _ hpt) hab
      rw [map_mul, hn g, tauPev_apply, tauPev_apply] at h1
      rw [map_sub, map_mul, eval_C, NPB.eval_psi, NPB.eval_psi, ← h1, sub_self]
    have h2 := congrArg (eval (Fin.addCases t0 (fun _ => (1 : ℂ)))) hQ
    rw [map_sub, map_mul, eval_C, NPB.eval_psi, NPB.eval_psi, d.gpt_one, map_zero, sub_eq_zero] at h2
    rw [div_eq_iff hbt]
    exact h2
  · intro a b t0 _ hab hbt
    let cX : MvPolynomial (Fin (d.N + 1 + d.D)) ℂ := ∏ P ∈ hfin.toFinset,
      ∑ j, X (Fin.castAdd d.D j) * C (P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)))
    have hcX : ∀ y, eval y cX = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
        ∑ j, y (Fin.castAdd d.D j) * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) := by
      intro y
      rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [cX, map_prod, map_sum, map_mul, eval_X, eval_C]
    have hQ : NPB.psi sg (fun q => d.tOf z q.1 q.2) a - cX * NPB.psi sg (fun q => d.tOf z q.1 q.2) b = 0 := by
      by_contra hQ
      obtain ⟨y, hy, hpt⟩ := NPB.exists_gen sg _ hG _ hQ
      obtain ⟨-, -, -, hn⟩ := d.fib hd h c sg (d.tOf z) y hpt
      apply hy
      have h1 := congrArg (tauPev sg _ hpt) hab
      rw [map_mul, hn, tauPev_apply, tauPev_apply] at h1
      rw [map_sub, map_mul, hcX, NPB.eval_psi, NPB.eval_psi, ← h1, sub_self]
    have h2 := congrArg (eval (Fin.addCases t0 (fun _ => (1 : ℂ)))) hQ
    rw [map_sub, map_mul, hcX, NPB.eval_psi, NPB.eval_psi, d.gpt_one, map_zero, sub_eq_zero] at h2
    simp only [Fin.addCases_left] at h2
    rw [div_eq_iff hbt]
    exact h2

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HintIntOfBounds
namespace ReciprocityTheory.ChartRestriction.G.T0

open MeasureTheory ReciprocityTheory.MultiplicativeHeights

noncomputable def hintPt {D n : ℕ} (t0 : Fin n → ℂ) (z : BlockSphere D n) :
    Fin (D + 1) × Fin n → ℂ :=
  fun v => Fin.cases (t0 v.2) (fun i => spherePoint (z i) v.2) v.1

theorem hint_mpSplit (D n : ℕ) (hn : 0 < n) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => UnitSphereC n) 0)
      (blockSphereProb (D + 1) n) ((sphereProb n).prod (blockSphereProb D n)) := by
  unfold blockSphereProb
  exact measurePreserving_piFinSuccAbove (fun _ : Fin (D + 1) => sphereProb n) 0

private theorem isProbabilityMeasure_sphereProb' (n : ℕ) (hn : 0 < n) : IsProbabilityMeasure (sphereProb n) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  unfold sphereProb
  have hpos : 0 < Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) := Module.finrank_pos
  have h1 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
    rw [Measure.toSphere_apply_univ]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hpos.ne') (Metric.measure_ball_pos _ _ one_pos).ne'
  have h2 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ ⊤ := by
    rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite h1 h2

theorem hint_mpTail (D n : ℕ) (hn : 0 < n) :
    MeasurePreserving (fun z : BlockSphere (D + 1) n => fun i : Fin D => z i.succ)
      (blockSphereProb (D + 1) n) (blockSphereProb D n) := by
  haveI := isProbabilityMeasure_sphereProb' n hn
  haveI : SFinite (blockSphereProb D n) := by
    unfold blockSphereProb
    infer_instance
  have h := (measurePreserving_snd (μ := sphereProb n) (ν := blockSphereProb D n)).comp
    (hint_mpSplit D n hn)
  have e : (fun z : BlockSphere (D + 1) n => fun i : Fin D => z i.succ) =
      Prod.snd ∘ ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => UnitSphereC n) 0) := by
    funext z i
    first
      | rfl
      | (simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth]; done)
      | (simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth]; rfl)
      | exact congrArg z (by simp)
  rw [e]
  exact h

theorem hint_blockPoint_eq {D n : ℕ} (z : BlockSphere (D + 1) n) :
    blockPoint z = hintPt (spherePoint (z 0)) (fun i : Fin D => z i.succ) := by
  funext ⟨i, j⟩
  cases i using Fin.cases with
  | zero => simp [blockPoint, hintPt]
  | succ i => simp [blockPoint, hintPt]

theorem hint_eval_indep {D n : ℕ} {a : Fin (D + 1) → ℕ} {q : MvPolynomial (Fin (D + 1) × Fin n) ℂ}
    (hq : IsMultiHomogeneous a q) (ha : a 0 = 0) (x y : Fin (D + 1) × Fin n → ℂ)
    (hxy : ∀ v : Fin (D + 1) × Fin n, v.1 ≠ 0 → x v = y v) :
    MvPolynomial.eval x q = MvPolynomial.eval y q := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl fun s hs => ?_
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v.1 = 0
  · have h0 : s v = 0 := by
      have hsum := hq s hs 0
      rw [ha] at hsum
      have hle : s (0, v.2) ≤ ∑ j : Fin n, s (0, j) :=
        Finset.single_le_sum (f := fun j => s (0, j)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ _)
      have hz : s (0, v.2) = 0 := by omega
      have hv' : v = (0, v.2) := Prod.ext hv rfl
      rw [hv']
      exact hz
    rw [h0, pow_zero, pow_zero]
  · rw [hxy v hv]

theorem hint_continuous_pt {D n : ℕ} (t0 : Fin n → ℂ) :
    Continuous fun z : BlockSphere D n => hintPt t0 z := by
  apply continuous_pi
  rintro ⟨i, j⟩
  cases i using Fin.cases with
  | zero =>
    simp only [hintPt, Fin.cases_zero]
    exact continuous_const
  | succ i =>
    simp only [hintPt, Fin.cases_succ]
    unfold spherePoint
    fun_prop

theorem hint_logInt_tail {D n : ℕ} (hn : 0 < n) {a : Fin (D + 1) → ℕ}
    {q : MvPolynomial (Fin (D + 1) × Fin n) ℂ} (hq0 : q ≠ 0) (hq : IsMultiHomogeneous a q)
    (ha : a 0 = 0) (t0 : Fin n → ℂ) :
    Integrable (fun z : BlockSphere D n => Real.log ‖MvPolynomial.eval (hintPt t0 z) q‖)
      (blockSphereProb D n) := by
  have hmeas : AEStronglyMeasurable
      (fun z : BlockSphere D n => Real.log ‖MvPolynomial.eval (hintPt t0 z) q‖)
      (blockSphereProb D n) :=
    ((continuous_norm.comp ((MvPolynomial.continuous_eval q).comp
      (hint_continuous_pt t0))).measurable.log).aestronglyMeasurable
  rw [← (hint_mpTail D n hn).integrable_comp hmeas]
  refine (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable (D + 1) n a q hq0 hq).congr
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply]
  rw [hint_blockPoint_eq, hint_eval_indep hq ha _ (hintPt t0 (fun i : Fin D => z i.succ))]
  rintro ⟨i, j⟩ hi
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hi
  rfl

theorem hint_ae_tail {D n : ℕ} (hn : 0 < n) {a : Fin (D + 1) → ℕ}
    {q : MvPolynomial (Fin (D + 1) × Fin n) ℂ} (hq0 : q ≠ 0) (hq : IsMultiHomogeneous a q)
    (ha : a 0 = 0) (t0 : Fin n → ℂ) :
    ∀ᵐ z ∂(blockSphereProb D n), MvPolynomial.eval (hintPt t0 z) q ≠ 0 := by
  have hA : MeasurableSet {z : BlockSphere D n | MvPolynomial.eval (hintPt t0 z) q = 0} :=
    (isClosed_eq ((MvPolynomial.continuous_eval q).comp (hint_continuous_pt t0))
      continuous_const).measurableSet
  rw [ae_iff]
  simp only [not_not]
  rw [← (hint_mpTail D n hn).measure_preimage hA.nullMeasurableSet]
  have h0 := ae_blockSphere_eval_ne_zero (D + 1) n a q hq0 hq
  rw [ae_iff] at h0
  refine measure_mono_null (fun z hz => ?_) h0
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hz
  simp only [Set.mem_ofPred_eq, not_not]
  rw [hint_blockPoint_eq, hint_eval_indep hq ha _ (hintPt t0 (fun i : Fin D => z i.succ))]
  · exact hz
  rintro ⟨i, j⟩ hi
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hi
  rfl

theorem hint_fubini {D n : ℕ} (hn : 0 < n) {a : Fin (D + 1) → ℕ}
    {F : MvPolynomial (Fin (D + 1) × Fin n) ℂ} (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    Integrable (fun z : BlockSphere D n =>
      ∫ s, Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) F‖ ∂(sphereProb n))
      (blockSphereProb D n) := by
  haveI := sphereMeasure_isProbability hn
  haveI := blockSphereMeasure_isProbability (B := D) hn
  set G : UnitSphereC n × BlockSphere D n → ℝ :=
    fun p => Real.log ‖MvPolynomial.eval (hintPt (spherePoint p.1) p.2) F‖ with hG
  have hint : Integrable G ((sphereProb n).prod (blockSphereProb D n)) := by
    rw [← (hint_mpSplit D n hn).integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => UnitSphereC n) 0).measurableEmbedding]
    refine (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable (D + 1) n a F hF0 hF).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.comp_apply, hG]
    rw [hint_blockPoint_eq]
    rfl
  exact hint.integral_prod_right

theorem hint_lin_ae {n : ℕ} (c : Fin n → ℂ) (hc : c ≠ 0) :
    ∀ᵐ s ∂(sphereProb n), ∑ j, c j * spherePoint s j ≠ 0 := by
  classical
  set Lc : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ :=
    ∑ j, c j • (EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).toLinearMap with hLc
  have hL : ∀ x : EuclideanSpace ℂ (Fin n), Lc x = ∑ j, c j * WithLp.ofLp x j := by
    intro x
    simp [hLc]
  set H : Submodule ℝ (EuclideanSpace ℂ (Fin n)) := LinearMap.ker (Lc.restrictScalars ℝ) with hH
  have hHtop : H ≠ ⊤ := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
    intro htop
    have hmem : EuclideanSpace.single j (1 : ℂ) ∈ H := htop ▸ Submodule.mem_top
    rw [hH, LinearMap.mem_ker, LinearMap.restrictScalars_apply, hL] at hmem
    simp at hmem
    exact hj hmem
  have hvol : (volume : Measure (EuclideanSpace ℂ (Fin n))) H = 0 :=
    Measure.addHaar_submodule _ H hHtop
  have hA : MeasurableSet {s : UnitSphereC n | ¬ (∑ j, c j * spherePoint s j ≠ 0)} := by
    simp only [not_not]
    exact (isClosed_eq (by unfold spherePoint; fun_prop) continuous_const).measurableSet
  rw [ae_iff]
  unfold sphereProb
  refine ProbabilityTheory.cond_absolutelyContinuous ?_
  rw [Measure.toSphere_apply' (μ := (volume : Measure (EuclideanSpace ℂ (Fin n)))) hA]
  apply mul_eq_zero_of_right
  refine measure_mono_null ?_ hvol
  rintro _ ⟨r, _, _, ⟨s, hs, rfl⟩, rfl⟩
  simp only [Set.mem_setOf_eq, not_not] at hs
  show r • (s : EuclideanSpace ℂ (Fin n)) ∈ H
  refine H.smul_mem r ?_
  rw [hH, LinearMap.mem_ker, LinearMap.restrictScalars_apply, hL]
  simpa [spherePoint] using hs

end ReciprocityTheory.ChartRestriction.G.T0
end
