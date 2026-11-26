module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.OverlapG
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Exbasis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.SimpBdM

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.MeasurableSetSimplex
noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.LocalOverlapAverage

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

def actEq (x : Gp L N) : HS L N ≃L[ℝ] HS L N where
  toLinearEquiv :=
    { toFun := actL x
      invFun := actL x⁻¹
      map_add' := (actL x).map_add
      map_smul' := (actL x).map_smul
      left_inv := fun h => by rw [← actL_mul, inv_mul_cancel, actL_one]
      right_inv := fun h => by rw [← actL_mul, mul_inv_cancel, actL_one] }
  continuous_toFun := (actL x).continuous
  continuous_invFun := (actL x⁻¹).continuous

@[simp] theorem actEq_apply (x : Gp L N) (h : HS L N) : actEq x h = actL x h := rfl

theorem pos_convex : Convex ℝ (Pos L N) := by
  intro h hh k hk a b ha hb hab w
  rw [mat_add, mat_smul, mat_smul]
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    subst hab
    simpa using hk w
  · exact ((hh w).smul ha').add_posSemidef ((hk w).posSemidef.smul hb)

theorem kset_sub {q : ℕ} (x : Fin (q + 1) → Gp L N) {B : Set (HS L N)} (hB : B ⊆ Pos L N) :
    Kset (fun j => actL (x j)) B ⊆ Pos L N := by
  rintro p ⟨τ, hτ0, hτ1, y, hy, rfl⟩
  exact pos_convex.sum_mem (fun j _ => hτ0 j) hτ1 fun j _ => actL_pos (x j) (hB (hy j))

theorem isCompact_kset {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {q : ℕ}
    (A : Fin (q + 1) → V →L[ℝ] V) {B : Set V} (hB : IsCompact B) : IsCompact (Kset A B) := by
  have hc : IsCompact ((stdSimplex ℝ (Fin (q + 1))) ×ˢ (Set.univ.pi fun _ : Fin (q + 1) => B)) :=
    IsCompact.prod (isCompact_stdSimplex ℝ (Fin (q + 1))) (isCompact_univ_pi fun _ => hB)
  have hcont : Continuous fun p : (Fin (q + 1) → ℝ) × (Fin (q + 1) → V) =>
      ∑ j, p.1 j • A j (p.2 j) := by fun_prop
  have e : Kset A B = (fun p : (Fin (q + 1) → ℝ) × (Fin (q + 1) → V) =>
      ∑ j, p.1 j • A j (p.2 j)) '' ((stdSimplex ℝ (Fin (q + 1))) ×ˢ (Set.univ.pi fun _ : Fin (q + 1) => B)) := by
    ext p
    constructor
    · rintro ⟨τ, hτ0, hτ1, y, hy, rfl⟩
      exact ⟨(τ, y), ⟨⟨hτ0, hτ1⟩, fun j _ => hy j⟩, rfl⟩
    · rintro ⟨⟨τ, y⟩, ⟨⟨hτ0, hτ1⟩, hy⟩, rfl⟩
      exact ⟨τ, hτ0, hτ1, y, fun j => hy j (Set.mem_univ _), rfl⟩
  rw [e]
  exact hc.image hcont

theorem simplex_pos {q : ℕ} (y : Fin (q + 1) → HS L N) (hy : ∀ j, y j ∈ Pos L N) (t : Fin q → ℝ)
    (ht : (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1) : y 0 + ∑ j, t j • (y j.succ - y 0) ∈ Pos L N := by
  have e : y 0 + ∑ j, t j • (y j.succ - y 0) =
      ∑ i, (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i • y i := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul, one_smul,
      ← Finset.sum_smul]
    abel
  rw [e]
  refine pos_convex.sum_mem (fun i _ => ?_) ?_ fun i _ => hy i
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      linarith [ht.2]
    · simpa only [Fin.cons_succ] using ht.1 j
  · rw [Fin.sum_univ_succ]
    simp

theorem measurableSet_simplex (q : ℕ) :
    MeasurableSet {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} := by
  have : {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} =
      (⋂ j, {t : Fin q → ℝ | 0 ≤ t j}) ∩ {t | ∑ j, t j ≤ 1} := by
    ext t
    simp
  rw [this]
  refine (IsClosed.inter (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j))
    (isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)).measurableSet

theorem intP_inv {q : ℕ} (ω : Form (HS L N) q) (g : Gp L N) (hg : FInv ω g)
    (y : Fin (q + 1) → Pos L N) : intP ω (fun j => g • y j) = intP ω y := by
  simp only [intP, intS]
  refine setIntegral_congr_fun (measurableSet_simplex q) fun t ht => ?_
  have hv : ∀ j, ((g • y j : Pos L N) : HS L N) = actL g (y j).1 := fun j => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hv, ← map_sub, ← map_smul, ← map_sum, ← map_add (f := _)]
  have hp := simplex_pos (fun j => (y j).1) (fun j => (y j).2) t ht
  have := congrArg (fun f => f (fun j => (y j.succ).1 - (y 0).1)) (hg _ hp)
  simpa [Function.comp_def, map_sub] using this

theorem cont_actL_apply (v : HS L N) : Continuous fun x : Gp L N => actL x v := by
  refine continuous_induced_rng.2 ?_
  change Continuous fun x : Gp L N => fun w i j =>
    ((((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ * mat v w *
      ((x w)⁻¹ : GL (Fin N) ℂ)) i j
  refine continuous_pi fun w => continuous_pi fun i => continuous_pi fun j => ?_
  have hi : Continuous fun x : Gp L N => (((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) :=
    Units.continuous_coe_inv.comp (continuous_apply w)
  exact ((hi.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hi).matrix_elem i j

theorem cont_actL : Continuous fun x : Gp L N => actL x :=
  continuous_clm_apply.2 fun v => cont_actL_apply v

theorem cont_fr {q : ℕ} (ω : Form (HS L N) q) (hω : ContinuousOn ω (Pos L N)) :
    Continuous (fr ω) := by
  have h1 : Continuous fun x : Gp L N => ω (actL x (one L N).1) :=
    hω.comp_continuous (cont_actL_apply _) fun x => actL_pos x (one L N).2
  exact (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp cont_actL).clm_apply h1

theorem cont_ofS : Continuous (ofS L N) :=
  continuous_pi fun w => Matrix.SpecialLinearGroup.continuous_toGL.comp (continuous_apply w)

theorem fr_mul {q : ℕ} (ω : Form (HS L N) q) (g x : Gp L N) (hg : FInv ω g) :
    fr ω (g * x) = fr ω x := by
  ext v
  have h := congrArg (fun f => f (fun i => actL x (v i))) (hg _ (actL_pos x (one L N).2))
  simpa [fr, actL_mul, Function.comp_def] using h

theorem ofS_lat {γ : Sp L N} (hγ : γ ∈ latS L N) : ∃ A : Gm L N, ofS L N γ = emb L N A := by
  obtain ⟨A, rfl⟩ := hγ
  refine ⟨Matrix.SpecialLinearGroup.toGL A, ?_⟩
  funext w
  ext i j
  rfl

theorem ball_pos : ∃ r : ℝ, 0 < r ∧ Metric.closedBall (one L N).1 r ⊆ Pos L N := by
  classical
  obtain ⟨c, hc, hev⟩ := UpperTheory.V.KT.lowbd L N (one L N).1 (one L N).2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε / 2, half_pos hε, fun k hk w => ?_⟩
  have hk' := hball (lt_of_le_of_lt (Metric.mem_closedBall.1 hk) (half_lt_self hε))
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨mat_herm k w, fun x hx => ?_⟩
  let z : VR L N := Pi.single w x
  have hz : z ≠ 0 := fun h => hx (by simpa [z] using congrFun h w)
  have h1 := hk' z
  have h2 : qR k z = (star x ⬝ᵥ (mat k w *ᵥ x)).re := by
    simp only [qR, z]
    rw [Finset.sum_eq_single w]
    · simp
    · intro v _ hv
      simp [Pi.single_eq_of_ne hv]
    · simp
  have h3 : 0 < c * ‖z‖ ^ 2 := by
    have : 0 < ‖z‖ := norm_pos_iff.2 hz
    positivity
  rw [Complex.lt_def]
  refine ⟨by simp only [Complex.zero_re]; linarith, ?_⟩
  have h4 := (mat_herm k w).im_star_dotProduct_mulVec_self x
  simp only [Complex.zero_im]
  exact h4.symm

end PositivityTheory.KB.LocalOverlapAverage

end
end

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped ENNReal NNReal

namespace PositivityTheory.KB.LocalOverlapAverage

theorem cs_bound {α : Type} [MeasurableSpace α] (μ : Measure α) (K : Set α) (f : α → ℝ≥0∞)
    (hf : AEMeasurable f (μ.restrict K)) :
    ∫⁻ x in K, f x ∂μ ≤ (∫⁻ x in K, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (μ K) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict K) Real.HolderConjugate.two_two hf
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simpa [ENNReal.rpow_two, Measure.restrict_apply_univ] using h

theorem ofReal_norm_sq {E : Type} [NormedAddCommGroup E] (v : E) :
    ENNReal.ofReal (‖v‖ ^ 2) = (‖v‖₊ : ℝ≥0∞) ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg v)]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]

instance countable_O (L : Type) [Field L] [NumberField L] : Countable (𝓞 L) :=
  (RingOfIntegers.basis L).equivFun.toEquiv.injective.countable

instance countable_SL (L : Type) [Field L] [NumberField L] (N : ℕ) :
    Countable (Matrix.SpecialLinearGroup (Fin N) (𝓞 L)) :=
  @Function.Injective.countable _ (Fin N → Fin N → 𝓞 L) _
    (fun A : Matrix.SpecialLinearGroup (Fin N) (𝓞 L) => ((A : Matrix (Fin N) (Fin N) (𝓞 L)) : Fin N → Fin N → 𝓞 L))
    Subtype.val_injective

instance countable_latS (L : Type) [Field L] [NumberField L] (N : ℕ) : Countable (latS L N) := by
  unfold latS
  exact (MonoidHom.rangeRestrict_surjective _).countable

private theorem integral_abs_intS_actL_le_mul_sqrt_integral (hS : SimpBd) (hU : Unfold) (hDi : Discr) (hO : OverlapG)
    {L : Type} [Field L] [NumberField L] {N k : ℕ} (hN : 1 ≤ N) (d : Dom L N)
    (μ : Measure (HS L N)) [μ.IsAddHaarMeasure] (B : Set (HS L N)) (hB : IsCompact B)
    (hBP : B ⊆ Pos L N) (h : Fin (k + 2) → Gp L N) :
    ∃ C : ℝ, ∀ ω : Form (HS L N) (k + 1), ContinuousOn ω (Pos L N) →
      (∀ γ : Gm L N, FInv ω (emb L N γ)) → (∀ s : InfinitePlace L → ℂˣ, FInv ω (scal L N s)) →
      IntegrableOn (fun x : Sp L N => ‖fr ω (ofS L N x)‖ ^ 2) d.D d.μ →
      ∫ y : Fin (k + 2) → HS L N, |intS ω (fun j => actL (h j) (y j))|
          ∂(Measure.pi fun _ => nrm μ B)
        ≤ C * √(∫ x in d.D, ‖fr ω (ofS L N x)‖ ^ 2 ∂d.μ) := by
  obtain ⟨C₁, hC₁⟩ := hS (HS L N) μ (k + 1) (fun j => actEq (h j)) B hB
  have hKeq : Kset (fun j => ((actEq (h j) : HS L N ≃L[ℝ] HS L N) : HS L N →L[ℝ] HS L N)) B
      = Kset (fun j => actL (h j)) B := by
    congr 1
  have hKP : Kset (fun j => actL (h j)) B ⊆ Pos L N := kset_sub h hBP
  have hKc : IsCompact (Kset (fun j => actL (h j)) B) := isCompact_kset _ hB
  obtain ⟨C₂, K', hC₂, hK'c, hC₂b⟩ := hU L N (k + 1) hN d μ _ hKc hKP
  haveI := d.haar
  obtain ⟨M, hM⟩ := hO (Sp L N) (latS L N) d.μ d.D d.fund (hDi L N) K' hK'c
  refine ⟨max C₁ 0 * C₂.toReal * M * ((d.μ d.D) ^ (1 / 2 : ℝ)).toReal, ?_⟩
  intro ω hωc hΓ hsc hint
  have hωK : ContinuousOn ω (Kset (fun j => actL (h j)) B) := hωc.mono hKP
  obtain ⟨-, hbd⟩ := hC₁ ω (hKeq ▸ hωK)
  rw [hKeq] at hbd
  simp only [actEq_apply] at hbd
  have hfc : Continuous fun x : Sp L N => fr ω (ofS L N x) := (cont_fr ω hωc).comp cont_ofS
  set f : Sp L N → ℝ≥0∞ := fun x => (‖fr ω (ofS L N x)‖₊ : ℝ≥0∞) with hf
  have hfm : Measurable f := (ENNReal.continuous_coe.comp hfc.nnnorm).measurable
  have hfinv : ∀ γ ∈ latS L N, ∀ x : Sp L N, f (γ * x) = f x := by
    intro γ hγ x
    obtain ⟨A, hA⟩ := ofS_lat hγ
    simp only [hf, map_mul, hA, fr_mul ω _ _ (hΓ A)]
  have hOv := hM f hfm hfinv
  have hUn := hC₂b ω hωc hsc
  have hcs := cs_bound d.μ d.D f hfm.aemeasurable
  have hsq : ∫⁻ x in d.D, f x ^ 2 ∂d.μ
      = ENNReal.ofReal (∫ x in d.D, ‖fr ω (ofS L N x)‖ ^ 2 ∂d.μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => by positivity)]
    congr 1
    funext x
    rw [ofReal_norm_sq]
  set I := ∫ x in d.D, ‖fr ω (ofS L N x)‖ ^ 2 ∂d.μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => by positivity
  have hμD : d.μ d.D ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) d.fin.ne
  have hchain : ENNReal.ofReal (∫ y : Fin (k + 2) → HS L N, |intS ω (fun j => actL (h j) (y j))|
        ∂(Measure.pi fun _ => nrm μ B))
      ≤ ENNReal.ofReal (max C₁ 0) * (C₂ * (M * (ENNReal.ofReal I ^ (1 / 2 : ℝ)
          * d.μ d.D ^ (1 / 2 : ℝ)))) := by
    calc _ ≤ _ := hbd
      _ ≤ ENNReal.ofReal (max C₁ 0) * (C₂ * ∫⁻ x in K', f x ∂d.μ) := by
        gcongr
        exact le_max_left _ _
      _ ≤ ENNReal.ofReal (max C₁ 0) * (C₂ * (M * ∫⁻ x in d.D, f x ∂d.μ)) := by
        gcongr
      _ ≤ _ := by
        gcongr
        rw [← hsq]
        exact hcs
  have hR : ENNReal.ofReal (max C₁ 0) * (C₂ * (M * (ENNReal.ofReal I ^ (1 / 2 : ℝ)
          * d.μ d.D ^ (1 / 2 : ℝ))))
      = ENNReal.ofReal (max C₁ 0 * C₂.toReal * M * ((d.μ d.D) ^ (1 / 2 : ℝ)).toReal * √I) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hI0 (by norm_num), ← Real.sqrt_eq_rpow]
    rw [ENNReal.ofReal_mul, ENNReal.ofReal_mul, ENNReal.ofReal_mul, ENNReal.ofReal_mul,
      ENNReal.ofReal_toReal hC₂, ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hμD]
    · ring
    all_goals positivity
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (hchain.trans_eq hR)

theorem sLoc_of_parts (hA : AvgS) (hS : SimpBd) (hU : Unfold) (hDi : Discr) (hO : OverlapG) : SLoc := by
  intro L _ _ N k hN d z hz
  classical
  obtain ⟨r, hr, hrP⟩ := ball_pos (L := L) (N := N)
  set B : Set (HS L N) := Metric.closedBall ((one L N : HS L N)) r with hBdef
  have hB : IsCompact B := isCompact_closedBall _ _
  set μ : Measure (HS L N) := Measure.addHaar with hμ
  have hμB0 : μ B ≠ 0 := (Metric.measure_closedBall_pos μ _ hr).ne'
  have hμBt : μ B ≠ ⊤ := hB.measure_lt_top.ne
  haveI hP : IsProbabilityMeasure (nrm μ B) :=
    ⟨by simp [nrm, ENNReal.inv_mul_cancel hμB0 hμBt]⟩
  have h1B : ((one L N : HS L N)) ∈ B := Metric.mem_closedBall_self hr.le
  let e : HS L N → ↑(Pos L N) := fun x => if hx : x ∈ Pos L N then ⟨x, hx⟩ else one L N
  have hcoe : ∀ x ∈ Pos L N, ((e x : ↑(Pos L N)) : HS L N) = x := by
    intro x hx
    simp [e, hx]
  have hae : ∀ᵐ x ∂(Measure.pi fun _ : Fin (k + 2) => nrm μ B), ∀ j, x j ∈ B := by
    rw [Filter.eventually_all]
    intro j
    have h0 : ∀ᵐ y ∂(nrm μ B), y ∈ B := by
      unfold nrm
      exact Measure.ae_smul_measure (ae_restrict_mem hB.measurableSet) _
    exact (Measure.tendsto_eval_ae_ae (i := j)).eventually h0
  have hKeq : ∀ h : Fin (k + 2) → Gp L N,
      Kset (fun j => ((actEq (h j) : HS L N ≃L[ℝ] HS L N) : HS L N →L[ℝ] HS L N)) B
        = Kset (fun j => actL (h j)) B := by
    intro h
    congr 1
  choose C hC using fun g : Fin (k + 1) → Gm L N =>
    integral_abs_intS_actL_le_mul_sqrt_integral hS hU hDi hO hN d μ B hB hrP (fun j => emb L N (Fin.partialProd g j))
  refine ⟨∑ g ∈ z.support, |z g| * C g, ?_⟩
  intro ω hgood hΓ hsc hint
  have hInv : Inv (emb L N) (intP ω) := fun g y => intP_inv ω (emb L N g) (hΓ g) y
  have hintg : ∀ (h : Fin (k + 2) → Gp L N) (b : Fin (k + 2) → Bool),
      Integrable (fun x : Fin (k + 2) → HS L N =>
        intP ω fun j => h j • if b j = true then e (x j) else one L N)
        (Measure.pi fun _ => nrm μ B) := by
    intro h b
    obtain ⟨C₁, hC₁⟩ := hS (HS L N) μ (k + 1) (fun j => actEq (h j)) B hB
    obtain ⟨hi, -⟩ := hC₁ ω ((hKeq h) ▸ hgood.1.mono (kset_sub h hrP))
    refine (hi b _ h1B).congr ?_
    filter_upwards [hae] with x hx
    show intS ω _ = intS ω _
    congr 1
    funext j
    rw [actEq_apply]
    show _ = actL (h j) ((if b j = true then e (x j) else one L N : ↑(Pos L N)) : HS L N)
    by_cases hb : b j = true
    · simp only [hb, if_true, hcoe _ (hrP (hx j))]
    · simp only [hb]
      rfl
  have hev := hA (Gm L N) (Gp L N) ↑(Pos L N) (HS L N) (emb L N) k (intP ω) (nrm μ B) e
    (one L N) hInv hgood.2 hintg z hz
  rw [hev]
  have key : ∀ g : Fin (k + 1) → Gm L N,
      |∫ x : Fin (k + 2) → HS L N, intP ω (fun j => emb L N (Fin.partialProd g j) • e (x j))
          ∂(Measure.pi fun _ => nrm μ B)|
        ≤ C g * √(∫ x in d.D, ‖fr ω (ofS L N x)‖ ^ 2 ∂d.μ) := by
    intro g
    calc _ ≤ ∫ x : Fin (k + 2) → HS L N,
          |intP ω (fun j => emb L N (Fin.partialProd g j) • e (x j))|
          ∂(Measure.pi fun _ => nrm μ B) := abs_integral_le_integral_abs
      _ = ∫ y : Fin (k + 2) → HS L N,
          |intS ω (fun j => actL (emb L N (Fin.partialProd g j)) (y j))|
          ∂(Measure.pi fun _ => nrm μ B) := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with x hx
        show |intS ω _| = |intS ω _|
        congr 2
        funext j
        show actL _ ((e (x j) : ↑(Pos L N)) : HS L N) = _
        rw [hcoe _ (hrP (hx j))]
      _ ≤ _ := hC g ω hgood.1 hΓ hsc hint
  unfold Finsupp.sum
  calc _ ≤ ∑ g ∈ z.support, |z g * ∫ x : Fin (k + 2) → HS L N,
          intP ω (fun j => emb L N (Fin.partialProd g j) • e (x j))
          ∂(Measure.pi fun _ => nrm μ B)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ g ∈ z.support, |z g| * (C g * √(∫ x in d.D, ‖fr ω (ofS L N x)‖ ^ 2 ∂d.μ)) := by
      gcongr with g hg
      rw [abs_mul]
      gcongr
      exact key g
    _ = _ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      ring

end PositivityTheory.KB.LocalOverlapAverage

end
