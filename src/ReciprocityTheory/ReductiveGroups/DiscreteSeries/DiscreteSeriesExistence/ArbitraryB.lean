module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamLeOfKTypes

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ArbitraryA
noncomputable section

open Finset Matrix MeasureTheory
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

local instance : ProperSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.proper ℝ _

section Bump

def hsOne (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖(g - 1) i j‖ ^ 2

theorem sum_sq_norm_eq_trace (A : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, ‖A i j‖ ^ 2 = (trace (Aᴴ * A)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
    Complex.normSq_apply]
  ring

theorem hsOne_conj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : hsOne (k * g * star k) = hsOne g := by
  have h1' : k * kᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 hk
    rwa [Matrix.star_eq_conjTranspose] at this
  have h2 : kᴴ * k = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hk
    rwa [Matrix.star_eq_conjTranspose] at this
  have e : k * g * star k - 1 = k * (g - 1) * kᴴ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1']
  have e2 : (k * (g - 1) * kᴴ)ᴴ * (k * (g - 1) * kᴴ) = k * ((g - 1)ᴴ * (g - 1)) * kᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc kᴴ k, h2, Matrix.one_mul]
  unfold hsOne
  rw [sum_sq_norm_eq_trace, sum_sq_norm_eq_trace, e, e2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2,
    Matrix.one_mul]

theorem contDiff_entry (i j : Fin n) : ContDiff ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => g i j) :=
  (contDiff_apply ℝ (fun _ => ℂ) j).comp (contDiff_apply ℝ (fun _ => (Fin n → ℂ)) i)

theorem contDiff_hsOne : ContDiff ℝ ∞ (hsOne (n := n)) := by
  unfold hsOne
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact (contDiff_norm_sq ℂ).comp ((contDiff_entry i j).sub contDiff_const)

def arbB (r : ℝ) (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.smoothTransition (r ^ 2 - hsOne g)

theorem contDiff_arbB (r : ℝ) : ContDiff ℝ ∞ (arbB (n := n) r) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub contDiff_hsOne)

theorem arbB_nonneg (r : ℝ) (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ arbB r g :=
  Real.smoothTransition.nonneg _

theorem arbB_one_pos {r : ℝ} (hr : 0 < r) : 0 < arbB r (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have h0 : hsOne (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [hsOne]
  unfold arbB
  rw [h0, sub_zero]
  exact Real.smoothTransition.pos_of_pos (by positivity)

theorem norm_lt_of_arbB_ne {r : ℝ} (hr : 0 < r) {g : Matrix (Fin n) (Fin n) ℂ} (h : arbB r g ≠ 0) :
    ‖g - 1‖ < r := by
  have hlt : hsOne g < r ^ 2 := by
    by_contra hc
    push Not at hc
    exact h (Real.smoothTransition.zero_of_nonpos (by linarith))
  rw [Matrix.norm_lt_iff hr]
  intro i j
  have h1 : ‖(g - 1) i j‖ ^ 2 ≤ hsOne g := by
    unfold hsOne
    calc ‖(g - 1) i j‖ ^ 2 ≤ ∑ j', ‖(g - 1) i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖(g - 1) i j'‖ ^ 2) (fun _ _ => by positivity)
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖(g - 1) i' j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖(g - 1) i' j'‖ ^ 2) (fun _ _ => by positivity)
            (Finset.mem_univ i)
  have h3 : ‖(g - 1) i j‖ ^ 2 < r ^ 2 := lt_of_le_of_lt h1 hlt
  nlinarith [norm_nonneg ((g - 1) i j)]

theorem hasCompactSupport_arbB {r : ℝ} (hr : 0 < r) : HasCompactSupport (arbB (n := n) r) := by
  refine HasCompactSupport.intro (isCompact_closedBall (1 : Matrix (Fin n) (Fin n) ℂ) r) fun g hg => ?_
  by_contra h
  exact hg (by rw [Metric.mem_closedBall, dist_eq_norm]; exact (norm_lt_of_arbB_ne hr h).le)

theorem arbB_conj (r : ℝ) {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (g : Matrix (Fin n) (Fin n) ℂ) : arbB r (k * g * star k) = arbB r g := by
  unfold arbB
  rw [hsOne_conj hk.1]

end Bump

section Conv

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem arb_umat_cont : Continuous (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y) :=
  (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.continuous

theorem arb_umat_mem (y : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.umat y ∈ UJset ε := y.2

theorem arb_orbit_cont (hσ : IsURepOn (UJset ε) σ) (w : H) :
    Continuous (fun y : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat y) w) :=
  (hσ.2.2 w).comp_continuous arb_umat_cont arb_umat_mem

theorem arb_rep_mul (hσ : IsURepOn (UJset ε) σ) (a b : Formalism.REAL.UJ ε) (v : H) :
    σ (Formalism.MainNotions.S.umat (a * b)) v = σ (Formalism.MainNotions.S.umat a) (σ (Formalism.MainNotions.S.umat b) v) := by
  show σ (Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b) v = _
  rw [hσ.1.2 _ (arb_umat_mem a) _ (arb_umat_mem b), ContinuousLinearMap.comp_apply]

theorem arb_exists_umat {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ γ : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat γ = g := by
  have : g ∈ Set.range (fun y : Formalism.REAL.UJ ε => ((y : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [(Formalism.REAL.isClosedEmbeddingMatrix n ε).2]; exact hg
  exact this

theorem arb_integrable (hσ : IsURepOn (UJset ε) σ) (w : H) {α : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hα : Continuous α) (hαc : HasCompactSupport α) :
    Integrable (fun y : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat y) • σ (Formalism.MainNotions.S.umat y) w) (Formalism.REAL.muG ε) :=
  ((hα.comp arb_umat_cont).smul (arb_orbit_cont hσ w)).integrable_of_hasCompactSupport
    ((hαc.comp_isClosedEmbedding (Formalism.REAL.isClosedEmbeddingMatrix n ε).1).smul_right)

theorem opConv_add (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ} (hα : Continuous α)
    (hαc : HasCompactSupport α) (v w : H) :
    opConv ε σ α (v + w) = opConv ε σ α v + opConv ε σ α w := by
  unfold opConv
  rw [← integral_add (arb_integrable hσ v hα hαc) (arb_integrable hσ w hα hαc)]
  congr 1
  funext y
  rw [map_add (f := _), smul_add]

theorem opConv_smul {α : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ) (v : H) :
    opConv ε σ α (c • v) = c • opConv ε σ α v := by
  unfold opConv
  rw [← integral_smul]
  congr 1
  funext y
  rw [map_smul, smul_comm]

theorem opConv_comm_K (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ} (hα : Continuous α)
    (hαc : HasCompactSupport α) (hαK : IsAdKInv ε α) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (v : H) : σ k (opConv ε σ α v) = opConv ε σ α (σ k v) := by
  have hkU : k ∈ UJset ε := closure_inUJ_of_mem_Kset hk
  obtain ⟨κ, hκ⟩ := arb_exists_umat hkU
  have hku : kᴴ * k = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hk.1
    rwa [Matrix.star_eq_conjTranspose] at this
  have hku' : k * kᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 hk.1
    rwa [Matrix.star_eq_conjTranspose] at this
  have hinv : Formalism.MainNotions.S.umat κ⁻¹ = kᴴ := by
    have h3 : Formalism.MainNotions.S.umat κ⁻¹ * k = 1 := by
      rw [← hκ]
      show Formalism.MainNotions.S.umat (κ⁻¹ * κ) = 1
      rw [inv_mul_cancel]
      rfl
    calc Formalism.MainNotions.S.umat κ⁻¹ = Formalism.MainNotions.S.umat κ⁻¹ * (k * kᴴ) := by rw [hku', Matrix.mul_one]
      _ = kᴴ := by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  have hF : ∀ y : Formalism.REAL.UJ ε,
      σ k (α (Formalism.MainNotions.S.umat y) • σ (Formalism.MainNotions.S.umat y) v) =
        (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat z) • σ (Formalism.MainNotions.S.umat z) (σ k v)) (κ * (y * κ⁻¹)) := by
    intro y
    have e1 : Formalism.MainNotions.S.umat (κ * (y * κ⁻¹)) = k * Formalism.MainNotions.S.umat y * star k := by
      show Formalism.MainNotions.S.umat κ * (Formalism.MainNotions.S.umat y * Formalism.MainNotions.S.umat κ⁻¹) = _
      rw [hκ, hinv, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    have m1 : k * Formalism.MainNotions.S.umat y * star k ∈ UJset ε := e1 ▸ arb_umat_mem (κ * (y * κ⁻¹))
    have h4 : k * Formalism.MainNotions.S.umat y * star k * k = k * Formalism.MainNotions.S.umat y := by
      rw [Matrix.mul_assoc (k * _), Matrix.star_eq_conjTranspose, hku, Matrix.mul_one]
    have e2 : σ (k * Formalism.MainNotions.S.umat y * star k) (σ k v) = σ k (σ (Formalism.MainNotions.S.umat y) v) := by
      calc σ (k * Formalism.MainNotions.S.umat y * star k) (σ k v)
          = ((σ (k * Formalism.MainNotions.S.umat y * star k)).comp (σ k)) v := rfl
        _ = σ (k * Formalism.MainNotions.S.umat y * star k * k) v := by rw [hσ.1.2 _ m1 _ hkU]
        _ = σ (k * Formalism.MainNotions.S.umat y) v := by rw [h4]
        _ = σ k (σ (Formalism.MainNotions.S.umat y) v) := by
            rw [hσ.1.2 _ hkU _ (arb_umat_mem y)]
            rfl
    show _ = α (Formalism.MainNotions.S.umat (κ * (y * κ⁻¹))) • σ (Formalism.MainNotions.S.umat (κ * (y * κ⁻¹))) (σ k v)
    rw [e1, hαK k hk, e2, map_smul]
  unfold opConv
  rw [← ContinuousLinearMap.integral_comp_comm _ (arb_integrable hσ v hα hαc)]
  calc ∫ y, σ k (α (Formalism.MainNotions.S.umat y) • σ (Formalism.MainNotions.S.umat y) v) ∂(Formalism.REAL.muG ε)
      = ∫ y, (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat z) • σ (Formalism.MainNotions.S.umat z) (σ k v))
          (κ * (y * κ⁻¹)) ∂(Formalism.REAL.muG ε) := by
        congr 1
        funext y
        exact hF y
    _ = ∫ y, (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat z) • σ (Formalism.MainNotions.S.umat z) (σ k v))
          (κ * y) ∂(Formalism.REAL.muG ε) :=
        integral_mul_right_eq_self
          (fun y => (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat z) • σ (Formalism.MainNotions.S.umat z) (σ k v)) (κ * y)) κ⁻¹
    _ = ∫ y, α (Formalism.MainNotions.S.umat y) • σ (Formalism.MainNotions.S.umat y) (σ k v) ∂(Formalism.REAL.muG ε) :=
        integral_mul_left_eq_self
          (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat z) • σ (Formalism.MainNotions.S.umat z) (σ k v)) κ

theorem opConv_translate (hσ : IsURepOn (UJset ε) σ) (w : H) {α : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hα : Continuous α) (hαc : HasCompactSupport α) (γ : Formalism.REAL.UJ ε) :
    σ (Formalism.MainNotions.S.umat γ) (opConv ε σ α w) =
      ∫ y, α (Formalism.MainNotions.S.umat (γ⁻¹ * y)) • σ (Formalism.MainNotions.S.umat y) w ∂(Formalism.REAL.muG ε) := by
  unfold opConv
  rw [← ContinuousLinearMap.integral_comp_comm _ (arb_integrable hσ w hα hαc)]
  calc ∫ y, σ (Formalism.MainNotions.S.umat γ) (α (Formalism.MainNotions.S.umat y) • σ (Formalism.MainNotions.S.umat y) w) ∂(Formalism.REAL.muG ε)
      = ∫ y, (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat (γ⁻¹ * z)) • σ (Formalism.MainNotions.S.umat z) w) (γ * y)
          ∂(Formalism.REAL.muG ε) := by
        congr 1
        funext y
        show _ = α (Formalism.MainNotions.S.umat (γ⁻¹ * (γ * y))) • σ (Formalism.MainNotions.S.umat (γ * y)) w
        rw [inv_mul_cancel_left, map_smul, arb_rep_mul hσ]
    _ = _ := integral_mul_left_eq_self
          (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat (γ⁻¹ * z)) • σ (Formalism.MainNotions.S.umat z) w) γ

end Conv

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory
open scoped ContDiff Convolution

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

local instance : ProperSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.proper ℝ _

section Conv

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def arbMulB (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        (Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℝ] _).toLinearMap.comp
      (LinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)))

def arbSharp (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => Formalism.REAL.Jm ε * pᴴ * Formalism.REAL.Jm ε
      map_add' := fun p q => by simp [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r p => by simp [Matrix.conjTranspose_smul] }

theorem arbSharp_apply (p : Matrix (Fin n) (Fin n) ℂ) :
    arbSharp ε p = Formalism.REAL.Jm ε * pᴴ * Formalism.REAL.Jm ε := rfl

theorem arb_umat_inv (γ : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.umat γ⁻¹ = arbSharp ε (Formalism.MainNotions.S.umat γ) := by
  rw [arbSharp_apply]
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hγ : (Formalism.MainNotions.S.umat γ)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.umat γ = Formalism.REAL.Jm ε := γ.2
  have hinv : Formalism.MainNotions.S.umat γ * Formalism.MainNotions.S.umat γ⁻¹ = 1 := by
    show ((γ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      (((γ⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  symm
  calc Formalism.REAL.Jm ε * (Formalism.MainNotions.S.umat γ)ᴴ * Formalism.REAL.Jm ε
      = Formalism.REAL.Jm ε * (Formalism.MainNotions.S.umat γ)ᴴ * Formalism.REAL.Jm ε * (Formalism.MainNotions.S.umat γ * Formalism.MainNotions.S.umat γ⁻¹) := by
        rw [hinv, Matrix.mul_one]
    _ = Formalism.REAL.Jm ε * ((Formalism.MainNotions.S.umat γ)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat γ⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.MainNotions.S.umat γ⁻¹ := by
        rw [hγ, hJ, Matrix.one_mul]

@[reducible] def arbMS (n : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _

attribute [local instance] arbMS

local instance : BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩

theorem arb_locInt (hσ : IsURepOn (UJset ε) σ) (w : H) :
    LocallyIntegrable (fun m : Matrix (Fin n) (Fin n) ℂ => σ m w)
      ((Formalism.REAL.muG ε).map (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y)) := by
  have hemb : MeasurableEmbedding (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.measurableEmbedding
  intro x
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
  rw [hemb.integrableOn_map_iff]
  exact (arb_orbit_cont hσ w).continuousOn.integrableOn_compact
    ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isCompact_preimage (isCompact_closedBall x 1))

theorem arb_param_integral {E P V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [hB : BorelSpace E] [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] {μ : Measure E} {f : E → V} (hf : LocallyIntegrable f μ)
    {Ψ : P → E → ℂ} {k : Set E} (hk : IsCompact k) (hΨ0 : ∀ p x, x ∉ k → Ψ p x = 0)
    (hΨ : ContDiff ℝ ∞ (Function.uncurry Ψ)) : ContDiff ℝ ∞ (fun p => ∫ y, Ψ p y • f y ∂μ) := by
  have key := contDiffOn_convolution_right_with_param_comp (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (μ := μ)
    ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] V →L[ℝ] V).flip) (s := (Set.univ : Set P))
    (v := fun _ => (0 : E)) contDiffOn_const (f := f) (g := fun p x => Ψ p (-x))
    (k := Set.image (fun x : E => -x) k) isOpen_univ (hk.image continuous_neg)
    (fun p x _ hx => hΨ0 p (-x) (by simpa using hx)) hf
    (hΨ.comp (contDiff_fst.prodMk contDiff_snd.neg)).contDiffOn
  rw [contDiffOn_univ] at key
  convert key using 1
  funext p
  simp [MeasureTheory.convolution]

theorem opConv_smooth (hσ : IsURepOn (UJset ε) σ) (w : H) {α : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hα : ContDiff ℝ ∞ α) (hαc : HasCompactSupport α) : IsSmoothVecU ε σ (opConv ε σ α w) := by
  unfold IsSmoothVecU S7.SmoothOnGV
  intro g₀ _
  set K₀ : Set (Matrix (Fin n) (Fin n) ℂ) :=
    (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2) ''
      (Metric.closedBall g₀ 1 ×ˢ tsupport α) with hK₀
  have hK₀c : IsCompact K₀ :=
    ((isCompact_closedBall g₀ 1).prod hαc.isCompact).image (continuous_fst.matrix_mul continuous_snd)
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ K₀ ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hR⟩ := hK₀c.isBounded.subset_closedBall 0
    exact ⟨max R 1, by positivity, hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  let χ : ContDiffBump (0 : Matrix (Fin n) (Fin n) ℂ) := ⟨R, R + 1, hR0, by linarith⟩
  let Ψ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → ℂ :=
    fun p y => (χ y : ℂ) * α (arbSharp ε p * y)
  have hΨ : ContDiff ℝ ∞ (Function.uncurry Ψ) := by
    apply ContDiff.mul
    · exact Complex.ofRealCLM.contDiff.comp (χ.contDiff.comp contDiff_snd)
    · exact hα.comp
        (((arbMulB n).contDiff.comp ((arbSharp ε).contDiff.comp contDiff_fst)).clm_apply contDiff_snd)
  have key : ContDiff ℝ ∞ (fun p => ∫ y, Ψ p y • σ y w
      ∂((Formalism.REAL.muG ε).map (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y))) :=
    arb_param_integral (hB := ⟨rfl⟩) (arb_locInt hσ w) (k := tsupport χ) χ.hasCompactSupport.isCompact
      (fun p x hx => by
        have : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [Ψ, this]) hΨ
  refine ⟨Metric.ball g₀ 1, fun p => ∫ y, Ψ p y • σ y w
      ∂((Formalism.REAL.muG ε).map (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y)),
    Metric.isOpen_ball, Metric.mem_ball_self one_pos, key.contDiffOn, ?_⟩
  · intro g hg hgU
    obtain ⟨γ, rfl⟩ := arb_exists_umat (ε := ε) hgU
    beta_reduce
    rw [opConv_translate hσ w hα.continuous hαc γ, (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.integral_map]
    congr 1
    funext y
    show α (Formalism.MainNotions.S.umat (γ⁻¹ * y)) • _ =
      ((χ (Formalism.MainNotions.S.umat y) : ℂ) * α (arbSharp ε (Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat y)) • _
    have e1 : Formalism.MainNotions.S.umat (γ⁻¹ * y) = arbSharp ε (Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat y := by
      show Formalism.MainNotions.S.umat γ⁻¹ * Formalism.MainNotions.S.umat y = _
      rw [arb_umat_inv]
    rw [e1]
    by_cases h0 : α (arbSharp ε (Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat y) = 0
    · rw [h0]
      simp
    · have hy : Formalism.MainNotions.S.umat y ∈ K₀ := by
        refine ⟨(Formalism.MainNotions.S.umat γ, arbSharp ε (Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat y),
          ⟨Metric.ball_subset_closedBall hg, subset_tsupport _ h0⟩, ?_⟩
        show Formalism.MainNotions.S.umat γ * (arbSharp ε (Formalism.MainNotions.S.umat γ) * Formalism.MainNotions.S.umat y) = Formalism.MainNotions.S.umat y
        rw [← Matrix.mul_assoc, ← arb_umat_inv]
        show Formalism.MainNotions.S.umat (γ * γ⁻¹) * Formalism.MainNotions.S.umat y = Formalism.MainNotions.S.umat y
        rw [mul_inv_cancel]
        exact Matrix.one_mul _
      have : χ (Formalism.MainNotions.S.umat y) = 1 := χ.one_of_mem_closedBall (hR hy)
      rw [this]
      simp

theorem exists_good_moll (hσ : IsURepOn (UJset ε) σ) (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    ∃ α : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ IsAdKInv ε α ∧
      ∀ w ∈ S, ‖opConv ε σ α w - w‖ ≤ ‖w‖ / 2 := by
  let f : Matrix (Fin n) (Fin n) ℂ → (S →L[ℂ] H) := fun g => (σ g).comp S.subtypeL - S.subtypeL
  have hf : ContinuousOn f (UJset ε) := by
    rw [continuousOn_clm_apply]
    intro y
    refine ContinuousOn.congr (f := fun x => σ x (y : H) - (y : H))
      ((hσ.2.2 (y : H)).sub (continuousOn_const (c := (y : H)))) fun x _ => ?_
    simp [f]
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := arb_umat_mem (1 : Formalism.REAL.UJ ε)
  have hf1 : f 1 = 0 := by
    ext y
    simp [f, hσ.1.1]
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousOn_iff.1 hf 1 h1 (1 / 2) (by norm_num)
  have hclose : ∀ g ∈ UJset ε, ‖g - 1‖ < δ → ∀ w ∈ S, ‖σ g w - w‖ ≤ ‖w‖ / 2 := by
    intro g hg hgd w hw
    have h2 := hδf g hg (by rwa [dist_eq_norm])
    rw [hf1, dist_zero_right] at h2
    have h3 : σ g w - w = f g ⟨w, hw⟩ := by simp [f]
    rw [h3]
    calc ‖f g ⟨w, hw⟩‖ ≤ ‖f g‖ * ‖(⟨w, hw⟩ : S)‖ := (f g).le_opNorm _
      _ ≤ (1 / 2) * ‖(⟨w, hw⟩ : S)‖ := mul_le_mul_of_nonneg_right h2.le (norm_nonneg _)
      _ = ‖w‖ / 2 := by rw [show ‖(⟨w, hw⟩ : S)‖ = ‖w‖ from rfl]; ring
  have hbc : Continuous (fun y : Formalism.REAL.UJ ε => arbB δ (Formalism.MainNotions.S.umat y)) :=
    (contDiff_arbB δ).continuous.comp arb_umat_cont
  have hbs : HasCompactSupport (fun y : Formalism.REAL.UJ ε => arbB δ (Formalism.MainNotions.S.umat y)) :=
    (hasCompactSupport_arbB hδ).comp_isClosedEmbedding (Formalism.REAL.isClosedEmbeddingMatrix n ε).1
  set c : ℝ := ∫ y, arbB δ (Formalism.MainNotions.S.umat y) ∂(Formalism.REAL.muG ε) with hc
  have hcpos : 0 < c :=
    hbc.integral_pos_of_hasCompactSupport_nonneg_nonzero hbs (fun y => arbB_nonneg δ _)
      (x := (1 : Formalism.REAL.UJ ε)) (arbB_one_pos hδ).ne'
  have hφc : Continuous (fun y : Formalism.REAL.UJ ε => arbB δ (Formalism.MainNotions.S.umat y) / c) := hbc.div_const c
  have hφs : HasCompactSupport (fun y : Formalism.REAL.UJ ε => arbB δ (Formalism.MainNotions.S.umat y) / c) :=
    ((hasCompactSupport_arbB hδ).comp_left (g := fun t : ℝ => t / c) (by simp)).comp_isClosedEmbedding
      (Formalism.REAL.isClosedEmbeddingMatrix n ε).1
  have hbi : Integrable (fun y : Formalism.REAL.UJ ε => arbB δ (Formalism.MainNotions.S.umat y) / c) (Formalism.REAL.muG ε) :=
    hφc.integrable_of_hasCompactSupport hφs
  have hint1 : ∫ y, arbB δ (Formalism.MainNotions.S.umat y) / c ∂(Formalism.REAL.muG ε) = 1 := by
    rw [integral_div, ← hc, div_self hcpos.ne']
  refine ⟨fun g => ((arbB δ g / c : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((contDiff_arbB δ).div_const c)
  · exact (hasCompactSupport_arbB hδ).comp_left (g := fun t : ℝ => ((t / c : ℝ) : ℂ)) (by simp)
  · intro k hk g
    simp only [arbB_conj δ hk g]
  · intro w hw
    have hsm : ∀ y : Formalism.REAL.UJ ε, ((arbB δ (Formalism.MainNotions.S.umat y) / c : ℝ) : ℂ) • σ (Formalism.MainNotions.S.umat y) w =
        (arbB δ (Formalism.MainNotions.S.umat y) / c) • σ (Formalism.MainNotions.S.umat y) w := fun y =>
      (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm
    have hi2 : Integrable (fun y : Formalism.REAL.UJ ε => (arbB δ (Formalism.MainNotions.S.umat y) / c) • σ (Formalism.MainNotions.S.umat y) w)
        (Formalism.REAL.muG ε) :=
      (hφc.smul (arb_orbit_cont hσ w)).integrable_of_hasCompactSupport hφs.smul_right
    have hi3 : Integrable (fun y : Formalism.REAL.UJ ε => (arbB δ (Formalism.MainNotions.S.umat y) / c) • w) (Formalism.REAL.muG ε) :=
      hbi.smul_const w
    have e : opConv ε σ (fun g => ((arbB δ g / c : ℝ) : ℂ)) w - w =
        ∫ y, (arbB δ (Formalism.MainNotions.S.umat y) / c) • (σ (Formalism.MainNotions.S.umat y) w - w) ∂(Formalism.REAL.muG ε) := by
      unfold opConv
      simp only [hsm]
      calc (∫ y, (arbB δ (Formalism.MainNotions.S.umat y) / c) • σ (Formalism.MainNotions.S.umat y) w ∂(Formalism.REAL.muG ε)) - w
          = (∫ y, (arbB δ (Formalism.MainNotions.S.umat y) / c) • σ (Formalism.MainNotions.S.umat y) w ∂(Formalism.REAL.muG ε)) -
              ∫ y, (arbB δ (Formalism.MainNotions.S.umat y) / c) • w ∂(Formalism.REAL.muG ε) := by
            rw [integral_smul_const, hint1, one_smul]
        _ = _ := by
            rw [← integral_sub hi2 hi3]
            congr 1
            funext y
            rw [smul_sub]
    rw [e]
    calc ‖∫ y, (arbB δ (Formalism.MainNotions.S.umat y) / c) • (σ (Formalism.MainNotions.S.umat y) w - w) ∂(Formalism.REAL.muG ε)‖
        ≤ ∫ y, (arbB δ (Formalism.MainNotions.S.umat y) / c) * (‖w‖ / 2) ∂(Formalism.REAL.muG ε) := by
          refine norm_integral_le_of_norm_le (hbi.mul_const _) (Filter.Eventually.of_forall fun y => ?_)
          have hnn : 0 ≤ arbB δ (Formalism.MainNotions.S.umat y) / c := div_nonneg (arbB_nonneg δ _) hcpos.le
          rw [norm_smul, Real.norm_of_nonneg hnn]
          by_cases h0 : arbB δ (Formalism.MainNotions.S.umat y) = 0
          · simp [h0]
          · exact mul_le_mul_of_nonneg_left
              (hclose _ (arb_umat_mem y) (norm_lt_of_arbB_ne hδ h0) w hw) hnn
      _ = ‖w‖ / 2 := by rw [integral_mul_const, hint1, one_mul]

theorem exists_moll_data (hσ : IsURepOn (UJset ε) σ) (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    ∃ α : Matrix (Fin n) (Fin n) ℂ → ℂ,
      (∀ v w : H, opConv ε σ α (v + w) = opConv ε σ α v + opConv ε σ α w) ∧
      (∀ (c : ℂ) (v : H), opConv ε σ α (c • v) = c • opConv ε σ α v) ∧
      (∀ k ∈ Kset ε, ∀ v : H, σ k (opConv ε σ α v) = opConv ε σ α (σ k v)) ∧
      (∀ v : H, IsSmoothVecU ε σ (opConv ε σ α v)) ∧
      ∀ w ∈ S, ‖opConv ε σ α w - w‖ ≤ ‖w‖ / 2 := by
  obtain ⟨α, hαs, hαc, hαK, hS⟩ := exists_good_moll hσ S
  exact ⟨α, fun v w => opConv_add hσ hαs.continuous hαc v w, fun c v => opConv_smul c v,
    fun k hk v => opConv_comm_K hσ hαs.continuous hαc hαK hk v,
    fun v => opConv_smooth hσ v hαs hαc, hS⟩

end Conv

end ReciprocityTheory.ChartRestriction.DS
