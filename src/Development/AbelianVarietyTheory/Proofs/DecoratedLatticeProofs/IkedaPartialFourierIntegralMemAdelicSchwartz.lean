module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyConstantPartial
noncomputable section

open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff

namespace GlobalTheory.PartialIntegral

section Real

variable {X A : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup A] [NormedSpace ℝ A] (μ : Measure X) [μ.IsAddHaarMeasure]

theorem exists_majorant {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) (k : ℕ) :
    ∃ b : X → ℝ, Integrable b μ ∧ ∀ x a, ‖a‖ ^ k * ‖F (x, a)‖ ≤ b x := by
  set N : ℕ := Module.finrank ℝ X + 1 with hN
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z : X × A, (1 + ‖z‖) ^ (k + N) * ‖F z‖ ≤ C := by
    have := fun z =>
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k + N, 0)) (k := k + N) (n := 0) le_rfl le_rfl F z
    simp only [norm_iteratedFDeriv_zero] at this
    exact ⟨_, this⟩
  refine ⟨fun x => C * (1 + ‖x‖) ^ (-(N : ℝ)), (integrable_one_add_norm (by rw [hN]; push_cast; linarith)).const_mul C,
    fun x a => ?_⟩
  have hp : 0 < 1 + ‖x‖ := by positivity
  show _ ≤ C * (1 + ‖x‖) ^ (-(N : ℝ))
  rw [Real.rpow_neg hp.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  refine le_trans ?_ (hC (x, a))
  have h1 : ‖a‖ ≤ 1 + ‖(x, a)‖ := by have := norm_snd_le (x, a); simp only at this; linarith
  have h2 : 1 + ‖x‖ ≤ 1 + ‖(x, a)‖ := by have := norm_fst_le (x, a); simp only at this; linarith
  rw [pow_add _ k N, mul_right_comm]
  gcongr

theorem continuous_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) (a : A) :
    Continuous fun x => F (x, a) := F.continuous.comp (continuous_id.prodMk continuous_const)

theorem integrable_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) (a : A) :
    Integrable (fun x => F (x, a)) μ := by
  obtain ⟨b, hb, h⟩ := exists_majorant μ F 0
  exact hb.mono' (continuous_slice F a).aestronglyMeasurable (Eventually.of_forall fun x => by simpa using h x a)

def dSnd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) : 𝓢(X × A, A →L[ℝ] E) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) ((ContinuousLinearMap.compL ℝ A (X × A) E).flip (ContinuousLinearMap.inr ℝ X A))
    (SchwartzMap.fderivCLM ℝ (X × A) E F)

theorem hasFDerivAt_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) (x : X) (a : A) :
    HasFDerivAt (fun a => F (x, a)) (dSnd F (x, a)) a :=
  (F.differentiable (x, a)).hasFDerivAt.comp a (hasFDerivAt_prodMk_right x a)

theorem hasFDerivAt_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) (a : A) :
    HasFDerivAt (fun a => ∫ x, F (x, a) ∂μ) (∫ x, dSnd F (x, a) ∂μ) a := by
  obtain ⟨b, hb, h⟩ := exists_majorant μ (dSnd F) 0
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun a x => F (x, a)) (F' := fun a x => dSnd F (x, a))
    (s := Set.univ) (bound := b) univ_mem
    (Eventually.of_forall fun a => (continuous_slice F a).aestronglyMeasurable) (integrable_slice μ F a)
    (continuous_slice (dSnd F) a).aestronglyMeasurable
    (Eventually.of_forall fun x a _ => by simpa using h x a) hb
    (Eventually.of_forall fun x a _ => hasFDerivAt_slice F x a)

theorem smooth_decay (n : ℕ) : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)),
    ContDiff ℝ n (fun a => ∫ x, F (x, a) ∂μ) ∧
      ∀ k : ℕ, ∃ C : ℝ, ∀ a, ‖a‖ ^ k * ‖iteratedFDeriv ℝ n (fun a => ∫ x, F (x, a) ∂μ) a‖ ≤ C := by
  induction n with
  | zero =>
    intro E _ _ F
    refine ⟨contDiff_zero.2 (continuous_iff_continuousAt.2 fun a => (hasFDerivAt_integral μ F a).continuousAt), fun k => ?_⟩
    obtain ⟨b, hb, h⟩ := exists_majorant μ F k
    refine ⟨∫ x, b x ∂μ, fun a => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    calc ‖a‖ ^ k * ‖∫ x, F (x, a) ∂μ‖ ≤ ‖a‖ ^ k * ∫ x, ‖F (x, a)‖ ∂μ := by
          gcongr
          exact norm_integral_le_integral_norm _
      _ = ∫ x, ‖a‖ ^ k * ‖F (x, a)‖ ∂μ := (integral_const_mul _ _).symm
      _ ≤ _ := integral_mono ((integrable_slice μ F a).norm.const_mul _) hb fun x => h x a
  | succ n ih =>
    intro E _ _ F
    obtain ⟨h1, h2⟩ := ih _ (dSnd F)
    have e : fderiv ℝ (fun a => ∫ x, F (x, a) ∂μ) = fun a => ∫ x, dSnd F (x, a) ∂μ :=
      funext fun a => (hasFDerivAt_integral μ F a).fderiv
    refine ⟨?_, fun k => ?_⟩
    · rw [Nat.cast_succ, contDiff_succ_iff_fderiv, e]
      exact ⟨fun a => (hasFDerivAt_integral μ F a).differentiableAt, by simp, h1⟩
    · obtain ⟨C, hC⟩ := h2 k
      exact ⟨C, fun a => by rw [← norm_iteratedFDeriv_fderiv, e]; exact hC a⟩

def intFst {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) : 𝓢(A, E) where
  toFun a := ∫ x, F (x, a) ∂μ
  smooth' := contDiff_infty.2 fun n => (smooth_decay μ n E F).1
  decay' k n := (smooth_decay μ n E F).2 k

theorem schwartz_partial [FiniteDimensional ℝ A] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : 𝓢(V, ℂ))
    (L₁ : X →ₗ[ℝ] V) (L₂ : A →ₗ[ℝ] V) (hL : ∀ x a, L₁ x + L₂ a = 0 → x = 0 ∧ a = 0) :
    (∀ a, Integrable (fun x => f (L₁ x + L₂ a)) μ) ∧ ∃ h : 𝓢(A, ℂ), ∀ a, h a = ∫ x, f (L₁ x + L₂ a) ∂μ := by
  let L : (X × A) →L[ℝ] V := LinearMap.toContinuousLinearMap (L₁.coprod L₂)
  obtain ⟨K, -, hK⟩ := LinearMap.exists_antilipschitzWith (L₁.coprod L₂)
    (LinearMap.ker_eq_bot'.2 fun z hz => Prod.ext (hL z.1 z.2 hz).1 (hL z.1 z.2 hz).2)
  let F : 𝓢(X × A, ℂ) := SchwartzMap.compCLMOfAntilipschitz ℂ (g := L) L.hasTemperateGrowth hK f
  exact ⟨fun a => integrable_slice μ F a, intFst μ F, fun a => rfl⟩

end Real

section Finite

variable {Y B W : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] [TopologicalSpace B] [T2Space B] [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  (ν : Measure Y) [ν.IsAddHaarMeasure]

theorem eventually_invariant {g : W → ℂ} (h1 : IsLocallyConstant g) (h2 : HasCompactSupport g) :
    ∀ᶠ u in 𝓝 (0 : W), ∀ x, g (x + u) = g x := by
  have h : ∀ᶠ u in 𝓝 (0 : W), ∀ x ∈ tsupport g, g (x + u) = g x ∧ g (x - u) = g x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : W × W => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : W × W => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : W × W => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  filter_upwards [h] with u hu x
  by_cases hx : x ∈ tsupport g
  · exact (hu x hx).1
  · by_cases hx' : x + u ∈ tsupport g
    · have := (hu _ hx').2
      rw [add_sub_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem locallyConstant_partial {g : W → ℂ} (h1 : IsLocallyConstant g) (h2 : HasCompactSupport g)
    {M₁ : Y → W} {M₂ : B → W} {Q₁ : W → Y} {Q₂ : W → B} (c₁ : Continuous M₁) (c₂ : Continuous M₂) (d₁ : Continuous Q₁)
    (d₂ : Continuous Q₂) (e₁ : ∀ y b, Q₁ (M₁ y + M₂ b) = y) (e₂ : ∀ y b, Q₂ (M₁ y + M₂ b) = b) :
    (∀ b, Integrable (fun y => g (M₁ y + M₂ b)) ν) ∧ IsLocallyConstant (fun b => ∫ y, g (M₁ y + M₂ b) ∂ν) ∧
      HasCompactSupport fun b => ∫ y, g (M₁ y + M₂ b) ∂ν := by
  refine ⟨fun b => ?_, ?_, ?_⟩
  · refine Continuous.integrable_of_hasCompactSupport (h1.continuous.comp (c₁.add continuous_const)) ?_
    refine HasCompactSupport.intro (h2.isCompact.image d₁) fun y hy => ?_
    by_contra h
    exact hy ⟨_, subset_tsupport g h, e₁ y b⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).2 fun b => ?_
    have ht : Tendsto (fun b' => M₂ b' - M₂ b) (𝓝 b) (𝓝 0) :=
      (c₂.sub continuous_const).tendsto' b 0 (sub_self _)
    filter_upwards [ht.eventually (eventually_invariant h1 h2)] with b' hb'
    congr 1
    funext y
    rw [← hb' (M₁ y + M₂ b)]
    congr 1
    abel
  · refine HasCompactSupport.intro (h2.isCompact.image d₂) fun b hb => ?_
    have : (fun y => g (M₁ y + M₂ b)) = fun _ => 0 := by
      funext y
      by_contra h
      exact hb ⟨_, subset_tsupport g h, e₂ y b⟩
    rw [this, integral_zero]

end Finite

theorem exists_integral_split {G X Y : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (e : G ≃ₜ+ X × Y) (m : Measure G) [m.IsAddHaarMeasure] (μ : Measure X) [μ.IsAddHaarMeasure] (ν : Measure Y)
    [ν.IsAddHaarMeasure] :
    ∃ c : ℂ, ∀ (u : X → ℂ) (v : Y → ℂ), Integrable u μ → Integrable v ν →
      Integrable (fun z => u (e z).1 * v (e z).2) m ∧
        ∫ z, u (e z).1 * v (e z).2 ∂m = c * ((∫ x, u x ∂μ) * ∫ y, v y ∂ν) := by
  haveI : (μ.prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μ ν
  haveI : (m.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map m
  have h := Measure.isAddLeftInvariant_eq_smul (m.map e) (μ.prod ν)
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  refine ⟨((Measure.addHaarScalarFactor (m.map e) (μ.prod ν) : ℝ) : ℂ), fun u v hu hv => ⟨?_, ?_⟩⟩
  · have : Integrable (fun z : X × Y => u z.1 * v z.2) (m.map e) := by
      rw [h]
      exact (hu.mul_prod hv).smul_measure_nnreal
    exact he.integrable_map_iff.1 this
  · rw [← he.integral_map (fun z : X × Y => u z.1 * v z.2)]
    conv_lhs => rw [h]
    rw [integral_smul_nnreal_measure, integral_prod_mul, NNReal.smul_def, Complex.real_smul]

end GlobalTheory.PartialIntegral

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartz
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.IkSchwartz

open GlobalTheory.SchwartzBruhatTensor GlobalTheory.PartialIntegral

abbrev AEf (D : D7) : Type := Af D.host.F ⊗[D.host.F] D.host.E

theorem exists_split {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (m n : ℕ) :
    ∃ e : Mx D m n ≃ₜ+ (D.what₂.Tau → Fin m → Fin n → ℂ) × (Fin m → Fin n → AEf D),
      ∀ x, e x = (fun τ i j => compAt θ τ x i j, fun i j => finPart D (x i j)) := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨s, hsc, hsf, hsi⟩ := exists_finSection D
  refine ⟨{ toFun := fun x => (fun τ i j => compAt θ τ x i j, fun i j => finPart D (x i j))
            invFun := fun p => s.mapMatrix (Matrix.of p.2) + chartM σ m n p.1
            left_inv := fun x => (decomp hσ hsf hsi x).symm
            right_inv := fun p => Prod.ext ?_ ?_
            map_add' := fun x y => Prod.ext ?_ ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun x => rfl⟩
  · funext τ i j
    show θ τ (infPart D (s (p.2 i j) + σ fun τ => p.1 τ i j)) = p.1 τ i j
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hsi, hσ.comp, RingHom.map_zero, zero_add]
  · funext i j
    show finPart D (s (p.2 i j) + σ fun τ => p.1 τ i j) = p.2 i j
    rw [RingHom.map_add (f := _), hsf, hσ.fin, add_zero]
  · funext τ i j
    show θ τ (infPart D (x i j + y i j)) = θ τ (infPart D (x i j)) + θ τ (infPart D (y i j))
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _)]
  · funext i j
    exact (finPart D).map_add _ _
  · exact (continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.FockCompare.continuous_comp hθ τ).comp (continuous_id.matrix_elem i j)).prodMk
      (continuous_pi fun i => continuous_pi fun j =>
        (GlobalTheory.Member.continuous_finPart D).comp (continuous_id.matrix_elem i j))
  · haveI := (lattice_Mx D m n).1
    refine Continuous.add ?_ ((continuous_chartM hσ.cont m n).comp continuous_fst)
    exact continuous_pi fun i => continuous_pi fun j =>
      hsc.comp ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))

def lmul {R : Type} [CommRing R] {m t : ℕ} (n : ℕ) (J : Matrix (Fin m) (Fin t) R) (x : Fin t → Fin n → R) :
    Fin m → Fin n → R := J ⬝ Matrix.of x

theorem continuous_lmul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m t : ℕ} (n : ℕ)
    (J : Matrix (Fin m) (Fin t) R) : Continuous (lmul n J) :=
  Continuous.matrix_mul (A := fun _ => J) (B := fun x : Matrix (Fin t) (Fin n) R => x) continuous_const continuous_id

def lmulC {ι : Type} {m t : ℕ} (n : ℕ) (J : ι → Matrix (Fin m) (Fin t) ℂ) :
    (ι → Fin t → Fin n → ℂ) →ₗ[ℝ] (ι → Fin m → Fin n → ℂ) where
  toFun c τ := lmul n (J τ) (c τ)
  map_add' c c' := funext fun τ => Matrix.mul_add (J τ) (Matrix.of (c τ)) (Matrix.of (c' τ))
  map_smul' r c := funext fun τ => Matrix.mul_smul (J τ) r (Matrix.of (c τ))

variable {D : D7} {T T' : HSp D} {t : ℕ} (d : HypDec T T' t) {R : Type} [CommRing R] (φ : AE D →+* R) {n : ℕ}

theorem map_emb (x : Mx D t n) (a : Mx D T'.rank n) :
    (fun i j => φ ((d.jX ⬝ x + d.j0 ⬝ a : Mx D T.rank n) i j)) =
      lmul n (d.jX.map φ) (fun i j => φ (x i j)) + lmul n (d.j0.map φ) (fun i j => φ (a i j)) := by
  show (d.jX ⬝ x + d.j0 ⬝ a : Mx D T.rank n).map φ = d.jX.map φ ⬝ x.map φ + d.j0.map φ ⬝ a.map φ
  ext i j
  simp [Matrix.mul_apply, map_sum]

theorem pX_emb (x : Fin t → Fin n → R) (a : Fin T'.rank → Fin n → R) :
    lmul n (d.pX.map φ) (lmul n (d.jX.map φ) x + lmul n (d.j0.map φ) a) = x := by
  show d.pX.map φ ⬝ (d.jX.map φ ⬝ Matrix.of x + d.j0.map φ ⬝ Matrix.of a) = Matrix.of x
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, d.pX_jX, d.pX_j0,
    Matrix.map_one _ φ.map_zero φ.map_one, Matrix.map_zero _ φ.map_zero, Matrix.one_mul, Matrix.zero_mul, add_zero]

theorem wittHyperbolic_projAnisotropic_leftMul_embedding (x : Fin t → Fin n → R) (a : Fin T'.rank → Fin n → R) :
    lmul n (d.p0.map φ) (lmul n (d.jX.map φ) x + lmul n (d.j0.map φ) a) = a := by
  show d.p0.map φ ⬝ (d.jX.map φ ⬝ Matrix.of x + d.j0.map φ ⬝ Matrix.of a) = Matrix.of a
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, d.p0_jX, d.p0_j0,
    Matrix.map_one _ φ.map_zero φ.map_one, Matrix.map_zero _ φ.map_zero, Matrix.one_mul, Matrix.zero_mul, zero_add]

theorem map_emb_fin (x : Mx D t n) (a : Mx D T'.rank n) :
    (fun i j => finPart D ((d.jX ⬝ x + d.j0 ⬝ a : Mx D T.rank n) i j)) =
      lmul n (d.jX.map (finPart D)) (fun i j => finPart D (x i j)) +
        lmul n (d.j0.map (finPart D)) (fun i j => finPart D (a i j)) := map_emb d (finPart D) x a


set_option maxHeartbeats 800000 in
theorem pure {θ : InfFam D} (hθ : IsInfFam θ) (μ : Measure (Mx D t n)) [μ.IsAddHaarMeasure]
    (f : SchwartzMap (D.what₂.Tau → Fin T.rank → Fin n → ℂ) ℂ) (g : (Fin T.rank → Fin n → AEf D) → ℂ)
    (hg : g ∈ WeilM.SB (Fin T.rank → Fin n → AEf D)) (Φ : Mx D T.rank n → ℂ)
    (hΦ : Φ = fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) :
    (∀ a : Mx D T'.rank n, Integrable (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) μ) ∧ ikS d μ Φ ∈ schwartzA θ T'.rank n := by
  haveI : IsModuleTopology (Af D.host.F) (AEf D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AEf D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : LocallyCompactSpace (AEf D) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AEf D) := e0.secondCountableTopology
  haveI : T2Space (AEf D) := e0.isEmbedding.t2Space
  letI : MeasurableSpace (Fin t → Fin n → AEf D) := borel _
  haveI : BorelSpace (Fin t → Fin n → AEf D) := ⟨rfl⟩
  haveI : BorelSpace (Mx D t n) := ⟨rfl⟩
  haveI := (lattice_Mx D t n).1
  obtain ⟨e, he⟩ := exists_split hθ t n
  let μr : Measure (D.what₂.Tau → Fin t → Fin n → ℂ) := Measure.addHaar
  let ν : Measure (Fin t → Fin n → AEf D) := Measure.addHaar
  obtain ⟨c, hc⟩ := exists_integral_split e μ μr ν
  let φ : D.what₂.Tau → AE D →+* ℂ := fun τ => (θ τ).comp (infPart D)
  obtain ⟨hf1, h, hh⟩ := schwartz_partial μr f (lmulC n fun τ => d.jX.map (φ τ)) (lmulC n fun τ => d.j0.map (φ τ))
    (fun x a hxa => by
      refine ⟨funext fun τ => ?_, funext fun τ => ?_⟩
      · have h0 : lmul n (d.jX.map (φ τ)) (x τ) + lmul n (d.j0.map (φ τ)) (a τ) = 0 := congrFun hxa τ
        rw [← pX_emb d (φ τ) (x τ) (a τ), h0]
        exact Matrix.mul_zero _
      · have h0 : lmul n (d.jX.map (φ τ)) (x τ) + lmul n (d.j0.map (φ τ)) (a τ) = 0 := congrFun hxa τ
        rw [← wittHyperbolic_projAnisotropic_leftMul_embedding d (φ τ) (x τ) (a τ), h0]
        exact Matrix.mul_zero _)
  obtain ⟨hg1, hg2, hg3⟩ := locallyConstant_partial ν hg.1 hg.2 (continuous_lmul n (d.jX.map (finPart D)))
    (continuous_lmul n (d.j0.map (finPart D))) (continuous_lmul n (d.pX.map (finPart D)))
    (continuous_lmul n (d.p0.map (finPart D))) (pX_emb d (finPart D)) (wittHyperbolic_projAnisotropic_leftMul_embedding d (finPart D))
  have key : ∀ a : Mx D T'.rank n, (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) = fun x =>
      f (lmulC n (fun τ => d.jX.map (φ τ)) (e x).1 + lmulC n (fun τ => d.j0.map (φ τ)) fun τ i j => compAt θ τ a i j) *
      g (lmul n (d.jX.map (finPart D)) (e x).2 + lmul n (d.j0.map (finPart D)) fun i j => finPart D (a i j)) := by
    intro a
    funext x
    have h2 : (fun τ i j => compAt θ τ (d.jX ⬝ x + d.j0 ⬝ a : Mx D T.rank n) i j) =
        lmulC n (fun τ => d.jX.map (φ τ)) (fun τ i j => compAt θ τ x i j) +
          lmulC n (fun τ => d.j0.map (φ τ)) fun τ i j => compAt θ τ a i j := funext fun τ => map_emb d (φ τ) x a
    rw [hΦ, he]
    exact congrArg₂ (· * ·) (congrArg f h2) (congrArg g (map_emb_fin d x a))
  refine ⟨fun a => by rw [key a]; exact (hc _ _ (hf1 _) (hg1 _)).1, ?_⟩
  have e2 : ikS d μ Φ = c • fun a : Mx D T'.rank n => h (fun τ i j => compAt θ τ a i j) *
      (fun b => ∫ y, g (lmul n (d.jX.map (finPart D)) y + lmul n (d.j0.map (finPart D)) b) ∂ν)
        (fun i j => finPart D (a i j)) := by
    funext a
    refine (congrArg (fun F => ∫ x, F x ∂μ) (key a)).trans ?_
    refine (hc _ _ (hf1 _) (hg1 _)).2.trans ?_
    rw [← hh]
    rfl
  rw [e2]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨h, _, ⟨hg2, hg3⟩, rfl⟩)

theorem ikS_mem_schwartzA : ∀ (D : D7), ∀ θ : InfFam D, IsInfFam θ → ∀ (T T' : HSp D) (t n : ℕ) (d : HypDec T T' t) (μ : Measure (Mx D t n)) (𝓕 : Set (Mx D t n)), IsCovolOne (ratMx D t n) μ 𝓕 → ∀ Φ ∈ schwartzA θ T.rank n, ikS d μ Φ ∈ schwartzA θ T'.rank n := by
  intro D θ hθ T T' t n d μ 𝓕 hμ Φ hΦ
  haveI := hμ.1
  suffices h : (∀ a : Mx D T'.rank n, Integrable (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) μ) ∧ ikS d μ Φ ∈ schwartzA θ T'.rank n from h.2
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, h⟩ := h
    exact pure d hθ μ f g hg Φ h
  | zero =>
    refine ⟨fun a => integrable_zero _ _ _, ?_⟩
    have : ikS d μ (0 : Mx D T.rank n → ℂ) = 0 := funext fun a => integral_zero _ _
    rw [this]
    exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    refine ⟨fun a => (h1.1 a).add (h2.1 a), ?_⟩
    have : ikS d μ (Φ + Ψ) = ikS d μ Φ + ikS d μ Ψ := funext fun a => integral_add (h1.1 a) (h2.1 a)
    rw [this]
    exact Submodule.add_mem _ h1.2 h2.2
  | smul c Φ _ h =>
    refine ⟨fun a => (h.1 a).smul c, ?_⟩
    have : ikS d μ (c • Φ) = c • ikS d μ Φ := funext fun a => integral_smul c _
    rw [this]
    exact Submodule.smul_mem _ c h.2

end GlobalTheory.RegSch.IkSchwartz

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartzStatement
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ikedaPartialFourierIntegral_mem_adelicSchwartz : ∀ (D : D7), ∀ θ : InfFam D, IsInfFam θ → ∀ (T T' : HSp D) (t n : ℕ) (d : HypDec T T' t) (μ : Measure (Mx D t n)) (𝓕 : Set (Mx D t n)), IsCovolOne (ratMx D t n) μ 𝓕 → ∀ Φ ∈ schwartzA θ T.rank n, ikS d μ Φ ∈ schwartzA θ T'.rank n := by
  first | exact @GlobalTheory.RegSch.IkSchwartz.ikS_mem_schwartzA | exact GlobalTheory.RegSch.IkSchwartz.ikS_mem_schwartzA | (intros; apply GlobalTheory.RegSch.IkSchwartz.ikS_mem_schwartzA <;> assumption)
end
