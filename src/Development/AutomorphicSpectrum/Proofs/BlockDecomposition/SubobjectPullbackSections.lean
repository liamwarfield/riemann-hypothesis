module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandSeriesShiftIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqSumOfKernel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevIntegrationByParts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectPullbackSections
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectPullbackSections
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

theorem secs_pullback_arrow {X : Scheme.{0}} {E : X.Modules} (D S : Subobject E) (V : X.Opens) :
    secs ((Subobject.pullback D.arrow).obj S) V = (D.arrow.app V) ⁻¹' secs S V := by
  let G : X.Modules ⥤ Type :=
    Scheme.Modules.toPresheaf X ⋙ (evaluation _ _).obj (Opposite.op V) ⋙ forget Ab
  haveI : PreservesLimitsOfSize.{0, 0} ((evaluation (TopologicalSpace.Opens X)ᵒᵖ Ab).obj
      (Opposite.op V)) := ⟨fun {J} _ => evaluation_preservesLimitsOfShape _⟩
  haveI : PreservesLimitsOfShape WalkingCospan (Scheme.Modules.toPresheaf X) := inferInstance
  haveI : PreservesLimitsOfShape WalkingCospan (forget Ab.{0}) := inferInstance
  haveI : PreservesLimitsOfShape WalkingCospan G := inferInstance
  have hp := (Subobject.isPullback D.arrow S).map G
  ext d
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨(Subobject.pullbackπ D.arrow S).app V p, ?_⟩
    exact congr($(hp.w) p)
  · rintro ⟨s, hs⟩
    obtain ⟨p, h₁, h₂⟩ := Types.exists_of_isPullback hp s d hs
    exact ⟨p, h₂⟩

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectPullbackSectionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subobject_pullback_sections : ∀ {X : Scheme.{0}} {E : X.Modules} (D S : Subobject E) (V : X.Opens), secs ((Subobject.pullback D.arrow).obj S) V = (D.arrow.app V) ⁻¹' secs S V := by
  first | exact @GlobalTheory.CompanionTheory.GE.secs_pullback_arrow | exact GlobalTheory.CompanionTheory.GE.secs_pullback_arrow | (intros; apply GlobalTheory.CompanionTheory.GE.secs_pullback_arrow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirRightLaplacianFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirRightLaplacianFormula
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem sk_skew {n : ℕ} (p : Ix n) : (sk p)ᴴ = -sk p := by
  obtain ⟨b, i, j⟩ := p
  have hc : ∀ (a b : Fin n) (c : ℂ), (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
    intro a b c
    ext x y
    simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
    by_cases h1 : a = y <;> by_cases h2 : b = x <;> simp [h1, h2]
  cases b
  · simp [sk, Matrix.conjTranspose_add, hc, Matrix.single_neg, add_comm]
  · simp [sk, Matrix.conjTranspose_sub, hc]

theorem Rd_Rd_of_act {n : ℕ} (E : KMod n) (Y : Mat n) (B : E.V →L[ℂ] E.V)
    (hB : ∀ f ∈ CE E, ∀ g ∈ GLs n, Rd Y f g = B (f g)) (f : Mat n → E.V) (hf : f ∈ CE E)
    (g : Mat n) (hg : g ∈ GLs n) : Rd Y (Rd Y f) g = B (B (f g)) := by
  have hnhds : GLs n ∈ nhds g := isOpen_GLs.mem_nhds hg
  have hev : Rd Y f =ᶠ[nhds g] (B.restrictScalars ℝ) ∘ f := by
    filter_upwards [hnhds] with y hy
    simpa using hB f hf y hy
  have hd : DifferentiableAt ℝ f g :=
    (hf.1.contDiffAt hnhds).differentiableAt (by simp)
  have hfd : fderiv ℝ (Rd Y f) g = (B.restrictScalars ℝ).comp (fderiv ℝ f g) := by
    rw [hev.fderiv_eq]
    exact ((B.restrictScalars ℝ).hasFDerivAt.comp g hd.hasFDerivAt).fderiv
  have h1 : Rd Y (Rd Y f) g = B (Rd Y f g) := by
    change fderiv ℝ (Rd Y f) g (g * Y) = B (fderiv ℝ f g (g * Y))
    rw [hfd]
    rfl
  rw [h1, hB f hf g hg]

theorem om_section {n : ℕ} (E : KMod n) : ∃ A : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n,
    Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g + A (f g) := by
  choose B hB using fun p : Ix n => rd_skew_eq_const E (sk p) (sk_skew p)
  refine ⟨-(1 / 4 : ℂ) • ∑ p, B p * B p, fun f hf g hg => ?_⟩
  rw [OmDec.Om_eq_squares f hf.1 g hg, sub_eq_add_neg]
  congr 1
  have h : ∀ p, Rd (sk p) (Rd (sk p) f) g = B p (B p (f g)) := fun p =>
    Rd_Rd_of_act E (sk p) (B p) (hB p) f hf g hg
  simp only [h, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.neg_apply, neg_smul]
  rfl

end GlobalTheory.CompanionTheory.WaveSpd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirRightLaplacianFormulaStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_right_laplacian_formula : ∀ {n : ℕ} (E : KMod n), ∃ A : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n, Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g + A (f g) := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.om_section | exact GlobalTheory.CompanionTheory.WaveSpd.om_section | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.om_section <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjGelfValOfIsHerm
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem amat_map_conj {n : ℕ} (l : Fin n → ℂ) :
    (Formalism.REAL.Amat l).map (starRingEnd ℂ) = Formalism.REAL.Amat (fun a => conj (l a)) := by
  ext a b
  simp only [Matrix.map_apply, Formalism.REAL.Amat, Matrix.of_apply]
  split_ifs <;> simp

theorem conj_gelfVal {n : ℕ} (c : Fin n → ℂ) (m : ℕ) :
    conj (GlobalTheory.Dec.gelfVal c m) = GlobalTheory.Dec.gelfVal (fun a => conj (c a)) m := by
  have h : ((Formalism.REAL.Amat fun a => c a + ((n : ℂ) - 1) / 2) ^ m).map (starRingEnd ℂ) =
      (Formalism.REAL.Amat fun a => conj (c a) + ((n : ℂ) - 1) / 2) ^ m := by
    rw [Matrix.map_pow, amat_map_conj]
    congr 2
    funext a
    simp [map_ofNat]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.Dec.gelfVal, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← h]
  rfl

theorem prod_one_sub_ne_zero {n : ℕ} (l : Fin n → ℂ) :
    (∏ a, (1 - PowerSeries.C (l a) * PowerSeries.X) : PowerSeries ℂ) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun a _ h => ?_
  have := congrArg PowerSeries.constantCoeff h
  simp at this

theorem gser_comp_perm {n : ℕ} (c : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    gser (fun a => c (σ a)) = gser c := by
  have h1 := gser_mul_prod n (fun a => c (σ a))
  have h2 := gser_mul_prod n c
  beta_reduce at h1
  have e1 : (∏ a, (1 - PowerSeries.C (c (σ a) + ((n : ℂ) - 1) / 2) * PowerSeries.X) : PowerSeries ℂ) =
      ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) :=
    Equiv.prod_comp σ (fun a => (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X))
  have e2 : (∏ a, (1 - PowerSeries.C (c (σ a) + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) : PowerSeries ℂ) =
      ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) :=
    Equiv.prod_comp σ (fun a => (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X))
  rw [e1, e2] at h1
  have hP : (∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) : PowerSeries ℂ) ≠ 0 :=
    prod_one_sub_ne_zero _
  have h3 : (1 - PowerSeries.X * gser (fun a => c (σ a))) = 1 - PowerSeries.X * gser c :=
    mul_right_cancel₀ hP (h1.trans h2.symm)
  have h4 : PowerSeries.X * gser (fun a => c (σ a)) = PowerSeries.X * gser c := sub_right_injective h3
  exact mul_left_cancel₀ PowerSeries.X_ne_zero h4

theorem gelfVal_comp_perm {n : ℕ} (c : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    GlobalTheory.Dec.gelfVal (fun a => c (σ a)) m = GlobalTheory.Dec.gelfVal c m := by
  have h := congrArg (PowerSeries.coeff m) (gser_comp_perm c σ)
  simpa [gser] using h

theorem conj_gelfVal_of_isHerm : ∀ (n : ℕ) (χ : Inf n), IsHerm χ → ∀ (s : Bool) (m : ℕ),
    conj (GlobalTheory.Dec.gelfVal (χ s) m) = GlobalTheory.Dec.gelfVal (fun a => - χ (!s) a) m := by
  intro n χ hχ s m
  obtain ⟨σ, hσ⟩ := hχ
  rw [conj_gelfVal]
  cases s
  · simp only [Bool.not_false]
    rw [← gelfVal_comp_perm (fun a => conj (χ false a)) σ]
    congr 1
    funext a
    simp [hσ a]
  · simp only [Bool.not_true]
    rw [← gelfVal_comp_perm (fun a => -χ false a) σ]
    congr 1
    funext a
    simp [hσ a]

end GlobalTheory.CompanionTheory.WaveMult
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivTwoSmul
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK GlobalTheory.CompanionTheory.WaveK.Base
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveK.Lin

variable {n : ℕ}

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Eu_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a b : Fin n) :
    ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) := by
  have h := fun X : Mat n => GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf
  unfold Eu
  exact ((h _).add (contDiffOn_const.smul (h _))).const_smul _

theorem Epow_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, ContDiffOn ℝ ∞ (Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b
    · simpa [Epow, hab] using hf
    · simp only [Epow, if_neg hab]
      exact contDiffOn_const (c := (0 : V))
  | succ m ih =>
    intro a b
    have e : Epow s (m + 1) a b f = fun x => ∑ c, Eu s a c (Epow s m c b f) x := by
      ext x
      simp only [Epow, Finset.sum_apply]
    rw [e]
    exact ContDiffOn.sum fun c _ => Eu_smooth (ih c b) s a c

theorem Eu_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) (s : Bool)
    (a b : Fin n) : Set.EqOn (Eu s a b (f + f')) (Eu s a b f + Eu s a b f') (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, GlobalTheory.CompanionTheory.RCalc.Rd_add _ hf hf' hx, smul_add]
  abel

theorem Eu_smul (c : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a b : Fin n) :
    Set.EqOn (Eu s a b (c • f)) (c • Eu s a b f) (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, GlobalTheory.CompanionTheory.RCalc.Rd_smul c _ hf hx]
  module

theorem Epow_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) : ∀ a b : Fin n, Set.EqOn (Epow s m a b (f + f')) (Epow s m a b f + Epow s m a b f') (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (ih c b) s a c hx]
    exact Eu_add (Epow_smooth hf s m c b) (Epow_smooth hf' s m c b) s a c hx

theorem Epow_smul (k : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s m a b (k • f)) (k • Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (ih c b) s a c hx]
    exact Eu_smul k (Epow_smooth hf s m c b) s a c hx

theorem gel_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) : Set.EqOn (gel s m (f + f')) (gel s m f + gel s m f') (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Epow_add hf hf' s m a a hx

theorem gel_smul (k : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (k • f)) (k • gel s m f) (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => Epow_smul k hf s m a a hx

theorem Om_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) :
    Set.EqOn (Om (f + f')) (Om f + Om f') (GLs n) := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_add hf hf' _ _ hx, smul_add]
  abel

theorem Om_smul (k : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Om (k • f)) (k • Om f) (GLs n) := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_smul k hf _ _ hx]
  module

theorem iterated_integral_add {w w' : ℝ → V} (hw : ContDiff ℝ ∞ w) (hw' : ContDiff ℝ ∞ w') (t : ℝ) :
    iteratedDeriv 2 (fun s => w s + w' s) t = iteratedDeriv 2 w t + iteratedDeriv 2 w' t := by
  have h2 : ∀ φ : ℝ → V, iteratedDeriv 2 φ = deriv (deriv φ) := fun φ => by
    rw [iteratedDeriv_eq_iterate]; rfl
  have hd : deriv (fun s => w s + w' s) = fun s => deriv w s + deriv w' s :=
    funext fun s => deriv_fun_add (hw.differentiable (by simp) s) (hw'.differentiable (by simp) s)
  have e1 : Differentiable ℝ (deriv w) := (contDiff_infty_iff_deriv.1 hw).2.differentiable (by simp)
  have e2 : Differentiable ℝ (deriv w') := (contDiff_infty_iff_deriv.1 hw').2.differentiable (by simp)
  rw [h2, h2, h2, hd]
  exact deriv_fun_add (e1 t) (e2 t)

theorem iteratedDeriv_two_smul (k : ℂ) {w : ℝ → V} (hw : ContDiff ℝ ∞ w) (t : ℝ) :
    iteratedDeriv 2 (fun s => k • w s) t = k • iteratedDeriv 2 w t := by
  have h2 : ∀ φ : ℝ → V, iteratedDeriv 2 φ = deriv (deriv φ) := fun φ => by
    rw [iteratedDeriv_eq_iterate]; rfl
  have hd : deriv (fun s => k • w s) = fun s => k • deriv w s :=
    funext fun s => deriv_fun_const_smul k (hw.differentiable (by simp) s)
  have e1 : Differentiable ℝ (deriv w) := (contDiff_infty_iff_deriv.1 hw).2.differentiable (by simp)
  rw [h2, h2, hd]
  exact deriv_fun_const_smul k (e1 t)

end Ops

theorem wave_add {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v) :
    IsWave E fun t y => u t y + v t y := by
  refine ⟨hu.1.add hv.1, fun t => ⟨(hu.2.1 t).1.add (hv.2.1 t).1, ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · intro g hg k
    simp only [(hu.2.1 t).2 g hg k, (hv.2.1 t).2 g hg k, map_add (f := _)]
  · rw [iterated_integral_add (GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg) (GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg), hu.2.2.1 t g hg, hv.2.2.1 t g hg]
    exact (Om_add (hu.2.1 t).1 (hv.2.1 t).1 hg).symm
  · have h1 : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).differentiable (by simp)).differentiableAt
    have h2 : DifferentiableAt ℝ (fun s => v s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg).differentiable (by simp)).differentiableAt
    rw [deriv_fun_add h1 h2, hu.2.2.2 g hg, hv.2.2.2 g hg, add_zero]

theorem wave_smul (k : ℂ) {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u) :
    IsWave E fun t y => k • u t y := by
  refine ⟨hu.1.const_smul k, fun t => ⟨(hu.2.1 t).1.const_smul k, ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · intro g hg k'
    simp only [(hu.2.1 t).2 g hg k', map_smul]
  · rw [iteratedDeriv_two_smul k (GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg), hu.2.2.1 t g hg]
    exact (Om_smul k (hu.2.1 t).1 hg).symm
  · have h1 : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).differentiable (by simp)).differentiableAt
    rw [deriv_fun_const_smul k h1, hu.2.2.2 g hg, smul_zero]

end GlobalTheory.CompanionTheory.WaveK.Lin
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandValueNegation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandValueNegation
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.ValPhi

open PowerSeries

section
variable {A : Type} [Ring A] (N : A) (τ : ℕ → A)

theorem bco_of_lt : ∀ (m j : ℕ), m < j → bco N τ m j = 0 := by
  intro m
  induction m with
  | zero =>
    intro j h
    cases j with
    | zero => omega
    | succ j => simp [bco]
  | succ m ih =>
    intro j h
    cases j with
    | zero => omega
    | succ j => rw [bco, ih j (by omega), ih (j + 1) (by omega)]; simp

theorem bco_self (m : ℕ) : bco N τ m m = 1 := by
  induction m with
  | zero => simp [bco]
  | succ m ih => rw [bco, ih, bco_of_lt N τ m (m + 1) (by omega)]; simp

theorem eq_phiSeq (p : ℕ → A) (h : ∀ m, ∑ j ∈ range (m + 1), bco N τ m j * p j = τ m) (m : ℕ) :
    p m = phiSeq N τ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have e : ∑ j ∈ range m, bco N τ m j * phiSeq N τ j = ∑ j ∈ range m, bco N τ m j * p j :=
      sum_congr rfl fun j hj => by rw [ih j (mem_range.1 hj)]
    rw [phiSeq, Fin.sum_univ_eq_sum_range (fun j => bco N τ m j * phiSeq N τ j) m, e, ← h m,
      sum_range_succ, bco_self, one_mul]
    abel
end

section
variable (N : ℂ) (τ : ℕ → ℂ)

noncomputable def bser (j : ℕ) : PowerSeries ℂ := PowerSeries.mk (fun m => bco N τ m j)

theorem coeff_bser (j m : ℕ) : coeff m (bser N τ j) = bco N τ m j := by simp [bser]

theorem constantCoeff_bser (j : ℕ) : constantCoeff (bser N τ j) = bco N τ 0 j := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_bser]

theorem bser_zero : (1 - C N * X) * bser N τ 0 = 1 - X * PowerSeries.mk τ := by
  have e : ∀ f : PowerSeries ℂ, (1 - C N * X) * f = f - C N * (X * f) := fun f => by ring
  rw [e]
  ext k
  cases k with
  | zero => simp [constantCoeff_bser, bco]
  | succ k =>
    simp [coeff_bser, bco, coeff_succ_X_mul, coeff_one]

theorem bser_succ (j : ℕ) : (1 - C N * X) * bser N τ (j + 1) = X * bser N τ j := by
  have e : ∀ f : PowerSeries ℂ, (1 - C N * X) * f = f - C N * (X * f) := fun f => by ring
  rw [e]
  ext k
  cases k with
  | zero => simp [constantCoeff_bser, bco]
  | succ k =>
    simp [coeff_bser, bco, coeff_succ_X_mul]

theorem bser_eq {w : PowerSeries ℂ} (hw : (1 - C N * X) * w = 1) (j : ℕ) :
    bser N τ j = (1 - X * PowerSeries.mk τ) * w ^ (j + 1) * X ^ j := by
  induction j with
  | zero =>
    have := bser_zero N τ
    rw [← this]
    linear_combination (-(bser N τ 0)) * hw
  | succ j ih =>
    have := bser_succ N τ j
    rw [ih] at this
    linear_combination (-(bser N τ (j + 1))) * hw + w * this

end

theorem mk_decomp (g : ℕ → ℂ) (m : ℕ) :
    PowerSeries.mk g = ∑ j ∈ range (m + 1), g j • (X : PowerSeries ℂ) ^ j
      + X ^ (m + 1) * PowerSeries.mk (fun i => g (i + (m + 1))) := by
  ext k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, coeff_mk, coeff_X_pow_mul', LinearMap.map_smul, coeff_X_pow,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hk : m + 1 ≤ k
  · rw [if_pos hk, Nat.sub_add_cancel hk, sum_ite_eq]
    simp [mem_range]
    omega
  · rw [if_neg hk, sum_ite_eq, if_pos (mem_range.2 (by omega))]
    simp

theorem sum_of_subst (N : ℂ) (τ g : ℕ → ℂ) {w : PowerSeries ℂ} (hw : (1 - C N * X) * w = 1)
    (ha : HasSubst (-(X * w)))
    (h : (1 - X * PowerSeries.mk τ) * subst (-(X * w)) (1 - X * PowerSeries.mk g) = 1) (m : ℕ) :
    ∑ j ∈ range (m + 1), bco N τ m j * ((-1) ^ j * g j) = τ m := by
  let θ : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ := substAlgHom ha
  have hθ : ∀ f, subst (-(X * w)) f = θ f := fun f => by simp [θ, coe_substAlgHom]
  have hX : θ X = -(X * w) := by rw [← hθ]; exact subst_X ha
  set H := PowerSeries.mk (fun i => g (i + (m + 1))) with hH
  set Q := 1 - X * PowerSeries.mk τ with hQ
  have hG : θ (PowerSeries.mk g) = ∑ j ∈ range (m + 1), g j • (-(X * w)) ^ j
      + (-(X * w)) ^ (m + 1) * θ H := by
    conv_lhs => rw [mk_decomp g m]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, map_mul, map_pow, hX, hH]
  rw [hθ, map_sub, map_one, map_mul, hX, hG] at h
  have hterm : ∀ j, Q * (X * w) * (g j • (-(X * w)) ^ j)
      = (g j * (-1) ^ j) • (X * bser N τ j) := by
    intro j
    rw [bser_eq N τ hw j, neg_pow]
    simp only [smul_eq_C_mul, map_mul, map_pow, map_neg, map_one]
    ring
  have hfin : Q + ∑ j ∈ range (m + 1), (g j * (-1) ^ j) • (X * bser N τ j)
      + X ^ (m + 2) * (Q * w * (-w) ^ (m + 1) * θ H) = 1 := by
    rw [← h, ← sum_congr rfl fun j _ => hterm j, ← mul_sum, neg_mul_eq_mul_neg X w, mul_pow]
    ring
  have hc := congrArg (coeff (m + 1)) hfin
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, LinearMap.map_smul, coeff_succ_X_mul, coeff_bser, coeff_X_pow_mul',
    smul_eq_mul, hQ, map_sub, coeff_mk, coeff_one] at hc
  simp at hc
  have e : ∑ j ∈ range (m + 1), bco N τ m j * ((-1) ^ j * g j)
      = ∑ x ∈ range (m + 1), g x * (-1) ^ x * bco N τ m x :=
    sum_congr rfl fun j _ => by ring
  rw [e]
  linear_combination hc

theorem mul_subst_eq_one (n : ℕ) (cc : Fin n → ℂ) {w : PowerSeries ℂ}
    (hw : (1 - C (n : ℂ) * X) * w = 1) (ha : HasSubst (-(X * w))) :
    (1 - X * gser cc) * subst (-(X * w)) (1 - X * gser (fun a => - cc a)) = 1 := by
  let θ : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ := substAlgHom ha
  have hθ : ∀ f, subst (-(X * w)) f = θ f := fun f => by simp [θ, coe_substAlgHom]
  have hX : θ X = -(X * w) := by rw [← hθ]; exact subst_X ha
  have hC : ∀ c : ℂ, θ (C c) = C c := fun c => θ.commutes c
  have e1 : ∀ i, 1 - C (-cc i + ((n : ℂ) - 1) / 2) * -(X * w)
      = w * (1 - C (cc i + ((n : ℂ) - 1) / 2 + 1) * X) := by
    intro i
    have hn : C (n : ℂ) = C (-cc i + ((n : ℂ) - 1) / 2) + C (cc i + ((n : ℂ) - 1) / 2 + 1) := by
      rw [← map_add (f := _)]; congr 1; ring
    linear_combination (-1 : PowerSeries ℂ) * hw - X * w * hn
  have e2 : ∀ i, 1 - C (-cc i + ((n : ℂ) - 1) / 2 + 1) * -(X * w)
      = w * (1 - C (cc i + ((n : ℂ) - 1) / 2) * X) := by
    intro i
    have hn : C (n : ℂ) = C (-cc i + ((n : ℂ) - 1) / 2 + 1) + C (cc i + ((n : ℂ) - 1) / 2) := by
      rw [← map_add (f := _)]; congr 1; ring
    linear_combination (-1 : PowerSeries ℂ) * hw - X * w * hn
  have h1 := GlobalTheory.T.gelfand_series_shift_identity n cc
  have h2 := congrArg θ (GlobalTheory.T.gelfand_series_shift_identity n (fun a => - cc a))
  simp only [map_mul, map_prod, map_sub, map_one, hC, hX, e1, e2, prod_mul_distrib, prod_const,
    card_univ, Fintype.card_fin] at h2
  set D := ∏ a, (1 - C (cc a + ((n : ℂ) - 1) / 2 + 1) * (X : PowerSeries ℂ)) with hD
  set E := ∏ a, (1 - C (cc a + ((n : ℂ) - 1) / 2) * (X : PowerSeries ℂ)) with hE
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hD0 : D ≠ 0 := by
    refine prod_ne_zero_iff.2 fun i _ h0 => ?_
    have := congrArg constantCoeff h0
    simp at this
  rw [hθ, map_sub, map_one, map_mul, hX]
  refine mul_right_cancel₀ (mul_ne_zero (pow_ne_zero n hw0) hD0) ?_
  linear_combination (1 - X * gser cc) * h2 + w ^ n * h1

theorem gelfVal_neg_eq_phiSeq : ∀ (n : ℕ) (cc : Fin n → ℂ) (m : ℕ),
    (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m = phiSeq (n : ℂ) (GlobalTheory.Dec.gelfVal cc) m := by
  intro n cc m
  have hu : constantCoeff (1 - C (n : ℂ) * X : PowerSeries ℂ) ≠ 0 := by simp
  have hw := PowerSeries.mul_inv_cancel _ hu
  have ha : HasSubst (-(X * (1 - C (n : ℂ) * X : PowerSeries ℂ)⁻¹)) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  exact eq_phiSeq (n : ℂ) (GlobalTheory.Dec.gelfVal cc)
    (fun m => (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m)
    (sum_of_subst (n : ℂ) _ _ hw ha (mul_subst_eq_one n cc hw ha)) m

end GlobalTheory.CompanionTheory.WaveMult.ValPhi
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandValueNegationStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_value_negation : ∀ (n : ℕ) (cc : Fin n → ℂ) (m : ℕ), (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m = phiSeq (n : ℂ) (GlobalTheory.Dec.gelfVal cc) m := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.ValPhi.gelfVal_neg_eq_phiSeq | exact GlobalTheory.CompanionTheory.WaveMult.ValPhi.gelfVal_neg_eq_phiSeq | (intros; apply GlobalTheory.CompanionTheory.WaveMult.ValPhi.gelfVal_neg_eq_phiSeq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionNormBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionNormBound
noncomputable section

open MeasureTheory Matrix Finset Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.SecBd

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem val_mem (y : G n) : y.val ∈ GLs n := (Matrix.isUnits_det_units y).ne_zero

theorem basis_true_eq_single (a c : Fin n) : bs (true, a, c) = Matrix.single a c (1 : ℂ) := by simp [bs]

theorem bs_f (a c : Fin n) : bs (false, a, c) = Matrix.single a c Complex.I := by simp [bs]

theorem Rw_append {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (w : List (Bool × Fin n × Fin n))
    (p : Bool × Fin n × Fin n) (f : Mat n → V) : Rw (w ++ [p]) f = Rw w (Rd (bs p) f) := by
  induction w with
  | nil => rfl
  | cons q w ih =>
    show Rd (bs q) (Rw (w ++ [p]) f) = Rd (bs q) (Rw w (Rd (bs p) f))
    rw [ih]

theorem Rd_sub {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (X X' : Mat n) (f : Mat n → V) (g : Mat n) :
    Rd (X - X') f g = Rd X f g - Rd X' f g := by
  simp [Rd, mul_sub]

theorem Rd_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (X X' : Mat n) (f : Mat n → V) (g : Mat n) :
    Rd (X + X') f g = Rd X f g + Rd X' f g := by
  simp [Rd, mul_add]

theorem single_conj (a b : Fin n) (c : ℂ) : (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
  ext x y
  simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
  by_cases h1 : a = y <;> by_cases h2 : b = x <;> simp [h1, h2]

theorem skewY (a c : Fin n) :
    (Matrix.single a c (1 : ℂ) - Matrix.single c a (1 : ℂ) : Mat n)ᴴ = -(Matrix.single a c (1 : ℂ) - Matrix.single c a 1) := by
  simp [Matrix.conjTranspose_sub, single_conj]

theorem skewZ (a c : Fin n) :
    (Matrix.single a c Complex.I + Matrix.single c a Complex.I : Mat n)ᴴ =
      -(Matrix.single a c Complex.I + Matrix.single c a Complex.I) := by
  simp [Matrix.conjTranspose_add, single_conj, Matrix.single_neg, add_comm]

section L2

variable [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem cls_eq {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) : cls μ f = h.toLp _ := dif_pos h

theorem cls_ae {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) : cls μ f =ᵐ[μ] fun y => f y.val := by
  rw [cls_eq μ h]
  exact h.coeFn_toLp

theorem cls_congr {f f' : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) (e : ∀ g ∈ GLs n, f g = f' g) :
    cls μ f = cls μ f' := by
  have e' : (fun y : G n => f y.val) = fun y => f' y.val := funext fun y => e _ (val_mem y)
  have h' : MemLp (fun y : G n => f' y.val) 2 μ := e' ▸ h
  rw [cls_eq μ h, cls_eq μ h']
  exact MemLp.toLp_congr h h' (by rw [e'])

theorem cls_sub {f f' : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) (h' : MemLp (fun y : G n => f' y.val) 2 μ) :
    cls μ (fun g => f g - f' g) = cls μ f - cls μ f' := by
  rw [cls_eq μ h, cls_eq μ h', cls_eq μ (h.sub h')]
  exact MemLp.toLp_sub h h'

theorem cls_sum {ι : Type} (s : Finset ι) (F : ι → Mat n → V)
    (h : ∀ i ∈ s, MemLp (fun y : G n => F i y.val) 2 μ) :
    MemLp (fun y : G n => ∑ i ∈ s, F i y.val) 2 μ ∧ cls μ (fun g => ∑ i ∈ s, F i g) = ∑ i ∈ s, cls μ (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : MemLp (fun _ : G n => (0 : V)) 2 μ := MemLp.zero
    refine ⟨by simpa using h0, ?_⟩
    simp only [Finset.sum_empty]
    rw [cls_eq μ h0]
    exact MemLp.toLp_zero h0
  | insert i s hi ih =>
    obtain ⟨m, e⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hi' := h i (Finset.mem_insert_self i s)
    simp only [Finset.sum_insert hi]
    refine ⟨hi'.add m, ?_⟩
    rw [← e, cls_eq μ hi', cls_eq μ (f := fun g => ∑ i ∈ s, F i g) m,
      cls_eq μ (f := fun g => F i g + ∑ i ∈ s, F i g) (hi'.add m)]
    exact MemLp.toLp_add hi' m

theorem norm_le_of_ae {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) (x : Lp V 2 μ) (C : V →L[ℂ] V)
    (e : ∀ᵐ y ∂μ, x y = C (f (y : G n).val)) : ‖x‖ ≤ ‖C‖ * ‖cls μ f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [e, cls_ae μ h] with y h1 h2
  rw [h1, h2]
  exact C.le_opNorm _

end L2

theorem pol_sub {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u v : H) :
    -(⟪v, u⟫_ℂ).re ≤ ‖u - v‖ ^ 2 / 4 := by
  have h1 := @norm_add_sq ℂ _ _ _ _ u v
  have h2 := @norm_sub_sq ℂ _ _ _ _ u v
  have h3 := @inner_re_symm ℂ _ _ _ _ u v
  simp only [RCLike.re_eq_complex_re] at h1 h2 h3
  nlinarith [sq_nonneg ‖u + v‖]

theorem pol_add {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u v : H) :
    (⟪v, u⟫_ℂ).re ≤ ‖u + v‖ ^ 2 / 4 := by
  have h1 := @norm_add_sq ℂ _ _ _ _ u v
  have h2 := @norm_sub_sq ℂ _ _ _ _ u v
  have h3 := @inner_re_symm ℂ _ _ _ _ u v
  simp only [RCLike.re_eq_complex_re] at h1 h2 h3
  nlinarith [sq_nonneg ‖u - v‖]

section Main

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem sob_Rd (hR : RCalc) {f : Mat n → V} (hS : Sob μ f) (p : Bool × Fin n × Fin n) : Sob μ (Rd (bs p) f) :=
  ⟨((hR n).1 V f hS.1).1 _, fun w => by
    have := hS.2 (w ++ [p])
    rwa [Rw_append] at this⟩

theorem mem1 {f : Mat n → V} (hS : Sob μ f) (p : Bool × Fin n × Fin n) :
    MemLp (fun y : G n => Rd (bs p) f y.val) 2 μ := hS.2 [p]

theorem mem0 {f : Mat n → V} (hS : Sob μ f) : MemLp (fun y : G n => f y.val) 2 μ := hS.2 []

end Main

theorem secBound (hI : IbpSob) : SecBound := by
  intro n _ _ μ _ E hL hU hR
  choose BY hBY using fun a c : Fin n => GlobalTheory.CompanionTheory.WaveSpd.rd_skew_eq_const E _ (skewY a c)
  choose BZ hBZ using fun a c : Fin n => GlobalTheory.CompanionTheory.WaveSpd.rd_skew_eq_const E _ (skewZ a c)
  refine ⟨∑ a, ∑ c, (‖BY a c‖ ^ 2 + ‖BZ a c‖ ^ 2) / 4, fun f hS hsec => ?_⟩
  have hCE : f ∈ CE E := ⟨hS.1, hsec⟩
  set x := cls μ f with hx
  have hf0 := mem0 μ hS

  have hd : ∀ p q : Bool × Fin n × Fin n, MemLp (fun y : G n => Rd (bs p) (Rd (bs q) f) y.val) 2 μ := fun p q =>
    mem1 μ (sob_Rd μ hR hS q) p
  have hip : ∀ p q : Bool × Fin n × Fin n, ⟪cls μ (Rd (bs p) (Rd (bs q) f)), x⟫_ℂ =
      -⟪cls μ (Rd (bs q) f), cls μ (Rd (bs p) f)⟫_ℂ := fun p q =>
    hI n μ E.V hL hU hR _ _ (sob_Rd μ hR hS q) hS (bs p)

  let T : Fin n → Fin n → Mat n → E.V := fun a c g =>
    Rd (bs (true, a, c)) (Rd (bs (true, c, a)) f) g - Rd (bs (false, a, c)) (Rd (bs (false, c, a)) f) g
  have hT : ∀ a c, MemLp (fun y : G n => T a c y.val) 2 μ := fun a c => (hd _ _).sub (hd _ _)
  have hOm : ∀ g ∈ GLs n, Om f g = ∑ a, ∑ c, T a c g := by
    intro g hg
    rw [GlobalTheory.CompanionTheory.Casimir.omFormula n E.V f hS.1 g hg]
    simp only [T, basis_true_eq_single, bs_f]
  have hsumc : ∀ a, MemLp (fun y : G n => ∑ c, T a c y.val) 2 μ ∧
      cls μ (fun g => ∑ c, T a c g) = ∑ c, cls μ (T a c) := fun a =>
    cls_sum μ _ (T a) fun c _ => hT a c
  have hsum := cls_sum μ Finset.univ (fun a g => ∑ c, T a c g) fun a _ => (hsumc a).1
  have hcls : cls μ (Om f) = ∑ a, ∑ c, cls μ (T a c) := by
    have h1 : cls μ (fun g => ∑ a, ∑ c, T a c g) = cls μ (Om f) :=
      cls_congr μ hsum.1 fun g hg => (hOm g hg).symm
    rw [← h1, hsum.2]
    exact Finset.sum_congr rfl fun a _ => (hsumc a).2

  have hterm : ∀ a c, (⟪cls μ (T a c), x⟫_ℂ).re ≤ (‖BY a c‖ ^ 2 + ‖BZ a c‖ ^ 2) / 4 * ‖x‖ ^ 2 := by
    intro a c
    set u := cls μ (Rd (bs (true, a, c)) f) with hu
    set u' := cls μ (Rd (bs (true, c, a)) f) with hu'
    set v := cls μ (Rd (bs (false, a, c)) f) with hv
    set v' := cls μ (Rd (bs (false, c, a)) f) with hv'
    have e1 : (⟪cls μ (T a c), x⟫_ℂ).re = -(⟪u', u⟫_ℂ).re + (⟪v', v⟫_ℂ).re := by
      have : cls μ (T a c) = _ := cls_sub μ (hd (true, a, c) (true, c, a)) (hd (false, a, c) (false, c, a))
      rw [this, inner_sub_left, hip, hip]
      simp [hu, hu', hv, hv']
    have b1 : ‖u - u'‖ ≤ ‖BY a c‖ * ‖x‖ := by
      refine norm_le_of_ae μ hf0 _ _ ?_
      filter_upwards [Lp.coeFn_sub u u', cls_ae μ (mem1 μ hS (true, a, c)), cls_ae μ (mem1 μ hS (true, c, a))] with y h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, ← hBY a c f hCE _ (val_mem y), Rd_sub, basis_true_eq_single, basis_true_eq_single]
    have b2 : ‖v + v'‖ ≤ ‖BZ a c‖ * ‖x‖ := by
      refine norm_le_of_ae μ hf0 _ _ ?_
      filter_upwards [Lp.coeFn_add v v', cls_ae μ (mem1 μ hS (false, a, c)), cls_ae μ (mem1 μ hS (false, c, a))] with y h1 h2 h3
      rw [h1, Pi.add_apply, h2, h3, ← hBZ a c f hCE _ (val_mem y), Rd_add, bs_f, bs_f]
    have p1 := pol_sub u u'
    have p2 := pol_add v v'
    have s1 : ‖u - u'‖ ^ 2 ≤ (‖BY a c‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) b1 2
    have s2 : ‖v + v'‖ ^ 2 ≤ (‖BZ a c‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) b2 2
    rw [e1]
    nlinarith
  rw [hcls, sum_inner, Complex.re_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [sum_inner, Complex.re_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun c _ => hterm a c

theorem secBound_main : SecBound := secBound GlobalTheory.T.sobolev_integration_by_parts

end GlobalTheory.CompanionTheory.SecBd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionNormBoundStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_norm_bound : PositivityTheory.RgBcC.Fc.SecBound := by
  first | exact @GlobalTheory.CompanionTheory.SecBd.secBound_main | exact GlobalTheory.CompanionTheory.SecBd.secBound_main | (intros; apply GlobalTheory.CompanionTheory.SecBd.secBound_main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnitaryRootMap
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnitaryRootMap
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

namespace GlobalTheory.CompanionTheory.SwapRoot

section Cont

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem continuous_of_v_eq (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x) : Continuous σ := by
  refine continuous_of_continuousAt_zero σ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero L _).tendsto_iff (Valued.hasBasis_nhds_zero L _)]
  refine fun γ _ => ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq] at hx ⊢
  rwa [show Valued.v.restrict (σ x) = Valued.v.restrict x from (Valuation.restrict_inj _).2 (hv x)]

theorem continuous_nU_val : Continuous fun x : L => ((nU x : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [nU] <;> first | exact continuous_id | exact continuous_const

theorem continuous_nU_inv_val :
    Continuous fun x : L => (((nU x)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [nU, Units.inv_mk] <;>
    first | exact continuous_id | exact continuous_const | exact continuous_neg

theorem continuous_partner_nU (σ : L →+* L) (hc : Continuous σ) :
    Continuous fun x : L => partner σ (nU x) := by
  unfold partner cT
  exact (continuous_const.matrix_mul
    (continuous_nU_inv_val.matrix_map hc).matrix_transpose).matrix_mul continuous_const

theorem continuous_uR_val (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ) (a : ℕ)
    (h : 2 * (a + 2) ≤ n) :
    Continuous fun x : L => (((uR σ hσ a h x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  simp only [uR, rootHom_val, blockM]
  exact (continuous_const.add (((continuous_const.matrix_mul
    (continuous_nU_val.sub continuous_const))).matrix_mul continuous_const)).add
    ((continuous_const.matrix_mul
    ((continuous_partner_nU σ hc).sub continuous_const)).matrix_mul continuous_const)

theorem uR_neg (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) :
    (uR σ hσ a h x)⁻¹ = uR σ hσ a h (-x) := by
  have h0 : uR σ hσ a h (0 : L) = 1 := by
    have e : nU (0 : L) = 1 := by
      ext p r; fin_cases p <;> fin_cases r <;> simp [nU]
    simp only [uR, e, map_one]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← uR_add, add_neg_cancel, h0]

theorem continuous_uR : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n),
    Continuous (uR σ hU.1 a h : L → GU σ n) := by
  intro L _ _ ϖ σ q n hU a h
  have hc : Continuous σ := continuous_of_v_eq σ hU.2.1
  refine Continuous.subtype_mk (f := fun x => ((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L)) ?_ _
  refine Units.continuous_iff.2 ⟨continuous_uR_val σ hU.1 hc a h, ?_⟩
  have e : ∀ x : L, ((((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (((uR σ hU.1 a h (-x) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := fun x => by
    rw [← uR_neg, Subgroup.coe_inv]
  simp only [e]
  exact (continuous_uR_val σ hU.1 hc a h).comp continuous_neg

end Cont

end GlobalTheory.CompanionTheory.SwapRoot

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnitaryRootMapStatement
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitary_root_map : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n), Continuous (uR σ hU.1 a h : L → GU σ n) := by
  first | exact @GlobalTheory.CompanionTheory.SwapRoot.continuous_uR | exact GlobalTheory.CompanionTheory.SwapRoot.continuous_uR | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.continuous_uR <;> assumption)
end
end
