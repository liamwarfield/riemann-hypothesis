module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawScalarFormsLawsOnClassData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DifferentiableAtLimitOfDirectionalDerivsConverge
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DifferentiableAtLimitOfDirectionalDerivsConverge
open scoped ContDiff Topology

namespace GlobalTheory

open Filter

theorem tendstoLocallyUniformly_sum_smul_const {E : Type} [TopologicalSpace E] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℂ F] {A : Type} (s : Finset A) (L : A → F)
    (f : A → ℕ → E → ℂ) (ψ : A → E → ℂ)
    (h : ∀ a, TendstoLocallyUniformly (f a) (ψ a) atTop) :
    TendstoLocallyUniformly (fun j y => ∑ a ∈ s, f a j y • L a)
      (fun y => ∑ a ∈ s, ψ a y • L a) atTop := by
  classical
  have hterm : ∀ a, TendstoLocallyUniformly (fun j y => f a j y • L a)
      (fun y => ψ a y • L a) atTop := by
    intro a
    have hu : UniformContinuous (fun z : ℂ => z • L a) :=
      ((ContinuousLinearMap.id ℂ ℂ).smulRight (L a)).uniformContinuous
    exact hu.comp_tendstoLocallyUniformly (h a)
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact fun u hu x => ⟨Set.univ, Filter.univ_mem,
      Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hterm a).add ih

theorem differentiableAt_of_tendstoLocallyUniformly_directional :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ (φ : E → ℂ) (g : ℕ → E → ℂ) (ψ : A → E → ℂ), (∀ j, Differentiable ℝ (g j)) → TendstoLocallyUniformly g φ Filter.atTop → (∀ a, TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (ψ a) Filter.atTop) → ∀ y, DifferentiableAt ℝ φ y ∧ ∀ a, fderiv ℝ φ y (v a) = ψ a y := by
  intro E _ _ A _ v c hvc φ g ψ hg hφ hψ y
  classical
  have hdecomp : (fun j z => fderiv ℝ (g j) z) =
      fun j z => ∑ a, fderiv ℝ (g j) z (v a) • (c a).smulRight (1 : ℂ) := by
    funext j z
    refine ContinuousLinearMap.ext fun x => ?_
    conv_lhs => rw [← hvc x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Complex.real_smul, mul_comm]
  have hconv : TendstoLocallyUniformly (fun j z => fderiv ℝ (g j) z)
      (fun z => ∑ a, ψ a z • (c a).smulRight (1 : ℂ)) Filter.atTop := by
    rw [hdecomp]
    exact tendstoLocallyUniformly_sum_smul_const Finset.univ (fun a => (c a).smulRight (1 : ℂ))
      (fun a j z => fderiv ℝ (g j) z (v a)) ψ hψ
  have hfd : HasFDerivAt φ (∑ a, ψ a y • (c a).smulRight (1 : ℂ)) y :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
      (hconv.tendstoLocallyUniformlyOn (s := Set.univ))
      (fun n z _ => (hg n z).hasFDerivAt)
      (fun z _ => (hφ.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ z))
      (Set.mem_univ y)
  refine ⟨hfd.differentiableAt, fun a => ?_⟩
  rw [hfd.fderiv]
  have h1 : Filter.Tendsto (fun j => fderiv ℝ (g j) y (v a)) Filter.atTop
      (𝓝 ((∑ b, ψ b y • (c b).smulRight (1 : ℂ)) (v a))) :=
    ((ContinuousLinearMap.apply ℝ ℂ (v a)).continuous.tendsto _).comp
      ((hconv.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ y))
  have h2 : Filter.Tendsto (fun j => fderiv ℝ (g j) y (v a)) Filter.atTop (𝓝 (ψ a y)) :=
    ((hψ a).tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ y)
  exact tendsto_nhds_unique h1 h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DifferentiableAtLimitOfDirectionalDerivsConvergeStatement
open scoped ContDiff Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableAt_limit_of_directional_derivs_converge : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ (φ : E → ℂ) (g : ℕ → E → ℂ) (ψ : A → E → ℂ), (∀ j, Differentiable ℝ (g j)) → TendstoLocallyUniformly g φ Filter.atTop → (∀ a, TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (ψ a) Filter.atTop) → ∀ y, DifferentiableAt ℝ φ y ∧ ∀ a, fderiv ℝ φ y (v a) = ψ a y := by
  first | exact @GlobalTheory.differentiableAt_of_tendstoLocallyUniformly_directional | exact GlobalTheory.differentiableAt_of_tendstoLocallyUniformly_directional | (intros; apply GlobalTheory.differentiableAt_of_tendstoLocallyUniformly_directional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsOpenLevelCompleteSobolev
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UniformCauchySeqOnHeisenbergWordSobolevCauchy
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UniformCauchySeqOnHeisenbergWordSobolevCauchy
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.ThetaDensCauchy

open GlobalTheory.Size

section

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem word_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
    {f f' : WO S T → ℂ} (h : IsThetaFunO ψ S T f) (h' : IsThetaFunO ψ S T f') :
    GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (f + f') =
      GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f + GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons, ih]
    exact GlobalTheory.Size.dRho_add hψ hθ a.1 _ (GlobalTheory.Size.theta_word hψ hθ l h) (GlobalTheory.Size.theta_word hψ hθ l h')

theorem word_mem (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
    {U : AddSubgroup (WO S T)} {f : WO S T → ℂ} (h : f ∈ GlobalTheory.Size.thetaLevel ψ S T U) :
    GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f ∈ GlobalTheory.Size.thetaLevel ψ S T U := by
  induction l with
  | nil => exact h
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons]
    exact GlobalTheory.Size.dRho_mem_thetaLevel hψ hθ ih a.1 _

theorem sobO_word_le (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (f : WO S T → ℂ) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) ≤ sobO ψ θ μ 𝓕 (d + l.length) f := by
  induction l generalizing d with
  | nil => exact le_rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons]
    refine (GlobalTheory.Size.sobO_heisDer_le d a).trans ((ih (d + 1)).trans (le_of_eq ?_))
    congr 1
    simp only [List.length_cons]
    omega

end

theorem uniformCauchySeqOn_word : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ GlobalTheory.Size.thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), UniformCauchySeqOn (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) Filter.atTop Set.univ := by
  intro D ψ hψ θ hθ S T μ 𝓕 hm U hU u hu hC l
  obtain ⟨d₀, C, hb⟩ := GlobalTheory.ThetaDensSup.sup_le_sobO D ψ hψ θ hθ S T μ 𝓕 hm U hU
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hη : (0 : ℝ) < ε / (C + 1) := by positivity
  obtain ⟨J, hJ⟩ := hC (d₀ + l.length) (ENNReal.ofReal (ε / (C + 1))) (ENNReal.ofReal_pos.2 hη)
  refine ⟨J, fun i hi j hj w _ => ?_⟩
  have hd : u i - u j ∈ GlobalTheory.Size.thetaLevel ψ S T U := Submodule.sub_mem _ (hu i) (hu j)
  have he := word_add hψ hθ l hd.1 (hu j).1
  rw [sub_add_cancel] at he
  have h1 := (hb _ (word_mem hψ hθ l hd) w).trans
    (mul_le_mul_right ((sobO_word_le μ 𝓕 l _ d₀).trans (hJ i hi j hj).le) _)
  rw [dist_eq_norm, he, Pi.add_apply, add_sub_cancel_right]
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  refine h1.trans_lt ?_
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
  nlinarith

end GlobalTheory.ThetaDensCauchy
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UniformCauchySeqOnHeisenbergWordSobolevCauchyStatement
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformCauchySeqOn_heisenbergWord_sobolevCauchy : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ GlobalTheory.Size.thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), UniformCauchySeqOn (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) Filter.atTop Set.univ := by
  first | exact @GlobalTheory.ThetaDensCauchy.uniformCauchySeqOn_word | exact GlobalTheory.ThetaDensCauchy.uniformCauchySeqOn_word | (intros; apply GlobalTheory.ThetaDensCauchy.uniformCauchySeqOn_word <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaWordLimitsSmoothAlongRealPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothOfLimitClassStableUnderDirectionalDerivs
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothOfLimitClassStableUnderDirectionalDerivs
open scoped ContDiff Topology

namespace GlobalTheory

theorem contDiff_of_class_tendstoLocallyUniformly : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ P : (E → ℂ) → Prop, (∀ φ, P φ → ∃ g : ℕ → E → ℂ, (∀ j, Differentiable ℝ (g j)) ∧ TendstoLocallyUniformly g φ Filter.atTop ∧ ∀ a, ∃ α : E → ℂ, ContDiff ℝ ∞ α ∧ ∃ χ, P χ ∧ TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (fun y => α y * φ y + χ y) Filter.atTop) → ∀ φ, P φ → ContDiff ℝ ∞ φ := by
  intro E _ _ A _ v c hc P hP
  have key : ∀ φ, P φ → Differentiable ℝ φ ∧ ∃ (α χ : A → E → ℂ), (∀ a, ContDiff ℝ ∞ (α a)) ∧
      (∀ a, P (χ a)) ∧ fderiv ℝ φ =
        fun y => ∑ a, (α a y * φ y + χ a y) • ((c a).smulRight (1 : ℂ)) := by
    intro φ hφ
    obtain ⟨g, hg, hlim, hd⟩ := hP φ hφ
    choose α hα χ hχ hlim' using hd
    have h := GlobalTheory.T.differentiableAt_limit_of_directional_derivs_converge v c hc φ g (fun a y => α a y * φ y + χ a y) hg hlim hlim'
    refine ⟨fun y => (h y).1, α, χ, hα, hχ, ?_⟩
    funext y
    ext x
    conv_lhs => rw [← hc x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, (h y).2, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Complex.real_smul, smul_eq_mul]
    ring
  have main : ∀ n : ℕ, ∀ φ, P φ → ContDiff ℝ n φ := by
    intro n
    induction n with
    | zero =>
      intro φ hφ
      simpa using (key φ hφ).1.continuous
    | succ n ih =>
      intro φ hφ
      obtain ⟨hd, α, χ, hα, hχ, hf⟩ := key φ hφ
      have : ContDiff ℝ ((n : WithTop ℕ∞) + 1) φ := by
        rw [contDiff_succ_iff_fderiv]
        refine ⟨hd, by simp, ?_⟩
        rw [hf]
        refine ContDiff.sum fun a _ => ?_
        have h1 : ContDiff ℝ n (α a) := (hα a).of_le (by exact_mod_cast le_top)
        exact ((h1.mul (ih φ hφ)).add (ih _ (hχ a))).smul contDiff_const
      exact_mod_cast this
  intro φ hφ
  exact contDiff_infty.2 fun n => main n φ hφ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothOfLimitClassStableUnderDirectionalDerivsStatement
open scoped ContDiff Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_of_limit_class_stable_under_directional_derivs : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ P : (E → ℂ) → Prop, (∀ φ, P φ → ∃ g : ℕ → E → ℂ, (∀ j, Differentiable ℝ (g j)) ∧ TendstoLocallyUniformly g φ Filter.atTop ∧ ∀ a, ∃ α : E → ℂ, ContDiff ℝ ∞ α ∧ ∃ χ, P χ ∧ TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (fun y => α y * φ y + χ y) Filter.atTop) → ∀ φ, P φ → ContDiff ℝ ∞ φ := by
  first | exact @GlobalTheory.contDiff_of_class_tendstoLocallyUniformly | exact GlobalTheory.contDiff_of_class_tendstoLocallyUniformly | (intros; apply GlobalTheory.contDiff_of_class_tendstoLocallyUniformly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaWordLimitsSmoothAlongRealPoints
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaDens


open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.Size in
theorem sm_of_tendstoUniformly_words {G R A : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    [FiniteDimensional ℝ R] [Fintype A] (ι : R →+ G) (p : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (hp : ∀ x, p (ι x) = x)
    (v : A → R) (c : A → R →L[ℝ] ℝ) (hv : ∀ x, ∑ a, c a x • v a = x) (g : List A → ℕ → G → ℂ)
    (hg : ∀ l j, Sm ι (g l j)) (hd : ∀ a l j, g (a :: l) j = hD ι p om (v a) (g l j)) (F : List A → G → ℂ)
    (hF : ∀ l, TendstoUniformly (g l) (F l) Filter.atTop) (l : List A) : Sm ι (F l) := by
  intro w
  refine GlobalTheory.T.smooth_of_limit_class_stable_under_directional_derivs v c hv (fun φ => ∃ l, φ = fun y => F l (w + ι y)) ?_ _ ⟨l, rfl⟩
  rintro _ ⟨l, rfl⟩
  have hU : ∀ l, TendstoLocallyUniformly (fun j y => g l j (w + ι y)) (fun y => F l (w + ι y)) Filter.atTop :=
    fun l => ((hF l).comp fun y => w + ι y).tendstoLocallyUniformly
  refine ⟨fun j y => g l j (w + ι y), fun j => (hg l j w).differentiable (by simp), hU l, fun a => ?_⟩
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : R => (om.flip (v a) (p w + x) : ℝ) :=
    (LinearMap.toContinuousLinearMap (om.flip (v a))).contDiff.comp (contDiff_const.add contDiff_id)
  have hα : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun x : R => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h1)
  refine ⟨_, hα, _, ⟨a :: l, rfl⟩, ?_⟩
  have hc : Continuous fun y => F l (w + ι y) :=
    (hU l).continuous (Filter.Eventually.of_forall fun j => (hg l j w).continuous).frequently
  have h0 : TendstoLocallyUniformly
      (fun (_ : ℕ) (x : R) => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ))
      (fun x : R => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ)) Filter.atTop :=
    fun U hU x => ⟨Set.univ, Filter.univ_mem, Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hU⟩
  have h2 := (h0.mul₀ (hU l) hα.continuous hc).add (hU (a :: l))
  have e : (fun j y => fderiv ℝ (fun y => g l j (w + ι y)) y (v a)) = fun j x =>
      (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ) * g l j (w + ι x) + g (a :: l) j (w + ι x) := by
    funext j x
    rw [hd, hD_eq_fderiv ι p om _ (hg l j), map_add p, hp, LinearMap.flip_apply]
    have := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : R => g l j (w + ι y)) (x := 0) x
    rw [add_zero] at this
    have e2 : (fun y : R => g l j (w + ι x + ι y)) = fun y => g l j (w + ι (x + y)) := by
      funext y
      rw [map_add (f := _), add_assoc]
    rw [← this, e2]
    ring
  rw [e]
  exact h2

theorem sum_coord_single {τs : Type} [Fintype τs] {m n : ℕ} (x : τs → Fin m → Fin n → ℂ)
    (v : τs × Fin m × Fin n × Bool → τs → Fin m → Fin n → ℂ)
    (hv : ∀ a τ i j, v a τ i j = if τ = a.1 then
      Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) i j else 0) :
    ∑ a : τs × Fin m × Fin n × Bool,
      (if a.2.2.2 then (x a.1 a.2.1 a.2.2.1).im else (x a.1 a.2.1 a.2.2.1).re) • v a = x := by
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, hv, Fintype.sum_prod_type, Matrix.single_apply]
  rw [Finset.sum_eq_single τ (fun b _ hb => by simp [hb.symm]) (by simp),
    Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp),
    Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp [add_comm]


open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.Size in
theorem contDiff_of_tendstoUniformly_words : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (u : ℕ → WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (u j)) → ∀ F : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) → WO S T → ℂ, (∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop) → ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => F l (w + L t) := by
  intro D ψ hψ θ hθ S T u hu F hF l
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  refine ((smooth_iff_sm_and_real_lines D θ σ h T S).1 (F l)).2 ?_
  let z : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun a =>
    Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)
  let c : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool → RW T S →L[ℝ] ℝ := fun a =>
    (if a.2.2.2 then Complex.imCLM else Complex.reCLM).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin S.rank => ℂ) a.2.2.1).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin T.rank => Fin S.rank → ℂ) a.2.1).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin T.rank → Fin S.rank → ℂ) a.1)))
  refine sm_of_tendstoUniformly_words (iotaW σ T S) (piW θ T S) (omO S T) (h.pi_iota T S)
    (fun a => piW θ T S (lineAt θ a.1 (z a) 1)) c (fun x => ?_) (fun l j => wordAct (heisDer ψ θ) l (u j))
    (fun l j => theta_sm h (theta_word hψ hθ l (hu j)))
    (fun a l j => dLine_eq_hD h hψ (isRealDir_lineAt hθ a.1 (z a)) _) F hF l
  refine Eq.trans ?_ (sum_coord_single x (fun a => piW θ T S (lineAt θ a.1 (z a) 1)) fun a τ i j => ?_)
  · refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    obtain ⟨τ, i, j, b⟩ := a
    cases b <;> rfl
  · have := congrFun (congrFun ((GlobalTheory.OrientedHeis.isLineAt_lineAt hθ a.1 (z a)).2.2 1 τ) i) j
    refine Eq.trans this ?_
    split_ifs <;> simp [z, *]

end GlobalTheory.ThetaDens
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaWordLimitsSmoothAlongRealPointsStatement
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_word_limits_smooth_along_real_points : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (u : ℕ → WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (u j)) → ∀ F : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) → WO S T → ℂ, (∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop) → ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => F l (w + L t) := by
  first | exact @GlobalTheory.ThetaDens.contDiff_of_tendstoUniformly_words | exact GlobalTheory.ThetaDens.contDiff_of_tendstoUniformly_words | (intros; apply GlobalTheory.ThetaDens.contDiff_of_tendstoUniformly_words <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergBasisDerivEqOfUniformLimits
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergBasisDerivEqOfUniformLimits
noncomputable section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaLimDeriv

theorem tendstoUniformly_heisO {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {G : ℕ → WO S T → ℂ} {F : WO S T → ℂ} (h : TendstoUniformly G F Filter.atTop) (x : ℝ → WO S T) (w : WO S T) :
    TendstoUniformly (fun j t => heisO ψ S T (x t) (G j) w) (fun t => heisO ψ S T (x t) F w) Filter.atTop := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with j hj t
  have := hj (w + x t)
  rw [dist_eq_norm] at this ⊢
  simp only [heisO]
  rw [← mul_sub, norm_mul, hψ.1.2.1, one_mul]
  exact this

theorem heisDer_of_tendstoUniformly : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (G : ℕ → WO S T → ℂ) (F F' : WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (G j)) → TendstoUniformly G F Filter.atTop → ∀ a : (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.heisDer ψ θ a (G j)) F' Filter.atTop → GlobalTheory.Size.heisDer ψ θ a F = F' := by
  intro D ψ hψ θ hθ S T G F F' hG hF a hF'
  have hL := GlobalTheory.OrientedHeis.isRealDir_lineAt (S := S) (T := T) hθ a.1
    (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))
  have e : ∀ f, GlobalTheory.Size.heisDer ψ θ a f = GlobalTheory.OrientedHeis.dLine ψ S T
      (lineAt θ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) f := fun _ => rfl
  simp only [e] at hF' ⊢
  generalize lineAt θ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) = L at hL hF' ⊢
  funext w
  have h1 := tendstoUniformly_heisO hψ hF L w
  have h2 := tendstoUniformly_heisO hψ hF' L w
  have h3 := hasDerivAt_of_tendstoUniformly h2
    (Filter.Eventually.of_forall fun j s => GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hL (hG j) w s)
    (fun s => h1.tendsto_at s) 0
  have h4 := h3.deriv
  rw [map_zero, GlobalTheory.OrientedHeis.heisO_zero] at h4
  exact h4

end GlobalTheory.ThetaLimDeriv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergBasisDerivEqOfUniformLimitsStatement
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergBasisDeriv_eq_of_uniform_limits : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (G : ℕ → WO S T → ℂ) (F F' : WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (G j)) → TendstoUniformly G F Filter.atTop → ∀ a : (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.heisDer ψ θ a (G j)) F' Filter.atTop → GlobalTheory.Size.heisDer ψ θ a F = F' := by
  first | exact @GlobalTheory.ThetaLimDeriv.heisDer_of_tendstoUniformly | exact GlobalTheory.ThetaLimDeriv.heisDer_of_tendstoUniformly | (intros; apply GlobalTheory.ThetaLimDeriv.heisDer_of_tendstoUniformly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsOpenLevelCompleteSobolev
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaComplete

theorem lim_clauses : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (U : AddSubgroup (WO S T)) (u : ℕ → WO S T → ℂ), (∀ j, u j ∈ GlobalTheory.Size.thetaLevel ψ S T U) → ∀ f : WO S T → ℂ, TendstoUniformly u f Filter.atTop → (∀ γ w, f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w) ∧ (∀ x ∈ U, x.map (infPart D) = 0 → heisO ψ S T x f = f) ∧ Continuous f := by
  intro D ψ S T U u hu f hf
  have ht : ∀ w, Filter.Tendsto (fun j => u j w) Filter.atTop (nhds (f w)) := fun w => hf.tendsto_at w
  refine ⟨fun γ w => ?_, fun x hx h0 => ?_, hf.continuous (Filter.Frequently.of_forall fun j => (hu j).1.cont)⟩
  · refine tendsto_nhds_unique (ht _) ?_
    have e : (fun j => u j (ratW T S γ + w)) = fun j => ψ (-(symplOH S T (ratW T S γ) w)) * u j w :=
      funext fun j => (hu j).1.quasi γ w
    rw [e]
    exact (ht w).const_mul _
  · funext w
    refine tendsto_nhds_unique ((ht (w + x)).const_mul (ψ (symplOH S T w x))) ?_
    have e : (fun j => ψ (symplOH S T w x) * u j (w + x)) = fun j => u j w :=
      funext fun j => congrFun ((hu j).2 x hx h0) w
    rw [e]
    exact ht w

theorem lim_deriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (G : ℕ → WO S T → ℂ) (F F' : WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (G j)) → TendstoUniformly G F Filter.atTop → ∀ a : (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.heisDer ψ θ a (G j)) F' Filter.atTop → GlobalTheory.Size.heisDer ψ θ a F = F' := GlobalTheory.T.heisenbergBasisDeriv_eq_of_uniform_limits
theorem lim_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (u : ℕ → WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (u j)) → ∀ F : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) → WO S T → ℂ, (∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop) → ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => F l (w + L t) := GlobalTheory.T.theta_word_limits_smooth_along_real_points

theorem limit_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ GlobalTheory.Size.thetaLevel ψ S T U) → ∀ F : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) → WO S T → ℂ, (∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop) → F [] ∈ GlobalTheory.Size.thetaLevel ψ S T U ∧ ∀ l, GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (F []) = F l := by
  intro D ψ hψ θ hθ S T U hU u hu F hF
  have h0 := lim_clauses D ψ S T U u hu (F []) (hF [])
  have hth : IsThetaFunO ψ S T (F []) :=
    ⟨h0.1, ⟨U, hU, h0.2.1⟩, h0.2.2, lim_smooth D ψ hψ θ hθ S T u (fun j => (hu j).1) F hF []⟩
  refine ⟨⟨hth, h0.2.1⟩, fun l => ?_⟩
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons, ih]
    exact lim_deriv D ψ hψ θ hθ S T (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) (F (a :: l))
      (fun j => GlobalTheory.Size.theta_word hψ hθ l (hu j).1) (hF l) a (hF (a :: l))

theorem complete : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ GlobalTheory.Size.thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∃ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0) := by
  intro D ψ hψ θ hθ S T μ 𝓕 hμ U hU u hu hc
  have hC := GlobalTheory.T.uniformCauchySeqOn_heisenbergWord_sobolevCauchy D ψ hψ θ hθ S T μ 𝓕 hμ U hU u hu hc
  have hlim : ∀ l w, ∃ z, Filter.Tendsto (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j) w) Filter.atTop (nhds z) :=
    fun l w => cauchySeq_tendsto_of_complete ((hC l).cauchySeq (Set.mem_univ w))
  choose F hF using hlim
  have hFu : ∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop :=
    fun l => tendstoUniformlyOn_univ.1 ((hC l).tendstoUniformlyOn_of_tendsto fun w _ => hF l w)
  obtain ⟨h1, h2⟩ := limit_theta D ψ hψ θ hθ S T U hU u hu F hFu
  refine ⟨F [], h1, GlobalTheory.T.thetaSobolevSeminorm_sub_tendsto_zero_of_words_unif D ψ hψ θ hθ S T μ 𝓕 hμ u (F []) h1.1 (fun j => (hu j).1) fun l => ?_⟩
  rw [h2 l]
  exact hFu l

end GlobalTheory.ThetaComplete
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsOpenLevelCompleteSobolevStatement
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunctions_open_level_complete_sobolev : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ GlobalTheory.Size.thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∃ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.ThetaComplete.complete | exact GlobalTheory.ThetaComplete.complete | (intros; apply GlobalTheory.ThetaComplete.complete <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LscSeminormThetaFunctionsLevelLeSobolev
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.SobBaire

open Filter Topology
open scoped Uniformity

theorem exists_bound_of_complete {E : Type} [AddCommGroup E] [Module ℂ E] (p : ℕ → Seminorm ℂ E)
    (hmono : ∀ d x, p d x ≤ p (d + 1) x)
    (hcomp : ∀ u : ℕ → E, (∀ d, ∀ ε > 0, ∃ J, ∀ i ≥ J, ∀ j ≥ J, p d (u i - u j) < ε) →
      ∃ x, ∀ d, Tendsto (fun j => p d (u j - x)) atTop (𝓝 0))
    (q : Seminorm ℂ E) (hq : ∀ (u : ℕ → E) (x : E), (∀ d, Tendsto (fun j => p d (u j - x)) atTop (𝓝 0)) →
      ∀ y : ℝ, (∀ j, q (u j) ≤ y) → q x ≤ y) :
    ∃ (d : ℕ) (C : ℝ≥0), ∀ x, q x ≤ C * p d x := by
  letI t : TopologicalSpace E := (SeminormFamily.moduleFilterBasis (𝕜 := ℂ) p).topology
  have hp : WithSeminorms p := ⟨rfl⟩
  haveI : IsTopologicalAddGroup E := hp.topologicalAddGroup
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  haveI : ContinuousSMul ℂ E := hp.continuousSMul
  haveI : FirstCountableTopology E := hp.firstCountableTopology
  haveI : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : CompleteSpace E := by
    refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ?_
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff] at hu
    obtain ⟨x, hx⟩ := hcomp u fun d ε hε => by
      have h := (hp.tendsto_nhds _ 0).1 hu d ε hε
      obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h
      refine ⟨max N₁ N₂, fun i hi j hj => ?_⟩
      have := hN (j, i) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hj, le_of_max_le_right hi⟩)
      simpa using this
    refine ⟨x, (hp.tendsto_nhds u x).2 fun d ε hε => ?_⟩
    exact (hx d).eventually (gt_mem_nhds hε)
  haveI : BarrelledSpace ℂ E := inferInstance
  have hlsc : LowerSemicontinuous q := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro y
    refine IsSeqClosed.isClosed fun u x hu hx => ?_
    exact hq u x (fun d => by
      have := ((hp.continuous_seminorm d).tendsto 0).comp ((tendsto_sub_nhds_zero_iff).2 hx)
      simpa [Function.comp_def] using this) y hu
  have hc : Continuous q := Seminorm.continuous_of_lowerSemicontinuous q hlsc
  obtain ⟨s, C, -, hle⟩ := Seminorm.bound_of_continuous hp q hc
  have hmono' : ∀ d d' x, d ≤ d' → p d x ≤ p d' x := fun d d' x h => by
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hmono _ x)
  refine ⟨s.sup id, C, fun x => (hle x).trans ?_⟩
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ C.2
  exact Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi => hmono' _ _ _ (Finset.le_sup (f := id) hi)

end GlobalTheory.SobBaire

namespace GlobalTheory.SobBaire

open Filter Topology

theorem le_mul_sobO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ N : (WO S T → ℂ) → ℝ≥0∞, (∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ g ∈ GlobalTheory.Size.thetaLevel ψ S T U, N (f + g) ≤ N f + N g) → (∀ (c : ℂ), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, N (c • f) = ‖c‖ₑ * N f) → (∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, N f ≠ ⊤) → (∀ (u : ℕ → WO S T → ℂ), (∀ j, u j ∈ GlobalTheory.Size.thetaLevel ψ S T U) → ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, (∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0)) → N f ≤ Filter.liminf (fun j => N (u j)) Filter.atTop) → ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, N f ≤ C * sobO ψ θ μ 𝓕 d f := by
  intro D ψ hψ θ hθ S T μ 𝓕 hm U hU N hadd hsmul hfin hlsc
  have hB := GlobalTheory.T.thetaFunctions_open_level_complete_sobolev D ψ hψ θ hθ S T μ 𝓕 hm U hU
  let E := GlobalTheory.Size.thetaLevel ψ S T U
  have hsf : ∀ d (f : E), sobO ψ θ μ 𝓕 d (f : WO S T → ℂ) ≠ ⊤ := fun d f =>
    GlobalTheory.Size.sobO_ne_top hψ hθ hm.1 hm.2.1 f.2.1 d
  let p : ℕ → Seminorm ℂ E := fun d => Seminorm.of (fun f => (sobO ψ θ μ 𝓕 d (f : WO S T → ℂ)).toReal)
    (fun f g => by
      rw [← ENNReal.toReal_add (hsf d f) (hsf d g)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hsf d f, hsf d g⟩)
        (GlobalTheory.Size.sobO_add_le hψ hθ f.2.1 g.2.1 d))
    (fun c f => by
      show (sobO ψ θ μ 𝓕 d (c • (f : WO S T → ℂ))).toReal = _
      rw [GlobalTheory.Size.sobO_smul, ENNReal.toReal_mul, toReal_enorm])
  have hp : ∀ d (f : E), p d f = (sobO ψ θ μ 𝓕 d (f : WO S T → ℂ)).toReal := fun _ _ => rfl
  let q : Seminorm ℂ E := Seminorm.of (fun f => (N f).toReal)
    (fun f g => by
      rw [← ENNReal.toReal_add (hfin f f.2) (hfin g g.2)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin f f.2, hfin g g.2⟩) (hadd f f.2 g g.2))
    (fun c f => by
      show (N (c • (f : WO S T → ℂ))).toReal = _
      rw [hsmul c f f.2, ENNReal.toReal_mul, toReal_enorm])
  have hq : ∀ f : E, q f = (N f).toReal := fun _ => rfl
  obtain ⟨d, C, hC⟩ := exists_bound_of_complete p
    (fun d f => by
      rw [hp, hp]
      exact ENNReal.toReal_mono (hsf _ f) (GlobalTheory.Size.sobO_mono (Nat.le_succ d)))
    (fun u hu => by
      obtain ⟨f, hf, hlim⟩ := hB (fun j => (u j : WO S T → ℂ)) (fun j => (u j).2) fun d ε hε => by
        rcases eq_or_ne ε ⊤ with rfl | hεt
        · exact ⟨0, fun i _ j _ => lt_top_iff_ne_top.2 (hsf d (u i - u j))⟩
        obtain ⟨J, hJ⟩ := hu d ε.toReal (ENNReal.toReal_pos hε.ne' hεt)
        refine ⟨J, fun i hi j hj => ?_⟩
        have := hJ i hi j hj
        rw [hp] at this
        exact (ENNReal.toReal_lt_toReal (hsf d (u i - u j)) hεt).1 this
      refine ⟨⟨f, hf⟩, fun d => ?_⟩
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hlim d)
      simpa [hp, Function.comp_def] using this)
    q (fun u x hux y hy => by
      have hy0 : 0 ≤ y := (apply_nonneg q (u 0)).trans (hy 0)
      have hconv : ∀ d, Tendsto (fun j => sobO ψ θ μ 𝓕 d ((u j : WO S T → ℂ) - x)) atTop (𝓝 0) := fun d => by
        have h1 := hux d
        simp only [hp] at h1
        rw [← ENNReal.toReal_zero] at h1
        exact (ENNReal.tendsto_toReal_iff (fun j => hsf d (u j - x)) ENNReal.zero_ne_top).1 h1
      have h2 := hlsc (fun j => (u j : WO S T → ℂ)) (fun j => (u j).2) x x.2 hconv
      have h3 : Filter.liminf (fun j => N (u j : WO S T → ℂ)) atTop ≤ ENNReal.ofReal y :=
        Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun j => by
          rw [← ENNReal.ofReal_toReal (hfin _ (u j).2)]
          exact ENNReal.ofReal_le_ofReal ((hq _).symm.trans_le (hy j) |>.trans_eq' rfl))
      rw [hq]
      exact ENNReal.toReal_le_of_le_ofReal hy0 (h2.trans h3))
  refine ⟨d, C, fun f hf => ?_⟩
  have h := hC ⟨f, hf⟩
  rw [hq, hp] at h
  calc N f = ENNReal.ofReal (N f).toReal := (ENNReal.ofReal_toReal (hfin f hf)).symm
    _ ≤ ENNReal.ofReal (C * (sobO ψ θ μ 𝓕 d f).toReal) := ENNReal.ofReal_le_ofReal h
    _ = C * sobO ψ θ μ 𝓕 d f := by
      rw [ENNReal.ofReal_mul (NNReal.coe_nonneg C), ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_toReal (GlobalTheory.Size.sobO_ne_top hψ hθ hm.1 hm.2.1 hf.1 d)]

end GlobalTheory.SobBaire
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LscSeminormThetaFunctionsLevelLeSobolevStatement
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lsc_seminorm_thetaFunctionsLevel_le_sobolev : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ N : (WO S T → ℂ) → ℝ≥0∞, (∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ g ∈ GlobalTheory.Size.thetaLevel ψ S T U, N (f + g) ≤ N f + N g) → (∀ (c : ℂ), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, N (c • f) = ‖c‖ₑ * N f) → (∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, N f ≠ ⊤) → (∀ (u : ℕ → WO S T → ℂ), (∀ j, u j ∈ GlobalTheory.Size.thetaLevel ψ S T U) → ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, (∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0)) → N f ≤ Filter.liminf (fun j => N (u j)) Filter.atTop) → ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, N f ≤ C * sobO ψ θ μ 𝓕 d f := by
  first | exact @GlobalTheory.SobBaire.le_mul_sobO | exact GlobalTheory.SobBaire.le_mul_sobO | (intros; apply GlobalTheory.SobBaire.le_mul_sobO <;> assumption)
end
