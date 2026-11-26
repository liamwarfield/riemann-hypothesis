module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectivePairingFiniteFamily
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassThird

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinCoefficientsSummable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterAlongOneParameterPath
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterAlongOneParameterPath
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section
namespace GlobalTheory.CompanionTheory.WSum

variable {D : D7}

theorem trace_incA_algebraMap_mul (D : D7) (β : D.host.F) (z : AE D) :
    Algebra.trace (AF D.host.F) (AE D) (incA D (algebraMap D.host.F D.host.E β) * z) =
      algebraMap D.host.F (AF D.host.F) β * Algebra.trace (AF D.host.F) (AE D) z := by
  have h : incA D (algebraMap D.host.F D.host.E β) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) β) := by
    show (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E β) =
      (algebraMap D.host.F (AF D.host.F) β) ⊗ₜ[D.host.F] (1 : D.host.E)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [h, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem theta_half_rs {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    {α β : D.host.F} (hβ : β + β = α) (s : ℝ) (t : AE D) (ρ : D.what₂.Tau) :
    θ ρ (infPart D (incA D (algebraMap D.host.F D.host.E β) * (rs σ s * t))) =
      ((1 / 2 * s : ℝ) : ℂ) * θ ρ (infPart D (incA D (algebraMap D.host.F D.host.E α) * t)) := by
  have hi : ∀ e, θ ρ (infPart D (incA D e)) = tauE D ρ e := fun e => (hσ.inf ρ).1 e
  have hs : θ ρ (infPart D (rs σ s)) = (s : ℂ) := hσ.comp _ ρ
  have hb : tauE D ρ (algebraMap D.host.F D.host.E α) =
      tauE D ρ (algebraMap D.host.F D.host.E β) + tauE D ρ (algebraMap D.host.F D.host.E β) := by
    rw [← map_add (f := _), ← map_add (f := _), hβ]
  rw [map_mul (infPart D), map_mul (θ ρ), hi, map_mul (infPart D), map_mul (θ ρ), hs,
    map_mul (infPart D), map_mul (θ ρ), hi, hb]
  push_cast
  ring

theorem psi_halfTr_rs : ∀ (D : D7) (ψ ψ₀ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ₀ (-1) → ∀ α : D.host.F,
    (∀ x, ψ x = ψ₀ (algebraMap D.host.F (AF D.host.F) α * x)) → ∀ (θ : InfFam D)
    (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (t : AE D) (s : ℝ),
    ψ (halfTr (rs σ s * t)) = Complex.exp (2 * Real.pi * Complex.I * ((s * lam θ α t : ℝ) : ℂ)) := by
  intro D ψ ψ₀ h₀ α hψ θ σ hσ t s
  obtain ⟨β, hβ', hβ⟩ : ∃ β : D.host.F, β = α * (1 / 2) ∧ β + β = α := ⟨_, rfl, by ring⟩
  set z' : AE D := incA D (algebraMap D.host.F D.host.E β) * (rs σ s * t) with hz'
  have hR : algebraMap D.host.F (AF D.host.F) α * halfTr (rs σ s * t) =
      Algebra.trace (AF D.host.F) (AE D) z' := by
    rw [hz', trace_incA_algebraMap_mul, hβ', map_mul, mul_assoc]
    rfl
  have hfin : finPart D z' = 0 := by
    have h0 : finPart D (rs σ s) = 0 := hσ.fin _
    rw [hz', map_mul (finPart D), map_mul (finPart D) (rs σ s), h0, zero_mul, mul_zero]
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set R := Algebra.trace (AF D.host.F) (AE D) z' with hRdef
  have h1 : ψ₀ R = psiInf D.host.F ψ₀ (fstA D.host.F R) := by
    unfold psiInf
    rw [← hT]
  have h2 := h₀.2.2 θ hσ.inf (fstA D.host.F R)
  have h3 : ∀ ρ, θ ρ (fstA D.host.F R ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((s * (θ ρ (infPart D (incA D (algebraMap D.host.F D.host.E α) * t))).re : ℝ) : ℂ) := by
    intro ρ
    rw [hRdef, GlobalTheory.PhaseReal.theta_trace θ hσ.inf ρ z', hz', theta_half_rs hσ hβ, Complex.re_ofReal_mul]
    congr 1
    ring
  rw [hψ, hR, h1, h2]
  congr 1
  simp only [h3]
  rw [← Complex.ofReal_sum, ← Finset.mul_sum]
  unfold lam
  push_cast
  ring

end GlobalTheory.CompanionTheory.WSum
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterAlongOneParameterPathStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_along_one_parameter_path : ∀ (D : D7) (ψ ψ₀ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ₀ (-1) → ∀ α : D.host.F, (∀ x, ψ x = ψ₀ (algebraMap D.host.F (AF D.host.F) α * x)) → ∀ (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (t : AE D) (s : ℝ), ψ (halfTr (rs σ s * t)) = Complex.exp (2 * Real.pi * Complex.I * ((s * lam θ α t : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.WSum.psi_halfTr_rs | exact GlobalTheory.CompanionTheory.WSum.psi_halfTr_rs | (intros; apply GlobalTheory.CompanionTheory.WSum.psi_halfTr_rs <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfLatticeDecay
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfLatticeDecay
open MeasureTheory

namespace GlobalTheory.CompanionTheory.LatticeCount

theorem summable_inv_one_add_sq_int :
    Summable (fun m : ℤ => ((1 : ℝ) + (m : ℝ) ^ 2)⁻¹) := by
  have h : Summable (fun m : ℤ => 1 / (m : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  refine Summable.of_norm_bounded_eventually h ?_
  have hfin : ({0} : Set ℤ).Finite := Set.finite_singleton 0
  refine Filter.mem_cofinite.2 (hfin.subset ?_)
  intro m hm
  by_contra h0
  have h0' : m ≠ 0 := by simpa using h0
  apply hm
  have hm0 : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (m : ℝ) ≠ 0 := by exact_mod_cast h0'
    positivity
  have hpos : (0 : ℝ) < 1 + (m : ℝ) ^ 2 := by positivity
  show ‖((1 : ℝ) + (m : ℝ) ^ 2)⁻¹‖ ≤ 1 / (m : ℝ) ^ 2
  rw [Real.norm_of_nonneg (inv_nonneg.2 hpos.le), one_div]
  exact inv_anti₀ hm0 (by linarith)

theorem summable_prod_inv_one_add_sq (d : ℕ) :
    Summable (fun n : Fin d → ℤ => ∏ k, ((1 : ℝ) + (n k : ℝ) ^ 2)⁻¹) := by
  induction d with
  | zero => exact Summable.of_finite
  | succ d ih =>
    have h2 := summable_inv_one_add_sq_int.mul_of_nonneg ih
      (fun m => by positivity) (fun n => Finset.prod_nonneg (fun k _ => by positivity))
    rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).summable_iff]
    refine h2.congr ?_
    intro x
    simp [Fin.prod_univ_succ, Fin.consEquiv]
    exact mul_comm _ _

theorem summable_of_lattice_decay (ι : Type) (d : ℕ) (w : ι → ℂ) (f : ι → Fin d → ℝ)
    (hf : Function.Injective f) (N : ℕ) (hN : 0 < N) (C : ℝ)
    (hC : ∀ i, ‖w i‖ * ∏ k, (1 + f i k ^ 2) ≤ C)
    (hint : ∀ i, w i ≠ 0 → ∀ k, ∃ n : ℤ, (N : ℝ) * f i k = n) : Summable w := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let S := {i // w i ≠ 0}
  choose n hn using fun i : S => hint i.1 i.2
  have hinj : Function.Injective n := by
    intro a b hab
    apply Subtype.ext
    apply hf
    funext k
    have h1 := hn a k
    have h2 := hn b k
    rw [hab] at h1
    exact mul_left_cancel₀ hNpos.ne' (h1.trans h2.symm)
  have hg := ((summable_prod_inv_one_add_sq d).comp_injective hinj).mul_left (((N : ℝ) ^ 2) ^ d * C)
  have hbound : ∀ a : S, ‖w a.1‖ ≤ ((N : ℝ) ^ 2) ^ d * C *
      ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2)⁻¹ := by
    intro a
    have hle : ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2) ≤
        ((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2) := by
      have : ((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2) =
          ∏ k : Fin d, ((N : ℝ) ^ 2 * (1 + f a.1 k ^ 2)) := by
        rw [Finset.prod_mul_distrib]; simp
      rw [this]
      refine Finset.prod_le_prod₀ (fun k _ => by positivity) (fun k _ => ?_)
      rw [← hn a k]
      have : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hpos : (0 : ℝ) < ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2) :=
      Finset.prod_pos (fun k _ => by positivity)
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hpos]
    calc ‖w a.1‖ * ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2)
        ≤ ‖w a.1‖ * (((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2)) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = ((N : ℝ) ^ 2) ^ d * (‖w a.1‖ * ∏ k, (1 + f a.1 k ^ 2)) := by ring
      _ ≤ ((N : ℝ) ^ 2) ^ d * C := mul_le_mul_of_nonneg_left (hC _) (by positivity)
  have hsub : Summable (w ∘ (Subtype.val : S → ι)) :=
    Summable.of_norm_bounded hg hbound
  refine (Function.Injective.summable_iff Subtype.val_injective ?_).1 hsub
  intro x hx
  by_contra h0
  exact hx ⟨⟨x, h0⟩, rfl⟩

end GlobalTheory.CompanionTheory.LatticeCount
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfLatticeDecayStatement
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_of_lattice_decay_of_injective : ∀ (ι : Type) (d : ℕ) (w : ι → ℂ) (f : ι → Fin d → ℝ), Function.Injective f → ∀ (N : ℕ), 0 < N → ∀ (C : ℝ), (∀ i, ‖w i‖ * ∏ k, (1 + f i k ^ 2) ≤ C) → (∀ i, w i ≠ 0 → ∀ k, ∃ n : ℤ, (N : ℝ) * f i k = n) → Summable w := by
  first | exact @GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay | exact GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay | (intros; apply GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierOneParameterIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierOneParameterIntegral
open MeasureTheory

namespace GlobalTheory.CompanionTheory.OneParamFourier

variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [MeasurableSpace A] [BorelSpace A]

theorem integral_translate_mul_char (lam : Measure A) [lam.IsAddHaarMeasure] (H : A → ℂ)
    (χ : AddChar A ℂ) (a : A) :
    ∫ b, H (b + a) * χ b ∂lam = χ (-a) * ∫ b, H b * χ b ∂lam := by
  have h := integral_add_right_eq_self (μ := lam) (fun b => H b * χ (b + -a)) a
  simp only [add_neg_cancel_right] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only [AddChar.map_add_eq_mul]
  ring

theorem integrable_mul_char {lam : Measure A} {H : A → ℂ} (hH : Integrable H lam)
    {χ : AddChar A ℂ} (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) :
    Integrable (fun b => H b * χ b) lam := by
  refine hH.mono (hH.aestronglyMeasurable.mul hχ.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun b => ?_)
  simp [hn]

theorem integrable_uncurry_translate (lam : Measure A) [lam.IsAddHaarMeasure] [SFinite lam]
    (c : ℝ →+ A) (hc : Continuous c) {G : A → ℂ} (hG : Continuous G) (hGi : Integrable G lam)
    {χ : AddChar A ℂ} (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) (K : ℂ) (s : ℝ) :
    Integrable (Function.uncurry fun (u : ℝ) (b : A) => K * G (b + c u) * χ b)
      ((volume.restrict (Set.uIoc 0 s)).prod lam) := by
  have hcont : Continuous (Function.uncurry fun (u : ℝ) (b : A) => K * G (b + c u) * χ b) := by
    unfold Function.uncurry
    fun_prop
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) s)) := by
    unfold Set.uIoc
    infer_instance
  refine (integrable_prod_iff hcont.aestronglyMeasurable).2 ⟨ae_of_all _ fun u => ?_, ?_⟩
  · have h1 : Integrable (fun b => G (b + c u)) lam := hGi.comp_add_right (c u)
    have h2 := integrable_mul_char (h1.const_mul K) hχ hn
    simpa [Function.uncurry, mul_assoc] using h2
  · have hconst : ∀ u : ℝ, ∫ b, ‖Function.uncurry (fun (u : ℝ) (b : A) => K * G (b + c u) * χ b) (u, b)‖ ∂lam
        = ‖K‖ * ∫ b, ‖G b‖ ∂lam := by
      intro u
      have h := integral_add_right_eq_self (μ := lam) (fun b => ‖G b‖) (c u)
      rw [← h, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp [Function.uncurry, hn]
    simp_rw [hconst]
    exact integrable_const _

theorem integral_mul_char_eq_of_hasDerivAt (A : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] (lam : Measure A)
    [lam.IsAddHaarMeasure] [SFinite lam] (c : ℝ →+ A) (hc : Continuous c) (F G : A → ℂ)
    (hF : Continuous F) (hG : Continuous G) (hFi : Integrable F lam) (hGi : Integrable G lam)
    (χ : AddChar A ℂ) (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) (f : ℝ)
    (hf : ∀ s : ℝ, χ (c s) = Complex.exp (-(2 * Real.pi * Complex.I * ((s * f : ℝ) : ℂ))))
    (hd : ∀ (b : A) (s : ℝ),
      HasDerivAt (fun t : ℝ => F (b + c t)) (2 * Real.pi * Complex.I * G (b + c s)) s) :
    ∫ b, G b * χ b ∂lam = (f : ℂ) * ∫ b, F b * χ b ∂lam := by
  set K : ℂ := 2 * Real.pi * Complex.I with hK
  have hK0 : K ≠ 0 := by
    simp [hK, Real.pi_ne_zero, Complex.I_ne_zero]
  set e : ℝ → ℂ := fun u => Complex.exp (K * ((u * f : ℝ) : ℂ)) with he
  have hχe : ∀ s : ℝ, χ (-(c s)) = e s := by
    intro s
    rw [← map_neg, hf, he]
    simp only
    congr 1
    push_cast
    ring
  set Fh : ℂ := ∫ b, F b * χ b ∂lam with hFh
  set Gh : ℂ := ∫ b, G b * χ b ∂lam with hGh
  have hec : Continuous e := by
    rw [he]
    fun_prop
  have key : ∀ s : ℝ, (e s - 1) * Fh = K * Gh * ∫ u in (0 : ℝ)..s, e u := by
    intro s
    have hftc : ∀ b : A, F (b + c s) - F b = ∫ u in (0 : ℝ)..s, K * G (b + c u) := by
      intro b
      have hcu : Continuous fun u : ℝ => K * G (b + c u) := by fun_prop
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := s)
        (f := fun t : ℝ => F (b + c t)) (f' := fun u => K * G (b + c u))
        (fun x _ => hd b x) (hcu.intervalIntegrable _ _)
      simpa using this.symm
    have hswap := intervalIntegral_integral_swap
      (integrable_uncurry_translate lam c hc hG hGi hχ hn K s)
    have h1 : ∫ b, F (b + c s) * χ b ∂lam = e s * Fh := by
      rw [integral_translate_mul_char, hχe]
    have hi1 : Integrable (fun b => F (b + c s) * χ b) lam :=
      integrable_mul_char (hFi.comp_add_right (c s)) hχ hn
    have hi2 : Integrable (fun b => F b * χ b) lam := integrable_mul_char hFi hχ hn
    have h2 : (e s - 1) * Fh = ∫ b, (∫ u in (0 : ℝ)..s, K * G (b + c u) * χ b) ∂lam := by
      have : (e s - 1) * Fh = ∫ b, (F (b + c s) * χ b - F b * χ b) ∂lam := by
        rw [integral_sub hi1 hi2, h1]
        ring
      rw [this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      rw [intervalIntegral.integral_mul_const, ← hftc b]
      ring
    rw [h2, ← hswap, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    beta_reduce
    have h3 : ∫ b, K * G (b + c u) * χ b ∂lam = K * ∫ b, G (b + c u) * χ b ∂lam := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      ring
    rw [h3, integral_translate_mul_char, hχe]
    ring
  have hL : HasDerivAt (fun s : ℝ => (e s - 1) * Fh) (K * f * Fh) 0 := by
    have h0 : HasDerivAt (fun u : ℝ => K * ((u * f : ℝ) : ℂ)) (K * f) 0 := by
      have : HasDerivAt (fun u : ℝ => ((u : ℂ))) 1 0 := Complex.ofRealCLM.hasDerivAt
      simpa [mul_assoc] using (this.mul_const (f : ℂ)).const_mul K
    have := ((h0.cexp).sub_const 1).mul_const Fh
    simpa [he] using this
  have hR : HasDerivAt (fun s : ℝ => K * Gh * ∫ u in (0 : ℝ)..s, e u) (K * Gh) 0 := by
    have := (hec.integral_hasStrictDerivAt 0 0).hasDerivAt.const_mul (K * Gh)
    simpa [he] using this
  have hEq : (fun s : ℝ => (e s - 1) * Fh) = fun s : ℝ => K * Gh * ∫ u in (0 : ℝ)..s, e u :=
    funext key
  rw [hEq] at hL
  have := hL.unique hR
  have h4 : K * (f * Fh) = K * Gh := by
    rw [← mul_assoc]
    exact this
  exact (mul_left_cancel₀ hK0 h4).symm

end GlobalTheory.CompanionTheory.OneParamFourier
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierOneParameterIntegralStatement
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_one_parameter_integral : ∀ (A : Type) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] (lam : Measure A) [lam.IsAddHaarMeasure] [SFinite lam] (c : ℝ →+ A), Continuous c → ∀ (F G : A → ℂ), Continuous F → Continuous G → Integrable F lam → Integrable G lam → ∀ (χ : AddChar A ℂ), Continuous χ → (∀ x, ‖χ x‖ = 1) → ∀ (f : ℝ), (∀ s : ℝ, χ (c s) = Complex.exp (-(2 * Real.pi * Complex.I * ((s * f : ℝ) : ℂ)))) → (∀ (b : A) (s : ℝ), HasDerivAt (fun t : ℝ => F (b + c t)) (2 * Real.pi * Complex.I * G (b + c s)) s) → ∫ b, G b * χ b ∂lam = (f : ℂ) * ∫ b, F b * χ b ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.OneParamFourier.integral_mul_char_eq_of_hasDerivAt | exact GlobalTheory.CompanionTheory.OneParamFourier.integral_mul_char_eq_of_hasDerivAt | (intros; apply GlobalTheory.CompanionTheory.OneParamFourier.integral_mul_char_eq_of_hasDerivAt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierParameterDerivative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierParameterDerivative
open MeasureTheory

namespace GlobalTheory.CompanionTheory.Analysis.OscPhase

private lemma norm_exp_two_pi_I_mul_real (r : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem hasDerivAt_integral_oscillating_phase
    (X : Type) [MeasurableSpace X] (μ : Measure X) (g : X → ℂ) (M : X → ℝ)
    (hM : Measurable M) (hg : Integrable g μ)
    (hMg : Integrable (fun y => (M y : ℂ) * g y) μ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ y, g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) ∂μ)
      (2 * Real.pi * Complex.I * ∫ y, (M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((s * M y : ℝ) : ℂ)) ∂μ) s := by
  have hnorm : ∀ r : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := norm_exp_two_pi_I_mul_real
  have hmeasE : ∀ t : ℝ,
      Measurable fun y => Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) :=
    fun t => by fun_prop
  have hdiff : ∀ (y : X) (t : ℝ), HasDerivAt
      (fun t : ℝ => g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)))
      (2 * Real.pi * Complex.I *
        ((M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)))) t := by
    intro y t
    have h1 : HasDerivAt (fun t : ℝ => ((t * M y : ℝ) : ℂ)) ((M y : ℝ) : ℂ) t := by
      simpa using ((hasDerivAt_id t).mul_const (M y)).ofReal_comp
    have h2 := ((h1.const_mul (2 * Real.pi * Complex.I)).cexp).const_mul (g y)
    exact h2.congr_deriv (by ring)
  obtain ⟨-, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s)
    (F := fun (t : ℝ) y => g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)))
    (F' := fun (t : ℝ) y => 2 * Real.pi * Complex.I *
      ((M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ))))
    (bound := fun y => ‖2 * Real.pi * Complex.I‖ * ‖(M y : ℂ) * g y‖) Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      hg.aestronglyMeasurable.mul (hmeasE t).aestronglyMeasurable)
    (hg.mono (hg.aestronglyMeasurable.mul (hmeasE s).aestronglyMeasurable)
      (ae_of_all _ fun y => by rw [norm_mul, hnorm, mul_one]))
    ((hMg.aestronglyMeasurable.mul (hmeasE s).aestronglyMeasurable).const_mul _)
    (ae_of_all _ fun y t _ => by simp only [norm_mul, hnorm, mul_one, le_refl])
    (hMg.norm.const_mul _)
    (ae_of_all _ fun y t _ => hdiff y t)
  rwa [integral_const_mul] at hd

end GlobalTheory.CompanionTheory.Analysis.OscPhase
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierParameterDerivativeStatement
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_parameter_derivative : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (g : X → ℂ) (M : X → ℝ), Measurable M → Integrable g μ → Integrable (fun y => (M y : ℂ) * g y) μ → ∀ s : ℝ, HasDerivAt (fun t : ℝ => ∫ y, g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) ∂μ) (2 * Real.pi * Complex.I * ∫ y, (M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((s * M y : ℝ) : ℂ)) ∂μ) s := by
  first | exact @GlobalTheory.CompanionTheory.Analysis.OscPhase.hasDerivAt_integral_oscillating_phase | exact GlobalTheory.CompanionTheory.Analysis.OscPhase.hasDerivAt_integral_oscillating_phase | (intros; apply GlobalTheory.CompanionTheory.Analysis.OscPhase.hasDerivAt_integral_oscillating_phase <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinCoefficientsSummable
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WSum

variable {D : D7} {r : ℕ}

theorem halfTr_add (x y : AE D) : halfTr (x + y) = halfTr x + halfTr y := by
  simp only [halfTr, trA, map_add (f := _), mul_add]

theorem halfTr_zero : halfTr (0 : AE D) = 0 := by
  simp only [halfTr, trA, map_zero, mul_zero]

theorem continuous_halfTr : Continuous (halfTr : AE D → AF D.host.F) :=
  continuous_const.mul (IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D)))

def chi (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D r) : AddChar (hermA D r) ℂ where
  toFun b := ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r)))
  map_zero_eq_one' := by
    show ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) (0 : Mx D r r) : Mx D r r))) = 1
    rw [Matrix.mul_zero, Matrix.trace_zero, halfTr_zero, neg_zero]
    exact ψ.map_zero_eq_one
  map_add_eq_mul' x y := by
    show ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) (x.1 + y.1) : Mx D r r))) = _
    rw [Matrix.mul_add, Matrix.trace_add, halfTr_add, neg_add, AddChar.map_add_eq_mul]

theorem chi_apply (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D r) (b : hermA D r) :
    chi ψ β b = ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r))) := rfl

theorem W_eq_chi (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r))
    (φ : Mx D V.rank r → ℂ) (β : HermE D r) :
    W ψ V μ lam φ β = ∫ b, Jt ψ V μ φ b * chi ψ β b ∂lam := rfl

theorem norm_chi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D r) (b : hermA D r) :
    ‖chi ψ β b‖ = 1 := hψ.2.1 _

theorem continuous_chi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D r) :
    Continuous (chi ψ β) := by
  have h0 : Continuous fun b : hermA D r => Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r) :=
    (continuous_const.matrix_mul continuous_subtype_val).matrix_trace
  exact hψ.1.comp (continuous_halfTr.comp h0).neg

theorem norm_W_le {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) (μ : Measure (Mx D V.rank r))
    (lam : Measure (hermA D r)) (φ : Mx D V.rank r → ℂ) (β : HermE D r) :
    ‖W ψ V μ lam φ β‖ ≤ ∫ b, ‖Jt ψ V μ φ b‖ ∂lam := by
  rw [W_eq_chi]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only [norm_mul, norm_chi hψ, mul_one]

def tq (V : HSp D) (b : Mx D r r) (y : Mx D V.rank r) : AE D :=
  Matrix.trace (HMul.hMul b (inner V y y) : Mx D r r)

theorem tq_add (V : HSp D) (b c : Mx D r r) (y : Mx D V.rank r) : tq V (b + c) y = tq V b y + tq V c y := by
  unfold tq
  rw [Matrix.add_mul, Matrix.trace_add]

theorem continuous_tq (V : HSp D) (b : Mx D r r) : Continuous (tq V b) := by
  have h : Continuous fun y : Mx D V.rank r => (inner V y y : Mx D r r) := by
    unfold GlobalTheory.StdUnn.inner
    exact continuous_adj.matrix_mul (continuous_const.matrix_mul continuous_id)
  exact (continuous_const.matrix_mul h).matrix_trace

theorem Jt_add (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (μ : Measure (Mx D V.rank r)) (φ : Mx D V.rank r → ℂ)
    (b c : hermA D r) :
    Jt ψ V μ φ (b + c) = ∫ y, φ y * ψ (halfTr (tq V b.1 y)) * ψ (halfTr (tq V c.1 y)) ∂μ := by
  unfold Jt
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show φ y * ψ (halfTr (tq V (b.1 + c.1) y)) = _
  rw [tq_add, halfTr_add, AddChar.map_add_eq_mul]
  exact (mul_assoc _ _ _).symm

theorem hasDeriv_Jt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D)
    (μ : Measure (Mx D V.rank r)) {φ : Mx D V.rank r → ℂ} (hφ : Integrable φ μ) {M : Mx D V.rank r → ℝ}
    (hM : Measurable M) (hMφ : Integrable (fun y => (M y : ℂ) * φ y) μ) (c : ℝ →+ hermA D r)
    (hc : ∀ (s : ℝ) y, ψ (halfTr (tq V (c s).1 y)) = Complex.exp (2 * Real.pi * Complex.I * ((s * M y : ℝ) : ℂ)))
    (b : hermA D r) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Jt ψ V μ φ (b + c t))
      (2 * Real.pi * Complex.I * Jt ψ V μ (fun y => (M y : ℂ) * φ y) (b + c s)) s := by
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  have hu : Continuous fun y => ψ (halfTr (tq V b.1 y)) :=
    hψ.1.comp (continuous_halfTr.comp (continuous_tq V b.1))
  have hn : ∀ y, ‖ψ (halfTr (tq V b.1 y))‖ = 1 := fun y => hψ.2.1 _
  have hg : Integrable (fun y => φ y * ψ (halfTr (tq V b.1 y))) μ :=
    hφ.norm.mono' (hφ.aestronglyMeasurable.mul hu.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => by simp only [norm_mul, hn, mul_one, le_refl])
  have hMg : Integrable (fun y => (M y : ℂ) * (φ y * ψ (halfTr (tq V b.1 y)))) μ := by
    refine hMφ.norm.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (hMφ.aestronglyMeasurable.mul hu.aestronglyMeasurable).congr
        (Filter.Eventually.of_forall fun y => mul_assoc _ _ _)
    · simp only [norm_mul, hn, mul_one, le_refl]
  have h := GlobalTheory.T.fourier_parameter_derivative _ μ (fun y => φ y * ψ (halfTr (tq V b.1 y))) M hM hg hMg s
  have e1 : (fun t : ℝ => Jt ψ V μ φ (b + c t)) = fun t : ℝ => ∫ y, φ y * ψ (halfTr (tq V b.1 y)) *
      Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) ∂μ := by
    funext t
    rw [Jt_add]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only [hc])
  have e2 : Jt ψ V μ (fun y => (M y : ℂ) * φ y) (b + c s) = ∫ y, (M y : ℂ) * (φ y * ψ (halfTr (tq V b.1 y))) *
      Complex.exp (2 * Real.pi * Complex.I * ((s * M y : ℝ) : ℂ)) ∂μ := by
    rw [Jt_add]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only [hc, mul_assoc])
  rw [e1, e2]
  exact h

theorem decay_abs {Φ ι : Type} {d : ℕ} (S : Set Φ) (w : Φ → ι → ℂ) (T : Fin d → Φ → Φ) (f : Fin d → ι → ℝ)
    (hb : ∀ φ ∈ S, ∃ C, ∀ i, ‖w φ i‖ ≤ C) (hS : ∀ k, ∀ φ ∈ S, T k φ ∈ S)
    (hR : ∀ k, ∀ φ ∈ S, ∀ i, w (T k φ) i = (f k i : ℂ) * w φ i) (s : Finset (Fin d)) :
    ∀ φ ∈ S, ∃ C, ∀ i, ‖w φ i‖ * ∏ k ∈ s, (1 + f k i ^ 2) ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro φ hφ
    obtain ⟨C, hC⟩ := hb φ hφ
    exact ⟨C, fun i => by simpa using hC i⟩
  | insert k s hk ih =>
    intro φ hφ
    obtain ⟨C₁, h₁⟩ := ih φ hφ
    obtain ⟨C₂, h₂⟩ := ih _ (hS k _ (hS k φ hφ))
    refine ⟨C₁ + C₂, fun i => ?_⟩
    have e : ‖w (T k (T k φ)) i‖ = f k i ^ 2 * ‖w φ i‖ := by
      rw [hR k _ (hS k φ hφ), hR k φ hφ, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc,
        abs_mul_abs_self, sq]
    have h2 := h₂ i
    rw [e] at h2
    rw [Finset.prod_insert hk]
    nlinarith [h₁ i, h2]

theorem tq_path {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (V : HSp D)
    (a : HermE D r) (s : ℝ) (y : Mx D V.rank r) :
    tq V (path hσ a s).1 y = rs σ s * tq V (a.1.map (incA D)) y := by
  show Matrix.trace (HMul.hMul (rs σ s • a.1.map (incA D)) (inner V y y) : Mx D r r) = _
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rfl

theorem continuous_path {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    (a : HermE D r) : Continuous (path hσ a) := by
  refine Continuous.subtype_mk (f := fun s : ℝ => rs σ s • a.1.map (incA D)) ?_ _
  exact continuous_pi fun i => continuous_pi fun j => (continuous_rs hσ).mul continuous_const

theorem trace_rat (β a : HermE D r) :
    Matrix.trace (HMul.hMul (β.1.map (incA D)) (a.1.map (incA D)) : Mx D r r) = incA D (Matrix.trace (β.1 * a.1)) := by
  have h : (HMul.hMul (β.1.map (incA D)) (a.1.map (incA D)) : Mx D r r) = (β.1 * a.1).map (incA D) := by
    rw [Matrix.map_mul]
  rw [h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem chi_path {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) {α : D.host.F}
    (hph : ∀ (t : AE D) (s : ℝ), ψ (halfTr (rs σ s * t)) =
      Complex.exp (2 * Real.pi * Complex.I * ((s * lam θ α t : ℝ) : ℂ)))
    (a β : HermE D r) (s : ℝ) :
    chi ψ β (path hσ a s) = Complex.exp (-(2 * Real.pi * Complex.I * ((s * pairF θ α a β : ℝ) : ℂ))) := by
  rw [chi_apply]
  have e : (Matrix.trace (HMul.hMul (β.1.map (incA D)) (path hσ a s).1 : Mx D r r)) =
      rs σ s * incA D (Matrix.trace (β.1 * a.1)) := by
    show Matrix.trace (HMul.hMul (β.1.map (incA D)) (rs σ s • a.1.map (incA D)) : Mx D r r) = _
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_rat]
  rw [e, AddChar.map_neg_eq_inv, hph, Complex.exp_neg]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem W_mult {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {θ : InfFam D} (hθ : IsInfFam θ)
    {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {α : D.host.F}
    (hph : ∀ (t : AE D) (s : ℝ), ψ (halfTr (rs σ s * t)) =
      Complex.exp (2 * Real.pi * Complex.I * ((s * lam θ α t : ℝ) : ℂ)))
    {V : HSp D} (hm : 2 * r < V.rank) {μ : Measure (Mx D V.rank r)} (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕)
    {lam' : Measure (hermA D r)} {𝓖 : Set (hermA D r)} (hlam : IsCovolOneH lam' 𝓖) (a : HermE D r)
    (hmem : ∀ φ ∈ schwartzA θ V.rank r, (fun y => (multM θ α V a y : ℂ) * φ y) ∈ schwartzA θ V.rank r)
    (hMc : Continuous (multM θ α V a))
    {φ : Mx D V.rank r → ℂ} (hφ : φ ∈ schwartzA θ V.rank r) (β : HermE D r) :
    W ψ V μ lam' (fun y => (multM θ α V a y : ℂ) * φ y) β = (pairF θ α a β : ℂ) * W ψ V μ lam' φ β := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : LocallyCompactSpace (Mx D r r) := i2
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : T2Space (Mx D r r) := i4
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : lam'.IsAddHaarMeasure := hlam.1
  haveI : LocallyCompactSpace (hermA D r) := (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := r)).locallyCompactSpace
  haveI : SFinite lam' := by
    haveI : SigmaFinite lam' := MeasureTheory.sigmaFinite_of_locallyFinite
    infer_instance
  obtain ⟨𝓕, hF⟩ := hμ
  haveI : μ.IsAddHaarMeasure := hF.1
  have hμ' : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕 := ⟨𝓕, hF⟩
  have hMφ := hmem φ hφ
  have cont : ∀ φ ∈ schwartzA θ V.rank r, Continuous (Jt ψ V μ φ) :=
    fun φ h => GlobalTheory.T.theta_integral_continuous D r V ψ θ μ φ hψ hθ hμ' h
  have intg : ∀ φ ∈ schwartzA θ V.rank r, Integrable (Jt ψ V μ φ) lam' := fun φ h =>
    (GlobalTheory.T.poisson_summation_hermitian_lattice D r ψ hψ lam' 𝓖 hlam _ (cont φ h) (GlobalTheory.T.theta_integral_locally_summable_bound D r V ψ θ μ φ hm hψ hθ hμ' h)).1
  have hc : ∀ (s : ℝ) y, ψ (halfTr (tq V (path hσ a s).1 y)) =
      Complex.exp (2 * Real.pi * Complex.I * ((s * multM θ α V a y : ℝ) : ℂ)) := fun s y => by
    rw [tq_path]
    exact hph _ s
  exact GlobalTheory.T.fourier_one_parameter_integral (hermA D r) lam' (path hσ a) (continuous_path hσ a) _ _ (cont φ hφ) (cont _ hMφ)
    (intg φ hφ) (intg _ hMφ) (chi ψ β) (continuous_chi hψ β) (norm_chi hψ β) (pairF θ α a β)
    (chi_path hσ hph a β)
    (hasDeriv_Jt hψ V μ (GlobalTheory.T.integrable_of_mem_schwartzA D θ hθ _ _ μ φ hφ) hMc.measurable
      (GlobalTheory.T.integrable_of_mem_schwartzA D θ hθ _ _ μ _ hMφ) (path hσ a) hc)

set_option synthInstance.maxHeartbeats 400000 in
theorem W_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {θ : InfFam D}
    {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {α : D.host.F}
    (hph : ∀ (t : AE D) (s : ℝ), ψ (halfTr (rs σ s * t)) =
      Complex.exp (2 * Real.pi * Complex.I * ((s * lam θ α t : ℝ) : ℂ)))
    {V : HSp D} {μ : Measure (Mx D V.rank r)} {lam' : Measure (hermA D r)} [lam'.IsAddHaarMeasure]
    (a : HermE D r) {φ : Mx D V.rank r → ℂ} (N : ℕ)
    (hN : ∀ y, φ y ≠ 0 → ψ (halfTr (Matrix.trace (HMul.hMul
      (N • ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1)).1 (inner V y y) : Mx D r r))) = 1)
    (β : HermE D r) (hW : W ψ V μ lam' φ β ≠ 0) : ∃ n : ℤ, (N : ℝ) * pairF θ α a β = n := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : SecondCountableTopology (Mx D r r) := i3
  set v : hermA D r := N • ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1) with hv
  have hper : ∀ b, Jt ψ V μ φ (b + v) = Jt ψ V μ φ b := fun b => by
    rw [Jt_add]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases h : φ y = 0
    · show φ y * _ * _ = φ y * _
      rw [h]
      simp
    · have h1 : ψ (halfTr (tq V v.1 y)) = 1 := hN y h
      show _ = φ y * ψ (halfTr (tq V b.1 y))
      simp only [h1, mul_one]
  have h1 : W ψ V μ lam' φ β = chi ψ β v * W ψ V μ lam' φ β := by
    rw [W_eq_chi, ← integral_const_mul]
    rw [← integral_add_right_eq_self (fun b => Jt ψ V μ φ b * chi ψ β b) v]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    show Jt ψ V μ φ (b + v) * chi ψ β (b + v) = chi ψ β v * (Jt ψ V μ φ b * chi ψ β b)
    rw [hper, AddChar.map_add_eq_mul]
    ring
  have h2 : chi ψ β v = 1 := by
    have : (chi ψ β v - 1) * W ψ V μ lam' φ β = 0 := by
      rw [sub_mul, ← h1, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hW)
  have h3 : chi ψ β (GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 = 1 := by
    rw [chi_apply]
    show ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) (a.1.map (incA D)) : Mx D r r))) = 1
    rw [trace_rat, GlobalTheory.CompanionTheory.ThetaInv.halfTr_incA, ← map_neg]
    exact hψ.2.2.1 _
  have h4 : chi ψ β v = Complex.exp (((N : ℂ)) * (2 * Real.pi * Complex.I * (pairF θ α a β : ℂ))) := by
    rw [hv, AddChar.map_nsmul_eq_pow, AddChar.map_sub_eq_div, h3, chi_path hσ hph, Complex.exp_nat_mul]
    congr 1
    rw [one_div, ← Complex.exp_neg, neg_neg]
    congr 1
    push_cast
    ring
  rw [h4, Complex.exp_eq_one_iff] at h2
  obtain ⟨n, hn⟩ := h2
  refine ⟨n, ?_⟩
  have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h5 : ((N : ℝ) * pairF θ α a β : ℝ) = n := by
    have : (((N : ℝ) * pairF θ α a β : ℝ) : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ hI
      push_cast
      linear_combination hn
    exact_mod_cast this
  exact h5

end GlobalTheory.CompanionTheory.WSum

theorem GlobalTheory.CompanionTheory.WSum.summable_W_of_two_mul_lt_rank : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)) (φ : Mx D V.rank r → ℂ),
    2 * r < V.rank → IsCharAF D.host.F ψ → IsInfFam θ → (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) →
    IsCovolOneH lam 𝓖 → φ ∈ schwartzA θ V.rank r → Summable (fun β : HermE D r => W ψ V μ lam φ β) := by
  intro D r V ψ θ μ lam 𝓖 φ hm hψ hθ hμ hlam hφ
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨ψ₀, h₀, α, hα0, hα⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hph := GlobalTheory.T.character_along_one_parameter_path D ψ ψ₀ h₀ α hα θ σ hσ
  obtain ⟨d, a, hinj⟩ := GlobalTheory.T.injective_pairing_finite_family D r θ hθ α hα0
  have hq := fun k => GlobalTheory.T.archimedean_multiplier_temperate D r θ hθ α V (a k)
  choose q hqt hqe using hq
  have hcomp : Continuous fun y : Mx D V.rank r => (fun τ i j => compAt θ τ y i j :
      D.what₂.Tau → Fin V.rank → Fin r → ℂ) :=
    continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).matrix_elem i j
  have hMc : ∀ k, Continuous (GlobalTheory.CompanionTheory.WSum.multM θ α V (a k)) := fun k => by
    have h1 : Continuous fun y => ((GlobalTheory.CompanionTheory.WSum.multM θ α V (a k) y : ℝ) : ℂ) := by
      simp only [hqe k]
      exact (hqt k).1.continuous.comp hcomp
    exact Complex.continuous_re.comp h1
  have hmem : ∀ k, ∀ φ ∈ schwartzA θ V.rank r,
      (fun y => (GlobalTheory.CompanionTheory.WSum.multM θ α V (a k) y : ℂ) * φ y) ∈ schwartzA θ V.rank r := fun k φ h => by
    simp only [hqe k]
    exact GlobalTheory.T.temperate_multiplier_preserves_schwartz D θ _ _ (q k) (hqt k) φ h
  have hdec := GlobalTheory.CompanionTheory.WSum.decay_abs (schwartzA θ V.rank r : Set (Mx D V.rank r → ℂ))
    (fun φ β => W ψ V μ lam φ β) (fun k φ y => (GlobalTheory.CompanionTheory.WSum.multM θ α V (a k) y : ℂ) * φ y)
    (fun k β => GlobalTheory.CompanionTheory.WSum.pairF θ α (a k) β)
    (fun φ _ => ⟨_, fun β => GlobalTheory.CompanionTheory.WSum.norm_W_le hψ V μ lam φ β⟩) hmem
    (fun k φ h β => GlobalTheory.CompanionTheory.WSum.W_mult hψ hθ hσ hph hm hμ hlam (a k) (hmem k) (hMc k) h β) Finset.univ φ hφ
  obtain ⟨C, hC⟩ := hdec
  have hlev := fun k => GlobalTheory.T.integral_multiple_path_trivial_character D r V ψ hψ θ σ hσ (a k) φ hφ
  choose Nk hNk hNy using hlev
  refine GlobalTheory.T.summable_of_lattice_decay_of_injective (HermE D r) d _ (fun β k => GlobalTheory.CompanionTheory.WSum.pairF θ α (a k) β) hinj (∏ k, Nk k)
    (Finset.prod_pos fun k _ => hNk k) C hC fun β hW k => ?_
  obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.WSum.W_int hψ hσ hph (a k) (Nk k) (hNy k) β hW
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem Nk (Finset.mem_univ k)
  refine ⟨c * n, ?_⟩
  rw [hc]
  push_cast
  rw [mul_comm ((Nk k : ℝ)) (c : ℝ), mul_assoc, hn]
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinCoefficientsSummableStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_eisenstein_coefficients_summable : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)) (φ : Mx D V.rank r → ℂ), 2 * r < V.rank → IsCharAF D.host.F ψ → IsInfFam θ → (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → IsCovolOneH lam 𝓖 → φ ∈ schwartzA θ V.rank r → Summable (fun β : HermE D r => W ψ V μ lam φ β) := by
  first | exact @GlobalTheory.CompanionTheory.WSum.summable_W_of_two_mul_lt_rank | exact GlobalTheory.CompanionTheory.WSum.summable_W_of_two_mul_lt_rank | (intros; apply GlobalTheory.CompanionTheory.WSum.summable_W_of_two_mul_lt_rank <;> assumption)
end
end

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermPoisson

theorem poissonHerm_main : PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm := by
  intro D r V ψ θ μ lam ν φ hH hJ
  obtain ⟨hm, hψ, hθ, hμ, ⟨𝓖, hlam⟩, -, hφ, -⟩ := hH
  have hc := GlobalTheory.T.theta_integral_continuous D r V ψ θ μ φ hψ hθ hμ hφ
  have hu := GlobalTheory.T.theta_integral_locally_summable_bound D r V ψ θ μ φ hm hψ hθ hμ hφ
  have hW := GlobalTheory.T.siegel_eisenstein_coefficients_summable D r V ψ θ μ lam 𝓖 φ hm hψ hθ hμ hlam hφ
  obtain ⟨-, hP⟩ := GlobalTheory.T.poisson_summation_hermitian_lattice D r ψ hψ lam 𝓖 hlam _ hc hu
  have hgW : ∀ β : HermE D r, (fun t : ratHerm D r => ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) ((hermEquiv (D := D) (r := r)) β) = W ψ V μ lam φ β :=
    fun β => (W_eq ψ V μ lam φ β).symm
  have hS : Summable (fun t : ratHerm D r => ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) := by
    refine (hermEquiv (D := D) (r := r)).summable_iff.1 ?_
    exact hW.congr fun β => (hgW β).symm
  have e := hP hS
  have hsumJ : ∑' b : HermE D r, J ψ V μ φ b = ∑' c : ratHerm D r, Jt ψ V μ φ c.1 :=
    (hermEquiv (D := D) (r := r)).tsum_eq (fun c => Jt ψ V μ φ c.1)
  have hsumW : ∑' β : HermE D r, W ψ V μ lam φ β = ∑' t : ratHerm D r, ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam := by
    rw [← (hermEquiv (D := D) (r := r)).tsum_eq]
    exact tsum_congr fun β => (hgW β).symm
  rw [hsumJ, e, ← hsumW]
  exact hW.hasSum

end GlobalTheory.CompanionTheory.HermPoisson
