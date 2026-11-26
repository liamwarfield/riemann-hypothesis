module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjIntertwinerPointValueSobolevContinuous
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualDirectionDerivativeMixedCoordinateBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.GaussSchwartz

open scoped Nat

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_id_le_one_add (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (id : E → E) x‖ ≤ 1 + ‖x‖ := by
  rcases j with _ | n
  · rw [norm_iteratedFDeriv_zero]; simp
  · rw [← norm_iteratedFDeriv_fderiv,
      show fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E from funext fun _ => fderiv_id]
    rcases n with _ | n
    · rw [norm_iteratedFDeriv_zero]
      exact (ContinuousLinearMap.norm_id_le).trans (by linarith [norm_nonneg x])
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
      simp only [Pi.zero_apply, norm_zero]
      positivity

theorem norm_iteratedFDeriv_diag_le (B : E →L[ℝ] E →L[ℝ] ℝ) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => B y y) x‖ ≤ ‖B‖ * (2 ^ n * (1 + ‖x‖) ^ 2) := by
  have h := B.norm_iteratedFDeriv_le_of_bilinear (f := id) (g := id) (N := (n : WithTop ℕ∞))
    contDiff_id contDiff_id x le_rfl
  simp only [id] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => y) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : E => y) x‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + ‖x‖) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [mul_assoc, sq]
        gcongr
        · exact norm_iteratedFDeriv_id_le_one_add i x
        · exact norm_iteratedFDeriv_id_le_one_add (n - i) x
    _ = 2 ^ n * (1 + ‖x‖) ^ 2 := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n

theorem norm_iteratedFDeriv_rexp (i : ℕ) (y : ℝ) : ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_exp_const_mul i 1) y
  simp only [one_mul, one_pow] at h
  rw [show (fun s => Real.exp s) = Real.exp from rfl] at h
  rw [h, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]

theorem exists_bound_poly_mul_exp (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ C, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ N * Real.exp (-(c * r ^ 2)) ≤ C := by
  first
  | exact @_root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded
  | exact _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded
  | (apply _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded ..)

theorem exists_coercive [FiniteDimensional ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ x, x ≠ 0 → B x x < 0) :
    ∃ c > 0, ∀ x, B x x ≤ -(c * ‖x‖ ^ 2) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨1, one_pos, fun x => ?_⟩
    rw [Subsingleton.elim x 0]; simp
  · have hcont : Continuous fun y : E => B y y := (B.continuous.clm_apply continuous_id)
    obtain ⟨x0, hx0, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn
      (NormedSpace.sphere_nonempty.2 zero_le_one) hcont.continuousOn
    have hx0n : ‖x0‖ = 1 := by simpa using hx0
    have hx0ne : x0 ≠ 0 := by intro h; rw [h, norm_zero] at hx0n; exact zero_ne_one hx0n
    refine ⟨-(B x0 x0), by linarith [hB x0 hx0ne], fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    · have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
      set u : E := ‖x‖⁻¹ • x with hu
      have hun : u ∈ Metric.sphere (0 : E) 1 := by
        rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
      have hxu : x = ‖x‖ • u := by rw [hu, smul_smul, mul_inv_cancel₀ hxn.ne', one_smul]
      have h1 : B u u ≤ B x0 x0 := hmax hun
      have h2 : B x x = ‖x‖ ^ 2 * B u u := by
        conv_lhs => rw [hxu]
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
      rw [h2]
      nlinarith [sq_nonneg ‖x‖]

theorem exists_schwartz_exp_diag [FiniteDimensional ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ x, x ≠ 0 → B x x < 0) :
    ∃ f : SchwartzMap E ℂ, ∀ x, f x = ((Real.exp (B x x) : ℝ) : ℂ) := by
  obtain ⟨c, hc, hBc⟩ := exists_coercive B hB
  have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => B y y) := B.contDiff.clm_apply contDiff_id
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Real.exp ∘ fun y : E => B y y) := Real.contDiff_exp.comp hq
  refine ⟨⟨Complex.ofRealLI ∘ (Real.exp ∘ fun y : E => B y y),
    Complex.ofRealLI.toContinuousLinearMap.contDiff.comp hg, ?_⟩, fun x => rfl⟩
  intro k n
  obtain ⟨C, hC⟩ := exists_bound_poly_mul_exp c hc (k + 2 * n)
  refine ⟨n ! * (2 * (‖B‖ + 1)) ^ n * C, fun x => ?_⟩
  have hn : ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  rw [LinearIsometry.norm_iteratedFDeriv_comp_left _ hg.contDiffAt hn]
  have hfb := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := fun y : E => B y y)
    Real.contDiff_exp hq hn x (C := Real.exp (B x x)) (D := 2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2)
    (fun i _ => (norm_iteratedFDeriv_rexp i _).le) (fun i hi _ => by
      have hB0 := norm_nonneg B
      have hx0 := norm_nonneg x
      have a1 : ‖B‖ ≤ (‖B‖ + 1) ^ i :=
        le_trans (by linarith) (le_self_pow₀ (by linarith) (by omega))
      have a2 : (1 + ‖x‖) ^ 2 ≤ ((1 + ‖x‖) ^ 2) ^ i :=
        le_self_pow₀ (by nlinarith) (by omega)
      calc ‖iteratedFDeriv ℝ i (fun y : E => B y y) x‖ ≤ ‖B‖ * (2 ^ i * (1 + ‖x‖) ^ 2) :=
            norm_iteratedFDeriv_diag_le B i x
        _ = 2 ^ i * ‖B‖ * (1 + ‖x‖) ^ 2 := by ring
        _ ≤ 2 ^ i * (‖B‖ + 1) ^ i * ((1 + ‖x‖) ^ 2) ^ i := by gcongr
        _ = (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ i := by rw [mul_pow, mul_pow])
  have hx0 := norm_nonneg x
  have hB0 := norm_nonneg B
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Real.exp ∘ fun y : E => B y y) x‖
      ≤ (1 + ‖x‖) ^ k * (n ! * Real.exp (-(c * ‖x‖ ^ 2)) * (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n) := by
        gcongr
        · linarith
        · exact hfb.trans (by gcongr; exact hBc x)
    _ = n ! * (2 * (‖B‖ + 1)) ^ n * ((1 + ‖x‖) ^ (k + 2 * n) * Real.exp (-(c * ‖x‖ ^ 2))) := by
        rw [show (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n = (2 * (‖B‖ + 1)) ^ n * (1 + ‖x‖) ^ (2 * n) by
          rw [mul_pow, pow_mul], pow_add]; ring
    _ ≤ n ! * (2 * (‖B‖ + 1)) ^ n * C := by gcongr; exact hC ‖x‖ hx0

end GlobalTheory.GaussSchwartz

namespace GlobalTheory.GaussSchwartz

open scoped ComplexOrder

section TraceForm

variable {ι : Type} [Fintype ι] {m n : ℕ}

def trForm (w : ι → ℝ) (M : ι → Matrix (Fin m) (Fin m) ℂ) (x y : ι → Fin m → Fin n → ℂ) : ℝ :=
  -(2 * Real.pi) * ∑ i, w i * (Matrix.trace ((Matrix.of (x i))ᴴ * M i * Matrix.of (y i))).re

def trFormL (w : ι → ℝ) (M : ι → Matrix (Fin m) (Fin m) ℂ) :
    (ι → Fin m → Fin n → ℂ) →ₗ[ℝ] (ι → Fin m → Fin n → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (trForm w M)
    (fun x x' y => by
      simp only [trForm, Pi.add_apply, ← Matrix.of_add_of, Matrix.conjTranspose_add, Matrix.add_mul,
        Matrix.trace_add, Complex.add_re, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [trForm, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : Matrix.of (c • x i) = c • Matrix.of (x i) := rfl
      rw [this, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul,
        Complex.smul_re, smul_eq_mul]
      ring)
    (fun x y y' => by
      simp only [trForm, Pi.add_apply, ← Matrix.of_add_of, Matrix.mul_add,
        Matrix.trace_add, Complex.add_re, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [trForm, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : Matrix.of (c • y i) = c • Matrix.of (y i) := rfl
      rw [this, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
      ring)

def trFormC (w : ι → ℝ) (M : ι → Matrix (Fin m) (Fin m) ℂ) :
    (ι → Fin m → Fin n → ℂ) →L[ℝ] (ι → Fin m → Fin n → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((ι → Fin m → Fin n → ℂ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ trFormL w M)

theorem trFormC_apply (w : ι → ℝ) (M : ι → Matrix (Fin m) (Fin m) ℂ) (x y : ι → Fin m → Fin n → ℂ) :
    trFormC w M x y = trForm w M x y := rfl

theorem trace_conjTranspose_mul_mul (M : Matrix (Fin m) (Fin m) ℂ) (Z : Matrix (Fin m) (Fin n) ℂ) :
    Matrix.trace (Zᴴ * M * Z) = ∑ j, star (fun a => Z a j) ⬝ᵥ (M *ᵥ fun a => Z a j) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem re_trace_nonneg {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.PosDef) (Z : Matrix (Fin m) (Fin n) ℂ) :
    0 ≤ (Matrix.trace (Zᴴ * M * Z)).re := by
  rw [trace_conjTranspose_mul_mul, Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => by
    simpa using (Complex.le_def.1 (hM.posSemidef.dotProduct_mulVec_nonneg (fun a => Z a j))).1

theorem re_trace_pos {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.PosDef) {Z : Matrix (Fin m) (Fin n) ℂ} (hZ : Z ≠ 0) :
    0 < (Matrix.trace (Zᴴ * M * Z)).re := by
  obtain ⟨j, hj⟩ : ∃ j, (fun a => Z a j) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hZ
    ext a j
    exact congrFun (h j) a
  rw [trace_conjTranspose_mul_mul, Complex.re_sum]
  refine Finset.sum_pos' (fun j _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
  · simpa using (Complex.le_def.1 (hM.posSemidef.dotProduct_mulVec_nonneg (fun a => Z a j))).1
  · simpa using (Complex.lt_def.1 (hM.dotProduct_mulVec_pos hj)).1

theorem trForm_self_neg (w : ι → ℝ) (hw : ∀ i, 0 < w i) (M : ι → Matrix (Fin m) (Fin m) ℂ)
    (hM : ∀ i, (M i).PosDef) (x : ι → Fin m → Fin n → ℂ) (hx : x ≠ 0) : trForm w M x x < 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  have hpos : 0 < ∑ i, w i * (Matrix.trace ((Matrix.of (x i))ᴴ * M i * Matrix.of (x i))).re := by
    refine Finset.sum_pos' (fun k _ => mul_nonneg (hw k).le (re_trace_nonneg (hM k) _))
      ⟨i, Finset.mem_univ _, mul_pos (hw i) (re_trace_pos (hM i) ?_)⟩
    intro h
    exact hi h
  unfold trForm
  have := Real.pi_pos
  nlinarith

theorem trace_conjTranspose_mul_mul_real {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.IsHermitian)
    (Z : Matrix (Fin m) (Fin n) ℂ) :
    (((Matrix.trace (Zᴴ * M * Z)).re : ℝ) : ℂ) = Matrix.trace (Zᴴ * M * Z) := by
  apply Complex.conj_eq_iff_re.mp
  change star (Matrix.trace _) = _
  rw [← Matrix.trace_conjTranspose]
  congr 1
  simp [Matrix.conjTranspose_mul, hM.eq, Matrix.mul_assoc]

end TraceForm

theorem exists_schwartz_gauss : ∀ (D : D7) (n : ℕ) (V : HSp D) (l : D.what₂.Tau → ℝ), (∀ τ, l τ ≠ 0) →
    ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∃ f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ, ∀ z, f z = gauss V l s (fun τ => Matrix.of (z τ)) := by
  intro D n V l hl s hs
  have hM : ∀ τ, (gramAt D V τ * s τ).PosDef := fun τ => (hs τ).2.2
  obtain ⟨f, hf⟩ := exists_schwartz_exp_diag (trFormC (n := n) (fun τ => |l τ|) (fun τ => gramAt D V τ * s τ))
    (fun x hx => by
      rw [trFormC_apply]
      exact trForm_self_neg _ (fun τ => abs_pos.2 (hl τ)) _ hM x hx)
  refine ⟨f, fun z => ?_⟩
  rw [hf, trFormC_apply, Complex.ofReal_exp, gauss]
  congr 1
  simp only [trForm]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [trace_conjTranspose_mul_mul_real (hM τ).1]

end GlobalTheory.GaussSchwartz

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
private theorem bijective_quot_mk_map_out {G₁ G₂ : Type} [Group G₁] [Group G₂] (κ : G₁ ≃* G₂)
    (P₁ Γ₁ : Subgroup G₁) (P₂ Γ₂ : Subgroup G₂) (hP : ∀ g, g ∈ P₁ ↔ κ g ∈ P₂)
    (hΓ : ∀ g, g ∈ Γ₁ ↔ κ g ∈ Γ₂) :
    Function.Bijective fun q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁) =>
      _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₂.subgroupOf Γ₂)
        (⟨κ (Quotient.out q : Γ₁), (hΓ _).1 (Quotient.out q : Γ₁).2⟩ : Γ₂) := by
  have hout : ∀ q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁),
      _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) (Quotient.out q) = q := by
    intro q
    unfold _root_.GlobalTheory.AutomorphicL2Unitary.mk
    exact Quotient.out_eq q
  constructor
  · intro q q' h
    simp only at h
    obtain ⟨p, hp⟩ := _root_.GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h
    have hp' : κ.symm ((p : Γ₂) : G₂) * (Quotient.out q : Γ₁) = (Quotient.out q' : Γ₁) := by
      apply κ.injective
      have := congrArg Subtype.val hp
      simpa using this
    have hmemΓ : κ.symm ((p : Γ₂) : G₂) ∈ Γ₁ := by
      rw [hΓ]; simpa using ((p : Γ₂)).2
    have hmemP : (⟨κ.symm ((p : Γ₂) : G₂), hmemΓ⟩ : Γ₁) ∈ P₁.subgroupOf Γ₁ := by
      rw [Subgroup.mem_subgroupOf, hP]
      simpa using Subgroup.mem_subgroupOf.1 p.2
    rw [← hout q, ← hout q']
    refine _root_.GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨_, hmemP⟩, ?_⟩
    ext
    simpa using hp'
  · intro q₂
    obtain ⟨y, rfl⟩ : ∃ y : Γ₂, _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₂.subgroupOf Γ₂) y = q₂ := by
      refine ⟨Quotient.out q₂, ?_⟩
      unfold _root_.GlobalTheory.AutomorphicL2Unitary.mk
      exact Quotient.out_eq q₂
    have hx : κ.symm (y : G₂) ∈ Γ₁ := by
      rw [hΓ]; simpa using y.2
    refine ⟨_root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) ⟨_, hx⟩, ?_⟩
    obtain ⟨p, hp⟩ := _root_.GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1
      (hout (_root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) ⟨_, hx⟩)).symm
    simp only
    rw [← hp]
    have hmemΓ : κ ((p : Γ₁) : G₁) ∈ Γ₂ := (hΓ _).1 (p : Γ₁).2
    have hmemP : (⟨κ ((p : Γ₁) : G₁), hmemΓ⟩ : Γ₂) ∈ P₂.subgroupOf Γ₂ := by
      rw [Subgroup.mem_subgroupOf]
      exact (hP _).1 (Subgroup.mem_subgroupOf.1 p.2)
    refine (_root_.GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨_, hmemP⟩, ?_⟩).symm
    ext
    simp

attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.StdUnn.cosetSum_along_mulEquiv : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (κ : G₁ ≃* G₂) (P₁ Γ₁ : Subgroup G₁) (P₂ Γ₂ : Subgroup G₂), (∀ g, g ∈ P₁ ↔ κ g ∈ P₂) → (∀ g, g ∈ Γ₁ ↔ κ g ∈ Γ₂) → ∀ (Φ₂ : G₂ → ℂ) (x : G₁) (c : ℂ) (Φ₁ : G₁ → ℂ), (∀ g, Φ₁ g = c * Φ₂ (κ (g * x))) → _root_.GlobalTheory.AutomorphicL2Unitary.LeftInv (P₂ ⊓ Γ₂) Φ₂ → _root_.GlobalTheory.AutomorphicL2Unitary.LeftInv (P₁ ⊓ Γ₁) Φ₁ ∧ ∀ g, (_root_.GlobalTheory.Eis.CosetConv P₂ Γ₂ Φ₂ (κ (g * x)) → _root_.GlobalTheory.Eis.CosetConv P₁ Γ₁ Φ₁ g) ∧ _root_.GlobalTheory.Eis.cosetSum P₁ Γ₁ Φ₁ g = c * _root_.GlobalTheory.Eis.cosetSum P₂ Γ₂ Φ₂ (κ (g * x)) := by
  intro G₁ G₂ _ _ κ P₁ Γ₁ P₂ Γ₂ hP hΓ Φ₂ x c Φ₁ hΦ hinv₂
  have hinv₁ : _root_.GlobalTheory.AutomorphicL2Unitary.LeftInv (P₁ ⊓ Γ₁) Φ₁ := by
    unfold _root_.GlobalTheory.AutomorphicL2Unitary.LeftInv at hinv₂ ⊢
    intro γ hγ g
    have hγ₂ : κ γ ∈ P₂ ⊓ Γ₂ :=
      Subgroup.mem_inf.2 ⟨(hP γ).1 (Subgroup.mem_inf.1 hγ).1, (hΓ γ).1 (Subgroup.mem_inf.1 hγ).2⟩
    rw [hΦ, hΦ, mul_assoc, map_mul, hinv₂ _ hγ₂]
  have hbij := bijective_quot_mk_map_out κ P₁ Γ₁ P₂ Γ₂ hP hΓ
  have hbij₁ : Function.Bijective fun q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁) =>
      _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) (Quotient.out q) := by
    have : (fun q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁) =>
        _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) (Quotient.out q)) = id := by
      funext q
      unfold _root_.GlobalTheory.AutomorphicL2Unitary.mk
      exact Quotient.out_eq q
    rw [this]
    exact Function.bijective_id
  have hterm : ∀ (g : G₁) (q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁)),
      Φ₁ (((Quotient.out q : Γ₁) : G₁) * g) =
        c * Φ₂ (((⟨κ (Quotient.out q : Γ₁), (hΓ _).1 (Quotient.out q : Γ₁).2⟩ : Γ₂) : G₂) *
          κ (g * x)) := by
    intro g q
    rw [hΦ, mul_assoc, map_mul]
  refine ⟨hinv₁, fun g => ⟨fun hconv => ?_, ?_⟩⟩
  · rw [_root_.GlobalTheory.Eis.cosetConv_iff hinv₁ hbij₁]
    rw [_root_.GlobalTheory.Eis.cosetConv_iff hinv₂ hbij] at hconv
    simp_rw [hterm g, norm_mul]
    exact hconv.mul_left _
  · rw [_root_.GlobalTheory.Eis.cosetSum_eq_tsum hinv₁ hbij₁,
      _root_.GlobalTheory.Eis.cosetSum_eq_tsum hinv₂ hbij]
    simp_rw [hterm g]
    exact tsum_mul_left

end GlobalTheory.StdUnn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroupsStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetSum_along_mulEquiv_subgroups : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (κ : G₁ ≃* G₂) (P₁ Γ₁ : Subgroup G₁) (P₂ Γ₂ : Subgroup G₂), (∀ g, g ∈ P₁ ↔ κ g ∈ P₂) → (∀ g, g ∈ Γ₁ ↔ κ g ∈ Γ₂) → ∀ (Φ₂ : G₂ → ℂ) (x : G₁) (c : ℂ) (Φ₁ : G₁ → ℂ), (∀ g, Φ₁ g = c * Φ₂ (κ (g * x))) → LeftInv (P₂ ⊓ Γ₂) Φ₂ → LeftInv (P₁ ⊓ Γ₁) Φ₁ ∧ ∀ g, (GlobalTheory.Eis.CosetConv P₂ Γ₂ Φ₂ (κ (g * x)) → GlobalTheory.Eis.CosetConv P₁ Γ₁ Φ₁ g) ∧ GlobalTheory.Eis.cosetSum P₁ Γ₁ Φ₁ g = c * GlobalTheory.Eis.cosetSum P₂ Γ₂ Φ₂ (κ (g * x)) := by
  first | exact @GlobalTheory.StdUnn.cosetSum_along_mulEquiv | exact GlobalTheory.StdUnn.cosetSum_along_mulEquiv | (intros; apply GlobalTheory.StdUnn.cosetSum_along_mulEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledBasisSkewColumnMatrixGramInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledBasisSkewColumnMatrixGramInverse
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section General

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem gram_fromCols_smul (G : Matrix (Fin (n + n)) (Fin (n + n)) E) (e e' : Matrix (Fin (n + n)) (Fin n) E) (μ : E)
    (hμ : star μ = -μ) (h₁ : eᴴ * G * e = 0) (h₂ : e'ᴴ * G * e' = 0) (h₃ : e'ᴴ * G * e = 1) (h₄ : eᴴ * G * e' = 1) :
    ((Matrix.fromCols e (μ • e')).submatrix id finSumFinEquiv.symm)ᴴ * G *
        (Matrix.fromCols e (μ • e')).submatrix id finSumFinEquiv.symm = μ • blk4 0 1 (-1) 0 := by
  have h : (Matrix.fromCols e (μ • e'))ᴴ * G * Matrix.fromCols e (μ • e') = μ • Matrix.fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
      Matrix.conjTranspose_smul, hμ, Matrix.fromBlocks_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, h₁, h₂, h₃, h₄, smul_zero, smul_neg, neg_smul, Matrix.neg_mul, neg_zero]
  ext i j
  exact congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)

theorem fromRows_mul_fromCols_smul (G : Matrix (Fin (n + n)) (Fin (n + n)) E) (e e' : Matrix (Fin (n + n)) (Fin n) E)
    (μ : E) (hμ : μ ≠ 0) (h₁ : eᴴ * G * e = 0) (h₂ : e'ᴴ * G * e' = 0) (h₃ : e'ᴴ * G * e = 1) (h₄ : eᴴ * G * e' = 1) :
    (Matrix.fromRows (e'ᴴ * G) (μ⁻¹ • (eᴴ * G))).submatrix finSumFinEquiv.symm id *
        (Matrix.fromCols e (μ • e')).submatrix id finSumFinEquiv.symm = (1 : Matrix (Fin (n + n)) (Fin (n + n)) E) := by
  have h : Matrix.fromRows (e'ᴴ * G) (μ⁻¹ • (eᴴ * G)) * Matrix.fromCols e (μ • e') = 1 := by
    rw [Matrix.fromRows_mul_fromCols]
    simp only [Matrix.smul_mul, Matrix.mul_smul, h₁, h₂, h₃, h₄, smul_zero, smul_smul, mul_inv_cancel₀ hμ,
      one_smul, Matrix.fromBlocks_one]
  rw [← Matrix.submatrix_one_equiv (finSumFinEquiv (m := n) (n := n)).symm, ← h]
  rfl

end General

theorem Tm_gram_inv : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → (Tm A μ)ᴴ * (dblSp A).gram * Tm A μ = μ • Jst D A.rank ∧ IsUnit (Tm A μ).det ∧ (Tm A μ)⁻¹ = (Matrix.fromRows (dblDec A).qX (μ⁻¹ • (dblDec A).qY)).submatrix finSumFinEquiv.symm id := by
  intro D A μ hμ
  have h₄ : (dblDec A).eᴴ * (dblSp A).gram * (dblDec A).e' = 1 := by
    have := congrArg Matrix.conjTranspose (dblDec A).e'e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
      Matrix.conjTranspose_one, ← Matrix.mul_assoc] at this
  have hi := fromRows_mul_fromCols_smul (n := A.rank) (dblSp A).gram (dblDec A).e (dblDec A).e' μ hμ.1
    (dblDec A).ee (dblDec A).e'e' (dblDec A).e'e h₄
  exact ⟨gram_fromCols_smul (n := A.rank) (dblSp A).gram (dblDec A).e (dblDec A).e' μ hμ.2
    (dblDec A).ee (dblDec A).e'e' (dblDec A).e'e h₄, Matrix.isUnit_det_of_left_inverse hi, Matrix.inv_eq_left_inv hi⟩

end GlobalTheory.StdUnn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledBasisSkewColumnMatrixGramInverseStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledBasisSkewColumnMatrix_gram_inverse : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → (Tm A μ)ᴴ * (dblSp A).gram * Tm A μ = μ • Jst D A.rank ∧ IsUnit (Tm A μ).det ∧ (Tm A μ)⁻¹ = (Matrix.fromRows (dblDec A).qX (μ⁻¹ • (dblDec A).qY)).submatrix finSumFinEquiv.symm id := by
  first | exact @GlobalTheory.StdUnn.Tm_gram_inv | exact GlobalTheory.StdUnn.Tm_gram_inv | (intros; apply GlobalTheory.StdUnn.Tm_gram_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {T L : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def zcol (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (y : WO L T) : n → k :=
  β.b' *ᵥ fun i => p.pr ((y *ᵥ fun j => incA D (ζ j)) i)

open Classical in
def colFun (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (a : (n → k) → ℂ) (y : WO L T) : ℂ :=
  if IsHalf p.e y then a (zcol β ζ y) else 0

def zrow (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (x : WO T L) : n → k :=
  (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)))⁻¹ •
    ((fun i => p.pr (((fun j => incA D ((star ζ ᵥ* L.gram) j)) ᵥ* x) i)) ᵥ* β.b)

open Classical in
def rowFun (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (b : (n → k) → ℂ) (x : WO T L) : ℂ :=
  if IsHalf p.e x then b (zrow β ζ x) else 0

def restrModel {m n m' n' m'' n'' : ℕ} (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (h : Mx D m'' n'' → ℂ)
    (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)) (y : Mx D m'' n'') :
    (Mx D m' n' → ℂ) →ₗ[ℂ] (Mx D m' n' → ℂ) where
  toFun Φ := fun w => T' (fun t => Φ (r t).1 * h (r t).2) (r.symm (w, y))
  map_add' Φ Φ' := by
    funext w
    have : (fun t => (Φ + Φ') (r t).1 * h (r t).2) = (fun t => Φ (r t).1 * h (r t).2) + fun t => Φ' (r t).1 * h (r t).2 := by
      funext t; simp [add_mul]
    rw [this, map_add (f := _)]; rfl
  map_smul' c Φ := by
    funext w
    have : (fun t => (c • Φ) (r t).1 * h (r t).2) = c • fun t => Φ (r t).1 * h (r t).2 := by
      funext t; simp [mul_assoc]
    rw [this, map_smul]; rfl

theorem restrModel_apply {m n m' n' m'' n'' : ℕ} (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (h : Mx D m'' n'' → ℂ)
    (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)) (y : Mx D m'' n'') (Φ : Mx D m' n' → ℂ) (w : Mx D m' n') :
    restrModel r h T' y Φ w = T' (fun t => Φ (r t).1 * h (r t).2) (r.symm (w, y)) := rfl

theorem heisO_resS_symm (ψ : AddChar (AF D.host.F) ℂ) {S A L T : HSp D} (o : OrthDec S A L) (a : WO A T)
    (F : WO S T → ℂ) (w : WO A T) (y : WO L T) :
    heisO ψ S T ((o.resS T).symm (a, 0)) F ((o.resS T).symm (w, y)) =
      heisO ψ A T a (fun w' => F ((o.resS T).symm (w', y))) w := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have h0 : symplOH L T y 0 = 0 := by simp [symplOH, symplO, hO]
  rw [h0, add_zero, ← map_add (f := _)]
  simp

theorem heisO_resT_symm (ψ : AddChar (AF D.host.F) ℂ) {S A L T : HSp D} (o : OrthDec S A L) (a : WO T A)
    (F : WO T S → ℂ) (w : WO T A) (y : WO T L) :
    heisO ψ T S ((o.resT T).symm (a, 0)) F ((o.resT T).symm (w, y)) =
      heisO ψ T A a (fun w' => F ((o.resT T).symm (w', y))) w := by
  simp only [heisO]
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have h0 : symplOH T L y 0 = 0 := by simp [symplOH, symplO, hO]
  rw [h0, add_zero, ← map_add (f := _)]
  simp

theorem symplO_resS_symm {S A L T : HSp D} (o : OrthDec S A L) (t : WO S T) (a : WO A T) :
    symplO S T t ((o.resS T).symm (a, 0)) = symplO A T ((o.resS T) t).1 a := by
  rw [o.symplO_resS, AddEquiv.apply_symm_apply]
  simp [symplO, hO]

theorem symplO_resT_symm {S A L T : HSp D} (o : OrthDec S A L) (t : WO T S) (a : WO T A) :
    symplO T S t ((o.resT T).symm (a, 0)) = symplO T A ((o.resT T) t).1 a := by
  rw [o.symplO_resT, AddEquiv.apply_symm_apply]
  simp [symplO, hO]

theorem half_resS_symm {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} {a : WO A T} (ha : IsHalf e a) :
    IsHalf e ((o.resS T).symm (a, 0)) := by
  intro i j
  rw [OrthDec.resS_symm_apply]
  simp only [Matrix.zero_mul, add_zero, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [← mul_assoc, ha]

theorem half_resT_symm {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} {a : WO T A} (ha : IsHalf e a) :
    IsHalf e ((o.resT T).symm (a, 0)) := by
  intro i j
  rw [OrthDec.resT_symm_apply]
  simp only [Matrix.mul_zero, add_zero, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [mul_left_comm, ha]

section Lat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [Fintype n']

theorem latInd_lastKer (ΛA : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)) :
    latInd (lastKer ΛA) ΛT = tensCol (latInd ΛA ΛT) (vecInd ΛT) := by
  classical
  funext x
  have hmv : ∀ y : n' ⊕ Fin 1 → k, x *ᵥ y = x.submatrix id Sum.inl *ᵥ (y ∘ Sum.inl) +
      y (Sum.inr 0) • fun i => x i (Sum.inr 0) := by
    intro y; funext i
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]
  have key : (∀ y ∈ lastKer ΛA, x *ᵥ y ∈ ΛT) ↔
      (∀ y ∈ ΛA, x.submatrix id Sum.inl *ᵥ y ∈ ΛT) ∧ (fun i => x i (Sum.inr 0)) ∈ ΛT := by
    constructor
    · intro h
      refine ⟨fun y hy => ?_, ?_⟩
      · have hm : Sum.elim y 0 ∈ lastKer ΛA := GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa using hy, by simp⟩
        have := h _ hm
        rw [hmv] at this
        simpa using this
      · have hm : (Sum.elim 0 1 : n' ⊕ Fin 1 → k) ∈ lastKer ΛA :=
          GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa using ΛA.zero_mem, by simp⟩
        have := h _ hm
        rw [hmv] at this
        simpa using this
    · rintro ⟨h1, h2⟩ y hy
      obtain ⟨hy1, hy2⟩ := GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy
      rw [hmv]
      refine ΛT.add_mem (h1 _ hy1) ?_
      have := ΛT.smul_mem (⟨y (Sum.inr 0), hy2⟩ : 𝒪[k]) h2
      exact this
  simp only [latInd, tensCol, vecInd]
  by_cases h : ∀ y ∈ lastKer ΛA, x *ᵥ y ∈ ΛT
  · rw [if_pos h, if_pos (key.1 h).1, if_pos (key.1 h).2, mul_one]
  · rw [if_neg h]
    by_cases h1 : ∀ y ∈ ΛA, x.submatrix id Sum.inl *ᵥ y ∈ ΛT
    · rw [if_pos h1, if_neg fun h2 => h (key.2 ⟨h1, h2⟩), mul_zero]
    · rw [if_neg h1, zero_mul]

theorem latInd_lastKer_row (ΛA : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)) :
    latInd ΛT (lastKer ΛA) = tensRow (latInd ΛT ΛA) (dualInd ΛT) := by
  classical
  funext x
  have key : (∀ y ∈ ΛT, x *ᵥ y ∈ lastKer ΛA) ↔
      (∀ y ∈ ΛT, x.submatrix Sum.inl id *ᵥ y ∈ ΛA) ∧ InDual ΛT (x (Sum.inr 0)) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer, InDual]
    exact ⟨fun h => ⟨fun y hy => (h y hy).1, fun y hy => (h y hy).2⟩, fun h y hy => ⟨h.1 y hy, h.2 y hy⟩⟩
  simp only [latInd, tensRow, dualInd]
  by_cases h : ∀ y ∈ ΛT, x *ᵥ y ∈ lastKer ΛA
  · rw [if_pos h, if_pos (key.1 h).1, if_pos (key.1 h).2, mul_one]
  · rw [if_neg h]
    by_cases h1 : ∀ y ∈ ΛT, x.submatrix Sum.inl id *ᵥ y ∈ ΛA
    · rw [if_pos h1, if_neg fun h2 => h (key.2 ⟨h1, h2⟩), mul_zero]
    · rw [if_neg h1, zero_mul]

end Lat

end GlobalTheory.FinPl.ExtZero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponen
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

namespace GlobalTheory.FrameGlob

open Matrix

theorem exists_gl_of_lattices {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (Λ₁ Λ₂ : Submodule 𝒪[k] (n → k)) (h₁ : Λ₁.IsFullLattice k)
    (h₂ : Λ₂.IsFullLattice k) : ∃ g : GL n k, ∀ z, z ∈ Λ₁ ↔ g.val *ᵥ z ∈ Λ₂ := by
  have key : ∀ (Λ : Submodule 𝒪[k] (n → k)), Λ.IsFullLattice k →
      ∃ e : (Fin (Fintype.card n) → k) ≃ₗ[k] (n → k), ∀ y, e y ∈ Λ ↔ ∀ i, y i ∈ 𝒪[k] := by
    intro Λ hΛ
    let : Module.Free 𝒪[k] Λ := Submodule.IsLattice.free k Λ
    let : Module.Finite 𝒪[k] Λ := Submodule.IsLattice.finite k Λ
    let b := Module.finBasisOfFinrankEq 𝒪[k] Λ
      ((Submodule.IsFullLattice.finrank_eq k Λ).trans (Module.finrank_fintype_fun_eq_card k))
    let b' := b.extendOfIsFullLattice k
    have hkey : ∀ c : Fin (Fintype.card n) → 𝒪[k],
        b'.equivFun.symm (fun i => (c i : k)) = ((∑ i, c i • b i : Λ) : n → k) := by
      intro c
      rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Module.Basis.extendOfIsFullLattice_apply]
      rfl
    refine ⟨b'.equivFun.symm, fun y => ⟨fun h => ?_, fun h => ?_⟩⟩
    · have h1 := hkey (b.repr ⟨_, h⟩)
      rw [b.sum_repr] at h1
      rw [← b'.equivFun.symm.injective h1]
      exact fun i => (b.repr ⟨_, h⟩ i).2
    · have h1 := hkey fun i => ⟨y i, h i⟩
      have h2 : b'.equivFun.symm y = _ := h1
      rw [h2]
      exact Subtype.property _
  obtain ⟨e₁, he₁⟩ := key Λ₁ h₁
  obtain ⟨e₂, he₂⟩ := key Λ₂ h₂
  let φ : (n → k) ≃ₗ[k] (n → k) := e₁.symm.trans e₂
  refine ⟨⟨LinearMap.toMatrix' φ.toLinearMap, LinearMap.toMatrix' φ.symm.toLinearMap, ?_, ?_⟩, fun z => ?_⟩
  · rw [← LinearMap.toMatrix'_mul]
    have : φ.toLinearMap * φ.symm.toLinearMap = LinearMap.id := by ext; simp
    rw [this, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_mul]
    have : φ.symm.toLinearMap * φ.toLinearMap = LinearMap.id := by ext; simp
    rw [this, LinearMap.toMatrix'_id]
  · show z ∈ Λ₁ ↔ LinearMap.toMatrix' φ.toLinearMap *ᵥ z ∈ Λ₂
    rw [LinearMap.toMatrix'_mulVec]
    have h := he₁ (e₁.symm z)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.coe_coe, ← he₂]
    rfl

end GlobalTheory.FrameGlob

namespace GlobalTheory.FrameGlob

open Matrix

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mem_idAt (p : SplitPt D k) : p.e ∈ idAt D (· = p.v) := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  obtain ⟨hee, hec, -⟩ := p.split
  refine ((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D p.v ε hε).1 p.e).2 ?_
  rw [← hsum, add_mul, hee, mul_comm (cA D p.e), hec, add_zero]

theorem sec_eq_mul (p : SplitPt D k) (a : k) : p.sec a = p.e * p.sec a := by
  have h := p.sec_pr (p.sec a)
  rwa [p.pr_sec] at h

theorem sec_mem_idAt (p : SplitPt D k) (a : k) : p.sec a ∈ idAt D (· = p.v) := by
  rw [sec_eq_mul]
  exact Ideal.mul_mem_right _ _ (e_mem_idAt p)

variable {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem mt_gl_vec {p : SplitPt D k} (β : Frame p S n) (g : GL n k) (z : n → k) :
    mt S (β.gl g) *ᵥ (fun i => p.sec ((β.b *ᵥ z) i)) = fun i => p.sec ((β.b *ᵥ (g.val *ᵥ z)) i) := by
  funext i
  set m := mt S (β.gl g)
  set y : Fin S.rank → AE D := fun i => p.sec ((β.b *ᵥ z) i)
  have he : (m *ᵥ y) i = p.e * (m *ᵥ y) i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show m i j * p.sec _ = p.e * (m i j * p.sec _)
    conv_lhs => rw [sec_eq_mul]
    ring
  have hpr : p.pr ((m *ᵥ y) i) = ((m.map p.pr) *ᵥ (β.b *ᵥ z)) i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, y, p.pr_sec]
  rw [he, ← p.sec_pr, hpr, β.gl_mat, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.mul_assoc, β.b'b, Matrix.mul_one]

theorem mt_gl_off {p : SplitPt D k} (β : Frame p S n) (g : GL n k) (y : Fin S.rank → AE D)
    (hy : ∀ i, y i ∈ idAt D (· ≠ p.v)) : mt S (β.gl g) *ᵥ y = y := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  have h0 : (mt S (β.gl g) - 1) *ᵥ y = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← β.gl_supp g i j, hsum]
    calc algebraMap (AF D.host.F) (AE D) ε * (mt S (β.gl g) - 1) i j * y j
        = (mt S (β.gl g) - 1) i j * (algebraMap (AF D.host.F) (AE D) ε * y j) := by ring
      _ = 0 := by rw [(GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D p.v ε hε).2 _ (hy j), mul_zero]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
  exact h0

theorem main : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (L : Lat S)
    (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → Λ.IsFullLattice k →
    ∃ M : Lat S, IsSelfDualC S M ∧ β.IsLat M Λ ∧ latV S M (· ≠ p.v) = latV S L (· ≠ p.v) := by
  intro D k _ _ _ _ p S n _ _ β L Λ hL hΛ
  obtain ⟨Λ₁, hΛ₁, hLat₁, -⟩ := GlobalTheory.T.selfDual_splitComponent_isLattice_stabilizer_eq D k p S n β L hL
  have hFull₁ : Λ₁.IsFullLattice k := by
    refine { toIsLattice := hΛ₁, span_eq_top := eq_top_iff.mpr fun x _ => ?_ }
    obtain ⟨m, s, c, hs, hc, -⟩ := FrameLat.exists_gen (p := p) hL
    have hx := congrArg (β.b' *ᵥ ·) (hc (β.b *ᵥ x))
    simp only [Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec, Matrix.mulVec_sum,
      Matrix.mulVec_smul] at hx
    rw [hx]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    apply (hLat₁ _).2
    rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
    exact FrameLat.sec_inc_mem (p := p) (hs l)
  obtain ⟨g, hg⟩ := exists_gl_of_lattices Λ₁ Λ hFull₁ hΛ
  obtain ⟨M, hM, hMv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D S L hL).1 (β.gl g)
  have supp : ∀ (N : Lat S), IsSelfDualC S N → ∀ y, y ∈ latV S N (· ≠ p.v) → ∀ i, y i ∈ idAt D (· ≠ p.v) :=
    fun N hN y hy => (((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· ≠ p.v)).2 S).2.2.2 N y hN.1 |>.1 hy).1
  refine ⟨M, hM, fun x => ?_, ?_⟩
  · have hx : x = g.val *ᵥ ((g⁻¹).val *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [hx, ← hg, hLat₁, hMv (· = p.v) _ (fun i => sec_mem_idAt p _), mt_gl_vec]
  · ext y
    constructor
    · intro hy
      have hs := supp M hM y hy
      rw [← mt_gl_off β g y hs] at hy
      exact (hMv (· ≠ p.v) y hs).2 hy
    · intro hy
      have hs := supp L hL y hy
      have h := (hMv (· ≠ p.v) y hs).1 hy
      rwa [mt_gl_off β g y hs] at h

end GlobalTheory.FrameGlob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_lattice_with_prescribed_splitComponent : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (L : Lat S)
    (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → Λ.IsFullLattice k →
    ∃ M : Lat S, IsSelfDualC S M ∧ β.IsLat M Λ ∧ latV S M (· ≠ p.v) = latV S L (· ≠ p.v) := by
  first | exact @GlobalTheory.FrameGlob.main | exact GlobalTheory.FrameGlob.main | (intros; apply GlobalTheory.FrameGlob.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionInvariantConvergent
noncomputable section

open scoped NNReal TensorProduct
open NumberField Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Eis.Conv GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GodementSectionReduction

open Formalism.UG (bc)

theorem row_ne_zero {A : Type} [CommRing A] [Nontrivial A] {r n : ℕ} {M : Matrix (Fin r) (Fin n) A}
    {N : Matrix (Fin n) (Fin r) A} (h : M * N = 1) (i : Fin r) : ¬∀ x, M i x = 0 := fun h2 => by
  have h5 := congrFun (congrFun h i) i
  rw [Matrix.mul_apply, one_apply_eq, Finset.sum_eq_zero fun x _ => by rw [h2, zero_mul]] at h5
  exact zero_ne_one h5

variable {D : D7} {T T₀ : HSp D} {r : ℕ}

variable (d : HypDec T T₀ r)

theorem nB_mem (b : Mx D r T₀.rank) : d.nB b ∈ stab d := ⟨1, by rw [d.nB_jX, Units.val_one, Matrix.mul_one]⟩

theorem nC_mem (c : skewA D r) : d.nC c ∈ stab d := ⟨1, by rw [d.nC_jX, Units.val_one, Matrix.mul_one]⟩

theorem wittCoreEmbedding_mem_isotropicStabilizer (g : GA D T₀) : d.emb0 g ∈ stab d := ⟨1, by rw [d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]⟩

theorem exists_decomp (p : stab d) : ∃ b c g, (p : GA D T) = d.nB b * d.nC c * d.emb0 g * d.levi (onX d p) := by
  have h : (p : GA D T) * d.levi (onX d p)⁻¹ ∈ MixPer.stabX d := by
    show mt T (p * d.levi (onX d p)⁻¹) ⬝ d.jX = d.jX
    rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, d.levi_jX, cancel₂ (mul_jX d p), Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  obtain ⟨n, hn, g, e⟩ := (MixPer.Decomp.mem_stabX_iff d).1 h
  obtain ⟨b, c, rfl⟩ := (MixPer.Decomp.mem_radX_iff d).1 hn
  exact ⟨b, c, g, by rw [← e, map_inv, inv_mul_cancel_right]⟩

theorem reduction_GL_diagonalUnitPowers_compact {E A : Type} [Field E] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    (j : E →+* A) {s : Aˣ} {ν : Aˣ →* ℝ≥0} (hν : Continuous ν) (hj : ∀ u : Eˣ, ν (Units.map j.toMonoidHom u) = 1)
    {b : ℝ} (hb : 0 < b) (hs : (ν s : ℝ) = b⁻¹) {r : ℕ}
    (hR : ∃ Ω : Set A, IsCompact Ω ∧ ∀ β : GL (Fin r) A, ∃ (δ : GL (Fin r) E) (l : Fin r → ℤ) (c : GL (Fin r) A),
      (∀ i k, c.1 i k ∈ Ω ∧ c⁻¹.1 i k ∈ Ω) ∧ δ.1.map j * β.1 = diagonal (fun i => (s ^ l i).1) * c.1) :
    ∃ (L : Set (GL (Fin r) A)) (C : ℝ), IsCompact L ∧ ∀ α : GL (Fin r) A,
    ∃ (δ : GL (Fin r) E) (l : Fin r → ℤ), ∃ c ∈ L, bc j δ * α = dg s l * c ∧
      (ν (GeneralLinearGroup.det α) : ℝ) ≤ C * ∏ i, (b ^ l i)⁻¹ := by
  obtain ⟨Ω, hΩ, hR⟩ := hR
  choose δ l c hcΩ hred using hR
  replace hred : ∀ β, bc j (δ β) * β = dg s (l β) * c β := fun β => Units.ext (hred β)
  obtain ⟨L, hL, hcL⟩ : Bdd c :=
    bdd_units (bdd_matrix hΩ fun q i k => (hcΩ q i k).1) (bdd_matrix hΩ fun q i k => (hcΩ q i k).2)
  have hdet : Continuous (GeneralLinearGroup.det : GL (Fin r) A → Aˣ) := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩
  obtain ⟨B, hB⟩ := (hL.image (NNReal.continuous_coe.comp (hν.comp hdet))).bddAbove
  refine ⟨L, B, hL, fun α => ⟨δ α, l α, c α, hcL α, hred α, ?_⟩⟩
  have h1 : GeneralLinearGroup.det (bc j (δ α)) = Units.map j.toMonoidHom (GeneralLinearGroup.det (δ α)) :=
    Units.ext (j.map_det (δ α).1).symm
  have h3 := congrArg (fun x => (ν (GeneralLinearGroup.det x) : ℝ)) (hred α)
  beta_reduce at h3
  rw [map_mul, map_mul, map_mul, map_mul, h1, hj, one_mul, det_dg, map_prod, NNReal.coe_mul, NNReal.coe_prod] at h3
  have h4 : ∀ i, (ν (s ^ l α i) : ℝ) = (b ^ l α i)⁻¹ := fun i => by
    rw [map_zpow, NNReal.coe_zpow, hs, _root_.inv_zpow]
  rw [h3, mul_comm, Finset.prod_congr rfl fun i _ => h4 i]
  exact mul_le_mul_of_nonneg_right (hB ⟨_, hcL α, rfl⟩) (by positivity)

theorem bound_aux {E A : Type} [Field E] [CommRing A] (j : E →+* A) {s : Aˣ} {Ω : Set A} {m₀ r n : ℕ}
    (hm₀ : ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, j x = s.1 ^ m * ω → x = 0) {l : Fin r → ℤ} {y : Matrix (Fin r) (Fin n) E}
    {w : Matrix (Fin r) (Fin n) A} (hw : ∀ i x, w i x ∈ Ω) (e : y.map j = (dg s l)⁻¹.1 * w) (i : Fin r)
    (h : ¬∀ x, y.map j i x = 0) : -(m₀ : ℤ) ≤ l i := by
  by_contra! hlt
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (a := -l i) (by omega)
  refine h fun x => ?_
  have h3 : j (y i x) = s.1 ^ m * w i x := by
    refine (congrFun (congrFun e i) x).trans ?_
    rw [show (dg s l)⁻¹.1 = diagonal fun i => (s ^ l i)⁻¹.1 from rfl, diagonal_mul, ← _root_.zpow_neg, hm, zpow_natCast,
      Units.val_pow_eq_pow_val]
  rw [map_apply, hm₀ m (by omega) _ (hw i x) _ h3, map_zero]

end GlobalTheory.GodementSectionReduction

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualDirectionDerivativeMixedCoordinateBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualDirection_derivative_mixedCoordinate_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin ρ) ℂ), ∃ Z : Matrix (Fin T.rank) (Fin S.rank) ℂ, ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ x w, |2 * (tauE D τ D.host.xi0 * ((compAt θ τ x)ᴴ * gramAt D T τ * z).trace).re| * ‖d.mixS T ψ v.μ v.𝓕 f x w‖ ≤ ‖d.mixS T ψ v.μ v.𝓕 (dRho (heisO ψ S T) θ τ Z f) x w‖ := by
  first | exact @GlobalTheory.Unf.norm_mixS_dRho_ge | exact GlobalTheory.Unf.norm_mixS_dRho_ge | (intros; apply GlobalTheory.Unf.norm_mixS_dRho_ge <;> assumption)
end
