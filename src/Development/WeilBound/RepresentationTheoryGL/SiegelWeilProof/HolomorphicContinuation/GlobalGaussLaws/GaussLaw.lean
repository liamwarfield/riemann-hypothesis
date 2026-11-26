module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def IsAwayFn {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (Ψ : Mx D m n → ℂ) : Prop :=
  ∀ x x' : Mx D m n, (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') → x.map (finPart D) = x'.map (finPart D) → Ψ x = Ψ x'

def IsTrivAt (θ : InfFam D) (τ : D.what₂.Tau) (x : G D n) : Prop := compAt θ τ (mat x) = 1

def IsLocFact {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (τ : D.what₂.Tau)
    (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (ι : GR n →* G D n)
    (L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)) : Prop :=
  (∀ y f, IsSch f → IsSch (L y f)) ∧ ∀ (y : GR n) Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
    (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (L y f) Ψ

def epsT {m : ℕ} (t : ℝ) (ε : Fin m → Bool) : Fin m → Bool := fun a => if 0 < t then ε a else !ε a

def gramB {m : ℕ} (ε : Fin m → Bool) (b : Bool) (y : Fin m → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => evX (Qb ε b i j) y

def gZf {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * c * (Z * gramB (epsT t ε) true y).trace - Complex.I * c * (Zᴴ * gramB (epsT t ε) false y).trace)

def IsSiegel (Z : Matrix (Fin n) (Fin n) ℂ) : Prop := ((-(Complex.I / 2)) • (Z - Zᴴ)).PosDef

def actZ (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((mR y).toBlocks₁₁ * Z + (mR y).toBlocks₁₂) * ((mR y).toBlocks₂₁ * Z + (mR y).toBlocks₂₂)⁻¹

def jF (e : ℤ) (p q : ℕ) (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (mR y).det ^ e * ((mR y).toBlocks₂₁ * Z + (mR y).toBlocks₂₂).det ^ (-(p : ℤ)) *
    ((mR y).toBlocks₂₁ * Zᴴ + (mR y).toBlocks₂₂).det ^ (-(q : ℤ))

def GZSch : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ), 0 < c → |t| = c → ∀ Z : Matrix (Fin n) (Fin n) ℂ, IsSiegel Z → IsSch (gZf ε t c Z)

def AwayAct : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ x : G D n, IsTrivAt θ τ x →
    ∃ A : (Mx D V.rank n → ℂ) → (Mx D V.rank n → ℂ), ∀ Ψ (hΨ : AwayCls θ τ fr Ψ), AwayCls θ τ fr (A Ψ) ∧
      ∀ f (hf : IsSch f), (ω x ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr f (A Ψ)

def DecompAway : Prop :=
  ∀ (D : D7) (n : ℕ) (θ : InfFam D) (τ : D.what₂.Tau) (ι : GR n →* G D n), IsInfFam θ → IsPlaceEmb θ τ ι → ∀ g : G D n,
    ∃ (x : G D n) (y : GR n), IsTrivAt θ τ x ∧ g = x * ι y ∧ ∀ y' : GR n, x * ι y' = ι y' * x

def LocFact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∃ L, IsLocFact ω τ fr ι L

def GaussLaw : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∃ e : ℤ, ∀ (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ), IsSiegel Z →
      L y (gZf ε (tLoc l τ) (cLoc l τ) Z) = fun u => jF e (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) y Z *
        gZf ε (tLoc l τ) (cLoc l τ) (actZ y Z) u

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.EvXTemperate
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

theorem evX_temperate {m n : ℕ} (P : PX m n) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => evX P u) := by
  have hcoord : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => u a i) := by
    intro a i
    exact ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ))).hasTemperateGrowth
  have hconj : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => star (u a i)) := by
    intro a i
    have h := (Complex.conjCLE.toContinuousLinearMap.comp
      ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))).hasTemperateGrowth
    convert h using 1
    funext u
    simp [Complex.conjCLE_apply]
  refine MvPolynomial.induction_on
    (motive := fun Q : PX m n =>
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => evX Q u)) P ?_ ?_ ?_
  · intro a
    convert Function.HasTemperateGrowth.const (E := Fin m → Fin n → ℂ) a using 1
    funext u
    simp [evX]
  · intro p q hp hq
    convert hp.add hq using 1
    funext u
    simp [evX]
  · intro p k hp
    obtain ⟨a, i, b⟩ := k
    cases b
    · have e : (fun u : Fin m → Fin n → ℂ => evX (p * X (a, i, false)) u) =
          (fun u => evX p u) * (fun u => u a i) := by
        funext u
        simp [evX]
      rw [e]
      exact hp.mul (hcoord a i)
    · have e : (fun u : Fin m → Fin n → ℂ => evX (p * X (a, i, true)) u) =
          (fun u => evX p u) * (fun u => star (u a i)) := by
        funext u
        simp [evX]
      rw [e]
      exact hp.mul (hconj a i)

private theorem hasTemperateGrowth_const_mul_sum_norm_sq {m n : ℕ} (c : ℝ) :
    Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) := by
  have hre : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => (u a i).re) := fun a i =>
    (Complex.reCLM.comp ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))).hasTemperateGrowth
  have him : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => (u a i).im) := fun a i =>
    (Complex.imCLM.comp ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))).hasTemperateGrowth
  have hsq : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => ‖u a i‖ ^ 2) := by
    intro a i
    have e : (fun u : Fin m → Fin n → ℂ => ‖u a i‖ ^ 2) =
        fun u : Fin m → Fin n → ℂ => (u a i).re * (u a i).re + (u a i).im * (u a i).im := by
      funext u
      rw [Complex.sq_norm, Complex.normSq_apply]
    rw [e]
    exact ((hre a i).mul (hre a i)).add ((him a i).mul (him a i))
  have hin : ∀ a : Fin m, Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => ∑ i : Fin n, ‖u a i‖ ^ 2) := fun a =>
    Function.HasTemperateGrowth.sum fun i _ => hsq a i
  have hsum : Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) :=
    Function.HasTemperateGrowth.sum fun a _ => hin a
  exact (Function.HasTemperateGrowth.const c).mul hsum

private theorem norm_iteratedFDeriv_cexp_neg_eq_exp_neg (i : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ i (fun s : ℝ => Complex.exp (-(s : ℂ))) t‖ = Real.exp (-t) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hit : iteratedDeriv i (fun s : ℝ => Complex.exp (-(s : ℂ))) =
      fun s : ℝ => (-1 : ℂ) ^ i * Complex.exp (-(s : ℂ)) := by
    induction i with
    | zero =>
      funext s
      simp
    | succ i ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := by
        simpa using (hasDerivAt_id s).ofReal_comp
      have hd : HasDerivAt (fun s : ℝ => -(s : ℂ)) (-1) s := h0.neg
      have he := (hd.cexp).const_mul ((-1 : ℂ) ^ i)
      rw [he.deriv]
      ring
  rw [hit]
  simp [Complex.norm_exp]

private theorem exists_bound_one_add_pow_mul_exp_neg_sq (c : ℝ) (hc : 0 < c) (j : ℕ) :
    ∃ M : ℝ, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ j * Real.exp (-(c * r ^ 2)) ≤ M := by
  refine ⟨2 ^ j * (1 + j.factorial / c ^ j), fun r hr => ?_⟩
  have hy : 0 ≤ c * r ^ 2 := by positivity
  have hexp := Real.pow_div_factorial_le_exp (c * r ^ 2) hy j
  have hE : 0 < Real.exp (c * r ^ 2) := Real.exp_pos _
  have hcj : 0 < c ^ j := pow_pos hc j
  have h2j : (0 : ℝ) < 2 ^ j := pow_pos two_pos j
  have hr2j : 0 ≤ (r ^ 2) ^ j := by positivity
  have h1 : (1 + r) ^ j ≤ 2 ^ j * (1 + (r ^ 2) ^ j) := by
    rcases le_total r 1 with h | h
    · calc (1 + r) ^ j ≤ 2 ^ j := pow_le_pow_left₀ (by linarith) (by linarith) j
        _ ≤ 2 ^ j * (1 + (r ^ 2) ^ j) := by nlinarith
    · calc (1 + r) ^ j ≤ (2 * r ^ 2) ^ j := pow_le_pow_left₀ (by linarith) (by nlinarith) j
        _ = 2 ^ j * (r ^ 2) ^ j := mul_pow _ _ _
        _ ≤ 2 ^ j * (1 + (r ^ 2) ^ j) := by nlinarith
  have h2 : (r ^ 2) ^ j * Real.exp (-(c * r ^ 2)) ≤ j.factorial / c ^ j := by
    rw [mul_pow, div_le_iff₀ (by positivity)] at hexp
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hE hcj]
    nlinarith
  have h3 : Real.exp (-(c * r ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  calc (1 + r) ^ j * Real.exp (-(c * r ^ 2))
      ≤ 2 ^ j * (1 + (r ^ 2) ^ j) * Real.exp (-(c * r ^ 2)) := by gcongr
    _ = 2 ^ j * (Real.exp (-(c * r ^ 2)) + (r ^ 2) ^ j * Real.exp (-(c * r ^ 2))) := by ring
    _ ≤ 2 ^ j * (1 + j.factorial / c ^ j) :=
        mul_le_mul_of_nonneg_left (add_le_add h3 h2) h2j.le

theorem gs_sch {m n : ℕ} (c : ℝ) (hc : 0 < c) :
    ∃ S : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u, S u = gs c u := by
  have hqT := hasTemperateGrowth_const_mul_sum_norm_sq (m := m) (n := n) c
  have hhC : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Complex.exp (-(s : ℂ))) :=
    Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.neg)
  have hgs : (gs c : (Fin m → Fin n → ℂ) → ℂ) =
      (fun s : ℝ => Complex.exp (-(s : ℂ))) ∘
        (fun u : Fin m → Fin n → ℂ => c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) := by
    funext u
    simp [gs]
  have hlow : ∀ u : Fin m → Fin n → ℂ, ‖u‖ ^ 2 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2 := by
    intro u
    have hS0 : 0 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2 := by positivity
    have hb : ‖u‖ ≤ Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      have h1 : ‖u a i‖ ^ 2 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2 :=
        calc ‖u a i‖ ^ 2 ≤ ∑ i' : Fin n, ‖u a i'‖ ^ 2 :=
              Finset.single_le_sum (f := fun i' => ‖u a i'‖ ^ 2)
                (fun _ _ => by positivity) (Finset.mem_univ i)
          _ ≤ ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2 :=
              Finset.single_le_sum (f := fun a' => ∑ i' : Fin n, ‖u a' i'‖ ^ 2)
                (fun _ _ => by positivity) (Finset.mem_univ a)
      have h2 := Real.abs_le_sqrt h1
      rwa [abs_of_nonneg (norm_nonneg _)] at h2
    calc ‖u‖ ^ 2 ≤ (Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = _ := Real.sq_sqrt hS0
  refine ⟨⟨gs c, ?_, ?_⟩, fun u => rfl⟩
  · rw [hgs]
    exact hhC.comp hqT.1
  · intro k N
    obtain ⟨K, C, hC0, hC⟩ := hqT.norm_iteratedFDeriv_le_uniform N
    obtain ⟨M, hM⟩ := exists_bound_one_add_pow_mul_exp_neg_sq c hc (k + K * N)
    refine ⟨N.factorial * (C + 1) ^ N * M, fun u => ?_⟩
    have hu0 := norm_nonneg u
    have hD1 : 1 ≤ (C + 1) * (1 + ‖u‖) ^ K :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by linarith))
    have hD : ∀ i : ℕ, 1 ≤ i → i ≤ N →
        ‖iteratedFDeriv ℝ i
          (fun u : Fin m → Fin n → ℂ => c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) u‖ ≤
          ((C + 1) * (1 + ‖u‖) ^ K) ^ i := by
      intro i hi1 hiN
      calc _ ≤ C * (1 + ‖u‖) ^ K := hC i hiN u
        _ ≤ (C + 1) * (1 + ‖u‖) ^ K := by gcongr; linarith
        _ ≤ _ := le_self_pow₀ hD1 (by omega)
    have key := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (n := N) hhC hqT.1
      (by exact_mod_cast le_top) u
      (C := Real.exp (-(c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2)))
      (fun i _ => (norm_iteratedFDeriv_cexp_neg_eq_exp_neg i _).le) hD
    have hexp_le : Real.exp (-(c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2)) ≤
        Real.exp (-(c * ‖u‖ ^ 2)) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left (hlow u) hc.le
      linarith
    have hpow : ‖u‖ ^ k ≤ (1 + ‖u‖) ^ k := pow_le_pow_left₀ hu0 (by linarith) k
    rw [hgs]
    calc ‖u‖ ^ k * ‖iteratedFDeriv ℝ N _ u‖
        ≤ (1 + ‖u‖) ^ k * (N.factorial * Real.exp (-(c * ‖u‖ ^ 2)) *
            ((C + 1) * (1 + ‖u‖) ^ K) ^ N) := by
          refine mul_le_mul hpow (key.trans ?_) (norm_nonneg _) (by positivity)
          gcongr
      _ = N.factorial * (C + 1) ^ N *
            ((1 + ‖u‖) ^ (k + K * N) * Real.exp (-(c * ‖u‖ ^ 2))) := by
          rw [mul_pow, ← pow_mul, pow_add]
          ring
      _ ≤ N.factorial * (C + 1) ^ N * M := by
          gcongr
          exact hM _ hu0

theorem schFP : SchFP := by
  intro m n c hc P
  obtain ⟨S, hS⟩ := gs_sch (m := m) (n := n) c hc
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => evX P u) S, ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply (evX_temperate P)]
  funext u
  simp [fP, hS, smul_eq_mul]

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellA
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocCellA

end PositivityTheory.Rg.Sw.Glob.LocCellA

namespace PositivityTheory.Rg.Sw.Glob

end PositivityTheory.Rg.Sw.Glob

namespace PositivityTheory.Rg.Sw.Glob.LocCellA

theorem block_matrix_mul_comm_ring {R : Type} [Ring R] {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_diagonal_one_eq_one {R : Type} [Ring R] {n : ℕ} : (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = blk4 1 0 0 1 := by
  simp only [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem block_matrix_map {R S : Type} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4
  rw [← Matrix.fromBlocks_map]
  rfl

theorem map_neg_one' {R S : Type} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) :
    (-1 : Matrix (Fin n) (Fin n) R).map f = -1 := by
  change (f.mapMatrix) (-1) = -1
  rw [map_neg, map_one]

theorem map_one' {R S : Type} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) :
    (1 : Matrix (Fin n) (Fin n) R).map f = 1 := by
  change (f.mapMatrix) 1 = 1
  rw [map_one]

theorem blockMatrixTwoByTwoFin_transpose {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d)ᵀ = blk4 aᵀ cᵀ bᵀ dᵀ := by
  simp only [blk4, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

end PositivityTheory.Rg.Sw.Glob.LocCellA

namespace PositivityTheory.Rg.Sw.Glob


open LocCellA in
theorem wEx : WEx := by
  intro D n
  let M : Matrix (Fin (n + n)) (Fin (n + n)) (AE D) := blk4 0 1 (-1) 0
  let Mi : Matrix (Fin (n + n)) (Fin (n + n)) (AE D) := blk4 0 (-1) 1 0
  have h1 : M * Mi = 1 := by simp [M, Mi, block_matrix_mul_comm_ring, block_matrix_diagonal_one_eq_one]
  have h2 : Mi * M = 1 := by simp [M, Mi, block_matrix_mul_comm_ring, block_matrix_diagonal_one_eq_one]
  let u : GL (Fin (n + n)) (AE D) := ⟨M, Mi, h1, h2⟩
  have hu : u ∈ HR (AF D.host.F) D.sp.cm.sig (Jst D n) := by
    show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M * JR (AF D.host.F) (Jst D n) * M = JR (AF D.host.F) (Jst D n)
    have hJ : JR (AF D.host.F) (Jst D n) = M := by
      simp [JR, Jst, M, block_matrix_map, map_neg_one', map_one']
    rw [hJ]
    simp [Formalism.UG.cT, M, block_matrix_map, blockMatrixTwoByTwoFin_transpose, block_matrix_mul_comm_ring, map_neg_one', map_one']
  exact ⟨⟨u, hu⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.InvGroup
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {m n : ℕ}

def IsUe (ε : Fin m → Bool) (X : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  Xᴴ * Matrix.diagonal (sgn ε) + Matrix.diagonal (sgn ε) * X = 0

def xyP (X : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) (b : Bool) : PX m n :=
  ∑ c, C (if b then star (X a c) else X a c) * MvPolynomial.X (c, i, b)

def vfX (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : PX m n :=
  ∑ a, ∑ i, (xyP X a i false * pderiv (a, i, false) P + xyP X a i true * pderiv (a, i, true) P -
    C (c : ℂ) * (xyP X a i false * MvPolynomial.X (a, i, true) + xyP X a i true * MvPolynomial.X (a, i, false)) * P)

def zRe (ε : Fin m → Bool) (a b : Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  (1 / 2 : ℂ) • (Matrix.single a b 1 - (sgn ε a * sgn ε b) • Matrix.single b a 1)

def zIm (ε : Fin m → Bool) (a b : Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  (-(Complex.I / 2) : ℂ) • (Matrix.single a b 1 + (sgn ε a * sgn ε b) • Matrix.single b a 1)


end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SigOKOf
noncomputable section

open scoped Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem cnt_add {m : ℕ} (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (p := fun a => ε a = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at h
  exact h

theorem sigOK_of (hlt : WittLBlt) (heq : WittLBeq) : SigOK := by
  intro D n V s hr hs
  by_contra hne
  push Not at hne
  choose ε fr hfr hng using hne
  obtain ⟨h1, h2, h3⟩ := hr
  have hb : ∀ τ, V.rank - n ≤ cnt (ε τ) true ∧ V.rank - n ≤ cnt (ε τ) false := by
    intro τ
    have hc := cnt_add (ε τ)
    unfold GoodSig at hng
    have := hng τ
    push Not at this
    obtain ⟨a, b, c, d⟩ := this
    constructor <;> omega
  have hS : SigAtLeast D V (V.rank - n) := fun τ =>
    ⟨ε τ, fr τ, (hfr τ).1, (hfr τ).2.1, (hb τ).1, (hb τ).2⟩
  have hw : V.rank - n ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
    rcases Nat.lt_or_ge (2 * (V.rank - n)) V.rank with h | h
    · exact hlt D V _ h hS
    · exact heq D V _ (by omega) hS
  omega

end PositivityTheory.Rg.Sw.Glob
end
end
