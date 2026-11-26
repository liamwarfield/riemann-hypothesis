module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Lemmata.B110.ExistsMoved

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.WeightBoundMultiplicative
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.BetaSesquilinearity

theorem Dw_clm {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] (L : E →L[ℂ] E') (w : List (Bool × B.Mat k r)) (hw : ∀ x ∈ w, B.inLie k r x.2)
    {f : B.Mat k r → E} (hf : B.CkOn (w.length : ℕ∞) (B.GV k r) f) :
    ∀ g ∈ B.GV k r, Dw w (fun h => L (f h)) g = L (Dw w f g) := by
  induction w with
  | nil => intro g _; rfl
  | cons x w ih =>
    intro g hg
    have hw' : ∀ y ∈ w, B.inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hx : B.inLie k r x.2 := hw x (by simp)
    have hle : ((w.length : ℕ) : ℕ∞) ≤ ((x :: w).length : ℕ) := by exact_mod_cast Nat.le_succ _
    show Dx x (Dw w (fun h => L (f h))) g = L (Dx x (Dw w f) g)
    rw [Dx_congr hx (ih hw' (sCkOn_mono hle hf)) g hg]
    have hc : B.CkOn 1 (B.GV k r) (Dw w f) := by
      apply CkOn_Dw hw'
      have : (1 : ℕ∞) + (w.length : ℕ∞) = ((x :: w).length : ℕ) := by simp; ring
      rw [this]; exact hf
    have h1 := CkOn_diff hx hc hg hg
    have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    rw [Dx_eq]
    exact h2.deriv

theorem ckOn_of_contDiff {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞}
    {f : B.Mat k r → E} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) : B.CkOn m (B.GV k r) f := by
  intro g₀ _
  exact ⟨Set.univ, f, isOpen_univ, Set.mem_univ _,
    (hf.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn, fun _ _ _ => rfl⟩

theorem sum_cost_le {k r : ℕ} (c : B.Mat k r → ℕ) {u v u₁ v₁ : List (B.Mat k r)} (hu : u₁.Sublist u)
    (hv : v₁.Sublist v) : (((u₁ ++ v₁).map c).sum : ℝ) ≤ (((u ++ v).map c).sum : ℝ) := by
  have h := ((hu.append hv).map c).sum_le_sum (fun _ _ => Nat.zero_le _)
  exact_mod_cast h

theorem weight_bound_multiplicative : WBmul := by
  intro k r φ₁ φ₂ c₁ c₂ n C₁ C₂ e₁ e₂ h₁ h₂ hw₁ hw₂
  refine ⟨2 ^ n * (|C₁| * |C₂|), fun u v hu hv hl g hg => ?_⟩
  set a : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun h => ContinuousLinearMap.mul ℂ ℂ (φ₁ h) with ha
  have hfun : (fun h => φ₁ h * φ₂ h) = ap a φ₂ := by funext h; simp [ap, ha]
  have hlie := lie_LR (unit_lie hu) (unit_lie hv)
  have hca : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a :=
    ((ContinuousLinearMap.mul ℂ ℂ).restrictScalars ℝ).contDiff.comp h₁
  have hP : Pr (∅ : Set (B.Mat k r)) (B.GV k r) ((wL u ++ wR v).length : ℕ) a φ₂ :=
    ⟨ckOn_of_contDiff hca, ckOn_of_contDiff h₂, fun _ _ h => absurd h (Set.notMem_empty _)⟩
  have hp := gN_pos hg
  have hg1 := gN_ge_one hg
  set S : ℝ := (((u ++ v).map c₁).sum : ℝ) with hS
  set T : ℝ := (((u ++ v).map c₂).sum : ℝ) with hT
  have hb := leib_bound isOpen_empty (fun g hg => Or.inr hg) g hg
    (|C₁| * |C₂| * B.gN g ^ (e₁ + e₂ + (S + T))) (wL u ++ wR v) a φ₂ hlie hP (by
      intro w₁ w₂ hs₁ hs₂ _
      obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR hs₁
      obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR hs₂
      have hl₁ : u₁.length + v₁.length ≤ n := by
        have := hu₁.length_le; have := hv₁.length_le; omega
      have hl₂ : u₂.length + v₂.length ≤ n := by
        have := hu₂.length_le; have := hv₂.length_le; omega
      have hu₁' : ∀ X ∈ u₁, B.unitLie k r X := fun X hX => hu X (hu₁.subset hX)
      have hv₁' : ∀ X ∈ v₁, B.unitLie k r X := fun X hX => hv X (hv₁.subset hX)
      have hu₂' : ∀ X ∈ u₂, B.unitLie k r X := fun X hX => hu X (hu₂.subset hX)
      have hv₂' : ∀ X ∈ v₂, B.unitLie k r X := fun X hX => hv X (hv₂.subset hX)
      have ea : Dw (wL u₁ ++ wR v₁) a g = ContinuousLinearMap.mul ℂ ℂ (Dw (wL u₁ ++ wR v₁) φ₁ g) :=
        Dw_clm (ContinuousLinearMap.mul ℂ ℂ) _ (lie_LR (unit_lie hu₁') (unit_lie hv₁'))
          (ckOn_of_contDiff h₁) g hg
      have b1 : ‖Dw (wL u₁ ++ wR v₁) a g‖ ≤ |C₁| * B.gN g ^ (e₁ + S) := by
        rw [ea]
        refine (ContinuousLinearMap.opNorm_mul_apply_le _ _ _).trans ?_
        rw [← dLR_eq]
        refine (hw₁ u₁ v₁ hu₁' hv₁' hl₁ g hg).trans ?_
        refine mul_le_mul (le_abs_self _) ?_ (by positivity) (abs_nonneg _)
        exact Real.rpow_le_rpow_of_exponent_le hg1 (by linarith [sum_cost_le c₁ hu₁ hv₁])
      have b2 : ‖Dw (wL u₂ ++ wR v₂) φ₂ g‖ ≤ |C₂| * B.gN g ^ (e₂ + T) := by
        rw [← dLR_eq]
        refine (hw₂ u₂ v₂ hu₂' hv₂' hl₂ g hg).trans ?_
        refine mul_le_mul (le_abs_self _) ?_ (by positivity) (abs_nonneg _)
        exact Real.rpow_le_rpow_of_exponent_le hg1 (by linarith [sum_cost_le c₂ hu₂ hv₂])
      calc ‖Dw (wL u₁ ++ wR v₁) a g‖ * ‖Dw (wL u₂ ++ wR v₂) φ₂ g‖
          ≤ (|C₁| * B.gN g ^ (e₁ + S)) * (|C₂| * B.gN g ^ (e₂ + T)) :=
            mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
        _ = |C₁| * |C₂| * B.gN g ^ (e₁ + e₂ + (S + T)) := by
            rw [show e₁ + e₂ + (S + T) = (e₁ + S) + (e₂ + T) by ring, Real.rpow_add hp (e₁ + S) (e₂ + T)]; ring)
  have hST : ((((u ++ v).map (c₁ + c₂)).sum : ℕ) : ℝ) = S + T := by
    rw [hS, hT, ← Nat.cast_add, ← List.sum_map_add]; rfl
  rw [hfun, dLR_eq, hST]
  have hpow : (2 : ℝ) ^ (wL u ++ wR v).length ≤ 2 ^ n := by
    rw [len_LR]; exact pow_le_pow_right₀ (by norm_num) hl
  calc ‖Dw (wL u ++ wR v) (ap a φ₂) g‖ ≤ 2 ^ (wL u ++ wR v).length * (|C₁| * |C₂| * B.gN g ^ (e₁ + e₂ + (S + T))) := hb
    _ ≤ 2 ^ n * (|C₁| * |C₂| * B.gN g ^ (e₁ + e₂ + (S + T))) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = 2 ^ n * (|C₁| * |C₂|) * B.gN g ^ (e₁ + e₂ + (S + T)) := by ring

end PI.UnitaryCorollaryDerivatives
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.GfWBOf
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.BetaSesquilinearity

theorem gfWB_of (h1 : GfPoly) (h2 : PolyB) (h3 : CompR) : GfWB := by
  intro k r z z' χε ε n hχ
  obtain ⟨hχs, hχd, -⟩ := hχ
  obtain ⟨hsmC, hwb⟩ :=
    h2 k r (2 * (r + 1)) (fun g => ((Gf k r z z' g : ℝ) : ℂ)) (h1 k r z z')
  have hsmR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat k r => Gf k r z z' g) := by
    have h := Complex.reCLM.contDiff.comp hsmC
    simpa [Function.comp_def] using h
  refine ⟨?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (hχs.comp hsmR)
  · obtain ⟨C₀, hC₀⟩ := hwb n
    refine h3 k r (fun g => Gf k r z z' g) χε (fun _ => 2 * (r + 1)) n C₀ hsmR hχs hχd ?_
    intro u v hu hv hlen hne g hg
    have hb := hC₀ u v hu hv hlen g hg
    have h1g : 1 ≤ B.gN g := gN_ge_one hg
    have hexp : ((2 * (r + 1) : ℕ) : ℝ) + ((((u ++ v).map (fun _ => (0 : ℕ))).sum : ℕ) : ℝ) ≤
        ((((u ++ v).map (fun _ => 2 * (r + 1))).sum : ℕ) : ℝ) := by
      have hl : 1 ≤ (u ++ v).length := List.length_pos_iff.mpr hne
      simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_zero, Nat.cast_zero,
        add_zero]
      exact_mod_cast Nat.le_mul_of_pos_left _ hl
    have hpos : 0 < B.gN g ^ (((2 * (r + 1) : ℕ) : ℝ) +
        ((((u ++ v).map (fun _ => (0 : ℕ))).sum : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos h1g) _
    have hC : 0 ≤ C₀ := (mul_nonneg_iff_of_pos_right hpos).mp ((norm_nonneg _).trans hb)
    exact hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1g hexp) hC)

end PI.UnitaryCorollaryDerivatives
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.DjPoly
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def djVarMat (k j ρ : ℕ) :
    Matrix (Fin j) (Fin j)
      (MvPolynomial ((Fin (2 * (j + ρ) + k + 1) × Fin (2 * (j + ρ) + k + 1)) ⊕
        (Fin (2 * (j + ρ) + k + 1) × Fin (2 * (j + ρ) + k + 1))) ℂ) :=
  fun a b => MvPolynomial.X (Sum.inl (⟨2 * (j + ρ) + k - a.val, by omega⟩, ⟨b.val, by omega⟩))

theorem isPolyDeg_determinant_derivative (k j ρ : ℕ) : IsPolyDeg j (DjU k j ρ) := by
  refine ⟨∑ σ : Equiv.Perm (Fin j),
      MvPolynomial.C ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) * ∏ i, djVarMat k j ρ (σ i) i, ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
    refine Finset.sup_le fun σ _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    calc (∑ i : Fin j, (djVarMat k j ρ (σ i) i).totalDegree) ≤ ∑ _i : Fin j, 1 := by
          refine Finset.sum_le_sum fun i _ => ?_
          simp [djVarMat, MvPolynomial.totalDegree_X]
      _ = j := by simp
  · intro g
    rw [DjU, Matrix.det_apply']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_prod, MvPolynomial.eval_C]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [djVarMat, Zh, MvPolynomial.eval_X]

theorem determinant_derivative_polynomial : DjPoly := fun k j ρ => isPolyDeg_determinant_derivative k j ρ

end PI.UnitaryCorollaryDerivatives
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.DjCurveA
open Matrix

noncomputable section

namespace PI.UnitaryCorollaryDerivatives.DjC

section Gen

variable {N j : ℕ}

def Pres (S : Set (Fin N)) (Y : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ c b : Fin N, b ∈ S → c ∉ S → Y c b = 0

theorem pres_mul {S : Set (Fin N)} {X Y : Matrix (Fin N) (Fin N) ℂ} (hX : Pres S X) (hY : Pres S Y) :
    Pres S (X * Y) := by
  intro c b hb hc
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : m ∈ S
  · rw [hX c m hm hc, zero_mul]
  · rw [hY m b hb hm, mul_zero]

theorem pres_pow {S : Set (Fin N)} {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Pres S Y) (n : ℕ) :
    Pres S (Y ^ n) := by
  induction n with
  | zero =>
    intro c b hb hc
    rw [pow_zero, Matrix.one_apply_ne]
    rintro rfl; exact hc hb
  | succ n ih => rw [pow_succ]; exact pres_mul ih hY

theorem pres_smul {S : Set (Fin N)} {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Pres S Y) (z : ℂ) :
    Pres S (z • Y) := by
  intro c b hb hc
  rw [Matrix.smul_apply, hY c b hb hc, smul_zero]

theorem pres_neg {S : Set (Fin N)} {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Pres S Y) : Pres S (-Y) := by
  intro c b hb hc
  rw [Matrix.neg_apply, hY c b hb hc, neg_zero]

open scoped Matrix.Norms.Operator in
theorem pres_exp {S : Set (Fin N)} {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Pres S Y) :
    Pres S (NormedSpace.exp Y) := by
  intro c b hb hc
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h1 := Pi.hasSum.1 h c
  have h2 := Pi.hasSum.1 h1 b
  have h3 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • Y ^ n) c b) 0 := by
    have : (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • Y ^ n) c b) = fun _ => 0 := by
      funext n; rw [Matrix.smul_apply, pres_pow hY n c b hb hc, smul_zero]
    rw [this]; exact hasSum_zero
  exact h2.unique h3

def sub (e : Fin j ↪ Fin N) (E : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin j) (Fin j) ℂ :=
  Matrix.of fun a b => E (e a) (e b)

end Gen

section DetExp

variable {n : Type} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry (X : Matrix n n ℂ) (i j : n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix n n ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_det_of_one (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 := by
  first | exact Bl.b110.goal1 .. | (apply Bl.b110.goal1 <;> assumption) | (intros; apply Bl.b110.goal1 <;> assumption) | (apply @Bl.b110.goal1 <;> assumption) | (intros; apply @Bl.b110.goal1 <;> assumption) | (apply @Bl.b110.goal1 <;> first | assumption | infer_instance) | exact @Bl.b110.goal1 n ‹_› ‹_› A A' h0 h | exact @Bl.b110.goal1 n ‹_› ‹_› A A' h0 | exact @Bl.b110.goal1 n ‹_› ‹_› A A' | exact @Bl.b110.goal1 n ‹_› ‹_› A | exact @Bl.b110.goal1 n ‹_› ‹_› | exact @Bl.b110.goal1 n ‹_› | exact @Bl.b110.goal1 n

end DetExp

theorem mul_hom_exp (φ : ℝ → ℂ) (c : ℂ) (hmul : ∀ s t, φ (s + t) = φ s * φ t) (h1 : φ 0 = 1)
    (h0 : HasDerivAt φ c 0) (t : ℝ) : φ t = Complex.exp (t * c) := by
  have hd : ∀ t, HasDerivAt φ (φ t * c) t := by
    intro t
    have h1' : HasDerivAt (fun s => φ (s - t)) c t := by
      have h00 := h0
      rw [← sub_self t] at h00
      exact h00.comp_sub_const t t
    have h2 := h1'.const_mul (φ t)
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show φ s = φ t * φ (s - t)
    rw [← hmul]; congr 1; ring
  let ψ : ℝ → ℂ := fun t => φ t * Complex.exp (-((t : ℂ) * c))
  have hψ : ∀ t, HasDerivAt ψ 0 t := by
    intro t
    have e0 : HasDerivAt (fun t : ℝ => -((t : ℂ) * c)) (-(1 * c)) t := by
      have h := ((hasDerivAt_id t).ofReal_comp.mul_const c).fun_neg
      simpa using h
    have e1 := e0.cexp
    have h3 := (hd t).fun_mul e1
    have h4 : φ t * c * Complex.exp (-((t : ℂ) * c)) +
        φ t * (Complex.exp (-((t : ℂ) * c)) * -(1 * c)) = 0 := by ring
    rw [h4] at h3
    exact h3
  have hc := is_const_of_deriv_eq_zero (fun t => (hψ t).differentiableAt) (fun t => (hψ t).deriv) t 0
  simp only [ψ, h1, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at hc
  rw [Complex.exp_neg] at hc
  exact eq_of_mul_inv_eq_one hc

end PI.UnitaryCorollaryDerivatives.DjC
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.GfPoly
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.GfPolyA
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

variable {N : ℕ}

theorem pd_mono {a b : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : a ≤ b) (hP : IsPolyDeg a P) :
    IsPolyDeg b P := by
  obtain ⟨q, hq, he⟩ := hP
  exact ⟨q, hq.trans h, he⟩

theorem pd_const (c : ℂ) : IsPolyDeg (N := N) 0 (fun _ => c) :=
  ⟨MvPolynomial.C c, by simp, fun g => by simp⟩

theorem pd_add {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) (hQ : IsPolyDeg a Q) :
    IsPolyDeg a (fun g => P g + Q g) := by
  obtain ⟨p, hp, hpe⟩ := hP
  obtain ⟨q, hq, hqe⟩ := hQ
  exact ⟨p + q, (MvPolynomial.totalDegree_add p q).trans (max_le hp hq), fun g => by simp [hpe, hqe]⟩

theorem pd_sub {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) (hQ : IsPolyDeg a Q) :
    IsPolyDeg a (fun g => P g - Q g) := by
  obtain ⟨p, hp, hpe⟩ := hP
  obtain ⟨q, hq, hqe⟩ := hQ
  exact ⟨p - q, (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq), fun g => by simp [hpe, hqe]⟩

theorem pd_mul {a b : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) (hQ : IsPolyDeg b Q) :
    IsPolyDeg (a + b) (fun g => P g * Q g) := by
  obtain ⟨p, hp, hpe⟩ := hP
  obtain ⟨q, hq, hqe⟩ := hQ
  exact ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (add_le_add hp hq), fun g => by simp [hpe, hqe]⟩

theorem pd_cmul {a : ℕ} (c : ℂ) {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) :
    IsPolyDeg a (fun g => c * P g) := by
  have h := pd_mul (pd_const c) hP
  rwa [zero_add] at h

theorem pd_mulc {a : ℕ} (c : ℂ) {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) :
    IsPolyDeg a (fun g => P g * c) := by
  have h := pd_mul hP (pd_const c)
  rwa [add_zero] at h

theorem pd_sum {ι : Type*} (s : Finset ι) {a : ℕ} (P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ)
    (h : ∀ i ∈ s, IsPolyDeg a (P i)) : IsPolyDeg a (fun g => ∑ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact pd_mono (Nat.zero_le a) (pd_const 0)
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact pd_add (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem pd_prod {ι : Type*} (s : Finset ι) (d : ι → ℕ) (P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ)
    (h : ∀ i ∈ s, IsPolyDeg (d i) (P i)) : IsPolyDeg (∑ i ∈ s, d i) (fun g => ∏ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact pd_const 1
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    exact pd_mul (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem pd_X (a b : Fin N) : IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => g a b) :=
  ⟨MvPolynomial.X (Sum.inl (a, b)), by simp [MvPolynomial.totalDegree_X], fun g => by simp⟩

theorem pd_Xs (a b : Fin N) : IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (g a b)) :=
  ⟨MvPolynomial.X (Sum.inr (a, b)), by simp [MvPolynomial.totalDegree_X], fun g => by simp⟩

theorem pd_det (n : ℕ) (M : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i j, IsPolyDeg 1 (fun g => M g i j)) : IsPolyDeg n (fun g => (M g).det) := by
  simp only [Matrix.det_apply']
  refine pd_sum _ _ fun σ _ => pd_cmul _ ?_
  have h2 := pd_prod (Finset.univ : Finset (Fin n)) (fun _ => 1) (fun i g => M g (σ i) i)
    (fun i _ => h (σ i) i)
  simpa using h2

theorem pd_det_star (n : ℕ) (M : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i j, IsPolyDeg 1 (fun g => star (M g i j))) : IsPolyDeg n (fun g => star (M g).det) := by
  have e : (fun g => star (M g).det) = fun g => ((M g).map (starRingEnd ℂ)).det := by
    funext g
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, starRingEnd_apply]
  rw [e]
  exact pd_det n _ fun i j => h i j

theorem pd_herm (H : Matrix (Fin N) (Fin N) ℂ) (v w : Fin N → ℂ) :
    IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => herm H (g *ᵥ v) w) := by
  simp only [herm, dotProduct, mulVec]
  exact pd_sum _ _ fun i _ => pd_cmul _ (pd_sum _ _ fun j _ => pd_cmul _
    (pd_sum _ _ fun l _ => pd_mulc _ (pd_X j l)))

theorem pd_herm_star (H : Matrix (Fin N) (Fin N) ℂ) (v w : Fin N → ℂ) :
    IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (herm H (g *ᵥ v) w)) := by
  simp only [herm, dotProduct, mulVec, star_sum, star_mul']
  exact pd_sum _ _ fun i _ => pd_cmul _ (pd_sum _ _ fun j _ => pd_cmul _
    (pd_sum _ _ fun l _ => isPolyDeg_one_conj_entry_mul j l))
where
  isPolyDeg_one_conj_entry_mul (j l : Fin N) : IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (g j l) * star (v l)) :=
    pd_mulc _ (pd_Xs j l)

end PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure
end
end

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PolynomialDegreeClosure in
theorem generating_function_polynomial : GfPoly := by
  intro k r z z'
  have hD : ∀ l : Fin (r + 2), IsPolyDeg l.val (fun g : B.Mat k r => Dmin k r z z' g l) := fun l =>
    pd_det l.val (fun g => (Zhat k r z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
      (Fin.castLE (Nat.le_of_lt_succ l.isLt))) fun i j =>
      pd_herm (Hpk k r) (fvec k r z' (Fin.castLE (Nat.le_of_lt_succ l.isLt) j))
        (fvec k r z (Fin.castLE (Nat.le_of_lt_succ l.isLt) i))
  have hDs : ∀ l : Fin (r + 2), IsPolyDeg l.val (fun g : B.Mat k r => star (Dmin k r z z' g l)) := fun l =>
    pd_det_star l.val (fun g => (Zhat k r z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
      (Fin.castLE (Nat.le_of_lt_succ l.isLt))) fun i j =>
      pd_herm_star (Hpk k r) (fvec k r z' (Fin.castLE (Nat.le_of_lt_succ l.isLt) j))
        (fvec k r z (Fin.castLE (Nat.le_of_lt_succ l.isLt) i))
  have e : (fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) = fun g =>
      Dmin k r z z' g (Fin.last (r + 1)) * star (Dmin k r z z' g (Fin.last (r + 1))) -
      ((Tz k r z * Tz k r z' : ℝ) : ℂ) *
        (Dmin k r z z' g ⟨r, by omega⟩ * star (Dmin k r z z' g ⟨r, by omega⟩)) := by
    funext g
    simp only [Gf]
    push_cast
    rw [← Complex.mul_conj, ← Complex.mul_conj]
    rfl
  rw [e]
  refine pd_sub (pd_mono ?_ (pd_mul (hD _) (hDs _))) (pd_mono ?_ (pd_cmul _ (pd_mul (hD _) (hDs _))))
  · omega
  · omega

end PI.UnitaryCorollaryDerivatives
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CompRA
open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace PI.UnitaryCorollaryDerivatives.CRH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma dif {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f := by
  first
  | exact hf.differentiable (by simp)
  | exact hf.differentiable le_top
  | exact hf.differentiable (by norm_num)

lemma hd_Dx (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) (g : Mat k r) :
    HasDerivAt (fun t : ℝ => f (crv x g t)) (Dx x f g) 0 := by
  rw [Dx_eq]
  exact ((hf _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)).differentiableAt.hasDerivAt

lemma Dx_fd (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) :
    Dx x f = fun g => fderiv ℝ f g (dirL x g) := by
  funext g
  have h := (hf (crv x g 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)
  rw [crv_zero] at h
  rw [dirL_apply]
  exact (hd_Dx x hf g).unique h

lemma cd_Dx (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dx x f) := by
  rw [Dx_fd x (dif hf)]
  first
  | exact (hf.fderiv_right (m := ∞) le_rfl).clm_apply (dirL x).contDiff
  | exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply (dirL x).contDiff
  | exact (hf.fderiv_right (m := ∞) (by norm_num)).clm_apply (dirL x).contDiff

lemma cd_Dw (w : List (Bool × Mat k r)) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Dw w f) := by
  induction w with
  | nil => exact hf
  | cons x w ih => exact cd_Dx x ih

lemma Dx_add' (x : Bool × Mat k r) {a b : Mat k r → ℂ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    Dx x (fun g => a g + b g) = fun g => Dx x a g + Dx x b g := by
  funext g
  exact (hd_Dx x (ha.add hb) g).unique ((hd_Dx x ha g).add (hd_Dx x hb g))

lemma Dw_add' (w : List (Bool × Mat k r)) {a b : Mat k r → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    Dw w (fun g => a g + b g) = fun g => Dw w a g + Dw w b g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => a g + b g) = _
    rw [ih]
    exact Dx_add' x (dif (cd_Dw w ha)) (dif (cd_Dw w hb))

lemma Dx_mul' (x : Bool × Mat k r) {a b : Mat k r → ℂ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    Dx x (fun g => a g * b g) = fun g => Dx x a g * b g + a g * Dx x b g := by
  funext g
  have h0 : crv x g 0 = g := by simp [crv]
  have h := (hd_Dx x ha g).mul (hd_Dx x hb g)
  rw [h0] at h
  exact (hd_Dx x (ha.mul hb) g).unique h

def Spl (w w₁ w₂ : List (Bool × Mat k r)) : Prop := w₁.Sublist w ∧ w₂.Sublist w ∧ (w₁ ++ w₂).Perm w

private lemma Dw_append_singleton (w : List (Bool × Mat k r)) (x : Bool × Mat k r) (f : Mat k r → ℂ) :
    Dw (w ++ [x]) f = Dw w (Dx x f) := by
  unfold Dw
  rw [List.foldr_append]
  rfl

lemma leibB (g : Mat k r) (M : ℝ) (w : List (Bool × Mat k r)) :
    ∀ a b : Mat k r → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      (∀ w₁ w₂, Spl w w₁ w₂ → ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) →
      ‖Dw w (fun g => a g * b g) g‖ ≤ 2 ^ w.length * M := by
  induction w using List.reverseRecOn with
  | nil =>
    intro a b ha hb hM
    simpa [Dw, norm_mul] using hM [] [] (by unfold Spl; simp)
  | append_singleton w x ih =>
    intro a b ha hb hM
    rw [Dw_append_singleton, Dx_mul' x (dif ha) (dif hb),
      Dw_add' w ((cd_Dx x ha).mul hb) (ha.mul (cd_Dx x hb))]
    have h1 := ih (Dx x a) b (cd_Dx x ha) hb (fun w₁ w₂ hs => by
      obtain ⟨s1, s2, p⟩ := hs
      have e : w₁ ++ [x] ++ w₂ = w₁ ++ x :: w₂ := by simp
      have hp : (w₁ ++ [x] ++ w₂).Perm (w ++ [x]) := by
        rw [e]
        exact List.perm_middle.trans ((p.cons x).trans (List.perm_append_singleton x w).symm)
      have := hM (w₁ ++ [x]) w₂ (by
        unfold Spl
        exact ⟨s1.append (List.Sublist.refl _), s2.trans (List.sublist_append_left _ _), hp⟩)
      rwa [Dw_append_singleton] at this)
    have h2 := ih a (Dx x b) ha (cd_Dx x hb) (fun w₁ w₂ hs => by
      obtain ⟨s1, s2, p⟩ := hs
      have hp : (w₁ ++ (w₂ ++ [x])).Perm (w ++ [x]) := by
        rw [← List.append_assoc]
        exact p.append_right [x]
      have := hM w₁ (w₂ ++ [x]) (by
        unfold Spl
        exact ⟨s1.trans (List.sublist_append_left _ _), s2.append (List.Sublist.refl _), hp⟩)
      rwa [Dw_append_singleton] at this)
    calc _ ≤ ‖Dw w (fun g => Dx x a g * b g) g‖ + ‖Dw w (fun g => a g * Dx x b g) g‖ := norm_add_le _ _
      _ ≤ 2 ^ w.length * M + 2 ^ w.length * M := add_le_add h1 h2
      _ = 2 ^ (w ++ [x]).length * M := by
        rw [List.length_append, List.length_singleton, pow_succ]
        ring

end PI.UnitaryCorollaryDerivatives.CRH
end
end
