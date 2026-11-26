module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmBorderES
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AddIntG
public import Formalism.YangianSpanCharacter.YangianRTTProofs.RttRelation
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.LevelGroupUnitaryHermitian
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelImageArithmetic.GlevImageOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.SecondCapelliMinorLevel
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRuleLeft
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusConjugationRule.WColOther
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTPres
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmCapComm
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnHermHaar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylCellRange.ReflectionMultiplicationOnBigCell
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmSandwich

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRuleTorus
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusConjugationRule.SecondHermitianPartDiagonal
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.QnRT

variable {k r : ℕ}

private lemma tau_val_lemma (i : Fin (2 * r + k + 1)) :
    (WeylGroupFacts.tau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl

private lemma tau_tau_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.tau k r (WeylGroupFacts.tau k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [tau_val_lemma]
  split_ifs <;> omega

private lemma sgn_tau_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r (WeylGroupFacts.tau k r i) = WeylGroupFacts.sgn k r i := by
  have hi := i.isLt
  unfold WeylGroupFacts.sgn
  simp only [tau_val_lemma]
  split_ifs <;> first | rfl | omega

private lemma sgn_sq_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r i * WeylGroupFacts.sgn k r i = 1 := by
  unfold WeylGroupFacts.sgn
  split_ifs <;> norm_num

private lemma hpk_eq_lemma (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = WeylGroupFacts.tau k r i then WeylGroupFacts.sgn k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk WeylGroupFacts.sgn
  simp only [Fin.ext_iff, tau_val_lemma]
  split_ifs <;> first | rfl | omega | norm_num

private lemma hpk_sq_lemma : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [hpk_eq_lemma, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, tau_tau_lemma, sgn_tau_lemma]
  by_cases h : i = j
  · subst h
    simp [sgn_sq_lemma]
  · simp [h, Ne.symm h]

lemma hpk_inv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hpk_sq_lemma

private lemma hpk_col_lemma (x y : Fin (2 * r + k + 1)) :
    Hpk k r x y = if x = WeylGroupFacts.tau k r y then WeylGroupFacts.sgn k r y else 0 := by
  rw [hpk_eq_lemma]
  by_cases h : x = WeylGroupFacts.tau k r y
  · subst h
    simp [tau_tau_lemma, sgn_tau_lemma]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    rw [h', tau_tau_lemma]

private lemma single_ct_lemma (a b : Fin (2 * r + k + 1)) (c : ℂ) :
    (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
  ext x y
  rw [Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.single_apply]
  by_cases h : a = y ∧ b = x
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), star_zero]

private lemma conj_single_lemma (A B : Mx k r) (a b : Fin (2 * r + k + 1)) (c : ℂ)
    (p q : Fin (2 * r + k + 1)) : (A * Matrix.single a b c * B) p q = A p a * c * B b q := by
  simp only [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma conj_single (x : Fin (2 * r + k + 1)) :
    Hpk k r * (single x x (1 : ℂ))ᴴ * Hpk k r =
      single (WeylGroupFacts.tau k r x) (WeylGroupFacts.tau k r x) 1 := by
  rw [single_ct_lemma, star_one]
  ext p q
  rw [conj_single_lemma, hpk_eq_lemma, hpk_col_lemma, Matrix.single_apply]
  by_cases hp : p = WeylGroupFacts.tau k r x
  · subst hp
    by_cases hq : q = WeylGroupFacts.tau k r x
    · subst hq
      simp [tau_tau_lemma, sgn_tau_lemma, sgn_sq_lemma]
    · have hq' : x ≠ WeylGroupFacts.tau k r q := fun h => hq (by rw [h, tau_tau_lemma])
      simp [hq', Ne.symm hq]
  · have hp' : x ≠ WeylGroupFacts.tau k r p := fun h => hp (by rw [h, tau_tau_lemma])
    simp [hp', Ne.symm hp]

lemma inv_conj_single (x : Fin (2 * r + k + 1)) :
    (Hpk k r)⁻¹ * (single x x (1 : ℂ))ᴴ * Hpk k r =
      single (WeylGroupFacts.tau k r x) (WeylGroupFacts.tau k r x) 1 := by
  rw [hpk_inv, conj_single]

def dz (l : Fin r) (κ κ' : ℂ) : Mx k r :=
  diagonal (fun p => if p = eI k r l then κ else if p = esI k r l then κ' else 0)

lemma X1_eq (l : Fin r) : hpart1 (Hpk k r) (single (eI k r l) (eI k r l) 1) =
    dz l ((1 / 2 : ℝ) : ℂ) (-((1 / 2 : ℝ) : ℂ)) := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold hpart1 dz
  rw [inv_conj_single, tau_e]
  ext p q
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  by_cases hpq : p = q
  · subst hpq
    by_cases h1 : p = eI k r l
    · subst h1
      simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
    · by_cases h2 : p = esI k r l
      · subst h2
        simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · have a1 : ¬ (eI k r l = p ∧ eI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    have a2 : ¬ (esI k r l = p ∧ esI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    simp [a1, a2, hpq]

lemma depthNumbers_threshold_eq (l : Fin r) : hpart2 (Hpk k r) (single (eI k r l) (eI k r l) 1) =
    dz l (((-1 / 2 : ℝ) : ℂ) * Complex.I) (((-1 / 2 : ℝ) : ℂ) * Complex.I) := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold hpart2 dz
  rw [inv_conj_single, tau_e]
  ext p q
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  by_cases hpq : p = q
  · subst hpq
    by_cases h1 : p = eI k r l
    · subst h1
      simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
    · by_cases h2 : p = esI k r l
      · subst h2
        simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · have a1 : ¬ (eI k r l = p ∧ eI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    have a2 : ¬ (esI k r l = p ∧ esI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    simp [a1, a2, hpq]

lemma first_hermitian_part_diagonal (l : Fin r) : hpart1 (Hpk k r) (single (esI k r l) (esI k r l) 1) =
    dz l (-((1 / 2 : ℝ) : ℂ)) ((1 / 2 : ℝ) : ℂ) := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold hpart1 dz
  rw [inv_conj_single, tau_es]
  ext p q
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  by_cases hpq : p = q
  · subst hpq
    by_cases h1 : p = eI k r l
    · subst h1
      simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
    · by_cases h2 : p = esI k r l
      · subst h2
        simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · have a1 : ¬ (eI k r l = p ∧ eI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    have a2 : ¬ (esI k r l = p ∧ esI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    simp [a1, a2, hpq]

lemma second_hermitian_part_diagonal (l : Fin r) : hpart2 (Hpk k r) (single (esI k r l) (esI k r l) 1) =
    dz l (((-1 / 2 : ℝ) : ℂ) * Complex.I) (((-1 / 2 : ℝ) : ℂ) * Complex.I) := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold hpart2 dz
  rw [inv_conj_single, tau_es]
  ext p q
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  by_cases hpq : p = q
  · subst hpq
    by_cases h1 : p = eI k r l
    · subst h1
      simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
    · by_cases h2 : p = esI k r l
      · subst h2
        simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · have a1 : ¬ (eI k r l = p ∧ eI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    have a2 : ¬ (esI k r l = p ∧ esI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    simp [a1, a2, hpq]

lemma w_decomp (l : Fin r) (b : ℂ) :
    w1 k r l b = w1 k r l 0 + b • single (esI k r l) (eI k r l) 1 +
      (star b)⁻¹ • single (eI k r l) (esI k r l) 1 := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  ext p q
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  unfold w1
  by_cases hp1 : p = eI k r l
  · subst hp1
    by_cases hq2 : q = esI k r l
    · subst hq2
      simp [hne, hne.symm]
    · simp [hne, hne.symm, hq2, Ne.symm hq2]
  · by_cases hp2 : p = esI k r l
    · subst hp2
      by_cases hq1 : q = eI k r l
      · subst hq1
        simp [hne, hne.symm]
      · simp [hne, hne.symm, hq1, Ne.symm hq1]
    · simp [hp1, hp2, Ne.symm hp1, Ne.symm hp2]

lemma w_diff (l : Fin r) (g₁ : Mx k r) (c : Fin r → ℂ) (hc : c l ≠ 0) :
    DifferentiableAt ℝ (fun c' : Fin r → ℂ => w1 k r l (c' l) * g₁) c := by
  have hfun : (fun c' : Fin r → ℂ => w1 k r l (c' l) * g₁) = fun c' : Fin r → ℂ =>
      (w1 k r l 0 + c' l • single (esI k r l) (eI k r l) (1 : ℂ) +
        (star (c' l))⁻¹ • single (eI k r l) (esI k r l) (1 : ℂ)) * g₁ := by
    funext c'
    rw [w_decomp]
  rw [hfun]
  have h1 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => c' l) c := differentiableAt_apply l c
  have hs : DifferentiableAt ℝ (fun c' : Fin r → ℂ => star (c' l)) c :=
    Complex.conjCLE.differentiableAt.comp c h1
  have h2 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => (star (c' l))⁻¹) c :=
    hs.inv (by simpa using hc)
  have hin : DifferentiableAt ℝ (fun c' : Fin r → ℂ => (w1 k r l 0 + c' l • single (esI k r l) (eI k r l) (1 : ℂ) +
        (star (c' l))⁻¹ • single (eI k r l) (esI k r l) (1 : ℂ) : Mx k r)) c :=
    ((differentiableAt_const _).add (h1.smul_const _)).add (h2.smul_const _)
  let Lm : Mx k r →L[ℝ] Mx k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g₁)
  exact Lm.differentiableAt.comp c hin

lemma phi_diff {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r) (D : Set (Mx k r))
    (f : Mx k r → E) (hf : SmoothLev k r l.castSucc D f) (c : Fin r → ℂ) (hc : c l ≠ 0)
    (g₁ : Mx k r) (hg₁ : g₁ ∈ Glev k r l.succ) (hD : w1 k r l (c l) * g₁ ∈ D) :
    DifferentiableAt ℝ (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) c := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf _ ⟨w_mul_mem l (c l) hc g₁ hg₁, hD⟩
  have hγ := w_diff l g₁ c hc
  have hFd : DifferentiableAt ℝ F (w1 k r l (c l) * g₁) :=
    (hF.differentiableOn (by first | simp | exact le_top | norm_num)).differentiableAt
      (hU.mem_nhds hgU)
  have hev1 : ∀ᶠ c' in 𝓝 c, w1 k r l (c' l) * g₁ ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)
  have hev2 : ∀ᶠ c' in 𝓝 c, c' l ≠ 0 := (continuous_apply l).continuousAt.eventually_ne hc
  have hev := hev1.and hev2
  refine (hFd.comp c hγ).congr_of_eventuallyEq ?_
  filter_upwards [hev] with c' hc'
  exact hfF _ hc'.1 (w_mul_mem l (c' l) hc'.2 g₁ hg₁)

lemma mul_exp_dz (l : Fin r) (a κ : ℂ) (g₁ : Mx k r) (hg₁ : g₁ ∈ Glev k r l.succ) (t : ℝ) :
    w1 k r l a * g₁ * NormedSpace.exp ((t : ℂ) • dz l κ (-star κ)) =
      w1 k r l (a * Complex.exp (t * κ)) * g₁ := by
  have hsm : (t : ℂ) • dz l κ (-star κ) = (diagonal (fun p => if p = eI k r l then (t : ℂ) * κ
      else if p = esI k r l then (t : ℂ) * -star κ else 0) : Mx k r) := by
    unfold dz
    ext p q
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs <;> simp
  have hconj : Complex.exp ((t : ℂ) * -star κ) = (star (Complex.exp ((t : ℂ) * κ)))⁻¹ := by
    rw [show (t : ℂ) * -star κ = -(star ((t : ℂ) * κ)) by simp, Complex.exp_neg]
    congr 1
    exact Complex.exp_conj _
  rw [hsm, exp_diag2, hconj, Matrix.mul_assoc, ← dg_comm l _ _ g₁ hg₁, ← Matrix.mul_assoc, w_mul_dg]

lemma rdV_dz {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r) (D : Set (Mx k r))
    (f : Mx k r → E) (hf : SmoothLev k r l.castSucc D f) (c : Fin r → ℂ) (hc : c l ≠ 0)
    (g₁ : Mx k r) (hg₁ : g₁ ∈ Glev k r l.succ) (hD : w1 k r l (c l) * g₁ ∈ D) (κ : ℂ) :
    RdV (dz l κ (-star κ)) f (w1 k r l (c l) * g₁) =
      fderiv ℝ (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) c (Pi.single l (c l * κ)) := by
  have hφ := phi_diff l D f hf c hc g₁ hg₁ hD
  have hηd : HasDerivAt (fun t : ℝ => Function.update c l (c l * Complex.exp ((t : ℂ) * κ)))
      (Pi.single l (c l * κ)) 0 := by
    rw [hasDerivAt_pi]
    intro i
    by_cases hi : i = l
    · subst hi
      simp only [Function.update_apply, if_true, Pi.single_eq_same]
      have h1 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * κ)) κ 0 := by
        have h2 := (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const κ).cexp).comp_ofReal
        simpa using h2
      simpa using h1.const_mul (c i)
    · simp only [Function.update_apply, hi, if_false, Pi.single_eq_of_ne hi]
      exact hasDerivAt_const _ _
  have hη0 : Function.update c l (c l * Complex.exp (((0 : ℝ) : ℂ) * κ)) = c := by simp
  have hcomp := hφ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hηd hη0.symm
  unfold RdV
  have hfun : (fun t : ℝ => f (w1 k r l (c l) * g₁ * NormedSpace.exp ((t : ℂ) • dz l κ (-star κ)))) =
      (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) ∘
        (fun t : ℝ => Function.update c l (c l * Complex.exp ((t : ℂ) * κ))) := by
    funext t
    rw [mul_exp_dz l (c l) κ g₁ hg₁ t]
    simp [Function.comp]
  rw [hfun, hcomp.deriv]

lemma rdV_dz' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r) (D : Set (Mx k r))
    (f : Mx k r → E) (hf : SmoothLev k r l.castSucc D f) (c : Fin r → ℂ) (hc : c l ≠ 0)
    (g₁ : Mx k r) (hg₁ : g₁ ∈ Glev k r l.succ) (hD : w1 k r l (c l) * g₁ ∈ D) (κ κ' : ℂ)
    (hκ : κ' = -star κ) :
    RdV (dz l κ κ') f (w1 k r l (c l) * g₁) =
      fderiv ℝ (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) c (Pi.single l (c l * κ)) := by
  subst hκ
  exact rdV_dz l D f hf c hc g₁ hg₁ hD κ

lemma lin_single {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r)
    (L : (Fin r → ℂ) →L[ℝ] E) (z : ℂ) :
    L (Pi.single l z) = (z.re : ℂ) • L (Pi.single l 1) + (z.im : ℂ) • L (Pi.single l Complex.I) := by
  have h : (Pi.single l z : Fin r → ℂ) =
      ((z.re : ℝ) • (Pi.single l (1 : ℂ) : Fin r → ℂ) +
        (z.im : ℝ) • (Pi.single l Complex.I : Fin r → ℂ) : Fin r → ℂ) := by
    ext i
    by_cases hi : i = l
    · subst hi
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Complex.real_smul, mul_one]
      exact (Complex.re_add_im z).symm
    · simp [hi]
  rw [h, map_add (f := _), map_smul, map_smul, Complex.coe_smul, Complex.coe_smul]

end PI.QnRT
end
end

theorem qnRuleTorus : Formalism.FourierDecayAlt.Q.RuleTorus := by
  open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q PI.QnRT in
  intro E _ _ k r l D f hD hf c hc g₁ hg₁ hmem
  have hcl : c l ≠ 0 := hc l
  have h1 : -((1 / 2 : ℝ) : ℂ) = -star ((1 / 2 : ℝ) : ℂ) := by simp
  have h2 : ((-1 / 2 : ℝ) : ℂ) * Complex.I = -star (((-1 / 2 : ℝ) : ℂ) * Complex.I) := by
    simp
  have h3 : ((1 / 2 : ℝ) : ℂ) = -star (-((1 / 2 : ℝ) : ℂ)) := by simp
  set φ : (Fin r → ℂ) → E := fun c' => f (w1 k r l (c' l) * g₁) with hφ
  set L := fderiv ℝ φ c with hL
  refine ⟨?_, ?_⟩
  · simp only [EH, EabH]
    rw [X1_eq, depthNumbers_threshold_eq, rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h1,
      rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h2]
    simp only [pOp, wirt, if_pos hc]
    rw [lin_single l L (c l * ((1 / 2 : ℝ) : ℂ)), lin_single l L (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]
    generalize L (Pi.single l 1) = A
    generalize L (Pi.single l Complex.I) = B
    obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, c l = (a : ℂ) + (b : ℂ) * Complex.I :=
      ⟨_, _, (Complex.re_add_im _).symm⟩
    rw [hab]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    match_scalars <;> simp [Complex.ext_iff] <;> ring
  · simp only [EH, EabH]
    rw [first_hermitian_part_diagonal, second_hermitian_part_diagonal, rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h3,
      rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h2]
    simp only [pbOp, wirtBar, if_pos hc]
    rw [lin_single l L (c l * -((1 / 2 : ℝ) : ℂ)), lin_single l L (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]
    generalize L (Pi.single l 1) = A
    generalize L (Pi.single l Complex.I) = B
    obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, c l = (a : ℂ) + (b : ℂ) * Complex.I :=
      ⟨_, _, (Complex.re_add_im _).symm⟩
    rw [hab]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    match_scalars <;> simp [Complex.ext_iff] <;> ring
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnLevTransfer
theorem level_transfer_of_levHom : Formalism.QuantumDeterminants.LevHom → Formalism.FourierDecayAlt.Q.LevelTransfer := by
  open PIQnLT Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q in
  intro hL E _ _ k i r' z z' Y p q f g hg
  have hinv : (ιLev k i r' g)⁻¹ = ιLev k i r' g⁻¹ := ιLev_inv hL g (isUnit_det_of_UH g hg)
  have hm := mdim_lev k i r'
  have hP : ∀ j, posL k (i + r') ⟨i, by omega⟩ j = levPos k i r' (posL k r' 0 (Fin.cast hm j)) :=
    posL_lev k i r'
  have hx : ∀ j, xv k (i + r') (liftVec k i r' z') ⟨i, by omega⟩ j = xv k r' z' 0 (Fin.cast hm j) := by
    intro j
    simp only [xv]
    rw [fvec_lift, hP, liftVec_lev]
  have hxb : ∀ j, xbv k (i + r') (liftVec k i r' z') ⟨i, by omega⟩ j =
      xbv k r' z' 0 (Fin.cast hm j) := by
    intro j
    simp only [xbv]
    rw [fvec_lift, hP, bvec_lev, herm_liftVec]
  have hy : ∀ j, yv k (i + r') (liftVec k i r' z) ⟨i, by omega⟩ (ιLev k i r' g) j =
      yv k r' z 0 g (Fin.cast hm j) := by
    intro j
    simp only [yv]
    rw [hinv, fvec_lift, mulVec_liftVec, hP, liftVec_lev]
  have hyb : ∀ j, ybv k (i + r') (liftVec k i r' z) ⟨i, by omega⟩ (ιLev k i r' g) j =
      ybv k r' z 0 g (Fin.cast hm j) := by
    intro j
    simp only [ybv]
    rw [fvec_lift, hP, bvec_lev, mulVec_liftVec, herm_liftVec]
  have hu := uC_lev k i r' Y
  fin_cases p <;> fin_cases q
  · simp only [tL, capL]
    rw [hu]
    exact capL_cast hL hm _ _ hP _ f g
  · simp only [tL, Pi.neg_apply]
    rw [hu]
    congr 1
    exact chatL_cast hL hm _ _ hP _ _ _ _ _ f g (fun j => hx j) (fun j => hyb j)
  · simp only [tL, Pi.neg_apply]
    rw [hu]
    congr 1
    exact chatL_cast hL hm _ _ hP _ _ _ _ _ f g (fun j => hy j) (fun j => hxb j)
  · simp only [tL, Pi.neg_apply]
    rw [hu]
    congr 1
    exact second_capelli_minor_cast hL hm _ _ hP _ _ _ _ _ _ _ _ _ f g (fun j => hy j) (fun j => hx j)
      (fun j => hyb j) (fun j => hxb j)
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnGlevImage
theorem gl_level_image : Formalism.QuantumDeterminants.LevHom → Formalism.QuantumDeterminants.LevUH → Formalism.FourierDecayAlt.Q.GlevImage :=
  QnGlevImageW.glevImage_of
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnLevBasics
theorem level_basics : Formalism.QuantumDeterminants.LevHom ∧ Formalism.QuantumDeterminants.LevUH ∧ Formalism.QuantumDeterminants.LevN ∧ Formalism.QuantumDeterminants.LevUW ∧ Formalism.QuantumDeterminants.LevWb ∧ Formalism.QuantumDeterminants.LevEll :=
  ⟨PI.QnLevBasicsW.level_group_homomorphism, PI.QnLevBasicsW.level_group_unitary_hermitian, PI.QnLevBasicsW.level_group_nilpotent,
    PI.QnLevBasicsW.level_group_unitary_weyl, PI.QnLevBasicsW.level_group_isotropic_vector, PI.QnLevBasicsW.level_group_ellipticity⟩
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmBorderFull
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderMinorRotation.QmBorderFullOf
section -- merged from Formalism.PeriodIntegrals.QmBorderFull
namespace PI

def QmBorderFull : Prop := BorderFull

end PI
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderMinorRotation.Development
open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmBorderFull

open PI

def BFMid : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (E : Fin n → Fin n → A) (e es : Fin n) (v : Fin m → Fin n),
    GlRel E → IsBorder e es v → ∀ (u : ℂ) (w : Fin m),
      (((-1 : ℤ) ^ ((w.castSucc.succ : Fin (m + 1 + 1)) : ℕ) : ℤ) : A) *
        (Tm E u (bE e (bS v es) w.castSucc.succ) (bE e (bS v es) 0) *
          qminor E (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) (bE e (bS v es) ∘ Fin.succ) (u - 1))
      = - (∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
            (E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) * Tm E (u - (m : ℂ) - 1) es es * E e (v x)))
        - (∑ w' : Fin m, ∑ x : Fin m, ∑ x' : Fin m,
            if w ≠ w' ∧ x ≠ x' then ((sg2 w w' * sg2 x x' : ℤ) : A) *
              (E (v w) e * E es (v x) *
                qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
                E e (v x') * E (v w') es)
            else 0)
        + (((-1 : ℤ) ^ ((w : ℕ) + 1 + m) : ℤ) : A) *
            (E (v w) e * qminor E (Fin.snoc (α := fun _ => Fin n) (v ∘ skip1 w) es ∘ Fin.cast (by
                have := w.isLt; omega)) v (u - 1) * E e es)

def BFCross : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n k : ℕ) (E : Fin n → Fin n → A) (e es : Fin n) (v : Fin (k + 1) → Fin n),
    GlRel E → IsBorder e es v → ∀ (u : ℂ) (w : Fin (k + 1)),
      ∑ j : Fin k, (((-1 : ℤ) ^ ((k + 1) + ((j.castSucc.succ : Fin (k + 1 + 1)) : ℕ)) : ℤ) : A) *
        (qminor E ((bE e (bS v es) ∘ (w.castSucc.succ).succAbove) ∘ (j.castSucc.succ).succAbove) v (u - 1) *
          Tm E (u - 1 - ((k + 1 : ℕ) : ℂ)) ((bE e (bS v es) ∘ (w.castSucc.succ).succAbove) j.castSucc.succ) es)
      = (((-1 : ℤ) ^ (w : ℕ) : ℤ) : A) *
        ∑ w' : Fin (k + 1), ∑ x : Fin (k + 1), ∑ x' : Fin (k + 1),
            if w ≠ w' ∧ x ≠ x' then ((sg2 w w' * sg2 x x' : ℤ) : A) *
              (E es (v x) *
                qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
                E e (v x') * E (v w') es)
            else 0

theorem tm_comm_E {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (u : ℂ) (e c d : Fin n) (h1 : e ≠ c) (h2 : d ≠ e) : Tm E u e e * E c d = E c d * Tm E u e e := by
  have h := hE e e c d
  rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at h
  rw [Formalism.REAL.Tm, if_pos rfl, add_mul, mul_add, Algebra.commutes, h]

theorem bL_last {n m : ℕ} (e es : Fin n) (v : Fin m → Fin n) :
    bE e (bS v es) ∘ (Fin.last (m + 1)).succAbove = bE e v := by
  funext i
  simp only [Function.comp_apply, Fin.succAbove_last]
  cases i using Fin.cases with
  | zero => simp [PI.bE]
  | succ j =>
    first
    | simp [PI.bE, PI.bS, ← Fin.succ_castSucc]
    | simp [PI.bE, PI.bS, Fin.cons_snoc_eq_snoc_cons]

private theorem mul_intCast_mul_eq_intCast_mul_mul {A : Type*} [Ring A] (s x : A) (z : ℤ) :
    s * ((z : A) * x) = (z : A) * (s * x) := by
  rw [← mul_assoc, ← mul_assoc, (Int.cast_commute z s).symm.eq]

theorem borderFull_of (hFC : ExpFirstCol) (hS : BorderS) (hM : BFMid) : BorderFull := by
  unfold PI.ExpFirstCol at hFC
  unfold PI.BorderS at hS
  unfold BFMid at hM
  unfold PI.BorderFull
  intro A _ _ n m E e es v hE hv u
  have hv2 : Function.Injective v ∧ e ≠ es ∧ (∀ j, v j ≠ e) ∧ ∀ j, v j ≠ es := hv
  obtain ⟨_, hne, hve, _⟩ := hv2
  have hmid := hM A n m E e es v hE hv u
  have hs : PI.bE e (PI.bS v es) ∘ Fin.succ = PI.bS v es := by
    funext i
    simp [PI.bE]
  have h0v : PI.bE e (PI.bS v es) 0 = e := by simp [PI.bE]
  have hLv : PI.bE e (PI.bS v es) (Fin.last m).succ = es := by simp [PI.bE, PI.bS]
  have hL : PI.bE e (PI.bS v es) ∘ ((Fin.last m).succ).succAbove = PI.bE e v := by
    rw [Fin.succ_last]
    exact bL_last e es v
  have hgen : Formalism.REAL.Tm E u es e = E es e := by
    simp [Formalism.REAL.Tm, hne.symm]
  have hu : u - 1 - (m : ℂ) = u - (m : ℂ) - 1 := by ring
  have hT2 : Formalism.REAL.Tm E u e e * ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (E es (v x) * Formalism.REAL.qminor E (v ∘ PI.skip1 w) (v ∘ PI.skip1 x) (u - 1) * E (v w) es)
      = ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (E es (v x) * Formalism.REAL.Tm E u e e * Formalism.REAL.qminor E (v ∘ PI.skip1 w) (v ∘ PI.skip1 x) (u - 1) * E (v w) es) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_intCast_mul_eq_intCast_mul_mul]
    congr 1
    rw [← mul_assoc, ← mul_assoc, tm_comm_E E hE u e es (v x) hne (hve x)]
  rw [hFC A n (m + 1) E (PI.bE e (PI.bS v es)) (PI.bE e (PI.bS v es)) u,
    Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  first
  | simp only [hmid]
  | rw [Finset.sum_congr rfl (fun w _ => hmid w)]
  rw [Fin.succAbove_zero, hs, h0v, hL, hLv, hgen]
  simp only [Fin.val_zero, pow_zero, Int.cast_one, one_mul, Fin.val_succ, Fin.val_last]
  rw [hS A n m E e es v hE hv (u - 1), hu, mul_sub (Formalism.REAL.Tm E u e e), hT2,
    ← mul_assoc (Formalism.REAL.Tm E u e e) (Formalism.REAL.qminor E v v (u - 1))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  abel

end PI.UnitaryGroupMassFormula.QmBorderFull
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderMinorRotation.SkipTwoSuccAboveComp
open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmBorderFull.Four

open PI

theorem val_sA {n : ℕ} (p : Fin (n + 1)) (k : Fin n) :
    (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
  by_cases h : k.val < p.val
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    rfl
  · rw [if_neg h, Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using not_lt.mp h)]
    rfl

theorem cons_comp_finRotate {n t : ℕ} (e : Fin n) (f : Fin t → Fin n) :
    bE e f ∘ (finRotate (t + 1) : Fin (t + 1) → Fin (t + 1)) = bS f e := by
  unfold bE bS
  rw [Fin.snoc_eq_cons_rotate]
  rfl

theorem neg_one_pow_mul_self (t : ℕ) : ((-1 : ℤ) ^ t) * ((-1 : ℤ) ^ t) = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

private theorem qminor_comp_perm_eq_sign_mul {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (τ : Equiv.Perm (Fin t)) (u : ℂ) :
    qminor E (a ∘ τ) b u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E a b u := by
  unfold qminor
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  simp only [Function.comp_apply, Equiv.coe_mulLeft, Equiv.Perm.coe_mul, Equiv.Perm.sign_mul]
  rw [← mul_assoc]
  congr 1
  rw [Units.val_mul, Int.cast_mul, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
    Units.val_one, Int.cast_one, one_mul]

theorem qminor_bE_eq {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (e : Fin n)
    (f : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E (bE e f) b u = (((-1 : ℤ) ^ t : ℤ) : A) * qminor E (bS f e) b u := by
  have h := qminor_comp_perm_eq_sign_mul E (bE e f) b (finRotate (t + 1)) u
  rw [cons_comp_finRotate, sign_finRotate, Nat.add_sub_cancel] at h
  rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at h
  rw [h, ← mul_assoc, ← Int.cast_mul, neg_one_pow_mul_self, Int.cast_one, one_mul]

theorem qminor_bS_eq {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (e : Fin n)
    (f : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E (bS f e) b u = (((-1 : ℤ) ^ t : ℤ) : A) * qminor E (bE e f) b u := by
  have h := qminor_comp_perm_eq_sign_mul E (bE e f) b (finRotate (t + 1)) u
  rw [cons_comp_finRotate, sign_finRotate, Nat.add_sub_cancel] at h
  rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at h
  exact h

theorem Tm_of_ne {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) {a b : Fin n}
    (h : a ≠ b) : Tm E u a b = E a b := by
  unfold Tm
  simp [h]

theorem zmul {A : Type} [Ring A] (z : ℤ) (y : A) : (z : A) * y = z • y := by
  rw [zsmul_eq_mul]

theorem rowPart (hR : ExpLastRow) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (hG : GlRel E) (e : Fin n) (f : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (he : ∀ x, b x ≠ e) (u : ℂ) :
    qminor E (bE e f) b u = ∑ x : Fin (t + 1), (((-1 : ℤ) ^ (x : ℕ) : ℤ) : A) *
      (qminor E f (b ∘ x.succAbove) (u - 1) * E e (b x)) := by
  rw [qminor_bE_eq, hR A n t E hG (bS f e) b u, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : bS f e ∘ Fin.castSucc = f := by
    funext i
    simp [bS]
  have h2 : bS f e (Fin.last t) = e := by simp [bS]
  have hs : (-1 : ℤ) ^ t * (-1 : ℤ) ^ (t + (x : ℕ)) = (-1 : ℤ) ^ (x : ℕ) := by
    rw [pow_add, ← mul_assoc, neg_one_pow_mul_self, one_mul]
  rw [h1, h2, Tm_of_ne E u (Ne.symm (he x)), ← mul_assoc, ← Int.cast_mul, hs]

theorem colPart (hF : ExpFirstRow) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (hG : GlRel E) (e : Fin n) (f : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (he : ∀ x, b x ≠ e) (u : ℂ) :
    qminor E (bS f e) b u = ∑ x : Fin (t + 1), (((-1 : ℤ) ^ (t + (x : ℕ)) : ℤ) : A) *
      (E e (b x) * qminor E f (b ∘ x.succAbove) u) := by
  rw [qminor_bS_eq, hF A n t E hG (bE e f) b u, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : bE e f ∘ Fin.succ = f := by
    funext i
    simp [bE]
  have h2 : bE e f 0 = e := by simp [bE]
  rw [h1, h2, Tm_of_ne E _ (Ne.symm (he x)), ← mul_assoc, ← Int.cast_mul, ← pow_add]

theorem inner (hR : ExpLastRow) (hF : ExpFirstRow) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (hG : GlRel E) (e es : Fin n) (W : Fin t → Fin n) (b : Fin (t + 2) → Fin n)
    (he : ∀ x, b x ≠ e) (hes : ∀ x, b x ≠ es) (z : ℂ) :
    qminor E (bE e (bS W es)) b z = ∑ x : Fin (t + 2), ∑ y : Fin (t + 1),
      (((-1 : ℤ) ^ ((x : ℕ) + t + (y : ℕ)) : ℤ) : A) *
        (E es (b (x.succAbove y)) * qminor E W ((b ∘ x.succAbove) ∘ y.succAbove) (z - 1) * E e (b x)) := by
  rw [rowPart hR E hG e (bS W es) b he z]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [colPart hF E hG es W (b ∘ x.succAbove) (fun y => hes _) (z - 1), Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Function.comp_apply, ← mul_assoc, ← Int.cast_mul, ← pow_add, add_assoc]

theorem skip_two_succAbove_comp_alt {k : ℕ} (w : Fin (k + 2)) (j : Fin (k + 1)) (i : Fin k) :
    skip2 (min w (w.succAbove j)) (max w (w.succAbove j)) i = w.succAbove (j.succAbove i) := by
  apply Fin.ext
  have hv := val_sA w j
  rw [val_sA w (j.succAbove i), val_sA j i]
  unfold skip2
  rcases lt_or_ge (j : ℕ) (w : ℕ) with h | h
  · have hlt : w.succAbove j < w := by rw [Fin.lt_def, hv, if_pos h]; exact h
    rw [min_eq_right hlt.le, max_eq_left hlt.le]
    rw [if_pos h] at hv
    split_ifs <;> (simp_all; try omega)
  · have hle : w ≤ w.succAbove j := by rw [Fin.le_def, hv, if_neg (by omega)]; omega
    rw [min_eq_left hle, max_eq_right hle]
    rw [if_neg (by omega)] at hv
    split_ifs <;> (simp_all; try omega)

theorem sign_pair_succAbove_right {k : ℕ} (w : Fin (k + 1)) (j : Fin k) :
    sg2 w (w.succAbove j) = (-1 : ℤ) ^ ((w : ℕ) + (j : ℕ)) := by
  unfold sg2
  rcases lt_or_ge (j : ℕ) (w : ℕ) with h | h
  · have hv : (w.succAbove j).val = j := by rw [val_sA, if_pos h]
    rw [if_pos (by rw [hv]; exact h), hv]
  · have hv : (w.succAbove j).val = j + 1 := by rw [val_sA, if_neg (by omega)]
    rw [if_neg (by rw [hv]; omega), hv, show (w : ℕ) + (j + 1) + 1 = (w + j) + 2 by ring, pow_add]
    norm_num

theorem sign_two_succAbove_left {k : ℕ} (x : Fin (k + 1)) (y : Fin k) :
    sg2 (x.succAbove y) x = -(-1 : ℤ) ^ ((x : ℕ) + (y : ℕ)) := by
  unfold sg2
  rcases lt_or_ge (y : ℕ) (x : ℕ) with h | h
  · have hv : (x.succAbove y).val = y := by rw [val_sA, if_pos h]
    rw [if_neg (by rw [hv]; omega), hv, pow_succ, add_comm (y : ℕ)]
    ring
  · have hv : (x.succAbove y).val = y + 1 := by rw [val_sA, if_neg (by omega)]
    rw [if_pos (by rw [hv]; omega), hv, show (y : ℕ) + 1 + x = (x + y) + 1 by ring, pow_succ]
    ring

theorem sum_sA_ite {M : Type*} [AddCommMonoid M] {k : ℕ} (w : Fin (k + 1)) (g : Fin (k + 1) → M) :
    ∑ w' : Fin (k + 1), (if w ≠ w' then g w' else 0) = ∑ j : Fin k, g (w.succAbove j) := by
  rw [Fin.sum_univ_succAbove _ w, if_neg (not_not.mpr rfl), zero_add]
  exact Finset.sum_congr rfl fun j _ => if_pos (Fin.succAbove_ne w j).symm

theorem triple {M : Type*} [AddCommMonoid M] {k : ℕ} (w : Fin (k + 1))
    (H : Fin (k + 1) → Fin (k + 1) → Fin (k + 1) → M) :
    ∑ w' : Fin (k + 1), ∑ x : Fin (k + 1), ∑ x' : Fin (k + 1), (if w ≠ w' ∧ x ≠ x' then H w' x x' else 0)
      = ∑ j : Fin k, ∑ x' : Fin (k + 1), ∑ y : Fin k, H (w.succAbove j) (x'.succAbove y) x' := by
  have h1 : ∀ w' : Fin (k + 1), (∑ x : Fin (k + 1), ∑ x' : Fin (k + 1),
      (if w ≠ w' ∧ x ≠ x' then H w' x x' else 0)) =
      if w ≠ w' then ∑ x : Fin (k + 1), ∑ x' : Fin (k + 1), (if x ≠ x' then H w' x x' else 0) else 0 := by
    intro w'
    by_cases hw : w ≠ w'
    · simp [hw]
    · simp [hw]
  rw [Finset.sum_congr rfl fun w' _ => h1 w', sum_sA_ite]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  have h2 : ∀ x : Fin (k + 1), (if x ≠ x' then H (w.succAbove j) x x' else 0) =
      if x' ≠ x then H (w.succAbove j) x x' else 0 := by
    intro x
    by_cases h : x = x'
    · subst h
      rfl
    · rw [if_pos h, if_pos (Ne.symm h)]
  rw [Finset.sum_congr rfl fun x _ => h2 x]
  exact sum_sA_ite x' (fun x => H (w.succAbove j) x x')

theorem mid_comp {n t : ℕ} (e es : Fin n) (F : Fin (t + 1) → Fin n) (p : Fin (t + 1)) :
    bE e (bS F es) ∘ (p.castSucc.succ).succAbove = bE e (bS (F ∘ p.succAbove) es) := by
  funext i
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp [bE]
  · simp only [Function.comp_apply, bE, Fin.succ_succAbove_succ, Fin.cons_succ]
    refine Fin.lastCases ?_ (fun i'' => ?_) i'
    · rw [Fin.succAbove_ne_last_last (Fin.castSucc_lt_last p).ne]
      simp [bS]
    · rw [Fin.castSucc_succAbove_castSucc]
      simp [bS]

theorem mid_val {n t : ℕ} (e es : Fin n) (F : Fin t → Fin n) (j : Fin t) :
    bE e (bS F es) j.castSucc.succ = F j := by
  simp [bE, bS]

theorem scal (k w j x y : ℕ) :
    (-1 : ℤ) ^ (k + 1 + 1 + (j + 1)) * (-1 : ℤ) ^ (x + k + y) =
      (-1 : ℤ) ^ w * ((-1 : ℤ) ^ (w + j) * -(-1 : ℤ) ^ (x + y)) := by
  have hk := neg_one_pow_mul_self k
  have hw := neg_one_pow_mul_self w
  linear_combination (-(-1 : ℤ) ^ (j + x + y)) * hk + ((-1 : ℤ) ^ (j + x + y)) * hw

private theorem intCast_mul_mul_mul_eq_of_mul_eq {A : Type} [Ring A] (c₁ c₂ c₀ a : ℤ) (X S : A) (h : c₁ * c₂ = c₀ * a) :
    (c₁ : A) * (((c₂ : A) * X) * S) = (c₀ : A) * ((a : A) * (X * S)) := by
  rw [mul_assoc (c₂ : A), ← mul_assoc, ← mul_assoc (c₀ : A), ← Int.cast_mul, ← Int.cast_mul, h]

theorem bfCross_of (hRow : PI.QmRowExp) (_hSkip : PI.QmSkip) : BFCross := by
  intro A _ _ n k E e es v hG hB u w
  obtain ⟨hF, hR⟩ := hRow
  obtain ⟨_, _, hve, hves⟩ := hB
  cases k with
  | zero =>
    rw [Fin.sum_univ_zero]
    symm
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun w' _ => Finset.sum_eq_zero fun x _ =>
      Finset.sum_eq_zero fun x' _ => if_neg fun h => h.1 (Fin.ext ?_))
    have := w.isLt
    have := w'.isLt
    omega
  | succ k =>
    have ht := triple w (M := A) (fun w' x x' => ((sg2 w w' * sg2 x x' : ℤ) : A) *
      (E es (v x) * qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
        E e (v x') * E (v w') es))
    beta_reduce at ht
    rw [ht, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mid_comp, mid_comp, mid_val, Tm_of_ne E _ (a := (v ∘ w.succAbove) j) (hves (w.succAbove j)),
      inner hR hF E hG e es _ v hve hves (u - 1), Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hq1 : v ∘ skip2 (min w (w.succAbove j)) (max w (w.succAbove j)) = (v ∘ w.succAbove) ∘ j.succAbove := by
      funext i
      simp only [Function.comp_apply, skip_two_succAbove_comp_alt]
    have hq2 : v ∘ skip2 (min (x.succAbove y) x) (max (x.succAbove y) x) =
        (v ∘ x.succAbove) ∘ y.succAbove := by
      rw [min_comm, max_comm]
      funext i
      simp only [Function.comp_apply, skip_two_succAbove_comp_alt]
    have hu : u - 1 - 1 = u - 2 := by ring
    have hj : (j.castSucc.succ : ℕ) = (j : ℕ) + 1 := by simp
    rw [hq1, hq2, ← hu, sign_pair_succAbove_right, sign_two_succAbove_left, hj]
    exact intCast_mul_mul_mul_eq_of_mul_eq _ _ _ _ _ _ (scal k w j x y)

end PI.UnitaryGroupMassFormula.QmBorderFull.Four
end
end

namespace PI

private theorem snoc_comp_cast_eq_bS_of_eq {n k t : ℕ} (hk : k = t) (h : t + 1 = k + 1) (f : Fin k → Fin n)
    (g : Fin t → Fin n) (es : Fin n) (hfg : ∀ i : Fin k, f i = g (Fin.cast hk i)) :
    (Fin.snoc f es ∘ Fin.cast h : Fin (t + 1) → Fin n) = bS g es := by
  subst hk
  have hf : f = g := funext fun i => by simpa using hfg i
  subst hf
  funext i
  simp [bS]

private theorem bfMid_of_expLastCol_expLastRow_skipSucc_bfCross (hLC : ExpLastCol) (hLR : ExpLastRow) (hS1 : SkipSucc)
    (hX : UnitaryGroupMassFormula.QmBorderFull.BFCross) : UnitaryGroupMassFormula.QmBorderFull.BFMid := by
  intro A _ _ n m E e es v hG hB u w
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by have := w.pos; omega⟩
  have hexp := hLC A n (t + 1) E (bE e (bS v es) ∘ w.castSucc.succ.succAbove) (bS v es) (u - 1)
  have hb1 : bS v es ∘ Fin.castSucc = v := by
    funext i
    simp [bS]
  have hb2 : bS v es (Fin.last (t + 1)) = es := by simp [bS]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hexp
  beta_reduce at hexp
  rw [hb1, hb2, Fin.succ_last, hX A n t E e es v hG hB u w, UnitaryGroupMassFormula.QmBorderFull.Four.mid_comp] at hexp
  simp only [Nat.succ_eq_add_one] at hexp
  have e1 : bE e (bS (v ∘ w.succAbove) es) ∘ Fin.succ = bS (v ∘ w.succAbove) es := by
    funext i
    simp [bE]
  have e2 : bE e (bS (v ∘ w.succAbove) es) 0 = e := by simp [bE]
  have e3 : bE e (bS (v ∘ w.succAbove) es) (Fin.last (t + 1)) = es := by
    rw [← Fin.succ_last]
    simp [bE, bS]
  have hees : e ≠ es := hB.2.1
  rw [Fin.succAbove_zero, e1, e2, e3, UnitaryGroupMassFormula.QmBorderFull.bL_last,
    UnitaryGroupMassFormula.QmBorderFull.Four.Tm_of_ne E _ hees,
    UnitaryGroupMassFormula.QmBorderFull.Four.rowPart hLR E hG e (v ∘ w.succAbove) v (fun x => hB.2.2.1 x) (u - 1)] at hexp
  have g1 : bE e (bS v es) ∘ Fin.succ = bS v es := by
    funext i
    simp [bE]
  have g2 : bE e (bS v es) 0 = e := by simp [bE]
  have hsk : ∀ i : Fin (t + 1), (v ∘ skip1 i : Fin t → Fin n) = v ∘ i.succAbove := by
    intro i
    funext j
    exact congrArg v (hS1 t i j)
  have hu1 : u - 1 - 1 = u - 2 := by ring
  have hu2 : u - 1 - ((t + 1 : ℕ) : ℂ) = u - ((t + 1 : ℕ) : ℂ) - 1 := by ring
  rw [UnitaryGroupMassFormula.QmBorderFull.Four.mid_val (t := t + 1) e es v w, g2,
    UnitaryGroupMassFormula.QmBorderFull.Four.Tm_of_ne E u (hB.2.2.1 w), UnitaryGroupMassFormula.QmBorderFull.Four.mid_comp, g1, hexp]
  rw [hu1, hu2]
  simp only [hsk, Fin.val_succ, Fin.coe_castSucc, Fin.val_zero, Fin.val_last]
  rw [snoc_comp_cast_eq_bS_of_eq (k := t + 1 - 1) (t := t) rfl _ (v ∘ w.succAbove) (v ∘ w.succAbove) es (fun _ => rfl)]
  have hT : ∀ x : Fin (t + 1), E e (v x) * Formalism.REAL.Tm E (u - ↑(t + 1) - 1) es es =
      Formalism.REAL.Tm E (u - ↑(t + 1) - 1) es es * E e (v x) := fun x =>
    (UnitaryGroupMassFormula.QmBorderFull.tm_comm_E E hG _ es e (v x) hees.symm (hB.2.2.2 x)).symm
  clear hexp hb1 hb2 e1 e2 e3 g1 g2 hu1 hu2 hX hLC hLR hS1 hsk
  simp only [UnitaryGroupMassFormula.QmBorderFull.Four.zmul, mul_smul_comm, smul_mul_assoc, smul_add, smul_smul, mul_add,
    Finset.mul_sum, Finset.smul_sum, Finset.sum_mul, mul_ite, mul_zero, smul_ite, smul_zero, mul_assoc, hT]
  have k1 : ((-1 : ℤ) ^ (t + 1 + 0) * (-1) ^ ((w : ℕ) + 1)) = (-1) ^ ((w : ℕ) + 1 + (t + 1)) := by ring
  have k2 : ∀ a b : ℤ, a * (b * ((-1) ^ (w : ℕ) * (-1) ^ ((w : ℕ) + 1))) = -(a * b) := by
    intro a b
    have hw : ((-1 : ℤ) ^ (w : ℕ)) * (-1) ^ ((w : ℕ) + 1) = -1 := by
      rw [pow_succ, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [hw]
    ring
  have k3 : ∀ x : ℕ, (-1 : ℤ) ^ x * ((-1) ^ (t + 1 + (t + 1)) * (-1) ^ ((w : ℕ) + 1)) = -(-1) ^ ((w : ℕ) + x) := by
    intro x
    have : ((-1 : ℤ) ^ (t + 1 + (t + 1))) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    rw [this]
    ring
  have kite : ∀ (c : Prop) [Decidable c] (X : A), (if c then -X else 0) = -(if c then X else 0) := by
    intro c _ X
    split_ifs <;> simp
  simp only [k1, k2, k3, neg_smul, kite, Finset.sum_neg_distrib]
  abel

theorem qmBorderFull_of (hES : PI.QmBorderES) (hCol : PI.QmColExp) (hRow : PI.QmRowExp) (hSkip : PI.QmSkip) :
    PI.QmBorderFull := by
  obtain ⟨hE, hS⟩ := hES
  obtain ⟨hFC, hLC⟩ := hCol
  obtain ⟨hFR, hLR⟩ := hRow
  obtain ⟨hS1, hS2⟩ := hSkip
  exact UnitaryGroupMassFormula.QmBorderFull.borderFull_of hFC hS
    (bfMid_of_expLastCol_expLastRow_skipSucc_bfCross hLC hLR hS1 (UnitaryGroupMassFormula.QmBorderFull.Four.bfCross_of ⟨hFR, hLR⟩ ⟨hS1, hS2⟩))

end PI
end

theorem quantum_minor_border_full : PI.QmBorderFull :=
  PI.qmBorderFull_of quantum_minor_border_es quantum_minor_column_expansion quantum_minor_row_expansion quantum_minor_skip
end

theorem Formalism.FourierDecayAlt.P.border_first_expansion : Formalism.FourierDecayAlt.Q.BorderE := by
  exact quantum_minor_border_es.1

theorem Formalism.FourierDecayAlt.P.border_last_expansion : Formalism.FourierDecayAlt.Q.BorderS := by
  exact quantum_minor_border_es.2

theorem Formalism.FourierDecayAlt.P.border_full_expansion : Formalism.FourierDecayAlt.Q.BorderFull := by
  exact quantum_minor_border_full

theorem Formalism.FourierDecayAlt.P.rtt_sandwich : Formalism.FourierDecayAlt.Q.RTTSandwich := by
  exact rtt_sandwich'

theorem Formalism.FourierDecayAlt.P.level_group_image : Formalism.FourierDecayAlt.Q.GlevImage := by
  obtain ⟨hH, hU, -⟩ := level_basics
  exact gl_level_image hH hU

theorem Formalism.FourierDecayAlt.P.level_transfer : Formalism.FourierDecayAlt.Q.LevelTransfer := by
  exact level_transfer_of_levHom level_basics.1

theorem Formalism.FourierDecayAlt.P.left_action_rule : Formalism.FourierDecayAlt.Q.RuleLeft := by
  exact qnRuleLeft

theorem Formalism.FourierDecayAlt.P.torus_action_rule : Formalism.FourierDecayAlt.Q.RuleTorus := by
  exact qnRuleTorus

theorem Formalism.FourierDecayAlt.P.operator_invariance : Formalism.FourierDecayAlt.Q.TInvariant := by
  exact qnTInv

theorem Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms : Formalism.FourierDecayAlt.Q.TPreservesFF := by
  exact qnTPres

theorem Formalism.FourierDecayAlt.P.capelli_commutation : Formalism.FourierDecayAlt.Q.CapCommute := by
  exact capelli_det_commute

theorem Formalism.FourierDecayAlt.P.hermitian_haar_invariance : Formalism.FourierDecayAlt.Q.HermHaar := by
  exact qnHermHaar
