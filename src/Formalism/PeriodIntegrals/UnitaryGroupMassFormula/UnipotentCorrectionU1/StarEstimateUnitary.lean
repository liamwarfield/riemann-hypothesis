module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.PolynomialBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.DjCurve

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStarOf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CCCNonneg
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CBLamnorm
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CADwlSmooth
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cAsec

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cA_hasDeriv (x : Bool × B.Mat k r) {F : B.Mat k r → E} {g : B.Mat k r} (hd : DifferentiableAt ℝ F g) :
    HasDerivAt (fun t : ℝ => F (crv x g t)) (fderiv ℝ F g (dirv x g)) 0 :=
  hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (crv_hasDerivAt x g) (crv_zero x g).symm

theorem cA_Dx_eq (x : Bool × B.Mat k r) {F : B.Mat k r → E} (hd : Differentiable ℝ F) :
    Dx x F = fun g => fderiv ℝ F g (dirL x g) := by
  funext g
  rw [Dx_eq, dirL_apply]
  exact (cA_hasDeriv x (hd g)).deriv

theorem cA_Dx_smooth (x : Bool × B.Mat k r) {F : B.Mat k r → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Dx x F) := by
  rw [cA_Dx_eq x (hF.differentiable (by simp))]
  exact (hF.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by exact_mod_cast le_rfl)).clm_apply (dirL x).contDiff

theorem cA_Dx_lin (x : Bool × B.Mat k r) {F₁ F₂ : B.Mat k r → E} (h₁ : Differentiable ℝ F₁)
    (h₂ : Differentiable ℝ F₂) (c : ℂ) :
    Dx x (fun g => F₁ g + c • F₂ g) = fun g => Dx x F₁ g + c • Dx x F₂ g := by
  funext g
  rw [Dx_eq, Dx_eq, Dx_eq, (cA_hasDeriv x (h₁ g)).deriv, (cA_hasDeriv x (h₂ g)).deriv]
  exact ((cA_hasDeriv x (h₁ g)).add ((cA_hasDeriv x (h₂ g)).const_smul c)).deriv

def Dwl (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) (F : B.Mat k r → E) : B.Mat k r → E :=
  w.foldr (fun x G => fun g => Dx x G g + lam x • G g) F

theorem cA_Dwl_smooth (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) {F : B.Mat k r → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Dwl lam w F) := by
  induction w with
  | nil => exact hF
  | cons x w ih => exact (cA_Dx_smooth x ih).add (ih.const_smul (lam x))

theorem cA_Dwl_lin (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) {F₁ F₂ : B.Mat k r → E}
    (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁) (h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₂) (c : ℂ) :
    Dwl lam w (fun g => F₁ g + c • F₂ g) = fun g => Dwl lam w F₁ g + c • Dwl lam w F₂ g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    have d₁ := (cA_Dwl_smooth lam w h₁).differentiable (by simp)
    have d₂ := (cA_Dwl_smooth lam w h₂).differentiable (by simp)
    show (fun g => Dx x (Dwl lam w _) g + lam x • Dwl lam w _ g) = _
    rw [ih, cA_Dx_lin x d₁ d₂ c]
    funext g
    show _ = (Dx x (Dwl lam w F₁) g + lam x • Dwl lam w F₁ g) + c • (Dx x (Dwl lam w F₂) g + lam x • Dwl lam w F₂ g)
    rw [smul_add, smul_add, smul_comm c (lam x)]
    exact add_add_add_comm _ _ _ _

theorem cA_Dwl_append (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) (x : Bool × B.Mat k r)
    (F : B.Mat k r → E) : Dwl lam (w ++ [x]) F = Dwl lam w (fun g => Dx x F g + lam x • F g) := by
  simp [Dwl, List.foldr_append]

theorem cA_Dwl_bound (lam : Bool × B.Mat k r → ℂ) {Λ : ℝ} (hΛ : 0 ≤ Λ) (g : B.Mat k r) (M : ℝ) :
    ∀ (w : List (Bool × B.Mat k r)) (F : B.Mat k r → E), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
      (∀ x ∈ w, ‖lam x‖ ≤ Λ) → (∀ s : List (Bool × B.Mat k r), s.Sublist w → ‖Dw s F g‖ ≤ M) →
      ‖Dwl lam w F g‖ ≤ (1 + Λ) ^ w.length * M := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro F _ _ hM
    simpa [Dwl, Dw] using hM [] (List.Sublist.refl _)
  | append_singleton w x ih =>
    intro F hF hl hM
    have hl' : ∀ y ∈ w, ‖lam y‖ ≤ Λ := fun y hy => hl y (by simp [hy])
    have hx : ‖lam x‖ ≤ Λ := hl x (by simp)
    rw [cA_Dwl_append, cA_Dwl_lin lam w (cA_Dx_smooth x hF) hF]
    have b1 := ih (Dx x F) (cA_Dx_smooth x hF) hl' (by
      intro s hs
      have := hM (s ++ [x]) (hs.append (List.Sublist.refl _))
      rwa [Dw_append] at this)
    have b2 := ih F hF hl' (fun s hs => hM s (hs.trans (List.sublist_append_left _ _)))
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM [] (List.nil_sublist _))
    calc ‖Dwl lam w (Dx x F) g + lam x • Dwl lam w F g‖
        ≤ (1 + Λ) ^ w.length * M + Λ * ((1 + Λ) ^ w.length * M) := by
          refine (norm_add_le _ _).trans (add_le_add b1 ?_)
          rw [norm_smul]
          exact mul_le_mul hx b2 (norm_nonneg _) hΛ
      _ = (1 + Λ) ^ (w ++ [x]).length * M := by simp [pow_succ]; ring

theorem cA_Dw_expmul (lam : Bool × B.Mat k r → ℂ) (h : B.Mat k r → ℂ) :
    ∀ (w : List (Bool × B.Mat k r)) (F : B.Mat k r → E), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
      (∀ x ∈ w, ∀ g (t : ℝ), h (crv x g t) = Complex.exp ((t : ℂ) * lam x) * h g) →
      Dw w (fun g => h g • F g) = fun g => h g • Dwl lam w F g := by
  intro w
  induction w with
  | nil => intro F _ _; rfl
  | cons x w ih =>
    intro F hF hh
    have hh' : ∀ y ∈ w, ∀ g (t : ℝ), h (crv y g t) = Complex.exp ((t : ℂ) * lam y) * h g :=
      fun y hy => hh y (by simp [hy])
    show Dx x (Dw w _) = _
    rw [ih F hF hh']
    funext g
    have hG := cA_Dwl_smooth lam w hF
    have d := cA_hasDeriv x ((hG.differentiable (by simp)) g)
    have he : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * lam x) * h g) (lam x * h g) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * lam x) (1 * lam x) 0 :=
        (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (lam x)
      have h2 := (h1.cexp).mul_const (h g)
      simpa using h2
    have hs : HasDerivAt (fun t : ℝ => (Complex.exp ((t : ℂ) * lam x) * h g) • Dwl lam w F (crv x g t))
        ((Complex.exp (((0 : ℝ) : ℂ) * lam x) * h g) • fderiv ℝ (Dwl lam w F) g (dirv x g) +
          (lam x * h g) • Dwl lam w F (crv x g 0)) 0 := he.smul d
    rw [Dx_eq]
    have e : (fun t : ℝ => h (crv x g t) • Dwl lam w F (crv x g t)) =
        fun t : ℝ => (Complex.exp ((t : ℂ) * lam x) * h g) • Dwl lam w F (crv x g t) := by
      funext t; rw [hh x (by simp) g t]
    rw [e, hs.deriv, crv_zero, ← dirL_apply, ← congrFun (cA_Dx_eq x (hG.differentiable (by simp))) g]
    show _ = h g • (Dx x (Dwl lam w F) g + lam x • Dwl lam w F g)
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, smul_add, smul_smul]
    rw [mul_comm (lam x)]

theorem cA_Dw_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℂ] E')
    {U : Set (B.Mat k r)} (hU : IsOpen U) (w : List (Bool × B.Mat k r)) (hw : ∀ x ∈ w, B.inLie k r x.2)
    {f : B.Mat k r → E} (hf : B.CkOn (w.length : ℕ∞) U f) :
    ∀ g ∈ B.GV k r, g ∈ U → Dw w (fun h => L (f h)) g = L (Dw w f g) := by
  induction w with
  | nil => intro g _ _; rfl
  | cons x w ih =>
    intro g hg hgU
    have hw' : ∀ y ∈ w, B.inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hx : B.inLie k r x.2 := hw x (by simp)
    have hle : ((w.length : ℕ) : ℕ∞) ≤ ((x :: w).length : ℕ) := by exact_mod_cast Nat.le_succ _
    show Dx x (Dw w (fun h => L (f h))) g = L (Dx x (Dw w f) g)
    rw [Dx_congr_loc hx hU (f₂ := fun h => L (Dw w f h)) (ih hw' (sCkOn_mono hle hf)) g hg hgU]
    have hc : B.CkOn 1 U (Dw w f) := by
      apply CkOn_Dw hw'
      have : (1 : ℕ∞) + (w.length : ℕ∞) = ((x :: w).length : ℕ) := by simp; ring
      rw [this]; exact hf
    have h1 := CkOn_diff hx hc hgU hg
    have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    rw [Dx_eq]
    exact h2.deriv

end cAsec

end PI.UnitaryCorollaryDerivatives
end
end

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def hhF (k j ρ a b : ℕ) (g : B.Mat k (j + ρ)) : ℂ := (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b

theorem cB_alg (a b : ℕ) (c D : ℂ) (t : ℝ) :
    (Complex.exp ((t : ℂ) * c) * D)⁻¹ ^ a * (star (Complex.exp ((t : ℂ) * c) * D))⁻¹ ^ b =
      Complex.exp ((t : ℂ) * -((a : ℂ) * c + (b : ℂ) * conj c)) * (D⁻¹ ^ a * (star D)⁻¹ ^ b) := by
  have e1 : star (Complex.exp ((t : ℂ) * c)) = Complex.exp ((t : ℂ) * conj c) := by
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  rw [star_mul', e1, mul_inv, mul_inv, mul_pow, mul_pow, ← Complex.exp_neg, ← Complex.exp_neg,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have : Complex.exp ((t : ℂ) * -((a : ℂ) * c + (b : ℂ) * conj c)) =
      Complex.exp ((a : ℂ) * -((t : ℂ) * c)) * Complex.exp ((b : ℂ) * -((t : ℂ) * conj c)) := by
    rw [← Complex.exp_add]; ring_nf
  rw [this]; ring

theorem cB_lamnorm (a b : ℕ) (c : ℂ) {j : ℕ} {m : ℝ} (hc : ‖c‖ ≤ (j : ℝ) * m) :
    ‖-((a : ℂ) * c + (b : ℂ) * conj c)‖ ≤ ((a + b : ℕ) : ℝ) * j * m := by
  rw [norm_neg]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast, Complex.norm_conj]
  push_cast
  have ha : (0 : ℝ) ≤ a := by positivity
  have hb : (0 : ℝ) ≤ b := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hc ha, mul_le_mul_of_nonneg_left hc hb]

theorem cB_curve (hC : DjCurve) (k j ρ a b : ℕ) :
    ∃ lam : Bool × B.Mat k (j + ρ) → ℂ, ∀ x : Bool × B.Mat k (j + ρ), inLieP k j ρ x.2 →
      ‖lam x‖ ≤ ((a + b : ℕ) : ℝ) * j * mx x.2 ∧
      ∀ (g : B.Mat k (j + ρ)) (t : ℝ), hhF k j ρ a b (crv x g t) = Complex.exp ((t : ℂ) * lam x) * hhF k j ρ a b g := by
  have key : ∀ x : Bool × B.Mat k (j + ρ), ∃ μ : ℂ, inLieP k j ρ x.2 →
      ‖μ‖ ≤ ((a + b : ℕ) : ℝ) * j * mx x.2 ∧
      ∀ (g : B.Mat k (j + ρ)) (t : ℝ), hhF k j ρ a b (crv x g t) = Complex.exp ((t : ℂ) * μ) * hhF k j ρ a b g := by
    rintro ⟨bb, Y⟩
    by_cases hY : inLieP k j ρ Y
    · obtain ⟨c₁, c₂, h₁, h₂, hcur⟩ := hC k j ρ Y hY
      cases bb
      · refine ⟨-((a : ℂ) * c₁ + (b : ℂ) * conj c₁), fun _ => ⟨cB_lamnorm a b c₁ h₁, fun g t => ?_⟩⟩
        rw [show crv (false, Y) g t = g * NormedSpace.exp ((t : ℂ) • Y) from rfl]
        unfold hhF
        rw [(hcur g t).1, cB_alg]
      · refine ⟨-((a : ℂ) * c₂ + (b : ℂ) * conj c₂), fun _ => ⟨cB_lamnorm a b c₂ h₂, fun g t => ?_⟩⟩
        rw [show crv (true, Y) g t = NormedSpace.exp (-((t : ℂ) • Y)) * g from rfl]
        unfold hhF
        rw [(hcur g t).2, cB_alg]
    · exact ⟨0, fun h => absurd h hY⟩
  choose lam hlam using key
  exact ⟨lam, hlam⟩

theorem cB_smooth {k j ρ : ℕ} (hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (DjU k j ρ)) {P : B.Mat k (j + ρ) → ℂ}
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P) (a b : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b)
      {g | DjU k j ρ g ≠ 0} := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (DjU k j ρ g)⁻¹) {g | DjU k j ρ g ≠ 0} :=
    hD.contDiffOn.inv (fun g hg => hg)
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => star (DjU k j ρ g)) := by
    have := Complex.conjCLE.contDiff.comp hD
    simpa [Function.comp_def, Complex.star_def] using this
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (star (DjU k j ρ g))⁻¹) {g | DjU k j ρ g ≠ 0} :=
    hs.contDiffOn.inv (fun g hg => by simpa using hg)
  exact (hP.contDiffOn.mul (h1.pow a)).mul (h2.pow b)

theorem cB_mx_le {α : Type*} [Fintype α] {X : Matrix α α ℂ} (hX : ∀ a b, ‖X a b‖ ≤ 1) : mx X ≤ 1 := by
  unfold mx
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => hX a b

theorem cB_unitLie {k j ρ : ℕ} {u : List (B.Mat k (j + ρ))} (hu : unitP k j ρ u) :
    ∀ X ∈ u, B.unitLie k (j + ρ) X := fun X hX => ⟨(hu X hX).1.1, (hu X hX).2⟩

theorem cB_wP {k j ρ : ℕ} {u v : List (B.Mat k (j + ρ))} (hu : unitP k j ρ u) (hv : unitP k j ρ v) :
    ∀ x ∈ wL u ++ wR v, inLieP k j ρ x.2 ∧ ∀ a b, ‖x.2 a b‖ ≤ 1 := by
  intro x hx
  simp only [wL, wR, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
  · exact hu X hX
  · exact hv X hX

theorem cB_bound (hP : PolyB) (hC : DjCurve) {k j ρ κ : ℕ} {P : B.Mat k (j + ρ) → ℂ} (hPd : IsPolyDeg κ P)
    (a b n : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : List (B.Mat k (j + ρ)), unitP k j ρ u →
      unitP k j ρ v → u.length + v.length ≤ n → ∀ g ∈ B.GV k (j + ρ), δ ≤ ‖DjU k j ρ g‖ →
        ‖Dw (wL u ++ wR v) (fun g => P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b) g‖ ≤
          C * B.gN g ^ (κ : ℝ) := by
  obtain ⟨hPs, hWB⟩ := hP k (j + ρ) κ P hPd
  obtain ⟨CP, hCP⟩ := hWB n
  obtain ⟨lam, hlam⟩ := cB_curve hC k j ρ a b
  set Λ : ℝ := ((a + b : ℕ) : ℝ) * j with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  refine ⟨(1 + Λ) ^ n * (δ⁻¹ ^ (a + b) * |CP|), by positivity, ?_⟩
  intro u v hu hv hl g hg hDg
  have hw := cB_wP hu hv
  have e : (fun g => P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b) =
      fun g => hhF k j ρ a b g • P g := by
    funext g; simp only [hhF, smul_eq_mul]; ring
  rw [e, cA_Dw_expmul lam (hhF k j ρ a b) _ P hPs (fun x hx g t => (hlam x (hw x hx).1).2 g t), norm_smul]
  have hp := gN_pos hg
  have hD0 : 0 < ‖DjU k j ρ g‖ := lt_of_lt_of_le hδ hDg
  have hh : ‖hhF k j ρ a b g‖ ≤ δ⁻¹ ^ (a + b) := by
    unfold hhF
    rw [norm_mul, norm_pow, norm_pow, norm_inv, norm_inv, norm_star, pow_add]
    have : ‖DjU k j ρ g‖⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hDg
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) this a) (pow_le_pow_left₀ (by positivity) this b)
      (by positivity) (by positivity)
  have hb := cA_Dwl_bound lam hΛ0 g (|CP| * B.gN g ^ (κ : ℝ)) (wL u ++ wR v) P hPs
    (fun x hx => (hlam x (hw x hx).1).1.trans (by
      have := cB_mx_le (hw x hx).2
      calc ((a + b : ℕ) : ℝ) * j * mx x.2 ≤ ((a + b : ℕ) : ℝ) * j * 1 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = Λ := by rw [mul_one]))
    (by
      intro s hs
      obtain ⟨u', v', hu', hv', rfl⟩ := sub_LR hs
      rw [← dLR_eq]
      have := hCP u' v' (fun X hX => cB_unitLie hu X (hu'.subset hX)) (fun X hX => cB_unitLie hv X (hv'.subset hX))
        (by have := hu'.length_le; have := hv'.length_le; omega) g hg
      simp only [List.map_append, List.map_const', List.sum_append, Nat.cast_add] at this
      refine this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) |>.trans_eq ?_
      congr 2
      simp)
  have hpow : (1 + Λ) ^ (wL u ++ wR v).length ≤ (1 + Λ) ^ n := by
    rw [len_LR]; exact pow_le_pow_right₀ (by linarith) hl
  calc ‖hhF k j ρ a b g‖ * ‖Dwl lam (wL u ++ wR v) P g‖
      ≤ δ⁻¹ ^ (a + b) * ((1 + Λ) ^ n * (|CP| * B.gN g ^ (κ : ℝ))) :=
        mul_le_mul hh (hb.trans (mul_le_mul_of_nonneg_right hpow (by positivity))) (norm_nonneg _) (by positivity)
    _ = (1 + Λ) ^ n * (δ⁻¹ ^ (a + b) * |CP|) * B.gN g ^ (κ : ℝ) := by ring

end PI.UnitaryCorollaryDerivatives
end
end

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cCsec

variable {k j ρ : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cC_c_nonneg {r : ℕ} {A : ℝ} {m : ℕ} {f : B.Mat k r → E} {c : ℝ} (hf : B.CCle A m f c) : 0 ≤ c := by
  have h1 := Formalism.QuantumDeterminants.WeylGroupFacts.uh_one (k := k) (r := r)
  have h := hf.2 [] [] (by simp) (by simp) (by simp) 1 h1
  have hpos := gN_pos h1
  exact le_trans (mul_nonneg (Real.rpow_nonneg hpos.le _) (norm_nonneg _)) h

theorem cC_smul_ck {r : ℕ} {m : ℕ∞} {φ : B.Mat k r → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    {f : B.Mat k r → E} (hf : B.CkOn m (B.GV k r) f) : B.CkOn m (B.GV k r) (fun g => φ g • f g) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf g₀ hg₀
  refine ⟨U, fun g => φ g • f' g, hU, hgU, ?_, fun g hg hgv => by simp only [hff g hg hgv]⟩
  exact ((hφ.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn).smul hf'

theorem cC_Psi_ck {r : ℕ} {Q mm : ℕ} {φ : B.Mat k r → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    {f : B.Mat k r → E} (hf : B.CkOn (mm : ℕ∞) (B.GV k r) f) {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X)
    (hQ : Q + w.length ≤ mm) : B.CkOn (Q : ℕ∞) (B.GV k r) (B.Rw w (fun g => φ g • f g)) := by
  have h := cC_smul_ck hφ hf
  have hmono : B.CkOn ((Q + w.length : ℕ) : ℕ∞) (B.GV k r) (fun g => φ g • f g) := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hff⟩ := h g₀ hg₀
    exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast hQ), hff⟩
  have hR : B.Rw w (fun g => φ g • f g) = Dw (wL [] ++ wR w) (fun g => φ g • f g) := by
    rw [← dLR_eq]
    rfl
  rw [hR]
  apply CkOn_Dw
  · intro x hx
    simp only [wL, wR, List.map_nil, List.nil_append, List.mem_map] at hx
    obtain ⟨X, hX, rfl⟩ := hx
    exact hw X hX
  · simpa [wL, wR] using hmono

theorem cC_cost {Q o d : ℕ} {u v u₁ v₁ w : List (B.Mat k (j + ρ))} (hu : unitP k j ρ u) (hv : unitP k j ρ v)
    (hl : u.length + v.length ≤ Q) (hwo : w.length ≤ o) (hu₁ : u₁.Sublist u) (hv₁ : v₁.Sublist (v ++ w.map nrm)) :
    ((((u₁ ++ v₁).map (fun X => costP k j ρ X + d)).sum : ℕ) : ℝ) ≤ (j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) := by
  have hu0 : ∀ X ∈ u, costP k j ρ X = 0 := fun X hX => by simp [costP, (hu X hX).1]
  have hv0 : ∀ X ∈ v, costP k j ρ X = 0 := fun X hX => by simp [costP, (hv X hX).1]
  have hle : ∀ X, costP k j ρ X ≤ j := fun X => by
    unfold costP
    split_ifs <;> omega
  have hA : ((u₁ ++ v₁).map (costP k j ρ)).sum ≤ j * o := by
    rw [List.map_append, List.sum_append]
    have h1 : (u₁.map (costP k j ρ)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hx
      exact hu0 X (hu₁.subset hX)
    have h2 : (v₁.map (costP k j ρ)).sum ≤ ((v ++ w.map nrm).map (costP k j ρ)).sum :=
      (hv₁.map _).sum_le_sum (fun _ _ => Nat.zero_le _)
    have h3 : ((v ++ w.map nrm).map (costP k j ρ)).sum ≤ j * w.length := by
      rw [List.map_append, List.sum_append]
      have h0 : (v.map (costP k j ρ)).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hx
        exact hv0 X hX
      rw [h0, zero_add, List.map_map]
      calc ((w.map (costP k j ρ ∘ nrm))).sum ≤ (w.map (fun _ => j)).sum :=
            List.sum_le_sum (fun X _ => hle _)
        _ = j * w.length := by simp [mul_comm]
    have h4 : j * w.length ≤ j * o := Nat.mul_le_mul_left _ hwo
    omega
  have hL : (u₁ ++ v₁).length ≤ Q + o := by
    have := hu₁.length_le
    have := hv₁.length_le
    simp only [List.length_append, List.length_map] at *
    omega
  have key : ((u₁ ++ v₁).map (fun X => costP k j ρ X + d)).sum ≤ j * o + d * (Q + o) := by
    rw [List.sum_map_add]
    have hd : ((u₁ ++ v₁).map (fun _ => d)).sum = (u₁ ++ v₁).length * d := by simp
    rw [hd]
    have : (u₁ ++ v₁).length * d ≤ d * (Q + o) := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ hL
    omega
  exact_mod_cast key

theorem cC_bound {d Q o mm₀ : ℕ} {A₀ : ℝ} {φ : B.Mat k (j + ρ) → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) {Cφ : ℝ}
    (hWB : WB (fun X => costP k j ρ X + d) φ (Q + o) Cφ 0) {w : List (B.Mat k (j + ρ))}
    (hw : ∀ X ∈ w, B.inLie k (j + ρ) X) (hwo : w.length ≤ o) (hQ : Q + o ≤ mm₀) :
    ∃ CΨ : ℝ, 0 ≤ CΨ ∧ ∀ (f : B.Mat k (j + ρ) → E) (c : ℝ), B.CCle A₀ mm₀ f c →
      ∀ u v : List (B.Mat k (j + ρ)), unitP k j ρ u → unitP k j ρ v → u.length + v.length ≤ Q →
        ∀ g ∈ B.GV k (j + ρ), ‖B.dLR u v (B.Rw w (fun g => φ g • f g)) g‖ ≤
          CΨ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) := by
  classical
  have h1 := Formalism.QuantumDeterminants.WeylGroupFacts.uh_one (k := k) (r := j + ρ)
  have hCφ : 0 ≤ Cφ := by
    have h := hWB [] [] (by simp) (by simp) (by simp) 1 h1
    have hX := Real.rpow_pos_of_pos (gN_pos h1)
      ((0 : ℝ) + ((([] ++ [] : List (B.Mat k (j + ρ))).map (fun X => costP k j ρ X + d)).sum : ℕ))
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg hX
    linarith [norm_nonneg (B.dLR [] [] φ 1)]
  have hw'lie : ∀ X ∈ w.map nrm, B.unitLie k (j + ρ) X := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact nrm_unit (hw Y hY)
  obtain ⟨a, ha⟩ : ∃ a : B.Mat k (j + ρ) → (E →L[ℂ] E),
      a = fun g => φ g • ContinuousLinearMap.id ℂ E := ⟨_, rfl⟩
  have ha_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a := by
    rw [ha]
    exact hφ.smul contDiff_const
  have hφU : ∀ n : ℕ∞, B.CkOn n Set.univ φ := fun n g₀ _ =>
    ⟨Set.univ, φ, isOpen_univ, trivial, hφ.contDiffOn.of_le (WithTop.coe_le_coe.2 le_top),
      fun _ _ _ => rfl⟩
  refine ⟨|((w.map nz).prod : ℝ)| * 2 ^ (Q + o) * Cφ, mul_nonneg (by positivity) hCφ,
    fun f c hf u v hu hv hl g hg => ?_⟩
  have hc : 0 ≤ c := cC_c_nonneg hf
  have hgN := gN_ge_one hg
  have hgN0 := gN_pos hg
  have hG : B.CkOn ((u.length + v.length : ℕ) : ℕ∞) (B.GV k (j + ρ))
      (B.Rw (w.map nrm) (fun g => φ g • f g)) :=
    cC_Psi_ck hφ hf.1 (fun X hX => (hw'lie X hX).1) (by simp only [List.length_map]; omega)
  obtain ⟨V, G', hVo, hgV, hG'c, hG'eq⟩ := hG g hg
  have hGV : B.CkOn ((u.length + v.length : ℕ) : ℕ∞) V (B.Rw (w.map nrm) (fun g => φ g • f g)) :=
    fun g₀ hg₀ => ⟨V, G', hVo, hg₀, hG'c, hG'eq⟩
  have hscale := cA_Dw_clm (E' := E) ((((w.map nz).prod : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E) hVo
    (wL u ++ wR v) (fun x hx => ((cB_wP hu hv) x hx).1.1) (by simpa [wL, wR] using hGV) g hg hgV
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hscale
  have hsplit : Dw (wL u ++ wR (v ++ w.map nrm)) (fun g => φ g • f g) =
      Dw (wL u ++ wR v) (B.Rw (w.map nrm) (fun g => φ g • f g)) := by
    rw [show wR (v ++ w.map nrm) = wR v ++ wR (w.map nrm) from List.map_append,
      ← List.append_assoc, Dw_append, Dw_wR]
  have hF : (fun g => φ g • f g) = ap a f := by
    funext g
    simp [ap, ha]
  have hW'lie : ∀ x ∈ wL u ++ wR (v ++ w.map nrm), B.inLie k (j + ρ) x.2 := by
    intro x hx
    simp only [wL, wR, List.map_append, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact (hu X hX).1.1
    · exact (hv X hX).1.1
    · exact (hw'lie X (List.mem_map.2 hX)).1
  have hlen : (wL u ++ wR (v ++ w.map nrm)).length = u.length + v.length + w.length := by
    simp [wL, wR]
    omega
  have hPr : Pr ∅ Set.univ ((wL u ++ wR (v ++ w.map nrm)).length : ℕ∞) a f := by
    refine ⟨fun g₀ _ => ⟨Set.univ, a, isOpen_univ, trivial,
      ha_smooth.contDiffOn.of_le (WithTop.coe_le_coe.2 le_top), fun _ _ _ => rfl⟩, fun g₀ hg₀ => ?_,
      fun g _ hg => absurd hg (Set.notMem_empty g)⟩
    obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf.1 g₀ hg₀
    refine ⟨U, f', hU, hgU, hf'.of_le ?_, hff⟩
    rw [hlen]
    exact_mod_cast (by omega : u.length + v.length + w.length ≤ mm₀)
  have hbound : ∀ w₁ w₂ : List (Bool × B.Mat k (j + ρ)), w₁.Sublist (wL u ++ wR (v ++ w.map nrm)) →
      w₂.Sublist (wL u ++ wR (v ++ w.map nrm)) → w₁.length + w₂.length = (wL u ++ wR (v ++ w.map nrm)).length →
      ‖Dw w₁ a g‖ * ‖Dw w₂ f g‖ ≤ Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) := by
    intro w₁ w₂ hw₁ hw₂ _
    obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR hw₁
    obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR hw₂
    have hunit : ∀ X ∈ v ++ w.map nrm, B.unitLie k (j + ρ) X := by
      intro X hX
      rcases List.mem_append.1 hX with hX | hX
      · exact cB_unitLie hv X hX
      · exact hw'lie X hX
    have hA : ‖Dw (wL u₁ ++ wR v₁) a g‖ ≤ Cφ * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ)) := by
      have hDa := cA_Dw_clm (E := ℂ) (E' := E →L[ℂ] E)
        (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) (ContinuousLinearMap.id ℂ E))
        isOpen_univ (wL u₁ ++ wR v₁) (fun x hx => hW'lie x (hw₁.subset hx)) (hφU _) g hg trivial
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply] at hDa
      rw [ha, hDa, norm_smul, ← dLR_eq]
      have hWB1 := hWB u₁ v₁ (fun X hX => cB_unitLie hu X (hu₁.subset hX))
        (fun X hX => hunit X (hv₁.subset hX))
        (by have := hu₁.length_le; have := hv₁.length_le; simp only [List.length_append, List.length_map] at *; omega) g hg
      have hcost := cC_cost hu hv hl hwo hu₁ hv₁ (d := d)
      have hexp : B.gN g ^ ((0 : ℝ) + ((((u₁ ++ v₁).map (fun X => costP k j ρ X + d)).sum : ℕ) : ℝ)) ≤
          B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hgN (by linarith)
      calc ‖B.dLR u₁ v₁ φ g‖ * ‖ContinuousLinearMap.id ℂ E‖ ≤ ‖B.dLR u₁ v₁ φ g‖ * 1 :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (norm_nonneg _)
        _ ≤ Cφ * B.gN g ^ ((0 : ℝ) + ((((u₁ ++ v₁).map (fun X => costP k j ρ X + d)).sum : ℕ) : ℝ)) := by
            rw [mul_one]; exact hWB1
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp hCφ
    have hB : ‖Dw (wL u₂ ++ wR v₂) f g‖ ≤ c * B.gN g ^ (-A₀) := by
      rw [← dLR_eq]
      have h2 := hf.2 u₂ v₂ (fun X hX => cB_unitLie hu X (hu₂.subset hX))
        (fun X hX => hunit X (hv₂.subset hX))
        (by have := hu₂.length_le; have := hv₂.length_le; simp only [List.length_append, List.length_map] at *; omega) g hg
      rw [Real.rpow_neg hgN0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hgN0 _), mul_comm]
      exact h2
    calc ‖Dw (wL u₁ ++ wR v₁) a g‖ * ‖Dw (wL u₂ ++ wR v₂) f g‖
        ≤ (Cφ * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ))) * (c * B.gN g ^ (-A₀)) :=
          mul_le_mul hA hB (norm_nonneg _) (mul_nonneg hCφ (Real.rpow_nonneg hgN0.le _))
      _ = Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) := by
          rw [sub_eq_add_neg, Real.rpow_add hgN0 ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ)) (-A₀)]
          ring
  have hleib := leib_bound isOpen_empty (fun g _ => Or.inr trivial) g hg
    (Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀)) (wL u ++ wR (v ++ w.map nrm)) a f
    hW'lie hPr hbound
  have hM : 0 ≤ Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) :=
    mul_nonneg (mul_nonneg hCφ hc) (Real.rpow_nonneg hgN0.le _)
  have hpow : (2 : ℝ) ^ (wL u ++ wR (v ++ w.map nrm)).length ≤ 2 ^ (Q + o) :=
    pow_le_pow_right₀ (by norm_num) (by rw [hlen]; omega)
  calc ‖B.dLR u v (B.Rw w (fun g => φ g • f g)) g‖
      = |((w.map nz).prod : ℝ)| * ‖Dw (wL u ++ wR (v ++ w.map nrm)) (ap a f) g‖ := by
        rw [Rw_scale, dLR_eq, hscale, norm_smul, Complex.norm_real, Real.norm_eq_abs, ← hF, hsplit]
    _ ≤ |((w.map nz).prod : ℝ)| * (2 ^ (wL u ++ wR (v ++ w.map nrm)).length *
          (Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀))) :=
        mul_le_mul_of_nonneg_left hleib (abs_nonneg _)
    _ ≤ |((w.map nz).prod : ℝ)| * (2 ^ (Q + o) *
          (Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hM) (abs_nonneg _)
    _ = |((w.map nz).prod : ℝ)| * 2 ^ (Q + o) * Cφ * c *
          B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) := by ring

end cCsec

end PI.UnitaryCorollaryDerivatives
end
end

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cDsec

variable {k j ρ : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Good (k j ρ Q : ℕ) (A₁ : ℝ) (O : Set (B.Mat k (j + ρ))) (F : B.Mat k (j + ρ) → E) (C c : ℝ) : Prop :=
  B.CkOn (Q : ℕ∞) (B.GV k (j + ρ)) F ∧ (∀ g ∈ B.GV k (j + ρ), g ∈ O → F g = 0) ∧
  ∀ u v : List (B.Mat k (j + ρ)), unitP k j ρ u → unitP k j ρ v → u.length + v.length ≤ Q →
    ∀ g ∈ B.GV k (j + ρ), B.gN g ^ A₁ * ‖B.dLR u v F g‖ ≤ C * c

theorem cD_add {Q : ℕ} {A₁ : ℝ} {O : Set (B.Mat k (j + ρ))} {F₁ F₂ : B.Mat k (j + ρ) → E} {C₁ C₂ c : ℝ}
    (h₁ : Good k j ρ Q A₁ O F₁ C₁ c) (h₂ : Good k j ρ Q A₁ O F₂ C₂ c) :
    Good k j ρ Q A₁ O (fun g => F₁ g + F₂ g) (C₁ + C₂) c := by
  obtain ⟨hc1, hz1, hb1⟩ := h₁
  obtain ⟨hc2, hz2, hb2⟩ := h₂
  refine ⟨CkOn_add hc1 hc2, fun g hg hO => by simp only [hz1 g hg hO, hz2 g hg hO, add_zero], ?_⟩
  intro u v hu hv hl g hg
  have hw : ∀ x ∈ wL u ++ wR v, B.inLie k (j + ρ) x.2 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx
      exact (hu X hX).1.1
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx
      exact (hv X hX).1.1
  have hlen : (((wL u ++ wR v).length : ℕ) : ℕ∞) ≤ (Q : ℕ∞) := by
    simp only [wL, wR, List.length_append, List.length_map]
    exact_mod_cast hl
  have hadd := Dw_add hw (sCkOn_mono hlen hc1) (sCkOn_mono hlen hc2) g hg
  have e1 := hb1 u v hu hv hl g hg
  have e2 := hb2 u v hu hv hl g hg
  rw [dLR_eq] at e1 e2 ⊢
  rw [hadd]
  have hpos : 0 ≤ B.gN g ^ A₁ := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  calc B.gN g ^ A₁ * ‖Dw (wL u ++ wR v) F₁ g + Dw (wL u ++ wR v) F₂ g‖ ≤
        B.gN g ^ A₁ * (‖Dw (wL u ++ wR v) F₁ g‖ + ‖Dw (wL u ++ wR v) F₂ g‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hpos
    _ = B.gN g ^ A₁ * ‖Dw (wL u ++ wR v) F₁ g‖ + B.gN g ^ A₁ * ‖Dw (wL u ++ wR v) F₂ g‖ :=
        mul_add _ _ _
    _ ≤ C₁ * c + C₂ * c := add_le_add e1 e2
    _ = (C₁ + C₂) * c := by ring

theorem cD_list {ι : Type*} {Q : ℕ} {A₁ : ℝ} {O : Set (B.Mat k (j + ρ))} {E₀ : Type*}
    (F : ι → E₀ → B.Mat k (j + ρ) → E) (Pf : E₀ → ℝ → Prop) :
    ∀ l : List ι, (∀ i ∈ l, ∃ C : ℝ, 0 ≤ C ∧ ∀ f c, Pf f c → Good k j ρ Q A₁ O (F i f) C c) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f c, Pf f c → Good k j ρ Q A₁ O (fun g => (l.map fun i => F i f g).sum) C c := by
  intro l
  induction l with
  | nil =>
    intro _
    refine ⟨0, le_rfl, fun f c _ => ⟨?_, fun g _ _ => by simp, fun u v _ _ _ g _ => ?_⟩⟩
    · simpa using (CkOn_zero (m := (Q : ℕ∞)) (UU := B.GV k (j + ρ)) (E := E))
    · simp only [List.map_nil, List.sum_nil]
      rw [dLR_eq, Dw_zero]
      simp
  | cons a l ih =>
    intro h
    obtain ⟨C₁, hC₁, h₁⟩ := h a (List.mem_cons_self ..)
    obtain ⟨C₂, hC₂, h₂⟩ := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun f c hf => ?_⟩
    have := cD_add (h₁ f c hf) (h₂ f c hf)
    simpa only [List.map_cons, List.sum_cons] using this

theorem cD_delta {χ : ℂ → ℂ} (hχ : IsCutC χ) : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ tsupport χ, δ ≤ ‖z‖ := by
  obtain ⟨-, -, h0⟩ := hχ
  have ho : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho 0 h0
  refine ⟨ε, hε, fun z hz => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact hball (by simpa [Metric.mem_ball, dist_zero_right] using hlt) hz

end cDsec

section cDterm

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem cD_term (hP : PolyB) (hC : DjCurve) {k j ρ κ d Q o mm₀ : ℕ} {A₀ : ℝ}
    (hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (DjU k j ρ)) {χ : ℂ → ℂ} (hχ : IsCutC χ) {δ : ℝ} (hδ : 0 < δ)
    (hδχ : ∀ z ∈ tsupport χ, δ ≤ ‖z‖) {φ : B.Mat k (j + ρ) → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφ0 : ∀ g, DjU k j ρ g ∉ tsupport χ → φ g = 0) {Cφ : ℝ}
    (hWB : WB (fun X => costP k j ρ X + d) φ (Q + o) Cφ 0) (hQ : Q + o ≤ mm₀)
    (T : B.DTerm k (j + ρ) Wp Wq)
    (hT : T.word.length ≤ o ∧ ∃ (P : B.Mat k (j + ρ) → ℂ) (a b : ℕ), IsPolyDeg κ P ∧
      ∀ g, T.coef g = (P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b) •
        ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : B.Mat k (j + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ mm₀ f c →
      Good k j ρ Q (A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ))
        {g | DjU k j ρ g ∉ tsupport χ} (ap T.coef (B.Rw T.word (fun g => φ g • f g))) C c := by
  obtain ⟨hwo, P, a, b, hPd, hcoef⟩ := hT
  have hPs := (hP k (j + ρ) κ P hPd).1
  set s : B.Mat k (j + ρ) → ℂ := fun g => P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b with hs
  set Lid : ℂ →L[ℂ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
    ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
  have hLn : ∀ z : ℂ, ‖Lid z‖ ≤ ‖z‖ := by
    intro z
    simp only [Lid, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, norm_smul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_id_le))
  have hce : T.coef = fun g => Lid (s g) := by
    funext g; rw [hcoef g]; simp [Lid, s]
  set O : Set (B.Mat k (j + ρ)) := {g | DjU k j ρ g ∉ tsupport χ}
  have hO : IsOpen O := (isClosed_tsupport χ).isOpen_compl.preimage hD.continuous
  set UU : Set (B.Mat k (j + ρ)) := {g | DjU k j ρ g ≠ 0}
  have hUU : IsOpen UU := isOpen_ne_fun hD.continuous continuous_const
  have hcov : ∀ g ∈ B.GV k (j + ρ), g ∈ O ∨ g ∈ UU := by
    intro g _
    by_cases h : DjU k j ρ g ∈ tsupport χ
    · right; intro h0; exact hχ.2.2 (h0 ▸ h)
    · left; exact h
  have hsUU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s UU := cB_smooth hD hPs a b
  have hsCk : ∀ m : ℕ∞, B.CkOn m UU s := fun m g₀ hg₀ =>
    ⟨UU, s, hUU, hg₀, hsUU.of_le (by exact_mod_cast le_top), fun _ _ _ => rfl⟩
  have hcoefCk : ∀ m : ℕ∞, B.CkOn m UU T.coef := fun m g₀ hg₀ =>
    ⟨UU, T.coef, hUU, hg₀, by
      rw [hce]; exact ((Lid.restrictScalars ℝ).contDiff.comp_contDiffOn hsUU).of_le (by exact_mod_cast le_top),
      fun _ _ _ => rfl⟩
  obtain ⟨CB, hCB0, hCB⟩ := cB_bound hP hC hPd a b Q hδ
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := cC_bound (E := Wq →L[ℂ] Wp) (A₀ := A₀) hφ hWB T.word_lie hwo hQ
  refine ⟨2 ^ Q * CB * CΨ, by positivity, fun f c hf => ?_⟩
  have hc0 := cC_c_nonneg hf
  set Ψ := B.Rw T.word (fun g => φ g • f g) with hΨ
  have hΨck : B.CkOn (Q : ℕ∞) (B.GV k (j + ρ)) Ψ := cC_Psi_ck hφ hf.1 T.word_lie (by omega)
  have hΨz : ∀ g ∈ B.GV k (j + ρ), g ∈ O → Ψ g = 0 :=
    Rw_vanish hO T.word_lie (fun g _ hgO => by simp [hφ0 g hgO])
  have hPr : Pr O UU (Q : ℕ∞) T.coef Ψ := ⟨hcoefCk Q, hΨck, hΨz⟩
  refine ⟨hPr.ck hO hcov, fun g hg hgO => (hPr.mono zero_le).apz g hg hgO, ?_⟩
  intro u v hu hv hl g hg
  have hlie := lie_LR (fun X hX => (hu X hX).1.1) (fun X hX => (hv X hX).1.1)
  have hp := gN_pos hg
  rw [dLR_eq]
  by_cases hgO : g ∈ O
  · rw [Dw_vanish hO hlie (hPr.mono zero_le).apz g hg hgO]
    simp only [norm_zero, mul_zero]
    positivity
  · have hDg : DjU k j ρ g ∈ tsupport χ := not_not.mp hgO
    have hgU : g ∈ UU := fun h0 => hχ.2.2 (h0 ▸ hDg)
    have hδg := hδχ _ hDg
    set Eφ : ℝ := (j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) with hEφ
    set M : ℝ := CB * B.gN g ^ (κ : ℝ) * (CΨ * c * B.gN g ^ (Eφ - A₀)) with hM
    have hM0 : 0 ≤ M := by positivity
    have hb := leib_bound hO hcov g hg M (wL u ++ wR v) T.coef Ψ hlie
      (hPr.mono (by rw [len_LR]; exact_mod_cast hl)) (by
        intro w₁ w₂ h₁ h₂ _
        obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR h₁
        obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR h₂
        have hu₁P : unitP k j ρ u₁ := fun X hX => hu X (hu₁.subset hX)
        have hv₁P : unitP k j ρ v₁ := fun X hX => hv X (hv₁.subset hX)
        have hu₂P : unitP k j ρ u₂ := fun X hX => hu X (hu₂.subset hX)
        have hv₂P : unitP k j ρ v₂ := fun X hX => hv X (hv₂.subset hX)
        have hlie₁ := lie_LR (fun X hX => (hu₁P X hX).1.1) (fun X hX => (hv₁P X hX).1.1)
        have hl₁ : u₁.length + v₁.length ≤ Q := by
          have := hu₁.length_le; have := hv₁.length_le; omega
        have hl₂ : u₂.length + v₂.length ≤ Q := by
          have := hu₂.length_le; have := hv₂.length_le; omega
        rw [hce, cA_Dw_clm Lid hUU _ hlie₁ (hsCk _) g hg hgU, ← dLR_eq]
        have b1 : ‖Lid (B.dLR u₁ v₁ s g)‖ ≤ CB * B.gN g ^ (κ : ℝ) :=
          (hLn _).trans (by rw [dLR_eq]; exact hCB u₁ v₁ hu₁P hv₁P hl₁ g hg hδg)
        have b2 : ‖Dw (wL u₂ ++ wR v₂) Ψ g‖ ≤ CΨ * c * B.gN g ^ (Eφ - A₀) := by
          rw [← dLR_eq]; exact hCΨ f c hf u₂ v₂ hu₂P hv₂P hl₂ g hg
        exact mul_le_mul b1 b2 (norm_nonneg _) (by positivity))
    have hexp : B.gN g ^ (A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ)) *
        B.gN g ^ (κ : ℝ) * B.gN g ^ (Eφ - A₀) = 1 := by
      rw [← Real.rpow_add hp, ← Real.rpow_add hp]
      rw [show A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ) + (κ : ℝ) + (Eφ - A₀) = 0 by
        rw [hEφ]; ring]
      exact Real.rpow_zero _
    have hpow : (2 : ℝ) ^ (wL u ++ wR v).length ≤ 2 ^ Q := by
      rw [len_LR]; exact pow_le_pow_right₀ (by norm_num) hl
    calc B.gN g ^ (A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ)) *
          ‖Dw (wL u ++ wR v) (ap T.coef Ψ) g‖
        ≤ B.gN g ^ (A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ)) * (2 ^ Q * M) :=
          mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right hpow hM0))
            (Real.rpow_nonneg hp.le _)
      _ = 2 ^ Q * CB * CΨ * c * (B.gN g ^ (A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ)) *
          B.gN g ^ (κ : ℝ) * B.gN g ^ (Eφ - A₀)) := by rw [hM]; ring
      _ = 2 ^ Q * CB * CΨ * c := by rw [hexp, mul_one]

end cDterm

theorem coreStar_of (hP : PolyB) (hDp : DjPoly) (hC : DjCurve) : CoreStar := by
  intro k j ρ Wp Wq _ _ _ _ _ o κ d Θ χ φ hΘ hχ Q mm₀ A₀ hQ hφ hφ0 hWBe
  obtain ⟨Cφ, hWB⟩ := hWBe
  have hD := (hP k (j + ρ) j (DjU k j ρ) (hDp k j ρ)).1
  obtain ⟨δ, hδ, hδχ⟩ := cD_delta hχ
  obtain ⟨C, _, hCg⟩ := cD_list (k := k) (j := j) (ρ := ρ) (Q := Q)
    (A₁ := A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ)) (O := {g | DjU k j ρ g ∉ tsupport χ})
    (fun (T : B.DTerm k (j + ρ) Wp Wq) (f : B.Mat k (j + ρ) → (Wq →L[ℂ] Wp)) =>
      ap T.coef (B.Rw T.word (fun g => φ g • f g)))
    (fun f c => B.CCle A₀ mm₀ f c) Θ
    (fun T hT => cD_term hP hC hD hχ hδ hδχ hφ hφ0 hWB hQ T (hΘ T hT))
  refine ⟨C, fun f c hf => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hCg f c hf
  refine ⟨h1, fun g hg hne => ?_, h3⟩
  by_contra hK
  exact hne (h2 g hg (fun hD' => hK ⟨_, hD', rfl⟩))

end PI.UnitaryCorollaryDerivatives
end
end

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem star_estimate_unitary : CoreStar :=
  coreStar_of polynomial_bound determinant_derivative_polynomial determinant_curve_derivative

end PI.UnitaryCorollaryDerivatives
