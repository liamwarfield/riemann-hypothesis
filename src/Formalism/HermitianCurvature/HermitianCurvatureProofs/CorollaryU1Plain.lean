module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UsCompose
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.StarEstimateUnitary
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CompactRegionEstimate
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UsCost

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CutoffPlainAndSmoothed
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.UnitaryCorollaryBothForms
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CompactCurveEstimate
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CompCA
open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace PI.UnitaryCorollaryDerivatives.CCA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma hasDx (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) (g : Mat k r) :
    HasDerivAt (fun t : ℝ => f (crv x g t)) (Dx x f g) 0 := by
  have h1 : HasFDerivAt f (fderiv ℝ f g) (crv x g 0) := by rw [crv_zero]; exact (hf g).hasFDerivAt
  have h2 := h1.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)
  have e : Dx x f g = fderiv ℝ f g (dirv x g) := by rw [Dx_eq]; exact h2.deriv
  rw [e]; exact h2

lemma Dx_fd (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) :
    Dx x f = fun g => fderiv ℝ f g (dirL x g) := by
  funext g
  rw [dirL_apply, Dx_eq]
  have h1 : HasFDerivAt f (fderiv ℝ f g) (crv x g 0) := by rw [crv_zero]; exact (hf g).hasFDerivAt
  exact (h1.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)).deriv

lemma sm_diff {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f := by
  first
  | exact hf.differentiable (by simp)
  | exact hf.differentiable le_top
  | exact hf.differentiable (by norm_num)

lemma sm_Dx (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dx x f) := by
  rw [Dx_fd x (sm_diff hf)]
  first
  | exact (hf.fderiv_right (m := ∞) le_rfl).clm_apply (dirL x).contDiff
  | exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply (dirL x).contDiff
  | exact (hf.fderiv_right (m := ∞) (by norm_num)).clm_apply (dirL x).contDiff

lemma sm_Dw (w : List (Bool × Mat k r)) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dw w f) := by
  induction w with
  | nil => exact hf
  | cons x w ih => exact sm_Dx x ih

lemma Dx_add' (x : Bool × Mat k r) {f₁ f₂ : Mat k r → ℂ} (h₁ : Differentiable ℝ f₁)
    (h₂ : Differentiable ℝ f₂) : Dx x (fun g => f₁ g + f₂ g) = fun g => Dx x f₁ g + Dx x f₂ g := by
  funext g
  exact (hasDx x (h₁.add h₂) g).unique ((hasDx x h₁ g).add (hasDx x h₂ g))

lemma Dw_add' (w : List (Bool × Mat k r)) {f₁ f₂ : Mat k r → ℂ} (h₁ : ContDiff ℝ ∞ f₁)
    (h₂ : ContDiff ℝ ∞ f₂) : Dw w (fun g => f₁ g + f₂ g) = fun g => Dw w f₁ g + Dw w f₂ g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => f₁ g + f₂ g) = _
    rw [ih]
    exact Dx_add' x (sm_diff (sm_Dw w h₁)) (sm_diff (sm_Dw w h₂))

lemma Dx_mul' (x : Bool × Mat k r) {a b : Mat k r → ℂ} (ha : Differentiable ℝ a)
    (hb : Differentiable ℝ b) : Dx x (fun g => a g * b g) = fun g => Dx x a g * b g + a g * Dx x b g := by
  funext g
  have h0 : crv x g 0 = g := by simp [crv]
  have h := (hasDx x ha g).mul (hasDx x hb g)
  rw [h0] at h
  exact (hasDx x (ha.mul hb) g).unique h

lemma Dx_clm (x : Bool × Mat k r) (L : ℂ →L[ℝ] ℂ) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) :
    Dx x (fun g => L (f g)) = fun g => L (Dx x f g) := by
  funext g
  exact (hasDx x (L.differentiable.comp hf) g).unique (L.hasFDerivAt.comp_hasDerivAt _ (hasDx x hf g))

lemma Dw_clm (w : List (Bool × Mat k r)) (L : ℂ →L[ℝ] ℂ) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) :
    Dw w (fun g => L (f g)) = fun g => L (Dw w f g) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => L (f g)) = _
    rw [ih]
    exact Dx_clm x L (sm_diff (sm_Dw w hf))

lemma Dw_snoc (w : List (Bool × Mat k r)) (x : Bool × Mat k r) (f : Mat k r → ℂ) :
    Dw (w ++ [x]) f = Dw w (Dx x f) := by
  unfold Dw
  rw [List.foldr_append]
  rfl

lemma leibC (g : Mat k r) (w : List (Bool × Mat k r)) :
    ∀ (a b : Mat k r → ℂ), ContDiff ℝ ∞ a → ContDiff ℝ ∞ b → ∀ M : ℝ,
      (∀ w₁ w₂ : List (Bool × Mat k r), w₁.Sublist w → w₂.Sublist w → (w₁ ++ w₂).Perm w →
        ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) →
      ‖Dw w (fun g => a g * b g) g‖ ≤ 2 ^ w.length * M := by
  induction w using List.reverseRecOn with
  | nil =>
    intro a b ha hb M hM
    simpa [Dw, norm_mul] using hM [] [] (by simp) (by simp) (by simp)
  | append_singleton w x ih =>
    intro a b ha hb M hM
    rw [Dw_snoc, Dx_mul' x (sm_diff ha) (sm_diff hb),
      Dw_add' w ((sm_Dx x ha).mul hb) (ha.mul (sm_Dx x hb))]
    have h1 := ih (Dx x a) b (sm_Dx x ha) hb M (fun w₁ w₂ s1 s2 p => by
      have e : w₁ ++ [x] ++ w₂ = w₁ ++ x :: w₂ := by simp
      have hp : (w₁ ++ [x] ++ w₂).Perm (w ++ [x]) := by
        rw [e]
        exact List.perm_middle.trans ((p.cons x).trans (List.perm_append_singleton x w).symm)
      have := hM (w₁ ++ [x]) w₂ (s1.append (List.Sublist.refl _))
        (s2.trans (List.sublist_append_left _ _)) hp
      rwa [Dw_snoc] at this)
    have h2 := ih a (Dx x b) ha (sm_Dx x hb) M (fun w₁ w₂ s1 s2 p => by
      have hp : (w₁ ++ (w₂ ++ [x])).Perm (w ++ [x]) := by
        rw [← List.append_assoc]
        exact p.append_right [x]
      have := hM w₁ (w₂ ++ [x]) (s1.trans (List.sublist_append_left _ _))
        (s2.append (List.Sublist.refl _)) hp
      rwa [Dw_snoc] at this)
    calc _ ≤ ‖Dw w (fun g => Dx x a g * b g) g‖ + ‖Dw w (fun g => a g * Dx x b g) g‖ := norm_add_le _ _
      _ ≤ 2 ^ w.length * M + 2 ^ w.length * M := add_le_add h1 h2
      _ = 2 ^ (w ++ [x]).length * M := by
        rw [List.length_append, List.length_singleton, pow_succ]
        ring

def reC : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

def imC : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM

lemma reC_apply (z : ℂ) : reC z = (z.re : ℂ) := rfl

lemma imC_apply (z : ℂ) : imC z = (z.im : ℂ) := rfl

lemma norm_reC (z : ℂ) : ‖reC z‖ ≤ ‖z‖ := by
  rw [reC_apply, Complex.norm_real, Real.norm_eq_abs]
  first
  | exact Complex.abs_re_le_norm z
  | exact Complex.abs_re_le_abs z

lemma norm_imC (z : ℂ) : ‖imC z‖ ≤ ‖z‖ := by
  rw [imC_apply, Complex.norm_real, Real.norm_eq_abs]
  first
  | exact Complex.abs_im_le_norm z
  | exact Complex.abs_im_le_abs z

lemma clm_split (L : ℂ →L[ℝ] ℂ) (d : ℂ) : L d = L 1 * reC d + L Complex.I * imC d := by
  have h : d = (d.re : ℝ) • (1 : ℂ) + (d.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [h]
  rw [map_add (f := _), map_smul, map_smul, reC_apply, imC_apply, Complex.real_smul, Complex.real_smul]
  ring

lemma Dx_comp (x : Bool × Mat k r) {χ : ℂ → ℂ} {ψ : Mat k r → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hψ : ContDiff ℝ ∞ ψ) :
    Dx x (fun g => χ (ψ g)) = fun g => (fun z => fderiv ℝ χ z 1) (ψ g) * reC (Dx x ψ g)
      + (fun z => fderiv ℝ χ z Complex.I) (ψ g) * imC (Dx x ψ g) := by
  funext g
  have h0 : crv x g 0 = g := by simp [crv]
  have hχd : Differentiable ℝ χ := by
    first
    | exact hχ.differentiable (by simp)
    | exact hχ.differentiable le_top
    | exact hχ.differentiable (by norm_num)
  have h1 := hasDx x (sm_diff hψ) g
  have h2 : HasFDerivAt χ (fderiv ℝ χ (ψ g)) (ψ (crv x g 0)) := by
    rw [h0]; exact (hχd (ψ g)).hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  have h4 := hasDx x (sm_diff (hχ.comp hψ)) g
  have h5 : Dx x (fun g => χ (ψ g)) g = fderiv ℝ χ (ψ g) (Dx x ψ g) := h4.unique h3
  rw [h5, clm_split]

lemma sm_fd {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ) (v : ℂ) : ContDiff ℝ ∞ (fun z => fderiv ℝ χ z v) := by
  first
  | exact (hχ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  | exact (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  | exact (hχ.fderiv_right (m := ∞) (by norm_num)).clm_apply contDiff_const

end PI.UnitaryCorollaryDerivatives.CCA
end
end

open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LatticeLocalGlobalTheory

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CCA

variable {k r : ℕ}

def Good (k r n : ℕ) (w : List (Bool × B.Mat k r)) : Prop :=
  ∃ u v : List (B.Mat k r), (∀ X ∈ u, unitLie k r X) ∧ (∀ X ∈ v, unitLie k r X) ∧
    u.length + v.length ≤ n ∧ w = wL u ++ wR v

lemma Good.sub {n : ℕ} {w w' : List (Bool × B.Mat k r)} (h : Good k r n w) (hs : w'.Sublist w) :
    Good k r n w' := by
  obtain ⟨u, v, hu, hv, hl, rfl⟩ := h
  obtain ⟨r₁, r₂, rfl, h1, h2⟩ := List.sublist_append_iff.1 hs
  obtain ⟨u', hu', rfl⟩ := List.sublist_map_iff.1 (show r₁.Sublist (u.map (Prod.mk true)) from h1)
  obtain ⟨v', hv', rfl⟩ := List.sublist_map_iff.1 (show r₂.Sublist (v.map (Prod.mk false)) from h2)
  refine ⟨u', v', fun X hX => hu X (hu'.subset hX), fun X hX => hv X (hv'.subset hX), ?_, rfl⟩
  have := hu'.length_le
  have := hv'.length_le
  omega

def cw (cost : B.Mat k r → ℕ) (w : List (Bool × B.Mat k r)) : ℕ := (w.map (fun x => cost x.2)).sum

lemma cw_perm (cost : B.Mat k r → ℕ) {w₁ w₂ w : List (Bool × B.Mat k r)} (hp : (w₁ ++ w₂).Perm w) :
    cw cost w₁ + cw cost w₂ = cw cost w := by
  unfold cw
  rw [← List.sum_append, ← List.map_append]
  exact (hp.map _).sum_eq

lemma cw_LR (cost : B.Mat k r → ℕ) (u v : List (B.Mat k r)) :
    cw cost (wL u ++ wR v) = ((u ++ v).map cost).sum := by
  simp [cw, wL, wR, List.map_append, List.map_map, Function.comp_def]

lemma gN_nn (g : B.Mat k r) : 0 ≤ gN g := by
  first
  | (unfold gN; positivity)
  | (simp only [gN]; positivity)
  | (unfold B.gN; positivity)

theorem faa (n : ℕ) (cost : B.Mat k r → ℕ) (ψ : B.Mat k r → ℂ) (hψ : ContDiff ℝ ∞ ψ) (K : Set ℂ)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (H : ∀ w, Good k r n w → w ≠ [] → ∀ g ∈ GV k r, ψ g ∈ K → ‖Dw w ψ g‖ ≤ C₀ * gN g ^ cw cost w) :
    ∀ m : ℕ, ∀ χ : ℂ → ℂ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ w, Good k r n w → w.length ≤ m → ∀ g ∈ GV k r, ψ g ∈ K →
        ‖Dw w (fun g => χ (ψ g)) g‖ ≤ C * gN g ^ cw cost w := by
  intro m
  induction m with
  | zero =>
    intro χ hχ hχc
    obtain ⟨c, hc⟩ := hχ.continuous.bounded_above_of_compact_support hχc
    refine ⟨max c 0, le_max_right _ _, fun w _ hw g _ _ => ?_⟩
    have : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw)
    subst this
    simp only [Dw, List.foldr_nil, cw, List.map_nil, List.sum_nil, pow_zero, mul_one]
    exact (hc _).trans (le_max_left _ _)
  | succ m ih =>
    intro χ hχ hχc
    obtain ⟨K₀, hK₀, h₀⟩ := ih χ hχ hχc
    obtain ⟨K₁, hK₁, h₁⟩ := ih _ (sm_fd hχ 1) (hχc.fderiv_apply (𝕜 := ℝ) 1)
    obtain ⟨K₂, hK₂, h₂⟩ := ih _ (sm_fd hχ Complex.I) (hχc.fderiv_apply (𝕜 := ℝ) Complex.I)
    refine ⟨max K₀ (2 ^ m * ((K₁ + K₂) * C₀)), le_max_of_le_left hK₀, fun w hw hlen g hg hgK => ?_⟩
    have hgN := gN_nn g
    rcases Nat.lt_or_ge w.length (m + 1) with hlt | hge
    · exact (h₀ w hw (by omega) g hg hgK).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hgN _))
    · obtain ⟨w', x, rfl⟩ : ∃ w' x, w = w' ++ [x] := by
        rcases List.eq_nil_or_concat w with h0 | ⟨w', x, hx⟩
        · subst h0; simp at hge
        · exact ⟨w', x, by rw [hx, List.concat_eq_append]⟩
      have hlen' : w'.length = m := by simp at hlen hge; omega
      rw [Dw_snoc, Dx_comp x hχ hψ]
      have hA : ContDiff ℝ ∞ (fun g => fderiv ℝ χ (ψ g) 1) := (sm_fd hχ 1).comp hψ
      have hB : ContDiff ℝ ∞ (fun g => fderiv ℝ χ (ψ g) Complex.I) := (sm_fd hχ Complex.I).comp hψ
      have hR : ContDiff ℝ ∞ (fun g => reC (Dx x ψ g)) := reC.contDiff.comp (sm_Dx x hψ)
      have hI : ContDiff ℝ ∞ (fun g => imC (Dx x ψ g)) := imC.contDiff.comp (sm_Dx x hψ)
      rw [Dw_add' w' (hA.mul hR) (hB.mul hI)]
      have key : ∀ (L : ℂ →L[ℝ] ℂ), (∀ z, ‖L z‖ ≤ ‖z‖) → ∀ (v : ℂ) (Kv : ℝ), 0 ≤ Kv →
          (∀ w₁, Good k r n w₁ → w₁.length ≤ m →
            ‖Dw w₁ (fun g => fderiv ℝ χ (ψ g) v) g‖ ≤ Kv * gN g ^ cw cost w₁) →
          ‖Dw w' (fun g => fderiv ℝ χ (ψ g) v * L (Dx x ψ g)) g‖ ≤
            2 ^ m * (Kv * C₀) * gN g ^ cw cost (w' ++ [x]) := by
        intro L hL v Kv hKv hv
        have hM := leibC g w' (fun g => fderiv ℝ χ (ψ g) v) (fun g => L (Dx x ψ g))
          ((sm_fd hχ v).comp hψ) (L.contDiff.comp (sm_Dx x hψ)) (Kv * C₀ * gN g ^ cw cost (w' ++ [x])) (by
            intro w₁ w₂ s1 s2 hp
            have hG1 : Good k r n w₁ := hw.sub (s1.trans (List.sublist_append_left _ _))
            have hG2 : Good k r n (w₂ ++ [x]) := hw.sub (s2.append (List.Sublist.refl _))
            have hl1 : w₁.length ≤ m := by have := s1.length_le; omega
            have e1 := hv w₁ hG1 hl1
            have e2 := H (w₂ ++ [x]) hG2 (by simp) g hg hgK
            rw [Dw_snoc] at e2
            rw [PI.UnitaryCorollaryDerivatives.CCA.Dw_clm w₂ L (sm_Dx x hψ)]
            have hcs : cw cost w₁ + cw cost (w₂ ++ [x]) = cw cost (w' ++ [x]) :=
              cw_perm cost (by rw [← List.append_assoc]; exact hp.append_right [x])
            calc _ ≤ (Kv * gN g ^ cw cost w₁) * (C₀ * gN g ^ cw cost (w₂ ++ [x])) :=
                  mul_le_mul e1 ((hL _).trans e2) (norm_nonneg _) (mul_nonneg hKv (pow_nonneg hgN _))
              _ = Kv * C₀ * gN g ^ cw cost (w' ++ [x]) := by rw [← hcs, pow_add]; ring)
        calc _ ≤ 2 ^ w'.length * (Kv * C₀ * gN g ^ cw cost (w' ++ [x])) := hM
          _ = _ := by rw [hlen']; ring
      have t1 := key reC norm_reC 1 K₁ hK₁ (fun w₁ hG hl => h₁ w₁ hG hl g hg hgK)
      have t2 := key imC norm_imC Complex.I K₂ hK₂ (fun w₁ hG hl => h₂ w₁ hG hl g hg hgK)
      calc _ ≤ _ + _ := norm_add_le _ _
        _ ≤ 2 ^ m * (K₁ * C₀) * gN g ^ cw cost (w' ++ [x]) +
            2 ^ m * (K₂ * C₀) * gN g ^ cw cost (w' ++ [x]) := add_le_add t1 t2
        _ = (2 ^ m * ((K₁ + K₂) * C₀)) * gN g ^ cw cost (w' ++ [x]) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hgN _)

end LatticeLocalGlobalTheory

private theorem Dw_comp_eq_zero_of_not_mem_tsupport {k r : ℕ} (ψ : B.Mat k r → ℂ) (hψ : ContDiff ℝ ∞ ψ) :
    ∀ m : ℕ, ∀ χ : ℂ → ℂ, ContDiff ℝ ∞ χ → ∀ w : List (Bool × B.Mat k r), w.length ≤ m →
      ∀ g, ψ g ∉ tsupport χ → P.BetaSesquilinearity.Dw w (fun g => χ (ψ g)) g = 0 := by
  intro m
  induction m with
  | zero =>
    intro χ hχ w hw g hg
    have : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw)
    subst this
    show χ (ψ g) = 0
    first
    | exact image_eq_zero_of_notMem_tsupport hg
    | exact image_eq_zero_of_nmem_tsupport hg
  | succ m ih =>
    intro χ hχ w hw g hg
    rcases Nat.lt_or_ge w.length (m + 1) with hlt | hge
    · exact ih χ hχ w (by omega) g hg
    · obtain ⟨w', x, rfl⟩ : ∃ w' x, w = w' ++ [x] := by
        rcases List.eq_nil_or_concat w with h0 | ⟨w', x, hx⟩
        · subst h0; simp at hge
        · exact ⟨w', x, by rw [hx, List.concat_eq_append]⟩
      have hlen' : w'.length ≤ m := by simp at hw; omega
      rw [CCA.Dw_snoc, CCA.Dx_comp x hχ hψ]
      have hA : ContDiff ℝ ∞ (fun g => fderiv ℝ χ (ψ g) 1) := (CCA.sm_fd hχ 1).comp hψ
      have hB : ContDiff ℝ ∞ (fun g => fderiv ℝ χ (ψ g) Complex.I) := (CCA.sm_fd hχ Complex.I).comp hψ
      have hR : ContDiff ℝ ∞ (fun g => CCA.reC (P.BetaSesquilinearity.Dx x ψ g)) := CCA.reC.contDiff.comp (CCA.sm_Dx x hψ)
      have hI : ContDiff ℝ ∞ (fun g => CCA.imC (P.BetaSesquilinearity.Dx x ψ g)) := CCA.imC.contDiff.comp (CCA.sm_Dx x hψ)
      rw [CCA.Dw_add' w' (hA.mul hR) (hB.mul hI)]
      have key : ∀ (L : ℂ →L[ℝ] ℂ) (v : ℂ),
          P.BetaSesquilinearity.Dw w' (fun g => fderiv ℝ χ (ψ g) v * L (P.BetaSesquilinearity.Dx x ψ g)) g = 0 := by
        intro L v
        have hM := CCA.leibC g w' (fun g => fderiv ℝ χ (ψ g) v) (fun g => L (P.BetaSesquilinearity.Dx x ψ g))
          ((CCA.sm_fd hχ v).comp hψ) (L.contDiff.comp (CCA.sm_Dx x hψ)) 0 (by
            intro w₁ w₂ s1 _ _
            have hg' : ψ g ∉ tsupport (fun z => fderiv ℝ χ z v) :=
              fun h => hg (tsupport_fderiv_apply_subset (𝕜 := ℝ) v h)
            rw [ih _ (CCA.sm_fd hχ v) w₁ (by have := s1.length_le; omega) g hg']
            simp)
        simpa using hM
      beta_reduce
      rw [key CCA.reC 1, key CCA.imC Complex.I, add_zero]

theorem compact_curve_estimate : CompC := by
  intro k r ψ χ cost n C₀ hψ hχ hχc H
  obtain ⟨C, hC0, hC⟩ := LatticeLocalGlobalTheory.faa n cost ψ hψ (tsupport χ) (max C₀ 0) (le_max_right _ _) (by
      rintro w ⟨u, v, hu, hv, hl, rfl⟩ hne g hg hgK
      have hne' : u ++ v ≠ [] := by
        rintro h0
        rw [List.append_eq_nil_iff] at h0
        obtain ⟨rfl, rfl⟩ := h0
        exact hne (by simp [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR])
      have key := H u v hu hv hl hne' g hg hgK
      rw [P.BetaSesquilinearity.dLR_eq, Real.rpow_natCast, ← LatticeLocalGlobalTheory.cw_LR] at key
      exact key.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (LatticeLocalGlobalTheory.gN_nn g) _)))
    n χ hχ hχc
  refine ⟨C, fun u v hu hv hl g hg => ?_⟩
  rw [P.BetaSesquilinearity.dLR_eq, zero_add, Real.rpow_natCast, ← LatticeLocalGlobalTheory.cw_LR]
  have hlen : (P.BetaSesquilinearity.wL u ++ P.BetaSesquilinearity.wR v).length ≤ n := by simpa [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR] using hl
  by_cases hgK : ψ g ∈ tsupport χ
  · exact hC _ ⟨u, v, hu, hv, hl, rfl⟩ hlen g hg hgK
  · rw [Dw_comp_eq_zero_of_not_mem_tsupport ψ hψ n χ hχ _ hlen g hgK, norm_zero]
    exact mul_nonneg hC0 (pow_nonneg (LatticeLocalGlobalTheory.gN_nn g) _)

end PI.UnitaryCorollaryDerivatives
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.UnitaryCorollaryOfEstimates
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem unitary_corollary_of_estimates (hC : CoreStar) (hD : DjWB) (hG : GfWB) (hM : WBmul) :
    Formalism.FourierDecayAlt.U.StarBoundOfCutoffOperator ∧ Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator := by
  constructor
  · intro k j ρ Wp Wq _ _ _ _ _ o κ Θ χ hΘ hχ Q mm₀ A₀ hQ
    obtain ⟨hcd, Cφ, hWB⟩ := hD k j ρ χ (Q + o) hχ
    obtain ⟨C, hCf⟩ := hC k j ρ Wp Wq o κ 0 Θ χ (fun g => χ (DjU k j ρ g)) hΘ hχ Q mm₀ A₀ hQ hcd
      (fun g hg => image_eq_zero_of_notMem_tsupport hg) ⟨Cφ, by simpa using hWB⟩
    refine ⟨C, fun f c hf => ?_⟩
    have := hCf f c hf
    simp only [Nat.cast_zero, zero_mul, sub_zero] at this
    exact this
  · intro k j ρ Wp Wq _ _ _ _ _ z z' o κ Θ χ χε ε hΘ hχ hε Q mm₀ A₀ hQ
    obtain ⟨hcd, C1, h1⟩ := hD k j ρ χ (Q + o) hχ
    obtain ⟨hcg, C2, h2⟩ := hG k (j + ρ) z z' χε ε (Q + o) hε
    obtain ⟨C3, h3⟩ := hM k (j + ρ) _ _ _ _ (Q + o) C1 C2 0 0 hcd hcg h1 h2
    rw [zero_add] at h3
    obtain ⟨C, hCf⟩ := hC k j ρ Wp Wq o κ (2 * (j + ρ + 1)) Θ χ
      (fun g => χ (DjU k j ρ g) * ((χε (Gf k (j + ρ) z z' g) : ℝ) : ℂ)) hΘ hχ Q mm₀ A₀ hQ (hcd.mul hcg)
      (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg]) ⟨C3, h3⟩
    refine ⟨C, fun f c hf => ?_⟩
    have := hCf f c hf
    convert this using 2
    · rfl
    · push_cast; ring

end PI.UnitaryCorollaryDerivatives
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.MxLeOne
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.BetaSesquilinearity

theorem mx_le_one {k r : ℕ} {X : B.Mat k r} (h : B.unitLie k r X) : mx X ≤ 1 := by
  show ‖Matrix.of.symm X‖ ≤ 1
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  exact h.2 i j

theorem dw_dj (h1 : DjCurve) (k j ρ : ℕ) : ∀ w : List (Bool × B.Mat k (j + ρ)),
    (∀ x ∈ w, inLieP k j ρ x.2 ∧ mx x.2 ≤ 1) →
    ∃ K : ℂ, ‖K‖ ≤ (j : ℝ) ^ w.length ∧ ∀ g, Dw w (DjU k j ρ) g = K * DjU k j ρ g := by
  intro w
  induction w with
  | nil => intro _; exact ⟨1, by simp, fun g => by simp [Dw]⟩
  | cons x w ih =>
    intro hw
    obtain ⟨K, hK, hD⟩ := ih fun y hy => hw y (by simp [hy])
    obtain ⟨hxP, hxm⟩ := hw x (by simp)
    obtain ⟨c₁, c₂, hc₁, hc₂, hcur⟩ := h1 k j ρ x.2 hxP
    have hderiv : ∀ (c D : ℂ), HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c) * D) (c * D) 0 := by
      intro c D
      have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) * c) (1 * c) 0 :=
        (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const c
      have := (h0.cexp).mul_const D
      simpa using this
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    obtain ⟨b, X⟩ := x
    cases b
    · refine ⟨c₁ * K, ?_, fun g => ?_⟩
      · rw [norm_mul, List.length_cons, pow_succ']
        exact mul_le_mul (hc₁.trans (mul_le_of_le_one_right hj hxm)) hK (norm_nonneg _) hj
      · have e : Dw ((false, X) :: w) (DjU k j ρ) = Dx (false, X) (fun g => K • DjU k j ρ g) := by
          show Dx (false, X) (Dw w (DjU k j ρ)) = _
          congr 1; funext g; rw [hD g, smul_eq_mul]
        rw [e, Dx_smul]
        show K • Dx (false, X) (DjU k j ρ) g = _
        rw [Dx_eq]
        have e2 : (fun t : ℝ => DjU k j ρ (crv (false, X) g t)) =
            fun t : ℝ => Complex.exp ((t : ℂ) * c₁) * DjU k j ρ g := by
          funext t; exact (hcur g t).1
        simp only [e2, (hderiv c₁ _).deriv, smul_eq_mul]
        ring
    · refine ⟨c₂ * K, ?_, fun g => ?_⟩
      · rw [norm_mul, List.length_cons, pow_succ']
        exact mul_le_mul (hc₂.trans (mul_le_of_le_one_right hj hxm)) hK (norm_nonneg _) hj
      · have e : Dw ((true, X) :: w) (DjU k j ρ) = Dx (true, X) (fun g => K • DjU k j ρ g) := by
          show Dx (true, X) (Dw w (DjU k j ρ)) = _
          congr 1; funext g; rw [hD g, smul_eq_mul]
        rw [e, Dx_smul]
        show K • Dx (true, X) (DjU k j ρ) g = _
        rw [Dx_eq]
        have e2 : (fun t : ℝ => DjU k j ρ (crv (true, X) g t)) =
            fun t : ℝ => Complex.exp ((t : ℂ) * c₂) * DjU k j ρ g := by
          funext t; exact (hcur g t).2
        simp only [e2, (hderiv c₂ _).deriv, smul_eq_mul]
        ring

theorem djWB_of (h1 : DjCurve) (h2 : PolyB) (h3 : DjPoly) (h4 : CompC) : DjWB := by
  intro k j ρ χ n hχ
  obtain ⟨hcD, hB⟩ := h2 k (j + ρ) j (DjU k j ρ) (h3 k j ρ)
  obtain ⟨CP, hCP⟩ := hB n
  refine ⟨hχ.1.comp hcD, ?_⟩
  obtain ⟨R, hR⟩ := (hχ.2.1 : IsCompact (tsupport χ)).isBounded.exists_norm_le
  refine h4 k (j + ρ) (DjU k j ρ) χ (costP k j ρ) n (|CP| + (max 1 (j : ℝ)) ^ n * |R|) hcD hχ.1 hχ.2.1 ?_
  intro u v hu hv hl hne g hg hgs
  have hg1 := gN_ge_one hg
  have hS0 : (0 : ℝ) ≤ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA : 0 ≤ |CP| := abs_nonneg _
  have hBn : 0 ≤ (max 1 (j : ℝ)) ^ n * |R| := by positivity
  by_cases hall : ∀ X ∈ u ++ v, inLieP k j ρ X
  ·
    have hw : ∀ x ∈ wL u ++ wR v, inLieP k j ρ x.2 ∧ mx x.2 ≤ 1 := by
      intro x hx
      simp only [wL, wR, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact ⟨hall X (List.mem_append_left _ hX), mx_le_one (hu X hX)⟩
      · exact ⟨hall X (List.mem_append_right _ hX), mx_le_one (hv X hX)⟩
    obtain ⟨K, hK, hD⟩ := dw_dj h1 k j ρ _ hw
    rw [dLR_eq, hD g, norm_mul]
    have hlen : (wL u ++ wR v).length ≤ n := by rw [len_LR]; exact hl
    have hK' : ‖K‖ ≤ (max 1 (j : ℝ)) ^ n :=
      hK.trans ((pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hlen))
    have hDR : ‖DjU k j ρ g‖ ≤ |R| := (hR _ hgs).trans (le_abs_self _)
    have h1' : 1 ≤ B.gN g ^ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) := Real.one_le_rpow hg1 hS0
    calc ‖K‖ * ‖DjU k j ρ g‖ ≤ (max 1 (j : ℝ)) ^ n * |R| :=
          mul_le_mul hK' hDR (norm_nonneg _) (by positivity)
      _ ≤ (|CP| + (max 1 (j : ℝ)) ^ n * |R|) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left h1' (by positivity)
  · obtain ⟨X, hX, hXP⟩ : ∃ X ∈ u ++ v, ¬ inLieP k j ρ X := by
      by_contra hc; exact hall (fun X hX => by by_contra h; exact hc ⟨X, hX, h⟩)
    have hcX : costP k j ρ X = j := by simp [costP, hXP]
    have hjS : (j : ℝ) ≤ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) := by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := costP k j ρ) hX)
      rw [hcX] at this; exact_mod_cast this
    have hb := hCP u v hu hv hl g hg
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_zero, Nat.cast_zero, add_zero] at hb
    calc ‖B.dLR u v (DjU k j ρ) g‖ ≤ CP * B.gN g ^ (j : ℝ) := hb
      _ ≤ |CP| * B.gN g ^ ((((u ++ v).map (costP k j ρ)).sum : ℕ) : ℝ) :=
          mul_le_mul (le_abs_self _) (Real.rpow_le_rpow_of_exponent_le hg1 hjS) (by positivity) hA
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end PI.UnitaryCorollaryDerivatives
end
end

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem unitary_corollary_both_forms : Formalism.FourierDecayAlt.U.StarBoundOfCutoffOperator ∧ Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator :=
  unitary_corollary_of_estimates star_estimate_unitary (djWB_of determinant_curve_derivative polynomial_bound determinant_derivative_polynomial compact_curve_estimate)
    (gfWB_of generating_function_polynomial polynomial_bound compact_region_estimate) weight_bound_multiplicative

end PI.UnitaryCorollaryDerivatives
end
end

theorem cutoff_plain_and_smoothed : Formalism.FourierDecayAlt.U.StarBoundOfCutoffOperator ∧ Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator := PI.UnitaryCorollaryDerivatives.unitary_corollary_both_forms
end

theorem Formalism.FourierDecayAlt.P.corollary_u1_truncated_alt : Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator :=
  cutoff_plain_and_smoothed.2
