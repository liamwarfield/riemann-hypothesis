module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftTypeAction

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordLengthLe
open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma admissible_word_mem_lie {n : ℕ} {w : List (Bool × Mat k r)} (h : admitted n w) : ∀ x ∈ w, inLie k r x.2 := by
  obtain ⟨u, v, hu, hv, -, rfl⟩ := h
  exact lie_LR (unit_lie hu) (unit_lie hv)

lemma admissible_word_length_le {n : ℕ} {w : List (Bool × Mat k r)} (h : admitted n w) : w.length ≤ n := by
  obtain ⟨u, v, -, -, hl, rfl⟩ := h
  rw [len_LR]
  exact hl

section defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def LSS (f : Mat k r → E) (S : Set (Mat k r)) : Prop :=
  ∀ g ∈ S, ∃ f' : Mat k r → E, ContDiff ℝ ∞ f' ∧ ∃ V : Set (Mat k r), IsOpen V ∧ g ∈ V ∧
    ∀ g' ∈ GV k r, g' ∈ V → f g' = f' g'

def UB (f : Mat k r → E) (S : Set (Mat k r)) (n : ℕ) (C : ℝ) (e γ : ℕ) : Prop :=
  ∀ w, admitted n w → ∀ g ∈ S, ‖Dw w f g‖ ≤ C * gN g ^ (e + γ * w.length)

lemma lss_of_contDiff {f : Mat k r → E} (hf : ContDiff ℝ ∞ f) (S : Set (Mat k r)) : LSS f S := by
  intro g _
  exact ⟨f, hf, univ, isOpen_univ, mem_univ g, fun _ _ _ => rfl⟩

lemma lss_mono {f : Mat k r → E} {S S' : Set (Mat k r)} (h : LSS f S) (hS : S' ⊆ S) : LSS f S' := fun g hg => h g (hS hg)

lemma lss_congr {f f₂ : Mat k r → E} {S : Set (Mat k r)} {V : Set (Mat k r)} (hV : IsOpen V) (hSV : S ⊆ V)
    (he : ∀ g ∈ GV k r, g ∈ V → f g = f₂ g) (h : LSS f₂ S) : LSS f S := by
  intro g hg
  obtain ⟨f', hf', W, hW, hgW, hfW⟩ := h g hg
  refine ⟨f', hf', V ∩ W, hV.inter hW, ⟨hSV hg, hgW⟩, ?_⟩
  intro g' hg' hgVW
  rw [he g' hg' hgVW.1, hfW g' hg' hgVW.2]

lemma ub_congr {f f₂ : Mat k r → E} {S : Set (Mat k r)} {V : Set (Mat k r)} (hV : IsOpen V) (hSV : S ⊆ V)
    (hSG : S ⊆ GV k r) (he : ∀ g ∈ GV k r, g ∈ V → f g = f₂ g) {n : ℕ} {C : ℝ} {e γ : ℕ} (h : UB f₂ S n C e γ) :
    UB f S n C e γ := by
  intro w hw g hg
  rw [Dw_congr_loc (admissible_word_mem_lie hw) hV he g (hSG hg) (hSV hg)]
  exact h w hw g hg

lemma lss_of_ckOn {f : Mat k r → E} {UU S : Set (Mat k r)} (hf : CkOn ⊤ UU f) (hS : S ⊆ UU) : LSS f S := by
  intro g hg
  obtain ⟨U, f', hU, hgU, hf', hfU⟩ := hf g (hS hg)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU g hgU
  let χ : ContDiffBump g := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hcl : Metric.closedBall g (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  refine ⟨fun x => χ x • f' x, ?_, Metric.ball g (ε / 4), Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity), ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Metric.closedBall g (ε / 2)
    · exact χ.contDiff.contDiffAt.smul (hf'.contDiffAt (hU.mem_nhds (hcl hx)))
    · have hzero : (fun x => χ x • f' x) =ᶠ[𝓝 x] fun _ => (0 : E) := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
        have hy' : ε / 2 ≤ dist y g := by
          simp only [mem_compl_iff, Metric.mem_closedBall, not_le] at hy
          exact hy.le
        have : χ y = 0 := χ.zero_of_le_dist hy'
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  · intro g' hg' hgb
    have h1 : χ g' = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hgb)
    dsimp only
    rw [h1, one_smul]
    exact hfU g' (hball (Metric.ball_subset_ball (by linarith) hgb)) hg'

lemma lss_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℝ] E') {f : Mat k r → E}
    {S : Set (Mat k r)} (h : LSS f S) : LSS (fun g => L (f g)) S := by
  intro g hg
  obtain ⟨f', hf', V, hV, hgV, hfV⟩ := h g hg
  exact ⟨fun x => L (f' x), L.contDiff.comp hf', V, hV, hgV,
    fun g' hg' hgV' => by dsimp only; rw [hfV g' hg' hgV']⟩

lemma ub_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℝ] E') {f : Mat k r → E}
    {S : Set (Mat k r)} (hSG : S ⊆ GV k r) (hl : LSS f S) {n : ℕ} {C : ℝ} {e γ : ℕ} (h : UB f S n C e γ) :
    UB (fun g => L (f g)) S n (‖L‖ * C) e γ := by
  intro w hw g hg
  obtain ⟨f', hf', V, hV, hgV, hfV⟩ := hl g hg
  have hlie := admissible_word_mem_lie hw
  have e1 := Dw_congr_loc hlie hV (f := fun x => L (f x)) (f₂ := fun x => L (f' x))
    (fun g' hg' hgV' => by rw [hfV g' hg' hgV']) g (hSG hg) hgV
  have e2 := Dw_congr_loc hlie hV hfV g (hSG hg) hgV
  have e3 : Dw w (fun x => L (f' x)) g = L (Dw w f' g) := congrFun (dw_clm L w hf') g
  rw [e1, e3, ← e2, mul_assoc]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h w hw g hg) (norm_nonneg L))

lemma ub_mono {f : Mat k r → E} {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {n : ℕ} {C : ℝ} {e γ e' γ' : ℕ}
    (h : UB f S n C e γ) (hC : 0 ≤ C) (he : e ≤ e') (hγ : γ ≤ γ') : UB f S n C e' γ' := by
  intro w hw g hg
  have h1 := gN_ge_one (hSG hg)
  refine (h w hw g hg).trans (mul_le_mul_of_nonneg_left ?_ hC)
  exact pow_le_pow_right₀ h1 (Nat.add_le_add he (Nat.mul_le_mul_right _ hγ))

private lemma Dw_cons_const_eq_zero (c : E) (x : Bool × Mat k r) (w : List (Bool × Mat k r)) :
    Dw (x :: w) (fun _ : Mat k r => c) = fun _ => 0 := by
  induction w generalizing x with
  | nil =>
    funext g
    show Dx x (fun _ => c) g = 0
    rw [Dx_eq]
    exact deriv_const _ _
  | cons y w ih =>
    show Dx x (Dw (y :: w) fun _ => c) = fun _ => 0
    rw [ih]
    exact Dx_zero x

lemma ub_const (c : E) (S : Set (Mat k r)) (hSG : S ⊆ GV k r) (n : ℕ) (γ : ℕ) :
    UB (fun _ : Mat k r => c) S n ‖c‖ 0 γ := by
  intro w _ g hg
  have h0 : 0 ≤ gN g := (gN_pos (hSG hg)).le
  cases w with
  | nil =>
    show ‖c‖ ≤ ‖c‖ * gN g ^ (0 + γ * 0)
    simp
  | cons x w =>
    rw [Dw_cons_const_eq_zero]
    simp only [norm_zero]
    exact mul_nonneg (norm_nonneg c) (pow_nonneg h0 _)

end defs

section app

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma leibC (g : Mat k r) (M : ℝ) (w : List (Bool × Mat k r)) (a : Mat k r → (F →L[ℂ] E)) (b : Mat k r → F)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hM : ∀ w₁ w₂, Spl w w₁ w₂ → ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) :
    ‖Dw w (fun g => a g (b g)) g‖ ≤ 2 ^ w.length * M := by
  let R : (F →L[ℂ] E) →L[ℝ] (F →L[ℝ] E) := ContinuousLinearMap.restrictScalarsL ℂ F E ℝ ℝ
  have hR : ∀ T : F →L[ℂ] E, ‖R T‖ = ‖T‖ := fun T => ContinuousLinearMap.norm_restrictScalars T
  have hRa : ContDiff ℝ ∞ (fun x => R (a x)) := R.contDiff.comp ha
  have hD : ∀ w₁ : List (Bool × Mat k r), Dw w₁ (fun x => R (a x)) g = R (Dw w₁ a g) :=
    fun w₁ => congrFun (dw_clm R w₁ ha) g
  have key := leibA g M w (fun x => R (a x)) b hRa hb
    (fun w₁ w₂ hs => by rw [hD, hR]; exact hM w₁ w₂ hs)
  exact key

lemma lss_app {S : Set (Mat k r)} {a : Mat k r → (F →L[ℂ] E)} {b : Mat k r → F} (ha : LSS a S) (hb : LSS b S) :
    LSS (fun g => a g (b g)) S := by
  intro g hg
  obtain ⟨a', ha', V₁, hV₁, hg₁, haV⟩ := ha g hg
  obtain ⟨b', hb', V₂, hV₂, hg₂, hbV⟩ := hb g hg
  let R : (F →L[ℂ] E) →L[ℝ] (F →L[ℝ] E) := ContinuousLinearMap.restrictScalarsL ℂ F E ℝ ℝ
  refine ⟨fun x => a' x (b' x), ?_, V₁ ∩ V₂, hV₁.inter hV₂, ⟨hg₁, hg₂⟩, ?_⟩
  · exact cd_app (a := fun x => R (a' x)) (R.contDiff.comp ha') hb'
  · intro g' hg' hV
    dsimp only
    rw [haV g' hg' hV.1, hbV g' hg' hV.2]

lemma ub_app {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {a : Mat k r → (F →L[ℂ] E)} {b : Mat k r → F}
    (hla : LSS a S) (hlb : LSS b S) {n : ℕ} {Ca Cb : ℝ} {ea eb γ : ℕ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (ha : UB a S n Ca ea γ) (hb : UB b S n Cb eb γ) :
    UB (fun g => a g (b g)) S n (2 ^ n * (Ca * Cb)) (ea + eb) γ := by
  intro w hw g hg
  obtain ⟨a', ha', V₁, hV₁, hg₁, haV⟩ := hla g hg
  obtain ⟨b', hb', V₂, hV₂, hg₂, hbV⟩ := hlb g hg
  have hgG := hSG hg
  have h0 : 0 ≤ gN g := (gN_pos hgG).le
  have hra : ∀ w' : List (Bool × Mat k r), admitted n w' → Dw w' a g = Dw w' a' g :=
    fun w' hw' => Dw_congr_loc (admissible_word_mem_lie hw') hV₁ haV g hgG hg₁
  have hrb : ∀ w' : List (Bool × Mat k r), admitted n w' → Dw w' b g = Dw w' b' g :=
    fun w' hw' => Dw_congr_loc (admissible_word_mem_lie hw') hV₂ hbV g hgG hg₂
  have happ : Dw w (fun x => a x (b x)) g = Dw w (fun x => a' x (b' x)) g :=
    Dw_congr_loc (admissible_word_mem_lie hw) (hV₁.inter hV₂)
      (fun g' hg' hV => by rw [haV g' hg' hV.1, hbV g' hg' hV.2]) g hgG ⟨hg₁, hg₂⟩
  have key := leibC g (Ca * Cb * gN g ^ (ea + eb + γ * w.length)) w a' b' ha' hb' (by
    intro w₁ w₂ hs
    have hw₁ := Adm_sub hs.1 hw
    have hw₂ := Adm_sub hs.2.1 hw
    rw [← hra w₁ hw₁, ← hrb w₂ hw₂]
    have hexp : ea + γ * w₁.length + (eb + γ * w₂.length) = ea + eb + γ * w.length := by
      rw [← spl_len hs]; ring
    calc ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖
        ≤ (Ca * gN g ^ (ea + γ * w₁.length)) * (Cb * gN g ^ (eb + γ * w₂.length)) :=
          mul_le_mul (ha w₁ hw₁ g hg) (hb w₂ hw₂ g hg) (norm_nonneg _)
            (mul_nonneg hCa (pow_nonneg h0 _))
      _ = Ca * Cb * gN g ^ (ea + γ * w₁.length + (eb + γ * w₂.length)) := by rw [pow_add]; ring
      _ = Ca * Cb * gN g ^ (ea + eb + γ * w.length) := by rw [hexp])
  rw [happ]
  refine key.trans ?_
  have hM : 0 ≤ Ca * Cb * gN g ^ (ea + eb + γ * w.length) :=
    mul_nonneg (mul_nonneg hCa hCb) (pow_nonneg h0 _)
  have h2 : (2 : ℝ) ^ w.length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (admissible_word_length_le hw)
  calc (2 : ℝ) ^ w.length * (Ca * Cb * gN g ^ (ea + eb + γ * w.length))
      ≤ 2 ^ n * (Ca * Cb * gN g ^ (ea + eb + γ * w.length)) := mul_le_mul_of_nonneg_right h2 hM
    _ = 2 ^ n * (Ca * Cb) * gN g ^ (ea + eb + γ * w.length) := by ring

end app

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section ube

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def UBL (f : Mat k r → E) (S : Set (Mat k r)) (n e γ : ℕ) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ UB f S n C e γ) ∧ LSS f S

lemma ubl_mono {f : Mat k r → E} {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {n e γ e' γ' : ℕ}
    (h : UBL f S n e γ) (he : e ≤ e') (hγ : γ ≤ γ') : UBL f S n e' γ' := by
  obtain ⟨⟨C, hC, hub⟩, hl⟩ := h
  exact ⟨⟨C, hC, ub_mono hSG hub hC he hγ⟩, hl⟩

lemma ubl_const (c : E) {S : Set (Mat k r)} (hSG : S ⊆ GV k r) (n γ : ℕ) : UBL (fun _ : Mat k r => c) S n 0 γ := by
  exact ⟨⟨‖c‖, norm_nonneg _, ub_const c S hSG n γ⟩, lss_of_contDiff contDiff_const S⟩

lemma ubl_clm {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℝ] E') {f : Mat k r → E}
    {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {n e γ : ℕ} (h : UBL f S n e γ) : UBL (fun g => L (f g)) S n e γ := by
  obtain ⟨⟨C, hC, hub⟩, hl⟩ := h
  exact ⟨⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, ub_clm L hSG hl hub⟩, lss_clm L hl⟩

lemma ubl_app {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {a : Mat k r → (F →L[ℂ] E)} {b : Mat k r → F} {n ea eb γ : ℕ} (ha : UBL a S n ea γ) (hb : UBL b S n eb γ) :
    UBL (fun g => a g (b g)) S n (ea + eb) γ := by
  obtain ⟨⟨Ca, hCa, hua⟩, hla⟩ := ha
  obtain ⟨⟨Cb, hCb, hub⟩, hlb⟩ := hb
  exact ⟨⟨2 ^ n * (Ca * Cb), by positivity, ub_app hSG hla hlb hCa hCb hua hub⟩, lss_app hla hlb⟩

lemma ubl_congr {f f₂ : Mat k r → E} {S V : Set (Mat k r)} (hV : IsOpen V) (hSV : S ⊆ V) (hSG : S ⊆ GV k r)
    (he : ∀ g ∈ GV k r, g ∈ V → f g = f₂ g) {n e γ : ℕ} (h : UBL f₂ S n e γ) : UBL f S n e γ := by
  obtain ⟨⟨C, hC, hub⟩, hl⟩ := h
  exact ⟨⟨C, hC, ub_congr hV hSV hSG he hub⟩, lss_congr hV hSV he hl⟩

lemma ubl_sub {f : Mat k r → E} {S S' : Set (Mat k r)} (hS : S' ⊆ S) {n e γ : ℕ} (h : UBL f S n e γ) :
    UBL f S' n e γ := by
  obtain ⟨⟨C, hC, hub⟩, hl⟩ := h
  exact ⟨⟨C, hC, fun w hw g hg => hub w hw g (hS hg)⟩, lss_mono hl hS⟩

end ube

lemma ubl_mul {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {a b : Mat k r → ℂ} {n ea eb γ : ℕ}
    (ha : UBL a S n ea γ) (hb : UBL b S n eb γ) : UBL (fun g => a g * b g) S n (ea + eb) γ := by
  have ha' : UBL (fun g => ((ContinuousLinearMap.mul ℂ ℂ).restrictScalars ℝ) (a g)) S n ea γ :=
    ubl_clm _ hSG ha
  have h := ubl_app hSG ha' hb
  convert h using 2
  simp

lemma ubl_prod {ι : Type*} [DecidableEq ι] {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {n γ : ℕ} (s : Finset ι)
    (f : ι → Mat k r → ℂ) (h : ∀ i ∈ s, UBL (f i) S n 0 γ) : UBL (fun g => ∏ i ∈ s, f i g) S n 0 γ := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact ubl_const 1 hSG n γ
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    have h1 := ubl_mul hSG (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa using h1

lemma ubl_poly {d : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg d P) (S : Set (Mat k r)) (hSG : S ⊆ GV k r) (n γ : ℕ) :
    UBL P S n d γ := by
  obtain ⟨hcd, C, hC, hb⟩ := Formalism.FourierDecayAlt.P.poly_adm (n := n) hP
  refine ⟨⟨C, hC, fun w hw g hg => ?_⟩, lss_of_contDiff hcd S⟩
  refine le_trans (hb w hw g (hSG hg)) (mul_le_mul_of_nonneg_left ?_ hC)
  exact pow_le_pow_right₀ (gN_ge_one (hSG hg)) (Nat.le_add_right _ _)

lemma poly_H {d : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg d P) (n : ℕ) :
    ∃ M : ℝ, ∀ w, admitted n w → w ≠ [] → ∀ g ∈ GV k r, ‖Dw w P g‖ ≤ M * gN g ^ (d * w.length) := by
  obtain ⟨-, C, hC, hb⟩ := Formalism.FourierDecayAlt.P.poly_adm (n := n) hP
  refine ⟨C, fun w hw hne g hg => le_trans (hb w hw g hg) (mul_le_mul_of_nonneg_left ?_ hC)⟩
  have hl : 1 ≤ w.length := List.length_pos_iff.2 hne
  exact pow_le_pow_right₀ (gN_ge_one hg) (Nat.le_mul_of_pos_right d hl)

lemma ubl_fdb {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ψ : Mat k r → F) (hψ : ContDiff ℝ ∞ ψ) (S : Set (Mat k r)) (hSG : S ⊆ GV k r) (K : Set F)
    (hK : ∀ g ∈ S, ψ g ∈ K) (α n : ℕ) (M : ℝ)
    (H : ∀ w, admitted n w → w ≠ [] → ∀ g ∈ GV k r, ‖Dw w ψ g‖ ≤ M * gN g ^ (α * w.length))
    (Φ : F → E) (hΦ : ContDiff ℝ ∞ Φ) (hB : ∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j Φ y‖ ≤ B) :
    UBL (fun g => Φ (ψ g)) S n 0 α := by
  obtain ⟨C, hC, hb⟩ := fdb ψ hψ S K hK gN (fun g hg => gN_ge_one (hSG hg)) α 0 M n
    (fun w hw hne g hg => by simpa using H w hw hne g (hSG hg)) n E Φ hΦ hB
  refine ⟨⟨C, hC, fun w hw g hg => ?_⟩, lss_of_contDiff (hΦ.comp hψ) S⟩
  have hlen : w.length ≤ n := by
    obtain ⟨u, v, -, -, hl, rfl⟩ := hw
    simpa [wL, wR] using hl
  simpa using hb w hw hlen g hg

lemma normSq_cd : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
  have h : (fun z : ℂ => Complex.normSq z) = fun z => ‖z‖ ^ 2 :=
    funext fun z => Complex.normSq_eq_norm_sq z
  rw [h]
  exact contDiff_norm_sq ℝ

def zinv (c : ℝ) (m : ℕ) (z : ℂ) : ℂ := (sc c (Complex.normSq z) : ℂ) * z⁻¹ ^ m

lemma zinv_cd {c : ℝ} (hc : 0 < c) (m : ℕ) : ContDiff ℝ ∞ (zinv c m) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · have hev : zinv c m =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      have hopen : IsOpen {w : ℂ | Complex.normSq w < c / 4} :=
        isOpen_lt normSq_cd.continuous continuous_const
      have hmem : z ∈ {w : ℂ | Complex.normSq w < c / 4} := by
        show Complex.normSq z < c / 4
        rw [hz, map_zero]
        positivity
      filter_upwards [hopen.mem_nhds hmem] with w hw
      unfold zinv
      rw [sc_zero hc (le_of_lt hw)]
      simp
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · unfold zinv
    have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => ((sc c (Complex.normSq w) : ℝ) : ℂ)) z :=
      (Complex.ofRealCLM.contDiff.comp ((sc_cd c).comp normSq_cd)).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun w : ℂ => w⁻¹ ^ m) z :=
      ((contDiffAt_inv ℂ hz).pow m).restrict_scalars ℝ
    exact h1.mul h2

lemma zinv_eq {c : ℝ} (hc : 0 < c) (m : ℕ) {z : ℂ} (hz : c / 2 ≤ Complex.normSq z) : zinv c m z = z⁻¹ ^ m := by
  unfold zinv
  rw [sc_one hc hz]
  simp

lemma zinv_bound {c : ℝ} (hc : 0 < c) (m j : ℕ) :
    ∃ B : ℝ, ∀ z ∈ {z : ℂ | c ≤ Complex.normSq z}, ‖iteratedFDeriv ℝ j (zinv c m) z‖ ≤ B := by
  refine ⟨‖∏ i ∈ Finset.range j, ((((-(m : ℤ)) : ℤ) : ℂ) - (i : ℂ))‖ * (Real.sqrt c)⁻¹ ^ (m + j),
    fun z hz => ?_⟩
  have hz' : c ≤ Complex.normSq z := hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz'
    linarith
  have hev : zinv c m =ᶠ[𝓝 z] fun w : ℂ => w⁻¹ ^ m := by
    have hopen : IsOpen {w : ℂ | c / 2 < Complex.normSq w} :=
      isOpen_lt continuous_const normSq_cd.continuous
    have hmem : z ∈ {w : ℂ | c / 2 < Complex.normSq w} := by
      show c / 2 < Complex.normSq z
      linarith
    filter_upwards [hopen.mem_nhds hmem] with w hw
    exact zinv_eq hc m (le_of_lt hw)
  have hcd : ContDiffAt ℂ ∞ (zinv c m) z :=
    ((contDiffAt_inv ℂ hz0).pow m).congr_of_eventuallyEq hev
  have hR : ‖iteratedFDeriv ℝ j (zinv c m) z‖ = ‖iteratedFDeriv ℂ j (zinv c m) z‖ := by
    rw [← (contDiffAt_infty.1 hcd j).restrictScalars_iteratedFDeriv, Function.comp_apply,
      ContinuousMultilinearMap.norm_restrictScalars]
  have hfz : (fun w : ℂ => w⁻¹ ^ m) = fun w : ℂ => w ^ (-(m : ℤ)) := by
    funext w
    rw [_root_.zpow_neg, zpow_natCast, inv_pow]
  rw [hR, norm_iteratedFDeriv_eq_norm_iteratedDeriv, hev.iteratedDeriv_eq, hfz, iteratedDeriv_eq_iterate,
    iter_deriv_zpow, norm_mul, norm_zpow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hzn : Real.sqrt c ≤ ‖z‖ := by
    rw [← Real.sqrt_sq (norm_nonneg z), ← Complex.normSq_eq_norm_sq]
    exact Real.sqrt_le_sqrt hz'
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  rw [show (-(m : ℤ) - (j : ℤ)) = -((m + j : ℕ) : ℤ) by push_cast; ring, _root_.zpow_neg, zpow_natCast, ← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg _)) (inv_anti₀ hsc hzn) _

lemma ubl_invpow {d : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg d P) {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {c : ℝ} (hc : 0 < c) (hS : ∀ g ∈ S, c ≤ Complex.normSq (P g)) (m n : ℕ) :
    UBL (fun g => (P g)⁻¹ ^ m) S n 0 d := by
  obtain ⟨hPc, -⟩ := Formalism.FourierDecayAlt.P.poly_adm (n := n) hP
  obtain ⟨M, hM⟩ := poly_H hP n
  have hV : IsOpen {g : Mat k r | c / 2 < Complex.normSq (P g)} :=
    isOpen_lt continuous_const (normSq_cd.continuous.comp hPc.continuous)
  have hSV : S ⊆ {g : Mat k r | c / 2 < Complex.normSq (P g)} := fun g hg => by
    show c / 2 < Complex.normSq (P g)
    linarith [hS g hg]
  refine ubl_congr hV hSV hSG (f₂ := fun g => zinv c m (P g)) (fun g _ hgV => (zinv_eq hc m (le_of_lt hgV)).symm) ?_
  exact ubl_fdb P hPc S hSG {z : ℂ | c ≤ Complex.normSq z} hS d n M hM (zinv c m) (zinv_cd hc m)
    (fun j => zinv_bound hc m j)

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
