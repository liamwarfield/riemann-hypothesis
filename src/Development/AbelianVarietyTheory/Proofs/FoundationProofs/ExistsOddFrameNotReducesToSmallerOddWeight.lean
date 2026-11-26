module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOddFrameNotReducesToSmallerOddWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOddFrameNotReducesToSmallerOddWeight
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame

theorem weights_nonneg_of_det {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {r : ℕ} {s : Fin r → SL(2, ℤ)}
    {w : Fin r → ℤ} {F : Fin r → ℍ → ℂ} (hF : ∀ j, IsMF Γ (w j) (F j))
    (hdet : ∃ τ, (evM s w F τ).det ≠ 0) (j : Fin r) : 0 ≤ w j := by
  by_contra hneg
  push_neg at hneg
  have h0 : F j = 0 := (hF j).eq_zero_of_neg hneg
  obtain ⟨τ, hτ⟩ := hdet
  apply hτ
  apply Matrix.det_eq_zero_of_column_eq_zero j
  intro i
  simp [evM, h0, SlashAction.zero_slash]

theorem mul_det_evM_update {r : ℕ} (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ)
    (j₀ : Fin r) (w' : ℤ) (G E : ℍ → ℂ) (e : Fin r → ℍ → ℂ)
    (hrel : ∀ (x : SL(2, ℤ)) (τ : ℍ), E τ * (G ∣[w'] x) τ = ∑ j, e j τ * (F j ∣[w j] x) τ) (τ : ℍ) :
    E τ * (evM s (Function.update w j₀ w') (Function.update F j₀ G) τ).det =
      e j₀ τ * (evM s w F τ).det := by
  have hM : evM s (Function.update w j₀ w') (Function.update F j₀ G) τ =
      (evM s w F τ).updateCol j₀ (fun i => (G ∣[w'] s i) τ) := by
    ext i j
    by_cases hj : j = j₀
    · subst hj; simp [evM, Matrix.updateCol_apply]
    · simp [evM, Matrix.updateCol_apply, hj, Function.update_of_ne hj]
  rw [hM, ← Matrix.det_updateCol_smul]
  have hc : (E τ • fun i => (G ∣[w'] s i) τ) =
      fun i => ∑ j, (fun j => e j τ) j • (evM s w F τ) i j := by
    ext i
    simp [evM, hrel]
  rw [hc, Matrix.det_updateCol_sum, smul_eq_mul]

theorem oddFrame_descent_of_weight_sum (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (r : ℕ) (s : Fin r → SL(2, ℤ)) :
    ∀ (n : ℕ) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), ∑ j, (w j).toNat = n →
      (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (∃ τ, (evM s w F τ).det ≠ 0) →
      ∃ (w' : Fin r → ℤ) (F' : Fin r → ℍ → ℂ), (∀ j, Odd (w' j) ∧ IsMF Γ (w' j) (F' j)) ∧
        (∃ τ, (evM s w' F' τ).det ≠ 0) ∧ ¬ Reduces Γ w' F' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w F hn hF hdet
  by_cases hR : Reduces Γ w F
  swap
  · exact ⟨w, F, hF, hdet, hR⟩
  obtain ⟨j₀, w₀, G, E, e, hlt, hodd, hG, he, hne, hrel⟩ := hR
  set w₁ := Function.update w j₀ w₀ with hw₁
  set F₁ := Function.update F j₀ G with hF₁
  have hF' : ∀ j, Odd (w₁ j) ∧ IsMF Γ (w₁ j) (F₁ j) := by
    intro j
    by_cases hj : j = j₀
    · subst hj; simp [w₁, F₁, hodd, hG]
    · simp only [w₁, F₁, Function.update_of_ne hj]; exact hF j
  have hdet' : ∃ τ, (evM s w₁ F₁ τ).det ≠ 0 := by
    have hd0 : (fun τ => (evM s w F τ).det) ≠ 0 := by
      obtain ⟨τ, hτ⟩ := hdet
      intro h; exact hτ (congrFun h τ)
    have hmd : MDiff (fun τ => (evM s w F τ).det) := mdiff_det_evM s w (fun j => (hF j).2.2.1)
    have hprod : e j₀ * (fun τ => (evM s w F τ).det) ≠ 0 := by
      rw [Ne, UpperHalfPlane.mul_eq_zero_iff (he j₀) hmd]
      push_neg; exact ⟨hne, hd0⟩
    obtain ⟨τ, hτ⟩ : ∃ τ, e j₀ τ * (evM s w F τ).det ≠ 0 := by
      by_contra h
      push_neg at h
      exact hprod (funext fun τ => by simpa using h τ)
    refine ⟨τ, fun h0 => hτ ?_⟩
    rw [← mul_det_evM_update s w F j₀ w₀ G E e hrel τ]
    rw [show w₁ = Function.update w j₀ w₀ from rfl, show F₁ = Function.update F j₀ G from rfl] at h0
    rw [h0, mul_zero]
  have hnn := weights_nonneg_of_det (fun j => (hF j).2) hdet
  have hnn' := weights_nonneg_of_det (fun j => (hF' j).2) hdet'
  have hlt' : ∑ j, (w₁ j).toNat < n := by
    rw [← hn]
    apply Finset.sum_lt_sum
    · intro j _
      by_cases hj : j = j₀
      · subst hj; simp only [w₁, Function.update_self]; omega
      · simp only [w₁, Function.update_of_ne hj]; exact le_rfl
    · refine ⟨j₀, Finset.mem_univ _, ?_⟩
      have := hnn' j₀
      simp only [w₁, Function.update_self] at this ⊢
      have := hnn j₀
      omega
  exact ih _ hlt' w₁ F₁ rfl hF' hdet'

theorem descent : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ),
    Γ.FiniteIndex → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (∃ τ, (evM s w F τ).det ≠ 0) →
    ∃ (w' : Fin r → ℤ) (F' : Fin r → ℍ → ℂ), (∀ j, Odd (w' j) ∧ IsMF Γ (w' j) (F' j)) ∧
      (∃ τ, (evM s w' F' τ).det ≠ 0) ∧ ¬ Reduces Γ w' F' := by
  intro Γ r s w F hΓ hF hdet
  exact oddFrame_descent_of_weight_sum Γ r s _ w F rfl hF hdet

end GlobalTheory.OddFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOddFrameNotReducesToSmallerOddWeightStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oddFrame_not_reducesToSmallerOddWeight : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), Γ.FiniteIndex → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (∃ τ, (evM s w F τ).det ≠ 0) → ∃ (w' : Fin r → ℤ) (F' : Fin r → ℍ → ℂ), (∀ j, Odd (w' j) ∧ IsMF Γ (w' j) (F' j)) ∧ (∃ τ, (evM s w' F' τ).det ≠ 0) ∧ ¬ Reduces Γ w' F' := by
  first | exact @GlobalTheory.OddFrame.descent | exact GlobalTheory.OddFrame.descent | (intros; apply GlobalTheory.OddFrame.descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPointSlashEvaluationsIndependentGamma
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPointSlashEvaluationsIndependentGamma
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.CosetEval

def mfMonoid (Γ : Subgroup SL(2, ℤ)) : Submonoid (Multiplicative ℤ × (ℍ → ℂ)) where
  carrier := {p | IsMF Γ (Multiplicative.toAdd p.1) p.2}
  mul_mem' := by
    rintro ⟨a, f⟩ ⟨b, g⟩ ha hb
    exact IsMF.mul ha hb (by simp)
  one_mem' := IsMF.one Γ

def evHom (Γ : Subgroup SL(2, ℤ)) (x : SL(2, ℤ)) (τ : ℍ) : mfMonoid Γ →* ℂ where
  toFun p := (p.1.2 ∣[Multiplicative.toAdd p.1.1] x) τ
  map_one' := by
    show ((1 : ℍ → ℂ) ∣[Multiplicative.toAdd (1 : Multiplicative ℤ)] x) τ = 1
    rw [toAdd_one, ModularForm.is_invariant_one]; rfl
  map_mul' p q := by
    show ((p.1.2 * q.1.2) ∣[Multiplicative.toAdd (p.1.1 * q.1.1)] x) τ = _
    rw [toAdd_mul, ModularForm.mul_slash_SL2]; rfl

open ModularForm (E₄ E₆) in
private lemma dense_setOf_ne_zero_of_mdifferentiable_of_ne_zero {D : ℍ → ℂ} (hD : MDiff D) (hD0 : D ≠ 0) :
    Dense {τ | D τ ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨τ, hτ⟩
  by_contra hempty
  have hzero : ∀ σ ∈ U, D σ = 0 := fun σ hσ => by_contra fun h => hempty ⟨σ, hσ, h⟩
  have hS : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have han : AnalyticOnNhd ℂ (D ∘ ofComplex) {w : ℂ | 0 < w.im} :=
    (UpperHalfPlane.mdifferentiable_iff.1 hD).analyticOnNhd hS
  have hev : D ∘ ofComplex =ᶠ[𝓝 (τ : ℂ)] 0 := by
    have hUc : IsOpen (((↑) : ℍ → ℂ) '' U) := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap U hU
    filter_upwards [hUc.mem_nhds ⟨τ, hτ, rfl⟩] with w hw
    obtain ⟨σ, hσ, rfl⟩ := hw
    simp [hzero σ hσ]
  have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ.im_pos hev
  apply hD0
  funext σ
  simpa using hall σ.im_pos

open ModularForm (E₄ E₆) in
theorem _root_.GlobalTheory.CosetEval.evals_independent : ∀ M : ℕ, 0 < M → (∀ x : SL(2, ℤ), x ∉ CongruenceSubgroup.Gamma M → ∃ (k : ℤ) (f : ℍ → ℂ), _root_.GlobalTheory.OddFrame.IsMF (CongruenceSubgroup.Gamma M) k f ∧ f ∣[k] x ≠ f) → ∃ τ₀ : ℍ, ∀ (ι : Type) [Fintype ι] (x : ι → SL(2, ℤ)) (c : ι → ℂ), (∀ i j, x i * (x j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j) → (∀ (k : ℤ) (f : ℍ → ℂ), _root_.GlobalTheory.OddFrame.IsMF (CongruenceSubgroup.Gamma M) k f → ∑ i, c i * (f ∣[k] x i) τ₀ = 0) → c = 0 := by
  intro M _ hsep
  classical
  have hsep' : ∀ p : SL(2, ℤ) × SL(2, ℤ), ∃ (k : ℤ) (f : ℍ → ℂ),
      _root_.GlobalTheory.OddFrame.IsMF (CongruenceSubgroup.Gamma M) k f ∧
      (p.1 * p.2⁻¹ ∉ CongruenceSubgroup.Gamma M → f ∣[k] p.1 ≠ f ∣[k] p.2) := by
    intro p
    by_cases hp : p.1 * p.2⁻¹ ∈ CongruenceSubgroup.Gamma M
    · exact ⟨0, 0, _root_.GlobalTheory.OddFrame.IsMF.zero _ _, fun h => absurd hp h⟩
    · obtain ⟨k, f, hf, hne⟩ := hsep _ hp
      refine ⟨k, f, hf, fun _ heq => hne ?_⟩
      have := congrArg (fun g => g ∣[k] p.2⁻¹) heq

      rwa [← SlashAction.slash_mul, ← SlashAction.slash_mul, mul_inv_cancel,
        SlashAction.slash_one] at this
  choose k f hf hne using hsep'
  set O : SL(2, ℤ) × SL(2, ℤ) → Set ℍ := fun p =>
    {_τ | p.1 * p.2⁻¹ ∈ CongruenceSubgroup.Gamma M} ∪
      {τ | (f p ∣[k p] p.1) τ ≠ (f p ∣[k p] p.2) τ} with hO
  have hcont : ∀ p (y : SL(2, ℤ)), Continuous (f p ∣[k p] y) := fun p y =>
    (_root_.GlobalTheory.OddFrame.mdiff_slash (hf p).2.1 _ y).continuous
  have hOopen : ∀ p, IsOpen (O p) := fun p =>
    isOpen_const.union (isOpen_ne_fun (hcont p p.1) (hcont p p.2))
  have hOdense : ∀ p, Dense (O p) := by
    intro p
    by_cases hp : p.1 * p.2⁻¹ ∈ CongruenceSubgroup.Gamma M
    · exact dense_univ.mono fun τ _ => Or.inl hp
    · have hD : MDiff (f p ∣[k p] p.1 - f p ∣[k p] p.2) :=
        (_root_.GlobalTheory.OddFrame.mdiff_slash (hf p).2.1 _ _).sub (_root_.GlobalTheory.OddFrame.mdiff_slash (hf p).2.1 _ _)
      refine (dense_setOf_ne_zero_of_mdifferentiable_of_ne_zero hD
        (fun h0 => hne p hp (sub_eq_zero.1 h0))).mono fun τ hτ => Or.inr ?_
      exact sub_ne_zero.1 hτ
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) := Subtype.countable
  obtain ⟨τ₀, hτ₀⟩ := (dense_iInter_of_isOpen hOopen hOdense).nonempty
  refine ⟨τ₀, fun ι _ x c hx hc => ?_⟩
  let χ : ι → (_root_.GlobalTheory.CosetEval.mfMonoid (CongruenceSubgroup.Gamma M) →* ℂ) :=
    fun i => _root_.GlobalTheory.CosetEval.evHom (CongruenceSubgroup.Gamma M) (x i) τ₀
  have hinj : Function.Injective χ := by
    intro i j hij
    by_contra hij'
    have hnot : x i * (x j)⁻¹ ∉ CongruenceSubgroup.Gamma M := fun h => hij' (hx i j h)
    rcases Set.mem_iInter.1 hτ₀ (x i, x j) with h | h
    · exact hnot h
    · exact h (DFunLike.congr_fun hij
        ⟨(Multiplicative.ofAdd (k (x i, x j)), f (x i, x j)), hf (x i, x j)⟩)
  have hli := (linearIndependent_monoidHom (_root_.GlobalTheory.CosetEval.mfMonoid (CongruenceSubgroup.Gamma M)) ℂ).comp χ hinj
  funext i
  refine Fintype.linearIndependent_iff.1 hli c ?_ i
  funext p
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, Pi.zero_apply]
  exact hc _ _ p.2

end GlobalTheory.CosetEval
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPointSlashEvaluationsIndependentGammaStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_slashEvaluations_independent_gamma : ∀ M : ℕ, 0 < M → (∀ x : SL(2, ℤ), x ∉ CongruenceSubgroup.Gamma M → ∃ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f ∧ f ∣[k] x ≠ f) → ∃ τ₀ : ℍ, ∀ (ι : Type) [Fintype ι] (x : ι → SL(2, ℤ)) (c : ι → ℂ), (∀ i j, x i * (x j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j) → (∀ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f → ∑ i, c i * (f ∣[k] x i) τ₀ = 0) → c = 0 := by
  first | exact @GlobalTheory.CosetEval.evals_independent | exact GlobalTheory.CosetEval.evals_independent | (intros; apply GlobalTheory.CosetEval.evals_independent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitCommDiamondOperatorOfMatrix
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

noncomputable section
namespace GlobalTheory.Hk.UDia

def gam (a b c d : ℤ) (j j' q : ℕ) (Y : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![a*d - b*q*c - a*j*c, a*b + b*j'*c + a*Y; c*d - c^2*j - c*d*q, a*d + c*d*j' + c*Y]

theorem det_gam (a b c d : ℤ) (j j' q : ℕ) (Y : ℤ) (hdet : a*d - b*c = 1)
    (hY : b = a*j + j*j'*c - j'*d - q*Y) : (gam a b c d j j' q Y).det = 1 := by
  rw [gam, Matrix.det_fin_two_of]
  subst hY
  linear_combination (a*d - (a*j + j*j'*c - j'*d - q*Y)*c + 1) * hdet

theorem alg (a b c d Y t w z j j' q : ℂ) (hq : q ≠ 0) (hdet : a*d - b*c = 1)
    (hY : b = a*j + j*j'*c - j'*d - q*Y) (hwq : w*q = t + j)
    (hzq : z*q*(c*t+d) = a*t + b + j'*(c*t+d)) :
    a*w + b = (c*t+d) * ((a*d - b*q*c - a*j*c) * z + (a*b + b*j'*c + a*Y)) ∧
    c*w + d = (c*t+d) * ((c*d - c^2*j - c*d*q) * z + (a*d + c*d*j' + c*Y)) := by
  subst hY
  constructor
  · apply mul_left_cancel₀ hq
    linear_combination a*hwq - (a*d - (a*j + j*j'*c - j'*d - q*Y)*q*c - a*j*c)*hzq
      - (a*(t+j) + (a*j + j*j'*c - j'*d - q*Y)*q)*hdet
  · apply mul_left_cancel₀ hq
    linear_combination c*hwq - (c*d - c^2*j - c*d*q)*hzq - (c*(t+j) + d*q)*hdet

theorem key {N l q : ℕ} {k : ℤ} (f : ModularForm (GlobalTheory.Hk.lev N l) k) (ρ : SL(2, ℤ))
    (hcN : ((ρ 1 0 : ℤ) : ZMod (N * l)) = 0) (hq : 0 < q) (j j' : ℕ) (Y : ℤ)
    (hY : ρ 0 1 = ρ 0 0 * j + j * j' * ρ 1 0 - j' * ρ 1 1 - q * Y) (τ : ℍ) :
    (⇑f ∣[k] ρ) (ofComplex (((τ : ℂ) + j) / q)) =
      f (ofComplex ((((ρ • τ : ℍ) : ℂ) + j') / q)) * denom ρ τ ^ (-k) := by
  have hdetZ : ρ 0 0 * ρ 1 1 - ρ 0 1 * ρ 1 0 = 1 := by
    have := ρ.det_coe; rwa [Matrix.det_fin_two] at this
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set γ : SL(2, ℤ) := ⟨gam (ρ 0 0) (ρ 0 1) (ρ 1 0) (ρ 1 1) j j' q Y,
    det_gam _ _ _ _ _ _ _ _ hdetZ hY⟩ with hγdef
  have hdiv : ((N * l : ℕ) : ℤ) ∣ ρ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcN
  have hN : ((ρ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_trans (by push_cast; exact dvd_mul_right _ _) hdiv)
  have hl : ((ρ 1 0 : ℤ) : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_trans (by push_cast; exact dvd_mul_left _ _) hdiv)
  have hγ : γ ∈ GlobalTheory.Hk.lev N l := by
    refine Subgroup.mem_inf.mpr ⟨(Gamma1_mem _ _).mpr ⟨?_, ?_, ?_⟩, Gamma0_mem.mpr ?_⟩
    · have e : γ 0 0 = 1 + ρ 1 0 * (ρ 0 1 - ρ 0 1 * q - ρ 0 0 * j) := by
        simp only [hγdef, gam]; simp; linear_combination hdetZ
      rw [e]; push_cast; rw [hN]; ring
    · have e : γ 1 1 = 1 + ρ 1 0 * (ρ 0 1 + ρ 1 1 * j' + Y) := by
        simp only [hγdef, gam]; simp; linear_combination hdetZ
      rw [e]; push_cast; rw [hN]; ring
    · have e : γ 1 0 = ρ 1 0 * (ρ 1 1 - ρ 1 0 * j - ρ 1 1 * q) := by
        simp only [hγdef, gam]; simp; ring
      rw [e]; push_cast; rw [hN]; ring
    · have e : γ 1 0 = ρ 1 0 * (ρ 1 1 - ρ 1 0 * j - ρ 1 1 * q) := by
        simp only [hγdef, gam]; simp; ring
      rw [e]; push_cast; rw [hl]; ring
  have hpos : ∀ x : ℍ, ∀ n : ℕ, 0 < (((x : ℂ) + n) / q).im := by
    intro x n
    have := x.im_pos
    rw [Complex.div_natCast_im]; simp; positivity
  set w : ℍ := ofComplex (((τ : ℂ) + j) / q) with hwdef
  set z : ℍ := ofComplex ((((ρ • τ : ℍ) : ℂ) + j') / q) with hzdef
  have hwc : (w : ℂ) = ((τ : ℂ) + j) / q := by rw [hwdef, ofComplex_apply_of_im_pos (hpos τ j)]
  have hzc : (z : ℂ) = (((ρ • τ : ℍ) : ℂ) + j') / q := by
    rw [hzdef, ofComplex_apply_of_im_pos (hpos (ρ • τ) j')]
  have hu : ((ρ 1 0 : ℤ) : ℂ) * τ + ((ρ 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := denom_ne_zero ρ τ; rwa [ModularGroup.denom_apply] at this
  have hρτ : ((ρ • τ : ℍ) : ℂ) = (((ρ 0 0 : ℤ) : ℂ) * τ + ((ρ 0 1 : ℤ) : ℂ)) /
      (((ρ 1 0 : ℤ) : ℂ) * τ + ((ρ 1 1 : ℤ) : ℂ)) := by
    rw [coe_specialLinearGroup_apply]; simp
  have hwq : (w : ℂ) * q = τ + j := by rw [hwc]; field_simp
  have hzq : (z : ℂ) * q * (((ρ 1 0 : ℤ) : ℂ) * τ + ((ρ 1 1 : ℤ) : ℂ)) =
      ((ρ 0 0 : ℤ) : ℂ) * τ + ((ρ 0 1 : ℤ) : ℂ) + (j' : ℂ) * (((ρ 1 0 : ℤ) : ℂ) * τ + ((ρ 1 1 : ℤ) : ℂ)) := by
    rw [hzc, div_mul_cancel₀ _ hqC, hρτ, add_mul, div_mul_cancel₀ _ hu]
  have hdetC : ((ρ 0 0 : ℤ) : ℂ) * ((ρ 1 1 : ℤ) : ℂ) - ((ρ 0 1 : ℤ) : ℂ) * ((ρ 1 0 : ℤ) : ℂ) = 1 := by
    exact_mod_cast hdetZ
  have hYC : ((ρ 0 1 : ℤ) : ℂ) = ((ρ 0 0 : ℤ) : ℂ) * (j : ℂ) + (j : ℂ) * (j' : ℂ) * ((ρ 1 0 : ℤ) : ℂ)
      - (j' : ℂ) * ((ρ 1 1 : ℤ) : ℂ) - (q : ℂ) * (Y : ℂ) := by exact_mod_cast hY
  obtain ⟨hA, hB⟩ := alg _ _ _ _ (Y : ℂ) (τ : ℂ) (w : ℂ) (z : ℂ) (j : ℂ) (j' : ℂ) (q : ℂ) hqC hdetC hYC hwq hzq
  have hγ10 : ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := denom_ne_zero γ z; rwa [ModularGroup.denom_apply] at this
  have hsm : ρ • w = γ • z := by
    apply UpperHalfPlane.ext
    rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
    simp only [hγdef, gam, algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    push_cast
    rw [hA, hB, mul_div_mul_left _ _ hu]
  have hden : denom ρ w = denom ρ τ * denom γ z := by
    rw [ModularGroup.denom_apply, ModularGroup.denom_apply, ModularGroup.denom_apply, hB]
    simp only [hγdef, gam]
    simp
  rw [ModularForm.SL_slash_apply, hsm, SlashInvariantForm.slash_action_eqn_SL'' f hγ z, hden, mul_zpow]
  have h1 := denom_ne_zero ρ τ
  have h2 := denom_ne_zero γ z
  rw [zpow_neg, zpow_neg]
  field_simp

theorem cast_toNat_emod {q : ℕ} (hq : 0 < q) (x : ℤ) :
    (((x % (q : ℤ)).toNat : ℕ) : ZMod q) = (x : ZMod q) := by
  have h0 : 0 ≤ x % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
  rw [show (((x % (q : ℤ)).toNat : ℕ) : ZMod q) = (((x % (q : ℤ)).toNat : ℤ) : ZMod q) by
    push_cast; rfl, Int.toNat_of_nonneg h0, ZMod.intCast_mod]

theorem toNat_emod_lt {q : ℕ} (hq : 0 < q) (x : ℤ) : (x % (q : ℤ)).toNat < q := by
  have h1 : x % (q : ℤ) < q := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
  omega

theorem eq_of_cast_eq {q : ℕ} {i i' : ℕ} (hi : i < q) (hi' : i' < q)
    (h : (i : ZMod q) = (i' : ZMod q)) : i = i' := by
  haveI : NeZero q := ⟨by omega⟩
  rw [← ZMod.val_cast_of_lt hi, ← ZMod.val_cast_of_lt hi', h]

end GlobalTheory.Hk.UDia

open GlobalTheory.Hk.UDia in
theorem GlobalTheory.Hk.uOp_dia_comm : ∀ (N l q : ℕ) (k d : ℤ) (ρ : SL(2, ℤ)), 0 < N → 0 < l → q.Prime →
    q ∣ N * l → GlobalTheory.Hk.IsDia N l d ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.uOp q (GlobalTheory.Hk.dia k ρ ⇑f) = GlobalTheory.Hk.dia k ρ (GlobalTheory.Hk.uOp q ⇑f) := by
  intro N l q k d ρ _ _ hqp hqNl hρ f
  have hq : 0 < q := hqp.pos
  have hcN := hρ.1
  have hdetZ : ρ 0 0 * ρ 1 1 - ρ 0 1 * ρ 1 0 = 1 := by
    have := ρ.det_coe; rwa [Matrix.det_fin_two] at this
  have hdiv : ((N * l : ℕ) : ℤ) ∣ ρ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcN
  have hcq : ((ρ 1 0 : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_trans (by exact_mod_cast hqNl) hdiv)
  have had : ((ρ 0 0 : ℤ) : ZMod q) * ((ρ 1 1 : ℤ) : ZMod q) = 1 := by
    have h := congrArg (fun x : ℤ => (x : ZMod q)) hdetZ
    push_cast at h; rw [hcq] at h; linear_combination h
  set a : ℤ := ρ 0 0
  set b : ℤ := ρ 0 1
  set dd : ℤ := ρ 1 1
  let φ : ℕ → ℕ := fun i => ((a * (a * i - b)) % (q : ℤ)).toNat
  let ψ : ℕ → ℕ := fun i => ((dd * (dd * i + b)) % (q : ℤ)).toNat
  funext τ
  simp only [GlobalTheory.Hk.dia]
  rw [ModularForm.SL_slash_apply]
  simp only [GlobalTheory.Hk.uOp]
  rw [mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  have hterm : ∀ i ∈ Finset.range q, (⇑f ∣[k] ρ) (ofComplex (((τ : ℂ) + i) / q)) =
      f (ofComplex ((((ρ • τ : ℍ) : ℂ) + (φ i : ℕ)) / q)) * denom ρ τ ^ (-k) := by
    intro i _
    have hX : ((q : ℕ) : ℤ) ∣ a * i + i * (φ i) * ρ 1 0 - (φ i) * dd - b := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [cast_toNat_emod hq, hcq]
      push_cast
      linear_combination (-(((a : ℤ) : ZMod q) * i - b)) * had
    obtain ⟨Y, hY⟩ := hX
    exact key f ρ hcN hq i (φ i) Y (by linear_combination -hY) τ
  rw [Finset.sum_congr rfl hterm]
  refine Finset.sum_nbij' φ ψ ?_ ?_ ?_ ?_ ?_
  · intro i _; simpa using toNat_emod_lt hq _
  · intro i _; simpa using toNat_emod_lt hq _
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_range] at hi
    apply eq_of_cast_eq (toNat_emod_lt hq _) hi
    simp only [ψ, φ]
    rw [cast_toNat_emod hq]; push_cast; rw [cast_toNat_emod hq]; push_cast
    linear_combination ((((a : ℤ) : ZMod q) * dd + 1) * i - dd * b) * had
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_range] at hi
    apply eq_of_cast_eq (toNat_emod_lt hq _) hi
    simp only [ψ, φ]
    rw [cast_toNat_emod hq]; push_cast; rw [cast_toNat_emod hq]; push_cast
    linear_combination ((((a : ℤ) : ZMod q) * dd + 1) * i + a * b) * had
  · intro i _; rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOddWeightFrameDetNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOddWeightFrameDetNeZero
noncomputable section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem exists_coset_reps {M : ℕ} (hM : 0 < M) (Γ : Subgroup SL(2, ℤ)) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : Nonempty Q) (t : Q → SL(2, ℤ)), (∀ q, t q ∈ Γ) ∧
      (∀ q q', t q * (t q')⁻¹ ∈ CongruenceSubgroup.Gamma M → q = q') ∧
      ∀ γ ∈ Γ, ∃ π : Equiv.Perm Q, ∀ q, ∃ g ∈ CongruenceSubgroup.Gamma M, t q * γ = g * t (π q) := by
  classical
  have : (CongruenceSubgroup.Gamma M).FiniteIndex := finiteIndex_of_Gamma_le hM le_rfl
  have : (CongruenceSubgroup.Gamma M).Normal := CongruenceSubgroup.Gamma_normal M

  let H : Subgroup (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M) :=
    Γ.map (QuotientGroup.mk' (CongruenceSubgroup.Gamma M))
  have hq : ∀ q : H, ∃ γ ∈ Γ, QuotientGroup.mk' (CongruenceSubgroup.Gamma M) γ = (q : _) :=
    fun q => Subgroup.mem_map.1 q.2
  choose t ht hmk using hq
  refine ⟨H, Fintype.ofFinite H, ⟨1⟩, t, ht, ?_, ?_⟩
  · intro q q' h
    apply Subtype.ext
    rw [← hmk q, ← hmk q', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
    exact h
  · intro γ hγ
    let g : H := ⟨QuotientGroup.mk' _ γ, Subgroup.mem_map_of_mem _ hγ⟩
    refine ⟨Equiv.mulRight g, fun q => ⟨t q * γ * (t (Equiv.mulRight g q))⁻¹, ?_, by group⟩⟩
    have h1 : QuotientGroup.mk' (CongruenceSubgroup.Gamma M) (t q * γ) =
        QuotientGroup.mk' (CongruenceSubgroup.Gamma M) (t (Equiv.mulRight g q)) := by
      rw [map_mul, hmk, hmk]
      rfl
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem,
      div_eq_mul_inv] at h1
    exact h1

theorem IsMF.sum_slash_reps {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {Q : Type} [Fintype Q] {t : Q → SL(2, ℤ)}
    (ht : ∀ γ ∈ Γ, ∃ π : Equiv.Perm Q, ∀ q, ∃ g ∈ CongruenceSubgroup.Gamma M, t q * γ = g * t (π q))
    {k : ℤ} {f : ℍ → ℂ} (hf : IsMF (CongruenceSubgroup.Gamma M) k f) : IsMF Γ k (∑ q, f ∣[k] t q) := by
  classical
  have : (CongruenceSubgroup.Gamma M).Normal := CongruenceSubgroup.Gamma_normal M
  have hsum : ∀ (A : SL(2, ℤ)) (u : Finset Q) (g : Q → ℍ → ℂ),
      (∑ q ∈ u, g q) ∣[k] A = ∑ q ∈ u, g q ∣[k] A := by
    intro A u g
    refine Finset.induction_on u (by simp) ?_
    intro a u ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

  have hx : ∀ x : SL(2, ℤ), IsMF (CongruenceSubgroup.Gamma M) k (f ∣[k] x) := by
    intro x
    unfold IsMF
    refine ⟨fun g hg => ?_, mdiff_slash hf.2.1 k x, fun y => ?_⟩
    · rw [← SlashAction.slash_mul]
      have e : x * g = (x * g * x⁻¹) * x := by group
      rw [e, IsMF.slash_mul hf ((inferInstance : (CongruenceSubgroup.Gamma M).Normal).conj_mem g hg x) x]
    · rw [← SlashAction.slash_mul]
      exact hf.2.2 (x * y)
  have hS : IsMF (CongruenceSubgroup.Gamma M) k (∑ q, f ∣[k] t q) :=
    IsMF.sum Finset.univ (fun q _ => hx (t q))
  unfold IsMF
  refine ⟨fun γ hγ => ?_, hS.2.1, hS.2.2⟩
  obtain ⟨π, hπ⟩ := ht γ hγ
  rw [hsum]
  calc ∑ q, (f ∣[k] t q) ∣[k] γ = ∑ q, f ∣[k] t (π q) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        obtain ⟨g, hg, he⟩ := hπ q
        rw [← SlashAction.slash_mul, he, IsMF.slash_mul hf hg]
    _ = ∑ q, f ∣[k] t q := Equiv.sum_comp π (fun q => f ∣[k] t q)

theorem IsReps.signed_reps_injective {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {r : ℕ} {s : Fin r → SL(2, ℤ)}
    (hle : CongruenceSubgroup.Gamma M ≤ Γ) (hneg : (-1 : SL(2, ℤ)) ∉ Γ) (hs : IsReps Γ s)
    {Q : Type} {t : Q → SL(2, ℤ)} (ht : ∀ q, t q ∈ Γ)
    (hinj : ∀ q q', t q * (t q')⁻¹ ∈ CongruenceSubgroup.Gamma M → q = q') :
    (∀ i j q q', t q * s i * (t q' * s j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j ∧ q = q') ∧
      ∀ i j q q', -(t q * s i * (t q' * s j)⁻¹) ∉ CongruenceSubgroup.Gamma M := by
  have hA : ∀ i j q q' (γ : SL(2, ℤ)), γ ∈ Γ →
      (s i = (t q)⁻¹ * γ * t q' * s j ∨ s i = -((t q)⁻¹ * γ * t q' * s j)) → i = j := by
    intro i j q q' γ hγ h
    exact hs.2 i j _ (Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (ht q)) hγ) (ht q')) h
  have key : ∀ i j q q', (t q)⁻¹ * (t q * s i * (t q' * s j)⁻¹) * t q' * s j = s i := by
    intro i j q q'; group
  have diag : ∀ i q q', t q * s i * (t q' * s i)⁻¹ = t q * (t q')⁻¹ := by
    intro i q q'; group
  refine ⟨fun i j q q' h => ?_, fun i j q q' h => ?_⟩
  · have hij : i = j := hA i j q q' _ (hle h) (Or.inl (key i j q q').symm)
    subst hij
    refine ⟨rfl, hinj q q' ?_⟩
    rwa [diag] at h
  · have hΓ := hle h
    have hij : i = j := by
      refine hA i j q q' _ hΓ (Or.inr ?_)
      rw [mul_neg, neg_mul, neg_mul, key, neg_neg]
    subst hij
    rw [diag] at hΓ
    apply hneg
    have hY : t q * (t q')⁻¹ ∈ Γ := Γ.mul_mem (ht q) (Γ.inv_mem (ht q'))
    have e : (-1 : SL(2, ℤ)) = -(t q * (t q')⁻¹) * (t q * (t q')⁻¹)⁻¹ := by
      rw [neg_mul, mul_inv_cancel]
    rw [e]
    exact Γ.mul_mem hΓ (Γ.inv_mem hY)

theorem exists_odd_det_evM_ne_zero (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (τ₀ : ℍ)
    (hM : 0 < M) (hle : CongruenceSubgroup.Gamma M ≤ Γ) (hneg : (-1 : SL(2, ℤ)) ∉ Γ) (hs : IsReps Γ s)
    (H : ∀ (ι : Type) [Fintype ι] (x : ι → SL(2, ℤ)) (c : ι → ℂ),
      (∀ i j, x i * (x j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j) →
      (∀ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f → ∑ i, c i * (f ∣[k] x i) τ₀ = 0) →
      c = 0) :
    ∃ (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) ∧
      (evM s w F τ₀).det ≠ 0 := by
  classical
  obtain ⟨Q, _, ⟨q0⟩, t, ht, hinj, hperm⟩ := exists_coset_reps hM Γ
  have hsum : ∀ (A : SL(2, ℤ)) (k : ℤ) (u : Finset Q) (g : Q → ℍ → ℂ),
      (∑ q ∈ u, g q) ∣[k] A = ∑ q ∈ u, g q ∣[k] A := by
    intro A k u g
    refine Finset.induction_on u (by simp) ?_
    intro a u ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]
  obtain ⟨hpos, hneg'⟩ := IsReps.signed_reps_injective hle hneg hs ht hinj

  let vec : ℤ → (ℍ → ℂ) → Fin r → ℂ := fun k f i => ((∑ q, f ∣[k] t q) ∣[k] s i) τ₀
  let V : Set (Fin r → ℂ) :=
    {v | ∃ k f, Odd k ∧ IsMF (CongruenceSubgroup.Gamma M) k f ∧ v = vec k f}
  have hvec : ∀ k f i, vec k f i = ∑ q, (f ∣[k] (t q * s i)) τ₀ := by
    intro k f i
    simp only [vec]
    rw [hsum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun q _ => by rw [SlashAction.slash_mul]

  have hV : Submodule.span ℂ V = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let c : Fin r → ℂ := fun i => φ (fun j => if i = j then 1 else 0)
    have hφc : ∀ v, φ v = ∑ i, v i * c i := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ φ v]
      simp only [c, smul_eq_mul]
    apply hφ
    have hc0 : c = 0 := by
      let x : Bool × Fin r × Q → SL(2, ℤ) := fun a =>
        if a.1 then t a.2.2 * s a.2.1 else -(t a.2.2 * s a.2.1)
      let c' : Bool × Fin r × Q → ℂ := fun a => if a.1 then c a.2.1 else -c a.2.1
      have ineg : ∀ B : SL(2, ℤ), (-B)⁻¹ = -B⁻¹ := fun B =>
        inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
      have hx : ∀ a b, x a * (x b)⁻¹ ∈ CongruenceSubgroup.Gamma M → a = b := by
        rintro ⟨_ | _, i, q⟩ ⟨_ | _, j, q'⟩ h <;>
          simp only [x, Bool.false_eq_true, ↓reduceIte] at h
        · rw [ineg, neg_mul_neg] at h
          obtain ⟨rfl, rfl⟩ := hpos i j q q' h
          rfl
        · rw [neg_mul] at h
          exact absurd h (hneg' i j q q')
        · rw [ineg, mul_neg] at h
          exact absurd h (hneg' i j q q')
        · obtain ⟨rfl, rfl⟩ := hpos i j q q' h
          rfl
      have hrel : ∀ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f →
          ∑ a, c' a * (f ∣[k] x a) τ₀ = 0 := by
        intro k f hf
        rw [Fintype.sum_prod_type, Fintype.sum_bool]
        simp only [x, c', Bool.false_eq_true, ↓reduceIte]
        rcases Int.even_or_odd k with hk | hk
        · simp only [slash_neg_of_even hk, neg_mul, Finset.sum_neg_distrib, add_neg_cancel]
        · have h0 : φ (vec k f) = 0 := hker (Submodule.subset_span ⟨k, f, hk, hf, rfl⟩)
          rw [hφc] at h0
          simp only [hvec] at h0
          have hS : ∑ i, ∑ q, c i * (f ∣[k] (t q * s i)) τ₀ = 0 := by
            rw [← h0]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.mul_sum, mul_comm]
          simp only [slash_neg_of_odd hk, Pi.neg_apply, neg_mul_neg]
          rw [Fintype.sum_prod_type, hS, add_zero]
      have hc'0 := H _ x c' hx hrel
      funext i
      simpa [c'] using congrFun hc'0 (true, i, q0)
    refine LinearMap.ext fun v => ?_
    rw [hφc v, hc0]
    simp

  obtain ⟨b, hbV, hspan, hli⟩ := exists_linearIndependent ℂ V
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Fin r → ℂ)) := by
    rw [Subtype.range_coe, hspan, hV]
  let e := (Pi.basisFun ℂ (Fin r)).indexEquiv (Module.Basis.mk hli hsp)
  have hmem : ∀ j, ∃ k f, Odd k ∧ IsMF (CongruenceSubgroup.Gamma M) k f ∧
      (e j : Fin r → ℂ) = vec k f := fun j => hbV (e j).2
  choose w f hw hf hv using hmem
  refine ⟨w, fun j => ∑ q, f j ∣[w j] t q, fun j => ⟨hw j, IsMF.sum_slash_reps hperm (hf j)⟩, ?_⟩
  have hcols : (fun j => Matrix.transpose (evM s w (fun j => ∑ q, f j ∣[w j] t q) τ₀) j) =
      fun j => (e j : Fin r → ℂ) := by
    funext j i
    rw [hv j]
    rfl
  have hli' : LinearIndependent ℂ (fun j => Matrix.transpose (evM s w (fun j => ∑ q, f j ∣[w j] t q) τ₀) j) := by
    rw [hcols]
    exact hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli')).ne_zero

end GlobalTheory.OddFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOddWeightFrameDetNeZeroStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_odd_weight_frame_det_ne_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (τ₀ : ℍ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → (-1 : SL(2, ℤ)) ∉ Γ → IsReps Γ s → (∀ (ι : Type) [Fintype ι] (x : ι → SL(2, ℤ)) (c : ι → ℂ), (∀ i j, x i * (x j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j) → (∀ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f → ∑ i, c i * (f ∣[k] x i) τ₀ = 0) → c = 0) → ∃ (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) ∧ (evM s w F τ₀).det ≠ 0 := by
  first | exact @GlobalTheory.OddFrame.exists_odd_det_evM_ne_zero | exact GlobalTheory.OddFrame.exists_odd_det_evM_ne_zero | (intros; apply GlobalTheory.OddFrame.exists_odd_det_evM_ne_zero <;> assumption)
end
end
