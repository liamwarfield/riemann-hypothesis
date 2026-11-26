module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecSmoothAtGapOfDecSmooth
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrep

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorStdRelAdjointSplitCasimir
open Formalism.REAL

namespace GlobalTheory

theorem tensorStd_rel_adjoint_splitCasimir : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → GlRel Et ∧ (∀ a b x y, inner ℂ (Et a b x) y = inner ℂ x (Et b a y)) ∧ Om.IsSymmetric ∧ ∀ a b, Om * Et a b = Et a b * Om := by
  intro V _ _ _ n E Et Om hE hadj hEt hOm
  have hv : ∀ a b c d v, E a b (E c d v) = E c d (E a b v) +
      ((if b = c then E a d v else 0) - if d = a then E c b v else 0) := by
    intro a b c d v
    have h := LinearMap.congr_fun (hE a b c d) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [← sub_eq_iff_eq_add', h]
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c d
    refine LinearMap.ext fun y => PiLp.ext fun k => ?_
    have h1 : ((if b = c then Et a d else 0) - if d = a then Et c b else 0 :
        Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) y k =
        (if b = c then Et a d y k else 0) - if d = a then Et c b y k else 0 := by
      split_ifs <;> simp
    rw [h1]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, PiLp.sub_apply, hEt, map_add (f := _)]
    rw [hv a b c d]
    split_ifs <;> (try simp only [map_zero]) <;> abel
  · intro a b x y
    simp only [PiLp.inner_apply, hEt, inner_add_left, inner_add_right, Finset.sum_add_distrib, hadj]
    congr 1
    have h1 : ∀ c, inner ℂ (if c = a then x b else 0) (y c) =
        if c = a then inner ℂ (x b) (y c) else 0 := by
      intro c; split_ifs <;> simp
    have h2 : ∀ c, inner ℂ (x c) (if c = b then y a else 0) =
        if c = b then inner ℂ (x c) (y a) else 0 := by
      intro c; split_ifs <;> simp
    simp [h1, h2]
  · intro x y
    simp only [PiLp.inner_apply, hOm, sum_inner, inner_sum, hadj]
    exact Finset.sum_comm
  · intro a b
    refine LinearMap.ext fun y => PiLp.ext fun k => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Module.End.mul_apply, hEt, hOm, map_add (f := _), map_sum, Finset.sum_add_distrib]
    have h1 : ∀ c, E c k (E a b (y c)) = _ := fun c => hv c k a b (y c)
    simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, apply_ite (E _ k), map_zero]
    by_cases h : k = a
    · simp [h, add_assoc]
    · simp [h]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerStepRaisingUnitaryComplement
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTensorStandardRep
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

noncomputable section

namespace GlobalTheory.TensorStd

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {k : ℕ}

def tenOp (C : Fin k → Fin k → ℂ) (A : V →L[ℂ] V) :
    PiLp 2 (fun _ : Fin k => V) →L[ℂ] PiLp 2 (fun _ : Fin k => V) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => V)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun c => ∑ d, C c d • (A ∘L PiLp.proj 2 (fun _ : Fin k => V) d)

theorem tenOp_apply (C : Fin k → Fin k → ℂ) (A : V →L[ℂ] V) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    tenOp C A y c = ∑ d, C c d • A (y d) := by
  simp [tenOp]

private lemma inner_map_of_norm_eq (A : V →L[ℂ] V) (hA : ∀ v, ‖A v‖ = ‖v‖) (u w : V) :
    inner ℂ (A u) (A w) = inner ℂ u w :=
  (⟨A.toLinearMap, hA⟩ : V →ₗᵢ[ℂ] V).inner_map_map u w

theorem tenOp_norm (C : Fin k → Fin k → ℂ) (A : V →L[ℂ] V)
    (hC : ∀ d e, ∑ c, C c e * star (C c d) = if e = d then 1 else 0) (hA : ∀ v, ‖A v‖ = ‖v‖)
    (y : PiLp 2 (fun _ : Fin k => V)) : ‖tenOp C A y‖ = ‖y‖ := by
  have key : inner ℂ (tenOp C A y) (tenOp C A y) = inner ℂ y y := by
    simp only [PiLp.inner_apply, tenOp_apply, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, inner_map_of_norm_eq A hA]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ e, ∑ c, C c d * ((starRingEnd ℂ) (C c e) * inner ℂ (y e) (y d)) =
        (if d = e then 1 else 0) * inner ℂ (y e) (y d) := by
      intro e
      rw [← hC e d, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [Complex.star_def]
      ring
    simp only [hterm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), key]

end GlobalTheory.TensorStd

namespace GlobalTheory

open TensorStd

private lemma herm_sum_smul_left' {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m → ℂ)
    (w : Fin m → Fin n → ℂ) (u : Fin n → ℂ) :
    herm H (∑ c, a c • w c) u = ∑ c, a c * herm H (w c) u := by
  simp [herm, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul]

private lemma herm_sum_smul_right' {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m → ℂ)
    (w : Fin m → Fin n → ℂ) (v : Fin n → ℂ) :
    herm H v (∑ c, a c • w c) = ∑ c, star (a c) * herm H v (w c) := by
  simp [herm, star_sum, sum_dotProduct, star_smul, smul_dotProduct]

theorem exists_tensor_standard_rep :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → IsRepW k r z π → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → IsFrameOf k r [z] B → ∃ πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V))), IsRepW k r z πt ∧ (∀ h ∈ UWset k r z, ∀ v, ‖πt h v‖ = ‖v‖) ∧ (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d)) := by
  intro V _ _ _ k r z π B hz hT hπ hiso hB
  obtain ⟨hcomp, hgrp⟩ := GlobalTheory.FrameExpansion.frame_expansion_uw_group k r z B hz hT hB

  have hexp : ∀ h ∈ UWset k r z, ∀ d,
      h *ᵥ B d = ∑ e, herm (Hpk k r) (h *ᵥ B d) (B e) • B e := by
    intro h hh d
    obtain ⟨h1, h2⟩ := (hgrp h hh).1 (B d) (hB.1 d) (hB.2.2 d z (List.mem_singleton_self z))
    exact hcomp _ h1 h2
  refine ⟨fun h => tenOp (fun c d => herm (Hpk k r) (h *ᵥ B d) (B c)) (π h), ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun y => PiLp.ext fun c => ?_
    rw [tenOp_apply, hπ.1.1]
    simp [hB.2.1]
  · intro a ha b hb
    refine ContinuousLinearMap.ext fun y => PiLp.ext fun c => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ContinuousLinearMap.comp_apply, tenOp_apply, hπ.1.2 a ha b hb, map_sum, map_smul,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    conv_lhs => rw [← Matrix.mulVec_mulVec, hexp b hb d, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    rw [herm_sum_smul_left']
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  · rw [continuousOn_clm_apply]
    intro y
    have hrepr : ∀ h, tenOp (fun c d => herm (Hpk k r) (h *ᵥ B d) (B c)) (π h) y =
        (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => V)).symm
          (fun c => ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d)) := by
      intro h
      exact PiLp.ext fun c => by rw [tenOp_apply]; rfl
    simp only [hrepr]
    refine (PiLp.continuousLinearEquiv 2 ℂ _).symm.continuous.comp_continuousOn ?_
    refine continuousOn_pi.2 fun c => continuousOn_finsetSum _ fun d _ => ?_
    refine ContinuousOn.smul ?_ (hπ.2.clm_apply continuousOn_const)
    exact Continuous.continuousOn (by unfold herm; fun_prop)
  · intro h hh y
    refine tenOp_norm _ _ (fun d e => ?_) (hiso h hh) y
    have hpres := (hgrp h hh).2.1 (B e) (B d)
    rw [hB.2.1 e d] at hpres
    rw [← hpres]
    conv_rhs => rw [hexp h hh d, herm_sum_smul_right']
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  · intro h hh y c
    exact tenOp_apply _ _ _ _

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.OpNormSumSmulSqLe
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh.ContrPlus

theorem herm_sum_smul_left {ι κ : Type} [Fintype ι] [Fintype κ] (H : Matrix ι ι ℂ) (l : κ → ℂ) (B : κ → ι → ℂ)
    (w : ι → ℂ) : herm H (∑ c, l c • B c) w = ∑ c, l c * herm H (B c) w := by
  unfold herm
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_conj {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (v w : ι → ℂ) :
    herm H w v = star (herm H v w) := by
  unfold herm
  rw [← star_dotProduct_star, star_star, Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec]

theorem herm_real_smul_right {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (t : ℝ) (v w : ι → ℂ) :
    herm H v ((t : ℂ) • w) = (t : ℂ) * herm H v w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]
  simp

theorem opNorm_sum_smul_sq_le {V V₂ κ : Type} [Fintype κ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (a : κ → (V₂ →L[ℂ] V)) (l : κ → ℂ)
    (ha : ∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) : ‖∑ c, l c • a c‖ ^ 2 ≤ ∑ c, ‖l c‖ ^ 2 := by
  have hS : 0 ≤ ∑ c, ‖l c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have h1 : ‖∑ c, l c • a c‖ ≤ Real.sqrt (∑ c, ‖l c‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
    have h2 : ‖(∑ c, l c • a c) y‖ ≤ ∑ c, ‖l c‖ * ‖a c y‖ := by
      rw [ContinuousLinearMap.sum_apply]
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
      rw [ContinuousLinearMap.smul_apply, norm_smul]
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun c => ‖l c‖) (fun c => ‖a c y‖)
    rw [ha y] at h3
    refine h2.trans ?_
    have h4 := Real.le_sqrt_of_sq_le h3
    rwa [Real.sqrt_mul hS, Real.sqrt_sq (norm_nonneg y)] at h4
  calc _ ≤ Real.sqrt (∑ c, ‖l c‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = _ := Real.sq_sqrt hS

theorem contraction_wigMap :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (a : Fin k → (V₂ →L[ℂ] V)), inWb k r z → 0 < Tz k r z → IsFrameOf k r [z] B → (∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) → (∀ h ∈ UWset k r z, ∀ y c, a c (π₂ h y) = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (a d y)) → GlobalTheory.WigSh.WigMap k r z π₂ π 1 (fun ω => ∑ c, herm (Hpk k r) (B c) ω • a c) ∧ ∀ c₀, (∑ c, herm (Hpk k r) (B c) (B c₀) • a c) = a c₀ := by
  intro V _ _ _ k r z π B V₂ _ _ _ π₂ a hz hT hB ha hequi
  obtain ⟨hcomp, hU⟩ := GlobalTheory.FrameExpansion.frame_expansion_uw_group k r z B hz hT hB
  have hH : (Hpk k r)ᴴ = Hpk k r := (hermitian_pos_facts_hold k r).1
  refine ⟨⟨⟨k, fun c => ∑ j, MvPolynomial.C ((Hpk k r *ᵥ B c) j) * MvPolynomial.X (Sum.inr j), a, ?_, ?_⟩,
    ?_, ?_, ?_⟩, ?_⟩
  · intro c
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  · intro ω
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    simp [herm, dotProduct, mul_comm]
  · intro h hh ω
    obtain ⟨hW, hiso, -⟩ := hU h hh
    ext y
    have key : ∀ d, ∑ c, herm (Hpk k r) (h *ᵥ B d) (B c) * herm (Hpk k r) (B c) (h *ᵥ ω)
        = herm (Hpk k r) (B d) ω := by
      intro d
      obtain ⟨h1, h2⟩ := hW (B d) (hB.1 d) (hB.2.2 d z (by simp))
      rw [← herm_sum_smul_left, ← hcomp _ h1 h2, hiso]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      map_sum, map_smul, hequi h hh, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_smul, ← key d]
    simp only [mul_comm]
  · intro t ω
    simp only [herm_real_smul_right, pow_one, Finset.smul_sum, smul_smul]
  · intro ω h1 h2
    rw [pow_one]
    refine (opNorm_sum_smul_sq_le a _ ha).trans (le_of_eq ?_)
    have h3 : herm (Hpk k r) ω ω = ∑ c, herm (Hpk k r) ω (B c) * herm (Hpk k r) (B c) ω := by
      rw [← herm_sum_smul_left, ← hcomp _ h1 h2]
    rw [h3, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [herm_conj _ hH (B c) ω, Complex.star_def, Complex.conj_mul']
    norm_cast
  · intro c₀
    simp [hB.2.1]

end GlobalTheory.WigSh.ContrPlus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoefHasDerivAt
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

namespace GlobalTheory.TensorStd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable def coefL {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => herm H (g *ᵥ v) w
      map_add' := fun g h => by simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
      map_smul' := fun c g => by simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul] }

theorem coefL_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    coefL H v w g = herm H (g *ᵥ v) w := rfl

theorem coef_hasDerivAt {k r : ℕ} (X : Mx k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    HasDerivAt (fun t : ℝ => herm (Hpk k r) (NormedSpace.exp ((t : ℂ) • X) *ᵥ v) w)
      (herm (Hpk k r) (X *ᵥ v) w) 0 := by
  have h1 := B5.curve_hasDerivAt (1 : Mx k r) X 0
  simp only [Matrix.one_mul, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero] at h1
  exact ((coefL (Hpk k r) v w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1

theorem hpart_sum {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H Z + Complex.I • hpart2 H Z = Z := by
  unfold hpart1 hpart2
  rw [smul_smul]
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [this, ← smul_add]
  have : Z - H⁻¹ * Zᴴ * H + (Z + H⁻¹ * Zᴴ * H) = (2 : ℂ) • Z := by rw [two_smul]; abel
  rw [this, smul_smul]; norm_num

theorem dOp_tensor {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (V →L[ℂ] V)} {B : Fin k → (Fin (2 * r + k + 1) → ℂ)}
    {πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))}
    (hπ : IsRepW k r z π) (hπt : IsRepW k r z πt) (hB : IsFrameOf k r [z] B)
    (hf : ∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d))
    {X : Mx k r} (hX : InLieW k r z X) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    dOp πt X y c = dOp π X (y c) + ∑ d, herm (Hpk k r) (X *ᵥ B d) (B c) • y d := by
  have h1 := dOp_hasDeriv hπt.1 hπt.2 hX
  have h2 := dOp_hasDeriv hπ.1 hπ.2 hX
  have h3 : HasDerivAt (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) (dOp πt X y c) 0 :=
    (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin k => V) c).comp
      (ContinuousLinearMap.apply ℂ _ y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h4 : ∀ d, HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) (y d)) (dOp π X (y d)) 0 := fun d =>
    ((ContinuousLinearMap.apply ℂ V (y d)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h5 := HasDerivAt.fun_sum (u := Finset.univ) fun d _ => (coef_hasDerivAt X (B d) (B c)).fun_smul (h4 d)
  have h6 : (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) = fun t : ℝ => ∑ d,
      herm (Hpk k r) (NormedSpace.exp ((t : ℂ) • X) *ᵥ B d) (B c) • π (NormedSpace.exp ((t : ℂ) • X)) (y d) :=
    funext fun t => hf _ (exp_uw hX t) y c
  rw [h6] at h3
  rw [h3.unique h5]
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec, hπ.1.1, hB.2.1,
    Finset.sum_add_distrib, one_apply_eq_self]
  simp

theorem EB_tensor_std : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))), inWb k r z → 0 < Tz k r z → IsRepW k r z π → IsRepW k r z πt → IsFrameOf k r [z] B → (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d)) → ∀ a b y c, EB πt B a b y c = EB π B a b (y c) + if c = a then y b else 0 := by
  intro V _ _ _ k r z π B πt _ _ hπ hπt hB hf a b y c
  obtain ⟨l1, l2⟩ := frame_lie hB a b
  have e1 := dOp_tensor hπ hπt hB hf l1 y c
  have e2 := dOp_tensor hπ hπt hB hf l2 y c
  have e3 : ∀ d, herm (Hpk k r) (hpart1 (Hpk k r) (unitB (Hpk k r) B a b) *ᵥ B d) (B c) +
      Complex.I * herm (Hpk k r) (hpart2 (Hpk k r) (unitB (Hpk k r) B a b) *ᵥ B d) (B c) =
      if d = b then (if c = a then 1 else 0) else 0 := by
    intro d
    rw [← coefL_apply, ← coefL_apply, ← smul_eq_mul Complex.I, ← map_smul, ← map_add (f := _), hpart_sum, coefL_apply,
      Qx8.unitB_mulVec, hB.2.1]
    have := hB.2.1 a c
    by_cases hd : d = b
    · subst hd
      have e : herm (Hpk k r) ((1 : ℂ) • B a) (B c) = herm (Hpk k r) (B a) (B c) := by rw [one_smul]
      rw [if_pos rfl, if_pos rfl, e, this]
      simp only [eq_comm]
    · simp [hd, herm]
  show dOp πt _ y c + Complex.I • dOp πt _ y c = (dOp π _ (y c) + Complex.I • dOp π _ (y c)) + _
  rw [e1, e2, smul_add, Finset.smul_sum, add_add_add_comm, ← Finset.sum_add_distrib]
  congr 1
  simp only [smul_smul, ← add_smul, e3]
  by_cases hc : c = a <;> simp [hc]

end GlobalTheory.TensorStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriRaisingSubmoduleGlSucc
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarProjectionSplitCasimirRaisingLast
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirStdEigenvalue
open Formalism.REAL

namespace GlobalTheory

theorem splitCasimirStd_eigenvalue : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (lam : ℂ) (x : (PiLp 2 (fun _ : Fin (n + 1) => V))), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + 0 := by
  intro V _ _ _ n E Et Om m hE hadj hq hEt hOm lam x hx hlam
  obtain ⟨K, hK, -⟩ := GlobalTheory.T.capelli_comatrix_last_row_inverts_casimir V n E Om m hE hq hOm
  obtain ⟨-, -, -, hc⟩ := tensorStd_rel_adjoint_splitCasimir V n E Et Om hE hadj hEt hOm
  by_contra hne
  have hprod : (∏ j, (-lam + m j)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun j _ h => hne ⟨j, ?_⟩
    linear_combination -h
  have hlast : ∀ y, Om y = lam • y → y (Fin.last n) = 0 := by
    intro y hy
    have h := hK (-lam) y
    rw [hy, sub_zero, neg_smul, neg_add_cancel, map_zero] at h
    exact (smul_eq_zero.1 h.symm).resolve_left hprod
  apply hx
  refine PiLp.ext fun c => ?_
  have h1 : Om (Et (Fin.last n) c x) = lam • Et (Fin.last n) c x := by
    have h := LinearMap.congr_fun (hc (Fin.last n) c) x
    simp only [Module.End.mul_apply] at h
    rw [h, hlam, map_smul]
  have h2 := hlast _ h1
  rw [hEt, hlast x hlam] at h2
  simpa using h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarProjectionSplitCasimirRaisingLast
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

theorem starProjection_splitCasimirStd_last : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + 0)).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  intro V _ _ _ n E Et Om β L l hH hadj hEt hOm M v hv
  have hq : ∀ w v, qdet E w v = (∏ j, (w + shf β L j)) • v := hH.cap
  obtain ⟨K, hK, hK'⟩ := comatrix_last_row_inverts_casimir V n E Om (shf β L) hH.gl hq hOm
  obtain ⟨-, -, hsym, -⟩ := tensorStd_rel_adjoint_splitCasimir V n E Et Om hH.gl hadj hEt hOm
  have hev := splitCasimirStd_eigenvalue V n E Et Om (shf β L) hH.gl hadj hq hEt hOm
  have hinj : Function.Injective (shf β L) := by
    intro a b h
    apply hH.anti.injective
    have h' : (L a : ℂ) = (L b : ℂ) := add_left_cancel h
    exact_mod_cast h'
  have hcont : Continuous fun u : ℂ => cpol (shf β M) (u - 1) := by
    unfold cpol
    fun_prop
  have h := ev_starProjection_eigenspace_eq_residue (PiLp 2 (fun _ : Fin (n + 1) => V)) V (n + 1)
    (shf β L) 0 Om (PiLp.projₗ 2 (fun _ : Fin (n + 1) => V) (Fin.last n)) K
    (fun u : ℂ => cpol (shf β M) (u - 1)) (PiLp.single 2 (Fin.last n) v) v l hinj hsym hev hK hcont
    (fun u => (hK' u v).trans (mem_CapSp.1 hv (u - 1)))
  refine Eq.trans h ?_
  congr 1
  simp only [cpol, shf, WigSh.wP]
  push_cast
  congr 1
  · exact Finset.prod_congr rfl fun j _ => by ring
  · exact Finset.prod_congr rfl fun j _ => by ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarProjectionSplitCasimirRaisingLastStatement
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starProjection_splitCasimir_raising_last : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + 0)).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  first | exact @GlobalTheory.starProjection_splitCasimirStd_last | exact GlobalTheory.starProjection_splitCasimirStd_last | (intros; apply GlobalTheory.starProjection_splitCasimirStd_last <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenspaceIrreducibleStandard
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HighestWeightTensorStandard
open Formalism.REAL

namespace GlobalTheory

theorem highestWeight_tensor_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (θ : Fin (n + 1) → ℂ) (lam : ℂ) (y : (PiLp 2 (fun _ : Fin (n + 1) => V))), (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → y ≠ 0 → IsHW Et θ y → Om y = lam • y → ∃ c, y c ≠ 0 ∧ IsHW E (fun a => θ a - if a = c then 1 else 0) (y c) ∧ lam = θ c - 1 - ((c : ℕ) : ℂ) := by
  classical
  intro V _ _ _ n E Et Om θ lam y hEt hOm hy hw hlam
  obtain ⟨h1, h2⟩ := hw
  have hne : (Finset.univ.filter (fun c => y c ≠ 0)).Nonempty := by
    by_contra h
    apply hy
    ext c
    by_contra hc
    exact h ⟨c, by simpa using hc⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image _ id hne
  have hc0 : y c ≠ 0 := by simpa using hc
  have hz : ∀ d, c < d → y d = 0 := by
    intro d hd
    by_contra h
    exact absurd (hmax d (by simpa using h)) (not_le.mpr hd)
  have hup : ∀ a b, a < b → ∀ e, E a b (y e) = - if e = a then y b else 0 := by
    intro a b hab e
    have h := hEt a b y e
    have h0 : Et a b y = 0 := h2 a b hab
    rw [h0] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hdiag : ∀ a, E a a (y c) = (θ a - if a = c then 1 else 0) • y c := by
    intro a
    have h := hEt a a y c
    have h0 : Et a a y = θ a • y := h1 a
    rw [h0] at h
    have h' : E a a (y c) = θ a • y c - if c = a then y a else 0 := by
      rw [eq_sub_iff_add_eq, ← h]; rfl
    rw [h']
    by_cases hca : c = a
    · subst hca; simp [sub_smul]
    · simp [hca, Ne.symm hca]
  have hraise : ∀ a b, a < b → E a b (y c) = 0 := by
    intro a b hab
    rw [hup a b hab c]
    by_cases hca : c = a
    · subst hca; simp [hz b hab]
    · simp [hca]
  refine ⟨c, hc0, ⟨hdiag, hraise⟩, ?_⟩
  have hterm : ∀ d, E d c (y d) =
      ((if d = c then θ c - 1 else 0) - if d < c then 1 else 0 : ℂ) • y c := by
    intro d
    rcases lt_trichotomy d c with h | h | h
    · rw [hup d c h d]; simp [h, h.ne]
    · subst h; rw [hdiag]; simp
    · simp [hz d h, h.ne', not_lt.mpr h.le]
  have hsum : lam • y c = (θ c - 1 - ((c : ℕ) : ℂ)) • y c := by
    have h := hOm y c
    rw [hlam] at h
    have h' : lam • y c = ∑ d, E d c (y d) := h
    rw [h', Finset.sum_congr rfl (fun d _ => hterm d), ← Finset.sum_smul,
      Finset.sum_sub_distrib]
    congr 2
    · simp
    · rw [Finset.sum_boole]
      have : Finset.univ.filter (fun d => d < c) = Finset.Iio c := by ext d; simp
      rw [this, Fin.card_Iio]
  exact smul_left_injective ℂ hc0 hsum

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenspaceIrreducibleStandard
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P

namespace GlobalTheory

theorem splitCasimir_eigenspace_irreducible_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → Stab Et (Module.End.eigenspace Om (β + L l + 0)) ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ Module.End.eigenspace Om (β + L l + 0) → Stab Et S' → S' = ⊥ ∨ S' = Module.End.eigenspace Om (β + L l + 0)) ∧ Module.End.eigenspace Om (β + L l + 0) ≤ CapSp Et (shf β (Function.update L l (L l + 1))) := by
  classical
  intro V _ _ _ n E Et Om β L l hyp hadj hEt hOm
  obtain ⟨hgl, hadjt, -, hcomm⟩ :=
    tensorStd_rel_adjoint_splitCasimir V n E Et Om hyp.gl hadj hEt hOm
  set S := Module.End.eigenspace Om (β + L l + 0) with hS
  have hmemS : ∀ y, y ∈ S ↔ Om y = (β + L l + 0) • y := fun y => Module.End.mem_eigenspace_iff
  have hstab : Stab Et S := by
    intro a b v hv
    rw [hmemS] at hv ⊢
    have h := LinearMap.congr_fun (hcomm a b) v
    simp only [Module.End.mul_apply] at h
    rw [h, hv, map_smul]
  have hcapV : ∀ v, v ∈ CapSp E (shf β L) := fun v => mem_CapSp.2 fun w => hyp.cap w v
  have hsdec : SDec (shf β L) := by
    intro a b hab
    have h := hyp.anti hab
    refine ⟨(L a - L b - 1).toNat, ?_⟩
    have h2 : (((L a - L b - 1).toNat : ℕ) : ℤ) = L a - L b - 1 := Int.toNat_of_nonneg (by omega)
    have h3 : (((L a - L b - 1).toNat : ℕ) : ℂ) = (L a : ℂ) - L b - 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ℂ) h2
    rw [h3]
    simp only [shf]
    ring
  have hwtV : ∀ ν v, v ≠ 0 → IsHW E ν v → ∀ j, ν j = β + L j + ((j : ℕ) : ℂ) := by
    intro ν v hv hw j
    have hne : CapSp E (shf β L) ≠ ⊥ := fun h =>
      hv ((Submodule.mem_bot ℂ).1 (h ▸ hcapV v))
    exact (capelli_singular V (n + 1) E _ hyp.gl hne).2 hsdec ν v (hcapV v) hv hw j
  have hkey : ∀ θ y, y ∈ S → y ≠ 0 → IsHW Et θ y →
      y l ≠ 0 ∧ IsHW E (fun j => β + L j + ((j : ℕ) : ℂ)) (y l) ∧
        θ = fun j => β + L j + ((j : ℕ) : ℂ) + if j = l then 1 else 0 := by
    intro θ y hy hy0 hw
    obtain ⟨c, hc0, hcw, hlam⟩ := highestWeight_tensor_standard V n E Et Om θ _ y hEt hOm hy0 hw
      ((hmemS y).1 hy)
    have hν := hwtV _ _ hc0 hcw
    have hcl : c = l := by
      have h1 := hν c
      simp only [if_true] at h1
      have h2 : (L c : ℂ) = L l := by linear_combination -h1 - hlam
      exact hyp.anti.injective (by exact_mod_cast h2)
    subst hcl
    refine ⟨hc0, ?_, ?_⟩
    · rw [← funext hν]; exact hcw
    · funext j
      rw [← hν j]; ring
  have hsub : ∀ ν v, IsHW E ν v → IsHW (subA E) (fun j => ν j.castSucc) v := by
    intro ν v hw
    exact ⟨fun a => hw.1 _, fun a b hab => hw.2 _ _ (by simpa using hab)⟩
  have hprop : ∀ θ y θ' y', y ∈ S → y ≠ 0 → IsHW Et θ y → y' ∈ S → y' ≠ 0 → IsHW Et θ' y' →
      ∃ t : ℂ, y' = t • y := by
    intro θ y θ' y' hy hy0 hw hy' hy0' hw'
    obtain ⟨h1, h2, h3⟩ := hkey θ y hy hy0 hw
    obtain ⟨-, h2', h3'⟩ := hkey θ' y' hy' hy0' hw'
    have hθ : θ' = θ := h3'.trans h3.symm
    rw [hθ] at hw'
    obtain ⟨t, ht⟩ := multiplicity_one V n E _ (y l) (y' l) hyp.gl hyp.irr (hsub _ _ h2)
      (hsub _ _ h2') h1
    refine ⟨t, ?_⟩
    by_contra hne
    have hz0 : y' - t • y ≠ 0 := sub_ne_zero.2 hne
    have hzw : IsHW Et θ (y' - t • y) := by
      refine ⟨fun a => ?_, fun a b hab => ?_⟩
      · rw [map_sub, map_smul, hw.1, hw'.1, smul_sub, smul_comm]
      · rw [map_sub, map_smul, hw.2 a b hab, hw'.2 a b hab]; simp
    apply (hkey θ _ (S.sub_mem hy' (S.smul_mem t hy)) hz0 hzw).1
    simp [ht]
  have hirr : ∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' →
      S' = ⊥ ∨ S' = S := by
    intro S' hle hst
    by_contra hcon
    push_neg at hcon
    obtain ⟨hb, hne⟩ := hcon
    have hst2 : Stab Et (S'ᗮ ⊓ S) := by
      intro a b v hv
      refine ⟨?_, hstab a b v hv.2⟩
      have hv1 : v ∈ S'ᗮ := hv.1
      change Et a b v ∈ S'ᗮ
      rw [Submodule.mem_orthogonal] at hv1 ⊢
      intro u hu
      rw [← hadjt]
      exact hv1 _ (hst b a u hu)
    have hb2 : S'ᗮ ⊓ S ≠ ⊥ := by
      intro h
      have h2 := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle
      rw [h, sup_bot_eq] at h2
      exact hne h2
    obtain ⟨θ, y, hy, hy0, hw, -⟩ := exists_singular_maximal_vector _ _ Et hgl S' hst hb
    obtain ⟨θ', y', hy', hy0', hw', -⟩ := exists_singular_maximal_vector _ _ Et hgl _ hst2 hb2
    obtain ⟨t, ht⟩ := hprop θ y θ' y' (hle hy) hy0 hw hy'.2 hy0' hw'
    have hmem : y' ∈ S' := ht ▸ S'.smul_mem t hy
    have hy1 : y' ∈ S'ᗮ := hy'.1
    exact hy0' (inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hy1 y' hmem))
  refine ⟨hstab, hirr, ?_⟩
  by_cases hb : S = ⊥
  · rw [hb]; exact bot_le
  obtain ⟨θ, y, hy, hy0, hw, -⟩ := exists_singular_maximal_vector _ _ Et hgl S hstab hb
  obtain ⟨-, -, h3⟩ := hkey θ y hy hy0 hw
  have hyc : y ∈ CapSp Et (shf β (Function.update L l (L l + 1))) := by
    rw [mem_CapSp]
    intro w
    rw [qDetHW _ _ Et θ y hgl hw w, h3]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hk : k = l
    · subst hk; simp; ring
    · simp [hk]
  have hst3 : Stab Et (CapSp Et (shf β (Function.update L l (L l + 1))) ⊓ S) := fun a b v hv =>
    ⟨(capelli_stabilizer _ _ Et _ hgl).1 a b v hv.1, hstab a b v hv.2⟩
  rcases hirr _ inf_le_right hst3 with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (⟨hyc, hy⟩ : y ∈ _ ⊓ S))) hy0
  · exact h ▸ inf_le_left

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenspaceIrreducibleStandardStatement
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitCasimir_eigenspace_irreducible_standard_alt : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → Stab Et (Module.End.eigenspace Om (β + L l + 0)) ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ Module.End.eigenspace Om (β + L l + 0) → Stab Et S' → S' = ⊥ ∨ S' = Module.End.eigenspace Om (β + L l + 0)) ∧ Module.End.eigenspace Om (β + L l + 0) ≤ CapSp Et (shf β (Function.update L l (L l + 1))) := by
  first | exact @GlobalTheory.splitCasimir_eigenspace_irreducible_standard | exact GlobalTheory.splitCasimir_eigenspace_irreducible_standard | (intros; apply GlobalTheory.splitCasimir_eigenspace_irreducible_standard <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriRaisingSubmoduleGlSucc
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory.WigSh

theorem exists_splitCasimir_std (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) :
    ∃ Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), ∀ y b, Om y b = ∑ c, E c b (y c) := by
  refine ⟨(WithLp.linearEquiv 2 ℂ (Fin (n + 1) → V)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun b => ∑ c, E c b ∘ₗ LinearMap.proj c) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (n + 1) → V)).toLinearMap, ?_⟩
  intro y b
  simp [LinearMap.sum_apply]

theorem pieri_step_raise : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ j, L j ≠ L l + 1) → ∃ S : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), Stab Et S ∧ S ≠ ⊥ ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' → S' = ⊥ ∨ S' = S) ∧ S ≤ CapSp Et (shf β (Function.update L l (L l + 1))) ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → S.starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  intro V _ _ _ n E Et β L l hyp hadj hEt hL
  obtain ⟨Om, hOm⟩ := exists_splitCasimir_std V n E
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.splitCasimir_eigenspace_irreducible_standard_alt V n E Et Om β L l hyp hadj hEt hOm
  have h4 := GlobalTheory.T.starProjection_splitCasimir_raising_last V n E Et Om β L l hyp hadj hEt hOm
  refine ⟨_, h1, ?_, h2, h3, h4⟩
  intro hbot
  have hbox : Box L (fun j : Fin n => L j.castSucc) := fun j =>
    ⟨hyp.anti (Fin.castSucc_lt_succ), le_rfl⟩
  have hne := (Formalism.FourierDecayAlt.P.branching_decomposition V n E β L hyp).1 _ hbox
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h5 := h4 _ v hv
  have hw := (wigner_extreme_ne_zero n L l hyp.anti).1 hL
  have hmem := Submodule.starProjection_apply_mem (Module.End.eigenspace Om (β + L l + 0))
    (PiLp.single 2 (Fin.last n) v)
  have hz : (Module.End.eigenspace Om (β + L l + 0)).starProjection
      (PiLp.single 2 (Fin.last n) v) = 0 := (Submodule.eq_bot_iff _).1 hbot _ hmem
  rw [hz] at h5
  have h6 : ((wP L (fun j : Fin n => L j.castSucc) l : ℝ) : ℂ) • v = 0 := by
    rw [← h5]; rfl
  rcases smul_eq_zero.1 h6 with h | h
  · exact hw (by exact_mod_cast h)
  · exact hv0 h

end GlobalTheory.WigSh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriRaisingSubmoduleGlSuccStatement
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pieri_raising_submodule_glSucc : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ j, L j ≠ L l + 1) → ∃ S : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), Stab Et S ∧ S ≠ ⊥ ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' → S' = ⊥ ∨ S' = S) ∧ S ≤ CapSp Et (shf β (Function.update L l (L l + 1))) ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → S.starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  first | exact @GlobalTheory.WigSh.pieri_step_raise | exact GlobalTheory.WigSh.pieri_step_raise | (intros; apply GlobalTheory.WigSh.pieri_step_raise <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerStepRaisingUnitaryComplement
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem adjoint_eval_subspace {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {k : ℕ} (S : Submodule ℂ (PiLp 2 (fun _ : Fin k => V))) (c : Fin k) (v : V) :
    ContinuousLinearMap.adjoint
        ((PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin k => V) c).comp S.subtypeL) v
      = S.orthogonalProjectionOnto (PiLp.single 2 c v) := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right, Submodule.inner_orthogonalProjection_eq_of_mem_left,
    PiLp.inner_apply, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [PiLp.single_eq_of_ne, hb]
  · simp

theorem wigner_step_raise : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, L j ≠ L l + 1) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + 1)) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π 1 A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((GlobalTheory.WigSh.wP L M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l hz hT hπ hL hu hB hl
  obtain ⟨hH, hadj⟩ := GlobalTheory.TypeGlModule.hyp_and_adj V n r z π u β L B hz hT hπ hL hu hB
  have hrep : IsRepW (n + 1) r z π := ⟨hπ.2.1, hπ.2.2.1⟩
  obtain ⟨πt, ht1, ht2, ht3⟩ :=
    GlobalTheory.exists_tensor_standard_rep V (n + 1) r z π B hz hT hrep hπ.2.2.2.1 hB
  have hE := GlobalTheory.TensorStd.EB_tensor_std V (n + 1) r z π B πt hz hT hrep ht1 hB ht3
  obtain ⟨S, hS1, hS2, hS3, hS4, hS5⟩ := GlobalTheory.T.pieri_raising_submodule_glSucc V n (EB π B) (EB πt B) β L l hH hadj hE hl
  have hq : ∀ (w : ℂ), ∀ y ∈ S, qdet (EB πt B) w y = (∏ i ∈ Finset.Icc 1 (n + 1),
      (w - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 +
        ((Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + 1) i : ℝ) : ℂ))) • y := by
    intro w y hy
    have h1 := hS4 hy
    unfold CapSp at h1
    rw [Submodule.mem_iInf] at h1
    have h2 := h1 w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply] at h2
    rw [h2, Formalism.FourierDecayAlt.P.FrameExtension.prod_Icc_fin]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl fun j _ => ?_
    have hj := hu j
    by_cases hjl : j = l
    · subst hjl
      simp only [Function.update_self]
      push_cast at hj ⊢
      linear_combination -hj
    · have hne : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hjl (Fin.ext (by omega))
      rw [Function.update_of_ne hjl, Function.update_of_ne hne]
      linear_combination -hj
  obtain ⟨πS, hπS, hπS2⟩ := GlobalTheory.isType_of_irreducible_stable _ (n + 1) r z πt B S _ hz hT ht1 ht2 hB
    hS1 hS2 hS3 hq
  let a : Fin (n + 1) → (S →L[ℂ] V) := fun c =>
    (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin (n + 1) => V) c).comp S.subtypeL
  have ha : ∀ c (y : S), a c y = (y : PiLp 2 (fun _ : Fin (n + 1) => V)) c := fun c y => rfl
  obtain ⟨hW, hA⟩ := GlobalTheory.WigSh.ContrPlus.contraction_wigMap V (n + 1) r z π B S πS a hz hT hB
    (by
      intro y
      simp only [ha]
      rw [← PiLp.norm_sq_eq_of_L2]
      rfl)
    (by
      intro h hh y c
      simp only [ha]
      rw [hπS2 h hh y, ht3 h hh])
  refine ⟨S, inferInstance, inferInstance, inferInstance, πS, _, hπS, hW, ?_⟩
  intro M v hv
  simp only [hA]
  rw [ha, ← hS5 M v hv]
  simp only [a]
  rw [adjoint_eval_subspace]
  rfl

end GlobalTheory.WigSh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerStepRaisingUnitaryComplementStatement
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wigner_step_raising_unitary_complement : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, L j ≠ L l + 1) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + 1)) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π 1 A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((GlobalTheory.WigSh.wP L M l : ℝ) : ℂ) • v := by
  first | exact @GlobalTheory.WigSh.wigner_step_raise | exact GlobalTheory.WigSh.wigner_step_raise | (intros; apply GlobalTheory.WigSh.wigner_step_raise <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsWignerContractionChainRaising
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem chain_raise : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)) (n₀ : ℕ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, j < l → L l + (n₀ : ℤ) < L j) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π n₀ A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wP (Function.update L l (L l + (j : ℤ))) M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l n₀ hz hT hπ hL hu hB
  induction n₀ with
  | zero =>
    intro _
    refine ⟨V, inferInstance, inferInstance, inferInstance, π, fun _ => ContinuousLinearMap.id ℂ V, ?_, ?_, ?_⟩
    · simpa using hπ
    · exact wigMap_zero_of_contraction V V (n + 1) r z π π _ (fun v => le_rfl) (fun h _ v => rfl)
    · intro M v _
      simp [ContinuousLinearMap.adjoint_id]
  | succ m ih =>
    intro hreg
    obtain ⟨V₂, i1, i2, i3, π₂, A, hπ₂, hA, hAA⟩ := ih (fun j hj => by
      have := hreg j hj
      push_cast at this
      omega)
    have hm0 : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
    have hL' : StrictAnti (Function.update L l (L l + (m : ℤ))) := by
      intro a b hab
      have h1 := hL hab
      by_cases ha : a = l
      · have hb : b ≠ l := fun hb => hab.ne (ha.trans hb.symm)
        subst ha
        rw [Function.update_self, Function.update_of_ne hb]
        omega
      · by_cases hb : b = l
        · subst hb
          rw [Function.update_self, Function.update_of_ne ha]
          have := hreg a hab
          push_cast at this
          omega
        · rw [Function.update_of_ne ha, Function.update_of_ne hb]
          exact h1
    have hu' : ∀ j : Fin (n + 1),
        ((Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + (m : ℝ)) ((j : ℕ) + 1) : ℝ) : ℂ) -
          ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + ((Function.update L l (L l + (m : ℤ)) j : ℤ) : ℂ) := by
      intro j
      by_cases hj : j = l
      · subst hj
        rw [Function.update_self, Function.update_self]
        have := hu j
        push_cast at this ⊢
        linear_combination this
      · have hj' : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hj (Fin.ext (by omega))
        rw [Function.update_of_ne hj, Function.update_of_ne hj']
        exact hu j
    have hreg' : ∀ j, Function.update L l (L l + (m : ℤ)) j ≠ Function.update L l (L l + (m : ℤ)) l + 1 := by
      intro j
      rw [Function.update_self]
      rcases lt_trichotomy j l with hj | hj | hj
      · rw [Function.update_of_ne hj.ne]
        have := hreg j hj
        push_cast at this
        omega
      · subst hj
        rw [Function.update_self]
        omega
      · rw [Function.update_of_ne hj.ne']
        have := hL hj
        omega
    obtain ⟨V₃, j1, j2, j3, π₃, a, hπ₃, ha, haa⟩ :=
      GlobalTheory.T.wigner_step_raising_unitary_complement V₂ n r z π₂ _ β _ B l hz hT hπ₂ hL' hu' hB hreg'
    refine ⟨V₃, j1, j2, j3, π₃, fun ω => (A ω).comp (a ω), ?_,
      wigMap_comp V V₂ V₃ (n + 1) r z π π₂ π₃ m 1 A a hA ha, ?_⟩
    · rw [Function.update_self, Function.update_idem] at hπ₃
      have e : u ((l : ℕ) + 1) + ((m + 1 : ℕ) : ℝ) = u ((l : ℕ) + 1) + (m : ℝ) + 1 := by
        push_cast
        ring
      rw [e]
      exact hπ₃
    · intro M v hv
      have hc := GlobalTheory.adjoint_mem_CapSp_subA V V₂ n r z π π₂ B (A (B (Fin.last n))) (shf β M)
        ⟨hπ.2.1, hπ.2.2.1⟩ ⟨hπ₂.2.1, hπ₂.2.2.1⟩ hπ.2.2.2.1 hπ₂.2.2.2.1 hB
        (fun h hh he => by
          have := hA.2.1 h hh (B (Fin.last n))
          rwa [he] at this) v hv
      have h2 := haa M _ hc
      show A (B (Fin.last n)) (a (B (Fin.last n))
        (ContinuousLinearMap.adjoint ((A (B (Fin.last n))).comp (a (B (Fin.last n)))) v)) = _
      rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply, h2, map_smul, hAA M v hv,
        smul_smul, Finset.prod_range_succ]
      push_cast
      rw [mul_comm]

end GlobalTheory.WigSh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsWignerContractionChainRaisingStatement
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wignerContraction_chain_raising : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)) (n₀ : ℕ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, j < l → L l + (n₀ : ℤ) < L j) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π n₀ A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wP (Function.update L l (L l + (j : ℤ))) M l : ℝ) : ℂ) • v := by
  first | exact @GlobalTheory.WigSh.chain_raise | exact GlobalTheory.WigSh.chain_raise | (intros; apply GlobalTheory.WigSh.chain_raise <;> assumption)
end
