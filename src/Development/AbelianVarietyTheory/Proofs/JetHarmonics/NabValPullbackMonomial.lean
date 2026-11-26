module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.NabTrans
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NabValPullbackMonomial
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.PullbackColumn

variable {k : Type} [CommRing k] {d : ℕ}

theorem expS_pow [Algebra ℚ k] {n : ℕ} (g : PS k n d) (hg : constantCoeff g = 0) (m : ℕ) :
    FB.expS k g ^ m = FB.expS k ((m : k) • g) := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, zero_smul, nt_expS_zero]
  | succ m ih =>
    rw [pow_succ, ih, Nat.cast_succ, add_smul, one_smul,
      gt_expS_add _ _ (by rw [nt_const_smul, hg, mul_zero]) hg]

theorem dpolyOf_monomial_one (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (mo : ι →₀ ℕ) (g : PS k 1 d) :
    DpolyOf F u (MvPolynomial.monomial mo (1 : k)) g = DmonOf F u mo g := by
  classical
  have e : DpolyOf F u (MvPolynomial.monomial mo (1 : k)) g =
      ∑ m ∈ ({mo} : Finset (ι →₀ ℕ)), C ((MvPolynomial.monomial mo (1 : k)).coeff m) * DmonOf F u m g := by
    unfold DpolyOf
    refine Finset.sum_subset MvPolynomial.support_monomial_subset fun x _ hx => ?_
    rw [MvPolynomial.notMem_support_iff.1 hx, map_zero, zero_mul]
  rw [e, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl, map_one, one_mul]

end GlobalTheory.PullbackColumn

namespace GlobalTheory

open PullbackColumn

theorem nabVal_pullback_monomial : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w0 a : O) (N m : ℕ) (w : PS R 1 d), FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) → ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → k) (α : ι → k), (∀ l, (dAct k B a).mulVec (u l) = α l • u l) → ∀ (f : PS k 1 d) (mo : ι →₀ ℕ), B.nabVal k h w0 (N * m) (ev (n := 1) ![B.actK k a] f * FB.toK k w ^ m) u (MvPolynomial.monomial mo 1) = (∏ l, α l ^ mo l) * B.nabVal k h w0 m f u (MvPolynomial.monomial mo 1) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 a N m w hw ι _ u α hα f mo
  have hA : ∀ b : O, GP (B.actK k b) := fun b => QuadDeriv.constantCoeff_mapP_eq_zero _ _ (B.A.const b)
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have cL : constantCoeff (B.hL k h w0) = 0 :=
    gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (hA w0) (gp_pt 0))) h hh0
  have cA : constantCoeff (ev (n := 1) ![B.actK k a] (B.hL k h w0)) = 0 :=
    gt_const_ev _ (single_point_zero_constant (hA a)) _ cL
  have cD : constantCoeff (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) = 0 := by
    rw [map_sub, cA, nt_const_smul, cL, mul_zero, sub_zero]
  have hG : ev (n := 1) ![B.actK k a] f * FB.toK k w ^ m * FB.expS k (((N * m : ℕ) : k) • B.hL k h w0) =
      ev (n := 1) ![B.actK k a] (f * FB.expS k ((m : k) • B.hL k h w0)) := by
    rw [hw, expS_pow _ cD, mul_assoc, ← gt_expS_add _ _ (by rw [nt_const_smul, cD, mul_zero])
      (by rw [nt_const_smul, cL, mul_zero]), gt_ev_mul _ (single_point_zero_constant (hA a)),
      gt_ev_expS _ (single_point_zero_constant (hA a)) _ (by rw [nt_const_smul, cL, mul_zero]), nt_ev_smul _ (single_point_zero_constant (hA a)),
      smul_sub, smul_smul, Nat.cast_mul, mul_comm (N : k) (m : k), sub_add_cancel]
  unfold FB.nabVal
  rw [hG, dpolyOf_monomial_one, dpolyOf_monomial_one]
  exact (invariantDeriv_along_endo R d O k B a).2 ι u α hα mo _

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundProjectionDualTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundProjectionDualTensor
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem kUnit_of_isUnitary_proj {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (h : IsUnitary ε E) : KUnit ε E := by
  intro a b hab u v
  have := h a b u v
  simpa [Formalism.REAL.sgn, hab] using this

theorem casKLe_proj_single : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (c : ℝ) (w : M), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → 0 ≤ c → CasKLe ε E c w → ∀ s d, CasKLe ε (F s) (c + Real.sqrt n) (pr s (Pi.single d w)) := by
  intro M _ _ n ε E N _ _ F io pr c w hE hF hT hc hw s d
  have key := GlobalTheory.T.compactCasimirLe_tensorOperator_raise M n ε E (N s) (Fin n) (F s)
    (fun j => (pr s) ∘ₗ (LinearMap.single ℂ (fun _ : Fin n => M) j))
    (fun a b => Matrix.of fun i j => if i = b ∧ j = a then (-1 : ℂ) else 0) c (Real.sqrt n)
    (kUnit_of_isUnitary_proj hE) (kUnit_of_isUnitary_proj (hF s)) hc (Real.sqrt_nonneg _) ?_ ?_ ?_ w hw d
  · simpa using key
  · intro a b _
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases h : i = a ∧ j = b
    · simp [h.1, h.2]
    · have h' : ¬ (j = b ∧ i = a) := fun h2 => h ⟨h2.2, h2.1⟩
      simp [h, h']
  · intro x
    rw [Real.sq_sqrt (Nat.cast_nonneg n), Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h1 : ∀ b : Fin n, ∑ i, ‖∑ j, (Matrix.of fun i j => if i = b ∧ j = a then (-1 : ℂ) else 0) i j • x j‖ ^ 2
        = ‖x a‖ ^ 2 := by
      intro b
      rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single a]
        · simp
        · intro j _ hj; simp [hj]
        · simp
      · intro i _ hi; simp [hi]
      · simp
    calc _ ≤ ∑ _b : Fin n, ‖x a‖ ^ 2 := by
          refine Finset.sum_le_sum fun b _ => ?_
          split_ifs
          · exact (h1 b).le
          · positivity
      _ = _ := by simp
  · intro a b _ j v
    simp only [LinearMap.comp_apply, LinearMap.single_apply, Matrix.of_apply]
    rw [← hT.pr_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum, ← map_add (f := _)]
    congr 1
    funext i
    rw [Finset.sum_eq_single b]
    · simp only [dualTens, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
      by_cases h1 : i = j <;> by_cases h2 : i = b <;> by_cases h3 : j = a <;>
        simp_all [sub_eq_add_neg, eq_comm]
    · intro k _ hk; simp [hk]
    · simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundProjectionDualTensorStatement
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactCasimirBound_projection_dualTensor : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (c : ℝ) (w : M), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → 0 ≤ c → CasKLe ε E c w → ∀ s d, CasKLe ε (F s) (c + Real.sqrt n) (pr s (Pi.single d w)) := by
  first | exact @GlobalTheory.casKLe_proj_single | exact GlobalTheory.casKLe_proj_single | (intros; apply GlobalTheory.casKLe_proj_single <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevEAddTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundElementaryApply
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory.CasKAdjoint

def adMat {n : ℕ} (a b : Fin n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ := fun i j =>
  (if i.1 = a ∧ j = (b, i.2) then 1 else 0) - (if i.2 = b ∧ j = (i.1, a) then 1 else 0)

end GlobalTheory.CasKAdjoint
end

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

private lemma adMat_conjTranspose_eq_adMat_swap {n : ℕ} (a b : Fin n) :
    (_root_.GlobalTheory.CasKAdjoint.adMat a b).conjTranspose = _root_.GlobalTheory.CasKAdjoint.adMat b a := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.conjTranspose_apply, _root_.GlobalTheory.CasKAdjoint.adMat, Prod.mk.injEq, star_sub, apply_ite star,
    star_one, star_zero]
  congr 1
  · exact if_congr ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, h₃.symm⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, h₃.symm⟩⟩ rfl rfl
  · exact if_congr ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₃, h₂.symm, h₁⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₃, h₂.symm, h₁⟩⟩ rfl rfl

private lemma sum_adMat_apply_first_index_smul {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (a b : Fin n) (x : Fin n × Fin n → M) (i : Fin n × Fin n) :
    ∑ j, _root_.GlobalTheory.CasKAdjoint.adMat a b i j • x j =
      (if i.1 = a then x (b, i.2) else 0) - (if i.2 = b then x (i.1, a) else 0) := by
  obtain ⟨i₁, i₂⟩ := i
  simp only [_root_.GlobalTheory.CasKAdjoint.adMat, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
    Fintype.sum_prod_type, Prod.mk.injEq]
  simp [ite_and]

private lemma norm_ite_zero_sq {M : Type} [NormedAddCommGroup M] (p : Prop) [Decidable p] (y : M) :
    ‖if p then y else 0‖ ^ 2 = if p then ‖y‖ ^ 2 else 0 := by
  split_ifs <;> simp

private lemma sum_norm_sq_adMat_mulVec_le {M : Type} [NormedAddCommGroup M]
    [InnerProductSpace ℂ M] {n : ℕ} (a b : Fin n) (x : Fin n × Fin n → M) :
    ∑ i, ‖∑ j, _root_.GlobalTheory.CasKAdjoint.adMat a b i j • x j‖ ^ 2 ≤
      2 * ∑ k, ‖x (b, k)‖ ^ 2 + 2 * ∑ k, ‖x (k, a)‖ ^ 2 := by
  simp_rw [sum_adMat_apply_first_index_smul]
  calc ∑ i : Fin n × Fin n, ‖(if i.1 = a then x (b, i.2) else 0) - (if i.2 = b then x (i.1, a) else 0)‖ ^ 2
      ≤ ∑ i : Fin n × Fin n, (2 * ‖if i.1 = a then x (b, i.2) else 0‖ ^ 2
          + 2 * ‖if i.2 = b then x (i.1, a) else 0‖ ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := norm_sub_le (if i.1 = a then x (b, i.2) else 0) (if i.2 = b then x (i.1, a) else 0)
        nlinarith [norm_nonneg ((if i.1 = a then x (b, i.2) else 0) - (if i.2 = b then x (i.1, a) else 0)),
          sq_nonneg (‖if i.1 = a then x (b, i.2) else 0‖ - ‖if i.2 = b then x (i.1, a) else 0‖)]
    _ = 2 * ∑ k, ‖x (b, k)‖ ^ 2 + 2 * ∑ k, ‖x (k, a)‖ ^ 2 := by
        simp only [norm_ite_zero_sq, Finset.sum_add_distrib, ← Finset.mul_sum, Fintype.sum_prod_type]
        rw [Finset.sum_comm (f := fun x_1 y => if y = b then ‖x (x_1, a)‖ ^ 2 else 0)]
        simp

private lemma sum_eq_sign_norm_sq_adMat_mulVec_le {M : Type} [NormedAddCommGroup M]
    [InnerProductSpace ℂ M] {n : ℕ} (ε : Fin n → Bool) (x : Fin n × Fin n → M) :
    (∑ a, ∑ b, if ε a = ε b then ∑ i, ‖∑ j, _root_.GlobalTheory.CasKAdjoint.adMat a b i j • x j‖ ^ 2 else 0) ≤
      (8 * (n : ℝ)) ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
  have hS : ∑ j, ‖x j‖ ^ 2 = ∑ b, ∑ k, ‖x (b, k)‖ ^ 2 := Fintype.sum_prod_type _
  have hS' : ∑ j, ‖x j‖ ^ 2 = ∑ a, ∑ k, ‖x (k, a)‖ ^ 2 := by
    rw [hS, Finset.sum_comm]
  have h0 : 0 ≤ ∑ j, ‖x j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc (∑ a, ∑ b, if ε a = ε b then ∑ i, ‖∑ j, _root_.GlobalTheory.CasKAdjoint.adMat a b i j • x j‖ ^ 2 else 0)
      ≤ ∑ a : Fin n, ∑ b : Fin n, (2 * ∑ k, ‖x (b, k)‖ ^ 2 + 2 * ∑ k, ‖x (k, a)‖ ^ 2) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        split_ifs
        · exact sum_norm_sq_adMat_mulVec_le a b x
        · positivity
    _ = 4 * n * ∑ j, ‖x j‖ ^ 2 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        rw [← hS, ← hS']
        ring
    _ ≤ (8 * (n : ℝ)) ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · simp [hn]
        · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 4 * n) h0)
            (by linarith : (0:ℝ) ≤ 16 * n - 1)]

private lemma sum_adMat_apply_second_index_smul {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (a b : Fin n) (y : Fin n × Fin n → M) (j : Fin n × Fin n) :
    ∑ i, _root_.GlobalTheory.CasKAdjoint.adMat a b i j • y i =
      (if j.1 = b then y (a, j.2) else 0) - (if j.2 = a then y (j.1, b) else 0) := by
  obtain ⟨j₁, j₂⟩ := j
  simp only [_root_.GlobalTheory.CasKAdjoint.adMat, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
    Fintype.sum_prod_type, Prod.mk.injEq]
  simp [ite_and, eq_comm]

private lemma sum_abs_shifted_weight_sub_le_add_two {n : ℕ} (ω μ : Fin n → ℝ) (a b : Fin n) :
    ∑ c, |ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0) - μ c| ≤ ∑ c, |ω c - μ c| + 2 := by
  calc ∑ c, |ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0) - μ c|
      ≤ ∑ c, (|ω c - μ c| + ((if c = a then 1 else 0) + (if c = b then 1 else 0))) := by
        refine Finset.sum_le_sum fun c _ => ?_
        have h1 : (0:ℝ) ≤ if c = a then 1 else 0 := by split_ifs <;> norm_num
        have h2 : (0:ℝ) ≤ if c = b then 1 else 0 := by split_ifs <;> norm_num
        rw [show ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0) - μ c
          = (ω c - μ c) + ((if c = a then 1 else 0) - (if c = b then 1 else 0)) by ring]
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [abs_le]; constructor <;> linarith
    _ = ∑ c, |ω c - μ c| + 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp; norm_num

private lemma isWeight_shift_of_glRel {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    {E : Fin n → Fin n → Module.End ℂ M} (hG : _root_.Formalism.REAL.GlRel E) {ω : Fin n → ℝ} {x : M} (hx : _root_.Formalism.REAL.IsWeight E ω x)
    (a b : Fin n) :
    _root_.Formalism.REAL.IsWeight E (fun c => ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) (E a b x) := by
  intro c
  have h := LinearMap.congr_fun (hG c c a b) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul, ite_apply, LinearMap.zero_apply,
    @eq_comm _ b c] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases ha : c = a <;> by_cases hb : c = b
  · subst ha; subst hb; simp
  · subst ha; simp [hb, add_smul]; abel
  · subst hb; simp [ha, sub_smul]; abel
  · simp [ha, hb]

theorem _root_.GlobalTheory.lev_E_add_two : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (j : ℕ) (w : M), _root_.Formalism.REAL.GlRel E → _root_.Formalism.REAL.IsUnitary ε E → _root_.BranchingSupport.Lev ε E μ j w → ∀ a b, _root_.BranchingSupport.Lev ε E μ (j + 2) (E a b w) := by
  intro M _ _ n ε E μ j w hG hU hw a b
  unfold _root_.BranchingSupport.Lev _root_.BranchingSupport.WtNear at hw ⊢
  obtain ⟨hC, hS⟩ := hw
  refine ⟨?_, ?_⟩
  · have hK := _root_.Formalism.REAL.isUnitary_kUnit ε E hU
    have h := _root_.GlobalTheory.TensOp.casKLe_tensor_operator M n ε E M (Fin n × Fin n) E (fun i => E i.1 i.2)
      _root_.GlobalTheory.CasKAdjoint.adMat _ (8 * n) hK hK (by positivity) (by positivity)
      (fun a b _ => adMat_conjTranspose_eq_adMat_swap a b)
      (sum_eq_sign_norm_sq_adMat_mulVec_le ε)
      (fun a b _ k v => by
        have hs := sum_adMat_apply_second_index_smul a b (fun i => E i.1 i.2 v) k
        simp only at hs ⊢
        rw [hs]
        have h := LinearMap.congr_fun (hG a b k.1 k.2) v
        simp only [LinearMap.sub_apply, Module.End.mul_apply, ite_apply, LinearMap.zero_apply,
          @eq_comm _ b k.1] at h
        rw [sub_eq_iff_eq_add'] at h
        rw [h]
        split_ifs <;> simp)
      w hC (a, b)
    convert h using 1
    push_cast
    ring
  · rw [← Submodule.mem_comap]
    refine Submodule.span_le.2 ?_ hS
    rintro x ⟨ω, hd, hx⟩
    exact Submodule.subset_span ⟨_, (sum_abs_shifted_weight_sub_le_add_two ω _ a b).trans (by push_cast; linarith),
      isWeight_shift_of_glRel hG hx a b⟩

end GlobalTheory
end
