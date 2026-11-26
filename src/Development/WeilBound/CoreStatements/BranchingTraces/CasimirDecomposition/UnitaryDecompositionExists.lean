module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanGapSmall
public import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.BranchingTraces.CasimirDecomposition.ExtensionFixesSmoothVectors
section -- merged from Development.WeilBound.CoreStatements.BranchingTraces.CasimirDecomposition.CasApply
open Matrix Finset
open scoped InnerProductSpace Classical

noncomputable section

namespace PositivityTheory.UnitaryDecomposition.DecA

open CompanionTheory.Zuck BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam)
open PI.ZuckTensor (GapAtLeast)

variable {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem decReg (S : Steps) (Lb : Lib t) (hk : 1 ≤ k) (b : Bool) {μ : Fin (2 * r + k + 1) → ℝ} {U : URep k r} {h : ℝ}
    (hU : U.R.IsDS ε μ) (hg : GapAtLeast ε μ h) (ht : t _ ε + (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) + 1 < h)
    (T : {s // IsHCParam (shift b μ s)} → URep k r) (hT : ∀ s, (T s).R.IsDS ε (shift b μ s.1)) :
    ∃ io pr, IsDec (N := M) IsHom (vr k r b, U) (fun s => one (T s)) io pr := by
  have C := S.homCat k r
  have h1 : (1 : ℝ) ≤ (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hsimp := S.schur S.infChar k r ε _ _ T ((shift_inj b μ).comp Subtype.val_injective) hT
  have adj' : ∀ U U' : URep k r, ∃ e : (M (vr k r (!b), U) →ₗ[ℂ] M (one U')) ≃ₗ[ℂ] (M (one U) →ₗ[ℂ] M (vr k r b, U')),
      ∀ p, IsHom (vr k r (!b), U) (one U') p ↔ IsHom (one U) (vr k r b, U') (e p) := by
    cases b
    · exact S.adj k r true
    · exact S.adj k r false
  have occ : ∀ s, ∃ i, IsHom (one (T s)) (vr k r b, U) i ∧ i ≠ 0 := by
    intro s
    obtain ⟨T', hT', -, hp⟩ := injV S Lb (!b) (hT s) (gap_shift hg b s.1) (by linarith)
    have hs : IsHCParam (shift (!b) (shift b μ s.1) s.1) := by rw [shift_shift]; exact hU.1
    obtain ⟨p, hp, hp0⟩ := hp ⟨s.1, hs⟩
    have hd : (T' ⟨s.1, hs⟩).R.IsDS ε μ := by simpa only [shift_shift] using hT' ⟨s.1, hs⟩
    obtain ⟨f, g, hf, -, hgf, -⟩ := iso_of S Lb hd hU hg (by linarith)
    obtain ⟨e, he⟩ := adj' (T s) U
    refine ⟨e (f ∘ₗ p), (he _).1 (C.comp _ _ _ _ _ hp hf), fun h0 => hp0 ?_⟩
    have h2 : f ∘ₗ p = 0 := e.map_eq_zero_iff.1 h0
    calc p = (g ∘ₗ f) ∘ₗ p := by rw [hgf, LinearMap.id_comp]
      _ = 0 := by rw [LinearMap.comp_assoc, h2, LinearMap.comp_zero]
  refine S.decOfInj _ _ _ C _ _ _ hsimp ?_ (fun s => ?_) occ
  · obtain ⟨T', hT', hi, -⟩ := injV S Lb b hU hg (by linarith)
    intro x hx
    refine hi x fun s p hp => ?_
    obtain ⟨f, g, hf, -, hgf, -⟩ := iso_of S Lb (hT' s) (hT s) (gap_shift hg b s.1) (by linarith)
    have h2 := hx s _ (C.comp _ _ _ _ _ hp hf)
    have h3 := LinearMap.congr_fun hgf (p x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2 h3
    rw [← h3, h2, map_zero]
  · obtain ⟨T', hT', hi, -⟩ := injV S Lb b (hT s) (gap_shift hg b s.1) (by linarith)
    have cB := S.casDS S.infChar k r ε _ (T s) hk (hT s)
    have m1 : AtMostOne (N := M) IsHom (one U) (vr k r (!b), T s) := by
      have := fun hi' ho' => S.multOne k r (!b) (T s) U _ T' _ _ _ (fun F => (cB F).1) (cB (triv k r)).2
        (S.casDS S.infChar k r ε _ U hk hU (triv k r)).2
        (fun u => (S.casDS S.infChar k r ε _ (T' u) hk (hT' u) (triv k r)).2)
        (fun u => cas_ne hU.1.1 b s.1 u.1) hi' (hsimp.2.1 s) ⟨_, _, hU⟩ ho'
      cases b
      · exact this hi (occ s)
      · exact this hi (occ s)
    obtain ⟨e, he⟩ := S.adj k r b U (T s)
    intro f g hf hg'
    obtain ⟨α, β, hab, h0⟩ := m1 _ _ ((he f).1 hf) ((he g).1 hg')
    refine ⟨α, β, hab, e.map_eq_zero_iff.1 ?_⟩
    rw [map_add (f := _), map_smul, map_smul, h0]

def kOp (U : URep k r) : Module.End ℂ (M (vr k r true, U)) :=
  LinearMap.pi fun c => ∑ b, U.dC (Matrix.single c b 1) ∘ₗ LinearMap.proj b

theorem kOp_apply (U : URep k r) (x : M (vr k r true, U)) (c : Fin (2 * r + k + 1)) :
    kOp U x c = ∑ b, U.dC (Matrix.single c b 1) (x b) := by
  simp [kOp, LinearMap.sum_apply]

theorem L_apply (U : URep k r) (a b : Fin (2 * r + k + 1)) (x : M (vr k r true, U)) (c : Fin (2 * r + k + 1)) :
    L (vr k r true, U) (Matrix.single a b 1) x c = U.dC (Matrix.single a b 1) (x c) - if c = b then x a else 0 := by
  have h : (vr k r true, U).1.dC (Matrix.single a b 1) = -(Matrix.single a b (1 : ℂ))ᵀ := (GlobalTheory.T.StandardDifferential k r _).2
  simp only [L, h, LinearMap.add_apply, Pi.add_apply, dOp, mAct, LinearMap.compLeft_apply, Function.comp_apply,
    LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, sub_eq_add_neg]
  congr 1
  rw [Finset.sum_eq_single a (fun d _ hd => by simp [Matrix.single_apply, hd.symm]) (by simp)]
  by_cases hc : c = b
  · simp [hc]
  · simp [Matrix.single_apply, hc, Ne.symm hc]

theorem cas_apply (U : URep k r) (x : M (vr k r true, U)) (c : Fin (2 * r + k + 1)) :
    cas (vr k r true, U) x c = casR (vr k r true, U) x c - (2 : ℂ) • kOp U x c + ((2 * r + k + 1 : ℕ) : ℂ) • x c := by
  simp only [cas, casR, dOp, LinearMap.compLeft_apply, Function.comp_apply, LinearMap.sum_apply, Finset.sum_apply,
    Module.End.mul_apply, L_apply, kOp_apply, map_sub, Finset.sum_sub_distrib, apply_ite (U.dC _), map_zero]
  have e1 : ∑ a, ∑ b, (if c = a then U.dC (Matrix.single a b 1) (x b) else 0) = ∑ b, U.dC (Matrix.single c b 1) (x b) := by
    rw [Finset.sum_comm]; simp
  have e2 : ∑ a : Fin (2 * r + k + 1), ∑ b, (if c = b then U.dC (Matrix.single b a 1) (x a) - (if True then x b else 0) else 0) =
      ∑ b, U.dC (Matrix.single c b 1) (x b) - ((2 * r + k + 1 : ℕ) : ℂ) • x c := by
    rw [Nat.cast_smul_eq_nsmul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
  rw [e1, e2, two_smul]
  abel

theorem kOp_io {μ : Fin (2 * r + k + 1) → ℝ} {U T : URep k r} (hk : 1 ≤ k) (hU : U.R.IsDS ε μ) (s : Fin (2 * r + k + 1))
    (hT : T.R.IsDS ε (shift true μ s)) (i : M (one T) →ₗ[ℂ] M (vr k r true, U)) (hi : IsHom (one T) (vr k r true, U) i)
    (y : M (one T)) : kOp U (i y) = ((μ s : ℂ) + (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2) • i y := by
  have S := zuckerman_ingredients
  have hL := S.homLie k r _ _ i (S.okTriv k r) (S.okVr k r true) hi
  have h1 : cas (vr k r true, U) (i y) = i (cas (one T) y) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [cas, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← LinearMap.comp_apply (L _ (Matrix.single b a 1)) i, ← hL, LinearMap.comp_apply,
      ← LinearMap.comp_apply (L _ (Matrix.single a b 1)) i, ← hL, LinearMap.comp_apply]
  rw [(S.casDS S.infChar k r ε _ T hk hT (triv k r)).2, casG_shift] at h1
  funext c
  have h2 := cas_apply U (i y) c
  rw [h1, (S.casDS S.infChar k r ε _ U hk hU (vr k r true)).1] at h2
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, Pi.smul_apply, if_true] at h2 ⊢
  push_cast at h2 ⊢
  linear_combination (norm := module) (1 / 2 : ℂ) • h2

end PositivityTheory.UnitaryDecomposition.DecA
end
end

open Matrix Finset
open scoped InnerProductSpace Classical

noncomputable section

namespace PositivityTheory.UnitaryDecomposition.DecB

open CompanionTheory.Zuck PositivityTheory.UnitaryDecomposition.DecA BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam IsCayleyU)
open Formalism.REAL (Jm UJ)

section Lin

variable {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Jm_sq (ε : Fin m → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem formT_mat (ε : Fin m → Bool) (A : Matrix (Fin m) (Fin m) ℂ) (hA : A * Jm ε * Aᴴ = Jm ε) (y x : Fin m → H) :
    formT ε (fun c => ∑ d, A d c • y d) (fun c => ∑ d, A d c • x d) = formT ε y x := by
  have key : ∀ d e, ∑ c, (if ε c = true then (1:ℂ) else -1) * (starRingEnd ℂ (A d c) * A e c) = Jm ε e d := by
    intro d e
    rw [← hA, Jm, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, conjTranspose_apply, Complex.star_def]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  calc formT ε (fun c => ∑ d, A d c • y d) (fun c => ∑ d, A d c • x d)
      = ∑ e, ∑ d, (∑ c, (if ε c = true then (1:ℂ) else -1) * (starRingEnd ℂ (A d c) * A e c)) * ⟪y d, x e⟫_ℂ := by
        unfold formT
        simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = formT ε y x := by
        simp only [key, Jm, diagonal_apply]
        unfold formT
        refine Finset.sum_congr rfl fun d _ => ?_
        simp

theorem formT_le (ε : Fin m → Bool) (A : Matrix (Fin m) (Fin m) ℂ) (y x : Fin m → H) :
    ‖formT ε (fun c => ∑ d, A d c • y d) (fun c => ∑ d, A d c • x d)‖ ≤
      (∑ c, (∑ d, ‖A d c‖) ^ 2) * ((∑ d, ‖x d‖) * ∑ d, ‖y d‖) := by
  have bound : ∀ (z : Fin m → H) (c : Fin m), ‖∑ d, A d c • z d‖ ≤ (∑ d, ‖A d c‖) * ∑ d, ‖z d‖ := by
    intro z c
    calc ‖∑ d, A d c • z d‖ ≤ ∑ d, ‖A d c‖ * ‖z d‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp [norm_smul]
      _ ≤ ∑ d, ‖A d c‖ * ∑ d, ‖z d‖ := by
          refine Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact Finset.single_le_sum (f := fun d => ‖z d‖) (fun i _ => norm_nonneg _) (Finset.mem_univ d)
      _ = (∑ d, ‖A d c‖) * ∑ d, ‖z d‖ := by rw [Finset.sum_mul]
  unfold formT
  calc ‖∑ c, (if ε c = true then (1:ℂ) else -1) * ⟪∑ d, A d c • y d, ∑ d, A d c • x d⟫_ℂ‖
      ≤ ∑ c, ‖∑ d, A d c • y d‖ * ‖∑ d, A d c • x d‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        rw [norm_mul]
        have h1 : ‖(if ε c = true then (1:ℂ) else -1)‖ = 1 := by split_ifs <;> simp
        rw [h1, one_mul]
        exact norm_inner_le_norm _ _
    _ ≤ ∑ c, ((∑ d, ‖A d c‖) * ∑ d, ‖y d‖) * ((∑ d, ‖A d c‖) * ∑ d, ‖x d‖) := by
        refine Finset.sum_le_sum fun c _ => mul_le_mul (bound y c) (bound x c) (norm_nonneg _) ?_
        exact mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ = (∑ c, (∑ d, ‖A d c‖) ^ 2) * ((∑ d, ‖x d‖) * ∑ d, ‖y d‖) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring

theorem sum_comp (A B : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → H) (c : Fin m) :
    ∑ d, B d c • ∑ e, A e d • x e = ∑ e, (A * B) e c • x e := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => by rw [mul_comm]

theorem sum_one (x : Fin m → H) (c : Fin m) : ∑ e, (1 : Matrix (Fin m) (Fin m) ℂ) e c • x e = x c := by
  simp [Matrix.one_apply]

end Lin

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem cay_mem {P : Mx k r} (hP : IsCayleyU k r ε P) {g : Mx k r} (hg : gᴴ * Jm ε * g = Jm ε) : P⁻¹ * g * P ∈ GG k r := by
  obtain ⟨⟨hu, hP⟩, _⟩ := hP
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hu)
  have hPi' : P⁻¹ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPi, conjTranspose_one]
  have hP' : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP
  show (P⁻¹ * g * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (P⁻¹ * g * P) = Formalism.QuantumDeterminants.Hpk k r
  rw [← hP']
  calc (P⁻¹ * g * P)ᴴ * (Pᴴ * Jm ε * P) * (P⁻¹ * g * P)
      = Pᴴ * gᴴ * (P⁻¹ᴴ * Pᴴ) * Jm ε * (P * P⁻¹) * g * P := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * (gᴴ * Jm ε * g) * P := by
        rw [hPi, hPi']
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Pᴴ * Jm ε * P := by rw [hg]

theorem cay_mem' {P : Mx k r} (hP : IsCayleyU k r ε P) {g : Mx k r} (hg : g ∈ GG k r) :
    (P * g * P⁻¹)ᴴ * Jm ε * (P * g * P⁻¹) = Jm ε := by
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : P⁻¹ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hPu, conjTranspose_one]
  have hg' : gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r := hg
  have hc : Pᴴ * Jm ε * P = PI.UpqRep.Hpk k r := hP.1.2
  calc (P * g * P⁻¹)ᴴ * Jm ε * (P * g * P⁻¹) = P⁻¹ᴴ * (gᴴ * (Pᴴ * Jm ε * P) * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹ᴴ * Pᴴ) * Jm ε * (P * P⁻¹) := by rw [hc, hg', ← hc]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one, Matrix.one_mul]

theorem cay_two {P Q : Mx k r} (hP : IsCayleyU k r ε P) (hQ : IsCayleyU k r ε Q) : Q⁻¹ * P ∈ GG k r := by
  obtain ⟨⟨hu, hP'⟩, _⟩ := hP
  obtain ⟨⟨hv, hQ'⟩, _⟩ := hQ
  have hQi : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).mp hv)
  have hQi' : Q⁻¹ᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQi, conjTranspose_one]
  have e1 : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP'
  have e2 : Qᴴ * Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r := hQ'
  show (Q⁻¹ * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Q⁻¹ * P) = Formalism.QuantumDeterminants.Hpk k r
  calc (Q⁻¹ * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Q⁻¹ * P)
      = Pᴴ * ((Q⁻¹ᴴ * Qᴴ) * Jm ε * (Q * Q⁻¹)) * P := by
        rw [← e2]
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by
        rw [hQi, hQi', Matrix.one_mul, Matrix.mul_one]
        exact e1

theorem act_coe (U : URep k r) {g : Mx k r} (hg : g ∈ GG k r) (x : M (vr k r true, U)) (c : Fin (2 * r + k + 1)) :
    (CompanionTheory.Zuck.act (vr k r true, U) g x c : U.R.H) = ∑ d, g⁻¹ d c • U.R.σ g (x d) := by
  simp only [CompanionTheory.Zuck.act, CompanionTheory.Zuck.mAct, CompanionTheory.Zuck.dOp, vr, if_true, ite_true, BranchingSupport.dualM, CompanionTheory.Zuck.URep.sig, dif_pos hg,
    LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.compLeft_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, Function.comp_apply, transpose_apply, Submodule.coe_sum,
    Submodule.coe_smul, LinearMap.restrict_coe_apply, ContinuousLinearMap.coe_coe]
  rfl

theorem act_one_coe (U : URep k r) {g : Mx k r} (hg : g ∈ GG k r) (x : M (one U)) :
    (CompanionTheory.Zuck.act (one U) g x () : U.R.H) = U.R.σ g (x ()) := by
  simp only [CompanionTheory.Zuck.act, CompanionTheory.Zuck.mAct, CompanionTheory.Zuck.dOp, CompanionTheory.Zuck.one, CompanionTheory.Zuck.triv, CompanionTheory.Zuck.URep.sig, dif_pos hg,
    LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.compLeft_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, Function.comp_apply, Submodule.coe_sum,
    Submodule.coe_smul, LinearMap.restrict_coe_apply, ContinuousLinearMap.coe_coe]
  simp only [Fintype.univ_unit, Finset.sum_singleton, Matrix.one_apply_eq, one_smul]
  rfl

def dn (U : URep k r) (P : Mx k r) : M (vr k r true, U) →ₗ[ℂ] (Fin (2 * r + k + 1) → U.R.H) where
  toFun x := fun c => ∑ d, P⁻¹ d c • (x d : U.R.H)
  map_add' x y := by funext c; simp [Finset.sum_add_distrib]
  map_smul' a x := by funext c; simp [Finset.smul_sum, smul_smul, mul_comm]

def ext1 (T : URep k r) (x : T.R.H) : M (one T) := if h : x ∈ T.R.sm then fun _ => ⟨x, h⟩ else 0

theorem extension_one_coe (T : URep k r) (y : M (one T)) : ext1 T (y ()) = y := by
  funext u
  have h : ((y ()) : T.R.H) ∈ T.R.sm := (y ()).2
  simp [ext1, h]

theorem extendHalfPlane_coe_point (T : URep k r) {x : T.R.H} (h : x ∈ T.R.sm) : (ext1 T x () : T.R.H) = x := by
  rw [ext1, dif_pos h]

theorem one_ext (T : URep k r) {y y' : M (one T)} (h : (y () : T.R.H) = y' ()) : y = y' :=
  funext fun _ => Subtype.ext h

private theorem formT_add_right {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ε : Fin m → Bool) (y x x' : Fin m → H) : formT ε y (x + x') = formT ε y x + formT ε y x' := by
  unfold formT
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.add_apply, inner_add_right, mul_add]

private theorem formT_add_left {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ε : Fin m → Bool) (y y' x : Fin m → H) : formT ε (y + y') x = formT ε y x + formT ε y' x := by
  unfold formT
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.add_apply, inner_add_left, mul_add]

private theorem formT_smul_right {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ε : Fin m → Bool) (a : ℂ) (y x : Fin m → H) : formT ε y (a • x) = a * formT ε y x := by
  unfold formT
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.smul_apply, inner_smul_right]
  ring

private theorem formT_smul_left {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ε : Fin m → Bool) (a : ℂ) (y x : Fin m → H) : formT ε (a • y) x = star a * formT ε y x := by
  unfold formT
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.smul_apply, inner_smul_left, Complex.star_def]
  ring

private theorem ext1_add' (T : URep k r) {x x' : T.R.H} (hx : x ∈ T.R.sm) (hx' : x' ∈ T.R.sm) :
    ext1 T (x + x') = ext1 T x + ext1 T x' := by
  have h : x + x' ∈ T.R.sm := T.R.smSub.add_mem hx hx'
  apply one_ext
  rw [extendHalfPlane_coe_point T h, Pi.add_apply, Submodule.coe_add, extendHalfPlane_coe_point T hx, extendHalfPlane_coe_point T hx']

private theorem ext1_smul (T : URep k r) (a : ℂ) {x : T.R.H} (hx : x ∈ T.R.sm) :
    ext1 T (a • x) = a • ext1 T x := by
  have h : a • x ∈ T.R.sm := T.R.smSub.smul_mem a hx
  apply one_ext
  rw [extendHalfPlane_coe_point T h, Pi.smul_apply, Submodule.coe_smul, extendHalfPlane_coe_point T hx]

private theorem sn_one_ext1_eq_norm_dsigW (T : URep k r) {x : T.R.H} (hx : x ∈ T.R.sm) (W : List (Mx k r)) :
    CompanionTheory.Zuck.sn (one T) W (ext1 T x) = ‖PI.UpqRep.dsigW T.R.σ W x‖ := by
  show ∑ c : Unit, ‖PI.UpqRep.dsigW T.R.σ W (ext1 T x c : T.R.H)‖ = _
  rw [Fintype.sum_unique]
  show ‖PI.UpqRep.dsigW T.R.σ W (ext1 T x () : T.R.H)‖ = _
  rw [extendHalfPlane_coe_point T hx]

private theorem sn_nil_eq_sum_norm (U : URep k r) (w : M (vr k r true, U)) :
    CompanionTheory.Zuck.sn (vr k r true, U) [] w = ∑ c, ‖(w c : U.R.H)‖ := rfl

theorem invForm {U T T' : URep k r} {P : Mx k r} (hP : IsCayleyU k r ε P) (i : M (one T) →ₗ[ℂ] M (vr k r true, U))
    (i' : M (one T') →ₗ[ℂ] M (vr k r true, U)) (hi : IsHom (one T) (vr k r true, U) i)
    (hi' : IsHom (one T') (vr k r true, U) i') :
    IsInvForm T.R T'.R fun x y => formT ε (dn U P (i' (ext1 T' y))) (dn U P (i (ext1 T x))) := by
  have hJ : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv (Jm_sq ε)
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  unfold BranchingSupport.IsInvForm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx x' hx' y hy
    simp only [ext1_add' T hx hx', map_add (f := _), formT_add_right]
  · intro a x hx y hy
    simp only [ext1_smul T a hx, map_smul, formT_smul_right]
  · intro x hx y hy y' hy'
    simp only [ext1_add' T' hy hy', map_add (f := _), formT_add_left]
  · intro a x hx y hy
    simp only [ext1_smul T' a hy, map_smul, formT_smul_left]
  · intro g hg x hx y hy
    have e1 : ∀ (T0 : URep k r) {z : T0.R.H}, z ∈ T0.R.sm →
        ext1 T0 (T0.R.σ g z) = CompanionTheory.Zuck.act (one T0) g (ext1 T0 z) := by
      intro T0 z hz
      have hm : T0.R.σ g z ∈ T0.R.sm := by
        have h0 := (CompanionTheory.Zuck.act (one T0) g (ext1 T0 z) ()).2
        rw [act_one_coe T0 hg, extendHalfPlane_coe_point T0 hz] at h0
        exact h0
      apply one_ext
      rw [extendHalfPlane_coe_point T0 hm, act_one_coe T0 hg, extendHalfPlane_coe_point T0 hz]
    have eB : P⁻¹ * (P * g * P⁻¹)⁻¹ = g⁻¹ * P⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hdet, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
    have e2 : ∀ w : M (vr k r true, U), dn U P (CompanionTheory.Zuck.act (vr k r true, U) g w) =
        fun c => ∑ d, (P * g * P⁻¹)⁻¹ d c • U.R.σ g (dn U P w d) := by
      intro w
      funext c
      show ∑ d, P⁻¹ d c • ((CompanionTheory.Zuck.act (vr k r true, U) g w d : U.R.H)) =
        ∑ d, (P * g * P⁻¹)⁻¹ d c • U.R.σ g (∑ e, P⁻¹ e d • (w e : U.R.H))
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [act_coe U hg, map_sum, map_smul]
      rw [sum_comp, sum_comp, eB]
    have hB : (P * g * P⁻¹)⁻¹ * Jm ε * ((P * g * P⁻¹)⁻¹)ᴴ = Jm ε := by
      have hC := cay_mem' hP hg
      have h2 : ((P * g * P⁻¹)ᴴ * Jm ε * (P * g * P⁻¹))⁻¹ = (Jm ε)⁻¹ := by rw [hC]
      rw [Matrix.mul_inv_rev ((P * g * P⁻¹)ᴴ * Jm ε) (P * g * P⁻¹), Matrix.mul_inv_rev ((P * g * P⁻¹)ᴴ) (Jm ε),
        hJ] at h2
      rw [Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
      exact h2
    have hiso : ∀ v w : U.R.H, ⟪U.R.σ g v, U.R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ := by
      intro v w
      let L : U.R.H →ₗᵢ[ℂ] U.R.H :=
        { toLinearMap := (U.R.σ g : U.R.H →ₗ[ℂ] U.R.H), norm_map' := U.rep.2.1 g hg }
      exact L.inner_map_map v w
    have hi1 := LinearMap.congr_fun (hi.equiv g hg) (ext1 T x)
    have hi2 := LinearMap.congr_fun (hi'.equiv g hg) (ext1 T' y)
    simp only [LinearMap.comp_apply] at hi1 hi2
    simp only []
    rw [e1 T hx, e1 T' hy, hi1, hi2, e2, e2, formT_mat ε _ hB]
    unfold formT
    simp only [hiso]
  · obtain ⟨C1, Ws, hWs, hb1⟩ := hi.cont [] (by intro Y hY; simp at hY)
    obtain ⟨C2, Ws', hWs', hb2⟩ := hi'.cont [] (by intro Y hY; simp at hY)
    refine ⟨(∑ c, (∑ d, ‖P⁻¹ d c‖) ^ 2) * C1 * C2, Ws, Ws', ?_, ?_⟩
    · intro W hW X hX
      rcases List.mem_append.mp hW with h | h
      · exact hWs W h X hX
      · exact hWs' W h X hX
    · intro x hx y hy
      have s1 := hb1 (ext1 T x)
      have s2 := hb2 (ext1 T' y)
      simp only [sn_one_ext1_eq_norm_dsigW T hx, sn_one_ext1_eq_norm_dsigW T' hy, sn_nil_eq_sum_norm] at s1 s2
      have hK : 0 ≤ ∑ c, (∑ d, ‖P⁻¹ d c‖) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have n1 : 0 ≤ ∑ d, ‖(i (ext1 T x) d : U.R.H)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      have n2 : 0 ≤ ∑ d, ‖(i' (ext1 T' y) d : U.R.H)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      calc ‖formT ε (dn U P (i' (ext1 T' y))) (dn U P (i (ext1 T x)))‖
          ≤ (∑ c, (∑ d, ‖P⁻¹ d c‖) ^ 2) *
              ((∑ d, ‖(i (ext1 T x) d : U.R.H)‖) * ∑ d, ‖(i' (ext1 T' y) d : U.R.H)‖) :=
            formT_le ε P⁻¹ (fun d => (i' (ext1 T' y) d : U.R.H)) (fun d => (i (ext1 T x) d : U.R.H))
        _ ≤ (∑ c, (∑ d, ‖P⁻¹ d c‖) ^ 2) *
              ((C1 * (List.map (fun W => ‖PI.UpqRep.dsigW T.R.σ W x‖) Ws).sum) *
                (C2 * (List.map (fun W => ‖PI.UpqRep.dsigW T'.R.σ W y‖) Ws').sum)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul s1 s2 n2 (n1.trans s1)) hK
        _ = (∑ c, (∑ d, ‖P⁻¹ d c‖) ^ 2) * C1 * C2 * (List.map (fun W => ‖PI.UpqRep.dsigW T.R.σ W x‖) Ws).sum *
              (List.map (fun W => ‖PI.UpqRep.dsigW T'.R.σ W y‖) Ws').sum := by ring

end PositivityTheory.UnitaryDecomposition.DecB
end
end

open Matrix Finset
open scoped InnerProductSpace Classical

noncomputable section

namespace PositivityTheory.UnitaryDecomposition.DecB

open CompanionTheory.Zuck PositivityTheory.UnitaryDecomposition.DecA BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam IsCayleyU)
open Formalism.REAL (Jm UJ)

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem cas_dn {μ : Fin (2 * r + k + 1) → ℝ} {U : URep k r} (hU : U.R.IsDS ε μ) {P : Mx k r} (hP : IsCayleyU k r ε P)
    (x : M (vr k r true, U)) : casT ε (fun g => U.R.σ (P⁻¹ * g * P)) (dn U P x) = dn U P (kOp U x) := by
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have hexp := (GlobalTheory.T.derivedAction_expand_matrixUnits CompanionTheory.D.gk.admitted.k_finite_smooth k r ε μ U.R hU 1 _ isUnit_one (GlobalTheory.CompanionTheory.CasimirDS.isE_one U)).2.1
  funext c
  show _ = ∑ a, P⁻¹ a c • (kOp U x a : U.R.H)
  have e1 : ∀ l, dn U P x l = ((∑ d, P⁻¹ d l • x d : U.R.smSub) : U.R.H) := fun l => by simp [dn]
  simp only [casT, (GlobalTheory.CayleyTransport.smooth_and_dsigC_transport k r ε U.R P hP).2, e1, hexp]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [inv_one, Matrix.one_mul, Matrix.mul_one, map_sum, map_smul, kOp_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.smul_sum, smul_smul]
  have e2 : ∀ a b d, ∑ l, (P⁻¹ * Matrix.single c l (1 : ℂ) * P) a b * P⁻¹ d l = if b = d then P⁻¹ a c else 0 := fun a b d => by
    have h1 : ∀ l, (P⁻¹ * Matrix.single c l (1 : ℂ) * P) a b = P⁻¹ a c * P l b := fun l => by
      rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single c (fun j _ hj => by
        rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hj, mul_zero]) (by simp), Matrix.single_mul_apply_same, one_mul]
    have h2 := congrFun (congrFun (Matrix.nonsing_inv_mul P hPu) d) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h2
    simp only [h1, mul_assoc, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun l _ => mul_comm (P l b) (P⁻¹ d l), h2]
    by_cases h : d = b
    · simp [h]
    · simp [h, Ne.symm h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, e2]
  simp

theorem dec_U (hk : 1 ≤ k) (lam : Fin (2 * r + k + 1) → ℝ) (U : URep k r) (π : Mx k r → (U.R.H →L[ℂ] U.R.H)) {P : Mx k r}
    (hP : IsCayleyU k r ε P) (hπe : (fun g => U.R.σ (P⁻¹ * g * P)) = π) (hU : U.R.IsDS ε lam)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) : Nonempty (Dec ε lam π) := by
  have S := zuckerman_ingredients
  have hl : IsHCParam lam := hU.1
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hth : thr _ ε + (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) + 1 < 200 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by
    have h1 := thr_le (n := 2 * r + k + 1) (by omega) ε
    have h2 : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
    have h3 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ hn1
    rw [Nat.cast_add, Nat.cast_pow]
    push_cast at h1 h2 h3 ⊢
    linarith
  obtain ⟨T0, hT0, -, -⟩ := injV S zuckerman_library_bounds true hU hg (by linarith)
  let T : Fin (2 * r + k + 1) → URep k r := fun s => if h : IsHCParam (shift true lam s) then T0 ⟨s, h⟩ else U
  have hT : ∀ s : {s // IsHCParam (shift true lam s)}, (T s.1).R.IsDS ε (shift true lam s.1) := fun s => by
    simp only [T, dif_pos s.2]; exact hT0 s
  obtain ⟨io, pr, hD⟩ := decReg S zuckerman_library_bounds hk true hU hg hth (fun s => T s.1) hT
  have hsimp := S.schur S.infChar k r ε _ _ (fun s : {s // IsHCParam (shift true lam s)} => T s.1)
    ((shift_inj true lam).comp Subtype.val_injective) hT
  have hQ : ∀ s, ∃ Q : Mx k r, IsCayleyU k r ε Q ∧ (IsHCParam (shift true lam s) →
      PI.UpqRep.IsDS ε (shift true lam s) fun g => (T s).R.σ (Q⁻¹ * g * Q)) := fun s => by
    by_cases h : IsHCParam (shift true lam s)
    · obtain ⟨Q, h1, h2⟩ := (hT ⟨s, h⟩).2
      exact ⟨Q, h1, fun _ => h2⟩
    · exact ⟨P, hP, fun h' => absurd h' h⟩
  choose Q hQ1 hQ2 using hQ
  have sm_iff : ∀ v : U.R.H, v ∈ PI.PhMeasCore.smoothVecs (Jm ε) π ↔ v ∈ U.R.sm := fun v => by
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · have h1 := GlobalTheory.CayleyTransport.smoothOn_comp (H := Jm ε) (J := PI.UpqRep.Hpk k r) (A := P) (B := P⁻¹)
        (f := fun g => π g v) (fun g hg' => cay_mem' hP hg') hv
      have h2 : (fun g => π (P * g * P⁻¹) v) = fun g => U.R.σ g v := funext fun g => by
        rw [← hπe]
        show U.R.σ (P⁻¹ * (P * g * P⁻¹) * P) v = _
        rw [Matrix.mul_assoc P, Matrix.nonsing_inv_mul_cancel_left _ _ hPu, Matrix.nonsing_inv_mul_cancel_right _ _ hPu]
      rw [h2] at h1
      exact h1
    · have := (GlobalTheory.CayleyTransport.smooth_and_dsigC_transport k r ε U.R P hP).1 v hv
      rwa [hπe] at this
  let up : (Fin (2 * r + k + 1) → U.R.H) → M (vr k r true, U) := fun x =>
    if h : x ∈ SmT ε π then fun c => ∑ d, P d c • (⟨x d, (sm_iff _).1 (h d)⟩ : U.R.smSub) else 0
  have up_coe : ∀ x ∈ SmT ε π, ∀ c, (up x c : U.R.H) = ∑ d, P d c • x d := fun x hx c => by
    simp only [up, dif_pos hx]; simp
  have dn_up : ∀ x ∈ SmT ε π, dn U P (up x) = x := fun x hx => funext fun c => by
    show ∑ d, P⁻¹ d c • (up x d : U.R.H) = x c
    simp only [up_coe x hx]
    rw [sum_comp, Matrix.mul_nonsing_inv _ hPu, sum_one]
  have dn_sm : ∀ z, dn U P z ∈ SmT ε π := fun z c =>
    (sm_iff _).2 (show ∑ d, P⁻¹ d c • (z d : U.R.H) ∈ U.R.smSub from
      U.R.smSub.sum_mem fun d _ => U.R.smSub.smul_mem _ (z d).2)
  have up_dn : ∀ z, up (dn U P z) = z := fun z => funext fun c => Subtype.ext (by
    rw [up_coe _ (dn_sm z)]
    show ∑ d, P d c • ∑ e, P⁻¹ e d • (z e : U.R.H) = _
    rw [sum_comp, Matrix.nonsing_inv_mul _ hPu, sum_one])
  have mem : ∀ g : UJ ε, P⁻¹ * um g * P ∈ GG k r := fun g => cay_mem hP g.2
  have dn_act : ∀ (g : UJ ε) z, dn U P (CompanionTheory.Zuck.act (vr k r true, U) (P⁻¹ * um g * P) z) = actT π (um g) (dn U P z) := fun g z => by
    funext c
    show ∑ d, P⁻¹ d c • (CompanionTheory.Zuck.act (vr k r true, U) (P⁻¹ * um g * P) z d : U.R.H) = ∑ d, (um g)⁻¹ d c • π (um g) (∑ e, P⁻¹ e d • (z e : U.R.H))
    have e0 : U.R.σ (P⁻¹ * um g * P) = π (um g) := congrFun hπe _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [act_coe U (mem g), map_sum, map_smul, e0]
    rw [sum_comp, sum_comp, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hPu, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_right _ _ hPu]
  have up_act : ∀ (g : UJ ε), ∀ x ∈ SmT ε π, up (actT π (um g) x) = CompanionTheory.Zuck.act (vr k r true, U) (P⁻¹ * um g * P) (up x) :=
    fun g x hx => by rw [← up_dn (CompanionTheory.Zuck.act _ _ _), dn_act, dn_up x hx]
  have hform := fun s s' => invForm (U := U) hP (io s) (io s') (hD.io_hom s) (hD.io_hom s')
  choose cI hc using fun s => (CompanionTheory.D.gk.Poul.poulsen_smooth_vectors_dense k r ε _ _ _ _ (hT s) (hT s)).1 _ (hform s s)
  have horth : ∀ s s', s ≠ s' → ∀ a b, formT ε (dn U P (io s' b)) (dn U P (io s a)) = 0 := fun s s' hs a b => by
    rcases (CompanionTheory.D.gk.Poul.poulsen_smooth_vectors_dense k r ε _ _ _ _ (hT s) (hT s')).2 _ (hform s s') with h | h
    · have := h _ (a ()).2 _ (b ()).2
      simpa only [extension_one_coe] using this
    · obtain ⟨f, g, hf, -, hgf, -⟩ := S.uIso k r (triv k r) _ _ h
      have h0 := hsimp.2.2 s s' hs f hf
      obtain ⟨y, y', hy⟩ := hsimp.1 s
      have h1 : ∀ z, z = (g ∘ₗ f) z := fun z => by rw [hgf]; rfl
      exact absurd ((h1 y).trans (by rw [h1 y', h0]; simp)) hy
  have bmem : ∀ s, (Q s)⁻¹ * P ∈ GG k r := fun s => cay_two hP (hQ1 s)
  have sumS : ∀ f : {s // IsHCParam (shift true lam s)} → Fin (2 * r + k + 1) → U.R.H,
      ∑ s ∈ univ.filter (fun s => IsHCParam (shift true lam s)), (if h : IsHCParam (shift true lam s) then f ⟨s, h⟩ else 0) =
        ∑ s, f s := fun f => by
    rw [Finset.sum_subtype (p := fun s => IsHCParam (shift true lam s)) _ (by simp)]
    exact Finset.sum_congr rfl fun s _ => dif_pos s.2
  have hsum : ∀ z, ∑ s, io s (pr s z) = z := fun z => by
    have := LinearMap.congr_fun hD.sum z
    simpa [LinearMap.sum_apply] using this
  refine ⟨{ S := univ.filter fun s => IsHCParam (shift true lam s)
            Hs := fun s => (T s).R.H
            πs := fun s g => (T s).R.σ ((Q s)⁻¹ * g * Q s)
            ds := fun s hs => ⟨(mem_filter.1 hs).2, hQ2 s (mem_filter.1 hs).2⟩
            p := fun s x => if h : IsHCParam (shift true lam s) then dn U P (io ⟨s, h⟩ (pr ⟨s, h⟩ (up x))) else 0
            pr := fun s x => if h : IsHCParam (shift true lam s) then (T s).R.σ ((Q s)⁻¹ * P) (pr ⟨s, h⟩ (up x) ()) else 0
            c := fun s => if h : IsHCParam (shift true lam s) then cI ⟨s, h⟩ else 0
            κ := fun s => (lam s : ℂ) + (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2
            p_sm := fun s hs x _ => by rw [dif_pos (mem_filter.1 hs).2]; exact dn_sm _
            sum := fun x hx => by rw [sumS fun s => dn U P (io s (pr s (up x))), ← map_sum, hsum, dn_up x hx]
            p_act := fun s hs g x hx => ?_
            pr_act := fun s hs g x hx => ?_
            form := fun s hs x hx y hy => ?_
            cas := fun s hs x hx => ?_
            κ_inj := fun s _ s' _ h => hl.1.injective (by exact_mod_cast add_right_cancel h) }⟩
  · have h := (mem_filter.1 hs).2
    simp only [dif_pos h]
    rw [up_act g x hx, ← dn_act]
    congr 1
    exact LinearMap.congr_fun (((S.homCat k r).comp _ _ _ _ _ (hD.pr_hom ⟨s, h⟩) (hD.io_hom ⟨s, h⟩)).equiv _ (mem g)) (up x)
  · have h := (mem_filter.1 hs).2
    have hQu : IsUnit (Q s).det := (Matrix.isUnit_iff_isUnit_det _).1 (hQ1 s).1.1
    simp only [dif_pos h]
    have e := LinearMap.congr_fun ((hD.pr_hom ⟨s, h⟩).equiv _ (mem g)) (up x)
    simp only [LinearMap.comp_apply] at e
    rw [up_act g x hx, e, act_one_coe _ (mem g), ← (T s).repOn.apply_mul (bmem s) (mem g),
      ← (T s).repOn.apply_mul (cay_mem (hQ1 s) g.2) (bmem s)]
    congr 2
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hPu, Matrix.mul_nonsing_inv_cancel_left _ _ hQu]
  · have h := (mem_filter.1 hs).2
    simp only [dif_pos h]
    have e := (LinearMap.norm_map_iff_inner_map_map ((T s).R.σ ((Q s)⁻¹ * P) : (T s).R.H →ₗ[ℂ] (T s).R.H)).1
      ((T s).rep.2.1 _ (bmem s)) (pr ⟨s, h⟩ (up y) ()) (pr ⟨s, h⟩ (up x) ())
    simp only [ContinuousLinearMap.coe_coe] at e
    rw [e, ← hc ⟨s, h⟩ _ (pr ⟨s, h⟩ (up x) ()).2 _ (pr ⟨s, h⟩ (up y) ()).2]
    simp only [extension_one_coe]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← dn_up y hy, ← hsum (up y), map_sum]
    have e2 : ∀ (f : {s // IsHCParam (shift true lam s)} → Fin (2 * r + k + 1) → U.R.H) z,
        formT ε (∑ s', f s') z = ∑ s', formT ε (f s') z := fun f z => by
      simp only [formT, Finset.sum_apply, sum_inner, Finset.mul_sum]
      exact Finset.sum_comm
    rw [e2, Finset.sum_eq_single ⟨s, h⟩ (fun s' _ hs' => horth _ _ (Ne.symm hs') _ _) (by simp)]
  · have h := (mem_filter.1 hs).2
    simp only [dif_pos h]
    have e := cas_dn hU hP (io ⟨s, h⟩ (pr ⟨s, h⟩ (up x)))
    rw [show (fun g => U.R.σ (P⁻¹ * g * P)) = π from hπe] at e
    rw [e, kOp_io hk hU s (hT ⟨s, h⟩) _ (hD.io_hom ⟨s, h⟩), map_smul]

theorem dec_hpk (hk : 1 ≤ k) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Mx k r → (H →L[ℂ] H)) {P : Mx k r} (hP : IsCayleyU k r ε P) (hl : IsHCParam lam) (hπ : Formalism.MainNotions.S.IsDS ε lam π)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) : Nonempty (Dec ε lam π) := by
  haveI : CompleteSpace H := hπ.1
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  let R : Rep k r := { H := H, σ := fun g => π (P * g * P⁻¹) }
  have hπe : (fun g => R.σ (P⁻¹ * g * P)) = π := funext fun g => by
    show π (P * (P⁻¹ * g * P) * P⁻¹) = π g
    rw [Matrix.mul_assoc P⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ hPu, Matrix.mul_nonsing_inv_cancel_right _ _ hPu]
  have hR : R.IsDS ε lam := ⟨hl, P, hP, by rw [hπe]; exact hπ⟩
  exact dec_U hk lam (mkU R hR) π hP hπe hR hg

theorem unitary_decomposition_exists : DecEx := by
  intro m ε lam H _ _ π ⟨a, ha⟩ hle hl hπ hg
  have h1 : 1 ≤ (univ.filter fun a => ε a = false).card := Finset.card_pos.2 ⟨a, by simp [ha]⟩
  have h2 : (univ.filter fun a => ε a = true).card + (univ.filter fun a => ε a = false).card = m := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) fun a => ε a = true
    simpa using this
  obtain ⟨r, hr⟩ : ∃ r, (univ.filter fun a => ε a = false).card = r + 1 := ⟨_, (Nat.sub_add_cancel h1).symm⟩
  obtain ⟨k, hk⟩ : ∃ k, (univ.filter fun a => ε a = true).card = k + r := ⟨_, (Nat.sub_add_cancel (by omega)).symm⟩
  obtain rfl : m = 2 * r + k + 1 := by omega
  obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_of_card k r ε hk
  exact dec_hpk (by omega) lam H π (P := P) hP hl hπ hg

end PositivityTheory.UnitaryDecomposition.DecB
