module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupLawCompMulNZero
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EqZeroOrSingleOfDegreeLtTwo
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AddCharMemValuationSubring
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.FourierChainCompare

section Duality

variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K]

variable [Fintype A] [Fintype B]


end Duality

section Fourier

variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K] [Fintype A] [Fintype B]

end Fourier

section Chain

variable {R : Type} [CommRing R] {d : ℕ}

theorem act_zero {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) : A.act 0 = 0 := by
  have hc := A.const 0
  have h1 : A.act 0 = G.add (A.act 0) (A.act 0) := by rw [← A.add_act, add_zero]
  have h2 : A.act 0 = comp1 (A.act 0) (A.act 0) := by rw [← A.mul_act, mul_zero]
  have h3 : dLin (A.act 0) = 0 := by
    have := GlobalTheory.FormalMulN.dLin_add G hc hc
    rw [← h1] at this
    exact left_eq_add.mp this
  have h4 : ∀ i, 2 ≤ (A.act 0 i).order := fun i =>
    GlobalTheory.FormalSeries.two_le_order_iff.mpr ⟨hc i, fun j => by
      obtain ⟨j0, j⟩ := j
      obtain rfl : j0 = 0 := Subsingleton.elim _ _
      exact congrFun (congrFun h3 i) j⟩
  have h5 : ∀ (k : ℕ) i, (k : ℕ∞) ≤ (A.act 0 i).order := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro i
      have := GlobalTheory.FormalSeries.le_order_subst_sub_subst
        (a := fun p : Fin 1 × Fin d => (![A.act 0] : Fin 1 → Pt R 1 d) p.1 p.2) (b := 0) (k := k)
        (fun p => GlobalTheory.GaugeAdjoint.const_one hc p.1 p.2) (by simp)
        (fun p => by simpa using ih p.2) (h4 i)
      rw [subst_zero_of_constantCoeff_zero (hc i), sub_zero] at this
      rw [congrFun h2 i]
      exact this
  funext i
  exact GlobalTheory.FormalSeries.eq_of_forall_le_order_sub fun k => by simpa using h5 k i

end Chain

end GlobalTheory.FourierChainCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardFilterFinBounds
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem card_filter_fin_bounds {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    (0 : ℝ) ≤ ((univ.filter p).card : ℝ) ∧ ((univ.filter p).card : ℝ) ≤ n := by
  refine ⟨Nat.cast_nonneg _, ?_⟩
  have h : (univ.filter p).card ≤ n :=
    le_trans (Finset.card_filter_le _ _) (by simp)
  exact_mod_cast h

theorem abs_lowK_sub_le {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) (a : Fin n) :
    -(n : ℝ) ≤ lowK ε μ a - μ a ∧ lowK ε μ a - μ a ≤ n := by
  have e : lowK ε μ a - μ a = rhoN ε a - rhoC ε a := by
    simp only [lowK, Pi.add_apply, Pi.sub_apply]
    ring
  rw [e]
  simp only [rhoN, rhoC]
  obtain ⟨h1, h2⟩ := card_filter_fin_bounds (fun b : Fin n => a < b ∧ ε b ≠ ε a)
  obtain ⟨h3, h4⟩ := card_filter_fin_bounds (fun b : Fin n => b < a ∧ ε b ≠ ε a)
  obtain ⟨h5, h6⟩ := card_filter_fin_bounds (fun b : Fin n => a < b ∧ ε b = ε a)
  obtain ⟨h7, h8⟩ := card_filter_fin_bounds (fun b : Fin n => b < a ∧ ε b = ε a)
  constructor <;> linarith

private lemma four_sq_add_le_of_large_bv {n : ℕ} {bv : ℝ} (hn : 2 ≤ n) (hb : 10 ^ 6 * (n : ℝ) ^ 7 ≤ bv) :
    4 * (n : ℝ) ^ 2 + 2 + n ≤ bv / 32 - bv / 100 := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h7 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hsq : 4 * (n : ℝ) ^ 2 + 2 + n ≤ 6 * (n : ℝ) ^ 2 := by nlinarith
  linarith

theorem shape_position : ∀ (n kk j : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (bv : ℝ), Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → 0 < bv ∧ (∀ ω : Fin n → ℝ, ∑ a, |ω a - lowK ε μ a| ≤ j → ∀ a : Fin n, (a.val + 1 < kk → -bv / 8 - bv / 32 ≤ -ω a ∧ -ω a ≤ bv / 32) ∧ (kk ≤ a.val + 1 → bv - bv / 32 ≤ -ω a ∧ -ω a ≤ 2 * bv + bv / 32)) ∧ ∀ a : Fin n, (a.val + 1 < kk → -bv / 8 - bv / 32 ≤ -μ a + (1 - (n : ℝ)) / 2 ∧ -μ a + (1 - (n : ℝ)) / 2 ≤ bv / 32) ∧ (kk ≤ a.val + 1 → bv - bv / 32 ≤ -μ a + (1 - (n : ℝ)) / 2 ∧ -μ a + (1 - (n : ℝ)) / 2 ≤ 2 * bv + bv / 32) := by
  intro n kk j ε μ bv hS hj
  obtain ⟨hk1, hkn, -, hcl, hnd, hb⟩ := hS
  have hn : 2 ≤ n := by omega
  have hm := four_sq_add_le_of_large_bv hn hb
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hbpos : 0 < bv := by
    have : (0 : ℝ) < (n : ℝ) ^ 7 := by positivity
    linarith
  have hjr : (j : ℝ) ≤ 4 * (n : ℝ) ^ 2 + 2 := by exact_mod_cast hj
  refine ⟨hbpos, ?_, ?_⟩
  · intro ω hω a
    have hle : |ω a - lowK ε μ a| ≤ j :=
      le_trans (Finset.single_le_sum (f := fun b => |ω b - lowK ε μ b|)
        (fun b _ => abs_nonneg _) (Finset.mem_univ a)) hω
    obtain ⟨hl1, hl2⟩ := abs_lowK_sub_le ε μ a
    obtain ⟨ha1, ha2⟩ := abs_le.mp hle
    constructor
    · intro ha
      obtain ⟨-, h1, h2⟩ := hcl a ha
      constructor <;> linarith
    · intro ha
      obtain ⟨h1, h2⟩ := hnd a ha
      constructor <;> linarith
  · intro a
    constructor
    · intro ha
      obtain ⟨-, h1, h2⟩ := hcl a ha
      constructor <;> linarith
    · intro ha
      obtain ⟨h1, h2⟩ := hnd a ha
      constructor <;> linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AlgTensWtNear
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AlgTensWtNear
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem l1_shift_single_le {n : ℕ} (ω Λ : Fin n → ℝ) (t e : ℝ) (he : |e| ≤ 1) (c : Fin n)
    (h : ∑ a, |ω a - Λ a| ≤ t) :
    ∑ a, |(ω a + if a = c then e else 0) - Λ a| ≤ t + 1 := by
  have h1 : ∀ a, |(ω a + if a = c then e else 0) - Λ a| ≤ |ω a - Λ a| + if a = c then 1 else 0 := by
    intro a
    split_ifs
    · have : ω a + e - Λ a = (ω a - Λ a) + e := by ring
      rw [this]
      exact (abs_add_le _ _).trans (by linarith)
    · simp
  calc _ ≤ ∑ a, (|ω a - Λ a| + if a = c then 1 else 0) := Finset.sum_le_sum fun a _ => h1 a
    _ = ∑ a, |ω a - Λ a| + 1 := by rw [Finset.sum_add_distrib]; simp
    _ ≤ t + 1 := by linarith

theorem algTens_wtNear : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (Λ : Fin n → ℝ) (t : ℝ), AlgTens ε E N F io pr → (∀ w, w ∈ WtNear E Λ t → ∀ s c, pr s (Pi.single c w) ∈ WtNear (F s) Λ (t + 1)) ∧ ∀ s (y : N s), y ∈ WtNear (F s) Λ t → ∀ d, io s y d ∈ WtNear E Λ (t + 1) := by
  intro M _ _ n ε E N _ _ F io pr Λ t hT
  refine ⟨fun w hw s c => ?_, fun s y hy d => ?_⟩
  · induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ω, hω, hx⟩ := hx
      refine Submodule.subset_span ⟨fun a => ω a + if a = c then -1 else 0,
        l1_shift_single_le ω Λ t (-1) (by simp) c hω, fun a => ?_⟩
      rw [← hT.pr_comm, ← map_smul]
      congr 1
      ext i
      by_cases hi : i = c
      · subst hi
        by_cases ha : a = i
        · subst ha
          simp [dualTens, hx a, add_smul, sub_eq_add_neg]
        · have : ¬ i = a := fun h => ha h.symm
          simp [dualTens, hx a, ha, this]
      · by_cases ha : i = a
        · subst ha
          simp [dualTens, hi]
        · simp [dualTens, hi, ha]
    | zero => simp
    | add x y _ _ hx hy => rw [Pi.single_add, map_add (f := _)]; exact add_mem hx hy
    | smul r x _ hx => rw [Pi.single_smul, map_smul]; exact Submodule.smul_mem _ _ hx
  · induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ω, hω, hx⟩ := hx
      refine Submodule.subset_span ⟨fun a => ω a + if a = d then 1 else 0,
        l1_shift_single_le ω Λ t 1 (by simp) d hω, fun a => ?_⟩
      have h := congrFun (hT.io_comm s a a x) d
      rw [hx a, map_smul] at h
      simp only [dualTens, Pi.smul_apply] at h
      rw [eq_sub_iff_add_eq] at h
      rw [← h]
      by_cases ha : a = d
      · subst ha
        simp [add_smul]
      · have : ¬ d = a := fun h => ha h.symm
        simp [ha, this]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), Pi.add_apply]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul, Pi.smul_apply]; exact Submodule.smul_mem _ _ hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AlgTensWtNearStatement
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wtNear_pr_and_io_of_algTens : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (Λ : Fin n → ℝ) (t : ℝ), AlgTens ε E N F io pr → (∀ w, w ∈ WtNear E Λ t → ∀ s c, pr s (Pi.single c w) ∈ WtNear (F s) Λ (t + 1)) ∧ ∀ s (y : N s), y ∈ WtNear (F s) Λ t → ∀ d, io s y d ∈ WtNear E Λ (t + 1) := by
  first | exact @GlobalTheory.algTens_wtNear | exact GlobalTheory.algTens_wtNear | (intros; apply GlobalTheory.algTens_wtNear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LastComatrixRowInvertsDual
open Formalism.REAL

namespace GlobalTheory

theorem _root_.GlobalTheory.lastComatrixRow_inverts_dual : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), _root_.Formalism.REAL.GlRel E → (∀ w v, _root_.Formalism.REAL.qdet E w v = (∏ j, (w + m j)) • v) → (∀ y a, Om y a = ∑ c, E a c (y c)) → ∃ K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V), (∀ u x, K u ((u - (n : ℂ)) • x + Om x) = (∏ j, (u + m j)) • x (Fin.last n)) ∧ ∀ u v, K u (PiLp.single 2 (Fin.last n) v) = _root_.Formalism.REAL.qdet (fun a b : Fin n => E a.castSucc b.castSucc) u v := by
  intro V _ _ _ n E Om m hE hdet hOm
  let c : ℂ → Fin (n + 1) → Module.End ℂ V := fun u j =>
    ((((-1 : ℤ) ^ ((Fin.last n : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V)) * _root_.Formalism.REAL.qminor E j.succAbove (Fin.last n).succAbove u
  refine ⟨fun u => ∑ j, (c u j) ∘ₗ ((LinearMap.proj j).comp (WithLp.linearEquiv 2 ℂ (Fin (n + 1) → V)).toLinearMap), ?_, ?_⟩
  · intro u x
    have hproj : ∀ (y : PiLp 2 (fun _ : Fin (n + 1) => V)) j, (WithLp.addEquiv 2 (Fin (n + 1) → V)).toFun y j = y.ofLp j := fun _ _ => rfl
    have hcom := _root_.Formalism.REAL.qComatrix (Module.End ℂ V) n E hE u (Fin.last n)
    have hT : ∀ j, (u - (n : ℂ)) • x j + Om x j = ∑ l, _root_.Formalism.REAL.Tm E (u - (n : ℂ)) j l (x l) := by
      intro j
      have hite : ∀ l, (if j = l then (u - (n : ℂ)) • (1 : Module.End ℂ V) else 0) (x l) = if j = l then (u - (n : ℂ)) • x l else 0 := by
        intro l; split_ifs <;> simp
      simp only [_root_.Formalism.REAL.shiftedGenerator_eq_ite_smul_add, LinearMap.add_apply, Finset.sum_add_distrib, hOm, ite_smul, zero_smul, hite, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [LinearMap.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, WithLp.linearEquiv_apply, LinearMap.proj_apply, hproj, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, hT, map_sum]
    rw [Finset.sum_comm]
    simp only [← Module.End.mul_apply, ← LinearMap.sum_apply]
    have hite : ∀ l, (if Fin.last n = l then _root_.Formalism.REAL.qdet E u else 0) (x l) = if Fin.last n = l then _root_.Formalism.REAL.qdet E u (x l) else 0 := by
      intro l; split_ifs <;> simp
    simp only [c, hcom, hite, Finset.sum_ite_eq, Finset.mem_univ, if_true, hdet]
  · intro u v
    have hproj : ∀ (y : PiLp 2 (fun _ : Fin (n + 1) => V)) j, (WithLp.addEquiv 2 (Fin (n + 1) → V)).toFun y j = y.ofLp j := fun _ _ => rfl
    rw [LinearMap.sum_apply, Finset.sum_eq_single (Fin.last n)]
    · simp only [c, LinearMap.comp_apply, LinearEquiv.coe_coe, WithLp.linearEquiv_apply, LinearMap.proj_apply, hproj, PiLp.ofLp_single, Pi.single_eq_same, Fin.succAbove_last, Module.End.mul_apply]
      have hsign : ((-1 : ℤ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 := by
        rw [← two_mul, pow_mul]; simp
      rw [hsign, Int.cast_one, Module.End.one_apply]
      unfold _root_.Formalism.REAL.qdet
      rw [_root_.Formalism.REAL.quantumMinor_eq_sum_term, _root_.Formalism.REAL.quantumMinor_eq_sum_term]
      unfold _root_.Formalism.REAL.exchangeTwo_self_eq_one
      simp only [_root_.Formalism.REAL.shiftedGenerator_eq_ite_smul_add, Fin.castSucc_inj, id]
    · intro j _ hj
      simp [LinearMap.comp_apply, hproj, PiLp.ofLp_single, Pi.single_eq_of_ne hj]
    · simp

end GlobalTheory
end
