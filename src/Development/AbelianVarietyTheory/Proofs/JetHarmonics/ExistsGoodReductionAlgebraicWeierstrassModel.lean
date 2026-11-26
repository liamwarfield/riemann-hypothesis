module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommGrpObjWeierstrassScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AddCharMemValuationSubring
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorAbsoluteOfExplicit
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelOffDiagNormSqLe
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelOffDiagNormSqLe
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

open Finset in
open scoped InnerProductSpace in
private lemma abs_half_card_sub_le {n : ℕ} (s t : Finset (Fin n)) :
    |((s.card : ℝ) - (t.card : ℝ)) / 2| ≤ n := by
  have hs : (s.card : ℝ) ≤ n := by
    exact_mod_cast (Finset.card_le_univ s).trans_eq (Fintype.card_fin n)
  have ht : (t.card : ℝ) ≤ n := by
    exact_mod_cast (Finset.card_le_univ t).trans_eq (Fintype.card_fin n)
  have hs0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ t.card := Nat.cast_nonneg _
  rw [abs_le]; constructor <;> linarith

open Finset in
open scoped InnerProductSpace in
private lemma re_inner_double_sum_apply {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    {n : ℕ} (F : Fin n → Fin n → Module.End ℂ M) (w : M) :
    (⟪w, (∑ a, ∑ b, F a b) w⟫_ℂ).re = ∑ a, ∑ b, (⟪w, F a b w⟫_ℂ).re := by
  simp [LinearMap.sum_apply, inner_sum, Complex.re_sum]

open Finset in
open scoped InnerProductSpace in
private lemma norm_sq_apply_eq_re_inner_of_isUnitary {M : Type} [NormedAddCommGroup M]
    [InnerProductSpace ℂ M] {n : ℕ} {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M}
    (hE : _root_.Formalism.REAL.IsUnitary ε E) (a b : Fin n) (w : M) :
    ‖E b a w‖ ^ 2 = (if ε a = ε b then 2 * (⟪w, (E a b * E b a) w⟫_ℂ).re else 0)
      - (⟪w, (E a b * E b a) w⟫_ℂ).re := by
  have h := hE b a w (E b a w)
  unfold _root_.Formalism.REAL.sgn at h
  have hn : ‖E b a w‖ ^ 2 = (⟪E b a w, E b a w⟫_ℂ).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]; rfl
  rw [hn, h, Module.End.mul_apply]
  by_cases hab : ε a = ε b
  · rw [if_pos hab.symm, if_pos hab]; simp; ring
  · rw [if_neg (fun h' => hab h'.symm), if_neg hab]; simp

open Finset in
open scoped InnerProductSpace in
private lemma mul_sq_sqrt_sub_le_sq_div_sixteen {n : ℕ} (μ U T ρ L : Fin n → ℝ) (K c bv : ℝ) (j : ℕ)
    (hμ : ∀ a, |μ a| ≤ 3 * bv) (hU : ∀ a, |U a| ≤ n) (hT : ∀ a, |T a| ≤ n)
    (hρ : ∀ a, |ρ a| ≤ n) (hL : ∀ a, L a = μ a + U a - T a)
    (hK : K = ∑ a, (μ a + U a) ^ 2 - ∑ a, T a ^ 2) (hc : c = ∑ a, μ a ^ 2 - ∑ a, ρ a ^ 2)
    (hn : (2 : ℝ) ≤ n) (hbv : 10 ^ 6 * (n : ℝ) ^ 7 ≤ bv) (hj : (j : ℝ) ≤ 4 * (n : ℝ) ^ 2 + 2) :
    (n : ℝ) * (2 * (√K + 4 * n * j) ^ 2 - c - (∑ a, L a ^ 2 - 8 * bv * j)) ≤ (bv / 16) ^ 2 := by
  have hN1 : (1 : ℝ) ≤ n := by linarith
  have hN0 : (0 : ℝ) ≤ n := by linarith
  have hJ0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h7 : ∀ k ≤ 7, (n : ℝ) ^ k ≤ (n : ℝ) ^ 7 := fun k hk => pow_le_pow_right₀ hN1 hk
  have hn7 : (1 : ℝ) ≤ (n : ℝ) ^ 7 := one_le_pow₀ hN1
  have hn2 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hbv1 : 30 * (n : ℝ) ^ 2 ≤ bv := by linarith [h7 2 (by norm_num)]
  have hnb : (n : ℝ) ≤ bv := by linarith [h7 1 (by norm_num), pow_one (n : ℝ)]
  have hbv0 : 0 ≤ bv := by linarith
  have hbvone : 1 ≤ bv := by linarith
  have hJ5 : (j : ℝ) ≤ 5 * (n : ℝ) ^ 2 := by linarith
  have hT2 : 0 ≤ ∑ a, T a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hA2 : 0 ≤ ∑ a, (μ a + U a) ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hAbound : ∑ a, (μ a + U a) ^ 2 ≤ (4 * n * bv) ^ 2 := by
    calc ∑ a, (μ a + U a) ^ 2 ≤ ∑ _a : Fin n, (4 * bv) ^ 2 := by
          refine Finset.sum_le_sum fun a _ => ?_
          have h1 : |μ a + U a| ≤ 4 * bv :=
            (abs_add_le _ _).trans (by linarith [hμ a, hU a])
          calc (μ a + U a) ^ 2 = |μ a + U a| ^ 2 := (sq_abs _).symm
            _ ≤ (4 * bv) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (n : ℝ) * (4 * bv) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (4 * n * bv) ^ 2 := by
          have := mul_le_mul_of_nonneg_right hnsq (sq_nonneg (4 * bv))
          linarith
  have hsq : √K ^ 2 ≤ K + ∑ a, T a ^ 2 := by
    rcases le_or_gt 0 K with h | h
    · rw [Real.sq_sqrt h]; linarith
    · rw [Real.sqrt_eq_zero'.mpr h.le, hK]; norm_num; linarith
  have hsqrt : √K ≤ 4 * n * bv := by
    calc √K ≤ √((4 * n * bv) ^ 2) := Real.sqrt_le_sqrt (by rw [hK]; linarith)
      _ = 4 * n * bv := Real.sqrt_sq (by positivity)
  have hsqrt0 : 0 ≤ √K := Real.sqrt_nonneg _
  have hpt : ∀ a, 2 * (μ a + U a) ^ 2 - μ a ^ 2 + ρ a ^ 2 - (μ a + U a - T a) ^ 2
      ≤ 12 * n * bv + 4 * (n : ℝ) ^ 2 := by
    intro a
    have e1 : μ a * U a ≤ 3 * bv * n := (le_abs_self _).trans
      (by rw [abs_mul]; exact mul_le_mul (hμ a) (hU a) (abs_nonneg _) (by linarith))
    have e2 : μ a * T a ≤ 3 * bv * n := (le_abs_self _).trans
      (by rw [abs_mul]; exact mul_le_mul (hμ a) (hT a) (abs_nonneg _) (by linarith))
    have e3 : U a * T a ≤ n * n := (le_abs_self _).trans
      (by rw [abs_mul]; exact mul_le_mul (hU a) (hT a) (abs_nonneg _) hN0)
    have e4 : U a ^ 2 ≤ (n : ℝ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hU a) 2
    have e5 : ρ a ^ 2 ≤ (n : ℝ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hρ a) 2
    linarith [sq_nonneg (T a)]
  have hsumid : 2 * K + 2 * ∑ a, T a ^ 2 - c - ∑ a, L a ^ 2
      = ∑ a, (2 * (μ a + U a) ^ 2 - μ a ^ 2 + ρ a ^ 2 - (μ a + U a - T a) ^ 2) := by
    rw [hK, hc]
    simp only [hL, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hsumle : ∑ a, (2 * (μ a + U a) ^ 2 - μ a ^ 2 + ρ a ^ 2 - (μ a + U a - T a) ^ 2)
      ≤ (n : ℝ) * (12 * n * bv + 4 * (n : ℝ) ^ 2) := by
    calc _ ≤ ∑ _a : Fin n, (12 * n * bv + 4 * (n : ℝ) ^ 2) := Finset.sum_le_sum fun a _ => hpt a
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcross : 16 * n * j * √K ≤ 16 * n * j * (4 * n * bv) :=
    mul_le_mul_of_nonneg_left hsqrt (by positivity)
  have hX : 2 * (√K + 4 * n * j) ^ 2 - c - (∑ a, L a ^ 2 - 8 * bv * j)
      ≤ (n : ℝ) * (12 * n * bv + 4 * (n : ℝ) ^ 2) + 64 * (n : ℝ) ^ 2 * j * bv
        + 32 * (n : ℝ) ^ 2 * (j : ℝ) ^ 2 + 8 * bv * j := by
    linarith [hsq, hsumid, hsumle, hcross]
  have b1 : 64 * (n : ℝ) ^ 2 * j * bv ≤ 320 * (n : ℝ) ^ 4 * bv := by
    have := mul_le_mul_of_nonneg_left hJ5 (by positivity : (0 : ℝ) ≤ 64 * (n : ℝ) ^ 2 * bv)
    linarith
  have b2 : 32 * (n : ℝ) ^ 2 * (j : ℝ) ^ 2 ≤ 800 * (n : ℝ) ^ 6 := by
    have h1 : (j : ℝ) ^ 2 ≤ (5 * (n : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ hJ0 hJ5 2
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 32 * (n : ℝ) ^ 2)
    linarith
  have b3 : 8 * bv * j ≤ 40 * (n : ℝ) ^ 2 * bv := by
    have := mul_le_mul_of_nonneg_left hJ5 hbv0
    linarith
  have hX' : 2 * (√K + 4 * n * j) ^ 2 - c - (∑ a, L a ^ 2 - 8 * bv * j)
      ≤ 52 * (n : ℝ) ^ 2 * bv + 4 * (n : ℝ) ^ 3 + 320 * (n : ℝ) ^ 4 * bv
        + 800 * (n : ℝ) ^ 6 := by linarith
  have c1 : (n : ℝ) ^ 3 * bv ≤ (n : ℝ) ^ 7 * bv :=
    mul_le_mul_of_nonneg_right (h7 3 (by norm_num)) hbv0
  have c2 : (n : ℝ) ^ 5 * bv ≤ (n : ℝ) ^ 7 * bv :=
    mul_le_mul_of_nonneg_right (h7 5 (by norm_num)) hbv0
  have c3 : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 7 := h7 4 (by norm_num)
  have c4 : (n : ℝ) ^ 7 ≤ (n : ℝ) ^ 7 * bv := le_mul_of_one_le_right (by positivity) hbvone
  have c6 : (n : ℝ) ^ 6 ≤ (n : ℝ) ^ 7 := h7 6 (by norm_num)
  have c5 : 10 ^ 6 * (n : ℝ) ^ 7 * bv ≤ bv * bv := mul_le_mul_of_nonneg_right hbv hbv0
  calc (n : ℝ) * (2 * (√K + 4 * n * j) ^ 2 - c - (∑ a, L a ^ 2 - 8 * bv * j))
      ≤ (n : ℝ) * (52 * (n : ℝ) ^ 2 * bv + 4 * (n : ℝ) ^ 3 + 320 * (n : ℝ) ^ 4 * bv
        + 800 * (n : ℝ) ^ 6) := mul_le_mul_of_nonneg_left hX' hN0
    _ = 52 * ((n : ℝ) ^ 3 * bv) + 4 * (n : ℝ) ^ 4 + 320 * ((n : ℝ) ^ 5 * bv)
        + 800 * (n : ℝ) ^ 7 := by ring
    _ ≤ (bv / 16) ^ 2 := by linarith


open Finset in
open scoped InnerProductSpace in
theorem _root_.GlobalTheory.lev_offDiag_normSq_le : ∀ (M : Type) [NormedAddCommGroup M]
    [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M)
    (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), _root_.BranchingSupport.IsMod ε E μ →
    _root_.BranchingSupport.Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 →
    _root_.BranchingSupport.Lev ε E μ j w →
    (n : ℝ) * ∑ a, ∑ b ∈ univ.erase a, ‖E a b w‖ ^ 2 ≤ (bv / 16) ^ 2 * ‖w‖ ^ 2 := by
  intro M _ _ n ε E μ kk j bv w hmod hshape hj hlev
  unfold _root_.BranchingSupport.IsMod at hmod
  obtain ⟨-, hE, hcas⟩ := hmod
  unfold _root_.BranchingSupport.Lev _root_.BranchingSupport.CasKLe at hlev
  obtain ⟨⟨S, -, -, hwS, hS⟩, hnear⟩ := hlev
  unfold _root_.BranchingSupport.Shape at hshape
  obtain ⟨hkk1, hkkn, -, hlow, hhigh, hbv⟩ := hshape
  have hn : 2 ≤ n := by omega
  have hNR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hN7 : (1 : ℝ) ≤ (n : ℝ) ^ 7 := one_le_pow₀ (by linarith)
  have hbv0 : 0 ≤ bv := by linarith
  have hnb : 2 * (n : ℝ) ≤ bv := by
    have : (n : ℝ) ≤ (n : ℝ) ^ 7 := by
      calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (n : ℝ) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  have hμ : ∀ a, |μ a| ≤ 3 * bv := by
    intro a
    rcases lt_or_ge ((a : ℕ) + 1) kk with h | h
    · obtain ⟨-, h1, h2⟩ := hlow a h
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨h1, h2⟩ := hhigh a h
      rw [abs_le]; constructor <;> linarith
  have hU : ∀ a, |_root_.Formalism.REAL.rhoN ε a| ≤ n := fun a => by
    unfold _root_.Formalism.REAL.rhoN; exact abs_half_card_sub_le _ _
  have hT : ∀ a, |_root_.Formalism.REAL.rhoC ε a| ≤ n := fun a => by
    unfold _root_.Formalism.REAL.rhoC; exact abs_half_card_sub_le _ _
  have hρ : ∀ a, |_root_.Formalism.QuantumDeterminants.rhoStd n a| ≤ n := by
    intro a
    unfold _root_.Formalism.QuantumDeterminants.rhoStd
    have ha : ((a : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast a.isLt
    have ha0 : (0 : ℝ) ≤ ((a : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [abs_le]; constructor <;> linarith
  have hLeq : ∀ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a = μ a + _root_.Formalism.REAL.rhoN ε a - _root_.Formalism.REAL.rhoC ε a := fun a => by
    unfold _root_.Formalism.QuantumDeterminants.lowK; simp
  have hLb : ∀ a, |_root_.Formalism.QuantumDeterminants.lowK ε μ a| ≤ 4 * bv := by
    intro a
    have h1 := hμ a; have h2 := hU a; have h3 := hT a
    rw [hLeq]; rw [abs_le] at h1 h2 h3 ⊢; constructor <;> linarith
  have hm : ∀ ω : Fin n → ℝ, ∑ a, |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a| ≤ (j : ℝ) →
      ∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * j ≤ ∑ a, ω a ^ 2 := by
    intro ω hω
    have hpt : ∀ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a| ≤ ω a ^ 2 := by
      intro a
      have h1 := neg_abs_le (_root_.Formalism.QuantumDeterminants.lowK ε μ a * (ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a))
      rw [abs_mul] at h1
      have h2 : |_root_.Formalism.QuantumDeterminants.lowK ε μ a| * |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a| ≤ 4 * bv * |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a| :=
        mul_le_mul_of_nonneg_right (hLb a) (abs_nonneg _)
      linarith [sq_nonneg (ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a)]
    calc ∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * j
        ≤ ∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * ∑ a, |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a| := by
          have := mul_le_mul_of_nonneg_left hω hbv0
          linarith
      _ = ∑ a, (_root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * |ω a - _root_.Formalism.QuantumDeterminants.lowK ε μ a|) := by
          rw [Finset.mul_sum, Finset.sum_sub_distrib]
      _ ≤ ∑ a, ω a ^ 2 := Finset.sum_le_sum fun a _ => hpt a
  have hdiag : (∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * j) * ‖w‖ ^ 2 ≤ ∑ a, ‖E a a w‖ ^ 2 :=
    (_root_.GlobalTheory.wtNear_diag_bounds M n ε E (_root_.Formalism.QuantumDeterminants.lowK ε μ) (j : ℝ) w hE hnear).1 _ hm
  have hΩ : (⟪w, _root_.Formalism.REAL.Cas E w⟫_ℂ).re = _root_.BranchingSupport.casG μ * ‖w‖ ^ 2 := by
    rw [hcas w, inner_smul_right, inner_self_eq_norm_sq_to_K]
    norm_cast
    rw [Complex.re_ofReal_mul]
    congr 1
  have hKc := hS w hwS
  have hsum : ∑ a, ∑ b, ‖E a b w‖ ^ 2
      = 2 * (⟪w, _root_.Formalism.REAL.CasK ε E w⟫_ℂ).re - (⟪w, _root_.Formalism.REAL.Cas E w⟫_ℂ).re := by
    rw [Finset.sum_comm]
    unfold _root_.Formalism.REAL.CasK _root_.Formalism.REAL.Cas
    rw [re_inner_double_sum_apply, re_inner_double_sum_apply, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [norm_sq_apply_eq_re_inner_of_isUnitary hE a b w]
    split_ifs <;> simp
  have hoff : ∑ a, ∑ b ∈ univ.erase a, ‖E a b w‖ ^ 2
      = ∑ a, ∑ b, ‖E a b w‖ ^ 2 - ∑ a, ‖E a a w‖ ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_erase_eq_sub (Finset.mem_univ a)
  have hKeq : _root_.Formalism.REAL.ckv ε (_root_.Formalism.QuantumDeterminants.lowK ε μ)
      = ∑ a, (μ a + _root_.Formalism.REAL.rhoN ε a) ^ 2 - ∑ a, _root_.Formalism.REAL.rhoC ε a ^ 2 := by
    unfold _root_.Formalism.REAL.ckv _root_.Formalism.REAL.nsq _root_.Formalism.REAL.dot _root_.Formalism.QuantumDeterminants.lowK
    simp only [Pi.add_apply, Pi.sub_apply, sub_add_cancel, sq]
  have hceq : _root_.BranchingSupport.casG μ = ∑ a, μ a ^ 2 - ∑ a, _root_.Formalism.QuantumDeterminants.rhoStd n a ^ 2 := by
    unfold _root_.BranchingSupport.casG; rfl
  have hj' : (j : ℝ) ≤ 4 * (n : ℝ) ^ 2 + 2 := by exact_mod_cast hj
  have hnum := mul_sq_sqrt_sub_le_sq_div_sixteen μ (_root_.Formalism.REAL.rhoN ε) (_root_.Formalism.REAL.rhoC ε) (fun a => _root_.Formalism.QuantumDeterminants.rhoStd n a)
    (_root_.Formalism.QuantumDeterminants.lowK ε μ) (_root_.Formalism.REAL.ckv ε (_root_.Formalism.QuantumDeterminants.lowK ε μ)) (_root_.BranchingSupport.casG μ) bv j hμ hU hT hρ
    hLeq hKeq hceq hNR hbv hj'
  have hw2 : 0 ≤ ‖w‖ ^ 2 := by positivity
  have hoff_le : ∑ a, ∑ b ∈ univ.erase a, ‖E a b w‖ ^ 2
      ≤ (2 * (√(_root_.Formalism.REAL.ckv ε (_root_.Formalism.QuantumDeterminants.lowK ε μ)) + 4 * n * j) ^ 2 - _root_.BranchingSupport.casG μ
        - (∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * j)) * ‖w‖ ^ 2 := by
    rw [hoff, hsum, hΩ]
    linarith [hKc, hdiag]
  calc (n : ℝ) * ∑ a, ∑ b ∈ univ.erase a, ‖E a b w‖ ^ 2
      ≤ (n : ℝ) * ((2 * (√(_root_.Formalism.REAL.ckv ε (_root_.Formalism.QuantumDeterminants.lowK ε μ)) + 4 * n * j) ^ 2
        - _root_.BranchingSupport.casG μ - (∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * j)) * ‖w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hoff_le (Nat.cast_nonneg n)
    _ = (n : ℝ) * (2 * (√(_root_.Formalism.REAL.ckv ε (_root_.Formalism.QuantumDeterminants.lowK ε μ)) + 4 * n * j) ^ 2
        - _root_.BranchingSupport.casG μ - (∑ a, _root_.Formalism.QuantumDeterminants.lowK ε μ a ^ 2 - 8 * bv * j)) * ‖w‖ ^ 2 := by
        ring
    _ ≤ (bv / 16) ^ 2 * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right hnum hw2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelOffDiagNormSqLeStatement
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGlModule_level_offDiag_normSq_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → Lev ε E μ j w → (n : ℝ) * ∑ a, ∑ b ∈ univ.erase a, ‖E a b w‖ ^ 2 ≤ (bv / 16) ^ 2 * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.lev_offDiag_normSq_le | exact GlobalTheory.lev_offDiag_normSq_le | (intros; apply GlobalTheory.lev_offDiag_normSq_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModel
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModel
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology UpperHalfPlane

namespace GlobalTheory.MomOne

theorem model_norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  let S : Subring ℂ_[q] := (NormedField.valuation (K := ℂ_[q])).integer
  have hS := Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))
  have h1 : IsIntegral S x := hx.tower_top
  have h2 := hS.mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem model_isIntegral_j {d : ℕ} (hd : d ≠ 0) {L : PeriodPair} (hL : IsOK d L) :
    IsIntegral ℤ (GlobalTheory.latticeCurve L).j := by
  have hw : ((GlobalTheory.halfOneAddSqrtNeg d hd : ℍ) : ℂ) = wK d := by
    change (1 + √d * Complex.I) / 2 = _
    rw [wK]; ring
  rw [GlobalTheory.latticeCurve_j (a := 1) (τ := GlobalTheory.halfOneAddSqrtNeg d hd) one_ne_zero]
  · exact GlobalTheory.isIntegral_modularJ_halfOneAddSqrtNeg d hd
  · intro x
    rw [hL x, hw]
    constructor
    · rintro ⟨u, v, rfl⟩
      exact ⟨v, u, by ring⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by ring⟩

theorem exists_model : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (L : PeriodPair), d.Prime → d % 16 = 7 → IsOK d L → ∃ M : Mdl q, M.ι = ι ∧ M.L = L ∧ M.Ok ∧ IsAlgebraic ℚ M.W.a₁ ∧ IsAlgebraic ℚ M.W.a₂ ∧ IsAlgebraic ℚ M.W.a₃ ∧ IsAlgebraic ℚ M.W.a₄ ∧ IsAlgebraic ℚ M.W.a₆ := by
  intro d q _ ι L hd _ hL
  obtain ⟨E, h₁, h₂, h₃, h₄, h₆, hΔ, hc⟩ :=
    GlobalTheory.CMCurves.exists_integral_curve (model_isIntegral_j hd.ne_zero hL)
  have hE : E.IsElliptic := ⟨hΔ ▸ isUnit_one⟩
  have hj : (GlobalTheory.latticeCurve L).j = E.j := by
    rw [← hc, WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', hΔ]
    simp
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ _ hj
  have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  have e4 : E.c₄ / 12 = L.g₂ / (C.u : ℂ) ^ 4 := by
    rw [← hC, WeierstrassCurve.variableChange_c₄, GlobalTheory.latticeCurve_c₄, Units.val_inv_eq_inv_val]
    field_simp
  have e6 : E.c₆ / 216 = L.g₃ / (C.u : ℂ) ^ 6 := by
    have : (GlobalTheory.latticeCurve L).c₆ = 216 * L.g₃ := by
      simp only [GlobalTheory.latticeCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆]
      ring
    rw [← hC, WeierstrassCurve.variableChange_c₆, this, Units.val_inv_eq_inv_val]
    field_simp
  have hi : ∀ {x : ℂ}, IsIntegral ℤ x → IsIntegral ℤ ((ι : ℂ →+* ℂ_[q]) x) := fun hx ↦
    hx.map_of_comp_eq (RingHom.id ℤ) (ι : ℂ →+* ℂ_[q]) (RingHom.ext_int _ _)
  have ha : ∀ {x : ℂ}, IsIntegral ℤ x → IsAlgebraic ℚ ((ι : ℂ →+* ℂ_[q]) x) := fun hx ↦
    (IsIntegral.tower_top (A := ℚ) (hi hx)).isAlgebraic
  refine ⟨⟨ι, L, C.u, E.map (ι : ℂ →+* ℂ_[q])⟩, rfl, rfl,
    ⟨hu, model_norm_le_one_of_isIntegral (hi h₁), model_norm_le_one_of_isIntegral (hi h₂),
      model_norm_le_one_of_isIntegral (hi h₃), model_norm_le_one_of_isIntegral (hi h₄),
      model_norm_le_one_of_isIntegral (hi h₆), ?_, ?_, ?_⟩, ha h₁, ha h₂, ha h₃, ha h₄, ha h₆⟩
  · simp [WeierstrassCurve.map_Δ, hΔ]
  · change (E.map (ι : ℂ →+* ℂ_[q])).c₄ / 12 = ι (L.g₂ / (C.u : ℂ) ^ 4)
    rw [← e4, WeierstrassCurve.map_c₄, map_div₀, map_ofNat]
    rfl
  · change (E.map (ι : ℂ →+* ℂ_[q])).c₆ / 216 = ι (L.g₃ / (C.u : ℂ) ^ 6)
    rw [← e6, WeierstrassCurve.map_c₆, map_div₀, map_ofNat]
    rfl

end GlobalTheory.MomOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModelStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodReduction_algebraic_weierstrass_model : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (L : PeriodPair), d.Prime → d % 16 = 7 → IsOK d L → ∃ M : Mdl q, M.ι = ι ∧ M.L = L ∧ M.Ok ∧ IsAlgebraic ℚ M.W.a₁ ∧ IsAlgebraic ℚ M.W.a₂ ∧ IsAlgebraic ℚ M.W.a₃ ∧ IsAlgebraic ℚ M.W.a₄ ∧ IsAlgebraic ℚ M.W.a₆ := by
  first | exact @GlobalTheory.MomOne.exists_model | exact GlobalTheory.MomOne.exists_model | (intros; apply GlobalTheory.MomOne.exists_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRationalIsometryOfTraceIsometry
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix

namespace GlobalTheory.TraceIsometry

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open NumberField in
open scoped Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.TraceIsometry.eq_or_eq_neg_of_norm_eq {x y : E} (hx : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc x = -x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc y = -y)
    (h : ∀ τ : E →+* ℂ, ‖τ x‖ = ‖τ y‖) : y = x ∨ y = -x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hre : ∀ z : E, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc z = -z → (τ z).re = 0 := by
    intro z hz
    have h1 := _root_.GlobalTheory.PerMove.map_cc τ z
    rw [hz, map_neg] at h1
    have h2 := congrArg Complex.re h1
    simp only [Complex.neg_re, Complex.conj_re] at h2
    linarith
  have hxr := hre x hx
  have hyr := hre y hy
  have key : (τ y).im = (τ x).im ∨ (τ y).im = -(τ x).im := by
    have h2 : ‖τ x‖ ^ 2 = ‖τ y‖ ^ 2 := by rw [h τ]
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hxr,
      hyr] at h2
    exact mul_self_eq_mul_self_iff.mp (by linarith)
  rcases key with k | k
  · left
    apply τ.injective
    apply Complex.ext <;> simp [hxr, hyr, k]
  · right
    apply τ.injective
    rw [map_neg]
    apply Complex.ext <;> simp [hxr, hyr, k]


open NumberField in
open scoped Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (X X' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) →
    ∀ (gam : X.Λ ≃ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm
    (gam u : Fin r → E) (gam v : Fin r → E)) = Algebra.trace ℚ E (-X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm
    (u : Fin r → E) (v : Fin r → E))) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧
    X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) =
    (gam v : Fin r → E)) ∧ (∀ v, v ∈ X.Λ ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ X'.Λ) ∧
    ∀ u v, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u)
    ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v := by
  intro E _ _ _ r X X' hξ gam hgam
  obtain ⟨ε, hε1, hεξ⟩ : ∃ ε : E, (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 := by
    rcases _root_.GlobalTheory.TraceIsometry.eq_or_eq_neg_of_norm_eq X.ξ0_im X'.ξ0_im hξ with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_mul]⟩
  have hsp : ∀ Y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r, Submodule.span E (Set.range Y.Λ.subtype) = ⊤ := by
    intro Y
    have : Set.range Y.Λ.subtype = (Y.Λ : Set (Fin r → E)) := by ext; simp
    rw [this]
    exact Y.Λ_span
  obtain ⟨A, hA⟩ := _root_.GlobalTheory.FrameFibre.exists_matrix X.Λ.subtype
    Subtype.val_injective (hsp X) (X'.Λ.subtype ∘ₗ gam.toLinearMap)
  obtain ⟨B, hB⟩ := _root_.GlobalTheory.FrameFibre.exists_matrix X'.Λ.subtype
    Subtype.val_injective (hsp X') (X.Λ.subtype ∘ₗ gam.symm.toLinearMap)
  have hA' : ∀ v : X.Λ, A *ᵥ (v : Fin r → E) = (gam v : Fin r → E) := fun v => hA v
  have hB' : ∀ w : X'.Λ, B *ᵥ (w : Fin r → E) = (gam.symm w : Fin r → E) := fun w => hB w
  have hBA : B * A = 1 := by
    have hlin : Matrix.mulVecLin (B * A) = LinearMap.id := by
      apply LinearMap.ext_on X.Λ_span
      intro v hv
      simp only [Matrix.mulVecLin_apply, LinearMap.id_apply]
      rw [← Matrix.mulVec_mulVec, show A *ᵥ v = _ from hA' ⟨v, hv⟩, hB']
      simp
    apply Matrix.ext_of_mulVec_single
    intro i
    have h1 := LinearMap.congr_fun hlin (Pi.single i 1)
    simp only [Matrix.mulVecLin_apply, LinearMap.id_apply] at h1
    rw [h1, Matrix.one_mulVec]
  have hsm : ∀ (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (x y : Fin r → E),
      _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (c • x) y = (c : E) * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y := by
    intro G c x y
    have h1 := _root_.GlobalTheory.FrameFibre.herm_smul_smul G (c : E) 1 x y
    rw [one_smul, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc_one, mul_one] at h1
    rw [← h1]
    rfl
  have hL : ∀ u v : X.Λ, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) =
      ε * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v := by
    intro u v
    have hD : -X'.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm (gam u) (gam v) - -X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v = 0 := by
      apply _root_.GlobalTheory.FrameFibre.eq_zero_of_trace
      intro c
      have h1 := hgam (c • u) v
      rw [LinearEquiv.map_smul, Submodule.coe_smul, Submodule.coe_smul, hsm, hsm] at h1
      rw [mul_sub, map_sub, sub_eq_zero, mul_left_comm (c : E), mul_left_comm (c : E)]
      exact h1
    rw [hεξ, ← hA' u, ← hA' v] at hD
    have hε2 : ε * ε = 1 := by rcases hε1 with h | h <;> rw [h] <;> ring
    apply mul_left_cancel₀ X.ξ0_ne
    linear_combination (-ε) * hD -
      X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) * hε2
  have hall : ∀ u v : Fin r → E, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm (A *ᵥ u) (A *ᵥ v) = ε * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v := by
    intro u v
    obtain ⟨c, u', hc, hu'⟩ := _root_.GlobalTheory.FrameFibre.exists_smul_eq X.Λ.subtype (hsp X) u
    obtain ⟨d, v', hd, hv'⟩ := _root_.GlobalTheory.FrameFibre.exists_smul_eq X.Λ.subtype (hsp X) v
    have h1 := hL u' v'
    have hu'' : (u' : Fin r → E) = (c : E) • u := hu'.symm
    have hv'' : (v' : Fin r → E) = (d : E) • v := hv'.symm
    rw [hu'', hv'', Matrix.mulVec_smul, Matrix.mulVec_smul, _root_.GlobalTheory.FrameFibre.herm_smul_smul,
      _root_.GlobalTheory.FrameFibre.herm_smul_smul] at h1
    have hc' : (c : E) ≠ 0 := by exact_mod_cast hc
    have hd' : (d : E) ≠ 0 := by exact_mod_cast hd
    have hcc : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (d : E) ≠ 0 := by
      intro h0
      apply hd'
      rw [← _root_.ReciprocityTheory.ChartRestriction.G.FD.cc_cc (d : E), h0, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc_zero]
    apply mul_left_cancel₀ (mul_ne_zero hc' hcc)
    linear_combination h1
  refine ⟨⟨A, B, (mul_eq_one_comm.mp hBA), hBA⟩, ε, hε1, hεξ, hA', ?_, hall⟩
  intro v
  change v ∈ X.Λ ↔ A *ᵥ v ∈ X'.Λ
  constructor
  · intro hv
    rw [show A *ᵥ v = _ from hA' ⟨v, hv⟩]
    exact (gam ⟨v, hv⟩).2
  · intro hv
    have h1 : B *ᵥ (A *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
    rw [← h1, show B *ᵥ (A *ᵥ v) = _ from hB' ⟨A *ᵥ v, hv⟩]
    exact (gam.symm _).2

end GlobalTheory.TraceIsometry
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelSumNormSqLe
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelSumNormSqLe
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem lev_gl_size : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv b : ℝ) (w : M),
    IsMod ε E μ → Shape ε kk μ bv → bv ≤ b → j ≤ 4 * n ^ 2 → Lev ε E μ j w →
    ∑ a, ∑ c, ‖E a c w‖ ^ 2 ≤ b ^ 4 * ‖w‖ ^ 2 := by
  intro M _ _ n ε E μ kk j bv b w hM hS hb hj hL
  have hj' : j ≤ 4 * n ^ 2 + 2 := by omega
  obtain ⟨hbv, hpos, -⟩ := GlobalTheory.shape_position n kk j ε μ bv hS hj'
  have hoff := GlobalTheory.T.unitaryGlModule_level_offDiag_normSq_le M n ε E μ kk j bv w hM hS hj' hL
  have hdiag := (GlobalTheory.T.weightNear_diagonalOperators_bounds M n ε E (lowK ε μ) (j : ℝ) w hM.2.1 hL.2).2.2
  have hd : ∀ a, ‖E a a w‖ ^ 2 ≤ (3 * bv) ^ 2 * ‖w‖ ^ 2 := by
    intro a
    refine hdiag a (3 * bv) ?_
    intro ω hω
    obtain ⟨h1, h2⟩ := hpos ω hω a
    rw [abs_le]
    by_cases h : a.val + 1 < kk
    · obtain ⟨h3, h4⟩ := h1 h
      constructor <;> linarith
    · obtain ⟨h3, h4⟩ := h2 (by omega)
      constructor <;> linarith
  have hn : (1 : ℝ) ≤ n := by
    have := hS.1
    have := hS.2.1
    exact_mod_cast (by omega : 1 ≤ n)
  have hbig : 10 ^ 6 * (n : ℝ) ^ 7 ≤ bv := hS.2.2.2.2.2
  have hsplit : ∑ a, ∑ c, ‖E a c w‖ ^ 2
      = ∑ a, ‖E a a w‖ ^ 2 + ∑ a, ∑ c ∈ univ.erase a, ‖E a c w‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact (Finset.add_sum_erase univ (fun c => ‖E a c w‖ ^ 2) (Finset.mem_univ a)).symm
  have hsum : ∑ a, ‖E a a w‖ ^ 2 ≤ n * ((3 * bv) ^ 2 * ‖w‖ ^ 2) := by
    calc ∑ a, ‖E a a w‖ ^ 2 ≤ ∑ _a : Fin n, (3 * bv) ^ 2 * ‖w‖ ^ 2 := Finset.sum_le_sum fun a _ => hd a
      _ = n * ((3 * bv) ^ 2 * ‖w‖ ^ 2) := by simp
  have hO : 0 ≤ ∑ a, ∑ c ∈ univ.erase a, ‖E a c w‖ ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun c _ => sq_nonneg _
  have hO' : ∑ a, ∑ c ∈ univ.erase a, ‖E a c w‖ ^ 2 ≤ (bv / 16) ^ 2 * ‖w‖ ^ 2 :=
    le_trans (le_mul_of_one_le_left hO hn) hoff
  have hn7 : (n : ℝ) ≤ (n : ℝ) ^ 7 := le_self_pow₀ hn (by norm_num)
  have hb1 : 10 ^ 6 * (n : ℝ) ≤ bv := by linarith
  have hb2 : 9 * (n : ℝ) + 1 ≤ bv ^ 2 := by nlinarith
  have hb4 : bv ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ hbv.le hb 4
  have hc : (n : ℝ) * (3 * bv) ^ 2 + (bv / 16) ^ 2 ≤ b ^ 4 := by
    have h1 : (9 * (n : ℝ) + 1) * bv ^ 2 ≤ bv ^ 2 * bv ^ 2 := mul_le_mul_of_nonneg_right hb2 (sq_nonneg _)
    nlinarith [sq_nonneg bv]
  have := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖w‖)
  rw [hsplit]
  nlinarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelSumNormSqLeStatement
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGlModule_level_sum_norm_sq_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv b : ℝ) (w : M), IsMod ε E μ → Shape ε kk μ bv → bv ≤ b → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∑ a, ∑ c, ‖E a c w‖ ^ 2 ≤ b ^ 4 * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.lev_gl_size | exact GlobalTheory.lev_gl_size | (intros; apply GlobalTheory.lev_gl_size <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DomSubsetClosureIsGenFrame
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open Cardinal Topology

namespace GlobalTheory.GenFrame

theorem subset_closure_forall_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {J : Type*} [Countable J] (f : J → E → ℂ) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (hne : ∀ j, ∃ x ∈ U, f j x ≠ 0) : U ⊆ closure {x | x ∈ U ∧ ∀ j, f j x ≠ 0} := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  set W : J → Set E := fun j => (U ∩ f j ⁻¹' {0}ᶜ) ∪ (closure U)ᶜ with hW
  have hWo : ∀ j, IsOpen (W j) := fun j =>
    ((hf j).continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton).union
      isClosed_closure.isOpen_compl
  have hWd : ∀ j, Dense (W j) := by
    intro j
    rw [dense_iff_inter_open]
    intro O hO hOne
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hnot : ∀ y ∈ O, y ∉ W j := fun y hy hyW => by
      have : y ∈ O ∩ W j := ⟨hy, hyW⟩
      rw [hemp] at this
      exact this
    obtain ⟨y, hy⟩ := hOne
    have hyc : y ∈ closure U := by
      by_contra h
      exact hnot y hy (Or.inr h)
    obtain ⟨z, hzO, hzU⟩ := mem_closure_iff.mp hyc O hO hy
    have hz := GlobalTheory.SCV.eqOn_of_eqOn_open (g := fun _ => (0 : ℂ)) hU hc (hf j)
      (differentiableOn_const 0) (hO.inter hU) ⟨z, hzO, hzU⟩ Set.inter_subset_right
      (fun w hw => by
        by_contra h
        exact hnot w hw.1 (Or.inl ⟨hw.2, h⟩))
    obtain ⟨x, hx, hx0⟩ := hne j
    exact hx0 (hz hx)
  have hD := dense_iInter_of_isOpen hWo hWd
  refine (hD.open_subset_closure_inter hU).trans (closure_mono ?_)
  rintro x ⟨hxU, hx⟩
  refine ⟨hxU, fun j => ?_⟩
  rcases Set.mem_iInter.mp hx j with h | h
  · exact h.2
  · exact absurd (subset_closure hxU) h

end GlobalTheory.GenFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirOffDiagonalNormSqLeOfLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirOffDiagonalNormSqLeOfLevel
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem norm_sum_sq_le_fin_mul {M : Type} [NormedAddCommGroup M] {n : ℕ} (s : Finset (Fin n)) (v : Fin n → M) :
    ‖∑ c ∈ s, v c‖ ^ 2 ≤ (n : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2 := by
  have h1 : ‖∑ c ∈ s, v c‖ ≤ ∑ c ∈ s, ‖v c‖ := norm_sum_le _ _
  have h2 : (∑ c ∈ s, ‖v c‖) ^ 2 ≤ (s.card : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : (s.card : ℝ) ≤ n := by
    have := card_le_univ s
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have h4 : 0 ≤ ∑ c ∈ s, ‖v c‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  calc ‖∑ c ∈ s, v c‖ ^ 2 ≤ (∑ c ∈ s, ‖v c‖) ^ 2 := by gcongr
    _ ≤ (s.card : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2 := h2
    _ ≤ (n : ℝ) * ∑ c ∈ s, ‖v c‖ ^ 2 := mul_le_mul_of_nonneg_right h3 h4

theorem offDiagPart_sq_le_of_lev : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ)
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M),
    IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) →
      ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by
  intro M _ _ n ε E μ kk j bv x hmod hsh hj hlev

  have step1 : ∀ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤
      (n : ℝ) * ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2 :=
    fun b => norm_sum_sq_le_fin_mul _ _
  have swap : ∑ b, ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2 =
      ∑ c, ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2 :=
    Finset.sum_comm' (fun b c => by
      simp only [mem_univ, mem_erase, true_and, and_true]
      exact ne_comm)
  have step2 : ∀ c, (n : ℝ) * ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2 ≤
      (bv / 16) ^ 2 * ‖x c‖ ^ 2 := by
    intro c
    refine le_trans ?_ (lev_offDiag_normSq_le M n ε E μ kk j bv (x c) hmod hsh hj (hlev c))
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
    calc ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2
        ≤ ∑ b ∈ univ.erase c, ∑ b' ∈ univ.erase b, ‖E b b' (x c)‖ ^ 2 := by
          refine sum_le_sum fun b hb => ?_
          have hcb : c ∈ univ.erase b :=
            mem_erase.2 ⟨fun h => (mem_erase.1 hb).1 h.symm, mem_univ _⟩
          exact single_le_sum (f := fun b' => ‖E b b' (x c)‖ ^ 2) (fun _ _ => sq_nonneg _) hcb
      _ ≤ ∑ b, ∑ b' ∈ univ.erase b, ‖E b b' (x c)‖ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
            fun _ _ _ => sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2
      ≤ ∑ b, (n : ℝ) * ∑ c ∈ univ.erase b, ‖E b c (x c)‖ ^ 2 := sum_le_sum fun b _ => step1 b
    _ = ∑ c, (n : ℝ) * ∑ b ∈ univ.erase c, ‖E b c (x c)‖ ^ 2 := by
      rw [← mul_sum, swap, mul_sum]
    _ ≤ ∑ c, (bv / 16) ^ 2 * ‖x c‖ ^ 2 := sum_le_sum fun c _ => step2 c
    _ = (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by rw [mul_sum]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirOffDiagonalNormSqLeOfLevelStatement
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitCasimir_offDiagonal_norm_sq_le_of_level : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by
  first | exact @GlobalTheory.offDiagPart_sq_le_of_lev | exact GlobalTheory.offDiagPart_sq_le_of_lev | (intros; apply GlobalTheory.offDiagPart_sq_le_of_lev <;> assumption)
end
end
