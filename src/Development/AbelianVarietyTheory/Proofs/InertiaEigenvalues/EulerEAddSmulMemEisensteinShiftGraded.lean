module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerEAddSmulMemEisensteinShiftGraded
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerEAddSmulMemEisensteinShiftGraded
noncomputable section

namespace GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
  {η H : ℕ}


omit [CompleteSpace K] in
theorem conn_mem_ext_Rpi (D : BKDat O K l e a ι η H) {y : Vec K a ι}
    (hy : y ∈ D.ext (Rpi O K l e)) : D.conn y ∈ D.ext (Rpi O K l e) := by
  have hf : ∀ i τ, (Matrix.mulVec (D.mxInv τ) (y τ)) i ∈ Rpi O K l e := fun i τ =>
    D.mem_extc_iff.1 (mem_tot.1 hy τ) i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [D.eq_sum_phi_bas y, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hL : D.phi (bas i) ∈ D.L := D.phi_mem_L (D.bas_mem_M i)
  have hM : D.phi (bas i) ∈ D.MM := D.ext_mono (A_le_S l e) hL
  rw [PhiMod.conn_smul_tot]
  refine Submodule.add_mem _ ?_ ?_
  · exact D.smul_tot_mem_ext (fun τ => N_mem (derivative_mem_R l (hf i τ)))
      (D.ext_mono (S_le_R l e) hM)
  · exact D.smul_tot_mem_ext (hf i) (D.ext_mono (S_le_R l e) (D.conn_mem_MM hM))

omit [CompleteSpace K] in
theorem EN_add_smul_mem_shiftE' (D : BKDat O K l e a ι η H) (j : ℤ) (x : Vec K a ι)
    (hx : x ∈ shiftE l e j (D.ext (Rpi O K l e))) :
    D.EN x + ((j * e * l : ℤ) : K) • x ∈ shiftE l e (j + 1) (D.ext (Rpi O K l e)) := by
  rw [mem_shiftE] at hx ⊢
  set y := Ezpow K l e (-j) • x with hy
  have hxy : x = Ezpow K l e j • y := by
    rw [hy, smul_smul, mul_comm, Ezpow_neg_mul, one_smul]
  clear_value y
  clear hy
  have h1 : Ezpow K l e (j + 1) = Ezpow K l e j * E K l e := by
    rw [Ezpow_add, show Ezpow K l e 1 = E K l e from (Ezpow_natCast l e 1).trans (pow_one _)]
  have hc : ((j * e * l : ℤ) : K) • x = ((j * e * l : ℤ) : K⟦X⟧) • x := by
    rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  have hN : E K l e * N K (Ezpow K l e j) + ((j * e * l : ℤ) : K⟦X⟧) * Ezpow K l e j =
      Ezpow K l e (j + 1) * ((j * e : ℤ) : K⟦X⟧) := by
    rw [E_mul_N_Ezpow, N_E, h1, E]
    push_cast
    ring
  have key : D.EN x + ((j * e * l : ℤ) : K) • x =
      Ezpow K l e (j + 1) • ((j * e : ℤ) • y + D.conn y) := by
    rw [hc, PhiMod.EN_apply, hxy, PhiMod.conn_smul, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
      ← Int.cast_smul_eq_zsmul K⟦X⟧ (j * e : ℤ), smul_smul, ← hN, add_smul, h1, mul_comm (E K l e) (Ezpow K l e j)]
    abel
  rw [key, smul_smul, Ezpow_neg_mul, one_smul]
  exact Submodule.add_mem _ (zsmul_mem hx _) (conn_mem_ext_Rpi D hx)

theorem EN_add_smul_mem_shiftE :
    ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (j : ℤ) (x : Vec K a ι), x ∈ shiftE l e j (D.ext (Rpi O K l e)) → D.EN x + ((j * e * l : ℤ) : K) • x ∈ shiftE l e (j + 1) (D.ext (Rpi O K l e)) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D j x hx
  exact EN_add_smul_mem_shiftE' D j x hx

end GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerEAddSmulMemEisensteinShiftGradedStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerE_add_smul_mem_eisenstein_shift_graded : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (j : ℤ) (x : Vec K a ι), x ∈ shiftE l e j (D.ext (Rpi O K l e)) → D.EN x + ((j * e * l : ℤ) : K) • x ∈ shiftE l e (j + 1) (D.ext (Rpi O K l e)) := by
  first | exact @GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded.EN_add_smul_mem_shiftE | exact GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded.EN_add_smul_mem_shiftE | (intros; apply GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded.EN_add_smul_mem_shiftE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsEqOfPowPredEqOfValOne
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace GlobalTheory

theorem eq_of_pow_pred_eq_of_sub_one_mem {R : Type*} [CommRing R] [IsDomain R] (I : Ideal R)
    (hI : I ≠ ⊤) (l : ℕ) (hl : 0 < l) (hlI : (l : R) ∈ I) (a b : R)
    (hab : a ^ (l - 1) = b ^ (l - 1)) (ha : a - 1 ∈ I) (hb : b - 1 ∈ I) : a = b := by
  by_contra hne
  have h := geom_sum₂_mul a b (l - 1)
  rw [hab, sub_self] at h
  have hs := (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hne)
  have ha' : Ideal.Quotient.mk I a = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact ha
  have hb' : Ideal.Quotient.mk I b = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hb
  have hl' : (l : R ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]; exact hlI
  have h2 := congrArg (Ideal.Quotient.mk I) hs
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, ha', hb', one_pow, mul_one, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, map_zero] at h2
  rw [Nat.cast_sub hl, hl', Nat.cast_one, zero_sub, neg_eq_zero] at h2
  apply hI
  rw [Ideal.eq_top_iff_one, ← Ideal.Quotient.eq_zero_iff_mem, map_one]
  exact h2

def posValIdeal {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) : Ideal ↥(OL LL) where
  carrier := {x | 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 x)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, (algebraMap ↥(OL LL) ↥LL.1).map_add] at ha hb ⊢
    exact (P.v LL).map_lt_add ha hb
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul, (algebraMap ↥(OL LL) ↥LL.1).map_mul,
      AddValuation.map_mul] at hx ⊢
    have hc : 0 ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 c) := (P.v_O LL _).2 c.2
    exact lt_of_lt_of_le hx (le_add_of_nonneg_left hc)

theorem oneUnit_eq_of_pow_pred_eq_of_pos {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (a b : ↥(OL LL)) (hab : a ^ (l - 1) = b ^ (l - 1))
    (ha : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 a - 1))
    (hb : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 b - 1)) : a = b := by
  refine eq_of_pow_pred_eq_of_sub_one_mem (posValIdeal P LL) ?_ l (Fact.out : l.Prime).pos ?_ a b
    hab ?_ ?_
  · rw [Ne, Ideal.eq_top_iff_one]
    change ¬ 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 1)
    simp
  · change 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL)))
    rw [map_natCast, P.v_l]
    exact zero_lt_one
  · change 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (a - 1))
    rwa [map_sub, map_one]
  · change 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (b - 1))
    rwa [map_sub, map_one]

theorem units_eq_of_pow_pred_eq_of_pos {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (u w : (↥(OL LL))ˣ) (h : u ^ (l - 1) = w ^ (l - 1))
    (hu : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (u : ↥(OL LL)) - 1))
    (hw : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)) - 1)) : u = w := by
  apply Units.ext
  refine oneUnit_eq_of_pow_pred_eq_of_pos P LL _ _ ?_ hu hw
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h]

theorem units_eq_of_pow_pred_eq_of_val_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (LL : FinExt l) (u w : (↥(OL LL))ˣ), u ^ (l - 1) = w ^ (l - 1) →
    P.v LL (algebraMap ↥(OL LL) ↥LL.1 ((u : ↥(OL LL)) - 1)) = 1 →
    P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)) - 1) = 1 → u = w := by
  intro l _ P LL u w h hu hw
  rw [map_sub, map_one] at hu
  refine units_eq_of_pow_pred_eq_of_pos P LL u w h ?_ ?_
  · rw [hu]; exact zero_lt_one
  · rw [hw]; exact zero_lt_one

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDivisibilityOfDescentDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDivisibilityOfDescentDatum
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.NgalDivisible

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

theorem l_pow_eq (n : ℕ) : ((l : K⟦X⟧)) ^ n =
    E K l e ^ n - (X : K⟦X⟧) ^ e * ∑ i ∈ Finset.range n, (l : K⟦X⟧) ^ i * E K l e ^ (n - 1 - i) := by
  have h := (Commute.all ((l : K⟦X⟧)) (E K l e)).geom_sum₂_mul n
  have hE : (l : K⟦X⟧) - E K l e = -((X : K⟦X⟧) ^ e) := by simp [E]
  rw [hE] at h
  linear_combination -h

theorem l_pow_smul (n : ℕ) (y : Vec K a ι) : (l : K) ^ n • y =
    E K l e ^ n • y - (X : K⟦X⟧) ^ e • ∑ i ∈ Finset.range n, ((l ^ i : ℕ)) • (E K l e ^ (n - 1 - i) • y : Vec K a ι) := by
  have h1 : (l : K) ^ n • y = ((l : K⟦X⟧)) ^ n • y := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [h1, l_pow_eq (e := e), sub_smul, mul_smul, Finset.sum_smul]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

variable (D : BKDat O K l e a ι η H)

theorem E_pow_smul_mem_M (j : ℕ) {m : Vec K a ι} (hm : m ∈ D.M) : E K l e ^ j • m ∈ D.M := by
  have := D.M.smul_mem (EIn l e (A O K) ^ j) hm
  simpa [Subalgebra.smul_def] using this

theorem E_pow_smul_mem_EM (j : ℕ) {y : Vec K a ι} (hy : y ∈ D.EM η) : E K l e ^ j • y ∈ D.EM η := by
  rw [mem_divE] at hy ⊢
  rw [smul_comm]
  exact E_pow_smul_mem_M D j hy

theorem E_pow_smul_mem_Y (j : ℕ) {y : Vec K a ι} (hy : y ∈ D.Y) : E K l e ^ j • y ∈ D.Y := by
  rw [BKDat.Y, Descent.mem_invOf] at hy ⊢
  exact ⟨E_pow_smul_mem_EM D j hy.1, fun g => by rw [Descent.act_E_pow_smul, hy.2 g]⟩

theorem cls_E_pow_smul_mem_Z (j : ℕ) {y : Vec K a ι} (hy : y ∈ D.EM η)
    (h : ∀ g, D.desc.actPol g (D.cls y) = D.cls y) : D.cls (E K l e ^ j • y) ∈ D.Z := by
  refine ⟨⟨_, E_pow_smul_mem_EM D j hy, rfl⟩, fun g => ?_⟩
  have h' := congrArg (D.mulPol ⟨_, pow_mem (E_mem l e (Rpi O K l e)) j⟩) (h g)
  rw [Descent.actPol_cls] at h'
  change D.desc.actPol g (D.cls (E K l e ^ j • y)) = D.cls (E K l e ^ j • y)
  rw [Descent.actPol_cls, Descent.act_E_pow_smul]
  exact h'

end GlobalTheory.NgalDivisible

namespace GlobalTheory.NgalDivisible

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}
  (D : BKDat O K l e a ι η H)

theorem l_pow_smul_Z {w : D.Pol} (hw : w ∈ D.Z) : ∃ z ∈ D.Z, (l : K) ^ η • w = D.vPol z := by
  obtain ⟨⟨y, hy, rfl⟩, h⟩ := D.desc.mem_Z.1 hw
  set s : Vec K a ι := ∑ i ∈ Finset.range η, (l ^ i : ℕ) • (E K l e ^ (η - 1 - i) • y : Vec K a ι) with hs
  have hsZ : D.cls s ∈ D.Z := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_nsmul]
      exact Submodule.smul_of_tower_mem _ _ (cls_E_pow_smul_mem_Z D _ hy h)
  refine ⟨-D.cls s, neg_mem hsZ, ?_⟩
  have h0 : D.cls (E K l e ^ η • y) = 0 := D.cls_eq_zero_iff.2 (D.M_le_Man hy)
  rw [← map_smul, l_pow_smul (e := e) η y, ← hs, map_sub, h0, zero_sub, map_neg, PhiMod.vPol_cls]

theorem l_pow_smul_Y {y : Vec K a ι} (hy : y ∈ D.Y) : (l : K) ^ η • y ∈ D.Y' ⊔ D.Minv := by
  have hy' := hy
  rw [BKDat.Y, Descent.mem_invOf] at hy'
  set s : Vec K a ι := ∑ i ∈ Finset.range η, (l ^ i : ℕ) • (E K l e ^ (η - 1 - i) • y : Vec K a ι) with hs
  have hsY : s ∈ D.Y := Submodule.sum_mem _ fun i _ =>
    Submodule.smul_of_tower_mem _ _ (E_pow_smul_mem_Y D _ hy)
  have h1 : -((X : K⟦X⟧) ^ e • s) ∈ D.Y' :=
    D.desc.mem_Y'.2 ⟨-s, neg_mem hsY, smul_neg _ _⟩
  have h2 : E K l e ^ η • y ∈ D.Minv := by
    rw [BKDat.Minv, Descent.mem_invOf]
    exact ⟨hy'.1, fun g => by rw [Descent.act_E_pow_smul, hy'.2 g]⟩
  rw [l_pow_smul (e := e) η y, ← hs, sub_eq_neg_add]
  exact Submodule.add_mem_sup h1 h2

end GlobalTheory.NgalDivisible

theorem GlobalTheory.divisible_of_BKDat : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ)
    (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Divisible D := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D
  exact ⟨fun _ hw => NgalDivisible.l_pow_smul_Z D hw, fun _ hy => NgalDivisible.l_pow_smul_Y D hy⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDivisibilityOfDescentDatumStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_divisibility_of_descentDatum : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Divisible D := by
  first | exact @GlobalTheory.divisible_of_BKDat | exact GlobalTheory.divisible_of_BKDat | (intros; apply GlobalTheory.divisible_of_BKDat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemAnalyticFiltrationIffLatticeFiltrationAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemAnalyticFiltrationIffLatticeFiltrationAdd
noncomputable section

open PowerSeries Matrix

namespace GlobalTheory.BK.FilAn

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι)

theorem E_pow_smul_mem_extRpi {β : ℕ} (hβ : ∀ v ∈ P.M, E K l e ^ β • v ∈ P.L) {m : Vec K a ι}
    (hm : m ∈ P.Mext (Rpi O K l e)) : E K l e ^ β • m ∈ P.ext (Rpi O K l e) :=
  P.smul_mem_ext_of_basis (fun i => hβ _ (P.bas_mem_M i)) (A_le_Rpi l e) hm

theorem mem_extInvL_of_Ezpow_smul {i : ℤ} {y : Vec K a ι} (hy : y ∈ P.ext (Rpi O K l e))
    (hg : Ezpow K l e i • y ∈ P.Mext (invL l (A O K))) : y ∈ P.ext (invL l (A O K)) := by
  refine mem_tot.2 fun τ => P.mem_extc_iff.2 fun j => ?_
  have hc : (P.mxInv τ *ᵥ y τ) j ∈ Rpi O K l e := P.mem_extc_iff.1 (mem_tot.1 hy τ) j
  have hB : invE l e (A O K) ≤ invE l e (invL l (A O K)) := away_mono (le_away _ _) rfl
  have h1 : (P.mxInv τ *ᵥ (Ezpow K l e i • y) τ) j ∈ invE l e (invL l (A O K)) := by
    simp only [Matrix.mulVec, dotProduct]
    exact Subalgebra.sum_mem _ fun k _ => mul_mem (hB (P.mxInv_mem τ j k))
      (le_away _ _ (mem_tot.1 hg τ k))
  obtain ⟨n, hn⟩ := h1
  have h2 : Ezpow K l e (n + i) * (P.mxInv τ *ᵥ y τ) j ∈ invL l (A O K) := by
    rw [Ezpow_add, Ezpow_natCast, mul_assoc]
    simpa [Matrix.mulVec_smul] using hn
  have h3 := mul_mem ((Ezpow_mem_invL_A_iff (O := O) (K := K) (l := l) (e := e)
    (i := ((-(n + i)).toNat : ℤ))).2 (by omega)) h2
  rw [← mul_assoc, ← Ezpow_add,
    show (((-(n + i)).toNat : ℕ) : ℤ) + (n + i) = ((n + i).toNat : ℕ) by omega, Ezpow_natCast] at h3
  exact mem_invL_A_of_E_pow_mul l e _ hc h3

omit [IsUltrametricDist K] [CompleteSpace K] [IsUnitBall O K] [Fintype ι] [DecidableEq ι] in
theorem Ezpow_zero' : Ezpow K l e 0 = 1 := by
  simpa using Ezpow_natCast (K := K) l e 0

omit [CompleteSpace K] in
theorem mem_extRpi_of_mem_shiftE_one {z : Vec K a ι} (hz : z ∈ shiftE l e 1 (P.ext (Rpi O K l e))) :
    z ∈ P.ext (Rpi O K l e) := by
  have h := P.smul_tot_mem_ext (f := fun _ => E K l e) (fun _ => E_mem l e _) (mem_shiftE.1 hz)
  have h1 : E K l e * Ezpow K l e (-1) = 1 := by
    simpa using E_pow_mul_Ezpow_neg (K := K) l e 1
  have h2 : ((fun _ : ZMod a => E K l e) • Ezpow K l e (-1) • z) = z := by
    ext τ j
    simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, h1, one_mul]
  rwa [h2] at h

theorem exists_mem_filL_of_mem_inf [NeZero a] (i : ℤ) {x : Vec K a ι}
    (hx : x ∈ P.ext (Rpi O K l e) ⊓ shiftE l e i (P.Mext (Rpi O K l e))) :
    ∃ y ∈ P.filL i, x - y ∈ shiftE l e 1 (P.ext (Rpi O K l e)) := by
  obtain ⟨hxL, hxM⟩ := Submodule.mem_inf.1 hx
  obtain ⟨-, β, -, hβ⟩ := P.exists_exponents
  set N : ℕ := (β + 1 - i).toNat with hN
  choose g hg h hh hgh using fun τ k => exists_div_E_pow l e N (mem_tot.1 (mem_shiftE.1 hxM) τ k)
  have hgM : g ∈ P.Mext (invL l (A O K)) := mem_tot.2 fun τ k => hg τ k
  have hhM : h ∈ P.Mext (Rpi O K l e) := mem_tot.2 fun τ k => hh τ k
  have hx' : Ezpow K l e (-i) • x = g + E K l e ^ N • h := by
    funext τ k
    exact hgh τ k
  have hxe : x = Ezpow K l e i • g + Ezpow K l e i • E K l e ^ N • h := by
    rw [← smul_add, ← hx', smul_smul, ← Ezpow_add, add_neg_cancel, Ezpow_zero', one_smul]
  have hsub : x - Ezpow K l e i • g ∈ shiftE l e 1 (P.ext (Rpi O K l e)) := by
    rw [mem_shiftE]
    have h1 := E_pow_smul_mem_extRpi P hβ (P.smul_tot_mem_Mext (f := fun _ => E K l e ^ (i - 1 + N - β).toNat)
      (fun _ => pow_mem (E_mem l e _) _) hhM)
    convert h1 using 1
    have hs : Ezpow K l e (-1) * (Ezpow K l e i * E K l e ^ N) =
        E K l e ^ β * E K l e ^ (i - 1 + N - β).toNat := by
      simp only [← Ezpow_natCast, ← Ezpow_add]
      congr 1
      omega
    rw [hxe, add_sub_cancel_left]
    funext τ k
    simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul]
    linear_combination (h τ k) * hs
  refine ⟨Ezpow K l e i • g, Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨?_, ?_⟩), hsub⟩
  · refine mem_extInvL_of_Ezpow_smul P (i := -i) ?_ ?_
    · have := sub_mem hxL (mem_extRpi_of_mem_shiftE_one P hsub)
      rwa [sub_sub_cancel] at this
    · rwa [smul_smul, ← Ezpow_add, neg_add_cancel, Ezpow_zero', one_smul]
  · rwa [mem_shiftE, smul_smul, ← Ezpow_add, neg_add_cancel, Ezpow_zero', one_smul]

end GlobalTheory.BK.FilAn


open GlobalTheory.BK in
theorem GlobalTheory.BK.PhiMod.mem_analytic_filtration_iff : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (i : ℤ) (x : Vec K a ι), x ∈ (P.ext (Rpi O K l e) ⊓ shiftE l e i (P.Mext (Rpi O K l e))) ⊔ shiftE l e 1 (P.ext (Rpi O K l e)) ↔ ∃ y ∈ P.filL i, x - y ∈ shiftE l e 1 (P.ext (Rpi O K l e)) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P i x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨y, hy, hxy⟩ := FilAn.exists_mem_filL_of_mem_inf P i hx₁
    refine ⟨y, hy, ?_⟩
    rw [add_sub_right_comm]
    exact add_mem hxy hx₂
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨hy₁L, hy₁M⟩ := Submodule.mem_inf.1 hy₁
    refine Submodule.mem_sup.2 ⟨y₁, Submodule.mem_inf.2 ⟨P.ext_mono (invL_A_le_Rpi l e) hy₁L,
      mem_shiftE.2 (P.Mext_mono (invL_A_le_Rpi l e) (mem_shiftE.1 hy₁M))⟩, y₂ + (x - (y₁ + y₂)),
      add_mem (mem_shiftE.2 (P.ext_mono (invL_A_le_Rpi l e) (mem_shiftE.1 hy₂))) hxy, by abel⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemAnalyticFiltrationIffLatticeFiltrationAddStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_analytic_filtration_iff_lattice_filtration_add : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (i : ℤ) (x : Vec K a ι), x ∈ (P.ext (Rpi O K l e) ⊓ shiftE l e i (P.Mext (Rpi O K l e))) ⊔ shiftE l e 1 (P.ext (Rpi O K l e)) ↔ ∃ y ∈ P.filL i, x - y ∈ shiftE l e 1 (P.ext (Rpi O K l e)) := by
  first | exact @GlobalTheory.BK.PhiMod.mem_analytic_filtration_iff | exact GlobalTheory.BK.PhiMod.mem_analytic_filtration_iff | (intros; apply GlobalTheory.BK.PhiMod.mem_analytic_filtration_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesRadiusSizeLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoUntiltFrobeniusSeriesTermNormsZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoUntiltFrobeniusSeriesTermNormsZero
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem psers_norm_natCast_self (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  rw [Padic.norm_p] at h
  simpa using h

theorem psers_terms_tendsto_zero : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ), 1 ≤ h → 0 ≤ r → r < 1 → Filter.Tendsto (fun n : ℤ => ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))) Filter.cofinite (nhds 0) := by
  intro l _ h j r h1 hr0 hr1
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hlR : (1 : ℝ) < l := by exact_mod_cast hl
  have ha := psers_norm_natCast_self l
  set a := ‖(l : ℂ_[l])‖ with ha_def
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha1 : a < 1 := by rw [ha]; exact inv_lt_one_of_one_lt₀ hlR
  rw [Int.cofinite_eq, Filter.tendsto_sup]
  constructor
  · rw [← Filter.map_neg_atTop, Filter.tendsto_map'_iff, ← Nat.map_cast_int_atTop,
      Filter.tendsto_map'_iff]
    refine squeeze_zero (fun k => ?_) (fun k => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1)
    · simp only [Function.comp_apply, neg_neg, zpow_natCast]
      exact mul_nonneg (pow_nonneg ha0 _) (Real.rpow_nonneg hr0 _)
    · simp only [Function.comp_apply, neg_neg, zpow_natCast]
      have : r ^ ((l : ℝ) ^ (-(k : ℤ) * h + j : ℤ)) ≤ 1 :=
        Real.rpow_le_one hr0 hr1.le (zpow_nonneg (by positivity) _)
      calc a ^ k * r ^ ((l : ℝ) ^ (-(k : ℤ) * h + j : ℤ)) ≤ a ^ k * 1 :=
            mul_le_mul_of_nonneg_left this (pow_nonneg ha0 _)
        _ = a ^ k := mul_one _
  · rw [← Nat.map_cast_int_atTop, Filter.tendsto_map'_iff]
    have hN : Filter.Tendsto (fun k : ℕ => l ^ (k * h + j)) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_mono (fun k => ?_) Filter.tendsto_id
      calc k ≤ l ^ k := (Nat.lt_pow_self hl).le
        _ ≤ l ^ (k * h + j) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    refine squeeze_zero (fun k => ?_) (fun k => ?_)
      ((tendsto_self_mul_const_pow_of_lt_one hr0 hr1).comp hN)
    · exact mul_nonneg (zpow_nonneg ha0 _) (Real.rpow_nonneg hr0 _)
    · have e1 : a ^ (-((k : ℕ) : ℤ)) = (l : ℝ) ^ k := by
        rw [zpow_neg, zpow_natCast, ha, inv_pow, inv_inv]
      have e2 : (l : ℝ) ^ (((k : ℕ) : ℤ) * h + j : ℤ) = ((l ^ (k * h + j) : ℕ) : ℝ) := by
        rw [show (((k : ℕ) : ℤ) * h + j : ℤ) = ((k * h + j : ℕ) : ℤ) by push_cast; ring,
          zpow_natCast]
        push_cast; ring
      simp only [Function.comp_apply]
      rw [e1, e2, Real.rpow_natCast]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 _)
      have : l ^ k ≤ l ^ (k * h + j) := Nat.pow_le_pow_right (by omega) (by nlinarith)
      exact_mod_cast this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoUntiltFrobeniusSeriesTermNormsZeroStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_untiltFrobeniusSeries_term_norms_zero : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ), 1 ≤ h → 0 ≤ r → r < 1 → Filter.Tendsto (fun n : ℤ => ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))) Filter.cofinite (nhds 0) := by
  first | exact @GlobalTheory.psers_terms_tendsto_zero | exact GlobalTheory.psers_terms_tendsto_zero | (intros; apply GlobalTheory.psers_terms_tendsto_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesRadiusSizeLaws
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem gam_norm_natCast_eq (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  exact @_root_.GlobalTheory.psers_norm_natCast_self l _

theorem gam_exists_max_of_tendsto (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hf : Filter.Tendsto f Filter.cofinite (nhds 0)) : ∃ n₀, ∀ n, f n ≤ f n₀ := by
  by_cases hall : ∀ n, f n = 0
  · exact ⟨0, fun n => by rw [hall n, hall 0]⟩
  push_neg at hall
  obtain ⟨m, hm⟩ := hall
  have hmpos : 0 < f m := lt_of_le_of_ne (hf0 m) (Ne.symm hm)
  have hev : ∀ᶠ n in Filter.cofinite, f n < f m := hf (Iio_mem_nhds hmpos)
  have hfin : {n | ¬ f n < f m}.Finite := Filter.eventually_cofinite.mp hev
  have hmem : m ∈ hfin.toFinset := by simp
  obtain ⟨n₀, hn₀, hmax⟩ := hfin.toFinset.exists_max_image f ⟨m, hmem⟩
  refine ⟨n₀, fun n => ?_⟩
  by_cases hn : f n < f m
  · exact hn.le.trans (hmax m hmem)
  · exact hmax n (by simpa using hn)

theorem gam_laws : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ), 1 ≤ h → 0 ≤ r → r < 1 → (∀ n : ℤ, ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ)) ≤ gam l h j r) ∧ (∃ n : ℤ, gam l h j r = ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))) ∧ 0 ≤ gam l h j r ∧ (0 < r → 0 < gam l h j r) ∧ gam l h j (r ^ l ^ h) = ‖(l : ℂ_[l])‖ * gam l h j r ∧ ∀ s : ℝ, r < s → s < 1 → gam l h j r < gam l h j s := by
  intro l _ h j r h1 hr0 hr1
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hlR : (1 : ℝ) < l := by exact_mod_cast hl
  have ha := gam_norm_natCast_eq l
  set a := ‖(l : ℂ_[l])‖ with ha_def
  have ha0 : 0 < a := by rw [ha]; positivity

  have key : ∀ t : ℝ, 0 ≤ t → t < 1 →
      (∀ n : ℤ, a ^ (-n) * t ^ ((l : ℝ) ^ (n * h + j : ℤ)) ≤ gam l h j t) ∧
      (∃ n : ℤ, gam l h j t = a ^ (-n) * t ^ ((l : ℝ) ^ (n * h + j : ℤ))) := by
    intro t ht0 ht1
    set f : ℤ → ℝ := fun n => a ^ (-n) * t ^ ((l : ℝ) ^ (n * h + j : ℤ)) with hf_def
    have hf0 : ∀ n, 0 ≤ f n := fun n => mul_nonneg (zpow_nonneg ha0.le _) (Real.rpow_nonneg ht0 _)
    obtain ⟨n₀, hn₀⟩ := gam_exists_max_of_tendsto f hf0 (GlobalTheory.T.tendsto_untiltFrobeniusSeries_term_norms_zero l h j t h1 ht0 ht1)
    have hbdd : BddAbove (Set.range f) := ⟨f n₀, by rintro _ ⟨n, rfl⟩; exact hn₀ n⟩
    have hg : gam l h j t = ⨆ n, f n := rfl
    refine ⟨fun n => ?_, n₀, ?_⟩
    · rw [hg]; exact le_ciSup hbdd n
    · rw [hg]; exact le_antisymm (ciSup_le hn₀) (le_ciSup hbdd n₀)
  obtain ⟨hle, n₀, hn₀⟩ := key r hr0 hr1
  refine ⟨hle, ⟨n₀, hn₀⟩, ?_, ?_, ?_, ?_⟩
  · rw [hn₀]; exact mul_nonneg (zpow_nonneg ha0.le _) (Real.rpow_nonneg hr0 _)
  · intro hr
    exact lt_of_lt_of_le (mul_pos (zpow_pos ha0 _) (Real.rpow_pos_of_pos hr _)) (hle 0)
  ·
    have hq0 : 0 ≤ r ^ l ^ h := pow_nonneg hr0 _
    have hq1 : r ^ l ^ h < 1 := pow_lt_one₀ hr0 hr1 (by positivity)
    obtain ⟨hle', m₀, hm₀⟩ := key (r ^ l ^ h) hq0 hq1
    have shift : ∀ n : ℤ, a ^ (-n) * (r ^ l ^ h) ^ ((l : ℝ) ^ (n * h + j : ℤ)) =
        a * (a ^ (-(n + 1)) * r ^ ((l : ℝ) ^ ((n + 1) * h + j : ℤ))) := by
      intro n
      have e1 : (r ^ l ^ h) ^ ((l : ℝ) ^ (n * h + j : ℤ)) = r ^ ((l : ℝ) ^ ((n + 1) * h + j : ℤ)) := by
        rw [← Real.rpow_natCast r (l ^ h), ← Real.rpow_mul hr0]
        congr 1
        have hl0 : (l : ℝ) ≠ 0 := by positivity
        rw [show ((n + 1) * h + j : ℤ) = (h : ℤ) + (n * h + j) by ring, zpow_add₀ hl0 (h : ℤ) (n * h + j), zpow_natCast, Nat.cast_pow]
      have e2 : a ^ (-n) = a * a ^ (-(n + 1)) := by
        rw [show -n = 1 + (-(n + 1)) by ring, zpow_add₀ ha0.ne', zpow_one]
      rw [e1, e2]; ring
    apply le_antisymm
    · rw [hm₀, shift]
      exact mul_le_mul_of_nonneg_left (hle (m₀ + 1)) ha0.le
    · rw [hn₀]
      have := hle' (n₀ - 1)
      rw [shift, show n₀ - 1 + 1 = n₀ by ring] at this
      exact this
  · intro s hrs hs1
    have hs0 : 0 < s := lt_of_le_of_lt hr0 hrs
    obtain ⟨hles, -⟩ := key s hs0.le hs1
    rw [hn₀]
    refine lt_of_lt_of_le ?_ (hles n₀)
    apply mul_lt_mul_of_pos_left _ (zpow_pos ha0 _)
    exact Real.rpow_lt_rpow hr0 hrs (zpow_pos (by positivity) _)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesRadiusSizeLawsStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ), 1 ≤ h → 0 ≤ r → r < 1 → (∀ n : ℤ, ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ)) ≤ gam l h j r) ∧ (∃ n : ℤ, gam l h j r = ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))) ∧ 0 ≤ gam l h j r ∧ (0 < r → 0 < gam l h j r) ∧ gam l h j (r ^ l ^ h) = ‖(l : ℂ_[l])‖ * gam l h j r ∧ ∀ s : ℝ, r < s → s < 1 → gam l h j r < gam l h j s := by
  first | exact @GlobalTheory.gam_laws | exact GlobalTheory.gam_laws | (intros; apply GlobalTheory.gam_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiagScaleApply
noncomputable section

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]


variable (K a ι) in
def diagScale (s : ZMod a → K) : Module.End K (Vec K a ι) where
  toFun v τ := s τ • v τ
  map_add' v w := by ext1 τ; simp [smul_add]
  map_smul' c v := by
    ext1 τ
    exact smul_comm (s τ) c (v τ)

@[simp] theorem diagScale_apply (s : ZMod a → K) (v : Vec K a ι) (τ : ZMod a) :
    diagScale K a ι s v τ = s τ • v τ := rfl

variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]

def isoProj {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e) : Module.End K (Vec K a ι) :=
  letI := Fintype.ofFinite (rootsOfUnity e K)
  (e : K)⁻¹ • ∑ ζ : rootsOfUnity e K,
    diagScale K a ι (fun τ => ((TameGal.inertia ζ : TameGal K l e a).root τ)⁻¹ ^ c.val) ∘ₗ
      Δ.act (TameGal.inertia ζ)

def Tsub {η H : ℕ} {D₁ : BKDat O K l e a ι η H} {D₂ : BKDat O K l e a κ η H} (F : BKHom D₁ D₂)
    (A' b : ℕ) : Submodule O (Vec K a κ) :=
  (F.imL.restrictScalars O).map ((mulV K a κ (((X : K⟦X⟧) ^ e) ^ A')).restrictScalars O) ⊔
    (D₂.L.restrictScalars O).map ((mulV K a κ ((l : K⟦X⟧) ^ b)).restrictScalars O) ⊔
    GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.MMHigh D₂.toPhiMod

end GlobalTheory.CokerL

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]

theorem act_vpow_smul {P : PhiMod O K l e a ι} (Δ : Descent P) (g : TameGal K l e a) (n : ℕ)
    (w : Vec K a ι) : Δ.act g (((X : K⟦X⟧) ^ e) ^ n • w) = ((X : K⟦X⟧) ^ e) ^ n • Δ.act g w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, ih, Δ.act_X_pow_smul, ← mul_smul, ← pow_succ]

theorem diagScale_smul (s : ZMod a → K) (f : K⟦X⟧) (w : Vec K a ι) :
    diagScale K a ι s (f • w) = f • diagScale K a ι s w := by
  ext1 τ
  exact smul_comm (s τ) f (w τ)

theorem isoProj_vpow {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e) (n : ℕ) (v : Vec K a ι) :
    isoProj Δ c (((X : K⟦X⟧) ^ e) ^ n • v) = ((X : K⟦X⟧) ^ e) ^ n • isoProj Δ c v := by
  letI := Fintype.ofFinite (rootsOfUnity e K)
  simp only [isoProj, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, act_vpow_smul, diagScale_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  exact smul_comm _ _ _

theorem app_isoProj {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {Δ₁ : Descent P}
    {Δ₂ : Descent Q} (F : Descent.Hom Δ₁ Δ₂) (c : ZMod e) (v : Vec K a ι) :
    F.app (isoProj Δ₁ c v) = isoProj Δ₂ c (F.app v) := by
  letI := Fintype.ofFinite (rootsOfUnity e K)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [isoProj, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.map_smul_of_tower, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [← F.app_act]
  ext1 τ
  simp only [diagScale_apply, BK.Hom.app_apply, Matrix.mulVec_smul]

end GlobalTheory.CokerL
end
end
