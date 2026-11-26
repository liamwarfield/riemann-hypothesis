module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeDegreeOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobFixedLatticeConditionSmulOfFrobeniusFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobFixedLatticeConditionSmulOfFrobeniusFixed
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

theorem latC_smul_of_fr_fixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (a : n → P.R.B) (e : ↥(MaximalUnramifiedExtension l)), fr l r e = e → LatC P U x y a → LatC P U x y (e • a) := by
  intro l _ P r n _ _ U x y a e he h
  obtain ⟨h1, h2⟩ := h
  have hsm : ∀ i, (e • a) i = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * a i := fun i => by
    rw [Pi.smul_apply, Algebra.smul_def]
  have hev : ∀ (m : ℕ) (b : P.R.B), ev P m (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * b) = kd P (fr l m e) * ev P m b := by
    intro m b
    rw [← evHom_apply, map_mul, evHom_apply, evHom_apply, ev_kur]
  refine ⟨fun i => ?_, fun m => ?_⟩
  · rw [hsm]
    have key : ∀ k : ℕ, P.φB^[k] (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * a i) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l k e) * P.φB^[k] (a i) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', ih, map_mul, Function.iterate_succ_apply', phiB_algebraMap, add_comm, fr_add, fr_one]
    rw [key, he, h1]
  · obtain ⟨w, hw, hw'⟩ := h2 m
    refine ⟨fun i => kd P (fr l m e) * w i, fun i => Fil_mul_left (kd_mem_Fil P _) (hw i), ?_⟩
    funext i
    rw [hsm, hev]
    have := congrFun hw' i
    rw [this]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PMon.ResR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobFixedLatticeConditionSmulOfFrobeniusFixedStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobFixedLatticeCondition_smul_of_frobenius_fixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (a : n → P.R.B) (e : ↥(MaximalUnramifiedExtension l)), fr l r e = e → LatC P U x y a → LatC P U x y (e • a) := by
  first | exact @GlobalTheory.PMon.ResR.latC_smul_of_fr_fixed | exact GlobalTheory.PMon.ResR.latC_smul_of_fr_fixed | (intros; apply GlobalTheory.PMon.ResR.latC_smul_of_fr_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRestrictionLatticeColumn
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRestrictionLatticeColumn
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR


open Fin.NatCast in
theorem eq_zero_of_sum_kd_mul_U0_mem_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x : Fin r × n), (∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∑ i, kd P (c i) * (U x.1 : Matrix n n P.R.BdR) i x.2 ∈ Fil P 1 → c = 0) → ∀ c : n × Fin r → ↥(MaximalUnramifiedExtension l), (∀ i, fr l 1 (c i) = c i) → ∑ i, kd P (c i) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) i (x.2, x.1) ∈ Fil P 1 → c = 0 := by
  intro l _ P r ω hω hdet n _ _ U x hx c hc hsum
  haveI : NeZero r := ⟨fun h => by subst h; exact x.1.elim0⟩
  set Q : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := ((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)).val with hQ
  have hQp : Q * resMat n ω = 1 := (resGL n ω hdet).inv_mul
  set d := Matrix.vecMul c Q with hd_def
  have hcd : c = Matrix.vecMul d (resMat n ω) := by
    rw [hd_def, Matrix.vecMul_vecMul, hQp, Matrix.vecMul_one]
  have hexp : ∀ i k, c (i, k) = ∑ m : Fin r, d (i, m) * fr l m (ω k) := by
    intro i k
    conv_lhs => rw [hcd]
    simp only [Matrix.vecMul, dotProduct, resMat_apply, Fintype.sum_prod_type, mul_ite, mul_zero]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  have hrel : ∀ i (m : Fin r), d (i, m + 1) = fr l 1 (d (i, m)) := by
    intro i
    have hv : Matrix.vecMul (fun m' : Fin r => fr l 1 (d (i, m' - 1)) - d (i, m')) (frobMat ω) = 0 := by
      funext k
      simp only [Matrix.vecMul, dotProduct, frobMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, Pi.zero_apply]
      rw [← hexp i k]
      have h1 : ∑ m' : Fin r, fr l 1 (d (i, m' - 1)) * fr l m' (ω k)
          = ∑ m : Fin r, fr l 1 (d (i, m)) * fr l 1 (fr l m (ω k)) := by
        refine (Fintype.sum_equiv (Equiv.addRight (1 : Fin r)) _ _ fun m => ?_).symm
        simp only [Equiv.coe_addRight, add_sub_cancel_right]
        congr 1
        rw [← fr_add, ← fr_mod (hω k) ((m + 1 : Fin r) : ℕ), ← fr_mod (hω k) (1 + (m : ℕ))]
        congr 1
        rw [Fin.val_add, Nat.mod_mod, add_comm]
        rcases Nat.lt_or_ge 1 r with h | h
        · rw [Fin.val_one', Nat.mod_eq_of_lt h]
        · have : r = 1 := by have := NeZero.ne r; omega
          subst this; simp
      rw [h1]
      simp_rw [← map_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← hexp i k, hc (i, k), sub_self]
    have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
    intro m
    have := congrFun h0 (m + 1)
    simp only [add_sub_cancel_right, Pi.zero_apply, sub_eq_zero] at this
    exact this.symm
  have hprop : ∀ i (k : ℕ), d (i, x.1 + (k : Fin r)) = fr l k (d (i, x.1)) := by
    intro i k
    induction k with
    | zero => simp [fr_zero]
    | succ k ih => rw [Nat.cast_succ, ← add_assoc, hrel, ih, ← fr_add, add_comm]
  have hfix : ∀ i, fr l r (d (i, x.1)) = d (i, x.1) := by
    intro i; rw [← hprop, Fin.natCast_self, add_zero]
  have hU0 : (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR)
      = Q.map (kd P) * Matrix.blockDiagonal (fun m => (U m : Matrix n n P.R.BdR)) := rfl
  have hid : ∑ a, kd P (c a) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) a (x.2, x.1)
      = ∑ j, kd P (d (j, x.1)) * (U x.1 : Matrix n n P.R.BdR) j x.2 := by
    have step : ∀ a, kd P (c a) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) a (x.2, x.1)
        = ∑ j, kd P (c a) * kd P (Q a (j, x.1)) * (U x.1 : Matrix n n P.R.BdR) j x.2 := by
      intro a
      rw [hU0]
      simp only [Matrix.mul_apply, Matrix.blockDiagonal_apply, Matrix.map_apply, Fintype.sum_prod_type, mul_ite,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_congr rfl fun a _ => step a, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hd_def, Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.sum_mul]
  have hzero : (fun j => d (j, x.1)) = 0 := hx _ hfix (hid ▸ hsum)
  have hd0 : d = 0 := by
    funext ⟨i, m⟩
    have hm : m = x.1 + (((m - x.1 : Fin r) : ℕ) : Fin r) := by simp
    rw [hm, hprop, show d (i, x.1) = 0 from congrFun hzero i, map_zero]
    rfl
  rw [hcd, hd0, Matrix.zero_vecMul]

end GlobalTheory.PMon.ResR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRestrictionLatticeColumnStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_restrictionLattice_column : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x : Fin r × n), (∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∑ i, kd P (c i) * (U x.1 : Matrix n n P.R.BdR) i x.2 ∈ Fil P 1 → c = 0) → ∀ c : n × Fin r → ↥(MaximalUnramifiedExtension l), (∀ i, fr l 1 (c i) = c i) → ∑ i, kd P (c i) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) i (x.2, x.1) ∈ Fil P 1 → c = 0 := by
  first | exact @GlobalTheory.PMon.ResR.eq_zero_of_sum_kd_mul_U0_mem_fil | exact GlobalTheory.PMon.ResR.eq_zero_of_sum_kd_mul_U0_mem_fil | (intros; apply GlobalTheory.PMon.ResR.eq_zero_of_sum_kd_mul_U0_mem_fil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBdRPlusUnitMatrixRestrictionLatticeMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBdRPlusUnitMatrixRestrictionLatticeMatrix
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem fil_mul_entries {n : Type} [Fintype n] {A B : Matrix n n P.R.BdR}
    (hA : ∀ i j, A i j ∈ Fil P 0) (hB : ∀ i j, B i j ∈ Fil P 0) : ∀ i j, (A * B) i j ∈ Fil P 0 :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Fil_sum fun k _ => Fil_mul_left (hA i k) (hB k j)

theorem fil_blockDiagonal_entries {r : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    (V : Fin r → Matrix n n P.R.BdR) (h : ∀ m i j, V m i j ∈ Fil P 0) :
    ∀ a b, Matrix.blockDiagonal V a b ∈ Fil P 0 := fun a b => by
  rw [Matrix.blockDiagonal_apply]
  split_ifs
  · exact h _ _ _
  · exact Fil_zero_mem 0

theorem fil_kd_entries {m : Type} [Fintype m] [DecidableEq m] (g : GL m ↥(MaximalUnramifiedExtension l)) :
    ∀ a b, ((Units.map ((kd P).mapMatrix : Matrix m m ↥(MaximalUnramifiedExtension l) →+* Matrix m m P.R.BdR).toMonoidHom g :
      GL m P.R.BdR) : Matrix m m P.R.BdR) a b ∈ Fil P 0 := fun a b => by
  rw [Units.coe_map]
  exact kd_mem_Fil P _

theorem unitM_U0_of_unitM : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR),
    (∀ m, UnitM P (U m)) → UnitM P (U0 P ω hdet U) := by
  intro l _ P r ω hdet n _ _ U hU
  constructor
  · unfold U0
    rw [Units.val_mul, ← map_inv]
    exact fil_mul_entries (fil_kd_entries _)
      (fil_blockDiagonal_entries _ fun m i j => (hU m).1 i j)
  · unfold U0
    rw [mul_inv_rev, inv_inv, Units.val_mul]
    exact fil_mul_entries
      (fil_blockDiagonal_entries _ fun m i j => (hU m).2 i j) (fil_kd_entries _)

end GlobalTheory.PMon.ResR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBdRPlusUnitMatrixRestrictionLatticeMatrixStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBdRPlusUnitMatrix_restrictionLatticeMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR), (∀ m, UnitM P (U m)) → UnitM P (U0 P ω hdet U) := by
  first | exact @GlobalTheory.PMon.ResR.unitM_U0_of_unitM | exact GlobalTheory.PMon.ResR.unitM_U0_of_unitM | (intros; apply GlobalTheory.PMon.ResR.unitM_U0_of_unitM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRestrictionLatticeColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRestrictionLatticeColumns
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.ResR

open Matrix

variable {l : ℕ} [Fact l.Prime] {r : ℕ}

theorem resGL_mul_inv_map (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    (hdet : (frobMat ω).det ≠ 0) {S : Type} [CommRing S] (f : ↥(MaximalUnramifiedExtension l) →+* S) :
    (resMat n ω).map f * (((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map f = 1 := by
  have h : (resMat n ω) = ((resGL n ω hdet : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) := rfl
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, Units.mul_inv, map_one]

theorem resGL_inv_mul_map (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    (hdet : (frobMat ω).det ≠ 0) {S : Type} [CommRing S] (f : ↥(MaximalUnramifiedExtension l) →+* S) :
    (((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map f * (resMat n ω).map f = 1 := by
  have h : (resMat n ω) = ((resGL n ω hdet : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) := rfl
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, Units.inv_mul, map_one]

theorem resMat_mulVec_apply (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    {S : Type} [CommRing S] (f : ↥(MaximalUnramifiedExtension l) →+* S) (v : n × Fin r → S) (i : n) (m : Fin r) :
    ((resMat n ω).map f *ᵥ v) (i, m) = ∑ k, f (fr l m (ω k)) * v (i, k) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, resMat_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

variable (P : LocPrime l) {n : Type} [Fintype n] [DecidableEq n]

theorem sum_fr_mul_eq_iter (hr : 0 < r) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hω : ∀ k, fr l r (ω k) = ω k)
    (a : n → P.R.B) (ha : ∀ i, P.φB^[r] (a i) = a i) (u : n × Fin r → P.R.B)
    (hu : (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) *ᵥ u = fun j => P.φB^[j.2] (a j.1))
    (m : ℕ) (i : n) :
    ∑ k, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l m (ω k)) * u (i, k) = P.φB^[m] (a i) := by
  have h := congrFun hu (i, ⟨m % r, Nat.mod_lt _ hr⟩)
  rw [resMat_mulVec_apply] at h
  simp only [fr_mod (hω _)] at h
  rw [h]
  exact Function.IsPeriodicPt.iterate_mod_apply (ha i) m

theorem phi_fix_of_res (hr : 0 < r) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hω : ∀ k, fr l r (ω k) = ω k)
    (hdet : (frobMat ω).det ≠ 0)
    (a : n → P.R.B) (ha : ∀ i, P.φB^[r] (a i) = a i) (u : n × Fin r → P.R.B)
    (hu : (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) *ᵥ u = fun j => P.φB^[j.2] (a j.1))
    (j : n × Fin r) : P.φB (u j) = u j := by
  set d : n × Fin r → P.R.B := fun j => P.φB (u j) - u j with hd
  have hz : (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) *ᵥ d = 0 := by
    funext ⟨i, m⟩
    rw [resMat_mulVec_apply]
    have h1 := sum_fr_mul_eq_iter P hr ω hω a ha u hu (m + (r - 1)) i
    have h2 := sum_fr_mul_eq_iter P hr ω hω a ha u hu (m + (r - 1) + 1) i
    have e : m + (r - 1) + 1 = (m : ℕ) + r := by omega
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Function.iterate_succ_apply', ← h1, map_sum] at h2
    simp only [map_mul, phiB_algebraMap, ← fr_one, ← fr_add] at h2
    rw [show 1 + ((m : ℕ) + (r - 1)) = (m : ℕ) + r by omega, e] at h2
    simp only [fr_add, hω] at h2
    simp only [hd, mul_sub, Finset.sum_sub_distrib, Pi.zero_apply]
    rw [h2, sub_self]
  have : d = 0 := by
    rw [← Matrix.one_mulVec d, ← resGL_inv_mul_map n ω hdet, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  exact sub_eq_zero.1 (congrFun this j)

def tzGL {N : Type} [Fintype N] [DecidableEq N] (e : N → ℤ) : GL N P.R.BdR where
  val := Matrix.diagonal fun j => tz P (e j)
  inv := Matrix.diagonal fun j => tz P (-e j)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp [← tz_add, tz_zero]
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp [← tz_add, tz_zero]

theorem iota_q_eq (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hdet : (frobMat ω).det ≠ 0) (U : Fin r → GL n P.R.BdR)
    (e : n × Fin r → ℤ) (A₀ : GL (n × Fin r) P.R.B) (W₀ : GL (n × Fin r) P.R.BdR)
    (hA : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) =
      (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j => tz P (e j)) *
        (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR)) :
    ((A₀⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B).map P.ιB *
      ((((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map
        (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map P.ιB *
      (blockGL U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j => tz P (e j)) =
      ((W₀⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
  set G : GL (n × Fin r) P.R.BdR := Units.map ((P.ιB : P.R.B →+* P.R.BdR).mapMatrix).toMonoidHom A₀ with hGdef
  set kp : GL (n × Fin r) P.R.BdR := Units.map ((kd P).mapMatrix : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) →+*
    Matrix (n × Fin r) (n × Fin r) P.R.BdR).toMonoidHom (resGL n ω hdet) with hkp
  have hG : G = kp⁻¹ * blockGL U * tzGL P e * W₀ := by
    apply Units.ext
    rw [hGdef]
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply, Units.val_mul]
    rw [show (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (P.ιB : P.R.B →+* P.R.BdR) =
      (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) from rfl, hA]
    rfl
  have h1 : ((A₀⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B).map P.ιB =
      ((G⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
    rw [hGdef, ← map_inv, Units.coe_map]
    rfl
  have h2 : ((((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map
        (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map P.ιB = ((kp⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
    rw [hkp, ← map_inv, Units.coe_map, Matrix.map_map]
    ext i j
    simp [iota_kur]
  have h3 : (blockGL U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j => tz P (e j)) =
      ((blockGL U * tzGL P e : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := rfl
  rw [h1, h2, Matrix.mul_assoc, h3, ← Units.val_mul, ← Units.val_mul, hG]
  congr 1
  group

theorem mem_span_colv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ), 0 < r → ∀ (ω : Fin r → ↥(MaximalUnramifiedExtension l)),
    (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n]
    (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B),
    (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) →
    ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ →
    (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) →
    ∀ a : n → P.R.B, LatC P U x y a → a ∈ Submodule.span ℚ_[l] (Set.range (colv P ω A₀)) := by
  intro l _ P r hr ω hω hdet n _ _ U x y A₀ hφ W₀ hW₀ hA a hLat
  obtain ⟨ha, hw⟩ := hLat
  choose w hw0 hwe using hw
  set pB : Matrix (n × Fin r) (n × Fin r) P.R.B := (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) with hpB
  set pI : Matrix (n × Fin r) (n × Fin r) P.R.B :=
    (((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map
      (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) with hpI
  set V : n × Fin r → P.R.B := fun j => P.φB^[j.2] (a j.1) with hV
  set u : n × Fin r → P.R.B := pI *ᵥ V with hu
  have hpu : pB *ᵥ u = V := by
    rw [hu, Matrix.mulVec_mulVec, hpB, hpI, resGL_mul_inv_map, Matrix.one_mulVec]
  set Ai : Matrix (n × Fin r) (n × Fin r) P.R.B := ((A₀⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B)
    with hAi
  set q : n × Fin r → P.R.B := Ai *ᵥ u with hq

  have hAφ : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map P.φB = A₀ := Matrix.ext fun i j => hφ i j
  have hAiφ : Ai.map (P.φB : P.R.B →+* P.R.B) = Ai := by
    have h1 : Ai.map (P.φB : P.R.B →+* P.R.B) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) = 1 := by
      conv_lhs => rw [← hAφ]
      rw [show (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map P.φB =
          ((P.φB : P.R.B →+* P.R.B).mapMatrix (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B)) from rfl,
        show Ai.map (P.φB : P.R.B →+* P.R.B) = (P.φB : P.R.B →+* P.R.B).mapMatrix Ai from rfl, ← map_mul, hAi,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    calc Ai.map (P.φB : P.R.B →+* P.R.B)
        = Ai.map (P.φB : P.R.B →+* P.R.B) * ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) * Ai) := by
          rw [hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = Ai := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have huφ : ∀ j, P.φB (u j) = u j := phi_fix_of_res P hr ω hω hdet a ha u hpu
  have hqφ : ∀ c, P.φB (q c) = q c := by
    intro c
    have := RingHom.map_mulVec (P.φB : P.R.B →+* P.R.B) Ai u c
    rw [hAiφ] at this
    change P.φB (q c) = _ at this
    rw [this, hq]
    congr 1
    funext j
    exact huφ j

  set wt : n × Fin r → P.R.BdR := fun j => w j.2 j.1 with hwt
  have hιV : (fun j => P.ιB (V j)) = ((blockGL U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1)))) *ᵥ wt := by
    funext ⟨i, m⟩
    have h := congrFun (hwe m) i
    change P.ιB (P.φB^[m] (a i)) = _
    have hd : ∀ (v w : n × Fin r → P.R.BdR), Matrix.diagonal v *ᵥ w = fun j => v j * w j :=
      fun v w => funext (Matrix.mulVec_diagonal v w)
    have hd' : ∀ (v w : n → P.R.BdR), Matrix.diagonal v *ᵥ w = fun j => v j * w j :=
      fun v w => funext (Matrix.mulVec_diagonal v w)
    rw [show P.ιB (P.φB^[m] (a i)) = ev P m (a i) from rfl, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hd, hd']
    simp only [Matrix.mulVec, dotProduct, blockGL, Matrix.blockDiagonal_apply, Fintype.sum_prod_type, hwt]
    rw [Finset.sum_comm, Finset.sum_eq_single m]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  have hιq : (fun c => P.ιB (q c)) = ((W₀⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *ᵥ wt := by
    funext c
    have e1 := RingHom.map_mulVec (P.ιB : P.R.B →+* P.R.BdR) Ai u c
    have e2 : (fun j => P.ιB (u j)) = (pI.map (P.ιB : P.R.B →+* P.R.BdR)) *ᵥ (fun j => P.ιB (V j)) := by
      funext j
      exact RingHom.map_mulVec (P.ιB : P.R.B →+* P.R.BdR) pI V j
    change P.ιB (q c) = _ at e1
    rw [e1]
    change (Ai.map P.ιB *ᵥ (fun j => P.ιB (u j))) c = _
    rw [e2, hιV, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [← iota_q_eq P ω hdet U (fun j : n × Fin r => eps x y (j.2, j.1)) A₀ W₀ hA]
    simp only [Matrix.mul_assoc]
    rfl
  have hqF : ∀ c, P.ιB (q c) ∈ Fil P 0 := by
    intro c
    rw [show P.ιB (q c) = (fun c => P.ιB (q c)) c from rfl, hιq]
    exact Fil_sum fun j _ => Fil_mul_left (hW₀.2 c j) (hw0 j.2 j.1)
  choose cq hcq using fun c => fund P (hqφ c) (hqF c)

  have hAq : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) *ᵥ q = u := by
    rw [hq, Matrix.mulVec_mulVec, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have haeq : a = ∑ c, cq c • colv P ω A₀ c := by
    funext i
    have h0 := sum_fr_mul_eq_iter P hr ω hω a ha u hpu 0 i
    simp only [fr_zero, Function.iterate_zero, id] at h0
    rw [← h0, ← hAq]
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply]
    simp only [Algebra.smul_def, hcq, colv, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [haeq]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self c))

end GlobalTheory.PMon.ResR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRestrictionLatticeColumnsStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_restrictionLattice_columns : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ), 0 < r → ∀ (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → ∀ a : n → P.R.B, LatC P U x y a → a ∈ Submodule.span ℚ_[l] (Set.range (colv P ω A₀)) := by
  first | exact @GlobalTheory.PMon.ResR.mem_span_colv | exact GlobalTheory.PMon.ResR.mem_span_colv | (intros; apply GlobalTheory.PMon.ResR.mem_span_colv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedMatrixUnitsOfLatticeBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedMatrixUnitsOfLatticeBasis
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Extract

theorem exists_matrix_of_span {F B n N : Type} [Field F] [CommRing B] [Algebra F B] [Fintype N]
    (u v : N → n → B) (h : Submodule.span F (Set.range u) ≤ Submodule.span F (Set.range v)) :
    ∃ G : Matrix N N F, ∀ (ψ : B →ₐ[F] B) (c : N) (i : n),
      ψ (u c i) = ∑ e, ψ (v e i) * algebraMap F B (G e c) := by
  classical
  have hc : ∀ c, ∃ g : N → F, ∑ e, g e • v e = u c := fun c =>
    (Submodule.mem_span_range_iff_exists_fun F).mp (h (Submodule.subset_span ⟨c, rfl⟩))
  choose g hg using hc
  refine ⟨Matrix.of fun e c => g c e, ?_⟩
  intro ψ c i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hg c, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Pi.smul_apply, map_smul, Algebra.smul_def, mul_comm, Matrix.of_apply]

theorem mul_mem_sub {R N : Type} [CommRing R] [Fintype N] (S : Subring R) {X Y : Matrix N N R}
    (hX : ∀ i j, X i j ∈ S) (hY : ∀ i j, Y i j ∈ S) (i j : N) : (X * Y) i j ∈ S := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)

theorem blocks {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] {r : ℕ} (S : Subring R)
    (E U : Fin r → GL n R) (d : n × Fin r → R) (hd : ∀ x, IsUnit (d x))
    (W W' : Matrix (n × Fin r) (n × Fin r) R) (hW : ∀ i j, W i j ∈ S) (hW' : ∀ i j, W' i j ∈ S)
    (hWW : W * W' = 1)
    (h : Matrix.blockDiagonal (fun m => (E m : Matrix n n R)) =
      Matrix.blockDiagonal (fun m => (U m : Matrix n n R)) * Matrix.diagonal d * W) (m : Fin r) :
    ∃ V : GL n R, (∀ i j, (V : Matrix n n R) i j ∈ S) ∧ (∀ i j, ((V⁻¹ : GL n R) : Matrix n n R) i j ∈ S) ∧
      (E m : Matrix n n R) = (U m : Matrix n n R) * Matrix.diagonal (fun j => d (j, m)) * (V : Matrix n n R) := by
  classical
  set M : Fin r → Matrix n n R := fun m => (U m : Matrix n n R) * Matrix.diagonal (fun j => d (j, m)) with hM
  set Mi : Fin r → Matrix n n R := fun m =>
    Matrix.diagonal (fun j => (((hd (j, m)).unit⁻¹ : Rˣ) : R)) * (((U m)⁻¹ : GL n R) : Matrix n n R) with hMi
  have hMiM : ∀ m, Mi m * M m = 1 := by
    intro m
    calc Mi m * M m = Matrix.diagonal (fun j => (((hd (j, m)).unit⁻¹ : Rˣ) : R)) *
          ((((U m)⁻¹ : GL n R) : Matrix n n R) * (U m : Matrix n n R)) * Matrix.diagonal (fun j => d (j, m)) := by
          simp only [hM, hMi, Matrix.mul_assoc]
      _ = 1 := by
          rw [Units.inv_mul, Matrix.mul_one, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
          congr 1
          funext j
          exact IsUnit.val_inv_mul _
  have hMMi : ∀ m, M m * Mi m = 1 := by
    intro m
    calc M m * Mi m = (U m : Matrix n n R) * ((Matrix.diagonal (fun j => d (j, m)) *
          Matrix.diagonal (fun j => (((hd (j, m)).unit⁻¹ : Rˣ) : R))) * (((U m)⁻¹ : GL n R) : Matrix n n R)) := by
          simp only [hM, hMi, Matrix.mul_assoc]
      _ = 1 := by
          rw [Matrix.diagonal_mul_diagonal]
          have : (fun j => d (j, m) * (((hd (j, m)).unit⁻¹ : Rˣ) : R)) = fun _ => (1 : R) := by
            funext j
            exact IsUnit.mul_val_inv _
          rw [this, Matrix.diagonal_one, Matrix.one_mul, Units.mul_inv]
  have hdiag : Matrix.diagonal d = Matrix.blockDiagonal (fun m => Matrix.diagonal fun j => d (j, m)) := by
    rw [Matrix.blockDiagonal_diagonal]
  have h' : Matrix.blockDiagonal (fun m => (E m : Matrix n n R)) = Matrix.blockDiagonal M * W := by
    rw [h, hdiag, Matrix.blockDiagonal_mul]
  set Vm : Fin r → Matrix n n R := fun m => Mi m * (E m : Matrix n n R) with hVm
  set Vm' : Fin r → Matrix n n R := fun m => (((E m)⁻¹ : GL n R) : Matrix n n R) * M m with hVm'
  have hVV : ∀ m, Vm m * Vm' m = 1 := by
    intro m
    simp only [hVm, hVm', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (E m : Matrix n n R), Units.mul_inv, Matrix.one_mul, hMiM]
  have hV'V : ∀ m, Vm' m * Vm m = 1 := by
    intro m
    simp only [hVm, hVm', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (M m), hMMi, Matrix.one_mul, Units.inv_mul]
  have hWb : W = Matrix.blockDiagonal Vm := by
    have hone : Matrix.blockDiagonal Mi * Matrix.blockDiagonal M = 1 := by
      rw [← Matrix.blockDiagonal_mul]
      simp only [hMiM]
      exact Matrix.blockDiagonal_one
    calc W = (Matrix.blockDiagonal Mi * Matrix.blockDiagonal M) * W := by rw [hone, Matrix.one_mul]
      _ = Matrix.blockDiagonal Mi * Matrix.blockDiagonal (fun m => (E m : Matrix n n R)) := by
          rw [Matrix.mul_assoc, ← h']
      _ = Matrix.blockDiagonal Vm := by rw [← Matrix.blockDiagonal_mul, hVm]
  have hW'b : W' = Matrix.blockDiagonal Vm' := by
    have hone : Matrix.blockDiagonal Vm' * W = 1 := by
      rw [hWb, ← Matrix.blockDiagonal_mul]
      simp only [hV'V]
      exact Matrix.blockDiagonal_one
    calc W' = (Matrix.blockDiagonal Vm' * W) * W' := by rw [hone, Matrix.one_mul]
      _ = Matrix.blockDiagonal Vm' := by rw [Matrix.mul_assoc, hWW, Matrix.mul_one]
  refine ⟨⟨Vm m, Vm' m, hVV m, hV'V m⟩, ?_, ?_, ?_⟩
  · intro i j
    have hij := hW (i, m) (j, m)
    rw [hWb, Matrix.blockDiagonal_apply_eq] at hij
    exact hij
  · intro i j
    have hij := hW' (i, m) (j, m)
    rw [hW'b, Matrix.blockDiagonal_apply_eq] at hij
    exact hij
  · show (E m : Matrix n n R) = (U m : Matrix n n R) * Matrix.diagonal (fun j => d (j, m)) * (Mi m * (E m : Matrix n n R))
    rw [← Matrix.mul_assoc]
    have := hMMi m
    simp only [hM] at this
    rw [this, Matrix.one_mul]

theorem abstract {F B R n : Type} [Field F] [CommRing B] [Algebra F B] [CommRing R] [Fintype n] [DecidableEq n]
    {r : ℕ} (hr : 0 < r) (φ : B →ₐ[F] B) (ι : B →+* R) (S : Subring R) (hS : ∀ q : F, ι (algebraMap F B q) ∈ S)
    (w : Fin r → B) (hw : ∀ k, (φ ^ r) (w k) = w k) (hwu : ∀ k, IsUnit (w k))
    (p q : Matrix (n × Fin r) (n × Fin r) B) (hp : ∀ a b, p a b = if a.1 = b.1 then (φ ^ (a.2 : ℕ)) (w b.2) else 0)
    (hpq : p * q = 1) (hpS : ∀ a b, ι (p a b) ∈ S) (hqS : ∀ a b, ι (q a b) ∈ S)
    (U : Fin r → GL n R) (d : n × Fin r → R) (hd : ∀ x, IsUnit (d x))
    (A₀ : GL (n × Fin r) B)
    (hA₀ : ∀ i j, φ ((A₀ : Matrix (n × Fin r) (n × Fin r) B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) B) i j)
    (W₀ : GL (n × Fin r) R) (hW₀ : ∀ i j, (W₀ : Matrix (n × Fin r) (n × Fin r) R) i j ∈ S)
    (hW₀' : ∀ i j, ((W₀⁻¹ : GL (n × Fin r) R) : Matrix (n × Fin r) (n × Fin r) R) i j ∈ S)
    (hA : (A₀ : Matrix (n × Fin r) (n × Fin r) B).map ι =
      q.map ι * Matrix.blockDiagonal (fun m => (U m : Matrix n n R)) * Matrix.diagonal d *
        (W₀ : Matrix (n × Fin r) (n × Fin r) R))
    (a : n → n → B)
    (hsp : Submodule.span F (Set.range fun (jk : n × Fin r) (i : n) => w jk.2 * a jk.1 i) =
      Submodule.span F (Set.range fun (c : n × Fin r) (i : n) =>
        ∑ k, w k * (A₀ : Matrix (n × Fin r) (n × Fin r) B) (i, k) c)) :
    ∃ A : GL n B, (∀ i j, (φ ^ r) ((A : Matrix n n B) i j) = (A : Matrix n n B) i j) ∧
      ∀ m : Fin r, ∃ V : GL n R, (∀ i j, (V : Matrix n n R) i j ∈ S) ∧
        (∀ i j, ((V⁻¹ : GL n R) : Matrix n n R) i j ∈ S) ∧
        (A : Matrix n n B).map (fun b => ι ((φ ^ (m : ℕ)) b)) =
          (U m : Matrix n n R) * Matrix.diagonal (fun j => d (j, m)) * (V : Matrix n n R) := by
  classical
  have hfix : ∀ (m : ℕ) (x : B), φ x = x → (φ ^ m) x = x := by
    intro m x hx
    induction m with
    | zero => simp
    | succ k ih => rw [pow_succ, AlgHom.mul_apply, hx, ih]
  obtain ⟨G, hG⟩ := exists_matrix_of_span (F := F)
    (fun (jk : n × Fin r) (i : n) => w jk.2 * a jk.1 i)
    (fun (c : n × Fin r) (i : n) => ∑ k, w k * (A₀ : Matrix (n × Fin r) (n × Fin r) B) (i, k) c) hsp.le
  obtain ⟨G', hG'⟩ := exists_matrix_of_span (F := F)
    (fun (c : n × Fin r) (i : n) => ∑ k, w k * (A₀ : Matrix (n × Fin r) (n × Fin r) B) (i, k) c)
    (fun (jk : n × Fin r) (i : n) => w jk.2 * a jk.1 i) hsp.ge
  set A : Matrix n n B := Matrix.of fun i j => a j i with hAdef
  set Gm : Matrix (n × Fin r) (n × Fin r) B := G.map (algebraMap F B) with hGm
  set G'm : Matrix (n × Fin r) (n × Fin r) B := G'.map (algebraMap F B) with hG'm
  set D : Matrix (n × Fin r) (n × Fin r) B := Matrix.blockDiagonal fun m : Fin r => A.map ⇑(φ ^ (m : ℕ)) with hDdef
  have hY : ∀ (i : n) (m : Fin r) (e : n × Fin r), (p * (A₀ : Matrix (n × Fin r) (n × Fin r) B)) (i, m) e =
      (φ ^ (m : ℕ)) (∑ k, w k * (A₀ : Matrix (n × Fin r) (n × Fin r) B) (i, k) e) := by
    intro i m e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hp, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul, hfix _ _ (hA₀ _ _)]
  have hZ : ∀ (i : n) (m : Fin r) (c : n × Fin r), (D * p) (i, m) c = (φ ^ (m : ℕ)) (w c.2 * a c.1 i) := by
    intro i m c
    have hinner : ∀ x : n, ∑ k : Fin r, D (i, m) (x, k) * p (x, k) c =
        (φ ^ (m : ℕ)) (a x i) * (if x = c.1 then (φ ^ (m : ℕ)) (w c.2) else 0) := by
      intro x
      rw [Fintype.sum_eq_single m]
      · simp only [hDdef, Matrix.blockDiagonal_apply_eq, Matrix.map_apply, hAdef, Matrix.of_apply, hp]
      · intro k hk
        rw [hDdef, Matrix.blockDiagonal_apply_ne _ _ _ (Ne.symm hk), zero_mul]
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [hinner, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul]
    rw [mul_comm]
  have hZY : D * p = p * (A₀ : Matrix (n × Fin r) (n × Fin r) B) * Gm := by
    ext ⟨i, m⟩ c
    rw [hZ, hG (φ ^ (m : ℕ)) c i, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hY]
    rfl
  have hYZ : p * (A₀ : Matrix (n × Fin r) (n × Fin r) B) = D * p * G'm := by
    ext ⟨i, m⟩ c
    rw [hY, hG' (φ ^ (m : ℕ)) c i, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hZ]
    rfl
  have hqp : q * p = 1 := mul_eq_one_comm.mp hpq
  have hL : ((A₀⁻¹ : GL (n × Fin r) B) : Matrix (n × Fin r) (n × Fin r) B) * q *
      (p * (A₀ : Matrix (n × Fin r) (n × Fin r) B)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc q, hqp, Matrix.one_mul]
    exact Units.inv_mul A₀
  have hGG : Gm * G'm = 1 := by
    calc Gm * G'm = (((A₀⁻¹ : GL (n × Fin r) B) : Matrix (n × Fin r) (n × Fin r) B) * q *
          (p * (A₀ : Matrix (n × Fin r) (n × Fin r) B))) * (Gm * G'm) := by rw [hL, Matrix.one_mul]
      _ = ((A₀⁻¹ : GL (n × Fin r) B) : Matrix (n × Fin r) (n × Fin r) B) * q *
          (p * (A₀ : Matrix (n × Fin r) (n × Fin r) B) * Gm * G'm) := by simp only [Matrix.mul_assoc]
      _ = ((A₀⁻¹ : GL (n × Fin r) B) : Matrix (n × Fin r) (n × Fin r) B) * q *
          (p * (A₀ : Matrix (n × Fin r) (n × Fin r) B)) := by rw [← hZY, ← hYZ]
      _ = 1 := hL
  have hD : D = p * (A₀ : Matrix (n × Fin r) (n × Fin r) B) * Gm * q := by
    calc D = D * (p * q) := by rw [hpq, Matrix.mul_one]
      _ = D * p * q := by rw [Matrix.mul_assoc]
      _ = p * (A₀ : Matrix (n × Fin r) (n × Fin r) B) * Gm * q := by rw [hZY]
  have hDinv : D * (p * G'm * ((A₀⁻¹ : GL (n × Fin r) B) : Matrix (n × Fin r) (n × Fin r) B) * q) = 1 := by
    rw [hD]
    calc p * (A₀ : Matrix (n × Fin r) (n × Fin r) B) * Gm * q *
          (p * G'm * ((A₀⁻¹ : GL (n × Fin r) B) : Matrix (n × Fin r) (n × Fin r) B) * q) =
        p * ((A₀ : Matrix (n × Fin r) (n × Fin r) B) * ((Gm * (q * p) * G'm) *
          (((A₀⁻¹ : GL (n × Fin r) B) : Matrix (n × Fin r) (n × Fin r) B) * q))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hqp, Matrix.mul_one, hGG, Matrix.one_mul, ← Matrix.mul_assoc (A₀ : Matrix (n × Fin r) (n × Fin r) B),
            Units.mul_inv, Matrix.one_mul, hpq]
  have hdetD : IsUnit D.det := Matrix.isUnit_det_of_right_inverse hDinv
  rw [hDdef, Matrix.det_blockDiagonal] at hdetD
  have hdetA : IsUnit A.det := by
    have h0 := isUnit_of_dvd_unit
      (Finset.dvd_prod_of_mem (fun m : Fin r => (A.map ⇑(φ ^ (m : ℕ))).det) (Finset.mem_univ ⟨0, hr⟩)) hdetD
    have hm0 : A.map ⇑(φ ^ ((⟨0, hr⟩ : Fin r) : ℕ)) = A := by
      ext i j
      simp
    simpa only [hm0] using h0
  refine ⟨Matrix.nonsingInvUnit A hdetA, ?_, ?_⟩
  · intro i j
    change (φ ^ r) (a j i) = a j i
    have hyfix : ∀ e : n × Fin r, (φ ^ r) (∑ k, w k * (A₀ : Matrix (n × Fin r) (n × Fin r) B) (i, k) e) =
        ∑ k, w k * (A₀ : Matrix (n × Fin r) (n × Fin r) B) (i, k) e := by
      intro e
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, hw k, hfix _ _ (hA₀ _ _)]
    have h1 := hG (φ ^ r) (j, ⟨0, hr⟩) i
    have h2 := hG (AlgHom.id F B) (j, ⟨0, hr⟩) i
    simp only [hyfix, AlgHom.id_apply] at h1 h2
    rw [← h2, map_mul, hw] at h1
    exact (hwu _).mul_left_cancel h1
  · intro m
    set Wm : Matrix (n × Fin r) (n × Fin r) R := (W₀ : Matrix (n × Fin r) (n × Fin r) R) * Gm.map ι * q.map ι with hWm
    set W'm : Matrix (n × Fin r) (n × Fin r) R :=
      p.map ι * G'm.map ι * ((W₀⁻¹ : GL (n × Fin r) R) : Matrix (n × Fin r) (n × Fin r) R) with hW'm
    have hGS : ∀ i j, (Gm.map ι) i j ∈ S := fun i j => hS (G i j)
    have hG'S : ∀ i j, (G'm.map ι) i j ∈ S := fun i j => hS (G' i j)
    have hWS : ∀ i j, Wm i j ∈ S := fun i j =>
      mul_mem_sub S (fun i j => mul_mem_sub S hW₀ hGS i j) hqS i j
    have hW'S : ∀ i j, W'm i j ∈ S := fun i j =>
      mul_mem_sub S (fun i j => mul_mem_sub S hpS hG'S i j) hW₀' i j
    have hWW : Wm * W'm = 1 := by
      calc Wm * W'm = (W₀ : Matrix (n × Fin r) (n × Fin r) R) * ((Gm * (q * p) * G'm).map ι) *
            ((W₀⁻¹ : GL (n × Fin r) R) : Matrix (n × Fin r) (n × Fin r) R) := by
            simp only [hWm, hW'm, Matrix.map_mul, Matrix.mul_assoc]
        _ = 1 := by
            rw [hqp, Matrix.mul_one, hGG, Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.mul_one, Units.mul_inv]
    have hpqι : p.map ι * q.map ι = 1 := by
      rw [← Matrix.map_mul, hpq, Matrix.map_one _ (map_zero ι) (map_one ι)]
    let E : Fin r → GL n R := fun m =>
      Units.map (ι.comp ((φ ^ (m : ℕ) : B →ₐ[F] B) : B →+* B)).mapMatrix.toMonoidHom (Matrix.nonsingInvUnit A hdetA)
    have hEm : (E m : Matrix n n R) = (Matrix.nonsingInvUnit A hdetA : Matrix n n B).map
        (fun b => ι ((φ ^ (m : ℕ)) b)) := by
      ext i j
      rfl
    have hblk : Matrix.blockDiagonal (fun m => (E m : Matrix n n R)) =
        Matrix.blockDiagonal (fun m => (U m : Matrix n n R)) * Matrix.diagonal d * Wm := by
      calc Matrix.blockDiagonal (fun m => (E m : Matrix n n R)) = D.map ι := by
            rw [hDdef, Matrix.blockDiagonal_map _ _ (map_zero ι)]
            rfl
        _ = p.map ι * (A₀ : Matrix (n × Fin r) (n × Fin r) B).map ι * Gm.map ι * q.map ι := by
            rw [hD]
            simp only [Matrix.map_mul]
        _ = p.map ι * (q.map ι * Matrix.blockDiagonal (fun m => (U m : Matrix n n R)) * Matrix.diagonal d *
            (W₀ : Matrix (n × Fin r) (n × Fin r) R)) * Gm.map ι * q.map ι := by rw [hA]
        _ = (p.map ι * q.map ι) * Matrix.blockDiagonal (fun m => (U m : Matrix n n R)) * Matrix.diagonal d *
            ((W₀ : Matrix (n × Fin r) (n × Fin r) R) * Gm.map ι * q.map ι) := by simp only [Matrix.mul_assoc]
        _ = Matrix.blockDiagonal (fun m => (U m : Matrix n n R)) * Matrix.diagonal d * Wm := by
            rw [hpqι, Matrix.one_mul]
    obtain ⟨V, hV1, hV2, hV3⟩ := blocks S E U d hd Wm W'm hWS hW'S hWW hblk m
    exact ⟨V, hV1, hV2, by rw [← hEm]; exact hV3⟩

theorem extract : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n), (∀ m, UnitM P (U m)) → ∀ (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → ∀ a : n → n → P.R.B, Submodule.span ℚ_[l] (Set.range fun jk : n × Fin r => ω jk.2 • a jk.1) = Submodule.span ℚ_[l] (Set.range (colv P ω A₀)) → ∃ A : GL n P.R.B, (∀ i j, P.φB^[r] ((A : Matrix n n P.R.B) i j) = (A : Matrix n n P.R.B) i j) ∧ ∀ m : Fin r, ∃ W : GL n P.R.BdR, UnitM P W ∧ (A : Matrix n n P.R.B).map (ev P m) = (U m : Matrix n n P.R.BdR) * Matrix.diagonal (fun j => tz P (eps x y (m, j))) * (W : Matrix n n P.R.BdR) := by
  intro l _ P r ω hω hdet n _ _ U x y hU A₀ hA₀ W₀ hW₀ hA a hsp
  classical
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact ⟨1, fun i j => rfl, fun m => m.elim0⟩
  have hcoe : ∀ (m : ℕ) (b : P.R.B), (P.φB ^ m) b = P.φB^[m] b := by
    intro m
    induction m with
    | zero => intro b; rfl
    | succ k ih => intro b; rw [pow_succ, AlgHom.mul_apply, ih, Function.iterate_succ_apply]
  have hWu := hW₀
  unfold UnitM at hWu
  let ι : P.R.B →+* P.R.BdR := (P.ιB : P.R.B →+* P.R.BdR)
  let pGL : GL (n × Fin r) P.R.B :=
    Units.map ((algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).mapMatrix :
      Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) →+* Matrix (n × Fin r) (n × Fin r) P.R.B).toMonoidHom (resGL n ω hdet)
  have hpv : ∀ a b, (pGL : Matrix (n × Fin r) (n × Fin r) P.R.B) a b =
      algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ((resGL n ω hdet : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) a b) := fun a b => rfl
  have hqv : ∀ a b, ((pGL⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B) a b =
      algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ((((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) :
        Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) a b) := fun a b => rfl
  have hres : (resGL n ω hdet : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = resMat n ω := rfl
  have hwu : ∀ k, IsUnit (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (ω k)) := by
    intro k
    refine IsUnit.map _ (isUnit_iff_ne_zero.mpr ?_)
    intro h0
    apply hdet
    apply Matrix.det_eq_zero_of_column_eq_zero k
    intro m
    simp [frobMat, h0]
  have hsp' : Submodule.span ℚ_[l] (Set.range fun (jk : n × Fin r) (i : n) =>
        algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (ω jk.2) * a jk.1 i) =
      Submodule.span ℚ_[l] (Set.range fun (c : n × Fin r) (i : n) =>
        ∑ k, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (ω k) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) (i, k) c) := by
    have e4 : (fun (jk : n × Fin r) (i : n) => algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (ω jk.2) * a jk.1 i) =
        fun jk => ω jk.2 • a jk.1 := by
      funext jk i
      rw [Pi.smul_apply, Algebra.smul_def]
    rw [e4]
    exact hsp
  have hAι : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map ι =
      ((pGL⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B).map ι *
        Matrix.blockDiagonal (fun m => (U m : Matrix n n P.R.BdR)) *
        Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) *
        (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
    have e1 : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map ι =
        (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) := by
      ext i j
      rfl
    have e3 : ((pGL⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B).map ι =
        ((((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))).map (kd P) := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, hqv]
      exact iota_kur P _
    have e2 : (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) =
        ((pGL⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B).map ι *
          Matrix.blockDiagonal (fun m => (U m : Matrix n n P.R.BdR)) := by
      rw [e3]
      rfl
    rw [e1, hA, e2]
  obtain ⟨A, hA1, hA2⟩ := abstract (F := ℚ_[l]) (B := P.R.B) (R := P.R.BdR) (n := n) hr P.φB ι (S0 P)
    (fun q => by
      rw [mem_S0_of_sum_eq]
      show P.ιB (algebraMap ℚ_[l] P.R.B q) ∈ Fil P 0
      rw [AlgHom.commutes]
      exact q_mem_Fil P q)
    (fun k => algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (ω k))
    (fun k => by rw [hcoe, phi_iter_kur, hω])
    hwu
    (pGL : Matrix (n × Fin r) (n × Fin r) P.R.B)
    ((pGL⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B)
    (fun a b => by
      rw [hpv, hres, resMat_apply]
      split_ifs
      · rw [hcoe, phi_iter_kur]
      · exact map_zero _)
    (Units.mul_inv pGL)
    (fun a b => by
      rw [mem_S0_of_sum_eq]
      show P.ιB ((pGL : Matrix (n × Fin r) (n × Fin r) P.R.B) a b) ∈ Fil P 0
      rw [hpv, iota_kur]
      exact kd_mem_Fil P _)
    (fun a b => by
      rw [mem_S0_of_sum_eq]
      show P.ιB (((pGL⁻¹ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B) a b) ∈ Fil P 0
      rw [hqv, iota_kur]
      exact kd_mem_Fil P _)
    U (fun j : n × Fin r => tz P (eps x y (j.2, j.1)))
    (fun j => by
      unfold tz
      exact (Units.isUnit _).map P.ιB)
    A₀ hA₀ W₀ (fun i j => (mem_S0_of_sum_eq P).mpr (hWu.1 i j)) (fun i j => (mem_S0_of_sum_eq P).mpr (hWu.2 i j)) hAι a hsp'
  refine ⟨A, fun i j => by rw [← hcoe]; exact hA1 i j, fun m => ?_⟩
  obtain ⟨V, hV1, hV2, hV3⟩ := hA2 m
  refine ⟨V, by unfold UnitM; exact ⟨fun i j => (mem_S0_of_sum_eq P).mp (hV1 i j), fun i j => (mem_S0_of_sum_eq P).mp (hV2 i j)⟩, ?_⟩
  rw [← hV3]
  ext i j
  show P.ιB (P.φB^[(m : ℕ)] _) = P.ιB ((P.φB ^ (m : ℕ)) _)
  rw [hcoe]

end GlobalTheory.PMon.Extract

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedMatrixUnitsOfLatticeBasisStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobeniusFixed_matrix_units_of_lattice_basis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n), (∀ m, UnitM P (U m)) → ∀ (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → ∀ a : n → n → P.R.B, Submodule.span ℚ_[l] (Set.range fun jk : n × Fin r => ω jk.2 • a jk.1) = Submodule.span ℚ_[l] (Set.range (colv P ω A₀)) → ∃ A : GL n P.R.B, (∀ i j, P.φB^[r] ((A : Matrix n n P.R.B) i j) = (A : Matrix n n P.R.B) i j) ∧ ∀ m : Fin r, ∃ W : GL n P.R.BdR, UnitM P W ∧ (A : Matrix n n P.R.B).map (ev P m) = (U m : Matrix n n P.R.BdR) * Matrix.diagonal (fun j => tz P (eps x y (m, j))) * (W : Matrix n n P.R.BdR) := by
  first | exact @GlobalTheory.PMon.Extract.extract | exact GlobalTheory.PMon.Extract.extract | (intros; apply GlobalTheory.PMon.Extract.extract <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeFrobFixedForallDegree
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem flAt_all : ∀ r : ℕ, FLAt r := by
  intro r l _ P AI T n _ _ U x y hxy hU hc
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact x.1.elim0
  obtain ⟨E, ω, -, -, -, hω, hlin, hspan, hdet⟩ := GlobalTheory.T.unramifiedExt_fixedField_frobeniusPow_degree l r hr
  have hdet' : (frobMat ω).det ≠ 0 := hdet
  have hxy' : ((0 : Fin 1), ((x.2, x.1) : n × Fin r)) ≠ (0, (y.2, y.1)) := by
    intro h
    apply hxy
    simp only [Prod.mk.injEq, true_and] at h
    exact Prod.ext h.2 h.1
  obtain ⟨A₀, hA₀, hW⟩ := GlobalTheory.T.fundamentalLemmaLattice_degreeOne l P AI T (n × Fin r) (fun _ => U0 P ω hdet' U) _ _ hxy'
    (fun _ => GlobalTheory.T.isBdRPlusUnitMatrix_restrictionLatticeMatrix l P r ω hdet' n U hU) (GlobalTheory.T.linearIndependent_restrictionLattice_column l P r ω hω hdet' n U x hc)
  obtain ⟨W₀, hW₀, heq⟩ := hW 0
  have he : ∀ j : n × Fin r, eps ((0 : Fin 1), ((x.2, x.1) : n × Fin r)) (0, (y.2, y.1)) (0, j) = eps x y (j.2, j.1) := by
    intro j
    simp only [eps, Prod.mk.injEq, true_and, Prod.ext_iff]
    grind
  have heq' : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet' U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
    simpa [he] using heq
  have hA₀' : ∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j :=
    fun i j => by simpa using hA₀ i j
  have h3 := GlobalTheory.T.restrictionLattice_columns_condition_linearIndependent l P r ω hω hdet' n U x y A₀ hA₀' W₀ hW₀ heq'
  obtain ⟨a, -, -, hsp⟩ := GlobalTheory.T.exists_frobeniusFixed_unramified_tower_basis l r ω hω hlin hspan (n → P.R.B) n (colv P ω A₀) h3.2
    (fun e he c => GlobalTheory.T.mem_span_restrictionLattice_columns l P r hr ω hω hdet' n U x y A₀ hA₀' W₀ hW₀ heq' _ (GlobalTheory.T.frobFixedLatticeCondition_smul_of_frobenius_fixed l P r n U x y _ e he (h3.1 c)))
  exact GlobalTheory.T.exists_frobeniusFixed_matrix_units_of_lattice_basis l P r ω hω hdet' n U x y hU A₀ hA₀' W₀ hW₀ heq' a hsp

end GlobalTheory.PMon

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeFrobFixedForallDegreeStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamentalLemmaLatticeFrobFixed_forall_degree : ∀ r : ℕ, FLAt r := by
  first | exact @GlobalTheory.PMon.flAt_all | exact GlobalTheory.PMon.flAt_all | (intros; apply GlobalTheory.PMon.flAt_all <;> assumption)
end
