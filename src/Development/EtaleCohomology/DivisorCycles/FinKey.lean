module

public import Development.EtaleCohomology.DivisorCycles.ChainPf
public import Development.EtaleCohomology.DivisorCycles.ConjugateIdempotents
public import Development.EtaleCohomology.DivisorCycles.UnitFactorizationTheorem
public import Development.EtaleCohomology.DivisorCycles.GenSpecProof

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PowEig
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qp8.Mat :
    Type → ℕ → Type :=
    fun (C : Type) (N : ℕ) ↦ Matrix (Fin N) (Fin N) C

theorem UpperTheory.Reformulated.B.Qp8.pow_eig :
    ∀ {C : Type} [inst : Field C] {N : ℕ} (y : UpperTheory.Reformulated.B.Qp8.Mat C N) (l : C) (w : Fin N → C),
      Matrix.mulVec y w = l • w → ∀ (m : ℕ), Matrix.mulVec (y ^ m) w = l ^ m • w := by
  intro C _ N y l w h m
  induction m with
  | zero => rw [pow_zero, pow_zero, one_smul, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
end

section -- merged from Development.EtaleCohomology.DivisorCycles.SumMulSum
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.KeyPf
open LateralTheory.DivDb

variable {C : Type} [Field C] {N n : ℕ}

theorem sum_mul_p {p : Fin n → Mat C N} (hS : Sys p) (d : Fin n → C) (k : Fin n) :
    (∑ j, d j • p j) * p k = d k • p k := by
  rw [Finset.sum_mul, Finset.sum_eq_single k]
  · rw [smul_mul_assoc, (hS.1.idem k).eq]
  · intro j _ hj; rw [smul_mul_assoc, hS.1.ortho hj, smul_zero]
  · simp

theorem p_mul_sum {p : Fin n → Mat C N} (hS : Sys p) (d : Fin n → C) (k : Fin n) :
    p k * (∑ j, d j • p j) = d k • p k := by
  rw [Finset.mul_sum, Finset.sum_eq_single k]
  · rw [mul_smul_comm, (hS.1.idem k).eq]
  · intro j _ hj; rw [mul_smul_comm, hS.1.ortho (Ne.symm hj), smul_zero]
  · simp

theorem sum_mul_sum {p : Fin n → Mat C N} (hS : Sys p) (d d' : Fin n → C) :
    (∑ j, d j • p j) * (∑ j, d' j • p j) = ∑ j, (d j * d' j) • p j := by
  rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc, p_mul_sum hS, smul_smul]

theorem sum_inv {p : Fin n → Mat C N} (hS : Sys p) (d : Fin n → C) (hd : ∀ j, d j ≠ 0) :
    (∑ j, d j • p j) * (∑ j, (d j)⁻¹ • p j) = 1 ∧ (∑ j, (d j)⁻¹ • p j) * (∑ j, d j • p j) = 1 := by
  rw [sum_mul_sum hS, sum_mul_sum hS]
  simp only [mul_inv_cancel₀ (hd _), inv_mul_cancel₀ (hd _), one_smul, hS.1.complete, and_self]

theorem sum_mem {p : Fin n → Mat C N} (A : Subalgebra C (Mat C N)) (hp : ∀ i, p i ∈ A) (d : Fin n → C) :
    (∑ j, d j • p j) ∈ A :=
  Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _ (hp j) _

theorem inv_in (A : Subalgebra C (Mat C N)) {v : Mat C N} (hvA : v ∈ A) (hv : IsUnit v) :
    ∃ w ∈ A, v * w = 1 := by
  let a : A := ⟨v, hvA⟩
  have hinj : Function.Injective A.val := Subtype.val_injective
  have ha : a ∈ nonZeroDivisors A := comap_nonZeroDivisors_le_of_injective hinj hv.mem_nonZeroDivisors
  haveI : Module.Finite C A := FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule A)
  have hu : IsUnit a := IsArtinianRing.isUnit_of_nonZeroDivisor_of_isIntegral' (R := C) ha
  obtain ⟨b, hb⟩ := hu
  refine ⟨((b⁻¹ : Aˣ) : A), ((b⁻¹ : Aˣ) : A).2, ?_⟩
  have := congrArg Subtype.val b.mul_inv
  rw [hb] at this; exact this

theorem zcl_sub (S : Set (Mat C N)) : S ⊆ Zcl S := fun x hx _ hf => hf x hx

theorem zcl_mono {S T : Set (Mat C N)} (h : S ⊆ T) : Zcl S ⊆ Zcl T :=
  fun y hy f hf => hy f fun x hx => hf x (h hx)

end LateralTheory.DivDb.KeyPf

namespace LateralTheory.DivDb.KeyPf
open LateralTheory.DivDb
variable {C : Type} [Field C] {N n : ℕ}

theorem sys_conj {p : Fin n → Mat C N} (hS : Sys p) (R Ri : Mat C N) (h1 : ∀ X, R * (Ri * X) = X)
    (h2 : ∀ X, Ri * (R * X) = X) : Sys (fun j => Ri * p j * R) := by
  have h2' : ∀ X, Ri * (R * X) = X := h2
  refine ⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i h => hS.2 i ?_⟩
  · show Ri * p i * R * (Ri * p i * R) = Ri * p i * R
    simp only [mul_assoc, h1]; rw [← mul_assoc (p i), (hS.1.idem i).eq]
  · show Ri * p i * R * (Ri * p j * R) = 0
    simp only [mul_assoc, h1]; rw [← mul_assoc (p i), hS.1.ortho hij]; simp
  · rw [← Finset.sum_mul, ← Finset.mul_sum, hS.1.complete, mul_one]
    have := h2 1; simpa using this
  · have := congrArg (fun Y => R * Y * Ri) h
    simp only [mul_assoc, h1, mul_zero, zero_mul] at this
    have e' : R * Ri = 1 := by simpa using h1 1
    rwa [e', mul_one] at this

theorem tv_zcl {ρS : Submonoid (Mat C N)} (hZM : ZclMul) (hUn : Unip) [CharZero C]
    (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N) (hS : Sys p)
    (hT : ∀ a ∈ A, ∀ j k, j ≠ k → p j * a * p k ∈ Tan (ρS : Set (Mat C N))) :
    ∀ u ∈ Tv A p, u ∈ Zcl (ρS : Set (Mat C N)) := by
  intro u hu
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, j, k, hjk, rfl⟩ := hx
    apply hUn C N ρS _ (hT a ha j k hjk)
    have : p k * p j = 0 := hS.1.ortho (Ne.symm hjk)
    calc p j * a * p k * (p j * a * p k) = p j * a * (p k * p j) * a * p k := by simp only [mul_assoc]
      _ = 0 := by rw [this]; simp
  | one => exact zcl_sub _ ρS.one_mem
  | mul x y _ _ hx hy => exact hZM C N ρS x hx y hy

theorem Key_of (hIC : IdemConj) (hMU : MatrixUnits₂) (hUF : UnitFactorization) (hTI : TanIndex) (hUn : Unip)
    (hZM : ZclMul) (hGS : GenSpec) (hTP : TorusPt) (hTD : TanDeg) (hCC : CycleCount) : Key := by
  intro Γ C _ _ _ _ N n ρ e p hDeg hLac hG U hU hUf g
  obtain ⟨hS, hX, hCo, hNN, hNo, _hKe, hOff⟩ := hG
  have hRiR : (ρ g⁻¹ : Mat C N) * (ρ g : Mat C N) = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hRRi : (ρ g : Mat C N) * (ρ g⁻¹ : Mat C N) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  set R : Mat C N := (ρ g : Mat C N) with hRdef
  set Ri : Mat C N := (ρ g⁻¹ : Mat C N) with hRidef
  have h1 : ∀ X, R * (Ri * X) = X := fun X => by rw [← mul_assoc, hRRi, one_mul]
  have h2 : ∀ X, Ri * (R * X) = X := fun X => by rw [← mul_assoc, hRiR, one_mul]
  set A := env ρ
  have hSq := sys_conj hS R Ri h1 h2
  have hCq : Corner A (fun j => Ri * p j * R) := by
    refine ⟨fun i => ?_, fun a ha i => ?_⟩
    · have := hNo g⁻¹ (p i) (hCo.1 i); rwa [inv_inv] at this
    · obtain ⟨c, hc⟩ := hCo.2 _ (hNo g a ha) i
      refine ⟨c, ?_⟩
      calc Ri * p i * R * a * (Ri * p i * R) = Ri * (p i * (R * a * Ri) * p i) * R := by
            simp only [mul_assoc]
        _ = c • (Ri * p i * R) := by rw [hc]; simp only [mul_smul_comm, smul_mul_assoc]
  obtain ⟨v, hvA, hvU, π, hvπ, hπ⟩ := hIC C N n A p _ hS hCo hSq hCq hNN
  obtain ⟨E, hE⟩ := hMU C N n A p hS hCo hNN
  obtain ⟨u, huT, d, hd, hvud⟩ := hUF C N n A p E hS hE v hvA hvU
  obtain ⟨hDD', hD'D⟩ := sum_inv hS d hd
  have hu : u = v * ∑ j, (d j)⁻¹ • p j := by rw [hvud, mul_assoc, hDD', mul_one]
  have hup : ∀ j, u * p j = Ri * p (π j) * R * u := by
    intro j
    have e1 : u * p j = v * ((d j)⁻¹ • p j) := by rw [hu, mul_assoc, sum_mul_p hS]
    have e2 : Ri * p (π j) * R * u = v * ((d j)⁻¹ • p j) := by
      rw [hu, ← mul_assoc, ← hvπ j, mul_assoc, p_mul_sum hS]
    rw [e1, e2]
  have hxp : ∀ j, R * u * p j = p (π j) * (R * u) := by
    intro j; rw [mul_assoc, hup]; simp only [mul_assoc, h1]
  have hD'U : IsUnit (∑ j, (d j)⁻¹ • p j) := ⟨⟨_, _, hD'D, hDD'⟩, rfl⟩
  have huU : IsUnit u := by rw [hu]; exact hvU.mul hD'U
  have hxU : IsUnit (R * u) := (Units.isUnit (ρ g)).mul huU
  obtain ⟨B, hBf, hB⟩ := hGS C N n p (R * u) π hS hxU hxp
  have hXT := hTI Γ C N ρ U hU hUf hX
  obtain ⟨τ, hτ, htZ, hτB⟩ := hTP C N n (img ρ U) p e hS hLac hXT B hBf
  have hdisj := hB τ hτ hτB
  obtain ⟨hTT', hT'T⟩ := sum_inv hS τ hτ
  set t := ∑ j, τ j • p j with htdef
  have huZ : u ∈ Zcl (img ρ U : Set (Mat C N)) :=
    tv_zcl hZM hUn A p hS (fun a ha j k hjk => hTI Γ C N ρ U hU hUf (hOff a ha j k hjk)) u huT
  have hmZ := hZM C N (img ρ U) u huZ t htZ
  have htU : IsUnit t := ⟨⟨_, _, hTT', hT'T⟩, rfl⟩
  have hyU : IsUnit (R * u * t) := hxU.mul htU
  have hyp : ∀ j, R * u * t * p j = p (π j) * (R * u * t) := by
    intro j
    rw [mul_assoc, sum_mul_p hS, ← mul_assoc (p _), ← hxp, mul_assoc, mul_assoc, p_mul_sum hS]
    simp only [mul_assoc]
  have himg : ∀ y ∈ img ρ U, y ∈ img ρ ⊤ := fun y hy => by
    obtain ⟨w, -, rfl⟩ := Submonoid.mem_map.mp hy
    exact Submonoid.mem_map.mpr ⟨w, by simp, rfl⟩
  have hdegS : ∀ x ∈ img ρ ⊤, Deg n x := fun x hx => by
    obtain ⟨w, -, rfl⟩ := Submonoid.mem_map.mp hx
    exact hDeg w
  have hRZ : R ∈ Zcl (img ρ ⊤ : Set (Mat C N)) :=
    zcl_sub _ (Submonoid.mem_map.mpr ⟨g, by simp, rfl⟩)
  have hyZ : R * u * t ∈ Zcl (img ρ ⊤ : Set (Mat C N)) := by
    rw [mul_assoc]; exact hZM C N _ R hRZ _ (zcl_mono himg hmZ)
  have hyDeg := (hTD C N n (img ρ ⊤) hdegS).1 _ hyZ
  obtain ⟨hEig, hfix⟩ := hCC C N n p (R * u * t) π hS hyU hyp hyDeg hdisj
  refine ⟨⟨u * t, hmZ, by rw [← mul_assoc]; exact hEig⟩, ?_⟩
  rintro i ⟨a, haA, hne⟩
  have ha' : Ri * a * R ∈ A := by have := hNo g⁻¹ a haA; rwa [inv_inv] at this
  have hπi : π i = i := by
    refine hπ i ⟨Ri * a * R, ha', fun h => hne ?_⟩
    have := congrArg (fun Y => R * Y) h
    simp only [mul_assoc, h1, mul_zero] at this
    simpa [mul_assoc] using this
  obtain ⟨c, hc⟩ := hfix i hπi
  have hpy : p i * (R * u * t) = c • p i := by rw [← hc, hyp i, hπi]
  obtain ⟨vi, hviA, hvvi⟩ := inv_in A hvA hvU
  set D := ∑ j, d j • p j
  set T' := ∑ j, (τ j)⁻¹ • p j
  have hm1 : u * t * (T' * D * vi) = 1 := by
    have ht' : ∀ X, t * (T' * X) = X := fun X => by rw [← mul_assoc, hTT', one_mul]
    have hd' : ∀ X, (∑ j, (d j)⁻¹ • p j) * (D * X) = X := fun X => by rw [← mul_assoc, hD'D, one_mul]
    rw [hu]; simp only [mul_assoc, ht', hd', hvvi]
  refine ⟨c • (T' * D * vi), Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
    (sum_mem A hCo.1 _) (sum_mem A hCo.1 _)) hviA) _, ?_⟩
  calc p i * R = p i * R * (u * t * (T' * D * vi)) := by rw [hm1, mul_one]
    _ = p i * (R * u * t) * (T' * D * vi) := by simp only [mul_assoc]
    _ = p i * (c • (T' * D * vi)) := by rw [hpy, smul_mul_assoc, mul_smul_comm]

end LateralTheory.DivDb.KeyPf
end

section -- merged from Development.EtaleCohomology.DivisorCycles.CycleCount2
open Matrix Polynomial
namespace LateralTheory.DivDb.CycleCount₂
open LateralTheory.DivDb

variable {C : Type} [Field C] {N : ℕ}

def fixSp (P : Mat C N) : Submodule C (Fin N → C) where
  carrier := {u | P *ᵥ u = u}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.mulVec_add, ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c u hu
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.mulVec_smul, hu]

theorem mem_fixSp {P : Mat C N} {u : Fin N → C} : u ∈ fixSp P ↔ P *ᵥ u = u := Iff.rfl

theorem eig_in [IsAlgClosed C] (W : Submodule C (Fin N → C)) (M : Mat C N)
    (hW : ∀ u ∈ W, M *ᵥ u ∈ W) (hne : ∃ u ∈ W, u ≠ 0) :
    ∃ u ∈ W, u ≠ 0 ∧ ∃ c : C, M *ᵥ u = c • u := by
  obtain ⟨u0, hu0, hu0'⟩ := hne
  have hW' : ∀ u ∈ W, Matrix.toLin' M u ∈ W := fun u hu => by
    rw [Matrix.toLin'_apply]; exact hW u hu
  let f : Module.End C W := (Matrix.toLin' M).restrict hW'
  have : Nontrivial W := ⟨⟨⟨u0, hu0⟩, 0, fun h => hu0' (by simpa using congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  refine ⟨x, x.2, fun h => hx.2 (Subtype.ext h), c, ?_⟩
  have := congrArg Subtype.val hx.apply_eq_smul
  simpa [f, LinearMap.restrict_apply, Matrix.toLin'_apply] using this

theorem eig_root (y : Mat C N) (l : C) (w : Fin N → C) (hw : w ≠ 0) (h : y *ᵥ w = l • w) :
    y.charpoly.IsRoot l := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly]
  apply (Matrix.exists_mulVec_eq_zero_iff).mp
  refine ⟨w, hw, ?_⟩
  rw [Matrix.sub_mulVec, h]
  simp [Matrix.scalar_apply, Pi.smul_def]

theorem pow_eig (y : Mat C N) (l : C) (w : Fin N → C) (h : y *ᵥ w = l • w) (m : ℕ) :
    (y ^ m) *ᵥ w = l ^ m • w :=
  _root_.UpperTheory.Reformulated.B.Qp8.pow_eig y l w h m

theorem aeval_eig (y : Mat C N) (l : C) (w : Fin N → C) (h : y *ᵥ w = l • w) (q : C[X]) :
    (aeval y q) *ᵥ w = q.eval l • w := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), Matrix.add_mulVec, hp, hq, eval_add, add_smul]
  | monomial n a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.smul_mulVec,
      pow_eig y l w h, smul_smul, eval_monomial]

theorem intertw {n : ℕ} (p : Fin n → Mat C N) (y : Mat C N) (π : Equiv.Perm (Fin n))
    (hπ : ∀ j, y * p j = p (π j) * y) (m : ℕ) (j : Fin n) : y ^ m * p j = p ((π ^ m) j) * y ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, hπ, mul_assoc, pow_succ', Equiv.Perm.mul_apply]

theorem move {n : ℕ} (p : Fin n → Mat C N) (y : Mat C N) (π : Equiv.Perm (Fin n))
    (hπ : ∀ j, y * p j = p (π j) * y) (m : ℕ) (j : Fin n) (v : Fin N → C) (hv : p j *ᵥ v = v) :
    p ((π ^ m) j) *ᵥ (y ^ m *ᵥ v) = y ^ m *ᵥ v := by
  conv_rhs => rw [← hv]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, intertw p y π hπ]

theorem cyc [IsAlgClosed C] [CharZero C] {n : ℕ} (p : Fin n → Mat C N) (y : Mat C N) (π : Equiv.Perm (Fin n))
    (hS : Sys p) (hy : IsUnit y) (hπ : ∀ j, y * p j = p (π j) * y) (j : Fin n) :
    ∃ S : Finset C, S.card = Function.minimalPeriod π j ∧ ∀ l ∈ S, ∃ w : Fin N → C, w ≠ 0 ∧
      y *ᵥ w = l • w ∧ ∀ k, ¬ π.SameCycle j k → p k *ᵥ w = 0 := by
  classical
  set k := Function.minimalPeriod π j with hkdef
  have hk : 0 < k := Function.minimalPeriod_pos_of_mem_periodicPts (π.injective.mem_periodicPts j)
  have hkj : (π ^ k) j = j := by rw [Equiv.Perm.coe_pow]; exact Function.isPeriodicPt_minimalPeriod π j
  have hne : ∀ m, 0 < m → m < k → (π ^ m) j ≠ j := fun m h0 h1 h =>
    Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod h0.ne' h1 (by rw [Equiv.Perm.coe_pow] at h; exact h)
  have hcomm : y ^ k * p j = p j * y ^ k := by rw [intertw p y π hπ, hkj]
  have hWm : ∀ u ∈ fixSp (p j), y ^ k *ᵥ u ∈ fixSp (p j) := by
    intro u hu; rw [mem_fixSp] at *; rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hu]
  have hWne : ∃ u ∈ fixSp (p j), u ≠ 0 := by
    by_contra hc; push_neg at hc
    apply hS.2 j
    refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
    rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply]
    exact hc _ (by rw [mem_fixSp, Matrix.mulVec_mulVec, (hS.1.idem j).eq])
  obtain ⟨v, hvW, hv0, β, hβ⟩ := eig_in _ _ hWm hWne
  rw [mem_fixSp] at hvW
  have hβ0 : β ≠ 0 := by
    rintro rfl
    apply hv0
    obtain ⟨U, hU⟩ := hy.pow k
    have h1 : ((U⁻¹ : (Mat C N)ˣ) : Mat C N) * (U : Mat C N) = 1 := U.inv_mul
    rw [← Matrix.one_mulVec v, ← h1, ← Matrix.mulVec_mulVec, hU, hβ, zero_smul, Matrix.mulVec_zero]
  refine ⟨(nthRoots k β).toFinset, ?_, ?_⟩
  · have hsep : (X ^ k - Polynomial.C β).Separable := separable_X_pow_sub_C β (by exact_mod_cast hk.ne') hβ0
    rw [Multiset.toFinset_card_of_nodup (by unfold nthRoots; exact nodup_roots hsep)]
    unfold nthRoots
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_X_pow_sub_C _]
  · intro l hl
    rw [Multiset.mem_toFinset, mem_nthRoots hk] at hl
    have hl0 : l ≠ 0 := by rintro rfl; rw [zero_pow hk.ne'] at hl; exact hβ0 hl.symm
    set a : ℕ → (Fin N → C) := fun m => (l⁻¹) ^ m • (y ^ m *ᵥ v) with ha
    have hya : ∀ m, y *ᵥ a m = l • a (m + 1) := by
      intro m; simp only [ha]
      rw [smul_smul, show l * (l⁻¹) ^ (m + 1) = (l⁻¹) ^ m by
        rw [pow_succ, mul_left_comm, mul_inv_cancel₀ hl0, mul_one], Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ']
    have hak : a k = a 0 := by
      simp only [ha]; rw [hβ, smul_smul, inv_pow, hl, inv_mul_cancel₀ hβ0, one_smul, pow_zero, pow_zero, one_smul,
        Matrix.one_mulVec]
    have hpa : ∀ i m, p i *ᵥ a m = if (π ^ m) j = i then a m else 0 := by
      intro i m; simp only [ha]; rw [Matrix.mulVec_smul]; split_ifs with h
      · subst h; rw [move p y π hπ m j v hvW]
      · rw [← move p y π hπ m j v hvW, Matrix.mulVec_mulVec, hS.1.ortho (Ne.symm h), Matrix.zero_mulVec, smul_zero]
    have hpj : p j *ᵥ ∑ m ∈ Finset.range k, a m = v := by
      rw [Matrix.mulVec_sum, Finset.sum_eq_single 0]
      · rw [hpa]; simp [ha]
      · intro m hm hm0; rw [hpa, if_neg]; exact hne m (Nat.pos_of_ne_zero hm0) (Finset.mem_range.mp hm)
      · intro h; exact absurd (Finset.mem_range.mpr hk) h
    refine ⟨∑ m ∈ Finset.range k, a m, ?_, ?_, ?_⟩
    · intro h; apply hv0; rw [← hpj, h, Matrix.mulVec_zero]
    · obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [Matrix.mulVec_sum, Finset.sum_congr rfl (fun m _ => hya m), ← Finset.smul_sum]
      congr 1
      rw [hk', Finset.sum_range_succ (fun m => a (m + 1)) k', Finset.sum_range_succ' a k', ← hk', hak]
    · intro i hi; rw [Matrix.mulVec_sum]; apply Finset.sum_eq_zero; intro m _; rw [hpa, if_neg]
      intro h; exact hi ⟨m, by rw [zpow_natCast]; exact h⟩

theorem eigs [IsAlgClosed C] [CharZero C] {n : ℕ} (p : Fin n → Mat C N) (y : Mat C N) (π : Equiv.Perm (Fin n))
    (hS : Sys p) (hy : IsUnit y) (hπ : ∀ j, y * p j = p (π j) * y) (hD : Disj y π p) :
    ∃ f : Fin n → C, Function.Injective f ∧ ∀ i, ∃ w : Fin N → C, w ≠ 0 ∧
      y *ᵥ w = f i • w ∧ ∀ k, ¬ π.SameCycle i k → p k *ᵥ w = 0 := by
  classical
  choose S hSc hSe using fun j => cyc p y π hS hy hπ j
  let rep : Fin n → Fin n := fun i => (@Quotient.mk _ (Equiv.Perm.SameCycle.setoid π) i).out
  have hrep : ∀ i, π.SameCycle (rep i) i := fun i => Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid π) i
  have hrepeq : ∀ i i', π.SameCycle i i' → rep i = rep i' := by
    intro i i' h
    exact congrArg Quotient.out (Quotient.sound (s := Equiv.Perm.SameCycle.setoid π) h)
  have hm : ∀ i, ∃ m, m < Function.minimalPeriod π (rep i) ∧ (π ^ m) (rep i) = i := by
    intro i; obtain ⟨m, hm⟩ := (hrep i).exists_nat_pow_eq
    refine ⟨m % Function.minimalPeriod π (rep i), Nat.mod_lt _
      (Function.minimalPeriod_pos_of_mem_periodicPts (π.injective.mem_periodicPts _)), ?_⟩
    rw [Equiv.Perm.coe_pow, Function.iterate_mod_minimalPeriod_eq, ← Equiv.Perm.coe_pow, hm]
  choose m hmlt hmeq using hm
  let g : Fin n → ℕ → C := fun r t => if h : t < (S r).card then ((S r).equivFin.symm ⟨t, h⟩ : C) else 0
  have hg : ∀ i, g (rep i) (m i) ∈ S (rep i) := by
    intro i; simp only [g]; rw [dite_eq_left (by rw [hSc]; exact hmlt i)]; exact Finset.coe_mem _
  have hsupp : ∀ i, ∃ w : Fin N → C, w ≠ 0 ∧ y *ᵥ w = g (rep i) (m i) • w ∧ ∀ k, ¬ π.SameCycle i k → p k *ᵥ w = 0 := by
    intro i; obtain ⟨w, hw0, hwe, hws⟩ := hSe _ _ (hg i)
    exact ⟨w, hw0, hwe, fun k hk => hws k (fun hc => hk ((hrep i).symm.trans hc))⟩
  refine ⟨fun i => g (rep i) (m i), ?_, hsupp⟩
  intro i i' h
  simp only at h
  have hsame : rep i = rep i' := by
    by_contra hne
    have hnc : ¬ π.SameCycle (rep i) (rep i') := fun hc =>
      hne (hrepeq _ _ (((hrep i).symm.trans hc).trans (hrep i')))
    obtain ⟨w, hw0, hwe, hws⟩ := hSe _ _ (hg i)
    obtain ⟨w', hw0', hwe', hws'⟩ := hSe _ _ (hg i')
    exact hD (rep i) (rep i') hnc _ w w' hw0 hw0' hwe (by rw [h]; exact hwe') hws hws'
  have hmm : m i = m i' := by
    have h2 := h
    simp only [g] at h2
    rw [dite_eq_left (by rw [hSc]; exact hmlt i), dite_eq_left (by rw [hSc]; exact hmlt i')] at h2
    have key : ∀ r r' : Fin n, r = r' → ∀ t t' (ht : t < (S r).card) (ht' : t' < (S r').card),
        ((S r).equivFin.symm ⟨t, ht⟩ : C) = (S r').equivFin.symm ⟨t', ht'⟩ → t = t' := by
      intro r r' hr; subst hr; intro t t' ht ht' he
      exact congrArg Fin.val ((S r).equivFin.symm.injective (Subtype.ext he))
    exact key _ _ hsame _ _ _ _ h2
  rw [← hmeq i, ← hmeq i', hsame, hmm]

theorem fixed_scalar [IsAlgClosed C] {n : ℕ} (p : Fin n → Mat C N) (y : Mat C N) (π : Equiv.Perm (Fin n))
    (hS : Sys p) (hπ : ∀ j, y * p j = p (π j) * y) (hdeg : Deg n y) (hD : Disj y π p)
    (f : Fin n → C) (hf : Function.Injective f) (hfe : ∀ i, ∃ w : Fin N → C, w ≠ 0 ∧
      y *ᵥ w = f i • w ∧ ∀ k, ¬ π.SameCycle i k → p k *ᵥ w = 0) (i : Fin n) (hi : π i = i) :
    ∃ c : C, y * p i = c • p i := by
  classical
  obtain ⟨q, hq0, hqd, hqy⟩ := hdeg
  have hroot : ∀ l (w : Fin N → C), w ≠ 0 → y *ᵥ w = l • w → q.eval l = 0 := by
    intro l w hw h
    have := aeval_eig y l w h q
    rw [hqy, Matrix.zero_mulVec] at this
    exact (smul_eq_zero.mp this.symm).resolve_right hw
  have hsub : Finset.univ.image f ⊆ q.roots.toFinset := by
    intro x hx
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw0, hwe, -⟩ := hfe i'
    rw [Multiset.mem_toFinset, mem_roots hq0]; exact hroot _ w hw0 hwe
  have hcard : (Finset.univ.image f).card = n := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have h1 : q.roots.toFinset.card ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
  have h2 : Multiset.card q.roots ≤ n := (Polynomial.card_roots' q).trans hqd
  have h3 := Finset.card_le_card hsub
  have hnd : q.roots.Nodup := Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega)
  have heq : Finset.univ.image f = q.roots.toFinset := Finset.eq_of_subset_of_card_le hsub (by omega)
  have honly : ∀ l (u : Fin N → C), u ≠ 0 → p i *ᵥ u = u → y *ᵥ u = l • u → l = f i := by
    intro l u hu hpu hyu
    have : l ∈ Finset.univ.image f := by
      rw [heq, Multiset.mem_toFinset, mem_roots hq0]; exact hroot l u hu hyu
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp this
    by_cases hc : π.SameCycle i i'
    · rw [hc.eq_of_left hi]
    · exfalso
      obtain ⟨w, hw0, hwe, hws⟩ := hfe i'
      refine hD i i' hc (f i') u w hu hw0 hyu hwe ?_ hws
      intro k hk
      have hki : k ≠ i := fun h => hk (h ▸ Equiv.Perm.SameCycle.refl _ _)
      rw [← hpu, Matrix.mulVec_mulVec, hS.1.ortho hki, Matrix.zero_mulVec]
  set l := f i
  have hlroot : q.IsRoot l := by obtain ⟨w, hw0, hwe, -⟩ := hfe i; exact hroot _ w hw0 hwe
  set q' := q /ₘ (X - Polynomial.C l)
  have hqq : q = q' * (X - Polynomial.C l) := by
    rw [mul_comm]; exact ((mul_divByMonic_eq_iff_isRoot).mpr hlroot).symm
  have hq'l : q'.eval l ≠ 0 := by
    intro h0
    have hdvd : (X - Polynomial.C l) ^ 2 ∣ q := by
      obtain ⟨r, hr⟩ := (Polynomial.dvd_iff_isRoot).mpr h0
      exact ⟨r, by rw [hqq, hr]; ring⟩
    have h4 := (le_rootMultiplicity_iff hq0).mpr hdvd
    rw [← count_roots] at h4
    have h5 := (Multiset.nodup_iff_count_le_one.mp hnd) l
    omega
  have hcomm : y * p i = p i * y := by rw [hπ, hi]
  have hc2 : aeval y q' * y = y * aeval y q' := by
    have := congrArg (aeval y) (mul_comm q' X)
    simpa [aeval_X] using this
  have hinj : ∀ u, p i *ᵥ u = u → aeval y q' *ᵥ u = 0 → u = 0 := by
    intro u hu hq'u
    by_contra hu0
    let W : Submodule C (Fin N → C) := fixSp (p i) ⊓ LinearMap.ker (Matrix.toLin' (aeval y q'))
    have hWm : ∀ x ∈ W, y *ᵥ x ∈ W := by
      intro x hx
      rw [Submodule.mem_inf, mem_fixSp, LinearMap.mem_ker, Matrix.toLin'_apply] at hx ⊢
      refine ⟨?_, ?_⟩
      · rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hx.1]
      · rw [Matrix.mulVec_mulVec, hc2, ← Matrix.mulVec_mulVec, hx.2, Matrix.mulVec_zero]
    obtain ⟨u', hu'W, hu'0, c, hc⟩ := eig_in W y hWm ⟨u, by
      rw [Submodule.mem_inf, mem_fixSp, LinearMap.mem_ker, Matrix.toLin'_apply]; exact ⟨hu, hq'u⟩, hu0⟩
    rw [Submodule.mem_inf, mem_fixSp, LinearMap.mem_ker, Matrix.toLin'_apply] at hu'W
    have hcl : c = l := honly c u' hu'0 hu'W.1 hc
    have h6 := aeval_eig y c u' hc q'
    rw [hu'W.2, hcl] at h6
    exact hq'l ((smul_eq_zero.mp h6.symm).resolve_right hu'0)
  refine ⟨l, ?_⟩
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun u => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec]
  have hc3 : p i * (y - l • 1) = (y - l • 1) * p i := by
    rw [mul_sub, sub_mul, ← hcomm, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have h4 : aeval y q' * (y - l • 1) = 0 := by
    rw [← hqy, hqq, map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  have hz := hinj ((y - l • 1) *ᵥ (p i *ᵥ u)) (by
      simp only [Matrix.mulVec_mulVec]; rw [← mul_assoc, hc3, mul_assoc, (hS.1.idem i).eq])
    (by simp only [Matrix.mulVec_mulVec]; rw [← mul_assoc, h4, Matrix.zero_mul, Matrix.zero_mulVec])
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, Matrix.mulVec_mulVec] at hz
  exact hz

theorem CycleCount_of : CycleCount := by
  intro C _ _ _ N n p y π hS hy hπ hdeg hD
  obtain ⟨f, hf, hfe⟩ := eigs p y π hS hy hπ hD
  refine ⟨⟨f, hf, fun i => ?_⟩, fun i hi => fixed_scalar p y π hS hπ hdeg hD f hf hfe i hi⟩
  obtain ⟨w, hw0, hwe, -⟩ := hfe i
  exact eig_root y _ w hw0 hwe

end LateralTheory.DivDb.CycleCount₂
end

section -- merged from Development.EtaleCohomology.DivisorCycles.TangentIndexDvd
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb
namespace TangentIndexDvd

section
variable {C : Type} [Field C] {N : ℕ}

theorem subset_zcl (S : Set (Mat C N)) : S ⊆ Zcl S := fun _ hx _ hf => hf _ hx

theorem ev_mul (x : Mat C N) (f g : MP C N) : ev x (f * g) = ev x f * ev x g := by
  simp only [ev, map_mul]

theorem ev_prod {ι : Type} (s : Finset ι) (x : Mat C N) (q : ι → MP C N) :
    ev x (∏ c ∈ s, q c) = ∏ c ∈ s, ev x (q c) := by
  simp only [ev, map_prod]

theorem dAt_mul (f g : MP C N) (x Y : Mat C N) :
    dAt (f * g) x Y = ev x f * dAt g x Y + ev x g * dAt f x Y := by
  unfold dAt
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Derivation.leibniz]
  simp only [ev, smul_eq_mul, map_add (f := _), map_mul]
  ring

theorem mem_img {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C) (U : Subgroup Γ) (x : Mat C N) :
    x ∈ img ρ U ↔ ∃ u ∈ U, ((ρ u : GL (Fin N) C) : Mat C N) = x := by
  simp [img, Submonoid.mem_map]

theorem coset_poly {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C) (U : Subgroup Γ) [U.Normal]
    [U.FiniteIndex] (hChain : Chain) (hMul : ZclMul) (f : MP C N)
    (hf : f ∈ Van (img ρ U : Set (Mat C N))) (g : Γ) :
    ∃ q : MP C N, ev 1 q ≠ 0 ∧ ∀ γ : Γ, (γ : Γ ⧸ U) = (g : Γ ⧸ U) →
      ev ((ρ γ : GL (Fin N) C) : Mat C N) (f * q) = 0 := by
  by_cases h : ∃ q : MP C N, ev 1 q ≠ 0 ∧ ∀ γ : Γ, (γ : Γ ⧸ U) = (g : Γ ⧸ U) →
      ev ((ρ γ : GL (Fin N) C) : Mat C N) q = 0
  · obtain ⟨q, hq1, hq⟩ := h
    exact ⟨q, hq1, fun γ hγ => by rw [ev_mul, hq γ hγ, mul_zero]⟩
  have h' : ∀ q : MP C N, (∀ γ : Γ, (γ : Γ ⧸ U) = (g : Γ ⧸ U) →
      ev ((ρ γ : GL (Fin N) C) : Mat C N) q = 0) → ev 1 q = 0 := fun q hq => by
    by_contra hne; exact h ⟨q, hne, hq⟩
  have hinv : ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) ∈ Zcl (img ρ U : Set (Mat C N)) := by
    intro h0 hh0
    obtain ⟨h1, hev, -⟩ := hChain C N N (LinearMap.mulLeft C ((ρ g⁻¹ : GL (Fin N) C) : Mat C N)) h0
    have key := h' h1 (fun γ hγ => by
      rw [hev, LinearMap.mulLeft_apply]
      apply hh0
      rw [SetLike.mem_coe, mem_img]
      refine ⟨g⁻¹ * γ, QuotientGroup.eq.mp hγ.symm, ?_⟩
      rw [map_mul, Units.val_mul])
    rwa [hev, LinearMap.mulLeft_apply, mul_one] at key
  obtain ⟨k, hk, hkU⟩ : ∃ k : ℕ, 0 < k ∧ g ^ k ∈ U := by
    have : Finite (Γ ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
    refine ⟨orderOf (g : Γ ⧸ U), orderOf_pos _, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, pow_orderOf_eq_one]
  have hpow : ∀ m : ℕ, ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) ^ m ∈ Zcl (img ρ U : Set (Mat C N)) := by
    intro m
    induction m with
    | zero => rw [pow_zero]; exact subset_zcl _ (img ρ U).one_mem
    | succ m ih => rw [pow_succ]; exact hMul C N _ _ ih _ hinv
  have hg : ((ρ g : GL (Fin N) C) : Mat C N) ∈ Zcl (img ρ U : Set (Mat C N)) := by
    have e : ((ρ g : GL (Fin N) C) : Mat C N) = ((ρ (g ^ k) : GL (Fin N) C) : Mat C N) *
        ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) ^ (k - 1) := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← map_pow, ← map_mul]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      congr 2
      simp [pow_succ', mul_assoc, inv_pow]
    rw [e]
    exact hMul C N _ _ (subset_zcl _ ((mem_img ρ U _).2 ⟨_, hkU, rfl⟩)) _ (hpow _)
  refine ⟨1, by simp [ev], fun γ hγ => ?_⟩
  rw [mul_one]
  have hγU : g⁻¹ * γ ∈ U := QuotientGroup.eq.mp hγ.symm
  have e : ((ρ γ : GL (Fin N) C) : Mat C N) = ((ρ g : GL (Fin N) C) : Mat C N) *
      ((ρ (g⁻¹ * γ) : GL (Fin N) C) : Mat C N) := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  rw [e]
  exact hMul C N _ _ hg _ (subset_zcl _ ((mem_img ρ U _).2 ⟨_, hγU, rfl⟩)) f hf

end

theorem TanIndex_of (hChain : Chain) (hMul : ZclMul) : TanIndex := by
  classical
  intro Γ C _ _ N ρ U hN hU Y hY
  have : Finite (Γ ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (Γ ⧸ U) := Fintype.ofFinite _
  have hY' : ∀ F ∈ Van (img ρ ⊤ : Set (Mat C N)), dAt F 1 Y = 0 := hY
  show ∀ f ∈ Van (img ρ U : Set (Mat C N)), dAt f 1 Y = 0
  intro f hf
  have hc : ∀ c : Γ ⧸ U, ∃ q : MP C N, ev 1 q ≠ 0 ∧ ∀ γ : Γ, (γ : Γ ⧸ U) = c →
      ev ((ρ γ : GL (Fin N) C) : Mat C N) (f * q) = 0 := by
    intro c
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    exact coset_poly ρ U hChain hMul f hf g
  choose q hq1 hq using hc
  have hF : f * ∏ c, q c ∈ Van (img ρ ⊤ : Set (Mat C N)) := by
    intro x hx
    obtain ⟨γ, -, rfl⟩ := (mem_img ρ ⊤ x).1 hx
    have h0 := hq (γ : Γ ⧸ U) γ rfl
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (γ : Γ ⧸ U)), ← mul_assoc,
      ev_mul, h0, zero_mul]
  have key := hY' _ hF
  rw [dAt_mul] at key
  have hf1 : ev 1 f = 0 := hf 1 (img ρ U).one_mem
  have hG1 : ev 1 (∏ c, q c) ≠ 0 := by
    rw [ev_prod]; exact Finset.prod_ne_zero_iff.2 fun c _ => hq1 c
  rw [hf1, zero_mul, zero_add] at key
  exact (mul_eq_zero.1 key).resolve_left hG1

end TangentIndexDvd
end LateralTheory.DivDb
end

section -- merged from Development.EtaleCohomology.DivisorCycles.UnipotentPartTrivial
open Matrix
namespace LateralTheory.DivDb.UnipotentPartTrivial
open LateralTheory.DivDb

theorem pow_vanish {C : Type} [Field C] {N : ℕ} (E : Mat C N) (h : E * E = 0) (k : ℕ) (hk : 2 ≤ k) :
    E ^ k = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, sq, h, zero_mul]

theorem series_eq {C : Type} [Field C] {N : ℕ} (E : Mat C N) (h : E * E = 0) (p : Fin N × Fin N) :
    PowerSeries.mk (fun k => ((k.factorial : C)⁻¹ • E ^ k) p.1 p.2)
      = ((Polynomial.C ((1 : Mat C N) p.1 p.2) + Polynomial.X * Polynomial.C (E p.1 p.2) : Polynomial C) :
          PowerSeries C) := by
  ext k
  rw [PowerSeries.coeff_mk, Polynomial.coeff_coe]
  rcases k with _ | _ | k
  · simp
  · simp
  · rw [pow_vanish E h _ (by omega)]
    simp

theorem Unip_of (h : ExpVan) : Unip := by
  intro C _ _ N S E hE hEE f hf
  have h0 := h C N S E hE f hf
  let g : Fin N × Fin N → Polynomial C := fun p =>
    Polynomial.C ((1 : Mat C N) p.1 p.2) + Polynomial.X * Polynomial.C (E p.1 p.2)
  have h1 : MvPolynomial.aeval g f = 0 := by
    apply Polynomial.coe_injective
    rw [Polynomial.coe_zero]
    have hc := congrArg (fun φ => φ f)
      (MvPolynomial.comp_aeval (R := C) g (Polynomial.coeToPowerSeries.algHom C))
    simp only [AlgHom.comp_apply] at hc
    simp only [Polynomial.coeToPowerSeries.algHom_apply, PowerSeries.map_id, Algebra.algebraMap_self] at hc
    simp only [id] at hc
    have hs : (fun p : Fin N × Fin N => PowerSeries.mk (fun k => ((k.factorial : C)⁻¹ • E ^ k) p.1 p.2))
        = fun i => ((g i : Polynomial C) : PowerSeries C) := funext (series_eq E hEE)
    rw [hs] at h0
    exact hc.trans h0
  have h2 := congrArg (fun q => Polynomial.aeval (1 : C) q) h1
  simp only [map_zero] at h2
  have hc := congrArg (fun φ => φ f) (MvPolynomial.comp_aeval (R := C) g (Polynomial.aeval (1 : C)))
  simp only [AlgHom.comp_apply] at hc
  rw [hc] at h2
  have h3 : (fun p : Fin N × Fin N => Polynomial.aeval (1 : C) (g p)) = fun p => (1 + E) p.1 p.2 := by
    funext p; simp [g]
  rw [h3] at h2
  unfold ev
  exact h2

end LateralTheory.DivDb.UnipotentPartTrivial
end

section -- merged from Development.EtaleCohomology.DivisorCycles.TorusPtPf
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.TorusPtPf
open LateralTheory.DivDb

variable {C : Type} [Field C] [CharZero C]

noncomputable def E (a : C) : PowerSeries C := PowerSeries.rescale a (PowerSeries.exp C)

lemma coeff_E (a : C) (k : ℕ) : PowerSeries.coeff k (E a) = a ^ k * (k.factorial : C)⁻¹ := by
  simp [E, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]

lemma E_add (a b : C) : E a * E b = E (a + b) := PowerSeries.exp_mul_exp_eq_exp_add a b

lemma E_zero : E (0 : C) = 1 := by
  ext k; rcases k with _ | k <;> simp [coeff_E, PowerSeries.coeff_one]

lemma E_prod {ι : Type} (s : Finset ι) (a : ι → C) : ∏ i ∈ s, E (a i) = E (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [E_zero]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, E_add]

lemma E_pow (a : C) (m : ℕ) : E a ^ m = E ((m : C) * a) := by
  induction m with
  | zero => simp [E_zero]
  | succ m ih => rw [pow_succ, ih, E_add]; congr 1; push_cast; ring

lemma E_ne (a b c : C) (h : E a - PowerSeries.C b * E c = 0) : b = 1 ∧ a = c := by
  have h0 := congrArg (PowerSeries.coeff 0) h
  have h1 := congrArg (PowerSeries.coeff 1) h
  simp only [map_sub, PowerSeries.coeff_C_mul, coeff_E, map_zero] at h0 h1
  simp at h0 h1
  have hb : b = 1 := by linear_combination -h0
  refine ⟨hb, ?_⟩
  rw [hb] at h1
  linear_combination h1

lemma pow_sys {N n : ℕ} {p : Fin n → Mat C N} (hp : Sys p) (e : Fin n → C) (k : ℕ) :
    (∑ i, e i • p i) ^ k = ∑ i, e i ^ k • p i := by
  induction k with
  | zero => simpa using hp.1.complete.symm
  | succ k ih =>
    rw [pow_succ, ih, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [smul_mul_smul_comm, (hp.1.idem i).eq, pow_succ]
    · intro j _ hji; rw [smul_mul_smul_comm, hp.1.ortho hji.symm, smul_zero]
    · simp

lemma entry_exp {N n : ℕ} {p : Fin n → Mat C N} (hp : Sys p) (e : Fin n → C) (a b : Fin N) :
    (PowerSeries.mk fun k => ((k.factorial : C)⁻¹ • (∑ i, e i • p i) ^ k) a b) =
      ∑ j, PowerSeries.C (p j a b) * E (e j) := by
  ext k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_C_mul, coeff_E, pow_sys hp, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

noncomputable def bin {n : ℕ} (q : Finset (Fin n) × Finset (Fin n) × C) : MvPolynomial (Fin n) C :=
  (∏ i ∈ q.1, MvPolynomial.X i) ^ q.2.1.card - MvPolynomial.C q.2.2 * (∏ i ∈ q.2.1, MvPolynomial.X i) ^ q.1.card

theorem TorusPt_of (hE : ExpVan) (hS : SpecPt) : TorusPt := by
  intro C _ _ _ N n S p e hp hlac hX B hB
  classical
  let x : Fin n → PowerSeries C := fun j => E (e j)
  let Q : Set (Finset (Fin n) × Finset (Fin n) × C) :=
    {q | q.1.Nonempty ∧ q.2.1.Nonempty ∧ Disjoint q.1 q.2.1 ∧ q.2.2 ∈ B}
  let G : Set (MvPolynomial (Fin n) C) := Set.range (fun j => MvPolynomial.X j) ∪ bin '' Q
  have hQ : Q.Finite := (Set.finite_univ.prod (Set.finite_univ.prod hB)).subset fun q hq => by
    simp only [Set.mem_prod, Set.mem_univ, true_and]; exact hq.2.2.2
  have hG : G.Finite := (Set.finite_range _).union (hQ.image _)
  have hxg : ∀ g ∈ G, MvPolynomial.aeval x g ≠ 0 := by
    rintro g (⟨j, rfl⟩ | ⟨q, ⟨h1, h2, h3, h4⟩, rfl⟩)
    · intro h0
      have := congrArg (PowerSeries.coeff 0) h0
      simp [x, coeff_E] at this
    · intro h0
      simp only [bin, map_sub, map_mul, map_pow, map_prod, MvPolynomial.aeval_X, MvPolynomial.aeval_C, x, E_prod,
        E_pow] at h0
      have h0' : E ((q.2.1.card : C) * ∑ i ∈ q.1, e i) - PowerSeries.C q.2.2 * E ((q.1.card : C) * ∑ i ∈ q.2.1, e i) = 0 := by
        simpa using h0
      exact hlac _ _ h1 h2 h3 (E_ne _ _ _ h0').2
  obtain ⟨y, hy1, hy2⟩ := hS C (PowerSeries C) (Fin n) x G hG hxg
  refine ⟨y, fun j => ?_, fun f hf => ?_, fun O O' hO hO' hd b hb => ?_⟩
  · have := hy2 _ (Or.inl ⟨j, rfl⟩); simpa using this
  · have h := hE C N S _ hX f hf
    have hent : (fun ab : Fin N × Fin N => PowerSeries.mk fun k =>
          ((k.factorial : C)⁻¹ • (∑ i, e i • p i) ^ k) ab.1 ab.2)
        = fun ab => MvPolynomial.aeval x (∑ j, MvPolynomial.C (p j ab.1 ab.2) * MvPolynomial.X j) := by
      funext ab; rw [entry_exp hp]; simp [x]
    rw [hent, ← MvPolynomial.aeval_bind₁] at h
    have h2 := hy1 _ h
    have h3 : MvPolynomial.aeval y
        ((MvPolynomial.bind₁ fun ab : Fin N × Fin N => ∑ j, MvPolynomial.C (p j ab.1 ab.2) * MvPolynomial.X j) f) = 0 := by
      exact h2
    rw [MvPolynomial.aeval_bind₁] at h3
    unfold ev
    rw [show (fun q : Fin N × Fin N => (∑ j, y j • p j) q.1 q.2) = fun ab =>
        MvPolynomial.aeval y (∑ j, MvPolynomial.C (p j ab.1 ab.2) * MvPolynomial.X j) from
      funext fun ab => by simp [Matrix.sum_apply, mul_comm]]
    exact h3
  · intro h
    apply hy2 _ (Or.inr ⟨(O, O', b), ⟨hO, hO', hd, hb⟩, rfl⟩)
    simp only [bin, map_sub, map_mul, map_pow, map_prod, MvPolynomial.eval_X, MvPolynomial.eval_C]
    rw [h]; ring
end LateralTheory.DivDb.TorusPtPf
end

section -- merged from Development.EtaleCohomology.DivisorCycles.ZclMulPf
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.ZclMulPf
open LateralTheory.DivDb

theorem left_mem (hC : Chain) {C : Type} [Field C] {N : ℕ} (S : Submonoid (Mat C N))
    (s : Mat C N) (hs : s ∈ S) (y : Mat C N) (hy : y ∈ Zcl (S : Set (Mat C N))) :
    s * y ∈ Zcl (S : Set (Mat C N)) := by
  intro f hf
  obtain ⟨f', hf', -⟩ := hC C N N (LinearMap.mulLeft C s) f
  have hv : f' ∈ Van (S : Set (Mat C N)) := by
    intro t ht
    rw [hf']
    exact hf _ (S.mul_mem hs ht)
  have := hy f' hv
  rw [hf'] at this
  simpa using this

theorem mul_mem (hC : Chain) {C : Type} [Field C] {N : ℕ} (S : Submonoid (Mat C N))
    (x : Mat C N) (hx : x ∈ Zcl (S : Set (Mat C N))) (y : Mat C N) (hy : y ∈ Zcl (S : Set (Mat C N))) :
    x * y ∈ Zcl (S : Set (Mat C N)) := by
  intro f hf
  obtain ⟨f', hf', -⟩ := hC C N N (LinearMap.mulRight C y) f
  have hv : f' ∈ Van (S : Set (Mat C N)) := by
    intro t ht
    rw [hf']
    exact left_mem hC S t ht y hy f hf
  have := hx f' hv
  rw [hf'] at this
  simpa using this

end LateralTheory.DivDb.ZclMulPf

namespace LateralTheory.DivDb

theorem ZclMul_of (hC : Chain) : ZclMul := fun _C _ _N S x hx y hy =>
  LateralTheory.DivDb.ZclMulPf.mul_mem hC S x hx y hy

end LateralTheory.DivDb
end

namespace LateralTheory.Fin.Key
theorem etale_matrix_units_system_of_key : LateralTheory.DivDb.MatrixUnits₂ := by
  apply LateralTheory.DivDb.MatrixUnitConstruction.MatUnits_of
theorem etale_idempotent_conjugacy_of_key : LateralTheory.DivDb.IdemConj := by
  apply LateralTheory.DivDb.ConjugateIdempotents.IdemConj_of <;> first | exact etale_matrix_units_system_of_key
theorem etale_unit_factorization_of_key : LateralTheory.DivDb.UnitFactorization := by
  apply LateralTheory.DivDb.UnitFactorizationTheorem.UnitFactor_of
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
theorem etale_zariski_closure_mul_closed_of_key : LateralTheory.DivDb.ZclMul := by
  apply LateralTheory.DivDb.ZclMul_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_tangent_index_divides_of_key : LateralTheory.DivDb.TanIndex := by
  apply LateralTheory.DivDb.TangentIndexDvd.TanIndex_of <;> first | exact etale_divisibility_chain_of_key | exact etale_zariski_closure_mul_closed_of_key
theorem etale_tangent_field_extension_of_key : LateralTheory.DivDb.TanField := by
  apply LateralTheory.DivDb.TangentFieldExtension.TanField_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_exponent_vanishing_of_key : LateralTheory.DivDb.ExpVan := by
  apply LateralTheory.DivDb.ExpVan_of <;> first | exact etale_tangent_field_extension_of_key
theorem etale_unipotent_part_trivial_of_key : LateralTheory.DivDb.Unip := by
  apply LateralTheory.DivDb.UnipotentPartTrivial.Unip_of <;> first | exact etale_exponent_vanishing_of_key
theorem etale_generic_spectrum_of_key : LateralTheory.DivDb.GenSpec := by
  apply LateralTheory.DivDb.GenSpecProof.GenSpec_of
theorem etale_special_point_exists_of_key : LateralTheory.DivDb.SpecPt := by
  apply LateralTheory.DivDb.SpecPtPf.SpecPt_of
theorem etale_torus_point_exists_of_key : LateralTheory.DivDb.TorusPt := by
  apply LateralTheory.DivDb.TorusPtPf.TorusPt_of <;> first | exact etale_exponent_vanishing_of_key | exact etale_special_point_exists_of_key
theorem etale_degree_polynomial_bound : LateralTheory.DivDb.DegPoly := by
  apply LateralTheory.DivDb.DegPoly₂.DegPoly_of
theorem etale_tangent_degree_bound_of_key : LateralTheory.DivDb.TanDeg := by
  apply LateralTheory.DivDb.TangentDegree.TanDeg_of <;> first | exact etale_exponent_vanishing_of_key | exact etale_degree_polynomial_bound
theorem etale_cycle_count_eigenvalues_of_key : LateralTheory.DivDb.CycleCount := by
  apply LateralTheory.DivDb.CycleCount₂.CycleCount_of
theorem etale_divisibility_key_criterion_of_components : LateralTheory.DivDb.Key := by
  apply LateralTheory.DivDb.KeyPf.Key_of <;> first | exact etale_idempotent_conjugacy_of_key | exact etale_matrix_units_system_of_key | exact etale_unit_factorization_of_key | exact etale_tangent_index_divides_of_key | exact etale_unipotent_part_trivial_of_key | exact etale_zariski_closure_mul_closed_of_key | exact etale_generic_spectrum_of_key | exact etale_torus_point_exists_of_key | exact etale_tangent_degree_bound_of_key | exact etale_cycle_count_eigenvalues_of_key
theorem intersectionNumber_baseChange : LateralTheory.DivDb.Key := etale_divisibility_key_criterion_of_components
end LateralTheory.Fin.Key
