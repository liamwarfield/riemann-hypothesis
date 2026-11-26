module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedSubgroupColumnMatricesEntryZero
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedSubgroupColumnMatricesEntryZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PosAgree

open Matrix

variable {k : Type} [CommRing k] {n : ℕ}

theorem vmv_mul_vmv (a α b β : Fin n → k) :
    vecMulVec a α * vecMulVec b β = (α ⬝ᵥ b) • vecMulVec a β := by
  ext i l
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem mul_vmv_mul (A B : Matrix (Fin n) (Fin n) k) (w φ : Fin n → k) :
    A * vecMulVec w φ * B = vecMulVec (A *ᵥ w) (φ ᵥ* B) := by
  ext i l
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun m _ => by ring

theorem vecMul_vmv (φ a α : Fin n → k) : φ ᵥ* vecMulVec a α = (φ ⬝ᵥ a) • α := by
  ext i
  simp only [vecMul, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

def tU (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) : GL (Fin n) k :=
  ⟨1 + vecMulVec v φ, 1 - vecMulVec v φ,
    by simp only [add_mul, mul_sub, one_mul, mul_one, vmv_mul_vmv, h, zero_smul]; abel,
    by simp only [sub_mul, mul_add, one_mul, mul_one, vmv_mul_vmv, h, zero_smul]; abel⟩

theorem tU_val (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) : (tU v φ h).val = 1 + vecMulVec v φ := rfl

theorem tU_inv_val (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) : (tU v φ h)⁻¹.val = 1 - vecMulVec v φ := rfl

theorem conj_val (g : GL (Fin n) k) (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) :
    (g * tU v φ h * g⁻¹).val = 1 + vecMulVec (g.val *ᵥ v) (φ ᵥ* (g⁻¹).val) := by
  rw [Units.val_mul, Units.val_mul, tU_val, mul_add, add_mul, mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    mul_vmv_mul]

theorem tU_mem_unip (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) (hl : ∀ i l : Fin n, l.val ≤ i.val → v i * φ l = 0) :
    tU v φ h ∈ unip k n := by
  refine ⟨fun i l (hli : l.val < i.val) => ?_, fun i => ?_⟩
  · rw [tU_val, Matrix.add_apply, vecMulVec_apply, hl i l hli.le, one_apply_ne (fun e => by rw [e] at hli; omega), add_zero]
  · rw [tU_val, Matrix.add_apply, vecMulVec_apply, hl i i le_rfl, one_apply_eq, add_zero]

theorem transvection_eq (i j : Fin n) (c : k) :
    transvection i j c = 1 + vecMulVec (Pi.single i c) (Pi.single j 1) := by
  unfold transvection
  congr 1
  ext p q
  simp only [single_apply, vecMulVec_apply, Pi.single_apply]
  split_ifs <;> simp_all

end GlobalTheory.PosAgree

namespace GlobalTheory.PosAgree

open Matrix

variable {k : Type} [CommRing k] {n : ℕ}

theorem sdot (p q : Fin n) (x : k) (h : q ≠ p) : Pi.single q 1 ⬝ᵥ Pi.single p x = 0 := by
  rw [single_dotProduct, Pi.single_apply, if_neg h, mul_zero]

theorem comm_a (p0 p1 pm : Fin n) (h01 : p0 ≠ p1) (h0m : p0 ≠ pm) (h1m : p1 ≠ pm) :
    (tU (Pi.single pm (1 : k)) (Pi.single p0 1) (sdot _ _ _ h0m))⁻¹ *
      (tU (Pi.single p0 1) (Pi.single p1 1) (sdot _ _ _ h01.symm) * tU (Pi.single pm 1) (Pi.single p0 1) (sdot _ _ _ h0m) *
        (tU (Pi.single p0 1) (Pi.single p1 1) (sdot _ _ _ h01.symm))⁻¹) =
      tU (Pi.single pm (-1)) (Pi.single p1 1) (sdot _ _ _ h1m) := by
  apply Units.ext
  simp only [Units.val_mul, tU_val, tU_inv_val, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, vmv_mul_vmv,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, single_dotProduct, Pi.single_apply, h01, h0m, h1m, h01.symm, h0m.symm, h1m.symm,
    if_false, if_true, mul_zero, zero_smul, add_zero, sub_zero, zero_mul, mul_one]
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp_all

theorem comm_b (p0 p1 pm : Fin n) (h01 : p0 ≠ p1) (h0m : p0 ≠ pm) (h1m : p1 ≠ pm) (a b : k) :
    tU (Pi.single p0 a) (Pi.single pm 1) (sdot _ _ _ h0m.symm) * tU (Pi.single pm b) (Pi.single p1 1) (sdot _ _ _ h1m) *
      (tU (Pi.single p0 a) (Pi.single pm 1) (sdot _ _ _ h0m.symm))⁻¹ * (tU (Pi.single pm b) (Pi.single p1 1) (sdot _ _ _ h1m))⁻¹ =
      tU (Pi.single p0 (a * b)) (Pi.single p1 1) (sdot _ _ _ h01.symm) := by
  apply Units.ext
  simp only [Units.val_mul, tU_val, tU_inv_val, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, vmv_mul_vmv,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, single_dotProduct, Pi.single_apply, h01, h0m, h1m, h01.symm, h0m.symm, h1m.symm,
    if_false, if_true, mul_zero, zero_smul, add_zero, sub_zero, zero_mul, mul_one]
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp_all [mul_comm]

end GlobalTheory.PosAgree

namespace GlobalTheory.PosAgree

open Matrix

theorem entry_zero : ∀ (k : Type) [CommRing k], IsField k → ∀ n r : ℕ, 2 ≤ r → r < n → ∀ (H : Subgroup (GL (Fin n) k)) (b : GL (Fin n) k), (∀ u ∈ unip k n, ∀ h ∈ H, u * h * u⁻¹ ∈ H) → (∀ (h : GL (Fin n) k) (m : Fin n) (v : Fin n → k), r ≤ (m : ℕ) → v m = 0 → h.val = colMat v m → h ∈ H) → (∀ (h : GL (Fin n) k) (m : Fin n) (v : Fin n → k), r ≤ (m : ℕ) → v m = 0 → (b * h * b⁻¹).val = colMat v m → h ∈ H) → (∀ i j : Fin n, (i : ℕ) + 1 = j → (j : ℕ) < r → ∃ (c : k) (h : GL (Fin n) k), h.val = Matrix.transvection i j c ∧ h ∉ H) → ∀ a c : Fin n, r ≤ (a : ℕ) → (c : ℕ) < r → b.val a c = 0 := by
  intro k _ hk n r hr hrn H b hU h2 h3 h4 a c ha hc
  classical
  by_contra hne
  have ofVal : ∀ (g h : GL (Fin n) k), g ∈ H → g.val = h.val → h ∈ H := fun g h hg e => (Units.ext e) ▸ hg
  have H4 : ∀ i j : Fin n, i.val + 1 = j.val → j.val < r →
      (∀ x : k, ∃ hx, tU (Pi.single i x) (Pi.single j 1) hx ∈ H) → False := by
    intro i j hij hj hall
    obtain ⟨x, h, hh, hn⟩ := h4 i j hij hj
    obtain ⟨hx, hm⟩ := hall x
    exact hn (ofVal _ _ hm (by rw [tU_val, hh, transvection_eq]))
  let φ : Fin n → k := fun l => b.val a l
  have hrow : φ ᵥ* (b⁻¹).val = Pi.single a 1 := by
    have e : φ = Pi.single a 1 ᵥ* b.val := by
      ext l
      simp [φ, vecMul, single_dotProduct]
    rw [e, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
  have H3 : ∀ w (hw : φ ⬝ᵥ w = 0), tU w φ hw ∈ H := fun w hw =>
    h3 _ a (b.val *ᵥ w) ha hw (by rw [conj_val, hrow]; rfl)
  let S := Finset.univ.filter (fun l : Fin n => φ l ≠ 0)
  have hcS : c ∈ S := by simp [S, φ, hne]
  set j := S.min' ⟨c, hcS⟩ with hjdef
  have hjc : j ≤ c := Finset.min'_le S c hcS
  have hφj : φ j ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem S ⟨c, hcS⟩)).2
  have hlow : ∀ l, l < j → φ l = 0 := fun l hl => by
    by_contra h'
    exact absurd (Finset.min'_le S l (by simp [S, h'])) (not_le.mpr hl)
  obtain ⟨t, ht⟩ := hk.mul_inv_cancel hφj
  have hjr : j.val < r := lt_of_le_of_lt (show j.val ≤ c.val from hjc) hc
  let ψ : Fin n → k := fun l => if j < l then φ l * t else 0
  have hψ : ψ ⬝ᵥ Pi.single j 1 = 0 := by simp [ψ, dotProduct_single]
  have hu : tU (Pi.single j 1) ψ hψ ∈ unip k n := tU_mem_unip _ _ _ (fun i l hli => by
    simp only [Pi.single_apply, ψ]
    split_ifs with h1 h2 <;> first | (simp; done) | (have := Fin.lt_def.mp h2; rw [h1] at hli; omega))
  have hvec : φ ᵥ* ((tU (Pi.single j 1) ψ hψ)⁻¹).val = Pi.single j (φ j) := by
    rw [tU_inv_val, vecMul_sub, vecMul_one, vecMul_vmv, dotProduct_single, mul_one]
    ext l
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ψ, Pi.single_apply]
    rcases lt_trichotomy l j with hl | hl | hl
    · rw [if_neg (not_lt.mpr hl.le), if_neg hl.ne, hlow l hl]; ring
    · rw [hl]; simp
    · rw [if_pos hl, if_neg hl.ne']; linear_combination (-(φ l)) * ht
  have KEY : ∀ (v : Fin n → k) (hv : Pi.single j 1 ⬝ᵥ v = 0), tU v (Pi.single j 1) hv ∈ H := by
    intro v hv
    have hw : φ ⬝ᵥ (t • (((tU (Pi.single j 1) ψ hψ)⁻¹).val *ᵥ v)) = 0 := by
      rw [dotProduct_smul, dotProduct_mulVec, hvec, single_dotProduct]
      rw [single_dotProduct, one_mul] at hv
      rw [hv, mul_zero, smul_zero]
    refine ofVal _ _ (hU _ hu _ (H3 _ hw)) ?_
    rw [conj_val, hvec, mulVec_smul, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, tU_val]
    congr 1
    ext p q
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs
    · linear_combination (v p) * ht
    · simp
  rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
  · have hn3 : 3 ≤ n := by omega
    let m0 : Fin n := ⟨n - 1, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    have hm0j : j ≠ m0 := fun e => by
      have := congrArg Fin.val e
      simp [m0] at this
      omega
    have hi1j : j ≠ i1 := fun e => by
      have := congrArg Fin.val e
      simp [i1] at this
      omega
    have hm0i1 : i1 ≠ m0 := fun e => by
      have := congrArg Fin.val e
      simp [m0, i1] at this
      omega
    have hX := KEY (Pi.single m0 1) (sdot _ _ _ hm0j)
    have hu1 : tU (Pi.single j 1) (Pi.single i1 1) (sdot _ _ _ hi1j.symm) ∈ unip k n :=
      tU_mem_unip _ _ _ (fun p q hpq => by
        simp only [Pi.single_apply]
        split_ifs with h1 h2 <;> first | (simp; done) | (subst h1 h2; simp [i1] at hpq; omega))
    have hQ : tU (Pi.single m0 (-1)) (Pi.single i1 1) (sdot _ _ _ hm0i1) ∈ H := by
      have := H.mul_mem (H.inv_mem hX) (hU _ hu1 _ hX)
      exact (congrArg (· ∈ H) (comm_a (k := k) j i1 m0 hi1j hm0j hm0i1)).mp this
    refine H4 j i1 (by simp [i1, hj0]) (by simp [i1]; omega) (fun x => ⟨sdot _ _ _ hi1j.symm, ?_⟩)
    have hP : tU (Pi.single j (-x)) (Pi.single m0 1) (sdot _ _ _ hm0j.symm) ∈ unip k n :=
      tU_mem_unip _ _ _ (fun p q hpq => by
        simp only [Pi.single_apply]
        split_ifs with h1 h2 <;> first | (simp; done) | (subst h1 h2; simp [m0] at hpq; omega))
    have hZ := H.mul_mem (hU _ hP _ hQ) (H.inv_mem hQ)
    exact ofVal _ _ hZ ((congrArg Units.val (comm_b j i1 m0 hi1j hm0j hm0i1 (-x) (-1))).trans
      (by rw [tU_val, tU_val, neg_mul_neg, mul_one]))
  · let i : Fin n := ⟨j.val - 1, by omega⟩
    have hij : j ≠ i := fun e => by
      have := congrArg Fin.val e
      simp [i] at this
      omega
    exact H4 i j (by simp [i]; omega) hjr (fun x => ⟨sdot _ _ _ hij, KEY _ _⟩)

end GlobalTheory.PosAgree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedSubgroupColumnMatricesEntryZeroStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalised_subgroup_column_matrices_entry_zero : ∀ (k : Type) [CommRing k], IsField k → ∀ n r : ℕ, 2 ≤ r → r < n → ∀ (H : Subgroup (GL (Fin n) k)) (b : GL (Fin n) k), (∀ u ∈ unip k n, ∀ h ∈ H, u * h * u⁻¹ ∈ H) → (∀ (h : GL (Fin n) k) (m : Fin n) (v : Fin n → k), r ≤ (m : ℕ) → v m = 0 → h.val = colMat v m → h ∈ H) → (∀ (h : GL (Fin n) k) (m : Fin n) (v : Fin n → k), r ≤ (m : ℕ) → v m = 0 → (b * h * b⁻¹).val = colMat v m → h ∈ H) → (∀ i j : Fin n, (i : ℕ) + 1 = j → (j : ℕ) < r → ∃ (c : k) (h : GL (Fin n) k), h.val = Matrix.transvection i j c ∧ h ∉ H) → ∀ a c : Fin n, r ≤ (a : ℕ) → (c : ℕ) < r → b.val a c = 0 := by
  first | exact @GlobalTheory.PosAgree.entry_zero | exact GlobalTheory.PosAgree.entry_zero | (intros; apply GlobalTheory.PosAgree.entry_zero <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ParaForce

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

abbrev incl (s : ReciprocityTheory.Aut.SplitPlace L) : Os s →+* s.v.adicCompletion (maximalRealSubfield L) :=
  (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype

theorem isCompOf_iff (s : ReciprocityTheory.Aut.SplitPlace L) (κ : Formalism.AUTREP.GAf L n) (y : GL (Fin n) (Os s)) :
    IsCompOf s κ y ↔ s.loc n κ = Matrix.GeneralLinearGroup.map (incl s) y := by
  constructor
  · intro h
    ext a c
    rw [← h a c]
    rfl
  · intro h a c
    rw [h]
    rfl

theorem isCompOf_mul {s : ReciprocityTheory.Aut.SplitPlace L} {κ κ' : Formalism.AUTREP.GAf L n} {y y' : GL (Fin n) (Os s)}
    (h : IsCompOf s κ y) (h' : IsCompOf s κ' y') : IsCompOf s (κ * κ') (y * y') := by
  rw [isCompOf_iff] at *
  rw [map_mul, map_mul, h, h']

theorem isCompOf_inv {s : ReciprocityTheory.Aut.SplitPlace L} {κ : Formalism.AUTREP.GAf L n} {y : GL (Fin n) (Os s)}
    (h : IsCompOf s κ y) : IsCompOf s κ⁻¹ y⁻¹ := by
  rw [isCompOf_iff] at *
  rw [map_inv, map_inv, h]

theorem exists_lift (s : ReciprocityTheory.Aut.SplitPlace L) (y : GL (Fin n) (Os s)) :
    ∃ κ : Formalism.AUTREP.GAf L n, ReciprocityTheory.Aut.TrivOutside {s.v} κ ∧ IsCompOf s κ y := by
  obtain ⟨x, hx, e⟩ := GlobalTheory.SplitSec.exists_trivOutside_loc L n s (Matrix.GeneralLinearGroup.map (incl s) y)
  exact ⟨x, hx, (isCompOf_iff s x y).2 e⟩

theorem isUnit_of_not_lt (s : ReciprocityTheory.Aut.SplitPlace L) (x : Os s)
    (hx : ¬ Valued.v (x : s.v.adicCompletion (maximalRealSubfield L)) < 1) : IsUnit x := by
  have h1 : Valued.v (x : s.v.adicCompletion (maximalRealSubfield L)) ≤ 1 := x.2
  have heq : Valued.v (x : s.v.adicCompletion (maximalRealSubfield L)) = 1 := le_antisymm h1 (not_lt.1 hx)
  have hx0 : (x : s.v.adicCompletion (maximalRealSubfield L)) ≠ 0 := by
    intro h
    rw [h, map_zero] at heq
    exact zero_ne_one heq
  have hinv : (x : s.v.adicCompletion (maximalRealSubfield L))⁻¹ ∈ s.v.adicCompletionIntegers (maximalRealSubfield L) := by
    change Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L))⁻¹) ≤ 1
    rw [map_inv₀, heq, inv_one]
  refine ⟨⟨x, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩ <;> apply Subtype.ext <;> simp [hx0]

theorem exists_gl_lift (s : ReciprocityTheory.Aut.SplitPlace L) {k : Type} [CommRing k] (φ : Os s →+* k) (hk : IsField k)
    (hφ : IsResidue s φ) (h : GL (Fin n) k) :
    ∃ y : GL (Fin n) (Os s), Matrix.GeneralLinearGroup.map φ y = h := by
  haveI : Nontrivial k := ⟨hk.exists_pair_ne⟩
  choose g hg using hφ.surj
  let M : Matrix (Fin n) (Fin n) (Os s) := fun a c => g (h.val a c)
  have hM : M.map φ = h.val := by
    ext a c
    exact hg _
  have hdet : IsUnit M.det := by
    apply isUnit_of_not_lt
    intro hlt
    have h0 : φ M.det = 0 := (hφ.ker _).2 hlt
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM] at h0
    exact (Matrix.isUnits_det_units h).ne_zero h0
  refine ⟨Matrix.nonsingInvUnit M hdet, ?_⟩
  ext a c
  simp [Matrix.GeneralLinearGroup.map, ← hM]
  rfl

end GlobalTheory.ParaForce

namespace GlobalTheory.ParaForce

theorem det_one_add_vecMulVec_single {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] (w : ι → R) (m : ι)
    (hw : w m = 0) : (1 + Matrix.vecMulVec w (Pi.single m 1)).det = 1 := by
  rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [hw]

theorem det_upperUnitri {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (hlow : ∀ a c : Fin n, c < a → M a c = 0) (hdiag : ∀ a, M a a = 1) : M.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun a c h => hlow a c h)]
  simp [hdiag]

section
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem map_incl_apply (s : ReciprocityTheory.Aut.SplitPlace L) (y : GL (Fin n) (Os s)) (a c : Fin n) :
    (Matrix.GeneralLinearGroup.map (incl s) y).val a c = ((y.val a c : Os s) : s.v.adicCompletion (maximalRealSubfield L)) := rfl

theorem uniRT_of (s : ReciprocityTheory.Aut.SplitPlace L) (r : ℕ) (y : GL (Fin n) (Os s))
    (hlow : ∀ a c : Fin n, (c : ℕ) < r → (c : ℕ) < a → y.val a c = 0) (hdiag : ∀ a : Fin n, (a : ℕ) < r → y.val a a = 1) :
    NG.UniRT s r (Matrix.GeneralLinearGroup.map (incl s) y) := by
  refine ⟨⟨⟨y, rfl⟩, fun a c ha hc => ?_⟩, fun a c ha hc => ⟨fun hca => ?_, fun hac => ?_⟩⟩
  · rw [map_incl_apply, hlow a c hc (by omega)]
    simp
  · rw [map_incl_apply, hlow a c hc hca]
    simp
  · subst hac
    rw [map_incl_apply, hdiag a ha]
    simp

theorem detDD_map (s : ReciprocityTheory.Aut.SplitPlace L) (r : ℕ) (y : GL (Fin n) (Os s)) :
    NG.detDD s r (Matrix.GeneralLinearGroup.map (incl s) y) =
      incl s (Matrix.of fun a b : {x : Fin n // r ≤ x.val} => y.val a.1 b.1).det := by
  rw [RingHom.map_det]
  rfl

end
end GlobalTheory.ParaForce

namespace GlobalTheory.ParaForce

theorem transvection_apply' {R : Type} [CommRing R] {n : ℕ} (i j a c : Fin n) (x : R) :
    Matrix.transvection i j x a c = (1 : Matrix (Fin n) (Fin n) R) a c + if a = i ∧ c = j then x else 0 := by
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
  by_cases h1 : a = i <;> by_cases h2 : c = j
  · subst h1 h2; simp
  · subst h1; simp [h2, Ne.symm h2]
  · subst h2; simp [h1, Ne.symm h1]
  · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem map_transvection_entry {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {n : ℕ} (i j a c : Fin n) (x : R) :
    φ ((1 : Matrix (Fin n) (Fin n) R) a c + if a = i ∧ c = j then x else 0) = Matrix.transvection i j (φ x) a c := by
  rw [transvection_apply', map_add (f := _)]
  by_cases h1 : a = c
  · subst h1; simp [Matrix.one_apply, apply_ite φ]
  · simp [h1, Matrix.one_apply, apply_ite φ]

end GlobalTheory.ParaForce

namespace GlobalTheory.ParaForce

theorem para_of_colMat_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n r : ℕ) (s : ReciprocityTheory.Aut.SplitPlace L) (k : Type) [CommRing k] (φ : Os s →+* k), IsField k → IsResidue s φ → 2 ≤ r → r < n → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : Formalism.AUTREP.GAf L n → W), f ≠ 0 → ∀ (J : Subgroup (Formalism.AUTREP.GAf L n)) (χ : J →* ℂˣ) (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield L)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ → NG.LevelUni J χ s r ψ₀ ξ → (∀ (κ : J) (x : Formalism.AUTREP.GAf L n), f (x * κ) = ((χ κ : ℂˣ) : ℂ) • f x) → ∀ b : GL (Fin n) k, (∀ (κ : Formalism.AUTREP.GAf L n) (y : GL (Fin n) (Os s)), ReciprocityTheory.Aut.TrivOutside {s.v} κ → IsCompOf s κ y → ∀ (m : Fin n) (v : Fin n → k), r ≤ (m : ℕ) → v m = 0 → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val = colMat v m → ∀ x, f (x * κ) = f x) → ∀ a c : Fin n, r ≤ (a : ℕ) → (c : ℕ) < r → b.val a c = 0 := by
  intro L _ _ _ n r s k _ φ hk hφ hr hrn W _ _ f hf J χ ψ₀ ξ hψ hJ hfJ b hb
  haveI : Nontrivial k := ⟨hk.exists_pair_ne⟩
  have hker : ∀ (κ : Formalism.AUTREP.GAf L n) (y : GL (Fin n) (Os s)), ReciprocityTheory.Aut.TrivOutside {s.v} κ → IsCompOf s κ y →
      Matrix.GeneralLinearGroup.map φ y = 1 → ∀ x, f (x * κ) = f x := by
    intro κ y hκ hy h1 x
    refine hb κ y hκ hy ⟨n - 1, by omega⟩ 0 (by simp only; omega) rfl ?_ x
    rw [h1, mul_one, mul_inv_cancel]
    ext a c
    simp [colMat]
  have htr : ∀ (κ : Formalism.AUTREP.GAf L n) (y : GL (Fin n) (Os s)) (κ' : Formalism.AUTREP.GAf L n) (y' : GL (Fin n) (Os s)),
      ReciprocityTheory.Aut.TrivOutside {s.v} κ → IsCompOf s κ y → ReciprocityTheory.Aut.TrivOutside {s.v} κ' → IsCompOf s κ' y' →
      Matrix.GeneralLinearGroup.map φ y = Matrix.GeneralLinearGroup.map φ y' → (∀ x, f (x * κ) = f x) →
      ∀ x, f (x * κ') = f x := by
    intro κ y κ' y' hκ hy hκ' hy' e hfix x
    have hd := hker (κ⁻¹ * κ') (y⁻¹ * y') (GlobalTheory.HeckeStdFacts.triv_mul (GlobalTheory.HeckeStdFacts.triv_inv hκ) hκ')
      (isCompOf_mul (isCompOf_inv hy) hy') (by rw [map_mul, map_inv, e, inv_mul_cancel])
    calc f (x * κ') = f ((x * κ) * (κ⁻¹ * κ')) := by rw [mul_assoc, mul_inv_cancel_left]
      _ = f (x * κ) := hd _
      _ = f x := hfix x
  have lift : ∀ h : GL (Fin n) k, ∃ κ : Formalism.AUTREP.GAf L n, ∃ y : GL (Fin n) (Os s),
      ReciprocityTheory.Aut.TrivOutside {s.v} κ ∧ IsCompOf s κ y ∧ Matrix.GeneralLinearGroup.map φ y = h := by
    intro h
    obtain ⟨y, hy⟩ := exists_gl_lift s φ hk hφ h
    obtain ⟨κ, hκ, hc⟩ := exists_lift s y
    exact ⟨κ, y, hκ, hc, hy⟩
  let H : Subgroup (GL (Fin n) k) :=
    { carrier := {h | ∀ (κ : Formalism.AUTREP.GAf L n) (y : GL (Fin n) (Os s)), ReciprocityTheory.Aut.TrivOutside {s.v} κ →
          IsCompOf s κ y → Matrix.GeneralLinearGroup.map φ y = h → ∀ x, f (x * κ) = f x}
      mul_mem' := by
        intro h1 h2 H1 H2 κ y hκ hy e
        obtain ⟨κ1, y1, hκ1, hy1, e1⟩ := lift h1
        obtain ⟨κ2, y2, hκ2, hy2, e2⟩ := lift h2
        refine htr (κ1 * κ2) (y1 * y2) κ y (GlobalTheory.HeckeStdFacts.triv_mul hκ1 hκ2) (isCompOf_mul hy1 hy2) hκ hy
          (by rw [map_mul, e1, e2, e]) ?_
        intro x
        rw [← mul_assoc, H2 κ2 y2 hκ2 hy2 e2, H1 κ1 y1 hκ1 hy1 e1]
      one_mem' := fun κ y hκ hy e => hker κ y hκ hy e
      inv_mem' := by
        intro h H1 κ y hκ hy e
        obtain ⟨κ1, y1, hκ1, hy1, e1⟩ := lift h
        refine htr κ1⁻¹ y1⁻¹ κ y (GlobalTheory.HeckeStdFacts.triv_inv hκ1) (isCompOf_inv hy1) hκ hy
          (by rw [map_inv, e1, e]) ?_
        intro x
        have := H1 κ1 y1 hκ1 hy1 e1 (x * κ1⁻¹)
        rw [inv_mul_cancel_right] at this
        exact this.symm }
  have hmem : ∀ (κ : Formalism.AUTREP.GAf L n) (y : GL (Fin n) (Os s)), ReciprocityTheory.Aut.TrivOutside {s.v} κ → IsCompOf s κ y →
      (∀ x, f (x * κ) = f x) → Matrix.GeneralLinearGroup.map φ y ∈ H :=
    fun κ y hκ hy hfix κ' y' hκ' hy' e => htr κ y κ' y' hκ hy hκ' hy' e.symm hfix
  have hJact : ∀ (κ : Formalism.AUTREP.GAf L n) (y : GL (Fin n) (Os s)), ReciprocityTheory.Aut.TrivOutside {s.v} κ → IsCompOf s κ y →
      NG.UniRT s r (Matrix.GeneralLinearGroup.map (incl s) y) → ∃ hJκ : κ ∈ J,
        ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ,
        (u : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r (Matrix.GeneralLinearGroup.map (incl s) y) →
        ((χ ⟨κ, hJκ⟩ : ℂˣ) : ℂ) = ψ₀ (NG.supDiag s r (Matrix.GeneralLinearGroup.map (incl s) y)) * ξ u := by
    intro κ y hκ hy hU
    rw [isCompOf_iff] at hy
    have hJκ : κ ∈ J := (hJ.mem κ hκ).2 (by rw [hy]; exact hU)
    refine ⟨hJκ, fun u hu => ?_⟩
    rw [← hy] at hu ⊢
    exact hJ.chr κ hJκ hκ u hu
  have hnorm : ∀ u ∈ unip k n, ∀ h ∈ H, u * h * u⁻¹ ∈ H := by
    intro u hu h hh
    have hu1 : u.val.BlockTriangular fun a => (a : ℕ) := hu.1
    have hu2 : ∀ a, u.val a a = 1 := hu.2
    choose g hg using hφ.surj
    let M : Matrix (Fin n) (Fin n) (Os s) := fun a c => if a < c then g (u.val a c) else if a = c then 1 else 0
    have hlow : ∀ a c : Fin n, c < a → M a c = 0 := by
      intro a c hca
      simp [M, not_lt.2 hca.le, hca.ne']
    have hdiag : ∀ a, M a a = 1 := by
      intro a
      simp [M]
    have hdet : M.det = 1 := det_upperUnitri M hlow hdiag
    let yu : GL (Fin n) (Os s) := Matrix.nonsingInvUnit M (by rw [hdet]; exact isUnit_one)
    have hyu : Matrix.GeneralLinearGroup.map φ yu = u := by
      ext a c
      show φ (M a c) = u.val a c
      rcases lt_trichotomy a c with hac | hac | hac
      · simp [M, hac, hg]
      · subst hac
        simp [M, hu2 a]
      · rw [hlow a c hac, map_zero, hu1 (show (c : ℕ) < a from hac)]
    obtain ⟨κu, hκu, hcu⟩ := exists_lift s yu
    have hUu : NG.UniRT s r (Matrix.GeneralLinearGroup.map (incl s) yu) :=
      uniRT_of s r yu (fun a c _ hca => hlow a c hca) (fun a _ => hdiag a)
    obtain ⟨hJu, -⟩ := hJact κu yu hκu hcu hUu
    obtain ⟨κh, yh, hκh, hch, eh⟩ := lift h
    rw [← hyu, ← eh, ← map_inv, ← map_mul, ← map_mul]
    refine hmem (κu * κh * κu⁻¹) (yu * yh * yu⁻¹)
      (GlobalTheory.HeckeStdFacts.triv_mul (GlobalTheory.HeckeStdFacts.triv_mul hκu hκh) (GlobalTheory.HeckeStdFacts.triv_inv hκu))
      (isCompOf_mul (isCompOf_mul hcu hch) (isCompOf_inv hcu)) ?_
    intro x
    have h1 : f (x * κu * κh * κu⁻¹) = (((χ ⟨κu, hJu⟩)⁻¹ : ℂˣ) : ℂ) • f (x * κu * κh) := by
      rw [← map_inv]
      exact hfJ ⟨κu, hJu⟩⁻¹ (x * κu * κh)
    have h2 : f (x * κu) = ((χ ⟨κu, hJu⟩ : ℂˣ) : ℂ) • f x := hfJ ⟨κu, hJu⟩ x
    have h3 : f (x * κu * κh) = f (x * κu) := hh κh yh hκh hch eh (x * κu)
    rw [show x * (κu * κh * κu⁻¹) = x * κu * κh * κu⁻¹ by simp only [mul_assoc], h1, h3, h2, smul_smul,
      Units.inv_mul, one_smul]
  have hcol : ∀ (h : GL (Fin n) k) (m : Fin n) (v : Fin n → k), r ≤ (m : ℕ) → v m = 0 → h.val = colMat v m → h ∈ H := by
    intro h m v hm hv e
    choose g hg using hφ.surj
    let w : Fin n → Os s := fun a => if a = m then 0 else g (v a)
    have hwm : w m = 0 := by simp [w]
    let M : Matrix (Fin n) (Fin n) (Os s) := 1 + Matrix.vecMulVec w (Pi.single m 1)
    have hMe : ∀ a c, M a c = (1 : Matrix (Fin n) (Fin n) (Os s)) a c + if c = m then w a else 0 := by
      intro a c
      simp [M, Matrix.vecMulVec_apply, Pi.single_apply]
    let y : GL (Fin n) (Os s) := Matrix.nonsingInvUnit M (by rw [det_one_add_vecMulVec_single w m hwm]; exact isUnit_one)
    have hy : Matrix.GeneralLinearGroup.map φ y = h := by
      ext a c
      show φ (M a c) = h.val a c
      rw [hMe, e]
      simp only [colMat, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_apply]
      by_cases hc : c = m <;> by_cases ha : a = m <;> simp [hc, ha, w, hg, hv, Matrix.one_apply]
    obtain ⟨κ, hκ, hcκ⟩ := exists_lift s y
    have hU : NG.UniRT s r (Matrix.GeneralLinearGroup.map (incl s) y) := by
      refine uniRT_of s r y (fun a c hc hca => ?_) (fun a ha => ?_)
      · have h1 : c ≠ m := fun h => by subst h; omega
        have h2 : a ≠ c := fun h => by subst h; omega
        show M a c = 0
        rw [hMe]
        simp [Matrix.one_apply, h1, h2]
      · have h1 : a ≠ m := fun h => by subst h; omega
        show M a a = 1
        rw [hMe]
        simp [h1]
    obtain ⟨hJκ, hχ⟩ := hJact κ y hκ hcκ hU
    have hsup : NG.supDiag s r (Matrix.GeneralLinearGroup.map (incl s) y) = 0 := by
      unfold NG.supDiag
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
      split_ifs with hac
      · have h1 : c ≠ m := fun h => by subst h; omega
        have h2 : a ≠ c := fun h => by subst h; omega
        rw [map_incl_apply]
        show ((M a c : Os s) : s.v.adicCompletion (maximalRealSubfield L)) = 0
        rw [hMe]
        simp [Matrix.one_apply, h1, h2]
      · rfl
    have hdd : NG.detDD s r (Matrix.GeneralLinearGroup.map (incl s) y) = 1 := by
      rw [detDD_map]
      have hb' : (Matrix.of fun a b : {x : Fin n // r ≤ x.val} => y.val a.1 b.1) =
          1 + Matrix.vecMulVec (fun a : {x : Fin n // r ≤ x.val} => w a.1) (Pi.single ⟨m, hm⟩ 1) := by
        refine Matrix.ext fun a c => ?_
        show M a.1 c.1 = _
        rw [hMe]
        simp [Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_apply, Subtype.ext_iff]
      rw [hb', det_one_add_vecMulVec_single (fun a : {x : Fin n // r ≤ x.val} => w a.1) ⟨m, hm⟩ hwm, map_one]
    rw [← hy]
    refine hmem κ y hκ hcκ fun x => ?_
    rw [hfJ ⟨κ, hJκ⟩ x, hχ 1 (by rw [hdd]; rfl), hsup, AddChar.map_zero_eq_one, map_one, Units.val_one, one_mul, one_smul]
  have hroot : ∀ i j : Fin n, (i : ℕ) + 1 = j → (j : ℕ) < r →
      ∃ (c : k) (h : GL (Fin n) k), h.val = Matrix.transvection i j c ∧ h ∉ H := by
    intro i j hij hjr
    obtain ⟨x0, hx0, hψx⟩ := hψ.2
    let x' : Os s := ⟨x0, hx0⟩
    have hne : i ≠ j := fun h => by subst h; omega
    let y : GL (Fin n) (Os s) :=
      Matrix.nonsingInvUnit (Matrix.transvection i j x') (by rw [Matrix.det_transvection_of_ne _ _ hne]; exact isUnit_one)
    have hent : ∀ a c, y.val a c = (1 : Matrix (Fin n) (Fin n) (Os s)) a c + if a = i ∧ c = j then x' else 0 := by
      intro a c
      exact transvection_apply' i j a c x'
    refine ⟨φ x', Matrix.GeneralLinearGroup.map φ y, ?_, ?_⟩
    · refine Matrix.ext fun a c => ?_
      show φ (y.val a c) = _
      rw [hent]
      exact map_transvection_entry φ i j a c x'
    · intro hmemH
      obtain ⟨κ, hκ, hcκ⟩ := exists_lift s y
      have hU : NG.UniRT s r (Matrix.GeneralLinearGroup.map (incl s) y) := by
        refine uniRT_of s r y (fun a c hc hca => ?_) (fun a ha => ?_)
        · have h2 : a ≠ c := fun h => by subst h; omega
          have h3 : ¬ (a = i ∧ c = j) := fun h => by obtain ⟨rfl, rfl⟩ := h; omega
          rw [hent]
          simp [Matrix.one_apply, h2, h3]
        · have h3 : ¬ (a = i ∧ a = j) := fun h => hne (h.1.symm.trans h.2)
          rw [hent]
          simp [h3]
      obtain ⟨hJκ, hχ⟩ := hJact κ y hκ hcκ hU
      have hterm : ∀ a c : Fin n, (if (a : ℕ) + 1 = c ∧ (c : ℕ) < r then
          (Matrix.GeneralLinearGroup.map (incl s) y).val a c else 0) = if a = i ∧ c = j then x0 else 0 := by
        intro a c
        rw [map_incl_apply, hent]
        by_cases h1 : a = i ∧ c = j
        · obtain ⟨rfl, rfl⟩ := h1
          simp [hij, hjr, Matrix.one_apply, hne, x']
        · rw [if_neg h1]
          split_ifs with h4
          · have h2 : a ≠ c := fun h => by subst h; omega
            simp [Matrix.one_apply, h2]
          · rfl
      have hsup : NG.supDiag s r (Matrix.GeneralLinearGroup.map (incl s) y) = x0 := by
        unfold NG.supDiag
        simp only [hterm]
        rw [Finset.sum_eq_single i (fun a _ ha => by simp [ha]) (by simp)]
        simp
      have hdd : NG.detDD s r (Matrix.GeneralLinearGroup.map (incl s) y) = 1 := by
        rw [detDD_map]
        have hb' : (Matrix.of fun a b : {x : Fin n // r ≤ x.val} => y.val a.1 b.1) = 1 := by
          refine Matrix.ext fun a c => ?_
          have h3 : ¬ (a.1 = i ∧ c.1 = j) := fun h => by have := a.2; rw [h.1] at this; omega
          show y.val a.1 c.1 = _
          rw [hent]
          simp [Matrix.one_apply, h3, Subtype.ext_iff]
        rw [hb', Matrix.det_one, map_one]
      have key : ∀ z, f z = ψ₀ x0 • f z := by
        intro z
        have h1 := hmemH κ y hκ hcκ rfl z
        have h2 := hfJ ⟨κ, hJκ⟩ z
        rw [hχ 1 (by rw [hdd]; rfl), hsup, map_one, Units.val_one, mul_one] at h2
        rw [← h2]
        exact h1.symm
      obtain ⟨z, hz⟩ : ∃ z, f z ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hf (funext hcon)
      have h0 : (ψ₀ x0 - 1) • f z = 0 := by rw [sub_smul, one_smul, ← key, sub_self]
      rcases smul_eq_zero.1 h0 with h | h
      · exact hψx (sub_eq_zero.1 h)
      · exact hz h
  exact GlobalTheory.T.normalised_subgroup_column_matrices_entry_zero k hk n r hr hrn H b hnorm hcol
    (fun h m v hm hv e κ y hκ hy ey x => hb κ y hκ hy m v hm hv (by rw [ey]; exact e) x) hroot

end GlobalTheory.ParaForce
