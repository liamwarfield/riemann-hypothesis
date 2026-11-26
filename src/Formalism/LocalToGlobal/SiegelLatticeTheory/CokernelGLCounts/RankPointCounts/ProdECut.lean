module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabMul
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.StabShape

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

section MulL

variable {E K : Type*} [Field E] [CommRing K] {r : ℕ}

theorem lL_eq (ι : E →+* K) (cj : K →+* K) (Dd : Fin (r + 1) → K) (a : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    lL ι cj Dd a = Matrix.diagonal (fun i => cj (Dd i)) * a.map ι *
      Matrix.diagonal (fun i => Ring.inverse (cj (Dd i))) := by
  ext i j
  simp [lL, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]

theorem lL_mul (ι : E →+* K) (cj : K →+* K) (Dd : Fin (r + 1) → K) (hD : ∀ i, IsUnit (Dd i))
    (a a' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : lL ι cj Dd (a * a') = lL ι cj Dd a * lL ι cj Dd a' := by
  have hinv : Matrix.diagonal (fun i => Ring.inverse (cj (Dd i))) * Matrix.diagonal (fun i => cj (Dd i)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact Ring.inverse_mul_cancel _ ((hD i).map cj)
  rw [lL_eq, lL_eq, lL_eq, Matrix.map_mul]
  set Dc := Matrix.diagonal (fun i => cj (Dd i))
  set Di := Matrix.diagonal (fun i => Ring.inverse (cj (Dd i)))
  rw [show Dc * a.map ι * Di * (Dc * a'.map ι * Di) = Dc * a.map ι * (Di * Dc) * a'.map ι * Di by
    simp only [Matrix.mul_assoc], hinv, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

def sgnE (K : Type*) [CommRing K] (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal fun i => (-1) ^ (r - i.val)

theorem sgnE_sq (K : Type*) [CommRing K] (r : ℕ) : sgnE K r * sgnE K r = 1 := by
  rw [sgnE, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem ρL_eq (ι : E →+* K) (Dd : Fin (r + 1) → K) (b : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    ρL ι Dd b = Matrix.diagonal (fun i => Ring.inverse (Dd i)) * (sgnE E r * b * sgnE E r).map ι *
      Matrix.diagonal Dd := by
  ext i j
  simp [ρL, sgnE, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc, mul_comm, mul_left_comm]

theorem ρL_mul (ι : E →+* K) (Dd : Fin (r + 1) → K) (hD : ∀ i, IsUnit (Dd i))
    (b b' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ρL ι Dd (b' * b) = ρL ι Dd b' * ρL ι Dd b := by
  have hinv : Matrix.diagonal Dd * Matrix.diagonal (fun i => Ring.inverse (Dd i)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact Ring.mul_inverse_cancel _ (hD i)
  have hS : sgnE E r * (b' * b) * sgnE E r = (sgnE E r * b' * sgnE E r) * (sgnE E r * b * sgnE E r) := by
    calc sgnE E r * (b' * b) * sgnE E r = sgnE E r * b' * (sgnE E r * sgnE E r) * b * sgnE E r := by
          rw [sgnE_sq]; simp [Matrix.mul_assoc]
      _ = _ := by simp [Matrix.mul_assoc]
  rw [ρL_eq, ρL_eq, ρL_eq, hS, Matrix.map_mul]
  set Dm := Matrix.diagonal Dd
  set Di := Matrix.diagonal (fun i => Ring.inverse (Dd i))
  set B1 := (sgnE E r * b' * sgnE E r).map ι
  set B2 := (sgnE E r * b * sgnE E r).map ι
  rw [show Di * B1 * Dm * (Di * B2 * Dm) = Di * B1 * (Dm * Di) * B2 * Dm by simp only [Matrix.mul_assoc], hinv,
    Matrix.mul_one]
  simp only [Matrix.mul_assoc]

end MulL

section MulG

open Matrix

variable {E F K : Type*} [Field E] [Field F] [CommRing K] [Algebra F K] {r : ℕ}

theorem cx_lG (e : K ≃ₐ[F] F × F) (ι : E →+* K) (Dd : Fin (r + 1) → K) (a b : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    cx e (lG e ι Dd a b) = Matrix.diagonal (fun i => (e (Dd i)).2) *
      a.map ((RingHom.fst F F).comp ((e : K →+* F × F).comp ι)) * Matrix.diagonal (fun i => ((e (Dd i)).2)⁻¹) := by
  ext i j
  simp only [cx, lG, Matrix.map_apply, Matrix.of_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_coe,
    AlgEquiv.apply_symm_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, div_eq_mul_inv]

theorem cy_lG (e : K ≃ₐ[F] F × F) (ι : E →+* K) (Dd : Fin (r + 1) → K) (a b : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    cy e (lG e ι Dd a b) = Matrix.diagonal (fun i => (e (Dd i)).2) *
      ((sgnE E r * b * sgnE E r).map ((RingHom.snd F F).comp ((e : K →+* F × F).comp ι)))ᵀ *
        Matrix.diagonal (fun i => ((e (Dd i)).2)⁻¹) := by
  ext i j
  simp only [cy, lG, sgnE, Matrix.map_apply, Matrix.of_apply, RingHom.comp_apply, RingHom.coe_snd, RingHom.coe_coe,
    AlgEquiv.apply_symm_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, div_eq_mul_inv, Matrix.transpose_apply, map_mul,
    Prod.snd_mul]
  ring

theorem cx_ρG (e : K ≃ₐ[F] F × F) (ι : E →+* K) (Dd : Fin (r + 1) → K) (a b : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    cx e (ρG e ι Dd a b) = Matrix.diagonal (fun i => ((e (Dd i)).1)⁻¹) *
      (sgnE E r * b * sgnE E r).map ((RingHom.fst F F).comp ((e : K →+* F × F).comp ι)) *
        Matrix.diagonal (fun i => (e (Dd i)).1) := by
  ext i j
  simp [cx, ρG, sgnE, Matrix.diagonal_mul, Matrix.mul_diagonal, div_eq_mul_inv]
  ring

theorem cy_ρG (e : K ≃ₐ[F] F × F) (ι : E →+* K) (Dd : Fin (r + 1) → K) (a b : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    cy e (ρG e ι Dd a b) = Matrix.diagonal (fun i => ((e (Dd i)).1)⁻¹) *
      (a.map ((RingHom.snd F F).comp ((e : K →+* F × F).comp ι)))ᵀ * Matrix.diagonal (fun i => (e (Dd i)).1) := by
  ext i j
  simp [cy, ρG, Matrix.diagonal_mul, Matrix.mul_diagonal, div_eq_mul_inv, Matrix.transpose_apply]
  ring

theorem diag_inv_mul {n : ℕ} (d : Fin n → F) (hd : ∀ i, d i ≠ 0) :
    Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hd i)

theorem diag_mul_inv {n : ℕ} (d : Fin n → F) (hd : ∀ i, d i ≠ 0) :
    Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hd i)

theorem sandwich {n : ℕ} (P Pi X Y : Matrix (Fin n) (Fin n) F) (h : Pi * P = 1) :
    P * X * Pi * (P * Y * Pi) = P * (X * Y) * Pi := by
  rw [show P * X * Pi * (P * Y * Pi) = P * X * (Pi * P) * Y * Pi by simp only [Matrix.mul_assoc], h, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem sgn_mul (b' b : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    sgnE E r * (b' * b) * sgnE E r = (sgnE E r * b' * sgnE E r) * (sgnE E r * b * sgnE E r) := by
  rw [show (sgnE E r * b' * sgnE E r) * (sgnE E r * b * sgnE E r) = sgnE E r * b' * (sgnE E r * sgnE E r) * b * sgnE E r by
    simp only [Matrix.mul_assoc], sgnE_sq, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem lG_mul (e : K ≃ₐ[F] F × F) (ι : E →+* K) (Dd : Fin (r + 1) → K) (hx : ∀ i, (e (Dd i)).1 ≠ 0)
    (hy : ∀ i, (e (Dd i)).2 ≠ 0) (a b a' b' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    lG e ι Dd (a * a') (b' * b) = lG e ι Dd a b * lG e ι Dd a' b' := by
  apply eq_of_cxy e
  · rw [cx_mul, cx_lG, cx_lG, cx_lG, Matrix.map_mul, sandwich _ _ _ _ (diag_inv_mul _ hy)]
  · rw [cy_mul, cy_lG, cy_lG, cy_lG, sgn_mul, Matrix.map_mul, Matrix.transpose_mul,
      sandwich _ _ _ _ (diag_inv_mul _ hy)]

theorem ρG_mul (e : K ≃ₐ[F] F × F) (ι : E →+* K) (Dd : Fin (r + 1) → K) (hx : ∀ i, (e (Dd i)).1 ≠ 0)
    (hy : ∀ i, (e (Dd i)).2 ≠ 0) (a b a' b' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    ρG e ι Dd (a * a') (b' * b) = ρG e ι Dd a' b' * ρG e ι Dd a b := by
  apply eq_of_cxy e
  · rw [cx_mul, cx_ρG, cx_ρG, cx_ρG, sgn_mul, Matrix.map_mul, sandwich _ _ _ _ (diag_mul_inv _ hx)]
  · rw [cy_mul, cy_ρG, cy_ρG, cy_ρG, Matrix.map_mul, Matrix.transpose_mul,
      sandwich _ _ _ _ (diag_mul_inv _ hx)]

end MulG

section RecMul

open Formalism.L2.SG.PairVal Formalism.L2.SG.CntLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

theorem lOf_mul {p : PlF D} (hA : Agree δ M p) (a b a' b' : MatR D) :
    lOf δ M p (a * a') (b' * b) = lOf δ M p a b * lOf δ M p a' b' := by
  cases h : (M p).split with
  | none => simp only [lOf, h]; exact lL_mul _ _ _ (frFac_unit δ M hA) a a'
  | some g =>
    simp only [lOf, h]
    exact lG_mul g.e _ _ (fun i => (split_units δ M hA g i).1) (fun i => (split_units δ M hA g i).2) a b a' b'

theorem ρOf_mul {p : PlF D} (hA : Agree δ M p) (a b a' b' : MatR D) :
    ρOf δ M p (a * a') (b' * b) = ρOf δ M p a' b' * ρOf δ M p a b := by
  cases h : (M p).split with
  | none => simp only [ρOf, h]; exact ρL_mul _ _ (frFac_unit δ M hA) b b'
  | some g =>
    simp only [ρOf, h]
    exact ρG_mul g.e _ _ (fun i => (split_units δ M hA g i).1) (fun i => (split_units δ M hA g i).2) a b a' b'

theorem cx_one {F K : Type*} [Field F] [CommRing K] [Algebra F K] {r : ℕ} (e : K ≃ₐ[F] F × F) :
    cx e (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) K) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem cy_one {F K : Type*} [Field F] [CommRing K] [Algebra F K] {r : ℕ} (e : K ≃ₐ[F] F × F) :
    cy e (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) K) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem lOf_one {p : PlF D} (hA : Agree δ M p) : lOf δ M p 1 1 = 1 := by
  cases h : (M p).split with
  | none =>
    simp only [lOf, h]
    rw [lL_eq, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1; funext i; exact Ring.mul_inverse_cancel _ ((frFac_unit δ M hA i).map _)
  | some g =>
    simp only [lOf, h]
    have hy := fun i => (split_units δ M hA g i).2
    apply eq_of_cxy g.e
    · rw [cx_lG, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, diag_mul_inv _ hy, cx_one]
    · rw [cy_lG, Matrix.mul_one, sgnE_sq, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one,
        Matrix.mul_one, diag_mul_inv _ hy, cy_one]

theorem ρOf_one {p : PlF D} (hA : Agree δ M p) : ρOf δ M p 1 1 = 1 := by
  cases h : (M p).split with
  | none =>
    simp only [ρOf, h]
    rw [ρL_eq, Matrix.mul_one, sgnE_sq, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact Ring.inverse_mul_cancel _ (frFac_unit δ M hA i)
  | some g =>
    simp only [ρOf, h]
    have hx := fun i => (split_units δ M hA g i).1
    apply eq_of_cxy g.e
    · rw [cx_ρG, Matrix.mul_one, sgnE_sq, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
        diag_inv_mul _ hx, cx_one]
    · rw [cy_ρG, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one,
        diag_inv_mul _ hx, cy_one]

end RecMul

end Formalism.L2.SG.Pf.StabShape
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEGen
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdE

section Gen

variable {G : Type} [Group G] {ι : Type} {H : ι → Type} [∀ i, Group (H i)] (π : ∀ i, G →* H i)

def glob (A : ∀ i, Subgroup (H i)) : Subgroup G := ⨅ i, (A i).comap (π i)

theorem mem_glob {A : ∀ i, Subgroup (H i)} {g : G} : g ∈ glob π A ↔ ∀ i, π i g ∈ A i := by
  simp [glob, Subgroup.mem_iInf]

theorem relIndex_glob (A C : ∀ i, Subgroup (H i)) (S : Finset ι) (hS : ∀ i ∉ S, A i = C i)
    (hfin : ∀ i, (C i).relIndex (A i) ≠ 0)
    (happrox : ∀ h : ∀ i, H i, ∃ g : G, (∀ i ∈ S, (h i)⁻¹ * π i g ∈ A i ⊓ C i) ∧ ∀ i ∉ S, π i g ∈ A i) :
    (glob π C).relIndex (glob π A) = ∏ i ∈ S, (C i).relIndex (A i) := by
  classical
  set K := (glob π C).subgroupOf (glob π A) with hK
  let Φ : ↥(glob π A) → ∀ i : S, ↥(A (i : ι)) ⧸ (C (i : ι)).subgroupOf (A (i : ι)) := fun g i =>
    QuotientGroup.mk ⟨π i g, (mem_glob π).1 g.2 i⟩
  have hrel : ∀ a b : ↥(glob π A), Φ a = Φ b ↔ a⁻¹ * b ∈ K := by
    intro a b
    rw [hK, Subgroup.mem_subgroupOf, mem_glob]
    simp only [Φ, funext_iff]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · have h1 := h ⟨i, hi⟩
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
        simpa using h1
      · rw [← hS i hi]
        simpa using (A i).mul_mem ((A i).inv_mem ((mem_glob π).1 a.2 i)) ((mem_glob π).1 b.2 i)
    · intro h i
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using h i
  have hsurj : Function.Surjective Φ := by
    intro q
    choose r hr using fun i : S => QuotientGroup.mk_surjective (q i)
    obtain ⟨g, hg1, hg2⟩ := happrox (fun i => if hi : i ∈ S then ((r ⟨i, hi⟩ : A i) : H i) else 1)
    have hgA : g ∈ glob π A := by
      rw [mem_glob]
      intro i
      by_cases hi : i ∈ S
      · have h1 := hg1 i hi
        simp only [dif_pos hi] at h1
        have h2 := (A i).mul_mem (r ⟨i, hi⟩).2 (Subgroup.mem_inf.1 h1).1
        simpa using h2
      · exact hg2 i hi
    refine ⟨⟨g, hgA⟩, ?_⟩
    funext i
    rw [← hr i]
    simp only [Φ]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 := hg1 i.1 i.2
    simp only [dif_pos i.2] at h1
    simpa using (C i).inv_mem (Subgroup.mem_inf.1 h1).2
  let Ψ : ↥(glob π A) ⧸ K → ∀ i : S, ↥(A (i : ι)) ⧸ (C (i : ι)).subgroupOf (A (i : ι)) :=
    Quotient.lift Φ (fun a b hab => (hrel a b).2 (QuotientGroup.leftRel_apply.1 hab))
  have hbij : Function.Bijective Ψ := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      exact QuotientGroup.eq.2 ((hrel a b).1 hxy)
    · intro q
      obtain ⟨a, ha⟩ := hsurj q
      exact ⟨QuotientGroup.mk a, ha⟩
  have hcard := Nat.card_congr (Equiv.ofBijective Ψ hbij)
  rw [Nat.card_pi] at hcard
  rw [← Finset.prod_coe_sort S]
  exact hcard

theorem idxRatio_glob (A C : ∀ i, Subgroup (H i)) (S : Finset ι) (hS : ∀ i ∉ S, A i = C i)
    (hfinA : ∀ i, (C i).relIndex (A i) ≠ 0) (hfinC : ∀ i, (A i).relIndex (C i) ≠ 0)
    (happrox : ∀ h : ∀ i, H i, ∃ g : G, (∀ i ∈ S, (h i)⁻¹ * π i g ∈ A i ⊓ C i) ∧ ∀ i ∉ S, π i g ∈ A i) :
    Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (glob π A) (glob π C) = ∏ i ∈ S, Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (A i) (C i) := by
  have happrox' : ∀ h : ∀ i, H i, ∃ g : G, (∀ i ∈ S, (h i)⁻¹ * π i g ∈ C i ⊓ A i) ∧ ∀ i ∉ S, π i g ∈ C i := by
    intro h
    obtain ⟨g, hg1, hg2⟩ := happrox h
    refine ⟨g, fun i hi => ?_, fun i hi => ?_⟩
    · rw [inf_comm]
      exact hg1 i hi
    · rw [← hS i hi]
      exact hg2 i hi
  unfold Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio
  rw [relIndex_glob π A C S hS hfinA happrox,
    relIndex_glob π C A S (fun i hi => (hS i hi).symm) hfinC happrox']
  push_cast
  rw [Finset.prod_div_distrib]

end Gen

end Formalism.L2.SG.Pf.ProdE
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdE

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

abbrev MP (p : PlF D) : Type := Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep

abbrev GLp (p : PlF D) : Type := Matrix.GeneralLinearGroup (Fin (D.R.rS + 1)) (D.s.atP p).Ep

def Y0 (p : PlF D) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatOM (ptMat w))

def StP (p : PlF D) : Subgroup (GLp p × (GLp p)ᵐᵒᵖ) where
  carrier := {x | IsLoUni (x.1 : MP p) ∧ IsUpUni ((x.2.unop : GLp p) : MP p) ∧
    (x.1 : MP p) * Y0 M δ u u' w p * ((x.2.unop : GLp p) : MP p) = Y0 M δ u u' w p}
  one_mem' := ⟨ZsVolGrp.isLoUni_one, ZsVolGrp.isUpUni_one, by simp⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    refine ⟨?_, ?_, ?_⟩
    · show IsLoUni ((x.1 * y.1 : GLp p) : MP p)
      rw [Units.val_mul]; exact ZsVolGrp.isLoUni_mul hx1 hy1
    · show IsUpUni (((x.2 * y.2).unop : GLp p) : MP p)
      rw [MulOpposite.unop_mul, Units.val_mul]; exact ZsVolGrp.isUpUni_mul hy2 hx2
    · show ((x.1 * y.1 : GLp p) : MP p) * _ * (((x.2 * y.2).unop : GLp p) : MP p) = _
      rw [MulOpposite.unop_mul, Units.val_mul, Units.val_mul]
      calc (x.1 : MP p) * (y.1 : MP p) * Y0 M δ u u' w p *
            (((y.2.unop : GLp p) : MP p) * ((x.2.unop : GLp p) : MP p))
          = (x.1 : MP p) * ((y.1 : MP p) * Y0 M δ u u' w p * ((y.2.unop : GLp p) : MP p)) *
              ((x.2.unop : GLp p) : MP p) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hy3, hx3]
  inv_mem' := by
    rintro x ⟨hx1, hx2, hx3⟩
    refine ⟨?_, ?_, ?_⟩
    · show IsLoUni ((x.1⁻¹ : GLp p) : MP p)
      rw [Matrix.coe_units_inv]; exact (ZsVolGrp.isLoUni_inv hx1).1
    · show IsUpUni (((x.2⁻¹).unop : GLp p) : MP p)
      rw [MulOpposite.unop_inv, Matrix.coe_units_inv]; exact (ZsVolGrp.isUpUni_inv hx2).1
    · show ((x.1⁻¹ : GLp p) : MP p) * _ * (((x.2⁻¹).unop : GLp p) : MP p) = _
      rw [MulOpposite.unop_inv]
      have h1 : ((x.1⁻¹ : GLp p) : MP p) * (x.1 : MP p) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have h2 : ((x.2.unop : GLp p) : MP p) * (((x.2.unop)⁻¹ : GLp p) : MP p) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      conv_lhs => rw [← hx3]
      calc ((x.1⁻¹ : GLp p) : MP p) * ((x.1 : MP p) * Y0 M δ u u' w p * ((x.2.unop : GLp p) : MP p)) *
            (((x.2.unop)⁻¹ : GLp p) : MP p)
          = (((x.1⁻¹ : GLp p) : MP p) * (x.1 : MP p)) * Y0 M δ u u' w p *
              (((x.2.unop : GLp p) : MP p) * (((x.2.unop)⁻¹ : GLp p) : MP p)) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

def AP (p : PlF D) : Subgroup (StP M δ u u' w p) where
  carrier := {x | Formalism.MainNotions.S.TieN.IntLow (M p) ((x.1.1 : GLp p) : MP p) ∧
    Formalism.MainNotions.S.TieN.IntUp (M p) ((x.1.2.unop : GLp p) : MP p)}
  one_mem' := ⟨ZsVolGrp.intLow_one _, ZsVolGrp.intUp_one _⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) (((x.1.1 * y.1.1 : GLp p)) : MP p)
      rw [Units.val_mul]; exact ZsVolGrp.intLow_mul _ hx1 hy1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) (((x.1.2 * y.1.2).unop : GLp p) : MP p)
      rw [MulOpposite.unop_mul, Units.val_mul]; exact ZsVolGrp.intUp_mul _ hy2 hx2
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) (((x.1.1)⁻¹ : GLp p) : MP p)
      rw [Matrix.coe_units_inv]; exact (ZsVolGrp.intLow_inv _ hx1).1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) ((((x.1.2)⁻¹).unop : GLp p) : MP p)
      rw [MulOpposite.unop_inv, Matrix.coe_units_inv]; exact (ZsVolGrp.intUp_inv _ hx2).1

def CP (p : PlF D) (Lp Lpi Up Upi : MP p) (hL : Lpi * Lp = 1) (hU : Up * Upi = 1) : Subgroup (StP M δ u u' w p) where
  carrier := {x | Formalism.MainNotions.S.TieN.IntLow (M p) (Lp * ((x.1.1 : GLp p) : MP p) * Lpi) ∧
    Formalism.MainNotions.S.TieN.IntUp (M p) (Upi * ((x.1.2.unop : GLp p) : MP p) * Up)}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) (Lp * ((1 : GLp p) : MP p) * Lpi)
      rw [Units.val_one, Matrix.mul_one, show Lp * Lpi = 1 from (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hL]
      exact ZsVolGrp.intLow_one _
    · show Formalism.MainNotions.S.TieN.IntUp (M p) (Upi * ((1 : GLp p) : MP p) * Up)
      rw [Units.val_one, Matrix.mul_one, show Upi * Up = 1 from (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hU]
      exact ZsVolGrp.intUp_one _
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) (Lp * ((x.1.1 * y.1.1 : GLp p) : MP p) * Lpi)
      rw [Units.val_mul]
      have e : Lp * ((x.1.1 : GLp p) * (y.1.1 : GLp p) : MP p) * Lpi =
          (Lp * ((x.1.1 : GLp p) : MP p) * Lpi) * (Lp * ((y.1.1 : GLp p) : MP p) * Lpi) := by
        rw [show (Lp * ((x.1.1 : GLp p) : MP p) * Lpi) * (Lp * ((y.1.1 : GLp p) : MP p) * Lpi) =
          Lp * ((x.1.1 : GLp p) : MP p) * (Lpi * Lp) * ((y.1.1 : GLp p) : MP p) * Lpi by simp only [Matrix.mul_assoc],
          hL, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      rw [e]; exact ZsVolGrp.intLow_mul _ hx1 hy1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) (Upi * (((x.1.2 * y.1.2).unop : GLp p) : MP p) * Up)
      rw [MulOpposite.unop_mul, Units.val_mul]
      have e : Upi * (((y.1.2.unop : GLp p) : MP p) * ((x.1.2.unop : GLp p) : MP p)) * Up =
          (Upi * ((y.1.2.unop : GLp p) : MP p) * Up) * (Upi * ((x.1.2.unop : GLp p) : MP p) * Up) := by
        rw [show (Upi * ((y.1.2.unop : GLp p) : MP p) * Up) * (Upi * ((x.1.2.unop : GLp p) : MP p) * Up) =
          Upi * ((y.1.2.unop : GLp p) : MP p) * (Up * Upi) * ((x.1.2.unop : GLp p) : MP p) * Up by
            simp only [Matrix.mul_assoc], hU, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      rw [e]; exact ZsVolGrp.intUp_mul _ hy2 hx2
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    have hLL : Lp * Lpi = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hL
    have hUU : Upi * Up = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hU
    refine ⟨?_, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) (Lp * (((x.1.1)⁻¹ : GLp p) : MP p) * Lpi)
      have hinv := ZsVolGrp.intLow_inv _ hx1
      have e : Lp * (((x.1.1)⁻¹ : GLp p) : MP p) * Lpi = (Lp * ((x.1.1 : GLp p) : MP p) * Lpi)⁻¹ := by
        symm
        apply Matrix.inv_eq_left_inv
        rw [show Lp * (((x.1.1)⁻¹ : GLp p) : MP p) * Lpi * (Lp * ((x.1.1 : GLp p) : MP p) * Lpi) =
          Lp * ((((x.1.1)⁻¹ : GLp p) : MP p) * (Lpi * Lp) * ((x.1.1 : GLp p) : MP p)) * Lpi by
            simp only [Matrix.mul_assoc], hL, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.mul_one, hLL]
      rw [e]; exact hinv.1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) (Upi * ((((x.1.2)⁻¹).unop : GLp p) : MP p) * Up)
      rw [MulOpposite.unop_inv]
      have hinv := ZsVolGrp.intUp_inv _ hx2
      have e : Upi * (((x.1.2.unop)⁻¹ : GLp p) : MP p) * Up = (Upi * ((x.1.2.unop : GLp p) : MP p) * Up)⁻¹ := by
        symm
        apply Matrix.inv_eq_left_inv
        rw [show Upi * (((x.1.2.unop)⁻¹ : GLp p) : MP p) * Up * (Upi * ((x.1.2.unop : GLp p) : MP p) * Up) =
          Upi * ((((x.1.2.unop)⁻¹ : GLp p) : MP p) * (Up * Upi) * ((x.1.2.unop : GLp p) : MP p)) * Up by
            simp only [Matrix.mul_assoc], hU, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.mul_one, hUU]
      rw [e]; exact hinv.1

section PiP

theorem lOf_low {p : PlF D} (a b : Formalism.L2.SG.PairVal.MatR D) (ha : IsLoUni a) (hb : IsUpUni b) (i j : Fin (D.R.rS + 1))
    (hij : i < j) : lOf δ M p a b i j = 0 := by
  cases h : (M p).split with
  | none => simp only [lOf, h, lL, Matrix.of_apply, (ha i j).1 hij, map_zero, mul_zero, zero_mul]
  | some g =>
    simp only [lOf, h, lG, Matrix.of_apply, (ha i j).1 hij, (hb j i).1 hij]
    simp

theorem ρOf_up {p : PlF D} (a b : Formalism.L2.SG.PairVal.MatR D) (ha : IsLoUni a) (hb : IsUpUni b) (i j : Fin (D.R.rS + 1))
    (hij : j < i) : ρOf δ M p a b i j = 0 := by
  cases h : (M p).split with
  | none => simp only [ρOf, h, ρL, Matrix.of_apply, (hb i j).1 hij]; simp
  | some g =>
    simp only [ρOf, h, ρG, Matrix.of_apply, (hb i j).1 hij, (ha j i).1 hij]
    simp

theorem lOf_loUni {p : PlF D} (hA : Agree δ M p) (a b : Formalism.L2.SG.PairVal.MatR D) (ha : IsLoUni a) (hb : IsUpUni b) :
    IsLoUni (lOf δ M p a b) := fun i j =>
  ⟨fun h => lOf_low M δ a b ha hb i j h, fun h => by subst h; exact lOf_diag δ M hA a b ha hb i⟩

theorem ρOf_upUni {p : PlF D} (hA : Agree δ M p) (a b : Formalism.L2.SG.PairVal.MatR D) (ha : IsLoUni a) (hb : IsUpUni b) :
    IsUpUni (ρOf δ M p a b) := fun i j =>
  ⟨fun h => ρOf_up M δ a b ha hb i j h, fun h => by subst h; exact ρOf_diag δ M hA a b ha hb i⟩

theorem bOf_spec (β : VolPinAsm.StG w) : IsLoUni ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) ∧
    IsUpUni (VolPinAsm.bOf w β) ∧
    ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ptMat w * VolPinAsm.bOf w β = ptMat w := by
  obtain ⟨ha, b, hb, hW⟩ := β.2
  have hWu := Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_isUnit (K := D.host.E) w
  have e : VolPinAsm.bOf w β = b := by
    unfold VolPinAsm.bOf
    have h1 : ((((β : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) *
        ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (ptMat w)⁻¹ * ((((β : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ptMat w
        = (ptMat w)⁻¹ * ((((β : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) *
            (((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ptMat w * b) := by rw [hW]
      _ = (ptMat w)⁻¹ * (((((β : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) *
            ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D)) * ptMat w * b := by simp only [Matrix.mul_assoc]
      _ = b := by rw [h1, Matrix.mul_one, Matrix.nonsing_inv_mul _ hWu, Matrix.one_mul]
  rw [e]
  exact ⟨ha, hb, hW⟩

theorem bOf_mul (β β' : Formalism.L2.SG.PairVal.GLR D) :
    VolPinAsm.bOf w (β * β') = VolPinAsm.bOf w β' * VolPinAsm.bOf w β := by
  have hWu := Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_isUnit (K := D.host.E) w
  unfold VolPinAsm.bOf
  rw [mul_inv_rev, Units.val_mul]
  calc (ptMat w)⁻¹ * (((β'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) *
        ((β⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D)) * ptMat w
      = (ptMat w)⁻¹ * ((β'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * (ptMat w * (ptMat w)⁻¹) *
          ((β⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ptMat w := by
        rw [Matrix.mul_nonsing_inv _ hWu, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem bOf_one : VolPinAsm.bOf w (1 : Formalism.L2.SG.PairVal.GLR D) = 1 := by
  have hWu := Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_isUnit (K := D.host.E) w
  unfold VolPinAsm.bOf
  rw [inv_one, Units.val_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hWu]

variable {p : PlF D} (hA : Agree δ M p)

def lU (β : Formalism.L2.SG.PairVal.GLR D) : GLp p :=
  ⟨lOf δ M p β (VolPinAsm.bOf w β), lOf δ M p (β⁻¹ : Formalism.L2.SG.PairVal.GLR D) (VolPinAsm.bOf w β⁻¹),
    by rw [← lOf_mul δ M hA, ← Units.val_mul, ← bOf_mul]
       simp only [mul_inv_cancel, inv_mul_cancel, Units.val_one, bOf_one]; exact lOf_one δ M hA,
    by rw [← lOf_mul δ M hA, ← Units.val_mul, ← bOf_mul]
       simp only [mul_inv_cancel, inv_mul_cancel, Units.val_one, bOf_one]; exact lOf_one δ M hA⟩

def ρU (β : Formalism.L2.SG.PairVal.GLR D) : GLp p :=
  ⟨ρOf δ M p β (VolPinAsm.bOf w β), ρOf δ M p (β⁻¹ : Formalism.L2.SG.PairVal.GLR D) (VolPinAsm.bOf w β⁻¹),
    by rw [← ρOf_mul δ M hA, ← Units.val_mul, ← bOf_mul]
       simp only [mul_inv_cancel, inv_mul_cancel, Units.val_one, bOf_one]; exact ρOf_one δ M hA,
    by rw [← ρOf_mul δ M hA, ← Units.val_mul, ← bOf_mul]
       simp only [mul_inv_cancel, inv_mul_cancel, Units.val_one, bOf_one]; exact ρOf_one δ M hA⟩

def πP : VolPinAsm.StG w →* StP M δ u u' w p where
  toFun β := ⟨(lU M δ w hA β, MulOpposite.op (ρU M δ w hA β)), by
    obtain ⟨ha, hb, hW⟩ := bOf_spec w β
    refine ⟨lOf_loUni M δ hA _ _ ha hb, ρOf_upUni M δ hA _ _ ha hb, ?_⟩
    show lOf δ M p ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) (VolPinAsm.bOf w β) * Y0 M δ u u' w p *
      ρOf δ M p ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) (VolPinAsm.bOf w β) = Y0 M δ u u' w p
    unfold Y0
    rw [← move δ M u u' hA _ _ ha hb, ZsVolGrp.zhatOM_zhatOM, hW]⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Units.ext
      show lOf δ M p ((1 : VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D) (VolPinAsm.bOf w ((1 : VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D)) = 1
      rw [OneMemClass.coe_one, bOf_one, Units.val_one, lOf_one δ M hA]
    · apply MulOpposite.unop_injective
      apply Units.ext
      show ρOf δ M p ((1 : VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D) (VolPinAsm.bOf w ((1 : VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D)) = 1
      rw [OneMemClass.coe_one, bOf_one, Units.val_one, ρOf_one δ M hA]
  map_mul' β β' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Units.ext
      show lOf δ M p ((β * β' : VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D) (VolPinAsm.bOf w ((β * β' : VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D)) =
        lOf δ M p ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) (VolPinAsm.bOf w β) *
          lOf δ M p ((β' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) (VolPinAsm.bOf w β')
      rw [Subgroup.coe_mul, bOf_mul, Units.val_mul, lOf_mul δ M hA]
    · apply MulOpposite.unop_injective
      apply Units.ext
      show ρOf δ M p ((β * β' : VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D) (VolPinAsm.bOf w ((β * β' : VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D)) =
        ρOf δ M p ((β' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) (VolPinAsm.bOf w β') *
          ρOf δ M p ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) (VolPinAsm.bOf w β)
      rw [Subgroup.coe_mul, bOf_mul, Units.val_mul, ρOf_mul δ M hA]

end PiP

section Props

open Formalism.L2.SG.Pf.ZsVolCut

variable {p : PlF D}

theorem lp_inv (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    lOf δ M p L⁻¹ U⁻¹ * lOf δ M p L U = 1 := by
  rw [← lOf_mul δ M hA, (ZsVolGrp.isLoUni_inv hL).2.1, (ZsVolGrp.isUpUni_inv hU).2.2, lOf_one δ M hA]

theorem up_inv (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    ρOf δ M p L U * ρOf δ M p L⁻¹ U⁻¹ = 1 := by
  rw [← ρOf_mul δ M hA, (ZsVolGrp.isLoUni_inv hL).2.1, (ZsVolGrp.isUpUni_inv hU).2.2, ρOf_one δ M hA]

def CPL (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) : Subgroup (StP M δ u u' w p) :=
  CP M δ u u' w p (lOf δ M p L U) (lOf δ M p L⁻¹ U⁻¹) (ρOf δ M p L U) (ρOf δ M p L⁻¹ U⁻¹)
    (lp_inv M δ hA L U hL hU) (up_inv M δ hA L U hL hU)

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def ApproxC : Prop :=
  ∀ (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : HypE M δ u u' F0 what₂ γ w F' L U),
    ∃ S : Finset (PlF D),
      (∀ p ∉ S, AP M δ u u' w p = CPL M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1) ∧
      (∀ p, (CPL M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1).relIndex (AP M δ u u' w p) ≠ 0 ∧
        (AP M δ u u' w p).relIndex (CPL M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1) ≠ 0) ∧
      ∀ h : ∀ p, StP M δ u u' w p, ∃ g : VolPinAsm.StG w,
        (∀ p ∈ S, (h p)⁻¹ * πP M δ u u' w (hE.1 p) g ∈
          AP M δ u u' w p ⊓ CPL M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1) ∧
        ∀ p ∉ S, πP M δ u u' w (hE.1 p) g ∈ AP M δ u u' w p

def LocIdxC : Prop :=
  ∀ (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D),
    Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (AP M δ u u' w p) (CPL M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1) =
      Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
        (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p)

end Props

end Formalism.L2.SG.Pf.ProdE
