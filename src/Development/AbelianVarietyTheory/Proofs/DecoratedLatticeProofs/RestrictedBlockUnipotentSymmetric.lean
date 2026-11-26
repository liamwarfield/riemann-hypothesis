module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeFrameLiftingSpanningVectorsMod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCongruenceIffFlagConditions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenusTypePlaceSetNotConjugatePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenusTypePlaceSetNotConjugatePlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeConjPg

theorem pg_places_not_isConjPl : ∀ {D : D7} (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → (∃ e, IsIdemSum e Pg) → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP' := by
  intro D Pg _ he PP hP PP' hP'
  obtain ⟨e, he⟩ := he
  exact GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he PP hP PP' hP'

end GlobalTheory.SeeConjPg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenusTypePlaceSetNotConjugatePlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genusTypePlaceSet_not_conjugatePlaces : ∀ {D : D7} (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → (∃ e, IsIdemSum e Pg) → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP' := by
  first | exact @GlobalTheory.SeeConjPg.pg_places_not_isConjPl | exact GlobalTheory.SeeConjPg.pg_places_not_isConjPl | (intros; apply GlobalTheory.SeeConjPg.pg_places_not_isConjPl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterArgumentCongrRootEntrySumMod
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterArgumentCongrRootEntrySumMod
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FlagChi

open Formalism.L2.SG.Pf.unitaryCongruence

theorem rootSum_eq {A : Type} [CommRing A] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (ε : A) (m : Matrix (Fin n) (Fin n) A) :
    rootSum ρ k ε m =
      (∑ a : Fin ρ, m ⟨a.1, by omega⟩ ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by split_ifs <;> omega⟩) +
      ∑ i : Fin k, if h : i.1 + 1 < k then ε * m ⟨ρ + i.1, by omega⟩ ⟨ρ + (i.1 + 1), by omega⟩ else 0 := by
  obtain rfl : n = ρ + (k + (ρ + 1)) := by omega
  unfold rootSum
  rw [Fin.sum_univ_add, Fin.sum_univ_add, ← add_assoc]
  have h3 : ∀ x y z : A, z = 0 → x = y → x + z = y := by
    intro x y z hz hx; rw [hz, hx, add_zero]
  refine h3 _ _ _ (Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun j _ => ?_) ?_
  · simp only [Fin.val_natAdd]
    rw [if_neg (by omega), if_neg (by omega)]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have ha := a.2
    rw [Finset.sum_eq_single (⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by split_ifs <;> omega⟩ : Fin (ρ + (k + (ρ + 1))))]
    · rw [if_pos]
      · rfl
      · simp only [Fin.val_castAdd]
        split_ifs <;> omega
    · intro j _ hj
      have hj' : j.1 ≠ if a.1 + 1 < ρ then a.1 + 1 else ρ + k := fun h => hj (Fin.ext h)
      simp only [Fin.val_castAdd]
      rw [if_neg (by split_ifs at hj' <;> omega), if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.2
    by_cases h : i.1 + 1 < k
    · rw [dite_eq_left h, Finset.sum_eq_single (⟨ρ + (i.1 + 1), by omega⟩ : Fin (ρ + (k + (ρ + 1))))]
      · rw [if_neg, if_pos]
        · rfl
        · simp only [Fin.val_natAdd, Fin.val_castAdd]
          omega
        · simp only [Fin.val_natAdd, Fin.val_castAdd]
          omega
      · intro j _ hj
        have hj' : j.1 ≠ ρ + (i.1 + 1) := fun h => hj (Fin.ext h)
        simp only [Fin.val_natAdd, Fin.val_castAdd]
        rw [if_neg (by omega), if_neg (by omega)]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dite_eq_right h]
      refine Finset.sum_eq_zero fun j _ => ?_
      simp only [Fin.val_natAdd, Fin.val_castAdd]
      rw [if_neg (by omega), if_neg (by omega)]

theorem hatL_eq_Lf (I : AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.1, z.2, rfl⟩

def colOf (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (j : Fin I.n) : VA I :=
  fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l j

theorem matIn_int (I : AutInst) {β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} {x : I.Gf}
    (hx : (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β) (i j : Fin I.n) :
    matIn I β x i j ∈ IntAf I.F I.E := by
  obtain ⟨y, hy⟩ := hx
  have hconj : β⁻¹ * frGL β y * β = intGL I.F I.E I.n y := by
    simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hy] at hconj
  unfold matIn
  rw [hconj]
  exact ((y : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) i j).2

theorem mul_matIn (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (x : I.Gf) :
    (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * matIn I β x =
      I.fmat x * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) := by
  unfold matIn
  rw [← Units.val_mul, ← Units.val_mul]
  congr 1
  group

theorem mulVec_mem_Lf (I : AutInst) {β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (hβ : IsFrame β I.L) {x : I.Gf}
    (hx : (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β) {v : VA I} (hv : v ∈ I.Lf) : I.fmat x *ᵥ v ∈ I.Lf := by
  rw [← hatL_eq_Lf] at hv ⊢
  refine (hβ _).2 fun i => ?_
  have h := (hβ v).1 hv
  have e : ((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *ᵥ
      (I.fmat x *ᵥ v) = matIn I β x *ᵥ
      (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *ᵥ v) := by
    unfold matIn
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  rw [e, Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (matIn_int I hx i l) (h l)

theorem col_mem_Lf (I : AutInst) {β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (hβ : IsFrame β I.L) (j : Fin I.n) :
    colOf I β j ∈ I.Lf := by
  rw [← hatL_eq_Lf]
  refine (hβ _).2 fun i => ?_
  show (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *
      (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))) i j ∈ _
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem mL_le_Lf (I : AutInst) (g : ℕ) : mL I g ≤ I.Lf :=
  Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact I.Lf.smul_mem (⟨(g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), natCast_mem _ g⟩ : IntAf I.F I.E) hy)

theorem mulVec_mem_mL (I : AutInst) (g : ℕ) {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)}
    (hM : ∀ y ∈ I.Lf, M *ᵥ y ∈ I.Lf) {v : VA I} (hv : v ∈ mL I g) : M *ᵥ v ∈ mL I g := by
  have : mL I g ≤ (mL I g).comap (mvO I M) := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact mL_mv I hM g le_rfl y hy)
  exact this hv

theorem hA_col (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (x : I.Gf) (p q : Fin I.n) :
    hA I (colOf I β p) (I.fmat x *ᵥ colOf I β q) = ∑ l, matIn I β x l q * gramIn I β p l := by
  have e : I.fmat x *ᵥ colOf I β q = ∑ l, matIn I β x l q • colOf I β l := by
    funext i
    have := congrFun (congrFun (mul_matIn I β x) i) q
    rw [Finset.sum_apply]
    refine Eq.trans this.symm ?_
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, ← hL_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hL_apply, hA_smul_right]
  rfl

theorem pair_zmod (I : AutInst) (g ρ k : ℕ) (b : ℕ → VA I) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))
    (hβ : IsLiftFrame I g b β)
    (hG : ∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) (x : I.Gf)
    (hx : (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β) (p q t : Fin I.n) (hp : p.1 ≠ ρ + k)
    (ht : t.1 = dualIdx ρ k p.1) : ZMod' I g (hA I (b p.1) (I.fmat x *ᵥ b q.1) - matIn I β x t q) := by
  have hM : ∀ y ∈ I.Lf, I.fmat x *ᵥ y ∈ I.Lf := fun y hy => mulVec_mem_Lf I hβ.1 hx hy
  have hp' : colOf I β p - b p.1 ∈ mL I g := hβ.2 p
  have hq' : colOf I β q - b q.1 ∈ mL I g := hβ.2 q
  have hbp : b p.1 ∈ I.Lf := by
    have := sub_mem (col_mem_Lf I hβ.1 p) (mL_le_Lf I g hp')
    rwa [sub_sub_cancel] at this
  have h1 : ZMod' I g (hA I (b p.1) (I.fmat x *ᵥ (colOf I β q - b q.1))) :=
    mL_Qs I g hbp (mulVec_mem_mL I g hM hq')
  have h2 : ZMod' I g (hA I (colOf I β p - b p.1) (I.fmat x *ᵥ colOf I β q)) := by
    rw [hA_symm]
    exact Z_sig I g (mL_Qs I g (hM _ (col_mem_Lf I hβ.1 q)) hp')
  have h3 : ZMod' I g (∑ l, matIn I β x l q * (gramIn I β p l - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k p l)) :=
    Z_sum I g _ _ fun l _ => Z_smul I g (matIn_int I hx l q) (hG p l)
  have e1 : ∑ l, matIn I β x l q * flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k p l = matIn I β x t q := by
    rw [Finset.sum_eq_single t]
    · unfold flagGram
      rw [if_pos ht, if_neg hp, mul_one]
    · intro l _ hl
      unfold flagGram
      rw [if_neg (fun h => hl (Fin.ext (h.trans ht.symm))), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [mul_sub] at h3
  rw [Finset.sum_sub_distrib, e1, ← hA_col] at h3
  have e2 : hA I (colOf I β p) (I.fmat x *ᵥ colOf I β q) =
      hA I (colOf I β p - b p.1) (I.fmat x *ᵥ colOf I β q) + hA I (b p.1) (I.fmat x *ᵥ colOf I β q) := by
    rw [← hA_add_left, sub_add_cancel]
  rw [Matrix.mulVec_sub, hA_sub_right] at h1
  rw [e2] at h3
  convert Z_sub I g (Z_sub I g h3 h2) h1 using 1
  ring

theorem chiArg_sub_rootSum : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β → (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) → ∀ x : I.Gf, (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β → ZMod' I g (chiArg I e0 f0 z0 bw bwd x - rootSum ρ k ew (matIn I β x)) := by
  intro I g ρ k e0 f0 z0 bw bwd ew hF hn β hβ hG x hx
  obtain ⟨-, -, -, -, ⟨hid, hor, hint, -⟩, ⟨hw, hwd⟩, -, -⟩ := hF
  rw [rootSum_eq hn]
  unfold chiArg
  rw [add_sub_add_comm, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Z_add I g (Z_sum I g _ _ fun a _ => ?_) (Z_sum I g _ _ fun i _ => ?_)
  · have ha := a.2
    have key := pair_zmod I g ρ k _ β hβ hG x hx ⟨2 * ρ + k - a.1, by omega⟩
      ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by split_ifs <;> omega⟩ ⟨a.1, by omega⟩ (by show 2 * ρ + k - a.1 ≠ _; omega)
      (by show a.1 = dualIdx ρ k (2 * ρ + k - a.1); unfold dualIdx; split_ifs <;> omega)
    have e1 : flagVec e0 f0 z0 bw bwd (2 * ρ + k - a.1) = f0 a := by
      unfold flagVec
      rw [dite_eq_right (by omega), dite_eq_right (by omega), if_neg (by omega), dite_eq_left (by omega)]
      congr 1
      apply Fin.ext
      show 2 * ρ + k - (2 * ρ + k - a.1) = a.1
      omega
    have e2 : flagVec e0 f0 z0 bw bwd (if a.1 + 1 < ρ then a.1 + 1 else ρ + k) = nxt e0 z0 a := by
      unfold nxt
      by_cases h : a.1 + 1 < ρ
      · rw [if_pos h, dite_eq_left h]
        unfold flagVec
        rw [dite_eq_left h]
      · rw [if_neg h, dite_eq_right h]
        unfold flagVec
        rw [dite_eq_right (by omega), dite_eq_right (by omega), if_pos rfl]
    rw [← e1, ← e2]
    exact key
  · have hi := i.2
    by_cases h : i.1 + 1 < k
    swap
    · rw [dite_eq_right h, dite_eq_right h, sub_zero]
      exact Z_zero I g
    rw [dite_eq_left h, dite_eq_left h]
    have key := pair_zmod I g ρ k _ β hβ hG x hx ⟨ρ + (k - (i.1 + 1)), by omega⟩
      ⟨ρ + (i.1 + 1), by omega⟩ ⟨ρ + i.1, by omega⟩ (by show ρ + (k - (i.1 + 1)) ≠ _; omega)
      (by show ρ + i.1 = dualIdx ρ k (ρ + (k - (i.1 + 1))); unfold dualIdx; split_ifs <;> omega)
    have c : ∀ l : Fin k, flagVec e0 f0 z0 bw bwd (ρ + l.1) = bw l + bwd (Fin.rev l) := by
      intro l
      have hl := l.2
      have : (⟨ρ + l.1 - ρ, by omega⟩ : Fin k) = l := Fin.ext (by show ρ + l.1 - ρ = l.1; omega)
      unfold flagVec
      rw [dite_eq_right (by omega), dite_eq_left (by omega), this]
    have e1 : bwd i = sigA I ew • flagVec e0 f0 z0 bw bwd (ρ + (k - (i.1 + 1))) := by
      have := c (Fin.rev i)
      rw [Fin.val_rev, Fin.rev_rev] at this
      rw [this, smul_add, hw, smul_smul, mul_comm, hor, zero_smul, zero_add]
      exact hwd i
    have e2 : bw ⟨i.1 + 1, h⟩ = ew • flagVec e0 f0 z0 bw bwd (ρ + (i.1 + 1)) := by
      rw [c ⟨i.1 + 1, h⟩, smul_add, hwd, smul_smul, hor, zero_smul, add_zero]
      exact hw _
    rw [e1, e2, Matrix.mulVec_smul, hA_smul_left, hA_smul_right, sigA_sigA, ← mul_assoc, hid, ← mul_sub]
    exact Z_smul I g hint key

end GlobalTheory.FlagChi

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterArgumentCongrRootEntrySumModStatement
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterArgument_congr_rootEntrySum_mod : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β → (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) → ∀ x : I.Gf, (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β → ZMod' I g (chiArg I e0 f0 z0 bw bwd x - rootSum ρ k ew (matIn I β x)) := by
  first | exact @GlobalTheory.FlagChi.chiArg_sub_rootSum | exact GlobalTheory.FlagChi.chiArg_sub_rootSum | (intros; apply GlobalTheory.FlagChi.chiArg_sub_rootSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricUnipotentMemOfFlagCongruenceDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricUnipotentMemOfFlagCongruenceDual
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.FlagCase

theorem dualIdx_lt' {ρ k a : ℕ} (h : a < 2 * ρ + k + 1) : dualIdx ρ k a < 2 * ρ + k + 1 := by
  unfold dualIdx; split_ifs <;> omega

theorem dualIdx_iff' {ρ k a b : ℕ} (ha : a < 2 * ρ + k + 1) (hb : b < 2 * ρ + k + 1) :
    a = dualIdx ρ k b ↔ b = dualIdx ρ k a := by
  unfold dualIdx; split_ifs <;> omega

theorem mul_flagGram_apply {K : Type} [CommRing K] {ρ k : ℕ}
    (A : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) (i j : Fin (2 * ρ + k + 1)) :
    (A * flagGram K (2 * ρ + k + 1) ρ k) i j =
      A i ⟨dualIdx ρ k j.val, dualIdx_lt' j.2⟩ * (if dualIdx ρ k j.val = ρ + k then -1 else 1) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨dualIdx ρ k j.val, dualIdx_lt' j.2⟩]
  · simp only [flagGram, Fin.val_mk]
    rw [if_pos ((dualIdx_iff' j.2 (dualIdx_lt' j.2)).mpr rfl)]
  · intro l _ hl
    simp only [flagGram]
    rw [if_neg, mul_zero]
    intro h
    exact hl (Fin.ext ((dualIdx_iff' j.2 l.2).mp h))
  · intro h; exact absurd (Finset.mem_univ _) h

theorem flagGram_mul_apply {K : Type} [CommRing K] {ρ k : ℕ}
    (A : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) (i j : Fin (2 * ρ + k + 1)) :
    (flagGram K (2 * ρ + k + 1) ρ k * A) i j =
      (if i.val = ρ + k then -1 else 1) * A ⟨dualIdx ρ k i.val, dualIdx_lt' i.2⟩ j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨dualIdx ρ k i.val, dualIdx_lt' i.2⟩]
  · simp only [flagGram, Fin.val_mk, if_true]
  · intro l _ hl
    simp only [flagGram]
    rw [if_neg, zero_mul]
    intro h
    exact hl (Fin.ext h)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem flagCond_dual_unipSym : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K,
    (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k →
    FlagCond (fun c : K => c = 0) ρ k 1 (M : Matrix (Fin n) (Fin n) K) →
    FlagCond (fun c : K => c = 0) ρ k 0 (M' : Matrix (Fin n) (Fin n) K) → M ∈ unipSym K n ρ k := by
  intro K _ n ρ k hn M M' hrel hM hM'
  subst hn

  have hkey : (M' : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K)ᵀ * flagGram K (2 * ρ + k + 1) ρ k =
      flagGram K (2 * ρ + k + 1) ρ k * ((M⁻¹ : GL (Fin (2 * ρ + k + 1)) K) : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) := by
    have h := congrArg (· * ((M⁻¹ : GL (Fin (2 * ρ + k + 1)) K) : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K)) hrel
    simp only [Matrix.mul_assoc] at h
    rw [← h, Units.mul_inv, Matrix.mul_one]

  have hN : ∀ p q : Fin (2 * ρ + k + 1), ρ + k < p.val → q.val ≤ p.val →
      ((M⁻¹ : GL (Fin (2 * ρ + k + 1)) K) : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q = (1 : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q := by
    intro p q hp hq
    have hp2 := p.2
    have hq2 := q.2
    have h1 := congrFun (congrFun hkey ⟨dualIdx ρ k p.val, dualIdx_lt' p.2⟩) q
    rw [mul_flagGram_apply, flagGram_mul_apply, transpose_apply] at h1
    have e1 : (⟨dualIdx ρ k (dualIdx ρ k p.val), dualIdx_lt' (dualIdx_lt' p.2)⟩ : Fin (2 * ρ + k + 1)) = p :=
      Fin.ext ((dualIdx_iff' p.2 (dualIdx_lt' p.2)).mpr rfl).symm
    have hs : (if dualIdx ρ k p.val = ρ + k then (-1 : K) else 1) = 1 :=
      if_neg (by unfold dualIdx; split_ifs <;> omega)
    simp only [Fin.val_mk] at h1
    rw [e1, hs, one_mul] at h1
    have hc := hM'.1 ⟨dualIdx ρ k q.val, dualIdx_lt' q.2⟩ ⟨dualIdx ρ k p.val, dualIdx_lt' p.2⟩
      (by simp only [Fin.val_mk]; unfold dualIdx; split_ifs <;> omega)
      (by simp only [Fin.val_mk]; unfold dualIdx; split_ifs <;> omega)
    simp only [Matrix.sub_apply, sub_eq_zero] at hc
    rw [← h1, hc]
    by_cases hpq : p = q
    · subst hpq
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, hs, one_mul]
    · have hne : (⟨dualIdx ρ k q.val, dualIdx_lt' q.2⟩ : Fin (2 * ρ + k + 1)) ≠ ⟨dualIdx ρ k p.val, dualIdx_lt' p.2⟩ := by
        intro h
        apply hpq
        have h' := congrArg Fin.val h
        simp only [Fin.val_mk] at h'
        apply Fin.ext
        unfold dualIdx at h'
        split_ifs at h' <;> omega
      rw [Matrix.one_apply_ne hne, zero_mul, Matrix.one_apply_ne hpq]

  have hMrow : ∀ t, ∀ p q : Fin (2 * ρ + k + 1), p.val + t = 2 * ρ + k → ρ + k < p.val → q.val ≤ p.val →
      (M : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q = (1 : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro p q ht hp hq
      have hNM : (((M⁻¹ : GL (Fin (2 * ρ + k + 1)) K) : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) * (M : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K)) p q = (1 : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q := by
        rw [Units.inv_mul]
      rw [Matrix.mul_apply, Finset.sum_eq_single p] at hNM
      · rw [hN p p hp le_rfl, Matrix.one_apply_eq, one_mul] at hNM
        exact hNM
      · intro l _ hl
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hl) with h | h
        · rw [hN p l hp (le_of_lt h), Matrix.one_apply_ne (fun e => hl (e.symm)), zero_mul]
        · have hl2 := l.2
          rw [ih (2 * ρ + k - l.val) (by omega) l q (by omega) (by omega) (by omega),
            Matrix.one_apply_ne (fun e => by rw [e] at h; omega), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hall : ∀ i j : Fin (2 * ρ + k + 1), j.val ≤ i.val → (M : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) i j = (1 : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) i j := by
    intro i j hji
    have hi2 := i.2
    by_cases h1 : j.val < ρ
    · have h := hM.1 i j h1 hji
      simp only [Matrix.sub_apply, sub_eq_zero] at h
      exact h
    by_cases h2 : j.val < ρ + k
    · have h := hM.2.2 i j (by omega) h2 hji
      simp only [Matrix.sub_apply, one_mul, sub_eq_zero] at h
      exact h
    by_cases h3 : j.val = ρ + k
    · have h := hM.2.1 i j h3 (by omega)
      simp only [Matrix.sub_apply, sub_eq_zero] at h
      exact h
    · exact hMrow (2 * ρ + k - i.val) i j (by omega) (by omega) hji
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j h0 h1 h2 => ?_⟩
  · have hij' : j.val < i.val := hij
    rw [hall i j (le_of_lt hij'), Matrix.one_apply_ne (fun e => by rw [e] at hij'; omega)]
  · rw [hall i i le_rfl, Matrix.one_apply_eq]
  · have h := hM.2.1 i j h2 h0
    simp only [Matrix.sub_apply, sub_eq_zero] at h
    rw [h, Matrix.one_apply_ne (fun e => by rw [e] at h1; omega)]

end GlobalTheory.FlagCase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricUnipotentMemOfFlagCongruenceDualStatement
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricUnipotent_mem_of_flagCongruence_dual : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K, (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k → FlagCond (fun c : K => c = 0) ρ k 1 (M : Matrix (Fin n) (Fin n) K) → FlagCond (fun c : K => c = 0) ρ k 0 (M' : Matrix (Fin n) (Fin n) K) → M ∈ unipSym K n ρ k := by
  first | exact @GlobalTheory.FlagCase.flagCond_dual_unipSym | exact GlobalTheory.FlagCase.flagCond_dual_unipSym | (intros; apply GlobalTheory.FlagCase.flagCond_dual_unipSym <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricUnipotentMemOfFlagBasisDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricUnipotentMemOfFlagBasisDual
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.FlagDual

theorem dualIdx_lt {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) {i : ℕ} (hi : i < n) : dualIdx ρ k i < n := by
  unfold dualIdx; split_ifs <;> omega

theorem dualIdx_dualIdx {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) {i : ℕ} (hi : i < n) :
    dualIdx ρ k (dualIdx ρ k i) = i := by
  unfold dualIdx; split_ifs <;> omega

theorem dualIdx_eq_self_iff {n ρ k i : ℕ} (hn : n = 2 * ρ + k + 1) (hi : i < n) : dualIdx ρ k i = ρ + k ↔ i = ρ + k := by
  unfold dualIdx; split_ifs <;> omega

def tau {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (i : Fin n) : Fin n := ⟨dualIdx ρ k i.val, dualIdx_lt hn i.2⟩

def sgn (K : Type) [CommRing K] (ρ k : ℕ) {n : ℕ} (i : Fin n) : K := if i.val = ρ + k then -1 else 1

theorem sgn_mul_self (K : Type) [CommRing K] (ρ k : ℕ) {n : ℕ} (i : Fin n) : sgn K ρ k i * sgn K ρ k i = 1 := by
  unfold sgn; split_ifs <;> simp

theorem gram_col (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (i j : Fin n) :
    flagGram K n ρ k i j = if i = tau hn j then sgn K ρ k j else 0 := by
  have hi := dualIdx_dualIdx hn i.2
  have hj := dualIdx_dualIdx hn j.2
  unfold flagGram sgn
  by_cases h1 : j.val = dualIdx ρ k i.val
  · have h2 : i = tau hn j := by
      ext; show i.val = dualIdx ρ k j.val; rw [h1, hi]
    rw [if_pos h1, if_pos h2]
    have h3 : (i.val = ρ + k ↔ j.val = ρ + k) := by
      rw [h1, dualIdx_eq_self_iff hn i.2]
    by_cases h4 : i.val = ρ + k
    · rw [if_pos h4, if_pos (h3.1 h4)]
    · rw [if_neg h4, if_neg (fun h => h4 (h3.2 h))]
  · have h2 : i ≠ tau hn j := by
      intro h; apply h1; rw [h]; show j.val = dualIdx ρ k (dualIdx ρ k j.val); rw [hj]
    rw [if_neg h1, if_neg h2]

theorem gram_row (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (i j : Fin n) :
    flagGram K n ρ k i j = if j = tau hn i then sgn K ρ k i else 0 := by
  unfold flagGram sgn
  by_cases h1 : j.val = dualIdx ρ k i.val
  · rw [if_pos h1, if_pos (Fin.ext h1)]
  · rw [if_neg h1, if_neg (fun h => h1 (congrArg Fin.val h))]

theorem gram_mul_gram (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) :
    flagGram K n ρ k * flagGram K n ρ k = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau hn i)]
  · rw [gram_row K hn i (tau hn i), if_pos rfl, gram_row K hn (tau hn i) j]
    have hii : tau hn (tau hn i) = i := Fin.ext (dualIdx_dualIdx hn i.2)
    rw [hii]
    by_cases hij : j = i
    · subst hij; rw [if_pos rfl, one_apply_eq]
      have : sgn K ρ k (tau hn j) = sgn K ρ k j := by
        unfold sgn tau; simp only [dualIdx_eq_self_iff hn j.2]
      rw [this, sgn_mul_self]
    · rw [if_neg hij, mul_zero, one_apply_ne (Ne.symm hij)]
  · intro b _ hb; rw [gram_row K hn i b, if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem gram_conj_apply (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1)
    (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (flagGram K n ρ k * A * flagGram K n ρ k) i j = sgn K ρ k i * sgn K ρ k j * A (tau hn i) (tau hn j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau hn j)]
  · rw [gram_col K hn (tau hn j) j, if_pos rfl, Matrix.mul_apply, Finset.sum_eq_single (tau hn i)]
    · rw [gram_row K hn i (tau hn i), if_pos rfl]; ring
    · intro b _ hb; rw [gram_row K hn i b, if_neg hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb; rw [gram_col K hn b j, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.FlagDual

namespace GlobalTheory.FlagDual

theorem dual_apply (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (M M' : GL (Fin n) K)
    (h : (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k)
    (i j : Fin n) :
    (M' : Matrix (Fin n) (Fin n) K) i j =
      sgn K ρ k j * sgn K ρ k i * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (tau hn j) (tau hn i) := by
  set G := flagGram K n ρ k
  have h1 : (M' : Matrix (Fin n) (Fin n) K)ᵀ * G = G * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have hM : (M : Matrix (Fin n) (Fin n) K) * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (M' : Matrix (Fin n) (Fin n) K)ᵀ * G
        = (M' : Matrix (Fin n) (Fin n) K)ᵀ * G * ((M : Matrix (Fin n) (Fin n) K) *
            ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [hM, Matrix.mul_one]
      _ = G * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [← Matrix.mul_assoc, h]
  have h2 : (M' : Matrix (Fin n) (Fin n) K)ᵀ = G * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * G := by
    rw [← h1, Matrix.mul_assoc, gram_mul_gram K hn, Matrix.mul_one]
  have h3 := congrFun (congrFun h2 j) i
  rw [transpose_apply] at h3
  rw [h3, gram_conj_apply K hn]

end GlobalTheory.FlagDual

theorem GlobalTheory.FlagDual.unipSym_of_dual :
    ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K,
      (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k →
      M ∈ unipSym K n ρ k → M' ∈ unipSym K n ρ k := by
  intro K _ n ρ k hn M M' h hM
  have hN : M⁻¹ ∈ unipSym K n ρ k := Subgroup.inv_mem _ hM
  obtain ⟨⟨hNl, hNd⟩, hNc⟩ := hN
  have hd := GlobalTheory.FlagDual.dual_apply K hn M M' h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j hji
    have hji' : j.val < i.val := hji
    rw [hd i j]
    by_cases hi : i.val = ρ + k
    · by_cases hj : j.val < ρ
      · rw [hNl (show (GlobalTheory.FlagDual.tau hn i).val < (GlobalTheory.FlagDual.tau hn j).val by
          show dualIdx ρ k i.val < dualIdx ρ k j.val
          unfold dualIdx; split_ifs <;> omega), mul_zero]
      · rw [hNc (GlobalTheory.FlagDual.tau hn j) (GlobalTheory.FlagDual.tau hn i)
          (by show ρ ≤ dualIdx ρ k j.val; unfold dualIdx; split_ifs <;> omega)
          (by show dualIdx ρ k j.val < ρ + k; unfold dualIdx; split_ifs <;> omega)
          (by show dualIdx ρ k i.val = ρ + k; unfold dualIdx; split_ifs <;> omega), mul_zero]
    · rw [hNl (show (GlobalTheory.FlagDual.tau hn i).val < (GlobalTheory.FlagDual.tau hn j).val by
        have := i.2; have := j.2
        show dualIdx ρ k i.val < dualIdx ρ k j.val
        unfold dualIdx; split_ifs <;> omega), mul_zero]
  · intro i
    rw [hd i i, hNd, mul_one, GlobalTheory.FlagDual.sgn_mul_self]
  · intro i j h0 h1 h2
    rw [hd i j, hNl (show (GlobalTheory.FlagDual.tau hn i).val < (GlobalTheory.FlagDual.tau hn j).val by
      show dualIdx ρ k i.val < dualIdx ρ k j.val
      unfold dualIdx; split_ifs <;> omega), mul_zero]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricUnipotentMemOfFlagBasisDualStatement
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricUnipotent_mem_of_flagBasisDual : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K, (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k → M ∈ unipSym K n ρ k → M' ∈ unipSym K n ρ k := by
  first | exact @GlobalTheory.FlagDual.unipSym_of_dual | exact GlobalTheory.FlagDual.unipSym_of_dual | (intros; apply GlobalTheory.FlagDual.unipSym_of_dual <;> assumption)
end
end

noncomputable section

namespace GlobalTheory.FlagBasis

section Alg
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV
open scoped TensorProduct

theorem flagCond_map {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B) (P : B → Prop) (ρ k : ℕ) (ε : A)
    (m : Matrix (Fin n) (Fin n) A) :
    FlagCond P ρ k (f ε) (m.map f) ↔ FlagCond (fun a => P (f a)) ρ k ε m := by
  have e : ∀ i j, (m.map f - 1) i j = f ((m - 1) i j) := fun i j => by
    simp only [Matrix.sub_apply, Matrix.map_apply, map_sub, Matrix.one_apply]
    split_ifs <;> simp
  simp only [FlagCond, e, ← map_mul]

theorem rootSum_map {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B) (ρ k : ℕ) (ε : A)
    (m : Matrix (Fin n) (Fin n) A) : rootSum ρ k (f ε) (m.map f) = f (rootSum ρ k ε m) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rootSum, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem flagGram_transpose (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) :
    (flagGram K n ρ k)ᵀ = flagGram K n ρ k := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [Matrix.transpose_apply, flagGram, dualIdx]
  split_ifs <;> first | rfl | omega

theorem flagCond_of_unipSym {K : Type} [CommRing K] {n ρ k : ℕ} (ε : K) {M : GL (Fin n) K} (hM : M ∈ unipSym K n ρ k) :
    FlagCond (fun c : K => c = 0) ρ k ε (M : Matrix (Fin n) (Fin n) K) := by
  have low : ∀ i j : Fin n, j.val ≤ i.val → ((M : Matrix (Fin n) (Fin n) K) - 1) i j = 0 := by
    intro i j h
    rcases eq_or_lt_of_le h with h | h
    · obtain rfl : j = i := Fin.ext h
      simp [unip_diag hM.1]
    · rw [Matrix.sub_apply, unip_lower hM.1 (show j < i from h), Matrix.one_apply_ne (ne_of_gt (show j < i from h)), sub_zero]
  refine ⟨fun i j _ h => low i j h, fun i j hj hi => ?_, fun i j _ _ h => by rw [low i j h, mul_zero]⟩
  by_cases h : j.val ≤ i.val
  · exact low i j h
  · rw [Matrix.sub_apply, hM.2 i j hi (by omega) hj, Matrix.one_apply_ne (fun e => h (by rw [e])), sub_zero]

theorem flagCond_iff_unipSym {K : Type} [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) {ε ε' : K}
    (hε : (ε = 1 ∧ ε' = 0) ∨ (ε = 0 ∧ ε' = 1)) (M M' : GL (Fin n) K)
    (h : (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k) :
    FlagCond (fun c : K => c = 0) ρ k ε (M : Matrix (Fin n) (Fin n) K) ∧
      FlagCond (fun c : K => c = 0) ρ k ε' (M' : Matrix (Fin n) (Fin n) K) ↔ M ∈ unipSym K n ρ k := by
  have h' : (M : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M' : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k := by
    have := congrArg Matrix.transpose h
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, flagGram_transpose K hn,
      ← Matrix.mul_assoc] at this
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun hM => ⟨flagCond_of_unipSym _ hM, flagCond_of_unipSym _ (GlobalTheory.T.symmetricUnipotent_mem_of_flagBasisDual K n ρ k hn M M' h hM)⟩⟩
  rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact GlobalTheory.T.symmetricUnipotent_mem_of_flagCongruence_dual K n ρ k hn M M' h h1 h2
  · exact GlobalTheory.T.symmetricUnipotent_mem_of_flagBasisDual K n ρ k hn M' M h' (GlobalTheory.T.symmetricUnipotent_mem_of_flagCongruence_dual K n ρ k hn M' M h' h2 h1)

theorem map_eq_zero_of_zmod (I : AutInst) {g : ℕ} {K : Type} [CommRing K] (p : Formalism.L2.Herm.intAf I.F I.E →+* K)
    (hg : (g : K) = 0) {s : Formalism.L2.Herm.intAf I.F I.E} (hs : ZMod' I g s) : p s = 0 := by
  obtain ⟨t, ht, e⟩ := hs
  have : s = (g : Formalism.L2.Herm.intAf I.F I.E) * ⟨t, ht⟩ := Subtype.ext (by simpa using e)
  rw [this, map_mul, map_natCast, hg, zero_mul]

theorem kset_iff (I : AutInst) {β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (hβ : IsFrame β I.L) (x : I.Gf) :
    x ∈ I.Kset ↔ (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β := by
  have e : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
    show Submodule.span _ _ = Submodule.span _ _
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.1, z.2, rfl⟩
  rw [GlobalTheory.LevSplit.mem_St_iff β I.L hβ, e]
  refine ⟨fun h => ⟨fun y hy => Formalism.L2.SG.Pf.unitaryCongruence.K_mv I h hy,
    fun y hy => Formalism.L2.SG.Pf.unitaryCongruence.K_mv I (Formalism.L2.SG.Pf.unitaryCongruence.K_inv I h) hy⟩, fun h y => ⟨h.1 y, fun hy => ?_⟩⟩
  have := h.2 _ hy
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

theorem read_in_frame (I : AutInst) (g : ℕ) (hg : g ≠ 0) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)
    (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (hF : IsRefFrame I g e0 f0 z0 bw bwd ew) (hn : I.n = 2 * ρ + k + 1)
    (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (hβ : IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β)
    (Pg : Finset (Pl I.E)) (hdiv : ∀ PP ∈ Pg, (g : 𝓞 I.E) ∈ PP.asIdeal)
    (hN : ∀ s : Formalism.L2.Herm.intAf I.F I.E,
      (∀ PP ∈ Pg, resS I.F PP s = 0 ∧ resS I.F PP (sigInt I s) = 0) → ZMod' I g s)
    (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ) (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
    (hint : ∀ x ∈ IntAf I.F I.E, psiEf x = 1)
    (ψ0 : ∀ PP : Pl I.E, AddChar (kP PP) ℂ) (a₁ a₂ : ∀ PP : Pl I.E, kP PP) (ha : ∀ PP ∈ Pg, a₁ PP ≠ 0 ∧ a₂ PP ≠ 0)
    (hχ : ∀ s : Formalism.L2.Herm.intAf I.F I.E, star (psiEf (divN I g s.1)) =
      ∏ PP ∈ Pg, ψ0 PP (a₁ PP * resS I.F PP s + a₂ PP * resS I.F PP (sigInt I s))) :
    ∃ a : ∀ PP : Pl I.E, Fin I.n → Fin I.n → kP PP, (∀ PP ∈ Pg, ∀ i j, symEdge ρ k i j → a PP i j ≠ 0) ∧
      ∀ x : I.Gf, (x ∈ K2set I g e0 z0 bw ↔ (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β ∧
          ∀ PP ∈ Pg, redFn β PP x ∈ unipSym (kP PP) I.n ρ k) ∧
        (x ∈ K2set I g e0 z0 bw → star (chi2f I psiEf g e0 f0 z0 bw bwd x) =
          ∏ PP ∈ Pg, ψ0 PP (∑ i, ∑ j, if symEdge ρ k i j then
            a PP i j * ((redFn β PP x : GL (Fin I.n) (kP PP)) : Matrix (Fin I.n) (Fin I.n) (kP PP)) i j else 0)) := by
  classical
  obtain ⟨hew, hG⟩ := GlobalTheory.T.liftFrame_gram_congr_flagGram I g e0 f0 z0 bw bwd ew hF hn β hβ
  have hpg : ∀ PP ∈ Pg, (g : kP PP) = 0 := fun PP hPP => by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hdiv PP hPP)
  let ewS : Formalism.L2.Herm.intAf I.F I.E := ⟨ew, hF.2.2.2.2.1.2.2.1⟩
  let p' : ∀ PP : Pl I.E, Formalism.L2.Herm.intAf I.F I.E →+* kP PP := fun PP => (resS I.F PP).comp (sigInt I)
  have hε : ∀ PP ∈ Pg, (resS I.F PP ewS = 1 ∧ p' PP ewS = 0) ∨ (resS I.F PP ewS = 0 ∧ p' PP ewS = 1) := by
    intro PP hPP
    have h1 : resS I.F PP (1 - ewS - sigInt I ewS) = 0 := map_eq_zero_of_zmod I _ (hpg PP hPP) hew
    have h2 : ewS * sigInt I ewS = 0 := Subtype.ext hF.2.2.2.2.1.2.1
    have h3 : resS I.F PP ewS * p' PP ewS = 0 := by
      show _ * resS I.F PP (sigInt I ewS) = 0
      rw [← map_mul, h2, map_zero]
    rw [map_sub, map_sub, map_one] at h1
    have h1' : 1 - resS I.F PP ewS - p' PP ewS = 0 := h1
    haveI := PP.isPrime
    rcases mul_eq_zero.1 h3 with h | h
    · exact Or.inr ⟨h, by rw [h] at h1'; linear_combination -h1'⟩
    · exact Or.inl ⟨by rw [h] at h1'; linear_combination -h1', h⟩
  have hZ : ∀ s : Formalism.L2.Herm.intAf I.F I.E, ZMod' I g s ↔ ∀ PP ∈ Pg, resS I.F PP s = 0 ∧ p' PP s = 0 :=
    fun s => ⟨fun h PP hPP => ⟨map_eq_zero_of_zmod I _ (hpg PP hPP) h, map_eq_zero_of_zmod I _ (hpg PP hPP) h⟩, hN s⟩
  have hroot := fun (PP : Pl I.E) (hPP : PP ∈ Pg) => GlobalTheory.T.flagRootSum_dual_eq_symmetricEdge_sum (kP PP) I.n ρ k hn _ _ (a₁ PP) (a₂ PP) (hε PP hPP)
    (ha PP hPP).1 (ha PP hPP).2
  choose! a ha1 ha2 using hroot
  have hmat : ∀ (x : I.Gf) (m : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)),
      frGL β m = (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) →
      matIn I β x = (m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map (Formalism.L2.Herm.intAf I.F I.E).subtype := by
    intro x m hm
    unfold matIn
    rw [← hm]
    have : β⁻¹ * frGL β m * β = intGL I.F I.E I.n m := by
      simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    rfl
  have hrel := fun (x : I.Gf) m hm (PP : Pl I.E) (hPP : PP ∈ Pg) =>
    GlobalTheory.T.unitary_liftedFlagBasis_reduce_mod_level I g ρ k β hG (kP PP) (resS I.F PP) (hpg PP hPP) x m hm
  have main : ∀ x : I.Gf, x ∈ K2set I g e0 z0 bw ↔ (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β ∧
      ∀ PP ∈ Pg, redFn β PP x ∈ unipSym (kP PP) I.n ρ k := by
    intro x
    show x ∈ I.Kset ∧ _ ↔ _
    rw [kset_iff I hβ.1]
    refine and_congr_right fun hS => ?_
    rw [GlobalTheory.T.levelCongruence_iff_flag_conditions I g e0 f0 z0 bw bwd ew hF hn β hβ x hS]
    obtain ⟨m, hm⟩ := hS
    rw [hmat x m hm, ← hm]
    refine (flagCond_map (Formalism.L2.Herm.intAf I.F I.E).subtype (ZMod' I g) ρ k ewS _).trans ?_
    have e : ∀ PP ∈ Pg, (redFn β PP (frGL β m) ∈ unipSym (kP PP) I.n ρ k ↔
        FlagCond (fun s => resS I.F PP s = 0) ρ k ewS m.1 ∧ FlagCond (fun s => p' PP s = 0) ρ k ewS m.1) := by
      intro PP hPP
      rw [redFn_frGL, ← flagCond_iff_unipSym hn (hε PP hPP) (Formalism.UG.bc (resS I.F PP) m) (Formalism.UG.bc (p' PP) m) (hrel x m hm PP hPP)]
      exact and_congr (flagCond_map (resS I.F PP) (fun c => c = 0) ρ k ewS m.1) (flagCond_map (p' PP) (fun c => c = 0) ρ k ewS m.1)
    rw [forall₂_congr e]
    constructor
    · rintro ⟨h1, h2, h3⟩ PP hPP
      exact ⟨⟨fun i j a b => ((hZ _).1 (h1 i j a b) PP hPP).1, fun i j a b => ((hZ _).1 (h2 i j a b) PP hPP).1,
          fun i j a b c => ((hZ _).1 (h3 i j a b c) PP hPP).1⟩,
        ⟨fun i j a b => ((hZ _).1 (h1 i j a b) PP hPP).2, fun i j a b => ((hZ _).1 (h2 i j a b) PP hPP).2,
          fun i j a b c => ((hZ _).1 (h3 i j a b c) PP hPP).2⟩⟩
    · intro h
      exact ⟨fun i j a b => (hZ _).2 fun PP hPP => ⟨(h PP hPP).1.1 i j a b, (h PP hPP).2.1 i j a b⟩,
        fun i j a b => (hZ _).2 fun PP hPP => ⟨(h PP hPP).1.2.1 i j a b, (h PP hPP).2.2.1 i j a b⟩,
        fun i j a b c => (hZ _).2 fun PP hPP => ⟨(h PP hPP).1.2.2 i j a b c, (h PP hPP).2.2.2 i j a b c⟩⟩
  refine ⟨a, ha1, fun x => ⟨main x, fun hx => ?_⟩⟩
  obtain ⟨hS, hU⟩ := (main x).1 hx
  have hc := GlobalTheory.T.characterArgument_congr_rootEntrySum_mod I g e0 f0 z0 bw bwd ew hF hn β hβ hG x hS
  obtain ⟨m, hm⟩ := hS
  rw [hmat x m hm] at hc
  have hr := rootSum_map (Formalism.L2.Herm.intAf I.F I.E).subtype ρ k ewS m.1
  have hc' : ZMod' I g (chiArg I e0 f0 z0 bw bwd x - (rootSum ρ k ewS m.1).1) := by
    have hr' : rootSum ρ k ew (m.1.map (Formalism.L2.Herm.intAf I.F I.E).subtype) = (rootSum ρ k ewS m.1).1 := hr
    rwa [hr'] at hc
  have e1 : chi2f I psiEf g e0 f0 z0 bw bwd x = psiEf (divN I g (rootSum ρ k ewS m.1).1) := by
    obtain ⟨t, ht, e⟩ := hc'
    rw [flagLevelCharacter_eq_psi_divN, eq_add_of_sub_eq e, Formalism.L2.SG.Pf.unitaryCongruence.divN_add, hadd, Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul _ _ hg, hint t ht, one_mul]
  rw [e1, hχ]
  refine Finset.prod_congr rfl fun PP hPP => congrArg _ ?_
  have hU' := hU PP hPP
  rw [← hm, redFn_frGL] at hU' ⊢
  rw [← ha2 PP hPP (Formalism.UG.bc (resS I.F PP) m) (Formalism.UG.bc (p' PP) m) (hrel x m hm PP hPP) hU']
  exact congrArg₂ (· + ·) (congrArg _ (rootSum_map (resS I.F PP) ρ k ewS m.1).symm)
    (congrArg _ (rootSum_map (p' PP) ρ k ewS m.1).symm)

end Alg

end GlobalTheory.FlagBasis

section Host
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.FlagBasis.read_inst (D : D7) (e0 f0 : Fin D.R.rS → VA (instOf D)) (z0 : VA (instOf D))
    (bw bwd : Fin D.R.k → VA (instOf D)) (ew : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F)
    (hF : IsRefFrame (instOf D) (D.host.g 0 * D.host.g 1) e0 f0 z0 bw bwd ew) (hn : (instOf D).n = D.R.r)
    (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ) (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
    (hint : ∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1)
    (hrat : ∀ x : (instOf D).E,
      psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1)
    (Pg : Finset (Pl D.host.E)) (hPg : GlobalTheory.Core.Mi.IsTypePlaces Pg)
    (hnc : ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP')
    (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (hψ : IsGenericPsi Pg ψ0) :
    ∃ β : GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D),
      IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0) ∧
      ∀ x : (instOf D).Gf, (x ∈ K2set (instOf D) (D.host.g 0 * D.host.g 1) e0 z0 bw ↔
          (x.1 : GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D)) ∈ St β ∧
          ∀ PP ∈ Pg, redFn β PP x.1 ∈ unipSym (kP PP) (D.sp.Y 0).rank D.R.rS D.R.k) ∧
        (x ∈ K2set (instOf D) (D.host.g 0 * D.host.g 1) e0 z0 bw →
          star (chi2f (instOf D) psiEf (D.host.g 0 * D.host.g 1) e0 f0 z0 bw bwd x) =
          ∏ PP ∈ Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (redFn β PP x.1))) := by
  have hg : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hn' : (instOf D).n = 2 * D.R.rS + D.R.k + 1 := by
    rw [hn]
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.r Ranks.rS
    omega
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.flagVec_mem_Lf_and_inMod (instOf D) _ e0 f0 z0 bw bwd ew hF hn'
  obtain ⟨β₀, hβ₀⟩ := GlobalTheory.T.exists_latticeFrame_lifting_spanning_vectors_mod D _ hg _ hs1 hs2
  have hN : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (∀ PP ∈ Pg, resS D.host.F PP s = 0 ∧ resS D.host.F PP (sigInt (instOf D) s) = 0) →
      ZMod' (instOf D) (D.host.g 0 * D.host.g 1) s.1 := by
    intro s hs
    refine GlobalTheory.T.integralAdele_congr_zero_of_residues_squarefree (instOf D) _ hg (GlobalTheory.T.typePrimes_product_not_mem_sq_place D) s fun Q hQ => ?_
    obtain ⟨PP, hPP, rfl | h⟩ := GlobalTheory.T.typePrimePlace_mem_or_conj_genusTypePlaceSet D Pg hPg Q hQ
    · exact (hs _ hPP).1
    · exact (h s).2 (hs _ hPP).2
  obtain ⟨a₁, a₂, ha, hχ⟩ := GlobalTheory.T.character_residueFields_eq_prod_genericShift D.host.E (Formalism.L2.Herm.intAf D.host.F D.host.E) Pg (fun PP => resS D.host.F PP)
    (fun PP => (resS D.host.F PP).comp (sigInt (instOf D)))
    (fun s => star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1))) ψ0 hψ
    (fun s t => (congrArg (fun z => star (psiEf z))
        (Formalism.L2.SG.Pf.unitaryCongruence.divN_add (instOf D) (D.host.g 0 * D.host.g 1) s.1 t.1)).trans (by rw [hadd, star_mul']))
    (fun s hs => by
      obtain ⟨t, ht, e⟩ := hN s hs
      have : divN (instOf D) (D.host.g 0 * D.host.g 1) s.1 = t :=
        (congrArg _ e).trans (Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul _ _ hg t)
      show star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1)) = 1
      rw [this, hint t ht, star_one])
    (GlobalTheory.T.exists_integralAdele_prescribed_residues_and_conj D Pg hnc)
    (GlobalTheory.T.residueSupport_single_place_to_conjugatePair_position D Pg hPg.1 hnc (fun s => star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1)) ≠ 1) fun Q hQ => by
      obtain ⟨s, h1, h2⟩ := GlobalTheory.T.exists_finiteAdditiveChar_ne_one_at_each_prime D psiEf hadd hint hrat Q hQ
      exact ⟨s, h1, fun h => h2 (by simpa using congrArg star h)⟩)
  obtain ⟨a, ha1, hK⟩ := read_in_frame (instOf D) _ hg e0 f0 z0 bw bwd ew hF hn' β₀ hβ₀ Pg hPg.1 hN psiEf hadd hint ψ0 a₁ a₂ ha hχ
  have hL : (instOf D).L = Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 := Lv_eq_map D
  obtain ⟨β, hβ, hSt, hred⟩ := GlobalTheory.T.exists_diagonal_frame_change_unweighting_symEdges (D := D) (n := (D.sp.Y 0).rank) D.R.rS D.R.k Pg _ β₀ hβ₀.1 a ha1
  refine ⟨β, hL ▸ hβ, fun x => ⟨?_, fun hx => ?_⟩⟩
  · rw [hSt]
    exact (hK x).1.trans (and_congr_right fun hS => forall₂_congr fun PP hPP => (hred PP hPP _ hS).1.symm)
  · exact ((hK x).2 hx).trans
      (Finset.prod_congr rfl fun PP hPP => congrArg _ (hred PP hPP _ ((hK x).1.1 hx).1).2)

end Host

section Main
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeConjRead

open Formalism.L2.DIV

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {n : ℕ} (hr : n ≤ n) (g : GL (Fin n) κ) : upperLeftBlock hr g = g := by
  have hg : g ∈ blockTri (κ := κ) (blk2 n) := fun i j h => by
    simp [blk2, i.2, j.2] at h
  apply Units.ext
  rw [upper_block_val_submatrix hr hg]
  ext i j
  simp

theorem blockTri_blkOf_top {κ : Type} [CommRing κ] {n r : ℕ} (t : ℕ) (hn : n ≤ r) (g : GL (Fin n) κ) :
    g ∈ blockTri (κ := κ) (blkOf r t) := fun i j h => by
  have hi : i.val < r := lt_of_lt_of_le i.2 hn
  have hj : j.val < r := lt_of_lt_of_le j.2 hn
  simp [blkOf, hi, hj] at h

theorem iotaX_fst_eq_one_iff {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (κ : GA D (D.sp.Y 0)) : (iotaX X h κ).1 = 1 ↔ κ ∈ GfC (D.sp.Y 0) := by
  have key : ∀ (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D)
      (y : (Formalism.L2.SG.InstExistsPf.instOf D).GA), ((castGA hI.symm) y).1 = 1 ↔ y.1 = 1 := by
    intro I hI y
    subst hI
    exact Iff.rfl
  show ((castGA h.symm) (Formalism.IndefR.RationalEmbedding.iota D κ)).1 = 1 ↔ _
  rw [key X.B.I h, ← Formalism.L2.SG.EvalTIota.brg_mem_GfC_i, ContinuousMulEquiv.symm_apply_apply]

theorem eq_symm_one {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (κ : GA D (D.sp.Y 0)) (h1 : (iotaX X h κ).1 = 1) : (iotaX X h).symm (1, (iotaX X h κ).2) = κ := by
  rw [ContinuousMulEquiv.symm_apply_eq]
  exact Prod.ext h1.symm rfl

end GlobalTheory.SeeConjRead

theorem GlobalTheory.SeeConjRead.read_fin {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (Pg : Finset (Pl D.host.E)) (hPg : GlobalTheory.Core.Mi.IsTypePlaces Pg)
    (hnc : ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP')
    (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (hψ : IsGenericPsi Pg ψ0) :
    ∃ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D),
      Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0) ∧
      ∀ κ : GA D (D.sp.Y 0), ((iotaX X h κ).2 ∈ X.K2 ↔ Lev.finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β ∧
          ∀ PP ∈ Pg, redFn β PP (Lev.finE (D.sp.Y 0) κ) ∈ unipSym (kP PP) (D.sp.Y 0).rank D.R.rS D.R.k) ∧
        ((iotaX X h κ).2 ∈ X.K2 → star (X.chi2 (iotaX X h κ).2) =
          ∏ PP ∈ Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (redFn β PP (Lev.finE (D.sp.Y 0) κ)))) := by
  have key : ∀ (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (g : ℕ) (_ : g = D.host.g 0 * D.host.g 1)
      (e0 f0 : Fin D.R.rS → VA I) (z0 : VA I) (bw bwd : Fin D.R.k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
      (_ : GlobalTheory.FlagBasis.IsRefFrame I g e0 f0 z0 bw bwd ew) (_ : I.n = D.R.r) (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ)
      (_ : ∀ x y, psiEf (x + y) = psiEf x * psiEf y) (_ : ∀ x ∈ IntAf I.F I.E, psiEf x = 1)
      (_ : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) * psiEinf I x = 1),
      ∃ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D),
      Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0) ∧
      ∀ κ : GA D (D.sp.Y 0), ((castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ K2set I g e0 z0 bw ↔
          Lev.finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β ∧
          ∀ PP ∈ Pg, redFn β PP (Lev.finE (D.sp.Y 0) κ) ∈ unipSym (kP PP) (D.sp.Y 0).rank D.R.rS D.R.k) ∧
        ((castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ K2set I g e0 z0 bw →
          star (chi2f I psiEf g e0 f0 z0 bw bwd (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2) =
          ∏ PP ∈ Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (redFn β PP (Lev.finE (D.sp.Y 0) κ)))) := by
    intro I hI g hg e0 f0 z0 bw bwd ew hF hn psiEf hadd hint hrat
    subst hI hg
    obtain ⟨β, hβ, hK⟩ := GlobalTheory.FlagBasis.read_inst D e0 f0 z0 bw bwd ew hF hn psiEf hadd hint hrat Pg hPg hnc ψ0 hψ
    refine ⟨β, hβ, fun κ => ?_⟩
    have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    have e2 : Lev.finE (D.sp.Y 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) :=
      (congrArg (Lev.finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
    have hx := hK (Formalism.IndefR.RationalEmbedding.iota D κ).2
    generalize Lev.finE (D.sp.Y 0) κ = y at e2 ⊢
    subst e2
    exact hx
  exact key X.B.I h X.B.g X.g_eq X.e0 X.f0 X.z0 X.bw X.bwd X.ew (GlobalTheory.FlagBasis.isRefFrame_setting X) X.n_eq X.psiEf
    X.psiEf_add X.psiEf_int X.psiEf_rat

end Main

end
