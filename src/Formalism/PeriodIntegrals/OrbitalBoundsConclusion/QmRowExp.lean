module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFirstColumn.FirstColumnSplitBijective
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerProductCast.OfFnProdIntCast
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.ExistsIntegralMultiple
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocOProj

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowExp
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowExpansionMinor.FirstColumnSplitBijective
open Finset

noncomputable section

namespace PI.QmRowExpWork

open Formalism.REAL

def cyc0 (m : ℕ) (j : Fin (m + 1)) : Equiv.Perm (Fin (m + 1)) := (Fin.cycleRange j).symm

theorem cycle_perm_zero (m : ℕ) (j : Fin (m + 1)) : cyc0 m j 0 = j := by
  apply (Fin.cycleRange j).injective
  simp [cyc0, Fin.cycleRange_self]

theorem cycle_perm_succ (m : ℕ) (j : Fin (m + 1)) (k : Fin m) : cyc0 m j k.succ = j.succAbove k := by
  apply (Fin.cycleRange j).injective
  simp [cyc0, Fin.cycleRange_succAbove]

theorem sign_cycle_perm (m : ℕ) (j : Fin (m + 1)) :
    Equiv.Perm.sign (cyc0 m j) = (-1) ^ (j : ℕ) := by
  rw [cyc0, Equiv.Perm.sign_symm, Fin.sign_cycleRange]

def ext0 {m : ℕ} (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  ((finSuccEquiv m).trans (Equiv.optionCongr τ)).trans (finSuccEquiv m).symm

theorem matrixExtendByZero_zero {m : ℕ} (τ : Equiv.Perm (Fin m)) : ext0 τ 0 = 0 := by
  simp [ext0]

theorem extByZero_succ {m : ℕ} (τ : Equiv.Perm (Fin m)) (k : Fin m) : ext0 τ k.succ = (τ k).succ := by
  simp [ext0]

theorem sign_extend_perm {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (ext0 τ) = Equiv.Perm.sign τ := by
  rw [ext0, Equiv.Perm.sign_trans_trans_symm, Equiv.optionCongr_sign]

def phi0 (m : ℕ) (p : Fin (m + 1) × Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  cyc0 m p.1 * ext0 p.2

theorem firstColumnSplit_bijective (m : ℕ) : Function.Bijective (phi0 m) := by
  have hinj : Function.Injective (phi0 m) := by
    rintro ⟨j, τ⟩ ⟨j', τ'⟩ h
    simp only [phi0] at h
    have hj : j = j' := by
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ 0) h
      simpa [Equiv.Perm.mul_apply, matrixExtendByZero_zero, cycle_perm_zero] using this
    subst hj
    have h2 : ext0 τ = ext0 τ' := mul_left_cancel h
    have hτ : τ = τ' := by
      ext k
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ k.succ) h2
      simp only [extByZero_succ, Fin.succ_inj] at this
      rw [this]
    rw [hτ]
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  simp [Fintype.card_perm, Nat.factorial_succ]

theorem qminorRow_succ {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (m + 1) → Fin n) (u : ℂ) :
    qminorRow E a b u = ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) *
      (List.ofFn fun k : Fin (m + 1) => Tm E (u - (m : ℂ) + ((k : ℕ) : ℂ)) (a k) (b (σ k))).prod := by
  have e : ∀ k : ℕ, u - ((m + 1 : ℕ) : ℂ) + 1 + (k : ℂ) = u - (m : ℂ) + (k : ℂ) := by
    intro k
    push_cast
    ring
  simp only [qminorRow, e]

theorem rowFirst {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (m + 1) → Fin n) (u : ℂ) :
    qminorRow E a b u = ∑ j : Fin (m + 1), (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) *
      (Tm E (u - (m : ℂ)) (a 0) (b j) * qminorRow E (a ∘ Fin.succ) (b ∘ j.succAbove) u) := by
  rw [qminorRow_succ, ← (firstColumnSplit_bijective m).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [qminorRow, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : ∀ k : ℕ, u - (m : ℂ) + ((k + 1 : ℕ) : ℂ) = u - (m : ℂ) + 1 + (k : ℂ) := by
    intro k
    push_cast
    ring
  simp only [phi0, Equiv.Perm.sign_mul, sign_cycle_perm, sign_extend_perm, Units.val_mul, Int.cast_mul,
    List.ofFn_succ, List.prod_cons, Equiv.Perm.mul_apply, matrixExtendByZero_zero, cycle_perm_zero, extByZero_succ, cycle_perm_succ,
    Fin.val_zero, Nat.cast_zero, add_zero, Fin.val_succ, e, Function.comp_apply]
  rw [mul_assoc]
  congr 1
  rw [← mul_assoc, ← mul_assoc, Int.cast_comm]

theorem rowLast {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (m + 1) → Fin n) (u : ℂ) :
    qminorRow E a b u = ∑ j : Fin (m + 1), (((-1 : ℤ) ^ (m + (j : ℕ)) : ℤ) : A) *
      (qminorRow E (a ∘ Fin.castSucc) (b ∘ j.succAbove) (u - 1) * Tm E u (a (Fin.last m)) (b j)) := by
  rw [qminorRow_succ, ← (lastColumnSplit_bijective m).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [qminorRow, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : ∀ k : ℕ, u - 1 - (m : ℂ) + 1 + (k : ℂ) = u - (m : ℂ) + (k : ℂ) := by
    intro k
    ring
  have hs : ((-1 : ℤ) ^ (m + (j : ℕ))) = (-1) ^ (m - (j : ℕ)) := by
    have hj : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.isLt
    have : m + (j : ℕ) = (m - (j : ℕ)) + 2 * (j : ℕ) := by omega
    rw [this, pow_add, pow_mul]
    simp
  simp only [lastColumnSplit, Equiv.Perm.sign_mul, sign_cycleToLast, sign_extendLast, Units.val_mul, Int.cast_mul,
    List.ofFn_succ', List.prod_concat, Equiv.Perm.mul_apply, extendLast_last, cycleToLast_last,
    extendLast_castSucc, cycleToLast_castSucc, Fin.val_last, Fin.val_castSucc, e, Function.comp_apply,
    sub_add_cancel, hs, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  rw [mul_assoc, mul_assoc]

theorem expFirstRow_of (h : PI.RowForm) : PI.ExpFirstRow := by
  intro A _ _ n t E hE a b u
  rw [h A n (t + 1) E hE a b u, rowFirst]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h A n t E hE]

theorem expLastRow_of (h : PI.RowForm) : PI.ExpLastRow := by
  intro A _ _ n t E hE a b u
  rw [h A n (t + 1) E hE a b u, rowLast]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h A n t E hE]

end PI.QmRowExpWork

namespace PI

theorem qmRowExp_of_rowForm (h : PI.QmRowForm) : PI.QmRowExp :=
  ⟨QmRowExpWork.expFirstRow_of h, QmRowExpWork.expLastRow_of h⟩

end PI
end
end

theorem quantum_minor_row_expansion : PI.QmRowExp := PI.qmRowExp_of_rowForm quantum_minor_row_form
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmColExp
private theorem bijective_cycleRange_symm_mul_decomposeFin_symm (t : ℕ) :
    Function.Bijective (fun p : Fin (t + 1) × Equiv.Perm (Fin t) =>
      (Fin.cycleRange p.1).symm * Equiv.Perm.decomposeFin.symm ((0 : Fin (t + 1)), p.2)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨l, τ⟩ ⟨l', τ'⟩ h
    simp only at h
    have h0 := congrArg (fun σ : Equiv.Perm (Fin (t + 1)) => σ 0) h
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_zero,
      Fin.cycleRange_symm_zero] at h0
    subst h0
    have h1 := mul_left_cancel h
    have h2 := Equiv.Perm.decomposeFin.symm.injective h1
    simp only [Prod.mk.injEq, true_and] at h2
    rw [h2]
  · simp [Fintype.card_perm, Nat.factorial_succ]

private theorem sum_perm_succ_eq_sum_cycleRange_decomposeFin {M : Type*} [AddCommMonoid M] (t : ℕ) (g : Equiv.Perm (Fin (t + 1)) → M) :
    ∑ σ, g σ = ∑ l : Fin (t + 1), ∑ τ : Equiv.Perm (Fin t),
      g ((Fin.cycleRange l).symm * Equiv.Perm.decomposeFin.symm ((0 : Fin (t + 1)), τ)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ (bijective_cycleRange_symm_mul_decomposeFin_symm t) _ _ (fun _ => rfl)).symm

private theorem sign_cycleRange_symm_mul_decomposeFin_symm (t : ℕ) (l : Fin (t + 1)) (τ : Equiv.Perm (Fin t)) :
    ((Equiv.Perm.sign ((Fin.cycleRange l).symm *
        Equiv.Perm.decomposeFin.symm ((0 : Fin (t + 1)), τ)) : ℤˣ) : ℤ)
      = (-1) ^ (l : ℕ) * (Equiv.Perm.sign τ : ℤ) := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
    Equiv.Perm.decomposeFin.symm_sign]
  simp

private theorem sign_cycleRange_symm_mul_decomposeFin_mul_finRotate (t : ℕ) (l : Fin (t + 1)) (τ : Equiv.Perm (Fin t)) :
    ((Equiv.Perm.sign ((Fin.cycleRange l).symm *
        Equiv.Perm.decomposeFin.symm ((0 : Fin (t + 1)), τ) * finRotate (t + 1)) : ℤˣ) : ℤ)
      = (-1) ^ (t + (l : ℕ)) * (Equiv.Perm.sign τ : ℤ) := by
  rw [Equiv.Perm.sign_mul, Units.val_mul, sign_cycleRange_symm_mul_decomposeFin_symm, sign_finRotate]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    add_tsub_cancel_right, add_tsub_cancel_left]
  ring

private theorem qminor_eq_sum_expand_first_column {A : Type} [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A)
    (a b : Fin (t + 1) → Fin n) (u : ℂ) :
    Formalism.REAL.qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (l : ℕ) : ℤ) : A) *
      (Formalism.REAL.Tm E u (a l) (b 0) *
        Formalism.REAL.qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (u - 1)) := by
  unfold Formalism.REAL.qminor
  rw [sum_perm_succ_eq_sum_cycleRange_decomposeFin]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [sign_cycleRange_symm_mul_decomposeFin_symm, List.ofFn_succ, List.prod_cons]
  have hs : ∀ k : Fin t, u - ((k : ℂ) + 1) = u - 1 - (k : ℂ) := fun k => by ring
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_zero,
    Fin.cycleRange_symm_zero, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self,
    Equiv.refl_apply, Fin.cycleRange_symm_succ, Function.comp_apply, Fin.val_zero,
    Nat.cast_zero, sub_zero, Fin.val_succ, Nat.cast_add, Nat.cast_one, hs]
  rw [Int.cast_mul, mul_assoc]
  congr 1
  rw [← mul_assoc, (Int.cast_commute ((Equiv.Perm.sign τ : ℤˣ) : ℤ)
    (Formalism.REAL.Tm E u (a l) (b 0))).eq, mul_assoc]

private theorem qminor_eq_sum_expand_last_column {A : Type} [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A)
    (a b : Fin (t + 1) → Fin n) (u : ℂ) :
    Formalism.REAL.qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (t + (l : ℕ)) : ℤ) : A) *
      (Formalism.REAL.qminor E (a ∘ l.succAbove) (b ∘ Fin.castSucc) u *
        Formalism.REAL.Tm E (u - (t : ℂ)) (a l) (b (Fin.last t))) := by
  unfold Formalism.REAL.qminor
  rw [← Equiv.sum_comp (Equiv.mulRight (finRotate (t + 1))), sum_perm_succ_eq_sum_cycleRange_decomposeFin]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Equiv.coe_mulRight]
  rw [sign_cycleRange_symm_mul_decomposeFin_mul_finRotate, List.ofFn_succ', List.prod_concat]
  simp only [Equiv.Perm.mul_apply, finRotate_apply, Fin.coeSucc_eq_succ, Fin.last_add_one,
    Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
    Fin.cycleRange_symm_succ, Function.comp_apply, Fin.coe_castSucc, Fin.val_last]
  rw [Int.cast_mul]
  simp only [mul_assoc]

theorem quantum_minor_column_expansion : PI.QmColExp := by
  delta PI.QmColExp PI.ExpFirstCol PI.ExpLastCol
  exact ⟨fun A _ _ n t E a b u => qminor_eq_sum_expand_first_column n t E a b u,
    fun A _ _ n t E a b u => qminor_eq_sum_expand_last_column n t E a b u⟩
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmStar
theorem quantum_minor_star : PI.QmStar :=
  PI.UnitaryGroupMassFormula.QmStar.qmStar_of quantum_minor_row_form
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocGlue
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.LocGlueOf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.MemOfProjEqZero
noncomputable section

open ValuativeRel
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.Glue

section Basic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm]

theorem h_sub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [sub_eq_add_neg, ← neg_one_smul E x', H.h_add_left, H.h_smul_left]
  ring

theorem h_sub_right (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [H.h_herm (y - y') x, h_sub_left, map_sub, ← H.h_herm, ← H.h_herm]

def hlin (u : V) : V →ₗ[E] E where
  toFun v := H.h v u
  map_add' a b := H.h_add_left a b u
  map_smul' a v := by rw [H.h_smul_left]; rfl

end Basic

section Proj

variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V]

theorem sub_proj_mem {A B : Submodule E V} (hAB : IsCompl A B) (x : V) :
    x - (A.projectionOnto B hAB x : V) ∈ B := by
  rw [← Submodule.projectionOnto_apply_eq_zero_iff hAB, map_sub,
    Submodule.projectionOnto_apply_left, sub_self]

theorem mem_of_proj_eq_zero {A B : Submodule E V} (hAB : IsCompl A B) {x : V}
    (h : (A.projectionOnto B hAB x : V) = 0) : x ∈ B := by
  exact (Submodule.projectionOnto_apply_eq_zero_iff hAB).1 (Subtype.ext h)

end Proj

set_option linter.deprecated false in
theorem pair_of (hR : Riesz) (hS : Scale) (hO : PI.LocHerm.LocOProj) : Pair := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H abelian₂ hL A B hAB orth u hu
  have e : Submodule.linearProjOfIsCompl A B hAB = A.projectionOnto B hAB := rfl
  rw [e]
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy hyA
    have hxB := sub_proj_mem hAB x
    have h1 : H.h x y = H.h (A.projectionOnto B hAB x : V) y := by
      have e2 := H.h_add_left (A.projectionOnto B hAB x : V) (x - (A.projectionOnto B hAB x : V)) y
      rw [add_sub_cancel, (orth y hyA _ hxB).2, add_zero] at e2
      exact e2
    rw [← h1]
    exact (hL.2.2 x).1 hx y hy
  · intro hyp

    let pB : V →ₗ[E] V := B.subtype ∘ₗ B.projectionOnto A hAB.symm
    have pB_apply : ∀ v, pB v = (B.projectionOnto A hAB.symm v : V) := fun v => rfl
    let P : Submodule M.L.O V := abelian₂.map (pB.restrictScalars M.L.O)
    let π : abelian₂ →ₗ[M.L.O] P := (pB.restrictScalars M.L.O).submoduleMap abelian₂
    have hπ : Function.Surjective π := LinearMap.submoduleMap_surjective _ _
    have hπv : ∀ l : abelian₂, (π l : V) = pB l := fun l => rfl
    have hPfg : P.FG := hL.1.map _
    have : Module.Projective M.L.O P := hO F E M hM V P hPfg
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
    have hsp : ∀ p : P, pB (s p : V) = p := by
      intro p
      have := congrArg Subtype.val (LinearMap.congr_fun hs p)
      rw [← hπv]
      exact this
    let Q : Submodule M.L.O V := LinearMap.range (abelian₂.subtype ∘ₗ s)
    let W : Submodule E V := Submodule.span E (Q : Set V)
    have hsW : ∀ p : P, (s p : V) ∈ W := fun p => Submodule.subset_span ⟨p, rfl⟩

    let d : abelian₂ → V := fun l => (l : V) - s (π l)
    have hdA : ∀ l : abelian₂, d l ∈ A := by
      intro l
      apply mem_of_proj_eq_zero hAB.symm
      rw [← pB_apply, map_sub, hsp, hπv, sub_self]
    have hdL : ∀ l : abelian₂, d l ∈ abelian₂ := fun l => abelian₂.sub_mem l.2 (s (π l)).2
    have hcompl : IsCompl A W := by
      refine isCompl_iff.2 ⟨?_, codisjoint_iff.2 ?_⟩
      · rw [Submodule.disjoint_def]
        intro w hwA hwW
        obtain ⟨r, hr0, hrw⟩ := hS M hM V Q w hwW
        obtain ⟨p, hp⟩ := hrw
        have hp' : (s p : V) = algebraMap F E r • w := hp
        have hpA : algebraMap F E r • w ∈ A := A.smul_mem _ hwA
        have h0 : (p : V) = 0 := by
          rw [← hsp p, hp', pB_apply]
          rw [Submodule.projectionOnto_apply_eq_zero_iff hAB.symm |>.2 hpA]
          rfl
        have hp0 : p = 0 := Subtype.ext h0
        have hrw0 : algebraMap F E r • w = 0 := by rw [← hp', hp0, map_zero]; rfl
        have : (algebraMap F E (r : F)⁻¹) • (algebraMap F E r • w) = w := by
          rw [smul_smul, ← map_mul, inv_mul_cancel₀ hr0, map_one, one_smul]
        rw [← this, hrw0, smul_zero]
      · rw [eq_top_iff, ← hL.2.1, Submodule.span_le]
        intro l hl
        have : l = d ⟨l, hl⟩ + (s (π ⟨l, hl⟩) : V) := by simp [d]
        rw [this]
        exact Submodule.add_mem_sup (hdA _) (hsW _)
    let pA' := A.projectionOnto W hcompl
    have hpA'd : ∀ l : abelian₂, (pA' l : V) = d l := by
      intro l
      have : (l : V) = d l + (s (π l) : V) := by simp [d]
      rw [this, map_add (f := _), Submodule.projectionOnto_apply_of_mem_right hcompl (hsW _), add_zero,
        Submodule.projectionOnto_apply_of_mem_left hcompl (hdA l)]
    let f : V →ₗ[E] E := hlin H u ∘ₗ A.subtype ∘ₗ pA'
    have hfA : ∀ y ∈ A, f y = H.h y u := by
      intro y hy
      show H.h (pA' y : V) u = H.h y u
      rw [Submodule.projectionOnto_apply_of_mem_left hcompl hy]
    have hfL : ∀ l : abelian₂, f l = H.h (d l) u := by
      intro l
      show H.h (pA' l : V) u = H.h (d l) u
      rw [hpA'd]
    obtain ⟨x, hx⟩ := hR M V H f
    have hxL : x ∈ abelian₂ := by
      refine (hL.2.2 x).2 (fun y hy => ?_)
      rw [H.h_herm y x, hx y, hfL ⟨y, hy⟩, H.h_herm u (d ⟨y, hy⟩)]
      exact PI.LocHerm.SlopeTestRemainingChoices.cj_mem_O M.L _
        (PI.LocHerm.SlopeTestRemainingChoices.cj_mem_O M.L _ (hyp _ (hdL _) (hdA _)))
    refine ⟨x, hxL, ?_⟩
    set z : V := (A.projectionOnto B hAB x : V) - u with hz
    have hzA : z ∈ A := A.sub_mem (A.projectionOnto B hAB x).2 hu
    have key : ∀ a ∈ A, H.h a z = 0 := by
      intro a ha
      have hxB := sub_proj_mem hAB x
      have e1 : H.h a x = H.h a (A.projectionOnto B hAB x : V) := by
        have e2 := h_add_right H a (A.projectionOnto B hAB x : V) (x - (A.projectionOnto B hAB x : V))
        rw [add_sub_cancel, (orth a ha _ hxB).1, add_zero] at e2
        exact e2
      rw [hz, h_sub_right, ← e1, hx a, hfA a ha, sub_self]
    have hz0 : z = 0 := by
      refine H.nondeg z (fun v => ?_)
      have hvB := sub_proj_mem hAB v
      have e3 := h_add_right H z (A.projectionOnto B hAB v : V) (v - (A.projectionOnto B hAB v : V))
      rw [add_sub_cancel, (orth z hzA _ hvB).1, add_zero] at e3
      rw [e3, H.h_herm _ z, key _ (A.projectionOnto B hAB v).2, map_zero]
    exact sub_eq_zero.1 hz0

end PI.LocHerm.Glue
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.RieszRepresentationHolds
noncomputable section

open ValuativeRel
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.Glue

theorem rieszRepresentation_holds : Riesz := by
  intro F _ _ _ E _ _ _ _ M V _ _ H f
  have : Module.Free F E := M.L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have : Module.Free E V := H.free
  have : Module.Finite E V := H.fin
  let b := Module.Free.chooseBasis E V
  let ℓ : V → V →ₗ[E] E := fun y =>
    { toFun := fun v => H.h v y
      map_add' := fun v w => H.h_add_left v w y
      map_smul' := fun c v => by
        simp only [RingHom.id_apply, smul_eq_mul]
        exact H.h_smul_left c v y }
  have hℓ : ∀ v y, ℓ y v = H.h v y := fun _ _ => rfl
  have key : ∀ (v : V) (a : Module.Free.ChooseBasisIndex E V → E),
      H.h v (∑ j, a j • b j) = ∑ j, M.L.cj (a j) * H.h v (b j) := by
    intro v a
    rw [H.h_herm (∑ j, a j • b j) v]
    have hs : H.h (∑ j, a j • b j) v = ∑ j, a j * H.h (b j) v := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hℓ, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, hℓ, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← H.h_herm]
  let A : Matrix (Module.Free.ChooseBasisIndex E V) (Module.Free.ChooseBasisIndex E V) E :=
    Matrix.of fun i j => H.h (b i) (b j)
  have hA : ∀ u i, H.h (b i) (∑ j, M.L.cj (u j) • b j) = A.mulVecLin u i := by
    intro u i
    rw [key, Matrix.mulVecLin_apply]
    simp only [M.L.cj_cj, Matrix.mulVec, dotProduct, A, Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hext : ∀ (x : V) (g : V →ₗ[E] E), (∀ i, H.h (b i) x = g (b i)) → ∀ v, H.h v x = g v := by
    intro x g hg v
    have : ℓ x = g := b.ext fun i => by rw [hℓ]; exact hg i
    rw [← hℓ, this]
  have hinj : Function.Injective A.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hx : ∀ v, H.h v (∑ j, M.L.cj (u j) • b j) = (0 : V →ₗ[E] E) v := by
      refine hext _ 0 fun i => ?_
      rw [hA, hu]
      rfl
    have hx0 : (∑ j, M.L.cj (u j) • b j) = 0 := by
      refine H.nondeg _ fun y => ?_
      rw [H.h_herm y, hx y, LinearMap.zero_apply, map_zero]
    have hc : (fun j => M.L.cj (u j)) = 0 := by
      apply b.equivFun.symm.injective
      rw [Module.Basis.equivFun_symm_apply, hx0, map_zero]
    funext j
    have := congrFun hc j
    simp only [Pi.zero_apply] at this
    have h2 := congrArg M.L.cj this
    rw [M.L.cj_cj, map_zero] at h2
    exact h2
  obtain ⟨u, hu⟩ := IsArtinian.surjective_of_injective_endomorphism A.mulVecLin hinj
    (fun i => f (b i))
  refine ⟨∑ j, M.L.cj (u j) • b j, hext _ f fun i => ?_⟩
  rw [hA, hu]

end PI.LocHerm.Glue
end
end

namespace PI.LocHerm.Glue

theorem locGlue_of (hO : PI.LocHerm.LocOProj) : PI.LocHerm.LocGlue :=
  locGlue_of_pair (pair_of rieszRepresentation_holds existsIntegralMultiple hO)

end PI.LocHerm.Glue
end

theorem local_hermitian_glue : PI.LocHerm.LocGlue :=
  PI.LocHerm.Glue.locGlue_of projectiveOverOrder
end
