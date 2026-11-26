module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantAntiHomomorphism
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantAntiHomomorphism
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgTransport

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL

theorem anti_list_prod {A B : Type} [Ring A] [Ring B] (f : A → B) (h1 : f 1 = 1)
    (hm : ∀ x y, f (x * y) = f y * f x) (l : List A) :
    f l.prod = (l.map f).reverse.prod := by
  induction l with
  | nil => simpa using h1
  | cons a l ih => simp [List.prod_cons, hm, ih]

theorem anti_Tm {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₗ[ℂ] B) (h1 : f 1 = 1)
    {m : ℕ} (E : Fin m → Fin m → A) (v : ℂ) (a b : Fin m) :
    f (Tm E v a b) = Tm (fun a b => f (E b a)) v b a := by
  have hal : f (algebraMap ℂ A v) = algebraMap ℂ B v := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, h1]
  unfold Tm
  by_cases h : a = b
  · subst h; simp [hal]
  · simp [h, Ne.symm h]

theorem qdet_eq_qminorRow_rev {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (hE : GlRel E)
    (u : ℂ) : qdet E u = PI.qminorRow E (id ∘ Fin.revPerm) (id ∘ Fin.revPerm) u := by
  have hrow : PI.RowForm := quantum_minor_row_form
  rw [← hrow A m m E hE, quantumMinorRowSkew_holds A m m E id _ Fin.revPerm u,
    quantumMinorColSkew_holds A m m E hE id id Fin.revPerm u, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
  rfl

theorem qdet_anti {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₗ[ℂ] B) (h1 : f 1 = 1)
    (hm : ∀ x y, f (x * y) = f y * f x) {m : ℕ} (E : Fin m → Fin m → A) (hE : GlRel E) (u : ℂ) :
    qdet (fun a b => f (E b a)) u = f (qdet E u) := by
  rw [qdet_eq_qminorRow_rev E hE]
  unfold qdet qminor PI.qminorRow
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (Fintype.sum_equiv (PI.UnitaryGroupMassFormula.QmRowForm.revConj m) _ _ (fun σ => ?_)).symm
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, PI.UnitaryGroupMassFormula.QmRowForm.sign_revConj,
    anti_list_prod f h1 hm, List.map_ofFn, PI.UnitaryGroupMassFormula.QmRowForm.reverse_ofFn']
  congr 2
  refine List.ofFn_inj.mpr (funext fun k => ?_)
  simp only [Function.comp_apply, anti_Tm f h1, id]
  show Tm _ _ _ _ = Tm _ _ (Fin.revPerm (σ (Fin.revPerm k))) _
  simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  congr 1
  rw [Nat.cast_sub (by omega : (k : ℕ) + 1 ≤ m)]
  push_cast
  ring

end GlobalTheory.CompanionTheory.RgTransport
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantAntiHomomorphismStatement
open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_determinant_anti_homomorphism : ∀ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₗ[ℂ] B), f 1 = 1 → (∀ x y, f (x * y) = f y * f x) → ∀ {m : ℕ} (E : Fin m → Fin m → A), GlRel E → ∀ u : ℂ, qdet (fun a b => f (E b a)) u = f (qdet E u) := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.qdet_anti | exact GlobalTheory.CompanionTheory.RgTransport.qdet_anti | (intros; apply GlobalTheory.CompanionTheory.RgTransport.qdet_anti <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommutingLocallyNilpotentCommonKernel
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommutingLocallyNilpotentCommonKernel
open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport

namespace GlobalTheory.CompanionTheory.RgTransport

theorem exists_joint_kernel_finset {V : Type} [AddCommGroup V] [Module ℂ V]
    (I : Submodule ℂ V) (hI : I ≠ ⊥) (D : ℂ → Module.End ℂ V)
    (hcomm : ∀ Y Y', Commute (D Y) (D Y'))
    (hstab : ∀ Y, ∀ x ∈ I, D Y x ∈ I)
    (hnil : ∀ Y, ∀ x ∈ I, ∃ N : ℕ, (D Y ^ N) x = 0) (F : Finset ℂ) :
    ∃ w ∈ I, w ≠ 0 ∧ ∀ Y ∈ F, D Y w = 0 := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff I).1 hI
    exact ⟨x, hx, hx0, by simp⟩
  | insert a F _ ih =>
    obtain ⟨x, hx, hx0, hF⟩ := ih
    have hex : ∃ N : ℕ, (D a ^ N) x = 0 := hnil a x hx
    have hN := Nat.find_spec hex
    have hmin := fun m => Nat.find_min hex (m := m)
    set N := Nat.find hex with hNdef
    have hpos : N ≠ 0 := by
      intro h0
      rw [h0] at hN
      exact hx0 (by simpa using hN)
    obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    have hiter : ∀ k : ℕ, (D a ^ k) x ∈ I := by
      intro k
      induction k with
      | zero => simpa using hx
      | succ k ihk =>
        rw [pow_succ', Module.End.mul_apply]
        exact hstab a _ ihk
    refine ⟨(D a ^ M) x, hiter M, hmin M (by omega), ?_⟩
    intro Y hY
    rcases Finset.mem_insert.1 hY with rfl | hY
    · rw [← Module.End.mul_apply, ← pow_succ']
      rw [hM] at hN
      exact hN
    · have hc : Commute (D Y) (D a ^ M) := (hcomm Y a).pow_right M
      rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hF Y hY, map_zero]

theorem exists_joint_kernel_polynomial_family :
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (I : Submodule ℂ V), I ≠ ⊥ →
      ∀ (D : ℂ → Module.End ℂ V), (∀ Y Y', Commute (D Y) (D Y')) →
      (∀ Y, ∀ x ∈ I, D Y x ∈ I) → (∀ Y, ∀ x ∈ I, ∃ N : ℕ, (D Y ^ N) x = 0) →
      ∀ (l : ℕ) (c : ℕ → Module.End ℂ V), (∀ Y, D Y = ∑ j ∈ Finset.range l, Y ^ j • c j) →
      ∃ w ∈ I, w ≠ 0 ∧ ∀ Y, D Y w = 0 := by
  intro V _ _ I hI D hcomm hstab hnil l c hD
  classical
  let F : Finset ℂ := (Finset.range l).image (fun n : ℕ => (n : ℂ))
  have hcard : F.card = l := by
    simpa using Finset.card_image_of_injective (Finset.range l)
      (Nat.cast_injective (R := ℂ))
  obtain ⟨w, hw, hw0, hF⟩ := exists_joint_kernel_finset I hI D hcomm hstab hnil F
  refine ⟨w, hw, hw0, fun Y => ?_⟩
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (D Y w)).1 fun φ => ?_
  let p : Polynomial ℂ :=
    ∑ j ∈ Finset.range l, Polynomial.C (φ (c j w)) * Polynomial.X ^ j
  have heval : ∀ Z : ℂ, p.eval Z = φ (D Z w) := by
    intro Z
    rw [hD Z]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, LinearMap.sum_apply, LinearMap.smul_apply,
      map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hdeg : p.degree < (F.card : ℕ) := by
    rw [hcard]
    refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe l)).2 fun j hj => ?_
    refine (Polynomial.degree_C_mul_X_pow_le j _).trans_lt ?_
    exact WithBot.coe_lt_coe.2 (Finset.mem_range.1 hj)
  have hp : p = 0 :=
    Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero F hdeg
      (fun Z hZ => by rw [heval, hF Z hZ, map_zero])
  rw [← heval, hp, Polynomial.eval_zero]

end GlobalTheory.CompanionTheory.RgTransport
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommutingLocallyNilpotentCommonKernelStatement
open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_locally_nilpotent_common_kernel : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (I : Submodule ℂ V), I ≠ ⊥ → ∀ (D : ℂ → Module.End ℂ V), (∀ Y Y', Commute (D Y) (D Y')) → (∀ Y, ∀ x ∈ I, D Y x ∈ I) → (∀ Y, ∀ x ∈ I, ∃ N : ℕ, (D Y ^ N) x = 0) → ∀ (l : ℕ) (c : ℕ → Module.End ℂ V), (∀ Y, D Y = ∑ j ∈ Finset.range l, Y ^ j • c j) → ∃ w ∈ I, w ≠ 0 ∧ ∀ Y, D Y w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.exists_joint_kernel_polynomial_family | exact GlobalTheory.CompanionTheory.RgTransport.exists_joint_kernel_polynomial_family | (intros; apply GlobalTheory.CompanionTheory.RgTransport.exists_joint_kernel_polynomial_family <;> assumption)
end
end
