module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Lemmata.GeneralBFactUpperAltForm.Imports
public import Lemmata.GeneralBFactThirdExtra.Imports

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.AutLzFinite
noncomputable section

open scoped Classical

namespace PI.AutLzFinite

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def AutLzFin : Prop :=
  (VS D).SigOK → ∀ (Tn : ℕ), 0 < Tn → ∀ (F0 : FlagG (VS D) D.R.rS ((Tn : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → (autLz D F0 Λ).Finite

end PI.AutLzFinite
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.AutLzFinMain
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.IndSetFinite
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.FiniteOfIntegralBound
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.MjSmulRight
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.MulVecMapInjective
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.SylvesterLe
namespace PI.AutLzFinite.SlopeTestRemainingChoices

open Matrix

theorem cT_conj_eq {m p : Type} (M : Matrix m p ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT]

theorem form_Jpq (p q : ℕ) (y : Fin p ⊕ Fin q → ℂ) :
    star y ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ y) =
      (∑ i, star (y (Sum.inl i)) * y (Sum.inl i)) - ∑ j, star (y (Sum.inr j)) * y (Sum.inr j) := by
  unfold Formalism.UG.Jpq
  simp [dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec,
    Function.comp_def, sub_eq_add_neg] <;> ring

theorem sylvester_le {n k : Type} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (J : Matrix n n ℂ) {p q : ℕ} (hJ : Formalism.UG.HasSignature J p q) (B : Matrix n k ℂ)
    (hB : Function.Injective B.mulVec)
    (hneg : ∀ v : k → ℂ, (star (B *ᵥ v) ⬝ᵥ (J *ᵥ (B *ᵥ v))).re ≤ 0) : Fintype.card k ≤ q := by
  classical
  obtain ⟨e, P, hP⟩ := hJ
  rw [cT_conj_eq] at hP
  by_contra hcon
  push_neg at hcon
  let T : (k → ℂ) →ₗ[ℂ] (Fin q → ℂ) := (LinearMap.funLeft ℂ ℂ Sum.inr) ∘ₗ
    (Matrix.mulVecLin ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) ∘ₗ
    (LinearMap.funLeft ℂ ℂ e.symm) ∘ₗ (Matrix.mulVecLin B)
  have hker : LinearMap.ker T ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card]
    exact hcon
  obtain ⟨v, hvK, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hTv : T v = 0 := LinearMap.mem_ker.1 hvK
  have hyr : ∀ j, (((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ
      ((B *ᵥ v) ∘ e.symm)) (Sum.inr j) = 0 := fun j => congrFun hTv j
  set w : n → ℂ := B *ᵥ v with hwdef
  set y : Fin p ⊕ Fin q → ℂ :=
    ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ (w ∘ e.symm) with hydef
  have hw : w ∘ e.symm = (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ y := by
    rw [hydef, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hwne : w ≠ 0 := by
    intro h
    apply hv0
    apply hB
    show B *ᵥ v = B *ᵥ 0
    rw [Matrix.mulVec_zero]
    exact h
  have hyne : y ≠ 0 := by
    intro h
    apply hwne
    funext i
    have h3 := congrFun hw (e i)
    rw [h, Matrix.mulVec_zero] at h3
    simpa using h3
  obtain ⟨i, hi⟩ : ∃ i, y (Sum.inl i) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hyne
    funext s
    cases s with
    | inl i => exact hall i
    | inr j => exact hyr j
  have h1 : star w ⬝ᵥ (J *ᵥ w) = star (w ∘ e.symm) ⬝ᵥ (J.reindex e e *ᵥ (w ∘ e.symm)) := by
    simp only [dotProduct, mulVec, Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply,
      Pi.star_apply]
    refine Fintype.sum_equiv e _ _ (fun a => ?_)
    simp only [Equiv.symm_apply_apply]
    congr 1
    exact Fintype.sum_equiv e _ _ (fun b => by simp only [Equiv.symm_apply_apply])
  have hform : star w ⬝ᵥ (J *ᵥ w) = star y ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ y) := by
    rw [h1, hw, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hP]
  have hre : ∀ z : ℂ, (star z * z).re = Complex.normSq z := fun z => by
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  have hpos : 0 < (star w ⬝ᵥ (J *ᵥ w)).re := by
    rw [hform, form_Jpq]
    simp only [hyr, mul_zero, Finset.sum_const_zero, sub_zero, Complex.re_sum, hre]
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩
  have := hneg v
  linarith

end PI.AutLzFinite.SlopeTestRemainingChoices
end

noncomputable section

namespace PI.AutLzFinite.SlopeTestRemainingChoices

open Matrix Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem hT_expand (x y : S.V) :
    S.hT x y = ∑ i, ∑ j, star (S.frame.repr x i) * S.gram i j * S.frame.repr y j := by
  have hx : ∀ w, S.hT x w = ∑ i, star (S.frame.repr x i) * S.hT (S.frame i) w := by
    intro w
    conv_lhs => rw [← S.frame.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    simp [LinearMap.map_smulₛₗ, starRingEnd_apply]
  have hy : ∀ w, S.hT w y = ∑ j, S.hT w (S.frame j) * S.frame.repr y j := by
    intro w
    conv_lhs => rw [← S.frame.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp [mul_comm]
  rw [hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hy, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [HSpace.gram, mul_assoc]

theorem herm_swap (x y : S.V) : S.hT y x = star (S.hT x y) := by
  rw [← S.herm.eq x y]; rfl

def coordC {k : Type} (τ : E →+* ℂ) (u : k → S.V) : Matrix (Fin S.rank) k ℂ :=
  Matrix.of fun i a => τ (S.frame.repr (u a) i)

theorem gram_entry (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    {k : Type} (τ : E →+* ℂ) (u : k → S.V) (a b : k) :
    ((coordC S τ u)ᴴ * S.gram.map τ * coordC S τ u) a b = τ (S.hT (u a) (u b)) := by
  rw [hT_expand, Matrix.mul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, coordC, Matrix.of_apply, Matrix.map_apply,
    map_sum, map_mul, hstar, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem form_eq {n k : Type} [Fintype n] [Fintype k] (B : Matrix n k ℂ) (J : Matrix n n ℂ) (v : k → ℂ) :
    star (B *ᵥ v) ⬝ᵥ (J *ᵥ (B *ᵥ v)) = star v ⬝ᵥ ((Bᴴ * J * B) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem mulVec_map_injective {K : Type} [Field K] {n k : Type} [Fintype n] [DecidableEq n] [Fintype k]
    [DecidableEq k] (f : K →+* ℂ) (A : Matrix n k K) (hA : Function.Injective A.mulVec) :
    Function.Injective (A.map f).mulVec := by
  first | exact Bl.general_b_fact_upper_alt_form.goal1 .. | (apply Bl.general_b_fact_upper_alt_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_alt_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_alt_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_upper_alt_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_alt_form.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› ‹_› ‹_› f A hA | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› ‹_› ‹_› f A | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› ‹_› ‹_› f | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› | exact @Bl.general_b_fact_upper_alt_form.goal1 K

theorem coord_injective {k : Type} [Fintype k] (u : k → S.V) (hu : LinearIndependent E u) :
    Function.Injective (Matrix.of fun i a => S.frame.repr (u a) i).mulVec := by
  intro c d hcd
  have key : ∀ c : k → E, (Matrix.of fun i a => S.frame.repr (u a) i) *ᵥ c = S.frame.repr (∑ a, c a • u a) := by
    intro c; ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, mul_comm]
  rw [key, key] at hcd
  have h2 := S.frame.repr.injective (Finsupp.ext fun i => congrFun hcd i)
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h2
  simp_rw [← sub_smul] at h2
  have h3 := (Fintype.linearIndependent_iff.mp hu) (fun a => c a - d a) h2
  funext a; exact sub_eq_zero.mp (h3 a)

theorem pos_perp (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    (τ : E →+* ℂ) {p q : ℕ} (hsig : Formalism.UG.HasSignature (S.gram.map τ) p q) {r : ℕ} (hq : q ≤ r + 1)
    (e : Fin r → S.V) (he : LinearIndependent E e) (hee : ∀ a b, S.hT (e a) (e b) = 0)
    (z : S.V) (hez : ∀ a, S.hT (e a) z = 0) (hzz : (τ (S.hT z z)).re < 0)
    (y : S.V) (hey : ∀ a, S.hT (e a) y = 0) (hzy : S.hT z y = 0)
    (hyX : y ∉ Submodule.span E (Set.range e)) : 0 < (τ (S.hT y y)).re := by
  by_contra hle'
  have hle := not_lt.mp hle'
  have hzz0 : S.hT z z ≠ 0 := by
    intro h; rw [h, map_zero] at hzz; simp at hzz
  have hze : ∀ a, S.hT z (e a) = 0 := fun a => by rw [herm_swap, hez, star_zero]
  have hye : ∀ a, S.hT y (e a) = 0 := fun a => by rw [herm_swap, hey, star_zero]
  have hyz : S.hT y z = 0 := by rw [herm_swap, hzy, star_zero]

  have hXz : ∀ x ∈ Submodule.span E (Set.range e), S.hT z x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hze a
    | zero => simp
    | add x y _ _ h1 h2 => simp [map_add (f := _), h1, h2]
    | smul c x _ h => simp [h]
  let u : Fin r ⊕ Fin 2 → S.V := Sum.elim e ![z, y]
  have hpair : LinearIndependent E ![z, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (S.hT z) hst
    simp [map_add (f := _), hzy] at h1
    have hs : s = 0 := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 hzz0
    subst hs
    refine ⟨rfl, ?_⟩
    simp at hst
    rcases hst with h | h
    · exact h
    · exact absurd (h ▸ Submodule.zero_mem _) hyX
  have hdisj : Disjoint (Submodule.span E (Set.range e)) (Submodule.span E (Set.range ![z, y])) := by
    rw [Submodule.disjoint_def]
    intro w hw1 hw2
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union, Submodule.mem_span_pair] at hw2
    obtain ⟨s, t, rfl⟩ := hw2
    have h1 := hXz _ hw1
    simp [map_add (f := _), hzy] at h1
    have hs : s = 0 := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 hzz0
    subst hs
    simp only [zero_smul, zero_add] at hw1 ⊢
    by_cases ht : t = 0
    · simp [ht]
    · exfalso; apply hyX
      have := Submodule.smul_mem _ t⁻¹ hw1
      rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this
  have hind : LinearIndependent E u := he.sum_type hpair hdisj
  have hB : Function.Injective (coordC S τ u).mulVec :=
    mulVec_map_injective τ _ (coord_injective S u hind)
  have hneg : ∀ v : Fin r ⊕ Fin 2 → ℂ,
      (star (coordC S τ u *ᵥ v) ⬝ᵥ (S.gram.map τ *ᵥ (coordC S τ u *ᵥ v))).re ≤ 0 := by
    intro v
    rw [form_eq]
    have hM : ∀ a b, ((coordC S τ u)ᴴ * S.gram.map τ * coordC S τ u) a b = τ (S.hT (u a) (u b)) :=
      gram_entry S hstar τ u
    simp only [dotProduct, Matrix.mulVec, hM, Fintype.sum_sum_type, Fin.sum_univ_two, u,
      Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      hee, hez, hey, hze, hye, hzy, hyz, map_zero, zero_mul, mul_zero, Finset.sum_const_zero, zero_add,
      add_zero]
    have hn : ∀ w : ℂ, ∀ c : ℂ, (star w * (c * w)).re = Complex.normSq w * c.re := by
      intro w c
      rw [Complex.star_def, mul_comm c w, ← mul_assoc, mul_comm (starRingEnd ℂ w) w, Complex.mul_conj]
      rw [Complex.re_ofReal_mul]
    rw [Pi.star_apply, Pi.star_apply, Complex.add_re, hn, hn]
    have := Complex.normSq_nonneg (v (Sum.inr 0))
    have := Complex.normSq_nonneg (v (Sum.inr 1))
    nlinarith
  have hc := sylvester_le _ hsig _ hB hneg
  simp at hc
  omega

end PI.AutLzFinite.SlopeTestRemainingChoices
end
end

noncomputable section

namespace PI.AutLzFinite.SlopeTestRemainingChoices

open Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

def mj (z x y : S.V) : E := S.hT x y - 2 / S.hT z z * (S.hT x z * S.hT z y)

variable {S}

theorem mj_add_left (z x x' y : S.V) : mj S z (x + x') y = mj S z x y + mj S z x' y := by
  simp only [mj, map_add (f := _), LinearMap.add_apply]
  ring

theorem mj_smul_left (z : S.V) (c : E) (x y : S.V) : mj S z (c • x) y = star c * mj S z x y := by
  simp only [mj, LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]
  ring

theorem mj_add_right (z x y y' : S.V) : mj S z x (y + y') = mj S z x y + mj S z x y' := by
  simp only [mj, map_add (f := _)]
  ring

theorem mj_smul_right (z : S.V) (c : E) (x y : S.V) : mj S z x (c • y) = c * mj S z x y := by
  simp only [mj, map_smul, smul_eq_mul]
  ring

theorem mj_swap (z x y : S.V) : mj S z y x = star (mj S z x y) := by
  have hs : ∀ a b : S.V, star (S.hT a b) = S.hT b a := fun a b => by
    have h := S.herm.eq a b
    rwa [starRingEnd_apply] at h
  simp only [mj, star_sub, star_mul', star_div₀, hs, star_ofNat]
  ring

theorem mj_self_star (z x : S.V) : star (mj S z x x) = mj S z x x := (mj_swap z x x).symm

theorem tau_real {τ : E →+* ℂ} (hstar : ∀ a : E, τ (star a) = starRingEnd ℂ (τ a)) {a : E}
    (ha : star a = a) : τ a = ((τ a).re : ℂ) := by
  have h := hstar a
  rw [ha] at h
  exact (Complex.conj_eq_iff_re.1 h.symm).symm

theorem tau_normSq {τ : E →+* ℂ} (hstar : ∀ a : E, τ (star a) = starRingEnd ℂ (τ a)) (c : E) :
    τ (star c * c) = (Complex.normSq (τ c) : ℂ) := by
  rw [map_mul, hstar, Complex.normSq_eq_conj_mul_self]

section Pos

variable (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) (τ : E →+* ℂ)
  (X P : Submodule E S.V) (hPX : ∀ x ∈ X, ∀ y ∈ P, S.hT x y = 0) (z : S.V) (hzP : z ∈ P)
  (hzz : (τ (S.hT z z)).re < 0)
  (hpos : ∀ y ∈ P, S.hT z y = 0 → y ∉ X → 0 < (τ (S.hT y y)).re)
include hstar hPX hzP hzz hpos

theorem mj_pos (y : S.V) (hy : y ∈ P) :
    0 ≤ (τ (mj S z y y)).re ∧ ((τ (mj S z y y)).re = 0 → y ∈ X) := by
  have hzz0 : S.hT z z ≠ 0 := by
    intro h; rw [h, map_zero] at hzz; simp at hzz
  set c := S.hT z y / S.hT z z with hc
  set y0 := y - c • z with hy0def
  have h1 : S.hT z y0 = 0 := by
    simp only [y0, map_sub, LinearMap.map_smul, smul_eq_mul, c]
    field_simp; ring
  have hy0 : y0 ∈ P := P.sub_mem hy (P.smul_mem c hzP)
  have h2 : S.hT y0 z = 0 := by rw [herm_swap, h1, star_zero]
  have hm : mj S z y y = S.hT y0 y0 - star c * c * S.hT z z := by
    have hyy : y = y0 + c • z := by simp [y0]
    rw [hyy]
    simp only [mj, map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, h1, h2, starRingEnd_apply, RingHom.id_apply]
    field_simp
    ring
  have hq : 0 ≤ (τ (S.hT y0 y0)).re ∧ ((τ (S.hT y0 y0)).re = 0 → y0 ∈ X) := by
    by_cases hX : y0 ∈ X
    · have : S.hT y0 y0 = 0 := hPX y0 hX y0 hy0
      simp [this, hX]
    · have := hpos y0 hy0 h1 hX
      exact ⟨this.le, fun h => absurd h this.ne'⟩
  have hτ : (τ (mj S z y y)).re = (τ (S.hT y0 y0)).re - Complex.normSq (τ c) * (τ (S.hT z z)).re := by
    rw [hm, map_sub, map_mul, tau_normSq (hstar τ), Complex.sub_re, Complex.re_ofReal_mul]
  have hns := Complex.normSq_nonneg (τ c)
  refine ⟨by rw [hτ]; nlinarith, fun h0 => ?_⟩
  rw [hτ] at h0
  have hA : Complex.normSq (τ c) * (τ (S.hT z z)).re = 0 := by nlinarith
  have hB : (τ (S.hT y0 y0)).re = 0 := by nlinarith
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp hA with h | h
    · exact τ.injective (by rw [Complex.normSq_eq_zero.mp h, map_zero])
    · exact absurd h hzz.ne
  have : y = y0 := by simp [y0, hc0]
  rw [this]; exact hq.2 hB

theorem mj_cs (x y : S.V) (hx : x ∈ P) (hy : y ∈ P) :
    Complex.normSq (τ (mj S z x y)) ≤ (τ (mj S z x x)).re * (τ (mj S z y y)).re := by
  have hnn : ∀ s : E, 0 ≤ (τ (mj S z (s • x + y) (s • x + y))).re := fun s =>
    (mj_pos hstar τ X P hPX z hzP hzz hpos _ (P.add_mem (P.smul_mem s hx) hy)).1
  have hexp : ∀ s : E, mj S z (s • x + y) (s • x + y) =
      star s * s * mj S z x x + star s * mj S z x y + s * star (mj S z x y) + mj S z y y := by
    intro s
    rw [mj_add_left, mj_add_right, mj_add_right, mj_smul_left, mj_smul_left, mj_smul_right,
      mj_smul_right, mj_swap z x y]
    ring
  have hareal := tau_real (hstar τ) (mj_self_star z x)
  have ha0 := (mj_pos hstar τ X P hPX z hzP hzz hpos x hx).1
  rcases ha0.lt_or_eq with hapos | hazero
  · have hane : mj S z x x ≠ 0 := by
      intro h; rw [h, map_zero] at hapos; simp at hapos
    have h := hnn (-(mj S z x y) / mj S z x x)
    rw [hexp] at h
    have hval : star (-(mj S z x y) / mj S z x x) * (-(mj S z x y) / mj S z x x) * mj S z x x +
        star (-(mj S z x y) / mj S z x x) * mj S z x y +
        (-(mj S z x y) / mj S z x x) * star (mj S z x y) + mj S z y y =
        mj S z y y - (star (mj S z x y) * mj S z x y) / mj S z x x := by
      rw [star_div₀, star_neg, mj_self_star]
      field_simp
      ring
    rw [hval, map_sub, map_div₀, tau_normSq (hstar τ), hareal, Complex.sub_re] at h
    rw [← Complex.ofReal_div, Complex.ofReal_re] at h
    rw [sub_nonneg, div_le_iff₀ hapos] at h
    linarith
  · have hτa : τ (mj S z x x) = 0 := by rw [hareal, ← hazero]; simp
    have ha : mj S z x x = 0 := τ.injective (by rw [hτa, map_zero])
    rw [← hazero, zero_mul]
    by_contra hlt
    have hpos' : 0 < Complex.normSq (τ (mj S z x y)) := lt_of_not_ge hlt
    obtain ⟨N, hN⟩ := exists_nat_gt ((τ (mj S z y y)).re / (2 * Complex.normSq (τ (mj S z x y))))
    have h := hnn (-(N : E) * mj S z x y)
    rw [hexp, ha] at h
    have hval : star (-(N : E) * mj S z x y) * (-(N : E) * mj S z x y) * 0 +
        star (-(N : E) * mj S z x y) * mj S z x y +
        (-(N : E) * mj S z x y) * star (mj S z x y) + mj S z y y =
        mj S z y y - (2 * (N : E)) * (star (mj S z x y) * mj S z x y) := by
      rw [star_mul, star_neg, star_natCast]
      ring
    rw [hval, map_sub, map_mul, tau_normSq (hstar τ), Complex.sub_re] at h
    have h2 : (τ (2 * (N : E))) = ((2 * (N : ℝ) : ℝ) : ℂ) := by
      rw [map_mul, map_natCast, map_ofNat]; push_cast; ring
    rw [h2, ← Complex.ofReal_mul, Complex.ofReal_re] at h
    rw [div_lt_iff₀ (by positivity)] at hN
    nlinarith

end Pos

end PI.AutLzFinite.SlopeTestRemainingChoices
end
end

noncomputable section

namespace PI.AutLzFinite.SlopeTestRemainingChoices

open Formalism.BasicNotions NumberField

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem exists_smul_mem (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.span E (Λ : Set S.V) = ⊤) (v : S.V) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  first | exact Bl.general_b_fact_third_extra.goal1 .. | (apply Bl.general_b_fact_third_extra.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_extra.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_extra.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_third_extra.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_extra.goal1 <;> first | assumption | infer_instance)

theorem finite_of_integral_bound (t : E) (ht : t ≠ 0) (C : ℝ) :
    {a : E | IsIntegral ℤ (t * a) ∧ ∀ τ : E →+* ℂ, ‖τ a‖ ≤ C}.Finite := by
  set K : ℝ := ∑ τ : E →+* ℂ, ‖τ t‖
  apply Set.Finite.of_finite_image (f := fun a => t * a)
  · apply (Embeddings.finite_of_norm_le E ℂ (K * C)).subset
    rintro _ ⟨a, ⟨ha1, ha2⟩, rfl⟩
    refine ⟨ha1, fun τ => ?_⟩
    rw [map_mul, norm_mul]
    have h1 : ‖τ t‖ ≤ K := Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ t‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ τ)
    have h2 := ha2 τ
    have h3 : 0 ≤ ‖τ a‖ := norm_nonneg _
    nlinarith [norm_nonneg (τ t)]
  · intro a _ b _ hab
    exact mul_left_cancel₀ ht hab

end PI.AutLzFinite.SlopeTestRemainingChoices
end
end

noncomputable section

namespace PI.AutLzFinite.SlopeTestRemainingChoices

open Formalism.BasicNotions NumberField

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

def indSet (X P : Submodule E S.V) (z : S.V) (Λ : Submodule (𝓞 E) S.V) :
    Set ((P ⧸ X.comap P.subtype) → (P ⧸ X.comap P.subtype)) :=
  {φ | ∃ γ : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (γ x) (γ y) = S.hT x y) ∧ γ z = z ∧ (∀ x ∈ Λ, γ x ∈ Λ) ∧
    (∀ x ∈ P, γ x ∈ P) ∧
    ∀ (x : P) (hx : γ x.1 ∈ P), φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨γ x.1, hx⟩}

theorem indSet_finite (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    (X P : Submodule E S.V) (hPX : ∀ x ∈ X, ∀ y ∈ P, S.hT x y = 0) (z : S.V) (hzP : z ∈ P)
    (hzz : ∀ τ : E →+* ℂ, (τ (S.hT z z)).re < 0)
    (hpos : ∀ τ : E →+* ℂ, ∀ y ∈ P, S.hT z y = 0 → y ∉ X → 0 < (τ (S.hT y y)).re)
    (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.span E (Λ : Set S.V) = ⊤)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (S.hT x y)) (hzΛ : z ∈ Λ) :
    (indSet X P z Λ).Finite := by
  classical
  set Xc := X.comap P.subtype
  have hzz0 : S.hT z z ≠ 0 := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    intro h; have := hzz τ; rw [h, map_zero] at this; simp at this

  set bB := Module.finBasis E P
  have hd : ∀ i, ∃ d : 𝓞 E, d ≠ 0 ∧ d • (bB i : S.V) ∈ Λ := fun i => exists_smul_mem Λ hΛ _
  choose d hd0 hdΛ using hd
  have hd0' : ∀ i, algebraMap (𝓞 E) E (d i) ≠ 0 := fun i => by
    rw [ne_eq, ← map_zero (algebraMap (𝓞 E) E), (IsFractionRing.injective (𝓞 E) E).eq_iff]
    exact hd0 i
  set b := bB.unitsSMul (fun i => Units.mk0 _ (hd0' i))
  have hbΛ : ∀ i, ((b i : P) : S.V) ∈ Λ := by
    intro i
    simp only [b, Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0,
      algebraMap_smul]
    exact hdΛ i

  set cf : Fin (Module.finrank E P) → ℝ := fun i =>
    ∑ τ : E →+* ℂ, |(τ (mj S z (b i : S.V) (b i : S.V))).re| with hcf
  set C : ℝ := ∑ i, cf i with hCdef
  have hC : ∀ i (τ : E →+* ℂ), (τ (mj S z (b i : S.V) (b i : S.V))).re ≤ C := by
    intro i τ
    have h1 : |(τ (mj S z (b i : S.V) (b i : S.V))).re| ≤ cf i :=
      Finset.single_le_sum (f := fun (τ : E →+* ℂ) => |(τ (mj S z (b i : S.V) (b i : S.V))).re|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
    have h2 : cf i ≤ C := Finset.single_le_sum (f := cf)
      (fun j _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    exact (le_abs_self _).trans (h1.trans h2)
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

  set Y : Set (P ⧸ Xc) := {q | ∃ y : P, (y : S.V) ∈ Λ ∧
    (∀ τ : E →+* ℂ, (τ (mj S z y y)).re ≤ C) ∧ q = Submodule.Quotient.mk y}

  let mjR : Fin (Module.finrank E P) → S.V →ₗ[E] E := fun j =>
    S.hT (b j : S.V) - (2 / S.hT z z * S.hT (b j : S.V) z) • S.hT z
  have hmjR : ∀ j y, mjR j y = mj S z (b j : S.V) y := by
    intro j y; simp only [mjR, mj, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]; ring
  let Pm : P →ₗ[E] (Fin (Module.finrank E P) → E) := LinearMap.pi fun j => (mjR j).comp P.subtype
  have hPm : ∀ (y : P) j, Pm y j = mj S z (b j : S.V) y := by
    intro y j; simp [Pm, hmjR]
  have hker : Xc ≤ LinearMap.ker Pm := by
    intro y hy
    rw [LinearMap.mem_ker]
    funext j
    rw [hPm]
    have h1 : S.hT (b j : S.V) y = 0 := by
      rw [herm_swap, hPX (y : S.V) hy _ (b j).2, star_zero]
    have h2 : S.hT z y = 0 := by rw [herm_swap, hPX (y : S.V) hy _ hzP, star_zero]
    simp [mj, h1, h2]
  let g : (P ⧸ Xc) →ₗ[E] (Fin (Module.finrank E P) → E) := Xc.liftQ Pm hker
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker, Submodule.liftQ_apply] at hq
    have hw : ∀ j, mj S z (b j : S.V) w = 0 := fun j => by rw [← hPm, hq]; rfl
    have hall : ∀ v : P, mj S z v w = 0 := by
      intro v
      have hv : v ∈ Submodule.span E (Set.range b) := by rw [b.span_eq]; trivial
      induction hv using Submodule.span_induction with
      | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hw j
      | zero => simpa using mj_smul_left (S := S) z 0 (0 : S.V) w
      | add x y _ _ h1 h2 => rw [Submodule.coe_add, mj_add_left, h1, h2, add_zero]
      | smul c x _ h => rw [Submodule.coe_smul, mj_smul_left, h, mul_zero]
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hw0 := (mj_pos hstar τ X P hPX z hzP (hzz τ) (hpos τ) w w.2).2 (by rw [hall w]; simp)
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hw0
  have hYfin : Y.Finite := by
    apply Set.Finite.of_finite_image (f := g) _ hg.injOn
    apply (Set.Finite.pi (t := fun _ => {a : E | IsIntegral ℤ (S.hT z z * a) ∧
      ∀ τ : E →+* ℂ, ‖τ a‖ ≤ C}) fun _ => finite_of_integral_bound _ hzz0 C).subset
    rintro _ ⟨q, ⟨y, hyΛ, hyC, rfl⟩, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro j
    have hgj : g (Submodule.Quotient.mk y) j = mj S z (b j : S.V) y := by
      simp only [g, Submodule.liftQ_apply]; exact hPm y j
    rw [hgj]
    constructor
    · have e1 : S.hT z z * mj S z (b j : S.V) y =
          S.hT z z * S.hT (b j : S.V) y - (S.hT (b j : S.V) z * S.hT z y + S.hT (b j : S.V) z * S.hT z y) := by
        simp only [mj]; field_simp; ring
      rw [e1]
      refine IsIntegral.sub (IsIntegral.mul (hint _ hzΛ _ hzΛ) (hint _ (hbΛ j) _ hyΛ))
        (IsIntegral.add (IsIntegral.mul (hint _ (hbΛ j) _ hzΛ) (hint _ hzΛ _ hyΛ))
          (IsIntegral.mul (hint _ (hbΛ j) _ hzΛ) (hint _ hzΛ _ hyΛ)))
    · intro τ
      have hcs := mj_cs hstar τ X P hPX z hzP (hzz τ) (hpos τ) _ _ (b j).2 y.2
      have ha := (mj_pos hstar τ X P hPX z hzP (hzz τ) (hpos τ) _ (b j).2).1
      have hb := (mj_pos hstar τ X P hPX z hzP (hzz τ) (hpos τ) _ y.2).1
      have h1 := hC j τ
      have h2 := hyC τ
      have hsq : ‖τ (mj S z (b j : S.V) y)‖ ^ 2 ≤ C ^ 2 := by
        rw [Complex.sq_norm]; nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hC0 two_ne_zero).mp hsq

  apply Set.Finite.of_finite_image (f := fun φ i => φ (Submodule.Quotient.mk (b i)))
  · apply (Set.Finite.pi (t := fun _ => Y) fun _ => hYfin).subset
    rintro _ ⟨φ, ⟨γ, hiso, hγz, hγΛ, hγP, hφ⟩, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    refine ⟨⟨γ (b i : S.V), hγP _ (b i).2⟩, hγΛ _ (hbΛ i), fun τ => ?_, hφ _ _⟩
    have e1 : ∀ x : S.V, S.hT (γ x) z = S.hT x z := fun x => by
      conv_lhs => rw [← hγz]
      exact hiso x z
    have e2 : ∀ x : S.V, S.hT z (γ x) = S.hT z x := fun x => by
      conv_lhs => rw [← hγz]
      exact hiso z x
    have : mj S z (γ (b i : S.V)) (γ (b i : S.V)) = mj S z (b i : S.V) (b i : S.V) := by
      simp only [mj, hiso, e1, e2]
    simp only [this]
    exact hC i τ
  · rintro φ ⟨γ, hiso, hγz, hγΛ, hγP, hφ⟩ φ' ⟨γ', hiso', hγz', hγΛ', hγP', hφ'⟩ heq
    let ψ : P →ₗ[E] (P ⧸ Xc) := Xc.mkQ ∘ₗ (γ : S.V →ₗ[E] S.V).restrict hγP
    let ψ' : P →ₗ[E] (P ⧸ Xc) := Xc.mkQ ∘ₗ (γ' : S.V →ₗ[E] S.V).restrict hγP'
    have hψ : ∀ x : P, φ (Submodule.Quotient.mk x) = ψ x := fun x => by
      rw [hφ x (hγP _ x.2)]; rfl
    have hψ' : ∀ x : P, φ' (Submodule.Quotient.mk x) = ψ' x := fun x => by
      rw [hφ' x (hγP' _ x.2)]; rfl
    have hψψ : ψ = ψ' := b.ext fun i => by
      rw [← hψ, ← hψ']; exact congrFun heq i
    funext q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hψ, hψ', hψψ]

end PI.AutLzFinite.SlopeTestRemainingChoices
end
end

noncomputable section

namespace PI.AutLzFinite.SlopeTestRemainingChoices

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem autLzFin_main (D : D7) : PI.AutLzFinite.AutLzFin D := by
  intro hsig Tn hTn F0 Λ hΛ
  obtain ⟨-, hfix, -⟩ := hΛ
  obtain ⟨hlat, hunimod, hlift, -⟩ := hfix
  have hstar : ∀ (τ : D.host.E →+* ℂ) (a : D.host.E), τ (star a) = starRingEnd ℂ (τ a) := by
    haveI := D.host.isCMField_hostE
    intro τ a
    exact NumberField.IsCMField.complexEmbedding_complexConj _ τ a
  have hPX : ∀ x ∈ F0.X, ∀ y ∈ perpS (VS D) F0.X, (VS D).hT x y = 0 := fun x hx y hy => hy x hx
  have hzX : ∀ x ∈ F0.X, (VS D).hT x F0.z = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, rfl⟩
      exact F0.z_orth a
    · simp
    · intro u v _ _ hu hv
      simp [hu, hv]
    · intro c u _ hu
      simp [hu]
  have hzP : F0.z ∈ perpS (VS D) F0.X := fun x hx => hzX x hx
  have hzz : ∀ τ : D.host.E →+* ℂ, (τ ((VS D).hT F0.z F0.z)).re < 0 := by
    intro τ
    rw [F0.z_norm, map_neg, map_natCast, Complex.neg_re, Complex.natCast_re]
    exact neg_neg_of_pos (by exact_mod_cast hTn)
  have hpos : ∀ τ : D.host.E →+* ℂ, ∀ y ∈ perpS (VS D) F0.X, (VS D).hT F0.z y = 0 → y ∉ F0.X →
      0 < (τ ((VS D).hT y y)).re := by
    intro τ y hy hzy hyX
    have hq : ((VS D).sig τ).2 ≤ D.R.rS + 1 := by
      have e : (VS D).sig τ = D.R.sigY0 := D.sp.baseSpace_signature_eq τ
      rw [e]
      simp [Formalism.BasicNotions.Ranks.sigY0]
    exact pos_perp (S := VS D) hstar τ (hsig τ) hq F0.e F0.e_indep F0.e_iso F0.z F0.z_orth (hzz τ) y
      (fun a => hy _ (Submodule.subset_span ⟨a, rfl⟩)) hzy hyX
  have hspan : Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ := by
    have hriesz (φ : (VS D).V →ₗ[D.host.E] D.host.E) : ∃ μ : (VS D).V, ∀ v, (VS D).hT μ v = φ v := by
      classical
      let b := (VS D).frame
      haveI := Module.Finite.of_basis b
      let T := LinearMap.pi fun i => (VS D).hT (b i)
      have hinj : Function.Injective T := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro x hx
        have h0 : ∀ i, (VS D).hT (b i) x = 0 := fun i => congrFun hx i
        have hflip : (VS D).hT.flip x = 0 := b.ext fun i => by simp [h0 i]
        exact (VS D).nondeg.2 x fun y => by simpa using LinearMap.congr_fun hflip y
      have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by simp [Module.finrank_eq_card_basis b])).mp hinj
      choose bs hbs' using fun j => hsurj (Pi.single j 1)
      have hbs : ∀ i j, (VS D).hT (b i) (bs j) = if i = j then 1 else 0 := by
        intro i j
        have h := congrFun (hbs' j) i
        simpa [T, Pi.single_apply] using h
      refine ⟨∑ j, star (φ ((VS D).frame j)) • bs j, fun v => ?_⟩
      have key : (VS D).hT (∑ j, star (φ ((VS D).frame j)) • bs j) = φ := by
        apply (VS D).frame.ext
        intro i
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, LinearMap.sum_apply]
        have hs : ∀ j, (VS D).hT (star (φ ((VS D).frame j)) • bs j) ((VS D).frame i) =
            φ ((VS D).frame j) * (if i = j then 1 else 0) := by
          intro j
          rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
          congr 1
          rw [← (VS D).herm.eq ((VS D).frame i) (bs j), hbs]
          split_ifs <;> simp
        simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [key]
    by_contra hspan
    obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
    obtain ⟨μ, hμ⟩ := hriesz φ
    have hμ₀ : μ ≠ 0 := by
      intro h
      apply hφ₀
      ext y
      simpa [h] using (hμ y).symm
    have hline (a : D.host.E) : a • μ ∈ Λ := by
      rw [← hunimod]
      change a • μ ∈ Formalism.E.hdual (VS D).hT Λ
      simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      intro y hy
      have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
      simp [← (VS D).herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
    obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
      (show μ ∉ (⊥ : Submodule D.host.E (VS D).V) by simpa using hμ₀)
    let f := ψ.restrictScalars (𝓞 D.host.E)
    have hmap (x : D.host.E) : x ∈ Λ.map f := by
      refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
      change ψ ((x / ψ μ) • μ) = x
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
    obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
      (S := nonZeroDivisors (𝓞 D.host.E)) (hlat.fg.map f)
    have hinj := IsFractionRing.injective (𝓞 D.host.E) D.host.E
    have hne {a : 𝓞 D.host.E} (ha : a ≠ 0) : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 :=
      fun h => ha (hinj (h.trans (map_zero _).symm))
    have hinteger (x : D.host.E) : IsLocalization.IsInteger (𝓞 D.host.E) x := by
      have hx := hd _ (hmap ((algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ * x))
      rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
        one_mul] at hx
    apply RingOfIntegers.not_isField D.host.E
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
    intro a ha
    obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 D.host.E) D.host.E a)⁻¹)
    refine ⟨b, hinj ?_⟩
    rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((VS D).hT x y) := by
    intro x hx y hy
    have hd : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hunimod
    have h1 : y ∈ Formalism.E.hdual (VS D).hT Λ := by
      have h2 : y ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by rw [hd]; exact hy
      exact h2
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (h1 x hx)
    have ho' : (VS D).hT x y = algebraMap (𝓞 D.host.E) D.host.E o := ho.symm
    rw [ho']
    exact o.isIntegral_coe
  have hzΛ : F0.z ∈ Λ := hlift.1
  have hfin := indSet_finite (S := VS D) hstar F0.X (perpS (VS D) F0.X) hPX F0.z hzP hzz hpos Λ hspan hint hzΛ
  refine hfin.subset ?_
  rintro φ ⟨γ, hγ, hgΛ, hφ⟩
  obtain ⟨hiso, hXa, hz⟩ := hγ
  have hiso' : ∀ x y, (VS D).hT (γ x) (γ y) = (VS D).hT x y := hiso
  have hXr : F0.Xa D.R.rS = F0.X := by
    simp [FlagG.Xa, FlagG.X, Fin.is_lt, Set.setOf_true, Set.image_univ]
  refine ⟨γ, hiso', hz, ?_, ?_, hφ⟩
  · intro x hx
    have h3 : γ x ∈ Formalism.HermitianLatticesTheory.gmap γ Λ := ⟨x, hx, rfl⟩
    rwa [hgΛ] at h3
  · intro x hxP y hyX
    have hX : F0.X.map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
      rw [← hXr]
      exact hXa D.R.rS
    rw [← hX] at hyX
    obtain ⟨y', hy', rfl⟩ := hyX
    show (VS D).hT (γ y') (γ x) = 0
    rw [hiso']
    exact hxP y' hy'

end PI.AutLzFinite.SlopeTestRemainingChoices
end
end

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem automorphism_lattice_finite (D : Formalism.BasicNotions.D7) : PI.AutLzFinite.AutLzFin D :=
  PI.AutLzFinite.SlopeTestRemainingChoices.autLzFin_main D
