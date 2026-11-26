module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGl
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace TensorGLSums

theorem glSum {R : Type*} [Ring R] {n : ℕ} {ι : Type*} [DecidableEq ι] (S : Finset ι) (L : Fin n → Fin n → R)
    (e : ι → Fin n → Fin n → R) (hL : GlRel L) (hLe : ∀ p a b c d, Commute (L a b) (e p c d))
    (he : ∀ p q a b c d, e p a b * e q c d - e q c d * e p a b =
      if p = q then (if b = c then e p a d else 0) - (if d = a then e p c b else 0) else 0) :
    GlRel (fun a b => L a b + ∑ p ∈ S, e p a b) := by
  intro a b c d
  have key : ∀ x y u v : R, (x + u) * (y + v) - (y + v) * (x + u) =
      (x * y - y * x) + (x * v - v * x) + (u * y - y * u) + (u * v - v * u) := by
    intros; noncomm_ring
  simp only
  rw [key, hL]
  have h1 : L a b * ∑ p ∈ S, e p c d - (∑ p ∈ S, e p c d) * L a b = 0 := by
    rw [sub_eq_zero]; exact (Commute.sum_right _ _ _ fun p _ => hLe p a b c d).eq
  have h2 : (∑ p ∈ S, e p a b) * L c d - L c d * ∑ p ∈ S, e p a b = 0 := by
    rw [sub_eq_zero]; exact (Commute.sum_left _ _ _ fun p _ => (hLe p c d a b).symm).eq
  have h3 : (∑ p ∈ S, e p a b) * (∑ q ∈ S, e q c d) - (∑ q ∈ S, e q c d) * (∑ p ∈ S, e p a b) =
      ∑ p ∈ S, ((if b = c then e p a d else 0) - (if d = a then e p c b else 0)) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := S) (t := S)
      (f := fun q p => e q c d * e p a b), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.sum_sub_distrib]
    simp_rw [he p]
    rw [Finset.sum_ite_eq]
    simp [hp]
  rw [h1, h2, h3]
  split_ifs <;> simp [Finset.sum_sub_distrib] <;> abel

theorem omComm {R : Type*} [Ring R] {n : ℕ} (L e : Fin n → Fin n → R) (hL : GlRel L)
    (hLe : ∀ a b c d, Commute (L a b) (e c d)) (he : ∀ a b c d, e a b * e c d = if b = c then e a d else 0)
    (c d : Fin n) : Commute (∑ a, ∑ b, L a b * e b a) (L c d + e c d) := by
  rw [Commute, SemiconjBy, ← sub_eq_zero]
  have hterm : ∀ a b, L a b * e b a * (L c d + e c d) - (L c d + e c d) * (L a b * e b a) =
      ((if b = c then L a d * e b a else 0) - (if d = a then L c b * e b a else 0)) +
      ((if a = c then L a b * e b d else 0) - (if d = b then L a b * e c a else 0)) := by
    intro a b
    have h1 : e b a * L c d = L c d * e b a := ((hLe c d b a).eq).symm
    have h2 : e c d * L a b = L a b * e c d := ((hLe a b c d).eq).symm
    have h3 := hL a b c d
    have e1 := he b a c d
    have e2 := he c d b a
    calc L a b * e b a * (L c d + e c d) - (L c d + e c d) * (L a b * e b a)
        = (L a b * L c d - L c d * L a b) * e b a + L a b * (e b a * e c d - e c d * e b a) := by
          have k1 : L a b * e b a * L c d = L a b * L c d * e b a := by rw [mul_assoc, h1, ← mul_assoc]
          have k2 : e c d * (L a b * e b a) = L a b * e c d * e b a := by rw [← mul_assoc, h2]
          rw [mul_add, add_mul, k1, k2]
          noncomm_ring
      _ = _ := by
          rw [h3, e1, e2]
          split_ifs <;> simp [sub_mul, mul_sub]
  have hx : (∑ a, ∑ b, L a b * e b a) * (L c d + e c d) - (L c d + e c d) * (∑ a, ∑ b, L a b * e b a) =
      ∑ a, ∑ b, (L a b * e b a * (L c d + e c d) - (L c d + e c d) * (L a b * e b a)) := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hx]
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun a b => if d = a then L c b * e b a else 0)]
  rw [Finset.sum_comm (f := fun a b => if a = c then L a b * e b d else 0)]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  abel

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [DecidableEq P]

theorem eAt_mul (p : P) (a b c d : Fin n) :
    (eAt p a b * eAt p c d : Module.End ℂ (TV n M P)) = if b = c then eAt p a d else 0 := by
  refine LinearMap.ext fun f => funext fun I => ?_
  by_cases hbc : b = c
  · subst hbc
    simp [Module.End.mul_apply, eAt_apply, Function.update_idem]
  · simp [Module.End.mul_apply, eAt_apply, hbc]

theorem eAt_comm {p q : P} (h : p ≠ q) (a b c d : Fin n) :
    (eAt p a b * eAt q c d : Module.End ℂ (TV n M P)) = eAt q c d * eAt p a b := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, eAt_apply, Function.update_of_ne h, Function.update_of_ne (Ne.symm h),
    Function.update_comm h]
  split_ifs <;> rfl

theorem pm_eAt (σ : Equiv.Perm P) (p : P) (a b : Fin n) :
    (pm σ * eAt p a b : Module.End ℂ (TV n M P)) = eAt (σ p) a b * pm σ := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, eAt_apply, pm_apply, Function.comp_apply]
  rw [Function.update_comp_equiv]
  simp

omit [DecidableEq P] in
theorem glLift (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) :
    GlRel (fun a b => (lift (E a b) : Module.End ℂ (TV n M P))) := by
  intro a b c d
  have := congrArg (liftA n M P) (hE a b c d)
  simp only [map_sub, map_mul, apply_ite (liftA n M P), map_zero] at this
  exact this

end TensorGLSums

open TensorGLSums in
theorem tensorGl_holds : TensorGl := by
  intro n M _ _ P _ _ E hE S
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact glSum S _ _ (glLift E hE) (fun p a b c d => lift_comm_eAt _ _ _ _) fun p q a b c d => by
      by_cases hpq : p = q
      · subst hpq; rw [if_pos rfl, eAt_mul, eAt_mul]
      · rw [if_neg hpq, eAt_comm hpq, sub_self]
  · intro p hp a b
    have hsplit : tE S E a b = (lift (E a b) + eAt p a b) + ∑ q ∈ S.erase p, eAt q a b := by
      rw [tE, add_assoc]; congr 1; exact (Finset.add_sum_erase S (fun q => eAt q a b) hp).symm
    rw [hsplit]
    refine Commute.add_right ?_ (Commute.sum_right _ _ _ fun q hq => ?_)
    · exact omComm (fun a b => lift (E a b)) (fun a b => eAt p a b) (glLift E hE)
        (fun a b c d => lift_comm_eAt _ _ _ _) (fun a b c d => eAt_mul p a b c d) a b
    · have hqp : q ≠ p := Finset.ne_of_mem_erase hq
      refine Commute.sum_left _ _ _ fun a' _ => Commute.sum_left _ _ _ fun b' _ => ?_
      exact Commute.mul_left (lift_comm_eAt _ _ _ _) (eAt_comm (Ne.symm hqp) _ _ _ _)
  · intro σ hσ a b
    rw [tE, Commute, SemiconjBy, mul_add, add_mul, (lift_comm_pm _ σ).eq, Finset.mul_sum, Finset.sum_mul]
    congr 1
    simp_rw [pm_eAt]
    exact Finset.sum_equiv σ (fun p => (hσ p).symm) fun p _ => rfl
  · intro σ p
    simp only [Om, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, ← (lift_comm_pm _ σ).eq, mul_assoc, pm_eAt, mul_assoc]

end PositivityTheory.Rg.Cz

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PLieInv
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace LieInverse

theorem exists_ne_of_ne_one {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) (i : Fin n) :
    ∃ j, j ≠ i ∧ σ j ≠ j := by
  by_contra h
  push Not at h
  apply hσ
  have hi : σ i = i := by
    by_contra hne
    have := h (σ i) hne
    exact hne (σ.injective this)
  ext j
  by_cases hj : j = i
  · subst hj; simp [hi]
  · simp [h j hj]

theorem hasDerivAt_det {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (h0 : A 0 = 1) (hA : ∀ i j, HasDerivAt (fun t => A t i j) (Y i j) 0) :
    HasDerivAt (fun t => (A t).det) Y.trace 0 := by
  have key : ∀ σ : Equiv.Perm (Fin n), HasDerivAt (fun t => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i)
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∑ i, (∏ j ∈ Finset.univ.erase i, A 0 (σ j) j) * Y (σ i) i) 0 := by
    intro σ
    have := (HasDerivAt.finsetProd (u := Finset.univ) (fun i _ => hA (σ i) i)).const_mul
      ((Equiv.Perm.sign σ : ℤ) : ℂ)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp [Finset.prod_apply]
  have hs := HasDerivAt.sum (u := Finset.univ) (fun σ _ => key σ)
  refine (hs.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simp [Matrix.det_apply', Finset.sum_apply]
  · simp only [Finset.mul_sum, smul_eq_mul]
    rw [Finset.sum_comm, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · simp [h0]
    · intro σ _ hσ
      obtain ⟨j, hji, hj⟩ := exists_ne_of_ne_one σ hσ i
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) (by rw [h0]; exact Matrix.one_apply_ne hj)]
      simp
    · simp

def Sop {ι : Type} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (E : ι → Fin n → Fin n → Module.End ℂ M)
    (bar : ι → ι) (τ : ι) (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ M :=
  ∑ a, ∑ b, (X a b • E τ a b + star (X a b) • E (bar τ) a b)

theorem Sop_add {ι : Type} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (E : ι → Fin n → Fin n → Module.End ℂ M)
    (bar : ι → ι) (τ : ι) (X Y : Matrix (Fin n) (Fin n) ℂ) : Sop E bar τ (X + Y) = Sop E bar τ X + Sop E bar τ Y := by
  simp only [Sop, Matrix.add_apply, add_smul, star_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by abel

theorem Sop_single {ι : Type} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (E : ι → Fin n → Fin n → Module.End ℂ M) (bar : ι → ι) (τ : ι) (p q : Fin n) (z : ℂ) :
    Sop E bar τ (Matrix.single p q z) = z • E τ p q + star z • E (bar τ) p q := by
  unfold Sop
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
  · simp [Matrix.single_apply]
  · intro b _ hb; simp [Matrix.single_apply, hb, Ne.symm hb]
  · simp
  · intro a _ ha
    exact Finset.sum_eq_zero fun b _ => by simp [Matrix.single_apply, ha, Ne.symm ha]
  · simp

end LieInverse

open LieInverse in
theorem lieInv_holds : LieInv := by
  intro n M _ _ ι _ _ Γ _ _ bar κ E ρ hK hG c ξ hξ τ a b
  have hbt : bar τ ≠ τ := hK.ne τ
  have hD : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X →
      Sop E bar τ X ξ = ((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) • ξ := by
    intro X hX
    obtain ⟨cv, hc0, hcd, hcoth, hρ⟩ := hG.der τ X hX
    let D : ι → ℂ := fun τ' => if τ' = τ then X.trace else if τ' = bar τ then star X.trace else 0
    have hdet : ∀ τ', HasDerivAt (fun t => (κ τ' (cv t)).det) (D τ') 0 := by
      intro τ'
      by_cases h1 : τ' = τ
      · subst h1
        simp only [D, if_true]
        exact hasDerivAt_det _ X (by rw [hc0, hK.one]) hcd
      · by_cases h2 : τ' = bar τ
        · subst h2
          simp only [D, if_neg h1, if_true]
          have ht : (X.map star).trace = star X.trace := by simp [Matrix.trace, star_sum]
          rw [← ht]
          refine hasDerivAt_det _ _ (by rw [hc0, hK.one]) fun i j => ?_
          simp only [hK.conj, Matrix.map_apply]
          exact (hcd i j).star
        · simp only [D, if_neg h1, if_neg h2]
          have hf : (fun t => (κ τ' (cv t)).det) = fun _ => 1 := by
            funext t; rw [hcoth τ' h1 h2 t, Matrix.det_one]
          rw [hf]; exact hasDerivAt_const _ _
    have h1 : ∀ τ', (κ τ' (cv 0)).det = 1 := fun τ' => by rw [hc0, hK.one, Matrix.det_one]
    have hz : ∀ τ', HasDerivAt (fun t => (κ τ' (cv t)).det ^ c τ') ((c τ' : ℂ) * D τ') 0 := by
      intro τ'
      have := (hasDerivAt_zpow (c τ') ((κ τ' (cv 0)).det) (Or.inl (by rw [h1]; exact one_ne_zero))).comp
        (0 : ℝ) (hdet τ')
      rw [h1, _root_.one_zpow, mul_one] at this
      exact this
    have hχ : HasDerivAt (fun t => ∏ τ', (κ τ' (cv t)).det ^ c τ')
        ((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) 0 := by
      have := HasDerivAt.finsetProd (u := Finset.univ) (fun τ' _ => hz τ')
      refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
        simp [Finset.prod_apply])).congr_deriv ?_
      simp only [h1, _root_.one_zpow, Finset.prod_const_one, one_smul]
      rw [Finset.sum_eq_add_of_mem τ (bar τ) (Finset.mem_univ _) (Finset.mem_univ _) hbt.symm]
      · simp [D, hbt]
      · intro x _ hx; simp [D, hx.1, hx.2]
    rw [← sub_eq_zero]
    apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
    intro lam
    have h2 : HasDerivAt (fun t => lam (ρ (cv t) ξ))
        (((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) * lam ξ) 0 := by
      refine (hχ.mul_const (lam ξ)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [hξ, map_smul, smul_eq_mul]
    have hu : lam (Sop E bar τ X ξ) = _ := (hρ ξ lam).unique h2
    rw [map_sub, hu, map_smul, smul_eq_mul, sub_self]
  have hsI : star Complex.I = -Complex.I := Complex.conj_I
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    have hX : (Matrix.single a a Complex.I)ᴴ = -Matrix.single a a Complex.I := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.single_apply]
      split_ifs with h1 h2 h2
      · simp [hsI]
      · exact (h2 ⟨h1.2, h1.1⟩).elim
      · exact (h1 ⟨h2.2, h2.1⟩).elim
      · simp
    have e := hD _ hX
    rw [Sop_single, Matrix.trace_single_eq_same, hsI] at e
    have e' : Complex.I • (E τ a a ξ - E (bar τ) a a ξ - ((c τ - c (bar τ) : ℤ) : ℂ) • ξ) = 0 := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply] at e
      push_cast
      linear_combination (norm := module) e
    rcases smul_eq_zero.mp e' with h | h
    · exact absurd h Complex.I_ne_zero
    · exact sub_eq_zero.mp h
  · rw [if_neg hab]
    have hX1 : (Matrix.single a b (1 : ℂ) + Matrix.single b a (-1))ᴴ =
        -(Matrix.single a b (1 : ℂ) + Matrix.single b a (-1)) := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.single_apply]
      split_ifs <;> simp_all
    have hX2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
        -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.single_apply]
      split_ifs <;> simp_all
    have e1 := hD _ hX1
    have e2 := hD _ hX2
    rw [Sop_add, Sop_single, Sop_single, Matrix.trace_add, Matrix.trace_single_eq_of_ne _ _ _ hab,
      Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hab)] at e1 e2
    simp only [LinearMap.add_apply, LinearMap.smul_apply, add_zero, star_zero, mul_zero, zero_smul, hsI,
      star_one, star_neg] at e1 e2
    have e2' : Complex.I • (E τ a b ξ + E τ b a ξ - E (bar τ) a b ξ - E (bar τ) b a ξ) = 0 := by
      linear_combination (norm := module) e2
    have e3 : E τ a b ξ + E τ b a ξ - E (bar τ) a b ξ - E (bar τ) b a ξ = 0 :=
      (smul_eq_zero.mp e2').resolve_left Complex.I_ne_zero
    linear_combination (norm := module) (1 / 2 : ℂ) • e1 + (1 / 2 : ℂ) • e3

end PositivityTheory.Rg.Cz

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSemiZero
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace SemiInvariantDeterminant

theorem det_bar {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] {n : ℕ} {bar : ι → ι}
    {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} (hK : IsKD bar κ) (τ : ι) (γ : Γ) :
    (κ (bar τ) γ).det = star (κ τ γ).det := by
  have e : κ (bar τ) γ = (starRingEnd ℂ).mapMatrix (κ τ γ) := by
    ext i j; exact hK.conj τ γ i j
  rw [e, ← RingHom.map_det]
  rfl

theorem det_mul_star {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] {n : ℕ} {bar : ι → ι}
    {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} (hK : IsKD bar κ) (τ : ι) (γ : Γ) :
    (κ τ γ).det * star (κ τ γ).det = 1 := by
  have := congrArg Matrix.det (hK.unit τ γ)
  rwa [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this

end SemiInvariantDeterminant

open SemiInvariantDeterminant in
theorem semiZero_of (hQ : QdetFacts) (_hW : WallAlg) (hL : LieInv) (hWQ : WallQuot) : SemiZero := by
  intro n hn M _ _ ι _ _ Γ _ _ bar κ E ρ hK hG s φ hφ hS
  obtain ⟨lab, c, ξ, -, hact, I, w, hw, hwξ⟩ := hS
  have hρ : ∀ γ, ρ γ (ξ I) = (∏ τ, (κ τ γ).det ^ c τ) • ξ I := by
    intro γ
    have h := congrFun (hact γ) I
    rw [actT_apply, Pi.smul_apply] at h
    rw [← h, Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
    rw [Subsingleton.elim (default : Fin 0 → Fin n) I]
  obtain ⟨N, F, hFgl, -, hFch, hFE, hN⟩ := hWQ n M ι E hG.gl hG.comm (fun _ _ => s) φ (by
    intro τ u
    rw [hφ τ u, Finset.prod_const, Finset.card_univ, Fintype.card_fin])
  have hξN : N.mkQ (ξ I) ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hN]
    push Not
    exact ⟨w, hw, hwξ⟩
  have htr : ∀ τ', N.mkQ ((∑ a, E τ' a a) (ξ I)) = (∑ a, F τ' a a) (N.mkQ (ξ I)) := by
    intro τ'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun a _ => LinearMap.congr_fun (hFE τ' a a) (ξ I)
  have hc : ∀ τ, c τ = c (bar τ) := by
    intro τ
    have hl := hL n M ι Γ bar κ E ρ hK hG c (ξ I) hρ τ
    have h1 : N.mkQ ((∑ a, E τ a a) (ξ I)) = N.mkQ ((∑ a, E (bar τ) a a) (ξ I)) := by
      rw [htr, htr, (hQ n (M ⧸ N) (F τ) (hFgl τ)).2.2.1 _ (hFch τ),
        (hQ n (M ⧸ N) (F (bar τ)) (hFgl (bar τ))).2.2.1 _ (hFch (bar τ))]
    have h2 : (∑ a, E τ a a) (ξ I) - (∑ a, E (bar τ) a a) (ξ I) =
        ((n : ℂ) * ((c τ - c (bar τ) : ℤ) : ℂ)) • ξ I := by
      rw [LinearMap.sum_apply, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
      simp only [hl, if_true]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have h3 : ((n : ℂ) * ((c τ - c (bar τ) : ℤ) : ℂ)) • N.mkQ (ξ I) = 0 := by
      rw [← map_smul, ← h2, map_sub, h1, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd (Nat.cast_eq_zero.mp h) (by omega)
      · exact sub_eq_zero.mp (Int.cast_eq_zero.mp h)
    · exact absurd h hξN
  have hχ : ∀ γ, (∏ τ, (κ τ γ).det ^ c τ) = 1 := by
    intro γ
    refine Finset.prod_involution (fun τ _ => bar τ) ?_ ?_ (fun _ _ => Finset.mem_univ _)
      (fun τ _ => hK.invol τ)
    · intro τ _
      rw [det_bar hK, ← hc τ, ← mul_zpow, det_mul_star hK, _root_.one_zpow]
    · intro τ _ _
      exact hK.ne τ
  exact ⟨ξ I, fun γ => by rw [hρ, hχ, one_smul], w, hw, hwξ⟩

end PositivityTheory.Rg.Cz

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PCurry
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace CurryingSwaps

variable {α : Type*} {m k : ℕ}

theorem upd_castAdd (I : Fin m → α) (J : Fin k → α) (i : Fin m) (v : α) :
    Function.update (Fin.append I J) (Fin.castAdd k i) v = Fin.append (Function.update I i v) J := by
  funext x
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) x
  · by_cases h : i' = i
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (Fin.castAdd_injective _ _ e)), Fin.append_left, Fin.append_left,
        Function.update_of_ne h]
  · rw [Function.update_of_ne (fun e => by simp [Fin.ext_iff] at e; omega), Fin.append_right, Fin.append_right]

theorem upd_natAdd (I : Fin m → α) (J : Fin k → α) (j : Fin k) (v : α) :
    Function.update (Fin.append I J) (Fin.natAdd m j) v = Fin.append I (Function.update J j v) := by
  funext x
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) x
  · rw [Function.update_of_ne (fun e => by simp [Fin.ext_iff] at e; omega), Fin.append_left, Fin.append_left]
  · by_cases h : j' = j
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (Fin.natAdd_injective _ _ e)), Fin.append_right, Fin.append_right,
        Function.update_of_ne h]

theorem swap_castAdd (I : Fin m → α) (J : Fin k → α) (i i' : Fin m) :
    Fin.append I J ∘ Equiv.swap (Fin.castAdd k i) (Fin.castAdd k i') = Fin.append (I ∘ Equiv.swap i i') J := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · simp only [Function.comp_apply, Fin.append_left, Equiv.swap_apply_def, Fin.castAdd_inj]
    split_ifs <;> simp
  · have h1 : Fin.natAdd m b ≠ Fin.castAdd k i := fun e => by simp [Fin.ext_iff] at e; omega
    have h2 : Fin.natAdd m b ≠ Fin.castAdd k i' := fun e => by simp [Fin.ext_iff] at e; omega
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right]

theorem swap_natAdd (I : Fin m → α) (J : Fin k → α) (j j' : Fin k) :
    Fin.append I J ∘ Equiv.swap (Fin.natAdd m j) (Fin.natAdd m j') = Fin.append I (J ∘ Equiv.swap j j') := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · have h1 : Fin.castAdd k a ≠ Fin.natAdd m j := fun e => by simp [Fin.ext_iff] at e; omega
    have h2 : Fin.castAdd k a ≠ Fin.natAdd m j' := fun e => by simp [Fin.ext_iff] at e; omega
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_left]
  · simp only [Function.comp_apply, Fin.append_right, Equiv.swap_apply_def, Fin.natAdd_inj]
    split_ifs <;> simp

theorem swap_mixed (I : Fin m → α) (J : Fin k → α) (i : Fin m) (j : Fin k) :
    Fin.append I J ∘ Equiv.swap (Fin.castAdd k i) (Fin.natAdd m j) =
      Fin.append (Function.update I i (J j)) (Function.update J j (I i)) := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · have h2 : Fin.castAdd k a ≠ Fin.natAdd m j := fun e => by simp [Fin.ext_iff] at e; omega
    by_cases h : a = i
    · subst h; simp
    · have h1 : Fin.castAdd k a ≠ Fin.castAdd k i := fun e => h (Fin.castAdd_injective _ _ e)
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_left,
        Function.update_of_ne h]
  · have h1 : Fin.natAdd m b ≠ Fin.castAdd k i := fun e => by simp [Fin.ext_iff] at e; omega
    by_cases h : b = j
    · subst h; simp
    · have h2 : Fin.natAdd m b ≠ Fin.natAdd m j := fun e => h (Fin.natAdd_injective _ _ e)
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right,
        Function.update_of_ne h]

theorem iteApp {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (p : Prop) [Decidable p]
    (g : V →ₗ[ℂ] W) (x : V) : (if p then g else 0) x = if p then g x else 0 := by
  split_ifs <;> rfl

end CurryingSwaps

open CurryingSwaps in
theorem curry_holds : Curry := by
  intro n M _ _ E m k
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g h
    funext K
    have := congrFun (congrFun (congrArg (fun x => x) h) (fun j => K (Fin.natAdd m j))) (fun i => K (Fin.castAdd k i))
    simpa only [curF_apply, Fin.append_castAdd_natAdd] using this
  · intro g
    refine ⟨fun K => g (fun j => K (Fin.natAdd m j)) (fun i => K (Fin.castAdd k i)), ?_⟩
    funext J I
    simp only [curF_apply, Fin.append_left, Fin.append_right]
  · intro a b
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    simp only [LinearMap.comp_apply, curF_apply, tE_apply, Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply,
      Fin.sum_univ_add, Fin.append_left, Fin.append_right, upd_castAdd, upd_natAdd, add_assoc]
  · intro i
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    have hz : ∀ b : Fin k, ¬ (Fin.natAdd m b < Fin.castAdd k i) := fun b h => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] at h <;> omega
    have hc : ∀ x : Fin m, Fin.castAdd k x < Fin.castAdd k i ↔ x < i := fun x => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega
    simp only [xJ, LinearMap.comp_apply, LinearMap.add_apply, Pi.add_apply, Om_apply, LinearMap.sum_apply,
      Finset.sum_apply, pm_apply, iteApp, ite_apply, Pi.zero_apply, lift_apply, curF_apply, Fin.append_left, upd_castAdd, Finset.sum_filter,
      Fin.sum_univ_add, swap_castAdd, hz, hc, if_false, Finset.sum_const_zero, add_zero]
  · intro j
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    have hz : ∀ x : Fin m, Fin.castAdd k x < Fin.natAdd m j := fun x => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega
    have hc : ∀ b : Fin k, Fin.natAdd m b < Fin.natAdd m j ↔ b < j := fun b => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega
    simp only [xJ, LinearMap.comp_apply, LinearMap.add_apply, Pi.add_apply, Om_apply, LinearMap.sum_apply,
      Finset.sum_apply, pm_apply, iteApp, ite_apply, Pi.zero_apply, curF_apply, tE_apply, Fin.append_right, upd_natAdd, upd_castAdd,
      Finset.sum_filter, Fin.sum_univ_add, swap_natAdd, swap_mixed, hz, hc, if_true, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun x p => if I p = x then
      f (Fin.append (Function.update I p (J j)) (Function.update J j x)) else 0)]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, add_assoc]
  · intro B
    rfl
  · intro i i'
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    simp only [LinearMap.comp_apply, curF_apply, pm_apply, lift_apply, swap_castAdd]
  · intro j j'
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    simp only [LinearMap.comp_apply, curF_apply, pm_apply, swap_natAdd]

end PositivityTheory.Rg.Cz

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransOf
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace TrOf

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem qdet_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B)
    (E : Fin n → Fin n → A) (u : ℂ) : φ (qdet E u) = qdet (fun a b => φ (E a b)) u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [qdet, qminor, Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def,
    map_add, apply_ite φ, map_zero, AlgHom.commutes]

variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

def rl (e : P ≃ Q) : TV n M P ≃ₗ[ℂ] TV n M Q :=
  LinearEquiv.funCongrLeft ℂ M (e.symm.arrowCongr (Equiv.refl (Fin n)))

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem rl_apply (e : P ≃ Q) (f : TV n M P) (J : Q → Fin n) : rl e f J = f (J ∘ e) := rfl

theorem tE_rl (e : P ≃ Q) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : TV n M P) :
    tE Finset.univ E a b (rl e f) = rl e (tE Finset.univ E a b f) := by
  funext J
  simp only [tE_apply, rl_apply]
  congr 1
  refine (Fintype.sum_equiv e.symm _ _ fun q => ?_)
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [← Function.update_comp_eq_of_injective J e.injective (e.symm q) b, Equiv.apply_symm_apply]

theorem conj_tE (e : P ≃ Q) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    (rl (n := n) (M := M) e).conjAlgEquiv ℂ (tE Finset.univ E a b) = tE Finset.univ E a b := by
  refine LinearMap.ext fun g => ?_
  simp only [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← tE_rl, LinearEquiv.apply_symm_apply]

theorem cA_rl {C : Type} [DecidableEq C] (e : P ≃ Q) (col : P → C) (b : P → Fin n) (f : TV n M P) :
    cA (col ∘ e.symm) (b ∘ e.symm) (rl e f) = cA col b f := by
  simp only [cA_apply, alt_apply, rl_apply]
  symm
  refine Finset.sum_equiv (Equiv.permCongr e) (fun σ => ?_) (fun σ _ => ?_)
  · simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply, Equiv.permCongr_apply,
      Equiv.symm_apply_apply]
    exact ⟨fun h q => h _, fun h p => by simpa using h (e p)⟩
  · rw [Equiv.Perm.sign_permCongr]
    congr 2
    funext x
    simp [Equiv.permCongr_apply]

theorem cA_congr {C C' : Type} [DecidableEq C] [DecidableEq C'] (c1 : Q → C) (c2 : Q → C')
    (h : ∀ p q, c1 p = c1 q ↔ c2 p = c2 q) (b : Q → Fin n) : (cA c1 b : TV n M Q →ₗ[ℂ] M) = cA c2 b := by
  have : colG c1 = colG c2 := by
    ext σ
    simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and, h]
  simp only [cA, this]

theorem transfer (e : P ≃ Q) (E : Fin n → Fin n → Module.End ℂ M) (l : Fin n → ℤ) (ℓ : M →ₗ[ℂ] ℂ)
    {C C' : Type} [DecidableEq C] [DecidableEq C'] (col : P → C) (col' : Q → C')
    (hcol : ∀ q q', col' q = col' q' ↔ col (e.symm q) = col (e.symm q')) (b co : P → Fin n)
    (h : ∃ S ∈ envAlg (fun _ : Unit => tE (Finset.univ : Finset Q) E), ℓ ∘ₗ cA col' (b ∘ e.symm) ∘ₗ S ≠ 0 ∧
      ∀ u : ℂ, (ℓ ∘ₗ cA col' (b ∘ e.symm) ∘ₗ S) ∘ₗ qdet (tE (Finset.univ : Finset Q) E) u =
        (∏ k, (u + l k + ((Finset.univ.filter fun p => co (e.symm p) = k).card : ℂ))) •
          (ℓ ∘ₗ cA col' (b ∘ e.symm) ∘ₗ S)) :
    ∃ S ∈ envAlg (fun _ : Unit => tE (Finset.univ : Finset P) E), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ u : ℂ,
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (Finset.univ : Finset P) E) u =
        (∏ k, (u + l k + ((Finset.univ.filter fun p => co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S) := by
  obtain ⟨S', hS', hne, heig⟩ := h
  set φ := (rl (n := n) (M := M) e).conjAlgEquiv ℂ with hφdef
  set K := ℓ ∘ₗ cA col' (b ∘ e.symm) ∘ₗ S' with hK
  have hsymm : ∀ T f, φ.symm T f = (rl e).symm (T (rl e f)) := fun T f => rfl
  have key : ∀ f, ℓ (cA col b (φ.symm S' f)) = K (rl e f) := by
    intro f
    simp only [hK, LinearMap.comp_apply, hsymm]
    rw [← cA_rl e col b, LinearEquiv.apply_symm_apply, cA_congr col' (col ∘ e.symm) hcol]
  have hq : ∀ u f, rl e (qdet (tE (Finset.univ : Finset P) E) u f) = qdet (tE (Finset.univ : Finset Q) E) u (rl e f) := by
    intro u f
    have h1 : φ (qdet (tE (Finset.univ : Finset P) E) u) = qdet (tE (Finset.univ : Finset Q) E) u := by
      have := qdet_map (φ : Module.End ℂ (TV n M P) →ₐ[ℂ] Module.End ℂ (TV n M Q)) (tE (Finset.univ : Finset P) E) u
      simpa [conj_tE, hφdef] using this
    rw [← h1]
    simp only [hφdef, LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  have hcard : ∀ k, (Finset.univ.filter fun p => co (e.symm p) = k).card = (Finset.univ.filter fun p => co p = k).card :=
    fun k => Finset.card_equiv e.symm (by simp)
  refine ⟨φ.symm S', ?_, ?_, ?_⟩
  · have hle : envAlg (fun _ : Unit => tE (Finset.univ : Finset Q) E) ≤
        (envAlg (fun _ : Unit => tE (Finset.univ : Finset P) E)).comap φ.symm.toAlgHom := by
      refine Algebra.adjoin_le ?_
      rintro T ⟨_, a, c, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_comap]
      change φ.symm (tE Finset.univ E a c) ∈ _
      rw [φ.symm_apply_eq.mpr (conj_tE e E a c).symm]
      exact Algebra.subset_adjoin ⟨(), a, c, rfl⟩
    exact hle hS'
  · intro h0
    apply hne
    refine LinearMap.ext fun g => ?_
    have := LinearMap.congr_fun h0 ((rl e).symm g)
    simp only [LinearMap.comp_apply] at this
    rw [key, LinearEquiv.apply_symm_apply] at this
    simpa using this
  · intro u
    refine LinearMap.ext fun f => ?_
    have := LinearMap.congr_fun (heig u) (rl e f)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at this ⊢
    rw [key, key, hq, this]
    simp only [hK, LinearMap.comp_apply, hcard]

theorem zero_case (E : Fin 0 → Fin 0 → Module.End ℂ M) (l : Fin 0 → ℤ) (ℓ : M →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0)
    {C : Type} [DecidableEq C] (col : P → C) (b co : P → Fin 0) :
    ∃ S ∈ envAlg (fun _ : Unit => tE (Finset.univ : Finset P) E), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ u : ℂ,
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (Finset.univ : Finset P) E) u =
        (∏ k, (u + l k + ((Finset.univ.filter fun p => co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S) := by
  have : IsEmpty P := ⟨fun p => (b p).elim0⟩
  have hσ : ∀ σ : Equiv.Perm P, σ = 1 := fun σ => Equiv.ext fun p => isEmptyElim p
  have hG : colG col = {1} := by
    ext σ
    simp [colG, hσ σ]
  have hqd : ∀ u, qdet (tE (Finset.univ : Finset P) E) u = 1 := by
    intro u
    simp [qdet, qminor]
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hℓ (LinearMap.ext h)
  refine ⟨1, Subalgebra.one_mem _, fun h0 => hv ?_, fun u => ?_⟩
  · have := LinearMap.congr_fun h0 (fun _ => v)
    simpa [cA_apply, alt_apply, hG] using this
  · rw [hqd]
    refine LinearMap.ext fun x => ?_
    simp

def cI {C : Type} [DecidableEq C] (col : P → C) (p : P) : ℕ :=
  (Fintype.equivFin (Set.range col) ⟨col p, p, rfl⟩ : ℕ)

theorem cI_eq {C : Type} [DecidableEq C] (col : P → C) (p q : P) : cI col p = cI col q ↔ col p = col q := by
  simp only [cI, Fin.val_inj, Equiv.apply_eq_iff_eq, Subtype.ext_iff]

omit [DecidableEq P] in
theorem exists_sort {α : Type} [LinearOrder α] (key : P → α) :
    ∃ e : P ≃ Fin (Fintype.card P), Monotone (key ∘ e.symm) :=
  ⟨(Fintype.equivFin P).trans (Tuple.sort (key ∘ (Fintype.equivFin P).symm)).symm,
    Tuple.monotone_sort (key ∘ (Fintype.equivFin P).symm)⟩

end TrOf

theorem trans_of (hT : TransFin) : Trans := by
  intro n M _ _ E hE l hl ℓ hℓ hW P _ _ C _ col b co hb hco
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact TrOf.zero_case E l ℓ hℓ col b co
  set a : P → ℕ := TrOf.cI col with ha
  set v : P → ℤ := fun p => l (co p) + ((Finset.univ.filter fun q => a q < a p ∧ co q = co p).card : ℤ) with hv
  obtain ⟨e, he⟩ := TrOf.exists_sort (fun p => toLex (a p, OrderDual.toDual (v p)))
  have hle : ∀ i j : Fin (Fintype.card P), i ≤ j → a (e.symm i) ≤ a (e.symm j) ∧
      (a (e.symm i) = a (e.symm j) → v (e.symm j) ≤ v (e.symm i)) := by
    intro i j hij
    have := he hij
    simp only [Function.comp_apply, Prod.Lex.toLex_le_toLex, OrderDual.toDual_le_toDual] at this
    rcases this with h | ⟨h1, h2⟩
    · exact ⟨h.le, fun h' => absurd h' h.ne⟩
    · exact ⟨h1.le, fun _ => h2⟩
  have hmono : Monotone (a ∘ e.symm) := fun i j hij => (hle i j hij).1
  have hainj : ∀ p q, a p = a q ↔ col p = col q := TrOf.cI_eq col
  have htab : IsTab (a ∘ e.symm) (b ∘ e.symm) := by
    refine ⟨fun i j h1 h2 => e.symm.injective (hb.1 _ _ ((hainj _ _).1 h1) h2), fun i k hk => ?_⟩
    obtain ⟨q, hq1, hq2⟩ := hb.2 (e.symm i) k hk
    exact ⟨e q, by simp [(hainj _ _).2 hq1], by simpa using hq2⟩
  have hco' : ∀ i j : Fin (Fintype.card P), a (e.symm i) = a (e.symm j) → co (e.symm i) = co (e.symm j) → i = j :=
    fun i j h1 h2 => e.symm.injective (hco _ _ ((hainj _ _).1 h1) h2)
  have hcnt : ∀ j : Fin (Fintype.card P), (Finset.univ.filter fun p => p < j ∧ co (e.symm p) = co (e.symm j)).card =
      (Finset.univ.filter fun q => a q < a (e.symm j) ∧ co q = co (e.symm j)).card := by
    intro j
    refine Finset.card_equiv e.symm (fun p => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr_left fun hc => ⟨fun hp => lt_of_le_of_ne (hmono hp.le) (fun h => hp.ne (hco' p j h hc)),
      fun h => ?_⟩
    by_contra hp
    exact absurd (hmono (not_lt.1 hp)) (not_le.2 h)
  have hord : ∀ i j : Fin (Fintype.card P), i < j → (a ∘ e.symm) i = (a ∘ e.symm) j →
      l ((co ∘ e.symm) j) + ((Finset.univ.filter fun p => p < j ∧ (co ∘ e.symm) p = (co ∘ e.symm) j).card : ℤ) ≤
        l ((co ∘ e.symm) i) + ((Finset.univ.filter fun p => p < i ∧ (co ∘ e.symm) p = (co ∘ e.symm) i).card : ℤ) := by
    intro i j hij h
    simp only [Function.comp_apply] at h ⊢
    rw [hcnt i, hcnt j]
    exact (hle i j hij.le).2 h
  have := hT n M E hE l hl ℓ hℓ hW hn (Fintype.card P) (a ∘ e.symm) (b ∘ e.symm) (co ∘ e.symm) hmono htab hord
  exact TrOf.transfer e E l ℓ col (a ∘ e.symm) (fun q q' => hainj _ _) b co this

end PositivityTheory.Rg.Cz

end
end
