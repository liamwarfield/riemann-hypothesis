module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestRawTail1Of
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TopOddNeEnd

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyOne
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

theorem liftSubst_one_X {p f : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p f) O] (w : O) (r : ℕ)
    {ι : Type} {k : ℕ} (LL : LiftLetters ι) (v : ι × Fin k) :
    liftSubst p f O w r LL (1 : Matrix (Fin k) (Fin k) (WF p f)) (X v) =
      C (algebraMap O (KK O) (dW O w LL r v.1 v.2)) * X v := by
  unfold liftSubst
  rw [MvPolynomial.aeval_X, sigMat_one, inv_one]
  by_cases hv : LL.vec v.1 <;> simp [hv, Matrix.one_apply, dW] <;> split_ifs <;> simp_all

theorem liftSubst_one_hh {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (x : X.TT × Bool) (b : Fin (X.m + 1)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
        (MvPolynomial.X (x, b)) =
      (if (x.2 = true ∧ 1 ≤ (b : ℕ)) ∨ (x.2 = false ∧ (b : ℕ) < 1) then
        C (algebraMap O (KK O) w) * MvPolynomial.X (x, b) else MvPolynomial.X (x, b)) := by
  rw [liftSubst_one_X]
  have hd : dW O w (hhLetters X.TT) 1 x b =
      if (x.2 = true ∧ 1 ≤ (b : ℕ)) ∨ (x.2 = false ∧ (b : ℕ) < 1) then w else 1 := rfl
  rw [hd]
  split_ifs <;> simp

private theorem liftSubst_X_true_zero_eq_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, true), (0 : Fin (X.m + 1)))) = MvPolynomial.X ((y, true), 0) := by
  rw [liftSubst_one_hh]
  simp

private theorem liftSubst_X_true_succ_eq_C_mul_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, true), c.succ)) =
        C (algebraMap O (KK O) w) * MvPolynomial.X ((y, true), c.succ) := by
  rw [liftSubst_one_hh]
  simp

private theorem liftSubst_X_false_zero_eq_C_mul_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, false), (0 : Fin (X.m + 1)))) =
        C (algebraMap O (KK O) w) * MvPolynomial.X ((y, false), 0) := by
  rw [liftSubst_one_hh]
  simp

private theorem liftSubst_X_false_succ_eq_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, false), c.succ)) = MvPolynomial.X ((y, false), c.succ) := by
  rw [liftSubst_one_hh]
  simp

theorem key3One_S {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (kSkey O X j i) =
      w • (MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), 0) +
        w ^ (X.p ^ (segDists X.TT j).get i - 1) • (∑ c : Fin X.m,
          MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) *
            MvPolynomial.X ((topOdd X j i, false), c.succ) : RHH O X) : RHH O X) := by
  have hq1 : 1 ≤ X.p ^ (segDists X.TT j).get i := Nat.one_le_pow _ _ (Fact.out : X.p.Prime).pos
  unfold kSkey
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Fin.sum_univ_succ]
  simp only [map_mul, map_pow, liftSubst_X_true_zero_eq_X, liftSubst_X_true_succ_eq_C_mul_X, liftSubst_X_false_zero_eq_C_mul_X, liftSubst_X_false_succ_eq_X]
  rw [Algebra.smul_def, Algebra.smul_def, MvPolynomial.algebraMap_apply,
    MvPolynomial.algebraMap_apply, map_pow, map_pow]
  obtain ⟨q', hq'⟩ : ∃ q', X.p ^ (segDists X.TT j).get i = q' + 1 :=
    ⟨_, (Nat.sub_add_cancel hq1).symm⟩
  rw [hq', Nat.add_sub_cancel]
  have hsum : ∑ c : Fin X.m, (C (algebraMap O (KK O) w) * MvPolynomial.X ((topStart X j, true), c.succ)) ^
      (q' + 1) * MvPolynomial.X ((topOdd X j i, false), c.succ) =
      C (algebraMap O (KK O) w) ^ (q' + 1) * ∑ c : Fin X.m,
        MvPolynomial.X ((topStart X j, true), c.succ) ^ (q' + 1) * MvPolynomial.X ((topOdd X j i, false), c.succ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsum]
  ring

theorem key_lift_identity_lower {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (kWkey O X j i c.succ) =
      w • (MvPolynomial.X ((topOdd X j i, true), c.succ) * MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) -
        w ^ (X.p ^ (segDists X.TT j).get i - 1) •
          (MvPolynomial.X ((topOdd X j i, true), 0) *
            MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) : RHH O X) : RHH O X) := by
  have hq1 : 1 ≤ X.p ^ (segDists X.TT j).get i := Nat.one_le_pow _ _ (Fact.out : X.p.Prime).pos
  unfold kWkey
  simp only [map_sub, map_mul, map_pow, liftSubst_X_true_zero_eq_X, liftSubst_X_true_succ_eq_C_mul_X]
  rw [Algebra.smul_def, Algebra.smul_def, MvPolynomial.algebraMap_apply,
    MvPolynomial.algebraMap_apply, map_pow, map_pow]
  obtain ⟨q', hq'⟩ : ∃ q', X.p ^ (segDists X.TT j).get i = q' + 1 :=
    ⟨_, (Nat.sub_add_cancel hq1).symm⟩
  rw [hq', Nat.add_sub_cancel]
  ring

theorem loc4One {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (locC O X c.succ) =
      ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j - 1) -
        w ^ (∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1)) •
          (∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ segG X.TT j - 1) : RHH O X) := by
  unfold locC
  simp only [map_sub, map_prod, map_pow, liftSubst_X_true_zero_eq_X, liftSubst_X_true_succ_eq_C_mul_X]
  rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, map_pow, map_pow,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun j _ => mul_pow _ _ _

def CoarseMultiplicityOrderBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X →
    ∀ (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)),
      ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
        InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) 1 ∧
        ∀ c : Fin X.m, InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c.succ) 1

def LocalOrderBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    ∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (locR O X j0) 1

theorem third_key_of_order (h : CoarseMultiplicityOrderBound) : CoarseMultiplicityBoundAtIdentity := by
  intro X _ O _ _ _ _ S hSq hD j i
  exact ⟨fun g hg => h X O S hSq hD j i g hg, key3One_S S.w j i, fun c => key_lift_identity_lower S.w j i c⟩

theorem local_fourth_of_order (h : LocalOrderBound) : LocalBoundAtIdentity := by
  intro X _ O _ _ _ _ S hSq hD hn
  exact ⟨fun j0 g hg hr => h X O S hSq hD hn j0 g hg hr, fun c => loc4One S.w c⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockMonomial
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem symVar_inj (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    Function.Injective (symVar C0 CE1 CE2 X j) := by
  rintro (⟨a, c⟩ | ⟨l, b⟩) (⟨a', c'⟩ | ⟨l', b'⟩) h
  · simp only [symVar] at h
    have ha2 := a.2
    have ha2' := a'.2
    split_ifs at h with h1 h2 h2
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨e1, e2⟩, e3⟩ := h
      have e1' : (a : ℕ) / 2 = (a' : ℕ) / 2 := congrArg Fin.val (topOdd_inj X j e1)
      have e2' := decide_eq_decide.1 e2
      have hc : c = c' := Fin.succ_injective _ e3
      have ha : a = a' := Fin.ext (by omega)
      rw [ha, hc]
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.1 (topOdd_ne_end X j _)
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.1.symm (topOdd_ne_end X j _)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨-, e2⟩, e3⟩ := h
      have e2' := decide_eq_decide.1 e2
      have hc : c = c' := Fin.succ_injective _ e3
      have ha : a = a' := Fin.ext (by omega)
      rw [ha, hc]
  · exfalso
    simp only [symVar] at h
    split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> exact Fin.succ_ne_zero _ h.2
  · exfalso
    simp only [symVar] at h
    split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> exact Fin.succ_ne_zero _ h.2.symm
  · simp only [symVar] at h
    have hl2 := l.2
    have hl2' := l'.2
    split_ifs at h with h1 h2 h2
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨e1, e2⟩, -⟩ := h
      have e1' : (X.seg C0 CE1 CE2 j).sigma + (l : ℕ) = (X.seg C0 CE1 CE2 j).sigma + (l' : ℕ) :=
        congrArg Fin.val (topOdd_inj X j e1)
      have hl : l = l' := Fin.ext (by omega)
      have hb : b = b' := by simpa using e2
      rw [hl, hb]
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.1 (topOdd_ne_end X j _)
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.1.symm (topOdd_ne_end X j _)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨-, e2⟩, -⟩ := h
      have hl : l = l' := Fin.ext (by omega)
      have hb : b = b' := by simpa using e2
      rw [hl, hb]

theorem symLev_pos (C0 CE1 CE2 : ℝ) (X : Loc) (hp : 0 < X.p) (j : Fin (numSeg X.TT)) (v : BV C0 CE1 CE2 X j) :
    0 < symLev X.p C0 CE1 CE2 X j v := by
  rcases v with ⟨a, c⟩ | ⟨l, b⟩
  · simp only [symLev]
    split_ifs
    · exact pow_pos hp _
    · exact one_pos
  · simp only [symLev]
    split_ifs
    · exact pow_pos hp _
    · exact one_pos

theorem coarse_eval (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (μ : BV C0 CE1 CE2 X j →₀ ℕ)
    (v0 : BV C0 CE1 CE2 X j) :
    (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n))
      (symVar C0 CE1 CE2 X j v0) = symLev X.p C0 CE1 CE2 X j v0 * μ v0 := by
  classical
  rw [Finsupp.sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finsupp.sum, Finset.sum_eq_single v0]
  · simp
  · intro v _ hv
    rw [if_neg fun e => hv (symVar_inj C0 CE1 CE2 X j e)]
  · intro hv
    simp [Finsupp.notMem_support_iff.1 hv]

theorem ioExp_inj (C0 CE1 CE2 : ℝ) (X : Loc) (hp : 0 < X.p) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) :
    Function.Injective (ioExp C0 CE1 CE2 X j b) := by
  intro μ μ' h
  unfold ioExp at h
  have h' := add_left_cancel h
  ext v0
  have := DFunLike.congr_fun h' (symVar C0 CE1 CE2 X j v0)
  rw [coarse_eval, coarse_eval] at this
  exact Nat.eq_of_mul_eq_mul_left (symLev_pos C0 CE1 CE2 X hp j v0) this

theorem ioBlock_monomial (C0 CE1 CE2 : ℝ) (X : Loc) (K : Type) [Field K] (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (μ : BV C0 CE1 CE2 X j →₀ ℕ) (c : K) :
    ioBlock K X.p C0 CE1 CE2 X j b (monomial μ c) = monomial (ioExp C0 CE1 CE2 X j b μ) c := by
  classical
  have hd : digitMon K C0 CE1 CE2 X j b = monomial (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
      (Finsupp.single ((topOdd X j i, true), c) (b.rz i c) + Finsupp.single ((topOdd X j i, false), c) (b.ry i c))) 1 := by
    unfold digitMon
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
  have hs : sTopMon K X.p C0 CE1 CE2 X j b = monomial (∑ i : Fin (segS X.TT j),
      if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
            ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i)) +
          Finsupp.single ((topOdd X j i, false), (0 : Fin (X.m + 1))) ((X.seg C0 CE1 CE2 j).P X.p i * b.sg i)
      else 0) 1 := by
    unfold sTopMon
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs
    · rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
    · simp
  have ha : aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) :
      MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^ symLev X.p C0 CE1 CE2 X j v) (monomial μ c) =
      monomial (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n)) c := by
    rw [aeval_monomial, monomial_finsupp_sum_index]
    congr 1
    refine Finsupp.prod_congr fun v _ => ?_
    rw [← pow_mul, X_pow_eq_monomial]
  unfold ioBlock ioExp baseExp
  rw [hd, hs, ha, monomial_mul, monomial_mul, one_mul, one_mul]

theorem ioFockAt : IoFockAt := by
  intro C0 CE1 CE2 X K _ hp j b u u'
  let f : MvPolynomial (BV C0 CE1 CE2 X j) K →ₗ[K] MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
    (LinearMap.mulLeft K (digitMon K C0 CE1 CE2 X j b * sTopMon K X.p C0 CE1 CE2 X j b)).comp
      (aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) :
        MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^ symLev X.p C0 CE1 CE2 X j v)).toLinearMap
  exact fock_monoMap f (ioExp C0 CE1 CE2 X j b) (ioExp_inj C0 CE1 CE2 X hp j b)
    (fun μ c => ioBlock_monomial C0 CE1 CE2 X K j b μ c) u u'

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SymbolVariableLowerLetter
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem wh_aeval {K : Type} [CommRing K] {σ τ : Type} (ω : τ → ℕ) (f : σ → τ) (lev : σ → ℕ) (u : MvPolynomial σ K) (n : ℕ)
    (h : IsWeightedHomogeneous (fun v => lev v * ω (f v)) u n) :
    IsWeightedHomogeneous ω (aeval (fun v => (X (f v) : MvPolynomial τ K) ^ lev v) u) n := by
  have e : aeval (fun v => (X (f v) : MvPolynomial τ K) ^ lev v) u =
      ∑ μ ∈ u.support, aeval (fun v => (X (f v) : MvPolynomial τ K) ^ lev v) (monomial μ (u.coeff μ)) := by
    conv_lhs => rw [← support_sum_monomial_coeff u]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
  rw [e]
  refine IsWeightedHomogeneous.sum _ _ _ fun μ hμ => ?_
  rw [aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.prod]
  have hw : Finsupp.weight (fun v => lev v * ω (f v)) μ = n := h (mem_support_iff.1 hμ)
  have h1 := IsWeightedHomogeneous.prod μ.support (fun v => ((X (f v) : MvPolynomial τ K) ^ lev v) ^ μ v) _
    (fun v _ => ((isWeightedHomogeneous_X K ω (f v)).pow (lev v)).pow (μ v))
  have h2 := (isWeightedHomogeneous_C ω (u.coeff μ)).mul h1
  refine wh_congr h2 ?_
  rw [zero_add, ← hw, Finsupp.weight_apply, Finsupp.sum]
  simp only [smul_eq_mul]

theorem sum_chain {s : ℕ} (f : Fin (2 * s + 1) → ℕ) :
    ∑ a, f a = ∑ i : Fin s, (f ⟨2 * i.val, by omega⟩ + f ⟨2 * i.val + 1, by omega⟩) + f ⟨2 * s, by omega⟩ := by
  let F : ℕ → ℕ := fun k => if h : k < 2 * s + 1 then f ⟨k, h⟩ else 0
  have e1 : ∑ a, f a = ∑ k ∈ Finset.range (2 * s + 1), F k := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [F]
    rw [dite_eq_left a.2]
  have e2 : ∀ n, ∑ k ∈ Finset.range (2 * n + 1), F k = ∑ i ∈ Finset.range n, (F (2 * i) + F (2 * i + 1)) + F (2 * n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring
  rw [e1, e2 s, Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have := i.2
    simp only [F]
    rw [dite_eq_left (by omega), dite_eq_left (by omega)]
  · simp only [F]
    rw [dite_eq_left (by omega)]

theorem sum_uTop {s : ℕ} (S : SegData s) (g : Fin s → ℕ) :
    ∑ l : Fin S.t, g (uTop S l) = ∑ i : Fin s, if S.sigma ≤ i.val then g i else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij (fun l => uTop S l) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro l _
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.le_add_right _ _⟩
  · intro l _ l' _ h
    apply Fin.ext
    have h' : S.sigma + l.val = S.sigma + l'.val := congrArg Fin.val h
    omega
  · intro i hi
    have hi' := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
    have := i.2
    exact ⟨⟨i.val - S.sigma, by unfold SegData.t; omega⟩, Finset.mem_coe.2 (Finset.mem_univ _),
      Fin.ext (by show S.sigma + (i.val - S.sigma) = i.val; omega)⟩

section Sym

variable (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))

theorem sv_Z (l : Fin (X.seg C0 CE1 CE2 j).t) (β : Bool) :
    symVar C0 CE1 CE2 X j (Sum.inr (Fin.castSucc l, β)) = ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !β), 0) := by
  simp only [symVar]
  rw [dite_eq_left (show ((Fin.castSucc l : Fin _) : ℕ) < _ from l.2)]
  rfl

theorem sl_Z (l : Fin (X.seg C0 CE1 CE2 j).t) (β : Bool) :
    symLev X.p C0 CE1 CE2 X j (Sum.inr (Fin.castSucc l, β)) =
      (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) := by
  simp only [symLev]
  rw [dite_eq_left (show ((Fin.castSucc l : Fin _) : ℕ) < _ from l.2)]
  rfl

theorem symbol_variable_last (β : Bool) :
    symVar C0 CE1 CE2 X j (Sum.inr (Fin.last _, β)) = ((topEnd X j, !β), 0) := by
  simp only [symVar]
  rw [dite_eq_right (hnc := by show ¬ ((Fin.last (X.seg C0 CE1 CE2 j).t : Fin _) : ℕ) < _; exact lt_irrefl _)]

theorem symbol_level_last (β : Bool) : symLev X.p C0 CE1 CE2 X j (Sum.inr (Fin.last _, β)) = 1 := by
  simp only [symLev]
  rw [dite_eq_right (hnc := by show ¬ ((Fin.last (X.seg C0 CE1 CE2 j).t : Fin _) : ℕ) < _; exact lt_irrefl _)]

theorem symbol_variable_lower_letter (i : Fin (segS X.TT j)) (c : Fin X.m) :
    symVar C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      ((topOdd X j i, true), c.succ) := by
  have hi := i.2
  simp only [symVar]
  rw [dite_eq_left (hc := by show 2 * i.val < 2 * segS X.TT j; omega)]
  have e1 : (⟨(2 * i.val) / 2, by omega⟩ : Fin (segS X.TT j)) = i := Fin.ext (by show 2 * i.val / 2 = i.val; omega)
  have e2 : decide ((2 * i.val) % 2 = 0) = true := by simp
  show ((topOdd X j ⟨(2 * i.val) / 2, _⟩, decide ((2 * i.val) % 2 = 0)), c.succ) = _
  rw [e1, e2]

theorem symbol_level_lower_letter (i : Fin (segS X.TT j)) (c : Fin X.m) :
    symLev X.p C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      (X.seg C0 CE1 CE2 j).P X.p i := by
  have hi := i.2
  simp only [symLev]
  rw [dite_eq_left (hc := by show 2 * i.val < 2 * segS X.TT j; omega)]
  have e1 : (⟨(2 * i.val) / 2, by omega⟩ : Fin (segS X.TT j)) = i := Fin.ext (by show 2 * i.val / 2 = i.val; omega)
  show (X.seg C0 CE1 CE2 j).P X.p ⟨(2 * i.val) / 2, _⟩ = _
  rw [e1]

theorem sv_E (i : Fin (segS X.TT j)) (c : Fin X.m) :
    symVar C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      ((topOdd X j i, false), c.succ) := by
  have hi := i.2
  simp only [symVar]
  rw [dite_eq_left (hc := by show 2 * i.val + 1 < 2 * segS X.TT j; omega)]
  have e1 : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin (segS X.TT j)) = i :=
    Fin.ext (by show (2 * i.val + 1) / 2 = i.val; omega)
  have e2 : decide ((2 * i.val + 1) % 2 = 0) = false := by
    rw [decide_eq_false_iff_not]
    omega
  show ((topOdd X j ⟨(2 * i.val + 1) / 2, _⟩, decide ((2 * i.val + 1) % 2 = 0)), c.succ) = _
  rw [e1, e2]

theorem sl_E (i : Fin (segS X.TT j)) (c : Fin X.m) :
    symLev X.p C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      (X.seg C0 CE1 CE2 j).P X.p i := by
  have hi := i.2
  simp only [symLev]
  rw [dite_eq_left (hc := by show 2 * i.val + 1 < 2 * segS X.TT j; omega)]
  have e1 : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin (segS X.TT j)) = i :=
    Fin.ext (by show (2 * i.val + 1) / 2 = i.val; omega)
  show (X.seg C0 CE1 CE2 j).P X.p ⟨(2 * i.val + 1) / 2, _⟩ = _
  rw [e1]

theorem sv_U (c : Fin X.m) :
    symVar C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      ((topEnd X j, true), c.succ) := by
  simp only [symVar]
  rw [dite_eq_right (hnc := by show ¬ 2 * segS X.TT j < 2 * segS X.TT j; exact lt_irrefl _)]
  show ((topEnd X j, decide (2 * segS X.TT j = 2 * segS X.TT j)), c.succ) = _
  simp

theorem sl_U (c : Fin X.m) :
    symLev X.p C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) = 1 := by
  simp only [symLev]
  rw [dite_eq_right (hnc := by show ¬ 2 * segS X.TT j < 2 * segS X.TT j; exact lt_irrefl _)]

theorem sv_xi (c : Fin X.m) :
    symVar C0 CE1 CE2 X j (Sum.inl (Fin.last (2 * segS X.TT j + 1), c)) = ((topEnd X j, false), c.succ) := by
  simp only [symVar]
  rw [dite_eq_right (hnc := by show ¬ 2 * segS X.TT j + 1 < 2 * segS X.TT j; omega)]
  show ((topEnd X j, decide (2 * segS X.TT j + 1 = 2 * segS X.TT j)), c.succ) = _
  simp

theorem sl_xi (c : Fin X.m) :
    symLev X.p C0 CE1 CE2 X j (Sum.inl (Fin.last (2 * segS X.TT j + 1), c)) = 1 := by
  simp only [symLev]
  rw [dite_eq_right (hnc := by show ¬ 2 * segS X.TT j + 1 < 2 * segS X.TT j; omega)]

end Sym

end Formalism.MainNotions.ColumnSystems.Pf
end
end
