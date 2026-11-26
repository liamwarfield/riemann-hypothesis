module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFDefs
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftSubstitutionCoeffDivisible

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.HookKeyOrderGeOne
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

section Order

variable {O : Type} [CommRing O] [IsDomain O] {σ : Type}

theorem inWj_mul {w : O} {P Q : MvPolynomial σ (KK O)} {a b : ℕ} (hP : InWj w P a) (hQ : InWj w Q b) :
    InWj w (P * Q) (a + b) := by
  classical
  intro m
  choose cp hcp using hP
  choose cq hcq using hQ
  refine ⟨∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, cp x.1 * cq x.2, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_mul, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hcp, hcq, ← map_mul]
  congr 1
  ring

theorem inWj_one (w : O) : InWj w (1 : MvPolynomial σ (KK O)) 0 := by
  classical
  intro m
  rw [coeff_one]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem inWj_pow {w : O} {P : MvPolynomial σ (KK O)} {a : ℕ} (hP : InWj w P a) (n : ℕ) : InWj w (P ^ n) (n * a) := by
  induction n with
  | zero => simpa using inWj_one w
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact inWj_mul ih hP

theorem inWj_prod {w : O} {ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ (KK O)) (a : ι → ℕ)
    (h : ∀ i ∈ s, InWj w (P i) (a i)) : InWj w (∏ i ∈ s, P i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inWj_one w
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact inWj_mul (h i (Finset.mem_insert_self _ _)) (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

end Order

section Rg

variable {p f : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF p f) O]
  {k : ℕ} {ι : Type}

theorem inWjRg_mul {w : O} {r : ℕ} {LL : LiftLetters ι} {g : Matrix (Fin k) (Fin k) (WF p f)}
    {F G : MvPolynomial (ι × Fin k) (KK O)} {a b : ℕ} (hF : InWjRg p f O w r LL g F a)
    (hG : InWjRg p f O w r LL g G b) : InWjRg p f O w r LL g (F * G) (a + b) := by
  unfold InWjRg at *
  rw [map_mul]
  exact inWj_mul hF hG

theorem inWjRg_pow {w : O} {r : ℕ} {LL : LiftLetters ι} {g : Matrix (Fin k) (Fin k) (WF p f)}
    {F : MvPolynomial (ι × Fin k) (KK O)} {a : ℕ} (hF : InWjRg p f O w r LL g F a) (n : ℕ) :
    InWjRg p f O w r LL g (F ^ n) (n * a) := by
  unfold InWjRg at *
  rw [map_pow]
  exact inWj_pow hF n

theorem inWjRg_prod {w : O} {r : ℕ} {LL : LiftLetters ι} {g : Matrix (Fin k) (Fin k) (WF p f)} {κ : Type}
    (s : Finset κ) (F : κ → MvPolynomial (ι × Fin k) (KK O)) (a : κ → ℕ)
    (h : ∀ i ∈ s, InWjRg p f O w r LL g (F i) (a i)) : InWjRg p f O w r LL g (∏ i ∈ s, F i) (∑ i ∈ s, a i) := by
  unfold InWjRg at *
  rw [map_prod]
  exact inWj_prod s _ a h

def hKey (O : Type) [CommRing O] [IsDomain O] {ι : Type} (k : ℕ) (l l' : ι) : MvPolynomial (ι × Fin k) (KK O) :=
  ∑ a : Fin k, X (l, a) * X (l', a)

theorem hook_key_lift_exact (w : O) (LL : LiftLetters ι) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p f)) (hg : IsGLW g) (l l' : ι)
    (hl : LL.vec l = true) (hl' : LL.vec l' = false) (hpos : LL.pos l = LL.pos l') :
    liftSubst p f O w r LL g (hKey O k l l') = C (algebraMap O (KK O) w) * hKey O k l l' := by
  classical
  unfold hKey
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_mul, liftSubst_X_vec p f O w LL r g hg l _ hl, liftSubst_X_cov p f O w LL r g l' _ hl']
  have hinv : ∀ b b' : Fin k, ∑ a : Fin k, sigMat p f O g⁻¹ (LL.pos l) b a * sigMat p f O g (LL.pos l') a b' =
      if b = b' then 1 else 0 := by
    intro b b'
    rw [← hpos, ← Matrix.mul_apply, ← sigMat_mul, Matrix.nonsing_inv_mul g hg, sigMat_one, Matrix.one_apply]
  have hd : ∀ b : Fin k, dW O w LL r l b * dW O w LL r l' b = w := by
    intro b
    by_cases hb : b.val < r
    · have hb' : ¬ r ≤ b.val := by omega
      simp [dW, hl, hl', hb, hb']
    · have hb' : r ≤ b.val := by omega
      simp [dW, hl, hl', hb, hb']
  calc ∑ a : Fin k, (∑ b : Fin k, C (algebraMap O (KK O) (dW O w LL r l b)) * X (l, b) *
          C (sigMat p f O g⁻¹ (LL.pos l) b a)) *
        (∑ b' : Fin k, C (algebraMap O (KK O) (dW O w LL r l' b')) * X (l', b') * C (sigMat p f O g (LL.pos l') a b'))
      = ∑ b : Fin k, ∑ b' : Fin k, C (algebraMap O (KK O) (dW O w LL r l b)) * X (l, b) *
          (C (algebraMap O (KK O) (dW O w LL r l' b')) * X (l', b')) *
          C (∑ a : Fin k, sigMat p f O g⁻¹ (LL.pos l) b a * sigMat p f O g (LL.pos l') a b') := by
        simp only [Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b' _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_mul]
        ring
    _ = ∑ b : Fin k, C (algebraMap O (KK O) (dW O w LL r l b)) * X (l, b) *
          (C (algebraMap O (KK O) (dW O w LL r l' b)) * X (l', b)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [hinv]
        rw [Finset.sum_eq_single b]
        · simp
        · intro b' _ hne
          rw [if_neg (Ne.symm hne)]
          simp
        · intro h; exact absurd (Finset.mem_univ b) h
    _ = C (algebraMap O (KK O) w) * ∑ a : Fin k, X (l, a) * X (l', a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        have hC : (C (algebraMap O (KK O) w) : MvPolynomial (ι × Fin k) (KK O)) =
            C (algebraMap O (KK O) (dW O w LL r l b)) * C (algebraMap O (KK O) (dW O w LL r l' b)) := by
          rw [← map_mul, ← map_mul, hd b]
        rw [hC]
        ring

theorem hook_key_order_ge_one (w : O) (LL : LiftLetters ι) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p f)) (hg : IsGLW g) (l l' : ι)
    (hl : LL.vec l = true) (hl' : LL.vec l' = false) (hpos : LL.pos l = LL.pos l') :
    InWjRg p f O w r LL g (hKey O k l l') 1 := by
  classical
  unfold InWjRg
  rw [hook_key_lift_exact w LL r g hg l l' hl hl' hpos, C_mul_eq_smul]
  have h0 : InWj w (hKey O k l l') 0 := by
    unfold hKey
    refine (wjSub w 0).sum_mem fun a _ => ?_
    have hX : ∀ v : ι × Fin k, InWj w (X v : MvPolynomial (ι × Fin k) (KK O)) 0 := by
      intro v m
      rw [coeff_X]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    exact inWj_mul (hX _) (hX _)
  have := wj_smul_pow h0 1
  rwa [pow_one, zero_add] at this

end Rg

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

def topStart (X : Loc) (j : Fin (numSeg X.TT)) : X.TT := ⟨segStart X.TT j, (start_mem X.TT j).1⟩

abbrev RHH (O : Type) [CommRing O] [IsDomain O] (X : Loc) := MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)

def kSkey (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : RHH O X :=
  ∑ a : Fin (X.m + 1), MvPolynomial.X ((topStart X j, true), a) ^ (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), a)

def kWkey (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (c : Fin (X.m + 1)) : RHH O X :=
  MvPolynomial.X ((topOdd X j i, true), c) * MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) -
    MvPolynomial.X ((topOdd X j i, true), 0) * MvPolynomial.X ((topStart X j, true), c) ^ (X.p ^ (segDists X.TT j).get i)

def locC (O : Type) [CommRing O] [IsDomain O] (X : Loc) (c : Fin (X.m + 1)) : RHH O X :=
  ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j - 1) -
    ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), c) ^ (X.p ^ segG X.TT j - 1)

def locR (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j0 : Fin (numSeg X.TT)) : RHH O X :=
  MvPolynomial.X ((topStart X j0, true), 0) * ∏ c : Fin X.m, locC O X c.succ

def CoarseMultiplicityBoundAtIdentity : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X →
    ∀ (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)),
      (∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
        InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) 1 ∧
        ∀ c : Fin X.m, InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c.succ) 1) ∧
      liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) 1 (kSkey O X j i) =
        S.w • (MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), 0) +
          S.w ^ (X.p ^ (segDists X.TT j).get i - 1) • (∑ c : Fin X.m,
            MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) *
              MvPolynomial.X ((topOdd X j i, false), c.succ) : RHH O X) : RHH O X) ∧
      ∀ c : Fin X.m, liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) 1 (kWkey O X j i c.succ) =
        S.w • (MvPolynomial.X ((topOdd X j i, true), c.succ) * MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) -
          S.w ^ (X.p ^ (segDists X.TT j).get i - 1) •
            (MvPolynomial.X ((topOdd X j i, true), 0) *
              MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) : RHH O X) : RHH O X)

def LocalBoundAtIdentity : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    (∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (locR O X j0) 1) ∧
    ∀ c : Fin X.m, liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) 1 (locC O X c.succ) =
      ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j - 1) -
        S.w ^ (∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1)) •
          (∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ segG X.TT j - 1) : RHH O X)

def AsmRTAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  CoarseMultiplicityBoundAtIdentity → LocalBoundAtIdentity → RawTailAt1 C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def RestAsmRT : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => AsmRTAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restRawTail1_of (h3 : CoarseMultiplicityBoundAtIdentity) (h4 : LocalBoundAtIdentity) (hA : RestAsmRT) : RestRawTail1 :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => h h3 h4) hA

section Fac

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

structure IsFac (w : O) (f : RHH O X) (o : ℕ) (sg : RHH O X) : Prop where
  inA : InA f
  ord : ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
    InWjRg X.p X.n' O w 1 (hhLetters X.TT) g f o
  sym : InWj w (liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f - (w ^ o) • sg) (o + 1)
  sgInt : InA sg

theorem isGLW_one' (k : ℕ) : IsGLW (1 : Matrix (Fin k) (Fin k) (WF X.p X.n')) := by
  unfold IsGLW
  rw [Matrix.det_one]
  exact isUnit_one

theorem IsFac.mul {w : O} {f f' sg sg' : RHH O X} {o o' : ℕ} (h : IsFac w f o sg) (h' : IsFac w f' o' sg') :
    IsFac w (f * f') (o + o') (sg * sg') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (inA_iff_wj w).2 (inWj_mul ((inA_iff_wj w).1 h.inA) ((inA_iff_wj w).1 h'.inA))
  · exact fun g hg => inWjRg_mul (h.ord g hg) (h'.ord g hg)
  · have e : liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (f * f') - (w ^ (o + o')) • (sg * sg') =
        (liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f - (w ^ o) • sg) *
            liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f' +
          ((w ^ o) • sg) * (liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f' - (w ^ o') • sg') := by
      rw [map_mul, pow_add, mul_smul_mul_comm]
      ring
    rw [e]
    have a1 := inWj_mul h.sym (h'.ord 1 (isGLW_one' _))
    have a2 := inWj_mul (wj_smul_pow ((inA_iff_wj w).1 h.sgInt) o) h'.sym
    have e1 : o + 1 + o' = o + o' + 1 := by ring
    have e2 : 0 + o + (o' + 1) = o + o' + 1 := by ring
    rw [e1] at a1
    rw [e2] at a2
    exact (wjSub w (o + o' + 1)).add_mem a1 a2
  · exact (inA_iff_wj w).2 (inWj_mul ((inA_iff_wj w).1 h.sgInt) ((inA_iff_wj w).1 h'.sgInt))

end Fac

end Formalism.MainNotions.ColumnSystems.Pf
