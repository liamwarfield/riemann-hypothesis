module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.MultidegAdd
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PsiRes0Ne

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IdentityLiftWeightedHomog
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

abbrev VarH (X : Loc) := (X.TT × Bool) × Fin (X.m + 1)

def wN (X : Loc) : VarH X → ℕ := fun v =>
  if (v.1.2 = true ∧ 1 ≤ v.2.val) ∨ (v.1.2 = false ∧ v.2.val < 1) then 1 else 0

def dX {X : Loc} (x l : X.TT × Bool) : ℕ := if x = l then 1 else 0

def wL (X : Loc) (l : X.TT × Bool) : VarH X → ℕ := fun v => dX v.1 l

section Grad

variable {X : Loc}

theorem wN_pos {v : VarH X} (h : (v.1.2 = true ∧ 1 ≤ v.2.val) ∨ (v.1.2 = false ∧ v.2.val < 1)) : wN X v = 1 := if_pos h

theorem wN_neg {v : VarH X} (h : ¬ ((v.1.2 = true ∧ 1 ≤ v.2.val) ∨ (v.1.2 = false ∧ v.2.val < 1))) : wN X v = 0 := if_neg h

theorem ndM_eq (m : MonH X) : ndM X m = Finsupp.weight (wN X) m := by
  classical
  unfold ndM degUS
  rw [Finsupp.weight_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : (v.1.2 = true ∧ 1 ≤ v.2.val) ∨ (v.1.2 = false ∧ v.2.val < 1)
  · have h' : ((hhLetters X.TT).vec v.1 = true ∧ 1 ≤ v.2.val) ∨ ((hhLetters X.TT).vec v.1 = false ∧ v.2.val < 1) := h
    rw [if_pos h', wN_pos h, smul_eq_mul, mul_one]
  · have h' : ¬ (((hhLetters X.TT).vec v.1 = true ∧ 1 ≤ v.2.val) ∨ ((hhLetters X.TT).vec v.1 = false ∧ v.2.val < 1)) := h
    rw [if_neg h', wN_neg h, smul_eq_mul, mul_zero]

theorem multideg_eq (m : MonH X) (l : X.TT × Bool) : multideg m l = Finsupp.weight (wL X l) m := by
  classical
  unfold multideg
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Fintype.sum_prod_type,
    Finset.sum_eq_single l]
  · simp [wL, dX]
  · intro b _ hb
    simp [wL, dX, hb]
  · intro h; exact absurd (Finset.mem_univ l) h

variable {K : Type} [CommRing K]

theorem mem_Pol_iff {d : X.TT × Bool → ℕ} {P : MvPolynomial (VarH X) K} :
    P ∈ Pol K (ι := X.TT × Bool) (X.m + 1) d ↔ ∀ l, IsWeightedHomogeneous (wL X l) P (d l) := by
  unfold Pol
  rw [MvPolynomial.mem_restrictSupport_iff]
  constructor
  · intro h l m hm
    rw [← multideg_eq]
    exact h (Finset.mem_coe.2 (MvPolynomial.mem_support_iff.2 hm)) l
  · intro h m hm l
    rw [multideg_eq]
    exact h l (MvPolynomial.mem_support_iff.1 (Finset.mem_coe.1 hm))

theorem ndHom_iff {o : ℕ} {P : MvPolynomial (VarH X) K} :
    (∀ m ∈ P.support, ndM X m = o) ↔ IsWeightedHomogeneous (wN X) P o := by
  constructor
  · intro h m hm
    rw [← ndM_eq]
    exact h m (MvPolynomial.mem_support_iff.2 hm)
  · intro h m hm
    rw [ndM_eq]
    exact h (MvPolynomial.mem_support_iff.1 hm)

end Grad

section Int

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}

theorem X_int (v : σ) : (MvPolynomial.X v : MvPolynomial σ (KK O)) ∈ intSub O σ := X_mem_goodSub v rfl

end Int

section Lift

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O]

theorem identity_lift_X (w : O) (v : VarH X) :
    lift1 X O w (MvPolynomial.X v) = (w ^ wN X v) • (MvPolynomial.X v : RHH O X) := by
  obtain ⟨x, b⟩ := v
  show liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (MvPolynomial.X (x, b)) = _
  rw [liftSubst_one_hh]
  by_cases h : (x.2 = true ∧ 1 ≤ (b : ℕ)) ∨ (x.2 = false ∧ (b : ℕ) < 1)
  · rw [if_pos h, C_mul_eq_smul, wN_pos (v := (x, b)) h, pow_one]
  · rw [if_neg h, wN_neg (v := (x, b)) h, pow_zero, one_smul]

theorem identity_lift_monomial (w : O) (M : MonH X) :
    lift1 X O w (monomial M 1) = (w ^ ndM X M) • (monomial M 1 : RHH O X) := by
  classical
  induction M using Finsupp.induction_linear with
  | zero =>
    have : ndM X (0 : MonH X) = 0 := degUS_zero _ _
    rw [this]
    simp
  | add f g hf hg =>
    have e : (monomial (f + g) 1 : RHH O X) = monomial f 1 * monomial g 1 := by
      rw [monomial_mul, one_mul]
    rw [e, map_mul, hf, hg, ndM_add, pow_add, smul_mul_smul_comm]
  | single a b =>
    have e : (monomial (Finsupp.single a b) 1 : RHH O X) = MvPolynomial.X a ^ b := (X_pow_eq_monomial).symm
    have hn : ndM X (Finsupp.single a b) = b * wN X a := by
      rw [ndM_eq, Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]
      simp
    rw [e, map_pow, identity_lift_X, smul_pow, hn, ← pow_mul, mul_comm]

theorem identity_lift_eq_sum (w : O) (P : RHH O X) :
    lift1 X O w P = ∑ m ∈ P.support, monomial m (algebraMap O (KK O) (w ^ ndM X m) * P.coeff m) := by
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff P]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : (monomial m (P.coeff m) : RHH O X) = C (P.coeff m) * monomial m 1 := by
    rw [C_mul_monomial, mul_one]
  rw [e, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, identity_lift_monomial, ← C_mul_eq_smul, C_mul_monomial,
    C_mul_monomial, mul_one, mul_comm]

theorem identity_lift_weighted_homog (w : O) {wt : VarH X → ℕ} {n : ℕ} {P : RHH O X} (h : IsWeightedHomogeneous wt P n) :
    IsWeightedHomogeneous wt (lift1 X O w P) n := by
  rw [identity_lift_eq_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  exact isWeightedHomogeneous_monomial wt m _ (h (MvPolynomial.mem_support_iff.1 hm))

theorem identity_lift_mem_Pol (w : O) {d : X.TT × Bool → ℕ} {P : RHH O X}
    (h : P ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) d) :
    lift1 X O w P ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) d :=
  mem_Pol_iff.2 fun l => identity_lift_weighted_homog w (mem_Pol_iff.1 h l)

theorem identity_lift_normal_homog (w : O) {o : ℕ} {P : RHH O X} (h : IsWeightedHomogeneous (wN X) P o) :
    lift1 X O w P = (w ^ o) • P := by
  rw [identity_lift_eq_sum]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff P]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [ndM_eq, h (MvPolynomial.mem_support_iff.1 hm), ← C_mul_eq_smul, C_mul_monomial]

end Lift

section FacCalc

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

theorem inWjRg_zero_of_inA (w : O) {f : RHH O X} (hf : InA f)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) :
    InWjRg X.p X.n' O w 1 (hhLetters X.TT) g f 0 := by
  intro m
  obtain ⟨a, ha⟩ := lift_substitution_coeff_divisible X.p X.n' O w (hhLetters X.TT) 1 g hg f hf m
  exact ⟨w ^ degUS (hhLetters X.TT) 1 m * a, by rw [ha, pow_zero, one_mul]⟩

theorem IsFac.one (w : O) : IsFac (X := X) w (1 : RHH O X) 0 1 := by
  have hInt : InA (1 : RHH O X) := (inA_iff_wj w).2 (inWj_one w)
  refine ⟨hInt, ?_, ?_, hInt⟩
  · intro g _
    unfold InWjRg
    rw [map_one]
    exact inWj_one w
  · rw [map_one, pow_zero, one_smul, sub_self]
    exact (wjSub w _).zero_mem

theorem IsFac.pow {w : O} {f sg : RHH O X} {o : ℕ} (h : IsFac w f o sg) (u : ℕ) : IsFac w (f ^ u) (u * o) (sg ^ u) := by
  induction u with
  | zero => simpa using IsFac.one (X := X) w
  | succ u ih =>
    have := ih.mul h
    rw [pow_succ, pow_succ]
    have e : u * o + o = (u + 1) * o := by ring
    rwa [e] at this

theorem IsFac.congr_sg {w : O} {f sg sg' : RHH O X} {o : ℕ} (h : IsFac w f o sg) (h' : InWj w (sg - sg') 1)
    (hi : InA sg') : IsFac w f o sg' := by
  refine ⟨h.inA, h.ord, ?_, hi⟩
  have e : liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f - (w ^ o) • sg' =
      (liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f - (w ^ o) • sg) + (w ^ o) • (sg - sg') := by
    rw [smul_sub]; abel
  rw [e]
  have := wj_smul_pow h' o
  rw [add_comm 1 o] at this
  exact (wjSub w (o + 1)).add_mem h.sym this

theorem IsFac.of_exact {w : O} {f sg r : RHH O X} {o e : ℕ} (hA : InA f)
    (hord : ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
      InWjRg X.p X.n' O w 1 (hhLetters X.TT) g f o)
    (he : 1 ≤ e) (hs : InA sg) (hr : InA r)
    (hl : liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f = (w ^ o) • (sg + (w ^ e) • r)) : IsFac w f o sg := by
  refine ⟨hA, hord, ?_, hs⟩
  rw [hl, smul_add, add_sub_cancel_left, smul_smul, ← pow_add]
  have := wj_smul_pow ((inA_iff_wj w).1 hr) (o + e)
  rw [zero_add] at this
  exact wj_mono (by omega) this

end FacCalc

structure SoftOK {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (w : O) (f : RHH O X) (od : ℕ) (sg : RHH O X) (dg : X.TT × Bool → ℕ) : Prop where
  fac : IsFac w f od sg
  sgHom : ∀ m ∈ sg.support, ndM X m = od
  liftPol : lift1 X O w f ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) dg
  sgPol : sg ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) dg

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.NormalWeightCovectorZero
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

section Wts

variable {X : Loc}

theorem normal_weight_vector_zero_eq_zero (x : X.TT) : wN X ((x, true), 0) = 0 := by
  simp [wN]
theorem wN_vecS (x : X.TT) (c : Fin X.m) : wN X ((x, true), c.succ) = 1 := by
  simp [wN, Fin.val_succ]
theorem normal_weight_covector_zero (x : X.TT) : wN X ((x, false), 0) = 1 := by
  simp [wN]
theorem wN_covS (x : X.TT) (c : Fin X.m) : wN X ((x, false), c.succ) = 0 := by
  simp [wN, Fin.val_succ]

theorem wN_pair (x : X.TT) (a : Fin (X.m + 1)) : wN X ((x, true), a) + wN X ((x, false), a) = 1 := by
  unfold wN
  split_ifs <;> simp_all <;> omega

variable {K : Type} [CommRing K] {σ : Type}

theorem wh_powX (wt : σ → ℕ) (v1 v2 : σ) (a : ℕ) :
    IsWeightedHomogeneous wt ((MvPolynomial.X v1 : MvPolynomial σ K) ^ a * MvPolynomial.X v2) (a * wt v1 + wt v2) := by
  exact ((isWeightedHomogeneous_X K wt v1).pow a).mul (isWeightedHomogeneous_X K wt v2)

theorem wh_Xpow (wt : σ → ℕ) (v1 v2 : σ) (a : ℕ) :
    IsWeightedHomogeneous wt ((MvPolynomial.X v1 : MvPolynomial σ K) * MvPolynomial.X v2 ^ a) (wt v1 + a * wt v2) := by
  exact (isWeightedHomogeneous_X K wt v1).mul ((isWeightedHomogeneous_X K wt v2).pow a)

theorem wh_sub {wt : σ → ℕ} {n : ℕ} {P Q : MvPolynomial σ K} (hP : IsWeightedHomogeneous wt P n)
    (hQ : IsWeightedHomogeneous wt Q n) : IsWeightedHomogeneous wt (P - Q) n := by
  intro d hd
  rw [coeff_sub] at hd
  by_cases h : AddMonoidAlgebra.coeff P d = 0
  · rw [h, zero_sub, neg_ne_zero] at hd
    exact hQ hd
  · exact hP h

end Wts

section Soft

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

theorem SoftOK.pow {w : O} {f sg : RHH O X} {od : ℕ} {dg : X.TT × Bool → ℕ} (h : SoftOK w f od sg dg) (u : ℕ) :
    SoftOK w (f ^ u) (u * od) (sg ^ u) (fun l => u * dg l) :=
  { fac := h.fac.pow u
    sgHom := ndHom_iff.2 (by simpa [smul_eq_mul] using (ndHom_iff.1 h.sgHom).pow u)
    liftPol := mem_Pol_iff.2 fun l => by
      rw [map_pow]
      simpa [smul_eq_mul] using (mem_Pol_iff.1 h.liftPol l).pow u
    sgPol := mem_Pol_iff.2 fun l => by simpa [smul_eq_mul] using (mem_Pol_iff.1 h.sgPol l).pow u }

def sgKS (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : RHH O X :=
  MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), 0)

def dgKS (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : X.TT × Bool → ℕ := fun l =>
  X.p ^ (segDists X.TT j).get i * dX (topStart X j, true) l + dX (topOdd X j i, false) l

theorem two_le_pd (hD : D1num X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    1 ≤ X.p ^ (segDists X.TT j).get i - 1 := by
  have hp5 : 5 ≤ X.p := hD.2.1
  have key : ∀ d ∈ segDists X.TT j, 0 < d := by
    intro d hd
    unfold segDists at hd
    simp only [Finset.mem_sort, Finset.mem_image, Finset.mem_filter] at hd
    obtain ⟨s, hs, rfl⟩ := hd
    exact hs.2.2.1
  have hpos := key _ (List.get_mem _ i)
  have : X.p ≤ X.p ^ (segDists X.TT j).get i := Nat.le_self_pow hpos.ne' X.p
  omega

theorem kS_pol (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    kSkey O X j i ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgKS X j i) := by
  rw [mem_Pol_iff]
  intro l
  unfold kSkey
  refine IsWeightedHomogeneous.sum _ _ _ (fun a _ => ?_)
  exact wh_powX (K := KK O) (wL X l) ((topStart X j, true), a) ((topOdd X j i, false), a)
    (X.p ^ (segDists X.TT j).get i)

theorem kS_inA (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : InA (kSkey O X j i) := by
  intro m
  refine ⟨(∑ a : Fin (X.m + 1), (MvPolynomial.X ((topStart X j, true), a) : MvPolynomial (VarH X) O) ^
    (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), a)).coeff m, ?_⟩
  rw [← MvPolynomial.coeff_map]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp [kSkey, map_sum, map_mul, map_pow, map_X]

theorem softKS (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    SoftOK S.w (kSkey O X j i) 1 (sgKS O X j i) (dgKS X j i) :=
  { fac := by
      refine IsFac.of_exact (e := X.p ^ (segDists X.TT j).get i - 1)
        (r := ∑ c : Fin X.m, MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) *
          MvPolynomial.X ((topOdd X j i, false), c.succ)) (kS_inA j i)
        (fun g hg => (key3Ord X O S hS hD j i g hg).1) (two_le_pd hD j i) ?_ ?_ ?_
      · exact (mem_intSub O _).1 (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (X_int _) _) (X_int _))
      · exact (mem_intSub O _).1 (Subalgebra.sum_mem _ fun a _ =>
          Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (X_int _) _) (X_int _))
      · rw [key3One_S, pow_one]; rfl
    sgHom := ndHom_iff.2 (by
      have := wh_powX (K := KK O) (wN X) ((topStart X j, true), 0) ((topOdd X j i, false), 0)
        (X.p ^ (segDists X.TT j).get i)
      rwa [normal_weight_vector_zero_eq_zero, normal_weight_covector_zero, mul_zero, zero_add] at this)
    liftPol := identity_lift_mem_Pol _ (kS_pol j i)
    sgPol := mem_Pol_iff.2 fun l => wh_powX (wL X l) _ _ _ }

theorem softKSP (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (P : ℕ) : SoftOK S.w (kSkey O X j i ^ P) P (sgKS O X j i ^ P) (fun l => P * dgKS X j i l) := by
  have h := (softKS S hS hD j i).pow P
  rwa [mul_one] at h

def sgKW (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (c : Fin X.m) :
    RHH O X :=
  MvPolynomial.X ((topOdd X j i, true), c.succ) * MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i)

def dgKW (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : X.TT × Bool → ℕ := fun l =>
  dX (topOdd X j i, true) l + X.p ^ (segDists X.TT j).get i * dX (topStart X j, true) l

theorem kW_pol (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (c : Fin (X.m + 1)) :
    kWkey O X j i c ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgKW X j i) := by
  rw [mem_Pol_iff]
  intro l
  unfold kWkey
  exact wh_sub (wh_Xpow (K := KK O) (wL X l) _ _ _) (wh_Xpow (K := KK O) (wL X l) _ _ _)

theorem kW_inA (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (c : Fin (X.m + 1)) : InA (kWkey O X j i c) := by
  intro m
  refine ⟨((MvPolynomial.X ((topOdd X j i, true), c) : MvPolynomial (VarH X) O) *
      MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) -
    MvPolynomial.X ((topOdd X j i, true), 0) *
      MvPolynomial.X ((topStart X j, true), c) ^ (X.p ^ (segDists X.TT j).get i)).coeff m, ?_⟩
  rw [← MvPolynomial.coeff_map]
  congr 1
  simp [kWkey, map_sub, map_mul, map_pow, map_X]

theorem softKW (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (c : Fin X.m) : SoftOK S.w (kWkey O X j i c.succ) 1 (sgKW O X j i c) (dgKW X j i) :=
  { fac := by
      refine IsFac.of_exact (e := X.p ^ (segDists X.TT j).get i - 1)
        (r := -(MvPolynomial.X ((topOdd X j i, true), 0) *
          MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i))) (kW_inA j i _)
        (fun g hg => (key3Ord X O S hS hD j i g hg).2 c) (two_le_pd hD j i) ?_ ?_ ?_
      · exact (mem_intSub O _).1 (Subalgebra.mul_mem _ (X_int _) (Subalgebra.pow_mem _ (X_int _) _))
      · exact (mem_intSub O _).1 (Subalgebra.neg_mem _ (Subalgebra.mul_mem _ (X_int _) (Subalgebra.pow_mem _ (X_int _) _)))
      · rw [key_lift_identity_lower, pow_one, smul_neg, ← sub_eq_add_neg]; rfl
    sgHom := ndHom_iff.2 (by
      have := wh_Xpow (K := KK O) (wN X) ((topOdd X j i, true), c.succ) ((topStart X j, true), 0)
        (X.p ^ (segDists X.TT j).get i)
      rwa [normal_weight_vector_zero_eq_zero, wN_vecS, mul_zero, add_zero] at this)
    liftPol := identity_lift_mem_Pol _ (kW_pol j i _)
    sgPol := mem_Pol_iff.2 fun l => wh_Xpow (wL X l) _ _ _ }

def sgLoc (O : Type) [CommRing O] [IsDomain O] (X : Loc) : RHH O X :=
  ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j - 1)

def dgLoc (X : Loc) : X.TT × Bool → ℕ := fun l =>
  ∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1) * dX (topStart X j, true) l

theorem wh_prodStart (wt : VarH X → ℕ) (c : Fin (X.m + 1)) :
    IsWeightedHomogeneous wt
      (∏ j : Fin (numSeg X.TT), (MvPolynomial.X ((topStart X j, true), c) : RHH O X) ^ (X.p ^ segG X.TT j - 1))
      (∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1) * wt ((topStart X j, true), c)) := by
  refine IsWeightedHomogeneous.prod _ _ _ (fun j _ => ?_)
  exact (isWeightedHomogeneous_X (KK O) wt ((topStart X j, true), c)).pow _

theorem loc_pol (c : Fin (X.m + 1)) : locC O X c ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgLoc X) := by
  rw [mem_Pol_iff]
  intro l
  unfold locC
  exact wh_sub (wh_prodStart (O := O) (wL X l) 0) (wh_prodStart (O := O) (wL X l) c)

theorem prodStart_int (c : Fin (X.m + 1)) :
    (∏ j : Fin (numSeg X.TT), (MvPolynomial.X ((topStart X j, true), c) : RHH O X) ^ (X.p ^ segG X.TT j - 1)) ∈
      intSub O (VarH X) := by
  have hX : ∀ v : VarH X, (MvPolynomial.X v : RHH O X) ∈ intSub O (VarH X) := by
    intro v m
    refine ⟨if Finsupp.single v 1 = m then 1 else 0, ?_⟩
    rw [MvPolynomial.coeff_X]
    split_ifs <;> simp
  exact Subalgebra.prod_mem _ fun j _ => Subalgebra.pow_mem _ (hX _) _

theorem loc_inA (c : Fin (X.m + 1)) : InA (locC O X c) := by
  intro m
  refine ⟨((∏ j : Fin (numSeg X.TT), (MvPolynomial.X ((topStart X j, true), 0) : MvPolynomial (VarH X) O) ^
      (X.p ^ segG X.TT j - 1)) -
    ∏ j : Fin (numSeg X.TT), (MvPolynomial.X ((topStart X j, true), c) : MvPolynomial (VarH X) O) ^
      (X.p ^ segG X.TT j - 1)).coeff m, ?_⟩
  rw [← MvPolynomial.coeff_map]
  congr 1
  simp [locC, map_sub, map_prod, map_pow, map_X]

theorem one_le_Mp (hD : D1num X) (h2 : 2 ≤ numSeg X.TT) : 1 ≤ ∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1) := by
  have hn' : 2 ≤ X.n' := hD.2.2.1
  have hp5 : 5 ≤ X.p := hD.2.1
  have hj : ∀ j, 1 ≤ X.p ^ segG X.TT j - 1 := by
    intro j
    have hg : 1 ≤ segG X.TT j := by
      unfold segG
      split_ifs with h
      · omega
      · omega
    have : X.p ≤ X.p ^ segG X.TT j := Nat.le_self_pow (by omega) X.p
    omega
  have j0 : Fin (numSeg X.TT) := ⟨0, by omega⟩
  calc 1 ≤ X.p ^ segG X.TT j0 - 1 := hj j0
    _ ≤ ∑ j, (X.p ^ segG X.TT j - 1) :=
      Finset.single_le_sum (f := fun j => X.p ^ segG X.TT j - 1) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ j0)

theorem softLoc (w : O) (hD : D1num X) (h2 : 2 ≤ numSeg X.TT) (c : Fin X.m) :
    SoftOK w (locC O X c.succ) 0 (sgLoc O X) (dgLoc X) :=
  { fac := by
      refine IsFac.of_exact (e := ∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1))
        (r := -(∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ segG X.TT j - 1)))
        (loc_inA _) (fun g hg => inWjRg_zero_of_inA w (loc_inA _) g hg) (one_le_Mp hD h2) ?_ ?_ ?_
      · exact (mem_intSub O _).1 (prodStart_int 0)
      · exact (mem_intSub O _).1 (Subalgebra.neg_mem _ (prodStart_int _))
      · rw [loc4One, pow_zero, one_smul, smul_neg, ← sub_eq_add_neg]; rfl
    sgHom := ndHom_iff.2 (by
      have := wh_prodStart (O := O) (wN X) 0
      simp only [normal_weight_vector_zero_eq_zero, mul_zero, Finset.sum_const_zero] at this
      exact this)
    liftPol := identity_lift_mem_Pol _ (loc_pol _)
    sgPol := mem_Pol_iff.2 fun l => wh_prodStart (wL X l) 0 }

theorem locPow_ord (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (h2 : 2 ≤ numSeg X.TT) (j0 : Fin (numSeg X.TT))
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g)
    (hne : ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1) (n : ℕ) :
    InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (locR O X j0 ^ n) n := by
  have := inWjRg_pow (loc4Ord_of (loc4Div_of loc4Res) X O S hS hD h2 j0 g hg hne) n
  rwa [mul_one] at this

end Soft

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TopKeyFormSelfSoft
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

section H

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

def hTop (O : Type) [CommRing O] [IsDomain O] (X : Loc) (x : X.TT) : RHH O X := hKey O (X.m + 1) (x, true) (x, false)

def dgH {X : Loc} (x : X.TT) : X.TT × Bool → ℕ := fun l => dX (x, true) l + dX (x, false) l

def EhatT (O : Type) [CommRing O] [IsDomain O] (X : Loc) (x : X.TT) (P : ℕ) : RHH O X :=
  MvPolynomial.X ((x, true), 0) ^ P * MvPolynomial.X ((x, false), 0) ^ P +
    ∑ c : Fin X.m, MvPolynomial.X ((x, true), c.succ) ^ P * MvPolynomial.X ((x, false), c.succ) ^ P

theorem hTop_eq (x : X.TT) : hTop O X x = MvPolynomial.X ((x, true), 0) * MvPolynomial.X ((x, false), 0) +
    ∑ c : Fin X.m, MvPolynomial.X ((x, true), c.succ) * MvPolynomial.X ((x, false), c.succ) := by
  rw [hTop, hKey, Fin.sum_univ_succ]

theorem EhatT_one (x : X.TT) : EhatT O X x 1 = hTop O X x := by
  rw [EhatT, hTop_eq]
  simp only [pow_one]

private theorem X_true_mul_X_false_pow_mem_Pol (x : X.TT) (a : Fin (X.m + 1)) (P : ℕ) :
    (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ P ∈
      Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (fun l => P * dgH x l) := by
  classical
  rw [show (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ P =
      monomial (P • (Finsupp.single ((x, true), a) 1 + Finsupp.single ((x, false), a) 1)) 1 by
    rw [MvPolynomial.X, MvPolynomial.X, monomial_mul, monomial_pow, one_mul, one_pow]]
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm' := support_monomial_subset hm
  rw [Finset.mem_singleton] at hm'
  subst hm'
  intro l
  simp only [multideg, dgH, dX, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq,
    smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
  congr 1 <;> split_ifs with h <;> simp [h]

theorem hTop_pol (x : X.TT) : hTop O X x ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgH x) := by
  have e : hTop O X x = ∑ a : Fin (X.m + 1),
      (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ 1 := by
    rw [hTop_eq, Fin.sum_univ_succ]
    simp only [pow_one]
  rw [e]
  refine Submodule.sum_mem _ (fun a _ => ?_)
  have h := X_true_mul_X_false_pow_mem_Pol (O := O) x a 1
  simp only [one_mul] at h
  exact h

theorem hTop_nd (x : X.TT) : IsWeightedHomogeneous (wN X) (hTop O X x) 1 := by
  rw [hTop_eq]
  have hpair : ∀ a : Fin (X.m + 1), IsWeightedHomogeneous (wN X)
      (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) 1 := by
    intro a
    have h1 := (isWeightedHomogeneous_X (KK O) (wN X) ((x, true), a)).mul
      (isWeightedHomogeneous_X (KK O) (wN X) ((x, false), a))
    have hw : wN X ((x, true), a) + wN X ((x, false), a) = 1 := by
      rcases Nat.lt_or_ge a.val 1 with h | h
      · have h' : ¬ 1 ≤ a.val := by omega
        simp [wN, h, h']
      · have h' : ¬ a.val < 1 := by omega
        simp [wN, h, h']
    rwa [hw] at h1
  refine (hpair 0).add (IsWeightedHomogeneous.sum _ _ _ (fun c _ => hpair c.succ))

private theorem X_mem_intSub' (v : VarH X) : (MvPolynomial.X v : RHH O X) ∈ intSub O (VarH X) := by
  classical
  change ∀ m, ∃ a : O, (MvPolynomial.X v : RHH O X).coeff m = algebraMap O (KK O) ((1 : O) ^ (0 : ℕ) * a)
  intro m
  rw [MvPolynomial.coeff_X']
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem hTop_int (x : X.TT) : hTop O X x ∈ intSub O (VarH X) := by
  rw [hTop_eq]
  exact add_mem (mul_mem (X_mem_intSub' _) (X_mem_intSub' _))
    (sum_mem fun c _ => mul_mem (X_mem_intSub' _) (X_mem_intSub' _))

theorem hTop_inA (x : X.TT) : InA (hTop O X x) := by
  have h := hTop_int (O := O) x
  change ∀ m, ∃ a : O, (hTop O X x).coeff m = algebraMap O (KK O) ((1 : O) ^ (0 : ℕ) * a) at h
  intro m
  obtain ⟨a, ha⟩ := h m
  exact ⟨a, by rw [ha, pow_zero, one_mul]⟩

theorem hTop_lift (w : O) (x : X.TT) : lift1 X O w (hTop O X x) = w • hTop O X x := by
  rw [identity_lift_normal_homog w (hTop_nd x), pow_one]

theorem hTop_ord (w : O) (x : X.TT) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) :
    InWjRg X.p X.n' O w 1 (hhLetters X.TT) g (hTop O X x) 1 := by
  exact hook_key_order_ge_one w (hhLetters X.TT) 1 g hg (x, true) (x, false) rfl rfl rfl

theorem softOK_hTop (w : O) (x : X.TT) : SoftOK w (hTop O X x) 1 (hTop O X x) (dgH x) := by
  exact
    { fac := IsFac.of_exact (e := 1) (r := 0) (hTop_inA x) (fun g hg => hTop_ord w x g hg) le_rfl (hTop_inA x)
        ((inA_iff_wj w).2 (wjSub w 0).zero_mem) (by
          have := hTop_lift w x
          rw [smul_zero, add_zero, pow_one]
          exact this)
      sgHom := ndHom_iff.2 (hTop_nd x)
      liftPol := identity_lift_mem_Pol _ (hTop_pol x)
      sgPol := hTop_pol x }

theorem EhatT_eq_sum (x : X.TT) (P : ℕ) :
    EhatT O X x P = ∑ a : Fin (X.m + 1), (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a) : RHH O X) ^ P := by
  rw [EhatT, Fin.sum_univ_succ]
  simp only [mul_pow]

theorem EhatT_int (x : X.TT) (P : ℕ) : EhatT O X x P ∈ intSub O (VarH X) := by
  rw [EhatT_eq_sum]
  exact sum_mem fun a _ => pow_mem (mul_mem (X_mem_intSub' _) (X_mem_intSub' _)) _

theorem EhatT_wh (wt : VarH X → ℕ) (n : ℕ) (x : X.TT) (P : ℕ) (h : ∀ a, wt ((x, true), a) + wt ((x, false), a) = n) :
    IsWeightedHomogeneous wt (EhatT O X x P) (P * n) := by
  rw [EhatT_eq_sum]
  refine IsWeightedHomogeneous.sum _ _ _ (fun a _ => ?_)
  have h1 := ((isWeightedHomogeneous_X (KK O) wt ((x, true), a)).mul
    (isWeightedHomogeneous_X (KK O) wt ((x, false), a))).pow P
  rwa [h a, smul_eq_mul] at h1

theorem hpow_congr (S : UniformizedDVR X.p O) (hS : S.SqP) (x : X.TT) (e : ℕ) :
    InWj S.w (hTop O X x ^ (X.p ^ e) - EhatT O X x (X.p ^ e)) 1 := by
  classical
  set D : MvPolynomial (VarH X) O :=
    (∑ a : Fin (X.m + 1), MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a)) ^ (X.p ^ e) -
      ∑ a : Fin (X.m + 1), (MvPolynomial.X ((x, true), a) * MvPolynomial.X ((x, false), a)) ^ (X.p ^ e) with hDdef
  have hD : hTop O X x ^ (X.p ^ e) - EhatT O X x (X.p ^ e) = MvPolynomial.map (algebraMap O (KK O)) D := by
    rw [EhatT_eq_sum, ← EhatT_one, EhatT_eq_sum, hDdef]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_pow, map_sum, map_mul, map_X, pow_one]
  rw [hD]
  apply Formalism.MainNotions.G.WittFrameLocaliserOrders.residue_zero_mem_order_one S
  have hp0 : ((X.p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact S.p_mem
  haveI : CharP (IsLocalRing.ResidueField O) X.p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hp0
  rw [hDdef]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_pow, map_sum, map_mul, map_X]
  rw [sum_pow_char_pow, sub_self]

theorem softH (S : UniformizedDVR X.p O) (hS : S.SqP) (x : X.TT) (e : ℕ) :
    SoftOK S.w (hTop O X x ^ (X.p ^ e)) (X.p ^ e) (EhatT O X x (X.p ^ e)) (fun l => X.p ^ e * dgH x l) := by
  exact
    { fac := by
        have := ((softOK_hTop S.w x).pow (X.p ^ e)).fac
        rw [mul_one] at this
        exact this.congr_sg (hpow_congr S hS x e) ((mem_intSub O _).1 (EhatT_int x _))
      sgHom := ndHom_iff.2 (by
        have := EhatT_wh (O := O) (wN X) 1 x (X.p ^ e) (wN_pair x)
        rwa [mul_one] at this)
      liftPol := ((softOK_hTop S.w x).pow (X.p ^ e)).liftPol
      sgPol := mem_Pol_iff.2 fun l => EhatT_wh (wL X l) _ x _ fun _ => rfl }

theorem softHseg (S : UniformizedDVR X.p O) (hS : S.SqP) (C0 CE1 CE2 : ℝ) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    SoftOK S.w (hTop O X (topOdd X j i) ^ ((X.seg C0 CE1 CE2 j).P X.p i)) ((X.seg C0 CE1 CE2 j).P X.p i)
      (EhatT O X (topOdd X j i) ((X.seg C0 CE1 CE2 j).P X.p i))
      (fun l => (X.seg C0 CE1 CE2 j).P X.p i * dgH (topOdd X j i) l) := by
  exact softH S hS (topOdd X j i) _

end H

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem pd_mul_P (X : Loc) (C0 CE1 CE2 : ℝ) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    X.p ^ (segDists X.TT j).get i * (X.seg C0 CE1 CE2 j).P X.p i = X.p ^ segG X.TT j := by
  have hmem : (segDists X.TT j).get i ∈ segDists X.TT j := List.get_mem _ _
  have hlt : (segDists X.TT j).get i < segG X.TT j := by
    generalize (segDists X.TT j).get i = x at hmem ⊢
    unfold segDists at hmem
    rw [Finset.mem_sort, Finset.mem_image] at hmem
    obtain ⟨s, hs, rfl⟩ := hmem
    exact (Finset.mem_filter.mp hs).2.2.2
  simp only [Formalism.MainNotions.ColumnSystems.Loc.seg, SegData.P, segData]
  rw [← pow_add, Nat.add_sub_cancel' hlt.le]

theorem sgKS_powP {X : Loc} {O : Type} [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (j : Fin (numSeg X.TT))
    (i : Fin (segS X.TT j)) :
    sgKS O X j i ^ ((X.seg C0 CE1 CE2 j).P X.p i) = MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j) *
      MvPolynomial.X ((topOdd X j i, false), 0) ^ ((X.seg C0 CE1 CE2 j).P X.p i) := by
  unfold sgKS
  rw [mul_pow, ← pow_mul, pd_mul_P X C0 CE1 CE2 j i]

end Formalism.MainNotions.ColumnSystems.Pf
