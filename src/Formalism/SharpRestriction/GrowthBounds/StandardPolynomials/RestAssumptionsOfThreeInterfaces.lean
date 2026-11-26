module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.PreDef

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ZeroOfMultideg
section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.SumMulLe
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Glue

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] {w : O} {mu : ℝ} {β : GlobalTheory X}
  {L : LvDat C0 CE1 CE2 mu X β} {G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)} {Std : MonH X}

abbrev PreSys.κ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : Type :=
  (Σ j, P.ιC j) ⊕ ((Σ j, Fin (BDk C0 CE1 CE2 mu X β j).T.t) ⊕ P.ιM)

def PreSys.mult (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → ℕ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun x => L.lv x.1 x.2) P.multM)

def PreSys.f (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → RHH O X :=
  Sum.elim (fun x => P.fC x.1 x.2) (Sum.elim (fun x => P.fH x.1 x.2) P.fM)

def PreSys.sg (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → RHH O X :=
  Sum.elim (fun x => P.sgC x.1 x.2) (Sum.elim (fun x => P.sgH x.1 x.2) (fun a => monomial (P.aM a) 1))

def PreSys.od (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → ℕ :=
  Sum.elim (fun x => P.oC x.1 x.2) (Sum.elim (fun x => P.oH x.1 x.2) P.oM)

def PreSys.dg (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → X.TT × Bool → ℕ :=
  Sum.elim (fun x => P.dgC x.1 x.2) (Sum.elim (fun x => P.dgH x.1 x.2) P.dgM)

theorem PreSys.prod_κ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (F : P.κ → RHH O X) :
    ∏ a, F a = (∏ j, ∏ a, F (Sum.inl ⟨j, a⟩)) * ((∏ j, ∏ i, F (Sum.inr (Sum.inl ⟨j, i⟩))) * ∏ a, F (Sum.inr (Sum.inr a))) := by
  simp only [Fintype.prod_sum_type, Fintype.prod_sigma]

theorem PreSys.sum_κ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (F : P.κ → ℕ) :
    ∑ a, F a = (∑ j, ∑ a, F (Sum.inl ⟨j, a⟩)) + ((∑ j, ∑ i, F (Sum.inr (Sum.inl ⟨j, i⟩))) + ∑ a, F (Sum.inr (Sum.inr a))) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma]

theorem sum_mul_le {κ : Type} [Fintype κ] (u d : κ → ℕ) (Q : ℕ) (h : ∀ a, d a ≤ Q) : ∑ a, u a * d a ≤ (∑ a, u a) * Q := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun a _ => Nat.mul_le_mul_left _ (h a)

theorem PreSys.sgNd (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (a : P.κ) : HomW (ndHom X) (P.od a) (P.sg a) := by
  rcases a with ⟨j, i⟩ | ⟨j, i⟩ | a
  · exact P.homC j i
  · exact P.homH j i
  · show HomW (ndHom X) (P.oM a) (monomial (P.aM a) (1 : KK O))
    intro m hm
    have hm' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
    subst hm'
    exact P.homM a

theorem PreSys.sgMd (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (a : P.κ) :
    P.sg a ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (P.dg a) := by
  rcases a with ⟨j, i⟩ | ⟨j, i⟩ | a
  · exact P.polC j i
  · exact P.polH j i
  · show monomial (P.aM a) (1 : KK O) ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (P.dgM a)
    rw [Pol, MvPolynomial.mem_restrictSupport_iff]
    intro m hm
    have hm' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hm))
    subst hm'
    exact P.polM a

theorem PreSys.dgQ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (a : P.κ) (l : X.TT × Bool) : P.dg a l ≤ X.p ^ X.G' := by
  rcases a with ⟨j, i⟩ | ⟨j, i⟩ | a
  · exact P.dgCQ j i l
  · exact P.dgHQ j i l
  · exact P.dgMQ a l

theorem PreSys.dgY (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (a : P.κ) (j' : Fin (numSeg X.TT)) :
    P.dg a (topEnd X j', false) = 0 := by
  rcases a with ⟨j, i⟩ | ⟨j, i⟩ | a
  · exact P.dgCY j i j'
  · exact P.dgHY j i j'
  · exact P.dgMY a j'

theorem PreSys.ordκ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) :
    P.oR + ∑ a, P.mult a * P.od a = ordFam C0 CE1 CE2 X β := by
  rw [P.sum_κ]
  simp only [PreSys.mult, PreSys.od, Sum.elim_inl, Sum.elim_inr, one_mul]
  exact P.ordEq

theorem PreSys.degκ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (l : X.TT × Bool) :
    P.dR l + ∑ a, P.mult a * P.dg a l = hhDegs X.TT X.aT X.bT l := by
  rw [P.sum_κ]
  simp only [PreSys.mult, PreSys.dg, Sum.elim_inl, Sum.elim_inr, one_mul]
  exact P.degEq l

theorem PreSys.fprod (P : PreSys C0 CE1 CE2 X O w mu β L G Std) :
    ∏ a, P.f a ^ P.mult a = (∏ j, ∏ a, P.fC j a) * ((∏ j, ∏ i, P.fH j i ^ L.lv j i) * ∏ a, P.fM a ^ P.multM a) := by
  rw [P.prod_κ]
  simp only [PreSys.f, PreSys.mult, Sum.elim_inl, Sum.elim_inr, pow_one]

theorem PreSys.symκ (P : PreSys C0 CE1 CE2 X O w mu β L G Std)
    (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j) :
    P.sgR * ∏ a, P.sg a ^ P.mult a = symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j)) := by
  have hsym : symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j)) =
      (∏ j, L.head O j (L.lv j) (G j)) * monomial Std 1 := by
    rw [hStd, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => L.ioBlock_word O j (G j))
  have h1 := P.ident (fun _ _ => 1) L.lv P.multM 0
  have h2 : P.R + ((∑ j, ∑ a, (1 : ℕ) • P.pl j a) + ∑ a, P.multM a • P.aM a) + 0 = Std := by
    refine Eq.trans ?_ P.stdEq.symm
    simp
  have h3 : ∀ j, ∏ a, P.Kc j a ^ (1 : ℕ) = G j := fun j => by simp [P.Kprod j]
  rw [h2] at h1
  simp only [h3] at h1
  rw [hsym, ← h1, P.prod_κ]
  simp [PreSys.mult, PreSys.sg]

end Glue

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Glue

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] {w : O} {mm : ℝ} {n : ℕ} {β : GlobalTheory X}
  {L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β}
  {G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)} {Std : MonH X}

theorem zero_of_multideg {l : X.TT × Bool} {M : MonH X} (h : multideg M l = 0) (c : Fin (X.m + 1)) : M (l, c) = 0 :=
  (Finset.sum_eq_zero_iff.1 h) c (Finset.mem_univ c)

theorem PreSys.core (D : Formalism.BasicNotions.D7) [CharZero (KK O)]
    (P : PreSys C0 CE1 CE2 X O w (mm + (n : ℝ) * ka1 X) β L G Std)
    (hT : TCoreBody C0 Cde CE1 CE2 X O mm n β L Std) (hG0 : ∀ j, G j ≠ 0)
    (hGY : ∀ j k, G j ∈ YCond (KK O) (r := X.m) (L.LL j) ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J k)
      ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k))
    (hcov : ∀ j, ∑ i, (if (L.LL j).vec i then 0 else 1) ≤ X.N1)
    (u : P.κ → ℕ) (hu : ∀ a, u a ≤ P.mult a) (M : MonH X) (e : ℕ) (he1 : 1 ≤ e) (hsum : ∑ a, u a ≤ e) (hen : e < n)
    (hdeg : ∀ l, multideg M l = ∑ a, u a * P.dg a l) (hnd : ndM X M ≤ ∑ a, u a * P.od a + e) :
    P.sgR * (∏ a, P.sg a ^ (P.mult a - u a)) * monomial M 1 ∈
      SSe C0 Cde CE1 CE2 X O mm n (ordFam C0 CE1 CE2 X β) e := by
  classical
  set uC : ∀ j, P.ιC j → ℕ := fun j a => u (Sum.inl ⟨j, a⟩) with huCdef
  set uH : ∀ j, Fin (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.t → ℕ := fun j i => u (Sum.inr (Sum.inl ⟨j, i⟩)) with huHdef
  set uM : P.ιM → ℕ := fun a => u (Sum.inr (Sum.inr a)) with huMdef
  have huC : ∀ j a, uC j a ≤ 1 := fun j a => hu (Sum.inl ⟨j, a⟩)
  have huM : ∀ a, uM a ≤ P.multM a := fun a => hu (Sum.inr (Sum.inr a))
  have hsum' : (∑ j, ∑ a, uC j a) + ((∑ j, ∑ i, uH j i) + ∑ a, uM a) ≤ e := by
    rw [← P.sum_κ u]; exact hsum
  set B : MonH X := (∑ j, ∑ a, (1 - uC j a) • P.pl j a) + ∑ a, (P.multM a - uM a) • P.aM a with hB
  set Brem : MonH X := (∑ j, ∑ a, uC j a • P.pl j a) + ∑ a, uM a • P.aM a with hBrem
  have key : P.sgR * (∏ a, P.sg a ^ (P.mult a - u a)) * monomial M 1 =
      (∏ j, L.head O j (fun i => L.lv j i - uH j i) (∏ a, P.Kc j a ^ (1 - uC j a))) * monomial (P.R + B + M) 1 := by
    rw [P.prod_κ]
    exact P.ident (fun j a => 1 - uC j a) (fun j i => L.lv j i - uH j i) (fun a => P.multM a - uM a) M
  have hSB : Std = (P.R + B) + Brem := by
    refine P.stdEq.trans ?_
    have h1 : (∑ j, ∑ a, P.pl j a) = (∑ j, ∑ a, (1 - uC j a) • P.pl j a) + ∑ j, ∑ a, uC j a • P.pl j a := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← add_smul, Nat.sub_add_cancel (huC j a), one_smul]
    have h2 : (∑ a, P.multM a • P.aM a) = (∑ a, (P.multM a - uM a) • P.aM a) + ∑ a, uM a • P.aM a := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← add_smul, Nat.sub_add_cancel (huM a)]
    rw [h1, h2, hB, hBrem]
    abel
  have hSv : ∀ v, Std v = (P.R + B) v + Brem v := fun v => by
    rw [← Finsupp.add_apply]; exact DFunLike.congr_fun hSB v
  have hAv : ∀ v, (P.R + B + M) v = (P.R + B) v + M v := fun v => Finsupp.add_apply _ _ v
  have hmdB : ∀ l, multideg Brem l = (∑ j, ∑ a, uC j a * multideg (P.pl j a) l) + ∑ a, uM a * multideg (P.aM a) l := by
    intro l
    have : (mdHom X l) Brem = (∑ j, ∑ a, uC j a * (mdHom X l) (P.pl j a)) + ∑ a, uM a * (mdHom X l) (P.aM a) := by
      rw [hBrem]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_nsmul, smul_eq_mul]
    exact this
  rw [key]
  refine hT e he1 hen (fun j i => L.lv j i - uH j i) (fun j i => Nat.sub_le _ _)
    (fun j => ∏ a, P.Kc j a ^ (1 - uC j a)) (fun j i => ∑ a, (1 - uC j a) * P.dK j a i) ?_ ?_ ?_ ?_ (P.R + B + M) ?_ ?_ ?_ ?_ ?_
  · exact fun j => glIntProd _ _ fun a _ => glIntPow (P.KInt j a) _
  · exact fun j => chain_pol_prod (KK O) Finset.univ (fun a i => (1 - uC j a) * P.dK j a i) _
      fun a _ => chain_pol_pow (KK O) (P.KPol j a) _
  · intro j i
    rw [← P.dKsum j i]
    refine Finset.sum_le_sum fun a _ => ?_
    calc (1 - uC j a) * P.dK j a i ≤ 1 * P.dK j a i := Nat.mul_le_mul_right _ (Nat.sub_le 1 _)
      _ = P.dK j a i := one_mul _
  · intro j k
    have hprod : (∏ a, P.Kc j a ^ (1 - uC j a)) * (∏ a, P.Kc j a ^ uC j a) = G j := by
      rw [← Finset.prod_mul_distrib, ← P.Kprod j]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← pow_add, Nat.sub_add_cancel (huC j a), pow_one]
    refine ycond_factor D (L.LL j) _ _ _ (∏ a, P.Kc j a ^ uC j a) (fun i => ∑ a, uC j a * P.dK j a i)
      (chain_pol_prod (KK O) Finset.univ (fun a i => uC j a * P.dK j a i) _
        fun a _ => chain_pol_pow (KK O) (P.KPol j a) _) ?_ ?_ (X.N1 * e) ?_
    · intro h0
      apply hG0 j
      rw [← hprod, h0, mul_zero]
    · rw [hprod]; exact hGY j k
    · have hCj : ∑ a, uC j a ≤ e := by
        have h1 : ∑ a, uC j a ≤ ∑ j, ∑ a, uC j a :=
          Finset.single_le_sum (f := fun j => ∑ a, uC j a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        omega
      calc ∑ i, (if (L.LL j).vec i then 0 else ∑ a, uC j a * P.dK j a i)
          ≤ ∑ i, (if (L.LL j).vec i then 0 else 1) * ∑ a, uC j a := by
            refine Finset.sum_le_sum fun i _ => ?_
            by_cases hv : (L.LL j).vec i = true
            · simp [hv]
            · simp only [hv, if_false, one_mul, Bool.false_eq_true]
              refine Finset.sum_le_sum fun a _ => ?_
              calc uC j a * P.dK j a i ≤ uC j a * 1 := Nat.mul_le_mul_left _ (P.digit_le_one j a i)
                _ = uC j a := mul_one _
        _ = (∑ i, (if (L.LL j).vec i then 0 else 1)) * ∑ a, uC j a := (Finset.sum_mul _ _ _).symm
        _ ≤ X.N1 * e := Nat.mul_le_mul (hcov j) hCj
  · intro l
    calc ∑ c, (Std (l, c) - (P.R + B + M) (l, c)) ≤ ∑ c, Brem (l, c) := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [hSv, hAv]; omega
      _ = multideg Brem l := rfl
      _ = (∑ j, ∑ a, uC j a * multideg (P.pl j a) l) + ∑ a, uM a * multideg (P.aM a) l := hmdB l
      _ ≤ (∑ j, ∑ a, uC j a) * X.p ^ X.G' + (∑ a, uM a) * X.p ^ X.G' := by
          refine Nat.add_le_add ?_ (sum_mul_le _ _ _ fun a => by rw [P.polM a l]; exact P.dgMQ a l)
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun j _ => sum_mul_le _ _ _ fun a => P.plQ j a l
      _ = ((∑ j, ∑ a, uC j a) + ∑ a, uM a) * X.p ^ X.G' := (Nat.add_mul _ _ _).symm
      _ ≤ e * X.p ^ X.G' := Nat.mul_le_mul_right _ (by omega)
      _ = X.p ^ X.G' * e := Nat.mul_comm _ _
  · intro l
    calc ∑ c, ((P.R + B + M) (l, c) - Std (l, c)) ≤ ∑ c, M (l, c) := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [hSv, hAv]; omega
      _ = multideg M l := rfl
      _ = ∑ a, u a * P.dg a l := hdeg l
      _ ≤ (∑ a, u a) * X.p ^ X.G' := sum_mul_le _ _ _ fun a => P.dgQ a l
      _ ≤ e * X.p ^ X.G' := Nat.mul_le_mul_right _ hsum
      _ = X.p ^ X.G' * e := Nat.mul_comm _ _
  · intro j c
    have hM0 : multideg M (topEnd X j, false) = 0 := by
      rw [hdeg]
      exact Finset.sum_eq_zero fun a _ => by rw [P.dgY a j, mul_zero]
    have hB0 : multideg Brem (topEnd X j, false) = 0 := by
      rw [hmdB]
      have h1 : (∑ j', ∑ a, uC j' a * multideg (P.pl j' a) (topEnd X j, false)) = 0 :=
        Finset.sum_eq_zero fun j' _ => Finset.sum_eq_zero fun a _ => by rw [P.plY j' a j, mul_zero]
      have h2 : (∑ a, uM a * multideg (P.aM a) (topEnd X j, false)) = 0 :=
        Finset.sum_eq_zero fun a _ => by rw [P.polM a, P.dgMY a j, mul_zero]
      rw [h1, h2]
    rw [hSv, hAv, zero_of_multideg hM0 c, zero_of_multideg hB0 c]
  · rw [← key]
    refine mem_Pol_iffW.2 fun l => ?_
    have h1 := hom_total (mdHom X l) P.sg (fun a => P.dg a l) (fun a => mem_Pol_iffW.1 (P.sgMd a) l)
      (mem_Pol_iffW.1 P.rigPol l) P.mult u M
    have h2 : P.dR l + ∑ a, (P.mult a - u a) * P.dg a l + (mdHom X l) M = hhDegs X.TT X.aT X.bT l := by
      have h3 : (mdHom X l) M = ∑ a, u a * P.dg a l := hdeg l
      rw [h3, add_assoc, sum_split _ _ _ hu, P.degκ l]
    rw [h2] at h1
    exact h1
  · rw [← key]
    intro m hm
    have h1 := hom_total (ndHom X) P.sg P.od P.sgNd P.rigHom P.mult u M m hm
    have h1' : ndM X m = P.oR + ∑ a, (P.mult a - u a) * P.od a + ndM X M := h1
    have h2 := sum_split P.mult u P.od hu
    have h3 := P.ordκ
    omega

def PreSys.toFacSys (D : Formalism.BasicNotions.D7) [CharZero (KK O)]
    (P : PreSys C0 CE1 CE2 X O w (mm + (n : ℝ) * ka1 X) β L G Std)
    (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j)
    (hT : TCoreBody C0 Cde CE1 CE2 X O mm n β L Std) (hG0 : ∀ j, G j ≠ 0)
    (hGY : ∀ j k, G j ∈ YCond (KK O) (r := X.m) (L.LL j) ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J k)
      ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k))
    (hcov : ∀ j, ∑ i, (if (L.LL j).vec i then 0 else 1) ≤ X.N1) :
    FacSys C0 Cde CE1 CE2 X O w mm n (ordFam C0 CE1 CE2 X β)
      (symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j))) where
  κ := P.κ
  fin := inferInstance
  mult := P.mult
  f := P.f
  sg := P.sg
  od := P.od
  dg := P.dg
  fR := P.fR
  sgR := P.sgR
  oR := P.oR
  fac := by
    rintro (⟨j, a⟩ | ⟨j, i⟩ | a)
    · exact P.facC j a
    · exact P.facH j i
    · exact P.facM a
  sgHom := fun a m hm => P.sgNd a m hm
  liftPol := by
    rintro (⟨j, a⟩ | ⟨j, i⟩ | a)
    · exact P.liftC j a
    · exact P.liftH j i
    · exact P.liftM a
  sgPol := P.sgMd
  rigA := P.rigA
  rigLift := P.rigLift
  rigInt := P.rigInt
  clean := fun g' hg' hne => by rw [P.fprod]; exact P.clean g' hg' hne
  total := by rw [P.fprod]; exact P.total
  ordEq := P.ordκ
  symEq := P.symκ hStd
  core := fun u hu M e he1 hsum hen hdeg hnd => P.core D hT hG0 hGY hcov u hu M e he1 hsum hen hdeg hnd

end Glue

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.PolBridge

section Mono

variable {σ : Type} {K : Type} [CommRing K]

def IsMono (P : MvPolynomial σ K) : Prop := ∃ M : σ →₀ ℕ, P = monomial M 1

theorem IsMono.one : IsMono (1 : MvPolynomial σ K) := ⟨0, rfl⟩

theorem IsMono.X (v : σ) : IsMono (MvPolynomial.X v : MvPolynomial σ K) := ⟨Finsupp.single v 1, rfl⟩

theorem IsMono.mul {P Q : MvPolynomial σ K} (hP : IsMono P) (hQ : IsMono Q) : IsMono (P * Q) := by
  obtain ⟨a, rfl⟩ := hP
  obtain ⟨b, rfl⟩ := hQ
  exact ⟨a + b, by rw [monomial_mul, one_mul]⟩

theorem IsMono.pow {P : MvPolynomial σ K} (hP : IsMono P) (n : ℕ) : IsMono (P ^ n) := by
  obtain ⟨a, rfl⟩ := hP
  exact ⟨n • a, by rw [monomial_pow, one_pow]⟩

theorem IsMono.prod {ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ K) (h : ∀ i ∈ s, IsMono (P i)) :
    IsMono (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsMono.one (σ := σ) (K := K)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

end Mono

section Std

variable (O : Type) [CommRing O] [IsDomain O] {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

theorem ioDXmono (j : Fin (numSeg X.TT)) (v : BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) :
    IsMono (ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X v)) := by
  have e : ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X v) =
      (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : RHH O X) ^ symLev X.p C0 CE1 CE2 X j v := aeval_X _ _
  rw [e]
  exact (IsMono.X _).pow _

theorem LvDat.stdPoly_mono (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) : IsMono (L.stdPoly O j) := by
  unfold LvDat.stdPoly
  refine (IsMono.mul ?_ ?_).mul ?_
  · unfold digitMon
    exact IsMono.prod _ _ fun i _ => IsMono.prod _ _ fun c _ => ((IsMono.X _).pow _).mul ((IsMono.X _).pow _)
  · unfold sTopMon
    refine IsMono.prod _ _ fun i _ => ?_
    split_ifs
    · exact ((IsMono.X _).pow _).mul ((IsMono.X _).pow _)
    · exact IsMono.one
  · simp only [map_mul, map_prod, map_pow]
    exact ((IsMono.prod _ _ fun i _ => (ioDXmono O j _).pow _).mul ((ioDXmono O j _).pow _)).mul
      (IsMono.prod _ _ fun c _ => (ioDXmono O j _).pow _)

theorem LvDat.exists_std (L : LvDat C0 CE1 CE2 mu X β) :
    ∃ Std : MonH X, (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j := by
  obtain ⟨M, hM⟩ := IsMono.prod Finset.univ (fun j => L.stdPoly O j) fun j _ => L.stdPoly_mono O j
  exact ⟨M, hM.symm⟩

end Std

theorem cov_count (s : ℕ) : ∑ i : Fin (2 * s + 1), (if decide ((i : ℕ) % 2 = 0) = true then 0 else 1) ≤ s := by
  classical
  have h1 : ∑ i : Fin (2 * s + 1), (if decide ((i : ℕ) % 2 = 0) = true then 0 else 1) =
      (Finset.univ.filter fun i : Fin (2 * s + 1) => ¬ (i : ℕ) % 2 = 0).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : (i : ℕ) % 2 = 0 <;> simp [h]
  rw [h1]
  refine (Finset.card_le_card_of_injOn (t := Finset.range s) (fun i : Fin (2 * s + 1) => (i : ℕ) / 2) ?_ ?_).trans
    (by simp)
  · intro i hi
    have h2 : ¬ (i : ℕ) % 2 = 0 := by simpa using hi
    have h3 := i.2
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  · intro a ha b hb hab
    have h2 : ¬ (a : ℕ) % 2 = 0 := by simpa using ha
    have h3 : ¬ (b : ℕ) % 2 = 0 := by simpa using hb
    have h4 : (a : ℕ) / 2 = (b : ℕ) / 2 := hab
    apply Fin.ext
    omega

section Psi

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r]

theorem psi_facts {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) {p : ℕ} [Fact p.Prime]
    (S : UniformizedDVR p O) (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (hJ : ∀ k, J k ≤ N)
    (x : Tx r LL) (hx : x ∈ sAll LL J M) :
    psiR (KK O) LL x ≠ 0 ∧ ∀ k, psiR (KK O) LL x ∈ YCond (KK O) (r := r) LL (J k) (M k) := by
  have hp : p.Prime := Fact.out
  have hKz : CharZero (KK O) := dvr_fraction_field_charZero S hp
  obtain ⟨hli, hspan⟩ := hA2 O N r (⟨LL.vec⟩ : Letters (Fin N)) LL.deg
  have hli' : LinearIndependent O (psiR (r := r) O LL) := hli
  have hrange : Submodule.span O (Set.range (psiR (r := r) O LL)) = Pol O r LL.deg := by
    rw [← hspan]
    congr 1
    ext G
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.1.1, x.1.2, x.2, rfl⟩
    · rintro ⟨P, I, h, rfl⟩; exact ⟨⟨(P, I), h⟩, rfl⟩
  have hfin : Finite (Tx r LL) := tx_finite LL hli' hrange
  obtain ⟨Bd, hBd⟩ := exists_bound (r := r) (Lt := (⟨LL.vec⟩ : Letters (Fin N))) (B := LL.deg)
  have hC1 := one_cond D LL hrange hspan (fun th M => (hA3 p O S N r _ LL.deg th M).1) Bd hBd J M hJ
  refine ⟨(psiK_li LL hli').ne_zero x, fun k => ?_⟩
  rw [← psiR_map]
  exact (hC1 k _ (psiK_mem LL hrange x).1).2 (Submodule.subset_span ⟨x, hx k, rfl⟩)

end Psi

theorem facSysAt_of {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D)
    {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hC : ColsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hP : PreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (hT : TCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    FacSysAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ _ O _ _ _ _ S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ s hs
  have hp : X.p.Prime := Fact.out
  haveI hKz : CharZero (KK O) := dvr_fraction_field_charZero S hp
  simp only [colGens, Set.mem_setOf_eq] at hs
  choose lv jp hOK y hy γ hγ hx using hs
  let L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β := ⟨lv, jp, hOK, γ, hγ⟩
  have hs' : s = fun j => L.word O j (psiR (KK O) (L.LL j) (y j)) := funext fun j => hx j
  obtain ⟨Std, hStd⟩ := L.exists_std O
  have hfacts := fun j => psi_facts hA2 hA3 S (L.LL j) (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J
    (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr (blockData_J_le _ _ _ _ _ _) (y j) (hy j)
  have CS := fun j => (hC X O S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ L j (y j) (hy j)).some
  obtain ⟨P⟩ := hP X O S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ L _ CS (fun j => (hfacts j).1) Std hStd
  rw [hs']
  exact ⟨P.toFacSys D hStd (hT X O S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ L Std hStd) (fun j => (hfacts j).1)
    (fun j => (hfacts j).2) (fun j => (cov_count (segS X.TT j)).trans (hHI.1.2.2.2.2.1 j).2)⟩

theorem restFacSys_of {D : Formalism.BasicNotions.D7} (hA : admitted D) (hC : RestCols) (hP : RestPre) (hT : RestTCore) : FacSysCondition :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h =>
    facSysAt_of (D := D) hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.1 h.1.1 h.1.2 h.2) ((hC.and hP).and hT)

theorem rest_assumptions_of_three_interfaces {D : Formalism.BasicNotions.D7} (hA : admitted D) (hC : RestCols) (hP : RestPre) (hT : RestTCore) : RestAsmRT :=
  restAsmRT_of_facSys hA (restFacSys_of hA hC hP hT)

end Formalism.MainNotions.ColumnSystems.Pf
