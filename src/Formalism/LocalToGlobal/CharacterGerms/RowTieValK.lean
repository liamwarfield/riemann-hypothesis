module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieMemCHarm

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.LinearCoeffExponentialEqIte
section -- merged from Formalism.LocalToGlobal.CharacterGerms.LinearCoeffSubstChainRule
section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieValCr
section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieValBr
section -- merged from Formalism.LocalToGlobal.CharacterGerms.ValueEquationOfProjectors
section -- merged from Formalism.LocalToGlobal.CharacterGerms.CoordinateChangeComp1IntertwinesAction
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}

variable (Y : FBChart C V O dd)

theorem coordinateChange_comp1_intertwines_action {n : ℕ} (x : O) (a : Pt C n dd) : comp1 (Y.B.A.act x) a = actAt Y x a := by
  unfold actAt
  unfold comp1
  funext i
  unfold ev
  first
  | rfl
  | (congr 1; funext q; simp)
  | (congr 1; funext q; skip)

theorem addOf_eq' {n : ℕ} (a b : Pt C n dd) : addOf Y.B.G.F a b = addAt Y a b := by
  unfold addAt
  unfold addOf
  funext i
  unfold ev
  first
  | rfl
  | (congr 1; funext q; unfold P2; rfl)
  | (congr 1; funext q; unfold P2; obtain ⟨j, k⟩ := q; fin_cases j <;> simp)

theorem actAt_addAt (x : O) {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    actAt Y x (addAt Y a b) = addAt Y (actAt Y x a) (actAt Y x b) := by
  have h := Y.B.A.hom x
  rw [show Y.B.G.add (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) = addAt Y (pt C dd 0) (pt C dd 1) from addOf_eq' Y _ _,
    show Y.B.G.add (comp1 (Y.B.A.act x) (pt C (n := 2) dd 0)) (comp1 (Y.B.A.act x) (pt C (n := 2) dd 1)) =
      addAt Y (comp1 (Y.B.A.act x) (pt C dd 0)) (comp1 (Y.B.A.act x) (pt C dd 1)) from addOf_eq' Y _ _,
    coordinateChange_comp1_intertwines_action, coordinateChange_comp1_intertwines_action, coordinateChange_comp1_intertwines_action] at h
  have k0 := cc_pt (C := C) (dd := dd) (0 : Fin 2)
  have k1 := cc_pt (C := C) (dd := dd) (1 : Fin 2)
  have hP := constantCoeff_pair_substitution ha hb
  have e0 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (0 : Fin 2) i)) = a := funext fun i => pair_subst_coordinate ha hb 0 i
  have e1 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (1 : Fin 2) i)) = b := funext fun i => pair_subst_coordinate ha hb 1 i
  funext i
  have h2 := congrArg (MvPowerSeries.subst (P2 a b)) (congrFun h i)
  rw [actAt_subst Y hP (cc_addAt Y k0 k1), addAt_subst Y hP (cc_actAt Y x k0) (cc_actAt Y x k1)] at h2
  have e2 : (fun i => MvPowerSeries.subst (P2 a b) (addAt Y (pt C dd (0 : Fin 2)) (pt C dd (1 : Fin 2)) i)) =
      addAt Y a b := by
    funext j
    rw [addAt_subst Y hP k0 k1, e0, e1]
  have e3 : (fun i => MvPowerSeries.subst (P2 a b) (actAt Y x (pt C dd (0 : Fin 2)) i)) = actAt Y x a := by
    funext j
    rw [actAt_subst Y hP k0, e0]
  have e4 : (fun i => MvPowerSeries.subst (P2 a b) (actAt Y x (pt C dd (1 : Fin 2)) i)) = actAt Y x b := by
    funext j
    rw [actAt_subst Y hP k1, e1]
  rw [e2, e3, e4] at h2
  exact h2

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}

variable (Y : FBChart C V O dd)

def exAt (a : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C := fun i => MvPowerSeries.subst a (e Y i)

theorem cc_exAt {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.constantCoeff (exAt Y a i) = 0 := by
  unfold exAt
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d = 0
  · subst hd
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, cc_e Y i]
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
      rw [map_finsuppProd]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
      show MvPowerSeries.constantCoeff (a s ^ d s) = 0
      rw [map_pow, ha s, zero_pow hs]
    rw [h0, smul_zero]

theorem l_add_at {u v : Fin dd → MvPowerSeries τ C} (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0)
    (hv : ∀ i, MvPowerSeries.constantCoeff (v i) = 0) (m : Fin dd) :
    MvPowerSeries.subst (addAt Y u v) (l Y m) = MvPowerSeries.subst u (l Y m) + MvPowerSeries.subst v (l Y m) := by
  have h := congrArg (MvPowerSeries.subst (P2 u v)) (l_add Y m)
  have hP := constantCoeff_pair_substitution hu hv
  rw [subst_add' hP, subst_subst (cc_F Y) hP,
    subst_subst (a := fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (fun _ => cc_X _) hP,
    subst_subst (a := fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (fun _ => cc_X _) hP] at h
  have e0 : (fun s : Fin dd => MvPowerSeries.subst (P2 u v) (MvPowerSeries.X ((0 : Fin 2), s) : PS C 2 dd)) = u :=
    funext fun i => subst_X hP _
  have e1 : (fun s : Fin dd => MvPowerSeries.subst (P2 u v) (MvPowerSeries.X ((1 : Fin 2), s) : PS C 2 dd)) = v :=
    funext fun i => subst_X hP _
  rw [e0, e1] at h
  exact h

theorem l_exAt {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (m : Fin dd) :
    MvPowerSeries.subst (exAt Y a) (l Y m) = a m := by
  unfold exAt
  rw [← subst_subst (cc_e Y) ha, lgex, subst_X ha]

theorem e_lAt {P : Fin dd → MvPowerSeries τ C} (hP : ∀ i, MvPowerSeries.constantCoeff (P i) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun m => MvPowerSeries.subst P (l Y m)) (e Y i) = P i := by
  rw [← subst_subst (cc_l Y) hP, exlg, subst_X hP]

theorem ex_add {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    exAt Y (fun m => a m + b m) = addAt Y (exAt Y a) (exAt Y b) := by
  funext i
  have hP := cc_addAt Y (cc_exAt Y ha) (cc_exAt Y hb)
  rw [← e_lAt Y hP i]
  unfold exAt
  congr 1
  funext m
  show a m + b m = MvPowerSeries.subst (addAt Y (exAt Y a) (exAt Y b)) (l Y m)
  rw [l_add_at Y (cc_exAt Y ha) (cc_exAt Y hb), l_exAt Y ha, l_exAt Y hb]

theorem exAt_zero : exAt Y (fun _ : Fin dd => (0 : MvPowerSeries τ C)) = fun _ => 0 := by
  funext i
  ext e'
  simp only [exAt]
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => map_zero _)),
    finsum_eq_zero_of_forall_eq_zero]
  · simp
  · intro d
    by_cases hd : d = 0
    · subst hd
      simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, cc_e Y i]
    · obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
      have h0 : (d.prod fun s e => (0 : MvPowerSeries τ C) ^ e) = 0 :=
        Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs)
      rw [h0, map_zero, smul_zero]

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def EndoLogSt (Y : FBChart C V O dd) : Prop :=
  ∀ ε : Pt C 1 dd, (∀ i, MvPowerSeries.constantCoeff (ε i) = 0) →
    comp1 ε (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 ε (pt C (n := 2) dd 0)) (comp1 ε (pt C (n := 2) dd 1)) →
    ∀ (τ : Type) [Finite τ] (a : Fin dd → MvPowerSeries τ C), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) →
    ∀ i, MvPowerSeries.subst (fun q : Fin 1 × Fin dd => VP.exAt Y a q.2) (ε i) =
      VP.exAt Y (fun m => ∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ε m) • a j) i

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}

def mapAt (ε : Pt C 1 dd) (a : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C :=
  fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (ε i)

theorem comp_eq_map_at {n : ℕ} (ε : Pt C 1 dd) (a : Pt C n dd) : comp1 ε a = mapAt ε a := by
  unfold comp1 mapAt ev
  funext i
  congr 1
  funext p
  first
    | (rw [Fin.fin_one_eq_zero p.1]; rfl)
    | (simp [Fin.fin_one_eq_zero p.1])

theorem cc_mapAt {ε : Pt C 1 dd} (hε : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0) {a : Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.constantCoeff (mapAt ε a i) = 0 := by
  unfold mapAt
  have hb : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => ha q.2)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst hb]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e = 0
  · rw [he, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hε i, zero_smul]
  · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.1 he
    have hmem : s ∈ e.support := Finsupp.mem_support_iff.2 (by simpa using hs)
    have h0 : MvPowerSeries.constantCoeff (e.prod fun s k => a s.2 ^ k) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero hmem
      rw [map_pow, ha s.2, zero_pow (Finsupp.mem_support_iff.1 hmem)]
    rw [h0, smul_zero]

theorem mapAt_subst [Finite τ] {A : τ → MvPowerSeries τ' C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0)
    (ε : Pt C 1 dd) {u : Fin dd → MvPowerSeries τ C} (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (i : Fin dd) :
    MvPowerSeries.subst A (mapAt ε u i) = mapAt ε (fun i => MvPowerSeries.subst A (u i)) i := by
  unfold mapAt
  have hb : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => u q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => hu q.2)
  have hA' : MvPowerSeries.HasSubst A := MvPowerSeries.hasSubst_of_constantCoeff_zero hA
  rw [MvPowerSeries.subst_comp_subst_apply hb hA']

theorem subst_pow' {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) (k : ℕ) :
    MvPowerSeries.subst a (f ^ k) = MvPowerSeries.subst a f ^ k := by
  have hb : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  first
    | exact MvPowerSeries.subst_pow hb f k
    | (rw [← MvPowerSeries.coe_substAlgHom hb, map_pow])

variable (Y : FBChart C V O dd)

theorem cmp_at {ε ε' : Pt C 1 dd} (hε : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0)
    (hε' : ∀ i, MvPowerSeries.constantCoeff (ε' i) = 0) {a b : Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    MvPowerSeries.subst (P2 a b) (FB.expS C (ev (n := 2) ![comp1 ε (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 ε' (pt C dd 1)] Y.h)) =
      mvExp (hAt Y (mapAt ε a) b - hAt Y a (mapAt ε' b)) := by
  rw [eval_two_points_eq_subst _ _ _ rfl, eval_two_points_eq_subst _ _ _ rfl, comp_eq_map_at, comp_eq_map_at]
  have k0 := cc_pt (C := C) (dd := dd) (0 : Fin 2)
  have k1 := cc_pt (C := C) (dd := dd) (1 : Fin 2)
  have hP := constantCoeff_pair_substitution ha hb
  have e0 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (0 : Fin 2) i)) = a := funext fun i => pair_subst_coordinate ha hb 0 i
  have e1 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (1 : Fin 2) i)) = b := funext fun i => pair_subst_coordinate ha hb 1 i
  have hcc : MvPowerSeries.constantCoeff (hAt Y (mapAt ε (pt C dd (0 : Fin 2))) (pt C dd (1 : Fin 2)) -
      hAt Y (pt C dd (0 : Fin 2)) (mapAt ε' (pt C dd (1 : Fin 2)))) = 0 := by
    rw [map_sub, cc_hAt Y (cc_mapAt hε k0) k1, cc_hAt Y k0 (cc_mapAt hε' k1), sub_zero]
  show MvPowerSeries.subst (P2 a b) (FB.expS C (hAt Y (mapAt ε (pt C dd (0 : Fin 2))) (pt C dd (1 : Fin 2)) -
      hAt Y (pt C dd (0 : Fin 2)) (mapAt ε' (pt C dd (1 : Fin 2))))) = _
  rw [expS_eq _ hcc, subst_exp hP hcc, subst_sub' hP, hAt_subst Y hP (cc_mapAt hε k0) k1,
    hAt_subst Y hP k0 (cc_mapAt hε' k1), e0, e1]
  congr 3
  · funext i; rw [mapAt_subst hP ε k0, e0]
  · funext i; rw [mapAt_subst hP ε' k1, e1]

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}

def lin1 {σ : Type} (f : MvPowerSeries σ C) (j : σ) : C := MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (R := C) j f)

theorem linear_coeff_eq_coeff_single {σ : Type} (f : MvPowerSeries σ C) (j : σ) : lin1 f j = MvPowerSeries.coeff (Finsupp.single j 1) f := by
  unfold lin1
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

theorem linear_coeff_subst_chain_rule {σ : Type} [Fintype σ] {A : σ → MvPowerSeries τ C}
    (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0) (f : MvPowerSeries σ C) (j : τ) :
    lin1 (MvPowerSeries.subst A f) j = ∑ k, lin1 (A k) j * lin1 f k := by
  have hs : MvPowerSeries.HasSubst A := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hA
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hA
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hA s]; exact IsNilpotent.zero)

  have hmul : ∀ P R : MvPowerSeries τ C, MvPowerSeries.constantCoeff P = 0 →
      MvPowerSeries.constantCoeff R = 0 → MvPowerSeries.coeff (Finsupp.single j 1) (P * R) = 0 := by
    intro P R hP hR
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun ab hab => ?_
    first
      | rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      | rw [Finset.mem_antidiagonal] at hab
      | simp only [Finset.mem_antidiagonal] at hab
    by_cases ha : ab.1 = 0
    · rw [ha, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hP, zero_mul]
    · have hb : ab.2 = 0 := by
        obtain ⟨i, hi⟩ : ∃ i, ab.1 i ≠ 0 := by
          by_contra h
          push_neg at h
          exact ha (Finsupp.ext h)
        have hij : i = j := by
          by_contra hne
          have := congrArg (fun d => d i) hab
          simp only [Finsupp.add_apply, Finsupp.single_apply, Ne.symm hne, if_false] at this
          omega
        subst hij
        ext t
        have := congrArg (fun d => d t) hab
        by_cases ht : t = i
        · subst ht
          simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
          simp only [Finsupp.coe_zero, Pi.zero_apply]
          omega
        · simp only [Finsupp.add_apply, Finsupp.single_apply, Ne.symm ht, if_false] at this
          simp only [Finsupp.coe_zero, Pi.zero_apply]
          omega
      rw [hb, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hR, mul_zero]

  have hpow : ∀ (a : σ) (b : ℕ), b ≠ 0 → MvPowerSeries.constantCoeff (A a ^ b) = 0 := by
    intro a b hb
    rw [map_pow, hA a, zero_pow hb]
  have hprod : ∀ d : σ →₀ ℕ, d ≠ 0 → MvPowerSeries.constantCoeff (d.prod fun s e => A s ^ e) = 0 ∧
      ((∀ k, d ≠ Finsupp.single k 1) →
        MvPowerSeries.coeff (Finsupp.single j 1) (d.prod fun s e => A s ^ e) = 0) := by
    intro d
    refine Finsupp.induction d ?_ ?_
    · intro h
      exact absurd rfl h
    · intro a b g hag hb ih _
      have hP : (Finsupp.single a b + g).prod (fun s e => A s ^ e) = A a ^ b * g.prod (fun s e => A s ^ e) := by
        rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
          show (Finsupp.single a b).prod (fun s e => A s ^ e) = A a ^ b from Finsupp.prod_single_index (pow_zero _)]
      rw [hP]
      refine ⟨by rw [map_mul, hpow a b hb, zero_mul], fun hnot => ?_⟩
      by_cases hg : g = 0
      · subst hg
        rw [Finsupp.prod_zero_index, mul_one]
        have hb1 : b ≠ 1 := by
          intro h1
          subst h1
          exact hnot a (add_zero _)
        obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
        rw [pow_succ]
        exact hmul _ _ (hpow a c (by omega)) (hA a)
      · exact hmul _ _ (hpow a b hb) (ih hg).1
  rw [linear_coeff_eq_coeff_single, MvPowerSeries.coeff_subst hs]
  have hsupp : (Function.support fun d : σ →₀ ℕ => MvPowerSeries.coeff d f •
      MvPowerSeries.coeff (Finsupp.single j 1) (d.prod fun s e => A s ^ e)) ⊆
      ↑(Finset.univ.image fun k : σ => Finsupp.single k 1) := by
    intro d hd
    rw [Function.mem_support] at hd
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    by_contra hne
    push_neg at hne
    apply hd
    by_cases h0 : d = 0
    · subst h0
      rw [Finsupp.prod_zero_index, MvPowerSeries.coeff_one, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero),
        smul_zero]
    · rw [(hprod d h0).2 (fun k h => hne k h.symm), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_image (fun k _ l _ h => Finsupp.single_left_injective one_ne_zero h)]
  refine Finset.sum_congr rfl fun k _ => ?_
  dsimp only
  rw [show (Finsupp.single k 1).prod (fun s e => A s ^ e) = A k ^ 1 from Finsupp.prod_single_index (pow_zero _),
    pow_one, smul_eq_mul, linear_coeff_eq_coeff_single, linear_coeff_eq_coeff_single, mul_comm]

theorem linear_coeff_X_eq_ite {σ : Type} (m j : σ) : lin1 (MvPowerSeries.X m : MvPowerSeries σ C) j = if m = j then 1 else 0 := by
  rw [linear_coeff_eq_coeff_single, MvPowerSeries.coeff_X]
  by_cases h : m = j
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    exact h ((Finsupp.single_left_inj one_ne_zero).mp h').symm

theorem lin_of_add (f : MvPowerSeries (Fin dd) C) (h0 : MvPowerSeries.constantCoeff f = 0)
    (hadd : MvPowerSeries.subst (fun m : Fin dd => (MvPowerSeries.X ((0 : Fin 2), m) + MvPowerSeries.X ((1 : Fin 2), m) : PS C 2 dd)) f =
      MvPowerSeries.subst (fun m : Fin dd => (MvPowerSeries.X ((0 : Fin 2), m) : PS C 2 dd)) f +
        MvPowerSeries.subst (fun m : Fin dd => (MvPowerSeries.X ((1 : Fin 2), m) : PS C 2 dd)) f) :
    f = ∑ j, lin1 f j • (MvPowerSeries.X j : MvPowerSeries (Fin dd) C) := by
  have cS : ∀ m : Fin dd, MvPowerSeries.constantCoeff
      (MvPowerSeries.X ((0 : Fin 2), m) + MvPowerSeries.X ((1 : Fin 2), m) : PS C 2 dd) = 0 := fun m => by
    rw [map_add (f := _), cc_X, cc_X, add_zero]
  set K : Fin 2 × Fin dd → MvPowerSeries (Fin dd) C := P2 MvPowerSeries.X (fun _ => 0) with hK
  have cK : ∀ q, MvPowerSeries.constantCoeff (K q) = 0 := constantCoeff_pair_substitution (fun _ => cc_X _) (fun _ => map_zero _)
  have hder : ∀ i, MvPowerSeries.pderiv (R := C) i f = MvPowerSeries.C (lin1 f i) := by
    intro i
    have h := congrArg (fun G => MvPowerSeries.subst K (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) G)) hadd
    beta_reduce at h
    rw [map_add (f := _), pderiv_subst (og cS), pderiv_subst (og fun _ => cc_X _), pderiv_subst (og fun _ => cc_X _),
      subst_add' cK, subst_sum cK, subst_sum cK, subst_sum cK] at h
    have h1 : ∀ m, MvPowerSeries.subst K (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i)
        (MvPowerSeries.X ((0 : Fin 2), m) + MvPowerSeries.X ((1 : Fin 2), m) : PS C 2 dd) *
        MvPowerSeries.subst (fun m : Fin dd => (MvPowerSeries.X ((0 : Fin 2), m) + MvPowerSeries.X ((1 : Fin 2), m) : PS C 2 dd))
          (MvPowerSeries.pderiv (R := C) m f)) = if m = i then MvPowerSeries.pderiv (R := C) i f else 0 := by
      intro m
      rw [map_add (f := _), MvPowerSeries.pderiv_X_of_ne (fun hh => by simpa using (Prod.ext_iff.1 hh).1), zero_add]
      by_cases hm : m = i
      · subst hm
        rw [MvPowerSeries.pderiv_X_self, one_mul, subst_subst cS cK, if_pos rfl]
        have : (fun s : Fin dd => MvPowerSeries.subst K
            (MvPowerSeries.X ((0 : Fin 2), s) + MvPowerSeries.X ((1 : Fin 2), s) : PS C 2 dd)) = MvPowerSeries.X := by
          funext s
          rw [subst_add' cK, subst_X cK, subst_X cK]
          show MvPowerSeries.X s + 0 = _
          rw [add_zero]
        rw [this, MvPowerSeries.subst_self]
        rfl
      · rw [MvPowerSeries.pderiv_X_of_ne (fun hh => hm (Prod.ext_iff.1 hh).2), zero_mul, subst_zero' cK, if_neg hm]
    have h2 : ∀ m, MvPowerSeries.subst K (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i)
        (MvPowerSeries.X ((0 : Fin 2), m) : PS C 2 dd) *
        MvPowerSeries.subst (fun m : Fin dd => (MvPowerSeries.X ((0 : Fin 2), m) : PS C 2 dd))
          (MvPowerSeries.pderiv (R := C) m f)) = 0 := by
      intro m
      rw [MvPowerSeries.pderiv_X_of_ne (fun hh => by simpa using (Prod.ext_iff.1 hh).1), zero_mul, subst_zero' cK]
    have h3 : ∀ m, MvPowerSeries.subst K (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i)
        (MvPowerSeries.X ((1 : Fin 2), m) : PS C 2 dd) *
        MvPowerSeries.subst (fun m : Fin dd => (MvPowerSeries.X ((1 : Fin 2), m) : PS C 2 dd))
          (MvPowerSeries.pderiv (R := C) m f)) = if m = i then MvPowerSeries.C (lin1 f i) else 0 := by
      intro m
      by_cases hm : m = i
      · subst hm
        rw [MvPowerSeries.pderiv_X_self, one_mul, subst_subst (fun _ => cc_X _) cK, if_pos rfl]
        have : (fun s : Fin dd => MvPowerSeries.subst K (MvPowerSeries.X ((1 : Fin 2), s) : PS C 2 dd)) = fun _ => 0 := by
          funext s
          rw [subst_X cK]
          rfl
        rw [this, subst_zeroPt]
        rfl
      · rw [MvPowerSeries.pderiv_X_of_ne (fun hh => hm (Prod.ext_iff.1 hh).2), zero_mul, subst_zero' cK, if_neg hm]
    rw [Finset.sum_congr rfl fun m _ => h1 m, Finset.sum_congr rfl fun m _ => h2 m,
      Finset.sum_congr rfl fun m _ => h3 m, Finset.sum_const_zero, zero_add, Finset.sum_ite_eq', Finset.sum_ite_eq'] at h
    simpa using h
  ext μ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, smul_eq_mul, MvPowerSeries.coeff_X]
  by_cases hμ : μ = 0
  · subst hμ
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (fun h => by simpa using congrArg (fun x => x j) h), mul_zero]
  · obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hμ (Finsupp.ext hcon)
    obtain ⟨ν, rfl⟩ : ∃ ν : Fin dd →₀ ℕ, μ = ν + Finsupp.single i 1 :=
      ⟨μ - Finsupp.single i 1, (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi))).symm⟩
    have hc := congrArg (MvPowerSeries.coeff ν) (hder i)
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_C] at hc
    have hne : ((ν i : C) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (ν i)
    by_cases hν : ν = 0
    · subst hν
      rw [zero_add, Finset.sum_eq_single i]
      · rw [if_pos rfl, mul_one, linear_coeff_eq_coeff_single]
      · intro j _ hj
        rw [if_neg fun h => hj (Finsupp.single_left_injective one_ne_zero h).symm, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hν] at hc
      rw [(mul_eq_zero.1 hc).resolve_right hne]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg, mul_zero]
      intro h
      have hd := congrArg Finsupp.degree h
      rw [map_add (f := _), Finsupp.degree_single, Finsupp.degree_single] at hd
      exact hν ((Finsupp.degree_eq_zero_iff _).1 (by omega))

end VP

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}

variable (Y : FBChart C V O dd)

theorem mapAt_addAt {ε : Pt C 1 dd} (hε : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0)
    (hadd : comp1 ε (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 ε (pt C (n := 2) dd 0)) (comp1 ε (pt C (n := 2) dd 1)))
    {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    mapAt ε (addAt Y a b) = addAt Y (mapAt ε a) (mapAt ε b) := by
  have h := hadd
  rw [addOf_eq', addOf_eq', comp_eq_map_at, comp_eq_map_at, comp_eq_map_at] at h
  have k0 := cc_pt (C := C) (dd := dd) (0 : Fin 2)
  have k1 := cc_pt (C := C) (dd := dd) (1 : Fin 2)
  have hP := constantCoeff_pair_substitution ha hb
  have e0 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (0 : Fin 2) i)) = a := funext fun i => pair_subst_coordinate ha hb 0 i
  have e1 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (1 : Fin 2) i)) = b := funext fun i => pair_subst_coordinate ha hb 1 i
  funext i
  have h2 := congrArg (MvPowerSeries.subst (P2 a b)) (congrFun h i)
  rw [mapAt_subst hP ε (cc_addAt Y k0 k1), addAt_subst Y hP (cc_mapAt hε k0) (cc_mapAt hε k1)] at h2
  have e2 : (fun i => MvPowerSeries.subst (P2 a b) (addAt Y (pt C dd (0 : Fin 2)) (pt C dd (1 : Fin 2)) i)) =
      addAt Y a b := by
    funext j
    rw [addAt_subst Y hP k0 k1, e0, e1]
  have e3 : (fun i => MvPowerSeries.subst (P2 a b) (mapAt ε (pt C dd (0 : Fin 2)) i)) = mapAt ε a := by
    funext j
    rw [mapAt_subst hP ε k0, e0]
  have e4 : (fun i => MvPowerSeries.subst (P2 a b) (mapAt ε (pt C dd (1 : Fin 2)) i)) = mapAt ε b := by
    funext j
    rw [mapAt_subst hP ε k1, e1]
  rw [e2, e3, e4] at h2
  exact h2

def PhiAt (ε : Pt C 1 dd) (a : Fin dd → MvPowerSeries τ C) (m : Fin dd) : MvPowerSeries τ C :=
  MvPowerSeries.subst (mapAt ε (exAt Y a)) (l Y m)

theorem exAt_subst [Finite τ] {A : τ → MvPowerSeries τ' C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0)
    {u : Fin dd → MvPowerSeries τ C} (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (i : Fin dd) :
    MvPowerSeries.subst A (exAt Y u i) = exAt Y (fun i => MvPowerSeries.subst A (u i)) i := subst_subst hu hA _

variable {ε : Pt C 1 dd} (hε : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0)

include hε in
theorem PhiAt_subst [Finite τ] {A : τ → MvPowerSeries τ' C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0)
    {u : Fin dd → MvPowerSeries τ C} (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (m : Fin dd) :
    MvPowerSeries.subst A (PhiAt Y ε u m) = PhiAt Y ε (fun i => MvPowerSeries.subst A (u i)) m := by
  unfold PhiAt
  rw [subst_subst (cc_mapAt hε (cc_exAt Y hu)) hA]
  congr 1
  funext k
  rw [mapAt_subst hA ε (cc_exAt Y hu)]
  congr 1
  funext i
  exact exAt_subst Y hA hu i

include hε in
theorem PhiAt_add (hadd : comp1 ε (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 ε (pt C (n := 2) dd 0)) (comp1 ε (pt C (n := 2) dd 1)))
    {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (m : Fin dd) :
    PhiAt Y ε (fun i => a i + b i) m = PhiAt Y ε a m + PhiAt Y ε b m := by
  unfold PhiAt
  rw [ex_add Y ha hb, mapAt_addAt Y hε hadd (cc_exAt Y ha) (cc_exAt Y hb),
    l_add_at Y (cc_mapAt hε (cc_exAt Y ha)) (cc_mapAt hε (cc_exAt Y hb))]

theorem linear_coeff_logarithm_eq_ite (m k : Fin dd) : lin1 (l Y m) k = if m = k then 1 else 0 := pderiv_l_zero Y m k

theorem linear_coeff_exponential_eq_ite (m j : Fin dd) : lin1 (e Y m) j = if m = j then 1 else 0 := by
  have h := congrArg (fun f => lin1 f j) (lgex Y m)
  beta_reduce at h
  rw [linear_coeff_subst_chain_rule (cc_e Y), linear_coeff_X_eq_ite] at h
  have h' : ∑ k, lin1 (e Y k) j * lin1 (l Y m) k = lin1 (e Y m) j := by
    simp only [linear_coeff_logarithm_eq_ite, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [h'] at h
  convert h

theorem exAt_X : exAt Y (MvPowerSeries.X : Fin dd → MvPowerSeries (Fin dd) C) = e Y := by
  funext i
  unfold exAt
  rw [MvPowerSeries.subst_self]
  rfl

include hε in
theorem linear_coeff_formal_law_at_X (m j : Fin dd) :
    lin1 (PhiAt Y ε (MvPowerSeries.X : Fin dd → MvPowerSeries (Fin dd) C) m) j =
      MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ε m) := by
  unfold PhiAt
  rw [linear_coeff_subst_chain_rule (cc_mapAt hε (cc_exAt Y fun _ => cc_X _))]
  simp only [linear_coeff_logarithm_eq_ite, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [exAt_X]
  unfold mapAt
  rw [linear_coeff_subst_chain_rule (A := fun q : Fin 1 × Fin dd => e Y q.2) (fun q => cc_e Y q.2), Finset.sum_eq_single ((0 : Fin 1), j)]
  · rw [linear_coeff_exponential_eq_ite, if_pos rfl, one_mul, linear_coeff_eq_coeff_single]
  · intro q _ hq
    rw [linear_coeff_exponential_eq_ite, if_neg, zero_mul]
    intro h
    apply hq
    obtain ⟨q1, q2⟩ := q
    have : q1 = 0 := Subsingleton.elim _ _
    subst this
    exact Prod.ext rfl h
  · intro h; exact absurd (Finset.mem_univ _) h

end VP

theorem endoLog_holds {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) : EndoLogSt Y := by
  intro ε hε hadd τ _ a ha i
  have cX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun _ => VP.cc_X _
  set φ : Fin dd → MvPowerSeries (Fin dd) C := VP.PhiAt Y ε MvPowerSeries.X with hφ
  have cφ : ∀ m, MvPowerSeries.constantCoeff (φ m) = 0 := fun m =>
    VP.cc_subst (VP.cc_mapAt hε (VP.cc_exAt Y cX)) (VP.cc_l Y m)
  have hsub : ∀ {τ' : Type} (b : Fin dd → MvPowerSeries τ' C), (∀ i, MvPowerSeries.constantCoeff (b i) = 0) →
      ∀ m, MvPowerSeries.subst b (φ m) = VP.PhiAt Y ε b m := by
    intro τ' b hb m
    rw [hφ, VP.PhiAt_subst Y hε hb cX]
    congr 1
    funext i
    exact VP.subst_X hb i
  have hlin : ∀ m, φ m = ∑ j, VP.lin1 (φ m) j • (MvPowerSeries.X j : MvPowerSeries (Fin dd) C) := by
    intro m
    refine VP.lin_of_add (φ m) (cφ m) ?_
    rw [hsub _ (fun k => by rw [map_add (f := _), VP.cc_X, VP.cc_X, add_zero]) m, hsub _ (fun _ => VP.cc_X _) m,
      hsub _ (fun _ => VP.cc_X _) m]
    exact VP.PhiAt_add Y hε hadd (fun _ => VP.cc_X _) (fun _ => VP.cc_X _) m
  have hP := VP.cc_mapAt hε (VP.cc_exAt Y ha)
  show VP.mapAt ε (VP.exAt Y a) i = _
  rw [← VP.e_lAt Y hP i]
  show VP.exAt Y (fun m => VP.PhiAt Y ε a m) i = _
  congr 1
  funext m
  rw [← hsub a ha m, hlin m, VP.subst_sum ha]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [VP.subst_smul ha, VP.subst_X ha]
  show VP.lin1 (VP.PhiAt Y ε MvPowerSeries.X m) j • a j = _
  rw [VP.linear_coeff_formal_law_at_X Y hε]

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

private theorem coeff_single_one_mul' (t : Fin 1 × Fin dd) (x y : PS C 1 dd) :
    MvPowerSeries.coeff (Finsupp.single t 1) (x * y) =
      MvPowerSeries.coeff (Finsupp.single t 1) x * MvPowerSeries.constantCoeff y +
        MvPowerSeries.constantCoeff x * MvPowerSeries.coeff (Finsupp.single t 1) y := by
  first
  | (have key : ∀ g : PS C 1 dd, MvPowerSeries.coeff (Finsupp.single t 1) g =
        MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (R := C) t g) := by
      intro g
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
      simp
     rw [key, key, key, Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, map_mul, map_mul]
     ring)
  | (rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
     simp [Finset.Nat.antidiagonal_succ]
     ring)

private theorem coeff_single_one_pow_add_two_eq_zero (x : PS C 1 dd) (hx : MvPowerSeries.constantCoeff x = 0)
    (t : Fin 1 × Fin dd) (k : ℕ) : MvPowerSeries.coeff (Finsupp.single t 1) (x ^ (k + 1 + 1)) = 0 := by
  rw [pow_succ, coeff_single_one_mul']
  simp [hx]

private theorem constantCoeff_and_linear_coeff_finsupp_prod_pow (a : Fin 1 × Fin dd → PS C 1 dd) (hac : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (t : Fin 1 × Fin dd) (d : Fin 1 × Fin dd →₀ ℕ) :
    MvPowerSeries.constantCoeff (d.prod fun s n => a s ^ n) = (if d = 0 then 1 else 0) ∧
      ((∀ s, d ≠ Finsupp.single s 1) →
        MvPowerSeries.coeff (Finsupp.single t 1) (d.prod fun s n => a s ^ n) = 0) := by
  induction d using Finsupp.induction
  next =>
    simp [MvPowerSeries.coeff_one]
  next s b f hs hb ih =>
    have hfs : f s = 0 := by
      by_contra h'
      exact hs (Finsupp.mem_support_iff.mpr h')
    have hne : Finsupp.single s b + f ≠ 0 := by
      intro h
      apply hb
      have h2 := congrArg (fun g : Fin 1 × Fin dd →₀ ℕ => g s) h
      simpa [hfs] using h2
    have hP : (Finsupp.single s b + f).prod (fun s n => a s ^ n) =
        a s ^ b * f.prod (fun s n => a s ^ n) := by
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      congr 1
      exact Finsupp.prod_single_index (pow_zero _)
    rw [hP]
    have hcs : MvPowerSeries.constantCoeff (a s ^ b) = 0 := by
      rw [map_pow, hac s, zero_pow hb]
    constructor
    · rw [map_mul, hcs, zero_mul, if_neg hne]
    · intro hnot
      rw [coeff_single_one_mul', hcs, zero_mul, add_zero]
      by_cases hf : f = 0
      · subst hf
        have hb1 : b ≠ 1 := by
          intro h1
          exact hnot s (by rw [h1, add_zero])
        obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 + 1 := ⟨b - 2, by omega⟩
        rw [coeff_single_one_pow_add_two_eq_zero (a s) (hac s) t k, zero_mul]
      · rw [ih.1, if_neg hf, mul_zero]

private theorem coeff_single_one_ev_eq_sum (f : PS C 1 dd) (ψ : Pt C 1 dd) (hψ : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0)
    (j : Fin dd) :
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ev ![ψ] f) =
      ∑ k, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), k) 1) f *
        MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ψ k) := by
  have hev : ev ![ψ] f = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => ψ p.2) f := by
    unfold ev
    congr 1
    funext ⟨i, k⟩
    rw [Fin.fin_one_eq_zero i]
    rfl
  have hs : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin dd => ψ p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun s => hψ s.2)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => hψ s.2)
    | exact ⟨fun s => by simp [hψ s.2], fun d => Set.toFinite _⟩
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by simp [hψ s.2])
  rw [hev, MvPowerSeries.coeff_subst hs]
  refine (finsum_eq_sum_of_support_subset _ (s := Finset.univ.image fun s => Finsupp.single s 1) ?_).trans ?_
  · intro d hd
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    by_contra hne
    push_neg at hne
    apply hd
    try dsimp only
    rw [(constantCoeff_and_linear_coeff_finsupp_prod_pow _ (fun s => hψ s.2) _ d).2 (fun s h => hne s h.symm), smul_zero]
  · first
    | rw [Finset.sum_image (fun x _ y _ h => Finsupp.single_left_injective one_ne_zero h)]
    | rw [Finset.sum_image ((Finsupp.single_left_injective one_ne_zero).injOn)]
    rw [Fintype.sum_prod_type, Fin.sum_univ_one]
    simp [Finsupp.prod_single_index, smul_eq_mul]

theorem linAct_comp1 (φ ψ : Pt C 1 dd) (hψ : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0) (x : Fin dd → C) :
    linAct (comp1 φ ψ) x = linAct φ (linAct ψ x) := by
  funext i
  simp only [linAct, comp1, coeff_single_one_ev_eq_sum _ ψ hψ, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

theorem linAct_smul (φ : Pt C 1 dd) (c : C) (x : Fin dd → C) : linAct φ (c • x) = c • linAct φ x := by
  funext i
  simp only [linAct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem linAct_sum {ι : Type} (φ : Pt C 1 dd) (s : Finset ι) (x : ι → Fin dd → C) :
    linAct φ (∑ c ∈ s, x c) = ∑ c ∈ s, linAct φ (x c) := by
  funext i
  simp only [linAct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

end Formalism.L2.FormalSeriesBounds
