module

public import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionRingAll
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdOfCoeffSubstXPowNeZero
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfB

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ConstantCoeffUniformiserZero
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfBSingleMem
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.BlockProductRing
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.EigenRingInvariants
namespace DualFramesAlt.eigenRingInvariants

open PowerSeries

noncomputable abbrev Ia {O : Type*} [CommRing O] (a : O) : Ideal (PowerSeries O) := Ideal.span {X - C a}

theorem mk_X {O : Type*} [CommRing O] (a : O) : Ideal.Quotient.mk (Ia a) X = Ideal.Quotient.mk (Ia a) (C a) :=
  Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr dvd_rfl)

section Ev

variable {O : Type*} [CommRing O] [IsLocalRing O]

theorem map_residue_X_sub_C {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) :
    (X - C a : PowerSeries O).map (IsLocalRing.residue O) = X := by
  rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero, sub_zero]

theorem order_map_X_sub_C {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) :
    ((X - C a : PowerSeries O).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))).order.toNat = 1 := by
  change ((X - C a : PowerSeries O).map (IsLocalRing.residue O)).order.toNat = 1
  rw [map_residue_X_sub_C ha, PowerSeries.order_X]
  rfl

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem ev_exists {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) (f : PowerSeries O) :
    ∃ c : O, Ideal.Quotient.mk (Ia a) f = Ideal.Quotient.mk (Ia a) (C c) := by
  have hg : (X - C a : PowerSeries O).map (IsLocalRing.residue O) ≠ 0 := by
    rw [map_residue_X_sub_C ha]
    exact PowerSeries.X_ne_zero
  obtain ⟨q, r, hW⟩ := f.exists_isWeierstrassDivision hg
  obtain ⟨hdeg, heq⟩ := hW
  rw [order_map_X_sub_C ha] at hdeg
  have hr : r = Polynomial.C (r.coeff 0) :=
    Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp (by exact_mod_cast hdeg))
  refine ⟨r.coeff 0, ?_⟩
  rw [heq, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)),
    zero_add]
  congr 1
  conv_lhs => rw [hr]
  exact Polynomial.coe_C _

theorem ev_inj {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) {c c' : O}
    (h : Ideal.Quotient.mk (Ia a) (C c) = Ideal.Quotient.mk (Ia a) (C c')) : c = c' := by
  rw [Ideal.Quotient.eq, ← map_sub] at h
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton.mp h
  have hrec : ∀ n, PowerSeries.coeff (R := O) n H = a * PowerSeries.coeff (R := O) (n + 1) H := by
    intro n
    have hn := congrArg (PowerSeries.coeff (R := O) (n + 1)) hH
    rw [PowerSeries.coeff_C, if_neg (by omega : n + 1 ≠ 0), sub_mul, map_sub, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_C_mul] at hn
    linear_combination -hn
  have hmem : ∀ n, PowerSeries.coeff (R := O) 0 H ∈ (IsLocalRing.maximalIdeal O) ^ n := by
    intro n
    have hpow : PowerSeries.coeff (R := O) 0 H = a ^ n * PowerSeries.coeff (R := O) n H := by
      induction n with
      | zero => simp
      | succ n ih => rw [ih, hrec n, pow_succ]; ring
    rw [hpow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ha n)
  have h0 : PowerSeries.coeff (R := O) 0 H = 0 := by
    apply IsHausdorff.haus' (I := IsLocalRing.maximalIdeal O)
    intro n
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    exact hmem n
  have hc := congrArg (PowerSeries.coeff (R := O) 0) hH
  rw [PowerSeries.coeff_zero_C, sub_mul, map_sub, PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_C_mul, h0,
    mul_zero, sub_zero] at hc
  exact sub_eq_zero.mp hc

theorem ev_zero {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) {c : O}
    (h : Ideal.Quotient.mk (Ia a) (C c) = 0) : c = 0 := by
  exact ev_inj ha (by rw [h, map_zero, map_zero])

end Ev

theorem ev_subst {O : Type*} [CommRing O] {P : PowerSeries O} (hP : constantCoeff P = 0) {a b c : O}
    {F : PowerSeries O}
    (hPb : Ideal.Quotient.mk (Ideal.span {X - C a}) P = Ideal.Quotient.mk (Ideal.span {X - C a}) (C b))
    (hF : Ideal.Quotient.mk (Ideal.span {X - C b}) F = Ideal.Quotient.mk (Ideal.span {X - C b}) (C c)) :
    Ideal.Quotient.mk (Ideal.span {X - C a}) (PowerSeries.subst P F) =
      Ideal.Quotient.mk (Ideal.span {X - C a}) (C c) := by
  have hs : HasSubst P := HasSubst.of_constantCoeff_zero' hP
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton'] at hF
  obtain ⟨k, hk⟩ := hF
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hPb ⊢
  have e : PowerSeries.subst P F - C c = PowerSeries.subst P k * (P - C b) := by
    have := congrArg (PowerSeries.subst P) hk
    rw [subst_mul hs, subst_sub hs, subst_sub hs, subst_X hs, subst_C, subst_C] at this
    exact this.symm
  rw [e]; exact Ideal.mul_mem_left _ _ hPb

section Dvd

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsDomain O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem prod_dvd (T : Finset O) (hT : ∀ t ∈ T, t ∈ IsLocalRing.maximalIdeal O) (f : PowerSeries O)
    (hf : ∀ t ∈ T, Ideal.Quotient.mk (Ia t) f = 0) : (∏ t ∈ T, (X - C t)) ∣ f := by
  classical
  induction T using Finset.induction_on generalizing f with
  | empty => simp
  | @insert t0 T ht0 ih =>
    rw [Finset.prod_insert ht0]
    have h0 : (X - C t0) ∣ f :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (hf t0 (Finset.mem_insert_self _ _)))
    obtain ⟨g, rfl⟩ := h0
    apply mul_dvd_mul_left
    apply ih (fun t ht => hT t (Finset.mem_insert_of_mem ht))
    intro t ht
    have htm := hT t (Finset.mem_insert_of_mem ht)
    obtain ⟨c, hc⟩ := ev_exists htm g
    have hft := hf t (Finset.mem_insert_of_mem ht)
    have key : Ideal.Quotient.mk (Ia t) (C ((t - t0) * c)) = 0 := by
      rw [← hft]
      simp only [map_mul, map_sub, mk_X, hc]
    have hz := ev_zero htm key
    have hne : t - t0 ≠ 0 := sub_ne_zero.mpr (fun h => ht0 (h ▸ ht))
    have hc0 : c = 0 := (mul_eq_zero.mp hz).resolve_left hne
    rw [hc, hc0, map_zero, map_zero]

end Dvd

section Order

variable {O : Type*} [CommRing O] [IsLocalRing O]

theorem card_le_of_dvd {f v k : PowerSeries O} {s : ℕ} (T : Finset O)
    (hT : ∀ t ∈ T, t ∈ IsLocalRing.maximalIdeal O) (hv : IsUnit v)
    (hf : f.map (IsLocalRing.residue O) = (X ^ s * v).map (IsLocalRing.residue O))
    (hk : f = (∏ t ∈ T, (X - C t)) * k) :
    T.card ≤ s ∧ (T.card = s → IsUnit k) := by
  set κ := IsLocalRing.ResidueField O
  have hprod : (∏ t ∈ T, (X - C t) : PowerSeries O).map (IsLocalRing.residue O) = X ^ T.card := by
    rw [map_prod]
    rw [Finset.prod_congr rfl fun t ht => (map_residue_X_sub_C (hT t ht))]
    rw [Finset.prod_const]
  have e : (X : PowerSeries κ) ^ s * v.map (IsLocalRing.residue O) =
      X ^ T.card * k.map (IsLocalRing.residue O) := by
    rw [← map_X (IsLocalRing.residue O), ← map_pow, ← map_mul, ← hf, hk, map_mul, hprod, map_X]
  have hv' : constantCoeff (v.map (IsLocalRing.residue O)) ≠ 0 := by
    have := (hv.map (PowerSeries.map (IsLocalRing.residue O)))
    rw [isUnit_iff_constantCoeff] at this
    exact this.ne_zero
  have hX : (X : PowerSeries κ) ≠ 0 := X_ne_zero
  by_cases hle : T.card ≤ s
  · refine ⟨hle, fun hcs => ?_⟩
    rw [hcs] at e
    have e2 := mul_left_cancel₀ (pow_ne_zero _ hX) e
    rw [isUnit_iff_constantCoeff]
    by_contra hnu
    apply hv'
    rw [e2, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu)]
  · exfalso
    replace hle := not_le.mp hle
    have e2 : (X : PowerSeries κ) ^ s * v.map (IsLocalRing.residue O) =
        X ^ s * (X ^ (T.card - s) * k.map (IsLocalRing.residue O)) := by
      rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle.le]
    have e3 := mul_left_cancel₀ (pow_ne_zero _ hX) e2
    apply hv'
    rw [e3, map_mul, map_pow, constantCoeff_X, zero_pow (by omega), zero_mul]

end Order

end DualFramesAlt.eigenRingInvariants

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries Formalism.IrreducibleCountingLemmas.WindowSums

variable {l : ℕ} [hl : Fact l.Prime]

section O

variable {O : Type*} [CommRing O] [Algebra ℤ_[l] O] {a ζ : O}

end O

end DualFramesAlt.eigenRingInvariants

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries Formalism.IrreducibleCountingLemmas.WindowSums Classical

variable {l : ℕ} [hl : Fact l.Prime]

section Act

variable {O : Type*} [CommRing O] [Algebra ℤ_[l] O]

variable [IsDomain O]

end Act

end DualFramesAlt.eigenRingInvariants

namespace DualFramesAlt.eigenRingInvariants

open PowerSeries Formalism.IrreducibleCountingLemmas.WindowSums Classical

variable {l : ℕ} [hl : Fact l.Prime]

section Fiber

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [Algebra ℤ_[l] O]

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

end Fiber

end DualFramesAlt.eigenRingInvariants
end

namespace DualFramesAlt.BlockProductRing

open PowerSeries

theorem prod_div_block {M : Type*} [CommMonoid M] (m : ℕ) (hm : 0 < m) (g : ℕ → M) (e : ℕ) :
    ∏ k ∈ Finset.range (m * e), g (k / m) = ∏ j ∈ Finset.range e, g j ^ m := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [mul_add_one, Finset.prod_range_add, ih, Finset.prod_range_succ]
    congr 1
    have hc : ∀ x ∈ Finset.range m, g ((m * e + x) / m) = g e := by
      intro x hx
      rw [Finset.mem_range] at hx
      congr 1
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hx, zero_add]
    rw [Finset.prod_congr rfl hc, Finset.prod_const, Finset.card_range]

theorem prod_ite_block {M : Type*} [CommMonoid M] (m : ℕ) (hm : 0 < m) (x : M) (k : ℕ) :
    ∏ i ∈ Finset.range k, (if i / m = k / m then x else 1) = x ^ (k % m) := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  have hset : Finset.filter (fun i => i / m = k / m) (Finset.range k) = Finset.Ico (m * (k / m)) k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hik, hd⟩
      refine ⟨?_, hik⟩
      rw [← hd]
      exact Nat.mul_div_le i m
    · rintro ⟨hle, hik⟩
      refine ⟨hik, le_antisymm (Nat.div_le_div_right hik.le) ?_⟩
      rw [Nat.le_div_iff_mul_le hm, mul_comm]
      exact hle
  rw [hset, Nat.card_Ico]
  have h := Nat.mod_add_div k m
  generalize m * (k / m) = q at h ⊢
  generalize k % m = r at h ⊢
  omega

theorem dvd_of_mk_eq {O : Type*} [CommRing O] {y c : O} {F : PowerSeries O}
    (h : Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y) F = Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y) (C c)) :
    ∃ H, F - C c = (X - C y) * H := by
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  exact ⟨H, hH⟩

theorem mk_eq_of_mem {O : Type*} [CommRing O] {y : O} {F G : PowerSeries O} (h : F - G ∈ DualFramesAlt.eigenRingInvariants.Ia y) :
    Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y) F = Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y) G :=
  Ideal.Quotient.eq.mpr h

theorem mem_of_factor {O : Type*} [CommRing O] (y : O) (F : PowerSeries O) :
    (X - C y) * F ∈ DualFramesAlt.eigenRingInvariants.Ia y :=
  Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)

end DualFramesAlt.BlockProductRing
end

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section unitaryAbsoluteValueBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem u2ringPfB_γ₀_comm (g h : W.Gam) (x : PowerSeries O) :
    W.γ₀ g (W.γ₀ h x) = W.γ₀ h (W.γ₀ g x) := by
  rw [← AlgHom.mul_apply, ← map_mul, mul_comm, map_mul, AlgHom.mul_apply]

theorem u2ringPfB_single_mem (c : ZMod n) (x : PowerSeries O) (hx : ∀ δ ∈ W.DelF, W.γ₀ δ x = x) :
    (Pi.single c x : LetA O n) ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ (Pi.single c x : LetA O n) = Pi.single c x
  intro δ hδ
  funext j
  show W.γ₀ δ ((Pi.single c x : LetA O n) j) = (Pi.single c x : LetA O n) j
  by_cases hj : j = c
  · subst hj
    simp only [Pi.single_eq_same]
    exact hx δ hδ
  · simp only [Pi.single_eq_of_ne hj, map_zero]

theorem u2ringPfB_letter_mem {a : LetA O n} (ha : a ∈ W.AΔ) (i : ZMod n) :
    ∀ δ ∈ W.DelF, W.γ₀ δ (a i) = a i := by
  intro δ hδ
  have h : W.γA δ a = a := ha δ hδ
  exact congrFun h i

theorem u2ringPfB_q₀_ne_zero [IsDomain O] [CharZero O] (hp : PD.p ≠ 0) : W.q₀ ≠ 0 := by
  intro h0
  have h := W.q₀_def
  rw [h0, mul_zero] at h
  have h1 := congrArg (PowerSeries.coeff 1) h.symm
  have e : ((1 + PowerSeries.X : PowerSeries O) ^ PD.p - 1) =
      ((((Polynomial.X + 1) ^ PD.p - 1 : Polynomial O)) : PowerSeries O) := by
    push_cast
    ring
  rw [e, Polynomial.coeff_coe, map_zero] at h1
  simp [Polynomial.coeff_X_add_one_pow, Polynomial.coeff_one, hp] at h1

end unitaryAbsoluteValueBounds

end Formalism.MainNotions.N.Ln34
end
end

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section U2C

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem constantCoeff_uniformiser_zero {s' : ℕ} {π' : LetA O n} (w : (LetA O n)ˣ) (hw : π' = (w : LetA O n) * letπ ^ s')
    (hs : 1 ≤ s') (i : ZMod n) : PowerSeries.constantCoeff (π' i) = 0 := by
  have : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
  rw [this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]

theorem u2ringPfC_subΔ {π' : LetA O n} (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0) :
    ∀ δ ∈ W.DelF, ∀ i (F : PowerSeries O),
      W.γ₀ δ (PowerSeries.subst (π' i) F) = PowerSeries.subst (π' i) F := by
  intro δ hδ i F
  rw [DualFramesAlt.EigenUniformiser.algHom_subst (W.γ₀ δ) (W.γ₀_X δ).1 (hπ0 i)]
  congr 1
  exact congrFun (hπΔ δ hδ) i

theorem u2ringPfC_inj {π' : LetA O n} (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hsub : ∀ a, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W a → ∃! f : ZMod n → PowerSeries O,
      ∀ i, a i = PowerSeries.subst (π' i) (f i))
    (hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0) (c : ZMod n) (F F' : PowerSeries O)
    (hFF : PowerSeries.subst (π' c) F = PowerSeries.subst (π' c) F') : F = F' := by
  have hsub0 : ∀ i, PowerSeries.subst (π' i) (0 : PowerSeries O) = 0 := fun i => by
    rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i)), map_zero]
  have hmem := u2ringPfB_single_mem W c (PowerSeries.subst (π' c) F)
    (fun δ hδ => u2ringPfC_subΔ W hπΔ hπ0 δ hδ c F)
  obtain ⟨f, -, huniq⟩ := hsub _ hmem
  have key : ∀ H, PowerSeries.subst (π' c) H = PowerSeries.subst (π' c) F →
      (Pi.single c H : ZMod n → PowerSeries O) = f := fun H hH => huniq _ (fun i => by
    by_cases hi : i = c
    · subst hi; simp only [Pi.single_eq_same]; exact hH.symm
    · simp only [Pi.single_eq_of_ne hi, hsub0])
  have := congrFun ((key F rfl).trans (key F' hFF.symm).symm) c
  simpa using this

theorem u2ringPfC_pre {π' : LetA O n}
    (hsub : ∀ a, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W a → ∃! f : ZMod n → PowerSeries O,
      ∀ i, a i = PowerSeries.subst (π' i) (f i)) (c : ZMod n) (x : PowerSeries O)
    (hx : ∀ δ ∈ W.DelF, W.γ₀ δ x = x) : ∃ F : PowerSeries O, PowerSeries.subst (π' c) F = x := by
  obtain ⟨f, hf, -⟩ := hsub _ (u2ringPfB_single_mem W c x hx)
  refine ⟨f c, ?_⟩
  have := hf c
  simp only [Pi.single_eq_same] at this
  exact this.symm

theorem u2ringPfC_nu [IsDomain O] [CharZero O] {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hs : 1 ≤ s') (hK : W.gamK = W.gam) (h' : ℕ) :
    ∃ ν : LetA O n, ν ∈ W.AΔ ∧
      ν * W.γA W.gamK (Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h') = Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h' := by
  obtain ⟨hπΔ, -, ⟨w, hw⟩, -, ⟨w₁, hq⟩, -, ⟨w₂, hγ⟩, -⟩ := hR
  have hπ0 := constantCoeff_uniformiser_zero w hw hs
  set Ê := Formalism.MainNotions.DeltaInvariantLattices.Eat E π' with hÊdef
  have hq₀ := u2ringPfB_q₀_ne_zero W PD.hp.ne_zero
  have hÊ0 : ∀ i, Ê i ≠ 0 := by
    intro i h
    apply hq₀
    have e1 : W.q₀ = (w₁ : LetA O n) i * Ê i := congrFun hq i
    rw [e1, h, mul_zero]
  have hπΔ' : ∀ δ ∈ W.DelF, ∀ i, W.γ₀ δ (π' i) = π' i := fun δ hδ i => congrFun (hπΔ δ hδ) i
  have hÊΔ : ∀ δ ∈ W.DelF, ∀ i, W.γ₀ δ (Ê i) = Ê i := by
    intro δ hδ i
    show W.γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply, hπΔ' δ hδ i]
  have hU : ∀ i, ∃ u : PowerSeries O, IsUnit u ∧ W.γ₀ W.gam (Ê i) = Ê i * u := by
    intro i
    have hγi : W.γ₀ W.gam (π' i) - π' i = (w₂ : LetA O n) i * π' i * Ê i := congrFun hγ i
    obtain ⟨D, hD⟩ := Polynomial.sub_dvd_eval_sub (W.γ₀ W.gam (π' i)) (π' i)
      ((E i).map (algebraMap O (PowerSeries O)))
    refine ⟨1 + (w₂ : LetA O n) i * π' i * D, ?_, ?_⟩
    · rw [PowerSeries.isUnit_iff_constantCoeff]
      simp [hπ0 i]
    · have e2 : W.γ₀ W.gam (Ê i) = Polynomial.aeval (W.γ₀ W.gam (π' i)) (E i) :=
        (Polynomial.aeval_algHom_apply (W.γ₀ W.gam) (π' i) (E i)).symm
      have e3 : Ê i = Polynomial.aeval (π' i) (E i) := rfl
      have hD' : Polynomial.aeval (W.γ₀ W.gam (π' i)) (E i) - Polynomial.aeval (π' i) (E i) =
          (W.γ₀ W.gam (π' i) - π' i) * D := by
        rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
          Polynomial.eval₂_eq_eval_map]
        exact hD
      rw [e3] at hγi
      rw [hγi] at hD'
      rw [e2, e3]
      linear_combination hD'
  choose U hUu hUeq using hU
  have hUunit : IsUnit (U : LetA O n) := Pi.isUnit_iff.2 hUu
  set V : LetA O n := ((hUunit.unit⁻¹ : (LetA O n)ˣ) : LetA O n) with hV
  have hVU : V * U = 1 := by rw [hV]; exact hUunit.val_inv_mul
  have hUΔ : ∀ δ ∈ W.DelF, ∀ i, W.γ₀ δ (U i) = U i := by
    intro δ hδ i
    have h1 := congrArg (W.γ₀ δ) (hUeq i)
    rw [u2ringPfB_γ₀_comm, map_mul, hÊΔ δ hδ i, hUeq i] at h1
    exact (mul_left_cancel₀ (hÊ0 i) h1).symm
  refine ⟨V ^ h', ?_, ?_⟩
  · intro δ hδ
    funext i
    show W.γ₀ δ ((V ^ h') i) = (V ^ h') i
    rw [Pi.pow_apply, map_pow]
    congr 1
    have hVi : V i * U i = 1 := congrFun hVU i
    have h1 := congrArg (W.γ₀ δ) hVi
    rw [map_mul, hUΔ δ hδ i, map_one] at h1
    exact mul_right_cancel₀ (hUu i).ne_zero (h1.trans hVi.symm)
  · have hγÊ : W.γA W.gam Ê = Ê * U := funext fun i => hUeq i
    rw [hK, map_pow, hγÊ]
    calc V ^ h' * (Ê * U) ^ h' = (V * U) ^ h' * Ê ^ h' := by ring
      _ = Ê ^ h' := by rw [hVU, one_pow, one_mul]

end U2C

end Formalism.MainNotions.N.Ln34
end
end

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section U2D

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem u2ringPfD_main [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hs : 1 ≤ s') (hK : W.gamK = W.gam)
    (he : e ≤ finrank K₀ K) (c : ZMod n) (a : O) (ha : IsUnit a) (r : Fin e → O)
    (hrm : ∀ j, r j ∈ IsLocalRing.maximalIdeal O)
    (hE : E c = Polynomial.C a * ∏ j, (Polynomial.X - Polynomial.C (r j)))
    (hnr : ∀ (j : Fin e) (w₀ : O), IsUnit w₀ → ∀ t : ℕ, 0 < t →
      (1 + r j * w₀ * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j')) ^ t ≠ 1)
    (h' : ℕ) (hh' : 1 ≤ h') :
    SecondPropositionRingInput W π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c := by
  obtain ⟨ν, hνΔ, hνeq⟩ := u2ringPfC_nu W hR hs hK h'
  obtain ⟨hπΔ, hsub, ⟨w, hw⟩, -, ⟨w₁, hq⟩, -, ⟨w₂, hγ⟩, -⟩ := hR
  have hπ0 := constantCoeff_uniformiser_zero w hw hs
  have hHS : ∀ i, PowerSeries.HasSubst (π' i) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i)
  set ψ : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom (hHS c) with hψdef
  have hψ : ∀ F, ψ F = PowerSeries.subst (π' c) F := fun F => by
    rw [hψdef, PowerSeries.coe_substAlgHom]
  have hψX : ψ PowerSeries.X = π' c := by rw [hψ, PowerSeries.subst_X (hHS c)]
  have hψC : ∀ x : O, ψ (PowerSeries.C x) = PowerSeries.C x := fun x => by
    rw [hψ, PowerSeries.subst_C]; rfl
  have hψΔ : ∀ δ ∈ W.DelF, ∀ F, W.γ₀ δ (ψ F) = ψ F := fun δ hδ F => by
    rw [hψ]; exact u2ringPfC_subΔ W hπΔ hπ0 δ hδ c F
  have hψinj : ∀ F F', ψ F = ψ F' → F = F' := fun F F' h =>
    u2ringPfC_inj W hπΔ hsub hπ0 c F F' (by rwa [hψ, hψ] at h)
  have hpre : ∀ x, (∀ δ ∈ W.DelF, W.γ₀ δ x = x) → ∃ F, ψ F = x := fun x hx => by
    obtain ⟨F, hF⟩ := u2ringPfC_pre W hsub c x hx
    exact ⟨F, by rw [hψ]; exact hF⟩
  have hsingle : ∀ F, (Pi.single c (ψ F) : LetA O n) ∈ W.AΔ := fun F =>
    u2ringPfB_single_mem W c _ (fun δ hδ => hψΔ δ hδ F)
  have halg : ∀ x : O, (algebraMap O (LetA O n) x) c = PowerSeries.C x := fun x => by
    rw [Pi.algebraMap_apply, PowerSeries.algebraMap_apply]; rfl

  set EY : PowerSeries O := PowerSeries.C a * ∏ j, (PowerSeries.X - PowerSeries.C (r j)) with hEY
  have hÊc : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' c = ψ EY := by
    show Polynomial.aeval (π' c) (E c) = ψ EY
    rw [hE, hEY, map_mul, map_prod, map_mul, map_prod, Polynomial.aeval_C, hψC]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_sub, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hψX, hψC]
    rfl
  have hXC0 : ∀ y : O, (PowerSeries.X - PowerSeries.C y : PowerSeries O) ≠ 0 := fun y h => by
    have := congrArg (PowerSeries.coeff 1) h; simp at this
  have hEY0 : EY ≠ 0 := by
    rw [hEY]
    refine mul_ne_zero (fun h => ha.ne_zero ?_) (Finset.prod_ne_zero_iff.2 fun j _ => hXC0 _)
    simpa using congrArg PowerSeries.constantCoeff h
  have hψEY0 : ψ EY ≠ 0 := fun h => hEY0 (hψinj _ _ (by rw [h, map_zero]))
  have hπc0 : π' c ≠ 0 := by
    have : π' c = (w : LetA O n) c * PowerSeries.X ^ s' := by rw [hw]; rfl
    rw [this]
    exact mul_ne_zero (w.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)).ne_zero
      (pow_ne_zero _ PowerSeries.X_ne_zero)

  have hγc : W.γ₀ W.gam (π' c) = π' c + (w₂ : LetA O n) c * π' c * ψ EY := by
    have e1 : W.γ₀ W.gam (π' c) - π' c = (w₂ : LetA O n) c * π' c * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' c :=
      congrFun hγ c
    rw [← hÊc, ← e1]; ring
  have hw2Δ : ∀ δ ∈ W.DelF, W.γ₀ δ ((w₂ : LetA O n) c) = (w₂ : LetA O n) c := by
    intro δ hδ
    have hπc : W.γ₀ δ (π' c) = π' c := congrFun (hπΔ δ hδ) c
    have h1 := congrArg (W.γ₀ δ) hγc
    rw [u2ringPfB_γ₀_comm, hπc, map_add (f := _), map_mul, map_mul, hπc, hψΔ δ hδ] at h1
    have h2 : (W.γ₀ δ ((w₂ : LetA O n) c) - (w₂ : LetA O n) c) * (π' c * ψ EY) = 0 := by
      linear_combination h1.symm.trans hγc
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right (mul_ne_zero hπc0 hψEY0))
  obtain ⟨Ŵ, hŴ⟩ := hpre _ hw2Δ
  have hŴ0 : IsUnit (PowerSeries.constantCoeff Ŵ) := by
    have h1 : IsUnit ((w₂ : LetA O n) c) :=
      w₂.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)
    rw [← hŴ, hψ, DualFramesAlt.EigenUniformiser.subst_eq_C_add (hπ0 c), PowerSeries.isUnit_iff_constantCoeff] at h1
    simpa [hπ0 c] using h1
  set Gt : PowerSeries O := 1 + Ŵ * EY with hGt
  set XG : PowerSeries O := PowerSeries.X * Gt with hXG
  have hXG0 : PowerSeries.constantCoeff XG = 0 := by
    rw [hXG, map_mul, PowerSeries.constantCoeff_X, zero_mul]
  have hHSXG := PowerSeries.HasSubst.of_constantCoeff_zero' hXG0
  set Γ : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom hHSXG with hΓdef
  have hΓ : ∀ F, Γ F = PowerSeries.subst XG F := fun F => by rw [hΓdef, PowerSeries.coe_substAlgHom]
  have hΓX : Γ PowerSeries.X = XG := by rw [hΓ, PowerSeries.subst_X hHSXG]
  have hΓC : ∀ x : O, Γ (PowerSeries.C x) = PowerSeries.C x := fun x => by
    rw [hΓ, PowerSeries.subst_C]; rfl
  have hγπc : W.γ₀ W.gam (π' c) = ψ XG := by
    rw [hγc, hXG, hGt]
    simp only [map_mul, map_add (f := _), map_one, hψX, hŴ]
    ring
  have hγψ : ∀ F, W.γ₀ W.gam (ψ F) = ψ (Γ F) := by
    intro F
    rw [hψ F, DualFramesAlt.EigenUniformiser.algHom_subst (W.γ₀ W.gam) (W.γ₀_X _).1 (hπ0 c), hγπc, hψ XG, hΓ F,
      hψ (PowerSeries.subst XG F), PowerSeries.subst_comp_subst_apply hHSXG (hHS c)]

  let θ : Fin e → PowerSeries O := fun j => 1 + PowerSeries.X * Ŵ * PowerSeries.C a *
      ∏ j' ∈ Finset.univ.erase j, (PowerSeries.X - PowerSeries.C (r j'))
  have hEYsplit : ∀ j, EY = (PowerSeries.X - PowerSeries.C (r j)) *
      (PowerSeries.C a * ∏ j' ∈ Finset.univ.erase j, (PowerSeries.X - PowerSeries.C (r j'))) := by
    intro j; rw [hEY, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]; ring
  have hΓlin : ∀ j, Γ (PowerSeries.X - PowerSeries.C (r j)) =
      (PowerSeries.X - PowerSeries.C (r j)) * θ j := by
    intro j
    rw [map_sub, hΓX, hΓC, hXG, hGt, hEYsplit j]
    ring
  have hΓEY : Γ EY = EY * ∏ j, θ j := by
    conv_lhs => rw [hEY]
    rw [map_mul, map_prod, hΓC, Finset.prod_congr rfl fun j _ => hΓlin j, Finset.prod_mul_distrib, hEY]
    ring

  obtain ⟨nh, hnh⟩ := hpre _ (u2ringPfB_letter_mem W hνΔ c)
  have hnθ : nh * (∏ j, θ j) ^ h' = 1 := by
    have h2 : ν c * W.γ₀ W.gamK (Formalism.MainNotions.DeltaInvariantLattices.Eat E π' c ^ h') = Formalism.MainNotions.DeltaInvariantLattices.Eat E π' c ^ h' :=
      congrFun hνeq c
    rw [hK, map_pow, hÊc, hγψ, ← hnh, ← map_pow ψ (Γ EY) h', ← map_pow ψ EY h', ← map_mul,
      hΓEY] at h2
    have h3 := hψinj _ _ h2
    have h4 : EY ^ h' * (nh * (∏ j, θ j) ^ h' - 1) = 0 := by linear_combination h3
    exact sub_eq_zero.1 ((mul_eq_zero.1 h4).resolve_left (pow_ne_zero _ hEY0))

  have hm : 0 < 2 * h' := by omega
  set m := 2 * h' with hmdef
  set NR := m * e with hNR
  let rI : ℕ → O := fun k => if h : k < e then r ⟨k, h⟩ else 0
  have hrI : ∀ j : Fin e, rI j = r j := fun j => by simp [rI, j.2]
  have hdiv : ∀ k, k < NR → k / m < e := fun k hk => Nat.div_lt_of_lt_mul hk
  let root : ℕ → O := fun k => if k < NR then rI (k / m) else 0
  have hrootm : ∀ k, root k ∈ IsLocalRing.maximalIdeal O := by
    intro k
    simp only [root, rI]
    split_ifs
    · exact hrm _
    · exact Ideal.zero_mem _
    · exact Ideal.zero_mem _
  let φY : ℕ → PowerSeries O := fun k =>
    if k < NR then PowerSeries.X - PowerSeries.C (root k) else PowerSeries.C (a ^ m) * PowerSeries.X
  let θ' : ℕ → PowerSeries O := fun j => if h : j < e then θ ⟨j, h⟩ else 1
  let θY : ℕ → PowerSeries O := fun k => if k < NR then θ' (k / m) else Gt
  let f : ℕ → LetA O n := fun k =>
    if k < NR then π' - algebraMap O (LetA O n) (root k) else algebraMap O (LetA O n) (a ^ m) * π'
  have hfc : ∀ k, f k c = ψ (φY k) := by
    intro k
    simp only [f, φY]
    split_ifs
    · rw [Pi.sub_apply, halg, map_sub, hψX, hψC]
    · rw [Pi.mul_apply, halg, map_mul, hψX, hψC]
  have hfΔ : ∀ k, f k ∈ W.AΔ := by
    intro k
    simp only [f]
    split_ifs
    · exact W.AΔ.sub_mem hπΔ (W.AΔ.algebraMap_mem _)
    · exact W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) hπΔ
  have hφroot : ∀ k, ∃ u : PowerSeries O, PowerSeries.X - PowerSeries.C (root k) = φY k * u := by
    intro k
    by_cases hk : k < NR
    · exact ⟨1, by simp only [φY, if_pos hk, mul_one]⟩
    · refine ⟨PowerSeries.C (((ha.unit⁻¹ : Oˣ) : O) ^ m), ?_⟩
      simp only [φY, root, if_neg hk, map_zero, sub_zero]
      rw [mul_comm, ← mul_assoc, ← map_mul, ← mul_pow, ha.val_inv_mul, one_pow, map_one, one_mul]
  have hΓφ : ∀ k, Γ (φY k) = φY k * θY k := by
    intro k
    by_cases hk : k < NR
    · have hj := hdiv k hk
      simp only [φY, θY, θ', root, rI, if_pos hk, dif_pos hj]
      exact hΓlin ⟨k / m, hj⟩
    · simp only [φY, θY, if_neg hk]
      rw [map_mul, hΓC, hΓX, hXG]
      ring
  have hPY : ∀ k, (∏ j ∈ Finset.range k, f j) c = ψ (∏ j ∈ Finset.range k, φY j) := by
    intro k
    rw [Finset.prod_apply, map_prod]
    exact Finset.prod_congr rfl fun j _ => hfc j
  have hΓP : ∀ k, Γ (∏ j ∈ Finset.range k, φY j) =
      (∏ j ∈ Finset.range k, φY j) * ∏ j ∈ Finset.range k, θY j := by
    intro k
    rw [map_prod, Finset.prod_congr rfl fun j _ => hΓφ j, Finset.prod_mul_distrib]
  have hprod : ∏ k ∈ Finset.range (NR + 1), φY k = PowerSeries.X * EY ^ m := by
    have h0 : φY NR = PowerSeries.C (a ^ m) * PowerSeries.X := by
      simp only [φY, if_neg (lt_irrefl NR)]
    have h1 : ∏ k ∈ Finset.range NR, φY k =
        ∏ k ∈ Finset.range NR, (PowerSeries.X - PowerSeries.C (rI (k / m))) :=
      Finset.prod_congr rfl fun k hk => by simp only [φY, root, if_pos (Finset.mem_range.1 hk)]
    have h3 := DualFramesAlt.BlockProductRing.prod_div_block m hm (fun j => PowerSeries.X - PowerSeries.C (rI j)) e
    have h2 : ∏ j ∈ Finset.range e, (PowerSeries.X - PowerSeries.C (rI j)) =
        ∏ j, (PowerSeries.X - PowerSeries.C (r j)) := by
      rw [← Fin.prod_univ_eq_prod_range]
      exact Finset.prod_congr rfl fun j _ => by rw [hrI j]
    rw [Finset.prod_range_succ, h0, h1, hNR, h3, Finset.prod_pow,
      h2, hEY, mul_pow, map_pow]
    ring

  let ρ : ℕ → PowerSeries O := fun k => nh * ∏ i ∈ Finset.range k, θY i
  let mkI := fun x : O => Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia x)
  let cc : ℕ → O := fun k => Classical.choose (DualFramesAlt.eigenRingInvariants.ev_exists (hrootm k) (ρ k))
  have hcc : ∀ k, (mkI (root k)) (ρ k) = (mkI (root k)) (PowerSeries.C (cc k)) := by
    intro k
    exact Classical.choose_spec (DualFramesAlt.eigenRingInvariants.ev_exists (hrootm k) (ρ k))
  have hmkΓ : ∀ k F, (mkI (root k)) (Γ F) = (mkI (root k)) F := by
    intro k F
    obtain ⟨c₀, hc₀⟩ := DualFramesAlt.eigenRingInvariants.ev_exists (hrootm k) F
    have hXGr : (mkI (root k)) XG = (mkI (root k)) (PowerSeries.C (root k)) := by
      apply DualFramesAlt.BlockProductRing.mk_eq_of_mem
      by_cases hkN : k < NR
      · have hj := hdiv k hkN
        have hrk : root k = r ⟨k / m, hj⟩ := by simp [root, rI, hkN, hj]
        have key : XG - PowerSeries.C (root k) = (PowerSeries.X - PowerSeries.C (root k)) *
            (1 + PowerSeries.X * Ŵ * (PowerSeries.C a *
              ∏ j' ∈ Finset.univ.erase ⟨k / m, hj⟩, (PowerSeries.X - PowerSeries.C (r j')))) := by
          rw [hXG, hGt, hEYsplit ⟨k / m, hj⟩, hrk]; ring
        rw [key]; exact DualFramesAlt.BlockProductRing.mem_of_factor _ _
      · have hrk : root k = 0 := by simp [root, hkN]
        have key : XG - PowerSeries.C (root k) = (PowerSeries.X - PowerSeries.C (root k)) * Gt := by
          rw [hXG, hrk, map_zero, sub_zero, sub_zero]
        rw [key]; exact DualFramesAlt.BlockProductRing.mem_of_factor _ _
    rw [hΓ, DualFramesAlt.eigenRingInvariants.ev_subst hXG0 hXGr hc₀, hc₀]
  refine ⟨?_, ?_, ⟨1 + (w₂ : LetA O n) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π', ?_, ?_⟩, ν, hνΔ, hνeq, NR + 1, f, cc,
    hfΔ, ?_, ?_, ?_, ?_⟩
  · rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  · have h1 := Formalism.MainNotions.LiftingTheory.liftb_q_unit W
    rw [hq, map_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  · exact gradNPf_fΔ W s' w π' _ hw hπΔ (by linear_combination hγ)
  · rw [hK]; linear_combination hγ
  · funext i
    by_cases hi : i = c
    · rw [hi]
      simp only [Pi.mul_apply]
      congr 1
      rw [hPY, hprod, map_mul, map_pow, hψX, ← hÊc]
      rfl
    · simp [letE, hi]
  · intro k hk x hx
    obtain ⟨F, hF⟩ := hpre _ (u2ringPfB_letter_mem W hx c)
    obtain ⟨a₀, ha₀⟩ := DualFramesAlt.eigenRingInvariants.ev_exists (hrootm k) F
    obtain ⟨H, hH⟩ := DualFramesAlt.BlockProductRing.dvd_of_mk_eq ha₀
    obtain ⟨u, hu⟩ := hφroot k
    refine ⟨a₀, Pi.single c (ψ (u * H)), hsingle _, ?_⟩
    funext i
    by_cases hi : i = c
    · rw [hi]
      simp only [Pi.mul_apply, Pi.add_apply, Pi.single_eq_same]
      congr 1
      rw [halg, hfc, ← hF, ← hψC, ← map_mul, ← map_add (f := _)]
      congr 1
      linear_combination hH + H * hu
    · simp [letE, hi]
  · intro k hk x hx
    obtain ⟨F, hF⟩ := hpre _ (u2ringPfB_letter_mem W hx c)
    have hZ0 : (mkI (root k)) (ρ k * Γ F - PowerSeries.C (cc k) * F) =
        (mkI (root k)) (PowerSeries.C 0) := by
      rw [map_sub, map_mul (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia (root k))) (ρ k) (Γ F),
        map_mul (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia (root k))) (PowerSeries.C (cc k)) F, hcc k, hmkΓ,
        map_zero, sub_self, map_zero]
    obtain ⟨Z', hZ'⟩ := DualFramesAlt.BlockProductRing.dvd_of_mk_eq hZ0
    rw [map_zero, sub_zero] at hZ'
    obtain ⟨u, hu⟩ := hφroot k
    refine ⟨Pi.single c (ψ (u * Z')), hsingle _, ?_⟩
    funext i
    by_cases hi : i = c
    · rw [hi]
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.single_eq_same]
      congr 1
      have hγA : ∀ (g : W.Gam) (y : LetA O n), (W.γA g y) c = W.γ₀ g (y c) := fun _ _ => rfl
      rw [hγA, Pi.mul_apply, hK, hPY, ← hF, ← map_mul, hγψ, ← hnh, halg, ← hψC, hPY (k + 1),
        ← map_mul, ← map_mul, ← map_mul, ← map_sub]
      congr 1
      rw [map_mul, hΓP, Finset.prod_range_succ]
      simp only [ρ] at hZ'
      linear_combination (∏ j ∈ Finset.range k, φY j) * hZ' + (∏ j ∈ Finset.range k, φY j) * Z' * hu
    · simp [letE, hi]
  · have hθother : ∀ j j' : Fin e, j ≠ j' → (mkI (r j)) (θ j') = 1 := by
      intro j j' hjj'
      rw [← map_one (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia (r j)))]
      apply DualFramesAlt.BlockProductRing.mk_eq_of_mem
      have hjmem : j ∈ Finset.univ.erase j' := Finset.mem_erase.2 ⟨hjj', Finset.mem_univ j⟩
      have key : θ j' - 1 = (PowerSeries.X - PowerSeries.C (r j)) * (PowerSeries.X * Ŵ * PowerSeries.C a *
          ∏ i ∈ (Finset.univ.erase j').erase j, (PowerSeries.X - PowerSeries.C (r i))) := by
        simp only [θ]
        rw [← Finset.mul_prod_erase _ _ hjmem]; ring
      rw [key]; exact DualFramesAlt.BlockProductRing.mem_of_factor _ _
    have hcval : ∀ j : Fin e, ∃ cj : O, IsUnit cj ∧ (∀ t : ℕ, 0 < t → cj ^ t ≠ 1) ∧
        (mkI (r j)) (θ j) = (mkI (r j)) (PowerSeries.C cj) := by
      intro j
      obtain ⟨wj, hwj⟩ := DualFramesAlt.eigenRingInvariants.ev_exists (hrm j) Ŵ
      have hwju : IsUnit wj := by
        obtain ⟨H, hH⟩ := DualFramesAlt.BlockProductRing.dvd_of_mk_eq hwj
        have h0 := congrArg PowerSeries.constantCoeff hH
        simp only [map_sub, map_mul, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C,
          zero_sub] at h0
        by_contra hnu
        have hwm : wj ∈ IsLocalRing.maximalIdeal O :=
          (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
        have hŴm : PowerSeries.constantCoeff Ŵ ∈ IsLocalRing.maximalIdeal O := by
          have e0 : PowerSeries.constantCoeff Ŵ = wj + -r j * PowerSeries.constantCoeff H := by
            linear_combination h0
          rw [e0]
          exact Ideal.add_mem _ hwm (Ideal.mul_mem_right _ _ ((Ideal.neg_mem_iff _).2 (hrm j)))
        exact (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hŴm)) hŴ0
      refine ⟨1 + r j * wj * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j'), ?_, hnr j wj hwju, ?_⟩
      · by_contra hnu
        have h1 : 1 + r j * wj * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j') ∈
            IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
        have h2 : r j * wj * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j') ∈
            IsLocalRing.maximalIdeal O :=
          Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (hrm j)))
        have h3 := Ideal.sub_mem _ h1 h2
        rw [add_sub_cancel_right] at h3
        exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h3)
      · simp only [mkI, θ, map_add (f := _), map_one, map_mul, map_prod, map_sub, DualFramesAlt.eigenRingInvariants.mk_X, hwj]
    have hcount : (Finset.range (NR + 1)).filter (fun k => cc k = 1) ⊆
        ((Finset.range e).image fun j => m * j + h') ∪ {NR} := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hkN, hk1⟩ := hk
      rcases Nat.lt_or_ge k NR with hlt | hge
      · apply Finset.mem_union_left
        have hj := hdiv k hlt
        obtain ⟨cj, hcju, hcjt, hcjmk⟩ := hcval ⟨k / m, hj⟩
        have hrk : root k = r ⟨k / m, hj⟩ := by simp [root, rI, hlt, hj]
        have hθY : ∀ i ∈ Finset.range k, (mkI (r ⟨k / m, hj⟩)) (θY i) =
            if i / m = k / m then (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) else 1 := by
          intro i hi
          have hiN : i < NR := lt_trans (Finset.mem_range.1 hi) hlt
          have hij := hdiv i hiN
          simp only [θY, θ', if_pos hiN, dif_pos hij]
          split_ifs with hik
          · have e0 : (⟨i / m, hij⟩ : Fin e) = ⟨k / m, hj⟩ := Fin.ext hik
            rw [e0]; exact hcjmk
          · exact hθother _ _ (fun h => hik (congrArg Fin.val h).symm)
        have hprodθ : (mkI (r ⟨k / m, hj⟩)) (∏ j, θ j) = (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) := by
          rw [map_prod, Finset.prod_eq_single ⟨k / m, hj⟩
            (fun j' _ hne => hθother _ _ (Ne.symm hne)) (fun h => absurd (Finset.mem_univ _) h)]
          exact hcjmk
        have hn : (mkI (r ⟨k / m, hj⟩)) nh * (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) ^ h' = 1 := by
          have e0 := congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia (r ⟨k / m, hj⟩))) hnθ
          rwa [map_mul, map_pow, hprodθ, map_one] at e0
        have hρ : (mkI (r ⟨k / m, hj⟩)) (ρ k) =
            (mkI (r ⟨k / m, hj⟩)) nh * (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) ^ (k % m) := by
          rw [show ρ k = nh * ∏ i ∈ Finset.range k, θY i from rfl, map_mul, map_prod,
            Finset.prod_congr rfl hθY, DualFramesAlt.BlockProductRing.prod_ite_block m hm _ k]
        have hkey : cc k * cj ^ h' = cj ^ (k % m) := by
          apply DualFramesAlt.eigenRingInvariants.ev_inj (hrm ⟨k / m, hj⟩)
          have h1 := hcc k
          rw [hrk, hρ] at h1
          have e1 : (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C (cc k * cj ^ h')) =
              (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C (cc k)) * (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) ^ h' := by
            simp only [map_mul, map_pow]
          have e2 : (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C (cj ^ (k % m))) =
              (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) ^ (k % m) := by
            simp only [map_pow]
          rw [e1, e2, ← h1]
          linear_combination (mkI (r ⟨k / m, hj⟩)) (PowerSeries.C cj) ^ (k % m) * hn
        rw [hk1, one_mul] at hkey
        have ht : k % m = h' := by
          rcases lt_trichotomy (k % m) h' with h1 | h1 | h1
          · exfalso
            apply hcjt (h' - k % m) (by omega)
            have e0 : cj ^ (k % m) * (cj ^ (h' - k % m) - 1) = 0 := by
              rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h1.le, hkey, sub_self]
            exact sub_eq_zero.1 ((mul_eq_zero.1 e0).resolve_left (pow_ne_zero _ hcju.ne_zero))
          · exact h1
          · exfalso
            apply hcjt (k % m - h') (by omega)
            have e0 : cj ^ h' * (cj ^ (k % m - h') - 1) = 0 := by
              rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h1.le, hkey, sub_self]
            exact sub_eq_zero.1 ((mul_eq_zero.1 e0).resolve_left (pow_ne_zero _ hcju.ne_zero))
        rw [Finset.mem_image]
        refine ⟨k / m, Finset.mem_range.2 hj, ?_⟩
        have e0 := Nat.div_add_mod k m
        rw [ht] at e0; exact e0
      · have e0 : k = NR := by omega
        exact Finset.mem_union_right _ (Finset.mem_singleton.2 e0)
    calc ((Finset.range (NR + 1)).filter fun k => cc k = 1).card
        ≤ (((Finset.range e).image fun j => m * j + h') ∪ {NR}).card := Finset.card_le_card hcount
      _ ≤ ((Finset.range e).image fun j => m * j + h').card + ({NR} : Finset ℕ).card :=
          Finset.card_union_le _ _
      _ ≤ e + 1 := by
        rw [Finset.card_singleton]
        exact Nat.add_le_add_right (Finset.card_image_le.trans (by rw [Finset.card_range])) 1
      _ ≤ finrank K₀ K + 1 := by omega

end U2D

end Formalism.MainNotions.N.Ln34
