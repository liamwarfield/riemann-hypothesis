module

public import Formalism.LocalToGlobal.CharacterGerms.CoeffFirstPairingLinear
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieGermI
namespace Formalism.L2.FormalSeriesBounds

theorem germIAll_holds : GermIAllSt := fun _ _ _ _ _ _ _ _ Y => germI_holds Y

end Formalism.L2.FormalSeriesBounds
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieVal
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

structure LetSys (C : Type) [Field C] (dd : ℕ) where
  ι : ℕ → Type
  fin : ∀ N, Fintype (ι N)
  cp : ∀ N, ι N → Fin N
  uv : ∀ N, ι N → Fin dd → C
  FF : ∀ N, Set (MvPolynomial (ι N) C)

attribute [instance] LetSys.fin

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.nab (Y : FBChart C V O dd) (Ls : LetSys C dd) (n : ℕ) (f : PS C n dd) (P : MvPolynomial (Ls.ι n) C) : C :=
  nabValN Y.B C Y.h Y.w0 Y.k f (Ls.cp n) (Ls.uv n) P

def FBChart.valSet (Y : FBChart C V O dd) (Ls : LetSys C dd) (n : ℕ) : Set (WithTop ℝ) :=
  {x | ∃ P ∈ Ls.FF n, ∃ f : PS C n dd, IntS V f ∧ x = V.v (Y.nab Ls n f P)}

def FBChart.nuPlE (Y : FBChart C V O dd) (Ls : LetSys C dd) (n : ℕ) : EReal :=
  ⨅ x ∈ Y.valSet Ls n, (WithBot.some x : WithBot (WithTop ℝ))

theorem map_prod_add (V : VF C) {α : Type} (s : Finset α) (x : α → C) : V.v (∏ o ∈ s, x o) = ∑ o ∈ s, V.v (x o) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, AddValuation.map_one]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

variable {d : ℕ} [NeZero d]

section One

variable {I : Fin 2 → Type} [∀ g, Fintype (I g)]

variable (Y : FBChart C V O dd) (p : PairData Y d I) (H : (Y.raw p).Hyps V) (Ls : LetSys C dd) (n : ℕ)

end One

section Orb

variable {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

abbrev WVO (I : Orb → Fin 2 → Type) := Σ o : Orb, WV (I o)

def IsImgO (X : ∀ o, RawChart C d (I o) (Fin dd)) {N : ℕ} {ι : Type} (cp : ι → Fin N) (uv : ι → Fin dd → C)
    (P : MvPolynomial ι C) (Q : MvPolynomial (Fin N × WVO I) C) : Prop :=
  ∃ co : ι → WVO I → C, (∀ ℓ ∈ P.vars, uv ℓ = ∑ w : WVO I, co ℓ w • (X w.1).u w.2.1 w.2.2) ∧
    Q = MvPolynomial.aeval
      (fun ℓ => ∑ w : WVO I, MvPolynomial.C (co ℓ w) * MvPolynomial.X (cp ℓ, w)) P

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)

def PairsSep : Prop :=
  ∀ x x' : Orb × Fin 2 × ZMod d, x ≠ x' →
    ∃ a : O, V.v ((p x.1).em x.2.1 x.2.2 a - (p x'.1).em x'.2.1 x'.2.2 a) = 0

def toAll {N : ℕ} (o : Orb) (Q : MvPolynomial (Fin N × WV (I o)) C) : MvPolynomial (Fin N × WVO I) C :=
  MvPolynomial.rename (fun x : Fin N × WV (I o) => (x.1, (⟨o, x.2⟩ : WVO I))) Q

def ValEqPSt : Prop :=
  PairsSep Y p → ∀ P ∈ Ls.FF n, ∀ Po : ∀ o, MvPolynomial (Fin n × WV (I o)) C,
    IsImgO (fun o => Y.raw (p o)) (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o)) →
    ∀ kind : Orb → Fin n → Option (Fin 2 × ZMod d × ZMod d),
    (∀ o, RowsOK ((Y.raw (p o)).rowData (H o)).G ((Y.raw (p o)).rowData (H o)).Alt (Po o) (kind o)) →
    ∀ (S : ∀ o g, Sys (((Y.raw (p o)).rowData (H o)).G g)) (t : ∀ o g, I o g → MvPowerSeries (I o g) C),
    (∀ o g, (S o g).IsT (t o g)) →
    ∀ gr : ∀ o, Fin n → MvPowerSeries (WV (I o)) C, (∀ o ρ, gr o ρ ∈ IntGerm V (t o)) →
      ∃ f : PS C n dd, IntS V f ∧
        Y.nab Ls n f P = ∏ o, ValOf ((Y.raw (p o)).rowData (H o)).hL (Po o) (kind o) (gr o)

end Orb

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqSum2
section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqOf
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds PartialDerivEval

variable {C : Type} [Field C]

def RawChart.expG {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} (X : RawChart C d I κ) (g : Fin 2)
    (i : κ) : MvPowerSeries (I g) C :=
  MvPowerSeries.subst (fun j : κ => ∑ c : I g, X.u g c j • (MvPowerSeries.X c : MvPowerSeries (I g) C)) (X.ex i)

namespace RowTiePCEq

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem hasSubst_X (g : Fin 2) : MvPowerSeries.HasSubst
    (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _

theorem upG_eq (g : Fin 2) (F : MvPowerSeries (I g) C) :
    upG g F = MvPowerSeries.substAlgHom (hasSubst_X (C := C) g) F := by
  rw [MvPowerSeries.substAlgHom_apply]
  rfl

theorem upG_const (g : Fin 2) {F : MvPowerSeries (I g) C} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (upG g F) = 0 :=
  constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) hF

theorem upG_subst {σ : Type} [Finite σ] (g : Fin 2) {a : σ → MvPowerSeries (I g) C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) :
    upG g (MvPowerSeries.subst a f) = MvPowerSeries.subst (fun s => upG g (a s)) f := by
  unfold upG
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) (hasSubst_X g)]

theorem upG_X (g : Fin 2) (c : I g) :
    upG g (MvPowerSeries.X c : MvPowerSeries (I g) C) = MvPowerSeries.X (⟨g, c⟩ : WV I) := by
  unfold upG
  rw [MvPowerSeries.subst_X (hasSubst_X g)]

theorem intS_upG {V : VF C} (g : Fin 2) {F : MvPowerSeries (I g) C} (hF : IntS V F) : IntS V (upG g F) :=
  IntS.subst (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => intS_X _) hF

theorem lin_const {κ : Type} (X : RawChart C d I κ) (g : Fin 2) (j : κ) :
    MvPowerSeries.constantCoeff (∑ c : I g, X.u g c j • (MvPowerSeries.X c : MvPowerSeries (I g) C)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_smul,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X, mul_zero]

theorem expPt_eq {κ : Type} [Fintype κ] (X : RawChart C d I κ) (g : Fin 2) (i : κ) :
    X.expPt g i = upG g (X.expG g i) := by
  unfold RawChart.expG
  rw [upG_subst g (lin_const X g)]
  unfold RawChart.expPt
  congr 1
  funext j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [upG_eq, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, ← upG_eq, upG_X]

def tW (t : ∀ g, I g → MvPowerSeries (I g) C) : WV I → MvPowerSeries (WV I) C := fun w => upG w.1 (t w.1 w.2)

theorem tW_const {t : ∀ g, I g → MvPowerSeries (I g) C} (ht : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0) :
    ∀ w, MvPowerSeries.constantCoeff (tW t w) = 0 := fun w => upG_const _ (ht _ _)

theorem subst_tW_upG {t : ∀ g, I g → MvPowerSeries (I g) C} (ht : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0)
    (g : Fin 2) (f : MvPowerSeries (I g) C) :
    MvPowerSeries.subst (tW t) (upG g f) = upG g (MvPowerSeries.subst (t g) f) := by
  rw [upG_subst g (ht g) f]
  show MvPowerSeries.subst (tW t) (MvPowerSeries.subst _ f) = _
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_X g)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (tW_const ht))]
  congr 1
  funext c
  rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero (tW_const ht))]
  rfl

theorem coeff_toLeaf {V : VF C} {J : Fin 2 → Type} [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g))
    (g : Fin 2) (a a' : ZMod d) (F : MvPowerSeries (WV I) C) (μ : WV I →₀ ℕ) :
    MvPowerSeries.coeff μ (toLeaf G g a a' F) =
      if ∀ w ∈ μ.support, OnLeafV G g a a' w then MvPowerSeries.coeff μ F else 0 := rfl

def toLeafL {V : VF C} {J : Fin 2 → Type} [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g))
    (g : Fin 2) (a a' : ZMod d) : MvPowerSeries (WV I) C →ₗ[C] MvPowerSeries (WV I) C where
  toFun := toLeaf G g a a'
  map_add' F F' := by
    ext μ
    rw [coeff_toLeaf, map_add (f := _), map_add (f := _), coeff_toLeaf, coeff_toLeaf]
    split_ifs <;> simp
  map_smul' r F := by
    ext μ
    rw [coeff_toLeaf, RingHom.id_apply, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, coeff_toLeaf]
    split_ifs <;> simp

theorem toLeaf_X_off {V : VF C} {J : Fin 2 → Type} [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g))
    (g : Fin 2) (a a' : ZMod d) (w : WV I) (hw : ¬ OnLeafV G g a a' w) :
    toLeaf G g a a' (MvPowerSeries.X w : MvPowerSeries (WV I) C) = 0 := by
  ext μ
  rw [coeff_toLeaf, MvPowerSeries.coeff_X, map_zero]
  split_ifs with h1 h2
  · exfalso
    apply hw
    apply h1
    rw [h2]
    simp
  · rfl
  · rfl

theorem dVar_hLf {κ : Type} [Fintype κ] {V : VF C} (X : RawChart C d I κ) (H : ∀ g, X.CartHyp V g)
    (g : Fin 2) (a a' : ZMod d) (w : WV I) (hw : X.OnLf g a a' w) :
    dVar w (X.hLf g a a') = toLeaf (fun g => RawChart.cart (H g)) g a a' (dVar w X.hRow) := by
  ext μ
  rw [coeff_toLeaf]
  have key : (∀ x ∈ (μ + Finsupp.single w 1).support, X.OnLf g a a' x) ↔ ∀ x ∈ μ.support, X.OnLf g a a' x := by
    constructor
    · intro h x hx
      apply h
      rw [Finsupp.mem_support_iff] at hx ⊢
      rw [Finsupp.add_apply]
      omega
    · intro h x hx
      by_cases hxw : x = w
      · exact hxw ▸ hw
      · apply h
        rw [Finsupp.mem_support_iff] at hx ⊢
        rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne hxw, add_zero] at hx
  show ((μ w + 1 : ℕ) : C) * (if ∀ x ∈ (μ + Finsupp.single w 1).support, X.OnLf g a a' x then
      MvPowerSeries.coeff (μ + Finsupp.single w 1) X.hRow else 0) =
    if ∀ x ∈ μ.support, X.OnLf g a a' x then ((μ w + 1 : ℕ) : C) * MvPowerSeries.coeff (μ + Finsupp.single w 1) X.hRow
      else 0
  by_cases hc : ∀ x ∈ μ.support, X.OnLf g a a' x
  · rw [if_pos (key.2 hc), if_pos hc]
  · rw [if_neg (fun h => hc (key.1 h)), if_neg hc, mul_zero]

end RowTiePCEq

open RowTiePCEq

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds PartialDerivEval RowTiePCEq ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

namespace RowTiePCEqSum

theorem subst_zero_const {σ τ : Type} [Finite σ] (f : MvPowerSeries σ C) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = 0 := by
  ext e
  rw [MvPowerSeries.coeff_subst MvPowerSeries.HasSubst.zero, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hn : n = 0
  · subst hn
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hn
    have hs' : n s ≠ 0 := by simpa using hs
    have : (n.prod fun s e => (0 : MvPowerSeries τ C) ^ e) = 0 :=
      Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.2 hs') (zero_pow hs')
    rw [this, map_zero, smul_zero]

theorem hasSubst_unit {τ : Type} {T : MvPowerSeries τ C} (hT : MvPowerSeries.constantCoeff T = 0) :
    MvPowerSeries.HasSubst (fun _ : Unit => T) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hT)

theorem subst_lin {σ τ : Type} {a : σ → MvPowerSeries τ C} (ha : MvPowerSeries.HasSubst a) {ι : Type}
    (s : Finset ι) (r : ι → C) (F : ι → MvPowerSeries σ C) :
    MvPowerSeries.subst a (∑ i ∈ s, r i • F i) = ∑ i ∈ s, r i • MvPowerSeries.subst a (F i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  first
  | exact map_smul _ _ _
  | exact AlgHom.map_smul_of_tower _ _ _

theorem coeff_subst_tyS {τ : Type} [Finite τ] {l : ℕ} (hl : 2 ≤ l) {T : MvPowerSeries τ C}
    (hT : MvPowerSeries.constantCoeff T = 0) (a : ℕ → C) (μ : τ →₀ ℕ) :
    MvPowerSeries.coeff μ (MvPowerSeries.subst (fun _ : Unit => T) (tyS l a)) =
      ∑ s ∈ Finset.range (μ.degree + 1), a s * MvPowerSeries.coeff μ (T ^ (l ^ s)) := by
  set N := μ.degree + 1 with hN
  set P : PowerSeries C := ∑ s ∈ Finset.range N, a s • PowerSeries.X ^ (l ^ s) with hP
  have hPc : ∀ m < l ^ N, PowerSeries.coeff m (tyS l a) = PowerSeries.coeff m P := by
    intro m hm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, map_sum]
    simp only [PowerSeries.coeff_smul, PowerSeries.coeff_X_pow]
    by_cases h : ∃ s', l ^ s' = m
    · obtain ⟨s', rfl⟩ := h
      rw [coeff_tyS_pow hl, Finset.sum_eq_single s']
      · simp
      · intro s _ hs
        rw [if_neg, smul_zero]
        intro h
        exact hs (Nat.pow_right_injective hl h).symm
      · intro h
        exfalso
        apply h
        rw [Finset.mem_range]
        exact (Nat.pow_lt_pow_iff_right (by omega)).1 hm
    · push Not at h
      rw [coeff_tyS_of_ne a m h]
      symm
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [if_neg (h s).symm, smul_zero]
  have hAg : Formalism.G.LogCR.Agree N (tyS l a : MvPowerSeries Unit C) (P : MvPowerSeries Unit C) := by
    intro e he
    have hes : e = Finsupp.single () (e ()) := Finsupp.unique_single e
    rw [hes] at he ⊢
    rw [Finsupp.degree_single] at he
    exact hPc _ (lt_of_lt_of_le he (Nat.lt_pow_self (by omega)).le)
  have h1 := Formalism.G.LogCR.Agree.subst (a := fun _ : Unit => T) (a' := fun _ : Unit => T) (fun _ => hT) (fun _ => hT) hAg
    (fun _ _ _ => rfl) μ (by omega)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, hP, ← MvPowerSeries.coe_substAlgHom (hasSubst_unit hT), map_sum, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, map_pow, MvPowerSeries.coe_substAlgHom]
  rw [show (PowerSeries.X : PowerSeries C) = (MvPowerSeries.X () : MvPowerSeries Unit C) from rfl,
    MvPowerSeries.subst_X (hasSubst_unit hT), MvPowerSeries.coeff_smul]

section Add

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

end Add

end RowTiePCEqSum


end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.FrobPowSmul
noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem frobPow_smul : ∀ (C : Type) [Field C] (V : VF C) (σ : Type) (f : MvPowerSeries σ C), IntS V f →
    ∀ μ : σ →₀ ℕ, V.MM (MvPowerSeries.coeff (V.l • μ) (f ^ V.l) - MvPowerSeries.coeff μ f ^ V.l) := by
  intro C _ V σ f hf μ
  have hl : 0 < V.l := V.l_prime.pos
  have h := PhPowP.frobPowMv f hf (V.l • μ)
  have hdiv : ∀ t, V.l ∣ (V.l • μ) t := fun t => by simp [Finsupp.smul_apply]
  have hdl : PhPowP.divL V.l (V.l • μ) = μ := by
    ext t
    rw [PhPowP.divL_apply, Finsupp.smul_apply, smul_eq_mul, Nat.mul_div_cancel_left _ hl]
  rw [if_pos hdiv, hdl] at h
  exact h

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.MmMulSeries
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace RootsP

variable {C : Type} [Field C] {V : VF C}

private lemma mm_zero_lemma : V.MM (0 : C) := by
  simp only [VF.MM, AddValuation.map_zero]
  first
    | exact WithTop.coe_lt_top 0
    | exact WithTop.zero_lt_top
    | simp

private lemma ge0_zero_lemma_2 : V.Ge 0 (0 : C) := by
  simp only [VF.Ge, AddValuation.map_zero]
  exact le_top

private lemma mm_add_lemma_3 {x y : C} (hx : V.MM x) (hy : V.MM y) : V.MM (x + y) := by
  simp only [VF.MM] at hx hy ⊢
  exact lt_of_lt_of_le (lt_min hx hy) (V.v.map_add x y)

private lemma ge0_add_lemma_4 {x y : C} (hx : V.Ge 0 x) (hy : V.Ge 0 y) : V.Ge 0 (x + y) := by
  simp only [VF.Ge] at hx hy ⊢
  exact le_trans (le_min hx hy) (V.v.map_add x y)

private lemma mm_mul_lemma_5 {x y : C} (hx : V.MM x) (hy : V.Ge 0 y) : V.MM (x * y) := by
  simp only [VF.MM, VF.Ge, AddValuation.map_mul] at hx hy ⊢
  have hy' : (0 : WithTop ℝ) ≤ V.v y := by simpa using hy
  exact lt_of_lt_of_le hx (le_add_of_nonneg_right hy')

private lemma ge0_mul_lemma_6 {x y : C} (hx : V.Ge 0 x) (hy : V.Ge 0 y) : V.Ge 0 (x * y) := by
  simp only [VF.Ge, AddValuation.map_mul] at hx hy ⊢
  have hx' : (0 : WithTop ℝ) ≤ V.v x := by simpa using hx
  have hy' : (0 : WithTop ℝ) ≤ V.v y := by simpa using hy
  have h := add_le_add hx' hy'
  simpa using h

private lemma ge0_one_lemma_7 : V.Ge 0 (1 : C) := by
  simp [VF.Ge]

private lemma ints_mul_lemma_8 {σ : Type} {F G : MvPowerSeries σ C} (hF : IntS V F) (hG : IntS V G) :
    IntS V (F * G) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  exact Finset.sum_induction _ (fun x => V.Ge 0 x) (fun a b ha hb => ge0_add_lemma_4 ha hb) ge0_zero_lemma_2
    (fun p _ => ge0_mul_lemma_6 (hF p.1) (hG p.2))

private lemma ints_one_lemma_9 {σ : Type} : IntS V (1 : MvPowerSeries σ C) := by
  intro μ
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact ge0_one_lemma_7
  · exact ge0_zero_lemma_2

private lemma ge_zero_of_mm {x : C} (h : V.MM x) : V.Ge 0 x := by
  simp only [VF.MM] at h
  simp only [VF.Ge]
  have h' := le_of_lt h
  simpa using h'

private lemma ge_zero_of_mm_sub_one {c : C} (h : V.MM (c - 1)) : V.Ge 0 c := by
  have h1 : c = (c - 1) + 1 := by ring
  rw [h1]
  exact ge0_add_lemma_4 (ge_zero_of_mm h) ge0_one_lemma_7

theorem mm_mul_series {σ : Type} {A B : MvPowerSeries σ C} (hA : ∀ μ, V.MM (MvPowerSeries.coeff μ A))
    (hB : ∀ μ, V.Ge 0 (MvPowerSeries.coeff μ B)) : ∀ μ, V.MM (MvPowerSeries.coeff μ (A * B)) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  exact Finset.sum_induction _ (fun x => V.MM x) (fun a b ha hb => mm_add_lemma_3 ha hb) mm_zero_lemma
    (fun p _ => mm_mul_lemma_5 (hA p.1) (hB p.2))

theorem root_one {ζ : C} (hζ : ζ ^ V.l = 1) : V.MM (ζ - 1) := by
  rcases V with ⟨v, l, hp, hv⟩
  change ζ ^ l = 1 at hζ
  change (0 : WithTop ℝ) < v (ζ - 1)
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by have := hp.pos; omega⟩
  by_contra hneg
  have hle : v (ζ - 1) ≤ 0 := not_lt.mp hneg
  have hne : v (ζ - 1) ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  have hr0 : r ≤ 0 := by
    rw [← hr] at hle
    exact_mod_cast hle
  have hnat : ∀ q : ℕ, (0 : WithTop ℝ) ≤ v (q : C) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      push_cast
      exact le_trans (le_min ih (by simp)) (v.map_add _ _)
  have hpow : ∀ m : ℕ, v ((ζ - 1) ^ m) = (((m : ℝ) * r : ℝ) : WithTop ℝ) := by
    intro m
    rw [AddValuation.map_pow, ← hr]
    first
      | rw [← WithTop.coe_nsmul, nsmul_eq_mul]
      | (norm_cast; simp [nsmul_eq_mul])
  have hbin : ∑ m ∈ Finset.range (l' + 1 + 1), (ζ - 1) ^ m * 1 ^ (l' + 1 - m) * ((l' + 1).choose m : C) = 1 := by
    rw [← add_pow, sub_add_cancel, hζ]
  rw [Finset.sum_range_succ, Finset.sum_range_succ'] at hbin
  simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one] at hbin
  have hx : (ζ - 1) ^ (l' + 1) = -∑ m ∈ Finset.range l', (ζ - 1) ^ (m + 1) * ((l' + 1).choose (m + 1) : C) := by
    linear_combination hbin
  have hterm : ∀ m ∈ Finset.range l', v ((ζ - 1) ^ (l' + 1)) <
      v ((ζ - 1) ^ (m + 1) * ((l' + 1).choose (m + 1) : C)) := by
    intro m hm
    rw [Finset.mem_range] at hm
    obtain ⟨q, hq⟩ := hp.dvd_choose_self (k := m + 1) (by omega) (by omega)
    rw [AddValuation.map_mul, hq, Nat.cast_mul, AddValuation.map_mul, hv, hpow, hpow]
    have hq0 := hnat q
    have hm' : (m : ℝ) ≤ l' := by exact_mod_cast hm.le
    have hreal : ((l' + 1 : ℕ) : ℝ) * r < ((m + 1 : ℕ) : ℝ) * r + 1 := by
      push_cast
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hm') hr0]
    have hA : ((((l' + 1 : ℕ) : ℝ) * r : ℝ) : WithTop ℝ) < ((((m + 1 : ℕ) : ℝ) * r + 1 : ℝ) : WithTop ℝ) :=
      WithTop.coe_lt_coe.mpr hreal
    have hB : ((((m + 1 : ℕ) : ℝ) * r + 1 : ℝ) : WithTop ℝ) ≤
        ((((m + 1 : ℕ) : ℝ) * r : ℝ) : WithTop ℝ) + (1 + v (q : C)) := by
      rw [WithTop.coe_add, WithTop.coe_one]
      exact add_le_add le_rfl (le_add_of_nonneg_right hq0)
    exact lt_of_lt_of_le hA hB
  have hsum : v ((ζ - 1) ^ (l' + 1)) <
      v (∑ m ∈ Finset.range l', (ζ - 1) ^ (m + 1) * ((l' + 1).choose (m + 1) : C)) := by
    refine Finset.sum_induction _ (fun y => v ((ζ - 1) ^ (l' + 1)) < v y) ?_ ?_ hterm
    · intro a b ha hb
      exact lt_of_lt_of_le (lt_min ha hb) (v.map_add a b)
    · rw [AddValuation.map_zero, hpow]
      exact WithTop.coe_lt_top _
  have hx' : v ((ζ - 1) ^ (l' + 1)) =
      v (∑ m ∈ Finset.range l', (ζ - 1) ^ (m + 1) * ((l' + 1).choose (m + 1) : C)) := by
    rw [hx, AddValuation.map_neg]
  rw [← hx'] at hsum
  exact lt_irrefl _ hsum

end RootsP

theorem rootsProd : ∀ (C : Type) [Field C] (V : VF C) (ζ : C), ζ ^ V.l = 1 → ∀ (j : Fin 2)
    (f : MvPowerSeries (Fin 2) C), IntS V f → ∀ μ, V.MM (MvPowerSeries.coeff μ
      (∏ k ∈ Finset.range V.l, MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f - f ^ V.l)) := by
  intro C _ V ζ hζ j f hf
  have hc : ∀ (k : ℕ) (μ : Fin 2 →₀ ℕ), (μ.prod fun s m => (if s = j then ζ ^ k else 1) ^ m) ^ V.l = 1 := by
    intro k μ
    have hk : (ζ ^ k) ^ V.l = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    unfold Finsupp.prod
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro s _
    rw [← pow_mul, mul_comm, pow_mul]
    split_ifs
    · rw [hk, one_pow]
    · simp
  have hcoef : ∀ (k : ℕ) (μ : Fin 2 →₀ ℕ),
      MvPowerSeries.coeff μ (MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f) =
        (μ.prod fun s m => (if s = j then ζ ^ k else 1) ^ m) * MvPowerSeries.coeff μ f := by
    intro k μ
    first
      | exact MvPowerSeries.coeff_rescale _ _ _
      | rw [MvPowerSeries.coeff_rescale]
      | simp [MvPowerSeries.coeff_rescale]
  have hE : ∀ (k : ℕ) (μ : Fin 2 →₀ ℕ), V.MM (MvPowerSeries.coeff μ
      (MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f - f)) := by
    intro k μ
    rw [map_sub, hcoef, ← sub_one_mul]
    exact RootsP.mm_mul_lemma_5 (RootsP.root_one (hc k μ)) (hf μ)
  have hG : ∀ k : ℕ, IntS V (MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f) := by
    intro k μ
    rw [hcoef]
    exact RootsP.ge0_mul_lemma_6 (RootsP.ge_zero_of_mm_sub_one (RootsP.root_one (hc k μ))) (hf μ)
  have hpow : ∀ n : ℕ, IntS V (f ^ n) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero]
      exact RootsP.ints_one_lemma_9
    | succ n ih =>
      rw [pow_succ]
      exact RootsP.ints_mul_lemma_8 ih hf
  have key : ∀ n : ℕ, ∀ μ, V.MM (MvPowerSeries.coeff μ
      (∏ k ∈ Finset.range n, MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f - f ^ n)) := by
    intro n
    induction n with
    | zero =>
      intro μ
      simp only [Finset.range_zero, Finset.prod_empty, pow_zero, sub_self, map_zero]
      exact RootsP.mm_zero_lemma
    | succ n ih =>
      intro μ
      have hid : ∏ k ∈ Finset.range (n + 1), MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f -
          f ^ (n + 1) =
          (∏ k ∈ Finset.range n, MvPowerSeries.rescale (fun i => if i = j then ζ ^ k else 1) f - f ^ n) *
              MvPowerSeries.rescale (fun i => if i = j then ζ ^ n else 1) f +
            f ^ n * (MvPowerSeries.rescale (fun i => if i = j then ζ ^ n else 1) f - f) := by
        rw [Finset.prod_range_succ, pow_succ]
        ring
      rw [hid, map_add (f := _)]
      refine RootsP.mm_add_lemma_3 (RootsP.mm_mul_series ih (hG n) μ) ?_
      rw [mul_comm]
      exact RootsP.mm_mul_series (hE n) (hpow n) μ
  exact key V.l

end Formalism.L2.FormalSeriesBounds
end
end
