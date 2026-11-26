module

public import Formalism.SharpRestriction.GrowthBounds.SelectionLemmas

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsCg
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VS

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {σ τ : Type} [Finite σ]

def UImg (V : VF C) (A : σ → MvPowerSeries τ C) (Φ : MvPowerSeries τ C) : Prop :=
  ∃ U : MvPowerSeries σ C, IsIU V U ∧ MvPowerSeries.subst A U = Φ

def GImg (V : VF C) (A : σ → MvPowerSeries τ C) (a : Fin dd → MvPowerSeries τ C) : Prop :=
  ∃ P : Fin dd → MvPowerSeries σ C, VP.GoodPt V P ∧ ∀ i, MvPowerSeries.subst A (P i) = a i

def Cg (V : VF C) (A : σ → MvPowerSeries τ C) (f g : MvPowerSeries τ C) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ MvPowerSeries.constantCoeff g = 0 ∧ UImg V A (mvExp (f - g))

variable {A : σ → MvPowerSeries τ C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0)

include hA

theorem UImg.one : UImg V A 1 := ⟨1, IsIU.one, VP.subst_one hA⟩

theorem UImg.mul {Φ Ψ : MvPowerSeries τ C} (h : UImg V A Φ) (h' : UImg V A Ψ) : UImg V A (Φ * Ψ) := by
  obtain ⟨U, hU, rfl⟩ := h
  obtain ⟨U', hU', rfl⟩ := h'
  exact ⟨U * U', hU.mul hU', VP.subst_mul hA _ _⟩

theorem UImg.pow {Φ : MvPowerSeries τ C} (h : UImg V A Φ) (k : ℕ) : UImg V A (Φ ^ k) := by
  obtain ⟨U, hU, rfl⟩ := h
  exact ⟨U ^ k, ⟨hU.1.pow k, by rw [map_pow, V.v.map_pow, hU.2, smul_zero]⟩, VP.subst_pow' hA _ _⟩

theorem UImg.exp_neg {f : MvPowerSeries τ C} (hf : MvPowerSeries.constantCoeff f = 0) (h : UImg V A (mvExp f)) :
    UImg V A (mvExp (-f)) := by
  obtain ⟨U, hU, e⟩ := h
  obtain ⟨U', hU'i, hUU⟩ := VP.intInv hU.1 hU.2
  have hU'0 : V.v (MvPowerSeries.constantCoeff U') = 0 := by
    have h1 := congrArg (fun x => V.v (MvPowerSeries.constantCoeff x)) hUU
    simp only [map_mul, map_one, V.v.map_mul, V.v.map_one, hU.2, add_zero] at h1
    exact h1
  refine ⟨U', ⟨hU'i, hU'0⟩, ?_⟩
  have h2 : MvPowerSeries.subst A U' * mvExp f = 1 := by
    rw [← e, ← VP.subst_mul hA, hUU, VP.subst_one hA]
  have h3 : mvExp (-f) * mvExp f = 1 := by
    rw [← VP.exp_add (by rw [map_neg, hf, neg_zero]) hf, neg_add_cancel, rtj_mvExp_zero]
  calc MvPowerSeries.subst A U' = MvPowerSeries.subst A U' * (mvExp (-f) * mvExp f) := by rw [h3, mul_one]
    _ = (MvPowerSeries.subst A U' * mvExp f) * mvExp (-f) := by ring
    _ = mvExp (-f) := by rw [h2, one_mul]

theorem Cg.refl {f : MvPowerSeries τ C} (hf : MvPowerSeries.constantCoeff f = 0) : Cg V A f f :=
  ⟨hf, hf, by rw [sub_self, rtj_mvExp_zero]; exact UImg.one hA⟩

theorem Cg.symm {f g : MvPowerSeries τ C} (h : Cg V A f g) : Cg V A g f :=
  ⟨h.2.1, h.1, by
    have := UImg.exp_neg hA (by rw [map_sub, h.1, h.2.1, sub_zero]) h.2.2
    rwa [neg_sub] at this⟩

theorem Cg.trans {f g k : MvPowerSeries τ C} (h : Cg V A f g) (h' : Cg V A g k) : Cg V A f k :=
  ⟨h.1, h'.2.1, by
    have := UImg.mul hA h.2.2 h'.2.2
    rw [← VP.exp_add (by rw [map_sub, h.1, h.2.1, sub_zero]) (by rw [map_sub, h'.1, h'.2.1, sub_zero])] at this
    rwa [sub_add_sub_cancel] at this⟩

theorem Cg.add {f g f' g' : MvPowerSeries τ C} (h : Cg V A f g) (h' : Cg V A f' g') : Cg V A (f + f') (g + g') :=
  ⟨by rw [map_add (f := _), h.1, h'.1, add_zero], by rw [map_add (f := _), h.2.1, h'.2.1, add_zero], by
    have := UImg.mul hA h.2.2 h'.2.2
    rw [← VP.exp_add (by rw [map_sub, h.1, h.2.1, sub_zero]) (by rw [map_sub, h'.1, h'.2.1, sub_zero])] at this
    rwa [show f - g + (f' - g') = f + f' - (g + g') by ring] at this⟩

theorem Cg.sum {ι : Type} (s : Finset ι) {f g : ι → MvPowerSeries τ C} (h : ∀ i ∈ s, Cg V A (f i) (g i)) :
    Cg V A (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (Cg.refl hA (map_zero _) : Cg V A (0 : MvPowerSeries τ C) 0)
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Cg.add hA (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Cg.nsmul {f g : MvPowerSeries τ C} (h : Cg V A f g) (k : ℕ) : Cg V A ((k : C) • f) ((k : C) • g) :=
  ⟨VP.cc_smul _ h.1, VP.cc_smul _ h.2.1, by
    rw [← smul_sub, VP.exp_nsmul (by rw [map_sub, h.1, h.2.1, sub_zero])]
    exact UImg.pow hA h.2.2 k⟩

theorem Cg.unit {f g : MvPowerSeries τ C} (h : Cg V A f g) :
    ∃ U : MvPowerSeries σ C, IsIU V U ∧ mvExp f = MvPowerSeries.subst A U * mvExp g := by
  obtain ⟨U, hU, e⟩ := h.2.2
  refine ⟨U, hU, ?_⟩
  rw [e, ← VP.exp_add (by rw [map_sub, h.1, h.2.1, sub_zero]) h.2.1, sub_add_cancel]

theorem cg_of {F G : MvPowerSeries σ C} (hF : MvPowerSeries.constantCoeff F = 0)
    (hG : MvPowerSeries.constantCoeff G = 0) (hi : IntS V (mvExp (F - G))) :
    Cg V A (MvPowerSeries.subst A F) (MvPowerSeries.subst A G) :=
  ⟨VP.cc_subst hA hF, VP.cc_subst hA hG, mvExp (F - G), VP.isIU_of_exp hi rfl, by
    rw [VP.subst_exp hA (by rw [map_sub, hF, hG, sub_zero]), VP.subst_sub' hA]⟩

theorem GImg.zero : GImg V A (fun _ : Fin dd => (0 : MvPowerSeries τ C)) :=
  ⟨fun _ => 0, VP.GoodPt.zero, fun _ => VP.subst_zero' hA⟩

variable (Y : FBChart C V O dd)

theorem GImg.add {a b : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) :
    GImg V A (VP.addAt Y a b) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  exact ⟨VP.addAt Y P Q, hP.add Y hQ, fun i => VP.addAt_subst Y hA hP.1 hQ.1 i⟩

theorem GImg.act (x : O) {a : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) : GImg V A (VP.actAt Y x a) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  exact ⟨VP.actAt Y x P, hP.act Y x, fun i => VP.actAt_subst Y hA hP.1 x i⟩

omit Y in
theorem GImg.map {Y : FBChart C V O dd} {φ : Pt C 1 dd} (hφ : IsEndo Y φ) {a : Fin dd → MvPowerSeries τ C}
    (ha : GImg V A a) : GImg V A (VP.mapAt φ a) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  exact ⟨VP.mapAt φ P, ⟨VP.cc_mapAt hφ.cc hP.1, fun i =>
    IntS.subst (a := fun q : Fin 1 × Fin dd => P q.2) (fun q => hP.1 q.2) (fun q => hP.2 q.2) (hφ.int i)⟩,
    fun i => VP.mapAt_subst hA φ hP.1 i⟩

theorem gauge_congr_additive_left {a b c : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) (hc : GImg V A c) :
    Cg V A (VP.hAt Y (VP.addAt Y a b) c) (VP.hAt Y a c + VP.hAt Y b c) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain ⟨R, hR, e''⟩ := hc
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  obtain rfl : (fun i => MvPowerSeries.subst A (R i)) = c := funext e''
  have c1 := VP.cc_hAt Y hP.1 hR.1
  have c2 := VP.cc_hAt Y hQ.1 hR.1
  have c3 := VP.cc_hAt Y (VP.cc_addAt Y hP.1 hQ.1) hR.1
  have h := cg_of (V := V) hA (F := VP.hAt Y P R + VP.hAt Y Q R) (G := VP.hAt Y (VP.addAt Y P Q) R)
    (by rw [map_add (f := _), c1, c2, add_zero]) c3 (by
      rw [← VP.first_partial_law_at_points Y hP.1 hQ.1 hR.1]
      exact IntS.subst (VP.constantCoeff_triple_substitution hP.1 hQ.1 hR.1) (VP.integral_triple_substitution hP.2 hQ.2 hR.2) Y.intPh1)
  rw [VP.subst_add' hA, VP.hAt_subst Y hA hP.1 hR.1, VP.hAt_subst Y hA hQ.1 hR.1,
    VP.hAt_subst Y hA (VP.cc_addAt Y hP.1 hQ.1) hR.1, funext (VP.addAt_subst Y hA hP.1 hQ.1)] at h
  exact Cg.symm hA h

theorem gauge_congr_additive_right {a b c : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) (hc : GImg V A c) :
    Cg V A (VP.hAt Y a (VP.addAt Y b c)) (VP.hAt Y a b + VP.hAt Y a c) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain ⟨R, hR, e''⟩ := hc
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  obtain rfl : (fun i => MvPowerSeries.subst A (R i)) = c := funext e''
  have c1 := VP.cc_hAt Y hP.1 hQ.1
  have c2 := VP.cc_hAt Y hP.1 hR.1
  have c3 := VP.cc_hAt Y hP.1 (VP.cc_addAt Y hQ.1 hR.1)
  have h := cg_of (V := V) hA (F := VP.hAt Y P Q + VP.hAt Y P R) (G := VP.hAt Y P (VP.addAt Y Q R))
    (by rw [map_add (f := _), c1, c2, add_zero]) c3 (by
      rw [← VP.second_partial_law_at_points Y hP.1 hQ.1 hR.1]
      exact IntS.subst (VP.constantCoeff_triple_substitution hP.1 hQ.1 hR.1) (VP.integral_triple_substitution hP.2 hQ.2 hR.2) Y.intPh2)
  rw [VP.subst_add' hA, VP.hAt_subst Y hA hP.1 hQ.1, VP.hAt_subst Y hA hP.1 hR.1,
    VP.hAt_subst Y hA hP.1 (VP.cc_addAt Y hQ.1 hR.1), funext (VP.addAt_subst Y hA hQ.1 hR.1)] at h
  exact Cg.symm hA h

theorem cg_sy {a b : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) :
    Cg V A (VP.hAt Y b a) (VP.hAt Y a b) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  have h := cg_of (V := V) hA (F := VP.hAt Y Q P) (G := VP.hAt Y P Q) (VP.cc_hAt Y hQ.1 hP.1) (VP.cc_hAt Y hP.1 hQ.1) (by
      rw [← VP.sy_at Y hP.1 hQ.1]
      exact IntS.subst (VP.constantCoeff_pair_substitution hP.1 hQ.1) (VP.integral_pair_substitution hP.2 hQ.2) Y.intSy)
  rwa [VP.hAt_subst Y hA hQ.1 hP.1, VP.hAt_subst Y hA hP.1 hQ.1] at h

theorem cg_ad (x : O) {a b : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) :
    Cg V A (VP.hAt Y (VP.actAt Y x a) b) (VP.hAt Y a (VP.actAt Y (star x) b)) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  have h := cg_of (V := V) hA (F := VP.hAt Y (VP.actAt Y x P) Q) (G := VP.hAt Y P (VP.actAt Y (star x) Q))
    (VP.cc_hAt Y (VP.cc_actAt Y x hP.1) hQ.1) (VP.cc_hAt Y hP.1 (VP.cc_actAt Y _ hQ.1)) (by
      rw [← VP.ad_at Y hP.1 hQ.1]
      exact IntS.subst (VP.constantCoeff_pair_substitution hP.1 hQ.1) (VP.integral_pair_substitution hP.2 hQ.2) (Y.intAd x))
  rwa [VP.hAt_subst Y hA (VP.cc_actAt Y x hP.1) hQ.1, VP.hAt_subst Y hA hP.1 (VP.cc_actAt Y _ hQ.1),
    funext (VP.actAt_subst Y hA hP.1 x), funext (VP.actAt_subst Y hA hQ.1 (star x))] at h

theorem cg_adj {φ φ' : Pt C 1 dd} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ' : ∀ i, MvPowerSeries.constantCoeff (φ' i) = 0)
    (hadj : IntS V (FB.expS C (ev (n := 2) ![comp1 φ (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 φ' (pt C dd 1)] Y.h)))
    {a b : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) :
    Cg V A (VP.hAt Y (VP.mapAt φ a) b) (VP.hAt Y a (VP.mapAt φ' b)) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  have h := cg_of (V := V) hA (F := VP.hAt Y (VP.mapAt φ P) Q) (G := VP.hAt Y P (VP.mapAt φ' Q))
    (VP.cc_hAt Y (VP.cc_mapAt hφ hP.1) hQ.1) (VP.cc_hAt Y hP.1 (VP.cc_mapAt hφ' hQ.1)) (by
      rw [← VP.cmp_at Y hφ hφ' hP.1 hQ.1]
      exact IntS.subst (VP.constantCoeff_pair_substitution hP.1 hQ.1) (VP.integral_pair_substitution hP.2 hQ.2) hadj)
  rwa [VP.hAt_subst Y hA (VP.cc_mapAt hφ hP.1) hQ.1, VP.hAt_subst Y hA hP.1 (VP.cc_mapAt hφ' hQ.1),
    funext (VP.mapAt_subst hA φ hP.1), funext (VP.mapAt_subst hA φ' hQ.1)] at h

end VS

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VS

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

section Defs

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))

def eW (w : WVO (IS I0)) : Fin dd → C := (p w.1).e w.2.2

def tyW (w : WVO (IS I0)) : ZMod d := (p w.1).ty0 w.2.2

def zeK (κ : WVO (IS I0) → C) (m : Fin dd) : MvPowerSeries (WVO (IS I0)) C :=
  ∑ w, (κ w * eW Y p w m) • (MvPowerSeries.X w : MvPowerSeries (WVO (IS I0)) C)

def EK (κ : WVO (IS I0) → C) : Fin dd → MvPowerSeries (WVO (IS I0)) C := VP.exAt Y (zeK Y p κ)

def AA : Fin 2 × Fin dd → MvPowerSeries (WVO (IS I0)) C := VP.linPt Y (uS Y p)

def GK (κ : WVO (IS I0) → C) : Prop := GImg V (AA Y p) (EK Y p κ)

def HK (κ κ' : WVO (IS I0) → C) : MvPowerSeries (WVO (IS I0)) C := VP.hAt Y (EK Y p κ) (EK Y p κ')

def kCol (col : Fin 2) (w : WVO (IS I0)) : C := (p w.1).gm (tyW Y p w) col w.2.1

def lamAct (x : O) (w : WVO (IS I0)) : C := (p w.1).em (tyW Y p w) x

def lamG (o : Orb) (r s : Fin 2) (w : WVO (IS I0)) : C := if w.1 = o then (p w.1).gm (tyW Y p w) r s else 0

def lamG' (o : Orb) (r s : Fin 2) (w : WVO (IS I0)) : C :=
  if w.1 = o then (p w.1).gm (tyW Y p w + (p w.1).hd) r s else 0

end Defs

def ind (s : Orb × Fin 2) (w : WVO (IS I0)) : C := if (w.1, w.2.1) = s then 1 else 0

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))

theorem cc_zeK (κ : WVO (IS I0) → C) (m : Fin dd) : MvPowerSeries.constantCoeff (zeK Y p κ m) = 0 := by
  simp [zeK]

theorem cc_EK (κ : WVO (IS I0) → C) (i : Fin dd) : MvPowerSeries.constantCoeff (EK Y p κ i) = 0 := by
  apply VP.cc_exAt
  intro m
  exact cc_zeK Y p κ m

theorem cc_AA (s : Fin 2 × Fin dd) : MvPowerSeries.constantCoeff (AA Y p s) = 0 := by
  obtain ⟨col, i⟩ := s
  exact cc_EK Y p (kCol Y p col) i

theorem cc_HK (κ κ' : WVO (IS I0) → C) : MvPowerSeries.constantCoeff (HK Y p κ κ') = 0 := by
  apply VP.cc_hAt <;> intro i <;> exact cc_EK Y p _ i

theorem AA_eq (col : Fin 2) (i : Fin dd) : AA Y p (col, i) = EK Y p (kCol Y p col) i := rfl

theorem GK_col (col : Fin 2) : GK Y p (kCol Y p col) :=
  ⟨fun i => MvPowerSeries.X (col, i), ⟨fun _ => VP.cc_X _, fun _ => VP.IntS_X _⟩, fun i => by
    rw [VP.subst_X (cc_AA Y p)]; rfl⟩

theorem zeK_add (κ κ' : WVO (IS I0) → C) (m : Fin dd) : zeK Y p (κ + κ') m = zeK Y p κ m + zeK Y p κ' m := by
  simp only [zeK, Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib]

theorem EK_add (κ κ' : WVO (IS I0) → C) : VP.addAt Y (EK Y p κ) (EK Y p κ') = EK Y p (κ + κ') := by
  unfold EK
  rw [← VP.ex_add Y (cc_zeK Y p κ) (cc_zeK Y p κ')]
  congr 1
  funext m
  exact (zeK_add Y p κ κ' m).symm

theorem EK_zero : EK Y p 0 = fun _ => 0 := by
  have hz : zeK Y p 0 = fun _ => 0 := by
    funext m
    simp [zeK]
  unfold EK
  rw [hz, VP.exAt_zero]

theorem EK_map {φ : Pt C 1 dd} (hφ : IsEndo Y φ) {lam : WVO (IS I0) → C}
    (hl : ∀ w, linAct φ (eW Y p w) = lam w • eW Y p w) (κ : WVO (IS I0) → C) :
    VP.mapAt φ (EK Y p κ) = EK Y p (lam * κ) := by
  funext i
  rw [show VP.mapAt φ (EK Y p κ) i = _ from
    endoLog_holds Y φ hφ.cc hφ.add (WVO (IS I0)) (zeK Y p κ) (cc_zeK Y p κ) i]
  show VP.exAt Y _ i = VP.exAt Y _ i
  congr 1
  funext m
  unfold zeK
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have h := congrFun (hl w) m
  unfold linAct at h
  rw [Pi.smul_apply, smul_eq_mul] at h
  rw [Pi.mul_apply, mul_right_comm, ← h, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem isEndo_act (x : O) : IsEndo Y (Y.B.A.act x) :=
  ⟨Y.intAct x, Y.B.A.const x, Y.B.A.hom x⟩

theorem EK_act (x : O) (κ : WVO (IS I0) → C) : VP.actAt Y x (EK Y p κ) = EK Y p (lamAct Y p x * κ) :=
  EK_map Y p (isEndo_act Y x) (fun w => (p w.1).e_eig w.2.2 x) κ

theorem GK.add {κ κ' : WVO (IS I0) → C} (h : GK Y p κ) (h' : GK Y p κ') : GK Y p (κ + κ') := by
  have h2 : GImg V (AA Y p) (VP.addAt Y (EK Y p κ) (EK Y p κ')) := by
    first
      | exact GImg.add (Y := Y) (cc_AA Y p) h h'
      | exact GImg.add (Y := Y) h h'
      | exact GImg.add (cc_AA Y p) h h'
  rw [EK_add] at h2
  exact h2

theorem GK.zero : GK Y p 0 := by
  unfold GK
  rw [EK_zero]
  first
    | exact GImg.zero (V := V) (A := AA Y p)
    | exact GImg.zero (V := V) (A := AA Y p) (cc_AA Y p)
    | exact GImg.zero (V := V) (A := AA Y p) (Y := Y)
    | exact GImg.zero (V := V) (A := AA Y p) (Y := Y) (cc_AA Y p)

theorem GK.sum {ι : Type} (s : Finset ι) {κ : ι → WVO (IS I0) → C} (h : ∀ i ∈ s, GK Y p (κ i)) :
    GK Y p (∑ i ∈ s, κ i) := by
  exact Finset.sum_induction κ (GK Y p) (fun a b ha hb => GK.add Y p ha hb) (GK.zero Y p) h

theorem GK.map {φ : Pt C 1 dd} (hφ : IsEndo Y φ) {lam : WVO (IS I0) → C}
    (hl : ∀ w, linAct φ (eW Y p w) = lam w • eW Y p w) {κ : WVO (IS I0) → C} (h : GK Y p κ) :
    GK Y p (lam * κ) := by
  have h2 : GImg V (AA Y p) (VP.mapAt φ (EK Y p κ)) := by
    first
      | exact GImg.map (cc_AA Y p) hφ h
      | exact GImg.map hφ (cc_AA Y p) h
      | exact GImg.map hφ h
  rw [EK_map Y p hφ hl] at h2
  exact h2

theorem GK.act (x : O) {κ : WVO (IS I0) → C} (h : GK Y p κ) : GK Y p (lamAct Y p x * κ) := by
  have h2 : GImg V (AA Y p) (VP.actAt Y x (EK Y p κ)) := by
    first
      | exact GImg.act (Y := Y) (cc_AA Y p) x h
      | exact GImg.act (Y := Y) x (cc_AA Y p) h
      | exact GImg.act (Y := Y) x h
  rw [EK_act] at h2
  exact h2

theorem kill_self (hs : SelfSep Y p) (o : Orb) (φ : Pt C 1 dd) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hcomm : ∀ a, comp1 φ (Y.B.A.act a) = comp1 (Y.B.A.act a) φ)
    (himg : ∀ v : Fin dd → C, ∃ b : I0 o → C, linAct φ v = ∑ c, b c • (p o).e c)
    (o' : Orb) (c' : I0 o') (ho : o' ≠ o) : linAct φ ((p o').e c') = 0 := by
  obtain ⟨b, hb⟩ := himg ((p o').e c')
  have h1 : ∀ a, linAct (Y.B.A.act a) (linAct φ ((p o').e c')) =
      (p o').em ((p o').ty0 c') a • linAct φ ((p o').e c') := by
    intro a
    rw [← VP.linAct_comp1 _ _ hφ, ← hcomm a, VP.linAct_comp1 _ _ (Y.B.A.const a), (p o').e_eig, VP.linAct_smul]
  have h2 : ∀ a, ∑ c, (b c * ((p o).em ((p o).ty0 c) a - (p o').em ((p o').ty0 c') a)) • (p o).e c = 0 := by
    intro a
    have h3 := h1 a
    rw [hb, VP.linAct_sum, Finset.smul_sum] at h3
    have h4 : ∀ c, linAct (Y.B.A.act a) (b c • (p o).e c) = (b c * (p o).em ((p o).ty0 c) a) • (p o).e c := by
      intro c
      rw [VP.linAct_smul, (p o).e_eig, smul_smul]
    rw [Finset.sum_congr rfl fun c _ => h4 c] at h3
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [smul_smul, ← sub_smul]
    congr 1
    ring
  obtain ⟨W, -, hW⟩ := (p o).e_sat
  have hb0 : ∀ c, b c = 0 := by
    intro c
    obtain ⟨a, ha⟩ := hs (o, (p o).ty0 c) (o', (p o').ty0 c') (fun h => ho (Prod.mk.inj h).1.symm)
    have hne : (p o).em ((p o).ty0 c) a - (p o').em ((p o').ty0 c') a ≠ 0 := by
      intro h
      have h6 : V.v ((p o).em ((p o).ty0 c) a - (p o').em ((p o').ty0 c') a) = 0 := ha
      rw [h, V.v.map_zero] at h6
      exact WithTop.top_ne_zero h6
    have h7 : ∑ x, (∑ c'', (b c'' * ((p o).em ((p o).ty0 c'') a - (p o').em ((p o').ty0 c') a)) • (p o).e c'') x *
        W x c = 0 := by
      rw [h2 a]
      simp
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul] at h7
    rw [Finset.sum_comm] at h7
    have h8 : ∀ c'', ∑ x, b c'' * ((p o).em ((p o).ty0 c'') a - (p o').em ((p o').ty0 c') a) * (p o).e c'' x * W x c =
        if c'' = c then b c'' * ((p o).em ((p o).ty0 c'') a - (p o').em ((p o').ty0 c') a) else 0 := by
      intro c''
      have := hW c'' c
      simp only [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum, this]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun c'' _ => h8 c'', Finset.sum_ite_eq'] at h7
    simp only [Finset.mem_univ, if_true] at h7
    exact (mul_eq_zero.1 h7).resolve_right hne
  rw [hb]
  exact Finset.sum_eq_zero fun c _ => by rw [hb0 c, zero_smul]

section Pack

variable {Y p} {γ γ' : Orb → Fin 2 → Fin 2 → Pt C 1 dd} (hs : SelfSep Y p) (hG : ∀ o, GmPack Y (p o) (γ o) (γ' o))

include hs hG

theorem diagG (o : Orb) (r s : Fin 2) (w : WVO (IS I0)) :
    linAct (γ o r s) (eW Y p w) = lamG Y p o r s w • eW Y p w := by
  obtain ⟨o', g, c⟩ := w
  by_cases h : o' = o
  · subst h
    show _ = (if o' = o' then _ else _) • _
    rw [if_pos rfl]
    exact (hG o').lin r s c
  · show _ = (if o' = o then _ else _) • _
    rw [if_neg h, zero_smul]
    exact kill_self Y p hs o (γ o r s) ((hG o).endo r s).cc ((hG o).comm r s) ((hG o).img r s) o' c h

theorem diagG' (o : Orb) (r s : Fin 2) (w : WVO (IS I0)) :
    linAct (γ' o r s) (eW Y p w) = lamG' Y p o r s w • eW Y p w := by
  obtain ⟨o', g, c⟩ := w
  by_cases h : o' = o
  · subst h
    show _ = (if o' = o' then _ else _) • _
    rw [if_pos rfl]
    exact (hG o').lin' r s c
  · show _ = (if o' = o then _ else _) • _
    rw [if_neg h, zero_smul]
    exact kill_self Y p hs o (γ' o r s) ((hG o).endo' r s).cc ((hG o).comm' r s) ((hG o).img' r s) o' c h

theorem GK.mulG (o : Orb) (r s : Fin 2) {κ : WVO (IS I0) → C} (h : GK Y p κ) : GK Y p (lamG Y p o r s * κ) :=
  GK.map Y p ((hG o).endo r s) (diagG hs hG o r s) h

theorem GK.mulG' (o : Orb) (r s : Fin 2) {κ : WVO (IS I0) → C} (h : GK Y p κ) : GK Y p (lamG' Y p o r s * κ) :=
  GK.map Y p ((hG o).endo' r s) (diagG' hs hG o r s) h

end Pack

theorem fin_two_ne_one_sub : ∀ g g' : Fin 2, g' = g ↔ ¬ (1 - g = g') := by
  decide

theorem kCol_eq (col : Fin 2) : kCol Y p col = ∑ s : Orb × Fin 2, lamG Y p s.1 col s.2 * ind s := by
  funext w
  simp only [Finset.sum_apply, Pi.mul_apply, lamG, ind, kCol]
  rw [Finset.sum_eq_single (w.1, w.2.1)]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ind_eq (s : Orb × Fin 2) : (ind s : WVO (IS I0) → C) = ∑ r, lamG' Y p s.1 r (1 - s.2) * kCol Y p r := by
  obtain ⟨o, g⟩ := s
  funext w
  rw [Finset.sum_apply]
  show (if (w.1, w.2.1) = (o, g) then (1 : C) else 0) =
    ∑ r, (if w.1 = o then (p w.1).gm (tyW Y p w + (p w.1).hd) r (1 - g) else 0) * (p w.1).gm (tyW Y p w) r w.2.1
  by_cases h : w.1 = o
  · simp only [if_pos h]
    rw [(p w.1).gm_hyp]
    by_cases hg : w.2.1 = g
    · rw [if_pos (Prod.ext h hg), if_neg ((fin_two_ne_one_sub g w.2.1).1 hg)]
    · rw [if_neg fun e => hg (Prod.mk.inj e).2, if_pos (not_not.1 fun e => hg ((fin_two_ne_one_sub g w.2.1).2 e))]
  · simp only [if_neg h, zero_mul, Finset.sum_const_zero]
    rw [if_neg fun e => h (Prod.mk.inj e).1]

theorem gram_eq (o o' : Orb) (g g' : Fin 2) (μ : WVO (IS I0) → C) :
    ∑ col, lamG' Y p o col g * (lamG Y p o' col g' * (μ * ind (o', g'))) =
      if (o', g') = (o, 1 - g) then μ * ind (o', g') else 0 := by
  funext w
  rw [Finset.sum_apply]
  simp only [Pi.mul_apply]
  by_cases hw : (w.1, w.2.1) = (o', g')
  · have h1 : w.1 = o' := (Prod.mk.inj hw).1
    by_cases ho : o' = o
    · have h2 : w.1 = o := h1.trans ho
      have e : ∀ col, lamG' Y p o col g w * (lamG Y p o' col g' w * (μ w * ind (o', g') w)) =
          ((p w.1).gm (tyW Y p w + (p w.1).hd) col g * (p w.1).gm (tyW Y p w) col g') * (μ w * ind (o', g') w) := by
        intro col
        unfold lamG' lamG
        rw [if_pos h2, if_pos h1]
        ring
      rw [Finset.sum_congr rfl fun col _ => e col, ← Finset.sum_mul, (p w.1).gm_hyp]
      by_cases hg : g = g'
      · rw [if_pos hg, zero_mul, if_neg fun h => (fin_two_ne_one_sub g g').1 hg.symm (Prod.mk.inj h).2.symm]
        rfl
      · rw [if_neg hg, one_mul, if_pos (Prod.ext ho (not_not.1 fun e => hg ((fin_two_ne_one_sub g g').2 fun e' => e e'.symm).symm))]
        rfl
    · have e : ∀ col, lamG' Y p o col g w * (lamG Y p o' col g' w * (μ w * ind (o', g') w)) = 0 := by
        intro col
        unfold lamG'
        rw [if_neg fun h => ho (h1.symm.trans h), zero_mul]
      rw [Finset.sum_eq_zero fun col _ => e col, if_neg fun h => ho (Prod.mk.inj h).1]
      rfl
  · have e : (ind (o', g') : WVO (IS I0) → C) w = 0 := if_neg hw
    simp only [e, mul_zero, Finset.sum_const_zero]
    split_ifs
    · rw [Pi.mul_apply, e, mul_zero]
    · rfl

section Pack2

variable {Y p} {γ γ' : Orb → Fin 2 → Fin 2 → Pt C 1 dd} (hs : SelfSep Y p) (hG : ∀ o, GmPack Y (p o) (γ o) (γ' o))

include hs hG

theorem GK_ind (s : Orb × Fin 2) : GK Y p (ind s) := by
  rw [ind_eq Y p s]
  exact GK.sum Y p Finset.univ fun r _ => GK.mulG' hs hG s.1 r (1 - s.2) (GK_col Y p r)

end Pack2

theorem toAllS_expPtS (o : Orb) (g col : Fin 2) (i : Fin dd) :
    toAllS (I := IS I0) o ((Y.rawSelf (p o)).expPt g (col, i)) = EK Y p (lamG Y p o col g * ind (o, g)) i := by
  unfold toAllS RawChart.expPt
  have h0 : ∀ x : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (∑ c : I0 o, (Y.rawSelf (p o)).u g c x •
      (MvPowerSeries.X (⟨g, c⟩ : WV (IS I0 o)) : MvPowerSeries (WV (IS I0 o)) C)) = 0 := by
    intro m
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  show MvPowerSeries.subst _ (MvPowerSeries.subst _ (MvPowerSeries.subst
    (fun x : Fin dd => (MvPowerSeries.X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C)) (VP.e Y i))) = _
  rw [VP.subst_subst (fun _ => VP.cc_X _) h0, VP.subst_subst (fun m => by rw [VP.subst_X h0]; exact h0 _) (fun _ => VP.cc_X _)]
  show _ = MvPowerSeries.subst _ (VP.e Y i)
  congr 1
  funext m
  rw [VP.subst_X h0, VP.subst_sum (fun _ => VP.cc_X _)]
  unfold zeK
  rw [Fintype.sum_sigma, Finset.sum_eq_single o]
  · rw [Fintype.sum_sigma, Finset.sum_eq_single g]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [VP.subst_smul (fun _ => VP.cc_X _), VP.subst_X (fun _ => VP.cc_X _)]
      congr 1
      rw [Pi.mul_apply]
      unfold lamG ind
      rw [if_pos rfl, if_pos rfl, mul_one]
      rfl
    · intro g' _ hg'
      refine Finset.sum_eq_zero fun c _ => ?_
      have : (ind (o, g) : WVO (IS I0) → C) ⟨o, ⟨g', c⟩⟩ = 0 := if_neg fun h => hg' (Prod.mk.inj h).2
      rw [Pi.mul_apply, this, mul_zero, zero_mul, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro o' _ ho'
    refine Finset.sum_eq_zero fun x _ => ?_
    have : (ind (o, g) : WVO (IS I0) → C) ⟨o', x⟩ = 0 := if_neg fun h => ho' (Prod.mk.inj h).1
    rw [Pi.mul_apply, this, mul_zero, zero_mul, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

end VS

theorem projSelf_of {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
    [NeZero d] {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
    (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (hG : ∀ o, GmPackSt Y (p o)) : ProjSelfSt Y p := by
  intro hs o g
  choose γ γ' hG using hG
  have h : ∀ col : Fin 2, VS.GK Y p (VS.lamG Y p o col g * VS.ind (o, g)) := fun col =>
    VS.GK.mulG hs hG o col g (VS.GK_ind hs hG (o, g))
  choose P hP hPe using h
  refine ⟨fun x => P x.1 x.2, fun x => (hP x.1).2 x.2, fun x => (hP x.1).1 x.2, fun x => ?_⟩
  obtain ⟨col, i⟩ := x
  rw [VS.toAllS_expPtS]
  exact hPe col i

end Formalism.L2.FormalSeriesBounds
