module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatPassesToLocalCongruence
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinates
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRowLatticeOrthogonalSplitPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PulledLocalGraphsEqIffIdentificationsCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PulledLocalGraphsEqIffIdentificationsCompatible
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PullGraph

section Abs

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}

theorem mem_perp (H : HermSp M V) {S : Submodule E V} {v : V} : v ∈ H.perp S ↔ ∀ x ∈ S, H.h v x = 0 := Iff.rfl

theorem h_smul_right (H : HermSp M V) (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem mem_smulLat (H : HermSp M V) (c : E) (Λ : Submodule M.L.O V) {x : V} :
    x ∈ H.smulLat c Λ ↔ ∃ v ∈ Λ, x = c • v := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨v, hv, rfl⟩ := hx; exact ⟨v, hv, rfl⟩
    | zero => exact ⟨0, Λ.zero_mem, (smul_zero c).symm⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨v, hv, rfl⟩ := ihx
      obtain ⟨w, hw, rfl⟩ := ihy
      exact ⟨v + w, Λ.add_mem hv hw, (smul_add c v w).symm⟩
    | smul o x _ ih =>
      obtain ⟨v, hv, rfl⟩ := ih
      refine ⟨o • v, Λ.smul_mem o hv, ?_⟩
      show ((o : E)) • (c • v) = c • ((o : E) • v)
      rw [smul_smul, smul_smul, mul_comm]
  · rintro ⟨v, hv, rfl⟩
    exact Submodule.subset_span ⟨v, hv, rfl⟩

def Fam (H : HermSp M V) (Λ : Submodule M.L.O V) (f f' : Fin (r + 1) → V) (a b : V) : Prop :=
  ∃ y' ∈ Λ, ∃ y ∈ Λ, y' ∈ H.perp (H.X f') ∧ y ∈ H.perp (H.X f) ∧ y' - a ∈ H.X f' ∧ y - b ∈ H.X f ∧
    ∃ v ∈ Λ, y' - y = algebraMap F E (LocNG.theta M) • v

variable {H : HermSp M V} {Λ : Submodule M.L.O V} {f f' : Fin (r + 1) → V}

theorem fam_congr {a b a' b' : V} (h : Fam H Λ f f' a b) (ha : a - a' ∈ H.X f') (hb : b - b' ∈ H.X f) :
    Fam H Λ f f' a' b' := by
  obtain ⟨y', hy', y, hy, hP', hP, h1, h2, hv⟩ := h
  refine ⟨y', hy', y, hy, hP', hP, ?_, ?_, hv⟩
  · have e : y' - a' = (y' - a) + (a - a') := by abel
    rw [e]; exact add_mem h1 ha
  · have e : y - b' = (y - b) + (b - b') := by abel
    rw [e]; exact add_mem h2 hb

theorem fam_iff {a b : V} : Fam H Λ f f' a b ↔ ∃ x' ∈ Λ, ∃ x ∈ Λ, x' ∈ H.perp (H.X f') ∧ x ∈ H.perp (H.X f) ∧
    a - x' ∈ H.X f' ∧ b - x ∈ H.X f ∧ Fam H Λ f f' x' x := by
  constructor
  · intro h
    obtain ⟨y', hy', y, hy, hP', hP, h1, h2, hv⟩ := h
    refine ⟨y', hy', y, hy, hP', hP, ?_, ?_, y', hy', y, hy, hP', hP, by simp, by simp, hv⟩
    · have := neg_mem h1; simpa using this
    · have := neg_mem h2; simpa using this
  · rintro ⟨x', -, x, -, -, -, ha, hb, h⟩
    refine fam_congr h ?_ ?_
    · have := neg_mem ha; simpa using this
    · have := neg_mem hb; simpa using this

theorem fam_pt (iso : H.X f ≤ H.perp (H.X f)) (iso' : H.X f' ≤ H.perp (H.X f')) {x' x : V} (hx' : x' ∈ Λ) (hx : x ∈ Λ)
    (hP' : x' ∈ H.perp (H.X f')) (hP : x ∈ H.perp (H.X f)) :
    Fam H Λ f f' x' x ↔ Cong H Λ f f' (x - x') := by
  constructor
  · rintro ⟨y', hy', y, hy, -, -, h1, h2, v, hv, e⟩
    refine ⟨-(algebraMap F E (LocNG.theta M) • v), (mem_smulLat H _ Λ).2 ⟨-v, Λ.neg_mem hv, by rw [smul_neg]⟩,
      x - y, Λ.sub_mem hx hy, y' - x', Λ.sub_mem hy' hx', ?_, h1, ?_⟩
    · have := neg_mem h2; simpa using this
    · rw [← e]; abel
  · rintro ⟨s, hs, b₀, hb₀, c₀, hc₀, hb₀X, hc₀X, e⟩
    obtain ⟨w, hw, rfl⟩ := (mem_smulLat H _ Λ).1 hs
    refine ⟨x' + c₀, Λ.add_mem hx' hc₀, x - b₀, Λ.sub_mem hx hb₀, add_mem hP' (iso' hc₀X),
      sub_mem hP (iso hb₀X), by simpa using hc₀X, by simpa using neg_mem hb₀X, -w, Λ.neg_mem hw, ?_⟩
    have e2 : algebraMap F E (LocNG.theta M) • w = x - x' - b₀ - c₀ := by rw [e]; abel
    rw [smul_neg, e2]; abel

theorem famL_iff {f₀ f₁ : Fin (r + 1) → V} (gβ gn : V ≃ₗ[E] V)
    (hΛ : ∀ v, gβ v ∈ Λ ↔ v ∈ Λ)
    (_hX : ∀ v, gβ v ∈ H.X f₁ ↔ v ∈ H.X f₀)
    (hP : ∀ v, gβ v ∈ H.perp (H.X f₁) ↔ v ∈ H.perp (H.X f₀))
    (hnX : ∀ z, gn z ∈ H.X f₀ ↔ z ∈ H.X f₁)
    (hm : ∀ x ∈ H.perp (H.X f₀), gn (gβ x) - x ∈ H.X f₀)
    (hnA : ∀ z, gn z ∈ H.X f ↔ z ∈ H.X f)
    (hnP : ∀ y ∈ H.perp (H.X f), gn y - y ∈ H.X f) {a b : V} :
    Fam H Λ f f₁ (gn.symm a) (gn.symm b) ↔ ∃ x' ∈ Λ, ∃ x ∈ Λ, x' ∈ H.perp (H.X f₀) ∧ x ∈ H.perp (H.X f) ∧
      a - x' ∈ H.X f₀ ∧ b - x ∈ H.X f ∧ Fam H Λ f f₁ (gβ x') x := by
  constructor
  · rintro ⟨y', hy', y, hy, hyP1, hyP, h1, h2, hv⟩
    have hx'Λ : gβ.symm y' ∈ Λ := (hΛ _).1 (by simpa using hy')
    have hx'P : gβ.symm y' ∈ H.perp (H.X f₀) := (hP _).1 (by simpa using hyP1)
    refine ⟨gβ.symm y', hx'Λ, y, hy, hx'P, hyP, ?_, ?_, ?_⟩
    · have k1 := (hnX _).2 h1
      rw [map_sub, LinearEquiv.apply_symm_apply] at k1
      have k2 := hm _ hx'P
      rw [LinearEquiv.apply_symm_apply] at k2
      have e : a - gβ.symm y' = (gn y' - gβ.symm y') - (gn y' - a) := by abel
      rw [e]; exact sub_mem k2 k1
    · have k1 := (hnA _).2 h2
      rw [map_sub, LinearEquiv.apply_symm_apply] at k1
      have k2 := hnP y hyP
      have e : b - y = (gn y - y) - (gn y - b) := by abel
      rw [e]; exact sub_mem k2 k1
    · rw [LinearEquiv.apply_symm_apply]
      exact ⟨y', hy', y, hy, hyP1, hyP, by simp, by simp, hv⟩
  · rintro ⟨x', hx', x, hx, hx'P, hxP, ha, hb, y', hy', y, hy, hyP1, hyP, h1, h2, hv⟩
    refine ⟨y', hy', y, hy, hyP1, hyP, ?_, ?_, hv⟩
    · rw [← hnX, map_sub, LinearEquiv.apply_symm_apply]
      have k1 := (hnX _).2 h1
      rw [map_sub] at k1
      have k2 := hm _ hx'P
      have e : gn y' - a = (gn y' - gn (gβ x')) + (gn (gβ x') - x') - (a - x') := by abel
      rw [e]; exact sub_mem (add_mem k1 k2) ha
    · rw [← hnA, map_sub, LinearEquiv.apply_symm_apply]
      have k2 := hnP y hyP
      have e : gn y - b = (gn y - y) + (y - x) - (b - x) := by abel
      rw [e]; exact sub_mem (add_mem k2 h2) hb

theorem main_abs {f₀ f₁ : Fin (r + 1) → V} (gβ gn : V ≃ₗ[E] V)
    (hΛ : ∀ v, gβ v ∈ Λ ↔ v ∈ Λ)
    (hX : ∀ v, gβ v ∈ H.X f₁ ↔ v ∈ H.X f₀)
    (hP : ∀ v, gβ v ∈ H.perp (H.X f₁) ↔ v ∈ H.perp (H.X f₀))
    (hnX : ∀ z, gn z ∈ H.X f₀ ↔ z ∈ H.X f₁)
    (hm : ∀ x ∈ H.perp (H.X f₀), gn (gβ x) - x ∈ H.X f₀)
    (hnA : ∀ z, gn z ∈ H.X f ↔ z ∈ H.X f)
    (hnP : ∀ y ∈ H.perp (H.X f), gn y - y ∈ H.X f)
    (isoA : H.X f ≤ H.perp (H.X f)) (iso0 : H.X f₀ ≤ H.perp (H.X f₀)) :
    (∀ a b, Fam H Λ f f₁ (gn.symm a) (gn.symm b) ↔ Fam H Λ f f₀ a b) ↔
      ∀ x' ∈ Λ, ∀ x ∈ Λ, x' ∈ H.perp (H.X f₀) → x ∈ H.perp (H.X f) →
        (Cong H Λ f f₀ (x - x') ↔ Cong H Λ f f₁ (x - gβ x')) := by
  have iso1 : H.X f₁ ≤ H.perp (H.X f₁) := by
    intro z hz
    have h1 : gβ.symm z ∈ H.X f₀ := (hX _).1 (by simpa using hz)
    have h2 := (hP _).2 (iso0 h1)
    simpa using h2
  have Lpt : ∀ x' ∈ Λ, ∀ x ∈ Λ, x' ∈ H.perp (H.X f₀) → x ∈ H.perp (H.X f) →
      (Fam H Λ f f₁ (gn.symm x') (gn.symm x) ↔ Fam H Λ f f₁ (gβ x') x) := by
    intro x' hx' x hx hx'P hxP
    rw [famL_iff gβ gn hΛ hX hP hnX hm hnA hnP]
    constructor
    · rintro ⟨x₁, -, x₂, -, -, -, h1, h2, h⟩
      refine fam_congr h ?_ ?_
      · rw [← map_sub]; refine (hX _).2 ?_
        have := neg_mem h1; simpa using this
      · have := neg_mem h2; simpa using this
    · intro h
      exact ⟨x', hx', x, hx, hx'P, hxP, by simp, by simp, h⟩
  constructor
  · intro h x' hx' x hx hx'P hxP
    rw [← fam_pt isoA iso0 hx' hx hx'P hxP, ← fam_pt isoA iso1 ((hΛ _).2 hx') hx ((hP _).2 hx'P) hxP,
      ← Lpt x' hx' x hx hx'P hxP, h]
  · intro h a b
    rw [famL_iff gβ gn hΛ hX hP hnX hm hnA hnP, fam_iff]
    constructor
    · rintro ⟨x', hx', x, hx, hx'P, hxP, ha, hb, k⟩
      refine ⟨x', hx', x, hx, hx'P, hxP, ha, hb, ?_⟩
      rw [fam_pt isoA iso1 ((hΛ _).2 hx') hx ((hP _).2 hx'P) hxP, ← h x' hx' x hx hx'P hxP] at k
      exact (fam_pt isoA iso0 hx' hx hx'P hxP).2 k
    · rintro ⟨x', hx', x, hx, hx'P, hxP, ha, hb, k⟩
      refine ⟨x', hx', x, hx, hx'P, hxP, ha, hb, ?_⟩
      rw [fam_pt isoA iso0 hx' hx hx'P hxP, h x' hx' x hx hx'P hxP] at k
      exact (fam_pt isoA iso1 ((hΛ _).2 hx') hx ((hP _).2 hx'P) hxP).2 k

end Abs

end GlobalTheory.PullGraph

namespace GlobalTheory.PullGraph

section Gen

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ} {H : HermSp M V}

theorem nu_keepX {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : g ∈ NU H f) {z : V} (hz : z ∈ H.X f) :
    g z ∈ H.X f := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    have h1 := hg.2.1 a
    have h2 : Submodule.span E ((fun b : Fin r => f b.castSucc) '' {b | b < a}) ≤ H.X f :=
      Submodule.span_mono (Set.image_subset_range _ _)
    have e : g (f a.castSucc) = (g (f a.castSucc) - f a.castSucc) + f a.castSucc := by abel
    rw [e]; exact add_mem (h2 h1) (Submodule.subset_span ⟨a, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem nu_X_iff {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : g ∈ NU H f) (hg' : g.symm ∈ NU H f) (z : V) :
    g z ∈ H.X f ↔ z ∈ H.X f :=
  ⟨fun h => by simpa using nu_keepX hg' h, nu_keepX hg⟩

theorem perp_iff_of_map {g : V ≃ₗ[E] V} (hu : IsUnitary H g) {S S' : Submodule E V} (hS : ∀ v, g v ∈ S' ↔ v ∈ S)
    (v : V) : g v ∈ H.perp S' ↔ v ∈ H.perp S := by
  rw [mem_perp, mem_perp]
  constructor
  · intro hv x hx
    rw [← hu]; exact hv _ ((hS x).2 hx)
  · intro hv y hy
    have := hv _ ((hS (g.symm y)).1 (by simpa using hy))
    rw [← hu v (g.symm y), LinearEquiv.apply_symm_apply] at this
    exact this

theorem X_iff_of_map {g : V ≃ₗ[E] V} {f f' : Fin (r + 1) → V} (h : ∀ a, g (f a) = f' a) (v : V) :
    g v ∈ H.X f' ↔ v ∈ H.X f := by
  have hm : (H.X f).map (g : V →ₗ[E] V) = H.X f' := by
    simp only [HermSp.X]
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
    ext x
    simp [h]
  rw [← hm, Submodule.mem_map_equiv]
  simp

theorem X_le_perp_of (f : Fin (r + 1) → V) (h0 : ∀ a b : Fin r, H.h (f a.castSucc) (f b.castSucc) = 0) :
    H.X f ≤ H.perp (H.X f) := by
  have s1 : ∀ x ∈ H.X f, ∀ b : Fin r, H.h x (f b.castSucc) = 0 := by
    intro x hx b
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h0 a b
    | zero => exact H.h_zero_left _
    | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]
  intro y hy
  rw [mem_perp]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨b, rfl⟩ := hx; exact s1 y hy b
  | zero => rw [H.h_herm 0 y, H.h_zero_left, map_zero]
  | add x x' _ _ hx hx' =>
    rw [H.h_herm (x + x') y, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm, hx, hx', add_zero]
  | smul c x _ hx => rw [h_smul_right, hx, mul_zero]

end Gen

section Glob

variable {D : D7}

theorem scaled_iso (Z : LocDat D) (p : PlF D) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) :
    (locH Z p).X (scaled Z p (frame F)) ≤ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F))) := by
  refine X_le_perp_of _ fun a b => ?_
  simp only [scaled, GlobalTheory.LocExt.frame_castSucc]
  rw [(locH Z p).h_smul_left, h_smul_right]
  show _ * (_ * LocFacts₂ Z.M p _ _) = 0
  rw [baseChangeAt_form Z.M p (Z.hcj p)]
  simp [brS, F.fl.e_iso]

theorem ext_trans {p : PlF D} {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V} {ga gb : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p}
    (ha : Ext p a ga) (hb : Ext p b gb) : Ext p (a * b) (gb.trans ga) := fun x => by
  show ga (gb (baseChange₂ D p x)) = baseChange₂ D p (a (b x))
  rw [hb, ha]

theorem ext_symm {p : PlF D} {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p}
    (h : Ext p a g) : Ext p a⁻¹ g.symm := fun x => by
  rw [LinearEquiv.symm_apply_eq, h]
  show baseChange₂ D p x = baseChange₂ D p (a (a.symm x))
  rw [LinearEquiv.apply_symm_apply]

theorem nu_of_ext (Z : LocDat D) (p : PlF D) {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T}
    {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hN : γ ∈ NRat F) (h : Ext p γ g) :
    g ∈ NU (locH Z p) (scaled Z p (frame F)) := by
  rw [GlobalTheory.LocExt.locEquiv_unique p γ g h]
  exact GlobalTheory.LocExt.locEquiv_NU Z p γ F hN

end Glob

end GlobalTheory.PullGraph

namespace GlobalTheory.PullGraph

variable {D : D7}

theorem pulled_iff_local (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Z : LocDat D) (t₀ t : TauC Y u u')
    (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hl : t.lam = t₀.lam) (hl' : t.lam' = t₀.lam')
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (ht : t.lin = n⁻¹ * t₀.lin * m)
    (p : PlF D) (gn : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hgn : Ext p n gn) :
    (∀ a b, Fam (locH Z p) (lattice₂ D Z.M p t₀.lam) (scaled Z p (frame (lf D (X.Fu u)))) (scaled Z p (frame t.frame))
        (gn.symm a) (gn.symm b) ↔
      Fam (locH Z p) (lattice₂ D Z.M p t₀.lam) (scaled Z p (frame (lf D (X.Fu u)))) (scaled Z p (frame t₀.frame)) a b) ↔
    (∀ gβ, Ext p (t.lin * t₀.lin⁻¹) gβ → ∀ x' ∈ lattice₂ D Z.M p t₀.lam, ∀ x ∈ lattice₂ D Z.M p t₀.lam,
      x' ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame t₀.frame))) →
      x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame (lf D (X.Fu u))))) →
      (Cong (locH Z p) (lattice₂ D Z.M p t₀.lam) (scaled Z p (frame (lf D (X.Fu u)))) (scaled Z p (frame t₀.frame)) (x - x') ↔
        Cong (locH Z p) (lattice₂ D Z.M p t₀.lam) (scaled Z p (frame (lf D (X.Fu u)))) (scaled Z p (frame t.frame))
          (x - gβ x'))) := by
  have hi0 : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have hi1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hβ : t.lin * t₀.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hi1 ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hi0)
  have hβΛ : Formalism.HermitianLatticesTheory.gmap (t.lin * t₀.lin⁻¹) t₀.lam = t₀.lam := by
    have hg0 : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
    have hg1 : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
    calc Formalism.HermitianLatticesTheory.gmap (t.lin * t₀.lin⁻¹) t₀.lam
        = Formalism.HermitianLatticesTheory.gmap t.lin (Formalism.HermitianLatticesTheory.gmap t₀.lin⁻¹ (Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam')) := by
          rw [Formalism.L2.SG.Pf.gmap_mul_sat, hg0]
      _ = t₀.lam := by rw [Formalism.L2.SG.Pf.gmap_inv_gmap, ← hl', hg1, hl]
  have hfr : ∀ a, (t.lin * t₀.lin⁻¹) (frame t₀.frame a) = frame t.frame a := by
    intro a
    show (t.lin * t₀.lin⁻¹) (frame (mapLF t₀.lin (lf D (X.Fu u'))) a) = frame (mapLF t.lin (lf D (X.Fu u'))) a
    rw [Formalism.L2.SG.Pf.Act.frame_mapLF hi0, Formalism.L2.SG.Pf.Act.frame_mapLF hi1]
    show t.lin (t₀.lin.symm (t₀.lin _)) = _
    rw [LinearEquiv.symm_apply_apply]
  have hm0 : n * (t.lin * t₀.lin⁻¹) ∈ NRat t₀.frame := by
    have e : n * (t.lin * t₀.lin⁻¹) = t₀.lin * m * t₀.lin⁻¹ := by rw [ht]; group
    rw [e]
    exact GlobalTheory.StabCnt.nrat_conj (GlobalTheory.StabCnt.adapt_mapLF hi0) hm
  have hgβ : Ext p (t.lin * t₀.lin⁻¹) (GlobalTheory.LocExt.locEquiv p (t.lin * t₀.lin⁻¹)) := GlobalTheory.LocExt.locEquiv_ext p _
  have huβ := GlobalTheory.LocExt.locEquiv_unitary Z p _ hβ
  have hgf : ∀ a, GlobalTheory.LocExt.locEquiv p (t.lin * t₀.lin⁻¹) (scaled Z p (frame t₀.frame) a) =
      scaled Z p (frame t.frame) a := by
    intro a
    simp only [scaled, map_smul, hgβ _, hfr]
  have hXβ := X_iff_of_map (H := locH Z p) hgf
  have hPβ := perp_iff_of_map huβ hXβ
  have hΛ : ∀ v, GlobalTheory.LocExt.locEquiv p (t.lin * t₀.lin⁻¹) v ∈ lattice₂ D Z.M p t₀.lam ↔ v ∈ lattice₂ D Z.M p t₀.lam := by
    have himg := GlobalTheory.LocExt.locEquiv_img Z p (t.lin * t₀.lin⁻¹) t₀.lam
    rw [hβΛ] at himg
    intro v
    constructor
    · intro hv
      rw [← himg] at hv
      obtain ⟨w, hw, e⟩ := Submodule.mem_map.1 hv
      have : w = v := (GlobalTheory.LocExt.locEquiv p (t.lin * t₀.lin⁻¹)).injective e
      rwa [← this]
    · intro hv
      rw [← himg]
      exact Submodule.mem_map_of_mem hv
  have hg0 := ext_trans hgn hgβ
  have hNU0 := nu_of_ext Z p hm0 hg0
  have hNU0' := nu_of_ext Z p (GlobalTheory.StabCnt.nrat_inv hm0) (ext_symm hg0)
  have hnN := nu_of_ext Z p hn hgn
  have hnN' := nu_of_ext Z p (GlobalTheory.StabCnt.nrat_inv hn) (ext_symm hgn)
  have hnX : ∀ z, gn z ∈ (locH Z p).X (scaled Z p (frame t₀.frame)) ↔ z ∈ (locH Z p).X (scaled Z p (frame t.frame)) := by
    intro z
    have e : gn z = ((GlobalTheory.LocExt.locEquiv p (t.lin * t₀.lin⁻¹)).trans gn)
        ((GlobalTheory.LocExt.locEquiv p (t.lin * t₀.lin⁻¹)).symm z) := by simp
    rw [e, nu_X_iff hNU0 hNU0', ← hXβ, LinearEquiv.apply_symm_apply]
  have hmm : ∀ x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame t₀.frame))),
      gn (GlobalTheory.LocExt.locEquiv p (t.lin * t₀.lin⁻¹) x) - x ∈ (locH Z p).X (scaled Z p (frame t₀.frame)) :=
    fun x hx => hNU0.2.2 x hx
  have key := main_abs (GlobalTheory.LocExt.locEquiv p (t.lin * t₀.lin⁻¹)) gn hΛ hXβ hPβ hnX hmm (nu_X_iff hnN hnN') hnN.2.2
    (scaled_iso Z p _) (scaled_iso Z p _)
  constructor
  · intro h gβ hgβ'
    rw [GlobalTheory.LocExt.locEquiv_unique p _ gβ hgβ']
    exact key.1 h
  · intro h
    exact key.2 (h _ hgβ)

theorem pulled_graph_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t₀ t : TauC Y u u') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V), t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∀ (p : PlF D) (gn : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p), Ext p n gn → ((∀ a b : Vp D p, (∃ y' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, ∃ y ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, y' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame))) ∧ y ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) ∧ y' - gn.symm a ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame)) ∧ y - gn.symm b ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) ∧ ∃ v ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, y' - y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (LocNG.theta ((⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p)) • v) ↔ (∃ y' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, ∃ y ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, y' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame))) ∧ y ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) ∧ y' - a ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame)) ∧ y - b ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) ∧ ∃ v ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, y' - y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (LocNG.theta ((⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p)) • v)) ↔ (∀ gβ, Ext p (t.lin * t₀.lin⁻¹) gβ → ∀ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, ∀ x ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, x' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame))) → x ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) → (Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame)) (x - x') ↔ Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame)) (x - gβ x')))) := by
  intro D X Y u u' t₀ t n m hl hl' hnm p gn hgn
  exact pulled_iff_local X Y u u' _ t₀ t n m hl hl' hnm.1 hnm.2.1 hnm.2.2 p gn hgn

end GlobalTheory.PullGraph
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PulledLocalGraphsEqIffIdentificationsCompatibleStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledLocalGraphs_eq_iff_identificationsCompatible : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t₀ t : TauC Y u u') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V), t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∀ (p : PlF D) (gn : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p), Ext p n gn → ((∀ a b : Vp D p, (∃ y' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, ∃ y ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, y' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame))) ∧ y ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) ∧ y' - gn.symm a ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame)) ∧ y - gn.symm b ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) ∧ ∃ v ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, y' - y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (LocNG.theta ((⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p)) • v) ↔ (∃ y' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, ∃ y ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, y' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame))) ∧ y ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) ∧ y' - a ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame)) ∧ y - b ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) ∧ ∃ v ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, y' - y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (LocNG.theta ((⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p)) • v)) ↔ (∀ gβ, Ext p (t.lin * t₀.lin⁻¹) gβ → ∀ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, ∀ x ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, x' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame))) → x ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) → (Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame)) (x - x') ↔ Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame)) (x - gβ x')))) := by
  first | exact @GlobalTheory.PullGraph.pulled_graph_iff | exact GlobalTheory.PullGraph.pulled_graph_iff | (intros; apply GlobalTheory.PullGraph.pulled_graph_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalThetaGraphRationalIsometryMovedLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalThetaGraphRationalIsometryMovedLattice
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GraphTr

theorem span_tri_le {K W : Type*} [Semiring K] [AddCommMonoid W] [Module K W] {n r : ℕ}
    (f g : Fin n → W) (A : Matrix (Fin n) (Fin n) K) (hA : ∀ a b, b < a → A a b = 0)
    (hg : ∀ b, g b = ∑ a, A a b • f a) :
    Submodule.span K (g '' {i | (i : ℕ) < r}) ≤ Submodule.span K (f '' {i | (i : ℕ) < r}) := by
  rw [Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  rw [hg b]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases hab : b < a
  · rw [hA a b hab, zero_smul]; exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ?_, rfl⟩)
    show (a : ℕ) < r
    exact lt_of_le_of_lt (Fin.le_iff_val_le_val.1 (not_lt.1 hab)) hb

theorem inv_rel {K W : Type*} [CommRing K] [AddCommGroup W] [Module K W] {n : ℕ}
    (f g : Fin n → W) (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A.det)
    (hg : ∀ b, g b = ∑ a, A a b • f a) : ∀ b, f b = ∑ a, A⁻¹ a b • g a := by
  intro b
  simp_rw [hg, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have h : ∀ c, ∑ a, A⁻¹ a b * A c a = (A * A⁻¹) c b := fun c => by
    rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  simp_rw [h, Matrix.mul_nonsing_inv _ hA, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

theorem range_castSucc {W : Type*} {r : ℕ} (f : Fin (r + 1) → W) :
    Set.range (fun a : Fin r => f a.castSucc) = f '' {i | (i : ℕ) < r} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a.castSucc, by simp, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, congrArg f (Fin.ext rfl)⟩

theorem span_units {K W ι : Type*} [CommRing K] [AddCommGroup W] [Module K W] (u : ι → K)
    (hu : ∀ a, IsUnit (u a)) (v : ι → W) (S : Set ι) :
    Submodule.span K ((fun a => u a • v a) '' S) = Submodule.span K (v '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]; rintro _ ⟨a, ha, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  · rw [Submodule.span_le]; rintro _ ⟨a, ha, rfl⟩
    obtain ⟨w, hw⟩ := hu a
    have h : u a • v a ∈ Submodule.span K ((fun a => u a • v a) '' S) := Submodule.subset_span ⟨a, ha, rfl⟩
    have h2 := Submodule.smul_mem _ ((w⁻¹ : Kˣ) : K) h
    rwa [smul_smul, ← hw, Units.inv_mul, one_smul] at h2

end GlobalTheory.GraphTr

namespace GlobalTheory.GraphTr

variable {D : D7}

theorem frFac_isUnit (Z : LocDat D) (p : PlF D) (a : Fin (D.R.rS + 1)) : IsUnit (frFac Z.δ p a) := by
  unfold frFac
  have hδ : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)) :=
    (Ne.isUnit (Z.agree p).2.1).map _
  have hg : ∀ i, D.host.g i ≠ 0 := fun i => (D.host.g_prime i).ne_zero
  have hgp : gpart p ≠ 0 := by
    unfold gpart; split_ifs <;> simp [hg]
  have hgS : (Formalism.MainNotions.S.Lat.gS D : ℚ) ≠ 0 := by
    unfold Formalism.MainNotions.S.Lat.gS; push_cast
    exact mul_ne_zero (by exact_mod_cast hg 0) (by exact_mod_cast hg 1)
  have hu : ((uP p : ℚ) : D.host.E) ≠ 0 := by
    rw [Rat.cast_ne_zero]; unfold uP; exact div_ne_zero (by exact_mod_cast hgp) hgS
  have hι : IsUnit ((D.s.atP p).ιE ((uP p : ℚ) : D.host.E)) := (Ne.isUnit hu).map _
  obtain ⟨w, hw⟩ := (hδ.mul hι).pow (D.R.rS - a.val)
  rw [← hw, Ring.inverse_unit]
  exact Units.isUnit _

theorem span_bc (p : PlF D) (s : Set (VS D).V) :
    Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (Submodule.span D.host.E s : Set (VS D).V)) =
      Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' s) := by
  apply le_antisymm
  · rw [Submodule.span_le]; rintro _ ⟨x, hx, rfl⟩; exact GlobalTheory.LocExt.baseChange_mem_span p hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem X_eq (Z : LocDat D) (p : PlF D) (f : Fin (D.R.rS + 1) → (VS D).V) :
    (locH Z p).X (scaled Z p f) = Submodule.span (D.s.atP p).Ep
      (baseChange₂ D p '' (Submodule.span D.host.E (f '' {i | (i : ℕ) < D.R.rS}) : Set (VS D).V)) := by
  rw [span_bc, Set.image_image]
  unfold Formalism.MainNotions.S.Loc.HermSp.X
  rw [range_castSucc]
  exact span_units (fun a => frFac Z.δ p a) (frFac_isUnit Z p) (fun a => baseChange₂ D p (f a)) _

theorem rat_span_eq (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (f f0 : Fin (D.R.rS + 1) → (VS D).V)
    (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (hU : IsUpUni U)
    (hσ : ∀ b, σ (f b) = ∑ a, U a b • f0 a) (r : ℕ) :
    (Submodule.span D.host.E (f '' {i | (i : ℕ) < r})).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) =
      Submodule.span D.host.E (f0 '' {i | (i : ℕ) < r}) := by
  rw [Submodule.map_span, Set.image_image]
  have hA : ∀ a b, b < a → U a b = 0 := fun a b h => (hU a b).1 h
  have hd : ∀ i, U i i = 1 := fun i => (hU i i).2 rfl
  have hdet : IsUnit U.det := by
    rw [Matrix.det_of_upperTriangular (by intro i j h; exact (hU i j).1 h)]
    simp [hd]
  apply le_antisymm
  · exact span_tri_le f0 (fun b => σ (f b)) U hA hσ
  · exact span_tri_le (fun b => σ (f b)) f0 U⁻¹ (inv_unitri U hA hd).1
      (inv_rel f0 (fun b => σ (f b)) U hdet hσ)

theorem map_X (Z : LocDat D) (p : PlF D) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (gσ : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hE : Ext p σ gσ) (f f0 : Fin (D.R.rS + 1) → (VS D).V)
    (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (hU : IsUpUni U)
    (hσ : ∀ b, σ (f b) = ∑ a, U a b • f0 a) :
    ((locH Z p).X (scaled Z p f)).map (gσ : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p) =
      (locH Z p).X (scaled Z p f0) := by
  rw [X_eq, X_eq, Submodule.map_span, Set.image_image, ← rat_span_eq σ f f0 U hU hσ, Submodule.map_coe,
    Set.image_image]
  congr 1
  apply Set.image_congr
  intro x _
  exact hE x

end GlobalTheory.GraphTr

namespace GlobalTheory.GraphTr

variable {D : D7}

section Coord

variable {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (D.sp.Y 0) D.R.rS T} {F0' : LFlag (D.sp.Y 0) D.R.rS T'}
  {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k}

theorem framesX (c : GCoord Z F0 F0' FP G) (p : PlF D) (hA : (FP p).A.f = scaled Z p (frame F0)) :
    (G.S p).X = ((locH Z p).X (scaled Z p (frame F0))).map
      (c.c p).e.toLinearMap := by
  unfold Frames.X Frames.spanTo Formalism.MainNotions.S.Loc.HermSp.X
  rw [range_castSucc, Submodule.map_span, Set.image_image]
  congr 1
  apply Set.image_congr
  intro a _
  rw [(c.c p).f_eq a, hA]
  rfl

theorem framesX' (c : GCoord Z F0 F0' FP G) (p : PlF D) (hB : (FP p).B.f = scaled Z p (frame F0')) :
    (G.S p).X' = ((locH Z p).X (scaled Z p (frame F0'))).map
      (c.c p).e.toLinearMap := by
  unfold Frames.X' Frames.spanTo Formalism.MainNotions.S.Loc.HermSp.X
  rw [range_castSucc, Submodule.map_span, Set.image_image]
  congr 1
  apply Set.image_congr
  intro a _
  rw [(c.c p).f'_eq a, hB]
  rfl

theorem lat_eq (c : GCoord Z F0 F0' FP G) (p : PlF D) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (gσ : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hE : Ext p σ gσ) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (placesOf Z).lat p (c.lat σ Λ) = (c.c p).lat (LocNG.img (M := Z.M p) gσ (lattice₂ D Z.M p Λ)) := by
  have hs : (placesOf Z).bc p '' ((c.lat σ Λ : Submodule (𝓞 D.host.E) G.V) : Set G.V) =
      ((fun y => (c.c p).e (gσ (baseChange₂ D p y))) '' (Λ : Set (VS D).V)) := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      show (c.c p).e (gσ (baseChange₂ D p y)) = (placesOf Z).bc p (c.e (σ y))
      rw [hE y]; exact c.compat p (σ y)
    · rintro ⟨y, hy, rfl⟩
      refine ⟨c.e (σ y), ⟨y, hy, rfl⟩, ?_⟩
      show (placesOf Z).bc p (c.e (σ y)) = (c.c p).e (gσ (baseChange₂ D p y))
      rw [hE y]; exact (c.compat p (σ y)).symm
  unfold WCoord.lat LocNG.img lattice₂ Places.lat
  rw [Submodule.map_span, Submodule.map_span, Set.image_image, Set.image_image, hs]
  rfl

theorem th_eq (c : GCoord Z F0 F0' FP G) (p : PlF D) : (G.S p).th = LocNG.theta (Z.M p) := by
  unfold Frames.th LocNG.theta
  rcases h : (Z.M p).split with _ | g
  · simp [(c.c p).gg_none h]; rfl
  · obtain ⟨h1, h2⟩ := (c.c p).gg_some g h
    simp [h1, h2]

end Coord

end GlobalTheory.GraphTr

namespace GlobalTheory.GraphTr

section Gen

open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
  {P : LocNG.FPair H r} {S : Frames M.L r k}

theorem mem_map_eg (c : WCoord P S) (g : V ≃ₗ[E] V) (W : Submodule E V) (y : V) :
    c.e (g y) ∈ (W.map (g : V →ₗ[E] V)).map (c.e : V →ₗ[E] S.V) ↔ y ∈ W := by
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, hx⟩
    have : z = y := g.injective (c.e.injective hx)
    exact this ▸ hz
  · intro hy; exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩

theorem mem_lat_eg (c : WCoord P S) (g : V ≃ₗ[E] V) (Λ0 : Submodule M.L.O V) (y : V) :
    c.e (g y) ∈ c.lat (LocNG.img g Λ0) ↔ y ∈ Λ0 := by
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, hx⟩
    have : z = y := g.injective (c.e.injective hx)
    exact this ▸ hz
  · intro hy; exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩

theorem h_eg (c : WCoord P S) (g : V ≃ₗ[E] V) (hg : LocNG.IsUnitary H g) (x y : V) :
    hf M.L S.Hm (c.e (g x)) (c.e (g y)) = H.h x y := by
  have h := c.h_eq (g x) (g y)
  rw [hg] at h
  exact h

theorem mem_perp_eg (c : WCoord P S) (g : V ≃ₗ[E] V) (hg : LocNG.IsUnitary H g) (W : Submodule E V) (y : V) :
    c.e (g y) ∈ perp M.L S.Hm ((W.map (g : V →ₗ[E] V)).map (c.e : V →ₗ[E] S.V)) ↔ y ∈ H.perp W := by
  constructor
  · intro h x hx
    have h1 := h (c.e (g x)) ⟨g x, ⟨x, hx, rfl⟩, rfl⟩
    rwa [h_eg c g hg] at h1
  · rintro h _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    show hf M.L S.Hm (c.e (g y)) (c.e (g x)) = 0
    rw [h_eg c g hg]
    exact h x hx

theorem graphOf_coord (c : WCoord P S) (g : V ≃ₗ[E] V) (hg : LocNG.IsUnitary H g) (Λ0 : Submodule M.L.O V)
    (X1 X2 : Submodule E V) (hX1 : S.X = (X1.map (g : V →ₗ[E] V)).map (c.e : V →ₗ[E] S.V))
    (hX2 : S.X' = (X2.map (g : V →ₗ[E] V)).map (c.e : V →ₗ[E] S.V)) (θ : F) (hθ : S.th = θ)
    (q : S.V × S.V) :
    q ∈ S.graphOf (c.lat (LocNG.img g Λ0)) ↔ ∃ y' ∈ Λ0, ∃ y ∈ Λ0, y' ∈ H.perp X2 ∧ y ∈ H.perp X1 ∧
      y' - g.symm (c.e.symm q.1) ∈ X2 ∧ y - g.symm (c.e.symm q.2) ∈ X1 ∧
      ∃ v ∈ Λ0, y' - y = algebraMap F E θ • v := by
  have hs : ∀ Y : S.V, Y = c.e (g (g.symm (c.e.symm Y))) := fun Y => by simp
  have hsub : ∀ (y : V) (Y : S.V), c.e (g y) - Y = c.e (g (y - g.symm (c.e.symm Y))) := fun y Y => by
    rw [map_sub, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  constructor
  · rintro ⟨Y', hY', Y, hY, h1, h2, h3, h4, w, hw, h5⟩
    obtain ⟨y', rfl⟩ : ∃ y', Y' = c.e (g y') := ⟨_, hs Y'⟩
    obtain ⟨y, rfl⟩ : ∃ y, Y = c.e (g y) := ⟨_, hs Y⟩
    obtain ⟨v, rfl⟩ : ∃ v, w = c.e (g v) := ⟨_, hs w⟩
    refine ⟨y', (mem_lat_eg c g Λ0 y').1 hY', y, (mem_lat_eg c g Λ0 y).1 hY, ?_, ?_, ?_, ?_, v,
      (mem_lat_eg c g Λ0 v).1 hw, ?_⟩
    · rw [hX2] at h1; exact (mem_perp_eg c g hg X2 y').1 h1
    · rw [hX1] at h2; exact (mem_perp_eg c g hg X1 y).1 h2
    · rw [hX2, hsub] at h3; exact (mem_map_eg c g X2 _).1 h3
    · rw [hX1, hsub] at h4; exact (mem_map_eg c g X1 _).1 h4
    · rw [hθ, ← map_sub, ← map_sub, ← map_smul, ← map_smul] at h5
      exact g.injective (c.e.injective h5)
  · rintro ⟨y', hy', y, hy, h1, h2, h3, h4, v, hv, h5⟩
    refine ⟨c.e (g y'), (mem_lat_eg c g Λ0 y').2 hy', c.e (g y), (mem_lat_eg c g Λ0 y).2 hy, ?_, ?_, ?_, ?_,
      c.e (g v), (mem_lat_eg c g Λ0 v).2 hv, ?_⟩
    · rw [hX2]; exact (mem_perp_eg c g hg X2 y').2 h1
    · rw [hX1]; exact (mem_perp_eg c g hg X1 y).2 h2
    · rw [hX2, hsub]; exact (mem_map_eg c g X2 _).2 h3
    · rw [hX1, hsub]; exact (mem_map_eg c g X1 _).2 h4
    · rw [hθ, ← map_sub, ← map_sub, h5, map_smul, map_smul]

end Gen

end GlobalTheory.GraphTr

theorem GlobalTheory.HL.graph_moved_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (p : PlF D) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (gσ : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (U₁ U₂ : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) F₂ σ U₁ U₂ → Ext p σ gσ → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (q : (G.S p).V × (G.S p).V), (q ∈ (G.datOf (c.lat σ Λ) p).2.2 ↔ ∃ y' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p Λ, ∃ y ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p Λ, y' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame F₂))) ∧ y ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) ∧ y' - gσ.symm ((c.c p).e.symm q.1) ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame F₂)) ∧ y - gσ.symm ((c.c p).e.symm q.2) ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) ∧ ∃ v ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p Λ, y' - y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (LocNG.theta ((⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p)) • v) := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ hFP G c p σ gσ F₂ U₁ U₂ hM hE Λ q
  obtain ⟨g0, _, hu0, huniq, -⟩ := GlobalTheory.LocExt.ext_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p σ hM.1
  have hu : LocNG.IsUnitary (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) gσ := (huniq gσ hE) ▸ hu0
  have hlat := GlobalTheory.GraphTr.lat_eq c p σ gσ hE Λ
  have hX1 := GlobalTheory.GraphTr.map_X (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p σ gσ hE (frame (lf D (X.Fu u))) (frame F00) U₁
    hM.2.1 hM.2.2.2.1
  have hX2 := GlobalTheory.GraphTr.map_X (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p σ gσ hE (frame F₂) (frame F'0) U₂
    hM.2.2.1 hM.2.2.2.2
  have hF1 := GlobalTheory.GraphTr.framesX c p (hFP p).1.1
  have hF2 := GlobalTheory.GraphTr.framesX' c p (hFP p).1.2.1
  rw [← hX1] at hF1
  rw [← hX2] at hF2
  show q ∈ (G.S p).graphOf ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat σ Λ)) ↔ _
  rw [hlat]
  exact GlobalTheory.GraphTr.graphOf_coord (c.c p) gσ hu _ _ _ hF1 hF2 _ (GlobalTheory.GraphTr.th_eq c p) q
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalThetaGraphRationalIsometryMovedLatticeStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localThetaGraph_rationalIsometry_moved_lattice : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (p : PlF D) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (gσ : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (U₁ U₂ : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) F₂ σ U₁ U₂ → Ext p σ gσ → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (q : (G.S p).V × (G.S p).V), (q ∈ (G.datOf (c.lat σ Λ) p).2.2 ↔ ∃ y' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p Λ, ∃ y ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p Λ, y' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame F₂))) ∧ y ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) ∧ y' - gσ.symm ((c.c p).e.symm q.1) ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame F₂)) ∧ y - gσ.symm ((c.c p).e.symm q.2) ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) ∧ ∃ v ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p Λ, y' - y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (LocNG.theta ((⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p)) • v) := by
  first | exact @GlobalTheory.HL.graph_moved_local | exact GlobalTheory.HL.graph_moved_local | (intros; apply GlobalTheory.HL.graph_moved_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatIffLocalGraphs
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IotaGraph

open Formalism.L2.SG.Pf Formalism.L2.SG.Saturated


set_option maxHeartbeats 2000000 in
theorem graph_eq_iff_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∀ p : PlF D, ((G.datOf (c.lat (ρ * n) t.lam) p).2.2 = (G.datOf (c.lat ρ t₀.lam) p).2.2 ↔ ∀ gβ, Ext p (t.lin * t₀.lin⁻¹) gβ → ∀ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, ∀ x ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, x' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame))) → x ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) → (Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame)) (x - x') ↔ Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame)) (x - gβ x'))) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMv t n m hl hl' hnm p
  obtain ⟨hn, hm, ht⟩ := hnm
  obtain ⟨gρ, hgρ, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p ρ hMv.1
  obtain ⟨gn, hgn, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p n hn.1
  have hgρn : Ext p (ρ * n) (gρ * gn) := by
    intro x
    show gρ (gn (baseChange₂ D p x)) = baseChange₂ D p (ρ (n x))
    rw [hgn x, hgρ (n x)]
  have hmv := (GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMv).2.2.2.2.2
  obtain ⟨A, A', -, -, -, -, hMv1⟩ := hmv t n m ⟨hn, hm, ht⟩
  have h1 := GlobalTheory.T.localThetaGraph_rationalIsometry_moved_lattice D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c p (ρ * n) (gρ * gn) t.frame
    (U * A) (U' * A') hMv1 hgρn t₀.lam
  have h0 := GlobalTheory.T.localThetaGraph_rationalIsometry_moved_lattice D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c p ρ gρ t₀.frame U U' hMv hgρ t₀.lam
  have hs : ∀ x, (gρ * gn).symm x = gn.symm (gρ.symm x) := fun x => rfl
  have hlat : G.datOf (c.lat (ρ * n) t.lam) p = G.datOf (c.lat (ρ * n) t₀.lam) p :=
    congrArg (fun Λ => G.datOf (c.lat (ρ * n) Λ) p) hl
  refine Iff.trans ?_ (GlobalTheory.T.pulledLocalGraphs_eq_iff_identificationsCompatible D X Y u u' t₀ t n m hl hl' ⟨hn, hm, ht⟩ p gn hgn)
  constructor
  · intro h a b
    rw [hlat] at h
    have hq := (h1 ((c.c p).e (gρ a), (c.c p).e (gρ b))).symm.trans
      ((iff_of_eq (congrArg (fun S => ((c.c p).e (gρ a), (c.c p).e (gρ b)) ∈ S) h)).trans
        (h0 ((c.c p).e (gρ a), (c.c p).e (gρ b))))
    have e1 : ∀ x, (gρ * gn).symm ((c.c p).e.symm ((c.c p).e (gρ x))) = gn.symm x := fun x => by
      rw [hs, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    have e2 : ∀ x, gρ.symm ((c.c p).e.symm ((c.c p).e (gρ x))) = x := fun x => by
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    dsimp only at hq
    simp only [e1, e2] at hq
    exact hq
  · intro h
    rw [hlat]
    apply Set.ext
    intro q
    have hq := h (gρ.symm ((c.c p).e.symm q.1)) (gρ.symm ((c.c p).e.symm q.2))
    refine (h1 q).trans (Iff.trans ?_ (h0 q).symm)
    rw [hs, hs]
    exact hq


set_option maxHeartbeats 2000000 in
theorem iotaCompat_iff_graph : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → (IotaCompat t₀.lam (lf D (X.Fu u)) t₀.frame t.frame (t.lin * t₀.lin⁻¹) (gS D) ↔ ∀ p, (G.datOf (c.lat (ρ * n) t.lam) p).2.2 = (G.datOf (c.lat ρ t₀.lam) p).2.2) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hloc := graph_eq_iff_local D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hγ0 : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have hγ1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hβ : t.lin * t₀.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hγ1 ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hγ0)
  have hg0 : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
  have hg1 : Formalism.HermitianLatticesTheory.gmap t.lin t₀.lam' = t₀.lam := by
    have h : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
    rw [hl, hl'] at h
    exact h
  have hβΛ : Formalism.HermitianLatticesTheory.gmap (t.lin * t₀.lin⁻¹) t₀.lam = t₀.lam := by
    rw [gmap_mul_sat, ← hg0, gmap_inv_gmap, hg1, hg0]
  constructor
  · intro hI p
    rw [hloc p]
    intro gβ hgβ x' hx' x hx hx'p hxp
    by_cases hs : (Y.M p).split = none
    · obtain ⟨g0, -, -, huniq, himg, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p _ hβ
      have hg : gβ = g0 := huniq gβ hgβ
      have hgx : gβ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam := by
        have h := himg t₀.lam
        rw [hβΛ] at h
        rw [← h, hg]
        exact ⟨x', hx', rfl⟩
      have hth : LocNG.theta ((⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p) = 1 := by
        show LocNG.theta (Y.M p) = 1
        unfold LocNG.theta; rw [hs]
      have key : ∀ (f f' : Fin (D.R.rS + 1) → Vp D p) (v : Vp D p), v ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam →
          Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) f f' v := by
        intro f f' v hv
        refine ⟨v, ?_, 0, Submodule.zero_mem _, 0, Submodule.zero_mem _, Submodule.zero_mem _,
          Submodule.zero_mem _, by simp⟩
        rw [hth]
        exact Submodule.subset_span ⟨v, hv, by simp⟩
      exact ⟨fun _ => key _ _ _ (Submodule.sub_mem _ hx hgx), fun _ => key _ _ _ (Submodule.sub_mem _ hx hx')⟩
    · have hrow : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 _ t₀.mem
      have hPD0 := t₀.rep.2.2.2.2
      have hPD1 : Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u' t.frame := by
        have h : Formalism.L2.SG.TermDef.PD D t.lam (lf D (X.Fu u)) u' t.frame := t.rep.2.2.2.2
        rw [hl] at h
        exact h
      have hfr : ∀ a, frame t.frame a = (t.lin * t₀.lin⁻¹) (frame t₀.frame a) := by
        intro a
        show frame (mapLF t.lin (lf D (X.Fu u'))) a = (t.lin * t₀.lin⁻¹) (frame (mapLF t₀.lin (lf D (X.Fu u'))) a)
        rw [Formalism.L2.SG.Pf.Act.frame_mapLF hγ1, Formalism.L2.SG.Pf.Act.frame_mapLF hγ0]
        show t.lin _ = t.lin (t₀.lin.symm (t₀.lin _))
        rw [LinearEquiv.symm_apply_apply]
      exact GlobalTheory.T.identificationCompat_passes_to_local_congruence D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t₀.lam hrow t₀.frame t.frame hPD0 hPD1 _ hβ hβΛ hfr hI p gβ hgβ hs
        x' hx' x hx hx'p hxp
  · intro h
    exact GlobalTheory.T.rationalCompatibility_of_local_identifications D X Y u u' t₀ t hl hl' (fun p _ => (hloc p).1 (h p))

end GlobalTheory.IotaGraph
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatIffLocalGraphsStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.identificationCompat_iff_localGraphs : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → (IotaCompat t₀.lam (lf D (X.Fu u)) t₀.frame t.frame (t.lin * t₀.lin⁻¹) (gS D) ↔ ∀ p, (G.datOf (c.lat (ρ * n) t.lam) p).2.2 = (G.datOf (c.lat ρ t₀.lam) p).2.2) := by
  first | exact @GlobalTheory.IotaGraph.iotaCompat_iff_graph | exact GlobalTheory.IotaGraph.iotaCompat_iff_graph | (intros; apply GlobalTheory.IotaGraph.iotaCompat_iff_graph <;> assumption)
end
