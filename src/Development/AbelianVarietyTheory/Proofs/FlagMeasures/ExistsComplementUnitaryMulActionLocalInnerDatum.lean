module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplementUnitaryMulActionLocalInnerDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplementUnitaryMulActionLocalInnerDatum
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.InnerDatumAct

open Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

def FixesFrame (H : HermSp M V) (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V) : Prop :=
  IsUnitary H g ∧ ∀ b, g (f b) = f b

lemma FixesFrame.symm {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g) :
    FixesFrame H f g.symm := by
  refine ⟨fun x y => ?_, fun b => ?_⟩
  · have := hg.1 (g.symm x) (g.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  · rw [LinearEquiv.symm_apply_eq, hg.2 b]

lemma FixesFrame.mem_X {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    {v : V} (hv : v ∈ H.X f) : g v ∈ H.X f := by
  have hle : H.X f ≤ (H.X f).comap (g : V →ₗ[E] V) := by
    unfold HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, hg.2]
    exact Submodule.subset_span ⟨a, rfl⟩
  exact hle hv

lemma FixesFrame.mem_perp {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    {v : V} (hv : v ∈ H.perp (H.X f)) : g v ∈ H.perp (H.X f) := by
  show ∀ x ∈ H.X f, H.h (g v) x = 0
  intro x hx
  have hx' := hg.symm.mem_X hx
  have h1 := hg.1 v (g.symm x)
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [h1]
  exact (hv : ∀ x ∈ H.X f, H.h v x = 0) _ hx'

def perpMap {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g) :
    ↥(H.perp (H.X f)) →ₗ[E] ↥(H.perp (H.X f)) :=
  (g : V →ₗ[E] V).restrict (fun _ hv => hg.mem_perp hv)

def wMap {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g) : H.Wb f →ₗ[E] H.Wb f :=
  Submodule.mapQ _ _ (perpMap hg) (fun x hx => by
    show ((perpMap hg x : ↥(H.perp (H.X f))) : V) ∈ H.X f
    exact hg.mem_X hx)

lemma wMap_mk {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    (x : ↥(H.perp (H.X f))) : wMap hg (H.mkW f x) = H.mkW f ⟨g x, hg.mem_perp x.2⟩ := rfl

lemma mkW_congr {f : Fin (r + 1) → V} {x y : ↥(H.perp (H.X f))} (h : (x : V) = y) :
    H.mkW f x = H.mkW f y := by
  rw [Subtype.ext h]

lemma wMap_of_eq {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    {x y : ↥(H.perp (H.X f))} (h : (y : V) = g x) : wMap hg (H.mkW f x) = H.mkW f y := by
  rw [wMap_mk]; exact mkW_congr h.symm

lemma wMap_symm_of_eq {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    {x y : ↥(H.perp (H.X f))} (h : (y : V) = g x) : wMap hg.symm (H.mkW f y) = H.mkW f x := by
  rw [wMap_mk]; apply mkW_congr; simp [h]

lemma wMap_symm_wMap {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    (w : H.Wb f) : wMap hg.symm (wMap hg w) = w := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ w
  exact (congrArg (wMap hg.symm) (wMap_of_eq hg (y := ⟨g x, hg.mem_perp x.2⟩) rfl)).trans
    (wMap_symm_of_eq hg rfl)

lemma wMap_wMap_symm {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    (w : H.Wb f) : wMap hg (wMap hg.symm w) = w := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ w
  have e : (x : V) = g (g.symm x) := by simp
  exact (congrArg (wMap hg) (wMap_symm_of_eq hg (x := ⟨g.symm x, hg.symm.mem_perp x.2⟩) e)).trans
    (wMap_of_eq hg e)

lemma mem_map_wMap {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    (L : Submodule M.L.O (H.Wb f)) (w : H.Wb f) :
    w ∈ L.map ((wMap hg).restrictScalars M.L.O) ↔ wMap hg.symm w ∈ L := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    show wMap hg.symm (wMap hg u) ∈ L
    rw [wMap_symm_wMap]; exact hu
  · intro h
    exact ⟨_, h, wMap_wMap_symm hg w⟩

def InU (P : FPair H r) (g : V ≃ₗ[E] V) : Prop := FixesFrame H P.A.f g ∧ FixesFrame H P.B.f g

lemma inU_of_mem {P : FPair H r} {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) : InU P g := by
  unfold FPair.UW0 at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨⟨hx.1, fun b => (hx.2 b).1⟩, ⟨hx.1, fun b => (hx.2 b).2⟩⟩
  | one => exact ⟨⟨fun _ _ => rfl, fun _ => rfl⟩, ⟨fun _ _ => rfl, fun _ => rfl⟩⟩
  | mul x y _ _ hx hy =>
    refine ⟨⟨fun a b => ?_, fun b => ?_⟩, ⟨fun a b => ?_, fun b => ?_⟩⟩ <;>
      simp only [LinearEquiv.mul_apply]
    · rw [hx.1.1, hy.1.1]
    · rw [hy.1.2, hx.1.2]
    · rw [hx.1.1, hy.1.1]
    · rw [hy.2.2, hx.2.2]
  | inv x _ hx => exact ⟨hx.1.symm, hx.2.symm⟩

lemma isInner_map (Fr : FrameD H r) {g : V ≃ₗ[E] V} (hg : FixesFrame H Fr.f g)
    {L : Submodule M.L.O (H.Wb Fr.f)} (hL : Fr.IsInner L) :
    Fr.IsInner (L.map ((wMap hg).restrictScalars M.L.O)) := by
  obtain ⟨hfg, hdual, xz, hxz, hxzL, hprim⟩ := hL
  have hz : g.symm xz = xz := by
    rw [hxz]; exact hg.symm.2 (Fin.last r)
  refine ⟨hfg.map _, fun x => ?_, xz, hxz, ?_, fun c y hy heq => ?_⟩
  · rw [mem_map_wMap, wMap_mk, hdual]
    constructor
    · intro h y hy
      rw [mem_map_wMap, wMap_mk] at hy
      have h1 := h _ hy
      have h2 := hg.symm.1 x y
      simp only at h1
      rw [h2] at h1
      exact h1
    · intro h y hy
      have hy' : H.mkW Fr.f ⟨g y, hg.mem_perp y.2⟩ ∈ L.map ((wMap hg).restrictScalars M.L.O) := by
        rw [mem_map_wMap, wMap_symm_of_eq hg rfl]; exact hy
      have h1 := h _ hy'
      have h2 := hg.symm.1 x (g y)
      simp only [LinearEquiv.symm_apply_apply] at h2
      show H.h (g.symm x) y ∈ M.L.O
      rw [h2]; exact h1
  · rw [mem_map_wMap, wMap_mk]
    rw [mkW_congr (y := xz) hz]; exact hxzL
  · rw [mem_map_wMap] at hy
    refine hprim c ⟨g.symm y, hg.symm.mem_perp y.2⟩ ?_ ?_
    · rw [← wMap_mk]; exact hy
    · have h3 := congrArg (wMap hg.symm) heq
      rw [LinearMap.map_smul, wMap_mk, wMap_mk, mkW_congr (y := xz) hz] at h3
      exact h3

def act {P : FPair H r} {g : V ≃ₗ[E] V} (hg : InU P g) (d : Datum P) : Datum P where
  L := d.L.map ((wMap hg.1).restrictScalars M.L.O)
  L' := d.L'.map ((wMap hg.2).restrictScalars M.L.O)
  hL := isInner_map P.A hg.1 d.hL
  hL' := isInner_map P.B hg.2 d.hL'
  io := {p | (wMap hg.2.symm p.1, wMap hg.1.symm p.2) ∈ d.io}
  io_L := fun h => by
    ext p
    simp [d.io_L h]

lemma datum_ext {P : FPair H r} {d₁ d₂ : Datum P} (hL : d₁.L = d₂.L) (hL' : d₁.L' = d₂.L')
    (hio : d₁.io = d₂.io) : d₁ = d₂ := by
  cases d₁; cases d₂
  simp only at hL hL' hio
  subst hL hL' hio
  rfl

lemma moves_act {P : FPair H r} {g : V ≃ₗ[E] V} (hg : InU P g) (d : Datum P) :
    Datum.Moves g d (act hg d) := by
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_, fun x' y' x y hx' hx => ?_⟩
  · show _ ↔ _ ∈ d.L.map _
    rw [mem_map_wMap, wMap_symm_of_eq hg.1 hxy]
  · show _ ↔ _ ∈ d.L'.map _
    rw [mem_map_wMap, wMap_symm_of_eq hg.2 hxy]
  · show _ ↔ (wMap hg.2.symm _, wMap hg.1.symm _) ∈ d.io
    rw [wMap_symm_of_eq hg.2 hx', wMap_symm_of_eq hg.1 hx]

lemma moves_unique {P : FPair H r} {g : V ≃ₗ[E] V} (hg : InU P g) {d d₁ d₂ : Datum P}
    (h₁ : Datum.Moves g d d₁) (h₂ : Datum.Moves g d d₂) : d₁ = d₂ := by
  refine datum_ext ?_ ?_ ?_
  · ext w
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ w
    have e : (y : V) = g (g.symm y) := by simp
    exact (h₁.1 ⟨g.symm y, hg.1.symm.mem_perp y.2⟩ y e).symm.trans
      (h₂.1 ⟨g.symm y, hg.1.symm.mem_perp y.2⟩ y e)
  · ext w
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ w
    have e : (y : V) = g (g.symm y) := by simp
    exact (h₁.2.1 ⟨g.symm y, hg.2.symm.mem_perp y.2⟩ y e).symm.trans
      (h₂.2.1 ⟨g.symm y, hg.2.symm.mem_perp y.2⟩ y e)
  · ext ⟨w', w⟩
    obtain ⟨y', rfl⟩ := Submodule.mkQ_surjective _ w'
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ w
    have e' : (y' : V) = g (g.symm y') := by simp
    have e : (y : V) = g (g.symm y) := by simp
    exact (h₁.2.2 ⟨g.symm y', hg.2.symm.mem_perp y'.2⟩ y' ⟨g.symm y, hg.1.symm.mem_perp y.2⟩ y
      e' e).symm.trans (h₂.2.2 ⟨g.symm y', hg.2.symm.mem_perp y'.2⟩ y'
        ⟨g.symm y, hg.1.symm.mem_perp y.2⟩ y e' e)

lemma moves_one {P : FPair H r} (d : Datum P) : Datum.Moves (1 : V ≃ₗ[E] V) d d := by
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_, fun x' y' x y hx' hx => ?_⟩
  · rw [Subtype.ext hxy]
  · rw [Subtype.ext hxy]
  · rw [Subtype.ext hx, Subtype.ext hx']

lemma moves_comp {P : FPair H r} {g g' : V ≃ₗ[E] V} (hg : InU P g) {d₁ d₂ d₃ : Datum P}
    (h₁₂ : Datum.Moves g d₁ d₂) (h₂₃ : Datum.Moves g' d₂ d₃) : Datum.Moves (g' * g) d₁ d₃ := by
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_, fun x' y' x y hx' hx => ?_⟩
  · exact (h₁₂.1 x ⟨g x, hg.1.mem_perp x.2⟩ rfl).trans
      (h₂₃.1 _ y (by rw [hxy, LinearEquiv.mul_apply]))
  · exact (h₁₂.2.1 x ⟨g x, hg.2.mem_perp x.2⟩ rfl).trans
      (h₂₃.2.1 _ y (by rw [hxy, LinearEquiv.mul_apply]))
  · exact (h₁₂.2.2 x' ⟨g x', hg.2.mem_perp x'.2⟩ x ⟨g x, hg.1.mem_perp x.2⟩ rfl rfl).trans
      (h₂₃.2.2 _ y' _ y (by rw [hx', LinearEquiv.mul_apply]) (by rw [hx, LinearEquiv.mul_apply]))

theorem exists_mulAction : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∃ act : MulAction P.UW0 (LocNG.Datum P), (∀ (g : P.UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧ ∀ d (g : P.UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r k P _ _
  let sm : P.UW0 → Datum P → Datum P := fun g d => act (inU_of_mem g.2) d
  have key : ∀ (g : P.UW0) d d', Datum.Moves g.1 d d' ↔ sm g d = d' := fun g d d' =>
    ⟨fun h => moves_unique (inU_of_mem g.2) (moves_act _ d) h, fun h => h ▸ moves_act _ d⟩
  letI act' : MulAction P.UW0 (Datum P) :=
    { smul := sm
      one_smul := fun d => (key 1 d d).1 (moves_one d)
      mul_smul := fun g g' d => (key (g * g') d _).1
        (moves_comp (inU_of_mem g'.2) ((key g' d _).2 rfl) ((key g _ _).2 rfl)) }
  refine ⟨act', key, fun d g => ?_⟩
  have hS : Datum.Stab d = (MulAction.stabilizer P.UW0 d).map P.UW0.subtype := by
    unfold Datum.Stab
    have hset : {g | g ∈ P.UW0 ∧ Datum.Moves g d d} =
        ((MulAction.stabilizer P.UW0 d).map P.UW0.subtype : Set (V ≃ₗ[E] V)) := by
      ext g
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_map, MulAction.mem_stabilizer_iff,
        Subgroup.coe_subtype]
      constructor
      · rintro ⟨hg, hm⟩
        exact ⟨⟨g, hg⟩, (key ⟨g, hg⟩ d d).1 hm, rfl⟩
      · rintro ⟨g', hg', rfl⟩
        exact ⟨g'.2, (key g' d d).2 hg'⟩
    rw [hset, Subgroup.closure_eq]
  rw [hS, Subgroup.mem_map]
  constructor
  · rintro ⟨g', hg', he⟩
    have : g' = g := Subtype.ext he
    subst this
    exact MulAction.mem_stabilizer_iff.1 hg'
  · intro h
    exact ⟨g, MulAction.mem_stabilizer_iff.2 h, rfl⟩

end GlobalTheory.InnerDatumAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplementUnitaryMulActionLocalInnerDatumStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∃ act : MulAction P.UW0 (LocNG.Datum P), (∀ (g : P.UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧ ∀ d (g : P.UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d := by
  first | exact @GlobalTheory.InnerDatumAct.exists_mulAction | exact GlobalTheory.InnerDatumAct.exists_mulAction | (intros; apply GlobalTheory.InnerDatumAct.exists_mulAction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesPairingStabilizerBlockDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesPairingStabilizerBlockDiagonal
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.BlockStab

theorem exists_monomial {E : Type} [CommRing E] (bs : List (Eˣ × ℕ+)) :
    ∃ (σ β : ℕ → ℕ) (t : ℕ → Eˣ), ∀ a, a < (bs.map (fun b => (b.2 : ℕ))).sum →
      σ a < (bs.map (fun b => (b.2 : ℕ))).sum ∧ σ (σ a) = a ∧ β (σ a) = β a ∧
      ∀ b, b < (bs.map (fun b => (b.2 : ℕ))).sum →
        (sameBlock bs a b = true ↔ β a = β b) ∧ (a ≤ b → β a ≤ β b) ∧
        (β a = β b → a + σ a = b + σ b) ∧
        ptEntryL bs a b = if b = σ a then (t (β a) : E) else 0 := by
  induction bs with
  | nil => exact ⟨id, id, fun _ => 1, by simp⟩
  | cons x bs ih =>
    obtain ⟨t0, s⟩ := x
    obtain ⟨σ, β, t, h⟩ := ih
    simp only [List.map_cons, List.sum_cons]
    generalize (bs.map (fun b => (b.2 : ℕ))).sum = N at h ⊢
    refine ⟨fun a => if a < (s : ℕ) then s - 1 - a else σ (a - s) + s,
      fun a => if a < (s : ℕ) then 0 else β (a - s) + 1,
      fun k => if k = 0 then t0 else t (k - 1), fun a ha => ?_⟩
    simp only [sameBlock, ptEntryL]
    generalize (s : ℕ) = m at *
    by_cases h1 : a < m
    · have h2 : m - 1 - a < m := by omega
      simp only [h1, h2, if_true]
      refine ⟨by omega, by omega, trivial, fun b hb => ?_⟩
      by_cases h3 : b < m
      · simp only [h3, if_true]
        refine ⟨by simp, by simp, fun _ => by omega, ?_⟩
        have : a + b + 1 = m ↔ b = m - 1 - a := by omega
        simp [this]
      · have h4 : ¬ m ≤ a := by omega
        have h5 : ¬ b = m - 1 - a := by omega
        simp [h3, h4, h5]
    · obtain ⟨e1, e2, e3, e4⟩ := h (a - m) (by omega)
      have h2 : ¬ σ (a - m) + m < m := by omega
      have h4 : m ≤ a := by omega
      simp only [h1, h2, if_false, Nat.add_sub_cancel, e2, e3]
      refine ⟨by omega, by omega, trivial, fun b hb => ?_⟩
      by_cases h3 : b < m
      · have h5 : ¬ m ≤ b := by omega
        have h6 : ¬ b = σ (a - m) + m := by omega
        have h7 : ¬ a ≤ b := by omega
        simp [h3, h5, h6, h7]
      · obtain ⟨f1, f2, f3, f4⟩ := e4 (b - m) (by omega)
        have h5 : m ≤ b := by omega
        have h6 : b = σ (a - m) + m ↔ b - m = σ (a - m) := by omega
        simp only [h3, h4, h5, if_false, h6, f4]
        refine ⟨by simp [f1], fun hab => ?_, fun hab => ?_, by simp⟩
        · have := f2 (by omega); omega
        · have := f3 (by omega); omega

section
variable {E : Type} [CommRing E] {n : ℕ}

theorem inv_facts (A : Matrix (Fin n) (Fin n) E) (hA : IsUni A) :
    ∃ B : Matrix (Fin n) (Fin n) E, A * B = 1 ∧ B * A = 1 ∧ IsUni B ∧
      (∀ O : Subring E, (∀ i j, A i j ∈ O) → ∀ i j, B i j ∈ O) ∧
      ∀ β : Fin n → ℕ, (∀ i j, β i < β j → A i j = 0) → ∀ i j, β i < β j → B i j = 0 := by
  have hT : A.BlockTriangular id := fun i j h => hA.1 i j h
  have hd : A.det = 1 := by rw [Matrix.det_of_upperTriangular hT]; simp [hA.2]
  have hu : IsUnit A.det := by rw [hd]; exact isUnit_one
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A hu
  have hT' := Matrix.blockTriangular_inv_of_blockTriangular hT
  refine ⟨A⁻¹, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu, ⟨fun i j h => hT' h, fun i => ?_⟩,
    fun O hO i j => ?_, fun β hβ i j h => ?_⟩
  · have h1 : (A * A⁻¹) i i = 1 := by rw [Matrix.mul_nonsing_inv _ hu]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hA.2, one_mul] at h1
    · exact h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hA.1 i k h, zero_mul]
      · rw [hT' (show id i < id k from h), mul_zero]
    · simp
  · have h1 : A = O.subtype.mapMatrix (Matrix.of fun i j => (⟨A i j, hO i j⟩ : O)) := by
      ext i j; simp
    rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul, h1, ← RingHom.map_adjugate]
    simp
  · have h1 : A.BlockTriangular (OrderDual.toDual ∘ β) := fun i j h => hβ i j h
    exact Matrix.blockTriangular_inv_of_blockTriangular h1 (i := i) (j := j) h

theorem mul_mono (σ : Fin n → Fin n) (hσ : ∀ a, σ (σ a) = a) (c : Fin n → E)
    (Z : Matrix (Fin n) (Fin n) E) (hZ : ∀ a b, Z a b = if b = σ a then c a else 0)
    (X Y : Matrix (Fin n) (Fin n) E) :
    X * Z = Z * Y ↔ ∀ i a, X i a * c a = c i * Y (σ i) (σ a) := by
  have h1 : ∀ i a, (X * Z) i (σ a) = X i a * c a := by
    intro i a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · simp [hZ]
    · intro k _ hk
      have : ¬ σ a = σ k := fun h => hk (by rw [← hσ k, ← h, hσ])
      simp [hZ, this]
    · simp
  have h2 : ∀ i j, (Z * Y) i j = c i * Y (σ i) j := by
    intro i j
    simp [Matrix.mul_apply, hZ]
  constructor
  · intro h i a; rw [← h1, h, h2]
  · intro h; ext i j; rw [← hσ j, h1, h2, h]

end

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {n : ℕ}

theorem cj_mem_iff (L : LocE F E) {x : E} : L.cj x ∈ L.O ↔ x ∈ L.O := by
  have h : ∀ x, x ∈ L.O → L.cj x ∈ L.O := fun x hx => by
    rw [L.O_def] at hx ⊢
    exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])
  exact ⟨fun hx => by simpa [L.cj_cj] using h _ hx, h x⟩

theorem cT_mul_eq_one (L : LocE F E) (A B : Matrix (Fin n) (Fin n) E) (h : A * B = 1) :
    cT L B * cT L A = 1 := by
  ext i j
  have h1 := congrArg L.cj (congrFun (congrFun h j) i)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul] at h1
  simp only [Matrix.mul_apply, cT]
  rw [Finset.sum_congr rfl fun k _ => mul_comm _ _, h1]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply, hij, Ne.symm hij]

theorem stab_monomial (L : LocE F E) (σ : Fin n → Fin n) (β : Fin n → ℕ) (c : Fin n → Eˣ)
    (Z : Matrix (Fin n) (Fin n) E) (hσ : ∀ a, σ (σ a) = a) (hβ : ∀ a, β (σ a) = β a)
    (hm : ∀ a b, a ≤ b → β a ≤ β b) (hr : ∀ a b, β a = β b → a < b → σ b < σ a)
    (hc : ∀ a b, β a = β b → c a = c b ∨ c a = - c b)
    (hZ : ∀ a b, Z a b = if b = σ a then (c a : E) else 0) :
    (∀ s s' : Matrix (Fin n) (Fin n) E, IsUni s → IsUni s' → cT L s * Z * s' = Z →
      (∀ i j, β i ≠ β j → s i j = 0 ∧ s' i j = 0) ∧ (IsIntM L s ↔ IsIntM L s')) ∧
    ∀ s : Matrix (Fin n) (Fin n) E, IsUni s → (∀ i j, β i ≠ β j → s i j = 0) →
      ∃ s', IsUni s' ∧ cT L s * Z * s' = Z := by
  have hlt : ∀ a b, β a < β b → a < b := fun a b h => by
    by_contra h'
    exact absurd (hm b a (not_lt.1 h')) (not_le.2 h)
  have key : ∀ X Y : Matrix (Fin n) (Fin n) E, IsUni X → IsUni Y → cT L X * Z = Z * Y →
      (∀ i j, β i ≠ β j → X i j = 0 ∧ Y i j = 0) ∧ (IsIntM L X ↔ IsIntM L Y) := by
    intro X Y hX hY h
    rw [mul_mono σ hσ (fun a => (c a : E)) Z hZ] at h
    simp only [cT] at h
    have hz : ∀ i j, β i ≠ β j → X i j = 0 ∧ Y i j = 0 := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with h1 | h1
      · constructor
        · have h2 := h j i
          rw [hY.1 _ _ (hlt _ _ (by rwa [hβ, hβ])), mul_zero, Units.mul_left_eq_zero] at h2
          simpa using h2
        · have h2 := h (σ i) (σ j)
          rw [hX.1 _ _ (hlt _ _ (by rwa [hβ, hβ])), map_zero, zero_mul, hσ, hσ, eq_comm,
            Units.mul_right_eq_zero] at h2
          exact h2
      · exact ⟨hX.1 _ _ (hlt _ _ h1), hY.1 _ _ (hlt _ _ h1)⟩
    have he : ∀ i a, X a i ∈ L.O ↔ Y (σ i) (σ a) ∈ L.O := by
      intro i a
      by_cases hia : β a = β i
      · have h2 := h i a
        rw [← cj_mem_iff L]
        rcases hc a i hia with h3 | h3
        · rw [h3, mul_comm, Units.mul_right_inj] at h2
          rw [h2]
        · rw [h3, Units.val_neg, mul_neg, ← neg_mul, mul_comm, Units.mul_right_inj] at h2
          rw [← h2, neg_mem_iff]
      · rw [(hz a i hia).1, (hz (σ i) (σ a) (by rw [hβ, hβ]; exact Ne.symm hia)).2]
    refine ⟨hz, fun hi p q => ?_, fun hi p q => (he q p).2 (hi _ _)⟩
    have := (he (σ p) (σ q)).1 (hi _ _)
    rwa [hσ, hσ] at this
  refine ⟨fun s s' hs hs' h => ?_, fun s hs hb => ?_⟩
  · obtain ⟨B, b1, b2, b3, b4, -⟩ := inv_facts s hs
    obtain ⟨U, u1, u2, u3, u4, -⟩ := inv_facts s' hs'
    have e1 : cT L s * Z = Z * U := by
      conv_rhs => rw [← h, Matrix.mul_assoc, u1, Matrix.mul_one]
    have e2 : cT L B * Z = Z * s' := by
      conv_lhs => rw [← h, Matrix.mul_assoc, ← Matrix.mul_assoc, cT_mul_eq_one L _ _ b1, Matrix.one_mul]
    obtain ⟨k1, k2⟩ := key s U hs u3 e1
    obtain ⟨k3, k4⟩ := key B s' b3 hs' e2
    exact ⟨fun i j hij => ⟨(k1 i j hij).1, (k3 i j hij).2⟩,
      fun hi => k4.1 (b4 L.O hi), fun hi => k2.2 (u4 L.O hi)⟩
  · let U : Matrix (Fin n) (Fin n) E := fun p q =>
      ((c (σ p))⁻¹ : Eˣ) * (L.cj (s (σ q) (σ p)) * c (σ q))
    have hU : IsUni U := by
      refine ⟨fun p q hpq => ?_, fun p => ?_⟩
      · have : s (σ q) (σ p) = 0 := by
          by_cases h1 : β q = β p
          · exact hs.1 _ _ (hr _ _ h1 hpq)
          · exact hb _ _ (by rwa [hβ, hβ])
        simp [U, this]
      · simp [U, hs.2]
    have e1 : cT L s * Z = Z * U := by
      rw [mul_mono σ hσ (fun a => (c a : E)) Z hZ]
      intro i a
      simp [U, hσ, cT]
    obtain ⟨V, u1, u2, u3, -⟩ := inv_facts U hU
    exact ⟨V, u3, by rw [e1, Matrix.mul_assoc, u1, Matrix.mul_one]⟩

end

theorem stabiliser_blockDiag : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s → IsUni s' → cT L s * S.Zh * s' = S.Zh → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0 ∧ s' i j = 0) ∧ (IsIntM L s ↔ IsIntM L s')) ∧ ∀ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0) → ∃ s', IsUni s' ∧ cT L s * S.Zh * s' = S.Zh := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  obtain ⟨σ, β, t, h⟩ := exists_monomial S.w.blocks
  rw [S.w.size] at h
  let σ' : Fin (r + 1) → Fin (r + 1) := fun a => ⟨σ a, (h a a.2).1⟩
  have hsb : ∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false ↔ β i ≠ β j := fun i j => by
    rw [Ne, ← ((h i i.2).2.2.2 j j.2).1]; simp
  simp only [hsb]
  refine stab_monomial L σ' (fun a => β a) (fun a => t (β a) * (-1) ^ (r - σ a)) S.Zh
    (fun a => Fin.ext (h a a.2).2.1) (fun a => (h a a.2).2.2.1)
    (fun a b hab => ((h a a.2).2.2.2 b b.2).2.1 hab) (fun a b hab hl => ?_) (fun a b hab => ?_)
    (fun a b => ?_)
  · have h1 := ((h a a.2).2.2.2 b b.2).2.2.1 hab
    have h2 : (a : ℕ) < b := hl
    show σ b < σ a
    omega
  · simp only [hab]
    rcases neg_one_pow_eq_or Eˣ (r - σ a) with h1 | h1 <;>
      rcases neg_one_pow_eq_or Eˣ (r - σ b) with h2 | h2 <;> simp [h1, h2]
  · have h1 : S.Zh a b = S.w.mat a b * (-1) ^ (r - (b : ℕ)) := S.relevant a b
    rw [h1, Pt.mat, ((h a a.2).2.2.2 b b.2).2.2.2]
    by_cases h2 : b = σ' a
    · subst h2; simp [σ']
    · have h3 : ¬ (b : ℕ) = σ a := fun h => h2 (Fin.ext h)
      simp [h2, h3]

end GlobalTheory.HL.BlockStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesPairingStabilizerBlockDiagonalStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrames_pairingStabilizer_blockDiagonal : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s → IsUni s' → cT L s * S.Zh * s' = S.Zh → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0 ∧ s' i j = 0) ∧ (IsIntM L s ↔ IsIntM L s')) ∧ ∀ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0) → ∃ s', IsUni s' ∧ cT L s * S.Zh * s' = S.Zh := by
  first | exact @GlobalTheory.HL.BlockStab.stabiliser_blockDiag | exact GlobalTheory.HL.BlockStab.stabiliser_blockDiag | (intros; apply GlobalTheory.HL.BlockStab.stabiliser_blockDiag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabilizerCommensurableUnramifiedHermitia
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisFurther
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc

namespace GlobalTheory.PowMulMemOrder

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_pow_mul_mem (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (c : E) :
    ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) * c ∈ L.O := by
  haveI : Module.Free F E := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have hc : IsIntegral F c := Algebra.IsIntegral.isIntegral c
  obtain ⟨⟨m, hm0⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) c hc
  have hmne : m ≠ 0 := nonZeroDivisors.ne_zero hm0
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hmne hϖ
  obtain ⟨u, hu⟩ := hk
  refine ⟨k, (L.O_def _).2 ?_⟩
  have h2 : IsIntegral 𝒪[F] ((u : 𝒪[F]) • ((⟨m, hm0⟩ : nonZeroDivisors 𝒪[F]) • c)) := hm.smul _
  convert h2 using 1
  simp only [Submonoid.smul_def, smul_smul, ← hu]
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E]
  rw [mul_comm (u : 𝒪[F]) m, hu]
  rfl

theorem main : ∀ {F : Type} [inst : Field F] [inst_1 : ValuativeRel F] [inst_2 : TopologicalSpace F] [IsNonarchimedeanLocalField F] {E : Type} [inst_4 : CommRing E] [inst_5 : Algebra F E] [inst_6 : TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) {ϖ : ↥(Valuation.integer (ValuativeRel.valuation F))}, Irreducible ϖ → ∀ (p : ↥(Formalism.MainNotions.S.Loc.LocE.O L)), (↑p : E) = (Algebra.algebraMap F E : F → E) (↑ϖ : F) → ∀ {n : ℕ} {Λ : Submodule (↥(Formalism.MainNotions.S.Loc.LocE.O L)) (Fin n → E)}, GlobalTheory.HL.IsLat L Λ → ∀ (v : Fin n → E), ∃ (j : ℕ), p ^ j • v ∈ Λ := by
  intro F _ _ _ _ E _ _ _ L ϖ hϖ p hp n Λ hΛ v
  have key : ∀ c : E, ∃ k : ℕ, ((p ^ k : L.O) : E) * c ∈ L.O := by
    intro c
    obtain ⟨k, hk⟩ := exists_pow_mul_mem L hϖ c
    refine ⟨k, ?_⟩
    have : ((p ^ k : L.O) : E) = algebraMap F E ((ϖ : F) ^ k) := by
      rw [SubmonoidClass.coe_pow, hp, map_pow]
    rw [this]; exact hk
  have mono : ∀ (x : Fin n → E) (i j : ℕ), p ^ j • x ∈ Λ → p ^ (i + j) • x ∈ Λ := by
    intro x i j h
    rw [pow_add, mul_smul]
    exact Λ.smul_mem _ h
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ (mono y a b hb)
    rw [add_comm]; exact mono x b a ha
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨k, hk⟩ := key c
    refine ⟨k + a, ?_⟩
    have e1 : p ^ (k + a) • (c • x) = (⟨((p ^ k : L.O) : E) * c, hk⟩ : L.O) • (p ^ a • x) := by
      simp only [Subring.smul_def, smul_smul, pow_add, Subring.coe_mul]
      congr 1
      ring
    rw [e1]
    exact Λ.smul_mem _ ha

end GlobalTheory.PowMulMemOrder
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabilizerCommensurableUnramifiedHermitia
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.LatComm

theorem finite_between {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (c : R)
    [Finite (R ⧸ Ideal.span {c})] (Λ : Submodule R V) (hΛ : Λ.FG) :
    {M : Submodule R V | M ≤ Λ ∧ ∀ v ∈ Λ, c • v ∈ M}.Finite := by
  have hfg : (⊤ : Submodule R Λ).FG := (Submodule.fg_top Λ).2 hΛ
  have hf : Finite (Λ ⧸ (Ideal.span {c}) • (⊤ : Submodule R Λ)) :=
    Submodule.finite_quotient_smul _ hfg
  have hs : Finite (Submodule R (Λ ⧸ (Ideal.span {c}) • (⊤ : Submodule R Λ))) :=
    Finite.of_injective _ SetLike.coe_injective
  have key : ∀ M : Submodule R V, (M ≤ Λ ∧ ∀ v ∈ Λ, c • v ∈ M) →
      (((M.comap Λ.subtype).map ((Ideal.span {c}) • (⊤ : Submodule R Λ)).mkQ).comap
        ((Ideal.span {c}) • (⊤ : Submodule R Λ)).mkQ).map Λ.subtype = M := by
    intro M hM
    have h1 : (Ideal.span {c}) • (⊤ : Submodule R Λ) ≤ M.comap Λ.subtype := by
      rw [Submodule.smul_le]
      intro r hr v _
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [mul_smul]
      exact Submodule.smul_mem _ _ (hM.2 v v.2)
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 h1, Submodule.map_comap_subtype,
      inf_eq_right.2 hM.1]
  refine Set.Finite.of_finite_image (f := fun M : Submodule R V =>
    (M.comap Λ.subtype).map ((Ideal.span {c}) • (⊤ : Submodule R Λ)).mkQ) (Set.toFinite _) ?_
  intro M hM N hN h
  rw [← key M hM, ← key N hN]
  simp only at h
  rw [h]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_pow_smul_mem (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (p : L.O)
    (hp : (p : E) = algebraMap F E (ϖ : F)) {n : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (v : Fin n → E) :
    ∃ j : ℕ, p ^ j • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.PowMulMemOrder.main
  | exact _root_.GlobalTheory.PowMulMemOrder.main
  | (apply _root_.GlobalTheory.PowMulMemOrder.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowMulMemOrder.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowMulMemOrder.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowMulMemOrder.main ..)

theorem exists_pow_smul_le (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (p : L.O)
    (hp : (p : E) = algebraMap F E (ϖ : F)) {n : ℕ}
    {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (hΛ' : Λ'.FG) :
    ∃ j : ℕ, ∀ v ∈ Λ', p ^ j • v ∈ Λ := by
  obtain ⟨s, rfl⟩ := hΛ'
  choose f hf using exists_pow_smul_mem L hϖ p hp hΛ
  refine ⟨s.sup f, fun v hv => ?_⟩
  have : Submodule.span L.O (s : Set (Fin n → E)) ≤
      Λ.comap (LinearMap.lsmul L.O (Fin n → E) (p ^ s.sup f)) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := f) hx)
    show p ^ s.sup f • x ∈ Λ
    rw [hk, pow_add, mul_smul]
    exact Λ.smul_mem _ (hf x)
  exact this hv

theorem stab_commensurable : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Λ Λ' : Submodule L.O (Fin n → E)), IsLat L Λ → IsLat L Λ' → ∀ H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), (H ⊓ stabL L Λ').relIndex (H ⊓ stabL L Λ) ≠ 0 ∧ ∀ g : ((Fin n → E) ≃ₗ[E] (Fin n → E)), IsLat L (g • Λ) ∧ stabL L (g • Λ) = MulAut.conj g • stabL L Λ := by
  intro F _ _ _ _ _ E _ _ _ L n Λ Λ' hΛ hΛ' H
  refine ⟨?_, fun g => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    obtain ⟨-, -, -, -, hO, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
    let p : L.O := ⟨algebraMap F E (ϖ : F), (hO _).2 ϖ.2⟩
    have hp : (p : E) = algebraMap F E (ϖ : F) := rfl
    obtain ⟨a, ha⟩ := exists_pow_smul_le L hϖ p hp hΛ hΛ'.1
    obtain ⟨b, hb⟩ := exists_pow_smul_le L hϖ p hp hΛ' hΛ.1
    have hfin : Finite (L.O ⧸ Ideal.span {p ^ (a + b)}) := by
      have h1 := hcard (a + b)
      have h2 : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ (a + b))} = {p ^ (a + b)} := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Subtype.ext_iff,
          SubmonoidClass.coe_pow, hp, map_pow]
      rw [h2] at h1
      apply Nat.finite_of_card_ne_zero
      rw [h1]
      exact pow_ne_zero _ (by omega)
    have hF := finite_between (p ^ (a + b)) Λ hΛ.1
    have hu : IsUnit ((p ^ a : L.O) : E) := by
      rw [SubmonoidClass.coe_pow, hp]
      exact ((IsUnit.mk0 _ (fun h => hϖ.ne_zero (Subtype.ext h))).map (algebraMap F E)).pow a
    have hinj : Function.Injective (LinearMap.lsmul L.O (Fin n → E) (p ^ a)) := by
      intro x y h
      exact hu.smul_left_cancel.1 h
    have hcomm : ∀ (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (r : L.O) (v : Fin n → E),
        g • (r • v) = r • (g • v) := fun g r v => map_smul g (r : E) v
    have heq : (H ⊓ stabL L Λ').subgroupOf (H ⊓ stabL L Λ) =
        MulAction.stabilizer (H ⊓ stabL L Λ :) Λ' := by
      ext g
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      exact ⟨fun h => h.2, fun h => ⟨g.2.1, h⟩⟩
    rw [Subgroup.relIndex, heq, MulAction.index_stabilizer]
    refine Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self Λ') ?_
    refine Set.Finite.of_finite_image
      (f := fun M => Submodule.map (LinearMap.lsmul L.O (Fin n → E) (p ^ a)) M) (hF.subset ?_)
      (Submodule.map_injective_of_injective hinj).injOn
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have hg : g.1 • Λ = Λ := g.2.2
    refine ⟨?_, fun v hv => ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists w g.1 Λ').1 hw
      show p ^ a • (g.1 • x) ∈ Λ
      rw [← hcomm]
      exact hg.le (Submodule.smul_mem_pointwise_smul _ _ _ (ha x hx))
    · rw [← hg] at hv
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v g.1 Λ).1 hv
      refine ⟨g.1 • (p ^ b • x), Submodule.smul_mem_pointwise_smul _ g.1 _ (hb x hx), ?_⟩
      rw [LinearMap.lsmul_apply, hcomm, pow_add, mul_smul]
  · exact hΛ.1.map _
  · rw [eq_top_iff]
    intro v _
    have hv : g.symm v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span (g : (Fin n → E) →ₗ[E] (Fin n → E)) hv
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.smul_mem_pointwise_smul _ g _ hx
  · exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g Λ

end GlobalTheory.LatComm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabilizerCommensurableUnramifiedHermitiaStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Λ Λ' : Submodule L.O (Fin n → E)), IsLat L Λ → IsLat L Λ' → ∀ H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), (H ⊓ stabL L Λ').relIndex (H ⊓ stabL L Λ) ≠ 0 ∧ ∀ g : ((Fin n → E) ≃ₗ[E] (Fin n → E)), IsLat L (g • Λ) ∧ stabL L (g • Λ) = MulAut.conj g • stabL L Λ := by
  first | exact @GlobalTheory.LatComm.stab_commensurable | exact GlobalTheory.LatComm.stab_commensurable | (intros; apply GlobalTheory.LatComm.stab_commensurable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEqPowAndIndexGe
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FiniteModuleOrder

theorem exists_card_eq_pow (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) :
    ∀ (D : Type) [AddCommGroup D] [Module R D] [Finite D], Nat.card D = n →
      ∃ i : ℕ, Nat.card D = Nat.card (R ⧸ IsLocalRing.maximalIdeal R) ^ i := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D _ _ _ hn
    rcases subsingleton_or_nontrivial D with h | h
    · exact ⟨0, by simp⟩
    have hfin : Finite (Submodule R D) := Finite.of_injective _ SetLike.coe_injective
    obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule R D)).resolve_left bot_ne_top
    have hs : IsSimpleModule R (D ⧸ M) := isSimpleModule_iff_isCoatom.2 hM
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
    have hI' : I = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hI
    subst hI'
    have hc := Submodule.card_eq_card_quotient_mul_card M
    have hnt : Nontrivial (D ⧸ M) := IsSimpleModule.nontrivial R _
    have hf : Finite (D ⧸ M) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective M)
    have h2 : 1 < Nat.card (D ⧸ M) := Finite.one_lt_card
    have hpos : 0 < Nat.card M := Nat.card_pos
    obtain ⟨i, hi⟩ := ih (Nat.card M) (by rw [← hn, hc]; nlinarith) M rfl
    exact ⟨i + 1, by rw [hc, hi, Nat.card_congr e.toEquiv, pow_succ]⟩

theorem card_eq_pow_and_index_ge : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D], (∃ i : ℕ, Nat.card D = resQ ϖ ^ i) ∧ ∀ I : Submodule L.O D, I ≠ ⊤ → resQ ϖ * Nat.card I ≤ Nat.card D := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a =>
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 a.2
  let i : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hint
  have key : ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D],
      ∃ i : ℕ, Nat.card D = resQ ϖ ^ i := by
    intro D _ _ _
    let : Module 𝒪[F] D := Module.compHom D i
    rw [resQ, ← hϖ.maximalIdeal_eq]
    exact exists_card_eq_pow 𝒪[F] _ D rfl
  intro D _ _ _
  refine ⟨key D, fun I hI => ?_⟩
  have hnt : Nontrivial (D ⧸ I) := Submodule.Quotient.nontrivial_iff.2 hI
  have hf : Finite (D ⧸ I) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective I)
  have h2 : 1 < Nat.card (D ⧸ I) := Finite.one_lt_card
  obtain ⟨j, hj⟩ := key (D ⧸ I)
  have hj0 : j ≠ 0 := by rintro rfl; rw [pow_zero] at hj; omega
  rw [Submodule.card_eq_card_quotient_mul_card I, hj, mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.le_self_pow hj0 _)

end GlobalTheory.FiniteModuleOrder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarInvVolumeConjModularCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarInvVolumeConjModularCharacter
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem invVol_conj_modular : ∀ {G : Type} [Group G] (H K : Subgroup G), K ≤ H → (∀ h ∈ H, K.relIndex (MulAut.conj h • K) ≠ 0 ∧ (MulAut.conj h • K).relIndex K ≠ 0) → (∀ a ∈ H, ∀ b ∈ H, invVol K (MulAut.conj (a * b) • K) = invVol K (MulAut.conj a • K) * invVol K (MulAut.conj b • K)) ∧ (∀ a ∈ H, 0 < invVol K (MulAut.conj a • K)) ∧ (∀ α : G ≃* G, K.map α.toMonoidHom = K → ∀ a ∈ H, invVol K (MulAut.conj (α a) • K) = invVol K (MulAut.conj a • K)) ∧ ∀ K' : Subgroup G, K.relIndex K' ≠ 0 → K'.relIndex K ≠ 0 → ∀ a ∈ H, invVol K (MulAut.conj a • K') = invVol K (MulAut.conj a • K) * invVol K K' ∧ (MulAut.conj a • K' = K' → invVol K (MulAut.conj a • K) = 1) := by
  intro G _ H K _ hc
  have e : ∀ (g : G) (A B : Subgroup G),
      (MulAut.conj g • A).relIndex (MulAut.conj g • B) = A.relIndex B := fun g A B =>
    Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) A B
      (MulAut.conj g).injective
  have key : ∀ K' : Subgroup G, K.relIndex K' ≠ 0 → K'.relIndex K ≠ 0 → ∀ a ∈ H,
      invVol K (MulAut.conj a • K') = invVol K (MulAut.conj a • K) * invVol K K' := by
    intro K' h1 h2 a ha
    have p1 : K.relIndex (MulAut.conj a • K') ≠ 0 :=
      Subgroup.relIndex_ne_zero_trans (hc a ha).1 (by rw [e]; exact h1)
    have p2 : (MulAut.conj a • K').relIndex K ≠ 0 :=
      Subgroup.relIndex_ne_zero_trans (by rw [e]; exact h2) (hc a ha).2
    rw [(invVol_mul_pos_le_conj K (MulAut.conj a • K) _ (hc a ha).1 (hc a ha).2 p1 p2).1,
      (invVol_mul_pos_le_conj K K' K' h1 h2 h1 h2).2.2.2 a]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    rw [map_mul, mul_smul]
    exact key _ (hc b hb).1 (hc b hb).2 a ha
  · intro a ha
    exact (invVol_mul_pos_le_conj K _ _ (hc a ha).1 (hc a ha).2 (hc a ha).1 (hc a ha).2).2.1
  · intro α hα a _
    have h1 : (MulAut.conj a • K).map α.toMonoidHom
        = MulAut.conj (α a) • K.map α.toMonoidHom := by
      change (K.map (MulAut.conj a).toMonoidHom).map α.toMonoidHom
        = (K.map α.toMonoidHom).map (MulAut.conj (α a)).toMonoidHom
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp
    rw [hα] at h1
    have f : ∀ A B : Subgroup G,
        (A.map α.toMonoidHom).relIndex (B.map α.toMonoidHom) = A.relIndex B := fun A B =>
      Subgroup.relIndex_map_map_of_injective (f := α.toMonoidHom) A B α.injective
    have f1 := f K (MulAut.conj a • K)
    have f2 := f (MulAut.conj a • K) K
    rw [hα, h1] at f1 f2
    rw [invVol, invVol, f1, f2]
  · intro K' h1 h2 a ha
    refine ⟨key K' h1 h2 a ha, fun h => ?_⟩
    have k := key K' h1 h2 a ha
    rw [h] at k
    have pos := (invVol_mul_pos_le_conj K K' K' h1 h2 h1 h2).2.1
    exact mul_right_cancel₀ pos.ne' (by rw [← k, one_mul])

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarInvVolumeConjModularCharacterStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarInvVolume_conj_modular_character : ∀ {G : Type} [Group G] (H K : Subgroup G), K ≤ H → (∀ h ∈ H, K.relIndex (MulAut.conj h • K) ≠ 0 ∧ (MulAut.conj h • K).relIndex K ≠ 0) → (∀ a ∈ H, ∀ b ∈ H, invVol K (MulAut.conj (a * b) • K) = invVol K (MulAut.conj a • K) * invVol K (MulAut.conj b • K)) ∧ (∀ a ∈ H, 0 < invVol K (MulAut.conj a • K)) ∧ (∀ α : G ≃* G, K.map α.toMonoidHom = K → ∀ a ∈ H, invVol K (MulAut.conj (α a) • K) = invVol K (MulAut.conj a • K)) ∧ ∀ K' : Subgroup G, K.relIndex K' ≠ 0 → K'.relIndex K ≠ 0 → ∀ a ∈ H, invVol K (MulAut.conj a • K') = invVol K (MulAut.conj a • K) * invVol K K' ∧ (MulAut.conj a • K' = K' → invVol K (MulAut.conj a • K) = 1) := by
  first | exact @GlobalTheory.HL.invVol_conj_modular | exact GlobalTheory.HL.invVol_conj_modular | (intros; apply GlobalTheory.HL.invVol_conj_modular <;> assumption)
end
end
