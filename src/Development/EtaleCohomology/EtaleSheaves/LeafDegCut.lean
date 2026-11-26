module

public import Development.EtaleCohomology.EtaleSheaves.PartDiagCut
public import Development.EtaleCohomology.EtaleSheaves.TwistTensorRestriction

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafDegCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafDegCut
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves

def Cov {B : Scheme.{0}} (U : B.Etale) (P : ∀ U' : B.Etale, (U' ⟶ U) → Prop) : Prop :=
  ∃ S ∈ (EtTop B) U, ∀ (U' : B.Etale) (a : U' ⟶ U), S a → P U' a

theorem Cov.mono {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P)
    (hPQ : ∀ U' a, P U' a → Q U' a) : Cov U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun U' a ha => hPQ U' a (hP U' a ha)⟩

theorem Cov.and {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P) (h' : Cov U Q) :
    Cov U (fun U' a => P U' a ∧ Q U' a) := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨S', hS', hQ⟩ := h'
  exact ⟨S ⊓ S', (EtTop B).intersection_covering hS hS', fun U' a ha => ⟨hP U' a ha.1, hQ U' a ha.2⟩⟩

theorem Cov.all {B : Scheme.{0}} {U : B.Etale} {P : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : ∀ U' a, P U' a) : Cov U P :=
  ⟨⊤, (EtTop B).top_mem U, fun U' a _ => h U' a⟩

def SHV (q : ℕ) (i : ℤ) {B Y0 Y1 Y2 : Scheme.{0}} (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) : Prop :=
  ∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)

abbrev rY (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) (m : ℤ) :=
  rpl q i (prU p ι U) (prU p ι U') (resYW p ι a) (resY p a) (pullback.lift_fst _ _ _).symm m

abbrev rB (q : ℕ) (i : ℤ) {B W : Scheme.{0}} (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) (m : ℤ) :=
  rpl q i (prB ι U) (prB ι U') (resBW ι a) a.left (pullback.lift_fst _ _ _).symm m

abbrev gY (q : ℕ) (i : ℤ) {B W Y Y' : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (ι : W ⟶ B) (U : B.Etale) (m : ℤ) :=
  rpl q i (prU p ι U) (prU (g ≫ p) ι U) (mW p g ι U) (mY p g U) (pullback.lift_fst _ _ _).symm m

abbrev bY (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (m : ℤ) :=
  rpl q i (prB ι U) (prU p ι U) (toBW p ι U) (toBY p U) (pullback.lift_fst _ _ _).symm m

def LeafNeg : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (m : ℤ), m < 0 →
  Subsingleton (Hrel R f F m)

def LeafShMapZero : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (K K' : DerivedCategory (SShv B q)) (f : K ⟶ K') (m : ℤ),
  (∀ (U : B.Etale) (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K),
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map f = 0)) →
  (DerivedCategory.homologyFunctor (SShv B q) m).map f = 0

def LeafShIso : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (L K : DerivedCategory (SShv B q)) (ℓ : L ⟶ K) (m : ℤ),
  (∀ (U : B.Etale) (x x' : (OU B q).obj U ⟶ (shiftFunctor _ m).obj L),
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map ℓ = (OU B q).map a ≫ x' ≫ (shiftFunctor _ m).map ℓ) →
    Cov U (fun U' a => (OU B q).map a ≫ x = (OU B q).map a ≫ x')) →
  (∀ (U : B.Etale) (y : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K),
    Cov U (fun U' a => ∃ x : (OU B q).obj U' ⟶ (shiftFunctor _ m).obj L, (OU B q).map a ≫ y = x ≫ (shiftFunctor _ m).map ℓ)) →
  IsIso ((DerivedCategory.homologyFunctor (SShv B q) m).map ℓ)

def LeafVan0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ (m : ℤ), 2 < m → ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m,
  Cov U (fun U' a => rY q i p ι a m y = 0)

def LeafKill2 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) 2,
  Cov U (fun U' a => rY q i (g1 ≫ p) ι a 2 (gY q i p g1 ι U 2 y) = 0)

def LeafKill1 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g1 ≫ p) ι U)) (tw q i) 1,
  Cov U (fun U' a => rY q i (g2 ≫ g1 ≫ p) ι a 1 (gY q i (g1 ≫ p) g2 ι U 1 y) = 0)

def LeafVanB : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ (m : ℤ), 0 < m → ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m,
  Cov U (fun U' a => rB q i ι a m c = 0)

def LeafInj0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0,
  Cov U (fun U' a => rY q i (g2 ≫ g1 ≫ p) ι a 0 (bY q i (g2 ≫ g1 ≫ p) ι U 0 c) = 0) →
  Cov U (fun U' a => rB q i ι a 0 c = 0)

def LeafSurj0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0,
  Cov U (fun U' a => ∃ c : Hrel (ZMod q) (sch.map (prB ι U')) (tw q i) 0,
    bY q i (g2 ≫ g1 ≫ p) ι U' 0 c = rY q i (g2 ≫ g1 ≫ p) ι a 0 y)

theorem loc_zero_map {B : Scheme.{0}} {q : ℕ} {K K' : DerivedCategory (SShv B q)} (f : K ⟶ K') {m : ℤ}
    (X X' : B.Etale → Type 1) [∀ U, Zero (X' U)]
    (e : ∀ U, X U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K))
    (e' : ∀ U, X' U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K'))
    (hb : ∀ U, Function.Surjective (e U))
    (res' : ∀ U U', (U' ⟶ U) → X' U → X' U') (φ : ∀ U, X U → X' U)
    (hnat : ∀ U U' (a : U' ⟶ U) y, e' U' (res' U U' a y) = (OU B q).map a ≫ e' U y)
    (hf : ∀ U y, e' U (φ U y) = e U y ≫ (shiftFunctor _ m).map f)
    (hv : ∀ U y, Cov U (fun U' a => res' U U' a (φ U y) = 0)) (U : B.Etale)
    (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K) :
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map f = 0) := by
  obtain ⟨y, rfl⟩ := hb U x
  obtain ⟨y0, hy0⟩ := hb U 0
  refine (Cov.and (hv U y) (hv U y0)).mono fun U' a ⟨h1, h2⟩ => ?_
  rw [← hf, ← hnat, h1, ← h2, hnat, hf, hy0, zero_comp, comp_zero]

theorem loc_zero {B : Scheme.{0}} {q : ℕ} {K : DerivedCategory (SShv B q)} {m : ℤ}
    (X : B.Etale → Type 1) [∀ U, Zero (X U)]
    (e : ∀ U, X U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K)) (hb : ∀ U, Function.Surjective (e U))
    (res : ∀ U U', (U' ⟶ U) → X U → X U')
    (hnat : ∀ U U' (a : U' ⟶ U) y, e U' (res U U' a y) = (OU B q).map a ≫ e U y)
    (hv : ∀ U y, Cov U (fun U' a => res U U' a y = 0)) (U : B.Etale)
    (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K) :
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map (𝟙 K) = 0) :=
  loc_zero_map (𝟙 K) X X e e hb res (fun _ y => y) hnat (fun U y => by simp) hv U x

theorem isZero_of (hZ : LeafShMapZero) {B : Scheme.{0}} {q : ℕ} (K : DerivedCategory (SShv B q)) (m : ℤ)
    (h : ∀ (U : B.Etale) (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K),
      Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map (𝟙 K) = 0)) :
    IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj K) := by
  rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id]
  exact hZ B q K K (𝟙 K) m h

theorem isZero_neg (hZ : LeafShMapZero) {B : Scheme.{0}} {q : ℕ} (K : DerivedCategory (SShv B q)) (m : ℤ)
    (X : B.Etale → Type 1) (hs : ∀ U, Subsingleton (X U))
    (e : ∀ U, X U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K)) (hb : ∀ U, Function.Surjective (e U)) :
    IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj K) := by
  refine isZero_of hZ K m fun U x => Cov.all fun U' a => ?_
  obtain ⟨y, rfl⟩ := hb U x
  obtain ⟨y0, hy0⟩ := hb U 0
  rw [Subsingleton.elim y y0, hy0]
  simp

theorem goal_of (hN : LeafNeg) (hZ : LeafShMapZero) (hI : LeafShIso) (hV0 : LeafVan0) (hK2 : LeafKill2)
    (hK1 : LeafKill1) (hVB : LeafVanB) (hIn : LeafInj0) (hSu : LeafSurj0) : LateralTheory.E.EtaleTopologySheaves.LeafDeg := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA K0 K1 K2 L f g ℓ l0 l1 l2 lL r0 r1 r2 rL mf mg mℓ
  have hS : SHV q i V p g1 g2 := hA
  refine ⟨fun m hm => ?_, ?_, ?_, fun m hm => ?_, fun m hm => ?_, ?_⟩
  · exact isZero_of hZ K0 m (loc_zero _ (l0 · m) (fun U => (r0.1 U m).2) (fun U U' a => rY q i p ι a m)
      (fun U U' a y => r0.2 U U' a m y) (fun U y => hV0 hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U m hm y))
  · exact hZ B q K0 K1 f 2 (loc_zero_map f _ _ (l0 · 2) (l1 · 2) (fun U => (r0.1 U 2).2)
      (fun U U' a => rY q i (g1 ≫ p) ι a 2) (fun U => gY q i p g1 ι U 2)
      (fun U U' a y => r1.2 U U' a 2 y) (fun U y => mf U 2 y)
      (fun U y => hK2 hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U y))
  · exact hZ B q K1 K2 g 1 (loc_zero_map g _ _ (l1 · 1) (l2 · 1) (fun U => (r1.1 U 1).2)
      (fun U U' a => rY q i (g2 ≫ g1 ≫ p) ι a 1) (fun U => gY q i (g1 ≫ p) g2 ι U 1)
      (fun U U' a y => r2.2 U U' a 1 y) (fun U y => mg U 1 y)
      (fun U y => hK1 hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U y))
  · exact isZero_neg hZ K2 m _ (fun U => hN _ _ _ m hm) (l2 · m) (fun U => (r2.1 U m).2)
  · rcases lt_or_gt_of_ne hm with hm | hm
    · exact isZero_neg hZ L m _ (fun U => hN _ _ _ m hm) (lL · m) (fun U => (rL.1 U m).2)
    · exact isZero_of hZ L m (loc_zero _ (lL · m) (fun U => (rL.1 U m).2) (fun U U' a => rB q i ι a m)
        (fun U U' a c => rL.2 U U' a m c) (fun U c => hVB hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U m hm c))
  · refine hI B q L K2 ℓ 0 (fun U x x' hx => ?_) (fun U y => ?_)
    · obtain ⟨c, rfl⟩ := (rL.1 U 0).2 x
      obtain ⟨c', rfl⟩ := (rL.1 U 0).2 x'
      have hd := hIn hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U (c - c') (hx.mono fun U' a h => by
        rw [← mℓ U 0 c, ← mℓ U 0 c', ← r2.2 U U' a 0, ← r2.2 U U' a 0] at h
        rw [map_sub, map_sub, (r2.1 U' 0).1 h, sub_self])
      refine hd.mono fun U' a h => ?_
      rw [← rL.2 U U' a 0 c, ← rL.2 U U' a 0 c', sub_eq_zero.1 ((map_sub _ c c').symm.trans h)]
    · obtain ⟨z, rfl⟩ := (r2.1 U 0).2 y
      refine (hSu hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U z).mono fun U' a ⟨c, hc⟩ => ⟨lL U' 0 c, ?_⟩
      rw [← r2.2 U U' a 0 z, ← hc, mℓ U' 0 c]

end LateralTheory.E.LeafDegCut
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafDescendVCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafDescendVCut

abbrev toR {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) : Sp Ω ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom (algebraMap R Ω))

abbrev incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R') : Sp R' ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)

def Chain {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) {C0 C1 C2 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0)
    (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2) : Prop :=
  IsProper q ∧ SmoothOfRelativeDimension 1 q ∧ IsProper (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
  IsProper (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
  IsPullback v0 c0 q (toR R) ∧ IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (toR R) ∧
  IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (toR R) ∧ γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2

def LeafDescendChain : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {C0 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω), IsCurve c0 → ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1),
    IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2), Chain R c0 γ1 γ2 q d1 d2 v0 v1 v2

def LeafDescendMap : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG → ∀ {C0 D0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (q : D0 ⟶ Sp R)
    (v0 : C0 ⟶ D0), IsProper q → IsPullback v0 c0 q (toR R) → ∀ (e : C0 ⟶ X),
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
    ∃ (R' : Subalgebra k Ω) (hR : R ≤ R'), R'.FG ∧ ∀ (E0 : Scheme.{0}) (q' : E0 ⟶ Sp R') (r : E0 ⟶ D0)
      (w0 : C0 ⟶ E0), IsPullback r q' q (incl hR) → IsPullback w0 c0 q' (toR R') → w0 ≫ r = v0 →
      ∃ f : E0 ⟶ X, w0 ≫ f = e ∧ f ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k R'))

def LeafBaseChange : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R R' : Subalgebra k Ω)
    (hR : R ≤ R') {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
    Chain R c0 γ1 γ2 q d1 d2 v0 v1 v2 →
    ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1)
      (w2 : C2 ⟶ E2) (r : E0 ⟶ D0), Chain R' c0 γ1 γ2 q' e1 e2 w0 w1 w2 ∧ IsPullback r q' q (incl hR) ∧
      w0 ≫ r = v0

def LeafIrred : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 D0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (q : D0 ⟶ Sp R) (v0 : C0 ⟶ D0), IsCurve c0 →
    SmoothOfRelativeDimension 1 q → IsPullback v0 c0 q (toR R) → IrreducibleSpace D0

def LeafDimBound : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {D0 : Scheme.{0}} (q : D0 ⟶ Sp R), SmoothOfRelativeDimension 1 q →
    topologicalKrullDim D0 ≤ ringKrullDim R + 1

theorem goal_of (hA : LeafDescendChain) (hB : LeafDescendMap) (hC : LeafBaseChange) (hI : LeafIrred)
    (hD : LeafDimBound) : LateralTheory.E.LeafSpreadVCut.LeafDescendV := by
  intro k _ X p _ Ω _ _ C0 c0 e hc0 he C1 C2 γ1 γ2 h1 h2
  obtain ⟨R, hR, D0, D1, D2, q, d1, d2, v0, v1, v2, hch⟩ := hA k Ω c0 hc0 C1 C2 γ1 γ2 h1 h2
  obtain ⟨R', hRR', hR', hM⟩ := hB k p Ω R hR c0 q v0 hch.1 hch.2.2.2.2.2.2.1 e he
  obtain ⟨E0, E1, E2, q', e1, e2, w0, w1, w2, r, hch', hr, hw⟩ :=
    hC k Ω R R' hRR' c0 γ1 γ2 q d1 d2 v0 v1 v2 hch
  obtain ⟨f, hf1, hf2⟩ := hM E0 q' r w0 hr hch'.2.2.2.2.2.2.1 hw
  obtain ⟨pq, sq, pq1, sq1, pq2, sq2, P0, P1, P2, c1, c2⟩ := hch'
  exact ⟨R', hR', E0, E1, E2, q', e1, e2, f, w0, w1, w2, pq, sq, pq1, sq1, pq2, sq2, hf2,
    hI k Ω R' hR' c0 q' w0 hc0 sq P0, hD k Ω R' hR' q' sq, P0, P1, P2, c1, c2, hf1⟩

end LateralTheory.E.LeafDescendVCut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.FiltPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.TruncationPieces

namespace LateralTheory.E.FiltPf

namespace Tri

open Pretriangulated
universe u v

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (CategoryTheory.shiftFunctor D n)] [Pretriangulated D]

def RelY (Y : ℤ → D) (n : ℤ) {A B : D} (g : A ⟶ B) : Prop :=
  Function.Surjective (fun x : B ⟶ Y (n - 1) => g ≫ x) ∧ Function.Injective (fun x : B ⟶ Y n => g ≫ x)

omit [HasZeroObject D] [HasShift D ℤ] [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D] in
theorem inj_iff {A B X : D} (g : A ⟶ B) :
    Function.Injective (fun x : B ⟶ X => g ≫ x) ↔ ∀ x : B ⟶ X, g ≫ x = 0 → x = 0 := by
  constructor
  · intro h x hx; exact h (by simpa using hx)
  · intro h x y hxy
    have := h (x - y) (by simp only [Preadditive.comp_sub]; exact sub_eq_zero.2 hxy)
    exact sub_eq_zero.1 this

theorem relY_mid (T₁ T₂ : Triangle D) (h₁ : T₁ ∈ distTriang D) (h₂ : T₂ ∈ distTriang D) (φ : T₁ ⟶ T₂)
    (Y : ℤ → D) (e : ∀ n, Y n ≅ (Y (n - 1))⟦(1 : ℤ)⟧) (n : ℤ)
    (ha : RelY Y n φ.hom₁) (hc : RelY Y n φ.hom₃) : RelY Y n φ.hom₂ := by
  have hci := (inj_iff _).1 hc.2
  have hai := (inj_iff _).1 ha.2
  refine ⟨fun x => ?_, (inj_iff _).2 fun d hd => ?_⟩
  · obtain ⟨y, hy⟩ := ha.1 (T₁.mor₁ ≫ x)
    simp only at hy
    have ho : T₂.mor₃ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map y ≫ (e n).inv = 0 := by
      apply hci
      rw [← Category.assoc, ← φ.comm₃, Category.assoc, ← Functor.map_comp_assoc, hy, Functor.map_comp_assoc,
        ← Category.assoc, comp_distTriang_mor_zero₃₁ T₁ h₁, zero_comp]
    have ho' : T₂.rotate.mor₂ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map y = 0 := by
      have := congrArg (· ≫ (e n).hom) ho
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] at this
      exact this
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ h₂) _ ho'
    obtain ⟨(z : T₂.obj₂ ⟶ Y (n - 1)), rfl⟩ := (CategoryTheory.shiftFunctor D (1 : ℤ)).map_surjective g
    have hyz : y = T₂.mor₁ ≫ (-z) := by
      apply (CategoryTheory.shiftFunctor D (1 : ℤ)).map_injective
      rw [hg]
      simp only [Triangle.rotate_mor₃, Functor.map_comp, Functor.map_neg, Preadditive.comp_neg]
      exact Preadditive.neg_comp _ _
    have hw : T₁.mor₁ ≫ (x - φ.hom₂ ≫ (-z)) = 0 := by
      rw [Preadditive.comp_sub, ← hy, hyz, ← Category.assoc, ← φ.comm₁, Category.assoc, sub_self]
    obtain ⟨w, hw⟩ := Triangle.yoneda_exact₂ _ h₁ _ hw
    obtain ⟨w', hw'⟩ := hc.1 w
    simp only at hw'
    refine ⟨-z + T₂.mor₂ ≫ w', ?_⟩
    simp only
    rw [Preadditive.comp_add, ← Category.assoc, ← φ.comm₂, Category.assoc, hw', ← hw]
    abel
  · have h1 : T₂.mor₁ ≫ d = 0 := by
      apply hai
      rw [← Category.assoc, ← φ.comm₁, Category.assoc, hd, comp_zero]
    obtain ⟨h, rfl⟩ := Triangle.yoneda_exact₂ _ h₂ _ h1
    have h3 : T₁.mor₂ ≫ φ.hom₃ ≫ h = 0 := by
      rw [← Category.assoc, φ.comm₂, Category.assoc, hd]
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ _ h₁ _ h3
    obtain ⟨k', hk'⟩ := (CategoryTheory.shiftFunctor D (1 : ℤ)).map_surjective (k ≫ (e n).hom)
    obtain ⟨k'', hk''⟩ := ha.1 k'
    simp only at hk''
    have hm : h = T₂.mor₃ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map k'' ≫ (e n).inv := by
      rw [← sub_eq_zero]
      apply hci
      rw [Preadditive.comp_sub, hk, ← Category.assoc φ.hom₃, ← φ.comm₃, Category.assoc, ← Functor.map_comp_assoc,
        hk'', hk', Category.assoc, Iso.hom_inv_id, Category.comp_id, sub_self]
    rw [hm, ← Category.assoc, comp_distTriang_mor_zero₂₃ _ h₂, zero_comp]

end Tri

section Bridge
open CochainComplex CochainComplex.HomComplex
variable (R : Type) [CommRing R]

abbrev Yres (F : Shv R) (m : ℤ) : HomotopyCategory (Shv R) (ComplexShape.up ℤ) :=
  (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦m⟧)

theorem pull_eq_comp {K L : Cx R} (f : K ⟶ L) (F : Shv R) (m : ℤ) :
    (fun g : (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj L ⟶ Yres R F m =>
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map f ≫ g) =
      (CohomologyClass.homAddEquiv) ∘ (HK.pull R f F m) ∘ (CohomologyClass.homAddEquiv.symm) := by
  funext g
  simp only [Function.comp_apply, CohomologyClass.homAddEquiv_apply, LateralTheory.E.E8.ExciseCut.ConeZeroPf.pull_toHom]
  congr 1
  exact (CohomologyClass.homAddEquiv.apply_symm_apply g).symm

theorem relK_iff {K L : Cx R} (f : K ⟶ L) (F : Shv R) (n : ℤ) :
    RelK R F n f ↔ Tri.RelY (Yres R F) n ((HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map f) := by
  unfold Tri.RelY RelK
  rw [pull_eq_comp, pull_eq_comp, EquivLike.comp_surjective, EquivLike.surjective_comp,
    EquivLike.comp_injective, EquivLike.injective_comp]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1 (n - 1) (by omega), h2⟩
  · rintro ⟨h1, h2⟩; refine ⟨fun m hm => ?_, h2⟩; obtain rfl : m = n - 1 := (by omega)
    exact h1

def yresIso (F : Shv R) (m : ℤ) : Yres R F m ≅ (Yres R F (m - 1))⟦(1 : ℤ)⟧ :=
  LateralTheory.E.E8.ExciseCut.ConeZeroPf.shIso R (res R F) m

end Bridge

def pieceC (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (p : ℕ) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (K.X (-(p : ℤ))) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (L.X (-(p : ℤ))) :=
  (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (f.f (-(p : ℤ)))

def Tower : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K L : Cx R} (f : K ⟶ L) (n : ℤ),
  (∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)) →
  (∀ p : ℕ, RelK R F n (pieceC R f p)) → RelK R F n f

def TowerFin : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K L : Cx R} (f : K ⟶ L) (n : ℤ) (P : ℕ),
  (∀ i : ℤ, (0 < i ∨ i < -(P : ℤ)) → IsZero (K.X i) ∧ IsZero (L.X i)) →
  (∀ p : ℕ, RelK R F n (pieceC R f p)) → RelK R F n f

def Trunc : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K L : Cx R} (f : K ⟶ L) (n : ℤ),
  (∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)) →
  ∃ (P : ℕ) (K' L' : Cx R) (f' : K' ⟶ L'),
    (∀ i : ℤ, (0 < i ∨ i < -(P : ℤ)) → IsZero (K'.X i) ∧ IsZero (L'.X i)) ∧
    ((∀ p : ℕ, RelK R F n (pieceC R f p)) → ∀ p : ℕ, RelK R F n (pieceC R f' p)) ∧
    (RelK R F n f' → RelK R F n f)

theorem tower_of (hB : TowerFin) (hT : Trunc) : Tower := by
  intro R _ F K L f n hz hp
  obtain ⟨P, K', L', f', hz', hpp, hback⟩ := hT R F f n hz
  exact hback (hB R F f' n P hz' (hpp hp))

theorem chains_X_isZero (R : Type) [CommRing R] (U : Spc) (i : ℤ) (hi : 0 < i) : IsZero (((chains R).obj U).X i) := by
  change IsZero ((((chainsN R).obj U).extend ComplexShape.embeddingDownNat).X i)
  apply HomologicalComplex.isZero_extend_X
  intro j hj
  have e : ComplexShape.embeddingDownNat.f j = -(j : ℤ) := rfl
  omega

end LateralTheory.E.FiltPf

open LateralTheory.E.FiltPf in
theorem LateralTheory.E.TruncationPieces.Filt_of_tower (hT : Tower) : LateralTheory.E.TruncationPieces.Filt := by
  intro R _ F U E u n h
  exact hT R F ((chains R).map u) n (fun i hi => ⟨chains_X_isZero R U i hi, chains_X_isZero R E i hi⟩) h
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafModelCurveCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafModelCurveCut

def ExistsNormalProperCurveModel : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    ∃ (C0 : Scheme.{0}) (c0 : C0 ⟶ Sp Ω) (x : C0) (ψ : Spec (C0.presheaf.stalk x) ⟶ Sp L),
      IsIntegral C0 ∧ IsProper c0 ∧ (∀ y : C0, IsIntegrallyClosed (C0.presheaf.stalk y)) ∧
      topologicalKrullDim C0 = 1 ∧ IsGenericPoint x (⊤ : Set C0) ∧
      ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = C0.fromSpecStalk x ≫ c0

def LeafSmoothOfNormal : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω),
  IsIntegral C → LocallyOfFiniteType c → (∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y)) →
    topologicalKrullDim C = 1 → SmoothOfRelativeDimension 1 c

theorem goal_of (hN : ExistsNormalProperCurveModel) (hS : LeafSmoothOfNormal) : LateralTheory.E.LeafCurveVCut.LeafModelCurve := by
  intro Ω L _ _ _ _ u hu hfin
  obtain ⟨C0, c0, x, ψ, hint, hprop, hnorm, hdim, hx, hψ⟩ := hN Ω L u hu hfin
  refine ⟨C0, c0, x, ψ, ⟨hint, hprop, ?_⟩, hx, hψ⟩
  have := hprop
  exact hS Ω c0 hint inferInstance hnorm hdim

end LateralTheory.E.LeafModelCurveCut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafExtendCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafExtendCut

def LeafStalkValuation : Prop := ∀ (Ω : Type) [Field Ω] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp Ω) (x y : C)
  (hx : IsGenericPoint x (⊤ : Set C)), IsCurve c → y ≠ x →
    ValuationRing (C.presheaf.stalk y) ∧
      (letI := (C.presheaf.stalkSpecializes (hx.specializes (Set.mem_univ y))).hom.toAlgebra
       IsFractionRing (C.presheaf.stalk y) (C.presheaf.stalk x))

def LeafLocalExtend : Prop := ∀ {C X S : Scheme.{0}} [IsIntegral C] (sC : C ⟶ S) (p : X ⟶ S) [IsProper p] (x y : C),
  IsGenericPoint x (⊤ : Set C) → ∀ (h : x ⤳ y), ValuationRing (C.presheaf.stalk y) →
    (letI := (C.presheaf.stalkSpecializes h).hom.toAlgebra
     IsFractionRing (C.presheaf.stalk y) (C.presheaf.stalk x)) →
    ∀ ψ : Spec (C.presheaf.stalk x) ⟶ X, ψ ≫ p = C.fromSpecStalk x ≫ sC →
      ∃ (U : C.Opens) (_ : y ∈ U) (hxU : x ∈ U) (f : U.toScheme ⟶ X),
        U.fromSpecStalkOfMem x hxU ≫ f = ψ ∧ f ≫ p = U.ι ≫ sC

def LeafGlueExtend : Prop := ∀ {C X S : Scheme.{0}} [IsIntegral C] (sC : C ⟶ S) (p : X ⟶ S) [IsSeparated p] (x : C),
  IsGenericPoint x (⊤ : Set C) → ∀ ψ : Spec (C.presheaf.stalk x) ⟶ X,
    (∀ y : C, ∃ (U : C.Opens) (_ : y ∈ U) (hxU : x ∈ U) (f : U.toScheme ⟶ X),
        U.fromSpecStalkOfMem x hxU ≫ f = ψ ∧ f ≫ p = U.ι ≫ sC) →
      ∃ e : C ⟶ X, C.fromSpecStalk x ≫ e = ψ ∧ e ≫ p = sC

theorem goal_of (h1 : LeafStalkValuation) (h2 : LeafLocalExtend) (h3 : LeafGlueExtend) :
    LateralTheory.E.LeafCurveVCut.LeafExtend := by
  intro k Ω _ _ _ X C0 p _ c0 x hc hx ψ hψ
  have : IsIntegral C0 := hc.1
  refine h3 (c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p x hx ψ ?_
  intro y
  by_cases hyx : y = x
  · subst hyx
    obtain ⟨U, hxU, f, hf1, hf2⟩ := spread_out_of_isGermInjective'
      (c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p ψ hψ
    exact ⟨U, hxU, hxU, f, hf1.symm, hf2⟩
  · obtain ⟨hv, hfr⟩ := h1 Ω c0 x y hx hc hyx
    exact h2 (c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p x y hx _ hv hfr ψ hψ

end LateralTheory.E.LeafExtendCut
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.FibreEqvPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.FibPf LateralTheory.E.FibClosedPf LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibreEqvPf

theorem eqv_snd_snd {q : ℕ} {i : ℤ} {Z S K L : Scheme.{0}} (c : Z ⟶ S) (t : L ⟶ S) (k : K ⟶ L) :
    Eqv _ (sch.map (pullback.snd (pullback.snd c t) k)) (tw q i) ↔ Eqv _ (sch.map (pullback.snd c (k ≫ t))) (tw q i) := by
  have e := pullbackLeftPullbackSndIso_hom_snd c t k
  rw [← e, Functor.map_comp]
  exact ⟨fun h => eqv_right h (eqv_iso (pullbackLeftPullbackSndIso c t k) q i), fun h => eqv_comp (eqv_iso _ q i) h⟩

theorem eqv_snd_iso {q : ℕ} {i : ℤ} {Z S K K' : Scheme.{0}} (c : Z ⟶ S) (T : K ⟶ S) (ρ : K' ⟶ K) [IsIso ρ]
    (h : Eqv _ (sch.map (pullback.snd c T)) (tw q i)) : Eqv _ (sch.map (pullback.snd c (ρ ≫ T))) (tw q i) := by
  rw [← eqv_snd_snd]
  have w : sch.map (pullback.snd (pullback.snd c T) ρ) ≫ sch.map ρ = sch.map (pullback.fst (pullback.snd c T) ρ) ≫ sch.map (pullback.snd c T) := by
    rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]
  refine eqv_left (g := sch.map ρ) ?_ (eqv_iso (asIso ρ) q i)
  rw [w]
  exact eqv_comp (eqv_iso (asIso (pullback.fst (pullback.snd c T) ρ)) q i) h

def StalkFib : Prop := Hyp → HZero → AICAcyc → ∀ (q : ℕ) (i : ℤ) {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c]
  [QuasiSeparated c] [IsDominant c], AICSch Z → AICSch S → ∀ x : S, IsUnit (q : S.presheaf.stalk x) →
  Eqv _ (sch.map (pullback.snd c (S.fromSpecStalk x))) (tw q i)

theorem residue_bij {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (f : R →+* R') [IsLocalHom f]
    (hf : Function.Surjective f) : Function.Bijective (IsLocalRing.ResidueField.map f) := by
  refine ⟨(IsLocalRing.ResidueField.map f).injective, fun y => ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨IsLocalRing.residue R x, IsLocalRing.ResidueField.map_residue f x⟩

theorem geom (H : Hyp) (h0 : HZero) (hA : AICAcyc) (hS : StalkSHS) (hF : StalkFib) (q : ℕ) (i : ℤ) {Z S : Scheme.{0}}
    (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c] (hZs : AICSch Z) (hSs : AICSch S)
    (hB : ∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t))
    (x : S) (hu : IsUnit (q : S.presheaf.stalk x)) :
    Eqv _ (sch.map (pullback.snd c (cpt (S.presheaf.stalk x) ≫ S.fromSpecStalk x))) (tw q i) := by
  have hsh := hS S hSs x
  obtain ⟨_, _⟩ := id hsh
  have hx := hF H h0 hA q i c hZs hSs x hu
  have hpb : Eqv _ (sch.map (pullback.fst (pullback.snd c (S.fromSpecStalk x)) (cpt (S.presheaf.stalk x)))) (tw q i) :=
    hB _ hsh hu (S.fromSpecStalk x)
  have hE1 : Eqv _ (sch.map (cpt (S.presheaf.stalk x))) (tw q i) := H.e1 q _ (IsLocalRing.maximalIdeal _) hu i
  rw [← eqv_snd_snd]
  refine eqv_left (g := sch.map (cpt (S.presheaf.stalk x))) ?_ hE1
  rw [← Functor.map_comp, ← pullback.condition, Functor.map_comp]
  exact eqv_comp hpb hx

theorem FibreEqv_of (hS : StalkSHS) (hF : StalkFib) : FibreEqv := by
  intro H h0 hA q i A _ _ hq Z S c p _ _ _ _ _ hZs hSs hB s
  set j := pullback.fst p (cpt A)
  have h1 : SurjectiveOnStalks (cpt A) :=
    SurjectiveOnStalks.Spec_iff.2 (RingHom.surjectiveOnStalks_of_surjective IsLocalRing.residue_surjective)
  have h2 : SurjectiveOnStalks j := MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback p (cpt A)).flip h1
  have hsurj : Function.Surjective (j.stalkMap s).hom := j.stalkMap_surjective s
  have hu0 : IsUnit (q : Γ(S, ⊤)) := unit_of hq p
  have hu : IsUnit (q : S.presheaf.stalk (j s)) := by
    simpa using hu0.map (S.presheaf.germ ⊤ (j s) trivial).hom
  have hbij := residue_bij (j.stalkMap s).hom hsurj
  let ρ : Spec (CommRingCat.of (IsLocalRing.ResidueField ((pullback p (cpt A)).presheaf.stalk s))) ⟶
      Spec (CommRingCat.of (IsLocalRing.ResidueField (S.presheaf.stalk (j s)))) :=
    Spec.map (RingEquiv.ofBijective _ hbij).toCommRingCatIso.hom
  have sq : cpt ((pullback p (cpt A)).presheaf.stalk s) ≫ (pullback p (cpt A)).fromSpecStalk s ≫ j =
      ρ ≫ cpt (S.presheaf.stalk (j s)) ≫ S.fromSpecStalk (j s) := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk j, ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [ρ, cpt, ← Spec.map_comp]
    congr 1
  rw [eqv_snd_snd, sq]
  exact eqv_snd_iso c _ ρ (geom H h0 hA hS hF q i c hZs hSs hB (j s) hu)

end LateralTheory.E.FibreEqvPf

namespace LateralTheory.E.FibreEqvPf

def BaseAIC : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, AICSch (pullback c (S.fromSpecStalk x))

def StalkAIC : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, AICSch (Spec (S.presheaf.stalk x))

theorem StalkFib_of (hZB : BaseAIC) (hSA : StalkAIC) : StalkFib := by
  intro H h0 hA q i Z S c _ _ _ hZs hSs x hu
  have hB := hZB c hZs hSs x
  have hK := hSA S hSs x
  have : IsIntegral (pullback c (S.fromSpecStalk x) : Scheme.{0}) := hB.1
  have : ConnectedSpace (pullback c (S.fromSpecStalk x) : Scheme.{0}) := inferInstance
  have : CompactSpace (pullback c (S.fromSpecStalk x) : Scheme.{0}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd c (S.fromSpecStalk x))
  have : QuasiSeparatedSpace (pullback c (S.fromSpecStalk x) : Scheme.{0}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd c (S.fromSpecStalk x))
  have hu1 : IsUnit (q : Γ(Spec (S.presheaf.stalk x), ⊤)) := unit_of (A := S.presheaf.stalk x) hu (𝟙 _)
  have hu2 : IsUnit (q : Γ(pullback c (S.fromSpecStalk x), ⊤)) :=
    unit_of (A := S.presheaf.stalk x) hu (pullback.snd c (S.fromSpecStalk x))
  exact eqv_of H.a9 _ (h0 H q (pullback.snd c (S.fromSpecStalk x)) hK inferInstance hu1 i) (fun n hn => hA H q _ hB hu2 n i hn)
    (fun n hn => hA H q _ hK hu1 n i hn)

end LateralTheory.E.FibreEqvPf

namespace LateralTheory.E.FibreEqvPf

def StalkAICRing : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, AIC (S.presheaf.stalk x)

def SpecAIC : Prop := ∀ (B : CommRingCat.{0}), IsDomain B → AIC B → AICSch (Spec B)

theorem StalkAIC_of (h1 : StalkAICRing) (h2 : SpecAIC) : StalkAIC := by
  intro S hS x
  have : IsIntegral S := hS.1
  exact h2 _ inferInstance (h1 S hS x)

end LateralTheory.E.FibreEqvPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SysOf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.BuildCut LateralTheory.E.CompCut

namespace LateralTheory.E.SysPf

def HasLim : Prop := ∀ {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}),
  (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → ∃ c : Cone D, Nonempty (IsLimit c)

def NbIso : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0})
      (ι : ∀ j, D.obj j ⟶ w.normalization),
      (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
      (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)) ∧
      ∀ c : Cone D, IsLimit c →
        Nonempty (c.pt ≅ (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization)

theorem Sys_of (hH : HasLim) (hN : NbIso) : Sys := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, ι, h1, h2, h3⟩ := hN W w hW y
  obtain ⟨c, ⟨hc⟩⟩ := hH D (fun f => (h2 f).2)
  exact ⟨q, J, inferInstance, inferInstance, D, c, ι, ⟨⟨hc⟩, h1, fun f => h2 f⟩, h3 c hc⟩

end LateralTheory.E.SysPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LChartPf
noncomputable section

namespace LateralTheory.E.LChartPf

def IdemLiftInt (A : Type) [CommRing A] (I : Ideal A) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (ε : B ⧸ I.map (algebraMap A B)), IsIdempotentElem ε →
    ∃ e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = ε

def LIdemLift : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I], IdemLiftInt A I

def LSurjChart : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A), I ≤ Ideal.jacobson ⊥ → IdemLiftInt A I →
  ∀ (A' : Type) [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I),
  ∃ g : A', IsUnit (φ g) ∧ Function.Surjective (algebraMap A (Localization.Away g))

theorem isStandardEtale_of_surjective (A : Type) [CommRing A] (A' : Type) [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (g : A') (hs : Function.Surjective (algebraMap A (Localization.Away g))) :
    Algebra.IsStandardEtale A (Localization.Away g) :=
  Algebra.IsStandardEtale.of_surjective (S := A) (Algebra.ofId A _) hs

theorem LChart_of (h1 : LIdemLift) (h2 : LSurjChart) : LateralTheory.E.LEtaleLiftPf.LChart := by
  intro A _ I _ A' _ _ _ φ
  obtain ⟨g, hg, hs⟩ := h2 A I (by simpa only [Ideal.jacobson_bot] using
    (HenselianRing.jac : I ≤ Ring.jacobson A)) (h1 A I) A' φ
  exact ⟨g, hg, isStandardEtale_of_surjective A A' g hs⟩

end LateralTheory.E.LChartPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafCloseBCut
noncomputable section
open CategoryTheory AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.LeafCloseBCut

def LeafProjModel : Prop := ∀ (k : Type) [Field k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A], ∃ (B : Scheme.{0}) (b : B ⟶ Sp k) (ι : Sp A ⟶ B), IsIntegral B ∧ IsProper b ∧
    IsOpenImmersion ι ∧ ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k A))

def LeafDimOpen : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (b : X ⟶ Sp k) [LocallyOfFiniteType b],
    IsIntegral X → ∀ U : Set X, IsOpen U → U.Nonempty → topologicalKrullDim X ≤ topologicalKrullDim U

theorem goal_of (h1 : LeafProjModel) (h2 : LeafDimOpen) : LateralTheory.E.LeafSpreadVCut.LeafCloseB := by
  intro k _ A _ _ _ _
  obtain ⟨B, b, ι, hB, hb, hι, hc⟩ := h1 k A
  refine ⟨B, b, ι, hB, hb, hι, hc, ?_⟩
  obtain ⟨x⟩ : Nonempty (PrimeSpectrum A) := inferInstance
  have hemb := ι.isOpenEmbedding
  calc topologicalKrullDim B ≤ topologicalKrullDim (Set.range ι) :=
        h2 k b hB _ hemb.isOpen_range ⟨ι x, x, rfl⟩
    _ = topologicalKrullDim (Sp A) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (hemb.isEmbedding.toHomeomorph).isHomeomorph).symm
    _ = ringKrullDim A := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A

end LateralTheory.E.LeafCloseBCut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.FibreIdem
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.StdChartsProof

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

def Restr (B : Subalgebra A K) (t : K) (Q : PrimeSpectrum (AdjoinInv B t)) (S : Subalgebra A K) (x : PrimeSpectrum S) :
    Prop := ∀ s : S, s ∈ x.asIdeal ↔ ∃ d ∈ Q.asIdeal, (d : K) = (s : K)

structure Cover {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K) : Prop where
  ex : ∃ (jU : Spec (CommRingCat.of B) ⟶ Z) (jV : Spec (CommRingCat.of C) ⟶ Z),
    IsOpenImmersion jU ∧ IsOpenImmersion jV ∧ Set.range jU.base ∪ Set.range jV.base = Set.univ ∧
    jU ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A B)) ∧ jV ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A C)) ∧
    ∀ (x : PrimeSpectrum B) (y : PrimeSpectrum C), jU.base x = jV.base y ↔
      ∃ Q : PrimeSpectrum (AdjoinInv B t), Restr B t Q B x ∧ Restr B t Q C y

def ChartsGeom : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z →
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧ Cover p B C t

def FibreIdem : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K] {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K), Charts B C t → Cover p B C t →
    ∀ W : Set ↑(pullback p (cpt A)), IsClopen W → ∃ e f : K, IdemPair B C t e f ∧
      ((e ∈ mS B ∧ f ∈ mS C) → W = ∅) ∧ ((e - 1 ∈ mS B ∧ f - 1 ∈ mS C) → W = Set.univ)

theorem StdCharts_of (hG : ChartsGeom) (hF : FibreIdem) : LateralTheory.E.StandardEtaleChartsIdempotentGluing.StdCharts := by
  intro A _ _ Z p hIL hZ
  obtain ⟨K, hK, hA, B, C, t, hc, hint, hcov⟩ := hG A p hIL hZ
  exact ⟨K, hK, hA, B, C, t, hc, hint, fun W hW => hF A K p B C t hc hcov W hW⟩

end LateralTheory.E.StdChartsProof
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LZIdemSumApprox
noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.IdempotentLiftingAlt

def LZIdemSumNoeth : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : Type) [Field K]
  [Algebra A K] (B C : Subalgebra A K) (t : K), Charts B C t → B.FG → C.FG → ∀ e f : K, IdemPair B C t e f →
  e - f ∈ mS B ⊔ mS C

def LZIdemSumApprox : Prop := LZIdemSumNoeth → ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K]
  [Algebra A K] (B C : Subalgebra A K) (t : K), Charts B C t → ∀ e f : K, IdemPair B C t e f →
  e - f ∈ mS B ⊔ mS C

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

theorem mS_le (S : Subalgebra A K) : mS S ≤ Subalgebra.toSubmodule S := by
  unfold mS
  exact Submodule.smul_le_right

theorem lift_of_sum (B C : Subalgebra A K) (e f : K) (he : e ∈ B) (hf : f ∈ C) (h : e - f ∈ mS B ⊔ mS C) :
    ∃ g ∈ B, g ∈ C ∧ g - e ∈ mS B ∧ g - f ∈ mS C := by
  obtain ⟨β, hβ, γ, hγ, hsum⟩ := Submodule.mem_sup.mp h
  have hβB : β ∈ B := mS_le B hβ
  have hγC : γ ∈ C := mS_le C hγ
  refine ⟨e - β, B.sub_mem he hβB, ?_, ?_, ?_⟩
  · have : e - β = f + γ := by linear_combination -hsum
    rw [this]; exact C.add_mem hf hγC
  · have : e - β - e = -β := by ring
    rw [this]; exact (mS B).neg_mem hβ
  · have : e - β - f = γ := by linear_combination -hsum
    rw [this]; exact hγ

theorem IdemLift_of (hN : LZIdemSumNoeth) (hA : LZIdemSumApprox) : LateralTheory.E.StandardEtaleChartsIdempotentGluing.IdemLift := by
  intro A _ _ _ K _ _ B C t hc e f hp
  exact lift_of_sum B C e f hp.1 hp.2.1 (hA hN A K B C t hc e f hp)

end LateralTheory.E.IdempotentLiftingAlt
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.RelDescPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.RelDescPf

theorem hkpull_comp (R : Type) [CommRing R] {K L M : Cx R} (a : K ⟶ L) (b : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (a ≫ b) F n x = HK.pull R a F n (HK.pull R b F n x) := by
  obtain ⟨y, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  change (Cochain.ofHom (a ≫ b)).comp y.1 (zero_add n) =
    (Cochain.ofHom a).comp ((Cochain.ofHom b).comp y.1 (zero_add n)) (zero_add n)
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]

theorem rmap_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm : f' ≫ e = u ≫ f) (comm' : f'' ≫ e' = u' ≫ f')
    (comm'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) :
    rmap R f f'' (u' ≫ u) (e' ≫ e) comm'' = rmap R f' f'' u' e' comm' ≫ rmap R f f' u e comm := by
  simp only [rmap, Functor.map_comp]
  exact mappingCone.map_comp _ _ _ _ _ _ _ _ _

theorem rpull_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm : f' ≫ e = u ≫ f) (comm' : f'' ≫ e' = u' ≫ f')
    (comm'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) (F : Shv R) (n : ℤ) (y : Hrel R f F n) :
    rpull R f f'' (u' ≫ u) (e' ≫ e) comm'' F n y = rpull R f' f'' u' e' comm' F n (rpull R f f' u e comm F n y) := by
  simp only [rpull]
  rw [rmap_comp R f f' f'' u e u' e' comm comm' comm'']
  exact hkpull_comp R _ _ F n y

def RelEqvInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
  (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f), Eqv R u F → Eqv R e F → ∀ n : ℤ, Function.Injective (rpull R f f' u e comm F n)

def CechEqv : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E)
  (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''), Et e → SpS e → IsPushout φ' e u φ'' →
  Eqv (ZMod q) (cechAug (Spec.map e)) (tw q i) ∧ Eqv (ZMod q) (cechAug (Spec.map u)) (tw q i)

def LevelInj : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → IsPushout φ' e u φ'' →
  ∃ (g : cech (Spec.map u) ⟶ cech (Spec.map e)) (_hA : g ≫ cechAug (Spec.map e) = cechAug (Spec.map u) ≫ sch.map (Spec.map φ'))
    (i0 : sch.obj (Spec E) ⟶ cech (Spec.map e)) (j0 : sch.obj (Spec Y'') ⟶ cech (Spec.map u))
    (h0 : sch.map (Spec.map φ'') ≫ i0 = j0 ≫ g),
    i0 ≫ cechAug (Spec.map e) = sch.map (Spec.map e) ∧ j0 ≫ cechAug (Spec.map u) = sch.map (Spec.map u) ∧
    Function.Injective (rpull (ZMod q) g (sch.map (Spec.map φ'')) j0 i0 h0 (tw q i) n)

theorem relDesc_of (hEq : RelEqvInj) (hC : CechEqv) (hL : LevelInj) : LateralTheory.E.TruncationKernel.RelDesc := by
  intro hH q _ i n A Y φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo'
  obtain ⟨g, hA, i0, j0, h0, hi, hj, hinj⟩ := hL hH q i n φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo'
  obtain ⟨hCe, hCu⟩ := hC hH q i φ' e u φ'' he hs hpo'
  have h1 := hEq (ZMod q) (tw q i) (sch.map (Spec.map φ')) g (cechAug (Spec.map u)) (cechAug (Spec.map e)) hA hCu hCe n
  have key : ∀ (a : sch.obj (Spec Y'') ⟶ sch.obj (Spec Y')) (b : sch.obj (Spec E) ⟶ sch.obj (Spec D))
      (ha : j0 ≫ cechAug (Spec.map u) = a) (hb : i0 ≫ cechAug (Spec.map e) = b)
      (c : sch.map (Spec.map φ'') ≫ b = a ≫ sch.map (Spec.map φ')),
      Function.Injective (rpull (ZMod q) (sch.map (Spec.map φ')) (sch.map (Spec.map φ'')) a b c (tw q i) n) := by
    intro a b ha hb c
    subst ha hb
    intro x y hxy
    rw [rpull_comp _ _ g _ _ _ _ _ hA h0 c, rpull_comp _ _ g _ _ _ _ _ hA h0 c] at hxy
    exact h1 (hinj hxy)
  exact key _ _ hj hi _

theorem etale_spec {D E : CommRingCat.{0}} (e : D ⟶ E) (he : Et e) : Etale (Spec.map e) :=
  HasRingHomProperty.Spec_iff.mpr he

theorem surj_spec {D E : CommRingCat.{0}} (e : D ⟶ E) (hs : SpS e) : Surjective (Spec.map e) := by
  constructor
  intro x
  obtain ⟨Q, hQ, hQr⟩ := hs x.asIdeal x.isPrime
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQr⟩

theorem cechEqv : CechEqv := by
  intro hH q _ i D Y' E Y'' φ' e u φ'' he hs hpo
  have hpb := isPullback_SpecMap_of_isPushout φ' e u φ'' hpo
  have hE : Etale (Spec.map e) := etale_spec e he
  have hS : Surjective (Spec.map e) := surj_spec e hs
  have hEu : Etale (Spec.map u) := MorphismProperty.of_isPullback (P := @Etale) hpb.flip hE
  have hSu : Surjective (Spec.map u) := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hS
  exact ⟨hH.2.1 (ZMod q) (Spec.map e) (tw q i), hH.2.1 (ZMod q) (Spec.map u) (tw q i)⟩

end LateralTheory.E.RelDescPf
end
end
