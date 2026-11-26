module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
section -- merged from Development.EtaleCohomology.EtaleSheaves.EtaleChapterEFour
def LateralTheory.E.EtaleChapterEFour : Prop :=
  GlobalTheory.EtC.A1 → GlobalTheory.EtC.A2 → GlobalTheory.EtC.A3 → GlobalTheory.EtC.A4 → GlobalTheory.EtC.A5 → GlobalTheory.EtC.A7 → GlobalTheory.EtC.A8 → GlobalTheory.EtC.A9 → GlobalTheory.EtC.A10 → GlobalTheory.EtC.A11 → GlobalTheory.EtC.B1 → GlobalTheory.EtC.B2 → GlobalTheory.EtC.B3 → GlobalTheory.EtC.B4 → GlobalTheory.EtC.B5 → GlobalTheory.EtC.B7 → GlobalTheory.EtC.C1 → GlobalTheory.EtC.C2 → GlobalTheory.EtC.C3 → GlobalTheory.EtC.C4 → GlobalTheory.EtC.C5 → GlobalTheory.EtC.D1 → GlobalTheory.EtC.D2 → GlobalTheory.EtC.D3 → GlobalTheory.EtC.E1 → GlobalTheory.EtC.E2 → GlobalTheory.EtC.E3 → GlobalTheory.EtC.E4
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4

def Hyps : Prop :=
  A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A7 ∧ A8 ∧ A9 ∧ A10 ∧ A11 ∧ B1 ∧ B2 ∧ B3 ∧ B4 ∧ B5 ∧ B7 ∧ C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5 ∧
    D1 ∧ D2 ∧ D3 ∧ E1 ∧ E2 ∧ E3

abbrev Sp (A : Type) [CommRing A] : Scheme.{0} := Spec (CommRingCat.of A)

abbrev pl (q : ℕ) (i : ℤ) {Y X : Scheme.{0}} (f : Y ⟶ X) (m : ℤ) : Ht q (sch.obj X) m i →+ Ht q (sch.obj Y) m i :=
  pull (ZMod q) (sch.map f) (tw q i) m

def IsCurve {Ω : Type} [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) : Prop :=
  IsIntegral C ∧ IsProper c ∧ SmoothOfRelativeDimension 1 c

def SmP {Y B : Scheme.{0}} (p : Y ⟶ B) (V : B.Opens) : Prop := IsProper p ∧ Smooth (p ∣_ V)

abbrev fibMap {Y1 Y0 B S : Scheme.{0}} (g : Y1 ⟶ Y0) (p : Y0 ⟶ B) (s : S ⟶ B) : pullback (g ≫ p) s ⟶ pullback p s :=
  pullback.map (g ≫ p) s p s g (𝟙 _) (𝟙 _) (by simp) (by simp)

def H0TwistOverClosedField : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) → ∀ i : ℤ,
  Finite (Ht q (sp Ω) 0 i) ∧ ∀ {X : Scheme.{0}} [ConnectedSpace X] (c : X ⟶ Sp Ω), Function.Bijective (pl q i c 0)

def LeafPt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p], topologicalKrullDim X ≤ 0 → ∀ n i : ℤ,
  Finite (Ht q (sch.obj X) n i)

def LeafComp : Prop := Hyps → ∀ (q : ℕ) (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (n i : ℤ),
  (∀ (Z : Scheme.{0}) (ι : Z ⟶ X), IsClosedImmersion ι → IsIntegral Z → Finite (Ht q (sch.obj Z) n i)) →
  ∃ (Y : Scheme.{0}) (f : Y ⟶ X), IsProper f ∧ Surjective f ∧ Finite (Ht q (sch.obj Y) n i)

def LeafDesc : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) →
  ∀ {Y X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (f : Y ⟶ X) [IsProper f] [Surjective f] (i : ℤ), Eqv _ (cechAug f) (tw q i)

def LeafSS : Prop := Hyps → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f] (n : ℤ),
  Eqv R (cechAug f) F → (∀ (Z : Scheme.{0}) (g : Z ⟶ X), IsProper g → ∀ m < n, Finite (H R (sch.obj Z) F m)) →
  Finite (pull R (sch.map f) F n).ker

def LeafUnits : Prop := ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], Finite (Bˣ ⧸ (powMonoidHom q : Bˣ →* Bˣ).range)

def LeafPic : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → Finite {c : CommRing.Pic B // c ^ q = 1}

def LeafKum : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B],
  IsUnit (q : k) → Finite (Bˣ ⧸ (powMonoidHom q : Bˣ →* Bˣ).range) → Finite {c : CommRing.Pic B // c ^ q = 1} →
  ∀ i : ℤ, Finite (Ht q (sp B) 1 i)

def LeafCurve : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) → ∀ i : ℤ,
  (∀ (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra Ω B] [Algebra.FiniteType Ω B], Finite (Ht q (sp B) 1 i)) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → Finite (Ht q (sch.obj C) 1 i) ∧ Finite (Ht q (sch.obj C) 2 i) ∧
    ∀ m : ℤ, 3 ≤ m → Subsingleton (Ht q (sch.obj C) m i)

def LeafKill : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → ∀ m i : ℤ, 0 < m → Finite (Ht q (sch.obj C) m i) →
  ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ pl q i γ m = 0

def Family {k Ω : Type} [Field k] [Field Ω] (X : Scheme.{0}) {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0)
    (γ2 : C2 ⟶ C1) : Prop :=
  ∃ (B W Y0 Y1 Y2 : Scheme.{0}) (b : B ⟶ Sp k) (ι : W ⟶ B) (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1)
    (h : Y0 ⟶ X) (s : Sp Ω ⟶ B) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
    IsIntegral B ∧ IsProper b ∧ IsClosedImmersion ι ∧ (V : Set B) = (Set.range ι)ᶜ ∧ Set.range s ⊆ V ∧
    SmP p V ∧ SmP (g1 ≫ p) V ∧ SmP (g2 ≫ g1 ≫ p) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧ Surjective (g2 ≫ g1 ≫ h) ∧
    topologicalKrullDim B < topologicalKrullDim X ∧
    topologicalKrullDim (pullback p ι : Scheme.{0}) < topologicalKrullDim X ∧
    IsPullback u0 c0 p s ∧ IsPullback u1 (γ1 ≫ c0) (g1 ≫ p) s ∧ IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ p) s ∧
    γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2

def LeafGeo : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k Ω) (C0 : Scheme.{0})
    (c0 : C0 ⟶ Sp Ω), IsCurve c0 ∧ ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) →
      IsCurve (γ2 ≫ γ1 ≫ c0) → Surjective γ1 → Surjective γ2 → Family (k := k) X c0 γ1 γ2

def LeafSpec : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B Y0 Y1 : Scheme.{0}} [IsIntegral B] (_ : B ⟶ Sp k) (V : B.Opens) (p : Y0 ⟶ B) (g : Y1 ⟶ Y0), SmP p V → SmP (g ≫ p) V →
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ B), Set.range s ⊆ V →
  ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ : C1 ⟶ C0) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1),
    IsPullback u0 c0 p s → IsPullback u1 (γ ≫ c0) (g ≫ p) s → γ ≫ u0 = u1 ≫ g →
  ∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, Subsingleton (Ht q (sch.obj C0) m i) → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧
    (∀ m, pl q i γ m = 0 → pl q i (fibMap g p t) m = 0) ∧
    (Function.Bijective (pl q i (γ ≫ c0) 0) → Function.Bijective (pl q i (pullback.snd (g ≫ p) t) 0))

def LeafGhost : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)) →
  ∀ (n : ℤ) (a : Ht q (sch.obj Y0) n i), pl q i (pullback.fst p ι) n a = 0 →
    ∃ b : Ht q (sch.obj B) n i, pl q i (g2 ≫ g1 ≫ p) n b = pl q i (g2 ≫ g1) n a

theorem fin_of {A C D E : Type*} [AddCommGroup A] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] (φ : A →+ C)
    (r : A →+ D) (ψ : E →+ C) [Finite D] [Finite E] (hk : Finite φ.ker) (h : ∀ a, r a = 0 → ∃ b, ψ b = φ a) : Finite A := by
  rw [AddMonoidHom.finite_iff_finite_ker_range r]
  refine ⟨?_, inferInstance⟩
  rw [AddMonoidHom.finite_iff_finite_ker_range (φ.comp r.ker.subtype)]
  constructor
  · exact Finite.of_injective (fun x : (φ.comp r.ker.subtype).ker => (⟨x.1.1, x.2⟩ : φ.ker))
      (fun x y hxy => Subtype.ext (Subtype.ext (congrArg (fun z : φ.ker => z.1) hxy)))
  · have : (Set.range ψ).Finite := Set.finite_range _
    refine Set.Finite.subset this ?_
    rintro _ ⟨a, rfl⟩
    exact h a.1 a.2

theorem pl_comp (q : ℕ) (i : ℤ) {Z Y X : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (m : ℤ) (x : Ht q (sch.obj X) m i) :
    pl q i (g ≫ f) m x = pl q i g m (pl q i f m x) := by
  rw [← pull_comp, ← Functor.map_comp]

theorem goal_of (hH0 : H0TwistOverClosedField) (hPt : LeafPt) (hComp : LeafComp) (hDesc : LeafDesc) (hSS : LeafSS) (hU : LeafUnits)
    (hPic : LeafPic) (hKum : LeafKum) (hCurve : LeafCurve) (hKill : LeafKill) (hGeo : LeafGeo) (hSpec : LeafSpec)
    (hGhost : LeafGhost) : LateralTheory.E.EtaleChapterEFour := by
  intro a1 a2 a3 a4 a5 a7 a8 a9 a10 a11 b1 b2 b3 b4 b5 b7 c1 c2 c3 c4 c5 d1 d2 d3 e1 e2 e3
  have hy : Hyps := ⟨a1, a2, a3, a4, a5, a7, a8, a9, a10, a11, b1, b2, b3, b4, b5, b7, c1, c2, c3, c4, c5, d1, d2, d3, e1, e2, e3⟩
  intro q _ k _ _ hq X p _ n i
  have step : ∀ n : ℤ, (∀ (X : Scheme.{0}) (p : X ⟶ Sp k), IsProper p → ∀ m < n, Finite (Ht q (sch.obj X) m i)) →
      ∀ (e : WithBot ℕ∞) (X : Scheme.{0}) (p : X ⟶ Sp k), IsProper p → topologicalKrullDim X ≤ e →
        Finite (Ht q (sch.obj X) n i) := by
    intro n Q
    have ker : ∀ (X Y : Scheme.{0}) (p : X ⟶ Sp k) (f : Y ⟶ X), IsProper p → IsProper f → Surjective f →
        Finite (pl q i f n).ker := fun X Y p f _ _ _ =>
      hSS hy _ _ f n (hDesc hy q k hq p f i) (fun Z g _ => Q Z (g ≫ p) inferInstance)
    intro e
    induction e using WellFoundedLT.induction with
    | ind e IH =>
    have int : ∀ (X : Scheme.{0}) (p : X ⟶ Sp k), IsProper p → IsIntegral X → topologicalKrullDim X ≤ e →
        Finite (Ht q (sch.obj X) n i) := by
      intro X p _ _ he
      rcases le_or_gt (topologicalKrullDim X) 0 with h0 | h0
      · exact hPt hy q k hq p h0 n i
      obtain ⟨Ω, _, _, _, C0, c0, hc0, hall⟩ := hGeo k p h0
      have hΩ : IsUnit (q : Ω) := by simpa using hq.map (algebraMap k Ω)
      have hc : ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → _ := fun c => hCurve hy q Ω hΩ i
        (fun B _ _ _ _ => hKum hy q Ω B hΩ (hU q Ω B) (hPic hy q Ω B hΩ) i) c
      obtain ⟨C1, γ1, hc1, s1, z1⟩ := hKill hy q Ω hΩ c0 hc0 2 i (by norm_num) (hc c0 hc0).2.1
      obtain ⟨C2, γ2, hc2, s2, z2⟩ := hKill hy q Ω hΩ (γ1 ≫ c0) hc1 1 i (by norm_num) (hc _ hc1).1
      obtain ⟨B, W, Y0, Y1, Y2, b, ι, V, π, g1, g2, h, s, u0, u1, u2, _, _, _, hV, hs, m0, m1, m2, f1, f2, dB, dW,
        P0, P1, P2, w1, w2⟩ := hall C1 C2 γ1 γ2 hc1 hc2 s1 s2
      have := m0.1
      have := hc2.1
      have fB := IH _ (dB.trans_le he) B b inferInstance le_rfl
      have fW := IH _ (dW.trans_le he) (pullback π ι) (pullback.fst π ι ≫ π ≫ b) inferInstance le_rfl
      have G := hGhost hy q k hq i b ι V hV π g1 g2 m0.1 m1.1 m2.1 (fun A _ t hA ht => by
        have S1 := hSpec hy q k hq i b V π g1 m0 m1 Ω s hs c0 γ1 u0 u1 P0 P1 w1 A t hA ht
        have S2 := hSpec hy q k hq i b V (g1 ≫ π) g2 m1 m2 Ω s hs (γ1 ≫ c0) γ2 u1 u2 P1 P2 w2 A t hA ht
        exact ⟨fun m hm => S1.1 m ((hc c0 hc0).2.2 m hm), S1.2.1 2 z1, S2.2.1 1 z2,
          S2.2.2 ((hH0 hy q Ω hΩ i).2 _)⟩) n
      refine fin_of (pl q i (g2 ≫ g1 ≫ h) n) (pl q i (pullback.fst π ι ≫ h) n) (pl q i (g2 ≫ g1 ≫ π) n)
        (ker X Y2 p _ inferInstance f1 f2) (fun a ha => ?_)
      rw [pl_comp] at ha
      obtain ⟨x, hx⟩ := G _ ha
      exact ⟨x, by rw [hx, ← pl_comp, Category.assoc]⟩
    intro X p _ he
    obtain ⟨Y, f, f1, f2, f3⟩ := hComp hy q k p n i (fun Z ι _ _ =>
      int Z (ι ≫ p) inferInstance inferInstance (ι.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans he))
    have := ker X Y p f inferInstance f1 f2
    rw [AddMonoidHom.finite_iff_finite_ker_range (pl q i f n)]
    exact ⟨this, inferInstance⟩
  have all : ∀ (N : ℕ) (X : Scheme.{0}) (p : X ⟶ Sp k), IsProper p → ∀ m < (N : ℤ), Finite (Ht q (sch.obj X) m i) := by
    intro N
    induction N with
    | zero =>
      intro X p _ m hm
      have := (a9 (ZMod q) (tw q i)).1 (sch.obj X) m (by simpa using hm)
      exact Finite.of_subsingleton
    | succ N IH =>
      intro X p hp m hm
      rcases lt_or_eq_of_le (show m ≤ N by omega) with h | h
      · exact IH X p hp m h
      · subst h
        exact step _ IH _ X p hp le_rfl
  exact all (n.toNat + 1) X p inferInstance n (by omega)

end LateralTheory.E.E4

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
section -- merged from Development.EtaleCohomology.EtaleSheaves.EtaleChapterEThree
def LateralTheory.E.EtaleChapterEThree : Prop :=
  GlobalTheory.EtC.A1 → GlobalTheory.EtC.A2 → GlobalTheory.EtC.A3 → GlobalTheory.EtC.A4 → GlobalTheory.EtC.A5 → GlobalTheory.EtC.A7 → GlobalTheory.EtC.A8 → GlobalTheory.EtC.A9 → GlobalTheory.EtC.A10 → GlobalTheory.EtC.A11 → GlobalTheory.EtC.B1 → GlobalTheory.EtC.B2 → GlobalTheory.EtC.B3 → GlobalTheory.EtC.B4 → GlobalTheory.EtC.B5 → GlobalTheory.EtC.B7 → GlobalTheory.EtC.C1 → GlobalTheory.EtC.C2 → GlobalTheory.EtC.C3 → GlobalTheory.EtC.C4 → GlobalTheory.EtC.C5 → GlobalTheory.EtC.D1 → GlobalTheory.EtC.D2 → GlobalTheory.EtC.D3 → GlobalTheory.EtC.E1 → GlobalTheory.EtC.E2 → GlobalTheory.EtC.E3
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.t_E3Cut

def Hyp : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A9 ∧ B1 ∧ B2 ∧ B4 ∧ C3 ∧ C4

def RE (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) : Prop := Eqv _ (sch.map (Spec.map f)) (tw q i)

def BC (q : ℕ) (i : ℤ) {A Y C : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) : Prop :=
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' → RE q i φ'

def Et : MorphismProperty CommRingCat.{0} := fun _ _ f => f.hom.Etale

def IE : MorphismProperty CommRingCat.{0} := MorphismProperty.ind.{0} Et

def AlgRes : MorphismProperty CommRingCat.{0} := fun A C f =>
  ∀ Q : Ideal C, Q.IsPrime → ∀ c : C, ∃ p : Polynomial A, (∃ n, f.hom (p.coeff n) ∉ Q) ∧ p.eval₂ f.hom c ∈ Q

def SpS {A B : CommRingCat.{0}} (f : A ⟶ B) : Prop :=
  ∀ r : Ideal A, r.IsPrime → ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap f.hom = r

abbrev pC (A : CommRingCat.{0}) : A ⟶ CommRingCat.of (Polynomial A) := CommRingCat.ofHom Polynomial.C

def Good (q : ℕ) (i : ℤ) {T K A : CommRingCat.{0}} (k : T ⟶ K) (t : T ⟶ A) : Prop :=
  ∀ (B : CommRingCat.{0}) (c : A ⟶ B), Et c → BC q i k (t ≫ c)

theorem RE.comp {q : ℕ} {i : ℤ} {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hf : RE q i f) (hg : RE q i g) :
    RE q i (f ≫ g) := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n) =
      pull _ (sch.map (Spec.map g)) (tw q i) n ∘ pull _ (sch.map (Spec.map f)) (tw q i) n := by
    funext x; rw [Spec.map_comp, Functor.map_comp, pull_comp]; rfl
  rw [h]; exact (hg n).comp (hf n)

theorem RE.of_comp_left {q : ℕ} {i : ℤ} {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hf : RE q i f)
    (hfg : RE q i (f ≫ g)) : RE q i g := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n) =
      pull _ (sch.map (Spec.map g)) (tw q i) n ∘ pull _ (sch.map (Spec.map f)) (tw q i) n := by
    funext x; rw [Spec.map_comp, Functor.map_comp, pull_comp]; rfl
  have := hfg n
  rw [h] at this; exact (Function.Bijective.of_comp_iff _ (hf n)).1 this

theorem RE.of_comp_right {q : ℕ} {i : ℤ} {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hg : RE q i g)
    (hfg : RE q i (f ≫ g)) : RE q i f := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n) =
      pull _ (sch.map (Spec.map g)) (tw q i) n ∘ pull _ (sch.map (Spec.map f)) (tw q i) n := by
    funext x; rw [Spec.map_comp, Functor.map_comp, pull_comp]; rfl
  have := hfg n
  rw [h] at this; exact (Function.Bijective.of_comp_iff' (hg n) _).1 this

theorem RE.of_isIso (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) [IsIso f] : RE q i f := fun n => by
  have h1 : ∀ x, pull _ (sch.map (Spec.map (inv f))) (tw q i) n (pull _ (sch.map (Spec.map f)) (tw q i) n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, CategoryTheory.Functor.map_id, pull_id]
  have h2 : ∀ x, pull _ (sch.map (Spec.map f)) (tw q i) n (pull _ (sch.map (Spec.map (inv f))) (tw q i) n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id, CategoryTheory.Functor.map_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem BC.of_one {q : ℕ} {i : ℤ} {A Y C Y' : CommRingCat.{0}} {φ : A ⟶ Y} {c : A ⟶ C} {w : Y ⟶ Y'} {φ' : C ⟶ Y'}
    (h : IsPushout φ c w φ') (hr : RE q i φ') : BC q i φ c := fun _ _ ψ h' => by
  rw [← h.inr_isoIsPushout_hom _ _ h']
  exact hr.comp (RE.of_isIso q i _)

def AlgResProps : Prop :=
  (∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), AlgRes f → AlgRes g → AlgRes (f ≫ g)) ∧
  (∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), AlgRes (f ≫ g) → AlgRes g) ∧
  (∀ {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D), IsPushout f g u v → AlgRes f → AlgRes v) ∧
  (∀ {A B : CommRingCat.{0}} (f : A ⟶ B), Et f → AlgRes f) ∧
  (∀ {A B : CommRingCat.{0}} (f : A ⟶ B), f.hom.IsIntegral → AlgRes f) ∧
  ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B],
    AlgRes (CommRingCat.ofHom (algebraMap A B))

def IEComp : Prop := ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), IE f → IE g → IE (f ≫ g)

def LocIE : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B],
  IE (CommRingCat.ofHom (algebraMap A B))

def SHExists : Prop := ∀ (A : CommRingCat.{0}) (r : Ideal A), r.IsPrime →
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O), IE f ∧ SH O ∧ ∀ a : A, a ∈ r ↔ ¬ IsUnit (f.hom a)

def AICSH : Prop := ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → SH T

def AICExt : Prop := ∀ (C : CommRingCat.{0}), ∃ (D : CommRingCat.{0}) (g : C ⟶ D),
  g.hom.IsIntegral ∧ Function.Injective g.hom ∧ AIC D

def DomCover : Prop := ∀ (C : CommRingCat.{0}), AIC C → ∃ (D : CommRingCat.{0}) (g : C ⟶ D),
  g.hom.IsIntegral ∧ SpS g ∧ ∀ (r : Ideal D) [r.IsPrime], IsDomain (Localization.AtPrime r) ∧ AIC (Localization.AtPrime r)

def HensInt : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] (f : A →+* B),
  f.IsIntegral → (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) → Nonempty (HenselianLocalRing B)

def SHTensor : Prop := ∀ {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z), IsPushout x b u v →
  SH A → SH X → IsLocalHom x.hom → b.hom.IsIntegral → IsLocalRing B → SH Z

def IntClos : Prop := ∀ {A C : CommRingCat.{0}} (c : A ⟶ C) [IsDomain C], SH A → AIC C → AlgRes c →
  ∃ (B : CommRingCat.{0}) (b : A ⟶ B) (j : B ⟶ C), b ≫ j = c ∧ b.hom.IsIntegral ∧ Function.Injective j.hom ∧ IsLocalRing B ∧
    AIC B ∧ ∀ z : C, ∃ s y : B, s ≠ 0 ∧ j.hom s * z = j.hom y

def SHSection : Prop := ∀ (A : CommRingCat.{0}), SH A → ∀ {V : Scheme.{0}} (g : V ⟶ Spec A) [Etale g] [Surjective g],
  ∃ s : Spec A ⟶ V, s ≫ g = 𝟙 _

def Coprod : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {ι : Type} (X : ι → Scheme.{0}) (n : ℤ),
  Function.Bijective fun (x : H R (sch.obj (∐ X)) F n) (j : ι) => pull R (sch.map (Sigma.ι X j)) F n x

def ZarLocal : Prop := Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (g : Y ⟶ X),
  (∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, IsAffineOpen V → V ≤ U → Eqv R (sch.map (g ∣_ V)) F) → Eqv R (sch.map g) F

def Limit : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  (∀ (C : CommRingCat.{0}) (c : A ⟶ C), Et c → BC q i φ c) → ∀ (C : CommRingCat.{0}) (c : A ⟶ C), IE c → BC q i φ c

def Stalk : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop,
  (∀ {C D E Z : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D) (g : C ⟶ E) (u : D ⟶ Z) (v : E ⟶ Z), IsPushout f g u v →
    P C c → P D (c ≫ f) → P E (c ≫ g) → P Z (c ≫ f ≫ u)) →
  (∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D), P C c → Et f → P D (c ≫ f)) →
  (∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → ∃ (D : CommRingCat.{0}) (g : C ⟶ D), g.hom.IsIntegral ∧ SpS g ∧ P D (c ≫ g) ∧
    ∀ r : Ideal D, r.IsPrime → ∃ (O : CommRingCat.{0}) (o : D ⟶ O) (Q : Ideal O), IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
      BC q i φ (c ≫ g ≫ o)) →
  ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BC q i φ c

def SHEqv : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B), IsUnit (q : A) → SH A → SH B → RE q i f

def EtaleBaseChangeFractionFieldIndEtaleOverPolynomial : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) (T K : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [Field K] [Algebra T K]
  [IsFractionRing T K], AIC T → IsUnit (q : T) → ∀ (X : CommRingCat.{0}) (h : CommRingCat.of (Polynomial T) ⟶ X), IE h →
  BC q i (CommRingCat.ofHom (algebraMap T K)) (pC (CommRingCat.of T) ≫ h)

def ULAStalk : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A X : CommRingCat.{0}} (h : CommRingCat.of (Polynomial A) ⟶ X),
  IsUnit (q : A) → SH A → SH X → IE h → IsLocalHom (pC A ≫ h).hom →
  ∀ (C : CommRingCat.{0}) (c : A ⟶ C) [IsDomain C] [IsLocalRing C], AIC C → AlgRes c → BC q i (pC A ≫ h) c

def ULA : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A X : CommRingCat.{0}} (h : CommRingCat.of (Polynomial A) ⟶ X),
  IsUnit (q : A) → SH A → SH X → IE h → IsLocalHom (pC A ≫ h).hom →
  ∀ (C : CommRingCat.{0}) (c : A ⟶ C), AlgRes c → BC q i (pC A ≫ h) c

def Step : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {T K A : CommRingCat.{0}} (k : T ⟶ K) (t : T ⟶ A), IsUnit (q : T) →
  AlgRes k → Good q i k t → Good q i k (t ≫ pC A)

def Base : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
  Good q i (CommRingCat.ofHom (algebraMap T (FractionRing T))) (𝟙 _)

def Global : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) {T K : CommRingCat.{0}} (k : T ⟶ K),
  (∀ n : ℕ, Good q i k (CommRingCat.ofHom (MvPolynomial.C : T →+* MvPolynomial (Fin n) T))) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec T) [Smooth p], Eqv _ (sch.map (pullback.fst p (Spec.map k))) (tw q i)

theorem Good.of_equiv {q : ℕ} {i : ℤ} {T K A A' : CommRingCat.{0}} {k : T ⟶ K} {t : T ⟶ A} (h : Good q i k t)
    (e : A ≃+* A') (t' : T ⟶ A') (ht : t ≫ CommRingCat.ofHom e.toRingHom = t') : Good q i k t' := fun B c hc => by
  rw [← ht, Category.assoc]
  exact h B _ (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective e.bijective) hc)

theorem goal_of (h1 : AlgResProps) (h2 : Base) (h3 : Step) (h4 : Global) : LateralTheory.E.EtaleChapterEThree := by
  intro a1 a2 a3 a4 a5 _ _ a9 _ _ b1 b2 _ b4 _ _ _ _ c3 c4 _ _ _ _ _ _ q _ T _ _ _ hT hq X p _ i
  have H : Hyp := ⟨a1, a2, a3, a4, a5, a9, b1, b2, b4, c3, c4⟩
  refine h4 H q i _ (fun n => ?_) p
  induction n with
  | zero =>
    refine (h2 H q i T hT hq).of_equiv (MvPolynomial.isEmptyRingEquiv T (Fin 0)).symm _ ?_
    ext x; simp
  | succ n ih =>
    refine (h3 H q i _ _ hq (h1.2.2.2.2.2 T _ (nonZeroDivisors T)) ih).of_equiv
      (MvPolynomial.finSuccEquiv T n).symm.toRingEquiv _ ?_
    ext1
    exact RingHom.ext fun x => (MvPolynomial.finSuccEquiv T n).symm.commutes x

end LateralTheory.E.t_E3Cut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.InstCommRingR
section -- merged from Development.EtaleCohomology.EtaleSheaves.EtaleChapterDTwo
def LateralTheory.E.EtaleChapterDTwo : Prop :=
  GlobalTheory.EtC.A1 → GlobalTheory.EtC.A2 → GlobalTheory.EtC.A3 → GlobalTheory.EtC.A4 → GlobalTheory.EtC.A5 → GlobalTheory.EtC.A7 → GlobalTheory.EtC.A8 → GlobalTheory.EtC.A9 → GlobalTheory.EtC.A10 → GlobalTheory.EtC.A11 → GlobalTheory.EtC.B1 → GlobalTheory.EtC.B2 → GlobalTheory.EtC.B3 → GlobalTheory.EtC.B4 → GlobalTheory.EtC.B5 → GlobalTheory.EtC.B7 → GlobalTheory.EtC.C1 → GlobalTheory.EtC.C2 → GlobalTheory.EtC.C3 → GlobalTheory.EtC.C4 → GlobalTheory.EtC.C5 → GlobalTheory.EtC.D1 → GlobalTheory.EtC.D2
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2

theorem inv_of {q : ℕ} {E E' : Spc} (f : E ⟶ E') (h : Inv q E') : Inv q E :=
  fun U ⟨x⟩ => h U ⟨(f.app _).app _ x⟩

structure Collected (q : ℕ) where
  R : ∀ E : Spc, Inv q E → Type 1
  ring : ∀ E h, CommRing (R E h)
  ι : ∀ {E : Spc} (h : Inv q E) (k : ℕ), letI := ring E h; Ht q E (2 * k) k →+ R E h
  π : ∀ {E : Spc} (h : Inv q E) (k : ℕ), letI := ring E h; R E h →+ Ht q E (2 * k) k
  map : ∀ {E E' : Spc} (_ : E ⟶ E') (h : Inv q E) (h' : Inv q E'), letI := ring E h; letI := ring E' h'; R E' h' →+* R E h
  π_ι : ∀ {E : Spc} (h : Inv q E) (k : ℕ) (a : Ht q E (2 * k) k), π h k (ι h k a) = a
  ι_one : ∀ {E : Spc} (h : Inv q E), letI := ring E h; ι h 0 ((one q E).cast (by simp) (by simp)) = 1
  ι_mul : ∀ {E : Spc} (h : Inv q E) (k l : ℕ) (a : Ht q E (2 * k) k) (b : Ht q E (2 * l) l), letI := ring E h
    ι h (k + l) ((cup q a b).cast (by push_cast; ring) (by push_cast; ring)) = ι h k a * ι h l b
  ι_cpow : ∀ {E : Spc} (h : Inv q E) (k : ℕ) (x : Ht q E 2 1), letI := ring E h
    ι h k (cpow q x k) = ι h 1 (x.cast (by simp) (by simp)) ^ k
  map_ι : ∀ {E E' : Spc} (f : E ⟶ E') (h : Inv q E) (h' : Inv q E') (k : ℕ) (a : Ht q E' (2 * k) k),
    map f h h' (ι h' k a) = ι h k (pull _ f _ _ a)
  π_map : ∀ {E E' : Spc} (f : E ⟶ E') (h : Inv q E) (h' : Inv q E') (k : ℕ) (r : R E' h'),
    π h k (map f h h' r) = pull _ f _ _ (π h' k r)

instance {q : ℕ} (P : Collected q) (E : Spc) (h : Inv q E) : CommRing (P.R E h) := P.ring E h

abbrev PB {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) : Spc := pullback V (PGL.pr N)

abbrev PB.pr {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) : PB V ⟶ E := pullback.fst V (PGL.pr N)

abbrev PB.line {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) : PB V ⟶ ofCat (glCat 1) := pullback.snd V (PGL.pr N) ≫ PGL.line N

abbrev Collected.deg1 {q : ℕ} (P : Collected q) {E : Spc} (h : Inv q E) (x : Ht q E 2 1) : P.R E h := P.ι h 1 (x.cast (by simp) (by simp))

def IsChern {q : ℕ} (P : Collected q) {E : Spc} (h : Inv q E) {N : ℕ} (V : E ⟶ ofCat (glCat N)) (c : ∀ j : ℕ, Ht q E (2 * j) j) : Prop :=
  P.ι h 0 (c 0) = 1 ∧ (∀ j, N < j → c j = 0) ∧
  ∑ j ∈ Finset.range (N + 1), P.map (PB.pr V) (inv_of (PB.pr V) h) h (P.ι h j (c j)) *
    P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ (N - j) = 0

def newton {A : Type 1} [CommRing A] (c : ℕ → A) (k : ℕ) : A :=
  PowerSeries.coeff k (-(PowerSeries.X * PowerSeries.derivative (PowerSeries.mk c)) * (PowerSeries.mk c).invOfUnit 1)

def LeafA6nat : Prop := DivisorNaturality

def LeafA6ring : Prop := DivisorRingCompatibility

def LeafA6supp : Prop := DivisorSupportCondition

def LeafRing : Prop := ∀ (q : ℕ) [NeZero q], Nonempty (Collected q)

def LeafChern : Prop := D1 → ∀ (q : ℕ) [NeZero q] (P : Collected q) {E : Spc} (h : Inv q E) {N : ℕ} (V : E ⟶ ofCat (glCat N)),
  ∃! c, IsChern P h V c

def LeafNat : Prop := ∀ (q : ℕ) [NeZero q] (P : Collected q) {E E' : Spc} (f : E ⟶ E') (h : Inv q E) (h' : Inv q E') {N : ℕ}
  (V : E' ⟶ ofCat (glCat N)) (c : ∀ j : ℕ, Ht q E' (2 * j) j), IsChern P h' V c → IsChern P h (f ≫ V) fun j => pull _ f _ _ (c j)

def LocCover {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) : Prop :=
  ∀ (n : ℕ) (X : Scheme.{0}) (x : Sx E n X), ∃ S : Sieve X, S ∈ Scheme.etaleTopology X ∧ ∀ (Y : Scheme.{0}) (k : Y ⟶ X), S.arrows k →
    (∃ y : Sx U n Y, (f.app _).app _ y = (E.obj (op (SimplexCategory.mk n))).map k.op x) ∨
    (∃ y : Sx V n Y, (g.app _).app _ y = (E.obj (op (SimplexCategory.mk n))).map k.op x)

def LeafCover2 : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Mono f → Mono g → LocCover f g → Cover2 R f g

def LeafGeom : Prop := ∀ {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)),
  ∃ (U₁ U₂ : Spc) (f₁ : U₁ ⟶ PB (bsumOf V W)) (f₂ : U₂ ⟶ PB (bsumOf V W)) (p₁ : U₁ ⟶ PB V) (p₂ : U₂ ⟶ PB W),
    Mono f₁ ∧ Mono f₂ ∧ LocCover f₁ f₂ ∧ p₁ ≫ PB.pr V = f₁ ≫ PB.pr _ ∧ p₁ ≫ PB.line V = f₁ ≫ PB.line _ ∧
    p₂ ≫ PB.pr W = f₂ ≫ PB.pr _ ∧ p₂ ≫ PB.line W = f₂ ≫ PB.line _

def LeafWhitney : Prop := ∀ (q : ℕ) [NeZero q] (P : Collected q) {E : Spc} (h : Inv q E) {a b : ℕ} (V : E ⟶ ofCat (glCat a))
  (W : E ⟶ ofCat (glCat b)) (c d : ∀ j : ℕ, Ht q E (2 * j) j), IsChern P h V c → IsChern P h W d →
  ∃ e, IsChern P h (bsumOf V W) e ∧ ∀ k, P.ι h k (e k) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, P.ι h p.1 (c p.1) * P.ι h p.2 (d p.2)

def LeafLine : Prop := ∀ (q : ℕ) [NeZero q] (P : Collected q) {E : Spc} (h : Inv q E) (L : E ⟶ ofCat (glCat 1))
  (c : ∀ j : ℕ, Ht q E (2 * j) j), IsChern P h L c → P.ι h 1 (c 1) = -P.deg1 h (c1 q L)

def LeafNewton : Prop :=
  (∀ (A B : Type 1) [CommRing A] [CommRing B] (φ : A →+* B) (c : ℕ → A), c 0 = 1 → ∀ k, φ (newton c k) = newton (fun j => φ (c j)) k) ∧
  (∀ (A : Type 1) [CommRing A] (c d e : ℕ → A), c 0 = 1 → d 0 = 1 → (∀ k, e k = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, c p.1 * d p.2) →
    ∀ k, newton e k = newton c k + newton d k) ∧
  ∀ (A : Type 1) [CommRing A] (c : ℕ → A) (x : A), c 0 = 1 → c 1 = -x → (∀ j, 1 < j → c j = 0) → ∀ k, 0 < k → newton c k = x ^ k

theorem goal_of (hR : LeafRing) (hC : LeafChern) (hN : LeafNat) (hW : LeafWhitney) (hL : LeafLine) (hS : LeafNewton) :
    LateralTheory.E.EtaleChapterDTwo := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hD q _ k hk
  classical
  obtain ⟨P⟩ := hR q
  have hE := fun {E : Spc} (h : Inv q E) {N : ℕ} (V : E ⟶ ofCat (glCat N)) => hC hD q P h V
  choose c hc hu using @hE
  refine ⟨fun {E N} V => if h : Inv q E then P.π h k (newton (fun j => P.ι h j (c h V j)) k) else 0, ?_, ?_, ?_⟩
  · intro E E' N f V h'
    have h := inv_of f h'
    simp only [dif_pos h, dif_pos h']
    rw [← hu h (f ≫ V) _ (hN q P f h h' V _ (hc h' V)), ← P.π_map f h h', hS.1 _ _ _ _ (hc h' V).1]
    simp only [P.map_ι]
  · intro E a b V W h
    simp only [dif_pos h]
    obtain ⟨e, he, hk⟩ := hW q P h V W _ _ (hc h V) (hc h W)
    rw [← hu h _ e he, hS.2.1 _ (fun j => P.ι h j (c h V j)) (fun j => P.ι h j (c h W j)) _ (hc h V).1 (hc h W).1 hk, map_add (f := _)]
  · intro E L h
    simp only [dif_pos h]
    rw [hS.2.2 _ _ _ (hc h L).1 (hL q P h L _ (hc h L)) (fun j hj => by rw [(hc h L).2.1 j hj, map_zero]) k hk,
      ← P.ι_cpow, P.π_ι]

end LateralTheory.E.D2
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.t_E1Cut

def QA (S : Type) [CommRing S] : Prop :=
  ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (π : T →+* S), AIC T ∧ Function.Surjective π

def Good (C : Type) [CommRing C] (J : Ideal C) : Prop :=
  J ≤ Ideal.jacobson ⊥ ∧ ∀ e : C ⧸ J, IsIdempotentElem e → ∃ x : C, IsIdempotentElem x ∧ Ideal.Quotient.mk J x = e

def lcMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {Y : Type} (φ : LocallyConstant (PrimeSpectrum A) Y) :
    LocallyConstant (PrimeSpectrum B) Y :=
  φ.comap ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩

def rL {S : Type} [CommRing S] (f g : S) : Localization.Away f →+* Localization.Away (f * g) :=
  IsLocalization.Away.awayToAwayRight f g

def rR {S : Type} [CommRing S] (f g : S) : Localization.Away g →+* Localization.Away (f * g) :=
  IsLocalization.Away.awayToAwayLeft g f

def Conn (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) : Prop :=
  (∀ j, j < n → Function.Bijective (pull R f F j)) ∧ Function.Injective (pull R f F n)

def Cover : Prop := ∀ (A : Type) [CommRing A], ∃ (A' : Type) (_ : CommRing A') (φ : A →+* A'),
  φ.IsIntegral ∧ Function.Surjective (PrimeSpectrum.comap φ) ∧ QA A'

def HensIdem : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (B : Type) [CommRing B] (φ : A →+* B),
  φ.IsIntegral → Good B (I.map φ)

def LCGood : Prop := ∀ (C : Type) [CommRing C] (J : Ideal C), Good C J → ∀ Y : Type,
  Function.Bijective (fun φ : LocallyConstant (PrimeSpectrum C) Y => lcMap (Ideal.Quotient.mk J) φ)

def QAClosed : Prop := ∀ (S : Type) [CommRing S], QA S →
  AIC S ∧ (∀ f : S, QA (Localization.Away f)) ∧ ∀ J : Ideal S, QA (S ⧸ J)

def EtLift : Prop := ∀ (T S C : Type) [CommRing T] [CommRing S] [CommRing C] [Algebra S C] [Algebra.Etale S C] (π : T →+* S),
  Function.Surjective π → ∃ (C' : Type) (_ : CommRing C') (_ : Algebra T C') (ρ : C' →+* C), Algebra.Etale T C' ∧
    Function.Surjective ρ ∧ ρ.comp (algebraMap T C') = (algebraMap S C).comp π ∧
    RingHom.ker ρ = (RingHom.ker π).map (algebraMap T C')

def EtAIC : Prop := ∀ (T C : Type) [CommRing T] [IsDomain T] [CommRing C] [Algebra T C] [Algebra.Etale T C], AIC T →
  ∃ (n : ℕ) (e : Fin n → C), CompleteOrthogonalIdempotents e ∧ ∀ j,
    IsOpenImmersion (Spec.map (CommRingCat.ofHom ((algebraMap C (Localization.Away (e j))).comp (algebraMap T C))))

def FinEtSection : Prop := ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Algebra.Etale S C] [Module.Finite S C], QA S →
  Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) → Nonempty (C →ₐ[S] S)

def LCSplit : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S], QA S → ∀ f g : S, Ideal.span {f, g} = ⊤ →
  ∀ φ : LocallyConstant (PrimeSpectrum (Localization.Away (f * g))) (ZMod q),
  ∃ a b, φ = lcMap (rL f g) a - lcMap (rR f g) b

def EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions : Prop := A9 → ∀ (q : ℕ) [NeZero q] (i : ℤ),
  ∃ e : ∀ (B : Type) [CommRing B], Prim q B → (LocallyConstant (PrimeSpectrum B) (ZMod q) ≃+ Ht q (sp B) 0 i),
    ∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C) (ζ : Prim q B) (φ : LocallyConstant (PrimeSpectrum B) (ZMod q)),
      pull _ (spMap f) _ _ (e B ζ φ) = e C (ζ.map f) (lcMap f φ)

def MV : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ → ∀ n : ℤ,
  (∀ c : H R (sp (Localization.Away (f * g))) F n, ∃ a b, c = pull R (spMap (rL f g)) F n a - pull R (spMap (rR f g)) F n b) →
  ∀ x : H R (sp S) F (n + 1), pull R (spMap (algebraMap S (Localization.Away f))) F _ x = 0 →
    pull R (spMap (algebraMap S (Localization.Away g))) F _ x = 0 → x = 0

def ZarLocal : Prop := B1 → B2 → ∀ (q : ℕ) (S : Type) [CommRing S], AIC S → IsUnit (q : S) → ∀ n i : ℤ, 0 < n →
  ∀ (x : Ht q (sp S) n i) (p : PrimeSpectrum S), ∃ f : S, f ∉ p.asIdeal ∧
    pull _ (spMap (algebraMap S (Localization.Away f))) _ _ x = 0

def AcycQA : Prop := A1 → A9 → B1 → B2 → ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S], QA S → IsUnit (q : S) → Acyc q (sp S)

def EqvQA : Prop := A1 → A9 → B1 → B2 → ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (J : Ideal S), QA S → Good S J →
  IsUnit (q : S) → ∀ i : ℤ, Eqv _ (spMap (Ideal.Quotient.mk J)) (tw q i)

def DescStep : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (f : E ⟶ E') (n : ℤ),
  (∀ p, Conn R (disc.map (f.app p)) F n) → Eqv R (disc.map (f.app (op (SimplexCategory.mk 0)))) F → Conn R f F (n + 1)

def CechLevels : Prop := ∀ (A A' : Type) [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A), φ.IsIntegral →
  Function.Surjective (PrimeSpectrum.comap φ) →
  (IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
    IsIntegralHom (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map))) ∧
    Surjective (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)))) ∧
  ∃ ψ : cech (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map))) ⟶
      cech (Spec.map (CommRingCat.ofHom φ)),
    ψ ≫ cechAug _ = cechAug _ ≫ spMap (Ideal.Quotient.mk I) ∧
    (∀ p, ∃ (B : Type) (_ : CommRing B) (χ : A →+* B), χ.IsIntegral ∧ Nonempty (Arrow.mk (ψ.app p) ≅
      Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map χ))))))) ∧
    Nonempty (Arrow.mk (ψ.app (op (SimplexCategory.mk 0))) ≅
      Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))))))

theorem eqv_iso (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) : Eqv R f F := fun n =>
  Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
    fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id], fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩

theorem sq (R : Type) [CommRing R] {E E' G G' : Spc} {f : E ⟶ E'} {g : G ⟶ G'} {a : E ⟶ G} {b : E' ⟶ G'} (w : f ≫ b = a ≫ g)
    {F : Shv R} (ha : Eqv R a F) (hb : Eqv R b F) (n : ℤ) :
    (Function.Bijective (pull R f F n) ↔ Function.Bijective (pull R g F n)) ∧
    (Function.Injective (pull R f F n) ↔ Function.Injective (pull R g F n)) := by
  have h : pull R f F n ∘ pull R b F n = pull R a F n ∘ pull R g F n := by
    funext x; simp only [Function.comp]; rw [← pull_comp, ← pull_comp, w]
  constructor
  · rw [← Function.Bijective.of_comp_iff _ (hb n), h, Function.Bijective.of_comp_iff' (ha n)]
  · rw [← Function.Injective.of_comp_iff' _ (hb n), h, Function.Injective.of_comp_iff (ha n).1]

theorem conn_sq (R : Type) [CommRing R] {E E' G G' : Spc} {f : E ⟶ E'} {g : G ⟶ G'} {a : E ⟶ G} {b : E' ⟶ G'} (w : f ≫ b = a ≫ g)
    {F : Shv R} (ha : Eqv R a F) (hb : Eqv R b F) (n : ℤ) : Conn R f F n ↔ Conn R g F n :=
  and_congr (forall_congr' fun j => imp_congr_right fun _ => (sq R w ha hb j).1) (sq R w ha hb n).2

theorem arr_w {P P' Q Q' : PSh} {f : P ⟶ P'} {g : Q ⟶ Q'} (e : Arrow.mk f ≅ Arrow.mk g) :
    ∃ (a : P ⟶ Q) (b : P' ⟶ Q'), IsIso a ∧ IsIso b ∧ disc.map f ≫ disc.map b = disc.map a ≫ disc.map g :=
  ⟨e.hom.left, e.hom.right, inferInstanceAs (IsIso e.hom.left), inferInstanceAs (IsIso e.hom.right), by
    rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg _ (Arrow.w e.hom).symm⟩

theorem unit_spec {A : Type} [CommRing A] {q : ℕ} (h : IsUnit (q : A)) : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

end LateralTheory.E.t_E1Cut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.CupProductRingLaws

def LeafCupSpec : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
  (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
    ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧
  ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k),
    μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def LeafTwPairExists : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ),
  ∃ μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j))), IsTwPair μ

def LeafTwPairUnique : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) (μ μ' : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j)))),
  IsTwPair μ → IsTwPair μ' → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k), μ.cup E hk = μ'.cup E hk

def LeafKumTExists : Prop := ∀ (q : ℕ) [NeZero q], ∃ t : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res _ (tw q 1)).X 0) U, IsKum q t

def IsOneCocycle (q : ℕ) (E : Spc) (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) : Prop :=
  ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev (R := ZMod q) α.1 0 0 (by simp) U x = resGen 0 ζ

def IsEtaleFirstChernClassCocycle (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) : Prop :=
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := ZMod q) γ.1 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev (R := ZMod q) γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev (R := ZMod q) γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

def LeafOneSpec : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E →
  (∃ α, IsOneCocycle q E α) ∧ ∀ α, IsOneCocycle q E α → one q E = CohomologyClass.mk α

def EtaleFirstChernClassRepresentedByChernCocycle : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  (∃ γ, IsEtaleFirstChernClassCocycle q L γ) ∧ ∀ γ, IsEtaleFirstChernClassCocycle q L γ → c1 q L = CohomologyClass.mk γ

def LeafNatCup : Prop := ∀ (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') {n m i j : ℤ} (a : Ht q E' n i) (b : Ht q E' m j),
  pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a) (pull _ f _ _ b)

def LeafNatOne : Prop := ∀ (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E'), Inv q E' → pull _ f _ _ (one q E') = one q E

def EtaleFirstChernClassNaturalUnderPullback : Prop := ∀ (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' →
  pull _ f _ _ (c1 q L) = c1 q (f ≫ L)

def LeafNatKum : Prop := ∀ (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
  pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)

def LeafRingUnit : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E →
  ∀ {n i : ℤ} (a : Ht q E n i), cup q (one q E) a = a.cast (by ring) (by ring)

def LeafRingAssoc : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l),
  cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring)

def LeafRingComm : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j),
  cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring)

end LateralTheory.E.CupProductRingLaws
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafAffCoverVanishPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

def LeafEmptyVanish : Prop := ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (F : Shv R) (n : ℤ),
  Subsingleton (H R (sch.obj (⊥ : X.Opens)) F n)

end LateralTheory.E.E8

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafConeExactPf
noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafConeExactPf

section General
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  {K L M : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ)

theorem pre_inr_eq_zero (c : Cocycle (mappingCone φ) M n) :
    CohomologyClass.mk (zcomp (Cocycle.ofHom φ) (zcomp (Cocycle.ofHom (mappingCone.inr φ)) c (zero_add n))
      (zero_add n)) = 0 := by
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • (mappingCone.inl φ).comp c.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp _ _ (show -1 + n = n - 1 by omega) 0 (n + 1) n (by omega) (by omega) (by omega)]
  simp only [Cocycle.δ_eq_zero, Cochain.comp_zero, zero_add, mappingCone.δ_inl, smul_smul,
    Int.units_mul_self, one_smul]
  apply Cochain.ext
  intro p q hpq
  simp [zcomp, Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq]

end General

end LateralTheory.E.LeafConeExactPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTwSecKillCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec

def twCls {q : ℕ} (j : ℤ) {A : CommRingCat.{0}} (ζ : Prim q A) : (twF q j).obj A :=
  Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))

def LeafOfRingsLocSurj : Prop := ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))
  (X : Scheme.{0}) (s : Sec (ofRings R M) X) (x : X), ∃ (U : Scheme.{0}) (w : U ⟶ X), Etale w ∧ x ∈ Set.range w ∧
  ∃ t : M.obj Γ(U, ⊤), Sec.res w s = ofRings.sec M U t

def LeafOfRingsLocInj : Prop := ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))
  (U : Scheme.{0}) (t : M.obj Γ(U, ⊤)), ofRings.sec M U t = 0 → ∀ u : U, ∃ (V : Scheme.{0}) (v : V ⟶ U),
  Etale v ∧ u ∈ Set.range v ∧ (M.map (Scheme.Γ.map v.op)).hom t = 0

def LeafTwAdj : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (u : U), IsUnit (q : Γ(U, ⊤)) →
  ∃ (W : Scheme.{0}) (w : W ⟶ U), Etale w ∧ u ∈ Set.range w ∧ Nonempty (Prim q Γ(W, ⊤))

def LeafTwGen : Prop := ∀ (q : ℕ) [NeZero q] (j : ℤ) (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (t : (twF q j).obj Γ(W, ⊤))
  (w0 : W), ∃ (O : W.Opens) (c : ZMod q), w0 ∈ O ∧
    ((twF q j).map (Scheme.Γ.map O.ι.op)).hom t = ((twF q j).map (Scheme.Γ.map O.ι.op)).hom (ULift.up c • twCls j ζ)

def LeafTwFieldZ : Prop := ∀ (q : ℕ) [NeZero q] (j : ℤ) (K : CommRingCat.{0}), IsField K →
  ∀ (ζ : Prim q K) (c : ZMod q), ULift.up c • twCls j ζ = 0 → c = 0

def LeafTwPt : Prop := ∀ (q : ℕ) [NeZero q] (j : ℤ) (U : Scheme.{0}) (u : U) (t : (twF q j).obj Γ(U, ⊤))
  (V : Scheme.{0}) (g : V ⟶ U) (v : V), g v = u → ((twF q j).map (Scheme.Γ.map g.op)).hom t = 0 →
  ∃ (W : Scheme.{0}) (w : W ⟶ U), Etale w ∧ u ∈ Set.range w ∧ ((twF q j).map (Scheme.Γ.map w.op)).hom t = 0

theorem sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}}
    (g : V ⟶ U) (t : M.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec M U t) = ofRings.sec M V ((M.map (Scheme.Γ.map g.op)).hom t) := by
  have h := congrArg (fun f => f.hom t) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)
  exact h.symm

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (s : Sec F U) :
    Sec.res (f ≫ g) s = Sec.res f (Sec.res g s) := by
  simp [Sec.res]

theorem sec_zero {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}) :
    ofRings.sec M U 0 = 0 :=
  map_zero _

end LateralTheory.E.E8.TwSec
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafConeZeroPf
section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafExciseCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8.ExciseCut

def relMap (q : ℕ) {Z' X' Z X : Scheme.{0}} (ι' : Z' ⟶ X') (ι : Z ⟶ X) (g : Z' ⟶ Z) (f : X' ⟶ X)
    (w : ι' ≫ f = g ≫ ι) (i n : ℤ) :
    HK (ZMod q) (mappingCone ((chains _).map (sch.map ι))) (tw q i) n →+
      HK (ZMod q) (mappingCone ((chains _).map (sch.map ι'))) (tw q i) n :=
  HK.pull (ZMod q) (mappingCone.map ((chains _).map (sch.map ι')) ((chains _).map (sch.map ι))
    ((chains _).map (sch.map g)) ((chains _).map (sch.map f)) (by simp only [← Functor.map_comp, w])) (tw q i) n

def LeafConeZero : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R),
  (∀ n, Function.Bijective (HK.pull R φ F n)) → ∀ n, Subsingleton (HK R (mappingCone φ) F n)

end LateralTheory.E.E8.ExciseCut
end
end

noncomputable section
open CategoryTheory Limits Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC Pretriangulated

namespace LateralTheory.E.E8.ExciseCut.ConeZeroPf

universe u v

theorem tri_zero {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, Functor.Additive (CategoryTheory.shiftFunctor D n)] [Pretriangulated D]
    (T : Triangle D) (hT : T ∈ distTriang D) (Y : ℤ → D) (e : ∀ n, Y n ≅ (Y (n - 1))⟦(1 : ℤ)⟧)
    (hb : ∀ n, Function.Bijective (fun g : T.obj₂ ⟶ Y n => T.mor₁ ≫ g)) (n : ℤ) (x : T.obj₃ ⟶ Y n) : x = 0 := by
  have hy : T.mor₂ ≫ x = 0 := by
    apply (hb n).1
    simp only [comp_zero, ← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, zero_comp]
  obtain ⟨g, rfl⟩ := Triangle.yoneda_exact₃ T hT x hy
  obtain ⟨h, hh⟩ := (CategoryTheory.shiftFunctor D (1 : ℤ)).map_surjective (g ≫ (e n).hom)
  obtain ⟨k, rfl⟩ := (hb (n - 1)).2 h
  have : g = (CategoryTheory.shiftFunctor D (1 : ℤ)).map (T.mor₁ ≫ k) ≫ (e n).inv := by
    rw [hh, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this, Functor.map_comp]
  simp only [← Category.assoc, comp_distTriang_mor_zero₃₁ T hT, zero_comp]

variable (R : Type) [CommRing R]

theorem pull_toHom {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (n : ℤ) (x : HK R L F n) :
    CohomologyClass.toHom (HK.pull R φ F n x) =
      (HomotopyCategory.quotient _ _).map φ ≫ CohomologyClass.toHom x := by
  obtain ⟨b, rfl⟩ := x.mk_surjective
  have : zcomp (Cocycle.ofHom φ) b (zero_add n) = b.precomp φ := by
    ext p q hpq
    simp [zcomp, Cocycle.precomp]
  change CohomologyClass.toHom (CohomologyClass.mk (zcomp (Cocycle.ofHom φ) b (zero_add n))) = _
  rw [this, CohomologyClass.toHom_mk, CohomologyClass.toHom_mk, Cocycle.equivHomShift_symm_precomp, Functor.map_comp]

theorem hb' {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (hb : ∀ n, Function.Bijective (HK.pull R φ F n)) (n : ℤ) :
    Function.Bijective (fun g : (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦n⟧) =>
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map φ ≫ g) := by
  have : (fun g : (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦n⟧) =>
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map φ ≫ g) =
      (CohomologyClass.homAddEquiv) ∘ (HK.pull R φ F n) ∘ (CohomologyClass.homAddEquiv.symm) := by
    funext g
    simp only [Function.comp_apply, CohomologyClass.homAddEquiv_apply, pull_toHom]
    congr 1
    exact (CohomologyClass.homAddEquiv.apply_symm_apply g).symm
  rw [this]
  exact CohomologyClass.homAddEquiv.bijective.comp ((hb n).comp CohomologyClass.homAddEquiv.symm.bijective)

def shIso (E : Cx R) (n : ℤ) :
    (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj (E⟦n⟧) ≅
      ((HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj (E⟦n - 1⟧))⟦(1 : ℤ)⟧ :=
  (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).mapIso
    ((CategoryTheory.shiftFunctorAdd' (CochainComplex (Shv R) ℤ) (n - 1) 1 n (by omega)).app E) ≪≫
    ((HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).app (E⟦n - 1⟧)

end LateralTheory.E.E8.ExciseCut.ConeZeroPf

open LateralTheory.E.E8.ExciseCut.ConeZeroPf in
theorem LateralTheory.E.E8.ExciseCut.LeafConeZero_of : LateralTheory.E.E8.ExciseCut.LeafConeZero := by
  intro R _ K L φ F hb n
  refine ⟨fun x y => ?_⟩
  apply (CohomologyClass.toHom_bijective _ _ _).1
  have hz := fun x : HK R (mappingCone φ) F n =>
    tri_zero (mappingCone.triangleh φ) (HomotopyCategory.mappingCone_triangleh_distinguished φ)
      (fun n => (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦n⟧))
      (shIso R (res R F)) (hb' R φ F hb) n (CohomologyClass.toHom x)
  exact (hz x).trans (hz y).symm
end
end
