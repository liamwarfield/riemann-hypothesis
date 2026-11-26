module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure HostAut (H : Host E) where

  σ : E ≃+* E
  fix : σ (H.rt : E) = H.rt

namespace HostAut

def refl (H : Host E) : HostAut H := ⟨RingEquiv.refl E, rfl⟩

def symm (g : HostAut H) : HostAut H := ⟨g.σ.symm, by rw [RingEquiv.symm_apply_eq, g.fix]⟩

def s (g : HostAut H) : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv g.σ

theorem coe_integer_automorphism (g : HostAut H) (a : 𝓞 E) : ((g.s a : 𝓞 E) : E) = g.σ (a : E) := rfl

theorem s_rt (g : HostAut H) : g.s H.rt = H.rt := RingOfIntegers.ext (by rw [coe_integer_automorphism]; exact g.fix)

theorem integer_automorphism_fixes_weight (g : HostAut H) : g.s H.w0 = H.w0 := by
  have h := congrArg g.s H.two_weight_eq_one_add_root
  rw [map_mul, map_add (f := _), map_one, s_rt, map_ofNat, ← H.two_weight_eq_one_add_root] at h
  exact mul_left_cancel₀ two_ne_zero h

theorem s_bar (g : HostAut H) (a : 𝓞 E) : g.s (H.bar a) = H.bar (g.s a) := by
  apply RingOfIntegers.ext
  show g.σ ((H.bar a : 𝓞 E) : E) = ((H.bar (g.s a) : 𝓞 E) : E)
  rw [H.bar_eq, H.bar_eq, coe_integer_automorphism]
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj]
  exact IsCMField.complexEmbedding_complexConj E (φ.comp g.σ.toRingHom) (a : E)

end HostAut

def twistAct {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct O G) (s : O ≃+* O) :
    OAct O G where
  act a := act.act (s a)
  hom a := act.hom (s a)
  one := by rw [map_one, act.one]
  mul a b := by rw [map_mul, act.mul]
  add a b := by rw [map_add (f := _), act.add]

def twistSAB {S : Scheme.{0}} (t : SAB H S) (g : HostAut H) : SAB H S where
  G := t.G
  semi := t.semi
  act := twistAct t.act g.s
  PP := t.PP
  cub := t.cub
  sym := t.sym
  adj a := by
    show LBIso _ (cubeLB t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (g.s (H.bar a))] t.PP.L)
    rw [g.s_bar]
    exact t.adj (g.s a)
  prim := by
    show LBIso _ (cubeLB t.G ![𝟙 t.G, t.act.act (g.s H.w0)] t.PP.L)
    rw [g.integer_automorphism_fixes_weight]
    exact t.prim

def TwMod {O : Type} [CommRing O] (_s : O ≃+* O) (L : Type) : Type := L

instance {O : Type} [CommRing O] (s : O ≃+* O) (L : Type) [AddCommGroup L] : AddCommGroup (TwMod s L) :=
  inferInstanceAs (AddCommGroup L)

instance {O : Type} [CommRing O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L] : Module O (TwMod s L) :=
  Module.compHom L s.toRingHom

def twForm (D : Datum H) (g : HostAut H) : LinearMap.BilinForm ℤ (TwMod g.s D.La) := D.EF

abbrev TwIso (D : Datum H) (g : HostAut H) : Type := ProIso (𝓞 E) D.EF (twForm D g)

variable {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

def TwOK (o : Obj D l b s) (g : HostAut H) (a : TwIso D g) : Prop :=
  (∀ x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), o.eta (a.a l.M x) = 1) ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), x ≫ s = spMap β →
    DetCond D (twistAct o.t.act g.s) x (β b.ρ) ∧
    ∃ I : TateIso D k (Over.mk x ⟶ o.t.G) (fun c y => y ≫ o.t.act.act (g.s c))
        (fun n y y' c => Out.WeilIs o.t.G o.t.PP.L n y y' (unitOn c)),
      (I.ζ l.A : k) = β b.ζ ∧ (∀ y, toUnit _ ≫ o.etaA (a.a l.A y) = I.ev l.A y) ∧
      ∀ y ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        toUnit _ ≫ o.eta (a.a l.M y) = I.ev l.M y

def twistObj (o : Obj D l b s) (g : HostAut H) (a : TwIso D g) (h : TwOK o g a) : Obj D l b s where
  t := twistSAB o.t g
  proper := o.proper
  ample := o.ample
  ktriv := o.ktriv
  eta x := o.eta (a.a l.M x)
  eta_add x y := by rw [map_add (f := _)]; exact o.eta_add _ _
  eta_ker := h.1
  etaA x := o.etaA (a.a l.A x)
  etaA_add x y := by rw [map_add (f := _)]; exact o.etaA_add _ _
  etaA_ker x := by rw [map_nsmul]; exact o.etaA_ker _
  geom := h.2

def twistMap {S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (g : HostAut H) :
    SABMap (twistSAB t' g) (twistSAB t g) f where
  cm := m.cm
  cart := m.cart
  base := m.base
  act c := m.act (g.s c)
  lin := m.lin

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top

structure RootFlat {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (τ : Ψ) where
  F : Type
  [field : Field F]
  [numberField : NumberField F]
  φ : F →+* M.Ω
  overInt : OverInt M.y φ
  A : HermLine M.ι
  A_smooth : IsSmoothHerm A
  S : FlatHerm M.y φ A
  deg : ∑ i, M.xdeg (τ, i) = A.a
  v : ℝ → ((Σ k, M.ι k) → ℂ) → ℝ
  v_inv : ∀ t (c : M.K → ℂ) z, (∀ k, c k ≠ 0) → v t (fun p => c p.1 * z p) = v t z
  v_smooth : ∀ t, SmoothFn (v t)
  prod : ∀ t, 0 < t → ∀ z ∈ mcPts M.P, ∏ i, (M.x t (τ, i)).h z = A.h z * Real.exp (-v t z)
  small : ∀ m : Ψ × Fin N →₀ ℕ, m.degree = dimFl Ψ N →
    Tendsto (fun t => ptsIntegral M.P (pot (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N))) (v t))
      (𝓝[>] 0) (𝓝 0)

attribute [instance] RootFlat.field RootFlat.numberField

def RootFlat.ht {Ψ : Type} [Fintype Ψ] {N : ℕ} {M : RootModel Ψ N} {τ : Ψ} (R : RootFlat M τ) : ℝ := R.S.ht

def NearRecord (N : ℕ) (bad : Finset ℕ) (rd Lval h : ℝ) : Prop :=
  ∃ (hrec : ℝ) (d v : ℕ → ℝ), |hrec| ≤ N * (3 / 2 * Real.log rd + |Lval| / 2) ∧ h = hrec + ∑ p ∈ bad, d p ∧
    (∀ p ∈ bad, 0 ≤ v p ∧ |d p| ≤ (N / ((p : ℝ) - 1) + N * v p) * Real.log p) ∧
    ∑ p ∈ bad, v p * Real.log p ≤ Real.log rd

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

def secVal {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (W : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (f : Γ(Z, W)) : B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((x.appLE W ⊤ h).hom f)

def FullTorsion (G : Over X) [GrpObj G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (n : ℕ) : Prop :=
  ∀ (k : Type) [Field k] (i : Ω →+* k) (g : Over.mk (spMap i ≫ ξ) ⟶ G), g ^ n = 1 →
    ∃ x : Over.mk ξ ⟶ G, g.left = spMap i ≫ x.left

namespace LieModel

def IsHTAt (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) (x : Over.mk ξ ⟶ G) (q : Cpt ξ)
    (w : Module.Dual Ω E) : Prop :=
  w ∈ M.omLat q ∧ ∃ (W : G.left.Opens) (f : Γ(G.left, W)), (η[G]).left q.1 ∈ W ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (xk g : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ)
      (h : ⊤ ≤ g.left ⁻¹ᵁ W), xk.left = spMap i ≫ x.left → g ^ n = 1 →
        Out.WeilIs G L n xk g (unitOn c) → secVal (B := k) g.left W h f = c) ∧
    ∀ e v, M.Extends q e v → ∀ h : ⊤ ≤ v.left ⁻¹ᵁ W, ∃ r ∈ regAt ξ q,
      w e = genMap ξ q (secVal (B := DualNumber (X.presheaf.stalk q.1)) v.left W h f).snd + n * r

def htOm (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) : Lat ξ (Module.Dual Ω E) := fun q =>
  Submodule.span (regAt ξ q) {w | ∃ x : Over.mk ξ ⟶ G, x ^ n = 1 ∧ M.IsHTAt L n x q w}

def htOmEig (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
    (σ : O →+* Ω) : Lat ξ (Module.Dual Ω (eigSp ρ σ)) :=
  (M.htOm L n).map (eigSp ρ σ).subtype.dualMap

def htDual (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
    (σ : O →+* Ω) : Lat ξ E := fun q =>
  Submodule.span (regAt ξ q) {e | e ∈ eigSp ρ σ ∧ ∀ w ∈ M.htOm L n q, w e ∈ regAt ξ q}

def htW (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
    (σ : O →+* Ω) (𝔡 : Ideal O) : Lat ξ E := fun q =>
  Submodule.span (regAt ξ q) {e | e ∈ eigSp ρ σ ∧ ∀ d ∈ 𝔡, σ d • e ∈ M.htDual L n ρ σ q}

variable (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
  (σ : O →+* Ω)

theorem htOm_le (q : Cpt ξ) : M.htOm L n q ≤ M.omLat q :=
  Submodule.span_le.2 fun _ ⟨_, _, h⟩ => h.1

theorem mem_htDual_iff (q : Cpt ξ) (e : E) :
    e ∈ M.htDual L n ρ σ q ↔ e ∈ eigSp ρ σ ∧ ∀ w ∈ M.htOm L n q, w e ∈ regAt ξ q := by
  constructor
  · intro he
    induction he using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨(eigSp ρ σ).zero_mem, fun w _ => by simpa using (regAt ξ q).zero_mem⟩
    | add x y _ _ hx hy =>
      exact ⟨(eigSp ρ σ).add_mem hx.1 hy.1, fun w hw => by
        simpa using (regAt ξ q).add_mem (hx.2 w hw) (hy.2 w hw)⟩
    | smul c x _ hx =>
      refine ⟨(eigSp ρ σ).smul_mem (c : Ω) hx.1, fun w hw => ?_⟩
      have : w (c • x) = (c : Ω) * w x := by
        show w ((c : Ω) • x) = _
        rw [map_smul, smul_eq_mul]
      rw [this]
      exact (regAt ξ q).mul_mem c.2 (hx.2 w hw)
  · exact fun h => Submodule.subset_span h

theorem mem_eigSp_of_mem_htDual {q : Cpt ξ} {e : E} (he : e ∈ M.htDual L n ρ σ q) : e ∈ eigSp ρ σ :=
  ((M.mem_htDual_iff L n ρ σ q e).1 he).1

theorem mem_htDual (q : Cpt ξ) (e : eigSp ρ σ) :
    (e : E) ∈ M.htDual L n ρ σ q ↔ ∀ u ∈ M.htOmEig L n ρ σ q, u e ∈ regAt ξ q := by
  rw [mem_htDual_iff]
  constructor
  · rintro ⟨-, h⟩ u hu
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hu
    exact h w hw
  · intro h
    refine ⟨e.2, fun w hw => ?_⟩
    exact h _ (Submodule.mem_map.2 ⟨w, hw, rfl⟩)

theorem eigLat_le_htDual (q : Cpt ξ) : M.eigLat ρ σ q ≤ M.htDual L n ρ σ q :=
  fun e he => Submodule.subset_span ⟨he.2, fun w hw => (M.htOm_le L n q hw) e he.1⟩

end LieModel


open Classical in
def Lat.patch (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) : Lat ξ E := by
  classical
  exact fun q =>
    if ∃ p ∈ S, InFibre ξ p q then ⨅ p ∈ S, ⨅ _ : InFibre ξ p q, Lp p q else L₀ q

theorem Lat.patch_empty (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) : Lat.patch ∅ L₀ Lp = L₀ := by
  funext q; simp [Lat.patch]

theorem Lat.patch_of_not (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) {q : Cpt ξ}
    (hq : ∀ p ∈ S, ¬ InFibre ξ p q) : Lat.patch S L₀ Lp q = L₀ q := by
  simp only [Lat.patch]; rw [if_neg]; rintro ⟨p, hp, h⟩; exact hq p hp h

theorem Lat.patch_of_unique (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) {q : Cpt ξ} {p : ℕ} (hp : p ∈ S)
    (hq : InFibre ξ p q) (hu : ∀ p' ∈ S, InFibre ξ p' q → p' = p) : Lat.patch S L₀ Lp q = Lp p q := by
  simp only [Lat.patch]; rw [if_pos ⟨p, hp, hq⟩]
  refine le_antisymm (iInf₂_le_of_le p hp (iInf_le _ hq)) (le_iInf₂ fun p' hp' => le_iInf fun h => ?_)
  rw [hu p' hp' h]

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.XR

open AlgebraicGeometry CategoryTheory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {Ω : Type} [Field Ω]

abbrev TateIsoAt (D : Datum H) (t : SAB H X) {k : Type} [Field k] (x : Sp k ⟶ X) : Type :=
  TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))

def IsFullLevelAt (D : Datum H) (t : SAB H X) (ξ : Sp Ω ⟶ X) (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)) :
    Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k), ∃ I : TateIsoAt D t (spMap i ≫ ξ),
    (I.ζ N : k) = i z ∧ ∀ a, (I.ev N a).left = spMap i ≫ (ev a).left

end GlobalTheory.CompanionTheory.Ar.XR
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ProjectiveLinePlaceTrivialOnConstants
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ProjectiveLinePlaces

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

theorem centre_specializes (z : Spec (CommRingCat.of R) ⟶ X) (φ : R →+* S) :
    centre (Spec.map (CommRingCat.ofHom φ) ≫ z) ⤳ centre z :=
  (IsLocalRing.specializes_closedPoint (R := R) _).map z.continuous

theorem stalk_square {x y : X} (hs : y ⤳ x) {A B : CommRingCat.{0}} (g : X.presheaf.stalk x ⟶ A)
    (g' : X.presheaf.stalk y ⟶ B) (φ : A ⟶ B)
    (h : Spec.map g' ≫ X.fromSpecStalk y = Spec.map φ ≫ Spec.map g ≫ X.fromSpecStalk x) :
    X.presheaf.stalkSpecializes hs ≫ g' = g ≫ φ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk x), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, h]

theorem genMap_specializes {x y : X} (hs : y ⤳ x) (h0 : genPt ξ ⤳ y) (h1 : genPt ξ ⤳ x)
    (s : X.presheaf.stalk x) :
    genMap ξ ⟨y, h0⟩ ((X.presheaf.stalkSpecializes hs).hom s) = genMap ξ ⟨x, h1⟩ s := by
  have h := X.presheaf.stalkSpecializes_comp h0 hs
  have h2 : X.presheaf.stalkSpecializes hs ≫ (X.presheaf.stalkSpecializes h0 ≫ Scheme.stalkClosedPointTo ξ) =
      X.presheaf.stalkSpecializes h1 ≫ Scheme.stalkClosedPointTo ξ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Scheme.stalkClosedPointTo ξ) h)
  exact congrArg (fun g => g.hom s) h2

theorem valAt_restrict {z : Spec (CommRingCat.of R) ⟶ X} (φ : R →+* S) {y : Spec (CommRingCat.of S) ⟶ X}
    (hy : Spec.map (CommRingCat.ofHom φ) ≫ z = y) (h0 : genPt ξ ⤳ centre y) {a : Ω} {r : R}
    (h : ValAt ξ z a r) : ValAt ξ y a (φ r) := by
  obtain ⟨hz, s, rfl, rfl⟩ := h
  have hs : centre y ⤳ centre z := hy ▸ centre_specializes z φ
  refine ⟨h0, (X.presheaf.stalkSpecializes hs).hom s, genMap_specializes hs h0 hz s, ?_⟩
  have key := stalk_square hs (Scheme.stalkClosedPointTo z) (Scheme.stalkClosedPointTo y)
    (CommRingCat.ofHom φ) ((Scheme.Spec_stalkClosedPointTo_fromSpecStalk y).trans (hy.symm.trans
      (congrArg (Spec.map (CommRingCat.ofHom φ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z)).symm))
  exact congrArg (fun g => g.hom s) key

theorem valAt_of_unit {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω}
    (ha : unitAt ξ ⟨centre z, h⟩ a) : ∃ r : Rˣ, ValAt ξ z a r := by
  obtain ⟨s, hs, rfl⟩ := (CptModel.unitAt_iff ξ _ a).1 ha
  obtain ⟨r, hr⟩ := hs.map (Scheme.stalkClosedPointTo z).hom
  exact ⟨r, h, s, rfl, hr.symm⟩

theorem unitAt_div {L : Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : L.IsGenAt p s) (ht : L.IsGenAt p t) :
    unitAt ξ p (s / t) := by
  have key : ∀ s t : Ω, L.IsGenAt p s → L.IsGenAt p t → s / t ∈ regAt ξ p := by
    intro s t hs ht
    have : s ∈ Submodule.span (regAt ξ p) {t} := ht.2 ▸ hs.2 ▸ Submodule.mem_span_singleton_self s
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 this
    rw [show c • t = (c : Ω) * t from rfl, mul_div_cancel_right₀ _ ht.1]
    exact c.2
  exact ⟨div_ne_zero hs.1 ht.1, key s t hs ht, by rw [inv_div]; exact key t s ht hs⟩

end General

section Line

open IsDedekindDomain Polynomial Crv.Inhab
open scoped Classical

variable (k : Type) [Field k]

end Line

section Proj

open MvPolynomial HomogeneousLocalization ProjCoord

attribute [local instance] MvPolynomial.gradedAlgebra

variable {o κ Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem valAt_pow {Y : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ Y} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ Y} {a : Ω} {r : R} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  exact ⟨hz, t ^ n, map_pow _ _ _, map_pow _ _ _⟩

end Proj

end GlobalTheory.CompanionTheory.Ar.Flat.ProjectiveLinePlaces
end
end

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

structure FibreCurve (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ϖ : Ω) where

  k : Type

  κ : Type
  [fk : Field k]
  [fκ : Field κ]
  [alg : Algebra k κ]
  fg : (⊤ : IntermediateField k κ).FG
  trdeg : Algebra.trdeg k κ = 1

  C : Crv.ACurve κ
  w_pos : ∀ i, 0 < C.w i
  triv : ∀ i (a : k), a ≠ 0 → C.v i (algebraMap k κ a) = 1
  all : ∀ W : ValuationSubring κ, W ≠ ⊤ → (∀ a : k, algebraMap k κ a ∈ W) → ∃! i, (C.v i).valuationSubring = W

  η : Spec (CommRingCat.of κ) ⟶ X
  η_spec : genPt ξ ⤳ centre η
  η_zero : ValAt ξ η ϖ 0

  z : ∀ i, Spec (CommRingCat.of (C.v i).valuationSubring) ⟶ X
  z_gen : ∀ i, Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype) ≫ z i = η

attribute [instance] FibreCurve.fk FibreCurve.fκ FibreCurve.alg

def FibreCurve.HasDeg {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ϖ : Ω} (Γ : FibreCurve ξ ϖ) (L : Lat ξ Ω) (d : ℤ) : Prop :=
  ∃ (e : Ω) (f : Γ.C.I → Ω) (r : Γ.C.I → Γ.κ), L.IsGenAt ⟨centre Γ.η, Γ.η_spec⟩ e ∧
    (∀ i, ∃ h : genPt ξ ⤳ centre (Γ.z i), L.IsGenAt ⟨centre (Γ.z i), h⟩ (f i)) ∧
    (∀ i, r i ≠ 0 ∧ ValAt ξ Γ.η (e / f i) (r i)) ∧ {i | Γ.C.v i (r i) ≠ 1}.Finite ∧
    ∑ᶠ i, (Γ.C.w i : ℤ) * (-WithZero.log (Γ.C.v i (r i))) = d

def NumTrivMod {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ Ω) (ϖ : Ω) : Prop :=
  ∀ Γ : FibreCurve ξ ϖ, Γ.HasDeg L 0

namespace FibreCurve

open ProjectiveLinePlaces

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ϖ : Ω} (Γ : FibreCurve ξ ϖ) {L L' M : Lat ξ Ω} {d d' : ℤ}

theorem generic_centre_specializes (i : Γ.C.I) : centre Γ.η ⤳ centre (Γ.z i) := by
  have := centre_specializes (Γ.z i) (Γ.C.v i).valuationSubring.subtype
  rwa [Γ.z_gen i] at this

theorem z_spec (i : Γ.C.I) : genPt ξ ⤳ centre (Γ.z i) := Γ.η_spec.trans (Γ.generic_centre_specializes i)

theorem exists_val_of_unitAt (i : Γ.C.I) {a : Ω} (ha : unitAt ξ ⟨centre (Γ.z i), Γ.z_spec i⟩ a) :
    ∃ t : Γ.κ, ValAt ξ Γ.η a t ∧ Γ.C.v i t = 1 := by
  obtain ⟨t, ht⟩ := valAt_of_unit _ ha
  refine ⟨_, valAt_restrict _ (Γ.z_gen i) Γ.η_spec ht, ?_⟩
  have a1 : Γ.C.v i ((Γ.C.v i).valuationSubring.subtype t) ≤ 1 := t.1.2
  have a2 : Γ.C.v i ((Γ.C.v i).valuationSubring.subtype ↑t⁻¹) ≤ 1 := (t⁻¹).1.2
  have a3 : Γ.C.v i ((Γ.C.v i).valuationSubring.subtype t) *
      Γ.C.v i ((Γ.C.v i).valuationSubring.subtype ↑t⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm a1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := a3.symm
    _ ≤ _ * 1 := by gcongr
    _ = _ := mul_one _

variable {Γ}

variable (Γ)

theorem hasDeg_zero_of_gen {e : Ω} (he : L.IsGenAt ⟨centre Γ.η, Γ.η_spec⟩ e)
    (hf : ∀ i, L.IsGenAt ⟨centre (Γ.z i), Γ.z_spec i⟩ e) : Γ.HasDeg L 0 :=
  ⟨e, fun _ => e, fun _ => 1, he, fun i => ⟨_, hf i⟩,
    fun _ => ⟨one_ne_zero, Γ.η_spec, 1, by rw [map_one, div_self he.1], map_one _⟩, by simp, by simp⟩

end FibreCurve

theorem numTrivMod_of_gen {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Lat ξ Ω} {e : Ω} (he : ∀ p, L.IsGenAt p e)
    (ϖ : Ω) : NumTrivMod L ϖ := fun Γ => Γ.hasDeg_zero_of_gen (he _) fun _ => he _

end General

namespace FibLine

open ProjectiveLinePlaces Crv.Inhab

section Proj

open MvPolynomial HomogeneousLocalization ProjCoord

attribute [local instance] MvPolynomial.gradedAlgebra

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

end Proj

attribute [local instance] MvPolynomial.gradedAlgebra

end FibLine

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
