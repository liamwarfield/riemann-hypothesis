module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PreUniformisationComparisonTorusInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PreUniformisationComparisonTorusInvariant
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory

namespace PreTorusInvariance

theorem cube_alg {V : Type} [CommGroup V] {A : Type} [CommGroup A] {a W W' d : A → V} (h : ∀ x, a x * W' x = W x * d x)
    {x y u : A} {C C' c c' : V}
    (h₁ : C * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * c)
    (h₂ : C' * W' (x * y) * W' (x * u) * W' (y * u) * W' 1 = W' (x * y * u) * W' x * W' y * W' u * c')
    (h₃ : c * d (x * y) * d (x * u) * d (y * u) * d 1 = d (x * y * u) * d x * d y * d u * c') :
    C = a (x * y * u) * (a (x * y))⁻¹ * (a (x * u))⁻¹ * (a (y * u))⁻¹ * a x * a y * a u * (a 1)⁻¹ * C' := by
  have E := fun {p q : V} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E h₁; have a₂ := E h₂; have a₃ := E h₃
  have b₁ := E (h (x * y * u)); have b₂ := E (h (x * y)); have b₃ := E (h (x * u)); have b₄ := E (h (y * u))
  have b₅ := E (h x); have b₆ := E (h y); have b₇ := E (h u); have b₈ := E (h 1)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at *
  linear_combination (norm := abel) a₁ - a₂ + a₃ - b₁ + b₂ + b₃ + b₄ - b₅ - b₆ - b₇ + b₈

theorem even_alg {V : Type} [CommGroup V] {A : Type} [CommGroup A] {a W W' d : A → V} (h : ∀ x, a x * W' x = W x * d x)
    {x : A} {s s' c c' : V} (h₁ : s * W x = W x⁻¹ * c) (h₂ : s' * W' x = W' x⁻¹ * c') (h₃ : c * d x = d x⁻¹ * c') :
    s * a x = a x⁻¹ * s' := by
  have E := fun {p q : V} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E h₁; have a₂ := E h₂; have a₃ := E h₃
  have b₁ := E (h x); have b₂ := E (h x⁻¹)
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at *
  linear_combination (norm := abel) a₁ - a₂ + a₃ + b₁ - b₂

theorem vals_id {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P P' : CP G}
    {w : LB.Iso P'.L.L (P.L.L.pull (𝟙 G.left))} {hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _}
    (h : IsCPMap P' P (𝟙 _) (𝟙 G.left) hw w) {T : Over S} {z : T.left} {N N'} (hN : Good P.L.L z N)
    (hN' : Good P'.L.L z N') (d : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ)
    (hd : ∀ x, d x = gw w x.left z (N x.left) (N' x.left)) {B : Type} [CommGroup B] (β : B →* (T ⟶ G)) :
    (∀ x, val P.sym (β x).left z N * d (β x) = d (β x⁻¹) * val P'.sym (β x).left z N') ∧
    ∀ x y u, cubV P.c z N (β x) (β y) (β u) * d (β (x * y)) * d (β (x * u)) * d (β (y * u)) * d (β 1) =
      d (β (x * y * u)) * d (β x) * d (β y) * d (β u) * cubV P'.c z N' (β x) (β y) (β u) := by
  obtain ⟨-, s, c⟩ := h.vals T z N' N hN' hN d (fun x => by rw [hd, Category.comp_id])
  refine ⟨fun x => ?_, fun x y u => ?_⟩
  · have s := s (β x)
    rwa [Category.comp_id, ← map_inv] at s
  · have c := c (β x) (β y) (β u)
    rw [_root_.id, cubV_toBase_id] at c
    simp only [map_mul, map_one]
    exact c

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] {e : ℕ} {D D' : DegPre R} {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {U : PreU I D A G} {U' : PreU I D' A' G}

def cubP (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (x y u : T ⟶ thickObj R I e G) : (T.left.presheaf.stalk z)ˣ :=
  cubV D.cub (T := (Over.map (thick R I e)).obj T) z J
    ((Over.map (thick R I e)).map x ≫ g.pG) ((Over.map (thick R I e)).map y ≫ g.pG)
    ((Over.map (thick R I e)).map u ≫ g.pG)

theorem cubP_congr (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) {a b a' b' : T ⟶ thickObj R I e G} (c : T ⟶ thickObj R I e G)
    (ha : a ≫ g.q = a' ≫ g.q) (hb : b ≫ g.q = b' ≫ g.q) : cubP g z J a b c = cubP g z J a' b' c := by
  have k : ∀ {a a' : T ⟶ thickObj R I e G}, a ≫ g.q = a' ≫ g.q →
      (Over.map (thick R I e)).map a ≫ g.pG = (Over.map (thick R I e)).map a' ≫ g.pG := fun h =>
    Over.OverMorphism.ext (TorusInvariance.pG_congr g h)
  unfold cubP
  rw [k ha, k hb]

theorem vals (u : LB.Iso (D'.P.L.pull (U'.gt e).pG.left) (D.P.L.pull (U.gt e).pG.left))
    {wL : LB.Iso U'.P.L.L (U.P.L.L.pull (𝟙 G.left))} {hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _}
    (hL : IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL)
    (sq : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι)
      (jL : U.P.L.L.ι) (jL' : U'.P.L.L.ι), (U.gt e).pG.left (r z) ∈ D.P.L.U jM →
      (U'.gt e).pG.left (r z) ∈ D'.P.L.U jM' → (fstG I e G).left (r z) ∈ U.P.L.L.U jL →
      (fstG I e G).left (r z) ∈ U'.P.L.L.U jL' →
      gw u r z jM (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') =
        gw (U.w e) r z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL')
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι}
    {J' : (T.left ⟶ D'.P.A.left) → D'.P.L.ι} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (a : (T.left ⟶ (thickObj R I e G).left) → (T.left.presheaf.stalk z)ˣ)
    (ha : ∀ r, a r = gw u r z (J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left))) :
    (∀ x : T ⟶ thickObj R I e G, val D.sym (x.left ≫ (U.gt e).pG.left) z J * a x.left =
      a (x⁻¹).left * val D'.sym (x.left ≫ (U'.gt e).pG.left) z J') ∧
    ∀ x y v : T ⟶ thickObj R I e G, cubP (U.gt e) z J x y v =
      a (x * y * v).left * (a (x * y).left)⁻¹ * (a (x * v).left)⁻¹ * (a (y * v).left)⁻¹ * a x.left * a y.left *
        a v.left * (a (1 : T ⟶ thickObj R I e G).left)⁻¹ * cubP (U'.gt e) z J' x y v := by
  obtain ⟨N, hN⟩ := exists_good_pt U.P.L.isLB z
  obtain ⟨N', hN'⟩ := exists_good_pt U'.P.L.isLB z
  obtain ⟨W, hW⟩ : ∃ W : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ, ∀ x, W x =
    gw (U.w e) x.left z (J (x.left ≫ (U.gt e).pG.left)) (fun _ => N (x.left ≫ (fstG I e G).left)) := ⟨_, fun _ => rfl⟩
  obtain ⟨W', hW'⟩ : ∃ W : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ, ∀ x, W x =
    gw (U'.w e) x.left z (J' (x.left ≫ (U'.gt e).pG.left)) (fun _ => N' (x.left ≫ (fstG I e G).left)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ((Over.map (thick R I e)).obj T ⟶ G) → (T.left.presheaf.stalk z)ˣ, ∀ x, d x =
    gw wL x.left z (N x.left) (N' x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨-, s₁, c₁⟩ := U.w_vals e T z N J hN hJ W hW
  obtain ⟨-, s₂, c₂⟩ := U'.w_vals e T z N' J' hN' hJ' W' hW'
  let β : (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
    MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ fstG I e G) fun x y =>
      toBase_mul_pullback G (thick R I e) T x y
  obtain ⟨s₃, c₃⟩ := vals_id hL (T := (Over.map (thick R I e)).obj T) hN hN' d hd β
  have h : ∀ x : T ⟶ thickObj R I e G, a x.left * W' x = W x * d (β x) := fun x => by
    rw [ha, hW, hW', hd]
    exact sq _ x.left z _ _ _ _ (hJ _) (hJ' _) (hN _) (hN' _)
  refine ⟨fun x => ?_, fun x y v => ?_⟩
  · exact even_alg (a := fun x => a x.left) (d := fun x => d (β x)) h (s₁ x) (s₂ x) (s₃ x)
  · obtain ⟨c, hc⟩ : ∃ c : (T.left.presheaf.stalk z)ˣ,
      c = cubV U.P.c (T := (Over.map (thick R I e)).obj T) z N (β x) (β y) (β v) := ⟨_, rfl⟩
    obtain ⟨c', hc'⟩ : ∃ c : (T.left.presheaf.stalk z)ˣ,
      c = cubV U'.P.c (T := (Over.map (thick R I e)).obj T) z N' (β x) (β y) (β v) := ⟨_, rfl⟩
    have k₁ : cubP (U.gt e) z J x y v * W (x * y) * W (x * v) * W (y * v) * W 1 =
      W (x * y * v) * W x * W y * W v * c := (c₁ x y v).trans (congrArg (_ * ·) hc.symm)
    have k₂ : cubP (U'.gt e) z J' x y v * W' (x * y) * W' (x * v) * W' (y * v) * W' 1 =
      W' (x * y * v) * W' x * W' y * W' v * c' := (c₂ x y v).trans (congrArg (_ * ·) hc'.symm)
    have k₃ : c * d (β (x * y)) * d (β (x * v)) * d (β (y * v)) * d (β 1) =
        d (β (x * y * v)) * d (β x) * d (β y) * d (β v) * c' := by
      rw [hc, hc']; exact c₃ x y v
    have k := cube_alg (A := T ⟶ thickObj R I e G) (a := fun x => a x.left) (d := fun x => d (β x)) h k₁ k₂ k₃
    exact k

end PreTorusInvariance


open TorusInvariance PreTorusInvariance in
set_option maxHeartbeats 400000 in
theorem preU_comparison_torus_invariant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D D' : DegPre R) (A A' : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (U' : PreU I D' A' G) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull (𝟙 G.left))) (hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _), IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL → ∀ (e : ℕ) (β : thickObj R I e D'.P.A ≅ thickObj R I e D.P.A), (U'.gt e).q ≫ β.hom = (U.gt e).q → ∀ u : LB.Iso (D'.P.L.pull (U'.gt e).pG.left) (D.P.L.pull (U.gt e).pG.left), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι) (jL : U.P.L.L.ι) (jL' : U'.P.L.L.ι), (U.gt e).pG.left (r z) ∈ D.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.P.L.U jM' → (fstG I e G).left (r z) ∈ U.P.L.L.U jL → (fstG I e G).left (r z) ∈ U'.P.L.L.U jL' → gw u r z jM (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') = gw (U.w e) r z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL') → ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.X) (y : Z ⟶ thickObj R I e G) (z : Z.left) (jM : D.P.L.ι) (jM' : D'.P.L.ι), (U.gt e).pG.left (y.left z) ∈ D.P.L.U jM → (U'.gt e).pG.left (y.left z) ∈ D'.P.L.U jM' → gw u ((τ ≫ (U.gt e).i) * y).left z jM (fun _ => jM') = gw u y.left z jM (fun _ => jM') := by
  intro R _ _ _ I D D' A A' G _ _ U U' wL hw hL e β hβ u hu sq Z₀ τ₀ y₀ z₀ jM jM' m m'
  have := (U.gt e).q_hom
  have := (U'.gt e).q_hom
  have := (U.gt e).i_hom
  have := U.semi.geomConnected
  have := connectedSpace_spec_quotient (I ^ (e + 1)) (Z₀.hom z₀)
  have : GeometricallyConnected (thickObj R I e G).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (thick R I e)))
  have : ConnectedSpace (thickObj R I e G).left :=
    GroupConn.connectedSpace_of_section (thickObj R I e G).hom (η : 𝟙_ _ ⟶ thickObj R I e G).left (Over.w _)
  have hq : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.X),
      (τ ≫ (U.gt e).i) ≫ (U.gt e).q = (1 : Z ⟶ thickObj R I e G) ≫ (U.gt e).q := fun τ => by
    rw [Category.assoc, (U.gt e).isKernel.w, MonObj.one_comp, ← Category.assoc, comp_toUnit, Hom.one_def]
  have hq' : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.X),
      (τ ≫ (U.gt e).i) ≫ (U'.gt e).q = (1 : Z ⟶ thickObj R I e G) ≫ (U'.gt e).q := fun τ => by
    rw [← cancel_mono β.hom, Category.assoc _ _ β.hom, Category.assoc _ _ β.hom, hβ]
    exact hq τ
  have hp : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.X)
      (y : Z ⟶ thickObj R I e G), ((τ ≫ (U.gt e).i) * y).left ≫ (U.gt e).pG.left = y.left ≫ (U.gt e).pG.left :=
    fun τ y => pG_congr _ (by rw [MonObj.mul_comp, hq, ← MonObj.mul_comp, _root_.one_mul])
  have hp' : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.X)
      (y : Z ⟶ thickObj R I e G), ((τ ≫ (U.gt e).i) * y).left ≫ (U'.gt e).pG.left = y.left ≫ (U'.gt e).pG.left :=
    fun τ y => pG_congr _ (by rw [MonObj.mul_comp, hq', ← MonObj.mul_comp, _root_.one_mul])
  obtain ⟨ρ, key⟩ := exists_ratio_translate (U.gt e).i D.P.isLB D'.P.isLB u hu (fun _ => hp) (fun _ => hp')
  have triv := ratio_eq_one (U.gt e).i ρ (fun Z z => by
    obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
    obtain ⟨J', hJ'⟩ := exists_good_pt D'.P.isLB z
    obtain ⟨a, ha⟩ : ∃ a : (Z.left ⟶ (thickObj R I e G).left) → (Z.left.presheaf.stalk z)ˣ,
      ∀ r, a r = gw u r z (J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left)) := ⟨_, fun _ => rfl⟩
    obtain ⟨s, c⟩ := vals u hL sq hJ hJ' a ha
    refine ⟨a, fun t y => ?_, fun t t' y => ?_, fun t => ?_⟩
    · rw [ha, ha, hp, hp']
      exact key Z t y z _ _ (hJ _) (hJ' _)
    · have p := c (t ≫ (U.gt e).i) (t' ≫ (U.gt e).i) y
      have q := c 1 1 y
      rw [cubP_congr (U.gt e) z J y (hq t) (hq t'), cubP_congr (U'.gt e) z J' y (hq' t) (hq' t')] at p
      rw [prod_psum, prod_psum]
      exact mul_right_cancel (p.symm.trans q)
    · have p := s (t ≫ (U.gt e).i)
      have q := s 1
      rw [pG_congr (U.gt e) (hq t), pG_congr (U'.gt e) (hq' t)] at p
      exact cancel_even p q)
  rw [key Z₀ τ₀ y₀ z₀ jM jM' m m', triv, map_one, _root_.one_mul]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PreUniformisationComparisonTorusInvariantStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preUniformisation_comparison_torus_invariant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D D' : DegPre R) (A A' : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (U' : PreU I D' A' G) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull (𝟙 G.left))) (hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _), IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL → ∀ (e : ℕ) (β : thickObj R I e D'.P.A ≅ thickObj R I e D.P.A), (U'.gt e).q ≫ β.hom = (U.gt e).q → ∀ u : LB.Iso (D'.P.L.pull (U'.gt e).pG.left) (D.P.L.pull (U.gt e).pG.left), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι) (jL : U.P.L.L.ι) (jL' : U'.P.L.L.ι), (U.gt e).pG.left (r z) ∈ D.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.P.L.U jM' → (fstG I e G).left (r z) ∈ U.P.L.L.U jL → (fstG I e G).left (r z) ∈ U'.P.L.L.U jL' → gw u r z jM (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') = gw (U.w e) r z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL') → ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.X) (y : Z ⟶ thickObj R I e G) (z : Z.left) (jM : D.P.L.ι) (jM' : D'.P.L.ι), (U.gt e).pG.left (y.left z) ∈ D.P.L.U jM → (U'.gt e).pG.left (y.left z) ∈ D'.P.L.U jM' → gw u ((τ ≫ (U.gt e).i) * y).left z jM (fun _ => jM') = gw u y.left z jM (fun _ => jM') := by
  first | exact @GlobalTheory.preU_comparison_torus_invariant | exact GlobalTheory.preU_comparison_torus_invariant | (intros; apply GlobalTheory.preU_comparison_torus_invariant <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.PreUnique

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R}
  {A A' : PolAV (Sp (FractionRing R))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_beta [IsLocalRing R] [IsNoetherianRing R] (hI : I ≠ ⊤) {e : ℕ} (g : GtCoord I D e G)
    (g' : GtCoord I D' e G) :
    ∃ β : thickObj R I e D'.P.A ≅ thickObj R I e D.P.A, IsMonHom β.hom ∧ g'.q ≫ β.hom = g.q := by
  have := g.q_affine
  have := g'.q_affine
  exact flatQuotient_iso_of_same_kernel _ _ _ _ _ _ g.q g.i g'.q g'.i g.q_hom g.i_hom g.q_flat g.q_surj
    inferInstance g.isKernel g'.q_hom g'.i_hom g'.q_flat g'.q_surj inferInstance g'.isKernel
    (gtCoord_i_comp_q hI _ _) (gtCoord_i_comp_q hI _ _)

variable (U : PreU I D A G) (U' : PreU I D' A' G)


open CharAgree in
theorem match_down {e : ℕ} {f : D'.X → D.X}
    (h : CharAgree.Match (U.gt (e + 1)) (U'.gt (e + 1)) f) : CharAgree.Match (U.gt e) (U'.gt e) f := by
  intro Z r z J J' hJ hJ' c c' x
  have t : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have up : ∀ {Y : Scheme.{0}} (p : (thickObj R I (e + 1) G).left ⟶ Y)
      (p₀ : (thickObj R I e G).left ⟶ Y) (s : G.left ⟶ Y), thickMap R I e G ≫ p = p₀ →
      r ≫ p₀ = r ≫ (fstG I e G).left ≫ s →
      (r ≫ thickMap R I e G) ≫ p = (r ≫ thickMap R I e G) ≫ (fstG I (e + 1) G).left ≫ s := by
    intro Y p p₀ s h₁ h₂
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) h₁).trans (h₂.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ s) t.symm).trans (Category.assoc _ _ _)
  have k := h Z (r ≫ thickMap R I e G) z J J' hJ hJ' (up _ _ _ (U.gt_q e) c)
    (up _ _ _ (U'.gt_q e) c') x
  exact (val_corr hJ (U.gt_t e (f x)) r).symm.trans ((val_pull hJ _ _ _).trans (k.trans
    ((val_pull hJ' _ _ _).symm.trans (val_corr hJ' (U'.gt_t e x) r))))


open CharAgree in
theorem exists_xe [IsLocalRing R] [IsNoetherianRing R] (hI : I ≠ ⊤) :
    ∃ xe : D'.X ≃+ D.X, ∀ e, CharAgree.Match (U.gt e) (U'.gt e) xe := by
  choose xe hxe using fun e => exists_match hI (U.gt e) (U'.gt e)
  have down : ∀ (e : ℕ) (f : D'.X → D.X), CharAgree.Match (U.gt e) (U'.gt e) f →
      CharAgree.Match (U.gt 0) (U'.gt 0) f := by
    intro e f
    induction e with
    | zero => exact id
    | succ e ih => exact fun h => ih (PreUnique.match_down U U' h)
  refine ⟨xe 0, fun e => ?_⟩
  have h := hxe e
  rw [match_unique hI _ _ (down e _ h) (hxe 0)] at h
  exact h

theorem trans_comp_q (e : ℕ) :
    thickMap R I e G ≫ (U.gt (e + 1)).q.left = (U.gt e).q.left ≫ thickMap R I e D.P.A := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((U.gt_q e).trans
      ((congrArg ((U.gt e).q.left ≫ ·) (UnifCompare.trans_comp_proj e D.P.A).symm).trans
        (Category.assoc _ _ _).symm))
  · have h₁ : (U.gt (e + 1)).q.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (U.gt (e + 1)).q
    have h₀ : (U.gt e).q.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (U.gt e).q
    have k : ∀ B : Over (Spec (CommRingCat.of R)), thickMap R I e B ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ thickTrans R I e := fun B => pullback.lift_snd _ _ _
    exact (Category.assoc _ _ _).trans ((congrArg (thickMap R I e G ≫ ·) h₁).trans ((k G).trans
      ((congrArg (· ≫ thickTrans R I e) h₀.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg ((U.gt e).q.left ≫ ·) (k _).symm).trans (Category.assoc _ _ _).symm)))))

theorem gw_trans (e : ℕ) (y : (thickObj R I e G).left) (jM : D.P.L.ι) (jL : U.P.L.L.ι)
    (hM : (U.gt e).pG.left y ∈ D.P.L.U jM) (hL : (fstG I e G).left y ∈ U.P.L.L.U jL) :
    gw (U.w (e + 1)) (thickMap R I e G) y jM (fun _ => jL) = gw (U.w e) (𝟙 _) y jM (fun _ => jL) := by
  have := U.w_compat e _ (𝟙 _) y jM jL hM hL
  rwa [Category.id_comp] at this

variable (wL : LB.Iso U'.P.L.L (U.P.L.L.pull (𝟙 G.left))) {hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _}

theorem exists_level [IsLocalRing R] (hwL : IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL) (e : ℕ)
    (β : thickObj R I e D'.P.A ≅ thickObj R I e D.P.A) (hq : (U'.gt e).q ≫ β.hom = (U.gt e).q) :
    ∃ v : LB.Iso (D'.P.L.pull (fstG I e D'.P.A).left) (D.P.L.pull (β.hom.left ≫ (fstG I e D.P.A).left)), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι)
      (jL : U.P.L.L.ι) (jL' : U'.P.L.L.ι), (U.gt e).pG.left (r z) ∈ D.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.P.L.L.U jL → (fstG I e G).left (r z) ∈ U'.P.L.L.U jL' →
      gw v (r ≫ (U'.gt e).q.left) z jM (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') =
        gw (U.w e) r z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL' := by
  obtain ⟨u, hu, hu'⟩ := LevelComparison.exists_comparison D.P.isLB D'.P.isLB U.P.L.isLB U'.P.L.isLB
    (U.w_gen e) (U'.w_gen e) hwL.gen
  have inv := GlobalTheory.T.preUniformisation_comparison_torus_invariant R I D D' A A' G U U' wL hw hwL e β hq u hu hu'
  haveI := (U'.gt e).q_flat
  haveI := (U'.gt e).q_surj
  haveI := (U'.gt e).q_affine
  haveI := (U.gt e).q_hom
  have hql : (U'.gt e).q.left ≫ β.hom.left = (U.gt e).q.left := congrArg (·.left) hq
  obtain ⟨v, hv, hv'⟩ := LevelComparison.exists_iso_descend (U'.gt e).q.left (fstG I e D'.P.A).left
    (β.hom.left ≫ (fstG I e D.P.A).left) (p := (U.gt e).pG.left) (p' := (U'.gt e).pG.left)
    (by rw [← Category.assoc, hql]; rfl) rfl u hu (fun Z g₁ g₂ z j j' h a b => by
      let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (g₂ ≫ (thickObj R I e G).hom)
      let k₂ : Z' ⟶ thickObj R I e G := Over.homMk g₂ rfl
      let k₁ : Z' ⟶ thickObj R I e G := Over.homMk g₁ (by
        change g₁ ≫ (thickObj R I e G).hom = g₂ ≫ (thickObj R I e G).hom
        rw [← Over.w (U'.gt e).q, reassoc_of% h])
      have e₁ : k₁ ≫ (U'.gt e).q = k₂ ≫ (U'.gt e).q := Over.OverMorphism.ext h
      have e' : k₁ ≫ (U.gt e).q = k₂ ≫ (U.gt e).q := by rw [← hq, reassoc_of% e₁]
      have w : (k₁ * k₂⁻¹) ≫ (U.gt e).q = toUnit Z' ≫ η[thickObj R I e D.P.A] := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, e', mul_inv_cancel]
        rfl
      have ht : ((U.gt e).isKernel.lift _ _ w ≫ (U.gt e).i) * k₂ = k₁ := by
        rw [(U.gt e).isKernel.lift_fst, inv_mul_cancel_right]
      have := inv Z' ((U.gt e).isKernel.lift _ _ w) k₂ z j j' a b
      rw [ht] at this
      exact this)
  refine ⟨v, hv, fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  rw [← hu' Z r z jM jM' jL jL' a₁ a₂ a₃ a₄]
  exact congrArg (· * _) (hv' Z r z jM jM' a₁ a₂)


open UnifCompare hiding trans_comp_q gw_trans in
theorem exists_iso [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete I R] (hI : I ≠ ⊤) (hS : SecBaseChangeSt)
    (hA : AmpleSt) (hwL : IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL) :
    ∃ (Φ : D'.P.A ≅ D.P.A) (w : LB.Iso D'.P.L (D.P.L.pull Φ.hom.left)), w.IsGen ∧ ∀ e : ℕ,
      (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι)
      (jL : U.P.L.L.ι) (jL' : U'.P.L.L.ι), (U.gt e).pG.left (r z) ∈ D.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.P.L.L.U jL → (fstG I e G).left (r z) ∈ U'.P.L.L.U jL' →
      gw w (r ≫ (U'.gt e).pG.left) z jM jM' * gw (U'.w e) r z jM' (fun _ => jL') =
        gw (U.w e) r z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL' := by
  choose β hβm hβ using fun e => exists_beta hI (U.gt e) (U'.gt e)
  choose v hvg hv using fun e => exists_level U U' wL hwL e (β e) (hβ e)
  have hβl : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left = (U.gt e).q.left := fun e =>
    congrArg (·.left) (hβ e)
  have hp : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left ≫ (fstG I e D.P.A).left =
      (U.gt e).pG.left := fun e =>
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (fstG I e D.P.A).left) (hβl e))
  have hc : ∀ e, thickMap R I e D'.P.A ≫ (β (e + 1)).hom.left =
      (β e).hom.left ≫ thickMap R I e D.P.A := by
    intro e
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have : Epi (U'.gt e).q.left := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (U'.gt e).q.left, ← Category.assoc, ← trans_comp_q, Category.assoc, hβl,
      trans_comp_q, ← Category.assoc, hβl]
  obtain ⟨Φ, w, hw, H⟩ := exists_iso_of_compatible_thickenings hS hA R I D.P D'.P β v hvg hc (by
    intro e Z r z j j' hj hj'
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have hm : ∀ y : (thickObj R I e D'.P.A).left,
        y ∈ (D.P.L.pull ((β e).hom.left ≫ (fstG I e D.P.A).left)).U (fun _ => j) ⊓
          (D'.P.L.pull (fstG I e D'.P.A).left).U (fun _ => j') →
        thickMap R I e D'.P.A y ∈
          (D.P.L.pull ((β (e + 1)).hom.left ≫ (fstG I (e + 1) D.P.A).left)).U (fun _ => j) ⊓
          (D'.P.L.pull (fstG I (e + 1) D'.P.A).left).U (fun _ => j') := by
      intro y hy
      have k : thickMap R I e D'.P.A ≫ (β (e + 1)).hom.left ≫ (fstG I (e + 1) D.P.A).left =
          (β e).hom.left ≫ (fstG I e D.P.A).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I (e + 1) D.P.A).left) (hc e)).trans
          ((Category.assoc _ _ _).trans (congrArg ((β e).hom.left ≫ ·) (trans_comp_proj e _))))
      exact ⟨mem_pull.2 ((congrArg (fun g => g y ∈ D.P.L.U j) k).mpr (mem_pull.1 hy.1)),
        mem_pull.2 ((congrArg (fun g => g y ∈ D'.P.L.U j') (trans_comp_proj e _)).mpr
          (mem_pull.1 hy.2))⟩
    have hz : r z ∈ (D.P.L.pull ((β e).hom.left ≫ (fstG I e D.P.A).left)).U (fun _ => j) ⊓
          (D'.P.L.pull (fstG I e D'.P.A).left).U (fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    refine (gm_pull r _ z _ (hm _ hz) _).symm.trans
      (gm_eq_of_flat_surjective (U'.gt e).q.left _ _ (fun x _ hx => ?_) r z (hm _ hz) hz)
    refine (gm_pull _ _ x _ (hm _ hx) _).trans ?_
    obtain ⟨jL, hL⟩ := exists_chart U.P.L.isLB ((fstG I e G).left x)
    obtain ⟨jL', hL'⟩ := exists_chart U'.P.L.isLB ((fstG I e G).left x)
    have hM : (U.gt e).pG.left x ∈ D.P.L.U j :=
      (congrArg (fun g => g x ∈ D.P.L.U j) (hp e)).mp (mem_pull.1 hx.1)
    have hM' : (U'.gt e).pG.left x ∈ D'.P.L.U j' := mem_pull.1 hx.2
    have h₀ := hv e _ (𝟙 _) x j j' jL jL' hM hM' hL hL'
    have h₁ := hv (e + 1) _ (thickMap R I e G) x j j' jL jL'
      ((congrArg (fun g => g x ∈ D.P.L.U j) (U.gt_q e)).mpr hM)
      ((congrArg (fun g => g x ∈ D'.P.L.U j') (U'.gt_q e)).mpr hM')
      ((congrArg (fun g => g x ∈ U.P.L.L.U jL) (trans_comp_proj e G)).mpr hL)
      ((congrArg (fun g => g x ∈ U'.P.L.L.U jL') (trans_comp_proj e G)).mpr hL')
    rw [gw_trans U' e x j' jL' hM' hL', gw_trans U e x j jL hM hL, trans_comp_q, trans_comp_proj] at h₁
    rw [Category.id_comp, Category.id_comp] at h₀
    exact mul_right_cancel (h₁.trans h₀.symm))
  refine ⟨Φ, w, hw, fun e => ⟨?_, fun Z r z jM jM' jL jL' hM hM' hL hL' => ?_⟩⟩
  · exact (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) (H e).1).trans (hp e))
  · have h := (H e).2 Z (r ≫ (U'.gt e).q.left) z jM jM'
      ((congrArg (fun g => g (r z) ∈ D.P.L.U jM) (hp e)).mpr hM) hM'
    rw [Category.assoc] at h
    exact (congrArg (· * _) h).trans (hv e Z r z jM jM' jL jL' hM hM' hL hL')

theorem isMonHom_of_pG [IsNoetherianRing R] [IsAdicComplete I R] (Φ : D'.P.A ≅ D.P.A)
    (H : ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) : IsMonHom Φ.hom := by
  refine AbelianPartIso.isMonHom_of_thickenings (IsAdicComplete.le_jacobson_bot I) D.P.isAb D'.P.isAb Φ.hom fun e => ?_
  have := (U.gt e).q_hom
  have := (U'.gt e).q_hom
  have := (U'.gt e).q_flat
  have := (U'.gt e).q_surj
  refine AbelianPartIso.isMonHom_of_comp (U'.gt e).q (U.gt e).q _ (Over.OverMorphism.ext ?_)
  refine pullback.hom_ext ?_ ?_
  · have k : ((Over.pullback (thick R I e)).map Φ.hom).left ≫
        pullback.fst D.P.A.hom (thick R I e) =
        pullback.fst D'.P.A.hom (thick R I e) ≫ Φ.hom.left := pullback.lift_fst _ _ _
    exact (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) k).trans
      ((Category.assoc _ _ _).symm.trans (H e)))
  · exact (Over.w _).trans (Over.w (U.gt e).q).symm


open CoordCompare in
theorem c_and_coord [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete I R] (hG : GlobalFnsSt)
    (Φ : D'.P.A ≅ D.P.A) (w : LB.Iso D'.P.L (D.P.L.pull Φ.hom.left)) (hw : w.IsGen) [IsMonHom Φ.hom]
    (hp : ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) (xe : D'.X ≃+ D.X)
    (hker : ∀ e, CharAgree.Match (U.gt e) (U'.gt e) xe) :
    (∀ x, D'.c x ≫ Φ.hom = D.c (xe x)) ∧ ∀ (e : ℕ) (x : D'.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left)
      (z : Z) (J) (J'), Good D.P.L z J → Good D'.P.L z J' → val ((U.gt e).t (xe x)) r z J =
        wVal (U'.gt e) Φ.hom x w r z J J' * val ((U'.gt e).t x) r z J' := by
  have hw' := (isGen_iff w).1 hw
  have hp' : ∀ e, (U'.gt e).pG ≫ Φ.hom = (U.gt e).pG := fun e => Over.OverMorphism.ext (hp e)
  have desc := fun e x => exists_desc_gen (U.gt e) (U'.gt e) Φ.hom (hp' e) (xe x) x w hw'
    (fun Z r z J J' hJ hJ' h h' => hker e Z r z J J' hJ hJ' h h' x)
  have hc : ∀ x, D'.c x ≫ Φ.hom = D.c (xe x) := fun x => by
    have := D.P.isAb.smooth
    have := D.P.isAb.geomConnected
    have := D.P.isAb.proper
    have h := (sec_eq_zero_and_hom_eq_of_thickenings R I (IsAdicComplete.le_jacobson_bot I)
      D.P.A).2 D.P.A (toUnit _ ≫ D'.c x ≫ Φ.hom) (toUnit _ ≫ D.c (xe x)) fun n => by
        obtain ⟨v, hv, -⟩ := desc n x
        have h₁ := thick_eq _ _ v hv
        have h₂ : (fstG I n D.P.A).left ≫ (toUnit D.P.A).left =
            pullback.snd D.P.A.hom (thick R I n) ≫ thick R I n := pullback.condition
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ _) h₂.symm).trans (Category.assoc _ _ _))))))
    simpa using congrArg (η[D.P.A] ≫ ·) h
  refine ⟨hc, fun e x Z r z J J' hJ hJ' => ?_⟩
  obtain ⟨v, hv, hv'⟩ := desc e x
  have h₁ := val_eq_one hG _ _ (hc x) v hv (fun y J hJ => by
    obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D'.P.L D'.P.isLB y
    have := (U.gt e).q_hom
    have h := hv' _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left
      y J J' hJ hJ'
    rwa [← Over.comp_left, MonObj.one_comp, wVal_one, TorusCoord.val_unit _ _ hJ,
      TorusCoord.val_unit _ _ hJ', inv_one, _root_.mul_one, _root_.mul_one] at h) _ (r ≫ (U.gt e).q.left) z J hJ
  have h₂ := (hv' _ r z J J' hJ hJ').symm.trans h₁
  rw [← _root_.mul_assoc, mul_inv_eq_one] at h₂
  exact h₂.symm

theorem exists_cmp_id : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegPre R) (A A' : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (U' : PreU I D' A' G) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull (𝟙 G.left))) (hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _), IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL → ∃ C : Cmp (RingHom.id R) U U' (𝟙 G.left), C.wL = wL := by
  intro hL R _ _ _ I hR D D' A A' G _ _ U U' wL hw hwL
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≠ ⊤ := by
    rintro rfl
    have : Subsingleton R := IsHausdorff.subsingleton hC.toIsHausdorff
    exact false_of_nontrivial_of_subsingleton R
  obtain ⟨Φ, w, hg, H⟩ := exists_iso U U' wL hI hL.secBaseChange hL.ample hwL
  have := isMonHom_of_pG U U' Φ fun e => (H e).1
  obtain ⟨xe, hxe⟩ := exists_xe U U' hI
  obtain ⟨hc, ht⟩ := c_and_coord U U' hL.globalFns Φ w hg (fun e => (H e).1) xe hxe
  have hm : ∀ (f : Sp R ⟶ Sp R) (_ : f = 𝟙 _) (h), IsCPMap U'.P U.P f (𝟙 G.left) h wL := by
    rintro _ rfl _
    exact hwL
  refine ⟨⟨Cmp.grpPullback_id G Cmp.spMap_ringHom_id, wL, hm _ Cmp.spMap_ringHom_id _, Φ.hom.left,
    (isGrpPullback_of_iso Φ).congr Cmp.spMap_ringHom_id.symm rfl, w, hg, xe, fun x => ?_, fun e Z x' x hx => ?_,
    (Ideal.map_id _).le⟩, rfl⟩
  · rw [Cmp.spMap_ringHom_id, ← hc]
    exact (Category.id_comp _).symm
  · have := Cmp.mono_fstG I e G
    rw [Category.comp_id, cancel_mono] at hx
    subst hx
    refine ⟨congrArg (x ≫ ·) (H e).1, fun z J J' hJ hJ' => ⟨fun χ => ?_, fun k k' hk hk' => ?_⟩⟩
    · refine (ht e χ Z x z J J' hJ hJ').trans ((mul_comm _ _).trans (congrArg _ ?_))
      simp only [CoordCompare.wVal, Category.assoc]
    · exact (H e).2 Z x z _ _ k k' (hJ (x ≫ (U.gt e).pG.left)) (hJ' (x ≫ (U'.gt e).pG.left)) hk hk'

end GlobalTheory.LN.PreUnique
end
