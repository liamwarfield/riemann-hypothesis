module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongGroupPullback
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LatticeIntegrallyClosedTorsion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagFieldExtension
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OmegaLatticeDominantCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogForm

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HeightPullbackDominatingMap
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HTPullK

theorem dual_sq {A B : Type} [CommRing A] [CommRing B] (c : A →+* B) :
    (dualMap c).comp (algebraMap A (DualNumber A)) = (algebraMap B (DualNumber B)).comp c := by
  ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    (dualMap d).comp (dualMap c) = dualMap (d.comp c) := by
  ext r <;> simp [dualMap]

theorem lieBC {S : Scheme.{0}} {G : Over S} [GrpObj G] {A B : Type} [CommRing A] [CommRing B] (c : A →+* B)
    (x : Sp A ⟶ S) (y : Sp B ⟶ S) (hy : y = Spec.map (CommRingCat.ofHom c) ≫ x) (hsm : Smooth G.hom)
    {E E' : Type} [AddCommGroup E] [Module A E] [AddCommGroup E'] [Module B E']
    (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap c)) ≫ (M.pt e).left) ∧
      (∀ (a : A) e, j (a • e) = c a • j e) ∧ Submodule.span B (Set.range j) = ⊤ ∧
      ∀ l : Module.Dual A E, ∃ l' : Module.Dual B E', ∀ e, l' (j e) = c (l e) := by
  subst hy
  letI : Algebra A B := c.toAlgebra
  letI : Module A E' := Module.compHom E' c
  haveI : IsScalarTower A B E' := ⟨fun a b e => by
    show (c a * b) • e = c a • b • e
    rw [mul_smul]⟩
  haveI : Smooth G.hom := hsm
  obtain ⟨j, h1, h2, -⟩ := GlobalTheory.T.lie_model_base_change_map S G A B x E E' M M'
  let β : E →ₗ[A] E' := { toFun := j, map_add' := map_add j, map_smul' := fun a e => h2 a e }
  have hbc : IsBaseChange B β := (GlobalTheory.T.lie_model_finite_base_change S G A x E M).2.2 B E' M' β h1
  refine ⟨j, h1, h2, ?_, ?_⟩
  · refine eq_top_iff.2 fun e _ => ?_
    refine hbc.inductionOn e (motive := fun z => z ∈ Submodule.span B (Set.range j)) ?_ ?_ ?_
    · exact fun m => Submodule.subset_span ⟨m, rfl⟩
    · exact fun s n h => Submodule.smul_mem _ s h
    · exact fun a b ha hb => Submodule.add_mem _ ha hb
  · intro l
    refine ⟨hbc.lift ((Algebra.linearMap A B).comp l), fun e => ?_⟩
    exact hbc.lift_eq _ e

theorem isHT_move {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : BT.QFGroup R T)
    {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (hφ : IsPullback φ G'.hom G.hom f) {x' : Sp R ⟶ S'} {y : Sp R ⟶ S} {i₁ : Γ.G.left ⟶ G.left}
    {i' : Γ.G.left ⟶ G'.left} (hi' : i' ≫ φ = i₁) (hover : i' ≫ G'.hom = Γ.G.hom ≫ x') {L : Type} [AddCommGroup L]
    [Module R L] {Ma : LieModel G y L} {Mb : LieModel G' x' L} (h : ∀ e, (Mb.pt e).left ≫ φ = (Ma.pt e).left)
    {N : ℕ} {χ : T →* Rˣ} {w : Module.Dual R L} (H : Γ.IsHT i₁ Ma N χ w) : Γ.IsHT i' Mb N χ w := _root_.GlobalTheory.CompanionTheory.Ar.HTPull.isHT_move (R := R) (T := T) (S := S) (S' := S') (G := G) (G' := G') (f := f) (φ := φ) (x' := x') (y := y) (i₁ := i₁) (i' := i') (L := L) (Ma := Ma) (Mb := Mb) (N := N) (χ := χ) (w := w) Γ hφ hi' hover h H

theorem isHT_lie {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : BT.QFGroup R T)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {i : Γ.G.left ⟶ G.left} {L₁ L₂ : Type} [AddCommGroup L₁]
    [Module R L₁] [AddCommGroup L₂] [Module R L₂] {M₁ : LieModel G x L₁} {M₂ : LieModel G x L₂} (g : L₁ ≃ₗ[R] L₂)
    (hg : ∀ e, M₂.pt (g e) = M₁.pt e) {N : ℕ} {χ : T →* Rˣ} {w : Module.Dual R L₂} (H : Γ.IsHT i M₂ N χ w) :
    Γ.IsHT i M₁ N χ (w.comp g.toLinearMap) := by
  obtain ⟨s, hs, hv⟩ := H
  refine ⟨s, hs, fun e => ?_⟩
  obtain ⟨v, h1, h2, h3⟩ := hv (g e)
  exact ⟨v, h1, by rw [h2, hg], h3⟩

theorem char_descends {R R' : Type} [CommRing R] [CommRing R'] [IsDomain R'] (s : R →+* R')
    (hs : Function.Injective s) {T : Type} [CommGroup T] {N : ℕ} (hN : 0 < N) {z : R} (hz : IsPrimitiveRoot z N)
    (hT : ∀ t : T, t ^ N = 1) (χ' : T →* R'ˣ) :
    ∃ χ : T →* Rˣ, (Units.map (s : R →* R')).comp χ = χ' := _root_.GlobalTheory.CompanionTheory.Ar.HTPull.char_descends (R := R) (R' := R') (T := T) (N := N) (z := z) s hs hN hz hT χ'

theorem core {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']
    (hs : Function.Injective (algebraMap R R')) {X X' : Scheme.{0}} (x : Sp R ⟶ X) (x' : Sp R' ⟶ X') (f : X' ⟶ X)
    (hx : x' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x)
    {G : Over X} {G' : Over X'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] (φ : G'.left ⟶ G.left)
    (hφ : IsGrpPullback G' G f φ) (hsm : Smooth G.hom) {T : Type} [CommGroup T] [Finite T] (Γ : BT.QFGroup R T)
    (N : ℕ) (i : Γ.G.left ⟶ G.left) (hi : Γ.IsTorsionAlong G x N i)
    {L L' : Type} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R' L']
    (M₀ : LieModel G x L) (M₀' : LieModel G' x' L') :
    ∃ (Γ' : BT.QFGroup R' T) (i' : Γ'.G.left ⟶ G'.left) (β : L →+ L'), Γ'.IsTorsionAlong G' x' N i' ∧
      (∀ e, (M₀'.pt (β e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M₀.pt e).left) ∧
      Submodule.span R' (Set.range β) = ⊤ ∧
      (∀ l : Module.Dual R L, ∃ l' : Module.Dual R' L', ∀ e, l' (β e) = algebraMap R R' (l e)) ∧
      ∀ (χ : T →* Rˣ) (w₀ : Module.Dual R L) (w₀' : Module.Dual R' L'), (∀ e, w₀' (β e) = algebraMap R R' (w₀ e)) →
        Γ.IsHT i M₀ N χ w₀ → Γ'.IsHT i' M₀' N ((Units.map (algebraMap R R' : R →* R')).comp χ) w₀' := _root_.GlobalTheory.CompanionTheory.Ar.HTPull.core (R := R) (R' := R') (X := X) (X' := X') (G := G) (G' := G') (T := T) (L := L) (L' := L') hs x x' f hx φ hφ hsm Γ N i hi M₀ M₀'

section Setup

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']
  {X X' : Scheme.{0}} {x : Sp R ⟶ X} {x' : Sp R' ⟶ X'} {f : X' ⟶ X}
  {G : Over X} {G' : Over X'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left}
  {Ω Ω' : Type} [Field Ω] [Field Ω'] {k : R →+* Ω} {k' : R' →+* Ω'} {i : Ω →+* Ω'}
  {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
  {M : LieModel G ξ V} {M' : LieModel G' ξ' V'} {j : V →+ V'}

theorem tan_eq (hφ : IsGrpPullback G' G f φ) {a b : V'}
    (h : (M'.pt a).left ≫ φ = (M'.pt b).left ≫ φ) : a = b := by
  refine M'.inj (Over.OverMorphism.ext (hφ.1.hom_ext h ?_))
  exact (Over.w (M'.pt a)).trans (Over.w (M'.pt b)).symm

theorem j_comm (hφ : IsGrpPullback G' G f φ) (hk : ∀ r, k' (algebraMap R R' r) = i (k r))
    (hj : ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap i)) ≫ (M.pt e).left)
    {L L' : Type} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R' L']
    {M₀ : LieModel G x L} {M₀' : LieModel G' x' L'} {β : L →+ L'}
    (hβ : ∀ e, (M₀'.pt (β e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M₀.pt e).left)
    {j₀ : L → V} (hj₀ : ∀ e, (M.pt (j₀ e)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀.pt e).left)
    {j' : L' → V'} (hj' : ∀ e, (M'.pt (j' e)).left = Spec.map (CommRingCat.ofHom (dualMap k')) ≫ (M₀'.pt e).left)
    (l : L) : j' (β l) = j (j₀ l) := by
  refine tan_eq (M' := M') hφ ?_
  rw [hj, hj₀, hj', Category.assoc, hβ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, dualMap_comp, dualMap_comp]
  have e : k'.comp (algebraMap R R') = i.comp k := RingHom.ext hk
  rw [e]

theorem form_eq (hk : ∀ r, k' (algebraMap R R' r) = i (k r))
    {L L' : Type} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R' L'] {β : L →+ L'}
    (hsp : Submodule.span R' (Set.range β) = ⊤) {j₀ : L → V} {j' : L' →+ V'}
    (hjs : ∀ (a : R') e, j' (a • e) = k' a • j' e) (hjj : ∀ l, j' (β l) = j (j₀ l))
    {w : Module.Dual Ω V} {w' : Module.Dual Ω' V'} (hww : ∀ e, w' (j e) = i (w e))
    {w₀ : Module.Dual R L} {w₀' : Module.Dual R' L'} (hw : ∀ l, w (j₀ l) = k (w₀ l))
    (hw₀ : ∀ l, w₀' (β l) = algebraMap R R' (w₀ l)) (e : L') : w' (j' e) = k' (w₀' e) := _root_.GlobalTheory.CompanionTheory.Ar.HTPull.form_eq (L := L) (L' := L') (β := β) (j₀ := j₀) (j' := j') (w := w) (w' := w') (w₀ := w₀) (w₀' := w₀') hk hsp hjs hjj hww hw hw₀ e

theorem forward (hs : Function.Injective (algebraMap R R'))
    (hx : x' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x)
    (hφ : IsGrpPullback G' G f φ) (hsm : Smooth G.hom)
    (hk : ∀ r, k' (algebraMap R R' r) = i (k r)) (hξ' : ξ' = Spec.map (CommRingCat.ofHom k') ≫ x')
    (hj : ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap i)) ≫ (M.pt e).left)
    {N : ℕ} {w : Module.Dual Ω V} {w' : Module.Dual Ω' V'} (hww : ∀ e, w' (j e) = i (w e))
    (H : M.IsHTFormOver N x k w) : M'.IsHTFormOver N x' k' w' := by
  have hsm' : Smooth G'.hom := MorphismProperty.of_isPullback hφ.1 hsm
  obtain ⟨_, T, _, Γ, i₀, L, _, _, M₀, j₀, χ, w₀, tor, hj₀, hHT, hw⟩ := H
  haveI := GlobalTheory.T.quasi_finite_group_finite R T Γ
  obtain ⟨L', _, _, ⟨M₀'⟩⟩ := lieModel_exists X' G' R' x'
  obtain ⟨Γ', i', β, tor', hβ, hsp, hext, hcore⟩ := core hs x x' f hx φ hφ hsm Γ N i₀ tor M₀ M₀'
  obtain ⟨j', hj', hjs, -, -⟩ := lieBC k' x' ξ' hξ' hsm' M₀' M'
  obtain ⟨w₀', hw₀⟩ := hext w₀
  refine ⟨inferInstance, T, _, Γ', i', L', _, _, M₀', j', (Units.map (algebraMap R R' : R →* R')).comp χ, w₀', tor',
    hj', hcore χ w₀ w₀' hw₀ hHT, ?_⟩
  exact form_eq hk hsp hjs (j_comm hφ hk hj hβ hj₀ hj') hww hw hw₀

end Setup

section Back

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']
  {X X' : Scheme.{0}} {x : Sp R ⟶ X} {x' : Sp R' ⟶ X'} {f : X' ⟶ X}
  {G : Over X} {G' : Over X'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left}
  {Ω Ω' : Type} [Field Ω] [Field Ω'] {k : R →+* Ω} {k' : R' →+* Ω'} {i : Ω →+* Ω'}
  {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
  {M : LieModel G ξ V} {M' : LieModel G' ξ' V'} {j : V →+ V'}

theorem backward [IsIntegrallyClosed R] [IsNoetherianRing R] (hs : Function.Injective (algebraMap R R'))
    (hx : x' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x)
    (hφ : IsGrpPullback G' G f φ) (hsm : Smooth G.hom)
    (hk : ∀ r, k' (algebraMap R R' r) = i (k r)) (hξ : ξ = Spec.map (CommRingCat.ofHom k) ≫ x)
    (hξ' : ξ' = Spec.map (CommRingCat.ofHom k') ≫ x')
    (hj : ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap i)) ≫ (M.pt e).left)
    {N : ℕ} (hN : 0 < N) (hN0 : (N : R') ≠ 0) {z : R} (hz : IsPrimitiveRoot z N)
    (h0 : M.IsHTFormOver N x k 0)
    (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (hjd : ∀ w e, jd w (j e) = i (w e))
    {w' : Module.Dual Ω' V'} (H : M'.IsHTFormOver N x' k' w') :
    ∃ w, M.IsHTFormOver N x k w ∧ ∃ u' : Module.Dual Ω' V', w' = jd w + N • u' ∧
      ∀ (e : V') (v : epsAt x' ⟶ G'), IsTanAt G' x' v →
        (M'.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k')) ≫ v.left → u' e ∈ k'.range := by
  have hsm' : Smooth G'.hom := MorphismProperty.of_isPullback hφ.1 hsm
  obtain ⟨_, T, _, Γ, i₀, L, _, _, M₀, -, -, -, tor, -, -, -⟩ := h0
  haveI := GlobalTheory.T.quasi_finite_group_finite R T Γ
  obtain ⟨_, T₂, _, Γ₂, i₂, L₂, _, _, M₂, j₂, χ₂, w₂, tor₂, hj₂, hHT₂, hw₂⟩ := H
  obtain ⟨L', _, _, ⟨M₀'⟩⟩ := lieModel_exists X' G' R' x'
  obtain ⟨Γ', i', β, tor', hβ, hsp, hext, hcore⟩ := core hs x x' f hx φ hφ hsm Γ N i₀ tor M₀ M₀'
  obtain ⟨b, hb⟩ := GlobalTheory.T.torsion_along_unique_up_to_iso R' T₂ T Γ₂ Γ' X' G' x' N i₂ i' tor₂ tor'
  have H₁ := hb L₂ M₂ χ₂ w₂ hHT₂
  obtain ⟨g, hg, -⟩ := GlobalTheory.T.lie_model_existsUnique_equiv X' G' R' x' L' L₂ M₀' M₂
  have H₂ := isHT_lie Γ' g hg H₁
  obtain ⟨χ, hχ⟩ := char_descends (algebraMap R R') hs hN hz (GlobalTheory.T.torsion_along_order_divides R T Γ X G x N i₀ tor)
    (χ₂.comp b.symm.toMonoidHom)
  obtain ⟨w₀, hw₀⟩ := PositivityTheory.UnitarySelfGeneration.ht_exists R T Γ X G x N i₀ tor hsm L M₀ χ
  obtain ⟨j₁, hj₁, -, -, hj₁ext⟩ := lieBC k x ξ hξ hsm M₀ M
  obtain ⟨w, hw⟩ := hj₁ext w₀
  obtain ⟨w₀', hw₀'⟩ := hext w₀
  have H₃ := hcore χ w₀ w₀' hw₀' hw₀
  rw [hχ] at H₃
  obtain ⟨u, hu⟩ := (GlobalTheory.T.hodge_tate_functional_unique_mod_smul R' T Γ' X' G' x' N i' tor' hsm' hN0 L' M₀' _ w₀' _ H₃).1 H₂
  obtain ⟨j', hj', hjs, hjsp, hjext⟩ := lieBC k' x' ξ' hξ' hsm' M₀' M'
  obtain ⟨u', hu'⟩ := hjext u
  refine ⟨w, ⟨inferInstance, T, _, Γ, i₀, L, _, _, M₀, j₁, χ, w₀, tor, hj₁, hw₀, hw⟩, u', ?_, ?_⟩
  · have hd := form_eq (w := w) (w' := jd w) hk hsp hjs (j_comm hφ hk hj hβ hj₁ hj') (hjd w) hw hw₀'
    refine LinearMap.ext_on hjsp ?_
    rintro _ ⟨e, rfl⟩
    have a1 : j₂ (g e) = j' e := M'.inj (Over.OverMorphism.ext (by rw [hj₂, hg, hj']))
    have a2 := hw₂ (g e)
    have a3 := LinearMap.congr_fun hu e
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.smul_apply] at a3
    rw [a1, a3] at a2
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    rw [a2, hd, hu', map_add (f := _), map_nsmul]
  · intro e v hv he
    obtain ⟨l, rfl⟩ := M₀'.onto v hv
    have : e = j' l := M'.inj (Over.OverMorphism.ext (he.trans (hj' l).symm))
    subst this
    exact ⟨u l, (hu' l).symm⟩

end Back

theorem om_decomp {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} {x : Sp R ⟶ X} {G : Over X} [GrpObj G]
    [IsCommMonObj G] {Ω Ω' : Type} [Field Ω] [Field Ω'] {k : R →+* Ω} {ξ : Sp Ω ⟶ X}
    {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] {M : LieModel G ξ V}
    (hξ : ξ = Spec.map (CommRingCat.ofHom k) ≫ x) (hsm : Smooth G.hom) (i : Ω →+* Ω') (j : V →+ V')
    (hjs : ∀ (a : Ω) e, j (a • e) = i a • j e) (hspan : Submodule.span Ω' (Set.range j) = ⊤)
    (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (hjd : ∀ w e, jd w (j e) = i (w e)) :
    ∃ (n : ℕ) (δ : Fin n → Module.Dual Ω V) (b : Fin n → V),
      (∀ a, ∃ v : epsAt x ⟶ G, IsTanAt G x v ∧
        (M.pt (b a)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v.left) ∧
      (∀ a e (v : epsAt x ⟶ G), IsTanAt G x v →
        (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v.left → δ a e ∈ k.range) ∧
      ∀ u' : Module.Dual Ω' V', u' = ∑ a, u' (j (b a)) • jd (δ a) := _root_.GlobalTheory.CompanionTheory.Ar.HTPull.om_decomp (R := R) (X := X) (x := x) (G := G) (Ω := Ω) (Ω' := Ω') (k := k) (ξ := ξ) (V := V) (V' := V') (M := M) hξ hsm i j hjs hspan jd hjd

end GlobalTheory.CompanionTheory.Ar.HTPullK

theorem GlobalTheory.CompanionTheory.Ar.HTPullK.main : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V') (j : V →+ V'), IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → Smooth G.hom → (∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left) → ∀ (jd : Module.Dual Ω V →+ Module.Dual Ω' V'), (∀ w e, jd w (j e) = i (w e)) → ∀ (N : ℕ), 0 < N → ∀ (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1), IsIntegrallyClosed (X.presheaf.stalk (f p'.1)) → IsNoetherianRing (X.presheaf.stalk (f p'.1)) → (∃ ζ : Ω, IsPrimitiveRoot ζ N) → M.IsHTFormAt N ⟨f p'.1, h⟩ 0 → M'.htLat N p' = (M.htLat N).pull ξ' f jd p' := by
  intro X X' Ω Ω' _ _ ξ ξ' f i G G' _ _ _ _ φ V V' _ _ _ _ M M' j gen gen' dom hφ hsm hj jd hjd N hN p' h hic hnoe
    hroot h0
  obtain ⟨ζ, hζ⟩ := hroot
  obtain ⟨hext, hspan, hlat⟩ := GlobalTheory.T.lie_lattice_dominant_compat X X' Ω Ω' ξ ξ' f i G G' φ V V' M M' j gen gen' dom hφ hsm hj
  have hsm' : Smooth G'.hom := MorphismProperty.of_isPullback hφ.1 hsm
  let p : Cpt ξ := ⟨f p'.1, h⟩
  let k := genMap ξ p
  let k' := genMap ξ' p'
  have hkinj : Function.Injective k := gen.inj p
  have hk'inj : Function.Injective k' := gen'.inj p'
  haveI : IsDomain (X.presheaf.stalk (f p'.1)) := hkinj.isDomain k
  haveI : IsDomain (X'.presheaf.stalk p'.1) := hk'inj.isDomain k'
  letI : Algebra (X.presheaf.stalk (f p'.1)) (X'.presheaf.stalk p'.1) := (f.stalkMap p'.1).hom.toAlgebra
  have hk : ∀ r, k' (algebraMap (X.presheaf.stalk (f p'.1)) (X'.presheaf.stalk p'.1) r) = i (k r) :=
    GlobalTheory.CompanionTheory.Ar.Flat.PullReg.stalkMap_comp_genMap dom p' h
  have hs : Function.Injective (algebraMap (X.presheaf.stalk (f p'.1)) (X'.presheaf.stalk p'.1)) := by
    intro a b e
    exact hkinj (i.injective (by rw [← hk, ← hk, e]))
  have hx : X'.fromSpecStalk p'.1 ≫ f = Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk (f p'.1)) (X'.presheaf.stalk p'.1))) ≫ X.fromSpecStalk (f p'.1) :=
    (Scheme.SpecMap_stalkMap_fromSpecStalk f).symm
  have hξ : ξ = Spec.map (CommRingCat.ofHom k) ≫ X.fromSpecStalk (f p'.1) := (RegAtDom.spec_genMap ξ _ h).symm
  have hξ' : ξ' = Spec.map (CommRingCat.ofHom k') ≫ X'.fromSpecStalk p'.1 :=
    (RegAtDom.spec_genMap ξ' p'.1 p'.2).symm
  haveI := hic
  haveI := hnoe
  haveI : NeZero N := ⟨hN.ne'⟩

  have hfr := RegAtRing.regAt_ring X Ω ξ gen p
  haveI : IsFractionRing (regAt ξ p) Ω := hfr.1
  haveI : IsIntegrallyClosed (regAt ξ p) := hfr.2.2 hic
  have hζint : IsIntegral (regAt ξ p) ζ :=
    IsIntegral.of_pow hN (by rw [hζ.pow_eq_one]; exact isIntegral_one)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hζint
  obtain ⟨z, hz⟩ := y.2
  have hkz : k z = ζ := hz.trans hy
  have hzp : IsPrimitiveRoot z N := IsPrimitiveRoot.of_map_of_injective (by rw [hkz]; exact hζ : IsPrimitiveRoot (k z) N) hkinj
  have hN0 : (N : X'.presheaf.stalk p'.1) ≠ 0 := by
    intro e
    have e' : (N : Ω') = 0 := by simpa using congrArg k' e
    have e'' : (N : Ω) = 0 := i.injective (by simpa using e')
    exact (hζ.neZero').out e''
  have hjds : ∀ (a : Ω) (w : Module.Dual Ω V), jd (a • w) = i a • jd w := by
    intro a w
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨e, rfl⟩
    rw [hjd, LinearMap.smul_apply, LinearMap.smul_apply, hjd, smul_eq_mul, smul_eq_mul, map_mul]
  have hreg : ∀ c ∈ regAt ξ p, i c ∈ regAt ξ' p' := by
    rintro _ ⟨r, rfl⟩
    exact ⟨_, hk r⟩
  have hC : ∀ u' ∈ M'.omLat p', N • u' ∈ (M.htLat N).pull ξ' f jd p' := by
    intro u' hu'
    have hu'' : ∀ e ∈ M'.lat p', u' e ∈ regAt ξ' p' := hu'
    obtain ⟨n, δ, b, hb, hδ, hdec⟩ := HTPullK.om_decomp (M := M) hξ hsm i j hext.1 hspan jd hjd
    have hδom : ∀ a, δ a ∈ M.omLat p := by
      intro a
      show ∀ e ∈ M.lat p, δ a e ∈ regAt ξ p
      intro e he
      obtain ⟨v, hv, hev⟩ := ((lieLat_carrier X G Ω ξ V M p).1 e).1 he
      exact hδ a e v hv hev
    have hNδ : ∀ a, (N : Ω) • δ a ∈ M.htLat N p := fun a =>
      (GlobalTheory.T.hodge_tate_lattice_le_omega X Ω ξ G V M N p gen hsm).2 h0 (δ a) (hδom a)
    have hc : ∀ a, u' (j (b a)) ∈ regAt ξ' p' := by
      intro a
      apply hu''
      rw [hlat]
      exact Submodule.subset_span ⟨h, b a, Submodule.subset_span (hb a), rfl⟩
    rw [hdec u', Finset.smul_sum]
    refine sum_mem fun a _ => ?_
    have e1 : N • (u' (j (b a)) • jd (δ a)) = u' (j (b a)) • jd ((N : Ω) • δ a) := by
      rw [Nat.cast_smul_eq_nsmul, map_nsmul, smul_comm]
    rw [e1]
    exact Submodule.smul_mem _ (⟨_, hc a⟩ : regAt ξ' p') (Submodule.subset_span ⟨h, _, hNδ a, rfl⟩)
  apply le_antisymm
  · refine Submodule.span_le.2 fun w' hw' => ?_
    obtain ⟨w, hwF, u', rfl, hu⟩ := HTPullK.backward (M := M) (M' := M') hs hx hφ hsm hk hξ hξ' hj hN hN0 hzp h0 jd hjd hw'
    have hu' : u' ∈ M'.omLat p' := by
      intro e he
      obtain ⟨v, hv, hev⟩ := ((lieLat_carrier X' G' Ω' ξ' V' M' p').1 e).1 he
      exact hu e v hv hev
    exact add_mem (Submodule.subset_span ⟨h, w, Submodule.subset_span hwF, rfl⟩) (hC u' hu')
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨h', e, he, rfl⟩
    show jd e ∈ M'.htLat N p'
    have he' : e ∈ M.htLat N p := he
    clear he
    induction he' using Submodule.span_induction with
    | mem w hw =>
      exact Submodule.subset_span (HTPullK.forward (M := M) (M' := M') hs hx hφ hsm hk hξ' hj (hjd w) hw)
    | zero => simp
    | add a b _ _ ha hb => simpa using add_mem ha hb
    | smul c a _ ha =>
      have e1 : jd (c • a) = i c • jd a := hjds c a
      rw [e1]
      exact Submodule.smul_mem _ (⟨i c, hreg c c.2⟩ : regAt ξ' p') ha

namespace PositivityTheory.UnitarySelfGeneration

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem height_pullback_dominating_map : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V') (j : V →+ V'), IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → Smooth G.hom → (∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left) → ∀ (jd : Module.Dual Ω V →+ Module.Dual Ω' V'), (∀ w e, jd w (j e) = i (w e)) → ∀ (N : ℕ), 0 < N → ∀ (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1), IsIntegrallyClosed (X.presheaf.stalk (f p'.1)) → IsNoetherianRing (X.presheaf.stalk (f p'.1)) → (∃ ζ : Ω, IsPrimitiveRoot ζ N) → M.IsHTFormAt N ⟨f p'.1, h⟩ 0 → M'.htLat N p' = (M.htLat N).pull ξ' f jd p' :=
  @GlobalTheory.CompanionTheory.Ar.HTPullK.main

end PositivityTheory.UnitarySelfGeneration
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HcptPullK

theorem pull_eq {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X)
    {E F : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Ω' F] (L : Lat ξ E) (j : E →+ F)
    (p' : Cpt ξ') (hq : genPt ξ ⤳ f p'.1) :
    L.pull ξ' f j p' = Submodule.span (regAt ξ' p') (j '' (L ⟨f p'.1, hq⟩ : Set E)) := by
  unfold Lat.pull
  congr 1
  ext e'
  constructor
  · rintro ⟨_, e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨hq, e, he, rfl⟩

theorem unitAt_natCast {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Sp Ω ⟶ X} (q : Cpt ξ) (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → unitAt ξ q (p : Ω)) : unitAt ξ q (n : Ω) := _root_.GlobalTheory.CompanionTheory.Ar.HcptPull.unitAt_natCast (X := X) (Ω := Ω) (ξ := ξ) q n hn h

theorem noeth_stalk {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (hg : IsCptGen ξ) (q : Cpt ξ)
    (h : IsNoetherianRing (regAt ξ q)) : IsNoetherianRing (X.presheaf.stalk q.1) :=
  isNoetherianRing_of_ringEquiv (regAt ξ q) (RingEquiv.ofBijective (genMap ξ q).rangeRestrict
    ⟨fun a b e => hg.inj q (congrArg Subtype.val e), (genMap ξ q).rangeRestrict_surjective⟩).symm

set_option maxHeartbeats 1000000 in
theorem hodgeCpt_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c) (Z : Scheme.{0}) (ξ' : Sp Ω' ⟶ Z) (h : Z ⟶ A.X), A.ξ ≫ A.f = x ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, ∀ s, ((A.M.htOm A.t.PP.L (p ^ A.R p)).map (A.Vgen s).dualRestrict).IsVBOn {q | InFibre A.ξ p q} (labelRk D s) ⊤) → (∀ q : Z, genPt ξ' ⤳ q) → CoordTie ℤ ξ' (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → GlobalTheory.CompanionTheory.Ar.Dominates ξ' A.ξ h i → ∃ (A' : HodgeCpt Y S y') (e : A'.X ≅ Z) (j : A.Li →+ A'.Li) (m : SABMap A'.t A.t (e.hom ≫ h)), A'.ξ ≫ e.hom = ξ' ∧ A'.f = e.hom ≫ h ≫ A.f ∧ A'.m.φ = m.φ ≫ A.m.φ ∧ A'.cst = i.comp A.cst ∧ A'.R = A.R ∧ IsExtOver i j ∧ (∀ v, (A'.M.pt (j v)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt v).left) ∧ (∀ p ∈ S, ∀ s, ((A'.M.htOm A'.t.PP.L (p ^ A'.R p)).map (A'.Vgen s).dualRestrict).IsVBOn {q | InFibre A'.ξ p q} (labelRk D s) ⊤) ∧ ∀ s, A'.V s = (A.V s).pull A'.ξ (e.hom ≫ h) j := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω Ω' _ _ i K K' _ _ J J' _ _ y y' A x Z ξ' h hx hS hvb hall htie hnorm hdom
  haveI : CharZero Ω := charZero_of_injective_ringHom A.cst.injective
  haveI : CharZero Ω' := charZero_of_injective_ringHom i.injective
  have hgen := A.tie.gen
  have hgen' := htie.gen
  obtain ⟨t', ⟨mh⟩⟩ : ∃ t' : SAB H Z, Nonempty (SABMap t' A.t h) :=
    ⟨_, ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabM Out.proved_CubePullSt h A.t⟩⟩
  obtain ⟨mf, hmf⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ A.m mh
  obtain ⟨Li', acg', mod', ⟨M'⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists Z t'.G Ω' ξ'
  obtain ⟨ρ', hρ', -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act Z t'.G Ω' ξ' Li' M' (𝓞 E) t'.act.act t'.act.hom t'.act.one
    t'.act.mul t'.act.add
  obtain ⟨j, hj⟩ := GlobalTheory.T.lie_model_pullback_map A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' hdom mh.cart
  have hsm : Smooth A.t.G.hom := A.t.semi.smooth
  obtain ⟨hext, hspan, hlat⟩ := GlobalTheory.T.lie_lattice_dominant_compat A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' j hgen hgen' hdom
    mh.cart hsm hj
  have hρj := GlobalTheory.T.lie_model_pullback_action A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' j (𝓞 E) A.t.act.act t'.act.act A.ρ ρ'
    hdom mh.cart hj A.act hρ' (fun a => mh.act a)
  obtain ⟨jd, hjd⟩ := GlobalTheory.T.dual_map_of_field_extension Ω Ω' i A.Li Li' j hext hspan
  have hW : ∀ s, eigSp ρ' ((i.comp A.cst).comp (labelEmb c s)) = Submodule.span Ω' (j '' (A.Vgen s : Set A.Li)) := fun s =>
    GlobalTheory.T.eigenspace_field_extension E Ω Ω' i A.Li Li' j A.ρ ρ' (A.emb s) hext hspan hρj
  have hdm := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates A.X Ω A.ξ Z Ω' ξ' h i hdom
  have hsp : ∀ p' : Cpt ξ', genPt A.ξ ⤳ h p'.1 := fun p' => (hdm p').choose
  have hreg : ∀ (p' : Cpt ξ'), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, i a ∈ regAt ξ' p' := fun p' => (hdm p').choose_spec.1
  have hun : ∀ (p' : Cpt ξ'), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, unitAt ξ' p' (i a) → unitAt A.ξ ⟨h p'.1, hsp p'⟩ a :=
    fun p' => (hdm p').choose_spec.2 hgen'
  have hfib : ∀ (p : ℕ) (p' : Cpt ξ'), InFibre ξ' p p' ↔ InFibre A.ξ p ⟨h p'.1, hsp p'⟩ := by
    intro p p'
    refine not_congr ⟨fun hu => ?_, fun ⟨a, b, d⟩ => ?_⟩
    · have hr : (p : Ω) ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩ := natCast_mem _ p
      exact hun p' _ hr (by simpa using hu)
    · refine ⟨?_, ?_, ?_⟩
      · intro e; apply a; apply i.injective; simpa using e
      · simpa using hreg p' _ b
      · simpa using hreg p' _ d
  have hnoeth := (GlobalTheory.T.regAt_noetherian_model_noetherian A.X Ω A.ξ ℤ _ _ A.tie).1
  have hnoeth' := (GlobalTheory.T.regAt_noetherian_model_noetherian Z Ω' ξ' ℤ _ _ htie).1
  have hic : ∀ q : Cpt A.ξ, IsIntegrallyClosed (A.X.presheaf.stalk q.1) := fun q => A.normal.isIntegrallyClosed_stalk q.1
  have hic' : ∀ q : Cpt ξ', IsIntegrallyClosed (Z.presheaf.stalk q.1) := fun q => (hnorm q.1).2
  have htors : ∀ p ∈ S, FullTorsion t'.G ξ' (p ^ A.R p) := fun p hp =>
    GlobalTheory.T.full_torsion_pullback A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ _ hdom mh.cart (A.tors p hp)
  have hint : ∀ (s) (q : Cpt A.ξ) (a : 𝓞 E), A.emb s a ∈ regAt A.ξ q := fun s q a =>
    GlobalTheory.T.integral_element_regular A.X Ω A.ξ q hgen (hic q) _ ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (A.emb s).toIntAlgHom)

  have hω : ∀ p ∈ S, ∀ p' : Cpt ξ', 0 < D.p + D.q → M'.htOm t'.PP.L (p ^ A.R p) p' =
      Submodule.span (regAt ξ' p') (jd '' (A.M.htOm A.t.PP.L (p ^ A.R p) ⟨h p'.1, hsp p'⟩ : Set _)) := by
    intro p hp p' hpos
    have hN : 0 < p ^ A.R p := pow_pos (A.S_prime p hp).pos _
    obtain ⟨s0, o, ⟨m0⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c O β Y A.X A.f A.t A.m Ω A.ξ x hx
    obtain ⟨s0', o', ⟨m0'⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c O β Y Z (h ≫ A.f) t' mf Ω' ξ' (spMap i ≫ x) (by
      rw [← Category.assoc, hdom, Category.assoc, hx, Category.assoc])
    have hc1 : IsIntegrallyClosed (A.X.presheaf.stalk (h p'.1)) := hic ⟨h p'.1, hsp p'⟩
    have hn1 : IsNoetherianRing (A.X.presheaf.stalk (h p'.1)) := noeth_stalk hgen ⟨h p'.1, hsp p'⟩ (hnoeth _)
    have h1 := PositivityTheory.UnitarySelfGeneration.lattice_integrally_closed_torsion E H D l (KA l) (baseKA l) A.X Ω A.ξ s0 o A.t m0 A.Li A.M (p ^ A.R p) ⟨h p'.1, hsp p'⟩ hgen hN
      (A.tors p hp) hc1 hn1
    have h1' := PositivityTheory.UnitarySelfGeneration.lattice_integrally_closed_torsion E H D l (KA l) (baseKA l) Z Ω' ξ' s0' o' t' m0' Li' M' (p ^ A.R p) p' hgen' hN
      (htors p hp) (hic' _) (noeth_stalk hgen' _ (hnoeth' _))
    have h2 := PositivityTheory.UnitarySelfGeneration.height_pullback_dominating_map A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' j hgen hgen' hdom mh.cart hsm hj jd hjd
      (p ^ A.R p) hN p' (hsp p') hc1 hn1 (h1.2.1 hpos) h1.1
    rw [h1'.2.2, h2, pull_eq ξ' h _ jd p' (hsp p'), h1.2.2]
  have hpos : ∀ s, 0 < labelRk D s → 0 < D.p + D.q := by
    intro s hs
    rcases s with τ | τ
    · have : 0 < D.p := hs
      omega
    · have : 0 < D.q := hs
      omega
  have hdual : ∀ p ∈ S, ∀ s, ∀ p' : Cpt ξ', InFibre ξ' p p' →
      M'.htDual t'.PP.L (p ^ A.R p) ρ' ((i.comp A.cst).comp (labelEmb c s)) p' =
        Submodule.span (regAt ξ' p') (j '' (A.M.htDual A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) ⟨h p'.1, hsp p'⟩ : Set A.Li)) := by
    intro p hp s p' hf
    have hq := (hfib p p').1 hf
    obtain ⟨U, hU, b, hb, hfr⟩ := hvb p hp s ⟨h p'.1, hsp p'⟩ hq
    obtain ⟨hli, hbs⟩ := hfr ⟨h p'.1, hsp p'⟩ hq hU
    exact GlobalTheory.T.dual_lattice_basis_extension Ω Ω' i (regAt A.ξ ⟨h p'.1, hsp p'⟩) (regAt ξ' p') A.Li Li' j jd (A.Vgen s) _
      (A.M.htOm A.t.PP.L (p ^ A.R p) ⟨h p'.1, hsp p'⟩) (M'.htOm t'.PP.L (p ^ A.R p) p') (labelRk D s) b hext (hreg p') hjd
      (hW s) (fun hr => hω p hp p' (hpos s hr)) hli hb hbs
  have hhtw : ∀ p ∈ S, ∀ s, ∀ p' : Cpt ξ', InFibre ξ' p p' →
      M'.htW t'.PP.L (p ^ A.R p) ρ' ((i.comp A.cst).comp (labelEmb c s)) (differentIdeal ℤ (𝓞 E)) p' =
        Submodule.span (regAt ξ' p')
          (j '' (A.M.htW A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) (differentIdeal ℤ (𝓞 E)) ⟨h p'.1, hsp p'⟩ : Set A.Li)) := by
    intro p hp s p' hf
    haveI := regAt_isLocalRing (ξ := A.ξ) ⟨h p'.1, hsp p'⟩
    obtain ⟨d₀, hd₀, hne, hdv⟩ := GlobalTheory.T.different_ideal_local_generator E Ω (regAt A.ξ ⟨h p'.1, hsp p'⟩) (A.emb s) (hint s _)
    exact GlobalTheory.T.different_scaled_lattice_extension Ω Ω' i (regAt A.ξ ⟨h p'.1, hsp p'⟩) (regAt ξ' p') A.Li Li' j (A.Vgen s) _ (𝓞 E) (A.emb s)
      (differentIdeal ℤ (𝓞 E)) d₀ (A.M.htDual A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) ⟨h p'.1, hsp p'⟩)
      (M'.htDual t'.PP.L (p ^ A.R p) ρ' ((i.comp A.cst).comp (labelEmb c s)) p') hext (hreg p') (hW s) hd₀ hne hdv
      (fun e he => LieModel.mem_eigSp_of_mem_htDual _ _ _ _ _ he) (hdual p hp s p' hf)
  have hV : ∀ s, Lat.patch S (M'.eigLat ρ' ((i.comp A.cst).comp (labelEmb c s)))
      (fun p => htLabel M' t'.PP.L (p ^ A.R p) ρ' (fun s' => (i.comp A.cst).comp (labelEmb c s')) s) =
      (A.V s).pull ξ' h j := by
    intro s
    funext p'
    rw [pull_eq ξ' h _ j p' (hsp p')]
    by_cases hc : ∃ p ∈ S, InFibre ξ' p p'
    · obtain ⟨p, hp, hf⟩ := hc
      rw [Lat.patch_of_unique S _ _ hp hf fun p2 hp2 h2 =>
        inFibre_unique (A.S_prime p hp) (A.S_prime p2 hp2) hf h2]
      have e1 : A.V s ⟨h p'.1, hsp p'⟩ = A.HT p s ⟨h p'.1, hsp p'⟩ :=
        Lat.patch_of_unique S _ _ hp ((hfib p p').1 hf) fun p2 hp2 h2 =>
          inFibre_unique (A.S_prime p hp) (A.S_prime p2 hp2) ((hfib p p').1 hf) h2
      rw [e1]
      rcases s with τ | τ
      · exact hhtw p hp _ p' hf
      · exact hdual p hp _ p' hf
    · have hc' : ∀ p ∈ S, ¬ InFibre ξ' p p' := fun p hp hf => hc ⟨p, hp, hf⟩
      rw [Lat.patch_of_not S _ _ hc']
      have hc'' : ∀ p ∈ S, ¬ InFibre A.ξ p ⟨h p'.1, hsp p'⟩ := fun p hp hf => hc' p hp ((hfib p p').2 hf)
      have e1 : A.V s ⟨h p'.1, hsp p'⟩ = A.dR s ⟨h p'.1, hsp p'⟩ := Lat.patch_of_not S _ _ hc''
      rw [e1]
      have hdisc : (((NumberField.discr E : ℤ) : Ω))⁻¹ ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩ := by
        have hn0 : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
        obtain ⟨-, -, hu⟩ := unitAt_natCast (ξ := A.ξ) ⟨h p'.1, hsp p'⟩ _ hn0 fun p hpp hd => by
          have hin := hS p hpp (Int.natCast_dvd.2 hd)
          exact not_not.1 (hc'' p hin)
        rcases Int.natAbs_eq (NumberField.discr E) with e | e
        · rw [e]; simpa using hu
        · rw [e]
          simpa using (regAt A.ξ ⟨h p'.1, hsp p'⟩).neg_mem hu
      show M'.lat p' ⊓ _ = _
      rw [hlat, pull_eq ξ' h _ j p' (hsp p')]
      exact GlobalTheory.T.lattice_eigen_field_extension E Ω Ω' i A.Li Li' j A.ρ ρ' (A.emb s) _ _ (A.M.lat ⟨h p'.1, hsp p'⟩) hext hρj (hreg p')
        (fun a e he => GlobalTheory.T.lie_lattice_stable_under_action A.X Ω A.ξ A.t.G A.Li A.M (𝓞 E) A.t.act A.ρ A.act _ a e he) (hint s _) hdisc
  have hvb' : ∀ s, (Lat.patch S (M'.eigLat ρ' ((i.comp A.cst).comp (labelEmb c s)))
      (fun p => htLabel M' t'.PP.L (p ^ A.R p) ρ' (fun s' => (i.comp A.cst).comp (labelEmb c s')) s)).IsVB (labelRk D s)
      (eigSp ρ' ((i.comp A.cst).comp (labelEmb c s))) := by
    intro s
    rw [hV s, hW s]
    have h3 := GlobalTheory.T.lattice_vector_bundle_pullback A.X Ω A.ξ A.Li Z Ω' ξ' h i Li' j (A.V s) Set.univ (labelRk D s) (A.Vgen s) hdom hext.1 hext.2
      (A.vb s)
    intro p' _
    obtain ⟨U, hU, b, hb, hfr⟩ := h3 p' ⟨hsp p', trivial⟩
    exact ⟨U, hU, b, hb, fun q _ hq => hfr q ⟨hsp q, trivial⟩ hq⟩
  have hvbt : ∀ p ∈ S, ∀ s, ((M'.htOm t'.PP.L (p ^ A.R p)).map
      (eigSp ρ' ((i.comp A.cst).comp (labelEmb c s))).dualRestrict).IsVBOn {q | InFibre ξ' p q} (labelRk D s) ⊤ := by
    intro p hp s
    exact GlobalTheory.T.lattice_flag_field_extension A.X Z Ω Ω' A.ξ ξ' h i A.Li Li' j jd (A.Vgen s) _ (A.M.htOm A.t.PP.L (p ^ A.R p))
      (M'.htOm t'.PP.L (p ^ A.R p)) {q | InFibre A.ξ p q} {q | InFibre ξ' p q} (labelRk D s) hdom hgen' hext hjd (hW s)
      (hvb p hp s) fun p' hf => ⟨hsp p', (hfib p p').1 hf, fun hr => hω p hp p' (hpos s hr)⟩
  let m' : SABMap t' A.t ((Iso.refl Z).hom ≫ h) :=
    { cm := mh.cm
      cart := by simpa using mh.cart
      base := by simpa using mh.base
      act := mh.act
      lin := mh.lin }
  refine ⟨{ X := Z, ξ := ξ', all := hall, tie := htie, normal := ⟨fun x => (hnorm x).1, fun x => (hnorm x).2⟩, f := h ≫ A.f, Ω₀ := A.Ω₀, ξ₀ := A.ξ₀,
            gen₀ := A.gen₀, cst := i.comp A.cst, cst_over := ?_, fn := i.comp A.fn, fn_over := ?_, t := t', m := mf,
            Li := Li', M := M', ρ := ρ', act := hρ', S_prime := A.S_prime, R := A.R, R_ge := A.R_ge, tors := htors,
            vb := hvb' }, Iso.refl Z, j, m', ?_, ?_, ?_, rfl, rfl, hext, hj, hvbt, ?_⟩
  · have e : ξ' ≫ h = spMap i ≫ A.ξ := hdom
    have e2 : ξ' ≫ h ≫ A.f ≫ Y.s = spMap i ≫ A.ξ ≫ A.f ≫ Y.s := by
      rw [← Category.assoc, e, Category.assoc]
    simp only [Category.assoc]
    rw [e2, A.cst_over]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · have := A.fn_over
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at this ⊢
    rw [← Category.assoc, hdom, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · simp
  · simp
  · exact hmf
  · intro s
    have e : (Iso.refl Z).hom ≫ h = h := Category.id_comp h
    refine (hV s).trans ?_
    exact congrArg (fun g => (A.V s).pull ξ' g j) e.symm

end GlobalTheory.CompanionTheory.Ar.HcptPullK

namespace PositivityTheory.UnitarySelfGeneration

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem hodge_compact_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c) (Z : Scheme.{0}) (ξ' : Sp Ω' ⟶ Z) (h : Z ⟶ A.X), A.ξ ≫ A.f = x ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, ∀ s, ((A.M.htOm A.t.PP.L (p ^ A.R p)).map (A.Vgen s).dualRestrict).IsVBOn {q | InFibre A.ξ p q} (labelRk D s) ⊤) → (∀ q : Z, genPt ξ' ⤳ q) → CoordTie ℤ ξ' (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) → IsNormalScheme Z → GlobalTheory.CompanionTheory.Ar.Dominates ξ' A.ξ h i → ∃ (A' : HodgeCpt Y S y') (e : A'.X ≅ Z) (j : A.Li →+ A'.Li) (m : SABMap A'.t A.t (e.hom ≫ h)), A'.ξ ≫ e.hom = ξ' ∧ A'.f = e.hom ≫ h ≫ A.f ∧ A'.m.φ = m.φ ≫ A.m.φ ∧ A'.cst = i.comp A.cst ∧ A'.R = A.R ∧ IsExtOver i j ∧ (∀ v, (A'.M.pt (j v)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt v).left) ∧ (∀ p ∈ S, ∀ s, ((A'.M.htOm A'.t.PP.L (p ^ A'.R p)).map (A'.Vgen s).dualRestrict).IsVBOn {q | InFibre A'.ξ p q} (labelRk D s) ⊤) ∧ ∀ s, A'.V s = (A.V s).pull A'.ξ (e.hom ≫ h) j :=
  @GlobalTheory.CompanionTheory.Ar.HcptPullK.hodgeCpt_pull

end PositivityTheory.UnitarySelfGeneration
