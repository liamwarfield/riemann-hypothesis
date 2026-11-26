module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharacterSectionMultiplicative

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharacterSectionTangentFunctional
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharacterSectionTangentFunctional
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.HTLinear

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem valAt_top {B : Type} [CommRing B] {X : Scheme.{0}} (v : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt v ⊤ le_top s = (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (v.appTop.hom s) := by
  rfl

theorem valAt_spec_comp {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (φ : B →+* C)
    (v : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom φ) ≫ v) ⊤ le_top s = φ (valAt v ⊤ le_top s) := by
  rw [valAt_top, valAt_top, Scheme.Hom.comp_appTop]
  exact congrArg (fun f => f.hom (v.appTop.hom s)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

theorem valAt_mul [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {B : Type} [CommRing B]
    (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (y z : Over.mk q ⟶ Γ.G) :
    valAt (B := B) (y * z).left ⊤ le_top s =
      valAt (B := B) y.left ⊤ le_top s * valAt (B := B) z.left ⊤ le_top s := by
  have h := (GlobalTheory.T.character_section_multiplicative R T Γ χ s hs (Over.mk q)).1 y z
  rw [valAt_top, valAt_top, valAt_top, ← map_mul]
  exact congrArg _ h

theorem valAt_one [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {B : Type} [CommRing B]
    (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) :
    valAt (B := B) (1 : Over.mk q ⟶ Γ.G).left ⊤ le_top s = 1 := by
  have h := (GlobalTheory.T.character_section_multiplicative R T Γ χ s hs (Over.mk q)).2
  rw [valAt_top]
  refine (congrArg _ h).trans ?_
  exact map_one _

theorem tors_one {Γ : QFGroup R T} {S : Scheme.{0}} {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left} (h : Γ.IsTorsionAlong G x N i)
    (Y : Over (Spec (CommRingCat.of R))) :
    (1 : Y ⟶ Γ.G).left ≫ i = (1 : Over.mk (Y.hom ≫ x) ⟶ G).left := by
  let y₀ : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk ((1 : Y ⟶ Γ.G).left ≫ i) (by
    show ((1 : Y ⟶ Γ.G).left ≫ i) ≫ G.hom = Y.hom ≫ x
    rw [Category.assoc, h.isOver, ← Category.assoc, Over.w])
  have h1 := h.mul Y 1 1 y₀ y₀ rfl rfl
  rw [_root_.mul_one] at h1
  have h2 : y₀ * y₀ = y₀ * 1 := by
    rw [_root_.mul_one]
    exact Over.OverMorphism.ext h1
  have h3 : y₀ = 1 := mul_left_cancel h2
  exact congrArg (fun f => f.left) h3

section Tangent

variable {A : Type} [CommRing A] (π : R →+* A)

abbrev qMap : Spec (CommRingCat.of (DualNumber A)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom ((algebraMap A (DualNumber A)).comp π))

abbrev dMap : Spec (CommRingCat.of (DualNumber A)) ⟶ Spec (CommRingCat.of (DualNumber R)) :=
  Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap π))

theorem dMap_over : dMap π ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = qMap π := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_epsMul (c : R) :
    (epsMul (π c)).comp (GlobalTheory.CompanionTheory.Ar.dualMap π) = (GlobalTheory.CompanionTheory.Ar.dualMap π).comp (epsMul c) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, epsMul, mul_comm]

theorem epsMul_algebraMap (c : A) : (epsMul c).comp (algebraMap A (DualNumber A)) = algebraMap A (DualNumber A) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_dualMap : ((TrivSqZeroExt.fstHom A A A).toRingHom).comp (GlobalTheory.CompanionTheory.Ar.dualMap π) =
    π.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [GlobalTheory.CompanionTheory.Ar.dualMap]

theorem fst_q : ((TrivSqZeroExt.fstHom A A A).toRingHom).comp ((algebraMap A (DualNumber A)).comp π) = π := by
  refine RingHom.ext fun a => ?_
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
  {L : Type} [AddCommGroup L] [Module R L]

def IsTan (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left) (M : LieModel G x L) (e : L)
    (v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left) : Prop :=
  v ≫ Γ.G.hom = qMap π ∧ v ≫ i = dMap π ≫ (M.pt e).left

variable {π} {N : ℕ} {Γ : QFGroup R T} {i : Γ.G.left ⟶ G.left} {M : LieModel G x L}

theorem fst_valAt [Finite T] (h : Γ.IsTorsionAlong G x N i) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {e : L}
    {v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left} (hv : IsTan π Γ i M e v) :
    (valAt v ⊤ le_top s).fst = 1 := by
  let r : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom π)
  let p : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (DualNumber A)) :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom)
  have hpq : p ≫ qMap π = r := by
    simp only [p, r, qMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fst_q]
  let y : Over.mk r ⟶ Γ.G := Over.homMk (p ≫ v) (by
    show (p ≫ v) ≫ Γ.G.hom = r
    rw [Category.assoc, hv.1, hpq])
  have hy : y = 1 := by
    apply h.inj (Over.mk r)
    rw [tors_one h]
    have hp : p ≫ dMap π = r ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
      simp only [p, r, dMap]
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, fst_dualMap]
    let w : Over.mk (r ≫ x) ⟶ Over.mk x := Over.homMk r rfl
    have h1 : (w ≫ (1 : Over.mk x ⟶ G)).left = r ≫ (1 : Over.mk x ⟶ G).left := rfl
    rw [comp_one] at h1
    show (p ≫ v) ≫ i = (1 : Over.mk (r ≫ x) ⟶ G).left
    rw [h1, Category.assoc, hv.2, ← Category.assoc, hp, Category.assoc]
    exact congrArg (r ≫ ·) (M.tan e)
  have h2 : valAt (p ≫ v) ⊤ le_top s = 1 := by
    have h3 := valAt_one Γ χ s hs r
    rw [← hy] at h3
    exact h3
  have h4 := valAt_spec_comp (TrivSqZeroExt.fstHom A A A).toRingHom v s
  exact h4.symm.trans h2

theorem isTan_add [Finite T] (h : Γ.IsTorsionAlong G x N i) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {e e' : L}
    {v v' : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left} (hv : IsTan π Γ i M e v)
    (hv' : IsTan π Γ i M e' v') :
    ∃ w, IsTan π Γ i M (e + e') w ∧ valAt w ⊤ le_top s = valAt v ⊤ le_top s * valAt v' ⊤ le_top s := by
  let y : Over.mk (qMap π) ⟶ Γ.G := Over.homMk v hv.1
  let z : Over.mk (qMap π) ⟶ Γ.G := Over.homMk v' hv'.1
  let ρ : Over.mk (qMap π ≫ x) ⟶ epsAt x := Over.homMk (dMap π) (by
    show dMap π ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x = qMap π ≫ x
    rw [← Category.assoc, dMap_over])
  have hm := h.mul (Over.mk (qMap π)) y z (ρ ≫ M.pt e) (ρ ≫ M.pt e') hv.2.symm hv'.2.symm
  rw [← comp_mul, ← M.add] at hm
  exact ⟨(y * z).left, ⟨Over.w (y * z), hm.symm⟩, valAt_mul Γ χ s hs (qMap π) y z⟩

theorem isTan_smul (c : R) {e : L} {v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left}
    (hv : IsTan π Γ i M e v) :
    IsTan π Γ i M (c • e) (Spec.map (CommRingCat.ofHom (epsMul (π c))) ≫ v) := by
  constructor
  · rw [Category.assoc, hv.1, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, epsMul_algebraMap]
  · rw [Category.assoc, hv.2, M.smul, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, dualMap_epsMul]

end Tangent

theorem snd_epsMul {A : Type} [CommRing A] (c : A) (a : DualNumber A) :
    (epsMul c a).snd = c * a.snd := by
  simp [epsMul]

theorem char_on_tangent_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) → ∃ l : L →ₗ[R] (R ⧸ Ideal.span {(N : R)}), ∀ (e : L) (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧ v ≫ i = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left → valAt v ⊤ le_top s = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (l e) := by
  intro R _ _ T _ _ Γ S G _ _ x N i h L _ _ M χ s hs
  have hex : ∀ e : L, ∃ v, IsTan (Ideal.Quotient.mk (Ideal.span {(N : R)})) Γ i M e v ∧
      ∀ w, IsTan (Ideal.Quotient.mk (Ideal.span {(N : R)})) Γ i M e w → w = v :=
    fun e => GlobalTheory.T.existsUnique_tangent_dual_number R T Γ S G x N i h L M e
  choose v hv hu using hex
  have hfst : ∀ e, (valAt (v e) ⊤ le_top s).fst = 1 := fun e => fst_valAt h χ s hs (hv e)
  refine ⟨{ toFun := fun e => (valAt (v e) ⊤ le_top s).snd, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro e e'
    obtain ⟨w, hw, hval⟩ := isTan_add h χ s hs (hv e) (hv e')
    rw [← hu _ w hw, hval, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [add_comm]
  · intro c e
    have h1 := hu _ _ (isTan_smul c (hv e))
    rw [← h1, valAt_spec_comp, snd_epsMul]
    simp [Algebra.smul_def]
  · intro e w hw
    rw [hu e w hw]
    ext
    · simp [hfst]
    · simp

end GlobalTheory.CompanionTheory.Ar.BT.HTLinear
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharacterSectionTangentFunctionalStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_section_tangent_functional : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) → ∃ l : L →ₗ[R] (R ⧸ Ideal.span {(N : R)}), ∀ (e : L) (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧ v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left → valAt v ⊤ le_top s = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (l e) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.HTLinear.char_on_tangent_linear | exact GlobalTheory.CompanionTheory.Ar.BT.HTLinear.char_on_tangent_linear | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.HTLinear.char_on_tangent_linear <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalBaseChange
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange

theorem valAt_comp_top {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : valAt (x ≫ f) ⊤ le_top s = valAt x ⊤ le_top (f.appTop.hom s) := by
  unfold valAt
  congr 1

theorem valAt_spec_map {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (ψ : B →+* C)
    (y : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom ψ) ≫ y) ⊤ le_top s = ψ (valAt y ⊤ le_top s) := by
  rw [valAt_comp_top]
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have := congrArg (fun φ => φ.hom (y.appTop.hom s)) h
  simp only [CommRingCat.comp_apply] at this
  exact this

abbrev qmap {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (N : ℕ) :
    R ⧸ Ideal.span {(N : R)} →+* R' ⧸ Ideal.span {(N : R')} :=
  Ideal.quotientMap (Ideal.span {(N : R')}) (algebraMap R R')
    (Ideal.span_le.2 (by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      simp only [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.subset_span rfl))

end GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange


open GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange in
theorem GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isHT_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N (F ≫ i) → ∀ (L' : Type) [AddCommGroup L'] [Module R' L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) L') (β : L →+ L'), (∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) → Submodule.span R' (Set.range β) = ⊤ → ∀ (χ : T →* Rˣ) (w : Module.Dual R L) (w' : Module.Dual R' L'), (∀ e, w' (β e) = algebraMap R R' (w e)) → Γ.IsHT i M N χ w → Γ'.IsHT (F ≫ i) M' N ((Units.map (algebraMap R R' : R →* R')).comp χ) w' := by
  intro R _ _ T _ _ Γ S G _ _ x N i hi L _ _ M R' _ _ _ Γ' F hF hi' L' _ _ M' β hβ hspan χ w w' hw hHT
  obtain ⟨s, hs, hv⟩ := hHT
  have hs' : Γ'.HasValues (F.appTop.hom s)
      (fun t => (((Units.map (algebraMap R R' : R →* R')).comp χ t : R'ˣ) : R')) := by
    obtain ⟨B, instB, ib, j, j', σ, hj, hji, hj'i, -, hσj, hσj'⟩ := hF.pts
    intro t
    have hb : valAt (σ t) ⊤ le_top s = ib (χ t) := by
      apply hj
      rw [← GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.valAt_spec_map, hσj, hs t, ← RingHom.comp_apply, hji]
    show valAt (Γ'.pt t).left ⊤ le_top (F.appTop.hom s) = _
    rw [← GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.valAt_comp_top, ← hσj', GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.valAt_spec_map, hb, ← RingHom.comp_apply, hj'i]
    simp
  obtain ⟨l', hl'⟩ := GlobalTheory.T.character_section_tangent_functional R' T Γ' S G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N (F ≫ i) hi'
    L' M' ((Units.map (algebraMap R R' : R →* R')).comp χ) (F.appTop.hom s) hs'
  have key : ∀ e, l' (β e) = Ideal.Quotient.mk (Ideal.span {(N : R')}) (w' (β e)) := by
    intro e
    obtain ⟨v, hv1, hv2, hv3⟩ := hv e
    have hc : (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.qmap (R := R) (R' := R') N))) ≫ v) ≫ Γ.G.hom =
        Spec.map (CommRingCat.ofHom ((algebraMap (R' ⧸ Ideal.span {(N : R')})
          (DualNumber (R' ⧸ Ideal.span {(N : R')}))).comp (Ideal.Quotient.mk _))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
      rw [Category.assoc, hv1, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext r
      all_goals simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.qmap, Ideal.quotientMap_mk, TrivSqZeroExt.algebraMap_eq_inl]
    set v'' := hF.cart.lift _ _ hc with hv''
    have h1 := hF.cart.lift_fst _ _ hc
    have h2 := hF.cart.lift_snd _ _ hc
    rw [← hv''] at h1 h2
    have h3 : v'' ≫ F ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R')})))) ≫
        (M'.pt (β e)).left := by
      rw [← Category.assoc, h1, Category.assoc, hv2, hβ e, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
        ← Spec.map_comp]
      congr 2
      ext a
      all_goals simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.qmap, Ideal.quotientMap_mk, TrivSqZeroExt.algebraMap_eq_inl]
    have h4 := hl' (β e) v'' ⟨h2, h3⟩
    rw [← GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.valAt_comp_top, h1, GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.valAt_spec_map, hv3] at h4
    have h5 := congrArg TrivSqZeroExt.snd h4
    simp only [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.BT.HTBaseChange.qmap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, zero_add, add_zero, Ideal.quotientMap_mk] at h5
    rw [← h5, hw]
  have heq : l' = (Ideal.Quotient.mkₐ R' (Ideal.span {(N : R')})).toLinearMap.comp w' :=
    LinearMap.ext_on_range hspan (fun e => by simpa using key e)
  refine ⟨F.appTop.hom s, hs', fun e' => ?_⟩
  obtain ⟨v', ⟨hv'1, hv'2⟩, -⟩ := GlobalTheory.T.existsUnique_tangent_dual_number R' T Γ' S G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N
    (F ≫ i) hi' L' M' e'
  refine ⟨v', hv'1, hv'2, ?_⟩
  rw [hl' e' v' ⟨hv'1, hv'2⟩, heq]
  simp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalBaseChangeStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_functional_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) N (F ≫ i) → ∀ (L' : Type) [AddCommGroup L'] [Module R' L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) L') (β : L →+ L'), (∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) → Submodule.span R' (Set.range β) = ⊤ → ∀ (χ : T →* Rˣ) (w : Module.Dual R L) (w' : Module.Dual R' L'), (∀ e, w' (β e) = algebraMap R R' (w e)) → Γ.IsHT i M N χ w → Γ'.IsHT (F ≫ i) M' N ((Units.map (algebraMap R R' : R →* R')).comp χ) w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isHT_baseChange | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isHT_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isHT_baseChange <;> assumption)
end
