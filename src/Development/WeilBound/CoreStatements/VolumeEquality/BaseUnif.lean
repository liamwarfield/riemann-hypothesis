module

public import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifGood
public import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifEx2
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InducedModelMorphismCompStructureMap
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateUniversalFamily
public import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifVec
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveOverCoordsExist

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicFamilyConjugate
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicFamilyConjugate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem top_le_spMap_comp_iff {X : Scheme.{0}} (σ : ℂ →+* ℂ) (x : Sp ℂ ⟶ X) (U : X.Opens) :
    ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U := by
  have hsub : ∀ a b : Sp ℂ, a = b := fun a b => Subsingleton.elim (α := PrimeSpectrum ℂ) a b
  constructor
  · intro h p _
    have hq : x.base ((spMap σ).base p) ∈ U := h (show p ∈ (⊤ : (Sp ℂ).Opens) from trivial)
    rwa [hsub ((spMap σ).base p) p] at hq
  · intro h p _
    exact h (show (spMap σ).base p ∈ (⊤ : (Sp ℂ).Opens) from trivial)

private theorem gammaSpecIso_appLE_spMap_apply (z : Γ(Sp ℂ, ⊤)) (σ : ℂ →+* ℂ)
    (e : (⊤ : (Sp ℂ).Opens) ≤ (spMap σ) ⁻¹ᵁ ⊤) :
    (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)
      ((CommRingCat.Hom.hom (Scheme.Hom.appLE (spMap σ) ⊤ ⊤ e)) z) =
    σ ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) z) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ)
  exact congrArg (fun φ => CommRingCat.Hom.hom φ z) h

theorem valAt'_spMap_comp {X : Scheme.{0}} (σ : ℂ →+* ℂ) (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (spMap σ ≫ x) U f = σ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U f) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt'
  by_cases hx : ⊤ ≤ x ⁻¹ᵁ U
  · have hc : ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := (top_le_spMap_comp_iff σ x U).2 hx
    rw [dite_eq_left hc, dite_eq_left hx]
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
    rw [← Scheme.Hom.appLE_comp_appLE (spMap σ) x U ⊤ ⊤ hx (by simp)]
    rw [CommRingCat.hom_comp, RingHom.comp_apply]
    exact gammaSpecIso_appLE_spMap_apply _ σ _
  · have hc : ¬ ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := fun h => hx ((top_le_spMap_comp_iff σ x U).1 h)
    rw [dite_eq_right hc, dite_eq_right hx, map_zero]

private theorem differentiableOn_conj_comp_star {m : ℕ} {g : (Fin m → ℂ) → ℂ} {S : Set (Fin m → ℂ)}
    (hg : DifferentiableOn ℂ g S) :
    DifferentiableOn ℂ (fun b => starRingEnd ℂ (g (star b))) (star ⁻¹' S) := by
  intro b hb
  obtain ⟨L, hL⟩ := hg (star b) hb
  have h1 : HasFDerivWithinAt (star : (Fin m → ℂ) → (Fin m → ℂ))
      ((starL' ℝ : (Fin m → ℂ) ≃L[ℝ] (Fin m → ℂ)) : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)) (star ⁻¹' S) b :=
    ((starL' ℝ : (Fin m → ℂ) ≃L[ℝ] (Fin m → ℂ)) : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)).hasFDerivWithinAt
  have h2 : HasFDerivWithinAt g (L.restrictScalars ℝ) S (star b) := hL.restrictScalars ℝ
  have h3 := h2.comp b h1 (fun y hy => hy)
  have hR := ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasFDerivWithinAt b h3
  let L' : (Fin m → ℂ) →L[ℂ] ℂ :=
    { toFun := fun v => star (L (star v))
      map_add' := fun v w => by simp [star_add, map_add (f := _)]
      map_smul' := fun c v => by simp [star_smul, map_smul]
      cont := continuous_star.comp (L.continuous.comp continuous_star) }
  exact ⟨L', HasFDerivWithinAt.of_restrictScalars (𝕜 := ℝ) hR (by ext v; rfl)⟩

theorem isHolTo_conj (X : Scheme.{0}) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (hy : IsHolTo B y) :
    IsHolTo (star ⁻¹' B) (fun b => spMap (starRingEnd ℂ) ≫ y (star b)) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo at hy ⊢
  intro U f
  obtain ⟨ho, hd⟩ := hy U f
  have hset : {b | b ∈ star ⁻¹' B ∧
        ⊤ ≤ (TopologicalSpace.Opens.map (spMap (starRingEnd ℂ) ≫ y (star b)).base).obj U}
      = star ⁻¹' {b | b ∈ B ∧ ⊤ ≤ (TopologicalSpace.Opens.map (y b).base).obj U} := by
    ext b
    exact and_congr_right fun _ => top_le_spMap_comp_iff (starRingEnd ℂ) (y (star b)) U
  rw [hset]
  refine ⟨ho.preimage continuous_star, ?_⟩
  refine (differentiableOn_conj_comp_star hd).congr ?_
  intro b _
  exact valAt'_spMap_comp (starRingEnd ℂ) (y (star b)) U f

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicFamilyConjugateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_family_conjugate : ∀ (X : Scheme.{0}) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsHolTo B y → IsHolTo (star ⁻¹' B) (fun b => spMap (starRingEnd ℂ) ≫ y (star b)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.isHolTo_conj | exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.isHolTo_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.isHolTo_conj <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifAsm
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem baseUnif_of_kUnif (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n g : ℕ)
    (q : CMType H × Fin j × Fin j' ≃ Fin n) (U : ∀ κ, KUnif Y sm j j' n g q κ) :
    ∃ B : BaseUnif Y sm j j' n, B.Locc := by
  classical
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  haveI : ∀ κ, Finite (U κ).ι := fun κ => (U κ).fin
  let C : Type := Σ κ : c.F →+* ℂ, (U κ).ι
  obtain ⟨np, ⟨e⟩⟩ := Finite.exists_equiv_fin C
  let a : Fin np → C := e.symm
  have hκ : ∀ κ κ' : c.F →+* ℂ, κ.comp (algebraMap (𝓞 c.F) c.F) = κ'.comp (algebraMap (𝓞 c.F) c.F) → κ = κ' :=
    fun κ κ' h => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h
  have hq : ∀ b : C, ((U b.1).F b.2).q = q := fun b => (U b.1).q_eq b.2
  have hdisj : ∀ b b' : C, ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, (U b.1).pt b.2 t = (U b'.1).pt b'.2 t' → b = b' := by
    rintro ⟨κ, k⟩ ⟨κ', k'⟩ t ht t' ht' h
    have h₁ := (U κ).comp_s_eq_spMap_of_isOver k t ht
    have h₂ := (U κ').comp_s_eq_spMap_of_isOver k' t' ht'
    dsimp only at h
    rw [h, h₂] at h₁
    obtain rfl := hκ _ _ (spMap_injective h₁)
    rw [(U κ').disj k k' t ht t' ht' h]
  have hemb : ∀ p : Sp ℂ ⟶ Y.X, ∃ κ : c.F →+* ℂ, p ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) := fun p => by
    obtain ⟨κ, hκρ⟩ := FamEx.exists_ringHom_extend (Spec.preimage (p ≫ Y.s)).hom
    refine ⟨κ, ?_⟩
    rw [hκρ]
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨{
    np := np
    g := g
    Di := fun k => (U (a k).1).Di (a k).2
    sig := fun k => (U _).sig _
    κ := fun k => (a k).1
    F := fun k => (U (a k).1).F (a k).2
    q_eq := fun k k' => (hq _).trans (hq _).symm
    form_eq := fun k => (U _).form_eq _
    σ_eq := fun k => (U _).σ_eq _
    Γ := fun k => (U (a k).1).Γ (a k).2
    mem_Γ := fun k => (U _).mem_Γ _
    arith := fun k => (U _).arith _
    pt := fun k => (U (a k).1).pt (a k).2
    hol := fun k => by rw [hq]; exact (U _).hol _
    comp_s_eq_spMap_of_isOver := fun k => by rw [hq]; exact (U _).comp_s_eq_spMap_of_isOver _
    interior := fun k => by rw [hq]; exact (U _).interior _
    disj := fun k k' => by
      rw [hq, hq]
      exact fun t ht t' ht' h => e.symm.injective (hdisj _ _ t ht t' ht' h)
    fibre := fun k => by rw [hq]; exact (U _).fibre _
    onto := fun p hp => ?_
    lat := fun k => by rw [hq]; exact (U _).lat _
    vec := fun S Ω _ K _ J _ y 𝔐 k V z hV hs => (U _).vec S Ω K J y 𝔐 _ V z hV (by rw [← hq (a k)]; exact hs) }, ?_⟩
  · obtain ⟨κ, hκ⟩ := hemb p
    obtain ⟨k, t, ht, h⟩ := (U κ).onto p hp hκ
    obtain ⟨i, hi⟩ := e.symm.surjective ⟨κ, k⟩
    refine ⟨i, t, by rw [hq]; exact ht, ?_⟩
    show (U (e.symm i).1).pt (e.symm i).2 t = p
    rw [hi]
    exact h
  · intro m T y hT hTc hy hyi b hb b' hb' k k' t ht t' ht' h h'
    choose κ hκy using fun b => hemb (y b)
    have hd : ∀ r : 𝓞 c.F, DifferentiableOn ℂ (fun b => κ b (r : c.F)) T := fun r => by
      have h3 := (PullbackSections.isHolTo_comp hy Y.s ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 c.F))).inv r)).2
      have hset : T ⊆ {b ∈ T | ⊤ ≤ (y b ≫ Y.s) ⁻¹ᵁ ⊤} := fun b hb => ⟨hb, le_top⟩
      refine (h3.mono hset).congr fun b _ => ?_
      show κ b (r : c.F) = valAt' (y b ≫ Y.s) ⊤ _
      rw [hκy b]
      exact (PullbackSections.valAt'_spMap ((κ b).comp (algebraMap (𝓞 c.F) c.F)) r).symm
    have hc : ∀ b₁ ∈ T, y b₁ ≫ Y.s = spMap ((κ b).comp (algebraMap (𝓞 c.F) c.F)) := fun b₁ hb₁ => by
      rw [hκy, FamEx.embedding_const_preconnected hTc κ hd hb₁ hb]
    have key : ∀ d d' : C, y b = (U d.1).pt d.2 t → y b' = (U d'.1).pt d'.2 t' → t ∈ ballDom q → t' ∈ ballDom q → d = d' := by
      rintro ⟨κ₁, k₁⟩ ⟨κ₂, k₂⟩ h₁ h₂ ht ht'
      dsimp only at h₁ h₂
      have e₁ := (U κ₁).comp_s_eq_spMap_of_isOver k₁ t ht
      have e₂ := (U κ₂).comp_s_eq_spMap_of_isOver k₂ t' ht'
      rw [← h₁, hc b hb] at e₁
      rw [← h₂, hc b' hb'] at e₂
      obtain rfl := hκ _ _ (spMap_injective e₁)
      obtain rfl := hκ _ _ (spMap_injective e₂)
      rw [(U (κ b)).locc m T y hT hTc hy hyi hc b hb b' hb' k₁ k₂ t ht t' ht' h₁ h₂]
    exact e.symm.injective (key (a k) (a k') h h' (by rw [← hq (a k)]; exact ht) (by rw [← hq (a k')]; exact ht'))

theorem baseUnifEx2_of (hV : VecOfPeriods) (hC : KUnifConj) : BaseUnifEx2 := by
  intro hG E _ _ _ H D l Xo c Y sm j j' n h1 hs hn
  have hN : N1c := hG.1.2.2.1
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  have q : CMType H × Fin j × Fin j' ≃ Fin n := Fintype.equivFinOfCardEq (by simp [hn, mul_assoc])
  let ρ : c.F := (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ
  have hρ : (ρ : ℂ) = H.rt0 := rfl
  have good : ∀ κ : c.F →+* ℂ, κ ρ = H.rt0 → Nonempty (KUnif Y sm j j' n g q κ) := fun κ hκ => by
    obtain ⟨FU⟩ := hN E H D l Xo (κ.comp (IntermediateField.inclusion c.le).toRingHom) g ty h1 hκ hty
    exact kUnif_good hV Y sm j j' n g q κ ty hty hs ρ hρ hκ FU
  have all : ∀ κ : c.F →+* ℂ, Nonempty (KUnif Y sm j j' n g q κ) := fun κ => by
    have e : ρ ^ 2 = -(H.d : c.F) := Subtype.ext (by show (ρ : ℂ) ^ 2 = -(H.d : ℂ); exact H.sqrt_neg_disc_sq)
    have e2 : (κ ρ) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, e, H.sqrt_neg_disc_sq]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 e2 with h | h
    · exact good κ h
    · have h' := hC E H D l Xo c Y sm j j' n g q _ (good ((starRingEnd ℂ).comp κ) (by
        show starRingEnd ℂ (κ ρ) = _
        rw [h, map_neg, FamEx.rt0_conj_neg_ne_zero, neg_neg]))
      have e3 : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp κ) = κ := RingHom.ext fun x => by simp
      rwa [e3] at h'
  exact baseUnif_of_kUnif Y sm j j' n g q fun κ => (all κ).some

end SheetDecomposition
end
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifConj
section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifConjA
noncomputable section

namespace SheetDecomposition.Cj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped CategoryTheory.Obj ComplexOrder

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'') :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  by
    apply RingHom.ext
    intro a
    apply TrivSqZeroExt.ext <;> simp [dualMap]

theorem dualMap_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (a : R) :
    dualMap φ (algebraMap R (DualNumber R) a) = algebraMap R' (DualNumber R') (φ a) := by
  change dualMap φ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (φ a)
  apply TrivSqZeroExt.ext <;> simp [dualMap]

theorem centre_conj (z : Spec (CommRingCat.of ℂ) ⟶ X) : centre (spMap (starRingEnd ℂ) ≫ z) = centre z := by
  have h : (spMap (starRingEnd ℂ)) (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint ℂ :=
    Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact congrArg (fun p => z p) h

theorem cj_cj (z : Sp ℂ ⟶ X) : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ z = z := by
  rw [← Category.assoc, GlobalTheory.ArchMetricCompare.cj_cj, Category.id_comp]

theorem extends_conj (M : LieModel G ξ E) {x x' : X} (hx : x = x') (h : genPt ξ ⤳ x) (h' : genPt ξ ⤳ x') (e : E)
    (v : epsAt (X.fromSpecStalk x) ⟶ G) (hv : M.Extends ⟨x, h⟩ e v)
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of ℂ) (φ' : X.presheaf.stalk x' ⟶ CommRingCat.of ℂ)
    (H : Spec.map φ' ≫ X.fromSpecStalk x' = spMap (starRingEnd ℂ) ≫ Spec.map φ ≫ X.fromSpecStalk x) :
    ∃ v' : epsAt (X.fromSpecStalk x') ⟶ G, M.Extends ⟨x', h'⟩ e v' ∧
      Spec.map (CommRingCat.ofHom (dualMap φ'.hom)) ≫ v'.left =
        spMap (dualMap (starRingEnd ℂ)) ≫ Spec.map (CommRingCat.ofHom (dualMap φ.hom)) ≫ v.left := _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint.extends_conj (x := x) (x' := x') M hx h h' e v hv φ φ' H

theorem eps_sq : spMap (dualMap (starRingEnd ℂ)) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
    spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (starRingEnd ℂ) := by
  have h2 : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫ CommRingCat.ofHom (dualMap (starRingEnd ℂ)) =
      CommRingCat.ofHom (starRingEnd ℂ) ≫ CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) :=
    CommRingCat.hom_ext (RingHom.ext fun a => dualMap_algebraMap (starRingEnd ℂ) a)
  have h3 := congrArg Spec.map h2
  simpa only [Spec.map_comp] using h3

def cjVec (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : epsAt z ⟶ G) : epsAt (spMap (starRingEnd ℂ) ≫ z) ⟶ G :=
  Over.homMk (spMap (dualMap (starRingEnd ℂ)) ≫ w.left) (by
    have h1 : w.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ z := Over.w w
    simp only [Over.mk_hom, Category.assoc, h1]
    rw [← Category.assoc, eps_sq, Category.assoc])

theorem valAt_conj (M : LieModel G ξ E) (z : Spec (CommRingCat.of ℂ) ⟶ X) (e : E) (w : epsAt z ⟶ G)
    (hw : M.ValAt z e w) : M.ValAt (spMap (starRingEnd ℂ) ≫ z) e (cjVec z w) := by
  obtain ⟨h, v, hv, hl⟩ := (show ∃ (h : genPt ξ ⤳ centre z) (v : epsAt (X.fromSpecStalk (centre z)) ⟶ G),
    M.Extends ⟨centre z, h⟩ e v ∧ w.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ v.left from hw)
  have hc := centre_conj z
  have h' : genPt ξ ⤳ centre (spMap (starRingEnd ℂ) ≫ z) := hc ▸ h
  obtain ⟨v', hv', hl'⟩ := extends_conj M hc.symm h h' e v hv (Scheme.stalkClosedPointTo z)
    (Scheme.stalkClosedPointTo (spMap (starRingEnd ℂ) ≫ z)) (by
      refine (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (spMap (starRingEnd ℂ) ≫ z)).trans ?_
      exact congrArg (spMap (starRingEnd ℂ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)
  refine ⟨h', v', hv', ?_⟩
  have : (cjVec z w).left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left := rfl
  rw [this, hl]
  exact hl'.symm

theorem isTangent_of_fibre {A : Over (Sp ℂ)} [GrpObj A] {z : Sp ℂ ⟶ X} {φ : A.left ⟶ G.left} (h : IsGrpPullback A G z φ)
    {v : epsAt z ⟶ G} (hv : IsTanAt G z v) {v' : epsR ℂ ⟶ A} (e : v'.left ≫ φ = v.left) : IsTangent v' := by
  refine h.1.hom_ext ?_ ?_
  · rw [Category.assoc, e]
    refine Eq.trans ?_ (GlobalTheory.PolBaseChange.eSec_comm h).symm
    refine Eq.trans hv ?_
    show (toUnit _ ≫ η[G]).left = _
    simp [eSec]
  · have z := congrArg (· ≫ A.hom) (GlobalTheory.ArchMetricCompare.isTangent_zero A)
    rw [← z, Category.assoc, Category.assoc, Over.w, Over.w]

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ]

theorem fibreLatVec_conj {X : Scheme.{0}} (t : SAB H X) (z : Sp ℂ ⟶ X) (R R' : RiemLat E g Λ) {A₀ : Type}
    (x : A₀ → Fin g → ℂ) (v : A₀ → (epsAt z ⟶ t.G)) (hP : ∀ x, R'.P x = star (R.P x))
    (hH : R'.Hm = R.Hm.map (starRingEnd ℂ)) (hB : ∀ a x, R'.B a x = star (R.B a (star x)))
    (htan : ∀ a, IsTanAt t.G z (v a)) (hF : FibreLatVec t z R x v) :
    FibreLatVec t (spMap (starRingEnd ℂ) ≫ z) R' (fun a => star (x a)) (fun a => cjVec z (v a)) := by
  obtain ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, hvec⟩ := hF
  have h := isGrpPullback_pullback A (spMap (starRingEnd ℂ))
  refine ⟨(Over.pullback (spMap (starRingEnd ℂ))).obj A, inferInstance, pullback.fst _ _ ≫ φ,
    GlobalTheory.ArchMetricCompare.cjUnif h u, fun l => star (χ ⟨star l.1, l.2⟩), h.comp hpb, ?_, fun a p => ?_, ?_,
    fun p => ?_, fun i => ?_⟩
  · rw [hH]
    exact GlobalTheory.ArchMetricCompare.cj_isAH h u hAH
  · show (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star (R'.B a p)))).left ≫ pullback.fst _ _ ≫ φ =
      (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star p))).left ≫ (pullback.fst _ _ ≫ φ) ≫ (t.act.act a).left
    rw [hB a p, star_star, GlobalTheory.ArchMetricCompare.cjPt_comp' h, Category.assoc, ← Category.assoc _ φ,
      ← Category.assoc _ (pullback.fst _ _ ≫ φ), GlobalTheory.ArchMetricCompare.cjPt_comp', hact a (star p)]
    simp only [Category.assoc]
  · intro x y e
    rw [hP, hP] at e
    exact hinj (star_injective e)
  · show star p ∈ u.Λ ↔ _
    rw [hmem]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by rw [hP, hx, star_star]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, by rw [hP, star_star]⟩
  · obtain ⟨v', e, hd⟩ := hvec i
    have sq : (spMap (dualMap (starRingEnd ℂ)) ≫ v'.left) ≫ A.hom = (epsR ℂ).hom ≫ spMap (starRingEnd ℂ) := by
      rw [Category.assoc, Over.w]
      exact eps_sq
    let t'' : epsR ℂ ⟶ (Over.pullback (spMap (starRingEnd ℂ))).obj A :=
      Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
    have e' : t''.left ≫ pullback.fst _ _ = spMap (dualMap (starRingEnd ℂ)) ≫ v'.left := h.1.lift_fst _ _ _
    refine ⟨t'', ?_, GlobalTheory.ArchMetricCompare.cj_isDiff h u (isTangent_of_fibre hpb (htan i) e) e' hd⟩
    rw [← Category.assoc, e', Category.assoc, e]
    rfl

theorem eqvBy_conj {R₁ R₂ R₁' R₂' : RiemLat E g Λ} (h₁ : ∀ x, R₁'.P x = star (R₁.P x))
    (h₂ : ∀ x, R₂'.P x = star (R₂.P x)) {gm : Λ ≃ₗ[𝓞 E] Λ} (h : R₁.EqvBy R₂ gm) : R₁'.EqvBy R₂' gm := by
  obtain ⟨k, hk⟩ := h
  refine ⟨{ toFun := fun x => star (k (star x))
            invFun := fun x => star (k.symm (star x))
            map_add' := fun x y => by simp
            map_smul' := fun a x => by simp
            left_inv := fun x => by simp
            right_inv := fun x => by simp }, fun x => ?_⟩
  show R₂'.P (gm x) = star (k (star (R₁'.P x)))
  rw [h₁, h₂, hk, star_star]

theorem autGrp_neg (f : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) : autGrp (E := E) (-f) = autGrp f := by
  ext gm
  show (∀ x y, (-f) (gm x) (gm y) = (-f) x y) ↔ ∀ x y, f (gm x) (gm y) = f x y
  simp

theorem star_mem_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} {q : Ψ × Fin j × Fin j' ≃ Fin n} {t : Fin n → ℂ}
    (ht : t ∈ ballDom q) : star t ∈ ballDom q := by
  intro τ
  have e : 1 - (ballMat q (star t) τ)ᴴ * ballMat q (star t) τ = (1 - (ballMat q t τ)ᴴ * ballMat q t τ)ᵀ := by
    ext a b
    simp [ballMat, Matrix.mul_apply, Matrix.one_apply, eq_comm, _root_.mul_comm]
  rw [e]
  exact (ht τ).transpose

theorem preimage_star_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    star ⁻¹' ballDom q = ballDom q := by
  ext t
  constructor
  · intro h
    have h' := star_mem_ballDom (q := q) (t := star t) h
    rwa [star_star] at h'
  · intro h
    exact star_mem_ballDom (q := q) (t := t) h

theorem analyticAt_star_star {n : ℕ} {f : (Fin n → ℂ) → Fin g → ℂ} {t₀ : Fin n → ℂ} (h : AnalyticAt ℂ f (star t₀)) :
    AnalyticAt ℂ (fun t => star (f (star t))) t₀ := by
  have h1 : ∀ᶠ t in 𝓝 t₀, AnalyticAt ℂ f (star t) :=
    (continuous_star.continuousAt (x := t₀)).tendsto.eventually h.eventually_analyticAt
  refine GlobalTheory.SCV.analyticAt_of_differentiableOn (s := {t | AnalyticAt ℂ f (star t)}) (fun t ht => ?_) h1
  have := (show AnalyticAt ℂ f (star t) from ht).differentiableAt.star_star
  rw [star_star] at this
  exact this.differentiableWithinAt

end SheetDecomposition.Cj
end
end

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem vecAt_conj {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
    {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) {n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R R' : (Fin n → ℂ) → RiemLat E g Λ) (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (t₀ : Fin n → ℂ)
    (hR : ∀ t, (∀ x, (R' t).P x = star ((R (star t)).P x)) ∧ (R' t).Hm = (R (star t)).Hm.map (starRingEnd ℂ) ∧
      ∀ a x, (R' t).B a x = star ((R (star t)).B a (star x)))
    (h : VecAt 𝔐 R (fun t => spMap (starRingEnd ℂ) ≫ z (star t)) (star t₀)) : VecAt 𝔐 R' z t₀ := by
  intro m s hs
  obtain ⟨x, hx, hev⟩ := h m s fun a => by
    obtain ⟨v, hv⟩ := hs a
    show ∃ v, 𝔐.M.ValAt (spMap (starRingEnd ℂ) ≫ z (star (star t₀))) (s a) v
    rw [star_star]
    exact ⟨_, Cj.valAt_conj 𝔐.M _ _ v hv⟩
  refine ⟨fun a t => star (x a (star t)), fun a => Cj.analyticAt_star_star (hx a), ?_⟩
  filter_upwards [(continuous_star.continuousAt (x := t₀)).tendsto.eventually hev] with t ht
  obtain ⟨v, hv, hF⟩ := ht
  have key : ∀ (w w' : Sp ℂ ⟶ 𝔐.X) (v : Fin m → (epsAt w ⟶ 𝔐.t.G)), w' = spMap (starRingEnd ℂ) ≫ w →
      (∀ a, 𝔐.M.ValAt w (s a) (v a)) → FibreLatVec 𝔐.t w (R (star t)) (fun a => x a (star t)) v →
      ∃ v' : Fin m → (epsAt w' ⟶ 𝔐.t.G), (∀ a, 𝔐.M.ValAt w' (s a) (v' a)) ∧
        FibreLatVec 𝔐.t w' (R' t) (fun a => star (x a (star t))) v' := by
    rintro w _ v rfl hv hF
    exact ⟨fun a => Cj.cjVec w (v a), fun a => Cj.valAt_conj 𝔐.M w _ _ (hv a),
      Cj.fibreLatVec_conj 𝔐.t w _ _ _ v (hR t).1 (hR t).2.1 (hR t).2.2 (fun a => (hv a).isTanAt) hF⟩
  exact key _ _ v (by rw [Cj.cj_cj, star_star]) hv hF

theorem kUnifConj : KUnifConj := by
  rintro E _ _ _ H D l Xo c Y sm j j' n g q κ ⟨U⟩
  choose F' hq hσ hform hR using fun k => GlobalTheory.T.conjugate_universal_family E (CMType H) j j' n g (U.Di k).La (U.F k)
  have hcanc : ∀ {X : Scheme.{0}} {a b : Sp ℂ ⟶ X}, spMap (starRingEnd ℂ) ≫ a = spMap (starRingEnd ℂ) ≫ b → a = b :=
    fun {X a b} e => by rw [← Cj.cj_cj a, e, Cj.cj_cj]
  have hs : spMap (((starRingEnd ℂ).comp κ).comp (algebraMap (𝓞 c.F) c.F)) =
      spMap (starRingEnd ℂ) ≫ spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) :=
    Spec.map_comp (CommRingCat.ofHom (κ.comp (algebraMap (𝓞 c.F) c.F))) (CommRingCat.ofHom (starRingEnd ℂ))
  refine ⟨{
    ι := U.ι
    fin := U.fin
    Di := U.Di
    sig := U.sig
    F := F'
    q_eq := fun k => (hq k).trans (U.q_eq k)
    form_eq := fun k => ?_
    σ_eq := fun k τ => ?_
    Γ := U.Γ
    mem_Γ := U.mem_Γ
    arith := fun k => ?_
    pt := fun k t => spMap (starRingEnd ℂ) ≫ U.pt k (star t)
    hol := fun k => ?_
    comp_s_eq_spMap_of_isOver := fun k t ht => ?_
    interior := fun k t ht => ?_
    disj := fun k k' t ht t' ht' e =>
      U.disj k k' _ (Cj.star_mem_ballDom ht) _ (Cj.star_mem_ballDom ht') (hcanc e)
    fibre := fun k t ht t' ht' => ?_
    onto := fun p hp hps => ?_
    lat := fun k t ht => ?_
    vec := fun S Ω _ K _ J _ y 𝔐 k V z hV hVs hz hzf t₀ ht₀ => ?_
    locc := fun m T y hT hTc hy hyi hys b hb b' hb' k k' t ht t' ht' e e' => ?_ }⟩
  · rw [hform]
    rcases U.form_eq k with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)
  · rw [hσ, U.σ_eq]
    rfl
  · have h := U.arith k
    unfold UnivFam.IsArith at h ⊢
    rwa [hform, Cj.autGrp_neg]
  · have h := GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ (U.hol k)
    rwa [Cj.preimage_star_ballDom] at h
  · rw [Category.assoc, U.comp_s_eq_spMap_of_isOver k _ (Cj.star_mem_ballDom ht), hs]
  · rw [Cj.centre_conj]
    exact U.interior k _ (Cj.star_mem_ballDom ht)
  · have h := U.fibre k _ (Cj.star_mem_ballDom ht) _ (Cj.star_mem_ballDom ht')
    constructor
    · intro e
      obtain ⟨γ, hγ, he⟩ := h.1 (hcanc e)
      exact ⟨γ, hγ, Cj.eqvBy_conj (hR k t).1 (hR k t').1 he⟩
    · rintro ⟨γ, hγ, he⟩
      have e := h.2 ⟨γ, hγ, Cj.eqvBy_conj (fun x => by rw [(hR k t).1, star_star])
        (fun x => by rw [(hR k t').1, star_star]) he⟩
      show spMap (starRingEnd ℂ) ≫ U.pt k (star t) = spMap (starRingEnd ℂ) ≫ U.pt k (star t')
      rw [e]
  · obtain ⟨k, t, ht, e⟩ := U.onto (spMap (starRingEnd ℂ) ≫ p) (by rwa [Cj.centre_conj])
      (by rw [Category.assoc, hps, hs, Cj.cj_cj])
    refine ⟨k, star t, Cj.star_mem_ballDom ht, ?_⟩
    show spMap (starRingEnd ℂ) ≫ U.pt k (star (star t)) = p
    rw [star_star, e, Cj.cj_cj]
  · have h := Cj.fibreLatVec_conj Y.t _ _ ((F' k).R t) _ _ (hR k t).1 (hR k t).2.1 (hR k t).2.2 (fun a => a.elim)
      (U.lat k _ (Cj.star_mem_ballDom ht))
    obtain ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, -⟩ := h
    exact ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, fun a => a.elim⟩
  · refine vecAt_conj 𝔐 (U.F k).R (F' k).R z t₀ (hR k) ?_
    refine U.vec S Ω K J y 𝔐 k (star ⁻¹' V) _ (hV.preimage continuous_star) (fun t ht => ?_)
      (GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ hz) (fun t ht => ?_) _ (by simpa using ht₀)
    · simpa using Cj.star_mem_ballDom (hVs ht)
    · rw [Category.assoc, hzf _ ht, Cj.cj_cj, star_star]
  · have hpre : IsPreconnected (star ⁻¹' T : Set (Fin m → ℂ)) := by
      have e₀ : (star ⁻¹' T : Set (Fin m → ℂ)) = star '' T := by
        ext x
        constructor
        · intro h
          exact ⟨star x, h, star_star x⟩
        · rintro ⟨a, ha, rfl⟩
          show star (star a) ∈ T
          rwa [star_star]
      rw [e₀]
      exact hTc.image _ continuous_star.continuousOn
    refine U.locc m (star ⁻¹' T) _ (hT.preimage continuous_star) hpre (GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ hy) (fun a ha => ?_)
      (fun a ha => ?_) (star b) (by simpa using hb) (star b') (by simpa using hb') k k' _ (Cj.star_mem_ballDom ht) _
      (Cj.star_mem_ballDom ht') ?_ ?_
    · rw [Cj.centre_conj]
      exact hyi _ ha
    · rw [Category.assoc, hys _ ha, hs, Cj.cj_cj]
    · show spMap (starRingEnd ℂ) ≫ y (star (star b)) = _
      rw [star_star, e, Cj.cj_cj]
    · show spMap (starRingEnd ℂ) ≫ y (star (star b')) = _
      rw [star_star, e', Cj.cj_cj]

end SheetDecomposition
end
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifCoord
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.TangentOrigin

theorem spMap_fst_comp {R : Type} [CommRing R] (φ : R →+* DualNumber ℂ) :
    spMap fstC ≫ spMap φ = spMap (fstC.comp φ) := (Spec.map_comp _ _).symm

theorem evalPt_top {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (r : Γ(Sp R, ⊤)) :
    evalPt (spMap φ) ⊤ le_rfl r = φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) := by
  rw [← evalPt_spMap φ]
  congr 1
  simp

theorem mem_basicOpen_iff {R : Type} [CommRing R] (φ : R →+* DualNumber ℂ) (r : Γ(Sp R, ⊤)) :
    ⊤ ≤ spMap φ ⁻¹ᵁ (Sp R).basicOpen r ↔ (φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)).fst ≠ 0 := by
  rw [top_le_preimage_iff, spMap_fst_comp, GlobalTheory.top_le_preimage_basicOpen_iff _ ⊤ r,
    valAt'_eq_evalPt _ _ le_rfl, evalPt_top]
  rfl

theorem exists_frac {Z : Scheme.{0}} {R : Type} [CommRing R] (v : Sp R ⟶ Z) (U : Z.Opens) (f : Γ(Z, U))
    (φ₀ : R →+* DualNumber ℂ) (h₀ : ⊤ ≤ (spMap φ₀ ≫ v) ⁻¹ᵁ U) :
    ∃ (a r : R) (k : ℕ), (φ₀ r).fst ≠ 0 ∧ ∀ φ : R →+* DualNumber ℂ, (φ r).fst ≠ 0 →
      ∃ h : ⊤ ≤ (spMap φ ≫ v) ⁻¹ᵁ U, evalPt (spMap φ ≫ v) U h f * φ r ^ k = φ a := by
  let p₀ : Sp R := (spMap fstC ≫ spMap φ₀) (default : PrimeSpectrum ℂ)
  have hmem : p₀ ∈ v ⁻¹ᵁ U := by
    have h1 : ⊤ ≤ spMap φ₀ ⁻¹ᵁ (v ⁻¹ᵁ U) := by rwa [Scheme.Hom.comp_preimage] at h₀
    exact (GlobalTheory.top_le_preimage_iff_mem _ _).1 ((top_le_preimage_iff _ _).1 h1)
  obtain ⟨r, hrU, hr0⟩ := (isAffineOpen_top (Sp R)).exists_basicOpen_le (V := v ⁻¹ᵁ U) ⟨p₀, hmem⟩ trivial
  obtain ⟨⟨hh, s⟩, hk⟩ := IsLocalization.surj (Submonoid.powers r) ((v.appLE U _ hrU).hom f)
  obtain ⟨k, hks⟩ := s.2
  dsimp only at hk hks
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom hh, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r, k, ?_,
    fun φ hφ => ?_⟩
  · rw [← mem_basicOpen_iff, top_le_preimage_iff]
    exact (GlobalTheory.top_le_preimage_iff_mem _ _).2 hr0
  · have hD := (mem_basicOpen_iff φ r).2 hφ
    have hU : ⊤ ≤ (spMap φ ≫ v) ⁻¹ᵁ U := by
      rw [Scheme.Hom.comp_preimage]
      exact hD.trans (Scheme.Hom.preimage_mono _ hrU)
    refine ⟨hU, ?_⟩
    have e := congrArg (evalPt (spMap φ) _ hD) hk
    have e2 : ∀ x : Γ(Sp R, ⊤), evalPt (spMap φ) _ hD (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen r) x) =
        φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) := fun x =>
      (evalPt_res (spMap φ) le_top le_rfl hD x).trans (evalPt_top φ x)
    rw [map_mul, e2, e2, ← hks, map_pow, map_pow] at e
    rw [← e]
    congr 1

theorem analyticAt_det {n g : ℕ} {M : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} {t₀ : Fin n → ℂ}
    (h : ∀ a b, AnalyticAt ℂ (fun t => M t a b) t₀) : AnalyticAt ℂ (fun t => (M t).det) t₀ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h _ _)

theorem analyticAt_of_forms {n g : ℕ} (w : (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ)
    (h : ∀ z : Fin g → ℂ, z ≠ 0 → ∃ (Λ : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] ℂ) (r : (Fin n → ℂ) → ℂ),
      (∀ u, AnalyticAt ℂ (fun t => Λ t u) t₀) ∧ AnalyticAt ℂ r t₀ ∧ (∀ᶠ t in 𝓝 t₀, Λ t (w t) = r t) ∧ Λ t₀ z ≠ 0) :
    AnalyticAt ℂ w t₀ := by
  classical
  let S : Set ((Fin g → ℂ) →ₗ[ℂ] ℂ) := {μ | ∃ (Λ : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] ℂ) (r : (Fin n → ℂ) → ℂ),
      (∀ u, AnalyticAt ℂ (fun t => Λ t u) t₀) ∧ AnalyticAt ℂ r t₀ ∧ (∀ᶠ t in 𝓝 t₀, Λ t (w t) = r t) ∧ Λ t₀ = μ}
  have hS : Submodule.span ℂ S = ⊤ := Submodule.span_eq_top_of_ne_zero fun z hz => by
    obtain ⟨Λ, r, h1, h2, h3, h4⟩ := h z hz
    exact ⟨Λ t₀, ⟨Λ, r, h1, h2, h3, rfl⟩, h4⟩
  have hall : ∀ μ, μ ∈ S := fun μ => by
    have hμ : μ ∈ Submodule.span ℂ S := hS ▸ Submodule.mem_top
    induction hμ using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨fun _ => 0, fun _ => 0, fun _ => analyticAt_const, analyticAt_const, by simp, rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨Λ, r, h1, h2, h3, rfl⟩ := hx
      obtain ⟨Λ', r', h1', h2', h3', rfl⟩ := hy
      refine ⟨fun t => Λ t + Λ' t, fun t => r t + r' t, fun u => (h1 u).add (h1' u), h2.add h2', ?_, rfl⟩
      filter_upwards [h3, h3'] with t a b
      rw [LinearMap.add_apply, a, b]
    | smul c x _ hx =>
      obtain ⟨Λ, r, h1, h2, h3, rfl⟩ := hx
      refine ⟨fun t => c • Λ t, fun t => c * r t, fun u => analyticAt_const.mul (h1 u), analyticAt_const.mul h2, ?_, rfl⟩
      filter_upwards [h3] with t a
      rw [LinearMap.smul_apply, a, smul_eq_mul]
  choose Λ r h1 h2 h3 h4 using fun k : Fin g => hall (LinearMap.proj k)
  let M : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun t => Matrix.of fun k l => Λ k t (Pi.single l 1)
  have hM : ∀ t x k, (M t *ᵥ x) k = Λ k t x := fun t x k => by
    rw [LinearMap.pi_apply_eq_sum_univ (Λ k t) x]
    show ∑ l, M t k l * x l = _
    refine Finset.sum_congr rfl fun l _ => ?_
    have e : (fun j => if l = j then (1 : ℂ) else 0) = Pi.single l 1 := by
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [e, smul_eq_mul, mul_comm]
    rfl
  have hM0 : M t₀ = 1 := by
    ext k l
    simp [M, h4, Pi.single_apply, Matrix.one_apply]
  have hd : AnalyticAt ℂ (fun t => (M t).det) t₀ := analyticAt_det fun a b => h1 a _
  have hd0 : (M t₀).det ≠ 0 := by rw [hM0]; simp
  refine analyticAt_pi_iff.2 fun k => ?_
  have hc : AnalyticAt ℂ (fun t => ((M t).updateCol k fun i => r i t).det) t₀ := analyticAt_det fun a b => by
    by_cases hb : b = k
    · subst hb
      simpa using h2 a
    · simp only [Matrix.updateCol_ne hb]
      exact h1 a (Pi.single b 1)
  refine (hc.div hd hd0).congr ?_
  filter_upwards [Filter.eventually_all.2 h3, hd.continuousAt.eventually_ne hd0] with t ht hne
  have e1 : (fun i => r i t) = M t *ᵥ w t := funext fun i => by rw [hM, ht]
  have e2 : (M t).cramer (M t *ᵥ w t) = (M t).det • w t := by
    rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have e3 := congrFun e2 k
  rw [Matrix.cramer_apply] at e3
  show ((M t).updateCol k fun i => r i t).det / (M t).det = w t k
  rw [e1, e3, Pi.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hne]

theorem snd_of_mul_eq {x ρ α : DualNumber ℂ} (h : x * ρ = α) (hρ : ρ.fst ≠ 0) :
    x.snd = (α.snd * ρ.fst - α.fst * ρ.snd) / ρ.fst ^ 2 := by
  subst h
  simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  field_simp
  ring

theorem holCoord : HolCoord := by
  intro Z n g B e A _ v ψ w hB hol hψ hder huniq t₀ ht₀
  refine analyticAt_of_forms w t₀ fun z hz => ?_

  obtain ⟨U, h₀, f, hf⟩ : ∃ (U : Z.Opens) (_ : ⊤ ≤ (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ t₀)) ≫ v) ⁻¹ᵁ U) (f : Γ(Z, U)),
      fderiv ℂ (fun z => valAt' (e t₀ z) U f) 0 z ≠ 0 := by
    by_contra hn
    push Not at hn
    have h' : IsDerivAt0 (e t₀) (w t₀ + z) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ t₀)) ≫ v) :=
      ⟨(hder t₀ ht₀).1, fun U h f => by rw [map_add (f := _), hn U h f, add_zero]; exact (hder t₀ ht₀).2 U h f⟩
    have := huniq t₀ ht₀ _ _ _ h' (hder t₀ ht₀)
    exact hz (by simpa using this)
  have h00 : ⊤ ≤ e t₀ 0 ⁻¹ᵁ U := (GlobalTheory.FibreDeriv.top_le_preimage_eps _ _ (hder t₀ ht₀).1 U).1 h₀
  let G : (Fin n → ℂ) × (Fin g → ℂ) → ℂ := fun bz => valAt' (e bz.1 bz.2) U f
  have hG : AnalyticAt ℂ G (t₀, 0) :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (hol U f).2 ((hol U f).1.mem_nhds ⟨⟨ht₀, trivial⟩, h00⟩)
  have hι : AnalyticAt ℂ (fun t : Fin n → ℂ => ((t, 0) : (Fin n → ℂ) × (Fin g → ℂ))) t₀ :=
    analyticAt_id.prod analyticAt_const
  have hslice : ∀ t, DifferentiableAt ℂ G (t, 0) → ∀ u,
      fderiv ℂ (fun z => valAt' (e t z) U f) 0 u = fderiv ℂ G (t, 0) (0, u) := fun t ht u => by
    have h1 : HasFDerivAt (fun z : Fin g → ℂ => ((t, z) : (Fin n → ℂ) × (Fin g → ℂ)))
        (ContinuousLinearMap.inr ℂ _ _) 0 := hasFDerivAt_prodMk_right t 0
    have h2 := ht.hasFDerivAt.comp (0 : Fin g → ℂ) h1
    have h3 := h2.fderiv
    exact congrArg (fun T => T u) h3
  obtain ⟨a, r, k, hr0, hfr⟩ := exists_frac v U f (GlobalTheory.CompanionTheory.Ar.dualMap (ψ t₀)) h₀
  have hψa : ∀ x, AnalyticAt ℂ (fun t => ψ t x) t₀ := fun x =>
    GlobalTheory.SCV.analyticAt_of_differentiableOn (hψ x) (hB.mem_nhds ht₀)
  have hfst : ∀ t (x : DualNumber A), (GlobalTheory.CompanionTheory.Ar.dualMap (ψ t) x).fst = ψ t x.fst := fun t x => by simp [GlobalTheory.CompanionTheory.Ar.dualMap]
  have hsnd : ∀ t (x : DualNumber A), (GlobalTheory.CompanionTheory.Ar.dualMap (ψ t) x).snd = ψ t x.snd := fun t x => by simp [GlobalTheory.CompanionTheory.Ar.dualMap]
  have hpow : ∀ t, ψ t r.fst ≠ 0 → ψ t (r ^ k).fst ≠ 0 := fun t ht => by
    rw [TrivSqZeroExt.fst_pow, map_pow]
    exact pow_ne_zero _ ht
  rw [hfst] at hr0
  refine ⟨fun t => (fderiv ℂ G (t, 0)).toLinearMap.comp (LinearMap.inr ℂ _ _),
    fun t => (ψ t a.snd * ψ t (r ^ k).fst - ψ t a.fst * ψ t (r ^ k).snd) / ψ t (r ^ k).fst ^ 2, fun u => ?_, ?_, ?_, ?_⟩
  · have h1 : AnalyticAt ℂ (fun t : Fin n → ℂ => fderiv ℂ G (t, 0)) t₀ := hG.fderiv.comp_of_eq hι rfl
    exact ((ContinuousLinearMap.apply ℂ ℂ ((0, u) : (Fin n → ℂ) × (Fin g → ℂ))).analyticAt _).comp h1
  · exact (((hψa _).mul (hψa _)).sub ((hψa _).mul (hψa _))).div ((hψa _).pow 2) (pow_ne_zero _ (hpow _ hr0))
  · filter_upwards [hB.mem_nhds ht₀, (hψa r.fst).continuousAt.eventually_ne hr0,
      hι.continuousAt.eventually hG.eventually_analyticAt] with t ht hne hGt
    obtain ⟨hU, he⟩ := hfr (GlobalTheory.CompanionTheory.Ar.dualMap (ψ t)) (by rwa [hfst])
    rw [← map_pow] at he
    have h1 := snd_of_mul_eq he (by rw [hfst]; exact hpow t hne)
    rw [hfst, hfst, hsnd, hsnd] at h1
    rw [← h1]
    exact (hslice t hGt.differentiableAt (w t)).symm.trans ((hder t ht).2 U hU f).symm
  · exact fun h => hf ((hslice t₀ hG.differentiableAt z).trans h)

end SheetDecomposition
end
end

namespace SheetDecomposition

theorem baseUnifEx2 : BaseUnifEx2 := baseUnifEx2_of (vecOfPeriods_of holCoord) kUnifConj

theorem baseUnifEx : BaseUnifEx := fun hG E _ _ _ H D l Xo c Y sm j j' n h₁ h₂ h₃ =>
  (baseUnifEx2 hG E H D l Xo c Y sm j j' n h₁ h₂ h₃).elim fun B _ => ⟨B⟩

end SheetDecomposition
