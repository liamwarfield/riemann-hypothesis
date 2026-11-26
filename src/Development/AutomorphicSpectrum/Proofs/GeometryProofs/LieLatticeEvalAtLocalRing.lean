module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAt
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuesOfFrame

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRing
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRing
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem exists_base {S : Scheme.{0}} {G : Over S} [GrpObj G] {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R)
    (x : Spec (CommRingCat.of A) ⟶ S) (z : Spec (CommRingCat.of R) ⟶ S)
    (hz : Spec.map (CommRingCat.ofHom φ) ≫ x = z) {E F : Type} [AddCommGroup E] [Module A E] [AddCommGroup F]
    [Module R F] (M : LieModel G x E) (N : LieModel G z F) :
    ∃ j : E →+ F, (∀ e, (N.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ (M.pt e).left) ∧
      (∀ (a : A) e, j (a • e) = φ a • j e) ∧
      (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) A E),
        Submodule.span R (Set.range fun k => j (b k)) = ⊤) := by
  subst hz
  letI := φ.toAlgebra
  obtain ⟨j, h1, h2, h3⟩ := GlobalTheory.T.lie_model_base_change_map S G A R x E F M N
  exact ⟨j, h1, h2, fun hs n b => (h3 hs n b).2⟩

end GlobalTheory.CompanionTheory.Ar.LieVal

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem lieLat_val (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type)
    [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) (ER : Type)
    [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER) :
    IsCptGen ξ → Smooth G.hom → ∃ ev : M.lat ⟨centre z, h⟩ →+ ER,
      (∀ (e : E) (w : ER), M.ValAt z e (MR.pt w) ↔ ∃ he : e ∈ M.lat ⟨centre z, h⟩, ev ⟨e, he⟩ = w) ∧
      (∀ (a : regAt ξ ⟨centre z, h⟩) (r : R) e, ValAt ξ z (a : Ω) r → ev (a • e) = r • ev e) ∧
      Submodule.span R (Set.range ev) = ⊤ := by
  intro hξ hs
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  obtain ⟨j, hj, hjs, hjb⟩ := LieVal.exists_base (A := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom _ z
    (LieTangent.spec_centre z) MA MR
  obtain ⟨i, hi, his, -⟩ := LieVal.exists_base (genMap ξ ⟨centre z, h⟩) _ ξ
    (LieTangent.spec_genMap ξ ⟨centre z, h⟩) MA M

  have hext : ∀ a, M.Extends ⟨centre z, h⟩ (i a) (MA.pt a) := fun a => ⟨MA.tan a, hi a⟩
  have hmem : ∀ a, i a ∈ M.lat ⟨centre z, h⟩ := fun a => (M.mem_lat_iff _ _).2 ⟨_, hext a⟩
  have hinj : ∀ a b, i a = i b → a = b := fun a b hab =>
    MA.inj ((hext a).unique (hξ.inj _) (hab ▸ hext b))
  have hsurj : ∀ e v, M.Extends ⟨centre z, h⟩ e v → ∃ a, i a = e ∧ MA.pt a = v := by
    intro e v hv
    obtain ⟨a, rfl⟩ := MA.onto v hv.1
    exact ⟨a, M.inj (Over.OverMorphism.ext ((hi a).trans hv.2.symm)), rfl⟩
  let i' : EA →+ M.lat ⟨centre z, h⟩ :=
    { toFun := fun a => ⟨i a, hmem a⟩
      map_zero' := Subtype.ext (map_zero i)
      map_add' := fun a b => Subtype.ext (map_add i a b) }
  have hbij : Function.Bijective i' := by
    refine ⟨fun a b hab => hinj a b (congrArg Subtype.val hab), fun e => ?_⟩
    obtain ⟨v, hv⟩ := (M.mem_lat_iff _ _).1 e.2
    obtain ⟨a, ha, -⟩ := hsurj _ _ hv
    exact ⟨a, Subtype.ext ha⟩
  let q := AddEquiv.ofBijective i' hbij
  have hq : ∀ a, q.symm ⟨i a, hmem a⟩ = a := fun a => q.symm_apply_apply a
  refine ⟨j.comp q.symm.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro e w
    constructor
    · rintro ⟨h', v, hv, hw⟩
      obtain ⟨a, rfl, rfl⟩ := hsurj _ _ hv
      refine ⟨hmem a, ?_⟩
      change j (q.symm ⟨i a, hmem a⟩) = w
      rw [hq]
      exact MR.inj (Over.OverMorphism.ext ((hj a).trans hw.symm))
    · rintro ⟨he, rfl⟩
      obtain ⟨v, hv⟩ := (M.mem_lat_iff _ _).1 he
      obtain ⟨a, rfl, rfl⟩ := hsurj _ _ hv
      change M.ValAt z (i a) (MR.pt (j (q.symm ⟨i a, hmem a⟩)))
      rw [hq]
      exact ⟨h, _, hext a, hj a⟩
  · rintro a r e ⟨_, s, hsa, rfl⟩
    obtain ⟨b, rfl⟩ := q.surjective e
    have : a • q b = q (s • b) := Subtype.ext (by
      change (a : Ω) • i b = i (s • b)
      rw [his, hsa])
    change j (q.symm (a • q b)) = _ • j (q.symm (q b))
    rw [this, q.symm_apply_apply, q.symm_apply_apply]
    exact hjs s b
  · obtain ⟨n, ⟨b⟩⟩ := GlobalTheory.T.lie_model_free_over_local_ring X G hs (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) EA MA
    refine top_le_iff.1 ((hjb hs n b).symm.le.trans (Submodule.span_mono ?_))
    rintro _ ⟨k, rfl⟩
    refine ⟨q (b k), ?_⟩
    change j (q.symm (q (b k))) = _
    rw [q.symm_apply_apply]

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_lattice_eval_at_local_ring : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type) [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) (ER : Type) [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER), IsCptGen ξ → Smooth G.hom → ∃ ev : M.lat ⟨centre z, h⟩ →+ ER, (∀ (e : E) (w : ER), M.ValAt z e (MR.pt w) ↔ ∃ he : e ∈ M.lat ⟨centre z, h⟩, ev ⟨e, he⟩ = w) ∧ (∀ (a : regAt ξ ⟨centre z, h⟩) (r : R) e, ValAt ξ z (a : Ω) r → ev (a • e) = r • ev e) ∧ Submodule.span R (Set.range ev) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieLat_val | exact GlobalTheory.CompanionTheory.Ar.lieLat_val | (intros; apply GlobalTheory.CompanionTheory.Ar.lieLat_val <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramPullbackIff
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramPullbackIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem lbIso_pull_gram {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M j j rfl) (chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem hodgeGram_iff_of_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (x' : Sp ℂ ⟶ S') (x : Sp ℂ ⟶ S) (k : ℕ) (v' : Fin k → (epsAt x' ⟶ t'.G)) (v : Fin k → (epsAt x ⟶ t.G)) (Γ : Matrix (Fin k) (Fin k) ℂ), x = x' ≫ f → (∀ a, (v' a).left ≫ m.φ = (v a).left) → (IsHodgeGram t'.G t'.PP.L x' v' Γ ↔ IsHodgeGram t.G t.PP.L x v Γ) := by
  intro E _ _ _ H S S' t t' f m x' x k v' v Γ hx hv
  subst hx
  have hL : LBIso t'.PP.L (t.PP.L.pull m.φ) := m.lin.imp fun _ h => h.1
  constructor
  · rintro ⟨Q, ψ, w, u, Hm, χ, W, hp, hl, hu, hw, hΓ⟩
    refine ⟨Q, ψ ≫ m.φ, w, u, Hm, χ, W, hp.comp m.cart, ?_, hu, fun i => ⟨?_, (hw i).2⟩, hΓ⟩
    · exact LBIso.trans (pull_isLB t.PP.isLB _) (pull_isLB t'.PP.isLB _) Q.isLB (lbIso_pull_gram hL ψ rfl).symm hl
    · rw [← Category.assoc, (hw i).1, hv]
  · rintro ⟨Q, ψ, w, u, Hm, χ, W, hp, hl, hu, hw, hΓ⟩
    have sq : ψ ≫ t.G.hom = (Q.A.hom ≫ x') ≫ f := by
      rw [Category.assoc]; exact hp.1.w
    let ψ' : Q.A.left ⟶ t'.G.left := m.cart.1.lift ψ (Q.A.hom ≫ x') sq
    have h1 : ψ' ≫ m.φ = ψ := m.cart.1.lift_fst _ _ sq
    have h2 : ψ' ≫ t'.G.hom = Q.A.hom ≫ x' := m.cart.1.lift_snd _ _ sq
    have hp' : IsGrpPullback Q.A t'.G x' ψ' := m.cart.cancel (hp.congr rfl h1.symm) h2
    refine ⟨Q, ψ', w, u, Hm, χ, W, hp', ?_, hu, fun i => ⟨?_, (hw i).2⟩, hΓ⟩
    · exact LBIso.trans (pull_isLB t'.PP.isLB _) (pull_isLB t.PP.isLB _) Q.isLB (lbIso_pull_gram hL ψ' h1.symm) hl
    · apply m.cart.1.hom_ext
      · rw [Category.assoc, h1, (hw i).1, hv]
      · rw [Category.assoc, h2, ← Category.assoc, Over.w (w i), Over.w (v' i)]
        rfl

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramPullbackIffStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_gram_pullback_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (x' : Sp ℂ ⟶ S') (x : Sp ℂ ⟶ S) (k : ℕ) (v' : Fin k → (epsAt x' ⟶ t'.G)) (v : Fin k → (epsAt x ⟶ t.G)) (Γ : Matrix (Fin k) (Fin k) ℂ), x = x' ≫ f → (∀ a, (v' a).left ≫ m.φ = (v a).left) → (IsHodgeGram t'.G t'.PP.L x' v' Γ ↔ IsHodgeGram t.G t.PP.L x v Γ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hodgeGram_iff_of_sabMap | exact GlobalTheory.CompanionTheory.Ar.Flat.hodgeGram_iff_of_sabMap | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hodgeGram_iff_of_sabMap <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameDomainInSegreChart
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameDomainInSegreChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

theorem inChart_unitAt_of_inFrameDomain : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (segreCoord y) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (cc : (k : K) → J k) (f : Ω) (h : genPt ξ ⤳ centre z), CoordsAt ξ y z w → InFrameDomain y cc f w → InChart ξ (segreCoord y) cc ⟨centre z, h⟩ ∧ unitAt ξ ⟨centre z, h⟩ f := by
  intro X Ω _ ξ K _ J _ y hT z w cc f h hw hd
  have hu : ∀ k, IsUnit (w ⟨k, cc k⟩) := fun k => IsUnit.mk0 _ (hd.1 k)
  have hy : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k => (hw.2 k (cc k) (hu k)).1
  have reg : ∀ {a : Ω} {r : ℂ}, ValAt ξ z a r → a ∈ regAt ξ ⟨centre z, h⟩ := by
    rintro a r ⟨_, s, hs, -⟩
    exact ⟨s, hs⟩
  refine ⟨⟨Finset.prod_ne_zero_iff.2 fun k _ => hy k, fun c' => ?_⟩, ?_⟩
  · choose r hr _ using fun k => (hw.2 k (cc k) (hu k)).2 (c' k)
    have hp : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, y ⟨k, c' k⟩ / y ⟨k, cc k⟩) (∏ k ∈ s, r k) := by
      classical
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using CxVal.one h
      | insert k s hk ih =>
        rw [Finset.prod_insert hk, Finset.prod_insert hk]
        exact CxVal.mul (hr k) ih
    have e : segreCoord y c' / segreCoord y cc = ∏ k, y ⟨k, c' k⟩ / y ⟨k, cc k⟩ := by
      simp only [segreCoord, Finset.prod_div_distrib]
    rw [e]
    exact reg (hp Finset.univ)
  · obtain ⟨v, hv, hv0⟩ := hd.2
    have hf : ValAt ξ z f v := (GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w h hw f v).2 hv
    refine ⟨?_, reg hf, reg (CxVal.inv hf hv0)⟩
    obtain ⟨_, s, hs, hsv⟩ := hf
    have hs0 : (Scheme.stalkClosedPointTo z).hom s ≠ 0 := by rw [hsv]; exact hv0
    have := (CxVal.isUnit s hs0).map (genMap ξ ⟨centre z, h⟩)
    rw [hs] at this
    exact this.ne_zero

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameDomainInSegreChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_domain_in_segre_chart : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (segreCoord y) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (cc : (k : K) → J k) (f : Ω) (h : genPt ξ ⤳ centre z), CoordsAt ξ y z w → InFrameDomain y cc f w → InChart ξ (segreCoord y) cc ⟨centre z, h⟩ ∧ unitAt ξ ⟨centre z, h⟩ f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.inChart_unitAt_of_inFrameDomain | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.inChart_unitAt_of_inFrameDomain | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.inChart_unitAt_of_inFrameDomain <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeDiscreteFree
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeDiscreteFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem FamExp.per_discrete : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), ∀ b ∈ B, ∃ Γ₀ : Submodule ℤ (Fin g → ℂ), (Γ₀ : Set (Fin g → ℂ)) = e.per b ∧ DiscreteTopology Γ₀ ∧ Module.Finite ℤ Γ₀ ∧ Module.Free ℤ Γ₀ := by
  intro R _ G _ _ g n M B ψ e b hb
  have h0 : e.ex b 0 = 1 := by
    have h := e.add b hb 0 0
    rw [add_zero] at h
    exact (left_eq_mul.mp h)
  let A : AddSubgroup (Fin g → ℂ) :=
    { carrier := e.per b
      zero_mem' := h0
      add_mem' := by
        intro z w hz hw
        have hz' : e.ex b z = 1 := hz
        have hw' : e.ex b w = 1 := hw
        show e.ex b (z + w) = 1
        rw [e.add b hb, hz', hw', _root_.one_mul]
      neg_mem' := by
        intro z hz
        have hz' : e.ex b z = 1 := hz
        show e.ex b (-z) = 1
        have h := e.add b hb z (-z)
        rw [add_neg_cancel, h0, hz', _root_.one_mul] at h
        exact h.symm }
  let Γ₀ : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule A
  obtain ⟨V, N, f, L, -, -, hL, -⟩ := e.log b hb
  have hslice : ∀ᶠ z : Fin g → ℂ in 𝓝 0,
      L (b, fun j => valAt' (e.ex b z).left V (f j)) = z := by
    have hc : Tendsto (fun z : Fin g → ℂ => (b, z)) (𝓝 0) (𝓝 (b, 0)) :=
      (Continuous.prodMk_right b).tendsto 0
    exact hc.eventually hL
  have hiso : ∀ᶠ z : Fin g → ℂ in 𝓝 0, z ∈ e.per b → z = 0 := by
    have h00 := hslice.self_of_nhds
    filter_upwards [hslice] with z hz hper
    have hz' : e.ex b z = e.ex b 0 := by
      have : e.ex b z = 1 := hper
      rw [this, h0]
    rw [hz'] at hz
    exact hz.symm.trans h00
  have hdisc : DiscreteTopology Γ₀ := by
    obtain ⟨U, hU, hUo, h0U⟩ := _root_.eventually_nhds_iff.mp hiso
    apply discreteTopology_of_isOpen_singleton_zero
    have : ({0} : Set Γ₀) = Subtype.val ⁻¹' U := by
      ext ⟨z, hz⟩
      constructor
      · intro h
        have : z = 0 := congrArg Subtype.val h
        simpa [this] using h0U
      · intro h
        have : z = 0 := hU z h hz
        exact Subtype.ext this
    rw [this]
    exact hUo.preimage continuous_subtype_val
  refine ⟨Γ₀, rfl, hdisc, ?_, ?_⟩
  · exact instModuleFinite_of_discrete_submodule Γ₀
  · exact instModuleFree_of_discrete_submodule Γ₀

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeDiscreteFreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_lattice_discrete_free : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), ∀ b ∈ B, ∃ Γ₀ : Submodule ℤ (Fin g → ℂ), (Γ₀ : Set (Fin g → ℂ)) = e.per b ∧ DiscreteTopology Γ₀ ∧ Module.Finite ℤ Γ₀ ∧ Module.Free ℤ Γ₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FamExp.per_discrete | exact GlobalTheory.CompanionTheory.Ar.Flat.FamExp.per_discrete | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FamExp.per_discrete <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentOpenStalksDomain
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentOpenStalksDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem stalkMap_bijective_of_flat_preimmersion {X Y : Scheme.{0}} (f : X ⟶ Y) [IsPreimmersion f] [Flat f] (x : X) :
    Function.Bijective (f.stalkMap x).hom := by
  refine ⟨?_, f.stalkMap_surjective x⟩
  have h := Flat.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

theorem spMap_flat_preimmersion {O F : Type} [CommRing O] [Field F] (β : O →+* F) (hi : Function.Injective β)
    (hq : ∀ x : F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) : IsPreimmersion (spMap β) ∧ Flat (spMap β) := by
  haveI : IsDomain O := hi.isDomain β
  letI : Algebra O F := β.toAlgebra
  have hal : ∀ a : O, algebraMap O F a = β a := fun _ => rfl
  have hfr : IsLocalization (nonZeroDivisors O) F :=
    { map_units := fun y => by
        refine IsUnit.mk0 _ ?_
        rw [hal]
        exact fun h => nonZeroDivisors.ne_zero y.2 (hi (h.trans (map_zero β).symm))
      surj := fun z => by
        obtain ⟨a, b, hb, e⟩ := hq z
        have hb0 : b ≠ 0 := fun h => hb (by rw [h, map_zero])
        exact ⟨(a, ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩), e⟩
      exists_of_eq := fun {x y} e => ⟨1, by rw [hi e]⟩ }
  refine ⟨IsPreimmersion.of_isLocalization (nonZeroDivisors O) (S := F), ?_⟩
  have hfl : Module.Flat O F := IsLocalization.flat F (nonZeroDivisors O)
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 hfl)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem j_flat_preimmersion {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) (hi : Function.Injective β) (hq : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) :
    IsPreimmersion Y.j ∧ Flat Y.j := by
  obtain ⟨h1, h2⟩ := spMap_flat_preimmersion β hi hq
  have h3 : IsPreimmersion (pullback.fst Y.s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip h1
  have h4 : Flat (pullback.fst Y.s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback _ _).flip h2
  have := Y.jQ_open
  exact ⟨inferInstanceAs (IsPreimmersion (Y.jQ ≫ pullback.fst _ _)), inferInstanceAs (Flat (Y.jQ ≫ pullback.fst _ _))⟩

theorem cptOver_isOpen_isDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → ∃ U' : (Xo.XF c).Opens, (U' : Set (Xo.XF c)) = U ∧ ∀ p : Xo.XF c, p ∈ U → IsDomain ((Xo.XF c).presheaf.stalk p) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z ⟨hi, hN, hq⟩
  obtain ⟨h1, h2⟩ := j_flat_preimmersion Y hi hq
  have hP : IsProper Y.s := GlobalTheory.SchemeWords.isProper_of_isProjOver Y.proj
  have hLN : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have ho := isOpen_closure_genPt (Z.ξ₀ ≫ Y.j) Z.gen
  have hU : U = Y.j ⁻¹' closure {genPt (Z.ξ₀ ≫ Y.j)} := by
    ext u
    rw [Z.closure u, Set.mem_preimage, ← specializes_iff_mem_closure]
    exact (Y.j.isEmbedding.isInducing.specializes_iff).symm
  refine ⟨⟨U, hU ▸ ho.preimage Y.j.continuous⟩, rfl, fun p _ => ?_⟩
  haveI := (Y.normal (Y.j p)).1
  have hb := stalkMap_bijective_of_flat_preimmersion Y.j p
  exact ((RingEquiv.ofBijective _ hb).symm.injective.isDomain (RingEquiv.ofBijective _ hb).symm.toRingHom)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentOpenStalksDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_open_stalks_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → ∃ U' : (Xo.XF c).Opens, (U' : Set (Xo.XF c)) = U ∧ ∀ p : Xo.XF c, p ∈ U → IsDomain ((Xo.XF c).presheaf.stalk p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.cptOver_isOpen_isDomain | exact GlobalTheory.CompanionTheory.Ar.Flat.cptOver_isOpen_isDomain | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.cptOver_isOpen_isDomain <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartLocalNormalForm
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartLocalNormalForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartGeo

open Topology

theorem inFrameDomain_eventually {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (y : (Σ k, J k) → Ω) (cc : (k : K) → J k) (f : Ω) {z : (Σ k, J k) → ℂ} (hz : InFrameDomain y cc f z) :
    ∀ᶠ w in 𝓝 z, InFrameDomain y cc f w := by
  obtain ⟨hc, v, ⟨d, g, h, hg, hh, hy, hgh, hhz, rfl⟩, hv⟩ := hz
  have hgz : MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) ≠ 0 := by
    intro h0
    apply hv
    rw [h0, zero_div]
  have c1 : ∀ᶠ w in 𝓝 z, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) ≠ 0 :=
    (MvPolynomial.continuous_eval _).continuousAt.eventually_ne hgz
  have c2 : ∀ᶠ w in 𝓝 z, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) h) ≠ 0 :=
    (MvPolynomial.continuous_eval _).continuousAt.eventually_ne hhz
  have c3 : ∀ᶠ w : (Σ k, J k) → ℂ in 𝓝 z, ∀ k, w ⟨k, cc k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k => (continuous_apply _).continuousAt.eventually_ne (hc k)
  filter_upwards [c1, c2, c3] with w h1 h2 h3
  exact ⟨h3, _, ⟨d, g, h, hg, hh, hy, hgh, h2, rfl⟩, div_ne_zero h1 h2⟩

theorem exists_perm_prefix {n : ℕ} (A : Finset (Fin n)) :
    ∃ π : Equiv.Perm (Fin n), ∀ i, ((π i : Fin n) : ℕ) < A.card ↔ i ∈ A := by
  classical
  have hle : A.card ≤ n := by simpa using A.card_le_univ
  let e : {x // x ∈ A} ≃ {j : Fin n // (j : ℕ) < A.card} :=
    A.equivFin.trans (Fin.castLEOrderIso hle).toEquiv
  refine ⟨e.extendSubtype, fun i => ⟨fun h => ?_, fun h => e.extendSubtype_mem i h⟩⟩
  by_contra hi
  exact e.extendSubtype_not_mem i hi h

theorem recentre_apply {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) (i : Fin n) :
    HodgeMetric.recentre t₀ ρ π u i = t₀ i + (ρ : ℂ) * u (π i) := by
  simp [HodgeMetric.recentre]

theorem recentre_mem_ball {n : ℕ} {t₀ u : Fin n → ℂ} {ρ ε : ℝ} (hρ : 0 < ρ) (hε : ρ ≤ ε) (π : Equiv.Perm (Fin n))
    (hu : u ∈ Metric.ball (0 : Fin n → ℂ) 1) : HodgeMetric.recentre t₀ ρ π u ∈ Metric.ball t₀ ε := by
  rw [mem_ball_iff_norm]
  refine lt_of_lt_of_le ?_ hε
  rw [pi_norm_lt_iff hρ]
  intro i
  have h1 : ‖u (π i)‖ < 1 :=
    lt_of_le_of_lt (norm_le_pi_norm u (π i)) (by simpa using hu)
  have h2 : (HodgeMetric.recentre t₀ ρ π u - t₀) i = (ρ : ℂ) * u (π i) := by
    simp [recentre_apply]
  rw [h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  nlinarith

theorem exists_recentre_chart : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (y : (Σ k, J k) → Ω) (P : Ideal (MRing J)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart P n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω), t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → InFrameDomain y cc f (χ.γ t₀) → ∃ (a₀ : ℕ) (π : Equiv.Perm (Fin n)) (ρ₀ : ℝ), a₀ ≤ n ∧ 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < χ.a ∧ t₀ (π.symm i) = 0) ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, HodgeMetric.recentre t₀ ρ π u ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ InFrameDomain y cc f (χ.γ (HodgeMetric.recentre t₀ ρ π u)) ∧ (χ.γ (HodgeMetric.recentre t₀ ρ π u) ∉ Bd ↔ u ∈ Flat.punct n a₀ 1) := by
  intro K _ J _ Ω _ y P n Bd χ t₀ cc f ht₀ hF
  classical
  let A : Finset (Fin n) := Finset.univ.filter (fun i => (i : ℕ) < χ.a ∧ t₀ i = 0)
  have hA : ∀ i, i ∈ A ↔ (i : ℕ) < χ.a ∧ t₀ i = 0 := fun i => by simp [A]
  obtain ⟨π, hπ⟩ := exists_perm_prefix A
  have hγ : ContinuousAt χ.γ t₀ := (χ.analytic t₀ ht₀).continuousAt
  have e1 : ∀ᶠ t in 𝓝 t₀, InFrameDomain y cc f (χ.γ t) :=
    hγ.eventually (inFrameDomain_eventually y cc f hF)
  have e2 : ∀ᶠ t : Fin n → ℂ in 𝓝 t₀, ∀ i : Fin n, t₀ i ≠ 0 → t i ≠ 0 := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : t₀ i = 0
    · exact Filter.Eventually.of_forall fun t h => absurd hi h
    · filter_upwards [(continuous_apply i).continuousAt.eventually_ne hi] with t ht _ using ht
  have e3 : ∀ᶠ t in 𝓝 t₀, t ∈ Metric.ball (0 : Fin n → ℂ) 1 :=
    Metric.isOpen_ball.mem_nhds ht₀
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (e1.and (e2.and e3))
  have hle : A.card ≤ n := by simpa using A.card_le_univ
  refine ⟨A.card, π, min ε 1, hle, lt_min hε one_pos, min_le_right _ _, fun i hi => ?_, fun ρ hρ hρ₀ u hu => ?_⟩
  · have : π.symm i ∈ A := (hπ _).1 (by simpa using hi)
    exact (hA _).1 this
  · obtain ⟨hF', hne, hb⟩ := hball _ (recentre_mem_ball hρ (hρ₀.trans (min_le_left _ _)) π hu)
    refine ⟨hb, hF', ?_⟩
    have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    rw [χ.boundary _ hb]
    constructor
    · intro h
      refine ⟨by simpa using hu, fun j hj => fun h0 => h ?_⟩
      have hm : π.symm j ∈ A := (hπ _).1 (by simpa using hj)
      obtain ⟨h1, h2⟩ := (hA _).1 hm
      refine ⟨π.symm j, h1, ?_⟩
      rw [recentre_apply, h2]
      simp [h0]
    · rintro ⟨-, hu'⟩ ⟨i, hi, h0⟩
      by_cases hti : t₀ i = 0
      · have hm : i ∈ A := (hA i).2 ⟨hi, hti⟩
        have := hu' (π i) ((hπ i).2 hm)
        rw [recentre_apply, hti, zero_add] at h0
        exact (mul_ne_zero hρc this) h0
      · exact hne i hti h0

end GlobalTheory.CompanionTheory.Ar.ChartGeo
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartLocalNormalFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_chart_local_normal_form : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (y : (Σ k, J k) → Ω) (P : Ideal (MRing J)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart P n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω), t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → InFrameDomain y cc f (χ.γ t₀) → ∃ (a₀ : ℕ) (π : Equiv.Perm (Fin n)) (ρ₀ : ℝ), a₀ ≤ n ∧ 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < χ.a ∧ t₀ (π.symm i) = 0) ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, HodgeMetric.recentre t₀ ρ π u ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ InFrameDomain y cc f (χ.γ (HodgeMetric.recentre t₀ ρ π u)) ∧ (χ.γ (HodgeMetric.recentre t₀ ρ π u) ∉ Bd ↔ u ∈ Flat.punct n a₀ 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartGeo.exists_recentre_chart | exact GlobalTheory.CompanionTheory.Ar.ChartGeo.exists_recentre_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartGeo.exists_recentre_chart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicCoordsOfGenericPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsChartFamilyOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.ChartHol

open Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt GlobalTheory.HolHom GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

theorem diffOn_div {f g : V → ℂ} {s : Set V} (hf : DifferentiableOn ℂ f s) (hg : DifferentiableOn ℂ g s)
    (h0 : ∀ b ∈ s, g b ≠ 0) : DifferentiableOn ℂ (fun b => f b / g b) s :=
  (hf.mul (hg.inv h0)).congr fun b _ => by simp [div_eq_mul_inv]

theorem holAt_of_isAffineOpen {N : Set V} {c : V → (Sp ℂ ⟶ X)} {A : X.Opens} (hA : IsAffineOpen A) (hN : IsOpen N)
    (hin : ∀ b ∈ N, ⊤ ≤ c b ⁻¹ᵁ A) (hz : ∀ r : Γ(X, A), DifferentiableOn ℂ (fun b => valAt' (c b) A r) N)
    {b₀ : V} (hb₀ : b₀ ∈ N) : HolAt c b₀ := by
  intro U hU
  have hmU : (c b₀) (default : PrimeSpectrum ℂ) ∈ U := (le_preimage_iff _ _).1 hU
  have hmA : (c b₀) (default : PrimeSpectrum ℂ) ∈ A := (le_preimage_iff _ _).1 (hin b₀ hb₀)
  obtain ⟨r, hrU, hr0⟩ := hA.exists_basicOpen_le (V := U) ⟨_, hmU⟩ hmA
  set M := {b ∈ N | valAt' (c b) A r ≠ 0} with hMdef
  have hMo : IsOpen M := (hz r).continuousOn.isOpen_inter_preimage hN isOpen_ne
  have hD : ∀ b ∈ M, ⊤ ≤ c b ⁻¹ᵁ X.basicOpen r := fun b hb =>
    (le_basicOpen_iff (c b) (hin b hb.1) r).2 hb.2
  have hb0M : b₀ ∈ M := ⟨hb₀, (le_basicOpen_iff (c b₀) (hin b₀ hb₀) r).1 ((le_preimage_iff _ _).2 hr0)⟩
  refine ⟨?_, fun f => ?_⟩
  · filter_upwards [hMo.mem_nhds hb0M] with b hb
    exact (hD b hb).trans (Scheme.Hom.preimage_mono _ hrU)
  · haveI := hA.isLocalization_basicOpen r
    obtain ⟨⟨hh, s⟩, hk⟩ := IsLocalization.surj (Submonoid.powers r) (X.presheaf.map (homOfLE hrU).op f)
    obtain ⟨k, hks⟩ := s.2
    dsimp only at hk
    have hval : ∀ b ∈ M, valAt' (c b) U f * valAt' (c b) A r ^ k = valAt' (c b) A hh := by
      intro b hb
      have e := congrArg (valAt' (c b) (X.basicOpen r)) hk
      rw [valAt'_mul, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_res (c b) hrU (hD b hb)] at e
      have e2 : ∀ x : Γ(X, A), valAt' (c b) (X.basicOpen r) (algebraMap Γ(X, A) Γ(X, X.basicOpen r) x) =
          valAt' (c b) A x := fun x => ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_res (c b) (X.basicOpen_le r) (hD b hb) x
      rw [e2, e2, ← hks] at e
      have e3 : valAt' (c b) A (r ^ k) = valAt' (c b) A r ^ k := map_pow (valHom (c b) A (hin b hb.1)) r k
      rw [e3] at e
      exact e
    have h1 : DifferentiableOn ℂ (fun b => valAt' (c b) A hh) M := (hz hh).mono fun b (hb : b ∈ M) => hb.1
    have h2 : DifferentiableOn ℂ (fun b => valAt' (c b) A r) M := (hz r).mono fun b (hb : b ∈ M) => hb.1
    have h3 : DifferentiableOn ℂ (fun b => valAt' (c b) A hh / valAt' (c b) A r ^ k) M :=
      diffOn_div h1 (h2.fun_pow k) fun b hb => pow_ne_zero _ hb.2
    refine ((h3.congr fun b hb => ?_).differentiableAt (hMo.mem_nhds hb0M))
    rw [eq_div_iff (pow_ne_zero _ hb.2)]
    exact hval b hb

variable {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

theorem genMap_germ {A : X.Opens} (hg : genPt ξ ∈ A) (q : Cpt ξ) (hq : q.1 ∈ A) (r : Γ(X, A)) :
    genMap ξ q (X.presheaf.germ A q.1 hq r) =
      (X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ).hom r := by
  have h1 := X.presheaf.germ_stalkSpecializes (U := A) (y := q.1) hq q.2
  have h3 : X.presheaf.germ A q.1 hq ≫ (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) =
      X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Scheme.stalkClosedPointTo ξ) h1)
  exact congrArg (fun f => f.hom r) h3

theorem valAt_section (hall : ∀ q : X, genPt ξ ⤳ q) {A : X.Opens} (hg : genPt ξ ∈ A) (r : Γ(X, A))
    {z : Sp ℂ ⟶ X} (hz : ⊤ ≤ z ⁻¹ᵁ A) :
    ValAt ξ z ((X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ).hom r) (valAt' z A r) := by
  have hc : centre z ∈ A := (le_preimage_iff z A).1 hz
  refine ⟨hall _, X.presheaf.germ A (centre z) hc r, genMap_germ hg ⟨centre z, hall _⟩ hc r, ?_⟩
  rw [valAt'_of _ _ hz]
  exact congrArg (fun φ => φ.hom r) (GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap z A hz)

theorem exists_hol_value (hall : ∀ q : X, genPt ξ ⤳ q) {N : Set V} {β : V → (Σ k, J k) → ℂ} {ζ : V → (Sp ℂ ⟶ X)}
    (c : (k : K) → J k) (hβ : ∀ p, DifferentiableOn ℂ (fun b => β b p) N)
    (hco : ∀ b ∈ N, CoordsAt ξ y (ζ b) (β b)) (hne : ∀ b ∈ N, ∀ k, β b ⟨k, c k⟩ ≠ 0) {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) :
    ∃ F : V → ℂ, DifferentiableOn ℂ F N ∧ ∀ b ∈ N, ValAt ξ (ζ b) a (F b) := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨j, rfl⟩ := ha
    refine ⟨fun b => ∏ k, β b ⟨k, j k⟩ / β b ⟨k, c k⟩, ?_, fun b hb => ?_⟩
    · have hS : ∀ S : Finset K, DifferentiableOn ℂ (fun b => ∏ k ∈ S, β b ⟨k, j k⟩ / β b ⟨k, c k⟩) N := by
        classical
        intro S
        induction S using Finset.induction_on with
        | empty => simpa using differentiableOn_const (c := (1 : ℂ))
        | insert k S hk ih =>
          simp only [Finset.prod_insert hk]
          exact (diffOn_div (hβ _) (hβ _) fun b hb => hne b hb k).fun_mul ih
      exact hS _
    · simp only [← Finset.prod_div_distrib]
      have hS : ∀ S : Finset K, ValAt ξ (ζ b) (∏ k ∈ S, y ⟨k, j k⟩ / y ⟨k, c k⟩)
          (∏ k ∈ S, β b ⟨k, j k⟩ / β b ⟨k, c k⟩) := by
        classical
        intro S
        induction S using Finset.induction_on with
        | empty => simpa using val_one (ξ := ξ) (z := ζ b) (hall _)
        | insert k S hk ih =>
          rw [Finset.prod_insert hk, Finset.prod_insert hk]
          refine val_mul ?_ ih
          obtain ⟨r, hr, hr'⟩ := ((hco b hb).2 k (c k) (isUnit_iff_ne_zero.2 (hne b hb k))).2 (j k)
          rwa [hr', mul_div_cancel_right₀ _ (hne b hb k)]
      exact hS _
  | algebraMap n =>
    refine ⟨fun _ => (n : ℂ), differentiableOn_const _, fun b _ => ?_⟩
    exact ⟨hall _, (n : X.presheaf.stalk (centre (ζ b))), by simp, map_intCast _ n⟩
  | add a a' _ _ h h' =>
    obtain ⟨F, hF, hv⟩ := h
    obtain ⟨F', hF', hv'⟩ := h'
    exact ⟨fun b => F b + F' b, hF.fun_add hF', fun b hb => val_add (hv b hb) (hv' b hb)⟩
  | mul a a' _ _ h h' =>
    obtain ⟨F, hF, hv⟩ := h
    obtain ⟨F', hF', hv'⟩ := h'
    exact ⟨fun b => F b * F' b, hF.fun_mul hF', fun b hb => val_mul (hv b hb) (hv' b hb)⟩

theorem isHolTo_of_coordsAt (htie : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hall : ∀ q : X, genPt ξ ⤳ q) {B : Set V} {β : V → (Σ k, J k) → ℂ} {ζ : V → (Sp ℂ ⟶ X)} (hB : IsOpen B)
    (hβ : ∀ p, DifferentiableOn ℂ (fun b => β b p) B) (hco : ∀ b ∈ B, CoordsAt ξ y (ζ b) (β b)) :
    IsHolTo B ζ := by
  refine isHolTo_of_holAt hB fun b₁ hb₁ => ?_
  choose c hc using (hco b₁ hb₁).1
  set N := {b ∈ B | ∀ k, β b ⟨k, c k⟩ ≠ 0} with hNdef
  have hNB : N ⊆ B := fun b hb => hb.1
  have hNo : IsOpen N := by
    refine isOpen_iff_mem_nhds.2 fun b hb => ?_
    have hk : ∀ᶠ t in 𝓝 b, ∀ k, β t ⟨k, c k⟩ ≠ 0 := eventually_all.2 fun k =>
      ((hβ _).continuousOn.continuousAt (hB.mem_nhds hb.1)).eventually_ne (hb.2 k)
    filter_upwards [hB.mem_nhds hb.1, hk] with t h1 h2 using ⟨h1, h2⟩
  have hb₁N : b₁ ∈ N := ⟨hb₁, fun k => (hc k).ne_zero⟩
  have hx0 : (∏ k, y ⟨k, c k⟩) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => ((hco b₁ hb₁).2 k (c k) (hc k)).1
  obtain ⟨A, hA, hAq⟩ := htie.affine c hx0
  have hin : ∀ b ∈ N, ⊤ ≤ ζ b ⁻¹ᵁ A := fun b hb =>
    (le_preimage_iff _ _).2 ((hAq _).2 ⟨hall _, in_chart (hall _) (hco b hb.1) hb.2⟩)
  have hg : genPt ξ ∈ A := (hall _).mem_open A.2 ((le_preimage_iff _ _).1 (hin b₁ hb₁N))
  refine holAt_of_isAffineOpen hA hNo hin (fun r => ?_) hb₁N
  have ha := (htie.ring c hx0 ((X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ).hom r)).2
    fun p hp => ⟨_, genMap_germ hg p ((hAq _).2 ⟨p.2, hp⟩) r⟩
  obtain ⟨F, hF, hFv⟩ := exists_hol_value hall c (fun p => (hβ p).mono hNB) (fun b hb => hco b hb.1)
    (fun b hb => hb.2) ha
  refine hF.congr fun b hb => ?_
  exact val_unique htie.gen (valAt_section hall hg r (hin b hb)) (hFv b hb)

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.ChartHol
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicCoordsOfGenericPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PeriodsHol

theorem isHolTo_of_coordsAt_family : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → ∀ (n : ℕ) (B : Set (Fin n → ℂ)) (w : (Fin n → ℂ) → (Σ k, J k) → ℂ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → DifferentiableOn ℂ w B → (∀ u ∈ B, CoordsAt ξ y (p u) (w u)) → IsHolTo B p := by
  intro X Ω _ ξ K _ J _ y htie hall n B w p hB hw hco
  exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.ChartHol.isHolTo_of_coordsAt htie hall hB
    (fun q => (differentiableOn_pi.1 hw) q) hco

end GlobalTheory.CompanionTheory.Ar.PeriodsHol
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicCoordsOfGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_coords_of_generic_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → ∀ (n : ℕ) (B : Set (Fin n → ℂ)) (w : (Fin n → ℂ) → (Σ k, J k) → ℂ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → DifferentiableOn ℂ w B → (∀ u ∈ B, CoordsAt ξ y (p u) (w u)) → IsHolTo B p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PeriodsHol.isHolTo_of_coordsAt_family | exact GlobalTheory.CompanionTheory.Ar.PeriodsHol.isHolTo_of_coordsAt_family | (intros; apply GlobalTheory.CompanionTheory.Ar.PeriodsHol.isHolTo_of_coordsAt_family <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodEigenFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodEigenFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.EigDir

open GlobalTheory.HolHom GlobalTheory.DerivEig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σK : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem isComb_iff_isCombAt (x : Sp ℂ ⟶ Xo.X) {n : ℕ} (c : Fin n → ℂ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G))
    (w : epsAt x ⟶ Xo.univ.t.G) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsComb c v w ↔ Formalism.L2.Pj.IsCombAt x (fun i => (v i).left) c w.left := by
  constructor
  · rintro ⟨u, hu, hw⟩
    exact ⟨u, hu, by rw [hw]⟩
  · rintro ⟨u, hu, hw⟩
    exact ⟨u, hu, Over.OverMorphism.ext hw.symm⟩

theorem isTanAt_of_isEigVec (x : Sp ℂ ⟶ Xo.X) (χ : 𝓞 E →+* ℂ) (v : epsAt x ⟶ Xo.univ.t.G)
    (h : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act x χ v) : Formalism.L2.Pj.IsTanAt x v.left :=
  ⟨Over.w v, h.1⟩

theorem isEigVec_of_isDerivAt0 (FU : FamilyUnif Xo σK ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (FU.Di i) ty P) (χ : 𝓞 E →+* ℂ) (τ : E →+* ℂ) (hχ : ∀ a : 𝓞 E, χ a = τ (a : E))
    (w : Fin g → ℂ) (hw : ∀ k, w k ≠ 0 → ty k = τ) (v : epsAt (FU.u i P) ⟶ Xo.univ.t.G)
    (hv : IsDerivAt0 (fun z => (FU.ex i P z).left) w v.left) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act (FU.u i P) χ v := by
  obtain ⟨h1, -, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo σK g ty FU i P hP
  have hhol : HolAt (fun z => (FU.ex i P z).left) 0 := holAt_of_isHolTo (isHolTo_ex FU i hP) (Set.mem_univ 0)
  have hv' := (isDerivAt0_iff _ _ _).1 hv
  refine ⟨(h1 _ _ hv).2, fun a => ?_⟩
  let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
    ContinuousLinearMap.pi fun k => ty k (a : E) • ContinuousLinearMap.proj k
  have e1 := hv'.comp (Xo.univ.t.act.act a).left
  have e2 : (fun t => (FU.ex i P t).left ≫ (Xo.univ.t.act.act a).left) = fun t => (FU.ex i P (L t)).left := by
    funext t
    rw [← Over.comp_left, ← FU.ex_lin i P hP a t]
    rfl
  rw [e2] at e1
  have e3 := isDerivAt_of_comp_linear hhol L e1
  have e4 : L w = χ a • w := by
    funext k
    by_cases hk : w k = 0
    · simp [L, hk]
    · simp [L, hw k hk, hχ a]
  rw [e4] at e3
  exact e3.unique (isDerivAt_epsMul hv' _)

end GlobalTheory.CompanionTheory.Ar.Flat.EigDir


open GlobalTheory.CompanionTheory.Ar.Flat.EigDir in
theorem GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σK : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σK ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (x : Sp ℂ ⟶ Xo.X) (χ : 𝓞 E →+* ℂ) (τ : E →+* ℂ) (n : ℕ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G)), IsPeriod (FU.Di i) ty P → x = FU.u i P → (∀ a : 𝓞 E, χ a = τ (a : E)) → IsEigFrame Xo.univ.t.act x χ v → ∃ V : Fin n → Fin g → ℂ, (∀ a u, IsDerivAt0 (fun z => (FU.ex i P z).left) u (v a).left ↔ u = V a) ∧ LinearIndependent ℂ V ∧ ∀ z, tyPart ty τ z ∈ Submodule.span ℂ (Set.range V) := by
  intro E _ _ _ H D l Xo σK g ty FU i P x χ τ n v hP hx hχ hF
  subst hx
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo σK g ty FU i P hP
  have ht : ∀ a, Formalism.L2.Pj.IsTanAt (FU.u i P) (v a).left := fun a => isTanAt_of_isEigVec _ χ _ (hF.1 a)
  choose V hV hVu using fun a => h3 _ (ht a)
  have comb : ∀ (c : Fin n → ℂ) (w : epsAt (FU.u i P) ⟶ Xo.univ.t.G),
      GlobalTheory.CompanionTheory.Ar.Fl.IsComb c v w ↔ IsDerivAt0 (fun z => (FU.ex i P z).left) (∑ k, c k • V k) w.left := fun c w =>
    (isComb_iff_isCombAt _ c v w).trans
      (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H D l Xo σK g ty FU i P hP n (fun k => (v k).left) V hV c w.left)
  refine ⟨V, fun a u => ⟨fun h => hVu a u h, fun h => h ▸ hV a⟩, ?_, fun z => ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun c hc => ?_
    obtain ⟨w, hw, -⟩ := (FU.ex_diff i P hP).1 0
    have hw' : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act (FU.u i P) χ w :=
      isEigVec_of_isDerivAt0 FU i P hP χ τ hχ 0 (fun k hk => absurd rfl hk) w hw
    obtain ⟨c₀, -, hu⟩ := hF.2 w hw'
    have a1 := hu c ((comb c w).2 (by rw [hc]; exact hw))
    have a2 := hu 0 ((comb 0 w).2 (by simpa using hw))
    intro k
    exact congrFun (a1.trans a2.symm) k
  · obtain ⟨w, hw, -⟩ := (FU.ex_diff i P hP).1 (tyPart ty τ z)
    have hw' : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act (FU.u i P) χ w :=
      isEigVec_of_isDerivAt0 FU i P hP χ τ hχ _ (fun k hk => ?_) w hw
    · obtain ⟨c, hc, -⟩ := hF.2 w hw'
      have e := (h3 _ (isTanAt_of_isEigVec _ χ _ hw')).unique ((comb c w).1 hc) hw
      rw [← e]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · by_contra hne
      exact hk (by simp [tyPart, hne])
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodEigenFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_eigen_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σK : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σK ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (x : Sp ℂ ⟶ Xo.X) (χ : 𝓞 E →+* ℂ) (τ : E →+* ℂ) (n : ℕ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G)), IsPeriod (FU.Di i) ty P → x = FU.u i P → (∀ a : 𝓞 E, χ a = τ (a : E)) → IsEigFrame Xo.univ.t.act x χ v → ∃ V : Fin n → Fin g → ℂ, (∀ a u, IsDerivAt0 (fun z => (FU.ex i P z).left) u (v a).left ↔ u = V a) ∧ LinearIndependent ℂ V ∧ ∀ z, tyPart ty τ z ∈ Submodule.span ℂ (Set.range V) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformisationLocalPeriod
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformisationLocalPeriod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_index_of_isPreconnected : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)), IsOpen B → IsPreconnected B → B.Nonempty → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ∃ i : Fin FU.n, ∀ b₀ ∈ B, ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (FU.Di i) ty B' P ∧ ∀ b ∈ B', FU.u i (P b) = y b := by
  intro E _ _ _ H D l Xo σ g ty FU m B y hB hpre hne hs hy
  let S : Fin FU.n → Set (Fin m → ℂ) := fun i => {b₀ | ∃ (B' : Set (Fin m → ℂ))
    (P : (Fin m → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧
      IsHolPeriods (FU.Di i) ty B' P ∧ ∀ b ∈ B', FU.u i (P b) = y b}
  have hopen : ∀ i, IsOpen (S i) := by
    intro i
    refine isOpen_iff_forall_mem_open.2 ?_
    rintro b₀ ⟨B', P, hB', hb₀, hsub, hP, hu⟩
    exact ⟨B', fun b hb => ⟨B', P, hB', hb, hsub, hP, hu⟩, hB', hb₀⟩
  have hcover : ∀ b ∈ B, ∃ i, b ∈ S i := by
    intro b hb
    obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := FU.lift m B y hB hs hy b hb
    exact ⟨i, B', P, hB', hb', hsub, hP, hu⟩
  have hdisj : ∀ i j b, b ∈ S i → b ∈ S j → i = j := by
    rintro i j b ⟨B₁, P₁, -, hb₁, -, hP₁, hu₁⟩ ⟨B₂, P₂, -, hb₂, -, hP₂, hu₂⟩
    exact FU.disj i j (P₁ b) (P₂ b) (hP₁.1 b hb₁) (hP₂.1 b hb₂) ((hu₁ b hb₁).trans (hu₂ b hb₂).symm)
  obtain ⟨b₁, hb₁⟩ := hne
  obtain ⟨i, hi⟩ := hcover b₁ hb₁
  have hsub : B ⊆ S i := by
    refine IsPreconnected.subset_left_of_subset_union (v := ⋃ j ∈ {j | j ≠ i}, S j) (hopen i)
      (isOpen_biUnion fun j _ => hopen j) ?_ ?_ ⟨b₁, hb₁, hi⟩ hpre
    · refine Set.disjoint_left.2 fun b hbi hbT => ?_
      obtain ⟨j, hj, hbj⟩ := Set.mem_iUnion₂.1 hbT
      exact hj (hdisj i j b hbi hbj).symm
    · intro b hb
      obtain ⟨j, hj⟩ := hcover b hb
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hj)
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hji, hj⟩)
  exact ⟨i, fun b₀ hb₀ => hsub hb₀⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformisationLocalPeriodStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_uniformisation_local_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)), IsOpen B → IsPreconnected B → B.Nonempty → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ∃ i : Fin FU.n, ∀ b₀ ∈ B, ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (FU.Di i) ty B' P ∧ ∀ b ∈ B', FU.u i (P b) = y b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_index_of_isPreconnected | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_index_of_isPreconnected | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_index_of_isPreconnected <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartIntegralPointAltBis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_integral_point_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (lab : CMType H ⊕ CMType H) (m : ℕ) (s : Fin m → 𝔐.Li), 𝔐.IsLinPtOf z P MV A → (𝔐.dR lab).IsFrameAt s ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ → ∃ sL : Fin m → V, IsValues 𝔐 z P MV s sL ∧ LinearIndependent L sL ∧ Submodule.span L (Set.range sL) = eigSp A.ρ (A.σ lab) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L _ _ z P V _ _ _ _ MV A lab m s hLin hfr
  obtain ⟨hact, hlab, -⟩ := hLin
  have hlat := (GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c (𝓞 c.F) (algebraMap _ _) Y S Ω K J y 𝔐
    (FaithfulSMul.algebraMap_injective _ _) ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩
    (fun r hr => FrameVal.not_inFibre _ _ r hr)).2.2
  exact FrameVal.values_core 𝔐 _ P.tK P.m MV A.ρ A.σ A.σ_bij.1 hact hlab hlat lab s hfr
end
