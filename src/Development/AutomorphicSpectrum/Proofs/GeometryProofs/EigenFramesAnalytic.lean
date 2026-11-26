module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameFunctionCompare
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GagaLineGeneratorEmbedding
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentPointValueHolomorphic

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointFrameSpecialization
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointFrameSpecialization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FrameVal

theorem exists_framed_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (y : Sp ℂ ⟶ Xo.XF c) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → y ≫ pullback.snd _ _ = spMap σ → (Z.eig τ).IsFrameAt b₁ ⟨_, h⟩ → (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt b₂ ⟨_, h⟩ → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed Set.univ τ σ y v w ∧ (∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w' := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ b₁ b₂ y h hO hτ _ hy hf₁ hf₂
  haveI : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hO hτ
  have hfib : (⟨centre (y ≫ Y.j), h⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib :=
    ⟨Y.jQ (y (IsLocalRing.closedPoint ℂ)), by simp only [Model.j, centre, Scheme.Hom.comp_apply]⟩
  obtain ⟨g, b, hb, hS⟩ := h3 _ hfib
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists Y.X Y.t.G ℂ (y ≫ Y.j)
  obtain ⟨ev, hev, -, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M ℂ (y ≫ Y.j) h ER MR Z.gen inferInstance
  have hval : ∀ {n : ℕ} (τ' : E →+* ℂ) (e : Fin n → Z.V), (Z.eig τ').IsFrameAt e ⟨centre (y ≫ Y.j), h⟩ →
      ∀ i, ∃ w, Z.M.ValAt (y ≫ Y.j) (e i) (MR.pt w) := fun τ' e hf i => by
    have hmem : e i ∈ Z.eig τ' ⟨centre (y ≫ Y.j), h⟩ := by
      rw [hf.2]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact ⟨ev ⟨e i, hmem.1⟩, (hev _ _).2 ⟨hmem.1, rfl⟩⟩
  choose w₁ hw₁ using hval τ b₁ hf₁
  choose w₂ hw₂ using hval _ b₂ hf₂
  choose v hv using fun i => exists_sameVec_left Y y (MR.pt (w₁ i))
  choose w hw using fun j => exists_sameVec_left Y y (MR.pt (w₂ j))
  obtain ⟨hL₁, hL₂⟩ := GlobalTheory.CompanionTheory.Ar.LocFrames.lieMult_at y σ τ hy hτ
  refine ⟨v, w, ⟨hy, Set.subset_univ _, ?_, ?_⟩, fun i => ⟨_, hw₁ i, hv i⟩, fun j => ⟨_, hw₂ j, hw j⟩⟩
  · exact GlobalTheory.CompanionTheory.Ar.LocFrames.isEigFrame_of_values Z σ y τ D.p b₁ v (fun i => MR.pt (w₁ i)) h hO.2.2 hy hL₁
      ⟨g, b, hb, hS τ⟩ hf₁ hw₁ hv
  · exact GlobalTheory.CompanionTheory.Ar.LocFrames.isEigFrame_of_values Z σ y _ D.q b₂ w (fun j => MR.pt (w₂ j)) h hO.2.2 hy hL₂
      ⟨g, b, hb, hS _⟩ hf₂ hw₂ hw

end GlobalTheory.CompanionTheory.Ar.FrameVal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointFrameSpecializationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_frame_specialization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (y : Sp ℂ ⟶ Xo.XF c) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → y ≫ pullback.snd _ _ = spMap σ → (Z.eig τ).IsFrameAt b₁ ⟨_, h⟩ → (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt b₂ ⟨_, h⟩ → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed Set.univ τ σ y v w ∧ (∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FrameVal.exists_framed_values | exact GlobalTheory.CompanionTheory.Ar.FrameVal.exists_framed_values | (intros; apply GlobalTheory.CompanionTheory.Ar.FrameVal.exists_framed_values <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValueAlongStalkSurjection
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValueAlongStalkSurjection
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

namespace GlobalTheory.CompanionTheory.Ar.Flat.ValLift

theorem valAt_of_stalkMap_surjective : ∀ (X₀ X' : Scheme.{0}) (Ω R : Type) [Field Ω] [CommRing R] [IsLocalRing R]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (π : X' ⟶ X₀)
    (z : Spec (CommRingCat.of R) ⟶ X') (a : Ω) (r : R), ξ' ≫ π = ξ →
    Function.Surjective (π.stalkMap (centre z)).hom → ValAt ξ' z a r → ValAt ξ (z ≫ π) a r := by
  intro X₀ X' Ω R _ _ _ ξ ξ' π z a r hξ hsurj hv
  subst hξ
  obtain ⟨h', s', hs'a, hs'r⟩ := hv
  obtain ⟨s, hs⟩ := hsurj s'
  have hsp : genPt (ξ' ≫ π) ⤳ centre (z ≫ π) := h'.map π.continuous
  refine ⟨hsp, s, ?_, ?_⟩
  · rw [← hs'a, ← hs]
    have key : X₀.presheaf.stalkSpecializes hsp ≫ AlgebraicGeometry.Scheme.stalkClosedPointTo (ξ' ≫ π) =
        π.stalkMap (centre z) ≫ X'.presheaf.stalkSpecializes h' ≫ AlgebraicGeometry.Scheme.stalkClosedPointTo ξ' := by
      rw [AlgebraicGeometry.Scheme.stalkClosedPointTo_comp]
      exact AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap_assoc π (genPt ξ') (centre z) h'
        (AlgebraicGeometry.Scheme.stalkClosedPointTo ξ')
    show (CommRingCat.Hom.hom (X₀.presheaf.stalkSpecializes hsp ≫
      AlgebraicGeometry.Scheme.stalkClosedPointTo (ξ' ≫ π))) s = _
    rw [key]
    rfl
  · rw [← hs'r, ← hs, AlgebraicGeometry.Scheme.stalkClosedPointTo_comp]
    rfl

end GlobalTheory.CompanionTheory.Ar.Flat.ValLift
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValueAlongStalkSurjectionStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_along_stalk_surjection : ∀ (X₀ X' : Scheme.{0}) (Ω R : Type) [Field Ω] [CommRing R] [IsLocalRing R] (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (π : X' ⟶ X₀) (z : Spec (CommRingCat.of R) ⟶ X') (a : Ω) (r : R), ξ' ≫ π = ξ → Function.Surjective (π.stalkMap (centre z)).hom → ValAt ξ' z a r → ValAt ξ (z ≫ π) a r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ValLift.valAt_of_stalkMap_surjective | exact GlobalTheory.CompanionTheory.Ar.Flat.ValLift.valAt_of_stalkMap_surjective | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ValLift.valAt_of_stalkMap_surjective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameNearGenericPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameNearGenericPoint
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen

theorem mem_regAt_genPt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hξ : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ (⟨genPt ξ, specializes_rfl⟩ : Cpt ξ) := by
  obtain ⟨g, hg⟩ := hξ.bij.2 a
  refine ⟨g, ?_⟩
  have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  show (X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫
    Scheme.stalkClosedPointTo ξ).hom g = a
  rw [e]
  exact hg

theorem exists_open_forall_mem_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hξ : IsCptGen ξ) (S : Finset Ω) :
    ∃ W : X.Opens, genPt ξ ∈ W ∧ ∀ q : Cpt ξ, q.1 ∈ W → ∀ a ∈ S, a ∈ regAt ξ q := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, fun _ _ _ h => absurd h (Finset.notMem_empty _)⟩
  | insert a S _ ih =>
    obtain ⟨W, hW, H⟩ := ih
    obtain ⟨U, hU, HU⟩ := exists_open_mem_regAt ξ ⟨genPt ξ, specializes_rfl⟩ a (mem_regAt_genPt hξ a)
    refine ⟨W ⊓ U, ⟨hW, hU⟩, fun q hq c hc => ?_⟩
    rcases Finset.mem_insert.1 hc with rfl | hc
    · exact HU q hq.2
    · exact H q hq.1 c hc

theorem span_regAt_le {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (q : Cpt ξ) (b e : Fin r → E) (M : Fin r → Fin r → Ω)
    (hM : ∀ i, ∑ j, M i j • e j = b i) (hreg : ∀ i j, M i j ∈ regAt ξ q) :
    Submodule.span (regAt ξ q) (Set.range b) ≤ Submodule.span (regAt ξ q) (Set.range e) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [← hM i]
  refine sum_mem fun j _ => ?_
  exact Submodule.smul_mem _ (⟨M i j, hreg i j⟩ : regAt ξ q) (Submodule.subset_span ⟨j, rfl⟩)

theorem isFrameAt_near_genPt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E) (b : Fin r → E), IsCptGen ξ → (⟨genPt ξ, specializes_rfl⟩ : Cpt ξ) ∈ T → L.IsVBOn T r V → LinearIndependent Ω b → Submodule.span Ω (Set.range b) = V → ∃ W : X.Opens, genPt ξ ∈ W ∧ ∀ q ∈ T, q.1 ∈ W → L.IsFrameAt b q := by
  classical
  intro X Ω _ ξ E _ _ L T r V b hξ hT hVB hb hspan
  obtain ⟨U, hU, e, he, hfr⟩ := hVB _ hT
  have hbe : ∀ i, ∃ c : Fin r → Ω, ∑ j, c j • e j = b i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (he ▸ hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
  have heb : ∀ i, ∃ c : Fin r → Ω, ∑ j, c j • b j = e i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (hspan ▸ he ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose M hM using hbe
  choose N hN using heb
  let S : Finset Ω := Finset.univ.image (fun ij : Fin r × Fin r => M ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin r × Fin r => N ij.1 ij.2)
  obtain ⟨W, hW, H⟩ := exists_open_forall_mem_regAt hξ S
  refine ⟨U ⊓ W, ⟨hU, hW⟩, fun q hq hqW => ⟨hb, ?_⟩⟩
  have hMr : ∀ i j, M i j ∈ regAt ξ q := fun i j => H q hqW.2 _
    (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))
  have hNr : ∀ i j, N i j ∈ regAt ξ q := fun i j => H q hqW.2 _
    (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))
  rw [(hfr q hq hqW.1).2]
  exact le_antisymm (span_regAt_le q e b N hN hNr) (span_regAt_le q b e M hM hMr)

end GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameNearGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_near_generic_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E) (b : Fin r → E), IsCptGen ξ → (⟨genPt ξ, specializes_rfl⟩ : Cpt ξ) ∈ T → L.IsVBOn T r V → LinearIndependent Ω b → Submodule.span Ω (Set.range b) = V → ∃ W : X.Opens, genPt ξ ∈ W ∧ ∀ q ∈ T, q.1 ∈ W → L.IsFrameAt b q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen.isFrameAt_near_genPt | exact GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen.isFrameAt_near_genPt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen.isFrameAt_near_genPt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFramesAnalytic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GenOnModel

theorem isPreimmersion_fst {O K : Type} [CommRing O] [Field K] (β : O →+* K) {X : Scheme.{0}} (s : X ⟶ Sp O)
    (hβ : Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : K, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) :
    IsPreimmersion (pullback.fst s (spMap β)) := by
  obtain ⟨hi, -, hx⟩ := hβ
  have hdom : IsDomain O := hi.isDomain β
  letI : Algebra O K := β.toAlgebra
  haveI : FaithfulSMul O K := (faithfulSMul_iff_algebraMap_injective O K).2 hi
  have hloc : IsLocalization (nonZeroDivisors O) K := by
    refine IsFractionRing.of_field O K fun z => ?_
    obtain ⟨a, b, hb, e⟩ := hx z
    exact ⟨a, b, by
      change z = β a / β b
      rw [← e]; field_simp⟩
  have h : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (R := O) (S := K) (nonZeroDivisors O)
  infer_instance

theorem genPt_comp {X X' : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) (π : X ⟶ X') :
    genPt (ξ ≫ π) = π (genPt ξ) := rfl

end GlobalTheory.CompanionTheory.Ar.Flat.GenOnModel

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GenOnModel

theorem exists_gen_of_unitAn : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → Z.IsGeom → IsUnitAn τ σ Φ → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → ∃ (f : Z.Ω) (κ : ℂ) (W : (Xo.XF c).Opens), κ ≠ 0 ∧ genPt Z.ξ₀ ∈ W ∧ IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (f • exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂) Z.genFib ∧ ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap σ → ⊤ ≤ y ⁻¹ᵁ W → Set.range y ⊆ U → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed U τ σ y v w ∧ ((∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') ∧ ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) f (κ * Φ y v w) := by
  intro hRes hGaga E _ _ _ H D l Xo c O _ β Y U Z τ σ Φ b₁ b₂ hβ hpq hτ hσ hgeom hΦ hi₁ hs₁ hi₂ hs₂
  classical
  have hξ : IsCptGen (Z.ξ₀ ≫ Y.j) := Z.gen
  obtain ⟨hA, hB, -, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hβ hτ
  have hη : (⟨genPt (Z.ξ₀ ≫ Y.j), specializes_rfl⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib := ⟨Y.jQ (genPt Z.ξ₀), rfl⟩
  obtain ⟨W₁, hW₁, hf₁⟩ := GlobalTheory.T.frame_near_generic_point _ _ _ _ (Z.eig τ) Z.genFib D.p _ b₁ hξ hη hA hi₁ hs₁
  obtain ⟨W₂, hW₂, hf₂⟩ := GlobalTheory.T.frame_near_generic_point _ _ _ _ (Z.eig (ComplexEmbedding.conjugate τ)) Z.genFib D.q _ b₂ hξ hη hB hi₂ hs₂
  obtain ⟨hwA, ha⟩ := GlobalTheory.T.wedge_lattice_generator _ _ _ _ (Z.eig τ) D.p b₁ _ (hf₁ _ hη hW₁)
  obtain ⟨hwB, hb⟩ := GlobalTheory.T.wedge_lattice_generator _ _ _ _ (Z.eig (ComplexEmbedding.conjugate τ)) D.q b₂ _ (hf₂ _ hη hW₂)
  have hcoef : IsCoeffAt (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q
      (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)
      ⟨genPt (Z.ξ₀ ≫ Y.j), specializes_rfl⟩ 1 :=
    ⟨1, 1, one_ne_zero, one_ne_zero, by rw [one_smul]; exact hwA, by rw [one_smul]; exact hwB, by simp⟩
  obtain ⟨hLvb, hLgen, hLfr⟩ := GlobalTheory.T.wedge_line_lattice_vector_bundle _ _ _ _ (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q _ _
    Z.genFib _ _ hA hB ha hb ⟨_, hη, 1, hcoef⟩
  have hW₀gen : ∀ x ∈ Z.genFib, x.1 ∈ W₁ ⊓ W₂ → (lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q
      (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).IsGenAt x 1 := fun x hx hxW => by
    have := hLfr x hx b₁ b₂ 1 1 (hf₁ x hx hxW.1) (hf₂ x hx hxW.2) (by rw [one_smul]) (by rw [one_smul])
    simpa using this
  have hpre : IsPreimmersion (pullback.fst Y.s (spMap β)) := isPreimmersion_fst β Y.s hβ
  obtain ⟨hnoeth, X', f, d, W', jW, hiso, hjW, hfP, hsP, hsm, hsnc⟩ := GlobalTheory.T.exists_resolution_generic_fibre hRes E H D l Xo c O β Y hβ
  have hjQo : IsOpenImmersion Y.jQ := Y.jQ_open
  have hmono : Mono Y.j := by
    unfold Model.j
    infer_instance

  have hsurj := GlobalTheory.T.stalk_surjective_open_immersion _ _ _ _ (pullback.fst Y.s (spMap β)) f W' jW Y.jQ hpre hjQo hiso hjW
  obtain ⟨π, hπ⟩ : ∃ π, π = f ≫ pullback.fst Y.s (spMap β) := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = f ≫ pullback.snd Y.s (spMap β) := ⟨_, rfl⟩
  rw [← hπ] at hsurj
  rw [← hs'] at hsP hsm hsnc
  have hιf : inv jW ≫ W'.ι ≫ f = Y.jQ := by rw [← hjW, IsIso.inv_hom_id_assoc]
  have hιf' : ∀ {Z' : Scheme.{0}} (t : pullback Y.s (spMap β) ⟶ Z'), inv jW ≫ W'.ι ≫ f ≫ t = Y.jQ ≫ t := by
    intro Z' t
    rw [← hιf]; simp only [Category.assoc]
  have hιπ : inv jW ≫ W'.ι ≫ π = Y.j := by rw [hπ, hιf']; rfl
  have hιs : inv jW ≫ W'.ι ≫ s' = pullback.snd _ _ := by rw [hs', hιf', Y.jQ_over]
  obtain ⟨ξ', hξ'⟩ : ∃ ξ', ξ' = Z.ξ₀ ≫ inv jW ≫ W'.ι := ⟨_, rfl⟩
  have h1 : ξ' ≫ f = Z.ξ₀ ≫ Y.jQ := by simp only [hξ', Category.assoc, hιf]
  have h2 : ξ' ≫ π = Z.ξ₀ ≫ Y.j := by simp only [hξ', Category.assoc, hιπ]
  have h3 : ξ' ≫ s' = spMap Z.inc := by
    simp only [hξ', Category.assoc, hιs]; exact Z.over_inc
  have hgW' : genPt ξ' ∈ W' := by
    rw [hξ', ← Category.assoc, genPt_comp]
    exact (genPt (Z.ξ₀ ≫ inv jW)).2
  have hsm' : Smooth s' := SmoothOfRelativeDimension.smooth d s'
  have hξg : IsCptGen ξ' := GlobalTheory.T.generic_of_smooth_surjective c.F _ _ _ _ ξ' π s' hsm' h2 hξ (hsurj _ hgW')
  have hdom : Dominates ξ' (Z.ξ₀ ≫ Y.j) π (RingHom.id Z.Ω) := by
    unfold Dominates
    rw [h2]
    simp
  obtain ⟨L, hLd⟩ : ∃ L, L = lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q
      (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂) := ⟨_, rfl⟩
  rw [← hLd] at hLvb hLgen hW₀gen
  have hcpt : ∀ p' : Cpt ξ', ∃ h : genPt (Z.ξ₀ ≫ Y.j) ⤳ π p'.1, (⟨π p'.1, h⟩ : Cpt _) ∈ Z.genFib := fun p' => by
    obtain ⟨h, -, -⟩ := pull_reg_and_gen _ _ _ _ _ ξ' π (RingHom.id _) hdom p'
    exact ⟨h, ⟨f p'.1, by subst hπ; rfl⟩⟩
  have hL'vb : (L.pull ξ' π (AddMonoidHom.id _)).IsVB 1 ⊤ := by
    intro p' _
    obtain ⟨h, hT⟩ := hcpt p'
    obtain ⟨N, hN, bb, hbb, hfr⟩ := hLvb _ hT
    refine ⟨π ⁻¹ᵁ N, hN, bb, hbb, fun q' _ hq' => ?_⟩
    obtain ⟨h', hT'⟩ := hcpt q'
    have hfr' := hfr _ hT' hq'
    exact GlobalTheory.T.lattice_basis_pullback_dominant _ _ (Z.ξ₀ ≫ Y.j) _ _ ξ' π (RingHom.id _) Z.Ω Z.Ω (AddMonoidHom.id _) hdom
      (fun a e => rfl) L 1 bb q' h' hfr'.1 hfr'
  obtain ⟨W, hWd⟩ : ∃ W : X'.Opens, W = (π ⁻¹ᵁ (W₁ ⊓ W₂)) ⊓ W' := ⟨_, rfl⟩
  have hWW' : W ≤ W' := by rw [hWd]; exact inf_le_right
  have hgW : genPt ξ' ∈ W := by
    rw [hWd]
    refine ⟨?_, hgW'⟩
    show π (genPt ξ') ∈ W₁ ⊓ W₂
    rw [← genPt_comp, h2]
    exact ⟨hW₁, hW₂⟩
  have hgenW : ∀ p : Cpt ξ', p.1 ∈ W → (L.pull ξ' π (AddMonoidHom.id _)).IsGenAt p 1 := fun p hp => by
    obtain ⟨h, hr, hg⟩ := pull_reg_and_gen _ _ _ _ _ ξ' π (RingHom.id _) hdom p
    have hpW : π p.1 ∈ W₁ ⊓ W₂ := by rw [hWd] at hp; exact hp.1
    obtain ⟨h', hT⟩ := hcpt p
    exact hg L 1 (hW₀gen _ hT hpW)

  obtain ⟨Q, hQ⟩ : ∃ Q : ∀ y : Sp ℂ ⟶ Xo.XF c, Vecs y D.p → Vecs y D.q → Prop, ∀ y v w, Q y v w ↔
      (IsFramed Set.univ τ σ y v w ∧ ((∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧
        ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w')) := ⟨_, fun _ _ _ => Iff.rfl⟩
  have hex : ∀ y : Sp ℂ ⟶ Xo.XF c, ∃ r : ℂ, (∃ v w, Q y v w) → ∃ v w, Q y v w ∧ r = Φ y v w := fun y => by
    by_cases h : ∃ v w, Q y v w
    · obtain ⟨v, w, hq⟩ := h
      exact ⟨Φ y v w, fun _ => ⟨v, w, hq, rfl⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Φ₀ hΦ₀ using hex
  have hexF : ∀ y' : Sp ℂ ⟶ X', ∃ r : ℂ, ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ Y.j = y' ≫ π → r = Φ₀ y := fun y' => by
    by_cases h : ∃ y : Sp ℂ ⟶ Xo.XF c, y ≫ Y.j = y' ≫ π
    · obtain ⟨y, hy⟩ := h
      refine ⟨Φ₀ y, fun y₂ h₂ => ?_⟩
      rw [(cancel_mono Y.j).1 (hy.trans h₂.symm)]
    · exact ⟨0, fun y hy => absurd ⟨y, hy⟩ h⟩
  choose F hF using hexF
  have H1 : ∀ (y' : Sp ℂ ⟶ X') (y : Sp ℂ ⟶ Xo.XF c), y' ≫ s' = spMap σ → ⊤ ≤ y' ⁻¹ᵁ W → genPt ξ' ⤳ centre y' →
      y ≫ Y.j = y' ≫ π → y ≫ pullback.snd _ _ = spMap σ → ∃ (v : Vecs y D.p) (w : Vecs y D.q),
        IsFramed Set.univ τ σ y v w ∧ ((∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧
        ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') ∧ F y' = Φ y v w := by
    intro y' y _ hW hsp hy hys
    have hc : centre (y ≫ Y.j) = π (centre y') := by rw [hy]; rfl
    have h₀ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := by
      rw [hc, ← h2, genPt_comp]
      exact hsp.map π.continuous
    have hT : (⟨_, h₀⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib := ⟨Y.jQ (y (IsLocalRing.closedPoint ℂ)), rfl⟩
    have hcW : centre y' ∈ W := hW (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
    have hxW : centre (y ≫ Y.j) ∈ W₁ ⊓ W₂ := by
      rw [hc]
      rw [hWd] at hcW
      exact hcW.1
    obtain ⟨v, w, hf, hv, hw⟩ := GlobalTheory.T.point_frame_specialization E H D l Xo c O β Y U Z τ σ b₁ b₂ y h₀ hβ hτ hσ hys
      (hf₁ _ hT hxW.1) (hf₂ _ hT hxW.2)
    obtain ⟨v₂, w₂, hq, hr⟩ := hΦ₀ y ⟨v, w, (hQ y v w).2 ⟨hf, hv, hw⟩⟩
    obtain ⟨q1, q2⟩ := (hQ y v₂ w₂).1 hq
    exact ⟨v₂, w₂, q1, q2, by rw [hF y' y hy, hr]⟩
  have hπs : π ≫ Y.s = s' ≫ spMap β := by
    rw [hπ, hs', Category.assoc, Category.assoc, pullback.condition]
  have hj1 : jW ≫ Y.j = W'.ι ≫ π := by
    rw [hπ]
    show jW ≫ Y.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, hjW, Category.assoc]
  have hj2 : jW ≫ pullback.snd _ _ = W'.ι ≫ s' := by
    rw [hs', ← Y.jQ_over, ← Category.assoc, hjW, Category.assoc]
  letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
  have hconst : ConstClosed c.F Z.Ω := fun a ha => by
    obtain ⟨p, hp0, hp⟩ := ha
    obtain ⟨x, rfl⟩ := hgeom a ⟨p, hp0, by rwa [Polynomial.aeval_def] at hp⟩
    exact ⟨x, 1, one_ne_zero, by simp; rfl⟩
  subst hLd
  have hext := GlobalTheory.T.eigen_frame_function_compare E H D l Xo c O β Y U Z τ σ Φ b₁ b₂ X' π s' d ξ' W' W jW F hβ hpq hτ hσ hΦ
    hi₁ hs₁ hi₂ hs₂ hπs hsm hsnc h2 hξg hj1 hj2 hWW' H1 hgenW
  obtain ⟨f₀, κ, hκ, hgen, hval⟩ := GlobalTheory.T.gaga_line_generator_embedding hGaga c.F σ X' s' Z.Ω ξ' _ W F hsP hsm' h3 hξg hconst hL'vb hgW
    hgenW hext
  have hnorm : NormalCpt (Z.ξ₀ ≫ Y.j) := GlobalTheory.CompanionTheory.Ar.XR.normalCpt_of_isCptGen hξ Y.normal
  have hall := GlobalTheory.T.proper_pullback_line_bundle _ _ _ _ (Z.ξ₀ ≫ Y.j) (Z.ξ₀ ≫ Y.jQ) ξ' (pullback.fst Y.s (spMap β)) f _ Z.genFib f₀ hpre hfP
    hnoeth (by simp [Model.j]) h1 hξ hnorm (fun x => Iff.rfl) hLvb (by rw [← hπ]; exact hgen)
  have hf0 : f₀ ≠ 0 := (hall _ hη).1
  refine ⟨f₀, κ, Y.j ⁻¹ᵁ (W₁ ⊓ W₂), hκ, ⟨hW₁, hW₂⟩, ⟨smul_ne_zero hf0 ha, hb, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨-, α, β', hα, hβ', hwa, hwb, e⟩ := (hLgen x hx f₀).1 (hall x hx)
    refine ⟨α / f₀, β', div_ne_zero hα hf0, hβ', ?_, hwb, ?_⟩
    · rw [smul_smul, div_mul_cancel₀ _ hf0]
      exact hwa
    · rw [_root_.one_mul, ← e]
      field_simp
  · intro y hys hyW hyU
    obtain ⟨y', hy'⟩ : ∃ y', y' = y ≫ inv jW ≫ W'.ι := ⟨_, rfl⟩
    have e1 : y' ≫ π = y ≫ Y.j := by simp only [hy', Category.assoc, hιπ]
    have e2 : y' ≫ s' = spMap σ := by simp only [hy', Category.assoc, hιs]; exact hys
    have hpt : ∀ pt, y' pt ∈ W := fun pt => by
      have hp : y pt ∈ Y.j ⁻¹ᵁ (W₁ ⊓ W₂) := hyW (show pt ∈ (⊤ : (Sp ℂ).Opens) from trivial)
      rw [hWd]
      refine ⟨?_, ?_⟩
      · show π (y' pt) ∈ W₁ ⊓ W₂
        have : π (y' pt) = Y.j (y pt) := by
          rw [← Scheme.Hom.comp_apply, e1, Scheme.Hom.comp_apply]
        rw [this]
        exact hp
      · rw [hy']
        exact ((y ≫ inv jW) pt).2
    have hyW' : ⊤ ≤ y' ⁻¹ᵁ W := fun pt _ => hpt pt
    have hsp : genPt ξ' ⤳ centre y' := by
      rw [hξ', hy']
      exact ((Z.closure _).1 (hyU ⟨IsLocalRing.closedPoint ℂ, rfl⟩)).map (inv jW ≫ W'.ι).continuous
    obtain ⟨v, w, hf, hv, hFe⟩ := H1 y' y e2 hyW' hsp e1.symm hys
    refine ⟨v, w, ⟨hf.1, hyU, hf.2.2.1, hf.2.2.2⟩, hv, ?_⟩
    have hv' := hval y' e2 hyW' hsp
    have hs := hsurj (centre y') (hWW' (hpt _))
    have h := GlobalTheory.T.value_along_stalk_surjection _ _ _ _ _ ξ' π y' f₀ _ h2 hs hv'
    rw [e1, hFe] at h
    exact h

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFramesAnalyticStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_frames_analytic : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → Z.IsGeom → IsUnitAn τ σ Φ → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → ∃ (f : Z.Ω) (κ : ℂ) (W : (Xo.XF c).Opens), κ ≠ 0 ∧ genPt Z.ξ₀ ∈ W ∧ IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (f • exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂) Z.genFib ∧ ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap σ → ⊤ ≤ y ⁻¹ᵁ W → Set.range y ⊆ U → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed U τ σ y v w ∧ ((∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') ∧ ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) f (κ * Φ y v w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_unitAn | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_unitAn | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_unitAn <;> assumption)
end
