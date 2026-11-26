module

public import Development.EtaleCohomology.EtaleSheaves.LeafVanStalk
public import Development.EtaleCohomology.EtaleSheaves.LeafNormalModelPf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafReducedSmooth
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.QuasiFiniteDescent

def QFChain {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Sp k) (R : Subalgebra k Ω)
    {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) (e : C0 ⟶ X) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2)
    (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) : Prop :=
  IsSeparated q ∧ QuasiCompact q ∧ SmoothOfRelativeDimension 1 q ∧
  IsSeparated (d1 ≫ q) ∧ QuasiCompact (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
  IsSeparated (d2 ≫ d1 ≫ q) ∧ QuasiCompact (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
  LocallyQuasiFinite (pullback.lift q f hf.symm) ∧ LocallyQuasiFinite d1 ∧ LocallyQuasiFinite d2 ∧
  IsPullback v0 c0 q (toR R) ∧ IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (toR R) ∧
  IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (toR R) ∧
  γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2 ∧ v0 ≫ f = e

def LeafQFOmega : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    ∀ (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))), genericPoint X ∈ Set.range e →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
      Surjective γ1 → Surjective γ2 →
    LocallyQuasiFinite (pullback.lift c0 e he.symm) ∧ LocallyQuasiFinite γ1 ∧ LocallyQuasiFinite γ2

def LeafDescendPreMap : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
      f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) ∧
      LateralTheory.E.LeafDescendChainPf.PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2 ∧ v0 ≫ f = e

def LeafSpreadQF : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG → ∀ {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω)
    (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) (e : C0 ⟶ X) (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))),
    IsCurve c0 → IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    LocallyQuasiFinite (pullback.lift c0 e he.symm) → LocallyQuasiFinite γ1 → LocallyQuasiFinite γ2 →
    ∀ {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (f : D0 ⟶ X) (v0 : C0 ⟶ D0)
    (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2), f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) →
    LateralTheory.E.LeafDescendChainPf.PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2 → v0 ≫ f = e →
    ∃ (R' : Subalgebra k Ω), R'.FG ∧ ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1)
      (f' : E0 ⟶ X) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1) (w2 : C2 ⟶ E2)
      (hf' : f' ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k R'))),
      QFChain p R' c0 γ1 γ2 e q' e1 e2 f' w0 w1 w2 hf'

def LeafReducedSmooth : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {D : Scheme.{0}} (q : D ⟶ Sp R), SmoothOfRelativeDimension 1 q → AlgebraicGeometry.IsReduced D

theorem integral_of (hI : LeafIrred) (hR : LeafReducedSmooth) {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (R : Subalgebra k Ω) (hFG : R.FG) {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D)
    (hc : IsCurve c) (hs : SmoothOfRelativeDimension 1 q) (hp : IsPullback v c q (toR R)) : IsIntegral D := by
  have := hI k Ω R hFG c q v hc hs hp
  have := hR k Ω R hFG q hs
  exact isIntegral_of_irreducibleSpace_of_isReduced D

theorem goal_of (hQ : LeafQFOmega) (hP : LeafDescendPreMap) (hS : LeafSpreadQF) (hI : LeafIrred)
    (hR : LeafReducedSmooth) (hD : LeafDimBound) : LateralTheory.E.LeafGeoVV2Cut.LeafDescendQF := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hgen C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨q0, q1, q2⟩ := hQ k p Ω hdim c0 e hc0 he hgen C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨R, hFG, D0, D1, D2, q, d1, d2, f, v0, v1, v2, hf, hpre, hve⟩ :=
    hP k p Ω c0 e hc0 he C1 C2 γ1 γ2 h1 h2
  obtain ⟨R', hFG', E0, E1, E2, q', e1, e2, f', w0, w1, w2, hf', hc⟩ :=
    hS k p Ω R hFG c0 γ1 γ2 e he hc0 h1 h2 q0 q1 q2 q d1 d2 f v0 v1 v2 hf hpre hve
  obtain ⟨a1, a2, a3, b1, b2, b3, c1, c2, c3, l0, l1, l2, P0, P1, P2, m1, m2, m3⟩ := hc
  exact ⟨R', hFG', E0, E1, E2, q', e1, e2, f', w0, w1, w2, hf', a1, a2, a3, b1, b2, b3, c1, c2, c3,
    integral_of hI hR R' hFG' c0 q' w0 hc0 a3 P0, integral_of hI hR R' hFG' (γ1 ≫ c0) (e1 ≫ q') w1 h1 b3 P1,
    integral_of hI hR R' hFG' (γ2 ≫ γ1 ≫ c0) (e2 ≫ e1 ≫ q') w2 h2 c3 P2, l0, l1, l2,
    hD k Ω R' hFG' q' a3, P0, P1, P2, m1, m2, m3⟩

end LateralTheory.E.QuasiFiniteDescent

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafGlueProperPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafGlueProperPf

structure Glued (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L)
    (hAD : A ≤ D) (hBD : B ≤ D) where
  C0 : Scheme.{0}
  c0 : C0 ⟶ Sp Ω
  iA : Sp A ⟶ C0
  iB : Sp B ⟶ C0
  hiA : IsOpenImmersion iA
  hiB : IsOpenImmersion iB
  hcA : iA ≫ c0 = Spec.map (CommRingCat.ofHom (algebraMap Ω A))
  hcB : iB ≫ c0 = Spec.map (CommRingCat.ofHom (algebraMap Ω B))
  agree : Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAD).toRingHom) ≫ iA =
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hBD).toRingHom) ≫ iB
  cover : Set.range iA.base ∪ Set.range iB.base = Set.univ
  inter : Set.range iA.base ∩ Set.range iB.base =
    Set.range (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAD).toRingHom) ≫ iA).base

def GH (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L) : Prop :=
  u ≠ 0 ∧ u ∈ A ∧ u⁻¹ ∈ B ∧ Algebra.FiniteType Ω A ∧ Algebra.FiniteType Ω B ∧
  IsIntegrallyClosed A ∧ IsIntegrallyClosed B ∧ ringKrullDim A = 1 ∧ ringKrullDim B = 1 ∧
  IsFractionRing A L ∧ IsFractionRing B L ∧
  Algebra.adjoin Ω ((A : Set L) ∪ {u⁻¹}) = Algebra.adjoin Ω ((B : Set L) ∪ {u}) ∧
  (∀ V : ValuationSubring L, (∀ a : Ω, algebraMap Ω L a ∈ V) → (A : Set L) ⊆ V ∨ (B : Set L) ⊆ V)

abbrev Dr (Ω : Type) {L : Type} [Field Ω] [Field L] [Algebra Ω L] (A : Subalgebra Ω L) (u : L) : Subalgebra Ω L :=
  Algebra.adjoin Ω ((A : Set L) ∪ {u⁻¹})

theorem le_Dr_A {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A : Subalgebra Ω L) (u : L) : A ≤ Dr Ω A u :=
  fun x hx => Algebra.subset_adjoin (Set.mem_union_left _ hx)

theorem le_Dr_B {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
    (h : Algebra.adjoin Ω ((A : Set L) ∪ {u⁻¹}) = Algebra.adjoin Ω ((B : Set L) ∪ {u})) : B ≤ Dr Ω A u := by
  intro x hx
  show x ∈ Algebra.adjoin Ω ((A : Set L) ∪ {u⁻¹})
  rw [h]; exact Algebra.subset_adjoin (Set.mem_union_left _ hx)

def LeafGlueExists : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u), Nonempty (Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1))

def LeafGlueIntegral : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsIntegral G.C0

def LeafGlueNormal : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  ∀ y : G.C0, IsIntegrallyClosed (G.C0.presheaf.stalk y)

def LeafGlueDim : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  topologicalKrullDim G.C0 = 1

def LeafGlueIsProper : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsProper G.c0

def LeafGlueGeneric : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  ∃ (x : G.C0) (ψ : Spec (G.C0.presheaf.stalk x) ⟶ Sp L), IsGenericPoint x (⊤ : Set G.C0) ∧
    ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = G.C0.fromSpecStalk x ≫ G.c0

theorem LeafGlueProper_of (h1 : LeafGlueExists) (h2 : LeafGlueIntegral) (h3 : LeafGlueNormal) (h4 : LeafGlueDim)
    (h5 : LeafGlueIsProper) (h6 : LeafGlueGeneric) : LateralTheory.E.LeafNormalModelPf.LeafGlueProper := by
  intro Ω L _ _ _ A B u hu huA huB hfA hfB hicA hicB hdA hdB hfrA hfrB hadj hV
  have h : GH Ω L A B u := ⟨hu, huA, huB, hfA, hfB, hicA, hicB, hdA, hdB, hfrA, hfrB, hadj, hV⟩
  obtain ⟨G⟩ := h1 Ω L A B u h
  obtain ⟨x, ψ, hx, hψ⟩ := h6 Ω L A B u h G
  exact ⟨G.C0, G.c0, x, ψ, h2 Ω L A B u h G, h5 Ω L A B u h G, h3 Ω L A B u h G, h4 Ω L A B u h G, hx, hψ⟩

theorem normal_spec (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (p : Sp R) :
    IsIntegrallyClosed ((Sp R).presheaf.stalk p) := by
  let q : PrimeSpectrum R := p
  have : IsIntegrallyClosed ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk q) := by
    haveI : q.asIdeal.IsPrime := q.isPrime
    exact isIntegrallyClosed_of_isLocalization (R := R) _ q.asIdeal.primeCompl
      (fun x hx => mem_nonZeroDivisors_of_ne_zero (fun h => hx (h ▸ q.asIdeal.zero_mem)))
  exact this

theorem normal_of_openImm {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X)
    (h : IsIntegrallyClosed (X.presheaf.stalk x)) : IsIntegrallyClosed (Y.presheaf.stalk (f.base x)) :=
  IsIntegrallyClosed.of_equiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm

theorem glued_affine_curve_stalks_integrally_closed : LeafGlueNormal := by
  intro Ω L _ _ _ A B u h G y
  haveI := G.hiA; haveI := G.hiB
  have hy : y ∈ Set.range G.iA.base ∪ Set.range G.iB.base := G.cover ▸ Set.mem_univ y
  rcases hy with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · haveI := h.2.2.2.2.2.1; exact normal_of_openImm G.iA z (normal_spec A z)
  · haveI := h.2.2.2.2.2.2.1; exact normal_of_openImm G.iB z (normal_spec B z)

theorem irr_union {X : Type} [TopologicalSpace X] {U V : Set X} (hU : IsIrreducible U) (hV : IsIrreducible V)
    (hVo : IsOpen U) (hi : (U ∩ V).Nonempty) (hc : U ∪ V = Set.univ) : IrreducibleSpace X := by
  have h1 : V ⊆ closure (V ∩ U) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hV.2 hVo (by rwa [Set.inter_comm])
  have h2 : closure U = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hc]
    exact Set.union_subset subset_closure (h1.trans (closure_mono Set.inter_subset_right))
  have := hU.closure
  rw [h2] at this
  exact (irreducibleSpace_def X).2 this

theorem glued_affine_curve_is_integral_scheme : LeafGlueIntegral := by
  intro Ω L _ _ _ A B u h G
  haveI := G.hiA; haveI := G.hiB
  haveI : IrreducibleSpace G.C0 := by
    have hA := (IrreducibleSpace.isIrreducible_univ (Sp A)).image G.iA.base G.iA.base.hom.continuous.continuousOn
    have hB := (IrreducibleSpace.isIrreducible_univ (Sp B)).image G.iB.base G.iB.base.hom.continuous.continuousOn
    rw [Set.image_univ] at hA hB
    refine irr_union hA hB G.iA.isOpenEmbedding.isOpen_range ?_ G.cover
    rw [G.inter]; exact Set.range_nonempty _
  haveI : ∀ y : G.C0, _root_.IsReduced (G.C0.presheaf.stalk y) := by
    intro y
    have hy : y ∈ Set.range G.iA.base ∪ Set.range G.iB.base := G.cover ▸ Set.mem_univ y
    rcases hy with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact isReduced_of_injective (asIso (G.iA.stalkMap z)).commRingCatIsoToRingEquiv.toRingHom
        (asIso (G.iA.stalkMap z)).commRingCatIsoToRingEquiv.injective
    · exact isReduced_of_injective (asIso (G.iB.stalkMap z)).commRingCatIsoToRingEquiv.toRingHom
        (asIso (G.iB.stalkMap z)).commRingCatIsoToRingEquiv.injective
  haveI : IsReduced G.C0 := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _
end LateralTheory.E.LeafGlueProperPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.EmbedNonDeg
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.StdChartsProof
  LateralTheory.E.ChartsGeom_vpaPf

namespace LateralTheory.E.GeometricData

def rA {A : Type} [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (W : Z.Opens) : A →+* Γ(Z, W) :=
  (p.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

def NonDeg {A : Type} [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) : Prop :=
  ∃ (U V : Z.Opens) (s : Γ(Z, U)) (s' : Γ(Z, V)), IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ ∧
    Z.basicOpen s = U ⊓ V ∧ Z.basicOpen s' = U ⊓ V ∧ ((U ⊓ V : Z.Opens) : Set Z).Nonempty ∧
    Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s *
      Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s' = 1 ∧
    (Polynomial.eval₂RingHom (rA p U) s).IsIntegral ∧ (Polynomial.eval₂RingHom (rA p V) s').IsIntegral

def Concl {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧ ChartData p B C t

def TopInt : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → (rA p ⊤).IsIntegral

def LineOpens : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z → IsAffineOpen (⊤ : Z.Opens) ∨ NonDeg p

def EmbedNonDeg : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IsIntegral Z → (rA p ⊤).IsIntegral → NonDeg p → Concl p

def EmbedAffine : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IsIntegral Z → (rA p ⊤).IsIntegral → IsAffineOpen (⊤ : Z.Opens) → Concl p

theorem GeoData_of (hT : TopInt) (hL : LineOpens) (hN : EmbedNonDeg) (hE : EmbedAffine) : GeoData := by
  intro A _ _ Z p hIL hZ
  have hI : IsIntegral Z := hZ.1
  have hTop := hT A p hIL
  rcases hL A p hIL hZ with h | h
  · exact hE A p hI hTop h
  · exact hN A p hI hTop h

end LateralTheory.E.GeometricData
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SysFMPfSys
section -- merged from Development.EtaleCohomology.EtaleSheaves.SysFMPfAlg
section -- merged from Development.EtaleCohomology.EtaleSheaves.SysFMPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut

namespace LateralTheory.E.SysFMPf

def phi {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) : Γ(w.normalization, ⊤) →+* W :=
  (w.toNormalization.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom

def RR {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (q : PrimeSpectrum W) : Set w.normalization :=
  {y | ∀ s : Γ(w.normalization, ⊤), IsIdempotentElem (phi w s) → phi w s ∉ q.asIdeal → y ∈ w.normalization.basicOpen s}

def Sys : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0})
      (ι : ∀ j, D.obj j ⟶ w.normalization),
      (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
      (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)) ∧
      ⋂ j, Set.range (ι j) = RR w q

def FMex : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ q : PrimeSpectrum W,
    ∃ m : (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization ⟶ w.normalization,
      Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w.toNormalization =
        (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).toNormalization ≫ m ∧
      m ≫ w.fromNormalization = (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).fromNormalization ∧
      Mono m ∧ Flat m ∧ QuasiCompact m

def FMrange : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ (q : PrimeSpectrum W)
    (m : (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization ⟶ w.normalization),
      Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w.toNormalization =
        (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).toNormalization ≫ m →
      m ≫ w.fromNormalization = (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).fromNormalization →
      Set.range m = RR w q

theorem SysFM_of (hS : Sys) (hE : FMex) (hR : FMrange) : LateralTheory.E.NbIsoPf.SysFM := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, ι, h1, h2, h3⟩ := hS W w hW y
  obtain ⟨m, e1, e2, hm, hf, hq⟩ := hE W w hW q
  refine ⟨q, J, inferInstance, inferInstance, D, ι, h1, h2, m, hm, hf, hq, ?_⟩
  rw [h3]
  exact hR W w hW q m e1 e2

end LateralTheory.E.SysFMPf
end
end

namespace LateralTheory.E.SysFMPfAlg

open LateralTheory.E.BuildCut

theorem prime_of_filter {W : Type} [CommRing W] (hW : ProdACF W) (F : Set W) (hF : ∀ e ∈ F, IsIdempotentElem e)
    (h0 : (0 : W) ∉ F) (hu : ∀ e, IsIdempotentElem e → e ∈ F ∨ 1 - e ∈ F) (hm : ∀ e ∈ F, ∀ f ∈ F, e * f ∈ F) :
    ∃ q : PrimeSpectrum W, ∀ e, IsIdempotentElem e → (e ∉ q.asIdeal ↔ e ∈ F) := by
  have h1 : (1 : W) ∈ F := by
    rcases hu 0 IsIdempotentElem.zero with h | h
    · exact absurd h h0
    · simpa using h
  let I : Ideal W :=
    { carrier := {a | ∃ f ∈ F, a * f = 0}
      add_mem' := by
        rintro a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩
        exact ⟨f * g, hm f hf g hg, by linear_combination g * ha + f * hb⟩
      zero_mem' := ⟨1, h1, by simp⟩
      smul_mem' := by
        rintro c a ⟨f, hf, ha⟩
        exact ⟨f, hf, by simp only [smul_eq_mul]; linear_combination c * ha⟩ }
  have key : ∀ e, IsIdempotentElem e → (e ∈ I ↔ e ∉ F) := by
    intro e he
    constructor
    · rintro ⟨f, hf, hef⟩ heF
      exact h0 (hef ▸ hm e heF f hf)
    · intro heF
      rcases hu e he with h | h
      · exact absurd h heF
      · exact ⟨1 - e, h, by rw [mul_sub, mul_one, he.eq, sub_self]⟩
  have hI : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one]
      rintro ⟨f, hf, h⟩
      rw [one_mul] at h
      exact h0 (h ▸ hf)
    · intro a b hab
      obtain ⟨e, u, he, hu', rfl⟩ := hW.2 a
      obtain ⟨e', u', he', hu'', rfl⟩ := hW.2 b
      by_contra hn
      push Not at hn
      have ha : e ∈ F := by
        by_contra h
        exact hn.1 ⟨1 - e, (hu e he).resolve_left h, by
          rw [mul_assoc, mul_comm u, ← mul_assoc, mul_sub, mul_one, he.eq, sub_self, zero_mul]⟩
      have hb : e' ∈ F := by
        by_contra h
        exact hn.2 ⟨1 - e', (hu e' he').resolve_left h, by
          rw [mul_assoc, mul_comm u', ← mul_assoc, mul_sub, mul_one, he'.eq, sub_self, zero_mul]⟩
      obtain ⟨f, hf, h⟩ := hab
      have hz : e * e' * f = 0 := by
        obtain ⟨v, hv⟩ := hu'.exists_left_inv
        obtain ⟨v', hv'⟩ := hu''.exists_left_inv
        linear_combination (v * v') * h - (e * e' * f) * hv - (e * e' * f * v * u) * hv'
      exact h0 (hz ▸ hm _ (hm e ha e' hb) f hf)
  refine ⟨⟨I, hI⟩, fun e he => ?_⟩
  rw [show (⟨I, hI⟩ : PrimeSpectrum W).asIdeal = I from rfl, key e he, not_not]


open AlgebraicGeometry in
theorem isClosed_basicOpen_idem {X : Scheme.{0}} {s : Γ(X, ⊤)} (hs : IsIdempotentElem s) :
    IsClosed (X.basicOpen s : Set X) := by
  have : (X.basicOpen s : Set X)ᶜ = (X.basicOpen (1 - s) : Set X) := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, Scheme.mem_basicOpen_top, map_sub, map_one]
    have he : IsIdempotentElem (X.presheaf.germ ⊤ x trivial s) := hs.map _
    constructor
    · intro h
      exact (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left h
    · intro h h'
      have hz : X.presheaf.germ ⊤ x trivial s * (1 - X.presheaf.germ ⊤ x trivial s) = 0 := by
        rw [mul_sub, mul_one, he.eq, sub_self]
      exact not_isUnit_zero (hz ▸ h'.mul h)
  rw [← isOpen_compl_iff, this]
  exact (X.basicOpen (1 - s)).isOpen

open AlgebraicGeometry in
theorem isClosedImmersion_basicOpen_idem {X : Scheme.{0}} {s : Γ(X, ⊤)} (hs : IsIdempotentElem s) :
    IsClosedImmersion (X.basicOpen s).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact isClosed_basicOpen_idem hs)

end LateralTheory.E.SysFMPfAlg
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut LateralTheory.E.SysFMPf LateralTheory.E.SysFMPfAlg

namespace LateralTheory.E.SysFMPfSys

def IdemSec : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), Function.Injective (phi w) ∧ ∀ e : W, IsIdempotentElem e → ∃ s, phi w s = e

theorem basicOpen_one_sub {X : Scheme.{0}} {s : Γ(X, ⊤)} (hs : IsIdempotentElem s) (x : X) :
    x ∉ X.basicOpen s ↔ x ∈ X.basicOpen (1 - s) := by
  simp only [Scheme.mem_basicOpen_top, map_sub, map_one]
  have he : IsIdempotentElem (X.presheaf.germ ⊤ x trivial s) := hs.map _
  constructor
  · intro h
    exact (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left h
  · intro h h'
    have hz : X.presheaf.germ ⊤ x trivial s * (1 - X.presheaf.germ ⊤ x trivial s) = 0 := by
      rw [mul_sub, mul_one, he.eq, sub_self]
    exact not_isUnit_zero (hz ▸ h'.mul h)

theorem Sys_of (hI : IdemSec) : Sys := by
  intro P _ _ W _ w hW y
  obtain ⟨hinj, hrg⟩ := hI W w
  have hid : ∀ s, IsIdempotentElem (phi w s) → IsIdempotentElem s := fun s h =>
    hinj (by rw [map_mul]; exact h.eq)
  let F : Set W := {e | IsIdempotentElem e ∧ ∃ s, phi w s = e ∧ y ∈ w.normalization.basicOpen s}
  have hF0 : (0 : W) ∉ F := by
    rintro ⟨-, s, hs, hy⟩
    have : s = 0 := hinj (by rw [hs, map_zero])
    subst this
    simp at hy
  have hFu : ∀ e, IsIdempotentElem e → e ∈ F ∨ 1 - e ∈ F := by
    intro e he
    obtain ⟨s, rfl⟩ := hrg e he
    by_cases hy : y ∈ w.normalization.basicOpen s
    · exact Or.inl ⟨he, s, rfl, hy⟩
    · exact Or.inr ⟨he.one_sub, 1 - s, by rw [map_sub, map_one], (basicOpen_one_sub (hid s he) y).1 hy⟩
  have hFm : ∀ e ∈ F, ∀ f ∈ F, e * f ∈ F := by
    rintro e ⟨he, s, rfl, hs⟩ f ⟨hf, t, rfl, ht⟩
    exact ⟨he.mul hf, s * t, map_mul _ _ _, by rw [Scheme.basicOpen_mul]; exact ⟨hs, ht⟩⟩
  obtain ⟨q, hq⟩ := prime_of_filter hW F (fun e h => h.1) hF0 hFu hFm
  let J : Type := {s : Γ(w.normalization, ⊤) // IsIdempotentElem (phi w s) ∧ phi w s ∉ q.asIdeal}
  letI : Preorder J := Preorder.lift (fun s : J => w.normalization.basicOpen s.1)
  have hmono : Monotone (fun s : J => w.normalization.basicOpen s.1) := fun _ _ h => h
  have hne : Nonempty J := ⟨⟨1, by rw [map_one]; exact IsIdempotentElem.one, by rw [map_one]; exact (Ideal.ne_top_iff_one _).1 q.2.ne_top⟩⟩
  haveI : IsCodirectedOrder J := by
    refine ⟨?_⟩
    rintro ⟨s, hs1, hs2⟩ ⟨t, ht1, ht2⟩
    refine ⟨⟨s * t, by rw [map_mul]; exact hs1.mul ht1, by rw [map_mul]; exact q.2.mul_notMem hs2 ht2⟩, ?_, ?_⟩
    · show w.normalization.basicOpen (s * t) ≤ w.normalization.basicOpen s
      rw [Scheme.basicOpen_mul]; exact inf_le_left
    · show w.normalization.basicOpen (s * t) ≤ w.normalization.basicOpen t
      rw [Scheme.basicOpen_mul]; exact inf_le_right
  haveI : IsCofiltered J := { nonempty := hne }
  let D : J ⥤ Scheme.{0} := hmono.functor ⋙ w.normalization.restrictFunctor ⋙ Over.forget _
  have hDι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ (w.normalization.basicOpen k.1).ι = (w.normalization.basicOpen j.1).ι :=
    fun f => Over.w (w.normalization.restrictFunctor.map (hmono.functor.map f))
  let ι : ∀ j : J, D.obj j ⟶ w.normalization := fun j => (w.normalization.basicOpen j.1).ι
  have hr : ∀ j : J, Set.range (ι j) = (w.normalization.basicOpen j.1 : Set w.normalization) := fun j =>
    Scheme.Opens.range_ι _
  refine ⟨q, J, inferInstance, inferInstance, D, ι, fun j => ⟨show IsOpenImmersion (w.normalization.basicOpen j.1).ι from
    inferInstance, isClosedImmersion_basicOpen_idem (hid _ j.2.1), ?_⟩, fun {j k} f => ⟨hDι f, ?_⟩, ?_⟩
  · rw [hr]
    obtain ⟨-, s, hs, hy⟩ := (hq _ j.2.1).1 j.2.2
    rwa [hinj hs] at hy
  · have hk : IsClosedImmersion (ι k) := isClosedImmersion_basicOpen_idem (hid _ k.2.1)
    have hc : IsClosedImmersion (D.map f ≫ ι k) := by
      rw [hDι f]; exact isClosedImmersion_basicOpen_idem (hid _ j.2.1)
    have := @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ (D.map f) (ι k) hk hc
    infer_instance
  · ext x
    simp only [Set.mem_iInter, hr, RR, Set.mem_setOf_eq, SetLike.mem_coe]
    exact ⟨fun h s h1 h2 => h ⟨s, h1, h2⟩, fun h j => h j.1 j.2.1 j.2.2⟩

theorem SysFM_of (hI : IdemSec) (hE : FMex) (hR : FMrange) : LateralTheory.E.NbIsoPf.SysFM :=
  LateralTheory.E.SysFMPf.SysFM_of (Sys_of hI) hE hR

end LateralTheory.E.SysFMPfSys
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafDescendFPPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf

namespace LateralTheory.E.LeafDescendFPPf

def FP {X Y : Scheme.{0}} (f : X ⟶ Y) : Prop :=
  LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f

theorem fp_of_curve {Ω : Type} [Field Ω] {C : Scheme.{0}} {c : C ⟶ Sp Ω} (h : IsCurve c) : FP c := by
  obtain ⟨_, hp, hs⟩ := h
  have := hp
  have := hs
  refine ⟨inferInstance, inferInstance, inferInstance⟩

def LeafObjFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D : Scheme.{0}) (q : D ⟶ Sp R) (v : X ⟶ D),
      FP q ∧ IsPullback v f q (toR R)

def LeafPairFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0), FP (γ1 ≫ c0) →
    ∀ {D0 : Scheme.{0}} (q : D0 ⟶ Sp R) (v0 : C0 ⟶ D0), FP q → IsPullback v0 c0 q (toR R) →
    ∃ (R' : Subalgebra k Ω), R'.FG ∧ ∃ (E0 E1 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (w0 : C0 ⟶ E0)
      (w1 : C1 ⟶ E1), FP q' ∧ FP (e1 ≫ q') ∧ IsPullback w0 c0 q' (toR R') ∧
      IsPullback w1 (γ1 ≫ c0) (e1 ≫ q') (toR R') ∧ γ1 ≫ w0 = w1 ≫ e1

def LeafTripleFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), FP (γ2 ≫ γ1 ≫ c0) →
    ∀ {D0 D1 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1), FP q → FP (d1 ≫ q) →
    IsPullback v0 c0 q (toR R) → IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (toR R) → γ1 ≫ v0 = v1 ≫ d1 →
    ∃ (R' : Subalgebra k Ω), R'.FG ∧ ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1)
      (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1) (w2 : C2 ⟶ E2), PreChain R' c0 γ1 γ2 q' e1 e2 w0 w1 w2

theorem diagramDescent_of_objects_pairs_triples (hO : LeafObjFP) (hP : LeafPairFP) (hT : LeafTripleFP) : LeafDescendFP := by
  intro k _ Ω _ _ C0 c0 hc0 C1 C2 γ1 γ2 h1 h2
  obtain ⟨R, hR, D0, q, v0, hq, hsq⟩ := hO k Ω c0 (fp_of_curve hc0)
  obtain ⟨R', hR', E0, E1, q', e1, w0, w1, hq', he1, hs0, hs1, hc⟩ :=
    hP k Ω R hR c0 γ1 (fp_of_curve h1) q v0 hq hsq
  exact hT k Ω R' hR' c0 γ1 γ2 (fp_of_curve h2) q' e1 w0 w1 hq' he1 hs0 hs1 hc

end LateralTheory.E.LeafDescendFPPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafExtTensPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafExtTensPf

theorem res_isKInjective (R : Type) [CommRing R] (F : Shv R) : (res R F).IsKInjective := by
  unfold res; infer_instance

theorem res_injective (R : Type) [CommRing R] (F : Shv R) (n : ℤ) : Injective ((res R F).X n) := by
  unfold res
  rw [InjectiveResolution.cochainComplex]
  by_cases h : ∃ k : ℕ, ComplexShape.embeddingUpNat.f k = n
  · obtain ⟨k, hk⟩ := h
    exact Injective.of_iso (HomologicalComplex.extendXIso _ _ hk).symm inferInstance
  · push_neg at h
    exact (HomologicalComplex.isZero_extend_X _ _ n h).injective

section
variable {C : Type*} [Category C] [Abelian C]

theorem exact_lift {S T L : CochainComplex C ℤ} (ι : S ⟶ T) [∀ n, Mono (ι.f n)] [∀ n, Injective (L.X n)]
    (u : S ⟶ L) (g0 : T ⟶ L) (H : Homotopy u (ι ≫ g0)) : ∃ g : T ⟶ L, ι ≫ g = u := by
  let h' : ∀ i j, T.X i ⟶ L.X j := fun i j => Injective.factorThru (H.hom i j) (ι.f i)
  have hh : (fun i j => ι.f i ≫ h' i j) = H.hom := by
    funext i j; exact Injective.comp_factorThru _ _
  refine ⟨g0 + Homotopy.nullHomotopicMap h', ?_⟩
  rw [Preadditive.comp_add, Homotopy.comp_nullHomotopicMap, hh]
  ext n
  rw [H.comm n]
  simp only [HomologicalComplex.add_f_apply]
  change _ + (dNext n H.hom + prevD n H.hom) = _
  abel

theorem homotopy_lift {S T L : CochainComplex C ℤ} (ι : S ⟶ T) [QuasiIso ι] [L.IsKInjective]
    (u : S ⟶ L) : ∃ g0 : T ⟶ L, Nonempty (Homotopy u (ι ≫ g0)) := by
  let _ := HasDerivedCategory.standard C
  let qt := (HomotopyCategory.quotient C (ComplexShape.up ℤ))
  have hi : IsIso (DerivedCategory.Qh.map (qt.map ι)) := by
    have e := (DerivedCategory.quotientCompQhIso C).hom.naturality ι
    have : IsIso (DerivedCategory.Q.map ι) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
    have e2 : DerivedCategory.Qh.map (qt.map ι) = (DerivedCategory.quotientCompQhIso C).hom.app S ≫
        DerivedCategory.Q.map ι ≫ (DerivedCategory.quotientCompQhIso C).inv.app T := by
      simp only [Functor.comp_map] at e
      rw [← reassoc_of% e]; simp [qt]
    rw [e2]; infer_instance
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj T) L).surjective
    (inv (DerivedCategory.Qh.map (qt.map ι)) ≫ DerivedCategory.Qh.map (qt.map u))
  obtain ⟨g0, rfl⟩ := qt.map_surjective g
  refine ⟨g0, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj S) L).injective
  rw [Functor.map_comp, Functor.map_comp, hg, IsIso.hom_inv_id_assoc]

theorem extAlongQIso {S T L : CochainComplex C ℤ} (ι : S ⟶ T) (hm : ∀ n, Mono (ι.f n)) (hq : QuasiIso ι)
    (hk : L.IsKInjective) (hinj : ∀ n, Injective (L.X n)) (u : S ⟶ L) : ∃ g : T ⟶ L, ι ≫ g = u := by
  obtain ⟨g0, ⟨H⟩⟩ := homotopy_lift ι u
  exact exact_lift ι u g0 H
end

def LeafTensMono : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {S T : Cx (ZMod q)} (σ : Pair (sgl (tw q 0)) (res _ (tw q i)) S)
  (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map ((resAug (tw q 0)).f s) a) b) →
  ∀ n, Mono (ι.f n)

def LeafTensQIso : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {S T : Cx (ZMod q)} (σ : Pair (sgl (tw q 0)) (res _ (tw q i)) S)
  (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map ((resAug (tw q 0)).f s) a) b) →
  QuasiIso ι

theorem LeafExtTens_of (hmono : LeafTensMono) (hqiso : LeafTensQIso) : LateralTheory.E.LeafPairExtPf2.LeafExtTens := by
  intro q _ i S T σ τ hσ hτ ι hι u
  exact extAlongQIso ι (hmono q i σ τ hσ hτ ι hι) (hqiso q i σ τ hσ hτ ι hι) (res_isKInjective _ _)
    (res_injective _ _) u

end LateralTheory.E.LeafExtTensPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafVanBStalkPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafVanBStalkPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafVanBPf

theorem hkpull_comp (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (y : HK R M F n) : HK.pull R (f ≫ g) F n y = HK.pull R f F n (HK.pull R g F n y) := by
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem rmap_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c1 : f' ≫ e = u ≫ f) (c2 : f'' ≫ e' = u' ≫ f')
    (c3 : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) :
    rmap R f f'' (u' ≫ u) (e' ≫ e) c3 = rmap R f' f'' u' e' c2 ≫ rmap R f f' u e c1 := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  rw [mappingCone.ext_from_iff _ (n + 1) n rfl]
  simp [rmap, mappingCone.map]

theorem rpull_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c1 : f' ≫ e = u ≫ f) (c2 : f'' ≫ e' = u' ≫ f')
    (c3 : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) (F : Shv R) (n : ℤ) (y : Hrel R f F n) :
    rpull R f f'' (u' ≫ u) (e' ≫ e) c3 F n y = rpull R f' f'' u' e' c2 F n (rpull R f f' u e c1 F n y) := by
  simp only [rpull]
  rw [rmap_comp R f f' f'' u e u' e' c1 c2 c3, hkpull_comp]

theorem rpull_congr (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') {u u₀ : U' ⟶ U}
    {e e₀ : E' ⟶ E} (hu : u = u₀) (he : e = e₀) (c : f' ≫ e = u ≫ f) (c₀ : f' ≫ e₀ = u₀ ≫ f) (F : Shv R) (n : ℤ) :
    rpull R f f' u e c F n = rpull R f f' u₀ e₀ c₀ F n := by
  subst hu he; rfl

theorem rB_comp (q : ℕ) (i : ℤ) {B W : Scheme.{0}} (ι : W ⟶ B) {U U' U'' : B.Etale} (a : U' ⟶ U) (b : U'' ⟶ U')
    (m : ℤ) (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m) :
    rB q i ι (b ≫ a) m c = rB q i ι b m (rB q i ι a m c) := by
  have h1 : resBW ι (b ≫ a) = resBW ι b ≫ resBW ι a := by
    apply pullback.hom_ext <;>
      simp only [resBW, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc] <;> rfl
  have h2 : (b ≫ a).left = b.left ≫ a.left := rfl
  simp only [rB, rpl]
  rw [rpull_congr (ZMod q) _ _ (show sch.map (resBW ι (b ≫ a)) = sch.map (resBW ι b) ≫ sch.map (resBW ι a) by
      rw [h1, Functor.map_comp])
    (show sch.map (b ≫ a).left = sch.map b.left ≫ sch.map a.left by rw [h2, Functor.map_comp]) _
    (by rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← h1, ← h2,
      pullback.lift_fst])]
  exact rpull_comp (ZMod q) _ _ _ _ _ _ _ _ _ _ (tw q i) m c

structure SHSys {B : Scheme.{0}} (U : B.Etale) (x : U.left) where
  J : Type
  [cat : SmallCategory J]
  [filt : IsFiltered J]
  D : J ⥤ CommRingCat.{0}
  V : J → B.Etale
  a : ∀ j, V j ⟶ U
  e : ∀ j, (V j).left ≅ Spec (D.obj j)
  tr : ∀ {j j' : J} (_ : j ⟶ j'), V j' ⟶ V j
  tr_a : ∀ {j j' : J} (g : j ⟶ j'), tr g ≫ a j = a j'
  tr_spec : ∀ {j j' : J} (g : j ⟶ j'), (e j').inv ≫ (tr g).left ≫ (e j).hom = Spec.map (D.map g)
  hx : ∀ j, x ∈ Set.range (a j).left
  c : Cocone D
  hc : IsColimit c
  sh : SH c.pt
  t : Spec c.pt ⟶ U.left
  ht : ∀ j, t = Spec.map (c.ι.app j) ≫ (e j).inv ≫ (a j).left

attribute [instance] SHSys.cat SHSys.filt

def LeafSHSys : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left), Nonempty (SHSys U x)

def LeafSHCont : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (m : ℤ)
  (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m) (x : U.left) (S : SHSys U x),
  bpl q i ι U S.t m c = 0 → ∃ j, rB q i ι (S.a j) m c = 0

def LeafStalkPt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (m : ℤ)
  (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m),
  (∀ (A : Type) [CommRing A] [IsLocalRing A] (t : Sp A ⟶ U.left), SH A → IsUnit (q : A) → bpl q i ι U t m c = 0) →
  ∀ x : U.left, ∃ (V : B.Etale) (a : V ⟶ U), x ∈ Set.range a.left ∧ rB q i ι a m c = 0

theorem cov_of_pts {B W : Scheme.{0}} (q : ℕ) (i : ℤ) (ι : W ⟶ B) (U : B.Etale) (m : ℤ)
    (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m)
    (h : ∀ x : U.left, ∃ (V : B.Etale) (a : V ⟶ U), x ∈ Set.range a.left ∧ rB q i ι a m c = 0) :
    Cov U (fun _ a => rB q i ι a m c = 0) := by
  choose V a hx hz using h
  refine ⟨Sieve.ofArrows V a, ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext x; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨x, hx x⟩
  · intro U' g hg
    rw [Sieve.mem_ofArrows_iff] at hg
    obtain ⟨x, b, rfl⟩ := hg
    rw [rB_comp, hz x, map_zero]

theorem stalkPt_of (hN : LeafSHSys) (hC : LeafSHCont) : LeafStalkPt := by
  intro hy q _ k _ hq i B W s ι _ U m c hc x
  obtain ⟨S⟩ := hN U x
  have hu : IsUnit (q : S.c.pt) := by
    have g := Spec.preimage (S.t ≫ U.hom ≫ s)
    simpa using hq.map g.hom
  haveI : IsLocalRing S.c.pt := S.sh.1.toIsLocalRing
  have h0 := hc S.c.pt S.t S.sh hu
  obtain ⟨j, hj⟩ := hC hy q k hq i s ι U m c x S h0
  exact ⟨S.V j, S.a j, S.hx j, hj⟩

theorem LeafVanBStalk_of_pt (hP : LeafStalkPt) : LeafVanBStalk := by
  intro hy q _ k _ hq i B W s ι _ U m c hc
  exact cov_of_pts q i ι U m c (hP hy q k hq i s ι U m c hc)

end LateralTheory.E.LeafVanBStalkPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.RelativeCohomologyForgetInjectiveDegreeZeroOfSub
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafInj0VPf
open CochainComplex CochainComplex.HomComplex
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf

def LeafSecTr : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (ι : W ⟶ B) (P : Y ⟶ B) (U : B.Etale)
  (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0), ∃ s : Sec (tw q i) U.left,
  (∀ (U' : B.Etale) (a : U' ⟶ U), Sec.res a.left s = 0 → rB q i ι a 0 c = 0) ∧
  (∀ (U' : B.Etale) (a : U' ⟶ U), rY q i P ι a 0 (bY q i P ι U 0 c) = 0 → Sec.res (toBY P U' ≫ a.left) s = 0)

def LeafSecV : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale) (s : Sec (tw q i) U.left),
  Cov U (fun U' a => Sec.res (toBY (g2 ≫ g1 ≫ p) U' ≫ a.left) s = 0) →
  ∀ x : U.left, U.hom x ∉ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Sec.res a.left s = 0

theorem res_comp {q : ℕ} {i : ℤ} {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Sec (tw q i) Z) :
    Sec.res (f ≫ g) s = Sec.res f (Sec.res g s) := by
  simp [Sec.res, op_comp, Functor.map_comp]

theorem relative_cohomology_forget_injective_degree_zero_of_subsingleton (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E)
    (hU : Subsingleton (H R U F (-1))) (y : Hrel R f F 0) (hy : fgt R f F 0 y = 0) : y = 0 := by
  obtain ⟨z, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr ((chains R).map f))) z (zero_add 0)) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff] at hy
  obtain ⟨m, hm, γ, hγ⟩ := hy
  obtain rfl : m = -1 := by omega
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe] at hγ
  set φ := (chains R).map f
  let w : Cochain (mappingCone φ) (res R F) (-1) := mappingCone.descCochain φ (0 : Cochain ((chains R).obj U) (res R F) (-2)) γ (by norm_num)
  let z' : Cochain (mappingCone φ) (res R F) 0 := z.1 - δ (-1) 0 w
  have hz'c : δ 0 1 z' = 0 := by
    simp [z', δ_δ]
  have hinr : (Cochain.ofHom (mappingCone.inr φ)).comp z' (zero_add 0) = 0 := by
    have h1 : δ (-1) 0 ((Cochain.ofHom (mappingCone.inr φ)).comp w (zero_add _)) =
        (Cochain.ofHom (mappingCone.inr φ)).comp (δ (-1) 0 w) (zero_add 0) := by
      rw [δ_ofHom_comp]
    simp only [z', Cochain.comp_sub, ← h1, w, mappingCone.inr_descCochain]
    rw [hγ, sub_self]
  let β : Cochain ((chains R).obj U) (res R F) (-1) := (mappingCone.inl φ).comp z' (by norm_num)
  have hβc : δ (-1) 0 β = 0 := by
    simp only [β]
    rw [δ_comp _ _ (by norm_num) 0 1 0 (by norm_num) (by norm_num) (by norm_num), mappingCone.δ_inl, hz'c]
    simp only [Cochain.comp_zero, smul_zero, add_zero, Cochain.ofHom_comp]
    rw [Cochain.comp_assoc_of_first_is_zero_cochain, hinr]
    simp
  have hβ0 : CohomologyClass.mk (Cocycle.mk β 0 (by norm_num) hβc) = (0 : H R U F (-1)) := Subsingleton.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff] at hβ0
  obtain ⟨m', hm', ε, hε⟩ := hβ0
  obtain rfl : m' = -2 := by omega
  have hz' : z' = δ (-1) 0 (mappingCone.descCochain φ ε 0 (by norm_num)) := by
    rw [mappingCone.δ_descCochain _ _ _ _ 0 (by norm_num)]
    rw [mappingCone.ext_cochain_from_iff φ (-1) 0 (by norm_num)]
    constructor
    · simp [β] at hε
      simp [hε, β]
    · simp [hinr]
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨-1, by norm_num, w + mappingCone.descCochain φ ε 0 (by norm_num), ?_⟩
  rw [δ_add, ← hz']
  simp [z']

theorem secTr (hH : Hyps) (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (ι : W ⟶ B) (P : Y ⟶ B) (U : B.Etale)
    (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0) : ∃ s : Sec (tw q i) U.left,
    (∀ (U' : B.Etale) (a : U' ⟶ U), Sec.res a.left s = 0 → rB q i ι a 0 c = 0) ∧
    (∀ (U' : B.Etale) (a : U' ⟶ U), rY q i P ι a 0 (bY q i P ι U 0 c) = 0 → Sec.res (toBY P U' ≫ a.left) s = 0) := by
  have hA9 : A9 := hH.2.2.2.2.2.2.2.1
  obtain ⟨hneg, e, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  refine ⟨(e U.left).symm (fgt _ _ _ 0 c), ?_, ?_⟩
  · intro U' a ha
    apply relative_cohomology_forget_injective_degree_zero_of_subsingleton _ _ _ (hneg _ (-1) (by norm_num))
    rw [relNat]
    have := hnat a.left ((e U.left).symm (fgt _ _ _ 0 c))
    rw [AddEquiv.apply_symm_apply] at this
    rw [this, ha, map_zero]
  · intro U' a ha
    have h0 := congrArg (fgt _ _ _ 0) ha
    rw [map_zero, relNat, relNat, ← pull_comp, ← Functor.map_comp] at h0
    have hsq : resY P a ≫ toBY P U = toBY P U' ≫ a.left := by simp only [resY, toBY]; exact pullback.lift_snd _ _ _
    rw [hsq] at h0
    have := hnat (toBY P U' ≫ a.left) ((e U.left).symm (fgt _ _ _ 0 c))
    rw [AddEquiv.apply_symm_apply, h0] at this
    exact (e _).injective (by rw [← this, map_zero])

def LeafSHPt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ) {B : Scheme.{0}}
  (U : B.Etale) (_ : U.left ⟶ Sp k) (x : U.left), ∃ (A : Type) (_ : CommRing A) (t : Sp A ⟶ U.left), SH A ∧
  (∀ O : U.left.Opens, x ∈ O → Set.range t ⊆ O) ∧
  (∀ S ∈ (EtTop B) U, ∃ (U' : B.Etale) (a : U' ⟶ U), S a ∧ ∃ t' : Sp A ⟶ U'.left, t' ≫ a.left = t) ∧
  ∀ s : Sec (tw q i) U.left, Sec.res t s = 0 → ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Sec.res a.left s = 0

theorem LeafSecV_of (hP : LeafSHPt) : LeafSecV := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s0 ι _ V hV' p g1 g2 hp1 hp2 hp3 hSH U s hc x hx
  have hA9 : A9 := hH.2.2.2.2.2.2.2.1
  obtain ⟨-, e, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  obtain ⟨A, _, t, hA, hO, hL, hG⟩ := hP hH q k hq i U (U.hom ≫ s0) x
  apply hG
  set P := g2 ≫ g1 ≫ p
  have hxV : x ∈ (U.hom ⁻¹ᵁ V) := by
    change U.hom x ∈ (V : Set B); rw [hV']; exact hx
  have hr : Set.range (t ≫ U.hom) ⊆ (V : Set B) := by
    rintro _ ⟨z, rfl⟩
    exact hO _ hxV ⟨z, rfl⟩
  have hinj := ((hSH A (t ≫ U.hom) hA hr).2.2.2).1
  obtain ⟨S, hS, hPS⟩ := hc
  obtain ⟨U', a, hSa, t', ht'⟩ := hL S hS
  have h0 := hPS U' a hSa
  have hm : pullback.snd P (t ≫ U.hom) ≫ t =
      pullback.map P (t ≫ U.hom) P U'.hom (𝟙 _) t' (𝟙 B) (by simp) (by
        rw [Category.comp_id, ← ht', Category.assoc]; congr 1; simpa using a.w) ≫ (toBY P U' ≫ a.left) := by
    simp only [toBY]
    rw [pullback.lift_snd_assoc, Category.assoc, ht']
  apply (e _).injective
  apply hinj
  rw [map_zero, map_zero]
  change pull _ (sch.map (pullback.snd P (t ≫ U.hom))) _ 0 (e _ (Sec.res t s)) = 0
  rw [hnat, ← res_comp, hm, res_comp, h0]
  simp

theorem LeafInj0V_of_sec (hT : LeafSecTr) (hS : LeafSecV) : LeafInj0V := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s0 ι _ V hV' p g1 g2 hp1 hp2 hp3 hSH U c hc x hx
  obtain ⟨s, h1, h2⟩ := hT hH q i ι (g2 ≫ g1 ≫ p) U c
  obtain ⟨U', a, y, hy, hs⟩ := hS hH q k hq i s0 ι V hV' p g1 g2 hp1 hp2 hp3 hSH U s
    (hc.mono fun U'' b hb => h2 U'' b hb) x hx
  refine ⟨U', a, y, hy, Cov.all fun U'' b => h1 U'' (b ≫ a) ?_⟩
  change Sec.res (b.left ≫ a.left) s = 0
  rw [res_comp, hs]
  simp
theorem LeafInj0V_of (hP : LeafSHPt) : LeafInj0V :=
  LeafInj0V_of_sec (fun hH q _ i _ _ _ ι P U c => secTr hH q i ι P U c) (LeafSecV_of hP)
end LateralTheory.E.LeafInj0VPf
end
end
