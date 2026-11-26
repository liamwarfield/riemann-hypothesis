module

public import Development.EtaleCohomology.EtaleSheaves.PartDiagCut
public import Development.EtaleCohomology.EtaleSheaves.TwistTensorRestriction
public import Development.EtaleCohomology.EtaleSheaves.StrictHenselColimits.ColimOf
public import Development.EtaleCohomology.EtaleSheaves.LPrimLocPf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.CurveThroughGenericPointSpreadsToSmoothProperFamily2
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGeoVCut

namespace LateralTheory.E.LeafGeoVV2Cut

def CurveThroughGenericPointSpreadsToSmoothProperFamily : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) → genericPoint X ∈ Set.range e →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
      Surjective γ1 → Surjective γ2 → FamilyVe (k := k) X c0 e γ1 γ2

def LeafDescendQF : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) → genericPoint X ∈ Set.range e →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
      Surjective γ1 → Surjective γ2 →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2)
      (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))),
      IsSeparated q ∧ QuasiCompact q ∧ SmoothOfRelativeDimension 1 q ∧
      IsSeparated (d1 ≫ q) ∧ QuasiCompact (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
      IsSeparated (d2 ≫ d1 ≫ q) ∧ QuasiCompact (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
      IsIntegral D0 ∧ IsIntegral D1 ∧ IsIntegral D2 ∧
      LocallyQuasiFinite (pullback.lift q f hf.symm) ∧ LocallyQuasiFinite d1 ∧ LocallyQuasiFinite d2 ∧
      topologicalKrullDim D0 ≤ ringKrullDim R + 1 ∧
      IsPullback v0 c0 q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2 ∧ v0 ≫ f = e

def LeafExtendZMT : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p]
  (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (B : Scheme.{0}) (b : B ⟶ Sp k) [IsProper b]
  (ι : Sp R ⟶ B) [IsOpenImmersion ι], ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k R)) →
  ∀ {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) (e : C0 ⟶ X),
    IsCurve c0 → IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
  ∀ {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (f : D0 ⟶ X) (v0 : C0 ⟶ D0)
    (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2) (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))),
    IsSeparated q → QuasiCompact q → SmoothOfRelativeDimension 1 q →
    IsSeparated (d1 ≫ q) → QuasiCompact (d1 ≫ q) → SmoothOfRelativeDimension 1 (d1 ≫ q) →
    IsSeparated (d2 ≫ d1 ≫ q) → QuasiCompact (d2 ≫ d1 ≫ q) → SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) →
    IsIntegral D0 → IsIntegral D1 → IsIntegral D2 →
    LocallyQuasiFinite (pullback.lift q f hf.symm) → LocallyQuasiFinite d1 → LocallyQuasiFinite d2 →
    IsPullback v0 c0 q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) →
    IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) →
    IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) →
    γ1 ≫ v0 = v1 ≫ d1 → γ2 ≫ v1 = v2 ≫ d2 → v0 ≫ f = e →
    ∃ (Y0 Y1 Y2 : Scheme.{0}) (π : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) (h : Y0 ⟶ X) (V : B.Opens)
      (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ⊆ V ∧
      SmP π V ∧ SmP (g1 ≫ π) V ∧ SmP (g2 ≫ g1 ≫ π) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧
      IrreducibleSpace Y0 ∧ topologicalKrullDim Y0 ≤ topologicalKrullDim D0 ∧
      IsPullback u0 c0 π (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ∧
      IsPullback u1 (γ1 ≫ c0) (g1 ≫ π) (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ∧
      IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ π) (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ∧
      γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2 ∧ u0 ≫ h = e

theorem spread_of (hD : LeafDescendQF) (hB : LateralTheory.E.LeafSpreadVCut.LeafCloseB) (hE : LeafExtendZMT) :
    CurveThroughGenericPointSpreadsToSmoothProperFamily := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨R, hR, D0, D1, D2, q, d1, d2, f, v0, v1, v2, hf, sp0, qc0, sm0, sp1, qc1, sm1, sp2, qc2, sm2, i0, i1, i2,
    qf0, qf1, qf2, dD, P0, P1, P2, c1, c2, ve⟩ := hD k p Ω hdim c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2
  have : Algebra.FiniteType k R := Subalgebra.fg_iff_finiteType R |>.mp hR
  obtain ⟨B, b, ι, iB, pb, oι, hι, dB⟩ := hB k R
  obtain ⟨Y0, Y1, Y2, π, g1, g2, h, V, u0, u1, u2, hs, m0, m1, m2, f1, irrY, dY, Q0, Q1, Q2, e1, e2, ue⟩ :=
    hE k p Ω R B b ι hι c0 γ1 γ2 e hc0 h1 h2 he q d1 d2 f v0 v1 v2 hf sp0 qc0 sm0 sp1 qc1 sm1 sp2 qc2 sm2 i0 i1 i2
      qf0 qf1 qf2 P0 P1 P2 c1 c2 ve
  have hR' : ringKrullDim R < topologicalKrullDim X := hdim R hR
  obtain ⟨hle, hlt⟩ := LateralTheory.E.LeafSpreadVCut.succ_le_of_lt hR'
  have := hc0.1
  obtain ⟨x⟩ : Nonempty C0 := inferInstance
  refine ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι,
    u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, lt_of_le_of_lt dB hR', irrY, dY.trans (dD.trans hle),
    lt_of_le_of_lt (dY.trans dD) hlt, ⟨u0 x, ?_⟩, Q0, Q1, Q2, e1, e2, ue⟩
  show π (u0 x) ∈ (V : Set B)
  rw [← Scheme.Hom.comp_apply, Q0.w]
  exact hs ⟨c0 x, rfl⟩

theorem geoV_of (hC : LeafCurveV) (hS : CurveThroughGenericPointSpreadsToSmoothProperFamily) : LateralTheory.E.LeafGeoCut.LeafGeoV := by
  intro k _ _ X _ p _ hd
  obtain ⟨Ω, iF, iA, iK, C0, c0, e, hc0, he, hη, hdim⟩ := hC k p hd
  refine ⟨Ω, iF, iA, iK, C0, c0, hc0, fun C1 C2 γ1 γ2 h1 h2 s1 s2 => ?_⟩
  obtain ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2, ue⟩ := hS k p Ω hdim c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2
  refine ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, ?_, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2⟩
  obtain ⟨x0, hx0⟩ := hη
  obtain ⟨x1, rfl⟩ := s1.surj x0
  obtain ⟨x2, rfl⟩ := s2.surj x1
  have key : u2 ≫ g2 ≫ g1 ≫ h = γ2 ≫ γ1 ≫ e := by
    rw [← ue, ← Category.assoc u2 g2, ← w2, Category.assoc, ← Category.assoc u1 g1, ← w1]
    simp only [Category.assoc]
  have := f1
  refine surj_of_generic (g2 ≫ g1 ≫ h) ⟨u2 x2, ?_⟩
  rw [← Scheme.Hom.comp_apply, key, ← hx0]
  simp only [Scheme.Hom.comp_apply]

end LateralTheory.E.LeafGeoVV2Cut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.GlueRelPfNat
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex CochainComplex AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.GlueRelPfNat
variable (R : Type) [CommRing R]

theorem map_fst {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) :
    (Cochain.ofHom (mappingCone.map φ₁ φ₂ a b comm)).comp (mappingCone.fst φ₂).1 (zero_add 1) =
      (mappingCone.fst φ₁).1.comp (Cochain.ofHom a) (add_zero 1) := by
  rw [mappingCone.ext_cochain_from_iff φ₁ 0 1 (zero_add 1)]
  constructor
  · rw [← Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.map, mappingCone.inl_desc,
      Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inl_fst, ← Cochain.comp_assoc_of_third_is_zero_cochain,
      mappingCone.inl_fst]
    simp
  · rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inr_fst]
    simp [mappingCone.map]

end LateralTheory.E.GlueRelPfNat
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafUnitActPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitActPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafUnitPairGPf

def LeafActSheaf : Prop := ∀ (q : ℕ) [NeZero q], ∃ L : ∀ (F : Shv (ZMod q)) (U : Scheme.{0}),
    Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)] Sec F U →ₗ[ULift.{1} (ZMod q)] Sec F U,
  (∀ (F : Shv (ZMod q)) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec (tw q 0) U) (b : Sec F U),
      Sec.res g (L F U a b) = L F V (Sec.res g a) (Sec.res g b)) ∧
  (∀ {F G : Shv (ZMod q)} (φ : F ⟶ G) (U : Scheme.{0}) (a : Sec (tw q 0) U) (b : Sec F U),
      Sec.map φ (L F U a b) = L G U a (Sec.map φ b)) ∧
  ∀ (F : Shv (ZMod q)) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (b : Sec F U), L F U (twGen 0 ζ) b = b

theorem LeafUnitAct_of (h : LeafActSheaf) : LeafUnitAct := by
  intro q _ i
  obtain ⟨L, hU, hF, hζ⟩ := h q
  refine ⟨fun U t => L ((res _ (tw q i)).X t) U, ⟨fun g t a b => hU _ g a b, fun U t a b => hF _ U a b⟩,
    fun U t ζ b => hζ _ U ζ b⟩

end LateralTheory.E.LeafUnitActPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.AugBij
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.TateTwistZeroAugmentationBijective

def Aug : Prop := ∀ q : ℕ, ∃ φ : ∀ T : Scheme.{0}, Sec (tw q 0) T →+ LocallyConstant T (ZMod q),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U), φ V (Sec.res g x) = (φ U x).comap g.base.hom) ∧
  ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), φ U (twGen 0 ζ) = 1

def AugBij : Prop := ∀ (q : ℕ) (φ : ∀ T : Scheme.{0}, Sec (tw q 0) T →+ LocallyConstant T (ZMod q)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U), φ V (Sec.res g x) = (φ U x).comap g.base.hom) →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), φ U (twGen 0 ζ) = 1) →
  ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → Function.Bijective (φ T)

theorem Tw0_of (hA : Aug) (hB : AugBij) : LateralTheory.E.LCIsoPf.Tw0 := by
  intro q
  obtain ⟨φ, hnat, hgen⟩ := hA q
  have hb := hB q φ hnat hgen
  refine ⟨fun T hT => (AddEquiv.ofBijective (φ T) (hb T hT)).symm, ?_⟩
  intro V U g hV hU a
  apply (hb V hV).1
  have h1 : ∀ (T : Scheme.{0}) (hT : IsUnit (q : Γ(T, ⊤))) (b : LocallyConstant T (ZMod q)),
      φ T ((AddEquiv.ofBijective (φ T) (hb T hT)).symm b) = b := fun T hT b =>
    (AddEquiv.ofBijective (φ T) (hb T hT)).apply_symm_apply b
  rw [hnat, h1 U hU, h1 V hV]

end LateralTheory.E.TateTwistZeroAugmentationBijective
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafConsPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafConsPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves

def LeafLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y0 Y1 Y2 : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι]
  (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1),
  ∃ (K0 K1 K2 L : DerivedCategory (SShv B q)) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
    (l0 : LocE q i p ι K0) (l1 : LocE q i (g1 ≫ p) ι K1) (l2 : LocE q i (g2 ≫ g1 ≫ p) ι K2) (lL : LocEB q i ι L),
    Rep q i p ι K0 l0 ∧ Rep q i (g1 ≫ p) ι K1 l1 ∧ Rep q i (g2 ≫ g1 ≫ p) ι K2 l2 ∧ RepB q i ι L lL ∧
    MorRep q i p g1 ι l0 l1 f ∧ MorRep q i (g1 ≫ p) g2 ι l1 l2 g ∧ MorRepB q i (g2 ≫ g1 ≫ p) ι lL l2 ℓ

def LeafGlob : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y0 Y1 Y2 : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι]
  (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1)
  (K0 K1 K2 L : DerivedCategory (SShv B q)) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
  (l0 : LocE q i p ι K0) (l1 : LocE q i (g1 ≫ p) ι K1) (l2 : LocE q i (g2 ≫ g1 ≫ p) ι K2) (lL : LocEB q i ι L),
  Rep q i p ι K0 l0 → Rep q i (g1 ≫ p) ι K1 l1 → Rep q i (g2 ≫ g1 ≫ p) ι K2 l2 → RepB q i ι L lL →
  MorRep q i p g1 ι l0 l1 f → MorRep q i (g1 ≫ p) g2 ι l1 l2 g → MorRepB q i (g2 ≫ g1 ≫ p) ι lL l2 ℓ →
  ∃ (e0 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst p ι)) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj K0))
    (e2 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι)) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj K2))
    (eL : ∀ n : ℤ, Hrel (ZMod q) (sch.map ι) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj L)),
    (∀ n, Function.Injective (e2 n)) ∧ (∀ n, Function.Surjective (eL n)) ∧
    (∀ n y, e2 n (rpl q i (pullback.fst p ι) (pullback.fst (g2 ≫ g1 ≫ p) ι)
          (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp)) (g2 ≫ g1)
          (pullback.lift_fst _ _ _).symm n y) = e0 n y ≫ (shiftFunctor _ n).map (f ≫ g)) ∧
    (∀ n c, e2 n (rpl q i ι (pullback.fst (g2 ≫ g1 ≫ p) ι) (pullback.snd (g2 ≫ g1 ≫ p) ι) (g2 ≫ g1 ≫ p)
          pullback.condition n c) = eL n c ≫ (shiftFunctor _ n).map ℓ)

theorem LeafCons_of (hL : LeafLoc) (hG : LeafGlob) : LateralTheory.E.EtaleTopologySheaves.LeafCons := by
  intro q _ i B W Y0 Y1 Y2 ι _ p g1 g2
  obtain ⟨K0, K1, K2, L, f, g, ℓ, l0, l1, l2, lL, r0, r1, r2, rL, mf, mg, mℓ⟩ := hL q i ι p g1 g2
  obtain ⟨e0, e2, eL, h1, h2, h3, h4⟩ :=
    hG q i ι p g1 g2 K0 K1 K2 L f g ℓ l0 l1 l2 lL r0 r1 r2 rL mf mg mℓ
  exact ⟨K0, K1, K2, L, f, g, ℓ, l0, l1, l2, lL, e0, e2, eL, r0, r1, r2, rL, mf, mg, mℓ, h1, h2, h3, h4⟩

end LateralTheory.E.LeafConsPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.DescendPf
noncomputable section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.DescendPf

def Spread : Prop := ∀ (A O : CommRingCat.{0}) (f : A ⟶ O), IE f →
  ∀ (C : Type) [CommRing C] [Algebra O C] [Algebra.Etale O C],
  ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (d : B ⟶ O) (C' : CommRingCat.{0}) (e : B ⟶ C') (c : C' →+* C),
    Et g ∧ Et e ∧ g ≫ d = f ∧
    IsPushout e d (CommRingCat.ofHom c) (CommRingCat.ofHom (algebraMap O C))

theorem Descend_of (hS : Spread) : LateralTheory.E.ColimPf.Descend := by
  intro A O f hf C _ _ _
  obtain ⟨B, g, d, C', e, c, hg, he, hgd, hP⟩ := hS A O f hf C
  refine ⟨B, g, d, C', e, c, hg, he, hgd, ?_, ?_, ?_⟩
  · ext y
    have := congrArg (fun φ => φ.hom y) hP.w
    simpa using this
  · intro k hk
    have hw : e ≫ k = d ≫ 𝟙 O := by rw [hk, Category.comp_id]
    let s := hP.desc k (𝟙 O) hw
    have h1 : CommRingCat.ofHom c ≫ s = k := hP.inl_desc k (𝟙 O) hw
    have h2 : CommRingCat.ofHom (algebraMap O C) ≫ s = 𝟙 O := hP.inr_desc k (𝟙 O) hw
    refine ⟨{ s.hom with commutes' := fun r => ?_ }, ?_⟩
    · have := congrArg (fun φ => φ.hom r) h2
      change s.hom (algebraMap O C r) = (𝟙 O : O ⟶ O).hom r
      exact this
    · ext y
      have := congrArg (fun φ => φ.hom y) h1
      simpa using this
  · intro R _ α β h1 h2
    have := hP.hom_ext (W := CommRingCat.of R) (k := CommRingCat.ofHom α) (l := CommRingCat.ofHom β) ?_ ?_
    · exact congrArg CommRingCat.Hom.hom this
    · ext y
      exact DFunLike.congr_fun h2 y
    · ext y
      exact DFunLike.congr_fun h1 y

end LateralTheory.E.DescendPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.TwTrivPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.TwistTrivial

theorem genRes {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  unfold twGen ofRings.sec
  have h := congrArg (fun φ => φ.hom (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom
    (((Scheme.Γ ⋙ twF q i).map g.op).hom _) = _
  congr 1
  exact congrArg Submodule.Quotient.mk Finsupp.mapDomain_single

theorem prim_map_comp {q : ℕ} {X Y S : Scheme.{0}} (ζ : Prim q Γ(S, ⊤)) (s : X ⟶ S) (f : Y ⟶ X) :
    (ζ.map s.appTop.hom).map f.appTop.hom = ζ.map (f ≫ s).appTop.hom := by
  apply Subtype.ext
  change f.appTop.hom (s.appTop.hom ζ.1) = (f ≫ s).appTop.hom ζ.1
  rw [Scheme.Hom.comp_appTop]
  rfl

def Mul : Prop := ∀ (q : ℕ), ∃ μ : ∀ (j k l : ℤ), j + k = l → ∀ (X : Scheme.{0}), Sec (tw q k) X → (Sec (tw q j) X →+ Sec (tw q l) X),
  (∀ (j k l : ℤ) (h : j + k = l) {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Sec (tw q k) X) (x : Sec (tw q j) X),
      Sec.res f (μ j k l h X y x) = μ j k l h Y (Sec.res f y) (Sec.res f x)) ∧
  (∀ (j k l k' : ℤ) (h : j + k = l) (h' : l + k' = j) (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (x : Sec (tw q j) X),
      μ l k' j h' X (twGen k' ζ) (μ j k l h X (twGen k ζ) x) = x)

theorem TwTriv_of (hM : Mul) : LateralTheory.E.LCIsoPf.TwTriv := by
  intro q i S ζ
  obtain ⟨μ, hnat, hcan⟩ := hM q
  refine ⟨fun X s => AddEquiv.mk' ⟨μ 0 i i (zero_add i) X (twGen i (ζ.map s.appTop.hom)),
      μ i (-i) 0 (add_neg_cancel i) X (twGen (-i) (ζ.map s.appTop.hom)),
      fun x => hcan 0 i i (-i) (zero_add i) (add_neg_cancel i) X _ x,
      fun y => hcan i (-i) 0 i (add_neg_cancel i) (zero_add i) X _ y⟩ (fun a b => map_add (μ 0 i i (zero_add i) X (twGen i (ζ.map s.appTop.hom))) a b), ?_⟩
  intro X Y s t f hf x
  change Sec.res f (μ 0 i i _ X _ x) = μ 0 i i _ Y _ (Sec.res f x)
  rw [hnat, genRes, prim_map_comp, hf]

end LateralTheory.E.TwistTrivial
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.EtaleEmbedding
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.EmbedPf

def AffClosed : Prop := ∀ (A : Type) [CommRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A))
  [LocallyOfFiniteType p] (V : X.Opens), IsAffineOpen V →
    ∃ (n : ℕ) (e : V.toScheme ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) A))), IsClosedImmersion e ∧
      e ≫ Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A))) = V.ι ≫ p

def Chart : Prop := ∀ (A : Type) [CommRing A] (n : ℕ), ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of A))
  (j : Spec (CommRingCat.of (MvPolynomial (Fin n) A)) ⟶ P), IterLine q ∧ IsOpenImmersion j ∧
    j ≫ q = Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)))

theorem affClosed : AffClosed := by
  intro A _ X p _ V hV
  haveI : IsAffine V.toScheme := hV
  have hfT : LocallyOfFiniteType (V.ι ≫ p) := inferInstance
  have happ := HasRingHomProperty.appTop @LocallyOfFiniteType (V.ι ≫ p) hfT
  let g : CommRingCat.of A ⟶ Γ(V.toScheme, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (V.ι ≫ p).appTop
  have hg : g.hom.FiniteType := by
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    exact RingHom.FiniteType.comp happ h1
  letI : Algebra A Γ(V.toScheme, ⊤) := g.hom.toAlgebra
  have hft : Algebra.FiniteType A Γ(V.toScheme, ⊤) := hg
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
  refine ⟨n, V.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom), ?_, ?_⟩
  · have hs := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ.toRingHom) hφ
    have hi : IsClosedImmersion V.toScheme.toSpecΓ := inferInstance
    exact @IsClosedImmersion.comp _ _ _ _ _ hi hs
  · have hcomp : CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)) ≫ CommRingCat.ofHom φ.toRingHom = g := by
      ext a
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
      exact φ.commutes a
    have h2 : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A))) =
        Spec.map g := by rw [← Spec.map_comp, hcomp]
    have h3 : V.toScheme.toSpecΓ ≫ Spec.map g = V.ι ≫ p := by
      have hn := Scheme.toSpecΓ_naturality (V.ι ≫ p)
      have h4 : Spec.map g = Spec.map (V.ι ≫ p).appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv :=
        Spec.map_comp _ _
      rw [h4, ← Category.assoc, ← hn, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    refine Eq.trans ?_ h3
    rw [Category.assoc]
    exact congrArg (fun t => V.toScheme.toSpecΓ ≫ t) h2

theorem Embed_of (hA : AffClosed) (hC : Chart) : LateralTheory.E.ChowGraphCut.Embed := by
  intro A _ X p _ V hV
  obtain ⟨n, e, he, hep⟩ := hA A p V hV
  obtain ⟨P, q, j, hq, hj, hjq⟩ := hC A n
  haveI := hj
  haveI := he
  refine ⟨P, q, j.opensRange, e ≫ j.isoOpensRange.hom, hq, inferInstance, ?_⟩
  rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, hjq, hep]

end LateralTheory.E.EmbedPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.NormACPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CompCut

namespace LateralTheory.E.NormACPf

theorem aic_integralClosure (A K : Type) [CommRing A] [CommRing K] [Algebra A K] (hK : AIC K) :
    AIC (integralClosure A K) := by
  intro p hp hd
  obtain ⟨a, ha⟩ := hK (p.map (integralClosure A K).val.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective Subtype.val_injective])
  have hint : IsIntegral (integralClosure A K) a := ⟨p, hp, by
    rw [Polynomial.eval_map] at ha; exact ha⟩
  have haA : a ∈ integralClosure A K := isIntegral_trans (R := A) a hint
  refine ⟨⟨a, haA⟩, Subtype.val_injective ?_⟩
  have h4 : (integralClosure A K).val.toRingHom (Polynomial.eval (⟨a, haA⟩ : integralClosure A K) p) = 0 := by
    rw [← Polynomial.eval₂_at_apply]; rw [Polynomial.eval_map] at ha; exact ha
  simpa using h4

theorem aic_of_subsingleton (R : Type) [CommRing R] [Subsingleton R] : AIC R :=
  fun _ _ _ => ⟨0, Subsingleton.elim _ _⟩

theorem aic_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : AIC R) : AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have h4 : e.symm.toRingHom (Polynomial.eval (e a) p) = 0 := by
    rw [← Polynomial.eval₂_at_apply]; rw [Polynomial.eval_map] at ha; simpa using ha
  simpa using h4

theorem aic_spec_field (K : Type) [Field K] (hA : AIC K) (W : (Spec (CommRingCat.of K)).Opens) :
    AIC Γ(Spec (CommRingCat.of K), W) := by
  by_cases h : (default : Spec (CommRingCat.of K)) ∈ W
  · have : W = ⊤ := by
      ext x; simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      rwa [Subsingleton.elim x default]
    subst this
    exact aic_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm hA
  · have : W = ⊥ := by
      ext x; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      rwa [Subsingleton.elim x default]
    subst this
    exact aic_of_subsingleton _

def Loc : Prop := ∀ (Z : Scheme.{0}), IsIntegral Z → (∀ z : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ z ∈ U ∧ AIC Γ(Z, U)) →
  ∀ U : Z.Opens, IsAffineOpen U → (U : Set Z).Nonempty → AIC Γ(Z, U)

theorem NormAC_of (hL : Loc) : NormAC := by
  intro P _ _ K _ hF hA v
  let := hF.toField
  have hI : IsIntegral v.normalization := inferInstance
  refine ⟨hI, hL _ hI ?_⟩
  intro z
  obtain ⟨V, hV, hz, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp P.isBasis_affineOpens
    (show v.fromNormalization z ∈ (⊤ : P.Opens) from trivial)
  refine ⟨v.fromNormalization ⁻¹ᵁ V, hV.preimage _, hz, ?_⟩
  letI := (v.app V).hom.toAlgebra
  exact aic_of_ringEquiv (v.normalizationObjIso hV).commRingCatIsoToRingEquiv.symm
    (aic_integralClosure _ _ (aic_spec_field K hA _))

end LateralTheory.E.NormACPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.PartCPf
noncomputable section
open Polynomial LateralTheory.E.PartDiagCut GlobalTheory.EtC

namespace LateralTheory.E.PartCPf

def Split : Prop := ∀ (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B →
  ∀ (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (p : Polynomial (PiLocalization₂ I P)), p.Monic →
    ∃ (n : ℕ) (r : Fin n → PiLocalization₂ I P), p = ∏ l, (X - C (r l))

def Idem : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (n : ℕ) (y : Fin n → PiLocalization₂ I P),
  ∏ l, y l ∈ I.map (βP I P) →
  IsUnit (Ideal.Quotient.mk (I.map (βP I P)) (∑ l, ∏ m ∈ Finset.univ.erase l, y m)) →
  ∃ f : Fin n → B, (∀ l, IsIdempotentElem (Ideal.Quotient.mk I (f l))) ∧
    (∀ l m, l ≠ m → Ideal.Quotient.mk I (f l) * Ideal.Quotient.mk I (f m) = 0) ∧
    ∑ l, Ideal.Quotient.mk I (f l) = 1 ∧ ∀ l, βP I P (f l) * y l ∈ I.map (βP I P)

def Lift : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (p : Polynomial (PiLocalization₂ I P)) (a₀ : PiLocalization₂ I P)
  (n : ℕ) (r : Fin n → PiLocalization₂ I P) (f : Fin n → B), p = ∏ l, (X - C (r l)) →
  (∀ l, IsIdempotentElem (Ideal.Quotient.mk I (f l))) →
  (∀ l m, l ≠ m → Ideal.Quotient.mk I (f l) * Ideal.Quotient.mk I (f m) = 0) →
  ∑ l, Ideal.Quotient.mk I (f l) = 1 → (∀ l, βP I P (f l) * (a₀ - r l) ∈ I.map (βP I P)) →
  ∃ (Q : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (h : P ≤ Q) (a : PiLocalization₂ I Q), (p.map (stageMap I h)).IsRoot a ∧
    a - stageMap I h a₀ ∈ I.map (βP I Q)

theorem eval_prod_lin {R : Type} [CommRing R] (n : ℕ) (r : Fin n → R) (x : R) :
    (∏ l, (X - C (r l))).eval x = ∏ l, (x - r l) := by
  simp [eval_prod]

theorem deriv_prod_lin {R : Type} [CommRing R] (n : ℕ) (r : Fin n → R) (x : R) :
    (derivative (∏ l, (X - C (r l)))).eval x = ∑ l, ∏ m ∈ Finset.univ.erase l, (x - r m) := by
  classical
  rw [derivative_prod_finset]
  simp [eval_finsetSum, eval_prod]

theorem PartC_of (hs : Split) (hi : Idem) (hl : Lift) : LateralTheory.E.PartDiagCut.PartC := by
  intro B _ _ I hB P p a₀ hm hev hder
  obtain ⟨n, r, hp⟩ := hs B I hB P p hm
  have h1 : ∏ l, (a₀ - r l) ∈ I.map (βP I P) := by
    rw [← eval_prod_lin n r a₀, ← hp]; exact hev
  have h2 : IsUnit (Ideal.Quotient.mk (I.map (βP I P)) (∑ l, ∏ m ∈ Finset.univ.erase l, (a₀ - r m))) := by
    rw [← deriv_prod_lin n r a₀, ← hp]; exact hder
  obtain ⟨f, hfi, hfo, hfs, hfy⟩ := hi B I P n (fun l => a₀ - r l) h1 h2
  exact hl B I P p a₀ n r f hp hfi hfo hfs hfy

theorem idem_of (hIP : LateralTheory.E.HensCut.IdemPart) (hA : LateralTheory.E.PartDiagCut.PartA) : Idem := by
  intro B _ I P n y hprod hsum
  let φ := RingEquiv.ofBijective (Ideal.quotientMap (I.map (βP I P)) (βP I P) Ideal.le_comap_map) (hA B I P)
  obtain ⟨e, hei, heo, hes, hey⟩ := hIP (PiLocalization₂ I P ⧸ I.map (βP I P)) n
    (fun l => Ideal.Quotient.mk (I.map (βP I P)) (y l))
    (by rw [← map_prod]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hprod)
    (by simpa [map_sum, map_prod] using hsum)
  choose f hf using fun l => Ideal.Quotient.mk_surjective (φ.symm (e l))
  refine ⟨f, fun l => ?_, fun l m hlm => ?_, ?_, fun l => ?_⟩
  · unfold IsIdempotentElem; rw [hf, ← map_mul, (hei l).eq]
  · rw [hf, hf, ← map_mul, heo l m hlm, map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp_rw [hf]; rw [← map_sum, hes, map_one]
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    have h1 : φ (Ideal.Quotient.mk I (f l)) = e l := by rw [hf]; exact φ.apply_symm_apply _
    have h2 : Ideal.Quotient.mk (I.map (βP I P)) (βP I P (f l)) = e l := by
      rw [← h1]; simp [φ, Ideal.quotientMap_mk]
    rw [h2]; exact hey l

theorem PartC_of' (hs : Split) (hIP : LateralTheory.E.HensCut.IdemPart) (hA : LateralTheory.E.PartDiagCut.PartA) (hl : Lift) :
    LateralTheory.E.PartDiagCut.PartC :=
  PartC_of hs (idem_of hIP hA) hl

end LateralTheory.E.PartCPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafPairExtPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafPairExtPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafUnitPairGPf

def LeafActSgl : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) L, IsAct q i L →
  ∃ lam : Pair (sgl (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
    ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      lam.mul U 0 t t (zero_add t) (Sec.map (sglι (tw q 0)) a) b = L U t a b

def LeafExtAlongAug : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (lam : Pair (sgl (tw q 0)) (res _ (tw q i)) (res _ (tw q i))),
  ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
    ∀ (U : Scheme.{0}) (t : ℤ) (x : Sec ((sgl (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      ν.mul U 0 t t (zero_add t) (Sec.map ((resAug (tw q 0)).f 0) x) b = lam.mul U 0 t t (zero_add t) x b

section Act
variable {q : ℕ} {i : ℤ}

def actPair (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) (U : Scheme.{0}) (s t w : ℤ)
    (h : s + t = w) : Sec ((sgl (tw q 0)).X s) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)]
      Sec ((res _ (tw q i)).X w) U :=
  if hs : s = 0 then
    ((L U t).compl₁₂ (((HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (tw q 0) s hs).hom.hom.app (op U)).hom)
      LinearMap.id).compr₂ ((((res _ (tw q i)).XIsoOfEq (show t = w by omega)).hom.hom.app (op U)).hom)
  else 0

theorem actPair_pos (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) (U : Scheme.{0}) (t : ℤ)
    (a : Sec ((sgl (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U) :
    actPair L U 0 t t (zero_add t) a b =
      L U t (Sec.map (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (tw q 0) 0 rfl).hom a) b := by
  simp [actPair, HomologicalComplex.XIsoOfEq_rfl]

theorem actPair_neg (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) (U : Scheme.{0}) (s t w : ℤ)
    (h : s + t = w) (hs : s ≠ 0) : actPair L U s t w h = 0 := by
  simp [actPair, hs]

end Act

theorem LeafPairExt_of (h1 : LeafActSgl) (h2 : LeafExtAlongAug) : LeafPairExt := by
  intro q _ i L hL
  obtain ⟨lam, hlam⟩ := h1 q i L hL
  obtain ⟨ν, hν⟩ := h2 q i lam
  refine ⟨ν, fun U t a b => ?_⟩
  have e : Sec.map (resι _ (tw q 0)) a = Sec.map ((resAug (tw q 0)).f 0) (Sec.map (sglι (tw q 0)) a) := rfl
  rw [e, hν, hlam]

theorem etale_twist_action_induces_single_complex_pairing_holds : LeafActSgl := by
  intro q _ i L hL
  refine ⟨⟨actPair L, ?_, ?_⟩, ?_⟩
  · intro V U g s t w h a b
    by_cases hs : s = 0
    · subst hs
      obtain rfl : w = t := by omega
      rw [actPair_pos, actPair_pos, hL.1]
      congr 2
    · rw [actPair_neg L U s t w h hs, actPair_neg L V s t w h hs]
      simp
  · intro U s t w h a b
    have hd : (sgl (tw q 0)).d s (s + 1) = 0 := by simp
    rw [hd]
    have h0 : Sec.map (0 : (sgl (tw q 0)).X s ⟶ (sgl (tw q 0)).X (s + 1)) a = 0 := rfl
    rw [h0, map_zero, LinearMap.zero_apply, zero_add]
    by_cases hs : s = 0
    · subst hs
      obtain rfl : w = t := by omega
      rw [actPair_pos, actPair_pos, Int.negOnePow_zero, one_smul]
      exact hL.2 U _ _ b
    · rw [actPair_neg L U s t w h hs, actPair_neg L U s (t + 1) (w + 1) (by omega) hs]
      simp
  · intro U t a b
    change actPair L U 0 t t (zero_add t) _ b = _
    rw [actPair_pos]
    congr 1

theorem LeafPairExt_of' (h2 : LeafExtAlongAug) : LeafPairExt := LeafPairExt_of etale_twist_action_induces_single_complex_pairing_holds h2

end LateralTheory.E.LeafPairExtPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.UnitSections
section -- merged from Development.EtaleCohomology.EtaleSheaves.TwistGenerators.LeafTwGenIndepOf
section -- merged from Development.EtaleCohomology.EtaleSheaves.TwistGenerators
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitSecPf

def LeafTwGenIndep : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), twGen 0 ζ = twGen 0 ξ

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map (Scheme.Γ.map g.op).hom) := by
  unfold twGen ofRings.sec
  have h := congrArg (fun t => t.hom (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  simp only [ModuleCat.hom_comp] at h
  refine h.symm.trans (congrArg (fun y => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom y) ?_)
  exact congrArg (Submodule.Quotient.mk (p := twRel q i Γ(V, ⊤))) (Finsupp.mapDomain_single (f := Prim.map (Scheme.Γ.map g.op).hom))

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (k : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res k x) = Sec.res (h ≫ k) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  show (F.obj.map (𝟙 U).op).hom x = x
  rw [op_id, F.obj.map_id]
  rfl

theorem tw_isSheafFor (q : ℕ) (U : Scheme.{0}) (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U) :
    Presieve.IsSheafFor ((tw q 0).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) S.arrows := by
  have hF := (Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology (tw q 0).obj
    (forget (ModuleCat.{1} (ULift.{1} (ZMod q))))).1 (tw q 0).property
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact hF S hS

section Glue

def cov (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : Sieve U := Classical.choose (hP q U hU)

theorem cov_mem (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : cov hP q U hU ∈ Scheme.etaleTopology U :=
  (Classical.choose_spec (hP q U hU)).1

theorem cov_prim (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (V : Scheme.{0}) (g : V ⟶ U) (hg : (cov hP q U hU).arrows g) :
    Nonempty (Prim q Γ(V, ⊤)) :=
  (Classical.choose_spec (hP q U hU)).2 V g hg

def fam (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) :
    Presieve.FamilyOfElements ((tw q 0).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) (cov hP q U hU).arrows :=
  fun V g hg => twGen 0 (Classical.choice (cov_prim hP q U hU V g hg))

theorem fam_compat (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : (fam hP q U hU).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro Y Z f g hf
  change _ = Sec.res g (twGen 0 _)
  rw [twGen_res]
  exact hI q Z _ _

def one (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : Sec (tw q 0) U :=
  (tw_isSheafFor q U _ (cov_mem hP q U hU)).amalgamate (fam hP q U hU) (fam_compat hP hI q U hU)

theorem one_char (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (W : Scheme.{0}) (k : W ⟶ U) (ζ : Prim q Γ(W, ⊤)) :
    Sec.res k (one hP hI q U hU) = twGen 0 ζ := by
  refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) W ((cov hP q U hU).pullback k)
    (Scheme.etaleTopology.pullback_stable k (cov_mem hP q U hU)) _ _ fun V h hh => ?_
  rw [res_comp, twGen_res]
  have hv := (tw_isSheafFor q U _ (cov_mem hP q U hU)).valid_glue (fam_compat hP hI q U hU) (h ≫ k) hh
  refine hv.trans ?_
  exact hI q V _ _

end Glue

theorem LeafUnitSec_of (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) :
    LateralTheory.E.LeafOneExistsPf.LeafUnitSec := by
  intro q _
  refine ⟨one hP hI q, fun V U g hU hV => ?_, fun U hU ζ => ?_⟩
  · refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) V (cov hP q V hV) (cov_mem hP q V hV) _ _ fun W h hh => ?_
    obtain ⟨ζ⟩ := cov_prim hP q V hV W h hh
    rw [res_comp, one_char hP hI q U hU W _ ζ, one_char hP hI q V hV W h ζ]
  · rw [← one_char hP hI q U hU U (𝟙 U) ζ, res_id]

end LateralTheory.E.LeafUnitSecPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitSecPf.Indep

def LeafPowLocal : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), ∃ S : Sieve U,
  S ∈ Scheme.etaleTopology U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g →
    ∃ a : (ZMod q)ˣ, (ξ.map (Scheme.Γ.map g.op).hom).1 = (ζ.map (Scheme.Γ.map g.op).hom).1 ^ (a : ZMod q).val

theorem twGen_pow {q : ℕ} {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)
  simp
  rfl

theorem LeafTwGenIndep_of (hL : LeafPowLocal) : LeafTwGenIndep := by
  intro q _ U ζ ξ
  obtain ⟨S, hS, hSa⟩ := hL q U ζ ξ
  refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) U S hS _ _ fun V g hg => ?_
  obtain ⟨a, ha⟩ := hSa V g hg
  rw [twGen_res, twGen_res]
  exact (twGen_pow _ _ a ha).symm

theorem LeafUnitSec_of (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hL : LeafPowLocal) :
    LateralTheory.E.LeafOneExistsPf.LeafUnitSec :=
  LateralTheory.E.LeafUnitSecPf.LeafUnitSec_of hP (LeafTwGenIndep_of hL)

end LateralTheory.E.LeafUnitSecPf.Indep
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.UnitSections

theorem powLocal : LateralTheory.E.LeafUnitSecPf.Indep.LeafPowLocal := by
  intro q _ U ζ ξ
  obtain ⟨s, hs, hf⟩ := LateralTheory.E.L_prim_locPf.algPow q Γ(U, ⊤) ζ ξ
  obtain ⟨S, hS, hP⟩ := LateralTheory.E.L_prim_locPf.loc_of_span s hs
    (P := fun V g => ∃ a : (ZMod q)ˣ,
      (ξ.map (Scheme.Γ.map g.op).hom).1 = (ζ.map (Scheme.Γ.map g.op).hom).1 ^ (a : ZMod q).val) (by
      intro f hfs V g hu
      obtain ⟨a, n, hn⟩ := hf f hfs
      refine ⟨a, ?_⟩
      have h := LateralTheory.E.L_prim_locPf.eq_of_unit_kill g.appTop.hom hn hu
      rw [map_pow] at h
      exact h)
  exact ⟨S, hS, hP⟩

theorem LeafUnitSec_of : LateralTheory.E.LeafOneExistsPf.LeafUnitSec :=
  LateralTheory.E.LeafUnitSecPf.Indep.LeafUnitSec_of LateralTheory.E.LeafPrimCoverPf.LeafPrimCover_of powLocal

end LateralTheory.E.UnitSections
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CoverExistence
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.CoverExistence

theorem Cover_of : LateralTheory.E.ChowGraphCut.Cover := by
  intro A _ X p _ _
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have h : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := by
    intro x
    obtain ⟨V, hV, hxV, -⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨V, hV, hxV⟩
  choose V hV hxV using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨t.card, fun j => V (t.equivFin.symm j), fun j => hV _, fun j => ⟨_, hxV _⟩, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

end LateralTheory.E.CoverExistence
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StageProdPf
noncomputable section
open GlobalTheory.EtC

namespace LateralTheory.E.StageProdPf
open LateralTheory.E.PartDiagCut

theorem zero_not_mem_S {B : Type} [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (e : P.1) :
    (0 : B) ∉ S I e.1 := by
  rintro ⟨t, ht⟩
  simp only [map_zero, zero_mul] at ht
  exact (P.idem e.1 e.2).2 ht.symm

theorem StageProd_of (hloc : LateralTheory.E.HensCut.LocAIC) : LateralTheory.E.PartDiagCut.StageProd := by
  intro q B _ _ I hB hq P
  let R : Fin P.1.card → Type := fun k => Localization (S I (P.1.equivFin.symm k).1)
  refine ⟨P.1.card, R, fun k => inferInstance, fun k => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hloc B (S I (P.1.equivFin.symm k).1) (zero_not_mem_S I P _) hB
    refine ⟨h1, h2, ?_⟩
    have := hq.map (algebraMap B (R k))
    rwa [map_natCast] at this
  · exact ⟨(RingEquiv.piCongrLeft (fun e : P.1 => Localization (S I e.1)) P.1.equivFin.symm).symm⟩

end LateralTheory.E.StageProdPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.DiagIdPf
noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.DiagIdPf

theorem par_self {A : Type} [CommRing A] {P : LateralTheory.E.PartDiagCut.Part A} (h : P ≤ P) (e : P.1) : par h e = e := by
  apply Subtype.ext
  by_contra hne
  have h1 := par_spec h e
  have h2 := P.orth e.1 e.2 (par h e).1 (par h e).2 (fun h' => hne h'.symm)
  exact (P.idem e.1 e.2).2 (h1.symm.trans h2)

theorem aux {B : Type} [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (x : PiLocalization₂ I P) (e0 e : P.1) (hee : e0 = e)
    (hle : S I e0.1 ≤ (S I e.1).comap (RingHom.id B)) :
    IsLocalization.map (M := S I e0.1) (T := S I e.1) (Localization (S I e.1)) (RingHom.id B) hle (x e0) = x e := by
  subst hee
  exact IsLocalization.map_id _ _

theorem DiagId_of : LateralTheory.E.PartDiagCut.DiagId := by
  intro B _ I P h
  refine RingHom.ext fun x => funext fun e => ?_
  simp only [stageMap, RingHom.pi_apply, RingHom.comp_apply, Pi.evalRingHom_apply, RingHom.id_apply]
  exact aux I P x (par h e) e (par_self h e) _

end LateralTheory.E.DiagIdPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.BinPfChains
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC
namespace LateralTheory.E.BinPfChains
variable (R : Type) [CommRing R]
instance freeModPres : PreservesColimitsOfShape (Discrete WalkingPair) (ModuleCat.free.{1} (ULift.{1} R)) := by
  have := (ModuleCat.adj.{1} (ULift.{1} R)).leftAdjoint_preservesColimits
  infer_instance
instance freePres : PreservesColimitsOfShape (Discrete WalkingPair) (free R) := by unfold free freeP; infer_instance
instance whPres : PreservesColimitsOfShape (Discrete WalkingPair) ((SimplicialObject.whiskering PSh (Shv R)).obj (free R)) := by
  change PreservesColimitsOfShape (Discrete WalkingPair) ((Functor.whiskeringRight _ _ _).obj (free R))
  infer_instance
instance chainsPres : PreservesColimitsOfShape (Discrete WalkingPair) (chains R) := by
  unfold chains chainsN; infer_instance
theorem chainsCoprod : LateralTheory.E.BinPf.ChainsCoprod := by
  intro R _ U V
  have h : IsIso (coprodComparison (chains R) U V) := inferInstance
  have e : biprod.desc ((chains R).map (coprod.inl : U ⟶ U ⨿ V)) ((chains R).map (coprod.inr : V ⟶ U ⨿ V)) =
      (biprod.isoCoprod _ _).hom ≫ coprodComparison (chains R) U V := by
    apply biprod.hom_ext' <;> simp [coprodComparison, coprod.inl_desc, coprod.inr_desc]
  rw [e]; infer_instance

theorem bin_of (hD : LateralTheory.E.BinPf.DescEqv) : LateralTheory.E.ProdAcycPf.Bin :=
  LateralTheory.E.ProdAcycPf.Bin_of hD chainsCoprod

end LateralTheory.E.BinPfChains
end
end
