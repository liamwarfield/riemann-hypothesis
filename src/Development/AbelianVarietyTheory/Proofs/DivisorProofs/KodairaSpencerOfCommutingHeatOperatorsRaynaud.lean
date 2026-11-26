module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalPointOriginSmoothCommGroupScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedGroupPointSameDerivations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingHeatOperatorsActOnValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsKodairaSpencerFormalPointValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorSymbolUniquePrincipalPolarisation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricKodairaSpencerAbelianLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricKodairaSpencerAbelianLocus
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSAbLocusSymm

theorem tanBasis_of_basis' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    (t : SAB H (Sp R)) {n : ℕ} (b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) {T : Type} [CommRing T]
    (φ : R →+* T) :
    (∀ i, IsTanAtG t (spMap φ ≫ 𝟙 (Sp R)) (spMap (dualMap φ) ≫ (tv (b i)).left)) ∧
      ∀ w, IsTanAtG t (spMap φ ≫ 𝟙 (Sp R)) w →
        ∃! a : Fin n → T, IsCombAtG t (spMap φ ≫ 𝟙 (Sp R)) (fun i => spMap (dualMap φ) ≫ (tv (b i)).left) a w := by
  refine GlobalTheory.LocM.FrameBase.tanBasis_baseChange t φ (𝟙 (Sp R)) n _ (fun i => GlobalTheory.LieMet.isTan_tv (b i)) ?_
  intro w hw
  refine ⟨b.repr (GlobalTheory.LieMet.tanOf hw), ?_, fun a ha => ?_⟩
  · show IsCombAtG t _ _ _ (tv (GlobalTheory.LieMet.tanOf hw)).left
    rw [GlobalTheory.LieMet.isComb_iff]
    exact (b.sum_repr _).symm
  · have h := (GlobalTheory.LieMet.isComb_iff b a (GlobalTheory.LieMet.tanOf hw)).1 ha
    rw [h]
    ext i
    simp [Finsupp.single_apply]

theorem exists_symm_isKS_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), ∃ Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1), Θ₁ᵀ = Θ₁ ∧ IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hab n v' DV
  obtain ⟨Θ₁, hKS⟩ := GlobalTheory.T.exists_kodairaSpencer_abelianLocus_chartRing E H R t P m tt gam hmon htt hab n v' 0 DV
  refine ⟨Θ₁, ?_, hKS⟩
  let U : (Sp R).affineOpens := (Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens))
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))
  let ρ : R →+* Γ(Sp R, U.1) := ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤)
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hc : spMap ρ ≫ 𝟙 (Sp R) = chart U := by
    rw [Category.comp_id]
    show Spec.map _ = U.2.fromSpec
    rw [← (isAffineOpen_top (Sp R)).map_fromSpec U.2 (homOfLE ((Sp R).basicOpen_le (U := ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec]
    rw [show CommRingCat.ofHom ρ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op from rfl]
    erw [Spec.map_comp]
    rfl
  obtain ⟨hv, hb⟩ := tanBasis_of_basis' t v' ρ
  rw [hc] at hv hb
  have h2 : (U.1 : (Sp R).Opens) = PrimeSpectrum.basicOpen (∏ i, tt i) :=
    basicOpen_eq_of_affine (R := CommRingCat.of R) (∏ i, tt i)
  have h4 : ∀ q : Sp R, q ∈ ((U.1 : (Sp R).Opens) : Set (Sp R)) → ∏ i, tt i ∉ q.asIdeal := by
    intro q hq
    rw [h2] at hq
    exact hq
  have hx : ∀ s, ∏ i, tt i ∉ ((chart U) s).asIdeal := fun s =>
    h4 _ (by rw [← U.2.range_fromSpec]; exact ⟨s, rfl⟩)
  have hne : ∏ i, tt i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => htt i
  haveI : Nonempty (U.1 : (Sp R).Opens) := by
    refine ⟨⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R), ?_⟩⟩
    show _ ∈ ((U.1 : (Sp R).Opens) : Set (Sp R))
    rw [h2]
    show ∏ i, tt i ∉ (⊥ : Ideal R)
    simpa using hne
  haveI : IsDomain Γ(Sp R, U.1) := inferInstance
  let K := FractionRing Γ(Sp R, U.1)
  let x₀ : Γ(Sp R, U.1) →+* K := algebraMap _ _
  letI : Algebra ℚ K := ((x₀.comp ρ).comp (algebraMap ℚ R)).toAlgebra
  haveI : CharZero K := algebraRat.charZero K
  obtain ⟨PP', cub, sym, adj, prim, mm, -⟩ := sabPull proved_CubePullSt (spMap x₀ ≫ chart U) t
  have hx' : ∀ s, ∏ i, tt i ∉ ((spMap x₀ ≫ chart U) s).asIdeal := fun s => hx ((spMap x₀) s)
  obtain ⟨hP, hA, hK⟩ := GlobalTheory.AbLocusPol.isProper_relAmple_kTriv_of_abLocus E H R t P m tt htt hab _
    (spMap x₀ ≫ chart U) _ hx' ⟨mm⟩
  obtain ⟨P₀, e, he⟩ := GlobalTheory.PolDvr.exists_polAV _ hP hA hK
  obtain ⟨w, g, -⟩ := mm.lin
  obtain ⟨h1, h2'⟩ := he t.G (spMap x₀ ≫ chart U) mm.φ t.PP.L mm.cart ⟨w, g⟩
  have hsym := GlobalTheory.FibSym.map_transpose_eq E H (Sp R) t _ U n _ hv hb K x₀ P₀ _ h1 h2' le_rfl _ Θ₁ hKS
  ext i j
  have hij := congrFun (congrFun hsym i) j
  simp only [Matrix.transpose_apply, Matrix.map_apply] at hij
  exact IsFractionRing.injective Γ(Sp R, U.1) K hij

end GlobalTheory.KSAbLocusSymm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricKodairaSpencerAbelianLocusStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_kodairaSpencer_abelianLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), ∃ Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1), Θ₁ᵀ = Θ₁ ∧ IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ := by
  first | exact @GlobalTheory.KSAbLocusSymm.exists_symm_isKS_abLocus | exact GlobalTheory.KSAbLocusSymm.exists_symm_isKS_abLocus | (intros; apply GlobalTheory.KSAbLocusSymm.exists_symm_isKS_abLocus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRaynaudExtensionNoetherianLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRaynaudExtensionNoetherianLocal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.RayInt

open ReciprocityTheory.ChartRestriction.G.Semi TopologicalSpace

attribute [local instance] SplitExt.free SplitExt.finite

theorem mem_chart_of_mem {S : Scheme.{0}} (E : SplitExt S) (j : E.ChartIdx) (b : E.B.left)
    (h : ∀ k, b ∈ (E.O (E.basis k)).L.U (j k)) : b ∈ E.chart j := by
  have e : E.chart j = Finset.univ.inf (fun k => (E.O (E.basis k)).L.U (j k)) :=
    (Finset.inf_univ_eq_iInf _).symm
  rw [e, ← SetLike.mem_coe, Opens.coe_finset_inf]
  simp only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Set.iInf_eq_iInter, Set.mem_iInter,
    Function.comp_apply, SetLike.mem_coe]
  exact h

theorem isIntegral_of_isGt (R : Type) [CommRing R] [IsDomain R] (E : SplitExt (Spec (CommRingCat.of R)))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (hG : E.IsGt G) (hs : Smooth G.hom) :
    IsIntegral G.left := by
  obtain ⟨d⟩ := hG
  have hB := E.isAbelian
  haveI : Smooth E.B.hom := hB.smooth
  haveI : GeometricallyConnected E.B.hom := hB.geomConnected
  have hSne : Nonempty (Spec (CommRingCat.of R)) := inferInstance
  have hBne : Nonempty E.B.left := ⟨(η[E.B] : 𝟙_ _ ⟶ E.B).left (show (𝟙_ (Over _)).left from hSne.some)⟩
  haveI : IrreducibleSpace E.B.left :=
    GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain R E.B ‹_› ‹_› hBne
  haveI : IsReduced E.B.left := GlobalTheory.isReduced_of_smooth_of_isReduced E.B.hom
  haveI : IsIntegral E.B.left := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : IsReduced G.left := GlobalTheory.isReduced_of_smooth_of_isReduced G.hom
  obtain ⟨b⟩ := hBne
  have hk : ∀ k, ∃ i, b ∈ (E.O (E.basis k)).L.U i := fun k => by
    have hb : b ∈ (⊤ : E.B.left.Opens) := trivial
    rw [← (E.O (E.basis k)).isLB.cover, Opens.mem_iSup] at hb
    exact hb
  choose j hj using hk
  have hbj : b ∈ E.chart j := mem_chart_of_mem E j b hj
  obtain ⟨V, hV, hbV, hVj⟩ := (Opens.isBasis_iff_nbhd.mp E.B.left.isBasis_affineOpens) hbj
  have hbV' : b ∈ V := hbV
  haveI : Nonempty V := ⟨⟨b, hbV'⟩⟩
  haveI := d.q_affine
  haveI := d.q_flat
  have hsurj := d.q_surjective
  set W : G.left.Opens := d.q.left ⁻¹ᵁ V with hWdef
  have hV : IsAffineOpen V := hV
  have hW : IsAffineOpen W := hV.preimage d.q.left
  have hbij := d.coord j V hV hVj
  haveI : IsDomain Γ(G.left, W) :=
    Function.Injective.isDomain (RingEquiv.ofBijective _ hbij).symm.toRingHom
      (RingEquiv.ofBijective _ hbij).symm.injective
  obtain ⟨g, hg⟩ := hsurj.surj b
  have hgW : g ∈ W := by show d.q.left g ∈ V; rw [hg]; exact hbV'
  haveI : Nonempty W := ⟨⟨g, hgW⟩⟩
  haveI : IsAffine W := hW
  haveI : IsDomain Γ(W, ⊤) :=
    Function.Injective.isDomain (W.topIso).commRingCatIsoToRingEquiv.toRingHom
      (W.topIso).commRingCatIsoToRingEquiv.injective
  haveI : IsIntegral W := isIntegral_of_isAffine_of_isDomain W
  have hirrW : IsIrreducible (W : Set G.left) := by
    have hI := (IrreducibleSpace.isIrreducible_univ W).image (⇑W.ι) (Scheme.Hom.continuous _).continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at hI
  have hη : genericPoint E.B.left ∈ V :=
    ((genericPoint_spec E.B.left).mem_open_set_iff V.isOpen).2 ⟨b, trivial, hbV'⟩
  have hcl : closure (W : Set G.left) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap d.q.left (genericPoint_specializes (d.q.left z))
    have hz'W : z' ∈ (W : Set G.left) := by show d.q.left z' ∈ V; rw [e]; exact hη
    exact closure_mono (Set.singleton_subset_iff.2 hz'W) (specializes_iff_mem_closure.mp hz')
  haveI : IrreducibleSpace G.left := by
    rw [irreducibleSpace_def]
    have := hirrW.closure
    rwa [hcl] at this
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem isIntegral_H : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), IsIntegral Y.H.left := by
  intro R _ _ _ _ Q O _ _ _ oa Y
  exact isIntegral_of_isGt R _ Y.H Y.isGt (GlobalTheory.RayTan.smooth_H R Q O oa Y)

end GlobalTheory.RayInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRaynaudExtensionNoetherianLocalStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_raynaudExtension_noetherian_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), IsIntegral Y.H.left := by
  first | exact @GlobalTheory.RayInt.isIntegral_H | exact GlobalTheory.RayInt.isIntegral_H | (intros; apply GlobalTheory.RayInt.isIntegral_H <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisUniformisedGroupOfRaynaudExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisUniformisedGroupOfRaynaudExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TanRayBasis

theorem vBasis_of_isPointOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∃ b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G), ⇑b = v' := by
  intro E _ _ _ H R _ _ _ _ _ _ t P
  letI := H.starRing
  intro Y n vH v' hv
  obtain ⟨b, hb⟩ := GlobalTheory.TanRay.tanBasis_of_isPointOf E H R t P Y n vH v' hv
  exact ⟨b, funext hb⟩

end GlobalTheory.TanRayBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisUniformisedGroupOfRaynaudExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentBasis_uniformisedGroup_of_raynaudExtension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∃ b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G), ⇑b = v' := by
  first | exact @GlobalTheory.TanRayBasis.vBasis_of_isPointOf | exact GlobalTheory.TanRayBasis.vBasis_of_isPointOf | (intros; apply GlobalTheory.TanRayBasis.vBasis_of_isPointOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerAffineChartOfBasicOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerAffineChartOfBasicOpen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.KSChartRes

theorem isUnit_of_comap_mem {A S : Type} [CommRing A] [CommRing S] (φ : A →+* S) (s : A)
    (h : ∀ x : PrimeSpectrum S, PrimeSpectrum.comap φ x ∈ PrimeSpectrum.basicOpen s) : IsUnit (φ s) := by
  by_contra hn
  obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top hn)
  exact h ⟨m, hm.isPrime⟩ (hsm (Ideal.mem_span_singleton_self _))

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap α = spMap (β.comp α) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    (dualMap β).comp (dualMap α) = dualMap (β.comp α) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem isKS_top_of_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (m : ℕ) (tt : Fin m → R) (n : ℕ) (v' : Fin n → TanM (𝟙 (Sp R)) t.G) (D : Derivation ℤ R R) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)) (Θ : Matrix (Fin n) (Fin n) R), (∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D r))) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV ((((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).mapMatrix Θ) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix Θ) := by
  intro E _ _ _ H R _ _ _ _ _ _ t m tt n v' D DV Θ hD ⟨J, Wc, j, d, hsup, hj, hfld, hcomp, htest⟩

  set s := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i) with hs
  set Wa := (Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) s with hWa
  have hWV : ∀ i, Wc i ≤ t.G.hom ⁻¹ᵁ Wa.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t.G.hom.preimage_mono inf_le_left))
  have hle : Wa.1 ≤ ⊤ := le_top
  refine ⟨J, Wc, j, d, ?_, hj, hfld, fun i h r => ?_, fun i i' O hO f S _ φ g₀ w hg₀ hO' hw => ?_⟩
  · rw [hsup, top_inf_eq]
    exact congrArg _ (inf_idem _)
  · have e : ∀ x, (t.G.hom.appLE ⊤ (Wc i) h).hom x =
        (t.G.hom.appLE Wa.1 (Wc i) (hWV i)).hom (((Sp R).presheaf.map (homOfLE hle).op).hom x) := fun x =>
      (congrArg (fun k => k.hom x) (t.G.hom.map_appLE (hWV i) (homOfLE hle).op)).symm
    have hr : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = r :=
      Iso.hom_inv_id_apply _ _
    rw [e, e, hcomp i (hWV i)]
    have := hD ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)
    rw [hr] at this
    exact congrArg _ this
  · have hOW : O ≤ t.G.hom ⁻¹ᵁ (Wa.1 ⊓ (Sp R).basicOpen s) :=
      hO.trans (inf_le_left.trans ((le_iSup Wc i).trans hsup.le))
    have hu : IsUnit (φ s) := by
      refine isUnit_of_comap_mem φ s fun x => ?_
      have hx : g₀ x ∈ O := hO' (show x ∈ (⊤ : (Sp S).Opens) from trivial)
      have hV : t.G.hom (g₀ x) ∈ (Sp R).basicOpen s := (hOW hx).2
      have e1 : t.G.hom (g₀ x) = (g₀ ≫ t.G.hom) x := rfl
      rw [e1, hg₀] at hV
      have h2 : (spMap φ) x ∈ (GlobalTheory.LogKS.chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ⁻¹ᵁ (Sp R).basicOpen s := hV
      change (spMap φ) x ∈ (isAffineOpen_top (Sp R)).fromSpec ⁻¹ᵁ (Sp R).basicOpen s at h2
      rw [(isAffineOpen_top (Sp R)).fromSpec_preimage_basicOpen s] at h2
      exact h2
    letI : Algebra Γ(Sp R, ⊤) Γ(Sp R, Wa.1) := ((Sp R).presheaf.map (homOfLE hle).op).hom.toAlgebra
    have hl : IsLocalization.Away s Γ(Sp R, Wa.1) :=
      (isAffineOpen_top (Sp R)).isLocalization_of_eq_basicOpen s (homOfLE hle) rfl
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Γ(Sp R, Wa.1) →+* S, ψ.comp ((Sp R).presheaf.map (homOfLE hle).op).hom = φ :=
      ⟨IsLocalization.Away.lift s hu, IsLocalization.lift_comp _⟩
    subst hψ
    have hres : spMap ((Sp R).presheaf.map (homOfLE hle).op).hom ≫
        GlobalTheory.LogKS.chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) = GlobalTheory.LogKS.chart Wa :=
      (isAffineOpen_top (Sp R)).map_fromSpec Wa.2 (homOfLE hle).op
    have := htest i i' O hO f S ψ g₀ w ?_ hO' ?_
    · exact this
    · rw [hg₀, ← hres, ← Category.assoc, spMap_comp']
    · intro a
      obtain ⟨g', v'', h₁, h₂, h₃⟩ := hw a
      refine ⟨g', v'', h₁, ?_, h₃⟩
      rw [h₂]
      dsimp only
      rw [← Category.assoc, ← Category.assoc, spMap_comp']
      erw [spMap_comp']
      erw [dualMap_comp']

end GlobalTheory.KSChartRes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerAffineChartOfBasicOpenStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKodairaSpencer_affineChart_of_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (m : ℕ) (tt : Fin m → R) (n : ℕ) (v' : Fin n → TanM (𝟙 (Sp R)) t.G) (D : Derivation ℤ R R) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)) (Θ : Matrix (Fin n) (Fin n) R), (∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D r))) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV ((((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).mapMatrix Θ) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix Θ) := by
  first | exact @GlobalTheory.KSChartRes.isKS_top_of_basicOpen | exact GlobalTheory.KSChartRes.isKS_top_of_basicOpen | (intros; apply GlobalTheory.KSChartRes.isKS_top_of_basicOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerOfCommutingHeatOperatorsRaynaud
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KBracket

theorem exists_der_ext {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (M : Submonoid A) [IsLocalization M S]
    (δ : Derivation ℤ A A) : ∃ δS : Derivation ℤ S S, ∀ a, δS (algebraMap A S a) = algebraMap A S (δ a) := by
  let h : A →+* DualNumber S :=
    { toFun := fun a => TrivSqZeroExt.inl (algebraMap A S a) + TrivSqZeroExt.inr (algebraMap A S (δ a))
      map_one' := by ext <;> simp [-DualNumber.inr_eq_smul_eps]
      map_mul' := fun a b => by ext <;> simp [Derivation.leibniz, Algebra.smul_def, mul_comm, add_comm, -DualNumber.inr_eq_smul_eps]
      map_zero' := by ext <;> simp [-DualNumber.inr_eq_smul_eps]
      map_add' := fun a b => by ext <;> simp [add_add_add_comm, -DualNumber.inr_eq_smul_eps] }
  have hu : ∀ m : M, IsUnit (h m) := fun m => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
    simpa [h] using IsLocalization.map_units S m)
  let L : S →+* DualNumber S := IsLocalization.lift hu
  have hfst : ∀ x, (L x).fst = x := by
    have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp L = RingHom.id S := by
      refine IsLocalization.ringHom_ext M (RingHom.ext fun a => ?_)
      simp [L, h, -DualNumber.inr_eq_smul_eps]
    exact fun x => congr($this x)
  let δS : Derivation ℤ S S := Derivation.mk'
    ((show S →+ S from
      { toFun := fun x => (L x).snd, map_zero' := by simp, map_add' := fun x y => by simp }).toIntLinearMap)
    (fun x y => by
      show (L (x * y)).snd = x • (L y).snd + y • (L x).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
      simp [mul_comm])
  refine ⟨δS, fun a => ?_⟩
  show (L (algebraMap A S a)).snd = _
  simp [L, h, Algebra.smul_def, -DualNumber.inr_eq_smul_eps]

theorem exists_der_fun {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (M : Submonoid A) [IsLocalization M S]
    (δ : Derivation ℤ A A) : ∃ f : S →+ S, (∀ x y, f (x * y) = x * f y + y * f x) ∧
      ∀ a, f (algebraMap A S a) = algebraMap A S (δ a) := by
  obtain ⟨δS, hδS⟩ := exists_der_ext M δ (S := S)
  exact ⟨δS.toLinearMap.toAddMonoidHom, fun x y => by simp [Derivation.leibniz, smul_eq_mul], hδS⟩

theorem exists_der_frac (Ω : Type) [CommRing Ω] [IsDomain Ω] (δ : Derivation ℤ Ω Ω) :
    ∃ δS : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      ∀ ω, δS (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ ω) := by
  obtain ⟨f, hf1, hf2⟩ := exists_der_fun (nonZeroDivisors Ω) δ (S := FractionRing Ω)
  have hf0 : f 1 = 0 := by
    have h11 := hf1 1 1
    rw [_root_.mul_one, _root_.one_mul] at h11
    linear_combination -h11
  have hfc : ∀ (c : ℤ) (y : FractionRing Ω), f ((c : FractionRing Ω) * y) = (c : FractionRing Ω) * f y := by
    intro c y
    have h2 : f (c : FractionRing Ω) = 0 := by
      rw [← zsmul_one, map_zsmul, hf0]
      simp
    rw [hf1, h2]
    simp
  refine ⟨{ toFun := f
            map_add' := f.map_add
            map_smul' := (fun c y => ?_)
            map_one_eq_zero' := hf0
            leibniz' := (fun x y => ?_) }, hf2⟩
  · simp only [RingHom.id_apply]
    rw [Algebra.smul_def, eq_intCast, zsmul_eq_mul]
    exact hfc c y
  · exact hf1 x y

theorem isKS_of_heat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix h.Θ) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hab Y n vH dd hdd v' hv' D h hB hDef
  letI := H.starRing
  have hsm : Smooth Y.H.hom := GlobalTheory.RayTan.smooth_H R _ _ _ Y
  have hint : IsIntegral Y.H.left := GlobalTheory.T.isIntegral_raynaudExtension_noetherian_local R _ _ _ Y
  obtain ⟨i0, hi0⟩ : ∃ i0, ⊤ ≤ (η[Y.H]).left ⁻¹ᵁ h.W i0 := by
    have hm : (η[Y.H]).left (IsLocalRing.closedPoint R) ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i0, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    exact ⟨i0, (ReciprocityTheory.ChartRestriction.G.DVR.eq_top_of_closedPoint_mem ((η[Y.H]).left ⁻¹ᵁ h.W i0) hi).ge⟩
  obtain ⟨Ω, _, _, _, φ, x, δ, dΩ, hΩc, hx, hxW, hdΩ, hδφ, hδ, hd, hinj⟩ :=
    GlobalTheory.T.exists_formalPoint_origin_smoothCommGroupScheme R Y.H hsm hint n vH dd hdd ⇑D (h.W i0) (h.d i0) (h.lift i0) hi0
  set e := Scheme.ΓSpecIso (CommRingCat.of R) with he
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    have h1 : valR x ⊤ (Y.H.hom.appTop.hom (e.inv.hom r)) = φ r := by
      refine (GlobalTheory.ZH.EvCrd.valR_comp x Y.H.hom ⊤ (by simp) _).trans ?_
      rw [hx]
      exact GlobalTheory.ZH.EvCrd.valR_fn φ r
    have h2 := GlobalTheory.PrimScale.valR_const (η[Y.H]).left Y.H.hom (Over.w η[Y.H]) r
    have h3 := hinj ⊤ _ (by simp) (h1.trans hr)
    rw [h3] at h2
    rw [← h2]
    simp [valR]

  obtain ⟨x', hx', dd', hdd', hδ', hinj', hpt⟩ :=
    GlobalTheory.T.exists_uniformisedGroup_point_sameDerivations E H R t P m tt gam hmon htt hab Y n vH dd hdd v' hv' Ω φ x δ hΩc hφ hx hδφ hδ
  obtain ⟨g, hg⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := Ω) t.PP.L t.PP.isLB (K := PUnit)
    (fun _ => x' ≫ 𝟙 t.G.left) (fun _ => 1)
  have hex : ∀ a, ∃ δS : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      ∀ ω, δS (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ a ω) :=
    fun a => exists_der_frac Ω (δ a)
  choose δL hδL using hex
  obtain ⟨dt, u', p, p', hdt, hact⟩ := GlobalTheory.T.commuting_heatOperators_act_on_values E H R t P m tt gam hmon htt hab Y n vH dd hdd v' hv' D h hB hDef
    i0 Ω φ x x' δ hΩc hx hx' hδφ hδ hpt dΩ hxW hd g hg δL hδL
  obtain ⟨b, rfl⟩ := GlobalTheory.T.tangentBasis_uniformisedGroup_of_raynaudExtension E H R t P Y n vH v' hv'
  let D₀ : Derivation ℤ Γ(Sp R, ⊤) Γ(Sp R, ⊤) := Derivation.mk'
    ((e.inv.hom.toAddMonoidHom.comp ((D : R →ₗ[ℤ] R).toAddMonoidHom.comp e.hom.hom.toAddMonoidHom)).toIntLinearMap)
    (fun a a' => by
      simp [Derivation.leibniz, smul_eq_mul])
  haveI := (isAffineOpen_top (Sp R)).isLocalization_basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))
  obtain ⟨DV, hDV⟩ := exists_der_ext (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) D₀ (S := Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))))
  have hDV' : ∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom (e.inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom (e.inv.hom (D r)) := fun r => by
    show DV (algebraMap _ _ (e.inv.hom r)) = algebraMap _ _ (e.inv.hom (D r))
    rw [hDV]
    congr 1
    simp [D₀]

  obtain ⟨Θ₁, hsym, hKS⟩ := GlobalTheory.T.exists_symmetric_kodairaSpencer_abelianLocus E H R t P m tt gam hmon htt hab n b DV
  obtain ⟨iota, dt₂, u₂, p₂, p₂', hiota, hdt₂, hact₂⟩ := GlobalTheory.T.heatOperators_kodairaSpencer_formal_point_values E H R t P m tt gam hmon htt hab n b D Ω φ x' δ dd'
    hΩc hx' hdd' hδφ hδ' hinj' g hg δL hδL Θ₁ DV hDV' hKS
  have heq := GlobalTheory.T.heatOperator_symbol_unique_principalPolarisation E H R t P m tt gam hmon htt hab n b D Ω φ x' δ dd' hΩc hx' hdd' hδφ hδ' hinj' g hg δL hδL
    (((algebraMap Ω (FractionRing Ω)).comp φ).mapMatrix h.Θ) (iota.mapMatrix Θ₁) dt dt₂ u' u₂ p p' p₂ p₂'
    (by rw [RingHom.mapMatrix_apply, ← Matrix.transpose_map, h.symm])
    (by rw [RingHom.mapMatrix_apply, ← Matrix.transpose_map, hsym])
    (fun r => (hdt r).trans (hdt₂ r).symm) hact hact₂
  have hi : Function.Injective iota := by
    have key : ∀ y : Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))), iota y = 0 → y = 0 := by
      intro y hy
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))) (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) y
      dsimp only at hy ⊢
      have h1 : iota (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) a) = 0 := by
        rw [← IsLocalization.mk'_spec (S := Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))) a s]
        erw [map_mul, hy, zero_mul]
      have h2 : (algebraMap Γ(Sp R, ⊤) _ a : Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom (e.inv.hom (e.hom.hom a)) := by
        rw [Iso.hom_inv_id_apply]
        rfl
      rw [h2, hiota] at h1
      have h3 : φ (e.hom.hom a) = 0 := IsFractionRing.injective Ω (FractionRing Ω) (by rw [h1, map_zero])
      have h4 : e.hom.hom a = 0 := hφ (by rw [h3, map_zero])
      have h5 : a = 0 := by simpa using congrArg e.inv.hom h4
      rw [h5, IsLocalization.mk'_zero]
    exact (injective_iff_map_eq_zero iota).2 key
  have hΘ : Θ₁ = (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp e.inv.hom).mapMatrix h.Θ := by
    ext a a'
    apply hi
    have := congrFun (congrFun heq a) a'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.comp_apply] at this ⊢
    rw [← this, hiota]
  rw [hΘ] at hKS
  exact GlobalTheory.T.isKodairaSpencer_affineChart_of_basicOpen E H R t m tt n ⇑b D DV h.Θ hDV' hKS

end GlobalTheory.KBracket
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerOfCommutingHeatOperatorsRaynaudStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_of_commuting_heat_operators_raynaud : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix h.Θ) := by
  first | exact @GlobalTheory.KBracket.isKS_of_heat | exact GlobalTheory.KBracket.isKS_of_heat | (intros; apply GlobalTheory.KBracket.isKS_of_heat <;> assumption)
end
