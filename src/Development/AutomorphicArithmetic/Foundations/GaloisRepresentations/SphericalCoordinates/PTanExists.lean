module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTanExists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

private theorem exists_basis {B : Type} [CommRing B] [Algebra ℂ B] (d : ℕ) (a : Fin d → B)
    (he : (MvPolynomial.aeval a : MvPolynomial (Fin d) ℂ →ₐ[ℂ] B).toRingHom.Etale) :
    ∃ b : Module.Basis (Fin d) B Ω[B⁄ℂ], ∀ l, b l = KaehlerDifferential.D ℂ B (a l) := by
  letI : Algebra (MvPolynomial (Fin d) ℂ) B := (MvPolynomial.aeval a).toRingHom.toAlgebra
  haveI : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) B := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap ℂ B r = MvPolynomial.aeval a (MvPolynomial.C r)
    rw [MvPolynomial.aeval_C])
  haveI : Algebra.Etale (MvPolynomial (Fin d) ℂ) B := he
  let b0 := Algebra.TensorProduct.basis B (KaehlerDifferential.mvPolynomialBasis ℂ (Fin d))
  refine ⟨b0.map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ (MvPolynomial (Fin d) ℂ) B),
    fun l => ?_⟩
  rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply,
    ← KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, LinearEquiv.apply_symm_apply,
    show algebraMap (MvPolynomial (Fin d) ℂ) B (MvPolynomial.X l) = a l from MvPolynomial.aeval_X a l]

private theorem exists_phi {B : Type} [CommRing B] [Algebra ℂ B] (e : B →ₐ[ℂ] ℂ) (d : ℕ)
    (bs : Module.Basis (Fin d) B Ω[B⁄ℂ]) :
    ∃ φ : Ω[B⁄ℂ] →ₗ[ℂ] (Fin d → ℂ),
      (∀ (r : B) (ω : Ω[B⁄ℂ]), φ (r • ω) = e r • φ ω) ∧ (∀ l, φ (bs l) = Pi.single l 1) ∧
      ∀ ω : Ω[B⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → B) (ω' : Fin m → Ω[B⁄ℂ]),
        (∀ i, e (b i) = 0) ∧ ω = ∑ i, b i • ω' i := by
  let φ : Ω[B⁄ℂ] →ₗ[ℂ] (Fin d → ℂ) :=
    { toFun := fun ω l => e (bs.repr ω l)
      map_add' := by
        intro x y
        funext l
        simp
      map_smul' := by
        intro c x
        funext l
        rw [← algebraMap_smul B c x, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
          AlgHom.commutes]
        simp }
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro r ω
    funext l
    simp [φ]
  · intro l
    funext l'
    by_cases h : l' = l
    · subst h
      simp [φ]
    · simp [φ, Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]
  · intro ω hω
    refine ⟨d, fun l => bs.repr ω l, bs, ?_, (bs.sum_repr ω).symm⟩
    intro i
    simpa [φ] using congrFun hω i

end UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.tanExists_of :
    UpperTheory.Gal.W2.TanExists := by
  intro Z Y sZ s' d hsmooth c₁ c₂ h₁ h₂ hc₁ y hy
  haveI := hsmooth
  obtain ⟨U, x, hUaff, hzU, het⟩ := GlobalTheory.AlgChart.exists_etale_coords (p := sZ) (D := d)
    ((↑y ≫ c₁ : Sp ℂ ⟶ Z) (IsLocalRing.closedPoint ℂ))
  have hyU : ⊤ ≤ (↑y : Sp ℂ ⟶ Y) ⁻¹ᵁ (c₁ ⁻¹ᵁ U ⊓ c₂ ⁻¹ᵁ U) := by
    rw [GlobalTheory.Points.le_preimage_iff]
    have h2 := hzU
    rw [hy] at h2
    exact ⟨hzU, h2⟩
  obtain ⟨V, hVaff, hyV, hVle⟩ := GlobalTheory.Points.exists_isAffineOpen_le (↑y : Sp ℂ ⟶ Y) hyU
  have hV1 : V ≤ c₁ ⁻¹ᵁ U := hVle.trans inf_le_left
  have hV2 : V ≤ c₂ ⁻¹ᵁ U := hVle.trans inf_le_right
  have hg := HasRingHomProperty.appLE @Etale c₁ hc₁ ⟨U, hUaff⟩ ⟨V, hVaff⟩ hV1
  have hres : ∀ t, (c₁.appLE U V hV1).hom t = Sec.res s' hV1 (appSec sZ s' c₁ U t) := by
    intro t
    rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  have heq : (MvPolynomial.aeval (fun l => Sec.res s' hV1 (appSec sZ s' c₁ U (x l))) :
      MvPolynomial (Fin d) ℂ →ₐ[ℂ] Sec s' V).toRingHom =
      (c₁.appLE U V hV1).hom.comp (MvPolynomial.eval₂Hom (DVR.FlatBC.algX sZ U) x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h1 := semiHom_appSec h₁ U r 1
      simp only [Algebra.smul_def, _root_.mul_one, map_one, RingHom.id_apply] at h1
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
      have h4 : (MvPolynomial.eval₂Hom (DVR.FlatBC.algX sZ U) x) (MvPolynomial.C r) =
          DVR.FlatBC.algX sZ U r := MvPolynomial.eval₂Hom_C _ _ _
      refine Eq.trans ?_ ((congrArg (c₁.appLE U V hV1).hom h4).trans (hres _)).symm
      change algebraMap ℂ (Sec s' V) r = Sec.res s' hV1 (appSec sZ s' c₁ U (algebraMap ℂ (Sec sZ U) r))
      rw [h1, AlgHom.commutes]
    · intro i
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
      have h4 : (MvPolynomial.eval₂Hom (DVR.FlatBC.algX sZ U) x) (MvPolynomial.X i) = x i :=
        MvPolynomial.eval₂Hom_X' _ _ _
      exact ((congrArg (c₁.appLE U V hV1).hom h4).trans (hres (x i))).symm
  have het' : (MvPolynomial.aeval (fun l => Sec.res s' hV1 (appSec sZ s' c₁ U (x l))) :
      MvPolynomial (Fin d) ℂ →ₐ[ℂ] Sec s' V).toRingHom.Etale := by
    rw [heq]
    exact RingHom.Etale.stableUnderComposition _ _ het hg
  obtain ⟨bs, hbs⟩ := UpperTheory.Gal.W2.exists_basis d _ het'
  have hyV' : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V := hyV
  let e : Sec s' V →ₐ[ℂ] ℂ :=
    { toRingHom := CxPts.evHom hyV'
      commutes' := fun r => (CxPts.ev_eq hyV' _).symm.trans (CxPts.ev_algX hyV' r) }
  obtain ⟨φ, hsm, hbasis, hker⟩ := UpperTheory.Gal.W2.exists_phi e d bs
  refine ⟨fun j l => φ (KaehlerDifferential.D ℂ (Sec s' V) (Sec.res s' hV2 (appSec sZ s' c₂ U (x j)))) l,
    U, V, hV1, hV2, x, hyV', hUaff, hVaff, φ, ?_, ?_, ?_, ?_⟩
  · intro b ω
    rw [hsm]
    congr 1
    exact (CxPts.ev_eq hyV' b).symm
  · intro l
    have h3 := hbasis l
    rw [hbs l] at h3
    exact h3
  · intro j
    rfl
  · intro ω hω
    obtain ⟨m, b, ω', hb, hsum⟩ := hker ω hω
    exact ⟨m, b, ω', fun i => (CxPts.ev_eq hyV' (b i)).trans (hb i), hsum⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPbFlat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem fderiv_line {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (F : V → ℂ) (v₀ w : V)
    (hF : DifferentiableAt ℂ F v₀) :
    DifferentiableAt ℂ (fun z : Fin 1 → ℂ => F (v₀ + z 0 • w)) 0 ∧
      fderiv ℂ (fun z : Fin 1 → ℂ => F (v₀ + z 0 • w)) 0 (fun _ => 1) = fderiv ℂ F v₀ w := by
  have hℓ : HasFDerivAt (fun z : Fin 1 → ℂ => v₀ + z 0 • w)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight w) 0 := by
    have h1 : HasFDerivAt (fun z : Fin 1 → ℂ => z 0 • w)
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight w) 0 :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight w).hasFDerivAt
    exact h1.const_add v₀
  have hF' : HasFDerivAt F (fderiv ℂ F v₀) ((fun z : Fin 1 → ℂ => v₀ + z 0 • w) 0) := by
    simpa using hF.hasFDerivAt
  have hc : HasFDerivAt (fun z : Fin 1 → ℂ => F (v₀ + z 0 • w))
      ((fderiv ℂ F v₀).comp ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight w)) 0 :=
    hF'.comp (0 : Fin 1 → ℂ) hℓ
  refine ⟨hc.differentiableAt, ?_⟩
  rw [hc.fderiv]
  simp

private theorem exists_isDerivAt0_line_of_isHolTo {X : Scheme.{0}} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} {t : V → (Sp ℂ ⟶ X)} (ht : IsHolTo B t) {v₀ : V} (hv : v₀ ∈ B) (w : V) :
    ∃ x, IsDerivAt0 (fun z : Fin 1 → ℂ => t (v₀ + z 0 • w)) (fun _ => 1) x := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ((t v₀) default)) isOpen_univ
  have hW0 : ⊤ ≤ t v₀ ⁻¹ᵁ W := by
    rw [top_le_preimage_iff_mem]
    have hd : (@default (PrimeSpectrum ℂ) _) = (@default (↥(Sp ℂ)) _) := Subsingleton.elim _ _
    rw [hd]
    exact hxW
  have hℓc : Continuous (fun z : Fin 1 → ℂ => v₀ + z 0 • w) := by
    fun_prop
  have hℓ0 : (fun z : Fin 1 → ℂ => v₀ + z 0 • w) 0 = v₀ := by
    simp
  have hev : ∀ᶠ z in 𝓝 (0 : Fin 1 → ℂ), ⊤ ≤ t (v₀ + z 0 • w) ⁻¹ᵁ W := by
    have h1 := LocalLift.hol_eventually_mem ht hv hW0
    have h2 : Tendsto (fun z : Fin 1 → ℂ => v₀ + z 0 • w) (𝓝 0) (𝓝 v₀) := by
      have := hℓc.tendsto 0
      simpa using this
    exact (h2.eventually h1).mono (fun z hz => hz.2)
  have hdiff : ∀ a : Γ(X, W), DifferentiableAt ℂ (fun z : Fin 1 → ℂ => valAt' (t (v₀ + z 0 • w)) W a) 0 :=
    fun a => (fderiv_line (fun v => valAt' (t v) W a) v₀ w
      (LocalLift.hol_differentiableAt ht hv hW0 a)).1
  let ψ : Γ(X, W) →+* DualNumber ℂ :=
    { toFun := fun a => FibreDeriv.jet (fun _ => 1) (fun z : Fin 1 → ℂ => valAt' (t (v₀ + z 0 • w)) W a)
      map_one' := by
        have hc : (fun z : Fin 1 → ℂ => valAt' (t (v₀ + z 0 • w)) W 1) =ᶠ[𝓝 0] (fun _ => (1 : ℂ)) :=
          hev.mono (fun z hz => valAt'_one _ hz)
        rw [FibreDeriv.jet_congr _ hc, FibreDeriv.jet_const]
        simp
      map_mul' := by
        intro a b
        simp only [valAt'_mul]
        exact FibreDeriv.jet_mul _ (hdiff a) (hdiff b)
      map_zero' := by
        simp only [valAt'_zero]
        rw [FibreDeriv.jet_const]
        simp
      map_add' := by
        intro a b
        simp only [valAt'_add]
        exact FibreDeriv.jet_add _ (hdiff a) (hdiff b) }
  obtain ⟨x, hx, hxψ⟩ := TangentOrigin.exists_evalPt_eq hW ψ
  refine ⟨x, FibreDeriv.isDerivAt0_of_affine ?_ hW hx (fun a => ⟨hdiff a, ?_⟩)⟩
  · have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ x) ⁻¹ᵁ W :=
      (TangentOrigin.top_le_preimage_iff x W).mp hx
    have h0 : ⊤ ≤ t (v₀ + (0 : Fin 1 → ℂ) 0 • w) ⁻¹ᵁ W := by
      simpa using hW0
    refine TangentOrigin.ext_evalPt hW h' h0 (RingHom.ext (fun a => ?_))
    rw [TangentOrigin.evalPt_spMap_comp _ x W hx h' a, hxψ, ← TangentOrigin.valAt'_eq_evalPt]
    exact FibreDeriv.fst_jet (fun _ => 1) (fun z : Fin 1 → ℂ => valAt' (t (v₀ + z 0 • w)) W a)
  · show TangentOrigin.evalPt x W hx a = _
    rw [hxψ]
    rfl

private theorem isDerivAt0_line_const_of_flat {X : Scheme.{0}} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} {t : V → (Sp ℂ ⟶ X)} (ht : IsHolTo B t) {v₀ : V} (hv : v₀ ∈ B) (w : V)
    (hf : Flat t v₀ w) :
    IsDerivAt0 (fun z : Fin 1 → ℂ => t (v₀ + z 0 • w)) (fun _ => 1)
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ t v₀) := by
  have h := LocalLift.isDerivAt0_const (fun z : Fin 1 → ℂ => t (v₀ + z 0 • w)) (fun _ => 1)
    (fun U f hU => by
      have hU' : ⊤ ≤ t v₀ ⁻¹ᵁ U := by
        simpa using hU
      rw [(fderiv_line (fun v => valAt' (t v) U f) v₀ w
        (LocalLift.hol_differentiableAt ht hv hU' f)).2]
      exact hf U f hU')
  simpa using h

private theorem flat_of_isDerivAt0_line_const {X : Scheme.{0}} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} {t : V → (Sp ℂ ⟶ X)} (ht : IsHolTo B t) {v₀ : V} (hv : v₀ ∈ B) (w : V)
    (hd : IsDerivAt0 (fun z : Fin 1 → ℂ => t (v₀ + z 0 • w)) (fun _ => 1)
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ t v₀)) :
    Flat t v₀ w := by
  intro U f hU
  rw [← (fderiv_line (fun v => valAt' (t v) U f) v₀ w
    (LocalLift.hol_differentiableAt ht hv hU f)).2]
  have hc : IsDerivAt0 (fun _ : Fin 1 → ℂ => t v₀) (fun _ => 1)
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ t v₀) :=
    LocalLift.isDerivAt0_const (fun _ : Fin 1 → ℂ => t v₀) (fun _ => 1)
      (fun U' f' _ => by simp)
  have h : ⊤ ≤ (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ t v₀) ⁻¹ᵁ U := by
    rw [TangentOrigin.top_le_preimage_iff, hc.1]
    exact hU
  rw [← hd.2 U h f, hc.2 U h f]
  simp

theorem UpperTheory.Gal.W2.pbFlat_of :
    UpperTheory.Gal.W2.FlatAffine → UpperTheory.Gal.W2.PbFlat := by
  intro hFA V _ _ P Y₁ Y₂ T p₁ p₂ f₁ f₂ hpb B s v₀ w hB hv h1 h2 hf1 hf2
  have hs : IsHolTo B s :=
    HolPullback.isHolTo_of_components V B Y₁ P T Y₂ p₁ p₂ f₁ f₂ s hpb hB h1 h2
  obtain ⟨x, hx⟩ := exists_isDerivAt0_line_of_isHolTo hs hv w
  have hc1 := isDerivAt0_line_const_of_flat h1 hv w hf1
  have hc2 := isDerivAt0_line_const_of_flat h2 hv w hf2
  have hx1 := FibreDeriv.isDerivAt0_comp hx p₁
  have hx2 := FibreDeriv.isDerivAt0_comp hx p₂
  have he1 : x ≫ p₁ = (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ s v₀) ≫ p₁ := by
    rw [Category.assoc]
    exact VerticalDeriv.isDerivAt0_unique hx1 hc1
  have he2 : x ≫ p₂ = (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ s v₀) ≫ p₂ := by
    rw [Category.assoc]
    exact VerticalDeriv.isDerivAt0_unique hx2 hc2
  have hxe : x = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ s v₀ := hpb.hom_ext he1 he2
  rw [hxe] at hx
  exact flat_of_isDerivAt0_line_const hs hv w hx
end
