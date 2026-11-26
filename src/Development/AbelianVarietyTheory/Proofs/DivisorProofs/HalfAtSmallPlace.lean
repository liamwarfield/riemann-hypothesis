module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupremumConstantLogBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentPhiLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfAtSmallPlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HalfLabels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

theorem cjE_cjE (φ : E →+* Formalism.ConjugateSelfDual.Qbar l) : ExpFrame.cj (cj φ) = φ := by
  ext x
  simp only [ExpFrame.cj, RingHom.comp_apply]
  exact congrArg φ (IsCMField.complexConj_apply_apply E x)

theorem isHalf_cj {ι : Type} {inc : ι → (E →+* Formalism.ConjugateSelfDual.Qbar l)} (h : IsHalf inc) : IsHalf fun τ => ExpFrame.cj (inc τ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a b hab => h1 ?_, fun τ τ' e => h2 τ' τ ?_, fun i => ?_⟩
  · have := congrArg ExpFrame.cj hab
    simpa only [cjE_cjE] using this
  · simp only [cjE_cjE] at e
    exact e.symm
  · obtain ⟨τ, hτ | hτ⟩ := h3 i
    · exact ⟨τ, Or.inr (by rw [cjE_cjE]; exact hτ)⟩
    · exact ⟨τ, Or.inl hτ⟩

end GlobalTheory.HalfLabels

namespace GlobalTheory.HalfLabels

theorem exists_aut {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [CharZero K] (ι i : E →+* K) :
    ∃ σ : E ≃ₐ[ℚ] E, i = ι.comp (σ : E →+* E) := by
  let _ : Algebra E K := ι.toAlgebra
  have : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ K), eq_ratCast (algebraMap ℚ E), map_ratCast]
  let φ : E →ₐ[ℚ] K := i.toRatAlgHom
  refine ⟨AlgEquiv.ofBijective (φ.restrictNormal E) (AlgHom.normal_bijective ℚ E E _), ?_⟩
  ext x
  have h := AlgHom.restrictNormal_commutes φ E x
  exact h.symm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isHalf_lab (D : D7) {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) : IsHalf (incOf D e0 false) := by
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  set ι : D.host.E →+* PadicAlgCl l := e0.comp D.embE with hι
  have hinc : ∀ τ, incOf D e0 false τ = ι.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E) := fun τ => rfl
  have hcc : ∀ g, ExpFrame.cj (ι.comp (D.host.sigmaOf g : D.host.E →+* D.host.E)) =
      ι.comp (D.host.sigmaOf (g * D.R.cc) : D.host.E →+* D.host.E) := by
    intro g
    have hs : D.host.sigmaOf (g * D.R.cc) = D.host.sigmaOf g * D.host.conj :=
      map_mul (D.host.gal).symm g (D.R.cc)
    ext x
    rw [hs]
    show ι (D.host.sigmaOf g (IsCMField.complexConj D.host.E x)) = ι (D.host.sigmaOf g (D.host.conj x))
    congr 2
    exact Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hinj : ∀ g g', ι.comp (D.host.sigmaOf g : D.host.E →+* D.host.E) = ι.comp (D.host.sigmaOf g' : D.host.E →+* D.host.E) →
      g = g' := by
    intro g g' h
    have : D.host.sigmaOf g = D.host.sigmaOf g' := AlgEquiv.ext fun x => ι.injective (RingHom.congr_fun h x)
    exact (D.host.gal).symm.injective this
  refine ⟨fun τ τ' h => ?_, fun τ τ' h => ?_, fun i => ?_⟩
  · rw [hinc, hinc] at h
    exact D.eTau.injective (Subtype.ext (hinj _ _ h))
  · rw [hinc, hinc, hcc] at h
    have e := hinj _ _ h
    exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau τ).2 (e ▸ (D.eTau τ').2)
  · obtain ⟨σ, hσ⟩ := exists_aut ι i
    have hσg : D.host.sigmaOf (D.host.gal σ) = σ :=
      (D.host.gal).symm_apply_apply σ
    by_cases hg : D.host.gal σ ∈ D.R.Psi
    · refine ⟨D.eTau.symm ⟨_, hg⟩, Or.inl ?_⟩
      rw [hinc, Equiv.apply_symm_apply, hσ, hσg]
    · have hg' : D.host.gal σ * D.R.cc ∈ D.R.Psi := by
        by_contra h'
        exact hg ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h')
      refine ⟨D.eTau.symm ⟨_, hg'⟩, Or.inr ?_⟩
      rw [hinc, Equiv.apply_symm_apply, ← hcc, cjE_cjE, hσ, hσg]

theorem halfAt_all (D : D7) (l : ℕ) : HalfAt D l := by
  intro _ e0 b
  cases b
  · exact isHalf_lab D (l := l) e0
  · exact isHalf_cj (isHalf_lab D e0)

end GlobalTheory.HalfLabels

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeCommRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeCommRing
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRham

open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham


set_option maxHeartbeats 1000000 in
theorem IsKSValue.exists_of_isAbelianScheme_ring (P : AbelianDeRham) {K : Type} [CommRing K] {A : Over (Sp K)} [GrpObj A]
    {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (epsRed K) i) {g : ℕ} (hA : Semi.IsAbelianScheme A')
    (hg : SmoothOfRelativeDimension g A'.hom) {f : HdR A} (hf : f ∈ Fil A) : ∃ v, IsKSValue h f v := by
  have a₀ : Semi.IsAbelianScheme A := by
    have := hA.comm
    open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in
    have hc : IsCommMonObj A := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected⟩
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  have hL := (P.2.1 K A g a₀ g₀).1
  letI : Algebra (DualNumber K) K := (TrivSqZeroExt.fstHom K K K).toRingHom.toAlgebra
  obtain ⟨-, hF⟩ := P.2.2.1 (DualNumber K) A' g hA hg K A i h
  obtain ⟨-, ⟨N, hN⟩, -⟩ := P.2.1 (DualNumber K) A' g hA hg
  obtain ⟨-, hproj, -⟩ := P.1.prim hA hg
  have su : Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom :=
    fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have rA := P.2.2.2.1 _ A' g hA hg _ (epsDP K) (isDPNilpotent_squareZero _) K _ su rfl A i h
  have rB := P.2.2.2.1.crysToDR_bijective hA hg (κ := epsDP K) (isDPNilpotent_squareZero _) su rfl h
  let φL : primDR A' →ₗ[DualNumber K] K :=
    { toFun := fun c => f ((bcMor h).pull c)
      map_add' := fun x y => by simp only [map_add (f := _)]
      map_smul' := fun r c => by
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  obtain ⟨u, hu⟩ := Module.projective_lifting_property (Algebra.linearMap (DualNumber K) K) φL
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩)
  let d' : HdR A' := u ∘ₗ N.projection (PrimitiveSubmodule A') hN.symm
  have hd' : d' ∈ Fil A' := by
    rw [Fil, Submodule.mem_dualAnnihilator]
    intro x hx
    change u (N.projection (PrimitiveSubmodule A') hN.symm x) = 0
    rw [Submodule.projection_apply_of_mem_right hN.symm hx, map_zero]
  have fd' : ∀ x, (d' x).fst = f ((bcMor h).pull x) := fun x => by
    have e1 : ∀ y, (u y).fst = f ((bcMor h).pull y) := fun y => LinearMap.congr_fun hu y
    have e2 := Submodule.projection_add_projection_eq_self hN.symm x
    have e3 : f ((bcMor h).pull ((PrimitiveSubmodule A').projection N hN.symm.symm x)) = 0 := by
      rw [Fil, hF] at hf
      exact (Submodule.mem_dualAnnihilator _).1 hf _
        (Submodule.subset_span ⟨_, Submodule.projection_apply_mem _ _, rfl⟩)
    change (u _).fst = _
    rw [e1, ← add_zero (f ((bcMor h).pull _)), ← e3, ← map_add (f := _), ← map_add (f := _), e2]
  obtain ⟨d, hd⟩ := rB.2 d'
  let k : HdR A :=
    { toFun := fun c => (d ((constMor A).pull c)).snd
      map_add' := fun x y => by simp only [map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' := fun r c => by
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul,
          TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_mul]
        simp }
  obtain ⟨v, hv, -⟩ := hL.1 k
  refine ⟨v, k, ⟨d, by rw [liftFil, Submodule.mem_comap, hd]; exact hd', fun c => ?_⟩, hv⟩
  obtain ⟨x, hx⟩ := rA.2 ((constMor A).pull c)
  have red : (bcMor h).pull x = c := by
    rw [← GrpMor.pull_pull (liftMor (epsDP K) h) (redMor A) (bcMor h) (fun _ => rfl) (by simp) x, hx,
      redMor_constMor]
  apply TrivSqZeroExt.ext
  · have e := fd' x
    rw [← hd, crysToDR_apply, hx, red] at e
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    exact e
  · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rfl

theorem ksRegular_of_isAbelianScheme_ring : GlobalTheory.Published.AbelianDeRham → ∀ {K : Type} [CommRing K] {A : Over (Sp K)}
    [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {g : ℕ}, Semi.IsAbelianScheme A' →
    SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  intro P K _ A _ A' _ i h g hA hg f hf
  obtain ⟨v, hv⟩ := IsKSValue.exists_of_isAbelianScheme_ring P h hA hg hf
  exact ⟨v, hv, fun w hw => IsKSValue.unique P hA hg hw hv⟩

end GlobalTheory.DeRham
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeCommRingStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_commRing : GlobalTheory.Published.AbelianDeRham → ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {g : ℕ}, Semi.IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  first | exact @GlobalTheory.DeRham.ksRegular_of_isAbelianScheme_ring | exact GlobalTheory.DeRham.ksRegular_of_isAbelianScheme_ring | (intros; apply GlobalTheory.DeRham.ksRegular_of_isAbelianScheme_ring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSmulIdemOfBdd
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatLine

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.L2.Pj GlobalTheory.AllWt

theorem isAlgebraic_of_norm_bdd {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Algebra K ℂ]
    (P₀ : Ω →ₐ[K] ℂ) {b : Ω} {C : ℝ} (h : ∀ P : Ω →ₐ[K] ℂ, ‖P b‖ ≤ C) : IsAlgebraic K b := by
  by_contra hb
  have hb0 : P₀ b ≠ 0 := fun h0 => hb ((map_eq_zero P₀).1 h0 ▸ isAlgebraic_zero)
  have hpos : 0 < ‖P₀ b‖ := norm_pos_iff.2 hb0
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ‖P₀ b‖)
  have hN0 : (N : K) ≠ 0 := by
    have : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (le_trans (norm_nonneg _) (h P₀)) hpos.le) hN
    exact_mod_cast (Nat.cast_pos.1 this).ne'
  have hi : AlgebraicIndepOn K id ({b} : Set Ω) := algebraicIndependent_unique_type_iff.2 hb
  obtain ⟨T, hT, hbas⟩ := exists_isTranscendenceBasis_superset hi
  have hw : AlgebraicIndependent K fun i : T => P₀ i := hbas.1.map' P₀.injective
  have hw2 : AlgebraicIndependent K fun i : T => Polynomial.aeval (P₀ i) (Polynomial.C (N : K) * Polynomial.X) :=
    hw.polynomial_aeval_of_transcendental fun _ => Polynomial.transcendental _
      (by rw [Polynomial.natDegree_C_mul_X _ hN0]; exact one_ne_zero)
      (by rw [Polynomial.leadingCoeff_C_mul_X]; exact mem_nonZeroDivisors_of_ne_zero hN0)
  letI : Algebra (MvPolynomial T K) Ω := (MvPolynomial.aeval fun i : T => (i : Ω)).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial T K) ℂ := (MvPolynomial.aeval fun i : T =>
    Polynomial.aeval (P₀ i) (Polynomial.C (N : K) * Polynomial.X)).toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial T K) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hbas.1
  haveI : FaithfulSMul (MvPolynomial T K) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hw2
  haveI : Algebra.IsAlgebraic (MvPolynomial T K) Ω :=
    haveI := hbas.isAlgebraic
    ⟨fun y => (IsAlgebraic.ringHom_of_comp_eq (f := hbas.1.aevalEquiv.symm.toRingHom) (g := RingHom.id Ω)
      (Algebra.IsAlgebraic.isAlgebraic y) hbas.1.aevalEquiv.symm.injective (RingHom.ext fun z => by
        obtain ⟨p, rfl⟩ := hbas.1.aevalEquiv.surjective z
        simp [RingHom.algebraMap_toAlgebra]))⟩
  let Q : Ω →ₐ[MvPolynomial T K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let P : Ω →ₐ[K] ℂ := { Q.toRingHom with
    commutes' := fun a => by
      have := Q.commutes (MvPolynomial.C a)
      simpa [RingHom.algebraMap_toAlgebra] using this }
  have h1 : P b = (N : ℂ) * P₀ b := by
    show Q b = _
    have := Q.commutes (MvPolynomial.X ⟨b, hT rfl⟩)
    simpa [RingHom.algebraMap_toAlgebra, map_natCast] using this
  have h2 := h P
  rw [h1, norm_mul, Complex.norm_natCast] at h2
  have h3 : C < N * ‖P₀ b‖ := (div_lt_iff₀ hpos).1 hN
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem exists_eq_smul_idem_of_bdd {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hF : FnAlgClosed (Xo := Xo) (c := c)) {Z : Comp Xo c} {g : Rul Xo c} (hg : g ∈ secZ Xo c 0) (hs : g ∈ suppOn Z) {C : ℝ}
    (hb : ∀ z ∈ framesOn U Z, ‖rdU U g z.1 z.2‖ ≤ C) : ∃ a : c.F, g = a • idem Z := by
  obtain ⟨hL, -, h, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨⟨P₀⟩, hP⟩ := GlobalTheory.GenericReading.embedding_read_at_frame E H Dw l Xo c σ r U hσ hU h Z
  have hi := idem_mem_secZ Z
  rw [secZ_zero_eq] at hg hi
  have key : ∀ P : Om Z →ₐ[c.F] CAt σ, ‖toC (P (evC h Z g))‖ ≤ C := fun P => by
    obtain ⟨k, x, y', t, hm, ht⟩ := hP P
    obtain ⟨w, -, hw⟩ := GlobalTheory.CompBij.rdU_eq_of_reads U h k Z x P y' t hm ht 0 0
    have hz : (⟨k, x.1⟩ : Σ k, Frame (U.X k).Ψ r) ∈ framesOn U Z :=
      ⟨x.2, liesOn_frBor ht (liesOn_frMap hm (liesOn_genFr h Z))⟩
    have h1 := hw _ hi
    have h2 : rdU U (idem Z) k x = 1 := by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, x.2, dif_pos]
      exact evR_idem (S := CAt σ) hz.2 (haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ); hL.test _ _)
    have h3 : evC h Z (idem Z) = 1 := evR_idem (liesOn_genFr h Z) (hL.test _ _)
    rw [h2, h3, map_one, mul_one] at h1
    rw [← hw g hg, h1]
    exact (congrArg norm (one_mul _)).trans_le (hb _ hz)
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨a, ha⟩ := hF Z _ (isAlgebraic_of_norm_bdd (K := c.F) (b := evC h Z g) P₀ fun P => key P)
  refine ⟨a, sub_eq_zero.1 (GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _
    (sub_mem hg (Submodule.smul_mem _ _ hi)) fun Z' => ?_)⟩
  by_cases hZ : Z' = Z
  · subst hZ
    have h3 : evC h Z' (idem Z') = 1 := evR_idem (liesOn_genFr h Z') (hL.test _ _)
    have h4 := evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) g ((-a) • idem Z')
      (genFr h Z')
    have h5 := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (-a) (idem Z')
      (genFr h Z')
    rw [sub_eq_add_neg, ← neg_smul]
    refine h4.trans ?_
    rw [h5]
    show evC h Z' g + algebraMap _ _ (-a) * evC h Z' (idem Z') = 0
    rw [h3, ← ha, map_neg, mul_one, add_neg_cancel]
  · exact evC_eq_zero h hZ (sub_mem hs (Submodule.smul_mem _ _ (idem_mem_suppOn Z)))

end GlobalTheory.FlatLine

namespace GlobalTheory.CovTop

end GlobalTheory.CovTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScal
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.ScalApprox

variable {K : Type} [Field K] [NumberField K]

theorem mem_pow_iff (w : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) (n : ℕ) :
    r ∈ w.asIdeal ^ n ↔ (n : ℤ) ≤ vAdd w (r : K) := by
  have h0 : w.intValuation r ≠ 0 := w.intValuation_ne_zero r hr
  rw [← w.intValuation_le_pow_iff_mem, vAdd, HeightOneSpectrum.valuation_of_algebraMap]
  conv_lhs => rw [← WithZero.exp_log h0]
  rw [WithZero.exp_le_exp]
  omega

theorem vAdd_div (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x / y) = vAdd w x - vAdd w y := by
  have hx' : w.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : w.valuation K y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [vAdd, vAdd, vAdd, map_div₀, WithZero.log_div hx' hy']
  ring

end GlobalTheory.RefSum.ScalApprox

namespace GlobalTheory.RefSum.ScalApprox

variable {K : Type} [Field K] [NumberField K]

theorem exists_scal : ∀ (K : Type) [Field K] [NumberField K] (ρ : HeightOneSpectrum (𝓞 K) → ℝ),
    (Function.support ρ).Finite → ∀ w : HeightOneSpectrum (𝓞 K), ∃ a : K, a ≠ 0 ∧
      (vAdd w a : ℝ) = -(⌊ρ w⌋ : ℝ) ∧ ∀ w', 0 ≤ (vAdd w' a : ℝ) + ρ w' := by
  intro K _ _ ρ hρ w
  classical
  set S : Finset (HeightOneSpectrum (𝓞 K)) := insert w hρ.toFinset with hS

  have hne : ∀ v : HeightOneSpectrum (𝓞 K), ∃ e : 𝓞 K, e ∈ v.asIdeal ∧ e ≠ 0 := fun v =>
    Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  choose e he he0 using hne
  set N : ℕ := ∑ v ∈ S, (⌊ρ v⌋).toNat with hN
  set c : 𝓞 K := (∏ v ∈ S, e v) ^ N with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun v _ => he0 v)
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc0
  have hcS : ∀ v ∈ S, -⌊ρ v⌋ + vAdd v (c : K) ≥ 0 := by
    intro v hv
    have h1 : ∏ u ∈ S, e u ∈ v.asIdeal := by
      obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem e hv
      rw [ht]; exact Ideal.mul_mem_right _ _ (he v)
    have h2 : c ∈ v.asIdeal ^ N := Ideal.pow_mem_pow h1 N
    have h3 := (mem_pow_iff v hc0 N).1 h2
    have h4 : (⌊ρ v⌋).toNat ≤ N := Finset.single_le_sum (f := fun u => (⌊ρ u⌋).toNat)
      (fun _ _ => Nat.zero_le _) hv
    have h5 : ⌊ρ v⌋ ≤ ((⌊ρ v⌋).toNat : ℤ) := Int.self_le_toNat _
    omega
  have hfc := GlobalTheory.FlatLine.finite_vAdd hcK
  set T : Finset (HeightOneSpectrum (𝓞 K)) := S ∪ hfc.toFinset with hT
  set E : HeightOneSpectrum (𝓞 K) → ℕ := fun v => (-⌊ρ v⌋ + vAdd v (c : K)).toNat with hE
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have hπpow : ∀ n : ℕ, w.intValuation (π ^ n) = WithZero.exp (-(n : ℤ)) := fun n => by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; congr 1; simp
  have hwT : w ∈ T := Finset.mem_union_left _ (Finset.mem_insert_self _ _)
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v => v.asIdeal) (fun v => if v = w then E w + 1 else E v)
    (fun v _ => v.prime) (fun v _ u _ h h' => h (HeightOneSpectrum.ext h'))
    (fun v => if (v : HeightOneSpectrum (𝓞 K)) = w then π ^ E w else 0)
  have hbw := hb w hwT
  simp only [if_true] at hbw
  have hπE : π ^ E w ∈ w.asIdeal ^ E w := (w.intValuation_le_pow_iff_mem _ _).1 (le_of_eq (hπpow _))
  have hπE1 : π ^ E w ∉ w.asIdeal ^ (E w + 1) := by
    rw [← w.intValuation_le_pow_iff_mem, hπpow, WithZero.exp_le_exp]
    push_cast; omega
  have hbw1 : b ∈ w.asIdeal ^ E w := by
    have := Ideal.pow_le_pow_right (I := w.asIdeal) (Nat.le_succ (E w)) hbw
    simpa using add_mem this hπE
  have hbw2 : b ∉ w.asIdeal ^ (E w + 1) := fun h => hπE1 (by simpa using sub_mem h hbw)
  have hb0 : b ≠ 0 := by rintro rfl; exact hbw2 (Submodule.zero_mem _)
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb0
  have hvw : vAdd w (b : K) = E w := by
    have h1 := (mem_pow_iff w hb0 _).1 hbw1
    have h2 := mt (mem_pow_iff w hb0 (E w + 1)).2 hbw2
    push_cast at h2; omega
  have hball : ∀ v, (E v : ℤ) ≤ vAdd v (b : K) := by
    intro v
    by_cases hv : v ∈ T
    · by_cases hvw' : v = w
      · subst hvw'; rw [hvw]
      · have := hb v hv
        simp only [hvw', if_false, sub_zero] at this
        exact (mem_pow_iff v hb0 _).1 this
    · have hvS : v ∉ S := fun h => hv (Finset.mem_union_left _ h)
      have hρv : ρ v = 0 := by
        by_contra h; exact hvS (Finset.mem_insert_of_mem (hρ.mem_toFinset.2 h))
      have hcv : vAdd v (c : K) = 0 := by
        by_contra h
        exact hv (Finset.mem_union_right _ (hfc.mem_toFinset.2 (by simpa using h)))
      have : E v = 0 := by simp [hE, hρv, hcv]
      rw [this]; exact (mem_pow_iff v hb0 0).1 (by simp)
  refine ⟨(b : K) / c, div_ne_zero hbK hcK, ?_, fun v => ?_⟩
  · rw [vAdd_div w hbK hcK, hvw]
    have := hcS w (Finset.mem_insert_self _ _)
    have h6 : ((E w : ℕ) : ℤ) = -⌊ρ w⌋ + vAdd w (c : K) := Int.toNat_of_nonneg this
    rw [h6]; push_cast; ring
  · rw [vAdd_div v hbK hcK]
    have h1 := hball v
    have h2 : -⌊ρ v⌋ + vAdd v (c : K) ≤ ((E v : ℕ) : ℤ) := Int.self_le_toNat _
    have h3 : -⌊ρ v⌋ ≤ vAdd v (b : K) - vAdd v (c : K) := by omega
    have h4 : (⌊ρ v⌋ : ℝ) ≤ ρ v := Int.floor_le _
    have h5 : ((-⌊ρ v⌋ : ℤ) : ℝ) ≤ ((vAdd v (b : K) - vAdd v (c : K) : ℤ) : ℝ) := by exact_mod_cast h3
    push_cast at h5 ⊢
    linarith

end GlobalTheory.RefSum.ScalApprox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGeometryWeightBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGeometryWeightBound
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.BergComp

open MeasureTheory

theorem bergOn_le_supConst : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E), Even G.2 → ∀ (w : ℝ), 0 < w → (∀ k, (∑ τ, ((U σ).X k).spread (AllWt.modelWt (U σ) G k) τ) ≤ w) → ∀ (Z : Comp Xo c) (y : FPt (U σ).X), (⟨y.1, y.2.1⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r) ∈ AllWt.framesOn (U σ) Z → AllWt.bergOn (U σ) (D.sp.W j) (dict σ) Z G y ≤ ENNReal.ofReal (GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d l.M w) := by
  intro hT D j H Dw l Xo c U dict hL σ hσ G hG w hw hsp Z y hy
  classical
  have hU : IsUnf (U σ) := hL.unf σ hσ
  obtain ⟨Kf, th, hr, -, -, hDU, -⟩ := hL.dictU σ hσ
  have hdom : ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom := Formalism.L2.Pj.dict_dom_of hDU
  set A := AllWt.framesOn (U σ) Z with hA
  set S : Set (U σ).Comp := {k | ∃ f, (⟨k, f⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r) ∈ A} with hS
  have key : ∀ g, dict σ g ∈ A ↔ (dict σ g).1 ∈ S := fun g =>
    ⟨fun h => ⟨_, h⟩, fun ⟨f, hf⟩ =>
      GlobalTheory.FramesUnion.framesOn_of_mem D.host.E H Dw l Xo c D.R.r U σ hU Z _ f _ (hdom g) hf⟩
  set la := AllWt.modelWt (U σ) G with hla
  have hchi := GlobalTheory.AllWt.Model.chi_modelWt (U σ) (hL.chiTriv σ hσ) G hG
  set Cl := AllWt.classesOver (D.sp.W j) (dict σ) A with hCl
  have hyS : y.1 ∈ S := ⟨y.2.1, hy⟩
  unfold AllWt.bergOn AllWt.bergE
  refine iSup₂_le fun P hP => ?_
  set P' : Formalism.L2.Pj.FDSec (U σ).X := fun k => if k ∈ S then P k else 0 with hP'
  have hP'm : P' ∈ Formalism.L2.Pj.holSub (U σ).X la := by
    refine Formalism.L2.Pj.holCusp_mem_holSub _ _ fun k => ?_
    by_cases hk : k ∈ S
    · simp only [hP', if_pos hk]
      exact Formalism.L2.Pj.holSub_comp_SS _ _ _ hP k
    · simp only [hP', if_neg hk]
      exact (ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds (E := D.host.E) D.R.r ((U σ).X k) (la k) (la k) 0).1.1
  have hpt : ∀ z : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r,
      AllWt.ptN la P' z = if z.1 ∈ S then AllWt.ptN la P z else 0 := fun z => by
    by_cases hz : z.1 ∈ S
    · simp only [AllWt.ptN, hP', if_pos hz]
    · simp only [AllWt.ptN, hP', if_neg hz]
      exact Formalism.L2.Pj.pnorm_zero _ _ _

  have h1 : ENNReal.ofReal (AllWt.ptN la P ⟨y.1, y.2.1⟩) ^ 2 ≤ Formalism.L2.Pj.supE (U σ).X la P' ^ 2 := by
    have e : AllWt.ptN la P ⟨y.1, y.2.1⟩ = AllWt.ptN la P' ⟨y.1, y.2.1⟩ := by
      rw [hpt, if_pos hyS]
    rw [e]
    gcongr
    exact le_iSup (fun p : Formalism.L2.Pj.FPt (U σ).X => ENNReal.ofReal (((U σ).X p.1).pnorm (la p.1) (P' p.1) p.2)) y

  have h2 := GlobalTheory.T.weighted_frame_sum_second hT D j H Dw l Xo c U dict hL σ hσ la w hw hsp hchi P' hP'm

  have h3 : AllWt.petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P' ≤
      AllWt.petE (D.sp.W j) (dict σ) (AllWt.muOn (U σ) (D.sp.W j) (dict σ) Z) la P := by
    have hsupp : Function.support (fun q : AutQ (D.sp.W j) => AllWt.ptN la P' (dict σ q.out)) ⊆ Cl := by
      intro q hq
      by_contra hn
      apply hq
      have : ¬ (dict σ q.out).1 ∈ S := fun h => hn ((key _).2 h)
      show AllWt.ptN la P' (dict σ q.out) = 0
      rw [hpt, if_neg this]
    unfold AllWt.petE
    have hrestrict : eLpNorm' (fun q : AutQ (D.sp.W j) => AllWt.ptN la P' (dict σ q.out)) 2
        ((muQ1 (D.sp.W j)).restrict Cl) =
        eLpNorm' (fun q : AutQ (D.sp.W j) => AllWt.ptN la P' (dict σ q.out)) 2 (muQ1 (D.sp.W j)) := by
      simp only [eLpNorm'_eq_lintegral_eNorm]
      congr 1
      apply setLIntegral_eq_of_support_subset
      simpa using hsupp
    rw [← hrestrict]
    calc eLpNorm' (fun q : AutQ (D.sp.W j) => AllWt.ptN la P' (dict σ q.out)) 2 ((muQ1 (D.sp.W j)).restrict Cl)
        ≤ eLpNorm' (fun q : AutQ (D.sp.W j) => AllWt.ptN la P (dict σ q.out)) 2 ((muQ1 (D.sp.W j)).restrict Cl) := by
          refine eLpNorm'_mono_ae (by norm_num) (Filter.Eventually.of_forall fun q => ?_)
          rw [Real.norm_of_nonneg (AllWt.ptN_nonneg _ _ _), Real.norm_of_nonneg (AllWt.ptN_nonneg _ _ _), hpt]
          split_ifs
          · exact le_rfl
          · exact AllWt.ptN_nonneg _ _ _
      _ ≤ eLpNorm' (fun q : AutQ (D.sp.W j) => AllWt.ptN la P (dict σ q.out)) 2
            (AllWt.muOn (U σ) (D.sp.W j) (dict σ) Z) := by
          show _ ≤ eLpNorm' _ 2 ((muQ1 (D.sp.W j) Cl)⁻¹ • (muQ1 (D.sp.W j)).restrict Cl)
          rw [eLpNorm'_smul_measure (by norm_num)]
          refine le_mul_of_one_le_left (by simp) ?_
          exact ENNReal.one_le_rpow (ENNReal.one_le_inv.2 prob_le_one) (by norm_num)
  have h4 : ENNReal.ofReal (AllWt.ptN la P ⟨y.1, y.2.1⟩) ^ 2 ≤
      ENNReal.ofReal (GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d l.M w) *
        AllWt.petE (D.sp.W j) (dict σ) (AllWt.muOn (U σ) (D.sp.W j) (dict σ) Z) la P ^ 2 :=
    h1.trans (h2.trans (by gcongr))
  exact ENNReal.div_le_of_le_mul h4

end GlobalTheory.BergComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGeometryWeightBoundStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_geometry_weight_bound : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E), Even G.2 → ∀ (w : ℝ), 0 < w → (∀ k, (∑ τ, ((U σ).X k).spread (AllWt.modelWt (U σ) G k) τ) ≤ w) → ∀ (Z : Comp Xo c) (y : FPt (U σ).X), (⟨y.1, y.2.1⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r) ∈ AllWt.framesOn (U σ) Z → AllWt.bergOn (U σ) (D.sp.W j) (dict σ) Z G y ≤ ENNReal.ofReal (GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d l.M w) := by
  first | exact @GlobalTheory.BergComp.bergOn_le_supConst | exact GlobalTheory.BergComp.bergOn_le_supConst | (intros; apply GlobalTheory.BergComp.bergOn_le_supConst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRuleBoundedBelow
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaLow
open GlobalTheory.ThetaBound GlobalTheory.PlaceInt

theorem finite_vLa_ne_zero {K : Type} [Field K] [NumberField K] (x : K) :
    {w : HeightOneSpectrum (𝓞 K) | vLa w x ≠ 0}.Finite := by
  by_cases hx : x = 0
  · subst hx
    simpa [vLa] using (Set.finite_empty : (∅ : Set (HeightOneSpectrum (𝓞 K))).Finite)
  · refine (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 x hx)).subset fun w hw h1 => hw ?_
    simp only [Units.val_mk0] at h1
    simp [vLa, h1]

theorem vLa_natCast_eq_zero {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {g p : ℕ}
    (hg : ((g : ℕ) : 𝓞 K) ∈ w.asIdeal) (hc : Nat.Coprime g p) : vLa w ((p : ℕ) : K) = 0 := by
  have hp : ((p : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    intro hp
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 K))
    apply w.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← huv]
    simp only [eq_intCast, Int.cast_natCast]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hg) (Ideal.mul_mem_left _ _ hp)
  have h1 : w.valuation K ((p : ℕ) : K) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) p, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hp
  simp [vLa, h1]

theorem thetaRule_bounded_below : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (g g' : ℕ) (π π' : 𝓞 D.host.E), HalfSplit l g g' π π' → Nat.Coprime (g * g') (D.host.QS * D.host.q * D.host.d) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∃ m : HeightOneSpectrum (𝓞 c.F) → ℝ, (Function.support m).Finite ∧ (∀ f ∈ thGen Xo c nab a n, ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, ((m w : ℝ) : EReal) ≤ v f) ∧ ∀ w : HeightOneSpectrum (𝓞 c.F), (((g : ℕ) : 𝓞 c.F) ∈ w.asIdeal ∨ ((g' : ℕ) : 𝓞 c.F) ∈ w.asIdeal) → m w = -((vLa w (nrm Dw c a (star π * star π')) : ℤ) : ℝ) := by
  intro D H Dw l Xo c
  letI := H.starRing
  intro nab hnab g g' π π' hs hcop a n
  have hstar : ∀ x : 𝓞 D.host.E, star x = H.bar x := hnab.1
  obtain ⟨hg, hg', hne, hM, hπ, hπ', hMb, -, -⟩ := hs
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hπ
    exact hg.ne_zero (by exact_mod_cast hπ.symm)
  have hπ0' : π' ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hπ'
    exact hg'.ne_zero (by exact_mod_cast hπ'.symm)
  have hb0 : star π * star π' ≠ 0 := by
    rw [hstar, hstar]
    refine mul_ne_zero (fun h => hπ0 ?_) (fun h => hπ0' ?_)
    · rw [← TorsFac.bar_bar (H := H) π, h, map_zero]
    · rw [← TorsFac.bar_bar (H := H) π', h, map_zero]
  let ρ : HeightOneSpectrum (𝓞 c.F) → ℝ := fun w =>
    ∑ p ∈ D.host.condN.primeFactors, ((vLa w ((p : ℕ) : c.F) : ℤ) : ℝ) *
      D.host.vdH p * (Formalism.L2.Pj.DF Dw a : ℝ) / 2
  refine ⟨fun w => -(ρ w + ((vLa w (nrm Dw c a (star π * star π')) : ℤ) : ℝ)), ?_, ?_, ?_⟩
  ·
    have hfin : ((⋃ p ∈ D.host.condN.primeFactors,
        {w : HeightOneSpectrum (𝓞 c.F) | vLa w ((p : ℕ) : c.F) ≠ 0}) ∪
        {w | vLa w (nrm Dw c a (star π * star π')) ≠ 0}).Finite :=
      (Set.Finite.biUnion (Finset.finite_toSet _) fun p _ => finite_vLa_ne_zero _).union (finite_vLa_ne_zero _)
    refine hfin.subset fun w hw => ?_
    by_contra hn
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists, not_not] at hn
    apply hw
    have h0 : ρ w = 0 := Finset.sum_eq_zero fun p hp => by rw [hn.1 p hp]; simp
    simp [h0, hn.2]
  · intro f hf w v hv
    obtain ⟨y, rfl⟩ := hv
    obtain ⟨T, io, e, ho, yI, hy, eta, heta, hq⟩ := y.2
    have hv : vAtV y f = nval T.V e (evI yI f) := by
      show y.1.1 f = _
      rw [hq]
      rfl
    rw [hv]
    refine bound_of_chBound Xo c (star π * star π') hb0 ?_ nab hnab w a n (ρ w) ?_ T io e ho yI hy f hf
    · intro ℓ hp hd
      rw [hM] at hd ⊢
      rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hg').1 h1
        refine ⟨fun h2 => hne ?_, star π', star π, _root_.mul_comm _ _, ?_, ?_⟩
        · rw [pow_two] at h2
          exact ((Nat.prime_dvd_prime_iff_eq hg' hg).1 (Nat.dvd_of_mul_dvd_mul_left hg'.pos h2)).symm
        · rw [hstar, TorsFac.bar_bar, _root_.mul_comm]; exact hπ'
        · rw [hMb, hstar, TorsFac.bar_bar, Ideal.span_singleton_le_span_singleton]
          exact Dvd.intro_left _ rfl
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hg).1 h1
        refine ⟨fun h2 => hne ?_, star π, star π', rfl, ?_, ?_⟩
        · rw [pow_two] at h2
          exact (Nat.prime_dvd_prime_iff_eq hg hg').1 (Nat.dvd_of_mul_dvd_mul_right hg.pos h2)
        · rw [hstar, TorsFac.bar_bar, _root_.mul_comm]; exact hπ
        · rw [hMb, hstar, TorsFac.bar_bar, Ideal.span_singleton_le_span_singleton]
          exact Dvd.intro _ rfl
    · intro T' io' y' C' e' ho'
      have hc := HostChart.chBound_host D H Dw l Xo c hstar T' io' y' C' e' ho'.1 a n
        (Formalism.L2.Pj.DF Dw a) le_rfl
      convert hc using 1
      refine Finset.sum_congr rfl fun p _ => ?_
      have h1 := ho'.2 ((p : ℕ) : c.F)
      rw [map_natCast] at h1
      have he : (e' : ℝ) ≠ 0 := by exact_mod_cast ho'.1.ne'
      rw [h1]
      push_cast
      rw [mul_div_cancel_left₀ _ he]
  · intro w hw
    have h0 : ρ w = 0 := Finset.sum_eq_zero fun p hp => by
      have hcp : Nat.Coprime (g * g') p := Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_primeFactors hp) hcop
      rcases hw with hw | hw
      · rw [vLa_natCast_eq_zero w hw (Nat.Coprime.coprime_dvd_left (dvd_mul_right g g') hcp)]; simp
      · rw [vLa_natCast_eq_zero w hw (Nat.Coprime.coprime_dvd_left (dvd_mul_left g' g) hcp)]; simp
    show -(ρ w + _) = _
    rw [h0, zero_add]
end GlobalTheory.ThetaLow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedPeriodSlopeMulRamificationIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedPeriodSlopeMulRamificationIndex
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

theorem valV_map_of_vV {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (ψ : FractionRing V →+* FractionRing V') {r : ℕ}
    (h : ∀ x, x ≠ 0 → vV V' (ψ x) = (r : ℤ) * vV V x) {x : FractionRing V} (hx : x ≠ 0) :
    valV V' (ψ x) = valV V x ^ r := by
  have h1 := h x hx
  simp only [vV] at h1
  rw [← WithZero.exp_log (valV_ne_zero (V := V') ((map_ne_zero ψ).2 hx)),
    ← WithZero.exp_log (valV_ne_zero (V := V) hx), ← WithZero.exp_nsmul]
  congr 1
  rw [nsmul_eq_mul]; linarith

theorem exists_ringHom_of_vV {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V']
    [IsDomain V'] [IsDiscreteValuationRing V'] (ψ : FractionRing V →+* FractionRing V') {r : ℕ}
    (h : ∀ x, x ≠ 0 → vV V' (ψ x) = (r : ℤ) * vV V x) :
    ∃ g : V →+* V', (algebraMap V' (FractionRing V')).comp g = ψ.comp (algebraMap V (FractionRing V)) ∧
      ∀ (ϖ : V) (ϖ' : V'), Irreducible ϖ → Irreducible ϖ' → Associated (g ϖ) (ϖ' ^ r) := by
  have hi := IsFractionRing.injective V' (FractionRing V')
  have hex : ∀ a : V, ∃ b : V', algebraMap V' (FractionRing V') b = ψ (algebraMap V (FractionRing V) a) := fun a => by
    by_cases ha : algebraMap V (FractionRing V) a = 0
    · exact ⟨0, by rw [ha, map_zero, map_zero]⟩
    refine IsDiscreteValuationRing.exists_lift_of_le_one (K := FractionRing V') ?_
    refine (valV_map_of_vV ψ h ha).trans_le (pow_le_one₀ zero_le ?_)
    exact HeightOneSpectrum.valuation_le_one _ a
  choose g hg using hex
  let g' : V →+* V' :=
    { toFun := g
      map_one' := hi (by rw [hg, map_one, map_one, map_one])
      map_mul' := fun a b => hi (by rw [map_mul, hg, hg, hg, map_mul, map_mul])
      map_zero' := hi (by rw [hg, map_zero, map_zero, map_zero])
      map_add' := fun a b => hi (by rw [map_add (f := _), hg, hg, hg, map_add (f := _), map_add (f := _)]) }
  refine ⟨g', RingHom.ext hg, fun ϖ ϖ' hϖ hϖ' => ?_⟩
  have key : ∀ {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {π : W}, Irreducible π →
      valV W (algebraMap W (FractionRing W) π) = WithZero.exp (-1 : ℤ) := fun {W} _ _ _ π hπ => by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero hπ.maximalIdeal_eq
  have h0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_valuation_eq (A := V')
    (algebraMap V' (FractionRing V') (g ϖ)) (algebraMap V' (FractionRing V') (ϖ' ^ r)) (by
      change valV V' _ = valV V' _
      rw [hg, valV_map_of_vV ψ h h0, map_pow, map_pow, key hϖ, key hϖ'])
  refine ⟨u, hi ?_⟩
  rw [← hu, map_mul, _root_.mul_comm, Units.smul_def, Algebra.smul_def]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem HasPhi.baseChange {T T' : CDVR} {io : c.F →+* T.Fr} {io' : c.F →+* T'.Fr} {y : IntFr Xo c T io}
    {y' : IntFr Xo c T' io'} {r : ℕ} (hr : 0 < r) (ψ : T.Fr →+* T'.Fr)
    (hv : ∀ x, x ≠ 0 → vV T'.V (ψ x) = (r : ℤ) * vV T.V x)
    (hx : letI := io.toAlgebra; letI := io'.toAlgebra; y'.1.x = spMap ψ ≫ y.1.x) {φ : ℝ} (h : HasPhi y φ) :
    HasPhi y' (r * φ) := by
  letI := io.toAlgebra; letI := io'.toAlgebra
  obtain ⟨G, t, m1, m2, P, ϖ, Q, β, hϖ, hQ, h0, hβ, rfl⟩ := h
  obtain ⟨h₁, -, h₃, h₄, h₅⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨g, hg, hass⟩ := exists_ringHom_of_vV ψ hv
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
  have ha := hass ϖ ϖ' hϖ hϖ'
  have ig : Function.Injective g := by
    have : Function.Injective ((algebraMap T'.V T'.Fr).comp g) := by
      rw [hg]; exact ψ.injective.comp (IsFractionRing.injective T.V T.Fr)
    exact Function.Injective.of_comp (f := algebraMap T'.V T'.Fr) this
  have hI : (maximalIdeal T.V).map g ≤ maximalIdeal T'.V := by
    rw [hϖ.maximalIdeal_eq, hϖ'.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_le_span_singleton]
    exact (dvd_pow_self ϖ' hr.ne').trans ha.symm.dvd
  obtain ⟨G', m₀, P', hD, -, -, -, -, hxe, -⟩ := ArcDataDescent.exists_pelUnif_pull h₃.cubePull h₁.polBaseChange
    h₄.unifBaseChange h₅ ⟨inferInstance, inferInstance, inferInstance, T.cpl⟩
    ⟨inferInstance, inferInstance, inferInstance, T'.cpl⟩ G P g ig hI
  obtain ⟨_, _, _, _, _, n, -⟩ := sabPull h₃.cubePull (spMap ψ) t
  obtain ⟨n1, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m1 n
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 n
  have sq : spMap ψ ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap g :=
    (spMap_comp _ ψ).symm.trans ((congrArg spMap hg.symm).trans (spMap_comp g _))
  rw [sq] at n2
  rw [← hx] at n1
  obtain ⟨n3, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m₀ n2
  let e : P'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X := { hD.xe with map_smul' := hxe }
  obtain ⟨β', hβ', hφ⟩ := GlobalTheory.EtaVal.phiC_smul_pull E _ _ _ e β r (Nat.cast_nonneg r)
  refine ⟨G', _, n1, n3, P', ϖ', fun a => r * Q (hD.xe a), β', hϖ',
    fun a => GlobalTheory.QValPull.main T T' g _ _ hD ϖ ϖ' r ig hϖ hϖ' ha a _ (hQ _),
    fun a => mul_nonneg (Nat.cast_nonneg r) (h0 _), fun a => ?_, hφ.symm⟩
  rw [hβ', hβ]
  change (r : ℝ) * (2 * (Q (hD.xe a) : ℝ)) = _
  push_cast
  ring

theorem phi_eq_mul_of_frMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io') (r : ℕ), 0 < r → (letI := io.toAlgebra; letI := io'.toAlgebra; ∃ ψ : T.Fr →ₐ[c.F] T'.Fr, (∀ x, x ≠ 0 → vV T'.V (ψ x) = (r : ℤ) * vV T.V x) ∧ FrMap ψ y.1 y'.1) → ∀ φ φ' : ℝ, HasPhi y φ → HasPhi y' φ' → φ' = r * φ := by
  rintro E _ _ _ H Dw l Xo c T T' io io' y y' r hr ⟨ψ, hv, hm⟩ φ φ' h h'
  letI := io.toAlgebra; letI := io'.toAlgebra
  exact HasPhi.unique h' (HasPhi.baseChange hr ψ.toRingHom hv hm.1 h)

end GlobalTheory.SlopeRec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedPeriodSlopeMulRamificationIndexStatement
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balancedPeriodSlope_mul_ramificationIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io') (r : ℕ), 0 < r → (letI := io.toAlgebra; letI := io'.toAlgebra; ∃ ψ : T.Fr →ₐ[c.F] T'.Fr, (∀ x, x ≠ 0 → vV T'.V (ψ x) = (r : ℤ) * vV T.V x) ∧ FrMap ψ y.1 y'.1) → ∀ φ φ' : ℝ, HasPhi y φ → HasPhi y' φ' → φ' = r * φ := by
  first | exact @GlobalTheory.SlopeRec.phi_eq_mul_of_frMap | exact GlobalTheory.SlopeRec.phi_eq_mul_of_frMap | (intros; apply GlobalTheory.SlopeRec.phi_eq_mul_of_frMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormAdjointCmActionModuliPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormAdjointCmActionModuliPoint
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolAdjointRing

theorem polForm_adjoint : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∀ {ψ : LinearMap.BilinForm S (HdR A)}, IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → IsAdjointFor a (fun z => H.bar z) ψ := by
  open ReciprocityTheory.ChartRestriction.G.Semi CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in
   intro P E _ _ _ H Dw l Xo S _ x A _ π hπ a ha ψ hψ z u v
   have hG := ObjDim.isAbelianScheme Xo.univ
   have hA : IsAbelianScheme A := by
     have := hG.comm
     have hc : IsCommMonObj A := by
       rw [isCommMonObj_iff_isMulCommutative]
       intro T
       refine ⟨⟨fun x y => Over.OverMorphism.ext (hπ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
       rw [← hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl,
         ← hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl, _root_.mul_comm]
     exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hπ.1 hG.smooth,
       MorphismProperty.of_isPullback (P := @IsProper) hπ.1 hG.proper,
       MorphismProperty.of_isPullback (P := @GeometricallyConnected) hπ.1 hG.geomConnected⟩
   have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
     (ObjDim.smoothOfRelativeDimension Xo.univ)
   have := hA.comm
   have := a.hom
   exact GlobalTheory.PolAdjoint.adjoint_of_lbIso P.1 hA gA (pull_isLB Xo.univ.t.PP.isLB π) hψ (a.act z)
     (a.act (H.bar z)) (GlobalTheory.PolAdjoint.lbIso_cube hπ _ (ha z) (ha (H.bar z)) (Xo.univ.t.adj z)) u v
end GlobalTheory.PolAdjointRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormAdjointCmActionModuliPointStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarizationForm_adjoint_cmAction_moduli_point : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∀ {ψ : LinearMap.BilinForm S (HdR A)}, IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → IsAdjointFor a (fun z => H.bar z) ψ := by
  first | exact @GlobalTheory.PolAdjointRing.polForm_adjoint | exact GlobalTheory.PolAdjointRing.polForm_adjoint | (intros; apply GlobalTheory.PolAdjointRing.polForm_adjoint <;> assumption)
end
end
