module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyCoordinateCombinationsNoCommonZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionGenericFibre
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CurveRootGeometry GlobalTheory.ConjSeq
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBExtDVR

theorem isOpenImmersion_spMap_fractionRing (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] :
    IsOpenImmersion (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : IsLocalization.Away ϖ K := by
    refine IsLocalization.Away.mk ϖ ?_ ?_ ?_
    · exact IsUnit.mk0 _ (by
        simpa using (IsFractionRing.injective R K).ne_iff.2 hϖ.ne_zero)
    · intro z
      obtain ⟨⟨x, y, hy⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) z
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (nonZeroDivisors.ne_zero hy) hϖ
      refine ⟨n, x * ↑u⁻¹, ?_⟩
      simp only at h
      rw [map_mul, ← h, hu, _root_.mul_assoc, ← map_mul, ← map_pow]
      congr 2
      rw [mul_right_comm, Units.mul_inv, _root_.one_mul]
    · intro x y h
      exact ⟨0, by rw [IsFractionRing.injective R K h]⟩
  exact IsOpenImmersion.of_isLocalization ϖ

theorem exists_lineBundle_extension_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X Y : Scheme.{0}) (s : X ⟶ Sp R) (t : Y ⟶ Sp K) (a : Y ⟶ X), Smooth s → QuasiCompact s → IsPullback a t s (spMap (algebraMap R K)) → ∀ L : LB Y, L.IsLB → ∃ M : LB X, M.IsLB ∧ LBIso (M.pull a) L := by
  intro R K _ _ _ _ _ _ X Y s t a hs hq hpb L hL
  haveI := isOpenImmersion_spMap_fractionRing R K
  have ha : IsOpenImmersion a := MorphismProperty.of_isPullback hpb.flip this
  haveI : IsRegularRing R := inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have key : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      UniqueFactorizationMonoid (X.presheaf.stalk x) := fun x => by
    haveI : IsRegularRing (X.presheaf.stalk x) :=
      GlobalTheory.ExtendRig.isRegularRing_stalk GlobalTheory.isRegularRing_of_smooth R s x
    haveI : IsRegularLocalRing (X.presheaf.stalk x) :=
      IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
    haveI : IsDomain (X.presheaf.stalk x) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
    exact ⟨inferInstance, GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
      GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE _⟩
  exact GlobalTheory.exists_lineBundle_extension_of_isDomain X Y a ha (fun x => (key x).1)
    (fun x => (key x).2) L hL

end GlobalTheory.LBExtDVR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftFieldPointFiniteSurjectiveAfterExtensi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftFieldPointFiniteSurjectiveAfterExtensi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinLift

theorem lift_point_finite_surjective : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (y : Sp K ⟶ X) (q : Y ⟶ X), IsFinite q → Surjective q → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (y' : Sp L ⟶ Y), y' ≫ q = spMap (algebraMap K L) ≫ y := by
  intro K _ X Y y q hq hs
  haveI := hq
  haveI := hs
  have : IsAffine (pullback q y) := isAffine_of_isAffineHom (pullback.snd q y)
  let e := (pullback q y).isoSpec
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (e.inv ≫ pullback.snd q y)
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  obtain ⟨x⟩ : Nonempty (PrimeSpectrum K) := inferInstance
  obtain ⟨p, -⟩ := (pullback.snd q y).surjective x
  let pt : PrimeSpectrum Γ(pullback q y, ⊤) := e.hom.base p
  obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal pt.asIdeal pt.isPrime.ne_top
  let L := Γ(pullback q y, ⊤) ⧸ m
  letI : Field L := Ideal.Quotient.field m
  let ψ : K →+* L := (Ideal.Quotient.mk m).comp φ.hom
  letI : Algebra K L := ψ.toAlgebra
  have hψ : ψ.Finite := RingHom.Finite.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) hfin
  haveI : FiniteDimensional K L := hψ
  refine ⟨L, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ e.inv ≫ pullback.fst q y, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.inv, ← hφ,
    ← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.FinLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftFieldPointFiniteSurjectiveAfterExtensiStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_fieldPoint_finite_surjective_after_extension : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (y : Sp K ⟶ X) (q : Y ⟶ X), IsFinite q → Surjective q → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (y' : Sp L ⟶ Y), y' ≫ q = spMap (algebraMap K L) ≫ y := by
  first | exact @GlobalTheory.FinLift.lift_point_finite_surjective | exact GlobalTheory.FinLift.lift_point_finite_surjective | (intros; apply GlobalTheory.FinLift.lift_point_finite_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermitianPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AHExists

theorem dotProduct_pullback {g n : ℕ} (J : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (H : Matrix (Fin n) (Fin n) ℂ)
    (z w : Fin g → ℂ) :
    z ⬝ᵥ ((LinearMap.toMatrix' J).transpose * H * (LinearMap.toMatrix' J).map star).mulVec (star w) =
      J z ⬝ᵥ H.mulVec (star (J w)) := by
  have e : ((LinearMap.toMatrix' J).map star).mulVec (star w) = star (J w) := by
    rw [← LinearMap.toMatrix'_mulVec J w]
    generalize LinearMap.toMatrix' J = N
    funext a
    simp [Matrix.mulVec, dotProduct, star_sum, _root_.mul_comm]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    LinearMap.toMatrix'_mulVec]

theorem isHermitian_pullback {g n : ℕ} (N : Matrix (Fin n) (Fin g) ℂ) {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) : (N.transpose * H * N.map star).IsHermitian := by
  have e : N.transpose = (N.map star).conjTranspose := by
    ext a b
    simp
  rw [e]
  exact Matrix.isHermitian_conjTranspose_mul_mul _ hH

theorem exists_isAH : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → ∀ (L : LB A.left) (u : HolUnif A L g), ∃ (M : LB A.left) (u' : HolUnif A M g) (H : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ), M.IsLB ∧ u'.ex = u.ex ∧ u'.Λ = u.Λ ∧ u'.IsAH H χ := by
  intro A _ g hA L u
  obtain ⟨Q, v, i, r, J, R, m, -, hi, -, hm, hJ, -, -, -, hRJ⟩ :=
    GlobalTheory.HolUnifHom.exists_linear_factor A g hA (GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u) L u
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨v', Hm, χ', -, hAH, -, hv1, hv2, -⟩ := thetaUnifAV_all Q rig hrig
  obtain ⟨J', hJ', hJΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom A Q.A hA Q.isAb L Q.L g Q.g u v'
    hv1 hv2 i hi
  have hinj : ∀ z, J' z = 0 → z = 0 := by
    intro z hz
    have h0 : J z = 0 := LatticeHom.eq_zero_of_forall_smul_mem v.Λ v.discrete fun t => by
      rw [← map_smul, ← v.ker, hJ, ← hJ', map_smul, hz, smul_zero, v'.ker]
      exact v'.Λ.zero_mem
    have h1 := hRJ z
    rw [h0, map_zero, ← Nat.cast_smul_eq_nsmul ℂ] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left (by exact_mod_cast (show m ≠ 0 by omega))
  obtain ⟨u₁, hex, hΛ₁, hfr⟩ := GlobalTheory.exists_holUnif_linComb A Q.A L Q.L g Q.g u v' PUnit (fun _ => i)
    (fun _ => J') (fun _ => 1) (fun _ z => hJ' z)
  have hmem : ∀ l : u₁.Λ, J' (l : Fin g → ℂ) ∈ v'.Λ := fun l => hJΛ _ (hΛ₁ ▸ l.2)
  refine ⟨_, u₁, (LinearMap.toMatrix' J').transpose * Hm * (LinearMap.toMatrix' J').map star,
    fun l => χ' ⟨J' l.1, hmem l⟩, LB.isLB_linComb Q.isLB _ _, hex, hΛ₁, isHermitian_pullback _ hAH.1,
    fun z hz => ?_, fun l => hAH.2.2.1 _, ?_⟩
  · rw [dotProduct_pullback]
    exact hAH.2.1 _ fun h => hz (hinj z h)
  intro l j z hz
  rw [hex] at hz
  have hz' : ⊤ ≤ (v'.ex (J' z)).left ⁻¹ᵁ Q.L.U (j PUnit.unit) := by
    rw [hJ' z]
    exact (CubeValues.le_preimage_wchart (u.ex z).left Q.L (fun _ => i.left) j).1 hz PUnit.unit
  have e1 : u₁.fr j z = v'.fr (j PUnit.unit) (J' z) := by simpa using hfr j z
  have e2 : u₁.fr j (z + l) = v'.fr (j PUnit.unit) (J' z + J' l) := by simpa using hfr j (z + l)
  rw [e1, e2, dotProduct_pullback, dotProduct_pullback]
  exact hAH.2.2.2 ⟨J' l.1, hmem l⟩ (j PUnit.unit) (J' z) hz'

end GlobalTheory.AHExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoVariablesResCocycleEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoVariablesResCocycleEq
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.fv_add_h_res {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R}
    {t : G.TorsionTower A} {c : primDR A} (d : Dat t c) (n : ℕ) (D : Type) [CommRing D] [Algebra R D]
    (φ : G.A n →ₐ[R] D) :
    fv d.f (G.A (n + 1)) D (φ.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) (t.y (n + 1)) +
      (φ.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) (d.h (n + 1)) = fv d.f (G.A n) D φ (t.y n) + φ (d.h n) := by
  have hc := (fv_isCoc_and_ev_eq R A d.f).1 (G.A (n + 1)) (G.A n) D
    (G.res n : G.A (n + 1) →ₐ[R] G.A n) φ (t.y (n + 1)) (sm_whole (t.y (n + 1)))
  rw [hc, t.res n, d.res n, AlgHom.comp_apply, map_sub]
  simp only [BialgHom.coe_toAlgHom]
  abel

theorem Dat.pullTwo_res_coc (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ) :
    pullbackTwo (G.res n) (d.coc (n + 1)) = d.coc n := by
  let L : G.A n →ₐ[R] G.A n ⊗[R] G.A n := Algebra.TensorProduct.includeLeft
  let Rt : G.A n →ₐ[R] G.A n ⊗[R] G.A n := Algebra.TensorProduct.includeRight
  have hres : ∀ u : G.A (n + 1) ⊗[R] G.A (n + 1), pullbackTwo (G.res n) u =
      Algebra.TensorProduct.lift (L.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n))
        (Rt.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) (fun _ _ ↦ Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul a b => simp [L, Rt]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hid : ∀ u : G.A n ⊗[R] G.A n,
      Algebra.TensorProduct.lift L Rt (fun _ _ ↦ Commute.all _ _) u = u := by
    intro u
    simp only [L, Rt, Algebra.TensorProduct.lift_includeLeft_includeRight, AlgHom.id_apply]
  have hmul : (toConv (L.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) *
      toConv (Rt.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n))).ofConv =
      (toConv L * toConv Rt).ofConv.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n) :=
    (AlgHom.convMul_comp_bialgHom_distrib (toConv L) (toConv Rt) (G.res n)).symm
  rw [hres, Dat.lift_coc, hmul, d.fv_add_h_res n, d.fv_add_h_res n, d.fv_add_h_res n]
  conv_rhs => rw [← hid (d.coc n), Dat.lift_coc]
  simp only [← spOver_comp, Category.assoc, t.res]

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoVariablesResCocycleEqStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.bialgebraPullbackTwoVariables_res_cocycle_eq
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ) :
    pullbackTwo (G.res n) (d.coc (n + 1)) = d.coc n :=
  Dat.pullTwo_res_coc R A p G t c d n
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosureCompleteNormalFiniteExtensi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosureCompleteNormalFiniteExtensi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_integralClosure_isCN_finite_local : ∀ (V₀ : Type) [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀], IsCN V₀ → ∀ (L : Type) [Field L] [Algebra (FractionRing V₀) L] [FiniteDimensional (FractionRing V₀) L], ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V₀ →+* V₁) (σ : L →+* FractionRing V₁), IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ ∀ x : V₀, σ (algebraMap (FractionRing V₀) L (algebraMap V₀ (FractionRing V₀) x)) = algebraMap V₁ (FractionRing V₁) (ρ x) := by
  intro V₀ _ _ _ hV L _ _ _
  obtain ⟨hN, hIC, hC, hCZ⟩ := hV
  haveI := hN
  haveI := hIC
  haveI := hC
  haveI := hCZ
  let K₀ := FractionRing V₀
  letI : Algebra V₀ L := ((algebraMap K₀ L).comp (algebraMap V₀ K₀)).toAlgebra
  haveI : IsScalarTower V₀ K₀ L := .of_algebraMap_eq fun _ => rfl
  haveI : CharZero K₀ := IsFractionRing.charZero_of_isFractionRing V₀
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K₀ L).injective
  haveI : Algebra.IsSeparable K₀ L := inferInstance
  let V₁ := integralClosure V₀ L
  haveI : Module.Finite V₀ V₁ := IsIntegralClosure.finite V₀ K₀ L V₁
  haveI hN₁ : IsNoetherianRing V₁ := IsIntegralClosure.isNoetherianRing V₀ K₀ L V₁
  haveI : IsFractionRing V₁ L := IsIntegralClosure.isFractionRing_of_finite_extension V₀ K₀ L V₁
  haveI : IsIntegrallyClosed V₁ := integralClosure.isIntegrallyClosedOfFiniteExtension K₀
  haveI : HenselianLocalRing V₀ := GlobalTheory.henselianLocalRing_of_isAdicComplete V₀
  haveI : IsLocalRing V₁ := GlobalTheory.TameKummer.isLocalRing_of_finite V₀ V₁
  have hinj : Function.Injective (algebraMap V₀ V₁) := by
    intro a b h
    have h' := congrArg (algebraMap V₁ L) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply V₀ K₀ L, IsScalarTower.algebraMap_apply V₀ K₀ L b] at h'
    exact IsFractionRing.injective V₀ K₀ ((algebraMap K₀ L).injective h')
  haveI : CharZero V₁ := charZero_of_injective_algebraMap hinj
  haveI : IsLocalHom (algebraMap V₀ V₁) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : (maximalIdeal V₁).comap (algebraMap V₀ V₁) = maximalIdeal V₀ :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := V₀) (maximalIdeal V₁))
    have hmem : a ∈ (maximalIdeal V₁).comap (algebraMap V₀ V₁) := by
      rw [hm]; exact hna
    exact hmem ha
  have hcompl : IsAdicComplete (maximalIdeal V₁) V₁ :=
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local V₀ V₁
  let e : L ≃ₐ[V₁] FractionRing V₁ := IsLocalization.algEquiv (nonZeroDivisors V₁) L (FractionRing V₁)
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, algebraMap V₀ V₁, e.toRingEquiv.toRingHom,
    ⟨hN₁, inferInstance, hcompl, inferInstance⟩, hinj, RingHom.finite_algebraMap.mpr inferInstance,
    inferInstance, fun x => ?_⟩
  have hx : algebraMap K₀ L (algebraMap V₀ K₀ x) = algebraMap V₁ L (algebraMap V₀ V₁ x) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv]
  rw [hx, AlgEquiv.commutes]

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosureCompleteNormalFiniteExtensiStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_local_extension_with_embedded_field_extension : ∀ (V₀ : Type) [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀], IsCN V₀ → ∀ (L : Type) [Field L] [Algebra (FractionRing V₀) L] [FiniteDimensional (FractionRing V₀) L], ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V₀ →+* V₁) (σ : L →+* FractionRing V₁), IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ ∀ x : V₀, σ (algebraMap (FractionRing V₀) L (algebraMap V₀ (FractionRing V₀) x)) = algebraMap V₁ (FractionRing V₁) (ρ x) := by
  first | exact @GlobalTheory.Poinc.exists_integralClosure_isCN_finite_local | exact GlobalTheory.Poinc.exists_integralClosure_isCN_finite_local | (intros; apply GlobalTheory.Poinc.exists_integralClosure_isCN_finite_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameOfSectionUnitsOnClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameOfSectionUnitsOnClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem isUnit_gs_id_iff {X : Scheme.{0}} (z : X) (U : X.Opens) (h : z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs (𝟙 X) z U a) ↔ z ∈ X.basicOpen a := by
  rw [gs_eq (𝟙 X) z U h, X.mem_basicOpen a z h]
  rfl

theorem exists_frame_of_isUnit_on_fibre : ∀ (X Y : Scheme.{0}) (β : X ⟶ Y), IsClosedMap β.base → ∀ (L : LB X), L.IsLB → ∀ (V : Y.Opens) (s : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V ⊓ L.U k)), IsSecOver L (β ⁻¹ᵁ V) s → ∀ y : Y, y ∈ V → (∀ (z : X) (k : L.ι), β z = y → z ∈ L.U k → IsUnit (gs (𝟙 X) z (β ⁻¹ᵁ V ⊓ L.U k) (s k))) → ∃ V' : Y.Opens, y ∈ V' ∧ V' ≤ V ∧ ∃ T : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V' ⊓ L.U k)ˣ, IsFrameOver L (β ⁻¹ᵁ V') T ∧ ∀ (f : X ⟶ X) (w : LB.Iso L (L.pull f)), SecCarriedOver L (β ⁻¹ᵁ V) s f w → FrameCarried L (β ⁻¹ᵁ V') T f w := by
  intro X Y β hβ L hL V s hs y hy hu
  let N : X.Opens := ⨆ k, X.basicOpen (s k)
  have hN : ∀ z : X, β z = y → z ∈ N := by
    intro z hz
    obtain ⟨k, hk⟩ := exists_chart hL z
    have hm : z ∈ β ⁻¹ᵁ V ⊓ L.U k := ⟨show β z ∈ V from hz ▸ hy, hk⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (isUnit_gs_id_iff z _ hm _).1 (hu z k hz hk)⟩
  let V₀ : Y.Opens := ⟨(β '' (N : Set X)ᶜ)ᶜ, (hβ _ N.2.isClosed_compl).isOpen_compl⟩
  have hy₀ : y ∈ V₀ := by
    rintro ⟨p, hp, e⟩
    exact hp (hN p e)
  have hV₀ : ∀ p : X, β p ∈ V₀ → p ∈ N := by
    intro p hp
    by_contra h
    exact hp ⟨p, h, rfl⟩
  have hle : ∀ k, β ⁻¹ᵁ (V ⊓ V₀) ⊓ L.U k ≤ β ⁻¹ᵁ V ⊓ L.U k := fun k z hz => ⟨hz.1.1, hz.2⟩
  have hunit : ∀ k, IsUnit ((X.presheaf.map (homOfLE (hle k)).op).hom (s k)) := by
    intro k
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    obtain ⟨k', hk'⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV₀ z hz.1.2)
    have hm' : z ∈ β ⁻¹ᵁ V ⊓ L.U k' := X.basicOpen_le _ hk'
    have h1 : IsUnit (gs (𝟙 X) z _ (s k)) := by
      rw [hs z k k' hm'.1 hz.2 hm'.2]
      exact (Units.isUnit _).mul ((isUnit_gs_id_iff z _ hm' _).2 hk')
    rw [← gs_res (𝟙 X) z (hle k) hz, gs_eq (𝟙 X) z _ hz] at h1
    exact h1
  have key : ∀ (f : X ⟶ X) (z : X) (k : L.ι), f z ∈ β ⁻¹ᵁ (V ⊓ V₀) → f z ∈ L.U k →
      (gm f z _ (hunit k).unit : X.presheaf.stalk z) = gs f z _ (s k) := by
    intro f z k h1 h2
    have hm : f z ∈ β ⁻¹ᵁ (V ⊓ V₀) ⊓ L.U k := ⟨h1, h2⟩
    rw [← gs_unit f z _ hm, IsUnit.unit_spec, gs_res f z (hle k) hm]
  refine ⟨V ⊓ V₀, ⟨hy, hy₀⟩, inf_le_left, fun k => (hunit k).unit, ?_, ?_⟩
  · intro k k'
    refine unit_ext fun z hz => ?_
    rw [map_mul, gm_res _ z _ hz, gm_res _ z _ hz, gm_res _ z _ hz]
    apply Units.ext
    rw [Units.val_mul, key (𝟙 X) z k hz.1.1 hz.1.2, key (𝟙 X) z k' hz.2.1 hz.2.2]
    exact hs z k k' hz.1.1.1 hz.1.2 hz.2.2
  · intro f w hw z j k hz hfz hk hj
    apply Units.ext
    rw [Units.val_mul, key f z j hfz hj, key (𝟙 X) z k hz hk]
    exact hw z j k hz.1 hfz.1 hk hj

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameOfSectionUnitsOnClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleFrame_of_section_units_on_closedFibre : ∀ (X Y : Scheme.{0}) (β : X ⟶ Y), IsClosedMap β.base → ∀ (L : LB X), L.IsLB → ∀ (V : Y.Opens) (s : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V ⊓ L.U k)), IsSecOver L (β ⁻¹ᵁ V) s → ∀ y : Y, y ∈ V → (∀ (z : X) (k : L.ι), β z = y → z ∈ L.U k → IsUnit (gs (𝟙 X) z (β ⁻¹ᵁ V ⊓ L.U k) (s k))) → ∃ V' : Y.Opens, y ∈ V' ∧ V' ≤ V ∧ ∃ T : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V' ⊓ L.U k)ˣ, IsFrameOver L (β ⁻¹ᵁ V') T ∧ ∀ (f : X ⟶ X) (w : LB.Iso L (L.pull f)), SecCarriedOver L (β ⁻¹ᵁ V) s f w → FrameCarried L (β ⁻¹ᵁ V') T f w := by
  first | exact @GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre | exact GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre | (intros; apply GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordOfGenericExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordOfGenericExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum


set_option maxHeartbeats 1000000 in
theorem lbIso_lam_of_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L' : LB G.left) (N : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left), L'.IsLB → N.IsLB → LBIso N (L'.pull (pullback.fst G.hom (jK R))) → ExtLam G N PP → LBIso (abelian₂ G L') PP := by
  intro R _ _ _ _ _ G _ _ hG L' N PP hL' hN hNL hE
  have hsm : Smooth G.hom := hG.smooth
  have hgc : GeometricallyConnected G.hom := hG.geomConnected
  have hsm₂ : Smooth (G ⊗ G).hom := by
    show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have hgc₂ : GeometricallyConnected (G ⊗ G).hom := by
    show GeometricallyConnected (pullback.fst G.hom G.hom ≫ G.hom)
    exact GeometricallyConnected.comp _ _
  have hgi₂ : GeometricallyIntegral (G2 G).hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have hLam : (abelian₂ G L').IsLB := DVR.linComb_isLB _ hL' _ _
  have hPP : PP.IsLB := hE.1

  have hpb := isGrpPullback_pullback G (jK R)
  obtain ⟨β₂, hsq, hβ⟩ := GlobalTheory.T.exists_mumfordBundle_pullback_grpPullback _ _ (jK R) G ((Over.pullback (jK R)).obj G) (pullback.fst G.hom (jK R)) hpb
  have h1 : LBIso (abelian₂ G L') ((abelian₂ G L').pull (𝟙 _)) :=
    LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hLam)
  have h2 := hβ L' N _ (abelian₂ G L') (𝟙 _) hL' hN hLam hNL h1
  rw [Category.comp_id] at h2
  have h3 := hE.2 β₂ hsq
  have hgen : LBIso ((abelian₂ G L').pull β₂) (PP.pull β₂) :=
    LBIso.trans (pull_isLB hLam _) (DVR.linComb_isLB _ hN _ _) (pull_isLB hPP _) (LBIso.symm h2) h3

  let p1 := pullback.fst (G2 G).hom (jK R)
  let p2 := pullback.snd (G2 G).hom (jK R)
  let T : Over (Spec (CommRingCat.of (FractionRing R))) := Over.mk p2
  have wx : (p1 ≫ (fst G G).left) ≫ G.hom = p2 ≫ jK R := by
    rw [Category.assoc, Over.w (fst G G)]; exact pullback.condition
  have wy : (p1 ≫ (snd G G).left) ≫ G.hom = p2 ≫ jK R := by
    rw [Category.assoc, Over.w (snd G G)]; exact pullback.condition
  let x : T ⟶ (Over.pullback (jK R)).obj G := Over.homMk (hpb.1.lift _ _ wx) (hpb.1.lift_snd _ _ _)
  let y : T ⟶ (Over.pullback (jK R)).obj G := Over.homMk (hpb.1.lift _ _ wy) (hpb.1.lift_snd _ _ _)
  let i : pullback (G2 G).hom (jK R) ⟶ (G2 ((Over.pullback (jK R)).obj G)).left := (lift x y).left
  have hi : i ≫ β₂ = p1 := by
    apply pullback.hom_ext
    · show i ≫ β₂ ≫ (fst G G).left = p1 ≫ (fst G G).left
      rw [hsq.1, ← Category.assoc]
      show (lift x y ≫ fst _ _).left ≫ _ = _
      rw [lift_fst]
      exact hpb.1.lift_fst _ _ _
    · show i ≫ β₂ ≫ (snd G G).left = p1 ≫ (snd G G).left
      rw [hsq.2, ← Category.assoc]
      show (lift x y ≫ snd _ _).left ≫ _ = _
      rw [lift_snd]
      exact hpb.1.lift_fst _ _ _
  have hK : LBIso ((abelian₂ G L').pull p1) (PP.pull p1) :=
    LBIso.chartPull (chartPullSame (abelian₂ G L') (fun _ => p1) (fun _ => β₂) (fun _ => 1) i (fun _ => hi.symm))
      (chartPullSame PP (fun _ => p1) (fun _ => β₂) (fun _ => 1) i (fun _ => hi.symm)) hgen
  exact GlobalTheory.T.lineBundleIso_of_generic_normal_local_base R (G2 G) (lift η[G] η[G]).left (Over.w (lift η[G] η[G])) (abelian₂ G L') PP hLam hPP hK

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordOfGenericExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_mumford_of_generic_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L' : LB G.left) (N : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left), L'.IsLB → N.IsLB → LBIso N (L'.pull (pullback.fst G.hom (jK R))) → ExtLam G N PP → LBIso (abelian₂ G L') PP := by
  first | exact @GlobalTheory.Mum.lbIso_lam_of_extLam | exact GlobalTheory.Mum.lbIso_lam_of_extLam | (intros; apply GlobalTheory.Mum.lbIso_lam_of_extLam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveRiemannFormOfRelAmpleExponential
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveRiemannFormOfRelAmpleExponential
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory

theorem im_dot_mulVec_star_zsmul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℤ) (v w : Fin g → ℂ) :
    ((c • v) ⬝ᵥ Hm *ᵥ star w).im = c * (v ⬝ᵥ Hm *ᵥ star w).im := by
  rw [smul_dotProduct, zsmul_eq_mul, Complex.mul_im]
  simp

theorem im_dot_mulVec_star_zsmul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℤ) (v w : Fin g → ℂ) :
    (v ⬝ᵥ Hm *ᵥ star (c • w)).im = c * (v ⬝ᵥ Hm *ᵥ star w).im := by
  rw [star_zsmul, Matrix.mulVec_smul, dotProduct_smul, zsmul_eq_mul, Complex.mul_im]
  simp

theorem exists_riemannForm_of_relAmple : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (L : LB G.left), L.IsLB → Out.RelAmple G L → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (La : Type) [AddCommGroup La] (P : La →+ (Fin g → ℂ)), IsExp y e → Function.Injective P → (∀ z, e z = 1 ↔ z ∈ P.range) → ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La), Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ (∀ x x', (hermForm Hm (P x) (P x')).im = EF x x') ∧ (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs G L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) := by
  intro X G _ _ g hG hsm L hL hamp y e La _ P he hP hker
  obtain ⟨Λ, hd, hfull, hΛ⟩ := GlobalTheory.T.complexFibreExponential_kernel_full_lattice X G g hG hsm y e he
  obtain ⟨hadd, honto, hhol, -, -⟩ := he
  letI : GrpObj ((Over.pullback y).obj G) := Functor.grpObjObj
  haveI : IsCommMonObj ((Over.pullback y).obj G) := Functor.isCommMonObj_obj
  have hp : IsGrpPullback ((Over.pullback y).obj G) G y (pullback.fst G.hom y) := isGrpPullback_pullback G y
  have hLA : (L.pull (pullback.fst G.hom y)).IsLB := LB.isLB_pull hL _
  obtain ⟨hA, hampA, -⟩ := GlobalTheory.pol_pull X (Sp ℂ) G ((Over.pullback y).obj G) y (pullback.fst G.hom y) L
    (L.pull (pullback.fst G.hom y)) hL hLA hG hp (GlobalTheory.PolBaseChange.lbIso_refl hLA)
  let L₀ : LB G.left := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
  let u₀ : HolUnif ((Over.pullback y).obj G) (L₀.pull (pullback.fst G.hom y)) g :=
    GlobalTheory.OrthoMetric.fibreUnif hp (L := L₀) e Λ.toAddSubgroup (fun _ _ => 1) hadd honto hΛ hd hfull hhol
      (fun _ => differentiableOn_const _) (fun _ _ _ => one_ne_zero)
      (fun j j' z hz => by
        show (1 : ℂ) = valAt' (e z).left (⊤ ⊓ ⊤) (1 : Γ(G.left, ⊤ ⊓ ⊤)ˣ).val * 1
        rw [_root_.mul_one]
        exact (valAt'_one _ hz).symm)
  obtain ⟨u, Hm, χ, hex, hF⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif _ hA _ g u₀ _ hLA
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple _ hA _ hLA (hampA hamp) g u Hm χ hF.1 hF.2.1 hF.2.2
  have hAH : u.IsAH Hm χ := GlobalTheory.TorusRM.isAH_of_isFactorAH hF hpos
  have huΛ : ∀ z, z ∈ u.Λ ↔ z ∈ P.range := fun z => by
    rw [← u.ker, hex]
    exact (u₀.ker z).trans ((hΛ z).symm.trans (hker z))
  have hmem : ∀ a, P a ∈ u.Λ := fun a => (huΛ _).2 ⟨a, rfl⟩
  choose N hN using fun a b => GlobalTheory.TorusRM.ahFactor_im_int g _ _ u Hm χ hLA hF (P a) (hmem a) (P b) (hmem b)
  let EF : LinearMap.BilinForm ℤ La := LinearMap.mk₂ ℤ N
    (fun a a' b => Int.cast_injective (α := ℝ) (by
      push_cast; rw [← hN, ← hN, ← hN, map_add (f := _), add_dotProduct, Complex.add_im]))
    (fun c a b => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, ← hN, ← hN, map_zsmul]
      exact im_dot_mulVec_star_zsmul_left Hm c _ _))
    (fun a b b' => Int.cast_injective (α := ℝ) (by
      push_cast; rw [← hN, ← hN, ← hN, map_add (f := _), star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im]))
    (fun c a b => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, ← hN, ← hN, map_zsmul]
      exact im_dot_mulVec_star_zsmul_right Hm c _ _))
  have hEF : ∀ a b, EF a b = N a b := fun _ _ => rfl
  have tr : ∀ (t : Sp ℂ ⟶ X), (𝟙_ (Over (Sp ℂ))).hom ≫ y = t → ∀ (k : ℤ)
      (x x' : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback y).obj G) (x₀ x₀' : Over.mk t ⟶ G) (c : Γ(Sp ℂ, ⊤)ˣ),
      x₀.left = x.left ≫ pullback.fst G.hom y → x₀'.left = x'.left ≫ pullback.fst G.hom y →
      Out.WeilIs _ (L.pull (pullback.fst G.hom y)) k x x' c → Out.WeilIs G L k x₀ x₀' c := by
    intro t ht
    subst ht
    intro k x x' x₀ x₀' c h1 h2 hw
    exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm X (Sp ℂ) G _ y _ L _ hL hLA hp
      (GlobalTheory.PolBaseChange.lbIso_refl hLA) (𝟙_ _) k x x' x₀ x₀' c h1 h2).1 hw
  have hexl : ∀ z, (e z).left = (u.ex z).left ≫ pullback.fst G.hom y := fun z => by
    rw [hex]
    exact (GlobalTheory.OrthoMetric.liftPt_comp hp (e z)).symm
  refine ⟨Hm, EF, hF.1, fun z hz => hpos z hz, fun x x' => (hN x x').trans (by rw [hEF]), ?_⟩
  intro k a b c hk hc
  have hw := GlobalTheory.AHWeilAny.weilIs_exp_riemannForm _ hA _ hLA g u Hm χ hAH k (P a) (P b) c hk (hmem a) (hmem b)
    (by rw [hc, hN a b, hEF, Complex.ofReal_intCast])
  exact tr y (Category.id_comp y) k _ _ _ _ _ (hexl _) (hexl _) hw

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveRiemannFormOfRelAmpleExponentialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_positiveRiemannForm_of_relAmple_exponential : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (L : LB G.left), L.IsLB → Out.RelAmple G L → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (La : Type) [AddCommGroup La] (P : La →+ (Fin g → ℂ)), IsExp y e → Function.Injective P → (∀ z, e z = 1 ↔ z ∈ P.range) → ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La), Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ (∀ x x', (hermForm Hm (P x) (P x')).im = EF x x') ∧ (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs G L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) := by
  first | exact @GlobalTheory.exists_riemannForm_of_relAmple | exact GlobalTheory.exists_riemannForm_of_relAmple | (intros; apply GlobalTheory.exists_riemannForm_of_relAmple <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpEvenOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.PrimCube

open GlobalTheory.PrimNorm GlobalTheory.MulPull

theorem evenOn_of_prim : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (P : GlobalTheory.UU.CP G) (a : G ⟶ G), IsMonHom a → LBIso P.L.L (cubeLB G ![𝟙 G, a] P.L.L) → EvenOn P := by
  intro R _ _ _ hR D A G _ _ hS U P a ha hw
  have hp : IsProper (pullback.snd G.hom (jK R)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK R) = U.gen.hom.left ≫ A.A.hom := (Over.w U.gen.hom).symm
    have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper U.gen.hom.left A.A.hom inferInstance A.isAb.proper
  have hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  let Q₀ := GlobalTheory.Mum.tqOfGtCoord (U.gt 0) hB
  obtain ⟨P₀, v, hv⟩ := GlobalTheory.UU.exists_isLevelCP (maximalIdeal R) 0 P
  have hm : (maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI : Field (R ⧸ maximalIdeal R ^ (0 + 1)) := Ideal.Quotient.field _
  have hS0 := IsSemiAbelian.pullback (thick R (maximalIdeal R) 0) G hS
  have := hS0.smooth
  have := hS0.geomConnected
  have := Q₀.i_hom
  letI := D.toPre.addX
  haveI := D.toPre.freeX
  haveI := D.toPre.finX
  obtain ⟨s⟩ := GlobalTheory.BiextTriv.main (R ⧸ maximalIdeal R ^ (0 + 1)) D.toPre.X (thickObj R (maximalIdeal R) 0 G) P₀.L P₀.c Q₀.i
    Q₀.i_hom
  obtain ⟨σ, hσ⟩ := GlobalTheory.EvenTriv.exists_even_of_surjective (GlobalTheory.EvenTriv.surjective_cube_of_generic G hS hp) P a hw P₀
    (IsPullback.of_hasPullback G.hom (thick R (maximalIdeal R) 0)) hv Q₀.i s
  exact ⟨D.toPre.X, D.toPre.addX, D.toPre.freeX, D.toPre.finX, Q₀, P₀, ⟨v, hv⟩, σ, hσ⟩

theorem exists_cp_evenOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, w + star w = 1 → TraceFormTwistIso D.toPre o w → ∃ P : GlobalTheory.UU.CP G, LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) ∧ EvenOn P := by
  intro R _ _ _ hR D A G _ _ hS U O _ _ _ o oA oG hlin w hw _
  obtain ⟨hno, -, hic, -⟩ := hR.1
  have ha := oG.hom w
  have hb := oG.hom (star w)
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hgh := U.gen_hom
  have hp : IsProper (pullback.snd G.hom (jK R)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK R) = U.gen.hom.left ≫ A.A.hom := (Over.w U.gen.hom).symm
    have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper U.gen.hom.left A.A.hom inferInstance A.isAb.proper
  have hM := U.LG.isLB
  have hT : ∃ t : LB.Gen (Theta G U.LG.L), t.IsGen := ⟨U.cubG.t, U.cubG.isGen⟩
  have hadd : oG.act w * oG.act (star w) = 𝟙 G := by
    have e := oG.map_add w (star w)
    rw [hw, oG.map_one] at e
    exact (e.trans rfl).symm
  have hadj := GlobalTheory.T.uniformisation_ringAction_adjoint_cubeBundle R hR.1 D A G hS U O o oA oG hlin w
  have hc := fun T : Over (Sp R) => diff₃_ptCls (T := T) hM hT
  have hq : ∀ T : Over (Sp R), (fun x : T ⟶ G => normCls U.LG.L (oG.act w) x.left) =
      fun x => diff₂ (ptCls U.LG.L T) x (postHom (oG.act w) T x) := fun T => funext fun x => normCls_left _ x
  have hs : ∀ (T : Over (Sp R)) (y : T ⟶ G), postHom (oG.act w) T y * postHom (oG.act (star w)) T y = y :=
    fun T y => (MonObj.comp_mul y _ _).symm.trans (by rw [hadd, Category.comp_id])
  have hadj' : ∀ (T : Over (Sp R)) (x y : T ⟶ G), diff₂ (ptCls U.LG.L T) (postHom (oG.act w) T x) y =
      diff₂ (ptCls U.LG.L T) x (postHom (oG.act (star w)) T y) := fun T x y => diff₂_ptCls_adj hM hadj x y
  have iso : ∀ (T : Over (Sp R)) (x y : T ⟶ G),
      LBIso (cubeLB G ![x, y] (cubeLB G ![𝟙 G, oG.act w] U.LG.L)) (cubeLB G ![x, y] U.LG.L) := fun T x y => by
    refine lbIso_nested hM _ _ _ _ _ _ ((prod_square_id x y (normCls U.LG.L (oG.act w))).trans
      (Eq.trans ?_ (prod_square_id x y (cls U.LG.L)).symm))
    rw [hq]
    exact diff₂_quadratic (hc T) _ _ (hs _) (hadj' _) x y
  have symN : HasGen (cubeLB G ![𝟙 G, oG.act w] U.LG.L) (K := Fin 2) ![(GrpObj.inv (X := G)).left, 𝟙 _] ![1, -1] := by
    refine hasGen_nested hM _ _ _ _ ?_
    rw [Fin.prod_univ_two]
    show normCls U.LG.L (oG.act w) (GrpObj.inv (X := G)).left ^ (1 : ℤ) *
      normCls U.LG.L (oG.act w) (𝟙 G : G ⟶ G).left ^ (-1 : ℤ) = 1
    have e : GrpObj.inv (X := G) = (𝟙 G)⁻¹ := by simp [Hom.inv_def]
    have e' : (𝟙 G)⁻¹ ≫ oG.act w = (𝟙 G ≫ oG.act w)⁻¹ := map_inv (postHom (oG.act w) G) _
    rw [normCls_left, normCls_left, e, e', diff₂_inv_inv (hc G), zpow_neg, mul_inv_cancel]
  have hN := GlobalTheory.LamCalc.cubeLB_isLB hM ![𝟙 G, oG.act w]
  obtain ⟨L', c', hL'⟩ := GlobalTheory.RigCube.exists_rigLB_cubicalStr R G hS hp _ hN
  have hsym : L'.IsSymmetric := isSymmetric_of_hasGen L' (hL' ▸ symN)
  obtain ⟨P, hP, -⟩ := GlobalTheory.UU.exists_cp_of_isSymmetric hL R A G hS U.gen hgh L' c' hsym
  have hPN : P.L.L = cubeLB G ![𝟙 G, oG.act w] U.LG.L := by rw [hP, hL']
  refine ⟨P, hPN ▸ GlobalTheory.PolBaseChange.lbIso_refl P.L.isLB, evenOn_of_prim R hR D A G hS U P (oG.act w) ha ?_⟩
  rw [hPN]
  exact (iso G (𝟙 G) (oG.act w)).symm

end GlobalTheory.Mum.PrimCube
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialPrimitiveU
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialPrimitiveU
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem symTup_unit_of_prim : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsIntegrallyClosed V] [Field K] (io : FractionRing V →+* K) (N : ℕ) (c : Fin N → K) (e : Fin N → FractionRing V), Prim (io.comp (algebraMap V (FractionRing V))) c → (∀ j, io (e j) = symTup c j) → ∃ e' : Fin N → V, (∀ j, algebraMap V (FractionRing V) (e' j) = e j) ∧ ∃ j, IsUnit (e' j) := by
  intro V K _ _ _ _ _ io N c e hP he
  set i := io.comp (algebraMap V (FractionRing V)) with hi
  have hio : Function.Injective io := io.injective
  have hinj : Function.Injective i := hio.comp (IsFractionRing.injective V (FractionRing V))
  letI : Algebra V K := i.toAlgebra
  have hcI : ∀ a, IsIntegral V (c a) := hP.1
  have hsI : ∀ j, IsIntegral V (symTup c j) := by
    intro j
    have : symTup c j ∈ integralClosure V K := by
      unfold symTup
      refine Subalgebra.pow_mem _ ?_ _
      rw [Finset.esymm_map_val]
      exact Subalgebra.sum_mem _ fun t _ => Subalgebra.prod_mem _ fun b _ => hcI b
    exact this
  let φ : FractionRing V →ₐ[V] K := { io with commutes' := fun r => rfl }
  have heI : ∀ j, IsIntegral V (e j) := fun j =>
    (isIntegral_algHom_iff φ hio).1 (by rw [show φ (e j) = io (e j) from rfl, he j]; exact hsI j)
  choose e' he' using fun j => IsIntegrallyClosed.isIntegral_iff.1 (heI j)
  refine ⟨e', he', ?_⟩
  obtain ⟨a₀, hc0, hinv⟩ := hP.2
  obtain ⟨W, hle⟩ := (LocalSubring.range i).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.1 hle
  have memW : ∀ x : K, i.IsIntegralElem x → x ∈ W := by
    intro x ⟨p, hp, hx⟩
    have : IsIntegral W x := by
      let g : V →+* W := i.codRestrict W (fun v => hle ⟨v, rfl⟩)
      refine ⟨p.map g, hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]; exact hx
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    rw [← hy]; exact y.2
  have hcW : ∀ a, c a ∈ W := fun a => memW _ (hP.1 a)
  have hc0W : (c a₀)⁻¹ ∈ W := memW _ hinv
  let y : Fin N → W := fun a => ⟨c a * (c a₀)⁻¹, mul_mem (hcW a) hc0W⟩
  have hy0 : y a₀ = 1 := Subtype.ext (mul_inv_cancel₀ hc0)
  obtain ⟨k, hk1, hkN, hu⟩ := GlobalTheory.exists_isUnit_esymm_of_eq_one W (Fin N) y a₀ hy0
  rw [Fintype.card_fin] at hkN
  set E := (Finset.univ.val.map y).esymm k with hE
  let u0 : W := ⟨c a₀, hcW a₀⟩
  have hu0 : IsUnit u0 := isUnit_iff_exists_inv.2 ⟨⟨(c a₀)⁻¹, hc0W⟩, Subtype.ext (mul_inv_cancel₀ hc0)⟩
  let Z : W := (u0 ^ k * E) ^ (N.factorial / k)
  have hZ : IsUnit Z := ((hu0.pow k).mul hu).pow _
  let j : Fin N := ⟨k - 1, by omega⟩
  have hjk : (j : ℕ) + 1 = k := by simp only [j]; omega
  have hZj : (Z : K) = i (e' j) := by
    have : i (e' j) = io (e j) := by rw [hi, RingHom.comp_apply, he' j]
    rw [this, he j]
    simp only [Z, symTup, hjk, hE, Finset.esymm_map_val]
    push_cast
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(Finset.mem_powersetCard.1 ht).2.symm, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    simp only [y, u0]
    field_simp
  refine ⟨j, ?_⟩
  have hmem : i (e' j) ∈ (LocalSubring.range i).toSubring := ⟨e' j, rfl⟩
  have h1 : IsUnit (Subring.inclusion hle ⟨i (e' j), hmem⟩) := by
    have h0 : Subring.inclusion hle ⟨i (e' j), hmem⟩ = Z := by apply Subtype.ext; exact hZj.symm
    rw [h0]; exact hZ
  obtain ⟨u, hu'⟩ := hloc.map_nonunit _ h1
  obtain ⟨w, hw⟩ := ((u⁻¹ : Units _) : (LocalSubring.range i).toSubring).2
  refine isUnit_iff_exists_inv.2 ⟨w, hinj ?_⟩
  have h3 : ((u : (LocalSubring.range i).toSubring) : K) * (((u⁻¹ : Units _) : (LocalSubring.range i).toSubring) : K) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  rw [map_mul, map_one, hw, ← h3, hu']

end GlobalTheory.UMin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialPrimitiveUStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_primitive_unit : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsIntegrallyClosed V] [Field K] (io : FractionRing V →+* K) (N : ℕ) (c : Fin N → K) (e : Fin N → FractionRing V), Prim (io.comp (algebraMap V (FractionRing V))) c → (∀ j, io (e j) = symTup c j) → ∃ e' : Fin N → V, (∀ j, algebraMap V (FractionRing V) (e' j) = e j) ∧ ∃ j, IsUnit (e' j) := by
  first | exact @GlobalTheory.UMin.symTup_unit_of_prim | exact GlobalTheory.UMin.symTup_unit_of_prim | (intros; apply GlobalTheory.UMin.symTup_unit_of_prim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedEighthPowerEndomorphismActsByIntMatri
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedEighthPowerEndomorphismActsByIntMatri
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.EndCompat

def preH {S : Scheme.{0}} {T T' G : Over S} [GrpObj G] (w : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) :=
  MonoidHom.mk' (w ≫ ·) fun a b => MonObj.comp_mul w a b

def postH {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) (hf : IsMonHom f) :
    (T ⟶ G) →* (T ⟶ H) :=
  haveI := hf
  MonoidHom.mk' (· ≫ f) fun a b => MonObj.mul_comp a b f

def pullH {S S' : Scheme.{0}} (f : S' ⟶ S) (T G : Over S) [GrpObj G] :
    (T ⟶ G) →* ((Over.pullback f).obj T ⟶ (Over.pullback f).obj G) where
  toFun := (Over.pullback f).map
  map_one' := by simp
  map_mul' a b := Functor.map_mul _ a b

theorem map_ofFn_prod {M N : Type} [Group M] [Group N] (f : M →* N) (x : Fin 8 → M) (k : Fin 8 → ℤ) :
    f (List.ofFn fun v => x v ^ k v).prod = (List.ofFn fun v => f (x v) ^ k v).prod := by
  rw [map_list_prod, List.map_ofFn]
  simp [Function.comp_def, map_zpow]

theorem aG_comp_eq_prod : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (E : EndU U.toUnifPre), (∀ u, E.aA ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∀ u, E.aG ≫ q u = (List.ofFn fun v => q v ^ a u v).prod := by
  intro g n o _ ζ F V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ y α hG₀ hα P c φc hφc pr hpr G _ _ hG D U q hq hqc a E hE u
  haveI : IsNoetherianRing V₁ := hCN.1
  haveI : IsIntegrallyClosed V₁ := hCN.2.1
  haveI := E.homG
  haveI := hq u
  haveI := U₀.gen_hom
  have hR : IsMonHom (List.ofFn fun v => q v ^ a u v).prod := by
    refine isMonHom_of_mul _ fun T x z => ?_
    have key : ∀ w : T ⟶ G, w ≫ (List.ofFn fun v => q v ^ a u v).prod = ∏ v, (w ≫ q v) ^ a u v := fun w => by
      rw [← List.prod_ofFn]
      exact map_ofFn_prod (preH w) q (a u)
    rw [key, key, key, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    haveI := hq v
    rw [MonObj.mul_comp, mul_zpow]
  obtain ⟨F0, -, huniq⟩ := GlobalTheory.semiAbelianHomExtension_holds.fractionField V₁ (FractionRing V₁) G G₀ hG hG₀
    ((Over.pullback (jK V₁)).map (E.aG ≫ q u))
  refine (huniq _ ⟨inferInstance, rfl⟩).trans (huniq _ ⟨hR, ?_⟩).symm
  rw [← cancel_mono U₀.gen.hom]
  apply Over.OverMorphism.ext
  refine hα.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)
  have hv : ∀ v, pushHom hα ((Over.pullback (jK V₁)).obj G) ((Over.pullback (jK V₁)).map (q v) ≫ U₀.gen.hom) =
      pushHom hφc ((Over.pullback (jK V₁)).obj G) (U.gen.hom ≫ pr v) :=
    fun v => Over.OverMorphism.ext (hqc v)
  have e₁ : ((Over.pullback (jK V₁)).map (List.ofFn fun v => q v ^ a u v).prod ≫ U₀.gen.hom).left ≫ α =
      (List.ofFn fun v => pushHom hφc ((Over.pullback (jK V₁)).obj G) (U.gen.hom ≫ pr v) ^ a u v).prod.left := by
    have := map_ofFn_prod ((pushHom hα ((Over.pullback (jK V₁)).obj G)).comp
      ((postH U₀.gen.hom U₀.gen_hom).comp (pullH (jK V₁) G G₀))) q (a u)
    refine (congrArg (fun z => z.left) this).trans ?_
    refine congrArg (fun z => Over.Hom.left (List.ofFn z).prod) (funext fun v => ?_)
    rw [← hv v]
    rfl
  have e₂ : ((Over.pullback (jK V₁)).map (E.aG ≫ q u) ≫ U₀.gen.hom).left ≫ α =
      (List.ofFn fun v => pushHom hφc ((Over.pullback (jK V₁)).obj G) (U.gen.hom ≫ pr v) ^ a u v).prod.left := by
    have h1 : ((Over.pullback (jK V₁)).map (E.aG ≫ q u) ≫ U₀.gen.hom).left ≫ α =
        (U.gen.hom ≫ (List.ofFn fun v => pr v ^ a u v).prod).left ≫ φc := by
      rw [Functor.map_comp, Category.assoc, Over.comp_left, Category.assoc, hqc u, ← Category.assoc,
        ← Over.comp_left, ← Category.assoc, E.ext, Category.assoc, hE u]
    have h2 := map_ofFn_prod ((pushHom hφc ((Over.pullback (jK V₁)).obj G)).comp (preH U.gen.hom)) pr (a u)
    exact h1.trans (congrArg (fun z => z.left) h2)
  exact e₁.trans e₂.symm

end GlobalTheory.Poinc.Sep.EndCompat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedEighthPowerEndomorphismActsByIntMatriStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedEighthPower_endomorphism_acts_by_intMatrix : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (E : EndU U.toUnifPre), (∀ u, E.aA ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∀ u, E.aG ≫ q u = (List.ofFn fun v => q v ^ a u v).prod := by
  first | exact @GlobalTheory.Poinc.Sep.EndCompat.aG_comp_eq_prod | exact GlobalTheory.Poinc.Sep.EndCompat.aG_comp_eq_prod | (intros; apply GlobalTheory.Poinc.Sep.EndCompat.aG_comp_eq_prod <;> assumption)
end
end
