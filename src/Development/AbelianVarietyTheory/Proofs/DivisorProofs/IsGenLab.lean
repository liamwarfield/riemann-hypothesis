module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisedFibrewiseNonvanishingSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabiliserFixesVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBoxTensorLeftFixedLinearApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountingVolumeLeSelfIntersectionNefHermitianBund
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesO1OfProjectiveRankCup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.ZH

namespace GlobalTheory.UPoinc.USum

def IsTwVal {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A}
    (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀)
    (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) : Prop :=
  ∃ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]))
    (U : ThetaGrp P.A P.L N T), α.IsGen ∧ SymLift P.A P.L N N x U ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Good P.L z J →
      gs r z ⊤ v * (val α (r ≫ (ptSecT P.A h).left) z J * val τ (r ≫ β.left) z J).val =
        (GlobalTheory.CommPairing.tval U (r ≫ (ptSecT P.A h).left) z J * val α (r ≫ (ptSecT P.A (x * h)).left) z J).val *
          sval (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => 1) θ
            (r ≫ (ptSecT P.A ((x * h) ^ m)).left ≫ (β ▷ P.A).left) z J

def wtChar {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (T : AddSubgroup S.Gam) (a : S.Gam) :
    T →+ ZMod S.N where
  toFun t := ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ (t : S.Gam) a)
  map_zero' := by simp [eStd]
  map_add' := by
    intro s t
    rw [← map_add (f := _)]
    congr 1
    simp only [eStd, AddSubgroup.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

abbrev genPt {R K : Type} [CommRing R] [CommRing K] (ψ : R →+* K) : Over (Sp R) := Over.mk (spMap ψ)

def genTo {R K : Type} [CommRing R] [CommRing K] (ψ : R →+* K) : genPt ψ ⟶ baseOver (Sp R) :=
  Over.homMk (spMap ψ) (Category.comp_id _)

def IsGenLab {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} (ρ : S.Real) (ρ' : S'.Real) (lab : S.Gam → S'.Gam) (φ : Ω →+* Ω')
    (P₀ : PolAV (Sp Ω')) (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ ρ'.P.A.left)
    (x : S'.Gam → (genPt (φ.comp S.R.val.toRingHom) ⟶ ρ.P.A)) : Prop :=
  IsGrpPullback P₀.A ρ.P.A (spMap (φ.comp S.R.val.toRingHom)) a ∧ IsGrpPullback P₀.A ρ'.P.A (spMap S'.R.val.toRingHom) a' ∧
    LBIso P₀.L (ρ.P.L.pull a) ∧ LBIso P₀.L (ρ'.P.L.pull a') ∧
    (∀ b, ∃ w : Sp Ω' ⟶ P₀.A.left, w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = (x b).left ∧
      w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt b).left) ∧
    ∀ k, x (lab k) = genTo _ ≫ ρ.pt k

end GlobalTheory.UPoinc.USum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreExponentialKernelFullLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreExponentialKernelFullLattice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.ExpKernel

theorem fderiv_apply_eq_zero {g : ℕ} (h : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) (hc : ∀ t : ℂ, h (t • w) = h 0) :
    fderiv ℂ h 0 w = 0 := by
  by_cases hd : DifferentiableAt ℂ h 0
  · have hl : HasFDerivAt (fun t : ℂ => t • w) ((ContinuousLinearMap.id ℂ ℂ).smulRight w) 0 :=
      ((ContinuousLinearMap.id ℂ ℂ).smulRight w).hasFDerivAt
    have h0 : HasFDerivAt h (fderiv ℂ h 0) ((0 : ℂ) • w) := by rw [zero_smul]; exact hd.hasFDerivAt
    have h1 := h0.comp (0 : ℂ) hl
    have h2 : HasFDerivAt (fun t : ℂ => h (t • w)) (0 : ℂ →L[ℂ] ℂ) 0 := by
      simp only [hc]; exact hasFDerivAt_const _ _
    have := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) (h1.unique h2)
    simpa using this
  · rw [fderiv_zero_of_not_differentiableAt hd]; rfl

theorem kernel_isFullLattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G →
    SmoothOfRelativeDimension g G.hom → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsExp y e →
    ∃ Λ : Submodule ℤ (Fin g → ℂ), DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧
      ∀ z, e z = 1 ↔ z ∈ Λ := by
  intro X G _ _ g hG hg y e he
  obtain ⟨hadd, hsurj, hhol, hd1, hd2⟩ := he
  let A : Over (Sp ℂ) := (Over.pullback y).obj G
  letI : GrpObj A := Functor.grpObjObj
  let φ : A.left ⟶ G.left := pullback.fst G.hom y
  have hp : IsGrpPullback A G y φ := isGrpPullback_pullback G y
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hp
  have hgA : SmoothOfRelativeDimension g A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hp.1 hg
  obtain ⟨L, ⟨u⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A g hA hgA
  obtain ⟨ht₁, ht₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u hgA
  have inj : ∀ x x' : 𝟙_ (Over (Sp ℂ)) ⟶ A, x.left ≫ φ = x'.left ≫ φ → x = x' := fun x x' h =>
    Over.OverMorphism.ext (hp.1.hom_ext h (by rw [Over.w x, Over.w x']))
  have lift : ∀ x₀ : Over.mk y ⟶ G, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x.left ≫ φ = x₀.left := fun x₀ =>
    ⟨Over.homMk (hp.1.lift x₀.left (𝟙 _) ((Over.w x₀).trans (Category.id_comp _).symm)) (hp.1.lift_snd _ _ _),
      hp.1.lift_fst _ _ _⟩
  choose Φ hΦ using lift
  have Φmul : ∀ x x', Φ (x * x') = Φ x * Φ x' := fun x x' => inj _ _ (by
    rw [hΦ, ← hp.2 _ (Φ x) (Φ x') (pushPt hp.1.w (Φ x)) (pushPt hp.1.w (Φ x')) rfl rfl]
    exact mul_left_congr (Category.id_comp _).symm _ _ _ _ (hΦ x).symm (hΦ x').symm)
  have Φinj : Function.Injective Φ := fun x x' h => Over.OverMorphism.ext (by rw [← hΦ, ← hΦ, h])
  have Φone : Φ 1 = 1 := by
    have := Φmul 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (Φ (e z)).left) :=
    FibreUnif.isHolTo_of_isPullback hp.1 (e := fun z => (Φ (e z)).left) (fun z => Over.w (Φ (e z)))
      (by simpa only [hΦ] using hhol)
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA L g g u ht₁ ht₂ (fun z => Φ (e z))
    (fun z z' => by rw [hadd, Φmul]) hol
  have Finj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun w hw => by
    have hconst : ∀ t : ℂ, e (t • w) = e 0 := fun t => Φinj (by
      rw [← hF, ← hF, map_smul, hw, smul_zero, map_zero])
    have hiff : ∀ v, IsDerivAt0 (fun z => (e z).left) w v ↔ IsDerivAt0 (fun z => (e z).left) 0 v := by
      intro v
      unfold IsDerivAt0
      refine and_congr_right fun _ => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => ?_
      rw [map_zero, fderiv_apply_eq_zero _ w (fun t => by simp only [hconst t, zero_smul])]
    obtain ⟨v, hv, -⟩ := hd1 w
    exact (hd2 v hv.1).unique hv ((hiff _).1 hv)
  let F' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofInjectiveEndo F Finj
  have hF' : ∀ z, F' z = F z := fun _ => rfl
  have hker : ∀ z, e z = 1 ↔ F z ∈ u.Λ := fun z => by
    rw [← u.ker, hF, ← Φone, Φinj.eq_iff]
  let Λ : Submodule ℤ (Fin g → ℂ) := u.Λ.comap F.toAddMonoidHom.toIntLinearMap
  have hmem : ∀ z, z ∈ Λ ↔ F z ∈ u.Λ := fun _ => Iff.rfl
  refine ⟨Λ, ?_, ?_, fun z => (hker z).trans (hmem z).symm⟩
  · have := u.discrete
    let c : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) := F'.toContinuousLinearEquiv
    let f : Λ → u.Λ := fun x => ⟨F x, (hmem x).1 x.2⟩
    have hcomp : (Subtype.val ∘ f) = c ∘ (Subtype.val : Λ → Fin g → ℂ) := rfl
    have hemb : Topology.IsEmbedding f := by
      rw [← Topology.IsEmbedding.subtypeVal.of_comp_iff, hcomp]
      exact c.toHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    exact hemb.discreteTopology
  · let Fr : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := F'.restrictScalars ℝ
    have hset : (Λ : Set (Fin g → ℂ)) = Fr.symm '' (u.Λ : Set (Fin g → ℂ)) := by
      rw [LinearEquiv.image_symm_eq_preimage]
      ext z
      exact hmem z
    rw [hset, ← LinearEquiv.coe_coe, Submodule.span_image, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact Fr.symm.surjective

end GlobalTheory.ExpKernel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreExponentialKernelFullLatticeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexFibreExponential_kernel_full_lattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsExp y e → ∃ Λ : Submodule ℤ (Fin g → ℂ), DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ z, e z = 1 ↔ z ∈ Λ := by
  first | exact @GlobalTheory.ExpKernel.kernel_isFullLattice | exact GlobalTheory.ExpKernel.kernel_isFullLattice | (intros; apply GlobalTheory.ExpKernel.kernel_isFullLattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationCompleteLocalEvenOnTorus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationCompleteLocalEvenOnTorus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.UnifEven

open GlobalTheory.UU GlobalTheory.LN

theorem isAdmissible_maximalIdeal_of_completeNormalCharZero {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) : admitted R (maximalIdeal R) := by
  refine ⟨hB.1, hB.1.2.2.2, hB.2, (maximalIdeal.isMaximal R).isPrime, ?_⟩
  letI := Ideal.Quotient.field (maximalIdeal R)
  infer_instance


set_option maxHeartbeats 1600000 in
theorem exists_setting {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (P : CP G) (hS : IsSemiAbelian G)
    (hE : EvenOn P) (A : PolAV (Sp (FractionRing R)))
    (gen : (Over.pullback (jK R)).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))))
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) (g : R →+* V) (hg : Function.Injective g)
    (hc : (maximalIdeal V).comap g = maximalIdeal R) :
    ∃ (A' : PolAV (Sp (FractionRing V))) (s : HidaSetting V A' ((Over.pullback (spMap g)).obj G)) (w : _),
      IsCPMap s.P P (spMap g) (pullback.fst G.hom (spMap g)) pullback.condition w := by
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.lawsAndExpansions.1
  obtain ⟨X, _, _, _, Q₀, P₀, ⟨wl, hl⟩, hev⟩ := hE
  have := hS.smooth
  have := hS.geomConnected
  have := GlobalTheory.PreUnifLocal.isLocalRing_quot (maximalIdeal.isMaximal R).ne_top 0
  have hsm : Smooth (thickObj R (maximalIdeal R) 0 G).hom := by
    show Smooth (pullback.snd _ _); infer_instance
  have hgc : GeometricallyConnected (thickObj R (maximalIdeal R) 0 G).hom := by
    show GeometricallyConnected (pullback.snd _ _); infer_instance
  obtain ⟨D₀⟩ := TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max 0) _ P₀ Q₀ hev
  let G' : Over (Sp V) := (Over.pullback (spMap g)).obj G
  have hS' : IsSemiAbelian G' := IsSemiAbelian.pullback _ G hS
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap g) G G' _ _ (toBase_mul_pullback G (spMap g)) P

  obtain ⟨ψ, sq'⟩ := ClosedPol.exists_generic_square g hg
  obtain ⟨A', gen', hgen', hA'⟩ := ClosedPol.exists_fibre_pull hL sq' P.L.isLB A gen hA
  rw [← hP'] at hA'
  obtain ⟨wA, hwA⟩ := hA'

  have le : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal V ^ (0 + 1)).comap g := by
    rw [zero_add, pow_one, pow_one, hc]
  let b : R ⧸ maximalIdeal R ^ (0 + 1) →+* V ⧸ maximalIdeal V ^ (0 + 1) :=
    Ideal.quotientMap (maximalIdeal V ^ (0 + 1)) g le
  have sq : spMap b ≫ thick R (maximalIdeal R) 0 = thick V (maximalIdeal V) 0 ≫ spMap g := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]
  obtain ⟨P₁, w₁, H₁⟩ := exists_isLevelCP (maximalIdeal V) 0 P'
  obtain ⟨F, pF, w₃, k₃⟩ := ClosedPol.exists_fourth (G := G) (G' := G') (H := thickObj R (maximalIdeal R) 0 G)
    (H' := thickObj V (maximalIdeal V) 0 G') (P := P) (P' := P') (N := P₀) (N' := P₁) sq
    (isGrpPullback_pullback G (spMap g)) (isGrpPullback_pullback G (thick R (maximalIdeal R) 0))
    (isGrpPullback_pullback _ (thick V (maximalIdeal V) 0)) H hl H₁
  obtain ⟨Q₁, D₁, -, -, -⟩ := ClosedPol.exists_desc_pull pF Q₀ D₀ k₃
  have ev := GlobalTheory.UniformizationSetting.exists_even_of_desc D₁
  exact ⟨A', ⟨hV, hS', gen', hgen', P', wA, hwA, X, Q₁, P₁, ⟨w₁, H₁⟩, ev⟩, wP, H⟩

end GlobalTheory.Mum.UnifEven


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Mum.exists_unif_even : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → EvenOn P → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegData R (maximalIdeal R)) (U : Unif (maximalIdeal R) D A G), U.LG = P.L ∧ U.gen = gen := by
  intro R _ _ _ hB G _ _ P hS hEv A gen hgen hA
  obtain ⟨⟨hL, hL2, hL3, -, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hE := GlobalTheory.LN.ega_holds
  have hU := GlobalTheory.uniformisation_dvr_unconditional
  have hR := GlobalTheory.Mum.UnifEven.isAdmissible_maximalIdeal_of_completeNormalCharZero hB
  have := hR.1.1
  have := hR.2.2.1
  have hI := hR.2.2.2.1
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R (maximalIdeal R)
  have := hV.1
  have hB' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hle : (maximalIdeal R).map φ ≤ maximalIdeal V := Ideal.map_le_iff_le_comap.2 hc.ge
  obtain ⟨D, U, rfl, rfl⟩ := GlobalTheory.T.exists_preUniformisation_even_torus_completeNormal R hB G P hS hEv A gen hgen hA
  have hθ := GlobalTheory.T.preUniformised_fibrewise_nonvanishing_section R hB D A G U hEv
  haveI := hgen
  obtain ⟨A', s, w, hw⟩ := GlobalTheory.Mum.UnifEven.exists_setting U.P hS hEv A U.gen hA hV φ hφ hc
  obtain ⟨D', U₀, hLG, -, -⟩ := hU V A' _ s
  obtain ⟨U', hU'⟩ := (GlobalTheory.LN.PreForm.under_exists_and_expands hL hL2 V _ D' A' _ s.semi).1 U₀.toUnifPre
  have := s.semi.smooth
  obtain ⟨w', hw'⟩ := GlobalTheory.PrimeUnif.isCPMap_of_eq hL.globalFns s.gen s.P U'.P (hU'.2.1.trans hLG) hw
  obtain ⟨C, -⟩ := GlobalTheory.T.exists_compare_uniformisationData_pullback hL hL2 hE R V (maximalIdeal R) _ hR.1 hB' (maximalIdeal.isMaximal V).ne_top φ hle D _
    A A' G _ U U' _ (isGrpPullback_pullback G _) w' hw'
  obtain ⟨psi, h, Dd, hD, e, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_degData_psi_of_section_nonzero_fibres hL hL2 hE R (maximalIdeal R) hR V hV φ hφ hc D D' A A' G _
    U U' U₀ _ C hU' hθ
  obtain ⟨U₂, C₂, hD₂, eP, eg, k₁, k₂, k₃⟩ := GlobalTheory.PrimeUnif.exists_move psi h C hD Dd.toPre e h₁ h₂ h₃
  obtain ⟨U₁, -, hU₁, -⟩ := GlobalTheory.UnifDescent.exists_unif_of_cmp hL hL2 hE R V (maximalIdeal R) _ hR.1 hB' hI.ne_top φ hφ
    hle Dd D' A A' G _ U₂ U' U₀ _ C₂ hD₂ hU' k₁ k₂ k₃
  exact ⟨Dd, U₁, hU₁.2.1.symm.trans (congrArg GlobalTheory.UU.CP.L eP), hU₁.1.symm.trans eg⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationCompleteLocalEvenOnTorusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → EvenOn P → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegData R (maximalIdeal R)) (U : Unif (maximalIdeal R) D A G), U.LG = P.L ∧ U.gen = gen := by
  first | exact @GlobalTheory.Mum.exists_unif_even | exact GlobalTheory.Mum.exists_unif_even | (intros; apply GlobalTheory.Mum.exists_unif_even <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBothStabilisersFixVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStabiliserVacuumEigenvalueOneInertPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStabiliserVacuumEigenvalueOneInertPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVacV

theorem eigen_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ c : ℂ, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv k hk c hc
  obtain ⟨d', hd', -, dd, omd, hdc, hsp, hbox⟩ := hT.weil.2.1
  have hvac := hT.geo.hM.vac v
  obtain ⟨r, hr, hr0⟩ := GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero _ v (G.M.vac v) hvac.1 hvac.2.1
  set V₀ := tens (evFin F v) (G.M.vac v) r with hV₀
  set S := boxFun V₀ (fun x => star (V₀ x)) with hS
  have hS0 : ∃ x, S x ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hr0
    refine ⟨Sum.elim x x, ?_⟩
    simp only [hS, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at hx ⊢
    exact mul_ne_zero hx (star_ne_zero.mpr hx)
  let H : Subgroup (GlobalTheory.DblVac.UD σ G.V) :=
    { carrier := {g | omd g S = S}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hD : ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H := fun p hp hpd => by
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.doubledVacuum_eigen_inertPlace_latticeStabiliser F E σ B a a' G X om om' hT v w hw hv d' hd' dd omd hdc hsp r hr p hp
    have h1 := GlobalTheory.T.doubledVacuum_eigenvalue_eq_one_inertPlace F E σ B a a' G X om om' hT v w hw hv d' hd' dd omd hdc hsp r hr hr0 p hp hpd μ hμ
    show omd p S = S
    rw [hμ, h1, one_smul]
  have hA : ∀ q ∈ GlobalTheory.DblVac.KD σ G.V v, q ∈ GlobalTheory.DblVac.PAnti σ G.V → q ∈ H := fun q hq hqa => by
    obtain ⟨w₀, hw₀, hW⟩ := GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem σ G.V v
    obtain ⟨h1, h2⟩ := hW q hq hqa
    have hq' : omd (w₀ * q * w₀⁻¹) S = S := hD _ h1 h2
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.doubledVacuum_eigen_inertPlace_latticeStabiliser F E σ B a a' G X om om' hT v w hw hv d' hd' dd omd hdc hsp r hr w₀ hw₀
    have hinv : μ • omd w₀⁻¹ S = S := by
      rw [← LinearMap.map_smul, ← hμ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    have e : q = w₀⁻¹ * (w₀ * q * w₀⁻¹) * w₀ := by group
    show omd q S = S
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hμ, LinearMap.map_smul, hq',
      LinearMap.map_smul, hinv]
  obtain ⟨gd, hgd, hgdK⟩ := GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer σ G.V v k hk
  have hfix : omd gd S = S := GlobalTheory.T.doubledStabilizer_generated_antidiag_splitPlace_V F E σ B a a' G X om om' hT v w hw hv H hD hA gd hgdK
  have hb := hbox k gd hgd V₀ hr.2 (fun x => star (V₀ x)) (GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem _ V₀ hr.2)
  have hk1 : (om.comp (MonoidHom.inl _ _)) k V₀ = c • V₀ := by
    rw [MonoidHom.comp_apply, MonoidHom.inl_apply, hV₀, hc r hr]
    funext x
    simp [tens, mul_assoc]
  rw [hk1] at hb
  have hcS : c • S = S := by
    calc c • S = boxFun (c • V₀) (fun x => star (V₀ x)) := by
          funext x
          simp [hS, boxFun, mul_assoc]
      _ = omd gd S := hb.symm
      _ = S := hfix
  obtain ⟨x, hx⟩ := hS0
  have := congrFun hcS x
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hx (this.trans (one_mul _).symm)

end GlobalTheory.DblVacV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStabiliserVacuumEigenvalueOneInertPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabiliser_vacuum_eigenvalue_one_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ c : ℂ, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  first | exact @GlobalTheory.DblVacV.eigen_eq_one | exact GlobalTheory.DblVacV.eigen_eq_one | (intros; apply GlobalTheory.DblVacV.eigen_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBothStabilisersFixVacuum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertSph

theorem vacV_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hvT k hk
  obtain ⟨hSB, hne, θ, hθ, hfix⟩ := hT.geo.hM.vac v
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV_pairVW F E σ B a a' G X om om' hT v k hk.1 _ hSB
  have hfix₁ := GlobalTheory.T.weilOperator_latticeStabiliser_left_preserves_vacuumType F E σ B a a' G X om om' hT v k hk θ hθ _ hSB φ₁ hφ₁ hfix hact
  obtain ⟨c, rfl⟩ := GlobalTheory.T.heisenbergSelfDualLattice_fixedFunctions_line F E σ B a a' G X om om' hT v (hT.base.inert v w hin).2.2
    (GlobalTheory.T.tensorLattice_inertPlace_selfDual F E σ B a a' G X om om' hT v w hin) θ hθ _ hSB hne hfix φ₁ hφ₁ hfix₁
  have hc := GlobalTheory.T.latticeStabiliser_vacuum_eigenvalue_one_inert_place F E σ B a a' G X om om' hT v w hin hvT k hk c hact
  rw [hc, one_smul] at hact
  exact hact

theorem vac_fixed_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ k' ∈ GlobalTheory.InertSph.KAt σ G.W v,
      Acts (evFin F v) (om (k, k')) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hvT k hk k' hk' r hr
  have h1 := vacV_fixed F E σ B a a' G X om om' hT v w hin hvT k hk
  have h2 := GlobalTheory.T.inert_place_lattice_stabiliser_fixes_vacuum F E σ B a a' G X om om' hT v w hin hvT k' hk'
  have e : om (k, k') = om (k, 1) * om (1, k') := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [e, Module.End.mul_apply, h2 r hr, h1 r hr]

end GlobalTheory.InertSph
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBothStabilisersFixVacuumStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_both_stabilisers_fix_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ k' ∈ GlobalTheory.InertSph.KAt σ G.W v,
      Acts (evFin F v) (om (k, k')) (G.M.vac v) (G.M.vac v) := by
  first | exact @GlobalTheory.InertSph.vac_fixed_pair | exact GlobalTheory.InertSph.vac_fixed_pair | (intros; apply GlobalTheory.InertSph.vac_fixed_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaBoundLengthUnit
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

noncomputable section
namespace GlobalTheory.ThetaSizeBounds
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem archimedeanBoundTotalConstant_nonneg_le_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r q m : ℕ) (L : ℝ), 2 ≤ L → 1 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E → 1 ≤ r → 1 ≤ m → m ≤ r → 1 ≤ q → 1 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E → Real.log (ReciprocityTheory.ChartRestriction.G.I2.PT.rd E) ≤ 2 * L → Real.log (ReciprocityTheory.ChartRestriction.G.I2.PT.f E) ≤ 2 * L → Real.log r ≤ L → Real.log q ≤ 70 * L → 0 ≤ GlobalTheory.EtaAn.p16 E r q m 5 1 ∧ GlobalTheory.EtaAn.p16 E r q m 5 1 ≤ 200000 * ((ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * r * L) ^ 2 := by
  intro E _ _ _ r q m L hL hf hr hm hmr hq hρ lρ lF lR lq
  have key := GlobalTheory.EtaAn.archimedeanBoundTotalConstant_size E r q m 1 L hL hf hr hm hmr hq hρ lρ lF lR lq (by simp; positivity)
  have hd : ((ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℕ) : ℝ) = 2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * m := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.dstar; push_cast; ring
  have hfR : (1 : ℝ) ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E := by exact_mod_cast hf
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd2 : (2 : ℝ) ≤ (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) := by rw [hd]; nlinarith
  have hRR : 1 ≤ ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) := by unfold ReciprocityTheory.ChartRestriction.G.I2.RR; exact one_le_pow₀ hρ
  have p3nn : 0 ≤ GlobalTheory.EtaAn.p3 E r q m := by
    unfold GlobalTheory.EtaAn.p3
    have hs := Real.sqrt_nonneg (((ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r : ℕ) : ℝ) * q)
    apply mul_nonneg (Nat.cast_nonneg _)
    have a1 : 0 ≤ Real.log (1 + 6 * Real.sqrt (((ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r : ℕ) : ℝ) * q)) :=
      Real.log_nonneg (by linarith)
    have a2 : 0 ≤ Real.log (2 * (3 * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ)) ^ ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (3 * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ)) ^ ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m :=
        one_le_pow₀ (by linarith)
      linarith
    have a3 : (0 : ℝ) ≤ ((ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r : ℕ) : ℝ) := Nat.cast_nonneg _
    have := mul_nonneg a3 a1
    linarith
  have hN : Real.log ((1 : ℕ) : ℝ) ≤ Real.log (((max 1 1 * 5 ^ (8 * ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r ^ 2) : ℕ)) : ℝ) := by
    rw [Nat.cast_one, Real.log_one]; exact Real.log_natCast_nonneg _
  refine ⟨?_, le_trans ?_ key.2⟩
  · unfold GlobalTheory.EtaAn.p16
    have l5 : 0 ≤ Real.log ((5 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have l1 : Real.log ((1 : ℕ) : ℝ) = 0 := by simp
    have hA : (1 : ℝ) ≤ ((5 : ℕ) : ℝ) ^ 4 * r * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) / 2 := by
      push_cast; nlinarith
    have hB : (1 : ℝ) ≤ 4 * ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) ^ 2 := by nlinarith
    have a5 : 0 ≤ Real.log (((5 : ℕ) : ℝ) ^ 4 * r * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) / 2 *
        (4 * ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) ^ 2)) :=
      Real.log_nonneg (by nlinarith)
    have t1 := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * (r : ℝ) ^ 2) l5
    have t2 := mul_nonneg (by linarith : (0 : ℝ) ≤ ((5 : ℕ) : ℝ) ^ 4 * r * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) / 2) a5
    have t3 := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((5 : ℕ) : ℝ) ^ 4) p3nn
    have h5 : (0 : ℝ) ≤ 2 * ((5 : ℕ) : ℝ) ^ 4 := by positivity
    rw [l1, zero_add]
    exact add_nonneg (mul_nonneg h5 (add_nonneg p3nn t1)) t2
  · unfold GlobalTheory.EtaAn.p16
    have h5 : (0 : ℝ) ≤ 2 * ((5 : ℕ) : ℝ) ^ 4 := by positivity
    exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl (add_le_add hN le_rfl)) h5) le_rfl

theorem size_inequality_real : ∀ (rd c t b f r DF g0 g1 : ℝ), 1 ≤ rd → rd ≤ c → c ^ 36 * t ^ 150 ≤ Real.sqrt b → 11 ≤ t → 1 ≤ f → f ≤ t → 1 ≤ r → r ≤ t → 1 ≤ DF → DF ≤ b ^ 2 → b ^ 8 ≤ g0 → b ^ 8 ≤ g1 → (rd ^ 7) ^ 4 * (90 * (f * r + DF)) * DF * r ≤ g0 * g1 := by
  intro rd c t b f r DF g0 g1 hrd hc hC ht hf1 hft hr1 hrt hD1 hDb hg0 hg1
  have ht1 : 1 ≤ t := by linarith
  have hc1 : 1 ≤ c := hrd.trans hc
  have hct : 1 ≤ c ^ 36 * t ^ 150 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hc1) (one_le_pow₀ ht1)
  have hs1 : 1 ≤ Real.sqrt b := hct.trans hC
  have hb0 : 0 ≤ b := by
    by_contra h
    push_neg at h
    rw [Real.sqrt_eq_zero'.2 h.le] at hs1
    linarith
  have hbs := Real.sq_sqrt hb0
  have hb1 : 1 ≤ b := by nlinarith
  have hsb : Real.sqrt b ≤ b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hcb : c ^ 36 * t ^ 150 ≤ b := hC.trans hsb
  have ht7 : t ^ 7 ≤ b := by
    have e1 : t ^ 7 ≤ t ^ 150 := pow_le_pow_right₀ ht1 (by norm_num)
    have e2 : t ^ 150 ≤ c ^ 36 * t ^ 150 := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1)
    linarith
  have hR : (rd ^ 7) ^ 4 ≤ b := by
    have e1 : (rd ^ 7) ^ 4 ≤ c ^ 28 := by rw [← pow_mul]; exact pow_le_pow_left₀ (by linarith) hc 28
    have e2 : c ^ 28 ≤ c ^ 36 := pow_le_pow_right₀ hc1 (by norm_num)
    have e3 : c ^ 36 ≤ c ^ 36 * t ^ 150 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1)
    linarith
  have ht2 : t ^ 2 ≤ t ^ 7 := pow_le_pow_right₀ ht1 (by norm_num)
  have htt : t ≤ t ^ 7 := le_self_pow₀ ht1 (by norm_num)
  have h180 : 180 ≤ b := by
    have : (11 : ℝ) ^ 7 ≤ t ^ 7 := pow_le_pow_left₀ (by norm_num) ht 7
    norm_num at this
    linarith
  have hfr : f * r ≤ b := by nlinarith
  have hrb : r ≤ b := by linarith
  have hY : 90 * (f * r + DF) ≤ 180 * b ^ 2 := by nlinarith
  have hg : b ^ 16 ≤ g0 * g1 := by
    have := mul_le_mul hg0 hg1 (by positivity) (by linarith [one_le_pow₀ (M₀ := ℝ) hb1 (n := 8)])
    rw [← pow_add] at this
    exact this
  have e1 : (rd ^ 7) ^ 4 * (90 * (f * r + DF)) * DF * r ≤ b * (180 * b ^ 2) * b ^ 2 * b := by
    have h0 : 0 ≤ (rd ^ 7) ^ 4 := by positivity
    have := mul_le_mul hR hY (by positivity) (by linarith)
    have := mul_le_mul this hDb (by linarith) (by positivity)
    exact mul_le_mul this hrb (by linarith) (by positivity)
  have e2 : b * (180 * b ^ 2) * b ^ 2 * b = 180 * b ^ 6 := by ring
  have e3 : 180 * b ^ 6 ≤ b ^ 16 := by
    have : b ^ 16 = b ^ 10 * b ^ 6 := by ring
    have h10 : b ≤ b ^ 10 := le_self_pow₀ hb1 (by norm_num)
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

theorem sqrt_lt_th_real (q : ℕ) (M f R0 RR b s : ℝ) (hq : 1 ≤ q) (hb : 0 < b) (hM : (q : ℝ) * b ≤ M)
    (hf : 1 ≤ f) (hR : 1 ≤ R0 ^ 2) (hRR : 1 ≤ RR) (hs : M * s < b) :
    Real.sqrt s < Real.sqrt (f * R0 ^ 2 * RR ^ 3 / q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hRR3 : 1 ≤ RR ^ 3 := one_le_pow₀ hRR
  have h1 : 1 ≤ f * R0 ^ 2 * RR ^ 3 := by
    have := mul_le_mul hf hR zero_le_one (by linarith)
    nlinarith
  have hpos : 0 < f * R0 ^ 2 * RR ^ 3 / q := by positivity
  rcases le_or_gt s 0 with h0 | h0
  · rw [Real.sqrt_eq_zero'.2 h0]; exact Real.sqrt_pos.2 hpos
  · apply Real.sqrt_lt_sqrt h0.le
    rw [lt_div_iff₀ hq0]
    have : (q : ℝ) * b * s ≤ M * s := mul_le_mul_of_nonneg_right hM h0.le
    nlinarith

theorem level_ge {eps : ℝ} {Fm : Formalism.MainNotions.FamP eps} {x : ℝ} {hx : Fm.x1 < x} {ι : Fm.Ix x} (p : Pt Fm x hx ι)
    (i : Fin (Fm.D x ι).R.m) (Y : Cov p i) (hY : GoodCov p i Y) (hL : 1 ≤ (Fm.L x ι).sc.L) :
    (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) * (Fm.L x ι).sc.b ≤ (Y.d.l₂.M : ℝ) := by
  have hM : Y.d.l₂.M = (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 * 15 ^ expL (Fm.L x ι).sc.L := by
    rw [hY.1.lev.1.2.1, hY.1.pd]
    congr 1
    exact p.fw.laws.toLawsM.pins.2.1.1
  have hlog3p : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have he : 3 * (Fm.L x ι).sc.L / Real.log 3 < (expL (Fm.L x ι).sc.L : ℝ) + 1 := Nat.lt_floor_add_one _
  have he' : (Fm.L x ι).sc.L ≤ (expL (Fm.L x ι).sc.L : ℝ) * Real.log 3 := by
    rw [div_lt_iff₀ hlog3p] at he
    nlinarith
  have hb : (Fm.L x ι).sc.b ≤ (15 : ℝ) ^ expL (Fm.L x ι).sc.L := by
    unfold Formalism.BasicNotions.Scale.b
    calc Real.exp (Fm.L x ι).sc.L ≤ Real.exp ((expL (Fm.L x ι).sc.L : ℝ) * Real.log 3) := Real.exp_le_exp.2 he'
      _ = (3 : ℝ) ^ expL (Fm.L x ι).sc.L := by
        rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]
      _ ≤ (15 : ℝ) ^ expL (Fm.L x ι).sc.L := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  rw [hM]
  push_cast
  exact mul_le_mul_of_nonneg_left hb (by positivity)


end GlobalTheory.ThetaSizeBounds
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormValueOnTangentVectorEqZeroOfGlobalFormZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormValueOnTangentVectorEqZeroOfGlobalFormZero
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechDR KaehlerDifferential
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TanVanish

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem snd_val_affine {R' : Type} [CommRing R'] [Algebra R R'] (U : X.affineOpens)
    (α : Sec s U.1 →ₐ[R] TrivSqZeroExt R' R') (y : Sp (TrivSqZeroExt R' R') ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (TrivSqZeroExt R' R')))
    (e : spMap (α : Sec s U.1 →+* TrivSqZeroExt R' R') ≫ affPt s U = y) (f : Form s)
    (h0 : connForm f.1 (affPt s U) (affPt_w s U) = 0) :
    TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val y hy f.1) = 0 := by
  have hx := affPt_w s U
  letI : Algebra (Sec s U.1) R' := ((TrivSqZeroExt.fstHom R R' R').comp α).toRingHom.toAlgebra
  haveI : IsScalarTower R (Sec s U.1) R' := IsScalarTower.of_algebraMap_eq fun r ↦
    (congrArg TrivSqZeroExt.fst (α.commutes r)).symm
  let δ : Derivation R (Sec s U.1) R' :=
    { toFun := fun b ↦ (α b).snd
      map_add' := fun a b ↦ by simp
      map_smul' := fun r b ↦ by
        simp [Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl']
      map_one_eq_zero' := by simp
      leibniz' := fun a b ↦ by
        simp only [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, Algebra.smul_def,
          RingHom.algebraMap_toAlgebra]
        simp [MulOpposite.smul_eq_mul_unop]
        ring }
  let δ' := δ.liftKaehlerDifferential
  have hop : ∀ (b : Sec s U.1) (ω : Ω[Sec s U.1⁄R]), MulOpposite.op b • ω = b • ω := fun _ _ ↦ rfl
  let Φ : TrivSqZeroExt (Sec s U.1) Ω[Sec s U.1⁄R] →ₐ[R] TrivSqZeroExt R' R' :=
    { toFun := fun c ↦ TrivSqZeroExt.inl (algebraMap (Sec s U.1) R' c.fst) +
        TrivSqZeroExt.inr (δ' c.snd)
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun a b ↦ by ext <;> simp <;> ring
      map_mul' := fun a b ↦ by
        ext
        · simp
        · simp only [TrivSqZeroExt.snd_mul, hop, map_add (f := _), map_smul, TrivSqZeroExt.snd_add,
            TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add,
            TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, smul_eq_mul, Algebra.smul_def]
          simp [MulOpposite.smul_eq_mul_unop]
          ring
      commutes' := fun r ↦ by
        ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl', ← IsScalarTower.algebraMap_apply] }
  let α₀ : Sec s U.1 →ₐ[R] R' := (TrivSqZeroExt.fstHom R R' R').comp α
  have hπ : ∀ c, α₀ ((diagExt R (Sec s U.1)).π c) = (SqExt.ofModule R R' R').π (Φ c) := fun c ↦ by
    simp [Φ, α₀, RingHom.algebraMap_toAlgebra]
  have e₀ : spMap (α₀ : Sec s U.1 →+* R') ≫ affPt s U =
      spMap ((SqExt.ofModule R R' R').π : TrivSqZeroExt R' R' →+* R') ≫ y := by
    rw [← e, ← Category.assoc, ← Cris.spMap_comp]; rfl
  let Ψ := (diagExt R (Sec s U.1)).thickHom (SqExt.ofModule R R' R') Φ α₀ hπ hx
    ((SqExt.ofModule R R' R').red_w hy) e₀
  let a1 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶
      Thick.triv R' _ ((SqExt.ofModule R R' R').red_w hy) := Thick.trivHom α₀ e₀
  let a2 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶ Thick.triv (TrivSqZeroExt R' R') y hy :=
    Thick.trivHom α e
  have k1 := Form.ev_sq f a1 ((SqExt.ofModule R R' R').secHom ((SqExt.ofModule R R' R').red_w hy)
    (SqExt.ofModule R R' R').i (SqExt.ofModule R R' R').π_i)
    ((diagExt R (Sec s U.1)).secHom hx (diagExt R (Sec s U.1)).i fun _ ↦ rfl) Ψ rfl rfl fun c ↦ by
      change TrivSqZeroExt.inl (α₀ c) = Φ (TrivSqZeroExt.inl c)
      ext <;> simp [Φ, α₀, RingHom.algebraMap_toAlgebra]
  have k2 := Form.ev_sq f a2 ((SqExt.ofModule R R' R').idHom hy)
    ((diagExt R (Sec s U.1)).secHom hx (diagSec R (Sec s U.1)) (fst_derSec _)) Ψ rfl rfl fun c ↦ by
      change α c = Φ (diagSec R (Sec s U.1) c)
      ext
      · simp [Φ, RingHom.algebraMap_toAlgebra]
      · simp only [Φ, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
          TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, snd_derSec]
        exact (Derivation.liftKaehlerDifferential_comp_D δ c).symm
  have hΦ : ∀ z, TrivSqZeroExt.snd (Φ z) = δ' z.snd := fun z ↦ by simp [Φ]
  rw [SqExt.val_apply, k1, k2, add_sub_add_right_eq_sub]
  change TrivSqZeroExt.snd (Φ _ - Φ _) = 0
  rw [← map_sub, hΦ]
  have h0' : TrivSqZeroExt.snd (ev f.1 ((diagExt R (Sec s U.1)).secHom hx (diagExt R (Sec s U.1)).i
      fun _ ↦ rfl) - ev f.1 ((diagExt R (Sec s U.1)).secHom hx (diagSec R (Sec s U.1))
      (fst_derSec _))) = 0 := h0
  rw [h0', map_zero]

theorem snd_val_eq_zero (y : Sp (DualNumber R) ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (DualNumber R))) (f : Form s)
    (h0 : ∀ U : X.affineOpens, connForm f.1 (affPt s U) (affPt_w s U) = 0) :
    TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val y hy f.1) = 0 := by
  have loc : ∀ m : Ideal R, m.IsMaximal →
      ∃ t ∉ m, t * TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val y hy f.1) = 0 := by
    intro m hm
    haveI := hm.isPrime
    let R' := Localization.AtPrime m
    haveI : IsLocalRing (TrivSqZeroExt R' R') :=
      IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun c ↦ by
        simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
        exact IsLocalRing.isUnit_or_isUnit_one_sub_self c.fst
    let φ : DualNumber R →ₐ[R] TrivSqZeroExt R' R' :=
      { toFun := fun c ↦ TrivSqZeroExt.inl (algebraMap R R' c.fst) +
          TrivSqZeroExt.inr (algebraMap R R' c.snd)
        map_one' := by ext <;> simp
        map_zero' := by ext <;> simp
        map_add' := fun a b ↦ by ext <;> simp [Algebra.smul_def] <;> ring
        map_mul' := fun a b ↦ by ext <;> simp [MulOpposite.smul_eq_mul_unop, Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl'] <;> ring
        commutes' := fun r ↦ by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl'] }
    let y' := spMap (φ : DualNumber R →+* TrivSqZeroExt R' R') ≫ y
    have hy' : y' ≫ s = spMap (algebraMap R (TrivSqZeroExt R' R')) := by
      change (spMap (φ : DualNumber R →+* TrivSqZeroExt R' R') ≫ y) ≫ s = _
      rw [Category.assoc, hy, ← Cris.spMap_comp, φ.comp_algebraMap]
    have hv := (SqExt.dual R).val_map (SqExt.ofModule R R' R') φ (Algebra.ofId R R')
      (fun c ↦ by simp [φ]) (fun b ↦ by ext <;> simp [φ, TrivSqZeroExt.algebraMap_eq_inl']) y hy y' hy' rfl f
    obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
      (x := y' (IsLocalRing.closedPoint (TrivSqZeroExt R' R'))) trivial
    have htop := Scheme.preimage_eq_top_of_closedPoint_mem y' hp
    let α₁ : Sec s U →+* TrivSqZeroExt R' R' := evalAt y' U htop.ge
    have hα : spMap α₁ ≫ affPt s ⟨U, hU⟩ = y' := by
      have k := IsAffineOpen.SpecMap_appLE_fromSpec y' hU (isAffineOpen_top _) htop.ge
      rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at k
      have e1 : spMap α₁ ≫ affPt s ⟨U, hU⟩ =
          Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R' R'))).hom) ≫
          Spec.map (y'.appLE U ⊤ htop.ge) ≫ hU.fromSpec := by
        rw [← Category.assoc, ← Spec.map_comp]; rfl
      rw [e1]
      rw [k]
      simp only [← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
    have hc : α₁.comp (algebraMap R (Sec s U)) = algebraMap R (TrivSqZeroExt R' R') := by
      have e2 : spMap (α₁.comp (algebraMap R (Sec s U))) = spMap (algebraMap R (TrivSqZeroExt R' R')) := by
        rw [Cris.spMap_comp, ← affPt_w s ⟨U, hU⟩, ← Category.assoc, hα, hy']
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
    let α : Sec s U →ₐ[R] TrivSqZeroExt R' R' :=
      { α₁ with commutes' := fun r ↦ RingHom.congr_fun hc r }
    have h1 := snd_val_affine ⟨U, hU⟩ α y' hy' hα f (h0 _)
    rw [hv] at h1
    have h2 : algebraMap R R' (TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val y hy f.1)) = 0 := by
      simpa [φ, Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl'] using h1
    obtain ⟨⟨t, ht⟩, ht'⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl R' _).1 h2
    exact ⟨t, ht, ht'⟩
  by_contra hx
  let J : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R
    (TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val y hy f.1)))
  have hJ : J ≠ ⊤ := fun h ↦ hx (by
    have : (1 : R) ∈ J := h ▸ Submodule.mem_top
    simpa [J] using this)
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨t, ht, ht'⟩ := loc m hm
  exact ht (hJm (by simpa [J] using ht'))

theorem tanVal_eq_zero_of_cmpForm_eq_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R))
    (v : epsR R ⟶ A) (f : Form (A.hom ≫ 𝟙 (Sp R))),
    GlobalTheory.CechDR.cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → tanVal v f = 0 := by
  intro R _ A v f hf
  rw [tanVal_apply]
  refine snd_val_eq_zero v.left (pt_w v) f fun U ↦ ?_
  have := congrArg (fun g : ClosedForm (A.hom ≫ 𝟙 (Sp R)) ↦ g.1.1 (Opposite.op U)) hf
  exact (cmpForm_apply _ f (Opposite.op U)).symm.trans (this.trans rfl)

end GlobalTheory.TanVanish
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormValueOnTangentVectorEqZeroOfGlobalFormZeroStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formValueOnTangentVector_eq_zero_of_globalForm_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) (v : epsR R ⟶ A) (f : Form (A.hom ≫ 𝟙 (Sp R))), GlobalTheory.CechDR.cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → tanVal v f = 0 := by
  first | exact @GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero | exact GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero | (intros; apply GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

def chartVal {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) {k : ℕ} (s : SecK L α k) (j : L.ι) (W : X.Opens)
    (hW : W ≤ L.U j) : Γ(Y, α ⁻¹ᵁ W) :=
  (Y.presheaf.map (homOfLE (locInt_le_chart L α j W hW)).op).hom (s.f (fun _ => j))

def IntAt {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) {k : ℕ} (s : SecK L α k) (x : X) : Prop :=
  ∃ (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), x ∈ W ∧ IsAffineOpen W ∧
    (α.app W).hom.IsIntegralElem (chartVal L α s j W hW)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotal
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false
namespace GlobalTheory.SmoothDimTotal
open IsLocalRing

theorem topologicalKrullDim_eq_iSup_stalk (X : Scheme.{0}) :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  simp only [ringKrullDim_stalk_eq_coheight]

theorem ringKrullDim_stalk_le_of_smooth (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (.of K)) (n : ℕ)
    (h : SmoothOfRelativeDimension n f) (x : X) : ringKrullDim (X.presheaf.stalk x) ≤ n := by
  haveI : Nonempty X := ⟨x⟩
  rw [ringKrullDim_stalk_eq_coheight, ← GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth f n h]
  exact (Order.coheight_le_krullDim x).trans (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).ge

end GlobalTheory.SmoothDimTotal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfHolUnif
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusAction

theorem smoothOfRelativeDimension_of_holUnif (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left}
    {g : ℕ} (u : HolUnif A L g) : SmoothOfRelativeDimension g A.hom := by
  haveI := hA.comm
  haveI := hA.proper
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ A hA
  obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ A hA
  have hamp : Out.RelAmple A H :=
    (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hH).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)
  obtain ⟨u₀⟩ := RealMultChart.exists_holUnif_of_compact A d hd (RealMultChart.compactSpace_points A H hamp)
    (fun a n hn => RealMultChart.exists_pow_eq A hA a n hn)
  obtain ⟨h₁, h₂⟩ := TorusTransfer.tangent_bijective u₀ hd
  obtain ⟨T, hT, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA _ d g u₀ h₁ h₂
    u.ex u.ex_add (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  rw [Obj.holUnif_dim_eq_of_linear u u₀ T hT]
  exact hd


end GlobalTheory.TorusAction
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarried
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def SecCarried {X : Scheme.{0}} (L : LB X) (θ : L.Sec) (f : X ⟶ X) (w : LB.Iso L (L.pull f)) : Prop :=
  ∀ (z : X) (j k : L.ι) (hk : z ∈ L.U k) (hj : f z ∈ L.U j),
    (X.presheaf.germ (f ⁻¹ᵁ L.U j) z hj).hom ((f.app (L.U j)).hom (θ.f j)) =
      (gw w (𝟙 X) z j k).val * (X.presheaf.germ (L.U k) z hk).hom (θ.f k)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesO1OfProjectiveRankCupStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.axesO1_of_projective_rank_cup : (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧ ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom), ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b) → AxesVanishingStructureSheafDegOne := by
  first | exact @GlobalTheory.Obs.axesO1_of_cohomology_structure | exact GlobalTheory.Obs.axesO1_of_cohomology_structure | (intros; apply GlobalTheory.Obs.axesO1_of_cohomology_structure <;> assumption)
end
