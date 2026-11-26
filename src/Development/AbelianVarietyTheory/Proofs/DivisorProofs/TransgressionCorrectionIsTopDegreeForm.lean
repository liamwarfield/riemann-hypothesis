module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionDensityHolomorphicChartEtale
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyWedgeNoPrimitiveH2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgClosedFieldTorsionMapsCommuteHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoEqOneAlongAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegOfPeriodicOfIsRegSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVariety

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeForm
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem isTopForm_corrDens : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → IsTopForm (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) := by
  intro F _ σ X m E O H H₀ hM hM₀ ρ hρ
  refine ⟨fun i j y hy hi hj => ?_, fun i => ?_⟩
  · exact GlobalTheory.T.transgressionDensity_holomorphicChart_etale E O H H₀ hM hM₀ hρ i.holo j hy hi hj (E.nonempty (under y)).choose_spec
  · refine GlobalTheory.T.aemeasurable_chart_of_locally_continuous_density i.e (isOpen_ptsIn O) fun y hy hc => ?_
    set A := (E.nonempty (under y)).choose with hAdef
    have hA : A ∈ E.S (under y) := (E.nonempty (under y)).choose_spec
    refine ⟨corrTop (fun v => ρ (i.e.symm v)) (fun v => H₀ A (i.e.symm v) ()) (fun v => H A (i.e.symm v) ()), ?_, ?_⟩
    · have hs : i.e.target ∩ i.e.symm ⁻¹' Set.univ ∈ 𝓝 (i.e y) := by
        simpa using i.e.open_target.mem_nhds (i.e.map_source hc)
      have hρ1 : ContDiffAt ℝ 1 (fun v => ρ (i.e.symm v)) (i.e y) :=
        ((contDiffOn_chart (S := Set.univ) (fun z _ => hρ z) i).contDiffAt hs).of_le (by norm_cast)
      have hc0 := GlobalTheory.T.continuousAt_transgressionTopCoeffComplex hρ1 (hM₀.mContDiffAt_chart mem_ptsIn_top i hc hA ())
        (hM₀.isUnit_det_chart mem_ptsIn_top i hc hA ()) (hM.mContDiffAt_chart hy i hc hA ())
        (hM.isUnit_det_chart hy i hc hA ())
      exact continuousAt_const.mul (Complex.continuous_re.continuousAt.comp hc0)
    · filter_upwards [(isOpen_ptsIn O).mem_nhds hy, i.e.open_source.mem_nhds hc, GlobalTheory.FrameLift.eventually_mem hA]
        with z hzO hzc hAz
      have h := GlobalTheory.T.transgressionDensity_holomorphicChart_etale E O H H₀ hM hM₀ hρ i.holo i hzO hzc hzc hAz
      rw [AlgChart.transDet_self i hzc, norm_one, one_pow, one_mul] at h
      exact h.symm

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeFormStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transgression_correction_isTopDegreeForm : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → IsTopForm (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) := by
  first | exact @GlobalTheory.GoodTop.isTopForm_corrDens | exact GlobalTheory.GoodTop.isTopForm_corrDens | (intros; apply GlobalTheory.GoodTop.isTopForm_corrDens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpUUniqueOfLower
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

theorem upU_unique_of_lower : ∀ (K : Type) [Field K] (s : ℕ) (y y' : Low s → K) (b : Matrix (Fin s) (Fin s) K),
    (∀ i j, i < j → b i j = 0) → upU y = b * upU y' → y = y' := by
  intro K _ s y y' b hb h
  have key : ∀ i j : Fin s, (∀ k, k < j → b i k = 0) → upU y i j = b i j := by
    intro i j hk
    rw [h, Matrix.mul_apply, Finset.sum_eq_single j]
    · simp [upU]
    · intro k _ hkj
      rcases lt_or_gt_of_ne hkj with h1 | h1
      · rw [hk k h1, zero_mul]
      · simp [upU, not_lt.mpr h1.le, hkj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have low : ∀ (i : Fin s) (N : ℕ) (j : Fin s), j.1 < N → j < i → b i j = 0 := by
    intro i N
    induction N with
    | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ N ih =>
      intro j hj hji
      rw [← key i j fun k hk => ih k (by have := Fin.lt_def.mp hk; omega) (hk.trans hji)]
      simp [upU, not_lt.mpr hji.le, hji.ne']
  have hb1 : b = 1 := by
    ext i j
    rcases lt_trichotomy i j with h1 | rfl | h1
    · rw [hb i j h1, Matrix.one_apply_ne h1.ne]
    · rw [← key i i fun k hk => low i (k.1 + 1) k (Nat.lt_succ_self _) hk]
      simp [upU]
    · rw [low i (j.1 + 1) j (Nat.lt_succ_self _) h1, Matrix.one_apply_ne h1.ne']
  rw [hb1, Matrix.one_mul] at h
  funext ⟨⟨c, a⟩, hac⟩
  have hac' : a < c := hac
  have := congrFun (congrFun h a) c
  simpa [upU, hac'] using this

end GlobalTheory.FlagCell2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyAbelianVarietyAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyAbelianVarietyAlgClosed
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exists_fin_affineOpen_cover_of_compactSpace (X : Scheme.{0}) [CompactSpace X] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  obtain ⟨Us, hUs, hfin, hU⟩ :=
    X.isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) isCompact_univ
  let s := hfin.toFinset
  refine ⟨s.card, fun i => (s.equivFin.symm i).1, fun i => ?_, ?_⟩
  · have h := (s.equivFin.symm i).2
    exact hUs (hfin.mem_toFinset.mp h)
  · apply le_antisymm le_top
    rw [hU]
    refine sSup_le fun u hu => ?_
    have hs : u ∈ s := hfin.mem_toFinset.mpr hu
    refine le_iSup_of_le (s.equivFin ⟨u, hs⟩) ?_
    simp

theorem structureSheafCoh_abelianVariety_algClosed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ),
      IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      Module.Finite K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g ∧
        GlobalTheory.AbCoh.WedgeO (OAff A.hom) ∧ GlobalTheory.AbCoh.NoPrimitiveStructureSheafH2 A ∧ GlobalTheory.AbCoh.AxesVanishingStructureSheafDegOne A := by
  intro K _ _ A _ g hA hg
  obtain ⟨hax, -, hrk⟩ := GlobalTheory.T.abelian_variety_h1_axes_primitive_rank K A g hA hg
  obtain ⟨hw, hno⟩ := GlobalTheory.T.abelian_variety_wedge_no_primitive_h2 K A g hA hg
  refine ⟨?_, hrk, hw, hno, hax⟩
  haveI : IsProper A.hom := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨n, D, hD, hcov⟩ := exists_fin_affineOpen_cover_of_compactSpace A.left
  obtain ⟨⟨e⟩, -⟩ := GlobalTheory.T.cech_cohomology_structure_sheaf_iso K A.left A.hom (Fin n) D inferInstance hD hcov
  obtain ⟨hfin, -, -⟩ := GlobalTheory.T.cech_cohomology_trivial_bundle_abelian K A g hA hg (Fin n) D hD hcov
  exact Module.Finite.equiv e.symm

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyAbelianVarietyAlgClosedStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structureSheafCohomology_abelianVariety_algClosed : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Module.Finite K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g ∧ GlobalTheory.AbCoh.WedgeO (OAff A.hom) ∧ GlobalTheory.AbCoh.NoPrimitiveStructureSheafH2 A ∧ GlobalTheory.AbCoh.AxesVanishingStructureSheafDegOne A := by
  first | exact @GlobalTheory.AbCoh.structureSheafCoh_abelianVariety_algClosed | exact GlobalTheory.AbCoh.structureSheafCoh_abelianVariety_algClosed | (intros; apply GlobalTheory.AbCoh.structureSheafCoh_abelianVariety_algClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthGeFinrankOfSemilinearSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthGeFinrankOfSemilinearSurjective
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem length_ge_finrank_of_semilinear_surj (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (N U : Type) [AddCommGroup N] [Module (WittVector p k) N] [AddCommGroup U]
    [Module k U] [Module.Finite k U] (e : (WittVector p k) ≃+* (WittVector p k)) (θ : N →+ U) :
    Function.Surjective θ → (∀ (a : (WittVector p k)) n, θ (e a • n) = WittVector.constantCoeff a • θ n) →
    ∀ L : Submodule (WittVector p k) N, ((∀ n ∈ L, θ n = 0) →
      (Module.finrank k U : ℕ∞) ≤ Module.length (WittVector p k) (N ⧸ L)) ∧
      ((∀ n, n ∈ L ↔ θ n = 0) → Module.length (WittVector p k) (N ⧸ L) = Module.finrank k U) := by
  intro hθ hsemi L
  let σ : WittVector p k →+* k := (WittVector.constantCoeff).comp e.symm.toRingHom
  have hσ : Function.Surjective σ := by
    intro x
    obtain ⟨a, ha⟩ : ∃ a : WittVector p k, WittVector.constantCoeff a = x :=
      ⟨WittVector.teichmuller p x, by simp⟩
    exact ⟨e a, by simp [σ, ha]⟩
  letI : Algebra (WittVector p k) k := σ.toAlgebra
  letI : Module (WittVector p k) U := Module.compHom U σ
  haveI : IsScalarTower (WittVector p k) k U :=
    ⟨fun a b u => by
      show (σ a * b) • u = σ a • (b • u)
      exact mul_smul _ _ _⟩
  have hlenU : Module.length (WittVector p k) U = Module.finrank k U := by
    rw [Module.length_eq_of_surjective (R := k) (S := WittVector p k) (M := U) hσ,
      Module.length_eq_finrank]
  let θl : N →ₗ[WittVector p k] U :=
    { toFun := θ
      map_add' := θ.map_add
      map_smul' := fun a n => by
        have h := hsemi (e.symm a) n
        rw [RingEquiv.apply_symm_apply] at h
        exact h }
  have hθl : Function.Surjective θl := hθ
  refine ⟨fun hL => ?_, fun hL => ?_⟩
  · have hle : L ≤ LinearMap.ker θl := fun n hn => hL n hn
    rw [← hlenU]
    exact Module.length_le_of_surjective (L.liftQ θl hle) (by
      intro u
      obtain ⟨n, rfl⟩ := hθl u
      exact ⟨Submodule.Quotient.mk n, rfl⟩)
  · have hK : L = LinearMap.ker θl := by
      ext n
      exact hL n
    rw [← hlenU, hK]
    exact (θl.quotKerEquivOfSurjective hθl).length_eq

end GlobalTheory.Dieu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthGeFinrankOfSemilinearSurjectiveStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_ge_finrank_of_semilinear_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N U : Type) [AddCommGroup N] [Module (WittVector p k) N] [AddCommGroup U] [Module k U] [Module.Finite k U] (e : (WittVector p k) ≃+* (WittVector p k)) (θ : N →+ U), Function.Surjective θ → (∀ (a : (WittVector p k)) n, θ (e a • n) = WittVector.constantCoeff a • θ n) → ∀ L : Submodule (WittVector p k) N, ((∀ n ∈ L, θ n = 0) → (Module.finrank k U : ℕ∞) ≤ Module.length (WittVector p k) (N ⧸ L)) ∧ ((∀ n, n ∈ L ↔ θ n = 0) → Module.length (WittVector p k) (N ⧸ L) = Module.finrank k U) := by
  first | exact @GlobalTheory.Dieu.length_ge_finrank_of_semilinear_surj | exact GlobalTheory.Dieu.length_ge_finrank_of_semilinear_surj | (intros; apply GlobalTheory.Dieu.length_ge_finrank_of_semilinear_surj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbackDvrTorsionPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbackDvrTorsionPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

open GlobalTheory.TorusExt GlobalTheory.Balanced

attribute [local instance] gtGroup


set_option maxHeartbeats 2000000 in
theorem pull_unif_tors : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f : R →+* V, Function.Injective f → J.map f ≤ maximalIdeal V → ∃ (D : DegData V (maximalIdeal V)) (hD : IsPullDeg f D₀.toPre D.toPre) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A ((Over.pullback (specOf f)).obj G₀)), IsSemiAbelian ((Over.pullback (specOf f)).obj G₀) ∧ IsPullUnif f hD (Iso.refl _) U₀ U ∧ ∀ (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀.toPre F₀ k) (x₀ : TFK (R := R) F₀ ⟶ A₀.A), QkToAkU U₀.toUnifPre F₀ k p₀ x₀ → ∃ (p : QkPt D.toPre F k) (x : TFK (R := V) F ⟶ A.A), p.y = hD.xe.symm p₀.y ∧ Tr f hD j p₀.g p.g ∧ QkToAkU U.toUnifPre F k p x ∧ x.left ≫ U.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf f)).obj G₀).hom (jK V) ≫ pullback.fst G₀.hom (specOf f) = spMap j ≫ x₀.left ≫ U₀.gen.inv.left ≫ pullback.fst G₀.hom (jK R) := by
  intro R _ _ _ J hR D₀ A₀ G₀ _ _ U₀ hG V _ _ _ _ hV f hf hJ
  have hL := GlobalTheory.firstFiveLaws
  have hR' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  obtain ⟨D, hD, A, U, hG', hU, hpt, -⟩ := GlobalTheory.T.uniformisation_endomorphisms_to_complete_dvr hL R J hR D₀ A₀ G₀ hG U₀ V f hV hf hJ
  refine ⟨D, hD, A, U, hG', hU, ?_⟩
  intro F₀ _ _ _ F _ _ _ j hj k hk p₀ x₀ hx₀
  letI : Algebra (FractionRing R) F := (j.comp (algebraMap (FractionRing R) F₀)).toAlgebra
  let σ : F₀ →ₐ[FractionRing R] F := { j with commutes' := fun _ => rfl }
  have hB := D₀.tau_bimult
  have hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) =
      algebraMap (FractionRing V) F (algebraMap V _ (f r)) := hj
  obtain ⟨p₁, hp₁⟩ := qkExtExists R D₀.toPre F₀ F σ.toRingHom (fun r => σ.commutes r) k p₀
  let x₁ : TFK (R := R) F ⟶ A₀.A := extPt σ x₀
  have hx₁ : QkToAkU U₀.toUnifPre F k p₁ x₁ := (GlobalTheory.T.qkToAkU_iff_galois_equivariant hL R J hR D₀ A₀ G₀ hG U₀ F₀ F σ k hk p₀ p₁ x₀ x₁
    hp₁ rfl).1 hx₀
  obtain ⟨ex, -, io, ns⟩ := hpt F hF
  obtain ⟨g, hg, -⟩ := ex p₁.g
  let p : QkPt D.toPre F k := ⟨hD.xe.symm p₁.y, g, by
    obtain ⟨s, h1, h2⟩ := p₁.eq
    obtain ⟨s', hs', -⟩ := ex s
    exact ⟨s', (ns k _ _ _ _ hg hs').1 h1, (io _ _ _ hs').1 (by rwa [AddEquiv.apply_symm_apply])⟩⟩
  obtain ⟨x, hx⟩ := exists_toG_pull f U₀.toUnifPre U.toUnifPre hF x₁
  refine ⟨p, x, by simpa [p, hp₁.1], ⟨p₁.g, hp₁.2, hg⟩, ?_, ?_⟩
  · exact hL.2.2.2.2.qkBaseChange R V J _ hR hR' f D₀ A₀ G₀ U₀ _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _))) A D
      hD U hU F hF k hk p₁ x₁ p x rfl hg
      (by simpa only [toG, Category.assoc, Iso.refl_hom, Over.id_left, Category.id_comp] using hx) hx₁
  · simpa only [toG, Category.assoc, x₁, extPt, Over.homMk_left] using hx

end GlobalTheory.TInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbackDvrTorsionPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_pullback_dvr_torsionPoints : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f : R →+* V, Function.Injective f → J.map f ≤ maximalIdeal V → ∃ (D : DegData V (maximalIdeal V)) (hD : IsPullDeg f D₀.toPre D.toPre) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A ((Over.pullback (specOf f)).obj G₀)), IsSemiAbelian ((Over.pullback (specOf f)).obj G₀) ∧ IsPullUnif f hD (Iso.refl _) U₀ U ∧ ∀ (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀.toPre F₀ k) (x₀ : TFK (R := R) F₀ ⟶ A₀.A), QkToAkU U₀.toUnifPre F₀ k p₀ x₀ → ∃ (p : QkPt D.toPre F k) (x : TFK (R := V) F ⟶ A.A), p.y = hD.xe.symm p₀.y ∧ Tr f hD j p₀.g p.g ∧ QkToAkU U.toUnifPre F k p x ∧ x.left ≫ U.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf f)).obj G₀).hom (jK V) ≫ pullback.fst G₀.hom (specOf f) = spMap j ≫ x₀.left ≫ U₀.gen.inv.left ≫ pullback.fst G₀.hom (jK R) := by
  first | exact @GlobalTheory.TInj.pull_unif_tors | exact GlobalTheory.TInj.pull_unif_tors | (intros; apply GlobalTheory.TInj.pull_unif_tors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberMultilinearSymm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberMultilinearSymm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AV.AbVar

theorem diffVanish_chiPic_structureModule {K : Type} [Field K] (A : AbVar K) :
    letI := A.algΓ
    DiffVanish (A.dim + 1) (chiPic K (QCoh.structureModule A.X.left)) := by
  letI := A.algΓ
  refine diffVanish_chiPic_of_isProjOver (f := A.X.hom) (fun r => rfl) _
    (GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K A).2 ?_
  refine (QCoh.suppDim_le _).trans ?_
  rw [GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K A]

theorem inter_update_add {K : Type} [Field K] (A : AbVar K) {J : Type} [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = A.dim) (c : J → Pic A.X.left) (i : J) (a b : Pic A.X.left) :
    inter A (Function.update c i (a + b)) = inter A (Function.update c i a) + inter A (Function.update c i b) := by
  letI := A.algΓ
  exact congrFun ((diffVanish_chiPic_structureModule A).multiDiff_update_add_of_le_card hJ.ge c i a b) 0

def interAdd {K : Type} [Field K] (A : AbVar K) {J : Type} [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = A.dim) (c : J → Pic A.X.left) (i : J) : Pic A.X.left →+ ℤ :=
  AddMonoidHom.mk' (fun a => inter A (Function.update c i a)) (inter_update_add A hJ c i)

theorem inter_comp_equiv {K : Type} [Field K] (A : AbVar K) {J J' : Type} [Fintype J] [Fintype J']
    (e : J' ≃ J) (c : J → Pic A.X.left) : inter A (c ∘ e) = inter A c := by
  letI := A.algΓ
  exact congrFun (multiDiff_comp_equiv e c _) 0

theorem inter_multilinear_and_symm :
    ∀ (K : Type) [Field K] (A : AbVar K) (J : Type) [Fintype J], Fintype.card J = A.dim →
      (∃ M : (J → Pic A.X.left) →ₘₗ[ℤ] ℤ, ∀ c, M c = inter A c) ∧
      ∀ (J' : Type) [Fintype J'] (e : J' ≃ J) (c : J → Pic A.X.left), inter A (c ∘ e) = inter A c := by
  intro K _ A J _ hJ
  classical
  refine ⟨⟨MultilinearMap.mk' (fun c => inter A c) (fun c i a b => inter_update_add A hJ c i a b)
    (fun c i n a => map_zsmul (interAdd A hJ c i) n a), fun c => rfl⟩, fun J' _ e c => inter_comp_equiv A e c⟩

end GlobalTheory.AV.AbVar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberMultilinearSymmStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_number_multilinear_symm : ∀ (K : Type) [Field K] (A : AbVar K) (J : Type) [Fintype J], Fintype.card J = A.dim → (∃ M : MultilinearMap (RingHom.id ℤ) (fun _ : J => Pic A.X.left) ℤ, ∀ c, M c = inter A c) ∧ ∀ (J' : Type) [Fintype J'] (e : J' ≃ J) (c : J → Pic A.X.left), inter A (c ∘ e) = inter A c := by
  intro K _ A J _ hJ
  classical
  have hMultilinear : ∃ M : MultilinearMap (RingHom.id ℤ) (fun _ : J => Pic A.X.left) ℤ,
      ∀ c, M c = inter A c := by
    refine ⟨MultilinearMap.mk' (fun c => inter A c) (inter_update_add A hJ) ?_, fun c => rfl⟩
    intro c i n a
    exact map_zsmul (interAdd A hJ c i) n a
  exact ⟨hMultilinear, fun J' _ e c => inter_comp_equiv A e c⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricThetaConstantsEqThetaMapCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricThetaConstantsEqThetaMapCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

theorem exists_symE_pCrd : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∃ e : Fin (N + 1) → Ω, SymE ρ m e ∧ ∀ (h : Sp Ω ⟶ PSpace (cycAway n) N), h = spMap (algebraMap S.R Ω) ≫ u ≫ f → PCrd h e := by
  intro g n _ _ _ F W _ P rig m N f hT o Ω _ _ _ hA β S ρ u hS
  obtain ⟨hPg, hPs, hrig, hm, -, hmu, hN, -, hf, -⟩ := hT
  obtain ⟨-, -, hSg, hρs, -⟩ := hS
  haveI : CharZero Ω := hA.char
  have hSB : SecBaseChangeAnySt := GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny
  let v : S.R →+* Ω := S.R.val.toRingHom

  obtain ⟨P₀, φ, hg₀, hφ, hL₀⟩ := exists_isPolFibre polBaseChange_holds v ρ.P
  have hφ' : IsGrpPullback P₀.A ρ.P.A (spMap v ≫ 𝟙 (Sp S.R)) φ := by
    simpa using hφ
  have hL₀' : LBIso P₀.L (ρ.P.L.pull φ) := hL₀.symm
  have hfib : PolFib ρ.P.A ρ.P.L (8 * g) (spMap v ≫ 𝟙 (Sp S.R)) :=
    ⟨P₀, φ, by rw [hg₀, ρ.g_eq, hSg], hφ', hL₀'⟩

  have hth : IsGenSec ρ.P.A ρ.P.L 1 ρ.th₁ := fun s =>
    (ρ.th₁_basis s).exists.elim fun r h => ⟨r 0, fun j => (h j).trans (Fin.sum_univ_one _)⟩
  let θ : SecAt ρ.P.A ρ.P.L (spMap v ≫ 𝟙 (Sp S.R)) := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ v
  have : IsAffine (Over.mk (𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap v ≫ 𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Spec _))
  have hθ : IsGenSec ρ.P.A ρ.P.L _ θ := GlobalTheory.EmbPull.isGenSec_pullS ρ.P hSB _ hth

  obtain ⟨e, he⟩ := GlobalTheory.T.exists_theta_symmetric_function_values_in_ground_field (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) m (N + 1) Ω
    (spMap v ≫ 𝟙 (Sp S.R)) θ hm hN hfib
  have hmΩ : (m : Ω) ≠ 0 := by
    let κ : cycAway n →+* S.R := (Spec.preimage (u ≫ F.s)).hom
    have := (hmu.map κ).map v
    rw [map_natCast, map_natCast] at this
    exact this.ne_zero
  refine ⟨e, ⟨by rw [hSg]; exact hN, hmΩ, he⟩, fun h hh => ?_⟩

  obtain ⟨ψ, hψ, hLψ⟩ := GlobalTheory.T.sharp_polarization_unique_pullback g n F W ρ.P P u (𝟙 F.X) u (Category.comp_id u) hρs hPs
  have hα : IsGrpPullback P₀.A P.A ((spMap v ≫ u) ≫ 𝟙 F.X) (φ ≫ ψ) := by
    simpa using hφ.comp hψ
  have hLα : LBIso P₀.L (P.L.pull (φ ≫ ψ)) :=
    LBIso.trans P₀.isLB (pull_isLB ρ.P.isLB φ) (pull_isLB P.isLB _) hL₀'
      (LBIso.trans (pull_isLB ρ.P.isLB φ) (pull_isLB (pull_isLB P.isLB ψ) φ) (pull_isLB P.isLB _)
        (RigidBundleGlue.LBIso.pull hLψ φ) (GlobalTheory.UMin.FibMove.lbIso_pull_comp P.isLB ψ φ).symm)
  have key := GlobalTheory.T.thetaMap_coords_of_symmetric_theta_isomorphic_fibre F.X P.A P.L rig P.isLB hrig (8 * g) m N (cycAway n) F.X (𝟙 F.X) f (Sp S.R) ρ.P.A ρ.P.L ρ.rig
    Ω (spMap v ≫ u) (spMap v ≫ 𝟙 (Sp S.R)) P₀ (φ ≫ ψ) φ θ e hm hN hf ρ.P.isLB ρ.rig_gen
    (by rw [hg₀, ρ.g_eq, hSg]) hα hLα hφ' hL₀' hθ he
  rw [hh, show algebraMap S.R Ω = v from RingHom.ext fun _ => rfl]
  simpa [Category.assoc] using key

end GlobalTheory.SiegTh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricThetaConstantsEqThetaMapCoordsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_theta_constants_eq_thetaMap_coords : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∃ e : Fin (N + 1) → Ω, SymE ρ m e ∧ ∀ (h : Sp Ω ⟶ PSpace (cycAway n) N), h = spMap (algebraMap S.R Ω) ≫ u ≫ f → PCrd h e := by
  first | exact @GlobalTheory.SiegTh.exists_symE_pCrd | exact GlobalTheory.SiegTh.exists_symE_pCrd | (intros; apply GlobalTheory.SiegTh.exists_symE_pCrd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamClassEqZeroOfPeriodsZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamClassEqZeroOfPeriodsZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
open Opposite GlobalTheory.CatCoh

namespace GlobalTheory.CechPer

theorem eq_zero_of_isPer_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ x, IsPer u.ex u.Λ x 0 → x = 0 := by
  intro A _ g L u hA x hx
  obtain ⟨c, h, rfl, ⟨hd, hc, hω⟩, hp⟩ := hx
  obtain ⟨hopen, -, -, -, -, hmono, -, hloc, hres, halg, -, -⟩ := GlobalTheory.CechPer.pre_val_rules A g L u
  have vsub : ∀ (U : A.left.Opens) (a b : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (a - b : Sec (str A) U) z = val u.ex U a z - val u.ex U b z := by
    intro U a b z hz
    obtain ⟨e, he⟩ := halg U z hz
    exact (he (a - b : Sec (str A) U)).trans ((map_sub e a b).trans (congrArg₂ (· - ·) (he a).symm (he b).symm))
  have hreg : ∀ U V : A.left.affineOpens, IsReg u.ex (U.1 ⊓ V.1) (h U - h V) := by
    intro U V
    apply GlobalTheory.T.isRegularOnOpenUniformised_of_locally A g L u hA
    intro z hz
    obtain ⟨W, hW, hzW⟩ := hloc _ z hz
    have hWU : W ≤ U := (le_inf_iff.1 hW).1
    have hWV : W ≤ V := (le_inf_iff.1 hW).2
    refine ⟨W.1, hW, hzW, (c.1.1 (op V) (op W) (homOfLE hWV).op - c.1.1 (op U) (op W) (homOfLE hWU).op :
      Sec (str A) W.1), fun y hy ↦ ?_⟩
    have e0 := vsub W.1 (c.1.1 (op V) (op W) (homOfLE hWV).op) (c.1.1 (op U) (op W) (homOfLE hWU).op) y hy
    have e1 := hc U W (homOfLE hWU).op y hy
    have e2 := hc V W (homOfLE hWV).op y hy
    refine Eq.trans ?_ e0.symm
    rw [Pi.sub_apply]
    linear_combination e2 - e1
  have hb := GlobalTheory.T.isReg_of_periodic_of_isReg_sub' A g L u hA A.left.affineOpens (fun U ↦ U.1) h
    (iSup_affineOpens_eq_top A.left) hd (fun U l z hz ↦ by simpa using hp U l z hz) hreg
  choose b hb using hb
  let b' : ∀ U : A.left.affineOpens, Sec (str A) U.1 := b
  refine (Hyp1.mk_eq_zero (F := OAff (str A))).2 ⟨fun T ↦ b' T.unop, Tot1.ext (fun T T' a ↦ ?_) (fun T ↦ ?_)⟩
  · obtain ⟨U⟩ := T
    obtain ⟨V⟩ := T'
    have hVU : V.1 ≤ U.1 := leOfHom a.unop
    have hz0 := GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA V.1
      ((b' V - Sec.res (str A) hVU (b' U) - c.1.1 (op U) (op V) a : Sec (str A) V.1)) (fun z hz ↦ by
        have e0 := vsub V.1 (b' V - Sec.res (str A) hVU (b' U)) (c.1.1 (op U) (op V) a) z hz
        have e1 := vsub V.1 (b' V) (Sec.res (str A) hVU (b' U)) z hz
        have e2 := hres U.1 V.1 hVU (b' U) z hz
        have e3 : h V z = val u.ex V.1 (b' V) z := hb V z hz
        have e4 : h U z = val u.ex U.1 (b' U) z := hb U z (hmono _ _ hVU hz)
        have e5 := hc U V a z hz
        refine e0.trans ?_
        linear_combination e1 - e2 - e3 + e4 + e5)
    exact sub_eq_zero.1 (show (b' V - Sec.res (str A) hVU (b' U) - c.1.1 (op U) (op V) a : Sec (str A) V.1) = 0 from hz0)
  · obtain ⟨U⟩ := T
    change KaehlerDifferential.D ℂ (Sec (str A) U.1) (b' U) = c.1.2 (op U)
    apply sub_eq_zero.1
    apply GlobalTheory.T.kaehlerOneForm_eq_zero_of_uniformised_values A g L u hA U
    intro z hz
    rw [map_sub, (GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u U.1 z hz).2.2 (b' U), ← hω U z hz, sub_eq_zero]
    refine (Filter.EventuallyEq.fderiv_eq ?_).symm
    filter_upwards [(hopen U.1).mem_nhds hz] with y hy
    exact hb U y hy

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamClassEqZeroOfPeriodsZeroStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechDeRham_class_eq_zero_of_periods_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ x, IsPer u.ex u.Λ x 0 → x = 0 := by
  first | exact @GlobalTheory.CechPer.eq_zero_of_isPer_zero | exact GlobalTheory.CechPer.eq_zero_of_isPer_zero | (intros; apply GlobalTheory.CechPer.eq_zero_of_isPer_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentKernelEqCokerOmegaMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentKernelEqCokerOmegaMap
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

noncomputable section

namespace GlobalTheory.PDivGroup

theorem cotMap_comp_eq_zero_of_kerIdeal_le {k A B C : Type} [Field k] [CommRing A] [CommRing B]
    [CommRing C] [Bialgebra k A] [Bialgebra k B] [Bialgebra k C] (g : B →ₐc[k] A)
    (π : A →ₐc[k] C) (h : kerIdeal g ≤ RingHom.ker π) (x : Cot k B) :
    cotMap π (cotMap g x) = 0 := by
  rw [← LinearMap.comp_apply, ← cotMap_comp]
  obtain ⟨b, rfl⟩ := AugCot.d_surjective _ x
  rw [cotMap_d]
  have h' := (kerIdeal_le_ker_iff g (π : A →ₐ[k] C)).1 h b
  change dUnit (R := k) ((π : A →ₐ[k] C) (g b)) = 0
  rw [h']
  exact AugCot.d_algebraMap _ _

theorem cot_kernel_eq_coker_omegaMap : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H) (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (π : G.A 1 →ₐc[k] C), Function.Surjective π → (kerIdeal (q.app 1) ≤ RingHom.ker π → ∀ w ∈ LinearMap.range (omegaMap G H q), cotMap π (w.1 1) = 0) ∧ (RingHom.ker π ≤ kerIdeal (q.app 1) ⊔ augIdeal k (G.A 1) ^ 2 → kerIdeal (q.app 1) ≤ RingHom.ker π → Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) = Module.finrank k (Cot k C)) ∧ ∀ (H' : PDivGroup p k) (f : G ⟶ H'), (∀ w ∈ LinearMap.range (omegaMap G H' f), cotMap π (w.1 1) = 0) → cotMap (π.comp (f.app 1)) = 0 := by
  intro p _ k _ _ G H q C _ _ _ _ π hπ
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have part1 : kerIdeal (q.app 1) ≤ RingHom.ker π →
      ∀ w ∈ LinearMap.range (omegaMap G H q), cotMap π (w.1 1) = 0 := by
    rintro h w ⟨v, rfl⟩
    exact cotMap_comp_eq_zero_of_kerIdeal_le (q.app 1) π h (v.1 1)
  refine ⟨part1, fun h1 h2 => ?_, fun H' f hf => ?_⟩
  ·
    let Φ : G.omega →ₗ[k] Cot k C := cotMap π ∘ₗ G.omegaLevel 1
    have hΦ : Function.Surjective Φ :=
      (cotMap_surjective hπ).comp (G.omegaLevel_one_bijective hp).2
    have hker : LinearMap.ker Φ = LinearMap.range (omegaMap G H q) := by
      ext w
      rw [LinearMap.mem_ker]
      constructor
      · intro hw
        have hw' : AugCot.map (π : G.A 1 →ₐ[k] C) (BialgHomClass.counitAlgHom_comp π) (w.1 1) = 0 :=
          hw
        obtain ⟨x, hx⟩ := (AugCot.exact_kerMap_map (π : G.A 1 →ₐ[k] C)
          (BialgHomClass.counitAlgHom_comp π) hπ (w.1 1)).1 hw'
        have hx2 : dUnit (R := k) (x : G.A 1) = w.1 1 := by
          rw [← hx]; exact (AugCot.kerMap_apply _ _ x).symm
        have hxm : (x : G.A 1) ∈ kerIdeal (q.app 1) ⊔ augIdeal k (G.A 1) ^ 2 := h1 x.2
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hxm
        have hz0 : dUnit (R := k) z = 0 := by
          have hzI : z ∈ augIdeal k (G.A 1) := Ideal.pow_le_self two_ne_zero hz
          have hεz : counitAlgHom k (G.A 1) z = 0 := hzI
          rw [dUnit, AugCot.d_eq_zero_iff, hεz, map_zero, sub_zero]
          exact hz
        obtain ⟨u, hu⟩ := dUnit_mem_range_of_mem_kerIdeal (q.app 1) hy
        obtain ⟨v, rfl⟩ := (H.omegaLevel_one_bijective hp).2 u
        refine ⟨v, (G.omegaLevel_one_bijective hp).1 ?_⟩
        change cotMap (q.app 1) (H.omegaLevel 1 v) = w.1 1
        rw [hu, ← hx2, ← hyz]
        change dUnit (R := k) y = dUnit (R := k) (y + z)
        rw [show dUnit (R := k) (y + z) = dUnit (R := k) y + dUnit (R := k) z from map_add _ y z, hz0, add_zero]
      · intro hw
        exact part1 h2 w hw
    rw [← hker]
    exact (Φ.quotKerEquivOfSurjective hΦ).finrank_eq
  · rw [cotMap_comp]
    refine LinearMap.ext fun u => ?_
    obtain ⟨v, rfl⟩ := (H'.omegaLevel_one_bijective hp).2 u
    exact hf _ ⟨v, rfl⟩

end GlobalTheory.PDivGroup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentKernelEqCokerOmegaMapStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H) (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (π : G.A 1 →ₐc[k] C), Function.Surjective π → (kerIdeal (q.app 1) ≤ RingHom.ker π → ∀ w ∈ LinearMap.range (omegaMap G H q), cotMap π (w.1 1) = 0) ∧ (RingHom.ker π ≤ kerIdeal (q.app 1) ⊔ augIdeal k (G.A 1) ^ 2 → kerIdeal (q.app 1) ≤ RingHom.ker π → Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) = Module.finrank k (Cot k C)) ∧ ∀ (H' : PDivGroup p k) (f : G ⟶ H'), (∀ w ∈ LinearMap.range (omegaMap G H' f), cotMap π (w.1 1) = 0) → cotMap (π.comp (f.app 1)) = 0 := by
  first | exact @GlobalTheory.PDivGroup.cot_kernel_eq_coker_omegaMap | exact GlobalTheory.PDivGroup.cot_kernel_eq_coker_omegaMap | (intros; apply GlobalTheory.PDivGroup.cot_kernel_eq_coker_omegaMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearPDivGroupHomEvalTwoVariableSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearPDivGroupHomEvalTwoVariableSeries
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem semiHom_ev₂_pull2 : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → ∀ n t, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ t)) = (s.app n).two (c.ev₂ n t) := by
  intro p k k' _ _ σ d e G G' c c' s φ hφ n t
  have hev := GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k' e G' c' n
  let a : Fin d ⊕ Fin d → MvPowerSeries (Fin e ⊕ Fin e) k' :=
    Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j))
  have ha : ∀ i, constantCoeff (a i) = 0 := by
    intro i
    have hc := hev.2.2.2
    cases i with
    | inl j =>
      change constantCoeff (inL (φ j)) = 0
      rw [← hc, hev.1, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      change Coalgebra.counit (R := k') (c'.ev n (φ j)) = 0
      rw [hφ n j, (s.app n).counit_map, c.aug, map_zero]
    | inr j =>
      change constantCoeff (inR (φ j)) = 0
      rw [← hc, hev.2.1, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      change Coalgebra.counit (R := k') (c'.ev n (φ j)) = 0
      rw [hφ n j, (s.app n).counit_map, c.aug, map_zero]
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  let B := G'.A n ⊗[k'] G'.A n
  letI : Algebra k B := ((algebraMap k' B).comp σ).toAlgebra
  let u : G.A n →ₐ[k] B :=
    { ((Algebra.TensorProduct.includeLeft : G'.A n →ₐ[k'] B) : G'.A n →+* B).comp
        (s.app n).toRingHom with
      commutes' := fun r => by
        change Algebra.TensorProduct.includeLeft (R := k') (S := k') ((s.app n) (algebraMap k (G.A n) r)) = _
        rw [(s.app n).map_algebraMap, AlgHom.commutes]; rfl }
  let v : G.A n →ₐ[k] B :=
    { ((Algebra.TensorProduct.includeRight : G'.A n →ₐ[k'] B) : G'.A n →+* B).comp
        (s.app n).toRingHom with
      commutes' := fun r => by
        change Algebra.TensorProduct.includeRight (R := k') ((s.app n) (algebraMap k (G.A n) r)) = _
        rw [(s.app n).map_algebraMap, AlgHom.commutes]; rfl }
  let T : G.A n ⊗[k] G.A n →ₐ[k] B := Algebra.TensorProduct.lift u v (fun _ _ => Commute.all _ _)
  have hT : ∀ z, T z = (s.app n).two z := fun z => by
    induction z with
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | tmul x y =>
      rw [Algebra.TensorProduct.lift_tmul, TensorProduct.map_tmul]
      change ((s.app n) x ⊗ₜ[k'] 1) * (1 ⊗ₜ[k'] (s.app n) y) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]; rfl
  let L : MvPowerSeries (Fin d ⊕ Fin d) k →ₐ[k] B :=
    { (c'.ev₂ n).toRingHom.comp
        ((substAlgHom (R := k') hs).toRingHom.comp
          (MvPowerSeries.map σ)) with
      commutes' := fun r => by
        change c'.ev₂ n (substAlgHom (R := k') hs (MvPowerSeries.map σ (C r))) = algebraMap k' B (σ r)
        rw [MvPowerSeries.map_C, show (C (σ r) : MvPowerSeries (Fin d ⊕ Fin d) k') =
          algebraMap k' _ (σ r) by rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply],
          AlgHom.commutes, AlgHom.commutes] }
  have hL : ∀ f, L f = c'.ev₂ n (pull2 φ (MvPowerSeries.map σ f)) := fun f => by
    change c'.ev₂ n (substAlgHom hs (MvPowerSeries.map σ f)) = _
    rw [coe_substAlgHom]; rfl
  have key : T.comp (c.ev₂ n) = L := by
    refine GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k (Fin d ⊕ Fin d) B _ _ (fun i => ?_) (fun i => ?_)
    · rw [AlgHom.comp_apply]
      change IsNilpotent (T (evA k (c.x₂ n) (c.nil₂ n) (X i)))
      rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact (c.nil₂ n i).map T
    · rw [AlgHom.comp_apply, hL, hT, MvPowerSeries.map_X]
      change (s.app n).two (evA k (c.x₂ n) (c.nil₂ n) (X i)) = c'.ev₂ n (subst a (X i))
      rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate, subst_X hs]
      cases i with
      | inl j =>
        change (s.app n).two (c.x n j ⊗ₜ 1) = c'.ev₂ n (inL (φ j))
        rw [hev.1, hφ n j, TensorProduct.map_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply]
        congr 1; exact map_one (s.app n).toRingHom
      | inr j =>
        change (s.app n).two (1 ⊗ₜ c.x n j) = c'.ev₂ n (inR (φ j))
        rw [hev.2.1, hφ n j, TensorProduct.map_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply]
        congr 1; exact map_one (s.app n).toRingHom
  rw [← hL, ← key, AlgHom.comp_apply, hT]

end GlobalTheory.Katz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearPDivGroupHomEvalTwoVariableSeriesStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearPDivGroupHom_eval_two_variable_series : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → ∀ n t, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ t)) = (s.app n).two (c.ev₂ n t) := by
  first | exact @GlobalTheory.Katz.semiHom_ev₂_pull2 | exact GlobalTheory.Katz.semiHom_ev₂_pull2 | (intros; apply GlobalTheory.Katz.semiHom_ev₂_pull2 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientKernelSupFrobeniusKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientKernelSupFrobeniusKernel
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDiv.FrobKerInter

theorem isHopfIdeal_sup {k A : Type} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (I J : Ideal A) [I.IsHopfIdeal k] [J.IsHopfIdeal k] : (I ⊔ J).IsHopfIdeal k := by
  refine Ideal.IsHopfIdeal.mk (toIsCoideal := ⟨?_, ?_⟩) ?_
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have h1 := Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars k) hy
    have h2 := Submodule.IsCoideal.counit_eq_zero (I := J.restrictScalars k) hz
    rw [map_add (f := _), h1, h2, add_zero]
  · intro x hx
    set K := (I ⊔ J).restrictScalars k
    have key : ∀ (L : Ideal A) [L.IsHopfIdeal k], L ≤ I ⊔ J → ∀ y ∈ L,
        TensorProduct.map K.mkQ K.mkQ (comul (R := k) y) = 0 := by
      intro L _ hL y hy
      have hle : L.restrictScalars k ≤ K := fun a ha => hL ha
      have e : K.mkQ = (Submodule.mapQ (L.restrictScalars k) K LinearMap.id hle) ∘ₗ
          (L.restrictScalars k).mkQ := by
        rw [Submodule.mapQ_mkQ, LinearMap.comp_id]
      rw [e, TensorProduct.map_comp, LinearMap.comp_apply,
        Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := L.restrictScalars k) hy, map_zero]
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _), map_add (f := _), key I le_sup_left y hy, key J le_sup_right z hz, add_zero]
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (Ideal.IsHopfIdeal.antipode_mem (R := k) hy)
      (Ideal.IsHopfIdeal.antipode_mem (R := k) hz)

theorem exists_quotient_kerIdeal_sup_frobKerIdeal : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), ∃ (C : Type) (_ : CommRing C) (_ : HopfAlgebra k C) (_ : IsCocomm k C) (_ : Module.Finite k C) (π : G.A 1 →ₐc[k] C), Function.Surjective π ∧ RingHom.ker π = kerIdeal (q.app 1) ⊔ frobKerIdeal p k (G.A 1) ∧ (∀ a ∈ augIdeal k C, a ^ p = 0) ∧ frobKerIdeal p k (G.A 1) ≤ augIdeal k (G.A 1) ^ 2 := by
  intro p hp k _ _ G H q
  have : (kerIdeal (q.app 1)).IsHopfIdeal k := isHopfIdeal_kerIdeal_of_bialgHom k _ _ (q.app 1)
  have : (frobKerIdeal p k (G.A 1)).IsHopfIdeal k := by
    let J := frobKerIdeal p k (G.A 1)
    let f := Ideal.Quotient.mkₐ k J
    refine Ideal.IsHopfIdeal.mk (toIsCoideal := ⟨?_, ?_⟩) ?_
    · exact frobKerIdeal_le_augIdeal hp.out.ne_zero k (G.A 1)
    · intro x hx
      have h : J ≤ RingHom.ker
          ((Algebra.TensorProduct.map f f).comp (comulAlgHom k (G.A 1))) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, AlgHom.comp_apply,
          FrobKerOrder.map_pow_eq, comulAlgHom_apply, rTensor_counit_comul,
          TensorProduct.lid_tmul, one_smul, ← map_pow]
        have hpow : f (a ^ p) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
        rw [hpow, tmul_zero]
      exact h hx
    · intro x hx
      have h : J ≤ J.comap (HopfAlgebra.antipodeAlgHom k (G.A 1)) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap, map_pow]
        apply pow_mem_frobKerIdeal
        have ha' : counit (R := k) a = 0 := ha
        simp [RingHom.mem_ker, ha']
      exact h hx
  set I := kerIdeal (q.app 1) ⊔ frobKerIdeal p k (G.A 1) with hI
  have : I.IsHopfIdeal k := isHopfIdeal_sup _ _
  let π : G.A 1 →ₐc[k] G.A 1 ⧸ I := Bialgebra.Quotient.mkBialgHom I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have : Module.Finite k (G.A 1) := G.finite 1
  refine ⟨G.A 1 ⧸ I, inferInstance, inferInstance, KerGrp.isCocomm_of_surjective π hπ,
    Module.Finite.of_surjective (π : G.A 1 →ₗ[k] G.A 1 ⧸ I) hπ, π, hπ,
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem, ?_, FrobKerOrder.le_sq p k (G.A 1)⟩
  intro a ha
  obtain ⟨b, rfl⟩ := hπ a
  have hb : b ∈ augIdeal k (G.A 1) := ha
  change Ideal.Quotient.mk I b ^ p = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (pow_mem_frobKerIdeal hb)

end GlobalTheory.PDiv.FrobKerInter
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientKernelSupFrobeniusKernelStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_kernel_sup_frobeniusKernel : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), ∃ (C : Type) (_ : CommRing C) (_ : HopfAlgebra k C) (_ : IsCocomm k C) (_ : Module.Finite k C) (π : G.A 1 →ₐc[k] C), Function.Surjective π ∧ RingHom.ker π = kerIdeal (q.app 1) ⊔ frobKerIdeal p k (G.A 1) ∧ (∀ a ∈ augIdeal k C, a ^ p = 0) ∧ frobKerIdeal p k (G.A 1) ≤ augIdeal k (G.A 1) ^ 2 := by
  first | exact @GlobalTheory.PDiv.FrobKerInter.exists_quotient_kerIdeal_sup_frobKerIdeal | exact GlobalTheory.PDiv.FrobKerInter.exists_quotient_kerIdeal_sup_frobKerIdeal | (intros; apply GlobalTheory.PDiv.FrobKerInter.exists_quotient_kerIdeal_sup_frobKerIdeal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothDimTensor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdDim

theorem smoothDim_tensor {S : Scheme.{0}} {A B : Over S} {g g' : ℕ} (hg : SmoothOfRelativeDimension g A.hom)
    (hg' : SmoothOfRelativeDimension g' B.hom) : SmoothOfRelativeDimension (g' + g) (A ⊗ B).hom := by
  have : SmoothOfRelativeDimension g' (Limits.pullback.fst A.hom B.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback
      (IsPullback.of_hasPullback A.hom B.hom).flip hg'
  rw [Over.tensorObj_hom]
  exact smoothOfRelativeDimension_comp g' g _ _

theorem g_eq_add : ∀ (S : Scheme.{0}) (P P₁ P₂ : PolAV S) (a₁ : P.A ⟶ P₁.A) (a₂ : P.A ⟶ P₂.A),
    Nonempty S → IsIso (lift a₁ a₂) → P.g = P₁.g + P₂.g := by
  intro S P P₁ P₂ a₁ a₂ ⟨s⟩ hi
  have h := smoothDim_tensor P₁.smoothDim P₂.smoothDim
  haveI : IsIso (lift a₁ a₂).left := inferInstanceAs (IsIso ((Over.forget S).map (lift a₁ a₂)))
  have hw : (lift a₁ a₂).left ≫ (P₁.A ⊗ P₂.A).hom = P.A.hom := Over.w _
  have h2 : SmoothOfRelativeDimension (0 + (P₂.g + P₁.g)) P.A.hom := by
    rw [← hw]
    exact smoothOfRelativeDimension_comp 0 (P₂.g + P₁.g) _ _
  have := ReciprocityTheory.ChartRestriction.G.H1.dim_unique P.A.hom P.smoothDim h2 (eSec P.A s)
  omega

end GlobalTheory.ProdDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePowerSeriesSemilinearPDivGroupHomCha
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePowerSeriesSemilinearPDivGroupHomCha
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace Katz

theorem existsUnique_semiHom_ev (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k')
    (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e)
    (s : SemiHom σ G' G) :
    ∃! φ : Fin d → MvPowerSeries (Fin e) k', ∀ n j, c'.ev n (φ j) = s.app n (c.x n j) := by
  have h := fun j : Fin d => existsUnique_evA_eq_of_presents k' (Fin e) G'.A c'.x c'.nil
    (fun n => (G'.res n : G'.A (n + 1) →ₐ[k'] G'.A n)) c'.res c'.presents
    (fun n => s.app n (c.x n j)) (fun n => by
      change G'.res n (s.app (n + 1) (c.x (n + 1) j)) = _
      rw [s.res_app, c.res])
  choose φ hφ hu using h
  refine ⟨φ, fun n j => hφ j n, fun ψ hψ => funext fun j => hu j (ψ j) fun n => hψ n j⟩

end Katz

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePowerSeriesSemilinearPDivGroupHomChaStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_powerSeries_semilinear_pDivGroupHom_chart : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G), ∃! φ : Fin d → MvPowerSeries (Fin e) k', ∀ n j, c'.ev n (φ j) = s.app n (c.x n j) := by
  first | (exact @GlobalTheory.Katz.existsUnique_semiHom_ev) | (exact GlobalTheory.Katz.existsUnique_semiHom_ev) | (intros; apply GlobalTheory.Katz.existsUnique_semiHom_ev  <;> assumption)
end
end
