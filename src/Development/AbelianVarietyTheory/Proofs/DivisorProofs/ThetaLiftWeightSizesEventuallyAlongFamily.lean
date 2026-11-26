module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoThreeOfOfDeterminantCharacterFiniteOrderType
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKtypeKilledByCompactRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKtypeHolomorphicKilledByLoweringRoots
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftWeightSizesEventuallyAlongFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftWeightSizesEventuallyAlongFamily
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow

theorem weightSizes_along : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x →
    ∀ (i : Fm.Ix x) j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := by
  intro eps Fm
  obtain ⟨x0, h0⟩ := GlobalTheory.ShNums.size_rel Fm
  refine ⟨x0, fun x hx1 hx i j => ?_⟩
  obtain ⟨-, -, -, heta, hw, h4, h2b, -, hw1, hsum⟩ := h0 x hx hx1 i
  have SZ := Fm.sizes x hx1 i
  have P := Fm.params x hx1 i
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -, -⟩ := SZ
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have he := L.etaSz_pos
  have hSc := L.Sc_pos
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'.le (by linarith)
  have hq0 : 0 < L.sc.b' / L.sc.x := div_pos hb' hxp
  have hwj : ∀ τ, wj D (j.1 + 1) τ = (((D.hc τ).e j : ℚ) : ℝ) := by
    intro τ
    unfold wj
    rw [dite_eq_left (by omega)]
    rfl
  have hwin : ∀ τ, 0 < wj D (j.1 + 1) τ ∧ wj D (j.1 + 1) τ ≤ 2 * L.sc.b := by
    intro τ
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have := L.win_thick (j.1 + 1) (by omega) (by omega) τ h1
      constructor <;> linarith [this.1, this.2]
    by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have a := L.win_top (j.1 + 1) (by omega) (by omega) τ ⟨t, ht⟩ e.symm
      have a3 := L.bT_ge ⟨t, ht⟩
      have a4 := GlobalTheory.Ggeo.bT_le_five_quarters P ⟨t, ht⟩
      constructor <;> linarith [a.1, a.2]
    · have a := L.win_thin (j.1 + 1) (by omega) (by omega) τ ⟨(D.eTau τ).2, h2, h1⟩
      constructor <;> linarith [a.1, a.2]
  refine ⟨fun τ => ⟨?_, ?_, fun l => ?_, fun l => ?_⟩, fun l => (hG l l).1⟩
  · rw [← hwj]; exact (hwin τ).1
  · rw [← hwj]; exact (hwin τ).2
  · have := L.cloud_v τ l
    exact ⟨this.1, by linarith [this.2]⟩
  · have := L.be_close τ l j
    push_cast at this
    linarith

end GlobalTheory.LowRow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftWeightSizesEventuallyAlongFamilyStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_weightSizes_eventually_along_family : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ (i : Fm.Ix x) j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := by
  first | exact @GlobalTheory.LowRow.weightSizes_along | exact GlobalTheory.LowRow.weightSizes_along | (intros; apply GlobalTheory.LowRow.weightSizes_along <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryOfFrameNormConj
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing
open scoped ComplexConjugate

namespace GlobalTheory

section Points

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {B : LB Y}

theorem CxPts.mem_ptsIn_conj {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    {U : Y.Opens} (hy : y ∈ ptsIn p σ U) : y' ∈ ptsIn p σ' U := by
  change ⊤ ≤ y'.1 ⁻¹ᵁ U
  rw [h]
  exact fun x _ => hy (Set.mem_univ _)

end Points

theorem mem_unitaryGroup_of_norm_mulVec {α : Type*} [Fintype α] [DecidableEq α] {V : Matrix α α ℂ}
    (h : ∀ w : α → ℂ, √(∑ i, ‖V.mulVec w i‖ ^ 2) = √(∑ i, ‖w i‖ ^ 2)) : V ∈ Matrix.unitaryGroup α ℂ := by
  have key := (LinearMap.norm_map_iff_inner_map_map (Matrix.toEuclideanLin V)).1 fun x => by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    exact h x.ofLp
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have := key (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  simpa [PiLp.inner_apply, Matrix.mul_apply, Matrix.one_apply, mul_comm, Pi.single_apply, eq_comm] using this

theorem exists_unitary_of_frameNorm_conj {N : ℕ} {M M' : Matrix (Fin N) (Fin N) ℂ} (hM : M.det ≠ 0)
    (hM' : M'.det ≠ 0) (h : ∀ x : Fin N → ℂ, frameNorm M' (fun j => conj (x j)) = frameNorm M x) :
    ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, M' = M.map (starRingEnd ℂ) * U := by
  have hV : M'⁻¹ * M.map (starRingEnd ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    mem_unitaryGroup_of_norm_mulVec fun w => by
      have := h (M.mulVec fun j => conj (w j))
      have e : (fun j => conj (M.mulVec (fun j => conj (w j)) j)) = (M.map (starRingEnd ℂ)).mulVec w :=
        funext fun j => by simp [Matrix.mulVec, dotProduct]
      rw [e, frameNorm, frameNorm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul M hM.isUnit, Matrix.one_mulVec] at this
      simpa only [RCLike.norm_conj] using this
  refine ⟨_, Unitary.star_mem hV, ?_⟩
  have e : M.map (starRingEnd ℂ) = M' * (M'⁻¹ * M.map (starRingEnd ℂ)) := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv M' hM'.isUnit, Matrix.one_mul]
  generalize M'⁻¹ * M.map (starRingEnd ℂ) = V at e hV
  rw [e, Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff.1 hV, Matrix.mul_one]

variable {F : Type} [Field F] [NumberField F]

theorem Adelic.HermSys.isConj_weight (T : Adelic.HermSys F) (hb : T.BasePointFree) (hh : T.Hermitian)
    (hc : T.ConjInvariant) (σ : F →+* ℂ) :
    (T.weight hb hh σ).IsConj (T.weight hb hh (ComplexEmbedding.conjugate σ)) := by
  obtain ⟨U, hU, e⟩ := exists_unitary_of_frameNorm_conj (hh σ) (hh (ComplexEmbedding.conjugate σ)) (hc σ)
  exact Weight.isConj_fsBasis_of_unitary _ _ _ _ _ hU e

namespace HilbertSamuel.Geo

variable (G : Geo F)

theorem isConj_φ₂ (σ : F →+* ℂ) : (G.φ₂ σ).IsConj (G.φ₂ (ComplexEmbedding.conjugate σ)) :=
  G.second.isConj_weight _ _ G.conj₂ σ

variable {G}

end HilbertSamuel.Geo

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvariantChartSetLeMulFundamentalSet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvariantChartSetLeMulFundamentalSet
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.Unfold

theorem lintegral_chart_le_mul_fundSet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 x : Frame X.Ψ r) (FF A : Set (V (nd X))) (m : ℝ≥0∞) (Φ : Frame X.Ψ r → ℝ≥0∞), IsOrth X x0 → IsOrth X x → IsFundSet X x0 FF → MeasurableSet A → A ⊆ OmF X x → Measurable Φ → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Φ (lact γ x) = Φ x) → (∀ b ∈ Bor X.Ψ r, ∀ x ∈ X.dom, Φ (rmul x b) = Φ x) → (({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ A, ∃ z' ∈ A, ∃ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b}.encard : ℝ≥0∞) ≤ m) → ∫⁻ z in A, Φ (cpt X x z) ∂(muF X x) ≤ m * ∫⁻ z in FF, Φ (cpt X x0 z) ∂(muF X x0) := by
  intro E _ _ _ r X x0 x FF A m Φ ho0 ho hF hA hAO hΦ hΓ hB hm
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hM := ReciprocityTheory.ChartRestriction.G.AR.Up.measInv_holds (E := E)
  have hc : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  let ψ : Frame X.Ψ r → ℝ≥0∞ := (satFrames X x A).indicator Φ
  have hψ : Measurable ψ := hΦ.indicator (measurableSet_satFrames X ho hA hAO)
  have hψB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y := by
    intro y hy b hb
    simp only [ψ, Set.indicator, rmul_mem_satFrames_iff X x A _ hb, hB b hb y hy]
  have h1 : ∫⁻ z in A, Φ (cpt X x z) ∂muF X x = ∫⁻ z, ψ (cpt X x z) ∂muF X x := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun z => ?_
    simp only [ψ, Set.indicator, cpt_mem_satFrames_iff X ho]
  rw [h1, ← hM r X x0 x ho0 ho ψ hψ hψB, lintegral_unfold hM r X x0 ho0 FF hF ψ hψ hψB,
    ← lintegral_const_mul m (f := fun z => Φ (cpt X x0 z)) (hΦ.comp hc)]
  refine setLIntegral_mono ((hΦ.comp hc).const_mul m) fun z hz => ?_
  set y := cpt X x0 z with hy_def
  have hy : y ∈ X.dom := hF.2.1 hz
  let S : Set (GL (Fin r) E) := {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ A, ∃ z' ∈ A, ∃ b ∈ Bor X.Ψ r,
    lact γ (cpt X x z) = rmul (cpt X x z') b}
  let T : Set X.Γ := {γ | lact γ.1 y ∈ satFrames X x A}
  by_cases hT : T.Nonempty
  swap
  · have h0 : ∀ γ : X.Γ, ψ (lact γ.1 y) = 0 := fun γ =>
      Set.indicator_of_notMem (s := satFrames X x A) (fun h => hT ⟨γ, h⟩) Φ
    simp [h0]
  obtain ⟨γ0, hγ0⟩ := hT
  obtain ⟨z0, hz0, b0, hb0, e0⟩ := hγ0
  have hpt : ∀ γ : X.Γ, ψ (lact γ.1 y) ≤ T.indicator (fun _ => Φ y) γ := by
    intro γ
    by_cases hγ : γ ∈ T
    · rw [Set.indicator_of_mem hγ]
      show (satFrames X x A).indicator Φ _ ≤ _
      rw [Set.indicator_of_mem (s := satFrames X x A) hγ Φ, hΓ γ.1 γ.2 y hy]
    · rw [Set.indicator_of_notMem hγ]
      exact le_of_eq (Set.indicator_of_notMem (s := satFrames X x A) hγ Φ)
  have hTS : T.encard ≤ S.encard := by
    let f : X.Γ → GL (Fin r) E := fun γ => γ.1 * γ0.1⁻¹
    have hinj : Set.InjOn f T := fun a _ b _ h => Subtype.ext (mul_right_cancel h)
    rw [← hinj.encard_image]
    refine Set.encard_le_encard ?_
    rintro _ ⟨γ, ⟨z1, hz1, b1, hb1, e1⟩, rfl⟩
    refine ⟨X.Γ.mul_mem γ.2 (X.Γ.inv_mem γ0.2), z0, hz0, z1, hz1,
      rmul b1 (ExtFPf.invF X b0), ExtFPf.mul_mem X hb1 (ExtFPf.invF_mem X hb0), ?_⟩
    have e0' : cpt X x z0 = rmul (lact γ0.1 y) (ExtFPf.invF X b0) := by
      rw [e0, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb0, ExtFPf.rmul_oneF]
    show lact (γ.1 * γ0.1⁻¹) (cpt X x z0) = _
    rw [e0', FundSetPf.lact_rmul, FundSetPf.lact_mul, FundSetPf.lact_inv, e1, ExtFPf.rmul_assoc]
  calc ∑' γ : X.Γ, ψ (lact γ.1 y) ≤ ∑' γ : X.Γ, T.indicator (fun _ => Φ y) γ := ENNReal.tsum_le_tsum hpt
    _ = (T.encard : ℝ≥0∞) * Φ y := by rw [← tsum_subtype, ENNReal.tsum_set_const]
    _ ≤ m * Φ y := by
      gcongr
      exact le_trans (by exact_mod_cast hTS) hm

end GlobalTheory.Unfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvariantChartSetLeMulFundamentalSetStatement
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_invariant_chartSet_le_mul_fundamentalSet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 x : Frame X.Ψ r) (FF A : Set (V (nd X))) (m : ℝ≥0∞) (Φ : Frame X.Ψ r → ℝ≥0∞), IsOrth X x0 → IsOrth X x → IsFundSet X x0 FF → MeasurableSet A → A ⊆ OmF X x → Measurable Φ → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Φ (lact γ x) = Φ x) → (∀ b ∈ Bor X.Ψ r, ∀ x ∈ X.dom, Φ (rmul x b) = Φ x) → (({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ A, ∃ z' ∈ A, ∃ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b}.encard : ℝ≥0∞) ≤ m) → ∫⁻ z in A, Φ (cpt X x z) ∂(muF X x) ≤ m * ∫⁻ z in FF, Φ (cpt X x0 z) ∂(muF X x0) := by
  first | exact @GlobalTheory.Unfold.lintegral_chart_le_mul_fundSet | exact GlobalTheory.Unfold.lintegral_chart_le_mul_fundSet | (intros; apply GlobalTheory.Unfold.lintegral_chart_le_mul_fundSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeCharMulInv
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistFactorProof

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct

def WeilUnique (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f

def WeilChange (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT νS νT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    IsHeckeChar D νS → IsHeckeChar D νT → ResEta D νS 0 → ResEta D νT 0 →
    ∃ om', IsWeilDatumO ψ S T (χS * νS) (χT * νT) om' ∧ ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y →
      om' (g, h) = ((((νT x)⁻¹ * νS y : Circle) : ℂ)) • om (g, h)

variable {D : D7}

theorem isHeckeChar_mul_inv {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) :
    IsHeckeChar D (χ * η⁻¹) :=
  ⟨hχ.1.mul hη.1.inv, fun x => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχ.2, hη.2, inv_one, mul_one]⟩

theorem isDetRoot_one (V : HSp D) : IsDetRoot V 1 1 := by
  unfold IsDetRoot
  rw [map_one, Units.val_one, Units.val_one, Matrix.det_one, map_one, one_mul]

theorem weil_ratio (hU : WeilUnique D) (hC : WeilChange D) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT χS' χT' : (AE D)ˣ →* Circle} {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (ho : IsWeilDatumO ψ S T χS χT om) (ho' : IsWeilDatumO ψ S T χS' χT' om') {g : GA D S} {h : GA D T}
    {x y : (AE D)ˣ} (hx : IsDetRoot S g x) (hy : IsDetRoot T h y) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om' (g, h) f = ((((χT' x * (χT x)⁻¹)⁻¹ * (χS' y * (χS y)⁻¹) : Circle) : ℂ)) • om (g, h) f := by
  obtain ⟨o, h1, h2⟩ := hC ψ ho.std S T χS χT (χS' * χS⁻¹) (χT' * χT⁻¹) om ho
    (isHeckeChar_mul_inv ho'.hecS ho.hecS) (isHeckeChar_mul_inv ho'.hecT ho.hecT)
    (resEta_parity (resEta_mul ho'.resS (resEta_inv ho.resS)) (by omega))
    (resEta_parity (resEta_mul ho'.resT (resEta_inv ho.resT)) (by omega))
  have e : ∀ a b : (AE D)ˣ →* Circle, a * (b * a⁻¹) = b := fun a b => by
    ext1 z
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_comm (b z), mul_inv_cancel_left]
  rw [e, e] at h1
  rw [hU ψ ho.std S T χS' χT' om' o ho' h1 _ f hf, h2 g h x y hx hy]
  rfl

theorem vac_ne_zero {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) : f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, hn⟩ := h.2.norm
  have := hn p hp
  simp [nrm2] at this

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem frame_ratio (hU : WeilUnique D) (hC : WeilChange D) (hω : R.thP_ωP) (i : Fin D.R.m) (t t' : T0)
    {h : GA D (Wc D i)} {x : (AE D)ˣ} (hx : IsDetRoot (Wc D i) h x) {f : WO (Vc D i) (Wc D i) → ℂ}
    (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f) :
    ((R.xi t x : Circle) : ℂ) • R.ωP i t' (1, h) f = ((R.xi t' x : Circle) : ℂ) • R.ωP i t (1, h) f := by
  rw [weil_ratio hU hC (hω i t) (hω i t') (isDetRoot_one _) hx hf, smul_smul, ← Circle.coe_mul]
  congr 2
  show R.xi t x * (_ * (R.mu0 _ x * R.xi t' x * (R.mu0 _ x * R.xi t x)⁻¹)) = _
  rw [map_one, map_one, mul_inv_cancel, inv_one, one_mul, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul,
    mul_comm (R.xi t' x), mul_inv_cancel_left]

end GlobalTheory.TwistFactorProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorTestFamilyPreservesLevelForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorTestFamilyPreservesLevelForms
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem levOp_id_mem_inf_fixed {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K K' : Subgroup G) (F : G → ℂ) (hF : ∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x)
    (M : Submodule ℂ V) (hM : ∀ g, ∀ v ∈ M, ρ g v ∈ M) (v : V) (hv : v ∈ M ⊓ fixed ρ K') :
    levOp ρ K K' F LinearMap.id v ∈ M ⊓ fixed ρ K' := by
  obtain ⟨hvM, hvK⟩ := Submodule.mem_inf.1 hv
  have hfix : ∀ k ∈ K', ρ k v = v := fun k hk => by simpa using hvK ⟨k, hk⟩
  set φ : G ⧸ K' → V →ₗ[ℂ] V := fun q => F q.out • (ρ q.out ∘ₗ LinearMap.id) with hφ
  unfold levOp
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  by_cases hs : (Function.support φ).Finite
  · have hs' : (Function.support fun q => φ q v).Finite :=
      hs.subset (fun q hq h => hq (by simp [h]))
    have happ : (∑ᶠ q, φ q) v = ∑ᶠ q, φ q v := map_finsum (LinearMap.applyₗ v) hs
    rw [happ]
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [finsum_eq_sum _ hs']
      exact Submodule.sum_mem _ fun q _ => M.smul_mem _ (hM _ _ hvM)
    · intro k
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      rw [map_finsum (ρ (k : G)) hs']
      have key : ∀ q : G ⧸ K', ρ (k : G) (φ q v) = φ ((k : G) • q) v := by
        intro q
        have hq : ((((k : G) • q).out : G) : G ⧸ K') = ((k : G) * q.out : G) := by
          rw [QuotientGroup.out_eq']
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rfl
        have hk2 : ((k : G) * q.out)⁻¹ * ((k : G) • q).out ∈ K' := QuotientGroup.eq.1 hq.symm
        obtain ⟨c, hc, hg'⟩ : ∃ c ∈ K', ((k : G) • q).out = (k : G) * q.out * c := ⟨_, hk2, by group⟩
        simp only [hφ, LinearMap.smul_apply, LinearMap.comp_id, map_smul]
        rw [hg', (hF _ hc _).2, (hF _ k.2 _).1, map_mul, Module.End.mul_apply, hfix _ hc, map_mul,
          Module.End.mul_apply]
      rw [finsum_congr key]
      exact finsum_comp_equiv (MulAction.toPerm (k : G)) (f := fun q => φ q v)
  · rw [finsum_of_infinite_support hs]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem toSub_mul_left_eq {w : Pl E} {U : Subgroup (UL n w)} (g : UL n w → ℂ) (hg : ∀ k ∈ U, ∀ x, g (k * x) = g x)
    (a : UL n w) (ha : a ∈ U) (y : GLw n w) : g (toSub (UL n w) (a.1 * y)) = g (toSub (UL n w) y) := by
  unfold toSub
  by_cases hy : y ∈ UL n w
  · rw [dite_eq_left (mul_mem a.2 hy), dite_eq_left hy, ← hg a ha ⟨y, hy⟩]
    rfl
  · have : a.1 * y ∉ UL n w := fun h => hy (by simpa using mul_mem (inv_mem a.2) h)
    rw [dite_eq_right this, dite_eq_right hy]

theorem toSub_mul_right_eq {w : Pl E} {U : Subgroup (UL n w)} (g : UL n w → ℂ) (hg : ∀ k ∈ U, ∀ x, g (x * k) = g x)
    (a : UL n w) (ha : a ∈ U) (y : GLw n w) : g (toSub (UL n w) (y * a.1)) = g (toSub (UL n w) y) := by
  unfold toSub
  by_cases hy : y ∈ UL n w
  · rw [dite_eq_left (mul_mem hy a.2), dite_eq_left hy, ← hg a ha ⟨y, hy⟩]
    rfl
  · have : y * a.1 ∉ UL n w := fun h => hy (by simpa using mul_mem h (inv_mem a.2))
    rw [dite_eq_right this, dite_eq_right hy]

theorem mem_globLev_iff (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (k : finU (E := E) (n := n)) :
    k ∈ globLev S K' ↔ ∀ w ∈ S, ∃ a ∈ K' w, (a : GLw n w) = cLoc w k.1 := by
  simp [globLev, Subgroup.mem_iInf]

theorem globFn_inv (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ)
    (hf : ∀ w, ∀ k ∈ K' w, ∀ x, f w (k * x) = f w x ∧ f w (x * k) = f w x) :
    ∀ k ∈ globLev S K', ∀ x, globFn S f (k * x) = globFn S f x ∧ globFn S f (x * k) = globFn S f x := by
  intro k hk x
  rw [mem_globLev_iff] at hk
  constructor
  · unfold globFn
    refine finprod_mem_congr rfl fun w hw => ?_
    obtain ⟨a, ha, hae⟩ := hk w hw
    rw [Subgroup.coe_mul, map_mul, ← hae]
    exact toSub_mul_left_eq (f w) (fun k hk x => (hf w k hk x).1) a ha _
  · unfold globFn
    refine finprod_mem_congr rfl fun w hw => ?_
    obtain ⟨a, ha, hae⟩ := hk w hw
    rw [Subgroup.coe_mul, map_mul, ← hae]
    exact toSub_mul_right_eq (f w) (fun k hk x => (hf w k hk x).2) a ha _

end GlobalTheory.BCT


open GlobalTheory.BCT in
theorem GlobalTheory.BCT.hop_mem_inf_fixed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ v ∈ π ⊓ fixed (RF E n) (globLev S K'), hop S K' f v ∈ π ⊓ fixed (RF E n) (globLev S K') := by
  intro E _ _ _ n S _ K' _ f hf π hπ v hv
  exact levOp_id_mem_inf_fixed (RF E n) _ _ _ (globFn_inv S K' f fun w => (hf.1 w).2) π
    (fun g v hv => hπ.stable _ v hv) v hv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorTestFamilyPreservesLevelFormsStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperator_testFamily_preserves_level_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ v ∈ π ⊓ fixed (RF E n) (globLev S K'), hop S K' f v ∈ π ⊓ fixed (RF E n) (globLev S K') := by
  first | exact @GlobalTheory.BCT.hop_mem_inf_fixed | exact GlobalTheory.BCT.hop_mem_inf_fixed | (intros; apply GlobalTheory.BCT.hop_mem_inf_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameBorelActsExtremalVectorByWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameBorelActsExtremalVectorByWeight
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.VKill

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem conj_exp {P : Mt n} (hP : IsUnit P) (X : Mt n) (t : ℝ) :
    P * NormedSpace.exp (t • X) * P⁻¹ = NormedSpace.exp (t • (P * X * P⁻¹)) := by
  rw [← Matrix.exp_conj P _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem dRep_conj {P : Mt n} (hP : IsUnit P) (σ : Mt n → (H →L[ℂ] H)) (X : Mt n) (v : H) :
    dRep (fun g => σ (P * g * P⁻¹)) X v = dRep σ (P * X * P⁻¹) v := by
  unfold dRep
  simp only [conj_exp hP]

theorem conjH_conj {P : Mt n} (hP : IsUnit P) (J Z : Mt n) :
    conjH (Pᴴ * J * P) (P⁻¹ * Z * P) = P⁻¹ * conjH J Z * P := by
  have hd : IsUnit Pᴴ.det := by
    rw [det_conjTranspose]; exact ((Matrix.isUnit_iff_isUnit_det _).1 hP).star
  have h1 : (Pᴴ)⁻¹ * Pᴴ = 1 := Matrix.nonsing_inv_mul _ hd
  have h2 : ∀ Y : Mt n, (Pᴴ)⁻¹ * (Pᴴ * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  unfold conjH
  simp only [Matrix.mul_inv_rev, conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc, h2, Matrix.mul_neg,
    Matrix.neg_mul]

theorem dRepC_conj {P : Mt n} (hP : IsUnit P) (J : Mt n) (σ : Mt n → (H →L[ℂ] H)) (Z : Mt n) (v : H) :
    dRepC (Pᴴ * J * P) (fun g => σ (P * g * P⁻¹)) (P⁻¹ * Z * P) v = dRepC J σ Z v := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : ∀ (c : ℂ) (Y : Mt n), P * (c • (P⁻¹ * Y * P)) * P⁻¹ = c • Y := fun c Y => by
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1,
      Matrix.mul_one]
  unfold dRepC
  rw [dRep_conj hP, dRep_conj hP, conjH_conj hP, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.sub_mul, ← Matrix.mul_sub,
    h2, h2]

theorem conj_prod {P : Mt n} (hP : IsUnit P) (l : List (Mt n)) :
    P * l.prod * P⁻¹ = (l.map fun g => P * g * P⁻¹).prod := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  induction l with
  | nil => simp [Matrix.mul_nonsing_inv _ hd]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ← ih]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P⁻¹ P, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]

theorem smooth_conj {P : Mt n} (hP : IsUnit P) (J : Mt n) (σ : Mt n → (H →L[ℂ] H)) (v : H)
    (h : SmoothVec (lieH (Pᴴ * J * P)) (fun g => σ (P * g * P⁻¹)) v) : SmoothVec (lieH J) σ v := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : ∀ Y : Mt n, P * (P⁻¹ * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hd : IsUnit Pᴴ.det := by
    rw [det_conjTranspose]; exact ((Matrix.isUnit_iff_isUnit_det _).1 hP).star
  have h3 : (Pᴴ)⁻¹ * Pᴴ = 1 := Matrix.nonsing_inv_mul _ hd
  have h4 : ∀ Y : Mt n, (Pᴴ)⁻¹ * (Pᴴ * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  intro k Xs hX
  have := h k (fun i => P⁻¹ * Xs i * P) (fun i => by
    have e : (Xs i)ᴴ * J + J * Xs i = 0 := hX i
    show (P⁻¹ * Xs i * P)ᴴ * (Pᴴ * J * P) + (Pᴴ * J * P) * (P⁻¹ * Xs i * P) = 0
    have e2 : (P⁻¹ * Xs i * P)ᴴ * (Pᴴ * J * P) + (Pᴴ * J * P) * (P⁻¹ * Xs i * P) =
        Pᴴ * ((Xs i)ᴴ * J + J * Xs i) * P := by
      simp only [conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc, h2, h4, Matrix.mul_add, Matrix.add_mul]
    rw [e2, e, Matrix.mul_zero, Matrix.zero_mul])
  simp only [conj_prod hP, List.map_ofFn, Function.comp_def, conj_exp hP] at this
  simp only [Matrix.mul_assoc, h2, h1, Matrix.mul_one] at this
  exact this

theorem jm_herm (ε : Fin n → Bool) : (Formalism.REAL.Jm ε).IsHermitian := by
  unfold Formalism.REAL.Jm
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  funext a
  by_cases h : ε a <;> simp [h]

theorem jm_det (ε : Fin n → Bool) : (Formalism.REAL.Jm ε).det ≠ 0 := by
  unfold Formalism.REAL.Jm
  rw [det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  by_cases h : ε a <;> simp [h]

theorem borel_extVec (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec) (_hθ : IsInfFam θ) (hM : HolShape M) (hw : WtIs M w) (hv : IsExtVec M v)
    (τ : D.what₂.Tau) :
    SmoothVec (lieH (gramAt D V τ)) (M.rep τ) (v τ : M.H τ) ∧ ∀ a c : Fin V.rank, a ≤ c →
      dRepC (gramAt D V τ) (M.rep τ) (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (v τ : M.H τ) =
        if a = c then (w τ a : ℂ) • (v τ : M.H τ) else 0 := by
  obtain ⟨hc, hU, -, hx⟩ := GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ
  obtain ⟨-, hx⟩ := hx hM
  obtain ⟨hHC, p, hp, hε⟩ := hM τ
  obtain ⟨-, hlow, hwt⟩ := hv τ
  have hP := M.fr_unit τ
  have hPd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hG := M.fr_gram τ
  have hH : (gramAt D V τ).IsHermitian := by
    rw [← hG]; exact Matrix.isHermitian_conjTranspose_mul_mul _ (jm_herm _)
  have hD : (gramAt D V τ).det ≠ 0 := by
    rw [← hG, det_mul, det_mul, det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero hPd.star.ne_zero (jm_det _)) hPd.ne_zero
  have hs : SmoothVec (lieH (gramAt D V τ)) (M.rep τ) (v τ : M.H τ) :=
    (GlobalTheory.UnitarySmVec.smoothVec_basic _ _ _ _ hH hD hU).1 _ (v τ).2
  refine ⟨hs, fun a c hac => ?_⟩
  have hs' : SmoothVec (lieH (Formalism.REAL.Jm (M.ε τ))) (M.σ τ) (v τ : M.H τ) := by
    refine smooth_conj hP _ _ _ ?_
    rw [hG]; exact hs
  have hl : (v τ : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := hlow
  have hB := GlobalTheory.T.extremal_lowest_Ktype_killed_by_compact_roots _ _ _ _ _ (M.ds τ) _ hl hs' hwt
  have hm := GlobalTheory.T.lowest_Ktype_holomorphic_killed_by_lowering_roots _ p _ _ _ _ hHC hε (M.ds τ) _ hl hs'
  have e : dRepC (gramAt D V τ) (M.rep τ) (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (v τ : M.H τ) =
      dRepC (Formalism.REAL.Jm (M.ε τ)) (M.σ τ)
        (Matrix.single (arr (nNeg (M.ε τ)) a) (arr (nNeg (M.ε τ)) c) 1) (v τ : M.H τ) := by
    rw [hx a c, ← hG]
    exact dRepC_conj hP _ _ _ _
  rw [e]
  split_ifs with h
  · subst h
    rw [hB.1]
    have := hw τ a
    unfold extWt at this
    rw [← this]
    simp
  · have hlt : (a : ℕ) < c := lt_of_le_of_ne hac fun h' => h (Fin.ext h')
    have hq := nNeg_shape hp hε
    have hcn := c.2
    have hsg : ∀ b : Fin V.rank, M.ε τ (arr (nNeg (M.ε τ)) b) = decide (¬ (b : ℕ) < V.rank - p) := by
      intro b
      have := b.2
      rw [hε, hq]
      unfold arr
      split_ifs with hb
      · simp only [hb, not_true_eq_false, decide_false, decide_eq_false_iff_not]; omega
      · simp only [hb, not_false_eq_true, decide_true, decide_eq_true_eq]; omega
    by_cases ha : (a : ℕ) < V.rank - p
    · by_cases hc' : (c : ℕ) < V.rank - p
      · refine hB.2 _ _ (by rw [hsg, hsg]; simp [ha, hc']) ?_
        rw [Fin.lt_def, revNeg_arr hp hε, revNeg_arr hp hε, if_pos ha, if_pos hc']
        omega
      · exact hm _ _ (by rw [hsg]; simp [hc']) (by rw [hsg]; simp [ha])
    · have hc' : ¬ (c : ℕ) < V.rank - p := by omega
      refine hB.2 _ _ (by rw [hsg, hsg]; simp [ha, hc']) ?_
      rw [Fin.lt_def, revNeg_arr hp hε, revNeg_arr hp hε, if_neg ha, if_neg hc']
      omega

end GlobalTheory.HolDict.VKill
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameBorelActsExtremalVectorByWeightStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ τ, SmoothVec (lieH (gramAt D V τ)) (M.rep τ) (v τ : M.H τ) ∧ ∀ a c : Fin V.rank, a ≤ c → dRepC (gramAt D V τ) (M.rep τ) (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (v τ : M.H τ) = if a = c then (w τ a : ℂ) • (v τ : M.H τ) else 0 := by
  first | exact @GlobalTheory.HolDict.VKill.borel_extVec | exact GlobalTheory.HolDict.VKill.borel_extVec | (intros; apply GlobalTheory.HolDict.VKill.borel_extVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff
set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.GraphLocal

open GlobalTheory.FieldPair

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

def placeAlg (E : Place (algebraMap ℂ K)) : Subalgebra ℂ K :=
  { E.ring.toSubring with algebraMap_mem' := E.const_mem }

theorem mem_placeAlg {E : Place (algebraMap ℂ K)} {e : K} : e ∈ placeAlg E ↔ e ∈ E.ring :=
  Iff.rfl


variable (κ') in
def tensMap (A : Subalgebra ℂ K) : A ⊗[ℂ] κ' →ₐ[ℂ] K ⊗[ℂ] κ' :=
  Algebra.TensorProduct.map A.val (AlgHom.id ℂ κ')

theorem tensMap_injective (A : Subalgebra ℂ K) : Function.Injective (tensMap κ' A) := by
  have e : ⇑(tensMap κ' A) = ⇑(LinearMap.rTensor κ' A.val.toLinearMap) := by
    funext w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  rw [e]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

def tens (A : Subalgebra ℂ K) : Subalgebra ℂ (K ⊗[ℂ] κ') := (tensMap κ' A).range

def tensEquiv (A : Subalgebra ℂ K) : A ⊗[ℂ] κ' ≃ₐ[ℂ] tens (κ' := κ') A :=
  AlgEquiv.ofInjective _ (tensMap_injective A)

@[simp] theorem coe_tensEquiv (A : Subalgebra ℂ K) (w : A ⊗[ℂ] κ') :
    (tensEquiv A w : K ⊗[ℂ] κ') = tensMap κ' A w := rfl

theorem tmul_mem {A : Subalgebra ℂ K} {e : K} (he : e ∈ A) (b : κ') :
    e ⊗ₜ[ℂ] b ∈ tens (κ' := κ') A :=
  ⟨⟨e, he⟩ ⊗ₜ b, rfl⟩

variable {κ : Type} [Field κ] [Algebra ℂ κ]

def graphIdeal (E : Place (algebraMap ℂ K)) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') :
    Ideal (tens (κ' := κ') (placeAlg E)) :=
  Ideal.span ({b | ∃ e : K, 0 < E.ord e ∧ (b : K ⊗[ℂ] κ') = e ⊗ₜ 1} ∪
    {b | ∃ a : R, (b : K ⊗[ℂ] κ') = (a : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π a)})

def gens (E : Place (algebraMap ℂ K)) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ')
    (hR : E.Contains R) (t : E.ring) {k : ℕ} (z : Fin k → R) :
    Fin (k + 1) → tens (κ' := κ') (placeAlg E) :=
  Fin.cons ⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩ fun i =>
    ⟨(z i : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π (z i)),
      sub_mem (tmul_mem (hR _ (z i).2) 1) (tmul_mem (one_mem (placeAlg E)) _)⟩

variable {L : Type} [Field L] [Algebra (K ⊗[ℂ] κ') L]

theorem one_notMem {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [h𝔭 : 𝔭.IsPrime] :
    (1 : tens (κ' := κ') A) ∉ 𝔭 :=
  (Ideal.ne_top_iff_one 𝔭).1 h𝔭.ne_top

def locAt {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime] : Subring L where
  carrier := {x | ∃ a s : tens (κ' := κ') A, s ∉ 𝔭 ∧
    x * algebraMap (K ⊗[ℂ] κ') L s = algebraMap (K ⊗[ℂ] κ') L a}
  mul_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨a', s', hs', hy⟩
    refine ⟨a * a', s * s', fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs hs', ?_⟩
    simp only [Subalgebra.coe_mul, map_mul]
    rw [← hx, ← hy]
    ring
  one_mem' := ⟨1, 1, one_notMem 𝔭, by simp⟩
  add_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨a', s', hs', hy⟩
    refine ⟨a * s' + a' * s, s * s', fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs hs', ?_⟩
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, map_mul, map_add (f := _)]
    rw [← hx, ← hy]
    ring
  zero_mem' := ⟨0, 1, one_notMem 𝔭, by simp⟩
  neg_mem' := by
    rintro x ⟨a, s, hs, hx⟩
    refine ⟨-a, s, hs, ?_⟩
    simp only [Subalgebra.coe_neg, map_neg]
    rw [← hx]
    ring

def toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime] :
    tens (κ' := κ') A →+* locAt (L := L) 𝔭 where
  toFun b := ⟨algebraMap (K ⊗[ℂ] κ') L b, b, 1, one_notMem 𝔭, by simp⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp] theorem coe_toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (b : tens (κ' := κ') A) : (toQ (L := L) 𝔭 b : L) = algebraMap (K ⊗[ℂ] κ') L b := rfl

theorem exists_mul_toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (x : locAt (L := L) 𝔭) : ∃ a s : tens (κ' := κ') A, s ∉ 𝔭 ∧ x * toQ 𝔭 s = toQ 𝔭 a := by
  obtain ⟨x, a, s, hs, hx⟩ := x
  exact ⟨a, s, hs, Subtype.ext hx⟩

section Inj

variable {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
  (hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L))
include hinj

theorem algebraMap_ne_zero {b : tens (κ' := κ') A} (hb : b ≠ 0) :
    algebraMap (K ⊗[ℂ] κ') L b ≠ 0 := fun h =>
  hb (Subtype.ext (hinj (h.trans (map_zero _).symm)))

theorem isUnit_toQ {b : tens (κ' := κ') A} (hb : b ∉ 𝔭) : IsUnit (toQ (L := L) 𝔭 b) := by
  have hb0 : algebraMap (K ⊗[ℂ] κ') L b ≠ 0 :=
    algebraMap_ne_zero hinj fun h => hb (h ▸ 𝔭.zero_mem)
  refine IsUnit.of_mul_eq_one (b := ⟨(algebraMap (K ⊗[ℂ] κ') L b)⁻¹, 1, b, hb, by simp [hb0]⟩)
    (Subtype.ext ?_)
  simp [hb0]

theorem isLocalRing_locAt : IsLocalRing (locAt (L := L) 𝔭) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨a, s, hs, hx⟩ := exists_mul_toQ 𝔭 x
  by_cases ha : a ∈ 𝔭
  · right
    have hsa : s - a ∉ 𝔭 := fun h => hs (by simpa using add_mem h ha)
    refine isUnit_of_mul_isUnit_left (y := toQ 𝔭 s) ?_
    rw [sub_mul, one_mul, hx, ← map_sub]
    exact isUnit_toQ 𝔭 hinj hsa
  · left
    refine isUnit_of_mul_isUnit_left (y := toQ 𝔭 s) ?_
    rw [hx]
    exact isUnit_toQ 𝔭 hinj ha

theorem isUnit_toQ_iff {b : tens (κ' := κ') A} : IsUnit (toQ (L := L) 𝔭 b) ↔ b ∉ 𝔭 := by
  refine ⟨fun h hb => ?_, isUnit_toQ 𝔭 hinj⟩
  obtain ⟨y, hy⟩ := h.exists_right_inv
  obtain ⟨a, s, hs, e⟩ := exists_mul_toQ 𝔭 y
  have e2 : toQ (L := L) 𝔭 (b * a) = toQ 𝔭 s := by
    rw [map_mul, ← e, ← mul_assoc, hy, one_mul]
  have e3 : b * a = s := Subtype.ext (hinj (congrArg Subtype.val e2))
  exact hs (e3 ▸ 𝔭.mul_mem_right a hb)

theorem toQ_mem_maximalIdeal_iff [IsLocalRing (locAt (L := L) 𝔭)] {b : tens (κ' := κ') A} :
    toQ (L := L) 𝔭 b ∈ IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) ↔ b ∈ 𝔭 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_toQ_iff 𝔭 hinj, not_not]

theorem map_le_maximalIdeal [IsLocalRing (locAt (L := L) 𝔭)] :
    𝔭.map (toQ (L := L) 𝔭) ≤ IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) :=
  Ideal.map_le_iff_le_comap.2 fun _ hb => (toQ_mem_maximalIdeal_iff 𝔭 hinj).2 hb

end Inj

end GlobalTheory.GraphLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingSecsOfClsEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.CechPic

theorem exists_generating_secs_of_cls_eq : ∀ (X : Scheme.{0}) (L A : LB X) (hL : L.IsLB) (hA : A.IsLB), cls L hL = cls A hA → ∀ (ι : Type) (u : ι → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∃ v : ι → A.Sec, ⨆ i, nonzeroLocus (v i) = ⊤ := by
  intro X L A hL hA h ι u hu
  have hiso : LBIso A L := (cls_eq_iff hA hL).1 h.symm
  choose v hv using fun i => GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso hA hL hiso (u i)
  refine ⟨v, ?_⟩
  simp only [hv]
  exact hu

end GlobalTheory.CechPic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveOfIsometric
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts

namespace GlobalTheory

namespace HermLB

theorem Isometric.semiPos : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
    (L M : GlobalTheory.HermLB p) (D : ℕ), L.Isometric M → L.SemiPos D → M.SemiPos D := by
  intro k _ X p L M D h hL σ a c y hy ξ
  have hb := mem_pick (L.φ σ).isLB y
  have hL' := hL σ _ c y ⟨hy.1, hb⟩ ξ
  have e := h.hess_eq c hy.1 hy.2 hb
  have hM : ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((M.φ σ).φ a (c.e.symm v) : ℂ)) (c.e y) ξ =
      ∑ j, ∑ l, c.hess (M.φ σ) a y j l * ξ j * (starRingEnd ℂ) (ξ l) := rfl
  have hL₂ : ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((L.φ σ).φ (pick (L.φ σ).isLB y) (c.e.symm v) : ℂ))
      (c.e y) ξ = ∑ j, ∑ l, c.hess (L.φ σ) (pick (L.φ σ).isLB y) y j l * ξ j * (starRingEnd ℂ) (ξ l) := rfl
  rw [hM, e, ← hL₂]
  exact hL'

end HermLB

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPolarisedTopChernCoeff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPolarisedTopChernCoeff
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop


set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
theorem _root_.GlobalTheory.GoodTop.continuousAt_mixTop :
    ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]
      {K : _root_.ReciprocityTheory.L2DbarEstimates.V n → Fin n → _root_.GlobalTheory.GoodTop.EndValuedForm11Coeffs n r} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n},
      (∀ i a b p q, ContinuousAt (fun x => K x i a b p q) v) →
        ContinuousAt (fun x => _root_.GlobalTheory.GoodTop.mixTop (K x)) v := by
  intro n r _ _ K v hK
  unfold _root_.GlobalTheory.GoodTop.mixTop
  simp only [Matrix.det_apply, Matrix.of_apply]
  fun_prop

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPolarisedTopChernCoeffStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousAt_polarisedTopChernCoeff : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {K : V n → Fin n → EndValuedForm11Coeffs n r} {v : V n}, (∀ i a b p q, ContinuousAt (fun x => K x i a b p q) v) → ContinuousAt (fun x => mixTop (K x)) v := by
  first | exact @GlobalTheory.GoodTop.continuousAt_mixTop | exact GlobalTheory.GoodTop.continuousAt_mixTop | (intros; apply GlobalTheory.GoodTop.continuousAt_mixTop <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHolomorphicChartTransEtaleChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHolomorphicChartTransEtaleChart
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem holoChart_trans_algChart {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e)
    (c : AlgChart X.str σ X.dim) :
    DifferentiableOn ℂ (c.e ∘ e.symm) (e.target ∩ e.symm ⁻¹' c.e.source) :=
  differentiableOn_euclidean.2 fun a => ((he _ (c.x a)).mono fun _ (hv : _ ∈ e.target ∩ e.symm ⁻¹' c.e.source) =>
    ⟨hv.1, c.source_subset hv.2⟩).congr fun _ hv => c.apply_eq _ hv.2 a

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHolomorphicChartTransEtaleChartStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ c : AlgChart X.str σ X.dim, DifferentiableOn ℂ (c.e ∘ e.symm) (e.target ∩ e.symm ⁻¹' c.e.source) := by
  first | exact @GlobalTheory.GoodTop.holoChart_trans_algChart | exact GlobalTheory.GoodTop.holoChart_trans_algChart | (intros; apply GlobalTheory.GoodTop.holoChart_trans_algChart <;> assumption)
end
end
