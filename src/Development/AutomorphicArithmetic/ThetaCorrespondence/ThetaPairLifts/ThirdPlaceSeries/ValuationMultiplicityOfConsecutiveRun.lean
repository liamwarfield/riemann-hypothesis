module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationMultiplicityWeight
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GloballyGeneratedOnOpenOfWeightGapGe
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConstructedAfterLargeBaseCorePropertyOfForall
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSectionOrderBoundHilbertSamuel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizesOfCoverStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SGalRead
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisationDeep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedTies
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsBoundOfDeepGood

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValuationMultiplicityOfConsecutiveRun
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentredPointPhiPositive
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DegVal
end GlobalTheory.DegVal
namespace GlobalTheory.DegVal
theorem exists_phiAt_pos_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∃ φ : ℝ, 0 < φ ∧ PhiAt TF.X Z y ν φ := by
  intro hP hD _ _
  refine Formalism.MainNotions.Closed.imp hD fun Fm CH _ h => ?_
  obtain ⟨C, hC, x0, h⟩ := h
  exact ⟨C, hC, x0, fun x hx hle ι p hp i _ Y _ Z TF y hy ν hν => _root_.GlobalTheory.DegVal.degree_valuation_phi_pos hP TF Z y hy ν hν⟩
end GlobalTheory.DegVal
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_phi_pos_of_centred_off_U0 : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∃ φ : ℝ, 0 < φ ∧ PhiAt TF.X Z y ν φ := by
  first | exact @_root_.GlobalTheory.DegVal.exists_phiAt_pos_alt_alt | exact _root_.GlobalTheory.DegVal.exists_phiAt_pos_alt_alt | (intros; apply _root_.GlobalTheory.DegVal.exists_phiAt_pos_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsNonzeroSectionWeightBound
set_option synthInstance.maxHeartbeats 200000

section
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaSteep
section Tau
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR _root_.Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open GlobalTheory.ThetaConst
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
end Tau
section Key
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyIntegralVal GlobalTheory.ShFam
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
end Key
section Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory _root_.Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.HSApp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)
end Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory _root_.Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 2000000 in
theorem exists_theta_section_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∃ θ : H0 (str₀ TF.X Z) (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))) ⊤, θ ≠ 0 ∧ (∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ f ∈ space TF.X Z Y.U (la - ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))), ((common₀ TF.X Z).addChart (add_sub_cancel ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i)) la)).mul θ f ∈ space TF.X Z Y.U la) ∧ ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∀ (j : (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).ι) (hj : y ∈ (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).U j) (m : ℤ), ν (H0.germ j y (memTop y) hj θ) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → 8 * φ / 625 ≤ (m : ℝ) := by
  intro h1 h2 h3 h4
  refine (((_root_.GlobalTheory.T.exists_phi_pos_of_centred_off_U0 h1 h2 h3 h4).and h4).and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C, hC, x0, hx0⟩, ⟨C₁, -, x1, hx1⟩⟩, ⟨C₂, -, x2, hx2⟩⟩ := h
  refine ⟨C, hC, max x0 (max x1 x2), fun x hx hle ι p hp i hi Y hY Z TF => ?_⟩
  have l0 : x0 ≤ x := (le_max_left _ _).trans hle
  have l1 : x1 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have l2 : x2 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  have hdeg := hx0 x hx l0 ι p hp i hi Y hY Z TF
  have hfl := hx1 x hx l1 ι p hp i hi Y hY
  have hnum := hx2 x hx l2 ι p hp i
  have hL := GlobalTheory.LawsDeep.laws_deep _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
  have hM : 5 ^ 4 ∣ Y.d.l₂.M := by
    rw [hY.1.lev.1.2.1, hY.1.pd]
    exact Dvd.dvd.mul_left ((pow_dvd_pow_of_dvd (by norm_num) 4).trans (pow_dvd_pow 15 (four_le_expL hnum.big.2.1))) _
  have hf : 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 := by
    have := hnum.f8
    have := hnum.deg
    omega
  obtain ⟨θ, hθ, hb⟩ := _root_.GlobalTheory.ThetaSteep.exists_section_of_theta_datum Z h1 hL hM TF (fun τ => (hfl Z τ).1.some) hdeg
  exact ⟨θ, hθ, fun la _ f hf' => vanBd_le_space _ _ _ Y _ _ hY.1 hf Z TF la
    (mul_mem_vanBd TF.X Z _ θ ((GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace _ _ _ Y _ _ hY.1 hf Z TF _).space_le hf')),
    fun y _ ν hν φ hφ j hj m hm => hb y ν hν φ hφ j hj m hm⟩
end GlobalTheory.ThetaSteep
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_section_weight_bound_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∃ θ : H0 (str₀ TF.X Z) (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))) ⊤, θ ≠ 0 ∧ (∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ f ∈ space TF.X Z Y.U (la - ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))), ((common₀ TF.X Z).addChart (add_sub_cancel ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i)) la)).mul θ f ∈ space TF.X Z Y.U la) ∧ ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∀ (j : (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).ι) (hj : y ∈ (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).U j) (m : ℤ), ν (H0.germ j y (memTop y) hj θ) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → 8 * φ / 625 ≤ (m : ℝ) := by
  first | exact @_root_.GlobalTheory.ThetaSteep.exists_theta_section_alt_alt | exact _root_.GlobalTheory.ThetaSteep.exists_theta_section_alt_alt | (intros; apply _root_.GlobalTheory.ThetaSteep.exists_theta_section_alt_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ValMultRun
section Algebra
open IsLocalRing IsDedekindDomain
open scoped NNReal
end Algebra
section Centre
open TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.TangentOrigin
open GlobalTheory.Adelic (ptOf le_iff_ptOf_mem ptOf_comp)
open scoped NNReal
end Centre
section Component
open TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.TangentOrigin GlobalTheory.Vanishing.H0
open GlobalTheory.Adelic (ptOf le_iff_ptOf_mem ptOf_comp)
open GlobalTheory.AllWt (secZ exOf suppOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (genVal genPoint)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open scoped NNReal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)
variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
end Component
private theorem gap_add' {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]; ring
  · simp
private theorem gap_sub' {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v - w) k = gap v k - gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.sub_apply]; ring
  · simp
private theorem gap_nsmul' {N : ℕ} (n : ℕ) (v : Fin N → ℤ) (k : ℕ) : gap (n • v) k = n * gap v k := by
  unfold gap
  split_ifs
  · simp only [Pi.smul_apply, nsmul_eq_mul]; ring
  · simp
private theorem gap_kap_le' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) :
    gap (FlagTan.kap Dw τ) k ≤ 2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2 := by
  unfold FlagTan.kap gap; simp only [dif_pos h]; split_ifs <;> push_cast <;> omega
private theorem div_le_sub_mul_div' (g : ℤ) {n : ℤ} (hn : 0 < n) : g / n ≤ g - (n - 1) * (g / n) := by
  have h₁ : n * (g / n) ≤ g := Int.mul_ediv_self_le hn.ne'
  linarith
private theorem gaps_of_wtBig' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (P : WtPar Dw), WtBig P → ∀ la ∈ [P.u₁, P.u₂, P.ub, P.u₁ - FlagTan.kap Dw - (FlagTan.dimFlag Dw + 2) • P.ub], GapGe 1 la ∧ GapGe (((FlagTan.dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) := by
  intro E _ _ _ H Dw P hP la hla
  have hD3 : (0 : ℤ) < (FlagTan.dimFlag Dw : ℤ) + 3 := by positivity
  have hmain : ∀ (τ : Psi H) (k : ℕ), k + 1 < Dw.p + Dw.q →
      (((FlagTan.dimFlag Dw + 1).choose 2 : ℕ) : ℤ) + 4 * ((Dw.p : ℤ) + Dw.q) + FlagTan.dimFlag Dw + 3 ≤ gap (P.ub τ) k ∧
      gap (P.ub τ) k ≤ gap (P.u₁ τ) k - ((FlagTan.dimFlag Dw : ℤ) + 2) * gap (P.ub τ) k ∧
      gap (P.u₁ τ) k ≤ gap (P.u₂ τ) k := by
    intro τ k h
    have hg := hP.gaps τ k h
    push_cast at hg
    rw [P.gap_ub τ h]
    refine ⟨?_, ?_, ?_⟩
    · apply Int.le_ediv_of_mul_le hD3
      linarith
    · have := div_le_sub_mul_div' (gap (P.u₁ τ) k) hD3
      linarith
    · rw [show P.u₂ τ = P.u₁ τ + P.rem τ from rfl, gap_add']
      linarith [(P.gap_rem τ k).1]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hla
  rcases hla with rfl | rfl | rfl | rfl <;> constructor <;> intro τ k h <;>
  · obtain ⟨h₁, h₂, h₃⟩ := hmain τ k h
    have h₄ := gap_kap_le' τ h
    push_cast at h₄
    have hC : (0 : ℤ) ≤ (((FlagTan.dimFlag Dw + 1).choose 2 : ℕ) : ℤ) := by positivity
    have hD : (0 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) := by positivity
    have hN : (2 : ℤ) ≤ (Dw.p : ℤ) + Dw.q := by omega
    have hb : (0 : ℤ) ≤ ((FlagTan.dimFlag Dw : ℤ) + 2) * gap (P.ub τ) k := by
      apply mul_nonneg <;> linarith
    try simp only [Pi.sub_apply, Pi.smul_apply, gap_sub', gap_nsmul']
    try push_cast
    linarith
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic GlobalTheory.Vanishing in
set_option maxHeartbeats 1000000 in
theorem valuation_multiplicity_of_consecutive_run_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ValMult Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) (wtOf (dat p i) (CompHt.uPrime (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) 0) := by
  intro hP hGD hQ hS hT hL h2 h3 h4
  refine ((((_root_.GlobalTheory.T.exists_nonzero_section_weight_bound_alt_alt hP h2 h3 h4).and (_root_.GlobalTheory.T.exists_section_order_bound_hilbertSamuel_alt hP h2 h3 h4)).and (_root_.GlobalTheory.T.exists_phi_pos_of_centred_off_U0 hP h2 h3 h4)).and _root_.GlobalTheory.HSApp.wtBig_run_alt).imp
    fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨C, hC, x0, hx⟩, ⟨C', hC', x1, hx1⟩⟩, ⟨C'', hC'', x2, hx2⟩⟩, ⟨C₃, hC₃, x3, hx3⟩⟩ := h
  refine ⟨C, hC, max (max x0 x1) (max x2 x3), fun x hx' hle ι p hp i hi Y hY Z => ?_⟩
  simp only [max_le_iff] at hle
  have hB := hx3 x hx' hle.2.2 ι p hp i hi
  have hP' := _root_.GlobalTheory.T.covering_topology_refinement hP
  obtain ⟨TF⟩ := @_root_.GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag_alt hP' _ _ _ _ _ _ _ Y.d.Xo₂ Y.d.c₂ hB.one_le
  obtain ⟨θ, hθ, -, hst⟩ := hx x hx' hle.1.1 ι p hp i hi Y hY Z TF
  have hJ := hx1 x hx' hle.1.2 ι p hp i hi Y hY Z TF _ (Or.inl rfl)
  have hD := hx2 x hx' hle.2.1 ι p hp i hi Y hY Z TF
  have hf : 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 := by
    have h3 : Module.finrank ℚ (Fm.D x ι).host.E = 4 * (Fm.D x ι).R.ord :=
      (Fm.D x ι).host.finrank_cmField
    have h : 4 ≤ (Fm.D x ι).R.ord := (Fm.D x ι).host.four_le_n'
    omega
  have hCI : ∀ la, CuspIso TF.X Z Y.U la := fun la =>
    ⟨GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace _ _ _ Y _ _ hY.1 hf Z TF _, vanBd_le_space _ _ _ Y _ _ hY.1 hf Z TF _⟩
  have hfree := _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open hP' hGD hQ hP.q15 hP.q16 hS hT.toroidalChartsForFan hL _ _ _ _ _ _ TF Z _ Y.U hY.1.geo
    hB.one_le _ (gaps_of_wtBig' _ _ _ _ hB _ List.mem_cons_self).2 (hCI _)
  refine valMult_of_section TF.X Z Y.U (GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hY.1.geo) hCI ?_ hfree θ hθ
    fun y hy ν hν => ?_
  · rw [CompHt.uPrime]
    module
  obtain ⟨φ, hφ, hPh⟩ := hD y hy ν hν
  obtain ⟨w, hw, hwb⟩ := hJ y hy ν hν φ hPh
  refine ⟨w, hw, fun j hj j' hj' => ?_⟩
  obtain ⟨hw0, hwm⟩ := hwb j' hj'
  obtain ⟨zw, hzw⟩ := WithZero.ne_zero_iff_exists.1 hw0
  have ew : ν (H0.germ j' y (memTop y) hj' w) =
      ((Multiplicative.ofAdd (-(-Multiplicative.toAdd zw)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [neg_neg, ofAdd_toAdd]; exact hzw.symm
  have bw := hwm _ ew
  by_cases h0 : ν (H0.germ j y (memTop y) hj θ) = 0
  · rw [h0, zero_pow three_ne_zero]
    exact zero_le'
  · obtain ⟨zt, hzt⟩ := WithZero.ne_zero_iff_exists.1 h0
    have et : ν (H0.germ j y (memTop y) hj θ) =
        ((Multiplicative.ofAdd (-(-Multiplicative.toAdd zt)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      rw [neg_neg, ofAdd_toAdd]; exact hzt.symm
    have bt := hst y hy ν hν φ hPh j hj _ et
    have hle' : (3 * Multiplicative.toAdd zt : ℝ) ≤ (8 * Multiplicative.toAdd zw : ℝ) := by
      push_cast at bw bt ⊢
      linarith
    have hle'' : 3 * Multiplicative.toAdd zt ≤ 8 * Multiplicative.toAdd zw := by exact_mod_cast hle'
    rw [← hzt, ← hzw, ← WithZero.coe_pow, ← WithZero.coe_pow, WithZero.coe_le_coe, ← Multiplicative.toAdd_le,
      toAdd_pow, toAdd_pow]
    simpa using hle''
end GlobalTheory.ValMultRun
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_multiplicity_run_estimate_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ValMult Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) (wtOf (dat p i) (CompHt.uPrime (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) 0) := by
  first | exact @_root_.GlobalTheory.ValMultRun.valuation_multiplicity_of_consecutive_run_alt | exact _root_.GlobalTheory.ValMultRun.valuation_multiplicity_of_consecutive_run_alt | (intros; apply _root_.GlobalTheory.ValMultRun.valuation_multiplicity_of_consecutive_run_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlIsTripleWithcharpolyFrob
theorem GlobalTheory.Triple.IsGaloisTripleWithReduction.charpoly_frob : type_of% (@GlobalTheory.Triple.IsGaloisTripleWithReduction.charpoly_frob_of_isTriple) := @GlobalTheory.Triple.IsGaloisTripleWithReduction.charpoly_frob_of_isTriple
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwJoin
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TwInputs
open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
structure TwistedRealJoin (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (nch : NChoice D) (xd : ThData D) (first : Prop) {G : Type}
    [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [aC : Algebra C.Q.c.F D.what₂.LL]
    (R : RealDat3 D A3 C.Q.c.F) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (S : RatDat D.ntw) (YS : NExpRealS R cG S)
    (cf : CharFrame D) : Type 1 where
  X : RealSide D
  Γ_eq : X.Γ = G
  grp_eq : HEq X.grp iG
  fin_eq : HEq X.fin fG
  Pl0_eq : X.Pl0 = Pl0
  I0_eq : X.I0 = I0
  T_eq : X.T = T
  core_eq : X.core = C
  alg_eq : HEq X.alg aC
  R_eq : HEq X.R R
  F_eq : HEq X.F F
  cG_eq : HEq X.cG cG
  geo_eq : HEq X.geo geo
  A3_eq : HEq X.A3 A3
  Y : SerSide X (twEOf xd)
  S_eq : Y.S = S
  YS_eq : HEq Y.YS YS
  gal : _root_.GlobalTheory.TwInputs.GalSideAlt D
  cf_eq : gal.cf = cf
  lam_eq : gal.lam.C = cf
  C_eq : X.R.C = cf
  field : FieldOk X
  cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL D gal.wd
  base : first → ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w)
def TwistNormChoice (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun _ B _ T w Z _ _ t nch _ xd c =>
  _root_.GlobalTheory.TwInputs.TwistedRealJoin hL (w.st Z).toD7 nch xd (T = TwDat.untw B T.pl) t.r.z.R t.r.z.F t.r.z.cG t.r.z.geo _ c.row.nexp (TC.cf w.I w.l Z)
end GlobalTheory.TwInputs
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwLe
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoefSt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoefSt
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.ConjTwist (BaseOf)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TupLe.CoefPf
theorem coefSt_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.CoefficientCondition' := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm B hB hBo c hc hS u hu O' hO' h hh v hv
  have hL : Links2 p := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  obtain ⟨gramR, c0R, c0L, hft, u', hu', hF⟩ := hS
  have huu : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  subst huu
  obtain ⟨F, hF0, rfl⟩ := GlobalTheory.T.coefLattice_indep_coefMap_proof D _ _ _ p.P.A3.A _ (R2 p) (F2 p) hC j c0L ⟨gramR, c0R, hft⟩ h v hv
  have hio : IoExt (R2 p) := hr.ioExt
  have hv0 : IsChosenExtremalVector (R2 p) j (sg0 D p.P.A3.A) (p.v₀ j _) := (hL.2.2.2.2.2.2.1 j).2.lift.v0
  have hval : ∀ w, (R2 p).ioP j (PiTensorProduct.tprod ℂ u') w ∈ harm (Wc D j).rank B.w B.F.BS := by
    have hcV : ((R2 p).cV j).Is := hC.models.cV j
    obtain ⟨u'', w₀, hu'', -, hw⟩ := IsChosenExtremalVector.io _ hv0 hio
    have huu : u'' = u' := funext fun ρ => Subtype.ext ((hu'' ρ).trans (hu ρ).symm)
    rw [huu] at hw
    have hT := GlobalTheory.SeriesTie.Scale.io_act hC.lev hC.thP hB hBo.ψ hBo.θ hBo.sT hBo.BS hBo.BT hBo.mu0 hBo.eta
      (PiTensorProduct.tprod ℂ u')
    have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) j
    rcases hcV.2.2.2.2 ((harm (Wc D j).rank B.w B.F.BS).comap ((R2 p).ioP j (PiTensorProduct.tprod ℂ u'))) (fun g => by
        obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 g
        rw [map_mul, hcV.1 k hk, mul_one]
        rintro _ ⟨w, hw', rfl⟩
        rw [Submodule.mem_comap, hT a ha]
        exact fockGL_mem_harm _ _ _ hw') with h0 | h0
    · have h1 : w₀ ∈ (harm (Wc D j).rank B.w B.F.BS).comap ((R2 p).ioP j (PiTensorProduct.tprod ℂ u')) := by
        rw [Submodule.mem_comap, hw, ← hBo.delta]
        exact delta_mem_harm _ _
      rw [h0, Submodule.mem_bot] at h1
      rw [h1, map_zero] at hw
      exact absurd hw.symm hΔ0
    · exact fun w => (h0 ▸ Submodule.mem_top : w ∈ (harm (Wc D j).rank B.w B.F.BS).comap
        ((R2 p).ioP j (PiTensorProduct.tprod ℂ u')))
  have hL0 : (B.F.ΛS : Set (Fin (Vc D j).rank → D.host.E)) = L0c D (Vc D j) := by
    rw [hBo.ΛS]
    exact GlobalTheory.OneMapRef.FactsLat.selfDual_frame_level_one_lattice_eq_standard (hL.1.lev.βV j)
  refine ⟨c⁻¹ • (R2 p).ioP j (PiTensorProduct.tprod ℂ u') (c0L j F), ?_, (smul_inv_smul₀ hc _).symm⟩
  refine (mem_harmLat _ _ _).2 ⟨Submodule.smul_mem _ _ (hval _), ?_⟩
  have hF' : harmFn (Wc D j).rank B.w B.F.BS ((R2 p).ioP j (PiTensorProduct.tprod ℂ u') (c0L j F)) =
      c • coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) := hF F
  rw [map_smul, hF', inv_smul_smul₀ hc, hBo.lam, GlobalTheory.LatAtHLat.latAt_eq_hLat D _ _ B hL0]
  exact Submodule.subset_span ⟨F, hF0, rfl⟩
end GlobalTheory.BigOn.Exp.TupLe.CoefPf
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoefStStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuple_coef_le : _root_.GlobalTheory.BigOn.Exp.TupLe.CoefficientCondition' := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt_alt | exact _root_.GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStAltBis
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStAltBis
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain
open NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links (PolF labLL)
open Formalism.L2.Host (embLL0)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SmallSpan
variable {D : D7} {m n : ℕ}
theorem smallSt_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.SmallnessCondition := by
  intro D _ _ _ _ _ _ _ _ _ p j _ _ B hB _ O O' _ hO' h P hP
  exact harmLat_le_span D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O O' hO'.int B.w B.F.BS hB.wt
    (GlobalTheory.CoefLatConj.pq_le hB) (isLattice_latAt hB.frame _) hP
end GlobalTheory.SmallSpan
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStAltBisStatement
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_tuple_statement_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.SmallnessCondition := by
  first | exact @_root_.GlobalTheory.SmallSpan.smallSt_alt | exact _root_.GlobalTheory.SmallSpan.smallSt_alt | (intros; apply _root_.GlobalTheory.SmallSpan.smallSt_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp.TupLe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem twLe_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.TwistUpperBound₂ := by
  intro _ _ _ hA hX
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA hX) fun Fm x hx i p hr hm w hw j ⟨a, c⟩ ρ hρ ν rd hf hc => ?_
  have hL := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have h0 := baseOf_of_pin (cG := p.cG) p.charW.base.lev hρ hf.pin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  obtain ⟨c1, c2⟩ := c ρ hρ hf.adapted
  obtain ⟨-, e, h1, h2⟩ := hf.adapted
  exact _root_.GlobalTheory.BigOn.Exp.TupLe.realTw_le_alt _root_.GlobalTheory.T.seesaw_places_statement _root_.GlobalTheory.T.tuple_flat_estimate _root_.GlobalTheory.T.tupLe_traceSt _root_.GlobalTheory.T.tuple_coef_le _root_.GlobalTheory.T.small_tuple_statement_alt hr hm hL hw a.1 hρ hf.pin hf.level
    { h0 with } e h1 h2 c1 c2 hf.norm hf.rat hc
end GlobalTheory.BigOn.Exp.TupLe
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGeo0At
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForallLinkedBundlesAndAlt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.AllAtMember
section large₂
variable {KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop} {Q Q' : V4.Slot}
theorem forall_linked_bundles_and_alt {Lk : LkT _root_.GlobalTheory.Fc.BundleCondition} {H H' : ∀ 𝒜 : FamClass, RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜 → Prop}
    (h : Lg1 KP Q Q' fun S => Row S Lk H) (h' : Lg1 KP Q Q' fun S => Row S Lk H') :
    Lg1 KP Q Q' fun S => Row S Lk fun 𝒜 σ => H 𝒜 σ ∧ H' 𝒜 σ :=
  RowL.and (KP := KP) (Q := Q) (Q' := Q') h h'
end large₂
end GlobalTheory.Fc.AllAtMember
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGeo0At
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.GeoZeroAt
theorem geometricWeakTies_of_linked_ties : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDivisorCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.Row_tie_alt → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.S0.GeometricWeakCompatibility' := by
  intro hR hL N S Γ hNE hD hT
  have hA := _root_.GlobalTheory.T.class_sum_divisor_all_alt hR hL N S Γ hNE hD
  refine AllAtMember.eventually_coreProperty_mono (_root_.GlobalTheory.Fc.AllAtMember.forall_linked_bundles_and_alt hA hT) fun Q h => ?_
  exact Row.imp h fun 𝒜 σ _ H _ Fm hc x hx i =>
    let ⟨t⟩ := H.2 Fm hc x hx i
    let ⟨a, b, c, _, e⟩ := H.1 Fm hc x hx i t
    ⟨t, a, b, c, e⟩
end GlobalTheory.Fc.GeoZeroAt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGeo0AtStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkedAt_geometricWeakTies_of_tie : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDivisorCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.Row_tie_alt → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.S0.GeometricWeakCompatibility' := by
  first | exact @_root_.GlobalTheory.Fc.GeoZeroAt.geometricWeakTies_of_linked_ties | exact _root_.GlobalTheory.Fc.GeoZeroAt.geometricWeakTies_of_linked_ties | (intros; apply _root_.GlobalTheory.Fc.GeoZeroAt.geometricWeakTies_of_linked_ties <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MEmbSph
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SGoodOfLevelShape
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RecT.Thread

section Level

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def LevelShape (π : NG.AutRep L n) : Prop :=
  ∃ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))),
    (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧ NG.HypOutside J χ B ∧
    (∃ f ∈ NG.isoTyp π.ρ π.S, f ∈ NG.TypeSp π.ρ J χ ∧ f ≠ 0) ∧
    ∀ s : SplitPlace L, s.v ∈ B → ∃ s₀ : SplitPlace L, s₀.v = s.v ∧
      ((∃ (r : ℕ) (ξ : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelPara J χ s₀ r ξ) ∨
      ((∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* s.w.adicCompletion L), Continuous i) ∧
        ∃ (r : ℕ) (ψ₀ : AddChar (s₀.v.adicCompletion (maximalRealSubfield L)) ℂ)
          (ξ : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelUni J χ s₀ r ψ₀ ξ ∧ NG.IsPsi0 s₀ ψ₀ ∧
          ∀ u : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ,
            Valued.v ((u : s₀.v.adicCompletion (maximalRealSubfield L)) - 1) < 1 → ξ u = 1))

theorem good_of_levelShape (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    (π : NG.AutRep L n) (h : LevelShape π) :
    ∀ (s : SplitPlace L) (σ : IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS π.S s σ →
      GlobalTheory.RecT.Good (GlobalTheory.LocLanglands.cls σ) := by
  obtain ⟨J, χ, B, hc, hH, ⟨f, hf, hfT, hf0⟩, hB⟩ := h
  intro s σ hσ
  by_cases hs : s.v ∈ B
  · obtain ⟨s₀, hv, hB'⟩ := hB s hs
    rcases hB' with ⟨r, ξ, hP⟩ | ⟨hk, r, ψ₀, ξ, hU, hψ, ht⟩
    · exact GlobalTheory.AVGood.good_of_toral (GlobalTheory.ParaToral.toral_of_levelPara hBZ hZ L n π.toAlgWt π.S π.irrS J χ hc s₀ r ξ hP
        f hf hfT hf0 s hv.symm σ hσ)
    · exact GlobalTheory.AVGood.good_of_fixed_KOne hZ hk _ (GlobalTheory.UniDepthZero.main L n π.toAlgWt π.S π.irrS J χ hc s₀ r ψ₀ ξ hU hψ ht
        f hf hfT hf0 s hv.symm σ hσ)
  · exact GlobalTheory.AVGood.good_of_isSpherical hBZ _ (GlobalTheory.SphHyp.isSpherical_of_hypOutside L n π.toAlgWt π.S π.irrS J χ hc B hH
      f hf hfT hf0 s hs σ hσ)

end Level

end GlobalTheory.RecT.Thread

end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.SphNonSplit
set_option maxHeartbeats 2000000 in
theorem sphAU_of_not_split_m_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (P : ι) (w : PlE D.host), ¬ IsSplitPl D.host w → D.nbc.sphAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp _hCS hMI _hstar _hE hsp _hCh big X T Sp i ι _ F irr hinj hsurj hne hind htop P w hns
  set v := HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w with hv
  have hover : NG.OverPl w v := rfl
  rw [A.au.sph (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 _ w v hns hover]
  obtain ⟨h1, h2⟩ := X.nd.j_range i
  let j : Fin D.R.m := ⟨X.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = X.nd.j i := by simp only [j]; omega
  have hvB := not_mem_bad D cf C tp hsp (X.nd.w i) j w v hover hns
  have hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j)) := by
    have key : ∀ (μ : D.what₂.Tup) (jj : ℕ) (k1 : 1 ≤ jj) (k2 : jj ≤ D.R.m), μ = D.what₂.muTw (X.nd.w i) → jj = j.1 + 1 →
        NG.HypOutside (M μ jj k1 k2).J (M μ jj k1 k2).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j)) := by
      rintro μ jj k1 k2 rfl rfl
      exact hMI.hyp (X.nd.w i) j
    exact key _ _ _ _ (X.nd.mu_w i) hj.symm
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (hne P)
  have hry : (mlX M X i).real y ≠ 0 := fun h0 =>
    hy0 ((mlX M X i).real_inj (h0.trans (map_zero (mlX M X i).real).symm))
  have hT : (mlX M X i).real y ∈ NG.TypeSp (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ := by
    rw [← (mlX M X i).real_range]; exact LinearMap.mem_range_self _ _
  obtain ⟨f, hfS, hf0, hfix⟩ := GlobalTheory.T.fixed_vector_of_mem_isotypic_component (mlX M X i).wt.ρ (F P)
    {κ | κ ∈ Umax D.host.E D.R.nV ∧ TrivOutside {v} κ} (irr P) _ hy hry (by
      rintro κ ⟨hU, htr⟩
      have ht : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j))ᶜ κ := fun u hu =>
        htr u (by rintro rfl; exact hu hvB)
      have hJ : κ ∈ (mlX M X i).J := ((hyp κ ht).1).2 hU
      rw [hT.2 ⟨κ, hJ⟩, (hyp κ ht).2 hJ, Units.val_one, one_smul])
  have hsh : ∀ (μ : D.what₂.Tup) (jj : ℕ) (k1 : 1 ≤ jj) (k2 : jj ≤ D.R.m), μ = D.what₂.muTw (X.nd.w i) → jj = j.1 + 1 →
      ∀ s : SplitPlace D.host.E, s.v ∈ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j) → ∃ s₀ : SplitPlace D.host.E, s₀.v = s.v ∧
      ((∃ (r : ℕ) (ξ : (s₀.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.LevelPara (M μ jj k1 k2).J (M μ jj k1 k2).χ s₀ r ξ) ∨
      ((∃ (g : ℕ) (_ : Fact g.Prime) (e : ℚ_[g] ≃+* s.w.adicCompletion D.host.E), Continuous e) ∧
        ∃ (r : ℕ) (ψ₀ : AddChar (s₀.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
          (ξ : (s₀.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.LevelUni (M μ jj k1 k2).J (M μ jj k1 k2).χ s₀ r ψ₀ ξ ∧ NG.IsPsi0 s₀ ψ₀ ∧
          ∀ u : (s₀.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
            Valued.v ((u : s₀.v.adicCompletion (maximalRealSubfield D.host.E)) - 1) < 1 → ξ u = 1)) := by
    rintro μ jj k1 k2 rfl rfl s hs
    by_cases hg : s.v ∈ gPl D
    · obtain ⟨k, v', s₀, hw, hv'⟩ := GlobalTheory.PlaceUnderFixed.exists_splitPlace_under_plGw D s hg
      obtain ⟨ψ₀, ξ, hψ, hc, hU⟩ := hMI.uni (X.nd.w i) j k v' s₀ hw
      refine ⟨s₀, hv', Or.inr ⟨GlobalTheory.SplitTypeCompl.exists_padic_equiv D s hg, D.R.r, ψ₀, ξ, hU, hψ,
        GlobalTheory.AVGood.compAt_eq_one_of_tameAt s₀ _ (fun x hx hx' => ?_) ξ hc⟩⟩
      have loc_mul (a b : HChar D.host.E) (v : HeightOneSpectrum (𝓞 D.host.E))
          (x : (v.adicCompletion D.host.E)ˣ) :
          (a * b).loc v x = a.loc v x * b.loc v x := rfl
      rw [TupTied.tup, loc_mul, (cf.isMu0 j).tame _ x hx hx', tp.xi_tame _ _ x hx hx', one_mul]
    · obtain ⟨s₀, ξ, hv', -, hP⟩ := hMI.para (X.nd.w i) j s.v (hs.resolve_left hg)
      exact ⟨s₀, hv', Or.inl ⟨D.R.r, ξ, hP⟩⟩
  have hlev : GlobalTheory.RecT.Thread.LevelShape ({ (mlX M X i).wt with S := F P, irrS := irr P } : NG.AutRep D.host.E D.R.nV) :=
    ⟨(mlX M X i).J, (mlX M X i).χ, _, (mlX M X i).J_open, hyp, ⟨_, hy, hT, hry⟩, hsh _ _ _ _ (X.nd.mu_w i) hj.symm⟩
  have h0 : _root_.UpperTheory.One.M.New.Sph0 ({ (mlX M X i).wt with S := F P, irrS := irr P } : NG.AutRep D.host.E D.R.nV) v :=
    ⟨f, hfS, hf0, fun κ hU htr => hfix κ ⟨hU, htr⟩⟩
  exact _root_.UpperTheory.One.M.New.sphMk h0 fun _ =>
    GlobalTheory.RecT.Thread.good_of_levelShape UpperTheory.Zero.LLC.Pr.bz UpperTheory.Zero.LLC.Pr.zel _ hlev
end GlobalTheory.SphNonSplit
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringDescentMapsCompatible
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
namespace GlobalTheory.CovTop.DescentMaps
end GlobalTheory.CovTop.DescentMaps
namespace GlobalTheory.CovTop.DescentMaps
set_option maxHeartbeats 1000000 in
theorem covering_descent_maps_compatible_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral →
    GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.MapsCondition := by
  intro hP hGD hQ hSI hTF hSN hGram hDG hSz hFD
  obtain ⟨C, hC0, hub⟩ := _root_.GlobalTheory.T.exists_short_integral_vector_of_determinant_bound hP hGD hQ hSI hTF hSN
  have hT := _root_.GlobalTheory.T.exists_psi_isTypeLevel_latDeep_eq_latN hP hGram hDG
  have hS := _root_.GlobalTheory.T.size_bounds_for_family_alt hSz
  have hH := _root_.GlobalTheory.CovTop.Sizes.hostN_alt (2 * C + 200)
  unfold _root_.GlobalTheory.CovTop.MapsCondition _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition
  unfold _root_.GlobalTheory.CovTop.DeepGoodness at hDG
  unfold _root_.GlobalTheory.CovTop.FlatDegreeCondition at hFD
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at hT hS hDG hFD
  unfold _root_.GlobalTheory.CovTop.HostNAlt _root_.GlobalTheory.CovTop.LiftsCondition at hH
  refine Closed.imp ((((hT.and hS).and hH).and hDG).and hFD) ?_
  intro eps Fm CH _ hall0
  obtain ⟨⟨⟨⟨⟨C1, -, hT'⟩, ⟨C2, -, hS'⟩⟩, ⟨A, -, hH'⟩⟩, ⟨C4, -, hDG'⟩⟩, ⟨C5, -, hFD'⟩⟩ := hall0
  refine ⟨0, le_rfl, ?_⟩
  obtain ⟨x0, hall⟩ := (((hT'.and hS').and hH').and hDG').and hFD'
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := hall x hx hle ι p hp
  obtain ⟨fr, ψ, -, hl, hlat, hcard⟩ := a1 i hi Y hY
  obtain ⟨hLaws, hInR, hL1, hM, hE, hfr, hexp, hg, hf8, hr100, hflat, -⟩ := a2 i hi Y hY
  have hN := a3 i
  have hDGY := a4 i hi Y hY
  have hFDY := a5 i hi Y hY
  obtain ⟨-, hpq, hq, h2q⟩ := GlobalTheory.Member.exists_iotaOK (Fm.D x ι) p.T.Q hLaws.pins ((i : ℕ) + 1) hInR
  have hq1 : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).q := by
    rw [hq]; simp only [Formalism.MainNotions.WeightFamilies.rho, Formalism.BasicNotions.Ranks.sigW]; omega
  have hp1 : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).p := by omega
  have hfin : 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 := by rw [hN.deg]; omega
  obtain ⟨u, hu, hdet, hB⟩ := hub (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY.1 (Fm.L x ι).sc.L hL1
    hM hE hfr (le_of_eq rfl) _ hFDY (by rw [abs_neg]; exact hflat) hexp hg hf8 hr100 fr
  have hK := GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY.1
  have hGk : Even (Gk p i).2 := (p.κ i).n_even.natCast
  have hW : Even (wtOf (p.T.Q.Dw ((i : ℕ) + 1)) (cZero (Fm.D x ι) ((i : ℕ) + 1) • hodgeWt (p.T.Q.Dw ((i : ℕ) + 1))) 0).2 :=
    GlobalTheory.AllWt.even_wtOf _ _
  have hGm : Even (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))).2 := hGk.add (GlobalTheory.AllWt.even_wtOf _ _)
  have hGW : Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1))) +
      wtOf (p.T.Q.Dw ((i : ℕ) + 1)) (cZero (Fm.D x ι) ((i : ℕ) + 1) • hodgeWt (p.T.Q.Dw ((i : ℕ) + 1))) 0 = Gk p i := by
    simp only [Gs, shiftG, add_assoc, ← GlobalTheory.AllWt.wtOf_add, neg_smul, neg_add_cancel, add_zero, GlobalTheory.AllWt.wtOf_zero]
  set z := zBase (Fm.L x ι) with hz
  have hzL : (Fm.L x ι).sc.L ≤ z := by
    have h8 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have h100 : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have h0 : (0 : ℝ) ≤ (Fm.L x ι).sc.L := by linarith
    rw [hz, zBase]
    nlinarith [mul_le_mul h8 h100 (by norm_num) (by linarith)]
  have hz1 : 2 * C + 200 ≤ z := hN.big.1.trans hzL
  have hPP : z ^ 12 ≤ (Fm.L x ι).sc.b := by
    have h1 := hN.ppLow
    obtain ⟨hA1, hA2, -⟩ := hN.poly
    have h3 := hN.room
    have hz0 : 1 ≤ z := by linarith
    have hx1 : 1 ≤ (Fm.L x ι).sc.x ^ A := le_trans (one_le_pow₀ hz0) (h1.trans hA2)
    have h4 : (Fm.L x ι).sc.x ^ A ≤ ((Fm.L x ι).sc.x ^ A) ^ (2 * C + 200) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hx1 (show (1 : ℝ) ≤ 2 * C + 200 by linarith)
    linarith
  have hb : (Fintype.card (grpHR fr) : ℝ) ^ 3 * Real.exp (C * ((Fm.D x ι).R.f * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 9) ^ 2 ≤
      Real.exp (2 * (Fm.L x ι).sc.b) := by
    have hz9 : ((Fm.D x ι).R.f * (Fm.D x ι).R.r * (Fm.L x ι).sc.L : ℝ) = z := by rw [hz, zBase]
    rw [hz9]
    rw [Nat.card_eq_fintype_card] at hcard
    have hn0 : (0 : ℝ) < Fintype.card (grpHR fr) := by exact_mod_cast Fintype.card_pos
    have hz0 : 1 ≤ z := by linarith
    have hn3 : (Fintype.card (grpHR fr) : ℝ) ^ 3 ≤ Real.exp (135 * z ^ 2) := by
      rw [← Real.exp_log (pow_pos hn0 3), Real.log_pow]
      exact Real.exp_le_exp.2 (by push_cast; linarith)
    have he : Real.exp (C * z ^ 9) ^ 2 = Real.exp (2 * C * z ^ 9) := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [he]
    calc (Fintype.card (grpHR fr) : ℝ) ^ 3 * Real.exp (2 * C * z ^ 9)
        ≤ Real.exp (135 * z ^ 2) * Real.exp (2 * C * z ^ 9) :=
          mul_le_mul_of_nonneg_right hn3 (Real.exp_pos _).le
      _ = Real.exp (135 * z ^ 2 + 2 * C * z ^ 9) := by rw [← Real.exp_add]
      _ ≤ Real.exp (2 * (Fm.L x ι).sc.b) := by
          refine Real.exp_le_exp.2 ?_
          have a1 : z ^ 2 ≤ z ^ 9 := pow_le_pow_right₀ hz0 (by norm_num)
          have a2 : z ^ 10 ≤ z ^ 12 := pow_le_pow_right₀ hz0 (by norm_num)
          have a3 : (135 + 2 * C) * z ^ 9 ≤ z * z ^ 9 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          have a4 : z * z ^ 9 = z ^ 10 := by ring
          nlinarith
  have e2 : Gs p i (cZero (Fm.D x ι) ((i : ℕ) + 1)) = Gk p i +
      wtOf (p.T.Q.Dw ((i : ℕ) + 1)) (cZero (Fm.D x ι) ((i : ℕ) + 1) • hodgeWt (p.T.Q.Dw ((i : ℕ) + 1))) 0 := by
    unfold Gs Gk shiftG; rfl
  obtain ⟨n, φ, h1, h2, h3, h4⟩ := mapsCore (grpHR fr) (Nat.le_add_right_of_le hp1) hl.coprime
    (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1))))
    (wtOf (p.T.Q.Dw ((i : ℕ) + 1)) (cZero (Fm.D x ι) ((i : ℕ) + 1) • hodgeWt (p.T.Q.Dw ((i : ℕ) + 1))) 0) (Gk p i) hGW
    hGm hW (hK _ hGk).1 (hK _ hW).1 (fun γ f g hg => ((hK _ hGk).2 γ f g hg).1)
    (fun γ f g hg => ((hK _ hW).2 γ f g hg).1) (fun γ f g hg => ((hK _ hGk).2 γ f g hg).2)
    hDGY.1 hDGY.2.2.1 (GlobalTheory.LevDesc.chiHR fr ψ) u hu hdet _ (Real.exp_pos _).le
    (fun γ f g hg σ => hB γ _ f g hGm hg σ) _ hb (latDeep p i Y) hlat
    (Gs p i (cZero (Fm.D x ι) ((i : ℕ) + 1))) e2.symm
  exact ⟨n, φ, h1, h2, h3, h4⟩
end GlobalTheory.CovTop.DescentMaps
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_maps_of_gram_deep_size_flatDeg : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.MapsCondition := by
  first | exact @_root_.GlobalTheory.CovTop.DescentMaps.covering_descent_maps_compatible_alt | exact _root_.GlobalTheory.CovTop.DescentMaps.covering_descent_maps_compatible_alt | (intros; apply _root_.GlobalTheory.CovTop.DescentMaps.covering_descent_maps_compatible_alt <;> assumption)
end
end
end
