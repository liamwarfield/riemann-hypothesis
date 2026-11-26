module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceStandardChartFubiniStudy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesPresentationUpToOrderTensorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteFreeNbhd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecNonzeroOnFiniteOfGeneratedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFubiniStudyDensityEqOneStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyPullbackChernMassEqDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntPullFubiniStudyEqZeroOfNotDominant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeFderivLtOfNotDominantCharts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeFderivLtOfVolumeImageEqZero
open Set Filter Topology MeasureTheory

namespace GlobalTheory

theorem finrank_range_fderiv_lt_of_volume_image_eq_zero :
    ∀ (n : ℕ) (h : (Fin n → ℂ) → (Fin n → ℂ)) (W : Set (Fin n → ℂ)), IsOpen W → AnalyticOnNhd ℂ h W → volume (h '' W) = 0 → ∀ y ∈ W, Module.finrank ℂ (LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) < n := by
  intro n h W hW ha h0 y hy
  by_contra hlt
  have hn : Module.finrank ℂ (Fin n → ℂ) = n := by simp
  have hle := Submodule.finrank_le
    (LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))
  have htop : LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by omega)
  have hs : HasStrictFDerivAt h (fderiv ℂ h y) y := (ha y hy).hasStrictFDerivAt
  have hmap := hs.map_nhds_eq_of_surj htop
  have hmem : h '' W ∈ 𝓝 (h y) := by
    rw [← hmap]
    exact image_mem_map (hW.mem_nhds hy)
  exact (Measure.measure_pos_of_mem_nhds volume hmem).ne' h0

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeFderivLtOfNotDominantCharts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem finrank_range_fderiv_lt_of_not_dominant : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (A : FinHolAtlas D (CxPts p σ)) (A' : FinHolAtlas D (CxPts q σ)), IsAlgAtlas A → IsAlgAtlas A' → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) ≠ genericPoint X → ∀ j l, ∀ y ∈ (A'.chart j).target, PtsOver.map π hπ (spMap σ) ((A'.chart j).symm y) ∈ (A.chart l).source → Module.finrank ℂ (LinearMap.range (fderiv ℂ (A.chart l ∘ PtsOver.map π hπ (spMap σ) ∘ (A'.chart j).symm) y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) < D := by
  intro k _ X Y _ _ p q σ D A A' hA hA' π hπ hgen j l y hy hyl
  set m := PtsOver.map π hπ (spMap σ) with hm_def
  have hm : ∀ z : CxPts q σ, (m z).1 = z.1 ≫ π := fun _ => rfl
  have hH := hA.holoMap hA' (f := π) hm
  set W := (A'.chart j).target ∩ (A'.chart j).symm ⁻¹' (m ⁻¹' (A.chart l).source) with hW_def
  have hWo : IsOpen W := (A'.chart j).isOpen_inter_preimage_symm
    ((A.chart l).open_source.preimage hH.1)
  have han : AnalyticOnNhd ℂ (A.chart l ∘ m ∘ (A'.chart j).symm) W := hH.2 j l
  set Z : Set X := closure {π (genericPoint Y)} with hZ_def
  have hZc : IsClosed Z := isClosed_closure
  have hZg : genericPoint X ∉ Z := by
    intro h
    have h1 : π (genericPoint Y) ⤳ genericPoint X := specializes_iff_mem_closure.2 h
    have h2 : genericPoint X ⤳ π (genericPoint Y) := genericPoint_specializes _
    exact hgen (h1.antisymm h2).eq
  have hZm : ∀ z : CxPts q σ, (m z).1 (IsLocalRing.closedPoint ℂ) ∈ Z := by
    intro z
    have hs : genericPoint Y ⤳ z.1 (IsLocalRing.closedPoint ℂ) := genericPoint_specializes _
    have := hs.map π.continuous
    rw [hm]
    exact specializes_iff_mem_closure.1 this
  obtain ⟨c, hc⟩ := hA l
  have hnull := GlobalTheory.T.volume_complexPoints_properClosed_chart_field k X p σ D Z hZc hZg c
  have hsub : (A.chart l ∘ m ∘ (A'.chart j).symm) '' W ⊆
      FinChart.toV D ⁻¹' (c.e '' (c.e.source ∩ {x : CxPts p σ | x.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨m ((A'.chart j).symm z), ⟨?_, hZm _⟩, ?_⟩
    · have := hz.2
      rw [hc] at this
      exact this
    · simp only [Function.comp_apply, hc]
      rfl
  have h0 : volume ((A.chart l ∘ m ∘ (A'.chart j).symm) '' W) = 0 :=
    measure_mono_null hsub (FinChart.measurePreserving_toV.quasiMeasurePreserving.preimage_null hnull)
  exact finrank_range_fderiv_lt_of_volume_image_eq_zero D _ W hWo han h0 y ⟨hy, hyl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeFderivLtOfNotDominantChartsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_range_fderiv_lt_of_not_dominant_charts : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (A : FinHolAtlas D (CxPts p σ)) (A' : FinHolAtlas D (CxPts q σ)), IsAlgAtlas A → IsAlgAtlas A' → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) ≠ genericPoint X → ∀ j l, ∀ y ∈ (A'.chart j).target, PtsOver.map π hπ (spMap σ) ((A'.chart j).symm y) ∈ (A.chart l).source → Module.finrank ℂ (LinearMap.range (fderiv ℂ (A.chart l ∘ PtsOver.map π hπ (spMap σ) ∘ (A'.chart j).symm) y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) < D := by
  first | exact @GlobalTheory.finrank_range_fderiv_lt_of_not_dominant | exact GlobalTheory.finrank_range_fderiv_lt_of_not_dominant | (intros; apply GlobalTheory.finrank_range_fderiv_lt_of_not_dominant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntPullFubiniStudyEqZeroOfNotDominant
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory

theorem chernInt_pull_fubiniStudy_eq_zero_of_not_dominant : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim) (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str), (∃ x : PSpace ℂ Y.dim, ¬ π (genericPoint Y.X) ⤳ x) → Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ (fun _ => 1) = 0 := by
  intro Y π hπ ⟨x, hx⟩
  have := ProjSpace.isIntegral_of_isDomain ℂ Y.dim
  obtain ⟨-, -, -, A', hA'⟩ := GlobalTheory.T.complexPoints_smoothProjVariety_compact_manifold Y
  have hA : IsAlgAtlas (ProjAn.finAtlas ℂ (RingHom.id ℂ) Y.dim) := AnRead.isAlgAtlas_finAtlas _
  have hne : π (genericPoint Y.X) ≠ genericPoint (PSpace ℂ Y.dim) := fun h =>
    hx (h ▸ genericPoint_specializes x)
  have hc := (ProjSpace.hermitianTwistingSheaf ℂ Y.dim).cInf (RingHom.id ℂ)
  have hs := (ProjSpace.hermitianTwistingSheaf ℂ Y.dim).isSmooth hA.anRead
  rw [(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y _ _ (hc.pull π hπ)).2 A' hA',
    SameForm.mInt_eq (fun _ => hs.sameForm_pull hA hA' π hπ)]
  exact rankDrop _ A' _ (hA.holoMap hA' (f := π) fun _ => rfl)
    (GlobalTheory.T.finrank_range_fderiv_lt_of_not_dominant_charts ℂ _ _ _ _ _ _ _ A' hA hA' π hπ hne) _ (fun _ => hs.isPotential hA) _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntPullFubiniStudyEqZeroOfNotDominantStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernInt_pull_fubiniStudy_eq_zero_of_not_specializes : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim) (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str), (∃ x : PSpace ℂ Y.dim, ¬ π (genericPoint Y.X) ⤳ x) → Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ (fun _ => 1) = 0 := by
  first | exact @GlobalTheory.chernInt_pull_fubiniStudy_eq_zero_of_not_dominant | exact GlobalTheory.chernInt_pull_fubiniStudy_eq_zero_of_not_dominant | (intros; apply GlobalTheory.chernInt_pull_fubiniStudy_eq_zero_of_not_dominant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFubiniStudyTotal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFubiniStudyTotal
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.FSMass

theorem chern_mass_hermitian_O_one_projective : ∀ N : ℕ, ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).chernPart N 1 Set.univ = 1 ∧ ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).chernPart N (-1) Set.univ = 0 := by
  intro N
  have hproj : IsProjOver (PSpace.str ℂ N) := ProjSpace.isProjOver_str ℂ N
  haveI : IsIntegral (PSpace ℂ N) := ProjSpace.isIntegral_of_isDomain ℂ N
  haveI := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) hproj
  have hC : ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).IsCInf := (ProjSpace.hermitianTwistingSheaf ℂ N).cInf _
  have hSP : ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).SemiPosReg N :=
    (HermLB.semiPos_fs _ _ _ _ _ _ : (ProjSpace.hermitianTwistingSheaf ℂ N).SemiPos N) _
  refine ⟨?_, by rw [Weight.chernPart_neg_eq_zero hC hSP]; rfl⟩
  obtain ⟨c, i, hsrc, htgt, hsub, hφv⟩ := GlobalTheory.T.exists_projSpace_standardChart_fubiniStudy N
  have hmem : c.e.symm 0 ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  have hgen : genericPoint (PSpace ℂ N) ∈ ProjSpace.chart ℂ N 0 := by
    have h0 : c.e.symm 0 ∈ ptsIn (PSpace.str ℂ N) (RingHom.id ℂ) (ProjSpace.chart ℂ N 0) := hsrc ▸ hmem
    exact ((genericPoint_spec (PSpace ℂ N)).mem_open_set_iff (ProjSpace.chart ℂ N 0).isOpen).2
      ⟨_, by simp, mem_ptsIn.1 h0⟩
  have hnull := GlobalTheory.T.chernPart_complement_dense_open_null_field ℂ (PSpace ℂ N) (PSpace.str ℂ N) (RingHom.id ℂ) N hproj _ hgen _
    ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)) 1
  rw [← hsrc] at hnull
  have hmeas : MeasurableSet c.e.source := c.e.open_source.measurableSet
  rw [← union_compl_self c.e.source, measure_union disjoint_compl_right hmeas.compl, hnull, add_zero,
    Weight.chernPart_apply hC 1 c hmeas subset_rfl, c.e.image_source_eq_target, htgt,
    Measure.restrict_univ]
  refine Eq.trans (lintegral_congr fun v => ?_) (GlobalTheory.T.lintegral_fubiniStudy_density_eq_one' N)
  have hv : c.e.symm v ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  rw [AlgChart.chernDens_eq c hC hv (hsub hv), AlgChart.hess, c.e.right_inv (htgt ▸ mem_univ _)]
  have hf : (fun w => ((((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).φ i (c.e.symm w) : ℝ) : ℂ)) =
      fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ) := funext fun w => by rw [hφv w]
  rw [hf, GlobalTheory.T.det_complexHessian_fubiniStudy_potential N v]
  simp
end GlobalTheory.FSMass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFubiniStudyTotalStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_form_fubini_study_total : ∀ N : ℕ, ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).chernPart N 1 Set.univ = 1 ∧ ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).chernPart N (-1) Set.univ = 0 := by
  first | exact @GlobalTheory.FSMass.chern_mass_hermitian_O_one_projective | exact GlobalTheory.FSMass.chern_mass_hermitian_O_one_projective | (intros; apply GlobalTheory.FSMass.chern_mass_hermitian_O_one_projective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassPullMulDegreeField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMeasurePartPreimageCoveringField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMeasurePartPreimageCoveringField
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverChernField

theorem chernPart_preimage_of_cover : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ (ε : ℤˣ) (U : Set (CxPts p σ)), IsOpen U → ∀ n : ℕ, (∀ y ∈ U, (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = (n : ℕ∞)) → (∀ y ∈ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) → (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → (φ.pull π hπ).chernPart D ε (PtsOver.map π hπ (spMap σ) ⁻¹' U) = (n : ENNReal) * φ.chernPart D ε U := by
  intro k _ X Y _ _ p q σ D hp hq π hπ B φ hφ ε U hU n hfib hchart hlift
  have := CxPts.t2Space_cxPts_of_isProjOver σ hq
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hp
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hq
  have hφ' := hφ.pull π hπ
  unfold Weight.chernPart
  refine GlobalTheory.CoverChern.glueMeas_preimage_of_cover_on (fun c c' => c.holo_trans c')
    (fun c c' y hy hy' => ?_)
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    (PtsOver.continuous_map π hπ _) hU hfib (fun z hz => ?_) hU.measurableSet subset_rfl
  · rw [c.chernDens_trans c' hφ hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]
  · rw [c.chernDens_trans c' hφ' hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]
  · obtain ⟨c, hc⟩ := hchart _ hz
    obtain ⟨c', hz', hc'⟩ := hlift z hz c hc
    exact ⟨c, c', hz', hc, fun w hw _ => ⟨(hc' w hw).2, by
      rw [GlobalTheory.PullChartDens.chernDens_pull_of_chart π hπ φ hφ c c' hc' w hw]⟩⟩

end GlobalTheory.CoverChernField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMeasurePartPreimageCoveringFieldStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernMeasurePart_preimage_covering_field : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ (ε : ℤˣ) (U : Set (CxPts p σ)), IsOpen U → ∀ n : ℕ, (∀ y ∈ U, (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = (n : ℕ∞)) → (∀ y ∈ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) → (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → (φ.pull π hπ).chernPart D ε (PtsOver.map π hπ (spMap σ) ⁻¹' U) = (n : ENNReal) * φ.chernPart D ε U := by
  first | exact @GlobalTheory.CoverChernField.chernPart_preimage_of_cover | exact GlobalTheory.CoverChernField.chernPart_preimage_of_cover | (intros; apply GlobalTheory.CoverChernField.chernPart_preimage_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCoveringChartsGenericallyFiniteField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCoveringChartsGenericallyFiniteField
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false
noncomputable section
open scoped Classical
open GlobalTheory.ChartGlue

namespace GlobalTheory.CoverDegField

theorem exists_open_covering_charts : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → SmoothOfRelativeDimension D p → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ (∀ y ∈ ptsIn p σ U, (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) ∧ (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) := by
  intro k _ X Y _ _ p q σ D hpP hqP hsm π hπ hη hδ
  haveI : SmoothOfRelativeDimension D p := hsm
  haveI : CharZero k := RingHom.charZero σ
  obtain ⟨U₁, t₁, hU₁, hx₁, ht⟩ := GlobalTheory.AlgChart.exists_etale_coords (p := p) (D := D) (genericPoint X)
  obtain ⟨U₂, hU₂, hx₂, hV₂, he₂, hf₂, hr₂⟩ := GlobalTheory.T.exists_affine_etale_finite_free_nbhd k X Y p q hpP hqP π hπ hη hδ
  obtain ⟨U, hxU, hG⟩ := GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover p π D _ _ U₁ U₂ hU₁ hx₁ ⟨t₁, ht⟩ hU₂ hx₂ hV₂ he₂ hf₂ hr₂
  refine ⟨U, hxU, fun y hy => ?_, fun y hy => ?_, fun z hz c hc => ?_⟩
  · rw [GlobalTheory.encard_fibre_eq_encard_ringHom π hπ U hG.1 hG.2.1 σ y hy]
    exact GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank (π.app U).hom _ hG.2.2.2.1 hG.2.2.2.2.1 hG.2.2.2.2.2 _
  · obtain ⟨t, ht⟩ := hG.2.2.1
    obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hG.1 t ht hy
    exact ⟨c, hc⟩
  · set y := PtsOver.map π hπ (spMap σ) z with hy
    have hyc : y ∈ ptsIn p σ c.U := c.source_subset hc
    have hpt : ∀ W : X.Opens, y ∈ ptsIn p σ W → π (z.1 (IsLocalRing.closedPoint ℂ)) ∈ W := by
      intro W hW
      have := mem_ptsIn.1 hW
      exact this
    obtain ⟨V, hV, hzV, h, hVe⟩ := GlobalTheory.CoverDeg.etale_pullback_coords π hπ D _ U hG c.U c.x c.affine c.etale _ (hpt U hz) (hpt c.U hyc)
    obtain ⟨c'', hc'', hU'', hx''⟩ := AlgChart.exists_of_etale (σ := σ) hV _ hVe (mem_ptsIn.2 hzV)
    have key : ∀ w ∈ c''.e.source, w ∈ ptsIn q σ V ∧
        ∀ a, c''.e w a = ev q σ V ((π.appLE c.U V h).hom (c.x a)) w := by
      rcases c'' with ⟨e, U', aff, x', et, ss, ae, ho⟩
      dsimp only at hU'' hx'' ⊢
      subst hU''
      have hx : x' = fun a => (π.appLE c.U U' h).hom (c.x a) := hx''
      subst hx
      exact fun w hw => ⟨ss hw, ae w hw⟩
    have hS : IsOpen (c''.e.source ∩ PtsOver.map π hπ (spMap σ) ⁻¹' c.e.source) :=
      (PtsOver.continuous_map π hπ (spMap σ)).continuousOn.isOpen_inter_preimage c''.e.open_source
        c.e.open_source
    refine ⟨c''.restr _ hS, ⟨hc'', hc'', hc⟩, fun w hw => ⟨hw.2.2, ?_⟩⟩
    have hw' : w ∈ c''.e.source := hw.1
    obtain ⟨hwV, hwe⟩ := key w hw'
    ext a
    change c''.e w a = c.e (PtsOver.map π hπ (spMap σ) w) a
    rw [hwe a, c.apply_eq _ hw.2.2 a]
    exact valR_appLE w.1 π h hwV _

end GlobalTheory.CoverDegField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCoveringChartsGenericallyFiniteFieldStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_covering_charts_generically_finite_field : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → SmoothOfRelativeDimension D p → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ (∀ y ∈ ptsIn p σ U, (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) ∧ (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) := by
  first | exact @GlobalTheory.CoverDegField.exists_open_covering_charts | exact GlobalTheory.CoverDegField.exists_open_covering_charts | (intros; apply GlobalTheory.CoverDegField.exists_open_covering_charts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassPullMulDegreeField
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.ChernMassPull

theorem mass : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → SmoothOfRelativeDimension D p → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ ε : ℤˣ, (φ.pull π hπ).chernPart D ε Set.univ = (π.residueDegree (genericPoint Y) : ENNReal) * φ.chernPart D ε Set.univ := by
  intro k _ X Y _ _ p q σ D hX hY hsm π hπ hη hδ B φ hφ ε
  obtain ⟨U, hUη, hcard, hchart, hlift⟩ := GlobalTheory.T.exists_open_covering_charts_generically_finite_field k X Y p q σ D hX hY hsm π hπ hη hδ
  have hpre : PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ U = ptsIn q σ (π ⁻¹ᵁ U) := by
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have h0Y := GlobalTheory.T.chernPart_complement_dense_open_null_field k Y q σ D hY (π ⁻¹ᵁ U) (by simp [hη, hUη]) _ (φ.pull π hπ) ε
  have h0X := GlobalTheory.T.chernPart_complement_dense_open_null_field k X p σ D hX U hUη B φ ε
  have h3 := GlobalTheory.T.chernMeasurePart_preimage_covering_field k X Y p q σ D hX hY π hπ B φ hφ ε (ptsIn p σ U) (isOpen_ptsIn U) _
    hcard hchart hlift
  rw [hpre] at h3
  rw [← measure_add_measure_compl (isOpen_ptsIn (π ⁻¹ᵁ U)).measurableSet, h0Y, add_zero, h3,
    ← measure_add_measure_compl (isOpen_ptsIn (p := p) (σ := σ) U).measurableSet, h0X, add_zero]

end GlobalTheory.ChernMassPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassPullMulDegreeFieldStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernMass_pull_mul_degree_field : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → SmoothOfRelativeDimension D p → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ ε : ℤˣ, (φ.pull π hπ).chernPart D ε Set.univ = (π.residueDegree (genericPoint Y) : ENNReal) * φ.chernPart D ε Set.univ := by
  first | exact @GlobalTheory.ChernMassPull.mass | exact GlobalTheory.ChernMassPull.mass | (intros; apply GlobalTheory.ChernMassPull.mass <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqDegreeMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqDegreeMul
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjFormulaTop

theorem topSelf_pull_eq_mul : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k] (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X ≤ D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom p; letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = (π.residueDegree (genericPoint Y) : ℤ) * topSelfIntersection k B D := by
  intro k _ X Y _ _ p q _ D hp hq hD π hπ hgen hdeg B hB
  obtain ⟨U, hU, hgU, hU', -, hfin, hfree, hrank⟩ :=
    GlobalTheory.T.exists_affine_etale_finite_free_nbhd k X Y p q hp hq π hπ hgen hdeg
  subst hπ
  letI := GlobalTheory.algebraΓOfHom p
  letI := GlobalTheory.algebraΓOfHom (π ≫ p)
  rw [topSelf_def, topSelf_def]
  letI := (π.app U).hom.toAlgebra
  have hfin' : Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := hfin
  exact GlobalTheory.FieldProj.interNum_pull_eq_mul k Y X p π hq hp U _ hgU hU hU'
    ⟨hfree, hfin', hrank⟩ D hD (fun _ => B) (fun _ => hB)

end GlobalTheory.ProjFormulaTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqDegreeMulStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topSelfIntersection_pullback_eq_degree_mul : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k] (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X ≤ D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom p; letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = (π.residueDegree (genericPoint Y) : ℤ) * topSelfIntersection k B D := by
  first | exact @GlobalTheory.ProjFormulaTop.topSelf_pull_eq_mul | exact GlobalTheory.ProjFormulaTop.topSelf_pull_eq_mul | (intros; apply GlobalTheory.ProjFormulaTop.topSelf_pull_eq_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionO1Projective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionO1Projective
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjSpaceDegree

theorem topSelf_O1_str : ∀ (k : Type) [Field k] (N : ℕ),
    letI := GlobalTheory.algebraΓOfHom (PSpace.str k N); topSelfIntersection k (ProjSpace.O1 k N) N = 1 :=
  fun k _ N => GlobalTheory.NefNumericsModel.selfIntersection_O1 k N

end GlobalTheory.ProjSpaceDegree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionO1ProjectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_self_intersection_O1_projective : ∀ (k : Type) [Field k] (N : ℕ), letI := GlobalTheory.algebraΓOfHom (PSpace.str k N); topSelfIntersection k (ProjSpace.O1 k N) N = 1 := by
  first | exact @GlobalTheory.ProjSpaceDegree.topSelf_O1_str | exact GlobalTheory.ProjSpaceDegree.topSelf_O1_str | (intros; apply GlobalTheory.ProjSpaceDegree.topSelf_O1_str <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceIntegralSmoothProjectiveDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceIntegralSmoothProjectiveDim
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem pspace_integral_dim_proj_smooth :
    ∀ (k : Type) [Field k] (N : ℕ), IsIntegral (PSpace k N) ∧ topologicalKrullDim (PSpace k N) = N ∧ IsProjOver (PSpace.str k N) ∧ SmoothOfRelativeDimension N (PSpace.str k N) :=
  fun k _ N => ⟨ProjSpace.isIntegral_of_isDomain k N, ProjSpace.topologicalKrullDim_eq k N,
    ⟨N, 𝟙 _, inferInstance, by simp⟩, inferInstance⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceIntegralSmoothProjectiveDimStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveSpace_integral_smooth_projective_dim : ∀ (k : Type) [Field k] (N : ℕ), IsIntegral (PSpace k N) ∧ topologicalKrullDim (PSpace k N) = N ∧ IsProjOver (PSpace.str k N) ∧ SmoothOfRelativeDimension N (PSpace.str k N) := by
  first | exact @GlobalTheory.pspace_integral_dim_proj_smooth | exact GlobalTheory.pspace_integral_dim_proj_smooth | (intros; apply GlobalTheory.pspace_integral_dim_proj_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyPullbackChernMassEqDegree
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FubiniStudyPull

theorem fubiniStudy_pullback_chern_mass_eq_degree : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim)
    (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str),
    Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ
      (fun _ => 1) = (topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℝ) := by
  intro Y π hπ
  obtain ⟨hPI, hPdim, hPproj, hPsm⟩ := GlobalTheory.T.projectiveSpace_integral_smooth_projective_dim ℂ Y.dim
  haveI := hPI
  by_cases hη : π (genericPoint Y.X) = genericPoint (PSpace ℂ Y.dim)
  · have hδ := GlobalTheory.T.residueDegree_genericPoint_ne_zero_projective_same_dim ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str Y.dim hPproj
      Y.isProjOver hPdim Y.topologicalKrullDim_eq π hπ hη
    have hm := fun ε => GlobalTheory.T.chernMass_pull_mul_degree_field ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str (RingHom.id ℂ)
      Y.dim hPproj Y.isProjOver hPsm π hπ hη hδ (ProjSpace.hermitianTwistingSheaf ℂ Y.dim).B
      ((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)) ((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).cInf _) ε
    obtain ⟨h1, h0⟩ := GlobalTheory.T.chern_form_fubini_study_total Y.dim
    have hi := GlobalTheory.T.topSelfIntersection_pullback_eq_degree_mul ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str Y.dim hPproj
      Y.isProjOver hPdim.le π hπ hη hδ (ProjSpace.O1 ℂ Y.dim) (ProjSpace.O1_isLB ℂ Y.dim)
    have ht := GlobalTheory.T.top_self_intersection_O1_projective ℂ Y.dim
    rw [GdegPullProof.chernInt_one, hm 1, hm (-1), h1, h0]
    change _ = ((topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℤ) : ℝ)
    rw [hi, ht]
    simp
  · have hc := GlobalTheory.T.chernInt_pull_fubiniStudy_eq_zero_of_not_specializes Y π hπ ⟨genericPoint (PSpace ℂ Y.dim), fun h =>
      hη (h.antisymm (genericPoint_specializes _)).eq⟩
    have hn := GlobalTheory.T.topSelfIntersection_pullback_eq_zero_of_not_dominant ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str Y.dim Y.isProjOver
      hPdim.le Y.topologicalKrullDim_eq.le π hη (ProjSpace.O1 ℂ Y.dim) (ProjSpace.O1_isLB ℂ Y.dim)
    rw [hc]
    change (0 : ℝ) = ((topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℤ) : ℝ)
    rw [hn]
    simp

end GlobalTheory.FubiniStudyPull

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyPullbackChernMassEqDegreeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernInt_pull_fubiniStudy_eq_topSelf : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim) (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str), Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℝ) := by
  first | exact @GlobalTheory.FubiniStudyPull.fubiniStudy_pullback_chern_mass_eq_degree | exact GlobalTheory.FubiniStudyPull.fubiniStudy_pullback_chern_mass_eq_degree | (intros; apply GlobalTheory.FubiniStudyPull.fubiniStudy_pullback_chern_mass_eq_degree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDimSuccGeneratingSectionsInfiniteField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTopologicalKrullDimDiffOpenLt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTopologicalKrullDimDiffOpenLt
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.Div

theorem exists_finite_topologicalKrullDim_diff_lt :
    ∀ (T : Type) [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T] [T0Space T] (Z : Set T),
      IsClosed Z → ∃ S : Set T, S.Finite ∧ ∀ U : Set T, IsOpen U → S ⊆ U → ∀ d : ℕ,
        (topologicalKrullDim Z < (d + 1 : ℕ) → topologicalKrullDim (Z \ U : Set T) < (d : ℕ)) := by
  intro T _ _ _ _ Z _
  have hfin : (irreducibleComponents Z).Finite := NoetherianSpace.finite_irreducibleComponents
  have hne : ∀ K : irreducibleComponents Z, ∃ x : Z, x ∈ (K : Set Z) := fun K => K.2.1.nonempty
  choose p hp using hne
  haveI : Finite (irreducibleComponents Z) := hfin.to_subtype
  refine ⟨Set.range (fun K => (p K : T)), Set.finite_range _, fun U _ hSU d hd => ?_⟩
  have hsub : (Z \ U : Set T) ⊆ Z := Set.diff_subset
  have hi : IsInducing (Set.inclusion hsub) := (IsEmbedding.inclusion hsub).isInducing
  have hcl : IsClosed {x : Z | (x : T) ∉ U} :=
    (IsOpen.preimage continuous_subtype_val ‹IsOpen U›).isClosed_compl
  refine Order.krullDim_lt_coe_iff.2 fun s => ?_
  have hm := IrreducibleCloseds.map_strictMono_of_isInducing hi
  let s' := s.map _ hm
  obtain ⟨K, hK, hsK⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (s'.last : Set Z) s'.last.isIrreducible
  let K' : IrreducibleCloseds Z := ⟨K, hK.1, isClosed_of_mem_irreducibleComponents K hK⟩
  have hlast : (s'.last : Set Z) ⊆ {x : Z | (x : T) ∉ U} := by
    have : s'.last = IrreducibleCloseds.map _ hi.continuous s.last := by
      simp [s']
    rw [this]
    refine closure_minimal ?_ hcl
    rintro _ ⟨y, -, rfl⟩
    exact y.2.2
  have hlt : s'.last < K' := by
    refine lt_of_le_of_ne hsK fun h => ?_
    have h1 : p ⟨K, hK⟩ ∈ (s'.last : Set Z) := by
      rw [h]; exact hp ⟨K, hK⟩
    exact hlast h1 (hSU ⟨⟨K, hK⟩, rfl⟩)
  have h2 := Order.krullDim_lt_coe_iff.1 hd (s'.snoc K' hlt)
  simp [s'] at h2
  exact h2

end GlobalTheory.Div
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTopologicalKrullDimDiffOpenLtStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_topologicalKrullDim_diff_open_lt : ∀ (T : Type) [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T] [T0Space T] (Z : Set T), IsClosed Z → ∃ S : Set T, S.Finite ∧ ∀ U : Set T, IsOpen U → S ⊆ U → ∀ d : ℕ, (topologicalKrullDim Z < (d + 1 : ℕ) → topologicalKrullDim (Z \ U : Set T) < (d : ℕ)) := by
  first | exact @GlobalTheory.Div.exists_finite_topologicalKrullDim_diff_lt | exact GlobalTheory.Div.exists_finite_topologicalKrullDim_diff_lt | (intros; apply GlobalTheory.Div.exists_finite_topologicalKrullDim_diff_lt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDimSuccGeneratingSectionsInfiniteField
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.GenCut

theorem isEmpty_of_topologicalKrullDim_lt_zero (T : Type) [TopologicalSpace T]
    (h : topologicalKrullDim T < ((0 : ℕ) : WithBot ℕ∞)) : IsEmpty T := by
  by_contra hT
  rw [not_isEmpty_iff] at hT
  obtain ⟨x⟩ := hT
  haveI : Nonempty (IrreducibleCloseds T) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim T := Order.krullDim_nonneg
  exact absurd h (not_lt.mpr (by simpa using h0))

theorem exists_sections_cover_closed (k : Type) [Field k] [Infinite k] (X : Scheme.{0})
    [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X) (hL : L.IsLB)
    (n : ℕ) (u : Fin n → L.Sec) (hu : ⨆ i, nonzeroLocus (u i) = ⊤) (e : ℕ) :
    ∀ Z : Set X, IsClosed Z → topologicalKrullDim Z < (e : ℕ) →
      ∃ s : Fin e → L.Sec, ∀ x ∈ Z, ∃ i, x ∈ nonzeroLocus (s i) := by
  induction e with
  | zero =>
    intro Z _ h
    have := isEmpty_of_topologicalKrullDim_lt_zero Z h
    exact ⟨Fin.elim0, fun x hx => (this.false ⟨x, hx⟩).elim⟩
  | succ e ih =>
    intro Z hZ h
    obtain ⟨S, hS, hdim⟩ := GlobalTheory.T.exists_finite_topologicalKrullDim_diff_open_lt X Z hZ
    obtain ⟨t, ht⟩ := GlobalTheory.T.exists_sec_nonzero_on_finite_of_generated' k X p L hL n u hu S hS
    have hU : IsOpen ((nonzeroLocus t : X.Opens) : Set X) := (nonzeroLocus t).isOpen
    obtain ⟨s, hs⟩ := ih (Z \ ((nonzeroLocus t : X.Opens) : Set X)) (hZ.sdiff hU)
      (hdim _ hU (fun x hx => ht x hx) e h)
    refine ⟨Fin.cons t s, fun x hx => ?_⟩
    by_cases hxt : x ∈ nonzeroLocus t
    · exact ⟨0, by simpa using hxt⟩
    · obtain ⟨i, hi⟩ := hs x ⟨hx, hxt⟩
      exact ⟨i.succ, by simpa using hi⟩

theorem exists_generating_sections_of_dim_le :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X), L.IsLB → ∀ d : ℕ, topologicalKrullDim X ≤ d → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∃ s : Fin (d + 1) → L.Sec, ⨆ i, nonzeroLocus (s i) = ⊤ := by
  intro k _ _ X _ p L hL d hd n u hu
  have h1 : topologicalKrullDim (Set.univ : Set X) ≤ topologicalKrullDim X :=
    topologicalKrullDim_subspace_le X _
  have h2 : ((d : ℕ) : WithBot ℕ∞) < ((d + 1 : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast Nat.lt_succ_self d
  obtain ⟨s, hs⟩ := exists_sections_cover_closed k X p L hL n u hu (d + 1) Set.univ isClosed_univ
    (lt_of_le_of_lt (h1.trans hd) h2)
  refine ⟨s, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨i, hi⟩ := hs x (Set.mem_univ x)
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

end GlobalTheory.GenCut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDimSuccGeneratingSectionsInfiniteFieldStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dimSucc_generating_sections_infiniteField : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X), L.IsLB → ∀ d : ℕ, topologicalKrullDim X ≤ d → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∃ s : Fin (d + 1) → L.Sec, ⨆ i, nonzeroLocus (s i) = ⊤ := by
  first | exact @GlobalTheory.GenCut.exists_generating_sections_of_dim_le | exact GlobalTheory.GenCut.exists_generating_sections_of_dim_le | (intros; apply GlobalTheory.GenCut.exists_generating_sections_of_dim_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralEqOfLineBundleIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralTopIndependentOfSmoothWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralTopIndependentOfSmoothWeight
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ChernMass

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {L : LB X}

theorem sub_pick_eq (φ ψ : Weight p σ L) {y : CxPts p σ} {i : L.ι} (hi : y ∈ ptsIn p σ (L.U i)) :
    ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y = ψ.φ i y - φ.φ i y := by
  rw [ψ.trans _ i y (mem_pick φ.isLB y) hi, φ.trans _ i y (mem_pick φ.isLB y) hi]
  ring

theorem cInfAt_half_sub {φ ψ : Weight p σ L} (hφ : φ.IsCInf) (hψ : ψ.IsCInf) (x : CxPts p σ) :
    CInfAt (fun y => (ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y) / 2) x := by
  have hx := mem_pick φ.isLB x
  refine (((hψ _ x hx).add (hφ _ x hx).neg).const_mul 2⁻¹).congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds hx] with z hz
  rw [sub_pick_eq φ ψ hz]
  ring

theorem mInt_one_eq {D : ℕ} [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    {A : FinHolAtlas D (CxPts p σ)} (hA : IsAlgAtlas A) {φ ψ : Weight p σ L} (hφ : φ.IsCInf)
    (hψ : ψ.IsCInf) :
    mInt A (fun _ => φ.locPot) (fun _ => 1) = mInt A (fun _ => ψ.locPot) (fun _ => 1) := by
  have hP : IsPotential A φ.locPot :=
    ((Weight.isCInf_iff_isSmooth hA.anRead).1 hφ).isPotential hA
  have hu : A.Smooth fun y => (ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y) / 2 :=
    (hA.smooth_iff hA.anRead).2 ((cInfAt_iff_smoothOn hA.anRead isOpen_univ).1
      fun y _ => cInfAt_half_sub hφ hψ y)
  rw [← massIndep A (fun _ => φ.locPot) (fun _ => _) (fun _ => hP) fun _ => hu]
  refine SameForm.mInt_eq (fun _ j y hy => hessCGerm _ _ _ ?_) _
  refine eventually_of_mem (((A.chart j).isOpen_inter_preimage_symm (isOpen_ptsIn _)).mem_nhds
    ⟨hy, mem_pick φ.isLB ((A.chart j).symm y)⟩) fun w hw => ?_
  change φ.φ _ _ / 2 + (_ - _) / 2 = ψ.φ (pick φ.isLB _) _ / 2
  rw [sub_pick_eq φ ψ hw.2]
  ring

theorem chernInt_one_eq : ∀ (Y : Var ℂ) (L : LB Y.X) (φ ψ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ψ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = Weight.chernInt ψ Y.dim Set.univ (fun _ => 1) := fun Y L φ ψ hφ hψ => by
  obtain ⟨h₁, h₂, -, A, hA⟩ := GlobalTheory.T.complexPoints_smoothProjVariety_compact_manifold Y
  rw [(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y L φ hφ).2 A hA, (GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y L ψ hψ).2 A hA]
  exact mInt_one_eq hA hφ hψ

end GlobalTheory.ChernMass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralTopIndependentOfSmoothWeightStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernIntegral_top_independent_of_smooth_weight : ∀ (Y : Var ℂ) (L : LB Y.X) (φ ψ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ψ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = Weight.chernInt ψ Y.dim Set.univ (fun _ => 1) := by
  first | exact @GlobalTheory.ChernMass.chernInt_one_eq | exact GlobalTheory.ChernMass.chernInt_one_eq | (intros; apply GlobalTheory.ChernMass.chernInt_one_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassLineBundleWeightOfIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassLineBundleWeightOfIso
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory.ChartGlue
open scoped ContDiff

namespace GlobalTheory.ChernIso

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {A B : LB X} {φ : Weight p σ B} {D : ℕ}

theorem cInfAt_log_normSq {W : X.Opens} (g : Γ(X, W)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W)
    (h0 : ev p σ W g y ≠ 0) : CInfAt (fun z => Real.log (‖ev p σ W g z‖ ^ 2)) y := by
  have hs : ContDiff ℝ ∞ fun v : Unit → ℂ => ‖v ()‖ ^ 2 := (contDiff_apply ℝ (fun _ => ℂ) ()).norm_sq ℂ
  refine ⟨W, Unit, inferInstance, fun _ => g, fun v => Real.log (‖v ()‖ ^ 2),
    {v | ‖v ()‖ ^ 2 ≠ 0}, hy, isOpen_ne_fun hs.continuous continuous_const,
    pow_ne_zero _ (norm_ne_zero_iff.2 h0), hs.contDiffOn.log fun _ h => h, EventuallyEq.rfl⟩

theorem ofIso_apply (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) {a : A.ι} {b : B.ι}
    {y : CxPts p σ} (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    (φ.ofIso hA w hw).φ a y = φ.φ b y + Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2) := by
  rw [Weight.ofIso, Weight.ofPairs_φ ha hb]

theorem isCInf_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) :
    (φ.ofIso hA w hw).IsCInf := fun a y ha => by
  have hb := mem_pick φ.isLB y
  refine ((h _ y hb).add (cInfAt_log_normSq (w.s (a, pick φ.isLB y)).val
    (mem_ptsIn_inf.2 ⟨ha, hb⟩) (ev_iso_ne_zero w hb ha))).congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds ha, (isOpen_ptsIn _).mem_nhds hb] with z h₁ h₂
  exact ofIso_apply hA w hw h₁ h₂

theorem hess_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen)
    (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) {a : A.ι} {b : B.ι}
    (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    c.hess (φ.ofIso hA w hw) a y = c.hess φ b y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (A.U a ⊓ B.U b))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have hg := c.holo (A.U a ⊓ B.U b) (w.s (a, b)).val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (A.U a ⊓ B.U b),
      (ev p σ (A.U a ⊓ B.U b) (w.s (a, b)).val ∘ c.e.symm) v ≠ 0 := fun v hv =>
    ev_iso_ne_zero w (mem_ptsIn_inf.1 hv.2).2 (mem_ptsIn_inf.1 hv.2).1
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (h b) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : cHess D (fun v => ((Real.log (‖(ev p σ (A.U a ⊓ B.U b) (w.s (a, b)).val ∘
      c.e.symm) v‖ ^ 2) : ℝ) : ℂ)) (c.e y) = 0 := by
    ext i j
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 i j
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [ofIso_apply hA w hw (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, one_mul]
  rfl

theorem chernPart_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) (ε : ℤˣ) :
    (φ.ofIso hA w hw).chernPart D ε = φ.chernPart D ε := by
  refine iSup_congr fun c => Measure.ext fun S hS => ?_
  rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
  refine setLIntegral_congr_fun (measurableSet_image c.e
    (c.e.open_source.measurableSet.inter hS) inter_subset_left) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [c.e.left_inv hy.1]
  rw [AlgChart.chernDens, AlgChart.chernDens,
    hess_ofIso h hA w hw c hy.1 (mem_pick _ y) (mem_pick φ.isLB y)]

theorem chernInt_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen)
    (S : Set (CxPts p σ)) (f : CxPts p σ → ℝ) :
    (φ.ofIso hA w hw).chernInt D S f = φ.chernInt D S f := by
  rw [Weight.chernInt, Weight.chernInt, chernPart_ofIso h, chernPart_ofIso h]

theorem chernMass_ofIso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L)
    (hA : A.IsLB) (w : L.Iso A) (hw : w.IsGen), φ.IsCInf → (φ.ofIso hA w hw).IsCInf ∧
      Weight.chernInt (φ.ofIso hA w hw) Y.dim Set.univ (fun _ => 1) =
        Weight.chernInt φ Y.dim Set.univ (fun _ => 1) :=
  fun _ _ _ _ hA w hw h => ⟨isCInf_ofIso h hA w hw, chernInt_ofIso h hA w hw _ _⟩

end GlobalTheory.ChernIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassLineBundleWeightOfIsoStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernMass_lineBundleWeightOfIso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L) (hA : A.IsLB) (w : L.Iso A) (hw : w.IsGen), φ.IsCInf → (φ.ofIso hA w hw).IsCInf ∧ Weight.chernInt (φ.ofIso hA w hw) Y.dim Set.univ (fun _ => 1) = Weight.chernInt φ Y.dim Set.univ (fun _ => 1) := by
  first | exact @GlobalTheory.ChernIso.chernMass_ofIso | exact GlobalTheory.ChernIso.chernMass_ofIso | (intros; apply GlobalTheory.ChernIso.chernMass_ofIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralEqOfLineBundleIso
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory

theorem chernInt_indep_of_iso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) A), LBIso L A → φ.IsCInf → ψ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = Weight.chernInt ψ Y.dim Set.univ (fun _ => 1) := by
  intro Y L A φ ψ hLA hφ hψ
  obtain ⟨w, hw⟩ := hLA
  obtain ⟨h1, h2⟩ := GlobalTheory.T.chernMass_lineBundleWeightOfIso Y L A φ ψ.isLB w hw hφ
  rw [← h2]
  exact GlobalTheory.T.chernIntegral_top_independent_of_smooth_weight Y A _ ψ h1 hψ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralEqOfLineBundleIsoStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernIntegral_eq_of_lineBundle_iso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) A), LBIso L A → φ.IsCInf → ψ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = Weight.chernInt ψ Y.dim Set.univ (fun _ => 1) := by
  first | exact @GlobalTheory.chernInt_indep_of_iso | exact GlobalTheory.chernInt_indep_of_iso | (intros; apply GlobalTheory.chernInt_indep_of_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPullO1ToProjOfIsLB
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjSpace

theorem lbIso_pull_O1_toProj_of_isLB : ∀ (R : Type) [CommRing R] (N : ℕ) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (f : X ⟶ Sp R) (s : Fin (N + 1) → L.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤), LBIso ((ProjSpace.O1 R N).pull (ProjSpace.toProj f s hs)) L :=
  fun _ _ _ _ _ _ f s hs => GlobalTheory.ProjSpace.lbIso_pullback_O1_toProj f s hs

end GlobalTheory.ProjSpace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassEqSelfIntersectionOfGenerated
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem chernInt_eq_topSelf_of_generated : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  intro Y L φ hφ n u hu
  have hL : L.IsLB := φ.isLB
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_dimSucc_generating_sections_infiniteField ℂ Y.X Y.str L hL Y.dim (Var.topologicalKrullDim_eq Y).le n u hu
  have hπ : ProjSpace.toProj Y.str s hs ≫ PSpace.str ℂ Y.dim = Y.str := ProjSpace.toProj_str Y.str s hs
  have e := GlobalTheory.ProjSpace.lbIso_pull_O1_toProj_of_isLB ℂ Y.dim Y.X L hL Y.str s hs
  have h1 := GlobalTheory.T.chernIntegral_eq_of_lineBundle_iso Y _ L (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull _ hπ) φ e
    (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).cInf (RingHom.id ℂ)).pull _ hπ) hφ
  rw [← h1, GlobalTheory.T.chernInt_pull_fubiniStudy_eq_topSelf Y _ hπ,
    topSelf_congr ℂ (LB.isLB_pull (ProjSpace.O1_isLB ℂ Y.dim) (ProjSpace.toProj Y.str s hs)) hL e]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassEqSelfIntersectionOfGeneratedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernMass_eq_selfIntersection_of_generated : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  first | exact @GlobalTheory.chernInt_eq_topSelf_of_generated | exact GlobalTheory.chernInt_eq_topSelf_of_generated | (intros; apply GlobalTheory.chernInt_eq_topSelf_of_generated <;> assumption)
end
