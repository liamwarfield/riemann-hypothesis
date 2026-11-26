module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLelongFormulaSectionProjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityFormulaLeSemipositive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRegularisedLogNormMixedMeasureDivisors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoIntegralLogAddInv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoIntegralLogAddInv
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem tendsto_integral_log_add_inv : ∀ (T : Type) [MeasurableSpace T] (μ : Measure T) [IsFiniteMeasure μ] (w : T → ℝ) (C : ℝ), Measurable w → (∀ x, 0 ≤ w x ∧ w x ≤ C) → (∀ᵐ x ∂μ, 0 < w x) → Integrable (fun x => Real.log (w x) / 2) μ → Tendsto (fun n : ℕ => ∫ x, Real.log (w x + 1 / ((n : ℝ) + 1)) ∂μ) atTop (𝓝 (2 * ∫ x, Real.log (w x) / 2 ∂μ)) := by
  intro T _ μ _ w C hw hwC hpos hint
  have hint' : Integrable (fun x => Real.log (w x)) μ := by
    refine (hint.const_mul 2).congr (Eventually.of_forall fun x => ?_)
    simp only; ring
  have hlim : 2 * ∫ x, Real.log (w x) / 2 ∂μ = ∫ x, Real.log (w x) ∂μ := by
    rw [← integral_const_mul]; congr 1; ext x; ring
  rw [hlim]
  refine tendsto_integral_of_dominated_convergence (fun x => |Real.log (w x)| + |Real.log (C + 1)|) ?_ ?_ ?_ ?_
  · intro n
    exact (Real.measurable_log.comp (hw.add_const _)).aestronglyMeasurable
  · exact hint'.abs.add (integrable_const _)
  · intro n
    filter_upwards [hpos] with x hx
    have hd : 0 < 1 / ((n:ℝ) + 1) := by positivity
    have hd1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    have h1 : Real.log (w x) ≤ Real.log (w x + 1 / ((n:ℝ)+1)) := Real.log_le_log hx (by linarith)
    have h2 : Real.log (w x + 1 / ((n:ℝ)+1)) ≤ Real.log (C + 1) :=
      Real.log_le_log (by linarith) (by linarith [(hwC x).2])
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (w x)), abs_nonneg (Real.log (C+1))]
    · linarith [le_abs_self (Real.log (C+1)), abs_nonneg (Real.log (w x))]
  · filter_upwards [hpos] with x hx
    have h : Tendsto (fun n : ℕ => w x + 1 / ((n:ℝ) + 1)) atTop (𝓝 (w x + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h
    exact (Real.continuousAt_log hx.ne').tendsto.comp h

end GlobalTheory.Mix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoIntegralLogAddInvStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_integral_log_add_inv_succ : ∀ (T : Type) [MeasurableSpace T] (μ : Measure T) [IsFiniteMeasure μ] (w : T → ℝ) (C : ℝ), Measurable w → (∀ x, 0 ≤ w x ∧ w x ≤ C) → (∀ᵐ x ∂μ, 0 < w x) → Integrable (fun x => Real.log (w x) / 2) μ → Tendsto (fun n : ℕ => ∫ x, Real.log (w x + 1 / ((n : ℝ) + 1)) ∂μ) atTop (𝓝 (2 * ∫ x, Real.log (w x) / 2 ∂μ)) := by
  first | exact @GlobalTheory.Mix.tendsto_integral_log_add_inv | exact GlobalTheory.Mix.tendsto_integral_log_add_inv | (intros; apply GlobalTheory.Mix.tendsto_integral_log_add_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRegularisedLogNormMixedMeasureDivisors
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix.LogLim

theorem compactSpace_of_proj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem nsq_nonneg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (N : MLine p σ) (t : N.B.Sec) (y : CxPts p σ) : 0 ≤ N.φ.nsq (secVal p σ t) y := by
  unfold Weight.nsq; positivity

theorem continuous_nsq {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (N : MLine p σ) (t : N.B.Sec) : Continuous (N.φ.nsq (secVal p σ t)) :=
  continuous_iff_continuousAt.2 fun y => ((GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties k X p σ N t).2.2.1 y).continuousAt

theorem exists_nsq_le {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (hp : IsProjOver p) (N : MLine p σ) (t : N.B.Sec) : ∃ C : ℝ, ∀ y, N.φ.nsq (secVal p σ t) y ≤ C := by
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hp
  obtain ⟨C, hC⟩ := (isCompact_univ.image (continuous_nsq N t)).bddAbove
  exact ⟨C, fun y => hC ⟨y, Set.mem_univ _, rfl⟩⟩

end GlobalTheory.Mix.LogLim


open GlobalTheory.Mix.LogLim in
theorem GlobalTheory.Mix.tendsto_logReg : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (N : MLine p σ) (t : N.B.Sec), (genericPoint X ∈ nonzeroLocus t → ∀ L : Fin (e + 1) → MLine p σ, Tendsto (fun n : ℕ => Mix.int L fun y => Real.log (N.φ.nsq (secVal p σ t) y + 1 / ((n : ℝ) + 1))) atTop (𝓝 (2 * Mix.int L (N.logSec t)))) ∧ ∀ (L : Fin e → MLine p σ) (Δ : CartierDiv X), (∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus t) → Tendsto (fun n : ℕ => ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (fun y => Real.log (N.φ.nsq (secVal p σ t) y + 1 / ((n : ℝ) + 1))) z) atTop (𝓝 (2 * ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (N.logSec t) z)) := by
  intro hP F _ X _ _ p σ e hp hdim N t
  set w := N.φ.nsq (secVal p σ t) with hw_def
  have hbasic := GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties F X p σ N t
  have hcont : Continuous w := continuous_nsq N t
  obtain ⟨C, hC⟩ := exists_nsq_le hp N t
  have hwC : ∀ y, 0 ≤ w y ∧ w y ≤ C := fun y => ⟨nsq_nonneg N t y, hC y⟩
  refine ⟨fun hgen L => ?_, fun L Δ hΔ => ?_⟩
  · have hfin := (GlobalTheory.T.mixedChernMeasure_finite_integrable_projective hP F X p σ (e + 1) hp hdim L).1
    have hint := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hp hdim L N t hgen
    have one (ε : ℤˣ) (hi : Integrable (N.logSec t) (part L ε)) :
        Tendsto (fun n : ℕ => ∫ y, Real.log (w y + 1 / ((n : ℝ) + 1)) ∂part L ε) atTop
          (𝓝 (2 * ∫ y, Real.log (w y) / 2 ∂part L ε)) := by
      haveI := hfin ε
      have hnull := GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero F X p σ σ.injective hp (e + 1) L ε (nonzeroLocus t) hgen
      refine GlobalTheory.T.tendsto_integral_log_add_inv_succ _ (part L ε) w C hcont.measurable hwC ?_ hi
      refine ae_iff.2 (measure_mono_null (fun y hy => ?_) hnull)
      exact fun h => hy ((hbasic.2.1 y).2 h)
    have h1 := one 1 hint.1
    have h2 := one (-1) hint.2
    simp only [Mix.int, MLine.logSec, mul_sub]
    exact h1.sub h2
  · haveI : CompactSpace X := compactSpace_of_proj hp
    have hS := Δ.finite_support_mult
    have hsub (f : X → ℝ) : Function.support (fun z => (Δ.mult z : ℝ) * f z) ⊆ ↑hS.toFinset := by
      intro z hz
      simp only [Set.Finite.coe_toFinset, Function.mem_support]
      intro h0; apply hz; simp [h0]
    have hrw : (fun n : ℕ => ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (fun y => Real.log (w y + 1 / ((n : ℝ) + 1))) z) =
        fun n : ℕ => ∑ z ∈ hS.toFinset, (Δ.mult z : ℝ) * cycInt L (fun y => Real.log (w y + 1 / ((n : ℝ) + 1))) z :=
      funext fun n => finsum_eq_sum_of_support_subset _ (hsub _)
    rw [hrw, finsum_eq_sum_of_support_subset _ (hsub _), Finset.mul_sum]
    refine tendsto_finsetSum _ fun z hz => ?_
    have hz0 : Δ.mult z ≠ 0 := by simpa using hz
    have hcoh := CartierDiv.coheight_eq_one_of_mult_ne_zero hz0
    have hdz := (GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hdim z).1 hcoh
    obtain ⟨hfin, -, hnull, hlog⟩ := GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure hP F X p σ hp e L z hdz
    have hzt := hΔ z hz0
    have hint := hlog N t hzt
    set π := ptMap (closι z) rfl σ with hπ
    have hπc : Continuous π := continuous_of_comp (f := closι z) fun _ => rfl
    have one (ε : ℤˣ) (hi : Integrable (fun y => N.logSec t (π y)) (part (fun i => (L i).pull (closι z) rfl) ε)) :
        Tendsto (fun n : ℕ => ∫ y, Real.log (w (π y) + 1 / ((n : ℝ) + 1)) ∂part (fun i => (L i).pull (closι z) rfl) ε)
          atTop (𝓝 (2 * ∫ y, Real.log (w (π y)) / 2 ∂part (fun i => (L i).pull (closι z) rfl) ε)) := by
      haveI := hfin ε
      refine GlobalTheory.T.tendsto_integral_log_add_inv_succ _ _ (fun y => w (π y)) C (hcont.comp hπc).measurable (fun y => hwC (π y)) ?_ hi
      refine ae_iff.2 (measure_mono_null (fun y hy => ?_) (hnull (nonzeroLocus t) hzt ε))
      exact fun h => hy ((hbasic.2.1 (π y)).2 h)
    have h1 := one 1 hint.1
    have h2 := one (-1) hint.2
    have := (h1.sub h2).const_mul (Δ.mult z : ℝ)
    simp only [cycInt, Mix.int, MLine.logSec] at this ⊢
    convert this using 2
    ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRegularisedLogNormMixedMeasureDivisorsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_regularisedLogNorm_mixedMeasure_divisors : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (N : MLine p σ) (t : N.B.Sec), (genericPoint X ∈ nonzeroLocus t → ∀ L : Fin (e + 1) → MLine p σ, Tendsto (fun n : ℕ => Mix.int L fun y => Real.log (N.φ.nsq (secVal p σ t) y + 1 / ((n : ℝ) + 1))) atTop (𝓝 (2 * Mix.int L (N.logSec t)))) ∧ ∀ (L : Fin e → MLine p σ) (Δ : CartierDiv X), (∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus t) → Tendsto (fun n : ℕ => ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (fun y => Real.log (N.φ.nsq (secVal p σ t) y + 1 / ((n : ℝ) + 1))) z) atTop (𝓝 (2 * ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (N.logSec t) z)) := by
  first | exact @GlobalTheory.Mix.tendsto_logReg | exact GlobalTheory.Mix.tendsto_logReg | (intros; apply GlobalTheory.Mix.tendsto_logReg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralDdcPairingSymmProjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralDdcPairingSymmProjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem mInt_half {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (g : X → ℝ) (hg : Continuous g) :
    mInt A Φ (fun x => g x / 2) = mInt A Φ g / 2 := by
  have h0 := mIntegrableCont A Φ hΦ (fun _ => 0) continuous_const
  have h1 := mIntLinear A Φ hΦ 1 (fun _ => 0) (fun _ => 0) h0 h0
  have h2 := mIntLinear A Φ hΦ (1 / 2) g (fun _ => 0) (mIntegrableCont A Φ hΦ g hg) h0
  have e1 : (fun x => 1 / 2 * g x + 0) = fun x => g x / 2 := funext fun x => by ring
  simp only [mul_zero, add_zero] at h1
  rw [e1] at h2
  linarith

theorem mInt_cons_ofFun_symm {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {e : ℕ}
    [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] {A : FinHolAtlas (e + 1) (CxPts p σ)} (hA : IsAlgAtlas A)
    (L : Fin e → MLine p σ) (u v : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (hv : ∀ y, CInfAt v y) :
    mInt A (fun i => ((Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) i).φ.locPot) v =
      mInt A (fun i => ((Fin.cons (MLine.ofFun v hv) L : Fin (e + 1) → MLine p σ) i).φ.locPot) u := by
  have hpot (N : MLine p σ) : IsPotential A N.φ.locPot :=
    ((Weight.isCInf_iff_isSmooth hA.anRead).1 N.cInf).isPotential hA
  have hsm (a : CxPts p σ → ℝ) (ha : ∀ y, CInfAt a y) : A.Smooth fun y => a y / 2 := fun j =>
    ((hA.smooth_iff hA.anRead).2 ((cInfAt_iff_smoothOn hA.anRead isOpen_univ).1 fun y _ => ha y) j).div_const 2
  have key (a b : CxPts p σ → ℝ) (ha : ∀ y, CInfAt a y) (hb : ∀ y, CInfAt b y) :
      mInt A (Fin.cons (LocPot.ofFun fun y => a y / 2) fun i => (L i).φ.locPot) (fun y => b y / 2) =
      mInt A (fun i => ((Fin.cons (MLine.ofFun a ha) L : Fin (e + 1) → MLine p σ) i).φ.locPot) b / 2 := by
    rw [← mInt_half A _ (fun i => hpot _) b (continuous_iff_continuousAt.2 fun y => (hb y).continuousAt)]
    refine SameForm.mInt_eq (fun i => ?_) _
    refine Fin.cases ?_ (fun j => ?_) i
    · exact fun _ _ _ => rfl
    · exact fun _ _ _ => rfl
  have h := byPartsSymm A _ _ (hsm v hv) (hsm u hu) (fun i => (L i).φ.locPot) fun i => hpot _
  rw [key u v hu hv, key v u hv hu] at h
  linarith

theorem int_cons_ofFun_symm : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (u v : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (hv : ∀ y, CInfAt v y), Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) v = Mix.int (Fin.cons (MLine.ofFun v hv) L : Fin (e + 1) → MLine p σ) u := by
  intro hP F _ X _ _ p σ e hproj hdim L u v hu hv
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hY, π, hsm, hprojY, -, hgen, hdeg, -⟩ :=
    GlobalTheory.T.exists_logResolution_projective_of_principalisation hP F X p (e + 1) hproj hdim ⊥
      (by rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot]; exact Set.notMem_empty _)
  haveI := hsm
  haveI : CompactSpace (CxPts (π ≫ p) σ) := CxPts.compactSpace σ hprojY
  haveI : T2Space (CxPts (π ≫ p) σ) := CxPts.t2Space_cxPts_of_isProjOver σ hprojY
  haveI : SecondCountableTopology (CxPts (π ≫ p) σ) := CxPts.secondCountableTopology_of_isProjOver σ hprojY
  have hA : IsAlgAtlas (AnRead.all (π ≫ p) σ (e + 1)).finAtlas := AnRead.isAlgAtlas_finAtlas _
  have hiso := GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus F X Y p (π ≫ p) σ π rfl
  have hisoY := GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus F Y Y (π ≫ p) (π ≫ p) σ (𝟙 Y) (Category.id_comp _)
  have key (a b : CxPts p σ → ℝ) (ha : ∀ y, CInfAt a y) (hb : ∀ y, CInfAt b y) :
      Mix.int (Fin.cons (MLine.ofFun a ha) L : Fin (e + 1) → MLine p σ) b =
      mInt (AnRead.all (π ≫ p) σ (e + 1)).finAtlas (fun i => ((Fin.cons (MLine.ofFun (fun z => a (ptMap π rfl σ z))
        fun z => (ha _).pull π rfl) fun i => (L i).pull π rfl : Fin (e + 1) → MLine (π ≫ p) σ) i).φ.locPot)
        (fun z => b (ptMap π rfl σ z)) := by
    have hbc : Continuous b := continuous_iff_continuousAt.2 fun y => (hb y).continuousAt
    have hbc' : Continuous fun z : CxPts (π ≫ p) σ => b (ptMap π rfl σ z) :=
      continuous_iff_continuousAt.2 fun z => ((hb _).pull π rfl).continuousAt
    have h1 := (GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ (e + 1) hproj hdim hprojY π rfl hgen
      (by rw [hdeg]; exact one_ne_zero) (Fin.cons (MLine.ofFun a ha) L) b hbc.measurable).2
    rw [hdeg, Nat.cast_one, one_mul] at h1
    have h2 := GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver F Y (π ≫ p) σ hprojY (e + 1)
      (fun i => ((Fin.cons (MLine.ofFun a ha) L : Fin (e + 1) → MLine p σ) i).pull π rfl)
      (Fin.cons (MLine.ofFun (fun z => a (ptMap π rfl σ z)) fun z => (ha _).pull π rfl) fun i => (L i).pull π rfl)
      (fun i => Fin.cases (hiso.2.2.2.1 a ha) (fun j => hisoY.1 _) i)
    have h3 := GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F Y (π ≫ p) σ (e + 1) _ hA
      (Fin.cons (MLine.ofFun (fun z => a (ptMap π rfl σ z)) fun z => (ha _).pull π rfl) fun i => (L i).pull π rfl)
      _ hbc'.measurable
    rw [← h1, ← h3.2 (h3.1.2 (mIntegrableCont _ _
      (fun i => ((Weight.isCInf_iff_isSmooth hA.anRead).1 (MLine.cInf _)).isPotential hA) _ hbc'))]
    simp only [Mix.int, h2]
  rw [key u v hu hv, key v u hv hu]
  exact mInt_cons_ofFun_symm hA _ _ _ _ _

end GlobalTheory.Mix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralDdcPairingSymmProjectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedIntegral_ddc_pairing_symm_projective : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (u v : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (hv : ∀ y, CInfAt v y), Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) v = Mix.int (Fin.cons (MLine.ofFun v hv) L : Fin (e + 1) → MLine p σ) u := by
  first | exact @GlobalTheory.Mix.int_cons_ofFun_symm | exact GlobalTheory.Mix.int_cons_ofFun_symm | (intros; apply GlobalTheory.Mix.int_cons_ofFun_symm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureNegEqZeroSemiPosi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureNegEqZeroSemiPosi
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

section
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ComplexOrder ComplexConjugate

theorem cHess_posSemidef_of_levi {n : ℕ} {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n} (hf : ContDiffAt ℝ 2 f x)
    (hL : ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => ((f v : ℝ) : ℂ)) x ξ).re) :
    (cHess n (fun v => ((f v : ℝ) : ℂ)) x).PosSemidef := by
  classical
  set g : ReciprocityTheory.L2DbarEstimates.V n → ℂ := fun v => ((f v : ℝ) : ℂ) with hg
  have hg2 : ContDiffAt ℝ 2 g x := Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  have hgc : (fun w => conj (g w)) = g := funext fun w => by simp [g]
  have hH : (cHess n g x).IsHermitian := by
    ext j k
    simp only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]
    show conj (wd n k (wdb n j g) x) = wd n j (wdb n k g) x
    have h1 : (fun w => conj (wdb n j g w)) = wd n j g := by
      funext w
      rw [← ChartWirtingerDerivatives.wd_conj' n j g w, hgc]
    rw [← ChartWirtingerDerivatives.wdb_conj' n k (wdb n j g) x, h1, comm_wd_wdb g x hg2 j k]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun y => ?_
  have hre : dotProduct (star y) (Matrix.mulVec (cHess n g x) y) = leviV n g x (fun k => conj (y k)) := by
    simp only [dotProduct, Matrix.mulVec, leviV, cHess, Matrix.of_apply, Finset.mul_sum,
      Pi.star_apply, Complex.conj_conj]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Complex.star_def]
    ring
  have him := hH.im_star_dotProduct_mulVec_self y
  refine Complex.le_def.2 ⟨?_, ?_⟩
  · rw [hre]; exact hL _
  · simpa using him.symm

theorem re_sum_perm_det_nonneg {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (hA : ∀ i, (A i).PosSemidef) :
    0 ≤ (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => A (τ l) j l).det).re := by
  have h := (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef A hA).2
  have h0 : (D.factorial : ℂ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  have e : (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => A (τ l) j l).det) =
      ((D.factorial : ℝ) : ℂ) * ReciprocityTheory.AnForm.mdisc A := by
    rw [ReciprocityTheory.AnForm.A.mdisc_eq_sum_perm, Complex.ofReal_natCast, ← mul_assoc, mul_one_div_cancel h0, one_mul]
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg (Nat.cast_nonneg _) h

end

theorem dens_nonneg_of_semiPosReg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {L : Fin D → MLine p σ} (h : ∀ i, (L i).φ.SemiPosReg D) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : 0 ≤ dens L c y :=
  mul_nonneg (by positivity) (re_sum_perm_det_nonneg (fun i => c.hess (L i).φ (pick (L i).φ.isLB y) y) fun i =>
    cHess_posSemidef_of_levi ((L i).cInf.contDiffAt c hy (mem_pick _ y)) (h i _ c y ⟨hy, mem_pick _ y⟩))

theorem part_neg_eq_zero_of_semiPosReg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ), (∀ i, (L i).φ.SemiPosReg D) → part L (-1) = 0 := by
  intro k _ X p σ _ D L h
  refine le_antisymm (iSup_le fun c => le_of_eq (Measure.measure_univ_eq_zero.1 ?_)) bot_le
  rw [chartMeas_apply _ _ MeasurableSet.univ, inter_univ, c.e.image_source_eq_target]
  refine setLIntegral_eq_zero c.e.open_target.measurableSet fun v hv => ?_
  have := dens_nonneg_of_semiPosReg h c (c.e.map_target hv)
  exact ENNReal.ofReal_eq_zero.2 (by simpa using this)

end GlobalTheory.Mix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureNegEqZeroSemiPosiStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernFormSignedPartMeasure_neg_eq_zero_semiPositive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ), (∀ i, (L i).φ.SemiPosReg D) → part L (-1) = 0 := by
  first | exact @GlobalTheory.Mix.part_neg_eq_zero_of_semiPosReg | exact GlobalTheory.Mix.part_neg_eq_zero_of_semiPosReg | (intros; apply GlobalTheory.Mix.part_neg_eq_zero_of_semiPosReg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosAddLogNormSqSectionAddPos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosAddLogNormSqSectionAddPos
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix.RegLog

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem cInfAt_comp {f : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) {G : ℝ → ℝ} {T : Set ℝ}
    (hT : IsOpen T) (hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G T) (hf : ∀ z, f z ∈ T) :
    CInfAt (fun z => G (f z)) y := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have e : f y = F (fun a => ev p σ W (g a) y) := h₅.eq_of_nhds
  refine ⟨W, ι, inferInstance, g, G ∘ F, O ∩ F ⁻¹' T, h₁, h₄.continuousOn.isOpen_inter_preimage h₂ hT,
    ⟨h₃, show F _ ∈ T from e ▸ hf y⟩, hG.comp (h₄.mono inter_subset_left) fun v hv => hv.2, ?_⟩
  filter_upwards [h₅] with z hz
  simp only [Function.comp_apply, hz]

theorem cInfAt_normSq_ev {W : X.Opens} (g : Γ(X, W)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) :
    CInfAt (fun z => ‖ev p σ W g z‖ ^ 2) y :=
  ⟨W, Unit, inferInstance, fun _ => g, fun v => ‖v ()‖ ^ 2, univ, hy, isOpen_univ, trivial,
    ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) ())).contDiffOn, EventuallyEq.rfl⟩

theorem cInfAt_nsq {B : LB X} (φ : Weight p σ B) (hφ : φ.IsCInf) (s : B.Sec) (y : CxPts p σ) :
    CInfAt (φ.nsq (secVal p σ s)) y := by
  have hi := mem_pick φ.isLB y
  have h := (cInfAt_normSq_ev (s.f (pick φ.isLB y)) hi).comp₂ (hφ _ y hi)
    (G := fun x => x.1 * Real.exp (-x.2)) (contDiff_fst.mul (Real.contDiff_exp.comp contDiff_snd.neg))
  refine h.congr ?_
  filter_upwards [(isOpen_ptsIn (p := p) (σ := σ) _).mem_nhds hi] with z hz
  exact φ.nsq_eq (secVal_mem s) hz

end GlobalTheory.Mix.RegLog


open GlobalTheory.Mix.RegLog in
theorem GlobalTheory.Mix.semiPosReg_addFn_log_nsq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (N : MLine p σ), N.φ.SemiPosReg D → ∀ (t : N.B.Sec) (δ : ℝ), 0 < δ → (∀ y, CInfAt (fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)) y) ∧ (N.φ.addFn fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)).SemiPosReg D := by
  intro k _ X p σ D N hN t δ hδ
  have hC : ∀ y, CInfAt (fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)) y := fun y =>
    cInfAt_comp ((cInfAt_nsq N.φ N.cInf t y).add (cInfAt_const δ y)) isOpen_compl_singleton
      Real.contDiffOn_log fun z => (add_pos_of_nonneg_of_pos (N.φ.nsq_nonneg _ z) hδ).ne'
  refine ⟨hC, ?_⟩
  intro i c y hy ξ
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (N.B.U i))
  have hm := mem_over c.e hy.1 hy.2
  have hf : ContDiffAt ℂ 2 (ev p σ (N.B.U i) (t.f i) ∘ c.e.symm) (c.e y) :=
    ReciprocityTheory.L2DbarEstimates.Y.contDiffAt_two_of_holo ho (c.holo _ (t.f i)) hm
  have hψ : ContDiffAt ℝ 2 (fun v => N.φ.φ i (c.e.symm v)) (c.e y) := N.cInf.contDiffAt c hy.1 hy.2
  have hψ' : ContDiffAt ℝ 2 (fun v => 1 * N.φ.φ i (c.e.symm v) + Real.log δ) (c.e y) :=
    (contDiffAt_const.mul hψ).add contDiffAt_const
  let w : Fin 2 → ReciprocityTheory.L2DbarEstimates.V D → ℝ := ![fun v => Complex.normSq ((ev p σ (N.B.U i) (t.f i) ∘ c.e.symm) v),
    fun v => Real.exp (1 * N.φ.φ i (c.e.symm v) + Real.log δ)]
  have hu : ∀ j, ContDiffAt ℝ 2 (w j) (c.e y) := by
    intro j; fin_cases j
    · exact ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp hf
    · exact Real.contDiff_exp.contDiffAt.comp _ hψ'
  have hl : ∀ j, ReciprocityTheory.L2DbarEstimates.LogPshAt D (w j) (c.e y) := by
    intro j; fin_cases j
    · exact ReciprocityTheory.L2DbarEstimates.logPshAt_normSq hf
    · refine ReciprocityTheory.L2DbarEstimates.logPshAt_exp hψ' fun ζ => ?_
      rw [ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul hψ 1 (Real.log δ) ζ, Complex.ofReal_one, one_mul]
      exact hN i c y hy ζ
  have hpos : 0 < ∑ j, w j (c.e y) := by
    simp only [Fin.sum_univ_two, w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (Real.exp_pos _)
  have key := ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg hu hl hpos ξ
  have e : (fun v => (((N.φ.addFn fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)).φ i (c.e.symm v) : ℝ) : ℂ))
      =ᶠ[𝓝 (c.e y)] fun v => ((Real.log (∑ j, w j v) : ℝ) : ℂ) := by
    filter_upwards [ho.mem_nhds hm] with v hv
    have hz : c.e.symm v ∈ ptsIn p σ (N.B.U i) := hv.2
    congr 1
    simp only [Weight.addFn, N.φ.nsq_eq (secVal_mem t) hz, Fin.sum_univ_two, w, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Function.comp_apply, secVal_apply]
    set a := N.φ.φ i (c.e.symm v)
    set b := ev p σ (N.B.U i) (t.f i) (c.e.symm v)
    have h1 : ‖b‖ ^ 2 * Real.exp (-a) + δ = Real.exp (-a) * (Complex.normSq b + Real.exp (1 * a + Real.log δ)) := by
      rw [Complex.normSq_eq_norm_sq, Real.exp_add, Real.exp_log hδ, one_mul, Real.exp_neg]
      field_simp
    rw [h1, Real.log_mul (Real.exp_pos _).ne' (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (Real.exp_pos _)).ne', Real.log_exp]
    ring
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e]
  exact key
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosAddLogNormSqSectionAddPosStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiPos_add_log_normSq_section_add_pos : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (N : MLine p σ), N.φ.SemiPosReg D → ∀ (t : N.B.Sec) (δ : ℝ), 0 < δ → (∀ y, CInfAt (fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)) y) ∧ (N.φ.addFn fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)).SemiPosReg D := by
  first | exact @GlobalTheory.Mix.semiPosReg_addFn_log_nsq | exact GlobalTheory.Mix.semiPosReg_addFn_log_nsq | (intros; apply GlobalTheory.Mix.semiPosReg_addFn_log_nsq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityFormulaLeSemipositive
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CycPair

theorem cInfAt_log_nsq_add : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (M : MLine p σ) (s : M.B.Sec) (δ : ℝ), 0 < δ → ∀ y, CInfAt (fun y => Real.log (M.φ.nsq (secVal p σ s) y + δ)) y := by
  intro k _ X p σ M s δ hδ y
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := (GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties k X p σ M s).2.2.1 y
  refine ⟨W, ι, inferInstance, g, fun w => Real.log (F w + δ), O ∩ F ⁻¹' Set.Ioi (-δ), h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_Ioi, ⟨h₃, ?_⟩, ?_, ?_⟩
  · have h0 := M.φ.nsq_nonneg (secVal p σ s) y
    rw [h₅.eq_of_nhds] at h0
    exact lt_of_lt_of_le (neg_neg_of_pos hδ) h0
  · refine ((h₄.mono Set.inter_subset_left).add contDiffOn_const).log fun w hw => ?_
    have : -δ < F w := hw.2
    linarith
  · filter_upwards [h₅] with z hz
    rw [hz]

theorem int_cons_addFn : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (e : ℕ) (L : Fin e → MLine p σ) (A : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (f : CxPts p σ → ℝ), Intg (Fin.cons A L : Fin (e + 1) → MLine p σ) f → Intg (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) f → Intg (Fin.cons (A.addFn u hu) L : Fin (e + 1) → MLine p σ) f ∧ Mix.int (Fin.cons (A.addFn u hu) L : Fin (e + 1) → MLine p σ) f = Mix.int (Fin.cons A L : Fin (e + 1) → MLine p σ) f + Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) f := by
  intro k _ X p σ hp e L A u hu f hA hU
  have hc := GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus k X X p p σ (𝟙 X) (Category.id_comp p)
  have hpart := GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver k X p σ hp (e + 1) (Fin.cons (A.addFn u hu) L)
    (Fin.cons (A.tens (MLine.ofFun u hu)) L) (Fin.cases (hc.2.2.2.2.1 A u hu) fun i => hc.1 (L i))
  have h := GlobalTheory.T.mixedChernIntegral_additive_in_factor k X p σ hp (e + 1) (Fin.cons A L) 0 A (MLine.ofFun u hu) f
  simp only [Fin.update_cons_zero] at h
  have h' := h hA hU
  rw [← h'.2]
  have h1 := h'.1
  simp only [Intg, Mix.int, hpart] at h1 ⊢
  exact ⟨h1, trivial⟩

theorem int_logSec_le : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ), (∀ i, (L i).φ.SemiPosReg D) → ∀ (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → ∀ δ : ℝ, 0 < δ → Intg L (M.logSec s) → Intg L (fun y => Real.log (M.φ.nsq (secVal p σ s) y + δ)) → Mix.int L (M.logSec s) ≤ Mix.int L (fun y => Real.log (M.φ.nsq (secVal p σ s) y + δ)) / 2 := by
  intro F _ X _ p σ hp D L hL M s hs δ hδ h₁ h₂
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hp
  have hneg := GlobalTheory.T.mixedChernFormSignedPartMeasure_neg_eq_zero_semiPositive F X p σ D L hL
  have hnull := GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero F X p σ σ.injective hp D L 1 _ hs
  have hpos := (GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties F X p σ M s).2.1
  simp only [Mix.int, hneg, integral_zero_measure, sub_zero]
  rw [← integral_div]
  refine integral_mono_ae h₁.1 (h₂.1.div_const 2) ?_
  have hae : ∀ᵐ y ∂part L 1, y ∈ ptsIn p σ (nonzeroLocus s) := hnull
  filter_upwards [hae] with y hy
  have h0 := (hpos y).2 hy
  have := Real.log_le_log h0 (le_add_of_nonneg_right hδ.le)
  simp only [MLine.logSec]
  linarith

theorem mem_of_mult_divOfSec_ne_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {A : LB X} (hA : A.IsLB) (s : A.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (U : X.Opens) (h : ∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ U) (z : X) (hz : (divOfSec hA s hs).mult z ≠ 0) : z ∈ U :=
  (h z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)).resolve_left fun h' =>
    notMem_supp_divOfSec.2 h' (CartierDiv.mem_supp_of_mult_ne_zero hz)

theorem side_le : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∀ i, (L i).φ.SemiPosReg (e + 1)) → N.φ.SemiPosReg (e + 1) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) ≤ side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP F _ X _ _ p σ e hproj hdim L M N s hs t ht hcod hL hN
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ : ∀ n, 0 < δ n := fun n => by positivity
  let v : ℕ → CxPts p σ → ℝ := fun n y => Real.log (N.φ.nsq (secVal p σ t) y + δ n)
  let u : ℕ → CxPts p σ → ℝ := fun m y => Real.log (M.φ.nsq (secVal p σ s) y + δ m)
  have hv : ∀ n y, CInfAt (v n) y := fun n => cInfAt_log_nsq_add F X p σ N t (δ n) (hδ n)
  have hu : ∀ m y, CInfAt (u m) y := fun m => cInfAt_log_nsq_add F X p σ M s (δ m) (hδ m)
  have cu : ∀ m, Continuous (u m) := fun m => continuous_iff_continuousAt.2 fun y => (hu m y).continuousAt
  have fin : ∀ (L' : Fin (e + 1) → MLine p σ) (f : CxPts p σ → ℝ), Continuous f → Intg L' f :=
    fun L' => (GlobalTheory.T.mixedChernMeasure_finite_integrable_projective hP F X p σ (e + 1) hproj hdim L').2
  have lint : ∀ L' : Fin (e + 1) → MLine p σ, Intg L' (M.logSec s) :=
    fun L' => GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim L' M s hs
  have supS : ∀ z, (divOfSec M.φ.isLB s hs).mult z ≠ 0 → z ∈ nonzeroLocus t :=
    mem_of_mult_divOfSec_ne_zero M.φ.isLB s hs _ hcod
  have supT : ∀ z, (divOfSec N.φ.isLB t ht).mult z ≠ 0 → z ∈ nonzeroLocus s :=
    mem_of_mult_divOfSec_ne_zero N.φ.isLB t ht _ fun z hz => (hcod z hz).symm
  have key : ∀ m n, Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s)
      + Mix.int (Fin.cons (MLine.ofFun (v n) (hv n)) L : Fin (e + 1) → MLine p σ) (M.logSec s) ≤
      (Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (u m)
        + Mix.int (Fin.cons (MLine.ofFun (u m) (hu m)) L : Fin (e + 1) → MLine p σ) (v n)) / 2 := by
    intro m n
    obtain ⟨-, h1⟩ := int_cons_addFn F X p σ hproj e L N (v n) (hv n) (M.logSec s) (lint _) (lint _)
    obtain ⟨-, h2⟩ := int_cons_addFn F X p σ hproj e L N (v n) (hv n) (u m) (fin _ _ (cu m)) (fin _ _ (cu m))
    have hsp : ∀ i, ((Fin.cons (N.addFn (v n) (hv n)) L : Fin (e + 1) → MLine p σ) i).φ.SemiPosReg (e + 1) :=
      Fin.cases (GlobalTheory.T.semiPos_add_log_normSq_section_add_pos F X p σ (e + 1) N hN t (δ n) (hδ n)).2 hL
    have h3 := int_logSec_le F X p σ hproj (e + 1) _ hsp M s hs (δ m) (hδ m) (lint _) (fin _ _ (cu m))
    have h4 := GlobalTheory.T.mixedIntegral_ddc_pairing_symm_projective hP F X p σ e hproj hdim L (v n) (u m) (hv n) (hu m)
    rw [← h1]
    refine h3.trans (le_of_eq ?_)
    change Mix.int _ (u m) / 2 = _
    rw [h2, h4]
  have ps : ∀ n, 2 * Mix.int (Fin.cons (MLine.ofFun (v n) (hv n)) L : Fin (e + 1) → MLine p σ) (M.logSec s) =
      ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (v n) z
        - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (v n) :=
    fun n => GlobalTheory.T.poincareLelong_formula_section_projective hP F X p σ e hproj hdim L M s hs (v n) (hv n)
  have pt : ∀ m, 2 * Mix.int (Fin.cons (MLine.ofFun (u m) (hu m)) L : Fin (e + 1) → MLine p σ) (N.logSec t) =
      ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (u m) z
        - Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (u m) :=
    fun m => GlobalTheory.T.poincareLelong_formula_section_projective hP F X p σ e hproj hdim L N t ht (u m) (hu m)
  have limT := GlobalTheory.T.tendsto_regularisedLogNorm_mixedMeasure_divisors hP F X p σ e hproj hdim N t
  have limS := GlobalTheory.T.tendsto_regularisedLogNorm_mixedMeasure_divisors hP F X p σ e hproj hdim M s
  have l1 : Tendsto (fun n => ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (v n) z) atTop
      (𝓝 (2 * ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (N.logSec t) z)) :=
    limT.2 L _ supS
  have l2 : Tendsto (fun n => Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (v n)) atTop
      (𝓝 (2 * Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t))) := limT.1 ht _
  have l3 : ∀ m, Tendsto (fun n => Mix.int (Fin.cons (MLine.ofFun (u m) (hu m)) L : Fin (e + 1) → MLine p σ) (v n))
      atTop (𝓝 (2 * Mix.int (Fin.cons (MLine.ofFun (u m) (hu m)) L : Fin (e + 1) → MLine p σ) (N.logSec t))) :=
    fun m => limT.1 ht _
  have l4 : Tendsto (fun m => ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (u m) z) atTop
      (𝓝 (2 * ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (M.logSec s) z)) :=
    limS.2 L _ supT
  have step : ∀ m, side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs)
      - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t) ≤
      (∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (u m) z) / 2 := by
    intro m
    have lim1 : Tendsto (fun n => Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s)
        + Mix.int (Fin.cons (MLine.ofFun (v n) (hv n)) L : Fin (e + 1) → MLine p σ) (M.logSec s)) atTop
        (𝓝 (side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs)
          - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t))) := by
      have e1 : (fun n => Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s)
          + Mix.int (Fin.cons (MLine.ofFun (v n) (hv n)) L : Fin (e + 1) → MLine p σ) (M.logSec s)) =
          fun n => Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s)
            + (∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (v n) z
              - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (v n)) / 2 :=
        funext fun n => by rw [← ps n]; ring
      rw [e1]
      convert tendsto_const_nhds.add ((l1.sub l2).div_const 2) using 2
      simp only [side]
      ring
    have lim2 := (tendsto_const_nhds (x := Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (u m))).add (l3 m)
    have h := le_of_tendsto_of_tendsto' lim1 (lim2.div_const 2) (key m)
    have := pt m
    linarith
  have h := ge_of_tendsto' (l4.div_const 2) step
  simp only [side] at h ⊢
  linarith

end GlobalTheory.CycPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityFormulaLeSemipositiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reciprocityFormula_le_semipositive : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∀ i, (L i).φ.SemiPosReg (e + 1)) → N.φ.SemiPosReg (e + 1) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) ≤ side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  first | exact @GlobalTheory.CycPair.side_le | exact GlobalTheory.CycPair.side_le | (intros; apply GlobalTheory.CycPair.side_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityDefectIndependentFirstMetric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityDefectIndependentFirstMetric
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MetricIndep

theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem int_sub_half {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) {f v : CxPts p σ → ℝ} (hf : Intg L f) (hv : Intg L v) :
    Mix.int L (fun y => f y - v y / 2) = Mix.int L f - Mix.int L v / 2 := by
  unfold Mix.int
  rw [integral_sub hf.1 (hv.1.div_const 2), integral_sub hf.2 (hv.2.div_const 2),
    integral_div, integral_div]
  ring

theorem upd_cons {α : Type*} {n : ℕ} (a b : α) (L : Fin n → α) :
    Function.update (Fin.cons a L : Fin (n + 1) → α) 0 b = Fin.cons b L :=
  Fin.update_cons_zero (α := fun _ => α) a L b

theorem side_sub_side_addFn : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), side N L ((M.addFn u hu).logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side (M.addFn u hu) L (N.logSec t) ((M.addFn u hu).logSec s) (divOfSec N.φ.isLB t ht) = side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP F _ X _ _ p σ e hproj hdim L M N s hs t ht hcod u hu
  have hσ : Function.Injective σ := σ.injective
  have hcont : Continuous u := continuous_iff_continuousAt.2 fun y => (hu y).continuousAt
  have hcomp : CompactSpace X := compactSpace_of_projOver hproj
  obtain ⟨-, -, -, hlog⟩ := GlobalTheory.Mix.SecNorm.logSec_basic F X p σ M s

  have hA : Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) ((M.addFn u hu).logSec s) =
      Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s) -
        Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) u / 2 := by
    have hae : ∀ ε : ℤˣ, (M.addFn u hu).logSec s =ᵐ[part (Fin.cons N L : Fin (e + 1) → MLine p σ) ε]
        fun y => M.logSec s y - u y / 2 := by
      intro ε
      refine ae_iff.2 (measure_mono_null (fun y hy => ?_)
        (GlobalTheory.MixNull.part_compl_null F X p σ hσ hproj (e + 1) (Fin.cons N L) ε (nonzeroLocus s) hs))
      exact fun hy' => hy (hlog u hu y hy')
    have hf := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons N L) M s hs
    have hv := (GlobalTheory.T.mixedChernMeasure_finite_integrable_projective hP F X p σ (e + 1) hproj hdim (Fin.cons N L)).2 u hcont
    rw [← int_sub_half _ hf hv]
    unfold Mix.int
    rw [integral_congr_ae (hae 1), integral_congr_ae (hae (-1))]

  have hB : Mix.int (Fin.cons (M.addFn u hu) L : Fin (e + 1) → MLine p σ) (N.logSec t) =
      Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t) +
        Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (N.logSec t) := by
    obtain ⟨hrefl, -, -, -, haddFn, -⟩ := GlobalTheory.Mix.isom_calculus F X X p p σ (𝟙 X) (Category.id_comp p)
    have hpart : ∀ ε : ℤˣ, part (Fin.cons (M.addFn u hu) L : Fin (e + 1) → MLine p σ) ε =
        part (Fin.cons (M.tens (MLine.ofFun u hu)) L : Fin (e + 1) → MLine p σ) ε :=
      GlobalTheory.Mix.part_eq_of_isom F X p σ hproj (e + 1) _ _ fun i => Fin.cases (haddFn M u hu) (fun j => hrefl (L j)) i
    have h1 := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons M L) N t ht
    have h2 := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons (MLine.ofFun u hu) L) N t ht
    have hadd := GlobalTheory.T.mixedChernIntegral_additive_in_factor F X p σ hproj (e + 1) (Fin.cons M L : Fin (e + 1) → MLine p σ) 0 M
      (MLine.ofFun u hu) (N.logSec t)
    rw [upd_cons, upd_cons, upd_cons] at hadd
    replace hadd := hadd h1 h2
    rw [← hadd.2]
    unfold Mix.int
    rw [hpart, hpart]

  have hC : ∀ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L ((M.addFn u hu).logSec s) z =
      ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (M.logSec s) z -
        ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L u z / 2 := by
    intro z
    by_cases h : (divOfSec N.φ.isLB t ht).mult z = 0
    · simp [h]
    have hz1 := CartierDiv.coheight_eq_one_of_mult_ne_zero h
    have hzs : z ∈ nonzeroLocus s := (hcod z hz1).resolve_right fun hzt =>
      (notMem_supp_divOfSec.2 hzt) (CartierDiv.mem_supp_of_mult_ne_zero h)
    have hdz := (GlobalTheory.FieldDimCoheight.coheight_eq_one_iff F X p e hproj hdim z).1 hz1
    obtain ⟨-, hcc, hnull, hlc⟩ := GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure hP F X p σ hproj e L z hdz
    have hae : ∀ ε : ℤˣ, (fun y => (M.addFn u hu).logSec s (ptMap (closι z) rfl σ y)) =ᵐ[part (fun i => (L i).pull (closι z) rfl) ε]
        fun y => M.logSec s (ptMap (closι z) rfl σ y) - u (ptMap (closι z) rfl σ y) / 2 := by
      intro ε
      refine ae_iff.2 (measure_mono_null (fun y hy => ?_) (hnull (nonzeroLocus s) hzs ε))
      exact fun hy' => hy (hlog u hu _ hy')
    have hcyc : cycInt L ((M.addFn u hu).logSec s) z = cycInt L (M.logSec s) z - cycInt L u z / 2 := by
      have e2 := int_sub_half (fun i => (L i).pull (closι z) rfl) (hlc M s hzs) (hcc u hcont)
      unfold cycInt
      rw [← e2]
      unfold Mix.int
      rw [integral_congr_ae (hae 1), integral_congr_ae (hae (-1))]
    rw [hcyc]
    ring
  have hfs := CartierDiv.finite_support_mult (divOfSec N.φ.isLB t ht)
  have hsub : ∀ g : X → ℝ, (Function.support fun z => ((divOfSec N.φ.isLB t ht).mult z : ℝ) * g z).Finite :=
    fun g => hfs.subset fun z hz h0 => hz (by simp [h0])
  have hsum : ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L ((M.addFn u hu).logSec s) z =
      ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (M.logSec s) z -
        (∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L u z) / 2 := by
    simp only [hC]
    rw [div_eq_mul_inv, finsum_mul]
    exact finsum_sub_distrib (hsub _) ((hsub (fun z => cycInt L u z)).subset fun z hz h0 => hz (by
      have h1 : ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L u z = 0 := h0
      simp only [h1, zero_div]))
  have hPL := GlobalTheory.T.poincareLelong_formula_section_projective hP F X p σ e hproj hdim L N t ht u hu
  simp only [side]
  rw [hA, hB, hsum]
  linarith

end GlobalTheory.MetricIndep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityDefectIndependentFirstMetricStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reciprocityDefect_independent_firstMetric : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), side N L ((M.addFn u hu).logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side (M.addFn u hu) L (N.logSec t) ((M.addFn u hu).logSec s) (divOfSec N.φ.isLB t ht) = side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  first | exact @GlobalTheory.MetricIndep.side_sub_side_addFn | exact GlobalTheory.MetricIndep.side_sub_side_addFn | (intros; apply GlobalTheory.MetricIndep.side_sub_side_addFn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedBundlesReciprocitySemiPositive
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem semiPosReg_of_eqOn {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {B : LB X}
    {φ ψ : Weight p σ B} {D : ℕ} (h : φ.SemiPosReg D)
    (e : ∀ i, ∀ y ∈ ptsIn p σ (B.U i), ψ.φ i y = φ.φ i y) : ψ.SemiPosReg D := by
  intro i c y hy ξ
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hm := ChartGlue.mem_over c.e hy.1 hy.2
  have ee : (fun v => (ψ.φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] (fun v => (φ.φ i (c.e.symm v) : ℂ)) :=
    Filter.eventually_of_mem (ho.mem_nhds hm) fun v hv => by simp only [e i _ hv.2]
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr ee]
  exact h i c y hy ξ

theorem exists_addFn_semiPosReg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (M : MLine p σ) (D : ℕ) (hg : ∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) :
    ∃ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), (M.addFn u hu).φ.SemiPosReg D := by
  obtain ⟨ψ, hψ, hψp⟩ := GlobalTheory.T.exists_smooth_semipositive_weight_of_generated k X p σ M.B M.φ.isLB hg
  obtain ⟨u, hu, he⟩ := GlobalTheory.T.smooth_weights_differ_by_smooth_function k X p σ M.B M.φ ψ M.cInf hψ
  exact ⟨u, hu, semiPosReg_of_eqOn (hψp D) fun i y hy => (he i y hy).symm⟩

end GlobalTheory.Mix

theorem GlobalTheory.Mix.side_eq_of_generated : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∀ i, (L i).φ.SemiPosReg (e + 1)) → (∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → (∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP F _ X _ _ p σ e hproj hdim L M N s hs t ht hz hL hgM hgN
  obtain ⟨u, hu, hMu⟩ := GlobalTheory.Mix.exists_addFn_semiPosReg M (e + 1) hgM
  obtain ⟨v, hv, hNv⟩ := GlobalTheory.Mix.exists_addFn_semiPosReg N (e + 1) hgN
  have hz' : ∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus t ∨ z ∈ nonzeroLocus s := fun z h => (hz z h).symm
  have h1 := GlobalTheory.T.reciprocityDefect_independent_firstMetric hP F X p σ e hproj hdim L M N s hs t ht hz u hu
  have h2 := GlobalTheory.T.reciprocityDefect_independent_firstMetric hP F X p σ e hproj hdim L N (M.addFn u hu) t ht s hs hz' v hv
  have h3 := GlobalTheory.T.reciprocityFormula_le_semipositive hP F X p σ e hproj hdim L (M.addFn u hu) (N.addFn v hv) s hs t ht hz hL hNv
  have h4 := GlobalTheory.T.reciprocityFormula_le_semipositive hP F X p σ e hproj hdim L (N.addFn v hv) (M.addFn u hu) t ht s hs hz' hL hMu
  have d1 : divOfSec (M.addFn u hu).φ.isLB s hs = divOfSec M.φ.isLB s hs := rfl
  have d2 : divOfSec (N.addFn v hv).φ.isLB t ht = divOfSec N.φ.isLB t ht := rfl
  rw [d1, d2] at h3 h4
  rw [d1] at h2
  linarith
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedBundlesReciprocitySemiPositiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generatedBundles_reciprocity_semiPositive : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∀ i, (L i).φ.SemiPosReg (e + 1)) → (∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → (∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  first | exact @GlobalTheory.Mix.side_eq_of_generated | exact GlobalTheory.Mix.side_eq_of_generated | (intros; apply GlobalTheory.Mix.side_eq_of_generated <;> assumption)
end
