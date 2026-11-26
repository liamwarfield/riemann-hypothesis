module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesPresentationUpToOrderTensorProduct
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralLinearOfDensityEqSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureChartApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingThetaConstantsGenerateIntegralTorsionLab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameAbelianPartTorsionFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSurjectiveOfOmegaMapSurjectiveConnected
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSurjectiveOfOmegaMapSurjectiveConnected
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.PDivGroup

theorem surjective_of_cotangentPullback_surjective_nilAug {k A B : Type} [Field k] [CommRing A] [CommRing B]
    [Bialgebra k A] [Bialgebra k B] [Module.Finite k A] (f : B →ₐc[k] A)
    (hA : ∀ a ∈ augIdeal k A, IsNilpotent a) (hf : Function.Surjective (cotMap f)) :
    Function.Surjective f := by
  set I := augIdeal k A with hIdef
  set J := augIdeal k B with hJdef
  have hfJ : ∀ b ∈ J, f b ∈ I := by
    intro b hb
    have hb' : counit (R := k) b = 0 := hb
    show counit (R := k) (f b) = 0
    rw [CoalgHomClass.counit_comp_apply]; exact hb'

  have step1 : ∀ x ∈ I, ∃ b ∈ J, x - f b ∈ I ^ 2 := by
    intro x hx
    obtain ⟨c, hc⟩ := hf (AugCot.d (counitAlgHom k A) x)
    obtain ⟨b0, rfl⟩ := AugCot.d_surjective _ c
    rw [cotMap_d] at hc
    set b := b0 - algebraMap k B (counit b0) with hb
    have hbJ : b ∈ J := by
      show counit (R := k) b = 0
      simp [hb]
    have hdb : AugCot.d (counitAlgHom k A) (f b) = AugCot.d (counitAlgHom k A) (f b0) := by
      rw [hb, map_sub, AlgHomClass.commutes, map_sub, AugCot.d_algebraMap, sub_zero]
    refine ⟨b, hbJ, ?_⟩
    have h1 : AugCot.d (counitAlgHom k A) (x - f b) = 0 := by
      rw [map_sub, hdb, ← hc, sub_self]
    have hmem : x - f b ∈ I := I.sub_mem hx (hfJ b hbJ)
    rw [AugCot.d_of_mem _ hmem, Ideal.toCotangent_eq_zero] at h1
    exact h1

  have step2 : ∀ m : ℕ, ∀ y ∈ I ^ (m + 1), ∃ b ∈ J ^ (m + 1), y - f b ∈ I ^ (m + 2) := by
    intro m
    induction m with
    | zero =>
      intro y hy
      rw [zero_add, pow_one] at hy
      obtain ⟨b, hb, h⟩ := step1 y hy
      exact ⟨b, by rwa [zero_add, pow_one], h⟩
    | succ m ih =>
      intro y hy
      rw [pow_succ'] at hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro x hx z hz
        obtain ⟨b1, hb1, hu⟩ := step1 x hx
        obtain ⟨b2, hb2, hv⟩ := ih z hz
        have hfb1 : f b1 ∈ I := hfJ b1 hb1
        have hfb2 : f b2 ∈ I ^ (m + 1) := by
          have : f b2 = z - (z - f b2) := by ring
          rw [this]
          exact (I ^ (m + 1)).sub_mem hz (Ideal.pow_le_pow_right (by omega) hv)
        refine ⟨b1 * b2, ?_, ?_⟩
        · rw [pow_succ']; exact Ideal.mul_mem_mul hb1 hb2
        · set u := x - f b1
          set v := z - f b2
          have hx' : x = f b1 + u := by simp [u]
          have hz' : z = f b2 + v := by simp [v]
          have : x * z - f (b1 * b2) = f b1 * v + u * f b2 + u * v := by
            rw [hx', hz', map_mul]; ring
          rw [this]
          refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
          · rw [show m + 1 + 2 = 1 + (m + 2) by omega, pow_add, pow_one]
            exact Ideal.mul_mem_mul hfb1 hv
          · rw [show m + 1 + 2 = 2 + (m + 1) by omega, pow_add]
            exact Ideal.mul_mem_mul hu hfb2
          · rw [show m + 1 + 2 = 1 + (m + 2) by omega, pow_add, pow_one]
            exact Ideal.mul_mem_mul (Ideal.pow_le_self (by norm_num) hu) hv
      · rintro y1 y2 ⟨b1, hb1, h1⟩ ⟨b2, hb2, h2⟩
        refine ⟨b1 + b2, Ideal.add_mem _ hb1 hb2, ?_⟩
        have : y1 + y2 - f (b1 + b2) = (y1 - f b1) + (y2 - f b2) := by rw [map_add (f := _)]; ring
        rw [this]; exact Ideal.add_mem _ h1 h2
  have step3 : ∀ m : ℕ, ∀ x ∈ I, ∃ b : B, x - f b ∈ I ^ (m + 1) := by
    intro m
    induction m with
    | zero => intro x hx; exact ⟨0, by rw [map_zero, sub_zero, zero_add, pow_one]; exact hx⟩
    | succ m ih =>
      intro x hx
      obtain ⟨b, hb⟩ := ih x hx
      obtain ⟨b', -, hb'⟩ := step2 m _ hb
      refine ⟨b + b', ?_⟩
      have : x - f (b + b') = x - f b - f b' := by rw [map_add (f := _)]; ring
      rw [this]; exact hb'

  haveI : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  have hnil : IsNilpotent I := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian I)).2 ?_
    intro a ha
    exact (mem_nilradical).2 (hA a ha)
  obtain ⟨N, hN⟩ := hnil
  have hI : ∀ x ∈ I, ∃ b : B, f b = x := by
    intro x hx
    obtain ⟨b, hb⟩ := step3 N x hx
    have : x - f b ∈ I ^ N := Ideal.pow_le_pow_right (by omega) hb
    rw [hN] at this
    exact ⟨b, (sub_eq_zero.1 ((Submodule.mem_bot _).1 this)).symm⟩
  intro a
  have ha : a - algebraMap k A (counit a) ∈ I := by
    show counit (R := k) (a - algebraMap k A (counit a)) = 0
    simp
  obtain ⟨b, hb⟩ := hI _ ha
  refine ⟨b + algebraMap k B (counit a), ?_⟩
  rw [map_add (f := _), AlgHomClass.commutes, hb, sub_add_cancel]

theorem app_surjective_of_omegaMap_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), G.IsConn → Function.Surjective (omegaMap G H q) → ∀ n, Function.Surjective (q.app n) := by
  intro p _ k _ _ G H q hG hq n
  refine surjective_of_cotangentPullback_surjective_nilAug (q.app n) (hG n) fun w => ?_
  obtain ⟨v, rfl⟩ := G.omegaLevel_surjective n w
  obtain ⟨u, rfl⟩ := hq v
  exact ⟨u.1 n, rfl⟩

end GlobalTheory.PDivGroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSurjectiveOfOmegaMapSurjectiveConnectedStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.app_surjective_of_omegaMap_surjective_connected : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), G.IsConn → Function.Surjective (omegaMap G H q) → ∀ n, Function.Surjective (q.app n) := by
  first | exact @GlobalTheory.PDivGroup.app_surjective_of_omegaMap_surjective | exact GlobalTheory.PDivGroup.app_surjective_of_omegaMap_surjective | (intros; apply GlobalTheory.PDivGroup.app_surjective_of_omegaMap_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIntegralPullMulDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIntegralPullMulDegree
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
open MeasureTheory GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchPull

open Set

theorem setIntegral_pull {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {p : X ⟶ Sp k} {e : ℕ} (hX : IsArithVar p e) (g : Y ⟶ X) (hY : IsArithVar (g ≫ p) e)
    (hη : g (genericPoint Y) = genericPoint X) (hδ : g.residueDegree (genericPoint Y) ≠ 0)
    (N : HermLB p) (σ : k →+* ℂ) (U : X.Opens) (hU : genericPoint X ∈ U)
    (f : CxPts p σ → ℝ) (hf : ContinuousOn f (ptsIn p σ U))
    (S' : Set (CxPts (g ≫ p) σ)) (hsub : ptsIn (g ≫ p) σ (g ⁻¹ᵁ U) ⊆ S')
    (f' : CxPts (g ≫ p) σ → ℝ)
    (hf' : EqOn f' (fun y => f (PtsOver.map g rfl _ y)) (ptsIn (g ≫ p) σ (g ⁻¹ᵁ U)))
    (ε : ℤˣ) :
    ∫ y in S', f' y ∂((N.restr g).φ σ).chernPart e ε =
      (g.residueDegree (genericPoint Y) : ℝ) * ∫ x in ptsIn p σ U, f x ∂(N.φ σ).chernPart e ε := by
  obtain ⟨V, hVη, hV⟩ := GlobalTheory.CoverDeg.exists_open_covering_charts hX hY g rfl hη hδ
  obtain ⟨hcard, hchart, hlift⟩ := hV σ
  set F := PtsOver.map g (rfl : g ≫ p = g ≫ p) (spMap σ) with hFdef
  have hFm : Measurable F := (PtsOver.continuous_map _ _ _).measurable
  have hpre : ∀ W : X.Opens, F ⁻¹' ptsIn p σ W = ptsIn (g ≫ p) σ (g ⁻¹ᵁ W) := by
    intro W
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have hUm : MeasurableSet (ptsIn p σ U) := (isOpen_ptsIn U).measurableSet
  have hVm : MeasurableSet (ptsIn p σ V) := (isOpen_ptsIn V).measurableSet
  have h0 : (N.φ σ).chernPart e ε (ptsIn p σ V)ᶜ = 0 := by
    have h := GlobalTheory.ChernNull.chernPart_over_closed hX ((V : X.Opens) : Set X)ᶜ
      V.isOpen.isClosed_compl (by simp [hVη]) σ (N.φ σ) ε
    convert h using 2
    ext y
    simp [mem_ptsIn]
  have hmeas : (g.residueDegree (genericPoint Y) : ℝ≥0∞) •
      ((N.φ σ).chernPart e ε).restrict (ptsIn p σ U) =
      Measure.map F ((((N.φ σ).pull g rfl).chernPart e ε).restrict
        (F ⁻¹' (ptsIn p σ U ∩ ptsIn p σ V))) := by
    ext A hA
    rw [Measure.smul_apply, Measure.restrict_apply hA, Measure.map_apply hFm hA,
      Measure.restrict_apply (hFm hA), ← Set.preimage_inter,
      GlobalTheory.CoverChern.chernPart_preimage_of_cover hX hY g rfl (N.φ σ) (N.cInf σ) ε (ptsIn p σ V)
        (isOpen_ptsIn V) _ hcard hchart hlift
        (fun c c' hc w hw => GlobalTheory.PullChartDens.chernDens_pull_of_chart g rfl (N.φ σ) (N.cInf σ)
          c c' hc w hw) _
        (hA.inter (hUm.inter hVm)) (fun x hx => hx.2.2), smul_eq_mul, ← Set.inter_assoc,
      measure_inter_conull h0]
  set T' := F ⁻¹' (ptsIn p σ U ∩ ptsIn p σ V) with hT'
  have hT'eq : T' = ptsIn (g ≫ p) σ (g ⁻¹ᵁ U) ∩ ptsIn (g ≫ p) σ (g ⁻¹ᵁ V) := by
    rw [hT', Set.preimage_inter, hpre, hpre]
  have hT'm : MeasurableSet T' := hFm (hUm.inter hVm)
  have hT'U : T' ⊆ ptsIn (g ≫ p) σ (g ⁻¹ᵁ U) := by
    rw [hT'eq]; exact Set.inter_subset_left
  have h0' : ((N.φ σ).pull g rfl).chernPart e ε T'ᶜ = 0 := by
    have h := GlobalTheory.ChernNull.chernPart_over_closed hY (g ⁻¹' ((U ⊓ V : X.Opens) : Set X)ᶜ)
      ((U ⊓ V).isOpen.isClosed_compl.preimage g.continuous) (by simp [hη, hU, hVη]) σ
      ((N.φ σ).pull g rfl) ε
    convert h using 2
    rw [hT'eq]
    ext y
    simp [mem_ptsIn]

  have hae : S' =ᵐ[((N.φ σ).pull g rfl).chernPart e ε] T' := by
    refine ae_eq_set.2 ⟨measure_mono_null (fun x hx => hx.2) h0', ?_⟩
    rw [Set.diff_eq_empty.2 (hT'U.trans hsub)]
    exact measure_empty
  have hfm : AEStronglyMeasurable f (Measure.map F ((((N.φ σ).pull g rfl).chernPart e ε).restrict T')) := by
    rw [← hmeas]
    exact (hf.aestronglyMeasurable hUm).smul_measure _
  calc ∫ y in S', f' y ∂((N.restr g).φ σ).chernPart e ε
      = ∫ y in T', f' y ∂((N.φ σ).pull g rfl).chernPart e ε := setIntegral_congr_set hae
    _ = ∫ y in T', f (F y) ∂((N.φ σ).pull g rfl).chernPart e ε :=
        setIntegral_congr_fun hT'm (hf'.mono hT'U)
    _ = ∫ x, f x ∂Measure.map F ((((N.φ σ).pull g rfl).chernPart e ε).restrict T') :=
        (integral_map hFm.aemeasurable hfm).symm
    _ = _ := by
        rw [← hmeas, integral_smul_measure, ENNReal.toReal_natCast, smul_eq_mul]

theorem archInt_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (e : ℕ), IsArithVar p e → IsArithVar q e → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), g.residueDegree (genericPoint Y) ≠ 0 → ∀ (M N : HermLB p) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (N.pull g hg).archInt (M.pull g hg) e (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) = (g.residueDegree (genericPoint Y) : ℝ) * N.archInt M e hr := by
  intro k _ X Y _ _ p q e hX hY g hg hη hδ M N r hr
  subst hg
  have hη' : g (genericPoint Y) ⤳ genericPoint X := hη ▸ specializes_rfl
  have hU : genericPoint X ∈ (M.div hr).supp.compl := (M.div hr).genericPoint_notMem_supp
  have key : ∀ σ : k →+* ℂ,
      ((N.restr g).φ σ).chernInt e
        (offSupp (g ≫ p) σ ((M.restr g).div (MultPull.isRatSec_pull_map g hη' hr)))
        (logNorm ((M.restr g).φ σ) (fun c => Units.map (TrueGeo.SmallSec.fnMap g hη').toMonoidHom
          (r (c PUnit.unit)))) =
      (g.residueDegree (genericPoint Y) : ℝ) *
        (N.φ σ).chernInt e (offSupp p σ (M.div hr)) (logNorm (M.φ σ) r) := by
    intro σ
    have hsub := fun (y : CxPts (g ≫ p) σ) (hy : y ∈ ptsIn (g ≫ p) σ (g ⁻¹ᵁ (M.div hr).supp.compl)) =>
      ArchIntAlter.mem_offSupp_pull M g hη' hr hy
    have hf' := fun (y : CxPts (g ≫ p) σ) (hy : y ∈ ptsIn (g ≫ p) σ (g ⁻¹ᵁ (M.div hr).supp.compl)) =>
      ArchIntAlter.logNorm_pull M g hη' hr hy
    have hc := ArchIntAlter.continuousOn_logNorm (M.φ σ) hr (M.cInf σ)
    unfold Weight.chernInt
    rw [setIntegral_pull hX g hY hη hδ N σ _ hU _ hc _ hsub _ hf' 1,
      setIntegral_pull hX g hY hη hδ N σ _ hU _ hc _ hsub _ hf' (-1), mul_sub]
    rfl
  unfold HermLB.archInt
  refine (finsum_congr key).trans ?_
  exact (mul_finsum _ _).symm

end GlobalTheory.ArchPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIntegralPullMulDegreeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanIntegral_pull_mul_degree : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (e : ℕ), IsArithVar p e → IsArithVar q e → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), g.residueDegree (genericPoint Y) ≠ 0 → ∀ (M N : HermLB p) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (N.pull g hg).archInt (M.pull g hg) e (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) = (g.residueDegree (genericPoint Y) : ℝ) * N.archInt M e hr := by
  first | exact @GlobalTheory.ArchPull.archInt_pull | exact GlobalTheory.ArchPull.archInt_pull | (intros; apply GlobalTheory.ArchPull.archInt_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearRelationMixedDensitiesIntegrals
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearRelationMixedDensitiesIntegrals
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open scoped ENNReal
set_option autoImplicit false
noncomputable section

theorem GlobalTheory.Mix.part_eq_zero_off_charts {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (ε : ℤˣ) {S : Set (CxPts p σ)} (hS : MeasurableSet S)
    (h : ∀ c : AlgChart p σ D, Disjoint c.e.source S) : part L ε S = 0 := by
  have key : part L ε ≤ (part L ε).restrict Sᶜ := iSup_le fun c => by
    have e : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * dens L c y)) S = 0 := by
      rw [chartMeas_apply _ _ hS, (h c).inter_eq, image_empty, Measure.restrict_empty,
        lintegral_zero_measure]
    rw [← Measure.restrict_eq_self_of_ae_mem (s := Sᶜ) (compl_mem_ae_iff.2 e)]
    exact Measure.restrict_mono le_rfl (le_iSup (fun c : AlgChart p σ D =>
      chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L c y)) c)
  refine le_antisymm ((key S).trans_eq ?_) zero_le
  rw [Measure.restrict_apply hS, inter_compl_self, measure_empty]

theorem GlobalTheory.Mix.sum_int_eq_zero_of_dens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (J : Type) [Fintype J] (a : J → ℝ) (L : J → Fin D → MLine p σ), (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ∑ i, a i * dens (L i) c y = 0) → ∀ f : CxPts p σ → ℝ, (∀ i, Intg (L i) f) → ∑ i, a i * Mix.int (L i) f = 0 := by
  intro k _ X p σ _ D J _ a N hlin g hint
  classical
  set P : J → ℤˣ → Measure (CxPts p σ) := fun j ε => part (N j) ε with hPdef
  let ap : J → ℝ := fun j => max (a j) 0
  let an : J → ℝ := fun j => max (-a j) 0
  let μ : (J → ℝ) → (J → ℝ) → Measure (CxPts p σ) := fun u w =>
    ∑ j, (ENNReal.ofReal (u j) • P j 1 + ENNReal.ofReal (w j) • P j (-1))

  have hcont : ∀ j (c : AlgChart p σ D), ContinuousOn (fun v => dens (N j) c (c.e.symm v)) c.e.target :=
    fun j c => (GlobalTheory.T.continuousOn_mixedChernFormDensityInChart k X p σ D (N j) c).comp c.e.continuousOn_symm c.e.mapsTo_symm

  have hchart : ∀ (u w : J → ℝ) (c : AlgChart p σ D) (A : Set (CxPts p σ)), MeasurableSet A → A ⊆ c.e.source →
      μ u w A = ∫⁻ v in c.e '' A, ∑ j, (ENNReal.ofReal (u j) * ENNReal.ofReal (1 * dens (N j) c (c.e.symm v)) +
        ENNReal.ofReal (w j) * ENNReal.ofReal (-1 * dens (N j) c (c.e.symm v))) := by
    intro u w c A hA hAc
    have hsub : c.e '' A ⊆ c.e.target := fun _ ⟨y, hy, e⟩ => e ▸ c.e.map_source (hAc hy)
    have hm : ∀ j (s : ℝ), AEMeasurable (fun v => ENNReal.ofReal (s * dens (N j) c (c.e.symm v)))
        (volume.restrict (c.e '' A)) := fun j s =>
      ((((hcont j c).aemeasurable c.e.open_target.measurableSet).const_mul s).ennreal_ofReal).mono_measure
        (Measure.restrict_mono hsub le_rfl)
    have hP : ∀ j (ε : ℤˣ), P j ε A = ∫⁻ v in c.e '' A, ENNReal.ofReal ((ε : ℤ) * dens (N j) c (c.e.symm v)) :=
      fun j ε => GlobalTheory.T.mixedChernFormSignedPartMeasure_chart_apply k X p σ D (N j) ε c A hA hAc
    have hm2 : ∀ j ∈ (Finset.univ : Finset J), AEMeasurable (fun v =>
        ENNReal.ofReal (u j) * ENNReal.ofReal (1 * dens (N j) c (c.e.symm v)) +
        ENNReal.ofReal (w j) * ENNReal.ofReal (-1 * dens (N j) c (c.e.symm v))) (volume.restrict (c.e '' A)) :=
      fun j _ => ((hm j 1).const_mul _).add ((hm j (-1)).const_mul _)
    rw [lintegral_finsetSum' _ hm2]
    simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [lintegral_add_left' ((hm j 1).const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hP, hP]
    simp

  set U : Set (CxPts p σ) := ⋃ c : AlgChart p σ D, c.e.source with hUdef
  have hUo : IsOpen U := isOpen_iUnion fun c => c.e.open_source
  have hzero : ∀ u w : J → ℝ, μ u w Uᶜ = 0 := by
    intro u w
    have h0 : ∀ j (ε : ℤˣ), P j ε Uᶜ = 0 := fun j ε =>
      GlobalTheory.Mix.part_eq_zero_off_charts (N j) ε hUo.measurableSet.compl fun c =>
        Set.disjoint_compl_right_iff_subset.2 (Set.subset_iUnion (fun c : AlgChart p σ D => c.e.source) c)
    simp [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.add_apply, Measure.smul_apply, h0]

  have hbal : μ ap an = μ an ap := by
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable (fun c : AlgChart p σ D => c.e.source)
      fun c => c.e.open_source
    let s : Option (AlgChart p σ D) → Set (CxPts p σ) := fun o => o.elim Uᶜ fun c => c.e.source
    refine Measure.ext_of_biUnion_eq_univ (S := insert none (some '' T)) (s := s) ((hTc.image _).insert _) ?_ ?_
    · refine Set.eq_univ_of_forall fun y => ?_
      by_cases hy : y ∈ U
      · rw [hUdef, ← hT] at hy
        obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.1 hy
        exact Set.mem_iUnion₂.2 ⟨some c, Set.mem_insert_of_mem _ ⟨c, hc, rfl⟩, hyc⟩
      · exact Set.mem_iUnion₂.2 ⟨none, Set.mem_insert _ _, hy⟩
    · rintro (_ | c) -
      · show (μ ap an).restrict Uᶜ = (μ an ap).restrict Uᶜ
        rw [Measure.restrict_eq_zero.2 (hzero _ _), Measure.restrict_eq_zero.2 (hzero _ _)]
      · show (μ ap an).restrict c.e.source = (μ an ap).restrict c.e.source
        ext B hB
        have hBs := hB.inter c.e.open_source.measurableSet
        rw [Measure.restrict_apply hB, Measure.restrict_apply hB, hchart _ _ c _ hBs Set.inter_subset_right,
          hchart _ _ c _ hBs Set.inter_subset_right]
        refine setLIntegral_congr_fun (GlobalTheory.ChartGlue.measurableSet_image _ hBs Set.inter_subset_right) fun v hv => ?_
        obtain ⟨y, hy, rfl⟩ := hv
        have h0 := hlin c (c.e.symm (c.e y)) (c.e.map_target (c.e.map_source hy.2))
        have := GlobalTheory.GoodMetric.ChernLin.ofReal_balance a fun j => dens (N j) c (c.e.symm (c.e y))
        rw [h0, mul_zero, mul_zero, ENNReal.ofReal_zero, zero_add, zero_add] at this
        exact this.symm

  have hI : ∀ u w : J → ℝ, (∀ j, 0 ≤ u j) → (∀ j, 0 ≤ w j) → ∫ y, g y ∂μ u w =
      ∑ j, (u j * ∫ y, g y ∂P j 1 + w j * ∫ y, g y ∂P j (-1)) := by
    intro u w hu hw
    simp only [μ]
    rw [integral_finsetSum_measure fun j _ => ((hint j).1.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((hint j).2.smul_measure ENNReal.ofReal_ne_top)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_add_measure ((hint j).1.smul_measure ENNReal.ofReal_ne_top)
      ((hint j).2.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal (hu j), ENNReal.toReal_ofReal (hw j), smul_eq_mul, smul_eq_mul]
  have e := congrArg (fun m : Measure (CxPts p σ) => ∫ y, g y ∂m) hbal
  rw [hI _ _ (fun j => le_max_right _ _) (fun j => le_max_right _ _),
    hI _ _ (fun j => le_max_right _ _) (fun j => le_max_right _ _)] at e
  have key : ∑ j, a j * Mix.int (N j) g =
      ∑ j, (ap j * ∫ y, g y ∂P j 1 + an j * ∫ y, g y ∂P j (-1)) -
      ∑ j, (an j * ∫ y, g y ∂P j 1 + ap j * ∫ y, g y ∂P j (-1)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have ha : ap j - an j = a j := GlobalTheory.GoodMetric.ChernLin.max_sub_max_neg (a j)
    rw [Mix.int]
    simp only [P]
    linear_combination (-(∫ y, g y ∂part (N j) 1) + ∫ y, g y ∂part (N j) (-1)) * ha
  rw [key, e, sub_self]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearRelationMixedDensitiesIntegralsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_relation_mixed_densities_integrals : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (J : Type) [Fintype J] (a : J → ℝ) (L : J → Fin D → MLine p σ), (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ∑ i, a i * dens (L i) c y = 0) → ∀ f : CxPts p σ → ℝ, (∀ i, Intg (L i) f) → ∑ i, a i * Mix.int (L i) f = 0 := by
  first | exact @GlobalTheory.Mix.sum_int_eq_zero_of_dens | exact GlobalTheory.Mix.sum_int_eq_zero_of_dens | (intros; apply GlobalTheory.Mix.sum_int_eq_zero_of_dens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberTermsIsThetaTermsTorsionFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberTermsIsThetaTermsTorsionFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Sep.ThetaTerms

theorem yK_ne_zero {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {x₀ : X₁.S.Gam}
    (hd : X₁.M.Div X₁.S.th x₀ z₁) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V}
    {δ : Fin m → LinearMap.BilinForm ℤ X} (𝔪 : UMem X₁ z₁ act V ev X t δ) :
    𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  obtain ⟨a, ha⟩ := GlobalTheory.ThetaGeneric.exists_th_ne_zero hL.1 hL.2.1 _ _ X₁.S X₁.ρ (FractionRing V) 𝔪.yK
  intro h0
  apply ha
  set y := jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy
  have hs : y (closedPoint (FractionRing V)) ⤳ z₁ := by
    have : y (closedPoint (FractionRing V)) ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hw : ∀ w, y w ⤳ y (closedPoint (FractionRing V)) := fun w => by
    rw [Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) w (closedPoint _)]
  have e : X₁.S.th a = X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀ := (div_mul_cancel₀ _ hd.1).symm
  rw [𝔪.yK_eq] at h0 ⊢
  change X₁.M.val y (X₁.S.th a) = 0
  change X₁.M.val y (X₁.S.th x₀) = 0 at h0
  rw [e, RatModel.val_mul hw ((hd.of_specializes hs).2 a) (𝔪.reg _ (X₁.S.th_mem x₀)), h0, mul_zero]

theorem isThetaTerms₀_of_terms : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), Set.range lab = X₁.S.HH X₁.M z₁ → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → IsThetaTerms₀ 𝔪.D.toPre (X₁.S.r * X₁.S.N) 𝔪.e₈ T := by
  intro g n F W Z i X₁ z₁ act x₀ hd V _ _ _ ev X _ m t δ 𝔪 C lab hlab T hT
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, -, hw₀, -, hg, hT⟩ := hT
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) := by
    have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  have h0 := yK_ne_zero hd 𝔪

  obtain ⟨ρ, hρ, Hr⟩ := GlobalTheory.ConstFam.exists_gen_through (K := PUnit) (φ' := fun _ => eSec 𝔪.A.A)
    (φ := fun _ => eSec X₁.ρ.P.A) (ε := fun _ => 1) (h := spMap 𝔪.yK) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB
    (fun _ => PolBaseChange.eSec_comm 𝔪.cart) X₁.ρ.rig X₁.ρ.rig_gen
  have htf : ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := fun a =>
    GlobalTheory.FrameMove.isTorsFrame_move (T := baseOver (Sp X₁.S.R)) (T' := TFK (R := V) (FractionRing V)) (w := 𝔪.wl)
      (h := spMap 𝔪.yK) 𝔪.cart 𝔪.wl_gen
      (fun Z r z J J' hJ hJ' =>
        (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _))))
      (hx a) (X₁.ρ.fr_tors a) (hfr a).1 (fun z J J' hJ hJ' => ((hfr a).2 z J J' hJ hJ').symm)
  obtain ⟨ρ', c, hc, hN, hmove⟩ := GlobalTheory.T.exists_renormalization_rigidification_multiple V _ 𝔪.D 𝔪.A 𝔪.G 𝔪.U.toUnifPre w₀ hw₀ ρ hρ
  choose w' fr' hw' hfr' hov hco hval using fun a : C => liesOver_scale V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.U.toUnifPre (FractionRing V) w₀
    (g' a) (w a) (x (lab a)) (fr (lab a)) (hg a).2.1 (hfr _).1 (hg a).2.2 c hc
  have htors : ∀ a, (g' a).b ^ (X₁.S.r * X₁.S.N) = 1 := fun a => by
    obtain ⟨o, h₁, h₂⟩ := (hg a).1
    letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (FractionRing V)
    have e := congrArg (GlobalTheory.TorusExt.gtProj 𝔪.D.toPre (FractionRing V)) ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 h₁)
    rw [map_nsmul] at e
    exact (congrArg Additive.toMul e).symm.trans ((isZero_iff o).1 h₂).1
  choose b hb₁ hb₂ using fun a => GlobalTheory.T.torsionPoint_extends_over_normal_domain hL.1 V 𝔪.cn.1 𝔪.cn.2.1 𝔪.D.toPre.P _ hk (g' a).b (htors a)
  refine ⟨(c / 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) • s + 0, g', b, w', hb₂, fun a => (hg a).1, ?_, fun a => ⟨hw' a, ?_⟩,
    fun mu a => ?_⟩
  · refine GlobalTheory.T.torsion_sections_exhaust_geometric_fibres hL.1 V 𝔪.cn.1 𝔪.D.toPre.P _ hk hu C b hb₁ fun p hp => ?_
    obtain ⟨a, ha⟩ := exhaust_of_labels hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hk C g' (fun a => x (lab a)) (fun a => (hg a).1)
      (fun a a' e => by
        have h₁ := hg a
        have h₂ := hg a'
        generalize w a' = om at h₂
        generalize g' a' = ga at e om h₂
        subst e
        exact GlobalTheory.T.eq_of_framedPoint_lies_over_torus_extension hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ w₀ hw₀ _ _ _ _ _ _ _ h₁.2.1 h₂.2.1 (hfr _).1 (hfr _).1
          h₁.2.2 h₂.2.2)
      (fun q y hq hy => by
        have hyN : y ^ (X₁.S.r * X₁.S.N) = 1 := (hy w₀ hw₀).1
        have e : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK =
            spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) :=
          (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom (algebraMap _ _))).symm
        obtain ⟨l, hl, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ (Geo.Tor.pushHom 𝔪.cart _ y)
          (by rw [← map_pow, hyN, map_one])
        have hl' : y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
            (X₁.ρ.pt l).left := by
          rw [← e]
          exact (congrArg (fun q => q.left) hl).symm
        have hH : l ∈ X₁.S.HH X₁.M z₁ := (GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i X₁ z₁ act x₀ hd V ev X m t δ 𝔪 l).2
          ⟨q, y, by rw [hq, map_zero], hy, hl'⟩
        obtain ⟨a, rfl⟩ : l ∈ Set.range lab := by rw [hlab]; exact hH
        refine ⟨a, 𝔪.cart.1.hom_ext ?_ ?_⟩
        · rw [hl', ← e]
          exact ((Category.assoc _ _ _).trans ((congrArg _ (hx _)).trans (Category.assoc _ _ _).symm)).symm
        · refine (Over.w y).trans (Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg _ (Over.w (x (lab a))))).symm)
          exact (Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) p hp
    refine ⟨a, Over.OverMorphism.ext ?_⟩
    rw [ha, hb₂ a, Over.comp_left, Over.comp_left, ← Category.assoc]
    congr 1
    change spMap _ ≫ spMap _ ≫ jK V = spMap _ ≫ jK V
    rw [Algebra.algebraMap_self, show spMap (RingHom.id (FractionRing V)) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  · obtain ⟨o, h₁, h₂⟩ := (hg a).1
    exact GlobalTheory.T.torsion_frame_abelian_part_torsion_frame hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ w₀ ρ' hN _ hk _ o h₁ h₂ _ _ _ (hw' a) (hov a)
      (hmove _ _ _ _ _ (htf _) (hfr' a) (hval a))
  · have h₁ := ((CoefBasic.coef_basic V 𝔪.D.toPre (FractionRing V) 1 (g' a)).2.2 (w' a) (hw' a)).2.1
    have h₂ : coef (0 : Fam 𝔪.D.toPre (FractionRing V) 1) (g' a) (w' a) (𝔪.e₈ mu) = 0 := by
      have := h₁ 0 0 1 (𝔪.e₈ mu)
      rw [one_smul, add_zero, _root_.one_mul] at this
      exact left_eq_add.1 this
    have h₃ : algebraMap V (FractionRing V) (T mu a) =
        coef ((c / 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) • s + 0) (g' a) (w' a) (𝔪.e₈ mu) := by
      rw [h₁, h₂, add_zero, div_mul_eq_mul_div, hco, ← hT, mul_div_cancel_right₀ _ h0]
    rw [h₃]
    exact CoefBasic.isCoef_coef _ (hw' a) _ _

end GlobalTheory.Poinc.Sep.ThetaTerms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberTermsIsThetaTermsTorsionFramesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberTerms_isThetaTerms_torsionFrames : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), Set.range lab = X₁.S.HH X₁.M z₁ → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → IsThetaTerms₀ 𝔪.D.toPre (X₁.S.r * X₁.S.N) 𝔪.e₈ T := by
  first | exact @GlobalTheory.Poinc.Sep.ThetaTerms.isThetaTerms₀_of_terms | exact GlobalTheory.Poinc.Sep.ThetaTerms.isThetaTerms₀_of_terms | (intros; apply GlobalTheory.Poinc.Sep.ThetaTerms.isThetaTerms₀_of_terms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdeleLimitCompatibleIntSystem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdeleLimitCompatibleIntSystem
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

noncomputable section

open IsDedekindDomain
namespace GlobalTheory.CompatLim

theorem norm_sub_le_of_dvd (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) (x y : ℤ) (h : ((ℓ ^ k : ℕ) : ℤ) ∣ x - y) :
    ‖((x : ℤ_[ℓ]) - (y : ℤ_[ℓ]))‖ ≤ (ℓ : ℝ) ^ (-(k : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
  obtain ⟨c, hc⟩ := h
  refine ⟨(c : ℤ_[ℓ]), ?_⟩
  have := congrArg (fun z : ℤ => (z : ℤ_[ℓ])) hc
  push_cast at this
  rw [← this]

theorem exists_padicInt_lim (p ℓ : ℕ) [Fact ℓ.Prime] (hp : p.Prime) (hne : ℓ ≠ p) (a : ℕ → ℤ)
    (ha : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) :
    ∃ L : ℤ_[ℓ], ∀ n : ℕ, 0 < n → n.Coprime p → ∃ b : ℤ_[ℓ], L = (a n : ℤ_[ℓ]) + (n : ℤ_[ℓ]) * b := by
  have hℓ : ℓ.Prime := Fact.out
  have hcop : ∀ k, (ℓ ^ k).Coprime p := fun k => Nat.Coprime.pow_left k ((Nat.coprime_primes hℓ hp).2 hne)
  have hpos : ∀ k, 0 < ℓ ^ k := fun k => pow_pos hℓ.pos k

  have key : ∀ k m, k ≤ m → ((ℓ ^ k : ℕ) : ℤ) ∣ a (ℓ ^ m) - a (ℓ ^ k) := by
    intro k m hkm
    have h := ha (ℓ ^ k) (ℓ ^ (m - k)) (hpos k) (hpos _) (by rw [← pow_add, Nat.add_sub_cancel' hkm]; exact hcop m)
    rwa [← pow_add, Nat.add_sub_cancel' hkm] at h
  set s : ℕ → ℤ_[ℓ] := fun k => (a (ℓ ^ k) : ℤ_[ℓ]) with hs
  have hdist : ∀ k m, k ≤ m → dist (s m) (s k) ≤ (ℓ : ℝ) ^ (-(k : ℤ)) := by
    intro k m hkm
    rw [dist_eq_norm]
    exact norm_sub_le_of_dvd ℓ k _ _ (key k m hkm)
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
  have hcs : CauchySeq s := by
    refine cauchySeq_of_le_geometric ((ℓ : ℝ)⁻¹) 1 (inv_lt_one_of_one_lt₀ hℓ1) fun k => ?_
    rw [dist_comm, _root_.one_mul, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact hdist k (k + 1) (Nat.le_succ k)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  have hLk : ∀ k, ‖L - s k‖ ≤ (ℓ : ℝ) ^ (-(k : ℤ)) := by
    intro k
    have hmem : L ∈ Metric.closedBall (s k) ((ℓ : ℝ) ^ (-(k : ℤ))) :=
      Metric.isClosed_closedBall.mem_of_tendsto hL
        (Filter.eventually_atTop.2 ⟨k, fun m hm => Metric.mem_closedBall.2 (hdist k m hm)⟩)
    rwa [Metric.mem_closedBall, dist_eq_norm] at hmem
  refine ⟨L, fun n hn hnp => ?_⟩
  set e := n.factorization ℓ
  set m := n / ℓ ^ e
  have hnm : ℓ ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n ℓ
  have hm : ℓ.Coprime m := Nat.coprime_ordCompl hℓ hn.ne'
  have hmpos : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hnm; omega

  have h1 : L - s e ∈ Ideal.span {(ℓ : ℤ_[ℓ]) ^ e} := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 (hLk e)

  have h2 := ha (ℓ ^ e) m (hpos e) hmpos (by rw [hnm]; exact hnp)
  rw [hnm] at h2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 h1
  obtain ⟨d, hd⟩ := h2
  have hu : IsUnit (m : ℤ_[ℓ]) := PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hm)
  obtain ⟨u, hu⟩ := hu
  refine ⟨(u⁻¹ : ℤ_[ℓ]ˣ) * (c - (d : ℤ_[ℓ])), ?_⟩
  have hd' : (a n : ℤ_[ℓ]) - s e = (ℓ : ℤ_[ℓ]) ^ e * d := by
    have := congrArg (fun z : ℤ => (z : ℤ_[ℓ])) hd
    push_cast at this
    simpa [hs] using this
  have hn' : (n : ℤ_[ℓ]) = (ℓ : ℤ_[ℓ]) ^ e * u := by
    rw [hu, ← hnm]; push_cast; ring
  rw [hn']
  have : (ℓ : ℤ_[ℓ]) ^ e * (u : ℤ_[ℓ]) * ((u⁻¹ : ℤ_[ℓ]ˣ) * (c - d)) = (ℓ : ℤ_[ℓ]) ^ e * (c - d) := by
    rw [_root_.mul_assoc, ← _root_.mul_assoc (u : ℤ_[ℓ]), Units.mul_inv, _root_.one_mul]
  rw [this]
  linear_combination hc - hd'

open Rat.HeightOneSpectrum in
theorem natGenerator_ne (p : ℕ) (v : AwayP p) : (primesEquiv v.1 : ℕ) ≠ p := by
  obtain ⟨w, hw⟩ := v
  intro h
  apply hw
  have hs := span_natGenerator (R := ℤ) w
  change natGenerator w = p at h
  rw [h] at hs
  rw [hs]
  ext x
  rw [Ideal.mem_map_of_equiv]
  simp [eq_intCast]


open Rat.HeightOneSpectrum in
theorem exists_integer_lim (p : ℕ) [hp : Fact p.Prime] (a : ℕ → ℤ)
    (ha : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) (v : AwayP p) :
    ∃ x : v.1.adicCompletionIntegers ℚ, ∀ n : ℕ, 0 < n → n.Coprime p →
      ∃ b : v.1.adicCompletionIntegers ℚ, x = (a n : v.1.adicCompletionIntegers ℚ) + (n : v.1.adicCompletionIntegers ℚ) * b := by
  haveI : Fact (primesEquiv v.1 : ℕ).Prime := ⟨(primesEquiv v.1).2⟩
  obtain ⟨L, hL⟩ := exists_padicInt_lim p (primesEquiv v.1 : ℕ) hp.out (natGenerator_ne p v) a ha
  let e := (RingEquivClass.toRingEquiv (adicCompletionIntegers.padicIntEquiv (R := ℤ) v.1)).symm
  refine ⟨e L, fun n hn hnp => ?_⟩
  obtain ⟨b, hb⟩ := hL n hn hnp
  refine ⟨e b, ?_⟩
  rw [hb, map_add (f := _), map_mul, map_intCast, map_natCast]

theorem exists_lim : ∀ (p : ℕ) [Fact p.Prime] (a : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) → ∃ α : AfP p, IsIntAf α ∧ ∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ α = (a n : AfP p) + n • β := by
  intro p _ a ha
  choose x hx using exists_integer_lim p a ha
  let α : AfP p := RestrictedProduct.mk (fun v => (x v : v.1.adicCompletion ℚ)) (Filter.Eventually.of_forall fun v => (x v).2)
  refine ⟨α, fun v => (x v).2, fun n hn hnp => ?_⟩
  choose b hb using fun v => hx v n hn hnp
  let β : AfP p := RestrictedProduct.mk (fun v => (b v : v.1.adicCompletion ℚ)) (Filter.Eventually.of_forall fun v => (b v).2)
  refine ⟨β, fun v => (b v).2, ?_⟩
  apply RestrictedProduct.ext
  intro v
  have h1 : AfP.eval v α = x v := rfl
  have h2 : AfP.eval v β = b v := rfl
  have h3 : AfP.eval v ((a n : AfP p) + n • β) = (a n : v.1.adicCompletion ℚ) + (n : v.1.adicCompletion ℚ) * b v := by
    rw [map_add (f := _), map_intCast, map_nsmul, h2, nsmul_eq_mul]
  change AfP.eval v α = AfP.eval v ((a n : AfP p) + n • β)
  rw [h3, h1, hb v]
  push_cast
  rfl

end GlobalTheory.CompatLim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdeleLimitCompatibleIntSystemStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralAdeleLimit_compatibleIntSystem : ∀ (p : ℕ) [Fact p.Prime] (a : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) → ∃ α : AfP p, IsIntAf α ∧ ∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ α = (a n : AfP p) + n • β := by
  first | (exact @GlobalTheory.CompatLim.exists_lim) | (exact GlobalTheory.CompatLim.exists_lim) | (intros; apply GlobalTheory.CompatLim.exists_lim  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigAlongBox
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

noncomputable section

namespace GlobalTheory.ProdUnif

open GlobalTheory.UnifPullRig

theorem rigAlong_box : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → ∀ (we : LB.Iso (L.pull f) (M.pull p)), BoxSq wM wL we we₁ we₂ h₁ h₂ → ∀ {S S₀ : Scheme.{0}} (u : S ⟶ T) (u₁ : S ⟶ T₁) (u₂ : S ⟶ T₂) (s : S ⟶ S₀) {eG : S₀ ⟶ G} {eG₁ : S₀ ⟶ G₁} {eG₂ : S₀ ⟶ G₂} {eB : S₀ ⟶ B} {eB₁ : S₀ ⟶ B₁} {eB₂ : S₀ ⟶ B₂} (rL : LB.Gen (L.pull eG)) (rL₁ : LB.Gen (L₁.pull eG₁)) (rL₂ : LB.Gen (L₂.pull eG₂)) (rM : LB.Gen (M.pull eB)) (rM₁ : LB.Gen (M₁.pull eB₁)) (rM₂ : LB.Gen (M₂.pull eB₂)), u ≫ h₁ = u₁ → u ≫ h₂ = u₂ → u ≫ f = s ≫ eG → u ≫ p = s ≫ eB → u₁ ≫ f₁ = s ≫ eG₁ → u₁ ≫ p₁ = s ≫ eB₁ → u₂ ≫ f₂ = s ≫ eG₂ → u₂ ≫ p₂ = s ≫ eB₂ → IsBoxGen wL (𝟙 S₀) (𝟙 S₀) rL rL₁ rL₂ → IsBoxGen wM (𝟙 S₀) (𝟙 S₀) rM rM₁ rM₂ → GlobalTheory.UnifPullRig.RigAlong we₁ u₁ s rL₁ rM₁ → GlobalTheory.UnifPullRig.RigAlong we₂ u₂ s rL₂ rM₂ → GlobalTheory.UnifPullRig.RigAlong we u s rL rM := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂ hM hM₁ hM₂
    hL hL₁ hL₂ hpb₁ hpb₂ hfg₁ hfg₂ we hQ S S₀ u u₁ u₂ s eG eG₁ eG₂ eB eB₁ eB₂ rL rL₁ rL₂ rM rM₁ rM₂ hu₁ hu₂
    hf hp hf₁ hp₁ hf₂ hp₂ bL bM H₁ H₂
  rintro ⟨qM, qL⟩ V a₁ a₂ a₃
  refine unit_ext fun y hy => ?_
  obtain ⟨J, hJ, eJ⟩ := exists_good M hM y (K := PUnit) (fun _ => s ≫ eB) (fun _ => qM ⟨⟩)
    (fun _ _ _ => rfl) (fun _ => (mem_pull (F := eB) (x := s y)).1 (a₃ hy))
  obtain ⟨N, hN, eN⟩ := exists_good L hL y (K := PUnit) (fun _ => s ≫ eG) (fun _ => qL ⟨⟩)
    (fun _ _ _ => rfl) (fun _ => (mem_pull (F := eG) (x := s y)).1 (a₂ hy))
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at hM₁ y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at hM₂ y
  obtain ⟨N₁, hN₁⟩ := BoxFamily.exists_good_at hL₁ y
  obtain ⟨N₂, hN₂⟩ := BoxFamily.exists_good_at hL₂ y
  have m₁ : (u ≫ p) ≫ b₁ = s ≫ eB₁ := by rw [Category.assoc, hpb₁, ← Category.assoc, hu₁, hp₁]
  have m₂ : (u ≫ p) ≫ b₂ = s ≫ eB₂ := by rw [Category.assoc, hpb₂, ← Category.assoc, hu₂, hp₂]
  have n₁ : (u ≫ f) ≫ g₁ = s ≫ eG₁ := by rw [Category.assoc, hfg₁, ← Category.assoc, hu₁, hf₁]
  have n₂ : (u ≫ f) ≫ g₂ = s ≫ eG₂ := by rw [Category.assoc, hfg₂, ← Category.assoc, hu₂, hf₂]
  have Q := hQ S u y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
  rw [m₁, m₂, n₁, n₂, hu₁, hu₂, hp, hf] at Q
  have HM := bM S s y J₁ J₂ J hJ₁ hJ₂ hJ
  have HL := bL S s y N₁ N₂ N hN₁ hN₂ hN
  simp only [Category.comp_id] at HM HL
  have E₁ := H₁.stalk hf₁ hp₁ (𝟙 S) y (J₁ (s ≫ eB₁)) (N₁ (s ≫ eG₁))
    ((pt_of_eq hp₁ y).symm ▸ hJ₁ (s ≫ eB₁)) ((pt_of_eq hf₁ y).symm ▸ hN₁ (s ≫ eG₁))
  have E₂ := H₂.stalk hf₂ hp₂ (𝟙 S) y (J₂ (s ≫ eB₂)) (N₂ (s ≫ eG₂))
    ((pt_of_eq hp₂ y).symm ▸ hJ₂ (s ≫ eB₂)) ((pt_of_eq hf₂ y).symm ▸ hN₂ (s ≫ eG₂))
  simp only [Category.id_comp] at E₁ E₂
  have key := rel_alg (K := PUnit) (fun _ => 1) (fun _ => om wM y J₁ J₂ J (s ≫ eB))
    (fun _ => om wL y N₁ N₂ N (s ≫ eG)) (fun _ => gw we u y (J (s ≫ eB)) (fun _ => N (s ≫ eG)))
    (fun _ => gw we₁ u₁ y (J₁ (s ≫ eB₁)) (fun _ => N₁ (s ≫ eG₁)))
    (fun _ => gw we₂ u₂ y (J₂ (s ≫ eB₂)) (fun _ => N₂ (s ≫ eG₂))) (fun _ => Q) HM HL
    (by rw [Fintype.prod_unique, zpow_one]; exact E₁.symm) (by rw [Fintype.prod_unique, zpow_one]; exact E₂.symm)
  rw [Fintype.prod_unique, zpow_one, val_of rM s y J qM (fun k => eJ k), val_of rL s y N qL (fun k => eN k),
    eJ ⟨⟩, eN ⟨⟩] at key
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res_pull _ u y a₁ hy _)
    (gm_res_pull _ s y a₂ hy _)).trans (Eq.trans ?_ (gm_res_pull _ s y a₃ hy _).symm))
  simp only [Category.id_comp]
  exact key.symm

end GlobalTheory.ProdUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentValuePullbackCrystallineFormDualNumbers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentValuePullbackCrystallineFormDualNumbers
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ParPt

theorem tanVal_pullForm_ofModule : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) (A' : Over (Sp R')) (φ : A'.left ⟶ A.left) (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (v : epsR R' ⟶ A') (hy : (v.left ≫ φ) ≫ A.hom ≫ 𝟙 (Sp R) = spMap (algebraMap R (DualNumber R'))) (f : Form (A.hom ≫ 𝟙 (Sp R))), tanVal v (m.pullForm f) = TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val (v.left ≫ φ) hy f.1) := by
  intro R R' _ _ _ A A' φ m v hy f
  let E := SqExt.ofModule R R' R'
  let E' := SqExt.dual R'
  have hy' := pt_w v
  have hc : ∀ r : R, RingHom.id (DualNumber R') (algebraMap R (DualNumber R') r) =
      algebraMap R' (DualNumber R') (algebraMap R R' r) := fun r =>
    IsScalarTower.algebraMap_apply R R' (DualNumber R') r
  have e₀ : spMap (RingHom.id R') ≫ spMap (E.π : E.C →+* E.B) ≫ v.left ≫ φ =
      (spMap (E'.π : E'.C →+* E'.B) ≫ v.left) ≫ φ := by
    rw [Category.assoc, ← Category.assoc, ← Cris.spMap_comp]
    rfl
  have e : spMap (RingHom.id (DualNumber R')) ≫ v.left ≫ φ = v.left ≫ φ := by
    rw [Cris.spMap_id, Category.id_comp]
  let Φ : E.thick _ (E.red_w hy) ⟶ m.obj (E'.thick _ (E'.red_w hy')) :=
    { φ := { RingHom.id (DualNumber R') with commutes' := hc }
      φ₀ := RingHom.id R'
      comm := fun b => rfl
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun a ha => ha
      pt := e₀ }
  let a : Thick.triv E.C _ hy ⟶ m.obj (Thick.triv E'.C _ hy') :=
    Thick.trivHom { RingHom.id (DualNumber R') with commutes' := hc } e
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hy')) :=
    Thick.trivHom { RingHom.id R' with commutes' := fun _ => rfl } e₀
  have k1 := Form.ev_sq f a (m.functor.map (E'.idHom hy')) (E.idHom hy) Φ rfl rfl fun _ => rfl
  have k2 := Form.ev_sq f b (m.functor.map (E'.secHom (E'.red_w hy') E'.i E'.π_i))
    (E.secHom (E.red_w hy) E.i E.π_i) Φ rfl rfl fun c => rfl
  have k : E'.val v.left hy' (m.pullForm f).1 = E.val (v.left ≫ φ) hy f.1 :=
    (congrArg₂ (fun u v : E'.C => u - v) k2 k1).trans
      (add_sub_add_right_eq_sub (G := E'.C) _ _ _)
  rw [tanVal_apply]
  exact congrArg (TrivSqZeroExt.snd (R := R')) k

end GlobalTheory.ParPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentValuePullbackCrystallineFormDualNumbersStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_value_pullback_crystalline_form_dual_numbers : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) (A' : Over (Sp R')) (φ : A'.left ⟶ A.left) (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (v : epsR R' ⟶ A') (hy : (v.left ≫ φ) ≫ A.hom ≫ 𝟙 (Sp R) = spMap (algebraMap R (DualNumber R'))) (f : Form (A.hom ≫ 𝟙 (Sp R))), tanVal v (m.pullForm f) = TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val (v.left ≫ φ) hy f.1) := by
  first | exact @GlobalTheory.ParPt.tanVal_pullForm_ofModule | exact GlobalTheory.ParPt.tanVal_pullForm_ofModule | (intros; apply GlobalTheory.ParPt.tanVal_pullForm_ofModule <;> assumption)
end
end
