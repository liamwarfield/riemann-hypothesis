module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralPullbackGenericallyFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoEqOneAlongAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdMulInertiaDegEqFinrankMulOrd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLelongNormalCrossingsSmoothProjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDivisorIntegralPushforward
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosurePullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasurePullbackEqZeroOfLtDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonKernelHessiansPullbackSmallerChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonKernelHessiansPullbackSmallerChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.HessKer

open ReciprocityTheory.L2DbarEstimates (V cHess bas)

theorem exists_vecMul_eq_zero {D D' : ℕ} (h : D' < D) (P : Matrix (Fin D) (Fin D') ℂ) :
    ∃ ξ : Fin D → ℂ, ξ ≠ 0 ∧ Matrix.vecMul ξ P = 0 := by
  have hk : LinearMap.ker P.vecMulLinear ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using h)
  obtain ⟨ξ, hξ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨ξ, h0, by simpa using hξ⟩

theorem exists_common_kernel : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D D' : ℕ), D' < D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (c : AlgChart p σ D') (c' : AlgChart q σ D) (w : CxPts q σ), w ∈ c'.e.source → ptMap π hπ σ w ∈ c.e.source → ∃ ξ : Fin D → ℂ, ξ ≠ 0 ∧ ∀ (A : MLine p σ) (i : (A.pull π hπ).B.ι), w ∈ ptsIn q σ ((A.pull π hπ).B.U i) → Matrix.vecMul ξ (c'.hess (A.pull π hπ).φ i w) = 0 := by
  intro k _ X Y p q σ D D' hD π hπ c c' y hy hy0
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  set F : V D → V D' := c.e ∘ m ∘ c'.e.symm with hFdef
  set U := c'.e.target ∩ c'.e.symm ⁻¹' (m ⁻¹' c.e.source)
  have hU : IsOpen U := isOpen_over c'.e (c.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c'.e y ∈ U := mem_over c'.e hy hy0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c' c
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c'.e y) = c.e (m y) := by
    simp only [hFdef, Function.comp_apply, c'.e.left_inv hy]
  obtain ⟨ξ, hξ, hP⟩ := exists_vecMul_eq_zero hD (Matrix.of fun j b => fderiv ℂ F (c'.e y) (bas D j) b)
  refine ⟨ξ, hξ, fun A i hi => ?_⟩
  have him : m y ∈ ptsIn p σ (A.B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hi PUnit.unit
  set g : V D' → ℂ := fun v => (A.φ.φ (i PUnit.unit) (c.e.symm v) : ℂ)
  have hg : ContDiffAt ℝ 2 g (F (c'.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (A.cInf.contDiffAt c hy0 him)
  have e : (fun v => ((A.pull π hπ).φ.φ i (c'.e.symm v) : ℂ)) =ᶠ[𝓝 (c'.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ A.φ π hπ i (c'.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c.e.left_inv hv.2]
    exact congrArg _ this
  have key : c'.hess (A.pull π hπ).φ i y =
      (Matrix.of fun j b => fderiv ℂ F (c'.e y) (bas D j) b) * (cHess D' g (F (c'.e y)) *
        Matrix.of fun a l => (starRingEnd ℂ) (fderiv ℂ F (c'.e y) (bas D l) a)) := by
    show cHess D _ (c'.e y) = _
    rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e, ← Matrix.mul_assoc]
    ext j l
    rw [GlobalTheory.HessPull.cHess_comp_apply D D' g F U hU _ hyU hF hg j l, Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [key, ← Matrix.vecMul_vecMul, hP, Matrix.zero_vecMul]

end GlobalTheory.HessKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonKernelHessiansPullbackSmallerChartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_kernel_hessians_pullback_smaller_chart : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D D' : ℕ), D' < D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (c : AlgChart p σ D') (c' : AlgChart q σ D) (w : CxPts q σ), w ∈ c'.e.source → ptMap π hπ σ w ∈ c.e.source → ∃ ξ : Fin D → ℂ, ξ ≠ 0 ∧ ∀ (A : MLine p σ) (i : (A.pull π hπ).B.ι), w ∈ ptsIn q σ ((A.pull π hπ).B.U i) → Matrix.vecMul ξ (c'.hess (A.pull π hπ).φ i w) = 0 := by
  exact @GlobalTheory.HessKer.exists_common_kernel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasurePullbackEqZeroOfLtDim
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixDrop

theorem part_pull_eq_zero : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D D' : ℕ), D' < D → IsProjOver p → topologicalKrullDim X = (D' : ℕ) → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ (L : Fin D → MLine p σ) (ε : ℤˣ), part (fun i => (L i).pull π hπ) ε = 0 := by
  intro F _ X Y _ _ p q σ D D' hD hp hX hq π hπ hgen L ε
  have hLN : IsLocallyNoetherian X := by
    obtain ⟨N, ι, _, h⟩ := hp
    have : LocallyOfFiniteType p := h ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨U, hU, hch⟩ := GlobalTheory.GenericCharts.exists_generic_charts F X p σ D' hp hX
  have hgU : genericPoint Y ∈ π ⁻¹ᵁ U := by
    show π (genericPoint Y) ∈ U
    rw [hgen]; exact hU
  have hnull := GlobalTheory.MixNull.part_compl_null F Y q σ σ.injective hq D (fun i => (L i).pull π hπ) ε (π ⁻¹ᵁ U) hgU
  have hz : ∀ (c : AlgChart q σ D) (w : CxPts q σ), w ∈ c.e.source → w ∈ ptsIn q σ (π ⁻¹ᵁ U) →
      dens (fun i => (L i).pull π hπ) c w = 0 := by
    intro c w hw hwU
    have hm : ptMap π hπ σ w ∈ ptsIn p σ U := by
      rw [mem_ptsIn] at hwU ⊢
      exact hwU
    obtain ⟨c0, hc0⟩ := hch _ hm
    obtain ⟨ξ, hξ, hker⟩ := GlobalTheory.T.exists_common_kernel_hessians_pullback_smaller_chart F X Y p q σ D D' hD π hπ c0 c w hw hc0
    have hdet : ∀ τ : Equiv.Perm (Fin D), (Matrix.of fun j l =>
        c.hess ((L (τ l)).pull π hπ).φ (pick ((L (τ l)).pull π hπ).φ.isLB w) w j l).det = 0 := by
      intro τ
      refine (Matrix.exists_vecMul_eq_zero_iff).1 ⟨ξ, hξ, funext fun l => ?_⟩
      have h1 := congrFun (hker (L (τ l)) (pick ((L (τ l)).pull π hπ).φ.isLB w) (mem_pick _ w)) l
      simpa [Matrix.vecMul, dotProduct] using h1
    unfold dens
    simp only [hdet, Finset.sum_const_zero, Complex.zero_re, mul_zero]
  have hc : ∀ c : AlgChart q σ D, chartMeas c.e
      (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y)) = 0 := by
    intro c
    set S := ptsIn q σ (π ⁻¹ᵁ U) with hSdef
    have hS : MeasurableSet S := (isOpen_ptsIn _).measurableSet
    have h1 : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y)) S = 0 := by
      rw [chartMeas_apply c.e _ hS]
      refine (setLIntegral_congr_fun (measurableSet_image _ (c.e.open_source.measurableSet.inter hS)
        inter_subset_left) ?_).trans lintegral_zero
      rintro _ ⟨y, hy, rfl⟩
      show ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c (c.e.symm (c.e y))) = 0
      rw [c.e.left_inv hy.1, hz c y hy.1 hy.2, mul_zero, ENNReal.ofReal_zero]
    have hle : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y)) ≤
        part (fun i => (L i).pull π hπ) ε :=
      le_iSup (fun c : AlgChart q σ D => chartMeas c.e
        (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y))) c
    have h2 := (Measure.le_iff'.1 hle Sᶜ).trans_eq hnull
    refine Measure.measure_univ_eq_zero.1 (le_antisymm ?_ bot_le)
    calc _ ≤ _ := measure_mono (show univ ⊆ S ∪ Sᶜ by simp)
      _ ≤ _ := measure_union_le _ _
      _ ≤ 0 := by rw [h1, zero_add]; exact h2
  show glueMeas _ _ = 0
  unfold glueMeas
  simp only [hc]
  exact le_antisymm (iSup_le fun _ => le_rfl) (Measure.zero_le _)

end GlobalTheory.MixDrop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasurePullbackEqZeroOfLtDimStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernMeasure_pullback_eq_zero_of_lt_dim : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D D' : ℕ), D' < D → IsProjOver p → topologicalKrullDim X = (D' : ℕ) → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ (L : Fin D → MLine p σ) (ε : ℤˣ), part (fun i => (L i).pull π hπ) ε = 0 := by
  first | exact @GlobalTheory.MixDrop.part_pull_eq_zero | exact GlobalTheory.MixDrop.part_pull_eq_zero | (intros; apply GlobalTheory.MixDrop.part_pull_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosurePullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.CycPush

theorem isProjOver_comp {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsProjOver p)
    (i : Z ⟶ X) [IsClosedImmersion i] : IsProjOver (i ≫ p) := by
  obtain ⟨N, j, hj, rfl⟩ := hp
  exact ⟨N, i ≫ j, inferInstance, by rw [Category.assoc]⟩

theorem pull_congr {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    (A : MLine p σ) {a b : Y ⟶ X} (hab : a = b) (ha : a ≫ p = q) (hb : b ≫ p = q) :
    A.pull a ha = A.pull b hb := by
  subst hab; rfl

theorem dim_le_of_dominant : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → ∀ n : ℕ, topologicalKrullDim Y = n → ∃ m : ℕ, m ≤ n ∧ topologicalKrullDim X = m := by
  intro F _ W M _ _ p q hp hq f hπ hη n hM
  obtain ⟨N, i, hi, hcomp⟩ := hp
  obtain ⟨N', j, hj, hcomp'⟩ := hq
  haveI : IsProper (PSpace.str F N) := isProper_str F N
  haveI : IsProper (PSpace.str F N') := isProper_str F N'
  haveI : IsProper p := by rw [← hcomp]; infer_instance
  haveI : IsProper (f ≫ p) := by rw [hπ, ← hcomp']; infer_instance
  haveI : IsProper f := IsProper.of_comp f p
  have hf : LocallyOfFiniteType f := inferInstance
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  have hV : IsAffineOpen V := hV
  have hx : f (genericPoint M) ∈ V := hη ▸ hxV
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, hUV⟩ := M.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint M ∈ f ⁻¹ᵁ V from hx) (f ⁻¹ᵁ V).isOpen
  have hU : IsAffineOpen U := hU
  haveI : Nonempty V := ⟨⟨_, hx⟩⟩
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  have e : U ≤ f ⁻¹ᵁ V := hUV
  let φ := Spec.preimage (hV.fromSpec ≫ p)
  have hφ : Spec.map φ = hV.fromSpec ≫ p := Spec.map_preimage _
  letI : Algebra F Γ(W, V) := φ.hom.toAlgebra
  have hftA : Algebra.FiniteType F Γ(W, V) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  letI : Algebra Γ(W, V) Γ(M, U) := (f.appLE V U e).hom.toAlgebra
  have hftB : Algebra.FiniteType Γ(W, V) Γ(M, U) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f hf ⟨V, hV⟩ ⟨U, hU⟩ e
  letI : Algebra F Γ(M, U) := (φ ≫ f.appLE V U e).hom.toAlgebra
  haveI : IsScalarTower F Γ(W, V) Γ(M, U) := IsScalarTower.of_algebraMap_eq' rfl
  have hftC : Algebra.FiniteType F Γ(M, U) := Algebra.FiniteType.trans hftA hftB
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(W, V)
  have hd : topologicalKrullDim (V : Set W) = d := by
    rw [← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
      hV.range_fromSpec
  rw [GlobalTheory.OpenDim.topologicalKrullDim_open F p V ⟨_, hx⟩] at hd
  have hB : Algebra.trdeg F Γ(M, U) = n := GlobalTheory.GenFinite.trdeg_affineOpen_eq F (f ≫ p) hU ⟨_, hy⟩ n hM
  letI := (W.evaluation V _ hx).hom.toAlgebra
  have nat : f.appLE V U e ≫ M.evaluation U _ hy =
      W.evaluation V _ hx ≫ f.residueFieldMap (genericPoint M) := by
    rw [Scheme.evaluation_naturality f _ hx, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp only [Scheme.evaluation]
    rw [← Category.assoc, TopCat.Presheaf.germ_res]
  haveI := GenFiniteEtale.isFractionRing_eval W hV hη hx
  have hinj : Function.Injective (IsScalarTower.toAlgHom F Γ(W, V) Γ(M, U)) := by
    have h₃ : Function.Injective (f.appLE V U e ≫ M.evaluation U _ hy).hom := by
      rw [nat]
      exact (f.residueFieldMap (genericPoint M)).hom.injective.comp
        (IsFractionRing.injective Γ(W, V) (W.residueField (f (genericPoint M))))
    exact Function.Injective.of_comp (f := (M.evaluation U _ hy).hom) h₃
  have hle := trdeg_le_of_injective _ hinj
  rw [h₂, hB] at hle
  exact ⟨d, by exact_mod_cast hle, hd⟩

theorem cycInt_pull : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (e : ℕ) (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∀ w : Y, topologicalKrullDim (closure ({w} : Set Y)) = e → (topologicalKrullDim (closure ({π w} : Set X)) = e → cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = π.residueDegree w * cycInt L f (π w)) ∧ (topologicalKrullDim (closure ({π w} : Set X)) ≠ e → cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = 0) := by
  intro F _ X Y p q σ hp hq π hπ e L f hf w hw
  obtain ⟨hIw, hgw, hdw, -⟩ := GlobalTheory.ClosFacts.clos_facts Y w
  obtain ⟨hIx, hgx, hdx, hfac⟩ := GlobalTheory.ClosFacts.clos_facts X (π w)
  have hη : (closι w ≫ π) (genericPoint (clos w)) = π w := by
    rw [Scheme.Hom.comp_apply, hgw]
  obtain ⟨g, hg, hgg, hgdeg, -⟩ := hfac (clos w) (closι w ≫ π) hη
  have hpX : IsProjOver (closι (π w) ≫ p) := isProjOver_comp hp _
  have hpY : IsProjOver (closι w ≫ q) := isProjOver_comp hq _
  have hgp : g ≫ closι (π w) ≫ p = closι w ≫ q := by
    rw [← Category.assoc, hg, Category.assoc, hπ]
  have hdY : topologicalKrullDim (clos w) = e := hdw.trans hw
  let L' : Fin e → MLine (closι (π w) ≫ p) σ := fun i => (L i).pull (closι (π w)) rfl
  let f' : CxPts (closι (π w) ≫ p) σ → ℝ := fun y => f (ptMap (closι (π w)) rfl σ y)
  have hf' : Measurable f' := hf.comp (PtsOver.continuous_map _ _ _).measurable

  have h1 : (closι w ≫ π) ≫ p = closι w ≫ q := by rw [Category.assoc, hπ]
  have h2 : (g ≫ closι (π w)) ≫ p = closι w ≫ q := by rw [Category.assoc, hgp]
  have hpart : ∀ ε : ℤˣ, part (fun i => ((L i).pull π hπ).pull (closι w) rfl) ε = part (fun i => (L' i).pull g hgp) ε := by
    intro ε
    have c1 := (GlobalTheory.Mix.isom_calculus F X Y p q σ π hπ).2.2.2.2.2 (clos w) (closι w ≫ q) (closι w) rfl h1
    have c2 := (GlobalTheory.Mix.isom_calculus F X (clos (π w)) p (closι (π w) ≫ p) σ (closι (π w)) rfl).2.2.2.2.2 (clos w)
      (closι w ≫ q) g hgp h2
    have e1 := GlobalTheory.Mix.part_eq_of_isom F (clos w) (closι w ≫ q) σ hpY e _ _ (fun i => c1 (L i)) ε
    have e2 := GlobalTheory.Mix.part_eq_of_isom F (clos w) (closι w ≫ q) σ hpY e _ _ (fun i => c2 (L i)) ε
    rw [e1, e2]
    congr 1
    funext i
    exact pull_congr _ hg.symm _ _
  have hfun : (fun y => (fun y => f (ptMap π hπ σ y)) (ptMap (closι w) rfl σ y)) = fun y => f' (ptMap g hgp σ y) := by
    funext y
    show f _ = f _
    congr 1
    apply Subtype.ext
    simp only [PtsOver.map_val, Category.assoc, hg]
  have hint : cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w =
      Mix.int (fun i => (L' i).pull g hgp) (fun y => f' (ptMap g hgp σ y)) := by
    simp only [cycInt, Mix.int]
    rw [hfun, hpart 1, hpart (-1)]
  refine ⟨fun hX => ?_, fun hX => ?_⟩
  · have hdX : topologicalKrullDim (clos (π w)) = e := hdx.trans hX
    have hne := GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint F (clos (π w)) (clos w)
      (closι (π w) ≫ p) (closι w ≫ q) e hpX hpY hdX hdY g hgp hgg
    have hpush := (GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) σ e hpX hdX hpY g hgp
      hgg hne L' f' hf').2
    have hdeg : g.residueDegree (genericPoint (clos w)) = π.residueDegree w := by
      rw [hgdeg, GlobalTheory.CurveDegreesCompare.residueDegree_comp, GlobalTheory.ProperCut.residueDegree_of_isClosedImmersion (closι w),
        mul_one, hgw]
    rw [hint, hpush, hdeg]
    rfl
  · obtain ⟨m, hm, hdX⟩ := dim_le_of_dominant F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) hpX hpY g hgp
      hgg e hdY
    have hlt : m < e := lt_of_le_of_ne hm fun h => hX (by rw [← hdx, hdX, h])
    have h0 := GlobalTheory.T.mixedChernMeasure_pullback_eq_zero_of_lt_dim F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) σ e m hlt hpX hdX hpY g hgp hgg L'
    rw [hint]
    simp only [Mix.int, h0, integral_zero_measure, sub_zero]

end GlobalTheory.CycPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosurePullbackStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernIntegral_pointClosure_pullback : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (e : ℕ) (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∀ w : Y, topologicalKrullDim (closure ({w} : Set Y)) = e → (topologicalKrullDim (closure ({π w} : Set X)) = e → cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = π.residueDegree w * cycInt L f (π w)) ∧ (topologicalKrullDim (closure ({π w} : Set X)) ≠ e → cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = 0) := by
  first | exact @GlobalTheory.CycPush.cycInt_pull | exact GlobalTheory.CycPush.cycInt_pull | (intros; apply GlobalTheory.CycPush.cycInt_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDivisorIntegralPushforward
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem finsum_weighted_regroup_along_fibres {A B : Type} (π : A → B) (m : A → ℤ) (n : B → ℤ) (d : A → ℕ) (g : A → ℝ) (h : B → ℝ)
    (P : B → Prop) (hm : (Function.support m).Finite) (hn : (Function.support n).Finite)
    (hP : ∀ z, n z ≠ 0 → P z) (hs : ∀ z, P z → ∑ᶠ (w : A) (_ : π w = z), m w * (d w : ℤ) = n z)
    (h₁ : ∀ w, m w ≠ 0 → P (π w) → g w = d w * h (π w)) (h₀ : ∀ w, m w ≠ 0 → ¬ P (π w) → g w = 0) :
    ∑ᶠ w, (m w : ℝ) * g w = ∑ᶠ z, (n z : ℝ) * h z := by
  classical
  set S := hm.toFinset with hS
  set T := hn.toFinset ∪ S.image π with hT
  have hmS : ∀ w, m w ≠ 0 ↔ w ∈ S := fun w => by simp [hS]
  rw [finsum_eq_sum_of_support_subset (s := S) _ (fun w hw => by
      have : m w ≠ 0 := fun h0 => hw (by simp [h0])
      exact Finset.mem_coe.2 ((hmS w).1 this)),
    finsum_eq_sum_of_support_subset (s := T) _ (fun z hz => by
      have : n z ≠ 0 := fun h0 => hz (by simp [h0])
      simp [hT, this]),
    ← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := π) (fun w hw => by
      simp only [hT, Finset.mem_union]; exact Or.inr (Finset.mem_image_of_mem _ hw))]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : P z
  · have e : ∑ᶠ (w : A) (_ : π w = z), m w * (d w : ℤ) = ∑ w ∈ S.filter (fun w => π w = z), m w * (d w : ℤ) := by
      refine finsum_mem_eq_sum_of_inter_support_eq (s := {w | π w = z}) _ ?_
      ext w
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, Finset.coe_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨(hmS w).1 (left_ne_zero_of_mul h2), h1⟩, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1.2, h2⟩
    rw [← hs z hz, e]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨hw', rfl⟩ := Finset.mem_filter.1 hw
    rw [h₁ w ((hmS w).2 hw') hz, mul_assoc]
  · have e : n z = 0 := by
      by_contra h'
      exact hz (hP z h')
    rw [e, Int.cast_zero, zero_mul]
    refine Finset.sum_eq_zero fun w hw => ?_
    obtain ⟨hw', rfl⟩ := Finset.mem_filter.1 hw
    rw [h₀ w ((hmS w).2 hw') hz, mul_zero]

theorem finsum_cycInt_push : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → IsProjOver q → topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv Y), (∀ z : X, Order.coheight z = 1 → ∑ᶠ (w : Y) (_ : π w = z), Δ'.mult w * (π.residueDegree w : ℤ) = Δ.mult z) → ∀ (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∑ᶠ w, (Δ'.mult w : ℝ) * cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L f z := by
  intro F _ X Y _ _ _ _ p q σ e hp hX hq hY π hπ _ Δ Δ' hΔ L f hf
  have hc : ∀ {Z : Scheme.{0}} {s : Z ⟶ Sp F}, IsProjOver s → CompactSpace Z := by
    rintro Z _ ⟨m, i, hi, rfl⟩
    have := isProper_str F m
    have : IsProper (i ≫ PSpace.str F m) := inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str F m)
  haveI := hc hp
  haveI := hc hq
  have key := fun (w : Y) (hw : Δ'.mult w ≠ 0) => GlobalTheory.T.mixedChernIntegral_pointClosure_pullback F X Y p q σ hp hq π hπ e L f hf w
    ((GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F Y q e hq hY w).1 (CartierDiv.coheight_eq_one_of_mult_ne_zero (D := Δ') hw))
  exact finsum_weighted_regroup_along_fibres π Δ'.mult Δ.mult (fun w => π.residueDegree w) _ _ (fun z => Order.coheight z = 1)
    Δ'.finite_support_mult Δ.finite_support_mult
    (fun z hz => CartierDiv.coheight_eq_one_of_mult_ne_zero (D := Δ) hz) hΔ
    (fun w hw h => (key w hw).1 ((GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hX _).1 h))
    (fun w hw h => (key w hw).2 fun h' => h ((GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hX _).2 h'))

end GlobalTheory.Mix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDivisorIntegralPushforwardStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_divisorIntegral_pushforward : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → IsProjOver q → topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv Y), (∀ z : X, Order.coheight z = 1 → ∑ᶠ (w : Y) (_ : π w = z), Δ'.mult w * (π.residueDegree w : ℤ) = Δ.mult z) → ∀ (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∑ᶠ w, (Δ'.mult w : ℝ) * cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L f z := by
  first | exact @GlobalTheory.Mix.finsum_cycInt_push | exact GlobalTheory.Mix.finsum_cycInt_push | (intros; apply GlobalTheory.Mix.finsum_cycInt_push <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFiniteRestrictNearCodimOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFiniteRestrictNearCodimOne
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FiniteNearCodimOne

theorem le_one_of_add_eq {c : ℕ∞} {s t : WithBot ℕ∞} {D : ℕ} (h₁ : (c : WithBot ℕ∞) + s = D)
    (h₂ : ((1 : ℕ∞) : WithBot ℕ∞) + t = D) (hts : t ≤ s) : c ≤ 1 := by
  induction t using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at h₂; exact absurd h₂.symm (WithBot.natCast_ne_bot _)
  | coe t =>
    have h₃ : (c : WithBot ℕ∞) + t ≤ ((1 : ℕ∞) : WithBot ℕ∞) + t :=
      (add_le_add le_rfl hts).trans (h₁.trans h₂.symm).le
    have h₄ : 1 + t = (D : ℕ∞) := by exact_mod_cast h₂
    have ht : t ≠ ⊤ := by rintro rfl; rw [add_top] at h₄; exact ENat.natCast_ne_top _ h₄.symm
    have h₅ : c + t ≤ 1 + t := by exact_mod_cast h₃
    exact (ENat.add_le_add_iff_right ht).1 h₅

theorem coheight_eq_zero_iff {X : Scheme.{0}} [IsIntegral X] (x : X) :
    Order.coheight x = 0 ↔ x = genericPoint X := by
  rw [Order.coheight_eq_zero]
  constructor
  · intro h
    have h' : x ⤳ genericPoint X := h (show x ≤ genericPoint X from genericPoint_specializes x)
    exact (h'.antisymm (genericPoint_specializes x)).eq
  · rintro rfl b _
    exact genericPoint_specializes b

theorem exists_isFinite_restrict_of_coheight_eq_one : ∀ (F : Type) [Field F] (X Y : Scheme.{0})
    [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (D : ℕ), IsProjOver p →
    topologicalKrullDim X = (D : ℕ) → IsProjOver q → topologicalKrullDim Y = D →
    ∀ π : Y ⟶ X, π ≫ p = q → π (genericPoint Y) = genericPoint X → ∀ z : X,
    Order.coheight z = 1 → ∃ U : X.Opens, z ∈ U ∧ IsFinite (π ∣_ U) := by
  intro F _ X Y _ _ p q D hp hX hq hY π hπ hη z hz
  have : IsProper p := by
    obtain ⟨N, c, hc, rfl⟩ := hp
    have := isProper_str F N
    infer_instance
  have : IsProper q := by
    obtain ⟨N, c, hc, rfl⟩ := hq
    have := isProper_str F N
    infer_instance
  have : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π p
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian Y := {}
  have hzne : z ≠ genericPoint X := fun h => by
    rw [(coheight_eq_zero_iff z).2 h] at hz
    exact zero_ne_one hz
  have hw : ∀ w : Y, π w = z → Order.coheight w = 1 := by
    intro w hwz
    have h₁ := (FieldDimCoheight.coheight_add_dim_closure_eq F Y q w).trans hY
    have h₂ := (FieldDimCoheight.coheight_add_dim_closure_eq F X p z).trans hX
    rw [hz] at h₂
    have h₃ := PosBaseChange.dim_image_le π.isClosedMap (isClosed_closure (s := ({w} : Set Y)))
    rw [← π.isClosedMap.closure_image_eq_of_continuous π.continuous, Set.image_singleton, hwz] at h₃
    refine le_antisymm (le_one_of_add_eq h₁ h₂ h₃) (Order.one_le_iff_ne_zero.2 fun h0 => ?_)
    rw [(coheight_eq_zero_iff w).1 h0] at hwz
    exact hzne (hwz.symm.trans hη)
  have hfin : (π ⁻¹' {z}).Finite := by
    let U : Y.Opens := π ⁻¹ᵁ ⟨(closure ({z} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
    have hU : genericPoint Y ∈ U := by
      show π (genericPoint Y) ∈ (closure ({z} : Set X))ᶜ
      rw [hη]
      intro hc
      exact hzne ((specializes_iff_mem_closure.2 hc).antisymm (genericPoint_specializes z)).eq
    refine (Mix.finite_coheight_one_notMem_open Y U hU).subset fun w hwz => ⟨hw w hwz, fun hwU => ?_⟩
    have hwU' : π w ∈ (closure ({z} : Set X))ᶜ := hwU
    exact hwU' (by rw [show π w = z from hwz]; exact subset_closure rfl)
  exact exists_isFinite_morphismRestrict_of_finite_preimage_singleton π z hfin

end GlobalTheory.FiniteNearCodimOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFiniteRestrictNearCodimOneStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isFinite_restrict_near_codimOne : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → IsProjOver q → topologicalKrullDim Y = D → ∀ π : Y ⟶ X, π ≫ p = q → π (genericPoint Y) = genericPoint X → ∀ z : X, Order.coheight z = 1 → ∃ U : X.Opens, z ∈ U ∧ IsFinite (π ∣_ U) := by
  first | exact @GlobalTheory.FiniteNearCodimOne.exists_isFinite_restrict_of_coheight_eq_one | exact GlobalTheory.FiniteNearCodimOne.exists_isFinite_restrict_of_coheight_eq_one | (intros; apply GlobalTheory.FiniteNearCodimOne.exists_isFinite_restrict_of_coheight_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdPullbackMulResidueDegreeCodimOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdPullbackMulResidueDegreeCodimOne
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.OrdPush

theorem ord_ringEquiv {T T' : Type*} [CommRing T] [CommRing T'] (e : T ≃+* T') (x : T) :
    Ring.ord T' (e x) = Ring.ord T x := by
  let _ : Algebra T T' := e.toRingHom.toAlgebra
  let e' : T ≃ₐ[T] T' := { e with commutes' := fun _ => rfl }
  unfold Ring.ord
  rw [← Module.length_eq_of_surjective (S := T) (R := T') e.surjective]
  refine (Ideal.quotientEquivAlg (Ideal.span {x}) (Ideal.span {e x}) e' ?_).toLinearEquiv.length_eq.symm
  rw [Ideal.map_span, Set.image_singleton]
  rfl

theorem ord_isLocalization {S : Type*} [CommRing S] (M : Submonoid S) (T T' : Type*) [CommRing T]
    [CommRing T'] [Algebra S T] [Algebra S T'] [IsLocalization M T] [IsLocalization M T'] (s : S) :
    Ring.ord T' (algebraMap S T' s) = Ring.ord T (algebraMap S T s) := by
  rw [← (IsLocalization.algEquiv M T T').commutes s]
  exact ord_ringEquiv (IsLocalization.algEquiv M T T').toRingEquiv _

theorem inertiaDeg_isLocalization {S : Type*} [CommRing S] (M : Submonoid S) (B : Type*)
    [CommRing B] [Algebra S B] [IsLocalization M B] (Q : Ideal B) [Q.IsPrime] :
    Q.inertiaDeg S = 1 := by
  rw [ResidueDegreeChart.inertiaDeg_eq_finrank_of_ker (K := Q.ResidueField) (L := Q.ResidueField)
    ((algebraMap B Q.ResidueField).comp (algebraMap S B)) (algebraMap B Q.ResidueField) Q
    (fun s => Ideal.algebraMap_residueField_eq_zero.symm) ?_ ?_ (fun _ => rfl), Module.finrank_self]
  · intro z
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B ⧸ Q) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨⟨a₁, a₂⟩, ha⟩ := IsLocalization.surj M a
    obtain ⟨⟨b₁, b₂⟩, hb⟩ := IsLocalization.surj M b
    have h₁ := ((IsLocalization.map_units B a₂).map (algebraMap B Q.ResidueField)).ne_zero
    have h₂ := ((IsLocalization.map_units B b₂).map (algebraMap B Q.ResidueField)).ne_zero
    refine ⟨a₁ * b₂, b₁ * a₂, ?_⟩
    simp only [RingHom.comp_apply, map_mul] at ha hb ⊢
    rw [← ha, ← hb, map_mul, map_mul, mul_assoc, mul_assoc, mul_comm (algebraMap B _ (algebraMap S B b₂)),
      mul_div_mul_right _ _ (mul_ne_zero h₁ h₂)]
    rfl
  · intro z
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B ⧸ Q) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨a, b, rfl⟩

theorem finsum_ord_mul_inertiaDeg (R S A : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] (hinj : Function.Injective (algebraMap R S))
    (p : PrimeSpectrum R) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Algebra R A] [IsLocalization.AtPrime A p.asIdeal] (hdim : ringKrullDim A = 1)
    (a : R) (ha : a ≠ 0) :
    ∑ᶠ Q ∈ {Q : PrimeSpectrum S | PrimeSpectrum.comap (algebraMap R S) Q = p},
      ((Ring.ord (Localization.AtPrime Q.asIdeal)
        (algebraMap S _ (algebraMap R S a))).toNat : ℤ) * (Q.asIdeal.inertiaDeg R : ℤ) =
      (Module.finrank R S : ℤ) * ((Ring.ord A (algebraMap R A a)).toNat : ℤ) := by
  let M := Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl
  let B := Localization M
  have hp0 : p.asIdeal.primeCompl ≤ nonZeroDivisors R := p.asIdeal.primeCompl_le_nonZeroDivisors
  have hM0 : M ≤ nonZeroDivisors S := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero (hp0 hr)))
  have : IsDomain B := IsLocalization.isDomain_localization hM0
  let _ : Algebra A B := localizationAlgebra p.asIdeal.primeCompl S
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R S B]
    exact (IsLocalization.map_eq (T := M) (S := A) (Q := B) _ r).symm
  have : Module.Finite A B := Module.Finite.of_isLocalization R S p.asIdeal.primeCompl
  have hAB : Function.Injective (algebraMap A B) := localizationAlgebra_injective A B hinj
  have ha' : algebraMap R A a ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective A hp0)).2 ha
  have hdeg : ∀ Q : PrimeSpectrum B,
      Q.asIdeal.inertiaDeg A = (Q.asIdeal.under S).inertiaDeg R := fun Q => by
    have h₁ := Ideal.inertiaDeg_tower (R := R) (Q.asIdeal.under S) Q.asIdeal
    have h₂ := Ideal.inertiaDeg_tower (R := R) (Q.asIdeal.under A) Q.asIdeal
    rw [inertiaDeg_isLocalization M B, mul_one] at h₁
    rw [inertiaDeg_isLocalization p.asIdeal.primeCompl A, one_mul] at h₂
    exact h₂.symm.trans h₁
  have hrk : Module.finrank A B = Module.finrank R S := by
    rw [← inertiaDeg_bot_eq_finrank A B hAB, ← inertiaDeg_bot_eq_finrank R S hinj]
    refine (hdeg ⊥).trans ?_
    congr 1
    exact Ideal.comap_bot_of_injective _ (IsLocalization.injective B hM0)
  rw [← hrk, ← finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord A B hAB hdim _ ha']
  symm
  have hmax : (IsLocalRing.maximalIdeal A).comap (algebraMap R A) = p.asIdeal :=
    IsLocalization.AtPrime.under_maximalIdeal A p.asIdeal
  have hsq : ∀ Q : PrimeSpectrum B,
      PrimeSpectrum.comap (algebraMap R S) (PrimeSpectrum.comap (algebraMap S B) Q) =
      PrimeSpectrum.comap (algebraMap R A) (PrimeSpectrum.comap (algebraMap A B) Q) := fun Q => by
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  refine finsum_mem_eq_of_bijOn (PrimeSpectrum.comap (algebraMap S B)) ⟨?_, ?_, ?_⟩ ?_
  · intro Q hQ
    change _ = p
    rw [hsq]
    ext1
    rw [← hmax, ← show Q.asIdeal.comap (algebraMap A B) = _ from hQ]
    rfl
  · exact (PrimeSpectrum.localization_comap_injective B M).injOn
  · intro Q hQ
    have hQ' : PrimeSpectrum.comap (algebraMap R S) Q = p := hQ
    have : Q ∈ Set.range (PrimeSpectrum.comap (algebraMap S B)) := by
      rw [PrimeSpectrum.localization_comap_range B M]
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨r, hr, rfl⟩ h
      exact hr (by rw [← hQ']; exact h)
    obtain ⟨Q', rfl⟩ := this
    refine ⟨Q', ?_, rfl⟩
    have := PrimeSpectrum.localization_comap_injective A p.asIdeal.primeCompl
      (a₁ := PrimeSpectrum.comap (algebraMap A B) Q') (a₂ := IsLocalRing.closedPoint A)
      (by rw [← hsq, hQ']; ext1; exact hmax.symm)
    exact congrArg PrimeSpectrum.asIdeal this
  · intro Q _
    rw [hdeg]
    congr 3
    have : IsLocalization.AtPrime (Localization.AtPrime Q.asIdeal)
        (PrimeSpectrum.comap (algebraMap S B) Q).asIdeal :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime Q.asIdeal) Q.asIdeal
    rw [← IsScalarTower.algebraMap_apply R A B, IsScalarTower.algebraMap_apply R S B,
      ← IsScalarTower.algebraMap_apply S B]
    exact ord_isLocalization (PrimeSpectrum.comap (algebraMap S B) Q).asIdeal.primeCompl _ _ _

theorem height_eq_one {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (Q : PrimeSpectrum S) (h : (PrimeSpectrum.comap (algebraMap R S) Q).asIdeal.height = 1) :
    Q.asIdeal.height = 1 := by
  refine le_antisymm ?_ ?_
  · rw [← h, PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.height_eq_orderHeight]
    exact Order.height_le_height_apply_of_strictMono _
      (fun a b hab => Ideal.IsIntegral.comap_lt_comap (R := R) (I := a.asIdeal) hab) Q
  · rw [Order.one_le_iff_ne_zero]
    intro h0
    have hQ : Q.asIdeal = ⊥ := Ideal.height_eq_zero_iff_eq_bot.1 h0
    rw [PrimeSpectrum.comap_asIdeal, hQ, Ideal.comap_bot_of_injective _ hinj, Ideal.height_bot] at h
    exact zero_ne_one h

theorem coheight_eq_height {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (x : X)
    (hx : x ∈ V) : Order.coheight x = (hV.primeIdealOf ⟨x, hx⟩).asIdeal.height := by
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  have h := IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf ⟨x, hx⟩).asIdeal
    (X.presheaf.stalk x)
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

theorem ord_fnOf {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {V : X.Opens}
    (hV : IsAffineOpen V) (x : X) (hx : x ∈ V) (h1 : Order.coheight x = 1) (a : Γ(X, V))
    (ha : a ≠ 0) : Scheme.ord (fnOf V (gen_mem hx) a) x =
      (Ring.ord (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal)
        (algebraMap Γ(X, V) _ a)).toNat := by
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  rw [← algebraMap_germ hx, ord_algebraMap h1
    ((map_ne_zero_iff _ (germ_injective_of_isIntegral X x hx)).2 ha),
    ord_isLocalization (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x)]
  rfl

theorem exists_affine {X Y : Scheme.{0}} (π : Y ⟶ X) (z : X) (U : X.Opens) (hz : z ∈ U)
    [IsFinite (π ∣_ U)] : ∃ V : X.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen (π ⁻¹ᵁ V) ∧
      (π.app V).hom.Finite := by
  obtain ⟨_, ⟨V', hV', rfl⟩, hzV, -⟩ := (U : Scheme.{0}).isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (⟨z, hz⟩ : U)) isOpen_univ
  refine ⟨U.ι ''ᵁ V', ⟨⟨z, hz⟩, hzV, rfl⟩, hV'.image_of_isOpenImmersion _, ?_, ?_⟩
  · rw [← image_morphismRestrict_preimage]
    exact (IsAffineOpen.preimage hV' (π ∣_ U)).image_of_isOpenImmersion _
  · have h := (π ∣_ U).finite_app V' hV'
    rw [morphismRestrict_app] at h
    exact (RingHom.finite_respectsIso.cancel_right_isIso _ _).1 h

theorem finsum_ord_fnOf {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (π : Y ⟶ X) (hη : π (genericPoint Y) ⤳ genericPoint X) (z : X)
    (h1 : Order.coheight z = 1) (V : X.Opens) (hz : z ∈ V) (hV : IsAffineOpen V)
    (hW : IsAffineOpen (π ⁻¹ᵁ V)) (hfin : (π.app V).hom.Finite) (a : Γ(X, V)) (ha : a ≠ 0) :
    ∑ᶠ w ∈ {w : Y | π w = z},
      Scheme.ord (TrueGeo.SmallSec.fnMap π hη (fnOf V (gen_mem hz) a)) w *
        (π.residueDegree w : ℤ) =
      (π.residueDegree (genericPoint Y) : ℤ) * Scheme.ord (fnOf V (gen_mem hz) a) z := by
  have hgen : genericPoint Y ∈ π ⁻¹ᵁ V := hη.mem_open V.isOpen (gen_mem hz)
  have : Nonempty V := ⟨⟨z, hz⟩⟩
  have : Nonempty (π ⁻¹ᵁ V : Y.Opens) := ⟨⟨_, hgen⟩⟩
  let _ : Algebra Γ(X, V) Γ(Y, π ⁻¹ᵁ V) := (π.app V).hom.toAlgebra
  have : Module.Finite Γ(X, V) Γ(Y, π ⁻¹ᵁ V) := hfin
  have hinj : Function.Injective (algebraMap Γ(X, V) Γ(Y, π ⁻¹ᵁ V)) := by
    intro s t hst
    apply germ_injective_of_isIntegral X (genericPoint X) (gen_mem hz)
    apply (TrueGeo.SmallSec.fnMap π hη).injective
    exact (TrueGeo.SmallSec.fnMap_fnOf π hη _ hgen s).trans
      ((congrArg (fnOf _ hgen) hst).trans (TrueGeo.SmallSec.fnMap_fnOf π hη _ hgen t).symm)
  have hcomap : ∀ (w : Y) (hw : w ∈ π ⁻¹ᵁ V),
      PrimeSpectrum.comap (algebraMap Γ(X, V) Γ(Y, π ⁻¹ᵁ V)) (hW.primeIdealOf ⟨w, hw⟩) =
        hV.primeIdealOf ⟨π w, hw⟩ := fun w hw => by
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := π) V hV _ hW le_rfl hw
    rwa [Scheme.Hom.appLE_eq_app] at h
  have hp1 : (hV.primeIdealOf ⟨z, hz⟩).asIdeal.height = 1 := by
    rw [← coheight_eq_height, h1]
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have key := finsum_ord_mul_inertiaDeg Γ(X, V) Γ(Y, π ⁻¹ᵁ V)
    (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal) hinj (hV.primeIdealOf ⟨z, hz⟩)
    (by rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf ⟨z, hz⟩).asIdeal, hp1]; rfl)
    a ha
  have hrk : π.residueDegree (genericPoint Y) = Module.finrank Γ(X, V) Γ(Y, π ⁻¹ᵁ V) := by
    rw [ResidueDegreeChart.residueDegree_eq_inertiaDeg X Y π V hV hW _ hgen,
      ← inertiaDeg_bot_eq_finrank _ _ hinj]
    congr 1
    rw [hW.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    rfl
  rw [hrk, ord_fnOf hV z hz h1 a ha, ← key, TrueGeo.SmallSec.fnMap_fnOf π hη _ hgen]
  symm
  have hmem : ∀ Q : PrimeSpectrum Γ(Y, π ⁻¹ᵁ V), hW.fromSpec Q ∈ π ⁻¹ᵁ V := fun Q => by
    have : hW.fromSpec Q ∈ Set.range hW.fromSpec := ⟨Q, rfl⟩
    rwa [hW.range_fromSpec] at this
  have hinv : ∀ Q : PrimeSpectrum Γ(Y, π ⁻¹ᵁ V), hW.primeIdealOf ⟨_, hmem Q⟩ = Q := fun Q =>
    hW.fromSpec.isOpenEmbedding.injective (hW.fromSpec_primeIdealOf _)
  refine finsum_mem_eq_of_bijOn (fun Q => hW.fromSpec Q) ⟨?_, ?_, ?_⟩ ?_
  · intro Q hQ
    have h := hcomap _ (hmem Q)
    rw [hinv, show PrimeSpectrum.comap _ Q = _ from hQ] at h
    have h' := congrArg (fun q => hV.fromSpec q) h
    simp only [hV.fromSpec_primeIdealOf] at h'
    exact h'.symm
  · exact hW.fromSpec.isOpenEmbedding.injective.injOn
  · intro w hw
    have hw' : π w = z := hw
    subst hw'
    exact ⟨hW.primeIdealOf ⟨w, hz⟩, hcomap w hz, hW.fromSpec_primeIdealOf _⟩
  · intro Q hQ
    have hc : Order.coheight (hW.fromSpec Q) = 1 := by
      rw [coheight_eq_height hW _ (hmem Q), hinv]
      exact height_eq_one hinj Q (by rw [show PrimeSpectrum.comap _ Q = _ from hQ, hp1])
    have h₁ := ord_fnOf hW _ (hmem Q) hc (algebraMap Γ(X, V) _ a) ((map_ne_zero_iff _ hinj).2 ha)
    have h₂ := ResidueDegreeChart.residueDegree_eq_inertiaDeg X Y π V hV hW _ (hmem Q)
    rw [hinv] at h₁ h₂
    rw [h₂]
    exact congrArg (· * _) h₁.symm

theorem finite_fibre {X Y : Scheme.{0}} (π : Y ⟶ X) (z : X) (U : X.Opens) (hz : z ∈ U)
    [IsFinite (π ∣_ U)] : {w : Y | π w = z}.Finite := by
  have h := (π ∣_ U).finite_preimage_singleton ⟨z, hz⟩
  refine (h.image (π ⁻¹ᵁ U).ι).subset ?_
  intro w hw
  have hw' : π w = z := hw
  subst hw'
  exact ⟨⟨w, hz⟩, Subtype.ext (morphismRestrict_base_coe π U ⟨w, hz⟩), rfl⟩

theorem finsum_ord_fnMap_mul_residueDegree : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (π : Y ⟶ X) (hη : π (genericPoint Y) ⤳ genericPoint X) (z : X), Order.coheight z = 1 → (∃ U : X.Opens, z ∈ U ∧ IsFinite (π ∣_ U)) → ∀ f : X.functionField, f ≠ 0 → ∑ᶠ (w : Y) (_ : π w = z), Scheme.ord (TrueGeo.SmallSec.fnMap π hη f) w * (π.residueDegree w : ℤ) = (π.residueDegree (genericPoint Y) : ℤ) * Scheme.ord f z := by
  rintro X Y _ _ _ _ π hη z h1 ⟨U, hU, hfin⟩ f hf
  obtain ⟨V, hz, hV, hW, hF⟩ := exists_affine π z U hU
  have : Nonempty V := ⟨⟨z, hz⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, V)) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : fnOf V (gen_mem hz) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Γ(X, V) X.functionField)).2 hb0
  have e : fnOf V (gen_mem hz) a = f * fnOf V (gen_mem hz) b :=
    (div_eq_iff hb').1 hab
  have ha0 : a ≠ 0 := fun h => mul_ne_zero hf hb' (by rw [← e, h, map_zero])
  have h₁ := finsum_ord_fnOf π hη z h1 V hz hV hW hF a ha0
  have h₂ := finsum_ord_fnOf π hη z h1 V hz hV hW hF b hb0
  have hi := (TrueGeo.SmallSec.fnMap π hη).injective
  have hf' := (map_ne_zero_iff _ hi).2 hf
  have hb'' := (map_ne_zero_iff _ hi).2 hb'
  rw [e, map_mul] at h₁
  simp only [Scheme.ord_mul hf hb', Scheme.ord_mul hf' hb'',
    add_mul, mul_add] at h₁
  rw [finsum_mem_add_distrib (finite_fibre π z U hU), h₂] at h₁
  exact add_right_cancel h₁

end GlobalTheory.OrdPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdPullbackMulResidueDegreeCodimOneStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_ord_pullback_mul_residueDegree_codim_one : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (π : Y ⟶ X) (hη : π (genericPoint Y) ⤳ genericPoint X) (z : X), Order.coheight z = 1 → (∃ U : X.Opens, z ∈ U ∧ IsFinite (π ∣_ U)) → ∀ f : X.functionField, f ≠ 0 → ∑ᶠ (w : Y) (_ : π w = z), Scheme.ord (TrueGeo.SmallSec.fnMap π hη f) w * (π.residueDegree w : ℤ) = (π.residueDegree (genericPoint Y) : ℤ) * Scheme.ord f z := by
  first | exact @GlobalTheory.OrdPush.finsum_ord_fnMap_mul_residueDegree | exact GlobalTheory.OrdPush.finsum_ord_fnMap_mul_residueDegree | (intros; apply GlobalTheory.OrdPush.finsum_ord_fnMap_mul_residueDegree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLelongFormulaSectionProjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory

theorem poincareLelong_sec : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), 2 * Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) = ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L u z - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
  intro hP F _ X _ _ p σ e hX hdim L M s hs u hu
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hYi, π, hsm, hproj, hdimY, hgen, hdeg, hsnc⟩ :=
    GlobalTheory.T.exists_logResolution_projective_of_principalisation hP F X p (e + 1) hX hdim (nonzeroLocus s).compl (fun h => h hs)
  haveI := hYi
  haveI : IsLocallyNoetherian Y := by
    haveI := SmoothOfRelativeDimension.smooth (e + 1) (π ≫ p)
    exact LocallyOfFiniteType.isLocallyNoetherian (π ≫ p)
  have hη : π (genericPoint Y) ⤳ genericPoint X := by rw [hgen]
  obtain ⟨s', hnz, hnsq, hmult⟩ := GlobalTheory.T.exists_pullback_section_zeros_norm_multiplicities F X Y p (π ≫ p) σ π rfl M s
  have hs' : genericPoint Y ∈ nonzeroLocus s' := by
    rw [hnz]; show π (genericPoint Y) ∈ nonzeroLocus s; rw [hgen]; exact hs
  have hsnc' : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (nonzeroLocus s').compl) := by
    convert hsnc using 2
    ext x
    simp [hnz]
  have hPL := GlobalTheory.T.poincareLelong_normalCrossings_smoothProjective F Y (π ≫ p) σ e hproj hsm (fun i => (L i).pull π rfl) (M.pull π rfl) s' hs' hsnc'
    (fun y => u (ptMap π rfl σ y)) (fun z => (hu _).pull π rfl)
  have hmu : Measurable u := (continuous_iff_continuousAt.2 fun y => (hu y).continuousAt).measurable
  have hml : Measurable (M.logSec s) := (GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties F X p σ M s).1
  have hiso := GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus F X Y p (π ≫ p) σ π rfl
  have hrefl := (GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus F Y Y (π ≫ p) (π ≫ p) σ (𝟙 Y) (Category.id_comp _)).1
  have hdeg' : π.residueDegree (genericPoint Y) ≠ 0 := by rw [hdeg]; exact one_ne_zero
  have intEq : ∀ (A B : Fin (e + 1) → MLine (π ≫ p) σ), (∀ i, (A i).Isom (B i)) → ∀ f, Mix.int A f = Mix.int B f := by
    intro A B h f
    simp only [Mix.int, GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver F Y (π ≫ p) σ hproj (e + 1) A B h]
  have hlog : (M.pull π rfl).logSec s' = fun y => M.logSec s (ptMap π rfl σ y) := by
    funext y; simp only [MLine.logSec, hnsq]

  have hA : Mix.int (Fin.cons (MLine.ofFun (fun y => u (ptMap π rfl σ y)) (fun z => (hu _).pull π rfl)) (fun i => (L i).pull π rfl) : Fin (e + 1) → MLine (π ≫ p) σ) ((M.pull π rfl).logSec s')
      = Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) := by
    rw [hlog, ← intEq (fun i => ((Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) i).pull π rfl)]
    · rw [(GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ (e + 1) hX hdim hproj π rfl hgen hdeg' _ _ hml).2, hdeg]
      simp
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hiso.2.2.2.1 u hu
      · simpa using hrefl ((L j).pull π rfl)
  have hB : Mix.int (Fin.cons (M.pull π rfl) (fun i => (L i).pull π rfl) : Fin (e + 1) → MLine (π ≫ p) σ) (fun y => u (ptMap π rfl σ y))
      = Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
    rw [← intEq (fun i => ((Fin.cons M L : Fin (e + 1) → MLine p σ) i).pull π rfl)]
    · rw [(GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ (e + 1) hX hdim hproj π rfl hgen hdeg' _ _ hmu).2, hdeg]
      simp
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hrefl (M.pull π rfl)
      · simpa using hrefl ((L j).pull π rfl)
  have hS := GlobalTheory.T.finsum_divisorIntegral_pushforward F X Y p (π ≫ p) σ e hX hdim hproj hdimY π rfl hgen
    (divOfSec M.φ.isLB s hs) (divOfSec (M.pull π rfl).φ.isLB s' hs') (by
      intro z hz
      obtain ⟨i, hi⟩ := exists_chart M.φ.isLB z
      have hfin := GlobalTheory.T.exists_isFinite_restrict_near_codimOne F X Y p (π ≫ p) (e + 1) hX hdim hproj hdimY π rfl hgen z hz
      have hord := GlobalTheory.T.finsum_ord_pullback_mul_residueDegree_codim_one X Y π hη z hz hfin (ratOfSec s hs i : X.functionField) (Units.ne_zero _)
      calc _ = ∑ᶠ (w : Y) (_ : π w = z), Scheme.ord (TrueGeo.SmallSec.fnMap π hη (ratOfSec s hs i : X.functionField)) w * (π.residueDegree w : ℤ) :=
            finsum_congr fun w => finsum_congr fun hw => by
              rw [hmult hη hs hs' w i (hw ▸ hi)]
        _ = _ := hord
        _ = _ := by
          rw [hdeg, Nat.cast_one, one_mul, ((presents_divOfRatSec M.φ.isLB _).isEqn i z hi).mult_eq])
    L u hmu
  rw [hA, hB, hS] at hPL
  exact hPL

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLelongFormulaSectionProjectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareLelong_formula_section_projective : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), 2 * Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) = ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L u z - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
  first | exact @GlobalTheory.poincareLelong_sec | exact GlobalTheory.poincareLelong_sec | (intros; apply GlobalTheory.poincareLelong_sec <;> assumption)
end
