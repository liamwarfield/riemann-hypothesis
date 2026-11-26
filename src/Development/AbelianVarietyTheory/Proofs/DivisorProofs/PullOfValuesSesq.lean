module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystalline
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOfValuesSesq
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

open scoped ComplexConjugate

namespace GlobalTheory.SecForm

theorem coordVec_expand {n : ℕ} (w : V n) : w = ∑ a, w a • coordVec a := by
  ext i
  simp [coordVec, Pi.single_apply]

theorem sesq_sum_left {n : ℕ} {α : V n → V n → ℂ} (hα : IsSesq α) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (x : ι → V n) (y : V n) : α (∑ i ∈ s, c i • x i) y = ∑ i ∈ s, c i * α (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hα.smul_left 0 0 y
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hα.add_left, hα.smul_left, ih, smul_eq_mul]

theorem sesq_sum_right {n : ℕ} {α : V n → V n → ℂ} (hα : IsSesq α) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (x : V n) (y : ι → V n) : α x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, conj (c i) * α x (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hα.smul_right 0 x 0
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hα.add_right, hα.smul_right, ih, smul_eq_mul]

theorem sesq_expand {n : ℕ} {α : V n → V n → ℂ} (hα : IsSesq α) (x y : V n) :
    α x y = ∑ a, ∑ b, α (coordVec a) (coordVec b) * (x a * conj (y b)) := by
  calc α x y = α (∑ a, x a • coordVec a) (∑ b, y b • coordVec b) := by
        rw [← coordVec_expand x, ← coordVec_expand y]
    _ = _ := by
        rw [sesq_sum_left (α := α) hα]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sesq_sum_right (α := α) hα, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring

theorem pull_ofValues : ∀ {n : ℕ} (L : V n →L[ℂ] V n) (α : V n → V n → ℂ), IsSesq α → pull L (ofValues α : Alt n) = ofValues (fun ξ η => α (L ξ) (L η)) := by
  intro n L α hα
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ofValues, sesq_expand hα (L _), AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, sym, map_sum,
    map_smul, map_mul, (pull_dz L _).1, (pull_dz L _).2, Finset.sum_mul, Finset.mul_sum, Finset.sum_smul,
    Finset.smul_sum, smul_mul_smul_comm, smul_smul]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, c, 2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]

end GlobalTheory.SecForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridSquareRankInequalities
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridSquareRankInequalities
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.Div.SquareRanks

theorem square_ranks : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (i j : Fin D.R.m),
    (spW₁ G i j).rank < (spW G i j).rank ∧ Even ((spW G i j).rank + (spW₁ G i j).rank) ∧
    2 * ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2) + 1 < ((spW G i j).rank - (spW₁ G i j).rank) / 2 ∧
    2 * ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2) + 1 < (spW₁ G i j).rank := by
  intro D T L sc G μ₀ hL i j
  have r : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hi := i.2
  have hj := j.2
  have e1 : (spW G i j).rank = rankV D (i + 1) (j + 1) := r _ _ (by omega) (by omega)
  have e2 : (spW₁ G i j).rank = rankV D i j := r _ _ (by omega) (by omega)
  have e3 : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  rw [e1, e2, e3]
  have h0 : D.R.r ≤ rankV D i j := by unfold rankV; omega
  have ht := D.R.t_odd
  have hk := D.R.k_even
  have hm := D.R.m_even
  have h3 := D.R.three_m_lt_t
  have h4 := D.R.m_add_three_le_k
  have h5 := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hs : sLen D = D.R.r + 6 := rfl
  obtain ⟨t', ht'⟩ := ht
  obtain ⟨k', hk'⟩ := hk
  obtain ⟨m', hm'⟩ := hm
  refine ⟨by omega, ?_, by omega, by omega⟩
  rw [Nat.even_iff]
  omega

end GlobalTheory.Div.SquareRanks
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridSquareRankInequalitiesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGridSquare_rank_inequalities : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (i j : Fin D.R.m),
    (spW₁ G i j).rank < (spW G i j).rank ∧ Even ((spW G i j).rank + (spW₁ G i j).rank) ∧
    2 * ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2) + 1 < ((spW G i j).rank - (spW₁ G i j).rank) / 2 ∧
    2 * ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2) + 1 < (spW₁ G i j).rank := by
  first | exact @GlobalTheory.Div.SquareRanks.square_ranks | exact GlobalTheory.Div.SquareRanks.square_ranks | (intros; apply GlobalTheory.Div.SquareRanks.square_ranks <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Fin

variable {n d n₁ d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d} {Y₁ : Spc F E n₁} {W₁ : Spc F E d₁}

structure IsIndMap (v : Pl F) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁) {P P₁ : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P₁] [Module ℂ P₁] (p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P)
    (p₁ : ((Fin n₁ × Fin d₁ → Fv F v) → ℂ) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (A : P →ₗ[ℂ] (UA σ W.J → P₁)) : Prop where
  right : ∀ g ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
    Acts (evFin F v) (om (1, g)) φ φ₁ → ∀ h ∈ UAt σ W (evFin F v), A (p φ₁) h = A (p φ) (h * g)
  unip : ∀ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) → ∀ x, ∀ h ∈ UAt σ W (evFin F v), A x (u * h) = A x h
  levi : ∀ (t : (AE F E)ˣ) (h₁ : UA σ W₁.J) (m : UA σ W.J), IsLevi H' t h₁ m → m ∈ UAt σ W (evFin F v) →
    h₁ ∈ UAt σ W₁ (evFin F v) → ∀ φ ∈ SB (Fin n₁ × Fin d₁ → Fv F v), ∀ φ₁ ∈ SB (Fin n₁ × Fin d₁ → Fv F v),
    Acts (evFin F v) (om₁ (1, h₁)) φ φ₁ → ∀ x, ∀ h ∈ UAt σ W (evFin F v), A x h = p₁ φ →
      A x (m * h) = ((χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)) • p₁ φ₁

def IndLineFin (v : Pl F) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁) {P P₁ : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P₁] [Module ℂ P₁] (p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P)
    (p₁ : ((Fin n₁ × Fin d₁ → Fv F v) → ℂ) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ) : Prop :=
  ∀ A A' : P →ₗ[ℂ] (UA σ W.J → P₁), IsIndMap v om om₁ p p₁ H' χ z A → IsIndMap v om om₁ p p₁ H' χ z A' →
    (∀ x, ∀ h ∈ UAt σ W (evFin F v), A x h = 0) ∨ ∃ c : ℂ, ∀ x, ∀ h ∈ UAt σ W (evFin F v), A' x h = c • A x h

end Fin

section Inf

variable {n d n₁ d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d} {Y₁ : Spc F E n₁} {W₁ : Spc F E d₁}

structure IsFrobInf (B : Base F E) (M : Model σ Y W) (M₁ : Model σ Y₁ W₁) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁)
    {P P₁ : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (p₁ : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E)
    (z : ℝ) (φ : P →ₗ[ℂ] P₁) : Prop where
  unip : ∀ γ ∈ Lines σ W, (∀ s, γ s ∈ unip σ W H') → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → φ (p f₁) = 0
  lie : ∀ γ ∈ Lines σ W, ∀ γ₁ ∈ Lines σ W₁, ∀ t : Multiplicative ℝ →* (AE F E)ˣ, (∀ s, IsLevi H' (t s) (γ₁ s) (γ s)) →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ →
    ∀ g ∈ M₁.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin n₁ × Fin d₁),
    ActsD (evI F) (fun s => om₁ (1, γ₁ (Multiplicative.ofAdd s))) g g₁ → φ (p f) = p₁ g → ∀ c : ℂ,
    HasDerivAt (fun s : ℝ => (χ (t (Multiplicative.ofAdd s)) : ℂ) *
      (((absE F E (t (Multiplicative.ofAdd s)) : ℝ) ^ z : ℝ) : ℂ)) c 0 →
      φ (p f₁) = p₁ g₁ + c • φ (p f)
  cpt : ∀ k ∈ KInf σ W B.emb, ∀ (t : (AE F E)ˣ) (k₁ : UA σ W₁.J), IsLevi H' t k₁ k → k₁ ∈ KInf σ W₁ B.emb →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ →
    ∀ g ∈ M₁.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin n₁ × Fin d₁), Acts (evI F) (om₁ (1, k₁)) g g₁ → φ (p f) = p₁ g →
      φ (p f₁) = ((χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)) • p₁ g₁

def IndLineInf (B : Base F E) (M : Model σ Y W) (M₁ : Model σ Y₁ W₁) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁)
    {P P₁ : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (p₁ : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E)
    (z : ℝ) : Prop :=
  ∀ φ φ' : P →ₗ[ℂ] P₁, IsFrobInf B M M₁ om om₁ p p₁ H' χ z φ → IsFrobInf B M M₁ om om₁ p p₁ H' χ z φ' →
    φ = 0 ∨ ∃ c : ℂ, φ' = c • φ

end Inf

end GlobalTheory.IndLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartSingleton
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchDimZero

theorem volume_univ_zero : (volume : Measure (ReciprocityTheory.L2DbarEstimates.V 0)) Set.univ = 1 := by
  have h := (stdOrthonormalBasis ℝ (ReciprocityTheory.L2DbarEstimates.V 0)).volume_parallelepiped
  rwa [Set.eq_univ_of_forall (s := parallelepiped _) fun v =>
    (Subsingleton.elim 0 v) ▸ ⟨0, by simp, by simp⟩] at h

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem exists_chart (hq : IsArithVar q 0) {σ : k →+* ℂ} (y : CxPts q σ) :
    ∃ c : AlgChart q σ 0, y ∈ c.e.source := by
  obtain ⟨U, x, hU, hg, hx⟩ := GenericEtale.exists_etale_coords hq
  have hy : y ∈ ptsIn q σ U := by
    rw [mem_ptsIn, show y.1 (IsLocalRing.closedPoint ℂ) = genericPoint Y from
      TwistTop.under_eq_genericPoint hq y]
    exact hg
  obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hU x hx hy
  exact ⟨c, hc⟩

theorem isProper (hq : IsArithVar q 0) : IsProper q := by
  obtain ⟨N, j, _, hj⟩ := hq.isProjOver
  have := isProper_str k N
  exact hj ▸ inferInstance

theorem chernPart_singleton (hq : IsArithVar q 0) (L : HermLB q) (σ : k →+* ℂ) (ε : ℤˣ)
    (y : CxPts q σ) : (L.φ σ).chernPart 0 ε {y} = ENNReal.ofReal (ε : ℤ) := by
  have := isProper hq
  obtain ⟨c, hc⟩ := exists_chart hq y
  rw [Weight.chernPart_apply (L.cInf σ) ε c (measurableSet_singleton y)
    (Set.singleton_subset_iff.2 hc)]
  have e : c.e '' {y} = Set.univ := Set.eq_univ_of_forall fun v => ⟨y, rfl, Subsingleton.elim _ _⟩
  simp [e, AlgChart.chernDens_zero, volume_univ_zero]

theorem finite_cxPts (hq : IsArithVar q 0) (σ : k →+* ℂ) : Finite (CxPts q σ) := by
  have := HtSelfInter.finite_ringHom hq
  obtain ⟨e⟩ := HtSelfInter.nonempty_equiv hq
  have : Finite (Σ σ : k →+* ℂ, CxPts q σ) := .of_equiv _ e.symm
  exact .of_injective _ (sigma_mk_injective (i := σ))

theorem chernInt_univ (hq : IsArithVar q 0) (L : HermLB q) (σ : k →+* ℂ) (f : CxPts q σ → ℝ) :
    (L.φ σ).chernInt 0 Set.univ f = ∑ᶠ y, f y := by
  have := isProper hq
  have := finite_cxPts hq σ
  let := Fintype.ofFinite (CxPts q σ)
  have h₁ : (L.φ σ).chernPart 0 1 = Measure.count := Measure.ext_iff_singleton.2 fun y => by
    rw [chernPart_singleton hq L σ 1 y, Measure.count_singleton]
    simp
  have h₂ : (L.φ σ).chernPart 0 (-1) = 0 := Measure.ext_iff_singleton.2 fun y => by
    rw [chernPart_singleton hq L σ (-1) y]
    simp
  rw [Weight.chernInt, h₁, h₂, Measure.restrict_univ, Measure.restrict_univ, integral_zero_measure,
    sub_zero, integral_fintype (Integrable.of_finite (μ := Measure.count) (f := f)), finsum_eq_sum_of_fintype]
  simp [Measure.real]

theorem main : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ (M N : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.archInt M 0 hr = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, logNorm (M.φ σ) r y := by
  intro k _ Y _ q hq M N r hr
  unfold HermLB.archInt
  refine finsum_congr fun σ => ?_
  have hS : offSupp q σ (M.div hr) = Set.univ := Set.eq_univ_of_forall fun y => mem_offSupp.2 fun h =>
    CartierDiv.genericPoint_notMem_supp _ (TwistTop.under_eq_genericPoint hq y ▸ h)
  rw [hS, chernInt_univ hq]

end GlobalTheory.ArchDimZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.DblSiegelX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def zs {n n₁ d : ℕ} (H : Plane E n n₁) (u : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  Matrix.vecMulVec (incV F H.y) ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ u)

variable {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module (AF F) V] {Bf : V → V → AF F} {d : ℕ}

theorem rho_add (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (w : V) (Φ Ψ : (κ → AF F) → ℂ) :
    dd.rho ψ w (Φ + Ψ) = dd.rho ψ w Φ + dd.rho ψ w Ψ := by
  funext x; simp [Darboux.rho, schr, mul_add]

theorem rho_smul (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (w : V) (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    dd.rho ψ w (c • Φ) = c • dd.rho ψ w Φ := by
  funext x; simp [Darboux.rho, schr]; ring

def avgFun (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → V) (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (Φ : (κ → AF F) → ℂ) : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → ℂ :=
  fun u => lam (dd.rho ψ (z u) Φ)

theorem avgFun_add (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → V)
    (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (Φ Ψ : (κ → AF F) → ℂ) :
    avgFun dd ψ z lam (Φ + Ψ) = avgFun dd ψ z lam Φ + avgFun dd ψ z lam Ψ := by
  funext u; simp [avgFun, rho_add]

theorem avgFun_smul (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → V)
    (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    avgFun dd ψ z lam (c • Φ) = c • avgFun dd ψ z lam Φ := by
  funext u; simp [avgFun, rho_smul]

def avgSub (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → V) (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (μ : @Measure (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (borel _)) : Submodule ℂ ((κ → AF F) → ℂ) where
  carrier := {Φ | Integrable (avgFun dd ψ z lam Φ) μ}
  zero_mem' := by
    show Integrable (avgFun dd ψ z lam 0) μ
    have : avgFun dd ψ z lam 0 = 0 := by
      have h := avgFun_smul dd ψ z lam 0 0
      simpa using h
    rw [this]; exact integrable_zero _ _ _
  add_mem' := fun {Φ Ψ} hΦ hΨ => by
    show Integrable (avgFun dd ψ z lam (Φ + Ψ)) μ
    rw [avgFun_add]; exact hΦ.add hΨ
  smul_mem' := fun c Φ hΦ => by
    show Integrable (avgFun dd ψ z lam (c • Φ)) μ
    rw [avgFun_smul]; exact hΦ.smul c

def averagedIntegralIntegrable (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → V) (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (μ : @Measure (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (borel _)) : avgSub dd ψ z lam μ →ₗ[ℂ] ℂ where
  toFun Φ := ∫ u, avgFun dd ψ z lam Φ.1 u ∂μ
  map_add' Φ Ψ := by
    simp only [Submodule.coe_add, avgFun_add, Pi.add_apply]
    exact integral_add Φ.2 Ψ.2
  map_smul' c Φ := by
    simp only [Submodule.coe_smul, avgFun_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

def avgL (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → V) (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (μ : @Measure (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (borel _)) : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ :=
  (LinearMap.exists_extend (averagedIntegralIntegrable dd ψ z lam μ)).choose

theorem avgL_apply (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → V)
    (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (μ : @Measure (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (borel _)) (Φ : (κ → AF F) → ℂ)
    (h : Integrable (avgFun dd ψ z lam Φ) μ) : avgL dd ψ z lam μ Φ = ∫ u, avgFun dd ψ z lam Φ u ∂μ := by
  have := congrArg (fun f => f ⟨Φ, h⟩) (LinearMap.exists_extend (averagedIntegralIntegrable dd ψ z lam μ)).choose_spec
  exact this

end GlobalTheory.DblSiegelX
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanWeilOperatorTransportsHeisenbergLineD
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanWeilOperatorTransportsHeisenbergLineD
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.HeisTransport

theorem actsD_heisLine_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) → (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f)) →
    ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ →
      ActsD (evI F) (M.heisLine B.ψ (mat g * u * (mat h).transpose)) (T f) (T f₁) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hB hX hW hM hWeil g hg h hh T hT hTi u hu f f₁ hf
  have hS := IsUWeilPair.isUSplitting hWeil
  set ψ := B.ψ with hψ
  set p : UA σ X.J × UA σ W.J := (g, h) with hp

  have hrest : ∀ (φ : SInf F (Fin n × Fin d)) (g' : (Fin n × Fin d → Af F) → ℂ), g' ∈ SB (Fin n × Fin d → Af F) →
      Rest (evI F) (⇑φ) (fun x => g' (fun i => (x i).2)) := by
    intro φ g' hg'
    refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨φ, g', hg', rfl⟩⟩
    change g' (fun i => (x i + z i).2) = g' (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
  have hpure : ∀ (φ : SInf F (Fin n × Fin d)) (g' : (Fin n × Fin d → Af F) → ℂ), g' ∈ SB (Fin n × Fin d → Af F) →
      om p (pureA F φ g') = pureA F (T φ) g' := fun φ g' hg' => hT φ _ (hrest φ g' hg')

  have h0 : ∀ v : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ t : ℝ, M.heisLine ψ v t 0 = 0 := by
    intro v t
    funext x
    simp [Model.heisLine, Darboux.rho, schr]

  obtain ⟨D, hD⟩ := GlobalTheory.HeisDer.derEx F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J) M.co hB.std
  have hSDD := (hD u hu f).1
  have hL := GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₁ (D u f)
  have hAD : ActsD (evI F) (M.heisLine ψ u) f (D u f) := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (D u f) f₁).1 _ (h0 u) hSDD
  have hf₁ : f₁ = D u f := hL.2.2.1 _ hf hAD
  rw [← hf₁] at hSDD

  have himpl : ∀ t : ℝ, ∀ Φ ∈ schA F (Fin n × Fin d),
      M.heisLine ψ (mat g * u * (mat h).transpose) t (om p Φ) = om p (M.heisLine ψ u t Φ) := by
    intro t Φ hΦ
    have e := hS.impl p (realAd F t • u) Φ hΦ
    simp only [Model.heisLine]
    rw [e]
    congr 2
    simp only [actAB, hp, mat, Matrix.mul_smul, Matrix.smul_mul]

  have hSD : GlobalTheory.RealLift.SD (M.heisLine ψ (mat g * u * (mat h).transpose)) (T f) (T f₁) := by
    intro g' hg' l hl
    have hΦ : pureA F (⇑f) g' ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g', hg', rfl⟩
    have e : (fun t => l (M.heisLine ψ (mat g * u * (mat h).transpose) t (pureA F (⇑(T f)) g'))) =
        fun t => (l ∘ₗ om p) (M.heisLine ψ u t (pureA F (⇑f) g')) := by
      funext t
      rw [← hpure f g' hg', himpl t _ hΦ]
      rfl
    rw [e, ← hpure f₁ g' hg']
    exact hSDD g' hg' (l ∘ₗ om p) (hS.adm p l hl)
  exact (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (T f) (T f₁) (T f₁)).1 _ (h0 _) hSD

end GlobalTheory.HeisTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanWeilOperatorTransportsHeisenbergLineDStatement
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanWeilOperator_transports_heisenbergLineDerivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) → (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f)) →
    ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ →
      ActsD (evI F) (M.heisLine B.ψ (mat g * u * (mat h).transpose)) (T f) (T f₁) := by
  first | exact @GlobalTheory.HeisTransport.actsD_heisLine_transport | exact GlobalTheory.HeisTransport.actsD_heisLine_transport | (intros; apply GlobalTheory.HeisTransport.actsD_heisLine_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundUnitaryAction
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.WeilDirBound

open GlobalTheory.AdelicU

theorem norm_entry_le_opNorm {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (i k : m) :
    ‖A i k‖ ≤ (opNorm A : ℝ) := by
  have h1 : Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A (EuclideanSpace.single k 1) =
      WithLp.toLp 2 (A *ᵥ Pi.single k 1) := Matrix.toEuclideanCLM_toLp A _
  have h2 : (A *ᵥ Pi.single k (1 : ℂ)) i = A i k := by simp
  calc ‖A i k‖ = ‖(Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A (EuclideanSpace.single k 1)).ofLp i‖ := by
        rw [h1, ← h2]
    _ ≤ ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A (EuclideanSpace.single k 1)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A‖ * ‖EuclideanSpace.single k (1 : ℂ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = (opNorm A : ℝ) := by simp [opNorm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_piInf_entry_le_heightGL {m : Type} [Fintype m] [DecidableEq m] (g : GL m (AF F ⊗[F] E))
    (w : InfinitePlace F) (τ : EmbOver E w) (i k : m) :
    ‖piInf τ ((g : Matrix m m (AF F ⊗[F] E)) i k)‖ ≤ (heightGL F g : ℝ) := by
  have e : piInf τ ((g : Matrix m m (AF F ⊗[F] E)) i k) =
      (((Formalism.UG.bc (compInf F E w) g : GL m (w.Completion ⊗[F] E)) : Matrix m m _).map (infEmb τ)) i k := rfl
  rw [e]
  refine (norm_entry_le_opNorm _ i k).trans ?_
  have h1 : opNorm (((Formalism.UG.bc (compInf F E w) g : GL m (w.Completion ⊗[F] E)) : Matrix m m _).map (infEmb τ))
      ≤ heightGL F g := by
    refine ((normInf_le_iff F w).1 le_rfl τ).trans ((le_htOf _ _).trans ?_)
    refine le_trans ?_ (le_mul_of_one_le_right' (one_le_finprod' fun _ => one_le_htOf _ _))
    exact Finset.single_le_prod' (f := fun w => htInf F w (Formalism.UG.bc (compInf F E w) g))
      (fun _ _ => one_le_htOf _ _) (Finset.mem_univ w)
  exact_mod_cast h1

end GlobalTheory.WeilDirBound

end

namespace GlobalTheory.WeilDirBound

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_piInf_actAB_le (σ : E →ₐ[F] E) (n d : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (p : UA σ J × UA σ J')
    (x : Matrix (Fin n) (Fin d) (AE F E)) (B : ℝ) (hB : 0 ≤ B)
    (hx : ∀ (w : InfinitePlace F) (τ : EmbOver E w) k l, ‖piInf τ (x k l)‖ ≤ B) :
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) i j,
      ‖piInf τ (actAB (cA σ) p x i j)‖ ≤ n * d * ((ht p.1 : ℝ) * ht p.2) * B := by
  intro w τ i j
  set g : GL (Fin n) (AF F ⊗[F] E) := (p.1 : GL (Fin n) (AF F ⊗[F] E)) with hg
  set h : GL (Fin d) (AF F ⊗[F] E) := (p.2 : GL (Fin d) (AF F ⊗[F] E)) with hh
  have hg1 : (ht p.1 : ℝ) = heightGL F g := rfl
  have hh1 : (ht p.2 : ℝ) = heightGL F h := rfl
  have e : actAB (cA σ) p x i j = ∑ l, ∑ k,
      (g : Matrix (Fin n) (Fin n) _) i k * x k l * (h : Matrix (Fin d) (Fin d) _) j l := by
    simp only [actAB, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rfl
  have hG := fun k => norm_piInf_entry_le_heightGL g w τ i k
  have hH := fun l => norm_piInf_entry_le_heightGL h w τ j l
  have hG0 : (0 : ℝ) ≤ heightGL F g := NNReal.coe_nonneg _
  have hH0 : (0 : ℝ) ≤ heightGL F h := NNReal.coe_nonneg _
  rw [e, hg1, hh1]
  calc ‖piInf τ (∑ l, ∑ k, (g : Matrix (Fin n) (Fin n) _) i k * x k l * (h : Matrix (Fin d) (Fin d) _) j l)‖
      ≤ ∑ l : Fin d, ∑ k : Fin n, ((heightGL F g : ℝ) * heightGL F h * B) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [map_mul, map_mul, norm_mul, norm_mul]
        calc ‖piInf τ ((g : Matrix (Fin n) (Fin n) _) i k)‖ * ‖piInf τ (x k l)‖ *
              ‖piInf τ ((h : Matrix (Fin d) (Fin d) _) j l)‖
            ≤ (heightGL F g : ℝ) * B * heightGL F h :=
              mul_le_mul (mul_le_mul (hG k) (hx w τ k l) (norm_nonneg _) hG0) (hH l) (norm_nonneg _)
                (mul_nonneg hG0 hB)
          _ = (heightGL F g : ℝ) * heightGL F h * B := by ring
    _ = n * d * ((heightGL F g : ℝ) * heightGL F h) * B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end GlobalTheory.WeilDirBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfLocalIntegralInBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfLocalIntegralInBasis
namespace StabilizerBasis
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.StabBasis

theorem exists_bc_eq_of_entries {R : Type} [CommRing R] (S : Subring R) {n : ℕ} (g : GL (Fin n) R)
    (h1 : ∀ i j, g.1 i j ∈ S) (h2 : ∀ i j, g⁻¹.1 i j ∈ S) :
    ∃ y : GL (Fin n) S, Formalism.UG.bc S.subtype y = g := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) S => A.map S.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem mem_St_of_inBasis_mem_KO : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)),
    (∀ w : Pl D.host.E, inBasis rfl β w x ∈ KO (Kw w) (Fin n)) → x ∈ St β := by
  intro D n β x h
  have hent : ∀ (w : Pl D.host.E) (g : GL (Fin n) (Kw w)), g ∈ KO (Kw w) (Fin n) →
      ∀ i j, g.1 i j ∈ Formalism.UG.Ov D.host.E w := by
    intro w g hg i j
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n] at hg
    obtain ⟨u, rfl⟩ := hg
    exact (u.1 i j).2
  have e2 : (β⁻¹ * x * β)⁻¹ = β⁻¹ * x⁻¹ * β := by group
  have a1 : ∀ i j, (β⁻¹ * x * β).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j =>
    (mem_OA_iff _).2 fun w => by
      have := hent w _ (h w) i j
      rwa [inBasis_apply] at this
  have a2 : ∀ i j, (β⁻¹ * x * β)⁻¹.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j =>
    (mem_OA_iff _).2 fun w => by
      have := hent w _ ((KO (Kw w) (Fin n)).inv_mem (h w)) i j
      rw [← map_inv, inBasis_apply] at this
      rwa [e2]
  obtain ⟨y, hy⟩ := exists_bc_eq_of_entries _ _ a1 a2
  refine ⟨y, ?_⟩
  have e : Formalism.L2.DIV.intGL D.host.F D.host.E n y = β⁻¹ * x * β := hy
  show β * Formalism.L2.DIV.intGL D.host.F D.host.E n y * β⁻¹ = x
  rw [e]; group

end GlobalTheory.CompanionTheory.StabBasis

end
end

end StabilizerBasis
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.Adopt.mem_latticeStabilizer_of_local_integral_inBasis : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)), (∀ w : Pl D.host.E, inBasis rfl β w x ∈ KO (Kw w) (Fin n)) → x ∈ St β := by
  first | exact @StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO | exact StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO | (intros; apply StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO <;> assumption)

end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfLocalIntegralInBasisStatement
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_latticeStabilizer_of_local_integral_inBasis : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)), (∀ w : Pl D.host.E, inBasis rfl β w x ∈ KO (Kw w) (Fin n)) → x ∈ St β := by
  first | exact @GlobalTheory.Adopt.mem_latticeStabilizer_of_local_integral_inBasis | exact GlobalTheory.Adopt.mem_latticeStabilizer_of_local_integral_inBasis | (intros; apply GlobalTheory.Adopt.mem_latticeStabilizer_of_local_integral_inBasis <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneLocalFactor
noncomputable section

namespace GlobalTheory.LeviLine

open Matrix

variable {R : Type} [CommRing R] {n : ℕ}

def sf (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) : R := u ⬝ᵥ (J *ᵥ fun i => c (v i))

variable (c : R →+* R) (J : Matrix (Fin n) (Fin n) R)

theorem sf_sub_left (u w v : Fin n → R) : sf c J (u - w) v = sf c J u v - sf c J w v := by
  simp [sf, sub_dotProduct]

theorem sf_smul_left (r : R) (u v : Fin n → R) : sf c J (r • u) v = r * sf c J u v := by
  simp [sf, smul_dotProduct]

theorem sf_sub_right (u v w : Fin n → R) : sf c J u (v - w) = sf c J u v - sf c J u w := by
  simp only [sf, Pi.sub_apply, map_sub]
  rw [show (fun i => c (v i) - c (w i)) = (fun i => c (v i)) - fun i => c (w i) from rfl, mulVec_sub, dotProduct_sub]

theorem sf_smul_right (r : R) (u v : Fin n → R) : sf c J u (r • v) = c r * sf c J u v := by
  simp only [sf, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => c r * c (v i)) = c r • fun i => c (v i) from rfl, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem vecMulVec_mulVec' (x a z : Fin n → R) : vecMulVec x a *ᵥ z = (a ⬝ᵥ z) • x := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem sf_skew (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j) (u v : Fin n → R) :
    sf c J u v = -c (sf c J v u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sf, dotProduct, mulVec, map_sum, map_mul, hc, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem ext_form {A B : Matrix (Fin n) (Fin n) R} (h : ∀ u v : Fin n → R, u ⬝ᵥ A *ᵥ v = u ⬝ᵥ B *ᵥ v) : A = B := by
  ext i j
  simpa [mulVec_single_one, single_one_dotProduct] using h (Pi.single i 1) (Pi.single j 1)

theorem ext_mulVec {A B : Matrix (Fin n) (Fin n) R} (h : ∀ u : Fin n → R, A *ᵥ u = B *ᵥ u) : A = B :=
  ext_form fun u v => by rw [h]

variable {c J}

end GlobalTheory.LeviLine

namespace GlobalTheory.LeviLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open Matrix

theorem ext_mulVec_single {R : Type} [CommRing R] {m k : ℕ} {A B : Matrix (Fin m) (Fin k) R}
    (h : ∀ j, A *ᵥ Pi.single j 1 = B *ᵥ Pi.single j 1) : A = B := by
  ext i j
  simpa [mulVec_single_one] using congrFun (h j) i

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cA_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, sigma_invol h]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem cA_inclR (σ : E →ₐ[F] E) (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [cA, inclR]

end GlobalTheory.LeviLine

namespace GlobalTheory.LeviLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open Matrix

end GlobalTheory.LeviLine

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlas
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlas
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem contDiffOn_real_transition (i j : A.ι) :
    ContDiffOn ℝ ∞ (A.e j ∘ (A.e i).symm) ((A.e i).target ∩ (A.e i).symm ⁻¹' (A.e j).source) :=
  (contDiffOn_piLp 2).2 fun a => GlobalTheory.ChartGlue.contDiffOn_real
    ((A.e i).isOpen_inter_preimage_symm (A.e j).open_source) (differentiableOn_euclidean.1 (A.holo i j) a)

theorem exists_smooth_bump [T2Space M] (x : M) :
    ∃ (i : A.ι) (ψ : M → ℝ), A.SmoothOn univ (fun y => (ψ y : ℂ)) ∧ tsupport ψ ⊆ (A.e i).source ∧
      ∀ᶠ y in 𝓝 x, ψ y = 1 := by
  classical
  obtain ⟨i, hxe⟩ := A.cover x
  set e := A.e i with he
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hxe)
  let β : ContDiffBump (e x) := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  have hcb : Metric.closedBall (e x) (ε / 2) ⊆ e.target :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  set C := e.symm '' Metric.closedBall (e x) (ε / 2) with hC
  have hCc : IsCompact C := (isCompact_closedBall (e x) (ε / 2)).image_of_continuousOn
    (e.continuousOn_symm.mono fun y hy => hcb hy)
  have hCsub : C ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_target (hcb hy)
  let ψ : M → ℝ := fun w => if w ∈ e.source then β (e w) else 0
  have hsupp : Function.support ψ ⊆ C := by
    intro w hw
    simp only [Function.mem_support, ψ] at hw
    split_ifs at hw with hws
    · have : e w ∈ Metric.ball (e x) (ε / 2) := by
        rw [← β.support_eq]; exact hw
      exact ⟨e w, Metric.ball_subset_closedBall this, e.left_inv hws⟩
    · exact absurd rfl hw
  have hts : tsupport ψ ⊆ C := closure_minimal hsupp hCc.isClosed
  refine ⟨i, ψ, ?_, hts.trans hCsub, ?_⟩
  · intro k
    rw [preimage_univ, inter_univ]
    apply contDiffOn_of_locally_contDiffOn
    intro y hy
    by_cases hys : (A.e k).symm y ∈ e.source
    · refine ⟨(A.e k).target ∩ (A.e k).symm ⁻¹' e.source,
        (A.e k).isOpen_inter_preimage_symm e.open_source, ⟨hy, hys⟩, ?_⟩
      have hβ : ContDiff ℝ ∞ (fun y : V n => ((β y : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp β.contDiff
      refine ((hβ.comp_contDiffOn (A.contDiffOn_real_transition k i)).mono inter_subset_right).congr
        fun v hv => ?_
      have hv1 : (A.e k).symm v ∈ e.source := hv.2.2
      simp only [Function.comp, ψ, if_pos hv1]
      rfl
    · refine ⟨(A.e k).target ∩ (A.e k).symm ⁻¹' Cᶜ,
        (A.e k).isOpen_inter_preimage_symm hCc.isClosed.isOpen_compl,
        ⟨hy, fun h => hys (hCsub h)⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : ℂ))).congr fun v hv => ?_
      have : ψ ((A.e k).symm v) = 0 := by
        by_contra h
        exact hv.2.2 (hsupp h)
      simp [Function.comp, this]
  · have ho : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e x) (ε / 4)) :=
      e.isOpen_inter_preimage Metric.isOpen_ball
    filter_upwards [ho.mem_nhds ⟨hxe, Set.mem_preimage.mpr (Metric.mem_ball_self (by linarith))⟩] with w hw
    simp only [ψ, if_pos hw.1]
    exact β.one_of_mem_closedBall (Metric.ball_subset_closedBall hw.2)

end GlobalTheory.CxForm.HolAtlas

namespace GlobalTheory

theorem exists_finite_smooth_partition_holAtlas {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] {n : ℕ}
    (A : GlobalTheory.CxForm.HolAtlas M n) :
    ∃ (N : ℕ) (c : Fin N → A.ι) (χ : Fin N → M → ℝ), (∀ j, A.SmoothOn univ fun y => (χ j y : ℂ)) ∧
      (∀ j, tsupport (χ j) ⊆ (A.e (c j)).source) ∧ ∀ y, ∑ j, χ j y = 1 := by
  classical
  choose E Ψ hΨs hΨt hΨ1 using A.exists_smooth_bump
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : M => interior {y | Ψ x y = 1})
    (fun _ => isOpen_interior) (fun y _ => mem_iUnion.2 ⟨y, mem_interior_iff_mem_nhds.2 (hΨ1 y)⟩)
  let p : Fin t.card → M := fun i => (t.equivFin.symm i : M)
  let ψ : Fin t.card → M → ℝ := fun i => Ψ (p i)
  have hsum : ∀ x, ∑ i, ψ i x * ∏ j ∈ Finset.univ with j < i, (1 - ψ j x) =
      1 - ∏ i, (1 - ψ i x) := fun x => by
    rw [Finset.prod_one_sub_ordered]; ring
  refine ⟨t.card, fun i => E (p i), fun i x => ψ i x * ∏ j ∈ Finset.univ with j < i, (1 - ψ j x),
    fun i k => ?_, fun i => (tsupport_mul_subset_left).trans (hΨt (p i)), fun x => ?_⟩
  · refine ((hΨs (p i) k).mul (contDiffOn_prod (t := Finset.univ.filter (· < i))
      fun j _ => (contDiffOn_const (c := (1 : ℂ))).sub (hΨs (p j) k))).congr fun v _ => ?_
    simp [Function.comp, ψ]
  · rw [hsum]
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    have h1 : ψ (t.equivFin ⟨u, hu⟩) x = 1 := by
      have : p (t.equivFin ⟨u, hu⟩) = u := by simp [p]
      simp only [ψ, this]
      exact (interior_subset hxu : x ∈ {y | Ψ u y = 1})
    rw [Finset.prod_eq_zero (Finset.mem_univ (t.equivFin ⟨u, hu⟩)) (by rw [h1]; ring)]
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlasStatement
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_smooth_partition_unity_holAtlas : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n), ∃ (N : ℕ) (c : Fin N → A.ι) (χ : Fin N → M → ℝ), (∀ j, A.SmoothOn univ fun y => (χ j y : ℂ)) ∧ (∀ j, tsupport (χ j) ⊆ (A.e (c j)).source) ∧ ∀ y, ∑ j, χ j y = 1 := by
  first | exact @GlobalTheory.exists_finite_smooth_partition_holAtlas | exact GlobalTheory.exists_finite_smooth_partition_holAtlas | (intros; apply GlobalTheory.exists_finite_smooth_partition_holAtlas <;> assumption)
end
end
