module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConjInvariantHZcomb
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersectionInt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharZero

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGraphChangeOfModel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

section Objects

variable {K : Type} {ι : K → Type} {K₂ : Type} {ι₂ : K₂ → Type}

def formApply (g : (Σ k, ι₂ k) → MRing ι) (z : (Σ k, ι k) → ℂ) : (Σ k, ι₂ k) → ℂ :=
  fun q => eval z (map (Int.castRingHom ℂ) (g q))

variable [Fintype K] [∀ k, Fintype (ι k)]

end Objects

def GraphChangeOfModel.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
      (P : Ideal (MRing ι)) (d : ℕ) (g : (Σ k, ι₂ k) → MRing ι) (δ : K₂ → K → ℕ)
      (G : GenFibre inrV (graphIdeal P g))
      (J : IFamily G.Φ (fibreIdx (Sum.elim ι ι₂) (Sum.inr : K₂ → K ⊕ K₂)))
      (L : Fin d → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι₂) (L₁ : Fin d → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
      IsArithVar P d → (∀ q, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g q) (δ q.1)) → IsBasePtFree P g →
      IsArithVar (imageZ inrV (graphIdeal P g)) d → IsFieldIntersection J →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L₁ j)) →
      (∀ j k, (L₁ j).a k = ∑ k₂, (L j).a k₂ * (δ k₂ k : ℤ)) →
      (∀ j, ∀ z ∈ mcPts P, (L₁ j).h z = (L j).h (formApply g z)) →
      I K ι P d L₁ = (J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 Fin.elim0 : ℝ) * I K₂ ι₂ (imageZ inrV (graphIdeal P g)) d L

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKodairaSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem nefOnGenericDeg_of_semipos (hN : NefOnGenericOfSemipos.Statement)
    (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) {P P0 : Ideal (MRing ι)} {M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hP0 : P0 ≤ P) (hs : IsSemipositiveRel P0 P M) : NefOnGenericDeg P M.a := by
  classical
  intro W hW hPW
  have h1 : 0 ≤ geomDeg W M 1 := hN K ι P P0 M hP0 hs W hW hPW
  have h2 := hD K ι W 1 (fun _ => M) hW (fun _ => hs.1)
  have h3 : geomDeg W M 1 = (genDeg W 1 M.a : ℝ) := by
    rw [geomDeg, genDeg]
    convert h2 using 2
    rfl
  exact_mod_cast h3 ▸ h1

theorem continuousOn_zcomb_fsH {M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hM : IsSmoothHerm M) (k : ℤ) :
    ContinuousOn (HermLine.zcomb M (fsH ι) k (-1)).h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have hH : ContinuousOn (fsH ι).h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs (ι := ι) 1).continuousOn
  exact (hM.continuousOn.zpow₀ k fun z hz => Or.inl (M.pos z hz).ne').mul
    (hH.zpow₀ (-1) fun z hz => Or.inl ((fsH ι).pos z hz).ne')

theorem KodairaSection.proof (hN : NefOnGenericOfSemipos.Statement)
    (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) (hK : KodairaGeneric.Statement)
    (hC : ChartDenominator.Statement) (hS : SectionSupBound.Statement) : KodairaSection.Statement := by
  intro K _ ι _ Ω _ _ y D M P0 hD1 har hb hM
  obtain ⟨k, e, hk, he0, heQ⟩ :=
    hK K ι Ω y D M.a hD1 har hb (nefOnGenericDeg_of_semipos hN hD hM.normalForm_baseLattice_le_dualSpan_sup_line hM.semipos) hM.big
  obtain ⟨n, hn, hne⟩ := hC K ι Ω y _ 1 e heQ
  have ha : (HermLine.zcomb M (fsH ι) k (-1)).a = (k : ℤ) • M.a - 1 := by
    funext i
    simp [HermLine.zcomb, fsH, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics]
    ring
  obtain ⟨C, hC0, hB⟩ := hS K ι Ω y (HermLine.zcomb M (fsH ι) k (-1)) 1 ((n : Ω) * e)
    (continuousOn_zcomb_fsH hM.semipos.1 k) (by rw [ha]; exact hne)
  exact ⟨k, (n : Ω) * e, C, hk, hC0, mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) he0, hne, hB⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.TwoBlockCycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section Cycle

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def vertCycleNum (P : Ideal (MRing ι)) (s : MRing ι) {n : ℕ} (e : Fin n → K → ℤ) : ℝ :=
  ∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
    (if IsHorizontal W then 0 else (geoNum n W e : ℝ) * Real.log (charOf W))

theorem vertR_eq_vertCycleNum (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.vertR P L s = vertCycleNum P s (fun j => (L j).a) :=
  rfl

end Cycle

section TwoBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def twoBlockDen (c : κ) : MRing (FinTwoTypeFamily κ) :=
  X ⟨0, c⟩

def twoBlockNum (l : Ix κ → ℤ) : MRing (FinTwoTypeFamily κ) :=
  ∑ j : Ix κ, MvPolynomial.C (l j) * X ⟨1, j.2⟩

def twoBlockVert (x x' : Ix κ → Ω) (c : κ) (l : Ix κ → ℤ) {n : ℕ} (e : Fin n → Fin 2 → ℤ) : ℝ :=
  vertCycleNum (twoBlockIdeal x x') (twoBlockNum l) e - vertCycleNum (twoBlockIdeal x x') (twoBlockDen c) e

def twoBlockDegList (D i : ℕ) : Fin D → Fin 2 → ℤ :=
  fun j => if (j : ℕ) < i then Pi.single 0 1 else Pi.single 1 1

theorem twoBlockDegList_eq (m m' : ConeMetric ℂ (Ix κ)) (D i : ℕ) (j : Fin D) :
    twoBlockDegList D i j = (twoBlockList m m' D i (if (j : ℕ) < i then j.castSucc else j.succ)).a := by
  unfold twoBlockDegList twoBlockList
  split_ifs with h1 h2 h2 <;> simp_all [blockLine]
  omega

end TwoBlock

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneSectionBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

section Mul

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}


omit [∀ k, Fintype (ι k)] in
theorem mul_mem_chartLatQ (b : K → ℤ) {t : Ω} (ht : t ∈ chartLatQ y (b - 1) 1) :
    (∏ k, y ⟨k, c k⟩) * t ∈ chartLatQ y b 1 := by
  intro c' hc'
  have h := ht c' hc'
  have hk : ∀ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) =
      y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (b - 1) k)) / y ⟨k, c' k⟩ := by
    intro k
    rw [eq_div_iff (hc' k), ← zpow_add_one₀ (hc' k)]
    congr 1
    simp only [Pi.sub_apply, Pi.one_apply]
    ring
  have heq : (∏ k, y ⟨k, c k⟩) * t * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) =
      (t * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (b - 1) k))) * ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) := by
    simp only [hk, Finset.prod_div_distrib]
    ring
  rw [heq]
  refine Subalgebra.mul_mem _ h (Subalgebra.prod_mem _ fun k _ => ?_)
  exact Algebra.subset_adjoin ⟨⟨k, c k⟩, rfl⟩

theorem finrank_chartLatQ_le (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ) :
    Module.finrank ℚ (chartLatQ y b 1) ≤
      Module.finrank ℚ (chartLatQ y (b - 1) 1) + Module.finrank ℚ (chartLatQ y b 1 ⧸ chartDivSec y c b) := by
  by_cases hfin : FiniteDimensional ℚ (chartLatQ y b 1)
  swap
  · rw [Module.finrank_of_not_finite hfin]; exact Nat.zero_le _
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  let φ : chartLatQ y (b - 1) 1 →ₗ[ℚ] chartDivSec y c b :=
    { toFun := fun t => ⟨⟨(∏ k, y ⟨k, c k⟩) * t, mul_mem_chartLatQ b t.2⟩,
        Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨t, t.2, rfl⟩)⟩
      map_add' := fun s t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_add, mul_add]
      map_smul' := fun r t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply, mul_smul_comm] }
  have hinj : Function.Injective φ := fun s t h => by
    have h' := congrArg (fun x : chartDivSec y c b => ((x : chartLatQ y b 1) : Ω)) h
    exact Subtype.ext (mul_left_cancel₀ hm0 h')
  have hsurj : Function.Surjective φ := by
    rintro ⟨⟨s, hsV⟩, hs⟩
    obtain ⟨t, ht, hts⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hs)
    exact ⟨⟨t, ht⟩, Subtype.ext (Subtype.ext hts)⟩
  have hφ := (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq
  rw [← Submodule.finrank_quotient_add_finrank (chartDivSec y c b), ← hφ, add_comm]

end Mul

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace TwistIntersection

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sheetDensity_add_locConst (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ j, ∀ z ∈ mcPts P, ∃ c : ℝ, ∀ᶠ u in 𝓝 z, φ' j u = φ j u + c)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ' g y w = sheetDensity P Ψ φ g y w := by
  unfold sheetDensity
  split_ifs with hγ
  · congr 1
    have hev := hγ.choose_spec.2
    have hH : ∀ k, cxHessian (fun y' => φ' k (hγ.choose y')) y =
        cxHessian (fun y' => φ k (hγ.choose y')) y := by
      intro k
      obtain ⟨c, hc⟩ := h k _ hev.self_of_nhds.2.1
      have h1 : (fun y' => φ' k (hγ.choose y')) =ᶠ[𝓝 y] fun y' => φ k (hγ.choose y') + c :=
        hev.self_of_nhds.1.continuousAt.eventually hc
      have h2 : fderiv ℝ (fun y' => φ' k (hγ.choose y')) =ᶠ[𝓝 y]
          fderiv ℝ (fun y' => φ k (hγ.choose y')) := by
        filter_upwards [h1.eventuallyEq_nhds] with x hx
        rw [hx.fderiv_eq, fderiv_add_const]
      unfold cxHessian
      rw [h2.fderiv_eq]
    simp only [maDensity, hH]
  · rfl

theorem ptsIntegral_add_locConst (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ j, ∀ z ∈ mcPts P, ∃ c : ℝ, ∀ᶠ u in 𝓝 z, φ' j u = φ j u + c) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ' g = ptsIntegral P φ g := by
  unfold ptsIntegral
  split_ifs
  · simp only [ptsIntegralAt, sheetDensity_add_locConst P h]
  · rfl

theorem I_snoc_degZero {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {P : Ideal (MRing ι)} {n : ℕ} {L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hP : IsArithVar P (n + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hB : IsSmoothHerm B) (ha : B.a = 0) :
    I P (n + 1) (Fin.snoc L B) = -ptsIntegral P (pot L) (logNorm B 1) := by
  have hhom : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι) 0 := by
    intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have hnot : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  rw [hI.2.2 P n L B 1 0 hP hL hB (fun k => by simp [ha]) hhom hnot]
  have hsupp : divSupp P (1 : MRing ι) = ∅ := by
    ext W
    refine ⟨fun hW => ?_, fun h => h.elim⟩
    have h1 : P ⊔ Ideal.span {(1 : MRing ι)} = ⊤ := by simp
    have hp : W.IsPrime := hW.1.1.1
    have hle : P ⊔ Ideal.span {(1 : MRing ι)} ≤ W := hW.1.1.2
    rw [h1] at hle
    exact hp.ne_top (top_le_iff.1 hle)
  unfold recR arInt
  simp only [hsupp, finsum_mem_empty, zero_sub]
  rfl

end TwistIntersection

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelSecM
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def relSecM (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) : Submodule R Ω :=
  Submodule.span R ((fun μ : (Σ k, ι k) → ℕ => ∏ p, y p ^ μ p) '' {μ | ∀ k, ∑ i, μ ⟨k, i⟩ = b k})

theorem monomial_mem_relSecM (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) {b : K → ℕ} (μ : (Σ k, ι k) → ℕ)
    (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = b k) : ∏ p, y p ^ μ p ∈ relSecM R y b :=
  Submodule.subset_span ⟨μ, hμ, rfl⟩

theorem relSecM_fg (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) : (relSecM R y b).FG := by
  have hfin : {μ : (Σ k, ι k) → ℕ | ∀ k, ∑ i, μ ⟨k, i⟩ = b k}.Finite := by
    refine (Set.Finite.pi (t := fun p : (Σ k, ι k) => Set.Iic (b p.1)) fun p => Set.finite_Iic _).subset ?_
    intro μ hμ p _
    simp only [Set.mem_Iic]
    rw [← hμ p.1]
    exact Finset.single_le_sum (f := fun i => μ ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)
  exact Submodule.fg_span (hfin.image _)

theorem mul_mem_relSecM (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) {b b' : K → ℕ} {x x' : Ω}
    (hx : x ∈ relSecM R y b) (hx' : x' ∈ relSecM R y b') : x * x' ∈ relSecM R y (b + b') := by
  have hle : relSecM R y b * relSecM R y b' ≤ relSecM R y (b + b') := by
    rw [relSecM, relSecM, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨μ, hμ, rfl⟩, _, ⟨ν, hν, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨μ + ν, fun k => ?_, ?_⟩
    · simp [Finset.sum_add_distrib, hμ k, hν k]
    · simp [pow_add, Finset.prod_mul_distrib]
  exact hle (Submodule.mul_mem_mul hx hx')

theorem adjoin_isNoetherianRing {m : ℕ} (g : Fin m → Ω) : IsNoetherianRing (Algebra.adjoin ℤ (Set.range g)) := by
  have : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (Set.range g)) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range g)
  exact Algebra.FiniteType.isNoetherianRing ℤ _


omit [∀ k, Fintype (ι k)] in
theorem mul_prod_mem_relChartLat (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) {a a' : K → ℤ} {n : ℕ} (e : K → ℕ)
    (c0 : ∀ k, ι k) (h : ∀ k, a' k = n * a k + e k) {s : Ω} (hs : s ∈ relChartLat R y a n) :
    s * ∏ k, y ⟨k, c0 k⟩ ^ e k ∈ relChartLat R y a' 1 := by
  intro c hc
  have key : ∀ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a' k)) =
      y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) * (y ⟨k, c k⟩ ^ e k)⁻¹ := by
    intro k
    rw [h k, show -(((1 : ℕ) : ℤ) * ((n : ℤ) * a k + (e k : ℤ))) = -((n : ℤ) * a k) + -((e k : ℕ) : ℤ) by push_cast; ring,
      zpow_add₀ (hc k), zpow_neg (y ⟨k, c k⟩) ((e k : ℕ) : ℤ), zpow_natCast]
  rw [Finset.prod_congr rfl fun k _ => key k, Finset.prod_mul_distrib]
  have hmem : (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, (y ⟨k, c0 k⟩ / y ⟨k, c k⟩) ^ e k ∈
      Algebra.adjoin R (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) :=
    mul_mem (hs c hc) (prod_mem fun k _ => pow_mem (Algebra.subset_adjoin
      (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ⟨k, c0 k⟩)) _)
  convert hmem using 1
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_inv_distrib]
  ring

end Objects

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionPointHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

set_option linter.unusedSectionVars false

namespace SmallSectionPointHeight

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_eq_eval_mConeMap (y : (Σ k, ι k) → Ω) (f : MRing ι) :
    aeval y f = eval (fun _ ↦ (1 : Ω)) (mConeMap y f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p n hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [mConeMap]

theorem notMem_mCoordIdeal {y : (Σ k, ι k) → Ω} {f : MRing ι} (hf : aeval y f ≠ 0) :
    f ∉ mCoordIdeal y := by
  intro h
  rw [mCoordIdeal, RingHom.mem_ker] at h
  exact hf (by rw [aeval_eq_eval_mConeMap, h, map_zero])

theorem coord_ne_zero {y : (Σ k, ι k) → Ω} {p : Σ k, ι k} (hp : (X p : MRing ι) ∉ mCoordIdeal y) :
    y p ≠ 0 := by
  intro h0
  apply hp
  rw [mCoordIdeal, RingHom.mem_ker]
  simp [mConeMap, h0]

theorem powLine_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m : ℕ) (z : (Σ k, ι k) → ℂ) :
    (IndefiniteRowSideFullHecke.HeightsSet.powLine A m).h z = A.h z ^ m := by
  induction m with
  | zero => simp [IndefiniteRowSideFullHecke.HeightsSet.powLine, IndefiniteRowSideFullHecke.HeightsSet.constLine]
  | succ m ih => simp [IndefiniteRowSideFullHecke.HeightsSet.powLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ih, pow_succ]

theorem aeval_chartMon (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (e : K → ℕ) :
    aeval y (IndefiniteRowSideFullHecke.HeightsSet.chartMon c e) = ∏ k, y ⟨k, c k⟩ ^ e k := by
  simp [IndefiniteRowSideFullHecke.HeightsSet.chartMon, map_prod, map_pow]

theorem vertR_le {W : Ideal (MRing ι)} {G H : MRing ι}
    (h : ∀ V ∈ divSupp W H, V ∈ divSupp W G ∧
      multAt (W ⊔ Ideal.span {H}) V ≤ multAt (W ⊔ Ideal.span {G}) V) :
    vertR W (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) H ≤ vertR W (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) G := by
  classical
  unfold vertR
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite W H),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite W G)]
  have hsub : (divSupp_finite W H).toFinset ⊆ (divSupp_finite W G).toFinset := fun V hV ↦ by
    rw [Set.Finite.mem_toFinset] at hV ⊢
    exact (h V hV).1
  have hc : ∀ V : Ideal (MRing ι), 0 ≤ (if IsHorizontal V then (0 : ℝ) else
      (geoNum 0 V (fun j ↦ ((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j).a) : ℝ) * Real.log (charOf V)) := by
    intro V
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (by exact_mod_cast IndefiniteRowSideFullHecke.HeightsSet.geoNum_zero_nonneg V _)
        (Real.log_natCast_nonneg _)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun V _ _ ↦
    mul_nonneg (Nat.cast_nonneg _) (hc V))
  refine Finset.sum_le_sum fun V hV ↦ ?_
  rw [Set.Finite.mem_toFinset] at hV
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (h V hV).2) (hc V)

end SmallSectionPointHeight


open SmallSectionPointHeight in
theorem SmallSectionPointHeight.proof (hOrd : SectionOrderAtPoint.Statement) :
    SmallSectionPointHeight.Statement := by
  intro K _ ι _ Ω _ y D A τ s II hII hP hbir hA hτ hs hs0 hsmall
  classical

  choose c hc using hP.2.1.2.2
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k ↦ coord_ne_zero (hc k)

  set ap : K → ℕ := fun k ↦ ((τ : ℤ) * A.a k).toNat with hap
  set an : K → ℕ := fun k ↦ (-((τ : ℤ) * A.a k)).toNat with han
  have hpn : ∀ k, (ap k : ℤ) = an k + τ * A.a k := fun k ↦ by
    have := Int.toNat_sub_toNat_neg ((τ : ℤ) * A.a k)
    simp only [hap, han]
    linarith
  obtain ⟨d, g0, h0, hg0, hh0, hh0y, hgh0⟩ := hbir (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * A.a k)))
  set G := g0 * IndefiniteRowSideFullHecke.HeightsSet.chartMon c ap with hGdef
  set H := h0 * IndefiniteRowSideFullHecke.HeightsSet.chartMon c an with hHdef
  have hG : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G (d + ap) :=
    IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hg0 (IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_chartMon c ap)
  have hH : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog H (d + an) :=
    IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hh0 (IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_chartMon c an)
  have hdeg : ∀ k, ((d + ap) k : ℤ) = (d + an) k + τ * A.a k := fun k ↦ by
    simp only [Pi.add_apply, Nat.cast_add, hpn k]
    ring
  have hGH : aeval y G = s * aeval y H := by
    have hprod : ∀ k, y ⟨k, c k⟩ ^ ap k = y ⟨k, c k⟩ ^ ((τ : ℤ) * A.a k) * y ⟨k, c k⟩ ^ an k := fun k ↦ by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), hpn k, add_comm]
    have h1 : (∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * A.a k))) * ∏ k, y ⟨k, c k⟩ ^ ((τ : ℤ) * A.a k) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun k _ ↦ by rw [← zpow_add₀ (hyc k), neg_add_cancel, zpow_zero]
    rw [hGdef, hHdef, map_mul, map_mul, aeval_chartMon, aeval_chartMon, hgh0,
      Finset.prod_congr rfl fun k _ ↦ hprod k, Finset.prod_mul_distrib]
    linear_combination (s * aeval y h0 * ∏ k, y ⟨k, c k⟩ ^ an k) * h1
  have hHy : aeval y H ≠ 0 := by
    rw [hHdef, map_mul, aeval_chartMon]
    exact mul_ne_zero hh0y (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hyc k))
  have hGy : aeval y G ≠ 0 := by
    rw [hGH]
    exact mul_ne_zero hs0 hHy
  refine ⟨G * H, ⟨_, IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hG hH⟩,
    notMem_mCoordIdeal (by rw [map_mul]; exact mul_ne_zero hGy hHy), ?_⟩
  intro W hW hPW hfW
  have hGW : G ∉ W := fun h ↦ hfW (W.mul_mem_right H h)
  have hHW : H ∉ W := fun h ↦ hfW (W.mul_mem_left G h)

  have hI : IsIntersectionFamily (II K ι) := hII K ι
  set E := IndefiniteRowSideFullHecke.HeightsSet.powLine A τ with hEdef
  have hE : IsSmoothHerm E := IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_powLine hA τ
  set B := ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric (ι := ι) (d + an) with hBdef
  have hB : IsSmoothHerm B := isSmoothHerm_sqMetric _
  have hEB : IsSmoothHerm (E.tensor B) := IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_tensor hE hB
  have hEBa : ∀ k, (E.tensor B).a k = ((d + ap) k : ℕ) := fun k ↦ by
    show E.a k + B.a k = _
    rw [hEdef, IndefiniteRowSideFullHecke.HeightsSet.powLine_a, hdeg k]
    show _ + ((d + an) k : ℤ) = _
    ring
  have hsecG : IsSectionOn W (E.tensor B) G := ⟨_, hEBa, hG, hGW⟩
  have hsecH : IsSectionOn W B H := ⟨_, fun k ↦ rfl, hH, hHW⟩
  have hRG := IndefiniteRowSideFullHecke.HeightsSet.inter_eq_recR (II K ι) hI hW hEB hEBa hG hGW
  have hRH := IndefiniteRowSideFullHecke.HeightsSet.inter_eq_recR (II K ι) hI hW hB (fun k ↦ rfl) hH hHW
  have hadd := IndefiniteRowSideFullHecke.HeightsSet.inter_tensor (II K ι) hI hW hE hB
  have hpow := IndefiniteRowSideFullHecke.HeightsSet.inter_powLine (II K ι) hI hW hA τ
  rw [recR_eq, Inter.cycR_eq_vertR_of_dimOne Inter.arithVarZero _ hW hsecG] at hRG
  rw [recR_eq, Inter.cycR_eq_vertR_of_dimOne Inter.arithVarZero _ hW hsecH] at hRH

  have hvert := vertR_le (hOrd K ι Ω y A.a τ s W G H (d + ap) (d + an) hW hPW hs hG hH hdeg hGH hGW hHW)

  have harch : arInt W G (E.tensor B) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) ≤
      arInt W H B (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) := by
    unfold arInt
    rw [Inter.ptsIntegral_add_of_dimOne fibreFinite hW _ (g₁ := logNorm B H)
      (g₂ := fun z ↦ logNorm (E.tensor B) G z - logNorm B H z) fun z _ ↦ by ring]
    refine add_le_of_nonpos_right (IndefiniteRowSideFullHecke.HeightsSet.ptsIntegral_nonpos W _ fun z hz ↦ ?_)
    show logNorm (E.tensor B) G z - logNorm B H z ≤ 0
    have hGz := norm_pos_iff.mpr (Inter.eval_ne_zero_of_dimOne Inter.arithVarZero hW hsecG hz)
    have hHz := norm_pos_iff.mpr (Inter.eval_ne_zero_of_dimOne Inter.arithVarZero hW hsecH hz)
    have hAz := A.pos z hz.1
    have hBz := B.pos z hz.1
    have hEz : E.h z = A.h z ^ τ := powLine_h A τ z
    have hEz0 : 0 < E.h z := hEz ▸ pow_pos hAz τ
    have hzP : z ∈ mcPts (mCoordIdeal y) := ⟨hz.1, fun f hf ↦ hz.2 f (hPW hf)⟩
    have hsm := hsmall (d + ap) (d + an) G H z hG hH hdeg hGH hzP
    rw [← hEz] at hsm
    refine sub_nonpos.mpr (Real.log_le_log (div_pos hGz (mul_pos hEz0 hBz)) ?_)
    show _ / (E.h z * B.h z) ≤ _ / B.h z
    rw [div_le_div_iff₀ (mul_pos hEz0 hBz) hBz]
    nlinarith [mul_le_mul_of_nonneg_right hsm hBz.le]

  have hτI : 0 ≤ (τ : ℝ) * II K ι W 1 ![A] := by
    rw [← hpow]
    linarith
  have hτ0 : (0 : ℝ) < τ := by exact_mod_cast hτ
  exact le_of_mul_le_mul_left (by rw [mul_zero]; exact hτI) hτ0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNormalLocusRep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace NormalLocusRep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_mul_zpow_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {d : K → ℕ} {g : MRing ι}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) : aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ)) ∈ chartRingZ y c := by
  rw [NmSectionsRationalProof.aeval_mul_prod_zpow y c hg, chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨g, rfl⟩

theorem isFractionRing_chartRingZ (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : IsFractionRing (chartRingZ y c) Ω := by
  refine IsFractionRing.of_field (chartRingZ y c) Ω fun z => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir z
  have hP : (∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  refine ⟨⟨_, aeval_mul_zpow_mem y c hg⟩, ⟨_, aeval_mul_zpow_mem y c hh⟩, ?_⟩
  change z = aeval y g * _ / (aeval y h * _)
  rw [hgh, mul_assoc, mul_div_assoc, div_self (mul_ne_zero hh0 hP), mul_one]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem charZero_of_isHorizontal (y : (Σ k, ι k) → Ω) (hH : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    show mConeMap y (C (n : ℤ)) = 0
    rw [mConeMap, aeval_C, MvPolynomial.algebraMap_apply]
    simp [hn]
  rw [hH, Ideal.mem_bot] at hmem
  exact_mod_cast hmem


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem charZero_chartRingZ [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : CharZero (chartRingZ y c) :=
  charZero_of_inj_zero fun n hn => by
    have : ((n : chartRingZ y c) : Ω) = 0 := by rw [hn]; rfl
    exact_mod_cast this

theorem finiteType_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Algebra.FiniteType ℤ (chartRingZ y c) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)

theorem exists_conductor [CharZero Ω] (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ a ∈ chartRingZ y c, a ≠ 0 ∧ ∀ t ∈ integralClosure (chartRingZ y c) Ω, a * t ∈ chartRingZ y c := by
  classical
  set A := chartRingZ y c
  have := isFractionRing_chartRingZ y hbir c hc
  have := charZero_chartRingZ y c
  have := finiteType_chartRingZ y c
  have : Module.Finite A (integralClosure A Ω) :=
    Model.finite_integralClosure_fractionRing_of_charZero A Ω
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A (integralClosure A Ω)).FG)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (S.image ((↑) : integralClosure A Ω → Ω))
  have hb0 : ((b : A) : Ω) ≠ 0 := by
    intro h0
    exact nonZeroDivisors.coe_ne_zero b (Subtype.ext h0)
  refine ⟨((b : A) : Ω), (b : A).2, hb0, fun t ht => ?_⟩
  have htop : (⟨t, ht⟩ : integralClosure A Ω) ∈ Submodule.span A (S : Set (integralClosure A Ω)) := by
    rw [hS]; trivial
  suffices key : ∀ x ∈ Submodule.span A (S : Set (integralClosure A Ω)), ((b : A) : Ω) * (x : Ω) ∈ A from
    key _ htop
  intro x hx
  set_option synthInstance.maxHeartbeats 200000 in
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr⟩ := hb (x : Ω) (Finset.mem_image_of_mem _ hx)
    rw [show ((b : A) : Ω) * (x : Ω) = (b : A) • (x : Ω) by rw [Algebra.smul_def]; rfl, ← hr]
    exact r.2
  | zero => simp
  | add x z _ _ hx hz =>
    simp only [Subalgebra.coe_add, mul_add]
    exact add_mem hx hz
  | smul r x _ hx =>
    have : ((b : A) : Ω) * (((r : A) • x : integralClosure A Ω) : Ω) = (r : Ω) * (((b : A) : Ω) * (x : Ω)) := by
      rw [Subalgebra.coe_smul, Algebra.smul_def]
      show _ * ((r : Ω) * _) = _
      ring
    rw [this]
    exact mul_mem r.2 hx


omit [Fintype K] in
theorem isMultiHomog_prod {J : Type} (s : Finset J) (H : J → MRing ι) (N : J → K → ℕ)
    (hH : ∀ j ∈ s, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (H j) (N j)) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ j ∈ s, H j) (∑ j ∈ s, N j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LocalRep.isMultiHomog_C (ι := ι) 1
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact LocalRep.isMultiHomog_mul (hH j (Finset.mem_insert_self j s))
      (ih fun i hi => hH i (Finset.mem_insert_of_mem hi))

theorem notMem_mCoordIdeal (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d)
    (h0 : aeval y f ≠ 0) : f ∉ mCoordIdeal y := by
  intro hmem
  have h := (RingHom.mem_ker).mp hmem
  erw [ConeTrdeg.mConeMap_of_isMultiHomog y hf] at h
  exact mul_ne_zero (MvPolynomial.C_ne_zero.2 h0)
    (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k)) h

end NormalLocusRep


open NormalLocusRep in
theorem NormalLocusRep.proof : NormalLocusRep.Statement := by
  intro K _ ι _ Ω _ y D hV hbir
  classical
  have := charZero_of_isHorizontal y hV.2.2.1

  have hchart : ∀ c : ∀ k, ι k, ∃ (N : K → ℕ) (H : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog H N ∧ aeval y H ≠ 0 ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ t ∈ integralClosure (chartRingZ y c) Ω,
        (aeval y H * ∏ k, y ⟨k, c k⟩ ^ (-(N k : ℤ))) * t ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨a, ha, ha0, hcond⟩ := exists_conductor y hbir c hc
      obtain ⟨N, H, hH, he⟩ := LocalRep.exists_form_of_mem_chartRingZ y c hc ha
      have hP : ∀ N' : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ N' k) ≠ 0 := fun N' =>
        Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
      have hHa : aeval y H * ∏ k, y ⟨k, c k⟩ ^ (-(N k : ℤ)) = a := by
        rw [he, mul_assoc, ← Finset.prod_mul_distrib]
        rw [Finset.prod_eq_one fun k _ => by
          rw [← zpow_natCast, ← zpow_add₀ (hc k), add_neg_cancel, zpow_zero], mul_one]
      refine ⟨N, H, hH, ?_, fun _ t ht => ?_⟩
      · rw [he]
        exact mul_ne_zero ha0 (hP N)
      · rw [hHa]
        exact hcond t ht
    · exact ⟨0, C 1, LocalRep.isMultiHomog_C 1, by simp, fun h => absurd h hc⟩
  choose N H hH hH0 hcond using hchart
  refine ⟨∑ c, N c, ∏ c, H c, isMultiHomog_prod _ H N fun c _ => hH c,
    notMem_mCoordIdeal y (isMultiHomog_prod _ H N fun c _ => hH c)
      (by rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun c _ => hH0 c), ?_⟩
  intro a τ s hs z hz hfz

  choose c hzc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    apply hzc k
    have hmem : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
      show mConeMap y (X ⟨k, c k⟩) = 0
      simp [mConeMap, h0]
    simpa using hz.2 _ hmem
  have hHz : eval z (map (Int.castRingHom ℂ) (H c)) ≠ 0 := by
    rw [map_prod, map_prod] at hfz
    exact (Finset.prod_ne_zero_iff.mp hfz) c (Finset.mem_univ c)
  have hx := hcond c hyc _ (hs c hyc)
  obtain ⟨M, G, hG, hGe⟩ := LocalRep.exists_form_of_mem_chartRingZ y c hyc hx
  refine ⟨M + (N c + fun k => ((τ : ℤ) * a k).toNat), N c + (M + fun k => (-((τ : ℤ) * a k)).toNat),
    G * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (N c + fun k => ((τ : ℤ) * a k).toNat) k,
    H c * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (M + fun k => (-((τ : ℤ) * a k)).toNat) k,
    LocalRep.isMultiHomog_mul hG (LocalRep.isMultiHomog_chartMono c _),
    LocalRep.isMultiHomog_mul (hH c) (LocalRep.isMultiHomog_chartMono c _), fun k => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    omega
  ·
    have hz' : ∀ p q : K → ℤ, (∏ k, y ⟨k, c k⟩ ^ p k) * ∏ k, y ⟨k, c k⟩ ^ q k =
        ∏ k, y ⟨k, c k⟩ ^ (p k + q k) := fun p q => by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => (zpow_add₀ (hyc k) _ _).symm
    have hnat : ∀ p : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ p k) = ∏ k, y ⟨k, c k⟩ ^ (p k : ℤ) := fun p =>
      Finset.prod_congr rfl fun k _ => (zpow_natCast _ _).symm
    have key : (∏ k, y ⟨k, c k⟩ ^ (-(N c k : ℤ))) * (∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) *
        (∏ k, y ⟨k, c k⟩ ^ M k) * (∏ k, y ⟨k, c k⟩ ^ (N c k + ((τ : ℤ) * a k).toNat)) =
        ∏ k, y ⟨k, c k⟩ ^ (M k + (-((τ : ℤ) * a k)).toNat) := by
      simp only [hnat]
      rw [hz', hz', hz']
      refine Finset.prod_congr rfl fun k _ => ?_
      congr 1
      push_cast
      omega
    simp only [map_mul, map_prod, map_pow, aeval_X, Pi.add_apply]
    rw [hGe]
    linear_combination (s * aeval y (H c)) * key
  · simp only [map_mul, map_prod, map_pow, map_X, eval_X]
    exact mul_ne_zero hHz (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hzc k))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCoordArithOfFnField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def CoordArithOfFnField.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (d : ℕ),
    Nonempty K' → (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → blockFnField y = blockFnField y' →
    IsArithVar (mCoordIdeal y) d → IsArithVar (mCoordIdeal y') d

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenKoszulStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenKoszulStep.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ),
    IsMultiHomogIdeal V → KH.GeneratedV S V α →
    ∃ R : ℕ, ∀ c : K → ℤ,
      (∀ p : ℕ, 1 ≤ p → p ≤ R → ∀ i : ℕ, 1 ≤ i →
        Subsingleton (KH.cechHc ι (KH.quotPart S V) (c - (p : ℤ) • α) i)) →
      ∀ i : ℕ, 1 ≤ i → Subsingleton (KH.cechHc ι (KH.quotPart S V) c i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHyperplaneRegularSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def HyperplaneRegularSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℕ),
    (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∃ σ : Ω, σ ≠ 0 ∧ σ ∈ chartLatQ y (fun k => (e k : ℤ)) 1 ∧
      ∀ (b : K → ℤ) (s : Ω), s ∈ chartLatQ y b 1 →
        σ * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b + (fun k => (e k : ℤ)) - 1) 1 →
        s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockGraphDeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockGraphDeg.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) →
    IsBlockImage y k₀ M N x →
    ∃ (G : GenFibre (inrV (ι := ι) (ι₂ := GlobalTheory κ)) (graphIdeal (mCoordIdeal y) (blockForms k₀ M)))
      (J : IFamily G.Φ (fibreIdx (Sum.elim ι (GlobalTheory κ)) (Sum.inr : Unit → K ⊕ Unit))),
      IsFieldIntersection J ∧ J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 Fin.elim0 = 1

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end
