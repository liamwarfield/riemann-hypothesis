module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurvePt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartScalingIndep

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Matrix ComplexOrder ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section HidaSetting

variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

def IsEEMetric (G : ((Σ k, T.yyIdx ι ν κ k) → ℂ) → Matrix κ κ ℂ) : Prop :=
  (∀ z, (G z).PosDef) ∧
  (∀ z z' : (Σ k, T.yyIdx ι ν κ k) → ℂ, (∀ i : ι, z ⟨.base, i⟩ = z' ⟨.base, i⟩) →
      (∀ l : ν, z ⟨.det, l⟩ = z' ⟨.det, l⟩) → G z = G z') ∧
  (∀ (c : T.YBlk → ℂ) (z : (Σ k, T.yyIdx ι ν κ k) → ℂ), (∀ k, c k ≠ 0) →
      G (fun p => c p.1 * z p) = G z) ∧
  ∀ m n : κ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => G z m n) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}

end HidaSetting

structure ProjectiveLineBundle (D : ℕ) where

  Ω : Type
  [fieldΩ : Field Ω]

  ι : Type

  ν : Type

  κ : Type
  [finι : Fintype ι]
  [finν : Fintype ν]
  [finκ : Fintype κ]

  E : Type
  [acgE : AddCommGroup E]
  [modE : Module Ω E]

  Φ : Type
  [fieldΦ : Field Φ]
  [algΦ : Algebra Ω Φ]
  x : ι → Ω
  B : ChartBundle ℤ x 2 E
  e : Module.Basis (Fin 2) Ω E
  φ : κ → E →ₗ[Ω] Ω
  δ : ν → Ω
  a : Fin 2 → Φ
  dualSec : T.IsTwistedDualSec B φ
  dualGen : T.IsTwistedDualGen B φ
  detGen : T.IsTwistedDetGen B e δ
  chart : ∃ i, x i ≠ 0
  indep : AlgebraicIndependent Ω a
  arithYY : IsArithVar (T.yyIdeal x δ e φ (a 0)) (D + 1)
  arithWW : IsArithVar (T.wwIdeal x δ e φ (a 0) (a 1)) (D + 2)

  G : ((Σ k, T.yyIdx ι ν κ k) → ℂ) → Matrix κ κ ℂ
  metric : IsEEMetric G
  n : ℕ

  g : MRing (T.wwIdx ι ν κ)

  h : MRing (T.wwIdx ι ν κ)
  g_deg : IsMultiHomog g (T.wwDeg n 1)
  h_deg : IsMultiHomog h (T.wwDeg (n + 3) 0)
  h_nmem : h ∉ T.wwIdeal x δ e φ (a 0) (a 1)
  quot : aeval (T.wwCoord x δ e φ (a 0) (a 1)) g =
    T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) h

attribute [instance] ProjectiveLineBundle.fieldΩ ProjectiveLineBundle.finι ProjectiveLineBundle.finν ProjectiveLineBundle.finκ ProjectiveLineBundle.acgE ProjectiveLineBundle.modE
  ProjectiveLineBundle.fieldΦ ProjectiveLineBundle.algΦ

namespace ProjectiveLineBundle

variable {D : ℕ} (S : ProjectiveLineBundle D)

abbrev WIdx : T.WBlk → Type := T.wwIdx S.ι S.ν S.κ

end ProjectiveLineBundle

section Diag

variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

end Diag

section Powers

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def hermZpow (A : HermLine ι) (m : ℤ) : HermLine ι where
  a := m • A.a
  h z := A.h z ^ m
  pos z hz := zpow_pos (A.pos z hz) m
  smul c z hc := by
    rw [A.smul c z hc, mul_zpow, ← Finset.prod_zpow]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, ← _root_.zpow_mul, mul_comm]

end Powers

section Statements

open ReciprocityTheory.ChartRestriction.G.AI

end Statements

section Inhabit

section Homog

variable {K : Type*} [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem exHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

end Homog

section FS

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem ofMetrics_fs_h (a : K → ℤ) (z : (Σ k, ι k) → ℂ) :
    (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) a).h z =
      ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ a k := by
  simp only [HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]

theorem isSmoothHerm_ofMetrics_fs (a : K → ℤ) :
    IsSmoothHerm (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) a) := by
  have hfun : (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) a).h =
      fun z => ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ a k := funext (ofMetrics_fs_h a)
  unfold IsSmoothHerm
  rw [hfun]
  refine contDiffOn_prod fun k _ => ?_
  have hpos : ∀ z ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
    intro z hz
    obtain ⟨i, hi⟩ := hz k
    exact Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2))
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    ContDiffOn.sqrt (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, ι k))).contDiffOn fun z hz => (hpos z hz).ne'
  have hf0 : ∀ z ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ≠ 0 :=
    fun z hz => (Real.sqrt_pos.2 (hpos z hz)).ne'
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg (a k)
  · simp only [hm, zpow_natCast]
    exact hf.pow m
  · simp only [hm, _root_.zpow_neg, zpow_natCast]
    exact (hf.pow m).inv fun z hz => pow_ne_zero _ (hf0 z hz)

end FS

end Inhabit

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSwap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SwapCycles.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (a a' : K → ℕ) (s s' : MRing ι),
    IsArithVar P d → IsMultiHomog s a → IsMultiHomog s' a' → s ∉ P → s' ∉ P →
    (∀ W, W ∈ divSupp P s → W ∉ divSupp P s') →
    ((divCycle P s).sum fun W m => m • divCycle W s') =
      (divCycle P s').sum fun W m => m • divCycle W s

def GeoNumCut.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι)) (n : ℕ)
    (a : Fin n → K → ℤ) (b : K → ℕ) (t : MRing ι),
    IsMultiProjPrime V → (charOf V).Prime →
    ringKrullDim (MRing ι ⧸ V) = ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    IsMultiHomog t b → t ∉ V →
    geoNum (n + 1) V (Fin.snoc a fun k => (b k : ℤ)) =
      ∑ᶠ U ∈ divSupp V t, (multAt (V ⊔ Ideal.span {t}) U : ℤ) * geoNum n U a

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsWellDefined
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def AddAt {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (n : ℕ) : Prop :=
  ∀ (W : Ideal (MRing ι)) (L : Fin n → HermLine ι) (A C : HermLine ι),
    IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm C →
    I W (n + 1) (Fin.snoc L (A.tensor C)) = I W (n + 1) (Fin.snoc L A) + I W (n + 1) (Fin.snoc L C)

def RPositionAdd.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A C B : HermLine ι) (s : MRing ι),
    AddAt I n → IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSmoothHerm C → IsSmoothHerm B → IsSectionOn P B s →
    recR I P (Fin.snoc L (A.tensor C)) B s = recR I P (Fin.snoc L A) B s + recR I P (Fin.snoc L C) B s

def WellDefined.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin (n + 1) → HermLine ι) (B : HermLine ι) (s t : MRing ι),
    HasRAt I n → AddAt I n → IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm B →
    IsSectionOn P B s → IsSectionOn P B t → recR I P L B s = recR I P L B t

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PChartScalingIndep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace ChartScalingIndep

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {K : Type} [Fintype K] [DecidableEq K]
  {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isHomogeneous_mw {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) :
    V.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι))) := by
  obtain ⟨S, hS, rfl⟩ := hV
  refine Ideal.homogeneous_span _ S fun f hf => ?_
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, mem_weighted_of_isMultiHomog ha⟩

theorem coeff_eq_zero (x : (Σ k, ι k) → Ω) (i : ∀ k, ι k) (hx : ∀ k, x ⟨k, i k⟩ ≠ 0)
    (hV : IsMultiHomogIdeal (RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω)))
    (s : Finset (K →₀ ℕ)) (g : (K →₀ ℕ) → MRingOver F ι)
    (hs : ∑ α ∈ s, aeval (fun q => x q / x ⟨q.1, i q.1⟩) (g α) * ∏ k, x ⟨k, i k⟩ ^ α k = 0) :
    ∀ β ∈ s, aeval (fun q => x q / x ⟨q.1, i q.1⟩) (g β) = 0 := by
  set y : (Σ k, ι k) → Ω := fun q => x q / x ⟨q.1, i q.1⟩ with hy
  have hxy : x = fun q => x ⟨q.1, i q.1⟩ * y q := by
    funext q
    show x q = x ⟨q.1, i q.1⟩ * (x q / x ⟨q.1, i q.1⟩)
    rw [mul_div_cancel₀ _ (hx q.1)]

  choose e₀ he₀ using fun α => exists_homog_chart (⊥ : Ideal (MRingOver F ι)) i (g α)
  set M : K → ℕ := s.sup e₀ with hM
  have hGex : ∀ α, ∃ G : MRingOver F ι, α ∈ s →
      G ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) M ∧
        Ideal.Quotient.mk (chartIdeal ⊥ i) G = Ideal.Quotient.mk (chartIdeal ⊥ i) (g α) := by
    intro α
    by_cases hα : α ∈ s
    · obtain ⟨G, h1, h2⟩ := he₀ α M (Finset.le_sup (f := e₀) hα)
      exact ⟨G, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hα⟩
  choose G hG using hGex
  have hker : chartIdeal (⊥ : Ideal (MRingOver F ι)) i ≤
      RingHom.ker (aeval y : MRingOver F ι →ₐ[F] Ω) := by
    unfold chartIdeal
    refine sup_le bot_le (Ideal.span_le.mpr ?_)
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, aeval_X, map_one]
    show x ⟨k, i k⟩ / x ⟨k, i k⟩ - 1 = 0
    rw [div_self (hx k), sub_self]
  have hGx : ∀ α ∈ s, aeval x (G α) = (∏ k, x ⟨k, i k⟩ ^ M k) * aeval y (g α) := by
    intro α hα
    have h0 := hker (Ideal.Quotient.eq.mp (hG α hα).2)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h0
    rw [← h0]
    have h := aeval_blockScale (isMultiHomog_of_mem_weighted (hG α hα).1) (fun k => x ⟨k, i k⟩) y
    exact (congrArg (fun z => aeval z (G α)) hxy).trans h
  have hxc : ∀ α : K →₀ ℕ,
      aeval x (∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k) = ∏ k, x ⟨k, i k⟩ ^ α k := by
    intro α
    simp [map_prod]
  have hcM : (∏ k, x ⟨k, i k⟩ ^ M k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hx k)

  have hH : (∑ α ∈ s, G α * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k) ∈
      RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.mem_ker, map_sum]
    calc ∑ α ∈ s, aeval x (G α * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k)
        = ∑ α ∈ s, (∏ k, x ⟨k, i k⟩ ^ M k) *
            (aeval y (g α) * ∏ k, x ⟨k, i k⟩ ^ α k) :=
          Finset.sum_congr rfl fun α hα => by rw [map_mul, hGx α hα, hxc, mul_assoc]
      _ = 0 := by rw [← Finset.mul_sum, hs, mul_zero]
  have hmem : ∀ α ∈ s, G α * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k ∈
      weightedHomogeneousSubmodule F (mw (ι := ι)) (M + ⇑α) := fun α hα =>
    SetLike.mul_mem_graded (hG α hα).1 (mem_weighted_of_isMultiHomog (isMultiHomog_coordProd i ⇑α))
  intro β hβ

  have hcomp : weightedHomogeneousComponent (mw (ι := ι)) (M + ⇑β)
      (∑ α ∈ s, G α * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ α k) =
        G β * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ β k := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single β]
    · rw [weightedHomogeneousComponent_of_mem (hmem β hβ), if_pos rfl]
    · intro α hα hne
      rw [weightedHomogeneousComponent_of_mem (hmem α hα), if_neg]
      intro h
      exact hne (DFunLike.coe_injective (add_left_cancel h)).symm
    · intro h
      exact absurd hβ h
  have hβV := weightedHomogeneousComponent_mem_of_mem F (mw (ι := ι)) (isHomogeneous_mw hV) hH (M + ⇑β)
  rw [hcomp, RingHom.mem_ker, map_mul, hGx β hβ, hxc] at hβV
  have hcβ : (∏ k, x ⟨k, i k⟩ ^ β k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hx k)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hβV).resolve_right hcβ)).resolve_left hcM

end ChartScalingIndep

theorem ChartScalingIndep.proof : ChartScalingIndep.Statement := by
  classical
  intro F Ω _ _ _ K _ ι _ x i hx hV
  set y : (Σ k, ι k) → Ω := fun q => x q / x ⟨q.1, i q.1⟩ with hy
  rw [algebraicIndependent_iff]
  intro p hp

  have hq : ∀ α, ∃ a b : MRingOver F ι, aeval y b ≠ 0 ∧
      ((p.coeff α : IntermediateField.adjoin F (Set.range y)) : Ω) * aeval y b = aeval y a := by
    intro α
    obtain ⟨r, hr, t, ht, he⟩ := IntermediateField.mem_adjoin_iff_div.mp (p.coeff α).2
    rw [Algebra.adjoin_range_eq_range_aeval] at hr ht
    obtain ⟨a, rfl⟩ := hr
    obtain ⟨b, rfl⟩ := ht
    change ((p.coeff α : IntermediateField.adjoin F (Set.range y)) : Ω) = aeval y a / aeval y b at he
    by_cases hb : aeval y b = 0
    · refine ⟨0, 1, by simp, ?_⟩
      rw [he, hb, div_zero]
      simp
    · exact ⟨a, b, hb, by rw [he, div_mul_cancel₀ _ hb]⟩
  choose a b hb hab using hq
  set D : MRingOver F ι := ∏ α ∈ p.support, b α with hD
  have hD0 : aeval y D ≠ 0 := by
    rw [hD, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun α _ => hb α
  set g : (K →₀ ℕ) → MRingOver F ι := fun α => a α * ∏ β ∈ p.support.erase α, b β with hg
  have hgD : ∀ α ∈ p.support,
      aeval y (g α) = aeval y D * ((p.coeff α : IntermediateField.adjoin F (Set.range y)) : Ω) := by
    intro α hα
    rw [hg, hD, map_mul, map_prod, map_prod, ← Finset.mul_prod_erase _ _ hα, ← hab α]
    ring
  have h1 : aeval (fun k => x ⟨k, i k⟩) p = ∑ α ∈ p.support,
      ((p.coeff α : IntermediateField.adjoin F (Set.range y)) : Ω) * ∏ k, x ⟨k, i k⟩ ^ α k := by
    conv_lhs => rw [p.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun k => pow_zero _)]
    rfl
  have hsum : ∑ α ∈ p.support, aeval y (g α) * ∏ k, x ⟨k, i k⟩ ^ α k = 0 := by
    calc ∑ α ∈ p.support, aeval y (g α) * ∏ k, x ⟨k, i k⟩ ^ α k
        = aeval y D * aeval (fun k => x ⟨k, i k⟩) p := by
          rw [h1, Finset.mul_sum]
          exact Finset.sum_congr rfl fun α hα => by rw [hgD α hα, mul_assoc]
      _ = 0 := by rw [hp, mul_zero]
  have h0 := ChartScalingIndep.coeff_eq_zero x i hx hV p.support g hsum
  refine MvPolynomial.ext _ _ fun α => ?_
  change p.coeff α = 0
  by_cases hα : α ∈ p.support
  · have h2 := h0 α hα
    rw [hgD α hα] at h2
    have h3 := (mul_eq_zero.mp h2).resolve_left hD0
    exact_mod_cast h3
  · exact notMem_support_iff.mp hα

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogTwoXc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

def RegularityProductFormula.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (f g : MRing ι) (a : K → ℕ),
    IsArithVar P 1 → IsMultiHomog f a → IsMultiHomog g a → f ∉ P → g ∉ P →
    vertR P (Fin.elim0 : Fin 0 → HermLine ι) f - vertR P (Fin.elim0 : Fin 0 → HermLine ι) g =
      ptsIntegral P (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ)
        (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖))

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityPointsSum_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 →
    ∃ R : Finset ((Σ k, ι k) → ℂ), (∀ t ∈ R, t ∈ mcPts P) ∧
      (∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t) ∧
      ∀ h : ((Σ k, ι k) → ℂ) → ℝ,
        (∀ z z', z ∈ mcPts P → SameOrbit z z' → h z = h z') →
        ptsIntegral P (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) h = ∑ t ∈ R, h t

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.IsHomogeneousOfIsMultiHomogOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

section Helpers

variable {F : Type} [Field F]

theorem linearForm_fin_one_eq {g : MvPolynomial (Fin 1) F} (hg : g.IsHomogeneous 1) :
    g = C (AddMonoidAlgebra.coeff g (Finsupp.single 0 1)) * X 0 := by
  ext d
  rw [coeff_C_mul, coeff_X]
  by_cases h : Finsupp.single 0 1 = d
  · subst h
    simp
  · rw [if_neg h, mul_zero]
    by_contra hne
    apply h
    have hw := hg hne
    refine Finsupp.ext fun i => ?_
    fin_cases i
    simp [Finsupp.weight_apply, Finsupp.sum_fintype] at hw ⊢
    omega

theorem isHomogeneous_of_isMultiHomog_one {K₀ : Type} [Fintype K₀] {ι₀ : K₀ → Type}
    [∀ k, Fintype (ι₀ k)] (hK : Fintype.card K₀ = 1) {f : MRingOver F ι₀}
    (hf : IsMultiHomog f fun _ => 1) : f.IsHomogeneous 1 := by
  intro d hd
  have h := hf d (mem_support_iff.mpr hd)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
  rw [Fintype.sum_sigma]
  simp [h, hK]

end Helpers

theorem LineFibreBlocks.proof (hLin : LinearQuotient.Statement) : LineFibreBlocks.Statement := by
  intro F _ K₀ _ ι₀ _ k₀ Q J hk hQ ⟨S, hS, hQS⟩ hJ m
  classical
  have hK : Fintype.card K₀ = 1 := Fintype.card_eq_one_iff.mpr ⟨k₀, hk⟩
  have hQp : Q.IsPrime := hQ.1.1
  obtain ⟨i₀, hi₀⟩ := hQ.1.2.2 k₀
  set ℓ : MRingOver F ι₀ := X ⟨k₀, i₀⟩ with hℓdef
  obtain ⟨r, φ, hφs, hφk, hφX⟩ := hLin F (Σ k, ι₀ k) (insert ℓ S) (by
    rintro f (rfl | hf)
    · exact isHomogeneous_X F _
    · exact isHomogeneous_of_isMultiHomog_one hK (hS f hf))
  set W : Ideal (MRingOver F ι₀) := RingHom.ker φ with hWdef
  have hQW : Q ⊔ Ideal.span {ℓ} = W := by
    rw [hφk, Ideal.span_insert, hQS, sup_comm]
  have hWp : W.IsPrime := RingHom.ker_isPrime φ
  have hWmin : W ∈ (Q ⊔ Ideal.span {ℓ}).minimalPrimes := by
    rw [hQW, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl

  have hdim := cyc_dim_quot_minimal_add_one hi₀ hWmin (fun h => by
    rw [hQ.2] at h
    exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
  have hdimW : ringKrullDim (MRingOver F ι₀ ⧸ W) = ((1 : ℕ) : WithBot ℕ∞) :=
    cyc_withBot_eq_of_add_one (by rw [hdim, hQ.2, hK])
  rw [hWdef, ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerAlgEquivOfSurjective hφs).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add] at hdimW
  have hr : r = 1 := by
    have h : ENat.card (Fin r) = (1 : ℕ∞) := WithBot.coe_injective hdimW
    rw [ENat.card_eq_coe_natCard] at h
    have h2 : Nat.card (Fin r) = 1 := by exact_mod_cast h
    simpa using h2
  subst hr

  have hex : ∃ s, (X s : MRingOver F ι₀) ∉ W := by
    by_contra hno
    simp only [not_exists, not_not] at hno
    have hφ0 : φ = (Algebra.ofId F _).comp (aeval fun _ => (0 : F)) := by
      apply MvPolynomial.algHom_ext
      intro s
      have h0 := hno s
      rw [hWdef, RingHom.mem_ker] at h0
      simp [h0]
    obtain ⟨f, hf⟩ := hφs (X 0)
    rw [hφ0] at hf
    have := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single 0 1)) hf
    simp [Algebra.ofId_apply, coeff_X, algebraMap_eq, coeff_C] at this
    rw [if_neg (Finsupp.single_ne_zero.mpr one_ne_zero).symm] at this
    exact zero_ne_one this
  obtain ⟨s₁, hs₁⟩ := hex
  have hWrel : IsRelevant W := fun k => by
    obtain rfl : k = s₁.1 := (hk k).trans (hk s₁.1).symm
    exact ⟨s₁.2, hs₁⟩

  have hdivℓ : divCycle Q ℓ = Finsupp.single W 1 := inh_divCycle_prime Q ℓ W hQW hWrel
  have hℓpow : ∀ n : ℕ, ℓ ^ n ∉ Q := fun n h => hi₀ (hQp.mem_of_pow_mem n h)
  have hdivpow : ∀ n : ℕ, divCycle Q (ℓ ^ n) = Finsupp.single W n := by
    intro n
    induction n with
    | zero => simp [divCycle_one]
    | succ n ih =>
      rw [pow_succ, divCycle_mul hQp (hℓpow n) hi₀, ih, hdivℓ, ← Finsupp.single_add]

  have hWpv : IsProjVarF W 0 :=
    isProjVarF_of_mem_divSupp (n := 0) hQ (isMultiHomog_X k₀ i₀) hi₀ ⟨hWmin, hWrel⟩
  set j : ∀ k, ι₀ k := fun k => (hWrel k).choose with hjdef
  have hj : IsChart W j := fun k => (hWrel k).choose_spec
  set p₁ : Σ k, ι₀ k := ⟨k₀, j k₀⟩ with hp₁
  set a : (Σ k, ι₀ k) → F := fun s => AddMonoidAlgebra.coeff (φ (X s)) (Finsupp.single 0 1) with hadef
  have hφXs : ∀ s, φ (X s) = C (a s) * X 0 := fun s => linearForm_fin_one_eq (hφX s)
  have ha1 : a p₁ ≠ 0 := by
    intro h0
    apply hj k₀
    rw [hWdef, RingHom.mem_ker, hφXs, h0, C_0, zero_mul]
  set c : (Σ k, ι₀ k) → F := fun s => a s / a p₁ with hcdef
  have hev : aeval c = (aeval fun _ : Fin 1 => (a p₁)⁻¹).comp φ := by
    apply MvPolynomial.algHom_ext
    intro s
    simp [hφXs, hcdef, div_eq_mul_inv]
  have hpt : ∀ L : Fin 0 → K₀ → ℤ, J W 0 L = 1 := by
    intro L
    rw [hJ.1 W L j hWpv hj]
    unfold ptDeg chartIdeal
    rw [inh_finrank_quot _ c]
    · rfl
    · apply sup_le
      · intro f hf
        rw [RingHom.mem_ker, ← coe_aeval_eq_eval, hev]
        rw [hWdef, RingHom.mem_ker] at hf
        simp [hf]
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        obtain rfl : k = k₀ := hk k
        rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, eval_X, map_one]
        exact sub_eq_zero.mpr (div_self ha1)
    · intro s
      have h1 : X s - C (c s) * X p₁ ∈ W := by
        rw [hWdef, RingHom.mem_ker, map_sub, map_mul, algHom_C, hφXs, hφXs, ← mul_assoc,
          algebraMap_eq, ← C_mul, hcdef, div_mul_cancel₀ _ ha1, sub_self]
      have h2 : C (c s) * (X p₁ - 1) ∈
          Ideal.span (Set.range fun k => (X ⟨k, j k⟩ : MRingOver F ι₀) - 1) :=
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k₀, rfl⟩)
      have e : X s - C (c s) = (X s - C (c s) * X p₁) + C (c s) * (X p₁ - 1) := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)

  have e1 : (![m] : Fin 1 → K₀ → ℤ) = Fin.snoc (α := fun _ => K₀ → ℤ) Fin.elim0 m := by
    funext i
    fin_cases i
    rfl
  have hmk : ∀ k, m k = m k₀ := fun k => by rw [hk k]
  have hhomℓ : ∀ n : ℕ, IsMultiHomog (ℓ ^ n) (fun _ => n) := fun n => by
    have := isMultiHomog_pow (isMultiHomog_X (F := F) (ι := ι₀) k₀ i₀) n
    convert this using 1
    funext k
    rw [hk k]
    simp
  have h1Q : (1 : MRingOver F ι₀) ∉ Q := fun h => hQp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  rw [e1]
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg (m k₀)
  · rw [hJ.2 Q 0 Fin.elim0 m (ℓ ^ n) 1 hQ ⟨fun _ => n, 0, hhomℓ n, isMultiHomog_one, hℓpow n, h1Q,
      fun k => by simp [hmk k, hn]⟩, ratDiv, hdivpow, divCycle_one]
    simp [inh_cycEval_single, hpt, hn]
  · rw [hJ.2 Q 0 Fin.elim0 m 1 (ℓ ^ n) hQ ⟨0, fun _ => n, isMultiHomog_one, hhomℓ n, h1Q, hℓpow n,
      fun k => by simp [hmk k, hn]⟩, ratDiv, hdivpow, divCycle_one]
    simp only [Finsupp.mapRange_zero, Finsupp.mapRange_single, zero_sub]
    rw [← Finsupp.single_neg, inh_cycEval_single, hpt, hn]
    simp

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PChoice
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace Choice

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]

theorem homog_mul {f g : MRingOver R ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem homog_one : IsMultiHomog (1 : MRingOver R ι) 0 := by
  classical
  intro m hm k
  have hm' : m = 0 := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hm) (by simp [MvPolynomial.coeff_one, Ne.symm h])
  subst hm'
  simp


open Classical in
theorem homog_X (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRingOver R ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  have hm' : m = Finsupp.single ⟨k, i⟩ 1 := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hm) (by rw [MvPolynomial.coeff_X]; simp [Ne.symm h])
  subst hm'
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, this, h, Pi.single_apply]

theorem homog_pow {f : MRingOver R ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (homog_one (R := R) (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact homog_mul ih hf

theorem homog_zero (a : K → ℕ) : IsMultiHomog (0 : MRingOver R ι) a := by
  intro m hm
  simp at hm

theorem homog_add {f g : MRingOver R ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem homog_sum {β : Type*} (s : Finset β) (f : β → MRingOver R ι) {a : K → ℕ}
    (h : ∀ b ∈ s, IsMultiHomog (f b) a) : IsMultiHomog (∑ b ∈ s, f b) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using homog_zero (R := R) (ι := ι) a
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    exact homog_add (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

theorem homog_prod {β : Type*} (s : Finset β) (f : β → MRingOver R ι) (a : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (f b) (a b)) : IsMultiHomog (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using homog_one (R := R) (ι := ι)
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact homog_mul (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

theorem homog_coordProd (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRingOver R ι) ^ d k) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRingOver R ι) ^ d k)
      (∑ k ∈ s, d k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (homog_one (R := R) (ι := ι))
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact homog_mul (homog_pow (homog_X k (c k)) _) ih
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [e] at this

theorem coordProd_not_mem {V : Ideal (MRingOver R ι)} (hV : V.IsPrime) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRingOver R ι) ∉ V) (d : K → ℕ) :
    (∏ k, (X ⟨k, c k⟩ : MRingOver R ι) ^ d k) ∉ V := by
  intro h
  obtain ⟨k, -, hk⟩ := (hV.prod_mem_iff).mp h
  exact hc k (hV.mem_of_pow_mem _ hk)

theorem exists_form_avoid (S : Set (Ideal (MRingOver R ι))) (hS : S.Finite)
    (hS' : ∀ W ∈ S, IsMultiProjPrime W) :
    ∃ d₀ : K → ℕ, ∀ d : K → ℕ, d₀ ≤ d →
      ∃ f : MRingOver R ι, IsMultiHomog f d ∧ ∀ W ∈ S, f ∉ W := by
  classical
  set T : Finset (Ideal (MRingOver R ι)) :=
    hS.toFinset.filter (fun W => ∀ W' ∈ S, W ≤ W' → W' = W) with hT
  have hTS : ∀ W ∈ T, W ∈ S := fun W hW => hS.mem_toFinset.mp (Finset.mem_filter.mp hW).1
  have hTmax : ∀ W ∈ T, ∀ W' ∈ S, W ≤ W' → W' = W := fun W hW => (Finset.mem_filter.mp hW).2
  have hle : ∀ W ∈ S, ∃ W' ∈ T, W ≤ W' := by
    intro W hW
    obtain ⟨W', hWW', hW'⟩ := hS.exists_le_maximal hW
    exact ⟨W', Finset.mem_filter.mpr ⟨hS.mem_toFinset.mpr hW'.prop,
      fun W'' hW'' h => le_antisymm (hW'.2 hW'' h) h⟩, hWW'⟩
  have hgen : ∀ W ∈ T, ∀ W' ∈ T, W' ≠ W →
      ∃ g : MRingOver R ι, ∃ a : K → ℕ, IsMultiHomog g a ∧ g ∈ W' ∧ g ∉ W := by
    intro W hW W' hW' hne
    obtain ⟨S', hS'h, hS'eq⟩ := (hS' W' (hTS W' hW')).2.1
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    apply hne
    refine (hTmax W' hW' W (hTS W hW) ?_).symm
    rw [hS'eq, Ideal.span_le]
    intro g hg
    obtain ⟨a, ha⟩ := hS'h g hg
    exact hc g a ha (hS'eq ▸ Ideal.subset_span hg)
  choose! gen degG hgenH hgenMem hgenNot using hgen
  set a : Ideal (MRingOver R ι) → MRingOver R ι := fun W => ∏ W' ∈ T.erase W, gen W W' with ha
  set δ : Ideal (MRingOver R ι) → K → ℕ := fun W => ∑ W' ∈ T.erase W, degG W W' with hδ
  have haH : ∀ W ∈ T, IsMultiHomog (a W) (δ W) := fun W hW =>
    homog_prod _ _ _ fun W' hW' =>
      hgenH W hW W' (Finset.mem_of_mem_erase hW') (Finset.ne_of_mem_erase hW')
  have haNot : ∀ W ∈ T, a W ∉ W := by
    intro W hW h
    obtain ⟨W', hW', hg⟩ := ((hS' W (hTS W hW)).1.prod_mem_iff).mp h
    exact hgenNot W hW W' (Finset.mem_of_mem_erase hW') (Finset.ne_of_mem_erase hW') hg
  have haMem : ∀ W ∈ T, ∀ W'' ∈ T, W'' ≠ W → a W ∈ W'' := by
    intro W hW W'' hW'' hne
    have hmem : W'' ∈ T.erase W := Finset.mem_erase.mpr ⟨hne, hW''⟩
    show (∏ W' ∈ T.erase W, gen W W') ∈ W''
    rw [← Finset.mul_prod_erase _ _ hmem]
    exact Ideal.mul_mem_right _ _ (hgenMem W hW W'' hW'' hne)
  refine ⟨∑ W ∈ T, δ W, fun d hd => ?_⟩
  have hδd : ∀ W ∈ T, δ W ≤ d := fun W hW =>
    le_trans (Finset.single_le_sum (f := δ) (fun _ _ _ => Nat.zero_le _) hW) hd
  have hrel : ∀ W ∈ T, IsRelevant W := fun W hW => (hS' W (hTS W hW)).2.2
  set m : Ideal (MRingOver R ι) → MRingOver R ι := fun W =>
    if h : IsRelevant W then ∏ k, (X ⟨k, (h k).choose⟩ : MRingOver R ι) ^ (d k - δ W k) else 0
    with hm
  have hmH : ∀ W ∈ T, IsMultiHomog (m W) (d - δ W) := by
    intro W hW
    simp only [hm, dif_pos (hrel W hW)]
    exact homog_coordProd _ _
  have hmNot : ∀ W ∈ T, m W ∉ W := by
    intro W hW
    simp only [hm, dif_pos (hrel W hW)]
    exact coordProd_not_mem (hS' W (hTS W hW)).1 _ (fun k => ((hrel W hW) k).choose_spec) _
  refine ⟨∑ W ∈ T, a W * m W, ?_, ?_⟩
  · apply homog_sum
    intro W hW
    have := homog_mul (haH W hW) (hmH W hW)
    rwa [add_tsub_cancel_of_le (hδd W hW)] at this
  · have key : ∀ W₀ ∈ T, (∑ W ∈ T, a W * m W) ∉ W₀ := by
      intro W₀ hW₀ h
      rw [← Finset.add_sum_erase _ _ hW₀] at h
      have hrest : (∑ W ∈ T.erase W₀, a W * m W) ∈ W₀ :=
        Ideal.sum_mem _ fun W hW => Ideal.mul_mem_right _ _
          (haMem W (Finset.mem_of_mem_erase hW) W₀ hW₀ (Finset.ne_of_mem_erase hW).symm)
      have h1 := (Ideal.add_mem_iff_left _ hrest).mp h
      rcases (hS' W₀ (hTS W₀ hW₀)).1.mem_or_mem h1 with h2 | h2
      · exact haNot W₀ hW₀ h2
      · exact hmNot W₀ hW₀ h2
    intro W hW h
    obtain ⟨W', hW', hle'⟩ := hle W hW
    exact key W' hW' (hle' h)

end Choice

end GroundTheory.Heights₂.Heights.Inter
end
end
