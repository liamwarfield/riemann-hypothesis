module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloOnDivCongr

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl

section Cell

variable {Ψ : Type} {N j : ℕ}

def Sep (keep : Ψ × Fin N → Prop) (q : LowIdx Ψ N j) : Prop :=
  ∃ i, keep (q.1.1, i) ∧ IsProperStep N j i ∧ q.1.2.2 ∈ stepCols N j i ∧ q.1.2.1 ∉ stepCols N j i

abbrev PIdx (j : ℕ) (keep : Ψ × Fin N → Prop) : Type := {q : LowIdx Ψ N j // Sep keep q}

def cExt (keep : Ψ × Fin N → Prop) (c : PIdx j keep → ℂ) : LowIdx Ψ N j → ℂ :=
  fun q => if h : Sep keep q then c ⟨q, h⟩ else 0

def pMat (keep : Ψ × Fin N → Prop) (c : PIdx j keep → ℂ) (τ : Ψ) : Matrix (Fin N) (Fin N) ℂ :=
  lowMat (cExt keep c) τ

def pSteps (j : ℕ) (keep : Ψ × Fin N → Prop) (τ : Ψ) (b : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun i => keep (τ, i) ∧ IsProperStep N j i ∧ b ∈ stepCols N j i

def pStep (j : ℕ) (keep : Ψ × Fin N → Prop) (τ : Ψ) (b : Fin N) : Fin N :=
  if h : (pSteps j keep τ b).Nonempty then (pSteps j keep τ b).min' h else b

def pSgn (S : Finset (Fin N)) (a b : Fin N) : ℂ :=
  minorIJ (1 + Matrix.single a b (1 : ℂ)) (insert a (S.erase b)) S

end Cell

section Param

variable {n e : ℕ} {Λ : Type}

def pB (ε : Fin n ⊕ Λ ≃ Fin e) (w : Fin e → ℂ) : Fin n → ℂ := fun i => w (ε (Sum.inl i))

def pL (ε : Fin n ⊕ Λ ≃ Fin e) (w : Fin e → ℂ) : Λ → ℂ := fun q => w (ε (Sum.inr q))

def pD (ε : Fin n ⊕ Λ ≃ Fin e) (V : Set (Fin n → ℂ)) : Set (Fin e → ℂ) := {w | pB ε w ∈ V}

end Param

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)] {n e : ℕ}

def upV (v : (Σ k, ιk k) → (Σ k, ι k)) (z : (Σ k, ιk k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => if h : ∃ q', v q' = q then z h.choose else 0

def pBase (M : FlagModel y Ψ N j) (v : (Σ k, ιk k) → (Σ k, ι k)) (z : (Σ k, ιk k) → ℂ) :
    (Σ k, baseIdx ι M.blk k) → ℂ := basePart M.blk (upV v z)

def pRead (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (keep : Ψ × Fin N → Prop)
    (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (τ : Ψ) (a b : Fin N) : ℂ :=
  (M.blk (τ, pStep j keep τ b)).elim 0 fun k =>
    twMinor M F zb (pStep j keep τ b) k (h τ)⁻¹ z (insert a ((stepCols N j (pStep j keep τ b)).erase b)) /
      (pSgn (stepCols N j (pStep j keep τ b)) a b *
        twMinor M F zb (pStep j keep τ b) k (h τ)⁻¹ z (stepCols N j (pStep j keep τ b)))

def pH (keep : Ψ × Fin N → Prop) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e) (τ : Ψ)
    (w : Fin e → ℂ) : Matrix (Fin N) (Fin N) ℂ := h τ * pMat keep (pL ε w) τ

def pPhi (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (keep : Ψ × Fin N → Prop)
    (v : (Σ k, ιk k) → (Σ k, ι k)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e) (w : Fin e → ℂ) : (Σ k, ιk k) → ℂ :=
  fun q => flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w) (v q)

def IsPCtx (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsBlockMap κ v ∧ (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) ∧
    M.IsFrame F ∧ IsBaseChart M Rb F kb V bl ∧
    (∀ z ∈ mcPts (mCoordIdeal M.x), SameOrbit (Rb.lift (r z) (r z)) z) ∧ ContinuousOn r (mcPts (mCoordIdeal M.x)) ∧
    ∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0

def pO (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop)
    (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : Set ((Σ k, ιk k) → ℂ) :=
  {z | z ∈ mcPts (mCoordIdeal (y ∘ v)) ∧ r (pBase M v z) ∈ (Rb.A.chart kb).source ∧
    Rb.A.chart kb (r (pBase M v z)) ∈ V ∧
    ∀ p k, keep p → M.blk p = some k →
      twMinor M F (pBase M v z) p.2 k (h p.1)⁻¹ (upV v z) (stepCols N j p.2) ≠ 0}

def pRho (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop)
    (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n)
    (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (ε : Fin n ⊕ PIdx j keep ≃ Fin e) (z : (Σ k, ιk k) → ℂ) : Fin e → ℂ := fun i =>
  match ε.symm i with
  | Sum.inl l => Rb.A.chart kb (r (pBase M v z)) l
  | Sum.inr q => pRead M F keep (pBase M v z) h (upV v z) q.1.1.1 q.1.1.2.1 q.1.1.2.2

theorem upV_apply {v : (Σ k, ιk k) → (Σ k, ι k)} (hv : Function.Injective v) (z : (Σ k, ιk k) → ℂ) (q : Σ k, ιk k) :
    upV v z (v q) = z q := by
  have h : ∃ q', v q' = v q := ⟨q, rfl⟩
  simp only [upV, dif_pos h]
  rw [hv h.choose_spec]

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.PFl
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticProjectionBijective
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticProjectionBijective
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem re_pi_bijective : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), Function.Bijective FA.Re.π := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA
  have hdeg0 := FA.Re.degree
  unfold ReciprocityTheory.AnForm.M.IsDegreeOff at hdeg0
  have hdeg := hdeg0.2.2.2.2.1
  rw [FA.br_empty, FA.deg_one] at hdeg
  have h1 : ∀ x, ∃ a, FA.Re.π ⁻¹' {x} = {a} := fun x => Set.ncard_eq_one.1 (hdeg x (by simp))
  constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := h1 (FA.Re.π a)
    have ha : a ∈ FA.Re.π ⁻¹' {FA.Re.π a} := Set.mem_preimage.2 (Set.mem_singleton _)
    have hb : b ∈ FA.Re.π ⁻¹' {FA.Re.π a} := Set.mem_preimage.2 (Set.mem_singleton_iff.2 hab.symm)
    rw [hc] at ha hb
    exact (Set.mem_singleton_iff.1 ha).trans (Set.mem_singleton_iff.1 hb).symm
  · intro x
    obtain ⟨c, hc⟩ := h1 x
    have hcx : c ∈ FA.Re.π ⁻¹' {x} := by
      rw [hc]
      exact Set.mem_singleton c
    exact ⟨c, Set.mem_singleton_iff.1 (Set.mem_preimage.1 hcx)⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticProjectionBijectiveStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_analytic_projection_bijective : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), Function.Bijective FA.Re.π := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.re_pi_bijective | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.re_pi_bijective | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.re_pi_bijective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbit
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbit
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem sameOrbit_symm' {K : Type} {ι : K → Type} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  rw [inv_mul_cancel_left₀ (hc p.1)]

theorem isValueAt_of_sameOrbit {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {s : Ω} {z z' : (Σ k, ι k) → ℂ} {v : ℂ} (h : SameOrbit z z')
    (hv : IsValueAt x s z' v) : IsValueAt x s z v := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, g, f, hg, hf, hy, heq, hz0, rfl⟩ := hv
  have hprod : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d, g, f, hg, hf, hy, heq, ?_, ?_⟩
  · rw [eval_smul_homog f d hf c]
    exact mul_ne_zero hprod hz0
  · rw [eval_smul_homog g d hg c, eval_smul_homog f d hf c, mul_div_mul_left _ _ hprod]

theorem valAt_eq_of_sameOrbit (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (s : Ω) (z z' : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal x))
    (h : SameOrbit z z') : valAt x s z = valAt x s z' := by
  have hz' : z' ∈ mcPts (mCoordIdeal x) :=
    mem_mcPts_of_sameOrbit (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal x)
      (sameOrbit_symm' h) hz
  by_cases hv : ∃ v, IsValueAt x s z v
  · obtain ⟨v, hv⟩ := hv
    rw [valAt_eq hz hv, valAt_eq hz' (isValueAt_of_sameOrbit (sameOrbit_symm' h) hv)]
  · have hv' : ¬ ∃ v, IsValueAt x s z' v := fun ⟨v, hw⟩ => hv ⟨v, isValueAt_of_sameOrbit h hw⟩
    rw [valAt, valAt, dite_eq_right hv, dite_eq_right hv']

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbitStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_constant_on_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (s : Ω) (z z' : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal x) → SameOrbit z z' → valAt x s z = valAt x s z' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSecond
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSecond
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

section Minor

variable {N : ℕ}

theorem minorIJ_mul_one_add_single (H : Matrix (Fin N) (Fin N) ℂ) (I C : Finset (Fin N)) {ca cb : Fin N} (hlt : ca < cb)
    (hiff : ca ∈ C ↔ cb ∈ C) (t : ℂ) :
    minorIJ (H * (1 + Matrix.single cb ca t)) I C = minorIJ H I C := by
  have hne : ∀ x, ¬ (x = cb ∧ x = ca) := fun x hx => hlt.ne (hx.2.symm.trans hx.1)
  have hent : ∀ x y, (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) x y =
      (if x = y then 1 else 0) + (if x = cb ∧ y = ca then t else 0) := by
    intro x y
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]
  rw [minorIJ_mul_of_support H _ I C]
  · have h1 : minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) C C = 1 := by
      rw [minorIJ_eq_det _ C C _ rfl rfl, Matrix.det_of_lowerTriangular]
      · refine Finset.prod_eq_one fun x _ => ?_
        rw [Matrix.submatrix_apply, hent, if_pos rfl, if_neg, add_zero]
        rintro ⟨e1, e2⟩
        exact hne _ ⟨e1, e2⟩
      · intro x y hxy
        have hxy' : x < y := hxy
        have hs := (C.orderEmbOfFin rfl).strictMono hxy'
        rw [Matrix.submatrix_apply, hent, if_neg hs.ne, if_neg, add_zero]
        rintro ⟨e1, e2⟩
        rw [e1, e2] at hs
        exact absurd hs (not_lt.mpr hlt.le)
    rw [h1, mul_one]
  · intro k c hc hk
    have hkc : k ≠ c := by
      rintro rfl
      exact hk hc
    rw [hent, if_neg hkc, if_neg, add_zero]
    rintro ⟨e1, e2⟩
    rw [e1] at hk
    rw [e2] at hc
    exact hk (hiff.mp hc)

theorem mem_stepCols_iff {j : ℕ} {a b ca cb i : Fin N} (hb : (b : ℕ) = a + 1) (h2 : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (hi : i ≠ a) :
    ca ∈ stepCols N j i ↔ cb ∈ stepCols N j i := by
  have h3 := i.2
  have h4 := b.2
  have h5 := ca.2
  have h6 := cb.2
  have hi' : (i : ℕ) ≠ a := fun e => hi (Fin.ext e)
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold lastCol at hca
  split_ifs at hca ⊢ <;> omega

end Minor

section Low

variable {Ψ : Type} {N j : ℕ}

theorem lowMat_isBlockDiag (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : IsBlockDiag j (lowMat c τ) := by
  intro x y hxy
  unfold lowMat
  rw [_root_.dite_eq_right (fun e => hxy e.2), if_neg]
  rintro rfl
  exact hxy Iff.rfl

theorem lowMat_det (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : (lowMat c τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun x _ => ?_
    unfold lowMat
    rw [_root_.dite_eq_right (fun e => lt_irrefl _ e.1), if_pos rfl]
  · intro x y hxy
    have hxy' : x < y := hxy
    unfold lowMat
    rw [_root_.dite_eq_right (fun e => lt_asymm hxy' e.1), if_neg hxy'.ne]

theorem analytic_wH {n e : ℕ} (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ)
    (r s : Fin N) (S : Set (Fin e → ℂ)) : AnalyticOnNhd ℂ (fun w => wH h ε τ' w r s) S := by
  have hl : ∀ x, AnalyticOnNhd ℂ (fun w => lowMat (wL ε w) τ' x s) S := by
    intro x
    unfold lowMat
    by_cases hh : s < x ∧ ((x : ℕ) < N - j ↔ (s : ℕ) < N - j)
    · simp only [dif_pos hh, wL]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ)
        (ε (Sum.inr (Sum.inl ⟨(τ', x, s), hh⟩)))).analyticOnNhd _
    · simp only [_root_.dite_eq_right hh]
      exact analyticOnNhd_const
  have : (fun w => wH h ε τ' w r s) = fun w => ∑ x, h τ' r x * lowMat (wL ε w) τ' x s := by
    funext w
    simp only [wH, Matrix.mul_apply]
  rw [this]
  exact Finset.analyticOnNhd_fun_sum _ fun x _ => analyticOnNhd_const.mul (hl x)

end Low

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {F : FrameData ι Ψ N M.Ω M.blk}
  {zb : (Σ k, baseIdx ι M.blk k) → ℂ} {H : Ψ → Matrix (Fin N) (Fin N) ℂ}

theorem flagZ_base (k : NonPluckerBlocks M.blk) (m : ι k.1) : flagZ M F zb H ⟨k.1, m⟩ = zb ⟨k, m⟩ := by
  unfold flagZ
  rw [_root_.dite_eq_right (fun e => by obtain ⟨p, hp⟩ := e; exact k.2 p hp)]

theorem flagZ_step {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) (m : ι k) :
    flagZ M F zb H ⟨k, m⟩ = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ (H p.1) I (stepCols N j p.2) := by
  have e : ∃ p, M.blk p = some k := ⟨p, hp⟩
  have hc : e.choose = p := M.blk_inj _ _ _ e.choose_spec hp
  unfold flagZ
  simp only [dif_pos e, hc]

variable {k₀ : K} {τ : Ψ} {ca cb : Fin N} {t : ℂ}

theorem fst_sqZ (k : K) (m : ι k) :
    fstPt k₀ (sqZ M F zb H k₀ τ ca cb t) ⟨k, m⟩ = flagZ M F zb H ⟨k, m⟩ := rfl

theorem snd_sqZ_ne {k : K} (hk : k ≠ k₀) (m : ι k) :
    sndPt k₀ (sqZ M F zb H k₀ τ ca cb t) ⟨k, m⟩ = flagZ M F zb H ⟨k, m⟩ := by
  show sqZ M F zb H k₀ τ ca cb t (v₁ k₀ ⟨k, m⟩) = _
  rw [v₁_ne (p := ⟨k, m⟩) hk]
  rfl

theorem snd_sqZ_self (m : ι k₀) :
    sndPt k₀ (sqZ M F zb H k₀ τ ca cb t) ⟨k₀, m⟩ =
      flagZ M F zb (Function.update H τ (H τ * (1 + Matrix.single cb ca t))) ⟨k₀, m⟩ := by
  show sqZ M F zb H k₀ τ ca cb t (v₁ k₀ ⟨k₀, m⟩) = _
  rw [v₁_self]
  rfl

theorem basePart_fst : basePart M.blk (fstPt k₀ (sqZ M F zb H k₀ τ ca cb t)) = zb := by
  funext q
  obtain ⟨k, m⟩ := q
  exact flagZ_base k m

theorem basePart_snd {a : Fin N} (hk₀ : M.blk (τ, a) = some k₀) :
    basePart M.blk (sndPt k₀ (sqZ M F zb H k₀ τ ca cb t)) = zb := by
  funext q
  obtain ⟨k, m⟩ := q
  have hne : k.1 ≠ k₀ := fun e => k.2 (τ, a) (by rw [hk₀, e])
  show sndPt k₀ (sqZ M F zb H k₀ τ ca cb t) ⟨k.1, m⟩ = _
  rw [snd_sqZ_ne hne]
  exact flagZ_base k m

theorem exact_fst (hn : ∀ k, zb ⟨k, F.c k⟩ = 1) (p : Ψ × Fin N) :
    M.ExactAt F p (fstPt k₀ (sqZ M F zb H k₀ τ ca cb t)) (H p.1) := by
  refine ⟨fun k => by rw [basePart_fst]; exact hn k, fun k hk m => ?_⟩
  rw [fst_sqZ, flagZ_step hk, basePart_fst]

theorem exact_snd {a : Fin N} (hk₀ : M.blk (τ, a) = some k₀) (hlt : ca < cb)
    (hiff : ∀ i, i ≠ a → (ca ∈ stepCols N j i ↔ cb ∈ stepCols N j i))
    (hn : ∀ k, zb ⟨k, F.c k⟩ = 1) (τ' : Ψ) (i : Fin N) :
    M.ExactAt F (τ', i) (sndPt k₀ (sqZ M F zb H k₀ τ ca cb t))
      (if τ' = τ then H τ * (1 + Matrix.single cb ca t) else H τ') := by
  refine ⟨fun k => by rw [basePart_snd hk₀]; exact hn k, fun k hk m => ?_⟩
  rw [basePart_snd hk₀]
  by_cases hkk : k = k₀
  · subst hkk
    have hp : (τ', i) = (τ, a) := M.blk_inj _ _ _ hk hk₀
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    rw [snd_sqZ_self, flagZ_step hk₀, if_pos rfl, Function.update_self]
  · rw [snd_sqZ_ne hkk, flagZ_step hk]
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases hτ : τ' = τ
    · subst hτ
      have hia : i ≠ a := by
        rintro rfl
        exact hkk (Option.some_injective _ (hk.symm.trans hk₀))
      rw [if_pos rfl, minorIJ_mul_one_add_single _ _ _ hlt (hiff i hia)]
    · rw [if_neg hτ]

end Flag

theorem chart_exact : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → (∀ τ' r s, AnalyticOnNhd ℂ (fun w => wH h ε τ' w r s) (wD ε V)) ∧ ∀ w ∈ wD ε V, (∀ τ', IsBlockDiag j (wH h ε τ' w) ∧ (wH h ε τ' w).det ≠ 0) ∧ baseOf M k₀ (wPhi M F bl h ε k₀ τ ca cb w) = bl (wB ε w) ∧ ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) (fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) (wH h ε τ' w) ∧ ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) (sndPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) (if τ' = τ then wH h ε τ w * (1 + Matrix.single cb ca (wT ε w)) else wH h ε τ' w) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hW
  obtain ⟨hb, h2, hk₀, hca, hcb, -, -, hB, -, -, hh⟩ := hW
  have hlt : ca < cb := by
    rw [Fin.lt_def]
    omega
  refine ⟨fun τ' r s => analytic_wH h ε τ' r s _, fun w hw => ⟨fun τ' => ⟨?_, ?_⟩, ?_, fun τ' i => ⟨?_, ?_⟩⟩⟩
  · exact isBlockDiag_mul (hh τ').1 (lowMat_isBlockDiag _ _)
  · rw [wH, Matrix.det_mul, lowMat_det, mul_one]
    exact (hh τ').2
  · exact basePart_fst
  · exact exact_fst (H := fun τ' => wH h ε τ' w) ((hB.2.2.2.2 _ hw).2.1) (τ', i)
  · exact exact_snd (H := fun τ' => wH h ε τ' w) hk₀ hlt
      (fun i hi => mem_stepCols_iff hb h2 hca hcb hi) ((hB.2.2.2.2 _ hw).2.1) τ' i

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSecondStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → (∀ τ' r s, AnalyticOnNhd ℂ (fun w => wH h ε τ' w r s) (wD ε V)) ∧ ∀ w ∈ wD ε V, (∀ τ', IsBlockDiag j (wH h ε τ' w) ∧ (wH h ε τ' w).det ≠ 0) ∧ baseOf M k₀ (wPhi M F bl h ε k₀ τ ca cb w) = bl (wB ε w) ∧ ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) (fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) (wH h ε τ' w) ∧ ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) (sndPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) (if τ' = τ then wH h ε τ w * (1 + Matrix.single cb ca (wT ε w)) else wH h ε τ' w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact.chart_exact | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact.chart_exact | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact.chart_exact <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationBijectiveDegreeOne
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationBijectiveDegreeOne
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem realis_bijective_of_degree_one : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P), Re.deg = 1 → Re.br = ∅ → Function.Bijective Re.π := by
  intro K _ ι _ D σ S P Re h1 h2
  have hd := Re.degree
  rw [h1, h2] at hd
  obtain ⟨g, hgl, hgr, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_holoMap_inverse_of_degree_one S.A Re.R.A Re.π Re.holo hd
  exact Function.bijective_iff_has_inverse.2 ⟨g, hgl, hgr⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationBijectiveDegreeOneStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisation_bijective_degree_one : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P), Re.deg = 1 → Re.br = ∅ → Function.Bijective Re.π := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.realis_bijective_of_degree_one | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.realis_bijective_of_degree_one | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.realis_bijective_of_degree_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PluckerNonvanishingOrbitInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PluckerNonvanishingOrbitInvariant
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem plk_ne_zero_iff_of_sameOrbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (z z' : (Σ k, ι k) → ℂ) (p : Ψ × Fin N), SameOrbit z z' → (FC.plk M F b z p ≠ 0 ↔ FC.plk M F b z' p ≠ 0) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F b z z' p h
  obtain ⟨c, hc, rfl⟩ := h
  unfold FC.plk
  cases hb : M.blk p with
  | none => simp
  | some k =>
    simp only [Option.elim, mul_left_comm _ (c k), ← Finset.mul_sum, ne_eq, mul_eq_zero, hc k, false_or]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PluckerNonvanishingOrbitInvariantStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plucker_nonvanishing_orbit_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (z z' : (Σ k, ι k) → ℂ) (p : Ψ × Fin N), SameOrbit z z' → (FC.plk M F b z p ≠ 0 ↔ FC.plk M F b z' p ≠ 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentPluckerOrbit
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentPluckerOrbit
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem mul_one_add_single_apply {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (ca cb : Fin N) (t : ℂ) (r c : Fin N) :
    (h * (1 + Matrix.single cb ca t)) r c = h r c + if c = ca then t * h r cb else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  simp only [Matrix.single_apply]
  split_ifs with hc
  · subst hc
    simp [mul_comm]
  · simp [Ne.symm hc]

theorem minorIJ_mul_transvection {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (I J : Finset (Fin N)) {ca cb : Fin N}
    (hne : ca ≠ cb) (t : ℂ) (hJ : ca ∈ J ↔ cb ∈ J) :
    minorIJ (h * (1 + Matrix.single cb ca t)) I J = minorIJ h I J := by
  unfold minorIJ
  split_ifs with e
  · by_cases hca : ca ∈ J
    · have hcb := hJ.1 hca
      obtain ⟨p, hp⟩ : ca ∈ Set.range (J.orderEmbOfFin (rfl : J.card = J.card)) := by
        rw [Finset.range_orderEmbOfFin]; exact hca
      obtain ⟨q, hq⟩ : cb ∈ Set.range (J.orderEmbOfFin (rfl : J.card = J.card)) := by
        rw [Finset.range_orderEmbOfFin]; exact hcb
      have hpq : p ≠ q := fun h' => hne (by rw [← hp, ← hq, h'])
      refine (congrArg Matrix.det ?_).trans
        (Matrix.det_updateCol_add_smul_self (h.submatrix (I.orderEmbOfFin e) (J.orderEmbOfFin rfl)) hpq t)
      ext a b
      rw [Matrix.submatrix_apply, mul_one_add_single_apply]
      by_cases hb : b = p
      · rw [hb, Matrix.updateCol_self]
        simp [hp, hq]
      · have hbc : J.orderEmbOfFin rfl b ≠ ca := fun h' =>
          hb ((J.orderEmbOfFin rfl).injective (h'.trans hp.symm))
        rw [Matrix.updateCol_ne hb]
        simp [hbc]
    · congr 1
      ext a b
      have hbc : J.orderEmbOfFin rfl b ≠ ca := fun h' => hca (h' ▸ Finset.orderEmbOfFin_mem J rfl b)
      simp [mul_one_add_single_apply, hbc]
  · rfl

theorem mem_stepCols_iff {N j : ℕ} {a b i ca cb : Fin N} (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (hi : i ≠ a) :
    ca ∈ stepCols N j i ↔ cb ∈ stepCols N j i := by
  have hi' : (i : ℕ) ≠ a := fun h => hi (Fin.ext h)
  have := a.isLt
  have := b.isLt
  have := i.isLt
  have := ca.isLt
  have := cb.isLt
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold lastCol at hca
  split_ifs at hca ⊢ <;> omega

theorem fstPt_sndPt_wVec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), fstPt k₀ (FC.wVec M F b h τ a k₀ ca cb t) = FC.flagPt M F b h ∧ sndPt k₀ (FC.wVec M F b h τ a k₀ ca cb t) = FC.flagPt M F b (Function.update h τ (h τ * (1 + Matrix.single cb ca t))) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hb hab hblk hca hcb F bv h t
  have hne : ca ≠ cb := by
    intro e
    have := congrArg Fin.val e
    omega
  refine ⟨?_, ?_⟩
  · funext p
    obtain ⟨k, m⟩ := p
    rfl
  · funext p
    obtain ⟨k, m⟩ := p
    simp only [sndPt, Function.comp_apply]
    by_cases hk : k = k₀
    · subst hk
      rw [v₁_self]
      show (∑ I, valAt M.x (F.u ⟨k, m⟩ I) bv * minorIJ (h τ * (1 + Matrix.single cb ca t)) I (stepCols N j a)) = _
      rw [flagPt_step M F bv _ hblk m]
      simp [Function.update_self]
    · rw [v₁_ne (p := ⟨k, m⟩) hk]
      show FC.flagPt M F bv h ⟨k, m⟩ = _
      by_cases hbase : ∀ p, M.blk p ≠ some k
      · simp [FC.flagPt, hbase]
      · push Not at hbase
        obtain ⟨⟨τ', i⟩, hp⟩ := hbase
        rw [flagPt_step M F bv h hp m, flagPt_step M F bv _ hp m]
        refine Finset.sum_congr rfl fun I _ => ?_
        dsimp only
        congr 1
        by_cases hτ : τ' = τ
        · subst hτ
          have hia : i ≠ a := by
            rintro rfl
            exact hk (Option.some_injective _ (hp.symm.trans hblk))
          rw [Function.update_self, minorIJ_mul_transvection _ _ _ hne t (mem_stepCols_iff hb hab hca hcb hia)]
        · rw [Function.update_of_ne hτ]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentPluckerOrbitStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_plucker_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), fstPt k₀ (FC.wVec M F b h τ a k₀ ca cb t) = FC.flagPt M F b h ∧ sndPt k₀ (FC.wVec M F b h τ a k₀ ca cb t) = FC.flagPt M F b (Function.update h τ (h τ * (1 + Matrix.single cb ca t))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fstPt_sndPt_wVec | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fstPt_sndPt_wVec | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fstPt_sndPt_wVec <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticSpaceNonempty
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticSpaceNonempty
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty

theorem flagAn_S_nonempty : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), Nonempty FA.S.X := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA
  exact FA.Re.nonempty_base

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticSpaceNonemptyStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_analytic_space_nonempty : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), Nonempty FA.S.X := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty.flagAn_S_nonempty | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty.flagAn_S_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty.flagAn_S_nonempty <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormNonvanishingAnalyticHarmonic
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormNonvanishingAnalyticHarmonic
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem log_norm_eventually_eq_re_analyticAt :
    ∀ (e : ℕ) (f : (Fin e → ℂ) → ℂ) (z : Fin e → ℂ), AnalyticAt ℂ f z → f z ≠ 0 →
      ∃ Hh : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, Real.log ‖f z'‖ = (Hh z').re := by
  intro e f z hf hz
  refine ⟨fun z' => Complex.log (f z' * (f z)⁻¹) + Complex.log (f z), ?_, ?_⟩
  · have h1 : AnalyticAt ℂ (fun z' => f z' * (f z)⁻¹) z := hf.mul analyticAt_const
    have h2 : AnalyticAt ℂ Complex.log (f z * (f z)⁻¹) := by
      apply analyticAt_clog
      rw [mul_inv_cancel₀ hz]
      exact Complex.one_mem_slitPlane
    exact (AnalyticAt.comp (f := fun z' => f z' * (f z)⁻¹) (x := z) h2 h1).add analyticAt_const
  · filter_upwards [hf.continuousAt.eventually_ne hz] with z' hz'
    simp only [Complex.add_re, Complex.log_re, norm_mul, norm_inv]
    rw [Real.log_mul (norm_ne_zero_iff.2 hz') (inv_ne_zero (norm_ne_zero_iff.2 hz)), Real.log_inv]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormNonvanishingAnalyticHarmonicStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic : ∀ (e : ℕ) (f : (Fin e → ℂ) → ℂ) (z : Fin e → ℂ), AnalyticAt ℂ f z → f z ≠ 0 → ∃ Hh : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, Real.log ‖f z'‖ = (Hh z').re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_eventually_eq_re_analyticAt | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_eventually_eq_re_analyticAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_eventually_eq_re_analyticAt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloMapOfLocalProductCharts
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloMapOfLocalProductCharts
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord

theorem holoMap_of_coord : ∀ (e n : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X) (B : FinHolAtlas n Y) (pr : X → Y), (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin B.n) (σ : Fin n → Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∀ x' ∈ ψ.source, pr x' ∈ (B.chart kb).source ∧ ∀ i, B.chart kb (pr x') i = ψ x' (σ i)) → HoloMap A B pr := by
  intro e n X Y _ _ A B pr hloc
  have key : ∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin B.n) (σ : Fin n → Fin e),
      IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∀ x' ∈ ψ.source, pr x' ∈ (B.chart kb).source ∧
        pr x' = (B.chart kb).symm (fun i => ψ x' (σ i)) ∧ (fun i => ψ x' (σ i)) ∈ (B.chart kb).target := by
    intro x
    obtain ⟨ψ, kb, σ, hψ, hx, h⟩ := hloc x
    refine ⟨ψ, kb, σ, hψ, hx, fun x' hx' => ?_⟩
    obtain ⟨hs, hc⟩ := h x' hx'
    have hfun : (fun i => ψ x' (σ i)) = B.chart kb (pr x') := funext fun i => (hc i).symm
    refine ⟨hs, ?_, ?_⟩
    · rw [hfun, (B.chart kb).left_inv hs]
    · rw [hfun]
      exact (B.chart kb).map_source hs
  refine ⟨?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨ψ, kb, σ, -, hx, h⟩ := key x
    let L : (Fin e → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ i)
    have hcont : ContinuousOn ((B.chart kb).symm ∘ L ∘ ψ) ψ.source :=
      (B.chart kb).continuousOn_symm.comp (L.continuous.comp_continuousOn ψ.continuousOn)
        (fun x' hx' => (h x' hx').2.2)
    have heq : ((B.chart kb).symm ∘ L ∘ ψ) =ᶠ[𝓝 x] pr :=
      Filter.eventually_of_mem (ψ.open_source.mem_nhds hx) fun x' hx' => ((h x' hx').2.1).symm
    exact (hcont.continuousAt (ψ.open_source.mem_nhds hx)).congr heq
  · intro j k y hy
    obtain ⟨hyt, hys⟩ := hy
    obtain ⟨ψ, kb, σ, hψ, hx, h⟩ := key ((A.chart j).symm y)
    let L : (Fin e → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ i)
    have h1 : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hψ j).1 y ⟨hyt, hx⟩
    have h2 : AnalyticAt ℂ (B.chart k ∘ (B.chart kb).symm) (L (ψ ((A.chart j).symm y))) := by
      apply B.holo kb k
      refine ⟨(h _ hx).2.2, ?_⟩
      show (B.chart kb).symm (fun i => ψ ((A.chart j).symm y) (σ i)) ∈ (B.chart k).source
      rw [← (h _ hx).2.1]
      exact hys
    have h3 : AnalyticAt ℂ ((B.chart k ∘ (B.chart kb).symm) ∘ L ∘ (ψ ∘ (A.chart j).symm)) y :=
      AnalyticAt.comp (f := L ∘ (ψ ∘ (A.chart j).symm)) h2
        (AnalyticAt.comp (f := ψ ∘ (A.chart j).symm) (L.analyticAt _) h1)
    apply h3.congr
    have hnb : ∀ᶠ y' in 𝓝 y, (A.chart j).symm y' ∈ ψ.source :=
      (A.chart j).continuousAt_symm hyt (ψ.open_source.mem_nhds hx)
    filter_upwards [hnb] with y' hy'
    simp only [Function.comp_apply]
    rw [(h _ hy').2.1]
    rfl

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloMapOfLocalProductChartsStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holoMap_of_local_product_charts : ∀ (e n : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X) (B : FinHolAtlas n Y) (pr : X → Y), (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin B.n) (σ : Fin n → Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∀ x' ∈ ψ.source, pr x' ∈ (B.chart kb).source ∧ ∀ i, B.chart kb (pr x') i = ψ x' (σ i)) → HoloMap A B pr := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord.holoMap_of_coord | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord.holoMap_of_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord.holoMap_of_coord <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousOrbitSection
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousOrbitSection
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

section Inverse

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem notMem_mcPts_top_inv (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro h
  have h1 := h.2 1 trivial
  simp at h1

theorem minors_of_sameOrbit_inv {a z : (Σ k, ι k) → ℂ} (h : SameOrbit a z) (k : K) (i i' : ι k) :
    a ⟨k, i⟩ * z ⟨k, i'⟩ = a ⟨k, i'⟩ * z ⟨k, i⟩ := by
  obtain ⟨c, -, rfl⟩ := h
  show c k * z ⟨k, i⟩ * z ⟨k, i'⟩ = c k * z ⟨k, i'⟩ * z ⟨k, i⟩
  ring

theorem sameOrbit_of_minors_inv {a z : (Σ k, ι k) → ℂ} (ha : ∀ k, ∃ i, a ⟨k, i⟩ ≠ 0)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (h : ∀ (k : K) (i i' : ι k), a ⟨k, i⟩ * z ⟨k, i'⟩ = a ⟨k, i'⟩ * z ⟨k, i⟩) : SameOrbit a z := by
  choose q hq using hz
  refine ⟨fun k => a ⟨k, q k⟩ / z ⟨k, q k⟩, fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := ha k
    refine div_ne_zero (fun h0 => hi ?_) (hq k)
    have h1 := h k i (q k)
    rw [h0, zero_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_right (hq k)
  · funext ⟨k, i⟩
    show a ⟨k, i⟩ = a ⟨k, q k⟩ / z ⟨k, q k⟩ * z ⟨k, i⟩
    rw [div_mul_eq_mul_div, eq_div_iff (hq k)]
    exact h k i (q k)

end Inverse

theorem exists_continuousOn_inv_pts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P ⊤ e), Nonempty R.X →
    ∃ r : ((Σ k, ι k) → ℂ) → R.X, (∀ z ∈ mcPts P, SameOrbit (R.lift (r z) (r z)) z) ∧
      ContinuousOn r (mcPts P) := by
  intro K _ ι _ P e R hX
  have hs : ∀ z ∈ mcPts P, ∃ x, SameOrbit (R.lift x x) z :=
    fun z hz => R.surj z hz (notMem_mcPts_top_inv z)
  choose! r hr using hs
  refine ⟨r, hr, fun z₀ hz₀ => ?_⟩
  refine isCompact_univ.le_nhds_of_unique_clusterPt (by simp) fun x' _ hx' => ?_
  obtain ⟨G, hG, hGr⟩ := mapClusterPt_iff_ultrafilter.mp hx'
  have hUx : R.U x' ∈ 𝓝 x' := (R.isOpen_U x').mem_nhds (R.mem_U x')
  have hGS : ∀ᶠ z in (G : Filter _), z ∈ mcPts P := hG self_mem_nhdsWithin
  have hGU : ∀ᶠ z in (G : Filter _), r z ∈ R.U x' := hGr hUx
  have hGz : (G : Filter _) ≤ 𝓝 z₀ := hG.trans nhdsWithin_le_nhds
  have hmin : ∀ᶠ z in (G : Filter _), SameOrbit (R.lift x' (r z)) z := by
    filter_upwards [hGS, hGU] with z h1 h2
    exact orbit_trans (R.compat x' (r z) (r z) ⟨h2, R.mem_U _⟩) (hr z h1)
  have ha : ∀ p, Tendsto (fun z => R.lift x' (r z) p) (G : Filter _) (𝓝 (R.lift x' x' p)) :=
    fun p => (((continuousOn_lift R x' p).continuousAt hUx).tendsto).comp hGr
  have hzc : ∀ p, Tendsto (fun z : (Σ k, ι k) → ℂ => z p) (G : Filter _) (𝓝 (z₀ p)) :=
    fun p => ((continuous_apply p).tendsto z₀).comp hGz
  have hsame : SameOrbit (R.lift x' x') z₀ :=
    sameOrbit_of_minors_inv (R.mem x' x' (R.mem_U x')).1 hz₀.1 fun k i i' =>
      tendsto_nhds_unique_of_eventuallyEq ((ha _).mul (hzc _)) ((ha _).mul (hzc _))
        (hmin.mono fun z hz => minors_of_sameOrbit_inv hz k i i')
  exact R.inj x' (r z₀) (notMem_mcPts_top_inv _) (orbit_trans hsame (orbit_symm (hr z₀ hz₀)))

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousOrbitSectionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_orbit_section : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P ⊤ e), Nonempty R.X → ∃ r : ((Σ k, ι k) → ℂ) → R.X, (∀ z ∈ mcPts P, SameOrbit (R.lift (r z) (r z)) z) ∧ ContinuousOn r (mcPts P) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.exists_continuousOn_inv_pts | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.exists_continuousOn_inv_pts | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.exists_continuousOn_inv_pts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticAtHolomorphicComposition
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_comp_of_holo_in_charts (e n : ℕ) (X : Type) [TopologicalSpace X]
    (A : FinHolAtlas n X) (Un : Set (Fin e → ℂ)) (bp : (Fin e → ℂ) → X) (w₀ : Fin e → ℂ)
    (W : Set X) (f : X → ℂ) (hUn : IsOpen Un) (hw₀ : w₀ ∈ Un) (hc : ContinuousOn bp Un)
    (hb : ∀ k, AnalyticOnNhd ℂ (A.chart k ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source))
    (_hW : IsOpen W) (hwW : bp w₀ ∈ W) (hf : A.HoloOn W f) : AnalyticAt ℂ (f ∘ bp) w₀ := by
  obtain ⟨k, hk⟩ := A.cover (bp w₀)
  have hca : ContinuousAt bp w₀ := hc.continuousAt (hUn.mem_nhds hw₀)
  have h1 : AnalyticAt ℂ (A.chart k ∘ bp) w₀ := hb k w₀ ⟨hw₀, hk⟩
  have h2 : AnalyticAt ℂ (f ∘ (A.chart k).symm) ((A.chart k ∘ bp) w₀) := by
    apply hf k
    refine ⟨(A.chart k).map_source hk, ?_⟩
    show (A.chart k).symm (A.chart k (bp w₀)) ∈ W
    rw [(A.chart k).left_inv hk]
    exact hwW
  have h3 := h2.comp h1
  refine h3.congr ?_
  have hev : ∀ᶠ w in 𝓝 w₀, bp w ∈ (A.chart k).source :=
    hca ((A.chart k).open_source.mem_nhds hk)
  filter_upwards [hev] with w hw
  simp only [Function.comp_apply, (A.chart k).left_inv hw]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
