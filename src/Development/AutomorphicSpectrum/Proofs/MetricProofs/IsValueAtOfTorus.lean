module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
public import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

noncomputable def scaleT (c : K → ℂ) : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ :=
  aeval fun k => C (c k) * X k

omit [Fintype K] in
theorem scaleT_inv_scaleT (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (f : MvPolynomial K ℂ) :
    scaleT (fun k => (c k)⁻¹) (scaleT c f) = f := by
  have h : (scaleT (fun k => (c k)⁻¹)).comp (scaleT c) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [scaleT, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]
    rw [← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  exact DFunLike.congr_fun h f


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mConeMap_torus (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    mConeMap (fun q : Σ k, ι k => c q.1 * z q) f = scaleT c (mConeMap z f) := by
  have h : mConeMap (fun q : Σ k, ι k => c q.1 * z q) =
      ((scaleT c).restrictScalars ℤ).comp (mConeMap z) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [mConeMap, scaleT, AlgHom.comp_apply, aeval_X, AlgHom.restrictScalars_apply, map_mul,
      algHom_C, algebraMap_eq, mul_assoc]
    rw [mul_left_comm]
  rw [h]
  rfl


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mCoordIdeal_torus (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    mCoordIdeal (fun q : Σ k, ι k => c q.1 * z q) = mCoordIdeal z := by
  ext f
  rw [mCoordIdeal, mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker, mConeMap_torus]
  constructor
  · intro h
    have := congrArg (scaleT fun k => (c k)⁻¹) h
    rwa [scaleT_inv_scaleT c hc, map_zero] at this
  · intro h
    rw [h, map_zero]

theorem isValueAt_torus {x : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ} (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) (hv : IsValueAt x s z v) :
    IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v := by
  obtain ⟨d, g, h, hg, hh, hy, he, h0, rfl⟩ := hv
  have hu : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, hy, he, ?_, ?_⟩
  · rw [eval_smul_homog h d hh]
    exact mul_ne_zero hu h0
  · rw [eval_smul_homog g d hg, eval_smul_homog h d hh, mul_div_mul_left _ _ hu]

theorem isValueAt_of_torus {x : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ} (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) (hv : IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v) :
    IsValueAt x s z v := by
  have h := isValueAt_torus (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hv
  have e : (fun q : Σ k, ι k => (c q.1)⁻¹ * (c q.1 * z q)) = z := by
    funext q
    exact inv_mul_cancel_left₀ (hc q.1) _
  rwa [e] at h

theorem valAt_torus {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (hz : z ∈ mcPts (mCoordIdeal x))
    (hcz : (fun q : Σ k, ι k => c q.1 * z q) ∈ mcPts (mCoordIdeal x)) (s : Ω) :
    valAt x s (fun q : Σ k, ι k => c q.1 * z q) = valAt x s z := by
  by_cases h : ∃ v, IsValueAt x s z v
  · obtain ⟨v, hv⟩ := h
    rw [valAt_eq hz hv, valAt_eq hcz (isValueAt_torus c hc hv)]
  · have h' : ¬ ∃ v, IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v :=
      fun ⟨v, hv⟩ => h ⟨v, isValueAt_of_torus c hc hv⟩
    rw [valAt, valAt, dite_eq_right h, dite_eq_right h']

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (c : K → ℂ), (∀ k, c k ≠ 0) →
    mCoordIdeal (fun q : Σ k, ι k => c q.1 * z q) = mCoordIdeal z ∧
      (z ∈ mcPts (mCoordIdeal x) → (fun q : Σ k, ι k => c q.1 * z q) ∈ mcPts (mCoordIdeal x) ∧
        ∀ s : Ω, valAt x s (fun q : Σ k, ι k => c q.1 * z q) = valAt x s z) := by
  intro K _ ι _ Ω _ x z c hc
  refine ⟨mCoordIdeal_torus c hc z, fun hz => ?_⟩
  have hcz := mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal x) c hc hz
  exact ⟨hcz, valAt_torus c hc hz hcz⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def bvec {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) (b : BM.Rb.X) :
    (Σ k, baseIdx ι M.blk k) → ℂ :=
  fun q => BM.Rb.lift b b q / BM.Rb.lift b b ⟨q.1, (BM.F l).c q.1⟩

def flagPt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : (Σ k, ι k) → ℂ := fun q =>
  if hk : ∀ p, M.blk p ≠ some q.1 then b ⟨⟨q.1, hk⟩, q.2⟩ else
    ∑ I, valAt M.x (F.u q I) b * minorIJ (h (not_forall.1 hk).choose.1) I (stepCols N j (not_forall.1 hk).choose.2)

theorem basePart_flagPt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : basePart M.blk (flagPt M F b h) = b := by
  funext q
  obtain ⟨⟨k, hk⟩, m⟩ := q
  exact dif_pos hk

theorem flagPt_step (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) (m : ι k) :
    flagPt M F b h ⟨k, m⟩ = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) b * minorIJ (h p.1) I (stepCols N j p.2) := by
  have hk : ¬ ∀ p', M.blk p' ≠ some k := fun h' => h' p hp
  simp only [flagPt]
  rw [dite_eq_right hk]
  have key : ∀ p' : Ψ × Fin N, M.blk p' = some k →
      (∑ I, valAt M.x (F.u ⟨k, m⟩ I) b * minorIJ (h p'.1) I (stepCols N j p'.2))
        = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) b * minorIJ (h p.1) I (stepCols N j p.2) := by
    intro p' hp'
    rw [M.blk_inj _ _ k hp' hp]
  exact key (not_forall.1 hk).choose (not_not.1 (not_forall.1 hk).choose_spec)

theorem exactAt_flagPt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : ∀ k, b ⟨k, F.c k⟩ = 1) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) :
    ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F p (flagPt M F b h) (h p.1) := by
  refine ⟨fun k => by rw [basePart_flagPt]; exact hb k, fun k hp m => ?_⟩
  rw [basePart_flagPt]
  exact flagPt_step M F b h hp m

def wVec (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (t : ℂ) :
    (Σ o : Option K, ι (o.getD k₀)) → ℂ
  | ⟨some k, m⟩ => flagPt M F b h ⟨k, m⟩
  | ⟨none, m⟩ => ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) b *
      minorIJ (h τ * (1 + Matrix.single cb ca t)) I (stepCols N j a)

def plk (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (z : (Σ k, ι k) → ℂ) (p : Ψ × Fin N) : ℂ :=
  (M.blk p).elim 1 fun k => ∑ m : ι k, valAt M.x (F.u' (stepCols N j p.2) ⟨k, m⟩) b * z ⟨k, m⟩

abbrev CIdx (Ψ : Type) (N j : ℕ) (τ : Ψ) (ca cb : Fin N) : Type := {q : LowIdx Ψ N j // q.1 ≠ (τ, cb, ca)}

def Lc (τ : Ψ) (ca cb : Fin N) (c : CIdx Ψ N j τ ca cb → ℂ) (τ' : Ψ) : Matrix (Fin N) (Fin N) ℂ := fun r s =>
  if h : (s < r ∧ ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)) ∧ (τ', r, s) ≠ (τ, cb, ca) then
    c ⟨⟨(τ', r, s), h.1⟩, h.2⟩ else if r = s then 1 else 0

def Lca (τ : Ψ) (ca cb : Fin N) (c : CIdx Ψ N j τ ca cb → ℂ) (a : ℂ) : Ψ → Matrix (Fin N) (Fin N) ℂ :=
  Function.update (Lc τ ca cb c) τ (Lc τ ca cb c τ * (1 + Matrix.single cb ca a))

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

def IsImg {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (z : (Σ k, ι' k) → ℂ) (w : (Σ k, ι k) → ℂ) : Prop :=
  ∀ z₁, SameOrbit z₁ z → ∀ F' F, M'.IsFrame F' → M.IsFrame F →
    M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z₁ ∘ Cv.v)) →
    ∀ h, M'.IsFlagOf F' z₁ h → ∃ z₀, SameOrbit z₀ w ∧ SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) ∧
      M.IsFlagOf F z₀ fun τ => Cv.trans F' F (basePart M'.blk z₁) τ * h τ

theorem IsImg.orbit {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} {Cv : FlagCover M' M}
    {z z₁ : (Σ k, ι' k) → ℂ} {w w₁ : (Σ k, ι k) → ℂ} (h : IsImg Cv z w) (hz : SameOrbit z₁ z)
    (hw : SameOrbit w₁ w) : IsImg Cv z₁ w₁ := by
  intro z₂ h2 F' F hF' hF hg' hg hh hfl
  obtain ⟨z₀, a, b, c⟩ := h z₂ (Cj.sameOrbit_trans h2 hz) F' F hF' hF hg' hg hh hfl
  exact ⟨z₀, Cj.sameOrbit_trans a (Cj.sameOrbit_symm hw), b, c⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure OrbitChart (P : Ideal (MRing ι)) (e : ℕ) where

  D : Set (Fin e → ℂ)
  isOpen_D : IsOpen D

  φ : (Fin e → ℂ) → (Σ k, ι k) → ℂ
  holo : ∀ p, AnalyticOnNhd ℂ (fun w => φ w p) D
  mem : ∀ w ∈ D, φ w ∈ mcPts P

  O : Set ((Σ k, ι k) → ℂ)
  O_open : ∃ O' : Set ((Σ k, ι k) → ℂ), IsOpen O' ∧ O = O' ∩ mcPts P
  O_orbit : ∀ z ∈ O, ∀ z' ∈ mcPts P, SameOrbit z' z → z' ∈ O

  ρ : ((Σ k, ι k) → ℂ) → Fin e → ℂ
  ρ_cont : ContinuousOn ρ O
  ρ_orbit : ∀ z ∈ O, ∀ z' ∈ O, SameOrbit z' z → ρ z' = ρ z
  φ_mem_O : ∀ w ∈ D, φ w ∈ O
  ρ_φ : ∀ w ∈ D, ρ (φ w) = w
  ρ_mem : ∀ z ∈ O, ρ z ∈ D
  φ_ρ : ∀ z ∈ O, SameOrbit (φ (ρ z)) z
  immersion : ∀ w ∈ D, ∀ p : (k : K) → ι k, (∀ k, φ w ⟨k, p k⟩ ≠ 0) →
    (fderiv ℂ (fun w' => affCoord p (φ w')) w).ker = ⊥

end Orbit

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def stepOf (N j : ℕ) (c : Fin N) : Fin N :=
  ⟨if N - j ≤ (c : ℕ) then (c : ℕ) - (N - j) else (c : ℕ) + j, by
    have := c.2
    split_ifs <;> omega⟩

def lowMat (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : Matrix (Fin N) (Fin N) ℂ := fun a b =>
  if h : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then c ⟨(τ, a, b), h⟩ else if a = b then 1 else 0

def flagZ (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : (Σ k, ι k) → ℂ := fun q =>
  if e : ∃ p, M.blk p = some q.1 then
    ∑ I, valAt M.x (F.u q I) zb * minorIJ (h e.choose.1) I (stepCols N j e.choose.2)
  else zb ⟨⟨q.1, fun p hp => e ⟨p, hp⟩⟩, q.2⟩

def sqZ (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (k₀ : K) (τ : Ψ) (ca cb : Fin N) (t : ℂ) :
    (Σ o : Option K, ι (o.getD k₀)) → ℂ
  | ⟨some k, m⟩ => flagZ M F zb h ⟨k, m⟩
  | ⟨none, m⟩ => flagZ M F zb (Function.update h τ (h τ * (1 + Matrix.single cb ca t))) ⟨k₀, m⟩

def pluck (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (k : K)
    (z : (Σ k, ι k) → ℂ) (I : Finset (Fin N)) : ℂ :=
  ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) zb * z ⟨k, m⟩

def twMinor (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (i : Fin N)
    (k : K) (g : Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (J : Finset (Fin N)) : ℂ :=
  ∑ I ∈ Finset.univ.filter (IsStepRows N j i), minorIJ g J I * pluck M F zb k z I

def lowRead (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (τ' : Ψ) (a' b' : Fin N) : ℂ :=
  (M.blk (τ', stepOf N j b')).elim 0 fun k =>
    twMinor M F zb (stepOf N j b') k (h τ')⁻¹ z (insert a' ((stepCols N j (stepOf N j b')).erase b')) /
      twMinor M F zb (stepOf N j b') k (h τ')⁻¹ z (stepCols N j (stepOf N j b'))

def baseOf (M : FlagModel y Ψ N j) (k₀ : K) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) :
    (Σ k, baseIdx ι M.blk k) → ℂ := basePart M.blk (fstPt k₀ z)

abbrev wP (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) :
    Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (fun o : Option K => ι (o.getD k₀))) :=
  mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)

section Param

variable {n e : ℕ} {Λ : Type}

def wB (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (w : Fin e → ℂ) : Fin n → ℂ := fun i => w (ε (Sum.inl i))

def wL (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (w : Fin e → ℂ) : Λ → ℂ := fun q => w (ε (Sum.inr (Sum.inl q)))

def wT (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (w : Fin e → ℂ) : ℂ := w (ε (Sum.inr (Sum.inr ())))

def wD (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (V : Set (Fin n → ℂ)) : Set (Fin e → ℂ) := {w | wB ε w ∈ V}

end Param

variable {n e : ℕ}

def wH (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ) (w : Fin e → ℂ) :
    Matrix (Fin N) (Fin N) ℂ := h τ' * lowMat (wL ε w) τ'

def wPhi (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (k₀ : K) (τ : Ψ) (ca cb : Fin N)
    (w : Fin e → ℂ) : (Σ o : Option K, ι (o.getD k₀)) → ℂ :=
  sqZ M F (bl (wB ε w)) (fun τ' => wH h ε τ' w) k₀ τ ca cb (wT ε w)

def IsBaseChart (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (F : FrameData ι Ψ N M.Ω M.blk)
    (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) : Prop :=
  IsOpen V ∧ V ⊆ (Rb.A.chart kb).target ∧ (∀ q, AnalyticOnNhd ℂ (fun w => bl w q) V) ∧
    (∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (bl w)) V) ∧
    ∀ w ∈ V, bl w ∈ mcPts (mCoordIdeal M.x) ∧ (∀ k, bl w ⟨k, F.c k⟩ = 1) ∧ M.GoodAt F (mCoordIdeal (bl w)) ∧
      SameOrbit (Rb.lift ((Rb.A.chart kb).symm w) ((Rb.A.chart kb).symm w)) (bl w)

def IsWCtx (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N)
    (d : ℕ) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (b : ℕ) = a + 1 ∧ ((b : ℕ) < j ∨ j ≤ (a : ℕ)) ∧ M.blk (τ, a) = some k₀ ∧ (ca : ℕ) = lastCol N j a ∧
    (cb : ℕ) = ca + 1 ∧ IsArithVar (mCoordIdeal y) (d + 2) ∧ M.IsFrame F ∧ IsBaseChart M Rb F kb V bl ∧
    (∀ z ∈ mcPts (mCoordIdeal M.x), SameOrbit (Rb.lift (r z) (r z)) z) ∧ ContinuousOn r (mcPts (mCoordIdeal M.x)) ∧
    ∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0

def wO (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N)
    (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) :
    Set ((Σ o : Option K, ι (o.getD k₀)) → ℂ) :=
  {z | z ∈ mcPts (wP M τ a k₀ ca cb) ∧ r (baseOf M k₀ z) ∈ (Rb.A.chart kb).source ∧
    Rb.A.chart kb (r (baseOf M k₀ z)) ∈ V ∧
    (∀ p k, M.blk p = some k →
      twMinor M F (baseOf M k₀ z) p.2 k (h p.1)⁻¹ (fstPt k₀ z) (stepCols N j p.2) ≠ 0) ∧
    twMinor M F (baseOf M k₀ z) a k₀ (h τ)⁻¹ (sndPt k₀ z) (stepCols N j a) ≠ 0}

def wRho (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (k₀ : K) (ca cb : Fin N)
    (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e)
    (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : Fin e → ℂ := fun i =>
  match ε.symm i with
  | Sum.inl l => Rb.A.chart kb (r (baseOf M k₀ z)) l
  | Sum.inr (Sum.inl q) => lowRead M F (baseOf M k₀ z) h (fstPt k₀ z) q.1.1 q.1.2.1 q.1.2.2
  | Sum.inr (Sum.inr _) =>
    lowRead M F (baseOf M k₀ z) h (sndPt k₀ z) τ cb ca - lowRead M F (baseOf M k₀ z) h (fstPt k₀ z) τ cb ca

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def flagAt {d : ℕ} (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) (ca cb : Fin N) (t : ℂ) (w : Fin d → ℂ)
    (τ' : Ψ) : Matrix (Fin N) (Fin N) ℂ :=
  if τ' = τ then H τ w * (1 + Matrix.single cb ca t) else H τ' w

def IsFibreData {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n} (FA : FlagAn BM d) (τ : Ψ) (a : Fin N) (ca cb : Fin N)
    {X : Type} (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q)
    (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X) : Prop :=
  (∀ τ' r s, AnalyticOnNhd ℂ (fun w => H τ' w r s) Un) ∧
    ContinuousOn bp Un ∧ (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) ∧
    (∀ w ∈ Un, bp w ∈ BM.O l \ bdry BM.s ∧ ∀ τ', IsBlockDiag j (H τ' w) ∧ (H τ' w).det ≠ 0) ∧
    (∀ w ∈ Un, ∀ r s : Fin 2, Gn w r s =
      minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) (insert (![ca, cb] r) ((stepCols N j a).erase ca))
          (insert (![ca, cb] s) ((stepCols N j a).erase ca)) /
        minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) ∧
    (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∀ x₀, FA.Re.π x₀ = ΦYn z → ∃ z₀ : (Σ k, ι k) → ℂ,
      SameOrbit (FA.Re.R.lift x₀ x₀) z₀ ∧ SameOrbit (basePart M.blk z₀) (BM.Rb.lift (bp (Fin.tail z)) (bp (Fin.tail z))) ∧
      ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ', i) z₀ (flagAt H τ ca cb (z 0) (Fin.tail z) τ')) ∧
    ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un →
      q 0 (ΦWn z) = ΦYn (Fin.cons (z 0) (Fin.tail (Fin.tail z))) ∧ q 1 (ΦWn z) = ΦYn (Fin.tail z)

theorem isFibreChart_iff {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n} (FA : FlagAn BM d) (τ : Ψ) (a : Fin N)
    (ca cb : Fin N) {X : Type} (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ))
    (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) :
    IsFibreChart FA τ a ca cb q Un Gn ΦYn ΦWn ↔ ∃ l H bp, IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp :=
  Iff.rfl

def upsVal {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X) : ℂ :=
  valAt M.x ((BM.F l).υ p) (BM.Rb.lift b b)

def upsLogAt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X) : ℝ :=
  if M.blk p = none then Real.log ‖upsVal BM l p b‖ else 0

def potAt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X)
    (hf : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  blockPot j p.2 (BM.G l p.1 b) hf - upsLogAt BM l p b

def alphaOf {M : FlagModel y Ψ N j} {n d : ℕ} (BM : BaseMetric M n) (l : Fin BM.q)
    (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X) (p : Ψ × Fin N) (w : Fin d → ℂ) : ℝ :=
  potAt BM l p (bp w) (H p.1 w)

def facOf (N j : ℕ) (a : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : ℂ :=
  if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1)
    else minorIJ h (omIdx N j) (omIdx N j)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.ValRing

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isPrime_mCoordIdeal (z : (Σ k, ι k) → ℂ) : (mCoordIdeal z).IsPrime :=
  RingHom.ker_isPrime _

theorem eval_ne_zero_of_notMem {z : (Σ k, ι k) → ℂ} {h : MRing ι} {d : K → ℕ}
    (hh : IsMultiHomog h d) (hn : h ∉ mCoordIdeal z) :
    eval z (map (Int.castRingHom ℂ) h) ≠ 0 := by
  intro h0
  refine hn (mem_mCoordIdeal_of_aeval_eq_zero z hh ?_)
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
  simpa using h0

theorem aeval_ne_zero_of_notMem {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal x)) {h : MRing ι} {d : K → ℕ}
    (hh : IsMultiHomog h d) (hn : h ∉ mCoordIdeal z) : aeval x h ≠ 0 := fun h0 =>
  eval_ne_zero_of_notMem hh hn
    (eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero x hh h0))

theorem exists_isValueAt {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (hs : RegAt x (mCoordIdeal z) s) :
    ∃ v, IsValueAt x s z v := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  exact ⟨_, d, g, h, hg, hh, aeval_ne_zero_of_notMem hz hh hn, heq,
    eval_ne_zero_of_notMem hh hn, rfl⟩

theorem isValueAt_add {x : (Σ k, ι k) → Ω} {s t : Ω} {z : (Σ k, ι k) → ℂ} {v w : ℂ}
    (hv : IsValueAt x s z v) (hw : IsValueAt x t z w) : IsValueAt x (s + t) z (v + w) := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  obtain ⟨d', g', h', hg', hh', hy', heq', hz0', rfl⟩ := hw
  refine ⟨d + d', g * h' + g' * h, h * h', LowerBoundFree.isMultiHomog_add (LowerBoundFree.isMultiHomog_mul hg hh') ?_,
    LowerBoundFree.isMultiHomog_mul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [add_comm d d']
    exact LowerBoundFree.isMultiHomog_mul hg' hh
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · simp only [map_add (f := _), map_mul, heq, heq']; ring
  · simp only [map_mul]; exact mul_ne_zero hz0 hz0'
  · simp only [map_add (f := _), map_mul]
    field_simp

theorem regAt_mul {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {s t : Ω}
    (hs : RegAt x (mCoordIdeal z) s) (ht : RegAt x (mCoordIdeal z) t) :
    RegAt x (mCoordIdeal z) (s * t) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  obtain ⟨d', g', h', hg', hh', hn', heq'⟩ := ht
  refine ⟨d + d', g * g', h * h', LowerBoundFree.isMultiHomog_mul hg hg', LowerBoundFree.isMultiHomog_mul hh hh',
    fun hm => ((isPrime_mCoordIdeal z).mem_or_mem hm).elim hn hn', ?_⟩
  rw [map_mul, map_mul, heq, heq']; ring

theorem regAt_add {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {s t : Ω}
    (hs : RegAt x (mCoordIdeal z) s) (ht : RegAt x (mCoordIdeal z) t) :
    RegAt x (mCoordIdeal z) (s + t) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  obtain ⟨d', g', h', hg', hh', hn', heq'⟩ := ht
  refine ⟨d + d', g * h' + g' * h, h * h', LowerBoundFree.isMultiHomog_add (LowerBoundFree.isMultiHomog_mul hg hh') ?_,
    LowerBoundFree.isMultiHomog_mul hh hh',
    fun hm => ((isPrime_mCoordIdeal z).mem_or_mem hm).elim hn hn', ?_⟩
  · rw [add_comm d d']
    exact LowerBoundFree.isMultiHomog_mul hg' hh
  · simp only [map_add (f := _), map_mul, heq, heq']; ring

theorem one_notMem_mCoordIdeal (z : (Σ k, ι k) → ℂ) : (1 : MRing ι) ∉ mCoordIdeal z :=
  (Ideal.ne_top_iff_one _).1 (isPrime_mCoordIdeal z).ne_top

theorem regAt_zero (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : RegAt x (mCoordIdeal z) 0 :=
  ⟨0, 0, 1, LowerBoundFree.isMultiHomog_zero 0, LowerBoundFree.isMultiHomog_one, one_notMem_mCoordIdeal z, by simp⟩

theorem regAt_one (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : RegAt x (mCoordIdeal z) 1 :=
  ⟨0, 1, 1, LowerBoundFree.isMultiHomog_one, LowerBoundFree.isMultiHomog_one, one_notMem_mCoordIdeal z, by simp⟩

theorem isValueAt_zero_self (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : IsValueAt x 0 z 0 :=
  ⟨0, 0, 1, LowerBoundFree.isMultiHomog_zero 0, LowerBoundFree.isMultiHomog_one, by simp, by simp, by simp, by simp⟩

end

theorem regAt_valAt_ring : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal x) → RegAt x (mCoordIdeal z) 0 ∧ RegAt x (mCoordIdeal z) 1 ∧ valAt x 0 z = 0 ∧ valAt x 1 z = 1 ∧ ∀ s t : Ω, RegAt x (mCoordIdeal z) s → RegAt x (mCoordIdeal z) t → RegAt x (mCoordIdeal z) (s * t) ∧ RegAt x (mCoordIdeal z) (s + t) ∧ valAt x (s * t) z = valAt x s z * valAt x t z ∧ valAt x (s + t) z = valAt x s z + valAt x t z := by
  intro K _ ι _ Ω _ x z hz
  refine ⟨regAt_zero x z, regAt_one x z, valAt_eq hz (isValueAt_zero_self x z),
    valAt_eq hz (isValueAt_one_self x z), fun s t hs ht => ⟨regAt_mul hs ht, regAt_add hs ht, ?_, ?_⟩⟩
  · obtain ⟨v, hv⟩ := exists_isValueAt hz hs
    obtain ⟨w, hw⟩ := exists_isValueAt hz ht
    rw [valAt_eq hz hv, valAt_eq hz hw, valAt_eq hz (isValueAt_mul hv hw)]
  · obtain ⟨v, hv⟩ := exists_isValueAt hz hs
    obtain ⟨w, hw⟩ := exists_isValueAt hz ht
    rw [valAt_eq hz hv, valAt_eq hz hw, valAt_eq hz (isValueAt_add hv hw)]

end GlobalTheory.CompanionTheory.Ar.PB.ValRing
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def xiDeg (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) : K → ℤ := fun k => ∑ p, xiCoef τ a p * M.dy p k

def aDeg (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) : Option K → ℤ := fun o =>
  match o with
  | none => 1
  | some k => if k = k₀ then 1 else -xiDeg M τ a k

def potA (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) : HermLine fun o : Option K => ι (o.getD k₀) :=
  fsHerm (fun o : Option K => ι (o.getD k₀)) (aDeg M τ a k₀)

def IsPtData (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) {e : ℕ}
    (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ)
    (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) : Prop :=
  M.IsFrame F ∧ M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) ∧ SameOrbit z₀ (fstPt k₀ (RW.lift x x)) ∧
    SameOrbit z₁ (sndPt k₀ (RW.lift x x)) ∧ IsBlockDiag j h ∧ h.det ≠ 0 ∧ t ≠ 0 ∧
    (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) ∧ ∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))

def IsLocSec (M : FlagModel y Ψ N j) {n e : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K)
    (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (x : RW.X)
    (ψ : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e) (i₀ : Fin e) (V : Set RW.X)
    (u : RW.X → ℂ) : Prop :=
  (∃ F H, IsWChart M Rb τ a k₀ ca cb RW pr ψ kb σ i₀ F H) ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ V ⊆ RW.U x ∧
    RW.A.HoloOn V u ∧ (∀ y' ∈ V, u y' ≠ 0) ∧
    (∀ y' ∈ V, ψ y' i₀ = 0 ↔ SameOrbit (fstPt k₀ (RW.lift y' y')) (sndPt k₀ (RW.lift y' y'))) ∧
    ∀ y' ∈ V, ψ y' i₀ ≠ 0 → ∀ z₀ z₁ F h t, IsPtData M τ a k₀ ca cb RW y' z₀ z₁ F h t →
      Real.log ‖u y' * ψ y' i₀‖ - Real.log ((potA M τ a k₀).h (RW.lift x y')) = normRhs M τ a F z₀ z₁ h t

def diagSet (k₀ : K) {P J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (fun o : Option K => ι (o.getD k₀)))} {e : ℕ} (R : AnLogRes P J e) : Set R.X :=
  {x | SameOrbit (fstPt k₀ (R.lift x x)) (sndPt k₀ (R.lift x x))}

def diagSec {e : ℕ} {X : Type} [TopologicalSpace X] (ψ : X → OpenPartialHomeomorph X (Fin e → ℂ)) (i₀ : X → Fin e)
    (u : X → X → ℂ) : X → X → ℂ := fun x y' => u x y' * ψ x y' (i₀ x)

def secPot {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)] {P J : Ideal (MRing ρ)} {e : ℕ}
    (R : AnLogRes P J e) (A : HermLine ρ) (V : R.X → Set R.X) (hV : ∀ x, IsOpen (V x)) (hm : ∀ x, x ∈ V x) (c : ℝ) :
    LocPot R.X where
  U := V
  isOpen_U := hV
  mem_U := hm
  φ x y' := Real.log (A.h (R.lift x y')) + c

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsClosedSectionBoundary
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsClosedSectionBoundary
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.CWeight

theorem isClosed_bdry_of_isSection : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsSection A L s → IsClosed (bdry s) := by
  intro e X _ A L s hS
  exact ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology.isClosed_bdry hS

end GlobalTheory.CompanionTheory.Ar.PB.CWeight
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsClosedSectionBoundaryStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_section_boundary : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsSection A L s → IsClosed (bdry s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection | exact GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FubiniStudyMetricSmooth
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FubiniStudyMetricSmooth
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

theorem fsHerm_isSmoothHerm : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (a : K → ℤ), IsSmoothHerm (fsHerm ι a) :=
  fun _ _ _ _ a => GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm a

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FubiniStudyMetricSmoothStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubini_study_metric_smooth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (a : K → ℤ), IsSmoothHerm (fsHerm ι a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SamePotBlock
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA

namespace BlockPot

theorem continuousAt_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {U : Set X}
    {g : X → ℂ} (hg : A.HoloOn U g) {x : X} (hx : x ∈ U) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have an := hg j (A.chart j x) ⟨(A.chart j).map_source hj, by
    simpa only [Set.mem_preimage, (A.chart j).left_inv hj] using hx⟩
  have c : ContinuousAt (fun y => (g ∘ (A.chart j).symm) (A.chart j y)) x :=
    ContinuousAt.comp (f := A.chart j) an.continuousAt ((A.chart j).continuousAt hj)
  refine c.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp only [Function.comp_apply, (A.chart j).left_inv hy]

theorem holoOn_comp {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e' X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h) {S : Set X}
    {g : X → ℂ} (hg : A.HoloOn S g) : B.HoloOn (h ⁻¹' S) (fun y => g (h y)) := by
  intro j u hu
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm u))
  have hτ : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart j).symm) u := hh.2 j k u ⟨hu.1, hk⟩
  have hgu : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (B.chart j).symm) u) :=
    hg k _ ⟨(A.chart k).map_source hk, by
      simpa only [Function.comp_apply, Set.mem_preimage, (A.chart k).left_inv hk] using hu.2⟩
  refine (hgu.comp hτ).congr ?_
  filter_upwards [((B.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hh.1)).mem_nhds
    ⟨hu.1, hk⟩] with y' hy'
  simp only [Function.comp_apply, (A.chart k).left_inv hy'.2]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K' : Type} [Fintype K']
  {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K' → K} {v : (Σ k, ι' k) → Σ k, ι k}

theorem sum_block (hb : IsBlockMap κ v) (z : (Σ k, ι k) → ℂ) (k : K') :
    ∑ i, ‖z ⟨κ k, i⟩‖ ^ 2 = ∑ m, ‖z (v ⟨k, m⟩)‖ ^ 2 := by
  obtain ⟨hκ, hv, h1, h2⟩ := hb
  have hS : (Finset.univ.image fun i : ι (κ k) => (⟨κ k, i⟩ : Σ k, ι k)) =
      Finset.univ.image fun m : ι' k => v ⟨k, m⟩ := by
    ext q
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨⟨k', m⟩, hp⟩ := h2 ⟨κ k, i⟩ ⟨k, rfl⟩
      have hk : k' = k := hκ (by simpa [hp] using (h1 ⟨k', m⟩).symm)
      subst hk
      exact ⟨m, hp⟩
    · rintro ⟨m, rfl⟩
      rcases hq : v ⟨k, m⟩ with ⟨a, b⟩
      have : a = κ k := by simpa [hq] using h1 ⟨k, m⟩
      subst this
      exact ⟨b, rfl⟩
  have e1 := Finset.sum_image (s := Finset.univ) (g := fun i : ι (κ k) => (⟨κ k, i⟩ : Σ k, ι k))
    (f := fun q => ‖z q‖ ^ 2) (fun a _ b _ hab => by simpa using hab)
  have e2 := Finset.sum_image (s := Finset.univ) (g := fun m : ι' k => v ⟨k, m⟩)
    (f := fun q => ‖z q‖ ^ 2) (fun a _ b _ hab => by simpa using hv hab)
  rw [← e1, hS, e2]

theorem refNorm_block (hb : IsBlockMap κ v) {a : K → ℤ} (ha : ∀ k, k ∉ Set.range κ → a k = 0)
    (z : (Σ k, ι k) → ℂ) : refNorm a z = refNorm (fun k => a (κ k)) (z ∘ v) := by
  unfold refNorm
  symm
  refine Fintype.prod_of_injective κ hb.1 _ _ (fun k hk => ?_) (fun k => ?_)
  · simp [ha k hk]
  · simp only [Function.comp_apply]
    rw [sum_block hb z k]

theorem orbit_near {P J : Ideal (MRing ι)} {P' J' : Ideal (MRing ι')} {e e' : ℕ} (R : AnLogRes P J e)
    (R' : AnLogRes P' J' e') (h : R.X → R'.X) (hb : IsBlockMap κ v)
    (hO : ∀ x, SameOrbit (R'.lift (h x) (h x)) (R.lift x x ∘ v)) {x y : R.X} (hy : y ∈ R.U x)
    (hy' : h y ∈ R'.U (h x)) :
    ∃ c : K' → ℂ, (∀ k, c k ≠ 0) ∧ ∀ p, R'.lift (h x) (h y) p = c p.1 * R.lift x y (v p) := by
  obtain ⟨c₁, hc₁, e₁⟩ := R'.compat (h x) (h y) (h y) ⟨hy', R'.mem_U _⟩
  obtain ⟨c₂, hc₂, e₂⟩ := hO y
  obtain ⟨c₃, hc₃, e₃⟩ := R.compat x y y ⟨hy, R.mem_U _⟩
  refine ⟨fun k => c₁ k * c₂ k * (c₃ (κ k))⁻¹, fun k => mul_ne_zero (mul_ne_zero (hc₁ k) (hc₂ k))
    (inv_ne_zero (hc₃ _)), fun p => ?_⟩
  have f₁ := congrFun e₁ p
  have f₂ := congrFun e₂ p
  have f₃ := congrFun e₃ (v p)
  have f₃' : R.lift x y (v p) = c₃ (κ p.1) * R.lift y y (v p) := by
    rw [← hb.2.2.1 p]
    exact f₃
  have hc : c₃ (κ p.1) ≠ 0 := hc₃ _
  simp only [Function.comp_apply] at f₂
  rw [f₁, f₂, f₃']
  field_simp

theorem samePot_block (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K']
    (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K' → K) (v : (Σ k, ι' k) → Σ k, ι k) (P J : Ideal (MRing ι))
    (P' J' : Ideal (MRing ι')) (e e' : ℕ) (R : AnLogRes P J e) (R' : AnLogRes P' J' e') (h : R.X → R'.X)
    (hh : HoloMap R.A R'.A h) (a : K → ℤ) (hb : IsBlockMap κ v) (ha : ∀ k, k ∉ Set.range κ → a k = 0)
    (hO : ∀ x, SameOrbit (R'.lift (h x) (h x)) (R.lift x x ∘ v)) :
    SamePot R.A Set.univ (potOf R (fsHerm ι a)) ((potOf R' (fsHerm ι' fun k => a (κ k))).pullback h hh.1) := by
  intro x _
  have hxU : x ∈ R.U x := R.mem_U x
  have hxU' : h x ∈ R'.U (h x) := R'.mem_U _

  obtain ⟨cx, hcx, ex⟩ := orbit_near R R' h hb hO hxU hxU'
  have hm : ∀ k : K', ∃ m : ι' k, R.lift x x (v ⟨k, m⟩) ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := (R.mem x x hxU).1 (κ k)
    obtain ⟨⟨k', m⟩, hp⟩ := hb.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
    have hk : k' = k := hb.1 (by simpa [hp] using (hb.2.2.1 ⟨k', m⟩).symm)
    subst hk
    exact ⟨m, by rw [hp]; exact hi⟩
  choose m hm using hm

  let den : K' → R.X → ℂ := fun k y => R.lift x y (v ⟨k, m k⟩)
  let num : K' → R.X → ℂ := fun k y => R'.lift (h x) (h y) ⟨k, m k⟩
  let rat : K' → R.X → ℂ := fun k y => num k y / den k y / cx k
  have hdenH : ∀ k, R.A.HoloOn (R.U x) (den k) := fun k => R.holo x _
  have hnumH : ∀ k, R.A.HoloOn (h ⁻¹' R'.U (h x)) (num k) := fun k =>
    holoOn_comp hh (R'.holo (h x) ⟨k, m k⟩)
  have hdenC : ∀ k, ContinuousAt (den k) x := fun k => continuousAt_of_holoOn (hdenH k) hxU
  have hnumC : ∀ k, ContinuousAt (num k) x := fun k => continuousAt_of_holoOn (hnumH k) hxU'
  have hratC : ∀ k, ContinuousAt (rat k) x := fun k =>
    ((hnumC k).div (hdenC k) (hm k)).div continuousAt_const (hcx k)
  have hrat1 : ∀ k, rat k x = 1 := by
    intro k
    have := ex ⟨k, m k⟩
    have h1 : den k x ≠ 0 := hm k
    have h2 := hcx k
    simp only [rat, num, den] at h1 ⊢
    rw [this]
    field_simp
  have hev : ∀ᶠ y in 𝓝 x, y ∈ R.U x ∧ h y ∈ R'.U (h x) ∧ ∀ k, den k y ≠ 0 ∧ rat k y ∈ Complex.slitPlane := by
    have e1 : ∀ᶠ y in 𝓝 x, y ∈ R.U x := (R.isOpen_U x).mem_nhds hxU
    have e2 : ∀ᶠ y in 𝓝 x, h y ∈ R'.U (h x) := ((R'.isOpen_U (h x)).preimage hh.1).mem_nhds hxU'
    have e3 : ∀ᶠ y in 𝓝 x, ∀ k, den k y ≠ 0 ∧ rat k y ∈ Complex.slitPlane := by
      refine eventually_all.2 fun k => ((hdenC k).eventually_ne (hm k)).and ?_
      exact (hratC k).eventually_mem (Complex.isOpen_slitPlane.mem_nhds (by
        simpa only [hrat1 k] using Complex.one_mem_slitPlane))
    exact e1.and (e2.and e3)
  obtain ⟨V, hVs, hVo, hxV⟩ := mem_nhds_iff.1 hev
  refine ⟨V, hVo, hxV, fun y => -∑ k, (a (κ k) : ℂ) * (Complex.log (rat k y) + (Real.log ‖cx k‖ : ℂ)), ?_, ?_⟩
  · intro j u hu
    obtain ⟨hy1, hy2, hy3⟩ := hVs hu.2
    have hd : ∀ k, AnalyticAt ℂ (fun u => den k ((R.A.chart j).symm u)) u := fun k =>
      hdenH k j u ⟨hu.1, hy1⟩
    have hn : ∀ k, AnalyticAt ℂ (fun u => num k ((R.A.chart j).symm u)) u := fun k =>
      hnumH k j u ⟨hu.1, hy2⟩
    have hr : ∀ k, AnalyticAt ℂ (fun u => rat k ((R.A.chart j).symm u)) u := fun k =>
      ((hn k).div (hd k) (hy3 k).1).div analyticAt_const (hcx k)
    have hl : ∀ k, AnalyticAt ℂ (fun u => (a (κ k) : ℂ) * (Complex.log (rat k ((R.A.chart j).symm u)) +
        (Real.log ‖cx k‖ : ℂ))) u := fun k =>
      analyticAt_const.mul (((hr k).clog (hy3 k).2).add analyticAt_const)
    exact (Finset.analyticAt_fun_sum Finset.univ fun k _ => hl k).neg
  · intro y hy
    obtain ⟨hy1, hy2, hy3⟩ := hVs hy
    obtain ⟨c, hc, ec⟩ := orbit_near R R' h hb hO hy1 hy2
    have hw : R'.lift (h x) (h y) = torusSmul c (R.lift x y ∘ v) := by
      funext p
      simpa [torusSmul] using ec p
    have hrat : ∀ k, rat k y = c k / cx k := by
      intro k
      have h1 : den k y ≠ 0 := (hy3 k).1
      have h2 := ec ⟨k, m k⟩
      simp only [rat, num, den] at h1 ⊢
      rw [h2]
      field_simp
    have hpos : 0 < refNorm a (R.lift x y) := refNorm_pos a (R.mem x y hy1).1
    have hprod : (∏ k, ‖c k‖ ^ a (κ k)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    have hL : Real.log (refNorm (fun k => a (κ k)) (R'.lift (h x) (h y))) =
        (∑ k, (a (κ k) : ℝ) * Real.log ‖c k‖) + Real.log (refNorm a (R.lift x y)) := by
      rw [hw, refNorm_smul, ← refNorm_block hb ha, Real.log_mul hprod hpos.ne', Real.log_prod]
      · simp only [Real.log_zpow]
      · exact fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    have hG : (-∑ k, (a (κ k) : ℂ) * (Complex.log (rat k y) + (Real.log ‖cx k‖ : ℂ))).re =
        -∑ k, (a (κ k) : ℝ) * Real.log ‖c k‖ := by
      rw [Complex.neg_re, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      have hck := norm_ne_zero_iff.2 (hc k)
      have hcxk := norm_ne_zero_iff.2 (hcx k)
      have hcast : ((a (κ k) : ℤ) : ℂ) = (((a (κ k) : ℤ) : ℝ) : ℂ) := by push_cast; rfl
      rw [hrat k, hcast, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
        Real.log_div hck hcxk]
      ring
    show Real.log (refNorm a (R.lift x y)) - Real.log (refNorm (fun k => a (κ k)) (R'.lift (h x) (h y))) = _
    rw [hL, hG]
    ring

end BlockPot

end GlobalTheory.CompanionTheory.Ar.PB.FA
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocDensAddOfFunContinuousOn
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem locDens_add_ofFun_continuousOn : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X), IsOpen U → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → ∀ j, ContinuousOn (locDens A (fun i => P i + LocPot.ofFun (f i) + Θ) j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) := by
  intro e X _ A U P f Θ hU hP hΘ hf j
  have hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).isOpen_inter_preimage_symm hU
  have hm : Continuous (mdisc : (Fin e → Matrix (Fin e) (Fin e) ℂ) → ℂ) := by
    unfold mdisc; fun_prop
  have hf2 : ∀ k, ContDiffOn ℝ 2 (f k ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) := fun k =>
    (hf k j).of_le (WithTop.coe_le_coe.2 le_top)
  have hH : ContinuousOn (fun y => fun k =>
      (hessC (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y +
        hessC (f k ∘ (A.chart j).symm) y +
        hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y :
          Matrix (Fin e) (Fin e) ℂ))
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    continuousOn_pi.2 fun k =>
      (((hessC_base_continuousOn A (P k) (hP k) j).mono Set.inter_subset_left).add
        (hessC_continuousOn _ _ hVo (hf2 k))).add
        ((hessC_base_continuousOn A Θ hΘ j).mono Set.inter_subset_left)
  have hc := (continuousOn_const (c := (e.factorial : ℝ) * (2 / Real.pi) ^ e)
    (s := (A.chart j).target ∩ (A.chart j).symm ⁻¹' U)).mul
    (Complex.continuous_re.comp_continuousOn (hm.comp_continuousOn hH))
  refine hc.congr fun y hy => ?_
  unfold locDens maDens
  simp only [Function.comp_apply, Pi.mul_apply]
  congr 3
  funext k
  have hP' := potential_contDiffAt A (P k) (hP k) j hy.1
  have hΘ' := potential_contDiffAt A Θ hΘ j hy.1
  have hf' : ContDiffAt ℝ 2 (f k ∘ (A.chart j).symm) y :=
    (hf2 k).contDiffAt (hVo.mem_nhds hy)
  rw [show (fun y' => (P k + LocPot.ofFun (f k) + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) =
    fun y' => ((fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y' +
      (f k ∘ (A.chart j).symm) y') + (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y'
    from rfl]
  rw [hessC_add' _ _ _ (hP'.add hf') hΘ', hessC_add' _ _ _ hP' hf']

end GlobalTheory.CompanionTheory.Ar.Giv
end
