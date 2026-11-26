module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameUnitCriterion
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapSameBaseOrbit
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PChartVelLift
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LintegralFibSum
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeI

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}

def tMat (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    Matrix (Fin (p + q)) (Fin (p + q)) Ω :=
  (Matrix.fromBlocks (Ts (.inr τ)) 0 0 (Ts (.inl τ))).submatrix (blockEquiv p q).symm (blockEquiv p q).symm

def cMin (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (t : StepIx Ψ p q)
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) (I : Finset (Fin (p + q))) : Ω :=
  if e : I.card = (t.2 : ℕ) + 1 then ((aExt C t.1).submatrix J (I.orderEmbOfFin e)).det else 0


open Classical in
def bExt (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (s : Ψ ⊕ Ψ) : Matrix (Fin (p + q)) (Fin (n s)) Ω :=
  fun a j => ∑ l, if posOf p q s l = a then B s l j else 0

def bMin (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (t : StepIx Ψ p q)
    (I : Finset (Fin (p + q))) (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) : Ω :=
  if e : I.card = (t.2 : ℕ) + 1 then ((bExt B t.1).submatrix (I.orderEmbOfFin e) J).det else 0


variable (p q) in
def fullT (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) : StepIx Ψ p q := ⟨s, ⟨rk Ψ p q s - 1, by omega⟩⟩

theorem fullT_base (K₀ : Type) (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) (r : Ψ × Fin (p + q)) :
    blkF (Ψ := Ψ) (p := p) (q := q) K₀ r ≠ some (.inr (fullT p q s h)) := by
  intro hr
  unfold blkF at hr
  split_ifs at hr with hp
  obtain ⟨h1, h2⟩ := hp
  simp only [Option.some.injEq, Sum.inr.injEq] at hr
  unfold stepOf fullT at hr
  have hv := r.2.isLt
  split_ifs at hr with hlt
  · rw [Sigma.mk.inj_iff] at hr
    obtain ⟨hs, hx⟩ := hr
    subst hs
    have hx' := congrArg Fin.val (eq_of_heq hx)
    simp [rk] at hx' h
    omega
  · rw [Sigma.mk.inj_iff] at hr
    obtain ⟨hs, hx⟩ := hr
    subst hs
    have hx' := congrArg Fin.val (eq_of_heq hx)
    simp [rk] at hx' h
    omega

def baseFull (K₀ : Type) (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) :
    NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀) :=
  ⟨.inr (fullT p q s h), fullT_base K₀ s h⟩

def baseInl {K₀ : Type} (k : K₀) : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀) :=
  ⟨.inl k, fun r => by
    classical
    unfold blkF
    split_ifs <;> simp⟩

variable {K₀ : Type} {J₀ : K₀ → Type}

def xcOf [Fintype K₀] (x₀ : (Σ k, J₀ k) → Ω)
    (c : ∀ k : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀),
      baseIdx (idx (p := p) (q := q) J₀ n) (blkF (Ψ := Ψ) (p := p) (q := q) K₀) k) : Ω :=
  ∏ k, x₀ ⟨k, c (baseInl k)⟩

def rowsOf (c : ∀ k : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀),
      baseIdx (idx (p := p) (q := q) J₀ n) (blkF (Ψ := Ψ) (p := p) (q := q) K₀) k)
    (s : Ψ ⊕ Ψ) : Fin (rk Ψ p q s) → Fin (n s) :=
  fun a => c (baseFull K₀ s (by have := a.2; omega)) (Fin.cast (by have := a.2; show _ = rk Ψ p q s - 1 + 1; omega) a)

def zOf (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (c : ∀ k : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀),
      baseIdx (idx (p := p) (q := q) J₀ n) (blkF (Ψ := Ψ) (p := p) (q := q) K₀) k)
    (s : Ψ ⊕ Ψ) : Ω :=
  ((A s).submatrix (rowsOf c s) id).det

theorem xb_full [Fintype Ψ] [Fintype K₀] [∀ k, Fintype (J₀ k)] (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (x₀ : (Σ k, J₀ k) → Ω) (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) (J : Fin (rk Ψ p q s) → Fin (n s)) :
    xb A x₀ ⟨baseFull K₀ s h, fun a => J (Fin.cast (by show _ = rk Ψ p q s; have := a.2; show rk Ψ p q s - 1 + 1 = _; omega) a)⟩ =
      ((A s).submatrix J id).det := by
  simp only [xb, baseFull, xv]
  have e : rk Ψ p q s - 1 + 1 = rk Ψ p q s := by omega
  rw [← Matrix.det_submatrix_equiv_self (finCongr e) ((A s).submatrix J id)]
  rfl

theorem xb_rowsOf [Fintype Ψ] [Fintype K₀] [∀ k, Fintype (J₀ k)] (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (x₀ : (Σ k, J₀ k) → Ω)
    (c : ∀ k : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀),
      baseIdx (idx (p := p) (q := q) J₀ n) (blkF (Ψ := Ψ) (p := p) (q := q) K₀) k)
    (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) :
    xb A x₀ ⟨baseFull K₀ s h, c (baseFull K₀ s h)⟩ = zOf A c s :=
  xb_full A x₀ s h (rowsOf c s)

theorem det_mem_subring {ι : Type} [Fintype ι] [DecidableEq ι] (R : Subring Ω) (M : Matrix ι ι Ω)
    (h : ∀ a b, M a b ∈ R) : M.det ∈ R := by
  rw [Matrix.det_apply]
  refine R.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact R.zsmul_mem (R.prod_mem fun i _ => h _ _) _


open Classical in
def sMin (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (t : StepIx Ψ p q)
    (I : Finset (Fin (p + q))) (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) : Ω :=
  if StrictMono J then bMin B t I J else 0

private theorem card_filter_fin_Ico (N lo hi : ℕ) (hh : hi ≤ N) :
    (Finset.univ.filter (fun a : Fin N => lo ≤ (a : ℕ) ∧ (a : ℕ) < hi)).card = hi - lo := by
  rw [← Nat.card_Ico lo hi]
  apply Finset.card_bij (fun (a : Fin N) _ => (a : ℕ))
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_Ico]
    omega
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro b hb
    simp only [Finset.mem_Ico] at hb
    exact ⟨⟨b, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, rfl⟩

theorem card_stepCols (r : Ψ × Fin (p + q)) :
    (stepCols (p + q) p r.2).card = ((stepOf Ψ p q r).2 : ℕ) + 1 := by
  have hv := r.2.isLt
  unfold stepCols
  by_cases hc : (r.2 : ℕ) < p
  · have hs : stepOf Ψ p q r = ⟨Sum.inl r.1, ⟨r.2, by simp [rk]; omega⟩⟩ := by
      unfold stepOf
      rw [dite_eq_left hc]
    have hc' : (r.2 : ℕ) + 1 ≤ p := hc
    rw [hs]
    simp only [if_pos hc']
    rw [card_filter_fin_Ico _ _ _ (by omega)]
    omega
  · have hs : stepOf Ψ p q r = ⟨Sum.inr r.1, ⟨r.2 - p, by simp [rk]; omega⟩⟩ := by
      unfold stepOf
      rw [dite_eq_right hc]
    have hc' : ¬ ((r.2 : ℕ) + 1 ≤ p) := by omega
    rw [hs]
    simp only [if_neg hc']
    have := card_filter_fin_Ico (p + q) 0 ((r.2 : ℕ) + 1 - p) (by omega)
    simp only [Nat.zero_le, true_and] at this
    rw [this]
    omega

theorem stepRows_pos (r : Ψ × Fin (p + q)) {I : Finset (Fin (p + q))} (h : IsStepRows (p + q) p r.2 I) :
    ∀ a ∈ I, ∃ l, posOf p q (stepOf Ψ p q r).1 l = a := by
  intro a ha
  obtain ⟨-, hsub⟩ := h
  have hmem := hsub ha
  have hv := a.isLt
  by_cases hc : (r.2 : ℕ) < p
  · have hs : stepOf Ψ p q r = ⟨Sum.inl r.1, ⟨r.2, by simp [rk]; omega⟩⟩ := by
      unfold stepOf
      rw [dite_eq_left hc]
    have hc' : (r.2 : ℕ) + 1 ≤ p := hc
    rw [if_pos hc'] at hmem
    simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [hs]
    refine ⟨⟨a - q, by simp [rk]; omega⟩, ?_⟩
    simp only [posOf, wEmb]
    ext
    simp only
    omega
  · have hs : stepOf Ψ p q r = ⟨Sum.inr r.1, ⟨r.2 - p, by simp [rk]; omega⟩⟩ := by
      unfold stepOf
      rw [dite_eq_right hc]
    have hc' : ¬ ((r.2 : ℕ) + 1 ≤ p) := by omega
    rw [if_neg hc'] at hmem
    simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [hs]
    refine ⟨⟨a, by simp [rk]; omega⟩, ?_⟩
    simp only [posOf, omEmb]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedAtlasCompatibility
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedAtlasCompatibility
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem blocks_of_orbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  intro k
  obtain ⟨i, hi⟩ := h' k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem fstPt_blocks {k₀ : K} {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : ∀ o, ∃ i, z ⟨o, i⟩ ≠ 0) :
    ∀ k, ∃ i, fstPt k₀ z ⟨k, i⟩ ≠ 0 := fun k => h (some k)

theorem sndPt_blocks {k₀ : K} {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : ∀ o, ∃ i, z ⟨o, i⟩ ≠ 0) :
    ∀ k, ∃ i, sndPt k₀ z ⟨k, i⟩ ≠ 0 := by
  intro k
  by_cases e : k = k₀
  · subst e
    obtain ⟨i, hi⟩ := h none
    refine ⟨i, ?_⟩
    change z (v₁ k ⟨k, i⟩) ≠ 0
    rw [v₁_self]
    exact hi
  · obtain ⟨i, hi⟩ := h (some k)
    refine ⟨i, ?_⟩
    change z (v₁ k₀ ⟨k, i⟩) ≠ 0
    rw [v₁_ne (p := ⟨k, i⟩) e]
    exact hi

theorem basePart_snd_eq_fst {σ : Type} (blk : σ → Option K) {k₀ : K} (p : σ) (hp : blk p = some k₀)
    (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) :
    basePart blk (sndPt k₀ z) = basePart blk (fstPt k₀ z) := by
  funext q
  obtain ⟨⟨k, hk⟩, i⟩ := q
  have e : k ≠ k₀ := by
    rintro rfl
    exact hk p hp
  change z (v₁ k₀ ⟨k, i⟩) = z (v₀ k₀ ⟨k, i⟩)
  rw [v₁_ne (p := ⟨k, i⟩) e]
  rfl

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ), SameOrbit z₀ (fstPt k₀ (RW.lift x x)) → SameOrbit z₁ (sndPt k₀ (RW.lift x x)) → basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) ∧ SameOrbit (basePart M.blk z₁) (basePart M.blk z₀) ∧ (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) ∧ ∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr hb hW x z₀ z₁ h₀ h₁
  have hL : ∀ o, ∃ i, RW.lift x x ⟨o, i⟩ ≠ 0 := (RW.mem x x (RW.mem_U x)).1
  have hbase : SameOrbit (basePart M.blk z₀) (Rb.lift (pr x) (pr x)) :=
    orbit_trans (basePart_orbit M.blk h₀) (orbit_symm (hW.2.1 x))
  refine ⟨?_, ?_, blocks_of_orbit h₀ (fstPt_blocks hL), blocks_of_orbit h₁ (sndPt_blocks hL)⟩
  · obtain ⟨c, hc, e⟩ := hbase
    rw [e]
    exact ((GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main _ _ _ M.x _ c hc).2 (Rb.mem (pr x) (pr x) (Rb.mem_U _))).1
  · have h₁' := basePart_orbit M.blk h₁
    rw [basePart_snd_eq_fst M.blk (τ, a) hb] at h₁'
    exact orbit_trans h₁' (orbit_symm (basePart_orbit M.blk h₀))

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedAtlasCompatibilityStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_atlas_compatibility : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ), SameOrbit z₀ (fstPt k₀ (RW.lift x x)) → SameOrbit z₁ (sndPt k₀ (RW.lift x x)) → basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) ∧ SameOrbit (basePart M.blk z₁) (basePart M.blk z₀) ∧ (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) ∧ ∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase.main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorOtherSteps
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorOtherSteps
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther

theorem mul_transv_apply {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (ca cb r c : Fin N) :
    (h * (1 + Matrix.single cb ca t)) r c = h r c + if c = ca then t * h r cb else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases hc : c = ca
  · subst hc
    simp [Matrix.mul_apply, Matrix.single_apply, mul_comm]
  · simp [Matrix.mul_apply, Matrix.single_apply, hc, Ne.symm hc]

private lemma det_submatrix_mul_transvection_eq {N k : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (ca cb : Fin N)
    (hne : ca ≠ cb) (f g : Fin k → Fin N) (hg : Function.Injective g)
    (hJ : ca ∈ Set.range g ↔ cb ∈ Set.range g) :
    ((h * (1 + Matrix.single cb ca t)).submatrix f g).det = (h.submatrix f g).det := by
  by_cases hca : ca ∈ Set.range g
  · obtain ⟨qa, hqa⟩ := hca
    obtain ⟨qb, hqb⟩ := hJ.mp ⟨qa, hqa⟩
    have hq : qb ≠ qa := by
      rintro rfl
      exact hne (hqa.symm.trans hqb)
    have hiff : ∀ q, g q = ca ↔ q = qa := fun q => by
      rw [← hqa]
      exact hg.eq_iff
    have hM : (h * (1 + Matrix.single cb ca t)).submatrix f g
        = h.submatrix f g * (1 + Matrix.single qb qa t) := by
      ext p q
      simp only [Matrix.submatrix_apply, mul_transv_apply, hqb, hiff]
    have h1 : (1 + Matrix.single qb qa t : Matrix (Fin k) (Fin k) ℂ) = Matrix.transvection qb qa t :=
      rfl
    rw [hM, Matrix.det_mul, h1, Matrix.det_transvection_of_ne qb qa hq t, mul_one]
  · congr 1
    ext p q
    have hq : g q ≠ ca := fun hh => hca ⟨q, hh⟩
    simp only [Matrix.submatrix_apply, mul_transv_apply, hq, if_false, add_zero]

theorem minorIJ_transv {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (ca cb : Fin N) (hne : ca ≠ cb)
    (I J : Finset (Fin N)) (hJ : ca ∈ J ↔ cb ∈ J) :
    minorIJ (h * (1 + Matrix.single cb ca t)) I J = minorIJ h I J := by
  unfold minorIJ
  split_ifs with e
  · apply det_submatrix_mul_transvection_eq h t ca cb hne
    · exact (J.orderEmbOfFin _).injective
    · rw [Finset.range_orderEmbOfFin, Finset.mem_coe, Finset.mem_coe]
      exact hJ
  · rfl

theorem minorIJ_other_step : ∀ (N j : ℕ) (a b ca cb : Fin N), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (i : Fin N), i ≠ a → ∀ I, minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j i) = minorIJ h I (stepCols N j i) := by
  intro N j a b ca cb hjN hb hab hca hcb h t i hi I
  apply minorIJ_transv h t ca cb
  · intro heq
    have := congrArg Fin.val heq
    omega
  · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold lastCol at hca
    have hi' : (i : ℕ) ≠ a := fun h' => hi (Fin.ext h')
    have := a.isLt
    have := b.isLt
    have := i.isLt
    have := ca.isLt
    have := cb.isLt
    split_ifs at hca ⊢ <;> omega

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorOtherStepsStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementary_twist_minor_other_steps : ∀ (N j : ℕ) (a b ca cb : Fin N), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (i : Fin N), i ≠ a → ∀ I, minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j i) = minorIJ h I (stepCols N j i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther.minorIJ_other_step | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther.minorIJ_other_step | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther.minorIJ_other_step <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackFirst
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackFirst
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt

theorem eq_on_block {K : Type} {ι : K → Type} {Kk : Type} {ιk : Kk → Type} {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) {a b : (Σ k, ι k) → ℂ} (h : a ∘ v = b ∘ v)
    {k : K} (hk : k ∈ Set.range κ) (m : ι k) : a ⟨k, m⟩ = b ⟨k, m⟩ := by
  obtain ⟨q, hq⟩ := hb.2.2.2 ⟨k, m⟩ hk
  rw [← hq]
  exact congrFun h q

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ (x y' : R.X) (z : (Σ k, ι k) → ℂ), y' ∈ R.U x → pr y' ∉ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → z ∘ v = R.lift x y' → stepPh M BM p v R pr y' = stepGap M BM p z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr H x y' z hy' hpr hz hzv
  obtain ⟨hb, hr, -, H1⟩ := H
  obtain ⟨z₀, hz₀, hz₀v, hz₀o⟩ := H1 y'
  have hex : pr y' ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift y' y' :=
    ⟨hpr, z₀, hz₀, hz₀v⟩
  have hph : stepPh M BM p v R pr y' = stepGap M BM p hex.2.choose := by
    unfold stepPh
    rw [dite_eq_left hex]
  obtain ⟨hz₁, hz₁v⟩ := hex.2.choose_spec
  rw [hph]
  generalize hex.2.choose = z₁ at hz₁ hz₁v

  have hbase : ∀ {a b : (Σ k, ι k) → ℂ}, a ∘ v = b ∘ v → basePart M.blk a = basePart M.blk b := by
    intro a b hab
    funext q
    exact eq_on_block hb hab (hr q.1.1 (Or.inl q.1.2)) q.2
  have hz₁o : SameOrbit (basePart M.blk z₁) (BM.Rb.lift (pr y') (pr y')) := by
    rw [hbase (hz₁v.trans hz₀v.symm)]
    exact hz₀o

  obtain ⟨c, hc, hcl⟩ := R.compat x y' y' ⟨hy', R.mem_U y'⟩
  set c' : K → ℂ := Function.extend κ c 1 with hc'
  have hc'0 : ∀ k, c' k ≠ 0 := by
    intro k
    by_cases hk : ∃ a, κ a = k
    · obtain ⟨a, rfl⟩ := hk
      rw [hc', hb.1.extend_apply]
      exact hc a
    · rw [hc', Function.extend_apply' _ _ _ hk]
      exact one_ne_zero
  set z₂ : (Σ k, ι k) → ℂ := fun q => c' q.1 * z₁ q with hz₂
  have hz₂m : z₂ ∈ mcPts (mCoordIdeal y) :=
    ((GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main K ι Φ y z₁ c' hc'0).2 hz₁).1
  have hz₂v : z₂ ∘ v = z ∘ v := by
    rw [hzv, hcl]
    funext q
    have h1 : z₁ (v q) = R.lift y' y' q := congrFun hz₁v q
    have h2 : c' (v q).1 = c q.1 := by
      rw [hb.2.2.1 q, hc', hb.1.extend_apply]
    simp only [Function.comp, hz₂, h1, h2]
  have ht : stepGap M BM p z₂ = stepGap M BM p z₁ :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_torus K ι Φ y Ψ N j M n BM p z₁ c' hc'0 hz₁.1
  have hz₂o : SameOrbit (basePart M.blk z₂) (BM.Rb.lift (pr y') (pr y')) := by
    obtain ⟨d, hd, hdl⟩ := hz₁o
    refine ⟨fun k => c' k.1 * d k, fun k => mul_ne_zero (hc'0 _) (hd k), ?_⟩
    funext q
    have h1 : basePart M.blk z₁ q = d q.1 * BM.Rb.lift (pr y') (pr y') q := congrFun hdl q
    have h2 : basePart M.blk z₂ q = c' q.1.1 * basePart M.blk z₁ q := rfl
    rw [h2, h1, mul_assoc]
  have hg : stepGap M BM p z₂ = stepGap M BM p z :=
    GlobalTheory.T.flag_gap_same_base_orbit K ι Φ y Ψ N j M n BM p (pr y') z₂ z hpr hz₂m hz hz₂o (hbase hz₂v)
      (fun k hk m => eq_on_block hb hz₂v (hr k (Or.inr hk)) m)
  rw [← ht, hg]

end GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackFirstStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_gap_pullback_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ (x y' : R.X) (z : (Σ k, ι k) → ℂ), y' ∈ R.U x → pr y' ∉ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → z ∘ v = R.lift x y' → stepPh M BM p v R pr y' = stepGap M BM p z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt.main | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocDensDivJacN
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem locDens_div_jacN (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hsm : ∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source →
      ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x))
    (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) (hxS : x ∉ S) :
    locDens A Φ j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) = pushDens A Φ q x := by
  set c := chartIdx A x
  have hc : x ∈ (A.chart c).source := Classical.choose_spec (A.cover x)
  set u := A.chart j x
  have hsu : (A.chart j).symm u = x := (A.chart j).left_inv hx
  set T := A.chart c ∘ (A.chart j).symm with hTdef
  have hT : AnalyticAt ℂ T u :=
    A.holo j c u ⟨(A.chart j).map_source hx, by rw [Set.mem_preimage, hsu]; exact hc⟩
  have hTu : T u = A.chart c x := by simp only [hTdef, Function.comp_apply, hsu]
  have hQc := (hq x hxS c hc).1
  have hQj := (hq x hxS j hx).2
  have heq : q ∘ (A.chart j).symm =ᶠ[𝓝 u] (q ∘ (A.chart c).symm) ∘ T := by
    filter_upwards [((A.chart j).isOpen_inter_preimage_symm (A.chart c).open_source).mem_nhds
      (⟨(A.chart j).map_source hx, by rw [Set.mem_preimage, hsu]; exact hc⟩ :
        u ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart c).source)] with v hv
    simp only [hTdef, Function.comp_apply, (A.chart c).left_inv hv.2]
  have hder : fderiv ℂ (q ∘ (A.chart j).symm) u =
      (fderiv ℂ (q ∘ (A.chart c).symm) (A.chart c x)).comp (fderiv ℂ T u) := by
    rw [heq.fderiv_eq, fderiv_comp u (by rw [hTu]; exact hQc.differentiableAt) hT.differentiableAt,
      hTu]
  have hdet : LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (q ∘ (A.chart c).symm) (A.chart c x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ T u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
    rw [hder]
    exact LinearMap.det_comp _ _
  have hloc : locDens A Φ j u = locDens A Φ c (A.chart c x) *
      ‖LinearMap.det (fderiv ℂ T u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by
    have := GlobalTheory.CompanionTheory.Ar.Giv.MeasOff.locDens_chart_of_contDiffAt A Φ j c
      ((A.chart j).map_source hx) (by rw [hsu]; exact hc)
      (fun i => by rw [hsu]; exact hsm x hxS i c hc)
    rw [hsu, ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq] at this
    exact this
  have hne := hQj
  rw [hdet] at hne
  have hc1 : ‖LinearMap.det (fderiv ℂ (q ∘ (A.chart c).symm) (A.chart c x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ≠ 0 := norm_ne_zero_iff.mpr (left_ne_zero_of_mul hne)
  have hc2 : ‖LinearMap.det (fderiv ℂ T u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (right_ne_zero_of_mul hne)
  unfold jacN pushDens
  rw [hloc, hdet, norm_mul, mul_pow, show chartIdx A x = c from rfl]
  field_simp

theorem sum_fibSum_ae (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (S : Set X)
    (hN : ∀ j, volume ((q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite) (Pt : ChartPartition A)
    (h : Fin A.n → (Fin e → ℂ) → ℝ) (T : X → ℝ)
    (hterm : ∀ j x, x ∈ (A.chart j).source → x ∉ S →
      h j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) = Pt.χ j x * T x) :
    ∀ᵐ y, ∑ j, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (h j) y = ∑ᶠ x ∈ q ⁻¹' {y} \ S, T x := by
  classical
  have hNall : ∀ᵐ y, ∀ j, y ∉ (q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S) :=
    ae_all_iff.mpr fun j => measure_eq_zero_iff_ae_notMem.mp (hN j)
  filter_upwards [hNall] with y hy
  have hterm' : ∀ j, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (h j) y =
      ∑ᶠ x ∈ q ⁻¹' {y} \ S, Pt.χ j x * T x := by
    intro j
    unfold fibSum
    rw [goodT_fibre_eq A q S hq j (hy j),
      finsum_mem_image ((A.chart j).injOn.mono Set.inter_subset_left)]
    refine (finsum_mem_congr (g := fun x => Pt.χ j x * T x) rfl
      fun x (hx : x ∈ (A.chart j).source ∩ (q ⁻¹' {y} \ S)) =>
        hterm j x hx.1 hx.2.2).trans ?_
    refine finsum_mem_inter_support_eq' _ _ _ fun x hx => ?_
    have hχ : Pt.χ j x ≠ 0 := left_ne_zero_of_mul hx
    have hxs : x ∈ (A.chart j).source := Pt.tsupport_subset j (subset_tsupport _ hχ)
    exact ⟨fun h => h.2, fun h => ⟨hxs, h⟩⟩
  simp_rw [hterm']
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  simp_rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul, Pt.sum_eq_one x, one_mul]

end GlobalTheory.CompanionTheory.Ar.Giv.Push
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagFrameAtGoodPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagFrameAtGoodPoint
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FlagPt

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (w : (Σ k, ι k) → ℂ) (H : Ψ → Matrix (Fin N) (Fin N) ℂ), M.IsFrame F → basePart M.blk w ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (basePart M.blk w)) → (∀ τ, IsBlockDiag j (H τ) ∧ (H τ).det ≠ 0) → (∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, w ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M.blk w) p.2 ⟨k, m⟩ (H p.1)) → w ∈ mcPts (mCoordIdeal y) ∧ ∃ z₀, SameOrbit z₀ w ∧ SameOrbit (basePart M.blk z₀) (basePart M.blk w) ∧ M.IsFlagOf F z₀ H := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F w H hF hb hG hH hP
  have hne : ∀ k : NonPluckerBlocks M.blk, w ⟨k.1, F.c k⟩ ≠ 0 := fun k h0 => hG.1 k (by
    show mConeMap (basePart M.blk w) (X ⟨k, F.c k⟩) = 0
    have : basePart M.blk w ⟨k, F.c k⟩ = 0 := h0
    rw [mConeMap, aeval_X, this, map_zero, zero_mul])
  let c : K → ℂ := fun k => if hk : ∀ p, M.blk p ≠ some k then (w ⟨k, F.c ⟨k, hk⟩⟩)⁻¹ else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases hk : ∀ p, M.blk p ≠ some k
    · simp only [c, dif_pos hk]; exact inv_ne_zero (hne ⟨k, hk⟩)
    · simp only [c, dif_neg hk]; exact one_ne_zero
  let z₀ : (Σ k, ι k) → ℂ := fun q => c q.1 * w q
  let c' : NonPluckerBlocks M.blk → ℂ := fun k => c k.1
  have hc' : ∀ k, c' k ≠ 0 := fun k => hc k.1
  have eb : basePart M.blk z₀ = fun q : Σ k, baseIdx ι M.blk k => c' q.1 * basePart M.blk w q := rfl
  obtain ⟨hI, hm⟩ := StepW.TorusAct.main _ _ M.Ω M.x (basePart M.blk w) c' hc'
  obtain ⟨hb₀, hval⟩ := hm hb
  rw [← eb] at hI hb₀ hval
  have hflag : M.IsFlagOf F z₀ H := by
    refine ⟨fun k => ?_, hH, fun p k hp => ?_⟩
    · show c k.1 * w ⟨k.1, F.c k⟩ = 1
      simp only [c, dif_pos k.2]
      exact inv_mul_cancel₀ (hne k)
    · obtain ⟨a, ha, hw⟩ := hP p k hp
      refine ⟨a, ha, fun m => ?_⟩
      have hk : ¬ ∀ p, M.blk p ≠ some k := fun h => h p hp
      show c k * w ⟨k, m⟩ = _
      simp only [c, dif_neg hk, one_mul]
      rw [hw m, CovMap.LocImg.plk]
      simp only [hval]
  have hG₀ : M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) := by rw [hI]; exact hG
  have hz₀ : z₀ ∈ mcPts (mCoordIdeal y) :=
    (((GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.2 F hF z₀ hb₀ hG₀ hflag.1).2 ⟨H, hflag⟩)
  have ho : SameOrbit z₀ w := ⟨c, hc, rfl⟩
  have ho' : SameOrbit w z₀ := ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), by
    funext q
    exact (inv_mul_cancel_left₀ (hc q.1) _).symm⟩
  exact ⟨mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y) ho' hz₀, z₀, ho, ⟨c', hc', rfl⟩, hflag⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FlagPt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagFrameAtGoodPointStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_diag_frame_at_good_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (w : (Σ k, ι k) → ℂ) (H : Ψ → Matrix (Fin N) (Fin N) ℂ), M.IsFrame F → basePart M.blk w ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (basePart M.blk w)) → (∀ τ, IsBlockDiag j (H τ) ∧ (H τ).det ≠ 0) → (∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, w ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M.blk w) p.2 ⟨k, m⟩ (H p.1)) → w ∈ mcPts (mCoordIdeal y) ∧ ∃ z₀, SameOrbit z₀ w ∧ SameOrbit (basePart M.blk z₀) (basePart M.blk w) ∧ M.IsFlagOf F z₀ H := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F w H hF hb hG hH hP
  have hne (k : NonPluckerBlocks M.blk) : w ⟨k.1, F.c k⟩ ≠ 0 := by
    intro hw
    apply hG.1 k
    show mConeMap (basePart M.blk w) (X ⟨k, F.c k⟩) = 0
    have hw' : basePart M.blk w ⟨k, F.c k⟩ = 0 := hw
    rw [mConeMap, aeval_X, hw', map_zero, zero_mul]
  let c (k : K) : ℂ := if hk : ∀ p, M.blk p ≠ some k then (w ⟨k, F.c ⟨k, hk⟩⟩)⁻¹ else 1
  have hc (k : K) : c k ≠ 0 := by
    by_cases hk : ∀ p, M.blk p ≠ some k
    · simpa only [c, dite_eq_left hk] using inv_ne_zero (hne ⟨k, hk⟩)
    · simpa only [c, dite_eq_right hk] using (one_ne_zero : (1 : ℂ) ≠ 0)
  let z₀ (q : Σ k, ι k) : ℂ := c q.1 * w q
  let c' (k : NonPluckerBlocks M.blk) : ℂ := c k.1
  have hc' (k : NonPluckerBlocks M.blk) : c' k ≠ 0 := hc k.1
  have eb : basePart M.blk z₀ = fun q : Σ k, baseIdx ι M.blk k => c' q.1 * basePart M.blk w q := rfl
  obtain ⟨hI, hm⟩ := StepW.TorusAct.main _ _ M.Ω M.x (basePart M.blk w) c' hc'
  obtain ⟨hb₀, hval⟩ := hm hb
  rw [← eb] at hI hb₀ hval
  have hflag : M.IsFlagOf F z₀ H := by
    refine ⟨fun k => ?_, hH, fun p k hp => ?_⟩
    · show c k.1 * w ⟨k.1, F.c k⟩ = 1
      simp only [c, dite_eq_left k.2]
      exact inv_mul_cancel₀ (hne k)
    · obtain ⟨a, ha, hw⟩ := hP p k hp
      refine ⟨a, ha, fun m => ?_⟩
      have hk : ¬ ∀ p, M.blk p ≠ some k := fun h => h p hp
      show c k * w ⟨k, m⟩ = _
      simp only [c, dite_eq_right hk, one_mul]
      rw [hw m, CovMap.LocImg.plk]
      simp only [hval]
  have hG₀ : M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) := by
    rw [hI]
    exact hG
  have hz₀ : z₀ ∈ mcPts (mCoordIdeal y) :=
    ((GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.2 F hF z₀ hb₀ hG₀ hflag.1).mpr
      ⟨H, hflag⟩
  have ho' : SameOrbit w z₀ := ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), by
    funext q
    exact (inv_mul_cancel_left₀ (hc q.1) _).symm⟩
  exact ⟨mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y) ho' hz₀,
    z₀, ⟨c, hc, rfl⟩, ⟨c', hc', rfl⟩, hflag⟩
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionLocalChartPolynomial
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionLocalChartPolynomial
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem proj_diag_ne_zero_iff (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k) :
    SncRes.proj z ⟨k, (i, i)⟩ ≠ 0 ↔ z ⟨k, i⟩ ≠ 0 := by
  simp only [SncRes.proj]
  constructor
  · intro h h0
    apply h
    simp [h0]
  · intro h
    have hn : (0 : ℝ) < ‖z ⟨k, i⟩‖ := norm_pos_iff.2 h
    have hpos : (0 : ℝ) < ∑ j, ‖z ⟨k, j⟩‖ ^ 2 := by
      refine lt_of_lt_of_le (pow_pos hn 2) ?_
      exact Finset.single_le_sum (f := fun j => ‖z ⟨k, j⟩‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i)
    have hden : ((∑ j, ‖z ⟨k, j⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    exact div_ne_zero (mul_ne_zero h ((map_ne_zero _).2 h)) hden

theorem isOpen_alt_bis (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    IsOpen (SncRes.src P p) := by
  have h : SncRes.src P p = ⋂ k, {x : SncRes.Pts P | x.1 ⟨k, (p k, p k)⟩ ≠ 0} := by
    ext x
    simp only [SncRes.src, Set.mem_ofPred_eq, Set.mem_iInter]
    refine forall_congr' fun k => ?_
    rw [← SncRes.proj_rep x]
    exact (proj_diag_ne_zero_iff _ k (p k)).symm
  rw [h]
  refine isOpen_iInter_of_finite fun k => ?_
  have hc : Continuous fun x : SncRes.Pts P => x.1 ⟨k, (p k, p k)⟩ :=
    (continuous_apply _).comp continuous_subtype_val
  exact isOpen_ne_fun hc continuous_const

theorem chart_coord_ratio : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ∀ p' : (k : K) → ι k, (∀ k, eval (SncRes.coord P p x) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) → ∃ O : Set (SncRes.Pts P), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src P p ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ) (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O, (∀ k, eval (SncRes.coord P p y) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) ∧ eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) q ≠ 0 ∧ ∀ l, SncRes.coord P p y l * eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) q = eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) (F l) := by
  intro K _ ι _ P _ p x hx p' hp'
  classical
  have key : ∀ y ∈ SncRes.src P p,
      ((∀ k, eval (SncRes.coord P p y) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) ↔ y ∈ SncRes.src P p') := by
    intro y hy
    simp only [SncRes.eval_lift p y hy, ReciprocityTheory.AnForm.R.affCoord]
    constructor
    · intro h k h0
      exact h k (by simp [h0])
    · intro h k
      exact div_ne_zero (h k) (hy k)
  refine ⟨SncRes.src P p ∩ SncRes.src P p', (isOpen_alt_bis P p).inter (isOpen_alt_bis P p'),
    ⟨hx, (key x hx).1 hp'⟩, Set.inter_subset_left, ∏ k, X ⟨k, p k⟩,
    fun l => X ((Fintype.equivFin (Σ k, ι k)).symm l) *
      ∏ k ∈ Finset.univ.erase ((Fintype.equivFin (Σ k, ι k)).symm l).1, X ⟨k, p k⟩, ?_⟩
  rintro y ⟨hy, hy'⟩
  have hw : (fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) =
      ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) := funext (SncRes.eval_lift p y hy)
  simp only [hw]
  have hone : ∀ k, ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨k, p k⟩ = 1 := fun k => by
    simp [ReciprocityTheory.AnForm.R.affCoord, hy k]
  have hne : ∀ k, ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨k, p' k⟩ ≠ 0 := fun k =>
    div_ne_zero (hy' k) (hy k)
  have ha : ∀ k, ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨k, p k⟩ ≠ 0 := by
    intro k
    have : ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨k, p k⟩ =
        1 / ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨k, p' k⟩ := by
      rw [← hone k]; rfl
    rw [this]
    exact div_ne_zero one_ne_zero (hne k)
  refine ⟨(key y hy).2 hy', ?_, fun l => ?_⟩
  · rw [map_prod]
    simp only [eval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => ha k
  · set q := (Fintype.equivFin (Σ k, ι k)).symm l with hq
    have hcoord : SncRes.coord P p y l = ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) q := rfl
    rw [map_mul, map_prod, map_prod, hcoord]
    simp only [eval_X]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun k => ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨k, p k⟩)
      (Finset.mem_univ q.1), ← mul_assoc]
    congr 1
    have h1 : ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨q.1, p q.1⟩ =
        1 / ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨q.1, p' q.1⟩ := by
      rw [← hone q.1]; rfl
    have h2 : ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) q =
        ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) q /
          ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨q.1, p' q.1⟩ := rfl
    rw [h1, h2, mul_one_div]

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionLocalChartPolynomialStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_resolution_local_chart_polynomial : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ∀ p' : (k : K) → ι k, (∀ k, eval (SncRes.coord P p x) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) → ∃ O : Set (SncRes.Pts P), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src P p ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ) (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O, (∀ k, eval (SncRes.coord P p y) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) ∧ eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) q ≠ 0 ∧ ∀ l, SncRes.coord P p y l * eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) q = eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) (F l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv.chart_coord_ratio | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv.chart_coord_ratio | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv.chart_coord_ratio <;> assumption)
end
end
