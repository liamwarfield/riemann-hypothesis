module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialTransportPlus
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLEig

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSTr
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSTr

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def hsL : (Wq →L[ℂ] Wp) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) where
  toFun := B.hsVec
  map_add' := VLem.hsV_add
  map_smul' := VLem.hsV_smul

theorem hsVec_sum {ι : Type} (s : Finset ι) (f : ι → (Wq →L[ℂ] Wp)) :
    B.hsVec (∑ i ∈ s, f i) = ∑ i ∈ s, B.hsVec (f i) := map_sum (hsL (Wp := Wp) (Wq := Wq)) f s

theorem fib_sum_smul (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (ζ : ℂ) (a : M.Ty P → ℂ)
    (X : M.Ty P → (Wq →L[ℂ] Wp)) (hX : ∀ ρ, X ρ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ) :
    ∑ ρ, a ρ • X ρ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
  intro p hp
  ext v
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have h := congrArg (fun L : Wq →L[ℂ] Wp => L v) (hX ρ p hp)
  simp only [ContinuousLinearMap.comp_apply] at h
  simp only [ContinuousLinearMap.smul_apply, map_smul, h]

theorem wR_pos (P : M.Par) {ζ : ℂ} (hζ : P.TT < Complex.normSq ζ) : 0 < wR P.k P.TT ζ := by
  unfold wR
  exact Real.sqrt_pos.2 (pow_pos (sub_pos.2 hζ) _)

theorem trR_apply (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ) q = rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q := by
  have h := radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ
  show (MA.toSm P (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) : MA.Qp P.r P.TT → ℂ) q = _
  rw [Gauge.toSm_of_mem P h]

theorem radBase (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
  ⟨hpl.1.k_pos, hpl.2.1, hpl.2.2.1, by rw [hpl.2.2.2.1]; exact hpl.1.T_pos,
    by rw [hpl.2.2.2.2.1]; exact hpl.1.T'_pos, Bs.sec, hpl.2.2.2.2.2.1.2.1, hpl.2.2.2.2.2.2.2.1,
    hpl.2.2.2.2.2.1.2.2.1, hpl.2.2.2.2.2.2.2.2.1⟩

theorem tz_eq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
  rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
  rfl

theorem qr_iff (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (x : (Fin P.r → ℂ) × ℂ) : x ∈ NF.QR P.k P.r Bs.z Bs.z' ↔ x ∈ MA.Qset P.r P.TT := by
  show (x.1 ∈ OmX P.r ∧ _) ↔ ((∀ l, x.1 l ≠ 0) ∧ _)
  rw [tz_eq P Bs hpl]
  rfl

theorem exists_tr (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (F : M.Ty P → MA.SmQ P.r P.TT) :
    ∃ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', trR P Bs e Φ = F ∧
      ∀ q : MA.Qp P.r P.TT, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
        ∑ ρ, ((((wR P.k P.TT q.1.2)⁻¹ : ℝ) : ℂ) * (F ρ : MA.Qp P.r P.TT → ℂ) q) • e ρ q.1.2 := by
  classical
  let g : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := fun x =>
    ∑ ρ, ((((wR P.k P.TT x.2)⁻¹ : ℝ) : ℂ) * MA.ext (F ρ : MA.Qp P.r P.TT → ℂ) x) • e ρ x.2
  let φ := (NF.QR P.k P.r Bs.z Bs.z').indicator g
  have hQR : NF.QR P.k P.r Bs.z Bs.z' = MA.Qset P.r P.TT := Set.ext (qr_iff P Bs hpl)
  have hg : ContDiffOn ℝ ∞ g (MA.Qset P.r P.TT) := by
    refine ContDiffOn.sum fun ρ _ => ?_
    have hw : ContDiffOn ℝ ∞ (fun x : MA.E P.r => (((wR P.k P.TT x.2)⁻¹ : ℝ) : ℂ)) (MA.Qset P.r P.TT) := by
      refine Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_ofReal ?_
      refine ContDiffOn.inv ?_ fun x hx => (wR_pos P hx.2).ne'
      unfold wR
      refine (((Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_normSq.comp contDiff_snd).sub contDiff_const).pow _).contDiffOn.sqrt
        fun x hx => ?_
      have h2 : P.TT < Complex.normSq x.2 := hx.2
      exact (pow_pos (show (0 : ℝ) < Complex.normSq x.2 - P.TT by linarith) _).ne'
    have hF : ContDiffOn ℝ ∞ (MA.ext (F ρ : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) := (F ρ).2
    have he' : ContDiffOn ℝ ∞ (fun x : MA.E P.r => e ρ x.2) (MA.Qset P.r P.TT) :=
      (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
    exact (hw.mul hF).smul he'
  have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [hQR]
      exact hg.congr fun x hx => by simp only [φ, hQR, Set.indicator_of_mem hx]
    · simp only [φ, Set.indicator_of_mem hx]
      have hx' : P.TT < Complex.normSq x.2 := ((qr_iff P Bs hpl x).1 hx).2
      exact fib_sum_smul P Bs x.2 _ _ fun ρ => (he.2 x.2 hx').1 ρ
    · simp [φ, Set.indicator_of_notMem hx]
  obtain ⟨Φ, hΦ, hrad⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π'
    (radBase P Bs hpl) φ hφ
  have hval : ∀ q : MA.Qp P.r P.TT, Φ q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
        ∑ ρ, ((((wR P.k P.TT q.1.2)⁻¹ : ℝ) : ℂ) * (F ρ : MA.Qp P.r P.TT → ℂ) q) • e ρ q.1.2 := by
    intro q
    have hq : q.1 ∈ NF.QR P.k P.r Bs.z Bs.z' := (qr_iff P Bs hpl q.1).2 q.2
    have h := congrFun hrad q.1
    simp only [NF.radR, Set.indicator_of_mem hq, φ] at h
    rw [h]
    simp only [g]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    congr 2
    simp [MA.ext, q.2]
  refine ⟨⟨Φ, hΦ⟩, ?_, hval⟩
  funext ρ
  apply Subtype.ext
  funext q
  rw [trR_apply P Bs hpl hk e he]
  simp only [rawR]
  rw [hval q, hsVec_sum, inner_sum]
  have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
  have horth := (he.2 q.1.2 hζ).2.1
  simp only [VLem.hsV_smul, inner_smul_right, horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have hw : ((wR P.k P.TT q.1.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (wR_pos P hζ).ne'
  push_cast
  field_simp

theorem trR_inj (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) {Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'} (h : trR P Bs e Φ = trR P Bs e Ψ) :
    Φ = Ψ := by
  have hRB := radBase P Bs hpl
  apply Subtype.ext
  refine Formalism.FourierDecayAlt.P.radical_reduction_injective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Φ.2 _ Ψ.2 ?_
  funext x
  by_cases hx : x ∈ NF.QR P.k P.r Bs.z Bs.z'
  · have hxQ : x ∈ MA.Qset P.r P.TT := (qr_iff P Bs hpl x).1 hx
    let q : MA.Qp P.r P.TT := ⟨x, hxQ⟩
    have hζ : P.TT < Complex.normSq x.2 := hxQ.2
    simp only [NF.radR, Set.indicator_of_mem hx]
    have hmΦ := (Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Φ.2).2.1 x hx
    have hmΨ := (Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Ψ.2).2.1 x hx
    simp only [NF.radR, Set.indicator_of_mem hx] at hmΦ hmΨ
    rw [(he.2 x.2 hζ).2.2 _ hmΦ, (he.2 x.2 hζ).2.2 _ hmΨ]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    congr 1
    have h1 := trR_apply P Bs hpl hk e he Φ ρ q
    have h2 := trR_apply P Bs hpl hk e he Ψ ρ q
    rw [h] at h1
    rw [h1] at h2
    simp only [rawR, q] at h2
    have hw : ((wR P.k P.TT x.2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (wR_pos P hζ).ne'
    exact mul_left_cancel₀ hw h2
  · simp [NF.radR, Set.indicator_of_notMem hx]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSTr
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportHer
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTie

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

section reindex

variable {K A S S' : Type}


end reindex

def TowerAt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq),
    ∃ T : D.LevTower k r Wp Wq, T.base.z = Bs.z ∧ T.base.z' = Bs.z' ∧ T.base.π = Bs.π ∧ T.base.π' = Bs.π' ∧
      D.TowerNormalised T

def PlAt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (Bs : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → 2 ≤ P.k → Bs.z = z → Bs.z' = z' → Bs.π = π → Bs.π' = π' →
    ∃ p : KB.Pl P Wp Wq, p.l0 = l0 ∧ p.T.base.z = z ∧ p.T.base.z' = z' ∧ p.T.base.π = π ∧ p.T.base.π' = π'

def shiftCf {r : ℕ} (i : Fin (r + 1)) (c'' : Fin (r - i) → ℂ) : Cf r i :=
  fun l => c'' ⟨l.1.val - i.val, by have := l.1.isLt; have := l.2; omega⟩

def LevTrClauses {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)} {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}
    (μ : Measure (Mt P.k P.r)) (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (i : Fin (P.r + 1)) (c : Fin P.r → ℂ)
    (Di : B.RealPlaceData P.k (P.r - i) Wp Wq) (μi : Measure (Mt P.k (P.r - i)))
    (Li : R.LevelData (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')) (P.r - i))
    (sti : Fr.Start (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')))
    (T : RadSp P.k P.r z z' π π' →ₗ[ℂ] RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π') : Prop :=
  (∀ Φ c'' g, (T Φ : Fn P.k (P.r - i) (Wq →L[ℂ] Wp)) c'' g =
      (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c (shiftCf i c'')) (D.castM (by omega) (ιLev P.k i (P.r - i) g))) ∧
    (∃ κ : ℝ, 0 < κ ∧ ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (shiftCf i c''))) ∧
    (∀ (n : ℕ) (hn : n + i ≤ P.r) (Y : ℂ),
      MRel T (QQi L st ⟨n + i, by omega⟩ Y) (QQi Li sti ⟨n, by omega⟩ Y)) ∧
    ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)),
      (∀ l : Fin (P.r - i), ARel T (bTl L ⟨l.val + i, by omega⟩ w) (bTl Li l w)) ∧
      (∀ (n : ℕ) (hn : n + i ≤ P.r), ARel T (RRi L st ⟨n + i, by omega⟩ w) (RRi Li sti ⟨n, by omega⟩ w)) ∧
      (WordOK P z z' π π' st l0 w → WordOK (JC.parLev P i) Di.z Di.z' Di.π Di.π' sti l0 w)

def LevTransportHer : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (Bs : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → Bs.z = z → Bs.z' = z' → Bs.π = π → Bs.π' = π' →
    ∀ (i : Fin (P.r + 1)) (c : Fin P.r → ℂ), (∀ l : Fin P.r, l.val < i.val → c l ≠ 0) →
    ∃ (Di : B.RealPlaceData P.k (P.r - i) Wp Wq)
      (Xi : ActualOps (JC.parLev P i).k (JC.parLev P i).r Di.z Di.z' Di.π Di.π') (μi : Measure (Mt P.k (P.r - i)))
      (Li : R.LevelData (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')) (P.r - i))
      (sti : Fr.Start (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')))
      (T : RadSp P.k P.r z z' π π' →ₗ[ℂ] RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π'),
      IsData (JC.parLev P i) Di.z Di.z' Di.π Di.π' Xi μi Li sti l0 ∧
        LevTrClauses P μ L st l0 i c Di μi Li sti T ∧
        ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ Φ ∈ herKc S P z z' π π' L st l0 Bs i,
          T Φ ∈ herKc S (JC.parLev P i) Di.z Di.z' Di.π Di.π' Li sti l0 Di 0

def JFScale : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs Bs' : B.RealPlaceData k r Wp Wq), Bs.z = Bs'.z → Bs.z' = Bs'.z' → Bs.π = Bs'.π →
    Bs.π' = Bs'.π' → ∃ κ : ℂ, ∀ F, B.JF Bs F = κ • B.JF Bs' F

def SliceStepHer : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r) (l0 : ℕ), 1 ≤ l0 → l0 ≤ P.k →
    ∀ (Xj : ActualOps (JC.parLev P j).k (JC.parLev P j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
      (μj : Measure (Mt P.k (P.r - j)))
      (Lj : R.LevelData (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (P.r - j))
      (stj : Fr.Start (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')))
      (Xs : ActualOps (JC.parLev P (j + 1)).k (JC.parLev P (j + 1)).r (T.bs (j + 1)).z (T.bs (j + 1)).z'
        (T.bs (j + 1)).π (T.bs (j + 1)).π')
      (μs : Measure (Mt P.k (P.r - (j + 1))))
      (Ls : R.LevelData (Pr (RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π
        (T.bs (j + 1)).π')) (P.r - (j + 1)))
      (sts : Fr.Start (Pr (RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π
        (T.bs (j + 1)).π'))),
    IsData (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Xj μj Lj stj l0 →
    IsData (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' Xs μs Ls
      sts l0 →
    ∀ (Tt : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →ₗ[ℂ]
        RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π') (t : ℂ),
      t ≠ 0 →
      (∀ Φ c g, (Tt Φ : Fn P.k (P.r - (j + 1)) (Wq →L[ℂ] Wp)) c g =
        (Φ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast (by omega) l))
          (D.castM (by omega) (ιLev P.k 1 (P.r - (j + 1)) g))) →
    ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S),
      WordOK (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' stj l0 w →
      ∀ Ψ ∈ herKc S (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Lj stj l0 (T.bs j) 0,
        Tt ((bTl Lj (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) w a b).1 Ψ) ∈
          herKc S (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' Ls sts
            l0 (T.bs (j + 1)) 0

end Formalism.FourierDecayAlt.P.PTie
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTKLine
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem lie_group_existence_holds : KLExists := lie_existence_of_iso_group KLIso.lie_algebra_isomorphism_holds lie_group_realization

theorem gauge_kappa_line_holds : GTKLine := gTKLine_of_cut lie_eigenvalue_holds lie_weight_at_most_holds lie_group_existence_holds

theorem gauge_kappa_holds : GTKap := GTK.gauge_kappa_of_point_line gauge_kappa_pointwise_holds gauge_kappa_line_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGVsTr
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

open Formalism.FourierDecayAlt.P.CutMP.Gauge

noncomputable section

theorem star_algebraMap_real (P : M.Par) (Y : ℝ) :
    star (algebraMap ℂ (MA.A P (MA.DQ P)) (Y : ℂ)) = algebraMap ℂ (MA.A P (MA.DQ P)) (Y : ℂ) := by
  rw [← algebraMap_star_comm, Complex.star_def, Complex.conj_ofReal]

theorem star_Ts_mul_0 (P : M.Par) (σ : Wd.Site (MA.A P (MA.DQ P))) (Y : ℂ) (V : Wd.M2 (MA.A P (MA.DQ P))) :
    star ((Wd.Ts σ Y * V) 0 0) =
      star (V 0 0) * star (algebraMap ℂ (MA.A P (MA.DQ P)) Y + σ.p) + -(star (V 1 0) * star σ.c) := by
  simp only [Wd.Ts, Formalism.YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, star_add, star_mul, star_neg, neg_mul, mul_neg]

theorem star_Ts_mul_1 (P : M.Par) (σ : Wd.Site (MA.A P (MA.DQ P))) (Y : ℂ) (V : Wd.M2 (MA.A P (MA.DQ P))) :
    star ((Wd.Ts σ Y * V) 1 0) = star (V 0 0) * star σ.ci := by
  simp [Wd.Ts, Formalism.YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two, star_add, star_mul]

theorem actA_sp (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (star (MA.siteA P (MA.DQ P) l).p) f = fun ρ => -MA.eulerQ (TT := P.TT) (M.vcb l) (f ρ) := by
  show MA.actA P (star (MA.sc P (MA.DQ P) _)) f = _
  rw [star_sc, actA_sc]
  rfl

theorem actA_sc' (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (star (MA.siteA P (MA.DQ P) l).c) f = fun ρ => MA.coordQ (TT := P.TT) (M.vcb l) * f ρ := by
  show MA.actA P (star (MA.sc P (MA.DQ P) _)) f = _
  rw [star_sc, actA_sc]
  rfl

theorem actA_sci (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (star (MA.siteA P (MA.DQ P) l).ci) f =
      fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vcb l)) * f ρ := by
  show MA.actA P (star (MA.sc P (MA.DQ P) _)) f = _
  rw [star_sc, actA_sc]
  rfl

section ind

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem vabs_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e) (Y : ℝ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 0) Φ) =
          MA.actA P (star (Vp P Y i 0 0)) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 1) Φ) =
          MA.actA P (star (Vp P Y i 1 0)) (trR P Bs.μsec e Φ)) := by
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) 0) 1) Φ = 0 := rfl
    have v0 : Vp P Y 0 0 0 = 1 := by simp [Vp_zero]
    have v1 : Vp P Y 0 1 0 = 0 := by simp [Vp_zero]
    rw [h0, h1, v0, v1, star_one, star_zero, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    set l : Fin P.r := ⟨i, h⟩ with hl
    have hv : Q.vABs (E := Wq →L[ℂ] Wp) P.r (Y : ℂ) (i + 1) =
        (fun f => (Q.vABs P.r (Y : ℂ) i).1 ((Y : ℂ) • f - pbOp l f) - (Q.vABs P.r (Y : ℂ) i).2 (cbOp l f),
          fun f => (Q.vABs P.r (Y : ℂ) i).1 (cbiOp l f)) := by
      simp only [Q.vABs, dif_pos h, hl]
    set Ψ := (Y : ℂ) • Φ - Q.crd (pbOp l) Φ with hΨ
    have hpb : FamR P Bs Dc (Q.crd (pbOp l) Φ) := famR_opL hΦ l 3
    have hcb : FamR P Bs Dc (Q.crd (cbOp l) Φ) := famR_opL hΦ l 4
    have hcbi : FamR P Bs Dc (Q.crd (cbiOp l) Φ) := famR_opL hΦ l 5
    have hΨf : FamR P Bs Dc Ψ := famR_sub (famR_smul hΦ _) hpb
    obtain ⟨⟨hA, tA⟩, -⟩ := ih (Nat.le_of_lt h) Dc Ψ hΨf
    obtain ⟨-, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc _ hcb
    obtain ⟨⟨hA', tA'⟩, -⟩ := ih (Nat.le_of_lt h) Dc _ hcbi
    have e0 : Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) (i + 1)) 0) Φ =
        Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 0) Ψ - Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 1) (Q.crd (cbOp l) Φ) := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) (i + 1)) 1) Φ =
        Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 0) (Q.crd (cbiOp l) Φ) := by
      rw [hv]; rfl
    have tΨ : trR P Bs.μsec e Ψ =
        MA.actA P (star (algebraMap ℂ (MA.A P (MA.DQ P)) (Y : ℂ) + (MA.siteA P (MA.DQ P) l).p))
          (trR P Bs.μsec e Φ) := by
      rw [hΨ, trR_sub _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hΦ _) ρ) (fun ρ => smR hpl hk he hpb ρ),
        trR_smul, trR_pb hpl hk he hΦ, star_add, star_algebraMap_real, actA_add, actA_algebraMap, actA_sp,
        sub_eq_add_neg]
      rfl
    have tcb : trR P Bs.μsec e (Q.crd (cbOp l) Φ) =
        MA.actA P (star (MA.siteA P (MA.DQ P) l).c) (trR P Bs.μsec e Φ) := by
      rw [actA_sc']
      exact trR_mul hpl hk he hΦ _ hcb (fun c => star (c l)) (fun _ _ => rfl) _ (fun q => coordE_vcb _ _)
    have tcbi : trR P Bs.μsec e (Q.crd (cbiOp l) Φ) =
        MA.actA P (star (MA.siteA P (MA.DQ P) l).ci) (trR P Bs.μsec e Φ) := by
      rw [actA_sci]
      exact trR_mul hpl hk he hΦ _ hcbi (fun c => (star (c l))⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vcb]; exact (star_ne_zero).2 (hx.1 _)), coordE_vcb])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hA hB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hA ρ) (fun ρ => smR hpl hk he hB ρ), tA, tB, tΨ, tcb,
        Vp_succ P Y i h, star_Ts_mul_0, actA_add, actA_mul, actA_neg, actA_mul, sub_eq_add_neg]
    · rw [e1]; exact hA'
    · rw [e1, tA', tcbi, Vp_succ P Y i h, star_Ts_mul_1, actA_mul]

end ind

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

open VLem

theorem gauge_conj_vector_transition : GVsTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he Dc Φ hΦ Y a
  have h := vabs_ind hpl hk he Y P.r le_rfl Dc Φ hΦ
  rw [sitesCommonSpace_v0_eq_Vp]
  fin_cases a
  · exact ⟨h.1.1, fun ρ => congrFun h.1.2 ρ⟩
  · exact ⟨h.2.1, fun ρ => congrFun h.2.2 ρ⟩

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end
