module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NfRadOrder0OfRadRed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.XepolNatDegree
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadDZKapLeft
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadDZCompLeft
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section closure

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

abbrev Coef (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] : Type :=
  (j : ℕ) → ℂ → (ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp))

abbrev AnnZ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) : Set ℂ :=
  {ζ : ℂ | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ}

abbrev Dj (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (j : ℕ)
    (q : (Fin P.r → ℂ) × ℂ) : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) :=
  iteratedFDeriv ℝ j (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec Φ (q.1, ζ)) q.2

def Rep (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
    (n : ℕ) (A : Coef Wp Wq) : Prop :=
  (∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A j) (AnnZ P Bs)) ∧
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
        ∑ j ∈ Finset.range (n + 1), A j q.2 (Dj P Bs (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) j q)

theorem rep_ext {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {n m : ℕ} (hnm : n ≤ m) {A : Coef Wp Wq}
    (h : Rep P Bs T n A) : Rep P Bs T m (fun j ζ => if j ≤ n then A j ζ else 0) := by
  refine ⟨fun j => ?_, fun Φ q hq => ?_⟩
  · by_cases hj : j ≤ n
    · simp only [hj, if_true]; exact h.1 j
    · simp only [hj, if_false]; exact contDiffOn_const
  · rw [h.2 Φ q hq]
    symm
    rw [← Finset.sum_subset (Finset.range_mono (by omega : n + 1 ≤ m + 1))]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have : j ≤ n := by simp at hj; omega
      simp only [this, if_true]
    · intro j _ hj
      have : ¬ j ≤ n := by simp at hj; omega
      simp only [this, if_false, ContinuousLinearMap.zero_apply]

theorem radR_smul' (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (c : ℂ) (F : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
    (x : (Fin P.r → ℂ) × ℂ) :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (c • F) x = c • NF.radR P.k P.r Bs.z Bs.z' Bs.μsec F x := by
  unfold NF.radR
  by_cases hx : x ∈ NF.QR P.k P.r Bs.z Bs.z' <;> simp [hx]

theorem radR_zero'' (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (x : (Fin P.r → ℂ) × ℂ) :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (0 : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x = 0 := by
  unfold NF.radR
  by_cases hx : x ∈ NF.QR P.k P.r Bs.z Bs.z' <;> simp [hx]

theorem radDZ_zero (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) :
    RadDZ P Bs (0 : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) := by
  refine ⟨0, fun _ _ => 0, fun _ => contDiffOn_const, fun Φ q _ => ?_⟩
  have : (((0 : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = 0 := rfl
  rw [this, radR_zero'']
  simp

theorem radDZ_one (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) :
    RadDZ P Bs (1 : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) := by
  refine ⟨0, fun j _ => ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) (fun _ => 0),
    fun _ => contDiffOn_const, fun Φ q _ => ?_⟩
  rw [Finset.sum_range_one]
  show _ = (iteratedFDeriv ℝ 0 (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (q.1, ζ)) q.2)
    (fun _ => 0)
  rw [iteratedFDeriv_zero_apply]
  rfl

theorem radDZ_add {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T1 T2 : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (h1 : RadDZ P Bs T1) (h2 : RadDZ P Bs T2) :
    RadDZ P Bs (T1 + T2) := by
  obtain ⟨n1, A1, hr1⟩ := h1
  obtain ⟨n2, A2, hr2⟩ := h2
  have e1 := rep_ext (by omega : n1 ≤ n1 + n2) hr1
  have e2 := rep_ext (by omega : n2 ≤ n1 + n2) hr2
  refine ⟨n1 + n2, fun j ζ => (if j ≤ n1 then A1 j ζ else 0) + (if j ≤ n2 then A2 j ζ else 0),
    fun j => (e1.1 j).add (e2.1 j), fun Φ q hq => ?_⟩
  have hc : ((T1 + T2) Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = (T1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) + (T2 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := rfl
  rw [hc, Formalism.FourierDecayAlt.P.NFRO.radR_add, e1.2 Φ q hq, e2.2 Φ q hq, ← Finset.sum_add_distrib]
  rfl

theorem radDZ_sum {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {ι : Type*} (s : Finset ι)
    (T : ι → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (h : ∀ i ∈ s, RadDZ P Bs (T i)) :
    RadDZ P Bs (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using radDZ_zero P Bs
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact radDZ_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem radDZ_comp_left {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T T' : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T)
    (Mf : ℂ → ((Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp)))
    (hM : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Mf (AnnZ P Bs))
    (h : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T' Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
        Mf q.2 (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q)) :
    RadDZ P Bs T' := by
  obtain ⟨n, A, hA, hTA⟩ := hT
  refine ⟨n, fun j ζ => (Mf ζ).comp (A j ζ), fun j => hM.clm_comp (hA j), fun Φ q hq => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h Φ q hq, hTA Φ q hq, map_sum]
  rfl

theorem radDZ_fun_left {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T T' : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) (s : ℂ → ℂ)
    (hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s (AnnZ P Bs))
    (h : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T' Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
        s q.2 • NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q) :
    RadDZ P Bs T' :=
  radDZ_comp_left hT (fun ζ => s ζ • ContinuousLinearMap.id ℝ (Wq →L[ℂ] Wp)) (hs.smul contDiffOn_const)
    fun Φ q hq => by rw [h Φ q hq]; rfl

theorem radDZ_smul {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) (c : ℂ) :
    RadDZ P Bs (c • T) :=
  radDZ_fun_left hT (fun _ => c) contDiffOn_const fun Φ q _ => by
    have : ((c • T) Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = c • (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := rfl
    rw [this, radR_smul']

theorem radDZ_neg {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) : RadDZ P Bs (-T) := by
  have := radDZ_smul hT (-1)
  rwa [neg_one_smul] at this

end closure

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab
end

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section pts

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem annZ_eq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    AnnZ P Bs = {ζ : ℂ | P.TT < Complex.normSq ζ} := by
  ext ζ
  simp only [Set.mem_setOf_eq]
  rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
  rfl

theorem radR_fn (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (j : Fin 6) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (q : (Fin P.r → ℂ) × ℂ) (hq : q ∈ NF.QR P.k P.r Bs.z Bs.z') :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (X.fn j Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
      Q.fnVal P.k P.r Bs.z Bs.z' j (NF.muZ P.k P.r Bs.μsec q.2) •
        NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q := by
  unfold NF.radR
  rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
  exact X.fn_apply j Φ _ (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hpl.2.1 hpl.2.2.1 Bs.sec hq)

theorem fnVal_zero (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    {ζ : ℂ} (hζ : ζ ∈ AnnZ P Bs) : Q.fnVal P.k P.r Bs.z Bs.z' 0 (NF.muZ P.k P.r Bs.μsec ζ) = ζ := by
  show Q.zetaL _ _ _ _ _ _ = _
  rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hpl.2.1 hpl.2.2.1 Bs.sec hζ]

theorem fnVal_two (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    {ζ : ℂ} (hζ : ζ ∈ AnnZ P Bs) : Q.fnVal P.k P.r Bs.z Bs.z' 2 (NF.muZ P.k P.r Bs.μsec ζ) = starRingEnd ℂ ζ := by
  show star (Q.zetaL _ _ _ _ _ _) = _
  rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hpl.2.1 hpl.2.2.1 Bs.sec hζ]
  rfl

theorem fnVal_five (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    {ζ : ℂ} (hζ : ζ ∈ AnnZ P Bs) : Q.fnVal P.k P.r Bs.z Bs.z' 5 (NF.muZ P.k P.r Bs.μsec ζ) =
      (((Complex.normSq ζ - Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' : ℝ)) : ℂ)⁻¹ := by
  show (((Q.GGl _ _ _ _ _ : ℝ)) : ℂ)⁻¹ = _
  unfold Q.GGl
  rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hpl.2.1 hpl.2.2.1 Bs.sec hζ]

theorem ggi_smooth (c : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => (((Complex.normSq ζ - c : ℝ)) : ℂ)⁻¹)
      {ζ : ℂ | c < Complex.normSq ζ} := by
  have hn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => (((Complex.normSq ζ - c : ℝ)) : ℂ)) := by
    have : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => Complex.normSq ζ - c) := by
      simp only [Complex.normSq_apply]
      exact ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
        (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)).sub contDiff_const
    exact Complex.ofRealCLM.contDiff.comp this
  refine hn.contDiffOn.inv fun ζ hζ h0 => ?_
  have h : c < Complex.normSq ζ := hζ
  have : Complex.normSq ζ - c = 0 := by exact_mod_cast h0
  linarith

theorem conj_smooth' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => starRingEnd ℂ ζ) :=
  Complex.conjCLE.contDiff

theorem radDZ_fn_left (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (j : Fin 6) (hj : j = 0 ∨ j = 2 ∨ j = 5)
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) :
    RadDZ P Bs (X.fn j * T) := by
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ζ => Q.fnVal P.k P.r Bs.z Bs.z' j (NF.muZ P.k P.r Bs.μsec ζ)) (AnnZ P Bs) := by
    rcases hj with rfl | rfl | rfl
    · exact (contDiffOn_id (s := AnnZ P Bs)).congr fun ζ hζ => fnVal_zero P Bs hpl hζ
    · exact conj_smooth'.contDiffOn.congr fun ζ hζ => fnVal_two P Bs hpl hζ
    · exact (ggi_smooth _).congr fun ζ hζ => fnVal_five P Bs hpl hζ
  refine radDZ_fun_left hT _ hs fun Φ q hq => ?_
  rw [Module.End.mul_apply, radR_fn P Bs hpl X j _ q hq]

def Lp [FiniteDimensional ℂ Wp] {P : M.Par} (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (ζ : ℂ) :
    (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  ((LinearMap.toContinuousLinearMap (Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem.Lin (B.hsVec (e ρ ζ)))).smulRight (e ρ ζ)).restrictScalars ℝ

theorem Lp_apply [FiniteDimensional ℂ Wp] {P : M.Par} (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (ζ : ℂ)
    (Xv : Wq →L[ℂ] Wp) : Lp e ρ ζ Xv = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec Xv) • e ρ ζ := rfl

theorem Lp_smooth [FiniteDimensional ℂ Wp] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)} (he : IsFrameB P Bs e) (ρ : M.Ty P) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Lp e ρ) (AnnZ P Bs) := by
  rw [contDiffOn_clm_apply]
  intro y
  rw [annZ_eq P Bs hpl]
  exact (((Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn (he.1 ρ)).inner ℂ contDiffOn_const).smul (he.1 ρ)).congr
    fun ζ _ => rfl

theorem radR_fib (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ) (hq : q ∈ NF.QR P.k P.r Bs.z Bs.z') :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q ∈
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' q.2 := by
  intro p hp
  unfold NF.radR
  rw [Set.indicator_of_mem hq]
  have hx := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hpl.2.1 hpl.2.2.1 Bs.sec hq
  have h := Θ.2.2.2 _ hx p.1 hp.1 p.2 hp.2.1
  simp only at h
  rw [hp.2.2] at h
  exact h.symm

theorem radR_kap [FiniteDimensional ℂ Wp] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ)
    (hq : q ∈ NF.QR P.k P.r Bs.z Bs.z') :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((d.κ f).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
      ∑ ρ, f ρ • (inner ℂ (B.hsVec (e ρ q.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q)) • e ρ q.2) := by
  obtain ⟨hpl, hk2, -, -, -, -, -⟩ := hH
  have hζ : P.TT < Complex.normSq q.2 := by
    have h := hq.2
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1] at h
    exact h
  let q' : MA.Qp P.r P.TT := ⟨q, hq.1, hζ⟩
  have hw : ((wR P.k P.TT q.2 : ℝ) : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.2 (ne_of_gt ?_)
    exact Real.sqrt_pos.2 (pow_pos (sub_pos.2 hζ) _)
  have hcoef : ∀ ρ, inner ℂ (B.hsVec (e ρ q.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
      ((d.κ f).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q)) =
      f ρ * inner ℂ (B.hsVec (e ρ q.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q)) := by
    intro ρ
    have hK := congrFun (hk f Φ) ρ
    rw [actA_kap] at hK
    have s1 := radial_space_smoothness Wp Wq P Bs hpl hk2 e he ((d.κ f).1 Φ) ρ
    have s2 := radial_space_smoothness Wp Wq P Bs hpl hk2 e he Φ ρ
    unfold trR at hK
    rw [Formalism.FourierDecayAlt.P.CutMP.Gauge.toSm_of_mem P s1, Formalism.FourierDecayAlt.P.CutMP.Gauge.toSm_of_mem P s2] at hK
    have h3 := congrFun (congrArg Subtype.val hK) q'
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, rawR] at h3
    unfold NF.radR
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
    have h4 : ((wR P.k P.TT q.2 : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ q.2))
        (B.hsVec (((d.κ f).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 (NF.muZ P.k P.r Bs.μsec q.2))) =
        ((wR P.k P.TT q.2 : ℝ) : ℂ) * (f ρ * inner ℂ (B.hsVec (e ρ q.2))
          (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 (NF.muZ P.k P.r Bs.μsec q.2)))) := by
      rw [h3]; ring
    exact mul_left_cancel₀ hw h4
  rw [(he.2 q.2 hζ).2.2 _ (radR_fib P Bs hpl _ q hq)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [hcoef ρ, mul_smul]

def dl {P : M.Par} (ρ : M.Ty P) : M.Ty P → ℂ := fun ρ' => if ρ' = ρ then 1 else 0

theorem radR_kap_dl [FiniteDimensional ℂ Wp] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (ρ : M.Ty P) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ)
    (hq : q ∈ NF.QR P.k P.r Bs.z Bs.z') :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((d.κ (dl ρ)).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
      Lp e ρ q.2 (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q) := by
  rw [radR_kap P Bs X d hH e he hk _ Φ q hq, Finset.sum_eq_single ρ]
  · simp [dl, Lp_apply]
  · intro b _ hb; simp [dl, hb]
  · intro h; exact absurd (Finset.mem_univ ρ) h

theorem radDZ_kap_left [FiniteDimensional ℂ Wp] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (ρ : M.Ty P) {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) :
    RadDZ P Bs ((d.κ (dl ρ)).1 * T) :=
  radDZ_comp_left hT (Lp e ρ) (Lp_smooth P Bs hH.1 he ρ) fun Φ q hq => by
    rw [Module.End.mul_apply, radR_kap_dl P Bs X d hH e he hk ρ _ q hq]

end pts

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab
end

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

section poly

theorem lag_weights (k : ℕ) : ∃ lam : Fin (k + 1) → ℂ, ∀ p : ℂ[X], p.natDegree ≤ k →
    ∑ j : Fin (k + 1), lam j * p.eval ((j : ℕ) : ℂ) = p.coeff (k - 1) := by
  classical
  let v : Fin (k + 1) → ℂ := fun j => ((j : ℕ) : ℂ)
  have hinj : Set.InjOn v (Finset.univ : Finset (Fin (k + 1))) := by
    intro a _ b _ hab
    have h' : ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ) := hab
    exact Fin.ext (by exact_mod_cast h')
  refine ⟨fun j => (Lagrange.basis Finset.univ v j).coeff (k - 1), ?_⟩
  intro p hp
  have hdeg : p.degree < (Finset.univ : Finset (Fin (k + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hp) (by exact_mod_cast Nat.lt_succ_self k)
  conv_rhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Polynomial.coeff_C_mul, mul_comm]

def xpol (P : M.Par) (ρ : M.Ty P) : ℂ[X] := ∏ i ∈ Finset.Icc 1 (P.k - 1), (X + C ((M.rho P ρ i : ℝ) : ℂ))

def xepol (P : M.Par) (l : ℕ) (ρ : M.Ty P) : ℂ[X] :=
  ∏ i ∈ Finset.Icc 1 (P.k - 1) \ {l}, (X + C ((M.rho P ρ i : ℝ) : ℂ))

theorem xpol_eval (P : M.Par) (ρ : M.Ty P) (Y : ℂ) : (xpol P ρ).eval Y = M.xC P ρ Y := by
  simp [xpol, M.xC, Polynomial.eval_prod]

theorem xepol_eval (P : M.Par) (l : ℕ) (ρ : M.Ty P) (Y : ℂ) : (xepol P l ρ).eval Y = M.xEx P {l} ρ Y := by
  simp [xepol, M.xEx, Polynomial.eval_prod]

theorem xpol_monic (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)

theorem xpol_natDegree (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).natDegree = P.k - 1 := by
  unfold xpol
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  simp [Polynomial.natDegree_X_add_C]

theorem xpol_coeff (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).coeff (P.k - 1) = 1 := by
  rw [← xpol_natDegree P ρ]
  exact (xpol_monic P ρ).coeff_natDegree

theorem xepol_natDegree (P : M.Par) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) :
    (xepol P l ρ).natDegree = P.k - 2 := by
  unfold xepol
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hl, Nat.card_Icc]
  omega

end poly

section ring

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

def fl (P : M.Par) (l : ℕ) (ρ : M.Ty P) : M.Ty P → ℂ := fun ρ0 => if M.Up P l ρ0 ρ then 1 else 0

theorem up_func {l : ℕ} {ρ0 ρ ρ' : M.Ty P} (h1 : M.Up P l ρ0 ρ) (h2 : M.Up P l ρ0 ρ') : ρ = ρ' := by
  funext i
  apply Fin.ext
  rw [h1 i, h2 i]

theorem kap_decomp (d : Q.NFData P A) (g : M.Ty P → ℂ) : d.κ g = ∑ ρ0, g ρ0 • d.κ (dl ρ0) := by
  have h : g = ∑ ρ0, g ρ0 • dl ρ0 := by
    funext ρ
    simp [dl, Finset.sum_apply]
  conv_lhs => rw [h]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul]

theorem sum_dl (d : Q.NFData P A) : ∑ ρ, d.κ (dl ρ) = 1 := by
  have h : ∑ ρ, (dl ρ : M.Ty P → ℂ) = 1 := by
    funext x
    simp [dl, Finset.sum_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, h, map_one]

theorem dl_mul_kap (d : Q.NFData P A) (ρ : M.Ty P) (g : M.Ty P → ℂ) :
    d.κ (dl ρ) * d.κ g = g ρ • d.κ (dl ρ) := by
  have h : dl ρ * g = g ρ • dl ρ := by
    funext x
    by_cases hx : x = ρ
    · subst hx
      simp [dl]
    · simp [dl, hx]
  rw [← map_mul, h, map_smul]

theorem kap_comm (d : Q.NFData P A) (hR : d.Rel) (f : M.Ty P → ℂ) {g : A}
    (hg : g ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A)) : d.κ f * g = g * d.κ f := by
  have hm : g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs} := Or.inl (Or.inr hg)
  exact (hR.2.1 f g hm).eq

theorem fns_comm' (d : Q.NFData P A) {x y : A}
    (hx : x ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A))
    (hy : y ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A)) : x * y = y * x :=
  d.L.fns_comm x (Or.inr hx) y (Or.inr hy)

theorem comb {k : ℕ} {lam : Fin (k + 1) → ℂ}
    (hlam : ∀ p : ℂ[X], p.natDegree ≤ k → ∑ j : Fin (k + 1), lam j * p.eval ((j : ℕ) : ℂ) = p.coeff (k - 1))
    (p : ℂ[X]) (hp : p.natDegree ≤ k) (O : A) :
    ∑ j : Fin (k + 1), lam j • (p.eval ((j : ℕ) : ℂ) • O) = p.coeff (k - 1) • O := by
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, hlam p hp]

theorem e10 (d : Q.NFData P A) (hR : d.Rel) (ρ : M.Ty P) (Y : ℂ) :
    d.κ (dl ρ) * d.QQ Y 1 0 =
      (xpol P ρ).eval Y • (-(d.L.GG * d.κ (dl ρ) * d.L.nab)) +
      ((xpol P ρ) * (X + C (1 / 2 : ℂ))).eval Y • (-(d.κ (dl ρ) * d.L.ζb)) +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), ∑ ρ0, (C (fl P l ρ ρ0) * xepol P l ρ0).eval Y • (d.SS l * d.κ (dl ρ0)) := by
  have hG : d.κ (dl ρ) * d.L.GG = d.L.GG * d.κ (dl ρ) := kap_comm d hR _ (by simp)
  have hGGi : d.L.GG * d.L.GGi = 1 := d.L.GG_GGi
  have hζbG : d.L.GG * d.L.ζb = d.L.ζb * d.L.GG := fns_comm' d (by simp) (by simp)
  have hx : d.κ (dl ρ) * d.x Y = (xpol P ρ).eval Y • d.κ (dl ρ) := by
    rw [Q.NFData.x, dl_mul_kap]
    simp only [xpol_eval]
  have key : d.L.GG * d.κ (dl ρ) * (d.L.ζb * d.L.GGi) = d.κ (dl ρ) * d.L.ζb := by
    calc d.L.GG * d.κ (dl ρ) * (d.L.ζb * d.L.GGi) = d.κ (dl ρ) * (d.L.GG * d.L.ζb * d.L.GGi) := by
          rw [← hG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * (d.L.ζb * (d.L.GG * d.L.GGi)) := by rw [hζbG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * d.L.ζb := by rw [hGGi, mul_one]
  show d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y) = _
  rw [mul_add]
  congr 1
  · calc d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.l0 Y)
          = d.L.GG * (d.κ (dl ρ) * d.x Y) * d.L.l0 Y := by
            rw [← mul_assoc, ← mul_assoc, hG]; simp only [mul_assoc]
      _ = (xpol P ρ).eval Y • (d.L.GG * d.κ (dl ρ) * d.L.l0 Y) := by
            rw [hx, mul_smul_comm, smul_mul_assoc]
      _ = _ := by
            rw [R.LevelData.l0, mul_sub, mul_neg, ← Algebra.smul_def, mul_smul_comm, key]
            rw [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
            module
  · rw [Q.NFData.weightedSumBis, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hc : d.κ (dl ρ) * d.SS l = d.SS l * d.κ (fl P l ρ) := by
      apply hR.2.2.2.1 l
      intro ρ0 ρ' hup
      by_cases h : ρ' = ρ
      · subst h
        simp [dl, fl, hup]
      · have hn : ¬ M.Up P l ρ0 ρ := fun h2 => h (up_func hup h2)
        simp [dl, fl, h, hn]
    rw [← mul_assoc, hc, mul_assoc, ← map_mul, kap_decomp, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ρ0 _ => ?_)
    rw [mul_smul_comm]
    congr 1
    simp [Polynomial.eval_mul, Polynomial.eval_C, xepol_eval]

theorem e01 (d : Q.NFData P A) (hR : d.Rel) (ρ : M.Ty P) (Y : ℂ) :
    d.κ (dl ρ) * d.QQ Y 0 1 =
      (xpol P ρ).eval Y • (-(d.L.GG * d.κ (dl ρ) * d.L.nabs)) +
      ((xpol P ρ) * (X - C (1 / 2 : ℂ))).eval Y • (-(d.κ (dl ρ) * d.L.ζ)) +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), (xepol P l ρ).eval Y • (d.κ (dl ρ) * star (d.SS l)) := by
  have hG : d.κ (dl ρ) * d.L.GG = d.L.GG * d.κ (dl ρ) := kap_comm d hR _ (by simp)
  have hGGi : d.L.GG * d.L.GGi = 1 := d.L.GG_GGi
  have hζG : d.L.GG * d.L.ζ = d.L.ζ * d.L.GG := fns_comm' d (by simp) (by simp)
  have hx : d.κ (dl ρ) * d.x Y = (xpol P ρ).eval Y • d.κ (dl ρ) := by
    rw [Q.NFData.x, dl_mul_kap]
    simp only [xpol_eval]
  have key : d.L.GG * d.κ (dl ρ) * (d.L.ζ * d.L.GGi) = d.κ (dl ρ) * d.L.ζ := by
    calc d.L.GG * d.κ (dl ρ) * (d.L.ζ * d.L.GGi) = d.κ (dl ρ) * (d.L.GG * d.L.ζ * d.L.GGi) := by
          rw [← hG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * (d.L.ζ * (d.L.GG * d.L.GGi)) := by rw [hζG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * d.L.ζ := by rw [hGGi, mul_one]
  show d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.m0 Y + d.S12 Y) = _
  rw [mul_add]
  congr 1
  · calc d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.m0 Y)
          = d.L.GG * (d.κ (dl ρ) * d.x Y) * d.L.m0 Y := by
            rw [← mul_assoc, ← mul_assoc, hG]; simp only [mul_assoc]
      _ = (xpol P ρ).eval Y • (d.L.GG * d.κ (dl ρ) * d.L.m0 Y) := by
            rw [hx, mul_smul_comm, smul_mul_assoc]
      _ = _ := by
            rw [R.LevelData.m0, mul_sub, mul_neg, ← Algebra.smul_def, mul_smul_comm, key]
            rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
            module
  · rw [Q.NFData.S12, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← mul_assoc, dl_mul_kap]
    simp only [xepol_eval, smul_mul_assoc]

end ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab
end

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section ring

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

private theorem natDegree_prod_X_add_C_le_card (S : Finset ℕ) (a : ℕ → ℂ) :
    (∏ i ∈ S, (X + C (a i))).natDegree ≤ S.card := by
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_sum (fun i _ => (Polynomial.natDegree_X_add_C (a i)).le)).trans ?_
  simp

private theorem xpol_natDegree_le (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).natDegree ≤ P.k - 1 := by
  have h2 := natDegree_prod_X_add_C_le_card (Finset.Icc 1 (P.k - 1)) (fun i => ((M.rho P ρ i : ℝ) : ℂ))
  beta_reduce at h2
  have h3 : (Finset.Icc 1 (P.k - 1)).card = P.k - 1 := by rw [Nat.card_Icc]; omega
  unfold xpol
  omega

theorem xpol_half_deg (P : M.Par) (hk : 1 ≤ P.k) (ρ : M.Ty P) (s : ℂ) :
    ((xpol P ρ) * (X + C s)).natDegree ≤ P.k := by
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_X_add_C]
  have := xpol_natDegree_le P ρ
  omega

theorem xpol_halfm_deg (P : M.Par) (hk : 1 ≤ P.k) (ρ : M.Ty P) (s : ℂ) :
    ((xpol P ρ) * (X - C s)).natDegree ≤ P.k := by
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_X_sub_C]
  have := xpol_natDegree_le P ρ
  omega

theorem xpol_deg (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).natDegree ≤ P.k := by
  have := xpol_natDegree_le P ρ
  omega

private theorem xepol_natDegree_le (P : M.Par) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) :
    (xepol P l ρ).natDegree ≤ P.k - 2 := by
  have h2 := natDegree_prod_X_add_C_le_card (Finset.Icc 1 (P.k - 1) \ {l}) (fun i => ((M.rho P ρ i : ℝ) : ℂ))
  beta_reduce at h2
  have h3 : (Finset.Icc 1 (P.k - 1) \ {l}).card = P.k - 2 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hl, Nat.card_Icc]; omega
  unfold xepol
  omega

theorem xepol_deg (P : M.Par) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) (c : ℂ) :
    (C c * xepol P l ρ).natDegree ≤ P.k := by
  have := xepol_natDegree_le P hl ρ
  exact (Polynomial.natDegree_C_mul_le c _).trans (by omega)

theorem xepol_coeff (P : M.Par) (hk : 2 ≤ P.k) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) (c : ℂ) :
    (C c * xepol P l ρ).coeff (P.k - 1) = 0 := by
  have := xepol_natDegree_le P hl ρ
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (Polynomial.natDegree_C_mul_le c _) (by omega))

theorem nab_eq (d : Q.NFData P A) (hR : d.Rel) (hk : 2 ≤ P.k) :
    ∃ (lam : Fin (P.k + 1) → ℂ) (e : M.Ty P → ℂ),
      d.L.nab = ∑ ρ, d.L.GGi * (-(∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 1 0)) -
        e ρ • (d.κ (dl ρ) * d.L.ζb)) := by
  classical
  obtain ⟨lam, hlam⟩ := lag_weights P.k
  refine ⟨lam, fun ρ => ((xpol P ρ) * (X + C (1 / 2 : ℂ))).coeff (P.k - 1), ?_⟩
  have key : ∀ ρ, ∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 1 0) =
      -(d.L.GG * d.κ (dl ρ) * d.L.nab) +
        ((xpol P ρ) * (X + C (1 / 2 : ℂ))).coeff (P.k - 1) • (-(d.κ (dl ρ) * d.L.ζb)) := by
    intro ρ
    simp_rw [e10 d hR ρ, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
    rw [comb hlam _ (xpol_deg P ρ), comb hlam _ (xpol_half_deg P (by omega) ρ _), xpol_coeff, one_smul]
    have h3 : ∑ j : Fin (P.k + 1), ∑ l ∈ Finset.Icc 1 (P.k - 1), ∑ ρ0,
        lam j • ((C (fl P l ρ ρ0) * xepol P l ρ0).eval ((j : ℕ) : ℂ) • (d.SS l * d.κ (dl ρ0))) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l hl => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun ρ0 _ => ?_
      rw [comb hlam _ (xepol_deg P hl ρ0 _), xepol_coeff P hk hl, zero_smul]
    rw [h3, add_zero]
  have hρ : ∀ ρ, d.κ (dl ρ) * d.L.nab = d.L.GGi * (-(∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) *
      d.QQ ((j : ℕ) : ℂ) 1 0)) - ((xpol P ρ) * (X + C (1 / 2 : ℂ))).coeff (P.k - 1) • (d.κ (dl ρ) * d.L.ζb)) := by
    intro ρ
    rw [key ρ, smul_neg, neg_add, neg_neg, neg_neg, add_sub_cancel_right, ← mul_assoc, ← mul_assoc,
      d.L.GGi_GG, one_mul]
  calc d.L.nab = (∑ ρ, d.κ (dl ρ)) * d.L.nab := by rw [sum_dl, one_mul]
    _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ρ _ => hρ ρ

theorem nabs_eq (d : Q.NFData P A) (hR : d.Rel) (hk : 2 ≤ P.k) :
    ∃ (lam : Fin (P.k + 1) → ℂ) (e : M.Ty P → ℂ),
      d.L.nabs = ∑ ρ, d.L.GGi * (-(∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 0 1)) -
        e ρ • (d.κ (dl ρ) * d.L.ζ)) := by
  classical
  obtain ⟨lam, hlam⟩ := lag_weights P.k
  refine ⟨lam, fun ρ => ((xpol P ρ) * (X - C (1 / 2 : ℂ))).coeff (P.k - 1), ?_⟩
  have key : ∀ ρ, ∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 0 1) =
      -(d.L.GG * d.κ (dl ρ) * d.L.nabs) +
        ((xpol P ρ) * (X - C (1 / 2 : ℂ))).coeff (P.k - 1) • (-(d.κ (dl ρ) * d.L.ζ)) := by
    intro ρ
    simp_rw [e01 d hR ρ, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
    rw [comb hlam _ (xpol_deg P ρ), comb hlam _ (xpol_halfm_deg P (by omega) ρ _), xpol_coeff, one_smul]
    have h3 : ∑ j : Fin (P.k + 1), ∑ l ∈ Finset.Icc 1 (P.k - 1),
        lam j • ((xepol P l ρ).eval ((j : ℕ) : ℂ) • (d.κ (dl ρ) * star (d.SS l))) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l hl => ?_
      have hd : (xepol P l ρ).natDegree ≤ P.k := by rw [xepol_natDegree P hl]; omega
      rw [comb hlam _ hd, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [xepol_natDegree P hl]; omega),
        zero_smul]
    rw [h3, add_zero]
  have hρ : ∀ ρ, d.κ (dl ρ) * d.L.nabs = d.L.GGi * (-(∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) *
      d.QQ ((j : ℕ) : ℂ) 0 1)) - ((xpol P ρ) * (X - C (1 / 2 : ℂ))).coeff (P.k - 1) • (d.κ (dl ρ) * d.L.ζ)) := by
    intro ρ
    rw [key ρ, smul_neg, neg_add, neg_neg, neg_neg, add_sub_cancel_right, ← mul_assoc, ← mul_assoc,
      d.L.GGi_GG, one_mul]
  calc d.L.nabs = (∑ ρ, d.κ (dl ρ)) * d.L.nabs := by rw [sum_dl, one_mul]
    _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ρ _ => hρ ρ

end ring

section fst

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem fst_mul' (a b : Q.Pr V) : (a * b).1 = a.1 * b.1 := rfl
theorem fst_neg' (a : Q.Pr V) : (-a).1 = -a.1 := rfl
theorem fst_sub' (a b : Q.Pr V) : (a - b).1 = a.1 - b.1 := rfl
theorem fst_smul' (c : ℂ) (a : Q.Pr V) : (c • a).1 = c • a.1 := by
  first
  | rfl
  | exact Prod.smul_fst _ _
theorem fst_sum' {ι : Type*} (s : Finset ι) (f : ι → Q.Pr V) : (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := by
  first
  | exact Prod.fst_sum
  | exact map_sum (AddMonoidHom.fst (Module.End ℂ V) (Module.End ℂ V)ᵐᵒᵖ) f s

end fst

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]

theorem radDZ_expr (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (hT : ∀ (Y : ℂ) (a b : Fin 2), RadDZ P Bs (X.t Y a b))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (lam : Fin (P.k + 1) → ℂ) (c : ℂ) (j0 : Fin 6) (hj0 : j0 = 0 ∨ j0 = 2) (a b : Fin 2) (ρ : M.Ty P) :
    RadDZ P Bs (X.fn 5 * (-(∑ j : Fin (P.k + 1), lam j • ((d.κ (dl ρ)).1 * X.t ((j : ℕ) : ℂ) a b)) -
      c • ((d.κ (dl ρ)).1 * X.fn j0))) := by
  have hpl := hH.1
  refine radDZ_fn_left P Bs hpl X 5 (Or.inr (Or.inr rfl)) ?_
  rw [sub_eq_add_neg]
  refine radDZ_add (radDZ_neg (radDZ_sum _ _ fun j _ => radDZ_smul ?_ _)) (radDZ_neg (radDZ_smul ?_ _))
  · exact radDZ_kap_left P Bs X d hH e he hk ρ (hT _ a b)
  · refine radDZ_kap_left P Bs X d hH e he hk ρ ?_
    simpa using radDZ_fn_left P Bs hpl X j0 (hj0.imp_right Or.inl) (radDZ_one P Bs)

theorem local_nabla_holds : GTCLNab := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH hT e he hk
  have hpl := hH.1
  have hk2 := hH.2.1
  have hL := hH.2.2.2.1
  have hR := hH.2.2.2.2.2.1
  have hQ := hH.2.2.2.2.2.2
  have hQt : ∀ (Y : ℂ) (a b : Fin 2), (d.QQ Y a b).1 = X.t Y a b := by
    intro Y a b
    rw [← hQ Y]
    rfl
  have hGGi : d.L.GGi.1 = X.fn 5 := by rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; rfl
  have hζb : d.L.ζb.1 = X.fn 2 := by rw [hL.2.2.2.2.2.2.2.2.1]; rfl
  have hζ : d.L.ζ.1 = X.fn 0 := by rw [hL.2.2.2.2.2.2.1]; rfl
  obtain ⟨lam, c, hn⟩ := nab_eq d hR hk2
  obtain ⟨lam', c', hns⟩ := nabs_eq d hR hk2
  constructor
  · rw [hn, fst_sum']
    refine radDZ_sum _ _ fun ρ _ => ?_
    rw [fst_mul', fst_sub', fst_neg', fst_sum', fst_smul', fst_mul', hGGi, hζb]
    have hs : ∀ j : Fin (P.k + 1), (lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 1 0)).1 =
        lam j • ((d.κ (dl ρ)).1 * X.t ((j : ℕ) : ℂ) 1 0) := by
      intro j; rw [fst_smul', fst_mul', hQt]
    simp_rw [hs]
    exact radDZ_expr P Bs X d hH hT e he hk lam (c ρ) 2 (Or.inr rfl) 1 0 ρ
  · rw [hns, fst_sum']
    refine radDZ_sum _ _ fun ρ _ => ?_
    rw [fst_mul', fst_sub', fst_neg', fst_sum', fst_smul', fst_mul', hGGi, hζ]
    have hs : ∀ j : Fin (P.k + 1), (lam' j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 0 1)).1 =
        lam' j • ((d.κ (dl ρ)).1 * X.t ((j : ℕ) : ℂ) 0 1) := by
      intro j; rw [fst_smul', fst_mul', hQt]
    simp_rw [hs]
    exact radDZ_expr P Bs X d hH hT e he hk lam' (c' ρ) 0 (Or.inl rfl) 0 1 ρ

end main

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem local_nabla_holds : GTCLNab := LNab.local_nabla_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
