module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermLocalOfFibres
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntertwinerStructure

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiNegBetaL
namespace Formalism.FourierDecayAlt.P.GermRealisation

open Formalism.FourierDecayAlt NumberField

noncomputable section

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def betaL (S : C.HidaSetting E Wp Wq) : ℂ := ((4 * Real.pi / (S.g : ℝ) : ℝ) : ℂ)

theorem psi_betaL (S : C.HidaSetting E Wp Wq) (σ z : ℂ) : G.psi (betaL S) (σ * z) = KB.psiL S σ z := by
  unfold G.psi KB.psiL betaL
  congr 1
  rw [Complex.re_ofReal_mul]
  push_cast
  ring

theorem psi_neg_betaL (S : C.HidaSetting E Wp Wq) (σ z : ℂ) : G.psi (-betaL S) (σ * z) = KB.psiL S (-σ) z := by
  have h : G.psi (-betaL S) (σ * z) = G.psi (betaL S) (-σ * z) := by
    unfold G.psi
    rw [show -betaL S * (σ * z) = betaL S * (-σ * z) by ring]
  rw [h, psi_betaL]

theorem betaL_ne_zero (S : C.HidaSetting E Wp Wq) (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) : betaL S ≠ 0 := by
  have hg0 : 0 < S.g := Nat.mul_pos hg1 hg2
  have hg : (0 : ℝ) < (S.g : ℝ) := by exact_mod_cast hg0
  unfold betaL
  exact Complex.ofReal_ne_zero.mpr (div_ne_zero (by positivity) hg.ne')

end loc

end

end Formalism.FourierDecayAlt.P.GermRealisation
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GenCapRepIntertwine
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Topx1

namespace Formalism.FourierDecayAlt.P.PBI

section gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def GrpInt (S : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (V : Wq →L[ℂ] Wp) : Prop :=
  ∀ hB ∈ UWset k r S.z', hB *ᵥ ν' = ν' → (S.π (m₀ * hB * m₀⁻¹)).comp (V.comp (S.π' hB⁻¹)) = V

theorem gen_dOp_intertwine (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) (V : Wq →L[ℂ] Wp) (hV : GrpInt S ν' m₀ V) {X : B.Mat k r}
    (hX : QrD.InLieW k r S.z' X) (hXν : X *ᵥ ν' = 0) (hY : QrD.InLieW k r S.z (m₀ * X * m₀⁻¹)) :
    (QrD.dOp S.π (m₀ * X * m₀⁻¹)).comp V = V.comp (QrD.dOp S.π' X) := by
  obtain ⟨hmU, -, hiU, -, um, -, -⟩ := vecw_base_parts S hbase
  have key : ∀ t : ℝ, (S.π (NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹)))).comp V =
      V.comp (S.π' (NormedSpace.exp ((t : ℂ) • X))) := by
    intro t
    have hhB := QrD.exp_uw hX t
    have hBν := Qx8.exp_fix hXν t
    set hB := NormedSpace.exp ((t : ℂ) • X) with hhBdef
    have hconj : NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹)) = m₀ * hB * m₀⁻¹ := by
      have h := LeftDerivativeCurves.exp_swap hiU X t
      rw [Matrix.nonsing_inv_nonsing_inv _ um] at h
      calc NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹))
          = m₀ * (m₀⁻¹ * NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹))) := by
            rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ um, Matrix.one_mul]
        _ = m₀ * hB * m₀⁻¹ := by rw [h, Matrix.mul_assoc]
    have h := hV hB hhB hBν
    have hinv := WeylGroupFacts.uw_inv hhB
    have uB := WeylGroupFacts.isUnit_of_uh hhB.1
    rw [hconj]
    calc (S.π (m₀ * hB * m₀⁻¹)).comp V
        = ((S.π (m₀ * hB * m₀⁻¹)).comp (V.comp (S.π' hB⁻¹))).comp (S.π' hB) := by
          rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, ← S.π'_rep.2 _ hinv _ hhB,
            Matrix.nonsing_inv_mul _ uB, S.π'_rep.1]
          rfl
      _ = V.comp (S.π' hB) := by rw [h]
  have hd1 := QrD.dOp_hasDeriv S.π'_rep S.π'_cont hX
  have hd2 := QrD.dOp_hasDeriv S.π_rep S.π_cont hY
  let L1 : (Wq →L[ℂ] Wq) →L[ℂ] (Wq →L[ℂ] Wp) := ContinuousLinearMap.compL ℂ Wq Wq Wp V
  let L2 : (Wp →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq Wp Wp).flip V
  have h1 := (L1.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd1
  have h2 := (L2.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd2
  have hfun : ((L2.restrictScalars ℝ) ∘ fun t : ℝ => S.π (NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹)))) =
      ((L1.restrictScalars ℝ) ∘ fun t : ℝ => S.π' (NormedSpace.exp ((t : ℂ) • X))) := by
    funext t
    exact key t
  rw [hfun] at h2
  exact h2.unique h1

theorem gen_ecOp_intertwine (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) (V : Wq →L[ℂ] Wp) (hV : GrpInt S ν' m₀ V) {m : ℕ}
    {Bs' : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [S.z', ν'] Bs') (a b : Fin m) :
    (QrD.ecOp S.π (Q.unitB (Hpk k r) (fun a => m₀ *ᵥ Bs' a) a b)).comp V =
      V.comp (QrD.ecOp S.π' (Q.unitB (Hpk k r) Bs' a b)) := by
  obtain ⟨hmU, -, -, -, um, -, -⟩ := vecw_base_parts S hbase
  have hBz : Q.IsFrameOf k r [S.z] (fun a => m₀ *ᵥ Bs' a) :=
    vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) (vecw_frame_fwd S hbase hB)
  have hBz' : Q.IsFrameOf k r [S.z'] Bs' := vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  have hBν : Q.IsFrameOf k r [ν'] Bs' := vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  obtain ⟨e1, e2, e3⟩ := vecw_conj_eq hmU um Bs' a b
  have lY := QrD.frame_lie hBz a b
  have lX := QrD.frame_lie hBz' a b
  have lν := QrD.frame_lie hBν a b
  rw [e1, e2, e3] at lY
  unfold QrD.ecOp
  rw [e1, e2, e3, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul, gen_dOp_intertwine S hbase V hV lX.1 lν.1.2 lY.1,
    gen_dOp_intertwine S hbase V hV lX.2 lν.2.2 lY.2]

theorem gen_capRep_intertwine (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) (V : Wq →L[ℂ] Wp) (hV : GrpInt S ν' m₀ V) {m : ℕ}
    {Bs' : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [S.z', ν'] Bs') (w : ℂ) (v : Wq) :
    Q.capRep k r S.π (fun a => m₀ *ᵥ Bs' a) w (V v) = V (Q.capRep k r S.π' Bs' w v) := by
  have hBz : Q.IsFrameOf k r [S.z] (fun a => m₀ *ᵥ Bs' a) :=
    vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) (vecw_frame_fwd S hbase hB)
  have hBz' : Q.IsFrameOf k r [S.z'] Bs' := vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  unfold Q.capRep
  refine vecw_qmF V.toLinearMap _ _ (fun i j y => ?_) id id w v
  have lY := QrD.frame_lie hBz i j
  have lX := QrD.frame_lie hBz' i j
  simp only [ContinuousLinearMap.coe_coe]
  rw [QrD.ecRep_eq S.π_rep S.π_cont lY.1 lY.2, QrD.ecRep_eq S.π'_rep S.π'_cont lX.1 lX.2]
  have h := congrArg (fun L : Wq →L[ℂ] Wp => L y) (gen_ecOp_intertwine S hbase V hV hB i j)
  simpa using h

end gen

open Finset

theorem types_of_grpInt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (S : B.RealPlaceData P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r)
    (TP : Formalism.FourierDecayAlt.Top.TypeProj P S.π S.z (m₀ *ᵥ ν')) (hPl : Q.IsPlace P S.z S.z' S.π S.π')
    (hbase : D.IsBaseFrame S ν' m₀) (V : Wq →L[ℂ] Wp) (hV : GrpInt S ν' m₀ V) :
    ∑ ρ : M.Ty P, (TP.E ρ).comp V = V := by
  obtain ⟨hOK, hz, hz', -, -, hty, hty'⟩ := hPl
  obtain ⟨hmU, hmW, -, -, -, hzeq, -⟩ := vecw_base_parts S hbase
  obtain ⟨hν, hνz, hνν, -, -⟩ := id hbase
  have he : inWb P.k P.r (m₀ *ᵥ ν') := hmW ν' hν
  have hee : herm (Hpk P.k P.r) (m₀ *ᵥ ν') (m₀ *ᵥ ν') = 1 := by rw [Dx2.DF.herm_m0_mulVec_invariant m₀ hmU]; exact hνν
  have hez : herm (Hpk P.k P.r) (m₀ *ᵥ ν') S.z = 0 := by
    rw [hzeq, Qx8.herm_smul_right', Dx2.DF.herm_m0_mulVec_invariant m₀ hmU, hνz, mul_zero]
  obtain ⟨Bs₀', hB₀'⟩ := vecw_frame_exists P.k P.r hOK.k_pos S.z' ν' hz' S.T'_pos hν hνz hνν
  have hB₀ := vecw_frame_fwd S hbase hB₀'
  obtain ⟨S', hInt', -, heig⟩ := branching_proof Wq (parametersUPrimeForU P) (parameters_u_prime_for_u_ok hOK) rfl S.z' ν' S.π' hz'
    S.T'_pos hty' hν hνz hνν
  have heig' : ∀ (σ : M.Ty (parametersUPrimeForU P)) (w : ℂ), ∀ v ∈ S' σ,
      Q.capRep P.k P.r S.π' Bs₀' w v = M.xC (parametersUPrimeForU P) σ (w - ((P.k : ℂ) - 2) / 2) • v :=
    fun σ w v hv => heig Bs₀' hB₀' σ w v hv
  refine ContinuousLinearMap.ext fun f => ?_
  rw [_root_.sum_apply]
  simp only [ContinuousLinearMap.comp_apply]
  have hf : f ∈ ⨆ σ, S' σ := by rw [hInt'.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction S' (motive := fun f => ∑ ρ, TP.E ρ (V f) = V f) hf ?_ ?_ ?_
  · intro σ v hv
    refine vecw_good_of_eig hOK hz S.T_pos hty he hez hee TP hB₀ σ _ fun w => ?_
    rw [gen_capRep_intertwine S hbase V hV hB₀' w v, heig' σ w v hv, map_smul]
  · simp
  · intro a b ha hb
    simp only [map_add (f := _), Finset.sum_add_distrib, ha, hb]

end Formalism.FourierDecayAlt.P.PBI
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCGenToQQ
noncomputable section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsv_add (A C : Wq →L[ℂ] Wp) : B.hsVec (A + C) = B.hsVec A + B.hsVec C := by
  unfold B.hsVec
  rw [← WithLp.toLp_add]
  rfl

theorem hsv_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  rw [← WithLp.toLp_smul]
  rfl

end hs

section intw

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
  {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

def Intw (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (A : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (A' : MA.A P (MA.DQ P)) : Prop :=
  ∀ Φ, trR P Bs e (A.1 Φ) = MA.actA P A' (trR P Bs e Φ)

theorem rawR_add (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) :
    rawR P Bs.μsec e ((Φ + Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ + rawR P Bs.μsec e (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
  funext q
  simp only [rawR, Submodule.coe_add, Pi.add_apply, hsv_add, inner_add_right, mul_add]

theorem rawR_smul (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) :
    rawR P Bs.μsec e ((c • Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
      c • rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
  funext q
  simp only [rawR, Submodule.coe_smul, Pi.smul_apply, hsv_smul, inner_smul_right, smul_eq_mul]
  ring

theorem toSm_smul' {u : MA.Qp P.r P.TT → ℂ} (c : ℂ) (hu : u ∈ MA.smSub P.r P.TT) :
    MA.toSm P (c • u) = c • MA.toSm P u := by
  apply Subtype.ext
  funext q
  simp [toSm_of_mem P hu, toSm_of_mem P (Subalgebra.smul_mem _ hu c)]

end intw

section clos

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
  {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem trR_add (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
    (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : trR P Bs e (Φ + Ψ) = trR P Bs e Φ + trR P Bs e Ψ := by
  funext ρ
  simp only [trR, Pi.add_apply]
  rw [rawR_add, toSm_add P (hsm Φ ρ) (hsm Ψ ρ)]

theorem trR_smul (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
    (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : trR P Bs e (c • Φ) = c • trR P Bs e Φ := by
  funext ρ
  simp only [trR, Pi.smul_apply]
  rw [rawR_smul, toSm_smul' c (hsm Φ ρ)]

theorem actA_smulM (c : ℂ) (x : MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (c • x) f = c • MA.actA P x f := by
  funext π
  show ∑ π', ((c • x) π π').1 (f π') = c • ∑ π', (x π π').1 (f π')
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun π' _ => ?_
  rw [Matrix.smul_apply, Algebra.smul_def]
  rfl

theorem actA_one (f : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 1 f = f := by
  funext π
  show ∑ π', ((1 : MA.A P (MA.DQ P)) π π').1 (f π') = f π
  rw [Fintype.sum_eq_single π (fun b hb => by rw [Matrix.one_apply_ne (Ne.symm hb)]; rfl), Matrix.one_apply_eq]
  rfl

theorem actA_alg (c : ℂ) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (algebraMap ℂ (MA.A P (MA.DQ P)) c) f = c • f := by
  rw [Algebra.algebraMap_eq_smul_one, actA_smulM, actA_one]

variable (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
include hsm

theorem intw_add {A B : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' B' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') (hB : Intw P Bs e B B') : Intw P Bs e (A + B) (A' + B') := by
  intro Φ
  show trR P Bs e (A.1 Φ + B.1 Φ) = _
  rw [trR_add hsm, hA, hB, actA_add]

theorem intw_mul {A B : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' B' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') (hB : Intw P Bs e B B') : Intw P Bs e (A * B) (A' * B') := by
  intro Φ
  show trR P Bs e (A.1 (B.1 Φ)) = _
  rw [hA, hB, actA_mul]

theorem intw_alg (c : ℂ) : Intw P Bs e (algebraMap ℂ _ c) (algebraMap ℂ (MA.A P (MA.DQ P)) c) := by
  intro Φ
  show trR P Bs e (c • Φ) = _
  rw [trR_smul hsm, actA_alg]

theorem intw_neg {A : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') : Intw P Bs e (-A) (-A') := by
  have h := intw_mul hsm (intw_alg hsm (-1)) hA
  intro Φ
  have e1 : (-A) = algebraMap ℂ _ (-1) * A := by simp
  have e2 : (-A') = algebraMap ℂ (MA.A P (MA.DQ P)) (-1) * A' := by simp
  rw [e1, e2]
  exact h Φ

theorem intw_sub {A B : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' B' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') (hB : Intw P Bs e B B') : Intw P Bs e (A - B) (A' - B') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact intw_add hsm hA (intw_neg hsm hB)

theorem intw_sum {ι : Type} (s : Finset ι) {A : ι → Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {A' : ι → MA.A P (MA.DQ P)} (h : ∀ i ∈ s, Intw P Bs e (A i) (A' i)) :
    Intw P Bs e (∑ i ∈ s, A i) (∑ i ∈ s, A' i) := by
  first | exact UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum .. | (apply UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (intros; apply UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s A A' h | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s A A' | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s A | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp

end clos

theorem generator_to_quadratic_form : GenToQQ := by
  intro hRS hGT Wp Wq _ _ _ _ _ _ P Bs hPl hk hsec X
  obtain ⟨d, hL, hstar, hrel, hQQ⟩ := Formalism.FourierDecayAlt.P.normal_form_actual Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hPl X
  obtain ⟨e, he, hg⟩ := hGT Wp Wq P Bs hPl hk hsec X d hL hstar hrel hQQ
  have hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT :=
    fun Φ ρ => hRS Wp Wq P Bs hPl hk e he Φ ρ
  refine ⟨e, he, fun Φ Y a b => ?_⟩

  have hζ : Intw P Bs e d.L.ζ (MA.zA P (MA.DQ P)) := fun Φ => (hg Φ).1
  have hζi : Intw P Bs e d.L.ζi (MA.ziA P (MA.DQ P)) := fun Φ => (hg Φ).2.1
  have hζb : Intw P Bs e d.L.ζb (MA.zbA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.1
  have hζbi : Intw P Bs e d.L.ζbi (MA.zbiA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.1
  have hGG : Intw P Bs e d.L.GG (MA.ggA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.1
  have hGGi : Intw P Bs e d.L.GGi (MA.ggiA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.2.1
  have hnab : Intw P Bs e d.L.nab (MA.nabA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.2.2.1
  have hnabs : Intw P Bs e d.L.nabs (MA.nabsA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.2.2.2.1
  have hκ : ∀ f, Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f) := fun f Φ => (hg Φ).2.2.2.2.2.2.2.2.1 f
  have hSS : ∀ l ∈ Finset.Icc 1 (P.k - 1), Intw P Bs e (d.SS l) (MA.SS P (MA.DQ P) l) :=
    fun l hl Φ => (hg Φ).2.2.2.2.2.2.2.2.2.1 l hl
  have hSSs : ∀ l ∈ Finset.Icc 1 (P.k - 1), Intw P Bs e (star (d.SS l)) (star (MA.SS P (MA.DQ P) l)) :=
    fun l hl Φ => (hg Φ).2.2.2.2.2.2.2.2.2.2 l hl

  have hx : Intw P Bs e (d.x Y) (MA.xA P (MA.DQ P) Y) := hκ _
  have hl0 : Intw P Bs e (d.L.l0 Y) (MA.l0A P (MA.DQ P) Y) := by
    show Intw P Bs e (-d.L.nab - algebraMap ℂ _ (Y + 1/2) * (d.L.ζb * d.L.GGi))
      (-MA.nabA P (MA.DQ P) - algebraMap ℂ (MA.A P (MA.DQ P)) (Y + 1 / 2) * (MA.zbA P (MA.DQ P) * MA.ggiA P (MA.DQ P)))
    exact intw_sub hsm (intw_neg hsm hnab) (intw_mul hsm (intw_alg hsm _) (intw_mul hsm hζb hGGi))
  have hm0 : Intw P Bs e (d.L.m0 Y) (MA.m0A P (MA.DQ P) Y) := by
    show Intw P Bs e (-d.L.nabs - algebraMap ℂ _ (Y - 1/2) * (d.L.ζ * d.L.GGi))
      (-MA.nabsA P (MA.DQ P) - algebraMap ℂ (MA.A P (MA.DQ P)) (Y - 1 / 2) * (MA.zA P (MA.DQ P) * MA.ggiA P (MA.DQ P)))
    exact intw_sub hsm (intw_neg hsm hnabs) (intw_mul hsm (intw_alg hsm _) (intw_mul hsm hζ hGGi))
  have hS21 : Intw P Bs e (d.weightedSumBis Y) (MA.weightedSumBis P (MA.DQ P) Y) :=
    intw_sum hsm _ fun l hl => intw_mul hsm (hSS l hl) (hκ _)
  have hS12 : Intw P Bs e (d.S12 Y) (MA.S12 P (MA.DQ P) Y) :=
    intw_sum hsm _ fun l hl => intw_mul hsm (hκ _) (hSSs l hl)
  have hS4 : Intw P Bs e (d.S4 Y) (MA.S4 P (MA.DQ P) Y) :=
    intw_sum hsm _ fun l hl => intw_sum hsm _ fun j hj =>
      intw_mul hsm (intw_mul hsm (hSSs l hl) (hSS j (Finset.mem_of_mem_erase hj))) (hκ _)

  have hent : ∀ a b : Fin 2, Intw P Bs e (d.QQ Y a b) (MA.QQr P (MA.DQ P) Y a b) := by
    intro a b
    fin_cases a <;> fin_cases b
    · show Intw P Bs e (d.L.GGi * (d.κ fun ρ => M.wC P ρ Y) + d.L.GG * d.x Y * d.L.m0 Y * d.L.l0 Y +
          d.L.GG * d.L.m0 Y * d.L.GGi * d.weightedSumBis Y + d.S12 Y * d.L.l0 Y + d.L.GGi * d.S4 Y) (MA.t11 P (MA.DQ P) Y)
      exact intw_add hsm (intw_add hsm (intw_add hsm (intw_add hsm (intw_mul hsm hGGi (hκ _))
        (intw_mul hsm (intw_mul hsm (intw_mul hsm hGG hx) hm0) hl0))
        (intw_mul hsm (intw_mul hsm (intw_mul hsm hGG hm0) hGGi) hS21))
        (intw_mul hsm hS12 hl0)) (intw_mul hsm hGGi hS4)
    · show Intw P Bs e (d.L.GG * d.x Y * d.L.m0 Y + d.S12 Y) (MA.t12 P (MA.DQ P) Y)
      exact intw_add hsm (intw_mul hsm (intw_mul hsm hGG hx) hm0) hS12
    · show Intw P Bs e (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y) (MA.t21 P (MA.DQ P) Y)
      exact intw_add hsm (intw_mul hsm (intw_mul hsm hGG hx) hl0) hS21
    · show Intw P Bs e (d.L.GG * d.x Y) (MA.t22 P (MA.DQ P) Y)
      exact intw_mul hsm hGG hx
  have ht : X.t Y a b = (X.QQ Y a b).1 := rfl
  rw [ht, hQQ Y]
  exact hent a b Φ

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbJConvCpt
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx3
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.CV

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem conv0 (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ)
    (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (c₁ : ℕ)
    (hPP : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), C2.Std k r z z' → C2.PosPt k r z z' γ →
      C2.IsMonomial (Zhat k r z z' γ) → ∃ C : ℝ,
        (∀ σ ∈ C2.Sg k r z z' γ, ∀ s' ∈ Sset k r z',
          B.gN σ + B.gN s' ≤ C * B.gN (σ⁻¹ * γ * s') ^ (c₁ * (r + 1) ^ 2)) ∧
        (∀ s ∈ Sset k r z, ∀ σ' ∈ C2.Sg' k r z z' γ,
          B.gN s + B.gN σ' ≤ C * B.gN (s⁻¹ * γ * σ') ^ (c₁ * (r + 1) ^ 2)))
    (hγ : γ ∈ B.GV k r) (hd : ∀ a, d a ≠ 0) (hZ : Zhat k r D.z D.z' γ = C2.monoP w d)
    (hpos : 0 < Gf k r D.z D.z' γ)
    (hA : 16 * ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A)
    (hFc : ContinuousOn F (B.GV k r)) (sharpFunctionalExponent : ℝ) (hb : ∀ g ∈ B.GV k r, B.gN g ^ A * ‖F g‖ ≤ sharpFunctionalExponent) :
    ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ (Formalism.FourierDecayAlt.D.muR D γ w) θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS := by
  set nn : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hnn
  set bN : ℝ := 4 * ((r : ℝ) * nn + 1) with hbN
  set c : ℕ := (c₁ + 1) * (r + 1) ^ 2 with hc
  set M : ℝ := A / c - 2 * bN with hM
  have hmono : C2.IsMonomial (Zhat k r D.z D.z' γ) := ⟨w, d, hd, hZ⟩
  obtain ⟨CP, hCP, -⟩ := hPP k r D.z D.z' γ (P.Dx2.Rad.std D) ⟨hγ, hpos⟩ hmono

  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc1
  have hnn0 : 0 ≤ nn := by positivity
  have hrn : 0 ≤ (r : ℝ) * nn := by positivity
  have hbN0 : 0 ≤ bN := by positivity
  have hccast : (c : ℝ) = ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 := by rw [hc]; push_cast; ring
  have hAc : 16 * ((r : ℝ) * nn + 1) ≤ A / c := by
    rw [le_div_iff₀ hcpos, hccast]
    calc 16 * ((r : ℝ) * nn + 1) * (((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2)
        = 16 * ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * nn + 1) := by ring
      _ ≤ A := hA
  have hA4 : 4 * bN ≤ A / c := by rw [hbN]; linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast D.k_pos
  have hr2 : ((r : ℝ) + 1) ^ 2 ≤ (r : ℝ) * nn + 1 := by
    rw [hnn]; push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
      (show (0 : ℝ) ≤ r + k - 1 by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])]
  have hMR : 2 * ((r : ℝ) + 1) ^ 2 < M := by
    rw [hM, hbN]; nlinarith [sq_nonneg ((r : ℝ) + 1)]
  have hM0 : 0 ≤ M := by nlinarith [sq_nonneg ((r : ℝ) + 1)]
  have hA0 : 0 ≤ A := by
    have := div_nonneg_iff.mp (show 0 ≤ A / c by linarith)
    rcases this with h | h
    · exact h.1
    · linarith [h.2]

  have hG : P.Dx2.Rad.Good D γ w d := ⟨P.Dx2.Rad.exists_rho D hγ hpos hd hZ, P.Dx2.Rad.u_inj D hγ hpos hd hZ,
    fun ρ hρ => P.Dx2.Rad.u_lstg D hγ hpos hd hZ hρ⟩
  have hR := P.Dx2.Rad.haar_good D hγ hd hG
  have := P.Dx2.OrbJ.sigmaF hR
  have hI := intR D hγ hd hG hMR
  set μR := Formalism.FourierDecayAlt.D.muR D γ w with hμR
  set cR : ℝ := ∫ x, B.gN (Matrix.of x) ^ (-M) ∂μR with hcRdef
  have hone : Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ B.GV k r := by
    rw [Equiv.apply_symm_apply]
    exact (P.unitary_group_closed k r).one_mem
  have hcR : 0 < cR := by
    have := om_pos hR hM0 hI hone
    simpa only [Om, Equiv.apply_symm_apply, Matrix.mul_one] using this

  set cF := max sharpFunctionalExponent 0 with hcF
  have hFb : ∀ g ∈ B.GV k r, ‖F g‖ ≤ cF * B.gN g ^ (-A) := by
    intro g hg
    have h0 := hb g hg
    have hg1 : 1 ≤ B.gN g := P.BetaSesquilinearity.gN_ge_one hg
    have hpw : 0 < B.gN g ^ A := Real.rpow_pos_of_pos (by linarith) _
    rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hpw]
    calc ‖F g‖ * B.gN g ^ A = B.gN g ^ A * ‖F g‖ := by ring
      _ ≤ sharpFunctionalExponent := h0
      _ ≤ cF := le_max_left _ _

  obtain ⟨KW, hKW1, hKW⟩ := UW_bound D.z D.z_mem D.T_pos
  obtain ⟨KW', hKW1', hKW'⟩ := UW_bound D.z' D.z'_mem D.T'_pos
  set K1 := KW * KW' with hK1
  set Kγ := B.gN γ⁻¹ * B.gN γ with hKγ
  have hγ1 : 1 ≤ B.gN γ := P.BetaSesquilinearity.gN_ge_one hγ
  have hγi : B.gN γ⁻¹ = B.gN γ := (P.norm_of_inverse k r γ hγ).1
  have hKγ0 : 0 < Kγ := by rw [hKγ, hγi]; nlinarith
  set Kf := cF * K1 ^ A * CP ^ (A / c) * Kγ ^ bN / cR with hKf
  refine ⟨cut μR M, ⟨cut_meas M, cut_nonneg μR M, fun p hp => cut_norm hR hM0 hI p hp.2.1⟩, ?_⟩
  have hmaj := (maj_int D (A / c - 3 * bN) bN (by linarith) le_rfl).const_mul Kf
  refine Integrable.mono' hmaj ((cut_meas M).aestronglyMeasurable.smul (integrand_aesm D hγ hFc)) ?_
  filter_upwards [P.Dx2.OrbJ.ae_inSS D] with p hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  obtain ⟨ρ, σ, X, hρ, hσ, hnρσ, hσX, hXY, hn'le⟩ := geom D hγ hpos hCP hmono h2 h4
  have hN1 : 1 ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) := P.BetaSesquilinearity.gN_ge_one h2.1
  have hN1' : 1 ≤ B.gN (Matrix.of p.2.2 : B.Mat k r) := P.BetaSesquilinearity.gN_ge_one h4.1
  have hS1 : 1 ≤ B.gN σ := P.BetaSesquilinearity.gN_ge_one hσ
  have hg0 : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2 ∈ B.GV k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h2.1) hγ) h4.1
  have hY1 : 1 ≤ B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) := P.BetaSesquilinearity.gN_ge_one hg0
  have hsgs := P.B7.sgs_mem D ⟨h1, h2, h3, h4⟩ hγ
  have hGg : 0 < B.gN (B.sgs p γ) := by linarith [P.BetaSesquilinearity.gN_ge_one hsgs]
  have hYG : B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) ≤ K1 * B.gN (B.sgs p γ) := by
    have hhu : IsUnit (Matrix.of p.1.1 : B.Mat k r).det := (P.unitary_group_closed k r).unit _ h1.1
    have hh'u : IsUnit (Matrix.of p.2.1 : B.Mat k r).det := (P.unitary_group_closed k r).unit _ h3.1
    have e : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2 =
        (Matrix.of p.1.1 : B.Mat k r) * B.sgs p γ * (Matrix.of p.2.1 : B.Mat k r)⁻¹ := by
      simp only [B.sgs, Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ hhu, Matrix.mul_nonsing_inv _ hh'u, Matrix.mul_one]
    rw [e]
    calc B.gN ((Matrix.of p.1.1 : B.Mat k r) * B.sgs p γ * (Matrix.of p.2.1 : B.Mat k r)⁻¹)
        ≤ B.gN (Matrix.of p.1.1 : B.Mat k r) * B.gN (B.sgs p γ) * B.gN (Matrix.of p.2.1 : B.Mat k r)⁻¹ :=
          (P.B6.gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right (P.B6.gN_mul_le _ _) (P.B6.gN_nonneg _))
      _ ≤ KW * B.gN (B.sgs p γ) * KW' := by
          have a1 := hKW _ h1
          have a2 := hKW' _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv h3)
          have s0 := P.B6.gN_nonneg (B.sgs p γ)
          exact mul_le_mul (mul_le_mul_of_nonneg_right a1 s0) a2 (P.B6.gN_nonneg _)
            (mul_nonneg (by linarith) s0)
      _ = K1 * B.gN (B.sgs p γ) := by rw [hK1]; ring
  have hθ : cut μR M p ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) * B.gN σ ^ M / cR := by
    have hlow := om_lower hR hM0 hI hρ hσ
    have e : Matrix.of.symm (ρ * σ) = p.1.2 := by rw [← hnρσ]; exact Equiv.symm_apply_apply _ _
    rw [e] at hlow
    have hσp : 0 < B.gN σ ^ (-M) := Real.rpow_pos_of_pos (by linarith) _
    have hpos' : 0 < cR * B.gN σ ^ (-M) := mul_pos hcR hσp
    unfold cut
    calc B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) / Om μR M p.1.2
        ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) / (cR * B.gN σ ^ (-M)) :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg (P.B6.gN_nonneg _) _) hpos' hlow
      _ = B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) * B.gN σ ^ M / cR := by
          rw [Real.rpow_neg (P.B6.gN_nonneg σ)]
          have : 0 < B.gN σ ^ M := Real.rpow_pos_of_pos (by linarith) _
          field_simp
  have hθ0 := cut_nonneg μR M p
  have hFv : ‖B.rho D p F γ‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A) :=
    (P.B7.norm_rho_le D ⟨h1, h2, h3, h4⟩ F γ).trans (hFb _ hsgs)
  have hCP0 : 0 < CP := by
    by_contra hle'
    have hle := not_lt.mp hle'
    have := mul_nonpos_of_nonpos_of_nonneg hle
      (pow_nonneg (P.B6.gN_nonneg ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2)) (c₁ * (r + 1) ^ 2))
    linarith
  have hec : c₁ * (r + 1) ^ 2 ≤ c := Nat.mul_le_mul_right _ (Nat.le_succ _)
  have hXY' : X ≤ CP * B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) ^ c :=
    hXY.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY1 hec) hCP0.le)
  have hK10 : 0 < K1 := by rw [hK1]; positivity
  have hkey := key_real hN1 hS1 hσX hY1 hGg hc1 hXY' hn'le hN1' hYG hθ hθ0 hFv (norm_nonneg _) hcR
    (le_max_right _ _) hCP0 hK10 hKγ0 hM hbN0 hA4
  rw [norm_smul, Real.norm_of_nonneg hθ0]
  unfold Formalism.FourierDecayAlt.D.orbIntegrand
  rw [norm_smul, P.B7.norm_xi, one_mul]
  exact hkey

theorem cpt_bound (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef D F) (A : ℝ)
    (hA : 0 ≤ A) : ∃ c : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖F g‖ ≤ c := by
  obtain ⟨hCk, ⟨R, hR⟩, -⟩ := hF
  have hFc : ContinuousOn F (B.GV k r) := P.B5.ckOn_continuousOn hCk
  set K : Set (B.Mat k r) := B.GV k r ∩ {g | B.gN g ≤ R} with hK
  have hgNc : Continuous (fun g : B.Mat k r => B.gN g) := by
    unfold B.gN
    refine Real.continuous_sqrt.comp ?_
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))
  have hKc : IsCompact K := by
    have hbox : IsCompact (Set.univ.pi fun _ : Fin (2 * r + k + 1) =>
        Set.univ.pi fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) (max R 0)) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    refine hbox.of_isClosed_subset ((P.unitary_group_closed k r).closed.inter
      (isClosed_le hgNc continuous_const)) ?_
    intro g hg
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact (entry_le_gN g i j).trans (hg.2.trans (le_max_left _ _))
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hFc.mono Set.inter_subset_left)
  refine ⟨(max R 1) ^ A * max C 0, fun g hg => ?_⟩
  by_cases hF0 : F g = 0
  · rw [hF0, norm_zero, mul_zero]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (le_max_right _ _)
  · have hgR := hR g hg hF0
    have hg1 : 1 ≤ B.gN g := P.BetaSesquilinearity.gN_ge_one hg
    have h1 : B.gN g ^ A ≤ (max R 1) ^ A :=
      Real.rpow_le_rpow (by linarith) (hgR.trans (le_max_left _ _)) hA
    have h2 : ‖F g‖ ≤ max C 0 := (hC g ⟨hg, hgR⟩).trans (le_max_left _ _)
    exact mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)

theorem orbJConv_cpt (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
    (d : Fin (r + 1) → ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hγ : γ ∈ B.GV k r) (hrel : C6.IsRelevant S γ)
    (hd : ∀ a, d a ≠ 0) (hZ : Zhat k r S.z S.z' γ = C2.monoP w d) (hpos : 0 < Gf k r S.z S.z' γ)
    (hF : KB.CptCoef S F) :
    ∃ θ, D.IsNormCut S γ (D.muR S γ w) θ ∧ Integrable (fun p => θ p • D.orbIntegrand S γ F p) S.μSS := by
  obtain ⟨c₁, hPP⟩ := Formalism.FourierDecayAlt.P.polynomial_map_proper
  set A : ℝ := 16 * ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) with hAdef
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨c, hc⟩ := cpt_bound S F hF A hA0
  exact conv0 S γ w d A F c₁ hPP hγ hd hZ hpos le_rfl (P.B5.ckOn_continuousOn hF.1) c hc

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.CV
end
end
