module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOfR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.LsSetresAvgW

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RelPtR
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
open Matrix

namespace Formalism.L2.SG.Pf.RelPtR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem rv_crd_fvec (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (a : Fin (D.R.rS + 1)) :
    rv X.B.I v (X.crd ((X.Fu u).fvec a)) = Formalism.L2.SG.RealObj.frm X u 1 v a := by
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
  refine Fin.lastCases ?_ (fun b => ?_) a
  · rw [FlagG.fvec, Fin.snoc_last, X.flagZVector u, Fin.snoc_last]
    rfl
  · rw [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e u, Fin.snoc_castSucc]
    rfl

theorem zhatP_eq (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (τ : D.what₂.Tau) (a b : Fin (D.R.rS + 1)) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ) a b =
      ((rhoF D a * rhoF D b : ℝ) : ℂ) *
        Formalism.L2.SG.RealObj.ZX X u u' 1 (Formalism.L2.SG.RealObj.gamW X u u' w) (vOf X τ) a b := by
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  have hA : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ)
      (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ) a b =
      hJ (X.B.I.ε (vOf X τ)) (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a)
        (uMat ((Formalism.L2.SG.RealObj.gamW X u u' w) (vOf X τ)) *ᵥ
          (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u' τ) b)) := by
    unfold Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm Formalism.L2.SG.Pf.JointAmplitudePoints.gamP Formalism.L2.SG.RealObj.trG hJ
    rw [← hH, ← Formalism.L2.SG.Pf.LTL.star_dot_conjT]
    congr 1
    simp only [Matrix.mulVec_mulVec]
    congr 1
    rw [show (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ *
        (C.Qi τ * uMat ((Formalism.L2.SG.RealObj.gamW X u u' w) (vOf X τ)) * C.Q τ) =
      (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) *
        uMat ((Formalism.L2.SG.RealObj.gamW X u u' w) (vOf X τ)) * C.Q τ by
        simp only [Matrix.mul_assoc], hQQi]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hA, Formalism.L2.SG.Pf.LTL.Q_fvec C u τ a, Formalism.L2.SG.Pf.LTL.Q_fvec C u' τ b, Matrix.mulVec_smul,
    Formalism.L2.SG.Pf.LTL.hJ_smul_real, rv_crd_fvec, rv_crd_fvec]
  rfl

theorem alf_eq (D : D7) (a : Fin (D.R.rS + 1)) : Formalism.MainNotions.BesselShellMomentBounds.alf D a = rhoF D a := by
  unfold Formalism.MainNotions.BesselShellMomentBounds.alf rhoF
  rw [← Real.rpow_intCast]
  congr 1
  push_cast
  ring

theorem ptMat_ptLoc (τ : D.what₂.Tau) (w : Point D.host.E (D.R.rS + 1)) (a b : Fin (D.R.rS + 1)) :
    ptMat (ptLoc D τ w) a b = ((rhoF D a * rhoF D b : ℝ) : ℂ) * embS D τ (ptMat w a b) := by
  have h := Formalism.MainNotions.BesselShellMomentBounds.ptEntry_loc D τ w.1 0 a b
  simp only [Nat.zero_add] at h
  change ptEntry (locBlocksFrom D (rhoReal D) τ 0 w.1) a b = _
  rw [h, alf_eq D a, alf_eq D b]
  rfl

variable (u u' : D.what₂.Word)

theorem zhatO_gamP (w : Point D.host.E (D.R.rS + 1)) (hw : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g)
    (τ : D.what₂.Tau) :
    ZhatO D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ) =
      ptMat (ptLoc D τ w) := by
  have hrep : Formalism.L2.SG.RealObj.IsPtRep X u u' w (Formalism.L2.SG.RealObj.gamW X u u' w) := by
    unfold Formalism.L2.SG.RealObj.gamW
    rw [dite_eq_left hw]
    exact hw.choose_spec
  ext a b
  have h1 := congrFun (congrFun (hrep (vOf X τ)) a) b
  unfold Formalism.L2.SG.RealObj.ZhatO Formalism.L2.SG.RealObj.ptC at h1
  simp only [Matrix.map_apply] at h1
  rw [X.φ_eq, X.ιE.apply_symm_apply, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ] at h1
  unfold ZhatO
  rw [zhatP_eq C u u' w τ a b, ptMat_ptLoc τ w a b, ← h1]
  ring

theorem normSq_dmin (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (g : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) (l : Fin (D.R.rS + 2)) :
    Complex.normSq (Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS z z' g l) =
      Complex.normSq (((ZhatO D.R.k D.R.rS z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
        (Fin.castLE (Nat.le_of_lt_succ l.isLt))).det) := by
  unfold Formalism.QuantumDeterminants.Dmin
  have hM : (ZhatO D.R.k D.R.rS z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
      (Fin.castLE (Nat.le_of_lt_succ l.isLt)) =
      (Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
        (Fin.castLE (Nat.le_of_lt_succ l.isLt)) *
      Matrix.diagonal (fun b : Fin l.val => (-1 : ℂ) ^ (D.R.rS - (Fin.castLE (Nat.le_of_lt_succ l.isLt) b).val)) := by
    ext i j
    simp [ZhatO, Matrix.mul_diagonal, mul_comm]
  rw [hM, Matrix.det_mul, Matrix.det_diagonal, map_mul, map_prod]
  simp [Complex.normSq_neg]

theorem gf_gamP (w : Point D.host.E (D.R.rS + 1)) (hw : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g)
    (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.Gf D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' w τ) =
      Gpt (((D.mem u).A.T : ℕ) : ℝ) (((D.mem u').A.T : ℕ) : ℝ) (ptLoc D τ w) := by
  unfold Formalism.QuantumDeterminants.Gf Gpt
  rw [normSq_dmin, normSq_dmin, zhatO_gamP C u u' w hw τ, Formalism.L2.SG.Pf.LTL.tz_zB C u τ,
    Formalism.L2.SG.Pf.LTL.tz_zB C u' τ]
  rfl

theorem relPtExPR_holds : Formalism.L2.SG.Pf.BDatR.RelPtExPR u u' C := by
  intro w hb hw τ
  refine ⟨Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _, ?_, ?_⟩
  · refine ⟨(1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ),
      fun i j => ⟨fun h => Matrix.one_apply_ne (ne_of_lt h), fun h => by subst h; exact Matrix.one_apply_eq i⟩,
      fun i j => ⟨fun h => Matrix.one_apply_ne (ne_of_lt h).symm, fun h => by subst h; exact Matrix.one_apply_eq i⟩, ?_⟩
    rw [Matrix.one_mul, Matrix.mul_one, zhatO_gamP C u u' w hw τ]
  · rw [gf_gamP C u u' w hw τ]
    exact (hb.2 τ).ne'

end Formalism.L2.SG.Pf.RelPtR
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRhoX
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.AllRowsRhoX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
  Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.AllRowsRho
  Formalism.L2.SG.AllRowsOf Formalism.MainNotions.ArithmeticCylinders

variable {D : D7} (X : HidaSetting D)

theorem exists_b (kv : Σ k : Fin 2, D.nd.PlG k) :
    ∃ b : Fin D.R.r → Fin X.B.I.n → X.B.I.E, IsRedBasis0 X.B.I (wB X (D.naut.plGw kv.1 kv.2)) b := by
  rw [← X.n_eq]
  exact exists_redBasis (I := X.B.I) (w := wB X (D.naut.plGw kv.1 kv.2)) (hp := D.host.g_prime kv.1)
    (hcard := by rw [card_wB, card_res_host])

def redBX (kv : Σ k : Fin 2, D.nd.PlG k) : RedB X.B.I D.R.r where
  w := wB X (D.naut.plGw kv.1 kv.2)
  p := D.host.g kv.1
  hp := D.host.g_prime kv.1
  hcard := by rw [card_wB, card_res_host]
  hm := X.n_eq.symm
  b := Classical.choose (exists_b X kv)
  hb := Classical.choose_spec (exists_b X kv)

def rhoX : KSub X.B.I →* G0g D.nd := MonoidHom.pi fun kv => rhoB (redBX X kv)

theorem rhoX_apply (x : KSub X.B.I) (kv : Σ k : Fin 2, D.nd.PlG k) : rhoX X x kv = rhoB (redBX X kv) x := rfl

theorem goodAt_rhoX (x : KSub X.B.I) : GoodAt X x (rhoX X x) := by
  intro kv
  exact (redMat_iff X _ _ _ _).mpr (redMat0_of (I := X.B.I) (hb := (redBX X kv).hb) (h := rhoB_spec (redBX X kv) x))

theorem redMatB_one_of {I : AutInst} {m : ℕ} (R : RedB I m) {x : I.Gf}
    (h : ∀ i, I.fmat x *ᵥ iv I (R.b i) - iv I (R.b i) ∈ Lq I R.w) :
    RedMatB I R.w R.p R.b x (1 : Matrix (Fin m) (Fin m) (ZMod R.p)) := by
  haveI : Fact (1 < R.p) := ⟨R.hp.one_lt⟩
  intro i
  have hsum : ∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod R.p)) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) •
      iv I (R.b j) = iv I (R.b i) := by
    rw [Finset.sum_eq_single i]
    · simp [Matrix.one_apply_eq, ZMod.val_one]
    · intro j _ hj
      simp [Matrix.one_apply_ne hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hsum]
  exact h i

theorem rhoX_eq_one_iff (x : KSub X.B.I) : rhoX X x = 1 ↔ (x : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
  have hRK : Formalism.L2.SG.AllRowsOf.RedKer X :=
    Formalism.L2.SG.AllRowsOf.redKer_of (X := X) (Formalism.L2.SG.AllRowsOf.redKerOne_of (X := X)
      (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 0) (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 1))
  constructor
  · intro h
    have h1 := goodAt_rhoX X x
    rw [h] at h1
    exact (hRK x x.2).1 h1
  · intro hx
    have hK : (x : X.B.I.Gf) ∈ X.B.I.Kset := x.2
    have hG := Formalism.L2.SG.AllRowsOf.goodAt_one_of_mem_Kg (X := X) hx
    funext kv
    rw [rhoX_apply]
    apply Units.ext
    have hR0 := (redMat_iff X _ _ _ _).mp (hG kv)
    have hR1 := hR0
    simp only [Pi.one_apply, Units.val_one] at hR1
    have hA := Formalism.L2.SG.Pf.AllRowsRedKerA.stepA (I := X.B.I) (redBX X kv).hp (redBX X kv).hcard hK hR1
    have hB : RedMatB X.B.I (redBX X kv).w (redBX X kv).p (redBX X kv).b x 1 :=
      redMatB_one_of (redBX X kv) fun i => by
        have h1 := hA _ (PIW.AdelClassFin.DictLat.iv_mem X.B.I ((redBX X kv).hb.1 i))
        rwa [Matrix.sub_mulVec, Matrix.one_mulVec] at h1
    have h2 := matB_eq (redBX X kv) hK hB
    show ((rhoB (redBX X kv) x : GL (Fin D.R.r) (ZMod (redBX X kv).p)) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (redBX X kv).p)) =
      ((1 : GL (Fin D.R.r) (ZMod (redBX X kv).p)) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (redBX X kv).p))
    rw [Units.val_one]
    exact h2

theorem ES_conj (S : Set (Tup2 D)) (γ P : G0g D.nd) : (ES S).coeff (P⁻¹ * γ * P) = (ES S).coeff γ := by
  unfold ES
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  refine finsum_congr fun a => ?_
  split_ifs
  · refine Finset.prod_congr rfl fun kv _ => ?_
    exact coeff_conj_of_central (D.ntypes.eSer_central kv.1 _) (γ kv) (P kv)
  · rfl

theorem egA_rhoX (a : MonoidAlgebra ℂ (G0g D.nd)) (ha : ∀ γ P : G0g D.nd, a.coeff (P⁻¹ * γ * P) = a.coeff γ)
    (x : KSub X.B.I) : egA X a x = a.coeff (rhoX X x) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) := by
  have h : (x : X.B.I.Gf) ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ :=
    ⟨x.2, rhoX X x, goodAt_rhoX X x⟩
  unfold egA
  rw [dite_eq_left h]
  congr 1
  have hγ := Classical.choose_spec h.2
  have hP : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ P : GL (Fin D.R.r) (ZMod (D.host.g kv.1)),
      (Classical.choose h.2) kv = P⁻¹ * rhoX X x kv * P := by
    intro kv
    have h1 := (redMat_iff X _ _ _ _).mp (goodAt_rhoX X x kv)
    have h2 := (redMat_iff X _ _ _ _).mp (hγ kv)
    exact Formalism.L2.SG.Pf.RedConj0Pf.reduction_conjugacy X.B.I _ _ (redBX X kv).hp (redBX X kv).hcard D.R.r
      (redBX X kv).hm x _ _ h1 h2
  choose P hP using hP
  have e1 : Classical.choose h.2 = P⁻¹ * rhoX X x * P := by
    funext kv
    rw [hP kv]
    rfl
  rw [e1, ha]

def RhoSurj : Prop := ∀ (D : D7) (X : HidaSetting D), Function.Surjective (rhoX X)

end Formalism.L2.SG.Pf.AllRowsRhoX
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PointUniformity
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.ThB Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.LatticeGluingRadicals Formalism.MainNotions.BridgeLemma
  Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut

namespace Formalism.L2.SG.PointUniformity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Minor

variable {D : D7}

theorem lead_sign (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    leadMinorK (ZhatOM Z) l hl * D.host.conj (leadMinorK (ZhatOM Z) l hl) =
      leadMinorK Z l hl * D.host.conj (leadMinorK Z l hl) := by
  have e : ∀ W : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E,
      ((ZhatOM W).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
        (∏ j : Fin l, ((-1 : D.host.E) ^ (D.R.rS - (Fin.castLE hl j).val))) *
          (W.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
    intro W
    rw [← Matrix.det_mul_row]
    rfl
  simp only [leadMinorK]
  rw [e Z, Finset.prod_pow_eq_pow_sum]
  rcases neg_one_pow_eq_or D.host.E (∑ j : Fin l, (D.R.rS - (Fin.castLE hl j).val)) with h | h <;>
    rw [h] <;> simp

theorem gglob_of_cell {T T' : ℕ} (F : LFlag (D.sp.Y 0) D.R.rS (T : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T' : D.host.E))
    (p : Point D.host.E (D.R.rS + 1)) (hc : IsInCell (ZhatOM (ZhatL F F')) p) :
    Gglob D T T' p = Gval F F' := by
  obtain ⟨L, U, hL, hU, hZ⟩ := hc
  have hinv : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1),
      leadMinorK (ZhatOM (ZhatL F F')) l hl = leadMinorK (ptMat p) l hl := by
    intro l hl
    rw [leadMinorK_eq, leadMinorK_eq, hZ]
    exact Formalism.HermitianLatticeCounting.Final.ExpansionTerms.leadingMinorUnipotentInvariant _ _ _ _ _ _ ⟨fun i => (hL i i).2 rfl, fun i j h => (hL i j).1 h⟩
      ⟨fun i => (hU i i).2 rfl, fun i j h => (hU i j).1 h⟩
  unfold Gglob
  rw [← hinv, ← hinv, lead_sign, lead_sign]
  unfold Gval Gflag Dl
  clear hinv hZ hL hU L U
  simp only [Formalism.MainNotions.S.Inh.tie_star]
  have hE : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1), leadMinorE (Zhat F.fl F'.fl) l = leadMinorK (ZhatL F F') l hl := by
    intro l hl
    unfold leadMinorE leadMinorK
    rw [dite_eq_left hl]
  rw [hE _ le_rfl, hE _ (Nat.le_succ _)]

theorem det_isIntegral {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (hM : ∀ i j, IsIntegral ℤ (M i j)) :
    IsIntegral ℤ M.det := by
  have key : M.det ∈ integralClosure ℤ D.host.E := by
    rw [Matrix.det_apply]
    refine Subalgebra.sum_mem _ (fun σ _ => ?_)
    rw [Units.smul_def]
    refine Subalgebra.zsmul_mem _ ?_ _
    exact Subalgebra.prod_mem _ (fun i _ => (mem_integralClosure_iff ..).2 (hM _ _))
  exact (mem_integralClosure_iff ..).1 key

end Minor

theorem rowPt_of {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hG : t.toTerm.G ≠ 0) (hv : (Y.tO u u').vec t ≠ 0) :
    Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T (Formalism.L2.SG.PairVal.ptOf t.toTerm) := by
  have hrel : t.toTerm.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := Formalism.L2.SG.TermOp.Vanish.ooVanish_of Formalism.L2.SG.TermOp.Vanish.avgCore
      Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Pf.chiTrivialC_outright
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t hr
    show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨w, hw⟩ := Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u' t.toTerm hG hrel
  obtain ⟨F2, ⟨hP2, -⟩, hG2, hcell⟩ := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hw, hrel⟩
  have hrow := (Y.rowsOK u).1 t.toTerm.lam t.toTerm.mem
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ t.toTerm.lam :=
    Formalism.L2.SG.NGCut.PtPf.frame_mem _ hrow.2.1.2.2.1.1 hrow.2.2
  have hF2 : ∀ b, frame F2 b ∈ t.toTerm.lam := Formalism.L2.SG.NGCut.PtPf.frame_mem _ hP2.1.1 hP2.2.2.2
  have hZint : ∀ i j, IsIntegral ℤ (ZhatOM (ZhatL (lf D (X.Fu u)) F2) i j) :=
    Formalism.L2.SG.NGCut.PtPf.zhatOM_isIntegral _ _ hrow.2.1.2.1 hF hF2
  have hGg : Gglob D (D.mem u).A.T (D.mem u').A.T (Formalism.L2.SG.PairVal.ptOf t.toTerm) = Gval (lf D (X.Fu u)) F2 :=
    gglob_of_cell (lf D (X.Fu u)) F2 _ hcell
  have hTu := tie_Tu_pos D u
  refine ⟨⟨⟨ZhatOM (ZhatL (lf D (X.Fu u)) F2), hZint, hcell⟩, by rw [hGg]; exact hG2, ?_⟩, fun v => ?_⟩
  ·
    obtain ⟨L, U, hL, hU, hZ⟩ := hcell
    have hlm : ∀ l (hl : l ≤ D.R.rS + 1), IsIntegral ℤ (leadMinorK (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) l hl) := by
      intro l hl
      have e : leadMinorK (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) l hl =
          leadMinorK (ZhatOM (ZhatL (lf D (X.Fu u)) F2)) l hl := by
        rw [leadMinorK_eq, leadMinorK_eq]
        exact Formalism.L2.SG.NGCut.LeadingMinorIntegrality.lead_cell _ _ ⟨L, U, hL, hU, hZ⟩ l
      rw [e]
      exact det_isIntegral _ fun i j => hZint _ _
    have hconj : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (D.host.conj x) := fun x hx => by
      rw [← Formalism.MainNotions.S.Inh.tie_star]
      exact hx.map (starRingEnd D.host.E).toIntAlgHom
    unfold Gglob
    have hn : ∀ n : ℕ, IsIntegral ℤ (n : D.host.E) := fun n => by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (n : ℤ)))
    exact ((hlm _ _).mul (hconj _ (hlm _ _))).sub (((hn _).mul (hn _)).mul ((hlm _ _).mul (hconj _ (hlm _ _))))
  ·
    have hpos := (b_G_pos (p_starConj D) hTu (lf D (X.Fu u)) F2 rfl hP2.1.2 hG2
      (p_posX D _ hTu (lf D (X.Fu u))) (plEmb D v)).1
    have hpos2 : 0 < ((plEmb D v) (Gglob D (D.mem u).A.T (D.mem u').A.T (Formalism.L2.SG.PairVal.ptOf t.toTerm))).re := by
      calc (0 : ℝ) < ((plEmb D v) (Gval (lf D (X.Fu u)) F2)).re := hpos
        _ = _ := by rw [hGg]
    rw [plEmb_Gglob, Complex.ofReal_re] at hpos2
    rw [GPoint_loc]
    have hc : 0 < ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 := by
      have := Finset.prod_pos (s := Finset.univ) (fun (i : Fin D.R.rS) _ => alf_pos D i)
      positivity
    exact mul_pos hc hpos2

theorem ptUnif' : Formalism.L2.SG.Pf.BDat.PtUnif := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' _ t ht hv => rowPt_of Y u u' t ?_ hv⟩
  intro h0
  apply ht.1
  simp [Full.tO, tOf, Gt, GTerm.G, h0]

theorem ptUnifG : Formalism.L2.SG.Pf.BDat.PtUnifG := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u _ t ht hv => rowPt_of Y u u t ?_ hv⟩
  intro h0
  apply ht.1
  simp [Full.tO, tOf, Gt, GTerm.G, h0]

end Formalism.L2.SG.PointUniformity

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowsGoodRed
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.RowDict Formalism.L2.SG.AllRowsOf
open scoped InnerProductSpace
open MeasureTheory

namespace Formalism.L2.SG.Pf.RowsGoodRed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def VT (t : Tup2 D) : Submodule ℂ (L2X X) :=
  Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X ⊓ LinearMap.ker ((ReT X {t} : L2X X →ₗ[ℂ] L2X X) - LinearMap.id)

def labOf (σ : Fin D.what₂.Drows) : Tup2 D := fun k => D.nd.lab k (D.what₂.ft σ)

def bRow (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) (σ : Fin D.what₂.Drows) : L2X X :=
  ((ι (D.sEE (D.what₂.onb σ)) : Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : L2X X)

def LabTie (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : Prop :=
  (∀ σ k v, IsLabel D k (D.nd.lab k (D.what₂.ft σ) v)) ∧ (∀ σ, D.ntypes.goodTuple (labOf σ)) ∧
    ∀ σ, bRow X ι σ ∈ VT X (labOf σ)

def ProjT (G : GoodOp X) : Prop :=
  (∀ t : Tup2 D, D.ntypes.goodTuple t → VT X t ≤ goodSub X G) ∧
    ∀ t t' : Tup2 D, t ≠ t' → ∀ φ ∈ VT X t, ∀ φ' ∈ VT X t', ⟪φ, φ'⟫_ℂ = 0

def DcountEq : Prop :=
  ∀ t ∈ labT (D := D), D.ntypes.goodTuple t → dimX X {t} = Module.finrank ℂ (VT X t)

theorem rowsGood_of (G : GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) (hT : RowDictTie X G ι)
    (hL : LabTie X ι) (hP : ProjT X G) (hD : DcountEq X) : RowsGood X := by
  classical
  obtain ⟨hl1, hl2, hl3⟩ := hL
  refine ⟨hl1, hl2, fun t ht hg => ?_⟩
  have hT' := hT
  obtain ⟨j, hj⟩ := hT
  have hb : ∀ σ, bRow X ι σ = star ((j (D.what₂.onb σ) : EEC X G) : L2X X) := fun σ => by
    have h1 := hj (D.what₂.onb σ)
    simp only at h1
    unfold bRow; rw [h1]; rfl

  have hf : LinearIndependent ℂ (fun σ => ((j (D.what₂.onb σ) : EEC X G) : L2X X)) :=
    (D.what₂.onb.toBasis.linearIndependent.map' j.toLinearEquiv.toLinearMap j.toLinearEquiv.ker).map'
      (EEC X G).subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent ℂ (bRow X ι) := by
    rw [linearIndependent_iff']
    intro s g hs i hi
    have h0 : Formalism.L2.SG.RowDict.conjL (muX X) (∑ i ∈ s, (starRingEnd ℂ (g i)) • ((j (D.what₂.onb i) : EEC X G) : L2X X)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      rw [← hs]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [LinearIsometryEquiv.map_smulₛₗ, Formalism.L2.SG.RowDict.conjL_apply, hb σ]
      simp
    have h1 : (∑ i ∈ s, (starRingEnd ℂ (g i)) • ((j (D.what₂.onb i) : EEC X G) : L2X X)) = 0 :=
      (Formalism.L2.SG.RowDict.conjL (muX X)).map_eq_zero_iff.1 h0
    have := (linearIndependent_iff'.1 hf) s (fun i => starRingEnd ℂ (g i)) h1 i hi
    simpa using this

  have hspan : ∀ φ ∈ goodSub X G, φ ∈ Submodule.span ℂ (Set.range (bRow X ι)) := by
    intro φ hφ
    obtain ⟨F, hF⟩ := (range_sEE X hT' ⟨φ, hφ.1⟩).1 hφ
    have e : φ = ((ι (D.sEE F) : Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : L2X X) := by rw [hF]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, ← D.what₂.onb.sum_repr F, map_sum, map_sum, Submodule.coe_sum]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [map_smulₛₗ, map_smul, Submodule.coe_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)

  let Sf : Finset (Fin D.what₂.Drows) := Finset.univ.filter fun σ => labOf σ = t
  have hEq : VT X t = Submodule.span ℂ (Set.range (fun σ : Sf => bRow X ι σ)) := by
    apply le_antisymm
    · intro φ hφ
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan φ (hP.1 t hg hφ))
      set φ1 := ∑ σ ∈ Sf, c σ • bRow X ι σ with hφ1
      set φ2 := ∑ σ ∈ Finset.univ.filter (fun σ => ¬ labOf σ = t), c σ • bRow X ι σ with hφ2
      have hsplit : φ = φ1 + φ2 := by
        rw [← hc, hφ1, hφ2, Finset.sum_filter_add_sum_filter_not]
      have h1V : φ1 ∈ VT X t := Submodule.sum_mem _ fun σ hσ => Submodule.smul_mem _ _ (by
        have := hl3 σ; rwa [(Finset.mem_filter.1 hσ).2] at this)
      have h2V : φ2 ∈ VT X t := by
        have := Submodule.sub_mem _ hφ h1V
        rwa [hsplit, add_sub_cancel_left] at this
      have horth : ⟪φ2, φ2⟫_ℂ = 0 := by
        conv_lhs => rw [hφ2]
        rw [sum_inner]
        refine Finset.sum_eq_zero fun σ hσ => ?_
        rw [inner_smul_left, hP.2 (labOf σ) t (Finset.mem_filter.1 hσ).2 _ (hl3 σ) _ h2V, mul_zero]
      have h20 : φ2 = 0 := inner_self_eq_zero.1 horth
      rw [hsplit, h20, add_zero, hφ1]
      exact Submodule.sum_mem _ fun σ hσ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨σ, hσ⟩, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨σ, rfl⟩
      have := hl3 σ
      rwa [(Finset.mem_filter.1 σ.2).2] at this
  have hli' : LinearIndependent ℂ (fun σ : Sf => bRow X ι σ) := hli.comp (Subtype.val : Sf → _) Subtype.val_injective
  rw [hD t ht hg, hEq, finrank_span_eq_card hli', Fintype.card_coe]
  rfl

def EtConv : Prop := ∀ (S S' : Set (Tup2 D)) (φ : L2X X), ReT X S (ReT X S' φ) = ReT X (S ∩ S') φ

def EtEmpty : Prop := ∀ φ : L2X X, ReT X ∅ φ = 0

def EtAdj : Prop := ∀ (S : Set (Tup2 D)) (φ ψ : L2X X), ⟪ReT X S φ, ψ⟫_ℂ = ⟪φ, ReT X S ψ⟫_ℂ

def EtGood (G : GoodOp X) : Prop :=
  ∀ t : Tup2 D, D.ntypes.goodTuple t → ∀ φ : L2X X, G.Rg (ReT X {t} φ) = ReT X {t} φ

theorem mem_VT {t : Tup2 D} {φ : L2X X} (h : φ ∈ VT X t) : ReT X {t} φ = φ := by
  have h2 := (Submodule.mem_inf.mp h).2
  rw [LinearMap.mem_ker] at h2
  simpa [sub_eq_zero] using h2

theorem projT_of (G : GoodOp X) (hC : EtConv X) (hE : EtEmpty X) (hA : EtAdj X) (hG : EtGood X G) : ProjT X G := by
  refine ⟨fun t ht φ hφ => ?_, fun t t' htt φ hφ φ' hφ' => ?_⟩
  · refine Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hφ).1, ?_⟩
    have h1 := hG t ht φ
    rw [mem_VT X hφ] at h1
    rw [LinearMap.mem_ker]
    simpa [sub_eq_zero] using h1
  · rw [← mem_VT X hφ, ← mem_VT X hφ', hA, hC]
    have hE0 : ({t} : Set (Tup2 D)) ∩ {t'} = ∅ := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro rfl
      exact htt
    rw [hE0, hE, inner_zero_right]

theorem etEmpty : EtEmpty X := by
  intro φ
  have hES : ∀ g, (ES (D := D) ∅).coeff g = 0 := by
    intro g
    simp [ES]
  have hg : egA X (ES (D := D) ∅) = 0 := by
    funext y
    simp [egA, hES]
  have he : eT X ∅ = 0 := by
    funext x
    simp [eT, Formalism.MainNotions.S.AutInst.convF, hg]
  unfold ReT
  split_ifs with h
  · have hT := (Classical.choose_spec h).2
    have h0 : ∀ x, ⟪x, (Classical.choose h) φ⟫_ℂ = 0 := fun x => by
      rw [hT x φ, he]
      simp
    exact inner_self_eq_zero.mp (h0 _)
  · rfl

theorem invInvariant_muf : X.B.μf.IsInvInvariant := by
  have : X.B.μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have he1 : X.B.e 1 ≠ 0 := by
    rw [X.e_eq]
    have h1 : (1 : X.B.I.Gf) ∈ X.K2 := hK.1
    rw [ite_eq_left (show (1 : X.B.I.Gf) ∈ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw from h1)]
    have hc : X.chi2 1 ≠ 0 := by
      intro h0; have := hK.2.2.2.2 1 h1; rw [h0, norm_zero] at this; exact zero_ne_one this
    have hv : ((X.B.μf X.K2).toReal : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact (ENNReal.toReal_pos hL.2.2.1.ne' hL.2.2.2.ne).ne'
    exact div_ne_zero (star_ne_zero.2 hc) hv
  exact Formalism.MainNotions.BridgeLemma.inv_invariant_of_bi_invariant X.B.μf (fun g => ‖X.B.e g‖) X.B.e_adm.1.continuous.norm
    X.B.Re_spec.1.norm (norm_pos_iff.2 he1)

def EtSA : Prop := ∀ (S : Set (Tup2 D)) (x : X.B.I.Gf), star (eT X S x⁻¹) = eT X S x

theorem etAdj_of (hSA : EtSA X) : EtAdj X := by
  have := invInvariant_muf X
  intro S φ ψ
  have hT := reT_spec X (etInt_holds X) S
  have := X.B.sf
  have := X.B.haar
  obtain ⟨hmul, hone, hiso⟩ := Formalism.L2.SG.Pf.reg_alg
    Formalism.L2.SG.Closed.UnimodGf_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec
  have hreg : ∀ g : X.B.I.Gf, ⟪X.B.R ((1, g) : X.B.I.GA) φ, ψ⟫_ℂ = ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ := by
    intro g
    have h := Formalism.L2.SG.Pf.inner_orbit X.B.R hmul hiso ((1, g) : X.B.I.GA) 1 φ ψ
    simpa only [hone, one_apply_eq_self, mul_one, Prod.inv_mk, inv_one] using h
  calc ⟪ReT X S φ, ψ⟫_ℂ = star ⟪ψ, ReT X S φ⟫_ℂ := (inner_conj_symm _ _).symm
    _ = star (∫ g, eT X S g * ⟪ψ, X.B.R ((1, g) : X.B.I.GA) φ⟫_ℂ ∂X.B.μf) := by rw [hT.2]
    _ = ∫ g, star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by
        rw [← starRingEnd_apply, ← integral_conj]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show (starRingEnd ℂ) (eT X S g * ⟪ψ, X.B.R ((1, g) : X.B.I.GA) φ⟫_ℂ) = _
        rw [map_mul]
        show _ = star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ
        rw [← hreg g, inner_conj_symm]
        rfl
    _ = ∫ g, star (eT X S g⁻¹) * ⟪φ, X.B.R ((1, g) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by
        rw [← MeasureTheory.integral_inv_eq_self (fun g => star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ) X.B.μf]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show star (eT X S g⁻¹) * ⟪φ, X.B.R ((1, g⁻¹⁻¹) : X.B.I.GA) ψ⟫_ℂ = _
        rw [inv_inv]
    _ = ∫ g, eT X S g * ⟪φ, X.B.R ((1, g) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show star (eT X S g⁻¹) * _ = _
        rw [hSA S g]
    _ = ⟪φ, ReT X S ψ⟫_ℂ := (hT.2 φ ψ).symm

theorem etGood_of (G : GoodOp X)
    (hEC : ∀ S S' : Set (Tup2 D), X.B.I.convF X.B.μf (egA X (ES S')) (eT X S) = eT X (S' ∩ S)) : EtGood X G := by
  intro t ht φ
  have h1 := Formalism.L2.SG.Pf.AllRowsRMul.isRConvF_conv X G.Rg_spec (reT_spec X (etInt_holds X) {t})
  have e : X.B.I.convF X.B.μf (eg X) (eT X {t}) = eT X {t} := by
    rw [← goodIdempotent_eq, ← ES_good, hEC]
    congr 1
    exact Set.inter_eq_right.2 (Set.singleton_subset_iff.2 ht)
  rw [e] at h1
  have h2 := isRConvF_unique X h1 (reT_spec X (etInt_holds X) {t})
  exact congrArg (fun T : L2X X →L[ℂ] L2X X => T φ) h2

end Formalism.L2.SG.Pf.RowsGoodRed
end
end
