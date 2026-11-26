module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadAATopOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGSlice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeStandardCompact
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormSmulL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutIntervalLong
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdj

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev GenW (k r : ℕ) := Polynomial ℂ × List (ℂ × B.Mat k r)

def fexp {k r : ℕ} : List (GenW k r) → List (Polynomial ℂ × List (B.Mat k r))
  | [] => [(1, [])]
  | gn :: gs => (fexp gs).map (fun t => (gn.1 * t.1, t.2)) ++
      gn.2.flatMap (fun dX => (fexp gs).map (fun t => (Polynomial.C dX.1 * t.1, dX.2 :: t.2)))

section ops

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def genOpR (gn : GenW k r) (u : ℂ) (F : B.Mat k r → E) : B.Mat k r → E :=
  fun h => gn.1.eval u • F h + (gn.2.map fun dX => dX.1 • Formalism.REAL.RdV dX.2 F h).sum

def genOpL (gn : GenW k r) (u : ℂ) (F : B.Mat k r → E) : B.Mat k r → E :=
  fun h => gn.1.eval u • F h + (gn.2.map fun dX => dX.1 • Q.LdV dX.2 F h).sum

def wsEvalR (ws : List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ) (f : B.Mat k r → E) (g : B.Mat k r) : E :=
  (ws.map fun t => t.1.eval u • B.Rw t.2 f g).sum

def wsEvalL (ws : List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ) (f : B.Mat k r → E) (g : B.Mat k r) : E :=
  (ws.map fun t => t.1.eval u • t.2.foldr Q.LdV f g).sum

end ops

def capGen {k r t : ℕ} (Zg : Fin t → Fin t → B.Mat k r) (σ : Equiv.Perm (Fin t)) (i : Fin t) : GenW k r :=
  (if σ i = i then Polynomial.X - Polynomial.C ((i : ℕ) : ℂ) else 0,
    [(1, hpart1 (Hpk k r) (Zg (σ i) i)), (Complex.I, hpart2 (Hpk k r) (Zg (σ i) i))])

def capGens {k r t : ℕ} (Zg : Fin t → Fin t → B.Mat k r) (σ : Equiv.Perm (Fin t)) : List (GenW k r) :=
  List.ofFn (capGen Zg σ)

def zgCV (k r : ℕ) : Fin (Q.mdim k r 0) → Fin (Q.mdim k r 0) → B.Mat k r :=
  fun a b => Matrix.single (Q.posL k r 0 a) (Q.posL k r 0 b) (1 : ℂ)

def zgB {k r : ℕ} (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) : Fin k → Fin k → B.Mat k r :=
  fun a b => Q.unitB (Hpk k r) Bs a b

def RdVRep : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (X : B.Mat k r) (U : Set (B.Mat k r))
    (F f : B.Mat k r → E), B.inLie k r X → IsOpen U → ContDiffOn ℝ 1 F U →
    (∀ g ∈ U, g ∈ B.GV k r → f g = F g) → ∀ h ∈ U, h ∈ B.GV k r →
      Formalism.REAL.RdV X f h = fderiv ℝ F h (h * X) ∧ Q.LdV X f h = fderiv ℝ F h (X * h)

def FExpEvalR : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (gens : List (GenW k r)) (u : ℂ)
    (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
    (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) → B.CkOn (gens.length : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
      (gens.map (fun gn => genOpR gn u)).foldr (fun T h => T h) f g = wsEvalR (fexp gens) u f g

def FExpEvalL : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (gens : List (GenW k r)) (u : ℂ)
    (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
    (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) → B.CkOn (gens.length : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
      (gens.map (fun gn => genOpL gn u)).foldr (fun T h => T h) f g = wsEvalL (fexp gens) u f g

def CVAsGens : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) (f : B.Mat k r → E) (g : B.Mat k r),
    Q.CV k r Y f g = ∑ σ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((capGens (zgCV k r) σ).map (fun gn => genOpR gn (Q.uC k r 0 Y))).foldr (fun T h => T h) f g

def CapRAsGens : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ)
    (f : B.Mat k r → E) (g : B.Mat k r),
    Q.capR k r Bs w f g = ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((capGens (zgB Bs) σ).map (fun gn => genOpR gn w)).foldr (fun T h => T h) f g

def CapLAsGens : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ)
    (f : B.Mat k r → E) (g : B.Mat k r),
    Q.capLft k r Bs w f g = ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((capGens (zgB Bs) σ).reverse.map (fun gn => genOpL gn w)).foldr (fun T h => T h) f g

def FExpDeg : Prop :=
  ∀ (k r : ℕ) (gens : List (GenW k r)), (∀ gn ∈ gens, gn.1.natDegree ≤ 1) →
    ∀ t ∈ fexp gens, t.1.natDegree + t.2.length ≤ gens.length ∧ ∀ X ∈ t.2, ∃ gn ∈ gens, ∃ d : ℂ, (d, X) ∈ gn.2

def FExpSymb : Prop :=
  ∀ (k r : ℕ) (gens : List (GenW k r)) (τ : B.Mat k r → ℂ) (u s : ℂ),
    ((fexp gens).map fun t => t.1.eval u * s ^ t.2.length * (t.2.map τ).prod).sum =
      (gens.map fun gn => gn.1.eval u + s * (gn.2.map fun dX => dX.1 * τ dX.2).sum).prod

def DetShiftCoeff : Prop :=
  ∀ (t : ℕ) (M : Matrix (Fin t) (Fin t) ℂ) (j : ℕ), j ≤ t →
    AddMonoidAlgebra.coeff (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
        ∏ i : Fin t, ((if σ i = i then MvPolynomial.X 0 - MvPolynomial.C ((i : ℕ) : ℂ) else 0) +
          MvPolynomial.X 1 * MvPolynomial.C (M (σ i) i)))
      (Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j) =
      (-1) ^ j * M.charpoly.coeff (t - j)

def CoeffInterp : Prop :=
  ∀ (N m : ℕ), m ≤ N → ∃ (Ys : Fin (N + 1) → ℝ) (lam : Fin (N + 1) → ℂ),
    ∀ q : Polynomial ℂ, q.natDegree ≤ N → ∑ i, lam i * q.eval (Ys i : ℂ) = q.coeff m

def CapWordsOfParts : Prop :=
  RdVRep → FExpEvalR → CVAsGens → FExpDeg → FExpSymb → DetShiftCoeff → CoeffInterp → CapWords

def CapRWordsOfParts : Prop :=
  RdVRep → FExpEvalR → CapRAsGens → FExpDeg → FExpSymb → DetShiftCoeff → CoeffInterp → CapRWords

def CapLWordsOfParts : Prop :=
  RdVRep → FExpEvalL → CapLAsGens → FExpDeg → FExpSymb → DetShiftCoeff → CoeffInterp → CapLWords

theorem capWords_all_of (hJ : CapWordsOfParts) (hJR : CapRWordsOfParts) (hJL : CapLWordsOfParts) (h1 : RdVRep)
    (hR : FExpEvalR) (hL : FExpEvalL) (hCV : CVAsGens) (hCR : CapRAsGens) (hCL : CapLAsGens) (hD : FExpDeg)
    (hS : FExpSymb) (hDet : DetShiftCoeff) (hI : CoeffInterp) : CapWords ∧ CapRWords ∧ CapLWords :=
  ⟨hJ h1 hR hCV hD hS hDet hI, hJR h1 hR hCR hD hS hDet hI, hJL h1 hL hCL hD hS hDet hI⟩

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWaveMain
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem letter_level_zero_eq {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (hj : 0 ≤ r) (l : C.Letter) (e : Fin 2) (G : B.Mat k r → E) :
    D.vLet k r z z' 0 hj l e G = if e = 0 then G else fun _ => 0 := by
  funext g
  by_cases he : e = 0
  · subst he
    have hD0 : Dmin k r z z' g 0 = 1 := by simp [Dmin]
    rcases l with ⟨b, Y⟩
    cases b <;>
      simp [D.vLet, C3.AAop, C3.AAvop, qminorOp, Matrix.det_isEmpty, Finset.univ_unique] <;>
      rw [if_pos (show StrictMono _ from fun a => a.elim0)] <;> simp [hD0]
  · have he1 : e = 1 := by omega
    subst he1
    simp [D.vLet]

theorem slicePolyAll : SlicePolyAll := by
  intro Wp Wq _ _ _ _ _ _ P p F hF j hj h hh w' b δ e
  by_cases hj0 : j = 0
  · subst hj0
    refine ⟨fun _ => if e = 0 then KB.slv p.T F 0 hj w' h hh.2 else 0, rfl, fun l => ?_, fun t => ?_⟩
    · by_cases he : e = 0
      · simp only [he, if_true]
        exact nice_vec_of_cpt (p.T.bs 0) (fun a => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F 0 hj w' h hh hF a)
      · simp only [he, if_false]
        exact ⟨0, fun a => Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero⟩
    · intro a g hg
      show D.castF _ (D.sliceAt P.k P.r p.T.base.z p.T.base.z'
        (D.vLet P.k P.r p.T.base.z p.T.base.z' 0 hj (b, t + δ) e
          (D.uwG P.k P.r p.T.base.z p.T.base.z' F 0 hj w' a)) h) g = _
      rw [letter_level_zero_eq]
      by_cases he : e = 0
      · simp [he, Finset.sum_apply, Fin.sum_univ_succ, KB.slv]
      · simp [he, sliceAt_zero, Finset.sum_apply, D.castF]
  · refine slicePoly_of_pt p.T F hF j hj (by omega) h hh w' b δ e (fun a g hg hD => ?_)
    obtain ⟨c, hcl, hc⟩ := uwG_letter_poly p.T.base.z p.T.base.z' j hj hF.1 w' a g hg hD b e
    obtain ⟨c', hc'l, hsh⟩ := poly_shift j c (δ : ℂ)
    refine ⟨c', hc'l.trans hcl, fun t => ?_⟩
    show D.vLet P.k P.r p.T.base.z p.T.base.z' j hj (b, t + δ) e (D.uwG P.k P.r p.T.base.z p.T.base.z' F j hj w' a) g = _
    rw [hc (t + δ), ← hsh (t : ℂ)]
    push_cast
    rfl

theorem _root_.Formalism.FourierDecayAlt.P.degree_of_plane_wave : KB.DegWave := degWave_of slicePolyAll

end Formalism.FourierDecayAlt.P.PBG
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialRaisingTopOfParts
open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem pOp_locO (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → E} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : pOp l f₁ c = pOp l f₂ c := by
  have hev : f₁ =ᶠ[nhds c] f₂ := by
    filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc' using h c' hc'
  simp only [pOp, wirt, ite_eq_left hc, hev.fderiv_eq]

theorem vAB_loc (Y : ℂ) : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, f₁ c = f₂ c) →
    ∀ c ∈ OmX r, (Q.vAB r Y i).1 f₁ c = (Q.vAB r Y i).1 f₂ c ∧ (Q.vAB r Y i).2 f₁ c = (Q.vAB r Y i).2 f₂ c := by
  intro i f₁ f₂ h
  induction i with
  | zero =>
    intro c hc
    exact ⟨h c hc, rfl⟩
  | succ i ih =>
    intro c hc
    by_cases hi : i < r
    · simp only [Q.vAB, dite_eq_left hi]
      refine ⟨?_, ?_⟩
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, cOp]
        rw [(ih c hc).1, (ih c hc).2, pOp_locO _ (fun c' hc' => (ih c' hc').1) hc]
      · simp only [ciOp]
        rw [(ih c hc).1]
    · simp only [Q.vAB, dite_eq_right hi]
      exact ih c hc

end loc

section jd

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem jf_dinv (Bs : B.RealPlaceData k r Wp Wq) (H : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.JF Bs (fun x => (Dmin k r Bs.z Bs.z' x (Fin.last _))⁻¹ • H x) g =
      (Dmin k r Bs.z Bs.z' g (Fin.last _))⁻¹ • B.JF Bs H g := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (fun x => (Dmin k r Bs.z Bs.z' x (Fin.last _))⁻¹ • H x) g ∂Bs.μSS =
    (Dmin k r Bs.z Bs.z' g (Fin.last _))⁻¹ • ∫ p, JF.xiP Bs p • B.rho Bs p H g ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  simp only [B.rho]
  rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

end jd

end Formalism.FourierDecayAlt.P.PBN

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBN

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_raising_top_of_parts : PBN.RadAATopOfParts := by
  intro hJ hC hM hR hCp Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 y hD F hF
  refine ⟨hCp P.k P.r Wp Wq Bs F y hF, fun Φ hΦ x hx => ?_⟩
  have hL : Q.IsActualLevel X L := hD.2.2.1
  have hc0 : (∏ a, x.1 a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a
  have hcell := Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs x hx
  have hγ := Formalism.FourierDecayAlt.P.TLB.wCell_om Bs hx

  have e1 : (TL.aP L (y : ℂ)).1 Φ = (L.ζi).1 ((L.Ar (y : ℂ)).1 Φ) := rfl
  rw [e1, hL.2.2.2.2.2.2.2.1]
  show ((X.fn 1 ((L.Ar (y : ℂ)).1 Φ) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.fn_apply 1 _ x hx, hR P.k P.r Bs.z Bs.z' Wp Wq Bs.π Bs.π' X L (y : ℂ) hL Φ x hx]
  have eΦ : Q.crd (Q.vAB P.r (y : ℂ) P.r).1 (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      Q.crd (Q.vAB P.r (y : ℂ) P.r).1 (Q.resG P.k P.r (Fin.last P.r) (B.JF Bs F)) x.1 x.2 :=
    (vAB_loc (y : ℂ) P.r _ _ (fun c' hc' => hΦ (c', x.2) ⟨hc', hx.2⟩) x.1 hx.1).1
  rw [eΦ, ← hM P.k P.r Wp Wq Bs F (y : ℂ) hF x hx]

  simp only [Q.resG]
  have eJ : B.JF Bs (aaTop Bs y F) (Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2) =
      (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)⁻¹ •
        qminorOp (EabH (Hpk P.k P.r)) (C3.xR P.k P.r P.r le_rfl) (C3.xR P.k P.r P.r le_rfl)
          ((y : ℂ) + ((2 * P.r + P.k : ℕ) : ℂ) / 2) (B.JF Bs F) (Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2) := by
    unfold aaTop
    rw [jf_dinv, hJ P.k P.r Wp Wq Bs F _ hF _ hγ, hC P.k P.r _ _ _ _ _ hx.2.1, hcell.2.2.1, smul_smul]
    congr 1
    rw [mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  rw [eJ, smul_comm]
  rfl

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormPosCompactSupport
namespace Formalism.FourierDecayAlt.P.ModuleFormPositivity

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexOrder

def FormPosCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w → ∀ x,
    (∀ e, KB.CptCoef (p.T.bs j) (x e)) → 0 ≤ p.form j hj w x x

end Formalism.FourierDecayAlt.P.ModuleFormPositivity

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexOrder

theorem module_form_pos_compact_support : ModuleFormPositivity.FormPosCpt := by
  intro hP Wp Wq _ _ _ _ _ _ P p j hj w hc x hx
  obtain ⟨ε, hε, R, hxN, hxR, -, -⟩ := Formalism.FourierDecayAlt.P.PBF.common_eps_R (p.T.bs j) x x hx hx
  obtain ⟨hl1, hlk, -⟩ := p.hl
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j)) with hμ
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X μ L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨K, hThm, -, -, hJc⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  obtain ⟨Cst, hC, hform⟩ := Formalism.FourierDecayAlt.P.radial_module_form Wp Wq P p.T jF X μ L st p.l0 hD
  choose Φ hΦK hΦ using fun a =>
    Formalism.FourierDecayAlt.P.PBF.pic_of_cptClause (p.T.bs jF) (K 0) hJc hε (hxN a) (hxR a)
  have hW := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hc.1 hc.2
  have hpos := ((hThm (D.positionted w) hW).2.2 0 (fun _ => 1) (fun _ => one_ne_zero)).2 Φ (fun a _ => hΦK a)
  have hpos' : 0 ≤ P5.form μ 0 (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ 0 :=
    hpos.trans_eq (Formalism.FourierDecayAlt.P.JCx2.form_zero_indep μ _ _ _ _)
  have e := hform w x x Φ Φ ε hε hxN hxN hΦ hΦ
  show 0 ≤ D.formLev p.T (M.sgn P p.l0) jF w x x
  rw [e]
  exact mul_nonneg (by exact_mod_cast hC.le) hpos'

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeAtMinusW
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem onOld_id {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {w : List C.Letter} :
    ∀ (ys : List ℝ) (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)),
      KB.onOld (⇑(LinearMap.id : (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) →ₗ[ℂ] _)) ys x = x
  | [], x => rfl
  | y :: ys, x => by
    funext e
    simp only [KB.onOld]
    rw [onOld_id ys]
    exact congrArg x (Fin.cons_self_tail e)

theorem mix_push {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (i : ℕ) {K d : ℕ}
    (grid : Fin K → Fin (d + 1) → ℝ) (mk : List ℝ → List C.Letter) (p q : C.LPt) :
    KB.mix S v ε i (PBD.pushU grid mk) (PBD.pushTh grid mk) p q =
      ∑ n : Fin K → Fin (d + 1), (F7.thGrid grid n : ℂ) *
        KB.gN S v ε i (mk (List.ofFn fun b => grid b (n b))) p q := by
  unfold KB.mix PBD.pushTh
  simp only [Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hmem : mk (List.ofFn fun b => grid b (n b)) ∈ PBD.pushU grid mk :=
    Finset.mem_image_of_mem _ (Finset.mem_univ n)
  rw [Finset.sum_eq_single_of_mem _ hmem]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
    simp

section sizes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem sizeAt_plusW (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ys : List ℝ) (a : List C.Letter) :
    S.sizeAt v (KB.plusW ys a) = (ys.map fun y => |S.P v y|).prod * S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  rw [PBD.plusW_eq, List.map_append, List.prod_append, List.map_map]
  rfl

theorem sizeAt_minusW (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ys : List ℝ) (a : List C.Letter) :
    S.sizeAt v (KB.minusW ys a) = (ys.map fun y => |S.P v (y + 1)|).prod * S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  rw [PBD.minusW_eq, List.map_append, List.prod_append, List.map_map]
  rfl

theorem sizeAt_pos (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (v : Fin S.f) (a : List C.Letter)
    (ha : D.AdmAt S v a) : 0 < S.sizeAt v a := by
  obtain ⟨w, hw⟩ := ha
  have hA := (PBD.admissible_list_of_word S w v).1
  rw [hw] at hA
  unfold C.HidaSetting.sizeAt
  refine List.prod_pos fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
  have hnode := hA j hj
  have hgrid : (∃ a', PBD.nodeOf a[j] ∈ S.grid v a') ∨ PBD.nodeOf a[j] ∈ S.grid1 v := by
    rcases Finset.mem_union.1 hnode with h | h
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr h
  obtain ⟨-, -, hP, hP1⟩ := (hG v).2.2.2.2.2 _ hgrid
  refine abs_pos.2 ?_
  unfold PBD.nodeOf at hP hP1
  split_ifs at hP hP1 with hs
  · exact hP
  · simpa using hP1

end sizes

section nodes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

def NodeOK (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (one : Bool) (y : ℝ) : Prop :=
  (one = false ∧ ∃ a', a.length < a' ∧ a' ≤ S.Ntop ∧ y ∈ S.grid v a') ∨
    (one = true ∧ y ∈ S.grid1 v ∧ ∀ x ∈ a, PBD.Sep (true, y) x)

theorem nodes_level (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (a : List C.Letter) (ha : D.AdmAt S v a)
    (K : ℕ) (hK : a.length + K ≤ S.Ntop) (j : ℕ) (hj : j ≤ S.G.r) :
    ∃ grid : Fin K → Fin (2 * j + 1) → ℝ,
      (∀ b, Function.Injective (grid b)) ∧
      (∀ b, ∑ i, |F7.lagCo (grid b) i| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ (2 * j)) ∧
      (∀ n : Fin K → Fin (2 * j + 1),
        D.AdmAt S v (KB.plusW (List.ofFn fun b => grid b (n b)) a) ∧
        D.AdmAt S v (KB.minusW (List.ofFn fun b => grid b (n b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (n b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun b => grid b (n b)) a) ∧
        (List.ofFn fun b => grid b (n b)).Pairwise (fun y y' => 2 < |y - y'|) ∧
        ∀ y ∈ (List.ofFn fun b => grid b (n b)), NodeOK S v a (decide (j = 0)) y) ∧
      KB.LocProb S v (a.length + K) (PBD.pushU grid fun ys => KB.plusW ys a)
        (PBD.pushTh grid fun ys => KB.plusW ys a) ∧
      KB.LocProb S v (a.length + K) (PBD.pushU grid fun ys => KB.minusW ys a)
        (PBD.pushTh grid fun ys => KB.minusW ys a) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, hGr, -⟩ := hB'
  have hCI := PBCut.cutInside_of_built hB
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  ·
    obtain ⟨ys, hlen, -, hg1, hp, hm, hcp, hcm, hpw⟩ :=
      Formalism.FourierDecayAlt.P.new_letters_admissible_level_one E Wp Wq S hGo hGr hCI v a K ha hK
    set grid : Fin K → Fin (2 * 0 + 1) → ℝ := fun b _ => ys.get ⟨b, by rw [hlen]; exact b.2⟩ with hgrid
    have hys : ∀ n : Fin K → Fin (2 * 0 + 1), (List.ofFn fun b => grid b (n b)) = ys := by
      intro n
      apply List.ext_get
      · simp [hlen]
      · intro i h1 h2
        simp [hgrid]
    have hsep : ∀ y ∈ ys, ∀ x ∈ a, PBD.Sep (true, y) x := by
      obtain ⟨w, hw⟩ := hp
      have hA := (PBD.admissible_list_of_word S w v).2
      rw [hw, PBD.plusW_eq] at hA
      intro y hy x hx
      exact (List.pairwise_append.1 hA).2.2 _ (List.mem_map.2 ⟨y, hy, rfl⟩) _ hx
    have hmk : ∀ mk : List ℝ → List C.Letter, (mk ys = KB.plusW ys a ∨ mk ys = KB.minusW ys a) →
        ∀ n : Fin K → Fin (2 * 0 + 1), D.AdmAt S v (mk (List.ofFn fun b => grid b (n b))) ∧
          (mk (List.ofFn fun b => grid b (n b))).length ≤ a.length + K := by
      intro mk hmk n
      rw [hys n]
      rcases hmk with h | h <;> rw [h]
      · exact ⟨hp, by rw [PBD.plusW_eq]; simp [hlen]; omega⟩
      · exact ⟨hm, by rw [PBD.minusW_eq]; simp [hlen]; omega⟩
    refine ⟨grid, fun b => fun i i' _ => Fin.ext (by have := i.isLt; have := i'.isLt; omega), fun b => ?_, fun n => ?_, ?_, ?_⟩
    · simp [F7.lagCo]
    · rw [hys n]
      refine ⟨hp, hm, hcp, hcm, hpw.imp fun h => by linarith, fun y hy => Or.inr ⟨rfl, hg1 y hy, hsep y hy⟩⟩
    · exact PBD.locProb_push S v _ grid (fun b => fun i i' _ => Fin.ext (by have := i.isLt; have := i'.isLt; omega)) _
        (hmk (fun ys => KB.plusW ys a) (Or.inl rfl))
    · exact PBD.locProb_push S v _ grid (fun b => fun i i' _ => Fin.ext (by have := i.isLt; have := i'.isLt; omega)) _
        (hmk (fun ys => KB.minusW ys a) (Or.inr rfl))
  ·
    obtain ⟨-, grid, hinj, hl1, hmem, hall, hlp, hlm⟩ :=
      Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a K (2 * j) ha hK (by omega)
    refine ⟨grid, hinj, hl1, fun n => ?_, hlp, hlm⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hall n
    refine ⟨h1, h2, h3, h4, h5.imp fun h => by linarith, fun y hy => Or.inl ⟨by simp; omega, ?_⟩⟩
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hy
    exact ⟨a.length + K - b, by omega, by omega, hmem b (n b)⟩

end nodes

end

end Formalism.FourierDecayAlt.P.PBL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CccoefMono
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cccoef_mono {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {Bs : B.RealPlaceData k r Wp Wq} {A : ℝ} {mm : ℕ} {ε ε' : ℝ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (h : JC.CCCoefM Bs A mm ε' F) (he : ε ≤ ε') : JC.CCCoefM Bs A mm ε F :=
  ⟨h.1, h.2.1, fun g hg hne => he.trans (h.2.2 g hg hne)⟩

theorem cut_eq {k r : ℕ} (cut : ℕ → B.Mat k r → ℂ)
    (hcut : ∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) (n : ℕ) (g : B.Mat k r) :
    cut n g = 1 - JCx2.pdPsi ((n : ℝ) + 1) g := by
  rw [hcut]
  simp [JCx2.pdPsi, JCx2.pdPhi, JCx2.pdChi, JCx2.pdSq]

theorem belowTop : ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ Cc : ℝ, Cl ≤ Cc →
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ) (cut : ℕ → B.Mat P.k P.r → ℂ),
    C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    ∀ i, i ≤ P.r → ∀ w : List C.Letter, w.length ≤ N → ∀ a b,
      Tendsto (fun n => p.RR (fun g => cut n g • D.cutF p.T.base χ f ε g) i w a b) atTop
        (𝓝 (p.RR (D.cutF p.T.base χ f ε) i w a b)) := by
  obtain ⟨Cs, hCs0, hSQ⟩ := sliceQ
  refine ⟨Cs + 1, by positivity, ?_⟩
  intro Cc hCc Wp Wq _ _ _ _ _ _ P p f χ ε A N cut hχ hε hf hfA hA hcut i hi w hw a b
  have hk2 : 2 ≤ P.k := p.hl.2.2
  set X : ℝ := (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 with hX
  have hX1 : 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ 2 * (P.r : ℝ) + P.k + 1 := by
      have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
      linarith
    have : 1 ≤ (2 * (P.r : ℝ) + P.k + 1) ^ 3 := one_le_pow₀ h1
    have : 0 ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 := by positivity
    linarith
  have hR4 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 := one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)
  have hA' : Cs * ((P.r : ℝ) + 1) ^ 4 * X ≤ A - 1 := by
    have h1 : (Cs + 1) * ((P.r : ℝ) + 1) ^ 4 * X ≤ A :=
      le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCc (by positivity)) (by positivity)) hA
    have h2 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 * X := by nlinarith
    nlinarith
  set M := 3 * (11 * (N * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5) with hM
  obtain ⟨bf, hbf⟩ := hfA M
  have hbf0 : 0 ≤ bf := JCx2.pd_ccle_nonneg hbf
  have hbf' : B.CCle (A - 1) M f bf := BetaSesquilinearity.CCle_mono_A (by linarith) hbf
  obtain ⟨Kp, hKp0, hKp⟩ := JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) M
  have hψ : ∀ n : ℕ, B.CCle (A - 1) M (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) (Kp * bf / ((n : ℝ) + 1)) :=
    fun n => hKp _ (by positivity) A f bf hbf
  have hψs : ∀ n : ℕ, B.CkOn ⊤ (B.GV P.k P.r) (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) :=
    fun n => JCx2.pd_smooth_smul (JCx2.pd_psi_cd _) hf
  set hn : ℕ → B.Mat P.k P.r → (Wq →L[ℂ] Wp) := fun n g => cut n g • f g with hhn
  have hneq : ∀ n, hn n = fun g => f g + (-1 : ℂ) • (JCx2.pdPsi ((n : ℝ) + 1) g • f g) := by
    intro n; funext g
    simp only [hhn, cut_eq cut hcut n g, sub_smul, one_smul]
    simp [sub_eq_add_neg]
  have hnC : ∀ n, B.CCle (A - 1) M (hn n) (bf + Kp * bf) := by
    intro n
    rw [hneq n]
    refine JCx2.pd_ccle_mono_c (BetaSesquilinearity.CCle_add hbf' (BetaSesquilinearity.CCle_smul (-1) (hψ n))) ?_
    have h1 : Kp * bf / ((n : ℝ) + 1) ≤ Kp * bf := div_le_self (by positivity) (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simp only [norm_neg, norm_one, one_mul]
    linarith
  have hns : ∀ n, B.CkOn ⊤ (B.GV P.k P.r) (hn n) := by
    intro n
    rw [hneq n]
    exact BetaSesquilinearity.CkOn_add hf (BetaSesquilinearity.CkOn_smul (-1) (hψs n))
  have hsub : ∀ n, (fun g => f g - hn n g) = fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g := by
    intro n; funext g
    rw [hneq n]; simp
  have hFn : ∀ n, (fun g => cut n g • D.cutF p.T.base χ f ε g) = D.cutF p.T.base χ (hn n) ε := by
    intro n; funext g
    simp only [D.cutF, hhn]
    rw [smul_comm]
  simp only [KB.Pl.RR, hFn]
  unfold D.RRplace
  by_cases hab : D.IsLocPt a i ∧ D.IsLocPt b i
  swap
  · simp only [dif_neg hab]; exact tendsto_const_nhds
  simp only [dif_pos hab, dif_pos hi]
  have hca : P.r - i = P.r - D.ptSize a := by simp [hab.1.2]
  have hcb : P.r - i = P.r - D.ptSize b := by simp [hab.2.2]
  have hQa := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N P rfl rfl hk2 hχ hA' ε hε i hi w hw a hca hab.1 e
  have hQb := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N P rfl rfl hk2 hχ hA' ε hε i hi w hw b hcb hab.2 e
  choose εa Ka hεa hKa hQ1a hQ2a using hQa
  choose εb Kb hεb hKb hQ1b hQ2b using hQb
  set S : ℝ := ∑ e, (εa e)⁻¹ + ∑ e, (εb e)⁻¹ with hS
  have hSa : ∀ e, (εa e)⁻¹ ≤ S := by
    intro e
    have h1 : (εa e)⁻¹ ≤ ∑ e, (εa e)⁻¹ :=
      Finset.single_le_sum (f := fun e => (εa e)⁻¹) (fun e _ => (inv_pos.2 (hεa e)).le) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, (εb e)⁻¹ := Finset.sum_nonneg fun e _ => (inv_pos.2 (hεb e)).le
    linarith
  have hSb : ∀ e, (εb e)⁻¹ ≤ S := by
    intro e
    have h1 : (εb e)⁻¹ ≤ ∑ e, (εb e)⁻¹ :=
      Finset.single_le_sum (f := fun e => (εb e)⁻¹) (fun e _ => (inv_pos.2 (hεb e)).le) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, (εa e)⁻¹ := Finset.sum_nonneg fun e _ => (inv_pos.2 (hεa e)).le
    linarith
  have hS0 : 0 < S := lt_of_lt_of_le (inv_pos.2 (hεa Wd.e1)) (hSa Wd.e1)
  have hε₀a : ∀ e, S⁻¹ ≤ εa e := fun e => by
    have := inv_anti₀ (inv_pos.2 (hεa e)) (hSa e); rwa [inv_inv] at this
  have hε₀b : ∀ e, S⁻¹ ≤ εb e := fun e => by
    have := inv_anti₀ (inv_pos.2 (hεb e)) (hSb e); rwa [inv_inv] at this
  set KK : ℝ := ∑ e, Ka e + ∑ e, Kb e with hKK
  have hKa' : ∀ e, Ka e ≤ KK := by
    intro e
    have h1 : Ka e ≤ ∑ e, Ka e := Finset.single_le_sum (f := Ka) (fun e _ => hKa e) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, Kb e := Finset.sum_nonneg fun e _ => hKb e
    linarith
  have hKb' : ∀ e, Kb e ≤ KK := by
    intro e
    have h1 : Kb e ≤ ∑ e, Kb e := Finset.single_le_sum (f := Kb) (fun e _ => hKb e) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, Ka e := Finset.sum_nonneg fun e _ => hKa e
    linarith
  have hKK0 : 0 ≤ KK := le_trans (hKa Wd.e1) (hKa' Wd.e1)
  have hB1 : bf ≤ bf + Kp * bf := by nlinarith

  have main : ∀ (q : C.LPt) (hcq : P.r - i = P.r - D.ptSize q) (εq Kq : Wd.Ix (Fin w.length) → ℝ),
      (∀ e, S⁻¹ ≤ εq e) → (∀ e, 0 ≤ Kq e) → (∀ e, Kq e ≤ KK) →
      (∀ e (h : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV P.k P.r) h → B.CCle (A - 1) M h c →
        JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) (εq e) (xs p.T χ ε i hi w q hcq h e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq h e) (Kq e * c)) →
      (∀ e (h₁ h₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c₁ c₂ : ℝ), B.CkOn ⊤ (B.GV P.k P.r) h₁ →
        B.CkOn ⊤ (B.GV P.k P.r) h₂ → B.CCle (A - 1) M h₁ c₁ → B.CCle (A - 1) M h₂ c₂ →
        ∀ γ ∈ B.GV P.k (P.r - i), xs p.T χ ε i hi w q hcq h₁ e γ - xs p.T χ ε i hi w q hcq h₂ e γ =
          xs p.T χ ε i hi w q hcq (fun g => h₁ g - h₂ g) e γ) →
      (∀ e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹ (xs p.T χ ε i hi w q hcq f e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq f e) (KK * (bf + Kp * bf))) ∧
      (∀ n e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹ (xs p.T χ ε i hi w q hcq (hn n) e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq (hn n) e) (KK * (bf + Kp * bf))) ∧
      (∀ n e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N)
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) (KK * (Kp * bf / ((n : ℝ) + 1)))) := by
    intro q hcq εq Kq hεq hKq hKq' hQ1 hQ2
    refine ⟨fun e => ?_, fun n e => ?_, fun n e => ?_⟩
    · obtain ⟨h1, h2⟩ := hQ1 e f bf hf hbf'
      exact ⟨cccoef_mono h1 (hεq e), JCx2.pd_ccle_mono_c h2 (mul_le_mul (hKq' e) hB1 hbf0 hKK0)⟩
    · obtain ⟨h1, h2⟩ := hQ1 e (hn n) _ (hns n) (hnC n)
      exact ⟨cccoef_mono h1 (hεq e), JCx2.pd_ccle_mono_c h2 (mul_le_mul_of_nonneg_right (hKq' e) (by positivity))⟩
    · obtain ⟨h1, h2⟩ := hQ1 e _ _ (hψs n) (hψ n)
      have hd : ∀ γ ∈ B.GV P.k (P.r - i), (fun γ => (-1 : ℂ) • xs p.T χ ε i hi w q hcq
          (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) e γ) γ =
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) γ := by
        intro γ hγ
        have := hQ2 e f (hn n) bf _ hf (hns n) hbf' (hnC n) γ hγ
        rw [hsub n] at this
        simp only [Pi.sub_apply, ← this]
        simp
      have hC2 := Formalism.FourierDecayAlt.P.Ux1.cc_congr hd (BetaSesquilinearity.CCle_smul (-1) h2)
      simp only [norm_neg, norm_one, one_mul] at hC2
      have hC3 := JCx2.pd_ccle_mono_c hC2 (mul_le_mul_of_nonneg_right (hKq' e) (by positivity))
      refine ⟨⟨hC3.1, ⟨_, hC3⟩, fun γ hγ hne => ?_⟩, hC3⟩
      rw [← hd γ hγ] at hne
      have hne' : xs p.T χ ε i hi w q hcq (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) e γ ≠ 0 := by
        intro h0; apply hne; simp [h0]
      exact (hεq e).trans (h1.2.2 γ hγ hne')
  obtain ⟨ma1, ma2, ma3⟩ := main a hca εa Ka hε₀a hKa hKa' hQ1a hQ2a
  obtain ⟨mb1, mb2, mb3⟩ := main b hcb εb Kb hε₀b hKb hKb' hQ1b hQ2b
  have hdn : Tendsto (fun n : ℕ => KK * (Kp * bf / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat.congr
      (fun n => by simp)
    have := (h1.const_mul (Kp * bf)).const_mul KK
    simpa [div_eq_mul_inv, mul_assoc] using this
  exact formLev_limit P p.T _ ⟨i, by omega⟩ w N hw S⁻¹ (inv_pos.2 hS0)
    (xs p.T χ ε i hi w a hca f) (xs p.T χ ε i hi w b hcb f)
    (fun n => xs p.T χ ε i hi w a hca (hn n)) (fun n => xs p.T χ ε i hi w b hcb (hn n))
    (KK * (bf + Kp * bf)) (fun n => KK * (Kp * bf / ((n : ℝ) + 1))) hdn ma1 mb1 ma2 mb2 ma3 mb3

theorem cutCpt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε : ℝ) (cut : ℕ → B.Mat P.k P.r → ℂ)
    (hχ : C6.IsCut0 χ) (hε : 0 < ε) (hf : B.CkOn ⊤ (B.GV P.k P.r) f)
    (hcut : ∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) (n : ℕ) :
    KB.CptCoef Bs fun g => cut n g • D.cutF Bs χ f ε g := by
  have hcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cut n) := by
    have e : cut n = fun g => 1 - JCx2.pdPsi ((n : ℝ) + 1) g := funext fun g => cut_eq cut hcut n g
    rw [e]
    exact contDiff_const.sub (JCx2.pd_psi_cd _)
  refine ⟨JCx2.pd_smooth_smul hcs (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF Bs hχ hf ε), ⟨2 * ((n : ℝ) + 1), ?_⟩, ?_⟩
  · intro g _ hne
    have hc : cut n g ≠ 0 := by intro h0; apply hne; simp [h0]
    rw [hcut] at hc
    have hpos : 0 < (4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3 := by
      by_contra hle
      push_neg at hle
      apply hc
      rw [Real.smoothTransition.zero_of_nonpos hle]
      simp
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hsum : ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j) =
        ((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal]
      ring
    have hlt : ∑ i, ∑ j, Complex.normSq (g i j) < 4 * ((n : ℝ) + 1) ^ 2 := by
      rw [hsum] at hpos
      have h1 : ((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j) < 4 := by linarith
      have h2 : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j)) =
          ∑ i, ∑ j, Complex.normSq (g i j) := by
        field_simp
      have h3 : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j)) < ((n : ℝ) + 1) ^ 2 * 4 :=
        mul_lt_mul_of_pos_left h1 (by positivity)
      rw [h2] at h3
      linarith
    unfold B.gN
    rw [show (2 * ((n : ℝ) + 1)) = Real.sqrt ((2 * ((n : ℝ) + 1)) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  · obtain ⟨δ, hδ, hδ0⟩ := hχ.2.1
    refine ⟨δ * ε, by positivity, fun g _ hne => ?_⟩
    have hc : χ (Gf P.k P.r Bs.z Bs.z' g / ε) ≠ 0 := by
      intro h0; apply hne; simp [D.cutF, h0]
    have h1 : δ ≤ Gf P.k P.r Bs.z Bs.z' g / ε := by
      by_contra hlt; push_neg at hlt; exact hc (hδ0 _ hlt)
    rw [le_div_iff₀ hε] at h1
    linarith

end Formalism.FourierDecayAlt.P.PBE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MinorCellOfParts
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def RightRuleE : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), inWb k r z' → IsOpen D → Q.SmoothLev k r 0 D f →
    Q.RightEq k r z' 0 D f → ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ a b : Fin r, a.val < b.val →
      Q.EH k r (eI k r a) (eI k r b) f g = (if b.val = a.val + 1 then (1 : ℂ) else 0) • f g

def LeftRuleCell : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), inWb k r z → IsOpen D →
    (∀ g ∈ Q.Glev k r 0 ∩ D, ∀ n ∈ Q.Nlev k r 0, n * g ∈ D) → Q.SmoothLev k r 0 D f → Q.LeftEq k r z 0 D f →
    ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D → ∀ a b : Fin r, b.val < a.val →
      Q.EH k r (eI k r a) (eI k r b) f (Q.wCell k r (Fin.last r) c * g) =
        (if a.val = b.val + 1 then c a / c b else 0) • f (Q.wCell k r (Fin.last r) c * g)

def TorusCell : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (D : Set (Q.Mx k r)) (f : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r 0 D f → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
    Q.wCell k r (Fin.last r) c * g ∈ D → ∀ l : Fin r,
      Q.EH k r (eI k r l) (eI k r l) f (Q.wCell k r (Fin.last r) c * g) =
        pOp l (fun c' => f (Q.wCell k r (Fin.last r) c' * g)) c

def GaugeP : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (r : ℕ) (n : Fin r → ℕ) (H : (Fin r → ℂ) → E)
    (c : Fin r → ℂ), c ∈ OmX r → DifferentiableAt ℝ H c → ∀ l : Fin r,
      pOp l (fun c' => ((∏ a, ‖c' a‖ ^ n a : ℝ) : ℂ) • H c') c =
        ((∏ a, ‖c a‖ ^ n a : ℝ) : ℂ) • (pOp l H c + ((n l : ℂ) / 2) • H c)

def MinorCellOfParts : Prop := RightRuleE → LeftRuleCell → TorusCell → GaugeP → MinorCell

end Formalism.FourierDecayAlt.P.PBN
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopRatio
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

def topR {P : M.Par} (l0 : ℕ) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (ρ : M.Ty P) (y : ℝ) : ℂ :=
  Wd.qw (M.qC P) (D.positionted w) (y : ℂ) / Fr.xs (fun Y => M.sgn P l0 * M.xC P ρ Y) (D.positionted w) e ((y : ℂ) + 1)

def TopRatio : Prop :=
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ → 28 * Real.exp 1 ≤ Cc → ∀ (v : Fin S.f) (w : List C.Letter) (y : ℝ),
    KB.CutWord (D.parOf S v) (S.l + 1) ((true, y) :: w) → (∃ m, y ∈ S.grid v m) → w.length < S.Ntop →
    (∀ x ∈ w, (S.Ntop : ℝ) ^ 2 + 1 ≤ |y - x.2| ∧ (x.1 = false → (S.Ntop : ℝ) ^ 2 + 1 ≤ |y - (x.2 - 1)|)) →
    ∀ (e : Wd.Ix (Fin w.length)) (ρ : M.Ty (D.parOf S v)),
      0 < (topR (S.l + 1) w e ρ y).re ∧ (topR (S.l + 1) w e ρ y).im = 0 ∧
      |S.P v y| ≤ Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
        (Real.sqrt (S.T * S.T'))⁻¹ * (topR (S.l + 1) w e ρ y).re

def lamTop {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (b : ℕ) (v : Fin S.f) : ℝ :=
  √((2 * Real.pi / S.G.g) ^ (-(2 * S6.nuBlock S.G.r b ((S.G.r : ℤ) + 2 - b))) * Real.exp 1 *
    (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1)) * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
    (√(S.T * S.T'))⁻¹)

def TopLocB : Prop :=
  KB.DegTop → Top.VecVTypes → TopRatio →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    (∀ s, 2 ≤ s → s ≤ S.G.r + 1 → ∀ v, 0 ≤ lamTop S (S.G.r + 2 - s) v ∧
      2 * lamTop S (S.G.r + 2 - s) v ≤ S.base.szL (S.G.r + 2 - s) s v) ∧
    ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.TopLoc (setC S p F) v fun b _ => lamTop S b v

end

end Formalism.FourierDecayAlt.P.PBL
end
