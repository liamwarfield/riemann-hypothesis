module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConnectionRaisingConstantEq
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterpolationInverseMatrixSumIdentity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLAtMost
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsotropicNormalFormFullStatement

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
namespace Formalism.FourierDecayAlt.P

theorem normalFormFromModule_statement : Formalism.FourierDecayAlt.Q.NormalFormFromModule :=
  normal_form_from_module theorem_S_ring actual_pre_level actual_hypotheses_of_parts
    level_coordinates_commute types_complete

theorem normal_form_actual : Formalism.FourierDecayAlt.Q.NormalFormActual :=
  JacquetIntegral.normalFormActual_of_fromModule normalFormFromModule_statement

theorem level_start_actual : Formalism.FourierDecayAlt.Q.LevelStartActual :=
  JacquetIntegral.levelStartActual_of_fromModule normalFormFromModule_statement

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDatumUnit
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

noncomputable section

namespace DU

variable {k r : ℕ}

theorem hadd_l {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (x y w : Fin m → ℂ) :
    herm H (x + y) w = herm H x w + herm H y w := by
  simp [herm, Matrix.mulVec_add]

theorem hadd_r {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (x w w' : Fin m → ℂ) :
    herm H x (w + w') = herm H x w + herm H x w' := by
  simp [herm, add_dotProduct]

theorem hsmul_l {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (x w : Fin m → ℂ) :
    herm H (c • x) w = c * herm H x w := by
  simp [herm, Matrix.mulVec_smul]

theorem hsmul_r {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (x w : Fin m → ℂ) :
    herm H x (c • w) = conj c * herm H x w := by
  simp [herm, smul_dotProduct, Complex.star_def]

private theorem herm_swap_eq_zero_of_eq_zero {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (hH : ∀ i j, H i j = star (H j i))
    (v w : Fin m → ℂ) : herm H w v = conj (herm H v w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [herm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hH b a]
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_conj]
  ring

private theorem Hpk_apply_eq_star_apply_swap : ∀ i j : Fin (2 * r + k + 1), Hpk k r i j = star (Hpk k r j i) := by
  intro i j
  simp only [Hpk]
  split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | (exfalso; omega)

theorem hswap (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) w v = conj (herm (Hpk k r) v w) := by
  exact herm_swap_eq_zero_of_eq_zero _ Hpk_apply_eq_star_apply_swap v w

theorem blockProjection_of_mem_block {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : SSn.wbP k r v = v := by
  funext i
  simp only [SSn.wbP]
  split_ifs with h
  · rfl
  · exact (hv i (by omega)).symm

theorem prWv_of {z v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    SSn.prWv k r z v = v + (herm (Hpk k r) v z / (Tz k r z : ℂ)) • z := by
  simp only [SSn.prWv, blockProjection_of_mem_block hv]

theorem prWv_fix {z x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (h0 : herm (Hpk k r) x z = 0) :
    SSn.prWv k r z x = x := by
  rw [prWv_of hx, h0]
  simp

private theorem herm_Hpk_self_eq_neg_Tz (z : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by
  have h := hswap (k := k) (r := r) z z
  apply Complex.ext
  · simp [Tz]
  · have h2 := congrArg Complex.im h
    simp only [Complex.conj_im] at h2
    simp
    linarith

theorem prWv_perp {z y : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) (hy : inWb k r y) :
    herm (Hpk k r) (SSn.prWv k r z y) z = 0 := by
  have hT0 : (Tz k r z : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [prWv_of hy, hadd_l, hsmul_l, herm_Hpk_self_eq_neg_Tz]
  have h1 : herm (Hpk k r) y z / (Tz k r z : ℂ) * -(Tz k r z : ℂ) = -herm (Hpk k r) y z := by
    rw [div_mul_eq_mul_div, mul_neg, neg_div, mul_div_assoc, div_self hT0, mul_one]
  rw [h1]
  ring

theorem prWv_inWb {z y : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hy : inWb k r y) :
    inWb k r (SSn.prWv k r z y) := by
  intro i hi
  have h1 : SSn.wbP k r y i = 0 := by
    simp only [SSn.wbP]
    rw [if_neg]
    omega
  simp only [SSn.prWv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz i hi, h1, mul_zero, add_zero]

private theorem herm_Hpk_self_self_eq_neg_ofReal_Tz (z : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by
  have h := hswap (k := k) (r := r) z z
  apply Complex.ext
  · simp [Tz]
  · have h2 := congrArg Complex.im h
    simp only [Complex.conj_im] at h2
    simp
    linarith

theorem prWv_norm {z y : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) (hy : inWb k r y) {ζ : ℂ} {T' : ℝ}
    (hyy : herm (Hpk k r) y y = -(T' : ℂ)) (hyz : herm (Hpk k r) y z = ζ) :
    herm (Hpk k r) (SSn.prWv k r z y) (SSn.prWv k r z y) =
      ((Complex.normSq ζ / Tz k r z - T' : ℝ) : ℂ) := by
  have hT0 : (Tz k r z : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [prWv_of hy]
  simp only [hadd_l, hadd_r, hsmul_l, hsmul_r, herm_Hpk_self_self_eq_neg_ofReal_Tz, hyy, hyz]
  rw [hswap y z, hyz, map_div₀, Complex.conj_ofReal]
  push_cast
  rw [← Complex.mul_conj]
  field_simp
  ring

theorem unitH_facts {z x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (h0 : herm (Hpk k r) x z = 0) {s : ℝ}
    (hs : 0 < s) (hxx : herm (Hpk k r) x x = (s : ℂ)) :
    SSn.prWv k r z (SSn.unitH k r x) = SSn.unitH k r x ∧ herm (Hpk k r) (SSn.unitH k r x) (SSn.unitH k r x) = 1 := by
  have hu : SSn.unitH k r x = (((Real.sqrt s)⁻¹ : ℝ) : ℂ) • x := by
    simp only [SSn.unitH, hxx, Complex.ofReal_re]
  have hin : inWb k r (SSn.unitH k r x) := by
    intro i hi
    rw [hu]
    simp [hx i hi]
  refine ⟨prWv_fix hin ?_, ?_⟩
  · rw [hu, hsmul_l, h0, mul_zero]
  · rw [hu, hsmul_l, hsmul_r, hxx, Complex.conj_ofReal]
    have key : (Real.sqrt s)⁻¹ * ((Real.sqrt s)⁻¹ * s) = 1 := by
      rw [← mul_assoc, ← mul_inv, ← sq, Real.sq_sqrt hs.le, inv_mul_cancel₀ hs.ne']
    exact_mod_cast key

theorem base {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    SSn.prWv k r z (SSn.nu0 k r z z' μsec ζ) = SSn.nu0 k r z z' μsec ζ ∧
      herm (Hpk k r) (SSn.nu0 k r z z' μsec ζ) (SSn.nu0 k r z z' μsec ζ) = 1 ∧
      SSn.prWv k r z' (SSn.nu0' k r z z' μsec ζ) = SSn.nu0' k r z z' μsec ζ ∧
      herm (Hpk k r) (SSn.nu0' k r z z' μsec ζ) (SSn.nu0' k r z z' μsec ζ) = 1 := by
  have hm := NFRadRedA.muZ_uwb hsec hζ
  have hG := NFRadRedA.uwb_glev hm
  have hU : NF.muZ k r μsec ζ ∈ UH (Hpk k r) := hG.1
  have hGi := FrameEntries.glev_inv hG
  have hUi : (NF.muZ k r μsec ζ)⁻¹ ∈ UH (Hpk k r) := hGi.1
  have hyz : herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ z') z = ζ := by
    rw [← NFRadRedA.zeta_eq]; exact NFRadRedA.zeta_muZ hz hz' hsec hζ
  have hy : inWb k r (NF.muZ k r μsec ζ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hyi : inWb k r ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) := Qx8.inWb_mulVec hGi hz
  have hyy : herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ z') (NF.muZ k r μsec ζ *ᵥ z') = -((Tz k r z' : ℝ) : ℂ) := by
    rw [Qx2.herm_uh hU, FrameEntries.herm_self]
  have hyyi : herm (Hpk k r) ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) =
      -((Tz k r z : ℝ) : ℂ) := by
    rw [Qx2.herm_uh hUi, FrameEntries.herm_self]
  have hyzi : herm (Hpk k r) ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) z' = conj ζ := by
    rw [hswap, ← FrameEntries.herm_inv hU, hyz]
  have hpos : 0 < Complex.normSq ζ / Tz k r z - Tz k r z' := by
    rw [sub_pos, lt_div_iff₀ hT]; linarith
  have hposi : 0 < Complex.normSq (conj ζ) / Tz k r z' - Tz k r z := by
    rw [Complex.normSq_conj, sub_pos, lt_div_iff₀ hT']; linarith
  obtain ⟨h1, h2⟩ := unitH_facts (prWv_inWb hz hy) (prWv_perp hT hy) hpos (prWv_norm hT hy hyy hyz)
  obtain ⟨h3, h4⟩ := unitH_facts (prWv_inWb hz' hyi) (prWv_perp hT' hyi) hposi (prWv_norm hT' hyi hyyi hyzi)
  exact ⟨h1, h2, h3, h4⟩

end DU

theorem datum_unit_norm_holds : DatumUnit := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v ζ hζ
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hζ' : Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' < Complex.normSq ζ := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; exact hζ
  exact DU.base hPl.2.1 hPl.2.2.1 (T v).base.T_pos (T v).base.T'_pos (T v).base.sec hζ'

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseCutoffIsTruncation
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P.Topx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


section helpers

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def chi0 (x : ℝ) : ℝ := Real.smoothTransition (2 * x - 1)

theorem base_cutoff_is_truncation : C6.IsCut0 chi0 := by
  unfold C6.IsCut0
  refine ⟨?_, ⟨1 / 2, by norm_num, fun x hx => ?_⟩, fun x hx => ?_⟩
  · exact Real.smoothTransition.contDiff.comp (f := fun x : ℝ => 2 * x - 1) (by fun_prop)
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · exact Real.smoothTransition.one_of_one_le (by linarith)

end helpers

section diff

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end diff

end Formalism.FourierDecayAlt.P.Topx2
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCore
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def ActHyp (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) : Prop :=
  Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' ∧ Q.IsActualLevel X d.L ∧ Fr.IsStarLevel d.L ∧ d.Rel ∧ ∀ Y : ℂ, X.QQ Y = d.QQ Y

def GQQ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
    Gauge.FamR P Bs Dc Φ →
    ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
      MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
        MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ

def IsSSPt (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (l : ℕ) (S : ℂ → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) : Prop :=
  ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ), c ∈ OmX P.r → ∀ ζ ∈ Gauge.GC.Ann P,
    ((d.SS l).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      S ζ ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ))

end preds

def GQQSSF : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e → GQQ P Bs e → Gauge.GC.SSF P Bs d e

def SSPointwise : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∃ S, IsSSPt P Bs d l S

def ThConst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∃ θ : M.Ty P → ℂ, ∀ ζ ∈ Gauge.GC.Ann P, ∀ π ρ : M.Ty P, M.Up P l π ρ →
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          θ π • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf)

def SSEntry : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e → Gauge.GC.SSF P Bs d e →
    ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S → ∀ ζ ∈ Gauge.GC.Ann P, ∀ π ρ : M.Ty P,
      inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (S ζ (e π ζ))) =
        if M.Up P l π ρ then ((Real.sqrt (M.Nrm P l π) : ℝ) : ℂ) else 0

def ThtGaugeConstOfCore : Prop :=
  GQQSSF → SSPointwise → ThConst → SSEntry → PRho.PRhoExists → PRho.GaugeLines → DatumUnit → ThtGaugeConst

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsHaarStabilizer
namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

def lowP {m : ℕ} (w : Equiv.Perm (Fin m)) (y : C2.LPidx w → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  C2.lowOf (fun q : C2.LPidx w => q.1) y

def lowS {m : ℕ} (w : Equiv.Perm (Fin m)) (x : C2.Lstidx w → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  C2.lowOf (fun q : C2.Lstidx w => q.1) x

def utc {m : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) : G.UT m → ℂ := fun q => u q.1.1 q.1.2

def lsc {m : ℕ} (w : Equiv.Perm (Fin m)) (l : Matrix (Fin m) (Fin m) ℂ) : C2.Lstidx w → ℂ := fun q => l q.1.1 q.1.2

def SplitUT : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)), ∃ e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT m → ℂ),
    MeasurePreserving e volume volume ∧ ∀ p, G.upper (e p) = (lowS w p.1)ᴴ * (lowP w p.2)ᴴ

def UTLeft : Prop :=
  ∀ (m : ℕ) (a : Matrix (Fin m) (Fin m) ℂ), a ∈ C2.UTset m →
    MeasurePreserving (fun u : G.UT m → ℂ => utc (a * G.upper u)) volume volume

def LstLeft : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ), (∀ a, d a ≠ 0) → ∀ x0 : C2.Lstidx w → ℂ,
    MeasurePreserving (fun x : C2.Lstidx w → ℂ => lsc w (lowS w x0 * lowS w x)) volume volume ∧
    ∀ x, lowS w x0 * lowS w x = lowS w (lsc w (lowS w x0 * lowS w x))

def MinorsLU : Prop :=
  ∀ (r : ℕ) (L M U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ), L ∈ C2.LTset (r + 1) → U ∈ C2.UTset (r + 1) →
    (L * M * U).det = M.det ∧
      ((L * M * U).submatrix Fin.castSucc Fin.castSucc).det = (M.submatrix Fin.castSucc Fin.castSucc).det

def PhiTopCoords : Prop :=
  ∀ (m : ℕ) (σ w : Equiv.Perm (Fin m)) (d d' : Fin m → ℂ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Φ : G.Mat m → V), (∀ a, d' a ≠ 0) → U.hMat σ d = C2.monoP w d' →
    U.PhiTop (p := m) (s := 0) U.betaU σ d Φ (fun x => x.elim0) =
      ∫ q : (C2.LPidx w → ℂ) × (G.UT m → ℂ),
        (C2.psiC cStd (C2.simpleUp (lowP w q.1)ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper q.2)))) •
          Φ (Matrix.of.symm (lowP w q.1 * C2.monoP w d' * G.upper q.2))

def ExistsHaarStabilizer : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → ∃ μ0 : Measure (Mt k r), B.IsHaarOn (C2.N0set k r z) μ0

def DisintN : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → ∀ μ0 μN : Measure (Mt k r),
    B.IsHaarOn (C2.N0set k r z) μ0 → B.IsHaarOn (Nset k r) μN →
    ∃ c : NNReal, 0 < c ∧ μN = c • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0).map
      (fun p => Matrix.of.symm (C2.tauM k r z (G.upper p.1) * Matrix.of p.2))

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCTheta
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def rhoSum (P : M.Par) (ρ : M.Ty P) : ℝ := ∑ i ∈ Finset.Icc 1 (P.k - 1), M.rho P ρ i

def uSum (P : M.Par) : ℝ := ∑ i ∈ Finset.Icc 1 P.k, (P.u i + P.u' i)

theorem aC_eq (P : M.Par) (ρ : M.Ty P) : M.aC P ρ = uSum P / 2 - rhoSum P ρ := rfl

def ThetaNF (P : M.Par) {𝒜 : Type} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] (d : Q.NFData P 𝒜) : 𝒜 :=
  d.L.ζ * d.L.nab + d.L.ζb * d.L.nabs + d.κ (fun ρ => ((rhoSum P ρ : ℝ) : ℂ)) +
    algebraMap ℂ 𝒜 d.L.TT * d.L.GGi * d.κ (fun ρ => ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ))

def GTRTopNF : Prop :=
  ∀ (P : M.Par) (𝒜 : Type) [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] (d : Q.NFData P 𝒜),
    P.OK → 2 ≤ P.k → Fr.IsStarLevel d.L → d.Rel → d.L.TT = ((P.TT : ℝ) : ℂ) →
    ∃ c : ℕ → 𝒜, (∀ Y : ℂ, d.QQ Y 0 0 = ∑ j ∈ Finset.range (P.k + 2), Y ^ j • c j) ∧
      ∃ s : ℤ, c P.k = ThetaNF P d + ((s : ℂ)) • (1 : 𝒜)

def GTRTopAct : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → 2 ≤ P.k → ∀ X : Q.ActualOps P.k P.r z z' π π',
    ∃ c : ℕ → Module.End ℂ (Q.RadSp P.k P.r z z' π π'),
      (∀ Y : ℂ, X.t Y 0 0 = ∑ j ∈ Finset.range (P.k + 2), Y ^ j • c j) ∧
      ∃ s : ℤ, ∀ (Φ : Q.RadSp P.k P.r z z' π π'), ∀ x ∈ Q.DomR P.k P.r z z',
        (c P.k Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
            Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
              ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
            ((s : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBesselEigen
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP

theorem thr_of_budget (k r : ℕ) (N A₀ : ℝ) (hk : 2 ≤ k) (hN : 0 ≤ N)
    (hA : 100 * ((r : ℝ) + 1) ^ 4 * (N * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀) :
    JF.TransportedAlt k r A₀ (2 * r + k + 1) := by
  unfold JF.TransportedAlt
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have hcast : ((2 * r + k + 1 : ℕ) : ℝ) = n := by rw [hn]; push_cast; ring
  rw [hcast, lt_div_iff₀ (by positivity)]
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; linarith
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
  have h4 : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) ^ 4 := by
    have : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
    calc (r : ℝ) + 1 = ((r : ℝ) + 1) * 1 := by ring
      _ ≤ ((r : ℝ) + 1) * ((r : ℝ) + 1) ^ 3 := by gcongr
      _ = ((r : ℝ) + 1) ^ 4 := by ring
  have h3 : n ^ 2 ≤ n ^ 3 := by
    calc n ^ 2 = n ^ 2 * 1 := by ring
      _ ≤ n ^ 2 * n := by gcongr
      _ = n ^ 3 := by ring
  have hNn : 0 ≤ N * n ^ 2 := by positivity
  have hstep : 100 * ((r : ℝ) + 1) * n ^ 2 ≤ A₀ := by
    calc 100 * ((r : ℝ) + 1) * n ^ 2 ≤ 100 * ((r : ℝ) + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by
          have : ((r : ℝ) + 1) * n ^ 2 ≤ ((r : ℝ) + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by
            calc ((r : ℝ) + 1) * n ^ 2 ≤ ((r : ℝ) + 1) ^ 4 * n ^ 2 := by gcongr
              _ ≤ ((r : ℝ) + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by gcongr; linarith
          linarith
      _ ≤ A₀ := hA
  have hrn : (r : ℝ) * n ≤ ((r : ℝ) + 1) * n ^ 2 := by
    have : (r : ℝ) ≤ (r : ℝ) + 1 := by linarith
    calc (r : ℝ) * n ≤ ((r : ℝ) + 1) * n := by gcongr
      _ = ((r : ℝ) + 1) * n * 1 := by ring
      _ ≤ ((r : ℝ) + 1) * n * n := by gcongr
      _ = ((r : ℝ) + 1) * n ^ 2 := by ring
  have hpos : 0 < ((r : ℝ) + 1) * n ^ 2 := by positivity
  nlinarith

theorem bessel_eigenvalue_equation_holds : BesselEigen := by
  refine ⟨100, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Y x hx
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, hCk, hk2, hA, _⟩, _, _, _⟩ := hB
  obtain ⟨_, hv⟩ := hbuilt
  obtain ⟨_, _, _, hplace, hCC, heig⟩ := hv v
  have hThr : JF.TransportedAlt S.G.k S.G.r A₀ (2 * S.G.r + S.G.k + 1) :=
    thr_of_budget S.G.k S.G.r (S.Ntop : ℝ) A₀ hk2 (Nat.cast_nonneg _) hA
  have hT : Tz S.G.k S.G.r (T v).base.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r (T v).base.z' = S.T' := hplace.2.2.2.2.1
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := by
    refine ⟨hx.1, ?_⟩
    have h3 : S.T * S.T' < Complex.normSq x.2 := hx.2
    rw [hT, hT']; exact h3
  have hg : B.gq (T v).base x ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' :=
    Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base x hq
  have hgG : B.gq (T v).base x ∈ B.GV S.G.k S.G.r := hg.1
  have hCkn : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (B.GV S.G.k S.G.r) (f v) :=
    Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top (hCk v)
  rw [Formalism.FourierDecayAlt.P.casimir_under_jacquet_integral S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A₀
    (2 * S.G.r + S.G.k + 1) (f v) (Y : ℂ) le_rfl hThr (hCC _) _ hg]
  have hint : ∀ᵐ p ∂(T v).base.μSS,
      JF.xiP (T v).base p • Q.CV S.G.k S.G.r (Y : ℂ) (B.rho (T v).base p (f v)) (B.gq (T v).base x) =
        ((S.P v Y : ℝ) : ℂ) • (JF.xiP (T v).base p • B.rho (T v).base p (f v) (B.gq (T v).base x)) := by
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS (T v).base] with p hp
    rw [Formalism.FourierDecayAlt.P.capelli_rho_commute S.G.k S.G.r _ _ (T v).base (Y : ℂ) (f v) p hp hCkn _ hgG]
    have hs := Formalism.FourierDecayAlt.P.B7.sgs_mem (T v).base hp hgG
    simp only [B.rho]
    rw [heig Y _ hs, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]
  rw [integral_congr_ae hint, integral_smul]
  rfl

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLExistsOf
open Matrix Finset Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExOf

noncomputable section

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA

theorem side {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {n r : ℕ}
    {z e : Fin (2 * r + (n + 1) + 1) → ℂ} {π : Mx (n + 1) r → (W →L[ℂ] W)} {u : ℕ → ℝ} {β : ℂ}
    {L : Fin (n + 1) → ℤ} (hz : inWb (n + 1) r z) (hT : 0 < Tz (n + 1) r z) (hty : IsType (n + 1) r z π u)
    (hL : StrictAnti L)
    (hu : ∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ))
    (he : inWb (n + 1) r e) (hez : herm (Hpk (n + 1) r) e z = 0) (hee : herm (Hpk (n + 1) r) e e = 1)
    {Bs₀ : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ} (hB₀ : IsFrameOf (n + 1) r [z, e] Bs₀) :
    GlRel (EB π Bs₀) ∧ DirectSum.IsInternal (fun M : {M : Fin n → ℤ // Box L M} => CapSp (EB π Bs₀) (shf β M.1)) ∧
      ∀ M : {M : Fin n → ℤ // Box L M}, CapSp (EB π Bs₀) (shf β M.1) ≠ ⊥ ∧
        ∀ S' : Submodule ℂ W, S' ≤ CapSp (EB π Bs₀) (shf β M.1) → Stab (EB π Bs₀) S' →
          S' = ⊥ ∨ S' = CapSp (EB π Bs₀) (shf β M.1) := by
  obtain ⟨hnt, hrep, hcont, -, hirr, hcap⟩ := hty
  have hR : IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  have hB₁ := FrameExtension.frame_snoc hB₀ he hez hee
  set Bs₁ : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs₀ e with hBs₁
  have hsub : subA (EB π Bs₁) = EB π Bs₀ := FrameExtension.subA_EB π Bs₀ e
  obtain ⟨hgl, hq⟩ := frame_general_linear W (n + 1) r (n + 1) z π Bs₁ hR hB₁
  have hH : Hyp (EB π Bs₁) β L := by
    refine ⟨hgl, ⟨hnt, fun S hS => hirr S (lie_stabilizer W (n + 1) r z π Bs₁ hz hT hR hB₁ S hS)⟩, hL, ?_⟩
    intro w v
    rw [← hq w v, hcap Bs₁ hB₁ w v, FrameExtension.prod_Icc_fin]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [← hu j]
    ring
  obtain ⟨hint, hS⟩ := branching_algebraic W n (EB π Bs₁) β L hH
  rw [hsub] at hint hS
  exact ⟨(frame_general_linear W (n + 1) r n z π Bs₀ hR (FrameExtension.frame_weaken hB₀)).1, hint, hS⟩

theorem labels {n r : ℕ} {T T' : ℝ} {u u' : ℕ → ℝ} (hOK : (⟨n + 1, r, T, T', u, u'⟩ : M.Par).OK)
    (ρ : M.Ty ⟨n + 1, r, T, T', u, u'⟩) (L L' : Fin (n + 1) → ℤ)
    (hL : ∀ j : Fin (n + 1), u ((j : ℕ) + 1) - u 1 = (L j : ℝ))
    (hL' : ∀ j : Fin (n + 1), u' ((j : ℕ) + 1) - u 1 = (L' j : ℝ)) :
    ∃ lab : Fin n → ℤ, Box L lab ∧ Box L' lab ∧
      SDec (shf ((u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2) lab) ∧
      ∀ Y : ℂ, cpol (shf ((u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2) lab) (Y + (((n + 1 : ℕ) : ℂ) - 2) / 2) =
        Formalism.FourierDecayAlt.M.xC ⟨n + 1, r, T, T', u, u'⟩ ρ Y := by
  have hmem : ∀ j : Fin n, (j : ℕ) + 1 ∈ Finset.Icc 1 ((⟨n + 1, r, T, T', u, u'⟩ : M.Par).k - 1) := fun j =>
    Finset.mem_Icc.2 ⟨by omega, by show (j : ℕ) + 1 ≤ n + 1 - 1; omega⟩
  choose N hN using fun j : Fin n => Qx8.rho_int hOK ρ ((j : ℕ) + 1) (hmem j)
  have hN' : ∀ j : Fin n, M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) = (N j : ℝ) + u 1 + 1 / 2 := fun j => by
    have := hN j
    change M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) - u 1 - 1 / 2 = (N j : ℝ) at this
    linarith
  have hI := types_interlace _ hOK ρ
  have hI' : ∀ j : Fin n, M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) + 1 / 2 ≤ u ((j : ℕ) + 1) ∧
      M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) + 1 / 2 ≤ u' ((j : ℕ) + 1) ∧ u ((j : ℕ) + 1 + 1) + 1 / 2 ≤ M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) ∧
      u' ((j : ℕ) + 1 + 1) + 1 / 2 ≤ M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) := fun j => hI _ (hmem j)
  refine ⟨fun j => N j + 1, ?_, ?_, ?_, ?_⟩
  · intro j
    have h1 := hL j.succ
    have h2 := hL j.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    have h3 := hI' j
    have h4 := hN' j
    constructor
    · have : (L j.succ : ℝ) < ((N j + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : ((N j + 1 : ℤ) : ℝ) ≤ (L j.castSucc : ℝ) := by push_cast; linarith
      exact_mod_cast this
  · intro j
    have h1 := hL' j.succ
    have h2 := hL' j.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    have h3 := hI' j
    have h4 := hN' j
    constructor
    · have : (L' j.succ : ℝ) < ((N j + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : ((N j + 1 : ℤ) : ℝ) ≤ (L' j.castSucc : ℝ) := by push_cast; linarith
      exact_mod_cast this
  · intro a b hab
    have hlt := Qx8.rho_anti hOK ρ ((a : ℕ) + 1) ((b : ℕ) + 1) (by omega) (by simp only [Fin.lt_def] at hab; omega)
      (by show (b : ℕ) + 1 ≤ n + 1 - 1; omega)
    have ha := hN' a
    have hb := hN' b
    have hNab : N b < N a := by
      have : (N b : ℝ) < (N a : ℝ) := by linarith
      exact_mod_cast this
    refine ⟨(N a - N b - 1).toNat, ?_⟩
    have h1 : (((N a - N b - 1).toNat : ℕ) : ℤ) = N a - N b - 1 := Int.toNat_of_nonneg (by omega)
    have h2 : (((N a - N b - 1).toNat : ℕ) : ℂ) = ((N a - N b - 1 : ℤ) : ℂ) := by exact_mod_cast h1
    simp only [shf]
    rw [h2]
    push_cast
    ring
  · intro Y
    unfold M.xC cpol
    rw [show (⟨n + 1, r, T, T', u, u'⟩ : M.Par).k - 1 = n from rfl, ProductIntervalFrames.prod_Icc_one]
    refine Finset.prod_congr rfl fun j _ => ?_
    have h4 : (M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) : ℂ) = (N j : ℂ) + (u 1 : ℂ) + 1 / 2 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) (hN' j)
      push_cast at this
      exact this
    simp only [shf]
    rw [h4]
    push_cast
    ring

theorem lie_existence_of_iso_group : KLExistsOf := by
  intro hIso hLG Wp Wq _ _ _ _ _ _ P
  obtain ⟨k, r, T, T', u, u'⟩ := P
  intro z z' π π' hPl hk
  have hk' : 2 ≤ k := hk
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  intro g hg hGG Fr hFr ρ
  obtain ⟨hOK, hz, hz', hTz, hTz', hπ, hπ'⟩ := id hPl
  have hT : 0 < Tz (n + 1) r z := by
    have h2 : Tz (n + 1) r z = T := hTz
    rw [h2]; exact hOK.T_pos
  have hT' : 0 < Tz (n + 1) r z' := by
    have h2 : Tz (n + 1) r z' = T' := hTz'
    rw [h2]; exact hOK.T'_pos
  obtain ⟨-, hrep, hcont, -, -, -⟩ := id hπ
  obtain ⟨-, hrep', hcont', -, -, -⟩ := id hπ'
  obtain ⟨e', f, -, -, -, -, -, -, -, -, ⟨he'W, he'z, he'e⟩, ⟨hfW, hfz, hff⟩, hFr1, hFr2⟩ :=
    KLAM.geom_fr hz hz' hT hT' hg hGG hFr

  have hIcc : ∀ j : Fin (n + 1), (j : ℕ) + 1 ∈ Finset.Icc 1 (n + 1) := fun j =>
    Finset.mem_Icc.2 ⟨by omega, by omega⟩
  choose L hL using fun j : Fin (n + 1) => hOK.int_u ((j : ℕ) + 1) (hIcc j)
  choose L' hL' using fun j : Fin (n + 1) => hOK.int_u' ((j : ℕ) + 1) (hIcc j)
  have hL2 : ∀ j : Fin (n + 1), u ((j : ℕ) + 1) - u 1 = (L j : ℝ) := hL
  have hL2' : ∀ j : Fin (n + 1), u' ((j : ℕ) + 1) - u 1 = (L' j : ℝ) := hL'
  have hgap : ∀ j : Fin n, max (u ((j : ℕ) + 1 + 1)) (u' ((j : ℕ) + 1 + 1)) + 1 / 2 ≤
      min (u ((j : ℕ) + 1)) (u' ((j : ℕ) + 1)) - 1 / 2 := fun j =>
    hOK.gap ((j : ℕ) + 1) (Finset.mem_Icc.2 ⟨by omega, by show (j : ℕ) + 1 ≤ n + 1 - 1; omega⟩)
  have hanti : StrictAnti L := Fin.strictAnti_iff_succ_lt.2 fun j => by
    have h1 := hL2 j.castSucc
    have h2 := hL2 j.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    have h3 := hgap j
    have h5 := le_max_left (u ((j : ℕ) + 1 + 1)) (u' ((j : ℕ) + 1 + 1))
    have h6 := min_le_left (u ((j : ℕ) + 1)) (u' ((j : ℕ) + 1))
    have : (L j.succ : ℝ) < (L j.castSucc : ℝ) := by linarith
    exact_mod_cast this
  have hanti' : StrictAnti L' := Fin.strictAnti_iff_succ_lt.2 fun j => by
    have h1 := hL2' j.castSucc
    have h2 := hL2' j.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    have h3 := hgap j
    have h5 := le_max_right (u ((j : ℕ) + 1 + 1)) (u' ((j : ℕ) + 1 + 1))
    have h6 := min_le_right (u ((j : ℕ) + 1)) (u' ((j : ℕ) + 1))
    have : (L' j.succ : ℝ) < (L' j.castSucc : ℝ) := by linarith
    exact_mod_cast this
  set β : ℂ := (u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 with hβ
  have hrel : ∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ) := fun j => by
    have h : (u ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) = (L j : ℂ) := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (hL2 j)
    rw [hβ, ← h]
    ring
  have hrel' : ∀ j : Fin (n + 1), (u' ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L' j : ℂ) := fun j => by
    have h : (u' ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) = (L' j : ℂ) := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (hL2' j)
    rw [hβ, ← h]
    ring
  obtain ⟨M, hbox, hbox', hsd, hcp⟩ := labels hOK ρ L L' hL2 hL2'
  have hfin : Finite {M : Fin n → ℤ // Box L' M} := by
    refine Finite.of_injective (β := ∀ j : Fin n, Finset.Ioc (L' j.succ) (L' j.castSucc))
      (fun M j => ⟨M.1 j, Finset.mem_Ioc.2 (M.2 j)⟩) ?_
    intro M₁ M₂ h
    apply Subtype.ext
    funext j
    exact congrArg Subtype.val (congrFun h j)
  letI : Fintype {M : Fin n → ℤ // Box L' M} := Fintype.ofFinite _

  obtain ⟨hgl', hint', hS'⟩ := side hz' hT' hπ' hanti' hrel' he'W he'z he'e hFr1
  obtain ⟨hgl, -, hS⟩ := side hz hT hπ hanti hrel hfW hfz hff hFr2
  set Mb : {M : Fin n → ℤ // Box L M} := ⟨M, hbox⟩ with hMb
  set Mb' : {M : Fin n → ℤ // Box L' M} := ⟨M, hbox'⟩ with hMb'
  set E := EB π (fun a => g *ᵥ Fr a) with hE
  set E' := EB π' Fr with hE'
  have hstabs' : ∀ (j : {M : Fin n → ℤ // Box L' M}) (a b : Fin n), ∀ v ∈ CapSp E' (shf β j.1), E' a b v ∈ CapSp E' (shf β j.1) :=
    fun j a b => (capelli_stabilizer Wq n E' (shf β j.1) hgl').1 a b
  have hstab : Stab E (CapSp E (shf β M)) := (capelli_stabilizer Wp n E (shf β M) hgl).1
  have hstab' : Stab E' (CapSp E' (shf β M)) := (capelli_stabilizer Wq n E' (shf β M) hgl').1
  obtain ⟨A, hA0, hAi⟩ := hIso (CapSp E (shf β M)) (CapSp E' (shf β M)) n (resE E _ hstab) (resE E' _ hstab')
    (shf β M) (glRel_resE hgl _ hstab) (glRel_resE hgl' _ hstab') (irr_resE _ hstab (hS Mb).1 (hS Mb).2)
    (irr_resE _ hstab' (hS' Mb').1 (hS' Mb').2) hsd (cap_resE (shf β M) hstab) (cap_resE (shf β M) hstab')

  set p : Wq →ₗ[ℂ] CapSp E' (shf β M) := projI hint' Mb' with hp
  have hpE : ∀ a b v, p (E' a b v) = resE E' _ hstab' a b (p v) := fun a b v =>
    projI_comm hint' (E' a b) (fun j => hstabs' j a b) Mb' v
  set Xl : Wq →ₗ[ℂ] Wp := (CapSp E (shf β M)).subtype ∘ₗ (A ∘ₗ p) with hXl
  set X : Wq →L[ℂ] Wp := LinearMap.toContinuousLinearMap Xl with hX
  have hXv : ∀ v, X v = (A (p v) : Wp) := fun v => by
    rw [hX, LinearMap.coe_toContinuousLinearMap']
    rfl
  have hAv : ∀ a b x, A (resE E' _ hstab' a b x) = resE E _ hstab a b (A x) := fun a b x =>
    LinearMap.congr_fun (hAi a b) x
  have hXint : ∀ (a b : Fin n) (v : Wq), X (EB π' Fr a b v) = EB π (fun i => g *ᵥ Fr i) a b (X v) := by
    intro a b v
    rw [hXv, hXv]
    change (A (p (E' a b v)) : Wp) = E a b (A (p v) : Wp)
    rw [hpE, hAv, resE_apply]
  refine ⟨X, hLG Wp Wq (n + 1) r z z' π π' hz hz' hT hT' ⟨hrep, hcont⟩ ⟨hrep', hcont'⟩ g hg hGG Fr hFr X hXint, ?_, ?_⟩
  · intro Y v
    rw [hXv, hXv]
    change (A (p (qdet E' (Y + (((n + 1 : ℕ) : ℂ) - 2) / 2) v)) : Wp) = Formalism.FourierDecayAlt.M.xC ⟨n + 1, r, T, T', u, u'⟩ ρ Y • (A (p v) : Wp)
    rw [qdet_int p hpE, cap_resE (shf β M) hstab', map_smul, Submodule.coe_smul, hcp Y]
  · intro hX0
    obtain ⟨x, hx⟩ : ∃ x, A x ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hA0 (LinearMap.ext hc)
    apply hx
    have h1 : X (x : Wq) = 0 := by rw [hX0]; rfl
    rw [hXv, hp, projI_self hint' (i := Mb') x] at h1
    exact_mod_cast h1

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExOf

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem lie_existence_of_iso_group : KLExistsOf := KLExOf.lie_existence_of_iso_group

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLSliceDZ
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem second_shift_slice_derivative : GTSSLSliceDZ := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl T hT Φ Φ' c c' hc hc' hEq ζ hζ
  obtain ⟨n, A, -, hTA⟩ := hT
  have hTT : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl
  have hU : IsOpen (Ann P) := isOpen_lt continuous_const Complex.continuous_normSq
  have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTT]; exact hζ⟩
  have hq' : ((c', ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc', by rw [hTT]; exact hζ⟩
  have hev : (fun ζ' => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ')) =ᶠ[nhds ζ]
      (fun ζ' => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c', ζ')) := by
    filter_upwards [hU.mem_nhds hζ] with ζ' hζ'
    have m : ((c, ζ') : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTT]; exact hζ'⟩
    have m' : ((c', ζ') : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc', by rw [hTT]; exact hζ'⟩
    unfold NF.radR
    rw [Set.indicator_of_mem m, Set.indicator_of_mem m']
    exact hEq ζ' hζ'
  have e1 : NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ) =
      (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) := by
    unfold NF.radR; rw [Set.indicator_of_mem hq]
  have e2 : NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c', ζ) =
      (T Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ) := by
    unfold NF.radR; rw [Set.indicator_of_mem hq']
  have h1 := hTA Φ (c, ζ) hq
  have h2 := hTA Φ' (c', ζ) hq'
  dsimp only at h1 h2
  rw [← e1, ← e2, h1, h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCAsm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem toSm_of_mem (P : M.Par) {u : MA.Qp P.r P.TT → ℂ} (h : u ∈ MA.smSub P.r P.TT) (q : MA.Qp P.r P.TT) :
    (MA.toSm P u : MA.Qp P.r P.TT → ℂ) q = u q := by
  unfold MA.toSm
  rw [dite_eq_left h]

theorem assumption_on_sections_holds : AsmSec := by
  intro hFL hGQ hML hRS hRaw hQL Wp Wq _ _ _ _ _ _ P Bs hPl hk hsec
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hPl
  obtain ⟨e, he, hQQ⟩ := hGQ Wp Wq P Bs hPl hk hsec X
  refine ⟨e, he, fun Dc Φ hΦ Y a b ρ => ?_⟩
  apply Subtype.ext
  funext q
  have hLsm := hRaw Wp Wq P Bs hPl hk e he Dc _ (hQL Wp Wq P Bs hPl hk Dc Φ hΦ Y a b) ρ
  rw [toSm_of_mem P hLsm q]
  obtain ⟨Φt, V, hV, hagree⟩ := hFL Wp Wq P Bs hPl hk X Dc Φ hΦ q
  have h1 : rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ q =
      rawR P Bs.μsec e ((X.t (Y : ℂ) a b Φt : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
        Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q := by
    unfold rawR
    rw [((hagree q.1.2 (mem_of_mem_nhds hV)).2 (Y : ℂ) a b).symm]
  rw [h1, ← toSm_of_mem P (hRS Wp Wq P Bs hPl hk e he (X.t (Y : ℂ) a b Φt) ρ) q]
  show (trR P Bs e (X.t (Y : ℂ) a b Φt) ρ : MA.Qp P.r P.TT → ℂ) q = _
  rw [hQQ Φt (Y : ℂ) a b]
  refine hML P (trR P Bs e Φt) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) q.1.1 (interior V) isOpen_interior
    (fun ρ' q' hq'c hq'V => ?_) (Y : ℂ) a b ρ q rfl (mem_interior_iff_mem_nhds.2 hV)
  show (MA.toSm P (rawR P Bs.μsec e (Φt : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ') : MA.Qp P.r P.TT → ℂ) q' =
    (MA.toSm P (rawR P Bs.μsec e Φ ρ') : MA.Qp P.r P.TT → ℂ) q'
  rw [toSm_of_mem P (hRS Wp Wq P Bs hPl hk e he Φt ρ') q',
    toSm_of_mem P (hRaw Wp Wq P Bs hPl hk e he Dc Φ hΦ ρ') q']
  unfold rawR
  rw [hq'c, (hagree q'.1.2 (interior_subset hq'V)).1]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermVectorIdentity
theorem Formalism.FourierDecayAlt.P.sign_permutation_identity : Formalism.FourierDecayAlt.C3.SignE :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.sign_permutation_identity

theorem Formalism.FourierDecayAlt.P.derivative_leading_zb : Formalism.FourierDecayAlt.C3.DleadZb :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb

theorem Formalism.FourierDecayAlt.P.minors_first_case : Formalism.FourierDecayAlt.C3.MinorsFirstCase :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.minors_first_case

theorem Formalism.FourierDecayAlt.P.third_polynomial_expansion : Formalism.FourierDecayAlt.C3.MinorsThirdCase :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.third_polynomial_expansion

theorem Formalism.FourierDecayAlt.P.first_peeling_identity : Formalism.FourierDecayAlt.C3.PeelingOmittedColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.first_peeling_identity

theorem Formalism.FourierDecayAlt.P.second_peeling_identity : Formalism.FourierDecayAlt.C3.PeelingCovector :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.second_peeling_identity

theorem Formalism.FourierDecayAlt.P.third_peeling_identity : Formalism.FourierDecayAlt.C3.PeelingDualColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.third_peeling_identity

theorem Formalism.FourierDecayAlt.P.first_expansion_identity : Formalism.FourierDecayAlt.C3.ExpansionOmittedColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.first_expansion_identity

theorem Formalism.FourierDecayAlt.P.second_expansion_identity : Formalism.FourierDecayAlt.C3.ExpansionDualColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.second_expansion_identity

theorem Formalism.FourierDecayAlt.P.column_indicator_expansion : Formalism.FourierDecayAlt.C3.ExpansionCovector :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.column_indicator_expansion

theorem Formalism.FourierDecayAlt.P.chain_first_identity : Formalism.FourierDecayAlt.C3.LastColumnChain :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.chain_first_identity

theorem Formalism.FourierDecayAlt.P.leading_term_identity : Formalism.FourierDecayAlt.C3.LeadAA :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_identity

theorem Formalism.FourierDecayAlt.P.leading_term_vector_identity : Formalism.FourierDecayAlt.C3.LeadAAv :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_vector_identity

theorem Formalism.FourierDecayAlt.P.dpsi_is_derivation : Formalism.FourierDecayAlt.C3.DpsiDerivation :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.dpsi_is_derivation

theorem Formalism.FourierDecayAlt.P.isotropicNormalFormFull_statement : Formalism.FourierDecayAlt.C3.IsotropicNormalFormFull :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.isotropicNormalFormFull_statement
end
