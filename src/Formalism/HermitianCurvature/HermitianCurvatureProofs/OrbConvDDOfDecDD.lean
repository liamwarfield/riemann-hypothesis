module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbConvDDOfDecDD
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CkOnZeroOfContOn
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem gv_closed (k r : ℕ) : IsClosed (B.GV k r) := by
  show IsClosed {g : B.Mat k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem ckOn_zero_of_contOn {k r : ℕ} (f : Mx k r → ℂ) (hf : ContinuousOn f (B.GV k r)) :
    B.CkOn ((0 : ℕ) : ℕ∞) (B.GV k r) (fun g => f g • (1 : ℂ →L[ℂ] ℂ)) := by
  have hcl := gv_closed k r
  haveI : NormalSpace (B.Mat k r) :=
    inferInstanceAs (NormalSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨g, hg⟩ := ContinuousMap.exists_extension' hcl.isClosedEmbedding_subtypeVal
    (⟨fun x : B.GV k r => f x, hf.restrict⟩ : C(B.GV k r, ℂ))
  intro g₀ hg₀
  refine ⟨Set.univ, fun y => g y • (1 : ℂ →L[ℂ] ℂ), isOpen_univ, Set.mem_univ _, ?_, fun y _ hy => ?_⟩
  · show ContDiffOn ℝ 0 _ _
    rw [contDiffOn_zero]
    exact (g.continuous.smul continuous_const).continuousOn
  · exact congrArg (fun c : ℂ => c • (1 : ℂ →L[ℂ] ℂ)) (congrFun hg ⟨y, hy⟩).symm

end Formalism.FourierDecayAlt.P.S3dx4
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem ag_nonneg (k r : ℕ) : 0 ≤ AG k r := by unfold AG; positivity

theorem gap4 {k r : ℕ} {h : ℝ} (hG : GapOK k r h) :
    9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 3 ≤ aOf r h := hG.2.2.2

theorem thr_of_gapOK {k r : ℕ} {h : ℝ} (hG : GapOK k r h) : JF.TransportedAlt k r (aOf r h) 0 := by
  have h4' := gap4 hG
  have h4 : 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < aOf r h := by
    linarith [ag_nonneg k r]
  unfold JF.TransportedAlt
  have hpos : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
  rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hpos]
  calc ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * (9 * ((r : ℝ) + 1))
      = 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by ring
    _ < aOf r h := h4

theorem aOf_pos_of_gapOK {k r : ℕ} {h : ℝ} (hG : GapOK k r h) : 0 < aOf r h := by
  have h4 := gap4 hG
  have h5 := ag_nonneg k r
  have : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  linarith

theorem rho_triv {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r)
    (F : B.Mat k r → (ℂ →L[ℂ] ℂ)) (g : B.Mat k r) : B.rho (triv D) p F g = F (B.sgs p g) := by
  ext
  simp [B.rho, triv]

theorem rpow_bound (t C a : ℝ) (ht : 0 ≤ t) (ha : a ≠ 0) : t ^ a * (C * t ^ (-a)) ≤ |C| := by
  rcases ht.lt_or_eq with h | h
  · rw [mul_left_comm, ← Real.rpow_add h, add_neg_cancel, Real.rpow_zero, mul_one]
    exact le_abs_self C
  · subst h
    rw [Real.zero_rpow ha, zero_mul]
    exact abs_nonneg C

theorem orbConvDD_of_decDD (hD : DecDD) : OrbConvDD := by
  intro hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS hS' x hx y hy
  obtain ⟨C, hC⟩ :=
    hD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS y hy x hx
  have hG : GapOK k r h := hS.2.2.2.1
  have hσ : PI.UpqRep.IsDSHpk k r ε lam σ := hS.2.1
  have hThr : JF.TransportedAlt k r (aOf r h) 0 := thr_of_gapOK hG
  have ha : aOf r h ≠ 0 := (aOf_pos_of_gapOK hG).ne'
  let f : Mx k r → ℂ := fun g => ⟪x, σ g y⟫_ℂ
  have hfc : ContinuousOn f (B.GV k r) :=
    ContinuousOn.inner continuousOn_const (sigma_contOn hσ y)
  let F : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun g => f g • (1 : ℂ →L[ℂ] ℂ)
  have hCC : B.InCC (aOf r h) 0 F := by
    refine ⟨|C|, ckOn_zero_of_contOn f hfc, ?_⟩
    intro uu vv _ _ hlen g hg
    have hu : uu = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hv : vv = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu; subst hv
    show B.gN g ^ aOf r h * ‖F g‖ ≤ |C|
    have hF : ‖F g‖ = ‖f g‖ := by simp [F]
    rw [hF]
    have hgN : 0 ≤ B.gN g := Real.sqrt_nonneg _
    calc B.gN g ^ aOf r h * ‖f g‖ ≤ B.gN g ^ aOf r h * (C * B.gN g ^ (-aOf r h)) :=
          mul_le_mul_of_nonneg_left (hC g hg) (Real.rpow_nonneg hgN _)
      _ ≤ |C| := rpow_bound _ _ _ hgN ha
  have hJC := Formalism.FourierDecayAlt.P.bessel_integral_converges k r ℂ ℂ (triv D) (aOf r h) F hThr hCC
  have hJD := Formalism.FourierDecayAlt.P.bessel_integral_domain k r ℂ ℂ (triv D) (aOf r h) 0 F hThr hCC
  have hnorm : ∀ p γ, ‖⟪x, σ (B.sgs p γ) y⟫_ℂ‖ = ‖B.rho (triv D) p F γ‖ := by
    intro p γ
    rw [rho_triv]
    simp [F, f]
  have happ : ∀ p γ, ⟪x, σ (B.sgs p γ) y⟫_ℂ = (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) (B.rho (triv D) p F γ) := by
    intro p γ
    rw [rho_triv]
    simp [F, f]
  refine ⟨fun γ hγ => ?_, fun K hK hKO => ?_⟩
  · obtain ⟨b, hb, hbd⟩ := hJC.2 {γ} isCompact_singleton (Set.singleton_subset_iff.mpr hγ)
    have hmeas : AEStronglyMeasurable (fun p => B.rho (triv D) p F γ) D.μSS :=
      hJD.1 [] [] (by simp) (by simp) (by simp) γ hγ
    have hmeas' : AEStronglyMeasurable (fun p => ⟪x, σ (B.sgs p γ) y⟫_ℂ) D.μSS := by
      have := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).continuous.comp_aestronglyMeasurable hmeas
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      exact (happ p γ).symm
    refine Integrable.mono' hb hmeas' ?_
    filter_upwards [hbd γ rfl] with p hp
    rw [hnorm]
    exact hp
  · obtain ⟨b, hb, hbd⟩ := hJC.2 K hK hKO
    refine ⟨b, hb, fun γ hγ => ?_⟩
    filter_upwards [hbd γ hγ] with p hp
    rw [hnorm]
    exact hp

end Formalism.FourierDecayAlt.P.S3dx4
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddScalBound
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddScal
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

def phiR (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : ℂ :=
  Formalism.QuantumDeterminants.Dmin k r z z' g ⟨r, by omega⟩ / Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1))

def phiD (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : ℂ :=
  Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1)) / (starRingEnd ℂ) (Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1)))

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def ScalOK (D : B.RealPlaceData k r Wp Wq) (Bg : ℝ) (φ : B.Mat k r → ℂ) : Prop :=
  B.CkOn ⊤ (B.GPos D) φ ∧
  ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ C : ℝ, ∀ u w : List (B.Mat k r),
    (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
    ∀ g ∈ B.GV k r, ε ≤ Formalism.QuantumDeterminants.Gf k r D.z D.z' g → ‖B.dLR u w φ g‖ ≤ C * B.gN g ^ (Bg * m)

end

def JAScalBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Bg : ℝ), K * ((r : ℝ) + 1) ≤ Bg →
    ScalOK D Bg (phiR k r D.z D.z') ∧ ScalOK D Bg (phiD k r D.z D.z')

def JAScalConj : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Bg : ℝ) (φ : B.Mat k r → ℂ),
    ScalOK D Bg φ → ScalOK D Bg (fun g => (starRingEnd ℂ) (φ g))

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def regE (D : B.RealPlaceData k r Wp Wq) (ε : ℝ) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ ε ≤ Gf k r D.z D.z' g}

theorem regE_sub (D : B.RealPlaceData k r Wp Wq) (ε : ℝ) : regE D ε ⊆ B.GV k r := fun _ hg => hg.1

theorem scal_bound_of_ubl (D : B.RealPlaceData k r Wp Wq) (φ : B.Mat k r → ℂ) (e γ : ℕ) (Bg : ℝ)
    (hBg : (e : ℝ) + γ ≤ Bg) (ε : ℝ)
    (h0 : ∃ C0 : ℝ, ∀ g ∈ regE D ε, ‖φ g‖ ≤ C0) (hU : ∀ n : ℕ, UBL φ (regE D ε) n e γ) (m : ℕ) :
    ∃ C : ℝ, ∀ u w : List (B.Mat k r),
      (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g → ‖B.dLR u w φ g‖ ≤ C * B.gN g ^ (Bg * m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    obtain ⟨C0, hC0⟩ := h0
    refine ⟨C0, fun u w _ _ hl g hg hgε => ?_⟩
    have hu : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu hw
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    exact hC0 g ⟨hg, hgε⟩
  · obtain ⟨⟨C, hC0, hUB⟩, -⟩ := hU m
    refine ⟨C, fun u w hu hw hl g hg hgε => ?_⟩
    have hA : admitted m (wL u ++ wR w) := ⟨u, w, hu, hw, hl, rfl⟩
    have hb := hUB _ hA g ⟨hg, hgε⟩
    rw [dLR_eq]
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    have h1 : 1 ≤ B.gN g := gN_ge_one hg
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le h1
    rw [len_LR]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hl' : ((u.length + w.length : ℕ) : ℝ) ≤ m := by exact_mod_cast hl
    have he : (0 : ℝ) ≤ e := Nat.cast_nonneg _
    have hγ : (0 : ℝ) ≤ γ := Nat.cast_nonneg _
    push_cast at hl' ⊢
    nlinarith [mul_le_mul_of_nonneg_left hl' hγ, mul_le_mul_of_nonneg_left hm1 he,
      mul_le_mul_of_nonneg_right hBg (by linarith : (0 : ℝ) ≤ m)]

theorem dlast_pos (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) {g : B.Mat k r} (hg : ε ≤ Gf k r D.z D.z' g) :
    ε ≤ Complex.normSq (Dmin k r D.z D.z' g (Fin.last (r + 1))) :=
  Formalism.FourierDecayAlt.P.gram_function_last_minor k r D.z D.z' D.T_pos.le D.T'_pos.le g ε hg

theorem dlast_ne (D : B.RealPlaceData k r Wp Wq) {g : B.Mat k r} (hg : g ∈ B.GPos D) :
    Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0 := by
  intro h
  have := dlast_pos D hg.2 (le_refl _)
  rw [h, map_zero] at this
  linarith [hg.2]

theorem open_dlast (z z' : Fin (2 * r + k + 1) → ℂ) :
    IsOpen {g : B.Mat k r | Dmin k r z z' g (Fin.last (r + 1)) ≠ 0} :=
  isOpen_ne_fun (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin z z' _).continuous continuous_const

theorem ckOn_phiR (D : B.RealPlaceData k r Wp Wq) : B.CkOn ⊤ (B.GPos D) (phiR k r D.z D.z') := by
  intro g₀ hg₀
  refine ⟨{g : B.Mat k r | Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0}, phiR k r D.z D.z', open_dlast D.z D.z',
    dlast_ne D hg₀, ?_, fun _ _ _ => rfl⟩
  have h0 := Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin (k := k) (r := r) D.z D.z' ⟨r, by omega⟩
  have h1 := Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin (k := k) (r := r) D.z D.z' (Fin.last (r + 1))
  refine (h0.contDiffOn.mul (h1.contDiffOn.inv (fun x hx => hx))).congr (fun x _ => ?_)
  simp [phiR, div_eq_mul_inv]

theorem ckOn_phiD (D : B.RealPlaceData k r Wp Wq) : B.CkOn ⊤ (B.GPos D) (phiD k r D.z D.z') := by
  intro g₀ hg₀
  refine ⟨{g : B.Mat k r | Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0}, phiD k r D.z D.z', open_dlast D.z D.z',
    dlast_ne D hg₀, ?_, fun _ _ _ => rfl⟩
  have h1 := Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin (k := k) (r := r) D.z D.z' (Fin.last (r + 1))
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => (starRingEnd ℂ) (Dmin k r D.z D.z' g (Fin.last (r + 1)))) :=
    Complex.conjCLE.contDiff.comp h1
  refine (h1.contDiffOn.mul (h2.contDiffOn.inv (fun x hx => by simpa using hx))).congr (fun x _ => ?_)
  simp [phiD, div_eq_mul_inv]

theorem phiR_le (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) :
    ∃ C0 : ℝ, ∀ g ∈ regE D ε, ‖phiR k r D.z D.z' g‖ ≤ C0 := by
  set T := Tz k r D.z * Tz k r D.z' with hT
  have hT0 : 0 < T := mul_pos D.T_pos D.T'_pos
  refine ⟨1 + 1 / T, fun g hg => ?_⟩
  have hG := hg.2
  have h1 := dlast_pos D hε hG
  have hpos : 0 < Complex.normSq (Dmin k r D.z D.z' g (Fin.last (r + 1))) := lt_of_lt_of_le hε h1
  unfold Gf at hG
  set a := Complex.normSq (Dmin k r D.z D.z' g ⟨r, by omega⟩)
  set b := Complex.normSq (Dmin k r D.z D.z' g (Fin.last (r + 1)))
  have hsq : ‖phiR k r D.z D.z' g‖ ^ 2 = a / b := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [phiR, Complex.normSq_div]
    rfl
  have hle : a / b ≤ 1 / T := by
    rw [div_le_div_iff₀ hpos hT0]
    nlinarith
  have hx := norm_nonneg (phiR k r D.z D.z' g)
  nlinarith [sq_nonneg (‖phiR k r D.z D.z' g‖ - 1)]

theorem phiD_le (D : B.RealPlaceData k r Wp Wq) (ε : ℝ) :
    ∃ C0 : ℝ, ∀ g ∈ regE D ε, ‖phiD k r D.z D.z' g‖ ≤ C0 := by
  refine ⟨1, fun g _ => ?_⟩
  simp only [phiD, norm_div, Complex.norm_conj]
  exact div_self_le_one _

theorem ubl_phiR (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    UBL (phiR k r D.z D.z') (regE D ε) n r (r + 1) := by
  have hP0 : U.IsPolyDeg r (fun g : B.Mat k r => Dmin k r D.z D.z' g ⟨r, by omega⟩) :=
    Formalism.FourierDecayAlt.P.minor_polynomial_property k r D.z D.z' ⟨r, by omega⟩
  have hP1 : U.IsPolyDeg (r + 1) (fun g : B.Mat k r => Dmin k r D.z D.z' g (Fin.last (r + 1))) := by
    have := Formalism.FourierDecayAlt.P.minor_polynomial_property k r D.z D.z' (Fin.last (r + 1))
    simpa using this
  have ha := ubl_poly hP0 (regE D ε) (regE_sub D ε) n (r + 1)
  have hb := ubl_invpow hP1 (regE_sub D ε) hε (fun g hg => dlast_pos D hε hg.2) 1 n
  have hm := ubl_mul (regE_sub D ε) ha hb
  have e : phiR k r D.z D.z' = fun g => Dmin k r D.z D.z' g ⟨r, by omega⟩ *
      (Dmin k r D.z D.z' g (Fin.last (r + 1)))⁻¹ ^ 1 := by
    funext g; simp [phiR, div_eq_mul_inv]
  rw [e]
  simpa using hm

theorem ubl_phiD (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    UBL (phiD k r D.z D.z') (regE D ε) n (r + 1) (r + 1) := by
  have hP1 : U.IsPolyDeg (r + 1) (fun g : B.Mat k r => Dmin k r D.z D.z' g (Fin.last (r + 1))) := by
    have := Formalism.FourierDecayAlt.P.minor_polynomial_property k r D.z D.z' (Fin.last (r + 1))
    simpa using this
  have hP2 := Formalism.FourierDecayAlt.P.CutMP.jdh_pd_star hP1
  have ha := ubl_poly hP1 (regE D ε) (regE_sub D ε) n (r + 1)
  have hb := ubl_invpow hP2 (regE_sub D ε) hε
    (fun g hg => by simpa [Complex.star_def] using dlast_pos D hε hg.2) 1 n
  have hm := ubl_mul (regE_sub D ε) ha hb
  have e : phiD k r D.z D.z' = fun g => Dmin k r D.z D.z' g (Fin.last (r + 1)) *
      (star (Dmin k r D.z D.z' g (Fin.last (r + 1))))⁻¹ ^ 1 := by
    funext g; simp [phiD, div_eq_mul_inv]
  rw [e]
  simpa using hm

end

theorem scalar_transfer_bound_holds : JAScalBound := by
  refine ⟨2, by norm_num, ?_⟩
  intro k r Wp Wq _ _ _ _ D Bg hBg
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  refine ⟨⟨ckOn_phiR D, fun ε hε m => ?_⟩, ⟨ckOn_phiD D, fun ε hε m => ?_⟩⟩
  · exact scal_bound_of_ubl D _ r (r + 1) Bg (by push_cast; linarith) ε (phiR_le D hε)
      (fun n => ubl_phiR D hε n) m
  · exact scal_bound_of_ubl D _ (r + 1) (r + 1) Bg (by push_cast; linarith) ε (phiD_le D ε)
      (fun n => ubl_phiD D hε n) m

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.XFibreOfParts
open Matrix Finset
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.TL

namespace TLC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

private theorem herm_swap_eq_zero_of_eq_zero {k r : ℕ} (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) w v = star (herm (Hpk k r) v w) := by
  have hH : ∀ i j : Fin (2 * r + k + 1), star (Hpk k r i j) = Hpk k r j i := by
    intro i j
    simp only [Hpk, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | norm_num
  simp only [herm, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH]
  ring

private theorem herm_Hpk_frame_sum_of_orthogonal {z' y u : Fin (2 * r + k + 1) → ℂ} {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hB0 : IsFrameOf k r [z'] B0) (a : ℂ) (hu : inWb k r u)
    (huz : herm (Hpk k r) u z' = 0) :
    herm (Hpk k r) u (∑ j, (a * herm (Hpk k r) y (B0 j)) • B0 j) = star a * herm (Hpk k r) u y := by
  have hdec := HermitianFormSums.complete0 hz' (HermitianFormSums.hzz hT') hB0 hu huz
  have h1 : herm (Hpk k r) u y = ∑ j, herm (Hpk k r) u (B0 j) * herm (Hpk k r) (B0 j) y := by
    conv_lhs => rw [hdec]
    exact HermitianFormSums.herm_lsum _ _ _ _ _
  rw [h1, HermitianFormSums.herm_rsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [herm_swap_eq_zero_of_eq_zero y (B0 j), star_mul']
  ring

theorem xf_perp {z' y u : Fin (2 * r + k + 1) → ℂ} {B0 : Fin k → Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z')
    (hT' : 0 < Tz k r z') (hB0 : IsFrameOf k r [z'] B0) (β : Fin k → ℂ) (a : ℂ)
    (hβ : ∀ j, β j = a * herm (Hpk k r) y (B0 j)) (hu : inWb k r u) (huz : herm (Hpk k r) u z' = 0)
    (huy : herm (Hpk k r) u y = 0) : herm (Hpk k r) u (∑ j, β j • B0 j) = 0 := by
  rw [show (∑ j, β j • B0 j) = ∑ j, (a * herm (Hpk k r) y (B0 j)) • B0 j from
    Finset.sum_congr rfl fun j _ => by rw [hβ j], herm_Hpk_frame_sum_of_orthogonal hz' hT' hB0 a hu huz, huy, mul_zero]

theorem xf_rad (hCell : CellVals) (hOm : OmFacts) (hCapF : CapVFrame) {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (Bs : B.RealPlaceData k r Wp Wq) (X : ActualOps k r Bs.z Bs.z' Bs.π Bs.π')
    {B0 : Fin k → Fin (2 * r + k + 1) → ℂ} (hB0 : IsFrameOf k r [Bs.z'] B0) (Y : ℂ)
    (Φ : RadSp k r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin r → ℂ) × Mx k r) (hx : x ∈ DomR k r Bs.z Bs.z') :
    (X.t Y 1 1 Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = ((GGl k r Bs.z Bs.z' x.2 : ℝ) : ℂ) •
      xFib Bs B0 (Y + ((k : ℂ) - 2) / 2) (wCell k r (Fin.last r) x.1 * x.2) ((Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2) := by
  have hx' := hx
  obtain ⟨-, hgl, hGG⟩ := hx'
  obtain ⟨hbig, -⟩ := hCell k r Wp Wq Bs x hx
  obtain ⟨-, hsq, -, hcell⟩ := hOm k r Wp Wq Bs B0 hB0
  obtain ⟨Bs', -, -, hF, -⟩ := Q.LieAlgebraWeightVectors.geom_package Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos hgl hGG.ne'
  have hν1 : C6.sq2 (C6.unitOf (Tz k r Bs.z') (Gf k r Bs.z Bs.z' (wCell k r (Fin.last r) x.1 * x.2))
      (omC Bs B0 (wCell k r (Fin.last r) x.1 * x.2))) = 1 :=
    AdmissibleLieWords.sq2_unitOf_eq_one_of_sq2_eq_div Bs.T'_pos hbig.2.1 (hsq _ hbig.1)
  have hF2 : IsFrameOf k r [Bs.z', ∑ j, C6.unitOf (Tz k r Bs.z') (Gf k r Bs.z Bs.z' (wCell k r (Fin.last r) x.1 * x.2))
      (omC Bs B0 (wCell k r (Fin.last r) x.1 * x.2)) j • B0 j] Bs' := by
    refine ⟨hF.1, hF.2.1, fun i v hv => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hF.2.2 i _ (by simp)
    · refine xf_perp Bs.z'_mem Bs.T'_pos hB0 _
        (((Real.sqrt (Tz k r Bs.z' / Gf k r Bs.z Bs.z' (wCell k r (Fin.last r) x.1 * x.2)) : ℝ) : ℂ) *
          conj (∏ a, x.1 a)) (fun j => ?_) (hF.1 i) (hF.2.2 i Bs.z' (by simp))
          (hF.2.2 i (x.2⁻¹ *ᵥ Bs.z) (by simp))
      simp only [C6.unitOf, Pi.smul_apply, smul_eq_mul, hcell x hx j, mul_assoc]
  have hcap := hCapF Wq k r Bs.z' Bs.π' B0 Bs' _ Bs.k_pos Bs.z'_mem Bs.T'_pos ⟨Bs.π'_rep, Bs.π'_cont⟩ hB0 hν1 hF2
  have hgl2 := (frame_general_linear Wq k r (k - 1) Bs.z' Bs.π' Bs' ⟨Bs.π'_rep, Bs.π'_cont⟩ (HermitianFormSums.frame_sub hF2)).2
  have hne : ((GGl k r Bs.z Bs.z' x.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hGG.ne'
  ext v
  have hfn := congrArg (fun T : Wq →L[ℂ] Wp => T v) (X.fn_apply 5 (X.t Y 1 1 Φ) x hx)
  have ht := P5.Kfp.diagonal_transfer_action X Bs.z_mem Bs.z'_mem Bs.π'_rep Bs.π'_cont (c := x.1) (g := x.2) hx Bs' hF Y Φ v
  simp only [Module.End.mul_apply] at ht
  simp only [_root_.smul_apply, fnVal] at hfn
  rw [ht] at hfn
  simp only [xFib, _root_.smul_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, hcap, hgl2]
  rw [hfn, smul_smul, mul_inv_cancel₀ hne, one_smul]

section fib

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem xf_capV_sum (π' : Mx k r → (Wq →L[ℂ] Wq)) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (ν : Fin k → ℂ) :
    capV π' B0 w ν = ∑ i : Fin k, ∑ j : Fin k, ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * star (ν i) * ν j) •
      LinearMap.toContinuousLinearMap (qminor (EB π' B0) (skip1 i) (skip1 j) w : Module.End ℂ Wq) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [capV, Q.chatA, map_sum, map_smul, Pi.star_apply]

theorem xf_capV_cd (π' : Mx k r → (Wq →L[ℂ] Wq)) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) :
    ContDiff ℝ ∞ (fun ν : Fin k → ℂ => capV π' B0 w ν) := by
  rw [show (fun ν : Fin k → ℂ => capV π' B0 w ν) = fun ν => ∑ i : Fin k, ∑ j : Fin k,
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * star (ν i) * ν j) •
        LinearMap.toContinuousLinearMap (qminor (EB π' B0) (skip1 i) (skip1 j) w : Module.End ℂ Wq) from
    funext (xf_capV_sum π' B0 w)]
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  have hs : ContDiff ℝ ∞ (fun ν : Fin k → ℂ => star (ν i)) :=
    Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) i)
  exact ((contDiff_const.mul hs).mul (contDiff_apply ℝ (fun _ => ℂ) j)).smul contDiff_const

def xfPi (π' : Mx k r → (Wq →L[ℂ] Wq)) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (ν : Fin k → ℂ) :
    C6.EndH Wp Wq :=
  (ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (capV π' B0 w ν)

theorem xf_Pi_cd (π' : Mx k r → (Wq →L[ℂ] Wq)) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) :
    ContDiff ℝ ∞ (xfPi (Wp := Wp) π' B0 w) := by
  exact (((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip).restrictScalars ℝ).contDiff.comp (xf_capV_cd π' B0 w)

private theorem contDiff_of_isPolyDeg' {k r κ : ℕ} {P : B.Mat k r → ℂ} (h : U.IsPolyDeg κ P) : ContDiff ℝ ∞ P := by
  obtain ⟨q, -, hq⟩ := h
  have hP : P = fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))) q := funext hq
  subst hP
  clear hq
  induction q using MvPolynomial.induction_on
  next a =>
    simp only [MvPolynomial.eval_C]
    exact contDiff_const
  next p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  next p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    rcases i with ⟨a, b⟩ | ⟨a, b⟩
    · exact JCx1.contDiff_entry a b
    · exact Complex.conjCLE.contDiff.comp (JCx1.contDiff_entry a b)

theorem xf_bound (hOm : OmFacts) (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB0 : IsFrameOf k r [Bs.z'] B0) (w : ℂ) : C6.FibBound Bs (xFib Bs B0 w) := by
  obtain ⟨hom, hsq, -, -⟩ := hOm k r Wp Wq Bs B0 hB0
  have hGc : ContDiff ℝ ∞ (fun g : B.Mat k r => ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (JCx1.contDiff_Gf Bs.z Bs.z')
  have hoc : ∀ a, ContDiff ℝ ∞ (fun g => omC Bs B0 g a) := fun a => contDiff_of_isPolyDeg' (hom a)
  refine ⟨fun g₀ hg₀ => ?_, fun ε hε i => ?_⟩
  · refine ⟨{g | Gf k r Bs.z Bs.z' g₀ / 2 < Gf k r Bs.z Bs.z' g},
      fun g => xfPi Bs.π' B0 w (AdmissibleLieWords.utv (Gf k r Bs.z Bs.z' g₀) (Tz k r Bs.z') (Gf k r Bs.z Bs.z') (omC Bs B0) g),
      isOpen_lt continuous_const (JCx1.contDiff_Gf Bs.z Bs.z').continuous, half_lt_self hg₀.2, ?_, fun g hg _ => ?_⟩
    · exact ((xf_Pi_cd Bs.π' B0 w).comp (AdmissibleLieWords.utv_cd (T := Tz k r Bs.z') hg₀.2 hGc hoc)).contDiffOn
    · exact congrArg (xfPi (Wp := Wp) Bs.π' B0 w) (AdmissibleLieWords.utv_eq hg₀.2 Bs.T'_pos _ _ hg)
  · exact fibre_cost_estimate k r k k (omC Bs B0) (omC Bs B0) (Gf k r Bs.z Bs.z') (Tz k r Bs.z') (Tz k r Bs.z')
      (C6.EndH Wp Wq) (fun p => xfPi Bs.π' B0 w p.1) Set.univ hom hom (gram_function_polynomial k r Bs.z Bs.z')
      Bs.T'_pos Bs.T'_pos hsq hsq isOpen_univ (Set.subset_univ _)
      ((xf_Pi_cd Bs.π' B0 w).comp contDiff_fst).contDiffOn ε hε i

theorem xf_equiv (hOm : OmFacts) (hCapE : CapVEquiv) (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB0 : IsFrameOf k r [Bs.z'] B0) (w : ℂ) :
    ∀ p, Bs.inSS p → ∀ g ∈ C6.domL Bs ∅, ∀ J : Wq →L[ℂ] Wp,
      xFib Bs B0 w g ((Bs.π (Matrix.of p.1.1)).comp (J.comp (Bs.π' (Matrix.of p.2.1)⁻¹))) =
        (Bs.π (Matrix.of p.1.1)).comp ((xFib Bs B0 w (B.sgs p g) J).comp (Bs.π' (Matrix.of p.2.1)⁻¹)) := by
  obtain ⟨-, hsq, hcov, -⟩ := hOm k r Wp Wq Bs B0 hB0
  intro p hp g hg J
  have hGf : Gf k r Bs.z Bs.z' (B.sgs p g) = Gf k r Bs.z Bs.z' g := JCx1.needs.gf_sgs Bs hp g
  have hsum : ∀ (c : ℂ) (v : Fin k → ℂ), ∑ j, (c • v) j • B0 j = c • ∑ j, v j • B0 j := by
    intro c v
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have hE := hCapE Wq k r Bs.z' Bs.π' B0 (C6.unitOf (Tz k r Bs.z') (Gf k r Bs.z Bs.z' g) (omC Bs B0 g))
    (C6.unitOf (Tz k r Bs.z') (Gf k r Bs.z Bs.z' (B.sgs p g)) (omC Bs B0 (B.sgs p g))) (Matrix.of p.2.1)
    Bs.k_pos Bs.z'_mem Bs.T'_pos ⟨Bs.π'_rep, Bs.π'_cont⟩ hB0
    (AdmissibleLieWords.sq2_unitOf_eq_one_of_sq2_eq_div Bs.T'_pos hg.2.1 (hsq g hg.1)) hp.2.2.1
    (by simp only [C6.unitOf, hsum, hGf, hcov p hp g hg, Matrix.mulVec_smul]) w
  ext v
  have hv := congrArg (fun T : Wq →L[ℂ] Wq => T v) hE
  simp only [ContinuousLinearMap.comp_apply] at hv
  simp only [xFib, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, hv]

end fib

end TLC

private theorem herm_Hpk_swap {k r : ℕ} (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) w v = star (herm (Hpk k r) v w) := by
  have hH : ∀ i j : Fin (2 * r + k + 1), star (Hpk k r i j) = Hpk k r j i := by
    intro i j
    simp only [Hpk, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | norm_num
  simp only [herm, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH]
  ring

private theorem exists_isFrameOf_singleton_of_Tz_pos {k r : ℕ} {z' : Fin (2 * r + k + 1) → ℂ} (hk : 1 ≤ k) (hz' : inWb k r z')
    (hT' : 0 < Tz k r z') : ∃ B0 : Fin k → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z'] B0 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hbw : ∀ i : Fin (2 * r + (n + 1) + 1), r ≤ i.val → i.val ≤ r + (n + 1) → inWb (n + 1) r (bvec i) := by
    intro i h1 h2 j hj
    simp only [bvec, Pi.single_apply]
    split_ifs with h
    · subst h
      omega
    · rfl
  obtain ⟨a, ha, hind⟩ : ∃ a, inWb (n + 1) r a ∧ ∀ c : ℂ, a ≠ c • z' := by
    obtain ⟨i0, hi0⟩ : ∃ i : Fin (2 * r + (n + 1) + 1), i.val = r := ⟨⟨r, by omega⟩, rfl⟩
    obtain ⟨i1, hi1⟩ : ∃ i : Fin (2 * r + (n + 1) + 1), i.val = r + 1 := ⟨⟨r + 1, by omega⟩, rfl⟩
    have hne : i0 ≠ i1 := fun h => by rw [h] at hi0; omega
    by_cases h : ∀ c : ℂ, bvec i0 ≠ c • z'
    · exact ⟨_, hbw i0 (by omega) (by omega), h⟩
    · simp only [ne_eq, not_forall, not_not] at h
      obtain ⟨c0, h0⟩ := h
      refine ⟨_, hbw i1 (by omega) (by omega), fun c hc => ?_⟩
      have e0 := congrFun h0 i0
      have e1 := congrFun hc i0
      have e2 := congrFun hc i1
      simp only [bvec, Pi.single_apply, Pi.smul_apply, smul_eq_mul, if_neg hne] at e0 e1 e2
      have hz0 : z' i0 ≠ 0 := fun h => by rw [h, mul_zero] at e0; exact one_ne_zero e0
      have hc0 : c = 0 := (mul_eq_zero.mp e1.symm).resolve_right hz0
      rw [hc0, zero_mul] at e2
      exact one_ne_zero e2
  obtain ⟨e, he, hez, hee, -⟩ := Q.LieAlgebraWeightVectors.exists_unit hz' hT' ha hind
  obtain ⟨Bs, hBs⟩ := Q.LieAlgebraWeightVectors.exists_frame he hz' hT'
  refine ⟨Fin.cons e (fun i => Bs (Fin.cast (by omega) i)), fun i => ?_, fun i j => ?_, fun i v hv => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simpa using he
    · simpa using hBs.1 _
  · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hee
    · simp only [Fin.cons_zero, Fin.cons_succ]
      rw [herm_Hpk_swap _ e, hBs.2.2 _ e (by simp), star_zero, if_neg (Fin.succ_ne_zero j).symm]
    · simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hBs.2.2 _ e (by simp), if_neg (Fin.succ_ne_zero i)]
    · simp only [Fin.cons_succ]
      rw [hBs.2.1]
      simp [Fin.ext_iff]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hez
    · simpa using hBs.2.2 _ _ (by simp)

theorem x_fibre_of_parts : TL.XFibOfParts := by
  intro hCell hOm hCapF hCapE Wp Wq _ _ _ _ _ _ P Bs X
  obtain ⟨B0, hB0⟩ := exists_isFrameOf_singleton_of_Tz_pos Bs.k_pos Bs.z'_mem Bs.T'_pos
  exact ⟨B0, hB0, fun Y => ⟨TLC.xf_bound hOm Bs hB0 _, TLC.xf_equiv hOm hCapE Bs hB0 _,
    fun Φ x hx => TLC.xf_rad hCell hOm hCapF Bs X hB0 Y Φ x hx⟩⟩

end Formalism.FourierDecayAlt.P
end
end
