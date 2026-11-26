module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EventuallyLevelPointMemOpen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLTorus
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolyLiftOfSmoothComm
namespace GlobalTheory.HatNF.SmoothLift

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF MeasureTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem opApply_JF (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (Θ : B.DiffOp k r Wp Wq) (ho : B.opOrder Θ ≤ m) (hT : TransportedAlt k r A m) (hF : B.InCC A m F)
    (g : B.Mat k r) (hg : g ∈ Om k r D.z D.z')
    (hC : ∀ p, D.inSS p → opApply Θ (rho D p F) g = rho D p (opApply Θ F) g) :
    B.opApply Θ (B.JF D F) g = B.JF D (B.opApply Θ F) g := by
  have hW := jacquet_derivative_formula
  have hR := rewrite_rho_action
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hgG : g ∈ GV k r := hg.1
  have key : ∀ T ∈ Θ, Integrable (fun p => xiP D p • Rw T.word (rho D p F) g) D.μSS ∧
      Rw T.word (JF D F) g = ∫ p, xiP D p • Rw T.word (rho D p F) g ∂D.μSS := by
    intro T hT'
    have hvl : T.word.length ≤ m := (B5.len_le_order Θ hT').trans ho
    set v' := T.word.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X with hv'
    have hv'u : ∀ X ∈ v', unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact B4.nrm_unit (x := (false, Y)) (T.word_lie Y hY)
    have hv'l : v'.length ≤ m := by rw [hv', List.length_map]; exact hvl
    obtain ⟨hI, hE⟩ := (hW k r Wp Wq D A m F hT hF).2 [] v' (by simp) hv'u (by simpa using hv'l) g hg
    simp only [List.map_nil] at hI hE
    have hae : (fun p => xiP D p • rho D p (dLR [] (v'.map (AdR p)) F) g) =ᵐ[D.μSS]
        fun p => xiP D p • Rw v' (rho D p F) g := by
      filter_upwards [B5.ae_inSS D] with p hp
      have := hR k r Wp Wq D m F p hp hCk [] v' (by simp) (fun X hX => (hv'u X hX).1) (by simpa using hv'l) g hgG
      simp only [List.map_nil] at this
      rw [← this]
      rfl
    have hI' : Integrable (fun p => xiP D p • Rw v' (rho D p F) g) D.μSS := hI.congr hae
    have hfun : (fun p => xiP D p • Rw T.word (rho D p F) g) =
        fun p => (B4.pn (B4.lr [] T.word) : ℝ) • (xiP D p • Rw v' (rho D p F) g) := by
      funext p
      rw [WordIntegralScaling.rw_scale T.word (rho D p F), Pi.smul_apply, smul_comm]
    refine ⟨?_, ?_⟩
    · rw [hfun]; exact hI'.smul (B4.pn (B4.lr [] T.word))
    · rw [WordIntegralScaling.rw_scale T.word (JF D F), Pi.smul_apply, hfun, integral_smul]
      congr 1
      rw [← integral_congr_ae hae]
      exact hE
  have hRHS : JF D (opApply Θ F) g = ∫ p, xiP D p • opApply Θ (rho D p F) g ∂D.μSS := by
    show (∫ p, xiP D p • rho D p (opApply Θ F) g ∂D.μSS) = _
    refine integral_congr_ae ?_
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hC p hp]
  rw [hRHS]
  unfold opApply
  simp only [WordIntegralScaling.smul_list]
  obtain ⟨_, hsum⟩ := WordIntegralScaling.int_list D.μSS Θ (fun T => T.coef g)
    (fun T p => xiP D p • Rw T.word (rho D p F) g) fun T hT' => (key T hT').1
  rw [hsum]
  congr 1
  refine List.map_congr_left fun T hT' => ?_
  rw [(key T hT').2]

theorem polyLift_of_smooth_comm (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (o κ : ℕ)
    (Θ : B.DiffOp P.k P.r Wp Wq) (a : RA P Bs) (hP : CutMP.PolyOp o κ Θ)
    (hC : ∀ p, Bs.inSS p → ∀ f : B.Mat P.k P.r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV P.k P.r) f →
      ∀ g ∈ B.GPos Bs, B.opApply Θ (B.rho Bs p f) g = B.rho Bs p (B.opApply Θ f) g)
    (hres : ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Q.OmPlus P.k P.r Bs.z Bs.z'),
      ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = Q.resG P.k P.r (Fin.last P.r) J x.1 x.2) →
      ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', (a.1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        Q.resG P.k P.r (Fin.last P.r) (B.opApply Θ J) x.1 x.2) :
    PolyLift P Bs o κ a := by
  refine ⟨Θ, hP, fun F hF Φ hΦ x hx => ?_⟩
  obtain ⟨ε, hε, hN⟩ := (compact_support_facts P.k P.r Wp Wq Bs F hF).1
  have hJ := bessel_function_finite_class P.k P.r Wp Wq Bs F ε hε hN
  rw [hres _ hJ Φ hΦ x hx]
  have hom : Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2 ∈ Om P.k P.r Bs.z Bs.z' :=
    ⟨TLB.wCell_gv Bs hx, P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hx.1 hx.2.1 hx.2.2⟩
  simp only [Q.resG]
  rw [opApply_JF Bs _ (B.opOrder Θ) F Θ le_rfl (JFxG.thr_big P.k P.r (B.opOrder Θ)) (hN.2.1 _ _) _ hom
    (fun p hp => hC p hp F hF.1 _ ⟨hom.1, hom.2.2⟩)]

end GlobalTheory.HatNF.SmoothLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CellMulExp
namespace GlobalTheory.HatNF.CellRules

open Matrix Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.Q Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

variable {k r : ℕ}

theorem eI_val (a : Fin r) : (eI k r a).val = a.val := rfl

theorem esI_val (a : Fin r) : (esI k r a).val = 2 * r + k - a.val := rfl

theorem cell_apply (c : Fin r → ℂ) (g : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (wCell k r (Fin.last r) c * g) p q = PI.QnWCellW.cf k r c p * g (PI.QnWCellW.swp k r p) q := by
  rw [PI.QnWCellW.wCell_last, PI.QnWCellW.Wm_mul_apply]

theorem swp_e (a : Fin r) : PI.QnWCellW.swp k r (eI k r a) = esI k r a := by
  have := a.isLt
  apply Fin.ext
  rw [PI.QnWCellW.swp_val, if_neg (by rw [eI_val]; omega), eI_val, esI_val]

theorem swp_es (a : Fin r) : PI.QnWCellW.swp k r (esI k r a) = eI k r a := by
  rw [← swp_e, PI.QnWCellW.swp_swp]

theorem cf_e (c : Fin r → ℂ) (a : Fin r) : PI.QnWCellW.cf k r c (eI k r a) = (star (c a))⁻¹ := by
  simp [PI.QnWCellW.cf, eI]

theorem cf_es (c : Fin r → ℂ) (a : Fin r) : PI.QnWCellW.cf k r c (esI k r a) = c a := by
  have := a.isLt
  unfold PI.QnWCellW.cf
  rw [if_neg (by rw [esI_val]; omega), if_neg (by rw [esI_val]; omega), esI_val, show 2 * r + k - (2 * r + k - a.val) = a.val by omega,
    PI.QnWCellW.cN_val]

theorem swp_eq_iff (p q : Fin (2 * r + k + 1)) : PI.QnWCellW.swp k r p = q ↔ p = PI.QnWCellW.swp k r q := by
  constructor
  · rintro rfl; rw [PI.QnWCellW.swp_swp]
  · rintro rfl; rw [PI.QnWCellW.swp_swp]

variable {g : Mx k r}

theorem col_e (hg : g ∈ Glev k r (Fin.last r)) (c : Fin r → ℂ) (a : Fin r) (p : Fin (2 * r + k + 1)) :
    (wCell k r (Fin.last r) c * g) p (eI k r a) = if p = esI k r a then c a else 0 := by
  rw [cell_apply, WeylGroupFacts.col_of_fix (hg.2 a a.isLt).1]
  simp only [swp_eq_iff, swp_e]
  split_ifs with h
  · rw [h, cf_es, mul_one]
  · rw [mul_zero]

theorem col_es (hg : g ∈ Glev k r (Fin.last r)) (c : Fin r → ℂ) (a : Fin r) (p : Fin (2 * r + k + 1)) :
    (wCell k r (Fin.last r) c * g) p (esI k r a) = if p = eI k r a then (star (c a))⁻¹ else 0 := by
  rw [cell_apply, WeylGroupFacts.col_of_fix (hg.2 a a.isLt).2]
  simp only [swp_eq_iff, swp_es]
  split_ifs with h
  · rw [h, cf_e, mul_one]
  · rw [mul_zero]

theorem row_e (hg : g ∈ Glev k r (Fin.last r)) (c : Fin r → ℂ) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    (wCell k r (Fin.last r) c * g) (eI k r a) q = if esI k r a = q then (star (c a))⁻¹ else 0 := by
  have := WeylGroupFacts.row_of_fixed_col hg.1 (eI k r a) (WeylGroupFacts.col_of_fix (hg.2 a a.isLt).1)
  rw [Qx3.tau_e] at this
  rw [cell_apply, swp_e, cf_e, this]
  split_ifs <;> simp

theorem row_es (hg : g ∈ Glev k r (Fin.last r)) (c : Fin r → ℂ) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    (wCell k r (Fin.last r) c * g) (esI k r a) q = if eI k r a = q then c a else 0 := by
  have := WeylGroupFacts.row_of_fixed_col hg.1 (esI k r a) (WeylGroupFacts.col_of_fix (hg.2 a a.isLt).2)
  rw [Qx3.tau_es] at this
  rw [cell_apply, swp_es, cf_es, this]
  split_ifs <;> simp

theorem cell_mem (hg : g ∈ Glev k r (Fin.last r)) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    wCell k r (Fin.last r) c * g ∈ Glev k r 0 :=
  Qx3.glev_mul (Qx3.wlist_glev hc _) (Qx3.glev_mono (Fin.zero_le _) hg)

def hX (k : ℕ) {r : ℕ} (a b : Fin r) (s : ℂ) : Mx k r :=
  s • Matrix.single (eI k r a) (eI k r b) (1 : ℂ) - star s • Matrix.single (esI k r b) (esI k r a) (1 : ℂ)

theorem hpart1_eq (a b : Fin r) :
    hpart1 (Hpk k r) (Matrix.single (eI k r a) (eI k r b) (1 : ℂ)) = hX k a b (1 / 2) := by
  unfold hpart1 hX
  rw [Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_eI, LevelPointCoordinates.single_mul_hpk_eI, smul_sub]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h2]

theorem hpart2_eq (a b : Fin r) :
    hpart2 (Hpk k r) (Matrix.single (eI k r a) (eI k r b) (1 : ℂ)) = hX k a b (-Complex.I / 2) := by
  unfold hpart2 hX
  rw [Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_eI, LevelPointCoordinates.single_mul_hpk_eI,
    smul_add, CutHL.half_I]
  have h2 : star (-Complex.I / 2 : ℂ) = -(-Complex.I / 2) := by
    apply Complex.ext <;> simp <;> norm_num
  rw [h2, neg_smul, sub_neg_eq_add]

theorem dag_hX (a b : Fin r) (s : ℂ) : QRR.dag k r (hX k a b s) = -hX k a b s := by
  unfold QRR.dag hX
  rw [Qx2.hpk_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    SingleEntryHermitianProducts.single_conjT, SingleEntryHermitianProducts.single_conjT, star_one, star_star, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, SingleEntryHermitianProducts.hpk_mul_single_eI,
    SingleEntryHermitianProducts.hpk_mul_single_esI, LevelPointCoordinates.single_mul_hpk_eI, LevelPointCoordinates.single_mul_hpk_esI, neg_sub]

theorem cell_mul_hX (hg : g ∈ Glev k r (Fin.last r)) {c : Fin r → ℂ} (hc : c ∈ OmX r) (a b : Fin r) (s : ℂ) :
    wCell k r (Fin.last r) c * g * hX k a b s =
      hX k b a (-star (s * (c a / c b))) * (wCell k r (Fin.last r) c * g) := by
  have ha := hc a
  have hb := hc b
  have ha' : star (c a) ≠ 0 := star_ne_zero.2 ha
  have hb' : star (c b) ≠ 0 := star_ne_zero.2 hb
  set x := wCell k r (Fin.last r) c * g with hx
  have e1 : x * Matrix.single (eI k r a) (eI k r b) (1 : ℂ) =
      (c a / c b) • (Matrix.single (esI k r a) (esI k r b) (1 : ℂ) * x) := by
    ext p q
    by_cases hq : q = eI k r b
    · subst hq
      rw [Matrix.mul_single_apply_same, hx, col_e hg, Matrix.smul_apply]
      by_cases hp : p = esI k r a
      · subst hp
        rw [Matrix.single_mul_apply_same, row_es hg]; simp [hb]
      · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hp]; simp [hp]
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hq, Matrix.smul_apply]
      by_cases hp : p = esI k r a
      · subst hp
        rw [Matrix.single_mul_apply_same, hx, row_es hg]; simp [Ne.symm hq]
      · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hp]; simp
  have e2 : x * Matrix.single (esI k r b) (esI k r a) (1 : ℂ) =
      star (c a / c b) • (Matrix.single (eI k r b) (eI k r a) (1 : ℂ) * x) := by
    ext p q
    by_cases hq : q = esI k r a
    · subst hq
      rw [Matrix.mul_single_apply_same, hx, col_es hg, Matrix.smul_apply]
      by_cases hp : p = eI k r b
      · subst hp
        rw [Matrix.single_mul_apply_same, row_e hg, star_div₀]
        simp only [if_true, smul_eq_mul]
        field_simp
      · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hp]; simp [hp]
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hq, Matrix.smul_apply]
      by_cases hp : p = eI k r b
      · subst hp
        rw [Matrix.single_mul_apply_same, hx, row_e hg]; simp [Ne.symm hq]
      · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hp]; simp
  unfold hX
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, e1, e2,
    smul_smul, smul_smul, star_neg, star_star, star_mul', neg_smul, neg_smul]
  abel

theorem pat_hX {a b : Fin r} (hab : b.val < a.val) (s : ℂ) : QRR.Pat k r b (hX k b a s) := by
  intro i j hij
  have ha := a.isLt
  by_cases h1 : eI k r b = i ∧ eI k r a = j
  · obtain ⟨rfl, rfl⟩ := h1
    left; rw [eI_val, eI_val]; omega
  by_cases h2 : esI k r a = i ∧ esI k r b = j
  · obtain ⟨rfl, rfl⟩ := h2
    right; rw [esI_val, esI_val]; omega
  exfalso; apply hij
  simp [hX, Matrix.single_apply, h1, h2]

theorem ell_hX {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {a b : Fin r} (hab : b.val < a.val) (s : ℂ) :
    ell k r z (hX k b a s) = if a.val = b.val + 1 then s else 0 := by
  have ha := a.isLt
  have hrow : ∀ (l : Fin r) q, hX k b a s (eI k r l) q = if l = b ∧ eI k r a = q then s else 0 := by
    intro l q
    have h1 : esI k r a ≠ eI k r l := by
      have := l.isLt
      simp only [eI, esI, ne_eq, Fin.ext_iff]; omega
    have h2 : (eI k r b = eI k r l) ↔ l = b := by
      simp only [eI, Fin.ext_iff]; exact eq_comm
    simp [hX, Matrix.single_apply, h1, h2]
  unfold ell
  rw [Finset.sum_eq_single b]
  · rw [dite_eq_left (by omega), hrow]
    simp [eI, Fin.ext_iff]
  · intro l _ hl
    split_ifs with h
    · rw [hrow, if_neg (fun h => hl h.1)]
    · simp only [Matrix.mulVec, dotProduct, hrow]
      simp [hl]
  · simp

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdV_left {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hg : g ∈ Glev k r (Fin.last r)) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) (Ψ : Mx k r → E)
    (hΨ : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, Ψ (n * (wCell k r (Fin.last r) c * g)) =
      psi k r z cStd n • Ψ (wCell k r (Fin.last r) c * g))
    {a b : Fin r} (hab : b.val < a.val) (s : ℂ) :
    RdV (hX k a b s) Ψ (wCell k r (Fin.last r) c * g) =
      (if a.val = b.val + 1 then s * (c a / c b) - star (s * (c a / c b)) else 0) •
        Ψ (wCell k r (Fin.last r) c * g) := by
  have hxG := cell_mem hg hc
  have hconj := cell_mul_hX hg hc a b s
  set x := wCell k r (Fin.last r) c * g with hx
  have hdet : IsUnit x.det := WeylGroupFacts.isUnit_of_uh hxG.1
  have hu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 hdet
  have h1 : RdV (hX k b a (-star (s * (c a / c b)))) (fun y => Ψ (y * x)) 1 =
      (ell k r z (hX k b a (-star (s * (c a / c b)))) -
        star (ell k r z (hX k b a (-star (s * (c a / c b)))))) • Ψ (1 * x) := by
    unfold RdV
    have hfun : (fun t : ℝ => Ψ ((1 * NormedSpace.exp ((t : ℂ) • hX k b a (-star (s * (c a / c b))))) * x)) =
        fun t : ℝ => psi k r z cStd (NormedSpace.exp ((t : ℂ) • hX k b a (-star (s * (c a / c b))))) • Ψ (1 * x) := by
      funext t
      simp only [Matrix.one_mul]
      apply hΨ
      apply (Formalism.FourierDecayAlt.Q.QRR.exp_mem_nlev (Formalism.FourierDecayAlt.Q.QRR.pat_smul _ (pat_hX hab _)) _).1
      rw [QRR.dag_smul, dag_hX, Complex.star_def, Complex.conj_ofReal, smul_neg]
    rw [hfun]
    exact ((Formalism.FourierDecayAlt.Q.QRR.hasDerivAt_psi z hz _).smul_const (Ψ (1 * x))).deriv
  have h2 : RdV (hX k a b s) Ψ x = RdV (hX k b a (-star (s * (c a / c b)))) (fun y => Ψ (y * x)) 1 := by
    unfold RdV
    congr 1
    funext t
    congr 1
    have e : (t : ℂ) • hX k b a (-star (s * (c a / c b))) = x * ((t : ℂ) • hX k a b s) * x⁻¹ := by
      rw [Matrix.mul_smul, hconj, Matrix.smul_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
    rw [e, Matrix.exp_conj _ _ hu, Matrix.one_mul, Matrix.nonsing_inv_mul_cancel_right _ _ hdet]
  rw [h2, h1, ell_hX hz hab, Matrix.one_mul]
  congr 1
  split_ifs
  · rw [star_neg, star_star]; ring
  · simp

theorem left_rule {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hg : g ∈ Glev k r (Fin.last r)) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) (Ψ : Mx k r → E)
    (hΨ : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, Ψ (n * (wCell k r (Fin.last r) c * g)) =
      psi k r z cStd n • Ψ (wCell k r (Fin.last r) c * g))
    {a b : Fin r} (hab : b.val < a.val) :
    EH k r (eI k r a) (eI k r b) Ψ (wCell k r (Fin.last r) c * g) =
      (if a.val = b.val + 1 then c a / c b else 0) • Ψ (wCell k r (Fin.last r) c * g) := by
  show EabH (Hpk k r) _ _ Ψ _ = _
  unfold EabH
  rw [hpart1_eq, hpart2_eq, rdV_left hz hg hc Ψ hΨ hab, rdV_left hz hg hc Ψ hΨ hab, smul_smul, ← add_smul]
  congr 1
  split_ifs
  · generalize c a / c b = w
    apply Complex.ext <;> simp <;> ring
  · simp

theorem hX_diag (a : Fin r) (s : ℂ) :
    hX k a a s = Matrix.diagonal fun q => if q = eI k r a then s else if q = esI k r a then -star s else 0 := by
  have hne : eI k r a ≠ esI k r a := PI.QnWCellW.eI_ne_esI k r a
  ext p q
  simp only [hX, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases hpq : p = q
  · subst hpq
    by_cases h1 : p = eI k r a
    · subst h1; simp [hne.symm]
    · by_cases h2 : p = esI k r a
      · subst h2; simp [hne, hne.symm]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · rw [if_neg hpq, if_neg (fun h => hpq (h.1.symm.trans h.2)), if_neg (fun h => hpq (h.1.symm.trans h.2))]
    simp

theorem cf_update (c : Fin r → ℂ) (a : Fin r) (v : ℂ) {p : Fin (2 * r + k + 1)} (h1 : p ≠ eI k r a)
    (h2 : p ≠ esI k r a) : PI.QnWCellW.cf k r (Function.update c a v) p = PI.QnWCellW.cf k r c p := by
  have h1' : p.val ≠ a.val := fun h => h1 (Fin.ext h)
  have h2' : p.val ≠ 2 * r + k - a.val := fun h => h2 (Fin.ext h)
  have hp := p.isLt
  have hN : ∀ j, j ≠ a.val → PI.QnWCellW.cN r (Function.update c a v) j = PI.QnWCellW.cN r c j := by
    intro j hj
    unfold PI.QnWCellW.cN
    split_ifs with h
    · rw [Function.update_of_ne (fun e => hj (congrArg Fin.val e))]
    · rfl
  unfold PI.QnWCellW.cf
  rw [hN _ h1', hN _ (by omega)]

theorem cell_mul_exp (hg : g ∈ Glev k r (Fin.last r)) (c : Fin r → ℂ) (a : Fin r) (s : ℂ) (t : ℝ) :
    wCell k r (Fin.last r) c * g * NormedSpace.exp ((t : ℂ) • hX k a a s) =
      wCell k r (Fin.last r) (Function.update c a (c a * Complex.exp (t * s))) * g := by
  have hne : eI k r a ≠ esI k r a := PI.QnWCellW.eI_ne_esI k r a
  rw [hX_diag, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext p q
  rw [Matrix.mul_diagonal, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases h1 : q = eI k r a
  · subst h1
    rw [col_e hg, col_e hg]
    split_ifs <;> simp_all
  · by_cases h2 : q = esI k r a
    · subst h2
      rw [col_es hg, col_es hg, if_neg h1, if_pos rfl]
      split_ifs
      · rw [Function.update_self, star_mul', mul_inv, mul_neg, Complex.exp_neg]
        simp [← Complex.exp_conj]
      · simp
    · rw [if_neg h1, if_neg h2, mul_zero, Complex.exp_zero, mul_one]
      by_cases h3 : p = eI k r a
      · subst h3
        rw [row_e hg, row_e hg, if_neg (Ne.symm h2), if_neg (Ne.symm h2)]
      · by_cases h4 : p = esI k r a
        · subst h4
          rw [row_es hg, row_es hg, if_neg (Ne.symm h1), if_neg (Ne.symm h1)]
        · rw [cell_apply, cell_apply, cf_update c a _ h3 h4]

theorem gauge_update (c : Fin r → ℂ) (a : Fin r) (w : ℂ) :
    (∏ l : Fin r, (if l.val < (Fin.last r).val then ‖Function.update c a (c a * Complex.exp w) l‖ ^ (Mdim k r l - 1)
      else 1) : ℝ) =
      Real.exp (((Mdim k r a - 1 : ℕ) : ℝ) * w.re) *
        ∏ l : Fin r, (if l.val < (Fin.last r).val then ‖c l‖ ^ (Mdim k r l - 1) else 1) := by
  simp only [Fin.val_last, Fin.is_lt, if_true]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ _ (Finset.mem_univ a),
    Function.update_self, norm_mul, Complex.norm_exp, mul_pow, Real.exp_nat_mul, ← mul_assoc, mul_comm (‖c a‖ ^ _)]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Function.update_of_ne (Finset.mem_erase.1 hl).1]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fderiv_resG {D : Set (Mx k r)} {Ψ : Mx k r → E} (hS : SmoothLev k r 0 D Ψ) (hg : g ∈ Glev k r (Fin.last r))
    {c : Fin r → ℂ} (hc : c ∈ OmX r) (hx : wCell k r (Fin.last r) c * g ∈ D) (a : Fin r) (s : ℂ) :
    fderiv ℝ (fun c' => resG k r (Fin.last r) Ψ c' g) c (Pi.single a (s * c a)) =
      resG k r (Fin.last r) (RdV (hX k a a s) Ψ) c g +
        ((((Mdim k r a - 1 : ℕ) : ℝ) * s.re : ℝ) : ℂ) • resG k r (Fin.last r) Ψ c g := by
  have hxG := cell_mem hg hc
  have hd : DifferentiableAt ℝ (fun c' => resG k r (Fin.last r) Ψ c' g) c := by
    obtain ⟨U, F, hU, hxU, hF, hFU⟩ := P5.Rad.sf_resG hS (c, g) ⟨hc, hx⟩ hg
    have h1 : DifferentiableAt ℝ F (c, g) := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)
    have h2 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => F (c', g)) c :=
      h1.comp c (differentiableAt_id.prodMk (differentiableAt_const g))
    refine h2.congr_of_eventuallyEq ?_
    have hm : ∀ᶠ c' in 𝓝 c, (c', g) ∈ U :=
      (Continuous.prodMk_left g).continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)
    filter_upwards [hm] with c' h using hFU (c', g) h hg
  have hcurve : HasDerivAt (fun t : ℝ => Function.update c a (c a * Complex.exp (t * s))) (Pi.single a (s * c a)) 0 := by
    refine hasDerivAt_pi.2 fun l => ?_
    by_cases hl : l = a
    · subst hl
      simp only [Function.update_self, Pi.single_eq_same]
      have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
      have := ((h0.mul_const s).cexp).const_mul (c l)
      refine this.congr_deriv ?_
      simp [mul_comm]
    · simp only [Function.update_of_ne hl, Pi.single_eq_of_ne hl]
      exact hasDerivAt_const _ _
  have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hcurve (by simp)
  have hΨ : HasDerivAt (fun t : ℝ => Ψ (wCell k r (Fin.last r) c * g * NormedSpace.exp ((t : ℂ) • hX k a a s)))
      (RdV (hX k a a s) Ψ (wCell k r (Fin.last r) c * g)) 0 := by
    obtain ⟨U, F, hU, hxU, hF, hFU⟩ := hS _ ⟨hxG, hx⟩
    have hd' : DifferentiableAt ℝ F (wCell k r (Fin.last r) c * g) :=
      (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)
    have hlie : inLieLev k r 0 (hX k a a s) := by
      refine ⟨?_, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩
      unfold hX
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, SingleEntryHermitianProducts.single_conjT,
        SingleEntryHermitianProducts.single_conjT, star_one, star_star, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul,
        LevelPointCoordinates.single_mul_hpk_eI, LevelPointCoordinates.single_mul_hpk_esI, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
        SingleEntryHermitianProducts.hpk_mul_single_eI, SingleEntryHermitianProducts.hpk_mul_single_esI]
      abel
    exact (Qx2.hasDeriv_ext hU hxU hxG hlie hd' hFU).differentiableAt.hasDerivAt
  set n : ℝ := ((Mdim k r a - 1 : ℕ) : ℝ) with hn
  set γ : ℝ := ∏ l : Fin r, (if l.val < (Fin.last r).val then ‖c l‖ ^ (Mdim k r l - 1) else 1) with hγ
  have hγd : HasDerivAt (fun t : ℝ => ((Real.exp (n * (t * s.re)) * γ : ℝ) : ℂ)) ((n * s.re * γ : ℝ) : ℂ) 0 := by
    have := ((((hasDerivAt_id (0 : ℝ)).mul_const s.re).const_mul n).exp.mul_const γ).ofReal_comp
    simpa using this
  have h2 := hγd.smul hΨ
  have e : ((fun c' => resG k r (Fin.last r) Ψ c' g) ∘ fun t : ℝ => Function.update c a (c a * Complex.exp (t * s))) =
      (fun t : ℝ => ((Real.exp (n * (t * s.re)) * γ : ℝ) : ℂ)) •
        fun t : ℝ => Ψ (wCell k r (Fin.last r) c * g * NormedSpace.exp ((t : ℂ) • hX k a a s)) := by
    funext t
    simp only [Function.comp, resG, Pi.smul_apply']
    rw [gauge_update, cell_mul_exp hg, Complex.re_ofReal_mul]
  rw [e] at h1
  rw [h1.unique h2]
  simp only [resG, ← hγ, smul_smul]
  simp

theorem torus_rule {D : Set (Mx k r)} {Ψ : Mx k r → E} (hS : SmoothLev k r 0 D Ψ) (hg : g ∈ Glev k r (Fin.last r))
    {c : Fin r → ℂ} (hc : c ∈ OmX r) (hx : wCell k r (Fin.last r) c * g ∈ D) (a : Fin r) :
    pOp a (fun c' => resG k r (Fin.last r) Ψ c' g) c =
      resG k r (Fin.last r) (EH k r (eI k r a) (eI k r a) Ψ) c g +
        (((r : ℂ) - (a.val : ℂ)) + (k : ℂ) / 2) • resG k r (Fin.last r) Ψ c g := by
  have h1 := fderiv_resG hS hg hc hx a (1 / 2)
  have h2 := fderiv_resG hS hg hc hx a (-Complex.I / 2)
  have h3 := CutHL.torus_id ((fderiv ℝ (fun c' => resG k r (Fin.last r) Ψ c' g) c).comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin r => ℂ) a)) (c a)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply] at h3
  unfold pOp wirt
  rw [if_pos hc, ← h3, h1, h2]
  have hM : ((Mdim k r a - 1 : ℕ) : ℂ) = 2 * ((r : ℂ) - (a.val : ℂ)) + k := by
    unfold Mdim
    rw [Nat.add_sub_cancel]
    push_cast [Nat.cast_sub a.isLt.le]
    ring
  have e1 : ((((Mdim k r a - 1 : ℕ) : ℝ) * (1 / 2 : ℂ).re : ℝ) : ℂ) = ((r : ℂ) - (a.val : ℂ)) + (k : ℂ) / 2 := by
    have : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    rw [this]; push_cast; rw [hM]; ring
  have e2 : ((((Mdim k r a - 1 : ℕ) : ℝ) * (-Complex.I / 2 : ℂ).re : ℝ) : ℂ) = 0 := by simp
  rw [e1, e2, zero_smul, add_zero]
  simp only [resG, EH, EabH, hpart1_eq, hpart2_eq]
  module

end

end GlobalTheory.HatNF.CellRules
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPolyDiffOpRadialPartEqShiftedOperator
namespace GlobalTheory.HatNF.TodaLift

open Matrix Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.Q Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5 GlobalTheory.HatNF.CellRules

noncomputable section

theorem qminor_commute {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (x : A)
    (a b : Fin t → Fin n) (u : ℂ) (h : ∀ i j : Fin t, Commute (E (a i) (b j)) x) : Commute (qminor E a b u) x := by
  have hT : ∀ (v : ℂ) (i j : Fin t), Commute (Tm E v (a i) (b j)) x := by
    intro v i j
    unfold Tm
    refine Commute.add_left ?_ (h i j)
    split_ifs
    · exact Algebra.commutes v x
    · exact Commute.zero_left x
  unfold qminor
  refine Commute.sum_left _ _ _ fun σ _ => ?_
  refine (Int.cast_commute _ x).mul_left (Commute.list_prod_left _ _ fun y hy => ?_)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
  exact hT _ _ i

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}

theorem leftEq_adjoin (z : Fin (2 * r + k + 1) → ℂ) (hD : IsOpen D)
    (hDN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D) (x : LevelPointCoordinates.SB E hD) :
    ∀ v : VS k r 0 D E, LeftEq k r z 0 D (v : Mx k r → E) →
      LeftEq k r z 0 D (((x : Module.End ℂ (VS k r 0 D E)) v : VS k r 0 D E) : Mx k r → E) := by
  obtain ⟨x, hx⟩ := x
  show ∀ v : VS k r 0 D E, LeftEq k r z 0 D (v : Mx k r → E) →
      LeftEq k r z 0 D ((x v : VS k r 0 D E) : Mx k r → E)
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨⟨p, q⟩, rfl⟩ := hy
    intro v hv g hg n hn
    have h := (generator_action_preserved E k r z 0 D (PBG.c0 p) (PBG.c0 q) v v 0 hD v.2.1 v.2.1).2.1 hDN hv g hg n hn
    have hng : n * g ∈ Glev k r 0 ∩ D := ⟨Qx3.glev_mul hn.2 hg.1, hDN g hg n hn⟩
    show ((Eh hD _ _ v : VS k r 0 D E) : Mx k r → E) _ = _ • ((Eh hD _ _ v : VS k r 0 D E) : Mx k r → E) _
    rw [ev_E hD _ _ v hng, ev_E hD _ _ v hg, h]
  | algebraMap c =>
    intro v hv g hg n hn
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hv g hg n hn, smul_comm]
  | add y1 y2 _ _ h1 h2 =>
    intro v hv g hg n hn
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [h1 v hv g hg n hn, h2 v hv g hg n hn, smul_add]
  | mul y1 y2 _ _ h1 h2 =>
    intro v hv
    exact h1 _ (h2 v hv)

def ap (hD : IsOpen D) (J : Mx k r → E) (hS : SmoothLev k r 0 D J) (x : LevelPointCoordinates.SB E hD) : Mx k r → E :=
  (((x : Module.End ℂ (VS k r 0 D E)) (PBG.vK hD J hS) : VS k r 0 D E) : Mx k r → E)

def mn (hD : IsOpen D) (Y : ℂ) (m : ℕ) (hm : m ≤ r) : LevelPointCoordinates.SB E hD :=
  qminor (LevelPointCoordinates.EB hD) (C3.xR k r m hm) (C3.xR k r m hm) (Y + ((2 * r + k : ℕ) : ℂ) / 2)

variable {g : Mx k r} {c : Fin r → ℂ}

theorem res_ap_one (hD : IsOpen D) {J : Mx k r → E} (hS : SmoothLev k r 0 D J) (hg : g ∈ Glev k r (Fin.last r))
    (hc : c ∈ OmX r) (hx : wCell k r (Fin.last r) c * g ∈ D) :
    resG k r (Fin.last r) (ap hD J hS 1) c g = resG k r (Fin.last r) J c g := by
  unfold resG
  congr 1
  exact cut_of_mem J ⟨cell_mem hg hc, hx⟩

theorem res_ap_torus (hD : IsOpen D) {J : Mx k r → E} (hS : SmoothLev k r 0 D J) (hg : g ∈ Glev k r (Fin.last r))
    (hc : c ∈ OmX r) (hx : wCell k r (Fin.last r) c * g ∈ D) (Y : ℂ) (a : Fin r) (x : LevelPointCoordinates.SB E hD) :
    resG k r (Fin.last r)
        (ap hD J hS (Tm (LevelPointCoordinates.EB hD) (Y + ((2 * r + k : ℕ) : ℂ) / 2 - (a.val : ℂ)) (eI k r a) (eI k r a) * x)) c g =
      Y • resG k r (Fin.last r) (ap hD J hS x) c g + pOp a (fun c' => resG k r (Fin.last r) (ap hD J hS x) c' g) c := by
  have hxG : wCell k r (Fin.last r) c * g ∈ Glev k r 0 ∩ D := ⟨cell_mem hg hc, hx⟩
  rw [torus_rule (Ψ := ap hD J hS x) ((x : Module.End ℂ (VS k r 0 D E)) (PBG.vK hD J hS)).2.1 hg hc hx a]
  have e : ap hD J hS (Tm (LevelPointCoordinates.EB hD) (Y + ((2 * r + k : ℕ) : ℂ) / 2 - (a.val : ℂ)) (eI k r a) (eI k r a) * x)
      (wCell k r (Fin.last r) c * g) =
      (Y + ((2 * r + k : ℕ) : ℂ) / 2 - (a.val : ℂ)) • ap hD J hS x (wCell k r (Fin.last r) c * g) +
        EH k r (eI k r a) (eI k r a) (ap hD J hS x) (wCell k r (Fin.last r) c * g) := by
    have h := ev_E hD (PBG.c0 (eI k r a)) (PBG.c0 (eI k r a))
      ((x : Module.End ℂ (VS k r 0 D E)) (PBG.vK hD J hS)) hxG
    rw [PBG.position_level_zero_coord] at h
    unfold ap
    rw [← h, Tm, if_pos rfl, add_mul, ← Algebra.smul_def]
    rfl
  simp only [resG, e]
  push_cast
  module

theorem mn_zero (hD : IsOpen D) (Y : ℂ) : mn (E := E) hD Y 0 (Nat.zero_le r) = 1 := by
  simp [mn, qminor]

theorem mn_one (hD : IsOpen D) (Y : ℂ) (h : 1 ≤ r) : mn (E := E) hD Y 1 h =
    Tm (LevelPointCoordinates.EB hD) (Y + ((2 * r + k : ℕ) : ℂ) / 2 - (((⟨0, h⟩ : Fin r).val : ℕ) : ℂ)) (eI k r ⟨0, h⟩) (eI k r ⟨0, h⟩) *
      mn hD Y 0 (Nat.zero_le r) := by
  rw [mn_zero, mul_one]
  simp [mn, qminor, C3.xR]
  rfl

theorem res_mn_succ {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (hD : IsOpen D)
    (hDN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D) {J : Mx k r → E} (hS : SmoothLev k r 0 D J)
    (hL : LeftEq k r z 0 D J) (hR : RightEq k r z' 0 D J) (hg : g ∈ Glev k r (Fin.last r))
    (hc : c ∈ OmX r) (hx : wCell k r (Fin.last r) c * g ∈ D) (Y : ℂ) (m : ℕ) (hm : m + 2 ≤ r) :
    resG k r (Fin.last r) (ap hD J hS (mn hD Y (m + 2) hm)) c g =
      Y • resG k r (Fin.last r) (ap hD J hS (mn hD Y (m + 1) (by omega))) c g +
        pOp ⟨m + 1, by omega⟩ (fun c' => resG k r (Fin.last r) (ap hD J hS (mn hD Y (m + 1) (by omega))) c' g) c -
        (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • resG k r (Fin.last r) (ap hD J hS (mn hD Y m (by omega))) c g := by
  have hxG : wCell k r (Fin.last r) c * g ∈ Glev k r 0 ∩ D := ⟨cell_mem hg hc, hx⟩
  have hN : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, n ∈ Nlev k r 0 := fun n hn => ⟨hn, SingleEntryHermitianProducts.glev0 hn.1⟩
  have hRr : ∀ g ∈ Glev k r 0 ∩ D, ∀ p q, C3.InNp k r p q → EH k r p q J g = C3.dpsiP k r z' p q • J g :=
    fun g hg p q hpq => rule_of_eq E k r z' J g hz' (fun n hn => hR g hg n (hN n hn)) p q hpq
  let La' : LevelPointCoordinates.SB E hD →ₗ[ℂ] E :=
    (PBG.La hD J hS (wCell k r (Fin.last r) c * g)).comp (LevelPointCoordinates.SB E hD).val.toLinearMap
  have hLa' : ∀ x, La' x = ap hD J hS x (wCell k r (Fin.last r) c * g) := fun x => rfl
  have hRR : C3.RightRuleFn k r z' (LevelPointCoordinates.EB hD) La' := fun x p q hpq =>
    PBG.La_rule hD z' J hS hRr _ x.1 p q hpq
  have hvK : LeftEq k r z 0 D (PBG.vK hD J hS : Mx k r → E) := by
    intro g hg n hn
    have hng : n * g ∈ Glev k r 0 ∩ D := ⟨Qx3.glev_mul hn.2 hg.1, hDN g hg n hn⟩
    show cut k r 0 D J _ = _ • cut k r 0 D J g
    rw [cut_of_mem J hng, cut_of_mem J hg, hL g hg n hn]
  have hLL : C3.LeftRuleBig k r c (LevelPointCoordinates.EB hD) La' := by
    intro x a b hab
    rw [hLa', hLa', ← left_rule hz hg hc (ap hD J hS x)
      (fun n hn => leftEq_adjoin z hD hDN x _ hvK _ hxG n (hN n hn)) hab]
    have h := ev_E hD (PBG.c0 (eI k r a)) (PBG.c0 (eI k r b))
      ((x : Module.End ℂ (VS k r 0 D E)) (PBG.vK hD J hS)) hxG
    rw [PBG.position_level_zero_coord, PBG.position_level_zero_coord] at h
    exact h
  have hch := chain_first_identity (LevelPointCoordinates.SB E hD) E k r z' c (LevelPointCoordinates.EB hD) La' (LevelPointCoordinates.EB_gl hD) hc hRR hLL m hm
    (Y + ((2 * r + k : ℕ) : ℂ) / 2)
  have hcomm : Commute (mn (E := E) hD Y (m + 1) (by omega))
      (Tm (LevelPointCoordinates.EB hD) (Y + ((2 * r + k : ℕ) : ℂ) / 2 - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩)
        (eI k r ⟨m + 1, by omega⟩)) := by
    unfold Tm
    rw [if_pos rfl]
    refine Commute.add_right (Algebra.commutes _ _).symm (qminor_commute _ _ _ _ _ fun i j => ?_)
    have hi := i.isLt
    have hj := j.isLt
    have h := LevelPointCoordinates.EB_gl (E := E) hD (C3.xR k r (m + 1) (by omega) i) (C3.xR k r (m + 1) (by omega) j)
      (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)
    rw [if_neg (by simp only [C3.xR, Fin.ext_iff, eI_val, Fin.val_castLE]; omega),
      if_neg (by simp only [C3.xR, Fin.ext_iff, eI_val, Fin.val_castLE]; omega), sub_zero, sub_eq_zero] at h
    exact h
  rw [← res_ap_torus hD hS hg hc hx Y ⟨m + 1, by omega⟩, ← hcomm.eq]
  simp only [resG, ← hLa']
  rw [smul_comm (c _ / c _), ← smul_sub]
  congr 1

theorem res_AAop (hD : IsOpen D) {J : Mx k r → E} (hS : SmoothLev k r 0 D J) (hg : g ∈ Glev k r (Fin.last r))
    (hc : c ∈ OmX r) (hx : wCell k r (Fin.last r) c * g ∈ D) (Y : ℂ) :
    resG k r (Fin.last r) (C3.AAop k r r le_rfl (Y + ((2 * r + k : ℕ) : ℂ) / 2) J) c g =
      (∏ a, c a) • resG k r (Fin.last r) (ap hD J hS (mn hD Y r le_rfl)) c g := by
  have hxG : wCell k r (Fin.last r) c * g ∈ Glev k r 0 ∩ D := ⟨cell_mem hg hc, hx⟩
  have hxi : ∀ a p, PBG.xi0 (wCell k r (Fin.last r) c * g) a p = if eI k r a = p then c a else 0 := by
    intro a p
    rw [← row_es hg]
    simp [PBG.xi0, herm, bvec, Matrix.mulVec, dotProduct, Pi.single_apply, Qx3.hpk_row_e]
  simp only [resG]
  rw [smul_comm (∏ a, c a), ← PBG.La_AAx hD J hS _ hxG,
    SignAntidiagonal.AAx_head k r _ _ r le_rfl (Matrix.diagonal c) _ ?_ ?_, map_smul, Matrix.det_diagonal]
  · congr 2
    unfold ap mn
    have := PBN.MC.map_qminor (LevelPointCoordinates.SB E hD).val (LevelPointCoordinates.EB hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (Y + ((2 * r + k : ℕ) : ℂ) / 2)
    show _ = (((LevelPointCoordinates.SB E hD).val _ (PBG.vK hD J hS) : VS k r 0 D E) : Mx k r → E) _
    rw [this]
    rfl
  · intro a p ha hp
    rw [hxi, if_neg]
    rintro rfl
    rw [eI_val] at hp; omega
  · intro a b
    rw [hxi, Matrix.diagonal_apply]
    simp [C3.xR, Fin.ext_iff, eI_val]

theorem isPolyDeg_pluecker (κ : ℕ) (hκ : r ≤ κ) (b : Fin r → Fin (2 * r + k + 1)) :
    U.IsPolyDeg κ fun g : B.Mat k r => (Matrix.of fun a l : Fin r =>
      herm (Hpk k r) (g *ᵥ bvec (b l)) (bvec (eI k r (Fin.castLE le_rfl a)))).det := by
  refine ⟨(Matrix.of fun a l : Fin r => MvPolynomial.X (Sum.inl (esI k r a, b l))).det, ?_, fun g => ?_⟩
  · rw [Matrix.det_apply]
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun σ _ => ?_)
    refine (MvPolynomial.totalDegree_smul_le _ _).trans ((MvPolynomial.totalDegree_finsetProd _ _).trans ?_)
    simpa [MvPolynomial.totalDegree_X] using hκ
  · rw [RingHom.map_det]
    refine congrArg Matrix.det ?_
    ext a l
    simp [herm, bvec, Matrix.mulVec, dotProduct, Pi.single_apply, Qx3.hpk_row_e]

section ops

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem exists_polyOp_AAop (k r o κ : ℕ) (ho : r ≤ o) (hκ : r ≤ κ) (u : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, CutMP.PolyOp o κ Θ ∧ ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), ∀ g ∈ B.GV k r,
      ∀ V : Set (B.Mat k r), IsOpen V → g ∈ V → B.CkOn ⊤ (B.GV k r ∩ V) F →
        B.opApply Θ F g = C3.AAop k r r le_rfl u F g := by
  classical
  obtain ⟨Θ, hΘ, he⟩ := GlobalTheory.HatNF.MinorPoly.minor_polyOp Wp Wq k r r κ (Fin r → Fin (2 * r + k + 1)) (fun _ => C3.xR k r r le_rfl)
    (fun b => b) u (fun b g => if StrictMono b then (Matrix.of fun a l : Fin r =>
      herm (Hpk k r) (g *ᵥ bvec (b l)) (bvec (eI k r (Fin.castLE le_rfl a)))).det else 0) (fun b => by
      by_cases hb : StrictMono b
      · simp only [if_pos hb]; exact isPolyDeg_pluecker κ hκ b
      · simp only [if_neg hb]; exact ⟨0, by simp, fun g => by simp⟩)
  refine ⟨Θ, fun T hT => ⟨(hΘ T hT).1.trans ho, (hΘ T hT).2⟩, fun F g hg V hV hgV hF => ?_⟩
  rw [he F g hg V hV hgV hF]
  unfold C3.AAop
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · rfl
  · rw [zero_smul]

variable {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

omit [FiniteDimensional ℂ Wp] in
theorem pref_succ (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (Y : ℂ) (n : ℕ) (hn : n < r) (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) (g : Mx k r) :
    ((JCx2.rma_pref L Y (n + 1) 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
        Y • ((JCx2.rma_pref L Y n 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g +
          pOp ⟨n, hn⟩ (fun c' => ((JCx2.rma_pref L Y n 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) c -
          c ⟨n, hn⟩ • ((JCx2.rma_pref L Y n 1 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g ∧
      ((JCx2.rma_pref L Y (n + 1) 1 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
        (c ⟨n, hn⟩)⁻¹ • ((JCx2.rma_pref L Y n 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g := by
  have key : ∀ a : Fin 2, ((JCx2.rma_pref L Y (n + 1) a 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) =
      TL k ⟨n, hn⟩ Y a 0 ((JCx2.rma_pref L Y n 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) +
        TL k ⟨n, hn⟩ Y a 1 ((JCx2.rma_pref L Y n 1 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) := by
    intro a
    rw [← JCx2.rma_T_fst X L hL, ← JCx2.rma_T_fst X L hL, JCx2.rma_pref, dite_eq_left hn, Matrix.mul_apply,
      Fin.sum_univ_two]
    rfl
  rw [key, key]
  simp [TL, crd, Tmat, cOp, ciOp, sub_eq_add_neg]

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
theorem prod_c_apply (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (c : Fin r → ℂ) (g : Mx k r) (l : List (Fin r)) (Ψ : RadSp k r z z' π π') :
    (((l.map L.c).prod).1 Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = (l.map c).prod • (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, one_smul]; rfl
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [mul_smul, ← ih, hL.2.2.1 a]
    show (X.op a 1 (((l.map L.c).prod).1 Ψ) : Fn k r (Wq →L[ℂ] Wp)) c g = _
    rw [X.op_apply]
    rfl


omit [FiniteDimensional ℂ Wp] in
theorem ahat_apply (hz : inWb k r z) (hz' : inWb k r z') (X : ActualOps k r z z' π π')
    (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (hL : IsActualLevel X L) (Y : ℂ)
    {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' 0 (OmPlus k r z z')) (Φ : RadSp k r z z' π π')
    (hΦ : ∀ x ∈ DomR k r z z', (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) J x.1 x.2) :
    ∀ x ∈ DomR k r z z', ((L.Ahat Y).1 Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
      resG k r (Fin.last r) (C3.AAop k r r le_rfl (Y + ((2 * r + k : ℕ) : ℂ) / 2) J) x.1 x.2 := by
  rintro ⟨c₀, g⟩ ⟨hc₀, hg, hG⟩
  have hDom := JCx2.rma_isDom_omPlus hz hz'
  have hD := hDom.1
  have hx : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g ∈ OmPlus k r z z' :=
    fun c hc => P5.Rad.wCell_mem_omPlus hz hz' hc hg hG
  have hDN : ∀ g ∈ Glev k r 0 ∩ OmPlus k r z z', ∀ n ∈ Nlev k r 0, n * g ∈ OmPlus k r z z' := by
    intro g hg n hn
    have h1 : (1 : Mx k r) ∈ Nlev k r 0 := ⟨(nSubgroup k r).1, Qx3.glev_one 0⟩
    have := hDom.2 g hg (1 * n) ⟨1, BigCellZetaMinors.one_uw z, n, hn, rfl⟩ (1 * 1) ⟨1, BigCellZetaMinors.one_uw z', 1, h1, rfl⟩
    simpa using this
  have hp : ∀ (l : Fin r) (f₁ f₂ : (Fin r → ℂ) → (Wq →L[ℂ] Wp)), (∀ c ∈ OmX r, f₁ c = f₂ c) →
      ∀ c ∈ OmX r, pOp l f₁ c = pOp l f₂ c := by
    intro l f₁ f₂ h c hc
    simp only [pOp, wirt, (JCx2.rma_eq_nhds hc h).fderiv_eq]
  have h0 : ∀ c ∈ OmX r, ((JCx2.rma_pref L Y 0 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
      resG k r (Fin.last r) (ap hD J hJ.1 (mn hD Y 0 (Nat.zero_le r))) c g := by
    intro c hc
    rw [mn_zero, res_ap_one hD hJ.1 hg hc (hx c hc), ← hΦ (c, g) ⟨hc, hg, hG⟩, JCx2.rma_pref, Matrix.one_apply_eq]
    rfl
  have key : ∀ (m : ℕ) (hm : m + 1 ≤ r), (∀ c ∈ OmX r, ((JCx2.rma_pref L Y m 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
      resG k r (Fin.last r) (ap hD J hJ.1 (mn hD Y m (by omega))) c g) ∧
      ∀ c ∈ OmX r, ((JCx2.rma_pref L Y (m + 1) 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
      resG k r (Fin.last r) (ap hD J hJ.1 (mn hD Y (m + 1) hm)) c g := by
    intro m
    induction m with
    | zero =>
      intro hm
      refine ⟨h0, fun c hc => ?_⟩
      rw [(pref_succ X L hL Y 0 hm Φ c g).1, hp _ _ _ h0 c hc, h0 c hc]
      have e : ((JCx2.rma_pref L Y 0 1 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 := by
        rw [JCx2.rma_pref, Matrix.one_apply_ne (by decide)]
        rfl
      rw [e, smul_zero, sub_zero, ← res_ap_torus hD hJ.1 hg hc (hx c hc) Y ⟨0, hm⟩, ← mn_one]
    | succ m ih =>
      intro hm
      obtain ⟨i1, i2⟩ := ih (by omega)
      refine ⟨i2, fun c hc => ?_⟩
      rw [(pref_succ X L hL Y (m + 1) hm Φ c g).1, (pref_succ X L hL Y m (by omega) Φ c g).2, hp _ _ _ i2 c hc,
        i2 c hc, i1 c hc, res_mn_succ hz hz' hD hDN hJ.1 hJ.2.1 hJ.2.2.1 hg hc (hx c hc) Y m hm, smul_smul,
        div_eq_mul_inv]
  have hr : ((JCx2.rma_pref L Y r 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c₀ g =
      resG k r (Fin.last r) (ap hD J hJ.1 (mn hD Y r le_rfl)) c₀ g := by
    have : ∀ (m : ℕ) (hm : m ≤ r), ((JCx2.rma_pref L Y m 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c₀ g =
        resG k r (Fin.last r) (ap hD J hJ.1 (mn hD Y m hm)) c₀ g := by
      intro m hm
      cases m with
      | zero => exact h0 c₀ hc₀
      | succ m => exact (key m hm).2 c₀ hc₀
    exact this r le_rfl
  show ((L.Dr).1 ((L.Tprod Y 0 0).1 Φ) : Fn k r (Wq →L[ℂ] Wp)) c₀ g = _
  rw [res_AAop hD hJ.1 hg hc₀ (hx c₀ hc₀), ← hr, TLB.rma_pref_take, ← TLB.tprod_take_all, R.LevelData.Dr,
    List.ofFn_eq_map, prod_c_apply X L hL, ← List.ofFn_eq_map, List.prod_ofFn]

end ops

end

end GlobalTheory.HatNF.TodaLift

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem polyLift_ahat : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ y : ℝ, PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (d.L.Ahat y) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d _ hNF y
  obtain ⟨Θ, hΘ, he⟩ := TodaLift.exists_polyOp_AAop (Wp := Wp) (Wq := Wq) P.k P.r (2 * P.r + P.k + 1)
    (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (by omega) (by nlinarith [Nat.zero_le P.r, Nat.zero_le P.k])
    ((y : ℂ) + ((2 * P.r + P.k : ℕ) : ℂ) / 2)
  refine SmoothLift.polyLift_of_smooth_comm P Bs _ _ Θ _ hΘ (fun p hp f hf g hg => ?_) (fun J hJ Φ hΦ x hx => ?_)
  · rw [he _ g hg.1 Set.univ isOpen_univ trivial (by simpa using Formalism.FourierDecayAlt.P.B5.ckOn_rho Bs hp hf),
      ← (Formalism.FourierDecayAlt.P.PBG.rho_AA Bs hf P.r le_rfl _ 0 hp hg.1).1]
    simp only [B.rho]
    rw [he f _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hg.1) Set.univ isOpen_univ trivial (by simpa using hf)]
  · rw [TodaLift.ahat_apply Bs.z_mem Bs.z'_mem X d.L hNF.1 y hJ Φ hΦ x hx]
    simp only [Q.resG]
    rw [he J _ (Formalism.FourierDecayAlt.P.TLB.wCell_gv Bs hx) (Q.OmPlus P.k P.r Bs.z Bs.z')
      (Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus Bs.z_mem Bs.z'_mem).1
      (Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hx.1 hx.2.1 hx.2.2) ?_]
    intro g₀ hg₀
    obtain ⟨U, F, a, b, c, e⟩ := hJ.1 g₀ ⟨Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.glev0 hg₀.1, hg₀.2⟩
    exact ⟨U, F, a, b, c, fun w hw hwG => e w hw (Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.glev0 hwG)⟩

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPolyDiffOpRadialPartEqShiftedOperatorStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polyDiffOp_radialPart_eq_shiftedOperator : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ y : ℝ, PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (d.L.Ahat y) := by
  first | exact @GlobalTheory.HatNF.polyLift_ahat | exact GlobalTheory.HatNF.polyLift_ahat | (intros; apply GlobalTheory.HatNF.polyLift_ahat <;> assumption)
end
