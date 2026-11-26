module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CuspFormValueLeSupNormAtOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOfVac

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMetricOfIsOrtho
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.OrthoMetric

namespace GlobalTheory.SupFull

theorem hm_eq_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (k : U.Comp) (x : (U.X k).dom) (W : PullbackSections.UnfAt U k x) (Wu : PullbackSections.UnitAt W), (U.X k).IsOrtho x.1 → Wu.Hm = Matrix.diagonal fun j => ((2 * ‖relab c σ (W.e j).1 (U.X k).ξ0‖ : ℝ) : ℂ) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k x W Wu hx
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1 (relab c σ) hbij
    Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  have hper : ∀ (v : Fin r → E) j, perFr (U.X k) x.1 v (relab c σ (W.e j).1) (W.e j).2 =
      if (((W.e.trans f) j).2 : ℕ) < (U.X k).p0 then
        FD.hermC ((W.e.trans f) j).1.1 (U.X k).Gm
          (FD.col (FD.mat x.1 ((W.e.trans f) j).1) ((W.e.trans f) j).2) (FD.Data.emb ((W.e.trans f) j).1.1 v)
      else ((FD.mat x.1 ((W.e.trans f) j).1)⁻¹.mulVec (FD.Data.emb ((W.e.trans f) j).1.1 v))
        ((W.e.trans f) j).2 := by
    intro v j
    have h := hf (W.e j)
    rw [Equiv.trans_apply]
    generalize f (W.e j) = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    generalize ((W.e j).2 : ℕ) = i at h ⊢
    dsimp only at h ⊢
    rw [← hp0] at h
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dite_eq_right a, dif_pos (show conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
      rfl
  have hcc : FD.cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    have h := (U.X k).ξ0_im
    unfold FD.cc at h ⊢
    rw [map_neg, h]
  have key : Wu.Hm = Matrix.diagonal fun j => ((2 * (((W.e.trans f) j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ) := by
    refine PullbackSections.UH.herm_eq_of_im W.Pm W.per.2.2.2.1 _ _ fun a b => ?_
    rw [Wu.c1, OrthoHerm.im_diag_eq_trace (U.X k).p0 _ (U.X k).Gm (U.X k).Ψ (U.X k).cmType (W.e.trans f) hcc x.1 hx
      (W.φ k a) (W.φ k b) _ _ (fun j => (W.pm_eq a j).trans (hper _ j)) (fun j => (W.pm_eq b j).trans (hper _ j)),
      ← W.isom, Rat.cast_intCast]
  have hd : ∀ j, (((W.e.trans f) j).1.1 (-(U.X k).ξ0)).im = ‖relab c σ (W.e j).1 (U.X k).ξ0‖ := by
    intro j
    have hn : ‖relab c σ (W.e j).1 (U.X k).ξ0‖ = ‖((W.e.trans f) j).1.1 (U.X k).ξ0‖ := by
      rcases hf (W.e j) with ⟨-, h, -⟩ | ⟨-, h, -⟩
      · rw [Equiv.trans_apply, h]
      · rw [Equiv.trans_apply, h]
        exact (Complex.norm_conj _).symm
    rw [hn]
    clear hn
    have hpos := Wu.pos (Pi.single j 1) (by simp)
    rw [key, hermForm, single_dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Pi.single_eq_same, star_one,
      _root_.one_mul, _root_.mul_one, Complex.ofReal_re] at hpos
    generalize ((W.e.trans f) j).1.1 = τ at hpos ⊢
    have hre : (τ (-(U.X k).ξ0)).re = 0 := by
      have h := congrArg τ hcc
      rw [FD.cc, IsCMField.complexEmbedding_complexConj, map_neg τ (-(U.X k).ξ0)] at h
      have := congrArg Complex.re h
      simp only [Complex.conj_re, Complex.neg_re] at this
      linarith
    have hp : 0 < (τ (-(U.X k).ξ0)).im := by linarith
    rw [← norm_neg, ← map_neg, ← Complex.abs_im_eq_norm.mpr hre, abs_of_pos hp]
  rw [key]
  simp only [hd]

theorem isMetric_of_isOrtho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q → ∀ (k : U.Comp) (x : (U.X k).dom), (U.X k).IsOrtho x.1 → IsMetric (U.un k x) 1 (fun b => ((2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ : ℝ) : ℂ) • 1) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hpq k x hx
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x
  obtain ⟨Wu⟩ := PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)
  have hH := hm_eq_diagonal E H Dw l Xo c σ r U hσ hU k x W Wu hx
  obtain ⟨Φ₀⟩ := nonempty_fibKey E H Dw l Xo ℂ (U.un k x).x hpq
  obtain ⟨-, h₁, h₂⟩ := SecTieEx.secTie_exists_unique E H Dw l Xo ℂ (U.un k x).x Φ₀.T.t Φ₀.m
  obtain ⟨th, ht⟩ := h₁ (U.un k x).s
  have hne := (h₂ th _ ht).2.1 (secNZ_of_secGen lawsFieldsSeparately.2.1 E H Dw l Xo ℂ _ _ (U.un k x).gen)
  let Φ : FibKey Xo ℂ (U.un k x).x := { Φ₀ with th := th, th_ne := hne }
  obtain ⟨u, χ, hΛ, hA, hR, hF, hg, hD⟩ := exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos Wu.c2 Wu.c3 Wu.c4
    Wu.c5 Wu.c6 Wu.c7
  choose w hw using fun τ i => hD _ _ ((U.un k x).tan τ i) (W.der τ i)
  have hFd : IsAddFundamentalDomain u.Λ Wu.Fd volume := hΛ ▸ Wu.c8
  have hN := Wu.c9.symm
  have hG : ∀ (b : E →+* ℂ) (i j : Fin (Dw.mult b)),
      (((2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ : ℝ) : ℂ) • (1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)) i j =
        Real.pi * hermForm Wu.Hm (Pi.single (W.e.symm ⟨b, j⟩) 1) (Pi.single (W.e.symm ⟨b, i⟩) 1) := by
    intro b i j
    rw [hH]
    simp [hermForm, Matrix.mulVec_diagonal, Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp_all <;> ring
  exact isMetricAt_of Φ hg u Wu.Hm χ Wu.θ Wu.Fd w (fun b i => Pi.single (W.e.symm ⟨b, i⟩) 1)
    ⟨ht, hA, hR, hF, hFd, hN, hw, hG⟩

theorem isBddSec_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U U' : Unf Xo c σ r), GoodEmb c σ → IsUnf U → IsUnf U' → 1 ≤ Dw.p + Dw.q → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, (∀ k, (U.X k).IsBddSec (laU U a n k) (rdU U f k)) → ∀ k, (U'.X k).IsBddSec (laU U' a n k) (rdU U' f k) := by
  intro E _ _ _ H Dw l Xo c σ r U U' hσ hU hU' hpq a n hd f hf hb k'
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, -, -, -, -, hwt⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hs' := hU'.2.2.2.2.1 a n hd f hf k'
  choose C hC using fun k => (hb k).2
  have hpos : ∀ (X : FD.Data E r) (b : E →+* ℂ), 0 < 2 * Real.pi * ‖relab c σ b X.ξ0‖ := fun X b =>
    mul_pos (by positivity) (norm_pos_iff.2 ((map_ne_zero _).2 X.ξ0_ne))
  let κ : U.Comp → (E →+* ℂ) → ℝ := fun k b =>
    2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ / (2 * Real.pi * ‖relab c σ b (U'.X k').ξ0‖)
  let B : U.Comp → ℝ := fun k =>
    (∏ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (Real.sqrt (κ k p.1))⁻¹ ^ a (p.1, p.2)) * |C k|
  refine ⟨hs', ∑ k, B k, fun x₁ hx₁ => ?_⟩
  obtain ⟨b, hbB, ho⟩ := (FD.orthonormalFlagTranslate_holds r (U'.X k')).1 x₁ hx₁
  have hx' := FD.OrthogonalFrameDomain.rmul_mem_dom (U'.X k') hx₁ hbB
  rw [← (FD.orthonormalFlagTranslate_holds r (U'.X k')).2.1 _ _ hs'.2.1 x₁ hx₁ b hbB,
    PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (PullbackSections.PfSupAtUnit.dmin_ortho _ ho)]
  have hN := isMetric_of_isOrtho E H Dw l Xo c σ r U' hσ hU' hpq k' ⟨_, hx'⟩ ho
  have hrd' : ‖rdU U' f k' (FD.rmul x₁ b)‖ = cabs (evR Xo c f (U'.un k' ⟨_, hx'⟩)) := by
    have e : rdU U' f k' (FD.rmul x₁ b) = toC (evR Xo c f (U'.un k' ⟨_, hx'⟩)) := dif_pos hx'
    rw [e]; rfl
  rw [hrd']
  generalize U'.un k' ⟨_, hx'⟩ = y at hN ⊢
  obtain ⟨k, x, t, hx, ht⟩ := GlobalTheory.T.exists_orthonormalFrame_borelChange_complexFramedPoint E H Dw l Xo c σ r U hU y
  obtain ⟨g, hg0, hgd, hchg⟩ :=
    ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) y y).1 t).1 ht
  have hm0 := isMetric_of_isOrtho E H Dw l Xo c σ r U hσ hU hpq k x hx
  have hm1 := GlobalTheory.T.metric_change_of_frame E H Dw l Xo c σ (U.un k x) y 1 _
    (fun b => Matrix.transpose (show Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ from g b))
    (show ℂ from (t none : CAt σ)) (Units.ne_zero (M₀ := ℂ) (t none)) hchg hm0
  obtain ⟨hNN, hG⟩ := GlobalTheory.T.metric_data_unique E H Dw l Xo c σ y _ _ _ _ hN hm1
  have hnone : cabs (t none : CAt σ) = 1 := by
    rw [_root_.mul_one] at hNN
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hNN.symm
  have hsome : ∀ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), cabs (t (some p) : CAt σ) = (Real.sqrt (κ k p.1))⁻¹ := by
    rintro ⟨τ, i⟩
    rw [← hgd τ i]
    refine OrthoBound.norm_diag_of_triangular
      (Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ)) _
      (div_pos (hpos _ _) (hpos _ _)) (fun i j hij => hg0 τ j i hij) ?_ i
    have h1 := (congrFun hG τ).symm
    have h2 : ((2 * Real.pi * ‖relab c σ τ (U'.X k').ξ0‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos _ _).ne'
    dsimp only at h1
    rw [Complex.ofReal_div, div_eq_inv_mul, mul_smul, Matrix.mul_smul, Matrix.smul_mul, h1, smul_smul,
      inv_mul_cancel₀ h2, one_smul]
  have hev := hwt (CAt σ) (GlobalTheory.FrameNorm.Comparison₂.isReduced_cAt σ) a n f hf t _ _ ht
  have hw : cabs (wchar (ex Dw a n) t) =
      ∏ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (Real.sqrt (κ k p.1))⁻¹ ^ a (p.1, p.2) := by
    rw [GlobalTheory.FrameNorm.Comparison₂.cabs_wchar, Fintype.prod_option, hnone, one_pow, _root_.one_mul]
    exact Finset.prod_congr rfl fun p _ => by rw [hsome p]; rfl
  have hrd : ‖rdU U f k x.1‖ = cabs (evR Xo c f (U.un k x)) := by
    have e : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := dif_pos x.2
    rw [e]; rfl
  have hle := hC k x.1 x.2
  rw [PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (PullbackSections.PfSupAtUnit.dmin_ortho _ hx), hrd] at hle
  have hB0 : ∀ k, 0 ≤ B k := fun k => mul_nonneg (Finset.prod_nonneg fun p _ => by positivity) (abs_nonneg _)
  rw [hev, GlobalTheory.FrameNorm.Comparison₂.cabs_mul, hw]
  exact (mul_le_mul_of_nonneg_left (hle.trans (le_abs_self _)) (Finset.prod_nonneg fun p _ => by positivity)).trans
    (Finset.single_le_sum (f := B) (fun k _ => hB0 k) (Finset.mem_univ k))

end GlobalTheory.SupFull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionTensorIsometricTransShift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionTensorIsometricTransShift
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.CechPic GlobalTheory.Points GlobalTheory.ChartGlue

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem norm_mul_exp_neg_log_normSq {u : ℂ} (hu : u ≠ 0) :
    ‖u‖ * Real.exp (-Real.log (‖u‖ ^ 2) / 2) = 1 := by
  have h : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [Real.log_pow, show -((2 : ℕ) * Real.log ‖u‖) / 2 = -Real.log ‖u‖ by push_cast; ring,
    Real.exp_neg, Real.exp_log h, mul_inv_cancel₀ h.ne']

theorem ratSec_div_eq {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {i j : L.ι}
    (h : genericPoint X ∈ L.U i ⊓ L.U j) :
    (r i : X.functionField) / (r j : X.functionField) = fnOf _ h (L.g i j : Γ(X, L.U i ⊓ L.U j)) := by
  rw [hr i j h, mul_div_cancel_right₀ _ (r j).ne_zero]

theorem regAt_ratSec_div {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {i j : L.ι} {x : X}
    (hi : x ∈ L.U i) (hj : x ∈ L.U j) : RegAt x ((r i : X.functionField) / (r j : X.functionField)) := by
  rw [ratSec_div_eq hr (gen_mem (memInf hi hj))]
  exact regAt_fnOf (memInf hi hj) _ _

theorem ratVal_ratSec_div {σ : k →+* ℂ} {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {i j : L.ι}
    {y : CxPts p σ} (hi : y ∈ ptsIn p σ (L.U i)) (hj : y ∈ ptsIn p σ (L.U j)) :
    ratVal ((r i : X.functionField) / (r j : X.functionField)) y = gv p σ L i j y := by
  have hy := mem_ptsIn_inf.2 ⟨hi, hj⟩
  rw [ratSec_div_eq hr (gen_mem (mem_ptsIn.1 hy)), ratVal_fnOf hy]
  rfl

theorem norm_ratSec_div {σ : k →+* ℂ} {L : LB X} (φ : Weight p σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r)
    {i j : L.ι} {y : CxPts p σ} (hi : y ∈ ptsIn p σ (L.U i)) (hj : y ∈ ptsIn p σ (L.U j)) :
    ‖ratVal ((r i : X.functionField) / (r j : X.functionField)) y‖ * Real.exp (-(φ.φ i y - φ.φ j y) / 2) = 1 := by
  rw [ratVal_ratSec_div hr hi hj, φ.trans i j y hi hj, sub_sub_cancel]
  exact norm_mul_exp_neg_log_normSq (gv_ne_zero hi hj)

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem Le.shift {A B : HermLB p} (t : ℝ) (h : Le B A) :
    Le (B.shift (fun _ => t) fun _ => rfl) (A.shift (fun _ => t) fun _ => rfl) := by
  obtain ⟨r, r', hr, hr', hreg, hn⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).1 h
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p _ _).2 ⟨r, r', hr, hr', hreg, fun σ y i j hi hj => ?_⟩
  have e : ((A.shift (fun _ => t) fun _ => rfl).φ σ).φ i y - ((B.shift (fun _ => t) fun _ => rfl).φ σ).φ j y =
      (A.φ σ).φ i y - (B.φ σ).φ j y := by
    simp only [HermLB.shift, Weight.addFn]; ring
  rw [e]
  exact hn σ y i j hi hj

theorem Le.trans {A B M : HermLB p} (h₁ : Le B A) (h₂ : Le A M) : Le B M := by
  obtain ⟨r₁, r₁', hr₁, hr₁', hreg₁, hn₁⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).1 h₁
  obtain ⟨r₂, r₂', hr₂, hr₂', hreg₂, hn₂⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p M A).1 h₂
  obtain ⟨a₀, h₀⟩ := exists_chart A.isLB (genericPoint X)
  let c : X.functionFieldˣ := r₂' a₀ / r₁ a₀
  have hs : IsRatSec B.B fun j => r₁' j * c := fun i j h => by
    simp only [Units.val_mul]
    rw [hr₁' i j h, mul_assoc]
  have key (a : A.B.ι) (ha : genericPoint X ∈ A.B.U a) (i : M.B.ι) (j : B.B.ι) :
      (r₂ i : X.functionField) / ((r₁' j * c : X.functionFieldˣ) : X.functionField) =
        (r₂ i : X.functionField) / (r₂' a : X.functionField) * ((r₁ a : X.functionField) / (r₁' j : X.functionField)) := by
    have e₁ := hr₁ a a₀ (memInf ha h₀)
    have e₂ := hr₂' a a₀ (memInf ha h₀)
    have n₁ := (r₁ a₀).ne_zero
    have n₂ := (r₂' a₀).ne_zero
    have n₃ := (r₂' a).ne_zero
    have n₄ := (r₁' j).ne_zero
    simp only [c, Units.val_mul, Units.val_div_eq_div_val]
    rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero n₄ (div_ne_zero n₂ n₁)) (mul_ne_zero n₃ n₄), e₁, e₂]
    field_simp
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p M B).2 ⟨r₂, _, hr₂, hs, fun x i j hi hj => ?_, fun σ y i j hi hj => ?_⟩
  · obtain ⟨a, ha⟩ := exists_chart A.isLB x
    rw [key a (gen_mem ha)]
    exact (hreg₂ x i a hi ha).mul (hreg₁ x a j ha hj)
  · have ha := mem_pick (A.φ σ).isLB y
    set a := pick (A.φ σ).isLB y
    have hx := mem_ptsIn.1 ha
    rw [key a (gen_mem hx), ratVal_mul (hreg₂ _ i a (mem_ptsIn.1 hi) hx) (hreg₁ _ a j hx (mem_ptsIn.1 hj)), norm_mul]
    have e : -((M.φ σ).φ i y - (B.φ σ).φ j y) / 2 =
        -((M.φ σ).φ i y - (A.φ σ).φ a y) / 2 + -((A.φ σ).φ a y - (B.φ σ).φ j y) / 2 := by ring
    rw [e, Real.exp_add]
    calc _ = (‖ratVal ((r₂ i : X.functionField) / (r₂' a : X.functionField)) y‖ *
          Real.exp (-((M.φ σ).φ i y - (A.φ σ).φ a y) / 2)) *
        (‖ratVal ((r₁ a : X.functionField) / (r₁' j : X.functionField)) y‖ *
          Real.exp (-((A.φ σ).φ a y - (B.φ σ).φ j y) / 2)) := by ring
      _ ≤ 1 := mul_le_one₀ (hn₂ σ y i a hi ha) (by positivity) (hn₁ σ y a j ha hj)

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem Le.tens {A B : HermLB p} (M : HermLB p) (h : Le B A) : Le (M.tens B) (M.tens A) := by
  obtain ⟨r, r', hr, hr', hreg, hn⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).1 h
  obtain ⟨ρ, hρ⟩ := exists_isRatSec M.isLB
  have hs := ((presents_divOfRatSec M.isLB hρ).tens (presents_divOfRatSec A.isLB hr)).isRatSec
  have hs' := ((presents_divOfRatSec M.isLB hρ).tens (presents_divOfRatSec B.isLB hr')).isRatSec
  have key (c : M.B.ι × A.B.ι) (d : M.B.ι × B.B.ι) :
      ((ρ c.1 * r c.2 : X.functionFieldˣ) : X.functionField) / ((ρ d.1 * r' d.2 : X.functionFieldˣ) : X.functionField) =
        (ρ c.1 : X.functionField) / (ρ d.1 : X.functionField) * ((r c.2 : X.functionField) / (r' d.2 : X.functionField)) := by
    rw [Units.val_mul, Units.val_mul, mul_div_mul_comm]
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p (M.tens A) (M.tens B)).2 ⟨fun c => ρ c.1 * r c.2, fun d => ρ d.1 * r' d.2, hs, hs',
    fun x c d hc hd => ?_, fun σ y c d hc hd => ?_⟩
  · beta_reduce
    erw [key c d]
    exact (regAt_ratSec_div hρ hc.1 hd.1).mul (hreg x c.2 d.2 hc.2 hd.2)
  · have hc' := mem_ptsIn_inf.1 hc
    have hd' := mem_ptsIn_inf.1 hd
    beta_reduce
    erw [key c d]
    rw [ratVal_mul (regAt_ratSec_div hρ (mem_ptsIn.1 hc'.1) (mem_ptsIn.1 hd'.1))
      (hreg _ c.2 d.2 (mem_ptsIn.1 hc'.2) (mem_ptsIn.1 hd'.2)), norm_mul]
    have e : -(((M.tens A).φ σ).φ c y - ((M.tens B).φ σ).φ d y) / 2 =
        -((M.φ σ).φ c.1 y - (M.φ σ).φ d.1 y) / 2 + -((A.φ σ).φ c.2 y - (B.φ σ).φ d.2 y) / 2 := by
      simp only [HermLB.tens, Weight.tens]; ring
    rw [e, Real.exp_add]
    calc _ = (‖ratVal ((ρ c.1 : X.functionField) / (ρ d.1 : X.functionField)) y‖ *
          Real.exp (-((M.φ σ).φ c.1 y - (M.φ σ).φ d.1 y) / 2)) *
        (‖ratVal ((r c.2 : X.functionField) / (r' d.2 : X.functionField)) y‖ *
          Real.exp (-((A.φ σ).φ c.2 y - (B.φ σ).φ d.2 y) / 2)) := by ring
      _ ≤ 1 := by
        rw [norm_ratSec_div (M.φ σ) hρ hc'.1 hd'.1, one_mul]
        exact hn σ y c.2 d.2 hc'.2 hd'.2

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem le_of_isometric {A B : HermLB p} (hi : B.Isometric A) : Le B A := by
  classical
  obtain ⟨w, hw, h⟩ := hi.exists_units
  obtain ⟨r, hr⟩ := exists_isRatSec B.isLB
  obtain ⟨b₀, h₀⟩ := exists_chart B.isLB (genericPoint X)
  let F (U : X.Opens) (u : Γ(X, U)ˣ) : X.functionFieldˣ := gm (𝟙 X) (genericPoint X) U u
  have hF (U : X.Opens) (u : Γ(X, U)ˣ) (hU : genericPoint X ∈ U) : (F U u : X.functionField) = fnOf U hU u.val :=
    gm_val (𝟙 X) _ U hU u
  have hw' (a a' b b') (h₁ : genericPoint X ∈ A.B.U a) (h₂ : genericPoint X ∈ A.B.U a')
      (h₃ : genericPoint X ∈ B.B.U b) (h₄ : genericPoint X ∈ B.B.U b') :
      F _ (w a b) = F _ (A.B.g a a') * (F _ (B.B.g b b'))⁻¹ * F _ (w a' b') :=
    hw _ (𝟙 X) _ a a' b b' h₁ h₂ h₃ h₄
  have hM (a) (h₁ : genericPoint X ∈ A.B.U a) : F _ (A.B.g a a) = 1 := gm_self A.isLB (𝟙 X) _ h₁
  have hL : F _ (B.B.g b₀ b₀) = 1 := gm_self B.isLB (𝟙 X) _ h₀
  have hr' : IsRatSec A.B fun a => F _ (w a b₀) * r b₀ := fun a a' h' => by
    beta_reduce
    rw [← hF, ← Units.val_mul, hw' a a' b₀ b₀ h'.1 h'.2 h₀ h₀, hL, inv_one, mul_one, mul_assoc]
  have key (a b) (h' : genericPoint X ∈ A.B.U a ⊓ B.B.U b) :
      ((F _ (w a b₀) * r b₀ : X.functionFieldˣ) : X.functionField) / (r b : X.functionField) = fnOf _ h' (w a b).val := by
    rw [div_eq_iff (r b).ne_zero, ← hF, hr b b₀ (memInf h'.2 h₀), ← hF _ (B.B.g b b₀), ← Units.val_mul, ← Units.val_mul,
      hw' a a b b₀ h'.1 h'.1 h'.2 h₀, hM a h'.1, one_mul, mul_comm (F _ (B.B.g b b₀))⁻¹, mul_assoc,
      inv_mul_cancel_left]
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).2 ⟨_, r, hr', hr, fun x a b ha hb => ?_, fun σ y a b ha hb => ?_⟩
  · beta_reduce
    rw [key a b (gen_mem (memInf ha hb))]
    exact regAt_fnOf (memInf ha hb) _ _
  · have hab := mem_ptsIn_inf.2 ⟨ha, hb⟩
    beta_reduce
    rw [key a b (gen_mem (mem_ptsIn.1 hab)), ratVal_fnOf hab, h σ a b y ha hb, add_sub_cancel_left, logSq,
      norm_mul_exp_neg_log_normSq (ev_ne_zero hab (Units.isUnit _))]

theorem le_tens_isometric_trans_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ A B M : HermLB p, (Le B A → Le (M.tens B) (M.tens A)) ∧ (B.Isometric A → Le B A) ∧ (Le B A → Le A M → Le B M) ∧
      ∀ t : ℝ, Le B A → Le (B.shift (fun _ => t) fun _ => rfl) (A.shift (fun _ => t) fun _ => rfl) :=
  fun _ _ _ _ _ _ _ _ => ⟨Le.tens _, le_of_isometric, Le.trans, fun t => Le.shift t⟩

end GlobalTheory.HSNef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionTensorIsometricTransShiftStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLBLeBySmallSection_tensor_isometric_trans_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ A B M : HermLB p, (Le B A → Le (M.tens B) (M.tens A)) ∧ (B.Isometric A → Le B A) ∧ (Le B A → Le A M → Le B M) ∧ ∀ t : ℝ, Le B A → Le (B.shift (fun _ => t) fun _ => rfl) (A.shift (fun _ => t) fun _ => rfl) := by
  first | exact @GlobalTheory.HSNef.le_tens_isometric_trans_shift | exact GlobalTheory.HSNef.le_tens_isometric_trans_shift | (intros; apply GlobalTheory.HSNef.le_tens_isometric_trans_shift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasNonzeroSecPowOfAmpleSubAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicMorseExistsSectionAmpleSubGenerated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorseInequalityArithStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorseInequalityArith
namespace GlobalTheory

theorem morse_inequality_arith (d : ℕ) (a b : ℤ) (h g : ℕ → ℕ) (C C' m₀ m₁ : ℕ)
    (H1 : ∀ m : ℕ, m₀ ≤ m → |((d + 1).factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ (d + 1)| ≤
      C * (((d + 1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ (d + 1 - 1)))
    (H2 : ∀ m : ℕ, m₁ ≤ m → |(d.factorial : ℤ) * (g m : ℤ) - b * (m : ℤ) ^ d| ≤
      C' * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)))
    (hab : ((d : ℤ) + 1) * b < a) : ∃ m : ℕ, 1 ≤ m ∧ m * g m < h m := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = C * (d + 1) + (d + 1) * C' * d := ⟨_, rfl⟩
  obtain ⟨m, hm0, hm1, hmK⟩ : ∃ m : ℕ, m₀ ≤ m ∧ m₁ ≤ m ∧ K * 2 ^ d + 1 ≤ m :=
    ⟨m₀ + m₁ + (K * 2 ^ d + 1), by omega, by omega, by omega⟩
  have hm : 1 ≤ m := le_trans (Nat.le_add_left 1 _) hmK
  refine ⟨m, hm, ?_⟩
  by_contra hcon
  have hcon' : (h m : ℤ) ≤ (m : ℤ) * g m := by exact_mod_cast not_lt.mp hcon
  have h1 := (abs_le.mp (H1 m hm0)).1
  have h2 := (abs_le.mp (H2 m hm1)).2
  rw [Nat.add_sub_cancel, Nat.factorial_succ] at h1
  push_cast at h1
  have hM : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hMK : (K : ℤ) * 2 ^ d + 1 ≤ m := by exact_mod_cast hmK
  have hKz : (K : ℤ) = C * ((d : ℤ) + 1) + (d + 1) * C' * d := by rw [hK]; push_cast; ring
  generalize (m : ℤ) = M at *
  have hF : (0 : ℤ) < d.factorial := by exact_mod_cast d.factorial_pos
  have hd : (0 : ℤ) ≤ d := by positivity
  have hA : M * ((d : ℤ) * (M + 1) ^ (d - 1)) ≤ d * (M + 1) ^ d := by
    rcases d with _ | e
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]
      have : (0 : ℤ) ≤ ((e + 1 : ℕ) : ℤ) * (M + 1) ^ e := by positivity
      nlinarith
  have hP : (M + 1) ^ d ≤ 2 ^ d * M ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) d
  have hQ : 0 < M ^ d := by positivity
  have e1 : ((d : ℤ) + 1) * d.factorial * h m ≤ ((d : ℤ) + 1) * d.factorial * (M * g m) :=
    mul_le_mul_of_nonneg_left hcon' (by positivity)
  have e2 : ((d : ℤ) + 1) * M * ((d.factorial : ℤ) * g m - b * M ^ d) ≤
      ((d : ℤ) + 1) * M * (C' * ((d : ℤ) * (M + 1) ^ (d - 1))) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e3 : ((d : ℤ) + 1) * C' * (M * ((d : ℤ) * (M + 1) ^ (d - 1))) ≤
      ((d : ℤ) + 1) * C' * (d * (M + 1) ^ d) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have e4 : (K : ℤ) * (M + 1) ^ d ≤ K * (2 ^ d * M ^ d) :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have e5 : ((K : ℤ) * 2 ^ d + 1) * M ^ d ≤ M * M ^ d :=
    mul_le_mul_of_nonneg_right hMK hQ.le
  have e6 : (((d : ℤ) + 1) * b + 1) * (M * M ^ d) ≤ a * (M * M ^ d) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e7 : (K : ℤ) * (M + 1) ^ d =
      C * ((d + 1) * (M + 1) ^ d) + ((d : ℤ) + 1) * C' * (d * (M + 1) ^ d) := by
    rw [hKz]; ring
  rw [pow_succ' M d] at h1
  linarith

end GlobalTheory
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_lt_of_asymptotic_bounds : ∀ (d : ℕ) (a b : ℤ) (h g : ℕ → ℕ) (C C' m₀ m₁ : ℕ), (∀ m : ℕ, m₀ ≤ m → |((d + 1).factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ (d + 1)| ≤ C * (((d + 1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ (d + 1 - 1))) → (∀ m : ℕ, m₁ ≤ m → |(d.factorial : ℤ) * (g m : ℤ) - b * (m : ℤ) ^ d| ≤ C' * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1))) → ((d : ℤ) + 1) * b < a → ∃ m : ℕ, 1 ≤ m ∧ m * g m < h m := by
  first | exact @GlobalTheory.morse_inequality_arith | exact GlobalTheory.morse_inequality_arith | (intros; apply GlobalTheory.morse_inequality_arith <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicMorseExistsSectionAmpleSubGenerated
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem exists_sec_of_ample_sub_generated :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsGenerated B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  intro k _ _ X _ _ hp d hd L B M hL hB hM e hlt
  have hf := algebraMap_eq_strHom k X
  have := isNoetherian_of_isProjOver hp
  have hsd : suppDim (GlobalTheory.structureModule X) ≤ (d + 1 : ℕ) := by
    rw [suppDim_structureModule]; exact hd
  have hfin := finiteCohTwists_of_isProjOver hf (GlobalTheory.structureModule X) hp
  obtain ⟨s, hs⟩ := IsGenerated.exists_mono_cutHom k (GlobalTheory.structureModule X) hB
  set G := cut (GlobalTheory.structureModule X) hB.isLB s with hG
  haveI : IsFiniteQC G := isFiniteQC_cut (GlobalTheory.structureModule X) hB.isLB s
  obtain ⟨t, ht⟩ := IsGenerated.exists_mono_cutHom k G hB
  have hGd : suppDim G ≤ (d : ℕ) := suppDim_cut_le _ hB.isLB s hsd
  have hcut := interNum_cons_eq_interNum_cut hB.isLB s (P := fun _ : Fin d => L) (fun _ => hL.isLB) hfin
  obtain ⟨C, m₀, hC⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp (d + 1) (GlobalTheory.structureModule X) hsd L hL
  obtain ⟨C', m₁, hC'⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp d G hGd L hL
  rw [hcut] at hlt
  obtain ⟨m, hm1, hm⟩ := GlobalTheory.T.exists_mul_lt_of_asymptotic_bounds d (topSelfIntersection k L (d + 1)) (interNum k G (fun _ : Fin d => L))
    (fun m => hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0)
    (fun m => hdim k (twist G (lbPow L m)) 0) C C' m₀ m₁ hC hC' hlt
  have hcl : cls (lbPow L m) (isLB_lbPow hL.isLB m) =
      cls (lbPow M m) (isLB_lbPow hM m) + m • cls B hB.isLB := by
    rw [cls_lbPow hL.isLB, cls_lbPow hM, e, smul_add]
  have hmono : ∀ (j : ℕ) (M' : LB X) (hM' : M'.IsLB),
      cls (lbPow L m) (isLB_lbPow hL.isLB m) = cls M' hM' + j • cls B hB.isLB →
      hdim k (twist G M') 0 ≤ hdim k (twist G (lbPow L m)) 0 := by
    intro j
    induction j with
    | zero =>
      intro M' hM' h
      rw [zero_nsmul, add_zero] at h
      obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq G (isLB_lbPow hL.isLB m) hM' h
      exact (hdim_congr k 0 e).ge
    | succ j ih =>
      intro M' hM' h
      have h1 := cls_tens hM' hB.isLB (isLB_tens hM' hB.isLB)
      have h2 := ih _ (isLB_tens hM' hB.isLB) (by rw [h1, h, succ_nsmul']; abel)
      exact ((GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hp G B _ M' hB.isLB _ hM' t ht h1).2.2).trans h2
  have hch : ∀ (j : ℕ) (M' : LB X) (hM' : M'.IsLB),
      cls (lbPow L m) (isLB_lbPow hL.isLB m) = cls M' hM' + j • cls B hB.isLB →
      hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 ≤
        hdim k (twist (GlobalTheory.structureModule X) M') 0 + j * hdim k (twist G (lbPow L m)) 0 := by
    intro j
    induction j with
    | zero =>
      intro M' hM' h
      rw [zero_nsmul, add_zero] at h
      obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq (GlobalTheory.structureModule X) (isLB_lbPow hL.isLB m) hM' h
      rw [hdim_congr k 0 e]
      omega
    | succ j ih =>
      intro M' hM' h
      have h1 := cls_tens hM' hB.isLB (isLB_tens hM' hB.isLB)
      have h0 : cls (lbPow L m) (isLB_lbPow hL.isLB m) = cls (tens M' B) (isLB_tens hM' hB.isLB) + j • cls B hB.isLB := by
        rw [h1, h, succ_nsmul']; abel
      have h2 := ih _ (isLB_tens hM' hB.isLB) h0
      have h3 := (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hp (GlobalTheory.structureModule X) B _ M' hB.isLB _ hM' s hs h1).1 0
      change hdim k (twist (GlobalTheory.structureModule X) (tens M' B)) 0 ≤
        hdim k (twist (GlobalTheory.structureModule X) M') 0 + hdim k (twist G (tens M' B)) 0 at h3
      have h4 := hmono j _ (isLB_tens hM' hB.isLB) h0
      rw [Nat.succ_mul]
      omega
  have hch' : hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 ≤
      hdim k (twist (GlobalTheory.structureModule X) (lbPow M m)) 0 + m * hdim k (twist G (lbPow L m)) 0 := hch m (lbPow M m) (isLB_lbPow hM m) hcl
  refine ⟨m, hm1, lineBundleHasNonzeroSection_of_globalSectionsDim_pos (k := k) ?_⟩
  show 0 < hdim k (twist (GlobalTheory.structureModule X) (lbPow M m)) 0
  have : m * hdim k (twist G (lbPow L m)) 0 < hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 := hm
  omega

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicMorseExistsSectionAmpleSubGeneratedStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_morse_exists_section_ample_sub_generated : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsGenerated B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  first | exact @GlobalTheory.exists_sec_of_ample_sub_generated | exact GlobalTheory.exists_sec_of_ample_sub_generated | (intros; apply GlobalTheory.exists_sec_of_ample_sub_generated <;> assumption)
end
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem exists_hasNonzeroSec_pow_of_ample_sub_ample : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsAmpleLB B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  intro k _ _ X _ _ hX d hdim L B M hL hB hM hcls hineq

  have hgen : ∀ᶠ n : ℕ in atTop, IsGenerated (lbPow B n) := by
    filter_upwards [hB.eventually_isGloballyGenerated_twist (LB.unitMod X)] with n hn
    obtain ⟨ι, hι, φ, hφ⟩ := hn
    exact (isGloballyGenerated_toMod_iff (isLB_lbPow hB.isLB n)).1
      ⟨ι, hι, φ ≫ (unitTwistIso (X := X) (L := lbPow B n)).hom, epi_comp _ _⟩
  obtain ⟨m, hmB, hm1⟩ := (hgen.and (eventually_ge_atTop 1)).exists

  have hLm : IsAmpleLB (lbPow L m) := (isAmpleLB_pow_iff hL.isLB hm1).2 hL
  have hMm : (lbPow M m).IsLB := isLB_lbPow hM m
  have hclsm : cls (lbPow L m) hLm.isLB = cls (lbPow M m) hMm + cls (lbPow B m) hmB.isLB := by
    rw [CechPic.cls_lbPow hL.isLB m, CechPic.cls_lbPow hM m, CechPic.cls_lbPow hB.isLB m, hcls,
      smul_add]

  have hv : DiffVanish (d + 1 + 1) (chiPic k (structureModule X)) := by
    exact diffVanish_chiPic_of_isProjOver (f := strHom k X) (algebraMap_eq_strHom k X)
      (structureModule X) hX
      (by
        unfold QCoh.suppDim
        exact (topologicalKrullDim_subspace_le _ _).trans hdim)
  have hprod : (∏ _i : Fin (d + 1), (m : ℤ)) = (m : ℤ) ^ (d + 1) := by simp
  have hP : ∀ i, ((Fin.cons B fun _ : Fin d => L : Fin (d + 1) → LB X) i).IsLB := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hB.isLB
    · exact hL.isLB
  have hQ : ∀ i, ((Fin.cons (lbPow B m) fun _ : Fin d => lbPow L m : Fin (d + 1) → LB X) i).IsLB := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hmB.isLB
    · exact hLm.isLB
  have hI : interNum k (structureModule X)
      (Fin.cons (lbPow B m) fun _ : Fin d => lbPow L m : Fin (d + 1) → LB X) =
      (m : ℤ) ^ (d + 1) * interNum k (structureModule X)
        (Fin.cons B fun _ : Fin d => L : Fin (d + 1) → LB X) := by
    rw [← hprod]
    exact hv.interNum_of_cls_eq_zsmul hP hQ (fun _ => (m : ℤ)) (by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (CechPic.cls_lbPow hB.isLB m _).trans (natCast_zsmul _ _).symm
      · exact (CechPic.cls_lbPow hL.isLB m _).trans (natCast_zsmul _ _).symm)
  have hT : topSelfIntersection k (lbPow L m) (d + 1) = (m : ℤ) ^ (d + 1) * topSelfIntersection k L (d + 1) := by
    rw [topSelf_def, topSelf_def, ← hprod]
    exact hv.interNum_of_cls_eq_zsmul (fun _ => hL.isLB) (fun _ => hLm.isLB) (fun _ => (m : ℤ))
      (fun _ => (CechPic.cls_lbPow hL.isLB m _).trans (natCast_zsmul _ _).symm)
  have hpos : (0 : ℤ) < (m : ℤ) ^ (d + 1) := pow_pos (by exact_mod_cast hm1) _
  have hineqm : ((d : ℤ) + 1) * interNum k (structureModule X)
      (Fin.cons (lbPow B m) fun _ : Fin d => lbPow L m : Fin (d + 1) → LB X) <
      topSelfIntersection k (lbPow L m) (d + 1) := by
    rw [hI, hT, mul_left_comm]
    exact mul_lt_mul_of_pos_left hineq hpos

  obtain ⟨r, hr, hs⟩ :=
    T.algebraic_morse_exists_section_ample_sub_generated k X hX d hdim (lbPow L m) (lbPow B m) (lbPow M m) hLm hmB hMm hclsm hineqm
  refine ⟨m * r, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  refine hs.of_cls_eq (isLB_lbPow hM (m * r)) (isLB_lbPow hMm r) ?_
  rw [CechPic.cls_lbPow hM (m * r), CechPic.cls_lbPow hMm r, CechPic.cls_lbPow hM m, smul_smul,
    mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInverseThetaTransformOnRealTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInverseThetaTransformOnRealTranslates
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.ThetaTransform.RealSchwartz

private theorem norm_add_smul_single_sub_le_of_hasDerivAt_bound {k : ℕ} (φ : (Fin k → ℝ) → ℂ) (φ' : Fin k → (Fin k → ℝ) → ℂ)
    (hd : ∀ i t, HasDerivAt (fun s : ℝ => φ (t + s • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' i t) 0)
    (B : Fin k → ℝ) (hB : ∀ i t, ‖φ' i t‖ ≤ B i) (i : Fin k) (t : Fin k → ℝ) (a : ℝ) :
    ‖φ (t + a • (Pi.single i (1 : ℝ) : Fin k → ℝ)) - φ t‖ ≤ B i * |a| := by
  set e : Fin k → ℝ := Pi.single i (1 : ℝ) with he
  have hder : ∀ s : ℝ, HasDerivAt (fun u : ℝ => φ (t + u • e)) (φ' i (t + s • e)) s := by
    intro s
    have h0 : HasDerivAt (fun u : ℝ => φ (t + s • e + u • e)) (φ' i (t + s • e)) (s - s) := by
      rw [sub_self]; exact hd i (t + s • e)
    have h1 := HasDerivAt.scomp (h := fun u : ℝ => u - s) s h0 ((hasDerivAt_id' s).sub_const s)
    rw [one_smul] at h1
    have hf : (fun u : ℝ => φ (t + u • e)) = ((fun u : ℝ => φ (t + s • e + u • e)) ∘ fun u : ℝ => u - s) := by
      funext u
      simp only [Function.comp_apply]
      congr 1
      rw [sub_smul]; abel
    rw [hf]
    exact h1
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.univ)
    (f := fun u : ℝ => φ (t + u • e)) (f' := fun s => φ' i (t + s • e))
    (fun s _ => (hder s).hasDerivWithinAt) (fun s _ => hB i _) convex_univ (Set.mem_univ 0) (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using h

theorem continuous_of_bdd_partials {k : ℕ} (φ : (Fin k → ℝ) → ℂ) (φ' : Fin k → (Fin k → ℝ) → ℂ)
    (hd : ∀ i t, HasDerivAt (fun s : ℝ => φ (t + s • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' i t) 0)
    (B : Fin k → ℝ) (hB : ∀ i t, ‖φ' i t‖ ≤ B i) : Continuous φ := by

  have hB0 : ∀ i, 0 ≤ B i := fun i => (norm_nonneg _).trans (hB i 0)
  set M : ℝ := ∑ i, B i with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => hB0 i
  have hBM : ∀ i, B i ≤ M := fun i => Finset.single_le_sum (fun j _ => hB0 j) (Finset.mem_univ i)

  have key : ∀ x y : Fin k → ℝ, ‖φ y - φ x‖ ≤ (k * M) * ‖y - x‖ := by
    intro x y
    let p : ℕ → Fin k → ℝ := fun j l => if (l : ℕ) < j then y l else x l
    have hp0 : p 0 = x := by funext l; simp [p]
    have hpk : p k = y := by funext l; simp [p, l.isLt]
    have hstep : ∀ j (hj : j < k), p (j + 1) =
        p j + (y ⟨j, hj⟩ - x ⟨j, hj⟩) • (Pi.single (⟨j, hj⟩ : Fin k) (1 : ℝ) : Fin k → ℝ) := by
      intro j hj
      funext l
      simp only [p, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      by_cases h : l = ⟨j, hj⟩
      · subst h; simp
      · have hne : (l : ℕ) ≠ j := fun h' => h (Fin.ext h')
        simp only [h, ↓reduceIte, mul_zero, add_zero]
        by_cases hl : (l : ℕ) < j
        · simp [hl, show (l : ℕ) < j + 1 by omega]
        · simp [hl, show ¬ (l : ℕ) < j + 1 by omega]
    have hind : ∀ j, j ≤ k → ‖φ (p j) - φ x‖ ≤ j * (M * ‖y - x‖) := by
      intro j
      induction j with
      | zero => intro _; simp [hp0]
      | succ j ih =>
        intro hj
        have hjk : j < k := hj
        have h1 := norm_add_smul_single_sub_le_of_hasDerivAt_bound φ φ' hd B hB ⟨j, hjk⟩ (p j) (y ⟨j, hjk⟩ - x ⟨j, hjk⟩)
        rw [← hstep j hjk] at h1
        have hc : |y ⟨j, hjk⟩ - x ⟨j, hjk⟩| ≤ ‖y - x‖ := by
          have := norm_le_pi_norm (y - x) ⟨j, hjk⟩
          simpa [Real.norm_eq_abs] using this
        have h2 : B ⟨j, hjk⟩ * |y ⟨j, hjk⟩ - x ⟨j, hjk⟩| ≤ M * ‖y - x‖ :=
          mul_le_mul (hBM _) hc (abs_nonneg _) hM0
        calc ‖φ (p (j + 1)) - φ x‖ ≤ ‖φ (p (j + 1)) - φ (p j)‖ + ‖φ (p j) - φ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ M * ‖y - x‖ + j * (M * ‖y - x‖) := add_le_add (h1.trans h2) (ih (by omega))
          _ = ((j + 1 : ℕ) : ℝ) * (M * ‖y - x‖) := by push_cast; ring
    have := hind k le_rfl
    rw [hpk] at this
    calc ‖φ y - φ x‖ ≤ k * (M * ‖y - x‖) := this
      _ = (k * M) * ‖y - x‖ := by ring
  refine (LipschitzWith.of_dist_le' (K := (k : ℝ) * M) fun x y => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  exact key y x

end GlobalTheory.ThetaTransform.RealSchwartz

namespace GlobalTheory.ThetaTransform.RealSchwartz

variable {F : Type} [Field F] [NumberField F]

theorem continuous_mixedSpace_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  apply continuous_pi
  intro v
  by_cases hv : v.IsReal
  · have hE := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding
    refine hE.isInducing.continuous_iff.2 ?_
    have h : (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv ∘
        fun y => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v) = fun y => y.1 ⟨v, hv⟩ := by
      funext y
      have h0 := congrArg (fun z => z.1 ⟨v, hv⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
      rw [Function.comp_apply]
      exact h0
    rw [h]
    exact (continuous_apply _).comp continuous_fst
  · have hc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hv
    have hE := (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding
    refine hE.isInducing.continuous_iff.2 ?_
    have h : (InfinitePlace.Completion.extensionEmbedding v ∘
        fun y => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v) = fun y => y.2 ⟨v, hc⟩ := by
      funext y
      have h0 := congrArg (fun z => z.2 ⟨v, hc⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
      rw [Function.comp_apply]
      exact h0
    rw [h]
    exact (continuous_apply _).comp continuous_snd

theorem embR_add {N : ℕ} (a b : Fin N → mixedEmbedding.mixedSpace F) :
    (embR (a + b) : Fin N → AF F) = embR a + embR b := by
  funext i
  simp only [embR, Pi.add_apply, map_add (f := _)]
  exact (congrArg (pairA F _) (add_zero (0 : Af F))).symm.trans rfl

theorem embR_zero {N : ℕ} : (embR (0 : Fin N → mixedEmbedding.mixedSpace F) : Fin N → AF F) = 0 := by
  funext i
  simp only [embR, pairA, Pi.zero_apply, map_zero]
  rfl

theorem continuous_embR {N : ℕ} : Continuous (embR : (Fin N → mixedEmbedding.mixedSpace F) → Fin N → AF F) := by
  apply continuous_pi
  intro i
  show Continuous fun t : Fin N → mixedEmbedding.mixedSpace F =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  exact (continuous_mixedSpace_symm.comp (continuous_apply i)).prodMk continuous_const

theorem fin_embR {N : ℕ} (t : Fin N → mixedEmbedding.mixedSpace F) : fin (embR t : Fin N → AF F) = 0 := by
  funext l
  first
  | rfl
  | simp [fin, embR, pairA, sndA]

def lineR {N : ℕ} (v : Fin N → mixedEmbedding.mixedSpace F) : ℝ →+ VA F N where
  toFun s := (embR (s • v), 0)
  map_zero' := by rw [zero_smul, embR_zero]; rfl
  map_add' a b := by rw [add_smul, embR_add, Prod.mk_add_mk, add_zero]

theorem isRealLine_lineR {N : ℕ} (v : Fin N → mixedEmbedding.mixedSpace F) : IsRealLine (lineR v) := by
  refine ⟨?_, fun t => ⟨fin_embR (t • v), ?_⟩⟩
  · show Continuous fun s : ℝ => ((embR (s • v), 0) : VA F N)
    exact (continuous_embR.comp (continuous_id.smul continuous_const)).prodMk continuous_const
  · funext l
    first
    | rfl
    | simp [fin, sndA]

end GlobalTheory.ThetaTransform.RealSchwartz

namespace GlobalTheory.ThetaTransform


open RealSchwartz in
theorem schwartz_invV_realTranslate : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ 𝒱 : Set (VA F N → ℂ), (∀ f ∈ 𝒱, Continuous f ∧ QuasiV ψ f ∧ ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) → (∀ f ∈ 𝒱, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ f' ∈ 𝒱, ∀ x, HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0) → (∀ f ∈ 𝒱, ∀ (x : Fin N → AF F) (k : ℕ), ∃ C : ℝ, ∀ t : Fin N → mixedEmbedding.mixedSpace F, ‖t‖ ^ k * ‖invV ψ ν 𝓓 f (x + embR t)‖ ≤ C) → ∀ f ∈ 𝒱, ∀ x : Fin N → AF F, ∃ g : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = invV ψ ν 𝓓 f (x + embR t) := by
  intro F _ _ N _ ψ lam ν _ 𝓓 _ _ 𝒱 _ hder hdec f hf x

  let E := Fin N → mixedEmbedding.mixedSpace F
  let L : (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] E :=
    (Module.finBasis ℝ E).equivFun.symm.toContinuousLinearEquiv

  let V : Set ((Fin (Module.finrank ℝ E) → ℝ) → ℂ) :=
    {φ | ∃ g ∈ 𝒱, φ = fun s => invV ψ ν 𝓓 g (x + embR (L s))}

  have hpart : ∀ g ∈ 𝒱, ∀ i : Fin (Module.finrank ℝ E), ∃ g' ∈ 𝒱, ∀ s,
      HasDerivAt (fun u : ℝ => invV ψ ν 𝓓 g (x + embR (L (s + u • (Pi.single i (1 : ℝ) : Fin _ → ℝ)))))
        (invV ψ ν 𝓓 g' (x + embR (L s))) 0 := by
    intro g hg i
    obtain ⟨g', hg', hd⟩ := hder g hg (lineR (L (Pi.single i (1 : ℝ)))) (isRealLine_lineR _)
    refine ⟨g', hg', fun s => ?_⟩
    have h := hd (x + embR (L s))
    have heq : (fun u : ℝ => invV ψ ν 𝓓 (heisV ψ (lineR (L (Pi.single i (1 : ℝ))) u) g) (x + embR (L s))) =
        fun u : ℝ => invV ψ ν 𝓓 g (x + embR (L (s + u • (Pi.single i (1 : ℝ) : Fin _ → ℝ)))) := by
      funext u
      rw [show lineR (L (Pi.single i (1 : ℝ))) u = (embR (u • L (Pi.single i (1 : ℝ))), 0) from rfl,
        invV_heisV_fst, map_add, map_smul, embR_add, add_assoc]
    rwa [heq] at h

  have hcont : ∀ φ ∈ V, Continuous φ := by
    rintro φ ⟨g, hg, rfl⟩
    choose g' hg' hd' using hpart g hg
    have hb : ∀ i, ∃ C : ℝ, ∀ s, ‖invV ψ ν 𝓓 (g' i) (x + embR (L s))‖ ≤ C := by
      intro i
      obtain ⟨C, hC⟩ := hdec (g' i) (hg' i) x 0
      exact ⟨C, fun s => by simpa using hC (L s)⟩
    choose B hB using hb
    exact continuous_of_bdd_partials _ (fun i s => invV ψ ν 𝓓 (g' i) (x + embR (L s)))
      (fun i t => hd' i t) B hB
  have hclosed : ∀ φ ∈ V, ∀ i : Fin (Module.finrank ℝ E), ∃ φ' ∈ V, ∀ s : Fin (Module.finrank ℝ E) → ℝ,
      HasDerivAt (fun u : ℝ => φ (s + u • (Pi.single i (1 : ℝ) : Fin _ → ℝ))) (φ' s) 0 := by
    rintro φ ⟨g, hg, rfl⟩ i
    obtain ⟨g', hg', hd'⟩ := hpart g hg i
    exact ⟨_, ⟨g', hg', rfl⟩, hd'⟩

  have hdecV : ∀ φ ∈ V, ∀ n : ℕ, ∃ C : ℝ, ∀ s, ‖s‖ ^ n * ‖φ s‖ ≤ C := by
    rintro φ ⟨g, hg, rfl⟩ n
    obtain ⟨C, hC⟩ := hdec g hg x n
    refine ⟨‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ ^ n * C, fun s => ?_⟩
    have hs : ‖s‖ ≤ ‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ * ‖L s‖ := by
      have h := (L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)).le_opNorm (L s)
      simpa using h
    calc ‖s‖ ^ n * ‖invV ψ ν 𝓓 g (x + embR (L s))‖
        ≤ (‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ * ‖L s‖) ^ n *
            ‖invV ψ ν 𝓓 g (x + embR (L s))‖ := by gcongr
      _ = ‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ ^ n *
            (‖L s‖ ^ n * ‖invV ψ ν 𝓓 g (x + embR (L s))‖) := by ring
      _ ≤ ‖(L.symm : E →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ))‖ ^ n * C := by
            gcongr
            exact hC (L s)
  obtain ⟨_, hS⟩ := GlobalTheory.Unf.PartialClass.smooth_schwartz _ V hcont hclosed
  obtain ⟨g0, hg0⟩ := hS hdecV _ ⟨f, hf, rfl⟩
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm g0, fun t => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg0]
  show invV ψ ν 𝓓 f (x + embR (L (L.symm t))) = _
  rw [L.apply_symm_apply]

end GlobalTheory.ThetaTransform
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInverseThetaTransformOnRealTranslatesStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_inverse_theta_transform_on_real_translates : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ 𝒱 : Set (VA F N → ℂ), (∀ f ∈ 𝒱, Continuous f ∧ QuasiV ψ f ∧ ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) → (∀ f ∈ 𝒱, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ f' ∈ 𝒱, ∀ x, HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0) → (∀ f ∈ 𝒱, ∀ (x : Fin N → AF F) (k : ℕ), ∃ C : ℝ, ∀ t : Fin N → mixedEmbedding.mixedSpace F, ‖t‖ ^ k * ‖invV ψ ν 𝓓 f (x + embR t)‖ ≤ C) → ∀ f ∈ 𝒱, ∀ x : Fin N → AF F, ∃ g : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = invV ψ ν 𝓓 f (x + embR t) := by
  first | exact @GlobalTheory.ThetaTransform.schwartz_invV_realTranslate | exact GlobalTheory.ThetaTransform.schwartz_invV_realTranslate | (intros; apply GlobalTheory.ThetaTransform.schwartz_invV_realTranslate <;> assumption)
end
end
