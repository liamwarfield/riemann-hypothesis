module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EntRCloudSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentRepresentation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.WtShape

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem laOf_real (τ : Psi p.T.Q.H) (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) (n : Fin ((dat p i).p + (dat p i).q)) :
    (laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ n : ℝ) = entR D i t n := by
  rw [← ent_cast, ← laOf_read p i τ t ht n, Rat.cast_intCast]

theorem anchor_real (τ : Psi p.T.Q.H) (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) :
    (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) = entR D i t (D.R.k - 1 - 1) := by
  have h : D.R.k - 1 - 1 < (dat p i).p + (dat p i).q := by
    have := D.R.m_add_three_le_k
    rw [dat_p]; omega
  unfold anchor
  rw [dite_eq_left h, laOf_real p i τ t ht]

theorem uW_real (τ : Psi p.T.Q.H) (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) (n : Fin ((dat p i).p + (dat p i).q)) :
    (uW p i τ n : ℝ) = entR D i t n - entR D i t (D.R.k - 1 - 1) := by
  rw [← laOf_real p i τ t ht n, ← anchor_real p i τ t ht, ← Int.cast_sub]
  rfl

theorem h0_eq : LevelStarExponents.h0 L = (p.h0 : ℝ) := by
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast p.hm
  unfold LevelStarExponents.h0
  rw [p.hh0]
  field_simp

theorem wtNum_at (P : ParameterChoice' D L) (T : ParamsT D L P) (hS : SizesAt L) (hx8 : 8 ≤ L.sc.x)
    (hy : 3 ≤ L.sc.x ^ (L.sc.eps / 4)) : WtNum p i T.PP := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have e1 := dat_p p i
  have e2 := dat_q p i
  have e3 := dat_rank p i
  have hD : dimFlag (dat p i) = T.Dp := (dim_eq p i).trans T.Dp_eq.symm
  have hlx : 2 ≤ Real.log L.sc.x := by
    have h1 : Real.log 8 ≤ Real.log L.sc.x := Real.log_le_log (by norm_num) hx8
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at h1
    have := Real.log_two_gt_d9
    push_cast at h1
    linarith
  have hL3 : 3 ≤ L.sc.L :=
    hy.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [L.sc.eps_pos]))
  have hwin := size_window D L hS hlx ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2
  have hP := forty_le_PP T
  have hPt := (parameterPrecision_le_length_and_rank D L P T (by linarith) (one_le_nWn D L P T)).2
  have hwid := mul_widths_le D L T.PP (by linarith) hS (by linarith) hy
  have hS0 := L.Sc_pos
  have hη0 := L.etaSz_pos
  have h40 : 40 * (L.Sc + L.etaSz) ≤ L.sc.w'' D.R.n := le_trans (mul_le_mul_of_nonneg_right hP (by linarith)) hwid
  have hrη : (D.R.r : ℝ) ≤ L.etaSz := by
    refine le_trans ?_ P.t_le_eta
    exact_mod_cast (by have := D.R.rank_add_five_le; omega : D.R.r ≤ D.R.t)
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have hlen : lenT p i T.PP ≤ T.TO := by
    unfold lenT; rw [hD]; exact Nat.ceil_le.2 (len_le D L P T)
  have hlen' : 4 * T.Dp + 4 ≤ lenT p i T.PP := by
    unfold lenT; rw [hD]; exact len_ge T
  obtain ⟨s1, s2, s3⟩ := spacing_ge T ((i : ℕ) + 1) _ hlen
  obtain ⟨q1, q2, q3⟩ := prod_bounds T _ hlen
  obtain ⟨g1, g2⟩ := gap_le D L P T (lenT p i T.PP) (Nat.cast_nonneg _) (by exact_mod_cast hlen)
  have hh : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη0.le (by exact_mod_cast (by omega : 1 ≤ D.R.m))
  have hstep : ∀ t a, a + 1 < D.R.r → ((lenT p i T.PP : ℝ) + T.Dp + 2) * (lenT p i T.PP + T.Dp + 2 + 2 * (D.R.r : ℝ)) + 1 ≤
      sgR D t a - sgR D t (a + 1) := fun t a ha =>
    sgR_step D L P t _ g1 g2
      (fun hm => le_trans g2 (minimalGap_le_first_lowerRowParameter D L P _ (Nat.le_add_left _ _) i.2 t (hwin t).1 hm)) a ha
  have hstep1 : ∀ t a, a + 1 < D.R.r → 1 ≤ sgR D t a - sgR D t (a + 1) := fun t a ha =>
    le_trans (le_add_of_nonneg_left (by positivity)) (hstep t a ha)
  have hent : ∀ t n, n < D.R.r → |entR D i t n| ≤ 3 * L.sc.b := by
    intro t n hn
    obtain ⟨w1, w2⟩ := hwin t
    by_cases h : n < D.R.k - 1
    · obtain ⟨a1, a2⟩ := entR_cloud L i t n h
      rw [abs_le]; constructor <;> linarith
    · have := entR_node L i t n (by omega) hn
      linarith
  have hanc : ∀ t, L.sc.w'' D.R.n - D.R.r ≤ entR D i t (D.R.k - 1 - 1) := fun t => by
    have := (entR_cloud L i t (D.R.k - 1 - 1) (by omega)).1
    linarith [(hwin t).1]
  have hc0 : (0 : ℝ) ≤ cZeroN D ((i : ℕ) + 1) := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ lenT p i T.PP := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ T.Dp := Nat.cast_nonneg _
  have eN : ((((dat p i).p + (dat p i).q : ℕ)) : ℝ) = D.R.r := by rw [e3]
  have eZ : ((((dat p i).p + (dat p i).q : ℕ)) : ℤ) = D.R.r := by rw [e3]
  refine ⟨⟨e1, e2, e3⟩, card_psi p, dim_eq p i, cols_eq p i, dom_wtA _, unit_eq p, ?_, ?_, ?_, ?_, fun him => ?_⟩
  · rw [ofRecord_logOm]; exact abs_logOm_le hS hL3
  · intro τ n
    obtain ⟨t, ht⟩ := exists_tau p τ
    rw [laOf_real p i τ t ht]
    have := hent t n (e3 ▸ n.2)
    have := abs_nonneg (entR D i t n)
    linarith
  · intro τ
    obtain ⟨t, ht⟩ := exists_tau p τ
    rw [anchor_real p i τ t ht]
    linarith [hanc t]
  · rw [hD]; exact ⟨q2, q3⟩
  rw [h0_eq p] at s1 s2 s3 q1 hh
  refine ⟨p.h0, L.Sc, L.etaSz, hS0.le, hη0.le, by linarith, by exact_mod_cast s3, by rw [hD]; exact_mod_cast q1, fun u1 => ?_⟩
  refine ⟨show 1 ≤ D.R.k - 1 by omega, show D.R.k - 1 < (dat p i).p by omega, show (dat p i).p < _ by omega,
    show _ - (dat p i).p < (dat p i).p by omega, Int.natCast_nonneg _, fun τ a ha => uWt_anchor _ _ _ _ τ a ha,
    show 4 * dimFlag (dat p i) + 4 ≤ lenT p i T.PP by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 4 * ((cZeroN D ((i : ℕ) + 1) : ℤ) + 2 * ((dat p i).p + (dat p i).q : ℕ) + lenT p i T.PP + dimFlag (dat p i) + 1) ≤ p.h0 ∧
      24 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) * lenT p i T.PP ≤ p.h0
    rw [hD, eZ]
    exact ⟨by exact_mod_cast s1, by exact_mod_cast s2⟩
  · intro τ a ha
    obtain ⟨t, ht⟩ := exists_tau p τ
    show |(uW p i τ a : ℝ) + (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)| ≤
      L.etaSz + L.Sc + ((dat p i).p + (dat p i).q : ℕ)
    rw [uW_real p i τ t ht, anchor_real p i τ t ht, sub_add_cancel, eN]
    have := entR_node L i t a ha (e3 ▸ a.2)
    linarith
  · intro τ a ha
    obtain ⟨t, ht⟩ := exists_tau p τ
    show 0 ≤ uW p i τ a ∧ (uW p i τ a : ℝ) ≤ L.Sc
    obtain ⟨a1, a2⟩ := entR_cloud_sub L i t (hstep1 t) a ha
    rw [← uW_real p i τ t ht] at a1 a2
    exact ⟨by exact_mod_cast a1, a2⟩
  · intro τ
    obtain ⟨t, ht⟩ := exists_tau p τ
    show 4 * ((L.etaSz + L.Sc + ((dat p i).p + (dat p i).q : ℕ)) + L.Sc + ((cZeroN D ((i : ℕ) + 1) : ℤ) : ℝ) +
      2 * ((dat p i).p + (dat p i).q : ℕ)) + 20 * ((dat p i).p + (dat p i).q : ℕ) * (lenT p i T.PP : ℝ) ≤
      (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)
    rw [anchor_real p i τ t ht, eN, Int.cast_natCast]
    have := hanc t
    have h5 : 0 ≤ (D.R.r : ℝ) * lenT p i T.PP := by positivity
    nlinarith
  · intro τ a b hab
    obtain ⟨t, ht⟩ := exists_tau p τ
    have hb := b.2
    have hd : ((uW p i τ a - uW p i τ b : ℤ) : ℝ) =
        sgR D t a - sgR D t (a + 1) - 1 + if (a : ℕ) + 1 = D.R.k + i then (D.R.r : ℝ) else 0 := by
      rw [Int.cast_sub, uW_real p i τ t ht, uW_real p i τ t ht, hab, ← entR_step]; ring
    have hge : sgR D t a - sgR D t (a + 1) - 1 ≤ ((uW p i τ a - uW p i τ b : ℤ) : ℝ) := by
      rw [hd]; split_ifs <;> linarith
    refine ⟨fun _ => ?_, fun ha => ?_, fun hp => ?_⟩
    · show ((lenT p i T.PP : ℤ) + dimFlag (dat p i) + 2) *
        ((lenT p i T.PP : ℤ) + dimFlag (dat p i) + 2 + 2 * ((dat p i).p + (dat p i).q : ℕ)) ≤ uW p i τ a - uW p i τ b + 2
      rw [hD, eZ]
      have := hstep t a (by omega)
      have h2 : ((lenT p i T.PP : ℝ) + T.Dp + 2) * (lenT p i T.PP + T.Dp + 2 + 2 * (D.R.r : ℝ)) ≤
        ((uW p i τ a - uW p i τ b : ℤ) : ℝ) + 2 := by linarith
      exact_mod_cast h2
    · show (p.h0 : ℤ) - 1 ≤ uW p i τ a - uW p i τ b
      have := sgR_step_low D L P t a ha (by omega)
      rw [h0_eq p] at this
      have h2 : (p.h0 : ℝ) - 1 ≤ ((uW p i τ a - uW p i τ b : ℤ) : ℝ) := by linarith
      exact_mod_cast h2
    · show (p.h0 : ℤ) ≤ uW p i τ a - uW p i τ b
      have hp' : (b : ℕ) = (dat p i).p := hp
      have := sgR_step_low D L P t a (by omega) (by omega)
      rw [h0_eq p] at this
      rw [if_pos (by omega)] at hd
      have c6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast six_le_r D.R
      have h2 : (p.h0 : ℝ) ≤ ((uW p i τ a - uW p i τ b : ℤ) : ℝ) := by linarith
      exact_mod_cast h2
  · intro τ a
    obtain ⟨t, ht⟩ := exists_tau p τ
    show |(uW p i τ a : ℝ)| + ((cZeroN D ((i : ℕ) + 1) : ℤ) : ℝ) + 4 * ((dat p i).p + (dat p i).q : ℕ) ≤ 2 * (4 * L.sc.b)
    rw [uW_real p i τ t ht, eN, Int.cast_natCast]
    have a1 := hent t a (e3 ▸ a.2)
    have a2 := hent t (D.R.k - 1 - 1) (by omega)
    have a3 := abs_sub (entR D i t a) (entR D i t (D.R.k - 1 - 1))
    obtain ⟨w1, w2⟩ := hwin t
    linarith

theorem wtN : WtN := by
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, le_rfl, max 8 ((3 : ℝ) ^ (4 / eps)), fun x hx hle ι p _ i => ?_⟩⟩⟩
  refine wtNum_at p i (Fm.params x hx ι) (Fm.parT x hx ι) (Fm.sizes x hx ι) ?_ ?_
  · rw [Fm.L_x x ι hx]; exact (le_max_left _ _).trans hle
  · rw [Fm.L_x x ι hx, Fm.L_eps x ι]
    have h3 : ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) = 3 := by
      rw [← Real.rpow_mul (by norm_num)]
      have : 4 / eps * (eps / 4) = 1 := by field_simp
      rw [this, Real.rpow_one]
    calc (3 : ℝ) = ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) := h3.symm
      _ ≤ x ^ (eps / 4) := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hle) (by positivity)

end GlobalTheory.CovTop.WtShape

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHoldsStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_bound_holds : WtN := by
  first | exact @GlobalTheory.CovTop.WtShape.wtN | exact GlobalTheory.CovTop.WtShape.wtN | (intros; apply GlobalTheory.CovTop.WtShape.wtN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.LogPole

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev toBase (TF : TorFlag Xo c) (Z : Comp Xo c) : Y₀ TF.X Z ⟶ TF.Y.X := inc₀ TF.X Z ≫ TF.X.π

def IsEigBasis (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) : Prop :=
  (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧
    (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' →
      ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧
    ∀ (a : 𝓞 E) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsCombAtG TF.Y.t (LogKS.chart U) v
      (Pi.single (e ⟨τ, i⟩) (algX TF.Y.s U.1 (embK c τ a))) (v (e ⟨τ, i⟩) ≫ (TF.Y.t.act.act a).left)

def IsCell (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J)
    (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) : Prop :=
  IsAffineOpen W ∧ W ≤ toBase TF Z ⁻¹ᵁ U.1 ∧ W ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k ∧
    (∀ σ i j, i < j → L σ i j = 0) ∧ (∀ σ i, IsUnit (L σ i i)) ∧
    (∀ σ i j, j < i → N σ i j = 0) ∧ (∀ σ i, N σ i i = 1) ∧
    ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1)
      (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z)
      (σ : E →+* ℂ) (i : Fin (Dw.mult σ)),
      IsCombAtG TF.Y.t (z ≫ toBase TF Z)
        (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩))
        (fun j => ev z W hz ((L σ * N σ) i j)) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left

def cellCoord {R : Type} (N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) R) (a : VIx Dw) : R :=
  N a.1 a.2.1.1 a.2.1.2

def IsBaseFrame (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) {K : Type} [CommRing K] [Algebra c.F K]
    (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) : Prop :=
  ∀ σ i, (tv (frVec TF.Y P rfl σ i)).left = spMap (dualMap (ev (frX P ≫ TF.Y.j) U.1 hU)) ≫ v (e ⟨σ, i⟩)

def KSCompare (TF : TorFlag Xo c) (s : ℚ) : Prop :=
  ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v →
    ∀ (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)
      (Θ : Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1)), LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v D.1 Θ →
    ∀ (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1),
      IsBaseFrame TF U e v P hU →
    ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1),
      y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) →
      (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) +
        TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D.1 r))) →
      FlagTan.IsKS (psiSet H) P (y' ≫ pullback.fst _ _) fun k =>
        (s : K) * ev (frX P ≫ TF.Y.j) U.1 hU (Θ (e ⟨k.1.1, k.2.2⟩) (e ⟨conjEmb k.1.1, k.2.1⟩))

def logDet {R : Type} [CommRing R] {m : ℕ} (b : Fin m → Derivation ℤ R R) (x : Fin m → R) : R :=
  (Matrix.of fun i j => b j (x i)).det

end GlobalTheory.LogPole
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O

namespace GlobalTheory.CoverNorm

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def Norms (V : Cover Y) (L : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ)
    (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) : Prop :=
  ∃ r : (L.B.pull V.j).ι → V.G.functionFieldˣ, IsRatSec (L.B.pull V.j) r ∧
    (∀ i, ∀ x ∈ (L.B.pull V.j).U i, UnitAt x (V.φ (f (V.π x)) * r i)) ∧
    (∀ (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F)))
      (i : (L.B.pull V.j).ι), y.1 = z.1 ≫ V.π → y'.1 = z.1 ≫ V.j → under z ∈ (L.B.pull V.j).U i →
      a σ y = Real.log ‖ratVal (V.φ (f (under y)) * (r i : V.G.functionField)) z‖ - (L.φ _).φ (i PUnit.unit) y' / 2) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X)
      (i : (L.B.pull V.j).ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit) →
      l v e y = Real.log (e.w (valAt z (V.φ (f (below y.1)) * (r i : V.G.functionField))))

end GlobalTheory.CoverNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTCount

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R] {b : GlobalTheory.UPel.HT.Base D R}
  {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R}

def crysAct (o₀ : GlobalTheory.UPel.HT.Obj b N t) : D.O →+* Module.End k (HdR o₀.A) :=
  RingHom.mk'
    { toFun x := haveI := o₀.act.hom x; push (dp0 k) (𝟙 _) (o₀.act.act x)
      map_one' := by
        haveI := o₀.act.hom 1
        exact (push_congr (dp0 k) (𝟙 _) o₀.act.one).trans (push_id (dp0 k) (𝟙 _))
      map_mul' x y := by
        haveI := o₀.act.hom
        exact (push_congr (dp0 k) (𝟙 _) (o₀.act.mul x y)).trans (push_comp (dp0 k) (𝟙 _) _ _) }
    fun x y ↦ by
      haveI := o₀.act.hom
      haveI : IsMonHom (o₀.act.act x * o₀.act.act y) := o₀.act.add x y ▸ o₀.act.hom _
      exact (push_congr (dp0 k) (𝟙 _) (o₀.act.add x y)).trans (push_mul (dp0 k) (𝟙 _) _ _)

theorem crysAct_apply (o₀ : GlobalTheory.UPel.HT.Obj b N t) (x : D.O) :
    crysAct o₀ x = (haveI := o₀.act.hom x; push (dp0 k) (𝟙 _) (o₀.act.act x)) := rfl

def rhoPart (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) : Submodule k (HdR o₀.A) :=
  LinearMap.range (crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : k) - β b.ρ) • 1)

def lieZ (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) : Submodule k (HdR o₀.A) :=
  Submodule.span k {z | ∃ (r : ℕ) (lam : Fin r → k) (c : Fin r → 𝓞 D.F) (y : HdR o₀.A), y ∈ rhoPart o₀ β ∧
    (∀ i, ∑ l, lam l * β (b.t i (c l)) = 0) ∧ z = ∑ l, lam l • crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) y}

end GlobalTheory.HTCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianPrim

variable {R : Type} [CommRing R]

theorem pullOver_one_eq_zero {Y A : Over (Sp R)} [GrpObj A] (c : FirstDeRham (A.hom ≫ 𝟙 _)) :
    pullOver (dp0 R) (𝟙 _) (1 : Y ⟶ A) c = 0 := by
  haveI : IsIso ((𝟙_ (Over (Sp R))).hom ≫ 𝟙 _) := inferInstanceAs (IsIso (𝟙 (Sp R) ≫ 𝟙 _))
  rw [Hom.one_def, ← pullOver_pullOver, firstDeRham_base_eq_zero _ (pullOver (dp0 R) (𝟙 _) η[A] c), map_zero]

theorem pullOver_id_apply {A : Over (Sp R)} (c : FirstDeRham (A.hom ≫ 𝟙 _)) :
    pullOver (dp0 R) (𝟙 _) (𝟙 A) c = c := IsMor.pullCohomologyOne_id _ _

theorem allPrim_of_free (H : GlobalTheory.Published.AbelianDeRhamFree) {A : Over (Sp R)} [GrpObj A] {g : ℕ}
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) : AllPrim (dp0 R) (𝟙 _) A := by
  obtain ⟨f1, p1, r1, -⟩ := H R A g hA hg
  obtain ⟨f2, p2, r2, -⟩ := H R (A ⊗ A) (g + g) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (GlobalTheory.AbDual.smooth_prod hg hg)
  let r : FirstDeRham ((A ⊗ A).hom ≫ 𝟙 _) →ₗ[R] FirstDeRham (A.hom ≫ 𝟙 _) × FirstDeRham (A.hom ≫ 𝟙 _) :=
    (pullOver (dp0 R) (𝟙 _) (lift (𝟙 A) 1)).prod (pullOver (dp0 R) (𝟙 _) (lift 1 (𝟙 A)))
  have hv : ∀ x, r x =
      (pullOver (dp0 R) (𝟙 _) (lift (𝟙 A) 1) x, pullOver (dp0 R) (𝟙 _) (lift 1 (𝟙 A)) x) :=
    fun _ ↦ rfl
  have hr : ∀ a b,
      r (pullOver (dp0 R) (𝟙 _) (fst A A) a + pullOver (dp0 R) (𝟙 _) (snd A A) b) = (a, b) := by
    intro a b
    rw [hv]
    simp only [map_add (f := _), pullOver_pullOver, lift_fst, lift_snd, pullOver_one_eq_zero,
      pullOver_id_apply, add_zero, zero_add]
  have hs : Function.Surjective r := fun x ↦ ⟨_, hr x.1 x.2⟩
  have hb : Function.Bijective r :=
    Module.bijective_of_surjective_of_rankAtStalk_eq hs fun m _ ↦ by
      rw [Module.rankAtStalk_prod, Pi.add_apply, r1, r2]; ring
  refine eq_top_iff.2 fun c _ ↦ (mem_prim_iff _ _ A c).2 (hb.1 ?_)
  rw [hr, hv]
  simp only [pullOver_pullOver, ← Hom.mul_def, _root_.mul_one, _root_.one_mul, pullOver_id_apply]

theorem abelianDeRham_free (H : GlobalTheory.Published.AbelianDeRhamFree) : GlobalTheory.Published.AbelianDeRham.Free :=
  fun R _ A _ g hA hg ↦ ⟨allPrim_of_free H hA hg, H R A g hA hg⟩

end GlobalTheory.AbelianPrim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelic
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp

theorem exists_realPart_hom : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V), V.SigOK → IsInfFam θ → IsFrames V A → ∃ rp : GA D V →* (∀ ρ, Upq V ρ), Continuous rp ∧ IsRealPart V θ A rp := by
  intro D V θ A hV hθ hA
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  obtain ⟨e1, he1⟩ := GlobalTheory.Mem.InfGroup.real_points D.host.F D.host.E D.sp.cm.sig V.rank V.gram D.what₂.Tau (tauE D) θ
    (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) A hcm hτ hθ (fun i => hV (tauE D i)) hA
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  refine ⟨e1.toMulEquiv.toMonoidHom.comp ((MonoidHom.fst _ _).comp e0.toMulEquiv.toMonoidHom),
    e1.continuous.comp (continuous_fst.comp e0.continuous), fun h i => ?_⟩
  show UpqT.mat (e1 (e0 h).1 i) * A i = _
  rw [he1, (he0 h).2]; rfl

end GlobalTheory.CovTop.VolUp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelicStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_realComponentHom_unitaryAdelic : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V), V.SigOK → IsInfFam θ → IsFrames V A → ∃ rp : GA D V →* (∀ ρ, Upq V ρ), Continuous rp ∧ IsRealPart V θ A rp := by
  first | exact @GlobalTheory.CovTop.VolUp.exists_realPart_hom | exact GlobalTheory.CovTop.VolUp.exists_realPart_hom | (intros; apply GlobalTheory.CovTop.VolUp.exists_realPart_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KeyVals

variable {S : Scheme.{0}}

abbrev FF (S : Scheme.{0}) [IsIntegral S] : Type := S.presheaf.stalk (genericPoint S)

instance fieldFF (S : Scheme.{0}) [IsIntegral S] : Field (FF S) := inferInstanceAs (Field S.functionField)

def genPt (S : Scheme.{0}) [IsIntegral S] : Sp (FF S) ⟶ S := S.fromSpecStalk (genericPoint S)

theorem genPt_le [IsIntegral S] (U : S.Opens) (h : genericPoint S ∈ U) : ⊤ ≤ genPt S ⁻¹ᵁ U := by
  intro p _
  have hp : (genPt S).base p ∈ Set.range (S.fromSpecStalk (genericPoint S)).base := ⟨p, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hp
  exact hp.mem_open U.isOpen h

theorem spMap_germ_fromSpec [IsIntegral S] (W : S.Opens) (hW : IsAffineOpen W) (h : genericPoint S ∈ W) :
    spMap (S.presheaf.germ W (genericPoint S) h).hom ≫ hW.fromSpec = genPt S :=
  hW.fromSpecStalk_eq_fromSpecStalk h

abbrev bG {R : Type} [CommRing R] (G : Over S) (ξ : Sp R ⟶ S) : Over (Sp R) := (Over.pullback ξ).obj G

instance isCommMonObj_bG {R : Type} [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (ξ : Sp R ⟶ S) :
    IsCommMonObj (bG G ξ) := Functor.isCommMonObj_obj

def eb {R : Type} [CommRing R] (ξ : Sp R ⟶ S) : (𝟙_ (Over (Sp R))).left ⟶ (𝟙_ (Over S)).left := ξ

theorem eSec_bG {R : Type} [CommRing R] (G : Over S) [GrpObj G] (ξ : Sp R ⟶ S) :
    eSec (bG G ξ) ≫ pullback.fst G.hom ξ = eb ξ ≫ eSec G :=
  LieVB.unitSec_comp (isGrpPullback_pullback G ξ)

def bL {R : Type} [CommRing R] {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (ξ : Sp R ⟶ S) :
    RigLB (bG G ξ) where
  L := L.L.pull (pullback.fst G.hom ξ)
  rig := rigPullOf (G' := bG G ξ) (G := G) (pullback.fst G.hom ξ) (eb ξ) (eSec_bG G ξ) L.L L.rig
  isLB := LB.isLB_pull L.isLB _
  rigGen := LBxP.isGen_pullAlong L.L (pullback.fst G.hom ξ) (eb ξ) (fun _ : PUnit => eSec G) (fun _ => 1)
    (fun _ => eSec (bG G ξ)) (fun _ => eSec_bG G ξ) L.rig L.rigGen

def IsLocSec {R : Type} [CommRing R] {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {δ : LB S}
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (ξ : Sp R ⟶ S) (s : (bL L ξ).L.Sec) : Prop :=
  ∀ (j : (bL L ξ).L.ι) (h : (bL L ξ).L.U j ≤
      pullback.fst G.hom ξ ⁻¹ᵁ (CechPic.tens L.L (δ.pull G.hom)).U (j PUnit.unit, fun _ => i)),
    s.f j = ((pullback.fst G.hom ξ).appLE _ _ h).hom (σ.f (j PUnit.unit, fun _ => i))

def pfr {R : Type} [CommRing R] {G : Over S} [GrpObj G] {g : ℕ} (c : VB.Chart (LieVB.omega G) g) (ξ : Sp R ⟶ S)
    (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) (k : Fin g) : Γ(LieVB.omega (bG G ξ), ⊤) :=
  (LieVB.omegaBase (isGrpPullback_pullback G ξ)).app ⊤ (QCoh.pullbackSections ξ (LieVB.omega G) hc (c.e k))

def IsDual {R : Type} [CommRing R] {G : Over S} [GrpObj G] {g : ℕ} (c : VB.Chart (LieVB.omega G) g)
    (ξ : Sp R ⟶ S) (y : Fin g → (epsR R ⟶ bG G ξ)) : Prop :=
  ∃ hc : ⊤ ≤ ξ ⁻¹ᵁ c.U, ∀ j, ∃ v : Pdiv.LieG (bG G ξ), v.1 = y j ∧ ∀ k,
    VB.dualApp (LieVB.tangent v) le_top (pfr c ξ hc k) = if j = k then 1 else 0

def IsKeyVal (κ : Rule) [IsIntegral S] [CharZero (FF S)] {G : Over S} [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G)
    {δ : LB S} (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (c : VB.Chart (LieVB.omega G) g) (i : δ.ι) (v : FF S) : Prop :=
  ∃ (s : (bL L (genPt S)).L.Sec) (y : Fin g → (epsR (FF S) ⟶ bG G (genPt S))) (x : KeyIn (FF S)) (hg : x.P.g = g),
    IsLocSec σ i (genPt S) s ∧ IsDual c (genPt S) y ∧
    KeyOn (RingHom.id (FF S)) x (bG G (genPt S)) (bL L (genPt S)) s (fun j => y (j.cast hg)) ∧ v = κ (FF S) x

end GlobalTheory.KeyVals

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor

namespace GlobalTheory

namespace GaloisDescentNoetherian

open QuotientDescent (up up_left up_comp)

variable {X Y : Scheme.{0}} {π : X ⟶ Y} {G : Over X} {G' : Over Y} {φ : G.left ⟶ G'.left}
  {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {ν : Ga → (G.left ⟶ G.left)}

noncomputable def act (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    pullback T.hom π ⟶ pullback T.hom π :=
  pullback.lift (pullback.fst T.hom π) (pullback.snd T.hom π ≫ ρ a)
    (by rw [Category.assoc, hc.inv, pullback.condition])

theorem act_fst (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    act hc T a ≫ pullback.fst T.hom π = pullback.fst T.hom π := pullback.lift_fst _ _ _

theorem act_snd (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    act hc T a ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ ρ a := pullback.lift_snd _ _ _

theorem isGaloisCover_act (hc : IsGaloisCover Ga ρ π) (T : Over Y) :
    IsGaloisCover Ga (act hc T) (pullback.fst T.hom π) :=
  ((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).2.2 _ _ (pullback.fst T.hom π) (act hc T) (pullback.snd T.hom π) T.hom
    (act_snd hc T) pullback.condition.symm).2 (IsPullback.of_hasPullback T.hom π).flip (act_fst hc T)

theorem cover_ext (hc : IsGaloisCover Ga ρ π) {Z : Scheme.{0}} {f g : Y ⟶ Z} (h : π ≫ f = π ≫ g) :
    f = g :=
  ((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).1 Z (π ≫ g) fun a ↦ by rw [← Category.assoc, hc.inv]).unique h rfl

theorem up_injective (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π) {T : Over Y}
    {x y : T ⟶ G'} (e : up H x = up H y) : x = y := by
  refine Over.OverMorphism.ext (cover_ext (isGaloisCover_act hc T) ?_)
  rw [← up_left H, ← up_left H, e]

noncomputable def equivariant [GrpObj G] (hc : IsGaloisCover Ga ρ π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (T : Over Y) : Subgroup ((Over.pullback π).obj T ⟶ G) :=
  ⨅ a : Ga, (preHom (Over.homMk (act hc T a) (act_snd hc T a))).eqLocus
    (pushHom (hν a) ((Over.pullback π).obj T))

theorem mem_equivariant [GrpObj G] (hc : IsGaloisCover Ga ρ π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) {T : Over Y} {w : (Over.pullback π).obj T ⟶ G} :
    w ∈ equivariant hc hν T ↔ ∀ a, act hc T a ≫ w.left = w.left ≫ ν a := by
  simp only [equivariant, Subgroup.mem_iInf]
  exact ⟨fun h a ↦ congrArg (fun z ↦ z.left) (h a), fun h a ↦ Over.OverMorphism.ext (h a)⟩

theorem exists_up [GrpObj G] (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (hφ : ∀ a, ν a ≫ φ = φ) {T : Over Y}
    {w : (Over.pullback π).obj T ⟶ G} (hw : w ∈ equivariant hc hν T) : ∃ z : T ⟶ G', up H z = w := by
  have hc' := isGaloisCover_act hc T
  obtain ⟨z, hz, -⟩ := (GlobalTheory.T.galoisCover_descent_and_cartesian_squares _ _ _ Ga _ hc').1 _ (w.left ≫ φ) fun a ↦ by
    rw [← Category.assoc, (mem_equivariant hc hν).mp hw a, Category.assoc, hφ]
  refine ⟨Over.homMk z (cover_ext hc' ?_), QuotientDescent.hom_ext H ((up_left H _).trans hz)⟩
  rw [reassoc_of% hz, H.w, pullback.condition]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ π) (Over.w w))

theorem up_mem [GrpObj G] (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (hφ : ∀ a, ν a ≫ φ = φ) {T : Over Y} (z : T ⟶ G') :
    up H z ∈ equivariant hc hν T := (mem_equivariant hc hν).mpr fun a ↦ by
  have e : (up H z).left ≫ G.hom = pullback.snd T.hom π := Over.w _
  have h₁ := act_fst hc T a
  refine H.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, hφ, up_left, reassoc_of% h₁]
  · rw [Category.assoc, Category.assoc, (hν a).1.w, e, act_snd, reassoc_of% e]

theorem exists_grpObj [GrpObj G] [IsCommMonObj G] (hc : IsGaloisCover Ga ρ π)
    (H : IsPullback φ G.hom G'.hom π) (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a))
    (hφ : ∀ a, ν a ≫ φ = φ) : ∃ _ : GrpObj G', IsCommMonObj G' ∧ IsGrpPullback G G' π φ := by
  have inj {T : Over Y} {x y : T ⟶ G'} (e : up H x = up H y) : x = y := up_injective hc H e
  have mem {T : Over Y} (z : T ⟶ G') := up_mem hc H hν hφ z
  obtain ⟨m, hm⟩ := exists_up hc H hν hφ (mul_mem (mem (fst G' G')) (mem (snd G' G')))
  obtain ⟨e, he⟩ := exists_up hc H hν hφ (T := 𝟙_ _) (one_mem _)
  obtain ⟨i, hi⟩ := exists_up hc H hν hφ (inv_mem (mem (𝟙 G')))
  have hm' {T : Over Y} (u : T ⟶ G' ⊗ G') :
      up H (u ≫ m) = up H (u ≫ fst _ _) * up H (u ≫ snd _ _) := by
    rw [up_comp, hm, MonObj.comp_mul, ← up_comp, ← up_comp]
  have he' {T : Over Y} (u : T ⟶ 𝟙_ _) : up H (u ≫ e) = 1 := by
    rw [up_comp, he, MonObj.comp_one]
  letI : GrpObj G' :=
    { one := e
      mul := m
      one_mul := inj (by
        rw [hm', whiskerRight_fst, he', _root_.one_mul, whiskerRight_snd, leftUnitor_hom])
      mul_one := inj (by
        rw [hm', whiskerLeft_snd, he', _root_.mul_one, whiskerLeft_fst, rightUnitor_hom])
      mul_assoc := inj (by
        rw [← Category.assoc, hm' (m ▷ G'), hm' (_ ≫ G' ◁ m), whiskerRight_fst, whiskerRight_snd,
          Category.assoc, Category.assoc, whiskerLeft_fst, whiskerLeft_snd, hm' (fst _ _),
          ← Category.assoc _ _ m, hm', Category.assoc, Category.assoc, associator_hom_fst,
          associator_hom_snd_fst, associator_hom_snd_snd, _root_.mul_assoc])
      inv := i
      left_inv := inj (by rw [hm', he', lift_fst, lift_snd, hi, inv_mul_cancel])
      right_inv := inj (by rw [hm', he', lift_fst, lift_snd, hi, mul_inv_cancel]) }
  have hmul {T : Over Y} (x y : T ⟶ G') : up H (x * y) = up H x * up H y := by
    rw [Hom.mul_def]
    exact (hm' _).trans (by rw [lift_fst, lift_snd])
  have hcomm : IsCommMonObj G' := ⟨inj (by
    refine (hm' _).trans (Eq.trans ?_ hm.symm)
    rw [braiding_hom_fst, braiding_hom_snd, mul_comm])⟩
  have sec {T : Over X} : ∃ s : T ⟶ (Over.pullback π).obj (Over.mk (T.hom ≫ π)),
      s.left ≫ pullback.fst _ π = 𝟙 T.left :=
    ⟨Over.homMk (pullback.lift (𝟙 T.left) T.hom (Category.id_comp _)) (pullback.lift_snd ..),
      pullback.lift_fst ..⟩
  refine ⟨inferInstance, hcomm, H, fun T x y x₀ y₀ hx hy ↦ ?_⟩
  obtain ⟨s, hs⟩ := sec (T := T)
  have k (z : Over.mk (T.hom ≫ π) ⟶ G') : (s ≫ up H z).left ≫ φ = z.left := by
    rw [Over.comp_left, Category.assoc, up_left, reassoc_of% hs]
  rw [← k, hmul, MonObj.comp_mul, QuotientDescent.hom_ext H ((k x₀).trans hx),
    QuotientDescent.hom_ext H ((k y₀).trans hy)]

end GaloisDescentNoetherian

open GaloisDescentNoetherian

theorem abelianScheme_descends_galoisCover_noetherian :
    ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  intro K _ _ X Y π sY Ga _ ρ G _ ν hc hq hG hν h1 hmul
  have := hc.finite
  have hinv (a : Ga) : ν a ≫ G.hom ≫ π = G.hom ≫ π := by
    rw [← Category.assoc, (hν a).1.w, Category.assoc, hc.inv]
  obtain ⟨Z, φ, sZ, -, hφ, -⟩ := GlobalTheory.T.exists_galoisCover_quotient_freeFiniteAction K G.left (G.hom ≫ π ≫ sY) Ga ν hq h1 hmul
    (fun a ↦ by rw [reassoc_of% (hinv a)]) (fun k _ _ y a hy ↦ by
      refine (hc.fibre k (y ≫ G.hom) (y ≫ G.hom) rfl).unique ?_ ?_
      · rw [Category.assoc, ← (hν a).1.w, reassoc_of% hy]
      · rw [hc.one, Category.comp_id])
  obtain ⟨v, hv, -⟩ := (GlobalTheory.T.galoisCover_descent_and_cartesian_squares _ _ φ Ga ν hφ).1 Y (G.hom ≫ π) hinv
  have H : IsPullback φ G.hom (Over.mk v).hom π :=
    (((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).2.2 _ _ φ ν G.hom v (fun a ↦ (hν a).1.w) hv.symm).1 hφ).flip
  have := hG.comm
  obtain ⟨inst, hcomm, hp⟩ := exists_grpObj (G' := Over.mk v) hc H hν hφ.inv
  refine ⟨Over.mk v, inst, φ, ?_, hp, hφ⟩
  have := hc.fin
  have := hc.etale
  have := hc.onto
  have := hφ.fin
  have := hφ.onto
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) π :=
    ⟨⟨‹_›, inferInstance⟩, inferInstance⟩
  have hs : Smooth (Over.mk v).hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.flip hQ ‹_›
  have hu : UniversallyClosed (Over.mk v).hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) H.flip hQ inferInstance
  have hsep : IsSeparated (Over.mk v).hom := by
    have : IsSeparated (φ ≫ (Over.mk v).hom) := by rw [H.w]; infer_instance
    exact SemiAbelianDescent.isSeparated_of_comp φ _
  exact ⟨hcomm, hs, ⟨⟩, SemiAbelianDescent.geometricallyConnected_of_isPullback H⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_descends_galoisCover_noetherian_base : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  first | exact @GlobalTheory.abelianScheme_descends_galoisCover_noetherian | exact GlobalTheory.abelianScheme_descends_galoisCover_noetherian | (intros; apply GlobalTheory.abelianScheme_descends_galoisCover_noetherian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM

namespace GlobalTheory.SiegelTor


open CategoryTheory AlgebraicGeometry Limits NumberField in
theorem _root_.GlobalTheory.SiegelTor.finiteType_cycAway (n : ℕ) : Algebra.FiniteType ℤ (_root_.GlobalTheory.SiegelTor.cycAway n) := by
  have hfg : (Algebra.adjoin ℤ ({_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, (n : ℂ)⁻¹} : Set ℂ)).FG := by
    rw [show ({_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, (n : ℂ)⁻¹} : Set ℂ) = ↑({_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, (n : ℂ)⁻¹} : Finset ℂ) by simp]
    exact Subalgebra.fg_adjoin_finset _
  have h := (Subalgebra.fg_iff_finiteType _).1 hfg
  rw [Algebra.adjoin_int] at h
  exact h


open CategoryTheory AlgebraicGeometry Limits NumberField in
theorem _root_.GlobalTheory.SiegelTor.arBase_cycAway : ∀ n : ℕ, n ≠ 0 → _root_.GlobalTheory.ZM.ArBase (_root_.GlobalTheory.SiegelTor.cycAway n).subtype := by
  intro n _
  exact ⟨_root_.GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n, _root_.GlobalTheory.SiegelTor.finiteType_cycAway n,
    Subtype.val_injective⟩

end GlobalTheory.SiegelTor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FormalOrigin

def iterOp {A : Type} {n : ℕ} (ds : Fin n → A → A) (α : Fin n →₀ ℕ) (f : A) : A :=
  (List.finRange n).foldr (fun i g => (ds i)^[α i] g) f

def taylor {A B : Type} [CommRing A] [CommRing B] [Algebra ℚ B] {n : ℕ} (ev : A →+* B) (ds : Fin n → A → A)
    (f : A) : MvPowerSeries (Fin n) B :=
  fun α => (∏ i, ((α i).factorial : ℚ))⁻¹ • ev (iterOp ds α f)

section Origin
variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]

def origin : G.left := (η[G]).left (IsLocalRing.closedPoint R)

def evO : G.left.presheaf.stalk (origin G) →+* R :=
  (Scheme.stalkClosedPointTo (R := CommRingCat.of R) (η[G]).left).hom

def constO : R →+* G.left.presheaf.stalk (origin G) :=
  (G.left.presheaf.germ ⊤ (origin G) trivial).hom.comp
    ((G.hom.appLE ⊤ ⊤ (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
end Origin

def intDer {S A : Type} [CommRing S] [CommRing A] [Algebra S A] (δ : Derivation S A A) : Derivation ℤ A A where
  toFun := δ
  map_add' := map_add δ
  map_smul' m x := by simpa using map_zsmul δ m x
  map_one_eq_zero' := δ.map_one_eq_zero
  leibniz' := δ.leibniz

theorem iterOp_zero {A : Type} {n : ℕ} (ds : Fin n → A → A) (f : A) : iterOp ds 0 f = f := by
  unfold iterOp
  induction (List.finRange n) with
  | nil => rfl
  | cons i l ih => simpa using ih
end GlobalTheory.FormalOrigin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover FlagModel Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IsFrameAt {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {R : Type} [CommRing R]
    {φ : c.F →+* R} (z : Sp R ⟶ Z) (k : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (g : EigFrame Y φ (z ≫ π)) : Prop :=
  ∀ σ i, g.v σ i = (tv (F.vecAt k z hz rfl σ i)).left

def Rel {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K] (z : Sp K ⟶ Z) (p : Sp K ⟶ C.Y.X) : Prop :=
  ∃ (φ : c.F →+* K) (k : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (g : EigFrame Y φ (z ≫ π)),
    z ≫ π ≫ Y.s = spMap φ ∧ IsFrameAt F z k hz g ∧ C.Carries p g

def FramesExist {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : c.F →+* R) (z : Sp R ⟶ X.YY) (k : X.F.J) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k),
    z ≫ X.π ≫ Y.s = spMap φ → ∃ g : EigFrame Y φ (z ≫ X.π), IsFrameAt X.F z k hz g

def CarriesTri {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) : Prop :=
  ∀ (K : Type) [Field K] (φ φ' : c.F →+* K) (x : Sp K ⟶ Y.X) (p : Sp K ⟶ C.Y.X) (g : EigFrame Y φ x)
    (g' : EigFrame Y φ' x), C.Carries p g → C.Carries p g' → ∃ t, g.Tri (RingHom.id K) g' t

def Vo {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) : C.Y.X.Opens :=
  C.π ⁻¹ᵁ ⟨Set.range Y.jQ, (haveI := Y.jQ_open; Y.jQ.isOpenEmbedding.isOpen_range)⟩


open GlobalTheory.Toroidal (gen genι genStr) in
instance isIso_genι {Y : Model Xo c (RingHom.id c.F)} : IsIso (genι Y) := by
  have : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (𝟙 _))
    infer_instance
  exact inferInstanceAs (IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))))

end GlobalTheory.VarFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}


open Classical in
def flatFrame {K : Type} [CommRing K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') :
    Matrix (Fin n) (Fin n') K :=
  (Matrix.blockDiagonal' A).submatrix e.symm e'.symm

theorem flatFrame_apply {K : Type} [CommRing K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    {n n' : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (τ : E →+* ℂ) (i k : Fin (Dw.mult τ)) : flatFrame A e e' (e ⟨τ, i⟩) (e' ⟨τ, k⟩) = A τ i k := by
  simp [flatFrame, Matrix.blockDiagonal'_apply_eq]

end GlobalTheory.LogKSDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaAndZelevinskyPolynomialRing
namespace GlobalTheory

theorem geometricLemma_and_zelevinskyPolynomialRing :
    GlobalTheory.Published.GeometricLemma ∧ GlobalTheory.Published.ZelevinskyPolynomialRing :=
  ⟨GlobalTheory.geometricLemma_of_filtration GlobalTheory.Laid.bzfin_holds
               GlobalTheory.geometricLemmaFiltration_unconditional,
    GlobalTheory.zelevinskyPolynomialRing_of_parts GlobalTheory.Laid.bzfin_holds
      GlobalTheory.segmentRepresentation' GlobalTheory.grothendieckRingPolynomial_outright⟩

end GlobalTheory
end
