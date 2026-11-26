module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemFormsLowCoeffsVanishIffFourierJacobi
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsArcFr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SumReCmTypeEqHalfTrace
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmLettersIsLieBasisAlongArc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCoeffNeZeroOfFourierJacobiArcDatum
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataAtSplitIsotropicPoint
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFjNeZeroAtSplitPoint
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.MemOfEqMulInvPow
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.JointModelGuards

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem mem_of_eq_mul_inv_pow (W : ValuationSubring ℂ) {x a : ℂ} (ha : a ∈ W) (n : ℕ) (h : x = a * x⁻¹ ^ n) :
    x ∈ W := by
  rcases W.mem_or_inv_mem x with hx | hx
  · exact hx
  · rw [h]; exact mul_mem ha (pow_mem hx n)

theorem exists_root_and_zeta (l : Level H) (c : Coeff l) (W : ValuationSubring ℂ) :
    ∃ r z : c.V W, (((c.V W).subtype r : c.F) : ℂ) = H.rt0 ∧ (((c.V W).subtype z : c.F) : ℂ) = zeta l.A := by
  have hr : H.rt0 ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hz : zeta l.A ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr H.d_prime.ne_zero
  have hr0 : H.rt0 ≠ 0 := fun h => by
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    exact hd (by simpa using this)
  have hrW : H.rt0 ∈ W := mem_of_eq_mul_inv_pow W (a := -(H.d : ℂ)) (neg_mem (natCast_mem W _)) 1 (by
    rw [← H.sqrt_neg_disc_sq]; field_simp)
  have hp : IsPrimitiveRoot (zeta l.A) l.A := Complex.isPrimitiveRoot_exp l.A l.A_pos.ne'
  have hz0 : zeta l.A ≠ 0 := hp.ne_zero l.A_pos.ne'
  have hzW : zeta l.A ∈ W := mem_of_eq_mul_inv_pow W (a := 1) (one_mem W) (l.A - 1) (by
    have h1 : zeta l.A * zeta l.A ^ (l.A - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel l.A_pos]; exact hp.pow_eq_one
    rw [one_mul, inv_pow]
    exact eq_inv_of_mul_eq_one_left h1)
  exact ⟨⟨⟨_, hr⟩, hrW⟩, ⟨⟨_, hz⟩, hzW⟩, rfl, rfl⟩

end GlobalTheory.JointModelGuards
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFamilyMemberFunctionalNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecEqOfSecBCIdOne
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open MonoidalCategory CartesianMonoidalCategory

namespace GlobalTheory.ArcDatumExists

theorem isUnit_det_letM {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    (K : Type) [Field K] (τ : E →+* ℂ) : IsUnit (letM Dw K τ).det := by
  have h1 : IsUnit (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K) (arcDet Dw K)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have h2 : Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (LaurentSeries K))) ∣ arcDet Dw K :=
    Finset.dvd_prod_of_mem (fun τ : E →+* ℂ => Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (LaurentSeries K)))) (Finset.mem_univ τ)
  have h3 := isUnit_of_dvd_unit
    (map_dvd (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)) h2) h1
  rw [RingHom.map_det] at h3
  exact h3

theorem flat_of_field {K S : Type} [Field K] [CommRing S] (f : K →+* S) : f.Flat := by
  let _ := f.toAlgebra
  exact (inferInstance : Module.Flat K S)

theorem appLE_id_apply {X : Scheme.{0}} (U : X.Opens) (h : U ≤ 𝟙 X ⁻¹ᵁ U) (r : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U U h).hom r = r :=
  GlobalTheory.Frames.ChgOf.appLE_id' U h r

theorem sec_eq_of_secBC_id_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (s s' : LB.Sec (PPx x))
    (h : SecBC (RingHom.id S) 1 x x s s') (i : (PPx x).ι) : s'.f i = s.f i := by
  simpa only [GlobalTheory.Frames.ChgOf.scal_one', one_mul] using
    (GlobalTheory.Frames.ChgOf.secBC_id_iff x 1 s s').mp h i

theorem isArcPt3At_of_frChg {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}
    {W : Wit Y a χ} {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)} {th : a.D₀.P.L.Sec}
    [Algebra c.F (ArcS Dw K₁)] {y₀ yF : FrPt Xo c (ArcS Dw K₁)} (hth : ∃ j, th.f j ≠ 0)
    (hfr : IsArcFr W e th (arcι Dw K₁) y₀) (hchg : FrChg (letM Dw K₁) 1 y₀ yF) : IsArcPt3At Y a χ W yF th := by
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := yF
  obtain ⟨hx, hu, hs⟩ := hchg
  dsimp only at hx hu hs
  subst hx
  obtain ⟨z, t', m1, m2, φ, -, -, -, h0, hm, -, θ, w1, w2, σ', s1, θ2, hθ, r1, r2, i1, i2, ps, hg⟩ := hfr
  obtain ⟨σ, fam, θ', a1, a2, a3, a4⟩ := hθ
  refine ⟨σ, fam, θ', θ, hth, a1, a2, a3, a4, t', m1, m2, w1, w2, σ', s1, θ2, ⟨φ, h0, hm⟩, r1, r2, i1, i2, ps, ?_⟩
  intro g g1 g2 j h
  rw [hg g g1 g2 j h]
  exact congrArg _ (sec_eq_of_secBC_id_one _ _ _ hs _).symm

theorem exists_arcDatum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (Wp : ValuationSubring ℂ) (Y : Model Xo c (c.V Wp).subtype), Y.N4 → ∀ a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁), ∃ (χ : Sp (PowerSeries K₁) ⟶ Y.X) (W : Wit Y (a.restrict (c.V Wp).subtype) χ), (∃ e, ArcLieBasis W e) ∧ ∀ e, ArcLieBasis W e → ∀ th : a.D₀.P.L.Sec, (∃ j, th.f j ≠ 0) → ∀ (μ : ArcLt Dw →₀ ℕ) (jj : ℤ), ∃ d : ArcDatum Xo c K₁, d.Wp = Wp ∧ HEq d.Y Y ∧ d.a = a ∧ HEq d.e e ∧ HEq d.th th ∧ d.μ = μ ∧ d.jj = jj ∧ d.OverBase ∧ d.Normal 1 := by
  intro hL hL2 E _ _ _ H Dw l Xo c K₁ _ _ Wp Y hN4 a
  have : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap c.F K₁).injective
  obtain ⟨χ, hχ, -⟩ := hN4 K₁ ((algebraMap c.F K₁).comp (c.V Wp).subtype) 1
    (a.restrict (c.V Wp).subtype) (Or.inl ⟨Field.toIsField K₁, rfl⟩)
  obtain ⟨hs, -, hj, hW⟩ := (hχ χ).1 rfl
  obtain ⟨W⟩ := (Y.hasArcData_iff _ _ _ _ χ).1 hW
  refine ⟨χ, W, ?_, fun e he th hth μ jj => ?_⟩
  · obtain ⟨e, -, he⟩ := GlobalTheory.ConstBasis.exists_arcBasis hL hL2 E H Dw l Xo c _ _ Y K₁ _ (a.restrict (c.V Wp).subtype) χ W
      (fun τ => (algebraMap c.F K₁).comp (embK c τ))
      ((algebraMap K₁ (FractionRing K₁)).comp (algebraMap c.F K₁)) rfl (fun _ _ => rfl)
      (GlobalTheory.JointModelGuards.exists_root_and_zeta l c Wp)
    exact ⟨e, he⟩
  · have hcomp : (algebraMap c.F (ArcS Dw K₁)).comp (c.V Wp).subtype =
        (arcι Dw K₁).comp ((PowerSeries.C (R := K₁)).comp ((algebraMap c.F K₁).comp (c.V Wp).subtype)) := by
      ext r
      simp only [RingHom.comp_apply]
      exact arcS_pin Dw K₁ ((c.V Wp).subtype r)
    obtain ⟨z, hz1, hz2⟩ := arcPt_point (Dw := Dw) Y ((algebraMap c.F K₁).comp (c.V Wp).subtype)
      hcomp χ hs (fun x hx => hj x (by rwa [map_one, one_mul]))
    have hnz : ThNZ th := (GlobalTheory.ThetaOverField.nonzero_generates hL hL2 K₁ a.D₀ th).1.1 hth
    have hflat : ((arcι Dw K₁).comp (PowerSeries.C (R := K₁))).Flat := flat_of_field _
    have hz3 : z ≫ pullback.fst _ _ ≫ Xo.s = sOf c (ArcS Dw K₁) := by
      rw [Y.jQ_over] at hz2
      rw [pullback.condition, ← Category.assoc, hz2, ← spMap_comp]
      rfl
    obtain ⟨y₀, -, hy₀⟩ := GlobalTheory.ArcQ.exists_isArcFr hL hL2 E H Dw l Xo c _ _ Y K₁ _ (a.restrict (c.V Wp).subtype) χ W
      (fun τ => (algebraMap c.F K₁).comp (embK c τ)) e th he hnz (Or.inl (Field.toIsField K₁))
      (ArcS Dw K₁) (arcι Dw K₁) z hflat hz1 hz3 (fun τ x => arcS_pin Dw K₁ (embK c τ x))
    obtain ⟨yF, hyF⟩ := (GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c (ArcS Dw K₁) (letM Dw K₁) 1 y₀).1
      (isUnit_det_letM Dw K₁) isUnit_one
    have h12 := hy₀.isFramedPoint_changed_by_letters hyF hs
    have h3 := isArcPt3At_of_frChg (W := W) (e := e) hth hy₀ hyF
    refine ⟨⟨Wp, Y, a, χ, W, e, yF, th, h12, h3, μ, jj⟩, rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, rfl, rfl, hs,
      y₀, hy₀, ?_⟩
    have h1 : GlobalTheory.ArcQ.cst Dw (1 : K₁) = 1 := by simp only [GlobalTheory.ArcQ.cst, map_one]
    rw [h1]
    exact hyF

end GlobalTheory.ArcDatumExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFamilyMemberFunctionalNeZero
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb relab laU
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcDetect

theorem exists_place (p : ℕ) (hp : p.Prime) : ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits := by
  have hne : (Ideal.span {(p : (⊥ : Subring ℂ))}) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨n, hn⟩ := Subring.mem_bot.1 v.2
    have h1 : ((p : ℤ) * n : ℤ) = 1 := by
      have := congrArg Subtype.val hv
      simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
      rw [← hn] at this
      exact_mod_cast this
    have := Int.isUnit_iff_natAbs_eq.1 (IsUnit.of_mul_eq_one _ h1)
    simp at this
    exact hp.one_lt.ne' this
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  exact ⟨W, hW ⟨p, Ideal.mem_span_singleton_self _, by simp⟩⟩

theorem iSup_sub_iInf_le {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) (A B : ℝ) (h1 : ∀ i, x i ≤ A) (h2 : ∀ i, -B ≤ x i) :
    (⨆ i, x i) - ⨅ i, x i ≤ A + B := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have := ciSup_le h1
  have := le_ciInf h2
  linarith

section Weight

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_cm {r : ℕ} (X : Data E r) (g : (E →+* ℂ) → ℕ) :
    ∑ τ : X.Ψ, (g τ.1 + g (conjEmb τ.1)) = ∑ τ, g τ := by
  classical
  rw [← Finset.sum_add_sum_compl X.Ψ g]
  have hc : X.Ψᶜ = X.Ψ.image NumberField.ComplexEmbedding.conjugate := by
    ext σ
    simp only [Finset.mem_compl, Finset.mem_image]
    constructor
    · intro h
      exact ⟨NumberField.ComplexEmbedding.conjugate σ, (X.cmType _).2 (by simpa using h), by simp⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact (X.cmType τ).1 hτ
  rw [hc, Finset.sum_image (fun a _ b _ h => by simpa using congrArg NumberField.ComplexEmbedding.conjugate h),
    ← Finset.sum_add_distrib]
  exact Finset.sum_coe_sort X.Ψ (fun τ => g τ + g (ComplexEmbedding.conjugate τ))

theorem card_cm {r : ℕ} (X : Data E r) : Fintype.card X.Ψ = fdeg E := by
  have h := sum_cm X (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  unfold fdeg
  rw [← NumberField.Embeddings.card E ℂ]
  omega

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem laU_dominant {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (h : Dom a n)
    (k : U.Comp) : (U.X k).IsDominant (laU U a n k) := by
  intro τ
  refine ⟨fun i j hij hj => ?_, fun i j hi hij => ?_, fun i j hi hj => ?_⟩
  · have hij' : (i : ℕ) ≤ j := hij
    have := h.1 (Function.invFun (relab c σ) (conjEmb τ.1))
      (show (U.X k).p0 - 1 - (j : ℕ) ≤ (U.X k).p0 - 1 - (i : ℕ) by omega)
    unfold laU
    rw [if_neg (by omega), if_neg (by omega)]
    dsimp only at this
    omega
  · have hij' : (i : ℕ) ≤ j := hij
    have := h.1 (Function.invFun (relab c σ) τ.1)
      (show (i : ℕ) - (U.X k).p0 ≤ (j : ℕ) - (U.X k).p0 by omega)
    unfold laU
    rw [if_pos (by omega), if_pos (by omega)]
    dsimp only at this
    omega
  · unfold laU
    rw [if_neg (by omega), if_pos (by omega)]
    omega

theorem invFun_relab (τ : E →+* ℂ) : Function.invFun (relab c c.F.val.toRingHom) τ = τ := by
  have h : ∀ τ : E →+* ℂ, relab c c.F.val.toRingHom τ = τ := fun τ => RingHom.ext fun _ => rfl
  have h2 : relab c c.F.val.toRingHom (Function.invFun (relab c c.F.val.toRingHom) τ) = τ :=
    Function.invFun_eq ⟨τ, h τ⟩
  rwa [h] at h2

theorem sum_spread_le {r : ℕ} (hr : 0 < r) (U : Unf Xo c c.F.val.toRingHom r) (hU : IsUnf U)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) :
    ∑ τ, (U.X k).spread (laU U a n k) τ ≤ (absA Dw a : ℝ) + (fdeg E : ℝ) * n := by
  obtain ⟨hrk, hk, -⟩ := hU
  obtain ⟨hp, hΨ⟩ := hk k
  let B : (E →+* ℂ) → ℕ := fun τ => ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))
  have hB : ∀ τ i, i < Dw.mult τ → a (τ, i) ≤ B τ := fun τ i hi =>
    Finset.single_le_sum (f := fun i : Fin (Dw.mult τ) => a (τ, (i : ℕ))) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ ⟨i, hi⟩)
  have h1 : ∀ τ : (U.X k).Ψ, (U.X k).spread (laU U a n k) τ ≤ ((B τ.1 + B (conjEmb τ.1) : ℕ) : ℝ) + n := by
    intro τ
    have m1 : Dw.mult τ.1 = Dw.p := if_pos ((hΨ _).1 τ.2)
    have m2 : Dw.mult (conjEmb τ.1) = Dw.q :=
      if_neg fun h => ((U.X k).cmType τ.1).1 τ.2 ((hΨ _).2 h)
    have hn : ((n / 2 : ℕ) : ℝ) + ((n / 2 : ℕ) : ℝ) ≤ n := by
      have : n / 2 + n / 2 ≤ n := by omega
      exact_mod_cast this
    have key : ∀ i, -((B (conjEmb τ.1) : ℤ) + ((n / 2 : ℕ) : ℤ)) ≤ laU U a n k τ i ∧
        laU U a n k τ i ≤ (B τ.1 : ℤ) + ((n / 2 : ℕ) : ℤ) := by
      intro i
      have hi := i.2
      unfold laU
      rw [invFun_relab, invFun_relab]
      split_ifs with h
      · have a1 := hB τ.1 ((i : ℕ) - (U.X k).p0) (by omega)
        constructor <;> omega
      · have a2 := hB (conjEmb τ.1) ((U.X k).p0 - 1 - (i : ℕ)) (by omega)
        constructor <;> omega
    refine (iSup_sub_iInf_le hr _ ((B τ.1 : ℝ) + ((n / 2 : ℕ) : ℝ))
      ((B (conjEmb τ.1) : ℝ) + ((n / 2 : ℕ) : ℝ)) (fun i => ?_) (fun i => ?_)).trans ?_
    · have h1 := (Int.cast_le (R := ℝ)).2 (key i).2
      rwa [Int.cast_add, Int.cast_natCast, Int.cast_natCast] at h1
    · exact_mod_cast (key i).1
    · rw [Nat.cast_add]; linarith
  refine (Finset.sum_le_sum fun τ _ => h1 τ).trans ?_
  rw [Finset.sum_add_distrib, ← Nat.cast_sum, sum_cm (U.X k) B, Finset.sum_const, Finset.card_univ, card_cm,
    nsmul_eq_mul]
  rfl

theorem exists_split {r : ℕ} (X₀ : Data E r) (X : DataX E r) (hX : X.toData = X₀) (la : Wt X₀.Ψ r)
    (P : Frame X₀.Ψ r → ℂ) (c₁ w : ℝ) (q g : ℕ) (hq : X₀.p0 = q) (hg : X.g = g)
    (hdom : X₀.IsDominant la) (hc : 0 < c₁) (hw : 1 ≤ w) (hspr : (∑ τ, X₀.spread la τ) ≤ w) (hr : (r : ℝ) ≤ w)
    (hχ : ∀ gm ∈ X₀.Γ, X₀.χ la gm = 1) (hP : P ∈ X₀.SS la) (hP' : P ∉ X₀.SSgt la c₁) :
    ∃ (ξ : Fin r → E) (ν : X₀.Ψ → ℝ) (x : Frame X₀.Ψ r) (lam : Fin (r - 2) → Fin r → E),
      X₀.IsIso ξ ∧ ∑ τ, ν τ ≤ c₁ ∧ x ∈ X₀.dom ∧ SplitData X ξ (LaQ E r q g X.NA X.NC c₁ w) (hX ▸ x) lam ∧
      (∀ m ∈ X₀.Λp ξ, ∃ e : E, e • ξ ∈ X₀.Λ ∧
        ((nQ E r g X.NA X.NC c₁ w : ℕ) : ℂ) • X₀.aproj x ξ (X₀.embV m) = X₀.embV (e • ξ)) ∧
      X₀.fj la ξ ν P x ≠ 0 := by
  subst hX hq hg
  obtain ⟨ξ, ν, hξ, hν, -, -, h⟩ := GlobalTheory.FJDetect.exists_fj_ne_zero_at_split_point' X la P c₁ w hdom hc hw hspr hr
    (fun gm hgm _ => hχ gm hgm) hP hP'
  obtain ⟨x, hx, lam, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h (nQ E r X.g X.NA X.NC c₁ w) (by
    unfold nQ
    push_cast
    exact (Nat.le_ceil _).trans (le_add_of_nonneg_right zero_le_one))
  refine ⟨ξ, ν, x, lam, hξ, hν, hx, ⟨h1, h2, h3, h4, h5, fun j τ => (h6 j τ).trans ?_⟩, h7, h8⟩
  refine pow_le_pow_left₀ ?_ (le_max_right _ _) 2
  have hw0 : 0 < w := by linarith
  unfold d6La ReciprocityTheory.MultiplicativeHeights.approxR d5mu d6rh dE
  positivity

end Weight

theorem detect_of_tie (hK : Known) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) {n' : ℕ} {La c₁ : ℝ}
    (s : CMIn d.a d.e d.th d.jj n' La c₁) (em : K₁ →+* ℂ) [Algebra (FractionRing ℂ) ℂ]
    [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (hσ : em.comp (algebraMap c.F K₁) = σ) {r : ℕ}
    (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r)
    (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    Std d → GoodEmb c σ → IsUnf U → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n →
    (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → (U.X k).IsIso ξ' → x ∈ (U.X k).dom →
    Comparison₂ Uw d.a em s.ξ k ξ' x → ∀ F ∈ sec Xo c a' n, (∀ k', (U.X k').IsBddSec (laU U a' n k') (rdU U F k')) →
    (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 s.ν₀).re) (rdU U F k) x ≠ 0 →
    ∃ mo : ArcLt Dw →₀ ℕ, cfOf d.yF mo d.jj F ≠ 0 := by
  subst hσ
  exact GlobalTheory.T.exists_coeff_ne_zero_of_fourierJacobi_arcDatum hK E H Dw l Xo c K₁ d n' La c₁ s em r U Uw k ξ' x a' n

theorem exists_fam_cfOf_ne_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r) (k : U.Comp) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ w : ℝ), ModelsAt Xo c → IsUnf U → l.A = 1 → 3 ≤ r → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → Xx.g = l.M → 0 < c₁ → ((absA Dw a' : ℝ) + (fdeg E : ℝ) * n + r ≤ w) → ∀ F ∈ sec Xo c a' n, (∀ k', rdU U F k' ∈ (U.X k').SS (laU U a' n k')) → rdU U F k ∉ (U.X k).SSgt (laU U a' n k) c₁ → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra c.F K₁) (d : ArcDatum Xo c K₁), Fam (nQ E r l.M Xx.NA Xx.NC c₁ w) (LaQ E r Dw.q l.M Xx.NA Xx.NC c₁ w) c₁ d ∧ cfOf d.yF d.μ d.jj F ≠ 0 := by
  intro hK E _ _ _ H Dw l Xo c r U k Xx hX 𝔄 a' n c₁ w hM hU hA hr hP hD hχ h𝔄 hΛ hg hc hw F hF hS hS'
  letI : Algebra (FractionRing ℂ) ℂ := FractionRing.liftAlgebra ℂ ℂ
  haveI : IsScalarTower ℂ (FractionRing ℂ) ℂ := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  have hr3 : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have h0 : (0 : ℝ) ≤ (absA Dw a' : ℝ) + (fdeg E : ℝ) * n := by positivity
  obtain ⟨ξ, ν, x, lam, hξ, hν, hx, hsp, htor, hfj⟩ := exists_split (U.X k) Xx hX (laU U a' n k) (rdU U F k) c₁ w
    Dw.q l.M (hU.2.1 k).1 hg (laU_dominant U hD k) hc (by linarith)
    ((sum_spread_le (by omega) U hU a' n k).trans (by linarith)) (by linarith) (hχ k) (hS k) hS'
  obtain ⟨ν₀, hν1, hν2, hν3, hν4⟩ := GlobalTheory.FjFreq.freq_real_nonneg_integral E r (U.X k) _ _ (hS k).1 ξ hξ ν x hx hfj
  obtain rfl : ν = fun τ => (τ.1 ν₀).re := funext hν2
  rw [GlobalTheory.sum_re_cmType_eq_half_trace] at hν
  obtain ⟨Uw⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c _ r U hU
  have htv := GlobalTheory.TransvPrinc.transvIn_of_hasPrinc E H Dw l Xo c _ r U a' n hP hχ k
  obtain ⟨K₁, _, _, _, em, a, e, th, jj, s, hem, hs, htie⟩ := GlobalTheory.T.exists_cmArcData_at_splitIsotropicPoint hK E H Dw l Xo c r U Uw k ξ x Xx hX 𝔄
    _ _ c₁ lam (nQ E r l.M Xx.NA Xx.NC c₁ w) ν₀ hU hA hr hξ hx h𝔄 hΛ hsp le_rfl (Nat.succ_pos _) htor hν1 hν3
    (fun s h1 h2 => hν4 s h1 (htv ξ hξ s h1 h2)) hν
  obtain ⟨Wp, hWp⟩ := exists_place 2 Nat.prime_two
  obtain ⟨Y, hY, hYp⟩ := hM 2 Wp Nat.prime_two hWp
  obtain ⟨χ, W, -, hd⟩ := GlobalTheory.ArcDatumExists.exists_arcDatum hK.laws hK.laws2 E H Dw l Xo c K₁ Wp Y hY a
  obtain ⟨d, d1, d2, d3, d4, d5, -, d7, d8, d9⟩ := hd e
    (GlobalTheory.T.cmLetters_isLieBasis_along_arc hK E H Dw l Xo c K₁ a e th jj _ _ c₁ s _ _ Y χ W) th s.th_nz.ne_zero 0 jj
  obtain ⟨Wp', Y', a₁, χ', W', e', yF, th', i12, i3, mu, jj'⟩ := d
  dsimp only at d1 d2 d3 d4 d5 d7
  subst d1 d3 d7
  cases d2
  cases d4
  cases d5
  obtain ⟨mo, hmo⟩ := detect_of_tie hK ⟨Wp', Y', a₁, χ', W', e', yF, th', i12, i3, mu, jj'⟩ s em _ hem U Uw k ξ x a' n
    ⟨d8, d9, hYp⟩ rfl hU hP hD hχ hξ hx htie F hF (fun k' => (hS k').1) (by rw [hs]; exact hfj)
  exact ⟨K₁, _, _, _, ⟨Wp', Y', a₁, χ', W', e', yF, th', i12, i3, mo, jj'⟩, ⟨⟨d8, d9, hYp⟩, ⟨s⟩⟩, hmo⟩

end GlobalTheory.ArcDetect
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFamilyMemberFunctionalNeZeroStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb relab laU
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_familyMember_functional_ne_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r) (k : U.Comp) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ w : ℝ), ModelsAt Xo c → IsUnf U → l.A = 1 → 3 ≤ r → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → Xx.g = l.M → 0 < c₁ → ((absA Dw a' : ℝ) + (fdeg E : ℝ) * n + r ≤ w) → ∀ F ∈ sec Xo c a' n, (∀ k', rdU U F k' ∈ (U.X k').SS (laU U a' n k')) → rdU U F k ∉ (U.X k).SSgt (laU U a' n k) c₁ → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra c.F K₁) (d : ArcDatum Xo c K₁), Fam (nQ E r l.M Xx.NA Xx.NC c₁ w) (LaQ E r Dw.q l.M Xx.NA Xx.NC c₁ w) c₁ d ∧ cfOf d.yF d.μ d.jj F ≠ 0 := by
  first | exact @GlobalTheory.ArcDetect.exists_fam_cfOf_ne_zero | exact GlobalTheory.ArcDetect.exists_fam_cfOf_ne_zero | (intros; apply GlobalTheory.ArcDetect.exists_fam_cfOf_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AbsNormHalfDifferentDvdDiscr
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem absNorm_halfDifferent_dvd_discr (D : D7) :
    Ideal.absNorm D.host.𝔟 ∣ (NumberField.discr D.host.E).natAbs := by
  have ht : differentIdeal ℤ (𝓞 D.host.E) = differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) *
      (differentIdeal ℤ (𝓞 D.host.K)).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) :=
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.K) (𝓞 D.host.E)
  have hdvd : D.host.𝔟 ∣ differentIdeal ℤ (𝓞 D.host.E) := by
    rw [ht, D.host.𝔟_spec.1, mul_assoc]
    exact dvd_mul_right _ _
  have h1 := map_dvd Ideal.absNorm hdvd
  rwa [NumberField.absNorm_differentIdeal D.host.E (𝓞 D.host.E)] at h1

theorem exists_dataX_discr_absNorm : FactPrincipalDatum → ∀ (D : D7) (T : Core D) (h : LawsCore T), GlobalTheory.RunIn.GamAt T → ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (T.U j σ).X k ∧ Xx.g = T.Q.l.M ∧ Xx.NA = (discr D.host.E).natAbs ∧ Xx.NC = Ideal.absNorm D.host.ccK ∧ Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} := by
  intro _ D T h hG j hj σ hσ k
  obtain ⟨Xx, h1, h2, h3, -⟩ :=
    GlobalTheory.LatticeData.exists_dataX_of_hasPrinc D T h j hj σ hσ (hG j hj σ hσ) k
  refine ⟨{ Xx with
    NA := (NumberField.discr D.host.E).natAbs
    NC := Ideal.absNorm D.host.ccK
    NA_pos := Int.natAbs_pos.2 (NumberField.discr_ne_zero D.host.E)
    NC_pos := Nat.pos_of_ne_zero fun e => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
    NA_sub := fun x hx => ?_
    NC_sub := fun x hx => ?_ }, h1, h2, rfl, rfl, h3⟩
  · rw [h3] at hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hv
      obtain ⟨z, hz⟩ := GlobalTheory.LatticeData.absNorm_mul_mem_one D ha
      obtain ⟨c, hc⟩ := absNorm_halfDifferent_dvd_discr D
      have e : (((NumberField.discr D.host.E).natAbs : ℕ) : D.host.E) * a =
          algebraMap (𝓞 D.host.E) D.host.E ((c : 𝓞 D.host.E) * z) := by
        rw [hc, map_mul, map_natCast, hz, Nat.cast_mul]; ring
      rw [smul_smul, e, algebraMap_smul]
      exact Xx.L'.smul_mem _ hu
    | zero => simp
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | smul c v _ hv => rw [smul_comm]; exact Xx.L'.smul_mem c hv
  · rw [h3]
    exact Submodule.subset_span ⟨_, GlobalTheory.LatticeData.absNorm_ccK_mem D, x, hx, rfl⟩

end GlobalTheory.ArcCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmFamilyFunctionalsDetectLowCoefficients
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem lowExponentBound_pos_below_last_index (D : D7) {j : ℕ} (CR : ℝ) {Tt cc : ℝ} (hj : j < D.R.m) (hT : 0 < Tt) (hc : 0 < cc) :
    0 < WeightFamilies.c1 D CR Tt cc j := by
  have hrho : 0 < WeightFamilies.rho D j := by
    unfold WeightFamilies.rho Ranks.sigW
    simp only
    omega
  have hf : 0 < D.R.f := by
    unfold Ranks.f Ranks.n
    exact Nat.mul_pos (by decide) D.R.ord_pos
  have hd : 0 < WeightFamilies.dP D j := by
    unfold WeightFamilies.dP
    positivity
  have hR : 0 < WeightFamilies.RRv D CR := by
    unfold WeightFamilies.RRv Formalism.BasicNotions.Host.rdE
    have h0 : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
      abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
    positivity
  unfold WeightFamilies.c1
  positivity

theorem sum_extendByZero_fin_eq_sum {p m : ℕ} (f : Fin p → ℕ) (h : m = p) : ∑ i : Fin m, ext0 f i = ∑ i, f i := by
  subst h
  exact Finset.sum_congr rfl fun i _ => by simp [ext0]

theorem conjugateEmbedding_not_in_cmType {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (τ : E →+* ℂ)
    (h : τ (H.rt : E) = H.rt0) : conjEmb τ (H.rt : E) ≠ H.rt0 := by
  intro h'
  have h1 : starRingEnd ℂ H.rt0 = H.rt0 := by
    have h0 : starRingEnd ℂ (τ (H.rt : E)) = H.rt0 := h'
    rwa [h] at h0
  have h2 : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  have h3 := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [pow_two, h2] at h3
  nlinarith [mul_self_nonneg H.rt0.re]

theorem absA_wtA_eq {D : D7} (T : Core D) (j : ℕ) (hD : IsDatW D j (T.Q.Dw j)) (hH : T.Q.PinHost)
    (w : WeightFamilies.Wt D j) :
    GlobalTheory.ArcCM.absA (T.Q.Dw j) (wtA w) = ∑ τ, ((∑ i, w.aP τ i) + ∑ i, w.aM τ i) := by
  classical
  simp only [GlobalTheory.ArcCM.absA, wtA]
  rw [Finset.sum_congr rfl fun σ _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Finset.sum_add_distrib]
  have ht := hH.2.2.2 t
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Finset.sum_eq_single (DV.tauEmb D t)]
    · simp only [if_true]
      exact sum_extendByZero_fin_eq_sum _ (by rw [← hD.1]; simp [Datum.mult, ht])
    · intro b _ hb; simp [hb]
    · simp
  · rw [Finset.sum_eq_single (conjEmb (DV.tauEmb D t))]
    · simp only [if_true]
      exact sum_extendByZero_fin_eq_sum _ (by rw [← hD.2.1]; simp [Datum.mult, conjugateEmbedding_not_in_cmType _ _ ht])
    · intro b _ hb; simp [hb]
    · simp

theorem absA_add_le_size {D : D7} (T : Core D) (hp : T.Q.Pins) {j : ℕ} (hj : InR D j) (ka : WeightFamilies.Wt D j) :
    (GlobalTheory.ArcCM.absA (T.Q.Dw j) (wtA ka) : ℝ) + (fdeg D.host.E : ℝ) * ka.n ≤ ka.size := by
  obtain ⟨-, -, -, -, -, hfin, hJ⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hp
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (hJ j hj).2.1
  have hfd : fdeg D.host.E = D.R.f := by
    unfold fdeg
    omega
  have ha := absA_wtA_eq T j (hp.2.2.2 j hj) hp.1 ka
  have hm : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  have h1 : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hm hr
  have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * ka.n := by positivity
  have h3 := mul_le_mul_of_nonneg_left h1 h2
  rw [ha, hfd]
  unfold WeightFamilies.Wt.size
  push_cast at h3 ⊢
  nlinarith

theorem detectQ_of_known : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → 3 ≤ D.R.r → 0 < Tt → 0 < cc → DetectQ h j ka CR Tt cc := by
  intro hK D T h j ka CR Tt cc hG hj hjm hr hT hc F hF
  have hP : FactPrincipalDatum := Formalism.IndefR.Fin.factPrincipalDatum
  obtain ⟨hS, hM⟩ := GlobalTheory.T.mem_forms_low_coeffs_vanish_iff_fourierJacobi D T h j ka CR Tt cc hj hjm F
  rw [hM]
  intro k
  by_contra hk
  obtain ⟨Xx, hX, hg, hNA, hNC, hLa⟩ := exists_dataX_discr_absNorm hP D T h hG j hj T.σ₀ T.good_σ₀ k
  obtain ⟨hgood, hA, -, -, -, -, hJ⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨hpq, hr1, -⟩ := hJ j hj
  have hmod : ModelsAt (T.Q.Xo j) T.Q.c :=
    modelsAt_of_good_level hK _ _ (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (by omega) hgood
  have hFC : F.1 ∈ T.C j ka := F.2.1
  have hw := absA_add_le_size T h.pins hj ka
  obtain ⟨K₁, i1, i2, i3, d, hd, hne⟩ := GlobalTheory.T.exists_familyMember_functional_ne_zero hK D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀)) k Xx hX D.host.AA (wtA ka) ka.n (WeightFamilies.c1 D CR Tt cc j) (ka.size + D.R.r)
    hmod (h.unf j hj T.σ₀ T.good_σ₀) hA hr (hG j hj T.σ₀ T.good_σ₀) (dom_wtA ka)
    (h.chiTriv j hj T.σ₀ T.good_σ₀ _ _ (dom_wtA ka)) (AA_ne_zero hP D) hLa hg (lowExponentBound_pos_below_last_index D CR hjm hT hc)
    (by linarith) F.1 (cusp_le_sec _ _ (T.U j) _ _ hFC) hS hk
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hq : (T.Q.Dw j).q = (D.R.sigW j).2 := (h.pins.2.2.2 j hj).2.1
  rw [hMg, hNA, hNC, hq] at hd
  exact hne (hF K₁ d hd)

end GlobalTheory.ArcCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmFamilyFunctionalsDetectLowCoefficientsStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmFamilyFunctionals_detect_lowCoefficients : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → 3 ≤ D.R.r → 0 < Tt → 0 < cc → DetectQ h j ka CR Tt cc := by
  first | exact @GlobalTheory.ArcCM.detectQ_of_known | exact GlobalTheory.ArcCM.detectQ_of_known | (intros; apply GlobalTheory.ArcCM.detectQ_of_known <;> assumption)
end
