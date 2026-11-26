module

public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaSeriesDominantWeightIsCuspForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsLeSpanShortThetaSeries
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPsiTieOfValues
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CurveOverOfRayField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SameSpaceOfLawsJ
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCharacter
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.RootOfUnityFn

theorem evR_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (f : Rul Xo c) {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S)
    (h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) (m : ℕ) :
    evR Xo c (f ^ m) y = evR Xo c f y ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero]; exact evalAt_one _ _ y h
  | succ k ih =>
    rw [pow_succ, pow_succ, ← ih]
    exact evalAt_mul _ _ _ _ y

theorem exists_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (n : ℕ) (d : DeltaDat Xo c n) (m : ℕ), 0 < m → d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 → d.cδ ^ m = 1 → (∀ y : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom), ∃ a : d.c₂.F, evR d.Xo₂ d.c₂ d.cδ y = algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom) a) → ∃ (Cls : Type) (_ : CommGroup Cls) (_ : Finite Cls) (δ : Cls →* d.c₂.Fˣ) (gdet : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom) → Cls), CMP Xo c d _ Cls δ gdet false := by
  intro E _ _ _ H Dw l Xo c n d m hm hsec hpow hval
  choose a ha using hval
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : IsReduced (CAt d.c₂.F.val.toRingHom) := (inferInstance : IsReduced ℂ)
  have hinj : Function.Injective (algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom)) :=
    (d.c₂.F.val.toRingHom).injective
  have hroot : ∀ y, a y ^ m = 1 := by
    intro y
    have hT := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂ _ y
    have h1 := evR_pow d.Xo₂ d.c₂ d.cδ y hT m
    have h0 := evR_pow d.Xo₂ d.c₂ d.cδ y hT 0
    rw [pow_zero, pow_zero] at h0
    rw [hpow, h0, ha, ← map_pow] at h1
    exact hinj (by rw [map_one]; exact h1.symm)
  refine ⟨rootsOfUnity m d.c₂.F, inferInstance, inferInstance, (rootsOfUnity m d.c₂.F).subtype,
    fun y => rootsOfUnity.mkOfPowEq (a y) (hroot y), hsec, fun y => ?_⟩
  rw [ha]
  rfl

end GlobalTheory.RootOfUnityFn
end
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta

namespace GlobalTheory.ShortLaws

theorem sameSpace_of_lawsJ {D : D7} (J : CoreJ D) (T : Top D) (hJ : LawsJ J) (hT : T.toCore = J.toCore) :
    ∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧
      ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0 := by
  have key : ∀ C : Core D, C = J.toCore → ∀ j, InR D j → ∀ k k', ((C.U j C.σ₀).X k).Gm = ((C.U j C.σ₀).X k').Gm ∧
      ((C.U j C.σ₀).X k).ξ0 = ((C.U j C.σ₀).X k').ξ0 := by
    rintro C rfl j hj k k'
    obtain ⟨hr, hm⟩ := hJ.modelW j hj J.toCore.σ₀ J.toCore.good_σ₀
    exact ⟨(hm k).1.trans (hm k').1.symm, (hm k).2.trans (hm k').2.symm⟩
  exact key _ hT

theorem lawsSh_of_pinned (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {D : D7} (T : Top D) (h : LawsP T) (hb : 0 < badN D)
    (hsp : ∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧
      ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0)
    (p : ℕ) (hp : p = D.host.pde ∨ p = D.host.pde')
    (hd : ∀ j, InR D j → ∀ n, (T.dδ j n).pd = p ∧ (T.dδ j n).IsLev ∧ (T.dδ j n).l₂.A = 1 ∧
      (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.dδ j n).Xo₂ (T.dδ j n).c₂ (T.dδ j n).nab₂) ∧
      (∃ m : ℕ, 0 < m ∧ (T.dδ j n).cδ ^ m = 1) ∧
      (∀ y : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt (T.dδ j n).c₂.F.val.toRingHom), ∃ a : (T.dδ j n).c₂.F,
        evR (T.dδ j n).Xo₂ (T.dδ j n).c₂ (T.dδ j n).cδ y =
          algebraMap (T.dδ j n).c₂.F (CAt (T.dδ j n).c₂.F.val.toRingHom) a) ∧
      ((T.Q.Dw j).p + (T.Q.Dw j).q ≤ n → ∃ ph ψ x₀, ψ ≠ 1 ∧ (T.dδ j n).PhiPin ph ψ x₀ ∧ (T.dδ j n).PsiTie ψ)) :
    LawsSh T := by
  have hM : LawsM T.toCore := h.toLawsCore.toLawsM
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hM.pins
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.firstFiveLaws.1
  have hr : ∀ j, InR D j → (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := fun j hj => (hnum j hj).1
  have hr1 : ∀ j, InR D j → 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := fun j hj => (hr j hj).symm ▸ (hnum j hj).2.1
  have hb1 : badN D ≠ 1 := by
    have h2 : 2 ∣ badN D := by
      unfold badN
      exact ((D.host.two_dvd_QS.mul_right _).mul_right _).mul_right _
    omega
  have hroot : ∀ j, InR D j → ∀ n, ∃ (Cls : Type) (_ : CommGroup Cls) (_ : Finite Cls)
      (δ : Cls →* (T.dδ j n).c₂.Fˣ)
      (gdet : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt (T.dδ j n).c₂.F.val.toRingHom) → Cls),
      CMP (T.Q.Xo j) T.Q.c (T.dδ j n) _ Cls δ gdet false := by
    intro j hj n
    obtain ⟨-, hlev, -, -, ⟨m, hm, hm1⟩, hval, -⟩ := hd j hj n
    exact GlobalTheory.RootOfUnityFn.exists_character _ _ _ _ _ _ n (T.dδ j n) m hm hlev.2.2.2.2.2.2.2.1 hm1 hval
  have htot : ∀ j, InR D j → ∀ a n,
      ShortValTot (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n (T.dδ j n) := by
    intro j hj a n
    obtain ⟨-, hlev, hA2, hnab, -, -, hphi⟩ := hd j hj n
    refine GlobalTheory.shortValTot_of_pinned hL hC _ _ _ _ _ _ n (T.dδ j n)
      (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 _ _ _ (hr1 j hj)).1 (hM.evalWD j hj) (h.allTest j hj)
      (GlobalTheory.Frames.algebraic_laws hL.secBaseChange _ _ _ _ _ _).2.2.1
      (GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange _ _ _ _ _ _) hlev (hA2.trans hA.symm) hnab ?_ _ _ _ a
    intro hn
    obtain ⟨ph, ψ, x₀, -, h1, h2⟩ := hphi hn
    exact ⟨ph, ψ, x₀, h1, h2⟩
  have hpin : ∀ j, InR D j → ∀ n, (T.Q.Dw j).p + (T.Q.Dw j).q ≤ n → ∃ ph ψ x₀, (T.dδ j n).PhiPin ph ψ x₀ := by
    intro j hj n hn
    obtain ⟨ph, ψ, x₀, -, h1, -⟩ := (hd j hj n).2.2.2.2.2.2 hn
    exact ⟨ph, ψ, x₀, h1⟩
  have hunit : ∀ j, InR D j → ∀ n, GlobalTheory.Dict.UnitC (T.dδ j n) := by
    intro j hj n
    obtain ⟨Cls, _, _, δ, gdet, hc⟩ := hroot j hj n
    exact GlobalTheory.Dict.unitC_of_finite_character _ _ _ _ _ _ _ _ Cls δ gdet (hr1 j hj) hc
  refine
    { beta := fun j _ n => GlobalTheory.betaExists_of_ne_one _ _ _ _ _ n _ hb1
      dLev := fun j hj n => (hd j hj n).2.1
      dNab := fun j hj n => (hd j hj n).2.2.2.1
      dPd := ⟨p, hp, fun j hj n => (hd j hj n).1⟩
      dPhi := fun j hj n hn => (hd j hj n).2.2.2.2.2.2 ((hr j hj).symm ▸ hn)
      dRoot := hroot
      shTot := fun j hj a n _ => htot j hj a n
      shCusp := fun j hj a n _ _ => GlobalTheory.T.short_thetaSeries_dominant_weight_isCuspForm hC D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n (T.dδ j n)
        D.R.r (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (hnum j hj).2.1 (fun σ hσ => hM.unf j hj σ hσ)
        (hd j hj n).2.1 (hd j hj n).2.2.2.1 (hunit j hj n) (hpin j hj n) (T.nab j) (badN D) D.R.nV a
      shNe := ?_ }
  intro j h1 h2
  have hj : InR D j := ⟨h1, h2.le⟩
  refine shortNe0_of_t4Span _ _ _ _ _ _ _ ?_
  refine GlobalTheory.T.cuspForms_le_span_shortThetaSeries hC D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.σ₀ T.good_σ₀ (hM.unf j hj _ T.good_σ₀) (hnum j hj).2.1 hA
    (hsp j hj) ?_ (fun a n hdom k => hM.chiTriv j hj _ T.good_σ₀ a n hdom k) (T.nab j) (badN D) D.R.nV (T.dδ j) hb ?_
  · intro k ga hga hv
    refine GlobalTheory.T.coreArithmeticGroup_contains_principalCongruence D T.toCore h.toLawsCore j hj _ T.good_σ₀ k ga hga fun x hx => ?_
    obtain ⟨u, hu, he⟩ := hv x hx
    refine ⟨u, hu, ?_⟩
    rw [he, Nat.cast_smul_eq_nsmul]
    exact add_sub_cancel_left _ _
  · intro n
    refine ⟨(hd j hj n).2.1, (hd j hj n).2.2.2.1, hunit j hj n, ?_, hpin j hj n, fun a _ => htot j hj a n⟩
    rw [(hd j hj n).1]
    have := D.host.pde_mod
    rcases hp with rfl | rfl <;> omega

end GlobalTheory.ShortLaws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ShortGenIndepConnection
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortConnIndep

theorem starRing_eq {R : Type} [CommRing R] (s t : StarRing R)
    (h : ∀ a : R, @star R s.toStarMul.toInvolutiveStar.toStar a = @star R t.toStarMul.toInvolutiveStar.toStar a) :
    s = t := by
  cases s with | @mk s1 _ =>
  cases t with | @mk t1 _ =>
  cases s1 with | @mk s2 _ =>
  cases t1 with | @mk t2 _ =>
  cases s2 with | @mk s3 _ =>
  cases t2 with | @mk t3 _ =>
  have : s3 = t3 := by
    cases s3; cases t3; congr; exact funext h
  subst this
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem sum_eq (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab nab' : NabV Xo c) (h : IsNab Xo c nab)
    (h' : IsNab Xo c nab') {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ}
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) (N : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab' y ((N : ℤ) ^ 2) (F b) (colOf m b) := by
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  have hU := thExprUniq_of_chartIndep2 hC
  obtain ⟨M, hM, hMP, hsupp⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP
  have key0 : ∀ (K : ℤ) (k : ℕ), K = (k : ℤ) →
      ∀ G : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x)),
      ∑ m ∈ ((M : c.F) • P).support, algebraMap c.F S (((M : c.F) • P).coeff m) *
          ∏ b, nab y K (G b) (colOf m b) =
        ∑ m ∈ ((M : c.F) • P).support, algebraMap c.F S (((M : c.F) • P).coeff m) *
          ∏ b, nab' y K (G b) (colOf m b) := by
    rintro K k rfl G
    exact hU E H Dw l Xo c nab nab' h h' S y k n G a _ hMP
  have key := key0 _ (N ^ 2) (Nat.cast_pow N 2).symm F
  rw [hsupp] at key
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, map_mul (algebraMap c.F S),
    _root_.mul_assoc, ← Finset.mul_sum] at key
  have hu : IsUnit (algebraMap c.F S (M : c.F)) :=
    (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hM.ne')).map _
  exact hu.mul_left_cancel key

theorem shortValAt_of (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab nab' : NabV Xo c) (h : IsNab Xo c nab)
    (h' : IsNab Xo c nab') {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S)
    (hv : ShortValAt Xo c nab w Λ β N P y v) : ShortValAt Xo c nab' w Λ β N P y v := by
  obtain ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  refine ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7.trans ?_⟩
  congr 1
  refine finsum_congr fun q => ?_
  congr 1
  exact Finset.sum_congr rfl fun i _ => sum_eq hC nab nab' h h' y' a P hP N (F q i)

end GlobalTheory.ShortConnIndep

namespace GlobalTheory

theorem shortGen_indep_connection : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (nab : NabV Xo c) (bad nV : ℕ), (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (_ : StarRing (𝓞 E)) (nab' : NabV d.Xo₂ d.c₂), IsNab d.Xo₂ d.c₂ nab' → ∀ a, shortGen Xo c nab bad nV a n { d with nab₂ := nab' } = shortGen Xo c nab bad nV a n d := by
  intro hC E _ _ _ H Dw l Xo c n d nab bad nV ⟨s, hs⟩ t nab' ht a
  have hst : s = t := ShortConnIndep.starRing_eq s t fun x => (hs.1 x).trans (ht.1 x).symm
  subst hst
  have hmap : ∀ P : MvPolynomial (LtN Dw n) c.F,
      P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) →
      MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈
        HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
    intro P hP
    have hs : Function.Surjective (d.eF : c.F →+* d.c₂.F) :=
      fun y => ⟨d.eF.symm y, d.eF.apply_symm_apply y⟩
    generalize (d.eF : c.F →+* d.c₂.F) = f at hs ⊢
    obtain ⟨h1, h2, h3⟩ := hP
    refine ⟨?_, ?_, ?_⟩
    · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
      intro τ hτ b b'
      have hlap : lap Dw.mult n d.c₂.F 1 τ _ b b' (MvPolynomial.map f P) =
          MvPolynomial.map f (lap Dw.mult n c.F 1 τ _ b b' P) := by
        simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum,
          Derivation.coeFn_coe, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C,
          MvPolynomial.pderiv_map]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        congr 2
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [hlap, h1 τ hτ b b', map_zero]
    · intro σ i i' hi t
      obtain ⟨s, rfl⟩ := hs t
      have hshift : rowShift Dw.mult n d.c₂.F σ i i' (f s) (MvPolynomial.map f P) =
          MvPolynomial.map f (rowShift Dw.mult n c.F σ i i' s P) := by
        clear h1 h2 h3
        induction P using MvPolynomial.induction_on with
        | C x => simp [rowShift]
        | add p q hp hq =>
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_add (f := _), hp, hq]
        | mul_X p x hp =>
          simp only [map_mul, hp, MvPolynomial.map_X]
          congr 1
          simp only [rowShift, MvPolynomial.aeval_X]
          set_option synthInstance.maxHeartbeats 100000 in
            split_ifs <;> simp
      rw [hshift, h2 σ i i' hi s]
    · intro m hm
      exact h3 m (MvPolynomial.support_map_subset f P hm)
  refine Set.ext fun f => ⟨?_, ?_⟩
  · rintro ⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, hr⟩
    refine ⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, ?_⟩
    intro k i1 i2 i3 i4 hk y y₂ hy
    obtain ⟨v, hv, he⟩ := @hr k i1 i2 i3 i4 hk y y₂ hy
    exact ⟨v, ShortConnIndep.shortValAt_of hC nab' d.nab₂ ht hs _ Λ _ N a _ (hmap P hP.1) y₂ v hv, he⟩
  · rintro ⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, hr⟩
    refine ⟨hf, Λ, N, x0, P, h1, h2, h3, h4, h5, hP, ?_⟩
    intro k i1 i2 i3 i4 hk y y₂ hy
    obtain ⟨v, hv, he⟩ := @hr k i1 i2 i3 i4 hk y y₂ hy
    exact ⟨v, ShortConnIndep.shortValAt_of hC d.nab₂ nab' hs ht _ Λ _ N a _ (hmap P hP.1) y₂ v hv, he⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSpecialPrimeLevelCoverOfFieldConditions
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.JacobiSymEqOneOfDvdLevel
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin.Cover

theorem zeta_mul_mem (F : IntermediateField ℚ ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : n.Coprime m)
    (h1 : zeta m ∈ F) (h2 : zeta n ∈ F) : zeta (m * n) ∈ F := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 h
  have huv' : (u : ℂ) * n + v * m = 1 := by exact_mod_cast huv
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have e : zeta (m * n) = zeta m ^ u * zeta n ^ v := by
    unfold zeta
    rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    linear_combination (-1 : ℂ) * huv'
  rw [e]
  exact mul_mem (zpow_mem h1 u) (zpow_mem h2 v)

theorem FO_le_coeff {D : D7} (Q : Par D) (h : Q.PinField) : FO D ≤ Q.c.F := by
  rw [FO, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, rfl⟩
  have e := h (Q.eO.symm y)
  rw [RingEquiv.apply_symm_apply] at e
  have e' : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := e
  rw [e']
  exact SetLike.coe_mem _

theorem half_of_split (D : D7) {p : ℕ} (hp : SplitOK D p) (P : HeightOneSpectrum (𝓞 D.host.K))
    (hP : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal) (I : Ideal (𝓞 D.host.E))
    (hI : I = P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) :
    I = Ideal.span {a | a ∈ I ∧ a ∈ Algebra.adjoin ℤ {w0E D}} ∧
      I * I.map (bH D) = Ideal.span {(p : 𝓞 D.host.E)} ∧ I ⊔ I.map (bH D) = ⊤ := by
  obtain ⟨e, he1, he2, hpb⟩ := LPb.pb_eq_JK D hp P hP
  rw [hpb, LPb.map_JK] at hI
  subst hI
  refine ⟨fromK_of_gen ⟨_, rfl, ?_⟩, ?_, ?_⟩
  · rintro y (rfl | hy)
    · exact Subalgebra.natCast_mem _ _
    · rw [Set.mem_singleton_iff.1 hy]
      exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) (Subalgebra.intCast_mem _ _)
  · rw [LPb.QE_map_bar, LPb.QE_mul D _ _ he1 he2]
  · rw [LPb.QE_map_bar, ← Ideal.isCoprime_iff_sup_eq]
    exact LPb.QE_cop_self D _ _ he2

end GlobalTheory.FinalJoin.Cover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSpecialPrimeLevelCoverOfFieldConditions
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2.Cover

theorem exists_cover : ∀ (D : D7) (Q : Par D), Q.Pins → Q.Canon → ∀ p : ℕ, FieldOK0 D p → jacobiSym (-(D.host.d : ℤ)) p = 1 → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → p.Prime ∧ 5 ≤ p ∧ ∀ j, InR D j → ∃ d : DeltaDat (Q.Xo j) Q.c 0, CoverOK d p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ FnAlgClosed (Xo := d.Xo₂) (c := d.c₂) := by
  intro D Q hP hC p hK hj P hPp
  have hpp : p.Prime ∧ p % 15 = 1 ∧ ∀ i, p ≠ D.host.g i := by
    rcases hK.own with rfl | rfl
    · exact ⟨D.host.pde_prime, D.host.pde_mod.1, fun i => (D.host.pde_ne_g i).1⟩
    · exact ⟨D.host.pde'_prime, D.host.pde_mod.2, fun i => (D.host.pde_ne_g i).2⟩
  obtain ⟨hp, h15, hg⟩ := hpp
  have h5 : 5 ≤ p := by have := hp.two_le; omega
  refine ⟨hp, h5, fun j hjR => ?_⟩
  have hM : Q.l.M = D.host.g 0 * D.host.g 1 := hP.2.1.1
  have hA : Q.l.A = 1 := hP.2.1.2
  have hcop : p.Coprime Q.l.M := by
    rw [hM]
    exact Nat.Coprime.mul_right ((Nat.coprime_primes hp (D.host.g_prime 0)).2 (hg 0))
      ((Nat.coprime_primes hp (D.host.g_prime 1)).2 (hg 1))
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.FinalJoin.Cover.half_of_split D ⟨hp, by omega, hj⟩ P hPp _ rfl
  have hw : Q.H.w0 = w0E D := by rw [hC.1]; rfl
  have hb : (Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = bH D := by rw [hC.1]; rfl
  rw [← hw] at h1
  rw [← hb] at h2 h3
  obtain ⟨l₂, hd, hM₂, hMb, hA₂⟩ := (GlobalTheory.exists_level_mul_split _ Q.H Q.l).1 p _
    (hp.odd_of_ne_two (by omega)) hcop h1 h2 h3
  obtain ⟨-, hr, -, -⟩ := GlobalTheory.Member.exists_iotaOK D Q hP j hjR
  have hr1 : 1 ≤ (Q.Dw j).p + (Q.Dw j).q := by
    have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
    rw [hr]; unfold Ranks.r; omega
  obtain ⟨Xo₂⟩ := GlobalTheory.Moduli.moduli_scheme_exists _ Q.H (Q.Dw j) l₂ hr1
  have hz : zeta Q.l.M ∈ Q.c.F := by
    have := Q.c.zeta_mem
    rwa [Level.M', hA, Nat.lcm_one_right] at this
  let c₂ : Coeff l₂ :=
    { F := Q.c.F
      fin := Q.c.fin
      conj := Q.c.conj
      zeta_mem := by
        rw [Level.M', hA₂, hA, Nat.lcm_one_right, hM₂]
        exact GlobalTheory.FinalJoin.Cover.zeta_mul_mem _ (by have := Q.l.three_le; omega) hp.pos hcop hz (GlobalTheory.FinalJoin.Cover.FO_le_coeff Q hP.2.2.1 hK.zetaP)
      le := by
        have := Q.c.le
        unfold KA at this ⊢
        rwa [hA₂] }
  obtain ⟨d, e1, e2, e3, -, -, -, hlev, hnab⟩ := GlobalTheory.LevelCover.exists_deltaDat_isLev _ Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c
    hr1 0 p _ l₂ Xo₂ c₂ rfl hd hM₂ hcop hMb h3
  have hA' : d.l₂.A = 1 := by rw [e3, hA₂, hA]
  refine ⟨d, ⟨e1, e2, hlev, hA', hnab⟩, ?_⟩
  refine GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_pins D Q hP hC (D.host.g 0 * D.host.g 1 * p)
    (Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hp.pos) hK.curve j hjR d.l₂ d.Xo₂ d.c₂
    hA' ?_ d.hF
  rw [e3, hM₂, hM]

theorem exists_cover_of_fieldOK : ∀ (D : D7) (Q : Par D), Q.Pins → Q.Canon → ∀ p : ℕ, FieldOK0 D p → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → p.Prime ∧ 5 ≤ p ∧ ∀ j, InR D j → ∃ d : DeltaDat (Q.Xo j) Q.c 0, CoverOK d p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ FnAlgClosed (Xo := d.Xo₂) (c := d.c₂) := by
  intro D Q hP hC p hK
  refine exists_cover D Q hP hC p hK ?_
  have h : D.host.cls p = PrimeClass.splitK := hK.split
  exact ((primeClass_eq_splitK_iff D.host.toHostRaw).1 h).2.2.2

end GlobalTheory.FinalJoin2.Cover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSpecialPrimeLevelCoverOfFieldConditionsStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specialPrime_levelCover_of_fieldConditions : ∀ (D : D7) (Q : Par D), Q.Pins → Q.Canon → ∀ p : ℕ, FieldOK0 D p → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → p.Prime ∧ 5 ≤ p ∧ ∀ j, InR D j → ∃ d : DeltaDat (Q.Xo j) Q.c 0, CoverOK d p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ FnAlgClosed (Xo := d.Xo₂) (c := d.c₂) := by
  first | exact @GlobalTheory.FinalJoin2.Cover.exists_cover_of_fieldOK | exact GlobalTheory.FinalJoin2.Cover.exists_cover_of_fieldOK | (intros; apply GlobalTheory.FinalJoin2.Cover.exists_cover_of_fieldOK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.LawsShortOfDeltaOK
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin

theorem laws_short_of_deltaOK : ∀ (D : D7) (J : CoreJ D) (T : Top D), LawsJ J → LawsP T → T.toCore = J.toCore → 0 ∉ D.host.levelPrimes → ∀ (p : ℕ) (I : Ideal (𝓞 D.host.E)), (p = D.host.pde ∨ p = D.host.pde') → ∀ dd : ∀ j n, DeltaDat (T.Q.Xo j) T.Q.c n, (∀ j, InR D j → ∀ n, DeltaOK (dd j n) p I) → LawsP ({ T with dδ := dd } : Top D) ∧ LawsSh ({ T with dδ := dd } : Top D) := by
  intro D J T hJ h hT h0 p I hp dd hd
  have h' : LawsP ({ T with dδ := dd } : Top D) := { h with }
  have hb : 0 < badN D := by
    have := D.host.qd_big
    unfold badN
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos D.host.QS_pos (by omega)) (by omega))
      (Finset.prod_pos fun x hx => Nat.pos_of_ne_zero fun h => h0 (h ▸ hx))
  refine ⟨h', GlobalTheory.ShortLaws.lawsSh_of_pinned GlobalTheory.chartIndependence_unconditional _ h' hb
    (GlobalTheory.ShortLaws.sameSpace_of_lawsJ J T hJ hT) p hp fun j hj n => ?_⟩
  obtain ⟨⟨h1, -, h3, h4, h5⟩, ⟨h6, h7⟩, h8⟩ := hd j hj n
  exact ⟨h1, h3, h4, h5, h6, h7, h8⟩

end GlobalTheory.FinalJoin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCoeffDeltaOKOfCover
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_coeff_deltaOK_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0) (p : ℕ) (I : Ideal (𝓞 E)), CoverOK d p I → RootOK d → (∃ ψ, ψ ≠ 1 ∧ d.PsiTie ψ) → ∃ φ : ∀ n, (Fin n → LevQ Dw d.l₂) → c.F, ∀ n, DeltaOK (GlobalTheory.FormTies.withCoeff d (φ n)) p I := by
  intro E _ _ _ H Dw l Xo c d p I hc hr ⟨ψ, hψ, ht⟩
  have key : ∀ n, ∃ φ : (Fin n → LevQ Dw d.l₂) → c.F, DeltaOK (GlobalTheory.FormTies.withCoeff d φ) p I := by
    intro n
    by_cases hn : Dw.p + Dw.q ≤ n
    · obtain ⟨φ, ph, x₀, h⟩ := GlobalTheory.exists_phiPin_of_character E H Dw l Xo c n
        (GlobalTheory.FormTies.withCoeff d (0 : (Fin n → LevQ Dw d.l₂) → c.F)) hc.2.2.1 hn ψ
      exact ⟨φ, hc, hr, fun _ => ⟨ph, ψ, x₀, hψ, h, ht⟩⟩
    · exact ⟨0, hc, hr, fun h => absurd h hn⟩
  choose φ hφ using key
  exact ⟨φ, hφ⟩

end GlobalTheory
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2.FullExt

theorem exists_delta_xiAt_noVol (D : D7) (J : CoreJ D) (hJ : LawsJ J) (hP : J.Q.Pins) (hC : J.Q.Canon) (p : ℕ) (hF : FieldOK0 D p)
    (P : HeightOneSpectrum (𝓞 D.host.K)) (hp : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal) (xi : (AfE D)ˣ →* ℂˣ)
    (hxi : XiOK D p xi) (j : ℕ) (hj : InR D j) :
    ∃ e : ∀ n, DeltaDat (J.Q.Xo j) J.Q.c n, ∀ n, (∃ φ, e n = GlobalTheory.FormTies.withCoeff (e 0) φ) ∧
      DeltaOK (e n) p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ XiAt J j (e n) xi := by
  obtain ⟨hpr, -, hd⟩ := GlobalTheory.T.exists_specialPrime_levelCover_of_fieldConditions D J.Q hP hC p hF P hp
  obtain ⟨d, hc, ha⟩ := hd j hj
  obtain ⟨f, hc', hr', hx⟩ := GlobalTheory.XiFun.exists_fun_xiAt D J hJ j hj p _ d xi hc ha hxi
  have ht := GlobalTheory.TwistTie.exists_psiTie_of_xiAt D J hJ j hj p _ { d with cδ := f } xi hpr hc' ha hxi hx
  obtain ⟨φ, hφ⟩ := GlobalTheory.exists_coeff_deltaOK_of_cover _ _ _ _ _ _ _ p _ hc' hr' ht
  exact ⟨fun n => GlobalTheory.FormTies.withCoeff { d with cδ := f } (φ n), fun n => ⟨⟨φ n, rfl⟩, hφ n, hx⟩⟩

theorem exists_full_of_xiOK_noVol : ∀ (D : D7) (J : CoreJ D) (T : Top D), LawsJ J → LawsP T → T.toCore = J.toCore → T.Q.Canon → ∀ p : ℕ, FieldOK0 D p → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → ∀ xi, XiOK D p xi → ∃ (dd : ∀ j n, DeltaDat (T.Q.Xo j) T.Q.c n) (TF : Full D), LawsFull TF ∧ TF.toTop = { T with dδ := dd } ∧ TF.J = J ∧ TF.xi = xi ∧ TF.half₂ = (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ ∀ j, InR D j → GlobalTheory.FormTies.OneCover TF.toTop j ∧ ∀ n, (TF.dδ j n).pd = p := by
  intro D J T hJ hT hc hC p hF P hp xi hxi
  obtain ⟨C, G, nab, d₀⟩ := T
  obtain ⟨C', cE, chiW, x₀, iota⟩ := J
  dsimp only at hc
  subst hc
  have key : ∀ j, ∃ e : ∀ n, DeltaDat (C.Q.Xo j) C.Q.c n, InR D j → ∀ n, (∃ φ, e n = GlobalTheory.FormTies.withCoeff (e 0) φ) ∧
      DeltaOK (e n) p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧
        XiAt (⟨C, cE, chiW, x₀, iota⟩ : CoreJ D) j (e n) xi := by
    intro j
    by_cases hj : InR D j
    · obtain ⟨e, he⟩ := exists_delta_xiAt_noVol D ⟨C, cE, chiW, x₀, iota⟩ hJ hT.pins hC p hF P hp xi hxi j hj
      exact ⟨e, fun _ => he⟩
    · exact ⟨d₀ j, fun h => absurd h hj⟩
  choose dd hdd using key
  obtain ⟨hLP, hLS⟩ := GlobalTheory.FinalJoin.laws_short_of_deltaOK D ⟨C, cE, chiW, x₀, iota⟩ ⟨C, G, nab, d₀⟩ hJ hT rfl hF.bad p _ hF.own dd
    (fun j hj n => (hdd j hj n).2.1)
  refine ⟨dd, ⟨⟨C, G, nab, dd⟩, cE, chiW, x₀, iota, xi, P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))⟩,
    ⟨hLP, hJ, hLS, hC, fun j hj n => (hdd j hj n).2.1.1.2.2.2.1, fun j hj n => (hdd j hj n).2.1.1.2.1,
      fun j hj n s nab' hn a _ => ?_, fun j hj n => (hdd j hj n).2.2⟩, rfl, rfl, rfl, rfl,
    fun j hj => ⟨fun n => (hdd j hj n).1, fun n => (hdd j hj n).2.1.1.1⟩⟩
  exact GlobalTheory.shortGen_indep_connection GlobalTheory.chartIndependence_unconditional _ _ _ _ _ _ n (dd j n) (nab j) _ _
    (hdd j hj n).2.1.1.2.2.2.2 s nab' hn a

end GlobalTheory.FinalJoin2.FullExt
