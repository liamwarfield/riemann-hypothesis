module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelDetAdelicOfPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (ChrEq)
open Formalism.L2.Host (HChar)
open scoped TensorProduct

namespace GlobalTheory.TowerCharRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem chrEq_mul {c c' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx, ← Units.val_mul]
    rfl

theorem exists_thetaChrTied (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch)
    (X : ThetaX D) (T : ThetaTied D X) (hR : ChrRead T C Tp.xi) :
    ∃ H : Formalism.L2.Host.ThetaChrTied D C nch Tp X, ∀ c, ChrEq (T.eChr c) (H.eChr c) := by
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.ChrEqUnique.chrEq_unique D
  have hc : ∀ c, IsHeckeChar D (T.eChr c) ∧ ∀ τ, ∃ a, HasInfExp D (T.eChr c) τ a := fun c => by
    have : T.eChr c ∈ Set.range T.eChr := ⟨c, rfl⟩
    rwa [T.eChr_range] at this
  choose e he using fun c => GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D (T.eChr c) (hc c).1
  have hmul : ∀ a b, e (a * b) = e a * e b := fun a b =>
    u1 _ _ _ (he (a * b)) (by rw [map_mul]; exact chrEq_mul (he a) (he b))
  have hinf : ∀ c, (e c).HasInfQ (Formalism.L2.Host.embTau D) (X.infTy c) := fun c =>
    (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D _ _ _ (he c)).1 (T.infTy c)
  refine ⟨⟨MonoidHom.mk' e hmul, fun a b hab => T.eChr_inj (u2 _ _ _ (he a) ?_), fun χ => ⟨?_, ?_⟩, hinf,
    fun μ j => u1 _ _ _ (he _) (hR.chr μ j), u1 _ _ _ (he _) hR.eta⟩, he⟩
  · have hab' : e a = e b := hab
    rw [hab']
    exact he b
  · rintro ⟨c, rfl⟩
    exact ⟨u3 _ _ (he c), _, hinf c⟩
  · rintro ⟨hu, a, ha⟩
    obtain ⟨c, hcχ⟩ := GlobalTheory.CharTransport.exists_chrEq D χ hu
    have hm : c ∈ Set.range T.eChr := by
      rw [T.eChr_range]
      exact ⟨hcχ.1, fun τ => ⟨a τ, (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D _ _ _ hcχ).2 ha τ⟩⟩
    obtain ⟨x, rfl⟩ := hm
    exact ⟨x, u1 _ _ _ (he x) hcχ⟩

end GlobalTheory.TowerCharRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormRationality
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

noncomputable section

namespace GlobalTheory.OneMapRef.IoCmp

theorem pure_rename {ι ι' κ X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {A' : ι' → (X → ℂ) → (X → ℂ)} {g : X → ℂ}
    (hX : ∀ v Q, pureTensorL A g (MvPolynomial.X v * Q) = A v (pureTensorL A g Q))
    (hX' : ∀ v Q, pureTensorL A' g (MvPolynomial.X v * Q) = A' v (pureTensorL A' g Q))
    (e : κ → ι) (e' : κ → ι') (h : ∀ k, A (e k) = A' (e' k)) (Q : MvPolynomial κ ℂ) :
    pureTensorL A g (MvPolynomial.rename e Q) = pureTensorL A' g (MvPolynomial.rename e' Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.rename_C, MvPolynomial.rename_C, ← mul_one (MvPolynomial.C a : MvPolynomial ι ℂ),
      ← mul_one (MvPolynomial.C a : MvPolynomial ι' ℂ), MvPolynomial.C_mul', MvPolynomial.C_mul', map_smul, map_smul,
      GlobalTheory.FockIndep.pure_one, GlobalTheory.FockIndep.pure_one]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [mul_comm, map_mul (MvPolynomial.rename e), map_mul (MvPolynomial.rename e'), MvPolynomial.rename_X, MvPolynomial.rename_X, hX, hX', hp, h]

theorem aeval_scale {L Y : Type} (f : L → Y) (s : ℂ) {N : ℕ} {Q : MvPolynomial L ℂ} (hQ : Q.IsHomogeneous N) :
    MvPolynomial.aeval (fun ℓ => MvPolynomial.C s * MvPolynomial.X (f ℓ)) Q =
      MvPolynomial.C (s ^ N) * MvPolynomial.rename f Q := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : m.degree = N := by
    have := hQ (MvPolynomial.mem_support_iff.1 hm)
    rwa [Finsupp.degree_eq_weight_one]
  rw [MvPolynomial.rename_eq_aeval, MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, ← hd]
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Function.comp_apply, map_pow,
    Finsupp.degree_apply]
  ring

theorem isHomogeneous_of_span {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop)
    (a : T → ℕ → ℕ) {P : MvPolynomial (Letter T r n) k} (hP : P ∈ Submodule.span k (HHa r n k cc isX a)) :
    P.IsHomogeneous (∑ σ, ∑ i : Fin (r σ), a σ i) := by
  refine (Submodule.span_le (p := MvPolynomial.homogeneousSubmodule _ k _)).2 (fun Q hQ m hm => ?_) hP
  have h := hQ.2.2 m (MvPolynomial.mem_support_iff.2 hm)
  refine Eq.trans (b := m.degree) (by rw [Finsupp.degree_eq_weight_one]; rfl) ?_
  rw [Finsupp.degree_eq_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => h σ i

theorem lieFac_eq_pow {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) (hx : 0 < xiR D)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    lieFac Dw (xiR D) a = (Real.sqrt (2 * Real.pi * xiR D))⁻¹ ^ (∑ σ, ∑ i : Fin (Dw.mult σ), a (σ, i)) := by
  have h : 0 < 2 * Real.pi * xiR D := by positivity
  have h2 : (Real.sqrt (2 * Real.pi * xiR D))⁻¹ = Real.exp (-(Real.log (2 * Real.pi * xiR D) / 2)) := by
    rw [Real.exp_neg, ← Real.log_sqrt h.le, Real.exp_log (Real.sqrt_pos.2 h)]
  rw [h2, ← Real.exp_nat_mul, lieFac]
  congr 1
  push_cast
  ring

theorem two_div_fockScale (D : D7) (τ : D.what₂.Tau) : 2 / fockScale D τ = (Real.sqrt (2 * Real.pi * xiR D))⁻¹ := by
  rw [fockScale, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB.norm_embedding_hostFormConstant_eq, div_mul_cancel_left₀ two_ne_zero]

theorem unitMap_submatrix {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ) (π : Fin m → Fin m)
    (c : Fin m) (j : Fin n) :
    Formalism.IndefR.Datum.unitMap B (B'.submatrix id π) c j = Formalism.IndefR.Datum.unitMap B B' (π c) j := by
  unfold Formalism.IndefR.Datum.unitMap
  congr 1
  ext a b
  by_cases h : b = j
  · subst h
    simp
  · simp [Matrix.mul_single_apply_of_ne _ _ _ _ _ h]

theorem pureTensorO_rename {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hS : ∀ τ, IsCartanInv (gramAt D S τ) 1)
    (hT : ∀ τ, IsCartanInv (gramAt D T τ) (s τ)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (Z Z' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (π : D.what₂.Tau → Fin T.rank → Fin T.rank) (hZ : ∀ τ, Z' τ = (Z τ).submatrix id (π τ)) {κ : Type} (ρ : κ → D.what₂.Tau)
    (c : κ → Fin T.rank) (b : κ → Fin S.rank) (Q : MvPolynomial κ ℂ) :
    pureTensorO ψ θ S T (fun _ => 1) s B Z f (MvPolynomial.rename (fun k => (ρ k, π (ρ k) (c k), b k)) Q) =
      pureTensorO ψ θ S T (fun _ => 1) s B Z' f (MvPolynomial.rename (fun k => (ρ k, c k, b k)) Q) := by
  have hX : ∀ B' v Q, pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (s τ)) B B') f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (s τ)) B B' v
        (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (s τ)) B B') f Q) := fun B' v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  unfold pureTensorO
  refine pure_rename (hX Z) (hX Z') _ _ (fun k => ?_) Q
  simp only [aPlusAll, hZ, unitMap_submatrix]

end GlobalTheory.OneMapRef.IoCmp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneFiniteAdeleDetClassOfIsDetLift
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

namespace GlobalTheory.Mem.Col2.FullDt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def detU : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) →* U1 (host_cmData R H).sig :=
  (Matrix.GeneralLinearGroup.det.comp (Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)).subtype).codRestrict _ fun x =>
    Units.ext (DetLift.det_mul_conj_det _ _ x.2)

def u1Dt (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) →* DtQ H SQ :=
  (normOneIdeleToFinerDeterminantClass H SQ (host_cmData R H).sig (fun x => bridge_star_holds R H x) (afIso H.F H.E)
    (afIso_tmul_one H.F H.E) (mem_rInt_iff H.F H.E)).comp (detU H)

theorem normOneFiniteAdeleDetClass_of_isDetLift (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (a : GlobalTheory.Mem.Chr.Ideles H.E)
    (ha : IsDetLift (host_cmData R H) x.1 a) : u1Dt H SQ x = QuotientGroup.mk a := by
  have e : detU H x = ⟨h90 (host_cmData R H).sig (finAf H.F H.E a), by
      rw [ha]; exact (detU H x).2⟩ := Subtype.ext ha.symm
  show normOneIdeleToFinerDeterminantClass H SQ _ _ _ _ _ (detU H x) = _
  rw [e]
  exact normOneIdeleToFinerDeterminantClass_eq_mk H SQ _ _ _ _ _ _ _ _ (afIso_finAf H.F H.E a).symm

theorem exists_lift (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) : ∃ a : GlobalTheory.Mem.Chr.Ideles H.E, IsDetLift (host_cmData R H) x.1 a :=
  DetLift.exists_isDetLift R H 1 x.1 x.2

theorem exists_of_idele (a : GlobalTheory.Mem.Chr.Ideles H.E) : ∃ x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H), IsDetLift (host_cmData R H) x.1 a := by
  have hu : h90 (host_cmData R H).sig (finAf H.F H.E a) ∈ U1 (host_cmData R H).sig :=
    (DetClass.exists_detClass R H (host_cmData R H).sig (fun x => bridge_star_holds R H x) (afIso H.F H.E)
      (afIso_tmul_one H.F H.E) (mem_rInt_iff H.F H.E)).1.le ⟨_, rfl⟩
  refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 1) (h90 (host_cmData R H).sig (finAf H.F H.E a)), ?_⟩, ?_⟩
  · show Formalism.UG.cT _ _ * _ * _ = _
    have hz := congrArg Units.val (show (h90 (host_cmData R H).sig (finAf H.F H.E a)) * conjId (host_cmData R H).sig (h90 (host_cmData R H).sig (finAf H.F H.E a)) = 1 from hu)
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Formalism.UG.cT, Matrix.mul_apply]
    exact (mul_comm _ _).trans hz
  · exact Units.ext (by simp)

theorem normOneFiniteAdeleDetClass_surjective (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) : Function.Surjective (u1Dt H SQ) := fun t => by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective t
  obtain ⟨x, hx⟩ := exists_of_idele H a
  exact ⟨x, normOneFiniteAdeleDetClass_of_isDetLift H SQ x a hx⟩

end GlobalTheory.Mem.Col2.FullDt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelOfLinearMap
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PtId.OneScalar

theorem map_pG_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c c' : Coeff l) (φ : c.F →+* ℂ) (φ' : c'.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    MvPolynomial.map φ (pG (Dw := Dw) c a n) = MvPolynomial.map φ' (pG (Dw := Dw) c' a n) := by
  have h : ∀ s i hi col, MvPolynomial.map φ (minorPolynomial (Dw := Dw) (n := n) c s i hi col) =
      MvPolynomial.map φ' (minorPolynomial c' s i hi col) := by
    intro s i hi col
    unfold minorPolynomial
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext p q : 2
    simp
  unfold pG
  simp only [map_prod, map_pow]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun i _ => ?_
  congr 1
  split_ifs
  · exact h _ _ _ _
  · exact h _ _ _ _
  · rw [map_zero, map_zero]

theorem ten_extremal_mem (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    (Formalism.L2.DIV.ten fun τ => extremal K n (lam τ)) ∈ Formalism.L2.DIV.VV K lam :=
  GlobalTheory.Proof.TensorMapDescent.ten_mem lam _ fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (Formalism.L2.DIV.natW_antitone (lam τ))

theorem lt_injective {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} (hH : ∀ ρ, tauE D ρ (H.rt : D.host.E) = H.rt0)
    {m n : ℕ} (lt : LtN Dw n → FVar D m n)
    (hlt : ∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨
      (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = Dw.p + ℓ.2.1))) : Function.Injective lt := by
  have hp : ∀ ℓ : LtN Dw n, ∀ ρ, ℓ.1 = tauE D ρ → (ℓ.2.1 : ℕ) < Dw.p := by
    rintro ⟨σ, s, b⟩ ρ h
    have hs := s.2
    have : Dw.mult σ = Dw.p := by
      rw [show σ = tauE D ρ from h]
      exact if_pos (hH ρ)
    exact this ▸ hs
  intro x y hxy
  obtain ⟨a1, a2⟩ := hlt x
  obtain ⟨b1, b2⟩ := hlt y
  have hpx := hp x (lt x).1
  have hpy := hp y (lt y).1
  rw [hxy] at a1 a2 hpx
  have key : x.1 = y.1 ∧ (x.2.1 : ℕ) = y.2.1 := by
    rcases a2 with ⟨a2, a3⟩ | ⟨a2, a3⟩ <;> rcases b2 with ⟨b2, b3⟩ | ⟨b2, b3⟩
    · exact ⟨a2.trans b2.symm, by omega⟩
    · have := hpx a2; omega
    · have := hpy b2; omega
    · exact ⟨a2.trans b2.symm, by omega⟩
  obtain ⟨σ, s, b⟩ := x
  obtain ⟨σ', s', b'⟩ := y
  obtain ⟨k1, k2⟩ := key
  dsimp only at k1 k2 a1 b1
  subst k1
  obtain rfl : s = s' := Fin.ext k2
  obtain rfl : b = b' := a1.symm.trans b1
  rfl

section Hw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}

theorem coefficientMap_extremalTensor_baseChange {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (hO : hwOK O.c' (lamV D i) O.hw)
    {c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W} (hc : CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0') :
    O.c0' O.hw = c0L ⟨_, ten_extremal_mem D.what₂.LL (lamV D i)⟩ := by
  obtain ⟨v', h1, h2⟩ := hc ⟨_, ten_extremal_mem D.what₂.LL (lamV D i)⟩
  rw [← h2]
  congr 1
  apply Subtype.ext
  rw [h1, show (O.hw : Formalism.L2.DIV.Pol O.c'.F D.what₂.Tau (Vc D i).rank) = _ from hO]
  dsimp only
  rw [GlobalTheory.Proof.TensorMapDescent.map_ten]
  simp only [Formalism.L2.DIV.map_extremal]

end Hw

end GlobalTheory.PtId.OneScalar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EWtApply
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def eWt (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ) :=
  LinearEquiv.refl ℂ _

theorem eWt_apply (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (z : (I.per l u a).Wrow)
    (c : (I.fm l u a).clsP) (s : Formalism.L2.Forms.FrP (I.rec7 l Z)) (s' : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m - 1))
    (h : s'.1 = s.1) : eWt I l Z u a z c s = z c s' := by
  have e : s' = s := Subtype.ext h
  subst e
  rfl

end GlobalTheory.Mem.Col2.TwP

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMkTauE
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th IsDedekindDomain NumberField
  Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharInfPlace

section General

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_inf : ∃ Θ : Ainf F ⊗[F] E →+* InfiniteAdeleRing E,
    ∀ a x, Θ (a ⊗ₜ[F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E a * algebraMap E _ x := by
  letI : Algebra F (InfiniteAdeleRing E) :=
    ((algebraMap E (InfiniteAdeleRing E)).comp (algebraMap F E)).toAlgebra
  let f : E →ₐ[F] InfiniteAdeleRing E := ⟨algebraMap E _, fun _ => rfl⟩
  let g : Ainf F →ₐ[F] InfiniteAdeleRing E :=
    ⟨GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E,
      fun x => congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap F E x)⟩
  exact ⟨(Algebra.TensorProduct.productMap g f).toRingHom, fun a x => rfl⟩

theorem exists_fin : ∃ Θ : Af F ⊗[F] E →+* FiniteAdeleRing (𝓞 E) E,
    ∀ a x, Θ (a ⊗ₜ[F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E a * algebraMap E _ x := by
  letI : Algebra F (FiniteAdeleRing (𝓞 E) E) :=
    ((algebraMap E (FiniteAdeleRing (𝓞 E) E)).comp (algebraMap F E)).toAlgebra
  let f : E →ₐ[F] FiniteAdeleRing (𝓞 E) E := ⟨algebraMap E _, fun _ => rfl⟩
  let g : Af F →ₐ[F] FiniteAdeleRing (𝓞 E) E :=
    ⟨GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E,
      fun x => congrArg Prod.snd (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap F E x)⟩
  exact ⟨(Algebra.TensorProduct.productMap g f).toRingHom, fun a x => rfl⟩

variable {F E}

theorem comp_eq [StarRing E] {Θ : Ainf F ⊗[F] E →+* InfiniteAdeleRing E}
    (hΘ : ∀ a x, Θ (a ⊗ₜ[F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E a * algebraMap E _ x)
    {φ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmb φ θ) {w : InfinitePlace E}
    (hw : InfinitePlace.mk φ = w) {y y' : Ainf F ⊗[F] E} (e : θ y = θ y') : Θ y w = Θ y' w := by
  let p : Ainf F ⊗[F] E →+* ℂ := (InfinitePlace.Completion.extensionEmbedding w).comp
    ((Pi.evalRingHom (fun v : InfinitePlace E => v.Completion) w).comp Θ)
  have hp : IsInfEmb w.embedding p := by
    refine ⟨fun x => ?_, ?_⟩
    · change InfinitePlace.Completion.extensionEmbedding w (Θ (1 ⊗ₜ[F] x) w) = _
      rw [hΘ, map_one, one_mul]
      rw [InfiniteAdeleRing.algebraMap_apply]
      simpa using InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)
    · have : (fun a : Ainf F => p (a ⊗ₜ[F] (1 : E))) = fun a =>
          InfinitePlace.Completion.extensionEmbedding w (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E a w) := by
        funext a
        change InfinitePlace.Completion.extensionEmbedding w (Θ (a ⊗ₜ[F] 1) w) = _
        rw [hΘ, map_one, mul_one]
      rw [this]
      exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
        ((AbsoluteValue.Completion.continuous_map (w.comap (algebraMap F E)).1 w.1).comp
          (continuous_apply _))
  refine (InfinitePlace.Completion.extensionEmbedding w).injective ?_
  change p y = p y'
  rcases InfinitePlace.mk_eq_iff.1 (hw.trans (InfinitePlace.mk_embedding w).symm) with h1 | h1
  · rw [← h1] at hp
    rwa [GlobalTheory.AutFunCompare.isInfEmb_unique φ p θ hp h]
  · have hq : IsInfEmb w.embedding ((starRingEnd ℂ).comp θ) :=
      ⟨fun x => by rw [← h1, RingHom.comp_apply, h.1]; rfl, Complex.continuous_conj.comp h.2⟩
    rw [GlobalTheory.AutFunCompare.isInfEmb_unique _ p _ hp hq, RingHom.comp_apply, RingHom.comp_apply, e]

end General

theorem conjugate_emb {R : Ranks} (H : Host R) (g : R.GG) :
    ComplexEmbedding.conjugate (H.emb g) = H.emb (g * R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp]
  refine RingHom.ext fun x => ?_
  have hcm := H.isCMField_hostE
  have h : IsCMField.complexConj H.E x = H.conj x := by
    apply H.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  show starRingEnd ℂ (H.emb g x) = H.emb g (H.conj x)
  rw [← h, IsCMField.complexEmbedding_complexConj]

theorem exists_mk_tauE (D : D7) (w : InfinitePlace D.host.E) : ∃ τ, InfinitePlace.mk (tauE D τ) = w := by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 w.embedding
  have e : InfinitePlace.mk (D.host.emb g) = w := by rw [hg, InfinitePlace.mk_embedding]
  by_cases h : g ∈ D.R.Psi
  · obtain ⟨τ, hτ⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 h
    exact ⟨τ, (congrArg _ hτ.symm).trans e⟩
  · obtain ⟨τ, hτ⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2
      (by_contra fun h' => h ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h'))
    rw [← conjugate_emb] at hτ
    exact ⟨τ, (congrArg _ hτ.symm).trans ((InfinitePlace.mk_conjugate_eq _).trans e)⟩

section Mult

variable {D : D7} {Θ : AE D →+* AdeleRing (𝓞 D.host.E) D.host.E}
  (hΘ : ∀ a x, Θ (a ⊗ₜ[D.host.F] x) =
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap D.host.F D.host.E a * algebraMap D.host.E _ x)

include hΘ

theorem mult_inc (x : D.host.E) : Θ (incA D x) = algebraMap D.host.E _ x := by
  change Θ ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [hΘ, map_one, one_mul]

theorem mult_fst {Ψ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* InfiniteAdeleRing D.host.E}
    (hΨ : ∀ a x, Ψ (a ⊗ₜ[D.host.F] x) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap D.host.F D.host.E a * algebraMap D.host.E _ x) (z : AE D) :
    (Θ z).1 = Ψ (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]; rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ← hx, ← hy]; rfl
  | tmul a x => rw [hΘ]; exact (hΨ a.1 x).symm

theorem mult_snd {Ψ : Af D.host.F ⊗[D.host.F] D.host.E →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}
    (hΨ : ∀ a x, Ψ (a ⊗ₜ[D.host.F] x) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap D.host.F D.host.E a * algebraMap D.host.E _ x) (z : AE D) :
    (Θ z).2 = Ψ (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]; rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ← hx, ← hy]; rfl
  | tmul a x => rw [hΘ]; exact (hΨ a.2 x).symm


set_option maxHeartbeats 800000 in
theorem mult_locE (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D) (he : IsPlIdem D e P) (k : D.host.Eˣ) :
    Θ (locE D e (k : D.host.E)) =
      ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨Ψ, hΨ⟩ := exists_inf D.host.F D.host.E
  have hfin : ∀ z, (Θ z).2 = Φ z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, RingHom.map_zero]; rfl
    | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ← hx, ← hy]; rfl
    | tmul a x =>
      have e : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap (AF D.host.F) (AE D) a * incA D x := by
        change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hΘ, e, RingHom.map_mul, hΦ.inc]
      refine FiniteAdeleRing.ext _ fun Q => ?_
      change _ = Φ _ Q * _
      rw [hΦ.base, GlobalTheory.CharTransport.locMap_eq]
      rfl
  obtain ⟨d0, d1, d2⟩ := GlobalTheory.CharTransport.isDelta_of_isPlIdem hΦ he
  have hl : Θ (locE D e (k : D.host.E)) =
      1 + Θ e * (algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) - 1) :=
    (GlobalTheory.CharTransport.map_loc Θ e (incA D (k : D.host.E))).trans (by rw [mult_inc hΘ])
  rw [hl]
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun Q => ?_)
  · change 1 + (Θ e).1 * _ = 1
    rw [mult_fst hΘ hΨ, d0, RingHom.map_zero, zero_mul, add_zero]
  · classical
    change 1 + (Θ e).2 Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) (k : D.host.E) - 1) =
      Function.update (fun w : HeightOneSpectrum (𝓞 D.host.E) => (1 : w.adicCompletion D.host.E)) P
        (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) Q
    rw [hfin]
    by_cases hQ : Q = P
    · subst hQ
      rw [d1, Function.update_self]
      ring
    · rw [d2 Q hQ, Function.update_of_ne hQ]
      ring


set_option maxHeartbeats 800000 in
theorem mult_infLoc {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam (D := D) θ)
    (τ : D.what₂.Tau) (k : D.host.Eˣ) (x : AE D) (hx : IsInfLoc D θ τ (k : D.host.E) x) :
    Θ x = ((infIdele D.host.E (plOf D θ τ) (atInf (plOf D θ τ) k) : Ideles D.host.E) :
      AdeleRing (𝓞 D.host.E) D.host.E) := by
  classical
  obtain ⟨Ψ, hΨ⟩ := exists_inf D.host.F D.host.E
  obtain ⟨Φ, hΦ⟩ := exists_fin D.host.F D.host.E
  obtain ⟨h1, h2, h3⟩ := hx
  have hpl : InfinitePlace.mk (tauE D τ) = plOf D θ τ :=
    congrArg InfinitePlace.mk (RingHom.ext fun y => ((hθ τ).1 y).symm)
  refine Prod.ext (funext fun w => ?_) ?_
  · change (Θ x).1 w = Pi.mulSingle (M := fun w : InfinitePlace D.host.E => w.Completion) (plOf D θ τ)
      (algebraMap D.host.E (plOf D θ τ).Completion (k : D.host.E)) w
    rw [mult_fst hΘ hΨ]
    by_cases hw : w = plOf D θ τ
    · subst hw
      rw [Pi.mulSingle_eq_same, comp_eq hΨ (hθ τ) hpl h3, ← mult_fst hΘ hΨ, mult_inc hΘ]
      rfl
    · obtain ⟨τ', hτ'⟩ := exists_mk_tauE D w
      have hne : τ' ≠ τ := by
        rintro rfl
        exact hw (hτ'.symm.trans hpl)
      rw [Pi.mulSingle_eq_of_ne hw, comp_eq hΨ (hθ τ') hτ' ((h2 τ' hne).trans (RingHom.map_one _).symm),
        RingHom.map_one]
      rfl
  · change (Θ x).2 = 1
    rw [mult_snd hΘ hΦ, h1, RingHom.map_one]

end Mult

theorem chrEq_infLoc : ∀ (D : D7) (c : IdC D) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ →
    ∀ θ, IsInfFam (D := D) θ → ∀ (τ : D.what₂.Tau) (k : D.host.Eˣ) (x : (AE D)ˣ),
      Formalism.L2.JoinChr.IsInfLoc D θ τ (k : D.host.E) (x : AE D) → ((c x : Circle) : ℂ) =
        ((χ.locInf (Formalism.L2.JoinChr.plOf D θ τ) (Formalism.L2.Host.atInf (Formalism.L2.JoinChr.plOf D θ τ) k) : ℂˣ) : ℂ) := by
  intro D c χ hcχ θ hθ τ k x hx
  have hχ : χ.IsUnitary := (GlobalTheory.T.heckeCharacter_ideleCharacter_match_unique D).2.2 c χ hcχ
  obtain ⟨Θ, hc, hΘ⟩ := GlobalTheory.CharTransport.exists_toAdele D.host.F D.host.E
  let u : (AE D)ˣ →* Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hc
  let c' : (AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  have h' : ChrEq c' χ := by
    refine ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩
    · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
    · have : u (Units.map (incA D).toMonoidHom x) = diagUnits D.host.E x := Units.ext (mult_inc hΘ x)
      rw [hcoe, this, χ.2.2]
      rfl
    · have : u x = localIdele D.host.E P (atFin P k) := by
        refine Units.ext ?_
        change Θ (x : AE D) = _
        rw [hx, mult_locE hΘ P e he]
      rw [hcoe, this]
      rfl
  have : u x = infIdele D.host.E (plOf D θ τ) (atInf (plOf D θ τ) k) :=
    Units.ext (mult_infLoc hΘ hθ τ k x hx)
  rw [(GlobalTheory.T.heckeCharacter_ideleCharacter_match_unique D).2.1 c c' χ hcχ h', hcoe, this]
  rfl

end GlobalTheory.CharInfPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFiniteVectorFixedPrincipalLevelCoeffSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFiniteVectorFixedPrincipalLevelCoeffSpace
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift.Level

variable {D : D7}

theorem isLift_one_V {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (t : T0) :
    Lev.IsLevelLift (Vc D i) (L.βV i) (L.datVt i t) 1 1 := by
  have h : (1 : GA D (Vc D i)) ∈ Lev.levG (Vc D i) (L.βV i) (L.datVt i t) := one_mem _
  exact ⟨h.1, h.2.1, Subgroup.mem_bot.1 h.2.2⟩

theorem levChi_flag_one {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    Lev.levChi V β (Lev.flagL L) 1 = 1 := by
  unfold Lev.levChi
  rw [(Lev.finE V).map_one]
  exact congrArg Units.val (Formalism.L2.DIV.levChar D.sp.cm V.gram β (Lev.flagL L)).map_one

theorem om_level_vP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_ωP → R.thP_vP → (∀ i t, IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t)) → ∀ i t, ∀ k ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv), R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hω hv _ i t k hk
  have h := GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hL (hv i t).1.2.inf hω hv i t 1 1 k (isLift_one_V R.toLevCh i t)
    ⟨hk.1, hk.2.1, Subgroup.mem_bot.1 hk.2.2⟩
  rw [h, levChi_flag_one, inv_one, one_smul]

end GlobalTheory.DefLift.Level
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFiniteVectorFixedPrincipalLevelCoeffSpaceStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilFiniteVector_fixed_principalLevel_coeffSpace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_ωP → R.thP_vP → (∀ i t, IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t)) → ∀ i t, ∀ k ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv), R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
  first | exact @GlobalTheory.DefLift.Level.om_level_vP | exact GlobalTheory.DefLift.Level.om_level_vP | (intros; apply GlobalTheory.DefLift.Level.om_level_vP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsDetRoot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilTwist

variable {D : D7}

theorem exists_isDetRoot (V : HSp D) (g : GA D V) : ∃ x, IsDetRoot V g x := by
  obtain ⟨a, aval, -⟩ := GlobalTheory.Member.exists_muVal D V 1 (isHC_one D).1 (fun _ => rfl)
  exact aval.1 g

theorem twist_both {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {χ χ' ν ν' : IdC D}
    (ha : AdmE V W χ χ') (hν : IsHC D ν) (rν : ResEta D ν 0) (hν' : IsHC D ν') (rν' : ResEta D ν' 0)
    {om om' : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (ho : IsWeilOn ψ V W χ χ' om)
    (ho' : IsWeilOn ψ V W (χ * ν) (χ' * ν') om') {g : GA D V} {h : GA D W} {x y : (AE D)ˣ}
    (hx : IsDetRoot V g x) (hy : IsDetRoot W h y) :
    om' (g, h) = (((ν' x)⁻¹ * ν y : Circle) : ℂ) • om (g, h) := by
  obtain ⟨⟨C, hC⟩, -⟩ := GlobalTheory.Mem.HeckeExp.hecke_exp_laws D
  have hmul : ∀ a b : IdC D, IsHC D a → IsHC D b → IsHC D (a * b) := fun a b k l =>
    (hC _).1 (C.mul_mem ((hC _).2 k) ((hC _).2 l))
  have ha' : AdmE V W (χ * ν) (χ' * ν') :=
    ⟨ha.1, hmul _ _ ha.2.1 hν, hmul _ _ ha.2.2.1 hν', resEta_mul ha.2.2.2.1 rν, resEta_mul ha.2.2.2.2 rν'⟩
  obtain ⟨o, hd, ht⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO_of_rank_eq D ψ hψ V W χ χ' om ha ho
  obtain ⟨o', hd', ht'⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO_of_rank_eq D ψ hψ V W _ _ om' ha' ho'
  obtain ⟨o'', hd'', hv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hψ V W χ χ' ν ν' o hd hν.1 hν'.1 rν rν'
  obtain ⟨e, -, -, he, -, -, -, hth, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W ha.1.le
  refine LinearMap.ext fun Φ => Subtype.ext (funext fun w => ?_)
  have hΦ : IsThetaFunO ψ V W fun x => Φ.1 (toTWsmall V W x) := by
    simp only [← he]
    exact (hth ψ _).2 (mem_ThS.1 Φ.2)
  have k := GlobalTheory.T.weilDatum_unique_on_thetaFunctions D ψ hψ V W _ _ o' o'' hd' hd'' (g, h) _ hΦ
  rw [ht', hv g h x y hx hy, LinearMap.smul_apply, ht] at k
  have k2 := congrFun k (e.symm w)
  simp only [← he, e.apply_symm_apply, Pi.smul_apply] at k2
  exact k2

theorem weilTwEq : ∀ D : D7, WeilTwEq D := by
  intro D ψ hψ V W χ χ' ν ha hν rν om ho
  have r1 : ResEta D 1 0 := ⟨rν.1, fun _ _ _ => by simp⟩
  refine ⟨fun om' ho' g h x hx => ?_, fun om' ho' g h x hx => ?_⟩
  · obtain ⟨y, hy⟩ := exists_isDetRoot W h
    have := twist_both hψ ha (isHC_one D) r1 hν rν ho (om' := om') (by rwa [mul_one]) hx hy
    rwa [MonoidHom.one_apply, mul_one] at this
  · obtain ⟨y, hy⟩ := exists_isDetRoot V g
    have := twist_both hψ ha hν rν (isHC_one D) r1 ho (om' := om') (by rwa [mul_one]) hy hx
    rwa [MonoidHom.one_apply, inv_one, one_mul] at this

end GlobalTheory.Mem.WeilTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvLgCanonical
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TwIdxEx

open JetEx

def stepSet (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E)
    (k : P.Word × ℕ × Finset (HeightOneSpectrum (𝓞 P.host.E)) × Finset (HeightOneSpectrum (𝓞 P.host.E))) : Set ℂ :=
  jetSet (hostAmb (amb0 P.host) (chiId χ)) (P.R.N k.2.1) (P.R.N (k.2.1 + 1)) k.2.2.1
    ((∏ Q ∈ k.2.2.2, qOf Q) ^ (P.R.m + 1) * (P.T k.1 * (∏ Q ∈ k.2.2.2, qOf Q) ^ (P.R.m + 1))) (totDeg P k.1 k.2.1)

def allSet (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) : Set ℂ :=
  ⋃ k ∈ {k : P.Word × ℕ × Finset (HeightOneSpectrum (𝓞 P.host.E)) × Finset (HeightOneSpectrum (𝓞 P.host.E)) |
      (k.2.1 < P.R.m ∧ (∀ Q ∈ k.2.2.1, Q ∈ badP P Ξ) ∧ ∀ Q ∈ k.2.2.2, Q ∈ badP P Ξ) ∧ FinAlg (stepSet P χ k)}, stepSet P χ k

theorem finAlg_allSet (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) {Ξ : Set (Formalism.L2.Host.HChar P.host.E)} (h : Ξ.Finite) : FinAlg (allSet P χ Ξ) := by
  have hb := badPrimes_finite₂ P h
  have hs : {S : Finset (HeightOneSpectrum (𝓞 P.host.E)) | ∀ Q ∈ S, Q ∈ badP P Ξ}.Finite :=
    hb.toFinset.powerset.finite_toSet.subset fun S hS =>
      Finset.mem_coe.2 (Finset.mem_powerset.2 fun Q hQ => hb.mem_toFinset.2 (hS Q hQ))
  refine finAlg_biUnion ?_ fun k hk => hk.2
  exact (Set.finite_univ.prod ((Set.finite_Iio P.R.m).prod (hs.prod hs))).subset fun k hk => ⟨trivial, hk.1⟩


open Classical in
def gens (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) : Finset ℂ :=
  if h : FinAlg (allSet P χ Ξ) then h.choose else ∅

theorem gens_algebraic (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) : ∀ z ∈ gens P χ Ξ, IsAlgebraic ℚ z := by
  unfold gens
  split_ifs with h
  · exact h.choose_spec.1
  · simp

theorem allSet_subset (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) {Ξ : Set (Formalism.L2.Host.HChar P.host.E)} (h : Ξ.Finite) {K : Subfield ℂ}
    (hK : ∀ z ∈ gens P χ Ξ, z ∈ K) : allSet P χ Ξ ⊆ K := by
  have h1 := finAlg_allSet P χ h
  rw [gens, dite_eq_left h1] at hK
  exact h1.choose_spec.2.trans (Subfield.closure_le.2 hK)

theorem jetsIn_of_isTw {B : Base} {X : PreX B.toPre} (hL : StagesInhab.HasLetters B.toPre) {I : TC B X} (h : I.Ok) (ht : I.IsTw)
    (hJ : I.J = amb0 B.host) (hK : ∀ z ∈ gens B.toPre I.C.chiPsi (Set.range I.xi), z ∈ B.embLL.fieldRange) :
    ColIn.JetsIn I := by
  have hall := allSet_subset B.toPre I.C.chiPsi (Set.finite_range I.xi) hK
  refine I.jetsIn_iff.2 fun a u i hi N N' c x hx e he => ?_
  have hM : I.modulus a u = (∏ Q ∈ rowSG (B.primes X) I.sel (I.tup a), qOf Q) ^ (B.R.m + 1) *
      (B.T u * (∏ Q ∈ rowSG (B.primes X) I.sel (I.tup a), qOf Q) ^ (B.R.m + 1)) := by
    have eA : (I.cst a).A = B.R.m + 1 := by rw [ht.cst_eq a]; rfl
    have eB : (I.cst a).B = B.R.m + 1 := by rw [ht.cst_eq a]; rfl
    unfold ColIn.modulus cAof cBof
    rw [eA, eB, Finset.prod_coe_sort _ qOf]
  have hS : stepSet B.toPre I.C.chiPsi (u, i, I.Sb a u, rowSG (B.primes X) I.sel (I.tup a)) =
      jetSet I.A (B.R.N i) (B.R.N (i + 1)) (I.Sb a u) (I.modulus a u) (totDeg B.toPre u i) := by
    rw [hM, ColIn.A, hJ]
    exact (jetSet_amb B _ _ _ _ _ _ _).symm
  have hpos : 0 < I.modulus a u := by
    rw [hM]
    have := Finset.prod_pos fun Q (_ : Q ∈ rowSG (B.primes X) I.sel (I.tup a)) =>
      Nat.pos_of_ne_zero (by simpa using qPow_ne_zero Q 1 : qOf Q ≠ 0)
    have := (B.T_prime u).pos
    positivity
  refine hall (Set.mem_iUnion₂.2 ⟨(u, i, I.Sb a u, rowSG (B.primes X) I.sel (I.tup a)),
    ⟨⟨hi, Sb_subset h a u, rowSG_subset h a⟩, ?_⟩, ?_⟩)
  · rw [hS]
    exact finAlg_step hL h a u _ _ _ _ hpos
  · rw [hS]
    exact ⟨N, N', c, x, e, hx, degree_eq_totDeg B u i e he, rfl⟩

theorem lg_gens (K : Top.Ctx) : Top.large₂ K fun B f T => ∀ z ∈ gens B.toPre f.chiPsi (T.set f), z ∈ B.embLL.fieldRange :=
  ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun P f _ _ Ξ => gens P f.chiPsi Ξ, by simp,
    fun P f _ _ Ξ => gens_algebraic P f.chiPsi Ξ, fun _ _ _ _ h _ _ => h.2⟩

theorem exists_quot {K : Top.Ctx} {P : Pre} (h : K.Over P) (X : PreX P) :
    ∃ X' : PreX P, X'.piG = X.piG ∧ ∀ u, P.cOf u * (X'.piT u : P.host.E) = (X'.piT P.u₀ : P.host.E) := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  refine ⟨{ X with
    piT := K.Lv.piT
    piT_K := K.Lv.piT_K
    piT_norm := K.Lv.piT_norm
    piT_cong := fun u => Ideal.mem_span_singleton.1 (K.Lv.piT_cong u) }, rfl, fun u => ?_⟩
  exact div_mul_cancel₀ _ (K.Lv.piT_ne u)

theorem evLg_canonical : GlobalTheory.Mem.Top.EvLg fun _ B f T => (letI := B.host.cmStar; ∀ (a : Fin B.sp.X'.rank) (b : Fin (B.sp.X B.R.m).rank), (a : ℕ) = b → B.sp.iX' (B.sp.X'.frame a) = (B.sp.X B.R.m).frame b) → Nonempty (PreX B.toPre) → ∀ Pv, IsSel B.fields Pv → ∃ (X : PreX B.toPre) (I : TC B X), I.Ok ∧ TC.Pins B X ∧ I.IsTw ∧ ColIn.JetsIn I ∧ I.sel = Pv ∧ I.C = f ∧ I.S = {p | p ∈ GlobalTheory.Mem.Top.offSet B.toPre ∧ p ≠ B.host.pde ∧ p ≠ B.host.pde'} ∧ Set.range I.xi = T.set f ∧ ∀ C W V S N G, Formalism.L2.Host.ValLL0 (assemble B C W V S N G) (GlobalTheory.Mem.Top.Fr.at ⟨B, C, W, V, S, N, G⟩ f) ∧ GlobalTheory.Mem.Per.FieldOK B.host B.embLL B.embE := by
  refine InEx.ev_of_forall fun K => ((InEx.lg_colIn K).inter (lg_gens K)).imp fun B f T hO h hi ⟨X₀⟩ Pv hPv => ?_
  obtain ⟨X₁, hX⟩ := InEx.exists_oriented X₀ f.P
  obtain ⟨X, e, hc⟩ := exists_quot hO X₁
  have hX' : InEx.Oriented X f.P := by
    unfold InEx.Oriented at hX ⊢
    rw [e]; exact hX
  obtain ⟨I, a1, rfl, a3, a4, a5, a6, a7⟩ := h.1.1 X hX' Pv hPv (amb0 B.host) (exists_ambIn_ok B.host).choose_spec
  have hk : (canon I).Ok := canon_ok a1 fun a P hP => ((a7 a).2.2.2 P hP).ge
  exact ⟨X, canon I, hk, ⟨hi, hc⟩, canon_isTw I,
    jetsIn_of_isTw (hasLetters_of_over hO) hk (canon_isTw I) a6 (by have := h.2; rw [← a4] at this; exact this), a5, rfl, a3, a4,
    fun C W V S N G => ⟨h.1.2.1 C W V S N G, h.1.2.2⟩⟩

end GlobalTheory.Mem.Col2.TwIdxEx

end
end
