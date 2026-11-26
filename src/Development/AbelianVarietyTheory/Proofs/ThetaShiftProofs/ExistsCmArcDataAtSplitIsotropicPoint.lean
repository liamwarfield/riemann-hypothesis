module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAnalyticModelOnFrameOrbitIsolating
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormAnOnOrbit
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ImHermFormEqCurveForm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibre
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcMatchesFrameOfModelOnOrbit
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataDescentNumberField
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLamObjGoodOfCmObj
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumSectionValueCoeffEqFourierJacobi
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmPointLatticeDataOfAdaptedBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmObjOfPeriod
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb perFr
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcCM.PeriodObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D D' : Datum H}
  {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} {P' : D'.La →+ (Fin g → ℂ)}

theorem mem_lat_iff (hP : IsPeriod D ty P) (ρ : ℂ) (a : D.La) :
    a ∈ PureType.lat hP ρ ↔ P (H.rt • a) = ρ • P a := by
  refine ⟨fun h => funext fun j => ?_, fun h j hj => ?_⟩
  · rw [hP.1, Pi.smul_apply, smul_eq_mul]
    by_cases hj : ty j (H.rt : E) = ρ
    · rw [hj]
    · rw [h j hj, mul_zero, mul_zero]
  · have := congrFun h j
    rw [hP.1, Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_mul_right_iff.1 this).resolve_left hj

theorem exists_lat_move (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P') (gam : D.La ≃ₗ[𝓞 E] D'.La)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hE : ∀ a b, D'.EF (gam a) (gam b) = D.EF a b)
    (hh : ∀ a, P' (gam a) = h (P a)) {p q : ℕ} (Z : GlobalTheory.CM.CMLat hP p q) :
    ∃ Z' : GlobalTheory.CM.CMLat hP' p q, Z'.hh = Z.hh :=
  ⟨{ D₁ := Z.D₁
     sigP := Z.sigP
     sigM := Z.sigM
     f := fun j => gam.toLinearMap ∘ₗ Z.f j
     pure := fun j a => by
       refine (mem_lat_iff hP' _ _).2 ?_
       show P' (H.rt • gam (Z.f j a)) = _ • P' (gam (Z.f j a))
       rw [← map_smul, hh, hh, (mem_lat_iff hP _ _).1 (Z.pure j a), map_smul]
     hh := Z.hh
     form := fun j a b => (hE _ _).trans (Z.form j a b)
     span := by
       obtain ⟨n, hn, hs⟩ := Z.span
       refine ⟨n, hn, fun a => ?_⟩
       obtain ⟨x, hx⟩ := hs (gam.symm a)
       refine ⟨x, ?_⟩
       have := congrArg gam hx
       set_option synthInstance.maxHeartbeats 100000 in
         rw [map_nsmul, gam.apply_symm_apply, map_sum] at this
       exact this }, rfl⟩

theorem isExp_move {R : Type} [CommRing R] {T : GlobalTheory.CM.PAT H (Sp R)} {σ : R →+* ℂ} (hP : IsPeriod D ty P)
    (gam : D.La ≃ₗ[𝓞 E] D'.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hE : ∀ a b, D'.EF (gam a) (gam b) = D.EF a b)
    (hh : ∀ a, P' (gam a) = h (P a)) {e : (Fin g → ℂ) → (Over.mk (spMap σ) ⟶ T.t.G)}
    (he : GlobalTheory.CM.IsExp T σ D' ty P' e) : GlobalTheory.CM.IsExp T σ D ty P fun z => e (h z) := by
  obtain ⟨hP', hol, add, onto, ker, lin, weil⟩ := he
  have hd : Differentiable ℂ h := h.toContinuousLinearEquiv.differentiable
  refine ⟨hP, fun U f => ⟨?_, ?_⟩, fun z w => ?_, onto.comp h.surjective, fun z => ?_, fun a z => ?_,
    fun k a b c hk hc => ?_⟩
  · exact (hol U f).1.preimage hd.continuous
  · exact (hol U f).2.comp hd.differentiableOn fun z hz => hz
  · beta_reduce
    rw [map_add (f := _), add]
  · refine (ker _).trans ⟨?_, ?_⟩
    · rintro ⟨a, ha⟩
      exact ⟨gam.symm a, h.injective (by rw [← hh, gam.apply_symm_apply, ha])⟩
    · rintro ⟨a, rfl⟩
      exact ⟨gam a, hh a⟩
  · let m : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
      LinearMap.pi fun k => (LinearMap.mulLeft ℝ (ty k (a : E))).comp (LinearMap.proj k)
    have hm : ∀ z, m z = fun k => ty k (a : E) * z k := fun _ => rfl
    have hc : h.toLinearMap.restrictScalars ℝ ∘ₗ m = m ∘ₗ h.toLinearMap.restrictScalars ℝ :=
      LinearMap.ext_on_range hP.2.2.2.1 fun x => by
        show h (m (P x)) = m (h (P x))
        rw [← hh, hm, hm, ← funext (hP.1 a x), ← funext (hP'.1 a (gam x)), ← hh, map_smul]
    have hz : h (m z) = m (h z) := LinearMap.congr_fun hc z
    show e (h (m z)) = _
    rw [hz, hm, lin]
  · beta_reduce
    rw [map_smul, map_smul, ← hh, ← hh]
    exact weil k _ _ c hk (by rw [hE]; exact hc)

end GlobalTheory.ArcCM.PeriodObj

namespace GlobalTheory.ArcCM

theorem exists_cmObj_of_period : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (DB : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (PB : DB.La →+ (Fin g → ℂ)) (hP : IsPeriod DB ty PB) (Z : GlobalTheory.CM.CMLat hP DB.p DB.q), 1 ≤ DB.p + DB.q → IsTypeFn H DB.p DB.q ty → l.A = 1 → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra c.F K) (σ₁ : K →+* ℂ) (ρ : 𝓞 K) (X : GlobalTheory.CM.CMObj H K ρ σ₁ DB.p DB.q) (ex : (Fin g → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G)), σ₁.comp (algebraMap c.F K) = c.F.val.toRingHom ∧ σ₁ (ρ : K) = H.rt0 ∧ X.hh = Z.hh ∧ GlobalTheory.CM.IsExp X.B (σ₁.comp (algebraMap (𝓞 K) K)) DB ty PB ex := by
  intro kn E _ _ _ H l c DB g ty PB hP Z hpq hty hA
  obtain ⟨Xo⟩ := kn.n1ab E H DB l hpq
  obtain ⟨FU⟩ := kn.n1c E H DB l Xo (algebraMap (KA l) ℂ) g ty hpq rfl hty
  have hζ : algebraMap (KA l) ℂ (baseKA l).ζ =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((1 : ℤ) : ℂ)) / l.A) := by
    show zeta l.A = _
    rw [hA, zeta]
    simp [Complex.exp_neg]
  obtain ⟨y, e, he⟩ := GlobalTheory.Moduli.exists_point_of_isPeriod kn.theta kn.laws E H DB l Xo (algebraMap (KA l) ℂ) g ty hpq
    rfl hty DB LinearMap.id PB ⟨rfl, rfl, fun _ => LinearMap.id, fun _ => 1, fun n m _ _ a => ⟨0, by simp⟩,
      fun n _ => ⟨fun a => Iff.rfl, fun a => ⟨a, 0, by simp⟩⟩, fun n _ a a' => by simp, hζ, rfl⟩ hP
  obtain ⟨i, P', hP', hy⟩ := FU.onto y he.1
  obtain ⟨gam, h, hE, -, -, hh⟩ := (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed kn.theta kn.laws E H DB l Xo
    (algebraMap (KA l) ℂ) g ty hpq rfl hty DB (FU.Di i) LinearMap.id (FU.t i) PB P' y (FU.u i P') e (FU.ex i P') he
    ⟨FU.over_σ i P' hP', hP', ⟨FU.ex_add i P' hP', FU.ex_onto i P' hP', ExpUniqFamily.isHolTo_ex FU i P' hP',
      (FU.ex_diff i P' hP').1, (FU.ex_diff i P' hP').2⟩, FU.ex_ker i P' hP', FU.ex_lin i P' hP', FU.ex_weil i P' hP',
      FU.ex_eta i P' hP', FU.ex_etaA i P' hP'⟩).1 hy.symm
  obtain ⟨Z', hZ'⟩ := PeriodObj.exists_lat_move hP hP' gam h hE hh Z
  obtain ⟨K, _, hk, ρ, X, y₀, t₀, m, m', gA, tyA, PA, eA, F, hle, hρ, hX, -, hy₀, -⟩ :=
    kn.cm E H DB l Xo g ty FU i P' hP' Z' c.F c.fin
  obtain ⟨eB, heB, -⟩ := GlobalTheory.CM.ExCompare.exists_isExp_of_family FU i hP' (algebraMap (𝓞 K) K) (algebraMap K ℂ)
    X.B m m' hy₀
  exact ⟨K, inferInstance, inferInstance, (IntermediateField.inclusion hle).toRingHom.toAlgebra, algebraMap K ℂ, ρ, X,
    fun z => eB (h z), RingHom.ext fun _ => rfl, hρ, hX.trans hZ', PeriodObj.isExp_move hP gam h hE hh heB⟩

end GlobalTheory.ArcCM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsScaled
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb perFr
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcCM.Letters

theorem exists_scaled {R : Type} [CommRing R] [IsDomain R] {D₀ : Out.DegPre R} {n : ℕ}
    {sB : ∀ T : Over (Sp R), (T ⟶ D₀.P.A) → Out.GtPt D₀ T} (h : IsSplit D₀ n sB) (r : R) {w : epsR R ⟶ D₀.P.A}
    (hw : IsTangent w) : ∃ ν, GtTanR ν ∧ Out.GtPt.IsPull (spMap (epsScaleR r)) (sB (epsR R) w) ν := by
  let sc : epsR R ⟶ epsR R := Over.homMk (spMap (epsScaleR r)) (by
    show spMap (epsScaleR r) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R))
    rw [spMap_comp_spMap]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])
  let z : Over.mk (𝟙 (Sp R)) ⟶ epsR R := Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (by
    show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _
    rw [spMap_comp_spMap]
    have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]
    exact Spec.map_id (CommRingCat.of R))
  have hz : z ≫ sc ≫ w = 1 := by
    apply Over.OverMorphism.ext
    have e : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (epsScaleR r) =
        spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
      rw [spMap_comp_spMap]
      congr 1
      ext a <;> simp [epsScaleR]
    show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (epsScaleR r) ≫ w.left = _
    rw [← Category.assoc, e, hw]
    exact (Category.id_comp _).symm
  refine ⟨sB _ (sc ≫ w), ⟨sB _ 1, TanPart.isZero_of_isAdd (by simpa using h.2.1 _ 1 1), ?_⟩, h.2.2 _ _ sc w⟩
  have := h.2.2 _ _ z (sc ≫ w)
  rwa [hz] at this

theorem exists_kind {I J : Type} (N m : I → ℕ) (h : ∀ τ, N τ = m τ + 1) (e : (Σ b, Fin (m b)) ≃ J) :
    ∃ kind : ∀ τ, Fin (N τ) → Option J, ∀ τ, Function.Injective (kind τ) ∧ (∃ k, kind τ k = none) ∧
      ∀ j, (∃ k, kind τ k = some j) ↔ (e.symm j).1 = τ := by
  let u : ∀ τ, Fin (N τ) ≃ Option (Fin (m τ)) := fun τ => (finCongr (h τ)).trans (finSuccEquiv _)
  refine ⟨fun τ k => (u τ k).map fun i => e ⟨τ, i⟩, fun τ => ⟨?_, ⟨(u τ).symm none, by simp⟩, fun j => ⟨?_, ?_⟩⟩⟩
  · exact (Option.map_injective (e.injective.comp sigma_mk_injective)).comp (u τ).injective
  · rintro ⟨k, hk⟩
    obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 hk
    simp
  · rintro rfl
    exact ⟨(u _).symm (some (e.symm j).2), by simp⟩

theorem exists_section (hT : Out.SecTwistSt) {K : Type} [Field K] (P : Out.PolAV (Sp K)) :
    ∃ th : P.L.Sec, ∀ s : Sp K, ∃ x : P.A.left, P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th := by
  obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section hT P
  obtain ⟨a, -, hu⟩ := hb b
  refine ⟨b, KeyPow.exists_mem_nonzeroLocus _ b ?_⟩
  by_contra hn
  push Not at hn
  exact zero_ne_one ((hu 0 fun i => by rw [hn i, mul_zero]).trans (hu 1 fun i => by rw [hn i, mul_zero]).symm)

theorem exists_cmIn : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (ρ : 𝓞 K₁) (σ₁ : K₁ →+* ℂ) (X : GlobalTheory.CM.CMObj H K₁ ρ σ₁ (Dw.p - 1) (Dw.q - 1)) (ψ : a.D₀.P.A.left ⟶ X.B.pol.A.left) (n' : ℕ) (La c₁ : ℝ) (ξ : Module.Dual ℤ a.D₀.X) (ν₀ : E) (jj : ℤ), letI := H.starRing; 1 ≤ Dw.p → 1 ≤ Dw.q → 3 ≤ Dw.p + Dw.q → σ₁.comp (algebraMap c.F K₁) = c.F.val.toRingHom → σ₁ (ρ : K₁) = H.rt0 → (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) → IsPolFibre (algebraMap (𝓞 K₁) K₁) X.B.pol a.D₀.P ψ → (∀ x, (a.oa.onB.act x).left ≫ ψ = ψ ≫ (X.B.t.act.act x).left) → 0 < n' → TauCan a.D₀ n' → Module.finrank (𝓞 E) a.D₀.X = 1 → ξ ≠ 0 → BetaAt ξ l.M' a.be ν₀ jj → ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) / 2 ≤ c₁ → ∃ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (s : CMIn a e th jj n' La c₁), s.ξ = ξ ∧ s.ν₀ = ν₀ := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a ρ σ₁ X ψ n' La c₁ ξ ν₀ jj hp hq hpq hσ hρ hLa hψ hact hn hτ hrk hξ hβ htr
  letI := H.starRing
  obtain ⟨th, hth⟩ := exists_section hK.laws2.secTwist a.D₀.P
  obtain ⟨v, hv⟩ := KeyPow.exists_isLieBasis a.D₀.P.A a.D₀.P.smoothDim
  have hf : 0 < Module.finrank ℚ E / 2 := by
    have e := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at e
    have : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  have gB : X.B.g = Module.finrank ℚ E / 2 * (Dw.p - 1 + (Dw.q - 1)) :=
    (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K₁ ρ X.B ⟨a.D₀.P, ψ, hψ, v, hv⟩ _ _ X.split X.typeB X.ρ_sq).2.2.2.1
  have hg : 1 ≤ a.D₀.P.g := by
    rw [hψ.1]
    show 1 ≤ X.B.g
    rw [gB]
    exact Nat.mul_pos hf (by omega)
  have hlab : ∀ τ, τ ∈ psiSet H ↔ labK c K₁ τ (H.rt : E) = (ρ : K₁) := fun τ => by
    have e : σ₁ (labK c K₁ τ (H.rt : E)) = τ (H.rt : E) := RingHom.congr_fun hσ (embF c τ (H.rt : E))
    rw [← σ₁.injective.eq_iff, e, hρ]
    rfl
  let xB : KeyIn K₁ := ⟨a.D₀.P, hg, a.D₀.rig, a.D₀.rig_gen, th, hth, v, hv⟩
  obtain ⟨oa, oaΨ, oa', xΨ, x', φΨ, φ', τΨ, τ', ℓΨ, ℓ', Tl, LamL, hoa, -, -, hgood⟩ :=
    exists_lamObjGood_of_cmObj hK.laws2.secTwist hK.theta hK.laws hK.hom E H l c (fun _ => rfl) K₁ ρ σ₁ _ _ X La hlab
      hLa xB ψ ((isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K₁) K₁) X.B.pol xB ψ).2 hψ)
  obtain ⟨L, hL, hm⟩ := exists_lamLetters_isGood E H l c _ _ _ _ La hgood
  obtain ⟨kind, hkind⟩ := exists_kind Dw.mult L.m (fun τ => by
    unfold Datum.mult
    split_ifs with h
    · rw [(hm τ).1 h]; omega
    · rw [(hm τ).2 h]; omega) L.e
  obtain ⟨sB, hsB⟩ := GlobalTheory.ArcCM.exists_isSplit hK K₁ a.D₀ n' hn hτ.1
  have tor : ∀ τ : E →+* ℂ, ∃ ν : Out.GtPt a.D₀ (epsR K₁), GtTanR ν ∧ ν.b = Out.DegPre.zeroT a.D₀ (epsR K₁) ∧
      ∀ x, DlogTan ν x (labK c K₁ τ (cc (pairE ξ x))) := fun τ =>
    ((GlobalTheory.TorusTangent.main hK.laws.globalFns K₁ a.D₀).1 (AddMonoidHom.mk' (fun x => labK c K₁ τ (cc (pairE ξ x)))
      fun x y => by rw [(pairE_properties E a.D₀.X ξ).2.1, cc, map_add (f := _), map_add (f := _)]; rfl)).exists
  have ab : ∀ m : Fin a.D₀.P.g, ∃ ν : Out.GtPt a.D₀ (epsR K₁), GtTanR ν ∧ ∃ w : epsR K₁ ⟶ a.D₀.P.A, L.IsLetter m w ∧
      Out.GtPt.IsPull (spMap (epsScaleR ((n' : K₁)⁻¹))) (sB (epsR K₁) w) ν := fun m => by
    obtain ⟨w, hw, hc⟩ := hL.2.2.1 m
    obtain ⟨ν, h₁, h₂⟩ := exists_scaled hsB ((n' : K₁)⁻¹) (w := w) (GlobalTheory.Reg.isTangent_of_isLieComb hv.1 hc)
    exact ⟨ν, h₁, w, hw, h₂⟩
  choose et het using tor
  choose ea hea using ab
  refine ⟨fun τ k => (kind τ k).elim (et τ) ea, th,
    { B := X.B.pol, oa := oa, AΨ := (X.A true).pol, oaΨ := oaΨ, A' := (X.A false).pol, oa' := oa'
      φΨ := fun i => X.φ (Sum.inl i), φ' := fun i => X.φ (Sum.inr i)
      hΨ := fun i => X.hh (Sum.inl i), h' := fun i => X.hh (Sum.inr i)
      g_pos := hg, th_nz := hth, v := v, basis := hv, xΨ := xΨ, x' := x', φB := ψ, φΨg := φΨ, φ'g := φ'
      τΨ := τΨ, τ' := τ', ℓΨ := ℓΨ, ℓ' := ℓ', Tl := Tl, LamL := LamL
      good := hgood, act := fun x => by rw [hoa]; exact hact x
      L := L, L_good := hL, n_pos := hn, tau := hτ, sB := sB, split := hsB, rk := hrk, ξ := ξ, ξ_ne := hξ
      ν₀ := ν₀, beta := hβ, tr := htr, kind := kind, full := hkind
      tan := fun τ k => ?_, xi := fun τ k h => ?_, eta := fun τ k m h => ?_ }, rfl, rfl⟩
  · cases kind τ k with
    | none => exact (het τ).1
    | some m => exact (hea m).1
  · rw [h]; exact (het τ).2
  · rw [h]; exact (hea m).2

end GlobalTheory.ArcCM.Letters
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmObjBaseChange
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb perFr
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem exists_cmObj_baseChange : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (K₂ : Type) [Field K₂] [NumberField K₂] (i : K →+* K₂) (σ₂ : K₂ →+* ℂ), σ₂.comp i = σ₁ → ∃ (ρ₂ : 𝓞 K₂) (X₂ : GlobalTheory.CM.CMObj H K₂ ρ₂ σ₂ p q) (_ : SABMap X₂.B.t X.B.t (spMap (RingOfIntegers.mapRingHom i))), (ρ₂ : K₂) = i (ρ : K) ∧ X₂.hh = X.hh := by
  intro _ E _ _ _ H K _ _ ρ σ₁ p q X K₂ _ _ i σ₂ h
  have extend {ρ : 𝓞 K} {σ : K →+* ℂ} {p q : ℕ}
      (X : GlobalTheory.CM.CMObj H K ρ σ p q) (j : K →+* K₂) (σ' : K₂ →+* ℂ)
      (h : σ'.comp j = σ) :
      ∃ (X' : GlobalTheory.CM.CMObj H K₂ (RingOfIntegers.mapRingHom j ρ) σ' p q)
        (a : ∀ b, SABMap (X'.A b).t (X.A b).t (spMap (RingOfIntegers.mapRingHom j)))
        (mb : SABMap X'.B.t X.B.t (spMap (RingOfIntegers.mapRingHom j))),
        X'.hh = X.hh ∧ ∀ i, (X'.φ i).left ≫ mb.φ = (a i.isLeft).φ ≫ (X.φ i).left := open GlobalTheory.CM GlobalTheory.CMExistsCompare in by
    set f := RingOfIntegers.mapRingHom j with hf
    have hinj : Function.Injective f := fun a b e => Subtype.ext (j.injective (congrArg Subtype.val e))
    choose A' a _ using fun b => PAT.exists_pullback E H _ _ (spMap f) (X.A b)
    obtain ⟨B', mb, -⟩ := PAT.exists_pullback E H _ _ (spMap f) X.B
    have hmon : ∀ i, IsMonHom (X.φ i) := fun i => (X.lin i).1
    choose φ' hφm hφ using fun i : Fin p ⊕ Fin q => PairingFibre.exists_hom (a i.isLeft).cart mb.cart (X.φ i)
    have hpt := spMap_int j h
    refine ⟨{ split := ((splits_basic E).2.2 K).2.2 K₂ j X.split |>.1
              ρ_sq := by rw [← map_pow, X.ρ_sq, map_neg, map_natCast]
              A := A', B := B'
              typeP := (hasType_baseChange E H _ _ f _ _ (a true) ρ 1 0).1 hinj X.typeP
              typeM := (hasType_baseChange E H _ _ f _ _ (a false) ρ 0 1).1 hinj X.typeM
              typeB := (hasType_baseChange E H _ _ f _ _ mb ρ p q).1 hinj X.typeB
              hh := X.hh, φ := φ', lin := fun i => ?_, onto := fun y => ?_, weil := fun i => ?_ }, a, mb, rfl, hφ⟩
    · refine ⟨hφm i, fun c => Over.OverMorphism.ext (pt_ext mb ?_ (by rw [Over.w, Over.w]))⟩
      have e := congrArg Over.Hom.left ((X.lin i).2 c)
      simp only [Over.comp_left] at e
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hφ, mb.act, ← Category.assoc,
        (a i.isLeft).act, Category.assoc, e, ← Category.assoc, ← hφ, Category.assoc]
    · obtain ⟨pB, hB⟩ := exists_ptEquiv mb hpt
      choose pA hA using fun b => exists_ptEquiv (a b) hpt
      obtain ⟨x, hx⟩ := X.onto (pB y)
      refine ⟨fun i => (pA i.isLeft).symm (x i), pB.injective ?_⟩
      rw [hx, map_list_prod, List.map_ofFn]
      congr 2
      funext i
      apply Over.OverMorphism.ext
      simp only [Function.comp_apply]
      rw [hB, Over.comp_left, Over.comp_left, Category.assoc]
      erw [hφ]
      rw [← Category.assoc, ← hA, MulEquiv.apply_symm_apply]
    · refine (PairingFibre.weilEq_iff (a i.isLeft).cart (a i.isLeft).cart mb.cart (a i.isLeft).cart X.B.t.PP.isLB
        (X.A i.isLeft).t.PP.isLB B'.t.PP.isLB (A' i.isLeft).t.PP.isLB (sab_lbIso mb) (sab_lbIso (a i.isLeft)) (hφ i) (hφ i)
        ((a i.isLeft).act _) (g₂ := 𝟙 _) (by simp) _).2 ?_
      rw [hpt]
      exact X.weil i
  obtain ⟨X₂, -, mb, hh, -⟩ := extend X i σ₂ h
  exact ⟨_, X₂, mb, rfl, hh⟩

end GlobalTheory.ArcCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmLatticeDataAbelianPartSplitPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmLatticeDataAbelianPartSplitPoint
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb perFr
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM.SplitLat

open GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_pair (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : FD.DataX E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hr : 0 < r) (h𝔄 : 𝔄 ≠ 0) (hΨ : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ X.L', v = a • u}) :
    ∃ (D₁ : Bool → Datum H) (e : ∀ b, (D₁ b).La ≃ₗ[𝓞 E] (𝔄 : Submodule (𝓞 E) E)) (s : Bool → ℤ),
      ((D₁ true).p = 1 ∧ (D₁ true).q = 0) ∧ ((D₁ false).p = 0 ∧ (D₁ false).q = 1) ∧ (∀ b, s b = 1 ∨ s b = -1) ∧
      ∀ b x y, (((D₁ b).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (s b * X.ξ0 * (e b x : E) * FD.cc (e b y : E)) := by
  obtain ⟨t, ht, hκ⟩ : ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ X.κ0 = 2 * (t * X.ξ0) := by
    rcases X.κ0_xi with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; simp⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; simp⟩
  have hd := GlobalTheory.trace_xi_mul_conj_int_iff_mem E r X 𝔄 hr h𝔄 hΛ
  obtain ⟨D, e, hp, hq, he⟩ := SelfDualDatum.exists_datum E H (𝔄 : Submodule (𝓞 E) E) (t * X.ξ0)
    (FractionalIdeal.fg_of_isUnit _ (IsUnit.mk0 _ h𝔄)) (FractionalIdeal.coeToSubmodule_ne_bot.2 h𝔄)
    (by
      have := X.ξ0_im
      rw [FD.cc] at this
      rw [map_mul, map_intCast, this, mul_neg])
    (fun τ hτ => by
      have := X.κ0_sign ⟨τ, (hΨ τ).2 hτ⟩
      rw [hκ, map_mul, map_ofNat] at this
      simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero] at this
      linarith)
    (fun x => by
      refine Iff.trans ?_ (hd x)
      refine forall₂_congr fun y _ => ?_
      rcases ht with rfl | rfl
      · simp [FD.cc]
      · simp only [Int.cast_neg, Int.cast_one, neg_mul, _root_.one_mul, map_neg, FD.cc]
        exact ⟨fun ⟨n, h⟩ => ⟨-n, by rw [Int.cast_neg, ← h, neg_neg]⟩, fun ⟨n, h⟩ => ⟨-n, by rw [h, Int.cast_neg]⟩⟩)
  refine ⟨fun b => match b with | true => D | false => oppDatum D,
    fun b => match b with | true => e | false => e, fun b => match b with | true => t | false => -t,
    ⟨hp, hq⟩, ⟨hq, hp⟩, ?_, ?_⟩
  · rintro (_ | _)
    · rcases ht with rfl | rfl <;> simp
    · exact ht
  · rintro (_ | _) x y
    · change D.La at x y
      change ((-(D.EF x y) : ℤ) : ℚ) = Algebra.trace ℚ E (((-t : ℤ) : E) * X.ξ0 * (e x : E) * FD.cc (e y : E))
      rw [Int.cast_neg, he, ← map_neg]
      congr 1
      simp [FD.cc]
    · exact he x y


omit [IsCMField E] in
theorem exists_nsmul_mem (𝔄 : Submodule (𝓞 E) E) (h : 𝔄 ≠ ⊥) {J : Type} [Fintype J] (c : J → E) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, (n : E) * c i ∈ 𝔄 := by
  classical
  obtain ⟨a, ha, h0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨n, hn, hi⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image fun i => c i / a)
  refine ⟨n.natAbs, Int.natAbs_pos.2 hn, fun i => ?_⟩
  have h1 := 𝔄.smul_mem (⟨n • (c i / a), hi _ (by simp)⟩ : 𝓞 E) ha
  have h2 : (n : E) * c i ∈ 𝔄 := by
    convert h1 using 1
    change _ = (n • (c i / a)) * a
    rw [zsmul_eq_mul, _root_.mul_assoc, div_mul_cancel₀ _ h0]
  rcases Int.natAbs_eq n with h | h
  · rwa [h, Int.cast_natCast] at h2
  · rw [h, Int.cast_neg, Int.cast_natCast, neg_mul] at h2
    exact 𝔄.neg_mem_iff.1 h2

omit [NumberField E] [IsCMField E] in
theorem emb_smul' (τ : E →+* ℂ) (a : E) (v : Fin r → E) :
    FD.Data.emb τ (a • v) = τ a • FD.Data.emb τ v := by
  funext k
  simp [FD.Data.emb]

theorem inv_mulVec_eq_zero {p : ℕ} (hp : p ≤ r) (M : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0)
    {u : Fin r → ℂ}
    (hu : u ∈ Submodule.span ℂ (Set.range fun a : Fin p => FD.col M (Fin.castLE hp a)))
    (k : Fin r) (hk : p ≤ (k : ℕ)) : (M⁻¹.mulVec u) k = 0 := _root_.GlobalTheory.PurePer.inv_mulVec_eq_zero (p := p) (u := u) hp M hM hu k hk

theorem herm_smul_smul (G : Matrix (Fin r) (Fin r) E) (a b : E) (u w : Fin r → E) :
    herm G (a • u) (b • w) = a * cc b * herm G u w := by
  simp only [FD.herm, FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (a : E) (u w : Fin r → E) :
    herm G (a • u) w = a * herm G u w := by
  have := herm_smul_smul G a 1 u w
  simpa [FD.cc] using this

theorem perFr_flow (X : Data E r) {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (h0 : 0 < X.p0) (s : X.Ψ → ℂ)
    (x : Frame X.Ψ r) {v : Fin r → E} (hv : herm X.Gm v ξ = 0) (τ : E →+* ℂ) (i : ℕ) :
    perFr X (X.flow ξ s x) v τ i = perFr X x v τ i := by
  by_cases hτ : τ ∈ X.Ψ
  · rw [PerFlow.flow_mem X hξ s x v ⟨τ, hτ⟩ i, hv]; simp
  · have h' : conjEmb τ ∈ X.Ψ := by
      by_contra h
      exact hτ ((X.cmType τ).2 h)
    have hc : τ = conjEmb (conjEmb τ) := by ext a; simp [conjEmb]
    have hlt : X.p0 - 1 - (X.p0 - 1 - (X.p0 - 1 - i)) < r := by have := X.p0_le; omega
    have key : ∀ y : Frame X.Ψ r, perFr X y v (conjEmb (conjEmb τ)) i =
        perFr X y v (conjEmb (conjEmb τ)) (X.p0 - 1 - (X.p0 - 1 - i)) := fun y => by
      rw [PerFlow.perFr_conj X y v ⟨_, h'⟩ i ⟨_, hlt⟩ (by simp only; omega),
        PerFlow.perFr_conj X y v ⟨_, h'⟩ _ ⟨_, hlt⟩ rfl]
    rw [hc, key, key, PerFlow.flow_conj X ξ s x v ⟨_, h'⟩ _ (by omega), hv]
    simp

theorem perFr_pos (X : Data E r) (ξ : Fin r → E) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (v : Fin r → E)
    (hv : X.Jz x (X.ucomp x ξ (X.embV v)) = Complex.I • X.ucomp x ξ (X.embV v)) (a : E) {τ : E →+* ℂ}
    (hτ : τ ∈ X.Ψ) : ∃ c : ℂ, ∀ i, perFr X x (a • v) τ i = c * perFr X x ξ τ i := by
  obtain ⟨c, u, hu, hp⟩ : ∃ (c : ℂ) (u : Fin r → ℂ), Data.emb τ v = u + c • Data.emb τ ξ ∧ X.ppos x ⟨τ, hτ⟩ u = u := by
    refine ⟨_, X.ucomp x ξ (X.embV v) ⟨τ, hτ⟩, (sub_add_cancel _ _).symm, ?_⟩
    have := congrFun hv ⟨τ, hτ⟩
    funext k
    have h2 := mul_left_cancel₀ Complex.I_ne_zero (congrFun this k)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h2
    linear_combination h2 / 2
  refine ⟨τ a * c, fun i => ?_⟩
  rw [PerFlow.perFr_mem X x _ ⟨τ, hτ⟩, PerFlow.perFr_mem X x _ ⟨τ, hτ⟩]
  split_ifs with hi
  · have h0 := inv_mulVec_eq_zero X.p0_le _ (hx ⟨τ, hτ⟩).1 (u := u) (by
      rw [← hp]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
      ⟨X.p0 + i, hi⟩ (by simp)
    simp only [emb_smul', hu, Matrix.mulVec_smul, Matrix.mulVec_add, Pi.smul_apply, Pi.add_apply, h0,
      smul_eq_mul]
    ring
  · simp

theorem perFr_neg (X : Data E r) (h0 : 0 < X.p0) (ξ : Fin r → E) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (v : Fin r → E)
    (hv : X.Jz x (X.ucomp x ξ (X.embV v)) = -(Complex.I • X.ucomp x ξ (X.embV v))) (a : E) {τ : E →+* ℂ}
    (hτ : τ ∉ X.Ψ) : ∃ c : ℂ, ∀ i, perFr X x (a • v) τ i = c * perFr X x ξ τ i := by
  have h' : conjEmb τ ∈ X.Ψ := by
    by_contra h
    exact hτ ((X.cmType τ).2 h)
  have hc : τ = conjEmb (conjEmb τ) := by ext a; simp [conjEmb]
  generalize conjEmb τ = ρ at h' hc
  subst hc
  obtain ⟨c, u, hu, hp⟩ : ∃ (c : ℂ) (u : Fin r → ℂ), Data.emb ρ v = u + c • Data.emb ρ ξ ∧ X.ppos x ⟨ρ, h'⟩ u = 0 := by
    refine ⟨_, X.ucomp x ξ (X.embV v) ⟨ρ, h'⟩, (sub_add_cancel _ _).symm, ?_⟩
    have := congrFun hv ⟨ρ, h'⟩
    funext k
    have h1 := congrFun this k
    simp only [Data.Jz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at h1
    apply mul_left_cancel₀ Complex.I_ne_zero
    simp only [Pi.zero_apply]
    linear_combination h1 / 2
  refine ⟨starRingEnd ℂ (ρ a) * starRingEnd ℂ c, fun i => ?_⟩
  have hlt : X.p0 - 1 - i < X.p0 := by omega
  rw [PerFlow.perFr_conj X x _ ⟨ρ, h'⟩ i (Fin.castLE X.p0_le ⟨_, hlt⟩) rfl,
    PerFlow.perFr_conj X x _ ⟨ρ, h'⟩ i (Fin.castLE X.p0_le ⟨_, hlt⟩) rfl]
  have h1 := X.hermC_ppos_colP hx ⟨ρ, h'⟩ u ⟨_, hlt⟩
  rw [hp, hermC_zero_left, ← hermC_conj _ X.Gm_herm, eq_comm, map_eq_zero] at h1
  simp only [Data.colP] at h1
  simp only [emb_smul', hu, hermC_smul_right, hermC_add_right, h1]
  ring

theorem exists_coords (X : Data E r) {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (hne : ξ ≠ 0) (hr : 2 ≤ r)
    (lam : Fin (r - 2) → Fin r → E) (hl : ∀ j, herm X.Gm (lam j) ξ = 0)
    (hli : LinearIndependent E (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E)) {v : Fin r → E}
    (hv : herm X.Gm v ξ = 0) : ∃ (c₀ : E) (c : Fin (r - 2) → E), v = c₀ • ξ + ∑ j, c j • lam j := by
  let f : (Fin r → E) →ₗ[E] E := { X.hermL ξ with map_smul' := fun a u => herm_smul_left _ a u ξ }
  have hf : ∀ u, f u = herm X.Gm u ξ := fun _ => rfl
  have hne' : LinearMap.ker f ≠ ⊤ := fun h => by
    have h1 : X.Gm.mulVec (fun b => cc (ξ b)) = 0 := by
      funext a
      have : f (Pi.single a 1) = 0 := LinearMap.mem_ker.1 (h ▸ Submodule.mem_top)
      simpa [hf, herm, Pi.single_apply, Matrix.mulVec, dotProduct] using this
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero X.Gm_det h1
    exact hne (funext fun b => by simpa [cc] using congrFun h2 b)
  have hlt := Submodule.finrank_lt hne'
  have hle : Submodule.span E (Set.range (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E)) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · exact hξ
    · exact hl j
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    rw [finrank_span_eq_card hli]
    simp at hlt ⊢
    omega)
  have hm : v ∈ LinearMap.ker f := hv
  rw [← heq, Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  exact ⟨c 0, fun j => c j.succ, by rw [← hc, Fin.sum_univ_succ]; simp⟩

omit [IsCMField E] in
theorem eq_zero_of_trace {z : E} (h : ∀ b : 𝓞 E, Algebra.trace ℚ E ((b : E) * z) = 0) : z = 0 := by
  by_contra hz
  obtain ⟨n, hn, hi⟩ := exists_integral_multiples ℤ ℚ ({z⁻¹} : Finset E)
  have := h ⟨n • z⁻¹, hi _ (by simp)⟩
  change Algebra.trace ℚ E ((n • z⁻¹) * z) = 0 at this
  rw [smul_mul_assoc, inv_mul_cancel₀ hz, map_zsmul, ← map_one (algebraMap ℚ E), Algebra.trace_algebraMap] at this
  simp [hn, Module.finrank_pos.ne'] at this


omit [IsCMField E] in
theorem eq_zero_of_rank_one {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Module (𝓞 E) X]
    (hrk : Module.finrank (𝓞 E) X = 1) (ξ : Module.Dual ℤ X) (hξ : ξ ≠ 0) {y : X} (hy : ∀ b : 𝓞 E, ξ (b • y) = 0) :
    y = 0 := by
  have hdvd : ∀ s : 𝓞 E, s ≠ 0 → ∃ (n : ℕ) (t : 𝓞 E), n ≠ 0 ∧ (n : 𝓞 E) = t * s := fun s hs => by
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {s}))
    exact ⟨_, t, by simpa [Ideal.absNorm_eq_zero_iff] using hs, ht.symm⟩
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨x, hx⟩ : ∃ x, ξ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hξ (LinearMap.ext h)
  have hn : ¬ LinearIndependent (𝓞 E) ![y, x] := fun hi => by
    have := hi.fintype_card_le_finrank
    simp [hrk] at this
  rw [LinearIndependent.pair_iff] at hn
  push Not at hn
  obtain ⟨s, t, e, hne⟩ := hn
  by_cases ht : t = 0
  · obtain ⟨n, u, hn, hu⟩ := hdvd s fun hs => hne hs ht
    rw [ht, zero_smul, add_zero] at e
    have : (n : ℤ) • y = 0 := by
      rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), hu, mul_smul, e, smul_zero]
    exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hn)
  · obtain ⟨n, u, hn, hu⟩ := hdvd t ht
    have h1 : n • x = (-(u * s)) • y := by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E), hu, mul_smul, eq_neg_of_add_eq_zero_right e, smul_neg, neg_smul, mul_smul]
    have h2 := hy (-(u * s))
    rw [← h1, map_nsmul] at h2
    simp [hn, hx] at h2


omit [IsCMField E] in
theorem apply_eq_zero {g g' : ℕ} {M : Type} (ty : Fin g → (E →+* ℂ)) (ty' : Fin g' → (E →+* ℂ))
    (π : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (P : M → Fin g → ℂ) (hP : Submodule.span ℝ (Set.range P) = ⊤)
    (hπ : ∀ (a : 𝓞 E) m i, π (fun j => ty j a * P m j) i = ty' i a * π (P m) i) (i : Fin g') (z t : Fin g → ℂ)
    (ht : π t i = 0) (c : ℂ) (hz : ∀ j, ty j = ty' i → z j = c * t j) : π z i = 0 := by
  classical
  have h1 : ∀ (a : 𝓞 E) (w : Fin g → ℂ), π (fun j => ty j a * w j) i = ty' i a * π w i := fun a w => by
    have hw : w ∈ Submodule.span ℝ (Set.range P) := hP ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨m, rfl⟩ := hw; exact hπ a m i
    | zero =>
      have : (fun j => ty j a * (0 : Fin g → ℂ) j) = 0 := by funext j; simp
      rw [this, map_zero]; simp
    | add u w _ _ hu hw =>
      have : (fun j => ty j a * (u + w) j) = (fun j => ty j a * u j) + fun j => ty j a * w j := by
        funext j; simp [mul_add]
      rw [this, map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, hu, hw, mul_add]
    | smul s w _ hw =>
      have : (fun j => ty j a * (s • w) j) = (s : ℂ) • fun j => ty j a * w j := by
        funext j; simp; ring
      rw [this, ← Complex.coe_smul, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, hw, smul_eq_mul, smul_eq_mul]
      ring
  have h2 : ∀ j, ty j ≠ ty' i → π (Pi.single j 1) i = 0 := fun j hj => by
    by_contra h
    apply hj
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => ?_
    have h3 := h1 a (Pi.single j 1)
    have : (fun k => ty k a * (Pi.single j 1 : Fin g → ℂ) k) = ty j a • (Pi.single j 1 : Fin g → ℂ) := by
      funext k
      by_cases hk : k = j
      · simp [hk]
      · simp [hk]
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul] at h3
    exact mul_right_cancel₀ h h3
  have h4 : ∀ w : Fin g → ℂ, π w i = ∑ j, w j * π (Pi.single j 1) i := fun w => by
    conv_lhs => rw [pi_eq_sum_univ' w]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Finset.sum_apply]
  have h5 : π z i = c * π t i := by
    rw [h4, h4 t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : ty j = ty' i
    · rw [hz j hj, _root_.mul_assoc]
    · simp [h2 j hj]
  rw [h5, ht, mul_zero]

theorem exists_cmLat (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {p q : ℕ} (Y : Data E r) (x : Frame Y.Ψ r) (hx : x ∈ Y.dom)
    (X : DataX E r) (hX : X.toData = Y) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (h𝔄 : 𝔄 ≠ 0)
    (h0 : 0 < Y.p0) (hrk : r = p + q + 2) (hp0 : Y.p0 = q + 1) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ X.L', v = a • u})
    (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)
    (L : Y.Λ →ₗ[𝓞 E] D.La) (ξ : Fin r → E) (hξ : Y.IsIso ξ) (hL : L ⟨ξ, hξ.1⟩ = 0)
    (isom : ∀ a b : Y.Λ, herm Y.Gm a ξ = 0 → herm Y.Gm b ξ = 0 →
      ((D.EF (L a) (L b) : ℤ) : ℚ) = Algebra.trace ℚ E (-Y.ξ0 * herm Y.Gm a b))
    (onto : ∀ z, ∃ a : Y.Λ, herm Y.Gm a ξ = 0 ∧ L a = z)
    (pm : ∀ a : Y.Λ, herm Y.Gm a ξ = 0 → ∀ i, (∃ c : ℂ, ∀ n, perFr Y x a (ty i) n = c * perFr Y x ξ (ty i) n) →
      Pe (L a) i = 0)
    (La : ℝ) (lam : Fin (r - 2) → Fin r → E) (hl : SplitData X ξ La (hX ▸ x) lam) :
    ∃ Z : CMLat hP p q, ∀ j (τ : E →+* ℂ), ‖τ (Z.hh j : E)‖ ≤ La ^ 2 := by
  classical
  subst hX
  obtain ⟨D₁, e, s, h1, h2, hs, he⟩ := exists_pair H X 𝔄 (by omega) h𝔄 hΨ hΛ
  obtain ⟨hL', hli, -, hpos, hneg, hbd⟩ := hl
  let σ : Fin p ⊕ Fin q ≃ Fin (r - 2) := (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))
  have hσl : ∀ j, X.p0 - 1 ≤ (σ (.inl j) : ℕ) := fun j => by simp [σ, hp0]
  have hσr : ∀ j, (σ (.inr j) : ℕ) < X.p0 - 1 := fun j => by simp [σ, hp0]
  have hmem : ∀ (a : (𝔄 : Submodule (𝓞 E) E)) j, (a : E) • lam j ∈ X.Λ := fun a j =>
    hΛ ▸ Submodule.subset_span ⟨a, a.2, _, (hL' j).1, rfl⟩
  have hperp : ∀ (a : E) j, herm X.Gm (a • lam j) ξ = 0 := fun a j => by rw [herm_smul_left, (hL' j).2, mul_zero]
  let m : Fin (r - 2) → (𝔄 : Submodule (𝓞 E) E) →ₗ[𝓞 E] X.Λ := fun j =>
    { toFun := fun a => ⟨_, hmem a j⟩
      map_add' := fun a b => Subtype.ext (add_smul _ _ _)
      map_smul' := fun c a => Subtype.ext (smul_assoc _ _ _) }
  let f : ∀ j : Fin p ⊕ Fin q, (D₁ j.isLeft).La →ₗ[𝓞 E] D.La := fun j => L ∘ₗ m (σ j) ∘ₗ (e _).toLinearMap
  have hf : ∀ j a, f j a = L ⟨(e _ a : E) • lam (σ j), hmem _ _⟩ := fun j a => rfl
  let hh : Fin p ⊕ Fin q → 𝓞 E := fun j =>
    -(s j.isLeft : 𝓞 E) * ⟨herm X.Gm (lam (σ j)) (lam (σ j)), X.L'_int _ (hL' _).1 _ (hL' _).1⟩
  have hhh : ∀ j, (hh j : E) = -(s j.isLeft : E) * herm X.Gm (lam (σ j)) (lam (σ j)) := fun j => by
    simp only [hh]
    rfl
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := fun τ => by
    refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
    rw [← map_pow, HostModel.coe_sq_eq_neg H.rt_sq, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  refine ⟨⟨D₁, h1, h2, f, ?_, hh, fun j a b => ?_, ?_⟩, fun j τ => ?_⟩
  · rintro (j | j) a k hk
    · have hk' : ty k (H.rt : E) ≠ H.rt0 := by simpa using hk
      exact pm ⟨(e _ a : E) • lam (σ (.inl j)), hmem _ _⟩ (hperp _ _) k (perFr_neg X.toData h0 ξ hx _ (hneg _ (hσl j)).2 _ fun h => hk' ((hΨ _).1 h))
    · have hk' : ty k (H.rt : E) ≠ -H.rt0 := by simpa using hk
      exact pm ⟨(e _ a : E) • lam (σ (.inr j)), hmem _ _⟩ (hperp _ _) k (perFr_pos X.toData ξ hx _ (hpos _ (hσr j)).2 _
        ((hΨ _).2 ((hsq _).resolve_right hk')))
  · apply Int.cast_injective (α := ℚ)
    rw [hf, hf, isom ⟨(e _ a : E) • lam (σ j), hmem _ _⟩ ⟨(e _ b : E) • lam (σ j), hmem _ _⟩ (hperp _ _) (hperp _ _),
      he, map_smul, Submodule.coe_smul, Algebra.smul_def (hh j),
      ← RingOfIntegers.coe_eq_algebraMap, hhh]
    congr 1
    rw [herm_smul_smul]
    rcases hs j.isLeft with h | h <;> rw [h] <;> push_cast <;> ring
  · let N : Submodule (𝓞 E) D.La := LinearMap.range (∑ j, f j ∘ₗ LinearMap.proj j)
    have hN : ∀ a, a ∈ N ↔ ∃ x : ∀ j : Fin p ⊕ Fin q, (D₁ j.isLeft).La, a = ∑ j, f j (x j) := fun a => by
      simp only [N, LinearMap.mem_range, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      exact exists_congr fun _ => eq_comm
    obtain ⟨S, hS⟩ := D.fin.fg_top
    choose v hv hLv using onto
    choose c₀ c hc using fun z => exists_coords X.toData hξ.2.1 hξ.2.2 (by omega) lam (fun j => (hL' j).2) hli (hv z)
    obtain ⟨n, hn, hnc⟩ := exists_nsmul_mem (𝔄 : Submodule (𝓞 E) E) (FractionalIdeal.coeToSubmodule_ne_bot.2 h𝔄)
      (fun i : S × Fin (r - 2) => c i.1 i.2)
    obtain ⟨n', hn', hnc'⟩ := exists_nsmul_mem (1 : Submodule (𝓞 E) E) one_ne_zero (fun i : S => c₀ i.1)
    refine ⟨n' * n, by positivity, fun a => (hN _).1 ?_⟩
    have : (⊤ : Submodule (𝓞 E) D.La) ≤ N.comap ((n' * n) • LinearMap.id) := by
      rw [← hS, Submodule.span_le]
      intro a ha
      obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hnc' ⟨a, ha⟩)
      refine (hN _).2 ⟨fun j => n' • (e _).symm ⟨_, hnc (⟨a, ha⟩, σ j)⟩, ?_⟩
      have h5 : (n' * n) • v a = (n • b) • (⟨ξ, hξ.1⟩ : X.Λ) +
          ∑ j, n' • (⟨((n : E) * c a (σ j)) • lam (σ j), hmem ⟨_, hnc (⟨a, ha⟩, σ j)⟩ _⟩ : X.Λ) := by
        apply Subtype.ext
        simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_add, AddSubmonoidClass.coe_nsmul,
          Submodule.coe_smul]
        rw [Equiv.sum_comp σ (fun j => n' • ((n : E) * c a j) • lam j), hc a, smul_add, Finset.smul_sum,
          ← algebraMap_smul E (n • b), map_nsmul, hb]
        congr 1
        · funext k; simp; ring
        · refine Finset.sum_congr rfl fun j _ => ?_
          funext k; simp; ring
      have h6 := congrArg L h5
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_nsmul, hLv, map_add (f := _), map_smul, hL, smul_zero, zero_add, map_sum] at h6
      refine h6.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [map_nsmul, map_nsmul, hf]
      simp only [LinearEquiv.apply_symm_apply]
    exact this Submodule.mem_top
  · change ‖τ (hh j : E)‖ ≤ _
    have h4 : ‖τ (hh j : E)‖ = ‖τ (herm X.Gm (lam (σ j)) (lam (σ j)))‖ := by
      rw [hhh]
      rcases hs j.isLeft with h | h <;> rw [h] <;> simp
    rw [h4]
    by_cases hτ : τ ∈ X.Ψ
    · exact hbd _ ⟨τ, hτ⟩
    · have := hbd (σ j) ⟨ComplexEmbedding.conjugate τ, by
        by_contra h
        exact hτ ((X.cmType τ).2 h)⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using this

theorem exists_cmLat_abelianPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (La : ℝ) (lam : Fin (r - 2) → Fin r → E), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → SplitData Xx ξ' La (hX ▸ x) lam → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → ∀ hB : AbDat H A DB tyB eB, ∃ Z : GlobalTheory.CM.CMLat hB.2.2.2.2 DB.p DB.q, ∀ j (τ : E →+* ℂ), ‖τ (Z.hh j : E)‖ ≤ La ^ 2 := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x Xx hX 𝔄 La lam _ hU hξ hx h𝔄 hΛ hl
  letI := H.starRing
  intro A gam ξ DB tyB eB hO hrk hp hq hB
  obtain ⟨hr, h2, -⟩ := hU
  obtain ⟨hp0, hΨ⟩ := h2 k
  obtain ⟨hEF, ⟨t, ht, htξ⟩, T₀, hT⟩ := hO
  obtain ⟨s, hs, h, hh⟩ := hT (((T₀ + 1 : ℝ) : ℂ) * Complex.I) (by simp)
  obtain ⟨τ₀⟩ : Nonempty (U.X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases hτ : τ ∈ (U.X k).Ψ
    · exact ⟨⟨τ, hτ⟩⟩
    · exact ⟨⟨ComplexEmbedding.conjugate τ, by
        by_contra h'
        exact hτ (((U.X k).cmType τ).2 h')⟩⟩
  obtain ⟨hb1, hb2⟩ := IsotropicIndexSums.isotropicIndex_bounds (U.X k) hξ.2.1 hξ.2.2 τ₀
  have hξy : ∀ v, ((ξ (gam v).y : ℤ) : ℚ) =
      Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ') := fun v => by
    rw [← htξ, LinearMap.IsAlt.neg (Uw.F.Di (Uw.ik k)).alt, Uw.iso, ht]
  have hξb : ∀ (b : 𝓞 E) v, ((ξ (b • (gam v).y) : ℤ) : ℚ) =
      Algebra.trace ℚ E ((b : E) * (-(U.X k).ξ0 * herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ')) := fun b v => by
    rw [← AnArc.La.smul_y, ← map_smul, hξy, map_smul, Submodule.coe_smul, ← algebraMap_smul E, herm_smul_left,
      mul_left_comm]
  have hξ0 : ξ ≠ 0 := fun h0 => by
    have : (Uw.F.Di (Uw.ik k)).EF t = (Uw.F.Di (Uw.ik k)).EF 0 := LinearMap.ext fun v => by
      simpa [h0] using htξ v
    apply hξ.2.2
    rw [← ht, (Uw.F.Di (Uw.ik k)).unimod.1 this]
    simp
  have hy : ∀ v, herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ' = 0 → (gam v).y = 0 := fun v hv =>
    eq_zero_of_rank_one hrk ξ hξ0 fun b => by
      have := hξb b v
      rw [hv] at this
      simpa using this
  have hty : (gam t).y = 0 := hy t (ht ▸ ht ▸ hξ.2.1)
  have htl : (gam t).l = 0 := by
    refine A.Ef_bij.1 (LinearMap.ext fun m => ?_)
    have h1 := htξ (gam.symm (AnArc.La.mk 0 0 m))
    rw [← hEF, gam.apply_symm_apply, AnArc.EF_apply] at h1
    simpa using h1
  let L₀ : A.La →ₗ[𝓞 E] DB.La :=
    { toFun := fun v => eB.symm v.l
      map_add' := fun _ _ => by simp
      map_smul' := fun a v => eB.injective (by simp [hB.2.2.1]) }
  let L : (U.X k).Λ →ₗ[𝓞 E] DB.La := L₀ ∘ₗ gam.toLinearMap ∘ₗ (Uw.φ k).symm.toLinearMap
  have hL : ∀ v, eB (L (Uw.φ k v)) = (gam v).l := fun v => by simp [L, L₀]
  refine exists_cmLat H (U.X k) x hx Xx hX 𝔄 h𝔄 hb1 (by omega) (by omega) hΨ hΛ DB hB.2.2.2.2 L ξ' hξ ?_ ?_ ?_ ?_
    La lam hl
  · have : (⟨ξ', hξ.1⟩ : (U.X k).Λ) = Uw.φ k t := Subtype.ext ht.symm
    apply eB.injective
    rw [this, hL, htl, map_zero]
  · intro a b ha hb
    obtain ⟨a, rfl⟩ := (Uw.φ k).surjective a
    obtain ⟨b, rfl⟩ := (Uw.φ k).surjective b
    rw [← Uw.iso, ← hEF, hB.2.2.2.1, hL, hL, AnArc.EF_apply, hy a ha, hy b hb]
    simp
  · intro z
    refine ⟨Uw.φ k (gam.symm (AnArc.La.mk 0 0 (eB z))), ?_, eB.injective (by rw [hL]; simp)⟩
    have := eq_zero_of_trace fun b => (hξb b (gam.symm (AnArc.La.mk 0 0 (eB z)))).symm.trans (by simp)
    exact (mul_eq_zero.1 this).resolve_left (neg_ne_zero.2 (U.X k).ξ0_ne)
  · rintro a ha i ⟨c', hc'⟩
    obtain ⟨a, rfl⟩ := (Uw.φ k).surjective a
    let π : (Fin Uw.g → ℂ) →ₗ[ℂ] (Fin A.gB → ℂ) := LinearMap.snd ℂ _ _ ∘ₗ h.toLinearMap
    have hπ : ∀ v, π (Uw.Pm k ⟨_, hs⟩ v) = A.ct (gam v).y + (gam v).l := fun v => by
      simp [π, hh]
    have hper := Uw.period k ⟨_, hs⟩
    have key := apply_eq_zero _ tyB π (Uw.Pm k ⟨_, hs⟩) hper.2.2.2.1 (fun b m j => by
      rw [← funext (hper.1 b m), hπ, hπ, map_smul, AnArc.La.smul_y, AnArc.La.smul_l, A.ct_smul, AnArc.coe_FLam,
        ← map_add (f := _), hB.1]) i (Uw.Pm k ⟨_, hs⟩ a) (Uw.Pm k ⟨_, hs⟩ t) (by simp [hπ, hty, htl]) c' (fun j hj => by
      rw [Uw.Pm_eq, Uw.Pm_eq, ht, perFr_flow _ hξ.2.1 hb1 _ _ ha, perFr_flow _ hξ.2.1 hb1 _ _ hξ.2.1, hj, hc'])
    rw [hπ, hy a ha, map_zero, zero_add, ← hL] at key
    exact key

end GlobalTheory.ArcCM.SplitLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmLatticeDataAbelianPartSplitPointStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb perFr
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cm_lattice_data_abelianPart_split_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (La : ℝ) (lam : Fin (r - 2) → Fin r → E), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → SplitData Xx ξ' La (hX ▸ x) lam → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → ∀ hB : AbDat H A DB tyB eB, ∃ Z : GlobalTheory.CM.CMLat hB.2.2.2.2 DB.p DB.q, ∀ j (τ : E →+* ℂ), ‖τ (Z.hh j : E)‖ ≤ La ^ 2 := by
  first | exact @GlobalTheory.ArcCM.SplitLat.exists_cmLat_abelianPart | exact GlobalTheory.ArcCM.SplitLat.exists_cmLat_abelianPart | (intros; apply GlobalTheory.ArcCM.SplitLat.exists_cmLat_abelianPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataAtSplitIsotropicPoint
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb perFr
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM.Exist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_lift_fibre {R R₂ K : Type} [CommRing R] [CommRing R₂] [Field K] {B : GlobalTheory.CM.PAT H (Sp R)}
    {B₂ : GlobalTheory.CM.PAT H (Sp R₂)} {j : R →+* R₂} (m : SABMap B₂.t B.t (spMap j)) {f : R →+* K} {f₂ : R₂ →+* K}
    (hf : f₂.comp j = f) {P : Out.PolAV (Sp K)} {ψ : P.A.left ⟶ B.pol.A.left} (hψ : IsPolFibre f B.pol P ψ)
    (act : 𝓞 E → (P.A ⟶ P.A)) (hact : ∀ x, (act x).left ≫ ψ = ψ ≫ (B.t.act.act x).left) :
    ∃ ψ₂ : P.A.left ⟶ B₂.pol.A.left, IsPolFibre f₂ B₂.pol P ψ₂ ∧
      ∀ x, (act x).left ≫ ψ₂ = ψ₂ ≫ (B₂.t.act.act x).left := by
  have hs : spMap f₂ ≫ spMap j = spMap f := (GlobalTheory.ArcId.sp_comp _ _).trans (congrArg spMap hf)
  have w : ψ ≫ B.t.G.hom = (P.A.hom ≫ spMap f₂) ≫ spMap j :=
    hψ.2.1.1.w.trans (by rw [Category.assoc, hs])
  obtain ⟨ψ₂, h₁, h₂⟩ : ∃ ψ₂ : P.A.left ⟶ B₂.t.G.left, ψ₂ ≫ m.φ = ψ ∧ ψ₂ ≫ B₂.t.G.hom = P.A.hom ≫ spMap f₂ :=
    ⟨_, m.cart.1.lift_fst _ _ w, m.cart.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback P.A B₂.t.G (spMap f₂) ψ₂ := m.cart.cancel (hψ.2.1.congr hs.symm h₁.symm) h₂
  refine ⟨ψ₂, ⟨?_, g₂, ?_⟩, fun x => ?_⟩
  · exact H1.dim_unique P.A.hom P.smoothDim
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback g₂.1 B₂.dim)
      (eSec P.A (IsLocalRing.closedPoint K))
  · have e : LBIso (B₂.t.PP.L.pull ψ₂) (B.t.PP.L.pull ψ) :=
      GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) ψ₂ h₁.symm
    exact LBIso.trans (pull_isLB B₂.t.PP.isLB _) (pull_isLB B.t.PP.isLB _) P.isLB e hψ.2.2
  · apply m.cart.1.hom_ext
    · have e := m.act x
      change ((act x).left ≫ ψ₂) ≫ m.φ = (ψ₂ ≫ (B₂.t.act.act x).left) ≫ m.φ
      rw [Category.assoc, Category.assoc, h₁, hact, e, ← Category.assoc, h₁]
    · rw [Category.assoc, Category.assoc, h₂, Over.w (B₂.t.act.act x), h₂, ← Category.assoc, Over.w (act x)]

theorem one_le_of_isIso {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
    {U : Unf Xo c σ r} (hU : IsUnf U) {k : U.Comp} {ξ' : Fin r → E} (hξ : (U.X k).IsIso ξ') :
    1 ≤ Dw.p ∧ 1 ≤ Dw.q := by
  obtain ⟨τ⟩ : Nonempty (U.X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : τ ∈ (U.X k).Ψ
    · exact ⟨⟨τ, h⟩⟩
    · exact ⟨⟨_, by_contra fun h' => h (((U.X k).cmType τ).2 h')⟩⟩
  have h := IsotropicIndexSums.isotropicIndex_bounds (U.X k) hξ.2.1 hξ.2.2 τ
  have h1 := hU.1
  have h2 := (hU.2.1 k).1
  omega

theorem exists_cmIn_tie : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (La₀ La c₁ : ℝ) (lam : Fin (r - 2) → Fin r → E) (n' : ℕ) (ν₀ : E), IsUnf U → l.A = 1 → 3 ≤ r → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → SplitData Xx ξ' La₀ (hX ▸ x) lam → La₀ ^ 2 ≤ La ^ 2 → 0 < n' → (∀ m ∈ (U.X k).Λp ξ', ∃ e : E, e • ξ' ∈ (U.X k).Λ ∧ (n' : ℂ) • (U.X k).aproj x ξ' ((U.X k).embV m) = (U.X k).embV (e • ξ')) → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s : E, cc s = s → (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (l.M' : E) • u) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) / 2 ≤ c₁ → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra c.F K₁) (em : K₁ →+* ℂ) (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (s : CMIn a e th jj n' La c₁), em.comp (algebraMap c.F K₁) = c.F.val.toRingHom ∧ s.ν₀ = ν₀ ∧ Comparison₂ Uw a em s.ξ k ξ' x := by
  intro hK E _ _ _ H Dw l Xo c _ _ r U Uw k ξ' x Xx hX 𝔄 La₀ La c₁ lam n' ν₀ hU hA hr hξ hx h𝔄 hΛ hS hLa hn hap hν hν₀
    hint htr
  letI := H.starRing
  have hg : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨hp, hq⟩ := one_le_of_isIso hU hξ
  have hpq : 3 ≤ Dw.p + Dw.q := hU.1 ▸ hr
  obtain ⟨A, gam, ξ, jj, DB, tyB, eB, hO, hξ0, hrk, hdvd, hbeta, hprim, hct, hab, hDp, hDq⟩ :=
    GlobalTheory.T.exists_analytic_model_on_frame_orbit_isolating E H Dw l Xo c _ r U Uw k ξ' x n' ν₀ hg hU hξ hx hap hν hν₀ hint
  obtain ⟨A', gam', ξ₁, eX, hO', hprim', hnorm', hξ₁, hbe', hab'⟩ :=
    GlobalTheory.ArcShift.exists_normAn_onOrbit E H Dw l Xo c _ r U Uw k ξ' x n' hg hU hξ hx hn A gam ξ hO hξ0 hrk hprim hct
  obtain ⟨tyB', eB', hB'⟩ := hab' DB ⟨tyB, eB, hab⟩
  have hrk' : Module.finrank (𝓞 E) A'.X = 1 := eX.finrank_eq.trans hrk
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_cm_lattice_data_abelianPart_split_point E H Dw l Xo c _ r U Uw k ξ' x Xx hX 𝔄 La₀ lam hg hU hξ hx h𝔄 hΛ hS A' gam' ξ₁ DB
    tyB' eB' hO' hrk' hDp hDq hB'
  obtain ⟨K, _, _, _, σ₁, ρ, X, ex, hσ₁, hρ, hhh, hex⟩ :=
    GlobalTheory.ArcCM.exists_cmObj_of_period hK E H l c DB _ tyB' _ hB'.2.2.2.2 Z (by omega) hB'.2.1 hA
  obtain ⟨aC, Λ, hΛA, φ, hφ, hφa, hlift⟩ := GlobalTheory.T.exists_complexArcDatum_cmFibre hK E H Dw l Xo c _ r U Uw k ξ' x (𝓞 K) X.B _ hg hU hA A' gam'
    ξ₁ DB tyB' eB' ex hO' hrk' (fun y y' => (hbe' y y').symm ▸ hdvd _ _) hprim' hB' hDp hDq hp hq hex
  subst hΛA
  have htau : TauCan aC.D₀ n' := (GlobalTheory.KappaAn.tauCan_iff_normAn E H Dw l c _ _ _ aC Λ.toGtAn₀ n').2 hnorm'
  let fC : aC.D₀.X ≃ₗ[𝓞 E] A.X := Λ.eX.symm.trans eX
  let ξC : Module.Dual ℤ aC.D₀.X := ξ.comp (fC.toLinearMap.restrictScalars ℤ)
  have htie := GlobalTheory.T.holomorphicArc_matches_frame_of_model_on_orbit hK E H Dw l Xo c _ r U Uw k ξ' x aC Λ.toGtAn₀ ξC hg hU hξ hx hA gam' ξ₁ hO'
    (fun y => by rw [hξ₁]; exact congrArg (fun z => ξ (eX z)) (Λ.eX.symm_apply_apply y)) hlift
  obtain ⟨K₂, _, _, _, i, σ₂, a, p, ψ, hσ₂, hbc, htau₂, hψ, hψa⟩ :=
    GlobalTheory.T.exists_cmArcData_descent_numberField hK E H Dw l c K σ₁ _ X.B aC φ n' hσ₁ hn hφ hφa htau
  obtain ⟨ρ₂, X₂, m, hρ₂, hh₂⟩ := GlobalTheory.ArcCM.exists_cmObj_baseChange hK E H K ρ σ₁ _ _ X K₂ i σ₂ hσ₂
  obtain ⟨ψ₂, hψ₂, hψa₂⟩ := exists_lift_fibre m (f₂ := algebraMap (𝓞 K₂) K₂) (RingHom.ext fun _ => rfl) hψ
    a.oa.onB.act hψa
  let f : aC.D₀.X ≃ₗ[𝓞 E] a.D₀.X := { p.xe with map_smul' := hbc.2.1 }
  let g : a.D₀.X ≃ₗ[𝓞 E] A.X := f.symm.trans fC
  have hem : σ₂.comp (algebraMap c.F K₂) = c.F.val.toRingHom := by
    rw [← hσ₁, ← hσ₂]
    exact RingHom.ext fun y => congrArg σ₂ (i.commutes y).symm
  have hbe : ∀ y z, a.be y z = A.be (g y) (g z) := fun y z => by
    obtain ⟨y, rfl⟩ := (Λ.eX.trans f).surjective y
    obtain ⟨z, rfl⟩ := (Λ.eX.trans f).surjective z
    refine (hbc.2.2.1 _ _).symm.trans ((Λ.be_eq _ _).trans ((hbe' _ _).trans ?_))
    simp [g, fC]
  have hhh₂ : ∀ j (τ : E →+* ℂ), ‖τ (X₂.hh j : E)‖ ≤ La ^ 2 := fun j τ => by
    rw [hh₂, hhh]; exact (hZ j τ).trans hLa
  have hρ' : σ₂ (ρ₂ : K₂) = H.rt0 := by rw [hρ₂, ← hρ, ← hσ₂]; rfl
  clear m hh₂
  generalize DB.p = p₁, DB.q = q₁ at X₂ hDp hDq hhh₂ ψ₂ hψ₂ hψa₂
  subst hDp hDq
  obtain ⟨e, th, s, hs, hsν⟩ := GlobalTheory.ArcCM.Letters.exists_cmIn hK E H Dw l c K₂ a ρ₂ σ₂ X₂ ψ₂ n' La c₁
    (ξ.comp (g.toLinearMap.restrictScalars ℤ)) ν₀ jj hp hq hpq hem hρ' hhh₂ hψ₂ hψa₂ hn htau₂
    (g.finrank_eq.trans hrk)
    (fun h => hξ0 (LinearMap.ext fun y => by
      obtain ⟨y, rfl⟩ := g.surjective y
      exact LinearMap.congr_fun h y))
    (GlobalTheory.ArcId.betaAt_comp g ξ hbe hbeta) htr
  refine ⟨K₂, _, _, _, σ₂, a, e, th, jj, s, hem, hsν, aC, p, ξC, hbc, fun y => ?_, htie⟩
  rw [hs]
  exact congrArg (fun z => ξ (fC z)) (f.symm_apply_apply y).symm

end GlobalTheory.ArcCM.Exist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataAtSplitIsotropicPointStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb perFr
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmArcData_at_splitIsotropicPoint : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (La₀ La c₁ : ℝ) (lam : Fin (r - 2) → Fin r → E) (n' : ℕ) (ν₀ : E), IsUnf U → l.A = 1 → 3 ≤ r → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → SplitData Xx ξ' La₀ (hX ▸ x) lam → La₀ ^ 2 ≤ La ^ 2 → 0 < n' → (∀ m ∈ (U.X k).Λp ξ', ∃ e : E, e • ξ' ∈ (U.X k).Λ ∧ (n' : ℂ) • (U.X k).aproj x ξ' ((U.X k).embV m) = (U.X k).embV (e • ξ')) → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s : E, cc s = s → (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (l.M' : E) • u) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) / 2 ≤ c₁ → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra c.F K₁) (em : K₁ →+* ℂ) (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (s : CMIn a e th jj n' La c₁), em.comp (algebraMap c.F K₁) = c.F.val.toRingHom ∧ s.ν₀ = ν₀ ∧ Comparison₂ Uw a em s.ξ k ξ' x := by
  first | exact @GlobalTheory.ArcCM.Exist.exists_cmIn_tie | exact GlobalTheory.ArcCM.Exist.exists_cmIn_tie | (intros; apply GlobalTheory.ArcCM.Exist.exists_cmIn_tie <;> assumption)
end
