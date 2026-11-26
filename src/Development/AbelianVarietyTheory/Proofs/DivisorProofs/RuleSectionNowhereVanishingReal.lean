module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSectionAndDegree
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceMoveRationalFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleSectionNowhereVanishingReal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenBasisOfIntegralFramedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEigenBasisTransportPullbackDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEigenBasisTransportPullbackDvr
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits

set_option autoImplicit false

noncomputable section

open MonObj MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntEigTransport

theorem isTan_iff_isTangent' {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] (w : epsR V ⟶ G) :
    IsTan (V := V) (R := V) (G := G) w ↔ IsTangent w := by
  have : (1 : ptOver V V ⟶ G).left = η[G].left := by
    show spMap (algebraMap V V) ≫ _ = _
    rw [show spMap (algebraMap V V) = 𝟙 _ from Spec.map_id _]
    exact Category.id_comp _
  unfold IsTan IsTangent
  rw [this]

theorem transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (G : SAB H (Sp T.V)) (S : Scheme.{0}) (t : SAB H S) (x : Sp T.V ⟶ S) (n : SABMap G t x) (τ : E →+* ℂ) (k : ℕ) (ub : Fin k → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ i, IsEigV c io G τ (ub i)) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → IsEigV c io G τ w → ∃! a : Fin k → T.V, IsComb ub a w) → ∃ v : Fin k → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt x ⟶ t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis t.act x (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (v i).left = (ub i).left ≫ n.φ := by
  intro E _ _ _ H l c T io φ hio G S t x n τ k ub htan heig hbas
  have hz : ∀ (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c τ a) → z = φ (embK c τ a) := by
    intro a z hz
    apply IsFractionRing.injective T.V T.Fr
    rw [hz, ← hio]; rfl
  have hE : ∀ w : epsR T.V ⟶ G.G, IsEigV c io G τ w ↔
      ∀ a, (w ≫ G.act.act a).left = spMap (epsScaleR (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ a)) ≫ w.left := by
    intro w
    constructor
    · intro h a
      exact h a (φ (embK c τ a)) (by rw [← hio]; rfl)
    · intro h a z hz'
      rw [hz a z hz']
      exact h a
  have hC : ∀ (a : Fin k → T.V) (w : epsR T.V ⟶ G.G), IsComb ub a w ↔ IsLieComb a ub w := fun a w => Iff.rfl
  have hv : GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsEigBasis G.act (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) ub := by
    refine ⟨fun i => ⟨(isTan_iff_isTangent' _).1 (htan i), (hE _).1 (heig i)⟩, fun w hw => ?_⟩
    exact (existsUnique_congr fun a => hC a w).1 (hbas w ((isTan_iff_isTangent' _).2 hw.1) ((hE w).2 hw.2))
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.FlatRow.exists_eigenBasis n hv
  exact ⟨u, hu, fun i => (hu' i).symm⟩

end GlobalTheory.IntEigTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEigenBasisTransportPullbackDvrStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralEigenBasis_transport_pullback_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (G : SAB H (Sp T.V)) (S : Scheme.{0}) (t : SAB H S) (x : Sp T.V ⟶ S) (n : SABMap G t x) (τ : E →+* ℂ) (k : ℕ) (ub : Fin k → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ i, IsEigV c io G τ (ub i)) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → IsEigV c io G τ w → ∃! a : Fin k → T.V, IsComb ub a w) → ∃ v : Fin k → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt x ⟶ t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis t.act x (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (v i).left = (ub i).left ≫ n.φ := by
  first | exact @GlobalTheory.IntEigTransport.transport | exact GlobalTheory.IntEigTransport.transport | (intros; apply GlobalTheory.IntEigTransport.transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenBasisOfIntegralFramedPoint
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace GlobalTheory.IntFrameLift

open ReciprocityTheory.ChartRestriction.G.Semi

theorem exists_eigenBasis_sameVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (y : letI := io.toAlgebra; FrPt Xo c T.Fr), Integral T io y → ∀ (χ : Sp T.V ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.genFibre Y), χ ≫ pullback.snd _ _ = spMap φ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y ≫ Y.jQ = spMap (algebraMap T.V T.Fr) ≫ χ) → ∀ (τ : E →+* ℂ) (n : ℕ) (hn : Dw.mult τ = n), ∃ v : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt (χ ≫ pullback.fst _ _) ⟶ Y.t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis Y.t.act (χ ≫ pullback.fst _ _) (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (letI := io.toAlgebra; SameVec Y y (y.u τ (Fin.cast hn.symm i)) (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap T.V T.Fr)) ≫ (v i).left)) := by
  intro E _ _ _ H Dw l Xo c Y T io φ hφ y hI χ hχ1 hχ2 τ n hn
  subst hn
  letI := io.toAlgebra
  obtain ⟨G, t', m1, m2, ⟨ub, htan, heig, hbas, hu⟩, -⟩ := hI
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull (χ ≫ pullback.fst _ _) Y.t
  have hx : GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
  let mK : SABMap t' Xo.univ.t (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _) := ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast m1 hx.symm
  obtain ⟨a, mF, hF0, hFm⟩ := GlobalTheory.CuspFrom.exists_genIdent Y hχ2 mK m
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.ModelUniqueChecks.existsUnique_map T.V T.Fr G t t' m2 a
  obtain ⟨nC, hnC⟩ := sabComp pullCubComp E H _ _ _ Y.t t G (χ ≫ pullback.fst _ _) (𝟙 _) m ψ
  let n' : SABMap G Y.t (χ ≫ pullback.fst _ _) := ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast nC (Category.id_comp _)
  obtain ⟨v, hv, hvl⟩ := GlobalTheory.T.integralEigenBasis_transport_pullback_dvr E H l c T io φ hφ G Y.X Y.t (χ ≫ pullback.fst _ _) n' τ _ (ub τ) (htan τ)
    (heig τ) (hbas τ)
  refine ⟨v, hv, fun i => ?_⟩
  obtain ⟨u', hu1, hu2⟩ := hu τ i
  have hmono : Mono (spMap (algebraMap T.V T.Fr)) := by
    have : Epi (CommRingCat.ofHom (algebraMap T.V T.Fr)) := IsLocalization.epi (nonZeroDivisors T.V) T.Fr
    exact Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  have hbase : spMap (dualMap (algebraMap T.V T.Fr)) ≫ (epsOver T.V T.V).hom =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := by
    show spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) = _
    rw [GlobalTheory.ShFam.OpenReg.spMap_comp, GlobalTheory.ShFam.OpenReg.spMap_comp]
    congr 1
    ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hut : u' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ 𝟙 _ := by
    rw [Category.comp_id]
    apply (cancel_mono (spMap (algebraMap T.V T.Fr))).1
    rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (ub τ i), hbase]
  have htan' : IsTanAtG t' (𝟙 _) u' := by
    have h1 := (GlobalTheory.ShFam.OpenReg.tan_iff m1 (Category.id_comp y.x) hut).1
    rw [hu1] at h1
    exact h1 (y.tan τ i)
  refine ⟨u' ≫ mF.φ, (GlobalTheory.ShFam.OpenReg.tan_iff mF (Category.id_comp _) hut).2 htan', ?_, ?_⟩
  · rw [Category.assoc, hF0, ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast_φ, hu1]
    rfl
  · rw [Category.assoc, hFm, ← hψ, hvl i, ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast_φ, hnC]
    simp only [← Category.assoc]
    rw [hu2]
    rfl

end GlobalTheory.IntFrameLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenBasisOfIntegralFramedPointStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieEigenBasis_of_integralFramedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (y : letI := io.toAlgebra; FrPt Xo c T.Fr), Integral T io y → ∀ (χ : Sp T.V ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.genFibre Y), χ ≫ pullback.snd _ _ = spMap φ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y ≫ Y.jQ = spMap (algebraMap T.V T.Fr) ≫ χ) → ∀ (τ : E →+* ℂ) (n : ℕ) (hn : Dw.mult τ = n), ∃ v : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt (χ ≫ pullback.fst _ _) ⟶ Y.t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis Y.t.act (χ ≫ pullback.fst _ _) (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (letI := io.toAlgebra; SameVec Y y (y.u τ (Fin.cast hn.symm i)) (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap T.V T.Fr)) ≫ (v i).left)) := by
  first | exact @GlobalTheory.IntFrameLift.exists_eigenBasis_sameVec | exact GlobalTheory.IntFrameLift.exists_eigenBasis_sameVec | (intros; apply GlobalTheory.IntFrameLift.exists_eigenBasis_sameVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraTer
namespace GlobalTheory.LiftAndFactorization

open _root_.Formalism.L2.Pj

theorem exists_lift (T : CDVR) (x : T.Fr) (hx : x ≠ 0 → vV T.V x = 0) :
    ∃ b : T.V, algebraMap T.V T.Fr b = x := by
  by_cases h0 : x = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  apply IsDiscreteValuationRing.exists_lift_of_le_one
  have hne : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr x ≠ 0 :=
    (Valuation.ne_zero_iff _).2 h0
  have hlog : WithZero.log ((IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr x) = 0 := by
    have := hx h0
    unfold vV valV at this
    exact neg_eq_zero.1 this
  have := WithZero.exp_log hne
  rw [hlog, WithZero.exp_zero] at this
  exact this.ge

theorem exists_factor (T : CDVR) {F : Type} [Field F] (io : F →+* T.Fr)
    (h : ∀ a : F, a ≠ 0 → vV T.V (io a) = 0) :
    ∃ φ : F →+* T.V, (algebraMap T.V T.Fr).comp φ = io := by
  have key : ∀ a : F, ∃ b : T.V, algebraMap T.V T.Fr b = io a := fun a =>
    exists_lift T (io a) (fun ha => h a (fun h0 => ha (by rw [h0, map_zero])))
  choose f hf using key
  have inj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  refine ⟨{ toFun := f
            map_one' := inj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => inj (by rw [map_mul, hf, hf, hf, map_mul])
            map_zero' := inj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => inj (by rw [map_add (f := _), hf, hf, hf, map_add (f := _)]) }, ?_⟩
  ext a
  exact hf a

end GlobalTheory.LiftAndFactorization
end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.BdryUnitVal

theorem pt_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (y : letI := io.toAlgebra; FrPt Xo c T.Fr), (letI := io.toAlgebra; ∀ s, GlobalTheory.AllWt.ptF y s ∈ (V : Set (Xo.XF c))) → ∃ χ : Sp T.V ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.genFibre Y, χ ≫ pullback.snd _ _ = spMap φ ∧ (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y ≫ Y.jQ = spMap (algebraMap T.V T.Fr) ≫ χ) ∧ Set.range χ ⊆ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.compactification Y V := by
  intro E _ _ _ H Dw l Xo c Y V T io φ hφ y hy
  letI := io.toAlgebra
  obtain ⟨χ, h1, h2⟩ := GlobalTheory.CuspFrom.exists_genPt (K := T.Fr) Y φ hφ y
  refine ⟨χ, h1, h2, ?_⟩
  rintro _ ⟨p, rfl⟩
  let η : Sp T.Fr := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr)
  have hη : χ (spMap (algebraMap T.V T.Fr) η) ∈ Y.jQ '' (V : Set (Xo.XF c)) := by
    rw [← Scheme.Hom.comp_apply, ← h2, Scheme.Hom.comp_apply]
    exact ⟨_, hy η, rfl⟩
  have hp : p ∈ closure {spMap (algebraMap T.V T.Fr) η} := by
    apply (PrimeSpectrum.le_iff_mem_closure _ _).1
    show Ideal.comap (algebraMap T.V T.Fr) (⊥ : Ideal T.Fr) ≤ (p : PrimeSpectrum T.V).asIdeal
    rw [Ideal.comap_bot_of_injective _ (IsFractionRing.injective T.V T.Fr)]
    exact bot_le
  exact map_mem_closure χ.continuous hp (fun z hz => by rw [Set.mem_singleton_iff.1 hz]; exact hη)

end GlobalTheory.BdryUnitVal

namespace GlobalTheory.BdryUnitVal

theorem vV_unit (T : CDVR) (u : T.V) (hu : IsUnit u) : vV T.V (algebraMap T.V T.Fr u) = 0 := by
  have h1 : valV T.V (algebraMap T.V T.Fr u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    refine le_antisymm (HeightOneSpectrum.intValuation_le_one _ _) (not_lt.1 fun h => ?_)
    exact (IsDiscreteValuationRing.maximalIdeal T.V).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ ((HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).1 h) hu)
  rw [vV, h1, WithZero.log_one, neg_zero]

theorem nval_unit (T : CDVR) (u : T.V) (hu : IsUnit u) : nval T.V 1 (algebraMap T.V T.Fr u) = 0 := by
  have hne : algebraMap T.V T.Fr u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hu.ne_zero
  rw [nval_of_ne hne, vV_unit T u hu]
  simp

theorem exists_factor (T : CDVR) {F : Type} [Field F] (io : F →+* T.Fr) (hio : ∀ a, a ≠ 0 → vV T.V (io a) = 0) :
    ∃ φ : F →+* T.V, (algebraMap T.V T.Fr).comp φ = io := by
  first
  | exact @_root_.GlobalTheory.LiftAndFactorization.exists_factor
  | exact _root_.GlobalTheory.LiftAndFactorization.exists_factor
  | (apply _root_.GlobalTheory.LiftAndFactorization.exists_factor <;> assumption)
  | (intros; apply _root_.GlobalTheory.LiftAndFactorization.exists_factor <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LiftAndFactorization.exists_factor <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LiftAndFactorization.exists_factor ..)

end GlobalTheory.BdryUnitVal

namespace GlobalTheory.BdryUnitVal

theorem conj_ne {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (τ : Psi H) :
    conjEmb τ.1 (H.rt : E) ≠ H.rt0 := fun h3 => by
  have h3' : starRingEnd ℂ (τ.1 (H.rt : E)) = H.rt0 := h3
  rw [τ.2] at h3'
  have h4 := H.sqrt_neg_disc_sq
  have h5 : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h3'
  have h6 := congrArg Complex.re h4
  have h7 : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  simp [pow_two, h5] at h6
  nlinarith [mul_self_nonneg H.rt0.re]

end GlobalTheory.BdryUnitVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeSphericalVectorDefiniteUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeSphericalVectorDefiniteUnitary
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameAut

theorem exists_locComp_hasSatGL_heckeVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ φ ∈ π, φ ≠ 0 →
    (∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) → RU E n x φ = φ) →
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ S ∧
      ∀ k ≤ n, GlobalTheory.LFun.heckeVec ((RU E n).comp (locU n w).subtype) ((GlobalTheory.LFun.KGL w (n := n)).comap ((cLoc w).comp (locU n w).subtype))
        (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov E w) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab n k)) ((cLoc w).comp (locU n w).subtype x)) φ =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n S k • φ := by
  intro E _ _ _ n π hπ w hw φ hφ h0 hfix
  obtain ⟨σ, -, hloc, hiff⟩ := GlobalTheory.DefU.exists_locComp_split E n ⟨π, hπ⟩ w hw
  obtain ⟨S, hS⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred (hiff.1 ⟨φ, hφ, h0, hfix⟩)
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hw
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  have hp : Function.Surjective ((cLoc w).comp (locU n w).subtype) := fun g =>
    ⟨e.symm g, (he _).symm.trans (e.apply_symm_apply g)⟩
  refine ⟨σ, S, hloc, hS, fun k hk => ?_⟩
  rw [GlobalTheory.SphPar.divInd_dualLab_splitLab E w n k hϖ]
  exact GlobalTheory.SplitTransfer.heckeVec_eq_of_isCompAlong hπ w (Formalism.UG.Final.GLintComm E w n) _ hp σ.ρ hloc
    (GlobalTheory.LFun.Tj_mem_hecke hϖ k) (fun v hv hv0 => (hS.2 v hv hv0).2.2.2 ϖ hϖ k hk) hφ fun x hx => hfix x x.2 hx

end GlobalTheory.FrameAut

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeSphericalVectorDefiniteUnitaryStatement
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satake_sphericalVector_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ φ ∈ π, φ ≠ 0 →
    (∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) → RU E n x φ = φ) →
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ S ∧
      ∀ k ≤ n, GlobalTheory.LFun.heckeVec ((RU E n).comp (locU n w).subtype) ((GlobalTheory.LFun.KGL w (n := n)).comap ((cLoc w).comp (locU n w).subtype))
        (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov E w) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab n k)) ((cLoc w).comp (locU n w).subtype x)) φ =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n S k • φ := by
  first | exact @GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec | exact GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec | (intros; apply GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearEmbSupLatticeOntoRealisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearEmbSupLatticeOntoRealisation
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.CovTop.SupImage

theorem linearIndependent_of_form {K L V : Type} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V] [Module L V]
    [IsScalarTower K L V] {S : Submodule K V} {n : ℕ} {b : Fin n → V} (hK : LinearIndependent K b)
    (hS : Submodule.span K (Set.range b) = S) (hL : LinearIndependent L b) {ι : Type} {c : ι → S}
    (hc : LinearIndependent K c) : LinearIndependent L fun k => (c k : V) := by
  subst hS
  let B := (Module.Basis.span hK).baseChange L
  let φ : L ⊗[K] Submodule.span K (Set.range b) →ₗ[L] V := (Submodule.span K (Set.range b)).subtype.liftBaseChange L
  have hB : φ ∘ B = b := by
    funext k
    simp [B, φ, Module.Basis.span_apply]
  have hφ : Function.Injective φ :=
    LinearMap.injective_of_linearIndependent (by rw [B.span_eq]) (hB ▸ hL)
  have h1 : LinearIndependent L fun k => (1 : L) ⊗ₜ[K] c k := Module.Flat.linearIndependent_one_tmul hc
  have h2 := h1.map' φ (LinearMap.ker_eq_bot.2 hφ)
  have h3 : (φ ∘ fun k => (1 : L) ⊗ₜ[K] c k) = fun k => (c k : V) := by
    funext k
    simp [φ]
  exact h3 ▸ h2


set_option maxHeartbeats 1000000 in
theorem exists_emb_image_latW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), ∃ ι : VK fw i →ₛₗ[algebraMap T.Q.c.F D.what₂.LL] (Fin (R.nW i) → D.what₂.LL), (∀ (f : VK fw i), ∃ h : (f : T.R ((i : ℕ) + 1)) ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ι f = ((fw.e i ⟨f, h⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)) ∧ (∀ (n : ℕ) (b : Fin n → VK fw i), LinearIndependent T.Q.c.F b → LinearIndependent D.what₂.LL (fun k => ι (b k))) ∧ ι '' (latW (T.U ((i : ℕ) + 1)) (wtZ (wtA (κ i)) (κ i).n) : Set (VK fw i)) = ((R.FW i).MK : Set (Fin (R.nW i) → D.what₂.LL)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ fw i
  have hE : VK fw i = T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := cuspW_wtZ _ _
  let e : VK fw i ≃ₗ[T.Q.c.F] (R.FW i).WK := (LinearEquiv.ofEq _ _ hE).trans (fw.e i)
  have he : ∀ f : VK fw i, e f = fw.e i ⟨f, hE ▸ f.2⟩ := fun _ => rfl
  let ι : VK fw i →ₛₗ[algebraMap T.Q.c.F D.what₂.LL] (Fin (R.nW i) → D.what₂.LL) :=
    { toFun := fun f => (e f : Fin (R.nW i) → D.what₂.LL)
      map_add' := fun f g => by rw [map_add (f := _)]; rfl
      map_smul' := fun a f => by rw [map_smul, algebraMap_smul]; rfl }
  have key : ∀ f : VK fw i, f ∈ latW (T.U ((i : ℕ) + 1)) (wtZ (wtA (κ i)) (κ i).n) ↔ ι f ∈ (R.FW i).MK := fun f => by
    have en := fun la y => fw.nrm_eq i la y ⟨f.1, hE ▸ f.2⟩
    constructor
    · intro hf
      refine ⟨(e f).2, fun la y => (en la y).trans_le ?_⟩
      exact (T.nrmM_le_one_iff _ la _ _).2 (hf la _ (fw.pt i la y).2)
    · rintro ⟨_, hf⟩ la v hv
      obtain ⟨y, hy⟩ := (fw.pt i la).surjective ⟨v, hv⟩
      have h2 := (en la y).symm.trans_le (hf la y)
      rw [hy] at h2
      exact (T.nrmM_le_one_iff _ la ⟨v, hv⟩ _).1 h2
  refine ⟨ι, fun f => ⟨hE ▸ f.2, rfl⟩, fun n b hb => ?_, ?_⟩
  · obtain ⟨m, c, -, h1, h2, h3, -⟩ := fw.ks i
    exact linearIndependent_of_form h1 h2 h3 (hb.map' e.toLinearMap e.ker)
  · ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (key f).1 hf
    · intro hx
      obtain ⟨f, hf⟩ := e.surjective ⟨x, hx.1⟩
      have hx' : ι f = x := congrArg Subtype.val hf
      exact ⟨f, (key f).2 (hx' ▸ hx), hx'⟩

end GlobalTheory.CovTop.SupImage

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearEmbSupLatticeOntoRealisationStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semilinear_emb_supLattice_onto_realisation : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), ∃ ι : VK fw i →ₛₗ[algebraMap T.Q.c.F D.what₂.LL] (Fin (R.nW i) → D.what₂.LL), (∀ (f : VK fw i), ∃ h : (f : T.R ((i : ℕ) + 1)) ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ι f = ((fw.e i ⟨f, h⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)) ∧ (∀ (n : ℕ) (b : Fin n → VK fw i), LinearIndependent T.Q.c.F b → LinearIndependent D.what₂.LL (fun k => ι (b k))) ∧ ι '' (latW (T.U ((i : ℕ) + 1)) (wtZ (wtA (κ i)) (κ i).n) : Set (VK fw i)) = ((R.FW i).MK : Set (Fin (R.nW i) → D.what₂.LL)) := by
  exact @GlobalTheory.CovTop.SupImage.exists_emb_image_latW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfMemBadPrimes
noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.BadLog

theorem logSum_le_log {B : Finset ℕ} {N : ℕ} (hN : N ≠ 0) (h : ∀ p ∈ B, p.Prime ∧ p ∣ N) : logSum B ≤ Real.log N := by
  have h1 : ∏ p ∈ B, p ∣ N :=
    (Finset.prod_dvd_prod_of_subset _ _ (fun p => p) fun p hp =>
      Nat.mem_primeFactors.2 ⟨(h p hp).1, (h p hp).2, hN⟩).trans (Nat.prod_primeFactors_dvd N)
  have h0 : ∀ p ∈ B, (p : ℝ) ≠ 0 := fun p hp => by exact_mod_cast (h p hp).1.ne_zero
  unfold logSum
  rw [← Real.log_prod h0, ← Nat.cast_prod]
  refine Real.log_le_log ?_ (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h1)
  exact_mod_cast Finset.prod_pos fun p hp => (h p hp).1.pos

variable {D : D7} {L : SizeData₂ D}

theorem log_level_le (P : ParameterChoice' D L) :
    LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 ≠ 0 ∧
    Real.log ((LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 : ℕ) : ℝ) ≤ (2 * |P.CYL| + 17) * zBase L := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hc0 : LevelStarExponents.condE D ≠ 0 := by
    unfold LevelStarExponents.condE
    exact mul_ne_zero (mul_ne_zero D.host.QS_pos.ne' D.host.hyp.1.ne_zero) D.host.hyp.2.1.ne_zero
  have hc1 : (1 : ℝ) ≤ LevelStarExponents.condE D := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hc0
  have hc : Real.log (LevelStarExponents.condE D) ≤ L.sc.L := by
    have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ L.t_win.1
    have a : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ L.sc.b ^ ((1 : ℝ) / 2) :=
      (le_mul_of_one_le_right (by positivity) ht).trans P.condE_le
    have b := Real.log_le_log (by positivity) a
    rw [Real.log_pow, Real.log_rpow hb, Scale.b, Real.log_exp] at b
    push_cast at b
    linarith
  obtain ⟨Y, y1, -, y3, y4⟩ := P.g_Y
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) y1
  have hg0 : ∀ i, (0 : ℝ) < D.host.g i := fun i => hY.trans_le (y4 i).1
  have l2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have l15 : Real.log 15 ≤ 14 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 15 by norm_num)]
  have hg : ∀ i, Real.log (D.host.g i) ≤ 1 + |P.CYL| * L.sc.L := fun i => by
    have a := Real.log_le_log (hg0 i) (y4 i).2
    rw [Real.log_mul two_ne_zero hY.ne'] at a
    have b : P.CYL * L.sc.L ≤ |P.CYL| * L.sc.L := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    linarith
  have hz : L.sc.L ≤ zBase L := by
    unfold zBase
    exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hf hr)
  refine ⟨mul_ne_zero (mul_ne_zero hc0 (mul_ne_zero ?_ ?_)) (by norm_num), ?_⟩
  · exact_mod_cast (hg0 0).ne'
  · exact_mod_cast (hg0 1).ne'
  have a0 := hg0 0
  have a1 := hg0 1
  push_cast
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity),
    Real.log_mul a0.ne' a1.ne']
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hz (by positivity))
  linarith [hg 0, hg 1]

theorem dvd_of_mem_badPrimes {T : Core D} (hQ : T.Q.Pins) {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ} (h : Y.Good e o)
    {p : ℕ} (hp : p ∈ badPrimes T.Q.H Y.d.l₂) : p.Prime ∧ p ∣ LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 := by
  obtain ⟨hp, h'⟩ := mem_badPrimes.1 hp
  refine ⟨hp, ?_⟩
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * 15 ^ e := by rw [← h.pd, h.lev.1.2.1, hQ.2.1.1]
  have key : ∀ a, a ∣ LevelStarExponents.condE D → a ∣ LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 := fun a ha =>
    (ha.mul_right _).mul_right _
  have cD : ∀ a : ℕ, a.Prime → (a : ℤ) ∣ NumberField.discr D.host.E → a ∣ LevelStarExponents.condE D := D.host.der.discr_primes.1
  have c2 : 2 ∣ LevelStarExponents.condE D := cD 2 Nat.prime_two D.host.der.discr_primes.2.1
  have cd : D.host.d ∣ LevelStarExponents.condE D := cD _ D.host.hyp.2.1 D.host.der.discr_primes.2.2
  rcases h' with rfl | h' | h' | h' | h'
  · exact key _ c2
  · rw [h', hQ.1.1]; exact key _ cd
  · exact key _ (cD p hp (Int.natCast_dvd.2 h'))
  · rw [hM] at h'
    rcases (Nat.Prime.dvd_mul hp).1 h' with h' | h'
    · exact (h'.mul_left _).mul_right _
    · exact (hp.dvd_of_dvd_pow h').mul_left _
  · rw [h.lev.2] at h'
    exact absurd (Nat.dvd_one.1 h') hp.ne_one

end GlobalTheory.BadLog

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeField
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRham

open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham


set_option maxHeartbeats 1000000 in
theorem IsKSValue.exists_of_isAbelianScheme (P : AbelianDeRham) {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
    {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (epsRed K) i) {g : ℕ} (hA : Semi.IsAbelianScheme A')
    (hg : SmoothOfRelativeDimension g A'.hom) {f : HdR A} (hf : f ∈ Fil A) : ∃ v, IsKSValue h f v := by
  have a₀ : Semi.IsAbelianScheme A := by
    have := hA.comm
    have hc : IsCommMonObj A := by
      open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected⟩
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  have hL := (P.2.1 K A g a₀ g₀).1
  letI : Algebra (DualNumber K) K := (TrivSqZeroExt.fstHom K K K).toRingHom.toAlgebra
  obtain ⟨-, hF⟩ := P.2.2.1 (DualNumber K) A' g hA hg K A i h
  obtain ⟨-, ⟨N, hN⟩, -⟩ := P.2.1 (DualNumber K) A' g hA hg
  obtain ⟨-, hproj, -⟩ := P.1.prim hA hg
  have su : Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom :=
    fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have rA := P.2.2.2.1 _ A' g hA hg _ (epsDP K) (isDPNilpotent_squareZero _) K _ su rfl A i h
  have rB := P.2.2.2.1.crysToDR_bijective hA hg (κ := epsDP K) (isDPNilpotent_squareZero _) su rfl h
  let φL : primDR A' →ₗ[DualNumber K] K :=
    { toFun := fun c => f ((bcMor h).pull c)
      map_add' := fun x y => by simp only [map_add (f := _)]
      map_smul' := fun r c => by
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  obtain ⟨u, hu⟩ := Module.projective_lifting_property (Algebra.linearMap (DualNumber K) K) φL
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩)
  let d' : HdR A' := u ∘ₗ N.projection (PrimitiveSubmodule A') hN.symm
  have hd' : d' ∈ Fil A' := by
    rw [Fil, Submodule.mem_dualAnnihilator]
    intro x hx
    change u (N.projection (PrimitiveSubmodule A') hN.symm x) = 0
    rw [Submodule.projection_apply_of_mem_right hN.symm hx, map_zero]
  have fd' : ∀ x, (d' x).fst = f ((bcMor h).pull x) := fun x => by
    have e1 : ∀ y, (u y).fst = f ((bcMor h).pull y) := fun y => LinearMap.congr_fun hu y
    have e2 := Submodule.projection_add_projection_eq_self hN.symm x
    have e3 : f ((bcMor h).pull ((PrimitiveSubmodule A').projection N hN.symm.symm x)) = 0 := by
      rw [Fil, hF] at hf
      exact (Submodule.mem_dualAnnihilator _).1 hf _
        (Submodule.subset_span ⟨_, Submodule.projection_apply_mem _ _, rfl⟩)
    change (u _).fst = _
    rw [e1, ← add_zero (f ((bcMor h).pull _)), ← e3, ← map_add (f := _), ← map_add (f := _), e2]
  obtain ⟨d, hd⟩ := rB.2 d'
  let k : HdR A :=
    { toFun := fun c => (d ((constMor A).pull c)).snd
      map_add' := fun x y => by simp only [map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' := fun r c => by
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul,
          TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_mul]
        simp }
  obtain ⟨v, hv, -⟩ := hL.1 k
  refine ⟨v, k, ⟨d, by rw [liftFil, Submodule.mem_comap, hd]; exact hd', fun c => ?_⟩, hv⟩
  obtain ⟨x, hx⟩ := rA.2 ((constMor A).pull c)
  have red : (bcMor h).pull x = c := by
    rw [← GrpMor.pull_pull (liftMor (epsDP K) h) (redMor A) (bcMor h) (fun _ => rfl) (by simp) x, hx,
      redMor_constMor]
  apply TrivSqZeroExt.ext
  · have e := fd' x
    rw [← hd, crysToDR_apply, hx, red] at e
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    exact e
  · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rfl

theorem ksRegular_of_isAbelianScheme : GlobalTheory.Published.AbelianDeRham → ∀ {K : Type} [Field K] {A : Over (Sp K)}
    [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {g : ℕ}, Semi.IsAbelianScheme A' →
    SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  intro P K _ A _ A' _ i h g hA hg f hf
  obtain ⟨v, hv⟩ := IsKSValue.exists_of_isAbelianScheme P h hA hg hf
  exact ⟨v, hv, fun w hw => IsKSValue.unique P hA hg hw hv⟩

end GlobalTheory.DeRham
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeFieldStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_field : GlobalTheory.Published.AbelianDeRham → ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {g : ℕ}, Semi.IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  first | exact @GlobalTheory.DeRham.ksRegular_of_isAbelianScheme | exact GlobalTheory.DeRham.ksRegular_of_isAbelianScheme | (intros; apply GlobalTheory.DeRham.ksRegular_of_isAbelianScheme <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingScalarsIntegral
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BigOn.Exp

section ScalarGeneric

variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}

theorem exists_smul_eq_sum_tmul_finBasis (x : L ⊗[O] M) : ∃ d : O, d ≠ 0 ∧
    ∃ c : _ → L, d • x = ∑ a, c a ⊗ₜ Module.finBasis (FractionRing O) M a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | add x y hx hy =>
    obtain ⟨d, hd, c, e⟩ := hx
    obtain ⟨d', hd', c', e'⟩ := hy
    refine ⟨d * d', mul_ne_zero hd hd', d' • c + d • c', ?_⟩
    rw [smul_add, mul_smul d d' y, mul_comm, mul_smul, e, e']
    simp [Finset.smul_sum, TensorProduct.add_tmul, Finset.sum_add_distrib, TensorProduct.smul_tmul']
  | tmul a f =>
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
      fun c => (Module.finBasis (FractionRing O) M).repr f c
    choose y hy using hd
    refine ⟨d, nonZeroDivisors.coe_ne_zero d, fun c => y c • a, ?_⟩
    rw [← TensorProduct.tmul_smul]
    conv_lhs => rw [← (Module.finBasis (FractionRing O) M).sum_repr f]
    rw [Finset.smul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing O) (y c), hy, smul_assoc]

variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))

theorem readExt_scalar_mem_range
    (hF : ∀ (n : ℕ) (v : Fin n → M), LinearIndependent (FractionRing O) v → LinearIndependent ℂ fun c => rd (v c))
    (x₁ x₂ : L ⊗[O] M) (κ : ℂ) (h : readExt rd eL hL x₁ = κ • readExt rd eL hL x₂) (h₂ : readExt rd eL hL x₂ ≠ 0) :
    ∃ b : L, eL b = κ := by
  set v := Module.finBasis (FractionRing O) M
  have hδ : ∀ d : O, d ≠ 0 → eL (algebraMap O L d) ≠ 0 := fun d hd => by
    rw [hL]
    exact (map_ne_zero eK).2 ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hd)
  have hsum : ∀ x : L ⊗[O] M, ∀ (d : O) (c : _ → L), d • x = ∑ a, c a ⊗ₜ v a →
      ∑ a, eL (c a) • rd (v a) = eL (algebraMap O L d) • readExt rd eL hL x := fun x d c e => by
    have := congrArg (readExt rd eL hL) e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← algebraMap_smul L d x, readExt_smul, map_sum] at this
    rw [this]
    rfl
  obtain ⟨d₁, hd₁, c₁, e₁⟩ := exists_smul_eq_sum_tmul_finBasis x₁
  obtain ⟨d₂, hd₂, c₂, e₂⟩ := exists_smul_eq_sum_tmul_finBasis x₂
  have r₁ := hsum _ _ _ e₁
  have r₂ := hsum _ _ _ e₂
  set δ₁ := eL (algebraMap O L d₁)
  set δ₂ := eL (algebraMap O L d₂)
  have h0 : ∑ a, (eL (c₁ a) - δ₁ * κ * δ₂⁻¹ * eL (c₂ a)) • rd (v a) = 0 := by
    have e3 : ∑ a, (eL (c₁ a) - δ₁ * κ * δ₂⁻¹ * eL (c₂ a)) • rd (v a) =
        ∑ a, eL (c₁ a) • rd (v a) - (δ₁ * κ * δ₂⁻¹) • ∑ a, eL (c₂ a) • rd (v a) := by
      simp only [sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, mul_smul]
    rw [e3, r₁, r₂, h, smul_smul, smul_smul, inv_mul_cancel_right₀ (hδ _ hd₂), sub_self]
  have hc := Fintype.linearIndependent_iff.1 (hF _ v v.linearIndependent) _ h0
  obtain ⟨a, ha⟩ : ∃ a, c₂ a ≠ 0 := by
    by_contra hne
    push_neg at hne
    apply h₂
    have : δ₂ • readExt rd eL hL x₂ = 0 := by rw [← r₂]; simp [hne]
    exact (smul_eq_zero.1 this).resolve_left (hδ _ hd₂)
  have hca : eL (c₂ a) ≠ 0 := (map_ne_zero eL).2 ha
  refine ⟨c₁ a * algebraMap O L d₂ / (algebraMap O L d₁ * c₂ a), ?_⟩
  have e := sub_eq_zero.1 (hc a)
  rw [map_div₀, map_mul, map_mul, e]
  have h1 : δ₁ ≠ 0 := hδ _ hd₁
  have h2 : δ₂ ≠ 0 := hδ _ hd₂
  change δ₁ * κ * δ₂⁻¹ * eL (c₂ a) * δ₂ / (δ₁ * eL (c₂ a)) = κ
  rw [div_eq_iff (mul_ne_zero h1 hca)]
  calc δ₁ * κ * δ₂⁻¹ * eL (c₂ a) * δ₂ = δ₁ * κ * eL (c₂ a) * (δ₂⁻¹ * δ₂) := by ring
    _ = κ * (δ₁ * eL (c₂ a)) := by rw [inv_mul_cancel₀ h2]; ring

end ScalarGeneric

theorem exists_algebraMap_eq_of_isIntegral {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (e : FractionRing R →+* ℂ) (b₀ : FractionRing R) (N : ℕ) (hN : IsUnit (N : R)) (m : ℕ)
    (h : IsIntegral ℤ ((N : ℂ) ^ m * e b₀)) : ∃ b : R, algebraMap R (FractionRing R) b = b₀ := by
  let f : FractionRing R →ₐ[ℤ] ℂ := { e with commutes' := fun r => by simp }
  have e1 : (N : ℂ) ^ m * e b₀ = f ((N : FractionRing R) ^ m * b₀) := by
    simp [f, map_mul, map_pow, map_natCast]
  rw [e1] at h
  have h' : IsIntegral ℤ ((N : FractionRing R) ^ m * b₀) := (isIntegral_algHom_iff f e.injective).1 h
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h'.tower_top (A := R))
  refine ⟨(↑hN.unit⁻¹ : R) ^ m * c, ?_⟩
  have hu : algebraMap R (FractionRing R) (↑hN.unit⁻¹ : R) * (N : FractionRing R) = 1 := by
    rw [← map_natCast (algebraMap R (FractionRing R)) N, ← map_mul, hN.val_inv_mul, map_one]
  rw [map_mul, map_pow, hc, ← mul_assoc, ← mul_pow, hu, one_pow, one_mul]

end GlobalTheory.BigOn.Exp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeHermitianRankAndHostDegreeEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeHermitianRankAndHostDegreeEq
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.RankHostFacts

theorem two_le_r_and_fdeg (D : D7) : 2 ≤ D.R.r ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f := by
  refine ⟨Formalism.L2.Geo.two_le_r D, ?_⟩
  unfold ReciprocityTheory.ChartRestriction.G.FD.fdeg
  rw [Formalism.L2.Pj.hostSize_finrank D]
  omega

theorem main : ∀ D : D7, 2 ≤ D.R.r ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f :=
  two_le_r_and_fdeg

end GlobalTheory.RankHostFacts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeHermitianRankAndHostDegreeEqStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_le_hermitianRank_and_hostDegree_eq : ∀ D : D7, 2 ≤ D.R.r ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f := by
  first | exact @GlobalTheory.RankHostFacts.main | exact GlobalTheory.RankHostFacts.main | (intros; apply GlobalTheory.RankHostFacts.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThFamMono
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovGmin

def Hyp (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    Prop :=
  LawsJ T ∧ 1 ≤ (T.Q.Dw j).p ∧ 1 ≤ (T.Q.Dw j).q ∧ 2 < Module.finrank ℚ D.host.E / 2 ∧ InR D j ∧ Y.Good e o ∧
    1 ≤ Lb ∧ Real.log Y.d.l₂.M ≤ 30 * Lb ∧ fieldSz D.host.E ≤ 3 * Lb ∧ Real.log (D.R.f * D.R.r) ≤ Lb ∧
    o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 ∧ Dom a n ∧ Even n ∧ 8 * D.R.f * D.R.r + 4 ≤ n ∧
    (∀ (τ : Psi T.Q.H) (k : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (k : ℕ) < (T.Q.Dw j).p →
      ((n / 2 : ℕ) : ℤ) < laOf (T.Q.Dw j) a n τ k) ∧
    Real.log (sizeK (T.Q.Dw j) a n) ≤ 20 * Lb

def badC {D : D7} {T : Core D} {j : ℕ} (Y : Deep T j) : ℕ := D.host.QS * D.host.q * D.host.d * Y.d.l₂.M

def thFam {D : D7} {T : Core D} {j : ℕ} (Y : Deep T j) (nab : NabV Y.d.Xo₂ Y.d.c₂) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (n : ℕ) (ρ : ℝ) : Set (Y.V (wtZ a n)) :=
  {y | ∃ (x0 : Fin n → LevQc (T.Q.Dw j) Y.d.l₂) (La : GenLat D.host.E n) (N : ℕ)
      (P : MvPolynomial (LtN (T.Q.Dw j) n) Y.d.c₂.F),
    Submodule.span (𝓞 D.host.E) (Set.range x0) = ⊤ ∧ La.Unimod ∧ La.TrivAt (badC Y) ∧ La.TrivAt Y.d.l₂.M ∧
      La.LevOK N Y.d.l₂.M ∧ P ∈ harmL Y.d.c₂ La a ∧ GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm Y.d.c₂ P ≤ ρ ∧
      ∀ (p : TRing Y.d.c₂.F) (y' : FrPt Y.d.Xo₂ Y.d.c₂ p.R),
        thLaValAt Y.d.Xo₂ Y.d.c₂ nab (phiHat Y.d.c₂ (indPhi Y.d.c₂ x0)) La N P y' ((y : Rul Y.d.Xo₂ Y.d.c₂) p y')}

end GlobalTheory.CovGmin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSub
set_option autoImplicit false

noncomputable section

open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD GlobalTheory.ExpFrame

namespace GlobalTheory.HighWtEmb

abbrev BVar (N : ℕ) (ι : Type) : Type := ι × (Fin N × Fin N)

abbrev OVar (N : ℕ) {ι : Type} (τ : ι) : Type := {p : BVar N ι // p.1 ≠ τ}

def blockRed (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι) :
    MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (BVar N ι) (O ⧸ Ideal.span {ϖ}) :=
  aeval fun v => X (τ, v)

def redT (O : Type) [CommRing O] (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) :
    NablaT O N mu →ₗ[O] MvPolynomial (BVar N ι) (O ⧸ Ideal.span {ϖ}) :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra O ι (MvPolynomial (BVar N ι) (O ⧸ Ideal.span {ϖ}))).compLinearMap
    fun τ => (blockRed O N ϖ τ).toLinearMap ∘ₗ (dualWeyl O N N (res N (mu τ))).subtype)

def nabK (k : Type) [CommRing k] (N : ℕ) {ι : Type} [Fintype ι] (ν : ι → Fin N → ℕ) : Submodule k (MvPolynomial (BVar N ι) k) :=
  Submodule.span k {P | ∃ f : ι → MvPolynomial (Fin N × Fin N) k, (∀ τ, f τ ∈ dualWeyl k N N (ν τ)) ∧
    P = ∏ τ, rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) (f τ)}

def toBlock (k : Type) [CommRing k] (N : ℕ) {ι : Type} [DecidableEq ι] (τ : ι) :
    MvPolynomial (BVar N ι) k →ₐ[k] MvPolynomial (Fin N × Fin N) (MvPolynomial (OVar N τ) k) :=
  aeval fun p => if h : p.1 = τ then X p.2 else C (X ⟨p, h⟩)

def blockSub (k : Type) [CommRing k] (N : ℕ) {ι : Type} (A : ι → Matrix (Fin N) (Fin N) k) :
    MvPolynomial (BVar N ι) k →ₐ[k] MvPolynomial (BVar N ι) k :=
  aeval fun p => ∑ b : Fin N, C (A p.1 p.2.1 b) * X (p.1, (b, p.2.2))

def blockW (N : ℕ) {ι : Type} [DecidableEq ι] (τ : ι) : BVar N ι → (Fin N → ℕ) :=
  fun p => if p.1 = τ then Pi.single p.2.1 1 else 0

end GlobalTheory.HighWtEmb

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogPeriodEqKroneckerCharacterLogPeriodOfHost
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogPeriodEqKroneckerCharacterLogPeriodOfHost
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.Period

theorem period_eq_kronecker : ∀ (D : D7) (L : SizeData₂ D) (Q : Par D), Q.PinHost → ∀ (Del h0 : ℕ), ∃ (_ : NeZero Q.H.d) (χ : DirichletCharacter ℂ Q.H.d), GlobalTheory.IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = (ofRecord D L Del h0).logOm ∧ (ofRecord D L Del h0).logOm = L.logOm ∧ GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField Q.H := by
  intro D L Q hp Del h0
  obtain ⟨i, χ, hχ, e⟩ := GlobalTheory.LamF.exists_kronecker_logOm_eq D Q hp L
  exact ⟨i, χ, hχ, e.trans (Formalism.L2.DIV.ofRecord_logOm D L Del h0).symm,
    Formalism.L2.DIV.ofRecord_logOm D L Del h0, GlobalTheory.FlatRow.isHostField D Q.H hp.1⟩

end GlobalTheory.CovTop.Period
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogPeriodEqKroneckerCharacterLogPeriodOfHostStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logPeriod_eq_kroneckerCharacter_logPeriod_of_host : ∀ (D : D7) (L : SizeData₂ D) (Q : Par D), Q.PinHost → ∀ (Del h0 : ℕ), ∃ (_ : NeZero Q.H.d) (χ : DirichletCharacter ℂ Q.H.d), GlobalTheory.IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = (ofRecord D L Del h0).logOm ∧ (ofRecord D L Del h0).logOm = L.logOm ∧ GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField Q.H := by
  first | exact @GlobalTheory.CovTop.Period.period_eq_kronecker | exact GlobalTheory.CovTop.Period.period_eq_kronecker | (intros; apply GlobalTheory.CovTop.Period.period_eq_kronecker <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCompNonempty
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.CovTop

theorem good_comp_nonempty : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → Nonempty (Comp Y.d.Xo₂ Y.d.c₂) := by
  intro D T hT j hj Y e o _
  exact (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Y.d.Xo₂ Y.d.c₂
    (Inhab.rank_pos T.toCore hT.pins j hj)).1

end GlobalTheory.CovTop
end
