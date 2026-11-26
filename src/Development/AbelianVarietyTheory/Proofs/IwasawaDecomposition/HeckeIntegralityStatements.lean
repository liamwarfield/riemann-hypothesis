module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnitNatCastUp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeInFamilies
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLinearLiftAdditiveHolomorphicAbelian
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeIsogenyFamilyPullbackCorrespondence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEtaleCoverListingHeckeKernelScheme
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCuspSectionsOfDominatedRationalIsometries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyGeneratorRatioLeTraceTerms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarHeckeTraceThetaGeneratorFamily
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulSumEqZeroOfPureTensorFunctionZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeTransformOfPointLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SectionValueAtMultipleOfBaseChangedGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SectionValueAtMultipleOfBaseChangedGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

noncomputable section

namespace GlobalTheory.HkValueMul

theorem fibreSectionScale_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : Formalism.L2.Pj.scal x (0 : S) i = 0 := by
  simp only [Formalism.L2.Pj.scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_zero]

theorem fibreSectionScale_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : Formalism.L2.Pj.scal x (1 : S) i = 1 := by
  simp only [Formalism.L2.Pj.scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem evR_of_secBC_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (T Ω : Type) [CommRing T] [IsReduced T] [Algebra c.F T] [Field Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (z₀ : FrPt Xo c T) (z₁ : FrPt Xo c Ω) (a₀ : T), z₁.x = spMap χ.toRingHom ≫ z₀.x → (∀ τ j, z₁.u τ j = spMap (dualMap χ.toRingHom) ≫ z₀.u τ j) → SecBC χ.toRingHom a₀ z₀.x z₁.x z₀.s z₁.s → evR Xo c f z₁ = χ (a₀ ^ n * evR Xo c f z₀) := by
  intro E _ _ _ H Dw l Xo c a n f hf T Ω _ _ _ _ _ χ z₀ z₁ a₀ hx hu hs
  have hL := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  obtain ⟨w, hw⟩ := hL.bc T Ω χ z₀
  have key : ∃ g : Ωˣ, (g : Ω) = χ a₀ ∧ FrBor (fun i => i.elim g fun _ => 1) w z₁ := by
    have hw' := hw
    obtain ⟨wx, wo, wu, wtan, weig, wbas, ws, wgen⟩ := w
    obtain ⟨zx, zo, zu, ztan, zeig, zbas, zs, zgen⟩ := z₁
    obtain ⟨hwx, hwu, pm, hp1, hp2, hp3⟩ := hw'
    dsimp only at hx hu hs hwx hwu hp1 hp2 hp3 ⊢
    subst hx
    subst hwx
    have hSw : GlobalTheory.Frames.SecBC χ.toRingHom 1 z₀.x (spMap χ.toRingHom ≫ z₀.x) z₀.s ws :=
      ⟨pm, hp1, hp2, fun i h => by rw [show Formalism.L2.Pj.scal z₀.x (1 : T) i = 1 from fibreSectionScale_one z₀.x i, _root_.one_mul]; exact hp3 i h⟩
    have hcalc := GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo T Ω Ω χ.toRingHom (RingHom.id Ω) z₀.x
      (spMap χ.toRingHom ≫ z₀.x) (spMap χ.toRingHom ≫ z₀.x) rfl (by simp [spMap])
    have hz : ∀ i, zs.f i = Formalism.L2.Pj.scal (spMap χ.toRingHom ≫ z₀.x) (χ a₀) i * ws.f i :=
      (hcalc.2.2.1 a₀ z₀.s ws zs hSw).1 hs
    have hne : χ a₀ ≠ 0 := by
      intro h0
      have hz0 : ∀ i, zs.f i = 0 := fun i => by rw [hz i, h0, show Formalism.L2.Pj.scal (spMap χ.toRingHom ≫ z₀.x) (0 : Ω) i = 0 from fibreSectionScale_zero _ i, MulZeroClass.zero_mul]
      obtain ⟨b, -, hb⟩ := zgen zs
      have e0 := hb 0 (fun i => by rw [hz0 i, MulZeroClass.mul_zero])
      have e1 := hb 1 (fun i => by rw [hz0 i, MulZeroClass.mul_zero])
      exact zero_ne_one (e0.trans e1.symm)
    have hcalc' := GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo Ω Ω Ω (RingHom.id Ω) (RingHom.id Ω)
      (spMap χ.toRingHom ≫ z₀.x) (spMap χ.toRingHom ≫ z₀.x) (spMap χ.toRingHom ≫ z₀.x)
      (by simp [spMap]) (by simp [spMap])
    refine ⟨Units.mk0 _ hne, rfl, (GlobalTheory.Frames.frBor_iff_frChg _ _ _).2
      ⟨fun τ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => by simp, rfl, fun τ i => ?_, ?_⟩⟩
    · have e : (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Ω) i = Pi.single i 1 := by
        ext j
        simp [Matrix.one_apply, Pi.single_apply, eq_comm]
      show IsCombAt _ (wu τ) ((1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Ω) i) (zu τ i)
      rw [e, (hu τ i).trans (hwu τ i).symm]
      exact Formalism.L2.PjFree.isCombAt_single (wtan τ) i
    · exact (hcalc'.2.1 _ ws zs).2 (by simpa using hz)
  obtain ⟨g, hg, hb⟩ := key
  rw [GlobalTheory.ArcQ.evR_scale_of_isReduced hL hf χ g z₀ w z₁ hw hb, hg, map_mul, map_pow]

end GlobalTheory.HkValueMul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SectionValueAtMultipleOfBaseChangedGeneratorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_value_at_multiple_of_baseChanged_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (T Ω : Type) [CommRing T] [IsReduced T] [Algebra c.F T] [Field Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (z₀ : FrPt Xo c T) (z₁ : FrPt Xo c Ω) (a₀ : T), z₁.x = spMap χ.toRingHom ≫ z₀.x → (∀ τ j, z₁.u τ j = spMap (dualMap χ.toRingHom) ≫ z₀.u τ j) → SecBC χ.toRingHom a₀ z₀.x z₁.x z₀.s z₁.s → evR Xo c f z₁ = χ (a₀ ^ n * evR Xo c f z₀) := by
  first | exact @GlobalTheory.HkValueMul.evR_of_secBC_mul | exact GlobalTheory.HkValueMul.evR_of_secBC_mul | (intros; apply GlobalTheory.HkValueMul.evR_of_secBC_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDividedHomTangentImageBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDividedHomTangentImageBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLieImg IsLinHom IsThGen IsHeckeIsog)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeLieBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem epsMul_comp_epsMul {R : Type} [CommRing R] (a b : R) :
    (epsMul a).comp (epsMul b) = epsMul (a * b) :=
  RingHom.ext fun z => by
    ext <;> simp [epsMul, mul_smul]

theorem epsMul_one' {R : Type} [CommRing R] : epsMul (1 : R) = RingHom.id _ :=
  RingHom.ext fun z => by
    ext <;> simp [epsMul]

theorem spMap_epsMul_cancel {R : Type} [CommRing R] {u : R} (hu : IsUnit u) {Z : Scheme.{0}}
    {f g : Sp (DualNumber R) ⟶ Z} (h : spMap (epsMul u) ≫ f = spMap (epsMul u) ≫ g) : f = g := by
  obtain ⟨u, rfl⟩ := hu
  have e : spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R)) = 𝟙 _ := by
    rw [GlobalTheory.Frames.ChgBC.spMap_comp_ring, epsMul_comp_epsMul, Units.inv_mul, epsMul_one',
      GlobalTheory.Frames.ChgBC.spMap_id]
  calc f = spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R)) ≫ f := by
        rw [← Category.assoc, e, Category.id_comp]
    _ = g := by rw [h, ← Category.assoc, e, Category.id_comp]

end GlobalTheory.HeckeLieBC

namespace GlobalTheory.HeckeLieBC

open GlobalTheory.HeckeFrCompare (toFib_fst toFib_snd)

theorem lieImg_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (T Ω : Type) [CommRing T] [CommRing Ω] (χ : T →+* Ω) (x x' : Sp T ⟶ Xo.X)
    (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (Ψ₁ : Gx x₁ ⟶ Gx x₁') (p : ℕ)
    (v w : Sp (DualNumber T) ⟶ Xo.univ.t.G.left) (w₁ : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left),
    IsUnit (p : Ω) → IsFib χ Ψ Ψ₁ → IsLieImg p Ψ v w → IsLieImg p Ψ₁ (spMap (dualMap χ) ≫ v) w₁ →
      w₁ = spMap (dualMap χ) ≫ w := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x' x₁ x₁' Ψ Ψ₁ p v w w₁ hp hF hL hL₁
  obtain ⟨pm, pm', hc, hc', hcomm, -⟩ := hF
  obtain ⟨-, -, a, ha, hw⟩ := hL
  obtain ⟨-, -, a₁, ha₁, hw₁⟩ := hL₁

  have hfib : GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.toFib x₁ (spMap (algebraMap Ω (DualNumber Ω))) a₁ ≫ pm =
      spMap (dualMap χ) ≫ GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.toFib x (spMap (algebraMap T (DualNumber T))) a := by
    apply GlobalTheory.Frames.ChgBC.gx_ext
    · rw [Category.assoc, hc.2.1, toFib_snd, Category.assoc, toFib_snd, ha₁, ha]
    · rw [Category.assoc, hc.2.2, GlobalTheory.HeckeFrCompare.toFib_fst_assoc, Category.assoc, toFib_fst,
        GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.dualMap_alg]
  have hpush : GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.push Ψ₁ (spMap (algebraMap Ω (DualNumber Ω))) a₁ =
      spMap (dualMap χ) ≫ GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.push Ψ (spMap (algebraMap T (DualNumber T))) a := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.push
    rw [← hc'.2.1, reassoc_of% hcomm, reassoc_of% hfib]
  apply spMap_epsMul_cancel hp
  rw [hw₁, hpush, ← hw, ← Category.assoc, ← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring,
    GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.dualMap_eps, map_natCast]

end GlobalTheory.HeckeLieBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDividedHomTangentImageBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_divided_hom_tangent_image_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T Ω : Type) [CommRing T] [CommRing Ω] (χ : T →+* Ω) (x x' : Sp T ⟶ Xo.X) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (Ψ₁ : Gx x₁ ⟶ Gx x₁') (p : ℕ) (v w : Sp (DualNumber T) ⟶ Xo.univ.t.G.left) (w₁ : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left), IsUnit (p : Ω) → IsFib χ Ψ Ψ₁ → IsLieImg p Ψ v w → IsLieImg p Ψ₁ (spMap (dualMap χ) ≫ v) w₁ → w₁ = spMap (dualMap χ) ≫ w := by
  first | exact @GlobalTheory.HeckeLieBC.lieImg_baseChange | exact GlobalTheory.HeckeLieBC.lieImg_baseChange | (intros; apply GlobalTheory.HeckeLieBC.lieImg_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalIsometryOfTraceSimilitudeSq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalIsometryOfTraceSimilitudeSq
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.TraceSimilitude

theorem trace_natSq_mul {E : Type} [Field E] [NumberField E] (N : ℕ) (x : E) :
    Algebra.trace ℚ E ((N : E) ^ 2 * x) = (N : ℚ) ^ 2 * Algebra.trace ℚ E x := by
  have h : ((N : E) ^ 2) = algebraMap ℚ E ((N : ℚ) ^ 2) := by simp
  rw [h, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem exists_gl_of_trace_similitude : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ), 0 < N → (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) → ∀ (gam : X.Λ →ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (gam u : Fin r → E) (gam v : Fin r → E)) = (N : ℚ) ^ 2 * Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (u : Fin r → E) (v : Fin r → E))) → (∀ w : X'.Λ, ∃ v, gam v = (N ^ 2) • w) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (N : E) • ((a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E)) = (gam v : Fin r → E)) ∧ (∀ w ∈ X'.Λ, (N : E) • (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) ∈ X.Λ) ∧ ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * herm X.Gm u v := by
  classical
  intro E _ _ _ r X X' N hN hn gam htr hsurj
  have hs : Submodule.span E (Set.range X.Λ.subtype) = ⊤ := by
    rw [← X.Λ_span]; congr 1; exact Subtype.range_coe
  have hs' : Submodule.span E (Set.range X'.Λ.subtype) = ⊤ := by
    rw [← X'.Λ_span]; congr 1; exact Subtype.range_coe
  obtain ⟨A, hA⟩ := FrameFibre.exists_matrix X.Λ.subtype X.Λ.injective_subtype hs
    (X'.Λ.subtype ∘ₗ gam)
  have hA' : ∀ v : X.Λ, A *ᵥ (v : Fin r → E) = (gam v : Fin r → E) := hA
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hcoe : ∀ w : X'.Λ, (((N ^ 2) • w : X'.Λ) : Fin r → E) = ((N : E) ^ 2) • (w : Fin r → E) := by
    intro w
    rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul E]
    push_cast; rfl
  have hsurjA : Function.Surjective (Matrix.toLin' A) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs', Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := hsurj w
    refine ⟨((N : E) ^ 2)⁻¹ • (v : Fin r → E), ?_⟩
    rw [map_smul, Matrix.toLin'_apply, hA', hv, hcoe, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hN0), one_smul]
    rfl
  have hU : IsUnit A := Matrix.mulVec_surjective_iff_isUnit.1 hsurjA
  set U := hU.unit with hUdef
  have hUA : (U : Matrix (Fin r) (Fin r) E) = A := hU.unit_spec
  let a : GL (Fin r) E :=
    ⟨(N : E)⁻¹ • A, (N : E) • ((U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E),
      by rw [smul_mul_smul_comm, inv_mul_cancel₀ hN0, one_smul, ← hUA, U.mul_inv],
      by rw [smul_mul_smul_comm, mul_inv_cancel₀ hN0, one_smul, ← hUA, U.inv_mul]⟩
  have ha : (a : Matrix (Fin r) (Fin r) E) = (N : E)⁻¹ • A := rfl
  have hai : ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) =
      (N : E) • ((U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := rfl
  obtain ⟨ε, hε, hξ⟩ : ∃ ε : E, (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 := by
    rcases TraceIsometry.eq_or_eq_neg_of_norm_eq X.ξ0_im X'.ξ0_im hn with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, _root_.one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_mul]⟩
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
  have h1 : cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
  have key : ∀ u v : X.Λ, herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) =
      (N : E) ^ 2 * ε * herm X.Gm u v := by
    intro u v
    have h0 : -X'.ξ0 * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) -
        (N : E) ^ 2 * (-X.ξ0 * herm X.Gm u v) = 0 := by
      refine FrameFibre.eq_zero_of_trace _ fun b => ?_
      have h2 := htr (b • u) v
      have h3 : ((b • u : X.Λ) : Fin r → E) = (b : E) • (u : Fin r → E) := rfl
      have h4 := FrameFibre.herm_smul_smul X'.Gm (b : E) 1 (A *ᵥ (u : Fin r → E))
        (A *ᵥ (v : Fin r → E))
      have h5 := FrameFibre.herm_smul_smul X.Gm (b : E) 1 (u : Fin r → E) (v : Fin r → E)
      rw [one_smul, h1, _root_.mul_one] at h4 h5
      rw [← hA', ← hA', h3, Matrix.mulVec_smul, h4, h5] at h2
      have e1 : (b : E) * (-X'.ξ0 * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E))) =
          -X'.ξ0 * ((b : E) * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E))) := by ring
      have e2 : (b : E) * ((N : E) ^ 2 * (-X.ξ0 * herm X.Gm u v)) =
          (N : E) ^ 2 * (-X.ξ0 * ((b : E) * herm X.Gm u v)) := by ring
      rw [mul_sub, map_sub, e1, e2, trace_natSq_mul, h2, sub_self]
    rw [hξ] at h0
    apply mul_left_cancel₀ X.ξ0_ne
    linear_combination (-ε) * h0 -
      (X.ξ0 * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E))) * hε2
  have keyA : ∀ x y : Fin r → E, herm X'.Gm (A *ᵥ x) (A *ᵥ y) = (N : E) ^ 2 * ε * herm X.Gm x y := by
    intro x y
    obtain ⟨c, v, hc, hv⟩ := FrameFibre.exists_smul_eq X.Λ.subtype hs x
    obtain ⟨d, w, hd, hw⟩ := FrameFibre.exists_smul_eq X.Λ.subtype hs y
    have h2 := key v w
    rw [Submodule.subtype_apply] at hv hw
    rw [← hv, ← hw, Matrix.mulVec_smul, Matrix.mulVec_smul, FrameFibre.herm_smul_smul,
      FrameFibre.herm_smul_smul] at h2
    have hc' : (c : E) ≠ 0 := by simpa using hc
    have hd' : cc (d : E) ≠ 0 := (map_ne_zero (IsCMField.complexConj E)).2 (by simpa using hd)
    apply mul_left_cancel₀ (mul_ne_zero hc' hd')
    linear_combination h2
  refine ⟨a, ε, hε, hξ, fun v => ?_, fun w hw => ?_, fun x y => ?_⟩
  · rw [ha, Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hN0, one_smul, hA']
  · obtain ⟨v, hv⟩ := hsurj ⟨w, hw⟩
    have h3 : (U : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) = (N : E) ^ 2 • w := by
      rw [hUA, hA', hv, hcoe]
    have h2 : ((U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((N : E) ^ 2 • w) = v := by
      rw [← h3, Matrix.mulVec_mulVec, U.inv_mul, Matrix.one_mulVec]
    rw [hai, Matrix.smul_mulVec, smul_smul, ← pow_two, ← Matrix.mulVec_smul, h2]
    exact v.2
  · have hcc : cc ((N : E)⁻¹) = (N : E)⁻¹ :=
      (map_inv₀ (IsCMField.complexConj E) _).trans (by rw [map_natCast])
    rw [ha, Matrix.smul_mulVec, Matrix.smul_mulVec, FrameFibre.herm_smul_smul, hcc,
      keyA]
    field_simp

end GlobalTheory.TraceSimilitude
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalIsometryOfTraceSimilitudeSqStatement
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_isometry_of_trace_similitude_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ), 0 < N → (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) → ∀ (gam : X.Λ →ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (gam u : Fin r → E) (gam v : Fin r → E)) = (N : ℚ) ^ 2 * Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (u : Fin r → E) (v : Fin r → E))) → (∀ w : X'.Λ, ∃ v, gam v = (N ^ 2) • w) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (N : E) • ((a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E)) = (gam v : Fin r → E)) ∧ (∀ w ∈ X'.Λ, (N : E) • (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) ∈ X.Λ) ∧ ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * herm X.Gm u v := by
  first | exact @GlobalTheory.TraceSimilitude.exists_gl_of_trace_similitude | exact GlobalTheory.TraceSimilitude.exists_gl_of_trace_similitude | (intros; apply GlobalTheory.TraceSimilitude.exists_gl_of_trace_similitude <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLineGeneratorZariskiLocally
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLineGeneratorZariskiLocally
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

theorem exists_secGen_away : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : Type) [CommRing T] [Algebra c.F T] (x : Sp T ⟶ Xo.X), x ≫ Xo.s = sOf c T → ∀ q : PrimeSpectrum T, ∃ g : T, g ∉ q.asIdeal ∧ ∃ s : LB.Sec (PPx (spMap (algebraMap T (Localization.Away g)) ≫ x)), SecGen _ s := by
  intro E _ _ _ H Dw l Xo c T _ _ x hx q
  have hS := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨xF, h1, h2⟩ : ∃ xF : Sp T ⟶ Xo.XF c, xF ≫ pullback.fst _ _ = x ∧
      xF ≫ pullback.snd _ _ = spMap (algebraMap c.F T) := by
    refine ⟨pullback.lift x (spMap (algebraMap c.F T)) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [hx]
    simp only [sOf, spMap, ← Spec.map_comp]
    rfl
  obtain ⟨p, j, y₀, hj, hp⟩ := GlobalTheory.Frames.exists_openChart_testRing hS E H Dw l Xo c (xF q)
  obtain ⟨g, hg, hT⟩ := openChart_factor_near_prime E H Dw l Xo c p.R j y₀ hj T xF h2 q hp
  refine ⟨g, hg, ?_⟩
  let lam : T →ₐ[c.F] Localization.Away g := IsScalarTower.toAlgHom c.F T (Localization.Away g)
  obtain ⟨ψ, hψ⟩ := hT (Localization.Away g) lam (IsLocalization.Away.algebraMap_isUnit g)
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c p.R _ ψ y₀
  have hzx : z.x = spMap (algebraMap T (Localization.Away g)) ≫ x := by
    rw [hz.1, ← hj.2.1, ← Category.assoc, ← hψ, Category.assoc, h1]
    rfl
  have key : ∀ x' : Sp (Localization.Away g) ⟶ Xo.X, z.x = x' → ∃ s : LB.Sec (PPx x'), SecGen x' s := by
    rintro _ rfl
    exact ⟨z.s, z.gen⟩
  exact key _ hzx

end GlobalTheory.HeckeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLineGeneratorZariskiLocallyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaLine_generator_zariski_locally : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : Type) [CommRing T] [Algebra c.F T] (x : Sp T ⟶ Xo.X), x ≫ Xo.s = sOf c T → ∀ q : PrimeSpectrum T, ∃ g : T, g ∉ q.asIdeal ∧ ∃ s : LB.Sec (PPx (spMap (algebraMap T (Localization.Away g)) ≫ x)), SecGen _ s := by
  first | exact @GlobalTheory.HeckeEx.exists_secGen_away | exact GlobalTheory.HeckeEx.exists_secGen_away | (intros; apply GlobalTheory.HeckeEx.exists_secGen_away <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTraceEqFinsumGeometricPointsEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgHomEqEval
namespace GlobalTheory.AlgHomEqEval

theorem algHom_eq_eval : ∀ {K : Type} [inst : Field K] {P : Type} [Fintype P] [DecidableEq P]
    (θ : (P → K) →ₐ[K] K), ∃ (p : P), ∀ (z : P → K), (θ : (P → K) → K) z = z p := by
  intro K _ P _ _ θ
  have hsum : ∑ p, (Pi.single p (1:K) : P → K) = 1 := by
    ext x; simp [Finset.sum_apply, Pi.single_apply]
  have h1 : ∑ p, θ (Pi.single p 1) = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hsum, map_one]
  obtain ⟨p, -, hp⟩ : ∃ p ∈ Finset.univ, θ (Pi.single p 1) ≠ 0 := by
    by_contra h
    push_neg at h
    rw [Finset.sum_eq_zero h] at h1
    exact zero_ne_one h1
  refine ⟨p, fun z => ?_⟩
  have hz : z * Pi.single p 1 = (algebraMap K (P → K) (z p)) * Pi.single p 1 := by
    ext x
    by_cases hx : x = p
    · subst hx; simp
    · simp [Pi.single_apply, hx]
  have h2 := congrArg θ hz
  rw [map_mul, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at h2
  exact mul_right_cancel₀ hp h2

end GlobalTheory.AlgHomEqEval
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTraceEqFinsumGeometricPointsEtale
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

noncomputable section

namespace GlobalTheory.EtaleTraceGeom

open TensorProduct

theorem exists_eq_eval {K : Type} [Field K] {P : Type} [Fintype P] [DecidableEq P]
    (θ : (P → K) →ₐ[K] K) : ∃ p : P, ∀ z : P → K, θ z = z p := by
  first
  | exact @_root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval
  | exact _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval
  | (apply _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval ..)

theorem trace_pi_self {K : Type} [Field K] {P : Type} [Fintype P] [DecidableEq P] (z : P → K) :
    Algebra.trace K (P → K) z = ∑ p, z p := by
  let b := Pi.basisFun K P
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul, b, Pi.single_apply]

theorem exists_trace_eq_finsum : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B], Module.Finite R B →
    Algebra.Etale R B → ∀ b : B, ∃ v : R, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω),
      φ v = ∑ᶠ χ : {χ : B →+* Ω // χ.comp (algebraMap R B) = φ}, χ.1 b := by
  intro R B _ _ _ hfin het b
  classical
  have : Module.FinitePresentation R B := .of_finite_of_finitePresentation R B
  have : Module.Flat R B := inferInstance
  have : Module.Projective R B := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R B
  refine ⟨LinearMap.trace R _ (g ∘ₗ Algebra.lmul R B b ∘ₗ f), fun Ω _ _ φ => ?_⟩
  letI := φ.toAlgebra
  have hφ : algebraMap R Ω = φ := rfl

  have step1 : φ (LinearMap.trace R _ (g ∘ₗ Algebra.lmul R B b ∘ₗ f)) =
      Algebra.trace Ω (Ω ⊗[R] B) (1 ⊗ₜ b) := by
    rw [← hφ, ← LinearMap.trace_baseChange, LinearMap.baseChange_comp, LinearMap.baseChange_comp,
      LinearMap.trace_comp_comm', LinearMap.comp_assoc, ← LinearMap.baseChange_comp, hfg,
      LinearMap.baseChange_id, LinearMap.comp_id, Algebra.trace_apply, Algebra.baseChange_lmul]
  rw [step1]
  set e := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω (Ω ⊗[R] B) with he
  haveI : Module.Finite Ω (PrimeSpectrum (Ω ⊗[R] B) → Ω) := Module.Finite.equiv e.toLinearEquiv
  haveI : IsArtinianRing (Ω ⊗[R] B) := isArtinian_of_tower Ω inferInstance
  haveI : Finite (PrimeSpectrum (Ω ⊗[R] B)) := inferInstance
  haveI : Fintype (PrimeSpectrum (Ω ⊗[R] B)) := Fintype.ofFinite _
  rw [← Algebra.trace_eq_of_algEquiv e, trace_pi_self]
  let S := {χ : B →+* Ω // χ.comp (algebraMap R B) = φ}
  let G : PrimeSpectrum (Ω ⊗[R] B) → (B →ₐ[R] Ω) := fun p =>
    (((Pi.evalAlgHom Ω (fun _ => Ω) p).comp (e : Ω ⊗[R] B →ₐ[Ω] _)).restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  let F : PrimeSpectrum (Ω ⊗[R] B) → S := fun p =>
    ⟨(G p).toRingHom, RingHom.ext fun r => (G p).commutes r⟩
  have hF : ∀ p y, (F p).1 y = e (1 ⊗ₜ y) p := fun p y => rfl
  have hinj : Function.Injective F := by
    intro p q h
    have h' : ∀ y : B, e (1 ⊗ₜ y) p = e (1 ⊗ₜ y) q := fun y => by
      rw [← hF, ← hF, h]
    have h'' : ∀ x, e x p = e x q := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a y =>
        rw [show a ⊗ₜ[R] y = a • (1 ⊗ₜ[R] y : Ω ⊗[R] B) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one], map_smul, Pi.smul_apply,
          Pi.smul_apply, h' y]
      | add x y hx hy => rw [map_add (f := _), Pi.add_apply, Pi.add_apply, hx, hy]
    have := h'' (e.symm (Pi.single p 1))
    rw [e.apply_symm_apply, Pi.single_eq_same] at this
    by_contra hne
    rw [Pi.single_eq_of_ne (Ne.symm hne)] at this
    exact one_ne_zero this
  have hsurj : Function.Surjective F := by
    rintro ⟨χ, hχ⟩
    let χ' : B →ₐ[R] Ω := { χ with commutes' := fun r => RingHom.congr_fun hχ r }
    let ψ : Ω ⊗[R] B →ₐ[Ω] Ω := AlgHom.liftEquiv R Ω B Ω χ'
    obtain ⟨p, hp⟩ := exists_eq_eval (ψ.comp e.symm.toAlgHom)
    refine ⟨p, Subtype.ext (RingHom.ext fun y => ?_)⟩
    rw [hF, ← hp (e (1 ⊗ₜ y))]
    simp [ψ, χ']
  rw [← finsum_comp_equiv (Equiv.ofBijective F ⟨hinj, hsurj⟩), finsum_eq_sum_of_fintype]
  rfl

end GlobalTheory.EtaleTraceGeom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTraceEqFinsumGeometricPointsEtaleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trace_eq_finsum_geometric_points_etale : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B], Module.Finite R B → Algebra.Etale R B → ∀ b : B, ∃ v : R, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω), φ v = ∑ᶠ χ : {χ : B →+* Ω // χ.comp (algebraMap R B) = φ}, χ.1 b := by
  first | exact @GlobalTheory.EtaleTraceGeom.exists_trace_eq_finsum | exact GlobalTheory.EtaleTraceGeom.exists_trace_eq_finsum | (intros; apply GlobalTheory.EtaleTraceGeom.exists_trace_eq_finsum <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

section Sec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
open GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection (TotalAt FunAt)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {P : Ideal (𝓞 E)} {p i : ℕ}

abbrev term (P : Ideal (𝓞 E)) (p i : ℕ) (f : Rul Xo c) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
    (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) P p i Ω y) : Ω :=
  hkTerm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)
    (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y C

theorem bc_exists {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) : ∃ z, FrMap φ y z :=
  GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c S T φ y

theorem bc_unique {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrMap φ y z) (h' : FrMap φ y z') : z = z' :=
  (frMap_unique_refl_iff E H Dw l Xo c S T φ y).1 z z' h h'

theorem isHeckeIsog_unique (hA : admitted l P p) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x x₁ x₂ : Sp Ω ⟶ Xo.X}
    {C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)} {ψ₁ : Gx x ⟶ Gx x₁} {ψ₂ : Gx x ⟶ Gx x₂}
    (hC : Xo.univ.t.HeckeKer (Over.mk x) Dw P p i C) (h₁ : IsHeckeIsog p C ψ₁) (h₂ : IsHeckeIsog p C ψ₂) :
    x₁ = x₂ ∧ HEq ψ₁ ψ₂ := by
  have hc : p.Coprime l.M' := (Nat.Prime.coprime_iff_not_dvd hA.2.2.1).2 hA.2.2.2.2
  obtain ⟨ψ₁, rfl⟩ := (GlobalTheory.HeckeFrCompare.conj x x₁).surjective ψ₁
  obtain ⟨ψ₂, rfl⟩ := (GlobalTheory.HeckeFrCompare.conj x x₂).surjective ψ₂
  obtain ⟨f₁, k₁⟩ := (GlobalTheory.HeckeFrCompare.isog_iff hc _ _ _ _).2 h₁
  obtain ⟨f₂, k₂⟩ := (GlobalTheory.HeckeFrCompare.isog_iff hc _ _ _ _).2 h₂
  obtain ⟨-, a, b⟩ := GlobalTheory.HeckePointLaw.isHkIsog_etale_unique Xo hA.1 hA.2.1 hA.2.2.1 hA.2.2.2.1 hA.2.2.2.2 hC k₂
  obtain rfl := a _ _ _ k₁
  obtain rfl := b _ _ k₁
  exact ⟨rfl, HEq.rfl⟩

theorem exists_card_heckeKer_le (hA : admitted l P p) : ∃ M : ℕ, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ Xo.X),
    Nat.card {C : Subgroup (Over.mk x ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk x) Dw P p i C} ≤ M := by
  have hp := hA.2.2.1.pos
  refine ⟨2 ^ (p ^ 2) ^ (2 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))), fun Ω _ _ x => ?_⟩
  have h₀ : Nat.card (Xo.univ.t.tors (Over.mk x) (Ideal.span {((p ^ 2 : ℕ) : 𝓞 E)})) = _ :=
    (HeckeKerModel.heckeKer_zero Xo.univ Ω x _ (Spec.map_preimage (x ≫ Xo.s)).symm P (p ^ 2)
      (pow_pos hp 2)).2.2.2.2.1
  have hf : Finite (Xo.univ.t.tors (Over.mk x) (Ideal.span {((p ^ 2 : ℕ) : 𝓞 E)})) :=
    Nat.finite_of_card_ne_zero (h₀.trans_ne (pow_ne_zero _ (pow_pos hp 2).ne'))
  have hs : ∀ C : {C : Subgroup (Over.mk x ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk x) Dw P p i C}, ∀ z ∈ C.1,
      z ∈ Xo.univ.t.tors (Over.mk x) (Ideal.span {((p ^ 2 : ℕ) : 𝓞 E)}) := fun C z hz a ha => by
    refine C.2.2.2.1 hz a ((Ideal.span_singleton_le_iff_mem _).2 ?_ ha)
    rw [Nat.cast_pow, pow_two]
    refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hA.2.2.2.1
    rwa [map_natCast] at this
  refine (Nat.card_le_card_of_injective
    (β := Xo.univ.t.tors (Over.mk x) (Ideal.span {((p ^ 2 : ℕ) : 𝓞 E)}) → Prop) (fun C z => z.1 ∈ C.1)
    fun C C' e => Subtype.ext (Subgroup.ext fun z => ⟨fun h => ?_, fun h => ?_⟩)).trans_eq ?_
  · exact (congrFun e ⟨z, hs C z h⟩).mp h
  · exact (congrFun e ⟨z, hs C' z h⟩).mpr h
  · rw [Nat.card_fun, h₀, Nat.card_eq_fintype_card, Fintype.card_prop]

theorem hkPt_along (hA : admitted l P p) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
    {y z : FrPt Xo c Ω} {x' : Sp Ω ⟶ Xo.X} {Ψ : Gx y.x ⟶ Gx x'} {C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G)}
    (hC : Xo.univ.t.HeckeKer (Over.mk y.x) Dw P p i C) (hΨ : IsHeckeIsog p C Ψ) (hz : HkPt p (hkTr Xo c p Ω) y C z) :
    ∃ h : z.x = x', (∀ τ j, IsLieImg p Ψ (y.u τ j) (z.u τ j)) ∧
      IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ p y.s (h ▸ z.s) := by
  obtain ⟨ψ, h₁, h₂, h₃⟩ := (GlobalTheory.HeckeFrCompare.hkPt_iff hA _ y C z).1 hz
  obtain ⟨rfl, e⟩ := isHeckeIsog_unique hA hC h₁ hΨ
  obtain rfl := eq_of_heq e
  rw [hkTr, Equiv.apply_symm_apply] at h₃
  exact ⟨rfl, h₂, h₃⟩

theorem exists_term_of_family (hA : admitted l P p) (hT : TotalAt Xo c P p i)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {T : Type} [CommRing T] [IsReduced T]
    [Algebra c.F T] (y : FrPt Xo c T) {x' : Sp T ⟶ Xo.X} (hx' : x' ≫ Xo.s = sOf c T) {Ψ : Gx y.x ⟶ Gx x'}
    (hΨ : IsHeckeFam P p i Ψ) {m : ℕ} {σ : Fin m → (Over.mk y.x ⟶ Xo.univ.t.G)} (hσ : IsListed Ψ σ)
    {s₀ : LB.Sec (PPx x')} (hs₀ : SecGen x' s₀) :
    ∃ b : T, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω)
      (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁') (C : hkKer (Xo := Xo) P p i Ω y₁), FrMap χ y y₁ →
      IsFib χ.toRingHom Ψ Ψ₁ → C.1 = transKer Xo.univ.t.G Ψ₁ → χ b = term P p i f y₁ C := by
  have hp : p ≠ 0 := hA.2.2.1.ne_zero
  obtain ⟨u, hu, he, hb⟩ := GlobalTheory.T.etale_linear_hom_framed_point_eigenbases E H Dw l Xo c T y x' Ψ p hp hΨ.1 hΨ.2.1
  let z₀ : FrPt Xo c T := ⟨x', hx', u, fun τ j => (hu τ j).2.1, he, hb, s₀, hs₀⟩
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.T.exists_scalar_heckeTrace_thetaGenerator_family E H Dw l Xo c P p i m T y x' Ψ σ s₀ hA hΨ hσ hs₀ (fun Ω _ _ _ χ y₁ x₁' Ψ₁ _ hF => by
    obtain ⟨hC, hI⟩ := hΨ.2.2.2.2 Ω _ _ _ Ψ₁ hF
    obtain ⟨z, hz⟩ := hT Ω y₁ ⟨_, hC⟩
    obtain ⟨rfl, -, h⟩ := hkPt_along hA hC hI hz
    exact ⟨z.s, z.gen, h⟩)
  refine ⟨a₀ ^ n * evR Xo c f z₀, fun Ω _ _ _ χ y₁ x₁' Ψ₁ C hy hF hC => ?_⟩
  obtain ⟨-, hI⟩ := hΨ.2.2.2.2 Ω _ _ _ Ψ₁ hF
  have hex := hT Ω y₁ C
  rw [term, hkTerm, dif_pos hex]
  have hz := hex.choose_spec
  generalize hex.choose = z at hz ⊢
  obtain ⟨rfl, h₁, h₂⟩ := hkPt_along hA C.2 (hC ▸ hI) hz
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap c.F Ω).injective
  exact (GlobalTheory.T.section_value_at_multiple_of_baseChanged_generator E H Dw l Xo c a n f hf T Ω χ z₀ z a₀ (by
    obtain ⟨_, _, _, h, _⟩ := hF
    exact h.1) (fun τ j => by
    refine GlobalTheory.T.lie_divided_hom_tangent_image_baseChange E H Dw l Xo T Ω _ _ _ _ _ Ψ Ψ₁ p _ _ _ (Nat.cast_ne_zero.2 hp).isUnit hF (hu τ j) ?_
    rw [← hy.2.1]
    exact h₁ τ j)
    (ha₀ Ω χ y₁ z.x Ψ₁ z.s hy hF z.gen h₂)).symm

theorem exists_term (hA : admitted l P p) (hT : TotalAt Xo c P p i) (Z : Corr Xo P p i)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {B : Type} [CommRing B] [IsReduced B]
    [Algebra c.F B] (y : FrPt Xo c B) (h : Sp B ⟶ Z.Hk) (hh : h ≫ Z.π₁ = y.x) :
    ∃ b : B, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : B →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω)
      (C : hkKer (Xo := Xo) P p i Ω y₁), FrMap χ y y₁ → Z.toKerScheme.Carries (spMap χ.toRingHom ≫ h) y₁.x C.1 →
      χ b = term P p i f y₁ C := by
  choose bc hbc using fun (Ω : Type) [Field Ω] [Algebra c.F Ω] (χ : B →ₐ[c.F] Ω) => bc_exists χ y
  choose e he using GlobalTheory.T.exists_equiv_heckeKernelScheme_points_heckeKernels E H Dw l Xo P p i Z.toKerScheme hA
  have hw : ∀ (Ω : Type) [Field Ω] [Algebra c.F Ω] (χ : B →ₐ[c.F] Ω),
      (spMap χ.toRingHom ≫ h) ≫ Z.π₁ = (bc Ω χ).x := fun Ω _ _ χ => by
    rw [Category.assoc, hh, (hbc Ω χ).1]
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_function_of_smooth_local_descent_reduced c.F B (fun Ω _ _ _ χ => term P p i f (bc Ω χ) (e Ω _ ⟨_, hw Ω χ⟩)) (fun q => by
    obtain ⟨T', _, _, m, σ, hT', hs, hσ, hl⟩ := GlobalTheory.T.exists_etale_cover_listing_heckeKernelScheme E H Dw l Xo P p i Z.toKerScheme hA B h
    obtain ⟨q', rfl⟩ := hs q
    letI : Algebra c.F T' := ((algebraMap B T').comp (algebraMap c.F B)).toAlgebra
    haveI : IsScalarTower c.F B T' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hso : ∀ (T : Type) [CommRing T] [Algebra c.F T] [Algebra B T] [IsScalarTower c.F B T],
        (spMap (algebraMap B T) ≫ h ≫ Z.π₂) ≫ Xo.s = sOf c T := fun T _ _ _ _ => by
      rw [Category.assoc, Category.assoc, Z.base₂, reassoc_of% hh, y.x_over, sOf, sOf, ChgBC.spMap_comp_ring,
        ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
    obtain ⟨g, hg, s₀, hs₀⟩ := GlobalTheory.T.exists_thetaLine_generator_zariski_locally E H Dw l Xo c T' _ (hso T') q'
    let T := Localization.Away g
    have hsm : Algebra.Smooth B T := by
      have : Algebra.Smooth T' T := Algebra.Smooth.of_isLocalization_Away g
      exact Algebra.Smooth.comp B T' T
    have hred : IsReduced T := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced B T
    have e₁ : spMap (algebraMap T' T) ≫ spMap (algebraMap B T') = spMap (algebraMap B T) := by
      rw [ChgBC.spMap_comp_ring, ← IsScalarTower.algebraMap_eq]
    obtain ⟨yT, hyT⟩ := bc_exists (IsScalarTower.toAlgHom c.F B T) y
    have hx : yT.x = (spMap (algebraMap B T) ≫ h) ≫ Z.π₁ := by rw [Category.assoc, hh]; exact hyT.1
    obtain ⟨Ψ, hΨ, hc⟩ := GlobalTheory.T.exists_heckeIsogenyFamily_pullback_correspondence E H Dw l Xo P p i Z hA T (spMap (algebraMap B T) ≫ h) yT.x
      (spMap (algebraMap T' T) ≫ spMap (algebraMap B T') ≫ h ≫ Z.π₂) hx (by rw [reassoc_of% e₁, Category.assoc])
    obtain ⟨b', hb'⟩ := exists_term_of_family hA hT hf yT (by rw [reassoc_of% e₁]; exact hso T) hΨ
      (σ := fun j => Over.homMk (spMap (algebraMap T' T) ≫ σ j) (by
        show _ = yT.x
        rw [Category.assoc, hσ, reassoc_of% e₁, hx, Category.assoc]))
      (fun Ω _ _ χ x₁ x₁' Ψ₁ hF => by
        obtain ⟨k, hk⟩ := hl Ω (χ.comp (algebraMap T' T)) x₁ (transKer _ Ψ₁) (by
          rw [← ChgBC.spMap_comp_ring, Category.assoc, reassoc_of% e₁]
          exact hc Ω χ _ _ Ψ₁ hF)
        exact ⟨k, fun j => by rw [hk, ← ChgBC.spMap_comp_ring, Category.assoc]; rfl⟩) hs₀
    refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, b', hsm, ?_, fun Ω _ _ _ χ => ?_⟩
    · obtain ⟨q'', rfl⟩ : q' ∈ Set.range (PrimeSpectrum.comap (algebraMap T' T)) := by
        rw [PrimeSpectrum.localization_away_comap_range T g]
        exact hg
      exact ⟨q'', by rw [IsScalarTower.algebraMap_eq B T' T]; rfl⟩
    · have hm : FrMap χ yT (bc Ω (χ.comp (IsScalarTower.toAlgHom c.F B T))) := by
        obtain ⟨w, hw⟩ := bc_exists χ yT
        rwa [bc_unique (hbc Ω _) (frMap_trans (Xo := Xo) (c := c) _ _ _ _ χ y yT w hyT hw)]
      obtain ⟨Ψ₁, hF⟩ := exists_isFib χ.toRingHom hm.1 rfl Ψ hΨ.1.1
      refine hb' Ω χ _ _ Ψ₁ _ hm hF ((he Ω _ ⟨_, hw Ω _⟩ _).1 ?_).symm
      have := hc Ω _ _ _ Ψ₁ hF
      rwa [← Category.assoc, ChgBC.spMap_comp_ring] at this)
  refine ⟨b, fun Ω _ _ _ χ y₁ C hy hC => ?_⟩
  obtain rfl := bc_unique hy (hbc Ω χ)
  rw [hb, show C = e Ω _ ⟨_, hw Ω χ⟩ from Subtype.ext ((he Ω _ ⟨_, hw Ω χ⟩ _).1 hC)]

theorem exists_sum (hr : 1 ≤ Dw.p + Dw.q) (hA : admitted l P p) (hT : TotalAt Xo c P p i)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {R : Type} [CommRing R] [IsReduced R]
    [Algebra c.F R] (y : FrPt Xo c R) :
    ∃ v : R, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (φ : R →ₐ[c.F] Ω) (z : FrPt Xo c Ω),
      FrMap φ y z → φ v = ∑ᶠ C, term P p i f z C := by
  obtain ⟨⟨Z, -⟩, -⟩ := heckeInFamilies E H Dw l Xo P p i hr hA
  obtain ⟨B, _, _, h, hfin, het, hh, -, hu⟩ := GlobalTheory.T.exists_finiteEtale_algebra_pullback_affine _ _ Z.π₁ Z.fin₁ Z.et₁ R y.x
  letI : Algebra c.F B := ((algebraMap R B).comp (algebraMap c.F R)).toAlgebra
  haveI : IsScalarTower c.F R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hred : IsReduced B := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced R B
  obtain ⟨yB, hyB⟩ := bc_exists (IsScalarTower.toAlgHom c.F R B) y
  obtain ⟨b, hb⟩ := exists_term hA hT Z hf yB h (hh.trans hyB.1.symm)
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_trace_eq_finsum_geometric_points_etale R B hfin het b
  refine ⟨v, fun Ω _ _ _ φ z hz => ?_⟩
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_heckeKernelScheme_points_heckeKernels E H Dw l Xo P p i Z.toKerScheme hA Ω z.x
  let k : {χ : B →+* Ω // χ.comp (algebraMap R B) = φ.toRingHom} → {w : Sp Ω ⟶ Z.Hk // w ≫ Z.π₁ = z.x} := fun χ =>
    ⟨spMap χ.1 ≫ h, by rw [Category.assoc, hh, ← Category.assoc, ChgBC.spMap_comp_ring, χ.2, hz.1]⟩
  have hk : Function.Bijective k := by
    rw [Function.bijective_iff_existsUnique]
    intro w
    obtain ⟨χ, ⟨h₁, h₂⟩, h₃⟩ := hu Ω φ.toRingHom w.1 (w.2.trans hz.1)
    exact ⟨⟨χ, h₁⟩, Subtype.ext h₂, fun χ' h' => Subtype.ext (h₃ _ ⟨χ'.2, congrArg Subtype.val h'⟩)⟩
  refine (hv Ω φ.toRingHom).trans (finsum_eq_of_bijective (e ∘ k) (e.bijective.comp hk) fun χ => ?_)
  let χ' : B →ₐ[c.F] Ω := { χ.1 with commutes' := fun r => (RingHom.congr_fun χ.2 _).trans (φ.commutes r) }
  have hm : FrMap χ' yB z := by
    obtain ⟨w, hw⟩ := bc_exists χ' yB
    have := frMap_trans (Xo := Xo) (c := c) _ _ _ _ χ' y yB w hyB hw
    rw [show χ'.comp (IsScalarTower.toAlgHom c.F R B) = φ from AlgHom.ext (RingHom.congr_fun χ.2)] at this
    rwa [bc_unique hz this]
  exact hb Ω χ' z _ hm ((he (k χ) _).2 rfl)

theorem secTransform (hL : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws) : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.SecTransform := by
  intro E _ _ _ H Dw l Xo c P p i cq a n hr hs _ _ f hf
  have hA : admitted l P p := ⟨hs.max, hs.split, hs.prime, hs.under, hs.off⟩
  have hP := GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 hA
  have hT := hL.2.1 E H Dw l Xo c P p i hP
  have red : ∀ q : TRing c.F, IsReduced q.R := fun q => (Ideal.isRadical_iff_quotient_reduced q.I).1 q.rad
  choose g hg using fun (q : TRing c.F) (y : FrPt Xo c q.R) => haveI := red q; exists_sum hr hA hT hf y
  have ext : ∀ (q : TRing c.F) (v w : q.R), (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
      (φ : q.R →ₐ[c.F] Ω), φ v = φ w) → v = w := fun q v w h =>
    haveI := red q
    sub_eq_zero.1 (GeometricValues.eq_zero_of_forall_algClosed (K := c.F) _ fun Ω _ _ _ φ => by
      rw [map_sub, h Ω φ, sub_self])
  have hsec : g ∈ sec Xo c a n := by
    refine ⟨fun q q' φ y z h => ext _ _ _ fun Ω _ _ _ ψ => ?_, fun q t y y' h => ext _ _ _ fun Ω _ _ _ ψ => ?_⟩
    · obtain ⟨w, hw⟩ := bc_exists ψ z
      exact (hg q' z Ω ψ w hw).trans
        (hg q y Ω (ψ.comp φ) w (frMap_trans (Xo := Xo) (c := c) _ _ _ φ ψ y z w h hw)).symm
    · obtain ⟨w, hw⟩ := bc_exists ψ y
      obtain ⟨w', hw'⟩ := bc_exists ψ y'
      rw [map_mul, hg q y Ω ψ w hw, hg q y' Ω ψ w' hw']
      refine (GlobalTheory.T.heckeKernel_value_sum_weight_triangular_frame E H Dw l Xo c P p i a n hA hT (hL.2.2.1 E H Dw l Xo c P p i hP) f hf Ω _ w w'
        (frBorBC (Xo := Xo) (c := c) _ _ ψ t y y' w w' h hw hw')).trans ?_
      congr 1
      simp [wchar]
  refine ⟨hkScal c cq P i n • g, Submodule.smul_mem _ _ hsec, fun Ω _ _ _ y => ?_⟩
  rw [evalAt_smul]
  congr 1
  have hy := GlobalTheory.T.framedPoint_reduced_from_testRing GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c Ω y
  rw [evalAt, dif_pos hy]
  exact hg _ _ Ω _ y hy.choose_spec.choose_spec.choose_spec

end Sec

section Cusp

open NumberField AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open GlobalTheory.HkFam (admitted)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Formalism.L2.PjFree.Unf Xo c σ r} {P : Ideal (𝓞 E)} {p i : ℕ}

theorem perFr_natCast_smul (X : Data E r) (x : Frame X.Ψ r) (N : ℕ) (v : Fin r → E) (τ : E →+* ℂ) (m : ℕ) :
    Formalism.L2.PjFree.perFr X x ((N : E) • v) τ m = N * Formalism.L2.PjFree.perFr X x v τ m := by
  have e : ∀ τ : E →+* ℂ, Data.emb τ ((N : E) • v) = (N : ℂ) • Data.emb τ v := fun τ => by
    funext a; simp [Data.emb]
  unfold Formalism.L2.PjFree.perFr
  split_ifs
  · rw [e, Matrix.mulVec_smul]; rfl
  · simp
  · rw [e, FD.hermC_smul_right]; simp
  · simp
  · simp

theorem exists_qmatch (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r)
    (hxi : ∀ k k' (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ‖τ (U.X k').ξ0‖) (hA : admitted l P p)
    {k k' : U.Comp} {x : (U.X k).dom} {x' : (U.X k').dom} {C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)}
    {z : FrPt Xo c (CAt σ)} {t : Ix Dw → (CAt σ)ˣ} (hC : Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C)
    (hm : HkPtC p (U.un k x) C z) (hb : FrBor t (U.un k' x') z)
    (hx : IsUnitFr (U.X k) x.1) (hx' : IsUnitFr (U.X k') x'.1) :
    ∃ (a : GL (Fin r) E) (h : QMatch (U.X k) (U.X k') p a), ∃ b ∈ Bor (U.X k').Ψ r,
      x'.1 = rmul (lact a (castFr h.psi x.1)) b ∧ (∀ τ i, ‖b τ i i‖ = 1) ∧ ∀ j, cabs (t (some j) : CAt σ) = 1 := by
  have hp0 : 0 < p := hA.2.2.1.pos
  obtain ⟨gam, A, htr, hsur, hA0, hAp, hAt⟩ := GlobalTheory.T.exists_similitude_triangular_periods_of_heckePoint E H Dw l Xo c σ r U hσ hU P p i k k' x x' C z t hA hC hm hb
  obtain ⟨a, ε, hε, hξ, hav, hlat, hiso⟩ := GlobalTheory.T.exists_rational_isometry_of_trace_similitude_sq E r (U.X k) (U.X k') p hp0 (hxi k k') gam htr hsur
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hrr, hty, -⟩ := hU
  have hΨ : (U.X k).Ψ = (U.X k').Ψ := Finset.ext fun τ => ((hty k).2 τ).trans ((hty k').2 τ).symm
  have hp : (U.X k).p0 = (U.X k').p0 := (hty k).1.trans (hty k').1.symm
  let e := Equiv.ofBijective _ hbij
  have he : ∀ τ, Formalism.L2.PjFree.relab c σ (e.symm τ) = τ := e.apply_symm_apply
  have m1 : ∀ τ ∈ (U.X k).Ψ, Dw.mult (e.symm τ) = r - (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_pos ((hrt _).1 (by rw [he]; exact ((hty k).2 τ).1 hτ)), (hty k).1]
    omega
  have m2 : ∀ τ ∉ (U.X k).Ψ, Dw.mult (e.symm τ) = (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg (fun h => hτ (((hty k).2 τ).2 (by rw [← he τ]; exact (hrt _).2 h))), (hty k).1]
  have hrel : ∀ τ, ∀ i < Dw.mult (e.symm τ), ∀ v ∈ (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k') x'.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
        ∑ j ∈ Finset.range (Dw.mult (e.symm τ)), A (e.symm τ) i j * Formalism.L2.PjFree.perFr (U.X k) x.1 v τ j :=
    fun τ i hi v hv => by
      have := hAp (e.symm τ) i hi ⟨v, hv⟩
      rw [he, ← hav, perFr_natCast_smul] at this
      exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hp0.ne') this
  rcases hε with rfl | rfl
  · have h : QMatch (U.X k) (U.X k') p a :=
      ⟨hΨ, hp, by rw [hξ, _root_.one_mul], fun u v => by rw [hiso, _root_.one_mul],
        fun v hv => hav ⟨v, hv⟩ ▸ (gam ⟨v, hv⟩).2, hlat⟩
    obtain ⟨b, hb, hxb, hu⟩ := GlobalTheory.T.frames_differ_by_isometry_of_triangular_periods E r _ _ p a h hp0 (fun τ => Dw.mult (e.symm τ)) m1 m2 x.1 x.2 x'.1 x'.2
      (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel
    obtain ⟨h1, h2⟩ := hu hx hx'
    refine ⟨a, h, b, hb, hxb, h1, fun ⟨τ, i⟩ => ?_⟩
    have := h2 (e τ) i (by rw [e.symm_apply_apply]; exact i.2)
    rw [e.symm_apply_apply, hAt] at this
    exact this
  · exact (GlobalTheory.T.not_antiIsometry_of_triangular_related_periods E r _ _ hΨ hp hr a hiso (fun τ => Dw.mult (e.symm τ)) m1 m2 x.1 x.2 x'.1 x'.2
      (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel).elim

theorem laU_qmatch {k k' : U.Comp} {N : ℕ} {a : GL (Fin r) E} (h : QMatch (U.X k) (U.X k') N a)
    (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : (U.X k').Ψ) (i : Fin r) :
    Formalism.L2.PjFree.laU U w n k' τ i = Formalism.L2.PjFree.laU U w n k ⟨τ.1, h.mem τ⟩ i := by
  unfold Formalism.L2.PjFree.laU
  rw [h.p0]

theorem rdU_mem_SS (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r)
    (hxi : ∀ k k' (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ‖τ (U.X k').ξ0‖) (hA : admitted l P p) {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (hD : Dom w n) {cq : c.F} {f g : Rul Xo c} (hf : f ∈ sec Xo c w n) (hg : g ∈ sec Xo c w n)
    (hfc : ∀ k, Formalism.L2.PjFree.rdU U f k ∈ (U.X k).SS (Formalism.L2.PjFree.laU U w n k))
    (hF : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.FinKer Xo c P p i) (hT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.IsTransform Xo c P p i cq n f g) (k : U.Comp) :
    Formalism.L2.PjFree.rdU U g k ∈ (U.X k).SS (Formalism.L2.PjFree.laU U w n k) := by
  have hsec := hU.2.2.2.2.1 w n hD g hg k
  obtain ⟨hun1, hun2⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r U hσ hU
  obtain ⟨M, hM⟩ := exists_card_heckeKer_le (Xo := Xo) (i := i) hA
  refine GlobalTheory.T.mem_cuspSections_of_dominated_rational_isometries E r _ U.Comp U.X _ _ _ _ p (‖σ (hkScal c cq P i n)‖ * (M * ((Ideal.absNorm P : ℝ) ^ i) ^ n))
    hA.2.2.1.pos (by positivity) hsec hfc (fun j a h => laU_qmatch h w n) fun x hx B hB0 hB => ?_
  obtain ⟨x₀, hx₀, ⟨b₀, hb₀, e₀⟩, -⟩ := hun1 k ⟨x, hx⟩
  letI := fieldCAt σ
  haveI := algClosedCAt σ
  have hb0 := norm_pos_iff.2 (AR.Up.OntoE.bchar_ne _ (Formalism.L2.PjFree.laU U w n k) hb₀)
  have hterm : ∀ C, cabs (term P p i f (U.un k x₀) C) ≤
      ((Ideal.absNorm P : ℝ) ^ i) ^ n * (‖bchar (Formalism.L2.PjFree.laU U w n k) b₀‖ * B) := fun C => by
    rw [term, hkTerm]
    split_ifs with hex
    swap
    · exact (norm_zero (E := ℂ)).trans_le (by positivity)
    have hz := hex.choose_spec
    generalize hex.choose = z at hz ⊢
    obtain ⟨k', x', t, hx', hb⟩ := hun2 z
    obtain ⟨a, h, b, hbB, hxb, hb1, ht⟩ := exists_qmatch hσ hU hr hxi hA C.2 hz hb hx₀ hx'
    have ht0 := GlobalTheory.T.heckeIsogeny_generatorRatio_le_traceTerms E H Dw l Xo c σ r U hσ hU P p i k k' x₀ x' C.1 z t hA C.2 hz hb hx₀ hx'
    have hQ := (hfc k').1.1
    have v2 : Formalism.L2.PjFree.rdU U f k' x'.1 = Formalism.L2.PjFree.toC (evR Xo c f (U.un k' x')) := dif_pos x'.2
    have v3 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 (CAt σ)
      (inferInstanceAs (IsReduced ℂ)) w n f hf t _ z hb
    have v4 : ‖Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ)‖ ≤ ((Ideal.absNorm P : ℝ) ^ i) ^ n := by
      have : Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ) =
        ∏ j, Formalism.L2.PjFree.toC (t j : CAt σ) ^ ex Dw w n j := rfl
      rw [this, norm_prod, Fintype.prod_option, Finset.prod_eq_one fun j _ => by
          rw [norm_pow, show ‖Formalism.L2.PjFree.toC (t (some j) : CAt σ)‖ = 1 from ht j, one_pow], _root_.mul_one, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ht0 n
    have v6 : ‖bchar (Formalism.L2.PjFree.laU U w n k') b‖ = 1 := by
      unfold bchar
      simp only [norm_prod, norm_zpow, hb1, one_zpow, Finset.prod_const_one]
    have v5 : ‖Formalism.L2.PjFree.rdU U f k' x'.1‖ ≤ ‖bchar (Formalism.L2.PjFree.laU U w n k) b₀‖ * B := by
      rw [hxb, hQ.2.1 _ (h.mem_dom x₀.2) b hbB, norm_mul, v6, _root_.one_mul, e₀,
        GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul,
        hQ.2.1 _ (h.mem_dom hx) _ (GlobalTheory.Dict.Pull.cast_bor h.psi hb₀),
        GlobalTheory.Dict.Pull.cast_bchar h.psi (laU_qmatch h w n), norm_mul]
      exact mul_le_mul_of_nonneg_left (hB k' a h) hb0.le
    rw [v2] at v5
    refine (congrArg cabs v3).trans_le ((norm_mul (Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ)) _).trans_le ?_)
    exact mul_le_mul v4 v5 (norm_nonneg _) (by positivity)
  have hfin := hF (CAt σ) (U.un k x₀)
  have := Fintype.ofFinite (hkKer (Xo := Xo) P p i (CAt σ) (U.un k x₀))
  have hc : (Fintype.card (hkKer (Xo := Xo) P p i (CAt σ) (U.un k x₀)) : ℝ) ≤ M := by
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast hM (CAt σ) (U.un k x₀).x
  have v1 : Formalism.L2.PjFree.rdU U g k x₀.1 =
      σ (hkScal c cq P i n) * ∑ C, Formalism.L2.PjFree.toC (term P p i f (U.un k x₀) C) :=
    (dif_pos x₀.2).trans ((hT (CAt σ) (U.un k x₀)).trans (congrArg _ (finsum_eq_sum_of_fintype _)))
  have v7 := congrArg norm v1
  rw [e₀, hsec.2.1 x hx b₀ hb₀, norm_mul, norm_mul] at v7
  have v8 := (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul Finset.univ
    (fun C => ‖Formalism.L2.PjFree.toC (term P p i f (U.un k x₀) C)‖) _ fun C _ => hterm C)
  rw [Finset.card_univ, nsmul_eq_mul] at v8
  refine le_of_mul_le_mul_left ?_ hb0
  rw [v7]
  refine (mul_le_mul_of_nonneg_left (v8.trans (mul_le_mul_of_nonneg_right hc (by positivity)))
    (norm_nonneg _)).trans_eq (by ring)

end Cusp


open Formalism.BasicNotions _root_.Formalism.L2.Pj in
theorem cuspTransform : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.CuspTransform := by
  intro D T h j hj P p i cq a n hs _ hD hE hDt hF f hf
  have hp := h.pins
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  obtain ⟨hs', hc⟩ := (mem_cusp _ _ _ _ _ _).1 hf
  refine (mem_cusp _ _ _ _ _ _).2 ⟨(hkOp hE hDt hF f).2, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩
  have hU := h.unf j hj σ hσ
  exact rdU_mem_SS (U := Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU (hU.1 ▸ hpq)
    (fun k k' τ => (h.xiAbs j hj σ hσ k τ).trans (h.xiAbs j hj σ hσ k' τ).symm)
    ⟨hs.max, hs.split, hs.prime, hs.under, hs.off⟩ hD hs' (hkOp hE hDt hF f).2
    (fun k => GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ (hc σ hσ) k) hF (hkOp_spec hE hDt hF f) k

theorem heckeTransform_of_pointLaws : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform :=
  fun h => ⟨secTransform h, cuspTransform⟩

end GlobalTheory.HeckeEx
end
end

namespace GlobalTheory.HeckeMember

theorem heckeInt_transform_readTie :
    GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt ∧ GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform ∧ GlobalTheory.HeckeSupSt.HeckeReadTie :=
  ⟨GlobalTheory.HkIntegral.heckeInt,
   GlobalTheory.HeckeEx.heckeTransform_of_pointLaws
     (GlobalTheory.HeckePointLaw.heckePointLaws_of_transport GlobalTheory.ThetaTransport.thetaTransportLaw),
   GlobalTheory.HeckeReadProof.heckeReadTie GlobalTheory.SplitLinear.splitLinearModel GlobalTheory.VacStabFixed.vacFixed⟩

end GlobalTheory.HeckeMember
