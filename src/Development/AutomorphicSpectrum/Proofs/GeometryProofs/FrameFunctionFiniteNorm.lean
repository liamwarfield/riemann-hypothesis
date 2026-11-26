module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerWeightOfZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodReductionDvrModelExists
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionAnalyticNorm
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FramedPointSpecialization

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineFunctionModelRatio
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FrameRatioConstantRational
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MemOfFixedByAutomorphisms
open NumberField IsDedekindDomain

namespace PositivityTheory.Xgn.FixedFieldAutomorphism

open scoped Cardinal

theorem exists_equiv {R K L : Type} [CommRing R] [IsDomain R] [Field K] [Field L]
    [IsAlgClosed K] [IsAlgClosed L] [Algebra R K] [Algebra R L] [FaithfulSMul R K]
    [FaithfulSMul R L] (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ g : K ≃+* L, ∀ r, g (algebraMap R K r) = algebraMap R L r := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK
  have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR
    (hKL ▸ hK)
  have h3 : #s = #t := by rw [← h1, ← h2, hKL]
  obtain ⟨e⟩ := Cardinal.eq.1 h3
  haveI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  haveI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let e' : Algebra.adjoin R (Set.range ((↑) : s → K)) ≃ₐ[R]
      Algebra.adjoin R (Set.range ((↑) : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L e'.toRingEquiv, fun r => ?_⟩
  rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap,
    IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : t → L))) L]
  congr 1
  exact e'.commutes r

theorem exists_aut {R : Type} [CommRing R] [IsDomain R] (hR : #R ≤ ℵ₀) (i j : R →+* ℂ)
    (hi : Function.Injective i) (hj : Function.Injective j) :
    ∃ g : ℂ ≃+* ℂ, ∀ r, g (i r) = j r := by
  have hC : ℵ₀ < #ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  exact @exists_equiv R ℂ ℂ _ _ _ _ _ _ i.toAlgebra j.toAlgebra
    ((@faithfulSMul_iff_algebraMap_injective R ℂ _ _ i.toAlgebra).2 hi)
    ((@faithfulSMul_iff_algebraMap_injective R ℂ _ _ j.toAlgebra).2 hj) hR hC rfl

end PositivityTheory.Xgn.FixedFieldAutomorphism

theorem PositivityTheory.Xgn.mem_of_fixed_by_automorphisms : ∀ (F : IntermediateField ℚ ℂ) (c : ℂ), FiniteDimensional ℚ F → (∀ g : ℂ ≃+* ℂ, (∀ a ∈ F, g a = a) → g c = c) → c ∈ F := by
  intro F c hF h
  have hFc : Cardinal.mk F ≤ Cardinal.aleph0 := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ F
    simpa using this
  by_cases hc : IsAlgebraic F c
  · have hint : IsIntegral F c := hc.isIntegral
    haveI : FiniteDimensional F (IntermediateField.adjoin F {c}) :=
      IntermediateField.adjoin.finiteDimensional hint
    set_option synthInstance.maxHeartbeats 200000 in
    have hE : Cardinal.mk (IntermediateField.adjoin F {c}) ≤ Cardinal.aleph0 := by
      refine (Algebra.IsAlgebraic.cardinalMk_le_max F _).trans (max_le hFc le_rfl)
    have key : ∀ φ : IntermediateField.adjoin F {c} →ₐ[F] ℂ,
        φ = (IntermediateField.adjoin F {c}).val := by
      intro φ
      obtain ⟨g, hg⟩ := PositivityTheory.Xgn.FixedFieldAutomorphism.exists_aut hE
        (IntermediateField.adjoin F {c}).val.toRingHom φ.toRingHom
        (RingHom.injective _) (RingHom.injective _)
      have h1 : g c = c := h g fun a ha => by
        have := hg (algebraMap F _ ⟨a, ha⟩)
        simpa using this
      have h2 := hg (IntermediateField.AdjoinSimple.gen F c)
      refine (IntermediateField.adjoin.powerBasis hint).algHom_ext ?_
      rw [IntermediateField.adjoin.powerBasis_gen]
      exact h2.symm.trans h1
    have hcard := AlgHom.card F (IntermediateField.adjoin F {c}) ℂ
    have h1 : Module.finrank F (IntermediateField.adjoin F {c}) = 1 := by
      rw [← hcard, Fintype.card_eq_one_iff]
      exact ⟨_, key⟩
    have h2 : c ∈ (⊥ : IntermediateField F ℂ) :=
      IntermediateField.finrank_adjoin_simple_eq_one_iff.1 h1
    obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 h2
    exact a.2
  · exfalso
    have hc' : ¬ IsAlgebraic F (c + 1) := fun h' => hc (by
      have := h'.isIntegral.sub (isIntegral_one (R := F))
      simpa using this.isAlgebraic)
    have hP : Cardinal.mk (Polynomial F) ≤ Cardinal.aleph0 :=
      Polynomial.cardinalMk_le_max.trans (max_le hFc le_rfl)
    obtain ⟨g, hg⟩ := PositivityTheory.Xgn.FixedFieldAutomorphism.exists_aut hP
      (Polynomial.aeval (R := F) c).toRingHom (Polynomial.aeval (R := F) (c + 1)).toRingHom
      (transcendental_iff_injective.1 hc) (transcendental_iff_injective.1 hc')
    have h1 : g c = c := h g fun a ha => by
      have := hg (Polynomial.C ⟨a, ha⟩)
      simpa using this
    have h2 := hg Polynomial.X
    simp [h1] at h2
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace PositivityTheory.Xgn.FrameRatioConstant

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem ratio_frames {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ φ' : FrameFn Xo c} (h : IsLineFn U τ φ)
    (h' : IsLineFn U τ φ') {F : Type} [Field F] {β : c.F →+* F} {y : Sp F ⟶ Xo.XF c} {v v' : Vecs y D.p}
    {w w' : Vecs y D.q} (hf : IsFramed U τ β y v w) (hf' : IsFramed U τ β y v' w') {r : F}
    (hr : φ' F y v w = r * φ F y v w) : φ' F y v' w' = r * φ F y v' w' := by
  obtain ⟨-, A, hA, A', hA', -⟩ := GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change _ F Xo.univ.t.G (under y) _
    Xo.univ.t.act _ _ _ v v' hf.2.2.1 hf'.2.2.1
  obtain ⟨-, B, hB, -⟩ := GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change _ F Xo.univ.t.G (under y) _
    Xo.univ.t.act _ _ _ w w' hf.2.2.2 hf'.2.2.2
  have hd : A.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hA'
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have e := h.chg F β y v w v' w' A B hf hf' hA hB
  have e' := h'.chg F β y v w v' w' A B hf hf' hA hB
  apply mul_right_cancel₀ hd
  rw [e', hr, _root_.mul_assoc, _root_.mul_assoc, e]

theorem ratio_spec {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ φ' : FrameFn Xo c} {κ : ℂ} (h : IsLineFn U τ φ)
    (h' : IsLineFn U τ φ')
    (hκ : ∀ y v w, IsFramed U τ (algebraMap c.F ℂ) y v w → φ' ℂ y v w = κ * φ ℂ y v w)
    {F : Type} [Field F] {β : c.F →+* F} {y : Sp F ⟶ Xo.XF c} {v : Vecs y D.p}
    {w : Vecs y D.q} (hf : IsFramed U τ β y v w) :
    ∃ (k : Type) (_ : Field k) (β₀ : c.F →+* k) (f : k →+* F) (j : k →+* ℂ) (r : k), r ≠ 0 ∧ f.comp β₀ = β ∧
      j.comp β₀ = algebraMap c.F ℂ ∧ φ' F y v w = f r * φ F y v w ∧
      ∀ j' : k →+* ℂ, j'.comp β₀ = algebraMap c.F ℂ → j' r = κ := by
  obtain ⟨k, _, β₀, y₀, v₀, w₀, f, j, h₀, hβ, hj, rfl, up⟩ :=
    PositivityTheory.Xgn.framed_point_specialization E H D l Xo c U τ F β y v w hf
  have n0 := h.ne k β₀ y₀ v₀ w₀ h₀
  have n0' := h'.ne k β₀ y₀ v₀ w₀ h₀
  refine ⟨k, inferInstance, β₀, f, j, φ' k y₀ v₀ w₀ / φ k y₀ v₀ w₀, div_ne_zero n0' n0, hβ, hj, ?_, ?_⟩
  · obtain ⟨v', w', hf', ev, ew⟩ := up F f
    rw [hβ] at hf'
    refine ratio_frames h h' hf' hf ?_
    rw [h.nat k F f β₀ y₀ v₀ w₀ _ v' w' h₀ rfl ev ew, h'.nat k F f β₀ y₀ v₀ w₀ _ v' w' h₀ rfl ev ew, ← map_mul,
      div_mul_cancel₀ _ n0]
  · intro j' hj'
    obtain ⟨v', w', hf', ev, ew⟩ := up ℂ j'
    rw [hj'] at hf'
    have e := hκ _ v' w' hf'
    rw [h.nat k ℂ j' β₀ y₀ v₀ w₀ _ v' w' h₀ rfl ev ew, h'.nat k ℂ j' β₀ y₀ v₀ w₀ _ v' w' h₀ rfl ev ew] at e
    rw [map_div₀, e, mul_div_cancel_right₀ _ ((map_ne_zero j').2 n0)]

end PositivityTheory.Xgn.FrameRatioConstant

open PositivityTheory.Xgn.FrameRatioConstant in
theorem PositivityTheory.Xgn.frame_ratio_constant_rational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c) (κ : ℂ), τ (H.rt : E) = H.rt0 → IsLineFn U τ φ → IsLineFn U τ φ' → (∀ y v w, IsFramed U τ (algebraMap c.F ℂ) y v w → φ' ℂ y v w = κ * φ ℂ y v w) → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  intro E _ _ _ H D l Xo c U τ φ φ' κ _ h h' hκ
  by_cases hex : ∃ (F : Type) (_ : Field F) (β : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q),
      IsFramed U τ β y v w
  · obtain ⟨F₀, _, β₁, y₁, v₁, w₁, hf₁⟩ := hex
    obtain ⟨k, _, β₀, -, j, r, hr, -, hj, -, hall⟩ := ratio_spec h h' hκ hf₁
    have hjr := hall j hj
    have hmem : κ ∈ c.F := by
      refine PositivityTheory.Xgn.mem_of_fixed_by_automorphisms c.F κ c.fin fun g hg => ?_
      have := hall (g.toRingHom.comp j) (by
        rw [RingHom.comp_assoc, hj]
        ext a
        exact hg a a.2)
      rw [RingHom.comp_apply, hjr] at this
      exact this
    refine ⟨⟨κ, hmem⟩, fun h0 => ?_, fun F _ βF y v w hf => ?_⟩
    · have : κ = 0 := congrArg Subtype.val h0
      exact (map_ne_zero j).2 hr (hjr.trans this)
    · obtain ⟨k', _, β₀', f, j', r', -, hβ, hj', e, hall'⟩ := ratio_spec h h' hκ hf
      have : r' = β₀' ⟨κ, hmem⟩ := j'.injective (by
        rw [hall' j' hj']
        exact (DFunLike.congr_fun hj' ⟨κ, hmem⟩).symm)
      rw [e, this, ← hβ]
      rfl
  · exact ⟨1, one_ne_zero, fun F _ βF y v w hf => absurd ⟨F, inferInstance, βF, y, v, w, hf⟩ hex⟩
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace PositivityTheory.Xgn.LineFunctionModelRatio₂

theorem exists_typeFn {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))
  refine ⟨_, fun i => (e.symm i).1, ?_⟩
  have key : ∀ τ : E →+* ℂ, Nat.card {i // (e.symm i).1 = τ} = m τ := by
    intro τ
    have e1 : {i // (e.symm i).1 = τ} ≃ Fin (m τ) :=
      (e.symm.subtypeEquiv (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype τ)
    rw [Nat.card_congr e1, Nat.card_fin]
  intro τ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [key]; simp [m, h]
  · rw [key]; simp [m, h]

end PositivityTheory.Xgn.LineFunctionModelRatio₂

theorem PositivityTheory.Xgn.line_function_model_ratio : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (U : Set (Xo.XF c)) (Z : CptOver Y U) (Z' : CptOver Y' U) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c), FracBase β → FracBase β' → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → Z.IsGeom → Z'.IsGeom → FlatOnModel Z τ φ → FlatOnModel Z' τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  intro hR hG E _ _ _ H D l Xo c O _ β Y O' _ β' Y' U Z Z' τ φ φ' hO hO' hpq hτ hZ hZ' hφ hφ'
  obtain ⟨g, ty, hty⟩ := PositivityTheory.Xgn.LineFunctionModelRatio₂.exists_typeFn H D.p D.q
  obtain ⟨FU⟩ := GlobalTheory.CompanionTheory.Ar.Top.complex_uniformisation_holds E H D l Xo
    ((algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom) g ty hpq rfl hty
  obtain ⟨Φ, hΦ, -⟩ := GlobalTheory.CompanionTheory.Ar.Flat.anUnit E H D l Xo c τ τ (algebraMap c.F ℂ) g ty FU hty hτ (fun _ => rfl)
  obtain ⟨κ, hκ, h₁⟩ := GlobalTheory.CompanionTheory.Ar.Flat.flat_eq_const_mul_unitAn hR hG E H D l Xo c O β Y U Z τ
    (algebraMap c.F ℂ) Φ φ hO hpq hτ hτ hZ hΦ hφ.1 hφ
  obtain ⟨κ', -, h₂⟩ := GlobalTheory.CompanionTheory.Ar.Flat.flat_eq_const_mul_unitAn hR hG E H D l Xo c O' β' Y' U Z' τ
    (algebraMap c.F ℂ) Φ φ' hO' hpq hτ hτ hZ' hΦ hφ'.1 hφ'
  refine PositivityTheory.Xgn.frame_ratio_constant_rational E H D l Xo c U τ φ φ' (κ' / κ) hτ hφ.1 hφ'.1 fun y v w hf => ?_
  rw [h₁ y v w hf, h₂ y v w hf]
  field_simp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionTwoModelsRelay
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionTwoModelsRelay
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.frame_function_two_models_relay : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (U : Set (Xo.XF c)) (Z : CptOver Y U) (Z' : CptOver Y' U) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c), FracBase β → FracBase β' → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → Z.IsGeom → Z'.IsGeom → FlatOnModel Z τ φ → FlatOnModel Z' τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  first | exact @PositivityTheory.Xgn.line_function_model_ratio | exact PositivityTheory.Xgn.line_function_model_ratio
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionTwoModelsRelayStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_function_two_models_relay : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (U : Set (Xo.XF c)) (Z : CptOver Y U) (Z' : CptOver Y' U) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c), FracBase β → FracBase β' → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → Z.IsGeom → Z'.IsGeom → FlatOnModel Z τ φ → FlatOnModel Z' τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  first | exact @GlobalTheory.CompanionTheory.Relay.frame_function_two_models_relay | exact GlobalTheory.CompanionTheory.Relay.frame_function_two_models_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.frame_function_two_models_relay <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionFiniteNorm
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.FinGood

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem finGood : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), FracBase β → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → U ∈ irreducibleComponents (Xo.XF c) → Z.IsGeom → FlatOnModel Z τ φ → l.GoodAt p → ∃ t : ℝ, HasFinNorm U τ φ p κ t := by
  intro hRes hGaga E _ _ _ H D l Xo c O _ β Y U Z τ φ p κ hβ hpq hrt hU hZ hφ hgood
  obtain ⟨O', _, _, _, β', Y', hβ', hκ, hsplit, hN3⟩ := GlobalTheory.T.good_reduction_dvr_model_exists E H D l Xo c p κ hpq hgood
  obtain ⟨-, hne, hgeom⟩ := GlobalTheory.T.irreducible_component_clopen E H D l Xo c U hU
  obtain ⟨Z'⟩ := hne O' β' Y' hβ'
  have hZ' : Z'.IsGeom := hgeom O β Y O' β' Y' Z Z' hβ hβ' hZ
  obtain ⟨φ', hline', hflat', -⟩ := GlobalTheory.T.flat_zero_from_resolution_and_gaga hRes hGaga E H D l Xo c O' β' Y' U Z' τ hβ' hpq hrt hZ'
  obtain ⟨t', ht'⟩ := GlobalTheory.T.finite_constant_all_holds E H D l Xo c O' β' Y' U Z' τ p κ φ' hrt hβ'.1 hκ hsplit hN3 hZ' hflat' hline'
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.T.frame_function_two_models_relay hRes hGaga E H D l Xo c O β Y O' β' Y' U Z Z' τ φ φ' hβ hβ' hpq hrt hZ hZ' hφ hflat'
  refine ⟨t' - Real.log ‖κ x‖, ?_⟩
  unfold GlobalTheory.CompanionTheory.Ar.Fl.HasFinNorm
  intro V K _ _ _ _ _ _ j β₁ y v w T tK m m' hj hjβ hfr hv hw
  have h1 := ht' V K j β₁ y v w T tK m m' hj hjβ hfr hv hw
  have hjx : j (β₁ x) = κ x := by rw [← hjβ]; rfl
  have hφne : j (φ K y v w) ≠ 0 := (map_ne_zero j).mpr (hφ.1.ne K β₁ y v w hfr)
  have hxne : j (β₁ x) ≠ 0 := (map_ne_zero j).mpr ((map_ne_zero β₁).mpr hx0)
  rw [hx K β₁ y v w hfr, map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hxne) (norm_ne_zero_iff.mpr hφne), hjx] at h1
  linarith

end GlobalTheory.CompanionTheory.Ar.Br.FinGood
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionFiniteNormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_function_finite_norm : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), FracBase β → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → U ∈ irreducibleComponents (Xo.XF c) → Z.IsGeom → FlatOnModel Z τ φ → l.GoodAt p → ∃ t : ℝ, HasFinNorm U τ φ p κ t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.FinGood.finGood | exact GlobalTheory.CompanionTheory.Ar.Br.FinGood.finGood | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.FinGood.finGood <;> assumption)
end
