module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeActionFramedPointsOfUnipotentModTwoPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenInertPlaceLatticeStabiliser
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinalRowGramAlgebraicSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepExistenceStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodCoverOverSizedField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodCoverOverSizedField
set_option autoImplicit false

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
open GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.CovTop.SizedCover

theorem stable_of_normal (R : IntermediateField ℚ ℂ) [hN : Normal ℚ R] (s : ℂ ≃+* ℂ) (a : ℂ) (ha : a ∈ R) : s a ∈ R := by
  have h := @AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ R (by convert hN)
    (s.toRingHom.toRatAlgHom.comp R.val)
  exact h.le ⟨⟨a, ha⟩, rfl⟩

theorem exists_ray (hRF : GlobalTheory.NT.RayField) {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n : ℕ) (hn : 3 ≤ n) :
    ∃ (R : IntermediateField ℚ ℂ) (a b : ℝ), Sz R a b ∧ a + b ≤ 20 * (Real.log n + Real.log H.d + 1) ∧
      (∀ s : ℂ ≃+* ℂ, ∀ z ∈ R, s z ∈ R) ∧ H.rt0 ∈ R ∧ zeta n ∈ R ∧ ∀ F, R ≤ F → GlobalTheory.FinalJoin.WeberIn H F n := by
  have hdm := H.d_mod
  have hd0 : 0 < H.d := H.d_prime.pos
  obtain ⟨hfin, h2⟩ := RayExistCurve.finrank_adjoin hd0 H.sqrt_neg_disc_sq
  have hr0 : H.rt0 ∈ ℚ⟮H.rt0⟯ := IntermediateField.mem_adjoin_simple_self ℚ H.rt0
  generalize ℚ⟮H.rt0⟯ = K₀ at hfin h2 hr0
  have hNF : NumberField K₀ := NumberField.mk
  have hr : (⟨H.rt0, hr0⟩ : K₀) ^ 2 = -(H.d : K₀) := Subtype.ext (by simpa using H.sqrt_neg_disc_sq)
  have hD : discr K₀ = -(H.d : ℤ) := discr_eq_neg_of_sq_eq h2 H.d_prime.squarefree (by omega) hr
  have hTC : IsTotallyComplex K₀ := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have h1 : InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩ ^ 2 = -(H.d : ℝ) := by
      rw [← map_pow, hr, map_neg, map_natCast]
    have h3 : (0 : ℝ) < H.d := by exact_mod_cast hd0
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩)]
  have hQ : Algebra.IsQuadraticExtension ℚ K₀ := ⟨h2⟩
  have hG : IsGalois ℚ K₀ := inferInstance
  obtain ⟨w, hw, hgen⟩ := exists_integer_generator_of_sq_eq_neg h2 H.d_prime.squarefree (by omega) hr
  let φ : K₀ →+* ℂ := algebraMap K₀ ℂ
  have hw' : φ w = (1 + H.rt0) / 2 := by
    have := congrArg φ hw
    rw [map_mul, map_add (f := _), map_one, map_ofNat] at this
    change _ = 1 + H.rt0 at this
    linear_combination this / 2
  have hc : ∀ a b : ℤ, φ ((a : 𝓞 K₀) + b * w : 𝓞 K₀) = a + b * ((1 + H.rt0) / 2) := fun a b => by
    rw [← hw']
    simp
  have hn0 : (n : 𝓞 K₀) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨L, _, _, _, hL⟩ := GlobalTheory.Mem.Fld.rayField_iff.1 hRF K₀ (Ideal.span {(n : 𝓞 K₀)})
    (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let ψ : L →ₐ[K₀] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e₀ : L ≃ₐ[K₀] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  have hfR : FiniteDimensional K₀ ψ.fieldRange := e₀.toLinearEquiv.finiteDimensional
  have hLR := fun (_ : NumberField ψ.fieldRange) => hL.of_algEquiv e₀
  generalize ψ.fieldRange = R at hfR hLR
  have hNR : NumberField R := NumberField.of_module_finite K₀ R
  have hin := (hLR hNR).isRayFieldIn_restrictScalars
  obtain ⟨hab, hR⟩ := hLR hNR
  change IsRay R (Ideal.span {(n : 𝓞 K₀)}) at hR
  have hGR : IsGalois ℚ R := GlobalTheory.RayNatGalois.isGalois_of_isRay_nat ℚ (L := K₀) (by omega) hR
  have hGR' : Normal ℚ (R.restrictScalars ℚ) := hGR.to_normal
  obtain ⟨hdeg, hsz⟩ := GlobalTheory.Mem.Fld.RaySize.degOver_le_and_sz K₀ _ n _ hin (by omega)
  have hNR' : NumberField (R.restrictScalars ℚ) := hNR
  have hdpos := GlobalTheory.Mem.Fld.degOver_pos _ _ hin.emb_mem
  refine ⟨R.restrictScalars ℚ, _, _, hsz, ?_, stable_of_normal _, R.algebraMap_mem (⟨H.rt0, hr0⟩ : K₀),
    GlobalTheory.Mem.RayRoots.rootOne_mem_of_isRayFieldIn K₀ _ n n _ (by omega) dvd_rfl hin, fun F hRle P hP => ?_⟩
  · have hcl := classNumber_le_abs_discr_of_finrank_eq_two K₀ h2
    generalize GlobalTheory.Mem.Fld.degOver _ _ hin.emb_mem = m at hdeg hdpos
    rw [h2] at hdeg
    rw [hD] at hcl
    rw [h2, hD]
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast, Nat.cast_ofNat] at hcl ⊢
    have hd1 : (1 : ℝ) ≤ H.d := by exact_mod_cast hd0
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hm : (0 : ℝ) < m := by exact_mod_cast hdpos
    have hm' : (m : ℝ) ≤ H.d * (n : ℝ) ^ 2 := by
      have : (m : ℝ) ≤ classNumber K₀ * (n : ℝ) ^ 2 := by exact_mod_cast hdeg
      exact this.trans (by gcongr)
    have h1 := Real.log_le_log hm hm'
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
    have h3 := Real.log_nonneg hd1
    have h4 := Real.log_nonneg hn1
    have h5 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    push_cast at h1
    linarith
  · have hW := GlobalTheory.T.weberInvariantTorsionValues_subset_rayClassField K₀ h2 (by omega) P (fun z => ?_) n hn R hR
    · exact ⟨hRle (hW (Set.mem_insert _ _)), fun s hs => hRle (hW (Set.mem_insert_of_mem _
        ⟨_, (hP _).2 ⟨s, rfl⟩, hs, rfl⟩))⟩
    · rw [hP]
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨_, hc s.1 s.2⟩
      · rintro ⟨a, rfl⟩
        obtain ⟨a, b, rfl⟩ := hgen a
        exact ⟨(a, b), hc a b⟩


set_option maxHeartbeats 1000000 in
theorem exists_good_sized : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (T : Core D), T.Q.Pins → ∀ j : ℕ, InR D j → 5 ≤ D.host.splitBound → Nat.Coprime 15 (D.host.g 0 * D.host.g 1) → ∀ e : ℕ, ∃ Y : Deep T j, Y.Good e (fieldSz T.Q.c.F + 20 * (Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * 15 ^ e) + Real.log D.host.d + 1)) := by
  intro hRF D T hQ j hj h5 h15 e
  obtain ⟨s, hs⟩ := Inhab.exists_root h5
  have hpos := Inhab.rank_pos T hQ j hj
  obtain ⟨I, hK, hp, hI⟩ := Inhab.exists_half T.Q.H s (by rw [hQ.1.1]; exact hs) e
  obtain ⟨l₂, l1, l2, l3, l4, l5, l6⟩ := GlobalTheory.CoverHalf.exists_coverLevel T.Q.l hQ.2.1.2 (15 ^ e) I (Odd.pow (by decide))
    (by rw [hQ.2.1.1]; exact h15.pow_left e) hK hp hI
  obtain ⟨Xo₂⟩ := GlobalTheory.Moduli.moduli_scheme_exists _ _ (T.Q.Dw j) l₂ hpos
  have hM' : l₂.M' = l₂.M := by
    show Nat.lcm l₂.M l₂.A = l₂.M
    rw [l6, Nat.lcm_one_right]
  obtain ⟨R, a, b, hsz, hab, hst, hrt, hz, hW⟩ := exists_ray hRF T.Q.H l₂.M l₂.three_le
  haveI := T.Q.c.fin
  have hsz0 : Sz T.Q.c.F (Real.log (Module.finrank ℚ T.Q.c.F))
      (Real.log |(discr T.Q.c.F : ℝ)| / (Module.finrank ℚ T.Q.c.F : ℝ)) := ⟨T.Q.c.fin, le_rfl, le_rfl⟩
  obtain ⟨hN, hN1, hN2⟩ := GlobalTheory.FieldSize.sz_sup _ _ _ _ _ _ hsz0 hsz
  have h1 : T.Q.c.F ≤ T.Q.c.F ⊔ R := le_sup_left
  have h2 : R ≤ T.Q.c.F ⊔ R := le_sup_right
  have hst' : ∀ s : ℂ ≃+* ℂ, (∀ a ∈ T.Q.c.F, s a = a) → ∀ a ∈ T.Q.c.F ⊔ R, s a ∈ T.Q.c.F ⊔ R := fun s hs a ha => by
    have : T.Q.c.F ⊔ R ≤ (T.Q.c.F ⊔ R).comap s.toRingHom.toRatAlgHom :=
      sup_le (fun x hx => show s x ∈ T.Q.c.F ⊔ R from (hs x hx).symm ▸ h1 hx) fun x hx => h2 (hst s x hx)
    exact this ha
  have hKA : KA l₂ ≤ T.Q.c.F ⊔ R := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro x (rfl | rfl)
    · exact h2 hrt
    · rw [l6]
      simpa [zeta] using one_mem (T.Q.c.F ⊔ R)
  generalize T.Q.c.F ⊔ R = N at hN hN1 hN2 h1 h2 hst' hKA
  haveI : NumberField N := NumberField.mk
  let c' : Coeff T.Q.l := ⟨N, hN, fun τ a => h1 (T.Q.c.conj τ a), h1 T.Q.c.zeta_mem, T.Q.c.le.trans h1⟩
  let c₂ : Coeff l₂ := ⟨N, hN, fun τ a => h1 (T.Q.c.conj τ a), hM' ▸ h2 hz, hKA⟩
  have hfa : FnAlgClosed (Xo := Xo₂) (c := c₂) := GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn D T.Q hQ j hj l₂ Xo₂ c₂ l₂.M
    (by have := l₂.three_le; omega) hM'.dvd (Or.inl (hW N h2))
  have hsize : fieldSz c₂.F ≤ fieldSz T.Q.c.F + 20 * (Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * 15 ^ e) +
      Real.log D.host.d + 1) := by
    rw [l2, hQ.2.1.1, hQ.1.1] at hab
    push_cast at hab
    unfold fieldSz
    have h3 : Real.log (Module.finrank ℚ c₂.F : ℝ) ≤ _ := hN1
    have h4 : Real.log |(discr c₂.F : ℝ)| / (Module.finrank ℚ c₂.F : ℝ) ≤ _ := hN2
    linarith
  obtain ⟨⟨pd', I', l₂', Xo₂', c₂', hF, r, mm, nab, cδ, φ₀⟩, a1, a2, a3, e₁, e₂, -, a4, a5⟩ :=
    GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ (T.Q.Xo j) c' hpos 0 (15 ^ e) I l₂ Xo₂ c₂ rfl l1 l2 l3 l4 l5
  dsimp only at a3 e₁ e₂
  subst a3
  obtain rfl := eq_of_heq e₁
  obtain rfl := eq_of_heq e₂
  obtain ⟨U, dict, Kf, h⟩ := Inhab.exists_good_of_cover T hQ j hj c' h1 _ e a1 a4 l6 hfa hst'
  exact ⟨_, h.mono hsize⟩

end GlobalTheory.CovTop.SizedCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodCoverOverSizedFieldStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_cover_over_sized_field : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (T : Core D), T.Q.Pins → ∀ j : ℕ, InR D j → 5 ≤ D.host.splitBound → Nat.Coprime 15 (D.host.g 0 * D.host.g 1) → ∀ e : ℕ, ∃ Y : Deep T j, Y.Good e (fieldSz T.Q.c.F + 20 * (Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * 15 ^ e) + Real.log D.host.d + 1)) := by
  first | exact @GlobalTheory.CovTop.SizedCover.exists_good_sized | exact GlobalTheory.CovTop.SizedCover.exists_good_sized | (intros; apply GlobalTheory.CovTop.SizedCover.exists_good_sized <;> assumption)
end
end

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.DeepExist

theorem floorThreeLOverLogThree_mul_log_fifteen_le {L : ℝ} (hL : 0 ≤ L) : (expL L : ℝ) * Real.log 15 ≤ 9 * L := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have he : (expL L : ℝ) ≤ 3 * L / Real.log 3 := Nat.floor_le (by positivity)
  have he' : (expL L : ℝ) * Real.log 3 ≤ 3 * L := (le_div_iff₀ h3).1 he
  have h15 : Real.log 15 ≤ 3 * Real.log 3 := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 15) (by norm_num : (15 : ℝ) ≤ 3 ^ 3)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have he0 : (0 : ℝ) ≤ expL L := Nat.cast_nonneg _
  nlinarith

theorem size_le {D : D7} {L : SizeData₂ D} {PP A M o : ℝ} (hN : HostNum D L PP A M) (hF : o ≤ 217 * zBase L ^ 2) :
    o + 20 * (Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * 15 ^ expL L.sc.L) + Real.log D.host.d + 1) ≤
      391 * zBase L ^ 2 := by
  have hL10 := hN.big.2.1
  have hcop := hN.cop
  have h01 : D.host.g 0 * D.host.g 1 ≠ 0 := fun h => by
    rw [h, Nat.coprime_zero_right] at hcop
    norm_num at hcop
  have hg0 : ((D.host.g 0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (mul_ne_zero_iff.1 h01).1
  have hg1 : ((D.host.g 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (mul_ne_zero_iff.1 h01).2
  have h15 : ((15 : ℝ) ^ expL L.sc.L) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hlog : Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * 15 ^ expL L.sc.L) =
      Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) + expL L.sc.L * Real.log 15 := by
    rw [Real.log_mul (mul_ne_zero hg0 hg1) h15, Real.log_mul hg0 hg1, Real.log_pow]
  have he := floorThreeLOverLogThree_mul_log_fifteen_le (L := L.sc.L) (by linarith)
  have a0 := hN.logg 0
  have a1 := hN.logg 1
  have ad := hN.logd
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hZ : 8 * L.sc.L ≤ zBase L := by
    unfold zBase
    have : (8 : ℝ) ≤ D.R.f * D.R.r := by nlinarith
    nlinarith
  rw [hlog]
  nlinarith

end GlobalTheory.CovTop.DeepExist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointOnModelPullbackCompatible
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.LiftW

theorem one_left_eq {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] :
    (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

theorem one_left_comp_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) hw
  have e := h.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at e
  have hxx : x₀ * x₀ = x₀ := by
    ext
    exact e
  have h1 : x₀ = 1 := mul_eq_right.mp hxx
  exact congrArg Over.Hom.left h1

end GlobalTheory.FlatModel.LiftW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropertyOfCodimOneLocalUnits
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.HartogsUnit

variable {A : Type} [CommRing A] [IsDomain A]

noncomputable def toFrac (p : Ideal A) [p.IsPrime] : Localization.AtPrime p →+* FractionRing A :=
  IsLocalization.lift (M := p.primeCompl) (S := Localization.AtPrime p)
    (g := algebraMap A (FractionRing A))
    (fun s => IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (p.primeCompl_le_nonZeroDivisors s.2)))

theorem toFrac_comp (p : Ideal A) [p.IsPrime] :
    (toFrac p).comp (algebraMap A (Localization.AtPrime p)) = algebraMap A (FractionRing A) :=
  IsLocalization.lift_comp _

theorem toFrac_mem (p : Ideal A) [p.IsPrime] (w : Localization.AtPrime p) :
    ∃ s, s ∉ p ∧ s • toFrac p w ∈ (algebraMap A (FractionRing A)).range := by
  obtain ⟨⟨m, s⟩, e⟩ := IsLocalization.surj p.primeCompl w
  refine ⟨s, s.2, m, ?_⟩
  have h := congrArg (toFrac p) e
  simp only [map_mul] at h
  rw [← RingHom.comp_apply (toFrac p), ← RingHom.comp_apply (toFrac p), toFrac_comp] at h
  rw [Algebra.smul_def, mul_comm, h]

end GlobalTheory.HartogsUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaStdAddNsmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegCover

theorem unitOn_pow' {R : Type} [CommRing R] (u : Rˣ) (m : ℕ) : unitOn (u ^ m) = unitOn u ^ m := by
  unfold unitOn; exact map_pow _ u m

theorem unitOn_one' {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 := by
  unfold unitOn; exact map_one _

theorem weilIs_congr_base {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {m : ℤ} {k : Type} [Field k]
    {y y' : Sp k ⟶ S} (e : y = y') {x₁ x₂ : Over.mk y ⟶ A} {x₁' x₂' : Over.mk y' ⟶ A}
    (h₁ : x₁.left = x₁'.left) (h₂ : x₂.left = x₂'.left) {c : Γ(Sp k, ⊤)ˣ} (H : Out.WeilIs A L m x₁ x₂ c) :
    Out.WeilIs A L m x₁' x₂' c := by
  subst e
  rwa [← Over.OverMorphism.ext h₁, ← Over.OverMorphism.ext h₂]

theorem weilTransport : ∀ (h N m : ℕ) (B B₁ : Type) [CommRing B] [CommRing B₁] (ζ : B) (ζ₁ : B₁) (S T : Scheme.{0}) (s : S ⟶ Sp B) (sT : T ⟶ Sp B₁) (c : SiegPre h m ζ s) (C' : SiegPre h N ζ₁ sT) (t : T ⟶ S) (φ : C'.A.left ⟶ c.A.left), IsGrpPullback C'.A c.A t φ → (∃ φ₂ : (G2 C'.A).left ⟶ (G2 c.A).left, IsSquare φ φ₂ ∧ LBIso C'.P (c.P.pull φ₂)) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T) (β : B₁ →+* k) (z : kˣ) (y : Sp k ⟶ S) (g g' : Over.mk y ⟶ c.A) (a a' : Fin h ⊕ Fin h → ℤ), x ≫ sT = spMap β → (z : k) = β ζ₁ → y = x ≫ t → g.left = x ≫ (C'.lev a).left ≫ φ → g'.left = x ≫ (C'.lev a').left ≫ φ → Out.WeilIs c.A c.diag N g g' (unitOn (z ^ (2 * omegaStd a a'))) := by
  intro h N m B B₁ _ _ ζ ζ₁ S T s sT c C' t φ pb hφ k _ _ x β z y g g' a a' hx hz hy hg hg'
  obtain ⟨φ₂, sq, iso⟩ := hφ
  subst hy
  obtain ⟨-, -, g₃⟩ := C'.geom k x β z hx hz
  exact (weilIs_grpPullback_of_comm S T c.A C'.A t φ _ _ (pull_isLB c.isLB _) (pull_isLB C'.isLB _) pb
    (SiegelPull.diag_iso sq iso) (Over.mk x) N _ _ g g' _
    (by rw [hg, Over.comp_left, Over.toUnit_left, Category.assoc]; rfl)
    (by rw [hg', Over.comp_left, Over.toUnit_left, Category.assoc]; rfl)).1 (g₃ a a')

theorem omegaStd_add_nsmul {h : ℕ} (N : ℕ) (a a' c₁ c₂ : Fin h ⊕ Fin h → ℤ) :
    omegaStd (a + N • c₁) (a' + N • c₂) =
      omegaStd a a' + N * (omegaStd c₁ a' + omegaStd a c₂ + N * omegaStd c₁ c₂) := by
  simp only [omegaStd, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, mul_add,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.SiegCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreePointFieldAlgebraicallyClosed
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefFree

theorem mem_smul_top_of_coprime {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] (I J : Ideal R) (hIJ : J ⊔ I = ⊤)
    (f : N →ₗ[R] N) (h : ∀ z ∈ J • (⊤ : Submodule R N), f z ∈ I • (⊤ : Submodule R N)) (x : N) :
    f x ∈ I • (⊤ : Submodule R N) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hIJ ▸ Submodule.mem_top : (1 : R) ∈ J ⊔ I)
  have e : f x = f (a • x) + b • f x := by rw [map_smul, ← add_smul, hab, one_smul]
  rw [e]
  exact add_mem (h _ (Submodule.smul_mem_smul ha Submodule.mem_top)) (Submodule.smul_mem_smul hb Submodule.mem_top)

theorem natCast_not_isUnit {K : Type} [Field K] [NumberField K] {g : ℕ} (hg : g.Prime) : ¬ IsUnit (g : 𝓞 K) := by
  intro hu
  have h1 := hu.map (Algebra.norm ℤ : 𝓞 K →* ℤ)
  have e : ((g : 𝓞 K)) = algebraMap ℤ (𝓞 K) (g : ℤ) := by simp
  rw [e, Algebra.norm_algebraMap] at h1
  have hn : Module.finrank ℤ (𝓞 K) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff hn, Int.isUnit_iff] at h1
  have := hg.two_le
  rcases h1 with h1 | h1 <;> omega

theorem sup_span_ne_top {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (l : Level H)
    {g : ℕ} (hg : g.Prime) (hd : g ∣ l.M) : l.Mb ⊔ Ideal.span {(g : 𝓞 E)} ≠ ⊤ := by
  intro htop
  have hb : Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) l.Mb ⊔ Ideal.span {(g : 𝓞 E)} = ⊤ := by
    have := congrArg (Ideal.map (H.bar : 𝓞 E →+* 𝓞 E)) htop
    rwa [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.map_top] at this
  have hle : (⊤ : Ideal (𝓞 E)) ≤ Ideal.span {(g : 𝓞 E)} := by
    calc (⊤ : Ideal (𝓞 E)) = (l.Mb ⊔ Ideal.span {(g : 𝓞 E)}) * (Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) l.Mb ⊔ Ideal.span {(g : 𝓞 E)}) := by
          rw [htop, hb, Ideal.top_mul]
      _ ≤ Ideal.span {(g : 𝓞 E)} := by
          rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, l.prod]
          refine sup_le (sup_le ?_ (Ideal.mul_le_inf.trans inf_le_right)) (sup_le (Ideal.mul_le_inf.trans inf_le_left) (Ideal.mul_le_inf.trans inf_le_left))
          rw [Ideal.span_singleton_le_span_singleton]
          exact_mod_cast (Nat.cast_dvd_cast hd : ((g : 𝓞 E)) ∣ (l.M : 𝓞 E))
  exact natCast_not_isUnit hg (Ideal.span_singleton_eq_top.1 (top_le_iff.1 hle))

end GlobalTheory.DefFree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfMemDualWeylLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfMemDualWeylLattice
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.DualWeylDeg

theorem weight_colW_apply {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (t : Fin N) :
    (Finsupp.weight (colW N N) m) t = ∑ a : Fin N, m (a, t) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, Pi.smul_apply, colW, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp only [Pi.single_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb; simp; intro h; exact absurd h.symm hb
  · simp

theorem totalDegree_le_of_mem_dualWeyl : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O), f ∈ dualWeyl O N N ν → f.totalDegree ≤ ∑ a, ν a := by
  intro O _ N ν f hf
  have h1 : f ∈ weightedHomogeneousSubmodule O (colW N N) ν := (Submodule.mem_inf.mp hf).1
  rw [mem_weightedHomogeneousSubmodule] at h1
  rw [totalDegree]
  refine Finset.sup_le fun m hm => ?_
  have h2 : Finsupp.weight (colW N N) m = ν := h1 (mem_support_iff.mp hm)
  have h3 : m.sum (fun _ e => e) = ∑ t, ∑ a : Fin N, m (a, t) := by
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type, Finset.sum_comm]
  rw [h3]
  refine le_of_eq (Finset.sum_congr rfl fun t _ => ?_)
  rw [← weight_colW_apply, h2]

end GlobalTheory.DualWeylDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfMemDualWeylLatticeStatement
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalDegree_le_of_mem_dualWeylLattice : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O), f ∈ dualWeyl O N N ν → f.totalDegree ≤ ∑ a, ν a := by
  first | exact @GlobalTheory.DualWeylDeg.totalDegree_le_of_mem_dualWeyl | exact GlobalTheory.DualWeylDeg.totalDegree_le_of_mem_dualWeyl | (intros; apply GlobalTheory.DualWeylDeg.totalDegree_le_of_mem_dualWeyl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFibrePowerAndExternalTensorSectionNonzeroClo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFibrePowerAndExternalTensorSectionNonzeroClo
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels

namespace GlobalTheory.BoxNonzeroClosed

theorem flat_powObj {S : Scheme.{0}} (G : Over S) [Flat G.hom] : ∀ n : ℕ, Flat (Out.powObj G n).hom
  | 0 => inferInstanceAs (Flat (𝟙 S))
  | n + 1 => by
    have := flat_powObj G n
    exact inferInstanceAs (Flat (pullback.fst G.hom (Out.powObj G n).hom ≫ G.hom))

theorem flat_pow {S : Scheme.{0}} (G : Over S) [Flat G.hom] (N : ℕ) : Flat (pow G N).hom := by
  have := flat_powObj G N
  let e : pow G N ≅ Out.powObj G N :=
    (productIsProduct (fun _ : Fin N => G)).conePointUniqueUpToIso (Out.powIsLimit G N)
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  rw [← Over.w e.hom]
  infer_instance

theorem main : ∀ (V : Type) [CommRing V] [IsLocalRing V] (G : Over (Sp V)) [Flat G.hom] (L : LB G.left) (θ : L.Sec),
    NonzeroClosed (X := G) θ → ∀ N : ℕ, Flat (pow G N).hom ∧ NonzeroClosed (X := pow G N) (boxSec G θ N) := by
  rintro V _ _ G _ L θ ⟨g, hg, hθ⟩ N
  refine ⟨flat_pow G N, ?_⟩
  obtain ⟨y, hy, hy'⟩ := GlobalTheory.BoxSection.exists_point (fun k => Pi.π (fun _ : Fin N => G) k)
    (productIsProduct (fun _ : Fin N => G)) _ (fun _ => g) (fun _ => hg)
  exact ⟨y, hy, GlobalTheory.BoxSection.mem_nonzeroLocus_prodSec L (pr G N) (fun _ => θ) y
    fun i => (hy' i).symm ▸ hθ⟩

end GlobalTheory.BoxNonzeroClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFibrePowerAndExternalTensorSectionNonzeroCloStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_fibrePower_and_externalTensorSection_nonzero_closedFibre : ∀ (V : Type) [CommRing V] [IsLocalRing V] (G : Over (Sp V)) [Flat G.hom] (L : LB G.left) (θ : L.Sec), NonzeroClosed (X := G) θ → ∀ N : ℕ, Flat (pow G N).hom ∧ NonzeroClosed (X := pow G N) (boxSec G θ N) := by
  first | exact @GlobalTheory.BoxNonzeroClosed.main | exact GlobalTheory.BoxNonzeroClosed.main | (intros; apply GlobalTheory.BoxNonzeroClosed.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedFibreOfFramedComplexPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedFibreOfFramedComplexPoint
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem exists_isVecs_of_eigBasis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E}
    {S : Scheme.{0}} {t : SAB H S} {t' : SAB H (Sp ℂ)} {x : Sp ℂ ⟶ S} (m : SABMap t' t x) {g n : ℕ}
    (u : HolUnif t'.G t'.PP.L g) (hd : ∀ v, IsTangent v → ∃! z, u.IsDiff z v)
    (hd' : ∀ z, ∃! v, IsTangent v ∧ u.IsDiff z v) {χ : 𝓞 E →+* ℂ} {v : Fin n → (epsAt x ⟶ t.G)}
    (hv : IsEigBasisAt t.act x χ v) : ∃ V : Fin n → Fin g → ℂ, IsVecs u m.φ v V ∧ LinearIndependent ℂ V := by
  choose v' hv' using fun i => FlatRow.exists_lift m.cart (v i)
  have ix := FlatDegreeCompare.Indep.of_eigBasis (((FlatRow.fibre_iff m.cart hv').2 m.act χ).2 hv)
  choose V hV using fun i => (hd _ (ix.1 i)).exists
  exact ⟨V, fun i => ⟨v' i, hv' i, hV i⟩, FlatDegreeCompare.ArchExists.linearIndependent_of_indep u hd' ix hV⟩

theorem exists_unif_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (e : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) v w, FrU Xo c U τ e y v w → ∃ (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (m : ObjMap o Xo.univ (y ≫ toX Xo c)) (g : ℕ) (u : HolUnif o.t.G o.t.PP.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (κ : u.Λ → ℂ) (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ), u.IsAH Hm κ ∧ IsVecs u m.toSABMap.φ v V ∧ IsVecs u m.toSABMap.φ w W ∧ LinearIndependent ℂ V ∧ LinearIndependent ℂ W := by
  intro E _ _ _ H D l Xo c U τ e y v w h
  rw [← Category.assoc]
  obtain ⟨t', ⟨n⟩⟩ := exists_sab (y ≫ toX Xo c) Xo.univ.t
  obtain ⟨T, hT, -⟩ := CM.exists_pat_of_obj E H D l _ _ _ _ (ModelCompare.objOfSABMap Xo.univ n)
  obtain rfl : T.t = t' := hT
  obtain ⟨rig, hrig⟩ := T.pol.rigid
  obtain ⟨u, Hm, κ, -, hA, -, hd, hd', -⟩ := thetaUnifAV_all T.pol rig hrig
  obtain ⟨V, hV, iV⟩ := exists_isVecs_of_eigBasis n u hd hd' h.2.2.1
  obtain ⟨W, hW, iW⟩ := exists_isVecs_of_eigBasis n u hd hd' h.2.2.2
  exact ⟨ModelCompare.objOfSABMap Xo.univ n, ModelCompare.objMapOfSABMap Xo.univ n, _, u, Hm, κ, V, W, hA, hV, hW,
    iV, iW⟩

end GlobalTheory.DetLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedFibreOfFramedComplexPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformised_fibre_of_framed_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (e : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) v w, FrU Xo c U τ e y v w → ∃ (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (m : ObjMap o Xo.univ (y ≫ toX Xo c)) (g : ℕ) (u : HolUnif o.t.G o.t.PP.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (κ : u.Λ → ℂ) (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ), u.IsAH Hm κ ∧ IsVecs u m.toSABMap.φ v V ∧ IsVecs u m.toSABMap.φ w W ∧ LinearIndependent ℂ V ∧ LinearIndependent ℂ W := by
  first | exact @GlobalTheory.DetLine.exists_unif_of_frame | exact GlobalTheory.DetLine.exists_unif_of_frame | (intros; apply GlobalTheory.DetLine.exists_unif_of_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSectionProjectiveOverField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSectionProjectiveOverField
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
open GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem secClosed_closedPoint (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Sp K) (z : Sp K ⟶ X)
    (_hq : IsProjOver q) (hz : z ≫ q = 𝟙 _) :
    IsClosed ({z (IsLocalRing.closedPoint K)} : Set X) := by
  have : IsClosedImmersion z := isClosedImmersion_of_comp_eq_id q z hz
  have hc : IsClosed (Set.range z.base) := z.isClosedEmbedding.isClosed_range
  convert hc using 1
  ext x
  constructor
  · rintro rfl; exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    rw [Set.mem_singleton_iff, Subsingleton.elim y (IsLocalRing.closedPoint K)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSectionProjectiveOverFieldStatement
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
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_image_section_projective_over_field : ∀ (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Sp K) (z : Sp K ⟶ X), IsProjOver q → z ≫ q = 𝟙 _ → IsClosed ({z (IsLocalRing.closedPoint K)} : Set X) := by
  first | exact @GlobalTheory.secClosed_closedPoint | exact GlobalTheory.secClosed_closedPoint | (intros; apply GlobalTheory.secClosed_closedPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspOfMovesAt
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def MovesAt (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
    (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E)
    (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a)
    (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom) : Prop :=
  ∃ (hy : castFrame hm.psi (lact a x) ∈ ((uAt r v i).X k').dom) (t : _),
    FrBor t ((uAt r v i).un k' ⟨castFrame hm.psi (lact a x), hy⟩) (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c γ ((uAt r v i).un k ⟨x, hx⟩))

def ReadsInv (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k)
    (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
    (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E) : Prop :=
  ∀ w : lattice₂ D ((uAt r v i).X k).Λ,
    ∃ hw : Matrix.mulVec (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (w : Fin D.R.r → D.host.E) ∈
        lattice₂ D ((uAt r v i).X k').Λ,
      Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (lattice₂ D ((uAt r v i).X k').Λ))) ⟨_, hw⟩ =
        ψ k' (γ.symm ((ψ k).symm (Submodule.Quotient.mk w)))

theorem isTransp_of_movesAt {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} {i : Fin D.R.m}
    {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
    {ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k}
    {γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l}
    {k k' : (uAt r v i).Comp} {a : GL (Fin D.R.r) D.host.E}
    (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a)
    (h₁ : ∀ x hx, MovesAt p r i v γ k k' a hm x hx) (h₂ : ReadsInv p r i v ψ γ k k' a) :
    IsTransp p r i v ψ γ k k' a :=
  ⟨hm, h₁, h₂⟩

end GlobalTheory.ShareOn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VariableMatrixDetPolyPowMulMemDualWeyl
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VariableMatrixDetPolyPowMulMemDualWeyl
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRead

theorem detPol_mem_dualWeyl_one (R : Type) [CommRing R] (n : ℕ) :
    detPol R n ∈ dualWeyl R n n (fun _ => 1) := by
  have h := Formalism.GradedWeylDivisibility.bidetMem R n n 1 (fun _ => n) (fun _ => le_refl n) (fun _ => id)
  have hb : bideterminant R (r := n) (n := n) (fun _ : Fin 1 => n) (fun _ => le_refl n) (fun _ => id) = detPol R n := by
    simp [bideterminant, initMinor, detPol]
  have hs : shapeDeg (n := n) (fun _ : Fin 1 => n) = fun _ => 1 := by
    funext t
    simp [shapeDeg, t.isLt]
  rw [hb, hs] at h
  exact h

theorem detPol_pow_mul_mem_dualWeyl : ∀ (R : Type) [CommRing R] (n k : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R), f ∈ dualWeyl R n n ν → detPol R n ^ k * f ∈ dualWeyl R n n fun a => ν a + k := by
  intro R _ n k ν f hf
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    have h := (Formalism.GradedWeylDivisibility.dualWeylMul R n n (fun _ => 1) (fun a => ν a + k) (detPol R n) (detPol R n ^ k * f)).1
      (detPol_mem_dualWeyl_one R n) ih
    have he : ((fun _ => 1) + fun a => ν a + k) = fun a : Fin n => ν a + (k + 1) := by
      funext a; simp only [Pi.add_apply]; omega
    rw [he, ← mul_assoc, ← pow_succ'] at h
    exact h

end GlobalTheory.FrameRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VariableMatrixDetPolyPowMulMemDualWeylStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.variableMatrixDetPoly_pow_mul_mem_dualWeyl : ∀ (R : Type) [CommRing R] (n k : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R), f ∈ dualWeyl R n n ν → detPol R n ^ k * f ∈ dualWeyl R n n fun a => ν a + k := by
  first | exact @GlobalTheory.FrameRead.detPol_pow_mul_mem_dualWeyl | exact GlobalTheory.FrameRead.detPol_pow_mul_mem_dualWeyl | (intros; apply GlobalTheory.FrameRead.detPol_pow_mul_mem_dualWeyl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAlgClosedCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAlgClosedCharZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MBLow

theorem exists_level_algClosed_charZero :
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (P : PolAV (Sp C)) (k : ℕ), 1 ≤ k → ∃ ζ : Cˣ, Nonempty (Out.Level P k (unitOn ζ)) := by
  intro C _ _ _ P k hk
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hk0 : (k : C) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have : NeZero (k : C) := ⟨hk0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C k
  let ze : Cˣ := (hζ.isUnit (by omega)).unit
  have hze : IsPrimitiveRoot ze k := IsPrimitiveRoot.coe_units_iff.1 (by simpa [ze] using hζ)
  obtain ⟨pt, hpt, hw⟩ := EllipticLevel.exists_symplectic_system hL P k hk0 ze hze
  have prim : ∀ {R : Type} [CommRing R] [Nontrivial R] (φ : C →+* R),
      IsPrimitiveRoot (Units.map φ.toMonoidHom ze) k := fun φ =>
    hze.map_of_injective (f := Units.map φ.toMonoidHom) (Units.map_injective φ.injective)
  have nt : ∀ (F : Type) [Field F], Nontrivial Γ(Spec (CommRingCat.of F), ⊤) := fun F _ =>
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨lev, -⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp C) P k (unitOn ze)
    (by have := nt C; exact prim (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)
    (fun F _ s => by
      have := nt F
      refine ⟨?_, prim (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)⟩
      have : CharZero F := charZero_of_injective_ringHom (Spec.preimage s).hom.injective
      exact Nat.cast_ne_zero.2 (by omega))
    pt hpt hw
  exact ⟨ze, ⟨lev⟩⟩

end GlobalTheory.MBLow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAlgClosedCharZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLevel_algClosed_charZero : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (P : PolAV (Sp C)) (k : ℕ), 1 ≤ k → ∃ ζ : Cˣ, Nonempty (Out.Level P k (unitOn ζ)) := by
  first | exact @GlobalTheory.MBLow.exists_level_algClosed_charZero | exact GlobalTheory.MBLow.exists_level_algClosed_charZero | (intros; apply GlobalTheory.MBLow.exists_level_algClosed_charZero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneIffIntegralAtPadicEmbeddingPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneIffIntegralAtPadicEmbeddingPlace
open NumberField IsDedekindDomain

set_option autoImplicit false

namespace GlobalTheory.FrameRead

theorem norm_map_le_one_of_isIntegral_int {F C : Type} [CommRing F] [NormedField C] [IsUltrametricDist C] (f : F →+* C) {x : F}
    (hx : IsIntegral ℤ x) : ‖f x‖ ≤ 1 := by
  have hy : IsIntegral ℤ (f x) := hx.map f.toIntAlgHom
  have := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hy.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at this
  exact_mod_cast this

theorem norm_le_one_iff_integral_at : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l), AtPlace w e0 → ∀ x : K, ‖e0 x‖ ≤ 1 ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ r : 𝓞 K, (s : K) * x = r := by
  intro K _ _ l _ w e0 hw x
  constructor
  · intro hx
    obtain ⟨n, d, h | h⟩ := w.exists_primeCompl_mul_eq_or_mul_eq (K := K) x
    · exact ⟨d, d.2, n, by rw [mul_comm]; exact h⟩
    · by_cases hn : n ∈ w.asIdeal
      · exfalso
        refine d.2 ((hw d).2 ?_)
        have h1 : ‖e0 ((d : 𝓞 K) : K)‖ = ‖e0 x‖ * ‖e0 (n : K)‖ := by
          have : ((d : 𝓞 K) : K) = x * (n : K) := h.symm
          rw [this, map_mul, norm_mul]
        rw [h1]
        have h2 : ‖e0 (n : K)‖ < 1 := (hw n).1 hn
        calc ‖e0 x‖ * ‖e0 (n : K)‖ ≤ 1 * ‖e0 (n : K)‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact h2
      · exact ⟨n, hn, d, by rw [mul_comm]; exact h⟩
  · rintro ⟨s, hs, r, hr⟩
    have hs1 : 1 ≤ ‖e0 (s : K)‖ := by
      by_contra h
      exact hs ((hw s).2 (lt_of_not_ge h))
    have hr1 : ‖e0 (r : K)‖ ≤ 1 := norm_map_le_one_of_isIntegral_int e0 r.isIntegral_coe
    have h1 : ‖e0 (s : K)‖ * ‖e0 x‖ ≤ 1 := by rw [← norm_mul, ← map_mul, hr]; exact hr1
    nlinarith [norm_nonneg (e0 x)]

end GlobalTheory.FrameRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneIffIntegralAtPadicEmbeddingPlaceStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_one_iff_integral_at_padicEmbedding_place : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l), AtPlace w e0 → ∀ x : K, ‖e0 x‖ ≤ 1 ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ r : 𝓞 K, (s : K) * x = r := by
  first | exact @GlobalTheory.FrameRead.norm_le_one_iff_integral_at | exact GlobalTheory.FrameRead.norm_le_one_iff_integral_at | (intros; apply GlobalTheory.FrameRead.norm_le_one_iff_integral_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataMapSupComapClosedImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataMapSupComapClosedImmersion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.ClosedImmIdeal

theorem ideal_comap_preimage {T W : Scheme.{0}} (i : T ⟶ W) [IsClosedImmersion i]
    (J : W.IdealSheafData) (U : W.affineOpens) :
    (J.comap i).ideal ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ = Ideal.map (i.app U.1).hom (J.ideal U) := by
  rw [GlobalTheory.Principalise.comapIdealAffine J i U ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ le_rfl,
    Scheme.Hom.app_eq_appLE]

theorem iSup_preimage_affineOpens {T W : Scheme.{0}} (i : T ⟶ W) :
    ⨆ U : W.affineOpens, i ⁻¹ᵁ U.1 = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]

theorem comap_map_eq {T W : Scheme.{0}} (i : T ⟶ W) [IsClosedImmersion i] (a : T.IdealSheafData) :
    (a.map i).comap i = a := by
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun U : W.affineOpens => ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩) (iSup_preimage_affineOpens i) fun U => ?_
  rw [ideal_comap_preimage, Scheme.IdealSheafData.ideal_map_of_isAffineHom,
    Ideal.map_comap_of_surjective _ (i.app_surjective U.1 U.2)]

theorem map_comap_eq {T W : Scheme.{0}} (i : T ⟶ W) [IsClosedImmersion i] (b : W.IdealSheafData)
    (hb : (⊥ : T.IdealSheafData).map i ≤ b) : (b.comap i).map i = b := by
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_map_comap _ _)
  refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun U : W.affineOpens => U)
    (iSup_affineOpens_eq_top W) fun U => ?_
  have h0 := hb U
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom] at h0 ⊢
  rw [ideal_comap_preimage, Ideal.comap_map_of_surjective _ (i.app_surjective U.1 U.2)]
  refine sup_le le_rfl (le_trans ?_ h0)
  simp

theorem map_sup_comap_and_comap_map : ∀ (T W : Scheme.{0}) (i : T ⟶ W), IsClosedImmersion i →
    ∀ (a : T.IdealSheafData) (J : W.IdealSheafData),
      (a ⊔ J.comap i).map i = a.map i ⊔ J ∧ (a.map i).comap i = a := by
  intro T W i hi a J
  haveI := hi
  refine ⟨?_, comap_map_eq i a⟩
  have hb : (⊥ : T.IdealSheafData).map i ≤ a.map i ⊔ J :=
    le_sup_of_le_left (Scheme.IdealSheafData.map_mono i bot_le)
  rw [← map_comap_eq i _ hb, Scheme.IdealSheafData.comap_sup, comap_map_eq]

end GlobalTheory.ClosedImmIdeal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataMapSupComapClosedImmersionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion : ∀ (T W : Scheme.{0}) (i : T ⟶ W), IsClosedImmersion i → ∀ (a : T.IdealSheafData) (J : W.IdealSheafData), (a ⊔ J.comap i).map i = a.map i ⊔ J ∧ (a.map i).comap i = a := by
  first | exact @GlobalTheory.ClosedImmIdeal.map_sup_comap_and_comap_map | exact GlobalTheory.ClosedImmIdeal.map_sup_comap_and_comap_map | (intros; apply GlobalTheory.ClosedImmIdeal.map_sup_comap_and_comap_map <;> assumption)
end
end
