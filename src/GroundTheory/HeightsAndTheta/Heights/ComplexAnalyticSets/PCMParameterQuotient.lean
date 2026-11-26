module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalizedQuotLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOrdFiniteNonZeroDivisor

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMParameterQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

theorem IsCohenMacaulayLocalRing.of_ringEquiv {A C : Type*} [CommRing A] [CommRing C]
    [IsCohenMacaulayLocalRing A] (e : A ≃+* C) : IsCohenMacaulayLocalRing C := by
  have : Nontrivial C := e.injective.nontrivial
  have : IsLocalRing C := IsLocalRing.of_surjective' e.toRingHom e.surjective
  have : IsNoetherianRing C := isNoetherianRing_of_ringEquiv A e
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := A)
  refine { exists_isWeaklyRegular := ⟨rs.map e, ?_, ?_, ?_⟩ }
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    have hs' := hm s hs
    rw [mem_maximalIdeal, mem_nonunits_iff] at hs' ⊢
    exact fun h => hs' (by simpa using h.map e.symm)
  · have := RingHomInvPair.of_ringEquiv e
    have := RingHomInvPair.symm (↑e : A →+* C) (e.symm : C →+* A)
    exact (e.toSemilinearEquiv.isWeaklyRegular_congr' rs).1 hreg
  · rw [← ringKrullDim_eq_of_ringEquiv e, hdim, List.length_map]

theorem exists_nat_of_add_natCast_eq {a : WithBot ℕ∞} {m n : ℕ}
    (h : a + (m : WithBot ℕ∞) = (n : WithBot ℕ∞)) : ∃ k : ℕ, a = k ∧ k + m = n := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj, top_add] at h
      exact absurd h (ENat.top_ne_natCast n)
    | coe k =>
      refine ⟨k, rfl, ?_⟩
      exact_mod_cast h

theorem CMParameterQuotient.proof (hreg : CMRegularElement.Statement.{0}) :
    CMParameterQuotient.Statement := by
  intro B _ _ d
  induction d generalizing B with
  | zero =>
    intro x _ _
    have h0 : Ideal.span (Set.range x) = ⊥ := by
      rw [Set.range_eq_empty, Ideal.span_empty]
    exact IsCohenMacaulayLocalRing.of_ringEquiv
      ((RingEquiv.quotientBot B).symm.trans (Ideal.quotEquivOfEq h0.symm))
  | succ d ih =>
    classical
    intro x hx hdim
    let x' : Fin d → B ⧸ Ideal.span {x 0} := fun i => Ideal.Quotient.mk _ (x i.succ)
    have hIJ : Ideal.span (Set.range x) =
        Ideal.span {x 0} ⊔ Ideal.span (Set.range (Fin.tail x)) := by
      rw [Fin.range_fin_succ, Ideal.span_insert]
    have hmap : (Ideal.span (Set.range (Fin.tail x))).map (Ideal.Quotient.mk (Ideal.span {x 0})) =
        Ideal.span (Set.range x') := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    let e : (B ⧸ Ideal.span {x 0}) ⧸ Ideal.span (Set.range x') ≃+* B ⧸ Ideal.span (Set.range x) :=
      (Ideal.quotEquivOfEq hmap.symm).trans
        ((DoubleQuot.quotQuotEquivQuotSup _ _).trans (Ideal.quotEquivOfEq hIJ.symm))
    have hIne : Ideal.span {x 0} ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal B).ne_top (top_le_iff.1 (h ▸ (Ideal.span_singleton_le_iff_mem _).2 (hx 0)))
    have : Nontrivial (B ⧸ Ideal.span {x 0}) := Ideal.Quotient.nontrivial_iff.2 hIne
    have : IsLocalRing (B ⧸ Ideal.span {x 0}) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x 0})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hx' : ∀ i, x' i ∈ maximalIdeal (B ⧸ Ideal.span {x 0}) := fun i =>
      (mem_maximalIdeal _).2 fun hu =>
        (mem_maximalIdeal _).1 (hx i.succ) (isUnit_of_map_unit (Ideal.Quotient.mk _) _ hu)
    obtain ⟨rs, -, -, hD⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
    have he := ringKrullDim_eq_of_ringEquiv e
    obtain ⟨k, hk, hkn⟩ := exists_nat_of_add_natCast_eq (hdim.trans hD)

    have hKrull : ringKrullDim (B ⧸ Ideal.span {x 0}) ≤ (k : WithBot ℕ∞) + (d : WithBot ℕ∞) := by
      have hs : ((Finset.univ.image x' : Finset _) : Set _) ⊆ SetLike.coe (Ring.jacobson (B ⧸ Ideal.span {x 0})) := by
        rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
        intro z hz
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ] at hz
        obtain ⟨i, rfl⟩ := hz
        exact hx' i
      have h1 := ringKrullDim_le_ringKrullDim_quotient_add_card _ hs
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, he, hk] at h1
      refine h1.trans ?_
      gcongr
      exact_mod_cast Finset.card_image_le.trans (Finset.card_univ.trans (Fintype.card_fin d)).le
    have hmin : ∀ p ∈ minimalPrimes B, x 0 ∉ p := by
      intro p hp hyp
      have hle : Ideal.span {x 0} ≤ p := (Ideal.span_singleton_le_iff_mem _).2 hyp
      have h1 := ringKrullDim_quotient_eq_of_mem_minimalPrimes hp
      have h2 : ringKrullDim (B ⧸ p) ≤ ringKrullDim (B ⧸ Ideal.span {x 0}) :=
        ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
      have h3 := (h1.symm.trans_le h2).trans hKrull
      rw [hD] at h3
      have h4 : rs.length ≤ k + d := by exact_mod_cast h3
      omega
    obtain ⟨hnzd, hCM⟩ := hreg B (x 0) (hx 0) hmin
    have hdimI : ringKrullDim (B ⧸ Ideal.span {x 0}) + ((1 : ℕ) : WithBot ℕ∞) = (rs.length : WithBot ℕ∞) := by
      rw [Nat.cast_one, ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hnzd (hx 0),
        hD]
    obtain ⟨k', hk', hk'n⟩ := exists_nat_of_add_natCast_eq hdimI
    have hdim' : ringKrullDim ((B ⧸ Ideal.span {x 0}) ⧸ Ideal.span (Set.range x')) + (d : WithBot ℕ∞) =
        ringKrullDim (B ⧸ Ideal.span {x 0}) := by
      rw [he, hk, hk']
      exact_mod_cast (by omega : k + d = k')
    have : IsCohenMacaulayLocalRing (B ⧸ Ideal.span {x 0}) := hCM
    have := ih (B ⧸ Ideal.span {x 0}) x' hx' hdim'
    exact IsCohenMacaulayLocalRing.of_ringEquiv e

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartChangeSheetNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace ChartChangeSheetNull

variable {n d : ℕ}

theorem eval_linForm (u x : Fin n → ℂ) : eval x (linForm u) = linEval u x := by
  simp [linForm, linEval]

theorem continuous_linEval (u : Fin n → ℂ) : Continuous (linEval u) := by
  unfold linEval
  fun_prop

theorem exists_poly_of_linForm {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {u : Fin n → ℂ} (hJ : J.IsPrime) (hA : IsFiniteProjection J A) (hu : linForm u ∉ J) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧
      ∀ x ∈ zeroSet J, linEval u x = 0 → eval (A *ᵥ x) c = 0 := by
  classical
  have hv0 : Ideal.Quotient.mk J (linForm u) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hu
  have hex : ∃ k, ∃ p : Polynomial (MvPolynomial (Fin d) ℂ), p.Monic ∧ p.natDegree = k ∧
      p.eval₂ (projHom J A).toRingHom (Ideal.Quotient.mk J (linForm u)) = 0 := by
    obtain ⟨p, hpm, hp⟩ := hA.finite.to_isIntegral (Ideal.Quotient.mk J (linForm u))
    exact ⟨_, p, hpm, rfl, hp⟩
  obtain ⟨p, hpm, hpk, hp⟩ := Nat.find_spec hex
  have hc0 : p.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.2 h0
    have hqm : q.Monic := Polynomial.monic_X.of_mul_monic_left hpm
    have hdeg : (Polynomial.X * q).natDegree = q.natDegree + 1 :=
      Polynomial.natDegree_X_mul hqm.ne_zero
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_X, mul_eq_zero] at hp
    refine Nat.find_min hex (m := q.natDegree) (by omega) ⟨q, hqm, rfl, ?_⟩
    exact hp.resolve_left hv0
  have hQ : Ideal.Quotient.mk J (p.eval₂ (pullback A).toRingHom (linForm u)) = 0 := by
    rw [Polynomial.hom_eval₂]; exact hp
  have hQJ := Ideal.Quotient.eq_zero_iff_mem.1 hQ
  refine ⟨p.coeff 0, hc0, fun x hx hux => ?_⟩
  have h1 : eval x (p.eval₂ (pullback A).toRingHom (linForm u)) = 0 := hx _ hQJ
  rw [Polynomial.hom_eval₂, eval_linForm, hux, Polynomial.eval₂_at_zero] at h1
  have h2 : eval x (pullback A (p.coeff 0)) = 0 := h1
  rwa [ComplexSets.eval_pullback] at h2

theorem volume_image_zero {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {u : Fin n → ℂ} (hJ : J.IsPrime) (hA : IsFiniteProjection J A) (hu : linForm u ∉ J) :
    volume ((fun x => A *ᵥ x) '' {x | x ∈ zeroSet J ∧ linEval u x = 0}) = 0 := by
  obtain ⟨c, hc, hcz⟩ := exists_poly_of_linForm hJ hA hu
  refine measure_mono_null ?_ (DiscriminantSheetCover.volume_zero_set c hc)
  rintro _ ⟨x, ⟨hx, hux⟩, rfl⟩
  exact hcz x hx hux

theorem isOpen_dom {Us : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ} {U : Set (Fin n → ℂ)}
    (u : Fin n → ℂ) (hUs : IsOpen Us) (hsd : DifferentiableOn ℂ s Us) (hU : IsOpen U) :
    IsOpen (Us ∩ s ⁻¹' (U ∩ {x | linEval u x ≠ 0})) :=
  hsd.continuousOn.isOpen_inter_preimage hUs
    (hU.inter (isOpen_ne_fun (continuous_linEval u) continuous_const))

theorem differentiableOn_tau {Us : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ} {U : Set (Fin n → ℂ)}
    {Ψ : (Fin n → ℂ) → Fin n → ℂ} (u : Fin n → ℂ) (A' : Matrix (Fin d) (Fin n) ℂ)
    (hsd : DifferentiableOn ℂ s Us) (hΨ : DifferentiableOn ℂ Ψ U) :
    DifferentiableOn ℂ (fun w => A' *ᵥ Ψ (s w)) (Us ∩ s ⁻¹' (U ∩ {x | linEval u x ≠ 0})) :=
  SheetOnlyNull.differentiableOn_mulVec A' (s := Ψ ∘ s)
    (hΨ.comp (hsd.mono Set.inter_subset_left) fun _ hy => hy.2.1)

theorem exists_sheet_of_det_ne_zero {J J' : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} {u u' : Fin n → ℂ} {U U' : Set (Fin n → ℂ)}
    {Φ Ψ : (Fin n → ℂ) → Fin n → ℂ} (hU : IsOpen U) (hU' : IsOpen U')
    (hUsub' : zeroSet J' \ {x | linEval u' x = 0} ⊆ U')
    (hΦ : DifferentiableOn ℂ Φ U') (hΨ : DifferentiableOn ℂ Ψ U)
    (hΦm : Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}))
    (hΨm : Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}))
    (hΨΦ : ∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x)
    (hΦΨ : ∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x)
    {x : Fin n → ℂ} (hxu : linEval u x ≠ 0) (hxU : x ∈ U) {s : (Fin d → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s)
    (hdet : (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ Ψ (s w)) (A *ᵥ x)).det ≠ 0) :
    ∃ s', IsSheetAt J' A' (Ψ x) s' := by
  obtain ⟨Us, hUs, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  have hxZ : x ∈ zeroSet J := hsx ▸ (hsec _ hyU).2
  set D := Us ∩ s ⁻¹' (U ∩ {x | linEval u x ≠ 0}) with hDdef
  have hD : IsOpen D := isOpen_dom u hUs hsd hU
  have hyD : A *ᵥ x ∈ D := ⟨hyU, by simp only [Set.mem_preimage, hsx]; exact ⟨hxU, hxu⟩⟩
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ Ψ (s w) with hFdef
  have hFd : DifferentiableOn ℂ F D := differentiableOn_tau u A' hsd hΨ
  have hΨsd : DifferentiableOn ℂ (fun w => Ψ (s w)) D :=
    hΨ.comp (hsd.mono Set.inter_subset_left) fun _ hy => hy.2.1
  have hFa := SheetOnlyNull.analyticOnNhd_of_differentiableOn hD hFd
  set G : Set (Fin d → ℂ) := D ∩ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G := (SheetOnlyNull.analyticOnNhd_det_jacC hD hFd).continuousOn
    |>.isOpen_inter_preimage hD isOpen_compl_singleton
  have hinj : ∀ w, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0 → Function.Injective (fderiv ℂ F w) :=
    fun w hw => (SheetOnlyNull.injective_iff_det_ne_zero _).2 (by rwa [← ReciprocityTheory.AnForm.A.det_jacC])
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    refine ⟨(LinearEquiv.ofInjectiveEndo _ (hinj w hw.2)).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw.1).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  obtain ⟨e, he⟩ := hequiv _ ⟨hyD, hdet⟩
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hysrc : A *ᵥ x ∈ φ.source := he.mem_toOpenPartialHomeomorph_source
  have hFx : F (A *ᵥ x) = A' *ᵥ Ψ x := by simp only [hFdef, hsx]
  have hsym : φ.symm (A' *ᵥ Ψ x) = A *ᵥ x := by rw [← hFx, ← hφ, φ.left_inv hysrc]
  have hP : Ψ x ∈ zeroSet J' \ {x | linEval u' x = 0} := hΨm ⟨hxZ, hxu⟩
  have hΦc : ContinuousAt Φ (Ψ x) := (hΦ.differentiableAt (hU'.mem_nhds (hUsub' hP))).continuousAt
  have hΦP : Φ (Ψ x) = x := hΦΨ x ⟨hxZ, hxu⟩
  refine ⟨fun z => Ψ (s (φ.symm z)), φ.target ∩ φ.symm ⁻¹' G, φ.isOpen_inter_preimage_symm hG,
    ⟨by rw [← hFx, ← hφ]; exact φ.map_source hysrc, by rw [Set.mem_preimage, hsym]; exact ⟨hyD, hdet⟩⟩,
    ?_, by simp only [hsym, hsx], fun z hz => ⟨?_, (hΨm ⟨(hsec _ hz.2.1.1).2, hz.2.1.2.2⟩).1⟩, ?_⟩
  · intro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hsymd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact ((hΨsd.differentiableAt (hD.mem_nhds hzG.1)).comp z
      hsymd.differentiableAt).differentiableWithinAt
  · show F (φ.symm z) = z
    rw [← hφ, φ.right_inv hz.1]
  · have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
    have hnx : V ∩ (fun z => A *ᵥ z) ⁻¹' (φ.source ∩ D) ∈ 𝓝 x :=
      inter_mem hV (((φ.open_source.inter hD).preimage hAc).mem_nhds ⟨hysrc, hyD⟩)
    refine ⟨{z | linEval u' z ≠ 0} ∩ Φ ⁻¹' (V ∩ (fun z => A *ᵥ z) ⁻¹' (φ.source ∩ D)),
      inter_mem ((isOpen_ne_fun (continuous_linEval u') continuous_const).mem_nhds hP.2)
        (hΦc.preimage_mem_nhds (by rw [hΦP]; exact hnx)), ?_⟩
    rintro x'' ⟨hx''Z, hx''u, hx''V, hx''src, hx''D⟩ -
    have hx''P : x'' ∈ zeroSet J' \ {x | linEval u' x = 0} := ⟨hx''Z, hx''u⟩
    have hx'' : Φ x'' = s (A *ᵥ Φ x'') := hVs _ ⟨(hΦm hx''P).1, hx''V⟩ hx''D.1
    have hA' : A' *ᵥ x'' = φ (A *ᵥ Φ x'') := by
      rw [hφ, hFdef]
      show A' *ᵥ x'' = A' *ᵥ Ψ (s (A *ᵥ Φ x''))
      rw [← hx'', hΨΦ x'' hx''P]
    show x'' = Ψ (s (φ.symm (A' *ᵥ x'')))
    rw [hA', φ.left_inv hx''src, ← hx'', hΨΦ x'' hx''P]

theorem exists_det_ne_zero (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) {J J' : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} {u u' : Fin n → ℂ} {U U' : Set (Fin n → ℂ)}
    {Φ Ψ : (Fin n → ℂ) → Fin n → ℂ} (hJ' : J'.IsPrime) (hA' : IsFiniteProjection J' A')
    (hU : IsOpen U) (hU' : IsOpen U')
    (hUsub' : zeroSet J' \ {x | linEval u' x = 0} ⊆ U')
    (hΦ : DifferentiableOn ℂ Φ U') (hΨ : DifferentiableOn ℂ Ψ U)
    (hΦm : Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}))
    (hΨm : Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}))
    (hΨΦ : ∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x)
    (hΦΨ : ∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x)
    {x : Fin n → ℂ} (hxu : linEval u x ≠ 0) (hxU : x ∈ U) {s : (Fin d → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s) {W₀ : Set (Fin d → ℂ)} (hW₀ : IsOpen W₀) (hxW₀ : A *ᵥ x ∈ W₀) :
    ∃ w ∈ W₀, (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ Ψ (s w)) w).det ≠ 0 := by
  obtain ⟨Us, hUs, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  have hxZ : x ∈ zeroSet J := hsx ▸ (hsec _ hyU).2
  set D := Us ∩ s ⁻¹' (U ∩ {x | linEval u x ≠ 0}) with hDdef
  have hD : IsOpen D := isOpen_dom u hUs hsd hU
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ Ψ (s w) with hFdef
  have hFd : DifferentiableOn ℂ F D := differentiableOn_tau u A' hsd hΨ
  by_contra hall
  push Not at hall
  have hcrit : F '' (W₀ ∩ D) ⊆ F '' {w | w ∈ D ∧ ¬ Function.Injective (fderiv ℂ F w)} :=
    Set.image_mono fun w hw => ⟨hw.2, fun hinj => (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
      (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall w hw.1)⟩
  have hnull := measure_mono_null hcrit (h₂ d d D F hD hFd)
  have hP : Ψ x ∈ zeroSet J' \ {x | linEval u' x = 0} := hΨm ⟨hxZ, hxu⟩
  have hΦc : ContinuousAt Φ (Ψ x) := (hΦ.differentiableAt (hU'.mem_nhds (hUsub' hP))).continuousAt
  have hΦP : Φ (Ψ x) = x := hΦΨ x ⟨hxZ, hxu⟩
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  have hnx : V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ D) ∈ 𝓝 x :=
    inter_mem hV (((hW₀.inter hD).preimage hAc).mem_nhds
      ⟨hxW₀, hyU, by simp only [Set.mem_preimage, hsx]; exact ⟨hxU, hxu⟩⟩)
  have hN : {z | linEval u' z ≠ 0} ∩ Φ ⁻¹' (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ D)) ∈ 𝓝 (Ψ x) :=
    inter_mem ((isOpen_ne_fun (continuous_linEval u') continuous_const).mem_nhds hP.2)
      (hΦc.preimage_mem_nhds (by rw [hΦP]; exact hnx))
  have hnhds := h₁ n d J' (linPoly A') hJ' hA'.injective hA'.finite (Ψ x) hP.1 _ hN
  have hev : ∀ z : Fin n → ℂ, (fun i => eval z (linPoly A' i)) = A' *ᵥ z := fun z => by
    ext i
    simp [linPoly, Matrix.mulVec, dotProduct]
  simp only [hev] at hnhds
  have hsub : (fun z => A' *ᵥ z) '' (IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J' ∩
      ({z | linEval u' z ≠ 0} ∩ Φ ⁻¹' (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ D)))) ⊆ F '' (W₀ ∩ D) := by
    rintro _ ⟨z, ⟨hzZ, hzu, hzV, hzW⟩, rfl⟩
    have hzP : z ∈ zeroSet J' \ {x | linEval u' x = 0} := ⟨hzZ, hzu⟩
    refine ⟨A *ᵥ Φ z, hzW, ?_⟩
    show A' *ᵥ Ψ (s (A *ᵥ Φ z)) = A' *ᵥ z
    rw [← hVs (Φ z) ⟨(hΦm hzP).1, hzV⟩ hzW.2.1, hΨΦ z hzP]
  have hpos := Measure.measure_pos_of_mem_nhds (μ := μH[(Module.finrank ℝ (Fin d → ℂ) : ℝ)])
    (Filter.mem_of_superset hnhds hsub)
  rw [SheetOnlyNull.finrank_real_fin_complex] at hpos
  exact hpos.ne' hnull

end ChartChangeSheetNull


open ChartChangeSheetNull in
theorem ChartChangeSheetNull.proof (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) : ChartChangeSheetNull.Statement := by
  intro n d J J' A A' u u' U U' Φ Ψ hJ _ hJ' _ hu _ hA hA' hU hU' hUsub hUsub' hΦ hΨ hΦm hΨm hΨΦ hΦΨ
  set B := {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧ linEval u x ≠ 0 ∧
    ¬ ∃ s', IsSheetAt J' A' (Ψ x) s'} with hBdef
  choose σ Us W hUs hW hσd hWsh hxW using
    fun x : Fin n → ℂ => SheetOnlyNull.exists_sheet_nhds (J := J) (A := A) x
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hpiece : ∀ i, volume ((fun x => A *ᵥ x) '' (B ∩ W i)) = 0 := by
    intro i
    apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro _ ⟨x, ⟨hxB, hxWi⟩, rfl⟩
    obtain ⟨hAx, hsh⟩ := hWsh i x ⟨hxB.1, hxWi⟩
    have hxU : x ∈ U := hUsub ⟨hxB.1, hxB.2.2.1⟩
    have hD := isOpen_dom u (hUs i) (hσd i) hU
    have hsx : σ i (A *ᵥ x) = x := by obtain ⟨_, _, _, _, h, _⟩ := hsh; exact h
    have hAxD : A *ᵥ x ∈ Us i ∩ σ i ⁻¹' (U ∩ {x | linEval u x ≠ 0}) :=
      ⟨hAx, by simp only [Set.mem_preimage, hsx]; exact ⟨hxU, hxB.2.2.1⟩⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD _ hAxD
    refine ⟨Metric.ball (A *ᵥ x) r, Metric.isOpen_ball, Metric.mem_ball_self hr,
      (convex_ball _ r).isPreconnected,
      fun w => (ReciprocityTheory.AnForm.A.jacC (fun v => A' *ᵥ Ψ (σ i v)) w).det,
      (SheetOnlyNull.analyticOnNhd_det_jacC hD (differentiableOn_tau u A' (hσd i) hΨ)).mono hball,
      exists_det_ne_zero h₁ h₂ hJ' hA' hU hU' hUsub' hΦ hΨ hΦm hΨm hΨΦ hΦΨ hxB.2.2.1 hxU hsh
        Metric.isOpen_ball (Metric.mem_ball_self hr), ?_⟩
    rintro _ ⟨⟨x'', ⟨hx''B, hx''W⟩, rfl⟩, -⟩
    by_contra hne
    exact hx''B.2.2.2 (exists_sheet_of_det_ne_zero hU hU' hUsub' hΦ hΨ hΦm hΨm hΨΦ hΦΨ hx''B.2.2.1
      (hUsub ⟨hx''B.1, hx''B.2.2.1⟩) (hWsh i x'' ⟨hx''B.1, hx''W⟩).2 hne)
  have hBnull : volume ((fun x => A *ᵥ x) '' B) = 0 := by
    refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun i _ => hpiece i)
    rintro _ ⟨x, hxB, rfl⟩
    have hx : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxB.2.1⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_biUnion hiT ⟨x, ⟨hxB, hxi⟩, rfl⟩
  refine measure_mono_null ?_ (measure_union_null hBnull (volume_image_zero hJ hA hu))
  rintro _ ⟨x, ⟨hxZ, hxs, hnot⟩, rfl⟩
  by_cases hux : linEval u x = 0
  · exact Or.inr ⟨x, ⟨hxZ, hux⟩, rfl⟩
  · exact Or.inl ⟨x, ⟨hxZ, hxs, hux, fun h => hnot ⟨hux, h⟩⟩, rfl⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLengthLocalizedQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

theorem isNilpotent_of_minimalPrimes_eq_singleton {B : Type*} [CommRing B] [IsNoetherianRing B] {P : Ideal B}
    (hmin : minimalPrimes B = {P}) : IsNilpotent P := by
  have h : sInf (minimalPrimes B) = nilradical B := Ideal.sInf_minimalPrimes
  rw [hmin, sInf_singleton] at h
  rw [h]
  exact IsNoetherianRing.isNilpotent_nilradical B

theorem length_localizedModule_self {B : Type*} [CommRing B] (P : Ideal B) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl B) =
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) :=
  ((IsLocalizedModule.iso P.primeCompl (Algebra.linearMap B (Localization.AtPrime P))).extendScalarsOfIsLocalization
    P.primeCompl (Localization.AtPrime P)).length_eq

theorem LengthLocalizedQuotient.proof (hCut : LengthCutLocalizedModule.Statement.{u, u}) :
    LengthLocalizedQuotient.Statement.{u} := by
  intro B _ _ P _ y hmin hnzd hy Q _ hQ
  have h1 := hCut B P y (Q.comap (Ideal.Quotient.mk (Ideal.span {y}))) B
    (isNilpotent_of_minimalPrimes_eq_singleton hmin) hy hQ (fun s hs m h => by
      rw [smul_eq_mul] at h
      exact (mem_nonZeroDivisors_iff.1 (hnzd s hs)).1 m h)
  have h2 := NumbersDVR.LocalizedQuotLength.proof B (Ideal.span {y}) Q 0
  have hE : (Ideal.span {y} • ⊤ : Submodule B B) = Ideal.span {y} ⊔ Ideal.span {(0 : B)} := by
    rw [Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq, smul_eq_mul, Ideal.mul_top]
  rw [hE, h2, length_localizedModule_self] at h1
  rw [← h1]
  have hb : Ideal.span {algebraMap (B ⧸ Ideal.span {y}) (Localization.AtPrime Q) (Ideal.Quotient.mk _ 0)} = ⊥ := by
    rw [map_zero, map_zero, Ideal.span_singleton_eq_bot]
  exact ((Submodule.quotEquivOfEqBot _ hb).length_eq).symm

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSameOrderBranchesMeet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable def VarBranch.restrictInto {n k : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (c : VarBranch I k q) (ε : ℝ) (hε : 0 < ε)
    (h : ∀ t ∈ Metric.ball (0 : Fin k → ℂ) ε, c.toFun t ∈ zeroSet J) : VarBranch J k q where
  radius := min ε c.radius
  radius_pos := lt_min hε c.radius_pos
  toFun := c.toFun
  differentiableOn := c.differentiableOn.mono (Metric.ball_subset_ball (min_le_right _ _))
  injOn := c.injOn.mono (Metric.ball_subset_ball (min_le_right _ _))
  map_zero := c.map_zero
  mapsTo := fun t ht ↦ h t (Metric.ball_subset_ball (min_le_left _ _) ht)

theorem VarBranch.eventually_mem_zeroSet {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (c : VarBranch I 1 q) (h : ∀ f ∈ J, branchOrder c f = ⊤) :
    ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), c.toFun t ∈ zeroSet J := by
  have key : ∀ f ∈ J, ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), eval (c.toFun t) f = 0 := by
    intro f hf
    have h0 := analyticOrderAt_eq_top.1 (h f hf)
    have ht : Tendsto (fun t : Fin 1 → ℂ ↦ t 0) (𝓝 0) (𝓝 0) := (continuous_apply 0).tendsto' _ _ rfl
    filter_upwards [ht.eventually h0] with t ht
    have : (fun _ : Fin 1 ↦ t 0) = t := funext fun i ↦ by rw [Subsingleton.elim i 0]
    rwa [this] at ht
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian J : J.FG)
  filter_upwards [(s.eventually_all).2 fun g hg ↦ key g (hs ▸ Submodule.subset_span hg)] with t ht f hf
  have hle : Ideal.span (s : Set (MvPolynomial (Fin n) ℂ)) ≤ RingHom.ker (eval (c.toFun t)) :=
    Ideal.span_le.2 fun g hg ↦ ht g hg
  have hf' : f ∈ Ideal.span (s : Set (MvPolynomial (Fin n) ℂ)) := by
    rw [Ideal.span, hs]
    exact hf
  exact hle hf'

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMQuotientUnmixed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

theorem map_mem_associatedPrimes_quotient {B : Type*} [CommRing B] [IsNoetherianRing B] (I p : Ideal B)
    (hp : p ∈ associatedPrimes B (B ⧸ I)) :
    I ≤ p ∧ p.map (Ideal.Quotient.mk I) ∈ associatedPrimes (B ⧸ I) (B ⧸ I) := by
  obtain ⟨hprime, a, rfl⟩ := (isAssociatedPrime_iff (I := p) (M := B ⧸ I)).1 hp
  have hI : I ≤ Submodule.colon (⊥ : Submodule B (B ⧸ I)) {a} := fun b hb => by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hb, zero_mul]
  refine ⟨hI, (isAssociatedPrime_iff).2 ⟨?_, a, ?_⟩⟩
  · exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker])
  · ext c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective, Submodule.mem_colon_singleton]
    constructor
    · rintro ⟨b', hb', hbb'⟩
      rw [← hbb']
      simpa [Submodule.mem_colon_singleton, Algebra.smul_def] using hb'
    · intro h
      exact ⟨b, by simpa [Submodule.mem_colon_singleton, Algebra.smul_def] using h, rfl⟩

theorem CMQuotientUnmixed.proof (hQ : CMParameterQuotient.Statement) (hU : CMRingUnmixed.Statement) :
    CMQuotientUnmixed.Statement := by
  intro B _ _ d x hx hdim p hp
  set I := Ideal.span (Set.range x) with hIdef
  have hCM : IsCohenMacaulayLocalRing (B ⧸ I) := hQ B d x hx hdim
  obtain ⟨hIp, hq⟩ := map_mem_associatedPrimes_quotient I p hp
  obtain ⟨hmin, hdq⟩ := hU (B ⧸ I) _ hq
  have hcomap : (p.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = p := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.2 hIp]
  refine ⟨?_, ?_⟩
  · rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨_, hmin, hcomap⟩
  · rw [← hdq]
    exact (ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIp)).symm

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchNormalisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem BranchNormalisation.proof (h₀ : BranchGermDimOne.Statement) (h₁ : BranchPlace.Statement)
    (h₂ : SameOrderBranchesMeet.Statement) (h₃ : PlaceHasBranch.Statement)
    (h₄ : OrdDeterminesPlace.Statement) (h₅ : CurveResidueDegree.Statement)
    (h₆ : OrdFiniteNonZeroDivisor.Statement) : BranchNormalisation.Statement := by
  intro n I q m c hrad hm hcov hdisj
  have hdim := h₀ n I q m c hm hcov
  refine ⟨hdim, fun f hf ↦ h₆ n I q f hrad hdim fun P ↦ ?_, ?_⟩
  · obtain ⟨b, hb⟩ := h₃ n I q m c hrad hdim hcov hdisj P
    rw [hb f]
    exact hf b
  choose P hP using fun b ↦ h₁ n I q (c b) hrad hdim

  have hcongr : ∀ Q Q' : MaximalSpectrum (curveNormalisation I q), Q = Q' → ∀ f : MvPolynomial (Fin n) ℂ,
      Ring.ord (Localization.AtPrime Q.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime Q.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
      Ring.ord (Localization.AtPrime Q'.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime Q'.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) := by
    rintro Q _ rfl f
    rfl
  have hinj : Function.Injective P := by
    intro b b' hbb
    by_contra hne
    obtain ⟨x, hx, hxq⟩ := h₂ n I q (c b) (c b') hrad hdim fun f ↦
      (hP b f).symm.trans ((hcongr _ _ hbb f).trans (hP b' f))
    exact hxq (hdisj b b' hne hx)
  have hsurj : Function.Surjective P := by
    intro Q
    obtain ⟨b, hb⟩ := h₃ n I q m c hrad hdim hcov hdisj Q
    exact ⟨b, h₄ n I q hrad hdim (P b) Q fun f ↦ (hP b f).trans (hb f).symm⟩
  exact ⟨Equiv.ofBijective P ⟨hinj, hsurj⟩, fun b ↦ ⟨h₅ n I q hrad hdim (P b), hP b⟩⟩

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelProjectionLocallyInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology IndefiniteRowSideFullHecke.ComplexSets

theorem NormalModelProjectionLocallyInjective.proof : NormalModelProjectionLocallyInjective.Statement := by
  intro n J M w hJ hdim hw
  choose a b hbJ hab using M.birational
  set B : MvPolynomial (Fin n) ℂ := ∏ i, b i with hB
  have hBJ : B ∉ J := fun h => by
    have := hJ
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hbJ i hi

  set S : Set (Fin n → ℂ) := ComplexSets.zeroSet J ∩ ComplexSets.zeroSet (Ideal.span {B}) with hS
  have hSfin : S.Finite := CurveProperClosedFinite.proof n J _ hJ hdim
    (fun h => hBJ (h (Ideal.subset_span rfl)))

  choose P hPm hP using M.integral
  set F : Set (Fin n ⊕ Fin M.m → ℂ) := {z | z ∈ zeroSetIn M.ideal ∧ firstCoords z ∈ S} with hF
  have hFfin : F.Finite := by
    have hT : (⋃ x ∈ S, ({x} : Set (Fin n → ℂ)) ×ˢ
        Set.pi Set.univ (fun i => {y : ℂ | ((P i).map (eval x)).IsRoot y})).Finite :=
      hSfin.biUnion fun x _ => (Set.finite_singleton x).prod
        (Set.Finite.pi fun i => Polynomial.finite_setOfPred_isRoot ((hPm i).map (eval x)).ne_zero)
    refine (hT.image fun p => Sum.elim p.1 p.2).subset ?_
    intro z hz
    refine ⟨(firstCoords z, fun i => z (Sum.inr i)), ?_, ?_⟩
    · refine Set.mem_biUnion hz.2 ⟨rfl, fun i _ => ?_⟩
      exact isRoot_map_eval_of_mem_zeroSetIn hz.1 i (P i) (hP i)
    · funext s
      rcases s with j | i <;> rfl
  refine ⟨(F \ {w})ᶜ, (hFfin.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds
    (fun h => h.2 rfl), ?_⟩

  have hnear : ∀ z ∈ zeroSetIn M.ideal ∩ (F \ {w})ᶜ, (∃ i, eval (firstCoords z) (b i) = 0) → z = w := by
    rintro z ⟨hz, hzU⟩ ⟨i, hi⟩
    have hxJ : firstCoords z ∈ ComplexSets.zeroSet J := fun q hq => by
      rw [← M.comap_eq, Ideal.mem_comap] at hq
      have h := hz _ hq
      rw [eval_rename] at h
      exact h
    have hxB : firstCoords z ∈ ComplexSets.zeroSet (Ideal.span {B}) := fun q hq => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hq
      rw [eval_mul, hB, map_prod, Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]
    by_contra hne
    exact hzU ⟨⟨hz, hxJ, hxB⟩, hne⟩
  intro z hz z' hz' hzz
  by_cases hbz : ∀ i, eval (firstCoords z) (b i) ≠ 0
  · have hbz' : ∀ i, eval (firstCoords z') (b i) ≠ 0 := hzz ▸ hbz
    rw [M.eq_graph_of_mem_zeroSetIn a b hab z hz.1 hbz, M.eq_graph_of_mem_zeroSetIn a b hab z' hz'.1 hbz', hzz]
  · simp only [not_forall, not_not] at hbz
    have hbz' : ∃ i, eval (firstCoords z') (b i) = 0 := hzz ▸ hbz
    rw [hnear z hz hbz, hnear z' hz' hbz']

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchInCurveComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem BranchInCurveComponent.proof (h₁ : BranchInComponent.Statement) :
    BranchInCurveComponent.Statement := by
  intro n I q c hdim
  obtain ⟨J, hJ, hmaps⟩ := h₁ n I 1 q c
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : I ≤ J := hJ.1.2
  have hq : q ∈ zeroSet J := c.map_zero ▸ hmaps (Metric.mem_ball_self c.radius_pos)
  refine ⟨J, hJ, ?_, Filter.mem_of_superset (Metric.ball_mem_nhds _ c.radius_pos) hmaps⟩
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J) := inferInstance
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ) := by
    refine (ringKrullDim_quotient_le J).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = e := by
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at h0 hle ⊢
    induction d using WithBot.recBotCoe with
    | bot => simp at h0
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        exfalso
        simp only [not_le.2 (show ((n : ℕ) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) from
          WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n))] at hle
      | coe e => exact ⟨e, rfl⟩
  have he1 : (e : WithBot ℕ∞) ≤ 1 := by
    rw [← LocalDimDomain.proof n e J hJp he q hq, ← hdim]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor (Ideal.map_mono hIJ))
      (Ideal.Quotient.factor_surjective _)
  have he0 : e ≠ 0 := by
    rintro rfl
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.2 (by simpa using he)
    have hJq : J = RingHom.ker (eval q) :=
      (Ideal.Quotient.maximal_of_isField J Ring.KrullDimLE.isField_of_isDomain).eq_of_le
        (RingHom.ker_ne_top _) fun f hf ↦ RingHom.mem_ker.2 (hq f hf)
    have hr := c.radius_pos
    have ht : (fun _ ↦ ((c.radius / 2 : ℝ) : ℂ)) ∈ Metric.ball (0 : Fin 1 → ℂ) c.radius := by
      rw [mem_ball_zero_iff, pi_norm_const, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
      linarith
    have hct : c.toFun (fun _ ↦ ((c.radius / 2 : ℝ) : ℂ)) = c.toFun 0 := by
      rw [c.map_zero]
      funext i
      have hmem : X i - C (q i) ∈ J := by
        rw [hJq, RingHom.mem_ker]
        simp
      simpa [sub_eq_zero] using hmaps ht _ hmem
    have h0 := congrFun (c.injOn ht (Metric.mem_ball_self hr) hct) 0
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at h0
    linarith
  rw [he]
  have : e ≤ 1 := by exact_mod_cast he1
  have : e = 1 := by omega
  subst this
  rfl

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeBranchDimOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem PrimeBranchDimOne.proof : PrimeBranchDimOne.Statement := by
  intro n J q c hJ hloc

  have hq : q ∈ zeroSet J := by
    have := c.mapsTo (Metric.mem_ball_self c.radius_pos)
    rwa [c.map_zero] at this

  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ) := by
    have h1 := ringKrullDim_quotient_le J
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
    simpa using h1
  have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ringKrullDim_nonneg_of_nontrivial
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (e : ℕ) := by
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at hle hnn
    induction d using WithBot.recBotCoe with
    | bot => exact absurd hnn (by simp)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hle
        exact absurd (WithBot.coe_le_coe.mp h3) (by simp)
      | coe e => exact ⟨e, rfl⟩
  have hdim : ringKrullDim (localRingAt J q) = (e : ℕ) := LocalDimDomain.proof n e J hJ he q hq
  have he1 : e ≤ 1 := by
    have h2 : ((e : ℕ) : WithBot ℕ∞) ≤ 1 := hdim ▸ hloc
    exact_mod_cast h2
  rw [he]
  obtain h0 | h1 : e = 0 ∨ e = 1 := by omega
  swap
  · rw [h1]
  exfalso
  subst h0

  have hfield : IsField (MvPolynomial (Fin n) ℂ ⧸ J) := by
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℂ ⧸ J) :=
      (ringKrullDimZero_iff_ringKrullDim_eq_zero).2 (by simpa using he)
    exact Ring.KrullDimLE.isField_of_isDomain
  have hmax : J.IsMaximal := Ideal.Quotient.maximal_of_isField J hfield
  have hJM : J = RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) :=
    hmax.eq_of_le (RingHom.ker_ne_top _) (fun f hf => RingHom.mem_ker.mpr (hq f hf))

  have hZ : ∀ x ∈ zeroSet J, x = q := by
    intro x hx
    funext i
    have hmem : X i - C (q i) ∈ J := by
      rw [hJM, RingHom.mem_ker]
      simp
    have := hx _ hmem
    simp only [map_sub, eval_X, eval_C] at this
    exact sub_eq_zero.mp this

  set r := c.radius
  let v : Fin 1 → ℂ := fun _ => ((r / 2 : ℝ) : ℂ)
  have hv : v ∈ Metric.ball (0 : Fin 1 → ℂ) r := by
    rw [mem_ball_zero_iff, pi_norm_lt_iff c.radius_pos]
    intro i
    simp only [v, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (half_pos c.radius_pos)]
    exact half_lt_self c.radius_pos
  have h0 : (0 : Fin 1 → ℂ) ∈ Metric.ball (0 : Fin 1 → ℂ) r := Metric.mem_ball_self c.radius_pos
  have heq : c.toFun v = c.toFun 0 := by
    rw [hZ _ (c.mapsTo hv), hZ _ (c.mapsTo h0)]
  have := congrFun (c.injOn hv h0 heq) 0
  simp only [v, Pi.zero_apply, Complex.ofReal_eq_zero] at this
  exact (half_pos c.radius_pos).ne' this

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMHeightAddDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

theorem CMHeightAddDim.height_add_ringKrullDim_quotient_of_isPrime (hreg : CMRegularElement.Statement.{u}) :
    ∀ (n : ℕ) (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B], ringKrullDim B = n →
      ∀ (P : Ideal B) [P.IsPrime], (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) = ringKrullDim B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B _ _ hn P hP
  refine le_antisymm (height_add_ringKrullDim_quotient_le P) ?_
  by_cases hmin : P ∈ minimalPrimes B
  · rw [Ideal.height_eq_zero_iff.mpr hmin, ringKrullDim_quotient_eq_of_mem_minimalPrimes hmin]
    simp

  have hfin := minimalPrimes.finite_of_isNoetherianRing (R := B)
  obtain ⟨y, hyP, hyq⟩ : ∃ y ∈ P, ∀ q ∈ minimalPrimes B, y ∉ q := by
    by_contra! h
    have hsub : (P : Set B) ⊆ ⋃ i ∈ (↑hfin.toFinset : Set (Ideal B)), (id i : Set B) := by
      intro z hz
      obtain ⟨q, hq, hzq⟩ := h z hz
      exact Set.mem_biUnion (by simpa using hq) hzq
    obtain ⟨q, hq, hPq⟩ := (Ideal.subset_union_prime (s := hfin.toFinset) (f := id) ⊥ ⊥
      (fun i hi _ _ => ((Set.Finite.mem_toFinset hfin).mp hi).1.1)).mp hsub
    have hq' : q ∈ minimalPrimes B := (Set.Finite.mem_toFinset hfin).mp hq
    have hqP : q ≤ P := hq'.2 ⟨hP, bot_le⟩ hPq
    exact hmin (le_antisymm hPq hqP ▸ hq')
  have hym : y ∈ maximalIdeal B := le_maximalIdeal hP.ne_top hyP
  obtain ⟨hynzd, hCM⟩ := hreg B y hym hyq
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hynzd hym
  obtain ⟨rs', -, -, hd'⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B ⧸ Ideal.span {y})
  have hlt : rs'.length < n := by
    have h1 : ((rs'.length + 1 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
      rw [← hn, ← hdim, hd']
      push_cast
      rfl
    have h2 : rs'.length + 1 = n := by exact_mod_cast h1
    omega
  have hle : Ideal.span {y} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hyP
  have hP' : (P.map (Ideal.Quotient.mk (Ideal.span {y}))).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hle
  have hIH := ih rs'.length hlt (B ⧸ Ideal.span {y}) hd' (P.map (Ideal.Quotient.mk (Ideal.span {y})))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hIH
  have hc := height_map_add_one_le_of_mem_nonZeroDivisors hynzd P hyP
  calc ringKrullDim B = ringKrullDim (B ⧸ Ideal.span {y}) + 1 := hdim.symm
    _ = ((P.map (Ideal.Quotient.mk (Ideal.span {y}))).height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) + 1 := by
        rw [hIH]
    _ = (((P.map (Ideal.Quotient.mk (Ideal.span {y}))).height + 1 : ℕ∞) : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by
        rw [WithBot.coe_add, WithBot.coe_one, add_right_comm]
    _ ≤ (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by
        gcongr

theorem CMHeightAddDim.proof (hreg : CMRegularElement.Statement.{u}) : CMHeightAddDim.Statement.{u} := by
  intro B _ _ J hJ
  obtain ⟨rs, -, -, hd⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hprime := CMHeightAddDim.height_add_ringKrullDim_quotient_of_isPrime hreg rs.length B hd
  refine le_antisymm ?_ ?_
  ·
    have : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
    have : Nonempty (PrimeSpectrum (B ⧸ J)) := inferInstance
    rw [show ringKrullDim (B ⧸ J) = Order.krullDim (PrimeSpectrum (B ⧸ J)) from rfl,
      Order.krullDim_eq_iSup_coheight_of_nonempty, ← WithBot.coe_add, ENat.add_iSup,
      WithBot.coe_iSup (OrderTop.bddAbove _)]
    refine iSup_le fun a => ?_
    obtain ⟨a, ha⟩ := a
    set Q := a.comap (Ideal.Quotient.mk J) with hQdef
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have hJQ : J ≤ Q := fun z hz => by
      rw [hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hz]
      exact Ideal.zero_mem _
    have hmap : a = Q.map (Ideal.Quotient.mk J) :=
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective a).symm
    have hco : (Order.coheight (⟨a, ha⟩ : PrimeSpectrum (B ⧸ J)) : WithBot ℕ∞) = ringKrullDim (B ⧸ Q) := by
      rw [← ringKrullDim_quotient_eq_coheight a,
        ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hmap).trans (DoubleQuot.quotQuotEquivQuotOfLE hJQ))]
    rw [WithBot.coe_add, hco, ← hprime Q]
    gcongr
  ·
    obtain ⟨P, hPmin, hPle⟩ := Set.exists_min_image J.minimalPrimes Ideal.height
      (Ideal.finite_minimalPrimes_of_isNoetherianRing B J) (Set.nonempty_coe_sort.mp (Ideal.nonempty_minimalPrimes hJ))
    have : P.IsPrime := hPmin.1.1
    have hht : J.height = P.height := by
      rw [Ideal.height_eq_inf_minimalPrimes]
      exact le_antisymm (iInf₂_le P hPmin) (le_iInf₂ fun Q hQ => hPle Q hQ)
    rw [hht, ← hprime P]
    gcongr
    exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hPmin.1.2)

end GroundTheory.Heights₂.Heights
end
