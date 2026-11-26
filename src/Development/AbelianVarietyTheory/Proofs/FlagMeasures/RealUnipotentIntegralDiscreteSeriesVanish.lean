module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalSquareEqHilbertSchmidtNormalisedVector
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericLocalTermsSelfDualLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataWithTermSingleOrbitPrimeTo

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentIntegralDiscreteSeriesVanish
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentIntegralDiscreteSeriesVanish
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.RealFibre

private lemma prod_mul_mulSingle_mul {ι : Type*} [Fintype ι] {dec : DecidableEq ι} {G : ι → Type*}
    [∀ i, Group (G i)] (f : ∀ i, G i → ℂ) (a b : ∀ i, G i) (v : ι) (m : G v) :
    ∏ u, f u (a u * Pi.mulSingle v m u * b u) =
      f v (a v * m * b v) * ∏ u ∈ Finset.univ.erase v, f u (a u * b u) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Pi.mulSingle_eq_same]
  congr 1
  refine Finset.prod_congr rfl fun u hu => ?_
  rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hu), mul_one]

theorem integral_phe_eq_zero_of_isKTypeOf : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → LocDec B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → ∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0 := by
  intro B d h hDS hK hLoc hh v Wv hW ν hν x y
  obtain ⟨-, hds, hlow, hfd⟩ := hDS v
  have hU := hds.2.2.1
  obtain ⟨α, hαs, hαc, hαf⟩ :=
    exists_smooth_fix_lowKSub B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) hU (hK v)
  have hq : 1 ≤ rkR (B.I.ε v) := one_le_rkR_of_isIsoC hW
  have hn : 1 ≤ B.I.n := by
    have hle : rkR (B.I.ε v) ≤ B.I.n := by
      unfold rkR
      exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
    omega
  obtain ⟨h0, hc⟩ := rate_lt hn hq (hh v)

  have hF := GlobalTheory.T.unitary_rep_matrixCoeff_integral_eq_zero B.I.n (B.I.ε v) Wv ν hW hν (B.H v) (B.σ v) (d v)
    (h / (8 * Real.sqrt (rkR (B.I.ε v)))) α (B.w v) hU hfd (by exact_mod_cast hc) hlow.1 hαs hαc
    (fun u => hαf (B.w v) hlow.2 u)
    ⟨Real.exp (h / 8), fun g => (hLoc v g).trans (decE_le_exp hq h0 _)⟩ (x.1 v) (y.1 v)

  have hpt : ∀ m : UJ (B.I.ε v), phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) =
      (open Classical in (((∏ u, d u : ℝ) : ℂ) *
        star (∏ u ∈ Finset.univ.erase v, ⟪B.w u, B.σ u (uMat (x.1 u * y.1 u)) (B.w u)⟫_ℂ) *
        B.e (x.2 * y.2))) * star ⟪B.w v, B.σ v (umat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ := by
    intro m
    simp only [phe, ph, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_one]
    rw [prod_mul_mulSingle_mul (fun u g => ⟪B.w u, B.σ u (uMat g) (B.w u)⟫_ℂ) x.1 y.1 v m, star_mul]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  have hconj : ∫ m, star ⟪B.w v, B.σ v (umat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ ∂ν =
      star (∫ m, ⟪B.w v, B.σ v (umat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ ∂ν) := integral_conj
  rw [hconj, hF, star_zero, mul_zero]

end GlobalTheory.RealFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentIntegralDiscreteSeriesVanishStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realUnipotent_integral_discreteSeries_vanish : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → LocDec B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → ∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0 := by
  first | exact @GlobalTheory.RealFibre.integral_phe_eq_zero_of_isKTypeOf | exact GlobalTheory.RealFibre.integral_phe_eq_zero_of_isKTypeOf | (intros; apply GlobalTheory.RealFibre.integral_phe_eq_zero_of_isKTypeOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeInverseDifferentPowMulLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeInverseDifferentPowMulLattice
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.CovMul

open GlobalTheory.HomCovolume GlobalTheory.SnMass.FrameDual

theorem hasDom_ideLat {E : Type} [Field E] [NumberField E] (hE : IsTotallyComplex E)
    (a : FractionalIdeal (𝓞 E)⁰ E) (ha : a ≠ 0) {c : ℝ} (hc : 0 < c) :
    HasDom volume (ideLat a c : Set (InfinitePlace E → ℂ))
      (ENNReal.ofReal ((FractionalIdeal.absNorm a : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E *
        c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  obtain ⟨L₀, hL₀, hcov⟩ := exists_idealLat E hE a ha
  let f : (InfinitePlace E → ℂ) →ₗ[ℝ] (InfinitePlace E → ℂ) := c⁻¹ • LinearMap.id
  have hf : ∀ z, f z = c⁻¹ • z := fun _ => rfl
  have hrank : Module.finrank ℝ (InfinitePlace E → ℂ) = 2 * Fintype.card (InfinitePlace E) := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have hdet : LinearMap.det f = (c ^ (2 * Fintype.card (InfinitePlace E)))⁻¹ := by
    change LinearMap.det (c⁻¹ • LinearMap.id) = _
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, hrank, inv_pow]
  have hpos : 0 < c ^ (2 * Fintype.card (InfinitePlace E)) := pow_pos hc _
  let L : Submodule ℤ (InfinitePlace E → ℂ) := L₀.comap (f.restrictScalars ℤ)
  obtain ⟨_, _, h⟩ := HasCov.of_det f (L := L) (by rw [hdet]; exact (inv_pos.2 hpos).ne')
    (fun _ => Iff.rfl) hcov
  have hL : ∀ z, z ∈ L ↔ z ∈ ideLat a c := by
    intro z
    change f z ∈ L₀ ↔ _
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h w => ?_, fun h w => ?_⟩
    · have h1 := h w
      rw [hf, Pi.smul_apply, Complex.real_smul] at h1
      rw [← h1, Complex.ofReal_inv, mul_inv_cancel_left₀ (by exact_mod_cast hc.ne')]
    · rw [hf, Pi.smul_apply, Complex.real_smul, h w, Complex.ofReal_inv,
        inv_mul_cancel_left₀ (by exact_mod_cast hc.ne')]
  refine ⟨GlobalTheory.latticeDomain L, GlobalTheory.measurableSet_latticeDomain L, fun v => ?_, ?_⟩
  · obtain ⟨z, hz, hu⟩ := GlobalTheory.existsUnique_add_mem_latticeDomain L v
    refine ⟨z, ⟨(hL _).1 z.2, hz⟩, ?_⟩
    rintro l ⟨hl, hlD⟩
    exact congrArg Subtype.val (hu ⟨l, (hL l).2 hl⟩ hlD)
  · rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (GlobalTheory.isAddFundamentalDomain_latticeDomain _ _), measureReal_def, hdet,
      abs_of_pos (inv_pos.2 hpos), div_inv_eq_mul] at h
    have hfin : volume (GlobalTheory.latticeDomain L) ≠ ⊤ :=
      (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, h]

theorem value_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hE : IsTotallyComplex E) (h2 : Module.finrank F E = 2)
    [Algebra.FormallyUnramified (𝓞 F) (𝓞 E)] (t t' : ℕ) :
    ((FractionalIdeal.absNorm (dInv E t * dInv E t') : ℚ) : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E =
      (2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) *
        |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) := by
  have hD : 0 < |(NumberField.discr F : ℝ)| :=
    abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F))
  have hdisc : |(discr E : ℝ)| = |(NumberField.discr F : ℝ)| ^ 2 := by
    have h1 := congrArg (Nat.cast : ℕ → ℝ) (natAbs_discr_sq (F := F) (E := E) h2)
    simpa [Nat.cast_natAbs] using h1
  have hcard : InfinitePlace.nrComplexPlaces E = Fintype.card (InfinitePlace E) := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hexp : |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) =
      ((|(NumberField.discr F : ℝ)| ^ 2)⁻¹ ^ t * (|(NumberField.discr F : ℝ)| ^ 2)⁻¹ ^ t') *
        |(NumberField.discr F : ℝ)| := by
    have e1 : (2 * (t : ℝ)) = ((2 * t : ℕ) : ℝ) := by push_cast; ring
    have e2 : (2 * (t' : ℝ)) = ((2 * t' : ℕ) : ℝ) := by push_cast; ring
    rw [Real.rpow_sub hD, Real.rpow_sub hD, Real.rpow_one, e1, e2, Real.rpow_natCast,
      Real.rpow_natCast, pow_mul, pow_mul, inv_pow, inv_pow]
    field_simp
  rw [map_mul, Rat.cast_mul, absNorm_dInv, absNorm_dInv, vInv_pow E hE, hdisc,
    Real.sqrt_sq hD.le, hcard, hexp]
  ring

theorem hasDom_ideLat_dInv_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * dInv E t') c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  intro F E _ _ _ _ _ σ hσ hU t t' c hc
  have h := hasDom_ideLat hσ.2.1 (dInv E t * dInv E t')
    (mul_ne_zero (dInv_ne_zero t) (dInv_ne_zero t')) hc
  rwa [value_eq hσ.2.1 hσ.2.2.1 t t'] at h

end GlobalTheory.SnMass.VolN.CovMul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeInverseDifferentPowMulLatticeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_inverseDifferentPow_mul_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * dInv E t') c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  first | exact @GlobalTheory.SnMass.VolN.CovMul.hasDom_ideLat_dInv_mul | exact GlobalTheory.SnMass.VolN.CovMul.hasDom_ideLat_dInv_mul | (intros; apply GlobalTheory.SnMass.VolN.CovMul.hasDom_ideLat_dInv_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarMeasureOfSigmaFinite
open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.SnMass.ProdQuot

theorem isHaarMeasure_of_sigmaFinite {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] (ν : Measure H)
    [SigmaFinite ν] [ν.IsMulLeftInvariant] (hν : ν ≠ 0) : ν.IsHaarMeasure := by
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts H) := inferInstance
  have e := Measure.haarMeasure_unique ν K
  rw [e]
  refine Measure.IsHaarMeasure.smul _ (fun hc => hν (by rw [e, hc, zero_smul])) fun hc => hν ?_
  rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets ν]
  refine measure_iUnion_null fun n => ?_
  have h1 := measure_spanningSets_lt_top ν n
  have h2 : ν (spanningSets ν n) = ⊤ * Measure.haarMeasure K (spanningSets ν n) := by
    have := congrArg (fun ρ : Measure H => ρ (spanningSets ν n)) e
    simpa [hc] using this
  by_cases h3 : Measure.haarMeasure K (spanningSets ν n) = 0
  · rw [h2, h3, mul_zero]
  · rw [h2, ENNReal.top_mul h3] at h1
    exact absurd h1 (lt_irrefl _)

theorem exists_cutoff {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (R : Subgroup G) (μ : Measure G)
    [SigmaFinite μ] (hR : IsClosed (R : Set G)) (h0 : μ ≠ 0) (hc : μ (R : Set G)ᶜ = 0)
    (hi : ∀ s ∈ R, μ.map (fun x => s * x) = μ ∧ μ.map (fun x => x * s) = μ) :
    ∃ b : G → ℝ≥0, Measurable b ∧ ∀ g, ∫⁻ s, (b (s * g) : ℝ≥0∞) ∂μ = 1 := by
  have hce : Topology.IsClosedEmbedding R.subtype := hR.isClosedEmbedding_subtypeVal
  have hφ : MeasurableEmbedding R.subtype := hce.measurableEmbedding
  haveI : LocallyCompactSpace R := hce.locallyCompactSpace
  haveI : SecondCountableTopology R := hce.isEmbedding.secondCountableTopology
  have h2 : (μ.comap R.subtype).map R.subtype = μ := by
    rw [hφ.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have : Set.range R.subtype = (R : Set G) := Subtype.range_coe
    rw [this]
    exact hc
  set ν : Measure R := μ.comap R.subtype with hν
  haveI : SigmaFinite ν := SigmaFinite.of_map _ hφ.measurable.aemeasurable (by rwa [h2])
  haveI : ν.IsMulLeftInvariant := ⟨fun g => by
    apply hφ.map_injective
    have hm : Measurable fun x : G => (g : G) * x := measurable_const_mul _
    rw [Measure.map_map hφ.measurable (measurable_const_mul g), h2]
    conv_rhs => rw [← (hi g g.2).1, ← h2, Measure.map_map hm hφ.measurable]
    rfl⟩
  haveI : ν.IsMulRightInvariant := ⟨fun g => by
    apply hφ.map_injective
    have hm : Measurable fun x : G => x * (g : G) := measurable_mul_const _
    rw [Measure.map_map hφ.measurable (measurable_mul_const g), h2]
    conv_rhs => rw [← (hi g g.2).2, ← h2, Measure.map_map hm hφ.measurable]
    rfl⟩
  haveI : ν.IsHaarMeasure := isHaarMeasure_of_sigmaFinite ν fun h => h0 (by rw [← h2, h, Measure.map_zero])
  obtain ⟨b, hb, h1⟩ := GlobalTheory.exists_measurable_lintegral_coset_eq_one G R ν R.subtype hce
  refine ⟨fun x => (b x).toNNReal, hb.ennreal_toNNReal, fun g => ?_⟩
  have hm : Measurable fun s => b (s * g) := hb.comp (measurable_mul_const g)
  have h3 : ∫⁻ s, b (s * g) ∂μ = 1 := by
    rw [← h2, hφ.lintegral_map]
    exact h1 g
  rw [← h3]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_lt_top hm (by rw [h3]; exact ENNReal.one_ne_top)] with s hs
  exact ENNReal.coe_toNNReal hs.ne

theorem map_eq {G : Type} [Group G] [MeasurableSpace G] (μG μ ν : Measure G) {b : G → ℝ≥0} (hb : Measurable b)
    (h1 : ∀ g, ∫⁻ s, (b (s * g) : ℝ≥0∞) ∂μ = 1)
    (hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (s * x) ∂μ ∂ν)
    {F : G → ℂ} (hF : Measurable F) (hi : ∀ᵐ s ∂μ, ∀ x, F (s * x) = F x) :
    ν.map F = (μG.withDensity fun x => b x).map F := by
  have hb' : Measurable fun x => (b x : ℝ≥0∞) := hb.coe_nnreal_ennreal
  ext A hA
  rw [Measure.map_apply hF hA, Measure.map_apply hF hA, withDensity_apply _ (hF hA),
    ← lintegral_indicator (hF hA), hν _ (hb'.indicator (hF hA)), ← lintegral_indicator_one (hF hA)]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ F ⁻¹' A
  · rw [Set.indicator_of_mem hx, Pi.one_apply, ← h1 x]
    refine lintegral_congr_ae ?_
    filter_upwards [hi] with s hs
    rw [Set.indicator_of_mem (by simpa [hs] using hx)]
  · rw [Set.indicator_of_notMem hx, ← lintegral_zero (μ := μ)]
    refine lintegral_congr_ae ?_
    filter_upwards [hi] with s hs
    rw [Set.indicator_of_notMem (by simpa [hs] using hx)]

theorem integral_eq {G : Type} [Group G] [MeasurableSpace G] (μG μ ν : Measure G) {b : G → ℝ≥0} (hb : Measurable b)
    (h1 : ∀ g, ∫⁻ s, (b (s * g) : ℝ≥0∞) ∂μ = 1)
    (hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (s * x) ∂μ ∂ν)
    {F : G → ℂ} (hF : Measurable F) (hi : ∀ᵐ s ∂μ, ∀ x, F (s * x) = F x) :
    ∫ x, F x ∂ν = ∫ x, (b x : ℂ) * F x ∂μG ∧ (Integrable F ν ↔ Integrable (fun x => (b x : ℂ) * F x) μG) := by
  have h := map_eq μG μ ν hb h1 hν hF hi
  have e : (fun x => (b x : ℂ) * F x) = fun x => b x • F x := by
    ext x
    simp [NNReal.smul_def]
  have hid : ∀ ρ : Measure ℂ, AEStronglyMeasurable (fun z : ℂ => z) ρ := fun ρ => continuous_id.aestronglyMeasurable
  rw [e]
  constructor
  · rw [← integral_withDensity_eq_integral_smul hb, ← integral_map hF.aemeasurable (hid _),
      ← integral_map hF.aemeasurable (hid _), h]
  · rw [← integrable_withDensity_iff_integrable_smul hb]
    have h2 := integrable_map_measure (μ := ν) (hid _) hF.aemeasurable
    have h3 := integrable_map_measure (μ := μG.withDensity fun x => b x) (hid _) hF.aemeasurable
    rw [h] at h2
    exact h2.symm.trans h3

end GlobalTheory.SnMass.ProdQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLieEUnitaryGroupIffOfInvolutive
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLieEUnitaryGroupIffOfInvolutive
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.TubeLie


open scoped Matrix.Norms.Operator in
theorem skew_of_mem_lieOf {N : ℕ} (H X : Matrix (Fin N) (Fin N) ℂ) (h : X ∈ lieOf (UH H)) :
    Xᴴ * H + H * X = 0 := by
  have hc : ∀ t : ℝ, (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp ((t : ℂ) • Xᴴ) := by
    intro t
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  have key : ∀ t : ℝ, H * NormedSpace.exp (t • X) = NormedSpace.exp (t • -Xᴴ) * H := by
    intro t
    have ht : (NormedSpace.exp ((t : ℂ) • X))ᴴ * H * NormedSpace.exp ((t : ℂ) • X) = H := h t
    rw [hc t] at ht
    have e1 : NormedSpace.exp (-((t : ℂ) • Xᴴ)) * NormedSpace.exp ((t : ℂ) • Xᴴ) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.refl ((t : ℂ) • Xᴴ)).neg_left, neg_add_cancel,
        NormedSpace.exp_zero]
    have e2 : H * NormedSpace.exp ((t : ℂ) • X) = NormedSpace.exp (-((t : ℂ) • Xᴴ)) * H := by
      calc H * NormedSpace.exp ((t : ℂ) • X)
          = (NormedSpace.exp (-((t : ℂ) • Xᴴ)) * NormedSpace.exp ((t : ℂ) • Xᴴ)) * H *
              NormedSpace.exp ((t : ℂ) • X) := by rw [e1, one_mul]
        _ = NormedSpace.exp (-((t : ℂ) • Xᴴ)) *
              (NormedSpace.exp ((t : ℂ) • Xᴴ) * H * NormedSpace.exp ((t : ℂ) • X)) := by
            simp only [mul_assoc]
        _ = NormedSpace.exp (-((t : ℂ) • Xᴴ)) * H := by rw [ht]
    rw [← smul_neg, Complex.coe_smul, Complex.coe_smul] at e2
    exact e2
  have d1 : HasDerivAt (fun t : ℝ => H * NormedSpace.exp (t • X))
      (H * (NormedSpace.exp ((0 : ℝ) • X) * X)) 0 :=
    (hasDerivAt_exp_smul_const X (0 : ℝ)).const_mul H
  have d2 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • -Xᴴ) * H)
      (NormedSpace.exp ((0 : ℝ) • -Xᴴ) * -Xᴴ * H) 0 :=
    (hasDerivAt_exp_smul_const (-Xᴴ) (0 : ℝ)).mul_const H
  rw [show (fun t : ℝ => H * NormedSpace.exp (t • X)) =
      (fun t : ℝ => NormedSpace.exp (t • -Xᴴ) * H) from funext key] at d1
  have hu := d1.unique d2
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hu
  rw [hu, neg_mul, add_neg_cancel]

private theorem conjTranspose_exp_mul_mul_exp_eq_of_skew {N : ℕ} (H X : Matrix (Fin N) (Fin N) ℂ) (h : Xᴴ * H + H * X = 0)
    (t : ℝ) : (NormedSpace.exp ((t : ℂ) • X))ᴴ * H * NormedSpace.exp ((t : ℂ) • X) = H := by
  have hx : H * X = -(Xᴴ * H) := by
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact h
  have hs : SemiconjBy H ((t : ℂ) • X) (-((t : ℂ) • Xᴴ)) := by
    unfold SemiconjBy
    rw [mul_smul_comm, hx, smul_neg, neg_mul, smul_mul_assoc]
  have hc : (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp ((t : ℂ) • Xᴴ) := by
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  let _ : NormedRing (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℚ (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedAlgebra
  let _ : NormedAlgebra ℂ (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedAlgebra
  have _ : CompleteSpace (Matrix (Fin N) (Fin N) ℂ) := FiniteDimensional.complete ℂ _
  have := hs.exp_neg_mul_mul_exp_eq_self
  rw [neg_neg] at this
  rw [hc]
  exact this

theorem mem_lieOf_of_skew {N : ℕ} (H X : Matrix (Fin N) (Fin N) ℂ) (h : Xᴴ * H + H * X = 0) :
    X ∈ lieOf (UH H) := by
  intro t
  exact conjTranspose_exp_mul_mul_exp_eq_of_skew H X h t

private theorem unrealify_equiv_symm_realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, realifyFun]

private theorem equiv_symm_realifyFun_unrealify_eq {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    (WithLp.equiv 2 _).symm (realifyFun (unrealify x)) = x := by
  ext ⟨i, j, b⟩
  cases b <;> simp [unrealify, realifyFun]

private theorem unrealify_map_add {m : ℕ} (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

private theorem unrealify_map_smul {m : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (c • x) = (c : ℂ) • unrealify x := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

private theorem unrealify_map_zero {m : ℕ} :
    unrealify (0 : EuclideanSpace ℝ (Fin m × Fin m × Bool)) = 0 := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

theorem mem_lieE_UH (m : ℕ) (H : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    x ∈ lieE (UH H) ↔ (unrealify x)ᴴ * H + H * unrealify x = 0 := by
  have hL : lieOf (UH H) = {X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * H + H * X = 0} := by
    ext X
    exact ⟨fun h => skew_of_mem_lieOf H X h, fun h => mem_lieOf_of_skew H X h⟩
  constructor
  · intro hx
    unfold lieE at hx
    rw [hL] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨X, hX, rfl⟩ := hy
      rw [unrealify_equiv_symm_realifyFun]
      exact hX
    | zero => simp [unrealify_map_zero]
    | add y z _ _ hy hz =>
      rw [unrealify_map_add, Matrix.conjTranspose_add, add_mul, mul_add]
      calc (unrealify y)ᴴ * H + (unrealify z)ᴴ * H + (H * unrealify y + H * unrealify z)
          = ((unrealify y)ᴴ * H + H * unrealify y) + ((unrealify z)ᴴ * H + H * unrealify z) := by
            abel
        _ = 0 := by rw [hy, hz, add_zero]
    | smul c y _ hy =>
      rw [unrealify_map_smul, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
        smul_mul_assoc, mul_smul_comm, ← smul_add, hy, smul_zero]
  · intro hx
    unfold lieE
    apply Submodule.subset_span
    refine ⟨unrealify x, ?_, equiv_symm_realifyFun_unrealify_eq x⟩
    rw [hL]
    exact hx

theorem mem_lieE_UH_of_sq : ∀ (m : ℕ) (H : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)),
    H * H = 1 → (x ∈ lieE (UH H) ↔ (unrealify x)ᴴ * H + H * unrealify x = 0) := by
  intro m H x _
  exact mem_lieE_UH m H x

end GlobalTheory.TubeLie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLieEUnitaryGroupIffOfInvolutiveStatement
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_lieE_unitaryGroup_iff_of_involutive : ∀ (m : ℕ) (H : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)), H * H = 1 → (x ∈ lieE (UH H) ↔ (unrealify x)ᴴ * H + H * unrealify x = 0) := by
  first | exact @GlobalTheory.TubeLie.mem_lieE_UH_of_sq | exact GlobalTheory.TubeLie.mem_lieE_UH_of_sq | (intros; apply GlobalTheory.TubeLie.mem_lieE_UH_of_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRootHaar
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.ThA.OrbSq
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Dx2
open scoped ENNReal

namespace GlobalTheory.Amp.RootQuot

variable {k r : ℕ}

theorem exists_setting (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') : ∃ Bs : B.RealPlaceData k r ℂ ℂ, Bs.z = z ∧ Bs.z' = z' := by
  obtain ⟨μG, hG⟩ := unitary_group_haar_exists k r
  obtain ⟨μN, hN⟩ := unipotent_haar_exists k r
  obtain ⟨μW, hW⟩ := weyl_haar_exists k r z hz hT
  obtain ⟨μW', hW'⟩ := weyl_haar_exists k r z' hz' hT'
  obtain ⟨μsec, hs⟩ := SettingConstruction.sectionExists k r z z' hk hz hz' hT hT'
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := character_exists_alt
  exact ⟨⟨z, z', fun _ => 1, fun _ => 1, μG, μW, μN, μW', μsec, χ, hk, hz, hz', hT, hT',
    ⟨rfl, fun _ _ _ _ => rfl⟩, ⟨rfl, fun _ _ _ _ => rfl⟩, fun _ _ _ => rfl, fun _ _ _ => rfl,
    continuousOn_const, continuousOn_const, hG, hW, hN, hW', hs, hχ1, hχ2, hχ3⟩, rfl, rfl⟩

theorem perm_invol (p : C.LPt) (n : ℕ) (h : D.ptSize p = n) (a : Fin n) :
    (h ▸ D.ptPerm p : Equiv.Perm (Fin n)) ((h ▸ D.ptPerm p : Equiv.Perm (Fin n)) a) = a := by
  subst h
  exact Dx1.ptPerm_invol p a

theorem zhat_inv_mono {z z' : Fin (2 * r + k + 1) → ℂ} (p : Point ℂ (r + 1)) {g : Mat k r} (hg : g ∈ GG k r)
    (hZ : ZhatO k r z z' g = ptMat p) :
    ∃ d : Fin (r + 1) → ℂ, (∀ a, d a ≠ 0) ∧ Zhat k r z' z g⁻¹ = C2.monoP (permOf p) d := by
  obtain ⟨hw, hd⟩ := VV.ptMatN_monoP' (sw p.1) (r + 1) (isLocPt_sw p).2 (isLocPt_sw p).1
  rw [ptMat_sw, ← hZ] at hw
  generalize (Eq.rec (motive := fun x _ => Fin x → ℂ) (D.ptDiag (sw p.1)) (isLocPt_sw p).2) = d at hw hd
  have hi : ∀ a, permOf p (permOf p a) = a := perm_invol _ _ _
  refine ⟨fun a => star ((-1) ^ (r - (permOf p a).val) * d (permOf p a)), fun a => ?_, ?_⟩
  · exact star_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hd _))
  · rw [NfMid.zhat_inv z z' hg]
    ext i a
    have h1 : (-1 : ℂ) ^ (r - i.val) * Zhat k r z z' g a i = if a = permOf p i then d i else 0 :=
      congrFun (congrFun hw a) i
    have h2 : Zhat k r z z' g a i = (-1 : ℂ) ^ (r - i.val) * if a = permOf p i then d i else 0 := by
      rw [← h1, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [conjTranspose_apply, h2]
    show _ = if i = permOf p a then _ else 0
    by_cases h : a = permOf p i
    · subst h
      simp [hi]
    · rw [if_neg h, if_neg (fun e => h (by rw [e, hi])), mul_zero, star_zero]

theorem gf_inv (z z' : Fin (2 * r + k + 1) → ℂ) {g : Mat k r} (hg : g ∈ GG k r) :
    Gf k r z' z g⁻¹ = Gf k r z z' g := by
  unfold Gf
  simp only [Complex.normSq_eq_norm_sq, NfMid.dmin_inv z z' hg]
  ring

theorem exists_root_haar (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (p : Point ℂ (r + 1)) {g : Mat k r} (hg : g ∈ GG k r)
    (hZ : ZhatO k r z z' g = ptMat p) (hG0 : Gf k r z z' g ≠ 0) :
    ∃ μ : Measure (Mt k r), IsHaarOn (Rset k r g) μ ∧ IsUnimod (Rset k r g) μ ∧
      μ.map (rootCoords k r z' p) = volume := by
  obtain ⟨Bs, rfl, rfl⟩ := exists_setting hk hz' hz hT' hT
  obtain ⟨d, hd, hZw⟩ := zhat_inv_mono p hg hZ
  have hu := isUnit_det_of_mem_GG hg
  have hgi : g⁻¹ ∈ B.GV k r := isClosedSub_GG.2.2.2.2 _ hg
  have hpos : 0 < Gf k r Bs.z Bs.z' g⁻¹ := by
    rw [gf_inv _ _ hg]
    exact lt_of_le_of_ne (gNonneg k r _ _ hz hz' hT hT' g hg) hG0.symm
  have hG : Rad.Good Bs g⁻¹ (permOf p) d :=
    ⟨Rad.exists_rho Bs hgi hpos hd hZw, Rad.u_inj Bs hgi hpos hd hZw, fun ρ hρ => Rad.u_lstg Bs hgi hpos hd hZw hρ⟩
  have hm := Rad.rhoF_meas Bs hgi hd hG
  have hH := Rad.haar_good Bs hgi hd hG
  have hI := haar_measure_inversion k r _ _ (OrbJ.closedR (Matrix.isUnit_nonsing_inv_det g hu)) hH
  have hset : C6.Rset g⁻¹ = Rset k r g := by
    ext x
    simp only [C6.Rset, Formalism.MainNotions.S.Rset, Set.mem_setOf_eq, Matrix.nonsing_inv_nonsing_inv _ hu]
  rw [hset] at hH
  have hmu : D.muR Bs g⁻¹ (permOf p) = (volume : Measure (C2.Lstidx (permOf p) → ℂ)).map
      (fun x => (Matrix.of.symm (Rad.rhoF Bs g⁻¹ (permOf p) x) : Mt k r)) := rfl
  have hphi : ∀ x : Mt k r, Rad.phi0 Bs (permOf p) x = cjE (rootEquiv p) (rootCoords k r Bs.z p x) := by
    intro x
    funext q
    rw [cjE_apply]
    have hq : q.1.2.val < r := by have h1 := q.2.1; have h2 := q.1.1.isLt; rw [Fin.lt_def] at h1; omega
    show star (C2.uMap k r Bs.z (Matrix.of x) q.1.2 q.1.1) = star (flagMat k r Bs.z (Matrix.of x) q.1.2 q.1.1)
    unfold C2.uMap flagMat
    rw [dite_eq_left hq, dite_eq_left hq]
    exact congrArg star (DF.herm_es _ _)
  have hrc : rootCoords k r Bs.z p = (cjE (rootEquiv p)).symm ∘ Rad.phi0 Bs (permOf p) := by
    funext x; simp [hphi x]
  have hrm : Measurable (rootCoords k r Bs.z p) := by
    rw [hrc]; exact (cjE (rootEquiv p)).symm.measurable.comp (Rad.continuous_radial_phi Bs).measurable
  refine ⟨D.muR Bs g⁻¹ (permOf p), ⟨OrbJ.sigmaF hH, hH.ne_zero, hH.conc, hH.left⟩, ⟨hH.right, hI⟩, ?_⟩
  rw [hmu, Measure.map_map hrm hm]
  have : rootCoords k r Bs.z p ∘ (fun x => (Matrix.of.symm (Rad.rhoF Bs g⁻¹ (permOf p) x) : Mt k r)) =
      (cjE (rootEquiv p)).symm := by
    funext x
    rw [hrc]
    simp only [Function.comp]
    rw [Rad.coordMap_hermRep_leftInverse Bs hgi hd hG]
  rw [this, (cjE_mp _).symm.map_eq]

theorem scale_pos (D : D7) : 0 < 2 * D.host.ka / gg D / (2 * Real.pi) := by
  have h1 : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
    have h : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
      abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
    have := Real.rpow_pos_of_pos h ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ))
    positivity
  have h2 : 0 < gg D := by
    unfold gg
    have a := (D.host.g_prime 0).pos
    have b := (D.host.g_prime 1).pos
    positivity
  positivity

theorem exists_rMeas : ∀ (D : D7) (W : LocW D.R.k D.R.rS) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)), inWb D.R.k D.R.rS W.z → inWb D.R.k D.R.rS W.z' → 0 < Tz D.R.k D.R.rS W.z → 0 < Tz D.R.k D.R.rS W.z' → IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG → RelPt D W.z W.z' γ p → ∃ ν, RMeas D W γ 1 ν := by
  rintro D W γ p hz hz' hT hT' hG ⟨hγ, hC, hG0⟩
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨n, hn, n', hn', g, hg, rfl, hZ⟩ := GlobalTheory.CellRep.cell_rep _ _ W.z W.z' γ p hz hz' hT hT' hγ hC
  rw [gInv _ _ W.z W.z' hz hz' n ⟨1, (isClosedSub_UWset W.z).2.2.1, n, hn, (Matrix.one_mul _).symm⟩
    n' ⟨1, (isClosedSub_UWset W.z').2.2.1, n', hn', (Matrix.one_mul _).symm⟩] at hG0
  obtain ⟨μ, h1, h2, h3⟩ := exists_root_haar hk hz hz' hT hT' p hg hZ hG0
  obtain ⟨n1, -, -, -, n5⟩ := isClosedSub_Nset (k := D.R.k) (r := D.R.rS)
  obtain ⟨d1, d2⟩ := StabMeas.haar_smul h1 h2 (pow_pos (scale_pos D) (rootPat p).card)
  obtain ⟨e1, e2⟩ := StabMeas.haar_conj (isUnit_det_of_mem_GG (n1 (n5 _ hn'))) (StabMeas.conj_mem_Rset hn hn' g) d1 d2
  obtain ⟨ν, hν⟩ := GlobalTheory.SgQuot.exists_isQuotMeas _ _ _ W.μG _ (StabMeas.isClosedSub_Rset hγ) hG e1 e2
  refine ⟨ν, p, _, ⟨n, hn, n', hn', g, rfl, hZ, _, d1.2.2.1, ?_, rfl⟩, ?_⟩
  · rw [Measure.map_smul, h3]
    apply Continuous.aemeasurable
    refine continuous_pi fun q => ?_
    unfold rootCoords flagMat
    split_ifs <;> first | exact continuous_const | fun_prop
  · have e : (fun x : Mt D.R.k D.R.rS => fun i j => (n'⁻¹ * Matrix.of x * n') i j) = conjM n'⁻¹ := by
      funext x
      unfold conjM
      rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_GG (n1 hn'))]
    rw [ENNReal.ofReal_one, one_smul, e]
    exact hν

end GlobalTheory.Amp.RootQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianOrbitUniqueLatticeIntegralFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianOrbitUniqueLatticeIntegralFrames
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GoodFrames

theorem Mof_eq_span {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ} (S : Frames L r k) (hth : S.th = 1)
    (g g' : Fin (r + 1) → S.V) :
    S.Mof g g' = Submodule.span L.O (Set.range (Sum.elim g g')) := by
  have hth' : algebraMap F E S.th⁻¹ = 1 := by rw [hth, inv_one, map_one]
  apply le_antisymm
  · rw [Frames.Mof]
    apply Submodule.span_le.2
    rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact Submodule.subset_span ⟨Sum.inl j, rfl⟩
    · simp only [hth', one_smul, SetLike.mem_coe]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
        (Submodule.subset_span ⟨Sum.inl j, rfl⟩)
  · apply Submodule.span_le.2
    rintro _ ⟨j | j, rfl⟩
    · exact Submodule.subset_span (Or.inl ⟨j, rfl⟩)
    · have h1 : g' j = algebraMap F E S.th⁻¹ • (g' j - g j) + g j := by rw [hth']; simp
      simp only [Sum.elim_inr, SetLike.mem_coe]
      rw [h1]
      exact Submodule.add_mem _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩))
        (Submodule.subset_span (Or.inl ⟨j, rfl⟩))

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → P.PrimeTo → ∀ (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → A a b = 0 ∧ A' a b = 0) → (∀ a, A a a = 1 ∧ A' a a = 1) → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O) → ∀ (f f' : Fin (r + 1) → V), (∀ j, f j = ∑ i, A i j • P.A.f i) → (∀ j, f' j = ∑ i, A' i j • P.B.f i) → ∀ d0 : LocNG.Datum P, (∃ t, LocNG.IsTermOver P d0 t) → ∀ d : LocNG.Datum P, (LocNG.Datum.Rel d0 d → ∃! Λ : Submodule M.L.O V, LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) ∧ ((∃ t, LocNG.IsTermOver P d t) → LocNG.Datum.Rel d0 d) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hdim hrel hpt A A' hAt hAd hAi f f' hf hf' d0 hd0 d
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hdim hrel
  have hsplit : M.split = none := hpt.1
  obtain ⟨hgg, hvG, -⟩ := (GlobalTheory.HL.CoordHeight.height_eq M hM H r k P S c).2.2 hpt
  have ha : S.a = 0 := by simp [GlobalTheory.HL.Frames.a, GlobalTheory.HL.Frames.vth, hgg, hvG]
  have hth : S.th = 1 := by simp [GlobalTheory.HL.Frames.th, hgg]
  obtain ⟨-, -, -, -, hD, -⟩ := GlobalTheory.FrameBasic.main M.L r k S
  have hDu : ∀ l, S.D l ≠ 0 → S.D l ∈ M.L.O ∧ ∃ y ∈ M.L.O, S.D l * y = 1 := by
    intro l hl
    by_cases h0 : l = 0
    · have e : S.D l = 1 := by
        subst h0
        unfold GlobalTheory.HL.Frames.D GlobalTheory.HL.lead
        exact Matrix.det_isEmpty (n := Fin 0)
      rw [e]
      exact ⟨M.L.O.one_mem, 1, M.L.O.one_mem, mul_one 1⟩
    · have hmem : (l : ℕ) ∈ P.ends := by
        unfold LocNG.FPair.ends
        simp only [Finset.mem_filter, Finset.mem_range]
        rw [GlobalTheory.HL.CoordHeight.Dm_eq c]
        exact ⟨l.2, Nat.one_le_iff_ne_zero.mpr fun h => h0 (Fin.ext h), hD l hl⟩
      have := hpt.2.2 _ hmem
      rwa [GlobalTheory.HL.CoordHeight.Dm_eq c] at this
  have hTC := GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c
  have hDT := GlobalTheory.HL.CoordDatum.transport M hM H r k P S c
  have hMT := GlobalTheory.HL.CoordMass.transport M hM H r k P S c
  have hNT := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c

  have hfc : ∀ j, c.e (f j) = ∑ i, A i j • S.f i := by
    intro j; rw [hf j, map_sum]; simp [c.f_eq]
  have hfc' : ∀ j, c.e (f' j) = ∑ i, A' i j • S.f' i := by
    intro j; rw [hf' j, map_sum]; simp [c.f'_eq]
  have hfN : ∃ n ∈ P.A.N, f = fun b => n (P.A.f b) := by
    obtain ⟨n, hn, hne⟩ := ((GlobalTheory.HL.FrameOnto.unipotent_onto M.L r k S).2.2 A
      ⟨fun i j h => (hAt i j h).1, fun i => (hAd i).1⟩).1
    refine ⟨c.grp.symm n, (hNT.2.1 _).2 (by simpa using hn), ?_⟩
    funext b
    apply c.e.injective
    change c.e (f b) = c.e (c.e.symm (n (c.e (P.A.f b))))
    rw [LinearEquiv.apply_symm_apply, ← c.f_eq, hne b, hfc b]
  have hf'N : ∃ n ∈ P.B.N, f' = fun b => n (P.B.f b) := by
    obtain ⟨n, hn, hne⟩ := ((GlobalTheory.HL.FrameOnto.unipotent_onto M.L r k S).2.2 A'
      ⟨fun i j h => (hAt i j h).2, fun i => (hAd i).2⟩).2
    refine ⟨c.grp.symm n, (hNT.2.2.1 _).2 (by simpa using hn), ?_⟩
    funext b
    apply c.e.injective
    change c.e (f' b) = c.e (c.e.symm (n (c.e (P.B.f b))))
    rw [LinearEquiv.apply_symm_apply, ← c.f'_eq, hne b, hfc' b]

  set fc : Fin (r + 1) → S.V := fun b => c.e (f b) with hfcdef
  set fc' : Fin (r + 1) → S.V := fun b => c.e (f' b) with hfc'def
  have hAi1 : GlobalTheory.HL.IsIntM M.L A := fun i j => (hAi i j).1
  have hAi2 : GlobalTheory.HL.IsIntM M.L A' := fun i j => (hAi i j).2
  have hcls : (fc, fc') ∈ S.frameCls S.f S.f' :=
    GlobalTheory.HL.GoodClass.mem_cls S hgg S.f S.f' (fc, fc')
      ⟨fun i j h => (hAt i j h).1, fun i => (hAd i).1⟩ ⟨fun i j h => (hAt i j h).2, fun i => (hAd i).2⟩
      hAi1 hAi2 hfc hfc'
  have hMof : S.Mof fc fc' = S.Mof S.f S.f' :=
    ((GlobalTheory.HL.FrameClass.frame_classes M.L r k S S.f S.f').2.1 _ hcls).2
  have hMM : ∀ Λ : Submodule M.L.O V,
      H.MMfam (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) = Sum.elim f f' := by
    intro Λ; simp [HermSp.MMfam, hsplit]
  have hmemlat : ∀ (Λ : Submodule M.L.O V) (v : V), c.e v ∈ c.lat Λ ↔ v ∈ Λ := by
    intro Λ v
    constructor
    · rintro ⟨w, hw, e⟩
      have : w = v := c.e.injective e
      rwa [← this]
    · intro hv; exact ⟨v, hv, rfl⟩
  have hlatspan : c.lat (Submodule.span M.L.O (Set.range (Sum.elim f f'))) =
      Submodule.span M.L.O (Set.range (Sum.elim fc fc')) := by
    rw [Coord.lat, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext x
    cases x <;> rfl
  have hst : ∀ g : Fin (r + 1) → S.V, S.spanTo g (r + 1) = Submodule.span E (Set.range g) := by
    intro g
    have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by ext i; simpa using i.2
    rw [Frames.spanTo, hs, Set.image_univ]
  have hME : ∀ v : V, c.e v ∈ S.ME ↔ v ∈ Submodule.span E (Set.range (Sum.elim f f')) := by
    have e1 : S.ME = Submodule.span E (Set.range (Sum.elim fc fc')) := by
      rw [Frames.ME, hst, hst, ← Submodule.span_union, ← Set.Sum.elim_range,
        ← Submodule.span_span_of_tower M.L.O E (Set.range (Sum.elim S.f S.f')),
        ← Submodule.span_span_of_tower M.L.O E (Set.range (Sum.elim fc fc')),
        ← Mof_eq_span S hth, ← Mof_eq_span S hth, hMof]
    have e2 : Submodule.span E (Set.range (Sum.elim fc fc')) =
        (Submodule.span E (Set.range (Sum.elim f f'))).map (c.e : V →ₗ[E] S.V) := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      funext x
      cases x <;> rfl
    intro v
    rw [e1, e2, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

  have hKM : ∀ Λ : Submodule M.L.O V,
      ((∀ i, H.MMfam (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) i ∈ Λ) ∧
        ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) ↔
      S.sat (c.lat Λ) = S.Mof fc fc' := by
    intro Λ
    rw [Mof_eq_span S hth, ← hlatspan]
    simp only [LocNG.BBne, hMM, not_exists, not_and, not_not]
    constructor
    · rintro ⟨hin, hbb⟩
      ext x
      obtain ⟨v, rfl⟩ := c.e.surjective x
      rw [Frames.sat, Submodule.mem_inf, Submodule.restrictScalars_mem, hmemlat, hmemlat, hME]
      constructor
      · rintro ⟨h1, h2⟩; exact hbb v h1 h2
      · intro hv
        refine ⟨(Submodule.span_le.2 ?_) hv, ?_⟩
        · rintro _ ⟨i, rfl⟩; exact hin i
        · exact Submodule.span_le_restrictScalars M.L.O E _ hv
    · intro hsat
      have hsub : ∀ v, v ∈ Submodule.span M.L.O (Set.range (Sum.elim f f')) ↔ v ∈ Λ ∧
          v ∈ Submodule.span E (Set.range (Sum.elim f f')) := by
        intro v
        rw [← hmemlat, ← hsat, Frames.sat, Submodule.mem_inf, Submodule.restrictScalars_mem, hmemlat, hME]
      refine ⟨fun i => ((hsub _).1 (Submodule.subset_span ⟨i, rfl⟩)).1, fun v h1 h2 => (hsub v).2 ⟨h1, h2⟩⟩

  have hloc := GlobalTheory.T.generic_local_terms_selfDual_lattices M hM H r k P hdim hrel f f' hfN hf'N
  have hmov := GlobalTheory.T.unitaryComplement_moves_hermitianTerms M hM H r k P hdim hrel f f' hfN hf'N

  have hex0 : ∃ Λ : Submodule M.L.O V,
      LocNG.IsTermOver P d0 (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧
        ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) := by
    obtain ⟨t0, ht0⟩ := hd0
    have hT0 := (hTC.1 d0 t0 ht0).1
    obtain ⟨s, hs, hsFr⟩ := (GlobalTheory.HL.GoodClass.one_class M.L r k S hgg hDu).2.2 _
      ((GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ hT0).2.2.2.2.2.2.1)
    have hact := GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S (c.dat d0) _ hT0 s⁻¹ (S.St.inv_mem hs)
    have hT1 : S.IsTerm (c.dat d0) (s⁻¹ • c.lat t0.abelian₂) := hact.1
    have hFr1 : S.Fr (c.dat d0) (s⁻¹ • c.lat t0.abelian₂) = S.frameCls S.f S.f' := by
      rw [hact.2.2.2.2.1, hsFr, smul_smul, inv_mul_cancel, one_smul]
    have hBB1 := (GlobalTheory.HL.UnimodTerm.term_unique M.L r k S _ _ hT1 ha).1
    have hM1 : S.M (c.dat d0) (s⁻¹ • c.lat t0.abelian₂) = S.Mof fc fc' := by
      rw [hMof]
      have hmem : (S.fr (c.dat d0) (s⁻¹ • c.lat t0.abelian₂), S.fr' (c.dat d0) (s⁻¹ • c.lat t0.abelian₂)) ∈
          S.frameCls S.f S.f' := by
        rw [← hFr1]; exact GlobalTheory.HL.FrameClass.refl_mem S _ _
      exact ((GlobalTheory.HL.FrameClass.frame_classes M.L r k S S.f S.f').2.1 _ hmem).2
    obtain ⟨⟨Lam1, g1, g1', T1, T1'⟩, ht1, ht1l⟩ := hTC.2.1 d0 _ hT1
    obtain rfl : T1 = P.A.T := ht1.1
    obtain rfl : T1' = P.B.T := ht1.2.1
    have hsat1 : S.sat (c.lat Lam1) = S.Mof fc fc' := by
      rw [ht1l, ← hBB1, hM1]
    obtain ⟨hin, hbb⟩ := (hKM Lam1).2 hsat1
    have hbb1 : ¬ LocNG.BBne (H := H) (⟨Lam1, g1, g1', P.A.T, P.B.T⟩ : Term V M r) := fun h =>
      ((hTC.1 d0 _ ht1).2.2.1 h) (by rw [ht1l]; exact hBB1)
    obtain ⟨n1, hn1, hn1f, -⟩ := ht1.2.2.1
    obtain ⟨n1', hn1', hn1f', -⟩ := ht1.2.2.2.1
    obtain ⟨hSD, hFG, -, -⟩ := (GlobalTheory.T.generic_local_terms_selfDual_lattices M hM H r k P hdim hrel g1 g1' ⟨n1, hn1, hn1f⟩
      ⟨n1', hn1', hn1f'⟩ Lam1).1.2 ⟨d0, ht1, hbb1⟩
    obtain ⟨d1, hd1, hbb1'⟩ := (hloc Lam1).1.1 ⟨hSD, hFG, hin, hbb⟩
    have hd10 : d1 = d0 := by
      have h2 := (hTC.1 d1 _ hd1).1
      simp only at h2
      rw [ht1l] at h2
      exact hDT.1 ((GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ hT1).2.2.2.2.2.2.2 _ h2)
    subst hd10
    exact ⟨Lam1, hd1, hbb1'⟩

  have huniq : ∀ (d : LocNG.Datum P) (Λ Λ' : Submodule M.L.O V),
      (LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧
        ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) →
      (LocNG.IsTermOver P d (⟨Λ', f, f', P.A.T, P.B.T⟩ : Term V M r) ∧
        ¬ LocNG.BBne (H := H) (⟨Λ', f, f', P.A.T, P.B.T⟩ : Term V M r)) → Λ = Λ' := by
    intro d Λ Λ' h h'
    have key : ∀ Λ : Submodule M.L.O V,
        (LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧
          ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) →
        S.IsTerm (c.dat d) (c.lat Λ) ∧ S.M (c.dat d) (c.lat Λ) = S.Mof fc fc' := by
      intro Λ h
      obtain ⟨-, -, hin, hbb⟩ := (hloc Λ).1.2 ⟨d, h⟩
      have h2 := hTC.1 d _ h.1
      refine ⟨h2.1, ?_⟩
      have hz : S.BBzero (c.dat d) (c.lat Λ) := by
        by_contra hn; exact h.2 (h2.2.2.2 hn)
      rw [hz]; exact (hKM Λ).1 ⟨hin, hbb⟩
    obtain ⟨a1, a2⟩ := key Λ h
    obtain ⟨b1, b2⟩ := key Λ' h'
    apply hMT.2.2.1.1
    exact le_antisymm (GlobalTheory.HL.UnimodTerm.le_of_M_eq S b1 a1 ha (a2.trans b2.symm))
      (GlobalTheory.HL.UnimodTerm.le_of_M_eq S a1 b1 ha (b2.trans a2.symm))
  refine ⟨fun hR => ?_, fun ht => ?_⟩
  · obtain ⟨Λ0, h0⟩ := hex0
    obtain ⟨g, hg, hmv⟩ := hR
    have hset := (hmov g hg d0 d hmv).2
    have hmem : LocNG.img g Λ0 ∈ {Λ : Submodule M.L.O V |
        LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧
          ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} := by
      rw [← hset]; exact ⟨Λ0, h0, rfl⟩
    exact ⟨LocNG.img g Λ0, hmem, fun Λ hΛ => huniq d _ _ hΛ hmem⟩
  · obtain ⟨t, ht⟩ := ht
    obtain ⟨t0, ht0⟩ := hd0
    exact GlobalTheory.T.hermitianData_with_term_single_orbit_primeTo M hM H r k P hdim hrel hpt d0 d t0 t ht0 ht

end GlobalTheory.HL.GoodFrames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianOrbitUniqueLatticeIntegralFramesStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_orbit_unique_lattice_integral_frames : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → P.PrimeTo → ∀ (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → A a b = 0 ∧ A' a b = 0) → (∀ a, A a a = 1 ∧ A' a a = 1) → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O) → ∀ (f f' : Fin (r + 1) → V), (∀ j, f j = ∑ i, A i j • P.A.f i) → (∀ j, f' j = ∑ i, A' i j • P.B.f i) → ∀ d0 : LocNG.Datum P, (∃ t, LocNG.IsTermOver P d0 t) → ∀ d : LocNG.Datum P, (LocNG.Datum.Rel d0 d → ∃! Λ : Submodule M.L.O V, LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) ∧ ((∃ t, LocNG.IsTermOver P d t) → LocNG.Datum.Rel d0 d) := by
  first | exact @GlobalTheory.HL.GoodFrames.main | exact GlobalTheory.HL.GoodFrames.main | (intros; apply GlobalTheory.HL.GoodFrames.main <;> assumption)
end
end
