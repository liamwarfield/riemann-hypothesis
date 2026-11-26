module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharInfTrivialOfTrivAtDegOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictScalarsHomContinuousKrullStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArtinRestrictEqArtinNormSinglePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdIdeleCharGlobalUnitEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdIdeleCharGlobalUnitEqOne
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open Neutral.B1 hiding G IsPlaceOver IsPlaceOver

namespace GlobalTheory.ProdLocUnit

theorem prod_locUnit_eq_one : ∀ (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (B : Type) [CommGroup B] (ψ : Ideles F →* B), IsOpen (ψ.ker : Set (Ideles F)) → (∀ k : Fˣ, ψ (diagUnits F k) = 1) → ∀ (a : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∉ T, ψ (locUnit F v a) = 1) → ∏ v ∈ T, ψ (locUnit F v a) = 1 := by
  intro F _ _ _ B _ ψ hker hd a T hT
  classical
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  have hψ : Continuous ψ := continuous_of_isOpen_ker' ψ hker
  let ι : (InfiniteAdeleRing F)ˣ →* Ideles F :=
    Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  have hι : Continuous ι := Continuous.units_map _ (continuous_id.prodMk continuous_const)
  have hinf : ∀ u, ψ (ι u) = 1 := by
    intro u
    obtain ⟨y, rfl⟩ := GlobalTheory.HeckeInfTriv.infUnit_surj F u
    have hc : Continuous fun y => ψ (ι (GlobalTheory.HeckeInfTriv.infUnit F y)) :=
      hψ.comp (hι.comp (GlobalTheory.HeckeInfTriv.continuous_infUnit F))
    have e := PreconnectedSpace.constant inferInstance hc (x := y) (y := 1)
    rw [e, map_one, map_one, map_one]
  let P : Ideles F →* (InfiniteAdeleRing F)ˣ :=
    Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let u : (InfiniteAdeleRing F)ˣ := P (diagUnits F a)
  let av : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ :=
    fun v => Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a
  let z : Ideles F := diagUnits F a * (ι u)⁻¹ * (∏ v ∈ T, locUnit F v a)⁻¹
  have hPι : P (ι u) = u := Units.ext rfl
  have hPl : ∀ v, P (locUnit F v a) = 1 := fun v => Units.ext rfl
  have hz1 : (z : AdeleRing (𝓞 F) F).1 = 1 := by
    have h : P z = 1 := by
      simp only [z, map_mul, map_inv, map_prod, hPι, hPl, Finset.prod_const_one, inv_one, mul_one]
      exact mul_inv_cancel u
    exact congrArg Units.val h
  have hev_d : ∀ v, Units.map (GlobalTheory.Mem.LocTriv.ev v) (diagUnits F a) = av v := fun v => Units.ext rfl
  have hev_i : ∀ v, Units.map (GlobalTheory.Mem.LocTriv.ev v) (ι u) = 1 := fun v => Units.ext rfl
  have hev_l : ∀ v w, Units.map (GlobalTheory.Mem.LocTriv.ev v) (locUnit F w a) = if w = v then av v else 1 := by
    intro v w
    apply Units.ext
    split_ifs with h
    · subst h
      exact GlobalTheory.Mem.LocTriv.ev_local_self w _
    · exact GlobalTheory.Mem.LocTriv.ev_local_ne (Ne.symm h) _
  have hzl : ∀ v, ψ (localIdele F v (Units.map (GlobalTheory.Mem.LocTriv.ev v) z)) = 1 := by
    intro v
    have e : Units.map (GlobalTheory.Mem.LocTriv.ev v) z = av v * (∏ w ∈ T, if w = v then av v else 1)⁻¹ := by
      simp only [z, map_mul, map_inv, map_prod, hev_d, hev_i, hev_l, inv_one, mul_one]
    rw [e, Finset.prod_ite_eq' T v]
    split_ifs with hv
    · rw [mul_inv_cancel, map_one, map_one]
    · rw [inv_one, mul_one]
      exact hT v hv
  have hz := GlobalTheory.FrobDense.eq_one_of_local ψ hψ z hz1 hzl
  simp only [z, map_mul, map_inv, map_prod, hd, hinf, inv_one, one_mul] at hz
  exact inv_eq_one.mp hz

end GlobalTheory.ProdLocUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdIdeleCharGlobalUnitEqOneStatement
open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open Neutral.B1 hiding G IsPlaceOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_idele_char_global_unit_eq_one : ∀ (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (B : Type) [CommGroup B] (ψ : Ideles F →* B), IsOpen (ψ.ker : Set (Ideles F)) → (∀ k : Fˣ, ψ (diagUnits F k) = 1) → ∀ (a : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∉ T, ψ (locUnit F v a) = 1) → ∏ v ∈ T, ψ (locUnit F v a) = 1 := by
  exact @GlobalTheory.ProdLocUnit.prod_locUnit_eq_one
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterGlobalArtinUnitsTrivialUniformiserPower
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterGlobalArtinUnitsTrivialUniformiserPower
open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open Neutral.B1 hiding G IsPlaceOver

namespace GlobalTheory.NormCompat

theorem chi_artin_restrict : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω] (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK → ∀ (ρ : Gab K Ω →* Gab E Ω), (∀ τ : G K Ω, ρ (toAb K Ω τ) = toAb E Ω (τ.restrictScalars E)) → ∀ (B : Type) [CommGroup B] (χ : Gab E Ω →* B) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → (∀ x, IsUnitAt v x → χ (art (localIdele E v x)) = 1) → (∀ x, IsUnitAt w x → χ (ρ (artK (localIdele K w x))) = 1) ∧ ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → χ (ρ (artK (localIdele K w x))) = χ (art (localIdele E v ϖ)) ^ w.asIdeal.inertiaDeg (𝓞 E) := by
  intro E Ω _ _ _ _ _ K _ _ _ art artK ha haK ρ hρ B _ χ v w hwv hχ
  obtain ⟨A, hAw⟩ := exists_isPlaceOver (F := K) Ω w
  obtain ⟨hAv, -, hine, hfrob⟩ := GlobalTheory.T.frobenius_restrictScalars_pow_mod_inertia E Ω K v w hwv A hAw

  have hI : ∀ ι ∈ Ine (F := E) A, χ (toAb E Ω ι) = 1 := by
    intro ι hι
    obtain ⟨u, hu, e⟩ := (ha.ine v A hAv (toAb E Ω ι)).mpr ⟨ι, hι, rfl⟩
    rw [← e]
    exact hχ u hu
  refine ⟨fun x hx => ?_, fun x ϖ hx hϖ => ?_⟩
  · obtain ⟨ι, hι, e⟩ := (haK.ine w A hAw _).mp ⟨x, hx, rfl⟩
    rw [← e, hρ]
    exact hI _ (hine ι hι)
  · obtain ⟨σ, hσ, e⟩ := (haK.frob w A hAw _).mp ⟨x, hx, rfl⟩
    obtain ⟨φ, hφ, e'⟩ := (ha.frob v A hAv _).mp ⟨ϖ, hϖ, rfl⟩
    have hm := hI _ (hfrob σ φ hσ hφ)
    have hr : (σ⁻¹).restrictScalars E = (σ.restrictScalars E)⁻¹ := AlgEquiv.ext fun _ => rfl
    rw [← e, hρ, ← e', hr, map_inv, map_inv, map_inv, map_inv, inv_pow]
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow] at hm
    rw [inv_inj]
    exact mul_inv_eq_one.mp hm

end GlobalTheory.NormCompat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterGlobalArtinUnitsTrivialUniformiserPowerStatement
open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open Neutral.B1 hiding G IsPlaceOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_globalArtin_units_trivial_uniformiser_power : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω] (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK → ∀ (ρ : Gab K Ω →* Gab E Ω), (∀ τ : G K Ω, ρ (toAb K Ω τ) = toAb E Ω (τ.restrictScalars E)) → ∀ (B : Type) [CommGroup B] (χ : Gab E Ω →* B) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → (∀ x, IsUnitAt v x → χ (art (localIdele E v x)) = 1) → (∀ x, IsUnitAt w x → χ (ρ (artK (localIdele K w x))) = 1) ∧ ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → χ (ρ (artK (localIdele K w x))) = χ (art (localIdele E v ϖ)) ^ w.asIdeal.inertiaDeg (𝓞 E) := by
  first | exact @GlobalTheory.NormCompat.chi_artin_restrict | exact GlobalTheory.NormCompat.chi_artin_restrict | (intros; apply GlobalTheory.NormCompat.chi_artin_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTotallyComplexOfAlgebraOfIsTotallyComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTotallyComplexOfAlgebraOfIsTotallyComplex
open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open Neutral.B1 hiding G IsPlaceOver

namespace GlobalTheory

theorem isTotallyComplex_of_algebra (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] [Algebra E K] [_root_.NumberField.IsTotallyComplex E] : IsTotallyComplex K := by
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  have h := InfinitePlace.IsReal.comap (algebraMap E K) hw
  exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _) h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTotallyComplexOfAlgebraOfIsTotallyComplexStatement
open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open Neutral.B1 hiding G IsPlaceOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTotallyComplex_of_algebra_of_isTotallyComplex : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [_root_.NumberField.IsTotallyComplex E], IsTotallyComplex K := by
  first | exact @GlobalTheory.isTotallyComplex_of_algebra | exact GlobalTheory.isTotallyComplex_of_algebra | (intros; apply GlobalTheory.isTotallyComplex_of_algebra <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArtinRestrictEqArtinNormSinglePlace
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open Neutral.B1 hiding G IsPlaceOver

namespace GlobalTheory.NormCompat

theorem val_div_sub_one_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {a c : K}
    (hc : c ≠ 0) {N m : ℕ} (hm : (WithZero.log (w.valuation K c)).natAbs ≤ m)
    (h : w.valuation K (a - c) ≤ WithZero.exp (-((N : ℤ) + m))) :
    w.valuation K (a / c - 1) ≤ WithZero.exp (-(N : ℤ)) := by
  have hv : w.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  rw [div_sub_one hc, map_div₀, ← WithZero.exp_log hv, div_le_iff₀ (by simp), ← WithZero.exp_add]
  refine h.trans (WithZero.exp_le_exp.mpr ?_)
  have : -(m : ℤ) ≤ WithZero.log (w.valuation K c) := by omega
  omega

theorem val_le_of_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {N N' : ℤ}
    (h : w.valuation K x ≤ WithZero.exp (-N)) (hN : N' ≤ N) : w.valuation K x ≤ WithZero.exp (-N') :=
  h.trans (WithZero.exp_le_exp.mpr (by omega))

theorem res_art_eq_art_norm : ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω]
    (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)),
      W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal →
      (∀ W' : HeightOneSpectrum (𝓞 K), W'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → W' = W) →
      ∀ (y : Kˣ) (τ : G K Ω),
        toAb K Ω τ = artK (localIdele K W (Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom y)) →
        toAb E Ω (τ.restrictScalars E) =
          art (localIdele E v (Units.map (algebraMap E (v.adicCompletion E)).toMonoidHom
            (Units.map (Algebra.norm E (S := K)) y))) := by
  intro E Ω _ _ _ _ _ _ K _ _ _ art artK ha haK v W hW hWu y τ hτ
  classical
  haveI : IsTotallyComplex K := GlobalTheory.T.isTotallyComplex_of_algebra_of_isTotallyComplex E K
  haveI : IsClosed ((commutator (G E Ω)).topologicalClosure : Set (G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  let r : G K Ω →* Gab E Ω := (toAb E Ω).comp (AlgEquiv.restrictScalarsHom E)
  have hr : Continuous r := QuotientGroup.continuous_mk.comp (GlobalTheory.T.continuous_restrictScalarsHom' E Ω K)
  let ρ : Gab K Ω →* Gab E Ω := liftAb r hr
  have hρ : ∀ σ : G K Ω, ρ (toAb K Ω σ) = toAb E Ω (σ.restrictScalars E) := fun σ => rfl
  have hρc : Continuous ρ := continuous_liftAb r hr
  let NK : Kˣ →* Eˣ := Units.map (Algebra.norm E (S := K))
  have hdE : ∀ k : Eˣ, art (diagUnits E k) = 1 := fun k => by
    have hk : diagUnits E k ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  have hdK : ∀ k : Kˣ, artK (diagUnits K k) = 1 := fun k => by
    have hk : diagUnits K k ∈ artK.ker := by
      rw [haK.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  show toAb E Ω (τ.restrictScalars E) = art (locUnit E v (NK y))
  rw [← hρ, hτ]
  change ρ (artK (locUnit K W y)) = art (locUnit E v (NK y))
  rw [← div_eq_one]
  refine GlobalTheory.T.absoluteGaloisAbelianization_eq_one_of_mem_open_subgroups E Ω _ fun U hU => ?_
  let χ : Gab E Ω →* Gab E Ω ⧸ U := QuotientGroup.mk' U
  suffices h : χ (ρ (artK (locUnit K W y))) = χ (art (locUnit E v (NK y))) by
    have h2 : χ (ρ (artK (locUnit K W y)) / art (locUnit E v (NK y))) = 1 := by
      rw [map_div, h, div_self']
    exact (QuotientGroup.eq_one_iff _).mp h2
  let ψ1 : Ideles K →* Gab E Ω ⧸ U := χ.comp (ρ.comp artK)
  let ψ2 : Ideles E →* Gab E Ω ⧸ U := χ.comp art
  have hker1 : (ψ1.ker : Set (Ideles K)) = (ρ.comp artK) ⁻¹' U := by
    ext x; simp [ψ1, χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hker2 : (ψ2.ker : Set (Ideles E)) = art ⁻¹' U := by
    ext x; simp [ψ2, χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have ho1 : IsOpen (ψ1.ker : Set (Ideles K)) := by
    rw [hker1]; exact hU.preimage (hρc.comp haK.quot.continuous)
  have ho2 : IsOpen (ψ2.ker : Set (Ideles E)) := by
    rw [hker2]; exact hU.preimage ha.quot.continuous

  obtain ⟨SE, ME, hvS, hSu, hSc⟩ := GlobalTheory.T.isOpen_idele_subgroup_contains_congruence_units E ψ2.ker ho2 {v}
  have hvSE : v ∈ SE := hvS (Finset.mem_singleton_self v)
  obtain ⟨TSK, hTSK⟩ := GlobalTheory.T.exists_finset_places_over_finset_places E K SE
  have hWT : W ∈ TSK := (hTSK W).mpr ⟨v, hvSE, hW⟩
  obtain ⟨MainNotions, MK, hTS, -, hSKc⟩ := GlobalTheory.T.isOpen_idele_subgroup_contains_congruence_units K ψ1.ker ho1 TSK
  choose M' hM' using fun v' : HeightOneSpectrum (𝓞 E) => GlobalTheory.T.norm_close_to_one_of_close_above_place E K v' ME
  let M'' : ℕ := SE.sup M'
  let m : ℕ := (WithZero.log (W.valuation K (y : K))).natAbs
  obtain ⟨a, ha'⟩ := GlobalTheory.T.exists_approx_finite_places_numberField_target K TSK (fun w => if w = W then (y : K) else 1) (MK + M'' + m + 1)
  have haW : W.valuation K (a - y) ≤ WithZero.exp (-(((MK + M'' + 1 : ℕ) : ℤ) + m)) := by
    have := ha' W hWT
    rw [ite_eq_left rfl] at this
    exact val_le_of_le W this (by push_cast; omega)
  have hz : W.valuation K (a / y - 1) ≤ WithZero.exp (-((MK + M'' + 1 : ℕ) : ℤ)) :=
    val_div_sub_one_le W y.ne_zero le_rfl haW
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_div, zero_sub, Valuation.map_neg, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at hz
    omega
  let au : Kˣ := Units.mk0 a ha0
  let zu : Kˣ := au / y
  have hzu : (zu : K) = a / y := by simp [zu, au]
  have hauy : au = y * zu := by simp [zu]

  have F1 : ψ1 (locUnit K W au) = ψ1 (locUnit K W y) := by
    have hm : locUnit K W zu ∈ ψ1.ker := hSKc W (hTS hWT) zu (by
      rw [hzu]; exact val_le_of_le W hz (by push_cast; omega))
    rw [hauy, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]

  have F2 : ψ2 (locUnit E v (NK au)) = ψ2 (locUnit E v (NK y)) := by
    have hm : locUnit E v (NK zu) ∈ ψ2.ker := hSc v hvSE (NK zu) (by
      refine hM' v (zu : K) fun w hw => ?_
      rw [hWu w hw, hzu]
      exact val_le_of_le W hz (by
        have : M' v ≤ M'' := Finset.le_sup hvSE
        push_cast; omega))
    rw [hauy, map_mul, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]

  have F3 : ∀ w ∈ TSK, w ≠ W → ψ1 (locUnit K w au) = 1 := fun w hw hne => by
    have := ha' w hw
    rw [ite_eq_right hne] at this
    exact MonoidHom.mem_ker.mp (hSKc w (hTS hw) au (val_le_of_le w this (by push_cast; omega)))
  have F4 : ∀ v' ∈ SE, v' ≠ v → ψ2 (locUnit E v' (NK au)) = 1 := fun v' hv' hne => by
    refine MonoidHom.mem_ker.mp (hSc v' hv' (NK au) ?_)
    refine hM' v' (au : K) fun w hw => ?_
    have hwT : w ∈ TSK := (hTSK w).mpr ⟨v', hv', hw⟩
    have hwW : w ≠ W := by
      rintro rfl
      exact hne (HeightOneSpectrum.ext (hw.symm.trans hW))
    have := ha' w hwT
    rw [ite_eq_right hwW] at this
    exact val_le_of_le w this (by
      have : M' v' ≤ M'' := Finset.le_sup hv'
      push_cast; omega)

  have hunitE : ∀ v' ∉ SE, ∀ x, IsUnitAt v' x → ψ2 (localIdele E v' x) = 1 := fun v' hv' x hx =>
    MonoidHom.mem_ker.mp (hSu v' hv' x hx)
  have hchi := fun (v' : HeightOneSpectrum (𝓞 E)) (hv' : v' ∉ SE) (w : HeightOneSpectrum (𝓞 K))
      (hw : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v'.asIdeal) =>
    GlobalTheory.T.character_globalArtin_units_trivial_uniformiser_power E Ω K art artK ha haK ρ hρ (Gab E Ω ⧸ U) χ v' w hw (hunitE v' hv')
  obtain ⟨TK, TE, hTK1, hTK2, hTE1, hTE2, hprod⟩ := GlobalTheory.T.prod_localValues_global_over_places_above E K (Gab E Ω ⧸ U) ψ1 ψ2 SE hunitE
    (fun v' hv' w hw => (hchi v' hv' w hw).1) (fun v' hv' w hw => (hchi v' hv' w hw).2) au

  have hPK : (∏ w ∈ TK, ψ1 (locUnit K w au)) * ψ1 (locUnit K W au) = 1 := by
    have hdisj : Disjoint TK TSK := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      obtain ⟨v', hv', e⟩ := (hTSK w).mp h2
      exact hTK1 w h1 v' hv' e
    have h := GlobalTheory.T.prod_idele_char_global_unit_eq_one K (Gab E Ω ⧸ U) ψ1 ho1 (fun k => by simp [ψ1, hdK]) au (TK ∪ TSK) fun w hw => by
      rw [Finset.mem_union, not_or] at hw
      refine hTK2 w hw.1 fun v' hv' e => hw.2 ((hTSK w).mpr ⟨v', hv', e⟩)
    rw [Finset.prod_union hdisj, Finset.prod_eq_single_of_mem W hWT F3] at h
    exact h
  have hPE : (∏ v' ∈ TE, ψ2 (locUnit E v' (NK au))) * ψ2 (locUnit E v (NK au)) = 1 := by
    have hdisj : Disjoint TE SE := by
      rw [Finset.disjoint_left]
      intro v' h1 h2
      exact hTE1 v' h1 h2
    have h := GlobalTheory.T.prod_idele_char_global_unit_eq_one E (Gab E Ω ⧸ U) ψ2 ho2 (fun k => by simp [ψ2, hdE]) (NK au) (TE ∪ SE) fun v' hv' => by
      rw [Finset.mem_union, not_or] at hv'
      exact hTE2 v' hv'.1 hv'.2
    rw [Finset.prod_union hdisj, Finset.prod_eq_single_of_mem v hvSE F4] at h
    exact h
  have key : ψ1 (locUnit K W au) = ψ2 (locUnit E v (NK au)) := by
    rw [← hprod] at hPE
    exact mul_left_cancel (hPK.trans hPE.symm)
  show ψ1 (locUnit K W y) = ψ2 (locUnit E v (NK y))
  rw [← F1, key, F2]

end GlobalTheory.NormCompat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArtinRestrictEqArtinNormSinglePlaceStatement
open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Neutral.B1 hiding G IsPlaceOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_restrict_eq_artin_norm_single_place : ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω]
    (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)),
      W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal →
      (∀ W' : HeightOneSpectrum (𝓞 K), W'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → W' = W) →
      ∀ (y : Kˣ) (τ : G K Ω),
        toAb K Ω τ = artK (localIdele K W (Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom y)) →
        toAb E Ω (τ.restrictScalars E) =
          art (localIdele E v (Units.map (algebraMap E (v.adicCompletion E)).toMonoidHom
            (Units.map (Algebra.norm E (S := K)) y))) := by
  first | exact @GlobalTheory.NormCompat.res_art_eq_art_norm | exact GlobalTheory.NormCompat.res_art_eq_art_norm | (intros; apply GlobalTheory.NormCompat.res_art_eq_art_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameEisensteinExtensionUniqueTotallyRamifiedPlac
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameEisensteinExtensionUniqueTotallyRamifiedPlac
open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Neutral.B1 hiding G IsPlaceOver

noncomputable section

namespace GlobalTheory.TameRecPlace

theorem int_val_le_one {L Ω : Type} [Field L] [Field Ω] [Algebra L Ω] (A : ValuationSubring Ω) (x : 𝓞 L) :
    A.valuation (algebraMap L Ω (x : L)) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom))

theorem intValuation_exp_neg_one {L : Type} [Field L] [NumberField L]
    (w : HeightOneSpectrum (𝓞 L)) (x : 𝓞 L) (h1 : x ∈ w.asIdeal) (h2 : x ∉ w.asIdeal ^ 2) :
    w.intValuation x = WithZero.exp (-1 : ℤ) := by
  have h0 : x ≠ 0 := by
    rintro rfl
    exact h2 (Submodule.zero_mem _)
  have ha : w.intValuation x ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (w.intValuation_le_pow_iff_mem x 1).mpr (by simpa using h1)
  have hb : ¬ w.intValuation x ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h =>
    h2 ((w.intValuation_le_pow_iff_mem x 2).mp h)
  rw [w.intValuation_if_neg h0] at ha hb ⊢
  rw [WithZero.exp_le_exp] at ha hb
  rw [WithZero.exp_inj]
  omega

theorem one_lt_normV {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) : 1 < normV v := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  exact Finite.one_lt_card

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (ϖ : 𝓞 E), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 →
    ∀ (π : Ω) [FiniteDimensional E (IntermediateField.adjoin E {π})] [NumberField (IntermediateField.adjoin E {π})],
    π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
    ∃ W : HeightOneSpectrum (𝓞 (IntermediateField.adjoin E {π})),
      W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 (IntermediateField.adjoin E {π}))) = v.asIdeal ∧
      (∀ W' : HeightOneSpectrum (𝓞 (IntermediateField.adjoin E {π})),
        W'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 (IntermediateField.adjoin E {π}))) = v.asIdeal → W' = W) ∧
      IsPlaceOver A W ∧ normV W = normV v ∧
      ∀ c : (W.adicCompletion (IntermediateField.adjoin E {π}))ˣ,
        (c : W.adicCompletion (IntermediateField.adjoin E {π})) =
          algebraMap (IntermediateField.adjoin E {π}) _ (IntermediateField.AdjoinSimple.gen E π) → IsUnifAt W c := by
  intro E Ω _ _ _ _ v A hA ϖ h1 h2 π _ _ hπ
  set K := IntermediateField.adjoin E {π} with hK
  have hn1 : 1 ≤ normV v - 1 := by have := one_lt_normV v; omega
  set n := normV v - 1 with hn

  set g : K := IntermediateField.AdjoinSimple.gen E π with hg
  have hgΩ : algebraMap K Ω g = π := IntermediateField.AdjoinSimple.algebraMap_gen E π
  have hgn : g ^ n = algebraMap E K (ϖ : E) := by
    apply (algebraMap K Ω).injective
    rw [map_pow, hgΩ, hπ]
    exact IsScalarTower.algebraMap_apply E K Ω _
  have hgint : IsIntegral ℤ g := by
    refine IsIntegral.of_pow (n := n) (by omega) ?_
    rw [hgn]
    exact ϖ.isIntegral_coe.map (algebraMap E K).toIntAlgHom
  set πO : 𝓞 K := ⟨g, hgint⟩ with hπO
  have hπOn : πO ^ n = algebraMap (𝓞 E) (𝓞 K) ϖ := by
    apply RingOfIntegers.ext
    show g ^ n = _
    rw [hgn]
    rfl
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact h2 (Submodule.zero_mem _)

  let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A fun x =>
    (A.valuation_le_one_iff _).1 (int_val_le_one A x)
  have hf : ∀ x, x ∈ (IsLocalRing.maximalIdeal A).comap f ↔ A.valuation (algebraMap K Ω (x : K)) < 1 := fun x =>
    A.valuation_lt_one_iff (f x)
  have hπΩ : algebraMap K Ω ((πO : 𝓞 K) : K) = π := hgΩ
  have hAπ : A.valuation π < 1 := by
    have hv1 : A.valuation (algebraMap E Ω (ϖ : E)) < 1 := (hA ϖ).2 h1
    rw [← hπ, map_pow] at hv1
    by_contra hc
    exact (not_lt.2 (one_le_pow₀ (not_lt.1 hc))) hv1
  have hπmem : πO ∈ (IsLocalRing.maximalIdeal A).comap f := (hf πO).2 (by rw [hπΩ]; exact hAπ)
  have hπO0 : πO ≠ 0 := by
    intro h0
    have : πO ^ n = 0 := by rw [h0, zero_pow (by omega)]
    rw [hπOn] at this
    exact hϖ0 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 K))).1 this)
  let W : HeightOneSpectrum (𝓞 K) :=
    ⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun hb => hπO0 (by
      have := hπmem; rw [hb] at this; exact this)⟩
  have hWmem : ∀ x : 𝓞 K, x ∈ W.asIdeal ↔ A.valuation (algebraMap K Ω (x : K)) < 1 := hf
  have hWv : W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
    ext x
    rw [Ideal.mem_comap, hWmem, ← hA x]
    have : ((algebraMap (𝓞 E) (𝓞 K) x : 𝓞 K) : K) = algebraMap E K (x : E) := rfl
    rw [this, ← IsScalarTower.algebraMap_apply]
  have hPW : IsPlaceOver A W := fun x => (hWmem x).symm

  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI hLO : W.asIdeal.LiesOver v.asIdeal := ⟨hWv.symm⟩
  have hprW : Prime W.asIdeal := Ideal.prime_of_isPrime W.ne_bot W.isPrime
  have hconds : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
  have hspan0 : Ideal.span {ϖ} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hϖ0
  have hem := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul (R := 𝓞 E) (S := 𝓞 K)
    hspan0 hconds.irreducible hprW.irreducible W.ne_bot
  have hspan : (Ideal.span {ϖ}).map (algebraMap (𝓞 E) (𝓞 K)) = Ideal.span {πO} ^ n := by
    rw [Ideal.map_span, Set.image_singleton, ← hπOn, Ideal.span_singleton_pow]
  have hv1 : emultiplicity v.asIdeal (Ideal.span {ϖ}) = 1 := by
    rw [← Nat.cast_one, emultiplicity_eq_coe]
    refine ⟨?_, ?_⟩
    · rw [pow_one, Ideal.dvd_span_singleton]; exact h1
    · rw [Ideal.dvd_span_singleton]; exact h2
  rw [hspan, emultiplicity_pow hprW, hv1, mul_one] at hem
  set e := v.asIdeal.ramificationIdx' W.asIdeal with he
  set m := emultiplicity W.asIdeal (Ideal.span {πO}) with hm
  have hm1 : 1 ≤ m := by
    have := le_emultiplicity_of_pow_dvd (a := W.asIdeal) (b := Ideal.span {πO}) (k := 1)
      (by rw [pow_one]; exact Ideal.dvd_span_singleton.2 hπmem)
    simpa using this
  have hne : n ≤ e := by
    have : (n : ℕ∞) ≤ e := by
      rw [← hem]
      calc (n : ℕ∞) = n * 1 := (mul_one _).symm
        _ ≤ n * m := by gcongr
    exact_mod_cast this
  have hsum := Ideal.sum_ramification_inertia (R := 𝓞 E) (S := 𝓞 K) E K (p := v.asIdeal) v.ne_bot
  have hfin : Module.finrank E K ≤ n := by
    have hint : IsIntegral E π := by
      refine ⟨Polynomial.X ^ n - Polynomial.C (ϖ : E), ?_, ?_⟩
      · exact Polynomial.monic_X_pow_sub_C _ (by omega)
      · simp [hπ, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    rw [IntermediateField.adjoin.finrank hint]
    have hd := minpoly.degree_le_of_ne_zero E π (p := Polynomial.X ^ n - Polynomial.C (ϖ : E))
      (Polynomial.X_pow_sub_C_ne_zero (by omega) _) (by simp [hπ])
    rw [Polynomial.degree_X_pow_sub_C (by omega)] at hd
    exact Polynomial.natDegree_le_of_degree_le hd
  have hWS : W.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K) :=
    (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot _).2 ⟨W.isPrime, hLO⟩
  have hpos : ∀ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K),
      1 ≤ v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P := by
    intro P hP
    obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot _).1 hP
    have h1' : v.asIdeal.ramificationIdx' P ≠ 0 := by
      refine Ideal.IsDedekindDomain.ramificationIdx'_ne_zero (Ideal.map_ne_bot_of_ne_bot v.ne_bot) hPp ?_
      rw [Ideal.map_le_iff_le_comap]
      exact (Ideal.LiesOver.over (P := P) (p := v.asIdeal)).le
    have h2' : 0 < v.asIdeal.inertiaDeg' P := Ideal.inertiaDeg'_pos v.asIdeal P
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h1' h2'.ne')
  rw [← Finset.add_sum_erase _ _ hWS] at hsum
  change e * v.asIdeal.inertiaDeg' W.asIdeal + _ = _ at hsum
  have hfW : 0 < v.asIdeal.inertiaDeg' W.asIdeal := Ideal.inertiaDeg'_pos v.asIdeal W.asIdeal
  have hrest : ∀ P ∈ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K)).erase W.asIdeal, False := by
    intro P hP
    have hle := Finset.single_le_sum (f := fun P => v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P)
      (fun _ _ => Nat.zero_le _) hP
    have := hpos P (Finset.mem_of_mem_erase hP)
    have : e * 1 ≤ e * v.asIdeal.inertiaDeg' W.asIdeal := Nat.mul_le_mul_left _ hfW
    omega
  have hsum0 : ∑ P ∈ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K)).erase W.asIdeal,
      v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P = 0 :=
    Finset.sum_eq_zero fun P hP => (hrest P hP).elim
  rw [hsum0, add_zero] at hsum
  have hen : e = n ∧ v.asIdeal.inertiaDeg' W.asIdeal = 1 := by
    have : e * 1 ≤ e * v.asIdeal.inertiaDeg' W.asIdeal := Nat.mul_le_mul_left _ hfW
    have h3 : e * v.asIdeal.inertiaDeg' W.asIdeal ≤ n := hsum ▸ hfin
    refine ⟨by omega, ?_⟩
    have he0 : 0 < e := by omega
    by_contra hc
    have : e * 2 ≤ e * v.asIdeal.inertiaDeg' W.asIdeal := Nat.mul_le_mul_left _ (by omega)
    omega

  obtain ⟨hen, hf1⟩ := hen
  have hπ2 : πO ∉ W.asIdeal ^ 2 := by
    intro h
    have h2m : ((2 : ℕ) : ℕ∞) ≤ m := le_emultiplicity_of_pow_dvd (Ideal.dvd_span_singleton.2 h)
    have : ((n * 2 : ℕ) : ℕ∞) ≤ (e : ℕ∞) := by
      rw [← hem, Nat.cast_mul]
      gcongr
    have := (Nat.cast_le.1 this)
    omega
  refine ⟨W, hWv, ?_, hPW, ?_, ?_⟩
  · intro W' hW'
    have hmem : W'.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K) :=
      (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot _).2 ⟨W'.isPrime, ⟨hW'.symm⟩⟩
    by_contra hne'
    have hne2 : W'.asIdeal ≠ W.asIdeal := fun h => hne' (HeightOneSpectrum.ext h)
    exact hrest _ (Finset.mem_erase.2 ⟨hne2, hmem⟩)
  · letI := Ideal.Quotient.field v.asIdeal
    have hfr : Module.finrank (𝓞 E ⧸ v.asIdeal) (𝓞 K ⧸ W.asIdeal) = 1 := by
      rw [← Ideal.inertiaDeg'_algebraMap]; exact hf1
    show Nat.card (𝓞 K ⧸ W.asIdeal) = Nat.card (𝓞 E ⧸ v.asIdeal)
    rw [Module.natCard_eq_pow_finrank (K := 𝓞 E ⧸ v.asIdeal), hfr, pow_one]
  · intro c hc
    show Valued.v (c : W.adicCompletion K) = WithZero.exp (-1)
    rw [hc]
    have h3 : Valued.v (((πO : 𝓞 K) : K) : W.adicCompletion K) = W.valuation K ((πO : 𝓞 K) : K) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' W _
    have h4 : W.valuation K ((πO : 𝓞 K) : K) = WithZero.exp (-1) := by
      rw [show ((πO : 𝓞 K) : K) = algebraMap (𝓞 K) K πO from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      exact intValuation_exp_neg_one W πO hπmem hπ2
    rw [← h4, ← h3]
    rfl

end GlobalTheory.TameRecPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameEisensteinExtensionUniqueTotallyRamifiedPlacStatement
open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Neutral.B1 hiding G IsPlaceOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameEisensteinExtension_unique_totallyRamified_place : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (ϖ : 𝓞 E), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 →
    ∀ (π : Ω) [FiniteDimensional E (IntermediateField.adjoin E {π})] [NumberField (IntermediateField.adjoin E {π})],
    π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
    ∃ W : HeightOneSpectrum (𝓞 (IntermediateField.adjoin E {π})),
      W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 (IntermediateField.adjoin E {π}))) = v.asIdeal ∧
      (∀ W' : HeightOneSpectrum (𝓞 (IntermediateField.adjoin E {π})),
        W'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 (IntermediateField.adjoin E {π}))) = v.asIdeal → W' = W) ∧
      IsPlaceOver A W ∧ normV W = normV v ∧
      ∀ c : (W.adicCompletion (IntermediateField.adjoin E {π}))ˣ,
        (c : W.adicCompletion (IntermediateField.adjoin E {π})) =
          algebraMap (IntermediateField.adjoin E {π}) _ (IntermediateField.AdjoinSimple.gen E π) → IsUnifAt W c := by
  first | exact @GlobalTheory.TameRecPlace.main | exact GlobalTheory.TameRecPlace.main | (intros; apply GlobalTheory.TameRecPlace.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinpolyAndNormOfPowEqUniformizer
open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Neutral.B1 hiding G IsPlaceOver

namespace GlobalTheory.TameEis

open Polynomial

theorem two_le_normV (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    2 ≤ normV v := by
  have h : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h' => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h')
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h' => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h')
  omega

theorem minpoly_and_norm_of_pow_eq_uniformizer : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E)) (ϖ : 𝓞 E),
    ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
      minpoly E π = Polynomial.X ^ (normV v - 1) - Polynomial.C (ϖ : E) ∧
      Algebra.norm E (IntermediateField.AdjoinSimple.gen E π) = (-1) ^ normV v * (ϖ : E) := by
  intro E Ω _ _ _ _ v ϖ hmem hnot π hπ
  have hq := two_le_normV E v
  set n := normV v - 1 with hn
  have hn1 : 0 < n := by omega
  have hmon : (X ^ n - C ϖ : (𝓞 E)[X]).Monic := monic_X_pow_sub_C ϖ hn1.ne'
  have hdeg : (X ^ n - C ϖ : (𝓞 E)[X]).natDegree = n := natDegree_X_pow_sub_C _
  have hEis : (X ^ n - C ϖ : (𝓞 E)[X]).IsEisensteinAt v.asIdeal := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmon.leadingCoeff]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro m hm
      rw [hdeg] at hm
      rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hm.ne]
      by_cases h0 : m = 0
      · subst h0; simpa using v.asIdeal.neg_mem_iff.2 hmem
      · simp [h0]
    · rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hn1.ne, if_pos rfl, zero_sub]
      rwa [Ideal.neg_mem_iff]
  have hirr : Irreducible (X ^ n - C ϖ : (𝓞 E)[X]) :=
    hEis.irreducible v.isPrime hmon.isPrimitive (by rw [hdeg]; exact hn1)
  have hmap : (X ^ n - C ϖ : (𝓞 E)[X]).map (algebraMap (𝓞 E) E) = X ^ n - C (ϖ : E) := by
    simp [Polynomial.map_sub]
  have hirrE : Irreducible (X ^ n - C (ϖ : E)) := by
    rw [← hmap]; exact (hmon.irreducible_iff_irreducible_map_fraction_map (K := E)).1 hirr
  have hmonE : (X ^ n - C (ϖ : E)).Monic := monic_X_pow_sub_C _ hn1.ne'
  have hroot : aeval π (X ^ n - C (ϖ : E)) = 0 := by
    simp [hπ]
  have hmin : minpoly E π = X ^ n - C (ϖ : E) :=
    (minpoly.eq_of_irreducible_of_monic hirrE hroot hmonE).symm
  refine ⟨hmin, ?_⟩
  have hx : IsIntegral E π := ⟨_, hmonE, hroot⟩
  rw [← IntermediateField.adjoin.powerBasis_gen hx,
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, IntermediateField.adjoin.powerBasis_gen hx,
    IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim, hmin, natDegree_X_pow_sub_C _]
  rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hn1.ne, if_pos rfl, zero_sub]
  have : normV v = n + 1 := by omega
  rw [this, pow_succ]; ring

end GlobalTheory.TameEis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrobFixOfEisenstein
open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Neutral.B1 hiding G IsPlaceOver

namespace GlobalTheory.TameRecip

theorem exists_frob_fix_of_eisenstein : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v →
    ∀ ϖ : 𝓞 E, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
    ∃ τ : G E Ω, IsFrob (F := E) A (normV v) τ ∧ τ π = π ∧
      ∀ c : (v.adicCompletion E)ˣ, (c : v.adicCompletion E) = (-1) ^ normV v * algebraMap E (v.adicCompletion E) (ϖ : E) →
        toAb E Ω τ⁻¹ = art (localIdele E v c) := by
  intro hG E Ω _ _ _ _ _ _ art hart v A hA ϖ hϖ hϖ2 π hπ
  have hint : IsIntegral E π := Algebra.IsIntegral.isIntegral π
  have : FiniteDimensional E (IntermediateField.adjoin E {π}) := IntermediateField.adjoin.finiteDimensional hint
  have : NumberField (IntermediateField.adjoin E {π}) := NumberField.of_module_finite E _
  have : IsAlgClosure (IntermediateField.adjoin E {π}) Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) _⟩
  set K := IntermediateField.adjoin E {π} with hKdef
  obtain ⟨artK, hartK⟩ := hG K Ω
  obtain ⟨W, hWv, hWuniq, hAW, hnW, hunif⟩ := GlobalTheory.T.tameEisensteinExtension_unique_totallyRamified_place E Ω v A hA ϖ hϖ hϖ2 π hπ
  obtain ⟨-, hnorm⟩ := GlobalTheory.TameEis.minpoly_and_norm_of_pow_eq_uniformizer E Ω v ϖ hϖ hϖ2 π hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    have hv1 : (1 : 𝓞 E) ∉ v.asIdeal := fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    rcases Nat.eq_zero_or_pos (normV v - 1) with h0 | h0
    · rw [h0, pow_zero] at hπ
      have : (ϖ : E) = ((1 : 𝓞 E) : E) := by
        apply (algebraMap E Ω).injective; rw [← hπ]; simp
      exact hv1 (by rw [← (RingOfIntegers.coe_injective this)]; exact hϖ)
    · rw [zero_pow h0.ne'] at hπ
      have : (ϖ : E) = 0 := (map_eq_zero_iff _ (algebraMap E Ω).injective).mp hπ.symm
      exact hϖ2 (by rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.mp this]; exact Ideal.zero_mem _)
  have hgen0 : IntermediateField.AdjoinSimple.gen E π ≠ 0 := by
    intro h; apply hπ0
    have := congrArg (algebraMap K Ω) h
    simpa using this
  set yK : Kˣ := Units.mk0 _ hgen0 with hyK
  set cπ : (W.adicCompletion K)ˣ := Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom yK with hcπ
  have hcu : IsUnifAt W cπ := hunif cπ rfl
  obtain ⟨σ, hσF, hσA⟩ := (hartK.frob W A hAW (artK (localIdele K W cπ))).mp ⟨cπ, hcu, rfl⟩
  have hN := GlobalTheory.T.artin_restrict_eq_artin_norm_single_place E Ω K art artK hart hartK v W hWv hWuniq yK σ⁻¹ hσA
  refine ⟨σ.restrictScalars E, ?_, ?_, ?_⟩
  · rw [← hnW]; exact hσF
  · have := σ.commutes (IntermediateField.AdjoinSimple.gen E π)
    simpa using this
  · intro c hc
    have hinv : (σ.restrictScalars E)⁻¹ = (σ⁻¹).restrictScalars E := rfl
    rw [hinv, hN]
    congr 2
    ext
    rw [hc]
    simp only [Units.coe_map, MonoidHom.coe_coe, hyK, Units.val_mk0]
    rw [hnorm]
    simp

end GlobalTheory.TameRecip
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrobFixOfEisensteinStatement
open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Neutral.B1 hiding G IsPlaceOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frob_of_eisenstein_root : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v →
    ∀ ϖ : 𝓞 E, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
    ∃ τ : G E Ω, IsFrob (F := E) A (normV v) τ ∧ τ π = π ∧
      ∀ c : (v.adicCompletion E)ˣ, (c : v.adicCompletion E) = (-1) ^ normV v * algebraMap E (v.adicCompletion E) (ϖ : E) →
        toAb E Ω τ⁻¹ = art (localIdele E v c) := by
  exact @GlobalTheory.TameRecip.exists_frob_fix_of_eisenstein
end
