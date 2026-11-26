module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.PlaceData
open NumberField IsDedekindDomain ValuativeRel PositivityTheory.Rg.Tf.Loc GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo
open scoped TensorProduct

theorem UpperTheory.V.Z.Tf.Orb.placeData :
    UpperTheory.V.Z.Tf.Orb.PlaceData := by
  intro F E _ _ _ _ _ _ σ hσ v w hw
  have hfix : ∀ τ : E ≃ₐ[F] E, w.1 = τ • w.1 := fun τ => (congrArg Subtype.val (hw (τ • w))).symm
  have hrk : Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = Module.finrank F E := by
    rw [← sum_finrank_eq E v, Finset.sum_eq_single w (fun b _ hb => absurd (hw b) hb) (by simp)]
  have hfin : FiniteDimensional (v.adicCompletion F) (w.1.adicCompletion E) :=
    Module.finite_of_finrank_pos (hrk ▸ Module.finrank_pos)
  have he0 : w.1.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := (Ideal.ramificationIdx_pos (R := 𝓞 F) w.1.asIdeal).ne'
  have hle : ∀ x y : w.1.adicCompletion E, valuation _ x ≤ valuation _ y ↔ Valued.v x ≤ Valued.v y := fun x y =>
    ValuativeRel.isEquiv (valuation (w.1.adicCompletion E)) Valued.v x y
  have hlt : ∀ x : w.1.adicCompletion E, valuation _ x < 1 ↔ Valued.v x < 1 := fun x =>
    (ValuativeRel.isEquiv (valuation (w.1.adicCompletion E)) Valued.v).lt_one_iff_lt_one
  have hval : ValuativeExtension (v.adicCompletion F) (w.1.adicCompletion E) := ⟨fun {a b} => by
    change Valued.v (completionMap v w.1 a) ≤ Valued.v (completionMap v w.1 b) ↔ Valued.v a ≤ Valued.v b
    rw [valued_completionMap, valued_completionMap]
    exact pow_le_pow_iff_left₀ zero_le zero_le he0⟩
  let Φ : (E ≃ₐ[F] E) →* (w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E) :=
    MonoidHom.mk' (fun τ => galEquiv v τ w.1 w.1 (hfix τ)) fun a b => AlgEquiv.ext fun y => by
      refine congrFun ((HeightOneSpectrum.denseRange_algebraMap E w.1).equalizer
        (continuous_galEquiv v (a * b) w.1 w.1 (hfix _))
        ((continuous_galEquiv v a w.1 w.1 (hfix _)).comp (continuous_galEquiv v b w.1 w.1 (hfix _))) ?_) y
      funext x
      simp only [Function.comp_apply, galEquiv_algebraMap, AlgEquiv.mul_apply]
  have hinj : Function.Injective Φ := fun a b h => AlgEquiv.ext fun x => by
    have h1 := DFunLike.congr_fun h (algebraMap E (w.1.adicCompletion E) x)
    change galEquiv v a w.1 w.1 (hfix _) _ = galEquiv v b w.1 w.1 (hfix _) _ at h1
    rw [galEquiv_algebraMap, galEquiv_algebraMap] at h1
    exact (algebraMap E (w.1.adicCompletion E)).injective h1
  have hc : Nat.card (w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E) = Nat.card (E ≃ₐ[F] E) := by
    refine le_antisymm ?_ (Nat.card_le_card_of_injective Φ hinj)
    rw [IsGalois.card_aut_eq_finrank F E, ← hrk, Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  have hgal : IsGalois (v.adicCompletion F) (w.1.adicCompletion E) :=
    IsGalois.of_card_aut_eq_finrank _ _ (by rw [hc, IsGalois.card_aut_eq_finrank F E, hrk])
  have hsurj : Function.Surjective Φ := ((Nat.bijective_iff_injective_and_card Φ).2 ⟨hinj, hc.symm⟩).2
  refine ⟨inferInstance, hval, hfin, hgal, Φ σ, fun τ => ?_, hrk, fun x => rfl, fun y => ?_, fun hu => ?_⟩
  · obtain ⟨a, rfl⟩ := hsurj τ
    obtain ⟨j, rfl⟩ := hσ a
    exact ⟨j, (map_zpow Φ σ j).symm⟩
  · obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
    have h1 : galFin σ v (tensorEquiv' E v t) =
        tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F (v.adicCompletion F)) t) := by
      simp [galFin, galOf]
    rw [h1]
    clear h1
    induction t with
    | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]
    | tmul x a =>
      rw [Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul, Pi.mul_apply, Pi.mul_apply, map_mul]
      congr 1
      · exact (galEquiv_algebraMap v σ w.1 w.1 (hfix σ) x).symm
      · exact ((Φ σ).commutes a).symm
  · have := w.1.isPrime
    have he : w.1.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one_iff.2 hu
    obtain ⟨π, hπ⟩ := valued_adicCompletion_surjective (K := F) v (WithZero.exp (-1 : ℤ))
    have h1 : Valued.v (algebraMap (v.adicCompletion F) (w.1.adicCompletion E) π) = WithZero.exp (-1 : ℤ) := by
      rw [algebraMap_completion_eq, valued_completionMap, he, pow_one, hπ]
    refine ⟨π, (hlt _).2 (by rw [h1, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega), fun x hx => (hle _ _).2 ?_⟩
    rw [h1]
    have h2 := (hlt x).1 hx
    by_cases h0 : Valued.v x = 0
    · rw [h0]; exact zero_le
    · rw [← WithZero.exp_log h0] at h2 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
      rw [WithZero.exp_le_exp]
      omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.PlaceOfLocal
open MeasureTheory NumberField IsDedekindDomain PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)
open scoped ENNReal

private theorem cent_facts (hCC : CentComm) {k : Type} [Field k] [TopologicalSpace k] {n : ℕ} [T2Space (GL (Fin n) k)]
    [ContinuousMul (GL (Fin n) k)] {γ : GL (Fin n) k} (hγ : IsRegSemisimple γ) :
    IsClosed ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) ∧
    ∀ a ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)), ∀ b ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)),
        Commute a b := by
  refine ⟨?_, fun a ha b hb => ?_⟩
  · have : ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = {x | x * γ = γ * x} := by
      ext x; simp [Subgroup.mem_centralizer_singleton_iff, Commute, SemiconjBy]
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  · rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
    exact Units.ext (hCC k n γ a b hγ (congrArg Units.val ha) (congrArg Units.val hb))

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets in
private theorem key (hT : GLTop) (hC : ExtCont) (hCC : CentComm) (hH : HaarComm) (hI : TwCentImg) (hG : GeoOfMatch) (hX : GeoTransport)
    (hA : AlongIndep) (k E S : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (s : E ≃ₐ[k] E) (hs : ∀ τ, τ ∈ Subgroup.zpowers s)
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (e : S ≃+* E) (he : Continuous e) (he' : Continuous e.symm)
    (ι : k →+* S) (t₀ : S →+* S) (h1 : ∀ x, e (ι x) = algebraMap k E x) (h2 : ∀ y, e (t₀ y) = (s : E →+* E) (e y))
    (n : ℕ) [MeasurableSpace (GL (Fin n) S)] [BorelSpace (GL (Fin n) S)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
    (mE : Measure (GL (Fin n) S)) (mF : Measure (GL (Fin n) k)) (hE : mE.IsHaarMeasure) (hF : mF.IsHaarMeasure)
    [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] :
    (mE.map (mapGL n (e : S →+* E))).IsHaarMeasure ∧ ∀ φ ∈ SB (GL (Fin n) E), ∀ f ∈ SB (GL (Fin n) k),
      Match s (mE.map (mapGL n (e : S →+* E))) mF φ f →
      PositivityTheory.Rg.Tf.Geo.Match ι t₀ (Module.finrank k E) mE mF 1 (fun g => φ (mapGL n (e : S →+* E) g)) f := by
  obtain ⟨x1, x2⟩ := hX _ _ _ e he he' ι (algebraMap k E) t₀ (s : E →+* E) h1 h2 n (Module.finrank k E) mE mF
  have hμ := x1 hE
  refine ⟨hμ, fun φ hφ f hf hM γ hγ ν hν => ?_⟩
  have hM' := hG k E s hs n _ mF hμ hF φ hφ f hf hM γ hγ ν hν
  obtain ⟨y1, y2⟩ := x2 γ
  have hl : ∀ x, mapGL n (e.symm : E →+* S) (mapGL n (e : S →+* E) x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => e.symm_apply_apply _)
  have hrt : ∀ x, mapGL n (e : S →+* E) (mapGL n (e.symm : E →+* S) x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => e.apply_symm_apply _)
  refine ⟨fun δ hδ => ?_, fun hn => hM'.2 fun ⟨δ', h'⟩ => hn ⟨mapGL n (e.symm : E →+* S) δ', (y1 _).2 (by rw [hrt]; exact h')⟩⟩
  have hδ' := (y1 δ).1 hδ
  rw [← hM'.1 _ hδ']
  obtain ⟨a1, a2, a3, -⟩ := hT E n
  obtain ⟨b1, b2, b3, -⟩ := hT k n
  obtain ⟨c1, c2⟩ := cent_facts hCC hγ
  obtain ⟨s1, s2, -⟩ := hH _ _ c1 c2 ν hν
  obtain ⟨d1, d2⟩ := (hC k E).2.2 n
  set δ' := mapGL n (e : S →+* E) δ with hδe
  have hS := (hI k E s hs n δ' γ hγ hδ').2
  let Φ : GL (Fin n) E → ℂ := fun x => φ (twConj (sigmaGL s) x δ')
  have hΦc : Continuous Φ := hφ.1.continuous.comp ((continuous_inv.mul continuous_const).mul (d2 s))
  have hΦe : ∀ x, φ (mapGL n (e : S →+* E) (x⁻¹ * δ * mapGL n t₀ x)) =
      Φ (mapGL n (e : S →+* E) x) := fun x => by
    rw [map_mul, map_mul, map_inv]
    refine congrArg (fun z => φ ((mapGL n (e : S →+* E) x)⁻¹ * δ' * z)) (?_ : mapGL n (e : S →+* E) (mapGL n t₀ x) = sigmaGL s (mapGL n (e : S →+* E) x))
    exact Units.ext (Matrix.ext fun i j => h2 _)
  unfold PositivityTheory.Rg.Tf.Geo.twOrb
  simp only [hΦe]
  by_cases hex : ∃ ρ, PositivityTheory.Rg.Tf.Geo.IsNormAlong id
      (fun t : Subgroup.centralizer {γ} => mapGL n ι (t : GL (Fin n) k)) ν ρ
  · have hρ := (y2 ν fun g => hex.choose (mapGL n (e.symm : E →+* S) g)).1.2 (by simp only [hl]; exact hex.choose_spec)
    haveI : MeasurableInv (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) :=
      ⟨(measurable_subtype_coe.inv).subtype_mk⟩
    have k1 := hA _ _ (mE.map (mapGL n (e : S →+* E))) ν
      ((incl : GL (Fin n) k →* GL (Fin n) E).comp (Subgroup.centralizer {γ}).subtype)
      (d1.measurable.comp measurable_subtype_coe) Φ hΦc.measurable
      (fun t g => congrArg φ (twConj_mul_left _ _ (hS ▸ ⟨t, t.2, rfl⟩) g)) _ hρ
    refine Eq.trans ?_ k1.symm
    rw [(y2 ν _).2, PositivityTheory.Rg.Tf.Geo.quotInt, dite_eq_left hex]
    simp only [hl, id]
  · rw [PositivityTheory.Rg.Tf.Geo.quotInt, dite_eq_right hex, PositivityTheory.Rg.Tf.Geo.quotInt, dite_eq_right fun ⟨ρ', h'⟩ => hex ⟨_, (y2 ν ρ').1.1 h'⟩]

theorem UpperTheory.V.Z.Tf.Orb.placeOfLocal :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.TwCentImg → UpperTheory.V.Z.Tf.Orb.GeoOfMatch → UpperTheory.V.Z.Tf.Orb.GeoTransport → UpperTheory.V.Z.Tf.Orb.AlongIndep → UpperTheory.V.Z.Tf.Orb.PlaceOfLocal := by
  intro hT hC hCC hH hI hG hX hA F E _ _ _ _ _ _ σ hσ v w hw i1 i2 i3 i4 s hs hr h1 h2 n _ _ _ _ mE mF hE hF _ _
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
  let e : CompletionsOver E v ≃+* w.1.adicCompletion E := RingEquiv.piUnique fun u : PlacesOver E v => u.1.adicCompletion E
  have he : Continuous e := continuous_apply w
  have he' : Continuous e.symm := (Homeomorph.piUnique fun u : PlacesOver E v => u.1.adicCompletion E).symm.continuous
  rw [← hr]
  exact @key hT hC hCC hH hI hG hX hA _ _ _ _ _ _ _ _ _ _ _ _ i1 i2 i3 i4 s hs _ _ _ e he he' _ _ h1 h2 n _ _ _ _ mE mF hE hF _ _
end
