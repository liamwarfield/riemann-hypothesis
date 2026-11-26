module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCSDOfIsEtaT
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DimZ1fCrystallineDeformation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LiftChart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpLiftL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OnCompSelf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TangentSpaceDeformationAtL

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem UpperTheory.V.Loc.laCyc :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → IsWtPart h ((cycBar F Ω l).comp (Dec (F := F) A).subtype) (fun _ => -1) 1 := by
  intro H F Ω _ _ _ _ _ l _ A w h _
  refine ⟨by simp, fun a ha σ => ?_⟩
  obtain ⟨art, hart⟩ := H F Ω
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨μ, hμ, hL⟩ := hart.exists_isLAdicOf ι (CharAboveModel.absPow_isAlgPos F 1)
  have e : μ = cycBar F Ω l ^ 1 := CharAboveModel.eq_cyc_pow hart hμ hL
  rw [pow_one] at e
  subst e
  have h1 := hL.loc (a (ineIncl h σ)) _ (ha.glob art hart (ineIncl h σ))
  have hu : Formalism.L2.Host.IsUnitAt w (a (ineIncl h σ)) := by
    have h2 := ha.ord_eq (ineIncl h σ)
    rw [deg_ineIncl, neg_zero] at h2
    haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion F))
      (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.1
      (GlobalTheory.SmGL.ord_eq_zero_iff.1 h2)
  rw [(Model.absPow_isAbsPow F (1 : ℕ)).1 w _ hu] at h1
  simp only [Units.val_one, map_one, one_mul, locPow] at h1
  simpa using h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteEmb
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem finite_emb {F : Type} [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (w : Plc F) :
    Finite (Emb l w) := by
  refine Finite.of_injective
    (fun j : Emb l w => (j.1.comp (algebraMap F (w.adicCompletion F)) : F →+* Qbar l)) fun j j' hjj => ?_
  refine Subtype.ext (DFunLike.coe_injective ?_)
  refine (HeightOneSpectrum.denseRange_algebraMap (K := F) (v := w)).equalizer j.2 j'.2 ?_
  funext x
  exact DFunLike.congr_fun hjj x

private theorem wt_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w)
    (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ)
    (ho : IsOpen (ph.ker : Set ↥(Ine (F := F) A)))
    (H : ∀ σ : ↥(Ine (F := F) A), κ (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ)) * ph σ = 1) :
    IsWtPart h κ 0 ph :=
  ⟨ho, fun a _ σ => by rw [H]; simp⟩

private theorem wt_mul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w}
    {κ κ' : ↥(Dec (F := F) A) →* (Qbar l)ˣ} {wt wt' : Emb l w → ℤ} {ph ph' : ↥(Ine (F := F) A) →* (Qbar l)ˣ}
    (H : IsWtPart h κ wt ph) (H' : IsWtPart h κ' wt' ph') : IsWtPart h (κ * κ') (wt + wt') (ph * ph') := by
  haveI := finite_emb l w
  haveI := Fintype.ofFinite (Emb l w)
  refine ⟨?_, fun a ha σ => ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := ph.ker ⊓ ph'.ker) (fun x hx => ?_) (H.1.inter H'.1)
    have h1 : ph x = 1 := hx.1
    have h2 : ph' x = 1 := hx.2
    simp [MonoidHom.mem_ker, h1, h2]
  · have h1 := H.2 a ha σ
    have h2 := H'.2 a ha σ
    rw [finprod_eq_prod_of_fintype] at h1 h2 ⊢
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, mul_mul_mul_comm, Units.val_mul, h1, h2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Pi.add_apply, neg_add, zpow_add₀ ((map_ne_zero τ.1).2 (Units.ne_zero _))]

private theorem wt_zpow {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w}
    {κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ} {wt : Emb l w → ℤ} {ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ}
    (H : IsWtPart h κ wt ph) (m : ℤ) : IsWtPart h (κ ^ m) (m • wt) (ph ^ m) := by
  haveI := finite_emb l w
  haveI := Fintype.ofFinite (Emb l w)
  refine ⟨?_, fun a ha σ => ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := ph.ker) (fun x hx => ?_) H.1
    have h1 : ph x = 1 := hx
    rw [MonoidHom.mem_ker, MonoidHom.zpow_apply, h1, one_zpow]
  · have h1 := H.2 a ha σ
    rw [finprod_eq_prod_of_fintype] at h1 ⊢
    rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, ← mul_zpow, Units.val_zpow_eq_zpow_val, h1, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← zpow_mul, Pi.smul_apply, smul_eq_mul, neg_mul, mul_comm]

theorem UpperTheory.V.Loc.laMul :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), (∀ (κ κ' : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (wt wt' : Emb l w → ℤ) (ph ph' : ↥(Ine (F := F) A) →* (Qbar l)ˣ), IsWtPart h κ wt ph → IsWtPart h κ' wt' ph' → IsWtPart h (κ * κ') (wt + wt') (ph * ph') ∧ IsWtPart h κ⁻¹ (-wt) ph⁻¹) ∧ (∀ (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (wt : Emb l w → ℤ) (ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ) (m : ℤ), IsWtPart h κ wt ph → IsWtPart h (κ ^ m) (m • wt) (ph ^ m)) ∧ ∀ (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ), IsOpen (ph.ker : Set ↥(Ine (F := F) A)) → (∀ σ : ↥(Ine (F := F) A), κ (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ)) * ph σ = 1) → IsWtPart h κ 0 ph := by
  intro F Ω _ _ _ _ _ l _ A w h
  refine ⟨fun κ κ' wt wt' ph ph' H H' => ⟨wt_mul H H', ?_⟩, fun κ wt ph m H => wt_zpow H m, wt_one h⟩
  simpa only [zpow_neg_one, neg_smul, one_smul] using wt_zpow H (-1)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaHecke
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

theorem UpperTheory.V.Loc.laHecke :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) (art : Neutral.B1.Ideles F →* Gab F Ω), IsGlobalArtin art → ∀ (ι : Qbar l ≃+* ℂ) (χ : Formalism.L2.Host.HChar F) (n : (F →+* ℂ) → ℤ) (μ : G F Ω →* (Qbar l)ˣ), IsLAdicOf art ι χ n μ → (∃ a, IsLocalArtin h a) → IsLocAlg h (μ.comp (Dec (F := F) A).subtype) fun τ => -n ((ι.toRingHom.comp τ.1).comp (algebraMap F (w.adicCompletion F))) := by
  intro F Ω _ _ _ _ _ l _ A w h art hart ι χ n μ hμ ⟨a0, ha0⟩
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' F Ω art hart w
  have hs : GlobalTheory.SmGL.IsSmoothChar (χ.loc w) := GlobalTheory.HeckeComp.smooth_loc χ w
  let φ : Ine (F := F) A →* ℂˣ := ((χ.loc w).comp a0).comp (ineIncl h)
  have hφ : IsOpen (φ.ker : Set (Ine (F := F) A)) := IsOpen.preimage ha0.cont hs
  refine ⟨((Units.map ι.symm.toRingHom.toMonoidHom).comp φ)⁻¹, ?_, fun a ha σ => ?_⟩
  · refine Subgroup.isOpen_mono (fun x hx => ?_) hφ
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [MonoidHom.inv_apply, MonoidHom.comp_apply, hx, map_one, inv_one]
  · have e : a (ineIncl h σ) = a0 (ineIncl h σ) :=
      hinj ((ha.glob art hart _).trans (ha0.glob art hart _).symm)
    have h1 := hμ.loc (a0 (ineIncl h σ)) _ (ha0.glob art hart _)
    have h0 : ι.symm ((χ.loc w (a0 (ineIncl h σ)) : ℂˣ) : ℂ) ≠ 0 := (map_ne_zero ι.symm).2 (Units.ne_zero _)
    rw [e, Units.val_mul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    simp only [neg_neg]
    show ((μ (ineIncl h σ : Weil h) : (Qbar l)ˣ) : Qbar l) * (ι.symm ((χ.loc w (a0 (ineIncl h σ)) : ℂˣ) : ℂ))⁻¹ = locPow ι n w (a0 (ineIncl h σ))
    rw [h1, mul_comm, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArtin
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem isSmoothChar_of_comp' {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} (hs : Function.Surjective a)
    (hc : Continuous fun σ : Ine (F := E) A => a (ineIncl h σ))
    (ho : ∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) {χ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hχ : WeilDeligne.IsSmooth (χ.comp a)) : IsSmoothChar χ := by
  haveI : CompactSpace (Ine (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  have hK : IsOpen {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1} := hχ
  have hC : IsClosed ((fun σ : Ine (F := E) A => a (ineIncl h σ)) ''
      {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1}ᶜ) :=
    (hK.isClosed_compl.isCompact.image hc).isClosed
  have hU : {x : (w.adicCompletion E)ˣ | valuation (w.adicCompletion E) (x : w.adicCompletion E) = 1} ∈ nhds 1 := by
    have h1 : {x : w.adicCompletion E | valuation (w.adicCompletion E) (x - 1) < 1} ∈ nhds 1 := by
      rw [IsValuativeTopology.mem_nhds_iff]
      exact ⟨1, fun z hz => by simpa [neg_add_eq_sub] using hz⟩
    have h2 := Units.continuous_val.continuousAt (x := (1 : (w.adicCompletion E)ˣ)) h1
    refine Filter.mem_of_superset h2 fun x hx => ?_
    have h3 : valuation (w.adicCompletion E) ((x : w.adicCompletion E) - 1) < 1 := hx
    have := Valuation.map_one_add_of_lt _ h3
    simpa using this
  refine Subgroup.isOpen_of_mem_nhds χ.ker (g := 1) ?_
  have h1 : (1 : (w.adicCompletion E)ˣ) ∈ ((fun σ : Ine (F := E) A => a (ineIncl h σ)) ''
      {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1}ᶜ)ᶜ := by
    rintro ⟨σ, hσ, e⟩
    refine hσ ?_
    have e' : a (ineIncl h σ) = 1 := e
    simp [e']
  refine Filter.mem_of_superset (Filter.inter_mem hU (hC.isOpen_compl.mem_nhds h1)) ?_
  rintro x ⟨hx, hx'⟩
  obtain ⟨σ, rfl⟩ := hs x
  have h0 : deg σ = 0 := by
    have := ho σ
    rw [ord_eq_zero_iff.2 hx] at this
    omega
  by_contra hn
  exact hx' ⟨⟨σ, deg_eq_zero_iff.mp h0⟩, hn, rfl⟩

end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

theorem UpperTheory.V.Loc.laArtin :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), ∃ a, IsLocalArtin h a := by
  intro hG E Ω _ _ _ _ _ A w h
  obtain ⟨art, hart⟩ := hG E Ω
  obtain ⟨a, hs, ho, hg⟩ := GlobalTheory.InvLocalArtin.exists_invLocalArtin E Ω A w h art hart
  have hc := GlobalTheory.ArtinInvCont.continuous_inv_on_ine E Ω A w h art a hart ho hg
  refine ⟨a, hs, hc, ho, fun ξ hξ => ?_, fun art' hart' => ?_⟩
  · have hker : a.ker ≤ ξ.ker := fun σ hσ => by
      refine GlobalTheory.WeilCharKer.apply_eq_one_of_toAb_eq_one E Ω A w h ξ hξ σ ?_
      rw [← hg σ, MonoidHom.mem_ker.1 hσ, map_one, map_one]
    have e : ξ = (a.liftOfSurjective hs ⟨ξ, hker⟩).comp a :=
      (MonoidHom.liftOfRightInverse_comp a _ (Function.rightInverse_surjInv hs) ⟨ξ, hker⟩).symm
    exact ⟨_, isSmoothChar_of_comp' hs hc ho (e ▸ hξ), e⟩
  · rw [GlobalTheory.ArtinUniq.globalArtin_unique E Ω art' art hart' hart]
    exact hg
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaWDDefs
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

def UpperTheory.V.Loc.HasLT {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (ι : Qbar l ≃+* ℂ)
    (wt : Emb l w → ℤ) (a : Weil h →* (w.adicCompletion F)ˣ) : Prop :=
  ∃ (μ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ξ : Weil h →* ℂˣ), Continuous μ ∧ IsSmooth ξ ∧
    GlobalTheory.Pst.IsPstAt (UpperTheory.V.Loc.PP l) Bw (GlobalTheory.TripleGal.rk1 μ) ∧
    (∀ σ, (ξ σ : ℂ) = ι ((μ (Subgroup.inclusion (Weil_le_Dec h) σ) : Qbar l) *
      ∏ᶠ τ : Emb l w, τ.1 (a σ : w.adicCompletion F) ^ wt τ)) ∧
    ∀ σ, (ξ σ : ℂ) ∈ (GlobalTheory.Pst.wdAt (UpperTheory.V.Loc.PP l) ι Bw h hj (GlobalTheory.TripleGal.rk1 μ)).eig σ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PotCrysOf
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

private theorem cr_transport {l : ℕ} [Fact l.Prime] {G G' A V : Type} [Group G] [Group G'] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]
    {φ : G →* GQ l} {ρ : Representation A G V} {φ' : G' →* GQ l} {ρ' : Representation A G' V}
    (e : G → G') (he : Function.Surjective e) (h1 : ∀ g, φ' (e g) = φ g)
    (h2 : ∀ g x, ρ' (e g) x = ρ g x) : IsCr φ ρ → IsCr φ' ρ' := by
  have hr : φ.range = φ'.range := by
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨e g, h1 g⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨g, rfl⟩ := he g
      exact ⟨g, (h1 g).symm⟩
  have hρ : ∀ g, resCoef ℚ_[l] ρ' (e g) = resCoef ℚ_[l] ρ g := fun g => LinearMap.ext fun x => h2 g x
  have hc : Dcr φ (resCoef ℚ_[l] ρ) = Dcr φ' (resCoef ℚ_[l] ρ') := by
    unfold Dcr
    rw [he.iInf_comp (fun g => LinearMap.ker (actC φ' (resCoef ℚ_[l] ρ') g - LinearMap.id)) |>.symm]
    refine iInf_congr fun g => ?_
    unfold actC
    rw [hρ, h1]
  unfold IsCr
  rw [hr, hc]
  exact id

private theorem crys_of_isCr {l : ℕ} [Fact l.Prime] (K E' : FinExt l) {n : ℕ}
    (ρ : Representation ↥E'.1 ↥(GK K) (Fin n → ↥E'.1)) (h : IsCr (GK K).subtype ρ) :
    Formalism.WeaklyAdmissibleFiltrations.IsCrys ((PP l).PD K) ρ := by
  have := E'.2
  have : IsModuleTopology ℚ_[l] (Fin n → ↥E'.1) := isModuleTopologyOfFiniteDimensional
  exact (isCrField K ρ).1.1 ((isCrIff K ρ).1.1 h)

private theorem ex_bridge {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} (j : Ω →+* Om l) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) :
    ∃ (L : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL L)), Bw.j = j ∧
      Bw.Kw.1 = IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)) := by
  let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap E Ω))⟩
  have := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := E) hj K rfl
  exact ⟨⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩,
    { Kw := K
      j := j
      j_E := fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
      j_dense := GlobalTheory.PlaceBridge.adjoin_range_subset_closure (j.comp (algebraMap E Ω))
      e := e
      e_cont := he
      e_symm_cont := he'
      e_comm := hec
      LL := ⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩
      LL_split := fun τ x => AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩
      eO := RingEquiv.refl _
      eO_alg := fun _ => rfl
      eO_cont := continuous_id
      eO_symm_cont := continuous_id }, rfl, rfl⟩

theorem UpperTheory.V.Loc.potCrysOf :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (j : Ω →+* Om l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →* GQ l) (ψ : H →* G F Ω), IsOpenEmbedding φ → (∀ h y, φ h (j y) = j (ψ h y)) → ∀ {n : ℕ} (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ (E' : FinExt l) (r' : H →* GL (Fin n) ↥E'.1), (∀ h a b, (((r' h : Matrix (Fin n) (Fin n) ↥E'.1) a b : ↥E'.1) : Om l) = (r (ψ h) : Matrix (Fin n) (Fin n) (Qbar l)) a b) → IsCr φ (colRep r') → UpperTheory.V.Af.PotCrysAt r (placeJ j) := by
  intro F Ω _ _ _ _ _ _ l _ j H _ _ _ φ ψ hφ hφψ n r hr E' r' hr' hcr
  have hj : ∀ x, x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := fun x => by
    change Valued.v (j x) ≤ 1 ↔ _
    rw [PadicAlgCl.valuation_def]
    exact Iff.rfl
  obtain ⟨L, Bw, hBj, hK⟩ := ex_bridge (E := F) j hj
  refine ⟨↥(OL L), inferInstance, inferInstance, inferInstance, Bw, fun x => by rw [hBj]; exact hj x, ?_⟩
  haveI : CompactSpace ↥(GK Bw.Kw) := by
    haveI := Bw.Kw.2
    exact isCompact_iff_compactSpace.1 Bw.Kw.1.fixingSubgroup_isClosed.isCompact
  haveI : CompactSpace ↥(Dec (F := F) (placeJ j)) :=
    Bw.e.symm.surjective.compactSpace Bw.e_symm_cont
  haveI : T2Space ↥(Dec (F := F) (placeJ j)) := inferInstance
  let r₀ := r.comp (Dec (F := F) (placeJ j)).subtype
  have hc0 : Continuous fun g => ((r₀ g : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) :=
    Units.continuous_val.comp (hr.comp continuous_subtype_val)
  obtain ⟨LL, hL, hent⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l _ n r₀ hc0 (GlobalTheory.Pst.supExt Bw.LL E')
  obtain ⟨r₁, hr₁⟩ := GlobalTheory.CompactRepField.exists_hom_of_entries_mem r₀ LL.1 hent
  have l₁ : Bw.LL.1 ≤ LL.1 := le_trans le_sup_left hL
  have l₂ : E'.1 ≤ LL.1 := le_trans le_sup_right hL
  refine ⟨LL, r₁, ⟨l₁, ?_⟩, ?_⟩
  · ext g a b
    exact hr₁ g a b
  obtain ⟨K, e, -, -, he, hKr, -, -⟩ := openField φ hφ
  have he' : ∀ g, ((e g : ↥(GK K)) : GQ l) = φ g := fun g => DFunLike.congr_fun he g
  have hle : GK K ≤ GK Bw.Kw := by
    rw [← hKr]
    rintro _ ⟨g, rfl⟩
    rw [GlobalTheory.PlaceBridge.mem_GK_iff Bw.Kw hK]
    intro x
    rw [hφψ, AlgEquiv.commutes]
  have h : Bw.Kw.1 ≤ K.1 := by
    have : IsGalois ℚ_[l] (Om l) := inferInstance
    rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, ← InfiniteGalois.fixedField_fixingSubgroup Bw.Kw.1]
    exact IntermediateField.fixedField_le hle
  refine ⟨K, h, ?_⟩
  let ρK : Representation ↥E'.1 ↥(GK K) (Fin n → ↥E'.1) := (colRep r').comp e.symm.toMonoidHom
  have t1 : IsCr (GK K).subtype ρK := cr_transport e e.surjective he' (fun g x => by simp [ρK]) hcr
  have t2 := crys_of_isCr K E' ρK t1
  let _ : Algebra ↥E'.1 ↥LL.1 := (IntermediateField.inclusion l₂).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥E'.1 ↥LL.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := LL.2
  have : FiniteDimensional ↥E'.1 ↥LL.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  refine (GlobalTheory.Pst.isCrys_ext_iff _ (ρ := ρK) fun g => ⟨r' (e.symm g), fun _ => rfl, fun x => ?_⟩).2 t2
  have hg : ((Bw.e.symm (Subgroup.inclusion (GK_le h) g) : ↥(Dec (F := F) (placeJ j))) : G F Ω) = ψ (e.symm g) := by
    apply AlgEquiv.ext
    intro y
    apply j.injective
    have h1 := Bw.e_comm (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) y
    rw [hBj, MulEquiv.apply_symm_apply] at h1
    rw [← h1, ← hφψ, ← he', MulEquiv.apply_symm_apply]
    rfl
  have hM : (r₁ (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) : Matrix (Fin n) (Fin n) ↥LL.1) =
      (r' (e.symm g) : Matrix (Fin n) (Fin n) ↥E'.1).map (algebraMap ↥E'.1 ↥LL.1) := by
    ext a b
    rw [hr₁]
    refine Eq.trans ?_ (hr' (e.symm g) a b).symm
    rw [← hg]
    rfl
  rw [← hM]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaExists
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W
open Topology Pointwise

private theorem ext_dense {W D B : Type} [Group W] [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
    [CompactSpace D] [T2Space D] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]
    (i : W →* D) (hi : DenseRange i) (χ : W →* B) (C : Set B) (hC : IsCompact C) (hχ : ∀ σ, χ σ ∈ C)
    (h1 : ∀ V ∈ 𝓝 (1 : B), ∃ U ∈ 𝓝 (1 : D), ∀ σ, i σ ∈ U → χ σ ∈ V) :
    ∃! κ : D →* B, Continuous κ ∧ ∀ σ, κ (i σ) = χ σ := by
  let Γ : Subgroup (D × B) := (i.prod χ).range.topologicalClosure
  have hΓ : IsCompact (Γ : Set (D × B)) := by
    refine (isCompact_univ.prod hC).of_isClosed_subset (Subgroup.isClosed_topologicalClosure _) ?_
    refine closure_minimal ?_ (isCompact_univ.prod hC).isClosed
    rintro _ ⟨σ, rfl⟩
    exact ⟨trivial, hχ σ⟩
  haveI : CompactSpace Γ := isCompact_iff_compactSpace.1 hΓ
  let p : Γ →* D := (MonoidHom.fst D B).comp Γ.subtype
  have hp : Continuous p := continuous_fst.comp continuous_subtype_val
  have hmem : ∀ σ, (i σ, χ σ) ∈ Γ := fun σ => Subgroup.le_topologicalClosure _ ⟨σ, rfl⟩
  have hinj : Function.Injective p := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨d, k⟩, hk⟩ hd
    obtain rfl : d = 1 := hd
    by_contra hne
    have hk1 : (1 : B) ≠ k := by
      rintro rfl
      exact hne rfl
    obtain ⟨V, V', hV, hV', hVV⟩ := t2_separation_nhds hk1
    obtain ⟨U, hU, H⟩ := h1 V hV
    obtain ⟨_, ⟨h2, h3⟩, σ, rfl⟩ := mem_closure_iff_nhds.1 hk _ (prod_mem_nhds hU hV')
    exact Set.disjoint_left.1 hVV (H σ h2) h3
  have hsurj : Function.Surjective p := by
    have h2 : IsClosed (Set.range p) := (isCompact_range hp).isClosed
    have h3 : Set.range i ⊆ Set.range p := by
      rintro _ ⟨σ, rfl⟩
      exact ⟨⟨_, hmem σ⟩, rfl⟩
    intro d
    exact closure_minimal h3 h2 (hi d)
  let e : Γ ≃* D := MulEquiv.ofBijective p ⟨hinj, hsurj⟩
  have he : Continuous e.symm := Continuous.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) hp
  refine ⟨((MonoidHom.snd D B).comp Γ.subtype).comp e.symm.toMonoidHom,
    ⟨continuous_snd.comp (continuous_subtype_val.comp he), fun σ => ?_⟩, ?_⟩
  · have : e.symm (i σ) = ⟨_, hmem σ⟩ := e.symm_apply_eq.2 rfl
    show (e.symm (i σ)).1.2 = _
    rw [this]
  · rintro κ ⟨hκ, H⟩
    refine DFunLike.coe_injective (hi.equalizer hκ (continuous_snd.comp (continuous_subtype_val.comp he)) ?_)
    funext σ
    have : e.symm (i σ) = ⟨_, hmem σ⟩ := e.symm_apply_eq.2 rfl
    show κ (i σ) = (e.symm (i σ)).1.2
    rw [this, H]

private def ballSub (l : ℕ) [Fact l.Prime] (ε : ℝ) (hε : 0 < ε) : Subgroup (Qbar l)ˣ where
  carrier := {x | ‖(x : Qbar l)‖ = 1 ∧ ‖(x : Qbar l) - 1‖ < ε}
  one_mem' := by simpa using hε
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by simp [hx, hy], ?_⟩
    have e : ((x * y : (Qbar l)ˣ) : Qbar l) - 1 = x * (y - 1) + (x - 1) := by push_cast; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hx')
    rwa [norm_mul, hx, one_mul]
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨by simp [hx], ?_⟩
    have e : ((x⁻¹ : (Qbar l)ˣ) : Qbar l) - 1 = -((x : Qbar l)⁻¹ * (x - 1)) := by
      have := x.ne_zero
      push_cast; field_simp; ring
    rwa [e, norm_neg, norm_mul, norm_inv, hx, inv_one, one_mul]

private theorem exists_compact {l : ℕ} [Fact l.Prime] (u : (Qbar l)ˣ) (hu : ‖(u : Qbar l)‖ = 1) :
    ∃ C : Subgroup (Qbar l)ˣ, IsCompact (C : Set (Qbar l)ˣ) ∧ u ∈ C ∧ ∀ x ∈ C, ‖(x : Qbar l)‖ = 1 := by
  let L : IntermediateField ℚ_[l] (Qbar l) := IntermediateField.adjoin ℚ_[l] {(u : Qbar l)}
  haveI : FiniteDimensional ℚ_[l] L := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  let C : Subgroup (Qbar l)ˣ :=
    { carrier := {x | (x : Qbar l) ∈ L ∧ ‖(x : Qbar l)‖ = 1}
      one_mem' := ⟨by simpa using L.one_mem, by simp⟩
      mul_mem' := fun hx hy => ⟨L.mul_mem hx.1 hy.1, by simp [hx.2, hy.2]⟩
      inv_mem' := fun hx => ⟨by simpa using L.inv_mem hx.1, by simp [hx.2]⟩ }
  refine ⟨C, ?_, ⟨IntermediateField.mem_adjoin_simple_self _ _, hu⟩, fun x hx => hx.2⟩
  rw [Units.isEmbedding_val₀.isCompact_iff]
  haveI : FiniteDimensional ℚ_[l] L.toSubmodule := inferInstanceAs (FiniteDimensional ℚ_[l] L)
  haveI : ProperSpace L.toSubmodule := FiniteDimensional.proper ℚ_[l] _
  convert (isCompact_sphere (0 : L.toSubmodule) 1).image continuous_subtype_val using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy.1⟩, by simpa using hy.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hy' : ‖(y : Qbar l)‖ = 1 := by simpa using hy
    have h0 : (y : Qbar l) ≠ 0 := fun h => by simp [h] at hy'
    exact ⟨Units.mk0 _ h0, ⟨y.2, hy'⟩, rfl⟩

theorem UpperTheory.V.Loc.laExists :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ ξ : (w.adicCompletion F)ˣ →* (Qbar l)ˣ, Continuous ξ → (∀ x, ‖(ξ x : Qbar l)‖ = 1) → ∃! κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ, Continuous κ ∧ ∀ σ : Weil h, κ (Subgroup.inclusion (Weil_le_Dec h) σ) = ξ (a σ) := by
  intro _ F Ω _ _ _ _ _ l _ A w h a ha ξ hξ hn
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  haveI := compactSpace_Ine (E := F) A
  let χ := ξ.comp a
  have hI : Continuous fun τ : Ine (F := F) A => χ (ineIncl h τ) := hξ.comp ha.cont
  obtain ⟨C, hC, huC, hC1⟩ := exists_compact (χ (frob h)) (hn _)
  refine ext_dense (Subgroup.inclusion (Weil_le_Dec h)) ?_ χ
    ((C : Set (Qbar l)ˣ) * Set.range fun τ : Ine (F := F) A => χ (ineIncl h τ))
    (hC.mul (isCompact_range hI)) (fun σ => ?_) fun V hV => ?_
  · have h1 := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A w h
      (Subgroup.inclusion (Weil_le_Dec h) (frob h)) (isFrob_frob (h := h))
    have h2 : Subgroup.zpowers (Subgroup.inclusion (Weil_le_Dec h) (frob h)) ⊔
        (Ine (F := F) A).subgroupOf (Dec (F := F) A) ≤ (Subgroup.inclusion (Weil_le_Dec h)).range := by
      refine sup_le ?_ fun σ hσ => ⟨⟨σ, Ine_le_Weil h hσ⟩, rfl⟩
      rw [Subgroup.zpowers_le]
      exact ⟨_, rfl⟩
    intro d
    have h3 : d ∈ (⊤ : Subgroup (Dec (F := F) A)) := trivial
    rw [← h1] at h3
    exact closure_mono h2 h3
  · obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul deg_frob σ
    refine ⟨χ (frob h) ^ deg σ, C.zpow_mem huC _, _, ⟨τ, rfl⟩, ?_⟩
    conv_rhs => rw [hτ, map_mul, map_zpow]
  · rw [Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap] at hV
    obtain ⟨V', hV', hVV⟩ := hV
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV'
    let H := ballSub l ε hε
    have hH : ∀ x ∈ H, x ∈ V := fun x hx => hVV (hεV (by simpa [dist_eq_norm] using hx.2))
    have hop : IsOpen {x : (Qbar l)ˣ | ‖(x : Qbar l) - 1‖ < ε} :=
      isOpen_lt ((Units.continuous_val.sub continuous_const).norm) continuous_const
    haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC
    have hHC : IsOpen ((H.subgroupOf C : Subgroup C) : Set C) := by
      convert hop.preimage (continuous_subtype_val (p := (· ∈ C))) using 1
      ext x
      exact ⟨fun hx => hx.2, fun hx => ⟨hC1 _ x.2, hx⟩⟩
    haveI := (H.subgroupOf C).quotient_finite_of_isOpen hHC
    obtain ⟨N, hN, -, hNH⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := H.subgroupOf C)) ⟨_, huC⟩
    have hNH' : χ (frob h) ^ N ∈ H := hNH
    have hM := (hop.preimage hI).mem_nhds (x := 1) (by simpa using hε)
    rw [nhds_subtype_eq_comap, Filter.mem_comap] at hM
    obtain ⟨U, hU, hUM⟩ := hM
    obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff F Ω U).1 hU
    have hEo : IsOpen (E.fixingSubgroup : Set (G F Ω)) := E.fixingSubgroup_isOpen
    haveI := E.fixingSubgroup.quotient_finite_of_isOpen hEo
    obtain ⟨m, hm, -, hmE⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := E.fixingSubgroup)) (frob h : G F Ω)
    obtain ⟨ζ, hζ⟩ := GlobalTheory.exists_fixed_dvd_deg F Ω A w h (m * N) (Nat.mul_pos hm hN)
    have hζo : IsOpen (MulAction.stabilizer (G F Ω) ζ : Set (G F Ω)) := stabilizer_isOpen_of_isIntegral ζ
    refine ⟨_, continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((hEo.inter hζo).mem_nhds ⟨E.fixingSubgroup.one_mem, (MulAction.stabilizer (G F Ω) ζ).one_mem⟩), fun σ hσ => hH _ ?_⟩
    obtain ⟨k, hk⟩ := hζ σ hσ.2
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul deg_frob σ
    have h1 : ((frob h ^ deg σ : Weil h) : G F Ω) ∈ E.fixingSubgroup := by
      rw [hk, Subgroup.coe_zpow, Nat.cast_mul, mul_assoc, zpow_mul, zpow_natCast]
      exact E.fixingSubgroup.zpow_mem hmE _
    have h2 : (τ : G F Ω) ∈ E.fixingSubgroup := by
      have h3 : (σ : G F Ω) ∈ E.fixingSubgroup := hσ.1
      rw [hτ, Subgroup.coe_mul] at h3
      exact (E.fixingSubgroup.mul_mem_cancel_left h1).1 h3
    rw [hτ, map_mul, map_zpow]
    refine H.mul_mem ?_ ⟨hn _, hUM (hEU h2)⟩
    rw [hk, Nat.cast_mul, mul_comm (m : ℤ), mul_assoc, zpow_mul, zpow_natCast]
    exact H.zpow_mem hNH' _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FinrankLocalCocyclesAdjointUnitaryThreeEqTwelve
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

private theorem wt_cases (a b : Fin 3) : ∃ j : Fin 5, wt a b = ((j : ℕ) : ℤ) - 2 := by
  revert a b; decide

private theorem sum_dim {E G : Type} [Field E] (S : Submodule E (G → Matrix (Fin 3) (Fin 3) E))
    [Module.Finite E S]
    (h : ∀ j : ℤ, ∀ γ ∈ S, (fun g => Matrix.of fun a b => if wt a b = j then γ g a b else 0) ∈ S) :
    finrank E S = ∑ j : Fin 5,
      finrank E ↥(S ⊓ Submodule.pi Set.univ fun _ => UpperTheory.V.U3.gw E (((j : ℕ) : ℤ) - 2)) := by
  classical
  let T : Fin 5 → Submodule E (G → Matrix (Fin 3) (Fin 3) E) := fun j =>
    S ⊓ Submodule.pi Set.univ fun _ => UpperTheory.V.U3.gw E (((j : ℕ) : ℤ) - 2)
  haveI : ∀ j, Module.Finite E (T j) := fun j => Submodule.finiteDimensional_of_le (inf_le_left : T j ≤ S)
  let f : (∀ j, T j) →ₗ[E] S :=
    { toFun := fun x => ⟨∑ j, (x j : G → Matrix (Fin 3) (Fin 3) E), S.sum_mem fun j _ => (x j).2.1⟩
      map_add' := fun x y => by ext1; simp [Finset.sum_add_distrib]
      map_smul' := fun c x => by ext1; simp [Finset.smul_sum] }
  have hinj : ∀ i j : Fin 5, ((i : ℕ) : ℤ) - 2 = ((j : ℕ) : ℤ) - 2 → i = j := fun i j hij =>
    Fin.ext (by omega)
  have hval : ∀ (x : ∀ j, T j) (g : G) (a b : Fin 3) (j : Fin 5), wt a b = ((j : ℕ) : ℤ) - 2 →
      (f x : G → Matrix (Fin 3) (Fin 3) E) g a b = (x j : G → Matrix (Fin 3) (Fin 3) E) g a b := by
    intro x g a b j hj
    change (∑ j, (x j : G → Matrix (Fin 3) (Fin 3) E)) g a b = _
    rw [Finset.sum_apply, Matrix.sum_apply]
    refine Finset.sum_eq_single j (fun i _ hi => ?_) (by simp)
    exact (x i).2.2 g trivial a b fun hh => hi (hinj _ _ (hh.symm.trans hj))
  have hb : Function.Bijective f := by
    constructor
    · intro x y hxy
      funext j
      apply Subtype.ext
      funext g
      ext a b
      by_cases hj : wt a b = ((j : ℕ) : ℤ) - 2
      · rw [← hval x g a b j hj, ← hval y g a b j hj, hxy]
      · rw [(x j).2.2 g trivial a b hj, (y j).2.2 g trivial a b hj]
    · intro γ
      refine ⟨fun j => ⟨_, h (((j : ℕ) : ℤ) - 2) γ γ.2, fun g _ a b hab => ?_⟩, ?_⟩
      · simp only [Matrix.of_apply, if_neg hab]
      · apply Subtype.ext
        funext g
        ext a b
        obtain ⟨j, hj⟩ := wt_cases a b
        rw [hval _ g a b j hj]
        simp only [Matrix.of_apply, if_pos hj]
  rw [← (LinearEquiv.ofBijective f hb).finrank_eq, Module.finrank_pi_fintype]

theorem UpperTheory.finrank_local_cocycles_adjoint_unitaryThree_eq_twelve :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E], finrank E ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E))) = 12 := by
  intro hP l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ _ _
  have H := fun j => UpperTheory.V.Loc.dim_Z1f_crystalline_deformation hP D E j
  haveI := (H 0).1
  rw [sum_dim _ fun j => (H j).2.2.1, Finset.sum_congr rfl fun j _ => (H _).2.1]
  decide
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpChartL
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

section Gen

variable {R K H : Type} [CommRing R] [CommRing K] [Group H]

private theorem cl_prj (f : R →+* K) (F : M4 R →+* M4 K) (hF : ∀ (a : R) X, F (a • X) = f a • F X)
    (c : Fin 4 → R) (X : M4 R) (i : Fin 4) : prj (fun a => f (c a)) (F X) i = F (prj c X i) := by
  unfold prj
  have h : ∀ p : Polynomial R, Polynomial.aeval (F X) (p.map f) = F (Polynomial.aeval X p) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hF, map_one]
  rw [← h, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

private theorem cl_eqs (f : R →+* K) (F : M4 R →+* M4 K) (hF : ∀ (a : R) X, F (a • X) = f a • F X)
    (hadj : ∀ X, adj (F X) = F (adj X)) (hch : ∀ X : M4 R, (F X).charpoly = X.charpoly.map f)
    (I : Subgroup H) (ν : H → R) (ps : Fin 4 → H → R) (s₀ : H) (r : H →* M4 R) (r' : H →* M4 K)
    (hr : ∀ g, r' g = F (r g)) :
    ((∀ g, IsGSp (ν g) (r g)) ∧ Ord I ps s₀ r →
      (∀ g, IsGSp (f (ν g)) (r' g)) ∧ Ord I (fun i g => f (ps i g)) s₀ r') ∧
    (Function.Injective f → Function.Injective F →
      (∀ g, IsGSp (f (ν g)) (r' g)) ∧ Ord I (fun i g => f (ps i g)) s₀ r' →
      (∀ g, IsGSp (ν g) (r g)) ∧ Ord I ps s₀ r) := by
  have e0 : ∀ g, adj (r' g) * r' g = F (adj (r g) * r g) := fun g => by rw [hr, hadj, map_mul]
  have e1 : ∀ a : R, f a • (1 : M4 K) = F (a • 1) := fun a => by rw [hF, map_one]
  have e2 : (∏ j, (Polynomial.X - Polynomial.C (f (ps j s₀)))) =
      (∏ j, (Polynomial.X - Polynomial.C (ps j s₀))).map f := by
    rw [Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have e3 : ∀ i, prj (fun a => f (ps a s₀)) (r' s₀) i = F (prj (fun a => ps a s₀) (r s₀) i) := fun i => by
    rw [hr, cl_prj f F hF (fun a => ps a s₀)]
  refine ⟨fun ⟨h1, h⟩ => ⟨fun g => ?_, ?_, fun g i j hij => ?_, fun s hs i => ?_⟩,
    fun hf hi ⟨h1, h⟩ => ⟨fun g => hi ?_, Polynomial.map_injective f hf ?_, fun g i j hij => hi ?_,
      fun s hs i => hi ?_⟩⟩
  · exact (e0 g).trans ((congrArg F (h1 g)).trans (e1 _).symm)
  · rw [hr, hch, h.charpoly, e2]
  · rw [e3, e3, hr, ← map_mul, ← map_mul, h.stable g i j hij, map_zero]
  · rw [e3, hr s, e1, ← map_sub, ← map_mul, ← map_mul, h.inert s hs i, map_zero]
  · exact (e0 g).symm.trans ((h1 g).trans (e1 _))
  · rw [← hch, ← hr, h.charpoly, e2]
  · rw [map_mul, map_mul, ← e3, ← e3, ← hr, h.stable g i j hij, map_zero]
  · rw [map_mul, map_mul, map_sub, ← e3, ← hr, ← e1, h.inert s hs i, map_zero]

private theorem cl_map (f : R →+* K) (I : Subgroup H) (ν : H → R) (ps : Fin 4 → H → R) (s₀ : H) (r : H →* M4 R) :
    ((∀ g, IsGSp (ν g) (r g)) ∧ Ord I ps s₀ r →
      (∀ g, IsGSp (f (ν g)) (mapRep f r g)) ∧ Ord I (fun i g => f (ps i g)) s₀ (mapRep f r)) ∧
    (Function.Injective f →
      (∀ g, IsGSp (f (ν g)) (mapRep f r g)) ∧ Ord I (fun i g => f (ps i g)) s₀ (mapRep f r) →
      (∀ g, IsGSp (ν g) (r g)) ∧ Ord I ps s₀ r) := by
  have h := cl_eqs f f.mapMatrix (fun a X => by ext i j; simp)
    (fun X => by
      ext i j
      simp only [adj_apply, RingHom.mapMatrix_apply, Matrix.map_apply, map_zsmul])
    (fun X => Matrix.charpoly_map X f) I ν ps s₀ r (mapRep f r) fun _ => rfl
  exact ⟨h.1, fun hf => h.2 hf fun X Y e => Matrix.map_injective hf e⟩

private def cl_conj (τ : ℤ × ℤ → R) (h0 : τ 0 = 1) (hm : ∀ i j, τ (i + j) = τ i * τ j) : M4 R →+* M4 R where
  toFun X := Matrix.of fun a b => τ (wt a b) * X a b
  map_one' := by
    ext a b
    by_cases h : a = b
    · subst h
      simp [(wt_eq_zero a a).2 rfl, h0]
    · simp [Matrix.one_apply_ne h]
  map_mul' X Y := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : wt a b = wt a k + wt k b := by simp [wt]
    rw [this, hm]
    ring
  map_zero' := by ext a b; simp
  map_add' X Y := by ext a b; simp [mul_add]

private theorem cl_tor (t : Multiplicative (ℤ × ℤ) →* Rˣ) (I : Subgroup H) (ν : H → R) (ps : Fin 4 → H → R) (s₀ : H)
    (r : H →* M4 R) (h : (∀ g, IsGSp (ν g) (r g)) ∧ Ord I ps s₀ r) :
    ∃ r' : H →* M4 R, (∀ g a b, r' g a b = t (Multiplicative.ofAdd (wt a b)) * r g a b) ∧
      (∀ g, IsGSp (ν g) (r' g)) ∧ Ord I ps s₀ r' := by
  let F := cl_conj (fun j => (t (Multiplicative.ofAdd j) : R)) (by simp) (fun i j => by simp [ofAdd_add])
  have hF : ∀ X a b, F X a b = t (Multiplicative.ofAdd (wt a b)) * X a b := fun _ _ _ => rfl
  refine ⟨F.toMonoidHom.comp r, fun _ _ _ => rfl,
    (cl_eqs (RingHom.id R) F (fun a X => ?_) (fun X => ?_) (fun X => ?_) I ν ps s₀ r _ fun _ => rfl).1 h⟩
  · ext i j
    simp [hF, mul_left_comm]
  · ext i j
    simp only [adj_apply, hF, wt_rev, mul_smul_comm]
  · let d : Fin 4 → Rˣ := fun a => t (Multiplicative.ofAdd (lamW a, muW a))
    let u : (M4 R)ˣ := ⟨Matrix.diagonal fun a => d a, Matrix.diagonal fun a => ((d a)⁻¹ : Rˣ),
      by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩
    have : F X = u.val * X * u⁻¹.val := by
      ext a b
      show _ = (Matrix.diagonal (fun a => (d a : R)) * X * Matrix.diagonal fun a => (((d a)⁻¹ : Rˣ) : R)) a b
      have e : wt a b = (lamW a, muW a) - (lamW b, muW b) := rfl
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hF, e, ofAdd_sub, map_div, div_eq_mul_inv, Units.val_mul]
      ring
    rw [this, Polynomial.map_id, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end Gen

private theorem cl_count {n : ℕ} (u : Fin n → ℤ × ℤ) (h : ∀ j, Nat.card {i // u i = j} = dimsL j) : n = 14 := by
  classical
  have h1 : ∀ i, u i ∈ wts := fun i => by
    by_contra hn
    have h2 : dimsL (u i) = 0 := by
      unfold dimsL
      rw [if_neg, if_neg hn]
      rintro (e | e | e | e | e) <;> exact hn (by rw [e]; decide)
    haveI : Nonempty {k // u k = u i} := ⟨⟨i, rfl⟩⟩
    exact Nat.card_pos.ne' ((h _).trans h2)
  have h3 := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := wts) (f := u) fun i _ => h1 i
  have h4 : ∀ j, (Finset.univ.filter fun i => u i = j).card = dimsL j := fun j => by
    rw [← h j, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [h4, Finset.card_univ, Fintype.card_fin] at h3
  rw [h3]
  decide

theorem UpperTheory.V.Loc.spChartL :
    LocalPublishedTheorems → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra ↥c.O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ↥c.O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing ↥c.O E] (R : Type) [CommRing R] [Algebra ↥c.O R] [IsCO ↥c.O R] (ρ : Lift c.O (D.rbarAt l) R), Represents D.condL ρ → ∃ (x : R →ₐ[c.O] c.O) (P : Ideal R) (w : Fin 14 → ℤ × ℤ) (φ : R →ₐ[c.O] MvPowerSeries (Fin 14) E), (ρ.map x).hom = D.r0At l ∧ UpperTheory.V.Loc.IsCompl P x φ ∧ (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a = 0) ∧ (∀ j, Nat.card {i // w i = j} = dimsL j) ∧ ∀ g a b, φ (ρ.hom g a b) ∈ wtPart E w (wt a b) := by
  intro hP Ω _ _ _ l _ c D hD E _ _ _ _ _ _ _ _ R _ _ _ ρ hρ
  haveI : CompactSpace (D.Gp l) := isCompact_iff_compactSpace.1 (isClosed_Dec (F := ℚ) (D.pl l)).isCompact
  have hmap : ∀ (B B' : Type) [CommRing B] [Algebra c.O B] [CommRing B'] [Algebra c.O B'] (f : B →ₐ[c.O] B')
      (r : D.Gp l →* M4 B), (EqL D r → EqL D (mapRep (f : B →+* B') r)) ∧
        (Function.Injective f → EqL D (mapRep (f : B →+* B') r) → EqL D r) := by
    intro B B' _ _ _ _ f r
    have h := cl_map (f : B →+* B') ((D.Ip l).subgroupOf (D.Gp l)) (fun g => algebraMap c.O B (D.th g))
      (fun i g => algebraMap c.O B (D.ps i g)) D.s0 r
    have hy : ∀ a : c.O, (f : B →+* B') (algebraMap c.O B a) = algebraMap c.O B' a := fun a => f.commutes a
    simp only [hy] at h
    exact h
  obtain ⟨ρ₁, h₁, hpt⟩ := r0pt D hD
  have hr0 : (D.loc ρ₁ l).hom = D.r0At l := congrArg (fun r : G ℚ Ω →* M4 c.O => r.comp (D.Gp l).subtype) h₁
  have h0 : EqL D (D.loc ρ₁ l).hom := by
    obtain ⟨B, _, _, _, _, ρ', h1, -, y, hy⟩ := hpt.atL
    rw [← hy]
    exact (hmap B c.O y ρ'.hom).1 h1
  have hst : ρ.TStable fun a => (lamW a, muW a) := by
    intro R' _ _ _ f t ht
    obtain ⟨r', h1, h2⟩ := cl_tor t _ _ _ _ (ρ.map f).hom ((hρ R').1 f)
    let ρ' : Lift c.O (D.rbarAt l) R' :=
      { hom := r'
        cont := fun a b N => by
          simp only [h1, map_mul]
          exact ((ρ.map f).cont a b N).comp (_ * ·)
        red := fun g a b => by rw [h1, map_mul, ht, one_mul, (ρ.map f).red] }
    obtain ⟨f', hf', -⟩ := (hρ R').2 ρ' h2
    refine ⟨f', fun g a b => ?_⟩
    rw [hf']
    exact h1 g a b
  obtain ⟨x, P, n, u, φ, h1, h2, h3, h4, h5⟩ := liftChart (l := l) (D.rbarAt l) (fun a => (lamW a, muW a)) E R ρ
    (fun B _ _ r => EqL D r) hmap hρ hst (D.loc ρ₁ l) h0
    (fun g a b hab => by
      rw [hr0]
      exact Matrix.diagonal_apply_ne (fun i => (D.ps i g : c.O)) fun e : a = b => hab (by rw [e]))
    (fun B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hπp r' e1 e2 e3 => by
      obtain ⟨r, k1, k2, k3⟩ := spLiftL hP D hD E B π hπ B' π' hπ' p hp hπp r' ⟨hr0 ▸ e1, e2⟩ e3
      exact ⟨r, k1.cont, k2, k3⟩)
  have h6 : ∀ j, Nat.card {i // u i = j} = dimsL j := fun j => by
    obtain ⟨S, hS, hS'⟩ := h5 j
    rw [hr0] at hS'
    exact hS.trans (UpperTheory.tangent_space_deformation_at_l hP D hD E j S hS')
  obtain rfl := cl_count u h6
  exact ⟨x, P, u, φ, by rw [h1, hr0], h2, h3, h6, h4⟩
end
