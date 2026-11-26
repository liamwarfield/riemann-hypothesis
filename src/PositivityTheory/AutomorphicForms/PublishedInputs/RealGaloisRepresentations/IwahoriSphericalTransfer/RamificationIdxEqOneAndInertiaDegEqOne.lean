module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitModelToPlaceModel

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RamificationIdxEqOneAndInertiaDegEqOne
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceIsoDec

open scoped Pointwise

theorem exists_isPlaceOver_mid {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP⟩

theorem liesOver_of_isPlaceOver {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (hv : IsPlaceOver A v) (hw : IsPlaceOver A w) : w.asIdeal.LiesOver v.asIdeal := by
  refine ⟨?_⟩
  ext x
  rw [← hv x, Ideal.under, Ideal.mem_comap, ← hw, IsScalarTower.algebraMap_apply K L Ω]
  rfl

theorem valuation_smul_lt_one_iff {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (σ : Ω ≃ₐ[F] Ω)
    (A : ValuationSubring Ω) (z : Ω) :
    (σ • A).valuation z < 1 ↔ A.valuation (σ.symm z) < 1 := by
  have hmem : ∀ y, y ∈ σ • A ↔ σ.symm y ∈ A := fun y => by
    conv_lhs => rw [show y = σ (σ.symm y) by simp]
    rw [← AlgEquiv.smul_def]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  rw [valuation_lt_one_iff', valuation_lt_one_iff', hmem, hmem, map_inv₀, map_eq_zero_iff _ σ.symm.injective]

end GlobalTheory.PlaceIsoDec

namespace GlobalTheory.PlaceIsoDec

open scoped Pointwise

variable {F K L Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra F K] [Algebra F L] [Algebra K L] [Algebra F Ω] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower F K L] [IsScalarTower F L Ω] [IsScalarTower K L Ω] [IsScalarTower F K Ω]

theorem fixes_of_mem_stabilizer [IsAlgClosure F Ω] [IsAlgClosure L Ω]
    {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 L)} (hP : IsPlaceOver A P)
    (hD : Dec (F := F) A ≤ (res F Ω K).range)
    (τ : L ≃ₐ[F] L) (hτ : τ • P.asIdeal = P.asIdeal) (x : K) :
    τ (algebraMap K L x) = algebraMap K L x := by
  haveI : Normal F Ω := IsAlgClosure.normal F Ω
  set σ : Ω ≃ₐ[F] Ω := τ.liftNormal Ω with hσ
  have hσL : ∀ y : L, σ (algebraMap L Ω y) = algebraMap L Ω (τ y) := fun y =>
    AlgEquiv.liftNormal_commutes τ Ω y
  have hσL' : ∀ y : L, σ.symm (algebraMap L Ω y) = algebraMap L Ω (τ.symm y) := fun y => by
    rw [AlgEquiv.symm_apply_eq, hσL, AlgEquiv.apply_symm_apply]
  have hσA : IsPlaceOver (σ • A) P := fun y => by
    rw [valuation_smul_lt_one_iff, hσL', ← hτ, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    exact hP (τ⁻¹ • y)
  obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_isPlaceOver (F := L) hσA hP
  set g : Ω ≃ₐ[F] Ω := ρ.restrictScalars F * σ with hg
  have hgA : g ∈ Dec (F := F) A := by
    show g • A = A
    rw [hg, mul_smul]
    exact hρ
  obtain ⟨h, hh⟩ := hD hgA
  have e1 : g (algebraMap K Ω x) = algebraMap K Ω x := by
    rw [← hh]
    exact h.commutes x
  have e2 : g (algebraMap K Ω x) = algebraMap L Ω (τ (algebraMap K L x)) := by
    rw [IsScalarTower.algebraMap_apply K L Ω]
    show ρ (σ (algebraMap L Ω _)) = _
    rw [hσL]
    exact ρ.commutes _
  exact (algebraMap L Ω).injective (by rw [← e2, e1, IsScalarTower.algebraMap_apply K L Ω])

end GlobalTheory.PlaceIsoDec

namespace GlobalTheory.PlaceIsoDec

open scoped Pointwise

variable {F K L Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra F K] [Algebra F L] [Algebra K L] [Algebra F Ω] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower F K L] [IsScalarTower F L Ω] [IsScalarTower K L Ω] [IsScalarTower F K Ω]

theorem ramificationIdx_eq_one_and_inertiaDeg_eq_one [IsAlgClosure F Ω] [IsAlgClosure L Ω] [IsGalois F L]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 K)}
    {P : HeightOneSpectrum (𝓞 L)} (hv : IsPlaceOver A v) (hw : IsPlaceOver A w) (hP : IsPlaceOver A P)
    (hD : Dec (F := F) A ≤ (res F Ω K).range) :
    w.asIdeal.ramificationIdx (𝓞 F) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois F K L
  haveI : w.asIdeal.LiesOver v.asIdeal := liesOver_of_isPlaceOver hv hw
  haveI : P.asIdeal.LiesOver w.asIdeal := liesOver_of_isPlaceOver hw hP
  haveI : P.asIdeal.LiesOver v.asIdeal := liesOver_of_isPlaceOver hv hP
  have hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) P.asIdeal) =
      Nat.card (MulAction.stabilizer (L ≃ₐ[F] L) P.asIdeal) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun σ ↦ ⟨(σ : L ≃ₐ[K] L).restrictScalars F, σ.2⟩) ⟨?_, ?_⟩)
    · intro σ τ h
      exact Subtype.ext (AlgEquiv.restrictScalars_injective F (congrArg Subtype.val h))
    · rintro ⟨τ, hτ⟩
      have hfix := fixes_of_mem_stabilizer (K := K) hP hD τ hτ
      exact ⟨⟨{ τ.toRingEquiv with commutes' := hfix }, hτ⟩, Subtype.ext (AlgEquiv.ext fun _ ↦ rfl)⟩
  have h1 := GroundTheory.Global.card_decompositionGroup v P
  have h2 := GroundTheory.Global.card_decompositionGroup w P
  rw [hcard] at h2
  rw [Ideal.ramificationIdx_tower (R := 𝓞 F) w.asIdeal P.asIdeal,
    Ideal.inertiaDeg_tower (R := 𝓞 F) w.asIdeal P.asIdeal, h2] at h1
  have hpos : 0 < P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) := by
    rw [← h2]
    exact Nat.card_pos
  have key : w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) *
      (P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K)) =
      1 * (P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K)) := by
    rw [one_mul]
    conv_rhs => rw [h1]
    ring
  exact mul_eq_one.1 (Nat.eq_of_mul_eq_mul_right hpos key)

end GlobalTheory.PlaceIsoDec

namespace GlobalTheory.PlaceIsoDec

open GroundTheory.Global.SemiLocal in
theorem exists_placeIso_of_dec_le_range : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → Dec (F := F) A ≤ (res F Ω K).range → ∃ (w : HeightOneSpectrum (𝓞 K)) (_ : IsPlaceOver A w) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ v A hv hD
  obtain ⟨w, hw⟩ := GlobalTheory.PlaceIsoDec.exists_isPlaceOver_mid (L := K) hv
  haveI : Module.Finite F K := Module.Finite.of_restrictScalars_finite ℚ F K
  haveI : NumberField (IntermediateField.normalClosure F K Ω) := NumberField.of_module_finite F (IntermediateField.normalClosure F K Ω)
  haveI : IsAlgClosure (IntermediateField.normalClosure F K Ω) Ω :=
    ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) (IntermediateField.normalClosure F K Ω)⟩
  obtain ⟨P, hP⟩ := GlobalTheory.PlaceIsoDec.exists_isPlaceOver_mid (L := IntermediateField.normalClosure F K Ω) hv
  obtain ⟨he, hf⟩ := GlobalTheory.PlaceIsoDec.ramificationIdx_eq_one_and_inertiaDeg_eq_one (K := K) hv hw hP hD
  haveI : w.asIdeal.LiesOver v.asIdeal := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hv hw
  have hrank : Module.finrank (v.adicCompletion F) (w.adicCompletion K) = 1 := by
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg K v w, he, hf]
  have hsurj : Function.Surjective (completionMap v w) := by
    intro y
    have hy : y ∈ (⊥ : Subalgebra (v.adicCompletion F) (w.adicCompletion K)) := by
      rw [Subalgebra.bot_eq_top_of_finrank_eq_one hrank]
      trivial
    obtain ⟨x, hx⟩ := Algebra.mem_bot.1 hy
    exact ⟨x, hx⟩
  refine ⟨w, hw, RingEquiv.ofBijective (completionMap v w) ⟨(completionMap v w).injective, hsurj⟩,
    ⟨fun _ => Iff.rfl, fun x => IsScalarTower.algebraMap_apply F K Ω x, continuous_completionMap v w, fun x => ?_⟩⟩
  exact (completionMap_algebraMap v w x).trans (IsScalarTower.algebraMap_apply F K _ x)

end GlobalTheory.PlaceIsoDec
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.BridgeJMemKwOfDecLe
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal

theorem bridge_j_mem_Kw_of_dec_le : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Dec (F := F) A ≤ (res F Ω K).range → ∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1 := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ A O _ _ _ Bw hD x
  have hfix : ∀ σ ∈ (Bw.Kw.1).fixingSubgroup, σ (Bw.j (algebraMap K Ω x)) = Bw.j (algebraMap K Ω x) := by
    intro σ hσ
    obtain ⟨g, hg⟩ := Bw.e.surjective ⟨σ, hσ⟩
    have h1 := Bw.e_comm g (algebraMap K Ω x)
    rw [hg] at h1
    obtain ⟨h, hh⟩ := hD g.2
    have h2 : (g : Ω ≃ₐ[F] Ω) (algebraMap K Ω x) = algebraMap K Ω x := by
      rw [← hh]
      exact h.commutes x
    simpa [h2] using h1
  haveI : IsGalois ℚ_[l] (Om l) := inferInstance
  rw [← InfiniteGalois.fixedField_fixingSubgroup Bw.Kw.1]
  exact fun σ => hfix σ.1 σ.2

end GlobalTheory.RealGal
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.IsoComm
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocCompCLit

open Matrix

section

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end

end GlobalTheory.LocCompCLit
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.DRSstCrysPstJumpsDescend
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.RealGal.dRSstCrysPstJumps_descend : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (P : LocPrime l) (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (a : ℕ) (r : G F Ω →* GL (Fin a) (Qbar l)), (IsdRAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsdRAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ (IsSstAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsSstAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ (IsCrysAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsCrysAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ (IsPstAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsPstAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ ∀ (τ : K →+* Qbar l) (J : Multiset ℤ), IsJumpsAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) τ J → IsJumpsAt P Bw (r.comp (Dec (F := F) A).subtype) (τ.comp (algebraMap F K)) J := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ P A O _ _ _ Bw Bw' hK hj hL a r
  obtain ⟨Kw', j', jE', jd', e', ec', esc', ecomm', LL0', hs', eO', h1', h2', h3'⟩ := Bw'
  dsimp only at hK hj hL
  subst hK hj hL
  set Bw' : LocBridge l K Ω (Dec (F := K) A) O :=
    ⟨Bw.Kw, Bw.j, jE', jd', e', ec', esc', ecomm', Bw.LL, hs', eO', h1', h2', h3'⟩ with hBw'
  have key : ∀ (LL' : FinExt l) (r'' : ↥(Dec (F := K) A) →* GL (Fin a) ↥LL'.1),
      IsModel Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) LL' r'' →
      IsModel Bw (r.comp (Dec (F := F) A).subtype) LL' (r''.comp (Bw.e.trans e'.symm).toMonoidHom) ∧
      Bw.repE LL' (r''.comp (Bw.e.trans e'.symm).toMonoidHom) = Bw'.repE LL' r'' := by
    intro LL' r'' ⟨hle, hmap⟩
    refine ⟨⟨hle, ?_⟩, ?_⟩
    · refine MonoidHom.ext fun g => ?_
      have h1 := DFunLike.congr_fun hmap (e'.symm (Bw.e g))
      have h2 : AlgEquiv.restrictScalarsHom F ((e'.symm (Bw.e g) : ↥(Dec (F := K) A)) : Ω ≃ₐ[K] Ω) =
          ((g : ↥(Dec (F := F) A)) : Ω ≃ₐ[F] Ω) := by
        refine AlgEquiv.ext fun x => Bw.j.injective ?_
        change Bw.j (((e'.symm (Bw.e g) : ↥(Dec (F := K) A)) : Ω ≃ₐ[K] Ω) x) = _
        rw [← ecomm', MulEquiv.apply_symm_apply, Bw.e_comm]
      exact h1.trans (congrArg r h2)
    · refine MonoidHom.ext fun g => ?_
      simp only [LocBridge.repE, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨LL', r'', hm, hd⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_⟩
    unfold LocBridge.IsdRE at hd ⊢
    rw [he]; exact hd
  · rintro ⟨LL', r'', hm, hd⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_⟩
    rw [he]; exact hd
  · rintro ⟨LL', r'', hm, hd⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_⟩
    unfold LocBridge.IsCrysE at hd ⊢
    rw [he]; exact hd
  · rintro ⟨LL', r'', hm, hd⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_⟩
    rw [he]; exact hd
  · rintro τ J ⟨LL', r'', hm, hd, τ', hind, hc⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_, τ', ?_, ?_⟩
    · unfold LocBridge.IsdRE at hd ⊢
      rw [he]; exact hd
    · intro x
      have := hind (algebraMap F K x)
      simp only [RingHom.comp_apply]
      rw [this]
      congr 3
      exact congrArg Bw.j (IsScalarTower.algebraMap_apply F K Ω x).symm
    · intro n
      rw [hc n]
      unfold LocBridge.multE
      rw [he]
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RecAlgNormDiag
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
open Polynomial

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SatFrobLit

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem val_inv_eq (n : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((1 - (n : ℝ)) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (a : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, mul_comm]
  congr 2
  push_cast
  ring

end GlobalTheory.SatFrobLit

end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.EqOfMultisetSymmetricReflections
section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.SymmMultisetCentreUnique
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Glob

theorem symm_multiset_centre_unique : ∀ (s : Multiset ℤ) (x y : ℤ), s ≠ 0 → s = s.map (x - ·) → s = s.map (y - ·) → x = y := by
  intro s x y hs hx hy
  have key : ∀ z : ℤ, s = s.map (z - ·) → 2 * s.sum = (Multiset.card s : ℤ) * z := by
    intro z hz
    have h1 : (s.map (z - ·)).sum = (Multiset.card s : ℤ) * z - s.sum := by
      rw [Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, Multiset.map_id']
      simp [nsmul_eq_mul]
    have h2 : s.sum = (Multiset.card s : ℤ) * z - s.sum := by
      conv_lhs => rw [hz]
      exact h1
    linarith
  have hc : (Multiset.card s : ℤ) ≠ 0 := by
    exact_mod_cast (mt Multiset.card_eq_zero.mp hs)
  have := (key x hx).symm.trans (key y hy)
  exact mul_left_cancel₀ hc this

end GlobalTheory.Glob
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_multiset_symmetric_reflections : ∀ (s : Multiset ℤ) (x y : ℤ), s ≠ 0 → s = s.map (x - ·) → s = s.map (y - ·) → x = y := by
  first | exact @GlobalTheory.Glob.symm_multiset_centre_unique | exact GlobalTheory.Glob.symm_multiset_centre_unique | (intros; apply GlobalTheory.Glob.symm_multiset_centre_unique <;> assumption)
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ComplexConjAlgebraMap
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RealGal

theorem exists_hodgeTate {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} (π : TR.CuspSub F a)
    (hπ : π.IsRegAlg) (v : InfinitePlace F) :
    ∃ H : Multiset ℤ, ∃ m, π.HasInfChar v m ∧
      H.map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z := by
  obtain ⟨m, hm, -, hz⟩ := hπ v
  refine ⟨m.attach.map fun z => -(hz z.1 z.2).choose, m, hm, ?_⟩
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.attach_map_val m, Multiset.map_map]
  refine Multiset.map_congr rfl fun z _ => ?_
  have h := (hz z.1 z.2).choose_spec
  simp only [Function.comp_apply, Int.cast_neg]
  linear_combination h

theorem complexConj_algebraMap {F K : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K]
    [IsCMField K] [Algebra F K] (x : F) :
    IsCMField.complexConj K (algebraMap F K x) = algebraMap F K x := by
  rw [IsCMField.complexConj_eq_self_iff, mem_maximalRealSubfield_iff]
  intro φ
  have h := ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_mk_iff.mp
    (IsTotallyReal.isReal (InfinitePlace.mk (φ.comp (algebraMap F K)))))
  rw [RCLike.star_def, ← ComplexEmbedding.conjugate_coe_eq]
  exact RingHom.congr_fun h x

end GlobalTheory.RealGal

end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.GaloisRepRestrictionLocalCompletion
section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsExtra
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ParamSplitPlace

theorem main : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G F Ω →* GL (Fin a) (Qbar l)) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i → ∀ x' : WD h', IsWDOf ι (r.comp (res F Ω K)) x' → ∃ x : WD h, IsWDOf ι r x ∧ WDRel (RingEquiv.refl Ω) x x' := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ ι n r A v w h h' i hP x' hx'
  obtain ⟨t', ht', φ', hφ', N, b', hN', hb', rfl⟩ := hx'
  obtain ⟨c, hc, hdeg, hq, hsm⟩ := GlobalTheory.T.place_over_transport_ring_iso F Ω A v h K Ω A w h' (RingEquiv.refl Ω) (algebraMap F K) i hP
  have hcz : ∀ (σ : Weil h) (z : Ω), ((c σ : Weil h') : G K Ω) z = (σ : G F Ω) z :=
    fun σ z => ((hc σ (c σ)).2 rfl z).symm
  have hres : ∀ σ : Weil h, res F Ω K ((c σ : Weil h') : G K Ω) = (σ : G F Ω) :=
    fun σ => AlgEquiv.ext fun z => hcz σ z
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic

  have hm : ∀ σ : Ine (F := F) A, ((c (ineIncl h σ) : Weil h') : G K Ω) ∈ Ine (F := K) A := fun σ => by
    rw [← deg_eq_zero_iff, hdeg, deg_ineIncl]
  let e : Ine (F := F) A →* Ine (F := K) A :=
    (((Weil h').subtype.comp c.toMonoidHom).comp (ineIncl h)).codRestrict _ hm
  have he : ∀ σ, ineIncl h' (e σ) = c (ineIncl h σ) := fun σ => Subtype.ext rfl
  have hez : ∀ (σ : Ine (F := F) A) (z : Ω), ((e σ : Ine (F := K) A) : G K Ω) z = (σ : G F Ω) z := fun σ z => by
    have := hcz (ineIncl h σ) z
    rwa [coe_ineIncl] at this
  have he_surj : Function.Surjective e := by
    intro τ
    have hm' : ((c.symm (ineIncl h' τ) : Weil h) : G F Ω) ∈ Ine (F := F) A := by
      rw [← deg_eq_zero_iff, ← hdeg, MulEquiv.apply_symm_apply, deg_ineIncl]
    refine ⟨⟨_, hm'⟩, Subgroup.inclusion_injective (Ine_le_Weil h') ?_⟩
    show ineIncl h' (e _) = ineIncl h' τ
    rw [he]
    have : ineIncl h ⟨_, hm'⟩ = c.symm (ineIncl h' τ) := Subtype.ext rfl
    rw [this, MulEquiv.apply_symm_apply]
  have he_cont : Continuous e := by
    refine continuous_of_continuousAt_one e ?_
    rw [ContinuousAt, map_one, tendsto_subtype_rng]
    intro O' hO'
    obtain ⟨U, hU, hU1, hUO⟩ := GlobalTheory.WeilTransport.conj_nhds F Ω K Ω (RingEquiv.refl Ω) O' hO'
    refine Filter.mem_map.2 (Filter.mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds hU1) ?_)
    intro τ hτ
    exact hUO (τ : G F Ω) hτ ((e τ : Ine (F := K) A) : G K Ω) fun z => (hez τ z).symm

  let t : Ine (F := F) A →* Multiplicative ℤ_[l] := t'.comp e
  have ht : IsTameChar t := ⟨ht'.1.comp he_cont, ht'.2.comp he_surj⟩
  have hφ : deg (c.symm φ') = 1 := by rw [← hdeg, MulEquiv.apply_symm_apply, hφ']
  have hN : IsMonodromy t r N := by
    obtain ⟨hnil, U', hU', H⟩ := hN'
    refine ⟨hnil, U'.comap e, hU'.preimage he_cont, fun σ hσ => ?_⟩
    have h1 := H (e σ) hσ
    have h2 : res F Ω K ((e σ : Ine (F := K) A) : G K Ω) = (σ : G F Ω) := AlgEquiv.ext fun z => hez σ z
    rw [MonoidHom.comp_apply, h2] at h1
    exact h1
  have hpart : ∀ g : Weil h, e (inePart hφ g) = inePart hφ' (c g) := fun g =>
    Subgroup.inclusion_injective (Ine_le_Weil h') (by
      show ineIncl h' _ = ineIncl h' _
      rw [he, ineIncl_inePart, ineIncl_inePart, map_mul, map_inv, map_zpow, MulEquiv.apply_symm_apply, hdeg])
  have key : ∀ g : Weil h, wdMat t hφ r N g = wdMat t' hφ' (r.comp (res F Ω K)) N (c g) := fun g => by
    rw [wdMat, wdMat, ← hpart]
    show (r (g : G F Ω) : Matrix (Fin n) (Fin n) (Qbar l)) * _ =
      (r (res F Ω K ((c g : Weil h') : G K Ω)) : Matrix (Fin n) (Fin n) (Qbar l)) * _
    rw [hres]
    rfl

  let b : WDRep h (Fin n → ℂ) :=
    { ρ := b'.ρ.comp c.toMonoidHom
      N := b'.N
      smooth := (hsm _ b'.ρ).1 b'.smooth
      semisimple := fun σ => b'.semisimple (c σ)
      nilpotent := b'.nilpotent
      comm := fun σ => by
        have := b'.comm (c σ)
        rwa [hdeg, hq] at this }
  refine ⟨WD.mk b, ⟨t, ht, c.symm φ', hφ, N, b, hN, ⟨hb'.1, fun g => ?_⟩, rfl⟩,
    ⟨_, b, b', rfl, rfl, rfl, fun σ σ' hσ => ?_⟩⟩
  · show Commute (b'.ρ (c g)) _ ∧ IsNilpotent (_ - b'.ρ (c g))
    simpa only [key] using hb'.2 (c g)
  · show b'.ρ (c σ) = b'.ρ σ'
    rw [(hc σ σ').1 hσ]

end GlobalTheory.ParamSplitPlace
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_rep_restriction_local_completion : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G F Ω →* GL (Fin a) (Qbar l)) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i → ∀ x' : WD h', IsWDOf ι (r.comp (res F Ω K)) x' → ∃ x : WD h, IsWDOf ι r x ∧ WDRel (RingEquiv.refl Ω) x x' := by
  first | exact @GlobalTheory.ParamSplitPlace.main | exact GlobalTheory.ParamSplitPlace.main | (intros; apply GlobalTheory.ParamSplitPlace.main <;> assumption)
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.IwahoriSphericalTransfer
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompletionIso

open ValuativeRel

section Val

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem valuation_le_one_of_map (f : k ≃+* k') (hf : Continuous f) {x : k}
    (hx : valuation k' (f x) ≤ 1) : valuation k x ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hx0 : x ≠ 0 := by rintro rfl; simp at h
  have h1 : valuation k x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ h
  have h2 := GlobalTheory.TypeRec.TwistInert.valuation_lt_one_map f.toRingHom hf h1
  have hfx : f x ≠ 0 := (map_ne_zero f).2 hx0
  have hw : 0 < valuation k' (f x) := by rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hfx
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀] at h2
  exact absurd ((inv_lt_one₀ hw).1 h2) (not_lt.2 hx)

theorem valuation_lt_one_of_map (f : k ≃+* k') (hf : Continuous f) {x : k}
    (hx : valuation k' (f x) < 1) : valuation k x < 1 := by
  by_contra h
  rw [not_lt] at h
  have hx0 : x ≠ 0 := by rintro rfl; simp at h
  have h1 : x⁻¹ ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff, map_inv₀]; exact inv_le_one_of_one_le₀ h
  have h2 := GlobalTheory.LastCompare.map_mem_integer f.toMonoidHom hf h1
  rw [Valuation.mem_integer_iff] at h2
  have hfx : f x ≠ 0 := (map_ne_zero f).2 hx0
  have hw : 0 < valuation k' (f x) := by rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hfx
  have h3 : valuation k' (f x⁻¹) ≤ 1 := h2
  rw [map_inv₀, map_inv₀] at h3
  exact absurd hx (not_lt.2 ((inv_le_one₀ hw).1 h3))

variable (f : k ≃+* k') (hf : Continuous f) {n : Type} [Fintype n] [DecidableEq n]

theorem map_map_symm (h : GL n k') :
    Matrix.GeneralLinearGroup.map f.toRingHom (Matrix.GeneralLinearGroup.map f.symm.toRingHom h) = h := by
  ext a b
  simp

include hf in
theorem map_symm_mem_KO {h : GL n k'} (hh : h ∈ GlobalTheory.SplitWeil.KO k' n) :
    Matrix.GeneralLinearGroup.map f.symm.toRingHom h ∈ GlobalTheory.SplitWeil.KO k n := by
  obtain ⟨h0, rfl⟩ := hh
  let j : 𝒪[k'] →+* 𝒪[k] := (f.symm.toRingHom.comp (algebraMap 𝒪[k'] k')).codRestrict 𝒪[k] (fun y => by
      show valuation k (f.symm (y : k')) ≤ 1
      apply valuation_le_one_of_map f hf
      rw [RingEquiv.apply_symm_apply]
      exact y.2)
  refine ⟨Matrix.GeneralLinearGroup.map j h0, ?_⟩
  ext a b
  simp [j] <;> rfl

include hf in
theorem map_symm_mem_iwahori [LinearOrder n] {h : GL n k'} (hh : h ∈ GlobalTheory.SmGL.iwahori k' n) :
    Matrix.GeneralLinearGroup.map f.symm.toRingHom h ∈ GlobalTheory.SmGL.iwahori k n := by
  rw [GlobalTheory.SmGL.mem_iwahori] at hh ⊢
  refine ⟨map_symm_mem_KO f hf hh.1, fun a b hab => ?_⟩
  apply valuation_lt_one_of_map f hf
  have := hh.2 a b hab
  simpa using this

end Val

theorem fixed_ne_bot_transfer {G G' V V' : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G' V') (φ : G →* G')
    (ψ : G' → G) (hψ : ∀ g, φ (ψ g) = g) (e : V ≃ₗ[ℂ] V') (he : ∀ g x, e (ρ g x) = ρ' (φ g) (e x))
    (H : Subgroup G) (H' : Subgroup G') (hH : ∀ h ∈ H', ψ h ∈ H) :
    GlobalTheory.PRep.fixed ρ H ≠ ⊥ → GlobalTheory.PRep.fixed ρ' H' ≠ ⊥ := by
  intro hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hx' : ∀ h : H, ρ (h : G) x = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • x := hx
  refine (Submodule.ne_bot_iff _).2 ⟨e x, ?_, by simpa using hx0⟩
  show ∀ h : H', ρ' (h : G') (e x) = (((1 : H' →* ℂˣ) h : ℂˣ) : ℂ) • e x
  intro h
  have h1 := hx' ⟨ψ h, hH h h.2⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
  rw [← hψ h, ← he, h1]

theorem iwahori_spherical_transfer : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (i : v.adicCompletion F ≃+* w.adicCompletion K), Continuous i → ∀ (a : ℕ) (σ : SmIrr (GL (Fin a) (v.adicCompletion F))) (σ' : SmIrr (GL (Fin a) (w.adicCompletion K))) (e : σ.V ≃ₗ[ℂ] σ'.V), (∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)) → (GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (v.adicCompletion F) (Fin a)) ≠ ⊥ → GlobalTheory.PRep.fixed σ'.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion K) (Fin a)) ≠ ⊥) ∧ (GlobalTheory.SmGL.IsSpherical σ.ρ → GlobalTheory.SmGL.IsSpherical σ'.ρ) := by
  intro F K _ _ _ _ v w i hi a σ σ' e he
  exact ⟨fixed_ne_bot_transfer σ.ρ σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom)
      (Matrix.GeneralLinearGroup.map i.symm.toRingHom) (map_map_symm i) e he _ _
      (fun h hh => map_symm_mem_iwahori i hi hh),
    fixed_ne_bot_transfer σ.ρ σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom)
      (Matrix.GeneralLinearGroup.map i.symm.toRingHom) (map_map_symm i) e he _ _
      (fun h hh => map_symm_mem_KO i hi hh)⟩

end GlobalTheory.CompletionIso
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InducedEmbeddingExtends
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem induced_embedding_extends : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → ∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' → ∃ (τK : K →+* Qbar l) (τ'' : ↥Bw'.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), τK.comp (algebraMap F K) = τ ∧ IsInduced Bw' τK τ'' := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ A O _ _ _ Bw Bw' hK hj τ LL' τ' hτ
  obtain ⟨Kw', j', j_E', _, _, _, _, _, _, _, _, _, _, _⟩ := Bw'
  dsimp only at hK hj ⊢
  subst hK
  subst hj
  let ι : K →+* ↥Bw.Kw.1 :=
    { toFun := fun x => ⟨Bw.j (algebraMap K Ω x), j_E' x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  refine ⟨(LL'.1.val.toRingHom.comp (τ'.toRingHom.comp ι)), τ', ?_, ?_⟩
  · ext x
    have := hτ x
    simp only [RingHom.coe_comp, Function.comp_apply] at this ⊢
    rw [this]
    have e : (ι (algebraMap F K x)) = ⟨Bw.j (algebraMap F Ω x), Bw.j_E x⟩ := by
      apply Subtype.ext
      simp [ι, ← IsScalarTower.algebraMap_apply]
    simp [e]
  · intro x
    rfl

end GlobalTheory
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Imports
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IsoOfFrobFree

private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem main : IsoOfFrob := by
  intro F Ω _ _ _ _ _ l _ ι n r r' hr hr' hs hs' hw
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  have hc : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G F Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    rintro σ ⟨v, hv, -, A, hA, hσ⟩
    obtain ⟨B, hB, hB'⟩ := not_not.1 hv
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

end GlobalTheory.IsoOfFrobFree
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.NormVUnderPow
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AttResTower

theorem normV_under_pow {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem two_le_normV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ normV v := by
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem under_under {F K M : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M] (w : HeightOneSpectrum (𝓞 M)) :
    (w.under (𝓞 K)).under (𝓞 F) = w.under (𝓞 F) := by
  apply HeightOneSpectrum.ext
  show Ideal.comap _ (Ideal.comap _ w.asIdeal) = Ideal.comap _ w.asIdeal
  rw [Ideal.comap_comap]
  congr 1
  ext x
  first
  | exact (IsScalarTower.algebraMap_eq (𝓞 F) (𝓞 K) (𝓞 M)).symm ▸ rfl
  | (apply RingOfIntegers.coe_injective; simp only [RingHom.comp_apply, RingOfIntegers.algebraMap_coe]; exact (IsScalarTower.algebraMap_apply F K M (x : F)).symm)
  | (apply RingOfIntegers.ext; simp [IsScalarTower.algebraMap_apply F K M])

end GlobalTheory.AttResTower

theorem GlobalTheory.AttResTower.attRes_comp_res : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [Algebra F M] [Algebra M Ω] [IsScalarTower F M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower F K M] [IsScalarTower K M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : G K Ω →* GL (Fin a) (Qbar l)), AttRes π ι K r → AttRes π ι M (r.comp (res K Ω M)) := by
  intro F Ω _ _ _ _ _ _ K _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ l _ ι a π r hatt
  unfold AttRes at hatt ⊢
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually hatt] with w h f hf
  have huv := GlobalTheory.AttResTower.under_under (F := F) (K := K) w
  have h1 := GlobalTheory.AttResTower.normV_under_pow (K := F) (w.under (𝓞 K))
  have h2 := GlobalTheory.AttResTower.normV_under_pow (K := K) w
  obtain ⟨B, hB, hF⟩ := h _ h1
  rw [huv] at hB hF h1
  refine ⟨B, hB, ?_⟩
  have h3 := (UpperTheory.frobenius_power_compatibility K M Ω l ι w _ h2).1 a r _ hF
  have hff : f = (w.under (𝓞 K)).asIdeal.inertiaDeg (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 K) := by
    apply Nat.pow_right_injective (GlobalTheory.AttResTower.two_le_normV (w.under (𝓞 F)))
    simp only
    rw [← hf, h2, h1, ← pow_mul]
  rw [Multiset.map_map] at h3
  rw [hff]
  convert h3 using 2
  simp [Function.comp_def, pow_mul]
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.WdRelOfFrobSS
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WdResGen

private theorem wdAt_of_model {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
    {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces B) {a : ℕ}
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (L₂ : FinExt l) (r₂ : ↥(Dec (F := E) A) →* GL (Fin a) ↥L₂.1)
    (hm₂ : IsModel B r L₂ r₂) (hV₂ : IsPst P (B.repE L₂ r₂)) :
    wdAt P ι B h hj r = wdPst P ι B h hj (B.repE L₂ r₂) := by
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι B h hj (r := r) ⟨L₂, r₂, hm₂, hV₂⟩
  have h₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have h₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have e : mapRep (IntermediateField.inclusion h₁).toRingHom r₁ =
      mapRep (IntermediateField.inclusion h₂).toRingHom r₂ := by
    ext g i j
    exact congrArg (fun f : ↥(Dec (F := E) A) →* GL (Fin a) (Om l) => (f g : Matrix (Fin a) (Fin a) (Om l)) i j)
      (hm₁.2.trans hm₂.2.symm)
  rw [e₁, BridgeParam.wdPst_enlarge P ι B h hj h₁ r₁ hV₁, BridgeParam.wdPst_enlarge P ι B h hj h₂ r₂ hV₂, e]

private theorem wdRel_of_frobSS {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'} (φ : Ω ≃+* Ω')
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Weil h → Module.End ℂ V} {ρ' : Weil h' → Module.End ℂ V} {N : Module.End ℂ V}
    {a : WDRep h V} {b : WDRep h' V} (ha : IsFrobSS ρ N a) (hb : IsFrobSS ρ' N b)
    (hρ : ∀ σ σ', WeilRel φ σ σ' → ρ σ = ρ' σ') : WDRel φ (WD.mk a) (WD.mk b) := by
  let e := (Module.finBasis ℂ V).equivFun
  refine ⟨_, a.transport e, b.transport e, WD.sound (a.iso_transport e).symm, WD.sound (b.iso_transport e).symm,
    ?_, fun σ σ' hσ => ?_⟩
  · show e.conjAlgEquiv ℂ a.N = e.conjAlgEquiv ℂ b.N
    rw [ha.1, hb.1]
  · show e.conjAlgEquiv ℂ (a.ρ σ) = e.conjAlgEquiv ℂ (b.ρ σ')
    have h1 := hρ σ σ' hσ
    have h2 := hb.2 σ'
    rw [← h1] at h2
    rw [(Module.End.isNilpotent_isSemisimple_unique (ha.2 σ).2 (a.semisimple σ) h2.2 (b.semisimple σ')
      ((ha.2 σ).1.symm.sub_left (Commute.refl _)) (h2.1.symm.sub_left (Commute.refl _))
      (by simp)).2]

end GlobalTheory.WdResGen

open GlobalTheory.WdResGen in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.RealGal.wdRelRes_gen : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (P : LocPrime l) (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (a : ℕ) (r : G F Ω →* GL (Fin a) (Qbar l)), IsPstAt P Bw (r.comp (Dec (F := F) A).subtype) → ∀ (ι : Qbar l ≃+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i → WDRel (RingEquiv.refl Ω) (wdAt P ι Bw h hj (r.comp (Dec (F := F) A).subtype)) (wdAt P ι Bw' h' hj' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype)) := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ P A O _ _ _ Bw Bw' hK hJ hL n r hr ι v w h h' hj hj' i hP
  obtain ⟨Kw, j, j_E, j_dense, e, e_cont, e_symm_cont, e_comm, LL, LL_split, eO, eO_alg, eO_cont, eO_symm_cont⟩ := Bw'
  dsimp only at hK hJ hL
  subst hK hJ hL
  set Bw' : LocBridge l K Ω (Dec (F := K) A) O :=
    ⟨Bw.Kw, Bw.j, j_E, j_dense, e, e_cont, e_symm_cont, e_comm, Bw.LL, LL_split, eO, eO_alg, eO_cont, eO_symm_cont⟩
    with hB
  obtain ⟨L, r', hm, hV⟩ := hr
  have key : ∀ (g : ↥(Dec (F := K) A)) (x : Ω), ((Bw.e.symm (e g) : ↥(Dec (F := F) A)) : G F Ω) x = (g : G K Ω) x :=
    fun g x => Bw.j.injective (by rw [← Bw.e_comm, MulEquiv.apply_symm_apply, e_comm])
  let r'' : ↥(Dec (F := K) A) →* GL (Fin n) ↥L.1 := r'.comp (e.trans Bw.e.symm).toMonoidHom
  have hm' : IsModel Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype)
      L r'' := by
    refine ⟨hm.1, MonoidHom.ext fun g => ?_⟩
    have h1 := DFunLike.congr_fun hm.2 (Bw.e.symm (e g))
    refine h1.trans (congrArg r (AlgEquiv.ext (key g)))
  have hrep : Bw'.repE L r'' = Bw.repE L r' := by
    refine MonoidHom.ext fun g => ?_
    have h1 : r'' (e.symm g) = r' (Bw.e.symm g) := by simp [r'']
    exact congrArg (fun m : GL (Fin n) ↥L.1 => Matrix.toLin' (m : Matrix (Fin n) (Fin n) ↥L.1)) h1
  have hV' : IsPst P (Bw'.repE L r'') := by rw [hrep]; exact hV
  rw [wdAt_of_model _ ι Bw h hj _ L r' hm hV, wdAt_of_model _ ι Bw' h' hj' _ L r'' hm' hV', hrep]
  generalize Bw.repE L r' = ρ at hV ⊢
  haveI := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, wdPst_of_isPst ι Bw' h' hj' hV]
  obtain ⟨c, hc, hdeg, hq, -⟩ := GlobalTheory.T.place_over_transport_ring_iso F Ω A v h K Ω A w h' _ _ i hP
  refine wdRel_of_frobSS _ (BridgeParam.isFrobSS_wdRep P ι Bw h hj ρ)
    (BridgeParam.isFrobSS_wdRep P ι Bw' h' hj' ρ) fun σ σ' hσ => ?_
  have h1 : weilToGK Bw h σ = weilToGK Bw' h' σ' := by
    have h2 : Subgroup.inclusion (Weil_le_Dec h) σ = Bw.e.symm (e (Subgroup.inclusion (Weil_le_Dec h') σ')) :=
      Subtype.ext (AlgEquiv.ext fun x => (hσ x).trans (key (Subgroup.inclusion (Weil_le_Dec h') σ') x).symm)
    exact (congrArg Bw.e h2).trans (Bw.e.apply_symm_apply _)
  have h3 : alpha l σ = alpha l σ' := by
    rw [alpha, alpha, ← (hc σ σ').1 hσ, hdeg, resDeg, resDeg, hq]
  have h4 : weilD Bw h P ρ σ = weilD Bw' h' P ρ σ' :=
    (weilD_apply Bw h P ρ σ).trans ((congrArg₂ (fun (g : ↥(GK Bw.Kw)) (m : ℤ) => actD P ρ g *
      Units.val (phiU P ρ ^ (-m)))
      h1 h3).trans (weilD_apply Bw' h' P ρ σ').symm)
  refine wd_ext _ ι ρ fun x => ?_
  exact (wdRho_mk P ι Bw h hj ρ σ x).trans
    ((congrArg (wdMk P ι ρ) (LinearMap.congr_fun h4 x)).trans (wdRho_mk P ι Bw' h' hj' ρ σ' x).symm)
end
