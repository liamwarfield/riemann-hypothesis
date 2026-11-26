module

public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.Transport
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkAssemble
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.SumEqCardMulSub
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.RatioEqOneOfAltSum

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.LemmaX
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

theorem lemmaX : PositivityTheory.Lit1.GEN.GlobalEulerCharCoprime := by
  intro K S hS ℓ _ hℓS L _ hL hPn hcop hζ hK ιr M _ _ hMl hMP
  have : Finite S := hS
  refine ratio_eq_one_of_altSum hℓS ιr M hMl ?_
  have : Finite (zmodRepOfTorsion ℓ M hMl) := ‹Finite M›
  have : Module.Finite (ZMod ℓ) (zmodRepOfTorsion ℓ M hMl) := Module.Finite.of_finite
  exact altSum hL hℓS hPn hcop hζ hK ιr (zmodRepOfTorsion ℓ M hMl) (fun g m => by
    have := congrArg (fun f => f m) (hMP g g.2)
    exact this)

end PositivityTheory.Lit1.GEN.X
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.Assemble
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkDevis
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_devis

theorem ratioOne_of_killed_l (ℓ : ℕ) [Fact ℓ.Prime] (P : FiniteSubfield → Prop) (h : RatioOneKilled ℓ P) :
    RatioOne ℓ P := by
  intro K S hS hSl hP ιr M _ _ hM
  obtain ⟨r, hr⟩ := hM
  have : Finite S := hS
  induction r generalizing M with
  | zero =>
    have : Subsingleton M := ⟨fun a b => by
      have ha := hr a
      have hb := hr b
      simp only [pow_zero, one_smul] at ha hb
      rw [ha, hb]⟩
    exact gsEulerRatio_eq_one_of_subsingleton S M ιr
  | succ r ih =>
    letI : Module (ULift.{0} ℤ) M := M.hV2
    let T : Module.End (ULift.{0} ℤ) M := (ℓ : Module.End (ULift.{0} ℤ) M)
    have hTx : ∀ x : M, T x = ℓ • x := fun x => Module.End.natCast_apply ℓ x
    have hT : ∀ g, Commute T (M.ρ g) := fun g => Nat.cast_commute ℓ _
    have hD : ∀ g, (⊤ : Submodule _ _) ≤ Submodule.comap (M.ρ g) ⊤ := fun _ => le_top
    have hSE := rangeStepComplex_shortExact T hT ⊤ hD
    have : Finite (Rep.subrepresentation M ⊤ hD) :=
      Finite.of_injective (fun x : Rep.subrepresentation M ⊤ hD => (x.1 : M)) fun _ _ h => Subtype.ext h
    have : Finite (Rep.subrepresentation M _ (inf_ker_le_comap T hT ⊤ hD)) :=
      Finite.of_injective (fun x : Rep.subrepresentation M _ (inf_ker_le_comap T hT ⊤ hD) => (x.1 : M))
        fun _ _ h => Subtype.ext h
    have : Finite (Rep.subrepresentation M _ (map_le_comap T hT ⊤ hD)) :=
      Finite.of_injective (fun x : Rep.subrepresentation M _ (map_le_comap T hT ⊤ hD) => (x.1 : M))
        fun _ _ h => Subtype.ext h
    have hl : ∃ r : ℕ, ∀ m : (rangeStepComplex T hT ⊤ hD).X₂, (ℓ ^ r) • m = 0 :=
      ⟨r + 1, fun m => Subtype.ext (hr m.1)⟩
    have hmul := ratio_shortExact_l ℓ K S hS hSl ιr _ hSE hl
    have h1 : gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₁ ιr = 1 := by
      refine h K S hS hSl hP ιr _ fun m => Subtype.ext ?_
      have h' : T m.1 = 0 := m.2.2
      rw [hTx] at h'
      exact h'
    have h3 : gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₃ ιr = 1 := by
      refine ih _ fun m => Subtype.ext ?_
      obtain ⟨x, -, hx⟩ := m.2
      change (ℓ ^ r) • m.1 = 0
      rw [← hx, hTx, smul_smul, ← pow_succ]
      exact hr x
    have htop : gsEulerRatio S M ιr = gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₂ ιr :=
      (gsEulerRatio_eq_of_iso S (M.subrepresentation ⊤ hD) ιr (subrepresentationTopIso M hD)).symm
    rw [htop, hmul, h1, h3, mul_one]

end PositivityTheory.Lit1.GEN.W_devis
end

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN

theorem ratioOne_of_killed_l (ℓ : ℕ) [Fact ℓ.Prime] (P : FiniteSubfield → Prop) (h : RatioOneKilled ℓ P) :
    RatioOne ℓ P :=
  W_devis.ratioOne_of_killed_l ℓ P h

theorem ratioOne_of_lemmaX (ℓ : ℕ) [Fact ℓ.Prime] (hX : GlobalEulerCharCoprime) : RatioOne ℓ (fun _ => True) :=
  ratioOne_of_killed_l ℓ _ (W_assemble.ratioOneKilled_of_lemmaX ℓ hX)

end PositivityTheory.Lit1.GEN
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GlobalEulerCharAtOfRatioOne
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkDictfwdA
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkDictfwdB
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_dictfwd_b


section DictA

open ReciprocityTheory.Gal Formalism.ConjugateSelfDual

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

noncomputable def resS (S : Set (HeightOneSpectrum (𝓞 F))) : G F Ω →* galUnramifiedOutside F Ω S :=
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  AlgEquiv.restrictNormalHom (maxUnramifiedOutside F Ω S)

noncomputable def gsIso (S : Set (HeightOneSpectrum (𝓞 F))) :
    GS Ω S ≃ₜ* galUnramifiedOutside F Ω S := by
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  let E := maxUnramifiedOutside F Ω S
  let φ : G F Ω →* Gal(E/F) := AlgEquiv.restrictNormalHom E
  have hφs : Function.Surjective φ := AlgEquiv.restrictNormalHom_surjective Ω
  have hNS : NS Ω S = (maxUnramifiedOutside F Ω S).fixingSubgroup :=
    le_antisymm (GlobalTheory.T.normal_subgroup_le_unramified_fixing F Ω S) (GlobalTheory.T.galois_unramified_outside_cohomology F Ω S)
  have hker : φ.ker = NS Ω S := by
    rw [hNS]
    ext σ
    rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      have h1 := AlgEquiv.restrictNormal_commutes σ E (⟨x, hx⟩ : E)
      have h2 : σ.restrictNormal E = 1 := h
      rw [h2] at h1
      exact h1.symm
    · intro h
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      exact (AlgEquiv.restrictNormal_commutes σ E x).trans (h x.1 x.2)
  have hφc : Continuous φ := InfiniteGalois.restrictNormalHom_continuous E
  let q : GS Ω S ≃* Gal(E/F) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hq : Continuous q := continuous_coinduced_dom.2 hφc
  have : CompactSpace (G F Ω) := inferInstance
  have : CompactSpace (GS Ω S) := Quotient.compactSpace
  exact { q with
    continuous_toFun := hq
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2 (f := q.toEquiv) hq }

theorem gsIso_toGS (S : Set (HeightOneSpectrum (𝓞 F))) (g : G F Ω) :
    gsIso (Ω := Ω) S (toGS Ω S g) = resS S g := by
  rfl

theorem gsIso_symm_resS (S : Set (HeightOneSpectrum (𝓞 F))) (g : G F Ω) :
    (gsIso (Ω := Ω) S).symm (resS S g) = toGS Ω S g := by
  rw [← gsIso_toGS, ContinuousMulEquiv.symm_apply_apply]

theorem dict_A {l : ℕ} [Fact l.Prime] {r : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hc : ContAction rhoS) :
    ∃ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))))
      (_ : IsDiscreteRep A), Finite A ∧ (∀ a : A, (l ^ r) • a = 0) ∧ Nat.card A = Nat.card M ∧
      Nat.card (cohomology A 0) = Nat.card (H0 rhoS) ∧ Nat.card (cohomology A 1) = Nat.card (H1 rhoS) ∧
      Nat.card (cohomology A 2) = Nat.card (H2 rhoS) ∧
      ∀ g : G F Ω, Nat.card {a : A // A.ρ (resS (S : Set (HeightOneSpectrum (𝓞 F))) g) a = a} =
        Nat.card {m : M // rhoS (toGS Ω _ g) m = m} := by
  let e : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ*
      GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) := (gsIso (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F)))).symm
  have hc' := ReciprocityTheory.Neutral.Bridge.contAction_comp e hc
  let rho' : Representation (ZMod (l ^ r)) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M :=
    rhoS.comp (e : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) →*
      GS Ω (S : Set (HeightOneSpectrum (𝓞 F))))
  obtain ⟨A, hA, eA, he⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcRep _ (ZMod (l ^ r)) M rho' hc'
  have hAf : Finite A.V := Finite.of_equiv _ eA.toEquiv
  have hn : ∀ a : A.V, (l ^ r) • a = 0 := by
    intro a
    obtain ⟨m, rfl⟩ := eA.surjective a
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)), ZMod.natCast_self, zero_smul, map_zero]
  obtain ⟨e0, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc0 _ (ZMod (l ^ r)) M rho' A eA he
  obtain ⟨e1, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 _ (ZMod (l ^ r)) M rho' A eA he
  obtain ⟨e2, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 _ (ZMod (l ^ r)) M rho' A eA he
  have t1 := ReciprocityTheory.Neutral.Bridge.equivH1OfIso e rhoS rho' (fun _ _ => rfl)
  have t2 := ReciprocityTheory.Neutral.Bridge.equivH2OfIso e rhoS rho' (fun _ _ => rfl)
  have hH0 : H0 rho' = H0 rhoS := by
    ext m
    rw [mem_riemannRochSpace_iff_regularAt_everywhere, mem_riemannRochSpace_iff_regularAt_everywhere]
    constructor
    · intro h g
      obtain ⟨g', rfl⟩ := e.surjective g
      exact h g'
    · intro h g
      exact h (e g)
  refine ⟨A, hA, hAf, hn, (Nat.card_congr eA.toEquiv).symm, ?_, ?_, ?_, fun g => ?_⟩
  · rw [← Nat.card_congr e0.toEquiv, hH0]
  · exact (Nat.card_congr (t1.toAddEquiv.trans e1).toEquiv).symm
  · exact (Nat.card_congr (t2.toAddEquiv.trans e2).toEquiv).symm
  · have hg : e (resS (S : Set (HeightOneSpectrum (𝓞 F))) g) = toGS Ω _ g :=
      gsIso_symm_resS _ g
    refine (Nat.card_congr (Equiv.subtypeEquiv eA.toEquiv fun m => ?_)).symm
    change rhoS (toGS Ω _ g) m = m ↔ A.ρ (resS _ g) (eA m) = eA m
    rw [← he, eA.apply_eq_iff_eq]
    change rhoS (toGS Ω _ g) m = m ↔ rhoS (e (resS _ g)) m = m
    rw [hg]

theorem isCCAt_conj {w : InfinitePlace F} (hw : w.IsReal) {c c' : G F Ω} (hc : IsCCAt w c)
    (hc' : IsCCAt w c') : ∃ g : G F Ω, c' = g * c * g⁻¹ := by
  obtain ⟨j, hj, hjw⟩ := hc
  obtain ⟨j', hj', hj'w⟩ := hc'
  have hreal : ComplexEmbedding.IsReal (j.comp (algebraMap F Ω)) := by
    rw [← InfinitePlace.isReal_mk_iff, hjw]
    exact hw
  have hres : j'.comp (algebraMap F Ω) = j.comp (algebraMap F Ω) := by
    rcases InfinitePlace.mk_eq_iff.1 (hj'w.trans hjw.symm) with h | h
    · exact h
    · calc j'.comp (algebraMap F Ω)
          = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (j'.comp (algebraMap F Ω))) :=
            by ext x; simp [ComplexEmbedding.conjugate_coe_eq]
        _ = ComplexEmbedding.conjugate (j.comp (algebraMap F Ω)) := by rw [h]
        _ = j.comp (algebraMap F Ω) := ComplexEmbedding.isReal_iff.1 hreal
  let _ : Algebra Ω ℂ := j.toAlgebra
  let _ : Algebra F ℂ := (j.comp (algebraMap F Ω)).toAlgebra
  have : IsScalarTower F Ω ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Normal F Ω := IsAlgClosure.normal F Ω
  let J' : Ω →ₐ[F] ℂ := { j' with commutes' := fun x => RingHom.congr_fun hres x }
  let σ : Gal(Ω/F) := Normal.algHomEquivAut F ℂ Ω J'
  have hσ : ∀ x, j (σ x) = j' x := fun x =>
    congrArg (fun f : Ω →ₐ[F] ℂ => f x) ((Normal.algHomEquivAut F ℂ Ω).symm_apply_apply J')
  have key : σ * c' = c * σ := by
    apply AlgEquiv.ext
    intro x
    apply j.injective
    show j (σ (c' x)) = j (c (σ x))
    rw [hσ, hj', hj, hσ]
  refine ⟨σ⁻¹, ?_⟩
  calc c' = σ⁻¹ * (σ * c') := by group
    _ = σ⁻¹ * (c * σ) := by rw [key]
    _ = σ⁻¹ * c * σ⁻¹⁻¹ := by group

theorem comap_comap' {k L N : Type*} [Field k] [Field L] [Field N] (w : InfinitePlace N)
    (f : L →+* N) (g : k →+* L) : (w.comap f).comap g = w.comap (f.comp g) := by
  rw [← InfinitePlace.mk_embedding w, InfinitePlace.comap_mk, InfinitePlace.comap_mk,
    InfinitePlace.comap_mk]
  rfl

theorem realPlaces_transport (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ)) :
    ∃ e : {w : InfinitePlace F // w.IsReal} ≃ {v : InfinitePlace K.1 // v.IsReal},
      Fintype.card (InfinitePlace F) = Fintype.card (InfinitePlace K.1) ∧
      ∀ (w : {w : InfinitePlace F // w.IsReal}) (g : G F Ω) (g' : G K.1 (AlgebraicClosure ℚ)),
        (∀ x : Ω, g' (τ x) = τ (g x)) → IsCCAt (e w).1 g' → IsCCAt w.1 g := by
  have h1 : ∀ w : InfinitePlace F, (w.comap (σ.symm : K.1 →+* F)).comap (σ : F →+* K.1) = w := by
    intro w
    rw [comap_comap']
    have : (σ.symm : K.1 →+* F).comp (σ : F →+* K.1) = RingHom.id F := by
      ext x
      simp
    rw [this, InfinitePlace.comap_id]
  have h2 : ∀ v : InfinitePlace K.1, (v.comap (σ : F →+* K.1)).comap (σ.symm : K.1 →+* F) = v := by
    intro v
    rw [comap_comap']
    have : (σ : F →+* K.1).comp (σ.symm : K.1 →+* F) = RingHom.id K.1 := by
      ext x
      simp
    rw [this, InfinitePlace.comap_id]
  let eP : InfinitePlace F ≃ InfinitePlace K.1 :=
    ⟨fun w => w.comap (σ.symm : K.1 →+* F), fun v => v.comap (σ : F →+* K.1), h1, h2⟩
  refine ⟨eP.subtypeEquiv fun w => (InfinitePlace.isReal_comap_iff σ.symm).symm,
    Fintype.card_congr eP, ?_⟩
  rintro w g g' hgg' ⟨j, hj, hjw⟩
  refine ⟨j.comp τ.toRingHom, fun x => ?_, ?_⟩
  · show j (τ (g x)) = starRingEnd ℂ (j (τ x))
    rw [← hgg', hj]
  · have : (j.comp τ.toRingHom).comp (algebraMap F Ω) =
        (j.comp (algebraMap K.1 (AlgebraicClosure ℚ))).comp (σ : F →+* K.1) := by
      ext x
      show j (τ (algebraMap F Ω x)) = j (algebraMap K.1 (AlgebraicClosure ℚ) (σ x))
      rw [hτ]
      rfl
    rw [this, ← InfinitePlace.comap_mk, hjw]
    exact h1 w.1

theorem places_transport (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ (S' : Set (HeightOneSpectrum (𝓞 K.1))) (_ : S'.Finite),
      (∀ n : ℕ, (∀ v : HeightOneSpectrum (𝓞 F), (n : 𝓞 F) ∈ v.asIdeal → v ∈ S) →
        ∀ v' : HeightOneSpectrum (𝓞 K.1), (n : 𝓞 K.1) ∈ v'.asIdeal → v' ∈ S') ∧
      ∀ x : Ω, x ∈ maxUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ↔
        τ x ∈ maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S' := by
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  classical
  have he : ∀ x : F, τ (algebraMap F Ω x) = algebraMap K.1 (AlgebraicClosure ℚ) (σ x) :=
    fun x => (hτ x).trans rfl
  let T : Finset (HeightOneSpectrum (𝓞 K.1)) :=
    S.map (GlobalTheory.CompanionTheory.GSCd.Transport.placeEquiv (RingOfIntegers.mapRingEquiv σ)).toEmbedding
  have hC : GlobalTheory.CompanionTheory.GSCd.Transport.Corr σ (S : Set (HeightOneSpectrum (𝓞 F)))
      (T : Set (HeightOneSpectrum (𝓞 K.1))) := by
    intro v
    simp [T]
  refine ⟨(T : Set (HeightOneSpectrum (𝓞 K.1))), T.finite_toSet, fun n hn w hw => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have hv : (GlobalTheory.CompanionTheory.GSCd.Transport.placeEquiv (RingOfIntegers.mapRingEquiv σ)).symm w ∈ S := by
      apply hn
      change RingOfIntegers.mapRingEquiv σ (n : 𝓞 F) ∈ w.asIdeal
      rw [map_natCast]
      exact hw
    exact Finset.mem_coe.2 (Finset.mem_map.2 ⟨_, hv, (GlobalTheory.CompanionTheory.GSCd.Transport.placeEquiv _).apply_symm_apply w⟩)
  · exact GlobalTheory.CompanionTheory.GSCd.Transport.mem_max σ τ he hC hx
  · have := GlobalTheory.CompanionTheory.GSCd.Transport.mem_max σ.symm τ.symm (GlobalTheory.CompanionTheory.GSCd.Transport.symm_compat σ τ he)
      hC.symm hx
    rwa [RingEquiv.symm_apply_apply] at this

end DictA

section Arch

open ReciprocityTheory.Gal Formalism.ConjugateSelfDual

theorem real_H0_card_eq_fixed_of_gen (K : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (v : {v : InfinitePlace K.1 // v.IsReal})
    (s : Gal(AlgebraicClosure v.1.Completion / v.1.Completion)) (hs : ∀ g, g = 1 ∨ g = s)
    (B : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S')) [IsDiscreteRep B] :
    gsRealH0Card S' B ιr v = Nat.card {b : B // B.ρ (gsRealFamily S' ιr v s) b = b} := by
  unfold gsRealH0Card
  rw [Nat.card_congr (H0Iso _).toLinearEquiv.toEquiv]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun b => ?_)
  change (∀ g, B.ρ (gsRealFamily S' ιr v g) b = b) ↔ B.ρ (gsRealFamily S' ιr v s) b = b
  refine ⟨fun h => h s, fun h g => ?_⟩
  rcases hs g with hg | hg
  · rw [hg, map_one, map_one]
    rfl
  · rw [hg]
    exact h


set_option maxHeartbeats 1600000 in
theorem exists_cc_gen (K : FiniteSubfield) (v : {v : InfinitePlace K.1 // v.IsReal}) :
    ∃ (κ : AlgebraicClosure v.1.Completion →+* ℂ) (s : Gal(AlgebraicClosure v.1.Completion / v.1.Completion)),
      (∀ y, κ (s y) = starRingEnd ℂ (κ y)) ∧ (∀ g, g = 1 ∨ g = s) ∧
      ∀ x : K.1, κ (algebraMap K.1 (AlgebraicClosure v.1.Completion) x) = v.1.embedding x := by
  have hv : v.1.IsReal := v.2
  let ρ := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  let φ : v.1.Completion →+* ℂ := Complex.ofRealHom.comp ρ.toRingHom
  let _ : Algebra v.1.Completion ℂ := φ.toAlgebra
  let κA : AlgebraicClosure v.1.Completion →ₐ[v.1.Completion] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hκr : ∀ r : v.1.Completion, κA (algebraMap v.1.Completion _ r) = (ρ r : ℂ) := fun r =>
    κA.commutes r

  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
    ((Polynomial.X ^ 2 + 1 : Polynomial (AlgebraicClosure v.1.Completion)))
    (by rw [← Polynomial.C_1, Polynomial.degree_X_pow_add_C (by norm_num : 0 < 2)]; norm_num)
  have hy2 : κA y ^ 2 = -1 := by
    have h := congrArg κA (show y ^ 2 + 1 = 0 by simpa using hy)
    rw [map_add (f := _), map_pow, map_one, map_zero] at h
    linear_combination h
  have hsurj : Function.Surjective κA := by
    intro z
    have hI : ∃ t, κA t = Complex.I := by
      have : (κA y - Complex.I) * (κA y + Complex.I) = 0 := by
        calc (κA y - Complex.I) * (κA y + Complex.I) = κA y ^ 2 - Complex.I ^ 2 := by ring
          _ = 0 := by rw [hy2, Complex.I_sq]; ring
      rcases mul_eq_zero.1 this with h | h
      · exact ⟨y, sub_eq_zero.1 h⟩
      · exact ⟨-y, by rw [map_neg]; linear_combination -h⟩
    obtain ⟨t, ht⟩ := hI
    refine ⟨algebraMap v.1.Completion _ (ρ.symm z.re) + algebraMap v.1.Completion _ (ρ.symm z.im) * t, ?_⟩
    rw [map_add (f := _), map_mul, hκr, hκr, ht, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact Complex.re_add_im z
  let e : AlgebraicClosure v.1.Completion ≃+* ℂ :=
    RingEquiv.ofBijective κA.toRingHom ⟨κA.toRingHom.injective, hsurj⟩
  have he : ∀ t, e t = κA t := fun _ => rfl
  have hreal : ∀ r : v.1.Completion, e.symm (ρ r : ℂ) = algebraMap v.1.Completion _ r := by
    intro r
    rw [e.symm_apply_eq, he, hκr]
  let s : Gal(AlgebraicClosure v.1.Completion / v.1.Completion) :=
    { toRingEquiv := (e.trans (starRingAut : ℂ ≃+* ℂ)).trans e.symm
      commutes' := fun r => by
        show e.symm (starRingEnd ℂ (e (algebraMap v.1.Completion _ r))) = algebraMap v.1.Completion _ r
        rw [he, hκr, Complex.conj_ofReal, hreal] }
  have hs : ∀ t, κA (s t) = starRingEnd ℂ (κA t) := by
    intro t
    show e (e.symm ((starRingAut : ℂ ≃+* ℂ) (e t))) = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  refine ⟨κA.toRingHom, s, hs, fun g => ?_, fun x => ?_⟩
  · let f : ℂ →ₐ[ℝ] ℂ :=
      { toRingHom := (e.symm.trans (g.toRingEquiv.trans e)).toRingHom
        commutes' := fun a => by
          show e (g (e.symm (Complex.ofReal a))) = Complex.ofReal a
          have : (Complex.ofReal a) = (ρ (ρ.symm a) : ℂ) := by rw [RingEquiv.apply_symm_apply]
          rw [this, hreal, AlgEquiv.commutes, he, hκr] }
    rcases Complex.real_algHom_eq_id_or_conj f with hf | hf
    · left
      ext t
      apply e.injective
      have := congrArg (fun F : ℂ →ₐ[ℝ] ℂ => F (e t)) hf
      simpa [f] using this
    · right
      ext t
      apply e.injective
      have := congrArg (fun F : ℂ →ₐ[ℝ] ℂ => F (e t)) hf
      simp only [f] at this
      rw [he (s t), hs]
      simp at this
      exact this
  · have hsc : algebraMap K.1 (AlgebraicClosure v.1.Completion) x =
        algebraMap v.1.Completion (AlgebraicClosure v.1.Completion) (algebraMap K.1 v.1.Completion x) :=
      IsScalarTower.algebraMap_apply _ _ _ x
    show κA (algebraMap K.1 (AlgebraicClosure v.1.Completion) x) = _
    rw [hsc, hκr, InfinitePlace.Completion.ringEquivRealOfIsReal_apply, ← InfinitePlace.embedding_of_isReal_apply hv]
    congr 1
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      Algebra.algebraMap_self_apply]
    simp

theorem real_H0_card_eq_fixed (K : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (v : {v : InfinitePlace K.1 // v.IsReal}) :
    ∃ cc : G K.1 (AlgebraicClosure ℚ), IsCCAt v.1 cc ∧
      ∀ (B : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S'))
        [IsDiscreteRep B], gsRealH0Card S' B ιr v =
          Nat.card {b : B // B.ρ (resS (Ω := AlgebraicClosure ℚ) S' cc) b = b} := by
  obtain ⟨κ, s, hκs, hs, hκK⟩ := exists_cc_gen K v
  refine ⟨decompHom v.1.Completion (ιr v) s, ⟨κ.comp (ιr v).toRingHom, fun x => ?_, ?_⟩, fun B _ => ?_⟩
  · show κ (ιr v (decompHom v.1.Completion (ιr v) s x)) = starRingEnd ℂ (κ (ιr v x))
    rw [decompHom_apply, hκs]
  · have : (κ.comp (ιr v).toRingHom).comp (algebraMap K.1 (AlgebraicClosure ℚ)) = v.1.embedding := by
      ext x
      show κ (ιr v (algebraMap K.1 (AlgebraicClosure ℚ) x)) = v.1.embedding x
      rw [AlgHom.commutes, hκK]
    rw [this, InfinitePlace.mk_embedding]
  · rw [real_H0_card_eq_fixed_of_gen K S' ιr v s hs B]
    have hfam : gsRealFamily S' ιr v s = resS (Ω := AlgebraicClosure ℚ) S' (decompHom v.1.Completion (ιr v) s) := by
      show decompHomS v.1.Completion S' (ιr v) s = _
      rw [decompHomS_eq]
      rfl
    simp only [hfam]

end Arch

end PositivityTheory.Lit1.GEN.W_dictfwd_b
end

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.GEN.W_dictfwd_a

noncomputable section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

def resS (S : Set (HeightOneSpectrum (𝓞 F))) : G F Ω →* galUnramifiedOutside F Ω S :=
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  AlgEquiv.restrictNormalHom (maxUnramifiedOutside F Ω S)

theorem card_fix_conj {k Γ : Type} [CommRing k] [Group Γ] (A : Rep.{0} k Γ) (g c : Γ) :
    Nat.card {a : A // A.ρ (g * c * g⁻¹) a = a} = Nat.card {a : A // A.ρ c a = a} := by
  have key : ∀ x y : Γ, ∀ a : A, A.ρ x (A.ρ y a) = A.ρ (x * y) a := fun x y a => by
    rw [map_mul, Module.End.mul_apply]
  refine Nat.card_congr
    { toFun := fun a => ⟨A.ρ g⁻¹ a.1, ?_⟩
      invFun := fun a => ⟨A.ρ g a.1, ?_⟩
      left_inv := fun a => Subtype.ext ?_
      right_inv := fun a => Subtype.ext ?_ }
  · conv_rhs => rw [← a.2]
    rw [key, key]
    congr 1
    group
  · conv_rhs => rw [← a.2]
    rw [key, key]
    congr 1
    group
  · show A.ρ g (A.ρ g⁻¹ a.1) = a.1
    rw [key, mul_inv_cancel, map_one, Module.End.one_apply]
  · show A.ρ g⁻¹ (A.ρ g a.1) = a.1
    rw [key, inv_mul_cancel, map_one, Module.End.one_apply]

theorem isCCAt_conj {w : InfinitePlace F} (hw : w.IsReal) {c c' : G F Ω} (hc : IsCCAt w c)
    (hc' : IsCCAt w c') : ∃ g : G F Ω, c' = g * c * g⁻¹ := by
  exact PositivityTheory.Lit1.GEN.W_dictfwd_b.isCCAt_conj hw hc hc'

theorem exists_fieldTransport :
    ∃ (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1),
      ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ) := by
  let σ0 : F →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let K : FiniteSubfield := ⟨σ0.fieldRange,
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField σ0).toLinearEquiv⟩
  letI : Algebra F (AlgebraicClosure ℚ) := σ0.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ F (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq fun q => (σ0.commutes q).symm
  haveI : Algebra.IsAlgebraic F (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  haveI : IsAlgClosure F (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  let τ : Ω ≃ₐ[F] AlgebraicClosure ℚ := IsAlgClosure.equiv F Ω (AlgebraicClosure ℚ)
  refine ⟨K, τ.toRingEquiv, (AlgEquiv.ofInjectiveField σ0).toRingEquiv, fun x => ?_⟩
  show τ (algebraMap F Ω x) = _
  rw [τ.commutes]
  rfl

theorem places_transport (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ (S' : Set (HeightOneSpectrum (𝓞 K.1))) (_ : S'.Finite),
      (∀ n : ℕ, (∀ v : HeightOneSpectrum (𝓞 F), (n : 𝓞 F) ∈ v.asIdeal → v ∈ S) →
        ∀ v' : HeightOneSpectrum (𝓞 K.1), (n : 𝓞 K.1) ∈ v'.asIdeal → v' ∈ S') ∧
      ∀ x : Ω, x ∈ maxUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ↔
        τ x ∈ maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S' := by
  exact PositivityTheory.Lit1.GEN.W_dictfwd_b.places_transport K τ σ hτ S

def tauE (τ : Ω ≃+* AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 F))) {K : FiniteSubfield}
    (S' : Set (HeightOneSpectrum (𝓞 K.1)))
    (hmem : ∀ x : Ω, x ∈ maxUnramifiedOutside F Ω S ↔
        τ x ∈ maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') :
    maxUnramifiedOutside F Ω S ≃+* maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S' where
  toFun x := ⟨τ (x : Ω), (hmem x).1 x.2⟩
  invFun y := ⟨τ.symm y, (hmem _).2 (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (τ.symm_apply_apply (x : Ω))
  right_inv y := Subtype.ext (τ.apply_symm_apply (y : AlgebraicClosure ℚ))
  map_mul' x y := Subtype.ext (map_mul τ (x : Ω) y)
  map_add' x y := Subtype.ext (map_add τ (x : Ω) y)

def galTransport (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ))
    (S : Set (HeightOneSpectrum (𝓞 F))) (S' : Set (HeightOneSpectrum (𝓞 K.1)))
    (hmem : ∀ x : Ω, x ∈ maxUnramifiedOutside F Ω S ↔
        τ x ∈ maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') :
    galUnramifiedOutside F Ω S ≃* galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S' where
  toFun h := AlgEquiv.ofRingEquiv (f := (tauE τ S S' hmem).symm.trans (h.toRingEquiv.trans (tauE τ S S' hmem)))
    fun k => Subtype.ext (by
      show τ ((h ⟨τ.symm k, _⟩ : maxUnramifiedOutside F Ω S) : Ω) = (k : AlgebraicClosure ℚ)
      have hk : τ.symm (k : AlgebraicClosure ℚ) = algebraMap F Ω (σ.symm k) := by
        rw [τ.symm_apply_eq, hτ, RingEquiv.apply_symm_apply]
      have : (⟨τ.symm k, (hmem _).2 (by rw [RingEquiv.apply_symm_apply]; exact (algebraMap K.1 (maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') k).2)⟩ :
          maxUnramifiedOutside F Ω S) = algebraMap F (maxUnramifiedOutside F Ω S) (σ.symm k) :=
        Subtype.ext hk
      rw [this, h.commutes]
      show τ (algebraMap F Ω (σ.symm k)) = _
      rw [hτ, RingEquiv.apply_symm_apply])
  invFun h' := AlgEquiv.ofRingEquiv (f := (tauE τ S S' hmem).trans (h'.toRingEquiv.trans (tauE τ S S' hmem).symm))
    fun x => Subtype.ext (by
      show τ.symm ((h' ⟨τ (algebraMap F Ω x), _⟩ : maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') :
        AlgebraicClosure ℚ) = algebraMap F Ω x
      have : (⟨τ (algebraMap F Ω x), (hmem _).1 (algebraMap F (maxUnramifiedOutside F Ω S) x).2⟩ :
          maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') =
          algebraMap K.1 (maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') (σ x) :=
        Subtype.ext (hτ x)
      rw [this, h'.commutes, τ.symm_apply_eq, hτ]
      rfl)
  left_inv h := by ext x; simp [tauE]
  right_inv h' := by ext y; simp [tauE]
  map_mul' a b := by ext y; simp [tauE]

theorem continuous_galTransport (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ))
    (S : Set (HeightOneSpectrum (𝓞 F))) (S' : Set (HeightOneSpectrum (𝓞 K.1)))
    (hmem : ∀ x : Ω, x ∈ maxUnramifiedOutside F Ω S ↔
        τ x ∈ maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') :
    Continuous (galTransport K τ σ hτ S S' hmem) ∧ Continuous (galTransport K τ σ hτ S S' hmem).symm := by
  have hc : Continuous (galTransport K τ σ hτ S S' hmem) := by
    let f : galUnramifiedOutside F Ω S →* galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S' :=
      (galTransport K τ σ hτ S S' hmem).toMonoidHom
    change Continuous f
    refine continuous_of_continuousAt_one f ?_
    rw [ContinuousAt, map_one]
    intro s hs
    obtain ⟨K0, hK0, hK0s⟩ := (krullTopology_mem_nhds_one_iff K.1 _ s).1 hs
    classical
    set_option synthInstance.maxHeartbeats 200000 in
      let b := Module.finBasis K.1 K0
    let L0 : IntermediateField F (maxUnramifiedOutside F Ω S) :=
      IntermediateField.adjoin F (Set.range fun i => (tauE τ S S' hmem).symm (b i : _))
    have hL0 : FiniteDimensional F L0 :=
      IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
    rw [Filter.mem_map]
    refine Filter.mem_of_superset
      ((krullTopology_mem_nhds_one_iff F _ _).2 ⟨L0, hL0, le_rfl⟩) fun h hh => hK0s ?_
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hh ⊢
    have hb : ∀ i, f h (b i : _) = b i := fun i => by
      change (tauE τ S S' hmem) (h ((tauE τ S S' hmem).symm (b i : _))) = _
      rw [hh _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩), RingEquiv.apply_symm_apply]
    intro y hy
    have key := b.ext (f₁ := (f h).toLinearMap ∘ₗ K0.val.toLinearMap) (f₂ := K0.val.toLinearMap)
      fun i => hb i
    exact LinearMap.congr_fun key ⟨y, hy⟩
  exact ⟨hc, Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := (galTransport K τ σ hτ S S' hmem).toEquiv) hc⟩

theorem galEquiv_transport (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ))
    (S : Set (HeightOneSpectrum (𝓞 F))) (S' : Set (HeightOneSpectrum (𝓞 K.1)))
    (hmem : ∀ x : Ω, x ∈ maxUnramifiedOutside F Ω S ↔
        τ x ∈ maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') :
    ∃ θ : galUnramifiedOutside F Ω S ≃ₜ* galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S',
      ∀ (g : G F Ω) (g' : G K.1 (AlgebraicClosure ℚ)), (∀ x : Ω, g' (τ x) = τ (g x)) →
        θ (resS (Ω := Ω) S g) = resS (Ω := AlgebraicClosure ℚ) S' g' := by
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  obtain ⟨h1, h2⟩ := continuous_galTransport K τ σ hτ S S' hmem
  refine ⟨{ galTransport K τ σ hτ S S' hmem with continuous_toFun := h1, continuous_invFun := h2 },
    fun g g' hg => ?_⟩
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  show τ ((g.restrictNormal (maxUnramifiedOutside F Ω S) ((tauE τ S S' hmem).symm y) : Ω)) =
    ((g'.restrictNormal (maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') y :
      maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') : AlgebraicClosure ℚ)
  have e1 := AlgEquiv.restrictNormal_commutes g (maxUnramifiedOutside F Ω S) ((tauE τ S S' hmem).symm y)
  have e2 := AlgEquiv.restrictNormal_commutes g' (maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') y
  simp only [IntermediateField.algebraMap_apply] at e1 e2
  rw [e1, e2, ← hg]
  show g' (τ (τ.symm (y : AlgebraicClosure ℚ))) = _
  rw [RingEquiv.apply_symm_apply]

theorem gsTransport_compat (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ (S' : Set (HeightOneSpectrum (𝓞 K.1))) (_ : S'.Finite)
      (θ : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ*
        galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S'),
      (∀ n : ℕ, (∀ v : HeightOneSpectrum (𝓞 F), (n : 𝓞 F) ∈ v.asIdeal → v ∈ S) →
        ∀ v' : HeightOneSpectrum (𝓞 K.1), (n : 𝓞 K.1) ∈ v'.asIdeal → v' ∈ S') ∧
      ∀ (g : G F Ω) (g' : G K.1 (AlgebraicClosure ℚ)), (∀ x : Ω, g' (τ x) = τ (g x)) →
        θ (resS (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F))) g) =
          resS (Ω := AlgebraicClosure ℚ) S' g' := by
  obtain ⟨S', hS', hn, hmem⟩ := places_transport K τ σ hτ S
  obtain ⟨θ, hθ⟩ := galEquiv_transport K τ σ hτ _ S' hmem
  exact ⟨S', hS', θ, hn, hθ⟩

theorem exists_transport_elem (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ))
    (g' : G K.1 (AlgebraicClosure ℚ)) : ∃ g : G F Ω, ∀ x : Ω, g' (τ x) = τ (g x) := by
  refine ⟨AlgEquiv.ofRingEquiv (f := τ.trans (g'.toRingEquiv.trans τ.symm)) fun x => ?_, fun x => ?_⟩
  · show τ.symm (g' (τ (algebraMap F Ω x))) = algebraMap F Ω x
    rw [hτ, τ.symm_apply_eq, hτ]
    exact g'.commutes (σ x)
  · show g' (τ x) = τ (τ.symm (g' (τ x)))
    rw [RingEquiv.apply_symm_apply]

theorem realPlaces_transport (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ)) :
    ∃ e : {w : InfinitePlace F // w.IsReal} ≃ {v : InfinitePlace K.1 // v.IsReal},
      Fintype.card (InfinitePlace F) = Fintype.card (InfinitePlace K.1) ∧
      ∀ (w : {w : InfinitePlace F // w.IsReal}) (g : G F Ω) (g' : G K.1 (AlgebraicClosure ℚ)),
        (∀ x : Ω, g' (τ x) = τ (g x)) → IsCCAt (e w).1 g' → IsCCAt w.1 g := by
  exact PositivityTheory.Lit1.GEN.W_dictfwd_b.realPlaces_transport K τ σ hτ

theorem real_H0_card_eq_fixed (K : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (v : {v : InfinitePlace K.1 // v.IsReal}) :
    ∃ cc : G K.1 (AlgebraicClosure ℚ), IsCCAt v.1 cc ∧
      ∀ (B : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S'))
        [IsDiscreteRep B], gsRealH0Card S' B ιr v =
          Nat.card {b : B // B.ρ (resS (Ω := AlgebraicClosure ℚ) S' cc) b = b} := by
  exact PositivityTheory.Lit1.GEN.W_dictfwd_b.real_H0_card_eq_fixed K S' ιr v


open scoped Classical in
theorem transport_data {l : ℕ} [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ContainsAbove S l) :
    ∃ (K : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K.1))) (_ : S'.Finite)
      (θ : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ*
        galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S')
      (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
      (c' : InfinitePlace F → G F Ω)
      (e : {w : InfinitePlace F // w.IsReal} ≃ {v : InfinitePlace K.1 // v.IsReal}),
      (∀ v : HeightOneSpectrum (𝓞 K.1), ((l : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S') ∧
      (∀ w, w.IsReal → IsCCAt w (c' w)) ∧
      Fintype.card (InfinitePlace F) = Fintype.card (InfinitePlace K.1) ∧
      ∀ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))))
        [IsDiscreteRep A] (w : {w : InfinitePlace F // w.IsReal}),
        haveI := IsDiscreteRep.res (φ := θ.symm.toMulEquiv.toMonoidHom) θ.symm.continuous A
        gsRealH0Card S' (Rep.res θ.symm.toMulEquiv.toMonoidHom A) ιr (e w) =
          Nat.card {a : A // A.ρ (resS (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F))) (c' w.1)) a = a} := by
  obtain ⟨K, τ, σ, hτ⟩ := exists_fieldTransport (F := F) (Ω := Ω)
  obtain ⟨S', hS', θ, hn, hθ⟩ := gsTransport_compat K τ σ hτ S
  obtain ⟨e, hcard, hcc⟩ := realPlaces_transport K τ σ hτ
  set_option synthInstance.maxHeartbeats 200000 in
    let ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion := fun v => IsAlgClosed.lift
  choose cc hccv hfixv using fun v => real_H0_card_eq_fixed K S' ιr v
  choose g hg using fun v => exists_transport_elem K τ σ hτ (cc v)
  refine ⟨K, S', hS', θ, ιr, fun w => if hw : w.IsReal then g (e ⟨w, hw⟩) else 1, e,
    hn l hS, fun w hw => ?_, hcard, fun A _ w => ?_⟩
  · simp only [dif_pos hw]
    exact hcc ⟨w, hw⟩ _ _ (hg _) (hccv _)
  · rw [hfixv (e w)]
    simp only [dif_pos w.2, Subtype.coe_eta]
    rw [← hθ _ _ (hg (e w))]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
    show A.ρ (θ.symm (θ _)) a = a ↔ _
    rw [ContinuousMulEquiv.symm_apply_apply]


open scoped Classical in
theorem ratio_F_exists {l : ℕ} [Fact l.Prime] (h : RatioOne l (fun _ => True))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ContainsAbove S l) :
    ∃ c' : InfinitePlace F → G F Ω, (∀ w, w.IsReal → IsCCAt w (c' w)) ∧
      ∀ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))))
        [IsDiscreteRep A] [Finite A] (r : ℕ), (∀ a : A, (l ^ r) • a = 0) →
        eulerChar A * (Nat.card A : ℚ) ^ Fintype.card (InfinitePlace F) =
          ∏ w : {w : InfinitePlace F // w.IsReal},
            (Nat.card {a : A // A.ρ (resS (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F))) (c' w.1)) a = a} : ℚ) := by
  obtain ⟨K, S', hS', θ, ιr, c', e, hl, hc', hcard, hfix⟩ := transport_data (Ω := Ω) S hS
  refine ⟨c', hc', fun A _ _ r hA => ?_⟩
  haveI := IsDiscreteRep.res (φ := θ.symm.toMulEquiv.toMonoidHom) θ.symm.continuous A
  haveI hBf : Finite (Rep.res θ.symm.toMulEquiv.toMonoidHom A) := inferInstanceAs (Finite A)
  have h1 := h K S' hS' hl trivial ιr (Rep.res θ.symm.toMulEquiv.toMonoidHom A) ⟨r, hA⟩
  have hχ := eulerChar_res_continuousMulEquiv θ.symm A
  unfold gsEulerRatio at h1
  rw [Subsingleton.elim (Subtype.fintype InfinitePlace.IsReal) (fintypeRealPlaces K)] at h1
  have hP : (∏ v : {v : InfinitePlace K.1 // v.IsReal},
      (gsRealH0Card S' (Rep.res θ.symm.toMulEquiv.toMonoidHom A) ιr v : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => by
      exact_mod_cast (gsRealH0Card_pos S' (Rep.res θ.symm.toMulEquiv.toMonoidHom A) ιr v).ne'
  rw [div_eq_one_iff_eq hP, hχ] at h1
  have hn : Nat.card (Rep.res θ.symm.toMulEquiv.toMonoidHom A) = Nat.card A := rfl
  rw [hn] at h1
  rw [hcard, h1]
  exact (Fintype.prod_equiv e _ _ (fun w => by rw [hfix A w])).symm


open scoped Classical in
theorem ratio_F {l : ℕ} [Fact l.Prime] (h : RatioOne l (fun _ => True))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ContainsAbove S l)
    (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))))
    [IsDiscreteRep A] [Finite A] (r : ℕ) (hA : ∀ a : A, (l ^ r) • a = 0)
    (c : InfinitePlace F → G F Ω) (hc : ∀ w, w.IsReal → IsCCAt w (c w)) :
    eulerChar A * (Nat.card A : ℚ) ^ Fintype.card (InfinitePlace F) =
      ∏ w : {w : InfinitePlace F // w.IsReal},
        (Nat.card {a : A // A.ρ (resS (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F))) (c w.1)) a = a} : ℚ) := by
  obtain ⟨c', hc', hrat⟩ := ratio_F_exists (Ω := Ω) h S hS
  rw [hrat A r hA]
  refine Finset.prod_congr rfl fun w _ => ?_
  obtain ⟨g, hg⟩ := isCCAt_conj w.2 (hc' w.1 w.2) (hc w.1 w.2)
  have e := card_fix_conj A (resS (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F))) g)
    (resS (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F))) (c' w.1))
  rw [← map_inv, ← map_mul, ← map_mul, ← hg] at e
  rw [e]

theorem dict_A {l : ℕ} [Fact l.Prime] {r : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hc : ContAction rhoS) :
    ∃ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))))
      (_ : IsDiscreteRep A), Finite A ∧ (∀ a : A, (l ^ r) • a = 0) ∧ Nat.card A = Nat.card M ∧
      Nat.card (cohomology A 0) = Nat.card (H0 rhoS) ∧ Nat.card (cohomology A 1) = Nat.card (H1 rhoS) ∧
      Nat.card (cohomology A 2) = Nat.card (H2 rhoS) ∧
      ∀ g : G F Ω, Nat.card {a : A // A.ρ (resS (S : Set (HeightOneSpectrum (𝓞 F))) g) a = a} =
        Nat.card {m : M // rhoS (toGS Ω _ g) m = m} := by
  exact PositivityTheory.Lit1.GEN.W_dictfwd_b.dict_A S rhoS hc

open scoped Classical in
theorem globalEulerCharAt_of_ratioOne {l : ℕ} [Fact l.Prime] {r : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (h : RatioOne l (fun _ => True)) : GlobalEulerCharAt S rhoS := by
  intro _ hS hc c hcc
  obtain ⟨A, hAd, hAf, hAt, hcard, h0, h1, h2, hfix⟩ := dict_A S rhoS hc
  have key := ratio_F h S hS A r hAt c hcc
  simp only [eulerChar, Finset.prod_range_succ, Finset.prod_range_zero, one_mul, pow_zero, pow_one,
    zpow_one, zpow_neg, neg_one_sq, Int.reduceNeg, hcard, h0, h1, h2] at key
  have hP : ∏ w : {w : InfinitePlace F // w.IsReal},
      (Nat.card {a : A // A.ρ (resS (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F))) (c w.1)) a = a} : ℚ) =
      ((∏ w ∈ Finset.univ.filter (fun w : InfinitePlace F => w.IsReal),
        Nat.card {m : M // rhoS (toGS Ω _ (c w)) m = m} : ℕ) : ℚ) := by
    rw [Nat.cast_prod, Finset.prod_subtype (p := fun w : InfinitePlace F => w.IsReal)
      (Finset.univ.filter (fun w : InfinitePlace F => w.IsReal)) (fun w => by simp)]
    exact Finset.prod_congr rfl fun w _ => by rw [hfix]
  rw [hP] at key
  have hR := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank F
  have hI : Fintype.card (InfinitePlace F) =
      InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F :=
    NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
  unfold archH0Card
  rw [← hR]
  rw [hI] at key
  have hpos : 0 < ∏ w ∈ Finset.univ.filter (fun w : InfinitePlace F => w.IsReal),
      Nat.card {m : M // rhoS (toGS Ω _ (c w)) m = m} :=
    Finset.prod_pos fun w _ => Nat.card_pos_iff.2 ⟨⟨⟨0, map_zero _⟩⟩, inferInstance⟩
  by_cases hh1 : Nat.card (H1 rhoS) = 0
  · rw [hh1] at key
    simp at key
    exact absurd key.symm (by exact_mod_cast hpos.ne')
  · have hq : ((Nat.card (H0 rhoS) * Nat.card (H2 rhoS) * Nat.card M ^
        (InfinitePlace.nrRealPlaces F + 2 * InfinitePlace.nrComplexPlaces F) : ℕ) : ℚ) =
        ((Nat.card (H1 rhoS) * ((∏ w ∈ Finset.univ.filter (fun w : InfinitePlace F => w.IsReal),
          Nat.card {m : M // rhoS (toGS Ω _ (c w)) m = m}) *
          Nat.card M ^ InfinitePlace.nrComplexPlaces F) : ℕ) : ℚ) := by
      push_cast
      rw [← Nat.cast_prod, ← key]
      have : (Nat.card (H1 rhoS) : ℚ) ≠ 0 := by exact_mod_cast hh1
      field_simp
      ring
    exact_mod_cast hq

end

end PositivityTheory.Lit1.GEN.W_dictfwd_a
end

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.GEN

theorem globalEulerCharAt_of_ratioOne {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (h : RatioOne l (fun _ => True)) : GlobalEulerCharAt S rhoS :=
  W_dictfwd_a.globalEulerCharAt_of_ratioOne S rhoS h

end PositivityTheory.Lit1.GEN
end

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.GEN

theorem globalEulerChar_of_lemmaX (hX : GlobalEulerCharCoprime) : ReciprocityTheory.Gal.GlobalEulerChar := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S rhoS
  exact globalEulerCharAt_of_ratioOne S rhoS (ratioOne_of_lemmaX l hX)

theorem globalEulerChar_full : ReciprocityTheory.Gal.GlobalEulerChar :=
  globalEulerChar_of_lemmaX X.lemmaX

end PositivityTheory.Lit1.GEN
