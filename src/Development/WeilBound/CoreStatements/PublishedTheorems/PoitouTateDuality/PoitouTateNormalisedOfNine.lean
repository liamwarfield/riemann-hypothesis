module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivCyclotomicCharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoitouTateSequenceTransport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvFamNormalised
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.FiniteH2TorsionModule
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualPf
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteH1UnramifiedOutside
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsRep
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsGsEquiv
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsLocal

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingIsomorphismTransportsPlaces
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingIsomorphismTransportsPlaces
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso.Places

variable {R S : Type} [CommRing R] [CommRing S]

theorem mem_iff_apply_mem_map (f : R ≃+* S) (I : Ideal R) (x : R) :
    x ∈ I ↔ f x ∈ I.map f := by
  rw [Ideal.mem_map_of_equiv]
  constructor
  · exact fun h => ⟨x, h, rfl⟩
  · rintro ⟨y, hy, e⟩
    rwa [← f.injective e]

variable [IsDedekindDomain R] [IsDedekindDomain S]

noncomputable def placeMap (f : R ≃+* S) (v : HeightOneSpectrum R) : HeightOneSpectrum S where
  asIdeal := v.asIdeal.map f
  isPrime := by
    haveI := v.isPrime
    exact Ideal.map_isPrime_of_equiv f
  ne_bot := by
    intro h
    apply v.ne_bot
    exact (Ideal.map_eq_bot_iff_of_injective f.injective).1 h

theorem placeMap_asIdeal (f : R ≃+* S) (v : HeightOneSpectrum R) :
    (placeMap f v).asIdeal = v.asIdeal.map f := rfl

theorem placeMap_symm_placeMap (f : R ≃+* S) (v : HeightOneSpectrum R) :
    placeMap f.symm (placeMap f v) = v := by
  apply HeightOneSpectrum.ext
  rw [placeMap_asIdeal, placeMap_asIdeal, Ideal.map_symm]
  ext x
  rw [Ideal.mem_comap]
  exact (mem_iff_apply_mem_map f _ x).symm

noncomputable def placeEquiv (f : R ≃+* S) : HeightOneSpectrum R ≃ HeightOneSpectrum S where
  toFun := placeMap f
  invFun := placeMap f.symm
  left_inv := placeMap_symm_placeMap f
  right_inv := placeMap_symm_placeMap f.symm

theorem exists_places_of_ringEquiv : ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] (e : F ≃+* F'), ∃ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ^ 2 ↔ eO x ∈ (eV v).asIdeal ^ 2) ∧ ∀ v : HeightOneSpectrum (𝓞 F), normV (eV v) = normV v := by
  intro F F' _ _ _ _ e
  refine ⟨RingOfIntegers.mapRingEquiv e, placeEquiv (RingOfIntegers.mapRingEquiv e), ?_, ?_, ?_, ?_⟩
  · intro x
    rw [RingOfIntegers.mapRingEquiv_apply]
  · intro v x
    exact mem_iff_apply_mem_map _ _ x
  · intro v x
    change x ∈ v.asIdeal ^ 2 ↔ _ ∈ (v.asIdeal.map (RingOfIntegers.mapRingEquiv e)) ^ 2
    rw [← Ideal.map_pow]
    exact mem_iff_apply_mem_map _ _ x
  · intro v
    exact (Nat.card_congr (Ideal.quotientEquiv v.asIdeal _ (RingOfIntegers.mapRingEquiv e) rfl).toEquiv).symm

end GlobalTheory.CompanionTheory.PTIso.Places
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingIsomorphismTransportsPlacesStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_isomorphism_transports_places : ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] (e : F ≃+* F'), ∃ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ^ 2 ↔ eO x ∈ (eV v).asIdeal ^ 2) ∧ ∀ v : HeightOneSpectrum (𝓞 F), normV (eV v) = normV v := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.Places.exists_places_of_ringEquiv | exact GlobalTheory.CompanionTheory.PTIso.Places.exists_places_of_ringEquiv | (intros; apply GlobalTheory.CompanionTheory.PTIso.Places.exists_places_of_ringEquiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsDecomposition
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

private theorem valuation_lt_one_iff_mem_and_inv_not_mem {K : Type*} [Field K] (A : ValuationSubring K) (y : K) :
    A.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ A := by
  by_cases hy : y = 0
  · subst hy
    simp
  · have hp : 0 < A.valuation y := (Valuation.pos_iff _).2 hy
    rw [← A.valuation_le_one_iff, Valuation.map_inv, inv_le_one₀ hp, not_le]
    simp [hy]

theorem isPlaceOver_transfer_fieldIso :
    ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE eO eV hO hv A A' hA v
  have hlt : ∀ y : Ω, A'.valuation (E y) < 1 ↔ A.valuation y < 1 := by
    intro y
    rw [valuation_lt_one_iff_mem_and_inv_not_mem, valuation_lt_one_iff_mem_and_inv_not_mem, ← map_inv₀, hA, map_eq_zero_iff E E.injective]
  have hx : ∀ x : 𝓞 F, (A'.valuation (algebraMap F' Ω' ((eO x : 𝓞 F') : F')) < 1 ↔ eO x ∈ (eV v).asIdeal) ↔
      (A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) := by
    intro x
    rw [hO x, ← hE, hlt, ← hv]
  unfold Formalism.ConjugateSelfDual.IsPlaceOver
  constructor
  · intro h x'
    obtain ⟨x, rfl⟩ := eO.surjective x'
    exact (hx x).2 (h x)
  · intro h x
    exact (hx x).1 (h (eO x))

end GlobalTheory.CompanionTheory.PTIso
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsDecompositionStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_equiv_transports_decomposition : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v) := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.isPlaceOver_transfer_fieldIso | exact GlobalTheory.CompanionTheory.PTIso.isPlaceOver_transfer_fieldIso | (intros; apply GlobalTheory.CompanionTheory.PTIso.isPlaceOver_transfer_fieldIso <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsResidue
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsResidue
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

noncomputable section

namespace GlobalTheory.CompanionTheory.PTIso.Norm

theorem isNormalised_transfer : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ^ 2 ↔ eO x ∈ (eV v).asIdeal ^ 2) → (∀ v : HeightOneSpectrum (𝓞 F), normV (eV v) = normV v) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), (∀ σ : G F Ω, cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → (∀ σ : G F Ω, (σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') ∧ (σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') ∧ ∀ q : ℕ, IsFrob (F := F) A q σ ↔ IsFrob (F := F') A' q (Φ σ)) → ∀ (ζ : Ω) (v : HeightOneSpectrum (𝓞 F)) (iA : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)) (iA' : H2 (muLoc F' l r A') →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), (∀ (z : Z2 (muLoc F l r A)) (z' : Z2 (muLoc F' l r A')), (∀ (g h : Dec (F := F) A) (g' h' : Dec (F := F') A'), (g' : G F' Ω') = Φ g → (h' : G F' Ω') = Φ h → z'.1 (g', h') = z.1 (g, h)) → iA' (Submodule.Quotient.mk z') = iA (Submodule.Quotient.mk z)) → IsNormalised ζ A v iA → IsNormalised (E ζ) A' (eV v) iA' := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ eO eV heO hI hI2 hN l _ r hc A A' hA hD ζ v iA iA'
    hrel hn ϖ' y' κ' χ' z' h1 h2 h3 h4 h5 h6 h7 h8
  let eD : Dec (F := F) A ≃ₜ* Dec (F := F') A' :=
    subgroupIso Φ (Dec (F := F) A) (Dec (F := F') A') (fun a => (hD a).1)
  have hcoe : ∀ g : Dec (F := F) A, ((eD g : Dec (F := F') A') : G F' Ω') = Φ g := fun _ => rfl
  let zz : Z2 (muLoc F l r A) :=
    compatiblePairCocycles2 (muLoc F' l r A') (muLoc F l r A) (eD : Dec (F := F) A →* Dec (F := F') A')
      eD.continuous LinearMap.id continuous_id
      (fun g m => by
        show ((cycMod F' Ω' l r (Φ g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * m =
          ((cycMod F Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * m
        rw [hc]) z'
  have hEy : E (E.symm y') = y' := E.apply_symm_apply y'
  have hϖ : eO (eO.symm ϖ') = ϖ' := eO.apply_symm_apply ϖ'
  have key : iA (Submodule.Quotient.mk zz) = 1 := by
    refine hn (eO.symm ϖ') (E.symm y') (fun g => κ' (eD g)) (fun g => χ' (eD g)) zz
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hI, hϖ]; exact h1
    · rw [hI2, hϖ]; exact h2
    · apply E.injective
      rw [map_pow, hEy, h3, hE, ← heO, hϖ]
    · intro g
      apply E.injective
      have h := h4 (eD g)
      rw [← hΦ, hEy, ← hcoe, h, map_mul, map_pow, hEy]
    · intro g h
      show χ' (eD (g * h)) = χ' (eD g) + χ' (eD h)
      rw [map_mul, h5]
    · intro g hg
      exact h6 (eD g) ((hD (g : G F Ω)).2.1.1 hg)
    · intro g hg
      refine h7 (eD g) ?_
      rw [hN]
      exact ((hD (g : G F Ω)).2.2 _).1 hg
    · intro g h
      exact h8 (eD g) (eD h)
  rw [hrel zz z' ?_]
  · exact key
  · intro g h g' h' hg hh
    have e1 : g' = eD g := Subtype.ext hg
    have e2 : h' = eD h := Subtype.ext hh
    subst e1 e2
    rfl

end GlobalTheory.CompanionTheory.PTIso.Norm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsResidueStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_equiv_transports_residue : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ^ 2 ↔ eO x ∈ (eV v).asIdeal ^ 2) → (∀ v : HeightOneSpectrum (𝓞 F), normV (eV v) = normV v) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), (∀ σ : G F Ω, cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → (∀ σ : G F Ω, (σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') ∧ (σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') ∧ ∀ q : ℕ, IsFrob (F := F) A q σ ↔ IsFrob (F := F') A' q (Φ σ)) → ∀ (ζ : Ω) (v : HeightOneSpectrum (𝓞 F)) (iA : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)) (iA' : H2 (muLoc F' l r A') →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), (∀ (z : Z2 (muLoc F l r A)) (z' : Z2 (muLoc F' l r A')), (∀ (g h : Dec (F := F) A) (g' h' : Dec (F := F') A'), (g' : G F' Ω') = Φ g → (h' : G F' Ω') = Φ h → z'.1 (g', h') = z.1 (g, h)) → iA' (Submodule.Quotient.mk z') = iA (Submodule.Quotient.mk z)) → IsNormalised ζ A v iA → IsNormalised (E ζ) A' (eV v) iA' := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.Norm.isNormalised_transfer | exact GlobalTheory.CompanionTheory.PTIso.Norm.isNormalised_transfer | (intros; apply GlobalTheory.CompanionTheory.PTIso.Norm.isNormalised_transfer <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSubfieldModel
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace GlobalTheory.CompanionTheory.FieldModel

theorem exists_subfield_model : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω], ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField K) (_ : IsAlgClosure K (AlgebraicClosure ℚ)) (e : F ≃+* K) (E : Ω ≃+* (AlgebraicClosure ℚ)), ∀ x : F, E (algebraMap F Ω x) = algebraMap K (AlgebraicClosure ℚ) (e x) := by
  intro F Ω _ _ _ _ _
  let σ : F →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e : F ≃ₐ[ℚ] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  haveI fd : FiniteDimensional ℚ σ.fieldRange := e.toLinearEquiv.finiteDimensional
  haveI nf : NumberField σ.fieldRange := { to_charZero := inferInstance, to_finiteDimensional := fd }
  haveI alg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
      (AlgebraicClosure.isAlgebraic ℚ)
    convert h
  haveI ac : IsAlgClosure σ.fieldRange (AlgebraicClosure ℚ) :=
    ⟨AlgebraicClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) σ.fieldRange⟩
  refine ⟨σ.fieldRange, nf, ac, e.toRingEquiv, IsAlgClosure.equivOfEquiv Ω (AlgebraicClosure ℚ) e.toRingEquiv, fun x => ?_⟩
  exact IsAlgClosure.equivOfEquiv_algebraMap Ω (AlgebraicClosure ℚ) e.toRingEquiv x

end GlobalTheory.CompanionTheory.FieldModel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDualInjectiveEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDualInjectiveEquiv
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.ZModDual

private theorem finite_dual_zmod_and_card_le (n : ℕ) [NeZero n] (X : Type) [AddCommGroup X]
    [Module (ZMod n) X] [Finite X] :
    Finite (Module.Dual (ZMod n) X) ∧ Nat.card (Module.Dual (ZMod n) X) ≤ Nat.card X := by
  have hfin : Finite (Module.Dual (ZMod n) X) :=
    Finite.of_injective (fun φ : Module.Dual (ZMod n) X => (φ : X → ZMod n)) DFunLike.coe_injective
  refine ⟨hfin, ?_⟩
  letI := Fintype.ofFinite X
  let e : Module.Dual (ZMod n) X → AddChar X ℂ :=
    fun φ => (ZMod.stdAddChar (N := n)).compAddMonoidHom φ.toAddMonoidHom
  have he : Function.Injective e := by
    intro φ ψ h
    ext x
    have hx := DFunLike.congr_fun h x
    exact ZMod.injective_stdAddChar hx
  calc Nat.card (Module.Dual (ZMod n) X) ≤ Nat.card (AddChar X ℂ) :=
        Nat.card_le_card_of_injective e he
    _ = Nat.card X := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]

theorem equiv_dual_of_injective_pair :
    ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X]
      [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y],
      (∃ f : Y →ₗ[ZMod n] Module.Dual (ZMod n) X, Function.Injective f) →
      (∃ g : X →ₗ[ZMod n] Module.Dual (ZMod n) Y, Function.Injective g) →
      Nonempty (Y ≃ₗ[ZMod n] Module.Dual (ZMod n) X) ∧ Nat.card X = Nat.card Y := by
  intro n _ X Y _ _ _ _ _ _ hf hg
  obtain ⟨f, hf⟩ := hf
  obtain ⟨g, hg⟩ := hg
  obtain ⟨hXf, hXc⟩ := finite_dual_zmod_and_card_le n X
  obtain ⟨hYf, hYc⟩ := finite_dual_zmod_and_card_le n Y
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 := Nat.card_le_card_of_injective g hg
  have hXY : Nat.card X = Nat.card Y := by omega
  refine ⟨⟨LinearEquiv.ofBijective f ⟨hf, ?_⟩⟩, hXY⟩
  exact (hf.bijective_of_nat_card_le (by omega)).2

end GlobalTheory.CompanionTheory.ZModDual
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDualInjectiveEquivStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dual_injective_equiv : ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y], (∃ f : Y →ₗ[ZMod n] Module.Dual (ZMod n) X, Function.Injective f) → (∃ g : X →ₗ[ZMod n] Module.Dual (ZMod n) Y, Function.Injective g) → Nonempty (Y ≃ₗ[ZMod n] Module.Dual (ZMod n) X) ∧ Nat.card X = Nat.card Y := by
  first | exact @GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair | exact GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair | (intros; apply GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementD
theorem UpperTheory.Reformulated.B.LocallyTrivialClassesAddEquiv.main :
    ∀ {R ι H C : Type} [inst : CommRing R] [inst_1 : AddCommGroup H] [inst_2 : _root_.Module R H] [inst_3 : AddCommGroup C]
      {Hv Cv : ι → Type} [inst_4 : (v : ι) → AddCommGroup (Hv v)] [inst_5 : (v : ι) → AddCommGroup (Cv v)]
      (res : (v : ι) → H →+ Hv v) (pres : (v : ι) → C →+ Cv v) (E : H ≃+ C) (Ev : (v : ι) → Hv v ≃+ Cv v),
      (∀ (v : ι) (x : H), (Ev v : Hv v → Cv v) ((res v : H → Hv v) x) = (pres v : C → Cv v) ((E : H → C) x)) →
        ∀ (U : Submodule R H) (T : AddSubgroup C),
          (∀ (x : H), x ∈ U ↔ ∀ (v : ι), (res v : H → Hv v) x = (0 : Hv v)) →
            (∀ (y : C), y ∈ T ↔ ∀ (v : ι), (pres v : C → Cv v) y = (0 : Cv v)) → Nonempty (↥U ≃+ ↥T) := by
  intro R ι H C _ _ _ _ Hv Cv _ _ res pres E Ev hcomm U T hU hT
  have key : ∀ x : H, x ∈ U ↔ E x ∈ T := by
    intro x
    rw [hU, hT]
    refine forall_congr' fun v => ?_
    rw [← hcomm v x]
    constructor
    · intro h; rw [h, map_zero]
    · intro h
      have := congrArg (Ev v).symm h
      simpa using this
  exact ⟨{ toFun := fun x => ⟨E x.1, (key x.1).1 x.2⟩
           invFun := fun y => ⟨E.symm y.1, (key _).2 (by simpa using y.2)⟩
           left_inv := fun x => by ext; simp
           right_inv := fun y => by ext; simp
           map_add' := fun x y => by ext; simp }⟩
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsHyp
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace PositivityTheory.PTN

def LocHyp : Prop :=
  ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, (σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') ∧ (σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') ∧ ∀ q : ℕ, IsFrob (F := F) A q σ ↔ IsFrob (F := F') A' q (Φ σ)

def PtfsHyp : Prop :=
  ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)], PTConclAt K (AlgebraicClosure ℚ)

end PositivityTheory.PTN
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsShaFinal
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsShaDict
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsSha
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GroundTheory.ProfCoh GroundTheory.Global CategoryTheory

namespace PositivityTheory.Lit1.PTN

def PerfectQZ (X Y : Type) [AddCommGroup X] [AddCommGroup Y] : Prop :=
  Finite X ∧ Finite Y ∧ ∃ P : X →+ Y →+ QZ, Function.Bijective P ∧ Function.Bijective P.flip

theorem perfectQZ_symm {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (h : PerfectQZ X Y) :
    PerfectQZ Y X := by
  obtain ⟨hX, hY, P, h1, h2⟩ := h
  have e : P.flip.flip = P := by ext; rfl
  exact ⟨hY, hX, P.flip, h2, by rw [e]; exact h1⟩

theorem perfectQZ_of_addEquiv {X Y X' Y' : Type} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup X'] [AddCommGroup Y'] (eX : X ≃+ X') (eY : Y ≃+ Y') (h : PerfectQZ X' Y') :
    PerfectQZ X Y := by
  obtain ⟨hX, hY, P, h1, h2⟩ := h
  have bY : Function.Bijective (fun φ : Y' →+ QZ => φ.comp eY.toAddMonoidHom) :=
    Function.bijective_iff_has_inverse.2 ⟨fun ψ => ψ.comp eY.symm.toAddMonoidHom,
      fun φ => by ext; simp, fun ψ => by ext; simp⟩
  have bX : Function.Bijective (fun φ : X' →+ QZ => φ.comp eX.toAddMonoidHom) :=
    Function.bijective_iff_has_inverse.2 ⟨fun ψ => ψ.comp eX.symm.toAddMonoidHom,
      fun φ => by ext; simp, fun ψ => by ext; simp⟩
  refine ⟨Finite.of_equiv _ eX.symm.toEquiv, Finite.of_equiv _ eY.symm.toEquiv,
    (P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom, ?_, ?_⟩
  · have e : ⇑((P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom) =
        (fun φ : Y' →+ QZ => φ.comp eY.toAddMonoidHom) ∘ P ∘ eX := by
      funext x; ext y; rfl
    rw [e]
    exact bY.comp (h1.comp eX.bijective)
  · have e : ⇑((P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom).flip =
        (fun φ : X' →+ QZ => φ.comp eX.toAddMonoidHom) ∘ P.flip ∘ eY := by
      funext y; ext x; rfl
    rw [e]
    exact bX.comp (h2.comp eY.bijective)

theorem perfectPair_of_perfectQZ {n : ℕ} [NeZero n] {X Y : Type} [AddCommGroup X]
    [Module (ZMod n) X] [AddCommGroup Y] [Module (ZMod n) Y] (h : PerfectQZ X Y) :
    PerfectPair (R := ZMod n) X Y := by
  obtain ⟨hX, hY, P, h1, h2⟩ := h
  have torX : ∀ x : X, n • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  have torY : ∀ y : Y, n • y = 0 := fun y => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  have hP : ∀ x y, n • P x y = 0 := fun x y => by rw [← map_nsmul, torY, map_zero]
  let Q : X →+ (Y →ₗ[ZMod n] ZMod n) :=
    { toFun := fun x => (zmodOfQZ (P x) (hP x)).toZModLinearMap n
      map_zero' := by
        ext y; apply zmodToQZ_injective (n := n)
        simp [zmodToQZ_zmodOfQZ]
      map_add' := fun x x' => by
        ext y; apply zmodToQZ_injective (n := n)
        simp [zmodToQZ_zmodOfQZ] }
  have hQ : ∀ x y, zmodToQZ n (Q.toZModLinearMap n x y) = P x y := fun x y =>
    zmodToQZ_zmodOfQZ (P x) (hP x) y
  refine ⟨hX, hY, Q.toZModLinearMap n, ⟨fun x x' hxx => h1.1 ?_, fun φ => ?_⟩,
    ⟨fun y y' hyy => h2.1 ?_, fun φ => ?_⟩⟩
  · ext y; rw [← hQ, ← hQ, hxx]
  · obtain ⟨x, hx⟩ := h1.2 ((zmodToQZ n).comp φ.toAddMonoidHom)
    refine ⟨x, LinearMap.ext fun y => zmodToQZ_injective (n := n) ?_⟩
    rw [hQ, hx]; rfl
  · ext x
    have := congrArg (fun f => zmodToQZ n (f x)) hyy
    exact (hQ x y).symm.trans (this.trans (hQ x y'))
  · obtain ⟨y, hy⟩ := h2.2 ((zmodToQZ n).comp φ.toAddMonoidHom)
    refine ⟨y, LinearMap.ext fun x => zmodToQZ_injective (n := n) ?_⟩
    show zmodToQZ n (Q.toZModLinearMap n x y) = _
    rw [hQ]
    exact DFunLike.congr_fun hy x

def ShaDictFS : Prop :=
  ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (l : ℕ) [Fact l.Prime] (r : ℕ),
  (l ≠ 2 ∨ IsTotallyComplex K) → 0 < r →
  ∀ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ (l ^ r) → ∀ inv : InvFam K (AlgebraicClosure ℚ) l r,
  InvNormalised ζ inv →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), ContainsAbove S l →
  ∀ (Av : S → ValuationSubring (AlgebraicClosure ℚ)), (∀ v, IsPlaceOver (Av v) v.1) →
  ∀ (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod K (AlgebraicClosure ℚ) l r),
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) M)
    (hρ : ContAction ρ),
    (∃ (K' : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K'.1))) (_ : Fintype S')
      (ιs : ∀ v : S', AlgebraicClosure ℚ →ₐ[K'.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K'.1)).adicCompletion K'.1))
      (N : ℕ) (_ : NeZero N)
      (_ : ∀ v : HeightOneSpectrum (𝓞 K'.1), ((N : ℕ) : 𝓞 K'.1) ∈ v.asIdeal → v ∈ S')
      (_ : Odd N ∨ IsTotallyComplex K'.1)
      (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 (AlgebraicClosure ℚ) S'))
      (hAd : IsDiscreteRep A) (hAf : Finite A) (_ : ∀ m : A, N • m = 0),
      letI : IsDiscreteRep (dualRep (gsRoots S' N) A) :=
        @isDiscreteRep_dualRep _ _ _ _ _ _ (gsRoots S' N) A (isDiscreteRep_gsRoots S' N) hAd hAf
      Nonempty (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) A 1) ∧
      Nonempty (Sha2 ρ (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) (dualRep (gsRoots S' N) A) 2)) ∧
    (∃ (K' : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K'.1))) (_ : Fintype S')
      (ιs : ∀ v : S', AlgebraicClosure ℚ →ₐ[K'.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K'.1)).adicCompletion K'.1))
      (N : ℕ) (_ : NeZero N)
      (_ : ∀ v : HeightOneSpectrum (𝓞 K'.1), ((N : ℕ) : 𝓞 K'.1) ∈ v.asIdeal → v ∈ S')
      (_ : Odd N ∨ IsTotallyComplex K'.1)
      (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 (AlgebraicClosure ℚ) S'))
      (hAd : IsDiscreteRep A) (hAf : Finite A) (_ : ∀ m : A, N • m = 0),
      letI : IsDiscreteRep (dualRep (gsRoots S' N) A) :=
        @isDiscreteRep_dualRep _ _ _ _ _ _ (gsRoots S' N) A (isDiscreteRep_gsRoots S' N) hAd hAf
      Nonempty (Sha1 ρ (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) A 1) ∧
      Nonempty (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) (dualRep (gsRoots S' N) A) 2))

section FoundSide

attribute [local instance 2000] Rep.hV2

theorem perfectQZ_of_found {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (h : ∃ (K' : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K'.1))) (_ : Fintype S')
      (ιs : ∀ v : S', AlgebraicClosure ℚ →ₐ[K'.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K'.1)).adicCompletion K'.1))
      (N : ℕ) (_ : NeZero N)
      (_ : ∀ v : HeightOneSpectrum (𝓞 K'.1), ((N : ℕ) : 𝓞 K'.1) ∈ v.asIdeal → v ∈ S')
      (_ : Odd N ∨ IsTotallyComplex K'.1)
      (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 (AlgebraicClosure ℚ) S'))
      (hAd : IsDiscreteRep A) (hAf : Finite A) (_ : ∀ m : A, N • m = 0),
      letI : IsDiscreteRep (dualRep (gsRoots S' N) A) :=
        @isDiscreteRep_dualRep _ _ _ _ _ _ (gsRoots S' N) A (isDiscreteRep_gsRoots S' N) hAd hAf
      Nonempty (Y ≃+ ptSha (gsFinFamily S' ιs) A 1) ∧
      Nonempty (X ≃+ ptSha (gsFinFamily S' ιs) (dualRep (gsRoots S' N) A) 2)) : PerfectQZ X Y := by
  obtain ⟨K', S', _, ιs, N, _, hS, hK, A, _, _, hA, ⟨eY⟩, ⟨eX⟩⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := poitouTate_sha_gs (K := K') (N := N) S' ιs hS hK A hA
  exact perfectQZ_of_addEquiv eX eY (perfectQZ_symm ⟨h1, h2, _, h3, h4⟩)

end FoundSide

set_option maxHeartbeats 1000000 in
theorem shaCmpFS_of_dict (h : ShaDictFS) : ShaCmpFS := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  have : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  have hh := h K l r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M ρ hρ
  exact ⟨perfectPair_of_perfectQZ
      (perfectQZ_of_found (X := Sha2 ρ (locFam S Av) (continuous_locFam S Av))
        (Y := Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) hh.1),
    perfectPair_of_perfectQZ
      (perfectQZ_of_found (X := Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av))
        (Y := Sha1 ρ (locFam S Av) (continuous_locFam S Av)) hh.2)⟩

end PositivityTheory.Lit1.PTN
end
end

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GroundTheory.ProfCoh CategoryTheory

namespace PositivityTheory.Lit1.PTN

theorem addEquiv_of_resCmp {R ι H C : Type} [CommRing R] [AddCommGroup H] [Module R H]
    [AddCommGroup C] {Hv Cv : ι → Type} [∀ v, AddCommGroup (Hv v)] [∀ v, AddCommGroup (Cv v)]
    (res : ∀ v, H →+ Hv v) (pres : ∀ v, C →+ Cv v) (E : H ≃+ C) (Ev : ∀ v, Hv v ≃+ Cv v)
    (h : ∀ v x, Ev v (res v x) = pres v (E x)) (U : Submodule R H) (T : AddSubgroup C)
    (hU : ∀ x, x ∈ U ↔ ∀ v, res v x = 0) (hT : ∀ y, y ∈ T ↔ ∀ v, pres v y = 0) :
    Nonempty (U ≃+ T) :=
  _root_.UpperTheory.Reformulated.B.LocallyTrivialClassesAddEquiv.main res pres E Ev h U T hU hT

section FoundSide

attribute [local instance 2000] Rep.hV2

theorem mem_ptSha_iff' {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
    [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) (A : Rep.{0} (ULift.{0} ℤ) G)
    [IsDiscreteRep A] (n : ℕ) (x : cohomology A n) : x ∈ ptSha φ A n ↔ ∀ v, ptRes φ A v n x = 0 := by
  rw [mem_ptSha, funext_iff]
  rfl

set_option maxHeartbeats 1000000 in
theorem shaIso_of_rep (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) ≃ₜ*
        galUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))))
    (ιs : ∀ v : (S : Set (HeightOneSpectrum (𝓞 K))), AlgebraicClosure ℚ →ₐ[K]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
    (ev : ∀ v : S, (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 K)).adicCompletion K]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ≃* Dec (F := K) (Av v))
    (hevc : ∀ v, Continuous (ev v) ∧ Continuous (ev v).symm)
    (hev : ∀ (v : S) σ, e (locFam S Av v (ev v σ)) =
        gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ σ)
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation R (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) M)
    (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))))
    [IsDiscreteRep A] (eM : M ≃+ A.V) (hM : ∀ g m, eM (rho g m) = A.ρ (e g) (eM m)) :
    Nonempty (Sha1 rho (locFam S Av) (continuous_locFam S Av) ≃+
        ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A 1) ∧
    Nonempty (Sha2 rho (locFam S Av) (continuous_locFam S Av) ≃+
        ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A 2) := by
  have hT : ∀ n (y : cohomology A n), y ∈ ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A n ↔
      ∀ v : S, ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) A v n y = 0 := by
    intro n y
    exact (mem_ptSha_iff' (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A n y).trans
      ⟨fun h v => h ⟨v.1, Finset.mem_coe.2 v.2⟩, fun h w => h ⟨w.1, Finset.mem_coe.1 w.2⟩⟩
  obtain ⟨E1, Ev1, h1⟩ := resCmp1' e (locFam S Av) (continuous_locFam S Av)
    (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) ev (fun v => (hevc v).1) (fun v => (hevc v).2) hev rho hc A eM hM
  obtain ⟨E2, Ev2, h2⟩ := resCmp2B e (locFam S Av) (continuous_locFam S Av)
    (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) ev (fun v => (hevc v).1) (fun v => (hevc v).2) hev rho hc A eM hM
  have hU1 : ∀ x, x ∈ Sha1 rho (locFam S Av) (continuous_locFam S Av) ↔
      ∀ v, (resH1 rho (locFam S Av v) (continuous_locFam S Av v)).toAddMonoidHom x = 0 := by
    intro x
    simp only [Sha1, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  have hU2 : ∀ x, x ∈ Sha2 rho (locFam S Av) (continuous_locFam S Av) ↔
      ∀ v, (resH2 rho (locFam S Av v) (continuous_locFam S Av v)).toAddMonoidHom x = 0 := by
    intro x
    simp only [Sha2, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  exact ⟨addEquiv_of_resCmp
      (fun v => (resH1 rho (locFam S Av v) (continuous_locFam S Av v)).toAddMonoidHom)
      (fun v => ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) A v 1) E1 Ev1 h1 _ _ hU1 (hT 1),
    addEquiv_of_resCmp
      (fun v => (resH2 rho (locFam S Av v) (continuous_locFam S Av v)).toAddMonoidHom)
      (fun v => ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) A v 2) E2 Ev2 h2 _ _ hU2 (hT 2)⟩

end FoundSide

end PositivityTheory.Lit1.PTN
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsBidual
noncomputable section

open CategoryTheory GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem bidualCmp {G : Type} [Group G] (D A : Rep.{0} (ULift.{0} ℤ) G) (N : ℕ) [NeZero N]
    (hD : Nonempty (D ≃+ ZMod N)) [Finite A] (hA : ∀ m : A, N • m = 0) :
    ∃ eB : A.V ≃+ (dualRep D (dualRep D A)).V,
      ∀ g a, eB (A.ρ g a) = (dualRep D (dualRep D A)).ρ g (eB a) := by
  have hb := bijective_toDualDual (D := D) (M := A) hD hA
  let f : A.V →+ (dualRep D (dualRep D A)).V :=
    { toFun := (toDualDual D A).hom, map_zero' := map_zero _, map_add' := map_add _ }
  refine ⟨AddEquiv.ofBijective f hb, fun g a => ?_⟩
  exact Rep.hom_comm_apply (toDualDual D A) g a

end PositivityTheory.Lit1.PTN
end
end

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GroundTheory.ProfCoh GroundTheory.Global CategoryTheory

namespace PositivityTheory.Lit1.PTN

abbrev toFS (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] : FiniteSubfield :=
  ⟨K, inferInstance⟩

section
attribute [local instance 2000] Rep.hV2
theorem finite_dualRep' {G : Type} [Group G] (D A : Rep.{0} (ULift.{0} ℤ) G) [Finite D] [Finite A] :
    Finite (dualRep D A) := inferInstance
end

set_option maxHeartbeats 0 in
theorem shaDictFS : ShaDictFS := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨e, he⟩ := gsEquiv_toGS' K (S : Set (HeightOneSpectrum (𝓞 K)))
  obtain ⟨ιs, ev, hevc, hev⟩ := localCmp' K S Av hAv e he
  obtain ⟨A, hAd, eM, hM⟩ := repCmp e ρ hρ
  have hc' : ContAction (twDual μ ρ) :=
    GlobalTheory.CompanionTheory.GalDual.contAction_twDual K (AlgebraicClosure ℚ) l r M S Av μ ρ hρ hμ
  obtain ⟨eD, hD, -⟩ := dualCmp' (toFS K) S hr ζ hζ hS e he μ hμ ρ A eM hM
  have hSN : ∀ v : HeightOneSpectrum (𝓞 K), ((l ^ r : ℕ) : 𝓞 K) ∈ v.asIdeal →
      v ∈ (S : Set (HeightOneSpectrum (𝓞 K))) := by
    intro v hv
    rw [Nat.cast_pow] at hv
    exact Finset.mem_coe.2 (hS v (v.isPrime.mem_of_pow_mem r hv))
  have hK : Odd (l ^ r) ∨ IsTotallyComplex K :=
    hl.imp (fun h => ((Fact.out : l.Prime).odd_of_ne_two h).pow) id
  have hDZ : Nonempty (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r) ≃+ ZMod (l ^ r)) :=
    nonempty_addEquiv_gsRoots_of_mem (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) hSN
  haveI : Finite (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) := Finite.of_equiv _ hDZ.some.symm.toEquiv
  haveI hFA : Finite A := Finite.of_equiv M eM.toEquiv
  have htor : ∀ m : A, (l ^ r) • m = 0 := fun m => by
    obtain ⟨x, rfl⟩ := eM.surjective m
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)), ZMod.natCast_self, zero_smul,
      map_zero]
  have htor1 : ∀ f : dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A, (l ^ r) • f = 0 :=
    nsmul_dualRep_eq_zero (fun d => nsmul_gsRoots (K := (toFS K)) _ _ d)
  haveI hDd : IsDiscreteRep (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) :=
    isDiscreteRep_dualRep _ _
  haveI hF1 : Finite (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) := finite_dualRep' _ _
  haveI hDDd : IsDiscreteRep (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A)) := isDiscreteRep_dualRep _ _
  obtain ⟨eB, hB⟩ := bidualCmp (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A (l ^ r) hDZ htor
  have hM'' : ∀ g m, (eM.trans eB) (ρ g m) = (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r))
      (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A)).ρ (e g) ((eM.trans eB) m) := by
    intro g m
    simp only [AddEquiv.trans_apply, hM, hB]
  have X1 : Nonempty (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) 1) :=
    (shaIso_of_rep K S Av e ιs ev hevc hev (twDual μ ρ) hc' (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) eD hD).1
  have X2 : Nonempty (Sha2 ρ (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A)) 2) :=
    (shaIso_of_rep K S Av e ιs ev hevc hev ρ hρ (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A)) (eM.trans eB) hM'').2
  have X3 : Nonempty (Sha1 ρ (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A 1) :=
    (shaIso_of_rep K S Av e ιs ev hevc hev ρ hρ A eM hM).1
  have X4 : Nonempty (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) 2) :=
    (shaIso_of_rep K S Av e ιs ev hevc hev (twDual μ ρ) hc' (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) eD hD).2
  refine ⟨⟨(toFS K), (S : Set (HeightOneSpectrum (𝓞 K))), inferInstance, ιs, l ^ r, inferInstance, hSN, hK, (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A), hDd, hF1, htor1, ?_, ?_⟩,
    ⟨(toFS K), (S : Set (HeightOneSpectrum (𝓞 K))), inferInstance, ιs, l ^ r, inferInstance, hSN, hK, A, hAd, hFA, htor, ?_, ?_⟩⟩
  · exact X1
  · exact X2
  · exact X3
  · exact X4

theorem shaCmpFS' : ShaCmpFS := shaCmpFS_of_dict shaDictFS

end PositivityTheory.Lit1.PTN
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bridge
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtConclOfIsoOf
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace PositivityTheory.PTN

theorem ptConcl_of_iso_of (hL : PositivityTheory.PTN.LocHyp) : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → PTConclAt F' Ω' → PTConclAt F Ω := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE hPT
  intro l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.galois_group_transport_isomorphism F Ω F' Ω' e E hE
  obtain ⟨eO, eV, heO, hV, hV2, hN⟩ := GlobalTheory.T.ring_isomorphism_transports_places F F' e
  have hloc := hL F Ω F' Ω' e E hE Φ hΦ
  have hpl := GlobalTheory.T.ring_equiv_transports_decomposition F Ω F' Ω' e E hE eO eV heO hV
  have hcyc := GlobalTheory.T.ring_equiv_cyclotomic_character F Ω F' Ω' e E hE Φ hΦ l r
  obtain ⟨inv', hinv'⟩ := GlobalTheory.T.ring_equiv_transports_inertia F Ω F' Ω' e E hE Φ hΦ
    (fun A A' hA σ => (hloc A A' hA σ).1) l r hcyc inv

  let S' : Finset (HeightOneSpectrum (𝓞 F')) := S.map eV.toEmbedding
  have hSS : ∀ v, v ∈ (S : Set (HeightOneSpectrum (𝓞 F))) ↔
      eV v ∈ (S' : Set (HeightOneSpectrum (𝓞 F'))) := by
    intro v; simp [S']
  let eI : S ≃ S' := Equiv.subtypeEquiv eV (fun v => by simp [S'])
  have heI : ∀ v : S, (eI v : HeightOneSpectrum (𝓞 F')) = eV v := fun _ => rfl
  let Av' : S' → ValuationSubring Ω' := fun v' => (Av (eI.symm v')).comap E.symm.toRingHom
  have hAv'' : ∀ (v : S) (x : Ω), E x ∈ Av' (eI v) ↔ x ∈ Av v := by
    intro v x
    simp [Av', ValuationSubring.mem_comap]
  have hPl' : ∀ v' : S', IsPlaceOver (Av' v') v'.1 := by
    intro v'
    obtain ⟨v, rfl⟩ := eI.surjective v'
    exact (hpl _ _ (hAv'' v) v.1).1 (hAv v)

  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.galois_quotient_equiv_of_matching_places F Ω F' Ω' e E hE Φ hΦ eV hpl
    (fun A A' hA σ => (hloc A A' hA σ).2.1) _ _ hSS
  let μ' : GS Ω' (S' : Set (HeightOneSpectrum (𝓞 F'))) →* (ZMod (l ^ r))ˣ :=
    μ.comp (Ψ.symm : GS Ω' (S' : Set (HeightOneSpectrum (𝓞 F'))) →* _)
  have hμ' : μ'.comp (toGS Ω' _) = cycMod F' Ω' l r := by
    ext1 τ
    obtain ⟨σ, rfl⟩ := Φ.surjective τ
    have h1 : Ψ.symm (toGS Ω' _ (Φ σ)) = toGS Ω _ σ := by rw [← hΨ]; simp
    have h2 : μ (toGS Ω _ σ) = cycMod F Ω l r σ := DFunLike.congr_fun hμ σ
    show μ (Ψ.symm (toGS Ω' _ (Φ σ))) = _
    rw [h1, h2, hcyc]
  let ρ' : Representation (ZMod (l ^ r)) (GS Ω' (S' : Set (HeightOneSpectrum (𝓞 F')))) M :=
    ρ.comp (Ψ.symm : GS Ω' (S' : Set (HeightOneSpectrum (𝓞 F'))) →* _)
  have hρ' : ContAction ρ' := hρ.comp' Ψ.symm.continuous

  have hl' : l ≠ 2 ∨ IsTotallyComplex F' := hl.imp id (GlobalTheory.T.totally_complex_of_ring_equiv F F' e)
  have hζ' : IsPrimitiveRoot (E ζ) (l ^ r) := hζ.map_of_injective E.injective
  have hnorm' : InvNormalised (E ζ) inv' := by
    intro A' v' hP
    obtain ⟨v, rfl⟩ := eV.surjective v'
    let A : ValuationSubring Ω := A'.comap E.toRingHom
    have hA : ∀ x, E x ∈ A' ↔ x ∈ A := fun x => by simp [A, ValuationSubring.mem_comap]
    have hP0 : IsPlaceOver A v := (hpl A A' hA v).2 hP
    refine ⟨(hinv' A A' hA).1 (hinv A v hP0).1, ?_⟩
    exact GlobalTheory.T.ring_equiv_transports_residue F Ω F' Ω' e E hE Φ hΦ eO eV heO hV hV2 hN l r hcyc A A' hA (hloc A A' hA) ζ v
      (inv A) (inv' A') (hinv' A A' hA).2 (hinv A v hP0).2
  have hS' : ContainsAbove S' l := by
    intro v' hv'
    obtain ⟨v, rfl⟩ := eV.surjective v'
    have : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal := by
      rw [hV, map_natCast]; exact hv'
    exact Finset.mem_map_of_mem _ (hS v this)
  obtain ⟨h9, hsha⟩ := hPT l r hl' hr (E ζ) hζ' inv' hnorm' S' hS' Av' hPl' μ' hμ' M ρ' hρ'

  let eD : ∀ v : S, Dec (F := F) (Av v) ≃ₜ* Dec (F := F') (Av' (eI v)) := fun v =>
    subgroupIso Φ _ _ (fun σ => (hloc _ _ (hAv'' v) σ).1)
  have hcomp : ∀ (v : S) (d : Dec (F := F) (Av v)),
      locFam S' Av' (eI v) (eD v d) = Ψ (locFam S Av v d) := by
    intro v d
    exact (hΨ (d : G F Ω)).symm
  have hχ : ∀ g, μ' (Ψ g) = μ g := fun g => by simp [μ']
  have hρc : ∀ g m, ρ' (Ψ g) m = ρ g m := fun g m => by simp [ρ']
  refine ⟨?_, ?_⟩
  · refine (nineTermExact_iff S Av μ _ ρ hρ).2 ?_
    refine GlobalTheory.T.poitou_tate_sequence_transport (locFam S Av) (continuous_locFam S Av) (locFam S' Av') (continuous_locFam S' Av')
      μ μ' ρ ρ' Ψ eI eD hcomp hχ hρc _ _ hρ hρ' ?_ ((nineTermExact_iff S' Av' μ' _ ρ' hρ').1 h9)
    intro v z z' hz
    refine (hinv' _ _ (hAv'' v)).2 (cocycles2Map _ _ LinearMap.id continuous_id (locFam_apply_eq S Av μ hμ v) z)
      (cocycles2Map _ _ LinearMap.id continuous_id (locFam_apply_eq S' Av' μ' hμ' (eI v)) z') ?_
    intro g h g' h' hg hh
    have e1 : g' = eD v g := Subtype.ext hg
    have e2 : h' = eD v h := Subtype.ext hh
    subst e1 e2
    exact hz g h
  · exact (shaDual_iff S Av μ ρ).2 (GlobalTheory.T.tate_shafarevich_transport (locFam S Av) (continuous_locFam S Av) (locFam S' Av')
      (continuous_locFam S' Av') μ μ' ρ ρ' Ψ eI eD hcomp hχ hρc ((shaDual_iff S' Av' μ' ρ').1 hsha))

end PositivityTheory.PTN
end
end

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.PTN

theorem ptConclAt_all_of (hfs : PtfsHyp) (hL : LocHyp) :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω],
      PTConclAt F Ω := by
  intro F Ω _ _ _ _ _
  obtain ⟨K, hK, hC, e, E, h⟩ := GlobalTheory.CompanionTheory.FieldModel.exists_subfield_model F Ω
  exact ptConcl_of_iso_of hL F Ω K (AlgebraicClosure ℚ) e E h (hfs K)

theorem poitouTateNormalised_of (hfs : PtfsHyp) (hL : LocHyp) (hvan : VanishAll) :
    PoitouTateNormalised := by
  intro F Ω _ _ _ _ _ l _ r hl hr ζ hζ
  obtain ⟨inv, hinv⟩ := GlobalTheory.CompanionTheory.PoitouTateInv.exists_invFam_normalised F Ω l r hr ζ hζ
  refine ⟨inv, hinv, ?_⟩
  intro S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  have h := ptConclAt_all_of hfs hL F Ω l r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M ρ hρ
  exact ⟨h.1, h.2, hvan F Ω l r hl hr S hS M ρ hρ⟩

end PositivityTheory.PTN
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsHypOfCmp
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsShaHalf
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

theorem shaHalf_of_perfectPair {n : ℕ} [NeZero n] {X Y : Type} [AddCommGroup X]
    [Module (ZMod n) X] [AddCommGroup Y] [Module (ZMod n) Y] (h : PerfectPair (R := ZMod n) X Y) :
    Finite Y ∧ Finite X ∧ Nonempty (X ≃ₗ[ZMod n] Module.Dual (ZMod n) Y) ∧
      Nat.card Y = Nat.card X := by
  obtain ⟨hX, hY, P, hP, hP'⟩ := h
  have key := GlobalTheory.T.finite_dual_injective_equiv n Y X ⟨P, hP.1⟩ ⟨P.flip, hP'.1⟩
  exact ⟨hY, hX, key.1, key.2⟩

section Published

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)

theorem shaDual_of_perfectPair
    (h1 : PerfectPair (R := ZMod (l ^ r)) (Sha2 ρ (locFam S Av) (continuous_locFam S Av))
      (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)))
    (h2 : PerfectPair (R := ZMod (l ^ r)) (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av))
      (Sha1 ρ (locFam S Av) (continuous_locFam S Av))) : ShaDual S Av μ ρ := by
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  exact ⟨shaHalf_of_perfectPair h1, shaHalf_of_perfectPair h2⟩

end Published

end PositivityTheory.Lit1.PTN
end
end

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN


private theorem exact_of_transfer {R : Type} [CommRing R] {A B C A' B' C' : Type} [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup A'] [Module R A'] [AddCommGroup B']
    [Module R B'] [AddCommGroup C'] [Module R C'] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (f' : A' →ₗ[R] B') (g' : B' →ₗ[R] C') (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C')
    (u v : Rˣ) (hf : ∀ a, f' (eA a) = u • eB (f a)) (hg : ∀ b, g' (eB b) = v • eC (g b))
    (h : Function.Exact f' g') : Function.Exact f g := by
  unfold Function.Exact at h ⊢
  intro b
  constructor
  · intro hb
    have h1 : g' (eB b) = 0 := by rw [hg, hb, map_zero, smul_zero]
    obtain ⟨a', ha'⟩ := (h (eB b)).1 h1
    refine ⟨(u : R) • eA.symm a', eB.injective ?_⟩
    have := hf (eA.symm a')
    rw [LinearEquiv.apply_symm_apply, ha'] at this
    rw [map_smul, map_smul, this, Units.smul_def]
  · rintro ⟨a, rfl⟩
    have h2 : g' (f' (eA a)) = 0 := (h _).2 ⟨_, rfl⟩
    rw [hf, Units.smul_def, map_smul, hg, ← Units.smul_def, smul_eq_zero_iff_eq,
      smul_eq_zero_iff_eq, LinearEquiv.map_eq_zero_iff] at h2
    exact h2

theorem nineTermExact_of_nineCmp {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Av : S → ValuationSubring Ω)
    (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
    (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hρ : ContAction ρ)
    (h : NineCmp (loc0 S Av ρ) (tr0 S Av μ j ρ) (loc1 S Av ρ) (tr1 S Av μ j ρ hρ)
      (loc2 S Av ρ) (tr2 S Av μ j ρ)) : NineTermExact S Av μ j ρ hρ := by
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7, BetaSesquilinearity, g0, g1, g2, g3, g4, g5, g6, g7,
    e0, e1, e2, e3, e4, e5, e6, e7, e8, u, h0, h1, h3, h4, h6, h7,
    i0, x01, x12, x23, x34, x45, x56, x67, s7⟩ := h
  have k2 : ∀ a, g2 (e2 a) = (1 : (ZMod (l ^ r))ˣ) • e3 ((e3.symm.toLinearMap ∘ₗ g2 ∘ₗ e2.toLinearMap) a) := by
    intro a; rw [one_smul]; exact (e3.apply_symm_apply _).symm
  have k5 : ∀ a, g5 (e5 a) = (1 : (ZMod (l ^ r))ˣ) • e6 ((e6.symm.toLinearMap ∘ₗ g5 ∘ₗ e5.toLinearMap) a) := by
    intro a; rw [one_smul]; exact (e6.apply_symm_apply _).symm
  refine ⟨e3.symm.toLinearMap ∘ₗ g2 ∘ₗ e2.toLinearMap, e6.symm.toLinearMap ∘ₗ g5 ∘ₗ e5.toLinearMap,
    ?_, exact_of_transfer _ _ _ _ e0 e1 e2 _ _ h0 h1 x01,
    exact_of_transfer _ _ _ _ e1 e2 e3 _ _ h1 k2 x12,
    exact_of_transfer _ _ _ _ e2 e3 e4 _ _ k2 h3 x23,
    exact_of_transfer _ _ _ _ e3 e4 e5 _ _ h3 h4 x34,
    exact_of_transfer _ _ _ _ e4 e5 e6 _ _ h4 k5 x45,
    exact_of_transfer _ _ _ _ e5 e6 e7 _ _ k5 h6 x56,
    exact_of_transfer _ _ _ _ e6 e7 e8 _ _ h6 h7 x67, ?_⟩
  · intro a b hab
    apply e0.injective
    apply i0
    rw [h0, h0, hab]
  · intro y
    obtain ⟨b, hb⟩ := s7 (e8 y)
    refine ⟨((u 5 : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) • e7.symm b, e8.injective ?_⟩
    have := h7 (e7.symm b)
    rw [LinearEquiv.apply_symm_apply, hb] at this
    rw [map_smul, map_smul, this, Units.smul_def]

theorem ptfsHyp_of_cmp (hN : NineCmpFS) (hS : ShaCmpFS) : PositivityTheory.PTN.PtfsHyp := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS' Av hAv μ hμ M _ _ _ _ _ ρ hρ
  exact ⟨nineTermExact_of_nineCmp S Av μ _ ρ hρ
      (hN K l r hl hr ζ hζ inv hinv S hS' Av hAv μ hμ M ρ hρ),
    shaDual_of_perfectPair S Av μ ρ (hS K l r hl hr ζ hζ inv hinv S hS' Av hAv μ hμ M ρ hρ).1
      (hS K l r hl hr ζ hζ inv hinv S hS' Av hAv μ hμ M ρ hρ).2⟩

end PositivityTheory.Lit1.PTN
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.MemDecompositionSubgroupIff
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso Pointwise

namespace PositivityTheory.PTNLoc

theorem mem_decompositionSubgroup_iff {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] (A : ValuationSubring Ω) (σ : G F Ω) :
    σ ∈ A.decompositionSubgroup F ↔ ∀ x, σ x ∈ A ↔ x ∈ A := by
  constructor
  · intro h x
    exact ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec (F := F) h x
  · intro h
    show σ • A = A
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    have := h ((σ⁻¹ : G F Ω) y)
    rw [ReciprocityTheory.Gal.mul_inv_apply] at this
    exact this.symm

theorem valuation_le_one_transport {Ω Ω' : Type} [Field Ω] [Field Ω'] (E : Ω ≃+* Ω')
    {A : ValuationSubring Ω} {A' : ValuationSubring Ω'} (hA : ∀ x, E x ∈ A' ↔ x ∈ A) (x : Ω) :
    A'.valuation (E x) ≤ 1 ↔ A.valuation x ≤ 1 := by
  rw [A'.valuation_le_one_iff, A.valuation_le_one_iff]
  exact hA x

theorem valuation_lt_one_transport {Ω Ω' : Type} [Field Ω] [Field Ω'] (E : Ω ≃+* Ω')
    {A : ValuationSubring Ω} {A' : ValuationSubring Ω'} (hA : ∀ x, E x ∈ A' ↔ x ∈ A) (x : Ω) :
    A'.valuation (E x) < 1 ↔ A.valuation x < 1 := by
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', ← map_inv₀ E x,
    hA, hA, map_eq_zero_iff E E.injective]

theorem locHyp : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, (σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') ∧ (σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') ∧ ∀ q : ℕ, IsFrob (F := F) A q σ ↔ IsFrob (F := F') A' q (Φ σ) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ A A' hA σ
  have hdec : σ ∈ A.decompositionSubgroup F ↔ Φ σ ∈ A'.decompositionSubgroup F' := by
    rw [mem_decompositionSubgroup_iff, mem_decompositionSubgroup_iff]
    constructor
    · intro h y
      obtain ⟨x, rfl⟩ := E.surjective y
      rw [hΦ, hA, hA]
      exact h x
    · intro h x
      have := h (E x)
      rwa [hΦ, hA, hA] at this
  refine ⟨hdec, ?_, fun q => ?_⟩
  · show (σ ∈ A.decompositionSubgroup F ∧ _) ↔ (Φ σ ∈ A'.decompositionSubgroup F' ∧ _)
    refine and_congr hdec ⟨fun h y hy => ?_, fun h x hx => ?_⟩
    · obtain ⟨x, rfl⟩ := E.surjective y
      rw [hΦ, ← map_sub E, valuation_lt_one_transport E hA]
      exact h x ((valuation_le_one_transport E hA x).1 hy)
    · have := h (E x) ((valuation_le_one_transport E hA x).2 hx)
      rwa [hΦ, ← map_sub E, valuation_lt_one_transport E hA] at this
  · show (σ ∈ A.decompositionSubgroup F ∧ _) ↔ (Φ σ ∈ A'.decompositionSubgroup F' ∧ _)
    refine and_congr hdec ⟨fun h y hy => ?_, fun h x hx => ?_⟩
    · obtain ⟨x, rfl⟩ := E.surjective y
      rw [hΦ, ← map_pow E x q, ← map_sub E, valuation_lt_one_transport E hA]
      exact h x ((valuation_le_one_transport E hA x).1 hy)
    · have := h (E x) ((valuation_le_one_transport E hA x).2 hx)
      rwa [hΦ, ← map_pow E x q, ← map_sub E, valuation_lt_one_transport E hA] at this

end PositivityTheory.PTNLoc
end

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.PTN

theorem locHyp_holds : LocHyp := PositivityTheory.PTNLoc.locHyp

theorem poitouTateNormalised_of_ptfs (hfs : PtfsHyp) (hvan : VanishAll) :
    PoitouTateNormalised :=
  poitouTateNormalised_of hfs locHyp_holds hvan

theorem poitouTateNormalised_of_cmp (hN : PositivityTheory.Lit1.PTN.NineCmpFS) (hS : PositivityTheory.Lit1.PTN.ShaCmpFS) :
    PoitouTateNormalised :=
  poitouTateNormalised_of_ptfs (PositivityTheory.Lit1.PTN.ptfsHyp_of_cmp hN hS) PositivityTheory.Lit1.GFVanish.vanishAll

theorem poitouTateNormalised_of_nine (hN : PositivityTheory.Lit1.PTN.NineCmpFS) : PoitouTateNormalised :=
  poitouTateNormalised_of_cmp hN PositivityTheory.Lit1.PTN.shaCmpFS'

end PositivityTheory.PTN
