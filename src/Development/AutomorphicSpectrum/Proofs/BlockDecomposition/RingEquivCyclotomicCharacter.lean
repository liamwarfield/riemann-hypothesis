module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivCyclotomicCharacter
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivCyclotomicCharacter
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

theorem apply_eq_pow_cycMod_val {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω) {ζ : Ω} (hζ : ζ ^ (l ^ r) = 1) :
    σ ζ = ζ ^ ((cycMod F Ω l r σ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have key := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G F Ω) Ω σ) ζ hζ
  simpa [cycMod, cycZ] using key

theorem cycMod_intrinsic : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω), cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ l _ r σ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  have h1 := apply_eq_pow_cycMod_val (F := F) (Ω := Ω) l r σ hζ.pow_eq_one
  have h2 := apply_eq_pow_cycMod_val (F := F') (Ω := Ω') l r (Φ σ) (ζ := E ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hζ' : IsPrimitiveRoot (E ζ) (l ^ r) := hζ.map_of_injective E.injective
  rw [hΦ, h1, map_pow] at h2
  have hv := hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2
  apply Units.ext
  exact ZMod.val_injective _ hv.symm

end GlobalTheory.CompanionTheory.PTIso
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivCyclotomicCharacterStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_equiv_cyclotomic_character : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω), cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic | exact GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic | (intros; apply GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSemilatticeSystem
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSemilatticeSystem
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis

theorem exists_finite_sys_of_separated_quasiCompact :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsSeparated s → QuasiCompact s →
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  intro R _ X s hsep hqc
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have hdiag : IsAffineHom (Limits.pullback.diagonal s) := inferInstance
  have hinf : ∀ U V : X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) :=
    fun U V hU hV => isAffineHom_diagonal_iff.mp hdiag ⊤ (isAffineOpen_top _) U (by simp) V
      (by simp) hU hV
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
    (by simpa using isCompact_univ)
  let A : Set X.Opens := infClosure ((fun i : X.affineOpens => i.1) '' S)
  have hA : ∀ U ∈ A, IsAffineOpen U :=
    infClosure_min (t := {U | IsAffineOpen U}) (by rintro _ ⟨i, -, rfl⟩; exact i.2)
      (fun a ha b hb => hinf a b ha hb)
  letI inst : SemilatticeInf A :=
    Subtype.semilatticeInf (fun _ _ ha hb => infClosed_infClosure ha hb)
  haveI hfin : Finite A := ((hS.image _).infClosure).to_subtype
  refine ⟨A, inst, hfin, ⟨⟨fun j => ⟨j.1, hA j.1 j.2⟩, fun a b => rfl, ?_⟩⟩⟩
  apply top_le_iff.mp
  rw [e]
  exact iSup₂_le fun i hi => le_iSup_of_le (⟨i.1, subset_infClosure ⟨i, hi, rfl⟩⟩ : A) le_rfl

end GlobalTheory.CompanionTheory.Axis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSemilatticeSystemStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_semilattice_system : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsSeparated s → QuasiCompact s →
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.exists_finite_sys_of_separated_quasiCompact | exact GlobalTheory.CompanionTheory.Axis.exists_finite_sys_of_separated_quasiCompact | (intros; apply GlobalTheory.CompanionTheory.Axis.exists_finite_sys_of_separated_quasiCompact <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIsDPMorphismOfCompat
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatDP

theorem γB_map {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B']
    [Algebra ℚ B'] (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (g : B →+* B') {y : B}
    (hy : y ∈ Lat.IB f ξ) (hy' : g y ∈ Lat.IB f' ξ') (n : ℕ) :
    g ((Lat.γB f ξ).dpow n y) = (Lat.γB f' ξ').dpow n (g y) := by
  have h1 := (Lat.γB f ξ).factorial_mul_dpow_eq_pow (n := n) hy
  have h2 := (Lat.γB f' ξ').factorial_mul_dpow_eq_pow (n := n) hy'
  have hu : IsUnit (n.factorial : B') := by
    have := (IsUnit.mk0 (n.factorial : ℚ) (by exact_mod_cast n.factorial_ne_zero)).map (algebraMap ℚ B')
    rwa [map_natCast] at this
  apply hu.mul_left_cancel
  rw [h2, ← map_pow, ← h1, map_mul, map_natCast]

theorem isDPMorphism_map {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W']
    [CommRing B'] [Algebra ℚ B'] (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)
    (g : B →+* B') (hmap : ∀ x ∈ Lat.sub f ξ l M, g x ∈ Lat.sub f' ξ' l M) (u : W')
    (hg : g (f ξ) = f' (u * ξ')) (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ))
    (hc' : Lat.DPClosed (Lat.ι f' ξ' l M) (Lat.γB f' ξ')) :
    IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γ f' ξ' l M hc') (Lat.map f ξ f' ξ' l M g hmap) := by
  have hB : ∀ x ∈ Lat.I f ξ l M, g (Lat.ι f ξ l M x) ∈ Lat.IB f' ξ' := by
    intro x hx
    have hx' : Lat.ι f ξ l M x ∈ Lat.IB f ξ := hx
    simp only [Lat.IB, Ideal.mem_span_singleton] at hx' ⊢
    obtain ⟨c, hc0⟩ := hx'
    refine ⟨f' u * g c, ?_⟩
    rw [hc0, map_mul, hg, map_mul]; ring
  have hI : ∀ x ∈ Lat.I f ξ l M, Lat.map f ξ f' ξ' l M g hmap x ∈ Lat.I f' ξ' l M := by
    intro x hx
    show Lat.ι f' ξ' l M (Lat.map f ξ f' ξ' l M g hmap x) ∈ Lat.IB f' ξ'
    rw [Lat.ι_map]; exact hB x hx
  refine ⟨Ideal.map_le_iff_le_comap.2 fun x hx => hI x hx, fun {n} x hx => ?_⟩
  apply Lat.ι_injective f' ξ' l M
  rw [Lat.ι_γ f' ξ' l M hc' (hI x hx)]
  simp only [Lat.ι_map]
  rw [Lat.ι_γ f ξ l M hc hx]
  have hx' : Lat.ι f ξ l M x ∈ Lat.IB f ξ := hx
  exact (γB_map f ξ f' ξ' g hx' (hB x hx) n).symm

end GlobalTheory.CompanionTheory.LatDP
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsInertia
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsInertia
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

noncomputable section

namespace GlobalTheory.CompanionTheory.PTIso.InvTransport

theorem exists_invFam : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), (∀ σ : G F Ω, cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ) → ∀ inv : InvFam F Ω l r, ∃ inv' : InvFam F' Ω' l r, ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → (Function.Bijective (inv A) → Function.Bijective (inv' A')) ∧ (∀ (z : Z2 (muLoc F l r A)) (z' : Z2 (muLoc F' l r A')), (∀ (g h : Dec (F := F) A) (g' h' : Dec (F := F') A'), (g' : G F' Ω') = Φ g → (h' : G F' Ω') = Φ h → z'.1 (g', h') = z.1 (g, h)) → inv' A' (Submodule.Quotient.mk z') = inv A (Submodule.Quotient.mk z)) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ hDec l _ r hcyc inv
  have hcm : ∀ (A' : ValuationSubring Ω') (x : Ω), E x ∈ A' ↔ x ∈ A'.comap E.toRingHom :=
    fun A' x => Iff.rfl
  let eD : ∀ A' : ValuationSubring Ω',
      Dec (F := F) (A'.comap E.toRingHom) ≃ₜ* Dec (F := F') A' :=
    fun A' => subgroupIso Φ _ _ (hDec _ A' (hcm A'))
  have hc : ∀ (A' : ValuationSubring Ω') (h : Dec (F := F) (A'.comap E.toRingHom))
      (m : ZMod (l ^ r)),
      (muLoc F' l r A') (eD A' h) m = (muLoc F l r (A'.comap E.toRingHom)) h m := by
    intro A' h m
    have h1 : cycMod F' Ω' l r (Φ h.1) = cycMod F Ω l r h.1 := hcyc h.1
    show charRep ((cycMod F' Ω' l r).comp (Dec (F := F') A').subtype) (eD A' h) m =
      charRep ((cycMod F Ω l r).comp (Dec (F := F) (A'.comap E.toRingHom)).subtype) h m
    have h2 : ((cycMod F' Ω' l r).comp (Dec (F := F') A').subtype) (eD A' h) =
        ((cycMod F Ω l r).comp (Dec (F := F) (A'.comap E.toRingHom)).subtype) h := h1
    rw [charRep_apply, charRep_apply, h2]
  refine ⟨fun A' => inv (A'.comap E.toRingHom) ∘ₗ
    (ReciprocityTheory.Neutral.Bridge.equivH2OfIso (eD A') (muLoc F' l r A')
      (muLoc F l r (A'.comap E.toRingHom)) (hc A')).toLinearMap, ?_⟩
  intro A A' hA
  obtain rfl : A = A'.comap E.toRingHom := by
    ext x
    exact (hA x).symm.trans (hcm A' x)
  refine ⟨fun hb => hb.comp (LinearEquiv.bijective _), fun z z' hz => ?_⟩
  show inv (A'.comap E.toRingHom) (ReciprocityTheory.Neutral.Bridge.equivH2OfIso (eD A') (muLoc F' l r A')
      (muLoc F l r (A'.comap E.toRingHom)) (hc A') (Submodule.Quotient.mk z')) = _
  rw [ReciprocityTheory.Neutral.Bridge.equivH2OfIso_mk]
  congr 2
  apply Subtype.ext
  funext p
  exact hz p.1 p.2 (eD A' p.1) (eD A' p.2) rfl rfl

end GlobalTheory.CompanionTheory.PTIso.InvTransport
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsInertiaStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_equiv_transports_inertia : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), (∀ σ : G F Ω, cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ) → ∀ inv : InvFam F Ω l r, ∃ inv' : InvFam F' Ω' l r, ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → (Function.Bijective (inv A) → Function.Bijective (inv' A')) ∧ (∀ (z : Z2 (muLoc F l r A)) (z' : Z2 (muLoc F' l r A')), (∀ (g h : Dec (F := F) A) (g' h' : Dec (F := F') A'), (g' : G F' Ω') = Φ g → (h' : G F' Ω') = Φ h → z'.1 (g', h') = z.1 (g, h)) → inv' A' (Submodule.Quotient.mk z') = inv A (Submodule.Quotient.mk z)) := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.InvTransport.exists_invFam | exact GlobalTheory.CompanionTheory.PTIso.InvTransport.exists_invFam | (intros; apply GlobalTheory.CompanionTheory.PTIso.InvTransport.exists_invFam <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InertiaQuotientTransport
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InertiaQuotientTransport
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

theorem map_mem_closedNormal {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] (Φ : A ≃ₜ* B) (X : Set A) (Y : Set B)
    (h : ∀ a ∈ X, Φ a ∈ Y) {a : A} (ha : a ∈ (Subgroup.normalClosure X).topologicalClosure) :
    Φ a ∈ (Subgroup.normalClosure Y).topologicalClosure := by
  let f : A →* B := (Φ : A ≃* B).toMonoidHom
  let K : Subgroup B := (Subgroup.normalClosure Y).topologicalClosure
  haveI : K.Normal := Subgroup.is_normal_topologicalClosure _
  haveI : (K.comap f).Normal := Subgroup.Normal.comap ‹_› f
  have hK : IsClosed (K : Set B) := Subgroup.isClosed_topologicalClosure _
  have hc : IsClosed ((K.comap f : Subgroup A) : Set A) := hK.preimage Φ.continuous
  have hle : Subgroup.normalClosure X ≤ K.comap f := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (h x hx))
  exact Subgroup.topologicalClosure_minimal _ hle hc ha

def quotientIso {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] (Φ : A ≃ₜ* B)
    (H : Subgroup A) (K : Subgroup B) [H.Normal] [K.Normal] (h : ∀ a, a ∈ H ↔ Φ a ∈ K) :
    A ⧸ H ≃ₜ* B ⧸ K where
  toMulEquiv := QuotientGroup.congr H K (Φ : A ≃* B) (by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (h a).1 ha
    · intro hb
      exact ⟨Φ.symm b, (h _).2 (by simpa using hb), Φ.apply_symm_apply b⟩)
  continuous_toFun := by
    exact (QuotientGroup.isQuotientMap_mk H).continuous_iff.2
      (QuotientGroup.continuous_mk.comp Φ.continuous)
  continuous_invFun := by
    exact (QuotientGroup.isQuotientMap_mk K).continuous_iff.2
      (QuotientGroup.continuous_mk.comp Φ.symm.continuous)

theorem exists_gsIso : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') → ∀ (T : Set (HeightOneSpectrum (𝓞 F))) (T' : Set (HeightOneSpectrum (𝓞 F'))), (∀ v, v ∈ T ↔ eV v ∈ T') → ∃ Ψ : GS Ω T ≃ₜ* GS Ω' T', ∀ σ : G F Ω, Ψ (toGS Ω T σ) = toGS Ω' T' (Φ σ) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E _ Φ _ eV hP hI T T' hT
  have hfwd : ∀ σ, σ ∈ NS Ω T → Φ σ ∈ NS Ω' T' := by
    intro σ hσ
    refine map_mem_closedNormal Φ _ _ ?_ hσ
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ ⊢
    obtain ⟨v, hv, A, hA, hτ⟩ := hτ
    let A' : ValuationSubring Ω' := A.comap (E.symm : Ω' →+* Ω)
    have hAA : ∀ x, E x ∈ A' ↔ x ∈ A := by
      intro x
      show E.symm (E x) ∈ A ↔ x ∈ A
      simp
    exact ⟨eV v, fun h => hv ((hT v).2 h), A', (hP A A' hAA v).1 hA, (hI A A' hAA τ).1 hτ⟩
  have hbwd : ∀ σ', σ' ∈ NS Ω' T' → Φ.symm σ' ∈ NS Ω T := by
    intro σ' hσ'
    refine map_mem_closedNormal Φ.symm _ _ ?_ hσ'
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ ⊢
    obtain ⟨v', hv', A', hA', hτ⟩ := hτ
    let A : ValuationSubring Ω := A'.comap (E : Ω →+* Ω')
    have hAA : ∀ x, E x ∈ A' ↔ x ∈ A := fun x => Iff.rfl
    refine ⟨eV.symm v', fun h => hv' ?_, A, ?_, ?_⟩
    · simpa using (hT _).1 h
    · refine (hP A A' hAA _).2 ?_
      simpa using hA'
    · refine (hI A A' hAA _).2 ?_
      simpa using hτ
  have hiff : ∀ σ, σ ∈ NS Ω T ↔ Φ σ ∈ NS Ω' T' := fun σ =>
    ⟨hfwd σ, fun h => by simpa using hbwd _ h⟩
  exact ⟨quotientIso Φ (NS Ω T) (NS Ω' T') hiff, fun σ => rfl⟩

end GlobalTheory.CompanionTheory.PTIso
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InertiaQuotientTransportStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_quotient_equiv_of_matching_places : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') → ∀ (T : Set (HeightOneSpectrum (𝓞 F))) (T' : Set (HeightOneSpectrum (𝓞 F'))), (∀ v, v ∈ T ↔ eV v ∈ T') → ∃ Ψ : GS Ω T ≃ₜ* GS Ω' T', ∀ σ : G F Ω, Ψ (toGS Ω T σ) = toGS Ω' T' (Φ σ) := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.exists_gsIso | exact GlobalTheory.CompanionTheory.PTIso.exists_gsIso | (intros; apply GlobalTheory.CompanionTheory.PTIso.exists_gsIso <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueConstantOfCompatibleFamily
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueConstantOfCompatibleFamily
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Axis

theorem existsUnique_const_of_trivSqZeroExt (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (M : Type) [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (F' : C ⥤ CommAlgCat.{0} (TrivSqZeroExt R M)) (bc : BC F F') :
    Stein F' → ∀ z : ∀ T : C, M ⊗[R] F.obj T,
      (∀ (T T' : C) (φ : T ⟶ T'), z T' = (mp F φ).toLinearMap.lTensor M (z T)) →
      ∃! m : M, ∀ T, z T = m ⊗ₜ[R] (1 : F.obj T) := by
  intro hS z hz
  choose e he using bc.bij
  have hpure : ∀ (T : C) (r : TrivSqZeroExt R M) (b : F.obj T), e T (r ⊗ₜ[R] b) = r • bc.α T b := by
    intro T r b
    have h : (r ⊗ₜ[R] b : TrivSqZeroExt R M ⊗[R] F.obj T) = r • ((1 : TrivSqZeroExt R M) ⊗ₜ[R] b) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [h, map_smul, he]
  have hnat : ∀ {T T' : C} (φ : T ⟶ T') (x : TrivSqZeroExt R M ⊗[R] F.obj T),
      e T' ((mp F φ).toLinearMap.lTensor _ x) = mp F' φ (e T x) := by
    intro T T' φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r b =>
      rw [LinearMap.lTensor_tmul, hpure, hpure, map_smul]
      exact congrArg (r • ·) (bc.naturality φ b)
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
  let jj : ∀ T : C, M ⊗[R] F.obj T →ₗ[R] TrivSqZeroExt R M ⊗[R] F.obj T :=
    fun T ↦ (TrivSqZeroExt.inrHom R M).rTensor _
  have hsnd : ∀ (T : C) (x : M ⊗[R] F.obj T),
      (TrivSqZeroExt.sndHom R M).rTensor _ (jj T x) = x := by
    intro T x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [jj]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hcomm : ∀ {T T' : C} (φ : T ⟶ T') (x : M ⊗[R] F.obj T),
      jj T' ((mp F φ).toLinearMap.lTensor M x) = (mp F φ).toLinearMap.lTensor _ (jj T x) := by
    intro T T' φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [jj]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  have hconst : ∀ (T : C) (r : TrivSqZeroExt R M),
      algebraMap (TrivSqZeroExt R M) (F'.obj T) r = e T (r ⊗ₜ[R] (1 : F.obj T)) := by
    intro T r
    rw [hpure, map_one, Algebra.algebraMap_eq_smul_one]
  let w : C0 F' := fun T ↦ e T (jj T (z T))
  have hw : d0 F' w = 0 := by
    funext T T' φ
    rw [amitsur_d0_apply]
    simp only [w, Pi.zero_apply]
    rw [← hnat, ← hcomm, ← hz, sub_self]
  obtain ⟨r, hr⟩ := (hS.1 w).1 hw
  have hjjr : ∀ T : C, jj T (z T) = r ⊗ₜ[R] (1 : F.obj T) := by
    intro T
    apply (e T).injective
    rw [← hconst]
    exact (congrFun hr T).symm
  refine ⟨r.snd, fun T ↦ ?_, fun m₂ hm₂ ↦ ?_⟩
  · rw [← hsnd T (z T), hjjr T]
    simp
  · have h0 : algebraMap (TrivSqZeroExt R M) (C0 F') (TrivSqZeroExt.inr (m₂ - r.snd)) = 0 := by
      funext T
      have hd : (m₂ - r.snd) ⊗ₜ[R] (1 : F.obj T) = 0 := by
        have h1 : z T = r.snd ⊗ₜ[R] (1 : F.obj T) := by
          rw [← hsnd T (z T), hjjr T]
          simp
        rw [TensorProduct.sub_tmul, ← hm₂ T, ← h1, sub_self]
      have h2 : (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) ⊗ₜ[R] (1 : F.obj T) = 0 := by
        have : jj T ((m₂ - r.snd) ⊗ₜ[R] (1 : F.obj T)) =
            (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) ⊗ₜ[R] (1 : F.obj T) := by
          simp [jj]
        rw [← this, hd, map_zero]
      change algebraMap (TrivSqZeroExt R M) (F'.obj T) _ = 0
      rw [hconst, h2, map_zero]
    have h3 : (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) = 0 :=
      hS.2 (h0.trans (map_zero _).symm)
    have h4 := congrArg TrivSqZeroExt.snd h3
    simpa [sub_eq_zero] using h4

end GlobalTheory.CompanionTheory.Axis
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueConstantOfCompatibleFamilyStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_constant_of_compatible_family : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (M : Type) [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (F' : C ⥤ CommAlgCat.{0} (TrivSqZeroExt R M)) (_ : BC F F'),
    Stein F' → ∀ z : ∀ T : C, M ⊗[R] F.obj T,
      (∀ (T T' : C) (φ : T ⟶ T'), z T' = (mp F φ).toLinearMap.lTensor M (z T)) →
      ∃! m : M, ∀ T, z T = m ⊗ₜ[R] (1 : F.obj T) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.existsUnique_const_of_trivSqZeroExt | exact GlobalTheory.CompanionTheory.Axis.existsUnique_const_of_trivSqZeroExt | (intros; apply GlobalTheory.CompanionTheory.Axis.existsUnique_const_of_trivSqZeroExt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisGroupTransportIsomorphism
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisGroupTransportIsomorphism
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

section GalConj

variable {F Ω F' Ω' : Type} [Field F] [Field Ω] [Algebra F Ω]
  [Field F'] [Field Ω'] [Algebra F' Ω']

def galConjFun (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) (σ : Ω ≃ₐ[F] Ω) :
    Ω' ≃ₐ[F'] Ω' :=
  AlgEquiv.ofRingEquiv (f := E.symm.trans ((σ : Ω ≃+* Ω).trans E)) (fun y => by
    obtain ⟨x, rfl⟩ := e.surjective y
    have h1 : E.symm (algebraMap F' Ω' (e x)) = algebraMap F Ω x := by
      rw [← hE, RingEquiv.symm_apply_apply]
    simp [h1, hE])

theorem galConjFun_apply (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) (σ : Ω ≃ₐ[F] Ω) (x : Ω) :
    galConjFun e E hE σ (E x) = E (σ x) := by
  simp [galConjFun]

def galConjHom (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) :
    (Ω ≃ₐ[F] Ω) →* (Ω' ≃ₐ[F'] Ω') where
  toFun := galConjFun e E hE
  map_one' := by
    ext y
    obtain ⟨x, rfl⟩ := E.surjective y
    rw [galConjFun_apply]; rfl
  map_mul' σ τ := by
    ext y
    obtain ⟨x, rfl⟩ := E.surjective y
    show galConjFun e E hE (σ * τ) (E x) = galConjFun e E hE σ (galConjFun e E hE τ (E x))
    rw [galConjFun_apply e E hE τ, galConjFun_apply e E hE σ, galConjFun_apply e E hE (σ * τ),
      AlgEquiv.mul_apply]

theorem galConjHom_apply (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) (σ : Ω ≃ₐ[F] Ω) (x : Ω) :
    galConjHom e E hE σ (E x) = E (σ x) :=
  galConjFun_apply e E hE σ x

theorem continuous_galConjHom [Algebra.IsAlgebraic F Ω]
    (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) :
    Continuous (galConjHom e E hE) := by
  refine continuous_of_continuousAt_one _ ?_
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨K', hK', hKs⟩ := hs
  let b := Module.finBasis F' K'
  let T : Set Ω := Set.range fun i => E.symm (b i : Ω')
  let L : IntermediateField F Ω := IntermediateField.adjoin F T
  have hL : FiniteDimensional F L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨L, hL, fun σ hσ => hKs ?_⟩
  have hfix : ∀ i, galConjHom e E hE σ (b i : Ω') = (b i : Ω') := by
    intro i
    have hmem : E.symm (b i : Ω') ∈ L :=
      IntermediateField.subset_adjoin F T ⟨i, rfl⟩
    have h1 : σ (E.symm (b i : Ω')) = E.symm (b i : Ω') :=
      (IntermediateField.mem_fixingSubgroup_iff L σ).1 hσ _ hmem
    have h2 := galConjHom_apply e E hE σ (E.symm (b i : Ω'))
    rwa [h1, RingEquiv.apply_symm_apply] at h2
  have hlin : ((galConjHom e E hE σ).toAlgHom.comp K'.val).toLinearMap = K'.val.toLinearMap :=
    b.ext fun i => hfix i
  refine (IntermediateField.mem_fixingSubgroup_iff K' _).2 fun x hx => ?_
  exact congrArg (fun f : K' →ₗ[F'] Ω' => f ⟨x, hx⟩) hlin

end GalConj

theorem exists_galContinuousMulEquiv : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω']
    [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'),
    (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) →
    ∃ Φ : G F Ω ≃ₜ* G F' Ω', ∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic F' Ω' := IsAlgClosure.isAlgebraic
  have hE' : ∀ x : F', E.symm (algebraMap F' Ω' x) = algebraMap F Ω (e.symm x) := by
    intro x
    rw [RingEquiv.symm_apply_eq, hE, RingEquiv.apply_symm_apply]
  refine ⟨{ toFun := galConjHom e E hE
            invFun := galConjHom e.symm E.symm hE'
            left_inv := ?_
            right_inv := ?_
            map_mul' := map_mul _
            continuous_toFun := continuous_galConjHom e E hE
            continuous_invFun := continuous_galConjHom e.symm E.symm hE' },
    fun σ x => galConjHom_apply e E hE σ x⟩
  · intro σ
    ext x
    have h := galConjHom_apply e.symm E.symm hE' (galConjHom e E hE σ) (E x)
    rw [galConjHom_apply e E hE σ x, RingEquiv.symm_apply_apply,
      RingEquiv.symm_apply_apply] at h
    exact h
  · intro τ
    ext y
    have h := galConjHom_apply e E hE (galConjHom e.symm E.symm hE' τ) (E.symm y)
    rw [galConjHom_apply e.symm E.symm hE' τ y, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply] at h
    exact h

end GlobalTheory.CompanionTheory.PTIso
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisGroupTransportIsomorphismStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_group_transport_isomorphism : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∃ Φ : G F Ω ≃ₜ* G F' Ω', ∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x) := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.exists_galContinuousMulEquiv | exact GlobalTheory.CompanionTheory.PTIso.exists_galContinuousMulEquiv | (intros; apply GlobalTheory.CompanionTheory.PTIso.exists_galContinuousMulEquiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateShafarevichTransport
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateShafarevichTransport
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge

namespace GlobalTheory.CompanionTheory.PTIso.ShaTransfer

theorem nonempty_equiv_of_mem_iff {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (e : A ≃ₗ[R] B) (p : Submodule R A) (q : Submodule R B)
    (h : ∀ x, x ∈ p ↔ e x ∈ q) : Nonempty (p ≃ₗ[R] q) := by
  refine ⟨LinearEquiv.ofSubmodules e p q ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx
  · intro hy
    exact ⟨e.symm y, (h _).2 (by simpa using hy), by simp⟩

theorem dualData_transfer {R A B A' B' : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    (eA : A' ≃ₗ[R] A) (eB : B' ≃ₗ[R] B)
    (h : Finite A' ∧ Finite B' ∧ Nonempty (B' ≃ₗ[R] Module.Dual R A') ∧
      Nat.card A' = Nat.card B') :
    Finite A ∧ Finite B ∧ Nonempty (B ≃ₗ[R] Module.Dual R A) ∧ Nat.card A = Nat.card B := by
  obtain ⟨hA, hB, ⟨f⟩, hc⟩ := h
  refine ⟨Finite.of_equiv _ eA.toEquiv, Finite.of_equiv _ eB.toEquiv,
    ⟨(eB.symm.trans f).trans eA.symm.dualMap⟩, ?_⟩
  rw [← Nat.card_congr eA.toEquiv, ← Nat.card_congr eB.toEquiv, hc]

section Rep

variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
  {I I' : Type} {D : I → Type} {D' : I' → Type}
  [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)]
  (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i))
  (φ' : ∀ i, D' i →* Γ') (hφ' : ∀ i, Continuous (φ' i))
  {N : Type} [AddCommGroup N] [Module R N] [TopologicalSpace N] [DiscreteTopology N]
  (σ : Representation R Γ N) (σ' : Representation R Γ' N)
  (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i))

theorem local_compat (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (i : I) :
    ∀ d m, (σ'.comp (φ' (eI i))) (eD i d) m = (σ.comp (φ i)) d m := by
  intro d m
  show σ' (φ' (eI i) (eD i d)) m = σ (φ i d) m
  rw [hD, hσ]

theorem res_h1_iso_h1 (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (i : I) (x : H1 σ') :
    resH1 σ (φ i) (hφ i) (equivH1OfIso eG σ' σ hσ x) =
      equivH1OfIso (eD i) (σ'.comp (φ' (eI i))) (σ.comp (φ i)) (local_compat φ φ' σ σ' eG eI eD hD hσ i)
        (resH1 σ' (φ' (eI i)) (hφ' (eI i)) x) := by
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    funext d
    show f.1 (eG (φ i d)) = f.1 (φ' (eI i) (eD i d))
    rw [hD]

theorem res_h2_iso_h2 (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (i : I) (x : H2 σ') :
    resH2 σ (φ i) (hφ i) (equivH2OfIso eG σ' σ hσ x) =
      equivH2OfIso (eD i) (σ'.comp (φ' (eI i))) (σ.comp (φ i)) (local_compat φ φ' σ σ' eG eI eD hD hσ i)
        (resH2 σ' (φ' (eI i)) (hφ' (eI i)) x) := by
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    funext d
    show f.1 (eG (φ i d.1), eG (φ i d.2)) = f.1 (φ' (eI i) (eD i d.1), φ' (eI i) (eD i d.2))
    rw [hD, hD]

theorem mem_Sha1_iff_equiv_mem (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (x : H1 σ') :
    x ∈ Sha1 σ' φ' hφ' ↔ equivH1OfIso eG σ' σ hσ x ∈ Sha1 σ φ hφ := by
  simp only [Sha1, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h i
    rw [res_h1_iso_h1 φ hφ φ' hφ' σ σ' eG eI eD hD hσ, h, map_zero]
  · intro h i'
    obtain ⟨i, rfl⟩ := eI.surjective i'
    have hi := h i
    rw [res_h1_iso_h1 φ hφ φ' hφ' σ σ' eG eI eD hD hσ] at hi
    exact (LinearEquiv.map_eq_zero_iff _).1 hi

theorem mem_Sha2_iff_equiv_mem (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (x : H2 σ') :
    x ∈ Sha2 σ' φ' hφ' ↔ equivH2OfIso eG σ' σ hσ x ∈ Sha2 σ φ hφ := by
  simp only [Sha2, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h i
    rw [res_h2_iso_h2 φ hφ φ' hφ' σ σ' eG eI eD hD hσ, h, map_zero]
  · intro h i'
    obtain ⟨i, rfl⟩ := eI.surjective i'
    have hi := h i
    rw [res_h2_iso_h2 φ hφ φ' hφ' σ σ' eG eI eD hD hσ] at hi
    exact (LinearEquiv.map_eq_zero_iff _).1 hi

theorem nonempty_sha1_equiv (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) :
    Nonempty (Sha1 σ' φ' hφ' ≃ₗ[R] Sha1 σ φ hφ) :=
  nonempty_equiv_of_mem_iff (equivH1OfIso eG σ' σ hσ) _ _
    (mem_Sha1_iff_equiv_mem φ hφ φ' hφ' σ σ' eG eI eD hD hσ)

theorem nonempty_sha2_equiv (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) :
    Nonempty (Sha2 σ' φ' hφ' ≃ₗ[R] Sha2 σ φ hφ) :=
  nonempty_equiv_of_mem_iff (equivH2OfIso eG σ' σ hσ) _ _
    (mem_Sha2_iff_equiv_mem φ hφ φ' hφ' σ σ' eG eI eD hD hσ)

end Rep

theorem twDual_compat_of_iso {R Γ Γ' M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [Group Γ'] [TopologicalSpace Γ'] [AddCommGroup M] [Module R M]
    (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ) (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
    (eG : Γ ≃ₜ* Γ') (hχ : ∀ g, χ' (eG g) = χ g) (hρ : ∀ g m, ρ' (eG g) m = ρ g m) :
    ∀ g ψ, twDual χ' ρ' (eG g) ψ = twDual χ ρ g ψ := by
  intro g ψ
  refine DFunLike.ext _ _ fun m => ?_
  rw [twDual_apply, twDual_apply, hχ, ← map_inv, hρ]

theorem shaG_transfer {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
    {I I' : Type} [Fintype I] [Fintype I'] {D : I → Type} {D' : I' → Type}
    [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
    [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)]
    (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i))
    (φ' : ∀ i, D' i →* Γ') (hφ' : ∀ i, Continuous (φ' i))
    (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ)
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
    (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i))
    (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hχ : ∀ g, χ' (eG g) = χ g) (hρ : ∀ g m, ρ' (eG g) m = ρ g m)
    (h : ShaG φ' hφ' χ' ρ') : ShaG φ hφ χ ρ := by
  have hT := twDual_compat_of_iso χ χ' ρ ρ' eG hχ hρ
  obtain ⟨a1⟩ := nonempty_sha1_equiv φ hφ φ' hφ' ρ ρ' eG eI eD hD hρ
  obtain ⟨a2⟩ := nonempty_sha2_equiv φ hφ φ' hφ' ρ ρ' eG eI eD hD hρ
  obtain ⟨b1⟩ := nonempty_sha1_equiv φ hφ φ' hφ' (twDual χ ρ) (twDual χ' ρ') eG eI eD hD hT
  obtain ⟨b2⟩ := nonempty_sha2_equiv φ hφ φ' hφ' (twDual χ ρ) (twDual χ' ρ') eG eI eD hD hT
  exact ⟨dualData_transfer b1 a2 h.1, dualData_transfer a1 b2 h.2⟩

end GlobalTheory.CompanionTheory.PTIso.ShaTransfer
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateShafarevichTransportStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_shafarevich_transport : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] {I I' : Type} [Fintype I] [Fintype I'] {D : I → Type} {D' : I' → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)] [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)] (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (φ' : ∀ i, D' i →* Γ') (hφ' : ∀ i, Continuous (φ' i)) (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ) {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (ρ' : Representation R Γ' M) (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i)), (∀ i d, φ' (eI i) (eD i d) = eG (φ i d)) → (∀ g, χ' (eG g) = χ g) → (∀ g m, ρ' (eG g) m = ρ g m) → ShaG φ' hφ' χ' ρ' → ShaG φ hφ χ ρ := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.ShaTransfer.shaG_transfer | exact GlobalTheory.CompanionTheory.PTIso.ShaTransfer.shaG_transfer | (intros; apply GlobalTheory.CompanionTheory.PTIso.ShaTransfer.shaG_transfer <;> assumption)
end
end
