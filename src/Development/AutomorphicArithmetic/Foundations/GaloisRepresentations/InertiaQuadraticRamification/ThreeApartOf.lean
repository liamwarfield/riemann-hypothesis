module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChangeLifts.SplitLift
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.ExistsCompletionEquivOfHe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

def QuadDisj : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (T : Set (HeightOneSpectrum (𝓞 F)))
    (N : Subgroup (G F Ω)), (∀ u ∉ T, ∀ A : ValuationSubring Ω, IsPlaceOver A u → Ine (F := F) A ≤ N) →
    ∀ Q : QCM F Ω, RamOff T Q → GlobalTheory.AboveL.SolvDisj ↥Q.K N

def AllUnr : Prop :=
  ∀ (Y Ω : Type) [Field Y] [NumberField Y] [Field Ω] [Algebra Y Ω] [IsAlgClosure Y Ω] (T : Set (HeightOneSpectrum (𝓞 Y)))
    (Q : QCM Y Ω), Step1 T Q → ∀ w : HeightOneSpectrum (𝓞 ↥Q.K),
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield ↥Q.K)) w.asIdeal

def Double : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (T : Set (HeightOneSpectrum (𝓞 E))) (Q : QCM E Ω), Step0 T Q → ∀ t ∈ T,
    ∃ w₁ w₂ : HeightOneSpectrum (𝓞 ↥Q.K), w₁.under (𝓞 E) = t ∧ w₂.under (𝓞 E) = t ∧ GlobalTheory.Cong.Apart w₁ w₂

def ApartUp : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M],
    (∀ w₁ w₂ : HeightOneSpectrum (𝓞 M), GlobalTheory.Cong.Apart (w₁.under (𝓞 K)) (w₂.under (𝓞 K)) → GlobalTheory.Cong.Apart w₁ w₂) ∧
    ∀ v : HeightOneSpectrum (𝓞 K), ∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v

def ThreeApart : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (T₁ : Set (HeightOneSpectrum (𝓞 E))) (Q₁ : QCM E Ω), Step0 T₁ Q₁ →
    ∀ (T₂ : Set (HeightOneSpectrum (𝓞 ↥Q₁.K))) (Q₂ : QCM ↥Q₁.K Ω), Step0 T₂ Q₂ → ∀ t ∈ T₁,
    (∀ w : HeightOneSpectrum (𝓞 ↥Q₁.K), w.under (𝓞 E) = t → w ∈ T₂) →
    ∀ (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra ↥Q₂.K M],
    ∃ w : Fin 3 → HeightOneSpectrum (𝓞 M), (∀ i, (((w i).under (𝓞 ↥Q₂.K)).under (𝓞 ↥Q₁.K)).under (𝓞 E) = t) ∧
      ∀ i j, i ≠ j → GlobalTheory.Cong.Apart (w i) (w j)

def SatSplit : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra K M]
    [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)), IsPlaceOver A v → IsPlaceOver A w →
    (∀ g ∈ Dec (F := K) A, Fixes M g) → ∀ (a : ℕ) (π : CuspSub K a) (P : CuspSub M a),
    UpperTheory.CBC.SplitLift (UpperTheory.CBC.Cusp.cx π) (UpperTheory.CBC.Cusp.cx P) → ∀ B, (CG.mk π).HasSat v B → (CG.mk P).HasSat w B

theorem threeApart_of (h1 : Double) (h2 : ApartUp) : ThreeApart := by
  intro E Ω _ _ _ _ _ _ T₁ Q₁ s₁ T₂ Q₂ s₂ t ht hT M _ _ _ _
  obtain ⟨a, b, ha, hb, hab⟩ := h1 E Ω T₁ Q₁ s₁ t ht
  obtain ⟨x, y, hx, hy, hxy⟩ := h1 ↥Q₁.K Ω T₂ Q₂ s₂ a (hT a ha)
  obtain ⟨z, hz⟩ := (h2 ↥Q₁.K ↥Q₂.K).2 b
  have hxz : GlobalTheory.Cong.Apart x z := (h2 ↥Q₁.K ↥Q₂.K).1 x z (by rw [hx, hz]; exact hab)
  have hyz : GlobalTheory.Cong.Apart y z := (h2 ↥Q₁.K ↥Q₂.K).1 y z (by rw [hy, hz]; exact hab)
  choose up hup using (h2 ↥Q₂.K M).2
  refine ⟨fun i => up (![x, y, z] i), fun i => ?_, fun i j hij => (h2 ↥Q₂.K M).1 _ _ ?_⟩
  · rw [hup]
    fin_cases i
    · simpa [hx] using ha
    · simpa [hy] using ha
    · simpa [hz] using hb
  · rw [hup, hup]
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | exact hxy | exact hxz | exact hyz | exact hxy.symm | exact hxz.symm | exact hyz.symm

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.QuadraticCharTwistOfExistsOfInfinity
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem isOpen_fixGrp (F Ω K : Type) [Field F] [Field Ω] [Field K] [Algebra F Ω] [Algebra K Ω] [Algebra F K]
    [IsScalarTower F K Ω] [FiniteDimensional F K] : IsOpen (fixGrp F Ω K : Set (G F Ω)) := by
  let φ := IsScalarTower.toAlgHom F K Ω
  haveI : FiniteDimensional F φ.fieldRange := LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ).toLinearEquiv
  refine Subgroup.isOpen_mono (fun g hg x => ?_) φ.fieldRange.fixingSubgroup_isOpen
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ ⟨x, rfl⟩

section

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem isAlgClosure_plus : IsAlgClosure (maximalRealSubfield E) Ω :=
  ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩

theorem cuts_base : Cuts (Fld.base E Ω) ⊤ := fun g => ⟨fun _ => trivial, fun _ x => g.commutes x⟩

end

theorem noSelfTwist_of (h : NormRam) : NoSelfTwist :=
  fun K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hp A v hA hτ a ha π B hB η hη =>
    GlobalTheory.TwistRamified.twist_ne K a ha π η v B hB (h K M Ω hp η hη A v hA hτ)

theorem quadraticCharTwist_of_exists_of_infinity (h1 : Quad0Ex) (h2 : InfOf) : Quad0 := by
  intro E Ω _ _ _ _ _ _ T hT
  refine h2 E Ω _ fun S hS => ?_
  obtain ⟨Q, ⟨δ, hδ, h3⟩, h4, u, hu, h5⟩ := h1 E Ω (T ∪ S) (hT.union hS)
  exact ⟨Q, ⟨⟨δ, hδ, fun t ht => h3 t (Or.inl ht)⟩, fun t ht => h4 t (Or.inl ht), u, fun h => hu (Or.inl h), h5⟩,
    u, fun h => hu (Or.inr h), h5⟩

theorem splitIso_holds : SplitIso := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ A v w hv hw h
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) M⟩
  obtain ⟨i, h1, -, h2, h3⟩ := PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions.RamifiedPlaceLift.exists_completionEquiv_of_he hv hw (fun σ => h _ (GlobalTheory.WeilDeligne.Weil_le_Dec hv σ.2))
    (GlobalTheory.InertFixVal.ramificationIdx_eq_one A v w hv hw fun σ hσ => h σ (Ine_le_Dec A hσ)).2
  exact ⟨i, h1, h2, h3⟩

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrCharAtOf
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

def RamSplit (E : Type) {Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (H : Subgroup (G (maximalRealSubfield E) Ω)) : Prop :=
  ∀ (t : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (A : ValuationSubring Ω), IsPlaceOver A t →
    Ine (F := maximalRealSubfield E) A ≤ H ∨ ∀ g ∈ Dec (F := maximalRealSubfield E) A, Fixes E g

def MoveRoot : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (U : Subgroup (G ℚ Ω)), IsOpen (U : Set (G ℚ Ω)) →
    ∀ ℓ : ℕ, ℓ.Prime → ∃ (b : ℕ) (σ : G ℚ Ω), σ ∈ U ∧ ∀ ζ : Ω, IsPrimitiveRoot ζ (ℓ ^ b) → σ ζ ≠ ζ

def NormVal : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (U : Subgroup (G ℚ Ω)), IsOpen (U : Set (G ℚ Ω)) →
    ∀ q : ℕ, 1 < q → ∃ D : ℕ, 0 < D ∧ ∀ (z : Ω) (n c : ℕ), (∀ τ ∈ U, τ z = z) → z ^ n * (q : Ω) ^ c = 1 → n ∣ c * D

def KumMove : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (U : Subgroup (G ℚ Ω)), IsOpen (U : Set (G ℚ Ω)) →
    ∀ ℓ q : ℕ, ℓ.Prime → 1 < q → ∃ j : ℕ, ∀ k, j ≤ k → ∀ ζ y : Ω, IsPrimitiveRoot ζ (ℓ ^ k) → y ^ ℓ ^ j = (q : Ω) →
      ∃ σ ∈ U, σ ζ = ζ ∧ σ y ≠ y

def OrdPrime : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ℓ k q B : ℕ), ℓ.Prime → 1 < q →
    ∃ p : ℕ, p.Prime ∧ B < p ∧ ℓ ^ k ∣ orderOf (q : ZMod p) ∧ ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 →
      ∀ h : Ω ≃+* Ω, (∀ z, h z ∈ A ↔ z ∈ A) → ∀ y : E, h (algebraMap E Ω y) = algebraMap E Ω y

def CharOrd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ℓ k : ℕ) (a : (ZMod p)ˣ), ℓ.Prime → ℓ ^ (k + 1) ∣ orderOf a →
    ∃ lam : (ZMod p)ˣ →* ℂˣ, lam (-1) = 1 ∧ orderOf (lam a) = ℓ ^ k

def UnrCharAt (f : ℕ) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
    ∃ r : G (maximalRealSubfield E) Ω →* ℂˣ, Good r.ker ∧ RamSplit E r.ker ∧
      ∀ A : ValuationSubring Ω, IsPlaceOver A v → Ine (F := maximalRealSubfield E) A ≤ r.ker ∧
        ∀ φ : G (maximalRealSubfield E) Ω, IsFrob A (normV v) φ → orderOf (r φ) = f

def UnrCharPP : Prop := ∀ ℓ k : ℕ, ℓ.Prime → UnrCharAt (ℓ ^ k)

def FreshSplit : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (U : Subgroup (G (maximalRealSubfield E) Ω)),
    IsOpen (U : Set (G (maximalRealSubfield E) Ω)) →
    ∀ T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), T.Finite → ∀ n : ℕ, 0 < n →
    ∃ ψ : G (maximalRealSubfield E) Ω →* ℂˣ, Good ψ.ker ∧ RamSplit E ψ.ker ∧ ψ ^ n = 1 ∧
      (∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := maximalRealSubfield E) A, ψ g = 1) ∧
      ∃ u ∉ T, ∀ A : ValuationSubring Ω, IsPlaceOver A u → Dec (F := maximalRealSubfield E) A ≤ U ∧
        ∃ τ ∈ Ine (F := maximalRealSubfield E) A, orderOf (ψ τ) = n

theorem RamSplit.inf {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {H H' : Subgroup (G (maximalRealSubfield E) Ω)} (h : RamSplit E H) (h' : RamSplit E H') : RamSplit E (H ⊓ H') := by
  intro t A hA
  rcases h t A hA with h1 | h1
  · rcases h' t A hA with h2 | h2
    · exact Or.inl (le_inf h1 h2)
    · exact Or.inr h2
  · exact Or.inr h1

theorem RamSplit.mono {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {H H' : Subgroup (G (maximalRealSubfield E) Ω)} (hle : H ≤ H') (h : RamSplit E H) : RamSplit E H' := by
  intro t A hA
  rcases h t A hA with h1 | h1
  · exact Or.inl (h1.trans hle)
  · exact Or.inr h1

theorem unrCharAt_of (h : UnrCharPP) (f : ℕ) (hf : 0 < f) : UnrCharAt f := by
  induction f using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp _ => exact h p n hp
  | zero => exact absurd hf (lt_irrefl 0)
  | one => simpa using h 2 0 Nat.prime_two
  | coprime a b ha hb hab iha ihb =>
    intro E Ω _ _ _ _ _ _ v
    obtain ⟨r, h1, h2, h3⟩ := iha (by omega) E Ω v
    obtain ⟨s, k1, k2, k3⟩ := ihb (by omega) E Ω v
    have hle : r.ker ⊓ s.ker ≤ (r * s).ker := fun g hg => by
      rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.mem_ker.1 hg.1, MonoidHom.mem_ker.1 hg.2, one_mul]
    refine ⟨r * s, (h1.inf k1).mono hle, (h2.inf k2).mono hle, fun A hA =>
      ⟨(le_inf (h3 A hA).1 (k3 A hA).1).trans hle, fun φ hφ => ?_⟩⟩
    have e1 := (h3 A hA).2 φ hφ
    have e2 := (k3 A hA).2 φ hφ
    rw [MonoidHom.mul_apply, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime (by rwa [e1, e2]), e1, e2]

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NormRam
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published UpperTheory.V.Af.Bc
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.normRam :
    NormRam := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ hp η hη A v hA hτ hunr
  obtain ⟨τ, hτI, hτM⟩ := hτ
  obtain ⟨hη1, hηp, hηev⟩ := hη
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨art, hart⟩ := GlobalTheory.globalArtinReciprocity_holds K Ω
  have halg : IsAlgPos η 0 := isAlgPos_zero_of_orderDvd hp.pos hηp
  obtain ⟨r, hrc, hr⟩ := hart.exists_isLAdicOf (ι : Qbar 2 ≃+* ℂ) halg
  have hrI : ∀ s ∈ Ine A, r s = 1 := (hr.unr_iff hart (Or.inr rfl) hA).2 hunr
  have hres : ∀ g : G M Ω, r (UpperTheory.V.Af.Bc.res K Ω M g) = 1 := by
    haveI : IsAlgClosure M Ω := by
      haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
      exact ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) M⟩
    obtain ⟨artM, hartM⟩ := GlobalTheory.globalArtinReciprocity_holds M Ω
    have hφc : Continuous (r.comp (UpperTheory.V.Af.Bc.res K Ω M)) :=
      hrc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom K M Ω)
    have hbad : {w : HeightOneSpectrum (𝓞 M) | ¬ (η.UnrAt (HeightOneSpectrum.under (𝓞 K) w) ∧
        ∀ f : ℕ, normV w = normV (HeightOneSpectrum.under (𝓞 K) w) ^ f →
          η.val (HeightOneSpectrum.under (𝓞 K) w) ^ f = 1)}.Finite := by
      have h1 := GlobalTheory.QuadNormChar.tendsto_under (K := K) (K' := M)
      have h2 : ∀ᶠ w in Filter.cofinite, η.UnrAt (HeightOneSpectrum.under (𝓞 K) w) :=
        h1.eventually (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified η))
      exact Filter.eventually_cofinite.1 (h2.and hηev)
    have hone := GlobalTheory.FrobDense.eq_one_of_frob M Ω artM hartM (Qbar 2)ˣ (r.comp (UpperTheory.V.Af.Bc.res K Ω M)) hφc
      hbad.toFinset ?_
    · intro g
      exact DFunLike.congr_fun hone g
    · intro w hw A' hA' σ hσ
      rw [Set.Finite.mem_toFinset] at hw
      simp only [Set.mem_setOf_eq, not_not] at hw
      obtain ⟨hwu, hwn⟩ := hw
      have hce : CharEig ι r (HeightOneSpectrum.under (𝓞 K) w)
          (η.val (HeightOneSpectrum.under (𝓞 K) w)) := by
        intro B hB
        refine ⟨(hr.unr_iff hart (Or.inr rfl) hB).2 hwu, fun σ' hσ' => ?_⟩
        have h3 := hr.frob_unr hart (Or.inr rfl) hwu hB hσ'
        rw [map_inv, Units.val_inv_eq_inv_val, h3, inv_inv]
        simp
      obtain ⟨-, hfr⟩ := UpperTheory.frobenius_power_compatibility K M Ω 2 ι w (w.asIdeal.inertiaDeg (𝓞 K))
        (GlobalTheory.QuadNormChar.normV_under w)
      obtain ⟨-, hval⟩ := hfr r _ hce A' hA'
      have h6 := hval σ hσ
      have h7 : ((η.val (HeightOneSpectrum.under (𝓞 K) w) : ℂˣ) : ℂ) ^
          (w.asIdeal.inertiaDeg (𝓞 K)) = 1 := by
        rw [← Units.val_pow_eq_pow_val, hwn _ (GlobalTheory.QuadNormChar.normV_under w)]
        rfl
      rw [h7] at h6
      have h8 : (((r.comp (UpperTheory.V.Af.Bc.res K Ω M)) σ⁻¹ : (Qbar 2)ˣ) : Qbar 2) = 1 := by
        have h9 := congrArg ι.symm h6
        simpa using h9
      have h10 : (r.comp (UpperTheory.V.Af.Bc.res K Ω M)) σ⁻¹ = 1 := Units.ext h8
      rw [map_inv, inv_eq_one] at h10
      exact h10
  have hr1 : ∀ g : G K Ω, r g = 1 := by
    haveI : Fact (Nat.Prime (Module.finrank K M)) := ⟨hp⟩
    let ρ : G K Ω →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
    have hfix : ∀ g : G K Ω, ρ g = 1 → r g = 1 := by
      intro g hg
      let g' : Ω ≃ₐ[M] Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun x => by
        have h1 := AlgEquiv.restrictNormal_commutes g M x
        have h2 : g.restrictNormal M = 1 := hg
        rw [h2] at h1
        simpa using h1.symm)
      have hg' : UpperTheory.V.Af.Bc.res K Ω M g' = g := by
        ext x
        rfl
      rw [← hg']
      exact hres g'
    have hρτ : ρ τ ≠ 1 := by
      intro h1
      apply hτM
      intro x
      have h3 := AlgEquiv.restrictNormal_commutes τ M x
      have h2 : τ.restrictNormal M = 1 := h1
      rw [h2] at h3
      simpa using h3.symm
    have hgen : Subgroup.zpowers (ρ τ) = ⊤ :=
      zpowers_eq_top_of_prime_card (p := Module.finrank K M)
        (IsGalois.card_aut_eq_finrank K M) hρτ
    intro g
    have hg : ρ g ∈ Subgroup.zpowers (ρ τ) := hgen ▸ Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hτ1 : r τ = 1 := hrI τ hτI
    have h4 : ρ ((τ ^ k)⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, map_zpow, hk, inv_mul_cancel]
    have h5 := hfix _ h4
    rw [map_mul, map_inv, map_zpow, hτ1, one_zpow, inv_one, one_mul] at h5
    exact h5
  apply hη1
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  obtain ⟨σ, hσ⟩ := toAb_surjective (E := K) (Ω := Ω) (art x)
  have h := hr x σ hσ.symm
  rw [infPow_zero, lPow_zero, hr1 σ] at h
  simp only [Units.val_one, inv_one, mul_one] at h
  have h2 : ((η.1 x : ℂˣ) : ℂ) = 1 := by
    have h3 := congrArg ι h
    simpa using h3.symm
  ext
  simpa using h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ValuationLeOneOfInteger
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem isFrob_pow' {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {q : ℕ} {φ : G F Ω} (h : IsFrob A q φ) (n : ℕ) :
    IsFrob A (q ^ n) (φ ^ n) := by
  induction n with
  | zero =>
    refine ⟨one_mem _, ?_⟩
    intro x _
    simp
  | succ n ih =>
    refine ⟨pow_mem h.1 _, ?_⟩
    intro x hx
    have hy : A.valuation (φ x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
      exact (apply_mem_iff_of_mem_Dec h.1 x).2 hx
    have h1 := ih.2 (φ x) hy
    have h2 := h.2 x hx
    have hz : A.valuation (x ^ q) ≤ 1 := by
      rw [map_pow]; exact pow_le_one' hx q
    have hc1 : A.valuation (∑ i ∈ Finset.range (q ^ n), (φ x) ^ i * (x ^ q) ^ (q ^ n - 1 - i)) ≤ 1 := by
      refine Valuation.map_sum_le _ (fun i _ => ?_)
      rw [map_mul, map_pow, map_pow]
      exact mul_le_one' (pow_le_one' hy _) (pow_le_one' hz _)
    have h3 : A.valuation ((φ x) ^ (q ^ n) - (x ^ q) ^ (q ^ n)) < 1 := by
      rw [← geom_sum₂_mul (φ x) (x ^ q) (q ^ n), map_mul]
      exact (mul_le_of_le_one_left' hc1).trans_lt h2
    have e : (φ ^ (n + 1)) x - x ^ (q ^ (n + 1))
        = ((φ ^ n) (φ x) - (φ x) ^ (q ^ n)) + ((φ x) ^ (q ^ n) - (x ^ q) ^ (q ^ n)) := by
      rw [pow_succ, AlgEquiv.mul_apply, pow_succ', pow_mul]
      ring
    rw [e]
    exact Valuation.map_add_lt _ h1 h3

private theorem one_lt_normV_inertia_quadratic_ramification {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    1 < normV w := by
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  letI : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  show 1 < Nat.card (𝓞 E ⧸ w.asIdeal)
  exact Finite.one_lt_card

theorem degOf : DegOf := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ A v w hv hw hI φ d hd hφ hfix
  obtain ⟨f, hf⟩ := GlobalTheory.WeilRestrict.normV_eq_pow_of_isPlaceOver (K := K) (L := M) hv hw
  have hq : 1 < normV v := one_lt_normV_inertia_quadratic_ramification v
  have hw1 : 1 < normV w := one_lt_normV_inertia_quadratic_ramification w
  have hdf : d ∣ f := by
    haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.tower_top (K := K) (A := Ω) M
    haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed K, inferInstance⟩
    obtain ⟨σ, hσ⟩ := exists_isFrob (F := M) hw
    have hφf := isFrob_pow' hφ f
    rw [← hf] at hφf
    set ρ := GlobalTheory.WeilRestrict.resG K σ with hρ
    have hρD : ρ ∈ Dec A := GlobalTheory.WeilRestrict.resG_mem_Dec hσ.1
    have hτI : ρ * (φ ^ f)⁻¹ ∈ Ine A := by
      show ρ * (φ ^ f)⁻¹ ∈ ValuationSubring.decompositionSubgroup K A ∧
        ∀ x : Ω, A.valuation x ≤ 1 → A.valuation ((ρ * (φ ^ f)⁻¹) x - x) < 1
      refine ⟨mul_mem hρD (inv_mem hφf.1), ?_⟩
      intro x hx
      obtain ⟨y, rfl⟩ : ∃ y, x = (φ ^ f) y := ⟨(φ ^ f).symm x, ((φ ^ f).apply_symm_apply x).symm⟩
      have hyA : A.valuation y ≤ 1 := by
        rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
        exact (apply_mem_iff_of_mem_Dec hφf.1 y).1 hx
      have h1 := hσ.2 y hyA
      have h2 := hφf.2 y hyA
      have e : (ρ * (φ ^ f)⁻¹) ((φ ^ f) y) - (φ ^ f) y
          = (σ y - y ^ normV w) - ((φ ^ f) y - y ^ normV w) := by
        rw [AlgEquiv.mul_apply]
        rw [show (φ ^ f)⁻¹ ((φ ^ f) y) = y from (φ ^ f).symm_apply_apply y]
        rw [hρ, GlobalTheory.WeilRestrict.resG_apply]
        ring
      rw [e]
      exact Valuation.map_sub_lt _ h1 h2
    have hfixτ := hI _ hτI
    rw [← hfix f]
    intro x
    have h1 : (ρ * (φ ^ f)⁻¹) (algebraMap M Ω x) = algebraMap M Ω x := hfixτ x
    have h2 : ρ (algebraMap M Ω x) = algebraMap M Ω x := by
      rw [hρ, GlobalTheory.WeilRestrict.resG_apply]
      exact σ.commutes x
    rw [AlgEquiv.mul_apply] at h1
    have h3 : (φ ^ f)⁻¹ (algebraMap M Ω x) = algebraMap M Ω x := ρ.injective (h1.trans h2.symm)
    calc (φ ^ f) (algebraMap M Ω x) = (φ ^ f) ((φ ^ f)⁻¹ (algebraMap M Ω x)) := by rw [h3]
      _ = algebraMap M Ω x := (φ ^ f).apply_symm_apply _
  have hfd : f ≤ d := by
    have key : ∀ x : 𝓞 M, x ^ (normV v ^ d) - x ∈ w.asIdeal := by
      intro x
      rw [← hw]
      have hint : A.valuation (algebraMap M Ω (x : M)) ≤ 1 :=
        GlobalTheory.InertiaAlmostAll.val_le_one_of_isIntegral A (x.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ M Ω))
      have hφd := (isFrob_pow' hφ d).2 _ hint
      rw [(hfix d).2 dvd_rfl x] at hφd
      have e : algebraMap M Ω (((x ^ (normV v ^ d) - x : 𝓞 M)) : M)
          = -(algebraMap M Ω (x : M) - (algebraMap M Ω (x : M)) ^ (normV v ^ d)) := by
        rw [show (((x ^ (normV v ^ d) - x : 𝓞 M)) : M) = (x : M) ^ (normV v ^ d) - (x : M) by push_cast; ring,
          map_sub, map_pow]
        ring
      rw [e, Valuation.map_neg]
      exact hφd
    haveI : w.asIdeal.IsMaximal := w.isMaximal
    letI : Field (𝓞 M ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
    have hR : Nat.card (𝓞 M ⧸ w.asIdeal) = normV v ^ f := hf
    haveI : Finite (𝓞 M ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by
      show normV w ≠ 0
      omega)
    letI := Fintype.ofFinite (𝓞 M ⧸ w.asIdeal)
    have hN : 1 < normV v ^ d := Nat.one_lt_pow (Nat.pos_iff_ne_zero.1 hd) hq
    have hp0 : (Polynomial.X ^ (normV v ^ d) - Polynomial.X : Polynomial (𝓞 M ⧸ w.asIdeal)) ≠ 0 :=
      Polynomial.X_pow_sub_X_ne_zero hN
    have hsub : (Finset.univ : Finset (𝓞 M ⧸ w.asIdeal)).val ⊆
        (Polynomial.X ^ (normV v ^ d) - Polynomial.X : Polynomial (𝓞 M ⧸ w.asIdeal)).roots := by
      intro a _
      rw [Polynomial.mem_roots hp0, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X]
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact key x
    have h := Polynomial.card_le_degree_of_subset_roots hsub
    rw [Polynomial.natDegree_X_pow_sub_X hN, Finset.card_univ, ← Nat.card_eq_fintype_card, hR] at h
    exact (Nat.pow_le_pow_iff_right hq).1 h
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at hf; omega
    · exact h
  rw [hf, le_antisymm hfd (Nat.le_of_dvd hf0 hdf)]

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.RealSpan
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.realSpan :
    RealSpan := by
  intro E M Ω F _ _ _ _ _ _ _ _ _ _ _ _ _ g hE hR
  have hnot : ∃ e : E, algebraMap E M e ∉ maximalRealSubfield M := by
    by_contra h
    push_neg at h
    obtain ⟨φ⟩ : Nonempty (M →+* ℂ) := inferInstance
    apply IsTotallyComplex.complexEmbedding_not_isReal (φ.comp (algebraMap E M))
    show ComplexEmbedding.conjugate _ = _
    ext x
    have := (mem_maximalRealSubfield_iff _).1 (h x) φ
    simpa [ComplexEmbedding.conjugate_coe_eq] using this
  obtain ⟨e, he⟩ := hnot
  set α := algebraMap E M e with hα
  have h2 : Module.finrank (maximalRealSubfield M) M = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have htop : IntermediateField.adjoin (maximalRealSubfield M) {α} = ⊤ := by
    have hd := IntermediateField.finrank_dvd_of_le_right
      (le_top : IntermediateField.adjoin (maximalRealSubfield M) {α} ≤ ⊤)
    rw [IntermediateField.finrank_top', h2, Nat.dvd_prime Nat.prime_two] at hd
    rcases hd with hd | hd
    · rw [IntermediateField.finrank_eq_one_iff] at hd
      have hmem := IntermediateField.mem_adjoin_simple_self (maximalRealSubfield M) α
      rw [hd, IntermediateField.mem_bot] at hmem
      obtain ⟨y, hy⟩ := hmem
      exact absurd (hy ▸ y.2) he
    · exact IntermediateField.eq_of_le_of_finrank_eq le_top
        (by rw [hd, IntermediateField.finrank_top', h2])
  intro x
  have hx : x ∈ IntermediateField.adjoin (maximalRealSubfield M) {α} := by
    rw [htop]
    exact IntermediateField.mem_top
  have hx' : x ∈ (IntermediateField.adjoin (maximalRealSubfield M) {α}).toSubfield := hx
  rw [IntermediateField.adjoin_toSubfield] at hx'
  have hle : Subfield.closure (Set.range (algebraMap (maximalRealSubfield M) M) ∪ {α}) ≤
      RingHom.eqLocusField ((g : Ω →+* Ω).comp (algebraMap M Ω)) (algebraMap M Ω) := by
    rw [Subfield.closure_le]
    rintro y (⟨z, rfl⟩ | hy)
    · exact hR z
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      have h1 := hE e
      rw [IsScalarTower.algebraMap_apply E M Ω] at h1
      exact h1
  exact hle hx'
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InclOf
noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem fixingSubgroup_fieldRange {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (K : Type) [Field K]
    [Algebra E K] [Algebra K Ω] [IsScalarTower E K Ω] :
    (IsScalarTower.toAlgHom E K Ω).fieldRange.fixingSubgroup = fixGrp E Ω K := by
  ext g
  rw [mem_fixGrp, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x
    exact h _ ⟨x, rfl⟩
  · rintro h _ ⟨x, rfl⟩
    exact h x

theorem inclOf : InclOf := by
  intro E Ω _ _ _ _ _ _ X Y hXY
  have hGal : IsGalois E Ω := inferInstance
  set f := IsScalarTower.toAlgHom E X.K Ω
  set g := IsScalarTower.toAlgHom E Y.K Ω
  have hX := fixingSubgroup_fieldRange (E := E) (Ω := Ω) X.K
  have hY := fixingSubgroup_fieldRange (E := E) (Ω := Ω) Y.K
  have hle : f.fieldRange ≤ g.fieldRange := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup f.fieldRange,
      ← InfiniteGalois.fixedField_fixingSubgroup g.fieldRange]
    apply IntermediateField.fixedField_le
    rw [hX, hY]
    exact hXY
  set eX := AlgEquiv.ofInjectiveField f
  set eY := AlgEquiv.ofInjectiveField g
  set φ : X.K →ₐ[E] Y.K := (eY.symm.toAlgHom.comp (IntermediateField.inclusion hle)).comp eX.toAlgHom
  have hφ : ∀ x : X.K, g (φ x) = f x := by
    intro x
    have h1 : (eY (φ x) : Ω) = g (φ x) := rfl
    rw [← h1]
    have h2 : eY (φ x) = IntermediateField.inclusion hle (eX x) := eY.apply_symm_apply _
    rw [h2]
    rfl
  letI alg : Algebra X.K Y.K := φ.toRingHom.toAlgebra
  have t1 : IsScalarTower E X.K Y.K := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  have t2 : IsScalarTower X.K Y.K Ω := IsScalarTower.of_algebraMap_eq (fun x => (hφ x).symm)
  refine ⟨alg, t1, t2, IsGalois.tower_top_of_isGalois E X.K Y.K, ?_⟩
  rw [← hX, ← hY]
  have iX := IntermediateField.finrank_eq_fixingSubgroup_index Ω f.fieldRange
  have iY := IntermediateField.finrank_eq_fixingSubgroup_index Ω g.fieldRange
  have fX : Module.finrank E X.K = Module.finrank E f.fieldRange := eX.toLinearEquiv.finrank_eq
  have fY : Module.finrank E Y.K = Module.finrank E g.fieldRange := eY.toLinearEquiv.finrank_eq
  have tw := Module.finrank_mul_finrank E X.K Y.K
  have hsub : g.fieldRange.fixingSubgroup ≤ f.fieldRange.fixingSubgroup := by
    rw [hX, hY]; exact hXY
  have rel := Subgroup.relIndex_mul_index hsub
  haveI : FiniteDimensional E X.K := Module.Finite.of_restrictScalars_finite ℚ E X.K
  have hpos : 0 < Module.finrank E X.K := Module.finrank_pos
  rw [fX, iX] at tw hpos
  rw [fY, iY, ← rel] at tw
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [mul_comm] at tw; exact tw)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.PowChar
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.powChar :
    PowChar := by
  intro p _ n hn hdvd
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hprim := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨ω, hωc⟩ := hprim.isUnit hn.ne'
  have hωp : IsPrimitiveRoot ω n := by
    rw [← IsPrimitiveRoot.coe_units_iff, hωc]
    exact hprim
  have hωo : orderOf ω = n := hωp.eq_orderOf.symm
  have hnd : n ∣ p - 1 := Dvd.dvd.trans (Dvd.intro_left 2 rfl) hdvd
  have hd : orderOf ω ∣ orderOf g := by rw [hωo, hog]; exact hnd
  let lam : (ZMod p)ˣ →* ℂˣ := monoidHomOfForallMemZpowers hg hd
  have hlg : lam g = ω := monoidHomOfForallMemZpowers_apply_gen hg hd
  have hωn : ω ^ n = 1 := hωp.pow_eq_one
  have hpow : ∀ a, (lam a) ^ n = 1 := by
    intro a
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    rw [map_zpow, hlg, ← zpow_natCast, zpow_comm, zpow_natCast, hωn, one_zpow]
  refine ⟨lam, ?_, ?_, ?_⟩
  · ext1 a
    rw [MonoidHom.pow_apply, hpow, MonoidHom.one_apply]
  · obtain ⟨c, hc⟩ := hdvd
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h
        omega
      · exact h
    have hx2 : (g ^ (n * c)) ^ 2 = 1 := by
      rw [← pow_mul, show n * c * 2 = p - 1 by rw [hc]; ring, ← hog, pow_orderOf_eq_one]
    have hx1 : g ^ (n * c) ≠ 1 := by
      intro h
      have h1 := orderOf_dvd_of_pow_eq_one h
      rw [hog, hc] at h1
      have h2 := Nat.le_of_dvd (Nat.mul_pos hn hcpos) h1
      have h3 : 0 < n * c := Nat.mul_pos hn hcpos
      nlinarith
    have hxm : g ^ (n * c) = -1 := by
      have h4 : (((g ^ (n * c) : (ZMod p)ˣ)) : ZMod p) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, hx2, Units.val_one]
      rw [sq] at h4
      rcases mul_self_eq_one_iff.mp h4 with h | h
      · exact absurd (Units.ext (by rw [h, Units.val_one])) hx1
      · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
    rw [← hxm, map_pow, hlg, pow_mul, hωn, one_pow]
  · intro a ha
    have htop : Subgroup.zpowers a = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, ha, hcard]
    have hga : g ∈ Subgroup.zpowers a := by rw [htop]; trivial
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hga
    have hωa : (lam a) ^ j = ω := by rw [← map_zpow, hlg]
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (hpow a))
    rw [← hωo]
    apply orderOf_dvd_of_pow_eq_one
    rw [← hωa, ← zpow_natCast, zpow_comm, zpow_natCast, pow_orderOf_eq_one, one_zpow]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.SplitPlace
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem norm_not_mem_sq {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
    (hd : u.asIdeal.inertiaDeg ℤ = 1) (he : u.asIdeal.ramificationIdx ℤ = 1) :
    ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 F) ∉ u.asIdeal ^ 2 := by
  classical
  have hprime : Nat.Prime (Ideal.absNorm u.asIdeal) :=
    ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 u).2 hd
  haveI : Fact (Nat.Prime (Ideal.absNorm u.asIdeal)) := ⟨hprime⟩
  have hmemZ : ((Ideal.absNorm u.asIdeal : ℕ) : ℤ) ∈ u.asIdeal.under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap]
    simpa using Ideal.absNorm_mem u.asIdeal
  have hspan : u.asIdeal.under ℤ = Ideal.span {((Ideal.absNorm u.asIdeal : ℕ) : ℤ)} :=
    ((Int.ideal_span_isMaximal_of_prime (Ideal.absNorm u.asIdeal)).eq_of_le
      Ideal.IsPrime.ne_top' ((Ideal.span_singleton_le_iff_mem _).2 hmemZ)).symm
  have hp0 : u.asIdeal.under ℤ ≠ ⊥ := by
    rw [hspan, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hprime.ne_zero
  have he' : (u.asIdeal.under ℤ).ramificationIdx' u.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (u.asIdeal.under ℤ) u.asIdeal hp0]
    exact he
  have hmap : (u.asIdeal.under ℤ).map (algebraMap ℤ (𝓞 F)) ≤ u.asIdeal := Ideal.map_comap_le
  intro hmem
  refine (Ideal.ramificationIdx'_ne_one_iff hmap).2 ?_ he'
  rw [hspan, Ideal.map_span, Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
  simpa using hmem

private theorem dec_le {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {N : Subgroup (G F Ω)} (hNo : IsOpen (N : Set (G F Ω))) {B : ValuationSubring Ω}
    {u : HeightOneSpectrum (𝓞 F)} (hB : IsPlaceOver B u) (hI : Ine (F := F) B ≤ N) {σ : G F Ω}
    (hσ : IsFrob B (normV u) σ) (hσN : σ ∈ N) : Dec (F := F) B ≤ N := by
  intro d hd
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω B u hB ⟨σ, hσ.1⟩ hσ
  have hc : IsClosed ((N.subgroupOf (Dec (F := F) B) : Subgroup (Dec (F := F) B)) : Set (Dec (F := F) B)) :=
    (N.isClosed_of_isOpen hNo).preimage continuous_subtype_val
  have h2 := Subgroup.topologicalClosure_minimal
    (Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) B) ⊔ (Ine (F := F) B).subgroupOf (Dec (F := F) B))
    (sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_subgroupOf.2 hσN))
      (fun x hx => Subgroup.mem_subgroupOf.2 (hI (Subgroup.mem_subgroupOf.1 hx)))) hc
  rw [h] at h2
  exact Subgroup.mem_subgroupOf.1 (h2 (Subgroup.mem_top (⟨d, hd⟩ : Dec (F := F) B)))

theorem splitPlace : SplitPlace := by
  intro F Ω _ _ _ _ _ U hU T hT
  obtain ⟨N, hNn, hNo, -, hNU⟩ := GlobalTheory.T.exists_openNormal_finiteIndex_le_absGaloisGroup Ω F U hU
  have hc : GlobalTheory.TwSys.Cheb :=
    GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 GlobalTheory.Published.chebotarevDegreeOne'
  unfold GlobalTheory.TwSys.Cheb at hc
  obtain ⟨v, hvA, hd, he, B, hB, hIB, σ, hσ, hσN⟩ := hc F Ω N hNo hNn 1 hT.toFinset
  have hvT : v ∉ T := fun h => hvA (hT.mem_toFinset.2 h)
  have hσN' : σ ∈ N := by simpa using hσN
  have hdec := dec_le hNo hB hIB hσ hσN'
  have hnorm : normV v = Ideal.absNorm v.asIdeal := by
    simp [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  refine ⟨v, hvT, ?_, ?_, ?_, ?_⟩
  · rw [hnorm]
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hd
  · rw [hnorm]
    exact Ideal.absNorm_mem _
  · rw [hnorm]
    exact norm_not_mem_sq v hd he
  · intro A hA ρ hρ
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver hB hA
    apply hNU
    have h1 : τ⁻¹ * ρ * τ ∈ Dec (F := F) B := by
      rw [mem_Dec] at hρ ⊢
      rw [← hτ] at hρ
      rw [mul_smul, mul_smul, hρ, ← mul_smul, inv_mul_cancel, one_smul]
    have h2 := hNn.conj_mem _ (hdec h1) τ
    simpa [mul_assoc] using h2

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.FreshPrime
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private lemma normV_pos' {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) : 0 < normV t := by
  have h : Nat.card (𝓞 F ⧸ t.asIdeal) = Ideal.absNorm t.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  show 0 < Nat.card (𝓞 F ⧸ t.asIdeal)
  rw [h]
  exact Nat.pos_of_ne_zero (fun h0 => t.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))

private lemma normV_mem' {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) :
    ((normV t : ℕ) : 𝓞 F) ∈ t.asIdeal := by
  have h : Nat.card (𝓞 F ⧸ t.asIdeal) = Ideal.absNorm t.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  show ((Nat.card (𝓞 F ⧸ t.asIdeal) : ℕ) : 𝓞 F) ∈ t.asIdeal
  rw [h]
  exact Ideal.absNorm_mem _

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.freshPrime :
    SplitPlace → RootMod → FreshPrime := by
  intro hS hR
  unfold SplitPlace at hS
  unfold RootMod at hR
  unfold FreshPrime
  intro F Ω _ _ _ _ _ U hU T hT n hn
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (((2 * n : ℕ)) : Ω) := ⟨by exact_mod_cast (by omega : 2 * n ≠ 0)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (2 * n)
  have hroot : ∀ t : HeightOneSpectrum (𝓞 F), ∃ x : Ω, x ^ n = (normV t : Ω) :=
    fun t => IsAlgClosed.exists_pow_nat_eq _ hn
  choose y hy using hroot
  set S : Set Ω := insert ζ (y '' T) with hSeq
  haveI : Finite S := (Set.Finite.insert ζ (hT.image y)).to_subtype
  haveI : FiniteDimensional F (IntermediateField.adjoin F S) :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := F) x).isIntegral)
  set U' : Subgroup (G F Ω) := U ⊓ (IntermediateField.adjoin F S).fixingSubgroup with hU'eq
  have hU' : IsOpen (U' : Set (G F Ω)) := by
    rw [hU'eq, Subgroup.coe_inf]
    exact hU.inter (IntermediateField.fixingSubgroup_isOpen _)
  have hfix : ∀ g : G F Ω, g ∈ U' → ∀ x ∈ S, (g : Ω → Ω) x = x := by
    intro g hg x hx
    have hg2 := (Subgroup.mem_inf.mp hg).2
    exact (mem_fixingSubgroup_iff _).mp hg2 x (IntermediateField.subset_adjoin F S hx)
  have hfinset : ∀ a : 𝓞 F, a ≠ 0 → {w : HeightOneSpectrum (𝓞 F) | a ∈ w.asIdeal}.Finite := by
    intro a ha
    have h0 : Ideal.span {a} ≠ (0 : Ideal (𝓞 F)) := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact ha
    simpa only [Ideal.dvd_span_singleton] using Ideal.finite_factors h0
  have hcast : ∀ m : ℕ, m ≠ 0 → ((m : ℕ) : 𝓞 F) ≠ 0 := fun m hm => by exact_mod_cast hm
  set B : Set (HeightOneSpectrum (𝓞 F)) :=
    T ∪ (⋃ t ∈ T, {w | ((normV t : ℕ) : 𝓞 F) ∈ w.asIdeal}) ∪ {w | ((2 * n : ℕ) : 𝓞 F) ∈ w.asIdeal}
    with hBeq
  have hB : B.Finite := by
    refine (hT.union (hT.biUnion fun t _ => hfinset _ (hcast _ (normV_pos' t).ne'))).union ?_
    exact hfinset _ (hcast _ (by omega))
  obtain ⟨u, huB, hp, hpu, hpu2, hdec⟩ := hS F Ω U' hU' B hB
  have hdvd_mem : ∀ m : ℕ, normV u ∣ m → ((m : ℕ) : 𝓞 F) ∈ u.asIdeal := by
    rintro m ⟨k, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ hpu
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω u
  have hDA : ∀ x ∈ S, ∀ g ∈ Dec A, (g : Ω → Ω) x = x := fun x hx g hg => hfix g (hdec A hA hg) x hx
  refine ⟨u, fun h => huB (Or.inl (Or.inl h)), hp, hpu, hpu2,
    fun A' hA' => le_trans (hdec A' hA') inf_le_left, ?_, ?_⟩
  · refine (hR F Ω A u hA (normV u) hp rfl ζ (2 * n) (by omega) (hDA ζ (Set.mem_insert _ _))).2 hζ ?_
    intro h2
    exact huB (Or.inr (hdvd_mem _ h2))
  · intro t ht
    refine ⟨?_, (hR F Ω A u hA (normV u) hp rfl (y t) n hn
      (hDA (y t) (Set.mem_insert_of_mem _ ⟨t, ht, rfl⟩))).1 (normV t) (hy t)⟩
    intro hut
    by_cases hd : normV u ∣ normV t
    · exact huB (Or.inl (Or.inr (Set.mem_biUnion ht (hdvd_mem _ hd))))
    · have hcop : Nat.Coprime (normV u) (normV t) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hd
      have hg := Nat.gcd_eq_gcd_ab (normV u) (normV t)
      rw [hcop] at hg
      have hg' := congrArg (Int.cast : ℤ → 𝓞 F) hg
      push_cast at hg'
      have h1 : (1 : 𝓞 F) ∈ t.asIdeal := by
        rw [hg']
        exact t.asIdeal.add_mem (Ideal.mul_mem_right _ _ hut) (Ideal.mul_mem_right _ _ (normV_mem' t))
      exact t.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
end
