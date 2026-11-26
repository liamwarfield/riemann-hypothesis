module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdempotentFiniteRankAdjointCuspidal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConj
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardOfInjective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasing
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3 hiding IsLabElt IsLocElt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodPrimes

theorem isConjPl_iff {D : D7} {P P' : Pl D.host.E} : Formalism.IndefR.Lev.IsConjPl P P' ↔ P' = Formalism.DivisionValues.conjPl P := by
  constructor
  · intro h
    apply HeightOneSpectrum.ext
    refine ((Formalism.DivisionValues.conjPl P).isMaximal.eq_of_le P'.isPrime.ne_top ?_).symm
    refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
    obtain ⟨c', h1, h2⟩ := h c hc
    have : Formalism.DivisionValues.cO _ c = c' := RingOfIntegers.ext h2.symm
    show Formalism.DivisionValues.cO _ c ∈ P'.asIdeal
    rwa [this]
  · rintro rfl
    exact fun c hc => ⟨Formalism.DivisionValues.cO _ c, Ideal.mem_map_of_mem _ hc, rfl⟩

theorem eq_or_conj_of_under_eq {D : D7} {P Q : Pl D.host.E} (h : Q.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) :
    Q = P ∨ Q = Formalism.DivisionValues.conjPl P := by
  have hsub : (Q.asIdeal : Set (𝓞 D.host.E)) ⊆ P.asIdeal ∪ (Formalism.DivisionValues.conjPl P).asIdeal := by
    intro x hx
    have hfix : star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E) := by
      rw [star_mul', star_star, mul_comm]
    obtain ⟨y, hy⟩ := (D.sp.cm.fixed ((x : D.host.E) * star (x : D.host.E))).1 hfix
    have hint : IsIntegral ℤ y := by
      rw [← isIntegral_algebraMap_iff (B := D.host.E)]
      have e : algebraMap D.host.F D.host.E y = ((x * Formalism.DivisionValues.cO _ x : 𝓞 D.host.E) : D.host.E) := hy
      rw [e]
      exact (x * Formalism.DivisionValues.cO _ x).isIntegral_coe
    have hn : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨y, hint⟩ = x * Formalism.DivisionValues.cO _ x := RingOfIntegers.ext hy
    have h1 : (⟨y, hint⟩ : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ Q.asIdeal
      rw [hn]
      exact Ideal.mul_mem_right _ _ hx
    rw [h] at h1
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨y, hint⟩ ∈ P.asIdeal := h1
    rw [hn] at h2
    refine (P.isPrime.mem_or_mem h2).imp id fun h3 => ?_
    have h4 : Formalism.DivisionValues.cO _ (Formalism.DivisionValues.cO _ x) ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ h3
    have e : Formalism.DivisionValues.cO _ (Formalism.DivisionValues.cO _ x) = x := RingOfIntegers.ext (star_star (x : D.host.E))
    rw [e] at h4
    exact h4
  exact (Ideal.subset_union.1 hsub).imp
    (fun h => HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h))
    (fun h => HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (Formalism.DivisionValues.conjPl P).isPrime.ne_top h))

theorem offS_iff {D : D7} (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : Pl D.host.E) :
    OffS D S P ↔ P.under (𝓞 D.host.F) ∉ S := by
  constructor
  · intro h hP
    obtain ⟨x, hx, hy⟩ := h _ hP
    exact hy (algebraMap _ _ x) rfl hx
  · intro h v hv
    by_contra hc
    push Not at hc
    apply h
    have : v = P.under (𝓞 D.host.F) := by
      refine HeightOneSpectrum.ext (v.isMaximal.eq_of_le (P.under (𝓞 D.host.F)).isPrime.ne_top fun x hx => ?_)
      obtain ⟨y, h1, h2⟩ := hc x hx
      have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x = y := RingOfIntegers.ext h1.symm
      show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P.asIdeal
      rwa [e]
    rwa [← this]

theorem good_primes : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.Q A.μ0 = ∅ ∧ (∀ t P, Good R t P → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ Good R t (Formalism.DivisionValues.conjPl P) ∧ Good R A.μ0 P) ∧ (∀ SF, IsSF R SF → ∀ P, OffS D SF P ↔ Good R A.μ0 P) ∧ (R.IsFam → ∀ t, ∀ P ∈ A.ok t, Good R t (R.pl P) ∧ Formalism.DivisionValues.conjPl (R.pl P) ≠ R.pl P ∧ A.q P = Ideal.absNorm (R.pl P).asIdeal) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL
  have hQ : R.Q A.μ0 = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP h => ?_
    refine (hL.Q_ram A.μ0 PP).2 (Or.inl h) ?_
    rw [hL.xi_base]
    exact fun x _ => rfl
  have hcc := fun w : Pl D.host.E => Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl w
  refine ⟨hQ, fun t P hP => ⟨fun hg => ?_, fun PP h => ?_, fun PP h => ?_⟩, fun SF hSF P => ?_, fun hF t P hP => ?_⟩
  · have hk : ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
      rw [Nat.cast_mul] at hg
      rcases P.isPrime.mem_or_mem hg with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    obtain ⟨k, hk⟩ := hk
    rcases GlobalTheory.ConjOverQuad.div_or_conj_div D R.C.P k P hk with h | ⟨w', h, hw⟩
    · exact (hP P (Or.inl ((hL.Pg P).2 ⟨k, h⟩))).1 rfl
    · refine (hP w' (Or.inl ((hL.Pg w').2 ⟨k, h⟩))).2 (isConjPl_iff.2 ?_)
      rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at hw
      rw [HeightOneSpectrum.ext hw, hcc]
  · obtain ⟨h1, h2⟩ := hP PP h
    rw [isConjPl_iff] at h2 ⊢
    refine ⟨fun e => h2 (by rw [e, hcc]), fun e => h1 ?_⟩
    rw [← hcc PP, ← e, hcc]
  · rw [hQ] at h
    exact hP PP (Or.inl (h.resolve_right (Finset.notMem_empty _)))
  · rw [offS_iff]
    constructor
    · intro h PP hPP
      rw [hQ] at hPP
      have hPP' := hPP.resolve_right (Finset.notMem_empty _)
      have key : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F) := fun e =>
        h ((hSF _).2 ⟨PP, hPP', by rw [← e]; rfl⟩)
      exact ⟨fun e => key (by rw [e]), fun e => key (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e)⟩
    · intro h hm
      obtain ⟨PP, hPP, e⟩ := (hSF _).1 hm
      obtain ⟨h1, h2⟩ := h PP (Or.inl hPP)
      have e' : P.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := HeightOneSpectrum.ext e.symm
      rcases eq_or_conj_of_under_eq e' with h3 | h3
      · exact h1 h3.symm
      · exact h2 (isConjPl_iff.2 h3)
  · obtain ⟨gramR, c0R, c0L, hT⟩ := hF.tie
    obtain ⟨h1, h2, h3⟩ := (hT.ok t P).1 hP
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at h1 h3
    refine ⟨fun PP h => ?_, fun e => h1 (by rw [e]), ?_⟩
    · have hm : PP ∈ (R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E)) :=
        h.imp (fun h => hF.Sb h) id
      refine ⟨fun e => h2 (e ▸ hm), fun hc => h3 PP hm ?_⟩
      rw [isConjPl_iff.1 hc, hcc]
    · rw [hT.q P, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.GoodPrimes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3 hiding IsLabElt IsLocElt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_levels_good_primes_properties : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.Q A.μ0 = ∅ ∧ (∀ t P, Good R t P → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ Good R t (conjPl P) ∧ Good R A.μ0 P) ∧ (∀ SF, IsSF R SF → ∀ P, OffS D SF P ↔ Good R A.μ0 P) ∧ (R.IsFam → ∀ t, ∀ P ∈ A.ok t, Good R t (R.pl P) ∧ conjPl (R.pl P) ≠ R.pl P ∧ A.q P = Ideal.absNorm (R.pl P).asIdeal) := by
  first | exact @GlobalTheory.GoodPrimes.good_primes | exact GlobalTheory.GoodPrimes.good_primes | (intros; apply GlobalTheory.GoodPrimes.good_primes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.SplitRead

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem eig_lpOfChar (ξ : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ) (σ : Weil h) :
    (WD.lpOfChar h ξ hξ).eig σ = {(ξ σ : ℂ)} := by
  rw [WD.lpOfChar, WD.eig_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp

theorem cls_eq_ofChar (χ : (w.adicCompletion E)ˣ →* ℂˣ) (c : Irr (w.adicCompletion E) 1)
    (hc : Nonempty (c.π.Equiv (detRep (Fin 1) χ))) :
    ∃ hχ : IsSmoothChar χ, cls (toIrrRep c) = .ofChar χ hχ := by
  obtain ⟨φ⟩ := hc
  have h1 : IsSmoothChar (detChar (Fin 1) χ) := (isSmooth_ofChar_iff _).1
    ((IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).isSmooth c.smooth)
  have h2 : Continuous (Matrix.GeneralLinearGroup.scalar (R := w.adicCompletion E) (Fin 1)) :=
    Units.continuous_map (continuous_matrix fun i j => by
      rw [Subsingleton.elim i j]; simpa using continuous_id')
  have h3 : (detChar (Fin 1) χ).comp (Matrix.GeneralLinearGroup.scalar (Fin 1)) = χ := by
    refine MonoidHom.ext fun z => congrArg χ ?_
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  exact ⟨h3 ▸ h1.comp _ h2, congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ⟨φ⟩)⟩

theorem IsRec.recUnit {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRec h rc) :
    RecUnit fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  intro χ c hu hc g α hα
  obtain ⟨hχ, e⟩ := cls_eq_ofChar χ c hc
  simp only [e, H.one, eig_lpOfChar, Multiset.mem_singleton] at hα
  rw [hα]
  exact hu _

end GlobalTheory.LocLanglands
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepDualIsoOfCommonRepresentedFunctional
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepDualIsoOfCommonRepresentedFunctional
open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.ContraPair

theorem iso_of_common_functional : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (s₁ s₂ : Op E a → Op E a), Function.Involutive s₁ → Function.Involutive s₂ → ∀ B₁ B₂ : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B₁ φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B₁ φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B₁ (π.op (.fin k) φ) (π.op (s₁ (.fin k)) ψ) = B₁ φ ψ) → (∀ k φ ψ, B₁ (π.op (.cpt k) φ) (π.op (s₁ (.cpt k)) ψ) = B₁ φ ψ) → (∀ X φ ψ, B₁ (π.op (.lie X) φ) ψ + B₁ φ (π.op (s₁ (.lie X)) ψ) = 0) → (∀ φ, (∀ ψ, B₂ φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B₂ φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B₂ (π.op (.fin k) φ) (π.op (s₂ (.fin k)) ψ) = B₂ φ ψ) → (∀ k φ ψ, B₂ (π.op (.cpt k) φ) (π.op (s₂ (.cpt k)) ψ) = B₂ φ ψ) → (∀ X φ ψ, B₂ (π.op (.lie X) φ) ψ + B₂ φ (π.op (s₂ (.lie X)) ψ) = 0) → ∀ ψ₁ ψ₂ : π.V, ψ₁ ≠ 0 → (∀ φ, B₁ φ ψ₁ = B₂ φ ψ₂) → ∃ S : π.V ≃ₗ[ℂ] π.V, ∀ o φ, S (π.op (s₁ o) φ) = π.op (s₂ o) (S φ) := by
  intro E _ _ _ a π s₁ s₂ hs₁ hs₂ B₁ B₂ hl₁ hr₁ hf₁ hc₁ hL₁ hl₂ hr₂ hf₂ hc₂ hL₂ ψ₁ ψ₂ hψ₁ hψ

  have irr : ∀ P : Submodule ℂ π.V, (∀ o, ∀ x ∈ P, π.op o x ∈ P) → P ≠ ⊥ → P = ⊤ := by
    intro P hP h0
    have hst : _root_.GlobalTheory.CuspRep.IsStable (P.map π.V.subtype) := by
      rintro o _ ⟨x, hx, rfl⟩
      exact ⟨π.op o x, hP o x hx, rfl⟩
    have e := Submodule.comap_map_eq_of_injective π.V.injective_subtype P
    rcases π.irred _ (Submodule.map_subtype_le _ _) hst with h | h
    · exact absurd (by rw [← e, h, Submodule.comap_bot, Submodule.ker_subtype]) h0
    · rw [← e, h, Submodule.comap_subtype_self]
  have hfin : ∀ k (φ : π.V), π.op (.fin k) (π.op (.fin k⁻¹) φ) = φ := fun k φ => Subtype.ext (by
    show (finRep E a k * finRep E a k⁻¹) φ.1 = φ.1
    rw [← map_mul, mul_inv_cancel, map_one]; rfl)
  have hcpt : ∀ k (φ : π.V), π.op (.cpt k) (π.op (.cpt k⁻¹) φ) = φ := fun k φ => Subtype.ext (by
    show (cptRep E a k * cptRep E a k⁻¹) φ.1 = φ.1
    rw [← map_mul, mul_inv_cancel, map_one]; rfl)

  have key : ∀ o ψ ψ', (∀ φ, B₁ φ ψ = B₂ φ ψ') → ∀ φ, B₁ φ (π.op (s₁ o) ψ) = B₂ φ (π.op (s₂ o) ψ') := by
    intro o ψ ψ' h φ
    cases o with
    | fin k =>
      have e1 := hf₁ k (π.op (.fin k⁻¹) φ) ψ
      have e2 := hf₂ k (π.op (.fin k⁻¹) φ) ψ'
      rw [hfin] at e1 e2
      rw [e1, e2, h]
    | cpt k =>
      have e1 := hc₁ k (π.op (.cpt k⁻¹) φ) ψ
      have e2 := hc₂ k (π.op (.cpt k⁻¹) φ) ψ'
      rw [hcpt] at e1 e2
      rw [e1, e2, h]
    | lie X =>
      have e1 := hL₁ X φ ψ
      have e2 := hL₂ X φ ψ'
      have e3 := h (π.op (.lie X) φ)
      linear_combination e1 - e2 - e3
  have uniq : ∀ x y : π.V, (∀ φ, B₂ φ x = B₂ φ y) → x = y := fun x y h =>
    sub_eq_zero.1 (hr₂ _ fun φ => by rw [map_sub, h, sub_self])
  have inj₂ : Function.Injective B₂.flip := fun x y h => uniq x y fun φ => by
    simpa using LinearMap.congr_fun h φ

  let N : Submodule ℂ π.V := (LinearMap.range B₂.flip).comap B₁.flip
  have memN : ∀ ψ ψ', (∀ φ, B₁ φ ψ = B₂ φ ψ') → ψ ∈ N := fun ψ ψ' h =>
    ⟨ψ', LinearMap.ext fun φ => by simpa using (h φ).symm⟩
  have hN : N = ⊤ := by
    refine irr N (fun o x hx => ?_) fun h => hψ₁ ((Submodule.eq_bot_iff _).1 h ψ₁ (memN _ _ hψ))
    obtain ⟨y, hy⟩ := hx
    have h : ∀ φ, B₁ φ x = B₂ φ y := fun φ => by simpa using (LinearMap.congr_fun hy φ).symm
    have := key (s₁ o) x y h
    rw [hs₁ o] at this
    exact memN _ _ this
  have hmem : ∀ ψ, B₁.flip ψ ∈ LinearMap.range B₂.flip := fun ψ =>
    (show ψ ∈ N from hN ▸ Submodule.mem_top)
  let T : π.V →ₗ[ℂ] π.V := (LinearEquiv.ofInjective B₂.flip inj₂).symm.toLinearMap ∘ₗ
    B₁.flip.codRestrict (LinearMap.range B₂.flip) hmem
  have hT : ∀ ψ φ, B₂ φ (T ψ) = B₁ φ ψ := by
    intro ψ φ
    have h1 := congrArg Subtype.val ((LinearEquiv.ofInjective B₂.flip inj₂).apply_symm_apply
      (B₁.flip.codRestrict (LinearMap.range B₂.flip) hmem ψ))
    rw [LinearEquiv.ofInjective_apply, LinearMap.codRestrict_apply] at h1
    have h2 := LinearMap.congr_fun h1 φ
    rw [LinearMap.flip_apply, LinearMap.flip_apply] at h2
    exact h2
  have hTo : ∀ o φ, T (π.op (s₁ o) φ) = π.op (s₂ o) (T φ) := fun o φ =>
    uniq _ _ fun χ => by rw [hT]; exact key o φ (T φ) (fun χ => (hT φ χ).symm) χ
  have injT : Function.Injective T := fun x y h =>
    sub_eq_zero.1 (hr₁ _ fun φ => by rw [map_sub, ← hT, ← hT, h, sub_self])
  have hR : LinearMap.range T = ⊤ := by
    refine irr _ (fun o x hx => ?_) fun h => hψ₁ (injT ?_)
    · obtain ⟨y, rfl⟩ := hx
      refine ⟨π.op (s₁ (s₂ o)) y, ?_⟩
      rw [hTo, hs₂ o]
    · rw [map_zero]
      exact (Submodule.eq_bot_iff _).1 h _ ⟨ψ₁, rfl⟩
  exact ⟨LinearEquiv.ofBijective T ⟨injT, LinearMap.range_eq_top.1 hR⟩, hTo⟩

end GlobalTheory.ContraPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepDualIsoOfCommonRepresentedFunctionalStatement
open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspRep_dual_iso_of_common_represented_functional : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (s₁ s₂ : Op E a → Op E a), Function.Involutive s₁ → Function.Involutive s₂ → ∀ B₁ B₂ : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B₁ φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B₁ φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B₁ (π.op (.fin k) φ) (π.op (s₁ (.fin k)) ψ) = B₁ φ ψ) → (∀ k φ ψ, B₁ (π.op (.cpt k) φ) (π.op (s₁ (.cpt k)) ψ) = B₁ φ ψ) → (∀ X φ ψ, B₁ (π.op (.lie X) φ) ψ + B₁ φ (π.op (s₁ (.lie X)) ψ) = 0) → (∀ φ, (∀ ψ, B₂ φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B₂ φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B₂ (π.op (.fin k) φ) (π.op (s₂ (.fin k)) ψ) = B₂ φ ψ) → (∀ k φ ψ, B₂ (π.op (.cpt k) φ) (π.op (s₂ (.cpt k)) ψ) = B₂ φ ψ) → (∀ X φ ψ, B₂ (π.op (.lie X) φ) ψ + B₂ φ (π.op (s₂ (.lie X)) ψ) = 0) → ∀ ψ₁ ψ₂ : π.V, ψ₁ ≠ 0 → (∀ φ, B₁ φ ψ₁ = B₂ φ ψ₂) → ∃ S : π.V ≃ₗ[ℂ] π.V, ∀ o φ, S (π.op (s₁ o) φ) = π.op (s₂ o) (S φ) := by
  first | exact @GlobalTheory.ContraPair.iso_of_common_functional | exact GlobalTheory.ContraPair.iso_of_common_functional | (intros; apply GlobalTheory.ContraPair.iso_of_common_functional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FunctionalFixedByIdempotentRepresented
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FunctionalFixedByIdempotentRepresented
namespace GlobalTheory

theorem functional_fixed_by_idempotent_represented
    {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hL : ∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) (_hR : ∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0)
    (P P' : Module.End ℂ V) (_hP : P ∘ₗ P = P) (hfin : FiniteDimensional ℂ (LinearMap.range P))
    (hadj : ∀ φ ψ, B (P φ) ψ = B φ (P' ψ)) (f : V →ₗ[ℂ] ℂ) (hf : f ∘ₗ P = f) :
    ∃ ψ, ∀ φ, B φ ψ = f φ := by
  set U := LinearMap.range P

  let T : V →ₗ[ℂ] Module.Dual ℂ U := (B.domRestrict U).flip
  have hT : ∀ ψ (u : U), T ψ u = B u ψ := fun _ _ => rfl
  have hcoann : (LinearMap.range T).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_dualCoannihilator] at hu
    have : (u : V) = 0 := hL u (fun ψ => by
      have := hu (T ψ) ⟨ψ, rfl⟩
      simpa [hT] using this)
    simpa using Subtype.ext this
  have hsurj : LinearMap.range T = ⊤ := by
    have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range T)
    rw [hcoann] at h
    rw [← h]
    exact Submodule.dualAnnihilator_bot
  have : f.domRestrict U ∈ LinearMap.range T := by rw [hsurj]; trivial
  obtain ⟨ψ, hψ⟩ := this
  refine ⟨P' ψ, fun φ => ?_⟩
  rw [← hadj]
  have h1 : T ψ ⟨P φ, φ, rfl⟩ = f (P φ) := by rw [hψ]; rfl
  rw [hT] at h1
  rw [h1]
  exact congrArg (fun g : V →ₗ[ℂ] ℂ => g φ) hf

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FunctionalFixedByIdempotentRepresentedStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ), (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) → ∀ (P P' : Module.End ℂ V), P ∘ₗ P = P → FiniteDimensional ℂ (LinearMap.range P) → (∀ φ ψ, B (P φ) ψ = B φ (P' ψ)) → ∀ f : V →ₗ[ℂ] ℂ, f ∘ₗ P = f → ∃ ψ, ∀ φ, B φ ψ = f φ := by
  first | exact @GlobalTheory.functional_fixed_by_idempotent_represented | exact GlobalTheory.functional_fixed_by_idempotent_represented | (intros; apply GlobalTheory.functional_fixed_by_idempotent_represented <;> assumption)
end
end

noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CsdBack

theorem invTOp_involutive {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} :
    Function.Involutive (invTOp : Op E a → Op E a) := by
  intro o
  cases o with
  | fin k => simp only [invTOp]; congr 1
  | cpt k => simp only [invTOp]; congr 1; ext i j; simp [barK, Matrix.star_apply]
  | lie X =>
    simp only [invTOp]; congr 1
    funext i j
    exact neg_neg (X i j)

theorem conjOp_involutive {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ} :
    Function.Involutive (conjOp : Op L a → Op L a) := by
  intro o
  cases o with
  | fin k => simp only [conjOp]; congr 1; ext i j; simp [GlobalTheory.ThetaPull.cFin_cFin]
  | cpt k => simp only [conjOp]; congr 1; ext i j; simp [barK, Matrix.star_apply]
  | lie X => simp only [conjOp]; congr 1; ext i j; simp

theorem isCsd_of_paired : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (a : ℕ) (π : CuspSub L a), Paired π π invTOp → DualIsConj π → π.IsCsd := by
  intro hP L _ _ _ a π h1 h2
  obtain ⟨B₁, l1, r1, f1, c1, x1⟩ := h1
  obtain ⟨B₂, l2, r2, f2, c2, x2⟩ := h2
  obtain ⟨P, hP0, hPP, hfin, hadj⟩ := GlobalTheory.T.exists_idempotent_finiteRank_adjoint_cuspidal hP L a π
  obtain ⟨P₁, e1⟩ := hadj invTOp (Or.inl rfl) B₁ l1 r1 f1 c1 x1
  obtain ⟨P₂, e2⟩ := hadj conjOp (Or.inr rfl) B₂ l2 r2 f2 c2 x2
  obtain ⟨v, hv⟩ : ∃ v, P v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP0 (LinearMap.ext h)
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ℂ π.V, g (P v) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ (P v)).1 h)
  have hf : (g ∘ₗ P) ∘ₗ P = g ∘ₗ P := by rw [LinearMap.comp_assoc, hPP]
  obtain ⟨ψ₁, hψ₁⟩ := GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate B₁ l1 r1 P P₁ hPP hfin e1 (g ∘ₗ P) hf
  obtain ⟨ψ₂, hψ₂⟩ := GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate B₂ l2 r2 P P₂ hPP hfin e2 (g ∘ₗ P) hf
  have hne : ψ₁ ≠ 0 := by
    rintro rfl
    apply hg
    have := hψ₁ v
    simp only [map_zero, LinearMap.comp_apply] at this
    exact this.symm
  obtain ⟨S, hS⟩ := GlobalTheory.T.cuspRep_dual_iso_of_common_represented_functional L a π invTOp conjOp invTOp_involutive conjOp_involutive B₁ B₂ l1 r1 f1 c1 x1
    l2 r2 f2 c2 x2 ψ₁ ψ₂ hne (fun φ => (hψ₁ φ).trans (hψ₂ φ).symm)
  exact GlobalTheory.T.isConjSelfDual_of_invTranspose_iso_cmConj L a π S hS

end GlobalTheory.CsdBack

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator (FnModAt FnMod facTop)
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis)

section Notions

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] {a b : ℕ}

def AwayAt (P : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)) (B : ℕ) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (Φ : HomE E a b → K) : Prop :=
  (∀ x, w.valuation K (Φ x) ≤ 1) ∧ ∀ x z, z ∈ homAt {P} N N' → Φ (x + ((qOf P : E) ^ B) • z) = Φ x

open Classical in
def DatumAt (Sg S : Finset (HeightOneSpectrum (𝓞 E))) (g c : ℕ) (w : HeightOneSpectrum (𝓞 K)) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (Ξ : HomE E a b → K) : Prop :=
  (∀ x, w.valuation K (Ξ x) ≤ 1) ∧ (∀ x, Ξ x ≠ 0 → x ∈ homAt Sg N N') ∧
    ∀ x z, z ∈ mulLat g (homAt Sg N N') → z ∈ mulLat c (homAt (S \ Sg) N N') → Ξ (x + z) = Ξ x

end Notions

def JetLossAt {X : Fields} (Pr : Primes X) (R : Ranks) (A : Amb X)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) : Prop :=
  ∀ (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)), ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal →
  ∀ (u : Pr.Word) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok →
  ∀ (j b : ℕ), j < R.m → b = R.N (j + 1) →
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E (R.N j))) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N → IsSdLat N' → StdOver (Pr.g i) N → StdOver (Pr.g i) N' →
  ∀ Ξ : HomE X.E (R.N j) b → X.K, DatumAt (Pr.vG i) (Sall sel mu u) (Pr.g i) (cBof sel mu cst u) w N N' Ξ →
  ∀ e : DVar X.Tau (R.N j) b →₀ ℕ, e.degree + 1 < Pr.g i →
    e ∈ RatIdx A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ →
    w.valuation X.K ((Pr.g i : X.K) ^ (X.f * R.N j * b) *
      (e.prod fun k n => X.emb k.1 (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ n) *
      jetSum A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ e) ≤ 1

def LevelPrimes : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel →
    ∀ P : rowSG Pr sel mu, DegOneUnram P.1 ∧ (P.1 ∉ Pr.vGs → qOf P.1 ∉ S)

def HeckeUnit : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (m : ℕ) (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (e : X.Tau → ℚ) (j : Fin m)
    (χ : Formalism.L2.Host.HChar X.E), X.Ok → Pr.Ok → IsMu0 Ch σ₀ e j χ →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (P : HeightOneSpectrum (𝓞 X.E)), p.Prime → (p : 𝓞 X.K) ∈ w.asIdeal →
      (p : 𝓞 X.E) ∉ P.asIdeal → ∀ (x : X.Eˣ) (k : X.K), σ₀ k = ((χ.locK P x : ℂˣ) : ℂ) → w.valuation X.K k = 1

def TwistUnit : Prop :=
  ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field K] [NumberField K] (S : Set ℕ)
    (mu : Tup F E K S) (P : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)),
    w.valuation K ((Formalism.L2.Ker.unifVal (mu : Chr F E K) P : Kˣ) : K) = 1 ∧ w.valuation K ((qValC (mu : Chr F E K) P : Kˣ) : K) = 1

def ScalarUnit : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ)
    (e : Fin R.m → X.Tau → ℚ) (eta : Formalism.L2.Host.HChar X.E),
    X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → Ch.Tied G.σ₀ e G.mu0 eta → L.Ok Ch sel mu cst G m2 →
    ∀ (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)), ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal → ∀ j, j < R.m →
      (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vG i → w.valuation X.K (cst.muq (j + 1) P) = 1) ∧
      ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)),
        IsSdLat N → StdOver (Pr.g i) N → IsFrames N fr →
        w.valuation X.K (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu j) (muAt Ch sel mu cst j) N fr) = 1

def EntryAtG : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    L.Ok Ch sel mu cst G m2 → ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
      DegOneUnram P.1 → FnMod P.1 (XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P))

def VolumeAtQ : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j)
    (w : HeightOneSpectrum (𝓞 X.K)), P ∉ Pr.vGs → DegOneUnram P → ((qOf P : ℕ) : 𝓞 X.K) ∉ w.asIdeal →
    w.valuation X.K (Loc.volN X.K (Loc.Cbe (Jat (Pr := Pr) sharp j P) h)
      (Loc.N1 X.E (R.N j) (cOf R j) ⊓ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P)))⁻¹ ≤ 1

def EntryAtQ : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    L.Ok Ch sel mu cst G m2 → ∀ (P : rowSG Pr sel mu) (w : HeightOneSpectrum (𝓞 X.K)), P.1 ∉ Pr.vGs → DegOneUnram P.1 →
      ((qOf P.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal → (∀ j, j < R.m → w.valuation X.K (cst.muq (j + 1) P) = 1) →
      (∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)),
        AwayAt P.1 w cst.B (stdLat X.E _) (stdLat X.E _) (XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P))) ∧
      ∀ (al : L.β m2) (y : Sp X.E (R.N (m2 + 1))),
        AwayAt P.1 w cst.B (stdLat X.E _) (stdLat X.E _) fun x => PsiAt Ch sel mu cst m2 P (L.h m2 al P) x y

def TopAtQ : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ)
    (u : Pr.Word), Pr.Ok → IsSel X sel → Pr.T u ∈ S →
    L.Ok Ch sel mu cst G m2 → ∀ (P : rowSG Pr sel mu) (w : HeightOneSpectrum (𝓞 X.K)), P.1 ∉ Pr.vGs → DegOneUnram P.1 →
      ((qOf P.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal →
      ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) (d : RowPt Pr R sel mu), ∀ Y ∈ ybSet sel mu cst p.deco.1.N,
        AwayAt P.1 w cst.B p.deco.1.N (tilQ sel mu u d).1.N (facTop Ch sel mu cst m2 p Y d P)

def JetOpIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b)
    (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ), WtCompat hab lam lam' s s' n →
    ∀ (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K)),
      LatWithBasis w M 1 → LatWithBasis w MW 1 →
      ∀ (c : K) (J : (DVar ι a b →₀ ℕ) → K), (∀ m, InDeg lam s' m → w.valuation K (c * J m) ≤ 1) →
        ∀ F ∈ HAt w lam M, c • jetOp lam lam' J n F ∈ HAt w lam' MW

def NabLeDel : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsFullLattice K (M τ)) →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → (∀ τ, (lam τ).spread < p) →
      localization₂ w.asIdeal (nabK lam M) ≤ localization₂ w.asIdeal (delK lam M)

theorem _root_.GlobalTheory.ColPeriod.N_lt_succ (R : _root_.Formalism.BasicNotions.Ranks) (j : ℕ) : R.N j < R.N (j + 1) := by
  unfold _root_.Formalism.BasicNotions.Ranks.N
  simp

def ChainWeights : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (u : Pr.Word) (j : ℕ), j < R.m →
    ∃ s s' : X.Tau → ℤ, WtCompat (N_lt_succ R j) (W.lamTrue u j) (W.lamTrue u (j + 1)) s s' (nuLast W u j) ∧
      ∀ (τ : X.Tau) (a : Fin (R.N j)), (W.lamTrue u j τ).w a + s' τ = (W.nuW u (j + 1) τ).w a

def PartitionSize : Prop :=
  ∀ (D : D7) (EX : ErrX D) (u : D.what₂.Word) (j : ℕ), j < D.R.m → ∀ τ : D.what₂.Tau,
    nuAbs D u (j + 1) τ = ((∑ a, ((recWts EX).nuW u (j + 1) τ).w a : ℤ) : ℝ)

def StdMove : Prop :=
  ∀ (X : Fields) (Pr : Primes X), Pr.Ok → ∀ (i : Fin 2) (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N →
    ∃ γ : UF X.E n, StdOver (Pr.g i) (gmap γ.1 N)

end GlobalTheory.ColPeriod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
noncomputable section

namespace GlobalTheory.Hk3.GramSep

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def gam (σ : L →+* L) (ϖ : L) {r : ℕ} (e : Fin r → ℕ) : AddSubgroup (Matrix (Fin r) (Fin r) L) where
  carrier := {Γ | (∀ k j, σ (Γ k j) = - Γ j k) ∧ ∀ k j, Valued.v (Γ k j) ≤ Valued.v ϖ ^ max (e k) (e j)}
  zero_mem' := ⟨fun k j => by simp, fun k j => by simp⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.add_apply, map_add (f := _), ha.1 k j, hb.1 k j]; ring
    · exact (Valuation.map_add _ _ _).trans (max_le (ha.2 k j) (hb.2 k j))
  neg_mem' := by
    intro a ha
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.neg_apply, map_neg, ha.1 k j]
    · simpa only [Matrix.neg_apply, Valuation.map_neg] using ha.2 k j

def gam0 (σ : L →+* L) (ϖ : L) {r : ℕ} (e : Fin r → ℕ) : AddSubgroup (Matrix (Fin r) (Fin r) L) where
  carrier := {Γ | (∀ k j, σ (Γ k j) = - Γ j k) ∧ ∀ k j, Valued.v (Γ k j) ≤ Valued.v ϖ ^ (e k + e j)}
  zero_mem' := ⟨fun k j => by simp, fun k j => by simp⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.add_apply, map_add (f := _), ha.1 k j, hb.1 k j]; ring
    · exact (Valuation.map_add _ _ _).trans (max_le (ha.2 k j) (hb.2 k j))
  neg_mem' := by
    intro a ha
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.neg_apply, map_neg, ha.1 k j]
    · simpa only [Matrix.neg_apply, Valuation.map_neg] using ha.2 k j

end GlobalTheory.Hk3.GramSep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsLiftsRationalSelfAdjointLabel
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsLiftsRationalSelfAdjointLabel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3 hiding IsLabElt IsLocElt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertHeckeLift

theorem dualC_single {d : List ℤ} (hd : dualLab d = d) :
    dualC (Finsupp.mapRange star (star_zero ℂ) (Finsupp.single d (1 : ℂ))) = Finsupp.single d 1 := by
  rw [Finsupp.mapRange_single, star_one, dualC, Finsupp.mapDomain_single, hd]

theorem ext_mul {Gr Γ W K : Type} [Group Gr] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* Gr} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gr} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι S σ ρ J χ) (f : S.Forms) (g : Gr) (k : J) (hk : χ k = 1) : P.ext f.1 (g * k) = P.ext f.1 g := by
  have h2 := (GlobalTheory.classPres_basic ι S σ ρ J χ P).1 f 1 g k
  rwa [map_one, map_one, one_mul, one_apply_eq_self, hk, Units.val_one, one_smul] at h2

theorem csum_adj {Gr Γ W K : Type} [Group Gr] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* Gr} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gr} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (Gr → W)) (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y))
    (jm : S.Forms → M.H) (hj : ∀ f, M.e (jm f) = P.ext f.1) (U : Module.End K S.Forms) (u : Module.End ℂ M.H)
    (hu : LinearMap.adjoint u = u) (hU : ∀ f, jm (U f) = u (jm f)) (f g : S.Forms) :
    S.csum (U f).1 g.1 = S.csum f.1 (U g).1 := by
  have hin : ∀ f g : S.Forms, inner ℂ (jm f) (jm g) = σ (S.csum f.1 g.1) := by
    intro f g
    rw [hM.2.2, hj, hj]
    exact (GlobalTheory.classPres_basic ι S σ ρ J χ P).2.1 f g
  apply σ.injective
  rw [← hin, ← hin, hU, hU, ← LinearMap.adjoint_inner_right, hu]

theorem tie_label {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : LevDat D.host.E ℂ V.rank) (hβ : IsSDFrame V β Λ 1) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : GQ V →* Module.End ℂ W} {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} {S : CSD K}
    (Pr : Bridge.ClassPres (Bridge.ratF V) S σ ρ (levEnv V β L).J (levEnv V β L).χ) {I : Type} {pl : I → Pl D.host.E}
    {ty : I → List ℤ} {op : I → Module.End K S.Forms} {inR : I → Prop}
    (Comparison₂ : Bridge.HeckeTie (Bridge.ratF V) Pr op inR (fun i => IsLabElt V (pl i) (ty i)) (fun i => IsLocElt V (pl i)))
    (i : I) (hi : inR i) (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ pl i ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i))
    (hpw : (ty i).Pairwise (fun a b => b ≤ a)) :
    IsLab V (pl i) (ty i) ∧ ∀ f : S.Forms, Pr.ext (op i f).1 = hkF V (pl i) (Finsupp.single (ty i) 1) (Pr.ext f.1) := by
  obtain ⟨c, hc⟩ := hβ
  rw [one_pow] at hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ (pl i).asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 (pl i).isPrime.ne_top
  have hd := GlobalTheory.T.doubleCosetOperator_eq_labelOperator_localReps V β Λ 1 L hc (pl i) h1 hoff (ty i) (Comparison₂.hx i) (Comparison₂.hA i) hpw
    (Comparison₂.hx_ok i hi) (Comparison₂.hA_loc i hi) (Comparison₂.hDC i hi)
  exact ⟨hd.1, fun f => (Comparison₂.op_eq i hi f).trans (hd.2 W _ fun g k hk => ext_mul Pr f g k (Comparison₂.chi_loc i hi k hk))⟩

theorem inert_lifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → ∀ j t, ∀ (I : Type) (pl : I → Pl D.host.E) (ty : I → List ℤ) (op : I → Module.End D.what₂.LL (A.MtCSD j t).Forms) (inR : I → Prop), (∀ i, inR i → Good R t (pl i) ∧ conjPl (pl i) = pl i ∧ (ty i).Pairwise (fun a b => b ≤ a)) → Bridge.HeckeTie (Bridge.ratF (Vc D j)) (R.B.L j t).pres op inR (fun i => IsLabElt (Vc D j) (pl i) (ty i)) (fun i => IsLocElt (Vc D j) (pl i)) → ∀ i, inR i → (∀ a b, LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis (op i) a b ∈ cmMax D.what₂.LL) ∧ (∀ f g : (A.MtCSD j t).Forms, (A.MtCSD j t).csum ((op i f : (A.MtCSD j t).Forms) : (A.MtCSD j t).Cl → (A.MtCSD j t).V) (g : (A.MtCSD j t).Cl → (A.MtCSD j t).V) = (A.MtCSD j t).csum (f : (A.MtCSD j t).Cl → (A.MtCSD j t).V) ((op i g : (A.MtCSD j t).Forms) : (A.MtCSD j t).Cl → (A.MtCSD j t).V)) ∧ IsLab (Vc D j) (pl i) (ty i) ∧ ∀ h, IsOpsV R j t h → ∀ f, R.jV j t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jV j t f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF hM j t I pl ty op inR hin Comparison₂ i hi
  have hgood := (hin i hi).1
  have hd := tie_label (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j t) (hL.βV j) (R.B.L j t).pres Comparison₂ i hi hgood (hin i hi).2.2
  have hj : ∀ f : (A.MtCSD j t).Forms, (R.HV j t).e (R.jV j t f) = (R.B.L j t).pres.ext f.1 := fun f => hM.jV j t f
  have hint : ∀ h, IsOpsV R j t h → ∀ f, R.jV j t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jV j t f) :=
    fun h hh f => (hM.HV j t).1 (((hj _).trans (hd.2 f)).trans
      ((congrArg (hkF (Vc D j) (pl i) (Finsupp.single (ty i) 1)) (hj f).symm).trans (hh (pl i) hgood _ _).symm))
  have hrat : ∀ a b, LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis (op i) a b ∈ cmMax D.what₂.LL := by
    obtain ⟨_, _, _, hT⟩ := hF.tie
    open GlobalTheory.HeckeRational in
    exact (dcOp_matrix_mem_cmMax (Vc D j) (R.cV j).coef (R.βV j) (R.datVt j t) (R.B.L j t).pres
      (hT.coefL j t) (hT.mapL j) (fun g a b => (coefAction_repr_mem_subfield (labLL D) _ _ labLL_mem_cmMax g a b).2)
      (Comparison₂.hA i) (op i) (Comparison₂.op_eq i hi)).2
  refine ⟨hrat, ?_, hd.1, hint⟩
  have hnormal : ∃ h, IsOpsV R j t h ∧ NormalFam (Good R t) h :=
    GlobalTheory.DefiniteOps.side (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j t) (hL.βV j) (Good R t)
      (fun _ h => h) (R.cV j).coef.ρ (fun γ => (hM.cV j).2.1 γ) (R.B.L j t).pres.y (R.B.L j t).pres.reps
      (fun c => Finite.of_equiv _ ((R.B.L j t).pres.stabI c).toEquiv) (R.HV j t) (hM.HV j t)
  obtain ⟨h, hh⟩ := hnormal
  have hdual : dualLab (ty i) = ty i := ((GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing (Vc D j) (pl i) (ty i)).1 hd.1).2.2 (hin i hi).2.1
  have hadj := (hh.2.2 (pl i) hgood (Finsupp.single (ty i) 1)).trans (congrArg (h (pl i)) (dualC_single hdual))
  exact csum_adj (R.B.L j t).pres (R.HV j t) (hM.HV j t) (fun f => R.jV j t f) hj (op i) _ hadj (hint h hh.1)

end GlobalTheory.InertHeckeLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsLiftsRationalSelfAdjointLabelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3 hiding IsLabElt IsLocElt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperators_lifts_rational_selfAdjoint_labels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → ∀ j t, ∀ (I : Type) (pl : I → Pl D.host.E) (ty : I → List ℤ) (op : I → Module.End D.what₂.LL (A.MtCSD j t).Forms) (inR : I → Prop), (∀ i, inR i → Good R t (pl i) ∧ conjPl (pl i) = pl i ∧ (ty i).Pairwise (fun a b => b ≤ a)) → Bridge.HeckeTie (Bridge.ratF (Vc D j)) (R.B.L j t).pres op inR (fun i => IsLabElt (Vc D j) (pl i) (ty i)) (fun i => IsLocElt (Vc D j) (pl i)) → ∀ i, inR i → (∀ a b, LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis (op i) a b ∈ cmMax D.what₂.LL) ∧ (∀ f g : (A.MtCSD j t).Forms, (A.MtCSD j t).csum ((op i f : (A.MtCSD j t).Forms) : (A.MtCSD j t).Cl → (A.MtCSD j t).V) (g : (A.MtCSD j t).Cl → (A.MtCSD j t).V) = (A.MtCSD j t).csum (f : (A.MtCSD j t).Cl → (A.MtCSD j t).V) ((op i g : (A.MtCSD j t).Forms) : (A.MtCSD j t).Cl → (A.MtCSD j t).V)) ∧ IsLab (Vc D j) (pl i) (ty i) ∧ ∀ h, IsOpsV R j t h → ∀ f, R.jV j t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jV j t f) := by
  first | exact @GlobalTheory.InertHeckeLift.inert_lifts | exact GlobalTheory.InertHeckeLift.inert_lifts | (intros; apply GlobalTheory.InertHeckeLift.inert_lifts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsRowsRationalSelfAdjointLabels
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsRowsRationalSelfAdjointLabels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3 hiding IsLabElt IsLocElt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertRows

theorem ext_right_inv {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
    [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G)
    (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ) (f : S.Forms) (g : G) (k : J) (hk : χ k = 1) :
    P.ext f (g * k) = P.ext f g := by
  have := (GlobalTheory.classPres_basic ι S σ ρ J χ P).1 f 1 g k
  rwa [hk, map_one, map_one, one_mul, Module.End.one_apply, Units.val_one, one_smul] at this

theorem ext_op_eq {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : LevDat D.host.E ℂ V.rank) (hβ : IsSDFrame V β Λ 1) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : GQ V →* Module.End ℂ W) {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K)
    (Pr : Bridge.ClassPres (Bridge.ratF V) S σ ρ (levEnv V β L).J (levEnv V β L).χ)
    {I : Type} (pl : I → Pl D.host.E) (ty : I → List ℤ) (op : I → Module.End K S.Forms) (inR : I → Prop)
    (HT : Bridge.HeckeTie (Bridge.ratF V) Pr op inR (fun i => IsLabElt V (pl i) (ty i)) (fun i => IsLocElt V (pl i)))
    (i : I) (hi : inR i) (hgood : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ pl i ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i))
    (hpw : (ty i).Pairwise (fun a b => b ≤ a)) :
    IsLab V (pl i) (ty i) ∧ ∀ f : S.Forms, Pr.extL (op i f) = hkF V (pl i) (Finsupp.single (ty i) 1) (Pr.extL f) := by
  refine hβ.elim fun c hc => ?_
  have hc' : IsBaseFrame V β Λ 1 := (one_pow c : (1 : ℕ) ^ c = 1) ▸ hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ (pl i).asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 (pl i).isPrime.ne_top
  have hd := GlobalTheory.T.doubleCosetOperator_eq_labelOperator_localReps V β Λ 1 L hc' (pl i) h1 hgood (ty i) (HT.hx i) (HT.hA i) hpw
    (HT.hx_ok i hi) (HT.hA_loc i hi) (HT.hDC i hi)
  exact ⟨hd.1, fun f => (HT.op_eq i hi f).trans (hd.2 W (Pr.ext f) fun g k hk =>
    ext_right_inv _ S σ ρ _ _ Pr f g k (HT.chi_loc i hi k hk))⟩

theorem csum_selfAdj {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
    [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G)
    (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (G → W))
    (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) (j : S.Forms → M.H) (hj : ∀ x, M.e (j x) = P.extL x)
    (U : Module.End K S.Forms) (u : Module.End ℂ M.H) (hu : LinearMap.adjoint u = u) (hU : ∀ f, j (U f) = u (j f))
    (f g : S.Forms) :
    S.csum ((U f : S.Forms) : S.Cl → S.V) (g : S.Cl → S.V) = S.csum (f : S.Cl → S.V) ((U g : S.Forms) : S.Cl → S.V) := by
  have hs : ∀ f g : S.Forms, inner ℂ (j f) (j g) = σ (S.csum (f : S.Cl → S.V) (g : S.Cl → S.V)) := by
    intro f g
    rw [hM.2.2, hj, hj]
    exact (GlobalTheory.classPres_basic ι S σ ρ J χ P).2.1 f g
  apply σ.injective
  rw [← hs, ← hs, hU, hU, ← LinearMap.adjoint_inner_right, hu]

theorem dualC_single {d : List ℤ} (h : dualLab d = d) :
    dualC (Finsupp.mapRange star (star_zero ℂ) (Finsupp.single d (1 : ℂ))) = Finsupp.single d 1 := by
  rw [Finsupp.mapRange_single, star_one, dualC, Finsupp.mapDomain_single, h]

theorem inert_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → ∀ t, ∀ (I : Type) (pl : I → Pl D.host.E) (ty : I → List ℤ) (op : I → Module.End D.what₂.LL (A.MtildeCSD t).Forms) (inR : I → Prop), (∀ i, inR i → Good R t (pl i) ∧ conjPl (pl i) = pl i ∧ (ty i).Pairwise (fun a b => b ≤ a)) → Bridge.HeckeTie (Bridge.ratF D.sp.X') (R.B.R t).pres op inR (fun i => IsLabElt D.sp.X' (pl i) (ty i)) (fun i => IsLocElt D.sp.X' (pl i)) → ∀ i, inR i → (∀ a b, LinearMap.toMatrix (A.MtildeCSD t).basis (A.MtildeCSD t).basis (op i) a b ∈ cmMax D.what₂.LL) ∧ (∀ f g : (A.MtildeCSD t).Forms, (A.MtildeCSD t).csum ((op i f : (A.MtildeCSD t).Forms) : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V) (g : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V) = (A.MtildeCSD t).csum (f : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V) ((op i g : (A.MtildeCSD t).Forms) : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V)) ∧ IsLab D.sp.X' (pl i) (ty i) ∧ ∀ h, IsOpsX R t h → ∀ f, R.jX t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jX t f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF hM t I pl ty op inR hin HT i hi
  have hgood := (hin i hi).1
  have hconj := (hin i hi).2.1
  have hpw := (hin i hi).2.2
  have hd := ext_op_eq D.sp.X' R.βX R.ΛX (R.datXt t) hL.βX R.cX.coef.ρ D.what₂.embLL (A.MtildeCSD t) (R.B.R t).pres
    pl ty op inR HT i hi hgood hpw
  have hint : ∀ h, IsOpsX R t h → ∀ f, R.jX t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jX t f) := by
    intro h hh f
    refine (hM.HX t).1 ?_
    refine (hM.jX t _).trans (Eq.trans ?_ (hh (pl i) hgood _ _).symm)
    exact (hd.2 f).trans (congrArg (hkF D.sp.X' (pl i) (Finsupp.single (ty i) 1)) (hM.jX t f).symm)
  refine ⟨fun a b => GlobalTheory.HeckeRational.rows_dcOp_mem_cmMax R hF.tie t _ _ (HT.op_eq i hi) a b, fun f g => ?_, hd.1, hint⟩
  refine ((GlobalTheory.T.realization_family_normal_operators R F hL hF hM).1 t).elim fun h hh => ?_
  have hdual : dualLab (ty i) = ty i := ((GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing D.sp.X' (pl i) (ty i)).1 hd.1).2.2 hconj
  have hadj := (hh.2.2 (pl i) hgood (Finsupp.single (ty i) 1)).trans (congrArg (h (pl i)) (dualC_single hdual))
  exact csum_selfAdj (Bridge.ratF D.sp.X') (A.MtildeCSD t) D.what₂.embLL R.cX.coef.ρ _ _ (R.B.R t).pres (R.HX t) (hM.HX t)
    (R.jX t) (hM.jX t) (op i) _ hadj (hint h hh.1) f g

end GlobalTheory.InertRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsRowsRationalSelfAdjointLabelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3 hiding IsLabElt IsLocElt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → ∀ t, ∀ (I : Type) (pl : I → Pl D.host.E) (ty : I → List ℤ) (op : I → Module.End D.what₂.LL (A.MtildeCSD t).Forms) (inR : I → Prop), (∀ i, inR i → Good R t (pl i) ∧ conjPl (pl i) = pl i ∧ (ty i).Pairwise (fun a b => b ≤ a)) → Bridge.HeckeTie (Bridge.ratF D.sp.X') (R.B.R t).pres op inR (fun i => IsLabElt D.sp.X' (pl i) (ty i)) (fun i => IsLocElt D.sp.X' (pl i)) → ∀ i, inR i → (∀ a b, LinearMap.toMatrix (A.MtildeCSD t).basis (A.MtildeCSD t).basis (op i) a b ∈ cmMax D.what₂.LL) ∧ (∀ f g : (A.MtildeCSD t).Forms, (A.MtildeCSD t).csum ((op i f : (A.MtildeCSD t).Forms) : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V) (g : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V) = (A.MtildeCSD t).csum (f : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V) ((op i g : (A.MtildeCSD t).Forms) : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V)) ∧ IsLab D.sp.X' (pl i) (ty i) ∧ ∀ h, IsOpsX R t h → ∀ f, R.jX t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jX t f) := by
  exact @_root_.GlobalTheory.InertRows.inert_rows
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemISupTypePartsOfGoodBaseForms
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemISupTypePartsOfGoodBaseForms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3 hiding IsLabElt IsLocElt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwParts

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL]

theorem mk_bC_mem_range (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m)
    (k : Fin ((R.toCx3 F).dW false j)) :
    Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.toRealDat.bC F.lv2 false j (sg0 D A3.A) k) ∈
      LinearMap.range ((R.toCx3 F).w0C false j) := by
  have hpos : (0 : ℝ) < Real.sqrt (RealDat.nP F.lv2 false) := Real.sqrt_pos.mpr (RealDat.nP_pos (F := F.lv2) false)
  refine ⟨Pi.single k ((((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ)), ?_⟩
  simp only [CxData.w0C, CxData.wC, lin, LinearMap.comp_apply, Fintype.linearCombination_apply_single]
  rw [LinearMap.map_smul]
  show Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW j (sg0 D A3.A)).H) (_ • _) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW j (sg0 D A3.A)).H) (Tw.mk _ _)
  erw [Tw.out_smul, cj_ofReal]
  show ((((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ)) • ((((Real.sqrt (RealDat.nP F.lv2 false)) : ℝ) : ℂ) • R.toRealDat.bC F.lv2 false j (sg0 D A3.A) k) = R.toRealDat.bC F.lv2 false j (sg0 D A3.A) k
  rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one, one_smul]

end GlobalTheory.TwParts

open GlobalTheory.TwParts in
theorem GlobalTheory.TwParts.mem_iSup_Wp3_of_mem_WS : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), (R.toCx3 F).PartsW false → ∀ j (w : (R.HW j (sg0 D A3.A)).H), w ∈ R.toRealDat.WS F.lv2 false j (sg0 D A3.A) → w ∈ ⨆ p, R.Wp3 j p := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hP j w hw
  obtain ⟨-, hsup⟩ := hP j
  refine Submodule.span_le.mpr ?_ hw
  rintro _ ⟨k, rfl⟩
  have hk := mk_bC_mem_range R F j k
  rw [← hsup] at hk
  have hk' : Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.toRealDat.bC F.lv2 false j (sg0 D A3.A) k) ∈
      ⨆ p, (R.toCx3 F).Wp j p := by
    have hle : (⨆ p, (R.toCx3 F).Wp j p ⊓ LinearMap.range ((R.toCx3 F).w0C false j)) ≤ ⨆ p, (R.toCx3 F).Wp j p :=
      iSup_mono fun p => inf_le_left
    exact hle hk
  refine Submodule.iSup_induction (fun p => (R.toCx3 F).Wp j p) (motive := fun x => Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW j (sg0 D A3.A)).H) x ∈ ⨆ p, R.Wp3 j p) hk' ?_ ?_ ?_
  · intro p x hx
    exact Submodule.mem_iSup_of_mem p hx
  · exact Submodule.zero_mem _
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemISupTypePartsOfGoodBaseFormsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3 hiding IsLabElt IsLocElt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_iSup_type_parts_of_good_base_forms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), (R.toCx3 F).PartsW false → ∀ j (w : (R.HW j (sg0 D A3.A)).H), w ∈ R.toRealDat.WS F.lv2 false j (sg0 D A3.A) → w ∈ ⨆ p, R.Wp3 j p := by
  first | exact @GlobalTheory.TwParts.mem_iSup_Wp3_of_mem_WS | exact GlobalTheory.TwParts.mem_iSup_Wp3_of_mem_WS | (intros; apply GlobalTheory.TwParts.mem_iSup_Wp3_of_mem_WS <;> assumption)
end
end
