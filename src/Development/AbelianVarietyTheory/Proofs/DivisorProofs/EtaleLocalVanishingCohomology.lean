module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcycFOfPiSh

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ContrAtEqComapMap
namespace GlobalTheory.LocalSaturationContraction

variable {B : Type*} [CommRing B]

def satAt (b : B) (P : Ideal B) [hP : P.IsPrime] : Ideal B where
  carrier := {x | ∃ s, s ∉ P ∧ s * x ∈ Ideal.span {b}}
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one P).1 hP.ne_top, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
    have : s * t * (x + y) = t * (s * x) + s * (t * y) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_left _ _ hy)
  smul_mem' := by
    rintro c x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    have : s * (c • x) = c * (s * x) := by rw [smul_eq_mul]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hx

variable (b : B) (P : Ideal B) [P.IsPrime]

end GlobalTheory.LocalSaturationContraction
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DedekindPowerLocalization
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLocalContinuousCongruenceSection
namespace GlobalTheory

theorem dedekind_pow_maximal_mul_mem_span (B : Type) [CommRing B] [IsDedekindDomain B] (f : B)
    (hf : f ≠ 0) (P : Ideal B) (hP : P.IsMaximal) :
    ∃ N : ℕ, ∀ b ∈ P ^ N, ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  classical
  have hI0 : Ideal.span {f} ≠ (0 : Ideal B) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hf
  have hPu : ¬ IsUnit P := by
    rw [Ideal.isUnit_iff]; exact hP.ne_top
  have hfin : FiniteMultiplicity P (Ideal.span {f}) := FiniteMultiplicity.of_not_isUnit hPu hI0
  have key : ¬ P ^ (multiplicity P (Ideal.span {f}) + 1) ∣ Ideal.span {f} :=
    hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  have hdvd : P ^ (multiplicity P (Ideal.span {f})) ∣ Ideal.span {f} := pow_multiplicity_dvd P _
  generalize multiplicity P (Ideal.span {f}) = m at key hdvd
  obtain ⟨J, hJ⟩ := hdvd
  refine ⟨m, ?_⟩
  have hJP : ¬ J ≤ P := by
    intro hle
    have hd : P ∣ J := Ideal.dvd_iff_le.mpr hle
    apply key
    rw [hJ, pow_succ]
    exact mul_dvd_mul_left _ hd
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.mp hJP
  intro b hb
  refine ⟨s, hsP, ?_⟩
  have hmem : b * s ∈ P ^ m * J := Ideal.mul_mem_mul hb hsJ
  rw [← hJ] at hmem
  rw [mul_comm]
  exact hmem

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dedekind_power_localization : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B), f ≠ 0 → ∀ (P : Ideal B), P.IsMaximal → ∃ N : ℕ, ∀ b ∈ P ^ N, ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.dedekind_pow_maximal_mul_mem_span) | (exact GlobalTheory.dedekind_pow_maximal_mul_mem_span) | (intros; apply GlobalTheory.dedekind_pow_maximal_mul_mem_span <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproximationQuotientsAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsIntegrallyEquivalentAlmostAll
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.ProdStep

theorem mem_span_prod {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] (a₁ : A₁) (a₂ : A₂) (x : A₁ × A₂) :
    x ∈ Ideal.span {((a₁, a₂) : A₁ × A₂)} ↔ x.1 ∈ Ideal.span {a₁} ∧ x.2 ∈ Ideal.span {a₂} := by
  simp only [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨⟨c.1, rfl⟩, ⟨c.2, rfl⟩⟩
  · rintro ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩
    exact ⟨(c₁, c₂), Prod.ext h₁ h₂⟩

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Functor.map_comp, ← Spec.map_comp]

theorem prodStep : ∀ (q : ℕ) (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂] (f : B) (I J : Ideal B) (n i : ℤ) (y : Ht q (sp B) n i), IsCoprime I J → (∀ a : A₁, ∃ b : B, a - algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f}) → (∀ b : B, algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f} ↔ b ∈ I) → (∀ a : A₂, ∃ b : B, a - algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f}) → (∀ b : B, algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f} ↔ b ∈ J) → pull _ (spMap (algebraMap B A₁)) _ _ y = 0 → pull _ (spMap (algebraMap B A₂)) _ _ y = 0 → (∀ a : A₁ × A₂, ∃ b : B, a - algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f}) ∧ (∀ b : B, algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f} ↔ b ∈ I ⊓ J) ∧ pull _ (spMap (algebraMap B (A₁ × A₂))) _ _ y = 0 := by
  intro q B A₁ A₂ _ _ _ _ _ f I J n i y hIJ hs₁ hk₁ hs₂ hk₂ hy₁ hy₂
  have hf : algebraMap B (A₁ × A₂) f = (algebraMap B A₁ f, algebraMap B A₂ f) := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro a
    obtain ⟨u, hu, v, hv, huv⟩ := Ideal.isCoprime_iff_exists.1 hIJ
    obtain ⟨b₁, hb₁⟩ := hs₁ a.1
    obtain ⟨b₂, hb₂⟩ := hs₂ a.2
    refine ⟨b₁ * v + b₂ * u, ?_⟩
    rw [hf, mem_span_prod]
    constructor
    · have e : a.1 - algebraMap B A₁ (b₁ * v + b₂ * u) = (a.1 - algebraMap B A₁ b₁) + algebraMap B A₁ ((b₁ - b₂) * u) := by
        have : b₁ * v + b₂ * u = b₁ - (b₁ - b₂) * u := by linear_combination b₁ * huv
        rw [this, map_sub]; ring
      show a.1 - algebraMap B A₁ (b₁ * v + b₂ * u) ∈ _
      rw [e]
      exact Ideal.add_mem _ hb₁ ((hk₁ _).2 (I.mul_mem_left _ hu))
    · have e : a.2 - algebraMap B A₂ (b₁ * v + b₂ * u) = (a.2 - algebraMap B A₂ b₂) + algebraMap B A₂ ((b₂ - b₁) * v) := by
        have : b₁ * v + b₂ * u = b₂ - (b₂ - b₁) * v := by linear_combination b₂ * huv
        rw [this, map_sub]; ring
      show a.2 - algebraMap B A₂ (b₁ * v + b₂ * u) ∈ _
      rw [e]
      exact Ideal.add_mem _ hb₂ ((hk₂ _).2 (J.mul_mem_left _ hv))
  · intro b
    rw [hf, mem_span_prod, Ideal.mem_inf]
    exact and_congr (hk₁ b) (hk₂ b)
  · have hbij := GlobalTheory.EtC.ProdCoh.ht_prod_bijective q A₁ A₂ n i
    apply hbij.1
    have e₁ : (RingHom.fst A₁ A₂).comp (algebraMap B (A₁ × A₂)) = algebraMap B A₁ := by ext; rfl
    have e₂ : (RingHom.snd A₁ A₂).comp (algebraMap B (A₁ × A₂)) = algebraMap B A₂ := by ext; rfl
    simp only [map_zero]
    rw [← pull_comp, ← pull_comp, ← spMap_comp, ← spMap_comp, e₁, e₂, hy₁, hy₂]

end GlobalTheory.EtC.ProdStep
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approximation_quotients_agree : ∀ (q : ℕ) (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂] (f : B) (I J : Ideal B) (n i : ℤ) (y : Ht q (sp B) n i), IsCoprime I J → (∀ a : A₁, ∃ b : B, a - algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f}) → (∀ b : B, algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f} ↔ b ∈ I) → (∀ a : A₂, ∃ b : B, a - algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f}) → (∀ b : B, algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f} ↔ b ∈ J) → pull _ (spMap (algebraMap B A₁)) _ _ y = 0 → pull _ (spMap (algebraMap B A₂)) _ _ y = 0 → (∀ a : A₁ × A₂, ∃ b : B, a - algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f}) ∧ (∀ b : B, algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f} ↔ b ∈ I ⊓ J) ∧ pull _ (spMap (algebraMap B (A₁ × A₂))) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.ProdStep.prodStep) | (exact GlobalTheory.EtC.ProdStep.prodStep) | (intros; apply GlobalTheory.EtC.ProdStep.prodStep  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAwayQuotientEqLocalization
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationInverseModF
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFiberMeasuresUniqueAe
namespace GlobalTheory

theorem unitsMod_away_of_unique_prime (B D : Type) [CommRing B] [CommRing D] [Algebra B D]
    (f : B) (P : Ideal B) (Q : Ideal D) (g : D)
    (hQP : Q.comap (algebraMap B D) = P)
    (huniq : ∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q) :
    ∀ s : B, s ∉ P → ∃ t : Localization.Away g,
      algebraMap B (Localization.Away g) s * t - 1 ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
  intro s hs
  set A := Localization.Away g
  by_cases hI : Ideal.span {algebraMap B A s, algebraMap B A f} = ⊤
  · have h1 : (1 : A) ∈ Ideal.span {algebraMap B A s, algebraMap B A f} := by
      rw [hI]; exact Submodule.mem_top
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp h1
    refine ⟨a, ?_⟩
    have : algebraMap B A s * a - 1 = (-b) * algebraMap B A f := by
      rw [← hab]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · exfalso
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hI
    have hMp : (M.comap (algebraMap D A)).IsPrime := Ideal.comap_isPrime _ _
    have hf : algebraMap B D f ∈ M.comap (algebraMap D A) := by
      rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact hIM (Ideal.subset_span (by simp))
    have hg : g ∉ M.comap (algebraMap D A) := by
      intro hgM
      rw [Ideal.mem_comap] at hgM
      exact hM.ne_top (Ideal.eq_top_of_isUnit_mem _ hgM
        (IsLocalization.Away.algebraMap_isUnit g))
    have hEq := huniq _ hMp hf hg
    apply hs
    rw [← hQP, Ideal.mem_comap, ← hEq, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact hIM (Ideal.subset_span (by simp))

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_inverse_mod_f : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (f : B) (P : Ideal B) (Q : Ideal D) (g : D), Q.comap (algebraMap B D) = P → (∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q) → ∀ s : B, s ∉ P → ∃ t : Localization.Away g, algebraMap B (Localization.Away g) s * t - 1 ∈ Ideal.span {algebraMap B (Localization.Away g) f} := by
  first | (exact @GlobalTheory.unitsMod_away_of_unique_prime) | (exact GlobalTheory.unitsMod_away_of_unique_prime) | (intros; apply GlobalTheory.unitsMod_away_of_unique_prime <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLocalizationMembership
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorInvolutionAlgebraProperties
namespace GlobalTheory

open IsLocalization in
theorem localFlat_dvd_descends : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] [Module.Flat B D] (Q : Ideal D) [Q.IsPrime] (f b : B), algebraMap B (Localization.AtPrime Q) b ∈ Ideal.span {algebraMap B (Localization.AtPrime Q) f} → ∃ s : B, s ∉ Q.comap (algebraMap B D) ∧ s * b ∈ Ideal.span {f} := by
  intro B D _ _ _ _ Q _ f b h
  set P : Ideal B := Q.comap (algebraMap B D) with hP
  let φ : Localization.AtPrime P →+* Localization.AtPrime Q :=
    Localization.localRingHom P Q (algebraMap B D) rfl
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) := φ.toAlgebra
  have hφ : ∀ x : B, φ (algebraMap B (Localization.AtPrime P) x) = algebraMap B (Localization.AtPrime Q) x := by
    intro x
    simp [φ, Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply B D (Localization.AtPrime Q)]
  have hfl : φ.Flat := RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) Q P rfl
  haveI : Module.Flat (Localization.AtPrime P) (Localization.AtPrime Q) := hfl
  haveI : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) :=
    (inferInstance : IsLocalHom φ)
  haveI : Module.FaithfullyFlat (Localization.AtPrime P) (Localization.AtPrime Q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have key : algebraMap B (Localization.AtPrime P) b ∈
      (Ideal.span {f}).map (algebraMap B (Localization.AtPrime P)) := by
    rw [Ideal.map_span, Set.image_singleton,
      ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Localization.AtPrime Q)
        (Ideal.span {algebraMap B (Localization.AtPrime P) f}), Ideal.mem_comap,
      Ideal.map_span, Set.image_singleton]
    change φ _ ∈ Ideal.span {φ _}
    rw [hφ, hφ]; exact h
  obtain ⟨s, hs, h2⟩ := (algebraMap_mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P) _ b).1 key
  exact ⟨s, hs, h2⟩

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_localization_membership : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] [Module.Flat B D] (Q : Ideal D) [Q.IsPrime] (f b : B), algebraMap B (Localization.AtPrime Q) b ∈ Ideal.span {algebraMap B (Localization.AtPrime Q) f} → ∃ s : B, s ∉ Q.comap (algebraMap B D) ∧ s * b ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.localFlat_dvd_descends) | (exact GlobalTheory.localFlat_dvd_descends) | (intros; apply GlobalTheory.localFlat_dvd_descends <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationResidueApproximation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveVectorQuadraticLevelMeasure
namespace GlobalTheory

theorem residue_surj_localizationAway : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (P : Ideal B), P.IsMaximal → ∀ (Q : Ideal D) (g : D), g ∉ Q → Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) → ∀ a : Localization.Away g, ∃ b : B, a - algebraMap B (Localization.Away g) b ∈ Q.map (algebraMap D (Localization.Away g)) := by
  intro B D _ _ _ P hP Q g hg hQP hsurj a
  obtain ⟨⟨d, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) a
  obtain ⟨n, hn⟩ := s.2
  obtain ⟨bd, hbd⟩ := hsurj d
  obtain ⟨bg, hbg⟩ := hsurj g
  have hbgP : bg ∉ P := by
    intro h
    rw [← hQP, Ideal.mem_comap] at h
    exact hg (by simpa using Q.add_mem hbg h)
  obtain ⟨c, i, hi, hci⟩ := hP.exists_inv hbgP
  have hcg : algebraMap B D c * g - 1 ∈ Q := by
    have hiQ : algebraMap B D i ∈ Q := by rw [← hQP] at hi; exact hi
    have e : algebraMap B D c * g - 1 = algebraMap B D c * (g - algebraMap B D bg) - algebraMap B D i := by
      have := congrArg (algebraMap B D) hci
      simp only [map_add (f := _), map_mul, map_one] at this
      linear_combination this
    rw [e]
    exact Q.sub_mem (Q.mul_mem_left _ hbg) hiQ
  refine ⟨bd * c ^ n, ?_⟩
  have key : d - algebraMap B D (bd * c ^ n) * (s : D) ∈ Q := by
    rw [← hn]
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hcg hbd ⊢
    simp only [map_sub, map_mul, map_pow, map_one, sub_eq_zero] at hcg hbd ⊢
    rw [hbd, mul_assoc, ← mul_pow, hcg, one_pow, mul_one]
  set L := Localization.Away g
  have hspec : algebraMap D L (s : D) * IsLocalization.mk' L (1 : D) s = 1 := by
    rw [IsLocalization.mk'_spec', map_one]
  have e : IsLocalization.mk' L d s - algebraMap B L (bd * c ^ n)
      = algebraMap D L (d - algebraMap B D (bd * c ^ n) * (s : D)) * IsLocalization.mk' L (1 : D) s := by
    rw [IsScalarTower.algebraMap_apply B D L, IsLocalization.mk'_eq_mul_mk'_one, map_sub, map_mul (algebraMap D L)]
    linear_combination (algebraMap D L (algebraMap B D (bd * c ^ n))) * hspec
  rw [e]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ key)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_residue_approximation : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (P : Ideal B), P.IsMaximal → ∀ (Q : Ideal D) (g : D), g ∉ Q → Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) → ∀ a : Localization.Away g, ∃ b : B, a - algebraMap B (Localization.Away g) b ∈ Q.map (algebraMap D (Localization.Away g)) := by
  first | (exact @GlobalTheory.residue_surj_localizationAway) | (exact GlobalTheory.residue_surj_localizationAway) | (intros; apply GlobalTheory.residue_surj_localizationAway <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentApproximationSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHermitianDiagonalizationUnits
namespace GlobalTheory

theorem surj_mod_of_surj_mod_map_sup_of_pow_map_le :
    ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (I : Ideal B) (K : Ideal A) (N : ℕ),
      (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ I.map (algebraMap B A) ⊔ K) →
      (I ^ N).map (algebraMap B A) ≤ K → ∀ a : A, ∃ b : B, a - algebraMap B A b ∈ K := by
  intro B A _ _ _ I K N hsurj hN
  set f := algebraMap B A with hf
  set J := I.map f with hJ

  have key : ∀ n : ℕ, ∀ a : A, ∃ b : B, a - f b ∈ J ^ n ⊔ K := by
    intro n
    induction n with
    | zero =>
      intro a
      exact ⟨0, by simp⟩
    | succ n ih =>

      have hspan : ∀ x ∈ J ^ n, ∀ c : A, ∃ b : B, c * x - f b ∈ J ^ (n + 1) ⊔ K := by
        intro x hx
        rw [hJ, ← Ideal.map_pow] at hx
        unfold Ideal.map at hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨i, hi, rfl⟩ := hx
          intro c
          obtain ⟨b', hb'⟩ := hsurj c
          obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hb'
          refine ⟨b' * i, ?_⟩
          have hfi : f i ∈ J ^ n := by
            rw [hJ, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hi
          have hc : c = f b' + y + z := by rw [add_assoc, hyz]; ring
          have e : c * f i - f (b' * i) = f i * y + z * f i := by
            rw [hc, map_mul]; ring
          rw [e]
          refine Submodule.add_mem_sup ?_ (K.mul_mem_right _ hz)
          rw [pow_succ]
          exact Ideal.mul_mem_mul hfi hy
        | zero =>
          intro c; exact ⟨0, by simp⟩
        | add x y _ _ hx hy =>
          intro c
          obtain ⟨b1, h1⟩ := hx c
          obtain ⟨b2, h2⟩ := hy c
          refine ⟨b1 + b2, ?_⟩
          have e : c * (x + y) - f (b1 + b2) = (c * x - f b1) + (c * y - f b2) := by
            rw [map_add (f := _)]; ring
          rw [e]; exact add_mem h1 h2
        | smul d x _ hx =>
          intro c
          obtain ⟨b, h⟩ := hx (c * d)
          refine ⟨b, ?_⟩
          rw [smul_eq_mul, ← mul_assoc]; exact h
      intro a
      obtain ⟨b, hb⟩ := ih a
      obtain ⟨x, hx, k, hk, hxk⟩ := Submodule.mem_sup.mp hb
      obtain ⟨b2, hb2⟩ := hspan x hx 1
      refine ⟨b + b2, ?_⟩
      have e : a - f (b + b2) = (1 * x - f b2) + k := by
        rw [map_add (f := _), one_mul]; linear_combination -hxk
      rw [e]
      refine add_mem hb2 (Submodule.mem_sup_right hk)
  intro a
  obtain ⟨b, hb⟩ := key N a
  refine ⟨b, ?_⟩
  have hle : J ^ N ⊔ K ≤ K := by
    refine sup_le ?_ le_rfl
    rw [hJ, ← Ideal.map_pow]; exact hN
  exact hle hb

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilpotent_approximation_surjective : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (I : Ideal B) (K : Ideal A) (N : ℕ), (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ I.map (algebraMap B A) ⊔ K) → (I ^ N).map (algebraMap B A) ≤ K → ∀ a : A, ∃ b : B, a - algebraMap B A b ∈ K := by
  first | (exact @GlobalTheory.surj_mod_of_surj_mod_map_sup_of_pow_map_le) | (exact GlobalTheory.surj_mod_of_surj_mod_map_sup_of_pow_map_le) | (intros; apply GlobalTheory.surj_mod_of_surj_mod_map_sup_of_pow_map_le <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolateMaximalAmongPrimesContainingEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolateMaximalAmongPrimesContainingEtale
namespace GlobalTheory.EtaleIsolate

theorem primes_above_finite {A : Type*} [CommRing A] (I : Ideal A) [IsArtinianRing (A ⧸ I)] :
    {Q : Ideal A | Q.IsPrime ∧ I ≤ Q}.Finite ∧
      ∀ Q : Ideal A, Q.IsPrime → I ≤ Q → Q.IsMaximal := by
  have key : ∀ Q : Ideal A, Q.IsPrime → I ≤ Q →
      (Q.map (Ideal.Quotient.mk I)).IsPrime ∧
        (Q.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = Q := by
    intro Q hQ hIQ
    have hk : RingHom.ker (Ideal.Quotient.mk I) ≤ Q := by rwa [Ideal.mk_ker]
    refine ⟨Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hk, ?_⟩
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hIQ]
  refine ⟨((IsArtinianRing.setOfPred_isPrime_finite (A ⧸ I)).image
    (Ideal.comap (Ideal.Quotient.mk I))).subset fun Q hQ => ?_, fun Q hQ hIQ => ?_⟩
  · exact ⟨_, (key Q hQ.1 hQ.2).1, (key Q hQ.1 hQ.2).2⟩
  · haveI := (key Q hQ hIQ).1
    have hm := IsArtinianRing.isMaximal_of_isPrime (Q.map (Ideal.Quotient.mk I))
    rw [← (key Q hQ hIQ).2]
    exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective

theorem isArtinianRing_quot_span (B : Type*) [CommRing B] [IsDedekindDomain B] (f : B)
    (hf : f ≠ 0) : IsArtinianRing (B ⧸ Ideal.span {f}) := by
  have hr0 : f ∈ nonZeroDivisors B := mem_nonZeroDivisors_of_ne_zero hf
  haveI : IsArtinian B (B ⧸ Ideal.span {f}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (isFiniteLength_quotient_span_singleton B hr0)).2
  exact isArtinian_of_tower B inferInstance

theorem isArtinianRing_fibre (B D : Type*) [CommRing B] [CommRing D] [Algebra B D]
    [Algebra.Etale B D] (P : Ideal B) [P.IsMaximal] :
    IsArtinianRing (D ⧸ P.map (algebraMap B D)) := by
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Algebra.Etale (B ⧸ P) (D ⧸ P.map (algebraMap B D)) :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor D P).symm
  haveI : Module.Finite (B ⧸ P) (D ⧸ P.map (algebraMap B D)) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  exact IsArtinianRing.of_finite (B ⧸ P) _

theorem exists_isolating (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D]
    [Algebra B D] [Algebra.Etale B D] (f : B) (hf : f ≠ 0) (Q : Ideal D) (hQ : Q.IsMaximal) :
    ∃ g : D, g ∉ Q ∧ ∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q := by
  classical
  haveI := isArtinianRing_quot_span B f hf
  obtain ⟨hBfin, hBmax⟩ := primes_above_finite (Ideal.span {f})
  set S : Set (Ideal D) := {Q' | Q'.IsPrime ∧ algebraMap B D f ∈ Q'} with hS
  set T : Set (Ideal B) := {P | P.IsPrime ∧ Ideal.span {f} ≤ P} with hT
  have hsub : S ⊆ ⋃ P ∈ T, {Q' : Ideal D | Q'.IsPrime ∧ P.map (algebraMap B D) ≤ Q'} := by
    rintro Q' ⟨hQ', hfQ'⟩
    refine Set.mem_biUnion (x := Q'.comap (algebraMap B D)) ⟨Ideal.IsPrime.comap _, ?_⟩
      ⟨hQ', Ideal.map_comap_le⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hfQ'
  have hfib : ∀ P ∈ T, {Q' : Ideal D | Q'.IsPrime ∧ P.map (algebraMap B D) ≤ Q'}.Finite ∧
      ∀ Q' : Ideal D, Q'.IsPrime → P.map (algebraMap B D) ≤ Q' → Q'.IsMaximal := by
    rintro P ⟨hP, hfP⟩
    haveI := hBmax P hP hfP
    haveI := isArtinianRing_fibre B D P
    exact primes_above_finite _
  have hSfin : S.Finite := (hBfin.biUnion fun P hP => (hfib P hP).1).subset hsub
  have hSmax : ∀ Q' ∈ S, Q'.IsMaximal := fun Q' hQ' => by
    obtain ⟨P, hP, hQ'P⟩ := Set.mem_iUnion₂.mp (hsub hQ')
    exact (hfib P hP).2 Q' hQ'P.1 hQ'P.2
  have hch : ∀ Q' ∈ S, Q' ≠ Q → ∃ x, x ∈ Q' ∧ x ∉ Q := fun Q' hQ' hne => by
    by_contra h
    push_neg at h
    exact hne ((hSmax Q' hQ').eq_of_le hQ.ne_top h)
  choose! x hxmem hxnot using hch
  refine ⟨∏ Q' ∈ hSfin.toFinset.filter (· ≠ Q), x Q', ?_, ?_⟩
  · intro h
    haveI := hQ.isPrime
    obtain ⟨Q', hQ', hmem⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hQ'
    exact hxnot Q' hQ'.1 hQ'.2 hmem
  · intro Q' hQ' hfQ' hg
    by_contra hne
    apply hg
    have hmem : Q' ∈ hSfin.toFinset.filter (· ≠ Q) :=
      Finset.mem_filter.2 ⟨hSfin.mem_toFinset.2 ⟨hQ', hfQ'⟩, hne⟩
    rw [← Finset.prod_erase_mul _ _ hmem]
    exact Ideal.mul_mem_left _ _ (hxmem Q' ⟨hQ', hfQ'⟩ hne)

theorem isolate_maximal_among_primes_containing : ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D]
    [Algebra.Etale B D] (f : B), f ≠ 0 → ∀ (Q : Ideal D), Q.IsMaximal →
    ∃ g : D, g ∉ Q ∧ ∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q :=
  fun B D _ _ _ _ _ f hf Q hQ => exists_isolating B D f hf Q hQ

end GlobalTheory.EtaleIsolate
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolateMaximalAmongPrimesContainingEtaleStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isolate_maximal_among_primes_containing_etale : ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D] [Algebra.Etale B D] (f : B), f ≠ 0 → ∀ (Q : Ideal D), Q.IsMaximal → ∃ g : D, g ∉ Q ∧ ∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q := by
  first | (exact @GlobalTheory.EtaleIsolate.isolate_maximal_among_primes_containing) | (exact GlobalTheory.EtaleIsolate.isolate_maximal_among_primes_containing) | (intros; apply GlobalTheory.EtaleIsolate.isolate_maximal_among_primes_containing  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleUniquePrimeLeMapMaximal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleUniquePrimeLeMapMaximal
namespace GlobalTheory

theorem etale_prime_le_map_of_unique (B A : Type) [CommRing B] [CommRing A] [Algebra B A]
    [Algebra.Etale B A] (P : Ideal B) (hP : P.IsMaximal) (Q : Ideal A)
    (hQ : ∀ Q' : Ideal A, Q'.IsPrime → P.map (algebraMap B A) ≤ Q' → Q' = Q) :
    Q ≤ P.map (algebraMap B A) := by
  set I := P.map (algebraMap B A) with hI
  by_cases htop : I = ⊤
  · rw [htop]; exact le_top

  have hrad : I.radical = Q := by
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop
    have hMQ : M = Q := hQ M hM.isPrime hIM
    rw [Ideal.radical_eq_sInf]
    apply le_antisymm
    · exact sInf_le ⟨hMQ ▸ hIM, hMQ ▸ hM.isPrime⟩
    · refine le_sInf ?_
      rintro J ⟨hJ1, hJ2⟩
      exact (hQ J hJ2 hJ1).ge

  haveI := hP
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Algebra.FormallyUnramified B (A ⧸ I) :=
    Algebra.FormallyUnramified.comp B A (A ⧸ I)
  haveI : Algebra.FormallyUnramified (B ⧸ P) (A ⧸ I) :=
    Algebra.FormallyUnramified.of_restrictScalars B (B ⧸ P) (A ⧸ I)
  haveI : Algebra.EssFiniteType B (A ⧸ I) := Algebra.EssFiniteType.comp B A (A ⧸ I)
  haveI : Algebra.EssFiniteType (B ⧸ P) (A ⧸ I) := Algebra.EssFiniteType.of_comp B (B ⧸ P) (A ⧸ I)
  haveI : IsReduced (A ⧸ I) := Algebra.FormallyUnramified.isReduced_of_field (B ⧸ P) (A ⧸ I)
  intro x hx
  rw [← hrad] at hx
  obtain ⟨n, hn⟩ := hx
  have h0 : (Ideal.Quotient.mk I x) ^ n = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn
  have : Ideal.Quotient.mk I x = 0 := IsReduced.eq_zero _ ⟨n, h0⟩
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleUniquePrimeLeMapMaximalStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_unique_prime_le_map_maximal : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] [Algebra.Etale B A] (P : Ideal B), P.IsMaximal → ∀ (Q : Ideal A), (∀ Q' : Ideal A, Q'.IsPrime → P.map (algebraMap B A) ≤ Q' → Q' = Q) → Q ≤ P.map (algebraMap B A) := by
  first | (exact @GlobalTheory.etale_prime_le_map_of_unique) | (exact GlobalTheory.etale_prime_le_map_of_unique) | (intros; apply GlobalTheory.etale_prime_le_map_of_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAwayQuotientEqLocalization
namespace GlobalTheory

theorem etale_away_quotient_eq_localization :
    ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D] [Algebra.Etale B D]
      (f : B), f ≠ 0 → ∀ (P : Ideal B), P.IsMaximal → f ∈ P → ∀ (Q : Ideal D), Q.IsPrime →
      Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) →
      ∃ g : D, (∀ a : Localization.Away g, ∃ b : B,
          a - algebraMap B (Localization.Away g) b ∈
            Ideal.span {algebraMap B (Localization.Away g) f}) ∧
        ∀ b : B, algebraMap B (Localization.Away g) b ∈
            Ideal.span {algebraMap B (Localization.Away g) f} ↔
          ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  intro B D _ _ _ _ _ f hf P hP hfP Q hQ hQP hres

  have hQmax : Q.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h1 => ?_, fun J x hQJ hx hxJ => ?_⟩
    · have : (1 : B) ∈ Q.comap (algebraMap B D) := by simpa using h1
      rw [hQP] at this
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 this)
    · obtain ⟨b, hb⟩ := hres x
      have hbP : b ∉ P := by
        intro hbP
        apply hx
        have : algebraMap B D b ∈ Q := by
          rw [← Ideal.mem_comap, hQP]; exact hbP
        simpa using Q.add_mem hb this
      obtain ⟨c, hc⟩ : ∃ c : B, c * b - 1 ∈ P := by
        obtain ⟨c, i, hi, hci⟩ := hP.exists_inv hbP
        refine ⟨c, ?_⟩
        have : c * b - 1 = -i := by rw [← hci]; ring
        rw [this]; exact P.neg_mem hi
      have h1 : algebraMap B D (c * b - 1) ∈ Q := by
        rw [← Ideal.mem_comap, hQP]; exact hc
      have h2 : algebraMap B D c * x - 1 ∈ Q := by
        have : algebraMap B D c * x - 1 =
            algebraMap B D c * (x - algebraMap B D b) + algebraMap B D (c * b - 1) := by
          simp only [map_sub, map_mul, map_one]; ring
        rw [this]
        exact Q.add_mem (Q.mul_mem_left _ hb) h1
      have h3 : algebraMap B D c * x ∈ J := J.mul_mem_left _ hxJ
      have : (1 : D) = algebraMap B D c * x - (algebraMap B D c * x - 1) := by ring
      rw [this]
      exact J.sub_mem h3 (hQJ h2)
  obtain ⟨g, hgQ, hQ'⟩ := GlobalTheory.T.isolate_maximal_among_primes_containing_etale B D f hf Q hQmax
  refine ⟨g, ?_⟩
  haveI : Algebra.Etale D (Localization.Away g) := Algebra.Etale.of_isLocalizationAway g
  haveI : Algebra.Etale B (Localization.Away g) := Algebra.Etale.comp B D (Localization.Away g)
  have hφ : ∀ b : B, algebraMap B (Localization.Away g) b =
      algebraMap D (Localization.Away g) (algebraMap B D b) := fun b =>
    IsScalarTower.algebraMap_apply B D (Localization.Away g) b

  have hunit := GlobalTheory.T.localization_inverse_mod_f B D f P Q g hQP hQ'

  have hker : ∀ b : B, (∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f}) →
      algebraMap B (Localization.Away g) b ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
    rintro b ⟨s, hs, hsb⟩
    obtain ⟨t, ht⟩ := hunit s hs
    have h1 : algebraMap B (Localization.Away g) (s * b) ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
      rw [Ideal.mem_span_singleton] at hsb ⊢
      obtain ⟨c, hc⟩ := hsb
      exact ⟨algebraMap B _ c, by rw [hc, map_mul]⟩
    have : algebraMap B (Localization.Away g) b = algebraMap B _ (s * b) * t -
        (algebraMap B _ s * t - 1) * algebraMap B (Localization.Away g) b := by
      rw [map_mul]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_right _ _ ht)
  refine ⟨?_, fun b => ⟨fun hb => ?_, hker b⟩⟩
  ·
    obtain ⟨N, hN⟩ := GlobalTheory.T.dedekind_power_localization B f hf P hP
    have hPN : (P ^ N).map (algebraMap B (Localization.Away g)) ≤
        Ideal.span {algebraMap B (Localization.Away g) f} := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      exact hker b (hN b hb)
    have hfib : ∀ Q' : Ideal (Localization.Away g), Q'.IsPrime →
        P.map (algebraMap B (Localization.Away g)) ≤ Q' →
        Q' = Q.map (algebraMap D (Localization.Away g)) := by
      intro Q' hQ'p hPQ'
      have hc : Q'.comap (algebraMap D (Localization.Away g)) = Q := by
        apply hQ' _ (Ideal.comap_isPrime _ _)
        · rw [Ideal.mem_comap, ← hφ]
          exact hPQ' (Ideal.mem_map_of_mem _ hfP)
        · intro hg
          rw [Ideal.mem_comap] at hg
          exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hg
            (IsLocalization.Away.algebraMap_isUnit g))
      rw [← hc]
      exact (IsLocalization.map_under (Submonoid.powers g) (Localization.Away g) Q').symm
    have hle := GlobalTheory.T.etale_unique_prime_le_map_maximal B (Localization.Away g) P hP
      (Q.map (algebraMap D (Localization.Away g))) hfib
    have hres' := GlobalTheory.T.localization_residue_approximation B D P hP Q g hgQ hQP hres
    refine GlobalTheory.T.nilpotent_approximation_surjective B (Localization.Away g) P _ N (fun a => ?_) hPN
    obtain ⟨b, hb⟩ := hres' a
    exact ⟨b, Ideal.mem_sup_left (hle hb)⟩
  ·
    have hgu : IsUnit (algebraMap D (Localization.AtPrime Q) g) :=
      IsLocalization.map_units (Localization.AtPrime Q) (⟨g, hgQ⟩ : Q.primeCompl)
    let ρ : Localization.Away g →+* Localization.AtPrime Q := IsLocalization.Away.lift g hgu
    have hρ : ∀ d : D, ρ (algebraMap D (Localization.Away g) d) =
        algebraMap D (Localization.AtPrime Q) d :=
      fun d => IsLocalization.Away.lift_eq g hgu d
    have e : ∀ x : B, algebraMap B (Localization.AtPrime Q) x =
        ρ (algebraMap B (Localization.Away g) x) := by
      intro x
      rw [hφ, hρ, IsScalarTower.algebraMap_apply B D (Localization.AtPrime Q)]
    have hloc : algebraMap B (Localization.AtPrime Q) b ∈
        Ideal.span {algebraMap B (Localization.AtPrime Q) f} := by
      rw [Ideal.mem_span_singleton] at hb ⊢
      obtain ⟨c, hc⟩ := hb
      exact ⟨ρ c, by rw [e, e, hc, map_mul]⟩
    obtain ⟨s, hs, hsb⟩ := GlobalTheory.T.flat_localization_membership B D Q f b hloc
    rw [hQP] at hs
    exact ⟨s, hs, hsb⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAwayQuotientEqLocalizationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.away_quotient_span_eq_localization : ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D] [Algebra.Etale B D] (f : B), f ≠ 0 → ∀ (P : Ideal B), P.IsMaximal → f ∈ P → ∀ (Q : Ideal D), Q.IsPrime → Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) → ∃ g : D, (∀ a : Localization.Away g, ∃ b : B, a - algebraMap B (Localization.Away g) b ∈ Ideal.span {algebraMap B (Localization.Away g) f}) ∧ ∀ b : B, algebraMap B (Localization.Away g) b ∈ Ideal.span {algebraMap B (Localization.Away g) f} ↔ ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.etale_away_quotient_eq_localization) | (exact GlobalTheory.etale_away_quotient_eq_localization) | (intros; apply GlobalTheory.etale_away_quotient_eq_localization  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMaximalContaining
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDensitiesBoundedAlmostAll
namespace GlobalTheory

theorem finite_maximal_ideals_containing (B : Type) [CommRing B] [IsDedekindDomain B] (f : B)
    (hf : f ≠ 0) : {P : Ideal B | P.IsMaximal ∧ f ∈ P}.Finite := by
  have hI : Ideal.span {f} ≠ (0 : Ideal B) := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact hf
  have hfin := Ideal.finite_factors hI
  apply (hfin.image (fun v : IsDedekindDomain.HeightOneSpectrum B => v.asIdeal)).subset
  rintro P ⟨hmax, hfP⟩
  have hne : P ≠ ⊥ := by
    rintro rfl
    exact hf ((Submodule.mem_bot B).mp hfP)
  refine ⟨⟨P, hmax.isPrime, hne⟩, ?_, rfl⟩
  show P ∣ Ideal.span {f}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hfP

theorem finite_maximal_ideals_containing' : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B),
    f ≠ 0 → {P : Ideal B | P.IsMaximal ∧ f ∈ P}.Finite :=
  fun B _ _ f hf => finite_maximal_ideals_containing B f hf

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_maximal_containing : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B), f ≠ 0 → {P : Ideal B | P.IsMaximal ∧ f ∈ P}.Finite := by
  first | (exact @GlobalTheory.finite_maximal_ideals_containing') | (exact GlobalTheory.finite_maximal_ideals_containing') | (intros; apply GlobalTheory.finite_maximal_ideals_containing' <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleProdOfEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleProdOfEtale
namespace GlobalTheory.EtaleProd

abbrev fam (A₁ A₂ : Type) : Fin 2 → Type := ![A₁, A₂]

instance instCommRing (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] : ∀ i, CommRing (fam A₁ A₂ i) :=
  Fin.cases (inferInstanceAs (CommRing A₁)) (Fin.cases (inferInstanceAs (CommRing A₂)) finZeroElim)

instance instAlgebra (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂] :
    ∀ i, Algebra B (fam A₁ A₂ i) :=
  Fin.cases (inferInstanceAs (Algebra B A₁)) (Fin.cases (inferInstanceAs (Algebra B A₂)) finZeroElim)

theorem etale_fam (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂]
    (h₁ : Algebra.Etale B A₁) (h₂ : Algebra.Etale B A₂) : ∀ i, Algebra.Etale B (fam A₁ A₂ i) :=
  Fin.cases h₁ (Fin.cases h₂ finZeroElim)

end GlobalTheory.EtaleProd


open GlobalTheory.EtaleProd in
theorem GlobalTheory.etale_prod : ∀ (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂], Algebra.Etale B A₁ → Algebra.Etale B A₂ → Algebra.Etale B (A₁ × A₂) := by
  intro B A₁ A₂ _ _ _ _ _ h₁ h₂
  haveI := etale_fam B A₁ A₂ h₁ h₂
  exact Algebra.Etale.of_equiv
    (AlgEquiv.ofRingEquiv (R := B) (f := RingEquiv.piFinTwo (fam A₁ A₂)) fun _ => rfl)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleProdOfEtaleStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_prod_of_etale : ∀ (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂], Algebra.Etale B A₁ → Algebra.Etale B A₂ → Algebra.Etale B (A₁ × A₂) := by
  first | (exact @GlobalTheory.etale_prod) | (exact GlobalTheory.etale_prod) | (intros; apply GlobalTheory.etale_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldAtPrimeIsSepClosedOfFiniteType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldAtPrimeIsSepClosedOfFiniteType
namespace GlobalTheory

theorem residueField_localization_atPrime_isSepClosed_of_finiteType :
    ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
      (P : Ideal B) [P.IsMaximal],
      IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) := by
  intro k B _ _ _ _ _ P _
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Module.Finite k (B ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ P)
  haveI : Algebra.IsIntegral k (B ⧸ P) := inferInstance
  let f : k ≃+* (B ⧸ P) := RingEquiv.ofBijective (algebraMap k (B ⧸ P))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsAlgClosed (B ⧸ P) := IsAlgClosed.of_ringEquiv k (B ⧸ P) f
  let e : (B ⧸ P) ≃+* IsLocalRing.ResidueField (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)).toRingEquiv
  haveI : IsAlgClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) :=
    IsAlgClosed.of_ringEquiv _ _ e
  infer_instance

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldAtPrimeIsSepClosedOfFiniteTypeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueField_atPrime_isSepClosed_of_finiteType : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B] (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) := by
  first | (exact @GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType) | (exact GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType) | (intros; apply GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalVanishingCohomology
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

noncomputable section

namespace GlobalTheory.CurveNbhdKill

def locKer {B : Type} [CommRing B] (f : B) (P : Ideal B) (hP : P.IsPrime) : Ideal B :=
  GlobalTheory.LocalSaturationContraction.satAt f P (hP := hP)

theorem locKer_coprime {B : Type} [CommRing B] [IsDedekindDomain B] (f : B) (hf : f ≠ 0) (P P' : Ideal B)
    (hP : P.IsMaximal) (hP' : P'.IsMaximal) (hne : P ≠ P') :
    IsCoprime (locKer f P hP.isPrime) (locKer f P' hP'.isPrime) := by
  obtain ⟨N, hN⟩ := GlobalTheory.T.dedekind_power_localization B f hf P hP
  obtain ⟨N', hN'⟩ := GlobalTheory.T.dedekind_power_localization B f hf P' hP'
  have hc : IsCoprime P P' := Ideal.isCoprime_iff_sup_eq.2 (Ideal.IsMaximal.coprime_of_ne hP hP' hne)
  have hc' : IsCoprime (P ^ N) (P' ^ N') := hc.pow
  rw [Ideal.isCoprime_iff_sup_eq] at hc' ⊢
  exact eq_top_iff.2 (hc' ▸ sup_le_sup (fun b hb => hN b hb) (fun b hb => hN' b hb))

theorem mem_of_forall_locKer {B : Type} [CommRing B] (f b : B)
    (h : ∀ P : Ideal B, P.IsMaximal → f ∈ P → ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f}) :
    b ∈ Ideal.span {f} := by
  let J : Ideal B := Submodule.comap (LinearMap.mulRight B b) (Ideal.span {f})
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
    have hfJ : f ∈ J := by
      rw [Submodule.mem_comap, LinearMap.mulRight_apply]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)
    obtain ⟨s, hs, hsb⟩ := h M hM (hJM hfJ)
    exact hs (hJM (by rw [Submodule.mem_comap, LinearMap.mulRight_apply]; exact hsb))
  have h1 : (1 : B) ∈ J := hJ ▸ Submodule.mem_top
  simpa [J] using h1

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, Spec.map_comp]

variable (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
  [Algebra.FiniteType k B]

theorem onePoint (hq : IsUnit (q : k)) (f : B) (hf : f ≠ 0) (m i : ℤ) (hm : 1 ≤ m) (y : Ht q (sp B) m i)
    (P : Ideal B) (hP : P.IsMaximal) (hfP : f ∈ P) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra B A) (_ : Algebra.Etale B A),
      (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ Ideal.span {algebraMap B A f}) ∧
      (∀ b : B, algebraMap B A b ∈ Ideal.span {algebraMap B A f} ↔ b ∈ locKer f P hP.isPrime) ∧
      pull _ (spMap (algebraMap B A)) _ _ y = 0 := by
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  have hsep := GlobalTheory.T.residueField_atPrime_isSepClosed_of_finiteType k B P
  obtain ⟨D, _, _, _, Q, hQ, hQP, hres, hy⟩ := GlobalTheory.T.etale_neighbourhood_kills_class q B hqB P hsep m i (by omega) y
  obtain ⟨g, hS, hK⟩ := GlobalTheory.T.away_quotient_span_eq_localization B D f hf P hP hfP Q hQ hQP hres
  refine ⟨Localization.Away g, inferInstance, inferInstance, inferInstance, hS, hK, ?_⟩
  rw [IsScalarTower.algebraMap_eq B D (Localization.Away g), spMap_comp', pull_comp, hy, map_zero]

theorem exists_nbhd_pull_eq_zero : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ¬ IsUnit f → ∀ (m i : ℤ), 1 ≤ m → ∀ y : Ht q (sp B) m i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A') (_ : Algebra.Etale B A'), IsNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ y = 0 := by
  intro q _ k B _ _ _ _ _ _ hq f hf hfu m i hm y
  let Pt := {P : Ideal B // P.IsMaximal ∧ f ∈ P}
  haveI : Finite Pt := (GlobalTheory.T.finite_maximal_containing B f hf).to_subtype
  letI : Fintype Pt := Fintype.ofFinite Pt
  let K : Pt → Ideal B := fun x => locKer f x.1 x.2.1.isPrime
  have key : ∀ T : Finset Pt, T.Nonempty → ∃ (A : Type) (_ : CommRing A) (_ : Algebra B A) (_ : Algebra.Etale B A),
      (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ Ideal.span {algebraMap B A f}) ∧
      (∀ b : B, algebraMap B A b ∈ Ideal.span {algebraMap B A f} ↔ b ∈ ⨅ x ∈ T, K x) ∧
      pull _ (spMap (algebraMap B A)) _ _ y = 0 := by
    intro T hT
    induction hT using Finset.Nonempty.cons_induction with
    | singleton x =>
      obtain ⟨A, _, _, _, hS, hK, hy⟩ := onePoint q k B hq f hf m i hm y x.1 x.2.1 x.2.2
      exact ⟨A, inferInstance, inferInstance, inferInstance, hS, fun b => by simpa [K] using hK b, hy⟩
    | cons x T hx hT ih =>
      obtain ⟨A₁, _, _, _, hS₁, hK₁, hy₁⟩ := ih
      obtain ⟨A₂, _, _, _, hS₂, hK₂, hy₂⟩ := onePoint q k B hq f hf m i hm y x.1 x.2.1 x.2.2
      have hcop : IsCoprime (⨅ j ∈ T, K j) (K x) := by
        refine (Ideal.isCoprime_biInf fun j hj => ?_).symm
        refine locKer_coprime f hf x.1 j.1 x.2.1 j.2.1 fun h => hx ?_
        have : x = j := Subtype.ext h
        exact this ▸ hj
      obtain ⟨hS, hK, hy⟩ := GlobalTheory.T.approximation_quotients_agree q B A₁ A₂ f _ _ m i y hcop hS₁ hK₁ hS₂ hK₂ hy₁ hy₂
      refine ⟨A₁ × A₂, inferInstance, inferInstance, GlobalTheory.T.etale_prod_of_etale B A₁ A₂ inferInstance inferInstance, hS, fun b => ?_, hy⟩
      rw [hK b, Finset.cons_eq_insert, Finset.iInf_insert, inf_comm]
  have hne : (Finset.univ : Finset Pt).Nonempty := by
    have hspan : Ideal.span {f} ≠ ⊤ := fun h => hfu (Ideal.span_singleton_eq_top.1 h)
    obtain ⟨M, hM, hfM⟩ := Ideal.exists_le_maximal _ hspan
    exact ⟨⟨M, hM, hfM (Ideal.mem_span_singleton_self f)⟩, Finset.mem_univ _⟩
  obtain ⟨A, _, _, _, hS, hK, hy⟩ := key Finset.univ hne
  refine ⟨A, inferInstance, inferInstance, inferInstance, ⟨hS, fun b hb => ?_⟩, hy⟩
  have hb' := (hK b).1 hb
  refine mem_of_forall_locKer f b fun P hP hfP => ?_
  have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hb' ⟨P, hP, hfP⟩) (Finset.mem_univ _)
  exact this

end GlobalTheory.CurveNbhdKill

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalVanishingCohomologyStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_local_vanishing_cohomology : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ¬ IsUnit f → ∀ (m i : ℤ), 1 ≤ m → ∀ y : Ht q (sp B) m i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A') (_ : Algebra.Etale B A'), IsNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ y = 0 := by
  first | (exact @GlobalTheory.CurveNbhdKill.exists_nbhd_pull_eq_zero) | (exact GlobalTheory.CurveNbhdKill.exists_nbhd_pull_eq_zero) | (intros; apply GlobalTheory.CurveNbhdKill.exists_nbhd_pull_eq_zero <;> assumption)
end
