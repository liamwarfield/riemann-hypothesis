module

public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterInnerEqIntMulCard
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicSections

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleOfVirtualCharacterNormOne
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleOfVirtualCharacterNormOne
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

theorem finsupp_eq_single_of_sum_sq_eq_one {α : Type} (c : α →₀ ℤ)
    (h : (c.sum fun _ m => m ^ 2) = 1) :
    ∃ a, c.support = {a} ∧ (c a = 1 ∨ c a = -1) := by
  simp only [Finsupp.sum] at h
  have hge : ∀ b ∈ c.support, (1 : ℤ) ≤ c b ^ 2 := by
    intro b hb
    have hb' : c b ≠ 0 := Finsupp.mem_support_iff.mp hb
    rcases lt_or_gt_of_ne hb' with hlt | hgt <;> nlinarith
  have hle : (c.support.card : ℤ) ≤ 1 := by
    calc (c.support.card : ℤ) = ∑ _b ∈ c.support, (1 : ℤ) := by simp
      _ ≤ ∑ b ∈ c.support, c b ^ 2 := Finset.sum_le_sum hge
      _ = 1 := h
  have hne : c.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.sum_empty] at h
    exact zero_ne_one h
  have hcard : c.support.card = 1 := by
    have := hne.card_pos
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  refine ⟨a, ha, ?_⟩
  rw [ha, Finset.sum_singleton] at h
  have h1 : c a ≤ 1 := by nlinarith
  have h2 : -1 ≤ c a := by nlinarith
  have h3 : c a ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  omega

private theorem exists_pos_nat_apply_one_of_isIrrChar {G : Type} [Group G] (χ : G → ℂ) (h : IsIrrChar ℂ ℂ χ) :
    ∃ n : ℕ, 0 < n ∧ χ 1 = n := by
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  refine ⟨n, ?_, ?_⟩
  · have hs : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hρ
    have hnt : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) _
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · exfalso
      subst h0
      obtain ⟨x, y, hxy⟩ := hnt
      exact hxy (Subsingleton.elim (α := Fin 0 → ℂ) x y)
    · exact hn
  · rw [hχ, Representation.char_one]
    simp

theorem irr_of_norm_one : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ), φ ∈ Virt ℂ ℂ G → ∑ᶠ g, φ g * star (φ g) = (Nat.card G : ℂ) → (IsIrrChar ℂ ℂ φ ∨ IsIrrChar ℂ ℂ (-φ)) ∧ (IsChar ℂ ℂ φ → IsIrrChar ℂ ℂ φ ∧ ∃ n : ℕ, 0 < n ∧ φ 1 = n) := by
  intro G _ _ φ hφ hnorm
  obtain ⟨c, hirr, hsum, hsq⟩ := GlobalTheory.T.virtualCharacter_irreducible_expansion_normSq G φ hφ
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h1 : (c.sum fun _ m => (m : ℂ) ^ 2) = 1 :=
    mul_right_cancel₀ hG ((hsq.symm.trans hnorm).trans (one_mul _).symm)
  have h2 : (c.sum fun _ m => m ^ 2) = 1 := by
    simp only [Finsupp.sum] at h1 ⊢
    exact_mod_cast h1
  obtain ⟨χ, hsupp, hc⟩ := finsupp_eq_single_of_sum_sq_eq_one c h2
  have hχ : IsIrrChar ℂ ℂ χ := hirr χ (by rw [hsupp]; exact Finset.mem_singleton_self χ)
  have hφχ : φ = c χ • χ := by
    rw [hsum, Finsupp.sum, hsupp, Finset.sum_singleton]
  have key : φ = χ ∨ φ = -χ := by
    rcases hc with h | h
    · left
      rw [hφχ, h, one_smul]
    · right
      rw [hφχ, h, neg_smul, one_smul]
  obtain ⟨n, hn, hn1⟩ := exists_pos_nat_apply_one_of_isIrrChar χ hχ
  rcases key with rfl | rfl
  · exact ⟨Or.inl hχ, fun _ => ⟨hχ, n, hn, hn1⟩⟩
  · refine ⟨Or.inr (by simpa using hχ), fun hc' => ?_⟩
    exfalso
    obtain ⟨-, -, m, hm, -⟩ := GlobalTheory.isChar_restrict_conj_one ℂ ℂ G (-χ) hc'
    have h3 : ((m + n : ℕ) : ℂ) = 0 := by
      push_cast
      rw [← hm, ← hn1, Pi.neg_apply]
      ring
    have h4 : m + n = 0 := by exact_mod_cast h3
    omega

end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleOfVirtualCharacterNormOneStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_of_virtualCharacter_norm_one : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ), φ ∈ Virt ℂ ℂ G → ∑ᶠ g, φ g * star (φ g) = (Nat.card G : ℂ) → (IsIrrChar ℂ ℂ φ ∨ IsIrrChar ℂ ℂ (-φ)) ∧ (IsChar ℂ ℂ φ → IsIrrChar ℂ ℂ φ ∧ ∃ n : ℕ, 0 < n ∧ φ 1 = n) := by
  first | exact @GlobalTheory.BI.irr_of_norm_one | exact GlobalTheory.BI.irr_of_norm_one | (intros; apply GlobalTheory.BI.irr_of_norm_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsHolomorphicFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsHolomorphicFamily
open Topology

namespace GlobalTheory.SmoothPointFamily

open KaehlerDifferential


set_option backward.isDefEq.respectTransparency.types false in
theorem exists_basis_away {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] :
    ∃ (g : S) (m : ℕ) (s : Fin m → S)
      (b : Module.Basis (Fin m) (Localization.Away g) Ω[Localization.Away g⁄R]),
      g ∉ p ∧ ∀ i, b i = D R (Localization.Away g) (algebraMap S _ (s i)) := by
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _
    (span_range_map_derivation_of_isLocalization R _ (Localization.AtPrime p) p.primeCompl)
  let e : (κ →₀ S) →ₗ[S] Ω[S⁄R] :=
    Finsupp.linearCombination S fun i : κ ↦ D R S (a i)
  let l₁ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S (Localization.AtPrime p))
  let l₂ : Ω[S⁄R] →ₗ[S] Ω[Localization.AtPrime p⁄R] := map R R S (Localization.AtPrime p)
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p] Ω[Localization.AtPrime p⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e <| l₁ <| Finsupp.single i 1
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb]
  have heₚ : Function.Bijective eₚ := this ▸ b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂ heₚ
  let l₁ₜ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S _)
  let l₂ₜ : Ω[S⁄R] →ₗ[S] Ω[Localization.Away g⁄R] :=
    map R R S (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ] at h
  let eₜ' : (κ →₀ Localization.Away g) →ₗ[Localization.Away g] Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e
  obtain ⟨m, ⟨u⟩⟩ := Finite.exists_equiv_fin κ
  let b' : Module.Basis κ (Localization.Away g) Ω[Localization.Away g⁄R] :=
    .ofRepr (LinearEquiv.ofBijective eₜ' h).symm
  have hb' : ∀ i, b' i = D R (Localization.Away g) (algebraMap S _ (a i)) := fun i => by
    simp +zetaDelta [IsLocalizedModule.map_linearCombination]
  exact ⟨g, m, fun i => a (u.symm i), b'.reindex u, hg, fun i => by
    rw [Module.Basis.reindex_apply, hb']⟩

theorem exists_etale_away {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] :
    ∃ (g : S) (m : ℕ) (s : Fin m → S), g ∉ p ∧
      (MvPolynomial.eval₂Hom (algebraMap R (Localization.Away g))
        fun i => algebraMap S (Localization.Away g) (s i)).Etale := by
  obtain ⟨g, m, s, b, hg, hb⟩ := exists_basis_away (R := R) p
  refine ⟨g, m, s, hg, ?_⟩
  letI : Algebra (MvPolynomial (Fin m) R) (Localization.Away g) :=
    (MvPolynomial.eval₂Hom (algebraMap R (Localization.Away g))
        fun i => algebraMap S (Localization.Away g) (s i)).toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin m) R) (Localization.Away g) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [RingHom.algebraMap_toAlgebra]
      simp
  haveI : Algebra.Smooth S (Localization.Away g) := Algebra.Smooth.of_isLocalization_Away g
  haveI : Algebra.Smooth R (Localization.Away g) := Algebra.Smooth.comp R S _
  refine GlobalTheory.EtaleCoordJacobian.etale_of_basis R (Localization.Away g) (Fin m) b fun i => ?_
  rw [hb, RingHom.algebraMap_toAlgebra]
  simp

theorem exists_finset_of_mem_nhds {A : Type} {x : A → ℂ} {U : Set (A → ℂ)} (hU : U ∈ 𝓝 x) :
    ∃ (S : Finset A) (ε : ℝ), 0 < ε ∧ ∀ y : A → ℂ, (∀ a ∈ S, ‖y a - x a‖ < ε) → y ∈ U := by
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, hI⟩ := hU
  choose δ hδ hδt using fun a => Metric.mem_nhds_iff.1 (ht a)
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a ∈ I, ε < δ a :=
    (Filter.eventually_all_finset I).2 fun a _ =>
      nhdsWithin_le_nhds (gt_mem_nhds (hδ a))
  obtain ⟨ε, h2, h3⟩ := (h1.and self_mem_nhdsWithin).exists
  refine ⟨I, ε, h3, fun y hy => hI fun a ha => hδt a ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  exact (hy a ha).trans (h2 a ha)

theorem exists_holomorphic_family : ∀ (K A : Type) [Field K] [CharZero K] [CommRing A] [Algebra K A] [Algebra.Smooth K A] (σ : K →+* ℂ) (φ₀ : A →+* ℂ), φ₀.comp (algebraMap K A) = σ → ∃ (m : ℕ) (s : Fin m → A) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (S : Finset A) (ε : ℝ), IsOpen B ∧ 0 < ε ∧ (∀ b ∈ B, (φ b).comp (algebraMap K A) = σ ∧ ∀ i, φ b (s i) = b i) ∧ (∀ a : A, DifferentiableOn ℂ (fun b => φ b a) B) ∧ ∀ ψ : A →+* ℂ, ψ.comp (algebraMap K A) = σ → (∀ a ∈ S, ‖ψ a - φ₀ a‖ < ε) → (fun i => ψ (s i)) ∈ B ∧ φ (fun i => ψ (s i)) = ψ := by
  intro K A _ _ _ _ _ σ φ₀ h₀
  haveI : (RingHom.ker φ₀).IsPrime := RingHom.ker_isPrime φ₀
  obtain ⟨g, m, s, hg, het⟩ := exists_etale_away (R := K) (RingHom.ker φ₀)
  have hg₀ : φ₀ g ≠ 0 := hg
  let R := Localization.Away g
  let ι : A →+* R := algebraMap A R
  let L : (ψ : A →+* ℂ) → ψ g ≠ 0 → (R →+* ℂ) := fun ψ h =>
    IsLocalization.Away.lift g (g := ψ) (isUnit_iff_ne_zero.2 h)
  have hL : ∀ ψ h a, L ψ h (ι a) = ψ a := fun ψ h a => IsLocalization.Away.lift_eq g _ a
  let P : MvPolynomial (Fin m) K →+* R := MvPolynomial.eval₂Hom (algebraMap K R) fun i => ι (s i)
  have hPC : ∀ k, P (MvPolynomial.C k) = ι (algebraMap K A k) := fun k => by
    simp only [P, MvPolynomial.eval₂Hom_C]
    exact IsScalarTower.algebraMap_apply K A R k
  have hPX : ∀ i, P (MvPolynomial.X i) = ι (s i) := fun i => by simp [P]
  have hLC : ∀ (ψ : A →+* ℂ) h, ψ.comp (algebraMap K A) = σ →
      ∀ k, L ψ h (P (MvPolynomial.C k)) = σ k := fun ψ h hψ k => by
    rw [hPC, hL ψ h, ← hψ]; rfl
  obtain ⟨N, τ, n, f, O, hN, hO, hO₀, hd, hτ, hrec⟩ :=
    GlobalTheory.EtaleFamily.exists_holomorphic_sections 0 m K R P Set.univ (fun _ => σ) 0 (L φ₀ hg₀) het
      isOpen_univ trivial (fun a => differentiableOn_const _) (hLC φ₀ hg₀ h₀)
  choose k c hc using fun j => IsLocalization.Away.surj g (f j)
  have hval : ∀ ψ h j, L ψ h (f j) = ψ (c j) / ψ g ^ k j := fun ψ h j => by
    have := congrArg (L ψ h) (hc j)
    rw [map_mul, map_pow, hL ψ h, hL ψ h] at this
    rw [← this, mul_div_cancel_right₀ _ (pow_ne_zero _ h)]
  have hcont : ContinuousAt
      (fun y : A → ℂ => ((0 : Fin 0 → ℂ), fun j => y (c j) / y g ^ k j)) φ₀ :=
    continuousAt_const.prodMk (continuousAt_pi.2 fun j =>
      (continuous_apply (c j)).continuousAt.div ((continuous_apply g).pow _).continuousAt
        (pow_ne_zero _ hg₀))
  have hU : {y : A → ℂ | y g ≠ 0 ∧ ((0 : Fin 0 → ℂ), fun j => y (c j) / y g ^ k j) ∈ O} ∈
      𝓝 (φ₀ : A → ℂ) := by
    refine Filter.Eventually.and ((continuous_apply g).continuousAt.eventually_ne hg₀)
      (hcont (hO.mem_nhds ?_))
    simpa only [hval] using hO₀
  obtain ⟨S, ε, hε, hS⟩ := exists_finset_of_mem_nhds hU
  have hin : Differentiable ℂ fun b : Fin m → ℂ => ((0 : Fin 0 → ℂ), b) :=
    (differentiable_const _).prodMk differentiable_id
  refine ⟨m, s, (fun b => ((0 : Fin 0 → ℂ), b)) ⁻¹' N, fun b => (τ (0, b)).comp ι, S, ε,
    hN.preimage hin.continuous, hε, fun b hb => ⟨RingHom.ext fun a => ?_, fun i => ?_⟩,
    fun a => (hd (ι a)).comp hin.differentiableOn fun _ h => h, fun ψ hψ hψS => ?_⟩
  · rw [RingHom.comp_apply, RingHom.comp_apply, ← hPC]
    exact (hτ _ hb).2.1 a
  · rw [RingHom.comp_apply, ← hPX]
    exact (hτ _ hb).2.2 i
  · obtain ⟨h1, h2⟩ := hS ψ hψS
    obtain ⟨h3, h4⟩ := hrec 0 (L ψ h1) (hLC ψ h1 hψ) (by simpa only [hval] using h2)
    simp only [hPX, hL ψ h1] at h3 h4
    refine ⟨h3, RingHom.ext fun a => ?_⟩
    rw [RingHom.comp_apply, h4, hL ψ h1]

end GlobalTheory.SmoothPointFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsHolomorphicFamilyStatement
open Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_family_of_ringHom_near : ∀ (K A : Type) [Field K] [CharZero K] [CommRing A] [Algebra K A] [Algebra.Smooth K A] (σ : K →+* ℂ) (φ₀ : A →+* ℂ), φ₀.comp (algebraMap K A) = σ → ∃ (m : ℕ) (s : Fin m → A) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (S : Finset A) (ε : ℝ), IsOpen B ∧ 0 < ε ∧ (∀ b ∈ B, (φ b).comp (algebraMap K A) = σ ∧ ∀ i, φ b (s i) = b i) ∧ (∀ a : A, DifferentiableOn ℂ (fun b => φ b a) B) ∧ ∀ ψ : A →+* ℂ, ψ.comp (algebraMap K A) = σ → (∀ a ∈ S, ‖ψ a - φ₀ a‖ < ε) → (fun i => ψ (s i)) ∈ B ∧ φ (fun i => ψ (s i)) = ψ := by
  first | exact @GlobalTheory.SmoothPointFamily.exists_holomorphic_family | exact GlobalTheory.SmoothPointFamily.exists_holomorphic_family | (intros; apply GlobalTheory.SmoothPointFamily.exists_holomorphic_family <;> assumption)
end
end
