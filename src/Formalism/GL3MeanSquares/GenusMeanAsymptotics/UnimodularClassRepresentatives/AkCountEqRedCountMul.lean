module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLiftBasis
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFibGEqProd

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AkCountEqRedCountMul
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SigmaCountPosBasis
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem exists_arch {S : Subring K} {ϖ : K} (hS : IsLocUnif S ϖ) {α : Type*} [Fintype α] (f : α → K) :
    ∃ l : ℕ, ∀ a, ϖ ^ l * f a ∈ S := by
  classical
  choose l hl using fun a => hS.arch (f a)
  refine ⟨∑ a, l a, fun a => ?_⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), add_comm, pow_add, mul_assoc]
  exact S.mul_mem (pow_mem hS _) (hl a)

theorem exists_isE (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ e, IsE h (locF 𝔭 (spanO b)) 𝔭 e := by
  classical
  have : 𝔭.IsPrime := h𝔭.isPrime
  let f := algebraMap (𝓞 F) (𝓞 K)
  let g := algebraMap (𝓞 K) K
  let a := (gramK h b)⁻¹
  have hdet : IsUnit (gramK h b).det := isUnit_iff_ne_zero.2 (gramK_det_ne_zero hd b)
  -- Clear the denominators of all entries of the inverse Gram matrix at once.
  obtain ⟨n, hn, ha⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image (fun p : κ × κ => a p.1 p.2))
  have hentry (i j : κ) : ∃ z : 𝓞 K, g z = (n : K) * a i j := by
    have hi := ha (a i j) (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    exact ⟨⟨n • a i j, hi⟩, by simp [g, zsmul_eq_mul]⟩
  have hnspan : Ideal.span {(n : 𝓞 F)} ≠ 0 := by
    simpa using (Int.cast_ne_zero.mpr hn : (n : 𝓞 F) ≠ 0)
  have hpunit : ¬ IsUnit 𝔭 := fun hunit => h𝔭.ne_top (Ideal.isUnit_iff.mp hunit)
  -- Factor out the power of 𝔭 in the denominator ideal.
  obtain ⟨J, hJ, hJp⟩ :=
    (FiniteMultiplicity.of_not_isUnit hpunit hnspan).exists_eq_pow_mul_and_not_dvd
  rw [Ideal.dvd_iff_le] at hJp
  obtain ⟨u, huJ, hu⟩ := IsConcreteLE.not_le_iff_exists.mp hJp
  generalize multiplicity 𝔭 (Ideal.span {(n : 𝓞 F)}) = l at hJ
  refine ⟨l, fun x hx t ht => ?_⟩
  have htu : t * u ∈ Ideal.span {(n : 𝓞 F)} := by
    rw [hJ]
    exact Ideal.mul_mem_mul ht huJ
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp htu
  let v := gramK h b *ᵥ b.equivFun x
  have hv : ∀ j, v j ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro j
    have h1 := hx (b j) (le_locF 𝔭 _ (Submodule.subset_span ⟨j, rfl⟩))
    rw [form_repr h b] at h1
    have hb1 : b.equivFun (b j) = Pi.single j 1 := by
      funext j'
      rw [Basis.equivFun_self, Pi.single_apply]
      simp only [eq_comm]
    have hb2 : star (Pi.single j (1 : K) : κ → K) = Pi.single j 1 := by
      funext l
      by_cases hl : l = j
      · subst hl; simp
      · simp [hl]
    rwa [hb1, hb2, single_one_dotProduct] at h1
  have hx' : b.equivFun x = a *ᵥ v := by
    change b.equivFun x = (gramK h b)⁻¹ *ᵥ (gramK h b *ᵥ b.equivFun x)
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, one_mulVec]
  change f t • x ∈ locF 𝔭 (spanO b)
  rw [← b.sum_equivFun x, hx', Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨s, hs, hsj⟩ := (mem_locF 𝔭 _ _).mp (hv j)
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp hsj
  obtain ⟨z, hz⟩ := hentry i j
  refine (mem_locF 𝔭 _ _).mpr ⟨u * s, fun hm => (h𝔭.isPrime.mem_or_mem hm).elim hu hs, ?_⟩
  have hprod : g (f (u * s)) * g (f t) * (a i j * v j) = g (f w * z * y) := by
    have hw' : g (f w) * (n : K) = g (f t) * g (f u) := by
      simpa [map_mul, f, g] using congrArg (fun r => g (f r)) hw
    have hy' : g y = g (f s) * v j := hy
    calc
      _ = (g (f t) * g (f u)) * (a i j * (g (f s) * v j)) := by
        simp only [map_mul]
        ring
      _ = _ := by
        rw [map_mul, map_mul, hz, hy', ← hw']
        ring
  change f (u * s) • f t • (a i j * v j) • b i ∈ spanO b
  rw [← algebraMap_smul K (f (u * s)), ← algebraMap_smul K (f t), smul_smul, smul_smul]
  change (g (f (u * s)) * g (f t) * (a i j * v j)) • b i ∈ spanO b
  rw [hprod, show g (f w * z * y) • b i = (f w * z * y) • b i from algebraMap_smul K _ _]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem isE_eA (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    IsE h (locF 𝔭 (spanO b)) 𝔭 (eA h (locF 𝔭 (spanO b)) 𝔭) :=
  Nat.sInf_mem (s := {e | IsE h (locF 𝔭 (spanO b)) 𝔭 e}) (exists_isE hK hF hd b h𝔭)

end Formalism.HermitianLattices.Ext.L3.HU
end
end

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_isom_lift (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k)
    (X : Module.End (𝓞 K) (↥(locF 𝔭 A₀) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 A₀))))
    (hX : ∀ x y x' y' : ↥(locF 𝔭 A₀), Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = X (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) :
    ∃ g ∈ autSub h (locF 𝔭 A₀), ∀ x x' : ↥(locF 𝔭 A₀), Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      g x - x' ∈ ((extP K 𝔭) ^ (k - eA h (locF 𝔭 A₀) 𝔭) • (locF 𝔭 A₀) : Submodule (𝓞 K) V) := by
  obtain ⟨b, hbL, hb⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  obtain ⟨H, hH, -⟩ := LocF.exists_gram hA₀i b hbL
  have hd' := LocF.aniso_of_totPosDef hd
  have key : ∀ A : Submodule (𝓞 K) V, A = locF 𝔭 (integralBasisSpans.spanO b) → ∀ k : ℕ, eA h A 𝔭 + 1 ≤ k →
      ∀ X : Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)),
      (∀ x y x' y' : ↥A, Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
        Submodule.Quotient.mk y' = X (Submodule.Quotient.mk y) →
        CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) →
      ∃ g ∈ autSub h A, ∀ x x' : ↥A, Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
        g x - x' ∈ ((extP K 𝔭) ^ (k - eA h A 𝔭) • A : Submodule (𝓞 K) V) := by
    rintro _ rfl k hk X hX
    exact HU.exists_isom_lift_basis hK hF hs hd' b hH h𝔭 (HU.isE_eA hK hF hd' b h𝔭) hk X hX
  exact key _ hb.symm k hk X hX

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsIntegralAtLocF
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.GoodPrimeTerms

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open UnimodularLocalization

theorem good_term (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvL : vd h L 𝔭 = 0) (hvn : vF 𝔭 n = 0) {T : Submodule (𝓞 K) V'} (hTl : locF 𝔭 T = T)
    (hT : fibLoc S L 𝔭 T ≠ 0) : fibLoc S L 𝔭 T = 1 ∧ lamP h' T 𝔭 = 1 := by
  obtain ⟨C, hC, hCi, hvC, e⟩ :=
    exists_lattice_of_fibLoc_ne_zero_good hK hF hs hd S hL hLi h𝔭 hn hvL hvn hT
  constructor
  · rw [← fibLoc_congr S L e]
    exact fibLoc_eq_one hK hF hs hd S hL hLi hC hCi h𝔭 hn hvL hvn hvC
  · rw [← hTl, ← e, localFactor_localField hK hF (S.isSymm hs) (S.isTotPosDef hd) hC.toIsLattice hCi h𝔭]
    exact localMassFactor_of_valuation_eq_zero hK hF (S.isSymm hs) (S.isTotPosDef hd) hC hCi h𝔭 hvC

theorem good_orbit (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvL : vd h L 𝔭 = 0) (hvn : vF 𝔭 n = 0) {T T' : Submodule (𝓞 K) V'}
    (hT : fibLoc S L 𝔭 T ≠ 0) (hT' : fibLoc S L 𝔭 T' ≠ 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 T) = locF 𝔭 T' := by
  obtain ⟨C, hC, hCi, hvC, e⟩ :=
    exists_lattice_of_fibLoc_ne_zero_good hK hF hs hd S hL hLi h𝔭 hn hvL hvn hT
  obtain ⟨C', hC', hCi', hvC', e'⟩ :=
    exists_lattice_of_fibLoc_ne_zero_good hK hF hs hd S hL hLi h𝔭 hn hvL hvn hT'
  rw [← e, ← e']
  exact exists_isom_locF_of_vd_zero hK hF (S.isSymm hs) (S.isTotPosDef hd) hC hC' hCi hCi' h𝔭
    hvC hvC'

theorem isIntegralAt_locF {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {h₀ : W →ₗ⋆[K] W →ₗ[K] K} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime)
    (hF : IsFixF K F) {C : Submodule (𝓞 K) W}
    (hCi : Formalism.HermitianLatticesTheory.IsIntegralLat h₀ C) : IsIntegralAt 𝔭 h₀ (locF 𝔭 C) := by
  intro x hx y hy
  obtain ⟨s, hs, hx⟩ := (LocF.mem_locF_iff h𝔭 _ _).mp hx
  obtain ⟨t, ht, hy⟩ := (LocF.mem_locF_iff h𝔭 _ _).mp hy
  refine (LocF.mem_locF_iff h𝔭 _ _).mpr ⟨s * t, fun e => (h𝔭.mem_or_mem e).elim hs ht, ?_⟩
  have h1 := hCi _ hx _ hy
  have e : conjO K (algebraMap (𝓞 F) (𝓞 K) s) = algebraMap (𝓞 F) (𝓞 K) s :=
    (conjO_eq_iff_mem_range hF _).mpr ⟨s, rfl⟩
  have h2 : h₀ (algebraMap (𝓞 F) (𝓞 K) s • x) (algebraMap (𝓞 F) (𝓞 K) t • y) =
      (conjO K (algebraMap (𝓞 F) (𝓞 K) s) * algebraMap (𝓞 F) (𝓞 K) t) • h₀ x y := by
    have e' : algebraMap (𝓞 K) K (conjO K (algebraMap (𝓞 F) (𝓞 K) s)) =
      starRingEnd K (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) s)) := rfl
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) s) x,
      ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) y, map_smul, map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, Algebra.smul_def, map_mul, e']
    ring
  rw [h2, e, ← map_mul] at h1
  exact h1

theorem psiP_eq_one' (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvL : vd h L 𝔭 = 0) (hvn : vF 𝔭 n = 0) : psiP S L 𝔭 = 1 := by
  classical
  obtain ⟨C, hC, hCi, hvC⟩ := exists_unimod_lattice_good hK hF hs hd S hL hLi h𝔭 hn hvL hvn
  have hfC : fibLoc S L 𝔭 (locF 𝔭 C) ≠ 0 := by
    rw [fibLoc_locF, fibLoc_eq_one hK hF hs hd S hL hLi hC hCi h𝔭 hn hvL hvn hvC]
    exact one_ne_zero
  have hex : ∃ s, IsLocReps S L 𝔭 s := by
    refine ⟨{locF 𝔭 C}, ?_, ?_⟩
    · intro T hT
      rw [Finset.mem_singleton] at hT
      subst hT
      exact ⟨LocF.locF_idem _ _, isIntegralAt_locF h𝔭.isPrime hF hCi, hfC⟩
    · intro T hTl _ hT
      obtain ⟨g, hg, e⟩ := good_orbit hK hF hs hd S hL hLi h𝔭 hn hvL hvn hfC hT
      rw [LocF.locF_idem, hTl] at e
      refine ⟨locF 𝔭 C, ⟨Finset.mem_singleton_self _, g, hg, e⟩, ?_⟩
      rintro T₀ ⟨h1, -⟩
      exact Finset.mem_singleton.mp h1
  unfold psiP
  rw [dite_eq_left hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set s := hex.choose
  obtain ⟨T₀, ⟨hT₀, -⟩, -⟩ := h2 (locF 𝔭 C) (LocF.locF_idem _ _)
    (isIntegralAt_locF h𝔭.isPrime hF hCi) hfC
  have hs1 : s = {T₀} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨hT₀, fun T hT => ?_⟩
    obtain ⟨g, hg, e⟩ := good_orbit hK hF hs hd S hL hLi h𝔭 hn hvL hvn (h1 T hT).2.2
      (h1 T₀ hT₀).2.2
    rw [(h1 T hT).1, (h1 T₀ hT₀).1] at e
    obtain ⟨T₁, -, hu⟩ := h2 T₀ (h1 T₀ hT₀).1 (h1 T₀ hT₀).2.1 (h1 T₀ hT₀).2.2
    rw [hu T ⟨hT, g, hg, e⟩, hu T₀ ⟨hT₀, 1, Subgroup.one_mem _, autSub_gmap_one _⟩]
  obtain ⟨e1, e2⟩ := good_term hK hF hs hd S hL hLi h𝔭 hn hvL hvn (h1 T₀ hT₀).1 (h1 T₀ hT₀).2.2
  rw [hs1, Finset.sum_singleton, e1, e2]
  simp

end Formalism.HermitianLattices.Ext.L3.GoodPrimeTerms
end
end
