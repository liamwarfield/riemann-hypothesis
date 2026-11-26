module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SumLocRepsEq
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsEquivOfMemEndL

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsGlobalOfFibLocNeZero
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem exists_locReps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ s, IsLocReps S L 𝔭 s :=
  BrB.exists_locReps' hK hF hs hd S hL hLi h𝔭

theorem psiP_eq_sum (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {s : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s) :
    psiP S L 𝔭 = ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 :=
  BrB.psiP_eq_sum' hs S L 𝔭 hsr

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsDualBound
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem nondegenerate {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) : h.Nondegenerate := by
  have key : ∀ x : V, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have h1 := hd x hne φ
    rw [hx, map_zero, Complex.zero_re] at h1
    exact lt_irrefl _ h1
  exact ⟨fun x hx => key x (hx x), fun y hy => key y (hy y)⟩

theorem exists_dual_bound (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ e : ℕ, ∀ (k : ℕ) (x : V), (∀ y ∈ locF 𝔭 A₀, h y x ∈ pK K 𝔭 (k + e)) →
      x ∈ extP K 𝔭 ^ k • locF 𝔭 A₀ := by
  classical
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  obtain ⟨b, hb, -⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  have hnd := nondegenerate hd
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis h hnd b
  choose n hn using fun j => (by
    first | exact exists_pow_smul_mem hA₀ h𝔭 hπ (bs j)
          | exact exists_pow_smul_mem hA₀.toIsLattice h𝔭 hπ (bs j))
  refine ⟨∑ j, n j, fun k x hx => ?_⟩
  rw [Formalism.HermitianLatticesTheory.dualLattice_expand h hnd b bs hbs x]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨c, hc, e⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 (hx (b j) (LocF.le_locF 𝔭 A₀ (hb j)))
  rw [e]
  have hle : n j ≤ ∑ j, n j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  refine (mem_smul_iff_unif h𝔭 hπ hπ' A₀).2
    ⟨(c * algebraMap F K (π : F) ^ (∑ j, n j - n j)) • (algebraMap F K (π : F) ^ n j • bs j),
      smul_mem_locF h𝔭 A₀ (by simpa using mul_mem_pK h𝔭 hc (unif_pow_mem_pK_zero hπ _)) (hn j), ?_⟩
  rw [smul_smul, smul_smul]
  congr 1
  have : k + ∑ j, n j = k + (∑ j, n j - n j) + n j := by omega
  rw [this, pow_add, pow_add]; ring

theorem exists_endL_le {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsFullLattice K A₀)
    (hB₀ : Submodule.IsFullLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ r : ℕ, ∀ d : ℕ, endL (locF 𝔭 A₀) (extP K 𝔭 ^ (d + r) • locF 𝔭 A₀) ≤
      endL (locF 𝔭 B₀) (extP K 𝔭 ^ d • locF 𝔭 B₀) := by
  obtain ⟨r1, h1⟩ := (by
    first | exact exists_smul_le hA₀.toIsLattice hB₀ h𝔭
          | exact exists_smul_le hA₀.toIsLattice hB₀.toIsLattice h𝔭)
  obtain ⟨r2, h2⟩ := (by
    first | exact exists_smul_le hB₀.toIsLattice hA₀ h𝔭
          | exact exists_smul_le hB₀.toIsLattice hA₀.toIsLattice h𝔭)
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have hπ0 := unif_ne_zero (K := K) hπ'
  refine ⟨r1 + r2, fun d D hD y hy => ?_⟩
  have hy' := h2 ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨y, hy, rfl⟩)
  obtain ⟨z, hz, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 (hD _ hy')
  have hz' := h1 ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨z, hz, rfl⟩)
  refine (mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨_, hz', ?_⟩
  apply smul_right_injective V (pow_ne_zero r2 hπ0)
  show algebraMap F K (π : F) ^ r2 • D y = algebraMap F K (π : F) ^ r2 • _
  rw [← map_smul, e, smul_smul, smul_smul]
  congr 1
  rw [pow_add, pow_add]; ring

theorem nSub_le_sSub (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {A₀ : Submodule (𝓞 K) V}
    (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    nSub (locF 𝔭 A₀) 𝔭 k ≤ sSub h (locF 𝔭 A₀) 𝔭 k := by
  rintro X ⟨hX, hX'⟩
  refine ⟨hX, fun x hx y hy => ?_⟩
  have hx0 : x ∈ extP K 𝔭 ^ 0 • locF 𝔭 A₀ := by rwa [pow_zero_smul]
  have hy0 : y ∈ extP K 𝔭 ^ 0 • locF 𝔭 A₀ := by rwa [pow_zero_smul]
  have e : h (X x) (X y) - h x y = h (X x - x) y + h x (X y - y) + h (X x - x) (X y - y) := by
    simp only [map_sub, LinearMap.sub_apply]; ring
  rw [e]
  refine add_mem (add_mem ?_ ?_) ?_
  · simpa using form_mem_pK hF hA₀i h𝔭 (hX' x hx) hy0
  · simpa using form_mem_pK hF hA₀i h𝔭 hx0 (hX' y hy)
  · exact pK_anti 𝔭 (Nat.le_add_right k k) (form_mem_pK hF hA₀i h𝔭 (hX' x hx) (hX' y hy))

theorem nSub_le_glSub {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsFullLattice K A₀)
    (hB₀ : Submodule.IsFullLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, nSub (locF 𝔭 A₀) 𝔭 k ≤ glSub (locF 𝔭 B₀) := by
  obtain ⟨r, hr⟩ := exists_endL_le hA₀ hB₀ h𝔭
  refine ⟨1 + r, fun k hk X hX => ?_⟩
  apply (by
    first | exact mem_glSub_of_sub_mem (X := X) hB₀ h𝔭
          | exact mem_glSub_of_sub_mem (X := X) hB₀.toIsLattice h𝔭)
  intro y hy
  have h1 : ((X : V →ₗ[K] V) - LinearMap.id) ∈ endL (locF 𝔭 A₀) (extP K 𝔭 ^ (1 + r) • locF 𝔭 A₀) :=
    fun x hx => smul_anti 𝔭 _ hk (hX.2 x hx)
  have := hr 1 h1 y hy
  rwa [pow_one] at this

end Formalism.HermitianLattices.Ext.L3.D2
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RepMassEqProdPsi
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SumRegroup
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.MassProductFormula

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open UnimodularLocalization GoodPrimeTerms GoodGenusOrbits LocalFactorEquality


open Classical in
theorem sum_regroup (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hLfull : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c)
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s')
    {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    {A : Submodule (𝓞 K) V'} (hAfull : Submodule.IsFullLattice K A) (hAi : Formalism.HermitianLatticesTheory.IsIntegralLat h' A)
    (Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (hZL : ∀ 𝔭 ∉ Z, vd h L 𝔭.1 = 0) (hZn : ∀ 𝔭 ∉ Z, vF 𝔭.1 n = 0)
    (hZA : ∀ 𝔭 ∉ Z, vd h' A 𝔭.1 = 0)
    (s : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Finset (Submodule (𝓞 K) V'))
    (hsr : ∀ 𝔭, IsLocReps S L 𝔭.1 (s 𝔭)) :
    ∑ Λ' ∈ s', (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) =
      c * ∏ 𝔭 ∈ Z, ∑ T ∈ s 𝔭, (fibLoc S L 𝔭.1 T : ℝ) * lamP h' T 𝔭.1 := by
  have hA := hAfull.toIsLattice
  have hZ1 : ∀ 𝔭 ∉ Z, fibLoc S L 𝔭.1 A = 1 := fun 𝔭 h𝔭 =>
    fibLoc_eq_one hK hF hs hd S hLfull hLi hAfull hAi 𝔭.2 hn (hZL 𝔭 h𝔭) (hZn 𝔭 h𝔭) (hZA 𝔭 h𝔭)
  have hex : ∀ τ : ↥Z → Submodule (𝓞 K) V', τ ∈ Fintype.piFinset (fun 𝔭 : ↥Z => s 𝔭.1) →
      ∃ M, Good F S L M ∧ (∀ 𝔭 : ↥Z, locF 𝔭.1.1 M = τ 𝔭) ∧
        ∀ 𝔭 ∉ Z, locF 𝔭.1 M = locF 𝔭.1 A := by
    intro τ hτ
    rw [Fintype.mem_piFinset] at hτ
    obtain ⟨M, hM, h1, h2⟩ := exists_patch hK hF S hLfull hAfull Z
      (fun 𝔭 => if H : 𝔭 ∈ Z then τ ⟨𝔭, H⟩ else ⊥)
      (fun 𝔭 h𝔭 => by
        simp only [dif_pos h𝔭]
        exact ⟨((hsr 𝔭).1 _ (hτ ⟨𝔭, h𝔭⟩)).1, ((hsr 𝔭).1 _ (hτ ⟨𝔭, h𝔭⟩)).2.2⟩)
      (fun 𝔭 h𝔭 => by rw [hZ1 𝔭 h𝔭]; exact one_ne_zero)
    exact ⟨M, hM, fun 𝔭 => by rw [h1 𝔭.1 𝔭.2, dif_pos 𝔭.2], h2⟩
  choose! M hMg hMZ hMA using hex
  rw [← Finset.prod_coe_sort Z (fun 𝔭 => ∑ T ∈ s 𝔭, (fibLoc S L 𝔭.1 T : ℝ) * lamP h' T 𝔭.1),
    Finset.prod_univ_sum, Finset.mul_sum]
  have e1 : ∀ τ ∈ Fintype.piFinset (fun 𝔭 : ↥Z => s 𝔭.1),
      c * ∏ 𝔭 : ↥Z, ((fibLoc S L 𝔭.1.1 (τ 𝔭) : ℝ) * lamP h' (τ 𝔭) 𝔭.1.1) =
        ∑ Λ' ∈ s'.filter (fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' (M τ) Λ'),
          (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) := by
    intro τ hτ
    rw [sum_genus hK hF hs hd S hLfull hLi hc hs' hA hAi Z hZ1 hZA (hMg τ hτ) (hMA τ hτ),
      ← Finset.prod_coe_sort Z]
    congr 1
    refine Finset.prod_congr rfl fun 𝔭 _ => ?_
    rw [hMZ τ hτ 𝔭]
  rw [Finset.sum_congr rfl e1]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Λ' hΛ' => ?_
  by_cases hg : Good F S L Λ'
  · have hloc : ∀ 𝔭 : ↥Z, ∃! T₀, T₀ ∈ s 𝔭.1 ∧
        ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g T₀ = locF 𝔭.1.1 Λ' := fun 𝔭 =>
      (hsr 𝔭.1).2 _ (LocF.locF_idem _ _)
        (isIntegralAt_locF 𝔭.1.2.isPrime hF (hg.integral hF hLfull.toIsLattice hLi))
        (by rw [fibLoc_locF]; exact hg.2 𝔭.1)
    choose τ₀ hτ₀ hu using hloc
    have hmem : τ₀ ∈ Fintype.piFinset (fun 𝔭 : ↥Z => s 𝔭.1) :=
      Fintype.mem_piFinset.mpr fun 𝔭 => (hτ₀ 𝔭).1
    rw [Finset.sum_eq_single τ₀, if_pos]
    · rw [sameGenus_iff hK hF]
      intro 𝔭
      by_cases h𝔭 : 𝔭 ∈ Z
      · have := (hτ₀ ⟨𝔭, h𝔭⟩).2
        rw [hMZ τ₀ hmem ⟨𝔭, h𝔭⟩]
        exact this
      · exact good_orbit hK hF hs hd S hLfull hLi 𝔭.2 hn (hZL 𝔭 h𝔭) (hZn 𝔭 h𝔭)
          ((hMg τ₀ hmem).2 𝔭) (hg.2 𝔭)
    · intro τ hτ hne
      rw [if_neg]
      intro hsg
      apply hne
      funext 𝔭
      apply hu 𝔭
      refine ⟨Fintype.mem_piFinset.mp hτ 𝔭, ?_⟩
      have := (sameGenus_iff hK hF _ _).mp hsg 𝔭.1
      rwa [hMZ τ hτ 𝔭] at this
    · intro hc'
      exact absurd hmem hc'
  · have hlat := isFullLattice_of_fibReps S hs' hΛ'
    have : ∃ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibLoc S L 𝔭.1 Λ' = 0 := by
      by_contra hcon
      push Not at hcon
      exact hg ⟨hlat.toIsLattice, hcon⟩
    obtain ⟨𝔭, h𝔭⟩ := this
    rw [card_fibG_eq_zero hK hF hs hd S hLfull hLi hlat 𝔭 h𝔭]
    simp

theorem repMass_eq_prod_psi' (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hLfull : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c) :
    repMass h L (h S.x₀ S.x₀) =
      c * ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 := by
  classical
  have hL : Submodule.IsLattice K L := hLfull.toIsLattice
  obtain ⟨s', hs'⟩ := exists_fibReps hK hs hd S hL hLi
  rw [repMass_eq_sum_fib hK hs hd S hL hLi hs']
  by_cases H : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, ∃ T, fibLoc S L 𝔭.1 T ≠ 0
  · obtain ⟨n, hn⟩ := exists_norm_eq hF hs S hLi H
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact S.hx₀ (by rw [hn]; simp)
    have hAfull := StabilizerLattices.isFullLattice_cut S hLfull
    have hAi := isIntegralLat_cut S hLi
    have f1 := finite_vd_ne_zero hK hF hs hd hLfull hLi
    have f2 := finite_vF_ne_zero hn0
    have f3 := finite_vd_ne_zero hK hF (S.isSymm hs) (S.isTotPosDef hd) hAfull hAi
    set Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
      f1.toFinset ∪ f2.toFinset ∪ f3.toFinset with hZ
    have hZL : ∀ 𝔭 ∉ Z, vd h L 𝔭.1 = 0 := by
      intro 𝔭 h𝔭
      by_contra h0
      exact h𝔭 (by simp only [hZ, Finset.mem_union, Set.Finite.mem_toFinset]; exact Or.inl (Or.inl h0))
    have hZn : ∀ 𝔭 ∉ Z, vF 𝔭.1 n = 0 := by
      intro 𝔭 h𝔭
      by_contra h0
      exact h𝔭 (by simp only [hZ, Finset.mem_union, Set.Finite.mem_toFinset]; exact Or.inl (Or.inr h0))
    have hZA : ∀ 𝔭 ∉ Z, vd h' (S.cut L) 𝔭.1 = 0 := by
      intro 𝔭 h𝔭
      by_contra h0
      exact h𝔭 (by simp only [hZ, Finset.mem_union, Set.Finite.mem_toFinset]; exact Or.inr h0)
    choose T hT using H
    obtain ⟨M₀, hM₀, -, -⟩ := exists_patch hK hF S hLfull hAfull Z (fun 𝔭 => locF 𝔭.1 (T 𝔭))
      (fun 𝔭 _ => ⟨LocF.locF_idem _ _, by rw [fibLoc_locF]; exact hT 𝔭⟩)
      (fun 𝔭 h𝔭 => by
        rw [fibLoc_eq_one hK hF hs hd S hLfull hLi hAfull hAi 𝔭.2 hn (hZL 𝔭 h𝔭) (hZn 𝔭 h𝔭) (hZA 𝔭 h𝔭)]
        exact one_ne_zero)
    have hex := fun 𝔭 => GoodGenusOrbits.exists_locReps hK hF hs hd S hLfull hLi hM₀ 𝔭
    rw [sum_regroup hK hF hs hd S hLfull hLi hc hs' hn hAfull hAi Z hZL hZn hZA
      (fun 𝔭 => (hex 𝔭).choose) (fun 𝔭 => (hex 𝔭).choose_spec)]
    congr 1
    rw [tprod_eq_prod (s := Z) (fun 𝔭 h𝔭 =>
      psiP_eq_one' hK hF hs hd S hLfull hLi 𝔭.2 hn (hZL 𝔭 h𝔭) (hZn 𝔭 h𝔭))]
    exact Finset.prod_congr rfl fun 𝔭 _ => (psiP_eq S L 𝔭.1 (hex 𝔭)).symm
  · push Not at H
    obtain ⟨𝔭, H⟩ := H
    rw [tprod_of_exists_eq_zero ⟨𝔭, psiP_eq_zero S L 𝔭.1 H⟩, mul_zero]
    refine Finset.sum_eq_zero fun Λ' hΛ' => ?_
    rw [card_fibG_eq_zero hK hF hs hd S hLfull hLi (isFullLattice_of_fibReps S hs' hΛ') 𝔭 (H Λ')]
    simp

end Formalism.HermitianLattices.Ext.L3.MassProductFormula
end
end

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem repMass_eq_prod_psi (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c) :
    repMass h L (h S.x₀ S.x₀) = c * ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 :=
  MassProductFormula.repMass_eq_prod_psi' hK hF hs hd S (by first | exact hL | exact hL.toIsLattice) hLi hc

end Formalism.HermitianLattices.Ext.L3
end
end
