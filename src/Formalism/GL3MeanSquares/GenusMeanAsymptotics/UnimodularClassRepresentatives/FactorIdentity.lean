module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSingSSum
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulEqUnifPow
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulSpanIff

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FactorIdentity
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormSpanEqProd
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem BrA.normD_eq_tprod (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    normD h L = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1 := by
  have hD := LocF.discrIdeal_ne_bot (LocF.aniso_of_totPosDef hd) hL hLi
  have hD' : BrA.discrF F h L ≠ ⊥ := by
    intro e
    apply hD
    rw [BrA.discrIdeal_eq_map hF hs, e, Ideal.map_bot]
  rw [BrA.normD_eq hK hF hs, BrA.absNorm_eq_tprod hD']
  exact tprod_congr fun 𝔭 => by rw [BrA.vd_eq hF hs]

theorem integral_of_mem_genus (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {M : Submodule (𝓞 K) V} (hM : M ∈ Formalism.HermitianLatticesTheory.genus h L) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h M ∧ (∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → vd h M 𝔭 = vd h L 𝔭) ∧
      normD h M = normD h L := by
  obtain ⟨hMl, hMg⟩ := hM
  have key : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 M := by
    intro 𝔭 h𝔭
    obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
    rw [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    exact hMg P hP
  have hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M := by
    intro x hx y hy
    rw [← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K), Submodule.mem_iInf]
    intro 𝔭
    obtain ⟨g, hg, e⟩ := key 𝔭.1 𝔭.2
    exact BrA.form_mem_locF hF hLi 𝔭.2.isPrime hg (e ▸ LocF.le_locF 𝔭.1 M hx)
      (e ▸ LocF.le_locF 𝔭.1 M hy)
  have hvd : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → vd h M 𝔭 = vd h L 𝔭 := by
    intro 𝔭 h𝔭
    obtain ⟨g, hg, e⟩ := key 𝔭 h𝔭
    rw [← localizedQuotients.vd_locF hF h M h𝔭, ← localizedQuotients.vd_locF hF h L h𝔭, ← e]
    unfold vd
    rw [BrA.discrIdeal_gmap hg]
  refine ⟨hMi, hvd, ?_⟩
  rw [BrA.normD_eq_tprod hK hF hs hd hMl hMi, BrA.normD_eq_tprod hK hF hs hd hL hLi]
  exact tprod_congr fun 𝔭 => by rw [hvd 𝔭.1 𝔭.2]

theorem normD_eq_prod (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    normD h L = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1 :=
  BrA.normD_eq_tprod hK hF hs hd hL hLi

theorem absNorm_span_eq_prod (n : 𝓞 F) (hn : n ≠ 0) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ vF 𝔭.1 n := by
  have hI : Ideal.span {n} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [BrA.absNorm_eq_tprod hI]
  refine tprod_congr fun 𝔭 => ?_
  unfold vF
  simp only [Ideal.span_singleton_le_iff_mem]

end Formalism.HermitianLattices.Ext.L3
end
end

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Step

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V V' : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

theorem alphaStd_succ (𝔭 : Ideal (𝓞 F)) {m : ℕ} (hm : 1 ≤ m) :
    alphaStd K 𝔭 m = alphaStd K 𝔭 (m - 1) * A5.eFac K m 𝔭 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  unfold alphaStd A5.eFac
  rw [Finset.prod_Icc_succ_top (by omega)]
  simp

theorem factor_identity (q aS e aL aN : ℝ) (m a b : ℕ) (hm : 1 ≤ m) (hq : q ≠ 0) (he : e ≠ 0)
    (hL : aL ≠ 0) :
    q ^ ((m - 1) * (a + b)) * aS * aN / aL =
      (q ^ a) ^ (m - 1) * (aS * e * q ^ (m * b) / aL) * (q ^ b)⁻¹ * (aN / e) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

theorem tprod_localPsi_eq (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V} (hLfull : Submodule.IsFullLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn0 : n ≠ 0)
    (hn : h S.x₀ S.x₀ = algebraMap F K (n : F)) :
    ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 =
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * lamG F h L * (normD h L)⁻¹ *
        singS F h L n := by
  classical
  set U : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
    (finite_vd_ne_zero (F := F) hK hF hs hd hLfull hLi).toFinset ∪ (A5.finite_primes_of_mem hn0).toFinset
    with hU
  have hU1 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ U → vd h L 𝔭.1 = 0 := by
    intro 𝔭 h𝔭
    rw [hU, Finset.mem_union, not_or, Set.Finite.mem_toFinset] at h𝔭
    exact not_not.mp h𝔭.1
  have hU2 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ U → n ∉ 𝔭.1 := by
    intro 𝔭 h𝔭
    rw [hU, Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at h𝔭
    exact h𝔭.2
  have hU3 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ U → vF 𝔭.1 n = 0 := by
    intro 𝔭 h𝔭
    by_contra hne
    have := (A5.mem_pow_iff_le_vF 𝔭.2 hn0 1).mpr (Nat.one_le_iff_ne_zero.mpr hne)
    rw [pow_one] at this
    exact hU2 𝔭 h𝔭 this
  have hpt : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 =
      ((Ideal.absNorm 𝔭.1 : ℝ) ^ vF 𝔭.1 n) ^ (finrank K V - 1) * lamP h L 𝔭.1 *
        ((Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1)⁻¹ *
        (alphaN h L 𝔭.1 n / (1 - etaF K F 𝔭.1 ^ finrank K V *
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ)))) := by
    intro 𝔭
    rw [hLI K F hK hF V V' h h' S L 𝔭.1 n hs hd 𝔭.2 hn0 hn hLfull hLi]
    unfold lamP
    rw [alphaStd_succ 𝔭.1 hm]
    have hq : (Ideal.absNorm 𝔭.1 : ℝ) ≠ 0 := by
      have := A5.two_le_absNorm 𝔭.2
      positivity
    exact factor_identity _ _ _ _ _ _ _ _ hm hq (A5.eFac_pos 𝔭.2 hm).ne'
      (alphaL_pos hK hF hs hd hLfull hLi 𝔭.2).ne'
  have e1 : (Ideal.absNorm (Ideal.span {n}) : ℝ) =
      ∏ 𝔭 ∈ U, (Ideal.absNorm 𝔭.1 : ℝ) ^ vF 𝔭.1 n := by
    rw [absNorm_span_eq_prod n hn0]
    exact tprod_eq_prod fun 𝔭 h𝔭 => by rw [hU3 𝔭 h𝔭, pow_zero]
  have e2 : lamG F h L = ∏ 𝔭 ∈ U, lamP h L 𝔭.1 := by
    unfold lamG
    exact tprod_eq_prod fun 𝔭 h𝔭 => localMassFactor_of_valuation_eq_zero hK hF hs hd hLfull hLi 𝔭.2 (hU1 𝔭 h𝔭)
  have e3 : normD h L = ∏ 𝔭 ∈ U, (Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1 := by
    rw [normD_eq_prod hK hF hs hd hLfull hLi]
    exact tprod_eq_prod fun 𝔭 h𝔭 => by rw [hU1 𝔭 h𝔭, pow_zero]
  have h4 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ U →
      alphaN h L 𝔭.1 n / (1 - etaF K F 𝔭.1 ^ finrank K V *
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ))) = 1 := by
    intro 𝔭 h𝔭
    rw [alphaN_of_vd_zero_unit hK hF hs hd hLfull hLi 𝔭.2 (hU1 𝔭 h𝔭) hm (hU2 𝔭 h𝔭)]
    exact div_self (A5.eFac_pos 𝔭.2 hm).ne'
  have e4 : singS F h L n = ∏ 𝔭 ∈ U, alphaN h L 𝔭.1 n / (1 - etaF K F 𝔭.1 ^ finrank K V *
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ))) := by
    unfold singS
    exact tprod_eq_prod h4
  have e0 : ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 = ∏ 𝔭 ∈ U, psiP S L 𝔭.1 := by
    refine tprod_eq_prod fun 𝔭 h𝔭 => ?_
    rw [hpt 𝔭, hU3 𝔭 h𝔭, hU1 𝔭 h𝔭, h4 𝔭 h𝔭, localMassFactor_of_valuation_eq_zero hK hF hs hd hLfull hLi 𝔭.2 (hU1 𝔭 h𝔭)]
    simp
  rw [e0, e1, e2, e3, e4, ← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun 𝔭 _ => hpt 𝔭

theorem repMass_eq (hH : HermRepUnram) (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (hm : 2 ≤ finrank K V) {c : ℝ} (hc : MassConst K F (finrank K V - 1) c) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    repMass h L (algebraMap F K (n : F)) = c * lamG F h L * (normD h L)⁻¹ *
      ((Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * singS F h L n) := by
  have hn0 : n ≠ 0 := A5.ne_zero_of_mem_boxSet hn
  obtain ⟨x₀, hx₀⟩ := exists_vec_of_hermRep hH hK hs hd hm (algebraMap F K (n : F))
    ((hF _).mpr ⟨_, rfl⟩) (fun φ => (hn φ).1)
  have hne : h x₀ x₀ ≠ 0 := by
    rw [hx₀]
    intro e
    apply hn0
    apply RingOfIntegers.ext
    exact (algebraMap F K).injective (by rw [e]; simp)
  have h1 := repMass_eq_prod_psi (F := F) hK hF hs hd (vecSplitPerp h hne) hL hLi hc
  have h2 := tprod_localPsi_eq hLI hK hF hs hd (vecSplitPerp h hne) hL hLi (by omega) hn0 hx₀
  rw [h2] at h1
  have h3 : h (vecSplitPerp h hne).x₀ (vecSplitPerp h hne).x₀ = algebraMap F K (n : F) := hx₀
  rw [h3] at h1
  rw [h1]
  ring

end Formalism.HermitianLattices.Ext.L3.Step
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RelIndexEqOfMap
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem relIndex_eq_of_map {G M : Type*} [Group G] [AddCommGroup M] (H G' : Subgroup G)
    (N P : AddSubgroup M) (φ : G → M) (h1 : ∀ x ∈ G', φ x ∈ P) (h2 : ∀ p ∈ P, ∃ x ∈ G', φ x = p)
    (h3 : ∀ x ∈ G', ∀ y ∈ G', x⁻¹ * y ∈ H ↔ φ y - φ x ∈ N) : H.relIndex G' = N.relIndex P := by
  classical
  rw [Subgroup.relIndex, AddSubgroup.relIndex, Subgroup.index, AddSubgroup.index]

  have hrel : ∀ a b : G', (a⁻¹ * b ∈ H.subgroupOf G') ↔
      (-(⟨φ a, h1 a a.2⟩ : P) + ⟨φ b, h1 b b.2⟩ ∈ N.addSubgroupOf P) := by
    intro a b
    rw [Subgroup.mem_subgroupOf, AddSubgroup.mem_addSubgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, AddSubgroup.coe_add, AddSubgroup.coe_neg, neg_add_eq_sub]
    exact h3 a a.2 b b.2
  let f : G' ⧸ H.subgroupOf G' → P ⧸ N.addSubgroupOf P :=
    Quotient.map' (fun x : G' => (⟨φ x, h1 x x.2⟩ : P)) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab
      rw [QuotientAddGroup.leftRel_apply]
      exact (hrel a b).1 hab)
  refine Nat.card_congr (Equiv.ofBijective f ⟨fun a b hab => ?_, fun p => ?_⟩)
  · induction a using QuotientGroup.induction_on with
    | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
    have hab' : ((⟨φ a, h1 a a.2⟩ : P) : P ⧸ N.addSubgroupOf P) = ((⟨φ b, h1 b b.2⟩ : P) : _) := hab
    rw [QuotientAddGroup.eq] at hab'
    exact QuotientGroup.eq.2 ((hrel a b).2 hab')
  · induction p using QuotientAddGroup.induction_on with
    | H p =>
    obtain ⟨x, hx, hφ⟩ := h2 p p.2
    refine ⟨((⟨x, hx⟩ : G') : G' ⧸ H.subgroupOf G'), ?_⟩
    change ((⟨φ x, h1 x hx⟩ : P) : P ⧸ N.addSubgroupOf P) = (p : _)
    congr 1
    exact Subtype.ext hφ

theorem relIndex_nSub_eq {A₀ B₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hB₀ : Submodule.IsFullLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ k₀ : ℕ, ∀ k ≥ k₀, nSub (locF 𝔭 B₀) 𝔭 (k + c) ≤ nSub (locF 𝔭 A₀) 𝔭 k ∧
      endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) ≤ endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀) ∧
      (nSub (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (nSub (locF 𝔭 A₀) 𝔭 k) =
        (endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀)).relIndex
          (endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀)) := by
  obtain ⟨r, hr⟩ := exists_endL_le hB₀ hA₀ h𝔭
  obtain ⟨k₁, hk₁⟩ := nSub_le_glSub hA₀ hB₀ h𝔭
  refine ⟨r, fun c hc => ⟨max k₁ 1, fun k hk => ?_⟩⟩
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk

  have hle : endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) ≤
      endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀) := by
    intro D hD
    refine hr k ?_
    intro x hx
    exact smul_anti 𝔭 _ (by omega) (hD x hx)

  have hlift : ∀ D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀),
      ∃ X ∈ nSub (locF 𝔭 A₀) 𝔭 k, (X : V →ₗ[K] V) - LinearMap.id = D := by
    intro D hD
    have hD1 : D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀) := by
      intro x hx
      have := smul_anti 𝔭 (locF 𝔭 A₀) hk1 (hD x hx)
      rwa [pow_one] at this
    obtain ⟨X, hX, hXg⟩ := exists_equiv_of_mem_endL hA₀ h𝔭 hD1
    refine ⟨X, mem_nSub.2 ⟨hXg, fun x hx => ?_⟩, ?_⟩
    · rw [hX, add_sub_cancel_left]
      exact hD x hx
    · ext v
      simp [hX]
  have hnsub : nSub (locF 𝔭 B₀) 𝔭 (k + c) ≤ nSub (locF 𝔭 A₀) 𝔭 k := by
    intro X hXm
    obtain ⟨hXB, hX⟩ := mem_nSub.1 hXm
    have hD : (X : V →ₗ[K] V) - LinearMap.id ∈ endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) := by
      intro x hx
      simpa using hX x hx
    obtain ⟨X', hX'm, hX'⟩ := hlift _ (hle hD)
    have hXX : X' = X := by
      ext v
      have := LinearMap.congr_fun hX' v
      simpa using this
    rw [← hXX]
    exact hX'm
  refine ⟨hnsub, hle, ?_⟩
  refine relIndex_eq_of_map _ _ _ _ (fun X => (X : V →ₗ[K] V) - LinearMap.id) (fun X hX => ?_)
    (fun D hD => ?_) (fun x hx y hy => ?_)
  · intro v hv
    simpa using (mem_nSub.1 hX).2 v hv
  · obtain ⟨X, hXm, hX⟩ := hlift D hD
    exact ⟨X, hXm, hX⟩
  · have hxB : x ∈ glSub (locF 𝔭 B₀) := hk₁ k (le_trans (le_max_left _ _) hk) hx
    have hyB : y ∈ glSub (locF 𝔭 B₀) := hk₁ k (le_trans (le_max_left _ _) hk) hy
    have hxyB : x⁻¹ * y ∈ glSub (locF 𝔭 B₀) := mul_mem (inv_mem hxB) hyB
    have e1 : ∀ v : V, x (x⁻¹ v) = v := fun v => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    rw [mem_nSub]
    constructor
    · rintro ⟨_, h⟩ v hv
      have h' := apply_mem_smul hxB _ (h v hv)
      have e2 : x ((x⁻¹ * y) v - v) = y v - x v := by
        rw [map_sub, LinearEquiv.mul_apply, e1]
      rw [e2] at h'
      simpa using h'
    · intro h
      refine ⟨hxyB, fun v hv => ?_⟩
      have h' := apply_mem_smul (inv_mem hxB) _ (h v hv)
      have e2 : x⁻¹ ((((y : V →ₗ[K] V) - LinearMap.id) - ((x : V →ₗ[K] V) - LinearMap.id) :
          V →ₗ[K] V) v) =
          (x⁻¹ * y) v - v := by
        simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, sub_sub_sub_cancel_right,
          map_sub, LinearEquiv.mul_apply]
        rw [← LinearEquiv.mul_apply x⁻¹ x, inv_mul_cancel]
        rfl
      rw [e2] at h'
      exact h'

theorem relIndex_endL (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {A₀ B₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hB₀ : Submodule.IsFullLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k c : ℕ}
    (hle : endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) ≤
      endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀)) :
    (endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀)).relIndex
        (endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀)) =
      Ideal.absNorm 𝔭 ^ (2 * finrank K V ^ 2 * c) := by
  classical
  obtain ⟨a, b, e, c0, hc0, he, hA, hB, hbe⟩ := exists_smith hA₀ hB₀ h𝔭
  have hinj := IsFractionRing.injective (𝓞 K) K
  set eK : Fin (finrank K V) → K := fun i => algebraMap (𝓞 K) K (e i) with heKdef
  set c0K : K := algebraMap (𝓞 K) K c0 with hc0Kdef
  have heK : ∀ i, eK i ≠ 0 := fun i => (map_ne_zero_iff _ hinj).2 (he i)
  have hc0K : c0K ≠ 0 := (map_ne_zero_iff _ hinj).2 hc0
  have hbeK : ∀ i, c0K • b i = eK i • a i := fun i => by
    simp only [c0K, eK, algebraMap_smul]
    exact hbe i
  have hab : ∀ l, a l = (c0K / eK l) • b l := fun l => by
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, hbeK l, smul_smul, inv_mul_cancel₀ (heK l), one_smul]
  have hba : ∀ j, b j = (eK j / c0K) • a j := fun j => by
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← hbeK j, smul_smul, inv_mul_cancel₀ hc0K, one_smul]

  have key : ∀ (D : V →ₗ[K] V) i j, LinearMap.toMatrix b b D i j * eK i =
      eK j * LinearMap.toMatrix a a D i j := by
    intro D i j
    have h2 : D (a j) = ∑ l, (LinearMap.toMatrix a a D l j * (c0K / eK l)) • b l := by
      conv_lhs => rw [← a.sum_repr (D (a j))]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [LinearMap.toMatrix_apply, ← smul_smul, ← hab l]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.toMatrix_apply b b, hba j, map_smul, h2, map_smul, Finsupp.smul_apply, map_sum,
      Finsupp.finsetSum_apply]
    simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    field_simp [heK i, hc0K]
  let φA : (V →ₗ[K] V) →+ Matrix (Fin (finrank K V)) (Fin (finrank K V)) K :=
    (LinearMap.toMatrix a a).toLinearMap.toAddMonoidHom
  have hφA : Function.Surjective φA := (LinearMap.toMatrix a a).surjective
  have hEA : endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀) =
      (matL 𝔭 k (fun _ _ => (1 : K)) (fun _ _ => 1)).comap φA := by
    ext D
    rw [AddSubgroup.mem_comap, ← hA, mem_endL_iff a h𝔭]
    constructor
    · intro h i j
      exact ⟨_, h i j, by simp [φA]⟩
    · intro h i j
      obtain ⟨w, hw, hw'⟩ := h i j
      simp only [one_mul, φA] at hw'
      rw [show LinearMap.toMatrix a a D i j = w from hw']
      exact hw
  have hEB : endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) =
      (matL 𝔭 (k + c) (fun _ j => eK j) (fun i _ => eK i)).comap φA := by
    ext D
    rw [AddSubgroup.mem_comap, ← hB, mem_endL_iff b h𝔭]
    constructor
    · intro h i j
      refine ⟨_, h i j, ?_⟩
      simp only [φA, LinearEquiv.coe_toLinearMap, LinearMap.toAddMonoidHom_coe]
      rw [← key, mul_comm]
    · intro h i j
      obtain ⟨w, hw, hw'⟩ := h i j
      simp only [φA, LinearEquiv.coe_toLinearMap, LinearMap.toAddMonoidHom_coe] at hw'
      rw [← key, mul_comm] at hw'
      rw [mul_left_cancel₀ (heK i) hw']
      exact hw
  rw [hEA, hEB] at hle ⊢
  have hle' : matL 𝔭 (k + c) (fun _ j => eK j) (fun i _ => eK i) ≤
      matL 𝔭 k (fun _ _ => (1 : K)) (fun _ _ => 1) := by
    intro M hM
    obtain ⟨D, rfl⟩ := hφA M
    exact hle hM
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hφA]
  have hmat := relIndex_matL hK hF h𝔭 (fun _ j => eK j) (fun i _ => eK i)
    (fun _ j => ⟨algebraMap_mem_pK 𝔭 _, heK j⟩) (fun i _ => ⟨algebraMap_mem_pK 𝔭 _, heK i⟩) k c hle'
  rw [Finset.prod_comm] at hmat
  have hP : (∏ i : Fin (finrank K V), ∏ _j : Fin (finrank K V), nO 𝔭 (eK i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun _ _ =>
      nO_ne_zero hK hF h𝔭 (algebraMap_mem_pK 𝔭 _) (heK i)
  rw [mul_comm _ (Ideal.absNorm 𝔭 ^ _)] at hmat
  simpa [Fintype.card_fin] using Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hP) hmat

theorem relIndex_nSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {A₀ B₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hB₀ : Submodule.IsFullLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ k₀ : ℕ, ∀ k ≥ k₀, nSub (locF 𝔭 B₀) 𝔭 (k + c) ≤ nSub (locF 𝔭 A₀) 𝔭 k ∧
      (nSub (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (nSub (locF 𝔭 A₀) 𝔭 k) =
        Ideal.absNorm 𝔭 ^ (2 * finrank K V ^ 2 * c) := by
  obtain ⟨c₀, hc₀⟩ := relIndex_nSub_eq hA₀ hB₀ h𝔭
  refine ⟨c₀, fun c hc => ?_⟩
  obtain ⟨k₀, hk₀⟩ := hc₀ c hc
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hk₀ k hk
  exact ⟨h1, h3.trans (relIndex_endL hK hF hA₀ hB₀ h𝔭 h2)⟩

end Formalism.HermitianLattices.Ext.L3.D2
end
end
