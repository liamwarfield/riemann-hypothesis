module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DifferentIdealEqTop

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsVecOfHermRep
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

def perpSpace (h : V →ₗ⋆[K] V →ₗ[K] K) (x₀ : V) : Submodule K V := LinearMap.ker (h x₀)

def perpForm (h : V →ₗ⋆[K] V →ₗ[K] K) (x₀ : V) :
    ↥(perpSpace h x₀) →ₗ⋆[K] ↥(perpSpace h x₀) →ₗ[K] K :=
  (h.comp (perpSpace h x₀).subtype).compl₂ (perpSpace h x₀).subtype

def vecSplitPerp (h : V →ₗ⋆[K] V →ₗ[K] K) {x₀ : V} (hx : h x₀ x₀ ≠ 0) :
    VecSplit h (perpForm h x₀) where
  x₀ := x₀
  ι := (perpSpace h x₀).subtype
  inj := Subtype.val_injective
  hx₀ := hx
  isom := fun _ _ => rfl
  orth := fun a => LinearMap.mem_ker.mp a.2
  cover := fun v => by
    refine ⟨h x₀ v / h x₀ x₀, ⟨v - (h x₀ v / h x₀ x₀) • x₀, ?_⟩, ?_⟩
    · change v - (h x₀ v / h x₀ x₀) • x₀ ∈ LinearMap.ker (h x₀)
      rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hx, sub_self]
    · simp

private theorem star_sesq_eq_swap_of_isSymm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (a b : V) :
    star (h a b) = h b a := by
  first | exact hs a b | exact hs.eq a b

theorem VecSplit.finrank_add_one {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (S : VecSplit h h') : finrank K V' + 1 = finrank K V := by
  let f : K × V' →ₗ[K] V := LinearMap.coprod (LinearMap.toSpanSingleton K V S.x₀) S.ι
  have hf : Function.Bijective f := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨c, a⟩ hca
      have h1 : c • S.x₀ + S.ι a = 0 := by simpa [f] using hca
      have h2 : h S.x₀ (c • S.x₀ + S.ι a) = 0 := by rw [h1, map_zero]
      rw [map_add (f := _), map_smul, S.orth, add_zero, smul_eq_mul] at h2
      have hc : c = 0 := (mul_eq_zero.mp h2).resolve_right S.hx₀
      subst hc
      have h3 : S.ι a = 0 := by simpa using h1
      have ha : a = 0 := S.inj (by rw [h3, map_zero])
      simp [ha]
    · intro v
      obtain ⟨c, a, hv⟩ := S.cover v
      exact ⟨(c, a), by simp [f, hv]⟩
  have := (LinearEquiv.ofBijective f hf).finrank_eq
  rw [Module.finrank_prod, Module.finrank_self] at this
  omega

theorem finrank_perpSpace {h : V →ₗ⋆[K] V →ₗ[K] K} {x₀ : V} (hx : h x₀ x₀ ≠ 0) :
    finrank K (perpSpace h x₀) + 1 = finrank K V :=
  VecSplit.finrank_add_one (vecSplitPerp h hx)

theorem VecSplit.isTotPosDef {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (S : VecSplit h h') (hd : IsTotPosDef h) : IsTotPosDef h' := by
  intro a ha φ
  rw [← S.isom]
  exact hd _ (fun h0 => ha (S.inj (by rw [h0, map_zero]))) φ

theorem VecSplit.isSymm {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (S : VecSplit h h') (hs : h.IsSymm) : h'.IsSymm := by
  have H : ∀ a b : V', star (h' a b) = h' b a := by
    intro a b
    rw [← S.isom, ← S.isom]
    exact star_sesq_eq_swap_of_isSymm hs _ _
  first | exact H | exact ⟨H⟩

theorem exists_vec_of_hermRep (hH : HermRepUnram) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) (hV : 2 ≤ finrank K V)
    (n : K) (hn : star n = n) (hpos : TotPos n) : ∃ x : V, h x x = n := by
  have hne : ∀ x : V, x ≠ 0 → h x x ≠ 0 := by
    intro x hx h0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd x hx φ
    rw [h0, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (by omega)
  have hfr := finrank_perpSpace (h := h) (hne x hx)
  obtain ⟨y', hy'⟩ : ∃ y : ↥(perpSpace h x), y ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (by omega)
  have hy0 : y'.1 ≠ 0 := fun h0 => hy' (Subtype.ext h0)
  have hxy : h x y'.1 = 0 := LinearMap.mem_ker.mp y'.2
  have hyx : h y'.1 x = 0 := by rw [← star_sesq_eq_swap_of_isSymm hs, hxy, star_zero]
  obtain ⟨s, t, hst⟩ := hH K hK (h x x) (h y'.1 y'.1) n (star_sesq_eq_swap_of_isSymm hs x x) (star_sesq_eq_swap_of_isSymm hs _ _) hn
    (fun φ => hd x hx φ) (fun φ => hd _ hy0 φ) hpos
  refine ⟨star s • x + star t • y'.1, ?_⟩
  simp only [map_add (f := _), map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    hxy, hyx, starRingEnd_apply, star_star]
  linear_combination hst

theorem VecSplit.le_dual_of_mem {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (hs : h.IsSymm) (S : VecSplit h h') {Λ : Submodule (𝓞 K) V}
    (hΛ : Formalism.HermitianLatticesTheory.IsIntegralLat h Λ) (hx : S.x₀ ∈ Λ) :
    S.adjoin (S.cut Λ) ≤ Λ ∧ Λ ≤ Formalism.HermitianLatticesTheory.dual h (S.adjoin (S.cut Λ)) := by
  have hle : S.adjoin (S.cut Λ) ≤ Λ :=
    sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) (Submodule.map_comap_le _ _)
  refine ⟨hle, fun x hx' => ?_⟩
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
  intro y hy
  exact hΛ y (hle hy) x hx'

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocF

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]

section Gen

variable {W : Type} [AddCommGroup W] [Module (𝓞 K) W]

theorem mem_closure_iff {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (s : 𝓞 K) :
    s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} ↔
      ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s := by
  constructor
  · intro hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨1, (Ideal.ne_top_iff_one 𝔭).mp hp.ne_top, map_one _⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨t, ht, rfl⟩ := iha
      obtain ⟨u, hu, rfl⟩ := ihb
      exact ⟨t * u, fun h => (hp.mem_or_mem h).elim ht hu, map_mul _ _ _⟩
  · intro hs
    exact Submonoid.subset_closure hs

theorem mem_locF_iff {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ locF 𝔭 L ↔ ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • x ∈ L := by
  unfold locF
  rw [Formalism.HermitianLatticesTheory.locBasic_mem_locS]
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨t, ht, rfl⟩ := (mem_closure_iff hp s).mp hs
    exact ⟨t, ht, hx⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨_, (mem_closure_iff hp _).mpr ⟨t, ht, rfl⟩, hx⟩

theorem le_locF (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) W) : L ≤ locF 𝔭 L :=
  Formalism.HermitianLatticesTheory.locBasic_le_locS _ L

theorem locF_mono (𝔭 : Ideal (𝓞 F)) {L M : Submodule (𝓞 K) W} (h : L ≤ M) :
    locF 𝔭 L ≤ locF 𝔭 M :=
  Formalism.HermitianLatticesTheory.locBasic_locS_mono _ h

theorem locF_idem (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) W) :
    locF 𝔭 (locF 𝔭 L) = locF 𝔭 L :=
  Formalism.HermitianLatticesTheory.locBasic_locS_idem _ L

theorem iInf_locF (L : Submodule (𝓞 K) W) :
    (⨅ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, locF 𝔭.1 L) = L := by
  apply le_antisymm
  · intro x hx
    by_contra hxL
    let I : Ideal (𝓞 F) := Ideal.comap (algebraMap (𝓞 F) (𝓞 K))
      (Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) W x) L)
    have hmem : ∀ r : 𝓞 F, r ∈ I ↔ algebraMap (𝓞 F) (𝓞 K) r • x ∈ L := by
      intro r
      simp [I]
    have hI : I ≠ ⊤ := by
      intro h
      apply hxL
      have h1 : (1 : 𝓞 F) ∈ I := h ▸ Submodule.mem_top
      simpa using (hmem 1).mp h1
    obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
    have h2 := (Submodule.mem_iInf _).mp hx ⟨p, hp⟩
    obtain ⟨t, ht, htx⟩ := (mem_locF_iff hp.isPrime L x).mp h2
    exact ht (hIp ((hmem t).mpr htx))
  · exact le_iInf fun 𝔭 => le_locF 𝔭.1 L

end Gen

theorem exists_prime_to_part {c : 𝓞 F} (hc : c ≠ 0) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsMaximal) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 F), 𝔮.IsMaximal → 𝔮 ≠ 𝔭 → ∃ u : 𝓞 F, u ∉ 𝔮 ∧ c ∣ u * t := by
  have hc' : Ideal.span {c} ≠ (0 : Ideal (𝓞 F)) := by
    simpa using hc
  have hu : ¬ IsUnit 𝔭 := by
    rw [Ideal.isUnit_iff]
    exact hp.ne_top
  obtain ⟨𝔟, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hu hc').exists_eq_pow_mul_and_not_dvd
  rw [Ideal.dvd_iff_le] at hnd
  obtain ⟨t, htb, htp⟩ := SetLike.not_le_iff_exists.mp hnd
  refine ⟨t, htp, fun 𝔮 hq hne => ?_⟩
  have h1 : ¬ 𝔭 ^ multiplicity 𝔭 (Ideal.span {c}) ≤ 𝔮 := by
    intro hle
    exact hne (hp.eq_of_le hq.ne_top (hq.isPrime.le_of_pow_le hle)).symm
  obtain ⟨u, hu1, hu2⟩ := SetLike.not_le_iff_exists.mp h1
  refine ⟨u, hu2, ?_⟩
  rw [← Ideal.mem_span_singleton, hb]
  exact Ideal.mul_mem_mul hu1 htb

section Lat

variable [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_zsmul_le {A B : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A)
    (hB : Submodule.IsFullLattice K B) : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ A, n • x ∈ B := by
  obtain ⟨S, hS⟩ := hA.fg
  choose n hn hnx using fun x : V => Formalism.HermitianLatticesTheory.traceReal_mult B hB x
  refine ⟨∏ x ∈ S, n x, Finset.prod_ne_zero_iff.mpr fun x _ => hn x, fun x hx => ?_⟩
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem n hy
    rw [hm, mul_comm, mul_smul]
    exact zsmul_mem (hnx y) m
  | zero => rw [smul_zero]; exact B.zero_mem
  | add y z _ _ hy hz => rw [smul_add]; exact B.add_mem hy hz
  | smul a y _ hy => rw [smul_comm]; exact B.smul_mem a hy

theorem algebraMap_intCast_smul (n : ℤ) (x : V) :
    algebraMap (𝓞 F) (𝓞 K) (n : 𝓞 F) • x = n • x := by
  rw [map_intCast, Int.cast_smul_eq_zsmul]

theorem patch {L₀ : Submodule (𝓞 K) V} (hL₀ : Submodule.IsFullLattice K L₀)
    (s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (B : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V)
    (hB : ∀ 𝔭, Submodule.IsFullLattice K (B 𝔭)) (hBs : ∀ 𝔭 ∉ s, B 𝔭 = L₀) :
    Submodule.IsLattice K (⨅ 𝔭, locF 𝔭.1 (B 𝔭)) ∧
      ∀ 𝔭, locF 𝔭.1 (⨅ 𝔮, locF 𝔮.1 (B 𝔮)) = locF 𝔭.1 (B 𝔭) := by
  classical
  choose n₁ hn₁ hn₁x using fun 𝔭 => exists_zsmul_le (hB 𝔭).toIsLattice hL₀
  choose n₂ hn₂ hn₂x using fun 𝔭 => exists_zsmul_le hL₀.toIsLattice (hB 𝔭)
  obtain ⟨N, hN, hN1, hN2⟩ : ∃ N : ℤ, N ≠ 0 ∧ (∀ 𝔭, ∀ x ∈ B 𝔭, N • x ∈ L₀) ∧
      ∀ 𝔭, ∀ x ∈ L₀, N • x ∈ B 𝔭 := by
    refine ⟨∏ 𝔭 ∈ s, (n₁ 𝔭 * n₂ 𝔭),
      Finset.prod_ne_zero_iff.mpr fun 𝔭 _ => mul_ne_zero (hn₁ 𝔭) (hn₂ 𝔭), ?_, ?_⟩
    · intro 𝔭 x hx
      by_cases h𝔭 : 𝔭 ∈ s
      · obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun 𝔭 => n₁ 𝔭 * n₂ 𝔭) h𝔭
        rw [hm, show n₁ 𝔭 * n₂ 𝔭 * m = (n₂ 𝔭 * m) * n₁ 𝔭 by ring, mul_smul]
        exact zsmul_mem (hn₁x 𝔭 x hx) _
      · rw [hBs 𝔭 h𝔭] at hx
        exact zsmul_mem hx _
    · intro 𝔭 x hx
      by_cases h𝔭 : 𝔭 ∈ s
      · obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun 𝔭 => n₁ 𝔭 * n₂ 𝔭) h𝔭
        rw [hm, show n₁ 𝔭 * n₂ 𝔭 * m = (n₁ 𝔭 * m) * n₂ 𝔭 by ring, mul_smul]
        exact zsmul_mem (hn₂x 𝔭 x hx) _
      · rw [hBs 𝔭 h𝔭]
        exact zsmul_mem hx _
  set Λ : Submodule (𝓞 K) V := ⨅ 𝔭, locF 𝔭.1 (B 𝔭) with hΛ
  have hΛle : ∀ 𝔭, Λ ≤ locF 𝔭.1 (B 𝔭) := fun 𝔭 => iInf_le _ 𝔭
  have h2 : ∀ x ∈ L₀, N • x ∈ Λ := by
    intro x hx
    rw [hΛ, Submodule.mem_iInf]
    exact fun 𝔭 => le_locF 𝔭.1 _ (hN2 𝔭 x hx)
  have h3 : ∀ x ∈ Λ, N • x ∈ L₀ := by
    intro x hx
    rw [← iInf_locF (F := F) L₀, Submodule.mem_iInf]
    intro 𝔭
    obtain ⟨t, ht, htx⟩ := (mem_locF_iff 𝔭.2.isPrime _ x).mp (hΛle 𝔭 hx)
    refine (mem_locF_iff 𝔭.2.isPrime _ _).mpr ⟨t, ht, ?_⟩
    rw [smul_comm]
    exact hN1 𝔭 _ htx
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · let φ : V →ₗ[𝓞 K] V := N • LinearMap.id
    have hφ : Function.Injective φ := by
      intro x y hxy
      have : N • x = N • y := hxy
      rw [← Int.cast_smul_eq_zsmul K, ← Int.cast_smul_eq_zsmul K] at this
      exact smul_right_injective V hNK this
    apply Submodule.fg_of_fg_map_injective φ hφ
    have hle : Λ.map φ ≤ L₀ := by
      rintro _ ⟨x, hx, rfl⟩
      exact h3 x hx
    exact hL₀.fg.of_le hle
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · intro 𝔭
    apply le_antisymm
    · calc locF 𝔭.1 Λ ≤ locF 𝔭.1 (locF 𝔭.1 (B 𝔭)) := locF_mono _ (hΛle 𝔭)
        _ = _ := locF_idem _ _
    · intro x hx
      obtain ⟨t₀, ht₀, hy⟩ := (mem_locF_iff 𝔭.2.isPrime _ x).mp hx
      have hc : ((N * N : ℤ) : 𝓞 F) ≠ 0 := by
        exact_mod_cast mul_ne_zero hN hN
      obtain ⟨t, ht, hq⟩ := exists_prime_to_part hc 𝔭.2
      refine (mem_locF_iff 𝔭.2.isPrime _ x).mpr
        ⟨t * t₀, fun h => (𝔭.2.isPrime.mem_or_mem h).elim ht ht₀, ?_⟩
      rw [map_mul, mul_smul]
      generalize algebraMap (𝓞 F) (𝓞 K) t₀ • x = y at hy
      have hcy : (N * N) • y ∈ Λ := by
        rw [mul_smul]
        exact h2 _ (hN1 𝔭 y hy)
      rw [hΛ, Submodule.mem_iInf]
      intro 𝔮
      by_cases hqp : 𝔮 = 𝔭
      · rw [hqp]
        exact Submodule.smul_mem _ _ (le_locF _ _ hy)
      · obtain ⟨u, hu, d, hd⟩ := hq 𝔮.1 𝔮.2 (fun h => hqp (Subtype.ext h))
        rw [← locF_idem]
        refine (mem_locF_iff 𝔮.2.isPrime _ _).mpr ⟨u, hu, ?_⟩
        rw [← mul_smul, ← map_mul, hd, mul_comm, map_mul, mul_smul, algebraMap_intCast_smul]
        exact Submodule.smul_mem _ _ (hΛle 𝔮 hcy)

end Lat

end Formalism.HermitianLattices.Ext.L3.LocF
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsBasisLocF
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocalSpans

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

abbrev sF (K : Type) {F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : Submonoid (𝓞 K) :=
  Algebra.algebraMapSubmonoid (𝓞 K) 𝔭.primeCompl

theorem closure_eq (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] :
    Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} = sF K 𝔭 := by
  have : {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} = (sF K 𝔭 : Set (𝓞 K)) := by
    ext s
    rfl
  rw [this, Submonoid.closure_eq]

theorem mem_locF {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime]
    (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ locF 𝔭 L ↔ ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • x ∈ L := by
  unfold locF
  rw [closure_eq]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, h⟩
    exact ⟨t, ht, h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨_, ⟨t, ht, rfl⟩, h⟩

theorem sF_le (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : sF K 𝔭 ≤ nonZeroDivisors (𝓞 K) :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ 𝔭.primeCompl_le_nonZeroDivisors

abbrev RP (K : Type) {F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (sF K 𝔭) (sF_le 𝔭)

theorem mem_span_RP (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (N : Submodule (𝓞 K) V) (x : V) :
    x ∈ Submodule.span (RP K 𝔭) (N : Set V) ↔ x ∈ locF 𝔭 N := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact (mem_locF 𝔭 N x).2 ⟨1, fun h => (Ideal.ne_top_iff_one 𝔭).1 (Ideal.IsPrime.ne_top inferInstance) h, by simpa using hx⟩
    | zero => exact (locF 𝔭 N).zero_mem
    | add x y _ _ hx hy => exact (locF 𝔭 N).add_mem hx hy
    | smul c x _ hx =>
      obtain ⟨a, s, ⟨t, ht, rfl⟩, hc⟩ := c.2
      obtain ⟨u, hu, hx⟩ := (mem_locF 𝔭 N x).1 hx
      refine (mem_locF 𝔭 N _).2 ⟨t * u, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ht hu, ?_⟩
      have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
        intro h0
        have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
        have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
        exact ht (h2 ▸ 𝔭.zero_mem)
      have : algebraMap (𝓞 F) (𝓞 K) (t * u) • c • x = a • (algebraMap (𝓞 F) (𝓞 K) u • x) := by
        rw [Subalgebra.smul_def, hc, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) (t * u)),
          ← algebraMap_smul K a, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) u), smul_smul, smul_smul,
          map_mul, map_mul]
        congr 1
        field_simp
      rw [this]
      exact N.smul_mem _ hx
  · intro hx
    obtain ⟨t, ht, hx⟩ := (mem_locF 𝔭 N x).1 hx
    have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
      intro h0
      have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
      have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
      exact ht (h2 ▸ 𝔭.zero_mem)
    let c : RP K 𝔭 := ⟨(algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹,
      ⟨1, _, ⟨t, ht, rfl⟩, by simp⟩⟩
    have : x = c • (algebraMap (𝓞 F) (𝓞 K) t • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t), smul_smul,
        inv_mul_cancel₀ ht0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

theorem exists_basis_locF {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ b : Basis (Fin (finrank K V)) K V, (∀ i, b i ∈ L) ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L := by
  have : 𝔭.IsPrime := h𝔭.isPrime
  have hp0 : 𝔭 ≠ ⊥ := fun h => RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.2 (h ▸ h𝔭))
  have : IsDedekindDomain (RP K 𝔭) := IsLocalization.isDedekindDomain (𝓞 K) (sF_le 𝔭) _
  have : IsPrincipalIdealRing (RP K 𝔭) :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K) 𝔭 hp0
  let M : Submodule (RP K 𝔭) V := Submodule.span (RP K 𝔭) (L : Set V)
  have hMfg : M.FG := by
    obtain ⟨s, hs⟩ := hL.fg
    refine ⟨s, ?_⟩
    show _ = Submodule.span (RP K 𝔭) (L : Set V)
    rw [← hs, Submodule.span_span_of_tower]
  have : Submodule.IsFullLattice K M :=
    { toIsLattice := Submodule.IsLattice.of_fg K hMfg
      span_eq_top := by
        rw [eq_top_iff, ← hL.span_eq_top]
        exact Submodule.span_mono Submodule.subset_span }
  have : Module.Free (RP K 𝔭) M := Submodule.IsLattice.free K M
  have : Module.Finite (RP K 𝔭) M := Submodule.IsLattice.finite K M
  let b0 := Module.Free.chooseBasis (RP K 𝔭) M
  let b1 := b0.extendOfIsFullLattice K
  have hb1 : ∀ i, b1 i = (b0 i : V) := fun i => Basis.extendOfIsFullLattice_apply K b0 i
  have hmem : ∀ i, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • b1 i ∈ L := fun i => by
    rw [← mem_locF, ← mem_span_RP, hb1]
    exact (b0 i).2
  choose t ht htL using hmem
  have ht0 : ∀ i, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)) ≠ 0 := by
    intro i h0
    have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
    have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
    exact ht i (h2 ▸ 𝔭.zero_mem)
  let b2 := b1.unitsSMul fun i => Units.mk0 _ (ht0 i)
  have hb2 : ∀ i, b2 i = algebraMap (𝓞 F) (𝓞 K) (t i) • b1 i := fun i => by
    rw [Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, algebraMap_smul]
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b2).symm
  refine ⟨b2.reindex e, fun i => ?_, ?_⟩
  · rw [Basis.reindex_apply, hb2]
    exact htL _
  · ext x
    rw [← mem_span_RP, ← mem_span_RP, Submodule.span_span_of_tower, Basis.range_reindex]
    have : Submodule.span (RP K 𝔭) (Set.range b2) = M := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [hb2]
        exact Submodule.subset_span (htL i)
      · have h1 : M = Submodule.map M.subtype (Submodule.span (RP K 𝔭) (Set.range b0)) := by
          rw [b0.span_eq, Submodule.map_top, Submodule.range_subtype]
        refine h1.le.trans ?_
        rw [Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        let c : RP K 𝔭 := ⟨(algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)))⁻¹,
          ⟨1, _, ⟨t i, ht i, rfl⟩, by simp⟩⟩
        have : M.subtype (b0 i) = c • b2 i := by
          rw [hb2, Subalgebra.smul_def, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) (t i)), smul_smul,
            inv_mul_cancel₀ (ht0 i), one_smul, hb1]
          rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [this]

end Formalism.HermitianLattices.Ext.L3.LocalSpans
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SigmaCount
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

section Defs

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def eA (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) : ℕ :=
  sInf {e : ℕ | ∀ x : V, (∀ y ∈ A, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) →
    ∀ t ∈ 𝔭 ^ e, algebraMap (𝓞 F) (𝓞 K) t • x ∈ A}

def repRatio (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F) : ℝ :=
  (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vd h L 𝔭) * alphaN h L 𝔭 n / alphaL h L 𝔭

end Defs

def LIRatio : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
      [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K)
      (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (S : VecSplit h h') (L L₀ : Submodule (𝓞 K) V)
      (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F),
      h.IsSymm → IsTotPosDef h → 𝔭.IsMaximal → n ≠ 0 → h S.x₀ S.x₀ = algebraMap F K (n : F) →
      Submodule.IsFullLattice K L → Formalism.HermitianLatticesTheory.IsIntegralLat h L →
      Submodule.IsFullLattice K L₀ → Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ →
      psiP S L 𝔭 * repRatio h L₀ 𝔭 n = psiP S L₀ 𝔭 * repRatio h L 𝔭 n

def LIPin : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
      [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K)
      (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (S : VecSplit h h') (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F),
      h.IsSymm → IsTotPosDef h → 𝔭.IsMaximal → n ≠ 0 → h S.x₀ S.x₀ = algebraMap F K (n : F) →
      ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsFullLattice K L₀ ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ ∧
        repRatio h L₀ 𝔭 n ≠ 0 ∧
        psiP S L₀ 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vF 𝔭 n) *
          alphaStd K 𝔭 (finrank K V - 1) * repRatio h L₀ 𝔭 n

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormEqProdOfMem
open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

def rEmb (w : {w : InfinitePlace F // w.IsReal}) : 𝓞 F →+* ℝ :=
  (InfinitePlace.embedding_of_isReal w.2).comp (algebraMap (𝓞 F) F)

theorem rEmb_apply (w : {w : InfinitePlace F // w.IsReal}) (n : 𝓞 F) :
    rEmb w n = InfinitePlace.embedding_of_isReal w.2 (n : F) := rfl

theorem mem_boxSet_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F} :
    n ∈ boxSet K F T ↔ ∀ w : {w : InfinitePlace F // w.IsReal}, 0 < rEmb w n ∧ rEmb w n ≤ T := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  constructor
  · intro h w
    let _ : Algebra F ℂ := w.1.embedding.toAlgebra
    let φ : K →ₐ[F] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    have h1 : φ (algebraMap F K (n : F)) = w.1.embedding (n : F) := φ.commutes _
    have h2 := h φ.toRingHom
    have h3 : (φ.toRingHom (algebraMap F K (n : F))).re = rEmb w n := by
      show (φ (algebraMap F K (n : F))).re = _
      rw [h1, rEmb_apply, ← InfinitePlace.embedding_of_isReal_apply w.2, Complex.ofReal_re]
    rwa [h3] at h2
  · intro h φ
    have hw : (InfinitePlace.mk (φ.comp (algebraMap F K))).IsReal := IsTotallyReal.isReal _
    have h1 := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hw)
    have h3 : (φ (algebraMap F K (n : F))).re = rEmb ⟨_, hw⟩ n := by
      rw [rEmb_apply, ← Complex.ofReal_re (InfinitePlace.embedding_of_isReal _ _),
        InfinitePlace.embedding_of_isReal_apply hw, h1]
      rfl
    rw [h3]
    exact h _

theorem absNorm_eq_prod [IsTotallyReal F] (n : 𝓞 F) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) = ∏ w : {w : InfinitePlace F // w.IsReal}, |rEmb w n| := by
  have h1 : (Ideal.absNorm (Ideal.span {n}) : ℝ) = |((Algebra.norm ℚ (n : F) : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, ← Algebra.coe_norm_int]
    push_cast
    rfl
  rw [h1, ← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
  have h2 : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  rw [Finset.prod_subtype (p := fun w : InfinitePlace F => w.IsReal) Finset.univ (by simp [h2])
    (fun w => w (n : F) ^ w.mult)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [w.2.mult_eq_one, pow_one, rEmb_apply, ← Real.norm_eq_abs,
    InfinitePlace.norm_embedding_of_isReal]

theorem absNorm_eq_prod_of_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) = ∏ w : {w : InfinitePlace F // w.IsReal}, rEmb w n := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  rw [absNorm_eq_prod]
  exact Finset.prod_congr rfl fun w _ => abs_of_pos (((mem_boxSet_iff hK hF).1 hn) w).1

theorem card_real (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    Fintype.card {w : InfinitePlace F // w.IsReal} = Formalism.HermitianLatticesTheory.fDeg K := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  have h1 := (discrTower K F hK hF).2.1
  rw [← h1, IsTotallyReal.finrank]

theorem finite_boxSet (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) :
    (boxSet K F T).Finite := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  have h0 := Embeddings.finite_of_norm_le F ℂ T
  refine Set.Finite.of_finite_image (f := fun n : 𝓞 F => (n : F)) (h0.subset ?_)
    (RingOfIntegers.coe_injective.injOn)
  rintro _ ⟨n, hn, rfl⟩
  refine ⟨n.2, fun ψ => ?_⟩
  have hw : (InfinitePlace.mk ψ).IsReal := IsTotallyReal.isReal _
  have h1 := ((mem_boxSet_iff hK hF).1 hn) ⟨_, hw⟩
  have h2 : ‖ψ (n : F)‖ = |rEmb ⟨_, hw⟩ n| := by
    rw [rEmb_apply, ← Real.norm_eq_abs, InfinitePlace.norm_embedding_of_isReal]
    rfl
  rw [h2, abs_of_pos h1.1]
  exact h1.2

theorem ne_zero_of_mem_boxSet {T : ℝ} {n : 𝓞 F} (hn : n ∈ boxSet K F T) : n ≠ 0 := by
  rintro rfl
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have := (hn φ).1
  simp at this

theorem absNorm_le_of_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) ≤ T ^ Formalism.HermitianLatticesTheory.fDeg K := by
  rw [absNorm_eq_prod_of_mem hK hF hn, ← card_real hK hF, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun w _ => (((mem_boxSet_iff hK hF).1 hn) w).1.le)
    fun w _ => (((mem_boxSet_iff hK hF).1 hn) w).2

end Formalism.HermitianLattices.Ext.L3.BoxSum
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FinitePrimesOfMem
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.A5

variable {F : Type} [Field F] [NumberField F]

theorem ne_bot_of_max {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)

theorem two_le_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 2 ≤ Ideal.absNorm 𝔭 :=
  (IdealNormInequalities.resChar_prime h𝔭).two_le.trans (IdealNormInequalities.resChar_le_absNorm h𝔭)

theorem summable_inv_absNorm_sq :
    Summable fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => ((Ideal.absNorm 𝔭.1 : ℝ) ^ 2)⁻¹ := by
  refine Summable.of_nonneg_of_le (fun 𝔭 => by positivity) (fun 𝔭 => ?_)
    (IdealNormInequalities.summable_resChar_sq (K := F))
  have h1 : (0 : ℝ) < (IdealNormInequalities.resChar 𝔭.1 : ℝ) := by
    exact_mod_cast (IdealNormInequalities.resChar_prime 𝔭.2).pos
  have h2 : (IdealNormInequalities.resChar 𝔭.1 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
    exact_mod_cast IdealNormInequalities.resChar_le_absNorm 𝔭.2
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h1.le h2 2)

theorem absNorm_span_ne_zero {n : 𝓞 F} (hn : n ≠ 0) : Ideal.absNorm (Ideal.span {n}) ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hn

theorem lt_of_mem_pow {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {e : ℕ}
    (he : n ∈ 𝔭 ^ e) : e < Ideal.absNorm (Ideal.span {n}) := by
  have h1 : Ideal.span {n} ≤ 𝔭 ^ e := (Ideal.span_singleton_le_iff_mem _).mpr he
  have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero (absNorm_span_ne_zero hn))
    (Ideal.absNorm_dvd_absNorm_of_le h1)
  rw [map_pow] at h2
  calc e < 2 ^ e := Nat.lt_two_pow_self
    _ ≤ Ideal.absNorm 𝔭 ^ e := Nat.pow_le_pow_left (two_le_absNorm h𝔭) e
    _ ≤ _ := h2

theorem mem_pow_iff_le_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (e : ℕ) :
    n ∈ 𝔭 ^ e ↔ e ≤ vF 𝔭 n := by
  have hb : BddAbove {e : ℕ | n ∈ 𝔭 ^ e} :=
    ⟨Ideal.absNorm (Ideal.span {n}), fun e he => (lt_of_mem_pow h𝔭 hn he).le⟩
  constructor
  · intro he
    exact le_csSup hb he
  · intro he
    have hm : vF 𝔭 n ∈ {e : ℕ | n ∈ 𝔭 ^ e} := Nat.sSup_mem ⟨0, by simp⟩ hb
    exact Ideal.pow_le_pow_right he hm

theorem finite_primes_of_mem {n : 𝓞 F} (hn : n ≠ 0) :
    {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} | n ∈ 𝔭.1}.Finite := by
  refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
  refine (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) (Ideal.absNorm (Ideal.span {n}))).subset ?_
  rintro _ ⟨𝔭, h𝔭, rfl⟩
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (absNorm_span_ne_zero hn))
    (Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr h𝔭))


open scoped Classical in
def valF (n : 𝓞 F) : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ :=
  if hn : n ≠ 0 then
    Finsupp.onFinset (finite_primes_of_mem hn).toFinset (fun 𝔭 => vF 𝔭.1 n) (fun 𝔭 h => by
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      have := (mem_pow_iff_le_vF 𝔭.2 hn 1).mpr (Nat.one_le_iff_ne_zero.mpr h)
      simpa using this)
  else 0

theorem valF_apply {n : 𝓞 F} (hn : n ≠ 0) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    valF n 𝔭 = vF 𝔭.1 n := by
  unfold valF
  rw [dite_eq_left hn]
  rfl

def bId (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) : Ideal (𝓞 F) := v.prod fun 𝔭 e => 𝔭.1 ^ e

theorem bId_ne_bot (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) : bId v ≠ ⊥ := by
  unfold bId Finsupp.prod
  rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  exact fun 𝔭 _ => pow_ne_zero _ (ne_bot_of_max 𝔭.2)

theorem absNorm_bId (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) :
    (Ideal.absNorm (bId v) : ℝ) = nrm (fun 𝔭 => (Ideal.absNorm 𝔭.1 : ℝ)) v := by
  unfold bId nrm Finsupp.prod
  rw [map_prod]
  push_cast
  simp only [map_pow, Nat.cast_pow]

theorem mem_bId_iff {n : 𝓞 F} (hn : n ≠ 0) (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) :
    n ∈ bId v ↔ v ≤ valF n := by
  unfold bId Finsupp.prod
  rw [← IsDedekindDomain.inf_pow_eq_prod_of_prime v.support (fun 𝔭 => 𝔭.1) v
    (fun 𝔭 _ => Ideal.prime_of_isPrime (ne_bot_of_max 𝔭.2) 𝔭.2.isPrime)
    (fun 𝔭 _ 𝔮 _ h => fun h' => h (Subtype.ext h')), Submodule.mem_finsetInf]
  constructor
  · intro h 𝔭
    by_cases h𝔭 : 𝔭 ∈ v.support
    · rw [valF_apply hn]
      exact (mem_pow_iff_le_vF 𝔭.2 hn _).mp (h 𝔭 h𝔭)
    · rw [Finsupp.notMem_support_iff.mp h𝔭]; exact Nat.zero_le _
  · intro h 𝔭 _
    have := h 𝔭
    rw [valF_apply hn] at this
    exact (mem_pow_iff_le_vF 𝔭.2 hn _).mpr this

theorem bId_sup_eq_top {v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ}
    {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}} (h𝔭 : 𝔭 ∉ v.support) : bId v ⊔ 𝔭.1 = ⊤ := by
  by_contra hne
  have hle : bId v ≤ 𝔭.1 := by
    have h1 : 𝔭.1 ≤ bId v ⊔ 𝔭.1 := le_sup_right
    have h2 := 𝔭.2.eq_of_le hne h1
    rw [h2]
    exact le_sup_left
  unfold bId Finsupp.prod at hle
  obtain ⟨𝔮, h𝔮, hle'⟩ := (Ideal.IsPrime.prod_le 𝔭.2.isPrime).mp hle
  have := 𝔭.2.isPrime
  have h3 : 𝔮.1 ≤ 𝔭.1 := Ideal.IsPrime.le_of_pow_le hle'
  have h4 : 𝔮.1 = 𝔭.1 := 𝔮.2.eq_of_le 𝔭.2.ne_top h3
  exact h𝔭 (Subtype.ext h4 ▸ h𝔮)

theorem exists_vF_eq {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (j : ℕ) :
    ∃ n : 𝓞 F, n ≠ 0 ∧ vF 𝔭 n = j := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hn'⟩ := SetLike.exists_of_lt (Ideal.pow_succ_lt_pow (ne_bot_of_max h𝔭) j)
  have h0 : n ≠ 0 := fun h => hn' (h ▸ Ideal.zero_mem _)
  refine ⟨n, h0, le_antisymm ?_ ((mem_pow_iff_le_vF h𝔭 h0 j).mp hn)⟩
  by_contra hlt
  exact hn' ((mem_pow_iff_le_vF h𝔭 h0 (j + 1)).mpr (by omega))

end Formalism.HermitianLattices.Ext.L3.A5
end
end
