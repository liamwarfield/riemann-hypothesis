module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountSplitOne
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DifferentIdealEqTop

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountEqEulerFacInert
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace C2

theorem geom_of_step (c : ℕ → ℕ) (a : ℕ) (h : ∀ k, 1 ≤ k → c (k + 1) = a * c k) (k : ℕ)
    (hk : 1 ≤ k) : c k = a ^ (k - 1) * c 1 := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [h n hn, ih, show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
    ring

theorem cast_geom (c : ℕ → ℕ) (q N : ℕ) (X : ℝ) (h : ∀ k, 1 ≤ k → c (k + 1) = q ^ N * c k)
    (h1 : (c 1 : ℝ) = (q : ℝ) ^ N * X) (k : ℕ) (hk : 1 ≤ k) :
    (c k : ℝ) = (q : ℝ) ^ (N * k) * X := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [geom_of_step c (q ^ N) h (j + 1) hk]
  push_cast
  rw [h1]
  ring

theorem inert_alg (q : ℝ) (hq : q ≠ 0) (M : ℕ) (hM : 1 ≤ M) :
    q ^ (M - 1) * (q ^ M - (-1) ^ M) = q ^ (2 * M - 1) * (1 - (-1 : ℝ) ^ M * q ^ (-(M : ℤ))) := by
  obtain ⟨j, rfl⟩ : ∃ j, M = j + 1 := ⟨M - 1, by omega⟩
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, Nat.add_sub_cancel, zpow_neg]
  rw [show ((j + 1 : ℕ) : ℤ) = ((j + 1 : ℕ) : ℤ) from rfl, zpow_natCast]
  field_simp
  ring

theorem split_alg (q : ℝ) (hq : q ≠ 0) (M : ℕ) (hM : 1 ≤ M) :
    q ^ (2 * M - 1) - q ^ (M - 1) = q ^ (2 * M - 1) * (1 - q ^ (-(M : ℤ))) := by
  obtain ⟨j, rfl⟩ : ∃ j, M = j + 1 := ⟨M - 1, by omega⟩
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, Nat.add_sub_cancel, zpow_neg]
  rw [show ((j + 1 : ℕ) : ℤ) = ((j + 1 : ℕ) : ℤ) from rfl, zpow_natCast]
  field_simp
  ring

end C2

theorem localDensity : LocalDensity := by
  intro K _ _ _ hK P hP M k hM hk n hn hnP
  have hPbot : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have hN0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hPbot
  constructor
  · intro hc
    obtain ⟨q, hq⟩ := exists_sq_absNorm_of_inert hK hP hc
    have hq0 : (q : ℝ) ≠ 0 := by
      intro h0
      have h1 : q = 0 := by exact_mod_cast h0
      rw [h1] at hq
      exact hN0 (by simpa using hq)
    have hsq : Real.sqrt (Ideal.absNorm P : ℝ) = q := by
      rw [hq]
      push_cast
      exact Real.sqrt_sq (Nat.cast_nonneg q)
    rw [hsq]
    have h1 : ((normRepCount K (P ^ 1) M n : ℕ) : ℝ) =
        (q : ℝ) ^ (2 * M - 1) * (1 - (-1 : ℝ) ^ M * (q : ℝ) ^ (-(M : ℤ))) := by
      rw [pow_one]
      have h3 := normRepCount_inert_one hK hP hc M hM n hn hnP q hq
      have h2 : ((normRepCount K P M n : ℕ) : ℝ) = (q : ℝ) ^ (M - 1) * ((q : ℝ) ^ M - (-1) ^ M) := by
        exact_mod_cast h3
      rw [h2, C2.inert_alg _ hq0 M hM]
    exact C2.cast_geom (fun j => normRepCount K (P ^ j) M n) q (2 * M - 1) _
      (fun j hj => normRepCount_pow_succ_inert hK hP hc M j hM hj n hn hnP q hq) h1 k hk
  · intro hc
    have hN : ((Ideal.absNorm P : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN0
    have h1 : ((normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ 1) M n : ℕ) : ℝ) =
        (Ideal.absNorm P : ℝ) ^ (2 * M - 1) * (1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ))) := by
      rw [pow_one]
      have h3 := normRepCount_split_one hK hP hc M hM n hn hnP
      have h2 : ((normRepCount K (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) M n : ℕ) : ℝ) =
          (Ideal.absNorm P : ℝ) ^ (2 * M - 1) - (Ideal.absNorm P : ℝ) ^ (M - 1) := by
        exact_mod_cast h3
      rw [h2, C2.split_alg _ hN M hM]
    exact C2.cast_geom (fun j => normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ j) M n)
      (Ideal.absNorm P) (2 * M - 1) _
      (fun j hj => normRepCount_pow_succ_split hK hP hc M j hM hj n hn hnP) h1 k hk

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem normRepCount_eq_eulerFac_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) :
    (normRepCount K (P ^ k) M n : ℝ) =
      Real.sqrt (Ideal.absNorm P : ℝ) ^ ((2 * M - 1) * k) * (Formalism.HermitianLatticesTheory.eulerFac K M P)⁻¹ := by
  rw [(localDensity K hK P hP M k hM hk n hn hnP).1 hc, Formalism.HermitianLatticesTheory.eulerFac, if_pos hc, inv_inv]

theorem normRepCount_eq_eulerFac_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) :
    (normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ k) M n : ℝ) =
      (Ideal.absNorm P : ℝ) ^ ((2 * M - 1) * k) *
        (Formalism.HermitianLatticesTheory.eulerFac K M P * Formalism.HermitianLatticesTheory.eulerFac K M (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P))⁻¹ := by
  have hc' : Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ≠ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P :=
    fun h => hc ((conjIdeal_conjIdeal hK P).symm.trans h).symm
  have hPbot : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have hN0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hPbot
  have hN1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hP.ne_top
  have hN2 : (1 : ℝ) < (Ideal.absNorm P : ℝ) := by
    have : 2 ≤ Ideal.absNorm P := by omega
    exact_mod_cast (by omega : 1 < Ideal.absNorm P)
  have hx : 0 < 1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) := by
    rw [zpow_neg, zpow_natCast, sub_pos]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hN2 (by omega))
  rw [(localDensity K hK P hP M k hM hk n hn hnP).2 hc, Formalism.HermitianLatticesTheory.eulerFac, Formalism.HermitianLatticesTheory.eulerFac, if_neg hc,
    if_neg hc', absNorm_conjIdeal hK, ← Real.rpow_add hx,
    show (-(1 : ℝ) / 2 + -(1 : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one, inv_inv]

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LValEtaEqLValEtaF
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace Regroup

theorem tprod_eq_of_fibre {α β : Type*} {f : α → ℝ} (π : α → β) {g : β → ℝ} (hf : Multipliable f)
    (hg : ∀ b, HasProd (fun c : {x // π x = b} => f c.1) (g b)) : ∏' a, f a = ∏' b, g b := by
  have h1 : HasProd (fun p : (Σ b : β, {x // π x = b}) => f (Equiv.sigmaFiberEquiv π p))
      (∏' a, f a) := (Equiv.sigmaFiberEquiv π).hasProd_iff.2 hf.hasProd
  exact (HasProd.sigma h1 hg).tprod_eq.symm

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem comap_isMaximal {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
  haveI : P.IsMaximal := hP
  Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := 𝓞 F) P

theorem hasProd_fibre (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (M : ℕ) (hM : 1 ≤ M)
    (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    HasProd (fun c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} => Formalism.HermitianLatticesTheory.eulerFac K M c.1.1)
      (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹ := by
  classical
  obtain ⟨P, hP, hP𝔭⟩ := exists_maximal_over hK hF 𝔭.2
  have hmem : ∀ c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭},
      c.1.1 = P ∨ c.1.1 = Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    intro c
    have h1 : c.1.1.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.1 := congrArg Subtype.val c.2
    exact (comap_eq_comap_iff hK hF hP c.1.2).1 (hP𝔭.trans h1.symm)
  have heta := etaF_comap hK hF hP
  rw [hP𝔭] at heta
  let c0 : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} := ⟨⟨P, hP⟩, Subtype.ext hP𝔭⟩
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · have hN := absNorm_comap_inert hK hF hP hc
    rw [hP𝔭] at hN
    have hval : Formalism.HermitianLatticesTheory.eulerFac K M P =
        (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹ := by
      rw [← inv_inv (Formalism.HermitianLatticesTheory.eulerFac K M P), eulerFac_inv_inert hK hP hc, heta, if_pos hc, ← hN]
      push_cast
      rw [Real.sqrt_sq (Nat.cast_nonneg _)]
    have h := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (f := fun c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} => Formalism.HermitianLatticesTheory.eulerFac K M c.1.1) (s := {c0})
      (by
        intro b hb
        exfalso
        apply hb
        rw [Finset.mem_singleton]
        apply Subtype.ext
        apply Subtype.ext
        rcases hmem b with h | h
        · exact h
        · exact h.trans hc)
    rw [Finset.prod_singleton] at h
    rw [← hval]
    exact h
  · have hN := absNorm_comap_split hK hF hP hc
    rw [hP𝔭] at hN
    have hPb := conjIdeal_isMaximal hK hP
    have hPb𝔭 : (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.1 := by
      rw [← hP𝔭]
      exact ((comap_eq_comap_iff hK hF hP hPb).2 (Or.inr rfl)).symm
    let c1 : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} :=
      ⟨⟨Formalism.HermitianLatticesTheory.conjIdeal (K := K) P, hPb⟩, Subtype.ext hPb𝔭⟩
    have hne : c0 ≠ c1 := by
      intro h
      exact hc (congrArg (fun c => c.1.1) h).symm
    have hval : Formalism.HermitianLatticesTheory.eulerFac K M P * Formalism.HermitianLatticesTheory.eulerFac K M (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) =
        (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹ := by
      rw [← inv_inv (Formalism.HermitianLatticesTheory.eulerFac K M P * _), eulerFac_mul_conj_inv_split hK hP hc M hM, heta,
        if_neg hc, hN, one_pow, one_mul]
    have h := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (f := fun c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} => Formalism.HermitianLatticesTheory.eulerFac K M c.1.1) (s := {c0, c1})
      (by
        intro b hb
        exfalso
        apply hb
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases hmem b with h | h
        · exact Or.inl (Subtype.ext (Subtype.ext h))
        · exact Or.inr (Subtype.ext (Subtype.ext h)))
    rw [Finset.prod_pair hne] at h
    rw [← hval]
    exact h

end Regroup

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem lValEta_eq_lValEtaF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (M : ℕ) (hM : 2 ≤ M) :
    Formalism.HermitianLatticesTheory.lValEta K M = lValEtaF K F M := by
  unfold Formalism.HermitianLatticesTheory.lValEta lValEtaF
  exact Regroup.tprod_eq_of_fibre
    (fun x : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), Regroup.comap_isMaximal x.2⟩ :
        {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}))
    (multipliable_eulerFac hK M hM) (Regroup.hasProd_fibre hK hF M (by omega))

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandG
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace GramDeterminantPositive

section

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem exists_ortho_ne_zero [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {k : ℕ}
    (v : Fin k → V) (hk : k < finrank K V) : ∃ x : V, x ≠ 0 ∧ ∀ i, h (v i) x = 0 := by
  let f : V →ₗ[K] (Fin k → K) := LinearMap.pi fun i => h (v i)
  have hlt : finrank K (Fin k → K) < finrank K V := by
    rw [Module.finrank_fin_fun]; exact hk
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
  exact ⟨x, hx0, fun i => congrFun (LinearMap.mem_ker.1 hx) i⟩

theorem exists_basis_of_ortho [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {k : ℕ}
    (v : Fin k → V) (hk : finrank K V = k) (ho : ∀ i j, i ≠ j → h (v i) (v j) = 0)
    (hne : ∀ i, h (v i) (v i) ≠ 0) : ∃ e : Basis (Fin k) K V, ∀ i, e i = v i := by
  have hli : LinearIndependent K v :=
    LinearMap.linearIndependent_of_isOrthoᵢ (B := h) (fun i j hij => ho i j hij) (fun i => hne i)
  have htop : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hk])
  exact ⟨Basis.mk hli htop.ge, fun i => Basis.mk_apply hli htop.ge i⟩

theorem exists_ortho_family [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) :
    ∀ k : ℕ, k ≤ finrank K V →
      ∃ v : Fin k → V, (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, v i ≠ 0 := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨v, ho, hne⟩ := ih (by omega)
    obtain ⟨x, hx0, hx⟩ := exists_ortho_ne_zero h v (by omega)
    refine ⟨Fin.snoc v x, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact hs.isRefl _ _ (hx j)
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact hx i
      · intro hij
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact ho i j (fun e => hij (by rw [e]))
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Fin.snoc_last]; exact hx0
      · rw [Fin.snoc_castSucc]; exact hne i

end

end GramDeterminantPositive

theorem orthBasisPos_holds : OrthBasisPos := by
  intro K _ _ _ hK V _ _ _ _ _ h hs hpos
  have hne0 : ∀ x : V, x ≠ 0 → h x x ≠ 0 := by
    intro x hx h0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpos x hx φ
    rw [h0, map_zero] at this
    simp at this
  obtain ⟨v, ho, hne⟩ := GramDeterminantPositive.exists_ortho_family h hs (finrank K V) le_rfl
  obtain ⟨e, he⟩ := GramDeterminantPositive.exists_basis_of_ortho h v rfl ho (fun i => hne0 _ (hne i))
  refine ⟨e, fun i j hij => by rw [he, he]; exact ho i j hij, fun i => ⟨?_, ?_⟩⟩
  · exact hs.eq (e i) (e i)
  · exact hpos (e i) (e.ne_zero i)

section

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

end

namespace GramDeterminantPositive

end GramDeterminantPositive

end Formalism.HermitianLattices.Ext.L3
end
end
