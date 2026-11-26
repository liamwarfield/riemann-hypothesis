module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResCyc
public import ReciprocityTheory.GroupCohomology.FiveTerm
public import ReciprocityTheory.GroupCohomology.CupCor
public import ReciprocityTheory.GroupCohomology.RankLen
public import ReciprocityTheory.GroupCohomology.LengthKerEqCoker
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.PrincZl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ControlGamma
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.H2SubsingletonTransport
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Transg
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

namespace UpperTheory.V.Base

open ReciprocityTheory.Coh

section

variable {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M]
  [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

private theorem transg_cont (σ : Representation R Γ M) (hσ : ContAction σ) (N : Subgroup Γ) [N.Normal] :
    ContAction (σ.quotientToInvariants N) := by
  unfold ReciprocityTheory.Gal.ContAction
  have hq := (QuotientGroup.isOpenQuotientMap_mk (N := N)).prodMap
    (IsOpenQuotientMap.id (X := Representation.invariants (σ.comp N.subtype)))
  rw [← hq.continuous_comp_iff]
  refine continuous_induced_rng.2 ?_
  exact hσ.comp (f := fun p : Γ × Representation.invariants (σ.comp N.subtype) => (p.1, (p.2 : M)))
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

private theorem transg_top [DiscreteTopology M] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    (σ : Representation R Γ M) (hσ : ContAction σ) (N : Subgroup Γ) [N.Normal] (hN : IsClosed (N : Set Γ)) :
    ∃ tg : (conjRep σ N).invariants →ₗ[R] H2 (σ.quotientToInvariants N),
      ∀ x, tg x = 0 ↔ x.1 ∈ LinearMap.range (resH1 σ N.subtype continuous_subtype_val) := by
  let A : TRep R Γ := { V := M, rho := σ, cont := hσ }
  let Q : TRep R (Γ ⧸ N) :=
    { V := Representation.invariants (σ.comp N.subtype), rho := σ.quotientToInvariants N, cont := transg_cont σ hσ N }
  let P : Pair Q A := ⟨QuotientGroup.mk' N, Submodule.subtype _, QuotientGroup.continuous_mk,
    continuous_subtype_val, fun _ _ => rfl⟩
  have hP : IsInvRep A N Q P := by
    refine ⟨rfl, Topology.IsEmbedding.subtypeVal, fun m => ?_⟩
    show m ∈ LinearMap.range (Submodule.subtype _) ↔ _
    rw [Submodule.range_subtype]
    exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g.1 g.2⟩
  obtain ⟨a₀, a₁, a₂, ha⟩ := exists_isLow A
  obtain ⟨n₀, n₁, n₂, hn⟩ := exists_isLow (A.resSub N)
  obtain ⟨q₀, q₁, q₂, hq⟩ := exists_isLow Q
  haveI : DiscreteTopology A.V := ‹DiscreteTopology M›
  let I : Submodule R ((A.resSub N).H 1) := (conjRep σ N).invariants.comap n₁.toLinearMap
  obtain ⟨tg, htg, -⟩ := fiveTerm_holds R Γ A N hN Q P hP I (by
    intro x
    constructor
    · intro hx s c h1 h2
      apply n₁.injective
      rw [(lowNat_holds R N N _ _ c _ _ _ _ _ _ hn hn).2.1]
      obtain ⟨φ, u, hφ, hu, he⟩ := c
      obtain rfl : φ = conjHom N s := MonoidHom.ext fun g => Subtype.ext (h1 g)
      obtain rfl : u = σ s := LinearMap.ext h2
      exact hx s
    · intro hx s
      let c : Pair (A.resSub N) (A.resSub N) := ⟨conjHom N s, σ s, continuous_conjHom N s,
        continuous_of_discreteTopology (α := M), fun u (m : M) => by
          show σ s (σ (s⁻¹ * u * s) m) = σ u (σ s m)
          rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
          simp [mul_assoc]⟩
      have e := congrArg n₁ (hx s c (fun _ => rfl) fun _ => rfl)
      rw [(lowNat_holds R N N _ _ c _ _ _ _ _ _ hn hn).2.1] at e
      exact e)
  let k : (conjRep σ N).invariants →ₗ[R] I :=
    { toFun := fun x => ⟨n₁.symm x.1, fun s => by
        have e := n₁.apply_symm_apply x.1
        exact (congrArg (conjRep σ N s) e).trans ((x.2 s).trans e.symm)⟩
      map_add' := fun x y => Subtype.ext (n₁.symm.map_add x.1 y.1)
      map_smul' := fun r x => Subtype.ext (n₁.symm.map_smul r x.1) }
  refine ⟨q₂.toLinearMap.comp (tg.comp k), fun x => ?_⟩
  have hr := (lowNat_holds R Γ N _ _ (Pair.res A N.subtype continuous_subtype_val) _ _ _ _ _ _ ha hn).2.1
  refine (q₂.map_eq_zero_iff.trans (htg (k x))).trans ⟨?_, ?_⟩
  · rintro ⟨y, hy⟩
    refine ⟨a₁ y, ?_⟩
    have e := congrArg n₁ hy
    rw [hr] at e
    exact e.trans (n₁.apply_symm_apply x.1)
  · rintro ⟨y, hy⟩
    refine ⟨a₁.symm y, n₁.injective ?_⟩
    rw [hr, LinearEquiv.apply_symm_apply]
    exact hy.trans (n₁.apply_symm_apply x.1).symm

end

end UpperTheory.V.Base

theorem UpperTheory.V.Base.transg :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G], ContAction ρ → ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsClosed (U : Set G) → IsClosed (U' : Set G) →
      ∃ tg : resCoker ρ h →ₗ[R] H2 (quotRep ρ U U'), Function.Injective tg := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ _ _ _ hρ U' U _ h hU hU'
  haveI : CompactSpace U := isCompact_iff_compactSpace.1 hU.isCompact
  let σ : Representation R U M := ρ.comp U.subtype
  have hσ : ContAction σ := hρ.comp (f := fun p : U × M => ((p.1 : G), p.2))
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨tg, htg⟩ := transg_top σ hσ (U'.subgroupOf U) (hU'.preimage continuous_subtype_val)
  let j : H1U ρ U' →ₗ[R] H1U σ (U'.subgroupOf U) :=
    pairH1DecompositionMap _ _ (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) LinearMap.id continuous_id fun _ _ => rfl
  let j' : H1U σ (U'.subgroupOf U) →ₗ[R] H1U ρ U' :=
    pairH1DecompositionMap _ _ (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom
      ((continuous_subtype_val.subtype_mk _).subtype_mk _) LinearMap.id continuous_id fun _ _ => rfl
  have h1 : ∀ x, j' (j x) = x := fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  have h2 : ∀ y, j (resU ρ h y) = resH1 σ (U'.subgroupOf U).subtype continuous_subtype_val y := fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  have h3 : ∀ (g : U) x, conjRep σ (U'.subgroupOf U) g (j x) = j (conjRep ρ U' g x) := fun g x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  let k : invariantsUnderSubgroupH1 ρ U U' →ₗ[R] (conjRep σ (U'.subgroupOf U)).invariants :=
    (j.comp (Submodule.subtype _)).codRestrict _ fun x g => (h3 g x.1).trans (congrArg j (x.2 g))
  have hk : ∀ x : invariantsUnderSubgroupH1 ρ U U', tg (k x) = 0 ↔ x.1 ∈ LinearMap.range (resU ρ h) := fun x => by
    refine (htg (k x)).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [← h1 (resU ρ h y), h2, hy]; exact h1 x.1⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, (h2 y).symm.trans (congrArg j hy)⟩
  refine ⟨Submodule.liftQ _ (tg.comp k) fun x hx => (hk x).2 hx, ?_⟩
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ fun x hx => (hk x).1 hx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DenseGen
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem contMod (l : ℕ) [Fact l.Prime] (k : ℕ) {N : Type} [TopologicalSpace N] (c : ZMod (l ^ k) → N) :
    Continuous fun x : ℤ_[l] => c (PadicInt.toZModPow k x) := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.ball_mem_nhds x hpos] with y hy
  have h1 : y - x ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hy.le
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at h1
  rw [h1]

private theorem clopenEq {X N : Type} [TopologicalSpace X] [TopologicalSpace N] [DiscreteTopology N] {f g : X → N}
    (hf : Continuous f) (hg : Continuous g) : IsClopen {x | f x = g x} := by
  have h : {x | f x = g x} = (fun x => (f x, g x)) ⁻¹' {p : N × N | p.1 = p.2} := rfl
  rw [h]
  exact (isClopen_discrete _).preimage (hf.prodMk hg)

private theorem powGen (l : ℕ) [Fact l.Prime] (n : ℕ) :
    (Multiplicative.ofAdd (1 : ℤ_[l])) ^ n = Multiplicative.ofAdd (n : ℤ_[l]) := by
  rw [← ofAdd_nsmul, nsmul_one]

private theorem denseGen (l : ℕ) [Fact l.Prime] :
    DenseRange fun n : ℕ => (Multiplicative.ofAdd (1 : ℤ_[l])) ^ n := by
  have h : (fun n : ℕ => (Multiplicative.ofAdd (1 : ℤ_[l])) ^ n) =
      fun n : ℕ => Multiplicative.ofAdd (n : ℤ_[l]) := funext (powGen l)
  rw [h]
  exact PadicInt.denseRange_natCast

private theorem tendGen (l : ℕ) [Fact l.Prime] :
    Filter.Tendsto (fun a : ℕ => (Multiplicative.ofAdd (1 : ℤ_[l])) ^ (l ^ a)) Filter.atTop (nhds 1) := by
  have h : (fun a : ℕ => (Multiplicative.ofAdd (1 : ℤ_[l])) ^ (l ^ a)) =
      fun a : ℕ => Multiplicative.ofAdd ((l : ℤ_[l]) ^ a) := by
    funext a
    rw [powGen]
    push_cast
    rfl
  rw [h]
  have h2 : ‖(l : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one h2

private theorem solveGen (l : ℕ) [Fact l.Prime] (R N : Type) [CommRing R] [AddCommGroup N] [Module R N]
    [TopologicalSpace N] [DiscreteTopology N] (σ : Representation R (Multiplicative ℤ_[l]) N) (hσ : ContAction σ)
    (ht : ∀ m : N, ∃ n : ℕ, l ^ n • m = 0) (φ : Multiplicative ℤ_[l] → N) (hφ : Continuous φ) (m₀ : N) :
    ∃ C : Multiplicative ℤ_[l] → N, Continuous C ∧ C 1 = m₀ ∧
      ∀ x, C (Multiplicative.ofAdd 1 * x) = σ (Multiplicative.ofAdd 1) (C x) - φ x := by
  let γ : Multiplicative ℤ_[l] := Multiplicative.ofAdd 1
  let a : ℕ → N := fun n => Nat.rec (motive := fun _ => N) m₀ (fun k ak => σ γ ak - φ (γ ^ k)) n
  have ha0 : a 0 = m₀ := rfl
  have haS : ∀ n, a (n + 1) = σ γ (a n) - φ (γ ^ n) := fun n => rfl
  have hσ' : Continuous fun p : Multiplicative ℤ_[l] × N => σ p.1 p.2 := hσ
  have hper : ∀ m : N, ∀ᶠ k in Filter.atTop, σ (γ ^ (l ^ k)) m = m := by
    intro m
    have hc : Continuous fun g : Multiplicative ℤ_[l] => σ g m :=
      hσ'.comp (continuous_id.prodMk continuous_const)
    have ht2 := (hc.tendsto 1).comp (tendGen l)
    rw [map_one σ, Module.End.one_apply, nhds_discrete, Filter.tendsto_pure] at ht2
    exact ht2
  have hφper : ∀ᶠ k in Filter.atTop, ∀ x, φ (γ ^ (l ^ k) * x) = φ x := by
    have hev : ∀ᶠ y in nhds (1 : Multiplicative ℤ_[l]),
        ∀ x ∈ (Set.univ : Set (Multiplicative ℤ_[l])), φ (y * x) = φ x := by
      apply isCompact_univ.eventually_forall_of_forall_eventually
      intro x _
      have hopen : IsOpen {z : Multiplicative ℤ_[l] × Multiplicative ℤ_[l] | φ (z.1 * z.2) = φ z.2} :=
        (clopenEq (hφ.comp continuous_mul) (hφ.comp continuous_snd)).isOpen
      exact hopen.mem_nhds (by simp)
    filter_upwards [(tendGen l).eventually hev] with k hk x
    exact hk x (Set.mem_univ x)
  have L1 : ∀ q : ℕ, (∀ x, φ (γ ^ q * x) = φ x) →
      ∀ n, a (n + q) - a n = σ (γ ^ n) (a q - a 0) := by
    intro q hq n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show n + 1 + q = n + q + 1 by omega, haS, haS, pow_succ', map_mul, Module.End.mul_apply,
        ← ih, map_sub]
      have h1 : φ (γ ^ (n + q)) = φ (γ ^ n) := by
        rw [pow_add, mul_comm (γ ^ n), hq]
      rw [h1]
      abel
  have L2 : ∀ q : ℕ, (∀ x, φ (γ ^ q * x) = φ x) →
      ∀ s, a (s * q) - a 0 = ∑ t ∈ Finset.range s, σ (γ ^ (t * q)) (a q - a 0) := by
    intro q hq s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Finset.sum_range_succ, ← ih, ← L1 q hq (s * q), add_one_mul]
      abel
  have Lmul : ∀ q : ℕ, (∀ x, φ (γ ^ q * x) = φ x) → ∀ s, ∀ x, φ (γ ^ (q * s) * x) = φ x := by
    intro q hq s
    induction s with
    | zero => intro x; simp
    | succ s ih => intro x; rw [Nat.mul_succ, pow_add, mul_assoc, ih, hq]
  obtain ⟨k, hk⟩ := hφper.exists
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp (hper (a (l ^ k) - a 0))
  have hK1 : l ^ (max A k) = l ^ k * l ^ (max A k - k) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_max_right A k)]
  have hφQ : ∀ x, φ (γ ^ (l ^ (max A k)) * x) = φ x := by
    rw [hK1]
    exact Lmul _ hk _
  have hdQ : a (l ^ (max A k)) - a 0 =
      ∑ t ∈ Finset.range (l ^ (max A k - k)), σ (γ ^ (t * l ^ k)) (a (l ^ k) - a 0) := by
    rw [← L2 _ hk, hK1, mul_comm (l ^ k)]
  have hfixQ : σ (γ ^ (l ^ (max A k))) (a (l ^ (max A k)) - a 0) = a (l ^ (max A k)) - a 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hdQ, map_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← Module.End.mul_apply, ← map_mul, mul_comm (γ ^ (l ^ (max A k))), map_mul,
      Module.End.mul_apply, hA (max A k) (le_max_left A k)]
  obtain ⟨j, hj⟩ := ht (a (l ^ (max A k)) - a 0)
  have hφK : ∀ x, φ (γ ^ (l ^ (max A k + j)) * x) = φ x := by
    rw [pow_add]
    exact Lmul _ hφQ _
  have haK : a (l ^ (max A k + j)) = a 0 := by
    have h2 := L2 _ hφQ (l ^ j)
    have h3 : ∀ t ∈ Finset.range (l ^ j),
        σ (γ ^ (t * l ^ (max A k))) (a (l ^ (max A k)) - a 0) = a (l ^ (max A k)) - a 0 := by
      intro t _
      rw [mul_comm t, pow_mul, map_pow, Module.End.pow_apply, Function.iterate_fixed hfixQ]
    rw [Finset.sum_congr rfl h3, Finset.sum_const, Finset.card_range, hj] at h2
    rw [pow_add, mul_comm]
    exact sub_eq_zero.mp h2
  have hperiod : ∀ n, a (n + l ^ (max A k + j)) = a n := by
    intro n
    have h4 := L1 _ hφK n
    rw [haK, sub_self, map_zero, sub_eq_zero] at h4
    exact h4
  have hperiod' : ∀ s n, a (n + l ^ (max A k + j) * s) = a n := by
    intro s
    induction s with
    | zero => intro n; simp
    | succ s ih => intro n; rw [Nat.mul_succ, ← add_assoc, hperiod, ih]
  have hmod : ∀ n, a (n % l ^ (max A k + j)) = a n := by
    intro n
    conv_rhs => rw [← Nat.mod_add_div n (l ^ (max A k + j))]
    rw [hperiod']
  let C : Multiplicative ℤ_[l] → N :=
    fun x => a (PadicInt.toZModPow (max A k + j) (Multiplicative.toAdd x)).val
  have hCc : Continuous C :=
    (contMod l (max A k + j) (fun i : ZMod (l ^ (max A k + j)) => a i.val)).comp continuous_toAdd
  have hCn : ∀ n : ℕ, C (γ ^ n) = a n := by
    intro n
    simp only [C, γ, powGen, toAdd_ofAdd, map_natCast, ZMod.val_natCast]
    exact hmod n
  refine ⟨C, hCc, ?_, ?_⟩
  · have h5 : C 1 = a 0 := by
      simp only [C, toAdd_one, map_zero, ZMod.val_zero]
    rw [h5, ha0]
  · intro x
    refine (denseGen l).induction_on
      (p := fun x => C (Multiplicative.ofAdd 1 * x) = σ (Multiplicative.ofAdd 1) (C x) - φ x) x ?_ ?_
    · exact (clopenEq (hCc.comp (continuous_const_mul _))
        ((continuous_of_discreteTopology
          (f := fun pr : N × N => σ (Multiplicative.ofAdd 1) pr.1 - pr.2)).comp
          (hCc.prodMk hφ))).isClosed
    · intro n
      show C (γ * γ ^ n) = σ γ (C (γ ^ n)) - φ (γ ^ n)
      rw [← pow_succ', hCn, hCn, haS]

theorem UpperTheory.V.Base.h2Zl :
    ∀ (l : ℕ) [Fact l.Prime] (R N : Type) [CommRing R] [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
      [ContinuousConstSMul R N] [DiscreteTopology N] (σ : Representation R (Multiplicative ℤ_[l]) N), ContAction σ →
      (∀ m : N, ∃ n : ℕ, l ^ n • m = 0) → Subsingleton (H2 σ) := by
  intro l _ R N _ _ _ _ _ _ _ σ hσ ht
  refine subsingleton_of_forall_eq 0 ?_
  intro x
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  show f.1 ∈ B2 σ
  rw [separated_dvr_second_cohomology_mem]
  have hf : Continuous f.1 := f.2.1
  have hcoc := f.2.2
  have hφ : Continuous fun y => f.1 (Multiplicative.ofAdd (1 : ℤ_[l]), y) :=
    hf.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC, hC1, hCeq⟩ := solveGen l R N σ hσ ht _ hφ (f.1 (1, 1))
  refine ⟨C, hC, ?_⟩
  funext pr
  obtain ⟨g, h⟩ := pr
  show σ g (C h) - C (g * h) + C g = f.1 (g, h)
  have hf1 : ∀ k, f.1 (1, k) = f.1 (1, 1) := by
    intro k
    have h0 := hcoc 1 1 k
    simp only [map_one, one_mul, Module.End.one_apply, sub_self, zero_add] at h0
    exact sub_eq_zero.mp h0
  have hσ' : Continuous fun p : Multiplicative ℤ_[l] × N => σ p.1 p.2 := hσ
  refine (denseGen l).induction_on (p := fun g => σ g (C h) - C (g * h) + C g = f.1 (g, h)) g ?_ ?_
  · exact (clopenEq
      (((hσ'.comp (continuous_id.prodMk continuous_const)).sub
        (hC.comp (continuous_mul_const h))).add hC)
      (hf.comp (continuous_id.prodMk continuous_const))).isClosed
  · intro n
    induction n with
    | zero =>
      simp only [pow_zero, map_one, Module.End.one_apply, one_mul, sub_self, zero_add]
      rw [hC1, hf1 h]
    | succ n ih =>
      rw [pow_succ', mul_assoc, hCeq, hCeq, map_mul, Module.End.mul_apply]
      have hc := hcoc (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1 ^ n) h
      rw [← ih, map_add (f := _), map_sub] at hc
      rw [← sub_eq_zero]
      convert hc using 1
      abel
end

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem H2_subsingleton_of_mulEquiv {R Q Q' N : Type} [CommRing R] [Group Q] [TopologicalSpace Q] [Group Q'] [TopologicalSpace Q']
    [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousConstSMul R N]
    (σ : Representation R Q N) (e : Q ≃* Q') (he : Continuous e) (he' : Continuous e.symm)
    (hs : Subsingleton (H2 (σ.comp e.symm.toMonoidHom : Representation R Q' N))) : Subsingleton (H2 σ) := by
  have hc : ∀ g m, (LinearMap.id : N →ₗ[R] N) ((σ.comp e.symm.toMonoidHom : Representation R Q' N) (e.toMonoidHom g) m)
      = σ g ((LinearMap.id : N →ₗ[R] N) m) := fun g m => by simp
  have hsurj : Function.Surjective
      (compatiblePairH2 (σ.comp e.symm.toMonoidHom : Representation R Q' N) σ e.toMonoidHom he LinearMap.id continuous_id hc) := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨Submodule.Quotient.mk (restrictCocycles2 σ e.symm.toMonoidHom he' z), ?_⟩
    show Submodule.Quotient.mk (compatiblePairCocycles2 _ σ e.toMonoidHom he LinearMap.id continuous_id hc _) = _
    congr 1
    refine Subtype.ext (funext fun p => ?_)
    obtain ⟨g, h⟩ := p
    show z.1 (e.symm (e g), e.symm (e h)) = _
    simp
  exact hsurj.subsingleton

private theorem cont_quot {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    (ρ : Representation R G M) (hρ : ReciprocityTheory.Gal.ContAction ρ) (S : Subgroup G) [S.Normal] :
    ReciprocityTheory.Gal.ContAction (ρ.quotientToInvariants S) := by
  unfold ReciprocityTheory.Gal.ContAction
  have hq := (QuotientGroup.isOpenQuotientMap_mk (N := S)).prodMap
    (IsOpenQuotientMap.id (X := Representation.invariants (ρ.comp S.subtype)))
  rw [← hq.continuous_comp_iff]
  refine Continuous.subtype_mk (f := fun p : G × Representation.invariants (ρ.comp S.subtype) => ρ p.1 p.2.1) ?_ _
  exact hρ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

private theorem H2_quotientToInvariants_subsingleton_of_zl_quotient (l : ℕ) [Fact l.Prime] {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] [DiscreteTopology M]
    (ρ : Representation R G M) (hρ : ReciprocityTheory.Gal.ContAction ρ) (hl : ∀ m : M, ∃ n : ℕ, l ^ n • m = 0) (S : Subgroup G) [S.Normal]
    (κ : G →* Multiplicative ℤ_[l]) (hκ : Continuous κ) (hs : Function.Surjective κ) (hk : κ.ker = S) :
    Subsingleton (H2 (ρ.quotientToInvariants S)) := by
  let e : G ⧸ S ≃* Multiplicative ℤ_[l] :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivOfSurjective κ hs)
  have he : Continuous e := by
    rw [← (QuotientGroup.isOpenQuotientMap_mk (N := S)).continuous_comp_iff]
    exact hκ
  have he' : Continuous e.symm := (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) he).symm.continuous
  refine H2_subsingleton_of_mulEquiv _ e he he' (h2Zl l R _ _ ?_ ?_)
  · exact (cont_quot ρ hρ S).comp ((he'.comp continuous_fst).prodMk continuous_snd)
  · intro m
    obtain ⟨n, hn⟩ := hl m.1
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

theorem UpperTheory.V.Base.resZl :
    ∀ (l : ℕ) [Fact l.Prime], ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G], ContAction ρ → (∀ m : M, ∃ n : ℕ, l ^ n • m = 0) →
      ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsClosed (U : Set G) → ∀ κ : U →* Multiplicative ℤ_[l], Continuous κ →
      Function.Surjective κ → κ.ker = U'.subgroupOf U → invariantsUnderSubgroupH1 ρ U U' ≤ LinearMap.range (resU ρ h) := by
  intro l _ R G M _ _ _ _ _ _ _ _ _ _ ρ _ _ _ hρ hl U' U _ h hU κ hκ hs hk
  haveI : CompactSpace U := isCompact_iff_compactSpace.1 hU.isCompact
  have hρU : ReciprocityTheory.Gal.ContAction (ρ.comp U.subtype : Representation R U M) :=
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  haveI : Subsingleton (H2 (quotRep ρ U U')) := H2_quotientToInvariants_subsingleton_of_zl_quotient l _ hρU hl _ κ hκ hs hk
  have hc : IsClosed (U'.subgroupOf U : Set U) := by
    rw [← hk]
    exact isClosed_singleton.preimage hκ
  have hc' : IsClosed (U' : Set G) := by
    have := hU.isClosedEmbedding_subtypeVal.isClosedMap _ hc
    convert this using 1
    ext x
    exact ⟨fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩, fun ⟨y, hy, e⟩ => e ▸ hy⟩
  obtain ⟨tg, htg⟩ := transg R G M ρ hρ U' U h hU hc'
  intro x hx
  have h0 : (Submodule.Quotient.mk ⟨x, hx⟩ : resCoker ρ h) = 0 := htg (Subsingleton.elim _ _)
  exact Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GammaGen
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.gammaGen :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G k Ω)), IsClosed (U : Set (G k Ω)) → U ≤ gamU l ⊤ → ¬ U ≤ (cycZ k Ω l).ker →
      ∃ (κ : U →* Multiplicative ℤ_[l]) (γ : U), Continuous κ ∧ Function.Surjective κ ∧ κ.ker = (cycU l U).subgroupOf U ∧
        κ γ = Multiplicative.ofAdd 1 ∧ U ≤ (Subgroup.zpowers γ.1 ⊔ cycU l U).topologicalClosure ∧ ¬ IsOfFinOrder (cycZ k Ω l γ.1) := by
  intro k Ω _ _ _ _ _ l _ U hUc hUg hUk
  have hχc : Continuous (cycZ k Ω l) := continuous_cycZ k Ω l
  have hHc : IsClosed ((U.map (cycZ k Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hUc.isCompact.image hχc).isClosed
  have hHp : U.map (cycZ k Ω l) ≤ KStar.TotallyRealRoots.princ l (qExp l) := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hUg hu
    simp only [gamU, levU, Subgroup.mem_inf, Subgroup.mem_comap] at h
    exact h.2
  have hHb : U.map (cycZ k Ω l) ≠ ⊥ := by
    intro h
    apply hUk
    intro u hu
    have hm : cycZ k Ω l u ∈ U.map (cycZ k Ω l) := ⟨u, hu, rfl⟩
    rw [h] at hm
    exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hm)
  obtain ⟨⟨e⟩, htor⟩ := princZl l _ hHc hHp hHb
  let ψ : U →* U.map (cycZ k Ω l) := (cycZ k Ω l).subgroupMap U
  have hψc : Continuous ψ := by
    apply Continuous.subtype_mk
    exact hχc.comp continuous_subtype_val
  let κ : U →* Multiplicative ℤ_[l] := e.toMulEquiv.toMonoidHom.comp ψ
  have hκc : Continuous κ := e.continuous.comp hψc
  have hκs : Function.Surjective κ := e.surjective.comp (MonoidHom.subgroupMap_surjective _ U)
  have hkκ : ∀ x : U, κ x = 1 ↔ cycZ k Ω l x = 1 := by
    intro x
    have h1 : κ x = e (ψ x) := rfl
    rw [h1, map_eq_one_iff e e.injective, Subtype.ext_iff]
    exact Iff.rfl
  obtain ⟨γ, hγ⟩ := hκs (Multiplicative.ofAdd 1)
  refine ⟨κ, γ, hκc, hκs, ?_, hγ, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, hkκ, Subgroup.mem_subgroupOf]
    simp only [cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  · set V := (Subgroup.zpowers γ.1 ⊔ cycU l U).topologicalClosure with hV
    have hVc : IsClosed (V : Set (G k Ω)) := Subgroup.isClosed_topologicalClosure _
    have hsub : Subgroup.zpowers γ.1 ⊔ cycU l U ≤ V := Subgroup.le_topologicalClosure _
    have hcU : CompactSpace U := isCompact_iff_compactSpace.mp hUc.isCompact
    let S : Set U := Subtype.val ⁻¹' (V : Set (G k Ω))
    have hSc : IsClosed S := hVc.preimage continuous_subtype_val
    have hIc : IsClosed (κ '' S) := (hSc.isCompact.image hκc).isClosed
    let T : Set ℤ_[l] := Multiplicative.ofAdd ⁻¹' (κ '' S)
    have hTc : IsClosed T := hIc.preimage continuous_ofAdd
    have hTz : Set.range (Int.cast : ℤ → ℤ_[l]) ⊆ T := by
      rintro _ ⟨n, rfl⟩
      refine ⟨γ ^ n, ?_, ?_⟩
      · show ((γ ^ n : U) : G k Ω) ∈ V
        rw [Subgroup.coe_zpow]
        exact hsub (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ n))
      · rw [map_zpow, hγ, ← ofAdd_zsmul, zsmul_one]
    have hT : T = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← PadicInt.denseRange_intCast.closure_range]
      exact closure_minimal hTz hTc
    intro u hu
    have ha : Multiplicative.toAdd (κ ⟨u, hu⟩) ∈ T := by rw [hT]; trivial
    obtain ⟨s, hs, hks⟩ := ha
    have hks' : κ s = κ ⟨u, hu⟩ := hks
    have hq : κ (⟨u, hu⟩ * s⁻¹) = 1 := by rw [map_mul, map_inv, ← hks', mul_inv_cancel]
    have hq' := (hkκ _).mp hq
    have hmem : ((⟨u, hu⟩ * s⁻¹ : U) : G k Ω) ∈ V := by
      apply hsub
      apply Subgroup.mem_sup_right
      simp only [cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
      exact ⟨(⟨u, hu⟩ * s⁻¹ : U).2, hq'⟩
    have hu' : u = ((⟨u, hu⟩ * s⁻¹ : U) : G k Ω) * (s : G k Ω) := by
      simp
    rw [hu']
    exact V.mul_mem hmem hs
  · intro hfin
    have hm : cycZ k Ω l γ.1 ∈ U.map (cycZ k Ω l) := ⟨γ.1, γ.2, rfl⟩
    have h1 := (hkκ γ).mpr (htor _ hm hfin)
    rw [hγ] at h1
    exact one_ne_zero (ofAdd_eq_one.mp h1)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem exists_val (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ W : ValuationSubring Ω, W.valuation (p : Ω) < 1 := by
  have hne : (Ideal.span {(p : (⊥ : Subring Ω))}) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨n, hn⟩ := Subring.mem_bot.1 v.2
    have h1 : ((p : ℤ) * n : ℤ) = 1 := by
      have := congrArg Subtype.val hv
      simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
      rw [← hn] at this
      exact_mod_cast this
    have := Int.isUnit_iff_natAbs_eq.1 (IsUnit.of_mul_eq_one _ h1)
    simp at this
    exact hp.one_lt.ne' this
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  exact ⟨W, (ValuationSubring.mem_nonunits_iff W).1 (hW ⟨p, Ideal.mem_span_singleton_self _, by simp⟩)⟩

private theorem inj_cyc (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ)
    [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (ψ : G k Ω →* Oˣ) (n : ℤ) (hn : n ≠ 0) (hψo : IsOpen (ψ.ker : Set (G k Ω)))
    (V : Subgroup (G k Ω)) (hV : IsClosed (V : Set (G k Ω))) (hg : V ≤ gamU l ⊤) (hψ : V ≤ ψ.ker)
    (hχ : ¬ V ≤ (cycZ k Ω l).ker) :
    Function.Injective (resU (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l V)) := by
  obtain ⟨κ, γ, -, -, hk, -, hcl, hfin⟩ := gammaGen k Ω l V hV hg hχ
  haveI : ((cycU l V).subgroupOf V).Normal := hk ▸ inferInstance
  refine (kerResCyc O (G k Ω) (QO l O) _ ((contTw k Ω l).2.2 O ψ n hψo) (cycU l V) V (cycU_le l V) γ.1 γ.2 hcl).2 ?_
  intro m _
  have hall : ∀ m' : QO l O, m' ∈ H0U (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU l V) := by
    intro m' u
    have h1 : ψ u.1 = 1 := hψ u.2.1
    have h2 : cycZ k Ω l u.1 = 1 := u.2.2
    have h3 : (ψ * chiO k Ω l O ^ n) u.1 = 1 := by
      simp [chiO, h1, h2]
    show (((ψ * chiO k Ω l O ^ n) u.1 : Oˣ) : O) • m' = m'
    rw [h3, Units.val_one, one_smul]
  have ha : (((ψ * chiO k Ω l O ^ n) γ.1 : Oˣ) : O) - 1 ≠ 0 := by
    intro h0
    have h1 : ψ γ.1 = 1 := hψ γ.2
    have h2 : (ψ * chiO k Ω l O ^ n) γ.1 = 1 := Units.ext (sub_eq_zero.1 h0)
    have h3 : Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ k Ω l γ.1 ^ n) = 1 := by
      rw [map_zpow]
      simpa [chiO, h1] using h2
    have h4 : cycZ k Ω l γ.1 ^ n = 1 :=
      Units.map_injective (f := (algebraMap ℤ_[l] O).toMonoidHom) (dvrFacts l O).1 (h3.trans (map_one _).symm)
    exact hfin (isOfFinOrder_iff_zpow_eq_one.2 ⟨n, hn, h4⟩)
  obtain ⟨m', hm'⟩ := (qoFacts l O).2.2.1 _ ha m
  refine ⟨m', hall m', ?_⟩
  show (((ψ * chiO k Ω l O ^ n) γ.1 : Oˣ) : O) • m' - m' = m
  rw [← hm', sub_smul, one_smul]

private theorem mem_selEig_one {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [IsTopologicalGroup G] [DiscreteTopology M]
    (ρ : Representation R G M) (U' : Subgroup G) [U'.Normal] {𝒟 : Set (Subgroup G)} (h𝒟 : ConjStable 𝒟)
    (U : Subgroup G) (x : LocSel ρ U' 𝒟) : x ∈ selEig ρ U' h𝒟 U 1 ↔ x.1 ∈ invariantsUnderSubgroupH1 ρ U U' := by
  unfold selEig
  rw [eig_one]
  exact ⟨fun h g => congrArg Subtype.val (h g), fun h g => Subtype.ext (h g)⟩

theorem UpperTheory.V.Base.controlGamma :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (U : Subgroup (G k Ω)) [U.Normal], IsOpen (U : Set (G k Ω)) → U ≤ gamU l ⊤ → ∀ (ψ : G k Ω →* Oˣ) (n : ℤ), U ≤ ψ.ker → n ≠ 0 →
      Function.Injective (selRes (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l U) (shaFam k Ω l)) ∧
      LinearMap.range (selRes (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l U) (shaFam k Ω l)) =
        shaEig (twist₂ l (ψ * chiO k Ω l O ^ n)) l (cycU l U) U 1 := by
  intro k Ω _ _ _ _ _ l hl O _ _ _ _ _ U _ hU hg ψ n hψ hn
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have hψo : IsOpen (ψ.ker : Set (G k Ω)) := Subgroup.isOpen_mono hψ hU
  have hUc : IsClosed (U : Set (G k Ω)) := U.isClosed_of_isOpen hU
  have hnt : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ¬ U ⊓ Dec (F := k) A ≤ (cycZ k Ω l).ker := by
    intro A hA h
    obtain ⟨g, hgm, hf⟩ := decInf k Ω l U hU A hA
    exact hf (by rw [MonoidHom.mem_ker.1 (h hgm)]; exact IsOfFinOrder.one)
  have hχ : ¬ U ≤ (cycZ k Ω l).ker := by
    obtain ⟨A, hA⟩ := exists_val Ω l hl.out
    exact fun h => hnt A hA (inf_le_left.trans h)
  refine ⟨fun a b hab => Subtype.ext
    (inj_cyc k Ω l O ψ n hn hψo U hUc hg hψ hχ (congrArg Subtype.val hab)), le_antisymm ?_ ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact (mem_selEig_one _ _ _ _ _).2 (restriction_mem_invariant_H1 _ (cycU_le l U) y.1)
  · intro x hx
    have hx1 : x.1 ∈ invariantsUnderSubgroupH1 (twist₂ l (ψ * chiO k Ω l O ^ n)) U (cycU l U) := (mem_selEig_one _ _ _ _ _).1 hx
    obtain ⟨κ, γ, hκ, hs, hk, -⟩ := gammaGen k Ω l U hUc hg hχ
    obtain ⟨y, hy⟩ := resZl l O (G k Ω) (QO l O) _ ((contTw k Ω l).2.2 O ψ n hψo) (qoFacts l O).2.1
      (cycU l U) U (cycU_le l U) hUc κ hκ hs hk hx1
    have hz : ∀ D ∈ shaFam k Ω l, ∀ (W : Subgroup (G k Ω)) (h : W ≤ cycU l U ⊓ D) (h' : W ≤ U),
        resU (twist₂ l (ψ * chiO k Ω l O ^ n)) h' y = 0 := by
      intro D hD W h h'
      have h0 := mem_locSel.1 x.2 D hD
      rw [← hy, resU_resU] at h0
      have := congrArg (fun t => resU (twist₂ l (ψ * chiO k Ω l O ^ n)) h t) h0
      rwa [resU_resU, map_zero] at this
    have hdec : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
        resU (twist₂ l (ψ * chiO k Ω l O ^ n)) (inf_le_left : U ⊓ Dec (F := k) A ≤ U) y = 0 := by
      intro A hA
      apply inj_cyc k Ω l O ψ n hn hψo (U ⊓ Dec (F := k) A) (hUc.inter (isClosed_Dec A)) (inf_le_left.trans hg)
        (inf_le_left.trans hψ) (hnt A hA)
      rw [resU_resU, map_zero]
      exact hz _ (Or.inl ⟨A, hA, rfl⟩) (cycU l (U ⊓ Dec (F := k) A)) (fun g hg => ⟨⟨hg.1.1, hg.2⟩, hg.1.2⟩) _
    refine ⟨⟨y, mem_locSel.2 ?_⟩, Subtype.ext hy⟩
    rintro D (⟨A, hA, rfl⟩ | ⟨A, rfl⟩)
    · exact hdec A hA
    · by_cases hA : A.valuation (l : Ω) < 1
      · have := congrArg (fun t => resU (twist₂ l (ψ * chiO k Ω l O ^ n)) (inf_le_inf_left U (Ine_le_Dec (F := k) A)) t)
          (hdec A hA)
        rwa [resU_resU, map_zero] at this
      · exact hz _ (Or.inr ⟨A, rfl⟩) (U ⊓ Ine (F := k) A)
          (fun g hg => ⟨⟨hg.1, (places k Ω l A).2.2.2 hA hg.2⟩, hg.2⟩) _
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem control_lemma {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
    (ρ : Representation R Γ M) {C V U : Subgroup Γ} [C.Normal] [V.Normal] [U.Normal]
    (hCV : C ≤ V) (hVU : V ≤ U) (hCU : C ≤ U) {𝒟 : Set (Subgroup Γ)} (h𝒟 : ConjStable 𝒟)
    (H1 : Function.Injective (selRes ρ hCV 𝒟) ∧
      LinearMap.range (selRes ρ hCV 𝒟) = selEig ρ C h𝒟 V 1)
    (H2 : Function.Injective (selRes ρ hVU 𝒟) ∧
      LinearMap.range (selRes ρ hVU 𝒟) = selEig ρ V h𝒟 U 1) :
    Function.Injective (selRes ρ hCU 𝒟) ∧
      LinearMap.range (selRes ρ hCU 𝒟) = selEig ρ C h𝒟 U 1 := by
  have hcomp : ∀ x, selRes ρ hCU 𝒟 x = selRes ρ hCV 𝒟 (selRes ρ hVU 𝒟 x) := by
    intro x
    apply Subtype.ext
    simp only [selRes, LinearMap.restrict_apply]
    exact (resU_resU ρ hCV hVU x.1).symm
  have memE : ∀ (W : Subgroup Γ) [W.Normal] (X : Subgroup Γ) (y : LocSel ρ W 𝒟),
      y ∈ selEig ρ W h𝒟 X 1 ↔ ∀ g : X, selRep ρ W h𝒟 g y = y := by
    intro W _ X y
    simp only [selEig, mem_eig, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MonoidHom.one_apply, Units.val_one, one_smul]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    rw [hcomp, hcomp] at hxy
    exact H2.1 (H1.1 hxy)
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [memE]
      intro g
      have hx : selRes ρ hVU 𝒟 x ∈ selEig ρ V h𝒟 U 1 := H2.2 ▸ ⟨x, rfl⟩
      rw [memE] at hx
      rw [hcomp, ← selRes_selRep, hx g]
    · intro hy
      rw [memE] at hy
      have hyV : y ∈ LinearMap.range (selRes ρ hCV 𝒟) := by
        rw [H1.2, memE]
        intro g
        exact hy ⟨g, hVU g.2⟩
      obtain ⟨z, rfl⟩ := hyV
      have hz : z ∈ LinearMap.range (selRes ρ hVU 𝒟) := by
        rw [H2.2, memE]
        intro g
        apply H1.1
        rw [selRes_selRep]
        exact hy g
      obtain ⟨x, rfl⟩ := hz
      exact ⟨x, hcomp x⟩

private theorem selRes_injective_range_eq_of_le {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
    (ρ : Representation R Γ M) {C C' V : Subgroup Γ} [C.Normal] [C'.Normal] [V.Normal]
    (e : C' = C) (h : C ≤ V) (h' : C' ≤ V) {𝒟 : Set (Subgroup Γ)} (h𝒟 : ConjStable 𝒟)
    (H : Function.Injective (selRes ρ h' 𝒟) ∧
      LinearMap.range (selRes ρ h' 𝒟) = selEig ρ C' h𝒟 V 1) :
    Function.Injective (selRes ρ h 𝒟) ∧
      LinearMap.range (selRes ρ h 𝒟) = selEig ρ C h𝒟 V 1 := by
  subst e
  exact H

private theorem zmod_eq_intCast_of_primitiveRoot_pow_eq_selmer {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ N) (a : ZMod N) (k : ℤ) (h : ζ ^ a.val = ζ ^ k) :
    a = (k : ZMod N) := by
  have h0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
  have h1 : ζ ^ ((a.val : ℤ) - k) = 1 := by
    rw [zpow_sub₀ h0, zpow_natCast, h, div_self (zpow_ne_zero _ h0)]
  have h2 := (hζ.zpow_eq_one_iff_dvd _).mp h1
  have h3 : (((a.val : ℤ) - k : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
  push_cast at h3
  rw [ZMod.natCast_zmod_val] at h3
  exact sub_eq_zero.mp h3

theorem UpperTheory.V.Base.control :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (U : Subgroup (G k Ω)) [U.Normal], IsOpen (U : Set (G k Ω)) → (l ≠ 2 ∨ U ≤ gamU l ⊤) → ∀ (ψ : G k Ω →* Oˣ) (n : ℤ), U ≤ ψ.ker → n ≠ 0 →
      Function.Injective (selRes (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l U) (shaFam k Ω l)) ∧
      LinearMap.range (selRes (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l U) (shaFam k Ω l)) =
        shaEig (twist₂ l (ψ * chiO k Ω l O ^ n)) l (cycU l U) U 1 := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ U _ hU hl ψ n hψ hn
  by_cases hγ : U ≤ gamU l ⊤
  · exact controlGamma k Ω l O U hU hγ ψ n hψ hn
  have hl2 : l ≠ 2 := hl.resolve_right hγ
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hρ : ReciprocityTheory.Gal.ContAction (twist₂ l (ψ * chiO k Ω l O ^ n)) :=
    (contTw k Ω l).2.2 O ψ n (Subgroup.isOpen_mono hψ hU)
  have hq : qExp l = 1 := by simp [qExp, hl2]
  have hV : gamU l U = U ⊓ ((KStar.TotallyRealRoots.redPow l 1).comp (cycZ k Ω l)).ker := by
    show levU l U (qExp l) = _
    rw [hq]
    simp only [levU, KStar.TotallyRealRoots.princ, MonoidHom.comap_ker]
  have hVγ : gamU l U ≤ gamU l ⊤ := by
    show levU l U (qExp l) ≤ levU l ⊤ (qExp l)
    simp only [levU]
    exact inf_le_inf_right _ le_top
  have hVU : gamU l U ≤ U := levU_le l U (qExp l)
  haveI hVn : (gamU l U).Normal := by
    rw [hV]
    infer_instance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have hVopen : IsOpen ((gamU l U : Subgroup (G k Ω)) : Set (G k Ω)) := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ 1)
    haveI : FiniteDimensional k (IntermediateField.adjoin k {ζ}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
    refine Subgroup.isOpen_mono
      (H₁ := U ⊓ (IntermediateField.adjoin k {ζ}).fixingSubgroup) ?_ ?_
    · intro g hg
      rw [Subgroup.mem_inf] at hg
      rw [hV, Subgroup.mem_inf, MonoidHom.mem_ker]
      refine ⟨hg.1, ?_⟩
      have hgz : g ζ = ζ := by
        have := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg.2 ζ
          (IntermediateField.mem_adjoin_simple_self k ζ)
        simpa [AlgEquiv.smul_def] using this
      have hs := cyclotomicCharacter.spec l (n := 1)
        (MulSemiringAction.toRingAut (G k Ω) Ω g) ζ hζ.pow_eq_one
      simp only [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply,
        AlgEquiv.smul_def, hgz] at hs
      have key := zmod_eq_intCast_of_primitiveRoot_pow_eq_selmer hζ _ 1 (by rw [zpow_one]; exact hs.symm)
      apply Units.ext
      simpa [KStar.TotallyRealRoots.redPow, cycZ] using key
    · rw [Subgroup.coe_inf]
      exact hU.inter (IntermediateField.fixingSubgroup_isOpen _)
  have hrel : IsOpen ((gamU l U).subgroupOf U : Set U) := by
    rw [Subgroup.coe_subgroupOf]
    exact hVopen.preimage continuous_subtype_val
  have hd : (gamU l U).relIndex U ∣ l - 1 := by
    rw [hV]
    unfold Subgroup.relIndex
    rw [Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf, MonoidHom.comap_ker,
      Subgroup.index_ker]
    refine (Subgroup.card_subgroup_dvd_card _).trans ?_
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hp]
  have hunit : IsUnit (((gamU l U).relIndex U : ℕ) : O) := by
    have h2 := hp.two_le
    have hpos : 0 < (gamU l U).relIndex U := Nat.pos_of_dvd_of_pos hd (by omega)
    have hle : (gamU l U).relIndex U ≤ l - 1 := Nat.le_of_dvd (by omega) hd
    have hnd : ¬ l ∣ (gamU l U).relIndex U := fun h => by
      have := Nat.le_of_dvd hpos h
      omega
    have hc : l.Coprime ((gamU l U).relIndex U) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
    have hu : IsUnit (((gamU l U).relIndex U : ℕ) : ℤ_[l]) :=
      PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hc)
    simpa using hu.map (algebraMap ℤ_[l] O)
  have H2 := selUnit O (G k Ω) (QO l O) (twist₂ l (ψ * chiO k Ω l O ^ n)) hρ (gamU l U) U hVU
    hrel hunit (shaFam k Ω l) (conjStable_shaFam k Ω l)
  have HV := controlGamma k Ω l O (gamU l U) hVopen hVγ ψ n (le_trans hVU hψ) hn
  have hCV : cycU l U ≤ gamU l U := by
    have := cycU_le l (gamU l U)
    rwa [show cycU l (gamU l U) = cycU l U from cycU_levU l U (qExp l)] at this
  have H1 := selRes_injective_range_eq_of_le (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_levU l U (qExp l)) hCV
    (cycU_le l (gamU l U)) (conjStable_shaFam k Ω l) HV
  exact control_lemma _ hCV hVU (cycU_le l U) (conjStable_shaFam k Ω l) H1 H2
