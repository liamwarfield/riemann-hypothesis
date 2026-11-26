module

public import ReciprocityTheory.GroupCohomology.InfRes
public import ReciprocityTheory.GroupCohomology.ConnNatHolds

@[expose] public section

section -- merged from ReciprocityTheory.GroupCohomology.FiniteLevel
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Topology
open scoped Pointwise

universe u

namespace FiniteLevelCohomology

theorem exists_nhds_right_const {K X : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [TopologicalSpace X] [DiscreteTopology X] (f : K → X) (hf : Continuous f) :
    ∃ V ∈ 𝓝 (1 : K), ∀ g v, v ∈ V → f (g * v) = f g := by
  have hfin : (Set.range f).Finite := (isCompact_range hf).finite_of_discrete
  have hV : ∀ x ∈ Set.range f, ∃ V ∈ 𝓝 (1 : K), f ⁻¹' {x} * V ⊆ f ⁻¹' {x} := by
    intro x _
    have hc : IsClosed (f ⁻¹' {x}) := (isClosed_discrete {x}).preimage hf
    exact compact_open_separated_mul_right hc.isCompact ((isOpen_discrete {x}).preimage hf) subset_rfl
  choose! V hV1 hV2 using hV
  refine ⟨⋂ x ∈ hfin.toFinset, V x, ?_, ?_⟩
  · exact (Filter.biInter_finset_mem _).2 fun x hx => hV1 x (hfin.mem_toFinset.1 hx)
  · intro g v hv
    have hx : f g ∈ Set.range f := ⟨g, rfl⟩
    have hvx : v ∈ V (f g) := Set.mem_iInter₂.1 hv (f g) (hfin.mem_toFinset.2 hx)
    exact hV2 (f g) hx (Set.mul_mem_mul (show f g ∈ ({f g} : Set X) from rfl) hvx)

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem stab_mem_nhds (M : TRep R G) [DiscreteTopology M.V] (m : M.V) :
    {a : G | M.rho a m = m} ∈ 𝓝 (1 : G) := by
  have hc : Continuous fun a : G => M.rho a m :=
    M.cont.comp (Continuous.prodMk continuous_id continuous_const)
  exact (hc.isOpen_preimage {m} (isOpen_discrete _)).mem_nhds (by simp)

theorem exists_open_normal [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] {n : ℕ} (c : (Fin n → G) → M.V) (hc : Continuous c) :
    ∃ N : Subgroup G, N.Normal ∧ IsOpen (N : Set G) ∧
      (∀ (g v : Fin n → G), (∀ i, v i ∈ N) → c (g * v) = c g) ∧
      ∀ g, ∀ a ∈ N, M.rho a (c g) = c g := by
  classical
  obtain ⟨V0, hV0, hV0c⟩ := exists_nhds_right_const c hc
  rw [nhds_pi, Filter.mem_pi] at hV0
  obtain ⟨I, -, t, ht, htV⟩ := hV0
  have hU : (⋂ i, t i) ∈ 𝓝 (1 : G) := Filter.iInter_mem.mpr fun i => ht i
  have hfin : (Set.range c).Finite := (isCompact_range hc).finite_of_discrete
  have hS : (⋂ m ∈ Set.range c, {a : G | M.rho a m = m}) ∈ 𝓝 (1 : G) :=
    (Filter.biInter_mem hfin).mpr fun m _ => stab_mem_nhds M m
  have hW : (⋂ i, t i) ∩ (⋂ m ∈ Set.range c, {a : G | M.rho a m = m}) ∈ 𝓝 (1 : G) :=
    Filter.inter_mem hU hS
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one isOpen_interior
    (mem_interior_iff_mem_nhds.mpr hW)
  refine ⟨H.toOpenSubgroup.toSubgroup, H.isNormal', H.toOpenSubgroup.isOpen', fun g v hv => ?_,
    fun g a ha => ?_⟩
  · apply hV0c g v
    apply htV
    intro i _
    have hvi := interior_subset (hH (hv i))
    exact Set.mem_iInter.mp hvi.1 i
  · have hai := interior_subset (hH ha)
    exact Set.mem_iInter₂.mp hai.2 (c g) ⟨g, rfl⟩

end FiniteLevelCohomology

namespace FiniteLevelCohomology

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_level [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] (n : ℕ) (x : M.H n) :
    ∃ (N : Subgroup G) (_ : N.Normal), IsOpen (N : Set G) ∧ ∀ (Q : TRep R (G ⧸ N)) (P : Pair Q M),
      IsInvRep M N Q P → x ∈ LinearMap.range (P.hom.H n) := by
  obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hc' : M.coch.d n c = 0 := hc
  obtain ⟨N, hN, hNo, hconst, hfix⟩ := exists_open_normal M c.1 c.2
  refine ⟨N, hN, hNo, fun Q P hP => ?_⟩
  have := QuotientGroup.discreteTopology hNo
  obtain ⟨hφ, hemb, hrange⟩ := hP
  have hval : ∀ q : Fin n → G ⧸ N, ∃ y, P.u y = c.1 (fun i => (q i).out) :=
    fun q => (hrange _).2 fun a ha => hfix _ a ha
  choose f' hf' using hval
  have hout : ∀ g : Fin n → G,
      c.1 (fun i => (QuotientGroup.mk (s := N) (g i) : G ⧸ N).out) = c.1 g := by
    intro g
    choose v hv using fun i => QuotientGroup.mk_out_eq_mul N (g i)
    have e : (fun i => (QuotientGroup.mk (s := N) (g i) : G ⧸ N).out) = g * fun i => (v i : G) :=
      funext fun i => hv i
    rw [e]
    exact hconst g _ fun i => (v i).2
  have hPf : ∀ g : Fin n → G, P.u (f' fun i => P.φ (g i)) = c.1 g := by
    intro g
    rw [hφ]
    exact (hf' _).trans (hout g)
  let F : Q.coch.X n := ⟨f', continuous_of_discreteTopology⟩
  have h2 : P.hom.f n F = c := Subtype.ext (funext hPf)
  have hF : Q.coch.d n F = 0 := by
    have h1 : P.hom.f (n + 1) (Q.coch.d n F) = M.coch.d n (P.hom.f n F) := P.hom.comm n F
    rw [h2, hc'] at h1
    apply Subtype.ext
    funext q
    have h3 := congrFun (congrArg Subtype.val h1) (fun i => (q i).out)
    have h4 : (fun i => P.φ ((q i).out)) = q := by
      funext i
      rw [hφ]
      exact QuotientGroup.out_eq' (q i)
    change P.u ((Q.coch.d n F).1 fun i => P.φ ((q i).out)) = 0 at h3
    rw [h4] at h3
    exact hemb.injective (h3.trans (map_zero _).symm)
  refine ⟨Submodule.Quotient.mk ⟨F, hF⟩, ?_⟩
  rw [Cx.Hom.H, Submodule.mapQ_apply]
  congr 1
  exact Subtype.ext h2

theorem sum_neg_one_pow (k : ℕ) :
    (1 : R) + ∑ j : Fin (k + 1), (-1 : R) ^ ((j : ℕ) + 1) = if Even k then 0 else 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, ← add_assoc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    rcases Nat.even_or_odd k with hk | hk
    · have h1 : ¬ Even (k + 1) := Nat.not_even_iff_odd.2 (Even.add_one hk)
      rw [if_pos hk, if_neg h1, pow_succ, pow_succ, Even.neg_one_pow hk]
      ring
    · have h1 : Even (k + 1) := Odd.add_one hk
      rw [if_neg (Nat.not_even_iff_odd.2 hk), if_pos h1, pow_succ, pow_succ, Odd.neg_one_pow hk]
      ring

theorem dn_subsingleton {K : Type u} [Group K] [TopologicalSpace K] [Subsingleton K]
    (M : TRep R K) (k : ℕ) (f : (Fin k → K) → M.V) (g : Fin (k + 1) → K) :
    dn M.rho k f g = (if Even k then (0 : R) else 1) • f (fun _ => 1) := by
  have e : ∀ x : Fin k → K, f x = f (fun _ => 1) := fun x => congrArg f (Subsingleton.elim _ _)
  have hs : (∑ j : Fin (k + 1), (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)) =
      ∑ j : Fin (k + 1), (-1 : R) ^ ((j : ℕ) + 1) • f (fun _ => 1) :=
    Finset.sum_congr rfl fun j _ => by rw [e (Fin.contractNth j (· * ·) g)]
  rw [dn_apply, Subsingleton.elim (g 0) 1, map_one, e (fun i => g i.succ), hs, ← Finset.sum_smul,
    ← sum_neg_one_pow k, add_smul, one_smul]
  rfl

theorem H_succ_trivial {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [Subsingleton K] (M : TRep R K) (m : ℕ) (z : M.H (m + 1)) : z = 0 := by
  classical
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [Submodule.Quotient.mk_eq_zero]
  have hwf : ∀ g, dn M.rho (m + 1) w.1.1 g = 0 := fun g => by
    have h := congrArg (fun x : M.coch.X (m + 1 + 1) => x.1 g) w.2
    exact h
  show (w : M.coch.X (m + 1)) ∈ LinearMap.range (M.coch.d m)
  rcases Nat.even_or_odd m with hm | hm
  · have h1 : w.1.1 (fun _ => 1) = 0 := by
      have h := hwf (fun _ => 1)
      rwa [dn_subsingleton, if_neg (Nat.even_add_one.not.mpr (not_not.mpr hm)), one_smul] at h
    refine ⟨0, ?_⟩
    rw [map_zero]
    symm
    apply Subtype.ext
    funext g
    show w.1.1 g = 0
    rw [Subsingleton.elim g (fun _ => 1)]
    exact h1
  · refine ⟨⟨fun _ => w.1.1 (fun _ => 1), ?_⟩, ?_⟩
    · exact continuous_const
    · apply Subtype.ext
      funext g
      show dn M.rho m (fun _ => w.1.1 (fun _ => 1)) g = w.1.1 g
      rw [dn_subsingleton, if_neg (Nat.not_even_iff_odd.mpr hm), one_smul]
      rw [Subsingleton.elim g (fun _ => 1)]

theorem torsion_finite {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [DiscreteTopology H] [Finite H] (Q : TRep R H) (m : ℕ) (y : Q.H (m + 1)) :
    Nat.card H • y = 0 := by
  have : Subsingleton (⊥ : Subgroup H) :=
    ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩
  obtain ⟨cor, -, hcor⟩ := cor_holds R H Q ⊥ (isOpen_discrete _)
  have h := hcor (m + 1) y
  rw [H_succ_trivial _ m ((Pair.res Q (⊥ : Subgroup H).subtype continuous_subtype_val).hom.H (m + 1) y),
    map_zero, Subgroup.index_bot] at h
  exact h.symm

end FiniteLevelCohomology

theorem finiteLevel_holds : FiniteLevelStatement.{u} := by
  intro R _ G _ _ _ _ _ _ M _ n x
  obtain ⟨N, hN, hNo, hlev⟩ := FiniteLevelCohomology.exists_level M n x
  refine ⟨⟨N, hN, hNo, hlev⟩, fun hn => ?_⟩
  obtain ⟨y, hy⟩ := hlev _ _ (InflationRestrictionInvariants.invariants_isInvRep M N)
  haveI : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hNo
  haveI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨Nat.card (G ⧸ N), Nat.card_pos, ?_⟩
  rw [← hy, ← map_nsmul, FiniteLevelCohomology.torsion_finite _ m y, map_zero]

end ReciprocityTheory.Coh
end

section -- merged from ReciprocityTheory.GroupCohomology.LowLES
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal LowDeg

universe u

section SlopeTestRemainingChoices

variable {R : Type u} [CommRing R] {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

theorem lowLES_h0Equiv_pair {M : TRep R G} {M' : TRep R G'} (P : Pair M M') (x : M.H 0) :
    cohomZeroEquivContinuous M' (P.hom.H 0 x) = P.h0 (cohomZeroEquivContinuous M x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x

  exact Subtype.ext (congrArg P.u (congrArg y.1.1 (Subsingleton.elim _ _)))

end SlopeTestRemainingChoices

private theorem exact_of_linearEquiv_conj {R X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [CommRing R]
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂] [AddCommGroup X₃] [Module R X₃]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂] [AddCommGroup Y₃] [Module R Y₃]
    {f : X₁ →ₗ[R] X₂} {g : X₂ →ₗ[R] X₃} {f' : Y₁ →ₗ[R] Y₂} {g' : Y₂ →ₗ[R] Y₃}
    (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂) (e₃ : X₃ ≃ₗ[R] Y₃)
    (hf : ∀ x, e₂ (f x) = f' (e₁ x)) (hg : ∀ x, e₃ (g x) = g' (e₂ x))
    (h : Function.Exact f g) : Function.Exact f' g' := by
  intro y
  obtain ⟨x, rfl⟩ := e₂.surjective y
  rw [← hg, LinearEquiv.map_eq_zero_iff, h x]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨e₁ z, (hf z).symm⟩
  · rintro ⟨w, hw⟩
    obtain ⟨z, rfl⟩ := e₁.surjective w
    refine ⟨z, e₂.injective ?_⟩
    rw [hf]
    exact hw

private theorem injective_of_linearEquiv_conj {R X₁ X₂ Y₁ Y₂ : Type*} [CommRing R]
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂]
    {f : X₁ →ₗ[R] X₂} {f' : Y₁ →ₗ[R] Y₂} (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂)
    (hf : ∀ x, e₂ (f x) = f' (e₁ x)) (h : Function.Injective f) : Function.Injective f' := by
  intro a b hab
  obtain ⟨x, rfl⟩ := e₁.surjective a
  obtain ⟨z, rfl⟩ := e₁.surjective b
  rw [← hf, ← hf] at hab
  rw [h (e₂.injective hab)]

private theorem surjective_of_linearEquiv_conj {R X₁ X₂ Y₁ Y₂ : Type*} [CommRing R]
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂]
    {f : X₁ →ₗ[R] X₂} {f' : Y₁ →ₗ[R] Y₂} (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂)
    (hf : ∀ x, e₂ (f x) = f' (e₁ x)) (h : Function.Surjective f) : Function.Surjective f' := by
  intro y
  obtain ⟨x, hx⟩ := h (e₂.symm y)
  refine ⟨e₁ x, ?_⟩
  rw [← hf, hx, LinearEquiv.apply_symm_apply]

theorem low_degree_long_exact_sequence : LowLESStatement.{u} := by
  intro R _ G _ _ _ A B C i p hadm
  have hses := admissibility_holds R G A B C i p hadm
  obtain ⟨⟨δ, hconn, hles⟩, -⟩ := lES_holds R _ _ _ i.hom p.hom hses

  have n0 : ∀ x : C.H 0, h1EquivOfOrderTwo A (δ 0 x) =
      ((h1EquivOfOrderTwo A).toLinearMap ∘ₗ δ 0 ∘ₗ (cohomZeroEquivContinuous C).symm.toLinearMap) (cohomZeroEquivContinuous C x) := by
    intro x
    show h1EquivOfOrderTwo A (δ 0 x) = h1EquivOfOrderTwo A (δ 0 ((cohomZeroEquivContinuous C).symm (cohomZeroEquivContinuous C x)))
    rw [LinearEquiv.symm_apply_apply]
  have n1 : ∀ x : C.H 1, h2EquivOfOrderTwo A (δ 1 x) =
      ((h2EquivOfOrderTwo A).toLinearMap ∘ₗ δ 1 ∘ₗ (h1EquivOfOrderTwo C).symm.toLinearMap) (h1EquivOfOrderTwo C x) := by
    intro x
    show h2EquivOfOrderTwo A (δ 1 x) = h2EquivOfOrderTwo A (δ 1 ((h1EquivOfOrderTwo C).symm (h1EquivOfOrderTwo C x)))
    rw [LinearEquiv.symm_apply_apply]
  refine ⟨(h1EquivOfOrderTwo A).toLinearMap ∘ₗ δ 0 ∘ₗ (cohomZeroEquivContinuous C).symm.toLinearMap,
    (h2EquivOfOrderTwo A).toLinearMap ∘ₗ δ 1 ∘ₗ (h1EquivOfOrderTwo C).symm.toLinearMap, ?_, ?_,
    injective_of_linearEquiv_conj (cohomZeroEquivContinuous A) (cohomZeroEquivContinuous B) (fun x => lowLES_h0Equiv_pair i x) hles.inj,
    exact_of_linearEquiv_conj (cohomZeroEquivContinuous A) (cohomZeroEquivContinuous B) (cohomZeroEquivContinuous C) (fun x => lowLES_h0Equiv_pair i x)
      (fun x => lowLES_h0Equiv_pair p x) (hles.exB 0),
    exact_of_linearEquiv_conj (cohomZeroEquivContinuous B) (cohomZeroEquivContinuous C) (h1EquivOfOrderTwo A) (fun x => lowLES_h0Equiv_pair p x)
      n0 (hles.exC 0),
    exact_of_linearEquiv_conj (cohomZeroEquivContinuous C) (h1EquivOfOrderTwo A) (h1EquivOfOrderTwo B) n0
      (fun x => h1Equiv_pair (P := i) (x := x)) (hles.exA 0),
    exact_of_linearEquiv_conj (h1EquivOfOrderTwo A) (h1EquivOfOrderTwo B) (h1EquivOfOrderTwo C) (fun x => h1Equiv_pair (P := i) (x := x))
      (fun x => h1Equiv_pair (P := p) (x := x)) (hles.exB 1),
    exact_of_linearEquiv_conj (h1EquivOfOrderTwo B) (h1EquivOfOrderTwo C) (h2EquivOfOrderTwo A) (fun x => h1Equiv_pair (P := p) (x := x))
      n1 (hles.exC 1),
    exact_of_linearEquiv_conj (h1EquivOfOrderTwo C) (h2EquivOfOrderTwo A) (h2EquivOfOrderTwo B) n1
      (fun x => h2Equiv_pair (P := i) (x := x)) (hles.exA 1),
    exact_of_linearEquiv_conj (h2EquivOfOrderTwo A) (h2EquivOfOrderTwo B) (h2EquivOfOrderTwo C) (fun x => h2Equiv_pair (P := i) (x := x))
      (fun x => h2Equiv_pair (P := p) (x := x)) (hles.exB 2),
    fun hsub => surjective_of_linearEquiv_conj (h2EquivOfOrderTwo B) (h2EquivOfOrderTwo C) (fun x => h2Equiv_pair (P := p) (x := x))
      (fun y => (hles.exC 2 y).1 (@Subsingleton.elim _ hsub _ _))⟩
  ·
    intro c b a hb ha
    let b₀ : B.coch.X 0 := ⟨fun _ => b, continuous_const⟩
    have hz : A.coch.d 1 ((oneCocyclesEquivFunctions A).symm a).1 = 0 := ((oneCocyclesEquivFunctions A).symm a).2
    have key : B.coch.d 0 b₀ = i.hom.f 1 ((oneCocyclesEquivFunctions A).symm a).1 := by
      apply Subtype.ext
      funext v
      show dn B.rho 0 (fun _ => b) v = i.u (a.1 (i.φ (v 0)))
      rw [hadm.i_id]
      show dn B.rho 0 (fun _ => b) v = i.u (a.1 (v 0))
      rw [ha (v 0), dn_zero_apply]
      all_goals rfl
    have hcd : C.coch.d 0 (p.hom.f 0 b₀) = 0 := by
      rw [← p.hom.comm, key]
      exact (hses.exact 1).apply_apply_eq_zero _
    have e₁ : (cohomZeroEquivContinuous C).symm c = C.coch.cls 0 (p.hom.f 0 b₀) hcd := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext hb.symm
    have e₂ : h1EquivOfOrderTwo A (A.coch.cls 1 _ hz) = Submodule.Quotient.mk a := by
      show Submodule.Quotient.mk (oneCocyclesEquivFunctions A ((oneCocyclesEquivFunctions A).symm a)) = _
      rw [LinearEquiv.apply_symm_apply]
    show h1EquivOfOrderTwo A (δ 0 ((cohomZeroEquivContinuous C).symm c)) = _
    rw [e₁, hconn 0 b₀ _ hcd hz key]
    exact e₂
  ·
    intro c b a hbc hpb hia
    let b₁ : B.coch.X 1 := ⟨fun v => b (v 0), hbc.comp (continuous_apply 0)⟩
    have hz : A.coch.d 2 ((twoCocyclesEquivFunctions A).symm a).1 = 0 := ((twoCocyclesEquivFunctions A).symm a).2
    have key : B.coch.d 1 b₁ = i.hom.f 2 ((twoCocyclesEquivFunctions A).symm a).1 := by
      apply Subtype.ext
      funext v
      show dn B.rho 1 (fun w => b (w 0)) v = i.u (a.1 (i.φ (v 0), i.φ (v 1)))
      rw [hadm.i_id]
      show dn B.rho 1 (fun w => b (w 0)) v = i.u (a.1 (v 0, v 1))
      rw [hia (v 0, v 1), dn_one_apply, d1_apply]
      all_goals rfl
    have hcd : C.coch.d 1 (p.hom.f 1 b₁) = 0 := by
      rw [← p.hom.comm, key]
      exact (hses.exact 2).apply_apply_eq_zero _
    have e₁ : (h1EquivOfOrderTwo C).symm (Submodule.Quotient.mk c) = C.coch.cls 1 (p.hom.f 1 b₁) hcd := by
      rw [LinearEquiv.symm_apply_eq]
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      show c.1 g = p.u (b (p.φ g))
      rw [hadm.p_id]
      exact (hpb g).symm
    have e₂ : h2EquivOfOrderTwo A (A.coch.cls 2 _ hz) = Submodule.Quotient.mk a := by
      show Submodule.Quotient.mk (twoCocyclesEquivFunctions A ((twoCocyclesEquivFunctions A).symm a)) = _
      rw [LinearEquiv.apply_symm_apply]
    show h2EquivOfOrderTwo A (δ 1 ((h1EquivOfOrderTwo C).symm (Submodule.Quotient.mk c))) = _
    rw [e₁, hconn 1 b₁ _ hcd hz key]
    exact e₂

end ReciprocityTheory.Coh
end
