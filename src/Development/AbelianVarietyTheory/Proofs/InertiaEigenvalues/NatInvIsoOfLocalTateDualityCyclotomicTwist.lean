module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeneratorH2TwistStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
noncomputable section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC

namespace GlobalTheory.FunctorialityH2

section Functor

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
variable {M'' : Type*} [AddCommGroup M''] [Module R M''] [TopologicalSpace M'']
  [IsTopologicalAddGroup M''] [ContinuousConstSMul R M'']
variable (rho : Representation R G M) (rho' : Representation R G M')
  (rho'' : Representation R G M'')

theorem map_H2_congr {u v : M →ₗ[R] M'} (huv : u = v) (hu : Continuous u)
    (hue : ∀ g m, u (rho g m) = rho' g (u m)) (hv : Continuous v)
    (hve : ∀ g m, v (rho g m) = rho' g (v m)) :
    mapH2 rho rho' u hu hue = mapH2 rho rho' v hv hve := by
  subst huv; rfl

theorem map_H2_id :
    mapH2 rho rho LinearMap.id continuous_id (fun _ _ => rfl) = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
  rfl

theorem map_H2_comp (u : M →ₗ[R] M') (hu : Continuous u)
    (hue : ∀ g m, u (rho g m) = rho' g (u m)) (v : M' →ₗ[R] M'') (hv : Continuous v)
    (hve : ∀ g m, v (rho' g m) = rho'' g (v m)) (hvu : Continuous (v ∘ₗ u))
    (hvue : ∀ g m, (v ∘ₗ u) (rho g m) = rho'' g ((v ∘ₗ u) m)) :
    mapH2 rho rho'' (v ∘ₗ u) hvu hvue =
      mapH2 rho' rho'' v hv hve ∘ₗ mapH2 rho rho' u hu hue := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
  rfl

theorem map_H2_zero (h0 : Continuous (0 : M →ₗ[R] M'))
    (h0e : ∀ g m, (0 : M →ₗ[R] M') (rho g m) = rho' g ((0 : M →ₗ[R] M') m)) :
    mapH2 rho rho' 0 h0 h0e = 0 := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
  rfl

theorem map_H2_add (u v : M →ₗ[R] M') (hu : Continuous u)
    (hue : ∀ g m, u (rho g m) = rho' g (u m)) (hv : Continuous v)
    (hve : ∀ g m, v (rho g m) = rho' g (v m)) (huv : Continuous (u + v))
    (huve : ∀ g m, (u + v) (rho g m) = rho' g ((u + v) m)) :
    mapH2 rho rho' (u + v) huv huve = mapH2 rho rho' u hu hue + mapH2 rho rho' v hv hve := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
  rfl

theorem map_H2_smul (c : R) (u : M →ₗ[R] M') (hu : Continuous u)
    (hue : ∀ g m, u (rho g m) = rho' g (u m)) (hcu : Continuous (c • u))
    (hcue : ∀ g m, (c • u) (rho g m) = rho' g ((c • u) m)) :
    mapH2 rho rho' (c • u) hcu hcue = c • mapH2 rho rho' u hu hue := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
  rfl

theorem map_H2_sum {ι : Type*} (s : Finset ι) (u : ι → M →ₗ[R] M') (hu : ∀ j, Continuous (u j))
    (hue : ∀ j g m, u j (rho g m) = rho' g (u j m))
    (hs : Continuous ((∑ j ∈ s, u j : M →ₗ[R] M') : M → M'))
    (hse : ∀ g m, (∑ j ∈ s, u j) (rho g m) = rho' g ((∑ j ∈ s, u j) m)) :
    mapH2 rho rho' (∑ j ∈ s, u j) hs hse = ∑ j ∈ s, mapH2 rho rho' (u j) (hu j) (hue j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact map_H2_zero rho rho' _ _
  | insert a s ha ih =>
    have hc : Continuous ((∑ j ∈ s, u j : M →ₗ[R] M') : M → M') := by
      have := continuous_finsetSum s (fun j _ => hu j)
      convert this using 1; ext x; simp
    have he : ∀ g m, (∑ j ∈ s, u j) (rho g m) = rho' g ((∑ j ∈ s, u j) m) := by
      intro g m; simp only [LinearMap.sum_apply, map_sum, hue]
    rw [map_H2_congr rho rho' (Finset.sum_insert ha) hs hse
        ((hu a).add hc) (fun g m => by simp only [LinearMap.add_apply, hue, he, map_add (f := _)]),
      map_H2_add rho rho' _ _ (hu a) (hue a) hc he, ih hc he, Finset.sum_insert ha]

end Functor

section Phi

variable {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ)

theorem cont_span (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [ContinuousSMul O M] (m : M) : Continuous (LinearMap.toSpanSingleton O M m) :=
  continuous_id.smul continuous_const

theorem span_twist (M : Type) [AddCommGroup M] [Module O M] (m : M) (g : G) (a : O) :
    LinearMap.toSpanSingleton O M m (twist ε O g a) =
      twist ε M g (LinearMap.toSpanSingleton O M m a) := by
  show ((ε g : O) • a) • m = (ε g : O) • (a • m)
  rw [smul_assoc]

variable (z : H2 (twist ε O))

def phi (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul O M] [ContinuousSMul O M] : M →ₗ[O] H2 (twist ε M) where
  toFun m := mapH2 (twist ε O) (twist ε M) (LinearMap.toSpanSingleton O M m) (cont_span M m)
    (span_twist ε M m) z
  map_add' m m' := by
    rw [map_H2_congr (twist ε O) (twist ε M) (LinearMap.ext fun a => by simp [smul_add] :
        LinearMap.toSpanSingleton O M (m + m') =
          LinearMap.toSpanSingleton O M m + LinearMap.toSpanSingleton O M m')
      (cont_span M _) (span_twist ε M _) ((cont_span M m).add (cont_span M m'))
      (fun g a => by simp only [LinearMap.add_apply, span_twist, map_add (f := _)]),
      map_H2_add _ _ _ _ (cont_span M m) (span_twist ε M m) (cont_span M m') (span_twist ε M m')]
    rfl
  map_smul' c m := by
    rw [map_H2_congr (twist ε O) (twist ε M) (LinearMap.ext fun a => by simp [smul_comm a c m] :
        LinearMap.toSpanSingleton O M (c • m) = c • LinearMap.toSpanSingleton O M m)
      (cont_span M _) (span_twist ε M _) ((cont_span M m).const_smul c)
      (fun g a => by simp only [LinearMap.smul_apply, span_twist, map_smul]),
      map_H2_smul _ _ c _ (cont_span M m) (span_twist ε M m)]
    rfl

theorem phi_apply (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [ContinuousSMul O M] (m : M) :
    phi ε z M m = mapH2 (twist ε O) (twist ε M) (LinearMap.toSpanSingleton O M m)
      (cont_span M m) (span_twist ε M m) z := rfl

theorem phi_natural (M M' : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [ContinuousSMul O M]
    [AddCommGroup M'] [Module O M'] [TopologicalSpace M']
    [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [ContinuousSMul O M']
    (f : M →ₗ[O] M') (hf : Continuous f) (hfe : ∀ g m, f (twist ε M g m) = twist ε M' g (f m))
    (m : M) : mapH2 (twist ε M) (twist ε M') f hf hfe (phi ε z M m) = phi ε z M' (f m) := by
  rw [phi_apply, phi_apply, ← LinearMap.comp_apply,
    ← map_H2_comp (twist ε O) (twist ε M) (twist ε M') _ (cont_span M m) (span_twist ε M m) f hf hfe
      (hf.comp (cont_span M m)) (fun g a => by simp only [LinearMap.comp_apply, span_twist, hfe])]
  exact congrArg (fun L : H2 (twist ε O) →ₗ[O] H2 (twist ε M') => L z)
    (map_H2_congr _ _ (LinearMap.ext fun a => by simp) _ _ _ _)

theorem phi_self (a : O) : phi ε z O a = a • z := by
  rw [phi_apply, map_H2_congr (twist ε O) (twist ε O)
    (show LinearMap.toSpanSingleton O O a = a • LinearMap.id from
      LinearMap.ext fun b => by simp [mul_comm])
    _ _ (continuous_id.const_smul a) (fun g b => by
      show a * ((ε g : O) * b) = (ε g : O) * (a * b); ring),
    map_H2_smul _ _ a _ continuous_id (fun _ _ => rfl), map_H2_id]
  rfl

end Phi

section Retract

variable {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ) (z : H2 (twist ε O))

theorem twist_equiv {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (f : M →ₗ[O] M') (g : G) (m : M) : f (twist ε M g m) = twist ε M' g (f m) := by
  show f ((ε g : O) • m) = (ε g : O) • f m
  exact map_smul f _ m

theorem cont_sum {ι M M' : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [AddCommGroup M'] [Module O M'] [TopologicalSpace M'] [IsTopologicalAddGroup M']
    (s : Finset ι) (u : ι → M →ₗ[O] M') (hu : ∀ j, Continuous (u j)) :
    Continuous ((∑ j ∈ s, u j : M →ₗ[O] M') : M → M') := by
  have h := continuous_finsetSum s (fun j _ => hu j)
  convert h using 1 <;> ext x <;> simp only [LinearMap.sum_apply, Finset.sum_apply]

theorem bijective_of_retract (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [ContinuousSMul O M]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (N : ι → Type) [∀ j, AddCommGroup (N j)] [∀ j, Module O (N j)] [∀ j, TopologicalSpace (N j)]
    [∀ j, IsTopologicalAddGroup (N j)] [∀ j, ContinuousConstSMul O (N j)]
    [∀ j, ContinuousSMul O (N j)]
    (N' : κ → Type) [∀ i, AddCommGroup (N' i)] [∀ i, Module O (N' i)] [∀ i, TopologicalSpace (N' i)]
    [∀ i, IsTopologicalAddGroup (N' i)] [∀ i, ContinuousConstSMul O (N' i)]
    [∀ i, ContinuousSMul O (N' i)]
    (p : ∀ j, M →ₗ[O] N j) (s : ∀ j, N j →ₗ[O] M) (p' : ∀ i, M →ₗ[O] N' i)
    (s' : ∀ i, N' i →ₗ[O] M) (hp : ∀ j, Continuous (p j)) (hs : ∀ j, Continuous (s j))
    (hp' : ∀ i, Continuous (p' i)) (hs' : ∀ i, Continuous (s' i))
    (hid : ∀ m, ∑ j, s j (p j m) + ∑ i, s' i (p' i m) = m)
    (hN : ∀ j, Function.Bijective (phi ε z (N j)))
    (hN' : ∀ i, Function.Bijective (phi ε z (N' i))) :
    Function.Bijective (phi ε z M) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro m hm
    have h1 : ∀ j, p j m = 0 := fun j => (injective_iff_map_eq_zero _).1 (hN j).1 _ (by
      rw [← phi_natural ε z M (N j) (p j) (hp j) (twist_equiv ε (p j)), hm, map_zero])
    have h2 : ∀ i, p' i m = 0 := fun i => (injective_iff_map_eq_zero _).1 (hN' i).1 _ (by
      rw [← phi_natural ε z M (N' i) (p' i) (hp' i) (twist_equiv ε (p' i)), hm, map_zero])
    rw [← hid m]
    simp [h1, h2]
  · intro w
    choose n hn using fun j =>
      (hN j).2 (mapH2 (twist ε M) (twist ε (N j)) (p j) (hp j) (twist_equiv ε (p j)) w)
    choose n' hn' using fun i =>
      (hN' i).2 (mapH2 (twist ε M) (twist ε (N' i)) (p' i) (hp' i) (twist_equiv ε (p' i)) w)
    refine ⟨∑ j, s j (n j) + ∑ i, s' i (n' i), ?_⟩
    have k1 : ∀ j, phi ε z M (s j (n j)) = mapH2 (twist ε M) (twist ε M) (s j ∘ₗ p j)
        ((hs j).comp (hp j)) (twist_equiv ε _) w := by
      intro j
      rw [← phi_natural ε z (N j) M (s j) (hs j) (twist_equiv ε (s j)), hn j,
        map_H2_comp (twist ε M) (twist ε (N j)) (twist ε M) (p j) (hp j) (twist_equiv ε _) (s j)
          (hs j) (twist_equiv ε _)]
      rfl
    have k2 : ∀ i, phi ε z M (s' i (n' i)) = mapH2 (twist ε M) (twist ε M) (s' i ∘ₗ p' i)
        ((hs' i).comp (hp' i)) (twist_equiv ε _) w := by
      intro i
      rw [← phi_natural ε z (N' i) M (s' i) (hs' i) (twist_equiv ε (s' i)), hn' i,
        map_H2_comp (twist ε M) (twist ε (N' i)) (twist ε M) (p' i) (hp' i) (twist_equiv ε _) (s' i)
          (hs' i) (twist_equiv ε _)]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, map_sum, Finset.sum_congr rfl (fun j _ => k1 j),
      Finset.sum_congr rfl (fun i _ => k2 i), ← LinearMap.sum_apply, ← LinearMap.sum_apply,
      ← map_H2_sum (twist ε M) (twist ε M) _ _ _ _ (cont_sum _ _ fun j => (hs j).comp (hp j))
        (twist_equiv ε _),
      ← map_H2_sum (twist ε M) (twist ε M) _ _ _ _ (cont_sum _ _ fun i => (hs' i).comp (hp' i))
        (twist_equiv ε _),
      ← LinearMap.add_apply,
      ← map_H2_add (twist ε M) (twist ε M) _ _ _ _ _ _
        ((cont_sum _ _ fun j => (hs j).comp (hp j)).add
          (cont_sum _ _ fun i => (hs' i).comp (hp' i))) (twist_equiv ε _),
      map_H2_congr (twist ε M) (twist ε M)
        (LinearMap.ext fun m => by simpa using hid m : (∑ j, s j ∘ₗ p j) + ∑ i, s' i ∘ₗ p' i =
          LinearMap.id) _ _ continuous_id (fun _ _ => rfl), map_H2_id]
    rfl

end Retract

end GlobalTheory.FunctorialityH2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalIdealDiscreteFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalIdealDiscreteFinite
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.NatQuot

theorem quot_pow_maximalIdeal_discrete_finite :
    ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
      [IsTopologicalRing O], PadicCoeff p O → ∀ k : ℕ,
      DiscreteTopology (O ⧸ IsLocalRing.maximalIdeal O ^ k) ∧ Finite (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  intro p O _ _ _ _ _ hO k
  haveI : CompactSpace O := hO.compact
  set I : Ideal O := IsLocalRing.maximalIdeal O ^ k with hI
  have hopen : IsOpen ((I : Ideal O) : Set O) := (isAdic_iff.mp hO.adic).1 k
  have hdisc : DiscreteTopology (O ⧸ I) := by
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have himg : (Ideal.Quotient.mk I) '' (I : Set O) = {0} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [Ideal.Quotient.eq_zero_iff_mem] using hx
      · rintro rfl
        exact ⟨0, I.zero_mem, map_zero _⟩
    rw [← himg]
    exact QuotientRing.isOpenMap_coe I _ hopen
  refine ⟨hdisc, ?_⟩
  haveI : CompactSpace (O ⧸ I) := Quotient.compactSpace
  exact finite_of_compact_of_discrete

end GlobalTheory.NatQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalIdealDiscreteFiniteStatement
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_maximalIdeal_pow_discrete_and_finite : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O], PadicCoeff p O → ∀ k : ℕ, DiscreteTopology (O ⧸ IsLocalRing.maximalIdeal O ^ k) ∧ Finite (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  first | exact @GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite | exact GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite | (intros; apply GlobalTheory.NatQuot.quot_pow_maximalIdeal_discrete_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCyclotomicCharacterLocalGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCyclotomicCharacterLocalGalois
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.FunctorialityH2

theorem cyc_char_continuous {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    {G : Type} [Group G] [TopologicalSpace G] (hO : PadicCoeff p O) (i : G ≃ₜ* GK p K)
    {ε : G →* Oˣ} (hc : IsCyc p K (carry i ε)) :
    Continuous (fun g : G => ((ε g : Oˣ) : O)) := by
  have := hO.ring
  set ε' : GK p K →* Oˣ := carry i ε with hε'
  have key : ∀ k : ℕ, ∃ H : Subgroup (GK p K), IsOpen (H : Set (GK p K)) ∧
      ∀ h ∈ H, ((ε' h : Oˣ) : O) - 1 ∈ Ideal.span {(p : O) ^ k} := by
    intro k
    have hN : 0 < p ^ k := pow_pos hp.out.pos k
    haveI : NeZero ((p ^ k : ℕ) : PadicAlgCl p) := ⟨by exact_mod_cast hN.ne'⟩
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (p ^ k) (PadicAlgCl p))
      (Polynomial.degree_cyclotomic_pos (p ^ k) (PadicAlgCl p) hN).ne'
    have hpr : IsPrimitiveRoot ζ (p ^ k) := Polynomial.isRoot_cyclotomic_iff.1 hζ
    have hint : IsIntegral K ζ :=
      IsIntegral.of_pow hN (by rw [hpr.pow_eq_one]; exact isIntegral_one)
    haveI := IntermediateField.adjoin.finiteDimensional hint
    refine ⟨(IntermediateField.adjoin K {ζ}).fixingSubgroup,
      IntermediateField.fixingSubgroup_isOpen _, fun h hh => ?_⟩
    have hfix : h ζ = ζ := hh ⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩
    obtain ⟨a, ha, hmem⟩ := hc h k ζ hpr.pow_eq_one
    have hz : ζ ≠ 0 := hpr.ne_zero hN.ne'
    have h1 : ζ ^ ((a : ℤ) - 1) = 1 := by
      rw [zpow_sub₀ hz, zpow_natCast, zpow_one, ← ha, hfix, div_self hz]
    obtain ⟨c, hcdef⟩ := (hpr.zpow_eq_one_iff_dvd _).1 h1
    have h2 : ((a : O) - 1) = ((p : O) ^ k) * (c : O) := by
      have := congrArg (fun z : ℤ => (z : O)) hcdef
      push_cast at this
      exact this
    have h3 : ((ε' h : Oˣ) : O) - 1 = (((ε' h : Oˣ) : O) - a) + ((a : O) - 1) := by ring
    rw [h3, h2]
    exact Ideal.add_mem _ hmem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hcont' : Continuous (fun g : GK p K => ((ε' g : Oˣ) : O)) := by
    rw [continuous_iff_continuousAt]
    intro g0
    rw [ContinuousAt, Filter.tendsto_def]
    intro U hU
    have hV : (fun o : O => ((ε' g0 : Oˣ) : O) + o) ⁻¹' U ∈ nhds (0 : O) :=
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨m, hm⟩ := (isAdic_iff.1 hO.adic).2 _ hV
    obtain ⟨H, hHo, hH⟩ := key m
    have hle : Ideal.span {(p : O) ^ m} ≤ IsLocalRing.maximalIdeal O ^ m :=
      (Ideal.span_singleton_le_iff_mem _).2 (Ideal.pow_mem_pow hO.p_mem m)
    refine Filter.mem_of_superset
      ((hHo.preimage (continuous_const_mul g0⁻¹)).mem_nhds (by simpa using H.one_mem)) ?_
    intro g hg
    have h1 := hH _ hg
    have h2 : ((ε' g : Oˣ) : O) - (ε' g0 : O) ∈ Ideal.span {(p : O) ^ m} := by
      have e : ((ε' g : Oˣ) : O) - (ε' g0 : O) =
          (ε' g0 : O) * (((ε' (g0⁻¹ * g) : Oˣ) : O) - 1) := by
        rw [map_mul, Units.val_mul, mul_sub, ← mul_assoc, ← Units.val_mul, ← map_mul,
          mul_inv_cancel, map_one, Units.val_one, one_mul, mul_one]
      rw [e]
      exact Ideal.mul_mem_left _ _ h1
    have h3 := hm (hle h2)
    simpa using h3
  have e : (fun g : G => ((ε g : Oˣ) : O)) = (fun g : GK p K => ((ε' g : Oˣ) : O)) ∘ i := by
    funext g
    simp only [Function.comp_apply, hε', carry, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    first
    | rw [ContinuousMulEquiv.symm_apply_apply]
    | exact congrArg (fun x => ((ε x : Oˣ) : O)) (i.toMulEquiv.symm_apply_apply g).symm
  rw [e]
  exact hcont'.comp i.continuous

end GlobalTheory.FunctorialityH2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCyclotomicCharacterLocalGaloisStatement
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_cyclotomic_character_localGalois : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G], PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → Continuous (fun g : G => ((ε g : Oˣ) : O)) := by
  first | exact @GlobalTheory.FunctorialityH2.cyc_char_continuous | exact GlobalTheory.FunctorialityH2.cyc_char_continuous | (intros; apply GlobalTheory.FunctorialityH2.cyc_char_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EveryGeneratorH2Twist
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2QuotientFiniteCard
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2LeCardLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardDualZmodLeCard
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory

theorem card_dual_zmod_le_card :
    ∀ (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A] [Module (ZMod n) A] [Finite A],
      Nat.card (Module.Dual (ZMod n) A) ≤ Nat.card A := by
  intro n _ A _ _ _
  classical
  haveI : Fintype A := Fintype.ofFinite A
  let Φ : Module.Dual (ZMod n) A → AddChar A ℂ := fun f =>
    (ZMod.stdAddChar (N := n)).compAddMonoidHom f.toAddMonoidHom
  have hinj : Function.Injective Φ := by
    intro f g h
    ext a
    have h1 := congrArg (fun χ : AddChar A ℂ => χ a) h
    simp only [Φ, AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe] at h1
    exact ZMod.injective_stdAddChar h1
  calc Nat.card (Module.Dual (ZMod n) A) ≤ Nat.card (AddChar A ℂ) :=
        Nat.card_le_card_of_injective Φ hinj
    _ = Nat.card A := by
        rw [Nat.card_eq_fintype_card, AddChar.card_eq, Nat.card_eq_fintype_card]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2LeCardLocal
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory

theorem card_H2_le_of_local_duality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K) M), 0 < r → ContAction rho → Finite (H2 rho) ∧ Nat.card (H2 rho) ≤ Nat.card M := by
  intro hT l _ K hK r M _ _ _ _ _ rho hr hrho
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hfin := (GlobalTheory.finite_H1_H2_of_localTateDuality hT l K hK r M rho hr hrho).2
  obtain ⟨⟨e⟩, -, -, -, h20⟩ := hT l K hK r M rho hr hrho
  refine ⟨hfin, ?_⟩
  haveI : Finite (TDual (ZMod (l ^ r)) M) :=
    Finite.of_injective (fun φ : TDual (ZMod (l ^ r)) M => (φ : M → ZMod (l ^ r)))
      DFunLike.coe_injective
  haveI : Finite (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
    Subtype.finite
  haveI : Finite (H2 ((charRep (Formalism.GaloisCohomology.cycK l K r)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
    Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K))) →ₗ[ZMod (l ^ r)]
      H2 ((charRep (Formalism.GaloisCohomology.cycK l K r)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
    Finite.of_injective (fun f => (f : _ → _)) DFunLike.coe_injective
  calc Nat.card (H2 rho)
      ≤ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K))) →ₗ[ZMod (l ^ r)]
          H2 ((charRep (Formalism.GaloisCohomology.cycK l K r)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
        Nat.card_le_card_of_injective _ h20.1
    _ = Nat.card (Module.Dual (ZMod (l ^ r))
          (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K))))) :=
        Nat.card_congr (LinearEquiv.congrRight e).toEquiv
    _ ≤ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
        GlobalTheory.card_dual_zmod_le_card (l ^ r) _
    _ ≤ Nat.card (TDual (ZMod (l ^ r)) M) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ ≤ Nat.card M := GlobalTheory.card_dual_zmod_le_card (l ^ r) M

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2LeCardLocalStatement
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_H2_le_card_local : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K) M), 0 < r → ContAction rho → Finite (H2 rho) ∧ Nat.card (H2 rho) ≤ Nat.card M := by
  first | exact @GlobalTheory.card_H2_le_of_local_duality | exact GlobalTheory.card_H2_le_of_local_duality | (intros; apply GlobalTheory.card_H2_le_of_local_duality <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCardH2CompEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCardH2CompEquiv
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.TransportH2

variable {R : Type} [CommRing R] {G Γ : Type} [Group G] [TopologicalSpace G] [Group Γ]
  [TopologicalSpace Γ] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

theorem apply_symm' (i : G ≃ₜ* Γ) (y : Γ) : i (i.symm y) = y := i.apply_symm_apply y

theorem symm_apply' (i : G ≃ₜ* Γ) (x : G) : i.symm (i x) = x := i.symm_apply_apply x

noncomputable def cocycleEquiv (i : G ≃ₜ* Γ) (rho : Representation R Γ M) :
    Z2 rho ≃ₗ[R] Z2 (rho.comp i.toMulEquiv.toMonoidHom) :=
  { restrictCocycles2 rho i.toMulEquiv.toMonoidHom i.continuous with
    invFun := fun f => ⟨fun p => f.1 (i.symm p.1, i.symm p.2),
      f.2.1.comp (i.symm.continuous.prodMap i.symm.continuous), fun g h k => by
        have e := f.2.2 (i.symm g) (i.symm h) (i.symm k)
        have e' : (rho.comp i.toMulEquiv.toMonoidHom) (i.symm g) = rho g := by
          show rho (i (i.symm g)) = rho g
          rw [apply_symm']
        rw [e'] at e
        show rho g (f.1 (i.symm h, i.symm k)) - f.1 (i.symm (g * h), i.symm k) +
          f.1 (i.symm g, i.symm (h * k)) - f.1 (i.symm g, i.symm h) = 0
        rw [map_mul, map_mul]
        exact e⟩
    left_inv := fun f => by
      apply Subtype.ext; funext p
      show f.1 (i (i.symm p.1), i (i.symm p.2)) = f.1 p
      rw [apply_symm', apply_symm']
    right_inv := fun f => by
      apply Subtype.ext; funext p
      show f.1 (i.symm (i p.1), i.symm (i p.2)) = f.1 p
      rw [symm_apply', symm_apply'] }

theorem map_cocycleEquiv (i : G ≃ₜ* Γ) (rho : Representation R Γ M) :
    ((B2 rho).comap (Z2 rho).subtype).map (cocycleEquiv i rho : Z2 rho →ₗ[R] _) =
      (B2 (rho.comp i.toMulEquiv.toMonoidHom)).comap
        (Z2 (rho.comp i.toMulEquiv.toMonoidHom)).subtype := by
  ext f
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · rintro ⟨f', hf', rfl⟩
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem rho _).1 hf'
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c ∘ i, hc.comp i.continuous, ?_⟩
    funext p
    have e := congrFun hcf (i p.1, i p.2)
    change _ = f'.1 (i p.1, i p.2)
    rw [← e]
    simp [d1]
    rfl
  · intro hf
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 hf
    refine ⟨(cocycleEquiv i rho).symm f, (separated_dvr_second_cohomology_mem rho _).2
      ⟨c ∘ i.symm, hc.comp i.symm.continuous, ?_⟩, (cocycleEquiv i rho).apply_symm_apply f⟩
    funext p
    have e := congrFun hcf (i.symm p.1, i.symm p.2)
    change _ = f.1 (i.symm p.1, i.symm p.2)
    rw [← e]
    simp [d1, symm_apply']
    exact congrArg (fun g => rho g (c (i.symm p.2))) (apply_symm' i p.1).symm

theorem natCard_H2_comp (i : G ≃ₜ* Γ) (rho : Representation R Γ M) :
    Nat.card (H2 (rho.comp i.toMulEquiv.toMonoidHom)) = Nat.card (H2 rho) :=
  (Nat.card_congr (Submodule.Quotient.equiv _ _ (cocycleEquiv i rho)
    (map_cocycleEquiv i rho)).toEquiv).symm

end GlobalTheory.TransportH2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCardH2CompEquivStatement
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCard_H2_comp_equiv : ∀ {R : Type} [CommRing R] {G Γ : Type} [Group G] [TopologicalSpace G] [Group Γ] [TopologicalSpace Γ] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (i : G ≃ₜ* Γ) (rho : Representation R Γ M), Nat.card (H2 (rho.comp i.toMulEquiv.toMonoidHom)) = Nat.card (H2 rho) := by
  first | exact @GlobalTheory.TransportH2.natCard_H2_comp | exact GlobalTheory.TransportH2.natCard_H2_comp | (intros; apply GlobalTheory.TransportH2.natCard_H2_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2EqSameAction
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2EqSameAction
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.H2CardScalars

theorem card_H2_eq_of_same_action {R S : Type} [CommRing R] [CommRing S] {G : Type} [Group G]
    [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module R M] [Module S M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [ContinuousConstSMul S M]
    (rho : Representation R G M) (rho' : Representation S G M)
    (h : ∀ g m, rho g m = rho' g m) : Nat.card (H2 rho) = Nat.card (H2 rho') := by
  have hZ : ∀ f : G × G → M, f ∈ Z2 rho ↔ f ∈ Z2 rho' := by
    intro f; rw [mem_cocycles2, mem_cocycles2]; simp only [h]
  have hd : ∀ c : G → M, d1 rho c = d1 rho' c := fun c => funext fun p => by
    simp only [d1, LinearMap.coe_mk, AddHom.coe_mk, h]
  have hB : ∀ f : G × G → M, f ∈ B2 rho ↔ f ∈ B2 rho' := by
    intro f; rw [separated_dvr_second_cohomology_mem, separated_dvr_second_cohomology_mem]; simp only [hd]
  let e : Z2 rho ≃ Z2 rho' := Equiv.subtypeEquiv (Equiv.refl _) hZ
  apply Nat.card_congr
  refine Quotient.congr e ?_
  intro a b
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
  simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub]
  exact hB _

end GlobalTheory.H2CardScalars
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2EqSameActionStatement
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_H2_eq_same_action : ∀ {R S : Type} [CommRing R] [CommRing S] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module R M] [Module S M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [ContinuousConstSMul S M] (rho : Representation R G M) (rho' : Representation S G M), (∀ g m, rho g m = rho' g m) → Nat.card (H2 rho) = Nat.card (H2 rho') := by
  first | exact @GlobalTheory.H2CardScalars.card_H2_eq_of_same_action | exact GlobalTheory.H2CardScalars.card_H2_eq_of_same_action | (intros; apply GlobalTheory.H2CardScalars.card_H2_eq_of_same_action <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2QuotientFiniteCard
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.QuotientH2Count

def zmodScalarRep (n : ℕ) {O Γ M : Type} [CommRing O] [Group Γ] [AddCommGroup M] [Module O M]
    [Module (ZMod n) M] (χ : Γ →* Oˣ) : Representation (ZMod n) Γ M where
  toFun g := (DistribSMul.toAddMonoidHom M ((χ g : Oˣ) : O)).toZModLinearMap n
  map_one' := LinearMap.ext fun x => by
    show ((χ 1 : Oˣ) : O) • x = x
    rw [map_one, Units.val_one, one_smul]
  map_mul' g h := LinearMap.ext fun x => by
    show ((χ (g * h) : Oˣ) : O) • x = ((χ g : Oˣ) : O) • (((χ h : Oˣ) : O) • x)
    rw [map_mul, Units.val_mul, mul_smul]

theorem h2_twist_card_of_zmod {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
    (hTD : Formalism.GaloisCohomology.LocalTateDualityK) (hK : FiniteDimensional ℚ_[p] K) (i : G ≃ₜ* GK p K)
    (ε : G →* Oˣ) (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [DiscreteTopology M] [Finite M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M]
    (r : ℕ) [Module (ZMod (p ^ r)) M] (hr : 0 < r)
    (hc : Continuous fun q : G × M => ((ε q.1 : Oˣ) : O) • q.2) :
    Finite (H2 (twist ε M)) ∧ Nat.card (H2 (twist ε M)) ≤ Nat.card M := by
  obtain ⟨rho, hrho⟩ : ∃ rho : Representation (ZMod (p ^ r)) (GK p K) M,
      ∀ (g : GK p K) (x : M), rho g x = ((ε (i.symm g) : Oˣ) : O) • x :=
    ⟨zmodScalarRep (p ^ r) (carry i ε), fun _ _ => rfl⟩
  have hcont : ReciprocityTheory.Gal.ContAction rho := by
    have e : (fun q : GK p K × M => rho q.1 q.2) =
        (fun q : G × M => ((ε q.1 : Oˣ) : O) • q.2) ∘ fun q => (i.symm q.1, q.2) := by
      funext q; exact hrho q.1 q.2
    unfold ReciprocityTheory.Gal.ContAction
    rw [e]
    exact hc.comp ((i.symm.continuous.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨hF, hC⟩ := GlobalTheory.T.card_H2_le_card_local hTD p K hK r M rho hr hcont
  have htr := GlobalTheory.T.natCard_H2_comp_equiv i rho
  have hsc := GlobalTheory.T.card_H2_eq_same_action (rho.comp i.toMulEquiv.toMonoidHom) (twist ε M) (fun g x => by
      show rho (i g) x = ((ε g : Oˣ) : O) • x
      rw [hrho, i.symm_apply_apply])
  have hcard : Nat.card (H2 (twist ε M)) = Nat.card (H2 rho) := by
    rw [← hsc, htr]
  refine ⟨?_, hcard ▸ hC⟩
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  exact Nat.card_pos.ne'

theorem h2_quot_card : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ k : ℕ, Finite (H2 (twist ε (O ⧸ IsLocalRing.maximalIdeal O ^ k))) ∧ Nat.card (H2 (twist ε (O ⧸ IsLocalRing.maximalIdeal O ^ k))) ≤ Nat.card (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  intro p _ K O _ _ _ _ _ G _ _ hTD hK hO i ε hε k
  obtain ⟨hdisc, hfin⟩ := GlobalTheory.T.quotient_maximalIdeal_pow_discrete_and_finite hO k
  haveI := hdisc
  haveI := hfin
  have hkill : ∀ x : O ⧸ IsLocalRing.maximalIdeal O ^ k, (p ^ (k + 1)) • x = 0 := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_nsmul, Ideal.Quotient.eq_zero_iff_mem, nsmul_eq_mul]
    push_cast
    rw [pow_succ, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hO.p_mem k)
  have hce := GlobalTheory.T.continuous_cyclotomic_character_localGalois hO i hε
  have hc : Continuous fun q : G × (O ⧸ IsLocalRing.maximalIdeal O ^ k) =>
      ((ε q.1 : Oˣ) : O) • q.2 := by
    have hq : Continuous (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ k)) := continuous_quot_mk
    have e : (fun q : G × (O ⧸ IsLocalRing.maximalIdeal O ^ k) => ((ε q.1 : Oˣ) : O) • q.2) =
        fun q => Ideal.Quotient.mk _ ((ε q.1 : Oˣ) : O) * q.2 := by
      funext q; exact Algebra.smul_def _ _
    rw [e]
    exact ((hq.comp hce).comp continuous_fst).mul continuous_snd
  letI : Module (ZMod (p ^ (k + 1))) (O ⧸ IsLocalRing.maximalIdeal O ^ k) :=
    AddCommGroup.zmodModule hkill
  exact h2_twist_card_of_zmod hTD hK i ε _ (k + 1) (Nat.succ_pos k) hc

end GlobalTheory.QuotientH2Count
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2QuotientFiniteCardStatement
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_H2_twist_quotient_pow_and_card_le : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ k : ℕ, Finite (H2 (twist ε (O ⧸ IsLocalRing.maximalIdeal O ^ k))) ∧ Nat.card (H2 (twist ε (O ⧸ IsLocalRing.maximalIdeal O ^ k))) ≤ Nat.card (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  first | exact @GlobalTheory.QuotientH2Count.h2_quot_card | exact GlobalTheory.QuotientH2Count.h2_quot_card | (intros; apply GlobalTheory.QuotientH2Count.h2_quot_card <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiInjectiveQuotientH2
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiInjectiveQuotientH2
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.NatQuot

theorem exists_continuous_div {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] {X : Type} [TopologicalSpace X]
    {π : O} (hπ : π ≠ 0) (u : X → O) (hu : Continuous u) (hd : ∀ x, π ∣ u x) :
    ∃ w : X → O, Continuous w ∧ ∀ x, u x = π * w x := by
  choose w hw using hd
  have hemb : Topology.IsClosedEmbedding (fun a : O => π * a) :=
    (continuous_const.mul continuous_id).isClosedEmbedding (mul_right_injective₀ hπ)
  refine ⟨w, hemb.isEmbedding.continuous_iff.2 ?_, hw⟩
  have : ((fun a : O => π * a) ∘ w) = u := funext fun x => (hw x).symm
  rw [this]; exact hu

theorem phi_quot_pow_injective :
    ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
      [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G],
      PadicCoeff p O → ∀ {ε : G →* Oˣ}, Continuous (fun g : G => ((ε g : Oˣ) : O)) →
      ∀ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) → ∀ k : ℕ,
      Function.Injective (phi ε z (O ⧸ IsLocalRing.maximalIdeal O ^ k)) := by
  intro p O _ _ _ _ _ G _ _ _ hO ε hε z hz k
  haveI : CompactSpace O := hO.compact
  haveI : T2Space O := hO.t2
  haveI hdisc := (quot_pow_maximalIdeal_discrete_finite hO k).1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hI : IsLocalRing.maximalIdeal O ^ k = Ideal.span {ϖ ^ k} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hπ : ϖ ^ k ≠ 0 := pow_ne_zero k hϖ.ne_zero
  generalize IsLocalRing.maximalIdeal O ^ k = I at hI hdisc
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨z₀, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hm' : cocycles2Map (twist ε O) (twist ε (O ⧸ I))
      (LinearMap.toSpanSingleton O (O ⧸ I) (Ideal.Quotient.mk I a)) (cont_span _ _)
      (span_twist ε _ _) z₀ ∈ (B2 (twist ε (O ⧸ I))).comap (Z2 (twist ε (O ⧸ I))).subtype :=
    (Submodule.Quotient.mk_eq_zero _).1 hm
  obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 hm'
  have hcf' : ∀ g h : G, (ε g : O) • c h - c (g * h) + c g =
      z₀.1 (g, h) • Ideal.Quotient.mk I a := fun g h => congrFun hcf (g, h)
  choose s hs using (Ideal.Quotient.mk_surjective (I := I))
  have hcs : Continuous (fun g => s (c g)) := continuous_of_discreteTopology.comp hc
  set u : G × G → O := fun q =>
    a * z₀.1 q - ((ε q.1 : O) * s (c q.2) - s (c (q.1 * q.2)) + s (c q.1)) with hu
  have huc : Continuous u :=
    (continuous_const.mul z₀.2.1).sub
      ((((hε.comp continuous_fst).mul (hcs.comp continuous_snd)).sub
        (hcs.comp (continuous_fst.mul continuous_snd))).add (hcs.comp continuous_fst))
  have hud : ∀ q, ϖ ^ k ∣ u q := by
    rintro ⟨g, h⟩
    rw [← Ideal.mem_span_singleton, ← hI, ← Ideal.Quotient.eq_zero_iff_mem]
    have e := hcf' g h
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] at e
    simp only [hu, map_sub, map_add (f := _), map_mul, hs]
    rw [e]; ring
  obtain ⟨w, hwc, hw⟩ := exists_continuous_div hπ u huc hud
  have hwZ : w ∈ Z2 (twist ε O) := by
    refine ⟨hwc, fun g h l => ?_⟩
    apply mul_left_cancel₀ hπ
    have e : (ε g : O) * z₀.1 (h, l) - z₀.1 (g * h, l) + z₀.1 (g, h * l) - z₀.1 (g, h) = 0 :=
      z₀.2.2 g h l
    have e1 := hw (h, l)
    have e2 := hw (g * h, l)
    have e3 := hw (g, h * l)
    have e4 := hw (g, h)
    simp only [hu, map_mul, Units.val_mul, mul_assoc] at e1 e2 e3 e4
    show ϖ ^ k * ((ε g : O) * w (h, l) - w (g * h, l) + w (g, h * l) - w (g, h)) = ϖ ^ k * 0
    linear_combination a * e - (ε g : O) * e1 + e2 - e3 + e4
  obtain ⟨b, hb⟩ := hz.2 (Submodule.Quotient.mk ⟨w, hwZ⟩)
  have key : a • (Submodule.Quotient.mk z₀ : H2 (twist ε O)) =
      (ϖ ^ k * b) • (Submodule.Quotient.mk z₀ : H2 (twist ε O)) := by
    simp only at hb
    rw [mul_smul, hb, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.eq]
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => s (c g), hcs, funext fun q => ?_⟩
    have e := hw q
    show (ε q.1 : O) * s (c q.2) - s (c (q.1 * q.2)) + s (c q.1) = a * z₀.1 q - ϖ ^ k * w q
    rw [← e, hu]; ring
  have hab : a = ϖ ^ k * b := hz.1 key
  rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
  exact ⟨b, hab⟩

end GlobalTheory.NatQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiInjectiveQuotientH2Statement
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_injective_quotient_H2 : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G], PadicCoeff p O → ∀ {ε : G →* Oˣ}, Continuous (fun g : G => ((ε g : Oˣ) : O)) → ∀ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) → ∀ k : ℕ, Function.Injective (phi ε z (O ⧸ IsLocalRing.maximalIdeal O ^ k)) := by
  first | exact @GlobalTheory.NatQuot.phi_quot_pow_injective | exact GlobalTheory.NatQuot.phi_quot_pow_injective | (intros; apply GlobalTheory.NatQuot.phi_quot_pow_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EveryGeneratorH2Twist
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.FunctorialityH2

theorem bijective_phi_quot_pow : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) → ∀ k : ℕ, Function.Bijective (phi ε z (O ⧸ IsLocalRing.maximalIdeal O ^ k)) := by
  intro p _ K O _ _ _ _ _ G _ _ hT hK hO i ε hε z hz k
  haveI : ContinuousMul G := ⟨by
    have h : (fun q : G × G => q.1 * q.2) = fun q => i.symm (i q.1 * i q.2) := by
      funext q; simp
    rw [h]
    exact i.symm.continuous.comp
      ((i.continuous.comp continuous_fst).mul (i.continuous.comp continuous_snd))⟩
  have hinj := GlobalTheory.T.phi_injective_quotient_H2 hO (GlobalTheory.T.continuous_cyclotomic_character_localGalois hO i hε) z hz k
  obtain ⟨_, hcard⟩ := GlobalTheory.T.finite_H2_twist_quotient_pow_and_card_le hT hK hO i hε k
  exact hinj.bijective_of_nat_card_le hcard

end GlobalTheory.FunctorialityH2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EveryGeneratorH2TwistStatement
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.every_generator_H2_twist : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) → ∀ k : ℕ, Function.Bijective (phi ε z (O ⧸ IsLocalRing.maximalIdeal O ^ k)) := by
  first | exact @GlobalTheory.FunctorialityH2.bijective_phi_quot_pow | exact GlobalTheory.FunctorialityH2.bijective_phi_quot_pow | (intros; apply GlobalTheory.FunctorialityH2.bijective_phi_quot_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivDvrFgModuleStructure
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivDvrFgModuleStructure
namespace GlobalTheory


open IsDiscreteValuationRing in
theorem dvr_fg_module_structure : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M], ∃ (n m : ℕ) (e : Fin m → ℕ),
    Nonempty (M ≃ₗ[O] (Fin n → O) × ((i : Fin m) → O ⧸ IsLocalRing.maximalIdeal O ^ e i)) := by
  intro O _ _ _ M _ _ _
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum (R := O) (M := M)
  have hid : ∀ i, (Submodule.span O {p i ^ e i} : Submodule O O) =
      (IsLocalRing.maximalIdeal O ^ e i : Ideal O) := by
    intro i
    rw [(irreducible_iff_uniformizer _).1 (hp i), Ideal.span_singleton_pow]
  classical
  let σ := Fintype.equivFin ι
  refine ⟨n, Fintype.card ι, fun j => e (σ.symm j), ⟨?_⟩⟩
  exact f ≪≫ₗ LinearEquiv.prodCongr (Finsupp.linearEquivFunOnFinite O O (Fin n))
    (DirectSum.linearEquivFunOnFintype O ι (fun i => O ⧸ O ∙ p i ^ e i) ≪≫ₗ
      LinearEquiv.piCongrRight (fun i => Submodule.quotEquivOfEq _ _ (hid i)) ≪≫ₗ
      (LinearEquiv.piCongrLeft O (fun i : ι => O ⧸ IsLocalRing.maximalIdeal O ^ e i) σ.symm).symm)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivDvrFgModuleStructureStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_dvr_fg_module_structure : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M], ∃ (n m : ℕ) (e : Fin m → ℕ), Nonempty (M ≃ₗ[O] (Fin n → O) × ((i : Fin m) → O ⧸ IsLocalRing.maximalIdeal O ^ e i)) := by
  first | exact @GlobalTheory.dvr_fg_module_structure | exact GlobalTheory.dvr_fg_module_structure | (intros; apply GlobalTheory.dvr_fg_module_structure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearMapContinuousOfCompactSpaceOfFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearMapContinuousOfCompactSpaceOfFinite
namespace GlobalTheory

theorem linearMap_continuous_of_compactSpace_of_finite
    {O : Type} [CommRing O] [TopologicalSpace O] [CompactSpace O] {M M' : Type}
    [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] [T2Space M] [Module.Finite O M] [AddCommGroup M'] [Module O M']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousSMul O M']
    (f : M →ₗ[O] M') : Continuous f := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' O M
  have hgc : Continuous g := g.continuous_on_pi
  have hq : Topology.IsQuotientMap g := hgc.isClosedMap.isQuotientMap hgc hg
  have hfg : Continuous (f ∘ g) := (f.comp g).continuous_on_pi
  exact hq.continuous_iff.mpr hfg

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearMapContinuousOfCompactSpaceOfFiniteStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_linearMap_of_finite : ∀ {O : Type} [CommRing O] [TopologicalSpace O] [CompactSpace O] {M M' : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul O M] [T2Space M] [Module.Finite O M] [AddCommGroup M'] [Module O M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousSMul O M'] (f : M →ₗ[O] M'), Continuous f := by
  first | exact @GlobalTheory.linearMap_continuous_of_compactSpace_of_finite | exact GlobalTheory.linearMap_continuous_of_compactSpace_of_finite | (intros; apply GlobalTheory.linearMap_continuous_of_compactSpace_of_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatInvIsoOfLocalTateDualityCyclotomicTwist
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory

theorem natInvIso_of_localTateDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) : NatInvIso := by
  intro p _ K O _ _ _ _ G _ _ hK hO i ε hε
  haveI := hO.ring; haveI := hO.compact; haveI := hO.t2
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_generator_H2_twist hT hK hO i hε
  have hq := GlobalTheory.T.every_generator_H2_twist hT hK hO i hε z hz
  have hbij : ∀ (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul O M] [ContinuousSMul O M] [T2Space M] [Module.Finite O M],
      Function.Bijective (phi ε z M) := by
    intro M _ _ _ _ _ _ _ _
    obtain ⟨n, m, e, ⟨E⟩⟩ := GlobalTheory.T.exists_equiv_dvr_fg_module_structure (O := O) M
    refine bijective_of_retract ε z M (fun _ : Fin n => O) (fun i : Fin m => O ⧸ IsLocalRing.maximalIdeal O ^ e i)
      (fun j => LinearMap.proj j ∘ₗ LinearMap.fst O _ _ ∘ₗ E.toLinearMap)
      (fun j => E.symm.toLinearMap ∘ₗ LinearMap.inl O _ _ ∘ₗ LinearMap.single O (fun _ : Fin n => O) j)
      (fun i => LinearMap.proj i ∘ₗ LinearMap.snd O _ _ ∘ₗ E.toLinearMap)
      (fun i => E.symm.toLinearMap ∘ₗ LinearMap.inr O _ _ ∘ₗ
        LinearMap.single O (fun i : Fin m => O ⧸ IsLocalRing.maximalIdeal O ^ e i) i)
      (fun j => GlobalTheory.T.continuous_linearMap_of_finite _) (fun j => GlobalTheory.T.continuous_linearMap_of_finite _) (fun i => GlobalTheory.T.continuous_linearMap_of_finite _) (fun i => ?_) ?_
      (fun j => ?_) (fun i => hq (e i))
    · have := GlobalTheory.T.continuous_linearMap_of_finite (M := O) (M' := M) ((E.symm.toLinearMap ∘ₗ LinearMap.inr O _ _ ∘ₗ
        LinearMap.single O (fun i : Fin m => O ⧸ IsLocalRing.maximalIdeal O ^ e i) i) ∘ₗ
          (IsLocalRing.maximalIdeal O ^ e i).mkQ)
      exact (Submodule.isOpenQuotientMap_mkQ _).isQuotientMap.continuous_iff.2 this
    · intro x
      conv_rhs => rw [← E.symm_apply_apply x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ← map_sum, ← map_add (f := _)]
      congr 1
      ext <;> simp [Finset.univ_sum_single]
    · show Function.Bijective (phi ε z O)
      rw [show ⇑(phi ε z O) = fun a : O => a • z from funext (phi_self ε z)]
      exact hz
  refine ⟨⟨fun M _ _ _ _ _ h => by
      haveI := h.csmul; haveI := h.t2; haveI := h.fg
      exact (LinearEquiv.ofBijective (phi ε z M) (hbij M)).symm, ?_⟩⟩
  intro M M' _ _ _ _ _ _ _ _ _ _ h h' f hf w
  haveI := h.csmul; haveI := h.t2; haveI := h.fg
  haveI := h'.csmul; haveI := h'.t2; haveI := h'.fg
  obtain ⟨m, rfl⟩ := (hbij M).2 w
  show (LinearEquiv.ofBijective (phi ε z M') (hbij M')).symm _ =
    f ((LinearEquiv.ofBijective (phi ε z M) (hbij M)).symm _)
  rw [phi_natural ε z M M' f hf (twist_map ε f) m]
  rw [LinearEquiv.ofBijective_symm_apply_apply, LinearEquiv.ofBijective_symm_apply_apply]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatInvIsoOfLocalTateDualityCyclotomicTwistStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natInvIso_of_localTateDuality_cyclotomicTwist : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.NatInvIso := by
  first | exact @GlobalTheory.natInvIso_of_localTateDuality | exact GlobalTheory.natInvIso_of_localTateDuality | (intros; apply GlobalTheory.natInvIso_of_localTateDuality <;> assumption)
end
