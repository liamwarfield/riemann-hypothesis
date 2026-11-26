module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaOfPow
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasis
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CupFlipContinuousCocycle

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasis
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LatTop

section General

variable {LL O V : Type} [Field LL] [CommRing O] [IsDomain O] [Algebra O LL] [IsFractionRing O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]

theorem exists_basis (M : Submodule O V) (hfg : M.FG) (hfree : Module.Free O M)
    (hspan : Submodule.span LL (M : Set V) = ⊤) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι LL V),
      ∀ x, x ∈ M ↔ ∀ i, ∃ a : O, b.repr x i = algebraMap O LL a := by
  haveI : Module.Finite O M := Module.Finite.iff_fg.2 hfg
  have hfull : ∀ v : V, ∃ c : O, c ≠ 0 ∧ ∃ m : M, algebraMap O LL c • v = (m : V) := by
    intro v
    have hv : v ∈ Submodule.span LL (M : Set V) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_ne_zero, ⟨x, hx⟩, by simp⟩
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, m, hm⟩ := hx
      obtain ⟨d, hd, m', hm'⟩ := hy
      refine ⟨c * d, mul_ne_zero hc hd, d • m + c • m', ?_⟩
      have e1 : ((d • m + c • m' : M) : V) =
          algebraMap O LL d • (m : V) + algebraMap O LL c • (m' : V) := by
        simp [algebraMap_smul]
      rw [e1, ← hm, ← hm', map_mul, smul_add, smul_smul, smul_smul,
        mul_comm (algebraMap O LL d)]
    | smul a x _ hx =>
      obtain ⟨c, hc, m, hm⟩ := hx
      obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors O) a
      refine ⟨d * c, mul_ne_zero (nonZeroDivisors.ne_zero d.2) hc, n • m, ?_⟩
      have e1 : ((n • m : M) : V) = algebraMap O LL n • (m : V) := by simp [algebraMap_smul]
      simp only at hnd
      rw [e1, ← hm, ← hnd, map_mul, smul_smul, smul_smul]
      congr 1
      ring
  obtain ⟨b, hb, hr⟩ := GlobalTheory.Cyc.exists_basis_of_fullLattice (R := O) (F := LL) (M := M) (V := V)
    M.subtype.toAddMonoidHom Subtype.val_injective
    (fun c m => by simp [algebraMap_smul]) (by simpa using hfull) (Module.Free.chooseBasis O M)
  refine ⟨_, inferInstance, b, fun x => ⟨fun hx i => ⟨_, hr ⟨x, hx⟩ i⟩, fun h => ?_⟩⟩
  choose a ha using h
  rw [← b.sum_repr x]
  refine M.sum_mem fun i _ => ?_
  rw [ha i, algebraMap_smul]
  refine M.smul_mem _ ?_
  rw [hb i]
  exact (Module.Free.chooseBasis O M i).2

theorem mem_of_dual_dual {V' : Type} [AddCommGroup V'] [Module LL V'] [FiniteDimensional LL V]
    [FiniteDimensional LL V'] (M : Submodule O V) (hfg : M.FG) (hfree : Module.Free O M)
    (hspan : Submodule.span LL (M : Set V) = ⊤) (M' : Set V') (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (hinj : ∀ y, (∀ x, P x y = 0) → y = 0) (hrank : finrank LL V = finrank LL V')
    (hM' : ∀ y, y ∈ M' ↔ ∀ x ∈ M, ∃ a : O, P x y = algebraMap O LL a)
    (x : V) (hx : ∀ y ∈ M', ∃ a : O, P x y = algebraMap O LL a) : x ∈ M := by
  obtain ⟨ι, _, b, hb⟩ := exists_basis M hfg hfree hspan
  have hi : Function.Injective P.flip := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    exact hinj y fun x => by simpa using LinearMap.congr_fun hy x
  have hs : Function.Surjective P.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq, hrank])).1 hi
  have hy : ∀ i, ∃ y : V', ∀ v, P v y = b.repr v i := fun i => by
    obtain ⟨y, hy⟩ := hs (b.coord i)
    exact ⟨y, fun v => by simpa using LinearMap.congr_fun hy v⟩
  choose y hy using hy
  rw [hb]
  intro i
  have hyi : y i ∈ M' := (hM' _).2 fun v hv => by
    obtain ⟨a, ha⟩ := (hb v).1 hv i
    exact ⟨a, by rw [hy, ha]⟩
  obtain ⟨a, ha⟩ := hx _ hyi
  exact ⟨a, by rw [← hy, ha]⟩

variable [TopologicalSpace LL] [IsTopologicalRing LL] [TopologicalSpace V] [IsModuleTopology LL V]

theorem isCompact_lattice (hC : IsCompact (Set.range (algebraMap O LL))) (M : Submodule O V)
    (hfg : M.FG) (hfree : Module.Free O M) (hspan : Submodule.span LL (M : Set V) = ⊤) :
    IsCompact (M : Set V) := by
  obtain ⟨ι, _, b, hb⟩ := exists_basis M hfg hfree hspan
  haveI := IsModuleTopology.toContinuousSMul LL V
  haveI := IsModuleTopology.toContinuousAdd LL V
  have hc : Continuous fun c : ι → LL => ∑ i, c i • b i :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have he : (M : Set V) = (fun c : ι → LL => ∑ i, c i • b i) ''
      Set.pi Set.univ (fun _ => Set.range (algebraMap O LL)) := by
    ext x
    constructor
    · intro hx
      refine ⟨fun i => b.repr x i, fun i _ => ?_, b.sum_repr x⟩
      obtain ⟨a, ha⟩ := (hb x).1 hx i
      exact ⟨a, ha.symm⟩
    · rintro ⟨c, hc', rfl⟩
      rw [SetLike.mem_coe, hb]
      intro i
      obtain ⟨a, ha⟩ := hc' i (Set.mem_univ i)
      exact ⟨a, by rw [b.repr_sum_self, ha]⟩
  rw [he]
  exact (isCompact_univ_pi fun _ => hC).image hc

theorem hasBasis_lattice (M : Submodule O V) (hopen : IsOpen (M : Set V))
    (hcomp : IsCompact (M : Set V)) (ϖ : O) (hϖ : ϖ ≠ 0)
    (hB : (nhds (0 : LL)).HasBasis (fun _ : ℕ => True)
      (fun n => (fun o : O => algebraMap O LL (ϖ ^ n * o)) '' Set.univ)) :
    (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (M : Set V)) := by
  haveI := IsModuleTopology.toContinuousSMul LL V
  have hne : ∀ n : ℕ, algebraMap O LL (ϖ ^ n) ≠ 0 := fun n => by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O LL)]
    exact pow_ne_zero n hϖ
  refine Filter.hasBasis_iff.2 fun t => ⟨fun ht => ?_, ?_⟩
  · have hn : IsOpen ((fun p : LL × V => p.1 • p.2) ⁻¹' interior t) :=
      isOpen_interior.preimage continuous_smul
    obtain ⟨u, v, hu, -, h0, hv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : LL)))
      hcomp hn (by
        rintro ⟨a, x⟩ ⟨ha, -⟩
        have ha' : a = 0 := ha
        simpa [ha'] using mem_interior_iff_mem_nhds.2 ht)
    obtain ⟨n, -, hn⟩ := hB.mem_iff.1 (hu.mem_nhds (h0 rfl))
    refine ⟨n, trivial, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h1 : algebraMap O LL (ϖ ^ n) ∈ u := hn ⟨1, trivial, by simp⟩
    have h2 := huv (Set.mk_mem_prod h1 (hv hx))
    have h3 : algebraMap O LL (ϖ ^ n) • x ∈ t := interior_subset h2
    rwa [algebraMap_smul] at h3
  · rintro ⟨n, -, hn⟩
    have hU : IsOpen ((fun y : V => (algebraMap O LL (ϖ ^ n))⁻¹ • y) ⁻¹' (M : Set V)) :=
      hopen.preimage (continuous_const_smul _)
    refine Filter.mem_of_superset (hU.mem_nhds (by simp)) fun y hy => hn ⟨_, hy, ?_⟩
    show ϖ ^ n • (algebraMap O LL (ϖ ^ n))⁻¹ • y = y
    rw [← algebraMap_smul LL (ϖ ^ n), smul_smul, mul_inv_cancel₀ (hne n), one_smul]

theorem exists_pow_smul_mem {G : Type} [TopologicalSpace G] [CompactSpace G] (M : Submodule O V)
    (hopen : IsOpen (M : Set V)) (ϖ : O)
    (hB : (nhds (0 : LL)).HasBasis (fun _ : ℕ => True)
      (fun n => (fun o : O => algebraMap O LL (ϖ ^ n * o)) '' Set.univ))
    (c : G → V) (hc : Continuous c) : ∃ n : ℕ, ∀ g, ϖ ^ n • c g ∈ M := by
  haveI := IsModuleTopology.toContinuousSMul LL V
  have hcov : Set.range c ⊆ ⋃ n : ℕ, {x : V | ϖ ^ n • x ∈ M} := by
    rintro _ ⟨g, rfl⟩
    have hU : IsOpen ((fun a : LL => a • c g) ⁻¹' (M : Set V)) :=
      hopen.preimage (continuous_id.smul continuous_const)
    obtain ⟨n, -, hn⟩ := hB.mem_iff.1 (hU.mem_nhds (by simp))
    have h1 : algebraMap O LL (ϖ ^ n) • c g ∈ M := hn ⟨1, trivial, by simp⟩
    rw [algebraMap_smul] at h1
    exact Set.mem_iUnion.2 ⟨n, h1⟩
  have hop : ∀ n : ℕ, IsOpen {x : V | ϖ ^ n • x ∈ M} := fun n => by
    have : {x : V | ϖ ^ n • x ∈ M} = (fun x : V => algebraMap O LL (ϖ ^ n) • x) ⁻¹' (M : Set V) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, algebraMap_smul]
    rw [this]
    exact hopen.preimage (continuous_const_smul _)
  have hdir : Directed (· ⊆ ·) fun n : ℕ => {x : V | ϖ ^ n • x ∈ M} :=
    Monotone.directed_le (f := fun n : ℕ => {x : V | ϖ ^ n • x ∈ M}) fun m n hmn x hx => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have : ϖ ^ (m + k) • x = ϖ ^ k • ϖ ^ m • x := by rw [smul_smul, pow_add, mul_comm]
      show ϖ ^ (m + k) • x ∈ M
      rw [this]
      exact M.smul_mem _ hx
  obtain ⟨n, hn⟩ := (isCompact_range hc).elim_directed_cover _ hop hcov hdir
  exact ⟨n, fun g => hn ⟨g, rfl⟩⟩

end General

end GlobalTheory.CompanionTheory.LatTop
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsDualLattices
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.LocDual.Lat

section Basis

variable {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {W : Type} [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W]

theorem mem_span_basis {ι : Type} [Fintype ι] (b : Basis ι LL W) (y : W) :
    y ∈ Submodule.span O (Set.range b) ↔ ∀ i, b.repr y i ∈ Set.range (algebraMap O LL) := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      by_cases h : j = i
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Finsupp.single_apply, h]⟩
    | zero => intro i; exact ⟨0, by simp⟩
    | add x z _ _ hx hz =>
      intro i
      obtain ⟨a, ha⟩ := hx i
      obtain ⟨c, hc⟩ := hz i
      exact ⟨a + c, by simp [ha, hc]⟩
    | smul a x _ hx =>
      intro i
      obtain ⟨c, hc⟩ := hx i
      refine ⟨a * c, ?_⟩
      rw [← algebraMap_smul LL a x, map_smul, Finsupp.smul_apply, ← hc, map_mul, smul_eq_mul]
  · intro h
    rw [← b.sum_repr y]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨a, ha⟩ := h i
    rw [← ha, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Basis

section Dual

variable {LL : Type} [Field LL] {O : Type} [CommRing O] [IsDomain O] [Algebra O LL]
  [IsFractionRing O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [FiniteDimensional LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  [FiniteDimensional LL V']

theorem exists_dual (T : Submodule O V) (hfg : T.FG) (hfree : Module.Free O T)
    (hspan : Submodule.span LL (T : Set V) = ⊤) (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (hr : ∀ y, (∀ x, P x y = 0) → y = 0) (hd : finrank LL V = finrank LL V') :
    ∃ T' : Submodule O V', T'.FG ∧ Module.Free O T' ∧ Submodule.span LL (T' : Set V') = ⊤ ∧
      (∀ y, y ∈ T' ↔ ∀ x ∈ T, ∃ a : O, P x y = algebraMap O LL a) ∧
      (∀ x, x ∈ T ↔ ∀ y ∈ T', ∃ a : O, P x y = algebraMap O LL a) := by
  classical
  haveI : Module.Finite O T := Module.Finite.iff_fg.2 hfg
  let bT := Module.Free.chooseBasis O T
  let ι := Module.Free.ChooseBasisIndex O T
  haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype O T
  let e : ι → V := fun i => (bT i : V)
  have hli : LinearIndependent O e :=
    bT.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hliL : LinearIndependent LL e := (LinearIndependent.iff_fractionRing O LL).1 hli
  have hTe : T = Submodule.span O (Set.range e) := by
    have h := congrArg (Submodule.map T.subtype) bT.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h.symm
  have hsp : ⊤ ≤ Submodule.span LL (Set.range e) := by
    rw [← hspan, Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, hTe] at hx
    have := Submodule.span_le_restrictScalars O LL (Set.range e) hx
    exact this
  let bV : Basis ι LL V := Basis.mk hliL hsp
  have hbV : ∀ i, bV i = e i := fun i => Basis.mk_apply hliL hsp i
  have hinj : Function.Injective P.flip := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    exact hr y fun x => by simpa using congrArg (fun f => f x) hy
  let φ : V' ≃ₗ[LL] Dual LL V := LinearMap.linearEquivOfInjective P.flip hinj
    (by rw [Subspace.dual_finrank_eq, hd])
  let bb : Basis ι LL V' := bV.dualBasis.map φ.symm
  have hflip : ∀ j x, P x (bb j) = bV.repr x j := by
    intro j x
    have h1 : φ (bb j) = bV.coord j := by simp [bb]
    have h2 : φ (bb j) x = P x (bb j) := rfl
    rw [← h2, h1]; rfl
  have hcoord : ∀ i y, P (e i) y = bb.repr y i := by
    intro i y
    have : (P (e i)) = bb.coord i := by
      refine bb.ext fun j => ?_
      rw [hflip, ← hbV]
      simp [Finsupp.single_apply, eq_comm]
    rw [this]; rfl
  have hTV : T = Submodule.span O (Set.range bV) := by
    rw [hTe]; congr 2; ext x; simp [hbV]
  have hpair : ∀ x ∈ T, ∀ y ∈ Submodule.span O (Set.range bb), ∃ a : O, P x y = algebraMap O LL a := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [hflip]
      rw [hTV] at hx
      obtain ⟨a, ha⟩ := (mem_span_basis bV x).1 hx j
      exact ⟨a, ha.symm⟩
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha⟩ := hy
      obtain ⟨c, hc⟩ := hz
      exact ⟨a + c, by simp [ha, hc]⟩
    | smul a y _ hy =>
      obtain ⟨c, hc⟩ := hy
      refine ⟨a * c, ?_⟩
      rw [← algebraMap_smul LL a y, map_smul, hc, map_mul, smul_eq_mul]
  refine ⟨Submodule.span O (Set.range bb), Submodule.fg_span (Set.finite_range _), ?_, ?_, ?_, ?_⟩
  · have hl : LinearIndependent O bb :=
      (LinearIndependent.iff_fractionRing O LL).2 bb.linearIndependent
    exact Module.Free.of_basis (Basis.span hl)
  · refine top_le_iff.1 ?_
    rw [← bb.span_eq]
    exact Submodule.span_mono (Submodule.subset_span)
  · intro y
    constructor
    · intro hy x hx
      exact hpair x hx y hy
    · intro h
      refine (mem_span_basis bb y).2 fun i => ?_
      obtain ⟨a, ha⟩ := h (e i) (by rw [hTe]; exact Submodule.subset_span ⟨i, rfl⟩)
      exact ⟨a, by rw [← hcoord, ha]⟩
  · intro x
    constructor
    · intro hx y hy
      exact hpair x hx y hy
    · intro h
      rw [hTV]
      refine (mem_span_basis bV x).2 fun j => ?_
      obtain ⟨a, ha⟩ := h (bb j) (Submodule.subset_span ⟨j, rfl⟩)
      exact ⟨a, by rw [← hflip, ha]⟩

end Dual

section Stable

variable {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL]
  {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL]
  [IsFractionRing O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [FiniteDimensional LL V] [TopologicalSpace V] [IsModuleTopology LL V]

theorem exists_stable (hO : IsOpen (Set.range (algebraMap O LL)))
    (ρ : Representation LL G V) (cont : ∀ x, Continuous fun g => ρ g x) :
    Nonempty (Lattice (O := O) ρ) := by
  classical
  let b : Basis (Fin (finrank LL V)) LL V := Module.finBasis LL V
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  have hc : ∀ i j, Continuous fun g => b.repr (ρ g (b i)) j := by
    intro i j
    have hl : Continuous (b.coord j) := IsModuleTopology.continuous_of_linearMap (b.coord j)
    exact hl.comp (cont (b i))
  let Wa : nonZeroDivisors O → Set G := fun a =>
    {g | ∀ i j, algebraMap O LL a * b.repr (ρ g (b i)) j ∈ Set.range (algebraMap O LL)}
  have hWo : ∀ a, IsOpen (Wa a) := by
    intro a
    have h : Wa a = ⋂ i, ⋂ j, (fun g => algebraMap O LL a * b.repr (ρ g (b i)) j) ⁻¹'
        Set.range (algebraMap O LL) := by
      ext g
      simp only [Wa, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [h]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (continuous_const.mul (hc i j))
  have hcov : (Set.univ : Set G) ⊆ ⋃ a, Wa a := by
    intro g _
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
      (Finset.univ : Finset (Fin (finrank LL V) × Fin (finrank LL V)))
      (fun p => b.repr (ρ g (b p.1)) p.2)
    refine Set.mem_iUnion.2 ⟨d, fun i j => ?_⟩
    obtain ⟨c, hc'⟩ := hd (i, j) (Finset.mem_univ _)
    refine ⟨c, ?_⟩
    rw [hc']
    exact Algebra.smul_def (d : O) _
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover Wa hWo hcov
  let a : O := ∏ s ∈ t, (s : O)
  have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => nonZeroDivisors.ne_zero s.2
  have hbound : ∀ g i j, algebraMap O LL a * b.repr (ρ g (b i)) j ∈
      Set.range (algebraMap O LL) := by
    intro g i j
    obtain ⟨s, hs, hg⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ g))
    obtain ⟨c, hc'⟩ := hg i j
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun s : nonZeroDivisors O => (s : O)) hs
    have hq' : a = (s : O) * q := hq
    refine ⟨q * c, ?_⟩
    rw [hq', map_mul, map_mul, hc']
    ring
  let T0 : Submodule O V := Submodule.span O (Set.range b)
  let T : Submodule O V := Submodule.span O (Set.range fun p : G × Fin (finrank LL V) => ρ p.1 (b p.2))
  have hTa : ∀ x ∈ T, a • x ∈ T0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g, i⟩, rfl⟩ := hx
      refine (mem_span_basis b _).2 fun j => ?_
      rw [← algebraMap_smul LL a, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact hbound g i j
    | zero => simp
    | add x z _ _ hx hz => rw [smul_add]; exact T0.add_mem hx hz
    | smul c x _ hx => rw [smul_comm]; exact T0.smul_mem c hx
  let φ : T →ₗ[O] T0 := (a • (LinearMap.id : V →ₗ[O] V)).restrict hTa
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : a • (x : V) = 0 := congrArg Subtype.val hx
    rw [← algebraMap_smul LL a, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd ((map_eq_zero_iff _ hinj).1 h1) ha0
    · exact Subtype.ext h1
  have hl0 : LinearIndependent O b :=
    (LinearIndependent.iff_fractionRing O LL).2 b.linearIndependent
  haveI : Module.Free O T0 := Module.Free.of_basis (Basis.span hl0)
  haveI : Module.Finite O T0 := Module.Finite.span_of_finite O (Set.finite_range _)
  haveI : Module.Finite O T := Module.Finite.of_injective φ hφ
  haveI : Module.Free O (LinearMap.range φ) := Module.free_of_finite_type_torsion_free'
  refine ⟨{ T := T, stable := ?_, fg := Module.Finite.iff_fg.1 inferInstance,
            free := Module.Free.of_equiv (LinearEquiv.ofInjective φ hφ).symm, span := ?_ }⟩
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g, i⟩, rfl⟩ := hx
      refine Submodule.subset_span ⟨(h * g, i), ?_⟩
      simp [map_mul, Module.End.mul_apply]
    | zero => simp
    | add x z _ _ hx hz => rw [map_add (f := _)]; exact T.add_mem hx hz
    | smul c x _ hx =>
      rw [LinearMap.map_smul_of_tower]
      exact T.smul_mem c hx
  · refine top_le_iff.1 ?_
    rw [← b.span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨(1, i), by simp⟩

end Stable

end GlobalTheory.CompanionTheory.LocDual.Lat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicTwistFiniteModuleCoboundary
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

theorem GlobalTheory.CompanionTheory.LocDual.cup_flip_cob {G W W' R : Type} [Group G] [TopologicalSpace G] [AddCommGroup W]
    [AddCommGroup W'] [CommRing R] (χ : G → R) (a : G → W →+ W) (a' : G → W' →+ W') (P : W →+ W' →+ R)
    (hP : ∀ g x y, P (a g x) (a' g y) = χ g * P x y) (y : G → W) (x : G → W')
    (hy : IsLocallyConstant y ∧ ∀ g h, y (g * h) = y g + a g (y h))
    (hx : IsLocallyConstant x ∧ ∀ g h, x (g * h) = x g + a' g (x h)) (z z' : G × G → R)
    (hz : (z = (fun p => P (y p.1) (a' p.1 (x p.2))) ∧ z' = (fun p => P (a p.1 (y p.2)) (x p.1))) ∨
      (z' = (fun p => P (y p.1) (a' p.1 (x p.2))) ∧ z = (fun p => P (a p.1 (y p.2)) (x p.1))))
    (h : ∃ f : G → R, IsLocallyConstant f ∧ ∀ g h, χ g * f h - f (g * h) + f g = z (g, h)) :
    ∃ f : G → R, IsLocallyConstant f ∧ ∀ g h, χ g * f h - f (g * h) + f g = z' (g, h) := by
  obtain ⟨f, hf, hfd⟩ := h
  have hlc : IsLocallyConstant fun g => P (y g) (x g) :=
    IsLocallyConstant.comp₂ hy.1 hx.1 fun u v => P u v
  have hid : ∀ g h, χ g * P (y h) (x h) - P (y (g * h)) (x (g * h)) + P (y g) (x g) =
      -P (y g) (a' g (x h)) - P (a g (y h)) (x g) := by
    intro g h
    rw [hy.2, hx.2, ← hP]
    simp only [map_add (f := _), AddMonoidHom.add_apply]
    abel
  refine ⟨fun g => -P (y g) (x g) - f g, (hlc.neg).sub hf, fun g h => ?_⟩
  have h1 := hid g h
  have h2 := hfd g h
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only at h2 ⊢ <;> linear_combination -h1 - h2
end

section -- merged from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsTorRange
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.TI

theorem exists_ext_zmod {N : ℕ} [NeZero N] {A B : Type} [AddCommGroup A] [AddCommGroup B] (j : A →+ B)
    (hj : Function.Injective j) (hB : ∀ b : B, N • b = 0) (ψ : A →+ ZMod N) :
    ∃ ψ' : B →+ ZMod N, ∀ a, ψ' (j a) = ψ a := by
  have hN : (N : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne N
  let e : ℤ →+ AddCircle (1 : ℚ) := zmultiplesHom _ (((1 / N : ℚ)) : AddCircle (1 : ℚ))
  have he : ∀ k : ℤ, e k = (((k : ℚ) / N : ℚ) : AddCircle (1 : ℚ)) := fun k => by
    change k • (((1 / N : ℚ)) : AddCircle (1 : ℚ)) = _
    rw [← QuotientAddGroup.mk_zsmul]
    congr 1
    simp [div_eq_mul_inv]
  have heN : e (N : ℤ) = 0 := by
    rw [he]
    have : (((N : ℤ) : ℚ) / N : ℚ) = 1 := by push_cast; field_simp
    rw [this]
    exact AddCircle.coe_period 1
  let ι : ZMod N →+ AddCircle (1 : ℚ) := ZMod.lift N ⟨e, heN⟩
  have hι : ∀ k : ℤ, ι (k : ZMod N) = e k := fun k => ZMod.lift_coe N ⟨e, heN⟩ k
  have hinj : Function.Injective ι := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective c
    rw [hι, he, AddCircle.coe_eq_zero_iff] at hc
    obtain ⟨m, hm⟩ := hc
    have h1 : (k : ℚ) = m * N := by
      have : (m : ℚ) = (k : ℚ) / N := by simpa using hm
      rw [this]; field_simp
    have h2 : k = m * N := by exact_mod_cast h1
    rw [h2]
    simp
  have hsurj : ∀ x : AddCircle (1 : ℚ), N • x = 0 → ∃ c, ι c = x := by
    intro x hx
    obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
    change N • ((q : ℚ) : AddCircle (1 : ℚ)) = 0 at hx
    rw [← QuotientAddGroup.mk_nsmul] at hx
    change (((N • q : ℚ)) : AddCircle (1 : ℚ)) = 0 at hx
    rw [AddCircle.coe_eq_zero_iff] at hx
    obtain ⟨m, hm⟩ := hx
    refine ⟨(m : ZMod N), ?_⟩
    rw [hι, he]
    have : (m : ℚ) / N = q := by
      have : (m : ℚ) = N * q := by simpa using hm
      rw [this]; field_simp
    rw [this]
  let φ : CharacterModule A := ι.comp ψ
  obtain ⟨Φ, hΦ⟩ := CharacterModule.dual_surjective_of_injective (R := ℤ) j.toIntLinearMap hj φ
  have hΦ' : ∀ a, Φ (j a) = ι (ψ a) := fun a => DFunLike.congr_fun hΦ a
  have hs : ∀ b, ∃ c, ι c = Φ b := fun b => hsurj _ (by rw [← map_nsmul, hB, map_zero])
  choose f hf using hs
  refine ⟨AddMonoidHom.mk' f fun x y => hinj (by rw [map_add (f := _), hf, hf, hf, map_add (f := _)]), fun a => hinj ?_⟩
  change ι (f (j a)) = _
  rw [hf, hΦ']

theorem descent {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Q : Type} [AddCommGroup Q]
    (ρ : G → Q →+ Q) (hmul : ∀ g h q, ρ (g * h) q = ρ g (ρ h q)) {N : ℕ} [NeZero N]
    (χ : G →* (ZMod N)ˣ) (hχ : IsLocallyConstant fun g => (χ g : ZMod N)) (M S : AddSubgroup Q) (hMS : M ≤ S)
    (hS : ∀ q ∈ S, N • q = 0) (hact : ∀ g, ∀ q ∈ S, ρ g q = (χ g : ZMod N).val • q)
    (F : G → Q) (hF : IsLocallyConstant F) (hFS : ∀ g, F g ∈ S) (z : G × G → Q)
    (hz : ∀ g h, ρ g (F h) - F (g * h) + F g = z (g, h)) (hzM : ∀ p, z p ∈ M)
    [Module (ZMod N) ↥M]
    (hTop : ∀ zz : G × G → ↥M, IsLocallyConstant zz →
      (∀ g h k, (χ g : ZMod N) • zz (h, k) - zz (g * h, k) + zz (g, h * k) - zz (g, h) = 0) →
      (∀ ψ : ↥M →+ ZMod N, ∃ f : G → ZMod N, IsLocallyConstant f ∧
        ∀ g h, (χ g : ZMod N) * f h - f (g * h) + f g = ψ (zz (g, h))) →
      ∃ f : G → ↥M, IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod N) • f h - f (g * h) + f g = zz (g, h)) :
    ∃ f : G → Q, IsLocallyConstant f ∧ (∀ g, f g ∈ M) ∧ ∀ g h, ρ g (f h) - f (g * h) + f g = z (g, h) := by
  have hsm : ∀ (g : G) (m : ↥M), (((χ g : ZMod N) • m : ↥M) : Q) = ρ g m := fun g m => by
    rw [hact g _ (hMS m.2), ← AddSubgroup.coe_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_zmod_val]
  have hzlc : IsLocallyConstant z := by
    have h1 : z = fun p : G × G => (χ p.1 : ZMod N).val • F p.2 - F (p.1 * p.2) + F p.1 := funext fun p => by
      rw [← hact _ _ (hFS _), hz]
    rw [h1]
    exact (((hχ.comp_continuous continuous_fst).comp₂ (hF.comp_continuous continuous_snd)
      (fun c q => c.val • q)).sub (hF.comp_continuous continuous_mul)).add
        (hF.comp_continuous continuous_fst)
  obtain ⟨f, hf, hfe⟩ := hTop (fun p => ⟨z p, hzM p⟩)
    (IsLocallyConstant.desc _ Subtype.val hzlc Subtype.val_injective)
    (fun g h k => Subtype.ext (by
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_sub, AddSubgroup.coe_zero, hsm]
      rw [← hz h k, ← hz (g * h) k, ← hz g (h * k), ← hz g h]
      simp only [map_add (f := _), map_sub, hmul, mul_assoc]
      abel))
    (fun ψ => by
      obtain ⟨ψ', hψ'⟩ := exists_ext_zmod (N := N) (AddSubgroup.inclusion hMS)
        (AddSubgroup.inclusion_injective hMS) (fun b => Subtype.ext (hS _ b.2)) ψ
      refine ⟨fun g => ψ' ⟨F g, hFS g⟩, (IsLocallyConstant.desc (fun g => (⟨F g, hFS g⟩ : ↥S)) Subtype.val hF
        Subtype.val_injective).comp _, fun g h => ?_⟩
      have h1 : (χ g : ZMod N).val • (⟨F h, hFS h⟩ : ↥S) - ⟨F (g * h), hFS _⟩ + ⟨F g, hFS g⟩ =
          AddSubgroup.inclusion hMS ⟨z (g, h), hzM _⟩ := Subtype.ext (by
        change _ = z (g, h)
        rw [← hz]
        simp [hact g _ (hFS h)])
      have h2 := congrArg ψ' h1
      rw [hψ', map_add (f := _), map_sub, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val] at h2
      exact h2)
  refine ⟨fun g => (f g : Q), hf.comp _, fun g => (f g).2, fun g h => ?_⟩
  have h1 := congrArg (Subtype.val) (hfe g h)
  simpa only [AddSubgroup.coe_add, AddSubgroup.coe_sub, hsm] using h1

section Coeff

variable {LL O : Type} [Field LL] [CommRing O] [Algebra O LL] (T : Submodule O LL)

theorem smul_mk (a : O) (x : LL) :
    a • (Submodule.Quotient.mk x : LL ⧸ T) = Submodule.Quotient.mk (algebraMap O LL a * x) := by
  rw [← Submodule.Quotient.mk_smul, Algebra.smul_def]

def tor (ϖ : O) (s : ℕ) : AddSubgroup (LL ⧸ T) := (Submodule.torsionBy O (LL ⧸ T) (ϖ ^ s)).toAddSubgroup

theorem mem_tor {ϖ : O} {s : ℕ} {q : LL ⧸ T} : q ∈ tor T ϖ s ↔ ϖ ^ s • q = 0 :=
  Submodule.mem_torsionBy_iff _ _

theorem mk_mem_tor {ϖ : O} {s : ℕ} {x : LL} :
    (Submodule.Quotient.mk x : LL ⧸ T) ∈ tor T ϖ s ↔ algebraMap O LL ϖ ^ s * x ∈ T := by
  rw [mem_tor, smul_mk, map_pow, Submodule.Quotient.mk_eq_zero]

theorem tor_mono {ϖ : O} {r s : ℕ} (h : r ≤ s) : tor T ϖ r ≤ tor T ϖ s := fun q hq => by
  rw [mem_tor] at hq ⊢
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm, pow_add, mul_smul, hq, smul_zero]

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]

theorem finite_tor (hT : T = LinearMap.range (Algebra.linearMap O LL)) {ϖ : O} (hϖ : Irreducible ϖ)
    (hfin : Finite (O ⧸ Ideal.span {ϖ})) (r : ℕ) : Finite ↥(tor T ϖ r) := by
  have h0 : algebraMap O LL ϖ ≠ 0 := fun h =>
    hϖ.ne_zero (IsFractionRing.injective O LL (by rw [h, map_zero]))
  have hq : Finite (O ⧸ Ideal.span {ϖ ^ r}) := by
    rw [← Ideal.span_singleton_pow]
    exact Ideal.finite_quotient_pow (Submodule.fg_span_singleton _) r
  let x₀ : LL := (algebraMap O LL ϖ ^ r)⁻¹
  have hmem : ∀ a : O, (Submodule.Quotient.mk (algebraMap O LL a * x₀) : LL ⧸ T) ∈ tor T ϖ r := fun a => by
    rw [mk_mem_tor, hT]
    refine ⟨a, ?_⟩
    change algebraMap O LL a = _
    have : algebraMap O LL ϖ ^ r ≠ 0 := pow_ne_zero _ h0
    simp only [x₀]
    field_simp
  refine Finite.of_surjective (α := O ⧸ Ideal.span {ϖ ^ r})
    (fun c => ⟨Submodule.Quotient.mk (algebraMap O LL (Quotient.out c) * x₀), hmem _⟩) ?_
  intro m
  obtain ⟨q, hq'⟩ := m
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective T q
  rw [mk_mem_tor, hT] at hq'
  obtain ⟨a, ha⟩ := hq'
  refine ⟨Ideal.Quotient.mk _ a, Subtype.ext ?_⟩
  change (Submodule.Quotient.mk _ : LL ⧸ T) = Submodule.Quotient.mk x
  rw [Submodule.Quotient.eq, hT]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1
    (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {ϖ ^ r}) a)))
  refine ⟨b, ?_⟩
  change algebraMap O LL b = _
  have h1 : algebraMap O LL ϖ ^ r ≠ 0 := pow_ne_zero _ h0
  have h2 : x = algebraMap O LL a * x₀ := by
    simp only [x₀]
    change algebraMap O LL a = _ at ha
    rw [ha]
    field_simp
  have h3 := congrArg (algebraMap O LL) hb
  rw [RingHom.map_sub, map_mul, map_pow] at h3
  rw [h2, ← sub_mul, h3]
  simp only [x₀]
  field_simp

theorem exists_tor {ϖ : O} (hϖ : Irreducible ϖ) (hT : T = LinearMap.range (Algebra.linearMap O LL))
    (q : LL ⧸ T) : ∃ s, ϖ ^ s • q = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective T q
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨k, u⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
  obtain ⟨u, hu⟩ := u
  refine ⟨k, ?_⟩
  rw [smul_mk, Submodule.Quotient.mk_eq_zero, hT]
  refine ⟨(u : O) * a, ?_⟩
  change algebraMap O LL ((u : O) * a) = _
  have h1 : algebraMap O LL b ≠ 0 := fun h =>
    hb0 (IsFractionRing.injective O LL (by rw [h, map_zero]))
  rw [← hu, map_mul, map_mul]
  field_simp

theorem exists_tor_range {X : Type} {F : X → LL ⧸ T} (hF : (Set.range F).Finite) {ϖ : O} (hϖ : Irreducible ϖ)
    (hT : T = LinearMap.range (Algebra.linearMap O LL)) (r : ℕ) : ∃ s, r ≤ s ∧ ∀ g, F g ∈ tor T ϖ s := by
  choose c hc using exists_tor T hϖ hT
  refine ⟨r + hF.toFinset.sup c, Nat.le_add_right _ _, fun g => ?_⟩
  refine tor_mono T ((Finset.le_sup (f := c) (hF.mem_toFinset.2 ⟨g, rfl⟩)).trans (Nat.le_add_left _ _))
    (mem_tor T |>.2 (hc _))

end Coeff

section Int

variable {l : ℕ} [Fact l.Prime]

theorem lc_toZModPow (n : ℕ) : IsLocallyConstant (PadicInt.toZModPow (p := l) n) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hq : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds x hq] with y hy
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    ← PadicInt.norm_le_pow_iff_mem_span_pow]
  simpa [dist_eq_norm] using hy

theorem mk_mul_int {LL O : Type} [Field LL] [Algebra ℚ_[l] LL] [CommRing O] [Algebra O LL]
    (T : Submodule O LL)
    (hZ : ∀ u : ℤ_[l], algebraMap ℚ_[l] LL (u : ℚ_[l]) ∈ Set.range (algebraMap O LL)) (n : ℕ) (u : ℤ_[l])
    (x : LL) (hx : (l ^ n) • (Submodule.Quotient.mk x : LL ⧸ T) = 0) :
    (Submodule.Quotient.mk (algebraMap ℚ_[l] LL (u : ℚ_[l]) * x) : LL ⧸ T) =
      (PadicInt.toZModPow n u).val • (Submodule.Quotient.mk x : LL ⧸ T) := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h : u - (((PadicInt.toZModPow n u).val : ℕ) : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 h
  obtain ⟨w', hw'⟩ := hZ w
  generalize (PadicInt.toZModPow n u).val = a at hw ⊢
  have hu : u = a + (l : ℤ_[l]) ^ n * w := by rw [← hw]; ring
  have h2 : algebraMap ℚ_[l] LL (u : ℚ_[l]) = (a : LL) + (l : LL) ^ n * algebraMap O LL w' := by
    rw [hw', hu]
    push_cast
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  have h3 : algebraMap ℚ_[l] LL (u : ℚ_[l]) * x = a • x + w' • (l ^ n • x) := by
    rw [h2, nsmul_eq_mul, nsmul_eq_mul, Algebra.smul_def]
    push_cast
    ring
  have h4 : T.mkQ (a • x) = a • T.mkQ x := map_nsmul T.mkQ a x
  have h5 : T.mkQ (w' • (l ^ n • x)) = 0 := by
    rw [LinearMap.map_smul, map_nsmul, Submodule.mkQ_apply, hx, smul_zero]
  rw [h3, ← Submodule.mkQ_apply, map_add (f := _), h4, h5, add_zero]
  rfl

end Int

end GlobalTheory.CompanionTheory.LocDual.TI
end
end
