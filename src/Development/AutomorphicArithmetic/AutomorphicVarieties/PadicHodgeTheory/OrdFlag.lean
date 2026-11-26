module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharDR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeRhamRationalTwistByCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeRhamRationalOfConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SharedDedup_Exists_trace

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsFrobeniusFixedPeriod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_trace {k U D : Type} [Field k] [Field U] [AddCommGroup D] [Module k D]
    (m : U →+* End k D) (φ : End k D) (n : ℕ) (hn : 0 < n) (t : ℕ → U)
    (ht : ∀ i j : Fin n, t i = t j → i = j) (htn : t n = t 0)
    (hφ : ∀ i j : ℕ, φ ^ i * m (t 0 ^ j) = m (t i ^ j) * φ ^ i) (x : D) (hx : x ≠ 0) (hp : (φ ^ n) x = x) :
    ∃ j : ℕ, (∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x ≠ 0 ∧
      φ ((∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x) = (∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x := _root_.DedupShared.dedup_exists_trace_4 (k := k) (U := U) (D := D) m φ n hn t ht htn hφ x hx hp

private theorem exists_orbit (l : ℕ) [hl : Fact l.Prime] (n : ℕ) (hn : 2 ≤ n) :
    ∃ c : ↥(MaximalUnramifiedExtension l), (frobUr l ^ n) c = c ∧
      ∀ i j : Fin n, (frobUr l ^ (i : ℕ)) c = (frobUr l ^ (j : ℕ)) c → i = j := by
  have h2 := hl.out.two_le
  have hlt : ∀ i, i < n → l ^ i < l ^ n - 1 := by
    intro i hi
    obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
    have h3 : l ^ i ≤ l ^ r := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : 1 < l ^ r := Nat.one_lt_pow (by omega) (by omega)
    have h5 : l ^ r * 2 ≤ l ^ r * l := Nat.mul_le_mul_left _ h2
    rw [pow_succ]; omega
  have h0 : 0 < l ^ n - 1 := lt_of_le_of_lt (Nat.zero_le _) (hlt 0 (by omega))
  have hd : ¬ l ∣ l ^ n - 1 := fun h => hl.out.one_lt.ne' (Nat.dvd_one.mp
    ((Nat.dvd_sub_iff_right (by omega) (dvd_pow_self l (by omega))).mp h))
  haveI : NeZero (l ^ n - 1) := ⟨h0.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ n - 1)
  have hmem : z ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨_, h0, hd, hz.pow_eq_one⟩
  have h1 : (⟨z, hmem⟩ : ↥(MaximalUnramifiedExtension l)) ^ (l ^ n - 1) = 1 := Subtype.ext hz.pow_eq_one
  refine ⟨⟨z, hmem⟩, ?_, fun i j hij => ?_⟩
  · rw [frobUr_pow_root _ _ _ h0 hd h1, show l ^ n = (l ^ n - 1) + 1 by omega, pow_succ, h1, one_mul]
  · rw [frobUr_pow_root _ _ _ h0 hd h1, frobUr_pow_root _ _ _ h0 hd h1] at hij
    have h6 : z ^ l ^ (i : ℕ) = z ^ l ^ (j : ℕ) := congrArg Subtype.val hij
    exact Fin.ext (Nat.pow_right_injective h2 (hz.pow_inj (hlt _ i.2) (hlt _ j.2) h6))

private theorem zpow_fix {k D : Type} [Field k] [AddCommGroup D] [Module k D] (u : (End k D)ˣ) (y : D)
    (hy : (u : End k D) y = y) (n : ℤ) : ((u ^ n : (End k D)ˣ) : End k D) y = y :=
  (GlobalTheory.PstLaws.vecStab (Units.coeHom (End k D)) y).zpow_mem hy n

private theorem pow_fix {k D : Type} [Field k] [AddCommGroup D] [Module k D] (u : (End k D)ˣ) (a : End k D) (y : D)
    (n : ℕ) (hc : Commute a ((u ^ (n : ℤ) : (End k D)ˣ) : End k D)) (ha : a y = y)
    (hy : (a * ((u ^ (n : ℤ) : (End k D)ˣ) : End k D)) y = y) : ((u : End k D) ^ n) y = y := by
  rwa [hc.eq, End.mul_apply, ha, zpow_natCast, Units.val_pow_eq_pow_val] at hy

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O]
  [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw)
  (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

private theorem exists_stab {K : FinExt l} (ρ : Representation LL ↥(GK K) V) (y : ↥(Dpst P ρ)) :
    ∃ K' : FinExt l, ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → g ∈ GlobalTheory.PstLaws.vecStab (actD P ρ) y := by
  obtain ⟨K', hK'⟩ := (mem_Dpst P ρ).mp y.2
  exact ⟨K', fun g hg => Subtype.ext (hK' g hg)⟩

private theorem deg_frob_inv_pow (s : ℕ) : deg ((frob h)⁻¹ ^ s) = -(s : ℤ) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 := deg_mul ((frob h)⁻¹ ^ (s + 1)) (frob h)
    rw [pow_succ, inv_mul_cancel_right, ih, deg_frob] at h1
    rw [pow_succ]; push_cast; omega

variable (ρ : Representation LL ↥(GK Bw.Kw) V)

private theorem fix_of_weil (z : ↥(Dpst P ρ)) (hz : ∀ σ, actD P ρ (weilToGK Bw h σ) z = z)
    (g : ↥(GK Bw.Kw)) : actD P ρ g z = z := by
  obtain ⟨K', hK'⟩ := exists_stab P ρ z
  haveI := K'.2
  let S := (GlobalTheory.PstLaws.vecStab (actD P ρ) z).comap Bw.e.toMonoidHom
  have hS : IsOpen (S : Set ↥(Dec (F := F) A)) := by
    refine Subgroup.isOpen_mono (H₁ := ((GK K').subgroupOf (GK Bw.Kw)).comap Bw.e.toMonoidHom)
      (fun τ hτ => hK' _ hτ) ?_
    exact (IntermediateField.fixingSubgroup_isOpen K'.1).preimage (continuous_subtype_val.comp Bw.e_cont)
  have hd := UpperTheory.weil_group_dense_in_galois_group F Ω w A h
  obtain ⟨τ, rfl⟩ := Bw.e.surjective g
  exact hd.induction_on (p := fun τ => τ ∈ S) τ (S.isClosed_of_isOpen hS) hz

variable [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]

include hj in
private theorem exists_period (x : ↥(Dpst P ρ)) (hx : ∀ σ, weilD Bw h P ρ σ x = x) :
    ∃ n : ℕ, 2 ≤ n ∧ (phiD P ρ ^ n) x = x := by
  have hf : resDeg l w ≠ 0 := by
    intro h0
    have hq1 := GlobalTheory.WeilDeligne.one_lt_normV w
    rw [normV_eq_pow (hj.mem_placesOver h), h0, pow_zero] at hq1
    exact lt_irrefl _ hq1
  obtain ⟨K', hK'⟩ := exists_stab P ρ x
  haveI := GlobalTheory.PstLaws.finite_quotient K' _ hK'
  haveI : (GlobalTheory.PstLaws.vecStab (actD P ρ) x).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨r, hr0, -, hr⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := GlobalTheory.PstLaws.vecStab (actD P ρ) x)) (weilToGK Bw h (frob h)⁻¹)
  have hr2 : weilToGK Bw h ((frob h)⁻¹ ^ (r * 2)) ∈ GlobalTheory.PstLaws.vecStab (actD P ρ) x := by
    rw [map_pow (weilToGK Bw h), pow_mul]
    exact (GlobalTheory.PstLaws.vecStab (actD P ρ) x).pow_mem hr 2
  have h2 := hx ((frob h)⁻¹ ^ (r * 2))
  have e : -alpha l ((frob h)⁻¹ ^ (r * 2)) = ((resDeg l w * (r * 2) : ℕ) : ℤ) := by
    rw [alpha, deg_frob_inv_pow]; push_cast; ring
  rw [weilD_apply, e] at h2
  refine ⟨_, ?_, pow_fix (phiU P ρ) _ x _ (commute_actD_phiU P ρ _ _) hr2 h2⟩
  have : 0 < resDeg l w * r := Nat.mul_pos (Nat.pos_of_ne_zero hf) hr0
  rw [← mul_assoc]; omega

include hj in
private theorem main (x : ↥(Dpst P ρ)) (hx0 : x ≠ 0) (hxI : ∀ s, weilD Bw h P ρ (ineIncl h s) x = x)
    (hW : ∀ x : ↥(Dpst P ρ), (∀ s, weilD Bw h P ρ (ineIncl h s) x = x) → ∀ σ, weilD Bw h P ρ σ x = x) :
    ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ phiD P ρ z = z ∧ ∀ g, actD P ρ g z = z := by
  obtain ⟨n, hn, hp⟩ := exists_period h Bw hj P ρ x (hW x hxI)
  obtain ⟨c, hc1, hc2⟩ := exists_orbit l n hn
  obtain ⟨j, hz0, hz1⟩ := exists_trace (mulD P ρ) (phiD P ρ) n (by omega) (fun i => (frobUr l ^ i) c) hc2
    (by simpa using hc1) (fun i j => by rw [phiD_pow_mulD, pow_zero, AlgHom.one_apply, map_pow]) x hx0 hp
  refine ⟨_, hz0, hz1, fix_of_weil h Bw P ρ _ fun σ => ?_⟩
  refine (congrArg (actD P ρ (weilToGK Bw h σ)) (zpow_fix (phiU P ρ) _ hz1 (-alpha l σ))).symm.trans
    (hW _ (fun s => ?_) σ)
  have hcm : Commute (weilD Bw h P ρ (ineIncl h s)) (∑ i ∈ Finset.range n, phiD P ρ ^ i *
      mulD P ρ ((frobUr l ^ 0) c ^ j)) := by
    refine Commute.sum_right _ _ _ fun i _ => Commute.mul_right (Commute.pow_right ?_ i)
      (weilD_mulD Bw h P ρ hj _ _)
    rw [weilD_ineIncl]
    exact (phiD_actD P ρ _).symm
  exact (LinearMap.congr_fun hcm.eq x).trans (congrArg _ (hxI s))

end

theorem UpperTheory.exists_frobenius_fixed_period :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (_hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)], (∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ s, weilD Bw h P ρ (ineIncl h s) x = x) → (∀ x : ↥(Dpst P ρ), (∀ s, weilD Bw h P ρ (ineIncl h s) x = x) → ∀ σ, weilD Bw h P ρ σ x = x) → ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ phiD P ρ z = z ∧ ∀ g, actD P ρ g z = z := by
  intro F Ω _ _ _ _ _ l hl A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ ⟨x, hx0, hxI⟩ hW
  exact main h Bw hj P ρ x hx0 hxI hW
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.InertiaEigenvectorExtendsOfDistinctCharacters
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.inertia_eigenvector_extends_of_distinct_characters :
    ∀ {Γ I W : Type} [Group Γ] [Group I] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ} (i : I →* Γ) (ρ : Γ →* Module.End ℂ W) (μ : Fin n → Γ →* ℂˣ), (∀ σ s, ∃ t, σ * i s = i t * σ) → (Set.range fun s => ρ (i s)).Finite → (∀ σ, (ρ σ).charpoly = ∏ j, (X - C (μ j σ : ℂ))) → (∀ j k, j ≠ k → ∃ s, μ j (i s) ≠ μ k (i s)) → (∀ N : Module.End ℂ W, IsNilpotent N → (∀ s, ρ (i s) * N = N * ρ (i s)) → N = 0) ∧ ∀ j, (∃ y : W, y ≠ 0 ∧ ∀ s, ρ (i s) y = (μ j (i s) : ℂ) • y) ∧ ∀ y : W, (∀ s, ρ (i s) y = (μ j (i s) : ℂ) • y) → ∀ σ, ρ σ y = (μ j σ : ℂ) • y := by
  intro Γ I W _ _ _ _ _ n i ρ μ hnorm hfin hchar hdist
  classical
  have htr : ∀ σ, LinearMap.trace ℂ W (ρ σ) = ∑ j, (μ j σ : ℂ) := by
    intro σ
    have hs : (ρ σ).charpoly.Splits := by
      rw [hchar]
      exact Splits.prod (fun j _ => Splits.X_sub_C _)
    have hr := Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map fun j => (μ j σ : ℂ))
    simp only [Multiset.map_map, Function.comp_def] at hr
    rw [Module.End.trace_eq_sum_roots_charpoly_of_splits hs, hchar, Finset.prod_eq_multiset_prod, hr,
      Finset.sum_eq_multiset_sum]
  have hK : ∀ u : I, ρ (i u) = 1 → ∀ k, μ k (i u) = 1 := by
    intro u hu k
    have hroot : (ρ (i u)).charpoly.IsRoot (μ k (i u) : ℂ) := by
      rw [hchar, Polynomial.IsRoot, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
    rw [← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hroot
    obtain ⟨v, hv⟩ := hroot.exists_hasEigenvector
    have h1 := hv.apply_eq_smul
    rw [hu, Module.End.one_apply] at h1
    have h2 : ((μ k (i u) : ℂ) - 1) • v = 0 := by
      rw [sub_smul, ← h1, one_smul, sub_self]
    have h3 := (smul_eq_zero.mp h2).resolve_right hv.2
    ext
    simpa [sub_eq_zero] using h3
  have hK' : ∀ s s' : I, ρ (i s) = ρ (i s') → ∀ k, μ k (i s) = μ k (i s') := by
    intro s s' h k
    have h1 : ρ (i (s'⁻¹ * s)) = 1 := by
      rw [map_mul, map_mul, h, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
    have h2 := hK _ h1 k
    rw [map_mul, map_mul, map_inv, map_inv] at h2
    exact (inv_mul_eq_one.mp h2).symm
  set U : I →* (Module.End ℂ W)ˣ := (ρ.comp i).toHomUnits with hU
  have hUval : ∀ s, ((U s : (Module.End ℂ W)ˣ) : Module.End ℂ W) = ρ (i s) := fun s => rfl
  have hKU : ∀ s s', U s = U s' → ∀ k, μ k (i s) = μ k (i s') :=
    fun s s' h k => hK' s s' (by rw [← hUval, ← hUval, h]) k
  have hfinU : (Set.range U).Finite := by
    refine (hfin.preimage (Function.Injective.injOn (fun a b h => Units.ext h))).subset ?_
    rintro x ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  haveI : Finite U.range := hfinU.to_subtype
  letI : Fintype U.range := Fintype.ofFinite _
  have hpre0 : ∀ h : U.range, ∃ s, U s = h := fun h => h.2
  choose pre hpre using hpre0
  have hpreval : ∀ h : U.range, (((h : (Module.End ℂ W)ˣ)) : Module.End ℂ W) = ρ (i (pre h)) := by
    intro h
    rw [← hUval, hpre]
  let ψ : Fin n → U.range →* ℂˣ := fun k =>
    { toFun := fun h => μ k (i (pre h))
      map_one' := by
        have : U (pre 1) = U 1 := by rw [hpre, map_one]; rfl
        show μ k (i (pre 1)) = 1
        rw [hKU _ _ this k, map_one, map_one]
      map_mul' := fun a b => by
        have : U (pre (a * b)) = U (pre a * pre b) := by rw [map_mul, hpre, hpre, hpre]; rfl
        show μ k (i (pre (a * b))) = μ k (i (pre a)) * μ k (i (pre b))
        rw [hKU _ _ this k, map_mul, map_mul] }
  have hψ : ∀ k (h : U.range), ψ k h = μ k (i (pre h)) := fun k h => rfl
  have hψU : ∀ k s, ψ k ⟨U s, s, rfl⟩ = μ k (i s) := fun k s => hKU _ _ (hpre _) k
  have horth : ∀ k m, ∑ h : U.range, (((ψ m * (ψ k)⁻¹) h : ℂˣ) : ℂ) =
      if m = k then (Fintype.card U.range : ℂ) else 0 := by
    intro k m
    split_ifs with hmk
    · subst hmk
      simp
    · let φ : U.range →* ℂ := (Units.coeHom ℂ).comp (ψ m * (ψ k)⁻¹)
      have hφ : φ ≠ 1 := by
        intro h1
        obtain ⟨s, hs⟩ := hdist m k hmk
        apply hs
        have h2 := DFunLike.congr_fun h1 ⟨U s, s, rfl⟩
        have h3 : ((ψ m * (ψ k)⁻¹) ⟨U s, s, rfl⟩ : ℂˣ) = 1 := Units.ext h2
        rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one, hψU, hψU] at h3
        exact h3
      exact sum_hom_units_eq_zero φ hφ
  let P : Fin n → Module.End ℂ W := fun k =>
    ∑ h : U.range, ((((ψ k)⁻¹ h : ℂˣ)) : ℂ) • (((h : (Module.End ℂ W)ˣ)) : Module.End ℂ W)
  let E : Fin n → W → Prop := fun k y => ∀ s, ρ (i s) y = (μ k (i s) : ℂ) • y
  have hcard0 : (Fintype.card U.range : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hact : ∀ k y, E k y → ∀ h : U.range,
      ((h : (Module.End ℂ W)ˣ) : Module.End ℂ W) y = (ψ k h : ℂ) • y := by
    intro k y hy h
    rw [hpreval, hy, hψ]
  have hPE : ∀ k y, E k y → ∀ m, P m y = if m = k then (Fintype.card U.range : ℂ) • y else 0 := by
    intro k y hy m
    have h1 : P m y = (∑ h : U.range, (((ψ k * (ψ m)⁻¹) h : ℂˣ) : ℂ)) • y := by
      simp only [P, LinearMap.sum_apply, LinearMap.smul_apply, hact k y hy,
        smul_smul, Finset.sum_smul]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [MonoidHom.mul_apply, Units.val_mul, mul_comm]
    rw [h1, horth m k]
    by_cases hmk : m = k
    · subst hmk
      simp
    · simp [hmk, Ne.symm hmk]
  have hPT : ∀ k s, ρ (i s) * P k = (μ k (i s) : ℂ) • P k := by
    intro k s
    let g : U.range := ⟨U s, s, rfl⟩
    let F : U.range → Module.End ℂ W := fun h' =>
      (((ψ k)⁻¹ h' : ℂˣ) : ℂ) • ((h' : (Module.End ℂ W)ˣ) : Module.End ℂ W)
    have key : ∀ h : U.range, (((ψ k)⁻¹ h : ℂˣ) : ℂ) •
        (ρ (i s) * ((h : (Module.End ℂ W)ˣ) : Module.End ℂ W)) = (μ k (i s) : ℂ) • F (g * h) := by
      intro h
      have e1 : (((ψ k)⁻¹ (g * h) : ℂˣ) : ℂ) =
          (((ψ k g)⁻¹ : ℂˣ) : ℂ) * (((ψ k)⁻¹ h : ℂˣ) : ℂ) := by
        rw [MonoidHom.inv_apply, MonoidHom.inv_apply, map_mul, _root_.mul_inv_rev, Units.val_mul, mul_comm]
      have e2 : (((g * h : U.range) : (Module.End ℂ W)ˣ) : Module.End ℂ W) =
          ρ (i s) * ((h : (Module.End ℂ W)ˣ) : Module.End ℂ W) := rfl
      have e3 : (μ k (i s) : ℂ) * (((ψ k g)⁻¹ : ℂˣ) : ℂ) = 1 := by
        rw [show ψ k g = μ k (i s) from hψU k s, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      show _ = (μ k (i s) : ℂ) • ((((ψ k)⁻¹ (g * h) : ℂˣ) : ℂ) •
        (((g * h : U.range) : (Module.End ℂ W)ˣ) : Module.End ℂ W))
      rw [e1, e2, smul_smul, ← mul_assoc, e3, one_mul]
    calc ρ (i s) * P k = ∑ h : U.range, (((ψ k)⁻¹ h : ℂˣ) : ℂ) •
          (ρ (i s) * ((h : (Module.End ℂ W)ˣ) : Module.End ℂ W)) := by
          simp only [P, Finset.mul_sum, mul_smul_comm]
      _ = ∑ h : U.range, (μ k (i s) : ℂ) • F (g * h) := Finset.sum_congr rfl fun h _ => key h
      _ = (μ k (i s) : ℂ) • ∑ h : U.range, F h := by
          rw [← Finset.smul_sum]
          congr 1
          exact Equiv.sum_comp (Equiv.mulLeft g) F
  have htrP : ∀ k, LinearMap.trace ℂ W (P k) = (Fintype.card U.range : ℂ) := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, map_sum, map_smul, hpreval, htr, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h1 : ∀ m, ∑ h : U.range, (((ψ k)⁻¹ h : ℂˣ) : ℂ) * (μ m (i (pre h)) : ℂ) =
        if m = k then (Fintype.card U.range : ℂ) else 0 := by
      intro m
      rw [← horth k m]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [MonoidHom.mul_apply, Units.val_mul, mul_comm, ← hψ]
    simp only [h1, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hPne : ∀ k, ∃ w, P k w ≠ 0 := by
    intro k
    by_contra hcon
    push_neg at hcon
    have h1 : P k = 0 := LinearMap.ext hcon
    have h2 := htrP k
    rw [h1, map_zero] at h2
    exact hcard0 h2.symm
  choose w hw using hPne
  have hPzE : ∀ k z, E k (P k z) := by
    intro k z s
    rw [← Module.End.mul_apply, hPT k s]
    rfl
  let yv : Fin n → W := fun k => P k (w k)
  have hyvE : ∀ k, E k (yv k) := fun k => hPzE k (w k)
  have hPE' : ∀ j k, P j (yv k) = if j = k then (Fintype.card U.range : ℂ) • yv k else 0 :=
    fun j k => hPE k (yv k) (hyvE k) j
  have hli : LinearIndependent ℂ yv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 := congrArg (P j) hg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h1
    simp only [map_smul, hPE', smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
    rw [smul_smul] at h1
    have h2 := (smul_eq_zero.mp h1).resolve_right (hw j)
    exact (mul_eq_zero.mp h2).resolve_right hcard0
  have hdim : Module.finrank ℂ W = n := by
    rw [← LinearMap.charpoly_natDegree (ρ 1), hchar 1]
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, Fintype.card_fin]
  let b := basisOfLinearIndependentOfCardEqFinrank' yv hli (by rw [Fintype.card_fin, hdim])
  have hb : ∀ k, b k = yv k := fun k => by simp [b]
  have hspan : ∀ k y, E k y → y = b.repr y k • yv k := by
    intro k y hy
    have hsum := b.sum_repr y
    have hzero : ∀ m, m ≠ k → b.repr y m = 0 := by
      intro m hm
      have h1 := congrArg (P m) hsum
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h1
      simp only [map_smul, hb, hPE', smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        if_true] at h1
      rw [hPE k y hy m, if_neg hm, smul_smul] at h1
      have h2 := (smul_eq_zero.mp h1).resolve_right (hw m)
      exact (mul_eq_zero.mp h2).resolve_right hcard0
    conv_lhs => rw [← hsum]
    rw [Finset.sum_eq_single k (fun m _ hm => by rw [hzero m hm, zero_smul]) (by simp), hb]
  refine ⟨?_, ?_⟩
  · intro N hN hcomm
    apply b.ext
    intro k
    rw [hb, LinearMap.zero_apply]
    have hNE : E k (N (yv k)) := by
      intro s
      rw [← Module.End.mul_apply, hcomm s, Module.End.mul_apply, hyvE k s, map_smul]
    set a := b.repr (N (yv k)) k with ha_def
    have ha : N (yv k) = a • yv k := hspan k _ hNE
    obtain ⟨p, hp⟩ := hN
    have hpow : ∀ q : ℕ, (N ^ q) (yv k) = a ^ q • yv k := by
      intro q
      induction q with
      | zero => simp
      | succ q ih =>
        rw [pow_succ N q, Module.End.mul_apply, ha, map_smul, ih, smul_smul, pow_succ' a q, mul_comm]
    have h0 := hpow p
    rw [hp, LinearMap.zero_apply] at h0
    have ha0 : a ^ p = 0 := (smul_eq_zero.mp h0.symm).resolve_right (hw k)
    have ha00 : a = 0 := by
      by_contra hne
      exact pow_ne_zero p hne ha0
    rw [ha, ha00, zero_smul]
  · intro j
    refine ⟨⟨yv j, hw j, hyvE j⟩, ?_⟩
    intro y hy σ
    have hpres : ∀ z, E j z → E j (ρ σ z) := by
      intro z hz s
      obtain ⟨t, ht⟩ := hnorm σ⁻¹ s
      have e1 : i s * σ = σ * i t := by
        calc i s * σ = σ * (σ⁻¹ * i s) * σ := by group
          _ = σ * (i t * σ⁻¹) * σ := by rw [ht]
          _ = σ * i t := by group
      have e2 : μ j (i t) = μ j (i s) := by
        have e3 : i s = σ * i t * σ⁻¹ := by rw [← e1]; group
        rw [e3, map_mul, map_mul, map_inv, mul_comm (μ j σ), mul_assoc, mul_inv_cancel, mul_one]
      rw [← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply, hz t, map_smul, e2]
    set c := b.repr (ρ σ (yv j)) j with hc
    have hcy : ρ σ (yv j) = c • yv j := hspan j _ (hpres _ (hyvE j))
    have hσP : ρ σ * P j = c • P j := by
      refine LinearMap.ext fun z => ?_
      have hz := hspan j _ (hPzE j z)
      rw [Module.End.mul_apply, LinearMap.smul_apply, hz, map_smul, hcy, smul_comm]
    have htrσ : ∀ h : U.range, LinearMap.trace ℂ W (ρ σ * ((h : (Module.End ℂ W)ˣ) : Module.End ℂ W)) =
        ∑ m, (μ m σ : ℂ) * (μ m (i (pre h)) : ℂ) := by
      intro h
      rw [hpreval, ← map_mul, htr]
      simp [Units.val_mul]
    have htr1 : LinearMap.trace ℂ W (ρ σ * P j) = c * (Fintype.card U.range : ℂ) := by
      rw [hσP, map_smul, htrP, smul_eq_mul]
    have htr2 : LinearMap.trace ℂ W (ρ σ * P j) = (μ j σ : ℂ) * (Fintype.card U.range : ℂ) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [P, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, htrσ, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      have h1 : ∀ m, ∑ h : U.range, (((ψ j)⁻¹ h : ℂˣ) : ℂ) * ((μ m σ : ℂ) * (μ m (i (pre h)) : ℂ)) =
          (μ m σ : ℂ) * (if m = j then (Fintype.card U.range : ℂ) else 0) := by
        intro m
        rw [← horth j m, Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [MonoidHom.mul_apply, Units.val_mul, ← hψ]
        ring
      simp only [h1, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hceq : c = μ j σ := mul_right_cancel₀ hcard0 (htr1.symm.trans htr2)
    rw [hspan j y hy, map_smul, hcy, hceq, smul_comm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsInvariantVectorOfFiniteImageAveraging
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.fixed_vector_descends_finite_image {Γ L D W : Type} [Group Γ] [Field L] [AddCommGroup D] [Module L D]
    [AddCommGroup W] [Module ℂ W] (a : Γ →* Module.End L D) (b : Γ →* Module.End ℂ W) (mk : D →+ W)
    (hs : Submodule.span ℂ (Set.range mk) = ⊤) (hc : ∀ g x, b g (mk x) = mk (a g x))
    [Finite (Γ ⧸ a.ker)] (y : W) (hy : y ≠ 0) (hi : ∀ g, b g y = y) :
    ∃ x : D, x ≠ 0 ∧ ∀ g, a g x = x := by
  classical
  by_contra hn
  push Not at hn
  let := Fintype.ofFinite (Γ ⧸ a.ker)
  let a' : Γ ⧸ a.ker →* Module.End L D := QuotientGroup.lift a.ker a le_rfl
  have ha : ∀ q : Γ ⧸ a.ker, a q.out = a' q := fun q => by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have h0 : ∀ x : D, ∑ q : Γ ⧸ a.ker, a' q x = 0 := fun x => by
    by_contra hx
    obtain ⟨g, hg⟩ := hn _ hx
    refine hg ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (g : Γ ⧸ a.ker)) _ _ fun q => ?_
    rw [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply]
    rfl
  have h1 : (∑ q : Γ ⧸ a.ker, b q.out) = 0 := by
    refine LinearMap.ext_on_range hs fun x => ?_
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    simp only [hc, ha]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, h0, map_zero]
  have h2 := LinearMap.congr_fun h1 y
  rw [LinearMap.sum_apply, LinearMap.zero_apply] at h2
  simp only [hi, Finset.sum_const, Finset.card_univ] at h2
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h2
  exact hy ((smul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

theorem UpperTheory.exists_invariant_vector_of_finite_image_averaging :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)], (∃ y : WDSpace P ι ρ, y ≠ 0 ∧ ∀ s, wdRho P ι Bw h hj ρ (ineIncl h s) y = y) → (∀ y : WDSpace P ι ρ, (∀ s, wdRho P ι Bw h hj ρ (ineIncl h s) y = y) → ∀ σ, wdRho P ι Bw h hj ρ σ y = y) → (∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ s, weilD Bw h P ρ (ineIncl h s) x = x) ∧ ∀ x : ↥(Dpst P ρ), (∀ s, weilD Bw h P ρ (ineIncl h s) x = x) → ∀ σ, weilD Bw h P ρ σ x = x := by
  intro F Ω _ _ _ _ _ l _ ι A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ h1 h2
  refine ⟨?_, fun x hx σ => ?_⟩
  · obtain ⟨y, hy, hi⟩ := h1
    have := compactSpace_Ine (E := F) A
    have : Finite (Ine (F := F) A ⧸ (MonoidHom.comp (weilD Bw h P ρ) (ineIncl h)).ker) :=
      Subgroup.quotient_finite_of_isOpen _ (isSmooth_weilD Bw h P ρ hj)
    exact UpperTheory.fixed_vector_descends_finite_image (MonoidHom.comp (weilD Bw h P ρ) (ineIncl h))
      (MonoidHom.comp (wdRho P ι Bw h hj ρ) (ineIncl h))
      (AddMonoidHom.mk' (wdMk P ι ρ) (wdMk_add P ι ρ)) (span_wdMk P ι ρ)
      (fun g x => wdRho_mk P ι Bw h hj ρ _ x) y hy hi
  · have hc : ∀ (n : ℕ) τ, Commute (phiD P ρ ^ n) (weilD Bw h P ρ τ) := fun n τ => by
      refine Commute.pow_left ?_ n
      rw [weilD_apply]
      refine Commute.mul_right (phiD_actD P ρ _) ?_
      exact Commute.units_zpow_right (u := phiU P ρ) (Commute.refl _) _
    have hc' : ∀ (n : ℕ) τ, weilD Bw h P ρ τ ((phiD P ρ ^ n) x) = (phiD P ρ ^ n) (weilD Bw h P ρ τ x) :=
      fun n τ => (LinearMap.congr_fun (hc n τ).eq x).symm
    refine sub_eq_zero.mp
      (GlobalTheory.PstFaithful.eq_zero_of_wdMk_phiD_pow l P ι _ L V ρ _ fun n => ?_)
    have h3 := h2 (wdMk P ι ρ ((phiD P ρ ^ n) x)) (fun s => by rw [wdRho_mk, hc', hx]) σ
    rw [wdRho_mk, hc'] at h3
    have h4 := wdMk_add P ι ρ ((phiD P ρ ^ n) (weilD Bw h P ρ σ x - x)) ((phiD P ρ ^ n) x)
    rw [← map_add (f := _), sub_add_cancel, h3] at h4
    exact left_eq_add.mp (h4.trans (add_comm _ _))
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices

open GlobalTheory.Pst Polynomial Module Matrix Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)

private theorem ine_normal (σ : ↥(Weil h)) (s : ↥(Ine (F := F) A)) : ∃ t, σ * ineIncl h s = ineIncl h t * σ := by
  have : deg (σ * ineIncl h s * σ⁻¹) = 0 := by simp
  refine ⟨⟨_, deg_eq_zero_iff.1 this⟩, ?_⟩
  have e : ineIncl h ⟨_, deg_eq_zero_iff.1 this⟩ = σ * ineIncl h s * σ⁻¹ := rfl
  rw [e, inv_mul_cancel_right]

private theorem core0 {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type}
    [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V]
    (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) (hV : IsPst P ρ) {n : ℕ} (μ : Fin n → ↥(Weil h) →* ℂˣ)
    (hμ : ∀ j k, j ≠ k → ∃ s, μ j (ineIncl h s) ≠ μ k (ineIncl h s))
    (hP : ∀ σ, (wdPst P ι Bw h hj ρ).charPol σ = ∏ j, (X - C (μ j σ : ℂ))) :
    wdN P ι ρ = 0 ∧ ∀ j, μ j = 1 → ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ phiD P ρ z = z ∧ ∀ g, actD P ρ g z = z := by
  haveI := hV.finite
  have hc : ∀ σ, (wdRho P ι Bw h hj ρ σ).charpoly = ∏ j, (X - C (μ j σ : ℂ)) :=
    fun σ => (DpstMap.charPol_wdPst P ι Bw h hj ρ hV σ).symm.trans (hP σ)
  obtain ⟨hN, hL⟩ := UpperTheory.inertia_eigenvector_extends_of_distinct_characters (ineIncl h) (wdRho P ι Bw h hj ρ) μ
    (ine_normal h) (isSmooth_wdRho P ι Bw h hj ρ).finite_range hc hμ
  refine ⟨hN _ (isNilpotent_wdN P ι ρ) fun s => ?_, fun j hj1 => ?_⟩
  · have := wdRho_wdN P ι Bw h hj ρ (ineIncl h s)
    rw [deg_ineIncl, zpow_zero, one_smul] at this
    exact this
  obtain ⟨h1, h2⟩ := hL j
  simp only [hj1, MonoidHom.one_apply, Units.val_one, one_smul] at h1 h2
  obtain ⟨h3, h4⟩ := UpperTheory.exists_invariant_vector_of_finite_image_averaging ι h Bw hj P ρ h1 h2
  exact UpperTheory.exists_frobenius_fixed_period h Bw hj P ρ h3 h4

private theorem core (hB : DeRhamPotSemistable) {n : ℕ} (r : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l))
    (hr : Continuous r) (HT : (F →+* Qbar l) → Multiset ℤ) (μ : Fin n → ↥(Weil h) →* ℂˣ)
    (hμ : ∀ j k, j ≠ k → ∃ s, μ j (ineIncl h s) ≠ μ k (ineIncl h s))
    (hD : DRat ι h r HT fun s => ∏ j, (X - C (μ j s : ℂ)))
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw) :
    IsPotCrysAt (UpperTheory.V.Loc.PP l) Bw r ∧ ∀ j, μ j = 1 → (∀ τ, ∀ c ∈ HT τ, 0 ≤ c) →
      ∃ v : Fin n → Qbar l, v ≠ 0 ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) (Qbar l)) *ᵥ v = v := by
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨hd, hJ, hP⟩ := hD O Bw hj
  have hp := hB.isPstAt T Bw r (Units.continuous_val.comp hr) hd
  obtain ⟨L, r', hm, hV, e⟩ := wdAt_of_isPstAt ι Bw h hj hp
  obtain ⟨hN0, hz⟩ := core0 ι h Bw hj (UpperTheory.V.Loc.PP l) (Bw.repE L r') hV μ hμ fun σ =>
    (congrArg (fun x => WD.charPol x σ) e).symm.trans (hP σ)
  refine ⟨(GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw h hj _ ι r hp).1 ?_, fun j hj1 hHT => ?_⟩
  · rw [e]
    exact (mono0_wdPst ι Bw h hj hV).2 hN0
  obtain ⟨z, z0, z1, z2⟩ := hz j hj1
  have hd' := (hm.isdRAt_iff _).1 hd
  have hM := (GlobalTheory.PstLaws.wdN_eq_zero_iff (UpperTheory.V.Loc.PP l) (Bw.repE L r') ι).1 hN0
  have hmult : ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (c : ℤ), c < 0 → Bw.multE (UpperTheory.V.Loc.PP l) L r' τ' c = 0 := by
    intro τ' c hc0
    let τ : F →+* Qbar l := ((algebraMap ↥L.1 (Om l)).comp τ'.toRingHom).comp
      ((Bw.j.comp (algebraMap F Ω)).codRestrict Bw.Kw.1 Bw.j_E)
    have hτ : IsInduced Bw τ τ' := fun _ => rfl
    have := IsJumpsAt.count_eq _ hm hτ (hJ τ L τ' hτ) c
    rw [Multiset.count_eq_zero.2 fun hc' => absurd (hHT τ c hc') (not_le.2 hc0)] at this
    exact this.symm
  obtain ⟨v, v0, hv⟩ := UpperTheory.exists_invariant_of_dpst_phi_fixed_of_nonneg_weights (fun τ x => hm.1 (Bw.LL_split τ x)) (Bw.repE L r')
    (finiteDimensional_DdR _ _ hd') hmult z z0 (LinearMap.congr_fun hM z) z1 z2
  refine ⟨fun i => (v i : Om l), fun h0 => v0 (funext fun i => Subtype.ext (congrFun h0 i)), fun g => ?_⟩
  have h5 : (r' g : Matrix (Fin n) (Fin n) ↥L.1) *ᵥ v = v := by
    have := hv (Bw.e g)
    rw [← Bw.e.symm_apply_apply g]
    exact this
  funext i
  have h6 := congrArg (algebraMap ↥L.1 (Om l)) (congrFun h5 i)
  rw [RingHom.map_mulVec] at h6
  rw [← hm.2]
  exact h6

omit [IsAlgClosure F Ω] in
private theorem ordChar_inv {a : ↥(Weil h) →* (w.adicCompletion F)ˣ} {ω : (w.adicCompletion F)ˣ →* ℂˣ}
    {hh : (F →+* Qbar l) → ℤ} {ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ} (H : OrdChar ι a ω hh ψ) :
    OrdChar ι a ω⁻¹ (-hh) ψ⁻¹ := by
  refine ⟨?_, H.cont.inv, ?_⟩
  · have hsmooth := H.smooth
    unfold GlobalTheory.SmGL.IsSmoothChar at hsmooth ⊢
    convert hsmooth using 1
    ext x
    simp
  · intro s g hg hs
    have := H.val s g hg hs
    simp only [MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val] at this ⊢
    rw [this, mul_inv, map_inv₀]
    congr 1
    unfold algPow
    rw [← finprod_inv_distrib]
    simp

end SlopeTestRemainingChoices

section Main

open GlobalTheory.Pst Polynomial Module Matrix Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)

private noncomputable def twR {H k : Type} [Group H] [Field k] {n : ℕ} (μ : H →* kˣ) (r : H →* GL (Fin n) k) : H →* GL (Fin n) k where
  toFun g := ⟨(μ g : k) • (r g : Matrix (Fin n) (Fin n) k), (μ g⁻¹ : k) • (r g⁻¹ : Matrix (Fin n) (Fin n) k),
    by rw [smul_mul_smul_comm, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]; simp,
    by rw [smul_mul_smul_comm, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' g g' := Units.ext (by simp [smul_smul, mul_comm])

private theorem twR_cont {H k : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Field k]
    [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} {μ : H →* kˣ} {r : H →* GL (Fin n) k}
    (hμ : Continuous μ) (hr : Continuous r) : Continuous (twR μ r) :=
  Units.continuous_iff.2 ⟨(Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr),
    ((Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr)).comp continuous_inv⟩

private theorem flag (hL : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal)
    {a : ↥(Weil h) →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) (n : ℕ) :
    ∀ (r : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (hh : Fin n → (F →+* Qbar l) → ℤ), (∀ τ, StrictMono fun j => hh j τ) →
    ∀ (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ) (ψ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      (∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) →
      (∀ i j, i ≠ j → ∃ s, ω i (a (ineIncl h s)) ≠ ω j (a (ineIncl h s))) →
      DRat ι h r (fun τ => Finset.univ.val.map fun j => hh j τ) (fun s => ∏ j, (X - C (ω j (a s) : ℂ))) →
      HasFlag r ψ := by
  have hB := hL.aut.berger
  induction n with
  | zero => exact fun r _ _ _ _ _ _ _ _ => ⟨1, fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    intro r hr hh hmono ω ψ hO hne hD
    have hO' := ordChar_inv ι h (hO 0)
    have hc := twR_cont hO'.cont hr
    have h1 := UpperTheory.deRham_rational_twist_by_character hB ι h r (twR (ψ 0)⁻¹ r) (ψ 0)⁻¹ hr hc hO'.cont (fun _ => rfl) _ _ _ _ hD
      (UpperTheory.V.Loc.charDR hL h hw ι a ha _ _ _ hO').1
    obtain ⟨LL, Bw, hj⟩ := GlobalTheory.Pst.Test.exists_induces (l := l) (E := F) (Ω := Ω) hw h
    obtain ⟨v, v0, hv⟩ := (core ι h hB _ hc _ (fun j => (ω j * (ω 0)⁻¹).comp a)
      (fun j k hjk => (hne j k hjk).imp fun s hs e => hs (mul_right_cancel e))
      (by simpa only [MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul] using h1) Bw hj).2 0
      (by rw [mul_inv_cancel]; rfl) (fun τ c hc => by
        simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, Pi.neg_apply] at hc
        obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := hc
        have := (hmono τ).monotone (Fin.zero_le j)
        omega)
    have hv' : ∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) *ᵥ v = (ψ 0 g : Qbar l) • v := fun g => by
      have := hv g
      change ((((ψ 0 g)⁻¹ : (Qbar l)ˣ) : Qbar l) • (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l))) *ᵥ v = v at this
      rw [Matrix.smul_mulVec] at this
      rw [← congrArg (fun x => (ψ 0 g : Qbar l) • x) this, smul_smul, Units.mul_inv, one_smul]
    obtain ⟨p, r₁, r', e₁, c₁, c', b1, b2, b3, hfl⟩ := UpperTheory.exists_common_eigenline r ψ v hr v0 hv'
    have h2 := UpperTheory.deRhamRational_of_conj hB ι h r r₁ p hr e₁ _ _ hD
    refine hfl (ih r' c' (fun j => hh j.succ) (fun τ => (hmono τ).comp Fin.strictMono_succ) (fun j => ω j.succ) _
      (fun j => hO j.succ) (fun i j hij => hne _ _ fun e => hij (Fin.succ_injective _ e)) ?_)
    refine UpperTheory.deRham_rational_of_extension_by_character hB ι h r₁ r' (ψ 0) c₁ b1 b2 b3 (hh 0) _ _ _ ?_
      (UpperTheory.V.Loc.charDR hL h hw ι a ha _ _ _ (hO 0)).1
    convert h2 using 2
    · rw [Fin.univ_val_map, Fin.univ_val_map, List.ofFn_succ, Multiset.cons_coe]
    · rw [Fin.prod_univ_succ]

end Main

theorem UpperTheory.V.Loc.ordFlag :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → OrdFlag := by
  intro hL F Ω _ _ _ _ _ l _ _ ι n w hw A h a ha r hr hh hmono ω ψ hO hne hD
  have hne' : ∀ i j, i ≠ j → ∃ s, ω i (a (ineIncl h s)) ≠ ω j (a (ineIncl h s)) := fun i j hij => by
    obtain ⟨⟨y, hy⟩, hy'⟩ := hne i j hij
    obtain ⟨σ, rfl⟩ := ha.surj y
    have h0 := ha.ord_eq σ
    rw [GlobalTheory.SmGL.ord_eq_zero hy, eq_comm, neg_eq_zero, deg_eq_zero_iff] at h0
    exact ⟨⟨σ, h0⟩, hy'⟩
  exact ⟨flag ι h hL hw ha n r hr hh hmono ω ψ hO hne' hD, fun O _ _ _ Bw hj =>
    (core ι h hL.aut.berger r hr _ (fun j => (ω j).comp a) hne' hD Bw hj).1⟩
