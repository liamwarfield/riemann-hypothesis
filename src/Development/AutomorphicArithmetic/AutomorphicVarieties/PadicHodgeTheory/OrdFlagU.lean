module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharDR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeRhamRationalTwistByCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeRhamRationalOfConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SharedDedup_Exists_trace

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.EqZeroOfTwistedCommuteOfDistinctCharacters
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.linearIndependent_distinct_characters {Γ W ι : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] [Fintype ι]
    (ρ : Γ →* Module.End ℂ W) (χ : ι → Γ →* ℂˣ) (y : ι → W) (hy : ∀ i, y i ≠ 0)
    (he : ∀ i σ, ρ σ (y i) = (χ i σ : ℂ) • y i) (hχ : Function.Injective χ) :
    LinearIndependent ℂ y := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hinj : Function.Injective (fun i => (Units.coeHom ℂ).comp (χ i)) := by
    intro a b hab
    apply hχ
    ext σ
    exact DFunLike.congr_fun hab σ
  have hli := (linearIndependent_monoidHom Γ ℂ).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  have key : ∀ φ : Module.Dual ℂ W, c i * φ (y i) = 0 := by
    intro φ
    refine hli (fun j => c j * φ (y j)) ?_ i
    funext σ
    have h1 : φ (ρ σ (∑ j, c j • y j)) = 0 := by rw [hc, map_zero, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum] at h1
    rw [Finset.sum_apply, Pi.zero_apply, ← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, he, map_smul, map_smul]
    simp only [Pi.smul_apply, Function.comp_apply, MonoidHom.comp_apply, Units.coeHom_apply, smul_eq_mul]
    ring
  by_contra hci
  apply hy i
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  exact (mul_eq_zero.mp (key φ)).resolve_left hci

theorem UpperTheory.eq_zero_of_twisted_commute_of_distinct_characters :
    ∀ {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ} (ρ : Γ →* Module.End ℂ W) (μ : Fin n → Γ →* ℂˣ) (ν : Γ →* ℂˣ) (N : Module.End ℂ W), Module.finrank ℂ W = n → (∀ j, ∃ y : W, y ≠ 0 ∧ ∀ σ, ρ σ y = (μ j σ : ℂ) • y) → Function.Injective μ → (∀ j k, μ j ≠ μ k * ν) → (∀ σ, ρ σ * N = (ν σ : ℂ) • (N * ρ σ)) → N = 0 := by
  intro Γ W _ _ _ _ n ρ μ ν N hn hy hμ hlink hN
  choose y hy0 hye using hy
  have hli : LinearIndependent ℂ y := UpperTheory.linearIndependent_distinct_characters ρ μ y hy0 hye hμ
  have hNy : ∀ k, N (y k) = 0 := by
    intro k
    by_contra hk
    have h2 : LinearIndependent ℂ (fun o : Option (Fin n) => o.elim (N (y k)) y) := by
      refine UpperTheory.linearIndependent_distinct_characters ρ (fun o : Option (Fin n) => o.elim (μ k * ν) μ) _ ?_ ?_ ?_
      · rintro (_ | j)
        · exact hk
        · exact hy0 j
      · rintro (_ | j) σ
        · have h3 := LinearMap.congr_fun (hN σ) (y k)
          simp only [Module.End.mul_apply, LinearMap.smul_apply, hye, map_smul, smul_smul] at h3
          simp only [Option.elim_none, MonoidHom.mul_apply, Units.val_mul]
          rw [h3, mul_comm]
        · exact hye j σ
      · rintro (_ | a) (_ | b) hab
        · rfl
        · exact absurd hab.symm (hlink b k)
        · exact absurd hab (hlink a k)
        · exact congrArg some (hμ hab)
    have h4 := h2.fintype_card_le_finrank
    rw [Fintype.card_option, Fintype.card_fin, hn] at h4
    omega
  have hspan : Submodule.span ℂ (Set.range y) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hn])
  refine LinearMap.ext_on_range hspan fun k => ?_
  rw [hNy k, LinearMap.zero_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsWeilInvariantInDpstOfWeilDeligneInvariant
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.fixed_vector_descends_weil_group {Γ I K D W : Type} [Group Γ] [Group I] [Field K] [CharZero K]
    [AddCommGroup D] [Module K D] [FiniteDimensional K D]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (j : I →* Γ) (φ : Γ) (hn : ∀ s, ∃ t, j s * φ = φ * j t) (hg : ∀ σ, ∃ (n : ℤ) (t : I), σ = φ ^ n * j t)
    (a : Γ →* Module.End K D) (b : Γ →* Module.End ℂ W) (mk : D →+ W)
    (hs : Submodule.span ℂ (Set.range mk) = ⊤) (hc : ∀ g x, b g (mk x) = mk (a g x))
    [Finite (I ⧸ (a.comp j).ker)] (y : W) (hy : y ≠ 0) (hi : ∀ g, b g y = y) :
    ∃ x : D, x ≠ 0 ∧ ∀ g, a g x = x := by
  classical
  by_contra hno
  let := Fintype.ofFinite (I ⧸ (a.comp j).ker)
  let a' : I ⧸ (a.comp j).ker →* Module.End K D := QuotientGroup.lift _ (a.comp j) le_rfl
  have ha : ∀ q : I ⧸ (a.comp j).ker, a (j q.out) = a' q := fun q => by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  let n : ℕ := Fintype.card (I ⧸ (a.comp j).ker)
  have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let E : Module.End K D := ∑ q : I ⧸ (a.comp j).ker, a (j q.out)
  let E' : Module.End ℂ W := ∑ q : I ⧸ (a.comp j).ker, b (j q.out)
  have hE : ∀ x s, a (j s) (E x) = E x := fun x s => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [E, LinearMap.sum_apply, map_sum, ha]
    refine Fintype.sum_equiv (Equiv.mulLeft (s : I ⧸ (a.comp j).ker)) _ _ fun q => ?_
    rw [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply]
    rfl
  have hE1 : ∀ z, (∀ s, a (j s) z = z) → E z = n • z := fun z hz => by
    simp only [E, LinearMap.sum_apply, hz, Finset.sum_const, Finset.card_univ, n]
  have hE2 : E' y = n • y := by
    simp only [E', LinearMap.sum_apply, hi, Finset.sum_const, Finset.card_univ, n]
  have hEE : ∀ x, E' (mk x) = mk (E x) := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [E, E', LinearMap.sum_apply, hc, map_sum]
  have hcan : ∀ z : D, n • z = 0 → z = 0 := fun z hz => by
    rw [← Nat.cast_smul_eq_nsmul K] at hz
    exact (smul_eq_zero.mp hz).resolve_left hn0
  let S : Module.End K D := a φ * E - E + n • 1 - E
  let S' : Module.End ℂ W := b φ * E' - E' + n • 1 - E'
  have hS : ∀ x, S x = a φ (E x) - E x + n • x - E x := fun x => rfl
  have hS' : ∀ x, S' x = b φ (E' x) - E' x + n • x - E' x := fun x => rfl
  have hinj : Function.Injective S := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : ∀ s, a (j s) (a φ (E x)) = a φ (E x) := fun s => by
      obtain ⟨t, ht⟩ := hn s
      rw [← Module.End.mul_apply, ← map_mul, ht, map_mul, Module.End.mul_apply, hE]
    have h2 := congrArg E hx
    rw [hS, map_sub, map_add (f := _), map_sub, map_nsmul, hE1 _ h1, hE1 _ (hE x), map_zero, add_sub_cancel_right,
      ← smul_sub] at h2
    have h3 : a φ (E x) = E x := sub_eq_zero.mp (hcan _ h2)
    have h4 : E x = 0 := by
      by_contra h0
      refine hno ⟨_, h0, fun g => ?_⟩
      obtain ⟨m, t, rfl⟩ := hg g
      rw [map_mul, Module.End.mul_apply, hE]
      exact (GlobalTheory.PstLaws.vecStab a (E x)).zpow_mem h3 m
    rw [hS, h4, map_zero, sub_zero, sub_zero, zero_add] at hx
    exact hcan _ hx
  have hsur := LinearMap.injective_iff_surjective.mp hinj
  have hsur' : Function.Surjective S' := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := hsur x
    refine ⟨mk z, ?_⟩
    rw [hS, hS', hEE, hc, map_sub, map_add (f := _), map_sub, map_nsmul]
  refine hy (LinearMap.injective_iff_surjective.mpr hsur' ?_)
  rw [hS', hE2, map_nsmul, hi, map_zero, sub_self, zero_add, sub_self]

theorem UpperTheory.exists_weil_invariant_in_Dpst_of_weilDeligne_invariant :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)], (∃ y : WDSpace P ι ρ, y ≠ 0 ∧ ∀ σ, wdRho P ι Bw h hj ρ σ y = y) → ∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ σ, weilD Bw h P ρ σ x = x := by
  intro F Ω _ _ _ _ _ l _ ι A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ h1
  obtain ⟨y, hy, hi⟩ := h1
  let a : ↥(Weil h) →* Module.End ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) :=
    { toFun := fun σ => urEnd P ρ (weilD Bw h P ρ σ) (weilD_mulD Bw h P ρ hj σ)
      map_one' := LinearMap.ext fun x => LinearMap.congr_fun (map_one (weilD Bw h P ρ)) ((toUr P ρ).symm x)
      map_mul' := fun σ τ => LinearMap.ext fun x =>
        LinearMap.congr_fun (map_mul (weilD Bw h P ρ) σ τ) ((toUr P ρ).symm x) }
  have := compactSpace_Ine (E := F) A
  have hle : (MonoidHom.comp (weilD Bw h P ρ) (ineIncl h)).ker ≤ (a.comp (ineIncl h)).ker := fun s hs =>
    LinearMap.ext fun x => LinearMap.congr_fun (MonoidHom.mem_ker.mp hs) ((toUr P ρ).symm x)
  have : Finite (Ine (F := F) A ⧸ (a.comp (ineIncl h)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ (Subgroup.isOpen_mono hle (isSmooth_weilD Bw h P ρ hj))
  have hn : ∀ s, ∃ t, ineIncl h s * frob h = frob h * ineIncl h t := fun s => by
    obtain ⟨t, ht⟩ := exists_eq_zpow_mul (deg_frob (h := h)) (ineIncl h s * frob h)
    refine ⟨t, ?_⟩
    rw [deg_mul, deg_ineIncl, deg_frob, zero_add, zpow_one] at ht
    exact ht
  obtain ⟨x, hx, hf⟩ := UpperTheory.fixed_vector_descends_weil_group (ineIncl h) (frob h) hn
    (fun σ => ⟨deg σ, exists_eq_zpow_mul (deg_frob (h := h)) σ⟩) a (wdRho P ι Bw h hj ρ)
    ((AddMonoidHom.mk' (wdMk P ι ρ) (wdMk_add P ι ρ)).comp (toUr P ρ).symm.toAddMonoidHom) (span_wdMk P ι ρ)
    (fun g x => wdRho_mk P ι Bw h hj ρ g ((toUr P ρ).symm x)) y hy hi
  exact ⟨(toUr P ρ).symm x, hx, hf⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCommonEigenvectorOfCharpolySplitCharacters
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_common_eigenvector_of_charpoly_split_characters :
    ∀ {Γ I W : Type} [Group Γ] [Group I] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ} (i : I →* Γ) (Φ : Γ) (ρ : Γ →* Module.End ℂ W) (μ : Fin n → Γ →* ℂˣ), (∀ σ s, ∃ t, σ * i s = i t * σ) → (∀ σ, ∃ (m : ℤ) (s : I), σ = Φ ^ m * i s) → (Set.range fun s => ρ (i s)).Finite → (∀ σ, (ρ σ).charpoly = ∏ j, (X - C (μ j σ : ℂ))) → ∀ j, ∃ y : W, y ≠ 0 ∧ ∀ σ, ρ σ y = (μ j σ : ℂ) • y := by
  intro Γ I W _ _ _ _ _ n i Φ ρ μ hnorm hgen hfin hchar j
  classical
  have htr : ∀ σ, LinearMap.trace ℂ W (ρ σ) = ∑ k, (μ k σ : ℂ) := by
    intro σ
    rw [LinearMap.trace_eq_matrix_trace ℂ (Module.Free.chooseBasis ℂ W),
      Matrix.trace_eq_neg_charpoly_nextCoeff, LinearMap.charpoly_toMatrix, hchar,
      Polynomial.prod_X_sub_C_nextCoeff, neg_neg]
  have heig : ∀ σ k, (ρ σ).HasEigenvalue (μ k σ : ℂ) := by
    intro σ k
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hchar, Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  let φ : I →* (Module.End ℂ W)ˣ := (ρ.toHomUnits).comp i
  have hφ : ∀ s, ((φ s : (Module.End ℂ W)ˣ) : Module.End ℂ W) = ρ (i s) := fun s => rfl
  have hker : ∀ k, φ.ker ≤ ((μ k).comp i).ker := by
    intro k s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    have h1 : ρ (i s) = 1 := by rw [← hφ, hs]; rfl
    obtain ⟨v, hv⟩ := (heig (i s) k).exists_hasEigenvector
    have hv1 := hv.apply_eq_smul
    rw [h1, Module.End.one_apply] at hv1
    have h2 : ((μ k (i s) : ℂ) - 1) • v = 0 := by rw [sub_smul, one_smul, ← hv1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · apply Units.ext
      simp only [MonoidHom.comp_apply, Units.val_one]
      exact sub_eq_zero.mp h
    · exact absurd h hv.2
  have hfinU : (Set.range φ).Finite := by
    refine (Set.Finite.preimage (Function.Injective.injOn (fun a b h => Units.ext h)) hfin).subset ?_
    rintro _ ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  have hr : ∀ q : I ⧸ φ.ker, QuotientGroup.kerLift φ q ∈ Set.range φ := by
    intro q
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨s, (QuotientGroup.kerLift_mk φ s).symm⟩
  haveI : Finite (I ⧸ φ.ker) := by
    haveI := hfinU.to_subtype
    exact Finite.of_injective (fun q => (⟨_, hr q⟩ : Set.range φ))
      (fun a b hab => QuotientGroup.kerLift_injective φ (congrArg Subtype.val hab))
  letI : Fintype (I ⧸ φ.ker) := Fintype.ofFinite _
  let R : I ⧸ φ.ker →* Module.End ℂ W := (Units.coeHom (Module.End ℂ W)).comp (QuotientGroup.kerLift φ)
  let c : Fin n → (I ⧸ φ.ker →* ℂˣ) := fun k => QuotientGroup.lift φ.ker ((μ k).comp i) (hker k)
  have hR : ∀ s : I, R (s : I ⧸ φ.ker) = ρ (i s) := fun s => rfl
  have hc : ∀ k (s : I), c k (s : I ⧸ φ.ker) = μ k (i s) := fun k s => rfl
  let E : Submodule ℂ W := ⨅ s, (ρ (i s)).eigenspace (μ j (i s) : ℂ)
  have hmemE : ∀ y, y ∈ E ↔ ∀ s, ρ (i s) y = (μ j (i s) : ℂ) • y := by
    intro y
    simp only [E, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hEinv : ∀ y ∈ E, ρ Φ y ∈ E := by
    intro y hy
    rw [hmemE] at hy ⊢
    intro s
    obtain ⟨t, ht⟩ := hnorm Φ⁻¹ s
    have e1 : i s * Φ = Φ * i t := by
      calc i s * Φ = Φ * (Φ⁻¹ * i s) * Φ := by group
        _ = Φ * (i t * Φ⁻¹) * Φ := by rw [ht]
        _ = Φ * i t := by group
    have e2 : μ j (i s) = μ j (i t) := by
      have h3 := congrArg (μ j) e1
      simp only [map_mul] at h3
      rw [mul_comm (μ j Φ)] at h3
      exact mul_right_cancel h3
    calc ρ (i s) (ρ Φ y) = ρ (i s * Φ) y := by rw [map_mul]; rfl
      _ = ρ (Φ * i t) y := by rw [e1]
      _ = ρ Φ (ρ (i t) y) := by rw [map_mul]; rfl
      _ = (μ j (i s) : ℂ) • ρ Φ y := by rw [hy t, map_smul, e2]
  have hmain : ∃ y ∈ E, y ≠ 0 ∧ ρ Φ y = (μ j Φ : ℂ) • y := by
    by_contra hno
    push_neg at hno
    let A : Module.End ℂ E := (ρ Φ).restrict hEinv
    let p := LinearMap.charpoly A
    have hp : p.eval (μ j Φ : ℂ) ≠ 0 := by
      intro h0
      have hA : A.HasEigenvalue (μ j Φ : ℂ) := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr h0
      obtain ⟨v, hv⟩ := hA.exists_hasEigenvector
      have hv0 : (v : W) ≠ 0 := by
        intro h
        apply hv.2
        exact Subtype.ext h
      apply hno v v.2 hv0
      have h5 := congrArg Subtype.val hv.apply_eq_smul
      simpa [A] using h5
    let S := Finset.univ.filter (fun k : Fin n => (μ k Φ : ℂ) ≠ μ j Φ)
    let h := ∏ k ∈ S, (Polynomial.X - Polynomial.C (μ k Φ : ℂ))
    let f := h * p
    have key : ∀ y (hy : y ∈ E), Polynomial.aeval (ρ Φ) p y = ((Polynomial.aeval A p) ⟨y, hy⟩ : W) := by
      intro y hy
      rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
      simp [A, Module.End.pow_restrict, LinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Module.End.pow_restrict]
      rfl
    have hfE : ∀ y ∈ E, Polynomial.aeval (ρ Φ) f y = 0 := by
      intro y hy
      rw [Polynomial.aeval_mul, Module.End.mul_apply, key y hy, LinearMap.aeval_self_charpoly]
      simp
    let P : Module.End ℂ W := ∑ q : I ⧸ φ.ker, (((c j q)⁻¹ : ℂˣ) : ℂ) • R q
    have hRP : ∀ a, R a * P = ((c j a : ℂˣ) : ℂ) • P := by
      intro a
      simp only [P, Finset.mul_sum, mul_smul_comm, ← map_mul, Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun q => ?_)
      simp only [Equiv.coe_mulLeft, smul_smul, map_mul]
      congr 1
      rw [← Units.val_mul, _root_.mul_inv_rev, mul_left_comm, mul_inv_cancel, mul_one]
    have hPE : ∀ w, P w ∈ E := by
      intro w
      rw [hmemE]
      intro s
      rw [← hR s, ← Module.End.mul_apply, hRP, LinearMap.smul_apply, hc]
    have hfP : Polynomial.aeval (ρ Φ) f * P = 0 := by
      apply LinearMap.ext
      intro w
      rw [Module.End.mul_apply, LinearMap.zero_apply]
      exact hfE _ (hPE w)
    have htrq : ∀ s : I, LinearMap.trace ℂ W (Polynomial.aeval (ρ Φ) f * ρ (i s)) =
        ∑ k, f.eval (μ k Φ : ℂ) * (μ k (i s) : ℂ) := by
      intro s
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul, map_sum]
      simp_rw [smul_mul_assoc, map_smul, ← map_pow, ← map_mul, htr]
      simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, Polynomial.eval_eq_sum_range,
        Finset.sum_mul, Finset.mul_sum, smul_eq_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun m _ => by ring))
    have hq : ∀ q, LinearMap.trace ℂ W (Polynomial.aeval (ρ Φ) f * R q) =
        ∑ k, f.eval (μ k Φ : ℂ) * (c k q : ℂ) := by
      intro q
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
      rw [hR, htrq]
      rfl
    have htot : LinearMap.trace ℂ W (Polynomial.aeval (ρ Φ) f * P) =
        ∑ k, f.eval (μ k Φ : ℂ) * ∑ q : I ⧸ φ.ker, (((c k q : ℂˣ) : ℂ) * (((c j q)⁻¹ : ℂˣ) : ℂ)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [P, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul, hq]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun q _ => by ring))
    have hψ : ∀ k, ∑ q : I ⧸ φ.ker, (((c k q : ℂˣ) : ℂ) * (((c j q)⁻¹ : ℂˣ) : ℂ)) =
        ((if (Units.coeHom ℂ).comp (c k / c j) = 1 then Fintype.card (I ⧸ φ.ker) else 0 : ℕ) : ℂ) := by
      intro k
      rw [← sum_hom_units]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp [div_eq_mul_inv]
    have hzero : ∀ k, (μ k Φ : ℂ) ≠ μ j Φ → f.eval (μ k Φ : ℂ) = 0 := by
      intro k hk
      simp only [f, Polynomial.eval_mul, h, Polynomial.eval_prod]
      rw [Finset.prod_eq_zero (i := k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩) (by simp), zero_mul]
    have hfl : f.eval (μ j Φ : ℂ) ≠ 0 := by
      simp only [f, Polynomial.eval_mul, h, Polynomial.eval_prod]
      refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)) hp
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact sub_ne_zero.mpr (Ne.symm (Finset.mem_filter.mp hk).2)
    let N : ℕ := ∑ k ∈ Finset.univ.filter (fun k : Fin n => (μ k Φ : ℂ) = μ j Φ),
      (if (Units.coeHom ℂ).comp (c k / c j) = 1 then Fintype.card (I ⧸ φ.ker) else 0)
    have hN : N ≠ 0 := by
      have hj : j ∈ Finset.univ.filter (fun k : Fin n => (μ k Φ : ℂ) = μ j Φ) := by simp
      have h7 : (Units.coeHom ℂ).comp (c j / c j) = 1 := by simp
      intro h8
      have h9 := (Finset.sum_eq_zero_iff.mp h8) j hj
      rw [if_pos h7] at h9
      exact Fintype.card_ne_zero h9
    have heq : LinearMap.trace ℂ W (Polynomial.aeval (ρ Φ) f * P) = f.eval (μ j Φ : ℂ) * N := by
      rw [htot]
      simp only [hψ, N, Nat.cast_sum, Finset.mul_sum]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      by_cases hk : (μ k Φ : ℂ) = μ j Φ
      · rw [if_pos hk, hk]
      · rw [if_neg hk, hzero k hk, zero_mul]
    rw [hfP, map_zero] at heq
    exact mul_ne_zero hfl (Nat.cast_ne_zero.mpr hN) heq.symm
  obtain ⟨y, hyE, hy0, hyΦ⟩ := hmain
  refine ⟨y, hy0, ?_⟩
  let G : Subgroup Γ :=
    { carrier := {σ | ρ σ y = (μ j σ : ℂ) • y}
      mul_mem' := by
        intro a b ha hb
        show ρ (a * b) y = (μ j (a * b) : ℂ) • y
        rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, map_mul, Units.val_mul, mul_comm]
      one_mem' := by
        show ρ 1 y = (μ j 1 : ℂ) • y
        simp
      inv_mem' := by
        intro a ha
        show ρ a⁻¹ y = (μ j a⁻¹ : ℂ) • y
        have h4 : y = ρ a⁻¹ (ρ a y) := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rw [ha, map_smul] at h4
        rw [map_inv (μ j), Units.val_inv_eq_inv_val]
        calc ρ a⁻¹ y = (μ j a : ℂ)⁻¹ • ((μ j a : ℂ) • ρ a⁻¹ y) := by
              rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
          _ = (μ j a : ℂ)⁻¹ • y := by rw [← h4] }
  intro σ
  obtain ⟨m, s, rfl⟩ := hgen σ
  have h1 : Φ ∈ G := hyΦ
  have h2 : i s ∈ G := (hmemE y).1 hyE s
  exact G.mul_mem (G.zpow_mem h1 m) h2
end

section Phi
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
private theorem phiMain (x : ↥(Dpst P ρ)) (hx0 : x ≠ 0) (hW : ∀ σ, weilD Bw h P ρ σ x = x) :
    ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ phiD P ρ z = z ∧ ∀ g, actD P ρ g z = z := by
  obtain ⟨n, hn, hp⟩ := exists_period h Bw hj P ρ x hW
  obtain ⟨c, hc1, hc2⟩ := exists_orbit l n hn
  obtain ⟨j, hz0, hz1⟩ := exists_trace (mulD P ρ) (phiD P ρ) n (by omega) (fun i => (frobUr l ^ i) c) hc2
    (by simpa using hc1) (fun i j => by rw [phiD_pow_mulD, pow_zero, AlgHom.one_apply, map_pow]) x hx0 hp
  refine ⟨_, hz0, hz1, fix_of_weil h Bw P ρ _ fun σ => ?_⟩
  refine (congrArg (actD P ρ (weilToGK Bw h σ)) (zpow_fix (phiU P ρ) _ hz1 (-alpha l σ))).symm.trans ?_
  have hcm : Commute (weilD Bw h P ρ σ) (∑ i ∈ Finset.range n, phiD P ρ ^ i *
      mulD P ρ ((frobUr l ^ 0) c ^ j)) := by
    refine Commute.sum_right _ _ _ fun i _ => Commute.mul_right (Commute.pow_right ?_ i)
      (weilD_mulD Bw h P ρ hj _ _)
    rw [weilD_apply]
    exact (Commute.mul_right (phiD_actD P ρ _)
      (Commute.units_zpow_right (u := phiU P ρ) (Commute.refl _) _)).symm
  exact (LinearMap.congr_fun hcm.eq x).trans (congrArg _ (hW σ))

end

private theorem ordPhiU :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (_hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)], (∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ σ, weilD Bw h P ρ σ x = x) → ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ GlobalTheory.Pst.phiD P ρ z = z ∧ ∀ g, GlobalTheory.Pst.actD P ρ g z = z := by
  intro F Ω _ _ _ _ _ l hl A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ ⟨x, hx0, hW⟩
  exact phiMain h Bw hj P ρ x hx0 hW

end Phi

section Priv
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
    (hμ : ∀ j k, j ≠ k → μ j ≠ μ k ∧ μ j ≠ μ k * unrChar h (qPow w 1))
    (hP : ∀ σ, (wdPst P ι Bw h hj ρ).charPol σ = ∏ j, (X - C (μ j σ : ℂ))) :
    wdN P ι ρ = 0 ∧ ∀ j, μ j = 1 → ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ phiD P ρ z = z ∧ ∀ g, actD P ρ g z = z := by
  haveI := hV.finite
  have hc : ∀ σ, (wdRho P ι Bw h hj ρ σ).charpoly = ∏ j, (X - C (μ j σ : ℂ)) :=
    fun σ => (DpstMap.charPol_wdPst P ι Bw h hj ρ hV σ).symm.trans (hP σ)
  have hL := UpperTheory.exists_common_eigenvector_of_charpoly_split_characters (ineIncl h) (frob h) (wdRho P ι Bw h hj ρ) μ (ine_normal h)
    (fun σ => ⟨deg σ, exists_eq_zpow_mul deg_frob σ⟩) (isSmooth_wdRho P ι Bw h hj ρ).finite_range hc
  have hq : ((qPow w 1 : ℂˣ) : ℂ) = ((normV w : ℕ) : ℂ) := by simp
  have hdim : finrank ℂ (WDSpace P ι ρ) = n := by
    rw [← LinearMap.charpoly_natDegree (wdRho P ι Bw h hj ρ 1), hc, natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  refine ⟨UpperTheory.eq_zero_of_twisted_commute_of_distinct_characters (wdRho P ι Bw h hj ρ) μ (unrChar h (qPow w 1)) _ hdim hL
    (fun j k e => by_contra fun hjk => (hμ j k hjk).1 e) (fun j k e => ?_) fun σ => ?_, fun j hj1 => ?_⟩
  · by_cases hjk : j = k
    · subst hjk
      have h1 := congrArg (fun x : ℂˣ => (x : ℂ)) (left_eq_mul.1 (DFunLike.congr_fun e (frob h)))
      simp only [unrChar_apply, deg_frob, zpow_one, hq, Units.val_one, Nat.cast_eq_one] at h1
      exact (ReciprocityTheory.Gal.one_lt_normV w).ne' h1
    · exact (hμ j k hjk).2 e
  · rw [unrChar_apply, Units.val_zpow_eq_zpow_val, hq]
    exact wdRho_wdN P ι Bw h hj ρ σ
  have h1 := hL j
  simp only [hj1, MonoidHom.one_apply, Units.val_one, one_smul] at h1
  exact ordPhiU h Bw hj P ρ (UpperTheory.exists_weil_invariant_in_Dpst_of_weilDeligne_invariant ι h Bw hj P ρ h1)

private theorem core (hB : DeRhamPotSemistable) {n : ℕ} (r : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l))
    (hr : Continuous r) (HT : (F →+* Qbar l) → Multiset ℤ) (μ : Fin n → ↥(Weil h) →* ℂˣ)
    (hμ : ∀ j k, j ≠ k → μ j ≠ μ k ∧ μ j ≠ μ k * unrChar h (qPow w 1))
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
    have hval := H.val s g hg hs
    simp only [MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val] at hval ⊢
    rw [hval, mul_inv, map_inv₀]
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

private theorem good_comp {a : ↥(Weil h) →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) {n : ℕ}
    {ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ}
    (hne : ∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * GlobalTheory.SmGL.absPow (w.adicCompletion F) 1) :
    ∀ j k, j ≠ k → (ω j).comp a ≠ (ω k).comp a ∧ (ω j).comp a ≠ (ω k).comp a * unrChar h (qPow w 1) := by
  intro j k hjk
  refine ⟨fun e => (hne j k hjk).1 ((MonoidHom.cancel_right ha.surj).1 e), fun e => (hne j k hjk).2
    ((MonoidHom.cancel_right ha.surj).1 ?_)⟩
  rw [e, MonoidHom.mul_comp, ← ha.absPow_comp, Complex.ofReal_one]

private theorem flag (hL : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal)
    {a : ↥(Weil h) →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) (n : ℕ) :
    ∀ (r : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (hh : Fin n → (F →+* Qbar l) → ℤ), (∀ τ, StrictMono fun j => hh j τ) →
    ∀ (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ) (ψ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      (∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) →
      (∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * GlobalTheory.SmGL.absPow (w.adicCompletion F) 1) →
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
      (good_comp h ha fun j k hjk => ⟨fun e => (hne j k hjk).1 (mul_right_cancel e),
        fun e => (hne j k hjk).2 (mul_right_cancel (e.trans (mul_right_comm _ _ _)))⟩)
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

end Priv

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Loc.ordFlagU :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ) (w : HeightOneSpectrum (𝓞 L)), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ (r : Dec (F := L) A →* GL (Fin n) (Qbar l)), Continuous r → ∀ (hh : Fin n → (L →+* Qbar l) → ℤ), (∀ τ, StrictMono fun j => hh j τ) → ∀ (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ) (ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ), (∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) → (∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * absPow (w.adicCompletion L) 1) → DRat ι h r (fun τ => Finset.univ.val.map fun j => hh j τ) (fun s => ∏ j, (X - C (ω j (a s) : ℂ))) → W.HasFlag r ψ ∧ PotCrys A r := by
  intro hL F Ω _ _ _ _ _ l _ _ ι n w hw A h a ha r hr hh hmono ω ψ hO hne hD
  exact ⟨flag ι h hL hw ha n r hr hh hmono ω ψ hO hne hD, fun O _ _ _ Bw hj =>
    (core ι h hL.aut.berger r hr _ (fun j => (ω j).comp a) (good_comp h ha hne) hD Bw hj).1⟩
