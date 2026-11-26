module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Expand
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoConj

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoBkRes
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoEmbConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.embConj :
    ∀ (l : ℕ) [Fact l.Prime] (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (j₀ : Ω →+* Om l) (τ : K →+* Om l), ∃ g : G ℚ Ω, (j₀.comp (g : Ω →+* Ω)).comp (algebraMap K Ω) = τ := by
  intro l _ K Ω _ _ _ _ _ _ _ j₀ τ
  haveI : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ K Ω
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hsub : ∀ x : K, ∃ b : Ω, j₀ b = τ x := by
    intro x
    have hp : minpoly ℚ x ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral x)
    have hrat : j₀.comp (algebraMap ℚ Ω) = τ.comp (algebraMap ℚ K) := Subsingleton.elim _ _
    have hroot : τ x ∈ (((minpoly ℚ x).map (algebraMap ℚ Ω)).map j₀).roots := by
      rw [Polynomial.map_map, Polynomial.mem_roots_map hp, hrat, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, minpoly.aeval, map_zero]
    rw [(IsAlgClosed.splits ((minpoly ℚ x).map (algebraMap ℚ Ω))).roots_map j₀] at hroot
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.mp hroot
    exact ⟨b, hb⟩
  choose f hf using hsub
  let τ' : K →+* Ω :=
    { toFun := f
      map_one' := j₀.injective (by rw [hf, map_one, map_one])
      map_mul' := fun a b => j₀.injective (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := j₀.injective (by rw [hf, map_zero, map_zero])
      map_add' := fun a b => j₀.injective (by rw [hf, map_add (f := _), map_add (f := _), hf, hf]) }
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let g0 : Ω →ₐ[ℚ] Ω := (τ'.toRatAlgHom).liftNormal Ω
  refine ⟨AlgEquiv.ofBijective g0 (Algebra.IsAlgebraic.algHom_bijective g0), ?_⟩
  ext x
  show j₀ (g0 (algebraMap K Ω x)) = τ x
  rw [AlgHom.liftNormal_commutes]
  exact hf x
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoResAway
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.resAway :
    ∀ (l : ℕ) [Fact l.Prime] (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (C V : Type) [CommRing C] [AddCommGroup V] [Module C V] (ρ : Representation C (G ℚ Ω) V) (c : G ℚ Ω → V), (∀ g h, c (g * h) = c g + ρ g (c h)) → (∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ∃ x : V, ∀ s ∈ Ine (F := ℚ) A, c s = ρ s x - x) → ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ∃ x : V, ∀ s ∈ Ine (F := K) A, c (s.restrictScalars ℚ) = ρ (s.restrictScalars ℚ) x - x := by
  intro l _ K Ω _ _ _ _ _ _ _ C V _ _ _ ρ c hc hyp w hw
  haveI : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ K Ω
  obtain ⟨B, hB⟩ := exists_isPlaceOver (F := K) Ω w
  have hne : w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K)) ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hy0 hy (Algebra.IsIntegral.isIntegral y)
  let p : HeightOneSpectrum (𝓞 ℚ) := ⟨w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K)), Ideal.comap_isPrime _ _, hne⟩
  have hBp : IsPlaceOver B p := by
    intro y
    have key := hB (algebraMap (𝓞 ℚ) (𝓞 K) y)
    have hcoe : ((algebraMap (𝓞 ℚ) (𝓞 K) y : 𝓞 K) : K) = algebraMap ℚ K (y : ℚ) := rfl
    rw [hcoe, ← IsScalarTower.algebraMap_apply] at key
    exact key
  have hlp : ((l : ℕ) : 𝓞 ℚ) ∉ p.asIdeal := by
    show _ ∉ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact hw
  obtain ⟨A, hA, x, hx⟩ := hyp p hlp
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hBp
  refine ⟨B, hB, ρ σ x - c σ, ?_⟩
  intro s hs
  have ht : s.restrictScalars ℚ ∈ Ine (F := ℚ) B := ⟨hs.1, fun y hy => hs.2 y hy⟩
  rw [← hσ] at ht
  have hu := hx _ (GlobalTheory.Cut.ShaBound.conj_mem_Ine' ht)
  have htu : s.restrictScalars ℚ * σ = σ * (σ⁻¹ * s.restrictScalars ℚ * σ) := by group
  have e1 := hc (s.restrictScalars ℚ) σ
  have e2 := hc σ (σ⁻¹ * s.restrictScalars ℚ * σ)
  rw [htu] at e1
  have hct := eq_sub_of_add_eq (e1.symm.trans e2)
  have hm : ρ σ (ρ (σ⁻¹ * s.restrictScalars ℚ * σ) x) = ρ (s.restrictScalars ℚ) (ρ σ x) := by
    rw [← Module.End.mul_apply, ← map_mul, ← htu, map_mul, Module.End.mul_apply]
  rw [hct, hu, map_sub, hm, map_sub]
  abel
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.bkRes :
    ∀ (l : ℕ) [Fact l.Prime] (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (C V : Type) [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G ℚ Ω) V) (c : G ℚ Ω → V), c ∈ Z1 ρ → IsBK l ρ c → (fun s : G K Ω => c (s.restrictScalars ℚ)) ∈ Z1 (ρ.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) ∧ IsBK l (ρ.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) (fun s : G K Ω => c (s.restrictScalars ℚ)) := by
  intro l _ K Ω _ _ _ _ _ _ _ C V _ _ _ _ _ _ _ _ _ ρ c hc hbk
  obtain ⟨hcont, hcc⟩ := (mem_Z1_iff_cocycle _ _).1 hc
  have hcont' : Continuous fun s : G K Ω => c (s.restrictScalars ℚ) :=
    hcont.comp (continuous_restrictScalarsHom ℚ K Ω)
  have hcc' : ∀ s t : G K Ω, c ((s * t).restrictScalars ℚ) =
      c (s.restrictScalars ℚ) + ρ (s.restrictScalars ℚ) (c (t.restrictScalars ℚ)) :=
    fun s t => hcc (s.restrictScalars ℚ) (t.restrictScalars ℚ)
  refine ⟨(mem_Z1_iff_cocycle _ _).2 ⟨hcont', hcc'⟩,
    UpperTheory.V.X.Kato.resAway l K Ω C V ρ c hcc hbk.away, fun τ => ?_⟩
  obtain ⟨j₀, -, -, x, hx⟩ := hbk.above (τ.comp (algebraMap ℚ K))
  obtain ⟨g, hg⟩ := UpperTheory.V.X.Kato.embConj l K Ω j₀ τ
  refine ⟨j₀.comp (g : Ω →+* Ω), hg, ⟨hcont'.comp (continuous_fst.comp continuous_subtype_val),
    fun s t => hcc' s.1.1 t.1.1⟩,
    TensorProduct.AlgebraTensorModule.map (ρ g⁻¹) LinearMap.id x - c g⁻¹ ⊗ₜ[ℚ_[l]] (1 : UpperTheory.V.Loc.Bcr l), ?_⟩
  rintro ⟨⟨s, σ⟩, hs⟩
  have ht : (g * s.restrictScalars ℚ * g⁻¹, σ) ∈ decJ ℚ j₀ := by
    intro y
    have h := hs (g⁻¹ y)
    change σ (j₀ (g (g.symm y))) = j₀ (g (s (g.symm y))) at h
    rw [AlgEquiv.apply_symm_apply] at h
    exact h
  have h1 := hx ⟨_, ht⟩
  change c (s.restrictScalars ℚ) ⊗ₜ[ℚ_[l]] (1 : UpperTheory.V.Loc.Bcr l) =
    TensorProduct.AlgebraTensorModule.map (ρ (s.restrictScalars ℚ)) ((UpperTheory.V.Loc.PP l).actQ σ).toLinearMap _ - _
  change c (g * s.restrictScalars ℚ * g⁻¹) ⊗ₜ[ℚ_[l]] (1 : UpperTheory.V.Loc.Bcr l) =
    TensorProduct.AlgebraTensorModule.map (ρ (g * s.restrictScalars ℚ * g⁻¹))
      ((UpperTheory.V.Loc.PP l).actQ σ).toLinearMap x - x at h1
  generalize s.restrictScalars ℚ = u at h1 ⊢
  have e1 : g⁻¹ * (g * u * g⁻¹) = u * g⁻¹ := by group
  have e2 := hcc g⁻¹ (g * u * g⁻¹)
  rw [e1, hcc] at e2
  have key : ∀ y : TensorProduct ℚ_[l] V (UpperTheory.V.Loc.Bcr l),
      TensorProduct.AlgebraTensorModule.map (ρ g⁻¹) LinearMap.id
        (TensorProduct.AlgebraTensorModule.map (ρ (g * u * g⁻¹)) ((UpperTheory.V.Loc.PP l).actQ σ).toLinearMap y) =
      TensorProduct.AlgebraTensorModule.map (ρ u) ((UpperTheory.V.Loc.PP l).actQ σ).toLinearMap
        (TensorProduct.AlgebraTensorModule.map (ρ g⁻¹) LinearMap.id y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply]
      rw [← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h2 := congrArg (TensorProduct.AlgebraTensorModule.map (ρ g⁻¹)
    (LinearMap.id : UpperTheory.V.Loc.Bcr l →ₗ[ℚ_[l]] UpperTheory.V.Loc.Bcr l)) h1
  rw [map_sub, key, TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply] at h2
  rw [map_sub, TensorProduct.AlgebraTensorModule.map_tmul, eq_sub_of_add_eq e2, TensorProduct.sub_tmul,
    TensorProduct.add_tmul, h2]
  simp only [AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply, map_one]
  abel
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ChrInvNeg
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

private theorem cls_onto {Ω : Type} [Field Ω] [inst : Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] :
    Function.Surjective (Chr.cls ℚ Ω N) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact (Chr.clsOnto Ω N).1

private theorem red_chi {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    {O k : Type} [CommRing O] [Algebra ℤ_[l] O] [Field k] [CharP k l] (red : O →+* k) (g : G ℚ Ω)
    (h : ∀ t : Ω, t ^ l = 1 → g t = t) : red (chiO ℚ Ω l O g : O) = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hpow : ∀ t : Ω, t ^ l ^ 1 = 1 → t ^ (1 : ZMod (l ^ 1)).val = t := by
    intro t ht
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ht, pow_one]
  have h1 : (cyclotomicCharacter Ω l g.toRingEquiv).val.toZModPow 1 = 1 := by
    rw [cyclotomicCharacter.toZModPow]
    refine (modularCyclotomicCharacter.unique Ω _ _ fun t ht => ?_).symm
    have ht' : (t : Ω) ^ l ^ 1 = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ht, Units.val_one]
    rw [hpow _ ht']
    exact h _ (by rwa [pow_one] at ht')
  rw [← sub_eq_zero, ← map_one (PadicInt.toZModPow (p := l) 1), ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    pow_one, Ideal.mem_span_singleton] at h1
  obtain ⟨y, hy⟩ := h1
  have e : (chiO ℚ Ω l O g : O) = algebraMap ℤ_[l] O (cyclotomicCharacter Ω l g.toRingEquiv).val := rfl
  rw [e, sub_eq_iff_eq_add.1 hy]
  simp

private theorem prodX_unit {R : Type} [CommRing R] {f n : ℕ} (φ : DirichletCharacter R f) (ξ : DirichletCharacter R (2 ^ n))
    (u : (ZMod (f * 2 ^ n))ˣ) :
    prodX φ ξ (u : ZMod (f * 2 ^ n)) = φ (ZMod.cast (u : ZMod (f * 2 ^ n))) * ξ (ZMod.cast (u : ZMod (f * 2 ^ n))) := by
  rw [prodX, MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd]

private theorem prodX_map {R S : Type} [CommRing R] [CommRing S] (j : R →+* S) {f n : ℕ} (φ : DirichletCharacter R f)
    (ξ : DirichletCharacter R (2 ^ n)) : (prodX φ ξ).ringHomComp j = prodX (φ.ringHomComp j) (ξ.ringHomComp j) := by
  ext u
  rw [MulChar.ringHomComp_apply, prodX_unit, prodX_unit, map_mul, MulChar.ringHomComp_apply, MulChar.ringHomComp_apply]

private theorem prodX_inv {R : Type} [CommRing R] {f n : ℕ} (φ : DirichletCharacter R f)
    (ξ : DirichletCharacter R (2 ^ n)) : (prodX φ ξ)⁻¹ = prodX φ⁻¹ ξ⁻¹ := by
  rw [prodX, prodX, mul_inv, map_inv, map_inv]

private theorem chr_inv_neg {R : Type} [CommRing R] {N : ℕ} (χ : DirichletCharacter R N) : χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply]
  congr 1
  have : ((-1 : (ZMod N)ˣ) : ZMod N) = -1 := by simp
  rw [← this, Ring.inverse_unit]
  simp

private theorem xd_inv {l d : ℕ} {R : Type} [CommRing R] {f n : ℕ} {φ : DirichletCharacter R f}
    {ξ : DirichletCharacter R (2 ^ n)} (h : XData l d φ ξ) : XData l d φ⁻¹ ξ⁻¹ := by
  refine ⟨h.d_pos, h.four, h.f_odd, h.prim.inv, ?_, h.prim2.inv, h.big, ?_⟩
  · simpa only [orderOf_inv] using h.ord
  · simpa only [chr_inv_neg] using h.odd

private theorem xd_map {l d : ℕ} {R S : Type} [CommRing R] [CommRing S] (j : R →+* S) (hj : Function.Injective j) {f n : ℕ}
    {φ : DirichletCharacter R f} {ξ : DirichletCharacter R (2 ^ n)} (h : XData l d φ ξ) :
    XData l d (φ.ringHomComp j) (ξ.ringHomComp j) := by
  haveI : NeZero f := ⟨h.f_odd.pos.ne'⟩
  refine ⟨h.d_pos, h.four, h.f_odd, ?_, ?_, ?_, h.big, ?_⟩
  · rw [DirichletCharacter.isPrimitive_def, (Bern.b_condmap j hj φ).1]; exact h.prim
  · rw [orderOf_dvd_iff_pow_eq_one, MulChar.ringHomComp_pow, orderOf_dvd_iff_pow_eq_one.1 h.ord, MulChar.ringHomComp_one]
  · rw [DirichletCharacter.isPrimitive_def, (Bern.b_condmap j hj ξ).1]; exact h.prim2
  · rw [MulChar.ringHomComp_apply, MulChar.ringHomComp_apply, ← map_mul, h.odd, map_neg, map_one]

private theorem xd_pos {l d : ℕ} (hl : l.Prime) (hd : 0 < d) : 0 < l ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' hl.one_lt)

private theorem xd_ne_two {l d : ℕ} (hd : 0 < d) (h : 4 ∣ l ^ d - 1) : l ≠ 2 := by
  rintro rfl
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  have : 0 < 2 ^ e := by positivity
  rw [pow_succ] at h
  omega

private theorem xi_pow {R : Type} [CommRing R] {n : ℕ} (ξ : DirichletCharacter R (2 ^ n)) (u : (ZMod (2 ^ n))ˣ) :
    ξ (u : ZMod (2 ^ n)) ^ 2 ^ n = 1 := by
  have h1 : Nat.totient (2 ^ n) ∣ 2 ^ n := by
    rcases n with _ | m
    · simp
    · rw [Nat.totient_prime_pow_succ Nat.prime_two]; simp [pow_succ]
  obtain ⟨e, he⟩ := h1
  rw [← map_pow, ← Units.val_pow_eq_pow_val]
  conv_lhs => enter [2, 1, 2]; rw [he]
  rw [pow_mul, ZMod.pow_totient, one_pow, Units.val_one, map_one]

private theorem xd_ord {l d : ℕ} (hl : l.Prime) {R : Type} [CommRing R] {f n : ℕ}
    {φ : DirichletCharacter R f} {ξ : DirichletCharacter R (2 ^ n)} (h : XData l d φ ξ) : ¬ l ∣ orderOf (prodX φ ξ) := by
  have h1 : ξ ^ 2 ^ n = 1 := by
    ext u
    rw [MulChar.pow_apply_coe, xi_pow, MulChar.one_apply_coe]
  have h2 : prodX φ ξ ^ ((l ^ d - 1) * 2 ^ n) = 1 := by
    rw [prodX, mul_pow, ← map_pow, ← map_pow, pow_mul, orderOf_dvd_iff_pow_eq_one.1 h.ord, pow_mul', h1]
    simp
  intro hd
  rcases (Nat.Prime.dvd_mul hl).1 (hd.trans (orderOf_dvd_of_pow_eq_one h2)) with h3 | h3
  · have h4 : l ∣ l ^ d := dvd_pow_self l h.d_pos.ne'
    have h5 := (Nat.dvd_sub_iff_right (Nat.one_le_pow d l hl.pos) h4).1 h3
    exact hl.one_lt.ne' (Nat.dvd_one.1 h5)
  · exact xd_ne_two h.d_pos h.four ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h3))

private theorem neg_one_of {R : Type} [CommRing R] [IsDomain R] (x : R) (hx : x ≠ 1) :
    ∀ m : ℕ, x ^ 2 ^ m = 1 → ∃ j : ℕ, x ^ j = -1 := by
  intro m
  induction m with
  | zero => intro h; exact absurd (by simpa using h) hx
  | succ m ih =>
    intro h
    rw [pow_succ, pow_mul, pow_two, mul_self_eq_one_iff] at h
    exact h.elim ih fun h => ⟨_, h⟩

private theorem xd_neg {l d : ℕ} (hl : l.Prime) {R : Type} [CommRing R] [IsDomain R] {f n : ℕ}
    {φ : DirichletCharacter R f} {ξ : DirichletCharacter R (2 ^ n)} (h : XData l d φ ξ) :
    ∃ b : (ZMod (2 ^ n))ˣ, ξ (b : ZMod (2 ^ n)) = -1 := by
  have h0 : 1 ≤ (l ^ d - 1).factorization 2 :=
    (Nat.prime_two.dvd_iff_one_le_factorization (xd_pos hl h.d_pos).ne').1 (dvd_trans (by norm_num) h.four)
  have h1 : 4 ≤ 2 ^ n := by
    refine le_trans ?_ h.big
    calc 4 = 1 * 4 ^ 1 := by norm_num
      _ ≤ _ := Nat.mul_le_mul h.f_odd.pos (Nat.pow_le_pow_right (by norm_num) h0)
  have h2 : ξ ≠ 1 := by
    rintro rfl
    have := h.prim2
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at this
    omega
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.1 h2
  obtain ⟨j, hj⟩ := neg_one_of _ hu n (xi_pow ξ u)
  exact ⟨u ^ j, by rw [Units.val_pow_eq_pow_val, map_pow, hj]⟩

private theorem xd_gal {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l d : ℕ} (hl : l.Prime) {R : Type} [CommRing R]
    [IsDomain R] {f n : ℕ} [NeZero (f * 2 ^ n)] {φ : DirichletCharacter R f} {ξ : DirichletCharacter R (2 ^ n)}
    (h : XData l d φ ξ) :
    ∃ g : G ℚ Ω, (∀ t : Ω, t ^ l = 1 → g t = t) ∧ (Chr.dirG ℚ Ω (prodX φ ξ) g : R) = -1 := by
  obtain ⟨b, hb⟩ := xd_neg hl h
  have hodd : Odd (l * f) := (hl.odd_of_ne_two (xd_ne_two h.d_pos h.four)).mul h.f_odd
  have hco : (l * f).Coprime (2 ^ n) := (Nat.coprime_two_right.2 hodd).pow_right n
  obtain ⟨a, ha1, ha2⟩ := Nat.chineseRemainder hco 1 (b : ZMod (2 ^ n)).val
  have hc : a.Coprime (l * f * 2 ^ n) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.Coprime, ha1.gcd_eq]; simp
    · rw [Nat.Coprime, ha2.gcd_eq]; exact ZMod.val_coe_unit_coprime b
  haveI : NeZero (l * f * 2 ^ n) := ⟨mul_ne_zero hodd.pos.ne' (by positivity)⟩
  obtain ⟨g, hg⟩ := cls_onto (Ω := Ω) (l * f * 2 ^ n) (ZMod.unitOfCoprime a hc)
  refine ⟨g, fun t ht => ?_, ?_⟩
  · have hM : t ^ (l * f * 2 ^ n) = 1 := by rw [mul_assoc, pow_mul, ht, one_pow]
    rw [Chr.cls_spec _ g t hM, hg, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod _ hM,
      pow_eq_pow_mod _ ht, ha1.of_mul_right f, ← pow_eq_pow_mod _ ht, pow_one]
  · have hd : f * 2 ^ n ∣ l * f * 2 ^ n := by rw [mul_assoc]; exact dvd_mul_left _ _
    have e1 : ((Chr.cls ℚ Ω (f * 2 ^ n) g : (ZMod (f * 2 ^ n))ˣ) : ZMod (f * 2 ^ n)) = a := by
      rw [← (Chr.clsFacts ℚ Ω (l * f * 2 ^ n)).2.1 _ hd, MonoidHom.comp_apply, hg, ZMod.unitsMap_val,
        ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd]
    rw [Chr.dirG, MonoidHom.comp_apply, MulChar.coe_toUnitHom, prodX_unit, e1, ZMod.cast_natCast (dvd_mul_right _ _),
      ZMod.cast_natCast (dvd_mul_left _ _), (ZMod.natCast_eq_natCast_iff _ _ _).2 (ha1.of_mul_left l),
      (ZMod.natCast_eq_natCast_iff _ _ _).2 ha2, ZMod.natCast_zmod_val, hb]
    simp

private theorem main (hX : LemmaX) (h16 : UnramifiedCocycleIsCoboundaryOfBernoulliUnit) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (c : HV.Coef l) (k : Type) [Field k] [CharP k l] (red : c.O →+* k) (d f n : ℕ) [NeZero (f * 2 ^ n)]
    (φ : DirichletCharacter c.O f) (ξ : DirichletCharacter c.O (2 ^ n)) (h : XData l d φ ξ) (z : G ℚ Ω → k)
    (hz : IsCoc (redChar Ω red (prodX φ ξ)) z) (hu : UnrEv l (redChar Ω red (prodX φ ξ)) z) :
    ∃ m : k, ∀ g, z g = (redChar Ω red (prodX φ ξ) g : k) * m - m := by
  have hl : l.Prime := Fact.out
  have h2 := xd_ne_two h.d_pos h.four
  obtain ⟨g, hg1, hg2⟩ := xd_gal (Ω := Ω) hl h
  have hne : (-1 : k) ≠ 1 := by
    intro e
    have : ((2 : ℕ) : k) = 0 := by rw [Nat.cast_ofNat, ← one_add_one_eq_two]; nth_rewrite 1 [← e]; simp
    exact h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 ((CharP.cast_eq_zero_iff k l 2).1 this))
  have hg3 : (redChar Ω red (prodX φ ξ) g : k) = -1 := by
    have : (redChar Ω red (prodX φ ξ) g : k) = red (Chr.dirG ℚ Ω (prodX φ ξ) g : c.O) := rfl
    rw [this, hg2, map_neg, map_one]
  refine h16 Ω l h2 c k red _ (prodX φ ξ) (fun e => hne ?_) (xd_ord hl h) ⟨g, ?_⟩ ?_ z hz hu
  · rw [← hg3, e, redChar, Chr.dirG]
    simp
  · rw [hg3, red_chi l red g hg1]; exact hne
  · rw [prodX_inv, prodX_map]
    exact hX l d f n _ _ (xd_map _ Subtype.val_injective (xd_inv h))

theorem UpperTheory.V.X.corX :
    LemmaX → UnramifiedCocycleIsCoboundaryOfBernoulliUnit → CorX := by
  intro hX h16 Ω _ _ _ l _ c k _ _ red d f n _ φ ξ h γ hγ z hz hu
  rcases hγ with rfl | rfl
  · exact main hX h16 Ω l c k red d f n φ ξ h z hz hu
  · have e : (redChar Ω red (prodX φ ξ))⁻¹ = redChar Ω red (prodX φ⁻¹ ξ⁻¹) := by
      rw [← prodX_inv, inv_eq_iff_mul_eq_one]
      ext g
      have : ∀ χ : DirichletCharacter c.O (f * 2 ^ n), (redChar Ω red χ g : k) = red (χ (Chr.cls ℚ Ω (f * 2 ^ n) g : (ZMod (f * 2 ^ n))ˣ)) :=
        fun χ => congrArg red (MulChar.coe_toUnitHom χ _)
      rw [MonoidHom.mul_apply, Units.val_mul, this, this, ← map_mul, ← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]
      simp
    rw [e] at hz hu ⊢
    exact main hX h16 Ω l c k red d f n _ _ (xd_inv h) z hz hu
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcXvan
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Module UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.X

private theorem xvan_of_van {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (γ : G ℚ Ω →* c.Oˣ) (γ' : G ℚ Ω →* (ResidueField c.O)ˣ)
    (h : ∀ g, Raw.bar γ g = (γ' g : ResidueField c.O)) (hv : Van D.T D.pl D.rbar.ker γ') : D.XVan γ := by
  intro z hzlc hzc hzU hzD
  obtain ⟨m, hm⟩ := hv z hzlc (fun g k => by rw [hzc, h])
    (fun A hA g hgA hgK => hzU A hA g hgA (MonoidHom.mem_ker.mp hgK))
    (fun v hvT => by
      obtain ⟨m, hm⟩ := hzD v hvT
      exact ⟨m, fun g hg => by rw [hm g hg, h]⟩)
  exact ⟨m, fun g => by rw [hm g, h]⟩

theorem UpperTheory.V.X.xvan :
    CorX → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), (∀ p ∈ D.T, p.Prime ∧ (D.pl p).valuation (p : Ω) < 1) → ∀ (d f n : ℕ) [NeZero (f * 2 ^ n)] (φ : DirichletCharacter c.O f) (ξ : DirichletCharacter c.O (2 ^ n)), XData l d φ ξ → ∀ γ : G ℚ Ω →* c.Oˣ, (∀ g, Raw.bar γ g = (redChar Ω (residue c.O) (prodX φ ξ) g : ResidueField c.O)) → D.XVan γ ∧ D.XVan γ⁻¹ := by
  intro hCor Ω _ _ _ l _ c D hT d f n _ φ ξ hX γ hγ
  haveI : CharP (ResidueField c.O) l := by
    obtain ⟨-, -, hloc, -⟩ := dvrFacts l c.O
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
    rw [← map_natCast (residue c.O), residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rw [← map_natCast (algebraMap ℤ_[l] c.O)] at hu
    exact PadicInt.p_nonunit (isUnit_of_map_unit (algebraMap ℤ_[l] c.O) _ hu)
  set γ' : G ℚ Ω →* (ResidueField c.O)ˣ := redChar Ω (residue c.O) (prodX φ ξ) with hγ'
  obtain ⟨hKn, hKi, -⟩ := spKer D
  have hv : ∀ γ'' : G ℚ Ω →* (ResidueField c.O)ˣ, (γ'' = γ' ∨ γ'' = γ'⁻¹) →
      Van D.T D.pl D.rbar.ker γ'' := by
    intro γ'' hor
    exact vanOf Ω l (ResidueField c.O) γ''
      (hCor Ω l c (ResidueField c.O) (residue c.O) d f n φ ξ hX γ'' hor) D.T D.pl D.rbar.ker hT hKn hKi
  refine ⟨xvan_of_van D γ γ' hγ (hv γ' (Or.inl rfl)), xvan_of_van D γ⁻¹ γ'⁻¹ ?_ (hv γ'⁻¹ (Or.inr rfl))⟩
  intro g
  have h1 := hγ g
  simp only [Raw.bar, MonoidHom.inv_apply] at h1 ⊢
  rw [map_units_inv, Units.val_inv_eq_inv_val, h1]
end
