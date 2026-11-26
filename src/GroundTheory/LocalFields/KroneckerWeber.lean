module

public import GroundTheory.LocalFields.Existence
public import GroundTheory.LocalFields.PrincipalUnitsRank
public import GroundTheory.LocalFields.LocalReciprocityUniversal

@[expose] public section

section -- merged from GroundTheory.LocalFields.KroneckerWeber
noncomputable section

open IntermediateField ValuativeRel

namespace GroundTheory.LocalField

open Abstract GroundTheory.LocalField.FormalGroup

section Abelian

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

theorem mul_comm_of_isAbelianGalois (L : IntermediateField K Ω) [IsAbelianGalois K L]
    (σ τ : L ≃ₐ[K] L) : σ * τ = τ * σ :=
  (IsMulCommutative.is_comm (M := L ≃ₐ[K] L)).comm σ τ

theorem isAbelianGalois_of_mul_comm (L : IntermediateField K Ω) [IsGalois K L]
    (h : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) : IsAbelianGalois K L where
  is_comm := ⟨h⟩

end Abelian

section LubinTate

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosed Ω] [Algebra.IsSeparable K Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

attribute [local instance] isDiscreteModule_units


include hf in
theorem isAbelianGalois_lubinTateField_sup {n : ℕ} (hn : 0 < n) {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) :
    IsAbelianGalois K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω) := by
  have := hE.1
  have := hE.isGalois
  have : IsSepClosure K Ω := ⟨inferInstance, inferInstance⟩
  have : Normal K (lubinTateField Ω hπ hf n) := by
    refine normal_iff_forall_map_le'.mpr fun σ => ?_
    rw [lubinTateField, adjoin_map, adjoin_le_iff]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    change σ x.val ∈ lubinTateField Ω hπ hf n
    rw [← lubinTateGalPointMap_val hf σ x]
    apply val_mem_lubinTateField hπ hf
    rw [mem_lubinTateTorsion, ← map_smul, (mem_lubinTateTorsion hf n x).mp hx, map_zero]
  have : IsGalois K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω) :=
    isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  exact isAbelianGalois_of_mul_comm _ (lubinTateUnramified_mul_comm hπ hf hn hE)


include hf in
theorem exists_le_lubinTateField_sup_unramifiedTower (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    ∃ n m : ℕ, L ≤ lubinTateField Ω hπ hf (n + 1) ⊔ unramifiedTower K Ω m := by
  have : IsSepClosure K Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨hO, hF⟩ := isOpen_range_normUnits_and_finiteIndex L
  obtain ⟨⟨n, hnH⟩, m, hm, hmH⟩ := exists_unitFiltrationUnits_le_and_range_pow_le hO
  have hE := isUnramifiedSubextension_unramifiedTower (K := K) (Ω := Ω) m
  have := hE.1
  have hmE : m ∣ Module.finrank K (unramifiedTower K Ω m) := by
    rw [finrank_unramifiedTower]
    exact Nat.dvd_factorial (Nat.pos_of_ne_zero hm) m.le_succ
  have hle := range_normUnits_sup_le hπ hf n.succ_pos hE hmE
    ((unitFiltrationUnits_antitone n.le_succ).trans hnH) hmH
  have hM := isAbelianGalois_lubinTateField_sup hπ hf n.succ_pos hE
  exact ⟨n, m, (range_normUnits_le_range_normUnits_iff (mul_comm_of_isAbelianGalois _)
    (mul_comm_of_isAbelianGalois L)).1 hle⟩

end LubinTate

section Padic

namespace Padic

open Polynomial

variable (p : ℕ) [hp : Fact p.Prime]

theorem irreducible_natCast_integer : Irreducible (p : 𝒪[ℚ_[p]]) := by
  have h := (MulEquiv.irreducible_iff (f := (PadicRank.padicIntEquivInteger p).toMulEquiv)
    (x := (p : ℤ_[p]))).2 PadicInt.irreducible_p
  simpa using h

theorem card_residueField : Nat.card 𝓀[ℚ_[p]] = p := by
  rw [← Nat.card_congr (IsLocalRing.ResidueField.mapEquiv
      (PadicRank.padicIntEquivInteger p)).toEquiv,
    Nat.card_congr PadicInt.residueField.toEquiv, Nat.card_zmod]

def multiplicativeLTPoly : 𝒪[ℚ_[p]][X] := (1 + X) ^ p - 1

theorem isLubinTateSeries_multiplicativeLTPoly :
    IsLubinTateSeries (p : 𝒪[ℚ_[p]]) (multiplicativeLTPoly p : PowerSeries 𝒪[ℚ_[p]]) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      multiplicativeLTPoly, coeff_sub, coeff_one_add_X_pow]
    simp
  · rw [Polynomial.coeff_coe, multiplicativeLTPoly, coeff_sub, coeff_one_add_X_pow]
    simp [Polynomial.coeff_one]
  · intro n
    rw [card_residueField, ← Polynomial.coe_X, ← Polynomial.coe_pow, ← Polynomial.coe_sub,
      Polynomial.coeff_coe, multiplicativeLTPoly, coeff_sub, coeff_sub, coeff_one_add_X_pow,
      coeff_one, coeff_X_pow]
    have hp0 := hp.out.ne_zero
    by_cases h0 : n = 0
    · subst h0
      simp [Ne.symm hp0]
    by_cases hpn : n = p
    · subst hpn
      simp [h0]
    rw [ite_eq_right h0, ite_eq_right hpn, sub_zero, sub_zero]
    rcases lt_or_gt_of_ne hpn with h | h
    · exact Nat.cast_dvd_cast (hp.out.dvd_choose_self h0 h)
    · rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero]
      exact dvd_zero _

section Torsion

variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra ℚ_[p] Ω] [ValuativeExtension ℚ_[p] Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

theorem val_pow_smul (n : ℕ)
    (x : IdealPoint Ω (lubinTateFormalGroup (irreducible_natCast_integer p)
      (isLubinTateSeries_multiplicativeLTPoly p))) :
    (((p : 𝒪[ℚ_[p]]) ^ n) • x).val = (1 + x.val) ^ (p ^ n) - 1 := by
  have := t2Space_of_isValuativeTopology Ω
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_smul, ih, lubinTate_uniformizer_smul_val, psEval_polynomial]
    simp only [multiplicativeLTPoly, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add (f := _), Polynomial.map_one,
      Polynomial.map_X, map_sub, map_pow, map_add, map_one, aeval_X]
    rw [add_sub_cancel, ← pow_mul, ← pow_succ']

theorem lubinTateField_le_adjoin_rootsOfUnity (n : ℕ) :
    lubinTateField Ω (irreducible_natCast_integer p) (isLubinTateSeries_multiplicativeLTPoly p) n ≤
      adjoin ℚ_[p] {ζ : Ω | ζ ^ (p ^ n) = 1} := by
  rw [lubinTateField, adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have h := congrArg IdealPoint.val ((mem_lubinTateTorsion _ n x).1 hx)
  rw [val_pow_smul, IdealPoint.val_zero, sub_eq_zero] at h
  have hx' : x.val = (1 + x.val) - 1 := by ring
  rw [hx']
  exact sub_mem (subset_adjoin _ _ h) (one_mem _)

end Torsion

variable {Ω : Type*} [Field Ω] [Algebra ℚ_[p] Ω] [IsSepClosed Ω] [Algebra.IsSeparable ℚ_[p] Ω]


omit [Algebra.IsSeparable ℚ_[p] Ω] in
theorem unramifiedTower_le_adjoin_rootsOfUnity (m : ℕ) :
    unramifiedTower ℚ_[p] Ω m ≤
      adjoin ℚ_[p] {ζ : Ω | ζ ^ (p ^ (m + 1).factorial - 1) = 1} := by
  rw [unramifiedTower, adjoin_simple_le_iff]
  refine subset_adjoin _ _ ?_
  have h := (isPrimitiveRoot_unramifiedTowerRoot (K := ℚ_[p]) (Ω := Ω) m).pow_eq_one
  rwa [card_residueField] at h

theorem exists_le_adjoin_rootsOfUnity (L : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] L]
    [IsAbelianGalois ℚ_[p] L] :
    ∃ N : ℕ, 0 < N ∧ L ≤ adjoin ℚ_[p] {ζ : Ω | ζ ^ N = 1} := by
  let := algebraicValuativeRel ℚ_[p] Ω
  let := algebraicTopology ℚ_[p] Ω
  have := algebraicValuativeRel_valuativeExtension ℚ_[p] Ω
  have := algebraicTopology_isValuativeTopology ℚ_[p] Ω
  obtain ⟨n, m, h⟩ := exists_le_lubinTateField_sup_unramifiedTower (irreducible_natCast_integer p)
    (isLubinTateSeries_multiplicativeLTPoly p) L
  have hM : 0 < p ^ (m + 1).factorial - 1 := Nat.sub_pos_of_lt
    (Nat.one_lt_pow (Nat.factorial_ne_zero _) hp.out.one_lt)
  refine ⟨p ^ (n + 1) * (p ^ (m + 1).factorial - 1),
    Nat.mul_pos (pow_pos hp.out.pos _) hM, h.trans (sup_le ?_ ?_)⟩
  · refine (lubinTateField_le_adjoin_rootsOfUnity p (n + 1)).trans (adjoin.mono _ _ _ ?_)
    intro ζ (hζ : ζ ^ _ = 1)
    change ζ ^ _ = 1
    rw [pow_mul, hζ, one_pow]
  · refine (unramifiedTower_le_adjoin_rootsOfUnity p m).trans (adjoin.mono _ _ _ ?_)
    intro ζ (hζ : ζ ^ _ = 1)
    change ζ ^ _ = 1
    rw [mul_comm, pow_mul, hζ, one_pow]

theorem coprime_pow_sub_one {k : ℕ} (hk : k ≠ 0) : (p ^ k - 1).Coprime p := by
  rw [Nat.coprime_comm, hp.out.coprime_iff_not_dvd]
  intro h
  have h1 : p ∣ p ^ k := dvd_pow_self p hk
  have h2 := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.out.pos)] at h2
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 h2)


omit [Algebra.IsSeparable ℚ_[p] Ω] in
theorem maximalUnramifiedExtension_eq_adjoin_rootsOfUnity :
    maximalUnramifiedExtension ℚ_[p] Ω =
      adjoin ℚ_[p] {ζ : Ω | ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ ζ ^ n = 1} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨m, hm⟩ := exists_mem_unramifiedTower hx
    have h1 := unramifiedTower_le_adjoin_rootsOfUnity p m hm
    refine adjoin.mono ℚ_[p] _ _ ?_ h1
    intro ζ hζ
    have hζ' : ζ ^ (p ^ (m + 1).factorial - 1) = 1 := hζ
    have hpos : 0 < p ^ (m + 1).factorial - 1 :=
      Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.factorial_ne_zero (m + 1)) hp.out.one_lt)
    exact ⟨p ^ (m + 1).factorial - 1, hpos,
      coprime_pow_sub_one p (Nat.factorial_ne_zero (m + 1)), hζ'⟩
  · rw [adjoin_le_iff]
    rintro ζ ⟨n, hn, hcop, hζn⟩
    have hφ : n.totient ≠ 0 := (Nat.totient_pos.2 hn).ne'
    obtain ⟨ξ, hξ⟩ := exists_isPrimitiveRoot_card_pow_sub_one (K := ℚ_[p]) (Ksep := Ω) hφ
    have hdvd : n ∣ p ^ n.totient - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.out.pos)).1
        (Nat.ModEq.pow_totient hcop.symm).symm
    have hU := (isUnramifiedSubextension_adjoin hφ hξ).1
    rw [card_residueField] at hξ
    have : NeZero (p ^ n.totient - 1) := ⟨(Nat.sub_pos_of_lt
      (Nat.one_lt_pow hφ hp.out.one_lt)).ne'⟩
    obtain ⟨i, -, hi⟩ := hξ.eq_pow_of_pow_eq_one (ξ := ζ) (by
      obtain ⟨c, hc⟩ := hdvd
      rw [hc, pow_mul, hζn, one_pow])
    rw [← hi]
    exact hU.le_maximalUnramifiedExtension (pow_mem (mem_adjoin_simple_self ℚ_[p] ξ) i)


variable (Ω) in
theorem maximalAbelianExtension_eq_adjoin_rootsOfUnity :
    maximalAbelianExtension ℚ_[p] Ω = adjoin ℚ_[p] {ζ : Ω | ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1} := by
  have : IsSepClosure ℚ_[p] Ω := ⟨inferInstance, inferInstance⟩
  refine le_antisymm (fun y hy => ?_) ?_
  · obtain ⟨L, _, _, hyL⟩ := exists_finite_abelian_mem hy
    obtain ⟨N, hN, h⟩ := exists_le_adjoin_rootsOfUnity p L
    refine (h.trans (adjoin.mono _ _ _ ?_)) hyL
    intro ζ hζ
    exact ⟨N, hN, hζ⟩
  · rw [adjoin_le_iff]
    rintro ζ ⟨n, hn, hζn⟩
    have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hζn⟩
    have : NeZero (orderOf ζ) := ⟨(orderOf_pos_iff.2 hfin).ne'⟩
    have hζ : IsPrimitiveRoot ζ (orderOf ζ) := IsPrimitiveRoot.orderOf ζ
    have := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ_[p]
    have := IsCyclotomicExtension.isAbelianGalois {orderOf ζ} ℚ_[p] ℚ_[p]⟮ζ⟯
    have : FiniteDimensional ℚ_[p] ℚ_[p]⟮ζ⟯ := adjoin.finiteDimensional
      (IsIntegral.of_pow hn (by rw [hζn]; exact isIntegral_one))
    exact le_maximalAbelianExtension ℚ_[p]⟮ζ⟯ (mem_adjoin_simple_self ℚ_[p] ζ)

end Padic

end Padic

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.LocalArtinMap
noncomputable section

namespace GroundTheory.LocalField

open Abstract ValuativeRel GroundTheory.LocalField.FormalGroup

theorem continuous_of_isOpen_ker {G D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group D] [TopologicalSpace D] [DiscreteTopology D] (f : G →* D)
    (hf : IsOpen (f.ker : Set G)) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, map_one, nhds_discrete D, Filter.tendsto_pure]
  exact Filter.mem_of_superset (hf.mem_nhds f.ker.one_mem) fun x hx => hx

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Def


variable (K Ω) in
def localArtinMap :
    Kˣ →* (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :=
  (topologicalAbelianizationEquiv K Ω).toMulEquiv.toMonoidHom.comp (localReciprocityLimit K Ω)

theorem localArtinMap_apply (x : Kˣ) :
    localArtinMap K Ω x = topologicalAbelianizationEquiv K Ω (localReciprocityLimit K Ω x) :=
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem restrictAb_topologicalAbelianizationEquiv_eq_abelianRestrict (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsAbelianGalois K L] (g : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) :
    restrictAb L (le_maximalAbelianExtension L) (topologicalAbelianizationEquiv K Ω g) =
      abelianRestrict L g := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
  rw [restrictAb_topologicalAbelianizationEquiv]
  rfl

theorem restrictAb_localArtinMap (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] (x : Kˣ) :
    restrictAb L (le_maximalAbelianExtension L) (localArtinMap K Ω x) =
      (localReciprocityAbelian L).symm (x : Kˣ ⧸ (normUnits K L).range) := by
  rw [localArtinMap_apply, restrictAb_topologicalAbelianizationEquiv_eq_abelianRestrict,
    abelianRestrict_localReciprocityLimit]

theorem ker_restrictAb_localArtinMap (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    ((restrictAb L (le_maximalAbelianExtension L)).comp (localArtinMap K Ω)).ker =
      (normUnits K L).range := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, restrictAb_localArtinMap, MulEquiv.map_eq_one_iff,
    QuotientGroup.eq_one_iff]

theorem surjective_restrictAb_localArtinMap (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    Function.Surjective ((restrictAb L (le_maximalAbelianExtension L)).comp (localArtinMap K Ω)) := by
  intro σ
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (localReciprocityAbelian L σ)
  refine ⟨x, ?_⟩
  rw [MonoidHom.comp_apply, restrictAb_localArtinMap, hx, MulEquiv.symm_apply_apply]

end Def

section Unramified

instance isAbelianGalois_maximalUnramifiedExtension :
    IsAbelianGalois K (maximalUnramifiedExtension K Ω) :=
  { toIsMulCommutative := ⟨⟨fun σ τ => (maximalUnramifiedExtensionGaloisEquiv K Ω).injective (by
      rw [map_mul, map_mul, mul_comm])⟩⟩ }

theorem maximalUnramifiedExtension_le_maximalAbelianExtension :
    maximalUnramifiedExtension K Ω ≤ maximalAbelianExtension K Ω :=
  le_maximalAbelianExtension _

theorem restrictAb_localArtinMap_uniformizer {π : Kˣ} (hπ : ord (π : K) = 1) :
    restrictAb (maximalUnramifiedExtension K Ω) maximalUnramifiedExtension_le_maximalAbelianExtension
      (localArtinMap K Ω π) = maximalUnramifiedExtensionFrobenius K Ω := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (localReciprocityLimit K Ω π)
  rw [localArtinMap_apply, ← hg, restrictAb_topologicalAbelianizationEquiv]
  exact restrictNormal_eq_frobenius_of_mk_eq_localReciprocityLimit hπ hg

theorem restrictAb_localArtinMap_of_le_maximalUnramifiedExtension (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsGalois K L] (hL : L ≤ maximalUnramifiedExtension K Ω) (x : Kˣ) :
    restrictAb L (hL.trans maximalUnramifiedExtension_le_maximalAbelianExtension) (localArtinMap K Ω x) =
      unramifiedFrobenius K Ω L ^ ord (x : K) := by
  have := isAbelianGalois_of_le_maximalAbelianExtension L
    (hL.trans maximalUnramifiedExtension_le_maximalAbelianExtension)
  apply (bijective_abelianizationOf L).1
  rw [restrictAb_localArtinMap, of_localReciprocityAbelian_symm,
    localReciprocity_symm_mk_of_le_maximalUnramifiedExtension L hL, map_zpow]

theorem localArtinMap_uniformizer_apply {π : Kˣ} (hπ : ord (π : K) = 1) {y : Ω}
    (hy : y ∈ maximalUnramifiedExtension K Ω) :
    ((localArtinMap K Ω π ⟨y, maximalUnramifiedExtension_le_maximalAbelianExtension hy⟩ :
      maximalAbelianExtension K Ω) : Ω) =
      (maximalUnramifiedExtensionFrobenius K Ω ⟨y, hy⟩ : Ω) := by
  rw [← restrictAb_localArtinMap_uniformizer hπ, restrictAb_apply]

end Unramified

section Topology

theorem continuous_localArtinMap : Continuous (localArtinMap K Ω) := by
  rw [continuous_iff_restrictAb]
  intro L _ _
  refine continuous_of_isOpen_ker ((restrictAb L (le_maximalAbelianExtension L)).comp
    (localArtinMap K Ω)) ?_
  rw [ker_restrictAb_localArtinMap]
  exact (isOpen_range_normUnits_and_finiteIndex (Ω := Ω) L).1

end Topology

section Injective

theorem eq_one_of_forall_mem_unitFiltration {u : 𝒪[K]ˣ}
    (h : ∀ n, 1 ≤ n → u ∈ unitFiltration K n) : u = 1 := by
  have hmem : (u : 𝒪[K]) - 1 ∈ ⨅ n : ℕ, 𝓂[K] ^ n := by
    refine Ideal.mem_iInf.2 fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact h n hn
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top', Ideal.mem_bot, sub_eq_zero] at hmem
  exact Units.ext hmem

theorem injective_localArtinMap : Function.Injective (localArtinMap K Ω) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hker : x ∈ (localReciprocityLimit K Ω).ker := by
    rw [MonoidHom.mem_ker]
    exact (topologicalAbelianizationEquiv K Ω).injective (by rw [map_one]; exact hx)
  rw [ker_localReciprocityLimit, Subgroup.mem_iInf] at hker
  have hnorm : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L], x ∈ (normUnits K L).range :=
    fun L _ => hker ⟨L, inferInstance⟩
  have hopen : ∀ (H : Subgroup Kˣ) [H.FiniteIndex], IsOpen (H : Set Kˣ) → x ∈ H := by
    intro H _ hH
    obtain ⟨L, hL, -, -, hLH⟩ := exists_range_normUnits_eq (Ω := Ω) H hH
    rw [← hLH]
    exact hnorm L
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set e := unitsEquivIntProd hπ
  have hk : (e x).1 = 1 := by
    set k := Multiplicative.toAdd (e x).1 with hk
    let f : Kˣ →* Multiplicative (ZMod (k.natAbs + 1)) :=
      (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod (k.natAbs + 1)))).comp
        ((MonoidHom.fst _ _).comp e.toMonoidHom)
    have hfo : IsOpen (f.ker : Set Kˣ) := by
      refine Subgroup.isOpen_mono (H₁ := unitFiltrationUnits K 0) ?_ (isOpen_unitFiltrationUnits 0)
      rintro _ ⟨u, -, rfl⟩
      simp [f, e, unitsEquivIntProd_unitsIncl]
    have hfx := hopen f.ker hfo
    rw [MonoidHom.mem_ker] at hfx
    have h0 : ((k : ℤ) : ZMod (k.natAbs + 1)) = 0 := by
      simpa [f, k] using hfx
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    have : k = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h0 (by simp only [Int.natAbs_natCast]; omega)
    rw [← ofAdd_toAdd (e x).1, ← hk, this, ofAdd_zero]
  set u := (e x).2
  have hxu : x = unitsIncl K u := by
    apply e.injective
    rw [unitsEquivIntProd_unitsIncl, ← hk]
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hf := isLubinTateSeries_ltPoly π
  have hu : u = 1 := by
    refine eq_one_of_forall_mem_unitFiltration fun n hn => ?_
    refine mem_unitFiltration_of_mem_range_normUnits (Ω := Ω) hπ hf hn u 0 ?_
    rw [unitUniformizerPow_eq, zpow_zero, one_mul, ← hxu]
    exact hnorm _
  rw [hxu, hu, map_one]

end Injective

end GroundTheory.LocalField
end
end
