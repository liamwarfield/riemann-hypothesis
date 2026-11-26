module

public import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
public import GroundTheory.GlobalFields.IdeleGroups.IndexProductFormula
public import GroundTheory.GlobalFields.KummerTheory.SplittingKummer
public import GroundTheory.GlobalFields.SplittingFromInequality
public import GroundTheory.GlobalFields.SUnits
public import GroundTheory.GlobalFields.KummerTheory.Unramified
public import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups

@[expose] public section

section -- merged from GroundTheory.GlobalFields.KummerTheory.KummerIndexLemma.Places
section -- merged from GroundTheory.GlobalFields.KummerTheory.KummerIndexLemma.PowerPlaces
section -- merged from GroundTheory.GlobalFields.KummerTheory.KummerIndexLemma.HasEnoughRootsOfUnityOfRingHom
noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh WithZero

namespace KummerIndex

theorem hasEnoughRootsOfUnity_of_ringHom {F E : Type*} [Field F] [Field E] (f : F →+* E)
    (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity F n] : HasEnoughRootsOfUnity E n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F n
  exact ⟨⟨f ζ, hζ.map_of_injective f.injective⟩, rootsOfUnity.isCyclic E n⟩

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev localUnits : Subgroup (v.adicCompletion K)ˣ :=
  (Submonoid.ofClass (v.adicCompletionIntegers K)).units


variable {v} in
theorem mem_localUnits_iff {x : (v.adicCompletion K)ˣ} :
    x ∈ localUnits v ↔ Valued.v (x : v.adicCompletion K) = 1 := by
  have hx : Valued.v (x : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  change (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K ↔ _
  rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hx)).1 h2)
  · intro h
    rw [h, inv_one]
    exact ⟨le_rfl, le_rfl⟩

theorem units_map_mem_localUnits {a : Kˣ} (ha : v.valuation K (a : K) = 1) :
    Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) a ∈ localUnits v := by
  rw [mem_localUnits_iff, Units.coe_map]
  change Valued.v ((a : K) : v.adicCompletion K) = 1
  rw [valuedAdicCompletion_eq_valuation', ha]

def localClass (p : ℕ) : Kˣ →* UnitsModPow (v.adicCompletion K) p :=
  (QuotientGroup.mk' (unitsPow (v.adicCompletion K) p)).comp
    (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K))

theorem ker_localClass (p : ℕ) :
    (localClass v p).ker = unitsPowIn K p (v.adicCompletion K) := by
  rw [localClass, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  rfl

def localUnitClasses (p : ℕ) : Subgroup (UnitsModPow (v.adicCompletion K) p) :=
  (localUnits v).map (QuotientGroup.mk' (unitsPow (v.adicCompletion K) p))

theorem localClass_mem_localUnitClasses (p : ℕ) {a : Kˣ} (ha : v.valuation K (a : K) = 1) :
    localClass v p a ∈ localUnitClasses v p :=
  Subgroup.mem_map_of_mem _ (units_map_mem_localUnits v ha)

def ordMod (p : ℕ) : (v.adicCompletion K)ˣ →* Multiplicative (ZMod p) where
  toFun x := Multiplicative.ofAdd (((-log (Valued.v (x : v.adicCompletion K)) : ℤ) : ZMod p))
  map_one' := by simp
  map_mul' x y := by
    have hx : Valued.v (x : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
    have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
    rw [Units.val_mul, map_mul, log_mul hx hy, ← ofAdd_add]
    push_cast
    ring_nf

theorem exists_uniformizer_unit :
    ∃ π : (v.adicCompletion K)ˣ, Valued.v (π : v.adicCompletion K) = exp (-1 : ℤ) := by
  obtain ⟨x, hx⟩ := valued_adicCompletion_surjective (v := v) (K := K) (exp (-1 : ℤ))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact exp_ne_zero hx.symm
  exact ⟨Units.mk0 x hx0, hx⟩

theorem ordMod_surjective (p : ℕ) [NeZero p] : Function.Surjective (ordMod v p) := by
  obtain ⟨π, hπ⟩ := exists_uniformizer_unit v
  intro z
  refine ⟨π ^ (Multiplicative.toAdd z).val, ?_⟩
  change Multiplicative.ofAdd (((-log (Valued.v ((π ^ (Multiplicative.toAdd z).val :
    (v.adicCompletion K)ˣ) : v.adicCompletion K)) : ℤ) : ZMod p)) = z
  rw [Units.val_pow_eq_pow_val, map_pow, hπ, ← exp_nsmul, log_exp]
  simp only [smul_neg, nsmul_eq_mul, mul_one, neg_neg, Int.cast_natCast, ZMod.natCast_zmod_val]
  rfl

theorem ker_ordMod (p : ℕ) [NeZero p] :
    (ordMod v p).ker = localUnits v ⊔ unitsPow (v.adicCompletion K) p := by
  apply le_antisymm
  · intro x hx
    have hx0 : Valued.v (x : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
    rw [MonoidHom.mem_ker] at hx
    change Multiplicative.ofAdd (((-log (Valued.v (x : v.adicCompletion K)) : ℤ) : ZMod p)) = 1
      at hx
    rw [ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨π, hπ⟩ := exists_uniformizer_unit v
    have hu : x * ((π ^ k) ^ p)⁻¹ ∈ localUnits v := by
      rw [mem_localUnits_iff, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
        Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, map_pow, map_zpow₀, hπ,
        ← exp_zsmul, ← exp_nsmul, ← exp_log hx0]
      rw [← exp_neg, ← exp_add]
      have : -(-log (Valued.v (x : v.adicCompletion K))) = (p : ℤ) * (-k) := by
        rw [hk]; ring
      rw [exp_eq_one]
      rw [neg_neg] at this
      rw [this]
      simp only [smul_eq_mul, nsmul_eq_mul]
      ring
    have hx' : x = (x * ((π ^ k) ^ p)⁻¹) * (π ^ k) ^ p := by group
    rw [hx']
    exact Subgroup.mul_mem_sup hu ⟨π ^ k, rfl⟩
  · rw [sup_le_iff]
    constructor
    · intro x hx
      rw [MonoidHom.mem_ker]
      change Multiplicative.ofAdd (((-log (Valued.v (x : v.adicCompletion K)) : ℤ) : ZMod p)) = 1
      rw [(mem_localUnits_iff).1 hx, log_one]
      simp
    · rintro _ ⟨b, rfl⟩
      have hb : Valued.v (b : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 b.ne_zero
      rw [MonoidHom.mem_ker]
      change Multiplicative.ofAdd (((-log (Valued.v (((b ^ p : (v.adicCompletion K)ˣ)) :
        v.adicCompletion K)) : ℤ) : ZMod p)) = 1
      rw [Units.val_pow_eq_pow_val, map_pow, log_pow]
      simp

theorem index_localUnits_sup_unitsPow (p : ℕ) [NeZero p] :
    (localUnits v ⊔ unitsPow (v.adicCompletion K) p).index = p := by
  rw [← ker_ordMod, Subgroup.index_ker, (ordMod v p).range_eq_top_of_surjective
    (ordMod_surjective v p), Subgroup.card_top, Nat.card_eq_fintype_card]
  simp

theorem index_unitsPow (p : ℕ) [NeZero p] [HasEnoughRootsOfUnity K p]
    (hv : (p : 𝓞 K) ∉ v.asIdeal) :
    (unitsPow (v.adicCompletion K) p).index = p ^ 2 := by
  have := hasEnoughRootsOfUnity_of_ringHom (algebraMap K (v.adicCompletion K)) p
  have h := index_range_powMonoidHom_adicCompletion_of_hasEnoughRootsOfUnity v (n := p)
  rw [norm_natCast_adicCompletion_eq_one hv, div_one] at h
  exact_mod_cast h

theorem natCard_localUnitClasses (p : ℕ) [NeZero p] [HasEnoughRootsOfUnity K p]
    (hv : (p : 𝓞 K) ∉ v.asIdeal) : Nat.card (localUnitClasses v p) = p := by
  have hidx : (localUnitClasses v p).index = p := by
    rw [localUnitClasses, Subgroup.index_map, QuotientGroup.ker_mk',
      (QuotientGroup.mk' _).range_eq_top_of_surjective (QuotientGroup.mk'_surjective _),
      Subgroup.index_top, mul_one, index_localUnits_sup_unitsPow]
  have hcard : Nat.card (UnitsModPow (v.adicCompletion K) p) = p ^ 2 :=
    index_unitsPow v p hv
  have h := Subgroup.card_mul_index (localUnitClasses v p)
  rw [hidx, hcard, pow_two] at h
  exact Nat.eq_of_mul_eq_mul_right (NeZero.pos p) h

theorem exists_mul_zpow_inv_mem_unitsPow (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity K p]
    (hv : (p : 𝓞 K) ∉ v.asIdeal) {a x : (v.adicCompletion K)ˣ} (ha : a ∈ localUnits v)
    (hx : x ∈ localUnits v) (hap : a ∉ unitsPow (v.adicCompletion K) p) :
    ∃ k : ℤ, x * (a ^ k)⁻¹ ∈ unitsPow (v.adicCompletion K) p := by
  let g : localUnitClasses v p := ⟨QuotientGroup.mk' _ a, Subgroup.mem_map_of_mem _ ha⟩
  let g' : localUnitClasses v p := ⟨QuotientGroup.mk' _ x, Subgroup.mem_map_of_mem _ hx⟩
  have hg : g ≠ 1 := by
    intro h
    apply hap
    have h' : QuotientGroup.mk' (unitsPow (v.adicCompletion K) p) a = 1 := congrArg Subtype.val h
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (mem_zpowers_of_prime_card (natCard_localUnitClasses v p hv) hg (g' := g'))
  refine ⟨k, ?_⟩
  have h' : QuotientGroup.mk' (unitsPow (v.adicCompletion K) p) a ^ k =
      QuotientGroup.mk' (unitsPow (v.adicCompletion K) p) x := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_zpow] at this
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
  change QuotientGroup.mk' _ x * (QuotientGroup.mk' _ a ^ k)⁻¹ = 1
  rw [h']
  exact mul_inv_cancel _

end KummerIndex

end GroundTheory.Global
end
end

noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh Module
  Filter IntermediateField AdeleBaseChange

namespace KummerIndex

section Radical

variable (K : Type*) [Field K] (p : ℕ)

def radicalGroup (y : Kˣ) : Subgroup Kˣ :=
  Subgroup.zpowers y ⊔ unitsPow K p

variable {K p}

theorem unitsPow_le_radicalGroup (y : Kˣ) : unitsPow K p ≤ radicalGroup K p y :=
  le_sup_right

theorem mem_radicalGroup_self (y : Kˣ) : y ∈ radicalGroup K p y :=
  le_sup_left (a := Subgroup.zpowers y) (Subgroup.mem_zpowers y)

theorem radicalGroup_le {y : Kˣ} {H : Subgroup Kˣ} (hy : y ∈ H) (hH : unitsPow K p ≤ H) :
    radicalGroup K p y ≤ H :=
  sup_le ((Subgroup.zpowers_le).2 hy) hH

theorem radicalClasses_radicalGroup (y : Kˣ) :
    radicalClasses K p (radicalGroup K p y) =
      Subgroup.zpowers (QuotientGroup.mk' (unitsPow K p) y) := by
  rw [radicalClasses, radicalGroup, Subgroup.map_sup, MonoidHom.map_zpowers,
    QuotientGroup.map_mk'_self, sup_bot_eq]

theorem natCard_radicalQuotient (y : Kˣ) :
    Nat.card (radicalGroup K p y ⧸ (unitsPow K p).subgroupOf (radicalGroup K p y)) =
      orderOf (QuotientGroup.mk' (unitsPow K p) y) := by
  rw [Nat.card_congr (radicalQuotientEquiv K p _).toEquiv, radicalClasses_radicalGroup,
    Nat.card_zpowers]

instance finite_radicalQuotient [NeZero p] (y : Kˣ) :
    Finite (radicalGroup K p y ⧸ (unitsPow K p).subgroupOf (radicalGroup K p y)) := by
  apply Nat.finite_of_card_ne_zero
  rw [natCard_radicalQuotient]
  exact (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
    ⟨p, NeZero.pos p, UnitsModPow.pow_eq_one _ _ _⟩)).ne'

theorem natCard_radicalQuotient_of_not_mem [Fact p.Prime] {y : Kˣ} (hy : y ∉ unitsPow K p) :
    Nat.card (radicalGroup K p y ⧸ (unitsPow K p).subgroupOf (radicalGroup K p y)) = p := by
  rw [natCard_radicalQuotient]
  refine orderOf_eq_prime (UnitsModPow.pow_eq_one _ _ _) ?_
  rwa [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

variable [Fact p.Prime] [HasEnoughRootsOfUnity K p] (Ω : Type*) [Field Ω] [Algebra K Ω]
  [IsSepClosed Ω]

theorem finrank_kummerExtension_radicalGroup {y : Kˣ} (hy : y ∉ unitsPow K p) :
    finrank K (kummerExtension K p Ω (radicalGroup K p y)) = p := by
  rw [finrank_kummerExtension, natCard_radicalQuotient_of_not_mem hy]

theorem isCyclic_kummerExtension_radicalGroup {y : Kˣ} (hy : y ∉ unitsPow K p) :
    IsCyclic Gal(kummerExtension K p Ω (radicalGroup K p y)/K) :=
  isCyclic_of_prime_card (p := p) (by
    rw [IsGalois.card_aut_eq_finrank, finrank_kummerExtension_radicalGroup Ω hy])

theorem unitsPowIn_kummerExtension_radicalGroup (y : Kˣ) :
    unitsPowIn K p (kummerExtension K p Ω (radicalGroup K p y)) = radicalGroup K p y :=
  unitsPowIn_kummerExtension K p Ω _ (unitsPow_le_radicalGroup y)

theorem exists_pow_eq_kummerExtension_radicalGroup (y : Kˣ) :
    ∃ α : kummerExtension K p Ω (radicalGroup K p y), α ^ p = algebraMap K _ (y : K) := by
  have h := mem_radicalGroup_self (p := p) y
  rw [← unitsPowIn_kummerExtension_radicalGroup Ω y] at h
  exact mem_unitsPowIn.1 h

end Radical

section Place

open SemiLocal

universe u

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity K p]

theorem _root_.GroundTheory.Global.FirstInequality.exists_place_mem_unitsPowIn_not_mem
    (hFI : FirstInequality.{u}) {a x : Kˣ} (hx : x ∉ radicalGroup K p a)
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite)
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (haS : ∀ v ∉ S, v.valuation K (a : K) = 1) (hxS : ∀ v ∉ S, v.valuation K (x : K) = 1) :
    ∃ v ∉ S, a ∈ unitsPowIn K p (v.adicCompletion K) ∧
      x ∉ unitsPowIn K p (v.adicCompletion K) := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  let Ω := AlgebraicClosure K
  let L := kummerExtension K p Ω (radicalGroup K p a)
  have hL : unitsPowIn K p L = radicalGroup K p a :=
    unitsPowIn_kummerExtension_radicalGroup Ω a
  obtain ⟨α, hα⟩ := exists_pow_eq_kummerExtension_radicalGroup (p := p) Ω a
  have : HasEnoughRootsOfUnity L p := hasEnoughRootsOfUnity_of_ringHom (algebraMap K L) p
  let xL : Lˣ := Units.map (algebraMap K L : K →* L) x
  have hxL : xL ∉ unitsPow L p := by
    intro h
    apply hx
    rw [← hL]
    exact Subgroup.mem_comap.2 h
  let L' := kummerExtension L p (AlgebraicClosure L) (radicalGroup L p xL)
  have hfin : finrank L L' = p := finrank_kummerExtension_radicalGroup _ hxL
  have : IsCyclic Gal(L'/L) := isCyclic_kummerExtension_radicalGroup _ hxL
  suffices h : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite, SplitsCompletely L' w by
    have h1 := hFI.finrank_eq_one_of_eventually_splitsCompletely h
    rw [hfin] at h1
    exact (Fact.out : p.Prime).one_lt.ne' h1
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite, below K w ∉ S :=
    tendsto_below.eventually hS.eventually_cofinite_notMem
  filter_upwards [hev] with w hw
  rw [splitsCompletely_kummerExtension_iff]
  suffices key : xL ∈ unitsPowIn L p (w.adicCompletion L) by
    intro c hc
    exact mem_unitsPowIn.1 (radicalGroup_le key (unitsPow_le_unitsPowIn L p _) hc)
  set v := below K w
  have hpv : (p : 𝓞 K) ∉ v.asIdeal := fun h ↦ hw (hpS v h)
  let ιK : Kˣ →* (w.adicCompletion L)ˣ := Units.map (algebraMap K (w.adicCompletion L) : K →* _)
  let ιv : (v.adicCompletion K)ˣ →* (w.adicCompletion L)ˣ :=
    Units.map (algebraMap (v.adicCompletion K) (w.adicCompletion L) : _ →* _)
  let κ : Kˣ →* (v.adicCompletion K)ˣ := Units.map (algebraMap K (v.adicCompletion K) : K →* _)
  have hικ (z : Kˣ) : ιv (κ z) = ιK z := by
    apply Units.ext
    simp only [ιv, ιK, κ, Units.coe_map, MonoidHom.coe_coe]
    exact (IsScalarTower.algebraMap_apply K (v.adicCompletion K) (w.adicCompletion L) _).symm
  have hxLw : ((ιK x : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
      algebraMap L (w.adicCompletion L) (xL : L) := by
    simp only [ιK, xL, Units.coe_map, MonoidHom.coe_coe]
    exact IsScalarTower.algebraMap_apply K L (w.adicCompletion L) _
  suffices h : ιK x ∈ unitsPow (w.adicCompletion L) p by
    obtain ⟨b, hb⟩ := mem_unitsPow.1 h
    refine mem_unitsPowIn.2 ⟨b, ?_⟩
    rw [← hxLw, ← hb, Units.val_pow_eq_pow_val]
  by_cases ha : a ∈ unitsPowIn K p (v.adicCompletion K)
  · obtain ⟨b, hb⟩ := mem_unitsPow.1 (Subgroup.mem_comap.1 (hcon v hw ha))
    refine mem_unitsPow.2 ⟨ιv b, ?_⟩
    rw [← map_pow, hb]
    exact hικ x
  · have ha' : κ a ∉ unitsPow (v.adicCompletion K) p := fun h ↦ ha (Subgroup.mem_comap.2 h)
    obtain ⟨k, hk⟩ := exists_mul_zpow_inv_mem_unitsPow v p hpv
      (units_map_mem_localUnits v (haS v hw)) (units_map_mem_localUnits v (hxS v hw)) ha'
    obtain ⟨b, hb⟩ := mem_unitsPow.1 hk
    have hα0 : algebraMap L (w.adicCompletion L) (α : L) ≠ 0 := by
      rw [ne_eq, map_eq_zero]
      intro h0
      have h1 : (α : kummerExtension K p Ω (radicalGroup K p a)) = 0 := h0
      rw [h1, zero_pow (Fact.out : p.Prime).ne_zero, eq_comm, map_eq_zero] at hα
      exact a.ne_zero hα
    let αw : (w.adicCompletion L)ˣ := Units.mk0 _ hα0
    have hαw : αw ^ p = ιK a := by
      apply Units.ext
      simp only [αw, ιK, Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map, MonoidHom.coe_coe]
      rw [← map_pow]
      change algebraMap L (w.adicCompletion L) ((α ^ p : kummerExtension K p Ω _) : L) = _
      rw [hα, IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
    refine mem_unitsPow.2 ⟨ιv b * αw ^ k, ?_⟩
    have hb' : ιv b ^ p = ιK x * (ιK a ^ k)⁻¹ := by
      rw [← map_pow, hb, map_mul, map_inv, map_zpow, hικ, hικ]
    have hαk : (αw ^ k) ^ p = ιK a ^ k := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hαw]
    rw [mul_pow, hb', hαk, inv_mul_cancel_right]

end Place

end KummerIndex

end GroundTheory.Global
end
end

noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh

namespace KummerIndex

variable {K : Type*} [Field K] [NumberField K]

def unitsPowAt (p : ℕ) (T : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup Kˣ :=
  ⨅ v ∈ T, unitsPowIn K p (v.adicCompletion K)

theorem mem_unitsPowAt {p : ℕ} {T : Finset (HeightOneSpectrum (𝓞 K))} {x : Kˣ} :
    x ∈ unitsPowAt p T ↔ ∀ v ∈ T, x ∈ unitsPowIn K p (v.adicCompletion K) := by
  simp only [unitsPowAt, Subgroup.mem_iInf]

theorem unitsPowAt_empty (p : ℕ) : unitsPowAt (K := K) p ∅ = ⊤ := by
  ext x
  simp [mem_unitsPowAt]

theorem unitsPowAt_insert [DecidableEq (HeightOneSpectrum (𝓞 K))] (p : ℕ)
    (v : HeightOneSpectrum (𝓞 K)) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    unitsPowAt p (insert v T) = unitsPowIn K p (v.adicCompletion K) ⊓ unitsPowAt p T := by
  ext x
  simp only [mem_unitsPowAt, Finset.mem_insert, forall_eq_or_imp, Subgroup.mem_inf]

theorem unitsPow_le_unitsPowAt (p : ℕ) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    unitsPow K p ≤ unitsPowAt p T := fun _ hx ↦
  mem_unitsPowAt.2 fun _ _ ↦ unitsPow_le_unitsPowIn K p _ hx

variable {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity K p]

theorem exists_localClass_eq (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hpT : ∀ v ∈ T, (p : 𝓞 K) ∉ v.asIdeal)
    (hidx : (unitsPowAt p T).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) =
      p ^ T.card)
    (z : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
    (hz : ∀ v ∈ T, z v ∈ localUnits v) :
    ∃ δ ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, ∀ v ∈ T,
      localClass v p δ = QuotientGroup.mk (z v) := by
  classical
  set Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  have hvS : ∀ v ∈ T, v ∉ (S : Set (HeightOneSpectrum (𝓞 K))) := fun v hv hvS ↦
    Finset.disjoint_left.1 hST (Finset.mem_coe.1 hvS) hv
  let _ : ∀ v : T, Group (UnitsModPow (v.1.adicCompletion K) p) := fun _ ↦ inferInstance
  let ψ : Δ →* ((v : T) → UnitsModPow (v.1.adicCompletion K) p) :=
    MonoidHom.pi fun v ↦ (localClass v.1 p).comp Δ.subtype
  have hker : ψ.ker = (unitsPowAt p T).subgroupOf Δ := by
    ext δ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_unitsPowAt, funext_iff]
    constructor
    · intro h v hv
      rw [← ker_localClass]
      exact h ⟨v, hv⟩
    · intro h v
      have := h v.1 v.2
      rw [← ker_localClass] at this
      exact this
  let U : Subgroup ((v : T) → UnitsModPow (v.1.adicCompletion K) p) :=
    Subgroup.pi Set.univ fun v ↦ localUnitClasses v.1 p
  have hU : Nat.card U = p ^ T.card := by
    have e : U ≃ ∀ v : T, localUnitClasses v.1 p :=
      (Equiv.subtypeEquivRight fun f ↦ by simp [U, Subgroup.mem_pi]).trans
        (Equiv.subtypePiEquivPi)
    rw [Nat.card_congr e, Nat.card_pi,
      Finset.prod_congr rfl fun v _ ↦ natCard_localUnitClasses v.1 p (hpT v.1 v.2),
      Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  have hrange : Nat.card ψ.range = p ^ T.card := by
    rw [← Subgroup.index_ker, hker, ← Subgroup.relIndex, hidx]
  have hle : ψ.range ≤ U := by
    rintro _ ⟨δ, rfl⟩
    rw [Subgroup.mem_pi]
    intro v _
    exact localClass_mem_localUnitClasses v.1 p (Set.unit_valuation_eq_one (S := (S : Set (HeightOneSpectrum (𝓞 K)))) (K := K) δ (hvS v.1 v.2))
  have : Finite U := Nat.finite_of_card_ne_zero (by
    rw [hU]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have heq : ψ.range = U := Subgroup.eq_of_le_of_card_ge hle (by rw [hU, hrange])
  have hf : (fun v : T ↦ (QuotientGroup.mk (z v.1) : UnitsModPow (v.1.adicCompletion K) p)) ∈
      ψ.range := by
    rw [heq, Subgroup.mem_pi]
    intro v _
    exact Subgroup.mem_map_of_mem _ (hz v.1 v.2)
  obtain ⟨δ, hδ⟩ := hf
  refine ⟨δ, δ.2, fun v hv ↦ ?_⟩
  exact congrFun hδ ⟨v, hv⟩

universe u

variable {K : Type u} [Field K] [NumberField K] [HasEnoughRootsOfUnity K p]


omit [Fact p.Prime] [HasEnoughRootsOfUnity K p] in
theorem valuation_eq_one_of_mem_unit {S : Set (HeightOneSpectrum (𝓞 K))} {x : Kˣ}
    (hx : x ∈ S.unit K) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    v.valuation K (x : K) = 1 :=
  Set.unit_valuation_eq_one (S := S) (K := K) ⟨x, hx⟩ hv


omit [HasEnoughRootsOfUnity K p] in
theorem relIndex_unitsPow_sUnit_ne_zero (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (unitsPow K p).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) ≠ 0 := by
  set Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  have hfi := Subgroup.finiteIndex_range_powMonoidHom_of_fg Δ (Fact.out : p.Prime).ne_zero
  have hle : (powMonoidHom p : Δ →* Δ).range ≤ (unitsPow K p).subgroupOf Δ := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨(y : Kˣ), rfl⟩
  exact fun h ↦ hfi.index_ne_zero (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hle))

theorem _root_.GroundTheory.Global.FirstInequality.exists_place_relIndex_unitsPowAt_insert
    (hFI : FirstInequality.{u}) [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S) {a : Kˣ}
    (ha : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) {T : Finset (HeightOneSpectrum (𝓞 K))}
    (hidx : (unitsPowAt p T).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) =
      p ^ T.card)
    {x : Kˣ} (hxΔ : x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hxT : x ∈ unitsPowAt p T)
    (hxa : x ∉ radicalGroup K p a) :
    ∃ v, v ∉ S ∧ v ∉ T ∧ a ∈ unitsPowIn K p (v.adicCompletion K) ∧
      (unitsPowAt p (insert v T)).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) =
        p ^ (T.card + 1) := by
  set Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  have hfin : ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).Finite :=
    (S.finite_toSet).union T.finite_toSet
  obtain ⟨v, hv, hav, hxv⟩ := hFI.exists_place_mem_unitsPowIn_not_mem hxa hfin
    (fun v hv ↦ Or.inl (hpS v hv))
    (fun v hv ↦ valuation_eq_one_of_mem_unit ha (fun h ↦ hv (Or.inl h)))
    (fun v hv ↦ valuation_eq_one_of_mem_unit hxΔ (fun h ↦ hv (Or.inl h)))
  have hvS : v ∉ S := fun h ↦ hv (Or.inl h)
  have hvT : v ∉ T := fun h ↦ hv (Or.inr h)
  refine ⟨v, hvS, hvT, hav, ?_⟩
  have hpv : (p : 𝓞 K) ∉ v.asIdeal := fun h ↦ hvS (hpS v h)
  rw [unitsPowAt_insert, ← Subgroup.relIndex_inf_mul_relIndex, hidx, pow_succ, mul_comm]
  congr 1
  rw [← ker_localClass, Subgroup.relIndex_ker]
  set H := (unitsPowAt p T ⊓ Δ).map (localClass v p)
  have hle : H ≤ localUnitClasses v p := by
    rintro _ ⟨y, hy, rfl⟩
    exact localClass_mem_localUnitClasses v p (valuation_eq_one_of_mem_unit hy.2 hvS)
  have hdvd : Nat.card H ∣ p := by
    have := Subgroup.card_dvd_of_le hle
    rwa [natCard_localUnitClasses v p hpv] at this
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h1 | hp
  · exfalso
    have hbot := Subgroup.card_eq_one.1 h1
    have hmem : localClass v p x ∈ H := Subgroup.mem_map_of_mem _ ⟨hxT, hxΔ⟩
    rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_localClass] at hmem
    exact hxv hmem
  · exact hp

theorem _root_.GroundTheory.Global.FirstInequality.exists_places_unitsPowAt
    (hFI : FirstInequality.{u}) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S) {a : Kˣ}
    (ha : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint S T ∧
      (∀ v ∈ T, a ∈ unitsPowIn K p (v.adicCompletion K)) ∧
      (unitsPowAt p T).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) = p ^ T.card ∧
      ∀ x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, x ∈ unitsPowAt p T →
        x ∈ radicalGroup K p a := by
  classical
  set Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  let Good : Finset (HeightOneSpectrum (𝓞 K)) → Prop := fun T ↦ Disjoint S T ∧
    (∀ v ∈ T, a ∈ unitsPowIn K p (v.adicCompletion K)) ∧
    (unitsPowAt p T).relIndex Δ = p ^ T.card
  have key : ∀ n : ℕ, ∃ T, Good T ∧
      (n ≤ T.card ∨ ∀ x ∈ Δ, x ∈ unitsPowAt p T → x ∈ radicalGroup K p a) := by
    intro n
    induction n with
    | zero =>
      refine ⟨∅, ⟨Finset.disjoint_empty_right S, by simp, ?_⟩, Or.inl le_rfl⟩
      rw [unitsPowAt_empty, Subgroup.relIndex_top_left, Finset.card_empty, pow_zero]
    | succ n ih =>
      obtain ⟨T, hT, h | h⟩ := ih
      · by_cases hfin : ∀ x ∈ Δ, x ∈ unitsPowAt p T → x ∈ radicalGroup K p a
        · exact ⟨T, hT, Or.inr hfin⟩
        · simp only [not_forall, exists_prop] at hfin
          obtain ⟨x, hxΔ, hxT, hxa⟩ := hfin
          obtain ⟨v, hvS, hvT, hav, hidx⟩ :=
            hFI.exists_place_relIndex_unitsPowAt_insert S hpS ha hT.2.2 hxΔ hxT hxa
          refine ⟨insert v T, ⟨?_, ?_, ?_⟩, Or.inl ?_⟩
          · exact Finset.disjoint_insert_right.2 ⟨hvS, hT.1⟩
          · intro w hw
            rcases Finset.mem_insert.1 hw with rfl | hw
            · exact hav
            · exact hT.2.1 w hw
          · rw [Finset.card_insert_of_notMem hvT, hidx]
          · rw [Finset.card_insert_of_notMem hvT]
            omega
      · exact ⟨T, hT, Or.inr h⟩
  set B := (unitsPow K p).relIndex Δ
  have hB : B ≠ 0 := relIndex_unitsPow_sUnit_ne_zero S
  obtain ⟨T, hT, h | h⟩ := key B
  · exfalso
    have hdvd : p ^ T.card ∣ B :=
      hT.2.2 ▸ Subgroup.relIndex_dvd_of_le_left Δ (unitsPow_le_unitsPowAt p T)
    have h1 : p ^ T.card ≤ B := Nat.le_of_dvd (Nat.pos_of_ne_zero hB) hdvd
    have h2 : T.card < p ^ T.card := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
    omega
  · exact ⟨T, hT.1, hT.2.1, hT.2.2, h⟩

end KummerIndex

end GroundTheory.Global
end
end

noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh Module
  Filter IntermediateField AdeleBaseChange SemiLocal IdeleNorm

open scoped NumberField.LiesOver

namespace KummerIndex

section LocalNorms

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem finiteProj_mem_localUnits {v : HeightOneSpectrum (𝓞 K)} {x : IdeleGroup K}
    (h : IdeleGroup.ord v x = 0) : IdeleGroup.finiteProj v x ∈ localUnits v := by
  have hx := (IdeleGroup.ord_eq_zero_iff v x).1 h
  rw [localUnits, Submonoid.mem_units_iff]
  have h2 : ((IdeleGroup.finiteProj v x)⁻¹ : (v.adicCompletion K)ˣ) =
      IdeleGroup.finiteProj v x⁻¹ := (map_inv _ _).symm
  rw [h2, IdeleGroup.coe_finiteProj, IdeleGroup.coe_finiteProj]
  exact hx

theorem pow_finrank_mem_range_finiteLocalNorm (v : HeightOneSpectrum (𝓞 K))
    (b : (v.adicCompletion K)ˣ) : b ^ finrank K L ∈ (finiteLocalNorm L v).range := by
  classical
  let y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ := fun w ↦
    Units.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) :
      v.adicCompletion K →* w.1.adicCompletion L) b
  refine ⟨y, ?_⟩
  rw [← Finset.univ_prod_mulSingle y, map_prod]
  simp_rw [y, finiteLocalNorm_mulSingle_algebraMap]
  rw [Finset.prod_pow_eq_pow_sum, sum_finrank_eq]

theorem range_infiniteLocalNorm_eq_top_of_splitsCompletely (w : InfinitePlace K)
    (h : InfinitePlace.SplitsCompletely L w) : (infiniteLocalNorm L w).range = ⊤ := by
  classical
  rw [eq_top_iff]
  intro u _
  obtain ⟨w'⟩ := nonempty_infinitePlacesOver L w
  have hd := (InfinitePlace.splitsCompletely_iff_forall_finrank w).1 h w'
  refine ⟨Pi.mulSingle w' (Units.map (algebraMap w.Completion
    (w' : InfinitePlace L).Completion : w.Completion →* (w' : InfinitePlace L).Completion) u), ?_⟩
  rw [infiniteLocalNorm_mulSingle]
  apply Units.ext
  simp [LocalField.normUnits, Algebra.norm_algebraMap, hd]

end LocalNorms

universe u

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity K p]

theorem _root_.GroundTheory.Global.FirstInequality.mem_unitsPow_of_forall_mem_unitsPowIn
    (hFI : FirstInequality.{u}) (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hS : (IdeleGroup.diagonal K).range ⊔
      IdeleGroup.sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤)
    (hsurj : ∀ z : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ,
      (∀ v ∈ T, z v ∈ localUnits v) → ∃ δ ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
        ∀ v ∈ T, localClass v p δ = QuotientGroup.mk (z v))
    {y : Kˣ}
    (hyE : y ∈ ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ (T : Set (HeightOneSpectrum (𝓞 K)))).unit K)
    (hyS : ∀ v ∈ S, y ∈ unitsPowIn K p (v.adicCompletion K))
    (hyinf : ∀ w : InfinitePlace K, y ∈ unitsPowIn K p w.Completion) :
    y ∈ unitsPow K p := by
  classical
  by_contra hy
  let Ω := AlgebraicClosure K
  let F := kummerExtension K p Ω (radicalGroup K p y)
  have hfinF : finrank K F = p := finrank_kummerExtension_radicalGroup Ω hy
  have : IsCyclic Gal(F/K) := isCyclic_kummerExtension_radicalGroup Ω hy
  obtain ⟨α, hα⟩ := exists_pow_eq_kummerExtension_radicalGroup (p := p) Ω y
  have hgen : IntermediateField.adjoin K {α} = ⊤ := by
    have hdvd : finrank K (IntermediateField.adjoin K {α}) ∣ p := by
      have := IntermediateField.finrank_dvd_of_le_right (K := K)
        (le_top : IntermediateField.adjoin K {α} ≤ ⊤)
      rwa [IntermediateField.finrank_top', hfinF] at this
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h1 | hpp
    · exfalso
      rw [IntermediateField.finrank_eq_one_iff] at h1
      have hmem : α ∈ (⊥ : IntermediateField K F) :=
        h1 ▸ IntermediateField.mem_adjoin_simple_self K α
      obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hmem
      have hcp : c ^ p = (y : K) := by
        apply (algebraMap K F).injective
        rw [map_pow, hc, hα]
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_pow (Fact.out : p.Prime).ne_zero] at hcp
        exact y.ne_zero hcp.symm
      exact hy (mem_unitsPow.2 ⟨Units.mk0 c hc0, Units.ext (by simp [hcp])⟩)
    · exact IntermediateField.eq_of_le_of_finrank_eq le_top
        (by rw [hpp, IntermediateField.finrank_top', hfinF])
  suffices h : (ideleNorm K F).range ⊔ (IdeleGroup.diagonal K).range = ⊤ by
    have h1 := hFI.finrank_eq_one_of_sup_eq_top h
    rw [hfinF] at h1
    exact (Fact.out : p.Prime).one_lt.ne' h1
  have hsplit : ∀ v ∈ S, (finiteLocalNorm F v).range = ⊤ := fun v hv ↦
    range_finiteLocalNorm_eq_top_of_isFiniteSplit v ((splitsCompletely_iff_isFiniteSplit v).1
      ((splitsCompletely_kummerExtension_iff v).2 fun c hc ↦
        mem_unitsPowIn.1 (radicalGroup_le (hyS v hv) (unitsPow_le_unitsPowIn K p _) hc)))
  have hinf : ∀ w, (infiniteLocalNorm F w).range = ⊤ := fun w ↦
    range_infiniteLocalNorm_eq_top_of_splitsCompletely w
      ((InfinitePlace.splitsCompletely_kummerExtension_iff w).2 fun c hc ↦
        mem_unitsPowIn.1 (radicalGroup_le (hyinf w) (unitsPow_le_unitsPowIn K p _) hc))
  have hunr : ∀ v, v ∉ S → v ∉ T →
      (integerUnitsOver F v).map (finiteLocalNorm F v) = localUnits v := by
    intro v hvS hvT
    obtain ⟨w⟩ := nonempty_placesOver F v
    have := w.1.isPrime
    refine map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w ?_
    refine Kummer.ramificationIdx_eq_one_of_pow_eq y hα hgen v (fun h ↦ hvS (hpS v h)) ?_
      w.1.asIdeal
    rw [valuation_eq_one_of_mem_unit hyE (by simp [hvS, hvT]), WithZero.log_one]
    exact dvd_zero _
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, s, hs, rfl⟩ := IdeleGroup.exists_diagonal_mul_of_sup_eq_top _ hS x
  have hsv : ∀ v ∉ S, IdeleGroup.finiteProj v s ∈ localUnits v := fun v hv ↦
    finiteProj_mem_localUnits ((IdeleGroup.mem_sIdeles _).1 hs v (by simpa using hv))
  obtain ⟨δ, hδ, hδT⟩ := hsurj (fun v ↦ IdeleGroup.finiteProj v s)
    (fun v hv ↦ hsv v (Finset.disjoint_right.1 hST hv))
  set t := IdeleGroup.diagonal K δ⁻¹ * s with ht_def
  have hloc : ∀ v, v ∉ S → IdeleGroup.finiteProj v t ∈ localUnits v := by
    intro v hvS
    rw [ht_def, map_mul, IdeleGroup.finiteProj_diagonal]
    exact mul_mem (units_map_mem_localUnits v (valuation_eq_one_of_mem_unit (inv_mem hδ)
      (by simpa using hvS))) (hsv v hvS)
  have ht : t ∈ (ideleNorm K F).range := by
    rw [mem_range_ideleNorm_iff]
    refine ⟨fun v ↦ ?_, fun w ↦ by rw [hinf w]; exact Subgroup.mem_top _, ?_⟩
    · by_cases hvS : v ∈ S
      · rw [hsplit v hvS]
        exact Subgroup.mem_top _
      by_cases hvT : v ∈ T
      · have hpow : IdeleGroup.finiteProj v t ∈ unitsPow (v.adicCompletion K) p := by
          rw [ht_def, map_mul, IdeleGroup.finiteProj_diagonal, map_inv]
          exact QuotientGroup.eq.1 (hδT v hvT)
        obtain ⟨b, hb⟩ := mem_unitsPow.1 hpow
        have hnorm := pow_finrank_mem_range_finiteLocalNorm (L := F) v b
        rw [hfinF, hb] at hnorm
        exact hnorm
      · exact Subgroup.map_le_range _ _ (hunr v hvS hvT ▸ hloc v hvS)
    · filter_upwards [(S.finite_toSet.union T.finite_toSet).eventually_cofinite_notMem] with v hv
      simp only [Set.mem_union, Finset.mem_coe, not_or] at hv
      rw [hunr v hv.1 hv.2]
      exact hloc v hv.1
  have hs_eq : s = t * IdeleGroup.diagonal K δ := by
    rw [ht_def, map_inv, mul_comm, mul_inv_cancel_left]
  rw [hs_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨a, rfl⟩)
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right ⟨δ, rfl⟩))

end KummerIndex

end GroundTheory.Global
