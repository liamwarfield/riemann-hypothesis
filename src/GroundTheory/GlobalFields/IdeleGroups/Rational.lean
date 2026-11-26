module

public import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups
public import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import GroundTheory.GlobalFields.Adele.Compact

@[expose] public section

section -- merged from GroundTheory.GlobalFields.IdeleGroups.Rational
namespace GroundTheory.Global

open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing

noncomputable section

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

namespace RationalIdeles

open IdeleGroup

theorem isReal_infinitePlace (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

def realEquiv : InfiniteAdeleRing ℚ ≃+* ℝ :=
  (RingEquiv.piUnique fun w : InfinitePlace ℚ ↦ w.Completion).trans
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_infinitePlace default))

theorem realEquiv_apply (x : InfiniteAdeleRing ℚ) :
    realEquiv x = InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (isReal_infinitePlace default) (x default) :=
  rfl

theorem continuous_realEquiv : Continuous realEquiv :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous.comp
    (continuous_apply _)

theorem continuous_realEquiv_symm : Continuous realEquiv.symm := by
  exact continuous_equiv_symm_of_eq realEquiv.toEquiv
    ((Homeomorph.piUnique fun w : InfinitePlace ℚ ↦ w.Completion).trans
      (InfinitePlace.Completion.isometryEquivRealOfIsReal
        (isReal_infinitePlace default)).toHomeomorph)
    fun _ ↦ rfl

def realUnitsEquiv : (InfiniteAdeleRing ℚ)ˣ ≃ₜ* ℝˣ :=
  unitsContinuousMulEquiv realEquiv.toMulEquiv continuous_realEquiv continuous_realEquiv_symm

def realPart : IdeleGroup ℚ →* ℝˣ :=
  realUnitsEquiv.toMulEquiv.toMonoidHom.comp (toInfinite ℚ)

theorem coe_realPart (x : IdeleGroup ℚ) : (realPart x : ℝ) = realEquiv (x : 𝔸[ℚ]).1 :=
  rfl

theorem continuous_realPart : Continuous realPart :=
  realUnitsEquiv.continuous.comp (continuous_toInfinite ℚ)

@[simp]
theorem realPart_diagonal (a : ℚˣ) : (realPart (diagonal ℚ a) : ℝ) = a := by
  rw [coe_realPart, coe_diagonal]
  exact eq_ratCast (realEquiv.toRingHom.comp (algebraMap ℚ (InfiniteAdeleRing ℚ))) a

theorem realPart_ofIntegerUnits (a : (InfiniteAdeleRing ℚ)ˣ)
    (u : Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) :
    realPart (ofIntegerUnits a u) = realUnitsEquiv a :=
  rfl

def positiveSubgroup : Subgroup (IdeleGroup ℚ) :=
  standardOpenSubgroup ℚ ⊓ (Units.posSubgroup ℝ).comap realPart

theorem mem_positiveSubgroup {x : IdeleGroup ℚ} :
    x ∈ positiveSubgroup ↔ x ∈ standardOpenSubgroup ℚ ∧ 0 < (realPart x : ℝ) := by
  rw [positiveSubgroup, Subgroup.mem_inf, Subgroup.mem_comap, Units.mem_posSubgroup]

theorem isOpen_positiveSubgroup : IsOpen (positiveSubgroup : Set (IdeleGroup ℚ)) := by
  have h : (positiveSubgroup : Set (IdeleGroup ℚ)) =
      (standardOpenSubgroup ℚ : Set (IdeleGroup ℚ)) ∩ {x | 0 < (realPart x : ℝ)} := by
    ext x
    exact mem_positiveSubgroup
  rw [h]
  exact (isOpen_standardOpenSubgroup ℚ).inter
    (isOpen_lt continuous_const (Units.continuous_val.comp continuous_realPart))

theorem diagonal_mem_standardOpenSubgroup_iff (a : ℚˣ) :
    diagonal ℚ a ∈ standardOpenSubgroup ℚ ↔ (a : ℚ) = 1 ∨ (a : ℚ) = -1 := by
  rw [← ker_toFractionalIdeal, MonoidHom.mem_ker, toFractionalIdeal_diagonal,
    toPrincipalIdeal_eq_iff, Units.val_one, ← FractionalIdeal.spanSingleton_one,
    FractionalIdeal.spanSingleton_eq_spanSingleton]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : ((z : 𝓞 ℚ) : ℚ) * a = 1 := by
      rw [Units.smul_def, Algebra.smul_def] at hz
      exact hz
    rcases Rat.RingOfIntegers.isUnit_iff.1 z.isUnit with h | h
    · left
      rwa [h, one_mul] at hz'
    · right
      rwa [h, neg_one_mul, neg_eq_iff_eq_neg] at hz'
  · rintro (h | h)
    · exact ⟨1, by rw [one_smul, h]⟩
    · exact ⟨-1, by rw [Units.neg_smul, one_smul, h, neg_neg]⟩

theorem positiveSubgroup_inf_diagonal_range : positiveSubgroup ⊓ (diagonal ℚ).range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, a, rfl⟩
  obtain ⟨h1, h2⟩ := mem_positiveSubgroup.1 hx
  rw [realPart_diagonal] at h2
  rw [Subgroup.mem_bot]
  rcases (diagonal_mem_standardOpenSubgroup_iff a).1 h1 with h | h
  · rw [show a = 1 from Units.ext h, map_one]
  · rw [h] at h2
    norm_num at h2

theorem subsingleton_classGroup : Subsingleton (ClassGroup (𝓞 ℚ)) := by
  have h := Rat.classNumber_eq
  rw [NumberField.classNumber] at h
  exact Fintype.card_le_one_iff_subsingleton.1 h.le

theorem positiveSubgroup_sup_diagonal_range : positiveSubgroup ⊔ (diagonal ℚ).range = ⊤ := by
  have htop : (diagonal ℚ).range ⊔ standardOpenSubgroup ℚ = ⊤ := by
    rw [← IdeleGroup.ker_toClassGroup, eq_top_iff]
    intro x _
    have := subsingleton_classGroup
    exact Subsingleton.elim _ _
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ (diagonal ℚ).range ⊔ standardOpenSubgroup ℚ := htop ▸ Subgroup.mem_top x
  obtain ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩ := Subgroup.mem_sup.1 hx
  rcases lt_or_gt_of_ne (realPart u).ne_zero with hneg | hpos
  · have hm : diagonal ℚ (-1) ∈ standardOpenSubgroup ℚ :=
      (diagonal_mem_standardOpenSubgroup_iff (-1)).2 (Or.inr (by simp))
    have hp : diagonal ℚ (-1) * u ∈ positiveSubgroup := by
      refine mem_positiveSubgroup.2 ⟨mul_mem hm hu, ?_⟩
      rw [map_mul, Units.val_mul, realPart_diagonal]
      push_cast
      linarith
    refine Subgroup.mem_sup.2 ⟨_, hp, diagonal ℚ (-a), ⟨-a, rfl⟩, ?_⟩
    rw [mul_right_comm, ← map_mul, neg_one_mul, neg_neg]
  · exact Subgroup.mem_sup.2 ⟨u, mem_positiveSubgroup.2 ⟨hu, hpos⟩, diagonal ℚ a, ⟨a, rfl⟩,
      mul_comm _ _⟩

def positiveSubgroupEquivIdeleClassGroup : positiveSubgroup ≃ₜ* IdeleClassGroup ℚ :=
  openSubgroupEquivQuotient _ _ isOpen_positiveSubgroup positiveSubgroup_inf_diagonal_range
    positiveSubgroup_sup_diagonal_range

@[simp]
theorem positiveSubgroupEquivIdeleClassGroup_apply (x : positiveSubgroup) :
    positiveSubgroupEquivIdeleClassGroup x = IdeleClassGroup.mk ℚ x :=
  rfl

def positiveSubgroupEquiv : positiveSubgroup ≃ₜ* Units.posSubgroup ℝ ×
    Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ where
  toFun x := (⟨realPart x, (Units.mem_posSubgroup _).2 (mem_positiveSubgroup.1 x.2).2⟩,
    (standardOpenSubgroupEquiv (K := ℚ) ⟨x, (mem_positiveSubgroup.1 x.2).1⟩).2)
  invFun p := ⟨ofIntegerUnits (realUnitsEquiv.symm p.1) p.2, mem_positiveSubgroup.2
    ⟨ofIntegerUnits_mem _ _, by
      rw [realPart_ofIntegerUnits, ContinuousMulEquiv.apply_symm_apply]
      exact (Units.mem_posSubgroup _).1 p.1.2⟩⟩
  left_inv x := by
    have h : realUnitsEquiv.symm (realPart x) = toInfinite ℚ x :=
      realUnitsEquiv.symm_apply_apply _
    apply Subtype.ext
    change ofIntegerUnits (realUnitsEquiv.symm (realPart x)) _ = (x : IdeleGroup ℚ)
    rw [h]
    exact Units.ext (Prod.ext rfl (Subtype.ext (funext fun _ ↦ rfl)))
  right_inv p := Prod.ext (Subtype.ext (realUnitsEquiv.apply_symm_apply _))
    (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  map_mul' x y := Prod.ext (Subtype.ext (map_mul realPart (x : IdeleGroup ℚ) y))
    (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  continuous_toFun := by
    exact ((continuous_realPart.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp ((standardOpenSubgroupEquiv (K := ℚ)).continuous.comp
        (continuous_subtype_val.subtype_mk _)))
  continuous_invFun := by
    exact (continuous_subtype_val.comp ((standardOpenSubgroupEquiv (K := ℚ)).symm.continuous.comp
      ((realUnitsEquiv.symm.continuous.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd))).subtype_mk _

def integersRingEquiv :
    (Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) ≃+* Π p : Nat.Primes, ℤ_[p] :=
  (RingEquiv.piCongrRight fun v ↦
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv).trans
    (RingEquiv.piCongrLeft (fun p : Nat.Primes ↦ ℤ_[p]) Rat.HeightOneSpectrum.primesEquiv)

def integersHomeomorph :
    (Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) ≃ₜ Π p : Nat.Primes, ℤ_[p] :=
  (Homeomorph.piCongrRight fun v ↦
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph).trans
    (Homeomorph.piCongrLeft (Y := fun p : Nat.Primes ↦ ℤ_[p]) Rat.HeightOneSpectrum.primesEquiv)

theorem integersRingEquiv_eq_integersHomeomorph (x : Π v : HeightOneSpectrum (𝓞 ℚ),
    v.adicCompletionIntegers ℚ) : integersRingEquiv x = integersHomeomorph x :=
  rfl

theorem continuous_integersRingEquiv : Continuous integersRingEquiv :=
  integersHomeomorph.continuous.congr fun x ↦ (integersRingEquiv_eq_integersHomeomorph x).symm

theorem continuous_integersRingEquiv_symm : Continuous integersRingEquiv.symm := by
  exact continuous_equiv_symm_of_eq integersRingEquiv.toEquiv integersHomeomorph
    integersRingEquiv_eq_integersHomeomorph

def integerUnitsEquiv :
    (Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) ≃ₜ*
      (Π p : Nat.Primes, ℤ_[p])ˣ :=
  ContinuousMulEquiv.piUnits.symm.trans
    (unitsContinuousMulEquiv integersRingEquiv.toMulEquiv continuous_integersRingEquiv
      continuous_integersRingEquiv_symm)

def mulMap : ℚˣ × positiveSubgroup →* IdeleGroup ℚ :=
  (diagonal ℚ).coprod positiveSubgroup.subtype

theorem mulMap_apply (p : ℚˣ × positiveSubgroup) :
    mulMap p = diagonal ℚ p.1 * (p.2 : IdeleGroup ℚ) :=
  rfl

theorem mulMap_bijective : Function.Bijective mulMap := by
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨a, u⟩ h
    have h' : diagonal ℚ a * (u : IdeleGroup ℚ) = 1 := h
    have hu : (u : IdeleGroup ℚ)⁻¹ ∈ positiveSubgroup ⊓ (diagonal ℚ).range :=
      ⟨positiveSubgroup.inv_mem u.2, a, eq_inv_of_mul_eq_one_left h'⟩
    rw [positiveSubgroup_inf_diagonal_range, Subgroup.mem_bot, inv_eq_one] at hu
    have ha : diagonal ℚ a = 1 := by rwa [hu, mul_one] at h'
    exact Prod.ext (diagonal_injective ℚ (ha.trans (map_one _).symm)) (Subtype.ext hu)
  · intro x
    have hx : x ∈ positiveSubgroup ⊔ (diagonal ℚ).range :=
      positiveSubgroup_sup_diagonal_range ▸ Subgroup.mem_top x
    obtain ⟨u, hu, _, ⟨a, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hx
    exact ⟨(a, ⟨u, hu⟩), mul_comm _ _⟩

def ideleClassGroupEquiv : IdeleClassGroup ℚ ≃ₜ* Units.posSubgroup ℝ × (Π p : Nat.Primes, ℤ_[p])ˣ :=
  positiveSubgroupEquivIdeleClassGroup.symm.trans (positiveSubgroupEquiv.trans
    (continuousMulEquivProdCongr (ContinuousMulEquiv.refl _) integerUnitsEquiv))

theorem ideleClassGroupEquiv_mk (x : positiveSubgroup) :
    ideleClassGroupEquiv (IdeleClassGroup.mk ℚ x) =
      (⟨realPart x, (Units.mem_posSubgroup _).2 (mem_positiveSubgroup.1 x.2).2⟩,
        integerUnitsEquiv (positiveSubgroupEquiv x).2) := by
  simp only [ideleClassGroupEquiv, ContinuousMulEquiv.trans_apply]
  rw [← positiveSubgroupEquivIdeleClassGroup_apply, ContinuousMulEquiv.symm_apply_apply]
  rfl

end RationalIdeles

end

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.IdeleGroups.LocalConditionIndex
namespace GroundTheory.Global

open NumberField IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem map_range_powMonoidHom {G H : Type*} [CommGroup G] [CommGroup H] (e : G ≃* H) (n : ℕ) :
    (powMonoidHom n : G →* G).range.map (e : G →* H) = (powMonoidHom n : H →* H).range := by
  ext y
  simp only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, by simp [map_pow]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e.symm x ^ n, ⟨e.symm x, rfl⟩, by simp [map_pow]⟩

theorem index_range_powMonoidHom_of_mulEquiv {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) :
    (powMonoidHom n : G →* G).range.index = (powMonoidHom n : H →* H).range.index := by
  rw [← map_range_powMonoidHom e n, Subgroup.index_map_equiv]


omit [NumberField K] in
open Classical in
theorem index_range_powMonoidHom_infinitePlaceCompletion (w : InfinitePlace K) {n : ℕ}
    (hn : n ≠ 0) :
    letI : Decidable (w.IsReal ∧ Even n) := Classical.propDecidable _
    (powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range.index =
      if w.IsReal ∧ Even n then 2 else 1 := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [index_range_powMonoidHom_of_mulEquiv
      (Units.mapEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMulEquiv) n,
      index_range_powMonoidHom_real hn]
    by_cases he : Even n <;> simp [hw, he]
  · rw [index_range_powMonoidHom_of_mulEquiv
      (Units.mapEquiv (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).toMulEquiv) n,
      index_range_powMonoidHom_complex hn]
    have hw' : ¬w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hw
    simp [hw']

namespace IdeleGroup

@[simp]
theorem finiteProj_infiniteEmbedding (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K)
    (x : (w.Completion)ˣ) : finiteProj v (infiniteEmbedding w x) = 1 :=
  Units.ext rfl

@[simp]
theorem infiniteProj_finiteEmbedding (w : InfinitePlace K) (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : infiniteProj w (finiteEmbedding v x) = 1 :=
  Units.ext rfl

theorem infiniteEmbedding_mem_standardOpenSubgroup (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    infiniteEmbedding w x ∈ standardOpenSubgroup K := by
  rw [mem_standardOpenSubgroup]
  intro v
  rw [← map_inv]
  simp only [coe_infiniteEmbedding]
  exact ⟨one_mem _, one_mem _⟩

def localSubgroup (S T : Set (HeightOneSpectrum (𝓞 K)))
    (H : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
    (H' : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ) : Subgroup (IdeleGroup K) where
  carrier := {x | (∀ v ∈ S, finiteProj v x ∈ H v) ∧ (∀ w, infiniteProj w x ∈ H' w) ∧
    ∀ v ∉ S ∪ T, ord v x = 0}
  one_mem' := ⟨fun v _ ↦ by rw [map_one]; exact one_mem _, fun w ↦ by rw [map_one]; exact one_mem _,
    fun v _ ↦ ord_one v⟩
  mul_mem' {x y} hx hy := ⟨fun v hv ↦ by rw [map_mul]; exact mul_mem (hx.1 v hv) (hy.1 v hv),
    fun w ↦ by rw [map_mul]; exact mul_mem (hx.2.1 w) (hy.2.1 w),
    fun v hv ↦ by rw [ord_mul, hx.2.2 v hv, hy.2.2 v hv, add_zero]⟩
  inv_mem' {x} hx := ⟨fun v hv ↦ by rw [map_inv]; exact inv_mem (hx.1 v hv),
    fun w ↦ by rw [map_inv]; exact inv_mem (hx.2.1 w),
    fun v hv ↦ by rw [ord_inv, hx.2.2 v hv, neg_zero]⟩

variable (S T : Set (HeightOneSpectrum (𝓞 K)))
  (H : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
  (H' : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ)

theorem mem_localSubgroup {x : IdeleGroup K} :
    x ∈ localSubgroup S T H H' ↔ (∀ v ∈ S, finiteProj v x ∈ H v) ∧
      (∀ w, infiniteProj w x ∈ H' w) ∧ ∀ v ∉ S ∪ T, ord v x = 0 :=
  Iff.rfl

theorem localSubgroup_le_sIdeles : localSubgroup S T H H' ≤ sIdeles (S ∪ T) :=
  fun _ hx ↦ hx.2.2

def localQuotientMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T) →*
      (∀ v : S, (v.1.adicCompletion K)ˣ ⧸ H v.1) × (∀ w : InfinitePlace K, (w.Completion)ˣ ⧸ H' w) :=
  MonoidHom.prod
    (MonoidHom.pi fun v ↦ (QuotientGroup.mk' (H v.1)).comp ((finiteProj v.1).comp (sIdeles _).subtype))
    (MonoidHom.pi fun w ↦ (QuotientGroup.mk' (H' w)).comp ((infiniteProj w).comp (sIdeles _).subtype))

theorem ker_localQuotientMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (localQuotientMap T H H' S).ker =
      (localSubgroup S T H H').subgroupOf (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_localSubgroup]
  simp only [localQuotientMap, MonoidHom.prod_apply, Prod.mk_eq_one, funext_iff, Pi.one_apply,
    MonoidHom.pi_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.coe_subtype, Subtype.forall, Finset.mem_coe]
  exact ⟨fun h ↦ ⟨h.1, h.2, x.2⟩, fun h ↦ ⟨h.1, h.2.1⟩⟩

theorem localQuotientMap_surjective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective (localQuotientMap T H H' S) := by
  classical
  rintro ⟨a, b⟩
  choose α hα using fun v : S ↦ QuotientGroup.mk_surjective (a v)
  choose β hβ using fun w ↦ QuotientGroup.mk_surjective (b w)
  let x : IdeleGroup K := (∏ v : S, finiteEmbedding v.1 (α v)) * ∏ w, infiniteEmbedding w (β w)
  have hx : x ∈ sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T) := by
    refine mul_mem (prod_mem fun v _ ↦ ?_) (prod_mem fun w _ ↦ ?_)
    · intro u hu
      exact ord_finiteEmbedding_of_ne (fun h ↦ hu (Or.inl (by rw [h]; exact Finset.mem_coe.2 v.2))) _
    · exact standardOpenSubgroup_le_sIdeles _ (infiniteEmbedding_mem_standardOpenSubgroup w _)
  have hfin : ∀ v : S, finiteProj v.1 x = α v := by
    intro v
    simp only [x, map_mul, map_prod, finiteProj_infiniteEmbedding, Finset.prod_const_one, mul_one]
    rw [Finset.prod_eq_single v (fun u _ hu ↦
      finiteProj_finiteEmbedding_of_ne (fun h ↦ hu (Subtype.ext h.symm)) _) (by simp),
      finiteProj_finiteEmbedding]
  have hinf : ∀ w : InfinitePlace K, infiniteProj w x = β w := by
    intro w
    simp only [x, map_mul, map_prod, infiniteProj_finiteEmbedding, Finset.prod_const_one, one_mul]
    rw [Finset.prod_eq_single w (fun u _ hu ↦
      infiniteProj_infiniteEmbedding_of_ne (fun h ↦ hu h.symm) _) (by simp),
      infiniteProj_infiniteEmbedding]
  refine ⟨⟨x, hx⟩, Prod.ext (funext fun v ↦ ?_) (funext fun w ↦ ?_)⟩
  · exact (congrArg (QuotientGroup.mk (s := H v.1)) (hfin v)).trans (hα v)
  · exact (congrArg (QuotientGroup.mk (s := H' w)) (hinf w)).trans (hβ w)

theorem relIndex_localSubgroup (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (localSubgroup S T H H').relIndex (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) =
      (∏ v ∈ S, (H v).index) * ∏ w : InfinitePlace K, (H' w).index := by
  have hk := Subgroup.index_ker (G' := (∀ v : S, (v.1.adicCompletion K)ˣ ⧸ H v.1) ×
    (∀ w : InfinitePlace K, (w.Completion)ˣ ⧸ H' w)) (localQuotientMap T H H' S)
  rw [Subgroup.relIndex, ← ker_localQuotientMap, hk,
    MonoidHom.range_eq_top_of_surjective _ (localQuotientMap_surjective T H H' S),
    Subgroup.card_top, Nat.card_prod, Nat.card_pi, Nat.card_pi, ← Finset.prod_coe_sort S]
  rfl

def powerSubgroup (n : ℕ) (S T : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup K) :=
  localSubgroup S T (fun v ↦ (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range)
    (fun w ↦ (powMonoidHom n : (w.Completion)ˣ →* _).range)

theorem powerSubgroup_le_sIdeles (n : ℕ) : powerSubgroup n S T ≤ sIdeles (S ∪ T) :=
  localSubgroup_le_sIdeles S T _ _

theorem relIndex_powerSubgroup (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (powerSubgroup n S T).relIndex (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) =
      (∏ v ∈ S, (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range.index) *
        ∏ w : InfinitePlace K, (powMonoidHom n : (w.Completion)ˣ →* _).range.index :=
  relIndex_localSubgroup T _ _ S

theorem relIndex_powerSubgroup_empty (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (powerSubgroup n S ∅).relIndex (sIdeles (S : Set (HeightOneSpectrum (𝓞 K)))) =
      (∏ v ∈ S, (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range.index) *
        ∏ w : InfinitePlace K, (powMonoidHom n : (w.Completion)ˣ →* _).range.index := by
  have h := relIndex_powerSubgroup (K := K) ∅ n S
  rwa [Set.union_empty] at h

end IdeleGroup

end

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.IdeleGroups.UnitBound
namespace GroundTheory.Global

open NumberField IsDedekindDomain Topology Filter NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped NumberField.AdeleRing RestrictedProduct

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

instance InfinitePlace.Completion.properSpace (w : InfinitePlace K) : ProperSpace w.Completion := by
  let _ : NontriviallyNormedField w.Completion :=
    { (inferInstance : NormedField w.Completion) with
      non_trivial := ⟨2, by
        have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) 2
        rw [map_ofNat] at h
        rw [← h]
        norm_num⟩ }
  exact ProperSpace.of_locallyCompactSpace w.Completion

namespace IdeleGroup

theorem abs_log_le_iff {r M : ℝ} (hr : 0 < r) :
    |Real.log r| ≤ M ↔ Real.exp (-M) ≤ r ∧ r ≤ Real.exp M := by
  rw [abs_le, neg_le, ← Real.log_inv, Real.log_le_iff_le_exp (inv_pos.2 hr),
    Real.log_le_iff_le_exp hr, inv_le_comm₀ hr (Real.exp_pos _), Real.exp_neg]


omit [NumberField K] in
theorem isCompact_units_abs_log_le (w : InfinitePlace K) (M : ℝ) :
    IsCompact {z : (w.Completion)ˣ | |Real.log ‖(z : w.Completion)‖| ≤ M} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have h : ((↑) : (w.Completion)ˣ → w.Completion) ''
      {z : (w.Completion)ˣ | |Real.log ‖(z : w.Completion)‖| ≤ M} =
      {c : w.Completion | Real.exp (-M) ≤ ‖c‖ ∧ ‖c‖ ≤ Real.exp M} := by
    ext c
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (abs_log_le_iff (norm_pos_iff.2 z.ne_zero)).1 hz
    · rintro ⟨h1, h2⟩
      have hc : c ≠ 0 := norm_pos_iff.1 ((Real.exp_pos _).trans_le h1)
      exact ⟨Units.mk0 c hc, (abs_log_le_iff (norm_pos_iff.2 hc)).2 ⟨h1, h2⟩, rfl⟩
  rw [h]
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · exact (Metric.isBounded_closedBall (x := (0 : w.Completion)) (r := Real.exp M)).subset
      fun c hc ↦ by simpa using hc.2


omit [NumberField K] in
theorem isCompact_infinite_abs_log_le (M : ℝ) :
    IsCompact {y : (InfiniteAdeleRing K)ˣ |
      ∀ w : InfinitePlace K, |Real.log ‖(y : InfiniteAdeleRing K) w‖| ≤ M} := by
  let p := (ContinuousMulEquiv.piUnits :
    (InfiniteAdeleRing K)ˣ ≃ₜ* ∀ w : InfinitePlace K, (w.Completion)ˣ)
  have hc : IsCompact ((p ⁻¹' Set.univ.pi fun w ↦
      {z : (w.Completion)ˣ | |Real.log ‖(z : w.Completion)‖| ≤ M}) : Set (InfiniteAdeleRing K)ˣ) :=
    p.toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi fun w ↦ isCompact_units_abs_log_le K w M)
  convert hc using 1
  ext y
  exact ⟨fun hy w _ ↦ hy w, fun hy w ↦ hy w (Set.mem_univ w)⟩

theorem isCompact_finite_units_integral :
    IsCompact {f : (FiniteAdeleRing (𝓞 K) K)ˣ | ∀ v : HeightOneSpectrum (𝓞 K),
      (f : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
        ((f⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v ∈
          v.adicCompletionIntegers K} := by
  have hI := isCompact_integralFiniteAdeles K
  have h : IsCompact ((integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) ×ˢ
      (MulOpposite.unop ⁻¹' (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)))) :=
    hI.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hI)
  convert Units.isClosedEmbedding_embedProduct.isCompact_preimage h using 1
  ext f
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply,
    MulOpposite.unop_op, SetLike.mem_coe, mem_integralFiniteAdeles, ← forall_and]

theorem isCompact_abs_log_le_inter_standardOpenSubgroup (M : ℝ) :
    IsCompact {x : IdeleGroup K | (∀ w : InfinitePlace K, |Real.log ‖(x : 𝔸[K]).1 w‖| ≤ M) ∧
      x ∈ standardOpenSubgroup K} := by
  let e := prodEquiv K
  have hc : IsCompact (e ⁻¹'
      ({y : (InfiniteAdeleRing K)ˣ |
        ∀ w : InfinitePlace K, |Real.log ‖(y : InfiniteAdeleRing K) w‖| ≤ M} ×ˢ
      {f : (FiniteAdeleRing (𝓞 K) K)ˣ | ∀ v : HeightOneSpectrum (𝓞 K),
        (f : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
          ((f⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v ∈
            v.adicCompletionIntegers K})) :=
    e.toHomeomorph.isCompact_preimage.2
      ((isCompact_infinite_abs_log_le K M).prod (isCompact_finite_units_integral K))
  convert hc using 1
  ext x
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, (mem_standardOpenSubgroup K).1 h2⟩,
    fun ⟨h1, h2⟩ ↦ ⟨h1, (mem_standardOpenSubgroup K).2 h2⟩⟩

def unitsToUnits : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom

omit [NumberField K] in
@[simp]
theorem coe_unitsToUnits (u : (𝓞 K)ˣ) : ((unitsToUnits K u : Kˣ) : K) = ((u : 𝓞 K) : K) :=
  rfl

theorem diagonal_unitsToUnits_mem (u : (𝓞 K)ˣ) :
    diagonal K (unitsToUnits K u) ∈ standardOpenSubgroup K := by
  rw [mem_standardOpenSubgroup K]
  intro v
  refine ⟨(coe_mem_adicCompletionIntegers_iff v _).2 (HeightOneSpectrum.valuation_le_one v _),
    ?_⟩
  rw [← map_inv]
  exact (coe_mem_adicCompletionIntegers_iff v _).2
    (HeightOneSpectrum.valuation_le_one v ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K))

theorem infiniteModule_diagonal_unitsToUnits (u : (𝓞 K)ˣ) :
    infiniteModule (diagonal K (unitsToUnits K u)) = 1 := by
  have h := congrArg Subtype.val (ideleModule_diagonal (unitsToUnits K u))
  rwa [ideleModule_apply, finiteModule_eq_one_of_mem (diagonal_unitsToUnits_mem K u), mul_one,
    Positive.val_one] at h

variable {K}

theorem norm_diagonal_mul (k : Kˣ) (y : IdeleGroup K) (w : InfinitePlace K) :
    ‖((diagonal K k * y : IdeleGroup K) : 𝔸[K]).1 w‖ = w (k : K) * ‖(y : 𝔸[K]).1 w‖ := by
  rw [Units.val_mul, adele_fst_mul_apply, norm_mul]
  congr 1
  rw [coe_diagonal, AdeleRing.algebraMap_fst_apply]
  exact AbsoluteValue.Completion.norm_coe (WithAbs.toAbs w.1 (k : K))

theorem log_infiniteModule (x : IdeleGroup K) :
    Real.log (infiniteModule x) =
      ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log ‖(x : 𝔸[K]).1 w‖ := by
  rw [infiniteModule, Real.log_prod fun w _ ↦ pow_ne_zero _ (norm_ne_zero_iff.2
    (infinite_ne_zero x w))]
  simp only [Real.log_pow]

def logVector (x : IdeleGroup K) : logSpace K :=
  fun w ↦ (w.1.mult : ℝ) * Real.log ‖(x : 𝔸[K]).1 w.1‖

theorem logVector_diagonal_mul (u : (𝓞 K)ˣ) (y : IdeleGroup K) :
    logVector (diagonal K (unitsToUnits K u) * y) =
      logEmbedding K (Additive.ofMul u) + logVector y := by
  ext w
  have hu : w.1 (((u : 𝓞 K) : K)) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 u.ne_zero
  rw [logVector, norm_diagonal_mul, coe_unitsToUnits,
    Real.log_mul hu (norm_ne_zero_iff.2 (infinite_ne_zero y w.1)),
    Pi.add_apply, logEmbedding_component, logVector, mul_add]

theorem exists_unit_forall_abs_log_le (M₀ : ℝ) : ∃ M : ℝ, ∀ y : IdeleGroup K,
    |Real.log (infiniteModule y)| ≤ M₀ → ∃ u : (𝓞 K)ˣ, ∀ w : InfinitePlace K,
      |Real.log ‖((diagonal K (unitsToUnits K u) * y : IdeleGroup K) : 𝔸[K]).1 w‖| ≤ M := by
  classical
  let B := (basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)
  obtain ⟨C, hC⟩ := (ZSpan.fundamentalDomain_isBounded B).exists_norm_le
  set C' := max C 0 with hC'
  refine ⟨M₀ + Fintype.card {w : InfinitePlace K // w ≠ w₀} * C' + C', fun y hy ↦ ?_⟩
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans hy
  have hC'0 : 0 ≤ C' := le_max_right _ _
  obtain ⟨⟨e, he⟩, hmem, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B (logVector y)
  rw [Module.Basis.ofZLatticeBasis_span ℝ (unitLattice K)] at he
  obtain ⟨u, -, rfl⟩ := he
  refine ⟨Additive.toMul u, ?_⟩
  set z := diagonal K (unitsToUnits K (Additive.toMul u)) * y with hz
  have hF : logVector z ∈ ZSpan.fundamentalDomain B := by
    rw [hz, logVector_diagonal_mul]
    exact hmem
  have hbound : ∀ w : {w : InfinitePlace K // w ≠ w₀},
      |(w.1.mult : ℝ) * Real.log ‖(z : 𝔸[K]).1 w.1‖| ≤ C' := fun w ↦ by
    have := (norm_le_pi_norm (logVector z) w).trans (hC _ hF)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hmult : ∀ (w : InfinitePlace K) (t : ℝ), |t| ≤ |(w.mult : ℝ) * t| := fun w t ↦ by
    rw [abs_mul]
    exact le_mul_of_one_le_left (abs_nonneg t) (by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast w.mult_pos)
  have hmod : infiniteModule z = infiniteModule y := by
    rw [hz, infiniteModule_mul, infiniteModule_diagonal_unitsToUnits, one_mul]
  intro w
  by_cases hw : w = w₀
  · subst hw
    have hsum := log_infiniteModule z
    rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace K), hmod] at hsum
    have h1 : |∑ w : {w : InfinitePlace K // w ≠ w₀},
        (w.1.mult : ℝ) * Real.log ‖(z : 𝔸[K]).1 w.1‖| ≤
        Fintype.card {w : InfinitePlace K // w ≠ w₀} * C' := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun w _ ↦ hbound w).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h2 : ((w₀ : InfinitePlace K).mult : ℝ) * Real.log ‖(z : 𝔸[K]).1 w₀‖ = Real.log (infiniteModule y) -
        ∑ w : {w : InfinitePlace K // w ≠ w₀},
          (w.1.mult : ℝ) * Real.log ‖(z : 𝔸[K]).1 w.1‖ := by
      linarith
    refine (hmult (w₀ : InfinitePlace K) _).trans ?_
    rw [h2]
    refine (abs_sub _ _).trans ?_
    linarith
  · refine (hmult w _).trans ((hbound ⟨w, hw⟩).trans ?_)
    have : 0 ≤ (Fintype.card {w : InfinitePlace K // w ≠ w₀} : ℝ) * C' :=
      mul_nonneg (Nat.cast_nonneg _) hC'0
    linarith

end IdeleGroup

end

end GroundTheory.Global
end
