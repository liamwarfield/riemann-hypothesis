module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.FilteredHomology
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section Elements

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{u} R) c)

theorem exists_iCycles_eq {i : ι} (x : K.X i) (hx : (K.d i (c.next i)).hom x = 0) :
    ∃ z : K.cycles i, (K.iCycles i).hom z = x := by
  refine ⟨(K.sc i).moduleCatCyclesIso.inv ⟨x, hx⟩, ?_⟩
  have := ShortComplex.moduleCatCyclesIso_inv_iCycles_apply (K.sc i) ⟨x, hx⟩
  exact this

theorem shortComplex_homologyπ_eq_zero_iff (S : ShortComplex (ModuleCat.{u} R)) (z : S.cycles) :
    S.homologyπ.hom z = 0 ↔ ∃ w : S.X₁, S.f.hom w = S.iCycles.hom z := by
  have hinj : Function.Injective S.moduleCatHomologyIso.hom.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have h1 : S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom z) =
      S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom.hom z) :=
    ShortComplex.π_moduleCatCyclesIso_hom_apply S z
  have h2 : S.moduleCatLeftHomologyData.i.hom (S.moduleCatCyclesIso.hom.hom z) =
      S.iCycles.hom z :=
    ShortComplex.moduleCatCyclesIso_hom_i_apply S z
  have h0 : S.homologyπ.hom z = 0 ↔ S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom z) = 0 :=
    ⟨fun h => by rw [h, map_zero], fun h => hinj (h.trans (map_zero _).symm)⟩
  rw [h0, h1]
  change Submodule.Quotient.mk (p := LinearMap.range S.moduleCatToCycles)
    (S.moduleCatCyclesIso.hom.hom z) = 0 ↔ _
  refine (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)
    (x := (S.moduleCatCyclesIso.hom.hom z : LinearMap.ker S.g.hom))).trans ?_
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (congrArg S.moduleCatLeftHomologyData.i.hom hw).trans h2⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, (ModuleCat.mono_iff_injective S.moduleCatLeftHomologyData.i).1 inferInstance
      (hw.trans h2.symm)⟩

theorem homologyπ_eq_zero_iff {i : ι} (z : K.cycles i) :
    (K.homologyπ i).hom z = 0 ↔
      ∃ w : K.X (c.prev i), (K.d (c.prev i) i).hom w = (K.iCycles i).hom z :=
  shortComplex_homologyπ_eq_zero_iff (K.sc i) z

end Elements

section Apply

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{u} R) c}

theorem hom_f_d_apply (φ : K ⟶ L) (i j : ι) (x : K.X i) :
    (φ.f j).hom ((K.d i j).hom x) = (L.d i j).hom ((φ.f i).hom x) :=
  (congrArg (fun g => ModuleCat.Hom.hom g x) (φ.comm i j)).symm

theorem iCycles_d_apply (K : HomologicalComplex (ModuleCat.{u} R) c) (i j : ι) (z : K.cycles i) :
    (K.d i j).hom ((K.iCycles i).hom z) = 0 := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.iCycles_d, ModuleCat.hom_zero,
    LinearMap.zero_apply]

theorem iCycles_cyclesMap_apply (φ : K ⟶ L) (i : ι) (z : K.cycles i) :
    (L.iCycles i).hom ((HomologicalComplex.cyclesMap φ i).hom z) =
      (φ.f i).hom ((K.iCycles i).hom z) :=
  congrArg (fun g => ModuleCat.Hom.hom g z) (HomologicalComplex.cyclesMap_i φ i)

theorem homologyMap_homologyπ_apply (φ : K ⟶ L) (i : ι) (z : K.cycles i) :
    (HomologicalComplex.homologyMap φ i).hom ((K.homologyπ i).hom z) =
      (L.homologyπ i).hom ((HomologicalComplex.cyclesMap φ i).hom z) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.homologyπ_naturality]
  rfl

end Apply

section Filtered

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {J : Type u} [SmallCategory J] [IsFiltered J]
  {F : J ⥤ HomologicalComplex (ModuleCat.{u} R) c} (t : Cocone F)

omit [IsFiltered J] in
theorem cocone_w_apply {j j' : J} (f : j ⟶ j') (i : ι) (y : (F.obj j).X i) :
    ((t.ι.app j').f i).hom (((F.map f).f i).hom y) = ((t.ι.app j).f i).hom y :=
  congrArg (fun φ : F.obj j ⟶ t.pt => (φ.f i).hom y) (t.w f)


omit [IsFiltered J] in
theorem exists_homologyMap_eq_of_cocone (i : ι)
    (hsurj : ∀ x : t.pt.X i, ∃ (j : J) (y : (F.obj j).X i), ((t.ι.app j).f i).hom y = x)
    (hinj : ∀ (j : J) (y : (F.obj j).X (c.next i)), ((t.ι.app j).f (c.next i)).hom y = 0 →
      ∃ (j' : J) (f : j ⟶ j'), ((F.map f).f (c.next i)).hom y = 0)
    (z : t.pt.homology i) :
    ∃ (j : J) (y : (F.obj j).homology i),
      (HomologicalComplex.homologyMap (t.ι.app j) i).hom y = z := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (t.pt.homologyπ i)).1 inferInstance z
  obtain ⟨j, y, hy⟩ := hsurj ((t.pt.iCycles i).hom z)
  have hdy : ((t.ι.app j).f (c.next i)).hom (((F.obj j).d i (c.next i)).hom y) = 0 := by
    rw [hom_f_d_apply, hy]
    exact iCycles_d_apply t.pt i _ z
  obtain ⟨j', f, hf⟩ := hinj j _ hdy
  rw [hom_f_d_apply] at hf
  obtain ⟨z', hz'⟩ := exists_iCycles_eq (F.obj j') (((F.map f).f i).hom y) hf
  refine ⟨j', (HomologicalComplex.homologyπ (F.obj j') i).hom z', ?_⟩
  rw [homologyMap_homologyπ_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective (t.pt.iCycles i)).1 inferInstance
  rw [iCycles_cyclesMap_apply, hz', cocone_w_apply, hy]

theorem exists_homologyMap_map_eq_zero_of_cocone (i : ι)
    (hsurj : ∀ x : t.pt.X (c.prev i),
      ∃ (j : J) (y : (F.obj j).X (c.prev i)), ((t.ι.app j).f (c.prev i)).hom y = x)
    (hinj : ∀ (j : J) (y : (F.obj j).X i), ((t.ι.app j).f i).hom y = 0 →
      ∃ (j' : J) (f : j ⟶ j'), ((F.map f).f i).hom y = 0)
    (j : J) (y : (F.obj j).homology i)
    (hy : (HomologicalComplex.homologyMap (t.ι.app j) i).hom y = 0) :
    ∃ (j' : J) (f : j ⟶ j'), (HomologicalComplex.homologyMap (F.map f) i).hom y = 0 := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((F.obj j).homologyπ i)).1 inferInstance y
  rw [homologyMap_homologyπ_apply, homologyπ_eq_zero_iff, iCycles_cyclesMap_apply] at hy
  obtain ⟨w, hw⟩ := hy
  obtain ⟨j₁, v, hv⟩ := hsurj w
  let m := IsFiltered.max j j₁
  let a : j ⟶ m := IsFiltered.leftToMax j j₁
  let b : j₁ ⟶ m := IsFiltered.rightToMax j j₁
  let e : (F.obj m).X i := ((F.map a).f i).hom (((F.obj j).iCycles i).hom z) -
    ((F.obj m).d (c.prev i) i).hom (((F.map b).f (c.prev i)).hom v)
  have he : ((t.ι.app m).f i).hom e = 0 := by
    simp only [e, map_sub]
    rw [cocone_w_apply, hom_f_d_apply, cocone_w_apply, hv]
    exact sub_eq_zero.2 hw.symm
  obtain ⟨j', g, hg⟩ := hinj m e he
  refine ⟨j', a ≫ g, ?_⟩
  rw [homologyMap_homologyπ_apply, homologyπ_eq_zero_iff, iCycles_cyclesMap_apply]
  refine ⟨((F.map (b ≫ g)).f (c.prev i)).hom v, ?_⟩
  simp only [e, map_sub, sub_eq_zero] at hg
  rw [F.map_comp, F.map_comp, HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [← hom_f_d_apply]
  exact hg.symm

end Filtered

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.OpenNormal
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Filter Topology

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace OpenNormalSubgroup

instance instNonempty : Nonempty (OpenNormalSubgroup G) :=
  ⟨{ toOpenSubgroup := ⊤, isNormal' := ⟨fun _ _ _ => Set.mem_univ _⟩ }⟩

variable [IsTopologicalGroup G]

instance discreteTopology_quotient (U : OpenNormalSubgroup G) :
    DiscreteTopology (G ⧸ (U : Subgroup G)) :=
  QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen

instance finite_quotient [CompactSpace G] (U : OpenNormalSubgroup G) :
    Finite (G ⧸ (U : Subgroup G)) :=
  Subgroup.quotient_finite_of_isOpen _ U.toOpenSubgroup.isOpen

variable [CompactSpace G] [TotallyDisconnectedSpace G]

theorem hasBasis_nhds_one :
    (𝓝 (1 : G)).HasBasis (fun _ : OpenNormalSubgroup G => True) (fun U => (U : Set G)) := by
  refine ⟨fun s => ⟨fun hs => ?_, fun ⟨U, _, hU⟩ => mem_of_superset U.mem_nhds_one hU⟩⟩
  obtain ⟨t, hts, ht, h1⟩ := mem_nhds_iff.mp hs
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ht h1
  exact ⟨U, trivial, hU.trans hts⟩

theorem hasBasis_nhds_one_pi (ι : Type*) [Finite ι] :
    (𝓝 (1 : ι → G)).HasBasis (fun _ : OpenNormalSubgroup G => True)
      (fun U => Set.univ.pi fun _ => (U : Set G)) := by
  simp only [nhds_pi, Pi.one_apply]
  refine (hasBasis_nhds_one.pi_self (ι := ι)).to_hasBasis ?_ ?_
  · rintro ⟨I, U⟩ -
    exact ⟨U, trivial, fun x hx i _ => hx i (Set.mem_univ i)⟩
  · intro U _
    exact ⟨⟨Set.univ, U⟩, ⟨Set.finite_univ, trivial⟩, subset_rfl⟩

end OpenNormalSubgroup

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.KummerBasic
namespace GroundTheory.ProfCoh

open Polynomial

section Defs

variable (K : Type*) [Field K] (n : ℕ)

def unitsPow : Subgroup Kˣ := (powMonoidHom n : Kˣ →* Kˣ).range

abbrev UnitsModPow : Type _ := Kˣ ⧸ unitsPow K n

variable {K n} in
lemma mem_unitsPow {a : Kˣ} : a ∈ unitsPow K n ↔ ∃ b : Kˣ, b ^ n = a := by
  simp [unitsPow]

lemma UnitsModPow.pow_eq_one (x : UnitsModPow K n) : x ^ n = 1 := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact mem_unitsPow.mpr ⟨a, rfl⟩

variable (L : Type*) [Field L] [Algebra K L]

def unitsPowIn : Subgroup Kˣ := (unitsPow L n).comap (Units.map (algebraMap K L : K →* L))

variable {K n L} in
lemma mem_unitsPowIn {a : Kˣ} : a ∈ unitsPowIn K n L ↔ ∃ α : L, α ^ n = algebraMap K L a := by
  simp only [unitsPowIn, Subgroup.mem_comap, mem_unitsPow]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by simpa [Units.ext_iff] using congrArg Units.val hb⟩
  · rintro ⟨α, hα⟩
    by_cases h0 : α = 0
    · have hn : n = 0 := by
        by_contra hn
        rw [h0, zero_pow hn] at hα
        exact (map_ne_zero (algebraMap K L)).mpr a.ne_zero hα.symm
      subst hn
      refine ⟨1, ?_⟩
      ext
      simpa using hα
    · exact ⟨Units.mk0 α h0, by ext; simpa using hα⟩

lemma unitsPow_le_unitsPowIn : unitsPow K n ≤ unitsPowIn K n L := by
  intro a ha
  obtain ⟨b, rfl⟩ := mem_unitsPow.mp ha
  exact mem_unitsPowIn.mpr ⟨algebraMap K L b, by simp⟩

def kummerGroup : Subgroup (UnitsModPow K n) :=
  (unitsPowIn K n L).map (QuotientGroup.mk' (unitsPow K n))

variable {K n L} in
lemma mk_mem_kummerGroup {a : Kˣ} :
    (a : UnitsModPow K n) ∈ kummerGroup K n L ↔ ∃ α : L, α ^ n = algebraMap K L a := by
  rw [← mem_unitsPowIn]
  constructor
  · rintro ⟨b, hb, hba⟩
    obtain ⟨c, hc⟩ := mem_unitsPow.mp (QuotientGroup.eq.mp hba)
    have : a = b * c ^ n := by rw [hc]; group
    rw [this]
    exact mul_mem hb (unitsPow_le_unitsPowIn K n L (mem_unitsPow.mpr ⟨c, rfl⟩))
  · intro ha
    exact ⟨a, ha, rfl⟩

end Defs

section RootsOfUnity

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
variable {L : Type*} [Field L] [Algebra K L]

lemma exists_algebraMap_eq_of_pow_eq_one {x : L} (hx : x ^ n = 1) :
    ∃ ζ : rootsOfUnity n K, algebraMap K L ((ζ : Kˣ) : K) = x := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  obtain ⟨i, -, hi⟩ := (hζ.map_of_injective (algebraMap K L).injective).eq_pow_of_pow_eq_one hx
  refine ⟨⟨(hζ.isUnit (NeZero.ne n)).unit ^ i, ?_⟩, ?_⟩
  · rw [mem_rootsOfUnity', Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← pow_mul, mul_comm,
      pow_mul, hζ.pow_eq_one, one_pow]
  · simpa using hi

lemma algHom_apply_eq_self_of_pow_eq_one {x : L} (hx : x ^ n = 1) (σ : L →ₐ[K] L) :
    σ x = x := by
  obtain ⟨ζ, rfl⟩ := exists_algebraMap_eq_of_pow_eq_one (K := K) hx
  exact σ.commutes _

omit [HasEnoughRootsOfUnity K n] in
lemma ne_zero_of_pow_eq_algebraMap {a : Kˣ} {α : L} (hα : α ^ n = algebraMap K L a) : α ≠ 0 := by
  rintro rfl
  rw [zero_pow (NeZero.ne n)] at hα
  exact (map_ne_zero (algebraMap K L)).mpr a.ne_zero hα.symm

end RootsOfUnity

section Pairing

variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (L : Type*) [Field L] [Algebra K L]

lemma exists_kummer_value (σ : Gal(L/K)) (x : kummerGroup K n L) :
    ∃ ζ : rootsOfUnity n K, ∀ a : Kˣ, (a : UnitsModPow K n) = x →
      ∀ α : L, α ^ n = algebraMap K L a → σ α = algebraMap K L ((ζ : Kˣ) : K) * α := by
  obtain ⟨x, a₀, ha₀, rfl⟩ := x
  obtain ⟨α₀, hα₀⟩ := mem_unitsPowIn.mp ha₀
  have hα₀0 : α₀ ≠ 0 := ne_zero_of_pow_eq_algebraMap hα₀
  have hσ : (σ α₀ / α₀) ^ n = 1 := by
    rw [div_pow, ← map_pow, hα₀, AlgEquiv.commutes, div_self]
    exact (map_ne_zero (algebraMap K L)).mpr a₀.ne_zero
  obtain ⟨ζ, hζ⟩ := exists_algebraMap_eq_of_pow_eq_one (K := K) hσ
  refine ⟨ζ, fun a ha α hα => ?_⟩

  obtain ⟨c, hc⟩ := mem_unitsPow.mp (QuotientGroup.eq.mp ha)
  set γ := algebraMap K L (c : K) with hγ
  have hγ0 : γ ≠ 0 := (map_ne_zero (algebraMap K L)).mpr c.ne_zero
  have ha0 : algebraMap K L (a : K) ≠ 0 := (map_ne_zero (algebraMap K L)).mpr a.ne_zero
  have ha' : algebraMap K L (a₀ : K) = algebraMap K L (a : K) * γ ^ n := by
    have h1 : (c : K) ^ n = (a : K)⁻¹ * (a₀ : K) := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
        using congrArg Units.val hc
    have h2 : (a₀ : K) = (a : K) * (c : K) ^ n := by
      rw [h1, ← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul]
    rw [h2, map_mul, map_pow]
  have hη : (α * γ / α₀) ^ n = 1 := by
    rw [div_pow, mul_pow, hα, hα₀, ha']
    exact div_self (mul_ne_zero ha0 (pow_ne_zero _ hγ0))
  have hfix : σ (α * γ / α₀) = α * γ / α₀ :=
    algHom_apply_eq_self_of_pow_eq_one (K := K) hη (σ : L →ₐ[K] L)
  have hσγ : σ γ = γ := σ.commutes _
  have hσα₀ : σ α₀ = algebraMap K L ((ζ : Kˣ) : K) * α₀ := by
    rw [hζ, div_mul_cancel₀ _ hα₀0]
  have hσα₀0 : σ α₀ ≠ 0 := (map_ne_zero σ).mpr hα₀0
  have key : σ α * γ / σ α₀ = α * γ / α₀ := by
    rw [← hfix, map_div₀, map_mul, hσγ]
  calc σ α = (σ α * γ / σ α₀) * (σ α₀ / γ) := by field_simp
    _ = (α * γ / α₀) * (algebraMap K L ((ζ : Kˣ) : K) * α₀ / γ) := by rw [key, hσα₀]
    _ = algebraMap K L ((ζ : Kˣ) : K) * α := by field_simp

noncomputable def kummerPairing (σ : Gal(L/K)) (x : kummerGroup K n L) : rootsOfUnity n K :=
  (exists_kummer_value K n L σ x).choose

variable {K n L}

lemma kummerPairing_spec (σ : Gal(L/K)) (x : kummerGroup K n L) {a : Kˣ}
    (ha : (a : UnitsModPow K n) = x) {α : L} (hα : α ^ n = algebraMap K L a) :
    σ α = algebraMap K L ((kummerPairing K n L σ x : Kˣ) : K) * α :=
  (exists_kummer_value K n L σ x).choose_spec a ha α hα

lemma kummerPairing_eq_of_apply (σ : Gal(L/K)) (x : kummerGroup K n L) {a : Kˣ}
    (ha : (a : UnitsModPow K n) = x) {α : L} (hα : α ^ n = algebraMap K L a)
    (ζ : rootsOfUnity n K) (h : σ α = algebraMap K L ((ζ : Kˣ) : K) * α) :
    kummerPairing K n L σ x = ζ := by
  have h' := kummerPairing_spec σ x ha hα
  rw [h] at h'
  have := mul_right_cancel₀ (ne_zero_of_pow_eq_algebraMap hα) h'
  ext
  exact ((algebraMap K L).injective this).symm

lemma kummerPairing_eq_one_iff (σ : Gal(L/K)) (x : kummerGroup K n L) {a : Kˣ}
    (ha : (a : UnitsModPow K n) = x) {α : L} (hα : α ^ n = algebraMap K L a) :
    kummerPairing K n L σ x = 1 ↔ σ α = α := by
  constructor
  · intro h
    rw [kummerPairing_spec σ x ha hα, h]
    simp
  · intro h
    exact kummerPairing_eq_of_apply σ x ha hα 1 (by rw [h]; simp)

omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma exists_rep (x : kummerGroup K n L) :
    ∃ a : Kˣ, (a : UnitsModPow K n) = x ∧ ∃ α : L, α ^ n = algebraMap K L a := by
  obtain ⟨x, a, ha, rfl⟩ := x
  exact ⟨a, rfl, mem_unitsPowIn.mp ha⟩

lemma kummerPairing_mul_left (σ τ : Gal(L/K)) (x : kummerGroup K n L) :
    kummerPairing K n L (σ * τ) x = kummerPairing K n L σ x * kummerPairing K n L τ x := by
  obtain ⟨a, ha, α, hα⟩ := exists_rep x
  apply kummerPairing_eq_of_apply (σ * τ) x ha hα
  rw [AlgEquiv.mul_apply, kummerPairing_spec τ x ha hα, map_mul, AlgEquiv.commutes,
    kummerPairing_spec σ x ha hα]
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  ring

lemma kummerPairing_mul_right (σ : Gal(L/K)) (x y : kummerGroup K n L) :
    kummerPairing K n L σ (x * y) = kummerPairing K n L σ x * kummerPairing K n L σ y := by
  obtain ⟨a, ha, α, hα⟩ := exists_rep x
  obtain ⟨b, hb, β, hβ⟩ := exists_rep y
  have hab : ((a * b : Kˣ) : UnitsModPow K n) =
      ((x * y : kummerGroup K n L) : UnitsModPow K n) := by
    rw [QuotientGroup.mk_mul, ha, hb]
    rfl
  have hαβ : (α * β) ^ n = algebraMap K L ((a * b : Kˣ) : K) := by
    rw [mul_pow, hα, hβ, Units.val_mul, map_mul]
  apply kummerPairing_eq_of_apply σ (x * y) hab hαβ
  rw [map_mul, kummerPairing_spec σ x ha hα, kummerPairing_spec σ y hb hβ]
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  ring

lemma kummerPairing_one_left (x : kummerGroup K n L) : kummerPairing K n L 1 x = 1 := by
  obtain ⟨a, ha, α, hα⟩ := exists_rep x
  exact (kummerPairing_eq_one_iff 1 x ha hα).mpr rfl

lemma kummerPairing_one_right (σ : Gal(L/K)) : kummerPairing K n L σ 1 = 1 := by
  have h := kummerPairing_mul_right σ (1 : kummerGroup K n L) 1
  rw [mul_one] at h
  exact (mul_eq_left.mp h.symm)

variable (K n L)

noncomputable def kummerPairingLeft : Gal(L/K) →* (kummerGroup K n L →* rootsOfUnity n K) where
  toFun σ :=
    { toFun := kummerPairing K n L σ
      map_one' := kummerPairing_one_right σ
      map_mul' := kummerPairing_mul_right σ }
  map_one' := by ext x : 1; exact kummerPairing_one_left x
  map_mul' σ τ := by ext x : 1; exact kummerPairing_mul_left σ τ x

noncomputable def kummerPairingRight : kummerGroup K n L →* (Gal(L/K) →* rootsOfUnity n K) where
  toFun x :=
    { toFun := fun σ => kummerPairing K n L σ x
      map_one' := kummerPairing_one_left x
      map_mul' := fun σ τ => kummerPairing_mul_left σ τ x }
  map_one' := by ext σ : 1; exact kummerPairing_one_right σ
  map_mul' x y := by ext σ : 1; exact kummerPairing_mul_right σ x y

@[simp] lemma kummerPairingLeft_apply (σ : Gal(L/K)) (x : kummerGroup K n L) :
    kummerPairingLeft K n L σ x = kummerPairing K n L σ x := rfl

end Pairing

section Field

variable (K : Type*) [Field K] (n : ℕ)

def kummerField (Ω : Type*) [Field Ω] [Algebra K Ω] (Δ : Subgroup (UnitsModPow K n)) :
    IntermediateField K Ω :=
  IntermediateField.adjoin K
    {α : Ω | ∃ a : Kˣ, (a : UnitsModPow K n) ∈ Δ ∧ α ^ n = algebraMap K Ω a}

end Field

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.TorsionDualDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Topology

def QZ : Type := AddCircle (1 : ℚ)

namespace QZ

instance : AddCommGroup QZ := inferInstanceAs (AddCommGroup (AddCircle (1 : ℚ)))

instance : TopologicalSpace QZ := ⊥

instance : DiscreteTopology QZ := ⟨rfl⟩

instance : IsTopologicalAddGroup QZ where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

def toAddCircle : QZ ≃+ AddCircle (1 : ℚ) := AddEquiv.refl _

def mk (q : ℚ) : QZ := toAddCircle.symm (q : AddCircle (1 : ℚ))

theorem mk_surjective : Function.Surjective mk := fun x =>
  QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℚ)) (toAddCircle x)

@[simp] theorem mk_add (p q : ℚ) : mk (p + q) = mk p + mk q := by
  simp [mk]

@[simp] theorem mk_zero : mk 0 = 0 := by simp [mk]

theorem mk_eq_zero_iff (q : ℚ) : mk q = 0 ↔ ∃ n : ℤ, (n : ℚ) = q := by
  simp only [mk, AddEquivClass.map_eq_zero_iff, AddCircle.coe_eq_zero_iff, zsmul_eq_mul, mul_one]

end QZ

abbrev QZDual (A : Type*) [AddCommGroup A] [TopologicalSpace A] : Type _ := A →ₜ+ QZ

namespace QZDual

variable {A B C : Type*} [AddCommGroup A] [TopologicalSpace A] [AddCommGroup B]
  [TopologicalSpace B] [AddCommGroup C] [TopologicalSpace C]


end QZDual

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.DiscreteModules
namespace GroundTheory.ProfCoh

open CategoryTheory

universe w u v

variable {k : Type u} {G : Type v} [CommRing k] [Group G]

def stabilizer {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply]

@[simp]
theorem mem_stabilizer {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (v : V) (g : G) : g ∈ stabilizer ρ v ↔ ρ g v = v :=
  Iff.rfl

variable [TopologicalSpace G]

class IsDiscreteRep (A : Rep.{w} k G) : Prop where
  isOpen_stabilizer : ∀ a : A, IsOpen (stabilizer A.ρ a : Set G)

theorem isOpen_stabilizer (A : Rep.{w} k G) [IsDiscreteRep A] (a : A) :
    IsOpen (stabilizer A.ρ a : Set G) :=
  IsDiscreteRep.isOpen_stabilizer a

theorem isDiscreteRep_iff (A : Rep.{w} k G) :
    IsDiscreteRep A ↔ ∀ a : A, IsOpen (stabilizer A.ρ a : Set G) :=
  ⟨fun h => h.isOpen_stabilizer, fun h => ⟨h⟩⟩


variable (k G) in
def isDiscreteRep : ObjectProperty (Rep.{w} k G) := fun A => IsDiscreteRep A


end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.Supernatural
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

def Supernatural : Type := Nat.Primes → ℕ∞

namespace Supernatural

def mk (f : Nat.Primes → ℕ∞) : Supernatural := f

def exp (a : Supernatural) (p : Nat.Primes) : ℕ∞ := a p

private theorem exp_ext {a b : Supernatural} (h : ∀ p, a.exp p = b.exp p) : a = b :=
  funext h

noncomputable instance : CompleteLattice Supernatural := inferInstanceAs (CompleteLattice (Nat.Primes → ℕ∞))

theorem le_def {a b : Supernatural} : a ≤ b ↔ ∀ p, a.exp p ≤ b.exp p := Iff.rfl

@[simp] theorem exp_iSup {ι : Sort*} (f : ι → Supernatural) (p : Nat.Primes) :
    (⨆ i, f i).exp p = ⨆ i, (f i).exp p :=
  iSup_apply (f := fun i => (f i : Nat.Primes → ℕ∞)) (a := p)

instance : One Supernatural := ⟨mk fun _ => 0⟩

instance : Mul Supernatural := ⟨fun a b => mk fun p => a.exp p + b.exp p⟩

@[simp] theorem exp_mul (a b : Supernatural) (p : Nat.Primes) :
    (a * b).exp p = a.exp p + b.exp p := rfl

instance : CommMonoid Supernatural where
  mul_assoc a b c := by exact exp_ext fun p => add_assoc (a.exp p) (b.exp p) (c.exp p)
  one_mul a := by exact exp_ext fun p => zero_add (a.exp p)
  mul_one a := by exact exp_ext fun p => add_zero (a.exp p)
  mul_comm a b := by exact exp_ext fun p => add_comm (a.exp p) (b.exp p)

theorem dvd_iff_le {a b : Supernatural} : a ∣ b ↔ a ≤ b := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [le_def]
    intro p
    simp
  · intro h
    refine ⟨mk fun p => b.exp p - a.exp p, ?_⟩
    exact exp_ext fun p => (add_tsub_cancel_of_le (le_def.mp h p)).symm

def ofNat (n : ℕ) : Supernatural := mk fun p => (n.factorization p : ℕ∞)

@[simp] theorem exp_ofNat (n : ℕ) (p : Nat.Primes) : (ofNat n).exp p = n.factorization p := rfl

theorem ofNat_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : ofNat (m * n) = ofNat m * ofNat n := by
  refine exp_ext fun p => ?_
  simp [Nat.factorization_mul hm hn]

theorem ofNat_dvd_ofNat {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : ofNat m ∣ ofNat n ↔ m ∣ n := by
  rw [dvd_iff_le, le_def, ← Nat.factorization_le_iff_dvd hm hn, Finsupp.le_def]
  constructor
  · intro h q
    by_cases hq : q.Prime
    · have h' : ((m.factorization q : ℕ) : ℕ∞) ≤ n.factorization q := h ⟨q, hq⟩
      exact_mod_cast h'
    · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  · intro h p
    show ((m.factorization p : ℕ) : ℕ∞) ≤ n.factorization p
    exact_mod_cast h p

theorem ofNat_prime_dvd_iff (p : Nat.Primes) (a : Supernatural) :
    ofNat p ∣ a ↔ 1 ≤ a.exp p := by
  have h1 : (ofNat p).exp p = 1 := by
    rw [exp_ofNat]
    simp [p.prop.factorization_self]
  rw [dvd_iff_le, le_def]
  constructor
  · intro h
    exact h1 ▸ h p
  · intro h q
    by_cases hq : q = p
    · subst hq
      exact h1 ▸ h
    · have hq' : (p : ℕ) ≠ q := fun e => hq (Subtype.ext e.symm)
      simp [p.prop.factorization, hq']

theorem ofNat_prime_dvd_iSup_iff (p : Nat.Primes) {ι : Sort*} (f : ι → Supernatural) :
    ofNat p ∣ ⨆ i, f i ↔ ∃ i, ofNat p ∣ f i := by
  simp only [ofNat_prime_dvd_iff p, Order.one_le_iff_ne_zero]
  rw [exp_iSup]
  constructor
  · intro h
    by_contra h'
    simp only [not_exists, ne_eq, not_not] at h'
    exact h (le_antisymm (iSup_le fun i => (h' i).le) zero_le)
  · rintro ⟨i, hi⟩ h
    exact hi (le_antisymm (h ▸ le_iSup (fun i => (f i).exp p) i) zero_le)

theorem iSup_mul_iSup {ι : Sort*} {f g : ι → Supernatural}
    (h : ∀ i j, ∃ k, f i ≤ f k ∧ g j ≤ g k) :
    (⨆ i, f i) * (⨆ i, g i) = ⨆ i, f i * g i := by
  refine exp_ext fun p => ?_
  simp only [exp_mul, exp_iSup]
  exact ENat.iSup_add_iSup fun i j => (h i j).imp fun k hk =>
    add_le_add (le_def.mp hk.1 p) (le_def.mp hk.2 p)

end Supernatural

end GroundTheory.ProfCoh
end
