module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.FinCoh
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsG
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrand

@[expose] public section

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsCT
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

section Cyclic

variable {R : Type} [CommRing R] {C : Type} [Group C] [Fintype C] [TopologicalSpace C] [IsTopologicalGroup C] [DiscreteTopology C]

theorem cyc_odd (M : TRep R C) (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (hi : Odd i) :
    Nonempty (M.H i ≃ₗ[R] (LinearMap.ker M.rho.norm ⧸
      (LinearMap.range (M.rho g - LinearMap.id)).comap (LinearMap.ker M.rho.norm).subtype)) := by
  have : IsCyclic C := ⟨g, hg⟩
  let : CommGroup C := IsCyclic.commGroup
  exact nonempty_cyclic_odd M g hg i hi

theorem cyc_even (M : TRep R C) (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (h0 : i ≠ 0)
    (hi : Even i) :
    Nonempty (M.H i ≃ₗ[R] (M.rho.invariants ⧸
      (LinearMap.range M.rho.norm).comap M.rho.invariants.subtype)) := by
  have : IsCyclic C := ⟨g, hg⟩
  let : CommGroup C := IsCyclic.commGroup
  exact nonempty_cyclic_even M g hg i h0 hi

theorem norm_apply' (M : TRep R C) (u : M.V) : M.rho.norm u = ∑ c, M.rho c u := by
  simp [Representation.norm]

theorem exists_sub_eq_of_cyclic_of_h1_subsingleton (M : TRep R C) (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g) (h1 : Subsingleton (M.H 1))
    (u : M.V) (hu : ∑ c, M.rho c u = 0) : ∃ w, M.rho g w - w = u := by
  obtain ⟨e⟩ := cyc_odd M g hg 1 (by decide)
  have hs := e.symm.injective.subsingleton
  rw [Submodule.Quotient.subsingleton_iff] at hs
  have hk : u ∈ LinearMap.ker M.rho.norm := by rw [LinearMap.mem_ker, norm_apply', hu]
  have hm : (⟨u, hk⟩ : LinearMap.ker M.rho.norm) ∈
      (LinearMap.range (M.rho g - LinearMap.id)).comap (LinearMap.ker M.rho.norm).subtype := by
    rw [hs]; exact Submodule.mem_top
  obtain ⟨w, hw⟩ := hm
  exact ⟨w, hw⟩

theorem cyc_subsingleton (M : TRep R C) (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hN : ∀ u, (∀ c, M.rho c u = u) → ∃ w, ∑ c, M.rho c w = u)
    (hD : ∀ u, ∑ c, M.rho c u = 0 → ∃ w, M.rho g w - w = u) (i : ℕ) (hi : 0 < i) :
    Subsingleton (M.H i) := by
  rcases Nat.even_or_odd i with h | h
  · obtain ⟨e⟩ := cyc_even M g hg i hi.ne' h
    have : Subsingleton (M.rho.invariants ⧸
        (LinearMap.range M.rho.norm).comap M.rho.invariants.subtype) := by
      rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
      rintro ⟨u, hu⟩ -
      obtain ⟨w, hw⟩ := hN u hu
      exact ⟨w, by rw [norm_apply', hw]; rfl⟩
    exact e.injective.subsingleton
  · obtain ⟨e⟩ := cyc_odd M g hg i h
    have : Subsingleton (LinearMap.ker M.rho.norm ⧸
        (LinearMap.range (M.rho g - LinearMap.id)).comap (LinearMap.ker M.rho.norm).subtype) := by
      rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
      rintro ⟨u, hu⟩ -
      obtain ⟨w, hw⟩ := hD u (by rw [← norm_apply']; exact hu)
      exact ⟨w, hw⟩
    exact e.injective.subsingleton

end Cyclic

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K}

theorem exists_frob_sub_eq_of_sum_eq_zero_layerU (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n)
    [Fintype (GalLK p K (Kn p K n))] (u : (layerU p K (Kn p K n)).V)
    (hu : ∑ g, (layerU p K (Kn p K n)).rho g u = 0) :
    ∃ w, (layerU p K (Kn p K n)).rho (frobLK p K (Kn p K n)) w - w = u := by
  have hL := finiteDimensional_Kn p K hK hn
  have hKL : K ≤ Kn p K n := le_sup_left
  have := discreteTopology_GalLK (K := K) hL
  have hg := mem_zpowers_frobLK_Kn hK hn
  have h1 : Subsingleton ((layer p K (Kn p K n)).H 1) :=
    quotient_multiplicative_h1_subsingleton p K _ _ _ (InflationRestrictionInvariants.invariants_isInvRep _ _)
  have hI : ∀ g x, (layerUIncl p K (Kn p K n)).u ((layerU p K (Kn p K n)).rho g x) =
      (layer p K (Kn p K n)).rho g ((layerUIncl p K (Kn p K n)).u x) :=
    (layerUIncl p K (Kn p K n)).equiv
  obtain ⟨w, hw⟩ := exists_sub_eq_of_cyclic_of_h1_subsingleton (layer p K (Kn p K n)) _ hg h1 ((layerUIncl p K (Kn p K n)).u u) (by
    simp only [← hI]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hu, map_zero])
  obtain ⟨π, hπ⟩ := vOn_surjective p K hK 1
  have hπL : π.1 ∈ multOf p (Kn p K n) := hKL π.2
  let π' : (layer p K (Kn p K n)).V := toLayer p ⟨π.1, hπL⟩
  have hπ' : vLayerMap p K (Kn p K n) π' = 1 := by
    rw [vLayerMap_of_mem p hL hKL π' π.2, eLK_Kn p hK hn]
    show ((1 : ℕ) : ℤ) * vOn p K π = 1
    rw [hπ]; simp
  have hfix : ∀ g, (layer p K (Kn p K n)).rho g π' = π' := (layer_invariant_iff π').2 π.2
  have he : 0 < eK p (Kn p K n) := eK_pos p _ hL
  have h0 : vLayerMap p K (Kn p K n) (w - vLayerMap p K (Kn p K n) w • π') = 0 := by
    rw [map_sub, map_zsmul, hπ']; simp
  obtain ⟨w', hw'⟩ := (vLayerMap_eq_zero_iff p he hKL _).1 h0
  refine ⟨w', layerUIncl_injective p ?_⟩
  rw [map_sub, hI, hw', map_sub, map_zsmul, hfix, ← hw]
  abel

theorem layerU_Kn_norm_surjective (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n)
    [Fintype (GalLK p K (Kn p K n))] (u : (layerU p K (Kn p K n)).V)
    (hu : ∀ g, (layerU p K (Kn p K n)).rho g u = u) :
    ∃ w, ∑ g, (layerU p K (Kn p K n)).rho g w = u := by
  have hL := finiteDimensional_Kn p K hK hn
  have hKL : K ≤ Kn p K n := le_sup_left
  have hg := mem_zpowers_frobLK_Kn hK hn
  obtain ⟨hfin, h1⟩ := herbrand_layerU hK hL hKL _ hg
  have : Subsingleton (Herbrand.H1 (layerU p K (Kn p K n)).rho (frobLK p K (Kn p K n))) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [Herbrand.mk_eq_mk_iff]
    have hxy : ∑ g, (layerU p K (Kn p K n)).rho g ((x : (layerU p K (Kn p K n)).V) - y) = 0 := by
      rw [← Herbrand.nHom_apply, map_sub]
      rw [show Herbrand.nHom (layerU p K (Kn p K n)).rho x = 0 from x.2,
        show Herbrand.nHom (layerU p K (Kn p K n)).rho y = 0 from y.2, sub_zero]
    obtain ⟨w, hw⟩ := exists_frob_sub_eq_of_sum_eq_zero_layerU hK hn _ hxy
    exact ⟨w, hw⟩
  rw [Herbrand.h_eq_card_H0hat] at h1
  have h2 : Nat.card (Herbrand.TateZerothCohomology (layerU p K (Kn p K n)).rho (frobLK p K (Kn p K n))) = 1 := by
    exact_mod_cast h1
  have := hfin.1
  have h3 := (Nat.card_eq_one_iff_unique.1 h2).1
  have hk : u ∈ (Herbrand.dHom (layerU p K (Kn p K n)).rho (frobLK p K (Kn p K n))).ker :=
    (Herbrand.mem_ker_dHom_iff _ _ hg u).2 hu
  have h4 := (Herbrand.mk_eq_zero_iff (N := Herbrand.nHom (layerU p K (Kn p K n)).rho) ⟨u, hk⟩).1
    (Subsingleton.elim _ _)
  obtain ⟨w, hw⟩ := h4
  exact ⟨w, by rw [← Herbrand.nHom_apply]; exact hw⟩

theorem layerU_Kn_H_subsingleton (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (i : ℕ) (hi : 0 < i) :
    Subsingleton ((layerU p K (Kn p K n)).H i) := by
  have hL := finiteDimensional_Kn p K hK hn
  have := discreteTopology_GalLK (K := K) hL
  have := finite_GalLK (K := K) hL
  let := Fintype.ofFinite (GalLK p K (Kn p K n))
  exact cyc_subsingleton _ _ (mem_zpowers_frobLK_Kn hK hn) (layerU_Kn_norm_surjective hK hn)
    (exists_frob_sub_eq_of_sum_eq_zero_layerU hK hn) i hi

theorem layerU_Kur_level (hK : FiniteDimensional ℚ_[p] K) (N : Subgroup (GalLK p K (MaximalUnramifiedExtension p K))) [N.Normal]
    (hN : IsOpen (N : Set (GalLK p K (MaximalUnramifiedExtension p K)))) (i : ℕ) (hi : 0 < i) :
    Subsingleton ((InflationRestrictionInvariants.invQ (layerU p K (MaximalUnramifiedExtension p K)) N).H i) := by
  obtain ⟨n, hn, hU⟩ := exists_Kn_of_isOpen hK (N.comap (QuotientGroup.mk' (subG p K (MaximalUnramifiedExtension p K))))
    (hN.preimage continuous_quot_mk) (fun σ hσ => by
      show (QuotientGroup.mk σ : GalLK p K (MaximalUnramifiedExtension p K)) ∈ N
      rw [(QuotientGroup.eq_one_iff σ).2 hσ]
      exact N.one_mem)
  have hU' : ∀ σ : GK p K, (QuotientGroup.mk σ : GalLK p K (MaximalUnramifiedExtension p K)) ∈ N ↔ σ ∈ subG p K (Kn p K n) :=
    fun σ => by rw [← hU]; rfl
  have hL := finiteDimensional_Kn p K hK hn
  have := discreteTopology_GalLK (K := K) hL
  have := QuotientGroup.discreteTopology hN
  have : DiscreteTopology (InflationRestrictionInvariants.invQ (layerU p K (MaximalUnramifiedExtension p K)) N).V :=
    (InflationRestrictionInvariants.invariants_isInvRep (layerU p K (MaximalUnramifiedExtension p K)) N).2.1.discreteTopology
  let θ : GalLK p K (Kn p K n) →* GalLK p K (MaximalUnramifiedExtension p K) ⧸ N :=
    QuotientGroup.lift (subG p K (Kn p K n))
      ((QuotientGroup.mk' N).comp (QuotientGroup.mk' (subG p K (MaximalUnramifiedExtension p K))))
      (fun σ hσ => (QuotientGroup.eq_one_iff _).2 ((hU' σ).2 hσ))
  have hθ : Bijective θ := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro g hg
      induction g using QuotientGroup.induction_on with
      | H σ => exact (QuotientGroup.eq_one_iff σ).2 ((hU' σ).1 ((QuotientGroup.eq_one_iff _).1 hg))
    · intro g
      induction g using QuotientGroup.induction_on with
      | H g =>
        induction g using QuotientGroup.induction_on with
        | H σ => exact ⟨QuotientGroup.mk σ, rfl⟩
  let u : (InflationRestrictionInvariants.invQ (layerU p K (MaximalUnramifiedExtension p K)) N).V →+ (layerU p K (Kn p K n)).V :=
    { toFun := fun x => ⟨x.1.1, fun σ => congrArg Subtype.val (x.2 ⟨QuotientGroup.mk σ.1, (hU' σ.1).2 σ.2⟩)⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hu : Bijective u := by
    constructor
    · intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : (layerU p K (Kn p K n)).V => z.1) hxy))
    · intro z
      refine ⟨⟨⟨z.1, fun σ => z.2 ⟨σ.1, subG_anti (Kn_le_Kur hn) σ.2⟩⟩, fun g => ?_⟩, rfl⟩
      obtain ⟨g, hg⟩ := g
      induction g using QuotientGroup.induction_on with
      | H σ => exact Subtype.ext (z.2 ⟨σ, (hU' σ).1 hg⟩)
  let R : Pair (InflationRestrictionInvariants.invQ (layerU p K (MaximalUnramifiedExtension p K)) N) (layerU p K (Kn p K n)) :=
    { φ := θ
      u := mkLin (A := InflationRestrictionInvariants.invQ (layerU p K (MaximalUnramifiedExtension p K)) N) (B := layerU p K (Kn p K n)) u
      φ_cont := continuous_of_discreteTopology
      u_cont := continuous_of_discreteTopology
      equiv := fun g m => by
        induction g using QuotientGroup.induction_on with
        | H σ => rfl }
  have hb := pair_H_bijective R ⟨continuous_of_discreteTopology, fun _ _ => isOpen_discrete _, hθ⟩
    ⟨continuous_of_discreteTopology, fun _ _ => isOpen_discrete _, hu⟩ i
  have := layerU_Kn_H_subsingleton hK hn i hi
  exact hb.1.subsingleton

theorem layerU_Kur_H_subsingleton (hK : FiniteDimensional ℚ_[p] K) (i : ℕ) (hi : 0 < i) :
    Subsingleton ((layerU p K (MaximalUnramifiedExtension p K)).H i) := by
  have h0 : ∀ x : (layerU p K (MaximalUnramifiedExtension p K)).H i, x = 0 := fun x => by
    obtain ⟨⟨N, hNn, hNo, h⟩, -⟩ := finiteLevel_holds ℤ (GalLK p K (MaximalUnramifiedExtension p K)) (layerU p K (MaximalUnramifiedExtension p K)) i x
    obtain ⟨y, rfl⟩ := h _ _ (InflationRestrictionInvariants.invariants_isInvRep (layerU p K (MaximalUnramifiedExtension p K)) N)
    have := layerU_Kur_level hK N hNo i hi
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨fun x y => by rw [h0 x, h0 y]⟩

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.BrUnrA
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function

noncomputable section

theorem bijective_H_of_adm {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B C : TRep ℤ G}
    {i : Pair A B} {q : Pair B C} (h : admitted i q) (n : ℕ) (h1 : Subsingleton (A.H n))
    (h2 : Subsingleton (A.H (n + 1))) : Bijective (q.hom.H n) := by
  have hs := admissibility_holds ℤ G _ _ _ _ _ h
  obtain ⟨⟨δ, -, hl⟩, -⟩ := lES_holds ℤ _ _ _ _ _ hs
  constructor
  · set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (hl.exB n x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  · intro y
    exact (hl.exC n y).1 (Subsingleton.elim _ _)

theorem card_QZ_torsion (n : ℕ) (hn : 0 < n) : Nat.card {a : QZ // n • a = 0} = n := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  let f : ℤ →+ QZ := (QuotientAddGroup.mk' (Int.castAddHom ℚ).range).comp
    ((AddMonoidHom.mulRight (1 / (n : ℚ))).comp (Int.castAddHom ℚ))
  have hf : ∀ k : ℤ, f k = QuotientAddGroup.mk ((k : ℚ) * (1 / (n : ℚ))) := fun _ => rfl
  have hker : f.ker = AddSubgroup.zmultiples (n : ℤ) := by
    ext k
    rw [AddMonoidHom.mem_ker, hf, QuotientAddGroup.eq_zero_iff, Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      have hj' : (j : ℚ) = (k : ℚ) * (1 / (n : ℚ)) := hj
      have : (k : ℚ) = (n : ℚ) * j := by rw [hj']; field_simp
      exact_mod_cast this
    · rintro ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      show (j : ℚ) = (((n : ℤ) * j : ℤ) : ℚ) * (1 / (n : ℚ))
      push_cast
      field_simp
  have hr : ∀ a : QZ, n • a = 0 ↔ a ∈ f.range := by
    intro a
    constructor
    · intro ha
      obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective a
      have h1 : ((n • q : ℚ) : QZ) = 0 := ha
      rw [QuotientAddGroup.eq_zero_iff] at h1
      obtain ⟨j, hj⟩ := h1
      have hj' : (j : ℚ) = n • q := hj
      refine ⟨j, ?_⟩
      rw [hf, hj', nsmul_eq_mul]
      congr 1
      field_simp
    · rintro ⟨k, rfl⟩
      rw [hf]
      show ((n • ((k : ℚ) * (1 / (n : ℚ))) : ℚ) : QZ) = 0
      rw [QuotientAddGroup.eq_zero_iff]
      refine ⟨k, ?_⟩
      show (k : ℚ) = n • ((k : ℚ) * (1 / (n : ℚ)))
      rw [nsmul_eq_mul]
      field_simp
  have hc : Nat.card f.range = n := by
    rw [← AddSubgroup.index_ker, hker, Int.index_zmultiples]
    simp
  exact (Nat.card_congr (Equiv.subtypeEquivRight hr)).trans hc

theorem card_h2_trivial_int_cyclic (C : Type) [Group C] [Finite C] [TopologicalSpace C] [IsTopologicalGroup C]
    [DiscreteTopology C] (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ((trivRep C ℤ).H 2) = Nat.card C := by
  let _ : CommGroup C :=
    { (inferInstance : Group C) with
      mul_comm := fun a b => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
        rw [← zpow_add, ← zpow_add, add_comm] }
  let _ : Fintype C := Fintype.ofFinite C
  obtain ⟨e⟩ := nonempty_cyclic_even (trivRep C ℤ) g hg 2 two_ne_zero even_two
  rw [Nat.card_congr e.toEquiv]
  have hinv : ∀ k : ℤ, (k : (trivRep C ℤ).V) ∈ (trivRep C ℤ).rho.invariants := fun k _ => rfl
  let f : ℤ →+ ((trivRep C ℤ).rho.invariants ⧸
      (LinearMap.range (trivRep C ℤ).rho.norm).comap (trivRep C ℤ).rho.invariants.subtype) :=
    { toFun := fun k => Submodule.Quotient.mk ⟨k, hinv k⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hnorm : ∀ k : (trivRep C ℤ).V, (trivRep C ℤ).rho.norm k = ((Nat.card C : ℤ) * (show ℤ from k) : ℤ) := by
    intro k
    have h0 : ∀ g : C, (trivRep C ℤ).rho g k = k := fun _ => rfl
    rw [Representation.norm, LinearMap.sum_apply, Finset.sum_congr rfl (fun g _ => h0 g), Finset.sum_const,
      Finset.card_univ, Nat.card_eq_fintype_card]
    exact nsmul_eq_mul (Fintype.card C) (show ℤ from k)
  have hsurj : Surjective f := by
    intro y
    obtain ⟨⟨k, hk⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨k, rfl⟩
  have hker : f.ker = AddSubgroup.zmultiples (Nat.card C : ℤ) := by
    ext k
    rw [AddMonoidHom.mem_ker, Int.mem_zmultiples_iff]
    show Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, ((hnorm j).symm.trans hj).symm⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, (hnorm j).trans hj.symm⟩
  have h1 : Nat.card f.range = Nat.card C := by
    rw [← AddSubgroup.index_ker, hker, Int.index_zmultiples]
    simp
  rw [← h1, AddMonoidHom.range_eq_top.2 hsurj]
  exact (Nat.card_congr (Equiv.Set.univ _)).symm

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G']

def trivInfl (φ : G' →* G) (hφ : Continuous φ) (A : Type) [AddCommGroup A] :
    Pair (trivRep G A) (trivRep G' A) where
  φ := φ
  u := (LinearMap.id : A →ₗ[ℤ] A)
  φ_cont := hφ
  u_cont := continuous_of_discreteTopology
  equiv _ _ := rfl

theorem trivial_inflation_h1_rat_mod_int_injective (φ : G' →* G) (hφ : Continuous φ) (hs : Surjective φ) :
    Injective ((trivInfl φ hφ QZ).hom.H 1) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨x, hx, rfl⟩ := Cx.exists_cls c
  obtain ⟨e, he⟩ := exists_h1_equiv_characters G
  obtain ⟨e', he'⟩ := exists_h1_equiv_characters G'
  apply e.injective
  rw [e.map_zero]
  refine Subtype.ext (AddMonoidHom.ext fun a => ?_)
  obtain ⟨g', hg'⟩ := hs a.toMul
  rw [Cx.Hom.H_cls] at hc
  have h1 := he' _ ((trivInfl φ hφ QZ).hom.d_f_eq_zero hx) g'
  rw [hc, e'.map_zero] at h1
  have h2 := he x hx (φ g')
  rw [hg'] at h2
  have h3 : (fun i => φ ((![g'] : Fin 1 → G') i)) = ![a.toMul] := by
    funext i; fin_cases i; exact hg'
  have h4 : (((trivInfl φ hφ QZ).hom.f 1 x).1 ![g'] : QZ) = x.1 ![a.toMul] := congrArg x.1 h3
  exact h2.trans (h4.symm.trans h1.symm)

theorem trivial_inflation_h2_int_injective [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [CompactSpace G']
    [T2Space G'] [TotallyDisconnectedSpace G'] (φ : G' →* G) (hφ : Continuous φ) (hs : Surjective φ) :
    Injective ((trivInfl φ hφ ℤ).hom.H 2) := by
  have hadm (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] :
      admitted (trivMap K (Int.castAddHom ℚ))
        (trivMap K (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)) := by
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · have hi : Injective (trivMap K (Int.castAddHom ℚ)).u := Int.cast_injective (α := ℚ)
      exact (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_of_discreteTopology hi
        (fun _ _ => isOpen_discrete _)).isEmbedding
    · intro (y : ℚ)
      show (QuotientAddGroup.mk y : QZ) = 0 ↔ y ∈ (Int.castAddHom ℚ).range
      exact QuotientAddGroup.eq_zero_iff y
    · have hq := QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range
      exact ⟨Function.surjInv hq, continuous_of_discreteTopology, Function.surjInv_eq hq⟩
  have s := admissibility_holds ℤ G _ _ _ _ _ (hadm G)
  have s' := admissibility_holds ℤ G' _ _ _ _ _ (hadm G')
  obtain ⟨⟨δ, h1, -⟩, -⟩ := lES_holds ℤ _ _ _ _ _ s
  obtain ⟨⟨δ', h1', -⟩, -⟩ := lES_holds ℤ _ _ _ _ _ s'
  have hnat := connNat_holds ℤ _ _ _ _ _ _ _ _ _ _ (trivInfl φ hφ ℤ).hom (trivInfl φ hφ ℚ).hom
    (trivInfl φ hφ QZ).hom δ δ' s s' (fun _ _ => rfl) (fun _ _ => rfl) h1 h1' 1
  intro a b hab
  obtain ⟨a', rfl⟩ := (conn_int_rat_bijective G δ h1 1 one_pos).2 a
  obtain ⟨b', rfl⟩ := (conn_int_rat_bijective G δ h1 1 one_pos).2 b
  have hab' : δ' 1 ((trivInfl φ hφ QZ).hom.H 1 a') = δ' 1 ((trivInfl φ hφ QZ).hom.H 1 b') :=
    (hnat a').trans (hab.trans (hnat b').symm)
  rw [trivial_inflation_h1_rat_mod_int_injective φ hφ hs ((conn_int_rat_bijective G' δ' h1' 1 one_pos).1 hab')]

theorem conn_cls_of_lift (δ)
    (hδ : Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ)
    (t : G → ℚ) (ht : IsLocallyConstant t) (m : (Fin 2 → G) → ℤ)
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) :
    ∃ (x : (trivRep G QZ).coch.X 1) (hx : (trivRep G QZ).coch.d 1 x = 0) (y : (trivRep G ℤ).coch.X 2)
      (hy : (trivRep G ℤ).coch.d 2 y = 0), (∀ g, x.1 g = (QuotientAddGroup.mk (t (g 0)) : QZ)) ∧ y.1 = m ∧
      δ 1 ((trivRep G QZ).coch.cls 1 x hx) = (trivRep G ℤ).coch.cls 2 y hy := by
  have hb : @Continuous _ (trivRep G ℚ).V _ _ (fun g : Fin 1 → G => t (g 0)) :=
    IsLocallyConstant.continuous (Y := (trivRep G ℚ).V) (ht.comp_continuous (continuous_apply 0))
  let b : (trivRep G ℚ).coch.X 1 := ⟨fun g => t (g 0), hb⟩
  have hmc : IsLocallyConstant m := by
    apply IsLocallyConstant.desc m (Int.cast : ℤ → ℚ) _ Int.cast_injective
    have h0 : ((Int.cast : ℤ → ℚ) ∘ m) = fun g => t (g 0) + t (g 1) - t (g 0 * g 1) := funext hm
    rw [h0]
    exact ((ht.comp_continuous (continuous_apply 0)).add (ht.comp_continuous (continuous_apply 1))).sub
      (ht.comp_continuous ((continuous_apply 0).mul (continuous_apply 1)))
  let a : (trivRep G ℤ).coch.X 2 := ⟨m, hmc.continuous⟩
  have hba : (trivRep G ℚ).coch.d 1 b = (trivMap G (Int.castAddHom ℚ)).hom.f 2 a := by
    apply Subtype.ext
    funext g
    show Gal.dn (trivRep G ℚ).rho 1 b.1 g = ((m (fun i => g i) : ℤ) : ℚ)
    rw [LowDeg.dn_one_apply]
    show t (g 1) - t (g 0 * g 1) + t (g 0) = _
    rw [hm]; ring
  have ha : (trivRep G ℤ).coch.d 2 a = 0 := by
    let i := (trivMap G (Int.castAddHom ℚ)).hom
    have hd : i.f 3 ((trivRep G ℤ).coch.d 2 a) = 0 := by
      rw [i.comm, ← hba, (trivRep G ℚ).coch.dd]
    apply Subtype.ext
    funext g
    apply Int.cast_injective (α := ℚ)
    exact congrArg (fun z => z.1 g) hd
  have hc : (trivRep G QZ).coch.d 1 ((trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom.f 1 b) = 0 := by
    rw [← (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom.comm, hba]
    apply Subtype.ext
    funext g
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨a.1 g, rfl⟩
  exact ⟨_, hc, a, ha, fun g => rfl, rfl, hδ 1 b a hc ha hba⟩

theorem exists_cocycle_form [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (c : (trivRep G ℤ).H 2) :
    ∃ (t : G → ℚ) (m : (Fin 2 → G) → ℤ) (y : (trivRep G ℤ).coch.X 2) (hy : (trivRep G ℤ).coch.d 2 y = 0),
      IsLocallyConstant t ∧ (∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) ∧ y.1 = m ∧
      c = (trivRep G ℤ).coch.cls 2 y hy := by
  have hadm : admitted (trivMap G (Int.castAddHom ℚ))
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)) := by
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · have hi : Injective (trivMap G (Int.castAddHom ℚ)).u := Int.cast_injective (α := ℚ)
      exact (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_of_discreteTopology hi
        (fun _ _ => isOpen_discrete _)).isEmbedding
    · intro (y : ℚ)
      show (QuotientAddGroup.mk y : QZ) = 0 ↔ y ∈ (Int.castAddHom ℚ).range
      exact QuotientAddGroup.eq_zero_iff y
    · have hq := QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range
      exact ⟨Function.surjInv hq, continuous_of_discreteTopology, Function.surjInv_eq hq⟩
  have s := admissibility_holds ℤ G _ _ _ _ _ hadm
  obtain ⟨⟨δ, h1, -⟩, -⟩ := lES_holds ℤ _ _ _ _ _ s
  obtain ⟨c', rfl⟩ := (conn_int_rat_bijective G δ h1 1 one_pos).2 c
  obtain ⟨x, hx, rfl⟩ := Cx.exists_cls c'
  let sec : QZ → ℚ := Function.surjInv (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range)
  have hsec : ∀ q : QZ, (QuotientAddGroup.mk (sec q) : QZ) = q :=
    Function.surjInv_eq (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range)
  let t : G → ℚ := fun g => sec (x.1 ![g])
  have hx1 : Continuous x.1 := x.2
  have ht : IsLocallyConstant t := by
    have h0 : IsLocallyConstant fun g : G => x.1 ![g] :=
      (IsLocallyConstant.iff_continuous _).2 (hx1.comp (continuous_pi fun i => by fin_cases i; exact continuous_id))
    exact h0.comp sec
  obtain ⟨χ, hχ⟩ : ∃ χ : G → QZ, ∀ g, χ g = x.1 ![g] := ⟨fun g => x.1 ![g], fun _ => rfl⟩
  have ht' : ∀ g, (QuotientAddGroup.mk (t g) : QZ) = χ g := fun g => (hsec _).trans (hχ g).symm
  have hcoc : ∀ g : Fin 2 → G, χ (g 1) - χ (g 0 * g 1) + χ (g 0) = 0 := by
    intro g
    have h0 := congrFun (LowDeg.dn_eq_zero _ hx) g
    rw [LowDeg.dn_one_apply] at h0
    rw [hχ, hχ, hχ]
    exact h0
  have hex : ∀ g : Fin 2 → G, ∃ k : ℤ, (k : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := by
    intro g
    have h0 : (QuotientAddGroup.mk (t (g 0) + t (g 1) - t (g 0 * g 1)) : QZ) = 0 := by
      rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add, ht', ht', ht', ← hcoc g]
      abel
    exact (QuotientAddGroup.eq_zero_iff _).1 h0
  choose m hm using hex
  obtain ⟨x', hx', y, hy, e1, e2, e3⟩ := conn_cls_of_lift δ h1 t ht m hm
  have hxx : x' = x := by
    apply Subtype.ext
    funext g
    exact (e1 g).trans ((ht' (g 0)).trans ((hχ (g 0)).trans (congrArg x.1 (by funext i; fin_cases i; rfl))))
  subst hxx
  exact ⟨t, m, y, hy, ht, hm, e2, e3⟩

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K}

theorem admissible_valuation_layer {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (he : 0 < eK p L) (h : K ≤ L)
    [(subG p K L).Normal] : admitted (layerUIncl p K L) (vLayer p K L) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · exact (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_of_discreteTopology
      (layerUIncl_injective p) fun _ _ => isOpen_discrete _).isEmbedding
  · intro y
    rw [← LinearMap.mem_ker, ker_vLayer p he h]
    rfl
  · exact ⟨Function.surjInv (vLayer_surjective p he h), continuous_of_discreteTopology, Function.surjInv_eq _⟩

theorem eK_Kn_pos (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : 0 < eK p (Kn p K n) := by
  rw [eK_Kn p hK hn]; exact eK_pos p K hK

theorem eK_Kur_pos (hK : FiniteDimensional ℚ_[p] K) : 0 < eK p (MaximalUnramifiedExtension p K) := by
  rw [eK_Kur p hK]; exact eK_pos p K hK

theorem valuation_unramified_layer_h2_bijective (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Bijective ((vLayer p K (Kn p K n)).hom.H 2) :=
  bijective_H_of_adm (admissible_valuation_layer (eK_Kn_pos hK hn) le_sup_left) 2
    (layerU_Kn_H_subsingleton hK hn 2 two_pos) (layerU_Kn_H_subsingleton hK hn 3 three_pos)

theorem valuation_unramified_closure_h2_bijective (hK : FiniteDimensional ℚ_[p] K) :
    Bijective ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2) :=
  bijective_H_of_adm (admissible_valuation_layer (eK_Kur_pos hK) le_Kur) 2
    (layerU_Kur_H_subsingleton hK 2 two_pos) (layerU_Kur_H_subsingleton hK 3 three_pos)

theorem card_h2_unramified_layer (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Nat.card ((layer p K (Kn p K n)).H 2) = n := by
  have hL := finiteDimensional_Kn p K hK hn
  have := discreteTopology_GalLK (K := K) hL
  have := finite_GalLK (K := K) hL
  rw [Nat.card_congr (Equiv.ofBijective _ (valuation_unramified_layer_h2_bijective hK hn)),
    card_h2_trivial_int_cyclic _ (frobLK p K (Kn p K n)) (mem_zpowers_frobLK_Kn hK hn), card_GalLK, degLK_Kn hK hn]

theorem vLayerMap_Kur_eq_one (hK : FiniteDimensional ℚ_[p] K) (π : (urT p K).V)
    (hπ : (eK p K : ℝ) * vbar p π.1 = 1) : vLayerMap p K (MaximalUnramifiedExtension p K) π = 1 := by
  apply Int.cast_injective (α := ℝ)
  rw [vLayerMap_spec p le_Kur, eK_Kur p hK, hπ, Int.cast_one]

theorem vLayer_Kur_cls (hK : FiniteDimensional ℚ_[p] K) (π : (urT p K).V)
    (hπ : (eK p K : ℝ) * vbar p π.1 = 1) (m : (Fin 2 → GalLK p K (MaximalUnramifiedExtension p K)) → ℤ)
    (z : (urT p K).coch.X 2) (hz : (urT p K).coch.d 2 z = 0) (hzm : ∀ g, z.1 g = m g • π)
    (y : (trivRep (GalLK p K (MaximalUnramifiedExtension p K)) ℤ).coch.X 2) (hy : (trivRep (GalLK p K (MaximalUnramifiedExtension p K)) ℤ).coch.d 2 y = 0)
    (hym : y.1 = m) :
    (vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 ((urT p K).coch.cls 2 z hz) =
      (trivRep (GalLK p K (MaximalUnramifiedExtension p K)) ℤ).coch.cls 2 y hy := by
  rw [Cx.Hom.H_cls]
  apply Cx.cls_congr
  apply Subtype.ext
  funext g
  show vLayerMap p K (MaximalUnramifiedExtension p K) (z.1 fun i => g i) = y.1 g
  rw [hym, hzm, map_zsmul, vLayerMap_Kur_eq_one hK π hπ]
  simp

theorem exists_invariant_of_connecting_map (hK : FiniteDimensional ℚ_[p] K) :
    ∃ f : (urT p K).H 2 ≃+ QZ, IsInv p K f.toAddMonoidHom ∧
      ∀ δ, Cx.IsConn (trivMap (GalLK p K (MaximalUnramifiedExtension p K)) (Int.castAddHom ℚ)).hom
        (trivMap (GalLK p K (MaximalUnramifiedExtension p K)) (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ →
      ∀ (c : (urT p K).H 2) (x) (hx),
        (vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 c = δ 1 ((trivRep (GalLK p K (MaximalUnramifiedExtension p K)) QZ).coch.cls 1 x hx) →
        f c = x.1 ![frobLK p K (MaximalUnramifiedExtension p K)] := by
  obtain ⟨e, he⟩ := exists_h2_int_equiv_rat_mod_int (GalLK p K (MaximalUnramifiedExtension p K)) (frobLK p K (MaximalUnramifiedExtension p K)) (isZHat_GalKur hK)
  refine ⟨(AddEquiv.ofBijective ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2).toAddMonoidHom
    (valuation_unramified_closure_h2_bijective hK)).trans e, ?_, ?_⟩
  · intro π t m z hz _ hπ ht hm hzm
    have hadm : admitted
        (trivMap (GalLK p K (MaximalUnramifiedExtension p K)) (Int.castAddHom ℚ))
        (trivMap _ (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)) := by
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩
      · have hi : Injective (trivMap (GalLK p K (MaximalUnramifiedExtension p K)) (Int.castAddHom ℚ)).u :=
          Int.cast_injective (α := ℚ)
        exact (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap continuous_of_discreteTopology
          hi fun _ _ => isOpen_discrete _).isEmbedding
      · intro (y : ℚ)
        show (QuotientAddGroup.mk y : QZ) = 0 ↔ y ∈ Set.range (Int.castAddHom ℚ)
        rw [QuotientAddGroup.eq_zero_iff]
        rfl
      · exact ⟨Function.surjInv (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range),
          continuous_of_discreteTopology, Function.surjInv_eq _⟩
    have s := admissibility_holds ℤ _ _ _ _ _ _ hadm
    obtain ⟨⟨δ, h1, -⟩, -⟩ := lES_holds ℤ _ _ _ _ _ s
    obtain ⟨x, hx, y, hy, e1, e2, e3⟩ := conn_cls_of_lift δ h1 t ht m hm
    show e ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 ((urT p K).coch.cls 2 z hz)) = _
    rw [vLayer_Kur_cls hK π hπ m z hz hzm y hy e2]
    exact (congrArg e e3.symm).trans ((he δ h1 x hx).trans (e1 _))
  · intro δ hδ c x hx h
    show e ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 c) = _
    exact (congrArg e h).trans (he δ hδ x hx)

theorem exists_isInv (hK : FiniteDimensional ℚ_[p] K) :
    ∃ f : (urT p K).H 2 ≃+ QZ, IsInv p K f.toAddMonoidHom := by
  obtain ⟨f, hf, -⟩ := exists_invariant_of_connecting_map hK
  exact ⟨f, hf⟩

theorem exists_uniformiser_Kur (hK : FiniteDimensional ℚ_[p] K) :
    ∃ π : (urT p K).V, π.1 ∈ multOf p K ∧ (eK p K : ℝ) * vbar p π.1 = 1 := by
  obtain ⟨x, hx⟩ := vOn_surjective p K hK 1
  have h1 := vOn_spec p K x
  rw [hx, Int.cast_one] at h1
  have hx' : x.1 ∈ multOf p (MaximalUnramifiedExtension p K) := le_Kur (K := K) x.2
  exact ⟨toLayer p ⟨x.1, hx'⟩, x.2, h1.symm⟩

theorem exists_std_cocycle (hK : FiniteDimensional ℚ_[p] K) (c : (urT p K).H 2) :
    ∃ (π : (urT p K).V) (t : GalLK p K (MaximalUnramifiedExtension p K) → ℚ) (m : (Fin 2 → GalLK p K (MaximalUnramifiedExtension p K)) → ℤ)
      (z : (urT p K).coch.X 2) (hz : (urT p K).coch.d 2 z = 0),
      π.1 ∈ multOf p K ∧ (eK p K : ℝ) * vbar p π.1 = 1 ∧ IsLocallyConstant t ∧
      (∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) ∧ (∀ g, z.1 g = m g • π) ∧
      c = (urT p K).coch.cls 2 z hz := by
  obtain ⟨π, hπK, hπ⟩ := exists_uniformiser_Kur hK
  obtain ⟨t, m, y, hy, ht, hm, hym, hc⟩ := exists_cocycle_form ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 c)
  have hinv := (layer_invariant_iff π).2 hπK
  have hyc : Continuous y.1 := y.2
  have hzc : Continuous fun g : Fin 2 → GalLK p K (MaximalUnramifiedExtension p K) => m g • π := by
    have h0 : Continuous fun k : (trivRep (GalLK p K (MaximalUnramifiedExtension p K)) ℤ).V => (show ℤ from k) • π :=
      continuous_of_discreteTopology
    rw [← hym]
    exact h0.comp hyc
  let z : (urT p K).coch.X 2 := ⟨fun g => m g • π, hzc⟩
  have hz : (urT p K).coch.d 2 z = 0 := by
    apply LowDeg.coch_d_eq_zero
    funext g
    have h0 := congrFun (LowDeg.dn_eq_zero _ hy) g
    rw [LowDeg.dn_two_apply, hym] at h0
    have h1 : m ![g 1, g 2] - m ![g 0 * g 1, g 2] + m ![g 0, g 1 * g 2] - m ![g 0, g 1] = 0 := h0
    rw [LowDeg.dn_two_apply]
    show (urT p K).rho (g 0) (m ![g 1, g 2] • π) - m ![g 0 * g 1, g 2] • π + m ![g 0, g 1 * g 2] • π -
      m ![g 0, g 1] • π = 0
    rw [map_zsmul, hinv, ← sub_smul, ← add_smul, ← sub_smul, h1, zero_smul]
  refine ⟨π, t, m, z, hz, hπK, hπ, ht, hm, fun _ => rfl, ?_⟩
  apply (valuation_unramified_closure_h2_bijective hK).1
  rw [hc, vLayer_Kur_cls hK π hπ m z hz (fun _ => rfl) y hy hym]

theorem IsInv.unique (hK : FiniteDimensional ℚ_[p] K) {f g : (urT p K).H 2 →+ QZ} (hf : IsInv p K f)
    (hg : IsInv p K g) : f = g := by
  ext c
  obtain ⟨π, t, m, z, hz, h1, h2, h3, h4, h5, rfl⟩ := exists_std_cocycle hK c
  rw [hf π t m z hz h1 h2 h3 h4 h5, hg π t m z hz h1 h2 h3 h4 h5]

theorem isInv_invUr (hK : FiniteDimensional ℚ_[p] K) : IsInv p K (invUr p K) := by
  obtain ⟨f, hf⟩ := exists_isInv hK
  have h : ∃ f, IsInv p K f := ⟨_, hf⟩
  unfold invUr
  rw [dite_eq_left h]
  exact h.choose_spec

theorem invUr_bijective (hK : FiniteDimensional ℚ_[p] K) : Bijective (invUr p K) := by
  obtain ⟨f, hf⟩ := exists_isInv hK
  rw [IsInv.unique hK (isInv_invUr hK) hf]
  exact f.bijective

theorem invUr_eq (hK : FiniteDimensional ℚ_[p] K) (δ)
    (hδ : Cx.IsConn (trivMap (GalLK p K (MaximalUnramifiedExtension p K)) (Int.castAddHom ℚ)).hom
      (trivMap (GalLK p K (MaximalUnramifiedExtension p K)) (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ)
    (c : (urT p K).H 2) (x) (hx)
    (h : (vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 c = δ 1 ((trivRep (GalLK p K (MaximalUnramifiedExtension p K)) QZ).coch.cls 1 x hx)) :
    invUr p K c = x.1 ![frobLK p K (MaximalUnramifiedExtension p K)] := by
  obtain ⟨f, hf, hf'⟩ := exists_invariant_of_connecting_map hK
  rw [IsInv.unique hK (isInv_invUr hK) hf]
  exact hf' δ hδ c x hx h

theorem layerInfl_u_val {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') [(subG p K L).Normal]
    [(subG p K L').Normal] (x : (layer p K L).V) : ((layerInfl (K := K) h).u x).1 = x.1 := rfl

theorem vLayerMap_layerInfl {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : K ≤ L) (h : L ≤ L')
    [(subG p K L).Normal] [(subG p K L').Normal] (he : eK p L' = eK p L) (x : (layer p K L).V) :
    vLayerMap p K L' ((layerInfl (K := K) h).u x) = vLayerMap p K L x := by
  apply Int.cast_injective (α := ℝ)
  rw [vLayerMap_spec p (hL.trans h), vLayerMap_spec p hL, he, layerInfl_u_val]

theorem layerInfl_φ_surjective {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L')
    [(subG p K L).Normal] [(subG p K L').Normal] : Surjective (layerInfl (K := K) h).φ := by
  intro g
  induction g using QuotientGroup.induction_on with
  | H σ => exact ⟨QuotientGroup.mk σ, rfl⟩

theorem vLayer_layerInfl_H {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : K ≤ L) (h : L ≤ L')
    [(subG p K L).Normal] [(subG p K L').Normal] (he : eK p L' = eK p L) (i : ℕ) (c : (layer p K L).H i) :
    (vLayer p K L').hom.H i ((layerInfl (K := K) h).hom.H i c) =
      (trivInfl (layerInfl (K := K) h).φ (layerInfl (K := K) h).φ_cont ℤ).hom.H i
        ((vLayer p K L).hom.H i c) := by
  obtain ⟨x, hx, rfl⟩ := Cx.exists_cls c
  rw [Cx.Hom.H_cls, Cx.Hom.H_cls, Cx.Hom.H_cls, Cx.Hom.H_cls]
  apply Cx.cls_congr
  apply Subtype.ext
  funext g
  exact vLayerMap_layerInfl hL h he _

theorem inflation_h2_injective_of_same_ramification {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : K ≤ L) (h : L ≤ L')
    [(subG p K L).Normal] [(subG p K L').Normal] (he : eK p L' = eK p L)
    (hv : Injective ((vLayer p K L).hom.H 2)) : Injective ((layerInfl (K := K) h).hom.H 2) := by
  intro a b hab
  apply hv
  apply trivial_inflation_h2_int_injective _ (layerInfl (K := K) h).φ_cont (layerInfl_φ_surjective h)
  rw [← vLayer_layerInfl_H hL h he, ← vLayer_layerInfl_H hL h he, hab]

theorem inflation_unramified_layer_h2_injective (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Injective ((layerInfl (K := K) (L := Kn p K n) (L' := MaximalUnramifiedExtension p K) (Kn_le_Kur hn)).hom.H 2) :=
  inflation_h2_injective_of_same_ramification (L := Kn p K n) le_sup_left (Kn_le_Kur hn) ((eK_Kur p hK).trans (eK_Kn p hK hn).symm)
    (valuation_unramified_layer_h2_bijective hK hn).1

theorem mem_range_layerInfl_Kn_iff (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (x : (urT p K).H 2) :
    x ∈ LinearMap.range ((layerInfl (K := K) (L := Kn p K n) (L' := MaximalUnramifiedExtension p K) (Kn_le_Kur hn)).hom.H 2) ↔ n • x = 0 := by
  have hsub : Set.range ((layerInfl (K := K) (L := Kn p K n) (L' := MaximalUnramifiedExtension p K) (Kn_le_Kur hn)).hom.H 2) ⊆
      {x : (urT p K).H 2 | n • x = 0} := by
    rintro _ ⟨y, rfl⟩
    show n • _ = 0
    have h0 : n • y = 0 := by
      have h1 := card_nsmul_eq_zero' (x := y)
      rwa [card_h2_unramified_layer hK hn] at h1
    rw [← map_nsmul, h0, map_zero]
  obtain ⟨f, -⟩ := exists_isInv hK
  have hT : Nat.card {x : (urT p K).H 2 | n • x = 0} = n := by
    refine (Nat.card_congr (Equiv.subtypeEquiv f.toEquiv fun a => ?_)).trans (card_QZ_torsion n hn)
    show n • a = 0 ↔ n • f a = 0
    rw [← map_nsmul, map_eq_zero_iff f f.injective]
  have hfin : ({x : (urT p K).H 2 | n • x = 0} : Set _).Finite :=
    Nat.finite_of_card_ne_zero (by rw [hT]; exact hn.ne')
  have hS : Nat.card (Set.range ((layerInfl (K := K) (L := Kn p K n) (L' := MaximalUnramifiedExtension p K) (Kn_le_Kur hn)).hom.H 2)) = n := by
    rw [Nat.card_range_of_injective (inflation_unramified_layer_h2_injective hK hn), card_h2_unramified_layer hK hn]
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (by rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hT, hS]) hfin
  show x ∈ Set.range _ ↔ _
  rw [heq]
  rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
