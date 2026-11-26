module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.CptConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MemTwCentConj

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.CptCpt
noncomputable section

open ValuativeRel Matrix

namespace UpperTheory.Gal.InertialTypesAlt.L

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem isOpen_ball (c : (ValueGroupWithZero k)ˣ) :
    IsOpen {y : k | valuation k y ≤ (c : ValueGroupWithZero k)} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨c, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  simp only [Set.mem_setOf_eq] at hz hx ⊢
  exact le_trans (Valuation.map_add _ _ _) (max_le hx (le_of_lt hz))

private theorem isIntegral_of_cpt {n : ℕ} (g : GL (Fin n) k)
    (hg : IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) k)))) :
    IsIntegral 𝒪[k] (g : Matrix (Fin n) (Fin n) k) := by
  have hcont : ∀ i j : Fin n, Continuous (fun M : GL (Fin n) k => (M : Matrix (Fin n) (Fin n) k) i j) :=
    fun i j => Units.continuous_val.matrix_elem i j
  set S := ⋃ (i : Fin n) (j : Fin n), (fun M : GL (Fin n) k => (M : Matrix (Fin n) (Fin n) k) i j) ''
    closure (Subgroup.zpowers g : Set (GL (Fin n) k)) with hS
  have hSc : IsCompact S := isCompact_iUnion (fun i => isCompact_iUnion (fun j => hg.image (hcont i j)))
  obtain ⟨c, hc⟩ : ∃ c : (ValueGroupWithZero k)ˣ, S ⊆ {y | valuation k y ≤ (c : ValueGroupWithZero k)} := by
    apply hSc.elim_directed_cover (fun c : (ValueGroupWithZero k)ˣ => {y | valuation k y ≤ (c : ValueGroupWithZero k)})
    · exact fun c => isOpen_ball c
    · intro y _
      rw [Set.mem_iUnion]
      by_cases hy : valuation k y = 0
      · exact ⟨1, by simp [hy]⟩
      · exact ⟨Units.mk0 _ hy, by simp only [Set.mem_setOf_eq, Units.val_mk0, le_refl]⟩
    · intro a b
      rcases le_total (a : ValueGroupWithZero k) b with h | h
      · exact ⟨b, fun y (hy : valuation k y ≤ _) => (le_trans hy h : valuation k y ≤ _), fun y hy => hy⟩
      · exact ⟨a, fun y hy => hy, fun y (hy : valuation k y ≤ _) => (le_trans hy h : valuation k y ≤ _)⟩
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective ((c⁻¹ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact (Units.ne_zero _) ha.symm
  apply GlobalTheory.isIntegral_matrix_of_pow_bounded (g : Matrix (Fin n) (Fin n) k) a ha0
  intro m i j
  have hmem : ((g ^ m : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ S := by
    rw [hS, Set.mem_iUnion]
    refine ⟨i, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨j, g ^ m, subset_closure (Subgroup.npow_mem_zpowers g m), rfl⟩
  have hle : valuation k (((g : Matrix (Fin n) (Fin n) k) ^ m) i j) ≤ (c : ValueGroupWithZero k) := by
    have h1 := hc hmem
    rw [Units.val_pow_eq_pow_val] at h1
    exact h1
  refine ⟨⟨a * ((g : Matrix (Fin n) (Fin n) k) ^ m) i j, ?_⟩, rfl⟩
  show valuation k (a * ((g : Matrix (Fin n) (Fin n) k) ^ m) i j) ≤ 1
  rw [map_mul, ha]
  calc ((c⁻¹ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) * valuation k (((g : Matrix (Fin n) (Fin n) k) ^ m) i j)
      ≤ ((c⁻¹ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) * c := by gcongr
    _ = 1 := Units.inv_mul c

private theorem bounded_adjoin {n : ℕ} (N : Matrix (Fin n) (Fin n) k) (hs : N.charpoly.Separable) :
    ∃ c : ValueGroupWithZero k, ∀ g ∈ Algebra.adjoin k {N}, IsIntegral 𝒪[k] g →
      ∀ i j, valuation k (g i j) ≤ c := by
  have hI := Valuation.integer.integers (valuation k)
  exact GlobalTheory.LocBounded.bounded_of_isIntegral_general (valuation k) (fun y => y.2) (fun x hx => ⟨⟨x, hx⟩, rfl⟩)
    (fun x hx => hI.isIntegral_iff_v_le_one.mp hx) N hs

private theorem isCompact_entries (n : ℕ) (c : ValueGroupWithZero k) :
    IsCompact {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j) ≤ c} := by
  have h : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n =>
      {x : k | valuation k x ≤ c}) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k c
  have e : {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j) ≤ c} =
      (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => {x : k | valuation k x ≤ c}) := by
    ext M
    exact ⟨fun hM i _ j _ => hM i j, fun hM i j => hM i trivial j trivial⟩
  rw [e]
  exact h

end UpperTheory.Gal.InertialTypesAlt.L

private theorem isIntegral_mul_of_mem_adjoin_singleton {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (A x y : Matrix (Fin n) (Fin n) k)
    (hx : x ∈ Algebra.adjoin k {A}) (hy : y ∈ Algebra.adjoin k {A})
    (hxi : IsIntegral 𝒪[k] x) (hyi : IsIntegral 𝒪[k] y) : IsIntegral 𝒪[k] (x * y) := by
  letI : CommRing (Algebra.adjoin k {A}) := by
    open scoped IsMulCommutative in
      exact inferInstance
  let f : Algebra.adjoin k {A} →ₐ[𝒪[k]] Matrix (Fin n) (Fin n) k :=
    (Algebra.adjoin k {A}).val.restrictScalars 𝒪[k]
  have hinj : Function.Injective f := Subtype.val_injective
  have h1 : IsIntegral 𝒪[k] (⟨x, hx⟩ : Algebra.adjoin k {A}) := (isIntegral_algHom_iff f hinj).mp hxi
  have h2 : IsIntegral 𝒪[k] (⟨y, hy⟩ : Algebra.adjoin k {A}) := (isIntegral_algHom_iff f hinj).mp hyi
  exact (isIntegral_algHom_iff f hinj).mpr (h1.mul h2)

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.cptCpt :
    UpperTheory.Gal.InertialTypesAlt.L.CptCpt := by
  intro k _ _ _ _ n A T hA hT hcomm
  obtain ⟨-, -, hT2, -, hprop⟩ := UpperTheory.V.Z.Tf.Orb.gLTop_holds k n
  haveI := hT2
  obtain ⟨c, hc⟩ := bounded_adjoin (A : Matrix (Fin n) (Fin n) k) hA
  have hΩ := isCompact_entries (k := k) n c
  have hC := hprop _ _ hΩ hΩ
  let K0 : Subgroup (GL (Fin n) k) :=
    { carrier := {g | (g : Matrix (Fin n) (Fin n) k) ∈ Algebra.adjoin k {(A : Matrix (Fin n) (Fin n) k)} ∧
        IsIntegral 𝒪[k] (g : Matrix (Fin n) (Fin n) k) ∧
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ Algebra.adjoin k {(A : Matrix (Fin n) (Fin n) k)} ∧
        IsIntegral 𝒪[k] ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)}
      mul_mem' := by
        rintro g h ⟨hg1, hg2, hg3, hg4⟩ ⟨hh1, hh2, hh3, hh4⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [Units.val_mul]
          exact Subalgebra.mul_mem _ hg1 hh1
        · rw [Units.val_mul]
          exact isIntegral_mul_of_mem_adjoin_singleton _ _ _ hg1 hh1 hg2 hh2
        · rw [_root_.mul_inv_rev, Units.val_mul]
          exact Subalgebra.mul_mem _ hh3 hg3
        · rw [_root_.mul_inv_rev, Units.val_mul]
          exact isIntegral_mul_of_mem_adjoin_singleton _ _ _ hh3 hg3 hh4 hg4
      one_mem' := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [Units.val_one]
          exact Subalgebra.one_mem _
        · rw [Units.val_one]
          exact isIntegral_one
        · rw [inv_one, Units.val_one]
          exact Subalgebra.one_mem _
        · rw [inv_one, Units.val_one]
          exact isIntegral_one
      inv_mem' := by
        rintro g ⟨hg1, hg2, hg3, hg4⟩
        refine ⟨hg3, hg4, ?_, ?_⟩
        · rw [inv_inv]
          exact hg1
        · rw [inv_inv]
          exact hg2 }
  have hsub : (K0 : Set (GL (Fin n) k)) ⊆
      {g | (g : Matrix (Fin n) (Fin n) k) ∈ {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j) ≤ c} ∧
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈
          {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j) ≤ c}} := by
    rintro g ⟨hg1, hg2, hg3, hg4⟩
    exact ⟨hc _ hg1 hg2, hc _ hg3 hg4⟩
  have hK1 : IsCompact (K0.topologicalClosure : Set (GL (Fin n) k)) := by
    rw [Subgroup.topologicalClosure_coe]
    exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)
  have hgen : ∀ t ∈ T, IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) k))) → t ∈ K0 := by
    intro t ht hcpt
    have hcA : ∀ s ∈ T, (s : Matrix (Fin n) (Fin n) k) * A = A * s := by
      intro s hs
      rw [← Units.val_mul, ← Units.val_mul, (hcomm s hs).eq]
    have hcpt' : IsCompact (closure (Subgroup.zpowers t⁻¹ : Set (GL (Fin n) k))) := by
      rw [Subgroup.zpowers_inv]
      exact hcpt
    exact ⟨GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute _ _ hA (hcA t ht), isIntegral_of_cpt t hcpt,
      GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute _ _ hA (hcA t⁻¹ (T.inv_mem ht)), isIntegral_of_cpt t⁻¹ hcpt'⟩
  have hle : GlobalTheory.BCT.cptPart T ≤ T ⊓ K0.topologicalClosure := by
    unfold GlobalTheory.BCT.cptPart
    rw [Subgroup.closure_le]
    rintro t ⟨ht, hcpt⟩
    exact ⟨ht, Subgroup.le_topologicalClosure K0 (hgen t ht hcpt)⟩
  have hge : T ⊓ K0.topologicalClosure ≤ GlobalTheory.BCT.cptPart T := GlobalTheory.LocFin.inf_le_cptPart T _ hK1
  rw [le_antisymm hle hge, Subgroup.coe_inf]
  exact hK1.inter_left hT
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.OrbSum
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.SumCoset
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

open PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

private lemma UpperTheory.Gal.InertialTypesAlt.L.mem_iff_mk {G : Type} [Group G] (T K : Subgroup G)
    (q : DoubleCoset.Quotient (T : Set G) (K : Set G)) (g : G) :
    (∃ t ∈ T, ∃ y ∈ K, g = t * Quotient.out q * y) ↔ DoubleCoset.mk T K g = q := by
  have h := @DoubleCoset.eq _ _ T K (Quotient.out q) g
  rw [DoubleCoset.out_eq'] at h
  exact h.symm.trans eq_comm

theorem UpperTheory.Gal.InertialTypesAlt.L.sumCoset :
    UpperTheory.Gal.InertialTypesAlt.L.SumCoset := by
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 T hTc hcomm ν hν F hF hFT hFC
  obtain ⟨hsf, hinv, hrinv⟩ := haarComm_holds G T hTc hcomm ν hν
  obtain ⟨ρ, hρ, -⟩ := normEx_holds G ⟨K, hKo, hKc⟩ T hTc ν hν hrinv
  have hInt := quotInt_holds G μ hμ T hTc ν hν hinv F hF hFT hFC ρ hρ
  obtain ⟨C, hC, hFC'⟩ := hFC
  have hFm : Measurable F := hF.measurable
  have hmk : ∀ h ∈ T, ∀ g : G, DoubleCoset.mk T K (h * g) = DoubleCoset.mk T K g :=
    fun h hh g => ((@DoubleCoset.eq _ _ T K g (h * g)).2 ⟨h, hh, 1, K.one_mem, by simp⟩).symm
  set Q : Set (DoubleCoset.Quotient (T : Set G) (K : Set G)) :=
    {q | ∃ y ∈ K, F (Quotient.out q * y) ≠ 0} with hQ
  have hkey : ∀ g, F g ≠ 0 → DoubleCoset.mk T K g ∈ Q := by
    intro g hg
    obtain ⟨t, ht, y, hy, he⟩ :=
      (UpperTheory.Gal.InertialTypesAlt.L.mem_iff_mk T K (DoubleCoset.mk T K g) g).2 rfl
    refine ⟨y, hy, ?_⟩
    have e : Quotient.out (DoubleCoset.mk T K g) * y = t⁻¹ * g := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc]
      exact he.symm
    rw [e, hFT t⁻¹ (T.inv_mem ht) g]
    exact hg
  have hfin : Q.Finite := by
    obtain ⟨s, hs⟩ := hC.elim_finite_subcover (fun c : G => {z : G | c⁻¹ * z ∈ K})
      (fun c => hKo.preimage (continuous_const_mul c⁻¹))
      (fun c _ => Set.mem_iUnion.2 ⟨c, by simp [K.one_mem]⟩)
    refine (s.finite_toSet.image (DoubleCoset.mk T K)).subset ?_
    rintro q ⟨y, hy, hq⟩
    obtain ⟨t, ht, c, hc, he⟩ := hFC' _ hq
    obtain ⟨i, hi, hci⟩ := Set.mem_iUnion₂.1 (hs hc)
    refine ⟨i, hi, ?_⟩
    rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
    refine ⟨t, ht, i⁻¹ * c * y⁻¹, K.mul_mem hci (K.inv_mem hy), ?_⟩
    calc Quotient.out q = Quotient.out q * y * y⁻¹ := by group
      _ = t * c * y⁻¹ := by rw [he]
      _ = t * i * (i⁻¹ * c * y⁻¹) := by group
  refine ⟨hfin, ?_⟩
  have hS : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
      {g | ∃ t ∈ T, ∃ y ∈ K, g = t * Quotient.out q * y} = {g | DoubleCoset.mk T K g = q} :=
    fun q => Set.ext (UpperTheory.Gal.InertialTypesAlt.L.mem_iff_mk T K q)
  simp_rw [hS]
  have hSo : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
      IsOpen {g | DoubleCoset.mk T K g = q} := by
    intro q
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨{z | g⁻¹ * z ∈ K}, fun z hz => ?_, hKo.preimage (continuous_const_mul g⁻¹),
      by simp [K.one_mem]⟩
    show DoubleCoset.mk T K z = q
    rw [← (show DoubleCoset.mk T K g = q from hg), eq_comm, DoubleCoset.eq]
    exact ⟨1, T.one_mem, g⁻¹ * z, hz, by group⟩
  have hSinv : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G), ∀ h ∈ T, ∀ g : G,
      {g | DoubleCoset.mk T K g = q}.indicator F (h * g) =
        {g | DoubleCoset.mk T K g = q}.indicator F g := by
    intro q h hh g
    simp only [Set.indicator_apply, Set.mem_setOf_eq, hmk h hh g, hFT h hh g]
  have hq_eq : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
      quotIntegral μ T ν ({g | DoubleCoset.mk T K g = q}.indicator F) =
        ∫ g, {g | DoubleCoset.mk T K g = q}.indicator
          (fun g => F g * ((ρ g).toReal : ℂ)) g ∂μ := by
    intro q
    rw [quotIndep_holds G μ hμ T ν hsf hinv _ (hFm.indicator (hSo q).measurableSet) (hSinv q) ρ hρ]
    congr 1
    funext g
    simp [Set.indicator_apply]
  have hsupp : (Function.support fun q : DoubleCoset.Quotient (T : Set G) (K : Set G) =>
      quotIntegral μ T ν ({g | DoubleCoset.mk T K g = q}.indicator F)) ⊆
        ↑hfin.toFinset := by
    intro q hq
    rw [Set.Finite.coe_toFinset]
    by_contra hqQ
    apply hq
    have h0 : {g | DoubleCoset.mk T K g = q}.indicator F = 0 := by
      funext g
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.zero_apply]
      split_ifs with hg
      · by_contra hne
        exact hqQ (hg ▸ hkey g hne)
      · rfl
    show quotIntegral μ T ν ({g | DoubleCoset.mk T K g = q}.indicator F) = 0
    rw [h0]
    simp [quotIntegral]
  rw [quotIndep_holds G μ hμ T ν hsf hinv F hFm hFT ρ hρ, finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_congr rfl (fun q _ => hq_eq q),
    ← integral_finsetSum _ (fun q _ => hInt.indicator (hSo q).measurableSet)]
  congr 1
  funext g
  by_cases hg : F g = 0
  · simp [Set.indicator_apply, hg]
  · rw [Finset.sum_eq_single (DoubleCoset.mk T K g)]
    · simp [Set.indicator_apply]
    · intro b _ hb
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rw [if_neg (fun h => hb h.symm)]
    · intro hn
      exact absurd (hfin.mem_toFinset.2 (hkey g hg)) hn
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.OneCoset
open MeasureTheory PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb
open scoped ENNReal

theorem UpperTheory.Gal.InertialTypesAlt.L.oneCoset :
    UpperTheory.Gal.InertialTypesAlt.L.OneCoset := by
  classical
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 T hTc hTcomm ν hν F hF hFT q
  haveI := hμ
  haveI := hν
  obtain ⟨hsf, hinv, hright⟩ := haarComm_holds G T hTc hTcomm ν hν
  haveI := hsf
  haveI := hinv
  haveI := hright
  obtain ⟨ρ, hρ, -⟩ := normEx_holds G ⟨K, hKo, hKc⟩ T hTc ν hν hright
  set D : Set G := {g | ∃ t ∈ T, ∃ y ∈ K, g = t * q * y} with hD
  set Hs : Set T := {t : T | q⁻¹ * (t : G) * q ∈ K} with hHs
  set qK : Set G := {g | q⁻¹ * g ∈ K} with hqK

  have hqKo : IsOpen qK := hKo.preimage (continuous_const.mul continuous_id)
  have hDo : IsOpen D := by
    have : D = ⋃ t : T, (fun g : G => ((t : G) * q)⁻¹ * g) ⁻¹' (K : Set G) := by
      ext g
      simp only [hD, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
      constructor
      · rintro ⟨t, ht, y, hy, rfl⟩
        refine ⟨⟨t, ht⟩, ?_⟩
        simpa [mul_assoc] using hy
      · rintro ⟨t, ht⟩
        exact ⟨t, t.2, _, ht, by group⟩
    rw [this]
    exact isOpen_iUnion fun t => hKo.preimage (continuous_const.mul continuous_id)
  have hHo : IsOpen Hs :=
    hKo.preimage (((continuous_const.mul continuous_subtype_val).mul continuous_const))
  have hHc : IsCompact Hs := by
    have hS : IsCompact ((fun x : G => q * x * q⁻¹) '' (K : Set G)) :=
      hKc.image (by fun_prop)
    have hpc := hTc.isClosedEmbedding_subtypeVal.isCompact_preimage hS
    have e : Hs = Subtype.val ⁻¹' ((fun x : G => q * x * q⁻¹) '' (K : Set G)) := by
      ext t
      simp only [hHs, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
      constructor
      · intro h
        exact ⟨_, h, by group⟩
      · rintro ⟨x, hx, hxt⟩
        have : q⁻¹ * (t : G) * q = x := by rw [← hxt]; group
        rwa [this]
    rw [e]
    exact hpc
  have h1H : (1 : T) ∈ Hs := by
    simpa [hHs] using K.one_mem
  set v : ℝ≥0∞ := ν Hs with hv
  have hv0 : v ≠ 0 := hHo.measure_ne_zero ν ⟨1, h1H⟩
  have hvt : v ≠ ∞ := hHc.measure_lt_top.ne
  have hqKD : qK ⊆ D := fun g hg => ⟨1, T.one_mem, q⁻¹ * g, hg, by group⟩
  have hDT : ∀ h ∈ T, ∀ g, h * g ∈ D ↔ g ∈ D := by
    intro h hh g
    constructor
    · rintro ⟨t, ht, y, hy, e⟩
      refine ⟨h⁻¹ * t, T.mul_mem (T.inv_mem hh) ht, y, hy, ?_⟩
      calc g = h⁻¹ * (h * g) := by group
        _ = _ := by rw [e]; group
    · rintro ⟨t, ht, y, hy, rfl⟩
      exact ⟨h * t, T.mul_mem hh ht, y, hy, by group⟩
  set ρ' : G → ℝ≥0∞ := D.piecewise (qK.indicator fun _ => v⁻¹) ρ with hρ'def
  have hρ' : IsQuotNormaliser T ν ρ' := by
    refine ⟨Measurable.piecewise hDo.measurableSet
      (measurable_const.indicator hqKo.measurableSet) hρ.1, fun g => ?_⟩
    by_cases hg : g ∈ D
    · obtain ⟨t₀, ht₀, y, hy, rfl⟩ := hg
      set A : Set T := (fun h : T => h * (⟨t₀, ht₀⟩ : T)) ⁻¹' Hs with hA
      have hAm : MeasurableSet A := (hHo.preimage (continuous_mul_const _)).measurableSet
      have hpt : ∀ h : T, ρ' ((h : G) * (t₀ * q * y)) = A.indicator (fun _ => v⁻¹) h := by
        intro h
        have hmem : (h : G) * (t₀ * q * y) ∈ D :=
          (hDT _ h.2 _).2 ⟨t₀, ht₀, y, hy, rfl⟩
        rw [hρ'def, Set.piecewise_eq_of_mem _ _ _ hmem]
        have hiff : (h : G) * (t₀ * q * y) ∈ qK ↔ h ∈ A := by
          have e : q⁻¹ * ((h : G) * (t₀ * q * y)) = (q⁻¹ * ((h : G) * t₀) * q) * y := by group
          simp only [hqK, hA, hHs, Set.mem_setOf_eq, Set.mem_preimage, e, Subgroup.coe_mul]
          exact Subgroup.mul_mem_cancel_right K hy
        by_cases hh : h ∈ A
        · rw [Set.indicator_of_mem (hiff.2 hh), Set.indicator_of_mem hh]
        · rw [Set.indicator_of_notMem (fun c => hh (hiff.1 c)), Set.indicator_of_notMem hh]
      simp_rw [hpt]
      rw [lintegral_indicator_const hAm, hA, measure_preimage_mul_right, ← hv]
      exact ENNReal.inv_mul_cancel hv0 hvt
    · have hpt : ∀ h : T, ρ' ((h : G) * g) = ρ ((h : G) * g) := by
        intro h
        rw [hρ'def, Set.piecewise_eq_of_notMem _ _ _ (fun c => hg ((hDT _ h.2 _).1 c))]
      simp_rw [hpt]
      exact hρ.2 g
  have hFm : Measurable (D.indicator F) := hF.measurable.indicator hDo.measurableSet
  have hFinv : ∀ h ∈ T, ∀ g, D.indicator F (h * g) = D.indicator F g := by
    intro h hh g
    by_cases hg : g ∈ D
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hDT h hh g).2 hg), hFT h hh]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun c => hg ((hDT h hh g).1 c))]
  rw [quotIndep_holds G μ hμ T ν hsf hinv _ hFm hFinv ρ' hρ']
  have hpt : ∀ g, D.indicator F g * ((ρ' g).toReal : ℂ) =
      qK.indicator (fun g => ((v.toReal : ℝ) : ℂ)⁻¹ * F g) g := by
    intro g
    by_cases hg : g ∈ D
    · rw [Set.indicator_of_mem hg, hρ'def, Set.piecewise_eq_of_mem _ _ _ hg]
      by_cases hq : g ∈ qK
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, ENNReal.toReal_inv]
        push_cast
        ring
      · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
        simp
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun c => hg (hqKD c)), zero_mul]
  simp_rw [hpt]
  rw [integral_indicator hqKo.measurableSet, integral_const_mul]
  have hpre : (fun y : G => q * y) ⁻¹' qK = (K : Set G) := by
    ext y
    simp [hqK]
  have := (measurePreserving_mul_left μ q).setIntegral_preimage_emb
    (measurableEmbedding_mulLeft q) F qK
  rw [hpre] at this
  rw [this]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.AvgInt
noncomputable section

open MeasureTheory
open scoped Classical ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

theorem avgInt : AvgInt := by
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 U hUo F hF q
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  set u : K → ℂ := fun y => F (q * (y : G)) with hu
  set S : Subgroup K := GlobalTheory.BCT.rStab u with hS
  have hUS : U.subgroupOf K ≤ S := by
    intro k hk
    have hk' : (k : G) ∈ U := Subgroup.mem_subgroupOf.mp hk
    show ∀ x : K, u (x * k) = u x
    intro x
    simp only [hu, Subgroup.coe_mul, ← mul_assoc]
    exact hF _ hk' _
  have hSo : IsOpen (S : Set K) := Subgroup.isOpen_mono hUS (Subgroup.subgroupOf_isOpen K U hUo)
  haveI : Finite (K ⧸ S) := Subgroup.quotient_finite_of_isOpen S hSo
  letI : Fintype (K ⧸ S) := Fintype.ofFinite _
  have hconst : ∀ y : K, u y = u (Quotient.out (QuotientGroup.mk y : K ⧸ S)) := by
    intro y
    have hmem : (Quotient.out (QuotientGroup.mk y : K ⧸ S))⁻¹ * y ∈ S := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    have h := hmem (Quotient.out (QuotientGroup.mk y : K ⧸ S))
    rw [mul_inv_cancel_left] at h
    exact h
  set S' : Set G := ((↑) : K → G) '' (S : Set K) with hS'
  have hS'o : IsOpen S' := hKo.isOpenMap_subtype_val _ hSo
  set A : K ⧸ S → Set G := fun c => (fun y => ((Quotient.out c : K) : G)⁻¹ * y) ⁻¹' S' with hA
  have hmemA : ∀ c y, y ∈ A c ↔ ∃ h : y ∈ K, (QuotientGroup.mk (⟨y, h⟩ : K) : K ⧸ S) = c := by
    intro c y
    simp only [hA, hS', Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨s, hs, hsy⟩
      have hy : y = ((Quotient.out c : K) : G) * (s : G) := by
        rw [hsy]
        group
      have hyK : y ∈ K := by
        rw [hy]
        exact K.mul_mem (Quotient.out c).2 s.2
      refine ⟨hyK, ?_⟩
      have he : (⟨y, hyK⟩ : K) = Quotient.out c * s := Subtype.ext hy
      rw [he]
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using hs
    · rintro ⟨hyK, hc⟩
      have hmem : (Quotient.out c)⁻¹ * (⟨y, hyK⟩ : K) ∈ S := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', hc]
      exact ⟨_, hmem, by simp⟩
  have hAm : ∀ c, MeasurableSet (A c) := fun c => (measurable_const_mul _) hS'o.measurableSet
  have hAK : ∀ c, A c ⊆ K := fun c y hy => ((hmemA c y).mp hy).1
  have hAμ : ∀ c, μ (A c) = μ S' := fun c => measure_preimage_mul μ _ S'
  have hunion : (⋃ c, A c) = (K : Set G) := by
    apply Set.Subset.antisymm (Set.iUnion_subset hAK)
    intro y hy
    exact Set.mem_iUnion.mpr ⟨_, (hmemA _ y).mpr ⟨hy, rfl⟩⟩
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro c c' hcc'
    refine Set.disjoint_left.mpr fun y h1 h2 => hcc' ?_
    obtain ⟨h, rfl⟩ := (hmemA c y).mp h1
    obtain ⟨h', rfl⟩ := (hmemA c' y).mp h2
    rfl
  have hsum : (Fintype.card (K ⧸ S) : ℝ≥0∞) * μ S' = 1 := by
    rw [← hK1, ← hunion, measure_iUnion hdisj hAm, tsum_fintype]
    simp only [hAμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (K ⧸ S) : ℕ) = S.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hreal : ∀ c, μ.real (A c) = ((S.index : ℝ))⁻¹ := by
    intro c
    have hne : (Fintype.card (K ⧸ S) : ℝ≥0∞) ≠ 0 := by
      simp
    have h1 : μ S' = ((Fintype.card (K ⧸ S) : ℝ≥0∞))⁻¹ := by
      rw [← ENNReal.eq_div_iff hne (by simp), ENNReal.div_eq_inv_mul, mul_one] at hsum
      exact hsum
    rw [Measure.real, hAμ, h1, ENNReal.toReal_inv, ENNReal.toReal_natCast, hcard]
  haveI : IsFiniteMeasure (μ.restrict (K : Set G)) :=
    ⟨by rw [Measure.restrict_apply_univ, hK1]; exact ENNReal.one_lt_top⟩
  have hint : ∫ y in (K : Set G), F (q * y) ∂μ =
      ∫ y in (K : Set G), ∑ c, (A c).indicator (fun _ => u (Quotient.out c)) y ∂μ := by
    refine setIntegral_congr_fun hKo.measurableSet fun y hy => ?_
    rw [Finset.sum_eq_single (QuotientGroup.mk (⟨y, hy⟩ : K) : K ⧸ S)]
    · rw [Set.indicator_of_mem ((hmemA _ y).mpr ⟨hy, rfl⟩)]
      exact hconst ⟨y, hy⟩
    · intro c _ hc
      refine Set.indicator_of_notMem (fun h => hc ?_) _
      obtain ⟨h', rfl⟩ := (hmemA c y).mp h
      rfl
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hint, integral_finsetSum _ fun c _ => (integrable_const _).indicator (hAm c)]
  unfold GlobalTheory.BCT.avg
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_indicator_const _ (hAm c), measureReal_restrict_apply (hAm c),
    Set.inter_eq_left.mpr (hAK c), hreal c, Complex.real_smul]
  push_cast
  rfl

end UpperTheory.Gal.InertialTypesAlt.L
end
end

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

open PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

private theorem continuous_of_rightInv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (F : G → ℂ) (h : ∀ u ∈ U, ∀ x, F (x * u) = F x) :
    Continuous F := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hev : F =ᶠ[nhds x] fun _ => F x := by
    have hop : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (U : Set G)) :=
      hU.preimage (continuous_const.mul continuous_id)
    have hx : x ∈ (fun y => x⁻¹ * y) ⁻¹' (U : Set G) := by
      simp [U.one_mem]
    filter_upwards [hop.mem_nhds hx] with y hy
    have h1 := h (x⁻¹ * y) hy x
    simpa using h1
  exact continuousAt_const.congr hev.symm

private theorem cptPart_le {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) :
    GlobalTheory.BCT.cptPart T ≤ T :=
  (Subgroup.closure_le _).2 fun _ ht => ht.1

theorem orbSum : OrbSum := by
  unfold OrbSum
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 θ hθ δ T hT hcomm hC ν hν U f hU hf hcm
  subst hT
  obtain ⟨hUo, hUK, hUθ⟩ := hU
  obtain ⟨hfc, hfi⟩ := hf
  set F : G → ℂ := fun x => f (x⁻¹ * δ * θ x) with hF
  have hTcl : IsClosed (GlobalTheory.BCT.twCent θ δ : Set G) := by
    show IsClosed {g : G | g * δ = δ * θ g}
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul hθ)
  have hFU : ∀ u ∈ U, ∀ x : G, F (x * u) = F x := by
    intro u hu x
    show f ((x * u)⁻¹ * δ * θ (x * u)) = f (x⁻¹ * δ * θ x)
    rw [_root_.mul_inv_rev, map_mul]
    have h1 : θ u ∈ U := hUθ u hu
    have hu' : u⁻¹ ∈ U := U.inv_mem hu
    calc f (u⁻¹ * x⁻¹ * δ * (θ x * θ u)) = f (u⁻¹ * (x⁻¹ * δ * θ x) * θ u) := by
          simp only [mul_assoc]
      _ = f (u⁻¹ * (x⁻¹ * δ * θ x)) := (hfi _ h1 _).2
      _ = f (x⁻¹ * δ * θ x) := (hfi _ hu' _).1
  have hFT : ∀ t ∈ GlobalTheory.BCT.twCent θ δ, ∀ x : G, F (t * x) = F x := by
    intro t ht x
    have h : t * δ = δ * θ t := ht
    have h2 : t⁻¹ * δ * θ t = δ := by
      rw [mul_assoc, ← h, inv_mul_cancel_left]
    show f ((t * x)⁻¹ * δ * θ (t * x)) = f (x⁻¹ * δ * θ x)
    rw [_root_.mul_inv_rev, map_mul]
    calc f (x⁻¹ * t⁻¹ * δ * (θ t * θ x)) = f (x⁻¹ * (t⁻¹ * δ * θ t) * θ x) := by
          simp only [mul_assoc]
      _ = f (x⁻¹ * δ * θ x) := by rw [h2]
  have hFc : Continuous F := continuous_of_rightInv U hUo F hFU
  obtain ⟨_, hsum⟩ := sumCoset G μ hμ K hKo hKc hK1 _ hTcl hcomm ν hν F hFc hFT hcm
  have hmapK : ∀ q x : G, x ∈ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K ↔
      q⁻¹ * x * q ∈ K := by
    intro q x
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa [mul_assoc] using hk
    · intro hx
      exact ⟨q⁻¹ * x * q, hx, by simp [mul_assoc]⟩
  have hset : ∀ q : G, {t : GlobalTheory.BCT.twCent θ δ | q⁻¹ * (t : G) * q ∈ K} =
      {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K} := by
    intro q
    ext t
    simp only [Set.mem_setOf_eq, Subgroup.mem_inf, hmapK, SetLike.coe_mem, true_and]
  have hopen : ∀ q : G, IsOpen {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K} := by
    intro q
    rw [← hset q]
    exact hKo.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  have hvol : ∀ q : G, _ := fun q => volIdx G (GlobalTheory.BCT.twCent θ δ) (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ))
    (GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K) hTcl ν hν
    (cptPart_le _) hC
    (GlobalTheory.LocFin.inf_le_cptPart _ _ (GlobalTheory.LocFin.isCompact_map_conj K hKc q)) (hopen q)
  have hCfin : ν {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)} ≠ ⊤ :=
    ((hTcl.isClosedEmbedding_subtypeVal).isCompact_preimage hC).measure_lt_top.ne
  have hCne : ν.real {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)} ≠ 0 := by
    have h1 := (hvol 1).1
    have hsub : {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (1 : G))) K} ⊆
        {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)} :=
      fun t ht => GlobalTheory.LocFin.inf_le_cptPart _ _ (GlobalTheory.LocFin.isCompact_map_conj K hKc 1) ht
    have h2 := measureReal_mono hsub hCfin
    intro h0
    exact h1 (le_antisymm (h0 ▸ h2) measureReal_nonneg)
  refine ⟨hCne, ?_⟩
  rw [hsum]
  unfold GlobalTheory.BCT.twOrb
  rw [mul_finsum]
  refine finsum_congr fun q => ?_
  obtain ⟨hH0, hCeq⟩ := hvol (Quotient.out q)
  have hidx : ((GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out q))) K).relIndex
      (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℝ) ≠ 0 := fun h0 => hCne (by rw [hCeq, h0, zero_mul])
  rw [oneCoset G μ hμ K hKo hKc hK1 _ hTcl hcomm ν hν F hFc hFT (Quotient.out q)]
  rw [← avgInt G μ hμ K hKo hKc hK1 U hUo F hFU (Quotient.out q)]
  rw [hset, hCeq]
  rw [show (fun y : K => F (Quotient.out q * ↑y)) =
    fun k : K => f ((Quotient.out q * ↑k)⁻¹ * δ * θ (Quotient.out q * ↑k)) from rfl]
  have hidxC : ((GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out q))) K).relIndex
      (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℂ) ≠ 0 := by exact_mod_cast hidx
  have hHC : ((ν.real {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out q))) K} : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hH0
  push_cast
  field_simp

end UpperTheory.Gal.InertialTypesAlt.L
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

open PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

private theorem kSide (k : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
    (μk : Measure (GL (Fin n) k)) (hμ : μk.IsHaarMeasure)
    (hk1 : μk (unitGL (n := Fin n) k : Set (GL (Fin n) k)) = 1)
    (U : Subgroup (GL (Fin n) k)) (f : GL (Fin n) k → ℂ)
    (hL : GlobalTheory.BCT.IsLevel (MonoidHom.id _) (unitGL k) U) (hH : GlobalTheory.BCT.IsHecke U f)
    (γ : GL (Fin n) k) (hγ : IsRegSemisimple γ) (μγ : Measure (Subgroup.centralizer {γ}))
    (hh : μγ.IsHaarMeasure) :
    IsCompact (GlobalTheory.BCT.cptPart (Subgroup.centralizer {γ}) : Set (GL (Fin n) k)) ∧
    ((μγ.real {t : Subgroup.centralizer {γ} |
        (t : GL (Fin n) k) ∈ GlobalTheory.BCT.cptPart (Subgroup.centralizer {γ})} : ℝ) ≠ 0) ∧
    orbIntegralC μk γ μγ f =
      ((μγ.real {t : Subgroup.centralizer {γ} |
        (t : GL (Fin n) k) ∈ GlobalTheory.BCT.cptPart (Subgroup.centralizer {γ})} : ℝ) : ℂ)⁻¹ *
        GlobalTheory.BCT.twOrb (MonoidHom.id _) (unitGL k) γ f := by
  obtain ⟨hLC, hSC, hT2, -, -⟩ := gLTop_holds k n
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hKo, hKc, -⟩ := unitSB_holds k n
  haveI : ValuativeExtension k k := ⟨by simp⟩
  obtain ⟨hgen, hσ1, hTw, -⟩ := untwist_holds k n μk γ
  have hT : Subgroup.centralizer {γ} = GlobalTheory.BCT.twCent (MonoidHom.id (GL (Fin n) k)) γ := by
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Iff.rfl
  have hTcl : IsClosed (Subgroup.centralizer {γ} : Set (GL (Fin n) k)) := by
    rw [hT]
    show IsClosed {g : GL (Fin n) k | g * γ = γ * (MonoidHom.id (GL (Fin n) k)) g}
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have hcommA : ∀ t ∈ Subgroup.centralizer {γ}, Commute t γ :=
    fun t ht => Subgroup.mem_centralizer_singleton_iff.1 ht
  have hcomm : ∀ a ∈ Subgroup.centralizer {γ}, ∀ b ∈ Subgroup.centralizer {γ}, Commute a b := by
    intro a ha b hb
    have hm : ∀ t ∈ Subgroup.centralizer {γ},
        Commute (t : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k) := by
      intro t ht
      have h := Subgroup.mem_centralizer_singleton_iff.1 ht
      show (t : Matrix (Fin n) (Fin n) k) * γ = γ * t
      rw [← Units.val_mul, ← Units.val_mul, h]
    have h := centComm_holds k n (γ : Matrix (Fin n) (Fin n) k) a b hγ (hm a ha) (hm b hb)
    show a * b = b * a
    exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact h.eq)
  have hC := cptCpt k n γ _ hγ hTcl hcommA
  have hcm : CptMod (Subgroup.centralizer {γ})
      (fun x => f (x⁻¹ * γ * (MonoidHom.id (GL (Fin n) k)) x)) := by
    obtain ⟨D, hD, hDp⟩ := orbProper_holds k k 1 hgen n γ (hTw hγ) (tsupport f) hH.1
    refine ⟨D, hD, fun g hg => ?_⟩
    have hg' : twConj (sigmaGL (1 : Gal(k/k))) g γ ∈ tsupport f := by
      have he : twConj (sigmaGL (1 : Gal(k/k))) g γ = g⁻¹ * γ * g := by
        show g⁻¹ * γ * (sigmaGL (1 : Gal(k/k))) g = g⁻¹ * γ * g
        rw [hσ1 g]
      rw [he]
      exact subset_tsupport f hg
    obtain ⟨t, ht, d, hd, rfl⟩ := hDp g hg'
    refine ⟨t, ?_, d, hd, rfl⟩
    have h1 := (mem_twCent _ _ _).1 ht
    rw [hσ1 t] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t * γ = t * (t⁻¹ * γ * t) := by rw [h1]
      _ = γ * t := by group
  obtain ⟨hne, heq⟩ := orbSum (GL (Fin n) k) μk hμ (unitGL k) hKo hKc hk1 (MonoidHom.id _)
    continuous_id γ (Subgroup.centralizer {γ}) hT hcomm hC μγ hh U f hL hH hcm
  exact ⟨hC, hne, heq⟩

theorem matchOfSum : MatchOfSum := by
  unfold MatchOfSum
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n _ _ _ _ μE μk hμE hμk hE1 hk1 UE Uk φ f hLE hLk hHE hHk
    hmatch hsurj
  obtain ⟨hgal, hnorm, htw, -, hpair, hnormOf⟩ := dict k E σ hgen n
  obtain ⟨hLCE, hSCE, hT2E, -, -⟩ := gLTop_holds E n
  haveI := hLCE
  haveI := hSCE
  haveI := hT2E
  obtain ⟨hLCk, hSCk, hT2k, -, -⟩ := gLTop_holds k n
  haveI := hLCk
  haveI := hSCk
  haveI := hT2k
  obtain ⟨hKo, hKc, -⟩ := unitSB_holds E n
  obtain ⟨-, -, hcontE⟩ := extCont_holds k E
  have hgalg : ∀ g : GL (Fin n) E, (GlobalTheory.LBC.galAct σ n) g = (sigmaGL σ) g :=
    fun g => DFunLike.congr_fun hgal g
  have hθc : Continuous (GlobalTheory.LBC.galAct σ n) := by
    have h := (hcontE n).2 σ
    have he : (⇑(GlobalTheory.LBC.galAct σ n)) = ⇑(sigmaGL (n := Fin n) σ) := funext hgalg
    rw [he]
    exact h
  have hpow : (sigmaGL (n := Fin n) σ) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  refine ⟨?_, ?_⟩
  · intro δ γ h μδ μγ hTw hnh hδ hγh hmap
    obtain ⟨hγ, hchar, hmem⟩ := hpair δ h γ hTw hnh
    obtain ⟨hCk, -, heqk⟩ := kSide k n μk hμk hk1 Uk f hLk hHk γ hγ μγ hγh
    obtain ⟨hTcl, hcomm⟩ := twCent_holds k E σ hgen n δ hTw
    have hT : PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL σ) δ = GlobalTheory.BCT.twCent (GlobalTheory.LBC.galAct σ n) δ := by
      rw [hgal]
      exact htw δ
    have hCE : IsCompact (GlobalTheory.BCT.cptPart (PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL σ) δ) : Set (GL (Fin n) E)) :=
      cptCpt E n (normGL σ δ) _ hTw hTcl (fun t ht => twCent_commute_twNorm (sigmaGL σ) hpow δ ht)
    have hcm : CptMod (PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL σ) δ)
        (fun x => φ (x⁻¹ * δ * (GlobalTheory.LBC.galAct σ n) x)) := by
      obtain ⟨D, hD, hDp⟩ := orbProper_holds k E σ hgen n δ hTw (tsupport φ) hHE.1
      refine ⟨D, hD, fun g hg => ?_⟩
      have hg2 : φ (g⁻¹ * δ * (sigmaGL σ) g) ≠ 0 := by
        rw [← hgalg]
        exact hg
      exact hDp g (subset_tsupport φ hg2)
    obtain ⟨-, heqE⟩ := orbSum (GL (Fin n) E) μE hμE (unitGL E) hKo hKc hE1 (GlobalTheory.LBC.galAct σ n) hθc δ _
      hT hcomm hCE μδ hδ UE φ hLE hHE hcm
    have hvol := cptConj (GL (Fin n) E) (GL (Fin n) k) incl (inclClosed_holds k E n)
      (PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL σ) δ) (Subgroup.centralizer {γ}) h hmem hCk μδ μγ hmap
    have hO : GlobalTheory.BCT.twOrb (GlobalTheory.LBC.galAct σ n) (unitGL E) δ φ =
        GlobalTheory.BCT.twOrb (MonoidHom.id (GL (Fin n) k)) (unitGL k) γ f :=
      hmatch δ (by rw [hnorm]; exact hTw) γ (by rw [hnorm]; exact hchar)
    have hL : twOrbIntegralC (sigmaGL σ) μE δ μδ φ = quotIntegral μE _ μδ
        (fun x => φ (x⁻¹ * δ * (GlobalTheory.LBC.galAct σ n) x)) := by
      refine congrArg (quotIntegral μE _ μδ) (funext fun x => ?_)
      show φ (x⁻¹ * δ * (sigmaGL σ) x) = φ (x⁻¹ * δ * (GlobalTheory.LBC.galAct σ n) x)
      rw [hgalg]
    rw [heqk, hL, heqE, hO, hvol]
  · intro γ μγ hγ hno hγh
    obtain ⟨-, -, heqk⟩ := kSide k n μk hμk hk1 Uk f hLk hHk γ hγ μγ hγh
    rw [heqk]
    have h0 : GlobalTheory.BCT.twOrb (MonoidHom.id (GL (Fin n) k)) (unitGL k) γ f = 0 := by
      by_contra hne
      obtain ⟨δ, hδ⟩ := hsurj γ hγ hne
      exact hno ⟨δ, hnormOf δ γ hγ (by rw [← hnorm]; exact hδ)⟩
    rw [h0, mul_zero]

end UpperTheory.Gal.InertialTypesAlt.L
