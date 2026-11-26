module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumOfFiltration
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

namespace IntNumOfFiltration

theorem eventually_mixedDiff_sum (h1 : MixedDiffLinear.Statement)
    (h3 : EventualValueFacts.Statement) {K : Type} {n : ℕ} (bs : Fin n → K → ℤ)
    {α : Type*} (h : α → (K → ℤ) → ℤ) (s : α → K → ℤ) :
    ∀ l : List α, (∀ p ∈ l, ∃ c : ℤ, ∀ᶠ m in Filter.atTop, mixedDiff bs (h p) m = c) →
      ∀ᶠ m in Filter.atTop,
        mixedDiff bs (fun m => (l.map fun p => h p (m - s p)).sum) m =
          (l.map fun p => eventualValue (mixedDiff bs (h p))).sum := by
  intro l
  induction l with
  | nil =>
    intro _
    have h0 : (fun m : K → ℤ => (([] : List α).map fun p => h p (m - s p)).sum) = 0 := by
      funext m
      simp
    have hz : mixedDiff bs (0 : (K → ℤ) → ℤ) = 0 := by
      have := (h1 K n bs 0 0 0 0 0).2.1
      simpa using this
    refine Filter.Eventually.of_forall fun m => ?_
    rw [h0, hz]
    simp
  | cons p l ih =>
    intro hl
    obtain ⟨c, hc⟩ := hl p List.mem_cons_self
    have hsplit : (fun m : K → ℤ => ((p :: l).map fun q => h q (m - s q)).sum) =
        shiftFn (s p) (h p) + fun m => (l.map fun q => h q (m - s q)).sum := by
      funext m
      simp [shiftFn]
    have hev := (h3 K _ c (s p)).1 hc
    have hsh := (h3 K _ c (s p)).2 hc
    filter_upwards [ih fun q hq => hl q (List.mem_cons_of_mem p hq), hsh] with m hm hm'
    rw [hsplit, (h1 K n bs (shiftFn (s p) (h p)) (fun m => (l.map fun q => h q (m - s q)).sum)
      0 (s p) 0).1, (h1 K n bs (h p) 0 0 (s p) 0).2.2.1]
    simp only [Pi.add_apply, List.map_cons, List.sum_cons]
    rw [hm', hm, hev]

theorem proof (h1 : MixedDiffLinear.Statement) (h2 : DegLTEventuallyConst.Statement)
    (h3 : EventualValueFacts.Statement) : IntNumOfFiltration.Statement := by
  intro F _ K _ _ ι _ n J l hdeg hJ bs
  have hfun : hilbFn J = fun m => (l.map fun p => hilbFn p.1 (m - fun k => (p.2 k : ℤ))).sum :=
    funext hJ
  have hev := eventually_mixedDiff_sum h1 h3 bs
    (fun p : Ideal (MRing ι F) × (K → ℕ) => hilbFn p.1) (fun p k => (p.2 k : ℤ)) l
    (fun p hp => h2 K n (hilbFn p.1) (hdeg p hp) bs)
  unfold intNum
  rw [hfun]
  exact (h3 K _ _ 0).1 hev

end IntNumOfFiltration

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDegLTClosure
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type}

theorem tendsto_sub_const_atTop (s : K → ℤ) :
    Filter.Tendsto (fun m : K → ℤ => m - s) Filter.atTop Filter.atTop := by
  simpa [sub_eq_add_neg] using
    Filter.tendsto_atTop_add_const_right Filter.atTop (-s) Filter.tendsto_id

theorem diffStep_eventuallyEq (b : K → ℤ) {F G : (K → ℤ) → ℤ} (h : F =ᶠ[Filter.atTop] G) :
    diffStep b F =ᶠ[Filter.atTop] diffStep b G := by
  have h' : ∀ᶠ m in Filter.atTop, F (m - b) = G (m - b) := (tendsto_sub_const_atTop b).eventually h
  filter_upwards [h, h'] with m hm hm'
  simp only [diffStep, hm, hm']

theorem foldr_diffStep_eventuallyEq (l : List (K → ℤ)) {F G : (K → ℤ) → ℤ}
    (h : F =ᶠ[Filter.atTop] G) :
    l.foldr diffStep F =ᶠ[Filter.atTop] l.foldr diffStep G := by
  induction l with
  | nil => simpa using h
  | cons b l ih =>
    simp only [List.foldr_cons]
    exact diffStep_eventuallyEq b ih

theorem DegLTClosure.proof (h1 : MixedDiffLinear.Statement) : DegLTClosure.Statement := by
  intro K n f g c s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hf hg bs
    filter_upwards [hf bs, hg bs] with m hm hm'
    rw [(h1 K n bs f g c s 0).1, Pi.add_apply, hm, hm', add_zero]
  · intro hf bs
    filter_upwards [hf bs] with m hm
    rw [(h1 K n bs f g c s 0).2.1, Pi.smul_apply, hm, smul_zero]
  · intro hf bs
    have h' := (tendsto_sub_const_atTop s).eventually (hf bs)
    filter_upwards [h'] with m hm
    rw [(h1 K n bs f g c s 0).2.2.1]
    exact hm
  · intro hf bs
    have hz : ∀ᶠ m in Filter.atTop, mixedDiff (fun i : Fin n => bs i.succ) f m = 0 :=
      hf (fun i => bs i.succ)
    have hz' := (tendsto_sub_const_atTop (bs 0)).eventually hz
    filter_upwards [hz, hz'] with m hm hm'
    have e : mixedDiff bs f = diffStep (bs 0) (mixedDiff (fun i : Fin n => bs i.succ) f) := by
      unfold mixedDiff
      rw [List.ofFn_succ, List.foldr_cons]
    rw [e]
    simp only [diffStep, hm, hm', sub_zero]
  · intro hfg hf bs
    have e : mixedDiff bs f =ᶠ[Filter.atTop] mixedDiff bs g :=
      foldr_diffStep_eventuallyEq (List.ofFn bs) hfg
    filter_upwards [e, hf bs] with m hm hm'
    rw [← hm, hm']

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGradedPieceFree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem finite_setOf_weight_blockWeight_eq {K : Type} [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (m : K → ℕ) :
    {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite := by
  refine ((Set.Finite.pi' fun v : (Σ k, ι k) => Set.finite_le_nat (m v.1)).preimage
    DFunLike.coe_injective.injOn).subset ?_
  intro d hd
  simp only [Set.mem_ofPred_eq] at hd
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  intro v
  rw [← hd, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  by_cases hv : v ∈ d.support
  · refine le_trans ?_ (Finset.single_le_sum
      (f := fun u => (d u • blockWeight ι u) v.1) (fun _ _ => Nat.zero_le _) hv)
    simp [blockWeight]
  · simp [Finsupp.notMem_support_iff.mp hv]

theorem mem_of_C_pow_mul_mem {O : Type u} [CommRing O] {K : Type} {ι : K → Type}
    {P : Ideal (MRing ι O)} {ϖ : O} (hP : ∀ x, C ϖ * x ∈ P → x ∈ P) :
    ∀ (n : ℕ) (y : MRing ι O), C (ϖ ^ n) * y ∈ P → y ∈ P := by
  intro n
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    apply hP
    apply ih
    rwa [pow_succ, map_mul, mul_assoc] at hy

theorem GradedPieceFree.proof : GradedPieceFree.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P hP m
  have hfg : (weightedHomogeneousSubmodule O (blockWeight ι) m).FG := by
    rw [weightedHomogeneousSubmodule_eq_finsupp_supported, ← Module.Finite.iff_fg]
    have := (finite_setOf_weight_blockWeight_eq ι m).to_subtype
    exact Module.Finite.of_basis (basisRestrictSupport O _)
  have hfin : Module.Finite O (gradedPieceR P m) := Module.Finite.iff_fg.mpr (hfg.map _)
  have htf : Module.IsTorsionFree O (gradedPieceR P m) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c x hcx => ?_
    by_cases hc : c = 0
    · exact Or.inl hc
    right
    obtain ⟨n, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (x : MRing ι O ⧸ P)
    have h1 : ((↑w * ϖ ^ n) • (x : MRing ι O ⧸ P)) = 0 := congrArg Subtype.val hcx
    rw [← hy, ← Ideal.Quotient.mkₐ_eq_mk O, ← map_smul, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, smul_eq_C_mul] at h1
    have h2 : C (ϖ ^ n) * y ∈ P := by
      have := P.mul_mem_left (C (↑w⁻¹ : O)) h1
      rwa [← mul_assoc, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul] at this
    apply Subtype.ext
    rw [← hy, Submodule.coe_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact mem_of_C_pow_mul_mem hP n y h2
  exact ⟨Module.free_of_finite_type_torsion_free', hfin⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericPieceRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section GenericPiece

variable {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [DecidableEq K] {ι : K → Type*}

theorem isWeightedHomogeneous_map_coeff {R S σ M : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] (f : R →+* S) {w : σ → M} {g : MvPolynomial σ R} {b : M}
    (h : IsWeightedHomogeneous w g b) : IsWeightedHomogeneous w (map f g) b := by
  intro d hd
  apply h
  intro h0
  rw [coeff_map, h0, map_zero] at hd
  exact hd rfl

theorem isWeightedHomogeneous_of_map_coeff {R S σ M : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] (f : R →+* S) (hf : Function.Injective f) {w : σ → M}
    {g : MvPolynomial σ R} {b : M} (h : IsWeightedHomogeneous w (map f g) b) :
    IsWeightedHomogeneous w g b := by
  intro d hd
  apply h
  rw [coeff_map]
  exact (map_ne_zero_iff f hf).mpr hd

def genFibQuot (P : Ideal (MRing ι O)) :
    (MRing ι O ⧸ P) →ₐ[O] (MRing ι (FractionRing O) ⧸ genFib P) :=
  Ideal.quotientMapₐ (genFib P) (mapAlgHom (Algebra.ofId O (FractionRing O)))
    (fun _ hx => Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ hx))

omit [IsDomain O] [DecidableEq K] in
theorem genFibQuot_mk (P : Ideal (MRing ι O)) (g : MRing ι O) :
    genFibQuot P (Ideal.Quotient.mk P g) =
      Ideal.Quotient.mk (genFib P) (map (algebraMap O (FractionRing O)) g) := rfl

def genFibPiece (P : Ideal (MRing ι O)) (m : K → ℕ) :
    gradedPieceR P m →ₗ[O] gradedPiece (genFib P) m where
  toFun x := ⟨genFibQuot P x.1, by
    obtain ⟨g, hg, hgx⟩ := Submodule.mem_map.mp x.2
    refine Submodule.mem_map.mpr ⟨map (algebraMap O (FractionRing O)) g, ?_, ?_⟩
    · exact (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
        (isWeightedHomogeneous_map_coeff _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hg))
    · rw [← hgx]
      rfl⟩
  map_add' x y := Subtype.ext (map_add (genFibQuot P) x.1 y.1)
  map_smul' c x := Subtype.ext ((genFibQuot P).toLinearMap.map_smul c x.1)

theorem isLocalizedModule_genFibPiece (P : Ideal (MRing ι O)) (m : K → ℕ) :
    IsLocalizedModule (nonZeroDivisors O) (genFibPiece P m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [Module.End.isUnit_iff]
    have hx : algebraMap O (FractionRing O) x ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
    constructor
    · intro y z h
      have h' : algebraMap O (FractionRing O) x • y = algebraMap O (FractionRing O) x • z := by
        simpa only [Module.algebraMap_end_apply, algebraMap_smul] using h
      exact smul_right_injective _ hx h'
    · intro y
      refine ⟨(algebraMap O (FractionRing O) x)⁻¹ • y, ?_⟩
      rw [Module.algebraMap_end_apply, ← algebraMap_smul (FractionRing O), smul_smul,
        mul_inv_cancel₀ hx, one_smul]
  · intro y
    obtain ⟨q, hq⟩ := y
    obtain ⟨F, hF, rfl⟩ := Submodule.mem_map.mp hq
    let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k, ι k) (R := O) (S := FractionRing O)
    obtain ⟨⟨g, c⟩, hgc⟩ :=
      IsLocalization.surj ((nonZeroDivisors O).map (C (σ := Σ k, ι k))) F
    obtain ⟨b, hb, hbc⟩ := Submonoid.mem_map.mp c.2
    simp only [algebraMap_def, ← hbc, map_C] at hgc
    have hFh : IsWeightedHomogeneous (blockWeight ι) F m :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mp hF
    have hmg : IsWeightedHomogeneous (blockWeight ι) (map (algebraMap O (FractionRing O)) g) m := by
      rw [← hgc]
      intro d hd
      rw [mul_comm, coeff_C_mul] at hd
      exact hFh (right_ne_zero_of_mul hd)
    have hg : IsWeightedHomogeneous (blockWeight ι) g m :=
      isWeightedHomogeneous_of_map_coeff _ (IsFractionRing.injective O (FractionRing O)) hmg
    refine ⟨(⟨Ideal.Quotient.mk P g, Submodule.mem_map.mpr
      ⟨g, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg, rfl⟩⟩, ⟨b, hb⟩), ?_⟩
    apply Subtype.ext
    change b • (Ideal.Quotient.mkₐ (FractionRing O) (genFib P)) F =
      genFibQuot P (Ideal.Quotient.mk P g)
    rw [genFibQuot_mk, ← hgc, ← algebraMap_smul (FractionRing O), ← map_smul, smul_eq_C_mul,
      mul_comm, Ideal.Quotient.mkₐ_eq_mk]
  · intro x₁ x₂ h
    obtain ⟨q₁, hq₁⟩ := x₁
    obtain ⟨q₂, hq₂⟩ := x₂
    obtain ⟨g₁, rfl⟩ := Ideal.Quotient.mk_surjective q₁
    obtain ⟨g₂, rfl⟩ := Ideal.Quotient.mk_surjective q₂
    have h₀ : genFibQuot P (Ideal.Quotient.mk P g₁) = genFibQuot P (Ideal.Quotient.mk P g₂) :=
      congrArg Subtype.val h
    rw [genFibQuot_mk, genFibQuot_mk, Ideal.Quotient.eq, ← map_sub] at h₀
    let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k, ι k) (R := O) (S := FractionRing O)
    rw [genFib, ← algebraMap_def,
      IsLocalization.mem_map_algebraMap_iff ((nonZeroDivisors O).map (C (σ := Σ k, ι k)))
        (MRing ι (FractionRing O))] at h₀
    obtain ⟨⟨⟨p, hp⟩, ⟨c, hc⟩⟩, hpc⟩ := h₀
    obtain ⟨b, hb, rfl⟩ := Submonoid.mem_map.mp hc
    simp only [algebraMap_def, ← map_mul] at hpc
    have hp' : (g₁ - g₂) * C b = p :=
      map_injective _ (IsFractionRing.injective O (FractionRing O)) hpc
    refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
    change b • (Ideal.Quotient.mkₐ O P) g₁ = b • (Ideal.Quotient.mkₐ O P) g₂
    rw [← map_smul, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, ← smul_sub,
      smul_eq_C_mul, mul_comm, hp']
    exact hp

theorem GenericPieceRank.proof : GenericPieceRank.Statement := by
  intro O _ _ _ K _ _ ι _ P _ m
  have := isLocalizedModule_genFibPiece P m
  rw [IsFractionRing.finrank_right_eq O (FractionRing O),
    IsLocalizedModule.finrank_eq (p := nonZeroDivisors O) (f := genFibPiece P m) (hp := le_rfl)]

end GenericPiece

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutPieces
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace CutPieces

variable {F : Type*} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem weightedHomogeneousSubmodule_le_total (m : K → ℕ) :
    weightedHomogeneousSubmodule F (blockWeight ι) m ≤
      weightedHomogeneousSubmodule F (fun _ : (Σ k, ι k) => (1 : ℕ)) (∑ k, m k) := by
  intro f hf
  rw [mem_weightedHomogeneousSubmodule] at hf ⊢
  intro d hd
  rw [← hf hd, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [blockWeight, Pi.single_apply]

instance finiteDimensional [∀ k, Fintype (ι k)] (m : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) m) := by
  have : Module.Finite F
      (weightedHomogeneousSubmodule F (fun _ : (Σ k, ι k) => (1 : ℕ)) (∑ k, m k)) :=
    Module.Finite.iff_fg.mpr (weightedHomogeneousSubmodule_fg (R := F) (w := fun _ => 1) (hw := fun _ => one_ne_zero) (n := _))
  exact Submodule.finiteDimensional_of_le (weightedHomogeneousSubmodule_le_total m)

attribute [local instance] MvPolynomial.weightedGradedAlgebra


open Classical in
theorem component_mul {x : MRing ι F} {e : K → ℕ} (hx : IsMultiHomog x e) (y : MRing ι F)
    (m : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) m (x * y) =
      if e ≤ m then x * weightedHomogeneousComponent (blockWeight ι) (m - e) y else 0 := by
  have key : ∀ (p : MRing ι F) (n : K → ℕ),
      (DirectSum.decompose (weightedHomogeneousSubmodule F (blockWeight ι)) p n : MRing ι F) =
        weightedHomogeneousComponent (blockWeight ι) n p :=
    fun p n => weightedDecomposition.decompose'_apply F _ p n
  have hx' : x ∈ weightedHomogeneousSubmodule F (blockWeight ι) e := hx
  split_ifs with h
  · have := DirectSum.coe_decompose_mul_of_left_mem_of_le
      (𝒜 := weightedHomogeneousSubmodule F (blockWeight ι)) (b := y) hx' h
    rwa [key, key] at this
  · have := DirectSum.coe_decompose_mul_of_left_mem_of_not_le
      (𝒜 := weightedHomogeneousSubmodule F (blockWeight ι)) (b := y) (n := m) hx' h
    rwa [key] at this

end CutPieces

theorem CutPieces.proof : CutPieces.Statement := by
  intro F _ K _ _ ι _ I x e m hI hx hnzd
  set S := weightedHomogeneousSubmodule F (blockWeight ι) with hS
  by_cases hx0 : x = 0
  · have hI1 : I = ⊤ := (Ideal.eq_top_iff_one I).2 (hnzd 1 (by simp [hx0]))
    subst hI1
    have e1 : S m ⊓ ((⊤ : Ideal (MRing ι F)) ⊔ Ideal.span {x}).restrictScalars F = S m := by
      rw [top_sup_eq, Submodule.restrictScalars_top, inf_top_eq]
    have e2 : ∀ n, S n ⊓ (⊤ : Ideal (MRing ι F)).restrictScalars F = S n := fun n => by
      rw [Submodule.restrictScalars_top, inf_top_eq]
    rw [e1, e2, e2]
    split_ifs <;> simp

  set μ := LinearMap.mulLeft F x with hμ
  have hμinj : Function.Injective μ := fun a b h => mul_left_cancel₀ hx0 h
  have hx' : x ∈ S e := hx

  have hsplit : ∀ f ∈ S m, f ∈ I ⊔ Ideal.span {x} →
      ∃ i ∈ S m ⊓ I.restrictScalars F, ∃ y : MRing ι F,
        f = i + weightedHomogeneousComponent (blockWeight ι) m (x * y) := by
    intro f hf hfI
    obtain ⟨i, hi, z, hz, rfl⟩ := Submodule.mem_sup.mp hfI
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hz
    refine ⟨weightedHomogeneousComponent (blockWeight ι) m i,
      ⟨weightedHomogeneousComponent_mem _ _ _, hI i hi m⟩, y, ?_⟩
    classical
    have h1 := weightedHomogeneousComponent_of_mem (m := m) hf
    rw [if_pos rfl, map_add (f := _)] at h1
    exact h1.symm
  by_cases hem : e ≤ m
  · rw [if_pos hem]
    set A := S m ⊓ I.restrictScalars F
    set B := (S (m - e)).map μ
    have hsup : S m ⊓ (I ⊔ Ideal.span {x}).restrictScalars F = A ⊔ B := by
      apply le_antisymm
      · rintro f ⟨hf, hfI⟩
        obtain ⟨i, hi, y, rfl⟩ := hsplit f hf hfI
        rw [CutPieces.component_mul hx, if_pos hem]
        exact Submodule.add_mem_sup hi
          ⟨_, weightedHomogeneousComponent_mem _ _ _, rfl⟩
      · refine sup_le (inf_le_inf_left _ (Submodule.restrictScalars_mono F le_sup_left)) ?_
        rintro _ ⟨s, hs, rfl⟩
        refine ⟨?_, Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr (dvd_mul_right x s))⟩
        have := IsWeightedHomogeneous.mul hx' hs
        rwa [add_tsub_cancel_of_le hem] at this
    have hinf : A ⊓ B = (S (m - e) ⊓ I.restrictScalars F).map μ := by
      apply le_antisymm
      · rintro _ ⟨⟨_, hI'⟩, ⟨s, hs, rfl⟩⟩
        exact ⟨s, ⟨hs, hnzd s hI'⟩, rfl⟩
      · rintro _ ⟨s, ⟨hs, hsI⟩, rfl⟩
        refine ⟨⟨?_, I.mul_mem_left x hsI⟩, ⟨s, hs, rfl⟩⟩
        have := IsWeightedHomogeneous.mul hx' hs
        rwa [add_tsub_cancel_of_le hem] at this
    have hA : FiniteDimensional F A := Submodule.finiteDimensional_of_le inf_le_left
    have key := Submodule.finrank_sup_add_finrank_inf_eq A B
    have h1 : Module.finrank F B = Module.finrank F (S (m - e)) :=
      (Submodule.equivMapOfInjective μ hμinj _).finrank_eq.symm
    have h2 : Module.finrank F ↥((S (m - e) ⊓ I.restrictScalars F).map μ) =
        Module.finrank F ↥(S (m - e) ⊓ I.restrictScalars F) :=
      (Submodule.equivMapOfInjective μ hμinj _).finrank_eq.symm
    rw [hinf, h1, h2] at key
    rw [hsup]
    omega
  · rw [if_neg hem, add_zero]
    have hsup : S m ⊓ (I ⊔ Ideal.span {x}).restrictScalars F = S m ⊓ I.restrictScalars F := by
      apply le_antisymm
      · rintro f ⟨hf, hfI⟩
        obtain ⟨i, hi, y, rfl⟩ := hsplit f hf hfI
        rw [CutPieces.component_mul hx, if_neg hem, add_zero]
        exact hi
      · exact inf_le_inf_left _ (Submodule.restrictScalars_mono F le_sup_left)
    rw [hsup]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlockAdjoinPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace BlockAdjoinPrime

variable {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}


open Classical in
def killB (B : Set K) : MRing ι R →ₐ[R] MRing ι R :=
  by
    classical
    exact aeval fun v => if v.1 ∈ B then 0 else X v

def varIdeal (B : Set K) : Ideal (MRing ι R) :=
  Ideal.span {p | ∃ v : Σ k, ι k, v.1 ∈ B ∧ p = X v}

theorem killB_X_of_mem (B : Set K) {v : Σ k, ι k} (hv : v.1 ∈ B) :
    killB (R := R) B (X v) = 0 := by
  classical
  simp [killB, hv]

theorem killB_X_of_not_mem (B : Set K) {v : Σ k, ι k} (hv : v.1 ∉ B) :
    killB (R := R) B (X v) = X v := by
  classical
  simp [killB, hv]

open Classical in
theorem killB_monomial (B : Set K) (d : (Σ k, ι k) →₀ ℕ) (a : R) :
    killB (R := R) B (monomial d a) =
      if ∀ v ∈ d.support, v.1 ∉ B then monomial d a else 0 := by
  rw [killB, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, algebraMap_eq]
    congr 1
    refine Finsupp.prod_congr fun v hv => ?_
    rw [if_neg (h v hv)]
  · push Not at h
    obtain ⟨v, hv, hB⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero hv, mul_zero]
    rw [if_pos hB, zero_pow (Finsupp.mem_support_iff.mp hv)]

open Classical in
theorem coeff_killB (B : Set K) (p : MRing ι R) (d : (Σ k, ι k) →₀ ℕ) :
    AddMonoidAlgebra.coeff (killB B p) d = if ∀ v ∈ d.support, v.1 ∉ B then AddMonoidAlgebra.coeff p d else 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial e a =>
    rw [killB_monomial]
    by_cases hed : e = d
    · subst hed
      split_ifs <;> simp
    · split_ifs <;> simp [coeff_monomial, hed]
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, hp, hq]
    split_ifs <;> simp

theorem sub_killB_mem (B : Set K) (p : MRing ι R) : p - killB B p ∈ varIdeal (R := R) B := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add (f := _), add_sub_add_comm]
    exact add_mem hp hq
  | mul_X p v hp =>
    have e : p * X v - killB B (p * X v) =
        (p - killB B p) * X v + killB B p * (X v - killB B (X v)) := by
      rw [map_mul]; ring
    rw [e]
    refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    by_cases hv : v.1 ∈ B
    · rw [killB_X_of_mem B hv, sub_zero]
      exact Ideal.subset_span ⟨v, hv, rfl⟩
    · rw [killB_X_of_not_mem B hv, sub_self]
      exact zero_mem _

variable [DecidableEq K]

theorem weight_eq_zero_iff (d : (Σ k, ι k) →₀ ℕ) (B : Set K) :
    (∀ k ∈ B, Finsupp.weight (blockWeight ι) d k = 0) ↔ ∀ v ∈ d.support, v.1 ∉ B := by
  have hw : ∀ k, Finsupp.weight (blockWeight ι) d k =
      ∑ i ∈ d.support, d i * (Pi.single i.1 1 : K → ℕ) k := by
    intro k
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    rfl
  constructor
  · intro h v hv hB
    have h0 := h v.1 hB
    rw [hw, Finset.sum_eq_zero_iff] at h0
    have := h0 v hv
    simp [Finsupp.mem_support_iff.mp hv] at this
  · intro h k hk
    rw [hw, Finset.sum_eq_zero_iff]
    intro i hi
    have hik : i.1 ≠ k := fun e => h i hi (e ▸ hk)
    simp [Ne.symm hik]

theorem killB_mem {Q : Ideal (MRing ι R)} (hQ : IsMultiHomogIdeal Q) (B : Set K)
    {q : MRing ι R} (hq : q ∈ Q) : killB B q ∈ Q := by
  classical
  let M := (q.support.image (Finsupp.weight (blockWeight ι))).filter (fun m => ∀ k ∈ B, m k = 0)
  have key : killB B q = ∑ m ∈ M, weightedHomogeneousComponent (blockWeight ι) m q := by
    ext d
    rw [coeff_killB, coeff_sum]
    simp_rw [coeff_weightedHomogeneousComponent]
    rw [Finset.sum_ite_eq]
    by_cases hd : AddMonoidAlgebra.coeff q d = 0
    · simp [hd]
    · have hmem : d ∈ q.support := mem_support_iff.mpr hd
      have hiff : Finsupp.weight (blockWeight ι) d ∈ M ↔ ∀ v ∈ d.support, v.1 ∉ B := by
        rw [← weight_eq_zero_iff]
        simp only [M, Finset.mem_filter, Finset.mem_image]
        exact ⟨fun h => h.2, fun h => ⟨⟨d, hmem, rfl⟩, h⟩⟩
      by_cases hP : ∀ v ∈ d.support, v.1 ∉ B
      · rw [if_pos hP, if_pos (hiff.mpr hP)]
      · rw [if_neg hP, if_neg (fun h => hP (hiff.mp h))]
  rw [key]
  exact Q.sum_mem fun m _ => hQ q hq m

theorem sup_eq_comap {Q : Ideal (MRing ι R)} (hQ : IsMultiHomogIdeal Q) (B : Set K) :
    Q ⊔ varIdeal B = Q.comap (killB B) := by
  apply le_antisymm
  · refine sup_le (fun q hq => killB_mem hQ B hq) ?_
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨v, hv, rfl⟩
    show killB B (X v) ∈ Q
    rw [killB_X_of_mem B hv]
    exact zero_mem _
  · intro p hp
    have : p = killB B p + (p - killB B p) := by ring
    rw [this]
    exact add_mem (Ideal.mem_sup_left hp) (Ideal.mem_sup_right (sub_killB_mem B p))

theorem proof : BlockAdjoinPrime.Statement := by
  intro R _ K _ _ ι Q B hP hQ
  have h := sup_eq_comap (R := R) hQ B
  change (Q ⊔ varIdeal B).IsPrime ∧ ∀ v : Σ k, ι k, v.1 ∉ B → (X v ∈ Q ⊔ varIdeal B ↔ X v ∈ Q)
  rw [h]
  refine ⟨Ideal.IsPrime.comap (killB B) (hK := hP), fun v hv => ?_⟩
  rw [Ideal.mem_comap, killB_X_of_not_mem B hv]

end BlockAdjoinPrime

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialPieceRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Reduction

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem map_residue_weightedHomogeneousComponent (m : K → ℕ) (f : MRing ι O) :
    MvPolynomial.map (IsLocalRing.residue O) (weightedHomogeneousComponent (blockWeight ι) m f) =
      weightedHomogeneousComponent (blockWeight ι) m (MvPolynomial.map (IsLocalRing.residue O) f) := by
  classical
  ext d
  simp only [coeff_map, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

theorem map_residue_mem_weightedHomogeneousSubmodule {m : K → ℕ} {f : MRing ι O}
    (hf : f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m) :
    MvPolynomial.map (IsLocalRing.residue O) f ∈
      weightedHomogeneousSubmodule (IsLocalRing.ResidueField O) (blockWeight ι) m := by
  rw [mem_weightedHomogeneousSubmodule] at hf ⊢
  rw [← weightedHomogeneousComponent_eq_self hf, map_residue_weightedHomogeneousComponent]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem exists_form_map_residue_eq {m : K → ℕ} {g : MRing ι (IsLocalRing.ResidueField O)}
    (hg : g ∈ weightedHomogeneousSubmodule (IsLocalRing.ResidueField O) (blockWeight ι) m) :
    ∃ f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m,
      MvPolynomial.map (IsLocalRing.residue O) f = g := by
  obtain ⟨f, rfl⟩ := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective g
  refine ⟨weightedHomogeneousComponent (blockWeight ι) m f, ?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · rw [map_residue_weightedHomogeneousComponent]
    exact weightedHomogeneousComponent_eq_self ((mem_weightedHomogeneousSubmodule _ _ _ _).1 hg)

theorem exists_eq_add_mul_of_map_residue_mem {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)}
    (hP : IsMultiHomogIdeal P) {m : K → ℕ} {f : MRing ι O}
    (hf : f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m)
    (hfP : MvPolynomial.map (IsLocalRing.residue O) f ∈ specialIdeal P) :
    ∃ p ∈ P, ∃ g ∈ weightedHomogeneousSubmodule O (blockWeight ι) m, f = p + C ϖ * g := by
  have hfh := (mem_weightedHomogeneousSubmodule _ _ _ _).1 hf
  obtain ⟨p, hp, hpf⟩ := (Ideal.mem_map_iff_of_surjective _
    (MvPolynomial.map_surjective _ IsLocalRing.residue_surjective)).1 hfP
  have hpm : weightedHomogeneousComponent (blockWeight ι) m p ∈ P := hP p hp m
  have hker : f - weightedHomogeneousComponent (blockWeight ι) m p ∈
      RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) : MRing ι O →+* _) := by
    rw [RingHom.mem_ker, map_sub, map_residue_weightedHomogeneousComponent, hpf,
      weightedHomogeneousComponent_eq_self ((mem_weightedHomogeneousSubmodule _ _ _ _).1
        (map_residue_mem_weightedHomogeneousSubmodule hf)), sub_self]
  rw [MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton, Ideal.mem_span_singleton'] at hker
  obtain ⟨g, hg⟩ := hker
  refine ⟨_, hpm, weightedHomogeneousComponent (blockWeight ι) m g, ?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · have h2 : C ϖ * weightedHomogeneousComponent (blockWeight ι) m g =
        f - weightedHomogeneousComponent (blockWeight ι) m p := by
      rw [C_mul', ← map_smul, ← C_mul', mul_comm, hg, map_sub, weightedHomogeneousComponent_eq_self hfh,
        weightedHomogeneousComponent_eq_self (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]
    rw [h2]
    ring

end Reduction

theorem SpecialPieceRank.proof (h1 : GradedPieceFree.Statement.{u}) : SpecialPieceRank.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P hP htor m
  obtain ⟨hfree, hfin⟩ := h1 O ϖ hϖ K ι P htor m
  let ρ : MRing ι O →ₐ[O] MRing ι (IsLocalRing.ResidueField O) :=
    mapAlgHom (Algebra.ofId O (IsLocalRing.ResidueField O))
  have hρ : ∀ f, ρ f = MvPolynomial.map (IsLocalRing.residue O) f := fun f => rfl
  have hle : P ≤ (specialIdeal P).comap ρ := fun x hx => by
    rw [Ideal.mem_comap, hρ]
    exact Ideal.mem_map_of_mem _ hx
  let T := Ideal.quotientMapₐ (specialIdeal P) ρ hle
  have hT : ∀ f, T (Ideal.Quotient.mk P f) =
      Ideal.Quotient.mk (specialIdeal P) (MvPolynomial.map (IsLocalRing.residue O) f) := fun f => rfl
  have hTM : ∀ y ∈ gradedPieceR P m, T y ∈ gradedPiece (specialIdeal P) m := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    exact Submodule.mem_map.2 ⟨_, map_residue_mem_weightedHomogeneousSubmodule hf, (hT f).symm⟩
  let b := Module.Free.chooseBasis O (gradedPieceR P m)
  let v : Module.Free.ChooseBasisIndex O (gradedPieceR P m) → gradedPiece (specialIdeal P) m :=
    fun i => ⟨T (b i), hTM _ (b i).2⟩
  have hv : ∀ i, ((v i : gradedPiece (specialIdeal P) m) : _) = T (b i) := fun i => rfl
  have hsmul : ∀ (c : O) (x : MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P),
      IsLocalRing.residue O c • x = c • x := fun c x => by
    rw [← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
  have hli : LinearIndependent (IsLocalRing.ResidueField O) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose c hc using fun j => IsLocalRing.residue_surjective (g j)
    let y : gradedPieceR P m := ∑ j, c j • b j
    obtain ⟨f, hf, hfy⟩ := Submodule.mem_map.1 y.2
    have hfy' : Ideal.Quotient.mk P f = (y : MRing ι O ⧸ P) := hfy
    have h0 : Ideal.Quotient.mk (specialIdeal P) (MvPolynomial.map (IsLocalRing.residue O) f) = 0 := by
      rw [← hT, hfy']
      have hg' := congrArg Subtype.val hg
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, hv] at hg'
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [y, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
      rw [← hg']
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hc j, hsmul]
    obtain ⟨p, hp, g0, hg0, hfp⟩ :=
      exists_eq_add_mul_of_map_residue_mem hϖ hP hf (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    let z : gradedPieceR P m := ⟨Ideal.Quotient.mk P g0, Submodule.mem_map.2 ⟨g0, hg0, rfl⟩⟩
    have hyz : y = ϖ • z := by
      apply Subtype.ext
      rw [← hfy', hfp, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_add, map_mul,
        Submodule.coe_smul]
      show _ = ϖ • Ideal.Quotient.mk P g0
      rw [← map_mul, C_mul']
      exact map_smul (Ideal.Quotient.mkₐ O P) ϖ g0
    have hbli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hbli
    have key : ∑ j, (c j - ϖ * b.repr z j) • b j = 0 := by
      have e1 : ∑ j, (c j - ϖ * b.repr z j) • b j =
          ∑ j, c j • b j - ϖ • ∑ j, b.repr z j • b j := by
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact (sub_smul (c j) (ϖ * b.repr z j) (b j)).trans
          (congrArg (c j • b j - ·) (mul_smul ϖ (b.repr z j) (b j)))
      rw [e1, b.sum_repr]
      exact sub_eq_zero.2 hyz
    have hi := hbli _ key i
    rw [← hc i, sub_eq_zero.1 hi, map_mul, (IsLocalRing.residue_eq_zero_iff ϖ).2
      ((IsLocalRing.mem_maximalIdeal ϖ).2 (mem_nonunits_iff.2 hϖ.not_isUnit)), zero_mul]
  have hsp : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField O) (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨f, hf, rfl⟩ := exists_form_map_residue_eq hg
    let y : gradedPieceR P m := ⟨Ideal.Quotient.mk P f, Submodule.mem_map.2 ⟨f, hf, rfl⟩⟩
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun j => IsLocalRing.residue O (b.repr y j), ?_⟩
    apply Subtype.ext
    have hy := congrArg Subtype.val (b.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hy ⊢
    change _ = T (y : MRing ι O ⧸ P)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hy, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hv, hsmul]
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Module.finrank_eq_card_chooseBasisIndex]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
