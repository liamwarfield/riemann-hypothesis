module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsG

@[expose] public section

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpenB
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}

theorem norm_coe_K (x : K) : ‖(x : PadicAlgCl p)‖ = ‖x‖ := rfl

theorem UK_eq_preimage : (UK p K : Set Kˣ) = Units.val ⁻¹' Metric.sphere (0 : K) 1 := by
  ext x
  simp only [Set.mem_preimage, mem_sphere_zero_iff_norm]
  rfl

theorem image_UK : Units.val '' (UK p K : Set Kˣ) = Metric.sphere (0 : K) 1 := by
  rw [UK_eq_preimage, Set.image_preimage_eq_iff]
  intro x hx
  have hx' : ‖x‖ = 1 := by simpa using hx
  have h0 : x ≠ 0 := by
    rintro rfl
    simp at hx'
  exact ⟨Units.mk0 x h0, rfl⟩

theorem isCompact_UK' (hK : FiniteDimensional ℚ_[p] K) : IsCompact (UK p K : Set Kˣ) := by
  have : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  rw [Units.isEmbedding_val₀.isCompact_iff, image_UK]
  exact isCompact_sphere _ _

theorem mem_UK_of_norm_sub_one_lt (x : Kˣ) (hx : ‖(x : K) - 1‖ < 1) : x ∈ UK p K := by
  show ‖((x : K) : PadicAlgCl p)‖ = 1
  rw [norm_coe_K]
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (x : K) - 1) (y := 1)
    (by rw [norm_one]; exact hx.ne)
  rw [sub_add_cancel, norm_one, max_eq_right hx.le] at h
  exact h

theorem mem_nhds_one_iff (S : Set Kˣ) :
    S ∈ nhds (1 : Kˣ) ↔ ∃ ε > 0, ∀ x : Kˣ, ‖(x : K) - 1‖ < ε → x ∈ S := by
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap, Units.val_one]
  constructor
  · rintro ⟨t, ht, hts⟩
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 ht
    refine ⟨ε, hε, fun x hx => hts (hb ?_)⟩
    rw [Metric.mem_ball, dist_eq_norm]; exact hx
  · rintro ⟨ε, hε, h⟩
    refine ⟨Metric.ball 1 ε, Metric.ball_mem_nhds _ hε, fun x hx => h x ?_⟩
    have : (x : K) ∈ Metric.ball (1 : K) ε := hx
    rwa [Metric.mem_ball, dist_eq_norm] at this

theorem isOpen_UKi (i : ℕ) : IsOpen (UKi p K i : Set Kˣ) := by
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  rw [mem_nhds_one_iff]
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨min 1 ((p : ℝ) ^ (- (i : ℝ) / eK p K)), lt_min one_pos (Real.rpow_pos_of_pos hp _), fun x hx => ?_⟩
  exact (mem_UKi_iff p K i x).2 ⟨mem_UK_of_norm_sub_one_lt x (hx.trans_le (min_le_left _ _)),
    (hx.trans_le (min_le_right _ _)).le⟩

theorem isOpen_range_pow' (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) := by
  have : CompleteSpace K := FiniteDimensional.complete ℚ_[p] K
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have hd : HasStrictDerivAt (fun x : K => x ^ n) ((n : K) * 1 ^ (n - 1)) 1 := hasStrictDerivAt_pow n 1
  have hne : ((n : K) * 1 ^ (n - 1)) ≠ 0 := by
    rw [one_pow, mul_one]; exact_mod_cast hn.ne'
  have hm := hd.map_nhds_eq hne
  simp only [one_pow] at hm
  have hr : Set.range (fun x : K => x ^ n) ∈ nhds (1 : K) := by
    rw [← hm]; exact Filter.range_mem_map
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap, Units.val_one]
  refine ⟨_, hr, ?_⟩
  rintro y ⟨x, hx⟩
  have hx' : x ^ n = (y : K) := hx
  have h0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hx'
    exact y.ne_zero hx'.symm
  exact ⟨Units.mk0 x h0, Units.ext (by simpa using hx')⟩

theorem finiteIndex_of_isOpen_of_vK (hK : FiniteDimensional ℚ_[p] K) (H : Subgroup Kˣ)
    (hH : IsOpen (H : Set Kˣ)) {x : Kˣ} (hx : x ∈ H) (hv : vK p K x ≠ 0) : H.FiniteIndex := by
  obtain ⟨π, hπ⟩ := exists_vK_eq_one p K hK
  have : DiscreteTopology (Kˣ ⧸ H) := QuotientGroup.discreteTopology hH
  set m := vK p K x with hm
  let C : Set Kˣ := ⋃ j ∈ Finset.range m.natAbs, (fun u => π ^ j * u) '' (UK p K : Set Kˣ)
  have hC : IsCompact C :=
    (Finset.range m.natAbs).isCompact_biUnion fun j _ =>
      (isCompact_UK' hK).image (continuous_const.mul continuous_id)
  have hfin : ((QuotientGroup.mk : Kˣ → Kˣ ⧸ H) '' C).Finite :=
    (hC.image QuotientGroup.continuous_mk).finite_of_discrete
  have hall : (QuotientGroup.mk : Kˣ → Kˣ ⧸ H) '' C = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro c
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    have hj0 : 0 ≤ vK p K y % m := Int.emod_nonneg _ hv
    have hj1 : vK p K y % m < |m| := Int.emod_lt_abs _ hv
    set j := (vK p K y % m).toNat with hj
    have hjc : (j : ℤ) = vK p K y % m := Int.toNat_of_nonneg hj0
    set k := vK p K y / m with hk
    have hu : (π ^ j)⁻¹ * y * (x ^ k)⁻¹ ∈ UK p K := by
      rw [mem_UK_iff p K hK, vK_mul, vK_mul, vK_inv, vK_inv, vK_pow, vK_zpow, hπ, hjc, ← hm]
      have := Int.emod_add_mul_ediv (vK p K y) m
      rw [← hk] at this
      linarith [mul_comm m k]
    refine ⟨π ^ j * ((π ^ j)⁻¹ * y * (x ^ k)⁻¹), ?_, ?_⟩
    · refine Set.mem_biUnion (x := j) ?_ ⟨_, hu, rfl⟩
      rw [Finset.coe_range, Set.mem_Iio]
      have : (j : ℤ) < (m.natAbs : ℤ) := by rw [hjc, Int.natCast_natAbs]; exact hj1
      exact_mod_cast this
    · rw [QuotientGroup.eq]
      have : (π ^ j * ((π ^ j)⁻¹ * y * (x ^ k)⁻¹))⁻¹ * y = x ^ k := by group
      rw [this]
      exact H.zpow_mem hx k
  have : Finite (Kˣ ⧸ H) := by
    rw [← Set.finite_univ_iff, ← hall]; exact hfin
  exact Subgroup.finiteIndex_of_finite_quotient

theorem finiteIndex_range_pow' (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    (powMonoidHom n : Kˣ →* Kˣ).range.FiniteIndex := by
  obtain ⟨π, hπ⟩ := exists_vK_eq_one p K hK
  refine finiteIndex_of_isOpen_of_vK hK _ (isOpen_range_pow' hK hn) (x := π ^ n) ⟨π, rfl⟩ ?_
  rw [vK_pow, hπ, mul_one]
  exact_mod_cast hn.ne'

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpenA
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem normHom_apply [Fintype (GK p K ⧸ subG p K L)] (y : KbarMult p) :
    normHom p K L y = ∑ c : GK p K ⧸ subG p K L, kbarRep p K c.out y := by
  unfold normHom
  rw [finsum_eq_sum_of_fintype, AddMonoidHom.finsetSum_apply]
  rfl

theorem kbarRep_mul (σ τ : GK p K) (y : KbarMult p) :
    kbarRep p K (σ * τ) y = kbarRep p K σ (kbarRep p K τ y) := by
  rw [map_mul]; rfl

theorem exists_ne_zero_KbarMult : ∃ x : KbarMult p, x ≠ 0 := by
  refine ⟨Additive.ofMul (-1 : (PadicAlgCl p)ˣ), fun h0 => ?_⟩
  have h1 : ((-1 : (PadicAlgCl p)ˣ) : PadicAlgCl p) = ((1 : (PadicAlgCl p)ˣ) : PadicAlgCl p) :=
    congrArg (fun u : (PadicAlgCl p)ˣ => (u : PadicAlgCl p)) h0
  rw [Units.val_neg, Units.val_one] at h1
  norm_num at h1

theorem normHom_of_infinite [Infinite (GK p K ⧸ subG p K L)] : normHom p K L = 0 := by
  unfold normHom
  apply finsum_of_infinite_support
  have hs : Function.support (fun c : GK p K ⧸ subG p K L => (kbarRep p K c.out).toAddMonoidHom) =
      Set.univ := by
    ext c
    simp only [mem_support, Set.mem_univ, iff_true]
    intro h0
    obtain ⟨x, hx⟩ := exists_ne_zero_KbarMult (p := p)
    apply hx
    have h1 : kbarRep p K c.out x = 0 := DFunLike.congr_fun h0 x
    have h2 : kbarRep p K (c.out⁻¹ * c.out) x = 0 := by rw [kbarRep_mul, h1, map_zero]
    rw [inv_mul_cancel, map_one] at h2
    exact h2
  rw [hs]
  exact Set.infinite_univ

theorem kbarRep_out (y : KbarMult p) (hy : y ∈ multOf p L) (σ : GK p K) :
    kbarRep p K (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out y = kbarRep p K σ y := by
  have h1 : σ⁻¹ * (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out ∈ subG p K L :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm
  have h2 : kbarRep p K (σ⁻¹ * (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out) y = y :=
    Units.ext (h1 _ hy)
  calc kbarRep p K (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out y
      = kbarRep p K (σ * (σ⁻¹ * (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out)) y := by
        rw [mul_inv_cancel_left]
    _ = kbarRep p K σ y := by rw [kbarRep_mul, h2]

theorem normHom_mem_multiplicative_group (hL : FiniteDimensional ℚ_[p] L) (y : KbarMult p) (hy : y ∈ multOf p L) :
    normHom p K L y ∈ multOf p K := by
  have := finite_GalLK (p := p) (K := K) hL
  have := Fintype.ofFinite (GK p K ⧸ subG p K L)
  rw [mem_multOf_iff_fixed (le_refl K)]
  intro σ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [normHom_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm σ) _ _ fun c => ?_
  induction c using QuotientGroup.induction_on with
  | H τ =>
    show _ = kbarRep p K (QuotientGroup.mk (σ * τ) : GK p K ⧸ subG p K L).out y
    rw [kbarRep_out y hy, kbarRep_out y hy, kbarRep_mul]

theorem normHom_layer_eq_trace_sum [(subG p K L).Normal] [Fintype (GalLK p K L)] (y : (layer p K L).V) :
    normHom p K L y.1 = (∑ g, (layer p K L).rho g y).1 := by
  refine (normHom_apply (K := K) (L := L) (y.1 : KbarMult p)).trans ?_
  have h1 : (∑ g, (layer p K L).rho g y).1 = ∑ g, ((layer p K L).rho g y).1 :=
    map_sum (Submodule.subtype _) _ _
  refine Eq.trans ?_ h1.symm
  refine Finset.sum_congr rfl fun g _ => ?_
  conv_rhs => rw [← QuotientGroup.out_eq' g]
  rfl

theorem normHom_of_mem_base (x : KbarMult p) (hx : x ∈ multOf p K) :
    normHom p K L x = degLK p K L • x := by
  rcases finite_or_infinite (GK p K ⧸ subG p K L) with hf | hi
  · have := Fintype.ofFinite (GK p K ⧸ subG p K L)
    rw [normHom_apply]
    have h1 : ∀ c : GK p K ⧸ subG p K L, kbarRep p K c.out x = x :=
      fun c => Units.ext (c.out.commutes ⟨_, hx⟩)
    simp only [h1]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl
  · rw [normHom_of_infinite]
    have h0 : degLK p K L = 0 := Subgroup.index_eq_zero_iff_infinite.2 hi
    rw [h0, zero_smul]
    rfl

theorem finite_quot_of_le {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L')
    (h' : L ≤ L') : Finite (GK p K ⧸ subG p K L) := by
  have h1 := finiteIndex_subG (p := p) (K := K) hL'
  have h2 : (subG p K L).FiniteIndex := Subgroup.finiteIndex_of_le (subG_anti h')
  exact Subgroup.finite_quotient_of_finiteIndex

theorem tower_bijective {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) (h' : L ≤ L') :
    Bijective (fun x : (GK p K ⧸ subG p K L) × (GK p L ⧸ subG p L L') =>
      (QuotientGroup.mk (x.1.out * resGK (p := p) (K := K) (L := L) h x.2.out) :
        GK p K ⧸ subG p K L')) := by
  have hres : ∀ τ : GK p L, resGK h τ ∈ subG p K L := fun τ => by
    rw [← range_resGK h]; exact ⟨τ, rfl⟩
  constructor
  · rintro ⟨c, d⟩ ⟨c', d'⟩ hcd
    have h1 : (c.out * resGK h d.out)⁻¹ * (c'.out * resGK h d'.out) ∈ subG p K L' :=
      QuotientGroup.eq.1 hcd
    have h2 : c.out⁻¹ * c'.out ∈ subG p K L := by
      have h3 := (subG p K L).mul_mem ((subG p K L).mul_mem (hres d.out) (subG_anti h' h1))
        ((subG p K L).inv_mem (hres d'.out))
      have h4 : resGK h d.out * ((c.out * resGK h d.out)⁻¹ * (c'.out * resGK h d'.out)) *
          (resGK h d'.out)⁻¹ = c.out⁻¹ * c'.out := by group
      rwa [h4] at h3
    have hc : c = c' := by
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      exact QuotientGroup.eq.2 h2
    subst hc
    have h5 : resGK h (d.out⁻¹ * d'.out) ∈ subG p K L' := by
      have h6 : (c.out * resGK h d.out)⁻¹ * (c.out * resGK h d'.out) = resGK h (d.out⁻¹ * d'.out) := by
        rw [map_mul, map_inv]; group
      rwa [h6] at h1
    have hd : d = d' := by
      rw [← QuotientGroup.out_eq' d, ← QuotientGroup.out_eq' d']
      exact QuotientGroup.eq.2 h5
    rw [hd]
  · intro e
    induction e using QuotientGroup.induction_on with
    | H σ =>
      have h1 : (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out⁻¹ * σ ∈ subG p K L :=
        QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
      have h1' : (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out⁻¹ * σ ∈ (resGK h).range := by
        rw [range_resGK h]; exact h1
      obtain ⟨τ, hτ⟩ := h1'
      refine ⟨(QuotientGroup.mk σ, QuotientGroup.mk τ), ?_⟩
      have h2 : (QuotientGroup.mk τ : GK p L ⧸ subG p L L').out⁻¹ * τ ∈ subG p L L' :=
        QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
      apply QuotientGroup.eq.2
      have h3 : ((QuotientGroup.mk σ : GK p K ⧸ subG p K L).out *
          resGK h (QuotientGroup.mk τ : GK p L ⧸ subG p L L').out)⁻¹ * σ =
          resGK h ((QuotientGroup.mk τ : GK p L ⧸ subG p L L').out⁻¹ * τ) := by
        rw [map_mul, map_inv, hτ, mul_inv_rev, mul_assoc]
      rw [h3]
      exact h2

theorem normHom_comp_normHom_of_le {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L')
    (h : K ≤ L) (h' : L ≤ L') (y : KbarMult p) (hy : y ∈ multOf p L') :
    normHom p K L (normHom p L L' y) = normHom p K L' y := by
  have := finite_quot_of_le (p := p) (K := K) hL' h'
  have := finite_quot_of_le (p := p) (K := K) hL' (le_refl L')
  have := finite_quot_of_le (p := p) (K := L) hL' (le_refl L')
  have := Fintype.ofFinite (GK p K ⧸ subG p K L)
  have := Fintype.ofFinite (GK p K ⧸ subG p K L')
  have := Fintype.ofFinite (GK p L ⧸ subG p L L')
  rw [normHom_apply, normHom_apply, normHom_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_bijective _ (tower_bijective h h') _ _ fun x => ?_
  rw [kbarRep_out y hy, kbarRep_mul]
  rfl

theorem coe_sum_KbarMult {ι : Type*} (s : Finset ι) (f : ι → KbarMult p) :
    ((Additive.toMul (∑ c ∈ s, f c) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      ∏ c ∈ s, ((Additive.toMul (f c) : (PadicAlgCl p)ˣ) : PadicAlgCl p) := by
  let F : KbarMult p →+ Additive (PadicAlgCl p) :=
    { toFun := fun x => Additive.ofMul ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h2 := congrArg Additive.toMul (map_sum F f s)
  rw [toMul_sum] at h2
  exact h2

theorem normHom_eq_algebra_norm (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (y : KbarMult p)
    (hy : y ∈ multOf p L) :
    ((Additive.toMul (normHom p K L y) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      ((Algebra.norm K (⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩ :
        IntermediateField.extendScalars h) : K) : PadicAlgCl p) := by
  have := finite_GalLK (p := p) (K := K) hL
  have := Fintype.ofFinite (GK p K ⧸ subG p K L)
  have hfin : FiniteDimensional K (IntermediateField.extendScalars h) := by
    apply Module.finite_of_finrank_pos
    rw [← degLK_eq_finrank h]
    exact degLK_pos hL
  have hbij : Bijective (fun c : GK p K ⧸ subG p K L =>
      ((c.out : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) : PadicAlgCl p →ₐ[K] PadicAlgCl p).comp
        (IntermediateField.extendScalars h).val) := by
    apply Function.Injective.bijective_of_nat_card_le
    · intro c c' hcc
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      apply QuotientGroup.eq.2
      intro x hx
      have h1 : c.out x = c'.out x := DFunLike.congr_fun hcc (⟨x, hx⟩ : IntermediateField.extendScalars h)
      show c.out⁻¹ (c'.out x) = x
      rw [← h1]
      exact c.out.symm_apply_apply x
    · rw [Nat.card_eq_fintype_card, AlgHom.card, ← degLK_eq_finrank h]
      exact le_of_eq rfl
  have h1 := Algebra.norm_eq_prod_embeddings K (PadicAlgCl p)
    (⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩ : IntermediateField.extendScalars h)
  refine Eq.trans ?_ h1.symm
  rw [normHom_apply]
  refine (coe_sum_KbarMult _ _).trans ?_
  exact Fintype.prod_bijective _ hbij _ _ fun c => rfl

theorem normGroup_antitone {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L')
    (h : K ≤ L) (h' : L ≤ L') : normGrp p K L' ≤ normGrp p K L := by
  intro x hx
  rw [mem_normGrp_iff] at hx ⊢
  obtain ⟨y, hy, hxy⟩ := hx
  exact ⟨normHom p L L' y, normHom_mem_multiplicative_group hL' y hy, by rw [normHom_comp_normHom_of_le hL' h h' y hy, hxy]⟩

theorem pow_degree_mem_normGroup (h : K ≤ L) (x : Kˣ) : x ^ degLK p K L ∈ normGrp p K L := by
  rw [mem_normGrp_iff]
  refine ⟨ofK p K (Additive.ofMul x), h (ofK_mem p K _), ?_⟩
  rw [normHom_of_mem_base _ (ofK_mem p K _), ofMul_pow, map_nsmul]

theorem normGroup_self_eq_top : normGrp p K K = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h1 : degLK p K K = 1 := by
    have h2 : subG p K K = ⊤ := eq_top_iff.2 fun σ _ x hx => σ.commutes ⟨x, hx⟩
    show (subG p K K).index = 1
    rw [h2, Subgroup.index_top]
  have h3 := pow_degree_mem_normGroup (le_refl K) x
  rwa [h1, pow_one] at h3

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem normHom_mem (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (y : KbarMult p) (hy : y ∈ multOf p L) :
    normHom p K L y ∈ multOf p K := normHom_mem_multiplicative_group hL y hy

theorem normHom_eq_algebraNorm (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (y : KbarMult p)
    (hy : y ∈ multOf p L) :
    ((Additive.toMul (normHom p K L y) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      ((Algebra.norm K (⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩ :
        IntermediateField.extendScalars h) : K) : PadicAlgCl p) :=
  normHom_eq_algebra_norm hL h y hy

theorem normHom_layer (h : K ≤ L) [(subG p K L).Normal] [Fintype (GalLK p K L)] (y : (layer p K L).V) :
    normHom p K L y.1 = (∑ g, (layer p K L).rho g y).1 := normHom_layer_eq_trace_sum y

theorem normHom_trans {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L') (h : K ≤ L) (h' : L ≤ L') (y : KbarMult p)
    (hy : y ∈ multOf p L') : normHom p K L (normHom p L L' y) = normHom p K L' y :=
  normHom_comp_normHom_of_le hL' h h' y hy

theorem normGrp_anti {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L') (h : K ≤ L) (h' : L ≤ L') :
    normGrp p K L' ≤ normGrp p K L := normGroup_antitone hL' h h'

theorem pow_degLK_mem_normGrp (h : K ≤ L) (x : Kˣ) : x ^ degLK p K L ∈ normGrp p K L :=
  pow_degree_mem_normGroup h x

theorem normGrp_self : normGrp p K K = ⊤ := normGroup_self_eq_top

theorem finiteIndex_range_pow (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    (powMonoidHom n : Kˣ →* Kˣ).range.FiniteIndex := finiteIndex_range_pow' hK hn

theorem isOpen_normGrp (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    IsOpen (normGrp p K L : Set Kˣ) :=
  Subgroup.isOpen_mono (by rintro _ ⟨x, rfl⟩; exact pow_degLK_mem_normGrp h x)
    (isOpen_range_pow' hK (degLK_pos hL))

theorem finiteIndex_normGrp (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    (normGrp p K L).FiniteIndex := by
  have := finiteIndex_range_pow' hK (degLK_pos (K := K) hL)
  exact Subgroup.finiteIndex_of_le (H := (powMonoidHom (degLK p K L) : Kˣ →* Kˣ).range)
    (by rintro _ ⟨x, rfl⟩; exact pow_degLK_mem_normGrp h x)

end ReciprocityTheory.DiscreteGroups.LocalClassField
