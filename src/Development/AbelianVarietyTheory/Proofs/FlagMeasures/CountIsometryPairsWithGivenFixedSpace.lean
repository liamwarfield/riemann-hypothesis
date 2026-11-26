module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticeMeanCountBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEmbeddedDataWithGivenFixedLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscriminantOrderCommonFixedLatticeEmbeddedData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiComplexifiedKEquivariance

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesIndexFixedTraceLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesIndexFixedTraceLe
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.TraceCount

theorem exists_gen_mod {R W : Type} [CommRing R] [IsDomain R] [AddCommGroup W] [Module R W] (C : Submodule R W)
    [Module.Finite R C] [Module.Projective R C] (m : ℕ) [Finite (R ⧸ Ideal.span {(m : R)})] :
    ∃ c : Fin (Module.finrank R C) → W, (∀ i, c i ∈ C) ∧
      ∀ y ∈ C, ∃ (r : Fin (Module.finrank R C) → R) (d : W), d ∈ C ∧ y = ∑ i, r i • c i + m • d := by
  obtain ⟨⟨v, hv⟩, -⟩ := GlobalTheory.CongIndex.quot_smul_top_span_card (R := R) (N := C) (Ideal.span {(m : R)})
  choose c hc using fun i => Submodule.Quotient.mk_surjective _ (v i)
  refine ⟨fun i => c i, fun i => (c i).2, fun y hy => ?_⟩
  have h1 : (Submodule.Quotient.mk ⟨y, hy⟩ : C ⧸ (Ideal.span {(m : R)} • (⊤ : Submodule R C))) ∈
      Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h1
  have h2 : (Submodule.Quotient.mk (∑ i, r i • c i) : C ⧸ (Ideal.span {(m : R)} • (⊤ : Submodule R C))) =
      Submodule.Quotient.mk ⟨y, hy⟩ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hr, ← Submodule.mkQ_apply, map_sum]
    simp [hc]
  have h3 := (Submodule.Quotient.eq _).1 h2.symm
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨d, -, hd⟩ := h3
  refine ⟨r, d, d.2, ?_⟩
  have h4 := congrArg Subtype.val hd
  simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_sum, Nat.cast_smul_eq_nsmul] at h4
  rw [eq_sub_iff_add_eq] at h4
  rw [← h4, add_comm]
  simp

theorem fibre_count {R V W : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (f : V →ₗ[R] W) (L M : Submodule R V) (C : Submodule R W) (m s : ℕ)
    (hm : M.toAddSubgroup.relIndex (L ⊓ LinearMap.ker f).toAddSubgroup = m) (hm0 : m ≠ 0)
    (c : Fin s → W) (hc : ∀ i, c i ∈ C)
    (hgen : ∀ y ∈ C, ∃ (r : Fin s → R) (d : W), d ∈ C ∧ y = ∑ i, r i • c i + m • d) :
    {La : Submodule R V | La ≤ L ∧ La.map f = C ∧ La ⊓ LinearMap.ker f = M}.encard ≤ (m ^ s : ℕ) := by
  set S := {La : Submodule R V | La ≤ L ∧ La.map f = C ∧ La ⊓ LinearMap.ker f = M} with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨L₁, hL₁⟩
  · simp [h0]
  have hlift : ∀ La : S, ∀ y ∈ C, ∃ a ∈ La.1, f a = y := fun La y hy => by
    have : y ∈ La.1.map f := La.2.2.1.symm ▸ hy
    exact this
  choose a ha hfa using fun (La : S) (i : Fin s) => hlift La (c i) (hc i)
  set K₀ := (L ⊓ LinearMap.ker f).toAddSubgroup with hK₀
  have hmem : ∀ (La : S) i, a La i - a ⟨L₁, hL₁⟩ i ∈ K₀ := fun La i =>
    ⟨sub_mem (La.2.1 (ha La i)) (hL₁.1 (ha ⟨L₁, hL₁⟩ i)), by simp [hfa]⟩
  let Φ : S → (Fin s → K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀) := fun La i => QuotientAddGroup.mk ⟨_, hmem La i⟩
  have hle : ∀ La La' : S, Φ La = Φ La' → La.1 ≤ La'.1 := by
    intro La La' h y hy
    have hML : M ≤ La'.1 := La'.2.2.2 ▸ inf_le_left
    have h1 : ∀ i, a La i ∈ La'.1 := fun i => by
      have h2 := QuotientAddGroup.eq.1 (congrFun h i)
      rw [AddSubgroup.mem_addSubgroupOf] at h2
      have h3 : -(a La i - a ⟨L₁, hL₁⟩ i) + (a La' i - a ⟨L₁, hL₁⟩ i) ∈ La'.1 := hML h2
      have h4 := sub_mem (ha La' i) h3
      convert h4 using 1
      abel
    have hfy : f y ∈ C := La.2.2.1 ▸ Submodule.mem_map_of_mem hy
    obtain ⟨r, d, hd, hyd⟩ := hgen _ hfy
    obtain ⟨b, hb, hfb⟩ := hlift La d hd
    obtain ⟨b', hb', hfb'⟩ := hlift La' d hd
    have h5 : y - (∑ i, r i • a La i + m • b) ∈ M := by
      rw [← La.2.2.2]
      refine ⟨sub_mem hy (add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ha La i))
        (nsmul_mem hb _)), ?_⟩
      simp [hfa, hfb, ← hyd]
    have h6 : m • (b - b') ∈ M := by
      have h7 : b - b' ∈ K₀ := ⟨sub_mem (La.2.1 hb) (La'.2.1 hb'), by simp [hfb, hfb']⟩
      have h8 := AddSubgroup.nsmul_index_mem (M.toAddSubgroup.addSubgroupOf K₀) ⟨_, h7⟩
      rw [AddSubgroup.mem_addSubgroupOf] at h8
      have h9 : (M.toAddSubgroup.addSubgroupOf K₀).index = m := hm
      rw [h9] at h8
      exact h8
    have h10 := add_mem (hML h5) (add_mem (Submodule.sum_mem _ fun i (_ : i ∈ Finset.univ) =>
      Submodule.smul_mem _ (r i) (h1 i)) (add_mem (hML h6) (nsmul_mem hb' m)))
    convert h10 using 1
    rw [smul_sub]
    abel
  have hΦ : Function.Injective Φ := fun La La' h => Subtype.ext (le_antisymm (hle _ _ h) (hle _ _ h.symm))
  have hcard : Nat.card (K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀) = m := hm
  have : Finite (K₀ ⧸ M.toAddSubgroup.addSubgroupOf K₀) := Nat.finite_of_card_ne_zero (hcard ▸ hm0)
  have hfin : Finite S := Finite.of_injective Φ hΦ
  have h11 := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_fun, hcard, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at h11
  rw [← (Set.toFinite S).cast_ncard_eq]
  exact_mod_cast h11

theorem relIndex_eq_mul {V W : Type} [AddCommGroup V] [AddCommGroup W] (f : V →+ W) (A L : AddSubgroup V)
    (h : A ≤ L) : A.relIndex L = (A ⊓ f.ker).relIndex (L ⊓ f.ker) * (A.map f).relIndex (L.map f) := by
  have h1 := AddSubgroup.relIndex_mul_relIndex A (A ⊔ (L ⊓ f.ker)) L le_sup_left (sup_le h inf_le_left)
  rw [← h1, AddSubgroup.relIndex_sup_left, AddSubgroup.relIndex_map_map]
  congr 1
  · rw [← AddSubgroup.inf_relIndex_right A, ← AddSubgroup.inf_relIndex_right (A ⊓ f.ker), inf_assoc,
      inf_eq_right.2 (inf_le_right : L ⊓ f.ker ≤ f.ker)]
  · have h2 : L ⊔ f.ker = L ⊔ (A ⊔ f.ker) := by rw [← sup_assoc, sup_eq_left.2 h]
    rw [h2, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right (A ⊔ f.ker), sup_inf_assoc_of_le _ h,
      inf_comm]

theorem encard_le_mul {α β : Type} (g : α → β) (S : Set α) (T : Set β) (hT : T.Finite) (k : ℕ)
    (hg : ∀ a ∈ S, g a ∈ T) (hk : ∀ b ∈ T, {a | a ∈ S ∧ g a = b}.encard ≤ k) :
    S.encard ≤ (T.ncard * k : ℕ) := by
  have hfin : S.Finite := by
    refine (hT.biUnion fun b hb => Set.finite_of_encard_le_coe (hk b hb)).subset fun a ha => ?_
    exact Set.mem_biUnion (hg a ha) ⟨ha, rfl⟩
  rw [← hfin.cast_ncard_eq, Nat.cast_le, Set.ncard_eq_toFinset_card _ hfin, Set.ncard_eq_toFinset_card _ hT,
    mul_comm]
  refine Finset.card_le_mul_card_image_of_maps_to (f := g) (fun a ha => by simpa using hg a (by simpa using ha)) k
    fun b hb => ?_
  have h1 := hk b (by simpa using hb)
  have h2 : {a | a ∈ S ∧ g a = b} = ((hfin.toFinset.filter fun a => g a = b : Finset α) : Set α) := by
    ext a; simp
  rw [h2, Set.encard_coe_eq_coe_finsetCard] at h1
  exact_mod_cast h1

theorem proj_rank {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (C : Submodule (𝓞 K) W) (hC : C.FG) :
    Module.Finite (𝓞 K) C ∧ Module.Projective (𝓞 K) C ∧ Module.finrank (𝓞 K) C ≤ Module.finrank K W := by
  have : Module.Finite (𝓞 K) C := Module.Finite.iff_fg.2 hC
  have : Module.IsTorsionFree (𝓞 K) W := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K W
  have : Module.Flat (𝓞 K) C := inferInstance
  have : Module.FinitePresentation (𝓞 K) C := Module.finitePresentation_of_finite _ _
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation,
    (GlobalTheory.CongIndex.finrank_le_finrank_span C).trans (Submodule.finrank_le _)⟩

theorem sub_count {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (C : Submodule (𝓞 K) W) (hC : C.FG) (j : ℕ) (hj : 1 ≤ j) :
    {N : Submodule (𝓞 K) W | N ≤ C ∧ N.toAddSubgroup.relIndex C.toAddSubgroup = j}.Finite ∧
    (({N : Submodule (𝓞 K) W | N ≤ C ∧ N.toAddSubgroup.relIndex C.toAddSubgroup = j}.ncard : ℕ) : ℝ) ≤
      (j : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (j : ℝ) ^ Module.finrank K W := by
  obtain ⟨h1, h2, h3⟩ := proj_rank C hC
  obtain ⟨h4, h5⟩ := Formalism.SLP.Final.submoduleIndexCountO K C j hj
  have h6 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) j Module.finrank_pos hj
  have hsub : {N : Submodule (𝓞 K) W | N ≤ C ∧ N.toAddSubgroup.relIndex C.toAddSubgroup = j} ⊆
      (fun N : Submodule (𝓞 K) C => N.map C.subtype) '' {N | N.toAddSubgroup.index = j} := by
    rintro N ⟨hN, hNj⟩
    refine ⟨N.comap C.subtype, hNj, ?_⟩
    simp only [Submodule.map_comap_subtype]
    exact inf_eq_right.2 hN
  refine ⟨(h4.image _).subset hsub, ?_⟩
  have h7 := ((Set.ncard_le_ncard hsub (h4.image _)).trans (Set.ncard_image_le h4)).trans h5
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  calc _ ≤ ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList j).length * (j : ℝ) ^ Module.finrank (𝓞 K) C := by
        exact_mod_cast h7
    _ ≤ _ := mul_le_mul h6 (pow_le_pow_right₀ hj1 h3) (by positivity) (by positivity)

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L₀ M : Submodule (𝓞 K) V) (U : Submodule K V) (x : ℕ), Submodule.IsLattice K L₀ → 1 ≤ x → ((({La : Submodule (𝓞 K) V | La ≤ L₀ ∧ idx L₀ La = x ∧ La ⊓ rs (𝓞 K) U = M}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (2 * (((Module.finrank K V) - Module.finrank K U : ℕ) : ℝ) + cf K)) := by
  intro K V _ _ _ _ _ _ _ _ L₀ M U x hL hx
  set S := {La : Submodule (𝓞 K) V | La ≤ L₀ ∧ idx L₀ La = x ∧ La ⊓ rs (𝓞 K) U = M} with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨L₁, hL₁⟩
  · simp [h0]
  let f : V →ₗ[𝓞 K] (V ⧸ U) := U.mkQ.restrictScalars (𝓞 K)
  have hker : LinearMap.ker f = rs (𝓞 K) U := by
    ext v
    simp [f]
  have hker' : f.toAddMonoidHom.ker = (LinearMap.ker f).toAddSubgroup := rfl
  set m := M.toAddSubgroup.relIndex (L₀ ⊓ LinearMap.ker f).toAddSubgroup with hm
  have hidx : ∀ La ∈ S, x = m * (La.map f).toAddSubgroup.relIndex (L₀.map f).toAddSubgroup := by
    intro La hLa
    have h1 := relIndex_eq_mul f.toAddMonoidHom La.toAddSubgroup L₀.toAddSubgroup hLa.1
    have h2 : La.toAddSubgroup.relIndex L₀.toAddSubgroup = x := hLa.2.1
    have h3 : La ⊓ LinearMap.ker f = M := hker ▸ hLa.2.2
    rw [← h2, h1, hm, ← h3]
    rfl
  set j := (L₁.map f).toAddSubgroup.relIndex (L₀.map f).toAddSubgroup with hj
  have hxj : x = m * j := hidx L₁ hL₁
  have hm0 : m ≠ 0 := fun h => by rw [h] at hxj; omega
  have hj0 : j ≠ 0 := fun h => by rw [h] at hxj; omega
  have hC : (L₀.map f).FG := (Submodule.IsLattice.fg (self := hL)).map f
  have hs : Module.finrank K (V ⧸ U) = Module.finrank K V - Module.finrank K U := by
    have := U.finrank_quotient_add_finrank
    omega
  set s := Module.finrank K V - Module.finrank K U with hsdef
  obtain ⟨hT, hTc⟩ := sub_count (L₀.map f) hC j (Nat.one_le_iff_ne_zero.2 hj0)
  rw [hs] at hTc
  have hfinq : Finite (𝓞 K ⧸ Ideal.span {(m : 𝓞 K)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hm0)
  have hcount := encard_le_mul (fun La : Submodule (𝓞 K) V => La.map f) S _ hT (m ^ s)
    (fun La hLa => ⟨Submodule.map_mono hLa.1,
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) ((hidx La hLa).symm.trans hxj)⟩)
    (fun N hN => by
      have hCf : Module.Finite (𝓞 K) (L₀.map f) := Module.Finite.iff_fg.2 hC
      have hNfg : N.FG := Submodule.FG.of_le_of_isNoetherian hN.1
      obtain ⟨h1, h2, h3⟩ := proj_rank N hNfg
      obtain ⟨c, hc, hgen⟩ := exists_gen_mod N m
      have h4 := fibre_count f L₀ M N m _ hm.symm hm0 c hc hgen
      refine le_trans (Set.encard_le_encard ?_) (h4.trans ?_)
      · rintro La ⟨hLa, hN'⟩
        exact ⟨hLa.1, hN', hker ▸ hLa.2.2⟩
      · exact_mod_cast Nat.pow_le_pow_right (Nat.pos_of_ne_zero hm0) (hs ▸ h3))
  refine le_trans (ENat.toENNReal_le.2 hcount) ?_
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hjx : (j : ℝ) ≤ x := by exact_mod_cast hxj ▸ Nat.le_mul_of_pos_left j (Nat.pos_of_ne_zero hm0)
  have hlog : 0 ≤ Real.logb 2 (Module.finrank ℚ K) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K))
  have hxr : (x : ℝ) = m * j := by exact_mod_cast hxj
  push_cast
  calc _ ≤ ((j : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (j : ℝ) ^ s) * (m : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right hTc (by positivity)
    _ = (j : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ s := by rw [hxr, mul_pow]; ring
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hjx hlog) (by positivity)
    _ = (x : ℝ) ^ (Real.logb 2 (Module.finrank ℚ K) + (s : ℝ)) := by
        rw [Real.rpow_add (by positivity), Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by
        have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
        unfold cf
        linarith)

end GlobalTheory.TraceCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesIndexFixedTraceLeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_sublattices_index_fixed_trace_le : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L₀ M : Submodule (𝓞 K) V) (U : Submodule K V) (x : ℕ), Submodule.IsLattice K L₀ → 1 ≤ x → ((({La : Submodule (𝓞 K) V | La ≤ L₀ ∧ idx L₀ La = x ∧ La ⊓ rs (𝓞 K) U = M}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (2 * (((Module.finrank K V) - Module.finrank K U : ℕ) : ℝ) + cf K)) := by
  first | exact @GlobalTheory.TraceCount.main | exact GlobalTheory.TraceCount.main | (intros; apply GlobalTheory.TraceCount.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedLatticeInfEqAndPairingOfIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedLatticeInfEqAndPairingOfIsometry
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem trip_fixLat_inf_eq_and_pairing : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), ∀ p ∈ Trip H g L₀ j x x', fixLat p.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) = fixLat p.2.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) ∧ ∀ y ∈ fixLat p.1.2, ∀ y' ∈ fixLat p.2.1.2, ∃ t : 𝓞 K, H.B y (y' - p.2.2 y') = (g : K) * (t : K) := by
  intro K V _ _ _ _ _ _ _ _ H _ _ L₀ g j D₀ _ _ _ _ x x' p hp
  obtain ⟨h1, -, -, -, h5⟩ := hp
  have hmem : ∀ (Γ : Submodule (𝓞 K) (V × V)) (y : V), y ∈ fixLat Γ ↔ (y, y) ∈ Γ := fun _ _ => Iff.rfl
  refine ⟨?_, ?_⟩
  · ext y
    have hf : y ∈ rs (𝓞 K) (fixSp p.2.2) ↔ p.2.2 y = y := by
      simp [fixSp, sub_eq_zero]
    rw [Submodule.mem_inf, Submodule.mem_inf, hmem, hmem, hf, h5]
    refine and_congr_left fun h => ?_
    rw [h]
  · intro y hy y' hy'
    rw [hmem] at hy hy'
    rw [h5] at hy'
    obtain ⟨t, ht⟩ := h1.2.2.1.2.2.2.2.2.2 _ hy _ hy'
    refine ⟨-t, ?_⟩
    simp only [map_mul, map_natCast] at ht
    rw [map_sub]
    have : ((-t : 𝓞 K) : K) = -(algebraMap (𝓞 K) K t) := map_neg (algebraMap (𝓞 K) K) t
    rw [this]
    linear_combination -ht

end GlobalTheory.DegCnt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedLatticeInfEqAndPairingOfIsometryStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedLattice_inf_eq_and_pairing_of_isometry : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), ∀ p ∈ Trip H g L₀ j x x', fixLat p.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) = fixLat p.2.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) ∧ ∀ y ∈ fixLat p.1.2, ∀ y' ∈ fixLat p.2.1.2, ∃ t : 𝓞 K, H.B y (y' - p.2.2 y') = (g : K) * (t : K) := by
  first | exact @GlobalTheory.DegCnt.trip_fixLat_inf_eq_and_pairing | exact GlobalTheory.DegCnt.trip_fixLat_inf_eq_and_pairing | (intros; apply GlobalTheory.DegCnt.trip_fixLat_inf_eq_and_pairing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountIsometryPairsWithGivenFixedSpace
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.FixedSpaceCount

theorem encard_le_mul {α β : Type*} (S : Set α) (T : Set β) (f : α → β) (a b : ℝ≥0∞)
    (hm : ∀ s ∈ S, f s ∈ T) (hT : ((T.encard : ℕ∞) : ℝ≥0∞) ≤ a)
    (hb : ∀ t ∈ T, ((({s ∈ S | f s = t}).encard : ℕ∞) : ℝ≥0∞) ≤ b) :
    ((S.encard : ℕ∞) : ℝ≥0∞) ≤ a * b := by
  have hS : S = ⋃ t : T, {s ∈ S | f s = t} := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨⟨f s, hm s h⟩, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  calc ((S.encard : ℕ∞) : ℝ≥0∞) = ∑' _ : (⋃ t : T, {s ∈ S | f s = t} : Set α), (1 : ℝ≥0∞) := by
        rw [← hS, ENNReal.tsum_set_one]
    _ ≤ ∑' t : T, ∑' _ : ({s ∈ S | f s = t} : Set α), (1 : ℝ≥0∞) :=
        ENNReal.tsum_iUnion_le_tsum (fun _ => 1) _
    _ ≤ ∑' _ : T, b := ENNReal.tsum_le_tsum fun t => by
        rw [ENNReal.tsum_set_one]; exact hb t t.2
    _ = ((T.encard : ℕ∞) : ℝ≥0∞) * b := ENNReal.tsum_set_const _ _
    _ ≤ a * b := by gcongr

section

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


omit [NumberField K] in
theorem finrank_le [NumberField K] (N : Submodule (𝓞 K) V) : Module.finrank (𝓞 K) N ≤ Module.finrank K V := by
  apply Module.finrank_le_of_rank_le
  rw [Module.finrank_eq_rank, IsLocalization.rank_eq K (𝓞 K)⁰ le_rfl]
  exact Submodule.rank_le N

theorem cf_nonneg (K : Type) [Field K] [NumberField K] : 0 ≤ cf K := by
  have h : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have := Real.logb_nonneg (b := 2) one_lt_two h
  unfold cf
  linarith

theorem sub_count [_root_.NumberField.IsTotallyComplex K] (N : Submodule (𝓞 K) V) (hN : N.FG) (y : ℕ) (hy : 1 ≤ y) :
    ((({M : Submodule (𝓞 K) V | M ≤ N ∧ GlobalTheory.Mass.idxN N M = y}).encard : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal ((y : ℝ) ^ ((Module.finrank K V : ℝ) + cf K)) := by
  haveI : Module.Finite (𝓞 K) N := Module.Finite.iff_fg.2 hN
  haveI : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  haveI : Module.Projective (𝓞 K) N := by
    haveI : Module.FinitePresentation (𝓞 K) N := Module.finitePresentation_of_finite _ _
    exact Module.Flat.projective_of_finitePresentation
  have hf : Module.finrank ℚ K = 2 * InfinitePlace.nrComplexPlaces K := IsTotallyComplex.finrank K
  obtain ⟨hfin, hc⟩ := Formalism.HermitianLatticeCounting.P.sublattice_count_alt K N _ y hf hy
  have h1 : ({M : Submodule (𝓞 K) V | M ≤ N ∧ GlobalTheory.Mass.idxN N M = y}).encard ≤
      ({M : Submodule (𝓞 K) N | M.toAddSubgroup.index = y}).encard := by
    refine Set.encard_le_encard_of_injOn (f := fun M => M.comap N.subtype) ?_ ?_
    · rintro M ⟨-, h⟩
      exact h
    · rintro M ⟨h, -⟩ M' ⟨h', -⟩ e
      have := congrArg (Submodule.map N.subtype) e
      simpa [Submodule.map_comap_subtype, inf_eq_right.2 h, inf_eq_right.2 h'] using this
  refine (ENat.toENNReal_le.2 h1).trans ?_
  rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal (hc.trans ?_)
  have e : (1 + Real.logb 2 (2 * (InfinitePlace.nrComplexPlaces K : ℝ))) = cf K := by
    unfold cf; rw [hf]; push_cast; rfl
  rw [e]
  refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hy) ?_
  have : (Module.finrank (𝓞 K) N : ℝ) ≤ Module.finrank K V := by exact_mod_cast finrank_le N
  linarith


omit [FiniteDimensional K V] in
theorem isLattice_of_idx {L M : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) (hM : M ≤ L)
    (h : idx L M ≠ 0) : Submodule.IsFullLattice K M := by
  haveI : Submodule.IsFullLattice K L := hL
  haveI : Submodule.IsLattice K M := Submodule.IsLattice.mono K hM
  refine ⟨?_⟩
  rw [← Submodule.IsFullLattice.span_eq_top (A := K) (M := L)]
  refine le_antisymm (Submodule.span_mono hM) ?_
  rw [Submodule.span_le]
  intro m hm
  have hn : (M.toAddSubgroup.relIndex L.toAddSubgroup) • m ∈ M :=
    AddSubgroup.nsmul_relIndex_mem M.toAddSubgroup (K := L.toAddSubgroup) hm
  have hnK : ((M.toAddSubgroup.relIndex L.toAddSubgroup : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr h
  have hm' : m = ((M.toAddSubgroup.relIndex L.toAddSubgroup : ℕ) : K)⁻¹ •
      (M.toAddSubgroup.relIndex L.toAddSubgroup • m) := by
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hnK, one_smul]
  rw [SetLike.mem_coe, hm']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hn)


omit [FiniteDimensional K V] [NumberField K] in
theorem idx_latIn_le (U : Submodule K V) (L M : Submodule (𝓞 K) V) (h : idx L M ≠ 0) :
    GlobalTheory.Mass.idxN (GlobalTheory.Mass.latIn U L) (GlobalTheory.Mass.latIn U M) ≤ idx L M := by
  have e : GlobalTheory.Mass.idxN (GlobalTheory.Mass.latIn U L) (GlobalTheory.Mass.latIn U M) =
      (M.toAddSubgroup.comap U.subtype.toAddMonoidHom).relIndex
        (L.toAddSubgroup.comap U.subtype.toAddMonoidHom) := rfl
  rw [e, AddSubgroup.relIndex_comap]
  exact AddSubgroup.relIndex_le_of_le_right (AddSubgroup.map_comap_le _ _) h


omit [FiniteDimensional K V] [NumberField K] in
theorem inf_eq_map (U : Submodule K V) (M : Submodule (𝓞 K) V) :
    M ⊓ rs (𝓞 K) U = (GlobalTheory.Mass.latIn U M).map (U.subtype.restrictScalars (𝓞 K)) := by
  ext v
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨v, h2⟩, h1, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw, w.2⟩

variable [StarRing K]


omit [FiniteDimensional K V] in
theorem hRes_nondeg (h : V →ₗ⋆[K] V →ₗ[K] K) (hP : GlobalTheory.Mass.PD h) (U : Submodule K V) :
    (GlobalTheory.Mass.hRes h U).Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have key : ∀ x : U, GlobalTheory.Mass.hRes h U x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have := hP τ x (fun e => hne (Subtype.ext e))
    have e : h x x = 0 := hx
    rw [e] at this
    simp at this
  exact ⟨fun x hx => key x (hx x), fun x hx => key x (hx x)⟩


omit [FiniteDimensional K V] in
theorem fixLat_le {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {g : ℕ} {L₀ : Submodule (𝓞 K) V} {j x : ℕ}
    {d : Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)} (hd : IsDat H g L₀ j x d) : fixLat d.2 ≤ L₀ :=
  fun _ hv => (hd.2.2.1.1 hv).2

theorem disc_trace (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hP : GlobalTheory.Mass.PD H.B.flip)
    {L M : Submodule (𝓞 K) V} (hL : GlobalTheory.Mass.IsIntLat H.B.flip L) (hM : M ≤ L) (h : idx L M ≠ 0)
    (U : Submodule K V) :
    GlobalTheory.Mass.idxN (GlobalTheory.Mass.latIn U L) (GlobalTheory.Mass.latIn U M) ≠ 0 ∧
    GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip U) (GlobalTheory.Mass.latIn U M) =
      GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip U) (GlobalTheory.Mass.latIn U L) *
        GlobalTheory.Mass.idxN (GlobalTheory.Mass.latIn U L) (GlobalTheory.Mass.latIn U M) ^ 2 := by
  have hM' : GlobalTheory.Mass.IsIntLat H.B.flip M :=
    ⟨isLattice_of_idx hL.1 hM h, fun x hx y hy => hL.2 x (hM hx) y (hM hy)⟩
  have hs : (GlobalTheory.Mass.hRes H.B.flip U).IsSymm := ⟨fun x y => H.herm y x⟩
  exact (GlobalTheory.Mass.DiscOrder.main K U _ hK hs (hRes_nondeg _ hP U) _
    (GlobalTheory.Mass.PrimMean.isIntLat_latIn _ hM' U)).2.2.1 _ (GlobalTheory.Mass.PrimMean.isIntLat_latIn _ hL U)
    (Submodule.comap_mono hM)

theorem dat_count (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hP : GlobalTheory.Mass.PD H.B.flip)
    (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ) (hL : GlobalTheory.Mass.IsIntLat H.B.flip L₀)
    (hD : GlobalTheory.Mass.discN H.B.flip L₀ = D₀) (hG : GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1) (hg : 2 ≤ g)
    (x : ℕ) (hx : 1 ≤ x) (U : Submodule K V) (M : Submodule (𝓞 K) V) :
    ((({d | IsDat H g L₀ j x d ∧ fixLat d.2 ⊓ rs (𝓞 K) U = M}).encard : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal ((x : ℝ) ^ (2 * (((Module.finrank K V) - Module.finrank K U : ℕ) : ℝ) + cf K)) *
        ((x : ℝ≥0∞) * D₀) ^ (3 * (2 * j + 1)) := by
  haveI : IsTotallyComplex K := hK.1
  refine encard_le_mul _ _ (fun d => fixLat d.2) _ _ ?_ (GlobalTheory.T.encard_sublattices_index_fixed_trace_le K V L₀ M U x hL.1.toIsLattice hx) ?_
  · rintro d ⟨hd, hM⟩
    exact ⟨fixLat_le hd, hd.2.2.2.1, hM⟩
  · intro La _
    refine le_trans (ENat.toENNReal_le.2 (Set.encard_le_encard ?_))
      (GlobalTheory.T.card_embeddedData_with_given_fixedLattice K V H hK hP L₀ g j D₀ hL hD hG hg La x)
    rintro d ⟨⟨hd, -⟩, h⟩
    exact ⟨hd, h⟩

end

theorem pow_bound (A c : ℝ) (n y x x' u k : ℕ) (hn : 1 ≤ n) (hy : 1 ≤ y) (hx : y ≤ x) (hx' : 1 ≤ x')
    (hu : u ≤ k) (hc : 0 ≤ c) (hA : (n : ℝ) * (y : ℝ) ^ 2 ≤ A) :
    (y : ℝ) ^ ((u : ℝ) + c) ≤ (A / n) ^ ((k : ℝ) / 2) * ((x : ℝ) * x') ^ c := by
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hn1 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx1 : (y : ℝ) ≤ x := by exact_mod_cast hx
  have hx2 : (1 : ℝ) ≤ x' := by exact_mod_cast hx'
  rw [Real.rpow_add (by linarith)]
  have h1 : (y : ℝ) ^ (u : ℝ) ≤ (A / n) ^ ((k : ℝ) / 2) := by
    calc (y : ℝ) ^ (u : ℝ) ≤ (y : ℝ) ^ (k : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hy1 (by exact_mod_cast hu)
      _ = ((y : ℝ) ^ 2) ^ ((k : ℝ) / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
          congr 1
          push_cast
          ring
      _ ≤ (A / n) ^ ((k : ℝ) / 2) := by
          refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          rw [le_div_iff₀ hn1]
          linarith
  have h2 : (y : ℝ) ^ c ≤ ((x : ℝ) * x') ^ c :=
    Real.rpow_le_rpow (by linarith) (by nlinarith) hc
  exact mul_le_mul h1 h2 (by positivity) ((by positivity : (0 : ℝ) ≤ (y : ℝ) ^ (u : ℝ)).trans h1)

theorem prod_bound (B c : ℝ) (x x' D s e C : ℕ) (hB : 0 ≤ B) (hx : 1 ≤ x) (hx' : 1 ≤ x') :
    (x : ℝ≥0∞) * ENNReal.ofReal (B * ((x : ℝ) * x') ^ c) *
      (ENNReal.ofReal ((x : ℝ) ^ (2 * (s : ℝ) + c)) * ((x : ℝ≥0∞) * D) ^ e *
        (ENNReal.ofReal ((x' : ℝ) ^ (2 * (s : ℝ) + c)) * ((x' : ℝ≥0∞) * D) ^ e * (C : ℝ≥0∞) ^ C)) ≤
    ENNReal.ofReal (B * ((x : ℝ) * x') ^ (2 * (s : ℝ) + 2 * c + 1) * ((x : ℝ) * x' * (D : ℝ) ^ 2) ^ e *
      (C : ℝ) ^ C) := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx2 : (1 : ℝ) ≤ x' := by exact_mod_cast hx'
  have e1 : ∀ a : ℕ, ((a : ℝ≥0∞) * D) ^ e = ENNReal.ofReal (((a : ℝ) * D) ^ e) := fun a => by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]
  have e2 : (C : ℝ≥0∞) ^ C = ENNReal.ofReal ((C : ℝ) ^ C) := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  rw [e1, e1, e2, ← ENNReal.ofReal_natCast x, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e3 : ((x : ℝ) * x') ^ (2 * (s : ℝ) + 2 * c + 1) =
      (x : ℝ) ^ (2 * (s : ℝ) + c) * (x' : ℝ) ^ (2 * (s : ℝ) + c) * ((x : ℝ) * x') ^ c * ((x : ℝ) * x') := by
    rw [← Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_add (by positivity),
      ← Real.rpow_add_one (by positivity)]
    congr 1
    ring
  have e4 : ((x : ℝ) * x' * (D : ℝ) ^ 2) ^ e = ((x : ℝ) * D) ^ e * ((x' : ℝ) * D) ^ e := by
    rw [← mul_pow]; congr 1; ring
  rw [e3, e4]
  have h : (x : ℝ) ≤ x * x' := by nlinarith
  calc _ = (B * ((x : ℝ) ^ (2 * (s : ℝ) + c) * (x' : ℝ) ^ (2 * (s : ℝ) + c) * ((x : ℝ) * x') ^ c) *
        (((x : ℝ) * D) ^ e * ((x' : ℝ) * D) ^ e) * (C : ℝ) ^ C) * x := by ring
    _ ≤ (B * ((x : ℝ) ^ (2 * (s : ℝ) + c) * (x' : ℝ) ^ (2 * (s : ℝ) + c) * ((x : ℝ) * x') ^ c) *
        (((x : ℝ) * D) ^ e * ((x' : ℝ) * D) ^ e) * (C : ℝ) ^ C) * (x * x') := by gcongr
    _ = _ := by ring

theorem main : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' s n : ℕ) (U : Submodule K V), 1 ≤ x → 1 ≤ x' → 1 ≤ n → Module.finrank K U + s = (Module.finrank K V) → GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip U) (GlobalTheory.Mass.latIn U L₀) = n → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = U}).encard : ℕ∞) : ℝ≥0∞) ≤ if (n : ℝ) ≤ (D₀ : ℝ) * x * x' then ENNReal.ofReal (((2 / (g : ℝ)) ^ (2 * s * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x' / n) ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x') ^ (2 * (s : ℝ) + 2 * cf K + 1) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (3 * (2 * j + 1)) * ((4 * s * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * s * (Formalism.HermitianLatticesTheory.fDeg K))) else 0 := by
  intro hM K V _ _ _ _ _ _ _ _ H hK hP L₀ g j D₀ hL hD hG hg x x' s n U hx hx' hn hs hdisc
  haveI : IsTotallyComplex K := hK.1
  have hsub : Module.finrank K V - Module.finrank K U = s := by omega
  set A : ℝ := (2 / (g : ℝ)) ^ (2 * s * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x' with hA
  set N := GlobalTheory.Mass.latIn U L₀ with hN
  have key : ∀ p ∈ {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = U},
      GlobalTheory.Mass.latIn U (fixLat p.1.2) ≤ N ∧ 1 ≤ GlobalTheory.Mass.idxN N (GlobalTheory.Mass.latIn U (fixLat p.1.2)) ∧
      GlobalTheory.Mass.idxN N (GlobalTheory.Mass.latIn U (fixLat p.1.2)) ≤ x ∧
      (n : ℝ) * (GlobalTheory.Mass.idxN N (GlobalTheory.Mass.latIn U (fixLat p.1.2)) : ℝ) ^ 2 ≤ A := by
    rintro p ⟨hp, hU⟩
    have hi : idx L₀ (fixLat p.1.2) = x := hp.1.2.2.2.1
    have hi0 : idx L₀ (fixLat p.1.2) ≠ 0 := by omega
    obtain ⟨h1, h2⟩ := disc_trace H hK hP hL (fixLat_le hp.1) hi0 U
    have h3 := GlobalTheory.T.discriminantOrder_common_fixedLattice_embeddedData K V H hK hP L₀ g j D₀ hL hD hG hg x x' hx hx' p hp
    rw [hU, hsub, h2, hdisc] at h3
    refine ⟨Submodule.comap_mono (fixLat_le hp.1), Nat.one_le_iff_ne_zero.2 h1,
      hi ▸ idx_latIn_le U _ _ hi0, ?_⟩
    push_cast at h3
    exact h3
  split_ifs with hcase
  · have hA0 : 0 ≤ A := by positivity
    refine le_trans ?_ (prod_bound ((A / n) ^ ((Module.finrank K V : ℝ) / 2)) (cf K) x x' D₀ s (3 * (2 * j + 1))
      (4 * s * Formalism.HermitianLatticesTheory.fDeg K) (by positivity) hx hx')
    refine encard_le_mul _ {M : Submodule (𝓞 K) U | M ≤ N ∧ 1 ≤ GlobalTheory.Mass.idxN N M ∧ GlobalTheory.Mass.idxN N M ≤ x ∧
      (n : ℝ) * (GlobalTheory.Mass.idxN N M : ℝ) ^ 2 ≤ A}
      (fun p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) =>
        GlobalTheory.Mass.latIn U (fixLat p.1.2)) _ _ key ?_ ?_
    · refine encard_le_mul _ {y : ℕ | 1 ≤ y ∧ y ≤ x ∧ (n : ℝ) * (y : ℝ) ^ 2 ≤ A} (GlobalTheory.Mass.idxN N) _ _
        (fun M h => h.2) ?_ ?_
      · have h1 : {y : ℕ | 1 ≤ y ∧ y ≤ x ∧ (n : ℝ) * (y : ℝ) ^ 2 ≤ A} ⊆ (Finset.Icc 1 x : Finset ℕ) := by
          rintro y ⟨a, b, -⟩
          simp [a, b]
        refine (ENat.toENNReal_le.2 (Set.encard_le_encard h1)).trans ?_
        rw [Set.encard_coe_eq_coe_finsetCard]
        simp
      · rintro y ⟨a, b, c⟩
        have hfg : N.FG := (GlobalTheory.Mass.PrimMean.isIntLat_latIn _ hL U).1.fg
        refine le_trans (ENat.toENNReal_le.2 (Set.encard_le_encard ?_)) ((sub_count N hfg y a).trans
          (ENNReal.ofReal_le_ofReal (pow_bound A (cf K) n y x x' _ _ hn a b hx' (by omega) (cf_nonneg K) c)))
        rintro M ⟨h, e⟩
        exact ⟨h.1, e⟩
    · intro M _
      have c1 := dat_count H hK hP L₀ g j D₀ hL hD hG hg x hx U (M.map (U.subtype.restrictScalars (𝓞 K)))
      have c2 := dat_count H hK hP L₀ g j D₀ hL hD hG hg x' hx' U (M.map (U.subtype.restrictScalars (𝓞 K)))
      rw [hsub] at c1 c2
      refine encard_le_mul _ _ (fun p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) => p.1) _ _ ?_ c1 ?_
      · rintro p ⟨⟨hp, -⟩, e⟩
        exact ⟨hp.1, by rw [inf_eq_map, e]⟩
      intro d hd
      refine encard_le_mul _ _ (fun p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) => p.2.1) _ _ ?_ c2 ?_
      · rintro p ⟨⟨⟨hp, hU⟩, e⟩, -⟩
        have h42 := (GlobalTheory.T.fixedLattice_inf_eq_and_pairing_of_isometry K V H hK hP L₀ g j D₀ hL hD hG hg x x' p hp).1
        rw [hU] at h42
        exact ⟨hp.2.1, by rw [← h42, inf_eq_map, e]⟩
      intro d' hd'
      have c3 := GlobalTheory.T.card_isometries_fixing_subspace_definite_lattices_le hM K V H hK hP U d'.1 d.1 hd'.1.1.1 hd.1.1.1
      rw [hsub] at c3
      refine le_trans (ENat.toENNReal_le.2 ?_) c3
      refine Set.encard_le_encard_of_injOn (f := fun p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) => p.2.2) ?_ ?_
      · rintro p ⟨⟨⟨⟨hp, hU⟩, -⟩, e1⟩, e2⟩
        refine ⟨hp.2.2.1, by rw [← e1, ← e2]; exact hp.2.2.2.1, fun y hy => ?_⟩
        rw [← hU] at hy
        have : p.2.2 y - y = 0 := hy
        exact sub_eq_zero.1 this
      · rintro p ⟨⟨-, e1⟩, e2⟩ q ⟨⟨-, f1⟩, f2⟩ e
        exact Prod.ext (e1.trans f1.symm) (Prod.ext (e2.trans f2.symm) e)
  · have hempty : {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = U} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun p hp => hcase ?_
      obtain ⟨-, a, -, c⟩ := key p hp
      have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
      have h1 : (2 / (g : ℝ)) ^ (2 * s * (Formalism.HermitianLatticesTheory.fDeg K)) ≤ 1 :=
        pow_le_one₀ (by positivity) ((div_le_one (by linarith)).2 hg')
      have h2 : A ≤ (D₀ : ℝ) * x * x' := by
        calc A ≤ 1 * D₀ * x * x' := by rw [hA]; gcongr
          _ = _ := by ring
      have a' : (1 : ℝ) ≤ (GlobalTheory.Mass.idxN N (GlobalTheory.Mass.latIn U (fixLat p.1.2)) : ℝ) ^ 2 :=
        one_le_pow₀ (by exact_mod_cast a)
      have h3 : (0 : ℝ) ≤ n := by positivity
      nlinarith
    rw [hempty]
    simp

end GlobalTheory.DegCnt.FixedSpaceCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountIsometryPairsWithGivenFixedSpaceStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.count_isometry_pairs_with_given_fixed_space : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' s n : ℕ) (U : Submodule K V), 1 ≤ x → 1 ≤ x' → 1 ≤ n → Module.finrank K U + s = (Module.finrank K V) → GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip U) (GlobalTheory.Mass.latIn U L₀) = n → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = U}).encard : ℕ∞) : ℝ≥0∞) ≤ if (n : ℝ) ≤ (D₀ : ℝ) * x * x' then ENNReal.ofReal (((2 / (g : ℝ)) ^ (2 * s * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x' / n) ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x') ^ (2 * (s : ℝ) + 2 * cf K + 1) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (3 * (2 * j + 1)) * ((4 * s * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * s * (Formalism.HermitianLatticesTheory.fDeg K))) else 0 := by
  first | exact @GlobalTheory.DegCnt.FixedSpaceCount.main | exact GlobalTheory.DegCnt.FixedSpaceCount.main | (intros; apply GlobalTheory.DegCnt.FixedSpaceCount.main <;> assumption)
end
