module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JKInvOfTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDetBlocks
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.HeightTrivialParameterEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRangeOfIsAlgClosed
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.PlaceBallNormLemmas

variable {l : ℕ} [Fact l.Prime]

theorem denseRange_of_isAlgClosed {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l) :
    DenseRange j := by
  rw [Metric.denseRange_iff]
  intro x δ hδ
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  set f := minpoly ℚ_[l] x with hf
  have hn : f.natDegree ≠ 0 := (minpoly.natDegree_pos hx).ne'
  have hM : 0 < max ‖x‖ 1 := lt_max_of_lt_right one_pos
  have hq : 0 < δ / max ‖x‖ 1 := div_pos hδ hM
  have hε : 0 < (δ / max ‖x‖ 1) ^ f.natDegree / (f.natDegree + 1) := by positivity
  have hd : DenseRange (algebraMap ℚ ℚ_[l]) := Padic.denseRange_ratCast l
  obtain ⟨g, hg, hdeg, hc⟩ := Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hd
    (minpoly.monic hx) hε
  obtain ⟨b, hb, hlt⟩ := Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (L := PadicAlgCl l) hε
    (minpoly.aeval ℚ_[l] x) (minpoly.monic hx) (hg.map _) (by rw [hg.natDegree_map]; exact hdeg.symm) hc
    (IsAlgClosed.splits _)
  rw [← hf, mul_div_cancel₀ _ (by positivity), Real.pow_rpow_inv_natCast hq.le hn, div_mul_cancel₀ _ hM.ne'] at hlt
  have hs : (g.map (algebraMap ℚ Ω)).Splits := IsAlgClosed.splits _
  have e : (g.map (algebraMap ℚ ℚ_[l])).map (algebraMap ℚ_[l] (PadicAlgCl l)) = (g.map (algebraMap ℚ Ω)).map j := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact Subsingleton.elim _ _
  rw [Polynomial.aroots_def, e, hs.roots_map] at hb
  obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hb
  exact ⟨y, by rwa [dist_eq_norm]⟩

theorem norm_aut (σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : PadicAlgCl l) : ‖σ x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv σ x).symm

theorem continuous_aut (σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) : Continuous σ :=
  (AddMonoidHomClass.isometry_of_norm σ (norm_aut σ)).continuous

theorem norm_l : ‖(l : PadicAlgCl l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem norm_eq_of_ball {Ω : Type} [Field Ω] (i j : Ω →+* PadicAlgCl l) (h : ∀ x, ‖i x‖ ≤ 1 ↔ ‖j x‖ ≤ 1) (x : Ω) :
    ‖i x‖ = ‖j x‖ := by
  let v : AbsoluteValue Ω ℝ := (NormedField.toAbsoluteValue (PadicAlgCl l)).comp i.injective
  let w : AbsoluteValue Ω ℝ := (NormedField.toAbsoluteValue (PadicAlgCl l)).comp j.injective
  have hv : ∀ x, v x = ‖i x‖ := fun _ => rfl
  have hw : ∀ x, w x = ‖j x‖ := fun _ => rfl
  have he : v.IsEquiv w := by
    rw [AbsoluteValue.isEquiv_iff_lt_one_iff]
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have := h y⁻¹
    rw [map_inv₀, map_inv₀, norm_inv, norm_inv, inv_le_one₀ (norm_pos_iff.2 ((map_ne_zero i).2 hy)),
      inv_le_one₀ (norm_pos_iff.2 ((map_ne_zero j).2 hy))] at this
    rw [hv, hw, ← not_le, ← not_le, this]
  obtain ⟨c, hc, e⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  have h1 := congrFun e (l : Ω)
  simp only [hv, hw, map_natCast] at h1
  have h0 : 0 < ‖(l : PadicAlgCl l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hc1 : c = 1 := by
    refine (Real.rpow_right_inj h0 norm_l.ne).1 ?_
    rw [h1, Real.rpow_one]
  have h2 := congrFun e x
  simpa only [hv, hw, hc1, Real.rpow_one] using h2

theorem exists_aut {Ω : Type} [Field Ω] (i j : Ω →+* PadicAlgCl l) (hj : DenseRange j) (h : ∀ x, ‖i x‖ = ‖j x‖) :
    ∃ σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, ∀ x, σ (j x) = i x := by
  letI : NormedField Ω := NormedField.induced Ω (PadicAlgCl l) j j.injective
  have hn : ∀ x : Ω, ‖x‖ = ‖j x‖ := fun _ => rfl
  have hji : Isometry j := AddMonoidHomClass.isometry_of_norm j fun x => (hn x).symm
  let f : Ω →+* ℂ_[l] := (algebraMap (PadicAlgCl l) ℂ_[l]).comp i
  have hf : Isometry f := AddMonoidHomClass.isometry_of_norm f fun x => by
    rw [hn, ← h]; exact PadicComplex.norm_extends l (i x)
  let φ : PadicAlgCl l →+* ℂ_[l] := IsDenseInducing.extendRingHom hji.isUniformInducing hj hf.uniformContinuous
  have hφ : ∀ x, φ (j x) = f x := fun x =>
    IsDenseInducing.extend_eq (hji.isUniformInducing.isDenseInducing hj) hf.continuous x
  have hφc : Continuous φ :=
    (uniformContinuous_uniformly_extend hji.isUniformInducing hj hf.uniformContinuous).continuous
  have hcomm : (fun r : ℚ_[l] => φ (algebraMap ℚ_[l] (PadicAlgCl l) r)) = fun r => algebraMap ℚ_[l] ℂ_[l] r := by
    refine (Padic.denseRange_ratCast l).equalizer (hφc.comp (continuous_algebraMap _ _)) (continuous_algebraMap _ _) ?_
    funext q
    simp
  let ψ : PadicAlgCl l →ₐ[ℚ_[l]] ℂ_[l] := { φ with commutes' := fun r => congrFun hcomm r }
  refine ⟨ψ.restrictNormal' (PadicAlgCl l), fun x => (algebraMap (PadicAlgCl l) ℂ_[l]).injective ?_⟩
  exact (ψ.restrictNormal_commutes (PadicAlgCl l) (j x)).trans (hφ x)

section Main

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def ring (j : Ω →+* PadicAlgCl l) : ValuationSubring Ω :=
  ((NormedField.valuation (K := PadicAlgCl l)).comap j).valuationSubring

theorem mem_ring (j : Ω →+* PadicAlgCl l) (x : Ω) : x ∈ ring j ↔ ‖j x‖ ≤ 1 := by
  rw [ring, Valuation.mem_valuationSubring_iff]
  exact Iff.rfl

theorem valuation_ring_lt (j : Ω →+* PadicAlgCl l) (x : Ω) : (ring j).valuation x < 1 ↔ ‖j x‖ < 1 := by
  rw [ring, ← (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one]
  exact Iff.rfl

theorem norm_int_le (τ : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖τ (x : E)‖ ≤ 1 := by
  have h : IsIntegral ℤ (τ (x : E)) := (RingOfIntegers.isIntegral_coe x).map τ.toIntAlgHom
  have hv := Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))
  exact hv.mem_of_integral (h.tower_top (A := (NormedField.valuation (K := PadicAlgCl l)).integer))

def place (τ : E →+* PadicAlgCl l) : HeightOneSpectrum (𝓞 E) where
  asIdeal := (IsLocalRing.maximalIdeal (ring τ)).comap
    ((algebraMap (𝓞 E) E).codRestrict (ring τ) fun x => (mem_ring τ _).2 (norm_int_le τ x))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have : ((l : ℕ) : 𝓞 E) ∈ (⊥ : Ideal (𝓞 E)) := by
      rw [← h, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, valuation_ring_lt]
      simpa using norm_l (l := l)
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast (Ideal.mem_bot.1 this))

theorem mem_place (τ : E →+* PadicAlgCl l) (x : 𝓞 E) : x ∈ (place τ).asIdeal ↔ ‖τ (x : E)‖ < 1 := by
  rw [place, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, valuation_ring_lt]
  exact Iff.rfl

def compl (τ : E →+* PadicAlgCl l) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range τ)

theorem compl_eq (τ : E →+* PadicAlgCl l) : ∃ α : E, compl τ = IntermediateField.adjoin ℚ_[l] {τ α} := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  refine ⟨α, le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ (by simp))⟩
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ IntermediateField.adjoin ℚ {α} := hα ▸ IntermediateField.mem_top
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => exact IntermediateField.subset_adjoin _ _ (by rw [Set.mem_singleton_iff.1 hy]; rfl)
  | algebraMap q => simpa using SubfieldClass.ratCast_mem _ q
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | inv a _ ha => rw [map_inv₀]; exact inv_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem compl_fin (τ : E →+* PadicAlgCl l) : FiniteDimensional ℚ_[l] (compl τ) := by
  obtain ⟨α, h⟩ := compl_eq τ
  rw [h]
  exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)

omit [NumberField E] in
theorem compl_dense (τ : E →+* PadicAlgCl l) : (compl τ : Set (PadicAlgCl l)) ⊆ closure (Set.range τ) := by
  let S : Subfield (PadicAlgCl l) := τ.fieldRange.topologicalClosure
  have hS : ∀ r : ℚ_[l], algebraMap ℚ_[l] (PadicAlgCl l) r ∈ S := fun r => by
    refine (Padic.denseRange_ratCast l).induction_on r ?_ fun q => ?_
    · exact (Subfield.isClosed_topologicalClosure _).preimage (continuous_algebraMap _ _)
    · simpa using SubfieldClass.ratCast_mem S q
  have : compl τ ≤ S.toIntermediateField hS := IntermediateField.adjoin_le_iff.2 fun x hx => subset_closure hx
  exact this

omit [NumberField E] in
theorem mem_fix (τ : E →+* PadicAlgCl l) (σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) :
    σ ∈ (compl τ).fixingSubgroup ↔ ∀ x, σ (τ x) = τ x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  refine ⟨fun h x => h _ (IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩), fun h y hy => ?_⟩
  induction hy using IntermediateField.adjoin_induction with
  | mem y hy => obtain ⟨x, rfl⟩ := hy; exact h x
  | algebraMap q => exact σ.commutes q
  | add a b _ _ ha hb => rw [map_add (f := _), ha, hb]
  | inv a _ ha => rw [map_inv₀, ha]
  | mul a b _ _ ha hb => rw [map_mul, ha, hb]

omit [NumberField E] in
theorem mem_dec (j : Ω →+* PadicAlgCl l) (g : Ω ≃ₐ[E] Ω) :
    g ∈ ReciprocityTheory.Gal.Dec (F := E) (ring j) ↔ ∀ x, ‖j (g x)‖ = ‖j x‖ := by
  have h0 : g ∈ ReciprocityTheory.Gal.Dec (F := E) (ring j) ↔ ∀ x, g x ∈ ring j ↔ x ∈ ring j := by
    rw [← inv_mem_iff]
    change (open Pointwise in g⁻¹ • ring j) = ring j ↔ _
    rw [SetLike.ext_iff]
    simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, AlgEquiv.smul_def]
  rw [h0]
  simp only [mem_ring]
  exact ⟨fun h => norm_eq_of_ball (j.comp (g : Ω →+* Ω)) j h, fun h x => by rw [h]⟩

omit [NumberField E] in
theorem exists_res [Normal E Ω] (j : Ω →+* PadicAlgCl l) (σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l)
    (h : ∀ x : E, σ (j (algebraMap E Ω x)) = j (algebraMap E Ω x)) : ∃ g : Ω ≃ₐ[E] Ω, ∀ x, σ (j x) = j (g x) := by
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  letI : Algebra E (PadicAlgCl l) := (j.comp (algebraMap E Ω)).toAlgebra
  haveI : IsScalarTower E Ω (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψ : PadicAlgCl l →ₐ[E] PadicAlgCl l := { (σ : PadicAlgCl l →+* PadicAlgCl l) with commutes' := h }
  exact ⟨ψ.restrictNormal' Ω, fun x => (ψ.restrictNormal_commutes Ω x).symm⟩

theorem exists_equiv [IsAlgClosure E Ω] (j : Ω →+* PadicAlgCl l) :
    ∃ e : ↥(compl (j.comp (algebraMap E Ω))).fixingSubgroup ≃* ↥(ReciprocityTheory.Gal.Dec (F := E) (ring j)),
      Continuous e ∧ Continuous e.symm ∧
      ∀ σ x, (σ.1 : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (j x) = j (((e σ).1 : Ω ≃ₐ[E] Ω) x) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI := compl_fin (j.comp (algebraMap E Ω))
  have hd := denseRange_of_isAlgClosed j
  set K := compl (j.comp (algebraMap E Ω)) with hK
  choose r hr using fun σ : ↥K.fixingSubgroup => exists_res (E := E) j σ ((mem_fix _ _).1 σ.2)
  let R : ↥K.fixingSubgroup →* (Ω ≃ₐ[E] Ω) := MonoidHom.mk' r fun a b => AlgEquiv.ext fun x => j.injective (by
    rw [← hr, AlgEquiv.mul_apply, ← hr, ← hr]; rfl)
  have hRc : Continuous R := by
    refine continuous_of_continuousAt_one R ?_
    rw [ContinuousAt, map_one]
    intro s hs
    obtain ⟨F, hF, hs⟩ := (krullTopology_mem_nhds_one_iff E Ω s).1 hs
    let b := Module.finBasis E F
    have ho : ∀ᶠ σ : ↥K.fixingSubgroup in nhds 1, ∀ i, (σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (j (b i)) = j (b i) := by
      refine Filter.eventually_all.2 fun i => ?_
      exact ((stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) (j (b i))).preimage continuous_subtype_val).mem_nhds
        (show (1 : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) ∈ MulAction.stabilizer _ (j (b i)) from one_mem _)
    refine Filter.mem_map.2 (Filter.mem_of_superset ho fun σ hσ => hs ?_)
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => ?_
    have hl : (r σ).toLinearMap ∘ₗ F.val.toLinearMap = F.val.toLinearMap :=
      b.ext fun i => j.injective ((hr σ _).symm.trans (hσ i))
    exact LinearMap.congr_fun hl ⟨y, hy⟩
  let R' : ↥K.fixingSubgroup →* ↥(ReciprocityTheory.Gal.Dec (F := E) (ring j)) :=
    R.codRestrict _ fun σ => (mem_dec j _).2 fun x => by
      change ‖j (r σ x)‖ = _
      rw [← hr, norm_aut]
  have hbij : Function.Bijective R' := by
    refine ⟨fun a b hab => Subtype.ext (AlgEquiv.ext fun x => ?_), fun g => ?_⟩
    · have hab' : r a = r b := congrArg Subtype.val hab
      refine congrFun (hd.equalizer (continuous_aut a.1) (continuous_aut b.1) (funext fun y => ?_)) x
      change a.1 (j y) = b.1 (j y)
      rw [hr, hr, hab']
    · obtain ⟨σ, hσ⟩ := exists_aut (j.comp (g.1 : Ω →+* Ω)) j hd ((mem_dec j _).1 g.2)
      refine ⟨⟨σ, (mem_fix _ _).2 fun x => (hσ _).trans (congrArg j (g.1.commutes x))⟩,
        Subtype.ext (AlgEquiv.ext fun x => j.injective ?_)⟩
      exact (hr _ x).symm.trans (hσ x)
  have hc : Continuous (MulEquiv.ofBijective R' hbij) := hRc.subtype_mk _
  haveI : CompactSpace ↥K.fixingSubgroup :=
    isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K).isCompact
  exact ⟨MulEquiv.ofBijective R' hbij, hc,
    Continuous.continuous_symm_of_equiv_compact_to_t2 (f := (MulEquiv.ofBijective R' hbij).toEquiv) hc, hr⟩

end Main

theorem exists_bridge {E : Type} (Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ}
    [Fact (Nat.Prime l)] (τ : E →+* Formalism.ConjugateSelfDual.Qbar l) :
    ∃ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (_ : Formalism.ConjugateSelfDual.IsPlaceOver A w) (LL : Formalism.BasicNotions.Loc.FinExt l)
      (Bw : Formalism.BasicNotions.LocBridge l E Ω (ReciprocityTheory.Gal.Dec A) ↥(Formalism.BasicNotions.Loc.OL LL)),
      GlobalTheory.Pst.Induces Bw ∧ GlobalTheory.Pst.IsInduced Bw τ (AlgHom.id ℚ_[l] ↥Bw.Kw.1) := by
  obtain ⟨j, hj⟩ : ∃ j : Ω →+* PadicAlgCl l, j.comp (algebraMap E Ω) = τ := by
    letI : Algebra E (PadicAlgCl l) := τ.toAlgebra
    haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
    let j : Ω →ₐ[E] PadicAlgCl l := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    exact ⟨j, RingHom.ext fun x => j.commutes x⟩
  subst hj
  obtain ⟨e, h1, h2, h3⟩ := exists_equiv (E := E) j
  haveI := compl_fin (j.comp (algebraMap E Ω))
  let LL : Formalism.BasicNotions.Loc.FinExt l :=
    ⟨IntermediateField.normalClosure ℚ_[l] (compl (j.comp (algebraMap E Ω))) (PadicAlgCl l), inferInstance⟩
  refine ⟨place (j.comp (algebraMap E Ω)), ring j, fun x => ?_, LL,
    { Kw := ⟨compl (j.comp (algebraMap E Ω)), inferInstance⟩
      j := j
      j_E := fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
      j_dense := compl_dense _
      e := e.symm
      e_cont := h2
      e_symm_cont := h1
      e_comm := fun g x => (h3 (e.symm g) x).trans (congrArg (fun u : ↥(ReciprocityTheory.Gal.Dec (F := E) (ring j)) => j (u.1 x)) (e.apply_symm_apply g))
      LL := LL
      LL_split := fun t x => t.fieldRange_le_normalClosure ⟨x, rfl⟩
      eO := RingEquiv.refl _
      eO_alg := fun _ => rfl
      eO_cont := continuous_id
      eO_symm_cont := continuous_id }, fun x => mem_ring j x, fun _ => rfl⟩
  rw [valuation_ring_lt, mem_place]
  exact Iff.rfl

end GlobalTheory.PlaceBallNormLemmas

end
end

set_option autoImplicit false

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.Published.CharAboveModel
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD

namespace GlobalTheory.ExpFrame.Tests

section Jumps

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]


variable (Ω) in
theorem exists_bridge (τ : E →+* Qbar l) : ∃ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (_ : IsPlaceOver A w)
    (LL : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL)), GlobalTheory.Pst.Induces Bw ∧
      IsInduced Bw τ (AlgHom.id ℚ_[l] ↥Bw.Kw.1) := by
  first
  | exact @_root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge
  | exact _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge
  | (apply _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge <;> assumption)
  | (intros; apply _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge ..)

end Jumps

section RankOne

variable (l : ℕ) [Fact l.Prime]

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

end RankOne

section Small

end Small

end GlobalTheory.ExpFrame.Tests

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedLocalSituationOfEmbedding
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.PlaceLetters

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]

theorem norm_emb_le (σ : E →+* Om l) (b : 𝓞 E) : ‖σ (b : E)‖ ≤ 1 :=
  GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int σ b.isIntegral_coe)

theorem emb_eq_of_congr (hE : ¬ (l : ℤ) ∣ discr E) (τ τ' : E →+* Om l)
    (hlt : ∀ b : 𝓞 E, ‖τ (b : E) - τ' (b : E)‖ < 1) : τ = τ' := by
  classical
  by_contra hne
  have hd := GlobalTheory.SplitEmbSep.one_le_norm_intCast (C := Om l) Fact.out GlobalTheory.PlaceBridge.norm_l_lt_one hE
  let b := integralBasis E
  have e : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] Om l) :=
    Fintype.equivOfCardEq (by rw [AlgHom.card, Module.finrank_eq_card_basis b])
  have hdet := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ (Om l) b e
  rw [← coe_discr, map_intCast] at hdet
  set M := Algebra.embeddingsMatrixReindex ℚ (Om l) b e with hM
  have hMij : ∀ i j, M i j = (e j).toRingHom ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i j
    simp [hM, b, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, integralBasis_apply]
  set k := e.symm τ.toRatAlgHom with hk
  set k' := e.symm τ'.toRatAlgHom with hk'
  have hkk : k ≠ k' := fun h => hne (by
    have := e.symm.injective h
    exact RingHom.ext fun x => DFunLike.congr_fun this x)
  have hcol : ∀ i, M i k + (-1 : Om l) • M i k' =
      τ ((RingOfIntegers.basis E i : 𝓞 E) : E) - τ' ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i
    rw [hMij, hMij, hk, hk', e.apply_symm_apply, e.apply_symm_apply, neg_one_smul,
      ← sub_eq_add_neg]
    rfl
  have hlt' : ‖M.det‖ < 1 := by
    rw [← Matrix.det_updateCol_add_smul_self M hkk (-1)]
    refine GlobalTheory.SplitEmbSep.norm_det_lt_one _ (fun i j => ?_) k fun i => ?_
    · by_cases hj : j = k
      · rw [hj, Matrix.updateCol_self, hcol]; exact (hlt _).le
      · rw [Matrix.updateCol_ne hj, hMij]; exact norm_emb_le _ _
    · rw [Matrix.updateCol_self, hcol]; exact hlt _
  rw [hdet, norm_pow] at hd
  exact absurd (hd.trans_lt (pow_lt_one₀ (norm_nonneg _) hlt' two_ne_zero)) (lt_irrefl _)

theorem norm_algHom {K : IntermediateField ℚ_[l] (Om l)} (f : ↥K →ₐ[ℚ_[l]] Om l) (x : ↥K) :
    ‖f x‖ = ‖(x : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]
  have h1 := minpoly.algHom_eq f f.toRingHom.injective x
  have h2 := minpoly.algHom_eq K.val K.val.toRingHom.injective x
  exact congrArg spectralValue (h1.trans h2.symm)

theorem norm_gal (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algEquiv_eq]

theorem norm_sub_lt_one {x y : Om l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx (by rwa [norm_neg]))

theorem inertia_of_fix (g : GQ l) (hg : ∀ x ∈ MaximalUnramifiedExtension l, g x = x) (x : Om l) (hx : ‖x‖ ≤ 1) : ‖g x - x‖ < 1 := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact norm_sub_lt_one (by rwa [norm_gal]) hlt
  · obtain ⟨ζ, m, hm, hζ, hxζ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller_bar x heq
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
    have h1 : g ζ = ζ := hg ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm0, hm, hζ⟩)
    have h2 : g x - x = g (x - ζ) - (x - ζ) := by rw [map_sub, h1]; ring
    rw [h2]
    exact norm_sub_lt_one (by rwa [norm_gal]) hxζ

theorem emb_mem_Kur (hE : ¬ (l : ℤ) ∣ discr E) (τ : E →+* Om l) (x : E) : τ x ∈ MaximalUnramifiedExtension l := by
  have : IsGalois ℚ_[l] (Om l) := {}
  rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
  intro g hg
  have h := emb_eq_of_congr hE ((g : Om l →+* Om l).comp τ) τ fun b =>
    inertia_of_fix g ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hg) _ (norm_emb_le τ b)
  exact DFunLike.congr_fun h x

theorem exists_extend {K : IntermediateField ℚ_[l] (Om l)} (f : ↥K →ₐ[ℚ_[l]] Om l) :
    ∃ g : Om l →ₐ[ℚ_[l]] Om l, ∀ x : ↥K, g x = f x :=
  ⟨f.liftNormal (Om l), fun x => f.liftNormal_commutes (Om l) x⟩

section Bridge

variable {Ω : Type} [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem kw_le (M : IntermediateField ℚ_[l] (Om l)) (h : ∀ x : E, Bw.j (algebraMap E Ω x) ∈ M) : Bw.Kw.1 ≤ M := by
  have hfin := GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (Bw.j.comp (algebraMap E Ω))
  have hcl := Submodule.closed_of_finiteDimensional (𝕜 := ℚ_[l])
    (IntermediateField.adjoin ℚ_[l] (Set.range (Bw.j.comp (algebraMap E Ω)))).toSubmodule
  refine le_trans (fun y hy => ?_) (IntermediateField.adjoin_le_iff.2 (Set.range_subset_iff.2 h))
  exact closure_minimal (IntermediateField.subset_adjoin ℚ_[l] _) hcl (Bw.j_dense hy)

theorem kw_le_comap (LL : FinExt l) (hL : ∀ (τ : E →+* Om l) (x : E), τ x ∈ LL.1) (g : Om l →ₐ[ℚ_[l]] Om l) :
    Bw.Kw.1 ≤ LL.1.comap g :=
  kw_le Bw _ fun x => hL ((g : Om l →+* Om l).comp (Bw.j.comp (algebraMap E Ω))) x

theorem caseA (hl : l ≠ 2) (hE : ¬ (l : ℤ) ∣ discr E) (LL : FinExt l) (hζ : ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l)
    (hL : ∀ (τ : E →+* Om l) (x : E), τ x ∈ LL.1) : CaseA Bw.Kw LL := by
  have hK : Bw.Kw.1 ≤ MaximalUnramifiedExtension l := kw_le Bw _ fun x => emb_mem_Kur hE (Bw.j.comp (algebraMap E Ω)) x
  refine ⟨hK, hl, le_rfl, fun h => absurd h hl, (le_inf le_rfl hK).trans le_sup_left, fun τ x => ?_⟩
  obtain ⟨g, hg⟩ := exists_extend τ
  obtain ⟨ζ, hζ⟩ := hζ
  have hζ' : IsPrimitiveRoot (ζ : Om l) l := hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  have hle : Ks Bw.Kw 1 ≤ LL.1.comap g := by
    refine sup_le (inf_le_left.trans (kw_le_comap Bw LL hL g)) (IntermediateField.adjoin_le_iff.2 fun y hy => ?_)
    have hy' : g y ^ l = 1 := by
      have : y ^ l = 1 := by simpa using hy
      rw [← map_pow, this, map_one]
    haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hy'
    change g y ∈ LL.1
    rw [← hi]
    exact pow_mem ζ.2 i
  rw [← hg]
  exact hle x.2

end Bridge

section Letters

variable {Ω : Type} [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (hK : Bw.Kw.1 ≤ K0 Bw.Kw) {LL : FinExt l}

def toK0 : E →+* ↥(K0 Bw.Kw) :=
  (Bw.j.comp (algebraMap E Ω)).codRestrict (K0 Bw.Kw) fun x => hK (Bw.j_E x)

def embOf (e : ↥(K0 Bw.Kw) →ₐ[ℚ_[l]] ↥LL.1) : E →+* Om l :=
  ((LL.1.val.comp e : ↥(K0 Bw.Kw) →ₐ[ℚ_[l]] Om l) : ↥(K0 Bw.Kw) →+* Om l).comp (toK0 Bw hK)


omit [NumberField E] in
theorem isInduced_embOf (e : ↥(K0 Bw.Kw) →ₐ[ℚ_[l]] ↥LL.1) (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hτ : ∀ x : ↥(K0 Bw.Kw), τ (algebraMap ↥(K0 Bw.Kw) ↥Bw.Kw.1 x) = e x) :
    GlobalTheory.Pst.IsInduced Bw (embOf Bw hK e) τ := fun x =>
  congrArg Subtype.val (hτ (toK0 Bw hK x)).symm


omit [NumberField E] in
theorem embOf_injective : Function.Injective (embOf Bw hK (LL := LL)) := by
  intro e e' h
  have h1 := isInduced_embOf Bw hK e (e.comp (IntermediateField.inclusion hK)) fun _ => rfl
  have h2 := isInduced_embOf Bw hK e' (e'.comp (IntermediateField.inclusion hK)) fun _ => rfl
  rw [← h] at h2
  have h3 := h1.unique h2
  exact AlgHom.ext fun x => DFunLike.congr_fun h3 (algebraMap ↥(K0 Bw.Kw) ↥Bw.Kw.1 x)

theorem embOf_frob (P : LocPrime l) (hE : ¬ (l : ℤ) ∣ discr E) {σ : Equiv.Perm (E →+* PadicAlgCl l)}
    (hσ : GlobalTheory.ExpFrame.IsFrobPerm σ) (e : ↥(K0 Bw.Kw) →ₐ[ℚ_[l]] ↥LL.1) :
    embOf Bw hK (e.comp (P.PD Bw.Kw).σ) = σ (embOf Bw hK e) := by
  refine emb_eq_of_congr hE _ _ fun b => ?_
  have h1 := hσ (embOf Bw hK e) b
  have h2 := P.PD_σ Bw.Kw (toK0 Bw hK b) (norm_emb_le (Bw.j.comp (algebraMap E Ω)) b)
  have h3 := norm_algHom (LL.1.val.comp e) ((P.PD Bw.Kw).σ (toK0 Bw hK b) - toK0 Bw hK b ^ l)
  rw [map_sub, map_pow] at h3
  have h4 : ‖embOf Bw hK (e.comp (P.PD Bw.Kw).σ) b - embOf Bw hK e b ^ l‖ < 1 := h3.trans_lt h2
  have h5 := norm_sub_lt_one h4 h1
  rwa [sub_sub_sub_cancel_right] at h5

end Letters

theorem exists_bridge_over (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (LL : FinExt l)
    (hL : ∀ (τ : E →+* Om l) (x : E), τ x ∈ LL.1) (τ : E →+* Om l) :
    ∃ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (_ : Formalism.ConjugateSelfDual.IsPlaceOver A w)
      (Bw : LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) A) ↥(OL LL)), GlobalTheory.Pst.Induces Bw ∧ Bw.LL.1 ≤ LL.1 ∧
        ∀ x, τ x = Bw.j (algebraMap E Ω x) := by
  obtain ⟨w, A, hA, L0, Bw, hI, hτ⟩ := GlobalTheory.ExpFrame.Tests.exists_bridge Ω τ
  refine ⟨w, A, hA, { Bw with
    LL := LL
    LL_split := fun f x => ?_
    eO := RingEquiv.refl _
    eO_alg := fun _ => rfl
    eO_cont := continuous_id
    eO_symm_cont := continuous_id }, hI, le_rfl, hτ⟩
  obtain ⟨g, hg⟩ := exists_extend f
  rw [← hg]
  exact kw_le_comap Bw LL hL g x.2

theorem exists_place : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (H : LocHW l P) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), GlobalTheory.ExpFrame.IsFrobPerm σ → ∀ LL : FinExt l, (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) → ∀ i₀ : E →+* PadicAlgCl l, ∃ (K : FinExt l) (hA : CaseA K LL) (ι : ↥(GK K) →* (Ω ≃ₐ[E] Ω)) (κ : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (E →+* PadicAlgCl l)), Function.Injective κ ∧ (∀ i, κ (i - 1) = σ (κ i)) ∧ i₀ ∈ Set.range κ ∧ ∀ (n : ℕ) (r : (Ω ≃ₐ[E] Ω) →* GL (Fin n) ↥(OL LL)) (J : (E →+* PadicAlgCl l) → Multiset ℤ), GlobalTheory.ExpFrame.CrysWith ((Matrix.GeneralLinearGroup.map (toOm LL)).comp r) J → MatGood P (H.W K 1 LL hA.2.2).emb (r.comp ι) (fun i => J (κ i)) := by
  intro l _ P AI hT H E Ω _ _ _ _ _ hl hE σ hσ LL hζ hL i₀
  obtain ⟨w, A, hA, Bw, hI, hLL, hi₀⟩ := exists_bridge_over Ω LL hL i₀
  have hC := caseA Bw hl hE LL hζ hL
  have hK0 : Bw.Kw.1 ≤ K0 Bw.Kw := le_inf le_rfl hC.1
  have hbij := (H.W Bw.Kw 1 LL hC.2.2).emb_bij
  have hembσ := (H.W Bw.Kw 1 LL hC.2.2).emb_σ
  let emb := (H.W Bw.Kw 1 LL hC.2.2).emb
  have hK0L : K0 Bw.Kw ≤ LL.1 := inf_le_left.trans (kw_le Bw _ fun x => hL (Bw.j.comp (algebraMap E Ω)) x)
  refine ⟨Bw.Kw, hC, (ReciprocityTheory.Gal.Dec (F := E) A).subtype.comp Bw.e.symm.toMonoidHom, fun i => embOf Bw hK0 (emb i),
    (embOf_injective Bw hK0).comp hbij.1, fun i => ?_, ?_, fun n r J hr => ?_⟩
  · have h := hembσ (i - 1)
    rw [sub_add_cancel] at h
    exact (congrArg (embOf Bw hK0) h.symm).trans (embOf_frob Bw hK0 P hE hσ (emb i))
  · obtain ⟨i, hi⟩ := hbij.2 (IntermediateField.inclusion hK0L)
    refine ⟨i, RingHom.ext fun x => ?_⟩
    change embOf Bw hK0 ((H.W Bw.Kw 1 LL hC.2.2).emb i) x = _
    rw [hi, hi₀]
    rfl
  · obtain ⟨hc, hj⟩ := hr.2 P AI ⟨hT⟩ w A hA _ Bw hI
    have hM : GlobalTheory.Pst.IsModel Bw (((Matrix.GeneralLinearGroup.map (toOm LL)).comp r).comp
        (ReciprocityTheory.Gal.Dec (F := E) A).subtype) LL
        (Formalism.MainNotions.N.mapRep (algebraMap ↥(OL LL) ↥LL.1) (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) :=
      ⟨hLL, by ext g a b; rfl⟩
    refine ⟨fun a b => ?_, (hM.isCrysAt_iff P).1 hc, fun i τ hτ a => ?_⟩
    · have h1 : Continuous fun g : ↥(GK Bw.Kw) => ((Bw.e.symm g : ↥(ReciprocityTheory.Gal.Dec (F := E) A)) : Ω ≃ₐ[E] Ω) :=
        continuous_subtype_val.comp Bw.e_symm_cont
      have h2 := (Units.continuous_val.comp (hr.1.comp h1)).matrix_elem a b
      exact continuous_induced_rng.2 h2
    · have hτ' := isInduced_embOf Bw hK0 (emb i) τ hτ
      exact (GlobalTheory.Pst.IsJumpsAt.count_eq P hM hτ' (hj _ _ _ hτ') a).symm

end GlobalTheory.PlaceLetters

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedLocalSituationOfEmbeddingStatement
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramifiedLocalSituation_of_embedding : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (H : LocHW l P) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), GlobalTheory.ExpFrame.IsFrobPerm σ → ∀ LL : FinExt l, (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) → ∀ i₀ : E →+* PadicAlgCl l, ∃ (K : FinExt l) (hA : CaseA K LL) (ι : ↥(GK K) →* (Ω ≃ₐ[E] Ω)) (κ : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (E →+* PadicAlgCl l)), Function.Injective κ ∧ (∀ i, κ (i - 1) = σ (κ i)) ∧ i₀ ∈ Set.range κ ∧ ∀ (n : ℕ) (r : (Ω ≃ₐ[E] Ω) →* GL (Fin n) ↥(OL LL)) (J : (E →+* PadicAlgCl l) → Multiset ℤ), GlobalTheory.ExpFrame.CrysWith ((Matrix.GeneralLinearGroup.map (toOm LL)).comp r) J → MatGood P (H.W K 1 LL hA.2.2).emb (r.comp ι) (fun i => J (κ i)) := by
  first | exact @GlobalTheory.PlaceLetters.exists_place | exact GlobalTheory.PlaceLetters.exists_place | (intros; apply GlobalTheory.PlaceLetters.exists_place <;> assumption)
end
