module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.NormCompat

def locUnit (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : Fˣ →* Ideles F :=
  (localIdele F v).comp (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom)

theorem locUnit_apply (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    locUnit F v a = localIdele F v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) := rfl

end GlobalTheory.NormCompat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousExtensionAdicCompletion
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory

theorem _root_.GlobalTheory.exists_continuous_extension_adicCompletion (E : Type) [Field E] [NumberField E] (l : ℕ)
    [Fact l.Prime] (τ : E →+* _root_.Formalism.ConjugateSelfDual.Qbar l) (v : HeightOneSpectrum (𝓞 E))
    (h : ∀ x : E, v.valuation E x < 1 ↔ ‖τ x‖ < 1) :
    ∃ j : v.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l, Continuous j ∧
      j.comp (algebraMap E (v.adicCompletion E)) = τ := by
  unfold _root_.Formalism.ConjugateSelfDual.Qbar at τ h ⊢

  let b := Module.finBasis ℚ E
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) :=
    IntermediateField.adjoin ℚ_[l] (Set.range fun i => τ (b i))
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  have hmem : ∀ x, τ x ∈ K := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem K _)
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

  let g : WithVal (v.valuation E) →+* PadicAlgCl l := τ.comp (WithVal.equiv (v.valuation E)).toRingHom
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E v
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  have hπ1 : ‖τ π‖ < 1 := (h π).1 (by rw [hπ]; decide)
  have hπpos : 0 < ‖τ π‖ := norm_pos_iff.2 ((map_ne_zero τ).2 hπ0)
  have hg : Continuous g := by
    refine continuous_of_continuousAt_zero g ?_
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hπ1
    let y : WithVal (v.valuation E) := (WithVal.equiv (v.valuation E)).symm (π ^ n)
    have hy : Valued.v.restrict y ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact (map_ne_zero _).2 (pow_ne_zero n hπ0)
    rw [Filter.Eventually, Valued.mem_nhds_zero]
    refine ⟨Units.mk0 _ hy, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx ⊢
    have hz : v.valuation E (WithVal.equiv (v.valuation E) x) < v.valuation E (π ^ n) := hx
    have hπn : v.valuation E (π ^ n) ≠ 0 := by
      rw [map_pow, hπ]; exact pow_ne_zero _ (WithZero.coe_ne_zero)
    have hq : v.valuation E (WithVal.equiv (v.valuation E) x / π ^ n) < 1 := by
      rw [map_div₀]
      exact (div_lt_one₀ (zero_lt_iff.2 hπn)).2 hz
    have hτq := (h _).1 hq
    rw [map_div₀, map_pow, norm_div, norm_pow, div_lt_one (pow_pos hπpos n)] at hτq
    rw [dist_zero_right]
    exact lt_trans hτq hn
  let τ' : WithVal (v.valuation E) →+* K :=
    (τ.codRestrict K hmem).comp (WithVal.equiv (v.valuation E)).toRingHom
  have hτ' : Continuous τ' := continuous_induced_rng.2 hg
  let ext : (v.valuation E).Completion →+* K := UniformSpace.Completion.extensionHom τ' hτ'
  let φ : v.adicCompletion E →+* (v.valuation E).Completion :=
    { toFun := HeightOneSpectrum.adicCompletion.toCompletion
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : Continuous φ := uniformContinuous_comap.continuous
  refine ⟨(algebraMap K (PadicAlgCl l)).comp (ext.comp φ), ?_, ?_⟩
  · exact continuous_subtype_val.comp (UniformSpace.Completion.continuous_extension.comp hφ)
  · ext x
    simp only [RingHom.comp_apply, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply]
    change ((ext ((WithVal.equiv (v.valuation E)).symm (algebraMap E E x) : (v.valuation E).Completion) : K) :
      PadicAlgCl l) = τ x
    rw [UniformSpace.Completion.extensionHom_coe]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormEmbeddingIntegerLeOne
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.LadicPlace

theorem norm_embedding_integer_le_one {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
    (τ : E →+* PadicAlgCl l) (a : 𝓞 E) : ‖τ (a : E)‖ ≤ 1 := by
  have h : IsIntegral ℤ (τ (a : E)) := by
    have := (RingOfIntegers.isIntegral_coe a).map τ.toIntAlgHom
    simpa using this
  obtain ⟨p, hp, hp0⟩ := h
  by_contra hlt
  push_neg at hlt
  set y := τ (a : E)
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at hp0
  have h1 : y ^ p.natDegree =
      - ∑ i ∈ Finset.range p.natDegree, algebraMap ℤ (PadicAlgCl l) (p.coeff i) * y ^ i := by
    linear_combination hp0
  have hpos : 0 < ‖y‖ ^ p.natDegree := pow_pos (by linarith) _
  have h2 : ‖∑ i ∈ Finset.range p.natDegree, algebraMap ℤ (PadicAlgCl l) (p.coeff i) * y ^ i‖
      < ‖y‖ ^ p.natDegree := by
    refine Finset.sum_induction _ (fun z => ‖z‖ < ‖y‖ ^ p.natDegree) ?_ (by simpa using hpos) ?_
    · intro u v hu hv
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max u v) (max_lt hu hv)
    · intro i hi
      rw [norm_mul, norm_pow]
      have h3 : ‖algebraMap ℤ (PadicAlgCl l) (p.coeff i)‖ ≤ 1 := by
        simpa using IsUltrametricDist.norm_intCast_le_one (PadicAlgCl l) (p.coeff i)
      calc _ ≤ 1 * ‖y‖ ^ i := by gcongr
        _ = ‖y‖ ^ i := one_mul _
        _ < _ := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  rw [← norm_neg, ← h1, norm_pow] at h2
  exact lt_irrefl _ h2

theorem exists_place_of_embedding :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (τ : E →+* Qbar l),
      ∃ v : HeightOneSpectrum (𝓞 E), ∀ x : E, v.valuation E x < 1 ↔ ‖τ x‖ < 1 := by
  intro E _ _ l hl τ
  have hle : ∀ a : 𝓞 E, ‖τ (a : E)‖ ≤ 1 := norm_embedding_integer_le_one τ
  let P : Ideal (𝓞 E) :=
    { carrier := {a | ‖τ (a : E)‖ < 1}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [RingOfIntegers.coe_eq_algebraMap, map_add (f := _), map_add (f := _)]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [RingOfIntegers.coe_eq_algebraMap, smul_eq_mul, map_mul, map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) ha }
  have hP : ∀ a : 𝓞 E, a ∈ P ↔ ‖τ (algebraMap (𝓞 E) E a)‖ < 1 := fun a => Iff.rfl
  have hone : ∀ a : 𝓞 E, a ∉ P → ‖τ (algebraMap (𝓞 E) E a)‖ = 1 := fun a ha =>
    le_antisymm (hle a) (not_lt.mp (fun h => ha ((hP a).mpr h)))
  have hprime : P.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hP]; simp
    · intro a b hab
      by_contra hn
      rw [not_or] at hn
      rw [hP, map_mul, map_mul, norm_mul, hone a hn.1, hone b hn.2] at hab
      simp at hab
  have hlP : (l : 𝓞 E) ∈ P := by
    rw [hP, map_natCast, map_natCast]
    have h1 : ((l : ℕ) : PadicAlgCl l) = ((l : ℚ_[l]) : PadicAlgCl l) := by
      simp
    rw [h1, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hlP
    exact hl.out.ne_zero (by exact_mod_cast hlP)
  let v : HeightOneSpectrum (𝓞 E) := ⟨P, hprime, hne⟩
  have key : ∀ x : E, v.valuation E x ≤ 1 → ∃ a s : 𝓞 E, s ∉ P ∧
      x * algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E a := by
    intro x hx
    obtain ⟨a, s, h⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
    exact ⟨a, s, s.2, h⟩
  refine ⟨v, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨a, s, hs, h⟩ := key x hx.le
    have ha : a ∈ P := by
      have : v.valuation E (algebraMap (𝓞 E) E a) < 1 := by
        rw [← h, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (v.valuation_le_one s)) hx
      exact (v.valuation_lt_one_iff_mem a).mp this
    rw [hP, ← h, map_mul, norm_mul, hone s hs, mul_one] at ha
    exact ha
  · by_contra hn
    have hn' : 1 ≤ v.valuation E x := not_lt.mp hn
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hn'
    have hinv : v.valuation E x⁻¹ ≤ 1 := by
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ hn'
    obtain ⟨a, s, hs, h⟩ := key _ hinv
    have h2 : algebraMap (𝓞 E) E s = x * algebraMap (𝓞 E) E a := by
      rw [← h, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
    have h3 := hone s hs
    rw [h2, map_mul, norm_mul] at h3
    have h4 := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx (hle a)
    exact absurd h3 h4.ne

end GlobalTheory.LadicPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfSupportedAtSplit
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct

namespace GlobalTheory.SplitLocEq

theorem _root_.GlobalTheory.SplitLocEq.conj_entry {L : Type} [Field L] [NumberField L] [IsCMField L]
    {n : ℕ} (x : _root_.ReciprocityTheory.Aut.GA L n) (i j : Fin n) :
    _root_.ReciprocityTheory.Aut.conjAL L ((x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) i j) =
      (((x⁻¹ : _root_.ReciprocityTheory.Aut.GA L n).1 : GL (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) j i := by
  have h : (x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) *
      _root_.ReciprocityTheory.Aut.conjT (_root_.ReciprocityTheory.Aut.conjAL L) (x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) = 1 := x.2
  have hinv : _root_.ReciprocityTheory.Aut.conjT (_root_.ReciprocityTheory.Aut.conjAL L) (x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) =
      (((x⁻¹ : _root_.ReciprocityTheory.Aut.GA L n).1 : GL (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) := by
    have h' := congrArg
      (fun M => (((x.1)⁻¹ : GL (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) * M) h
    simpa [← mul_assoc] using h'
  rw [← hinv]
  rfl

theorem proj_entry {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) (x : GA L n)
    (i j : Fin n) : SplitPlace.proj s ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      ((SplitPlace.loc s n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := rfl

private theorem evalAt_apply' {L : Type} [Field L] [NumberField L] (w)
    (a : _root_.ReciprocityTheory.Aut.AFplus L) : _root_.ReciprocityTheory.Aut.evalAt L w a = a w := rfl

private theorem eq_zero_of_compAt_eq_zero_of_proj_conj_eq_zero {L : Type} [Field L] [NumberField L] [IsCMField L]
    (s : _root_.ReciprocityTheory.Aut.SplitPlace L) (d : _root_.ReciprocityTheory.Aut.AL L)
    (hw : ∀ w, w ≠ s.v → _root_.ReciprocityTheory.Aut.compAt L w d = 0) (h₁ : SplitPlace.proj s d = 0)
    (h₂ : SplitPlace.proj s (_root_.ReciprocityTheory.Aut.conjAL L d) = 0) : d = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L :=
    Module.finBasisOfFinrankEq _ _ (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
  obtain ⟨a, c, rfl⟩ := _root_.GlobalTheory.tensor_exists_decomp b d
  have hw' : ∀ w, w ≠ s.v → a w = 0 ∧ c w = 0 := fun w hne =>
    _root_.GlobalTheory.tensor_decomp_eq_zero b _ _
      (by simpa [_root_.ReciprocityTheory.Aut.compAt, evalAt_apply'] using hw w hne)
  simp only [map_add (f := _), _root_.ReciprocityTheory.Aut.SplitPlace.proj, _root_.ReciprocityTheory.Aut.conjAL] at h₁ h₂
  simp [evalAt_apply'] at h₁ h₂
  set σ := IsCMField.complexConj L
  have hΔ : s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) ≠ 0 := by
    intro h0
    have h0' : b 0 * σ (b 1) - b 1 * σ (b 0) = 0 :=
      (injective_iff_map_eq_zero s.i.toRingHom).mp (RingHom.injective s.i.toRingHom) _ h0
    have hb1 : b 1 ≠ 0 := b.ne_zero 1
    have hσb1 : σ (b 1) ≠ 0 := by simpa using hb1
    have hfix : σ (b 0 / b 1) = b 0 / b 1 := by
      rw [map_div₀, div_eq_div_iff hσb1 hb1]
      linear_combination -h0'
    obtain ⟨k, hk⟩ : ∃ k : maximalRealSubfield L, (k : L) = b 0 / b 1 :=
      ⟨⟨_, (IsCMField.complexConj_eq_self_iff L _).mp hfix⟩, rfl⟩
    have hsum : ∑ i, (![1, -k] : Fin 2 → maximalRealSubfield L) i • b i = 0 := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
      have hsm : k • b 1 = (k : L) * b 1 := rfl
      rw [hsm, hk, div_mul_cancel₀ _ hb1]
      ring
    have := Fintype.linearIndependent_iff.mp b.linearIndependent _ hsum 0
    simp at this
  have hA : a s.v = 0 := by
    have : s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) * a s.v = 0 := by
      simp only [map_sub, map_mul]
      linear_combination s.i (σ (b 1)) * h₁ - s.i (b 1) * h₂
    exact (mul_eq_zero.mp this).resolve_left hΔ
  have hC : c s.v = 0 := by
    have : s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) * c s.v = 0 := by
      simp only [map_sub, map_mul]
      linear_combination s.i (b 0) * h₂ - s.i (σ (b 0)) * h₁
    exact (mul_eq_zero.mp this).resolve_left hΔ
  have ha : a = 0 := by
    ext w : 1
    by_cases hv : w = s.v
    · subst hv; exact hA
    · exact (hw' w hv).1
  have hc : c = 0 := by
    ext w : 1
    by_cases hv : w = s.v
    · subst hv; exact hC
    · exact (hw' w hv).2
  simp [ha, hc]

theorem _root_.GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq : ∀ (L : Type) [Field L] [NumberField L]
    [IsCMField L] (n : ℕ) (s : _root_.ReciprocityTheory.Aut.SplitPlace L) (x y : _root_.Formalism.AUTREP.GAf L n),
    _root_.ReciprocityTheory.Aut.TrivOutside (L := L) {s.v} x →
    _root_.ReciprocityTheory.Aut.TrivOutside (L := L) {s.v} y →
      SplitPlace.loc s n x = SplitPlace.loc s n y → x = y := by
  intro L _ _ _ n s x y hx hy hxy
  have triv : ∀ z : _root_.ReciprocityTheory.Aut.GA L n, _root_.ReciprocityTheory.Aut.TrivOutside (L := L) {s.v} z → ∀ w, w ≠ s.v → ∀ i j,
      _root_.ReciprocityTheory.Aut.compAt L w ((z.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) i j) =
        (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro z hz w hw i j
    have := hz w (by simpa using hw)
    exact congrFun (congrFun this i) j
  have trivInv : ∀ z : _root_.ReciprocityTheory.Aut.GA L n, _root_.ReciprocityTheory.Aut.TrivOutside (L := L) {s.v} z → _root_.ReciprocityTheory.Aut.TrivOutside (L := L) {s.v} z⁻¹ := by
    intro z hz w hw
    show ((z⁻¹).1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)).map (_root_.ReciprocityTheory.Aut.compAt L w) = 1
    have hm : (z.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) *
        ((z⁻¹).1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) = 1 := by simp
    have h2 := congrArg (Matrix.map · (_root_.ReciprocityTheory.Aut.compAt L w)) hm
    simp only [Matrix.map_mul] at h2
    rw [hz w hw, one_mul] at h2
    rw [h2]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hinv : SplitPlace.loc s n x⁻¹ = SplitPlace.loc s n y⁻¹ := by simp [map_inv, hxy]
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [← sub_eq_zero]
  apply eq_zero_of_compAt_eq_zero_of_proj_conj_eq_zero s
  · intro w hw
    rw [map_sub, triv x hx w hw, triv y hy w hw, sub_self]
  · rw [map_sub, _root_.GlobalTheory.SplitLocEq.proj_entry, _root_.GlobalTheory.SplitLocEq.proj_entry, hxy, sub_self]
  · rw [map_sub, _root_.GlobalTheory.SplitLocEq.conj_entry, _root_.GlobalTheory.SplitLocEq.conj_entry,
      map_sub, _root_.GlobalTheory.SplitLocEq.proj_entry, _root_.GlobalTheory.SplitLocEq.proj_entry, hinv, sub_self]

end GlobalTheory.SplitLocEq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceEqOfContEmbCompEq
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.HeckeGal.norm_lt_one_of_contEmb {E : Type} [Field E] [NumberField E]
    {l : ℕ} [Fact l.Prime]
    (v : HeightOneSpectrum (𝓞 E)) (j : v.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l) (hj : Continuous j)
    (a : 𝓞 E) (ha : a ∈ v.asIdeal) :
    ‖j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a))‖ < 1 := by
  set x := algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a) with hx
  have hx1 : ‖x‖ < 1 := by
    rw [hx, Valued.toNormedField.norm_lt_one_iff]
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) v a
    erw [h]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_mem]
    exact ha
  have hlim : Filter.Tendsto (fun n : ℕ => j x ^ n) Filter.atTop (nhds 0) := by
    have h0 := (hj.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx1)
    simpa [Function.comp_def, map_pow] using h0
  by_contra hge
  push_neg at hge
  have hball : ∀ᶠ n : ℕ in Filter.atTop, ‖j x ^ n‖ < 1 :=
    (tendsto_norm_zero.comp hlim).eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨n, hn⟩ := hball.exists
  rw [norm_pow] at hn
  exact absurd hn (not_lt.mpr (one_le_pow₀ hge))

theorem _root_.GlobalTheory.HeckeGal.place_eq_of_contEmb_comp_eq :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (v v' : HeightOneSpectrum (𝓞 E))
      (j : v.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l) (j' : v'.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l),
      Continuous j → Continuous j' →
      j.comp (algebraMap E (v.adicCompletion E)) = j'.comp (algebraMap E (v'.adicCompletion E)) →
      v = v' := by
  intro E _ _ l _ v v' j j' hj hj' hcomp
  by_contra hne
  have hideal : v.asIdeal ≠ v'.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have htop : v.asIdeal ⊔ v'.asIdeal = ⊤ := v.isMaximal.coprime_of_ne v'.isMaximal hideal
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ _)
  have hna := _root_.GlobalTheory.HeckeGal.norm_lt_one_of_contEmb v j hj a ha
  have hnb := _root_.GlobalTheory.HeckeGal.norm_lt_one_of_contEmb v' j' hj' b hb
  have hb' : j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E b)) =
      j' (algebraMap E (v'.adicCompletion E) (algebraMap (𝓞 E) E b)) :=
    RingHom.congr_fun hcomp _
  rw [← hb'] at hnb
  have hsum : j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a)) +
      j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E b)) = 1 := by
    rw [← map_add (f := _), ← map_add (f := _), ← map_add (f := _), hab, map_one, map_one, map_one]
  have hle := IsUltrametricDist.norm_add_le_max
    (j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a)))
    (j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E b)))
  rw [hsum, norm_one] at hle
  exact absurd (hle.trans_lt (max_lt hna hnb)) (lt_irrefl 1)

end GlobalTheory.HeckeGal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRationalPointOrbitAlgebraicWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRationalPointOrbitAlgebraicWeight
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem span_ratPt_orbit : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ v : ι → ℂ, v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ x = evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) *ᵥ v} := by
  intro L _ _ _ n a ι _ _ b P hA v hv w
  classical
  set x : a.W := b.equivFun.symm v with hx
  have hxv : b.repr x = v := by
    rw [← Module.Basis.equivFun_apply, hx, LinearEquiv.apply_symm_apply]
  have hx0 : x ≠ 0 := by
    intro h
    apply hv
    rw [← hxv, h, map_zero]
    rfl
  let S0 : Submodule ℂ a.W := Submodule.span ℂ (Set.range fun γ : GQ L n => a.ρ γ x)
  have hinv : ∀ (g : GQ L n) (y : a.W), y ∈ S0 → a.ρ g y ∈ S0 := by
    intro g y hy
    have hle : S0 ≤ S0.comap (a.ρ g) := by
      rw [Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      show a.ρ g (a.ρ γ x) ∈ S0
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨g * γ, rfl⟩
    exact hle hy
  let S : Subrepresentation a.ρ := ⟨S0, hinv⟩
  have hxS : x ∈ S0 := Submodule.subset_span ⟨1, by simp⟩
  have hS0 : S0 = ⊤ := by
    haveI := a.irr
    rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hx0
      have h2 : S.toSubmodule = (⊥ : Subrepresentation a.ρ).toSubmodule := congrArg _ h
      have h3 : x ∈ (⊥ : Subrepresentation a.ρ).toSubmodule := h2 ▸ hxS
      change x ∈ (⊥ : Submodule ℂ a.W) at h3
      exact (Submodule.mem_bot ℂ).1 h3
    · have h2 : S.toSubmodule = (⊤ : Subrepresentation a.ρ).toSubmodule := congrArg _ h
      exact h2
  have hw : w = b.equivFun.toLinearMap (b.equivFun.symm w) := (b.equivFun.apply_symm_apply w).symm
  have hmem : b.equivFun.symm w ∈ S0 := by rw [hS0]; trivial
  rw [hw]
  have hmap : Submodule.map b.equivFun.toLinearMap S0 ≤ Submodule.span ℂ {x | ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ x = evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) *ᵥ v} := by
    rw [Submodule.map_span_le]
    rintro _ ⟨γ, rfl⟩
    apply Submodule.subset_span
    have hγ : (γ : GA L n) ∈ ((GQ0 L n).map (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L))).subgroupOf (GA L n) := γ.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hγ
    obtain ⟨γ₀, hγ₀, he⟩ := hγ
    refine ⟨γ₀, hγ₀, ?_⟩
    have hE : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
      rw [← he]; rfl
    have hM := hA γ γ₀ hE
    show b.equivFun (a.ρ γ x) = _
    rw [Module.Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr b b, hxv, hM]
    rfl
  exact hmap (Submodule.mem_map_of_mem hmem)

end GlobalTheory.AlgWtHW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRationalPointOrbitAlgebraicWeightStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_rationalPoint_orbit_algebraicWeight : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ v : ι → ℂ, v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ x = evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) *ᵥ v} := by
  first | exact @GlobalTheory.AlgWtHW.span_ratPt_orbit | exact GlobalTheory.AlgWtHW.span_ratPt_orbit | (intros; apply GlobalTheory.AlgWtHW.span_ratPt_orbit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateNeSelf
noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace GlobalTheory.AlgWtHW

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem exists_gq (γ₀ : GL (Fin n) L) (h : γ₀ ∈ GQ0 L n) :
    ∃ γ : GQ L n, (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
  set g := Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) γ₀ with hgdef
  have hg : g ∈ GA L n := by
    show g.val * conjT (conjAL L) g.val = 1
    have e : conjT (conjAL L) g.val =
        (conjT (IsCMField.complexConj L : L →+* L) γ₀.val).map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := by
      ext i j
      simp [conjT, g, conjAL, Algebra.TensorProduct.map_tmul]
    rw [e]
    have h' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1 := h
    show γ₀.val.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) * _ = 1
    rw [← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.2 ⟨γ₀, h, rfl⟩⟩, rfl⟩

theorem conj_conj (φ : L →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by
  ext x; simp

theorem conjugate_ne_self (τ : L →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
  IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)

theorem isUPt_ratPt (γ₀ : GL (Fin n) L) (h : γ₀ ∈ GQ0 L n) : IsUPt (ratPt γ₀.val) := by
  intro σ
  have h' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1 := h
  have e : ratPt γ₀.val (ComplexEmbedding.conjugate σ) = (γ₀.val.map (IsCMField.complexConj L : L →+* L)).map σ := by
    ext i j
    simp [ratPt, IsCMField.complexEmbedding_complexConj]
  rw [e]
  have := congrArg (fun M => M.map σ) h'
  simpa [ratPt, conjT, Matrix.map_mul, Matrix.transpose_map] using this

open scoped Classical in
open Classical in
def tauPt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ := fun σ =>
  if σ = τ then B.val else if σ = ComplexEmbedding.conjugate τ then (B⁻¹).valᵀ else 1

theorem evPt_eq_upt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) :
    Formalism.L2.NG.evPt τ B = upt (tauPt τ B) := by
  funext p
  simp only [Formalism.L2.NG.evPt, upt, tauPt]
  split_ifs <;> simp [Matrix.one_apply, *]

theorem isUPt_tauPt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : IsUPt (tauPt τ B) := by
  intro σ
  have hne := conjugate_ne_self τ
  by_cases h1 : σ = τ
  · subst h1
    simp [tauPt, hne, Matrix.transpose_transpose]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      simp only [tauPt, if_neg h1, conj_conj, if_true]
      rw [← Matrix.transpose_transpose (B.val), ← Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
    · have h3 : ComplexEmbedding.conjugate σ ≠ τ := fun e => h2 (by rw [← e, conj_conj])
      have h4 : ComplexEmbedding.conjugate σ ≠ ComplexEmbedding.conjugate τ := fun e => h1 (by
        simpa using congrArg ComplexEmbedding.conjugate e)
      simp [tauPt, h1, h2, h3, h4]

end GlobalTheory.AlgWtHW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyTransformMemRationalUnitaryGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyTransformMemRationalUnitaryGroup
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.CayleyRat

theorem exists_mem_GQ0_eq_cayley_of_skew_hermitian : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (S : Matrix (Fin n) (Fin n) L), S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 → (1 - S).det ≠ 0 → ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ (γ₀ : Matrix (Fin n) (Fin n) L) = (1 + S) * (1 - S)⁻¹ := by
  intro L _ _ _ n S hS hdet
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  set T : Matrix (Fin n) (Fin n) L := 1 - S with hT
  set U : Matrix (Fin n) (Fin n) L := 1 + S with hU
  have hSc : conjT c S = -S := by
    unfold conjT; exact (neg_eq_of_add_eq_zero_right hS).symm
  have hcT : conjT c T = U := by
    have : conjT c T = conjT c 1 - conjT c S := by
      simp [conjT, hT, Matrix.map_sub, Matrix.transpose_sub]
    rw [this, conjT_one, hSc, hU, sub_neg_eq_add]
  have hcU : conjT c U = T := by
    have : conjT c U = conjT c 1 + conjT c S := by
      simp [conjT, hU, Matrix.map_add (f := _), Matrix.transpose_add]
    rw [this, conjT_one, hSc, hT, sub_eq_add_neg]
  have hdetU : U.det ≠ 0 := by
    have : U.det = c T.det := by
      rw [← hcT, conjT, Matrix.det_transpose, RingHom.map_det]; rfl
    rw [this]; exact (map_ne_zero c).mpr hdet
  have huT : IsUnit T.det := isUnit_iff_ne_zero.mpr hdet
  have huU : IsUnit U.det := isUnit_iff_ne_zero.mpr hdetU
  have hcTinv : conjT c T⁻¹ = U⁻¹ := by
    have h1 : U * conjT c T⁻¹ = 1 := by
      rw [← hcT, ← conjT_mul, Matrix.nonsing_inv_mul _ huT, conjT_one]
    exact (Matrix.inv_eq_right_inv h1).symm
  have hcomm : U * T = T * U := by
    simp [hU, hT, mul_sub, sub_mul, mul_add, add_mul]; abel
  have hinv : T⁻¹ * U⁻¹ = U⁻¹ * T⁻¹ := by
    rw [← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, hcomm]
  have hdetγ : IsUnit (U * T⁻¹).det := by
    rw [Matrix.det_mul]; exact huU.mul (Matrix.isUnit_nonsing_inv_det T huT)
  refine ⟨Matrix.nonsingInvUnit (U * T⁻¹) hdetγ, ?_, rfl⟩
  show (U * T⁻¹) * conjT c (U * T⁻¹) = 1
  rw [conjT_mul, hcTinv, hcU, Matrix.mul_assoc, ← Matrix.mul_assoc T⁻¹, hinv, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huU, Matrix.one_mul, Matrix.nonsing_inv_mul _ huT]

end GlobalTheory.CayleyRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyTransformMemRationalUnitaryGroupStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayleyTransform_mem_rational_unitaryGroup : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (S : Matrix (Fin n) (Fin n) L), S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 → (1 - S).det ≠ 0 → ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ (γ₀ : Matrix (Fin n) (Fin n) L) = (1 + S) * (1 - S)⁻¹ := by
  first | exact @GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian | exact GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian | (intros; apply GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaPowResidueCardSubOneApplyOfPowMem
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaPowResidueCardSubOneApplyOfPowMem
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory

theorem eq_one_of_pow_eq_one_of_val_sub_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {n : ℕ}
    (hn : A.valuation (n : Ω) = 1) {ξ : Ω} (hξ : ξ ^ n = 1) (h1 : A.valuation (ξ - 1) < 1) : ξ = 1 := by
  by_contra hne
  have hξA : A.valuation ξ ≤ 1 := by
    have : ξ = (ξ - 1) + 1 := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le h1.le (by simp))
  have hS : (∑ k ∈ Finset.range n, ξ ^ k) = 0 := by
    have h := geom_sum_mul ξ n
    rw [hξ, sub_self] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  have hsum : (n : Ω) = ∑ k ∈ Finset.range n, (1 - ξ ^ k) := by
    rw [Finset.sum_sub_distrib, hS]; simp
  have hlt : A.valuation (n : Ω) < 1 := by
    rw [hsum]
    refine Valuation.map_sum_lt _ one_ne_zero fun k _ => ?_
    have e : 1 - ξ ^ k = -((∑ j ∈ Finset.range k, ξ ^ j) * (ξ - 1)) := by
      rw [geom_sum_mul]; ring
    rw [e, Valuation.map_neg, Valuation.map_mul]
    have hs : A.valuation (∑ j ∈ Finset.range k, ξ ^ j) ≤ 1 :=
      Valuation.map_sum_le _ fun j _ => by rw [Valuation.map_pow]; exact pow_le_one' hξA j
    calc A.valuation (∑ j ∈ Finset.range k, ξ ^ j) * A.valuation (ξ - 1)
        ≤ 1 * A.valuation (ξ - 1) := by gcongr
      _ < 1 := by rw [one_mul]; exact h1
  rw [hn] at hlt
  exact lt_irrefl _ hlt

theorem val_eq_one_of_pow_eq_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {n : ℕ} (hn0 : n ≠ 0)
    {ζ : Ω} (hζ : ζ ^ n = 1) : A.valuation ζ = 1 := by
  have h : A.valuation ζ ^ n = 1 := by rw [← Valuation.map_pow, hζ, Valuation.map_one]
  exact valuation_eq_one_of_pow_eq_one A hn0 hζ

theorem ine_pow_normV_sub_one_apply_of_pow_mem : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (w : E) (π : Ω), π ^ (normV v - 1) = algebraMap E Ω w →
    ∀ ρ ∈ Ine (F := E) A, (ρ ^ (normV v - 1)) π = π := by
  intro E Ω _ _ _ _ v A hA w π hπ ρ hρ
  set n := normV v - 1 with hn_def
  rcases eq_or_ne n 0 with hn0 | hn0
  · rw [hn0, pow_zero]; rfl
  rcases eq_or_ne π 0 with hπ0 | hπ0
  · rw [hπ0, map_zero]

  have hq1 : 1 ≤ normV v := by omega
  have hqv : ((normV v : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    show ((Nat.card (𝓞 E ⧸ v.asIdeal) : ℕ) : 𝓞 E ⧸ v.asIdeal) = 0
    rcases finite_or_infinite (𝓞 E ⧸ v.asIdeal) with hf | hf
    · haveI := Fintype.ofFinite (𝓞 E ⧸ v.asIdeal)
      rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
    · rw [Nat.card_eq_zero_of_infinite]; simp
  have hqA : A.valuation ((normV v : ℕ) : Ω) < 1 := by
    have := (hA _).mpr hqv
    simpa using this
  have hnA : A.valuation (n : Ω) = 1 := by
    rw [hn_def, Nat.cast_sub hq1, Nat.cast_one, Valuation.map_sub_swap]
    exact Valuation.map_one_sub_of_lt _ hqA

  have hρπ : (ρ π) ^ n = π ^ n := by
    rw [← map_pow, hπ]; exact ρ.commutes w
  set ζ := ρ π * π⁻¹ with hζ_def
  have hζn : ζ ^ n = 1 := by
    rw [hζ_def, mul_pow, hρπ, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hπ0)]
  have hρπ' : ρ π = ζ * π := by rw [hζ_def, mul_assoc, inv_mul_cancel₀ hπ0, mul_one]
  have hζ1 : A.valuation ζ = 1 := valuation_eq_one_of_pow_eq_one A hn0 hζn
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, zero_pow hn0] at hζn; exact zero_ne_one hζn
  have hρζn : (ρ ζ) ^ n = 1 := by rw [← map_pow, hζn, map_one]
  have hclose : A.valuation (ρ ζ - ζ) < 1 := hρ.2 ζ hζ1.le
  have hξ : ρ ζ * ζ⁻¹ = 1 := by
    refine eq_one_of_pow_eq_one_of_val_sub_lt A hnA ?_ ?_
    · rw [mul_pow, hρζn, inv_pow, hζn, inv_one, one_mul]
    · have e : ρ ζ * ζ⁻¹ - 1 = (ρ ζ - ζ) * ζ⁻¹ := by field_simp
      rw [e, Valuation.map_mul, map_inv₀, hζ1, inv_one, mul_one]; exact hclose
  have hρζ : ρ ζ = ζ := by
    have := congrArg (· * ζ) hξ
    simpa [mul_assoc, inv_mul_cancel₀ hζ0] using this
  have key : ∀ k : ℕ, (ρ ^ k) π = ζ ^ k * π := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hρζ, hρπ', pow_succ]; ring
  rw [key, hζn, one_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaPowResidueCardSubOneApplyOfPowMemStatement
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_pow_residueCard_sub_one_apply_of_pow_mem : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (w : E) (π : Ω), π ^ (normV v - 1) = algebraMap E Ω w →
    ∀ ρ ∈ Ine (F := E) A, (ρ ^ (normV v - 1)) π = π := by
  first | exact @GlobalTheory.ine_pow_normV_sub_one_apply_of_pow_mem | exact GlobalTheory.ine_pow_normV_sub_one_apply_of_pow_mem | (intros; apply GlobalTheory.ine_pow_normV_sub_one_apply_of_pow_mem <;> assumption)
end
end
