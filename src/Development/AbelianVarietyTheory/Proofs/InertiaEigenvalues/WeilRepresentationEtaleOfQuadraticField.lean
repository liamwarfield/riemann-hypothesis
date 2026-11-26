module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepresentationHyperbolicSplit
public import GroundTheory.LocalFields.UnramifiedHensel
public import GroundTheory.LocalFields.UnramifiedGalois
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilConditionProductSplitting

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaKEqNegOneOfNotNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaKEqNegOneOfNotNorm
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.NonNorm

open ValuativeRel GroundTheory.LocalField IntermediateField

theorem not_two_dvd_ord_norm (F K L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Field L] [Algebra K L] (h2 : Module.finrank K L = 2) (ζ : L)
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[F] ^ 2 - 1)) (htop : K⟮ζ⟯ = ⊤) (s : K) (hs0 : s ≠ 0)
    (hs : ¬ ∃ y : L, Algebra.norm K y = s) : ¬ (2 : ℤ) ∣ ord (Algebra.norm F s) := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  obtain ⟨vK, tK, hK, eK⟩ := exists_isNonarchimedeanLocalField_valuativeExtension F K
  obtain ⟨vL, tL, hL, eL⟩ := exists_isNonarchimedeanLocalField_valuativeExtension K L
  have hm : ((Nat.card 𝓀[F] ^ 2 - 1 : ℕ) : 𝓀[K]) ≠ 0 :=
    by
      have hmF : ((Nat.card 𝓀[F] ^ 2 - 1 : ℕ) : 𝓀[F]) ≠ 0 :=
        natCast_card_pow_sub_one_ne_zero (K := F) two_ne_zero
      simpa using (map_ne_zero (algebraMap (𝓀[F]) (𝓀[K]))).2 hmF
  haveI : IsUnramified K L := ⟨ramificationIndex_eq_one_of_adjoin_eq_top hζ hm htop⟩
  have hodd : ¬ (2 : ℤ) ∣ ord s := by
    intro hd
    have h := (mem_range_normUnits_iff (K := K) (L := L) (Units.mk0 s hs0)).2 (by rw [h2]; exact hd)
    obtain ⟨y, hy⟩ := h
    exact hs ⟨y, congrArg Units.val hy⟩
  have hf : ¬ 2 ∣ ((IsLocalRing.maximalIdeal 𝒪[K]).inertiaDeg (𝒪[F])) := by
    rintro ⟨j, hj⟩
    have hcard : Nat.card 𝓀[K] = Nat.card 𝓀[F] ^ ((IsLocalRing.maximalIdeal 𝒪[K]).inertiaDeg (𝒪[F])) := by
      rw [residueDegree_eq_finrank]
      exact Module.natCard_eq_pow_finrank
    obtain ⟨z, hz⟩ := exists_isPrimitiveRoot_card_residueField_sub_one (L := K)
    have hz1 : IsPrimitiveRoot (z : K) (Nat.card 𝓀[K] - 1) :=
      hz.map_of_injective (f := (𝒪[K]).subtype) Subtype.val_injective
    have hz2 : IsPrimitiveRoot (algebraMap K L z) (Nat.card 𝓀[K] - 1) :=
      hz1.map_of_injective (algebraMap K L).injective
    haveI : NeZero (Nat.card 𝓀[K] - 1) := ⟨by have := one_lt_card_residueField K; omega⟩
    have hdvd : Nat.card 𝓀[F] ^ 2 - 1 ∣ Nat.card 𝓀[K] - 1 := by
      rw [hcard, hj, pow_mul]
      exact Nat.sub_one_dvd_pow_sub_one _ _
    obtain ⟨i, -, hi⟩ := hz2.eq_pow_of_pow_eq_one ((hζ.pow_eq_one_iff_dvd _).2 hdvd)
    have hbot : K⟮ζ⟯ = ⊥ := by
      rw [adjoin_simple_eq_bot_iff, ← hi, ← map_pow]
      exact IntermediateField.algebraMap_mem _ _
    have h1 : Module.finrank K L = 1 := by
      rw [← finrank_top', ← htop, hbot, IntermediateField.finrank_bot]
    omega
  rw [ord_norm]
  intro hd
  rcases (Int.prime_two.dvd_or_dvd hd) with h | h
  · exact hf (by exact_mod_cast h)
  · exact hodd h

@[reducible] noncomputable def normRel (F : Type) [NormedField F] [IsUltrametricDist F] : ValuativeRel F :=
  ValuativeRel.ofValuation (NormedField.valuation (K := F))

theorem isLocalField (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] :
    letI := normRel F;
    IsNonarchimedeanLocalField F := by
  letI := normRel F
  have hc : (NormedField.valuation (K := F)).Compatible := Valuation.Compatible.ofValuation _
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := inferInstance, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := F))
      (fun {s} => (NormedField.toValued (K := F)).is_topological_valuation s)
  · rw [isNontrivial_iff_isNontrivial (NormedField.valuation (K := F))]
    infer_instance

theorem ord_eq_of_norm_eq (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (x y : F) (h : ‖x‖ = ‖y‖) :
    letI := normRel F;
    haveI := isLocalField F;
    ord x = ord y := by
  letI := normRel F
  haveI := isLocalField F
  have h1 : x ≤ᵥ y := h.le
  have h2 : y ≤ᵥ x := h.ge
  rw [(valuation F).vle_iff_le] at h1 h2
  unfold ord
  rw [normalizedValuation_eq_iff.2 (le_antisymm h1 h2)]

theorem etaK_eq_neg_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∀ s : A.Kˣ, (¬ ∃ y : A.L, A.NL y = s) → A.etaK s = -1 := by
  intro F E _ _ _ _ hU A hK hL s hs
  haveI := hU.ultraF
  haveI := hU.ultraE
  haveI := hU.lcF
  haveI := hU.lcE
  letI := normRel F
  letI := normRel E
  haveI := isLocalField F
  haveI := isLocalField E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : ValuativeExtension F E := ⟨fun {a b} => by
    change ‖algebraMap F E a‖ ≤ ‖algebraMap F E b‖ ↔ ‖a‖ ≤ ‖b‖
    rw [norm_algebraMap', norm_algebraMap']⟩
  have he : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) = 1 := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
    obtain ⟨x, hx⟩ := hU.unram (π : E)
    have h1 := ord_eq_of_norm_eq E (π : E) (algebraMap F E x) (by rw [norm_algebraMap', hx])
    rw [ord_uniformizer hπ, ord_algebraMap] at h1
    have h2 : ((_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) : ℤ) ∣ 1 := ⟨_, h1⟩
    exact Nat.dvd_one.1 (by exact_mod_cast h2)
  obtain ⟨ζ, hζ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified F E he
  have hcard : Nat.card 𝓀[E] = Nat.card 𝓀[F] ^ 2 := by
    rw [← hU.finrank_eq, ← residueDegree_eq_finrank_of_unramified F E he, residueDegree_eq_finrank]
    exact Module.natCard_eq_pow_finrank
  rw [hcard] at hζ
  obtain ⟨⟨b⟩, -⟩ := Et.quadratic_structure F E A
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  have h2 : Module.finrank A.K A.L = 2 := by simpa using Module.finrank_eq_card_basis b
  have hζ' : IsPrimitiveRoot (algebraMap E A.L ζ) (Nat.card 𝓀[F] ^ 2 - 1) :=
    hζ.map_of_injective (algebraMap E A.L).injective
  have hE : ∀ e : E, algebraMap E A.L e ∈ A.K⟮algebraMap E A.L ζ⟯ := by
    intro e
    have he' : e ∈ F⟮ζ⟯ := by rw [htop]; trivial
    induction he' using IntermediateField.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.1 hx]
      exact mem_adjoin_simple_self _ _
    | algebraMap x =>
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F A.K A.L]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have htop' : A.K⟮algebraMap E A.L ζ⟯ = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hbc := A.push.symm.out
    induction y using hbc.inductionOn with
    | tmul e => exact hE e
    | smul k y hy => exact IntermediateField.smul_mem _ (hy trivial)
    | add y z hy hz => exact add_mem (hy trivial) (hz trivial)
  have hodd := not_two_dvd_ord_norm F A.K A.L h2 _ hζ' htop' s s.ne_zero hs
  unfold Et.etaK eta
  rw [if_neg]
  rintro ⟨y, hy⟩
  apply hodd
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h0 : Algebra.norm F (s : A.K) = 0 := norm_eq_zero.1 (by simpa using hy)
    exact s.ne_zero (Algebra.norm_eq_zero_iff.1 h0)
  have h3 := ord_eq_of_norm_eq F (Algebra.norm F (s : A.K)) (y ^ 2) (by rw [norm_pow, hy])
  rw [ord_pow hy0] at h3
  exact ⟨ord y, by exact_mod_cast h3⟩

end GlobalTheory.JR.NonNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaKEqNegOneOfNotNormStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaK_eq_neg_one_of_not_norm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∀ s : A.Kˣ, (¬ ∃ y : A.L, A.NL y = s) → A.etaK s = -1 := by
  first | exact @GlobalTheory.JR.NonNorm.etaK_eq_neg_one | exact GlobalTheory.JR.NonNorm.etaK_eq_neg_one | (intros; apply GlobalTheory.JR.NonNorm.etaK_eq_neg_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationExistsEtaleOfSubsingleton
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationExistsEtaleOfSubsingleton
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR

theorem weilAt_of_subsingleton (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (hK : Subsingleton A.K) : WeilAt A := by
  have h01 : (0 : A.L) = 1 := by
    rw [← map_zero (algebraMap A.K A.L), ← map_one (algebraMap A.K A.L), Subsingleton.elim (0 : A.K) 1]
  haveI hL : Subsingleton A.L := subsingleton_of_zero_eq_one h01
  have hpsi : ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ t : A.K, A.psiK ψ t = 1 := by
    intro ψ _ t
    unfold Et.psiK
    rw [Subsingleton.elim t 0, map_zero, AddChar.map_zero_eq_one]
  intro ψ hψ x μ hμ
  haveI := hμ.1
  have hpos : 0 < μ Set.univ := (isOpen_univ.measure_pos μ Set.univ_nonempty)
  have hfin : μ Set.univ < ⊤ := isCompact_univ.measure_lt_top
  have hreal : μ.real Set.univ ≠ 0 := by
    rw [measureReal_def]; exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  refine ⟨(μ.real Set.univ : ℂ)⁻¹, fun _ φ => φ, ?_, ?_⟩
  · exact ⟨fun _ _ hf => hf, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  · intro φ _
    refine ⟨?_, ?_, ?_⟩
    · intro z y; simp [hpsi ψ hψ]
    · intro s y
      have he : A.etaK (s : A.K) = 1 := by
        unfold Et.etaK eta
        rw [Subsingleton.elim (s : A.K) 1, map_one]
        rw [if_pos ⟨1, by simp⟩]
      have ha : A.absK (s : A.K) = 1 := by
        unfold Et.absK
        rw [dite_eq_left s.isUnit]
        rw [Subsingleton.elim (s.isUnit.unit) 1, map_one]
        rfl
      rw [he, ha, Subsingleton.elim ((s : A.K) • y) y]
      simp
    · intro y
      unfold fourB
      have : (fun x' => φ x' * A.kerL ψ x x' y) = fun _ => φ y := by
        funext x'
        unfold Et.kerL
        rw [hpsi ψ hψ, Subsingleton.elim x' y, mul_one]
      rw [this, integral_const, Complex.real_smul]
      show φ y = _
      have hc : ((μ.real Set.univ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hreal
      field_simp

end GlobalTheory.JR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationExistsEtaleOfSubsingletonStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationExistsEtale_of_subsingleton : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Subsingleton A.K → WeilAt A := by
  first | exact @GlobalTheory.JR.weilAt_of_subsingleton | exact GlobalTheory.JR.weilAt_of_subsingleton | (intros; apply GlobalTheory.JR.weilAt_of_subsingleton <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleInvolutiveAlgebraSplittingSmaller
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleInvolutiveAlgebraSplittingSmaller
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.EtQuot
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

section star
variable {L : Type} [CommRing L] [StarRing L]

def quotStarRing (J : Ideal L) (hJ : ∀ a ∈ J, star a ∈ J) : StarRing (L ⧸ J) where
  star := Ideal.Quotient.lift J ((Ideal.Quotient.mk J).comp (starRingEnd L))
    (fun a ha => by
      simp only [RingHom.comp_apply, starRingEnd_apply]; exact Ideal.Quotient.eq_zero_iff_mem.2 (hJ a ha))
  star_involutive x := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp
  star_mul x y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp [← map_mul, mul_comm]
  star_add x y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_add (Ideal.Quotient.mk J)]
    simp only [Ideal.Quotient.lift_mk, RingHom.comp_apply, starRingEnd_apply, map_add]

end star

variable (A : Et F E) (e : A.K)

abbrev QK := A.K ⧸ Ideal.span {e}

abbrev QL := A.L ⧸ (Ideal.span {e}).map (algebraMap A.K A.L)

instance twQ : IsScalarTower F (QK A e) (QL A e) := IsScalarTower.of_algebraMap_eq fun x => by
  rw [IsScalarTower.algebraMap_apply F A.K (QK A e)]
  simp only [Ideal.Quotient.algebraMap_eq, RingHom.comp_apply, Ideal.Quotient.algebraMap_quotient_map_quotient]
  show Ideal.Quotient.mk _ (algebraMap F A.L x) = _
  rw [IsScalarTower.algebraMap_apply F A.K A.L]

theorem star_mem (a : A.L) (ha : a ∈ (Ideal.span {e}).map (algebraMap A.K A.L)) :
    star a ∈ (Ideal.span {e}).map (algebraMap A.K A.L) := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at ha ⊢
  obtain ⟨c, rfl⟩ := ha
  exact ⟨star c, by rw [star_mul, A.star_K, mul_comm]⟩

def eq0 : TensorProduct A.K (QK A e) A.L ≃ₗ[A.K] QL A e :=
  (TensorProduct.comm A.K (QK A e) A.L).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A.L (Ideal.span {e})).symm.toLinearEquiv.restrictScalars A.K)

theorem etaleQuotientTensorLinearEquiv_one_tmul (x : A.L) : eq0 A e (1 ⊗ₜ x) = Ideal.Quotient.mk _ x := by
  simp only [eq0, LinearEquiv.trans_apply, TensorProduct.comm_tmul, LinearEquiv.restrictScalars_apply,
    AlgEquiv.toLinearEquiv_apply]
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {e})), Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul,
    one_smul]
  rfl

theorem isBaseChange_quot : IsBaseChange (QK A e) (IsScalarTower.toAlgHom A.K A.L (QL A e)).toLinearMap :=
  IsBaseChange.of_equiv ((eq0 A e).extendScalarsOfSurjective Ideal.Quotient.mk_surjective) fun x => by
    simpa using etaleQuotientTensorLinearEquiv_one_tmul A e x

theorem push_quot : Algebra.IsPushout F E (QK A e) (QL A e) := by
  have h2 : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap :=
    (Algebra.isPushout_iff F A.K E A.L).1 A.push.symm
  have h5 := h2.comp (isBaseChange_quot A e)
  refine Algebra.IsPushout.symm ((Algebra.isPushout_iff F (QK A e) E (QL A e)).2 ?_)
  have hm : (IsScalarTower.toAlgHom F E (QL A e)).toLinearMap =
      (IsScalarTower.toAlgHom A.K A.L (QL A e)).toLinearMap.restrictScalars F ∘ₗ
        (IsScalarTower.toAlgHom F E A.L).toLinearMap := by
    ext y; rfl
  rw [hm]; exact h5

end GlobalTheory.JR.EtQuot

namespace GlobalTheory.JR.EtQuot
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable (A : Et F E) (e : A.K)

theorem isReduced_quot (he : IsIdempotentElem e) : IsReduced (QK A e) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, hn⟩ := hx
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hn
  obtain ⟨c, hc⟩ := hn
  have h1 : IsNilpotent (y * (1 - e)) := ⟨n + 1, by
    rw [mul_pow, he.one_sub.pow_succ_eq, pow_succ, ← hc]
    linear_combination (-(c * y)) * he.eq⟩
  have h2 := IsReduced.eq_zero _ h1
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨y, by linear_combination -h2⟩

def quotEt (he : IsIdempotentElem e) : Et F E :=
  letI tK : TopologicalSpace (QK A e) := moduleTopology F _
  haveI mtK : IsModuleTopology F (QK A e) := ⟨rfl⟩
  letI tL : TopologicalSpace (QL A e) := moduleTopology F _
  haveI mtL : IsModuleTopology F (QL A e) := ⟨rfl⟩
  letI mK : MeasurableSpace (QK A e) := borel _
  letI mL : MeasurableSpace (QL A e) := borel _
  letI sL : StarRing (QL A e) := quotStarRing _ (star_mem A e)
  { K := QK A e
    L := QL A e
    redK := isReduced_quot A e he
    trK := IsModuleTopology.isTopologicalRing F _
    lcK := (IsModuleTopology.isOpenQuotientMap_of_surjective (R := F) (A := A.K)
      (φ := (Ideal.Quotient.mkₐ F (Ideal.span {e})).toLinearMap) (Ideal.Quotient.mkₐ_surjective F _)).locallyCompactSpace
    bK := ⟨rfl⟩
    bL := ⟨rfl⟩
    push := push_quot A e
    star_K := fun x => by
      obtain ⟨k, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
      show Ideal.Quotient.mk _ (star _) = _
      rw [A.star_K]
    star_E := fun y => by
      show Ideal.Quotient.mk _ (star (algebraMap E A.L y)) = Ideal.Quotient.mk _ (algebraMap E A.L (star y))
      rw [A.star_E] }

theorem exists_idem (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] [Nontrivial K] (hf : ¬ IsField K) :
    ∃ e : K, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  classical
  obtain ⟨m₁, hm₁⟩ := Ideal.exists_maximal K
  have hex : ∃ m₂ : Ideal K, m₂.IsMaximal ∧ m₂ ≠ m₁ := by
    by_contra h
    push_neg at h
    haveI : IsLocalRing K := IsLocalRing.of_unique_max_ideal ⟨m₁, hm₁, fun y hy => h y hy⟩
    exact hf (IsArtinianRing.isField_of_isReduced_of_isLocalRing K)
  obtain ⟨m₂, hm₂, hne⟩ := hex
  let i : MaximalSpectrum K := ⟨m₁, hm₁⟩
  let j : MaximalSpectrum K := ⟨m₂, hm₂⟩
  have hij : j ≠ i := fun h => hne (congrArg MaximalSpectrum.asIdeal h)
  haveI : i.asIdeal.IsMaximal := hm₁
  haveI : j.asIdeal.IsMaximal := hm₂
  let φ := IsArtinianRing.equivPi K
  refine ⟨φ.symm (Pi.single i 1), ?_, ?_, ?_⟩
  · unfold IsIdempotentElem
    rw [← map_mul, ← Pi.single_mul, mul_one]
  · intro h
    have := congrArg φ h
    simp at this
  · intro h
    have := congrFun (congrArg φ h) j
    simp [Pi.single_apply, hij] at this

end GlobalTheory.JR.EtQuot

namespace GlobalTheory.JR.EtQuot

theorem idem_eq_one_of_isUnit {K : Type} [CommRing K] {e : K} (he : IsIdempotentElem e) (hu : IsUnit e) : e = 1 := by
  obtain ⟨u, rfl⟩ := hu
  calc (u : K) = u * u * ↑u⁻¹ := by simp
    _ = u * ↑u⁻¹ := by rw [he.eq]
    _ = 1 := by simp

theorem nontrivial_quot {K : Type} [CommRing K] {e : K} (he : IsIdempotentElem e) (h1 : e ≠ 1) :
    Nontrivial (K ⧸ Ideal.span {e}) :=
  Ideal.Quotient.nontrivial_iff.2 (fun h => h1 (idem_eq_one_of_isUnit he (Ideal.span_singleton_eq_top.1 h)))

theorem exists_splitting : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), Nontrivial A.K → ¬ IsField A.K →
    ∃ (A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L),
      IsSplitting A A₁ A₂ eK eL ∧ Module.finrank F A₁.K < Module.finrank F A.K ∧
        Module.finrank F A₂.K < Module.finrank F A.K := by
  intro F E _ _ _ _ _ A hnt hf
  haveI : IsArtinianRing A.K := IsArtinianRing.of_finite F A.K
  obtain ⟨e, he, h0, h1⟩ := exists_idem A.K hf
  let A₁ := quotEt A e he
  let A₂ := quotEt A (1 - e) he.one_sub
  let eK : A.K ≃ₐ[F] A₁.K × A₂.K :=
    AlgEquiv.prodQuotientOfIsIdempotentElem F he he.one_sub (by ring) he.mul_one_sub_self
  let e' := algebraMap A.K A.L e
  have he' : IsIdempotentElem e' := he.map _
  have hJ1 : (Ideal.span {e}).map (algebraMap A.K A.L) = Ideal.span {e'} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hJ2 : (Ideal.span {1 - e}).map (algebraMap A.K A.L) = Ideal.span {1 - e'} := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_one]
  let eL : A.L ≃ₐ[F] A₁.L × A₂.L :=
    (AlgEquiv.prodQuotientOfIsIdempotentElem F he' he'.one_sub (by ring) he'.mul_one_sub_self).trans
      (AlgEquiv.prodCongr (Ideal.quotientEquivAlgOfEq F hJ1.symm) (Ideal.quotientEquivAlgOfEq F hJ2.symm))
  have hsum : Module.finrank F A.K = Module.finrank F A₁.K + Module.finrank F A₂.K := by
    rw [eK.toLinearEquiv.finrank_eq, Module.finrank_prod]
  haveI : Nontrivial A₁.K := nontrivial_quot he h1
  haveI : Nontrivial A₂.K := nontrivial_quot he.one_sub (fun h => h0 (by linear_combination -h))
  have p1 : 0 < Module.finrank F A₁.K := Module.finrank_pos
  have p2 : 0 < Module.finrank F A₂.K := Module.finrank_pos
  refine ⟨A₁, A₂, eK, eL, ⟨fun k => ?_, fun y => ?_, fun y => ?_⟩, by omega, by omega⟩
  · refine Prod.ext ?_ ?_
    · show Ideal.quotientEquivAlgOfEq F hJ1.symm (Ideal.Quotient.mk _ (algebraMap A.K A.L k)) =
        algebraMap (QK A e) (QL A e) (Ideal.Quotient.mk _ k)
      rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.Quotient.algebraMap_quotient_map_quotient]
    · show Ideal.quotientEquivAlgOfEq F hJ2.symm (Ideal.Quotient.mk _ (algebraMap A.K A.L k)) =
        algebraMap (QK A (1 - e)) (QL A (1 - e)) (Ideal.Quotient.mk _ k)
      rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.Quotient.algebraMap_quotient_map_quotient]
  · refine Prod.ext ?_ ?_
    · show Ideal.quotientEquivAlgOfEq F hJ1.symm (Ideal.Quotient.mk _ (algebraMap E A.L y)) =
        Ideal.Quotient.mk _ (algebraMap E A.L y)
      rw [Ideal.quotientEquivAlgOfEq_mk]
    · show Ideal.quotientEquivAlgOfEq F hJ2.symm (Ideal.Quotient.mk _ (algebraMap E A.L y)) =
        Ideal.Quotient.mk _ (algebraMap E A.L y)
      rw [Ideal.quotientEquivAlgOfEq_mk]
  · refine Prod.ext ?_ ?_
    · show Ideal.quotientEquivAlgOfEq F hJ1.symm (Ideal.Quotient.mk _ (star y)) =
        (quotStarRing _ (star_mem A e)).star (Ideal.quotientEquivAlgOfEq F hJ1.symm (Ideal.Quotient.mk _ y))
      rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientEquivAlgOfEq_mk]
      rfl
    · show Ideal.quotientEquivAlgOfEq F hJ2.symm (Ideal.Quotient.mk _ (star y)) =
        (quotStarRing _ (star_mem A (1 - e))).star (Ideal.quotientEquivAlgOfEq F hJ2.symm (Ideal.Quotient.mk _ y))
      rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientEquivAlgOfEq_mk]
      rfl

end GlobalTheory.JR.EtQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleInvolutiveAlgebraSplittingSmallerStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleInvolutiveAlgebraSplitting_smaller : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Nontrivial A.K → ¬ IsField A.K → ∃ (A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L), IsSplitting A A₁ A₂ eK eL ∧ Module.finrank F A₁.K < Module.finrank F A.K ∧ Module.finrank F A₂.K < Module.finrank F A.K := by
  first | exact @GlobalTheory.JR.EtQuot.exists_splitting | exact GlobalTheory.JR.EtQuot.exists_splitting | (intros; apply GlobalTheory.JR.EtQuot.exists_splitting <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationEtaleOfQuadraticField
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilEtProof

theorem weilAt_of_isField : WeilField → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → WeilAt A := by
  intro hF F E _ _ _ _ _ A hK hL ψ hψ x μ hμ
  have hfacts := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  refine hF F E A hK hL ψ hψ x μ hμ A.etaK (fun s => ⟨?_, fun h => GlobalTheory.T.etaK_eq_neg_one_of_not_norm F E A hK hL s h⟩)
  rintro ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h1 := hfacts.1 0
    rw [hy, zero_mul] at h1
    have hu : IsUnit (algebraMap A.K A.L s) := s.isUnit.map _
    rw [h1, isUnit_zero_iff] at hu
    obtain ⟨a, b, hab⟩ := hL.exists_pair_ne
    exact hab (by rw [← one_mul a, ← one_mul b, ← hu, zero_mul, zero_mul])
  obtain ⟨b, hb⟩ := hL.mul_inv_cancel hy0
  have := hfacts.2.2.2.1 y (IsUnit.of_mul_eq_one _ hb)
  rwa [hy] at this

end GlobalTheory.JR.WeilEtProof


open GlobalTheory.JR.WeilEtProof in
theorem GlobalTheory.JR.weilEt_of_weilField : WeilField → WeilEt := by
  intro hF F E _ _ _ _ _ A ψ hψ x μ hμ
  suffices h : ∀ (n : ℕ) (A : Et F E), Module.finrank F A.K = n → WeilAt A from h _ A rfl ψ hψ x μ hμ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hn
    rcases subsingleton_or_nontrivial A.K with hs | hnt
    · exact GlobalTheory.T.weilRepresentationExistsEtale_of_subsingleton F E A hs
    by_cases hK : IsField A.K
    · by_cases hL : IsField A.L
      · exact weilAt_of_isField hF F E A hK hL
      · intro ψ hψ x μ hμ
        obtain ⟨W, hW⟩ := GlobalTheory.T.exists_weilRepresentation_hyperbolic_split F E A ψ hψ hK hL x μ hμ
        exact ⟨1, W, hW⟩
    · obtain ⟨A₁, A₂, eK, eL, hs, h₁, h₂⟩ := GlobalTheory.T.exists_etaleInvolutiveAlgebraSplitting_smaller F E A hnt hK
      exact GlobalTheory.T.weil_condition_product_splitting F E A A₁ A₂ eK eL hs (ih _ (hn ▸ h₁) A₁ rfl) (ih _ (hn ▸ h₂) A₂ rfl)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationEtaleOfQuadraticFieldStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationEtale_of_quadraticField : WeilField → WeilEt := by
  first | exact @GlobalTheory.JR.weilEt_of_weilField | exact GlobalTheory.JR.weilEt_of_weilField | (intros; apply GlobalTheory.JR.weilEt_of_weilField <;> assumption)
end
