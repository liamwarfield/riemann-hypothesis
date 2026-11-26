module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.ExistsIsWeilDatumOF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPWMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.LatK

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpEta
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsEtaCmTypeK
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsHeckeCharacterTrivialExponent
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsWeilCharK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.WeilTypeChar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem exists_weil_char_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∃ ξ : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ξ ∧ HasExp B.emb ξ (fun _ => 1) := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsCMField E := isCMField_of_cmExt hB.cm
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨q, hq1, hq⟩ := Nat.exists_infinite_primes (max 3 (Nat.card (Units.torsion E) + 1))
  have hq2 : 2 < q := by omega
  have htq : Nat.card (Units.torsion E) < q := by omega
  have ht : ¬ q ∣ Nat.card (Units.torsion E) := fun h => absurd (Nat.le_of_dvd Nat.card_pos h) (by omega)
  obtain ⟨U, hU, hUinf, hUk⟩ := GlobalTheory.T.exists_open_idele_subgroup_congruence_mod_q F E q hq.ne_zero
  obtain ⟨χ, hχc, hχ1, hχU, hχk⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (AF F ⊗[F] E)ˣ Eˣ U hU
    (Units.map (incAF F E).toMonoidHom) 1 (chiInf B.emb) (continuous_chiInf B.emb) (norm_chiInf B.emb)
    (fun _ => by simp) (fun k hk => by
      obtain ⟨u, hu, hu1⟩ := hUk k hk
      refine Units.ext ?_
      rw [chiInf_apply, MonoidHom.one_apply, Units.val_one]
      have e : ∀ w, piInf (B.emb w) ((Units.map (incAF F E).toMonoidHom k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
          (B.emb w).1 ((u : 𝓞 E) : E) := fun w => by
        rw [hu]
        exact GlobalTheory.ThK.EvAt0.ZPartArc.piInf_inclR' (B.emb w) (k : E)
      simp only [e]
      exact (GlobalTheory.T.cmType_unit_phase_prod_eq_one_of_congruent_one F E σ hB.cm B.emb q hq hq2 ht u hu1).symm)
  refine ⟨GlobalTheory.unitaryCharToCircle χ hχ1, ⟨?_, fun k => ?_⟩, fun z hz => ?_⟩
  · exact Continuous.subtype_mk (Units.continuous_val.comp hχc) _
  · apply Circle.ext
    show ((χ (Units.map (incAF F E).toMonoidHom k) : ℂˣ) : ℂ) = 1
    rw [hχk]; rfl
  · show ((χ z : ℂˣ) : ℂ) = _
    rw [hχU z (hUinf z hz), chiInf_apply]
    simp
end GlobalTheory.WeilTypeChar
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hecke_character_trivial_exponent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∃ ξ : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ξ ∧ HasExp B.emb ξ (fun _ => 1) := by
  first | exact @_root_.GlobalTheory.WeilTypeChar.exists_weil_char_k | exact _root_.GlobalTheory.WeilTypeChar.exists_weil_char_k | (intros; apply _root_.GlobalTheory.WeilTypeChar.exists_weil_char_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExtendCharacterToNormGroup
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsExtendHeckeK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open GlobalTheory.HeckeExtend
noncomputable section
namespace GlobalTheory.HeckeExtend
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem exists_extend_hecke_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ lam : (AF F)ˣ →* Circle, Continuous lam →
      (∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1) →
      (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) →
      ∃ lam' : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF lam' ∧
        (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → lam' z = 1) ∧
        ∀ a, lam' (idFF F E a) = lam a := by
  intro F E _ _ _ _ _ σ B hB lam hc h1 hinf
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨M, hM, hMk⟩ := GlobalTheory.T.exists_congruence_kernel_ideleCharacter_trivialAtInfinity F lam hc hinf
  let V : Subgroup (AF F ⊗[F] E)ˣ := (Units.map (incAF F E).toMonoidHom).range ⊔ WE F E (8 * M)
  have hkey : ∀ a : (AF F)ˣ, idFF F E a ∈ V → lam a = 1 := key σ hB.cm M hM lam h1 hMk
  have hN : 0 < 8 * M := by positivity
  have hWo : IsOpen (WE F E (8 * M) : Set (AF F ⊗[F] E)ˣ) := by
    have ho := GlobalTheory.T.isOpen_integralTensorAdeleMultiples F E (8 * M) hN
    have hcv : Continuous fun z : (AF F ⊗[F] E)ˣ => (z : AF F ⊗[F] E) - 1 :=
      Units.continuous_val.sub continuous_const
    have hci : Continuous fun z : (AF F ⊗[F] E)ˣ => ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 :=
      Units.continuous_coe_inv.sub continuous_const
    exact (ho.preimage hcv).inter (ho.preimage hci)
  have hVo : IsOpen (V : Set (AF F ⊗[F] E)ˣ) := Subgroup.isOpen_mono le_sup_right hWo
  let ψ0 : (AF F)ˣ →* (AF F ⊗[F] E)ˣ ⧸ V := (QuotientGroup.mk' V).comp (idFF F E)
  have hker : ψ0.ker ≤ lam.ker := fun a ha => hkey a ((QuotientGroup.eq_one_iff _).1 ha)
  letI : DivisibleBy (Additive Circle) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨t, ht⟩ := Circle.exp_surjective u.toMul
    refine ⟨Additive.ofMul (Circle.exp (t / n)), ?_⟩
    show Additive.ofMul (Circle.exp (t / n) ^ n) = u
    rw [← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn), ht]
    rfl
  letI : DivisibleBy (Additive Circle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive (QuotientGroup.kerLift ψ0)) (QuotientGroup.kerLift_injective ψ0)
    (MonoidHom.toAdditive (QuotientGroup.lift ψ0.ker lam hker))
  let κ : (AF F ⊗[F] E)ˣ ⧸ V →* Circle := MonoidHom.toAdditive.symm ρ
  have hκ : ∀ x, κ (QuotientGroup.kerLift ψ0 x) = QuotientGroup.lift ψ0.ker lam hker x :=
    fun x => DFunLike.congr_fun hρ (Additive.ofMul x)
  have hV1 : ∀ z ∈ V, κ.comp (QuotientGroup.mk' V) z = 1 := fun z hz => by
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz, map_one]
  refine ⟨κ.comp (QuotientGroup.mk' V), ⟨?_, fun x => hV1 _ (le_sup_left (a := (Units.map (incAF F E).toMonoidHom).range)
    ⟨x, rfl⟩)⟩, fun z hz => hV1 z (le_sup_right (a := (Units.map (incAF F E).toMonoidHom).range) ?_), fun a => hκ (a : (AF F)ˣ ⧸ ψ0.ker)⟩
  · refine continuous_of_continuousAt_one _ ?_
    unfold ContinuousAt
    rw [map_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hVo.mem_nhds (one_mem V)] with z hz
    exact (hV1 z hz).symm
  · have hN' := hN
    refine ⟨GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity F E _ hN' _ hz, GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity F E _ hN' _ ?_⟩
    intro u hu
    have e : ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = -(((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((z : AF F ⊗[F] E) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [e, smul_neg, ← mul_smul_comm, hz u hu, mul_zero, neg_zero]
end GlobalTheory.HeckeExtend
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_character_to_norm_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ lam : (AF F)ˣ →* Circle, Continuous lam →
      (∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1) →
      (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) →
      ∃ lam' : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF lam' ∧
        (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → lam' z = 1) ∧
        ∀ a, lam' (idFF F E a) = lam a := by
  first | exact @_root_.GlobalTheory.HeckeExtend.exists_extend_hecke_k | exact _root_.GlobalTheory.HeckeExtend.exists_extend_hecke_k | (intros; apply _root_.GlobalTheory.HeckeExtend.exists_extend_hecke_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EtaCharacterArchimedeanFormula
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EtaEqProdSignK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
namespace GlobalTheory.EtaSignReal
open GlobalTheory.QuadSymbol GlobalTheory.IdeleNormChar GlobalTheory.AdelicU
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem eta_eq_prod_sign_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ η : (AF F)ˣ →* Circle, IsEtaF E η → ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) →
      (η a : ℂ) = ∏ w, piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) /
        ((‖piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)‖ : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ σ B hB η hη a ha
  have hcm := hB.cm
  haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
  haveI := hcm.1
  rw [eq_signToCircle η hη, MonoidHom.comp_apply, normSign_eq_prod (finComp_eq_one ha), map_prod]
  rw [show ((∏ w : InfinitePlace F, signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) =
      ∏ w : InfinitePlace F, ((signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) from
    map_prod Circle.coeHom _ _]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw : w.IsReal := IsTotallyReal.isReal w
  rw [piInf_idFF hw]
  set r := InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion)
  have hx := mem_normGroup_iff_pos hcm hw (B.emb w) (infComp a w)
  have hr0 : r ≠ 0 := (map_ne_zero _).2 (infComp a w).ne_zero
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hpos : 0 < r
  · rw [eta_eq_one_iff.2 (hx.2 hpos), map_one, abs_of_pos hpos, div_self (by exact_mod_cast hr0)]
    rfl
  · have hneg : r < 0 := lt_of_le_of_ne (not_lt.1 hpos) hr0
    rw [eta_eq_neg_one_iff.2 (fun h => hpos (hx.1 h)), abs_of_neg hneg]
    change ((if (-1 : ℤˣ) = 1 then (1 : Circle) else -1 : Circle) : ℂ) = _
    rw [if_neg (by decide)]
    push_cast
    rw [div_neg, div_self (by exact_mod_cast hr0)]
end GlobalTheory.EtaSignReal
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eta_character_archimedean_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ η : (AF F)ˣ →* Circle, IsEtaF E η → ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) →
      (η a : ℂ) = ∏ w, piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) /
        ((‖piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)‖ : ℝ) : ℂ) := by
  first | exact @_root_.GlobalTheory.EtaSignReal.eta_eq_prod_sign_k | exact _root_.GlobalTheory.EtaSignReal.eta_eq_prod_sign_k | (intros; apply _root_.GlobalTheory.EtaSignReal.eta_eq_prod_sign_k <;> assumption)
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.EtaCMType
theorem exists_eta_cmType_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∃ η : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF η ∧ ResEtaF η 1 ∧ HasExp B.emb η (fun _ => 1) := by
  intro F E _ _ _ _ _ σ B hB
  obtain ⟨ξ, hξ, hξe⟩ := _root_.GlobalTheory.T.exists_hecke_character_trivial_exponent F E σ B hB
  obtain ⟨η₀, hη₀, huniq⟩ := GlobalTheory.IdeleNormChar.globalNormIndexTwo F E hB.cm.2.2.1
  have hη₀' : IsEtaF E η₀ := hη₀
  let lam : (AF F)ˣ →* Circle := ξ.comp (idFF F E) * η₀⁻¹
  have hlam : ∀ a, lam a = ξ (idFF F E a) * (η₀ a)⁻¹ := fun a => rfl
  have hlc : Continuous lam := by
    have : Continuous fun a => ξ (idFF F E a) * (η₀ a)⁻¹ :=
      (hξ.1.comp continuous_idFF).mul (hη₀.1.inv)
    exact this
  have hlF : ∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1 := by
    intro a
    rw [hlam, idFF_rat, hξ.2, hη₀.2.1, inv_one, one_mul]
  have hlinf : ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1 := by
    intro a ha
    have e1 := hξe _ (at_idFF a ha)
    have e2 := _root_.GlobalTheory.T.eta_character_archimedean_formula F E σ B hB η₀ hη₀' a ha
    have e3 : ξ (idFF F E a) = η₀ a := by
      apply Circle.ext
      rw [e1, e2]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [zpow_one]
    rw [hlam, e3, mul_inv_cancel]
  obtain ⟨lam', hl'H, hl'inf, hl'res⟩ := _root_.GlobalTheory.T.extend_character_to_norm_group F E σ B hB lam hlc hlF hlinf
  refine ⟨ξ * lam'⁻¹, ⟨hξ.1.mul hl'H.1.inv, fun x => ?_⟩, ⟨⟨η₀, hη₀'⟩, fun η hη a => ?_⟩, fun z hz => ?_⟩
  · change ξ _ * (lam' _)⁻¹ = 1
    rw [hξ.2, hl'H.2, inv_one, one_mul]
  · change ξ _ * (lam' _)⁻¹ = _
    rw [huniq η hη, hl'res, hlam, pow_one, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel_comm]
  · change ((ξ z * (lam' z)⁻¹ : Circle) : ℂ) = _
    rw [hl'inf z hz, inv_one, mul_one]
    exact hξe z hz
end GlobalTheory.EtaCMType
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpEtaA
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.InertCompletionIsField
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsFieldTensorOfIsInertAtK
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
namespace GlobalTheory.InertTensorField
theorem isField_tensor_of_isInertAt_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) := by
  intro F E _ _ _ _ _ σ B hB v w hvw
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [show v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal from hvw]
    exact w.isPrime
  exact GlobalTheory.InertField.isField_of_inert F E hB.cm.2.2.1 v hp
end GlobalTheory.InertTensorField
end
end

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_completion_isField : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) := by
  first | exact @_root_.GlobalTheory.InertTensorField.isField_tensor_of_isInertAt_k | exact _root_.GlobalTheory.InertTensorField.isField_tensor_of_isInertAt_k | (intros; apply _root_.GlobalTheory.InertTensorField.isField_tensor_of_isInertAt_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnitEqMulConjK
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
namespace GlobalTheory.InertUnitNorm
open IsDedekindDomain.HeightOneSpectrum Polynomial
end GlobalTheory.InertUnitNorm
namespace GlobalTheory.InertUnitNorm
open IsDedekindDomain.HeightOneSpectrum Polynomial
end GlobalTheory.InertUnitNorm
namespace GlobalTheory.InertUnitNorm
open IsDedekindDomain.HeightOneSpectrum Polynomial
end GlobalTheory.InertUnitNorm
namespace GlobalTheory.InertUnitNorm
open IsDedekindDomain.HeightOneSpectrum Polynomial
end GlobalTheory.InertUnitNorm
namespace GlobalTheory.InertUnitNorm
open IsDedekindDomain.HeightOneSpectrum Polynomial
end GlobalTheory.InertUnitNorm
namespace GlobalTheory.InertUnitNorm
open IsDedekindDomain.HeightOneSpectrum Polynomial
theorem unit_eq_mul_conj_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) →
    ∀ u : Fv F v, Valued.v u = 1 →
      ∃ z : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) u = z * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ z := by
  intro F E _ _ _ _ _ σ B hB v w hvw _hfield u hu
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [show v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal from hvw]
    exact w.isPrime
  obtain ⟨a, b, c, hq, hconj, hroot⟩ := exists_integral_gen σ hB.cm v hp
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hB.inert v w hvw).1
  obtain ⟨x, y, hxy⟩ := exists_int_sol v b c h2 hroot ⟨u, hu.le⟩ hu
  have hK : (x : Fv F v) ^ 2 - algebraMap F (Fv F v) (b : F) * x * y +
      algebraMap F (Fv F v) (c : F) * y ^ 2 = u := by
    have := congrArg (fun t : v.adicCompletionIntegers F => (t : v.adicCompletion F)) hxy
    simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul,
      SubmonoidClass.coe_pow, coe_algebraMap_adicCompletionIntegers] at this
    exact this
  let ι := algebraMap (Fv F v) (Fv F v ⊗[F] E)
  have hιF : ∀ t : F, ι (algebraMap F (Fv F v) t) = (1 : Fv F v) ⊗ₜ[F] algebraMap F E t := fun t => by
    rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  set α : Fv F v ⊗[F] E := (1 : Fv F v) ⊗ₜ[F] (a : E) with hα
  have hq' : α ^ 2 + ι (algebraMap F (Fv F v) (b : F)) * α + ι (algebraMap F (Fv F v) (c : F)) = 0 := by
    have := congrArg (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E) hq
    rw [map_add (f := _), map_add (f := _), map_mul, map_pow, map_zero] at this
    rw [hιF, hιF]
    exact this
  have hσα : Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ α =
      -ι (algebraMap F (Fv F v) (b : F)) - α := by
    rw [hα, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hconj, hιF,
      TensorProduct.tmul_sub, TensorProduct.tmul_neg]
  refine ⟨ι x + ι y * α, ?_⟩
  rw [map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, hσα]
  have hKι := congrArg ι hK
  simp only [map_add (f := _), map_sub, map_mul, map_pow] at hKι
  linear_combination (-1 : Fv F v ⊗[F] E) * hKι + ι y ^ 2 * hq'
end GlobalTheory.InertUnitNorm
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF Formalism.IndefR.LiftF
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeExtend GlobalTheory.HeckeExtend.AtInf GlobalTheory.SplitDetCharF
namespace PositivityTheory.ThKW.Eta
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem local_norm_k {σ : E →ₐ[F] E} {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v)ˣ)
    (h1 : 2 * (u : Fv F v) ∈ v.adicCompletionIntegers F)
    (h2 : 2 * ((u⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F) :
    u ∈ GlobalTheory.QuadSymbol.normGroup F E (Fv F v) := by
  obtain ⟨δ, b, hδ, hb0, hb1, hbb⟩ :=
    GlobalTheory.QuadNormBase.exists_basis F E σ hB.cm.2.2.1 (sig_invol hB.cm) (sig_ne hB.cm)
  have hbb' : b 1 * b 1 = algebraMap F E δ := hbb
  refine (GlobalTheory.QuadSymbol.mem_normGroup_iff_form b hb0 hbb').2 ?_
  rcases _root_.GlobalTheory.T.nonempty_algHom_or_exists_inert_of_goodK F E σ B hB v with ⟨τ⟩ | ⟨w, hw⟩
  · obtain ⟨τ⟩ := τ
    have hs : τ (b 1) * τ (b 1) = algebraMap F (Fv F v) δ := by rw [← map_mul, hbb', AlgHom.commutes]
    have hs0 : τ (b 1) ≠ 0 := (map_ne_zero τ).2 (b.ne_zero 1)
    have h20 : (2 : Fv F v) ≠ 0 := by
      rw [← map_ofNat (algebraMap F (Fv F v)) 2]
      exact (map_ne_zero _).2 two_ne_zero
    refine ⟨((u : Fv F v) + 1) / 2, ((u : Fv F v) - 1) / (2 * τ (b 1)), ?_⟩
    rw [← hs]
    field_simp
    ring
  · have hv2 : Valued.v (2 : Fv F v) = 1 := by
      have e : (2 : Fv F v) = algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) := by rw [map_ofNat, map_ofNat]
      rw [e]
      refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans ?_
      refine le_antisymm (v.valuation_le_one 2) (not_lt.1 fun h => (hB.inert v w hw).1 ?_)
      exact (v.valuation_lt_one_iff_mem 2).1 h
    have a1 : Valued.v (2 * (u : Fv F v)) ≤ 1 := h1
    have a2 : Valued.v (2 * ((u⁻¹ : (Fv F v)ˣ) : Fv F v)) ≤ 1 := h2
    rw [map_mul, hv2, one_mul] at a1 a2
    have hu : Valued.v (u : Fv F v) = 1 := by
      refine le_antisymm a1 ?_
      have hm := congrArg Valued.v u.mul_inv
      rw [map_mul, map_one] at hm
      rw [← hm]
      exact mul_le_of_le_one_right' a2
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.InertUnitNorm.unit_eq_mul_conj_k F E σ B hB v w hw (_root_.GlobalTheory.T.inert_completion_isField F E σ B hB v w hw) u hu
    obtain ⟨x, y, rfl⟩ := tensor_decomp (A := Fv F v) (b 1) (fun x => ⟨b.repr x 0, b.repr x 1, by
      have hx := b.sum_repr x
      rw [Fin.sum_univ_two, hb0] at hx
      exact hx.symm⟩) z
    refine ⟨x, y, tensor_inj (F := F) (E := E) ?_⟩
    have e1 : ((1 : Fv F v) ⊗ₜ[F] b 1) * ((1 : Fv F v) ⊗ₜ[F] b 1) =
        algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) δ) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hbb', ← IsScalarTower.algebraMap_apply,
        Algebra.TensorProduct.algebraMap_apply']
    rw [hz, map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hb1,
      TensorProduct.tmul_neg, map_sub, map_mul, map_pow, map_pow, ← e1]
    ring
end PositivityTheory.ThKW.Eta
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF Formalism.IndefR.LiftF
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeExtend GlobalTheory.HeckeExtend.AtInf GlobalTheory.SplitDetCharF
namespace PositivityTheory.ThKW.Eta
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem eta_fin_k {σ : E →ₐ[F] E} {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {η : (AF F ⊗[F] E)ˣ →* Circle} (hη : ResEtaF η 1)
    (a : (AF F)ˣ) (h1 : (idFF F E a : AF F ⊗[F] E) ∈ SE F E) (h2 : (idFF F E a⁻¹ : AF F ⊗[F] E) ∈ SE F E) :
    η (idFF F E (finU F (sndU F a))) = 1 := by
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := hB.cm.2.2.1 }
  have hint : ∀ t : AF F, algebraMap (AF F) (AF F ⊗[F] E) t ∈ SE F E → ∀ v : HeightOneSpectrum (𝓞 F),
      2 * t.2 v ∈ v.adicCompletionIntegers F := by
    intro t ht v
    have := GlobalTheory.T.finrank_smul_mem_adelesFiniteMultiple_of_tensorCongruence F E 1 t (CE_one ht)
    rw [hB.cm.2.2.1] at this
    obtain ⟨c, hc, e⟩ := this
    have e2 : evalV F v (2 • t.2) = evalV F v (1 • c) := congrArg (evalV F v) e
    rw [one_smul, map_nsmul, nsmul_eq_mul, Nat.cast_ofNat] at e2
    have e3 : 2 * t.2 v = c v := e2
    rw [e3]
    exact hc v
  have hn : finU F (sndU F a) ∈ GlobalTheory.QuadSymbol.normGroup F E (AF F) := by
    refine (GlobalTheory.IdeleNormChar.mem_normGroup_iff_everywhereNorm E _).2 ⟨fun v => ?_, fun w => ?_⟩
    · exact _root_.PositivityTheory.ThKW.Eta.local_norm_k hB v _ (hint _ h1 v) (hint _ h2 v)
    · have : GlobalTheory.IdeleNormChar.infComp (finU F (sndU F a)) w = 1 := Units.ext rfl
      rw [this]
      exact one_mem _
  obtain ⟨x, hx⟩ := hn
  obtain ⟨⟨η₀, h0⟩, h⟩ := hη
  rw [h η₀ h0, ← hx, h0.2.2.1 x, one_pow]
theorem key_k {σ : E →ₐ[F] E} {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {η : (AF F ⊗[F] E)ˣ →* Circle} (hc : Continuous η)
    (hη : ResEtaF η 1) : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ UI σ,
      x ∈ ((Units.map (incAF F E).toMonoidHom).range ⊔ (idFF F E).range) ⊔ WE F E N → η x = 1 := by
  obtain ⟨M, hM, hMk⟩ := exists_level η hc
  obtain ⟨N, hN, hNk⟩ := exists_sep B.v₁
  refine ⟨M * N, Nat.mul_pos hM hN, fun x hx hV => ?_⟩
  obtain ⟨y, hy, w, hw, hyw⟩ := Subgroup.mem_sup.1 hV
  obtain ⟨_, ⟨k, rfl⟩, _, ⟨a, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hy
  have hk := fixed_of_mem hB.cm B.τ₁ hNk hx hw k a hyw
  obtain ⟨f, hf⟩ := (GlobalTheory.T.cmExtension_conjugation_involutive_fixedField F E σ hB.cm).2 k hk
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact k.ne_zero hf.symm
  let fU : (AF F)ˣ := Units.map (algebraMap F (AF F)).toMonoidHom (Units.mk0 f hf0)
  have hinc : Units.map (incAF F E).toMonoidHom k = idFF F E fU := by
    apply Units.ext
    show incAF F E (k : E) = algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) f)
    rw [← hf, incAF_algebraMap]
  rw [hinc, ← map_mul] at hyw
  generalize fU * a = a' at hyw
  have e1 : idFF F E a' = x * w⁻¹ := by rw [← hyw, mul_inv_cancel_right]
  have e2 : idFF F E a'⁻¹ = x⁻¹ * w := by rw [map_inv, e1, mul_inv, inv_inv]
  have h1 := _root_.PositivityTheory.ThKW.Eta.eta_fin_k hB hη a' (by rw [e1]; exact SE_mul hx.2.2.1 (mem_SE_of_CE hw.2))
    (by rw [e2]; exact SE_mul hx.2.2.2 (mem_SE_of_CE hw.1))
  let p : (AF F ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ := Units.map (cut (fI F E) fI_idem)
  have hp : ∀ z : (AF F ⊗[F] E)ˣ, (p z : AF F ⊗[F] E) = (1 - fI F E) + fI F E * z := fun _ => rfl
  have px : p x = x := Units.ext (by
    have : (1 - fI F E) * (x : AF F ⊗[F] E) = 1 - fI F E := hx.1
    rw [hp]
    linear_combination -this)
  have pa : p (idFF F E a') = idFF F E (finU F (sndU F a')) := Units.ext (by
    rw [hp]
    show 1 - algebraMap (AF F) (AF F ⊗[F] E) (uFin F) + algebraMap (AF F) (AF F ⊗[F] E) (uFin F) *
      algebraMap (AF F) (AF F ⊗[F] E) (a' : AF F) = algebraMap (AF F) (AF F ⊗[F] E) (pairA F 1 (a' : AF F).2)
    rw [← map_mul, ← map_one (algebraMap (AF F) (AF F ⊗[F] E)), ← map_sub, ← map_add (f := _), uFin_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · show (1 : Ainf F) - 0 + 0 = 1
      simp
    · show (1 : Af F) - 1 + (a' : AF F).2 = (a' : AF F).2
      simp)
  have pC : ∀ z : (AF F ⊗[F] E)ˣ, (z : AF F ⊗[F] E) - 1 ∈ CE F E (M * N) → (p z : AF F ⊗[F] E) - 1 ∈ CE F E M := by
    intro z hz
    obtain ⟨s, hs, e⟩ := mem_CE.1 (CE_mul hz)
    refine mem_CE.2 ⟨fI F E * s, SE_mul fI_mem hs, ?_⟩
    rw [← mul_smul_comm, e, hp]
    ring
  have h2 : η (p w) = 1 := by
    refine hMk _ ⟨pC w hw.1, by rw [← map_inv]; exact pC _ hw.2⟩ ?_
    show (1 - fI F E) * (p w : AF F ⊗[F] E) = 1 - fI F E
    rw [hp]
    linear_combination (1 - (w : AF F ⊗[F] E)) * (fI_idem (F := F) (E := E))
  rw [← px, ← hyw, map_mul, map_mul, pa, h1, h2, mul_one]
end PositivityTheory.ThKW.Eta
namespace PositivityTheory.ThKW
open Eta
theorem exists_eta_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∃ η : (AF F ⊗[F] E)ˣ →* Circle,
      IsHeckeCharF η ∧ ResEtaF η 1 ∧ HasExp B.emb η (fun _ => 1) ∧ UnramInert σ η := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨η, h1, h2, h3⟩ := _root_.GlobalTheory.EtaCMType.exists_eta_cmType_k F E σ B hB
  obtain ⟨N, hN, hk⟩ := _root_.PositivityTheory.ThKW.Eta.key_k hB h1.1 h2
  obtain ⟨ν, hV, hU⟩ := exists_ext _ _ η hk
  have hW : ∀ z ∈ WE F E N, ν z = 1 := fun z hz => hV z (Subgroup.mem_sup_right hz)
  have hWo : IsOpen (WE F E N : Set (AF F ⊗[F] E)ˣ) := by
    have ho := CE_isOpen F E N hN
    have hcv : Continuous fun z : (AF F ⊗[F] E)ˣ => (z : AF F ⊗[F] E) - 1 :=
      Units.continuous_val.sub continuous_const
    have hci : Continuous fun z : (AF F ⊗[F] E)ˣ => ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 :=
      Units.continuous_coe_inv.sub continuous_const
    exact (ho.preimage hcv).inter (ho.preimage hci)
  have hν : Continuous ν := by
    refine continuous_of_continuousAt_one _ ?_
    unfold ContinuousAt
    rw [map_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hWo.mem_nhds (one_mem _)] with z hz
    exact (hW z hz).symm
  refine ⟨η * ν⁻¹, ⟨h1.1.mul hν.inv, fun x => ?_⟩, ⟨h2.1, fun e he a => ?_⟩, fun z hz => ?_, fun x a b c d => ?_⟩
  · change η _ * (ν _)⁻¹ = 1
    rw [h1.2, hV _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨x, rfl⟩)), inv_one, one_mul]
  · change η _ * (ν _)⁻¹ = _
    rw [h2.2 e he, hV _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨a, rfl⟩)), inv_one, mul_one]
  · change ((η z * (ν z)⁻¹ : Circle) : ℂ) = _
    have : z ∈ WE F E N := by
      refine ⟨mem_CE_of_atInf F E _ hN _ hz, mem_CE_of_atInf F E _ hN _ ?_⟩
      intro u hu
      have e : ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 =
          -(((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((z : AF F ⊗[F] E) - 1)) := by
        rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
      rw [e, smul_neg, ← mul_smul_comm, hz u hu, mul_zero, neg_zero]
    rw [hW z this, inv_one, mul_one]
    exact h3 z hz
  · change η _ * (ν _)⁻¹ = 1
    have hx : x ∈ UI σ := by
      refine ⟨?_, b, mem_SE_of_fin c, mem_SE_of_fin d⟩
      show (1 - fI F E) * (x : AF F ⊗[F] E) = 1 - fI F E
      rw [← sub_eq_zero, ← mul_sub_one]
      refine adele_tensor_ext _ ?_ ?_
      · rw [map_mul, map_sub _ (x : AF F ⊗[F] E), a, map_one, sub_self, mul_zero]
      · rw [map_mul, map_sub, map_one, fin_fI, sub_self, zero_mul]
    rw [hU x hx, mul_inv_cancel]
end PositivityTheory.ThKW
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilDatumSplittingCharacters
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsWeilDatumOFTwistK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.WeilTwistF
open MeasureTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
end GlobalTheory.WeilTwistF
namespace GlobalTheory.WeilTwistF
open MeasureTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
end GlobalTheory.WeilTwistF
namespace GlobalTheory.WeilTwistF
open MeasureTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
theorem exists_weilDatumOF_twist_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT νS νT : (AF F ⊗[F] E)ˣ →* Circle) ω,
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        IsHeckeCharF νS → IsHeckeCharF νT → ResEtaF νS 0 → ResEtaF νT 0 →
        ∃ ω', IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (χS * νS) (χT * νT) ω' := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ χS χT νS νT om ho hνS hνT rS rT
  have hcm := hB.cm
  have hun := hB.unram
  obtain ⟨a, aval, arat, acont⟩ := exists_muF (σ := σ) hcm hun hS.2 νT⁻¹ (heckeF_inv hνT)
    (fun t => by rw [MonoidHom.inv_apply, triv_of_resEtaF rT, inv_one])
  obtain ⟨b, bval, brat, bcont⟩ := exists_muF (σ := σ) hcm hun hT.2 νS hνS (triv_of_resEtaF rS)
  let om' : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ) :=
    { toFun := fun p => ((a p.1 * b p.2 : Circle) : ℂ) • om p
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul, smul_mul_smul_comm, Circle.coe_mul]
        congr 1
        ring }
  have happ : ∀ p f, om' p f = ((a p.1 * b p.2 : Circle) : ℂ) • om p f := fun p f => rfl
  have hval : ∀ g h x y, IsRootF σ JS g x → IsRootF σ JT h y →
      ((a g * b h : Circle) : ℂ) = (((νT x)⁻¹ * νS y : Circle) : ℂ) := by
    intro g h x y hx hy
    rw [aval g x hx, bval h y hy, MonoidHom.inv_apply]
  refine ⟨om', ⟨ho.std, heckeF_mul ho.hecS hνS, heckeF_mul ho.hecT hνT, resEtaF_mul ho.resS rS,
    resEtaF_mul ho.resT rT, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro p f hf
    rw [happ]
    exact thetaOF_smul _ (ho.om_pres p f hf)
  · intro g h w₀ f hf
    rw [happ, happ, heisOF_smul, ho.om_heis g h w₀ f hf]
  · intro γ hγ γ' hγ' f hf
    rw [happ]
    change ((a γ * b γ' : Circle) : ℂ) * om (γ, γ') f 0 = f 0
    rw [arat γ hγ, brat γ' hγ', mul_one, Circle.coe_one, one_mul]
    exact ho.om_aut γ hγ γ' hγ' f hf
  · intro f hf w
    exact (continuous_subtype_val.comp ((acont.comp continuous_fst).mul (bcont.comp continuous_snd))).mul
      (ho.om_cont f hf w)
  · intro μ 𝓕 hμ h𝓕 p f hf
    rw [← ho.om_unit μ 𝓕 hμ h𝓕 p f hf]
    refine lintegral_congr fun w => ?_
    have hn : ‖om' p f w‖ = ‖om p f w‖ := by
      rw [happ, Pi.smul_apply, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
    rw [← ofReal_norm, ← ofReal_norm, hn]
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := ho.om_split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    rw [happ, map_smul, H ℓ hℓ f hf,
      hval g h x y (root_of_detAt hS.2 he g hg x hx) (root_of_detAt hT.2 he h hh y hy)]
    simp only [splitFacOF, MonoidHom.mul_apply, mul_inv, Circle.coe_mul, smul_eq_mul]
    ring
end GlobalTheory.WeilTwistF
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_datum_splitting_characters : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT νS νT : (AF F ⊗[F] E)ˣ →* Circle) ω,
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        IsHeckeCharF νS → IsHeckeCharF νT → ResEtaF νS 0 → ResEtaF νT 0 →
        ∃ ω', IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (χS * νS) (χT * νT) ω' := by
  first | exact @_root_.GlobalTheory.WeilTwistF.exists_weilDatumOF_twist_k | exact _root_.GlobalTheory.WeilTwistF.exists_weilDatumOF_twist_k | (intros; apply _root_.GlobalTheory.WeilTwistF.exists_weilDatumOF_twist_k <;> assumption)
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
namespace PositivityTheory.ThKW.S
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem exists_isWeilDatumOF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → PositivityTheory.ThKW.LatH σ JS JT ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∃ ω, Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ hLat χS χT hcS hcT rS rT
  obtain ⟨η, hη1, hη2, hη3, hη4⟩ := _root_.PositivityTheory.ThKW.exists_eta_k F E σ B hB
  obtain ⟨Λ, hΛ1, hΛ2⟩ := hLat
  have hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ := _root_.GlobalTheory.T.theta_function_heisenberg_translate F E σ B hB nS nT JS JT ξ₀
  obtain ⟨w, lam, Om, hO⟩ := _root_.UpperTheory.TP.W.latK F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ Λ hΛ1 hΛ2 hc
  obtain ⟨om, hom⟩ := _root_.UpperTheory.TP.W.datumK_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ Λ hΛ1 hΛ2 hc w lam Om hO η hη1 hη2 hη3 hη4
  obtain ⟨om', hom'⟩ := _root_.GlobalTheory.T.weil_datum_splitting_characters F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ _ _ ((η ^ nS)⁻¹ * χS) ((η ^ nT)⁻¹ * χT) om hom
    (isHeckeCharF_div_pow hcS hη1 _) (isHeckeCharF_div_pow hcT hη1 _)
    (resEtaF_div_pow rS hη2) (resEtaF_div_pow rT hη2)
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at hom'
  exact ⟨om', hom'⟩
end PositivityTheory.ThKW.S
end
