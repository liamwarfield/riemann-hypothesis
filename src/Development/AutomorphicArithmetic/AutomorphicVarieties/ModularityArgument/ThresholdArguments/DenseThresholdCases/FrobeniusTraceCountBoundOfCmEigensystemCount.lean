module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.IntPHolds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PseudoLocalLanglandsDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SharedDedup_Dual_conj

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SatK
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Af.satake_k_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.SatK := by
  intro P K _ _ _ n M π hπ w hw
  obtain ⟨⟨σ, hσ⟩, h⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
  exact sat_of_isotypic (_root_.UpperTheory.V.Af.satake_local_of_printed_results P) π.finPart hπ w hw σ (h σ hσ)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IntFinal
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.Int
theorem intP'_alt : _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Br.IntP := fun _ => intP_holds
theorem intK_of_prints : _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.IntK := fun _ => intK_holds
end UpperTheory.V.Z.Int
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VConjP
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
private theorem regAlg_of_infOf {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {m : Fin n → ℤ}
    (hm : StrictAnti m) {π : CuspSub K n} (h : ∀ τ, π.HasInfChar τ (infOf m)) : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  rw [CG.HasInfChar.infChar_eq (π := CG.mk π) (h τ)]
  refine ⟨Multiset.Nodup.map (fun i j e => hm.injective ?_) Finset.univ.nodup, fun z hz => ?_⟩
  · exact_mod_cast add_left_cancel e
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, add_comm _ _⟩
private theorem eventually_notMem {K : Type} [Field K] [NumberField K] {M : ℕ} (hM : 1 ≤ M) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (M : 𝓞 K) ∉ w.asIdeal := by
  have h0 : Ideal.span {(M : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 (not_not.1 hw)
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem normV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    normV (cPl w) = normV w := by
  have e : (cPl w).asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv) :=
    (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_congr (Ideal.quotientEquiv _ _
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv).symm ?_).toEquiv).symm
  rw [e]
  exact (Ideal.map_symm _).symm
private theorem eventually_unr {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (χ : HChar F) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, χ.UnrAt (w.under (𝓞 F)) := by
  rw [Filter.eventually_cofinite]
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified χ).preimage' (f := fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 F))
    fun v _ => ?_).subset fun w hw => hw
  haveI := v.isMaximal
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)).preimage
    (f := fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) fun _ _ _ _ e => HeightOneSpectrum.ext e).subset fun w hw => ?_
  exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal (Eq.symm hw)⟩⟩
private theorem dual_conj {n q : ℕ} (hn : 1 ≤ n) (hq : q ≠ 0) (σ : ℂ ≃+* ℂ) {B B₁ B' B₁' : Multiset ℂˣ} {z z' : ℂˣ}
    (hz : (z' : ℂ) = σ z) (h : B₁.map (·⁻¹) = B.map (· * z⁻¹)) (e : algSat n q B' = (algSat n q B).map σ)
    (e₁ : algSat n q B₁' = (algSat n q B₁).map σ) : B₁'.map (·⁻¹) = B'.map (· * z'⁻¹) := _root_.DedupShared.dedup_dual_conj_3 (n := n) (q := q) (B := B) (B₁ := B₁) (B' := B') (B₁' := B₁') (z := z) (z' := z') hn hq σ hz h e e₁
theorem UpperTheory.GalN.V.conjP_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Br.ConjP := by
  intro P K _ _ _ hK n hn m hm M hM σ π ⟨hinf, ⟨χ, hpol⟩, hfix⟩
  have hreg := regAlg_of_infOf hm hinf
  obtain ⟨π', τ, τ', h1, h2, h3, h4⟩ := P.conjC K n (by omega) π hreg σ
  obtain ⟨hs, hs'⟩ := sep_of_conj h1 h2 h3
  have hsat : ∀ w B, (CG.mk π).HasSat w B →
      ∃ B', (CG.mk π').HasSat w B' ∧ algSat n (normV w) B' = (algSat n (normV w) B).map σ :=
    fun w B hB => (hs.comp _).exists_hasSatGL (hs'.comp _) hB
  refine ⟨π', ⟨fun φ => ?_, ?_, hs.hasFixed hfix⟩, hsat⟩
  · have e : σ.toRingHom.comp (σ.symm.toRingHom.comp φ) = φ := RingHom.ext fun x => σ.apply_symm_apply _
    exact e ▸ h4 _ _ (hinf _)
  obtain ⟨a, ha⟩ := GlobalTheory.T.isAlgebraicHeckeChar_of_regularAlgebraic_polarizedPair K n (by omega) π χ hreg hpol
  have hF : Module.finrank ℚ (maximalRealSubfield K) = 1 := by
    have h1 := (letI : Module.Free (maximalRealSubfield K) K := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K] at h1
    omega
  obtain ⟨χ', hsg, hv⟩ := UpperTheory.V.Br.charConj _ hF χ a ha σ
  refine ⟨χ', fun v => (hsg v).trans (hpol.sign v),
    UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse P.litN.aut.js.1 P.litN.aut.gk K n (by omega) π' _ ?_⟩
  have hM1 := eventually_notMem (K := K) hM
  filter_upwards [eventually_unr (K := K) χ, hM1,
    (conjSrc_injective (IsCMField.complexConj K).toRingEquiv).tendsto_cofinite.eventually hM1] with w hw a1 a2
  obtain ⟨B, hB⟩ := _root_.UpperTheory.V.Af.satake_k_of_printed_results P K n M π hfix w a1
  obtain ⟨B₁, hB₁⟩ := _root_.UpperTheory.V.Af.satake_k_of_printed_results P K n M π hfix (cPl w) a2
  obtain ⟨B', hB', e⟩ := hsat w B hB
  obtain ⟨B₁', hB₁', e₁⟩ := hsat _ B₁ hB₁
  rw [normV_cPl] at e₁
  obtain ⟨e3, e4⟩ := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility K χ w _ (normV_under w) hw
  obtain ⟨e5, e6⟩ := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility K χ' w _ (normV_under w) (hv _ hw).1
  refine ⟨e5, B', B₁', hB', hB₁', dual_conj (by omega) (GlobalTheory.WeilDeligne.one_lt_normV w).ne_bot σ ?_
    (UpperTheory.V.Br.satOfPol K n π _ hpol.dual w e3 B B₁ hB hB₁) e e₁⟩
  rw [e4, e6, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, (hv _ hw).2]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TConjK
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep

noncomputable section

namespace TConjKDualProof

open Matrix GlobalTheory.ContraPair

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

private def phiOp (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) : Module.End ℂ (Sm L a) :=
  act (.fin (PhiU a (Af L))) * act (.cpt (PhiK L a))

private theorem barK_barK (k : Kinf L a) : barK (barK k) = k := Subtype.ext (by
  ext i j : 1
  exact star_star _)

private theorem fin_cpt (k : GL (Fin a) (Af L)) (u : Kinf L a) :
    act (.cpt u) * act (.fin k) = act (.fin k) * act (Op.cpt u : Op L a) := by
  change rt L a _ * rt L a _ = rt L a _ * rt L a _
  rw [← map_mul, ← map_mul]
  exact congrArg _ (infGL_comm _ _)

private theorem phiOp_mul (o : Op L a) : phiOp L a * act (invTOp (conjOp o)) = act (thetaOp o) * phiOp L a := by
  cases o with
  | fin k =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    rw [mul_assoc, fin_cpt, ← mul_assoc, ← mul_assoc]
    congr 1
    change finRep L a _ * finRep L a _ = finRep L a _ * finRep L a _
    rw [← map_mul, ← map_mul]
    congr 1
    change _ = PhiU a (Af L) * _ * (PhiU a (Af L))⁻¹ * _
    rw [inv_mul_cancel_right]
    rfl
  | cpt k =>
    simp only [phiOp, conjOp, invTOp, thetaOp, barK_barK]
    rw [← mul_assoc, fin_cpt, mul_assoc, mul_assoc]
    congr 1
    change cptRep L a _ * cptRep L a _ = cptRep L a _ * cptRep L a _
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  | lie X =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    have h1 := GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits (PhiK L a)) (-(Matrix.of X)ᴴ)
    have h2 := lie_rt_fin (E := L) (toL (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ)))
      (PhiU a (Af L))
    have e : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl
    have e2 : (Unitary.toUnits (PhiK L a)).val * (-(Matrix.of X)ᴴ) * ((Unitary.toUnits (PhiK L a))⁻¹).val =
        -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ) := by
      rw [e, mul_neg, neg_mul]; rfl
    rw [e2] at h1
    rw [mul_assoc, ← mul_assoc (act (Op.lie _))]
    exact (congrArg (act (.fin (PhiU a (Af L))) * ·) h1).trans ((mul_assoc _ _ _).symm.trans
      (congrArg (· * _) h2.symm))

private theorem dualIsConj_of_isCsd {π : CuspSub L a} (h : Paired π π invTOp) (hc : π.IsCsd) : DualIsConj π := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨T, hT⟩ := hc
  let P : Module.End ℂ π.V := π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a))
  let Q : Module.End ℂ π.V := π.op (.cpt (PhiK L a)⁻¹) * π.op (.fin (PhiU a (Af L))⁻¹)
  have f1 : ∀ k k' : GL (Fin a) (Af L), k * k' = 1 → ∀ φ, π.op (.fin k) (π.op (.fin k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (finRep L a k * finRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  have f2 : ∀ k k' : Kinf L a, k * k' = 1 → ∀ φ, π.op (.cpt k) (π.op (.cpt k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (cptRep L a k * cptRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  let Pe : π.V ≃ₗ[ℂ] π.V := LinearEquiv.ofLinear P Q
    (LinearMap.ext fun φ => by simp [P, Q, f1, f2]) (LinearMap.ext fun φ => by simp [P, Q, f1, f2])
  let S := Pe.trans T
  have hS : ∀ o φ, S (π.op (invTOp (conjOp o)) φ) = π.op o (S φ) := fun o φ => by
    change T _ = π.op o (T _)
    rw [← hT]
    exact congrArg T (Subtype.ext (LinearMap.congr_fun (phiOp_mul o) φ.1))
  have hS' : ∀ o φ, S.symm (π.op o φ) = π.op (invTOp (conjOp o)) (S.symm φ) := fun o φ => by
    rw [LinearEquiv.symm_apply_eq, hS, LinearEquiv.apply_symm_apply]
  refine ⟨B.flip ∘ₗ S.symm.toLinearMap, fun φ h => ?_, fun ψ h => h1 ψ fun x => ?_, fun k φ ψ => ?_, fun k φ ψ => ?_,
    fun X φ ψ => ?_⟩
  · exact (map_eq_zero_iff _ S.symm.injective).1 (h2 _ h)
  · simpa using h (S x)
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h3 _ _ _
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h4 _ _ _
  · change B _ (S.symm _) + B _ (S.symm _) = 0
    rw [hS', add_comm]; exact h5 _ _ _

end TConjKDualProof

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.ThetaPull
namespace UpperTheory.V.Af
private theorem regAlg_of_infOf {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {m : Fin n → ℤ}
    (hm : StrictAnti m) {π : CuspSub K n} (h : ∀ τ, π.HasInfChar τ (infOf m)) : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  rw [CG.HasInfChar.infChar_eq (π := CG.mk π) (h τ)]
  refine ⟨Multiset.Nodup.map (fun i j e => hm.injective ?_) Finset.univ.nodup, fun z hz => ?_⟩
  · exact_mod_cast add_left_cancel e
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, add_comm _ _⟩
private theorem eventually_notMem {K : Type} [Field K] [NumberField K] {M : ℕ} (hM : 1 ≤ M) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (M : 𝓞 K) ∉ w.asIdeal := by
  have h0 : Ideal.span {(M : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 (not_not.1 hw)
private theorem sep_theta {K : Type} [Field K] [NumberField K] [IsCMField K] {n : ℕ} {π π' : CuspSub K n} {σ : ℂ ≃+* ℂ}
    (hc : π.IsCsd) (h : Sep σ π.finPart π'.finPart) (h' : Sep σ.symm π'.finPart π.finPart) :
    Sep (RingEquiv.refl ℂ) π'.finPart (thetaSub π').finPart ∧ Sep (RingEquiv.refl ℂ) (thetaSub π').finPart π'.finPart := by
  obtain ⟨T, hT⟩ := hc
  have h1 := Sep.of_equiv (ρ := π.finPart.comp (thetaGL n (cFin K))) (ρ' := π.finPart) T fun g v => hT (.fin g) v
  have h2 := Sep.of_equiv (ρ := π'.finPart.comp (thetaGL n (cFin K))) (ρ' := (thetaSub π').finPart)
    ((pull K n).submoduleMap π'.V) fun g v => Subtype.ext (act_pull (.fin g) v.1).symm
  have e : σ.symm.trans σ = RingEquiv.refl ℂ := σ.symm_trans_self
  exact ⟨e ▸ ((h'.trans h1.2).trans (h.comp _)).trans h2.1, e ▸ ((h2.2.trans (h'.comp _)).trans h1.1).trans h⟩
end UpperTheory.V.Af
open UpperTheory.V.Af in
theorem UpperTheory.V.Af.conjK_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.ConjK := by
  intro P K _ _ _ n hn m hm M hM σ π ⟨hinf, hdual, hfix⟩
  obtain ⟨π', τ, τ', h1, h2, h3, h4⟩ := P.conjC K n (by omega) π (regAlg_of_infOf hm hinf) σ
  obtain ⟨hs, hs'⟩ := sep_of_conj h1 h2 h3
  have hfix' := hs.hasFixed hfix
  refine ⟨π', ⟨fun φ => ?_, ?_, hfix'⟩, fun w B hB => (hs.comp _).exists_hasSatGL (hs'.comp _) hB⟩
  · have e : σ.toRingHom.comp (σ.symm.toRingHom.comp φ) = φ := RingHom.ext fun x => σ.apply_symm_apply _
    exact e ▸ h4 _ _ (hinf _)
  · obtain ⟨ht, ht'⟩ := sep_theta (GlobalTheory.CsdBack.isCsd_of_paired P.litN.aut.fin K n π (P.litN.aut.gk K n π) hdual) hs hs'
    refine TConjKDualProof.dualIsConj_of_isCsd (P.litN.aut.gk K n π') (isCsd_of_iso (Quotient.exact
      (P.litN.aut.js.1.strong_multiplicity_one (by omega) (CG.mk (thetaSub π')) (CG.mk π') (by
        refine (eventually_notMem hM).mono fun w hw => ?_
        obtain ⟨B, hB⟩ := _root_.UpperTheory.V.Af.satake_k_of_printed_results P K n M π' hfix' w hw
        exact ⟨B, (ht.comp _).hasSatGL_refl (ht'.comp _) hB, hB⟩))))
end

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BrCardP
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
private theorem klev_three (K : Type) [Field K] [NumberField K] (n M : ℕ) :
    UpperTheory.V.Af.KLev K n (3 * M) ≤ UpperTheory.V.Af.KLev K n M := by
  refine Subgroup.map_mono fun k hk => ?_
  have hle : Ideal.span {((3 * M : ℕ) : ↥(UpperTheory.V.Af.Ohat K))} ≤ Ideal.span {(M : ↥(UpperTheory.V.Af.Ohat K))} :=
    Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast (Dvd.intro_left 3 rfl))
  have e := congrArg (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.factor hle)) (MonoidHom.mem_ker.1 hk)
  rw [map_one] at e
  exact e
theorem UpperTheory.V.Br.cardP_of_prints :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Br.CardP := by
  intro P K _ _ _ n hn
  obtain ⟨c₁, A₁, hW⟩ := _root_.UpperTheory.V.Af.weyl_complex_of_printed_results P K n
  obtain ⟨c₂, A₂, hC⟩ := UpperTheory.V.Af.cohBoundFree K (Or.inl inferInstance) n ⊤ inferInstance
  refine ⟨c₂ * c₁, A₁ + A₂, fun m hm H hH M hM S hS hiso => ?_⟩
  obtain ⟨Ξ, hΞ, hd⟩ := hW m hm H hH
  have h3 : 1 ≤ 3 * M := by omega
  have hB := P.borelC K n (by omega) (UpperTheory.V.Af.KLev K n (3 * M)) (by apply UpperTheory.V.Af.isOpen_KLev; exact h3)
    (by apply UpperTheory.V.Af.isCompact_KLev; exact h3) Ξ S hiso fun π hπ =>
      ⟨P.cohC K n (by omega) π Ξ fun τ => ⟨_, (hS π hπ).1 τ, hΞ τ⟩,
        (hS π hπ).2.2.imp fun _ hv => ⟨hv.1, fun u hu => hv.2 u (klev_three K n M hu)⟩⟩
  have h1 : S.card ≤ c₂ * M ^ A₂ * Ξ.d := Nat.cast_le.1 (hB.trans (hC M hM _ _))
  have h2 : M ^ A₂ ≤ M ^ (A₁ + A₂) := Nat.pow_le_pow_right hM (by omega)
  have h4 : (H + 1) ^ A₁ ≤ (H + 1) ^ (A₁ + A₂) := Nat.pow_le_pow_right (by omega) (by omega)
  calc S.card ≤ c₂ * M ^ A₂ * Ξ.d := h1
    _ ≤ c₂ * M ^ (A₁ + A₂) * (c₁ * (H + 1) ^ (A₁ + A₂)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) (hd.trans (Nat.mul_le_mul_left _ h4))
    _ = c₂ * c₁ * (M * (H + 1)) ^ (A₁ + A₂) := by rw [mul_pow]; ring
end
end

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br
open Neutral.B1 hiding G IsPlaceOver
namespace UpperTheory.GalN.V.Win.N
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp
open scoped Matrix
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.V.Af.Bc
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br
def CountKAlt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ), StrictAnti m → (∀ i, m i + m i.rev = 1 - n) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ¬ (p : ℤ) ∣ discr K →
      ∃ D : EigData n (normV w) m (1 - n), Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (_root_.UpperTheory.GalN.V.AdmKNAlt ι M m)
def CountQAlt : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → (∀ i, m i + m i.rev = wt) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)), p.Prime → (p : 𝓞 ℚ) ∈ w.asIdeal → ¬ p ∣ M →
      ∃ D : EigData n p m wt, Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (_root_.UpperTheory.GalN.V.AdmRNAlt ι M m wt)
def CountPAlt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → (∀ i, m i + m i.rev = wt) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ¬ (p : ℤ) ∣ discr K →
      ∃ D : EigData n (normV w) m wt, Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (_root_.UpperTheory.GalN.V.AdmPNAlt ι M m)
def NewAdmAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e M : ℕ), 1 ≤ e →
    ∀ W : G ℚ Ω →* GL (Fin 2) (Qbar l), IsIrr W →
    ((∃ f : Newform (2 * e + 1), f.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ _root_.UpperTheory.V.Z.Win.WitAQ ι W) →
    Level l M ![(e : ℤ), -(e : ℤ)] W → IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) → _root_.UpperTheory.GalN.V.AdmRNAlt ι M ![(e : ℤ), -(e : ℤ)] 0 W
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.CuspRep UpperTheory.V.Af in
theorem countK_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.GalN.V.LevelKNAlt → _root_.UpperTheory.GalN.V.Win.N.CountKAlt := by
  intro hP hL K _ _ _ n hn
  classical
  obtain ⟨c, A, hcard⟩ := _root_.UpperTheory.V.Af.card_k_of_printed_results hP K n hn
  refine ⟨c, A, fun m hm hwt H hH M hM p w hp hw hpM hpd => ?_⟩
  have hwM : (M : 𝓞 K) ∉ w.asIdeal := natCast_notMem_of_not_dvd hp hw hpM
  let Wd := {v : HeightOneSpectrum (𝓞 K) // (M : 𝓞 K) ∉ v.asIdeal}
  let sys : CuspSub K n → Wd → Multiset ℂ := fun π v =>
    if h : ∃ B, (CG.mk π).HasSat v.1 B then algSat n (normV v.1) h.choose else 0
  have hsys : ∀ π (v : Wd) B, (CG.mk π).HasSat v.1 B → sys π v = algSat n (normV v.1) B := by
    intro π v B hB
    have h : ∃ B, (CG.mk π).HasSat v.1 B := ⟨B, hB⟩
    simp only [sys, dif_pos h]
    rw [h.choose_spec.unique hB]
  have hsat : ∀ π ∈ SigK K m M, ∀ v : Wd, ∃ B, (CG.mk π).HasSat v.1 B := fun π hπ v =>
    _root_.UpperTheory.V.Af.satake_k_of_printed_results hP K n M π hπ.2.2 v.1 v.2
  obtain ⟨D, hD, cl, hcl, hβ⟩ := exists_eigData (SigK K m M) (fun π π' => π.Iso π') sys
    (fun π hπ π' _ h => funext fun v => by
      obtain ⟨B, hB⟩ := hsat π hπ v
      rw [hsys π v B hB, hsys π' v B (CuspSub.Iso.hasSatGL h hB)])
    (c * (M * (H + 1)) ^ A) (hcard m hm H hH M hM)
    (fun σ π hπ => by
      obtain ⟨π', hπ', h⟩ := _root_.UpperTheory.V.Af.conjK_alt hP K n hn m hm M hM σ π hπ
      refine ⟨π', hπ', fun v => ?_⟩
      obtain ⟨B, hB⟩ := hsat π hπ v
      obtain ⟨B', hB', e⟩ := h v.1 B hB
      rw [hsys π v B hB, hsys π' v B' hB', e])
    ⟨w, hwM⟩ (n := n) (q := normV w) (m := m) (wt := 1 - n)
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB, algSat, Multiset.card_map, ← hB.card]
      simp)
    (by
      rw [normV, ← Ideal.absNorm_eq_natCard]
      exact zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w))
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB]
      exact win_algSat (by omega) π m _ hwt hπ.1 hB)
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB]
      exact _root_.UpperTheory.V.Z.Int.intK_of_prints hP K n hn m hm M hM π hπ p w hp hw hpM hpd B hB)
  refine ⟨D, hD, fun l hl hl2 hlp Ω _ _ _ ι => ?_⟩
  have hform : ∀ r : {r : G K Ω →* GL (Fin n) (Qbar l) // _root_.UpperTheory.GalN.V.AdmKNAlt ι M m r}, ∃ π : ↥(SigK K m M), IsSSRep r.1 ∧
      ∀ v : Wd, (l : 𝓞 K) ∉ v.1.asIdeal → FrobEig ι r.1 v.1 (sys π v) := by
    intro r
    obtain ⟨π, h1, h2, h3⟩ := r.2.aut.1
    obtain ⟨hπ, hF⟩ := hL K n hn m hm M hM l hl2 Ω ι r.1 π r.2.level r.2.odd (r.2.aut.2 r.2.level.cont) h1 h2 h3
    refine ⟨⟨π, hπ⟩, h3.1, fun v hv => ?_⟩
    obtain ⟨B, hB⟩ := hsat π hπ v
    rw [hsys π v B hB]
    exact hF v.1 hv B hB
  choose f hss hf using hform
  refine ⟨fun r => cl (f r), fun r r' h => ?_, fun r => ?_⟩
  · refine _root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results hP K Ω l ι n r.1 r'.1 r.2.level.cont r'.2.level.cont (hss r) (hss r') ?_
    filter_upwards [eventually_natCast_notMem (F := K) (M := M) (by omega),
      eventually_natCast_notMem (F := K) hl.out.ne_zero] with v hvM hvl
    refine ⟨sys (f r) ⟨v, hvM⟩, hf r ⟨v, hvM⟩ hvl, ?_⟩
    rw [hcl _ _ h]
    exact hf r' ⟨v, hvM⟩ hvl
  · rw [hβ]
    refine hf r ⟨w, hwM⟩ (natCast_notMem_of_not_dvd hp hw fun h => hlp ?_)
    exact ((Nat.prime_dvd_prime_iff_eq hp hl.out).1 h).symm
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.CuspRep UpperTheory.V.Af in
theorem countP_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.GalN.V.LevelPNAlt → _root_.UpperTheory.GalN.V.Win.N.CountPAlt := by
  intro hP hL K _ _ _ hK n hn
  classical
  obtain ⟨c, A, hcard⟩ := _root_.UpperTheory.V.Br.cardP_of_prints hP K n hn
  refine ⟨c, A, fun m wt hm hwt H hH M hM p w hp hw hpM hpd => ?_⟩
  have hwM : (M : 𝓞 K) ∉ w.asIdeal := natCast_notMem_of_not_dvd hp hw hpM
  let Wd := {v : HeightOneSpectrum (𝓞 K) // (M : 𝓞 K) ∉ v.asIdeal}
  let sys : CuspSub K n → Wd → Multiset ℂ := fun π v =>
    if h : ∃ B, (CG.mk π).HasSat v.1 B then algSat n (normV v.1) h.choose else 0
  have hsys : ∀ π (v : Wd) B, (CG.mk π).HasSat v.1 B → sys π v = algSat n (normV v.1) B := by
    intro π v B hB
    have h : ∃ B, (CG.mk π).HasSat v.1 B := ⟨B, hB⟩
    simp only [sys, dif_pos h]
    rw [h.choose_spec.unique hB]
  have hsat : ∀ π ∈ SigP K m M, ∀ v : Wd, ∃ B, (CG.mk π).HasSat v.1 B := fun π hπ v =>
    _root_.UpperTheory.V.Af.satake_k_of_printed_results hP K n M π hπ.2.2 v.1 v.2
  obtain ⟨D, hD, cl, hcl, hβ⟩ := exists_eigData (SigP K m M) (fun π π' => π.Iso π') sys
    (fun π hπ π' _ h => funext fun v => by
      obtain ⟨B, hB⟩ := hsat π hπ v
      rw [hsys π v B hB, hsys π' v B (CuspSub.Iso.hasSatGL h hB)])
    (c * (M * (H + 1)) ^ A) (hcard m hm H hH M hM)
    (fun σ π hπ => by
      obtain ⟨π', hπ', h⟩ := _root_.UpperTheory.GalN.V.conjP_alt hP K hK n hn m hm M hM σ π hπ
      refine ⟨π', hπ', fun v => ?_⟩
      obtain ⟨B, hB⟩ := hsat π hπ v
      obtain ⟨B', hB', e⟩ := h v.1 B hB
      rw [hsys π v B hB, hsys π' v B' hB', e])
    ⟨w, hwM⟩ (n := n) (q := normV w) (m := m) (wt := wt)
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB, algSat, Multiset.card_map, ← hB.card]
      simp)
    (by
      rw [normV, ← Ideal.absNorm_eq_natCard]
      exact zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w))
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB]
      exact win_algSat (by omega) π m _ hwt hπ.1 hB)
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB]
      exact _root_.UpperTheory.V.Z.Int.intP'_alt hP K n hn m hm M hM π hπ p w hp hw hpM hpd B hB)
  refine ⟨D, hD, fun l hl hl2 hlp Ω _ _ _ ι => ?_⟩
  have hform : ∀ r : {r : G K Ω →* GL (Fin n) (Qbar l) // _root_.UpperTheory.GalN.V.AdmPNAlt ι M m r}, ∃ π : ↥(SigP K m M), IsSSRep r.1 ∧
      ∀ v : Wd, (l : 𝓞 K) ∉ v.1.asIdeal → FrobEig ι r.1 v.1 (sys π v) := by
    intro r
    obtain ⟨π, h1, h2, h3⟩ := r.2.aut
    obtain ⟨hπ, hF⟩ := hL K hK n hn m hm M hM l hl2 Ω ι r.1 π r.2.level r.2.safe r.2.unl h1 h2 h3
    refine ⟨⟨π, hπ⟩, h3.1, fun v hv => ?_⟩
    obtain ⟨B, hB⟩ := hsat π hπ v
    rw [hsys π v B hB]
    exact hF v.1 hv B hB
  choose f hss hf using hform
  refine ⟨fun r => cl (f r), fun r r' h => ?_, fun r => ?_⟩
  · refine _root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results hP K Ω l ι n r.1 r'.1 r.2.level.cont r'.2.level.cont (hss r) (hss r') ?_
    filter_upwards [eventually_natCast_notMem (F := K) (M := M) (by omega),
      eventually_natCast_notMem (F := K) hl.out.ne_zero] with v hvM hvl
    refine ⟨sys (f r) ⟨v, hvM⟩, hf r ⟨v, hvM⟩ hvl, ?_⟩
    rw [hcl _ _ h]
    exact hf r' ⟨v, hvM⟩ hvl
  · rw [hβ]
    refine hf r ⟨w, hwM⟩ (natCast_notMem_of_not_dvd hp hw fun h => hlp ?_)
    exact ((Nat.prime_dvd_prime_iff_eq hp hl.out).1 h).symm
end
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
  UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Br
private theorem bit_of_fibre {X U : Type} (R : X → X → Prop) (hs : ∀ x y, R x y → R y x)
    (ht : ∀ x y z, R x y → R y z → R x z) (Q : X → U → Prop) (hQ : ∀ x, ∃ u, Q x u)
    (h2 : ∀ u x₀ x x', Q x₀ u → Q x u → Q x' u → ¬ R x₀ x → ¬ R x₀ x' → R x x') :
    ∃ g : X → U × Bool, (∀ x x', g x = g x' → R x x') ∧ ∀ x, Q x (g x).1 := by
  classical
  choose u hu using hQ
  have hex : ∀ x : X, ∃ y, Q y (u x) := fun x => ⟨x, hu x⟩
  refine ⟨fun x => (u x, decide (R (Classical.epsilon (α := X) (h := ⟨x⟩) fun y => Q y (u x)) x)), fun x x' h => ?_, hu⟩
  obtain ⟨h1, h3⟩ := Prod.ext_iff.1 h
  simp only at h1 h3
  have h0 := Classical.epsilon_spec (hex x)
  rw [← h1, decide_eq_decide] at h3
  have hx' : Q x' (u x) := h1 ▸ hu x'
  by_cases hc : R (Classical.epsilon (α := X) (h := ⟨x⟩) fun y => Q y (u x)) x
  · exact ht _ _ _ (hs _ _ hc) (h3.1 hc)
  · exact h2 _ _ _ _ h0 (hu x) hx' hc fun h4 => hc (h3.2 h4)
private theorem iso_symm {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r') :
    RepIso r' r := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, fun s => by rw [hg s]; group⟩
private theorem iso_trans {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' r'' : Γ →* GL (Fin n) k} (h : RepIso r r')
    (h' : RepIso r' r'') : RepIso r r'' := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  exact ⟨g' * g, fun s => by rw [hg' s, hg s]; group⟩
private theorem normV_rat {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  obtain ⟨h, h1, h2, h3⟩ := UpperTheory.exists_normV_eq_prime_pow_le_finrank ℚ p w hp hw
  rw [Module.finrank_self] at h2
  rw [h3, le_antisymm h2 h1, pow_one]
private theorem exists_over (K : Type) [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (f : ℕ), v.under (𝓞 ℚ) = w ∧ (p : 𝓞 K) ∈ v.asIdeal ∧ 1 ≤ f ∧ f ≤ 2 ∧ normV v = p ^ f := by
  haveI := w.isMaximal
  obtain ⟨Q, hQ, hL⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) w.asIdeal
  have hpQ : (p : 𝓞 K) ∈ Q := by
    have : (p : 𝓞 ℚ) ∈ Q.under (𝓞 ℚ) := hL.over ▸ hw
    simpa [Ideal.under, Ideal.mem_comap] using this
  have h0 : Q ≠ ⊥ := by
    rintro rfl
    exact hp.ne_zero (by simpa using hpQ)
  obtain ⟨f, f1, f2, f3⟩ := UpperTheory.exists_normV_eq_prime_pow_le_finrank K p ⟨Q, hQ.isPrime, h0⟩ hp hpQ
  exact ⟨⟨Q, hQ.isPrime, h0⟩, f, HeightOneSpectrum.ext hL.over.symm, hpQ, f1, h2 ▸ f2, f3⟩
private theorem not_mem_of_coprime {F : Type} [Field F] [NumberField F] {p a : ℕ} (h : p.Coprime a)
    (w : HeightOneSpectrum (𝓞 F)) (hw : (p : 𝓞 F) ∈ w.asIdeal) : (a : 𝓞 F) ∉ w.asIdeal := fun ha => by
  obtain ⟨x, y, e⟩ : IsCoprime (p : 𝓞 F) (a : 𝓞 F) := Nat.Coprime.cast h
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw)
    (w.asIdeal.mul_mem_left _ ha)))
private theorem exists_avoid {N : ℕ} (d : Fin (N + 1) → ℤ) (hd : ∀ i j, i ≠ j → IsCoprime (d i) (d j)) {p : ℕ} (hp : p.Prime) :
    ∃ u : Fin N → Fin (N + 1), Function.Injective u ∧ ∀ i, ¬ (p : ℤ) ∣ d (u i) := by
  by_cases h : ∃ j, (p : ℤ) ∣ d j
  · obtain ⟨j, hj⟩ := h
    refine ⟨j.succAbove, Fin.succAbove_right_injective, fun i hi => ?_⟩
    have := (hd _ _ (Fin.succAbove_ne j i)).isUnit_of_dvd' hi hj
    exact (Nat.prime_iff_prime_int.1 hp).not_unit this
  · exact ⟨Fin.succ, Fin.succ_injective _, fun i hi => h ⟨_, hi⟩⟩
private theorem map_inv_inv (B : Multiset ℂ) : (B.map (·⁻¹)).map (·⁻¹) = B := by
  rw [Multiset.map_map]
  simp
theorem countQ_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.GalN.V.LevelPNAlt → _root_.UpperTheory.GalN.V.AdmResNAlt → _root_.UpperTheory.GalN.V.Win.N.CountQAlt := by
  intro hP hL hA n hn
  classical
  obtain ⟨K₀, _, _, _, hK2, hKc⟩ := quadFam (n ^ 2 + 1 + 1)
  choose c A hcA using fun i => _root_.UpperTheory.GalN.V.Win.N.countP_alt hP hL (K₀ i) (hK2 i) n hn
  refine ⟨2 ^ (n + 1) * ((n ^ 2 + 1) * ∑ i, c i), ∑ i, A i, ?_⟩
  intro m wt hm hwt H hH M hM p w hp hpw hpM
  obtain ⟨u, hu, hup⟩ := exists_avoid (fun i => discr (K₀ i)) hKc hp
  choose v f hvw hpv hf1 hf2 hvf using fun i => exists_over (K₀ (u i)) (hK2 _) hp w hpw
  choose D hDc hD using fun i => hcA (u i) m wt hm hwt H hH M hM p (v i) hp (hpv i) hpM (hup i)
  obtain ⟨D', hD', e, he, heβ⟩ := rootSum n p hp.pos m wt (Fin (n ^ 2 + 1)) (fun i => normV (v i)) f
    (fun i => ⟨hf1 i, hf2 i, hvf i⟩) D
  refine ⟨D', hD'.trans ?_, ?_⟩
  · rw [mul_assoc, mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    have hb : ∀ i, Nat.card (D i).S ≤ (∑ i, c i) * (M * (H + 1)) ^ (∑ i, A i) := fun i =>
      (hDc i).trans (Nat.mul_le_mul (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
        (Nat.pow_le_pow_right (Nat.mul_pos hM (Nat.succ_pos _))
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))))
    refine (Finset.sum_le_sum fun i _ => hb i).trans ?_
    simp
  intro l _ hl2 hlp Ω _ _ _ ι
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let emb : ∀ i, K₀ (u i) →ₐ[ℚ] Ω := fun i => IsAlgClosed.lift
  letI alg : ∀ i, Algebra (K₀ (u i)) Ω := fun i => (emb i).toRingHom.toAlgebra
  haveI tow : ∀ i, IsScalarTower ℚ (K₀ (u i)) Ω := fun i =>
    IsScalarTower.of_algebraMap_eq fun x => ((emb i).commutes x).symm
  haveI clo : ∀ i, IsAlgClosure (K₀ (u i)) Ω := fun i => ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  choose δ _ _ hδ _ using fun i => UpperTheory.exists_quadratic_sign_character ℚ (K₀ (u i)) Ω l (hK2 _)
  have hδi : Function.Injective δ := fun i j hij => by
    by_contra hne
    refine signNe (K₀ (u i)) (K₀ (u j)) Ω (hK2 _) (hKc _ _ fun h => hne (hu h)) (Subgroup.ext fun s => ?_)
    rw [← (hδ i).1, ← (hδ j).1, hij]
  choose cl hcl hclβ using fun i => hD i l hl2 hlp Ω ι
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal :=
    not_mem_of_coprime ((Nat.coprime_primes hp Fact.out).2 hlp.symm) w hpw
  have hMw : ((M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := not_mem_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM) w hpw
  refine Exists.elim (bit_of_fibre (X := {r : G ℚ Ω →* GL (Fin n) (Qbar l) // _root_.UpperTheory.GalN.V.AdmRNAlt ι M m wt r})
    (U := Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1})
    (fun r r' => RepIso r.1 r'.1) (fun _ _ => iso_symm) (fun _ _ _ => iso_trans)
    (fun r t => (∃ h : _root_.UpperTheory.GalN.V.AdmPNAlt ι M m (r.1.comp (res ℚ Ω (K₀ (u t.1)))), cl t.1 ⟨_, h⟩ = t.2.1.1) ∧
      FrobEig ι r.1 w (t.2.1.2.map (·⁻¹))) ?ex ?two) ?main
  case main =>
    rintro g ⟨hg, hgQ⟩
    refine ⟨fun r => e ⟨(g r).1.1, (g r).1.2, (g r).2⟩, fun r r' h => hg r r' ?_, fun r => ?_⟩
    · have h1 := congrArg (fun x : (Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool) =>
        ((⟨x.1, x.2.1⟩ : Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1}), x.2.2)) (he h)
      exact h1
    · rw [heβ]
      exact (hgQ r).2
  case ex =>
    rintro ⟨r, hr⟩
    obtain ⟨i, hi⟩ : ∃ i, ¬ RepIso r (tw r (δ i)) := by
      by_contra hall
      have h1 := twCard _ _ n r hr.irr (Finset.univ.image δ) fun d hd => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hd
        by_contra h
        exact hall ⟨i, h⟩
      rw [Finset.card_image_of_injective _ hδi, Finset.card_univ, Fintype.card_fin] at h1
      omega
    have hirr := (resTwo _ _ _ n (res ℚ Ω (K₀ (u i))) (δ i) (hδ i).1 (hδ i).2 r).1 hr.irr hi
    have hadm := hA (K₀ (u i)) (hK2 _) n hn m wt hm M hM l hl2 Ω ι r hr hirr
    obtain ⟨B, hB⟩ := (frobEx ℚ Ω l ι n r w).2 M hr.level.away hlw hMw
    have h1 := (UpperTheory.frobenius_power_compatibility ℚ (K₀ (u i)) Ω l ι (v i) (f i) (by rw [hvw, hvf, normV_rat hp w hpw])).1 n r B
      (by rw [hvw]; exact hB)
    have h2 := (frobEx (K₀ (u i)) Ω l ι n _ (v i)).1 _ _ h1 (hclβ i ⟨_, hadm⟩)
    refine ⟨⟨i, ⟨(cl i ⟨_, hadm⟩, B.map (·⁻¹)), ?_⟩⟩, ⟨hadm, rfl⟩, ?_⟩
    · show (B.map (·⁻¹)).map (· ^ f i) = (D i).β (cl i ⟨_, hadm⟩)
      rw [← map_inv_inv ((D i).β _), ← h2, Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl fun b _ => inv_pow b (f i)
    · show FrobEig ι r w ((B.map (·⁻¹)).map (·⁻¹))
      rw [map_inv_inv]
      exact hB
  case two =>
    rintro ⟨i, t⟩ r₀ r r' ⟨⟨a₀, e₀⟩, -⟩ ⟨⟨a, e₁⟩, -⟩ ⟨⟨a', e₂⟩, -⟩ n1 n2
    have hR := (resTwo _ _ _ n (res ℚ Ω (K₀ (u i))) (δ i) (hδ i).1 (hδ i).2 r₀.1).2
    have k1 := (hR r.1 a₀.irr (hcl i _ _ (e₀.trans e₁.symm))).resolve_left n1
    have k2 := (hR r'.1 a₀.irr (hcl i _ _ (e₀.trans e₂.symm))).resolve_left n2
    exact iso_trans (iso_symm k1) k2
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af
private theorem trace_conj_gl3 {k : Type} [Field k] (g x : GL (Fin 3) k) :
    ((g * x * g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).trace = (x : Matrix (Fin 3) (Fin 3) k).trace := by
  rw [Units.val_mul, Matrix.trace_mul_comm, ← Units.val_mul, ← mul_assoc, inv_mul_cancel, one_mul]
private theorem place_over_rational_prime (K : Type) [Field K] [NumberField K] (p : ℕ) (w : HeightOneSpectrum (𝓞 K))
    (hw : (p : 𝓞 K) ∈ w.asIdeal) : ∃ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal := by
  refine ⟨w.under (𝓞 ℚ), ?_⟩
  change (p : 𝓞 ℚ) ∈ w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K))
  rw [Ideal.mem_comap, map_natCast]
  exact hw
theorem frobenius_trace_count_bound_of_rat_eigensystem_count_alt :
    _root_.UpperTheory.GalN.V.Win.N.CountQAlt → _root_.UpperTheory.GalN.V.Win.N.NewAdmAlt → ∃ c A : ℕ, ∀ (K : Type) [Field K] [NumberField K], ∀ e : ℕ, 1 ≤ e → ∀ M : ℕ, 1 ≤ M → ∀ (p h : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ∃ D : TrData (p ^ h) e, Nat.card D.S ≤ c * (M * (e + 1)) ^ A ∧ ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (B : ValuationSubring Ω), IsPlaceOver B w → ∀ σ : G K Ω, IsFrob B (p ^ h) σ → D.Classifies ι σ⁻¹ (_root_.UpperTheory.V.Z.Win.Dn.Adm2B ι e M) := by
  intro hQ hN
  obtain ⟨c, A, hc⟩ := hQ 2 le_rfl
  refine ⟨c, A, ?_⟩
  intro K _ _ e he M hM p h w hp hw hpM
  obtain ⟨v, hv⟩ := place_over_rational_prime K p w hw
  have hanti : StrictAnti (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    omega
  have hrev : ∀ i : Fin 2, (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i + (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i.rev = 0 := by
    intro i
    fin_cases i <;> simp [Fin.rev]
  have habs : ∀ i : Fin 2, |(![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i| ≤ (e : ℕ) := by
    intro i
    fin_cases i <;> simp
  obtain ⟨D, hcard, hD⟩ := hc _ 0 hanti hrev e habs M hM p v hp hv hpM
  obtain ⟨T, u, hT⟩ := traces_from_eigenvalues_rank2 p h e hp.pos D
  refine ⟨T, (Nat.card_congr u) ▸ hcard, ?_⟩
  intro l _ hl2 hlp Ω _ _ _ _ _ ι B hB σ hσ
  haveI : IsAlgClosure ℚ Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed K
      isAlgebraic := Algebra.IsAlgebraic.trans ℚ K Ω }
  obtain ⟨cl, hcl1, hcl2⟩ := hD l hl2 hlp Ω ι
  obtain ⟨hBv, τ, hτ, hI⟩ := UpperTheory.frobenius_pow_resDeg_place_norm K Ω p h w v hp hw hv B hB σ hσ
  have hex : ∀ r : {r // _root_.UpperTheory.V.Z.Win.Dn.Adm2B ι e M (K := K) (Ω := Ω) r},
      ∃ W : {W : G ℚ Ω →* GL (Fin 2) (Qbar l) // _root_.UpperTheory.GalN.V.AdmRNAlt ι M ![(e : ℤ), -(e : ℤ)] 0 W},
      ∃ g : GL (Fin 3) (Qbar l), ∀ s : G K Ω,
        ((g * r.1 s * g⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) =
        !![W.1 (s.restrictScalars ℚ) 0 0, 0, W.1 (s.restrictScalars ℚ) 0 1; 0, 1, 0;
          W.1 (s.restrictScalars ℚ) 1 0, 0, W.1 (s.restrictScalars ℚ) 1 1] := by
    rintro ⟨r, W, h1, h2, h3, h4, h5⟩
    exact ⟨⟨W, hN Ω l ι e M he W h1 h2 h3 h4⟩, h5⟩
  choose W g hg using hex
  refine ⟨fun r => u (cl (W r)), fun r r' H => ?_, fun r => ?_⟩
  · exact UpperTheory.block_conjugate_rank_three_rep _ _ _ (fun s : G K Ω => s.restrictScalars ℚ) (W r).1 (W r').1 r.1 r'.1 (g r) (g r')
      (hg r) (hg r') (hcl1 _ _ (u.injective H))
  · obtain ⟨hun, hfr⟩ := hcl2 (W r) B hBv
    have h1 := hun _ hI
    rw [map_mul, map_inv, inv_mul_eq_one, map_pow] at h1
    have h2 : (W r).1 ((σ⁻¹).restrictScalars ℚ) = (W r).1 τ⁻¹ ^ h := by
      have : (σ⁻¹).restrictScalars ℚ = (σ.restrictScalars ℚ : G ℚ Ω)⁻¹ := rfl
      rw [this, map_inv, map_inv, ← h1, inv_pow]
    have h3 := (UpperTheory.map_trace_eq_sum_roots_of_charpoly_map (Qbar l) ι.toRingHom _).2 _ (hfr τ hτ) h
    rw [Multiset.map_map] at h3
    rw [hT, ← trace_conj_gl3 (g r), hg r, h2, RingEquiv.eq_symm_apply]
    change _ = 1 + ((D.β (cl (W r))).map ((fun x => x ^ h) ∘ fun x => x⁻¹)).sum
    rw [← h3, ← Units.val_pow_eq_pow_val, Matrix.trace_fin_two, Matrix.trace_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_add (f := _), map_one, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    ring
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af
private theorem not_mem_of_distinct_prime {K : Type} [Field K] [NumberField K] {p l : ℕ} (w : HeightOneSpectrum (𝓞 K)) (hp : p.Prime)
    (hl : l.Prime) (hlp : l ≠ p) (hw : (p : 𝓞 K) ∈ w.asIdeal) : (l : 𝓞 K) ∉ w.asIdeal := by
  intro h
  have hc : IsCoprime (l : 𝓞 K) (p : 𝓞 K) := Nat.Coprime.cast ((Nat.coprime_primes hl hp).2 hlp)
  obtain ⟨a, b, hab⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left a h) (w.asIdeal.mul_mem_left b hw)))
private theorem admissible_twist_cyclotomic {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) (h : _root_.UpperTheory.GalN.V.Adm3NAlt ι e N ρ) :
    _root_.UpperTheory.GalN.V.AdmKNAlt ι N ![(e : ℤ) - 1, -1, -(e : ℤ) - 1] (tw ρ (cycBar K Ω l)⁻¹) := by
  refine ⟨(UpperTheory.isIrr_twist_and_repIso_of_twist_repIso _ _ 3 _).1 ρ h.irr, h.aut, ?_, _root_.UpperTheory.V.Keep.oddTw' _ h.unl⟩
  have h1 := UpperTheory.level_twist_cyclotomic_pow K Ω l 3 N _ ρ (-1) h.level
  rw [zpow_neg_one] at h1
  convert h1 using 1
  funext i
  fin_cases i <;> simp <;> ring
theorem frobenius_trace_count_bound_of_cm_eigensystem_count_alt :
    _root_.UpperTheory.GalN.V.Win.N.CountKAlt → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], ∃ c A : ℕ, ∀ e : ℕ, 1 ≤ e → ∀ N : ℕ, 1 ≤ N → ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ N → ¬ (p : ℤ) ∣ discr K → ∃ D : TrData (normV w) e, Nat.card D.S ≤ c * (N * (e + 1)) ^ A ∧ ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (B : ValuationSubring Ω), IsPlaceOver B w → ∀ σ : G K Ω, IsFrob B (normV w) σ → D.Classifies ι σ⁻¹ (_root_.UpperTheory.GalN.V.Adm3NAlt ι e N) := by
  intro hC K _ _ _
  obtain ⟨c, A, hK⟩ := hC K 3 (by norm_num)
  refine ⟨c * 2 ^ A, A, fun e he N hN p w hp hw hpN hpd => ?_⟩
  have hq : 1 ≤ normV w := by
    rw [normV, ← Ideal.absNorm_eq_natCard]
    exact (NumberField.HeightOneSpectrum.one_lt_absNorm w).le
  have hqC : ((normV w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : normV w ≠ 0)
  obtain ⟨D, hcard, hcl⟩ := hK ![(e : ℤ) - 1, -1, -(e : ℤ) - 1]
    (by
      refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
      fin_cases i <;> simp <;> omega)
    (by
      intro i
      fin_cases i <;> simp [Fin.rev] <;> ring)
    (e + 1)
    (by
      intro i
      rw [abs_le]
      fin_cases i <;> simp <;> omega)
    N hN p w hp hw hpN hpd
  obtain ⟨T, u, hT⟩ := traces_from_eigenvalues_rank3 (normV w) e hq D
  refine ⟨T, ?_, fun l _ hl2 hlp Ω _ _ _ ι B hB σ hσ => ?_⟩
  · rw [← Nat.card_congr u, mul_assoc, ← mul_pow]
    refine hcard.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
    nlinarith
  · obtain ⟨cl, h1, h2⟩ := hcl l hl2 hlp Ω ι
    refine ⟨fun r => u (cl ⟨_, admissible_twist_cyclotomic ι e N r.1 r.2⟩), fun r r' H => ?_, fun r => ?_⟩
    · exact (UpperTheory.isIrr_twist_and_repIso_of_twist_repIso _ _ 3 _).2 _ _ (h1 _ _ (u.injective H))
    · have hl := not_mem_of_distinct_prime w hp (Fact.out : l.Prime) hlp hw
      have e2 := ReciprocityTheory.Gal.cycZ_of_isFrob hl hB hσ
      have e3 : ((cycBar K Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l) := by
        change algebraMap ℚ_[l] (Qbar l) (((ReciprocityTheory.Gal.cycZ K Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = _
        rw [e2]; simp
      have h3 := (UpperTheory.map_trace_eq_sum_roots_of_charpoly_map _ ι.toRingHom _).1 _ ((h2 ⟨_, admissible_twist_cyclotomic ι e N r.1 r.2⟩ B hB).2 σ hσ)
      rw [tw_val, Matrix.trace_smul, MonoidHom.inv_apply, map_inv (cycBar K Ω l), inv_inv, e3, smul_eq_mul, map_mul,
        map_natCast] at h3
      rw [hT, eq_comm, RingEquiv.symm_apply_eq]
      simp only [mul_inv]
      rw [Multiset.sum_map_mul_left, ← h3, inv_mul_cancel_left₀ hqC]
      rfl
end
end UpperTheory.GalN.V.Win.N
end
end
