module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSubConjNotMem
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal GlobalTheory.SelfDualLatticeCompare

namespace GlobalTheory.UnramConjUnit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem _root_.GlobalTheory.UnramConjUnit.conj_ne_id (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : ¬ ∀ e, σ e = e := by
  intro hσ
  obtain ⟨-, hE, -, hconj⟩ := h
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc := hE.isComplex w
  rw [← InfinitePlace.mk_embedding w, InfinitePlace.isComplex_mk_iff] at hc
  apply hc
  ext x
  simpa [hσ x] using (hconj w.embedding x).symm

theorem _root_.GlobalTheory.UnramConjUnit.exists_sub_conj_notMem (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v) :
    ∃ (t d : 𝓞 E) (s : 𝓞 F), (d : E) = (t : E) - σ t ∧
      algebraMap F E (s : F) = (d : E) * d ∧ s ∉ v.asIdeal := by
  classical
  have hne := _root_.GlobalTheory.UnramConjUnit.conj_ne_id h
  obtain ⟨-, -, hrank, -⟩ := h
  let τ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ σ.bijective
  have hτ : ∀ x, τ x = σ x := fun _ => rfl
  have hτ1 : τ ≠ 1 := fun h1 => hne fun e => by rw [← hτ, h1]; rfl
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    refine le_antisymm (hrank ▸ AlgEquiv.card_le) ?_
    have h2 : ({1, τ} : Finset (E ≃ₐ[F] E)).card = 2 := Finset.card_pair (Ne.symm hτ1)
    exact h2 ▸ Finset.card_le_univ _
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E
    (by rw [Nat.card_eq_fintype_card, hcard, hrank])
  have hG : ∀ g : E ≃ₐ[F] E, g = 1 ∨ g = τ := by
    intro g
    by_contra hg
    push_neg at hg
    have h3 : ({g, 1, τ} : Finset (E ≃ₐ[F] E)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hg.1, hg.2]), Finset.card_pair (Ne.symm hτ1)]
    have := h3 ▸ Finset.card_le_univ ({g, 1, τ} : Finset (E ≃ₐ[F] E))
    omega
  have hττ : ∀ x, τ (τ x) = x := by
    intro x
    rcases hG (τ * τ) with h2 | h2
    · exact congrArg (fun g : E ≃ₐ[F] E => g x) h2
    · exact absurd (mul_eq_right.mp h2) hτ1
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := 𝓞 E) v.asIdeal
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [hPv.over, Ideal.under, Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
  have he := hv ⟨P, hP, hPbot⟩ hPv
  have hin : τ ∉ Ideal.inertia (E ≃ₐ[F] E) P := by
    intro hmem
    have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) v.asIdeal P
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P (E ≃ₐ[F] E)] at h1
    have h1' : Nat.card (Ideal.inertia (E ≃ₐ[F] E) P) = 1 := h1.trans he
    rw [Subgroup.card_eq_one] at h1'
    rw [h1', Subgroup.mem_bot] at hmem
    exact hτ1 hmem
  have hin' : ¬ ∀ x : 𝓞 E, τ • x - x ∈ P := fun hall => hin (AddSubgroup.mem_inertia.mpr hall)
  push_neg at hin'
  obtain ⟨x, hx⟩ := hin'
  set d : 𝓞 E := x - τ • x with hd_def
  have hd : d ∉ P := fun hd => hx (by rw [← neg_sub]; exact P.neg_mem hd)
  have hdE : (d : E) = x - σ x := rfl
  have hfix : ∀ g : E ≃ₐ[F] E, g ((d : E) * d) = (d : E) * d := by
    intro g
    rcases hG g with rfl | rfl
    · rfl
    · have : τ (d : E) = -(d : E) := by
        rw [hdE, map_sub, ← hτ, hττ, neg_sub]
      rw [map_mul, this, neg_mul_neg]
  obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).mpr hfix
  have hcint : IsIntegral ℤ c := by
    have hi : IsIntegral ℤ (algebraMap F E c) := by
      rw [hc]
      exact ((d * d : 𝓞 E)).isIntegral_coe
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E)
      (algebraMap F E).injective).mp hi
  refine ⟨x, d, ⟨c, hcint⟩, hdE, hc, ?_⟩
  intro hs
  have hmem : algebraMap (𝓞 F) (𝓞 E) ⟨c, hcint⟩ ∈ P := by
    rw [hPv.over] at hs
    exact hs
  have heq : algebraMap (𝓞 F) (𝓞 E) ⟨c, hcint⟩ = d * d := by
    apply RingOfIntegers.ext
    change _ = (d : E) * d
    rw [← hc]
    rfl
  rw [heq] at hmem
  exact hd ((hP.mem_or_mem hmem).elim id id)

theorem _root_.GlobalTheory.UnramConjUnit.exists_sub_conj_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    ∀ v : HeightOneSpectrum (𝓞 F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v →
    ∃ θ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v, ∃ b ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v,
      (θ - _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ θ) * b = 1 := by
  intro F E _ _ _ _ _ σ h v hv
  obtain ⟨t, d, s, hd, hs, hsv⟩ := _root_.GlobalTheory.UnramConjUnit.exists_sub_conj_notMem h v hv
  have hu : Valued.v (algebraMap F (v.adicCompletion F) (s : F)) = 1 := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [HeightOneSpectrum.adicCompletion.valued_coe]
    exact (HeightOneSpectrum.valuation_of_algebraMap v s).trans
      ((HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v s).mpr hsv)
  set u : v.adicCompletion F := algebraMap F (v.adicCompletion F) (s : F) with hu_def
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have huinv : u⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu, inv_one]
  have hintR : ∀ y : 𝓞 E, IsIntegral (v.adicCompletionIntegers F)
      ((1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (y : E)) := by
    intro y
    exact y.isIntegral_coe.map_of_comp_eq (Int.castRingHom _)
      (Algebra.TensorProduct.includeRight (R := F) (A := _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (B := E)).toRingHom
      (RingHom.ext_int _ _)
  refine ⟨(1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (t : E), hintR t,
    (u⁻¹ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E), ?_, ?_⟩
  · have hb : (u⁻¹ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E) =
        algebraMap (v.adicCompletionIntegers F) (TensorProduct F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E) ⟨u⁻¹, huinv⟩ *
          ((1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E)) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul]
      rfl
    rw [hb]
    exact isIntegral_algebraMap.mul (hintR d)
  · have hsub : (1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (t : E) -
        _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ ((1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (t : E)) =
        (1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E) := by
      simp [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hd, TensorProduct.tmul_sub]
    rw [hsub, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hs, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
    change (u * u⁻¹) ⊗ₜ[F] (1 : E) = 1
    rw [mul_inv_cancel₀ hu0]
    rfl

end GlobalTheory.UnramConjUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsPullback
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.MomN

private def zcRing (q : ℕ) [Fact q.Prime] : ℤ_[q] →+* ℂ_[q] :=
  (algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom

private theorem zc_eq (q : ℕ) [Fact q.Prime] (a : ℤ_[q]) : zc a = zcRing q a := rfl

private theorem isUnit_of_coprime (q : ℕ) [hq : Fact q.Prime] (s : ℕ) (h : Nat.Coprime s q) : IsUnit (s : ℤ_[q]) := by
  refine PadicInt.isUnit_iff.2 (le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => ?_))
  have h1 : ‖((s : ℤ) : ℤ_[q])‖ < 1 := by simpa using hlt
  have h2 : (q : ℤ) ∣ (s : ℤ) := (PadicInt.norm_int_lt_one_iff_dvd _).1 h1
  have h3 : q ∣ s := Int.natCast_dvd_natCast.1 h2
  exact (Nat.Prime.coprime_iff_not_dvd hq.out).1 h.symm h3

theorem latInt_pull : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (V' : Type) [NormedAddCommGroup V'] [NormedSpace ℂ V'] (ω : ℂ_[q]) (Λ : AddSubgroup V) (Λ' : AddSubgroup V') (g : V' →L[ℂ] V) (G : V → ℂ), ContDiff ℂ ⊤ G → (∀ x ∈ Λ', ∃ s : ℕ, Nat.Coprime s q ∧ s • g x ∈ Λ) → LatInt ι ω Λ G → LatInt ι ω Λ' fun z => G (g z) := by
  classical
  intro q _ ι V _ _ V' _ _ ω Λ Λ' g G hG hg hL κ _ v hv
  choose s hs hsΛ using fun i => hg (v i) (hv i)
  have hs0 : ∀ i, (s i : ℂ) ≠ 0 := by
    intro i h0
    have h1 : s i = 0 := by exact_mod_cast h0
    have h2 := hs i
    rw [h1, Nat.coprime_zero_left] at h2
    exact (Fact.out : q.Prime).one_lt.ne' h2
  choose u hu using fun i => isUnit_of_coprime q (s i) (hs i)
  have hM := hL κ (fun i => s i • g (v i)) hsΛ
  have hP : MomInt ι (fun i => ι.symm ω • g (v i)) G := by
    refine GlobalTheory.T.jetsAreBoundedMeasureMoments_padicInt_matrix_change q ι V κ κ (fun i => ι.symm ω • s i • g (v i)) (fun i => ι.symm ω • g (v i))
      (fun i j => if i = j then (s i : ℂ)⁻¹ else 0) (fun i j => if i = j then ((u i)⁻¹ : ℤ_[q]ˣ).1 else 0) G ?_ ?_ hM
    · intro i j
      by_cases hij : i = j
      · subst hij
        simp only [if_true, map_inv₀, map_natCast, zc_eq]
        have e : zcRing q ((u i)⁻¹ : ℤ_[q]ˣ).1 * (s i : ℂ_[q]) = 1 := by
          have e1 : (s i : ℂ_[q]) = zcRing q (u i).1 := by rw [hu i, map_natCast]
          rw [e1, ← map_mul, Units.inv_mul, map_one]
        exact (eq_inv_of_mul_eq_one_left e).symm
      · simp [hij, zc_eq]
    · intro i
      simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_comm (ι.symm ω) (s i : ℂ), smul_smul, inv_mul_cancel₀ (hs0 i), one_smul]
  obtain ⟨μ, hμ, hm⟩ := hP
  refine ⟨μ, hμ, fun k j f hf => ?_⟩
  rw [← hm k j f hf]
  congr 1
  have e := g.iteratedFDeriv_comp_right hG 0 (i := k) le_top
  have e2 : iteratedFDeriv ℂ k (fun z => G (g z)) 0 = iteratedFDeriv ℂ k (G ∘ g) 0 := rfl
  rw [e2, e]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, Function.comp_def, map_smul]

end GlobalTheory.MomN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsPullbackStatement
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeJetsAreBoundedMoments_pullback : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (V' : Type) [NormedAddCommGroup V'] [NormedSpace ℂ V'] (ω : ℂ_[q]) (Λ : AddSubgroup V) (Λ' : AddSubgroup V') (g : V' →L[ℂ] V) (G : V → ℂ), ContDiff ℂ ⊤ G → (∀ x ∈ Λ', ∃ s : ℕ, Nat.Coprime s q ∧ s • g x ∈ Λ) → LatInt ι ω Λ G → LatInt ι ω Λ' fun z => G (g z) := by
  first | exact @GlobalTheory.MomN.latInt_pull | exact GlobalTheory.MomN.latInt_pull | (intros; apply GlobalTheory.MomN.latInt_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasDerivAtOddJacobiThetaZeroEtaCube
open Complex

open UpperHalfPlane hiding I
open scoped Real
open Filter Topology

noncomputable section

namespace GlobalTheory.ThetaWeberRoad.OddDeriv

def tailProd (τ : ℍ) (v : ℂ) : ℂ := ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ) * v)

lemma hasProd_tailProd (τ : ℍ) (v : ℂ) :
    HasProd (fun n : ℕ => 1 - ModularForm.eta_q n (τ : ℂ) * v) (tailProd τ v) := by
  have hs : Summable fun n : ℕ => ‖-(ModularForm.eta_q n (τ : ℂ) * v)‖ := by
    have h := ModularForm.summable_eta_q τ
    simp only [norm_neg, norm_mul] at h ⊢
    exact h.mul_right _
  have hm : Multipliable fun n : ℕ => 1 + -(ModularForm.eta_q n (τ : ℂ) * v) :=
    multipliable_one_add_of_summable hs
  simp only [← sub_eq_add_neg] at hm
  exact hm.hasProd

lemma continuousAt_tailProd (τ : ℍ) (v₀ : ℂ) : ContinuousAt (tailProd τ) v₀ := by
  have hK : IsCompact (Metric.closedBall v₀ 1) := isCompact_closedBall v₀ 1
  have hu : Summable fun n : ℕ => ‖ModularForm.eta_q n (τ : ℂ)‖ * (‖v₀‖ + 1) := by
    have h := ModularForm.summable_eta_q τ
    simp only [norm_neg] at h
    exact h.mul_right _
  have H := Summable.hasProdUniformlyOn_nat_one_add
    (f := fun n v => -(ModularForm.eta_q n (τ : ℂ) * v)) hK hu
    (Filter.Eventually.of_forall fun n v hv => by
      rw [norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_of_mem_closedBall hv) (norm_nonneg _))
    (fun n => by fun_prop)
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at H
  have hc := H.continuousOn (Frequently.of_forall fun s =>
    (continuous_finsetProd s fun i _ => by fun_prop).continuousOn)
  have : ContinuousOn (tailProd τ) (Metric.closedBall v₀ 1) := by
    refine hc.congr fun v _ => ?_
    simp [tailProd, sub_eq_add_neg]
  exact this.continuousAt (Metric.closedBall_mem_nhds v₀ one_pos)

lemma tpFactor_shift (τ : ℍ) (z : ℂ) (n : ℕ) :
    tpFactor τ (z + ((τ : ℂ) + 1) / 2) n =
      (1 - ModularForm.eta_q n (τ : ℂ) * 1) *
        (1 - ModularForm.eta_q n (τ : ℂ) * cexp (2 * π * I * z)) *
        (1 - cexp (2 * π * I * n * (τ : ℂ)) * cexp (-(2 * π * I * z))) := by
  have hm : cexp (-(π * I)) = -1 := by rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  have hp : cexp (π * I) = -1 := Complex.exp_pi_mul_I
  have h1 : cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) + 2 * π * I * (z + ((τ : ℂ) + 1) / 2)) =
      -(cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ)) * cexp (2 * π * I * z)) := by
    rw [show -(cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ)) * cexp (2 * π * I * z)) =
      cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ)) * cexp (2 * π * I * z) * cexp (π * I) by
        rw [hp]; ring, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; ring
  have h2 : cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) - 2 * π * I * (z + ((τ : ℂ) + 1) / 2)) =
      -(cexp (2 * π * I * n * (τ : ℂ)) * cexp (-(2 * π * I * z))) := by
    rw [show -(cexp (2 * π * I * n * (τ : ℂ)) * cexp (-(2 * π * I * z))) =
      cexp (2 * π * I * n * (τ : ℂ)) * cexp (-(2 * π * I * z)) * cexp (-(π * I)) by
        rw [hm]; ring, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; ring
  unfold tpFactor
  rw [ModularForm.eta_q_eq_cexp, h1, h2]
  ring

lemma jacobiTheta₂_shift (hT : TripleProduct) (τ : ℍ) (z : ℂ) :
    jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ =
      tailProd τ 1 * tailProd τ (cexp (2 * π * I * z)) *
        ((1 - cexp (-(2 * π * I * z))) * tailProd τ (cexp (-(2 * π * I * z)))) := by
  have hA := hasProd_tailProd τ 1
  have hB := hasProd_tailProd τ (cexp (2 * π * I * z))
  have h0 := hasProd_tailProd τ (cexp (-(2 * π * I * z)))
  have h1 : HasProd (fun n : ℕ => 1 - cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (τ : ℂ)) *
      cexp (-(2 * π * I * z))) (tailProd τ (cexp (-(2 * π * I * z)))) := by
    convert h0 using 2 with n
    rw [ModularForm.eta_q_eq_cexp]; push_cast; ring_nf
  have hC := HasProd.zero_mul
    (f := fun n : ℕ => 1 - cexp (2 * π * I * (n : ℂ) * (τ : ℂ)) * cexp (-(2 * π * I * z))) h1
  have e0 : (1 - cexp (2 * π * I * ((0 : ℕ) : ℂ) * (τ : ℂ)) * cexp (-(2 * π * I * z))) =
      1 - cexp (-(2 * π * I * z)) := by simp
  rw [e0] at hC
  have hAll := (hA.mul hB).mul hC
  refine (hT τ (z + ((τ : ℂ) + 1) / 2)).unique ?_
  convert hAll using 1
  funext n
  rw [tpFactor_shift]

end GlobalTheory.ThetaWeberRoad.OddDeriv

namespace GlobalTheory.ThetaWeberRoad.OddDeriv

theorem hasDerivAt_mul_of_eq_zero {F R : ℂ → ℂ} {F' : ℂ} (hF : HasDerivAt F F' 0) (hF0 : F 0 = 0)
    (hR : ContinuousAt R 0) : HasDerivAt (fun z => F z * R z) (F' * R 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope] at hF ⊢
  have hR' : Tendsto R (𝓝[≠] (0 : ℂ)) (𝓝 (R 0)) := hR.tendsto.mono_left nhdsWithin_le_nhds
  refine (hF.mul hR').congr' ?_
  filter_upwards with z
  simp only [slope_def_field, hF0, sub_zero, zero_mul]
  ring

theorem hasDerivAt_oddTheta_zero :
    TripleProduct → ∀ τ : UpperHalfPlane,
      HasDerivAt (oddTheta τ) (-2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3) 0 := by
  intro hT τ
  set F : ℂ → ℂ := fun z => cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)) *
    (1 - cexp (-(2 * π * I * z))) with hFdef
  set R : ℂ → ℂ := fun z => tailProd τ 1 * tailProd τ (cexp (2 * π * I * z)) *
    tailProd τ (cexp (-(2 * π * I * z))) with hRdef
  have hfun : oddTheta τ = fun z => F z * R z := by
    funext z
    simp only [oddTheta, F, R]
    rw [jacobiTheta₂_shift hT]
    ring
  have hF0 : F 0 = 0 := by simp [F]
  have h1 : HasDerivAt (fun z : ℂ => cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)))
      (cexp (π * I * (τ : ℂ) / 4 + π * I * (0 + 1 / 2)) * (π * I * 1)) 0 :=
    ((((hasDerivAt_id (0 : ℂ)).add_const (1 / 2)).const_mul (π * I)).const_add _).cexp
  have h2 : HasDerivAt (fun z : ℂ => 1 - cexp (-(2 * π * I * z)))
      (-(cexp (-(2 * π * I * 0)) * -(2 * π * I * 1))) 0 :=
    (((hasDerivAt_id (0 : ℂ)).const_mul (2 * π * I)).neg.cexp).const_sub 1
  have hF : HasDerivAt F (cexp (π * I * (τ : ℂ) / 4 + π * I * (0 + 1 / 2)) * (π * I * 1) *
      (1 - cexp (-(2 * π * I * 0))) + cexp (π * I * (τ : ℂ) / 4 + π * I * (0 + 1 / 2)) *
      (-(cexp (-(2 * π * I * 0)) * -(2 * π * I * 1)))) 0 := h1.mul h2
  have hR : ContinuousAt R 0 := by
    have hu : Continuous fun z : ℂ => cexp (2 * π * I * z) := by fun_prop
    have hv : Continuous fun z : ℂ => cexp (-(2 * π * I * z)) := by fun_prop
    exact (continuousAt_const.mul ((continuousAt_tailProd τ _).comp hu.continuousAt)).mul
      ((continuousAt_tailProd τ _).comp hv.continuousAt)
  rw [hfun]
  have key := hasDerivAt_mul_of_eq_zero hF hF0 hR
  convert key using 1
  have hT1 : tailProd τ 1 = ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) := by
    simp [tailProd]
  have hq : (Function.Periodic.qParam 24 (τ : ℂ)) ^ 3 = cexp (π * I * (τ : ℂ) / 4) := by
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hI : cexp (π * I * (τ : ℂ) / 4 + π * I * (0 + 1 / 2)) = cexp (π * I * (τ : ℂ) / 4) * I := by
    rw [Complex.exp_add]
    congr 1
    rw [show π * I * (0 + 1 / 2) = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  simp only [R, mul_zero, neg_zero, Complex.exp_zero, hT1, hI]
  unfold ModularForm.eta
  rw [mul_pow, hq]
  ring_nf
  rw [Complex.I_sq]
  ring

end GlobalTheory.ThetaWeberRoad.OddDeriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsReflection
open scoped Matrix
open Formalism.UG

namespace GlobalTheory.WittTransitivity

variable {A : Type} [CommRing A] (c : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)

theorem hform_sub_left (x y z : Fin M → A) :
    hform c J (x - y) z = hform c J x z - hform c J y z := by
  simp only [Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_sub_right (x y z : Fin M → A) :
    hform c J x (y - z) = hform c J x y - hform c J x z := by
  simp only [Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hform_smul_left (a : A) (x z : Fin M → A) :
    hform c J (a • x) z = c a * hform c J x z := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_smul_right (a : A) (x z : Fin M → A) :
    hform c J x (a • z) = a * hform c J x z := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem conj_hform (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = J i j) (x y : Fin M → A) :
    c (hform c J x y) = hform c J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, hc, hJ]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem hform_eq_sum (x y : Fin M → A) :
    hform c J x y = ∑ j, hform c J x (Pi.single j 1) * y j := by
  have key : ∀ j, hform c J x (Pi.single j 1) = ∑ i, c (x i) * J i j := by
    intro j
    simp [Formalism.UG.hform, Pi.single_apply]
  simp_rw [key]
  simp only [Formalism.UG.hform, Finset.sum_mul]
  exact Finset.sum_comm

theorem exists_mem_UJ (hdet : IsUnit J.det) (g : Matrix (Fin M) (Fin M) A)
    (hg : ∀ y z, hform c J (g *ᵥ y) (g *ᵥ z) = hform c J y z) :
    ∃ G ∈ UJ c J, (G : Matrix (Fin M) (Fin M) A) = g := by
  have hsingle : ∀ k l, hform c J (Pi.single k 1) (Pi.single l 1) = J k l := by
    intro k l
    simp [Formalism.UG.hform, Pi.single_apply, apply_ite c]
  have hcol : ∀ k, g *ᵥ Pi.single k 1 = fun i => g i k := by
    intro k
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have key : (g.map c)ᵀ * J * g = J := by
    ext k l
    have h1 := hg (Pi.single k 1) (Pi.single l 1)
    rw [hcol, hcol, hsingle] at h1
    rw [← h1]
    simp only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Finset.sum_mul]
    exact Finset.sum_comm
  have hdg : IsUnit g.det := by
    have h2 := congrArg Matrix.det key
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    have h3 : J.det * ((g.map c)ᵀ.det * g.det) = J.det * 1 := by
      linear_combination h2
    have h4 := hdet.mul_left_cancel h3
    exact isUnit_of_mul_isUnit_right (by rw [h4]; exact isUnit_one)
  refine ⟨Matrix.nonsingInvUnit g hdg, ?_, rfl⟩
  simp only [Formalism.UG.UJ, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq,
    Formalism.UG.cT]
  exact key

theorem exists_reflection (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = J i j)
    (hdet : IsUnit J.det) (x x' : Fin M → A) (hx : hform c J x x = hform c J x' x')
    (hs : IsUnit (hform c J x x - hform c J x' x)) :
    ∃ g ∈ UJ c J, (g : Matrix (Fin M) (Fin M) A) *ᵥ x = x' := by
  set s := hform c J x x - hform c J x' x with hs_def
  obtain ⟨su, hsu⟩ := hs
  set b : A := ↑su⁻¹ with hb_def
  have hbs : b * s = 1 := by rw [hb_def, ← hsu, Units.inv_mul]
  have hcb : c b * c s = 1 := by rw [← map_mul, hbs, map_one]
  set v := x - x' with hv
  have hvv : hform c J v v = s + c s := by
    have hxx : c (hform c J x x) = hform c J x x := conj_hform c J hc hJ x x
    have e1 : c s = hform c J x x - hform c J x x' := by
      rw [hs_def, map_sub, hxx, conj_hform c J hc hJ]
    rw [hv, hform_sub_left, hform_sub_right, hform_sub_right, e1, hs_def, ← hx]
    ring
  set g : Matrix (Fin M) (Fin M) A :=
    1 - Matrix.of (fun k j => b * v k * hform c J v (Pi.single j 1)) with hg_def
  have hgy : ∀ y, g *ᵥ y = y - (b * hform c J v y) • v := by
    intro y
    rw [hform_eq_sum c J v y]
    ext k
    rw [hg_def, Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Matrix.of_apply]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hpres : ∀ y z, hform c J (g *ᵥ y) (g *ᵥ z) = hform c J y z := by
    intro y z
    rw [hgy, hgy, hform_sub_left, hform_sub_right, hform_sub_right, hform_smul_left,
      hform_smul_left, hform_smul_right, hform_smul_right, map_mul,
      conj_hform c J hc hJ v y, hvv]
    linear_combination (hform c J y v * hform c J v z * c b) * hbs +
      (hform c J y v * hform c J v z * b) * hcb
  obtain ⟨G, hG, hGg⟩ := exists_mem_UJ c J hdet g hpres
  refine ⟨G, hG, ?_⟩
  have hvx : hform c J v x = s := by rw [hv, hform_sub_left, hs_def]
  rw [hGg, hgy, hvx, hbs, one_smul, hv, sub_sub_cancel]

theorem exists_norm_one (hc : ∀ a, c (c a) = a) (hf : ∀ a, c a = a → a ≠ 0 → IsUnit a)
    (h2 : IsUnit (2 : A)) (h3 : (3 : A) ≠ 0) (hθ : ∃ θ, IsUnit (θ - c θ))
    (b t : A) (hcb : c b = b) (hb : IsUnit b) :
    ∃ u : A, u * c u = 1 ∧ IsUnit (b - c u * t) := by
  have hN : ∀ a : A, a * c a ≠ 0 → IsUnit (a * c a) := by
    intro a ha
    exact hf _ (by rw [map_mul, hc, mul_comm]) ha
  by_cases h1 : (b - t) * c (b - t) = 0
  · by_cases h1' : (b + t) * c (b + t) = 0
    · rw [map_sub, hcb] at h1
      rw [map_add (f := _), hcb] at h1'
      have h4 : (2 * b) * (t + c t) = (2 * b) * 0 := by linear_combination h1' - h1
      have htc : t + c t = 0 := (h2.mul hb).mul_left_cancel h4
      have hct : c t = -t := by linear_combination htc
      rw [hct] at h1 h1'
      have h5 : (2 : A) * (b * b - t * t) = 2 * 0 := by linear_combination h1 + h1'
      have hb2 : b * b = t * t := sub_eq_zero.mp (h2.mul_left_cancel h5)
      have ht : IsUnit t := isUnit_of_mul_isUnit_left (by rw [← hb2]; exact hb.mul hb)
      have key : ∀ w : A, IsUnit (w * c w) → IsUnit (w - c w) → IsUnit (w + c w) →
          ∃ u : A, u * c u = 1 ∧ IsUnit (b - c u * t) := by
        intro w hw hm hp
        obtain ⟨e, he⟩ := isUnit_of_mul_isUnit_right hw
        have h0 : c (↑e⁻¹ : A) * w = 1 := by
          have h6 := congrArg c (Units.inv_mul e)
          rw [map_mul, he, hc, map_one] at h6
          exact h6
        refine ⟨w * ↑e⁻¹, ?_, ?_⟩
        · calc w * ↑e⁻¹ * c (w * ↑e⁻¹) = (↑e⁻¹ * c w) * (c ↑e⁻¹ * w) := by rw [map_mul]; ring
            _ = 1 := by rw [← he, Units.inv_mul, h0, one_mul]
        · have hprod : IsUnit ((w * b - c w * t) * (c w * b + w * t)) := by
            have e1 : (w * b - c w * t) * (c w * b + w * t) = b * t * (w - c w) * (w + c w) := by
              linear_combination (w * c w) * hb2
            rw [e1]
            exact ((hb.mul ht).mul hm).mul hp
          have e2 : b - c (w * ↑e⁻¹) * t = c ↑e⁻¹ * (w * b - c w * t) := by
            rw [map_mul]
            linear_combination (-b) * h0
          rw [e2]
          exact (isUnit_of_mul_isUnit_left (by rw [h0]; exact isUnit_one)).mul
            (isUnit_of_mul_isUnit_left hprod)
      obtain ⟨θ, hθu⟩ := hθ
      have hcδ : c (θ - c θ) = -(θ - c θ) := by rw [map_sub, hc]; ring
      by_cases hd : (1 + (θ - c θ)) * c (1 + (θ - c θ)) = 0
      · rw [map_add (f := _), map_one, hcδ] at hd
        apply key (2 + (θ - c θ))
        · have e : (2 + (θ - c θ)) * c (2 + (θ - c θ)) = 3 := by
            rw [map_add (f := _), map_ofNat, hcδ]
            linear_combination hd
          rw [e]
          exact hf 3 (map_ofNat c 3) h3
        · have e : 2 + (θ - c θ) - c (2 + (θ - c θ)) = 2 * (θ - c θ) := by
            rw [map_add (f := _), map_ofNat, hcδ]
            ring
          rw [e]
          exact h2.mul hθu
        · have e : 2 + (θ - c θ) + c (2 + (θ - c θ)) = 2 * 2 := by
            rw [map_add (f := _), map_ofNat, hcδ]
            ring
          rw [e]
          exact h2.mul h2
      · apply key (1 + (θ - c θ)) (hN _ hd)
        · have e : 1 + (θ - c θ) - c (1 + (θ - c θ)) = 2 * (θ - c θ) := by
            rw [map_add (f := _), map_one, hcδ]
            ring
          rw [e]
          exact h2.mul hθu
        · have e : 1 + (θ - c θ) + c (1 + (θ - c θ)) = 2 := by
            rw [map_add (f := _), map_one, hcδ]
            ring
          rw [e]
          exact h2
    · refine ⟨-1, by rw [map_neg, map_one]; ring, ?_⟩
      have e : b - c (-1) * t = b + t := by rw [map_neg, map_one]; ring
      rw [e]
      exact isUnit_of_mul_isUnit_left (hN _ h1')
  · refine ⟨1, by rw [map_one, one_mul], ?_⟩
    have e : b - c 1 * t = b - t := by rw [map_one, one_mul]
    rw [e]
    exact isUnit_of_mul_isUnit_left (hN _ h1)

theorem witt_transitive (A : Type) [CommRing A] (c : A →+* A) (hc : ∀ a, c (c a) = a)
    (hf : ∀ a, c a = a → a ≠ 0 → IsUnit a) (h2 : IsUnit (2 : A)) (h3 : (3 : A) ≠ 0)
    (hθ : ∃ θ, IsUnit (θ - c θ)) (M : ℕ) (J : Matrix (Fin M) (Fin M) A)
    (hJ : ∀ i j, c (J j i) = J i j) (hdet : IsUnit J.det) (x x' : Fin M → A)
    (hx : hform c J x x = hform c J x' x') (hb : IsUnit (hform c J x x)) :
    ∃ g ∈ UJ c J, (g : Matrix (Fin M) (Fin M) A) *ᵥ x = x' := by
  have hxx : c (hform c J x x) = hform c J x x := conj_hform c J hc hJ x x
  obtain ⟨u, hu, hut⟩ :=
    exists_norm_one c hc hf h2 h3 hθ (hform c J x x) (hform c J x' x) hxx hb
  have hux : hform c J x x = hform c J (u • x') (u • x') := by
    rw [hform_smul_left, hform_smul_right, ← hx]
    linear_combination (-(hform c J x x)) * hu
  obtain ⟨g1, hg1, hg1x⟩ := exists_reflection c J hc hJ hdet x (u • x') hux
    (by rw [hform_smul_left]; exact hut)
  obtain ⟨g2, hg2, hg2e⟩ := exists_mem_UJ c J hdet (c u • (1 : Matrix (Fin M) (Fin M) A))
    (by
      intro y z
      simp only [Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [hform_smul_left, hform_smul_right, hc]
      linear_combination (hform c J y z) * hu)
  refine ⟨g2 * g1, mul_mem hg2 hg1, ?_⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg1x, hg2e]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul]
  rw [mul_comm, hu, one_smul]

end GlobalTheory.WittTransitivity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeberFunctionProductEqSqrtTwo
open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.WeberProduct

def eulerProd (x : ℂ) : ℂ := ∏' n : ℕ, (1 - x ^ (n + 1))

def oddProd (x : ℂ) : ℂ := ∏' k : ℕ, (1 - x ^ (2 * k + 1))

theorem multipliable_odd {x : ℂ} (hx : ‖x‖ < 1) :
    Multipliable fun k : ℕ ↦ 1 - x ^ (2 * k + 1) := by
  have h2 : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
  have hs : Summable fun k : ℕ ↦ ‖x‖ * (‖x‖ ^ 2) ^ k :=
    (summable_geometric_of_lt_one (by positivity) h2).mul_left _
  have := multipliable_one_add_of_summable (f := fun k : ℕ ↦ -x ^ (2 * k + 1))
    (hs.congr fun k ↦ by simp [norm_pow, pow_succ, pow_mul]; ring)
  simpa [sub_eq_add_neg] using this

theorem multipliable_euler {x : ℂ} (hx : ‖x‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 - x ^ (n + 1) :=
  ModularForm.multipliable_one_sub_pow hx

theorem eulerProd_split {y : ℂ} (hy : ‖y‖ < 1) : eulerProd y = oddProd y * eulerProd (y ^ 2) := by
  have hy2 : ‖y ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg y]
  have e1 : (fun k : ℕ ↦ (fun n : ℕ ↦ 1 - y ^ (n + 1)) (2 * k)) = fun k ↦ 1 - y ^ (2 * k + 1) := rfl
  have e2 : (fun k : ℕ ↦ (fun n : ℕ ↦ 1 - y ^ (n + 1)) (2 * k + 1)) =
      fun k ↦ 1 - (y ^ 2) ^ (k + 1) := by
    funext k; rw [← pow_mul]; ring_nf
  have h := tprod_even_mul_odd (f := fun n : ℕ ↦ 1 - y ^ (n + 1))
    (by rw [e1]; exact multipliable_odd hy) (by rw [e2]; exact multipliable_euler hy2)
  rw [e1, e2] at h
  rw [eulerProd, eulerProd, oddProd, h]

theorem oddProd_neg_mul {t : ℂ} (ht : ‖t‖ < 1) : oddProd (-t) * oddProd t = oddProd (t ^ 2) := by
  have hn : ‖-t‖ < 1 := by rwa [norm_neg]
  rw [oddProd, oddProd, oddProd, ← (multipliable_odd hn).tprod_mul (multipliable_odd ht)]
  congr 1
  funext k
  rw [Odd.neg_pow ⟨k, rfl⟩, ← pow_mul]
  ring_nf

theorem eulerProd_identity {t : ℂ} (ht : ‖t‖ < 1) :
    eulerProd (-t) * eulerProd t * eulerProd (t ^ 4) = eulerProd (t ^ 2) ^ 3 := by
  have hn : ‖-t‖ < 1 := by rwa [norm_neg]
  have h2 : ‖t ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg t]
  have a := eulerProd_split hn
  have b := eulerProd_split ht
  have c := eulerProd_split h2
  rw [neg_sq] at a
  rw [← pow_mul] at c
  norm_num at c
  have d := oddProd_neg_mul ht
  norm_num at c
  linear_combination (eulerProd t * eulerProd (t ^ 4)) * a + (oddProd (-t) * eulerProd (t ^ 2) * eulerProd (t ^ 4)) * b +
    (eulerProd (t ^ 2) ^ 2 * eulerProd (t ^ 4)) * d - eulerProd (t ^ 2) ^ 2 * c

theorem eta_eq (z : ℂ) : ModularForm.eta z = Function.Periodic.qParam 24 z * eulerProd (Function.Periodic.qParam 1 z) :=
  rfl

theorem eta_relation (τ : ℍ) :
    cexp (-(π * I / 24)) * ModularForm.eta (((τ : ℂ) + 1) / 2) * ModularForm.eta ((τ : ℂ) / 2) *
      ModularForm.eta (2 * (τ : ℂ)) = ModularForm.eta τ ^ 3 := by
  set t := cexp (π * I * (τ : ℂ)) with ht_def
  have ht : ‖t‖ < 1 := by
    rw [ht_def, Complex.norm_exp, Real.exp_lt_one_iff]
    have := τ.im_pos
    simp only [mul_re, ofReal_re, Complex.I_re, ofReal_im, Complex.I_im, mul_im, coe_re, coe_im]
    nlinarith [Real.pi_pos]
  have q1 : Function.Periodic.qParam 1 (((τ : ℂ) + 1) / 2) = -t := by
    rw [Function.Periodic.qParam, ht_def, ← mul_neg_one, ← Complex.exp_pi_mul_I, ← Complex.exp_add]
    congr 1; push_cast; ring
  have q2 : Function.Periodic.qParam 1 ((τ : ℂ) / 2) = t := by
    rw [Function.Periodic.qParam, ht_def]; congr 1; push_cast; ring
  have q3 : Function.Periodic.qParam 1 (2 * (τ : ℂ)) = t ^ 4 := by
    rw [Function.Periodic.qParam, ht_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have q4 : Function.Periodic.qParam 1 (τ : ℂ) = t ^ 2 := by
    rw [Function.Periodic.qParam, ht_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hq : cexp (-(π * I / 24)) * Function.Periodic.qParam 24 (((τ : ℂ) + 1) / 2) *
      Function.Periodic.qParam 24 ((τ : ℂ) / 2) * Function.Periodic.qParam 24 (2 * (τ : ℂ)) =
      Function.Periodic.qParam 24 (τ : ℂ) ^ 3 := by
    simp only [Function.Periodic.qParam, ← Complex.exp_add, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [eta_eq, eta_eq, eta_eq, eta_eq, q1, q2, q3, q4]
  have key := eulerProd_identity ht
  linear_combination (eulerProd (-t) * eulerProd t * eulerProd (t ^ 4)) * hq +
    Function.Periodic.qParam 24 (τ : ℂ) ^ 3 * key

theorem weber_prod (τ : ℍ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₁ τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₂ τ =
      ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h0 : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero τ.2
  have key := eta_relation τ
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₁, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₂]
  rw [div_mul_div_comm, div_mul_div_comm, div_eq_iff (by simp [h0])]
  linear_combination ((Real.sqrt 2 : ℝ) : ℂ) * key

end GlobalTheory.WeberProduct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GaussianOddJacobiThetaEqDerivMulSgStar
open Complex

noncomputable section

namespace GlobalTheory.SgStarOddTheta

open Formalism.L2.Th1.F

theorem jacobiTheta₂_add_int_lattice (z τ : ℂ) (m k : ℤ) :
    jacobiTheta₂ (z + (m * τ + k)) τ =
      cexp (-(Real.pi : ℂ) * I * (m ^ 2 * τ + 2 * m * z)) * jacobiTheta₂ z τ := by
  rw [jacobiTheta₂, jacobiTheta₂, ← (Equiv.addRight m).tsum_eq (fun n => jacobiTheta₂_term n z τ),
    ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term, jacobiTheta₂_term, ← Complex.exp_add]
  refine Complex.exp_eq_exp_iff_exists_int.2 ⟨n * k, ?_⟩
  simp only [Equiv.coe_addRight]
  push_cast
  ring

theorem oddTheta_add (τ : UpperHalfPlane) (z : ℂ) (m k : ℤ) :
    GlobalTheory.ThetaWeberRoad.oddTheta τ (z + (m * (τ : ℂ) + k)) =
      cexp ((Real.pi : ℂ) * I * (k - m - m ^ 2 * (τ : ℂ) - 2 * m * z)) *
        GlobalTheory.ThetaWeberRoad.oddTheta τ z := by
  unfold GlobalTheory.ThetaWeberRoad.oddTheta
  rw [show z + (m * (τ : ℂ) + k) + ((τ : ℂ) + 1) / 2 = (z + ((τ : ℂ) + 1) / 2) + (m * (τ : ℂ) + k) by ring,
    jacobiTheta₂_add_int_lattice, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  ring

theorem exp_pi_I_int (j : ℤ) : cexp ((Real.pi : ℂ) * I * j) = if Even j then 1 else -1 := by
  rw [mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  split_ifs with h
  · exact h.neg_one_zpow
  · exact (Int.not_even_iff_odd.1 h).neg_one_zpow

theorem area_periodPairOfTau (τ : UpperHalfPlane) : area (GlobalTheory.periodPairOfTau τ) = τ.im := by
  simp [area, GlobalTheory.periodPairOfTau, abs_of_pos τ.im_pos]

theorem semiChar_periodPairOfTau (τ : UpperHalfPlane) (m k : ℤ) :
    semiChar (GlobalTheory.periodPairOfTau τ) (m * (τ : ℂ) + k) =
      cexp ((Real.pi : ℂ) * I * ((k - m + m * k : ℤ) : ℂ)) := by
  have hpar : Even (k - m + m * k) ↔ Even m ∧ Even k := by
    simp only [parity_simps]; tauto
  have hmem : (m * (τ : ℂ) + k) / 2 ∈ (GlobalTheory.periodPairOfTau τ).lattice ↔ Even m ∧ Even k := by
    rw [GlobalTheory.mem_lattice_periodPairOfTau]
    constructor
    · rintro ⟨p, q, e⟩
      have e1 : (m * (τ : ℂ) + k) = (p + p : ℤ) * (τ : ℂ) + (q + q : ℤ) := by
        push_cast
        linear_combination -2 * e
      have h1 := congrArg Complex.im e1
      simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
        add_zero, UpperHalfPlane.coe_im, mul_left_inj' τ.im_ne_zero, Int.cast_inj] at h1
      rw [h1, add_right_inj, Int.cast_inj] at e1
      exact ⟨⟨p, h1⟩, ⟨q, e1⟩⟩
    · rintro ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩
      exact ⟨p, q, by push_cast; ring⟩
  rw [exp_pi_I_int, semiChar]
  by_cases h : Even m ∧ Even k
  · rw [if_pos (hmem.2 h), if_pos (hpar.2 h)]
  · rw [if_neg (fun h' => h (hmem.1 h')), if_neg (fun h' => h (hpar.1 h'))]

def expOddTheta (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  cexp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * GlobalTheory.ThetaWeberRoad.oddTheta τ z

theorem differentiable_expOddTheta (τ : UpperHalfPlane) : Differentiable ℂ (expOddTheta τ) := by
  have := GlobalTheory.ThetaWeberRoad.differentiable_oddTheta τ
  unfold expOddTheta
  fun_prop

theorem expOddTheta_law (τ : UpperHalfPlane) : ∀ ω ∈ (GlobalTheory.periodPairOfTau τ).lattice, ∀ z,
    semiChar (GlobalTheory.periodPairOfTau τ) ω * opU (GlobalTheory.periodPairOfTau τ) ω (expOddTheta τ) z =
      expOddTheta τ z := by
  intro ω hω z
  obtain ⟨m, k, rfl⟩ := (GlobalTheory.mem_lattice_periodPairOfTau τ ω).1 hω
  simp only [one_mul]
  rw [semiChar_periodPairOfTau, opU, herm, herm, area_periodPairOfTau, expOddTheta, expOddTheta,
    oddTheta_add]
  have hE : ∀ A B C D w : ℂ, cexp A * (cexp B * (cexp C * w) * cexp D) = cexp (A + B + C + D) * w := by
    intros
    simp only [Complex.exp_add]
    ring
  rw [hE]
  congr 1
  refine Complex.exp_eq_exp_iff_exists_int.2 ⟨k - m + m * k, ?_⟩
  have hc : (starRingEnd ℂ) (τ : ℂ) = τ - 2 * τ.im * I := by
    apply Complex.ext <;> simp
    ring
  have hy : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_ne_zero
  simp only [map_add (f := _), map_mul, map_intCast, hc]
  field_simp
  push_cast
  ring

theorem exp_mul_oddTheta_eq_deriv_mul_sgStar :
    Formalism.L2.Th1.F.ThetaLine → Formalism.L2.Th1.F.SgStarBasic → ∀ (τ : UpperHalfPlane) (z : ℂ),
      Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * GlobalTheory.ThetaWeberRoad.oddTheta τ z =
        deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z := by
  intro hTL hSB τ z
  obtain ⟨c, hc⟩ := hTL _ (expOddTheta τ) (differentiable_expOddTheta τ) (expOddTheta_law τ)
  have hfun : expOddTheta τ = fun z => c * sgStar (GlobalTheory.periodPairOfTau τ) z := funext hc
  obtain ⟨hdiff, -, -, hd1, -⟩ := hSB (GlobalTheory.periodPairOfTau τ)
  have h1 : deriv (expOddTheta τ) 0 = c := by
    rw [hfun]
    have := ((hdiff 0).hasDerivAt.const_mul c).deriv
    rw [hd1, mul_one] at this
    exact this
  have he : HasDerivAt (fun z : ℂ => cexp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ)))) 0 0 := by
    have := (((hasDerivAt_pow 2 (0 : ℂ)).const_mul (Real.pi : ℂ)).div_const
      (2 * ((τ.im : ℝ) : ℂ))).cexp
    simpa using this
  have h2 : deriv (expOddTheta τ) 0 = deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 := by
    have := (he.mul (GlobalTheory.ThetaWeberRoad.differentiable_oddTheta τ 0).hasDerivAt).deriv
    simp only [zero_mul, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, zero_div, Complex.exp_zero, one_mul] at this
    exact this
  have := hc z
  rw [expOddTheta] at this
  rw [this, ← h1, h2]

end GlobalTheory.SgStarOddTheta
end
end
