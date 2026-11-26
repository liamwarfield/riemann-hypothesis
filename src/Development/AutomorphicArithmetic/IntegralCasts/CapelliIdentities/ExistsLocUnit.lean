module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnramifiedAntiInvariantLocal
open NumberField

theorem UpperTheory.unramified_anti_invariant_local :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      Module.finrank F E = 2 →
      Algebra.Unramified (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers E) →
      ∀ (ξ : E), ξ ≠ 0 → σ ξ = -ξ →
      ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
        ∃ (a b : NumberField.RingOfIntegers E) (n : NumberField.RingOfIntegers F),
          n ∉ v.asIdeal ∧ σ (a : E) = -(a : E) ∧ (a : E) * (b : E) = algebraMap F E (n : F) := by
  intro F E _ _ _ _ _ σ hr hU ξ hξ hσ v
  have hne : σ ξ ≠ ξ := by
    intro h
    rw [hσ] at h
    exact hξ (by linear_combination (-1 / 2 : E) * h)
  have hfix : ∀ y : E, σ y = y → ∃ c : F, algebraMap F E c = y := by
    intro y hy
    have := Subalgebra.isSimpleOrder_of_finrank hr
    rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
    · have : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := hy
      rw [h] at this
      exact Algebra.mem_bot.mp this
    · have : ξ ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
      exact absurd this hne
  have hinv : ∀ y : E, σ (σ y) = y := by
    intro y
    have := Subalgebra.isSimpleOrder_of_finrank hr
    rcases eq_bot_or_eq_top (AlgHom.equalizer (σ.comp σ) (AlgHom.id F E)) with h | h
    · have : ξ ∈ AlgHom.equalizer (σ.comp σ) (AlgHom.id F E) := by
        show σ (σ ξ) = ξ
        rw [hσ, map_neg, hσ, neg_neg]
      rw [h] at this
      obtain ⟨c, hc⟩ := Algebra.mem_bot.mp this
      exact absurd (by rw [← hc, AlgHom.commutes]) hne
    · have : y ∈ AlgHom.equalizer (σ.comp σ) (AlgHom.id F E) := by rw [h]; trivial
      exact this
  let τ : 𝓞 E →ₐ[𝓞 F] 𝓞 E := RingOfIntegers.mapAlgHom σ
  have hτ : ∀ x : 𝓞 E, ((τ x : 𝓞 E) : E) = σ x := fun _ => rfl
  have := v.isMaximal
  obtain ⟨w, hw, hwv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hx : ∃ x : 𝓞 E, x - τ x ∉ w := by
    by_contra hcon
    push Not at hcon
    have heq : AlgHom.id (𝓞 F) (𝓞 E) = τ :=
      Algebra.FormallyUnramified.ext_of_iInf w (Ideal.iInf_pow_eq_bot_of_isDomain w hw.ne_top)
        (fun x => Ideal.Quotient.eq.mpr (hcon x))
    have hall : ∀ x : 𝓞 E, σ x = x := fun x => by rw [← hτ, ← heq]; rfl
    obtain ⟨p, q, -, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 E) ξ
    apply hne
    rw [← hpq, map_div₀]
    exact congrArg₂ (· / ·) (hall p) (hall q)
  obtain ⟨x, hx⟩ := hx
  set a : 𝓞 E := x - τ x with ha
  have hσa : σ (a : E) = -(a : E) := by
    have : (a : E) = x - σ x := by rw [← hτ]; rfl
    rw [this, map_sub, hinv, neg_sub]
  obtain ⟨c, hc⟩ := hfix ((a : E) * a) (by rw [map_mul, hσa, neg_mul_neg])
  have hci : IsIntegral ℤ c := by
    rw [← isIntegral_algebraMap_iff (B := E) , hc]
    exact a.isIntegral_coe.mul a.isIntegral_coe
  refine ⟨a, a, ⟨c, hci⟩, ?_, hσa, hc.symm⟩
  intro hn
  have h1 := (Ideal.mem_of_liesOver w v.asIdeal _).mp hn
  have h2 : algebraMap (𝓞 F) (𝓞 E) ⟨c, hci⟩ = a * a := by
    apply RingOfIntegers.ext
    exact hc
  rw [h2] at h1
  exact hx ((hw.isPrime.mem_or_mem h1).elim id id)
end

private theorem inv_mem {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (n : NumberField.RingOfIntegers F) (hn : n ∉ v.asIdeal) :
    algebraMap F (v.adicCompletion F) (n : F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : v.valuation F (n : F) = 1 := by
    have := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) v (r := n)).2 hn
    exact this
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have h2 := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((n : F)⁻¹)
  refine le_of_eq (Eq.trans h2 ?_)
  rw [map_inv₀, h1, inv_one]

theorem UpperTheory.Reformulated.B.Gs6.exists_locUnit :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {σ : E →ₐ[F] E} {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E},
      UpperTheory.TP.W.GoodK σ B →
        ∀ {ξ : E},
          ξ ≠ (0 : E) →
            (σ : E → E) ξ = -ξ →
              ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
                ∃ (u : (TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E)ˣ),
                  (↑u : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E) ∈ GlobalTheory.AdelicU.intLoc F E v ∧
                    (↑u⁻¹ : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E) ∈ GlobalTheory.AdelicU.intLoc F E v ∧
                      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ :
                                  TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E → TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E)
                                (↑u : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E) =
                        -(↑u : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E) := by
  intro F E _ _ _ _ _ σ B hG ξ hξ hσ v
  obtain ⟨hCM, -, hU, -, -, -⟩ := hG
  obtain ⟨a, b, n, hn, ha, hab⟩ := UpperTheory.unramified_anti_invariant_local σ hCM.2.2.1 hU ξ hξ hσ v
  have hn0 : (n : F) ≠ 0 := by
    intro h
    apply hn
    have : n = 0 := by exact_mod_cast h
    rw [this]; exact v.asIdeal.zero_mem
  have hmul : ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (a : E)) *
      (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (n : F)⁻¹ ⊗ₜ[F] (b : E)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, hab, one_mul, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul_smul, inv_mul_cancel₀ hn0, one_smul]
    rfl
  refine ⟨⟨_, _, hmul, by rw [mul_comm]; exact hmul⟩, ?_, ?_, ?_⟩
  · exact AddSubgroup.subset_closure ⟨1, one_mem _, a, rfl⟩
  · exact AddSubgroup.subset_closure ⟨_, inv_mem v n hn, b, rfl⟩
  · change Algebra.TensorProduct.map (AlgHom.id F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) σ (1 ⊗ₜ[F] (a : E)) = -(1 ⊗ₜ[F] (a : E))
    rw [Algebra.TensorProduct.map_tmul, ha, map_one, TensorProduct.tmul_neg]
