module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueBarCompatibility

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaleFractionalIdealIntegralAvoidMaximals
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaleFractionalIdealIntegralAvoidMaximals
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem exists_scale_integral_not_le_maximal :
  ∀ (E : Type) [Field E] [NumberField E] (I : Submodule (𝓞 E) E), I.FG → I ≠ ⊥ →
    ∀ (ι : Type) [Fintype ι] (Q : ι → Ideal (𝓞 E)), (∀ i, (Q i).IsMaximal) →
    ∃ s : E, s ≠ 0 ∧ (∀ a ∈ I, IsIntegral ℤ (s * a)) ∧ ∀ i, ∃ a ∈ I, ∃ o : 𝓞 E, (o : E) = s * a ∧ o ∉ Q i := by
  intro E _ _ I hfg hne ι _ Q hQ
  classical
  let F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨I, FractionalIdeal.isFractional_of_fg hfg⟩
  have hFcoe : (F : Submodule (𝓞 E) E) = I := rfl
  have hF0 : F ≠ 0 := by
    intro h
    apply hne
    rw [← hFcoe, h, FractionalIdeal.coe_zero]
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := FaithfulSMul.algebraMap_injective _ _
  have hint : ∀ s ∈ F⁻¹, ∀ a ∈ I, ∃ o : 𝓞 E, (o : E) = s * a := by
    intro s hs a ha
    have h1 := (FractionalIdeal.mem_inv_iff hF0).1 hs a ha
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h1
    exact ⟨o, ho⟩
  have key : ∀ P : Ideal (𝓞 E), P ≠ ⊤ →
      ∃ s ∈ F⁻¹, ∃ a ∈ I, ∃ o : 𝓞 E, (o : E) = s * a ∧ o ∉ P := by
    intro P hP
    by_contra h
    push_neg at h
    apply hP
    have hle : ((F * F⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) ≤
        Submodule.map (Algebra.linearMap (𝓞 E) E) P := by
      rw [FractionalIdeal.coe_mul, Submodule.mul_le]
      intro m hm n hn
      obtain ⟨o, ho⟩ := hint n hn m hm
      refine Submodule.mem_map.2 ⟨o, h n hn m hm o ho, ?_⟩
      rw [mul_comm, ← ho]; rfl
    rw [mul_inv_cancel₀ hF0, FractionalIdeal.coe_one] at hle
    have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.2 ⟨1, map_one _⟩
    obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.1 (hle h1)
    have : p = 1 := hinj (by rw [map_one]; exact hp1)
    exact (Ideal.eq_top_iff_one P).2 (this ▸ hp)
  choose! sf hsf af haf of hof hof' using key
  have hc : ∀ P' P : Ideal (𝓞 E), P'.IsMaximal → P.IsMaximal → P' ≠ P → ∃ c ∈ P', c ∉ P := by
    intro P' P hP' hP hne'
    by_contra h
    push_neg at h
    exact hne' (hP'.eq_of_le hP.ne_top h)
  choose! c hc1 hc2 using hc
  obtain ⟨M0, hM0⟩ := Ideal.exists_maximal (𝓞 E)
  let T : Finset (Ideal (𝓞 E)) := insert M0 (Finset.univ.image Q)
  have hT : ∀ P ∈ T, P.IsMaximal := by
    intro P hP
    rcases Finset.mem_insert.1 hP with h | h
    · exact h ▸ hM0
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact hQ i
  let u : Ideal (𝓞 E) → 𝓞 E := fun P => ∏ P' ∈ T.erase P, c P' P
  have hu1 : ∀ P ∈ T, u P ∉ P := by
    intro P hP hmem
    haveI := (hT P hP).isPrime
    obtain ⟨P', hP', hcP⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
    exact hc2 P' P (hT P' (Finset.mem_of_mem_erase hP')) (hT P hP) (Finset.ne_of_mem_erase hP') hcP
  have hu2 : ∀ P ∈ T, ∀ P' ∈ T, P' ≠ P → u P ∈ P' := by
    intro P hP P' hP' hne'
    have hm : P' ∈ T.erase P := Finset.mem_erase.2 ⟨hne', hP'⟩
    show ∏ P'' ∈ T.erase P, c P'' P ∈ P'
    rw [← Finset.mul_prod_erase _ _ hm]
    exact Ideal.mul_mem_right _ _ (hc1 P' P (hT P' hP') (hT P hP) hne')
  let s : E := ∑ P ∈ T, (u P : E) * sf P
  have hs : s ∈ F⁻¹ := by
    refine Submodule.sum_mem _ (fun P hP => ?_)
    have := Submodule.smul_mem ((F⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) (u P) (hsf P (hT P hP).ne_top)
    rwa [Algebra.smul_def] at this

  have main : ∀ P0 ∈ T, ∃ o : 𝓞 E, (o : E) = s * af P0 ∧ o ∉ P0 := by
    intro P0 hP0
    have hP0t := (hT P0 hP0).ne_top
    have hterm : ∀ P ∈ T, ∃ o : 𝓞 E, (o : E) = sf P * af P0 :=
      fun P hP => hint _ (hsf P (hT P hP).ne_top) _ (haf P0 hP0t)
    choose! w hw using hterm
    refine ⟨∑ P ∈ T, u P * w P, ?_, ?_⟩
    · push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun P hP => ?_)
      rw [mul_assoc, ← hw P hP]
    · intro hmem
      haveI := (hT P0 hP0).isPrime
      rw [← Finset.add_sum_erase _ _ hP0] at hmem
      have hrest : ∑ P ∈ T.erase P0, u P * w P ∈ P0 :=
        Ideal.sum_mem _ (fun P hP => Ideal.mul_mem_right _ _
          (hu2 P (Finset.mem_of_mem_erase hP) P0 hP0 (Finset.ne_of_mem_erase hP).symm))
      have h2 : u P0 * w P0 ∈ P0 := by
        have := P0.sub_mem hmem hrest
        simpa using this
      have hwo : w P0 = of P0 := hinj (by
        show (w P0 : E) = (of P0 : E)
        rw [hw P0 hP0, hof P0 hP0t])
      rcases Ideal.IsPrime.mem_or_mem ‹_› h2 with h3 | h3
      · exact hu1 P0 hP0 h3
      · exact hof' P0 hP0t (hwo ▸ h3)
  refine ⟨s, ?_, ?_, ?_⟩
  · intro hs0
    obtain ⟨o, ho, hno⟩ := main M0 (Finset.mem_insert_self _ _)
    rw [hs0, zero_mul] at ho
    have : o = 0 := hinj (by rw [map_zero]; exact ho)
    exact hno (this ▸ M0.zero_mem)
  · intro a ha
    obtain ⟨o, ho⟩ := hint s hs a ha
    rw [← ho]
    exact o.isIntegral_coe
  · intro i
    have hi : Q i ∈ T := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    obtain ⟨o, ho, hno⟩ := main (Q i) hi
    exact ⟨af (Q i), haf _ (hQ i).ne_top, o, ho, hno⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaleFractionalIdealIntegralAvoidMaximalsStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scale_fractionalIdeal_integral_avoid_maximals : ∀ (E : Type) [Field E] [NumberField E] (I : Submodule (𝓞 E) E), I.FG → I ≠ ⊥ →
    ∀ (ι : Type) [Fintype ι] (Q : ι → Ideal (𝓞 E)), (∀ i, (Q i).IsMaximal) →
    ∃ s : E, s ≠ 0 ∧ (∀ a ∈ I, IsIntegral ℤ (s * a)) ∧ ∀ i, ∃ a ∈ I, ∃ o : 𝓞 E, (o : E) = s * a ∧ o ∉ Q i := by
  first | exact @GlobalTheory.exists_scale_integral_not_le_maximal | exact GlobalTheory.exists_scale_integral_not_le_maximal | (intros; apply GlobalTheory.exists_scale_integral_not_le_maximal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitEmbeddingIntegralAndMaximalIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitEmbeddingIntegralAndMaximalIdeal
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

theorem GlobalTheory.adicEmbedding_integral_place (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] v.adicCompletion F) :
    (∀ a : 𝓞 E, Valued.v (τ a) ≤ 1) ∧ ∃ Q : Ideal (𝓞 E), Q.IsMaximal ∧ ∀ a : 𝓞 E, a ∈ Q ↔ Valued.v (τ a) < 1 := by
  set O := v.adicCompletionIntegers F
  have hv : (Valued.v : Valuation (v.adicCompletion F) _).Integers O := by
    have := Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)
    exact this
  have ha : ∀ a : 𝓞 E, Valued.v (τ a) ≤ 1 := by
    intro a
    have h1 : IsIntegral ℤ (τ a) := IsIntegral.map τ (NumberField.RingOfIntegers.isIntegral_coe a)
    have h2 : IsIntegral O (τ a) := h1.tower_top
    exact hv.mem_of_integral h2
  refine ⟨ha, ?_⟩
  let φ : 𝓞 E →+* O :=
    ((τ : E →+* v.adicCompletion F).comp (algebraMap (𝓞 E) E)).codRestrict O.toSubring
      (fun a => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 (ha a))
  have hmem : ∀ a : 𝓞 E, a ∈ (IsLocalRing.maximalIdeal O).comap φ ↔ Valued.v (τ a) < 1 := by
    intro a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one]
    change ¬ Valued.v (τ a) = 1 ↔ _
    exact ⟨fun h => lt_of_le_of_ne (ha a) h, fun h => ne_of_lt h⟩
  refine ⟨(IsLocalRing.maximalIdeal O).comap φ, ?_, hmem⟩
  apply Ideal.IsPrime.isMaximal inferInstance
  intro hbot
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hlt : Valued.v (algebraMap F (v.adicCompletion F) (π : F)) < 1 := by
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v π).2 hπ
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at this
    exact this
  have hne : (algebraMap (𝓞 F) (𝓞 E) π) ≠ 0 := by
    intro h
    apply hπ0
    apply FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)
    simpa using h
  apply hne
  have : algebraMap (𝓞 F) (𝓞 E) π ∈ (IsLocalRing.maximalIdeal O).comap φ := by
    rw [hmem]
    have e : ((algebraMap (𝓞 F) (𝓞 E) π : 𝓞 E) : E) = algebraMap F E (π : F) := by
      exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E π).symm.trans (IsScalarTower.algebraMap_apply (𝓞 F) F E π)
    rw [e, AlgHom.commutes]
    exact hlt
  rw [hbot] at this
  simpa using this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitEmbeddingIntegralAndMaximalIdealStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitEmbedding_integral_and_maximalIdeal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] v.adicCompletion F),
    (∀ a : 𝓞 E, Valued.v (τ a) ≤ 1) ∧ ∃ Q : Ideal (𝓞 E), Q.IsMaximal ∧ ∀ a : 𝓞 E, a ∈ Q ↔ Valued.v (τ a) < 1 := by
  first | exact @GlobalTheory.adicEmbedding_integral_place | exact GlobalTheory.adicEmbedding_integral_place | (intros; apply GlobalTheory.adicEmbedding_integral_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPairSelfDualLatticeIsotropic
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.HypPairLat

theorem form_smul_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (c : E) (z w : Fin n → E) : form σ J (c • z) w = c * form σ J z w := by
  simp [form, smul_dotProduct]

theorem form_smul_right {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (c : E) (z w : Fin n → E) : form σ J z (c • w) = σ c * form σ J z w := by
  have : (fun i => σ ((c • w) i)) = σ c • fun i => σ (w i) := by ext i; simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_conj {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (z w : Fin n → E) :
    σ (form σ J z w) = form σ J w z := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem isIntegral_sigma {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {e : E}
    (h : IsIntegral ℤ e) : IsIntegral ℤ (σ e) :=
  h.map (σ.toRingHom.toIntAlgHom)

theorem exists_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), Y.IsHerm σ B r s →
    ∀ x : Fin n → E, x ≠ 0 → form σ Y.J x x = 0 →
    ∃ x' y : Fin n → E, form σ Y.J x' x' = 0 ∧ form σ Y.J y y = 0 ∧ form σ Y.J x' y = 1 ∧
      (∀ z ∈ Y.L, form σ Y.J z y • x' ∈ Y.L ∧ form σ Y.J z x' • y ∈ Y.L) ∧
      ∀ v : B.P, ((∀ c : E, c • x' ∈ Y.L → Valued.v (B.τ v c) ≤ 1) ∧ ∃ c : E, c • x' ∈ Y.L ∧ Valued.v (B.τ v c) = 1) ∧
        ((∀ c : E, c • y ∈ Y.L → Valued.v (B.τ v c) ≤ 1) ∧ ∃ c : E, c • y ∈ Y.L ∧ Valued.v (B.τ v c) = 1) := by
  intro F E _ _ _ _ _ σ B hB n Y r s hY x hx0 hxx
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := by haveI := hB.unram; infer_instance
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm hfu
  have hfg : Y.L.FG := hY.lat.fg
  obtain ⟨z0, hz0L, hz0⟩ := GlobalTheory.T.selfDual_hermitianLattice_exists_nonzero_pairing F E σ hσ n Y.J Y.L hfg hY.herm hY.dual x hx0
  let f : (Fin n → E) →ₗ[𝓞 E] E :=
    { toFun := fun z => form σ Y.J z x
      map_add' := fun a b => by simp [form, add_dotProduct]
      map_smul' := fun c a => by
        show form σ Y.J ((c : E) • a) x = (c : E) * form σ Y.J a x
        exact form_smul_left σ Y.J (c : E) a x }
  have hf : ∀ z, f z = form σ Y.J z x := fun z => rfl
  let I₀ : Submodule (𝓞 E) E := Y.L.map f
  have hI₀fg : I₀.FG := hfg.map f
  have hI₀ne : I₀ ≠ ⊥ := by
    intro h
    have : f z0 ∈ I₀ := Submodule.mem_map_of_mem hz0L
    rw [h, Submodule.mem_bot] at this
    exact hz0 this
  have hT4 := fun (v : B.P) (b : Bool) => GlobalTheory.T.splitEmbedding_integral_and_maximalIdeal F E v.1 (if b then (B.τ v).comp σ else B.τ v)
  choose hle Q hQmax hQ using hT4
  obtain ⟨s, hs0, hsI, hsQ⟩ := GlobalTheory.T.exists_scale_fractionalIdeal_integral_avoid_maximals E I₀ hI₀fg hI₀ne (B.P × Bool) (fun p => Q p.1 p.2) (fun p => hQmax _ _)
  set x' : Fin n → E := σ s • x with hx'def
  have hfx' : ∀ z, form σ Y.J z x' = s * form σ Y.J z x := fun z => by
    rw [hx'def, form_smul_right, hσ]
  have hx'x' : form σ Y.J x' x' = 0 := by
    rw [hfx', hx'def, form_smul_left, hxx, mul_zero, mul_zero]
  obtain ⟨y₀, hy₀1, hy₀L⟩ := GlobalTheory.T.exists_section_hermitianLinearForm_fg_module F E σ n Y.J Y.L hfg x' ⟨z0, hz0L, by rw [hfx']; exact mul_ne_zero hs0 hz0⟩
  obtain ⟨y, hyy, hx'y, hL⟩ := GlobalTheory.T.exists_isotropic_dual_partner_selfDual_hermitianLattice F E σ hσ n Y.J Y.L hY.herm hY.dual θ hθ x' y₀ hx'x' hy₀1 hy₀L
  have hint : ∀ z ∈ Y.L, IsIntegral ℤ (form σ Y.J z x') := fun z hz => by
    rw [hfx']; exact hsI _ (Submodule.mem_map_of_mem hz)
  have hx'L : x' ∈ Y.L := (hY.dual x').2 fun w hw => by
    rw [← form_conj σ hσ Y.J hY.herm]; exact isIntegral_sigma σ (hint w hw)
  have hyx' : form σ Y.J y x' = 1 := by
    rw [← form_conj σ hσ Y.J hY.herm, hx'y, map_one]

  have hval : ∀ (v : B.P) (b : Bool) (e : E), IsIntegral ℤ e →
      Valued.v ((if b then (B.τ v).comp σ else B.τ v) e) ≤ 1 := fun v b e he =>
    hle v b ⟨e, he⟩
  have hwit : ∀ (v : B.P) (b : Bool), ∃ z ∈ Y.L, IsIntegral ℤ (form σ Y.J z x') ∧
      Valued.v ((if b then (B.τ v).comp σ else B.τ v) (form σ Y.J z x')) = 1 := by
    intro v b
    obtain ⟨a, ha, o, ho, hoQ⟩ := hsQ (v, b)
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 ha
    refine ⟨z, hz, hint z hz, ?_⟩
    have h1 := hle v b o
    have h2 : ¬ Valued.v ((if b then (B.τ v).comp σ else B.τ v) (o : E)) < 1 := fun h => hoQ ((hQ v b o).2 h)
    rw [ho, hf, ← hfx'] at h1 h2
    exact le_antisymm h1 (not_lt.1 h2)
  refine ⟨x', y, hx'x', hyy, hx'y, hL, fun v => ⟨⟨fun c hc => ?_, 1, by rw [one_smul]; exact hx'L, by simp⟩,
    ⟨fun c hc => ?_, ?_⟩⟩⟩
  · obtain ⟨z, hz, -, hz1⟩ := hwit v true
    have hi : IsIntegral ℤ (form σ Y.J (c • x') z) := (hY.dual _).1 hc z hz
    rw [form_smul_left, ← form_conj σ hσ Y.J hY.herm z x'] at hi
    have := hval v false _ hi
    simp only [Bool.false_eq_true, ↓reduceIte, map_mul] at this
    simp only [↓reduceIte, AlgHom.comp_apply] at hz1
    rw [hz1, mul_one] at this
    exact this
  · have hi := hint _ hc
    rw [form_smul_left, hyx', mul_one] at hi
    simpa using hval v false c hi
  · obtain ⟨z, hz, -, hz1⟩ := hwit v false
    exact ⟨form σ Y.J z x', (hL z hz).2, by simpa using hz1⟩

end GlobalTheory.HypPairLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPairSelfDualLatticeIsotropicStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hyperbolicPair_selfDualLattice_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), Y.IsHerm σ B r s →
    ∀ x : Fin n → E, x ≠ 0 → form σ Y.J x x = 0 →
    ∃ x' y : Fin n → E, form σ Y.J x' x' = 0 ∧ form σ Y.J y y = 0 ∧ form σ Y.J x' y = 1 ∧
      (∀ z ∈ Y.L, form σ Y.J z y • x' ∈ Y.L ∧ form σ Y.J z x' • y ∈ Y.L) ∧
      ∀ v : B.P, ((∀ c : E, c • x' ∈ Y.L → Valued.v (B.τ v c) ≤ 1) ∧ ∃ c : E, c • x' ∈ Y.L ∧ Valued.v (B.τ v c) = 1) ∧
        ((∀ c : E, c • y ∈ Y.L → Valued.v (B.τ v c) ≤ 1) ∧ ∃ c : E, c • y ∈ Y.L ∧ Valued.v (B.τ v c) = 1) := by
  first | exact @GlobalTheory.HypPairLat.exists_pair | exact GlobalTheory.HypPairLat.exists_pair | (intros; apply GlobalTheory.HypPairLat.exists_pair <;> assumption)
end
