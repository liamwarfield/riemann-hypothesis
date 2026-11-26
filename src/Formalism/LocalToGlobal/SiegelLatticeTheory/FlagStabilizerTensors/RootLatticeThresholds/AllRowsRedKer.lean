module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKerA

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKer
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.AllRowsRedKer

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.MainNotions.BridgeLemma

variable {D : D7}

def sigH (D : D7) : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv

theorem sigH_coe (a : 𝓞 D.host.E) : ((sigH D a : 𝓞 D.host.E) : D.host.E) = D.host.conj (a : D.host.E) := rfl

def conjH (w : HeightOneSpectrum (𝓞 D.host.E)) : HeightOneSpectrum (𝓞 D.host.E) where
  asIdeal := w.asIdeal.comap (sigH D)
  isPrime := by have := w.isPrime; exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := Ideal.map_comap_of_surjective _ (sigH D).surjective w.asIdeal
    rw [← this, h, Ideal.map_bot]

theorem conj_conj (X : HidaSetting D) (y : D.host.E) : D.host.conj (D.host.conj y) = y := by
  obtain ⟨x, rfl⟩ := X.ιE.surjective y
  rw [← X.ιE_conj, ← X.ιE_conj, star_star]

theorem sigH_sigH (X : HidaSetting D) (a : 𝓞 D.host.E) : sigH D (sigH D a) = a := by
  apply RingOfIntegers.ext
  rw [sigH_coe, sigH_coe]
  exact conj_conj X _

theorem conjH_conjH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : conjH (conjH w) = w := by
  apply HeightOneSpectrum.ext
  show (w.asIdeal.comap (sigH D)).comap (sigH D) = w.asIdeal
  ext a
  simp only [Ideal.mem_comap]
  rw [sigH_sigH X]

theorem isConjPl_conjH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : IsConjPl D.host w (conjH w) := by
  intro x y hxy
  have hs : sigH D y = x := by
    apply RingOfIntegers.ext
    rw [sigH_coe, hxy, conj_conj X]
  show x ∈ w.asIdeal ↔ sigH D y ∈ w.asIdeal
  rw [hs]

theorem natCast_mem_conjH {w : HeightOneSpectrum (𝓞 D.host.E)} {p : ℕ} (h : (p : 𝓞 D.host.E) ∈ w.asIdeal) :
    (p : 𝓞 D.host.E) ∈ (conjH w).asIdeal := by
  show sigH D (p : 𝓞 D.host.E) ∈ w.asIdeal
  rw [map_natCast]
  exact h

theorem wB_conjH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : wB X (conjH w) = wc X.B.I (wB X w) := by
  apply HeightOneSpectrum.ext
  ext a
  rw [mem_wc]
  simp only [wB, conjH, Ideal.mem_comap]
  have hc : sigH D (RingOfIntegers.mapRingEquiv X.ιE a) =
      RingOfIntegers.mapRingEquiv X.ιE (sigO X.B.I a) := by
    apply RingOfIntegers.ext
    rw [sigH_coe]
    simp [RingOfIntegers.mapRingEquiv, sigO_coe, X.ιE_conj]
  rw [hc]

theorem finrank_cmField (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  haveI := D.host.galois
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr D.host.gal.toEquiv, Formalism.HC.Frame.natCard_GG]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
  ring

theorem cover (X : HidaSetting D) (k : Fin 2) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ∃ v, w = D.naut.plGw k v ∨ w = conjH (D.naut.plGw k v) := by
  have hp := D.host.g_prime k
  set A : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
    Set.range (D.naut.plGw k) ∪ Set.range (fun v => conjH (D.naut.plGw k v)) with hA
  set T : Set (HeightOneSpectrum (𝓞 D.host.E)) := placesOver D.host.E (D.host.g k) with hT
  have hAT : A ⊆ T := by
    rintro _ (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · exact D.naut.plGw_over k v
    · exact natCast_mem_conjH (D.naut.plGw_over k v)
  have hTfin : T.Finite := finite_plOver D.host.E hp
  have hinj2 : Function.Injective (fun v => conjH (D.naut.plGw k v)) := by
    intro v v' h
    apply D.naut.plGw_inj k
    have := congrArg conjH h
    simpa only [conjH_conjH X] using this
  have hdisj : Disjoint (Set.range (D.naut.plGw k)) (Set.range (fun v => conjH (D.naut.plGw k v))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, rfl⟩ ⟨v', hv'⟩
    apply D.naut.plGw_nconj k v' v
    have := isConjPl_conjH X (D.naut.plGw k v')
    have hv'' : conjH (D.naut.plGw k v') = D.naut.plGw k v := hv'
    rw [hv''] at this
    exact this
  have hcA : A.ncard = 2 * D.R.f := by
    rw [hA, Set.ncard_union_eq hdisj (Set.finite_range _) (Set.finite_range _),
      Set.ncard_range_of_injective (D.naut.plGw_inj k), Set.ncard_range_of_injective hinj2,
      Nat.card_eq_fintype_card, D.nd.card_PlG k]
    ring
  have hcT : T.ncard = 2 * D.R.f := by rw [hT, D.nd.g_split k, finrank_cmField]
  have hEq : A = T := Set.eq_of_subset_of_ncard_le hAT (by rw [hcA, hcT]) hTfin
  have : w ∈ A := by rw [hEq]; exact hw
  rcases this with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · exact ⟨v, Or.inl rfl⟩
  · exact ⟨v, Or.inr rfl⟩

theorem unram (X : HidaSetting D) (k : Fin 2) (P : Ideal (𝓞 X.B.I.E)) (hPm : P.IsMaximal)
    (hgP : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P) : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∉ P ^ 2 := by
  have hp := D.host.g_prime k
  have := span_isMaximal hp
  have hspl := splitsCompl_of_ncard D.host.E (D.host.g k) hp (by
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hp) (𝓞 D.host.E), ← image_plOver _ hp,
      (injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k)
  set e : 𝓞 X.B.I.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv X.ιE
  have hQm : (P.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
  have hgQ : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.map e := by
    have := Ideal.mem_map_of_mem e hgP
    rwa [map_natCast] at this
  obtain ⟨-, hsq⟩ := hspl _ hQm hgQ
  intro h
  apply hsq
  have := Ideal.mem_map_of_mem e h
  rwa [map_natCast, Ideal.map_pow] at this

def toH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 X.B.I.E)) : HeightOneSpectrum (𝓞 D.host.E) where
  asIdeal := w.asIdeal.comap (RingOfIntegers.mapRingEquiv X.ιE).symm
  isPrime := by have := w.isPrime; exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv X.ιE).symm.surjective w.asIdeal
    rw [← this, h, Ideal.map_bot]

theorem wB_toH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 X.B.I.E)) : wB X (toH X w) = w := by
  apply HeightOneSpectrum.ext
  ext a
  simp [wB, toH, Ideal.mem_comap]

theorem redKerP_holds (X : HidaSetting D) (k : Fin 2) : Formalism.L2.SG.AllRowsOf.RedKerP X k := by
  intro x hx hred
  have hp := D.host.g_prime k
  have hA : ∀ v, ∀ y ∈ X.B.I.Lf, (X.B.I.fmat x - 1) *ᵥ y ∈ Lq X.B.I (wB X (D.naut.plGw k v)) := by
    intro v
    have h0 := (redMat_iff X _ _ x _).1 (hred v)
    exact stepA X.B.I hp (by rw [card_wB, card_res_host]) hx h0
  refine glue X.B.I hp (unram X k) hx fun w hw => ?_
  have hwH : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (toH X w).asIdeal := by
    show (RingOfIntegers.mapRingEquiv X.ιE).symm ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
    rw [map_natCast]; exact hw
  obtain ⟨v, hv | hv⟩ := cover X k (toH X w) hwH
  · rw [← wB_toH X w, hv]
    exact hA v
  · rw [← wB_toH X w, hv, wB_conjH X]
    exact stepB X.B.I hx (hA v)

end Formalism.L2.SG.Pf.AllRowsRedKer
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRMul
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.AllRowsRMul

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

abbrev phi (x y : X.B.I.L2 X.B.μf X.B.fund) (c : X.B.I.Gf) : ℂ := ⟪x, X.B.R (1, c) y⟫_ℂ

theorem R_facts :
    (∀ a b : X.B.I.GA, X.B.R (a * b) = (X.B.R a).comp (X.B.R b)) ∧ (∀ a F, ‖X.B.R a F‖ = ‖F‖) ∧
      (∀ x y : X.B.I.L2 X.B.μf X.B.fund, StronglyMeasurable (phi X x y)) := by
  have : X.B.μf.IsHaarMeasure := X.B.haar
  have hU := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have hFR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  have := hFR.2.1
  have := hFR.2.2.2.1
  have : X.B.μf.IsMulRightInvariant := hU
  have : (X.B.I.muA X.B.μf).IsMulLeftInvariant := rr_muA_left X.B.I X.B.μf
  have : (X.B.I.muA X.B.μf).IsMulRightInvariant := rr_muA_right X.B.I X.B.μf
  have : SigmaFinite (X.B.I.muA X.B.μf) := rr_muA_sigmaFinite X.B.I X.B.μf
  have h1 := rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec
  have h2 := rr_IsReg_of X.B.I X.B.μf X.B.fund X.B.R X.B.R_spec
  refine ⟨fun a b => rr_mul h1 h2 a b, fun a F => rr_norm h1 h2 a F, fun x y => ?_⟩
  exact (rr_weak_meas h1 h2 x y).comp_measurable (measurable_const.prodMk measurable_id)

theorem phi_bound (x y : X.B.I.L2 X.B.μf X.B.fund) (c : X.B.I.Gf) : ‖phi X x y c‖ ≤ ‖x‖ * ‖y‖ := by
  have h := (R_facts X).2.1 (1, c) y
  calc ‖phi X x y c‖ ≤ ‖x‖ * ‖X.B.R (1, c) y‖ := norm_inner_le_norm _ _
    _ = ‖x‖ * ‖y‖ := by rw [h]

theorem isRConvF_conv {f g : X.B.I.Gf → ℂ} {T U : X.B.I.L2 X.B.μf X.B.fund →L[ℂ] X.B.I.L2 X.B.μf X.B.fund}
    (hf : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R f T) (hg : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R g U) :
    X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (X.B.I.convF X.B.μf f g) (T.comp U) := by
  obtain ⟨hmul, -, hmeas⟩ := R_facts X
  have : X.B.μf.IsHaarMeasure := X.B.haar
  have : SecondCountableTopology X.B.I.Gf := rr_secondCountable X.B.I X.B.μf
  have hK : Integrable (fun p : X.B.I.Gf × X.B.I.Gf => f p.1 * g (p.1⁻¹ * p.2)) (X.B.μf.prod X.B.μf) := by
    have h0 : Integrable (fun q : X.B.I.Gf × X.B.I.Gf => f q.1 * g q.2) (X.B.μf.prod X.B.μf) := hf.1.mul_prod hg.1
    exact ((measurePreserving_prod_inv_mul X.B.μf X.B.μf).integrable_comp h0.aestronglyMeasurable).2 h0
  have hF : ∀ x y : X.B.I.L2 X.B.μf X.B.fund, Integrable (fun p : X.B.I.Gf × X.B.I.Gf =>
      f p.1 * g (p.1⁻¹ * p.2) * phi X x y p.2) (X.B.μf.prod X.B.μf) := fun x y =>
    hK.mul_bdd ((hmeas x y).comp_measurable measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => phi_bound X x y p.2)
  refine ⟨hK.integral_prod_right, fun x y => ?_⟩
  have step : ∀ a, ⟪x, X.B.R (1, a) (U y)⟫_ℂ = ∫ c, g (a⁻¹ * c) * phi X x y c ∂X.B.μf := by
    intro a
    rw [← ContinuousLinearMap.adjoint_inner_left, hg.2]
    have e : ∀ b, g b * ⟪ContinuousLinearMap.adjoint (X.B.R (1, a)) x, X.B.R (1, b) y⟫_ℂ =
        g b * phi X x y (a * b) := by
      intro b
      rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← hmul, Prod.mk_mul_mk, one_mul]
    simp_rw [e]
    rw [← integral_mul_left_eq_self (fun c => g (a⁻¹ * c) * phi X x y c) a]
    congr 1
    funext b
    simp only [inv_mul_cancel_left]
  rw [ContinuousLinearMap.comp_apply, hf.2]
  simp_rw [step, ← integral_const_mul]
  have hF' : Integrable (Function.uncurry fun a c => f a * (g (a⁻¹ * c) * phi X x y c)) (X.B.μf.prod X.B.μf) := by
    have := hF x y
    simp only [mul_assoc] at this
    exact this
  rw [integral_integral_swap hF']
  congr 1
  funext c
  unfold AutInst.convF
  rw [← integral_mul_const]
  congr 1
  funext a
  ring

end Formalism.L2.SG.Pf.AllRowsRMul
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRho
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.AllRowsRho

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence
  Formalism.L2.SG.Pf.AllRowsRedKerA

variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))

def RedMatB (p : ℕ) {m : ℕ} (b : Fin m → Fin I.n → I.E) (x : I.Gf) (M : Matrix (Fin m) (Fin m) (ZMod p)) : Prop :=
  ∀ i, I.fmat x *ᵥ iv I (b i) - ∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w

theorem redMat0_of {p m : ℕ} {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) {x : I.Gf}
    {M : Matrix (Fin m) (Fin m) (ZMod p)} (h : RedMatB I w p b x M) : RedMat0 I w p x M := ⟨b, hb, h⟩

theorem natSmul_Lq (k : ℕ) {z : Fin I.n → I.E ⊗[I.F] Af I.F} (hz : z ∈ Lq I w) :
    (k : I.E ⊗[I.F] Af I.F) • z ∈ Lq I w := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hz k

theorem redMatB_exists {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ}
    {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) {x : I.Gf} (hx : x ∈ I.Kset) :
    ∃ M : Matrix (Fin m) (Fin m) (ZMod p), RedMatB I w p b x M := by
  have : NeZero p := ⟨hp.ne_zero⟩
  choose c hc using fun i => coords I w hp hcard hb (K_mv I hx (DictLat.iv_mem I (hb.1 i)))
  refine ⟨Matrix.of fun j i => ((c i j : ℤ) : ZMod p), fun i => ?_⟩
  have h2 : ∑ j, ((((c i j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) -
      ∑ j, (c i j : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    exact sum_mem fun j _ => val_sub I w hp hcard (hb.1 j) (c i j)
  have := sub_mem (hc i) h2
  convert this using 1
  simp only [Matrix.of_apply]
  abel

theorem mkQ_natSmul (k : ℕ) (v : Fin I.n → I.E ⊗[I.F] Af I.F) :
    (Lq I w).mkQ ((k : I.E ⊗[I.F] Af I.F) • v) = ((k : ℤ)) • (Lq I w).mkQ v := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, natCast_zsmul]

theorem redMatB_unique {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ} (hm : m = I.n)
    {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) {x : I.Gf} {M M' : Matrix (Fin m) (Fin m) (ZMod p)}
    (h : RedMatB I w p b x M) (h' : RedMatB I w p b x M') : M = M' := by
  subst hm
  have : NeZero p := ⟨hp.ne_zero⟩
  ext j i
  have hdiff : ∑ l, (((M' l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l) -
      ∑ l, (((M l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l) ∈ Lq I w := by
    have := sub_mem (h i) (h' i)
    convert this using 1
    abel
  have hz : ∑ l, ((((M' l i).val : ℕ) : ℤ) - (((M l i).val : ℕ) : ℤ)) • (Lq I w).mkQ (iv I (b l)) = 0 := by
    have h0 : (Lq I w).mkQ (∑ l, (((M' l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l) -
        ∑ l, (((M l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hdiff
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, map_sum] at h0
    simp only [mkQ_natSmul] at h0
    rw [← h0, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => sub_smul _ _ _
  have hj := Formalism.L2.SG.Pf.RedConj0Pf.zcoef_A I w p hp hcard hb _ hz j
  have hj' : ((M' j i).val : ZMod p) - ((M j i).val : ZMod p) = 0 := by exact_mod_cast hj
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, sub_eq_zero] at hj'
  exact hj'.symm

theorem redMatB_mul {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ}
    {b : Fin m → Fin I.n → I.E} (hb : ∀ i, b i ∈ I.L) {x y : I.Gf} (hx : x ∈ I.Kset)
    {M N : Matrix (Fin m) (Fin m) (ZMod p)} (hM : RedMatB I w p b x M) (hN : RedMatB I w p b y N) :
    RedMatB I w p b (x * y) (M * N) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  intro i
  have hAB : I.fmat (x * y) = I.fmat x * I.fmat y := rfl
  have s1 : I.fmat x *ᵥ (I.fmat y *ᵥ iv I (b i)) -
      ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ iv I (b k)) ∈ Lq I w := by
    have := stab_w I w hx (hN i)
    rw [Matrix.mulVec_sub, Matrix.mulVec_sum] at this
    simpa only [Matrix.mulVec_smul] using this
  have s2 : ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ iv I (b k)) -
      ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) •
        ∑ j, (((M j k).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun k _ => ?_
    rw [← smul_sub]
    exact natSmul_Lq I w _ (hM k)
  have e3 : ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) •
        ∑ j, (((M j k).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) =
      ∑ j, (((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j) := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Int.cast_natCast, Nat.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.cast_mul, mul_comm]
  have s3 : ∑ j, (((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j) -
      ∑ j, ((((M * N) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun j _ => ?_
    have hc : (((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ) : ZMod p) = (M * N) j i := by
      rw [Int.cast_natCast, Nat.cast_sum, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have := val_sub I w hp hcard (hb j) ((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ)
    rw [hc] at this
    have := neg_mem this
    rwa [neg_sub] at this
  rw [e3] at s2
  have := add_mem (add_mem s1 s2) s3
  rw [hAB, ← Matrix.mulVec_mulVec]
  convert this using 1
  abel

theorem redMatB_one {p : ℕ} (hp : p.Prime) {m : ℕ} (b : Fin m → Fin I.n → I.E) :
    RedMatB I w p b 1 (1 : Matrix (Fin m) (Fin m) (ZMod p)) := by
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  intro i
  have e : ∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod p)) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) =
      iv I (b i) := by
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.one_apply_eq, ZMod.val_one, Nat.cast_one, one_smul]
    · intro j _ hj; simp [Matrix.one_apply_ne hj]
    · simp
  rw [e, fmat_one, Matrix.one_mulVec, sub_self]
  exact zero_mem _

structure RedB (I : AutInst) (m : ℕ) where
  w : HeightOneSpectrum (𝓞 I.E)
  p : ℕ
  hp : p.Prime
  hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p
  hm : m = I.n
  b : Fin m → Fin I.n → I.E
  hb : IsRedBasis0 I w b

variable {I} {m : ℕ}


open Classical in
def matB (R : RedB I m) (x : I.Gf) : Matrix (Fin m) (Fin m) (ZMod R.p) :=
  if hx : x ∈ I.Kset then Classical.choose (redMatB_exists I R.w R.hp R.hcard R.hb hx) else 0

theorem matB_spec (R : RedB I m) {x : I.Gf} (hx : x ∈ I.Kset) : RedMatB I R.w R.p R.b x (matB R x) := by
  unfold matB; rw [dite_eq_left hx]; exact Classical.choose_spec (redMatB_exists I R.w R.hp R.hcard R.hb hx)

theorem matB_eq (R : RedB I m) {x : I.Gf} (hx : x ∈ I.Kset) {M : Matrix (Fin m) (Fin m) (ZMod R.p)}
    (h : RedMatB I R.w R.p R.b x M) : matB R x = M :=
  redMatB_unique I R.w R.hp R.hcard R.hm R.hb (matB_spec R hx) h

theorem matB_mul (R : RedB I m) {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) :
    matB R (x * y) = matB R x * matB R y :=
  matB_eq R (K_mul I hx hy) (redMatB_mul I R.w R.hp R.hcard R.hb.1 hx (matB_spec R hx) (matB_spec R hy))

theorem matB_one (R : RedB I m) : matB R 1 = 1 := matB_eq R (K_one I) (redMatB_one I R.w R.hp R.b)

def rhoB (R : RedB I m) : Formalism.L2.SG.AllRowsOf.KSub I →* GL (Fin m) (ZMod R.p) :=
  MonoidHom.toHomUnits
    { toFun := fun x => matB R x
      map_one' := matB_one R
      map_mul' := fun x y => matB_mul R x.2 y.2 }

theorem rhoB_val (R : RedB I m) (x : Formalism.L2.SG.AllRowsOf.KSub I) :
    ((rhoB R x : GL (Fin m) (ZMod R.p)) : Matrix (Fin m) (Fin m) (ZMod R.p)) = matB R x := rfl

theorem rhoB_spec (R : RedB I m) (x : Formalism.L2.SG.AllRowsOf.KSub I) :
    RedMatB I R.w R.p R.b x ((rhoB R x : GL (Fin m) (ZMod R.p)) : Matrix (Fin m) (Fin m) (ZMod R.p)) :=
  matB_spec R x.2

end Formalism.L2.SG.Pf.AllRowsRho
end
end
