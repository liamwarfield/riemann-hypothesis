module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverCompGLTwoPosRat
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenLangRatFunc
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPowApplyDivSubOneLt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace GlobalTheory

theorem _root_.GlobalTheory.valuation_pow_apply_div_sub_one_lt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (x : Ω) (hx : x ≠ 0) (i : ℕ) :
    A.valuation ((σ ^ i) x / x - 1) < 1 := by
  induction i with
  | zero => simp [hx]
  | succ i ih =>
    have hy0 : (σ ^ i) x ≠ 0 := (map_ne_zero (σ ^ i)).2 hx
    have hle : A.valuation ((σ ^ i) x / x) ≤ 1 := by
      have e : (σ ^ i) x / x = ((σ ^ i) x / x - 1) + 1 := by ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le ih.le (by simp))
    have key : (σ ^ (i + 1)) x / x - 1 =
        (σ ((σ ^ i) x) / (σ ^ i) x - 1) * ((σ ^ i) x / x) + ((σ ^ i) x / x - 1) := by
      rw [pow_succ', AlgEquiv.mul_apply]
      field_simp
      ring
    rw [key]
    apply Valuation.map_add_lt _ _ ih
    rw [map_mul]
    calc A.valuation (σ ((σ ^ i) x) / (σ ^ i) x - 1) * A.valuation ((σ ^ i) x / x)
        ≤ A.valuation (σ ((σ ^ i) x) / (σ ^ i) x - 1) * 1 := by gcongr
      _ < 1 := by simpa using hσ _ hy0

theorem _root_.GlobalTheory.mem_of_wild_of_pow_mem_open_normal :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ (H : Subgroup (_root_.Formalism.ConjugateSelfDual.G E Ω)), H.Normal → IsOpen (H : Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) → ∀ (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) (n : ℕ), ((n : ℕ) : 𝓞 E) ∉ v.asIdeal → (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → σ ^ n ∈ H → σ ∈ H := by
  intro E Ω _ _ _ _ _ A v hA H _ hH σ n hn hσ hpow
  change Ω ≃ₐ[E] Ω at σ
  have hv : A.valuation (n : Ω) = 1 := by
    have h1 : ¬ A.valuation (n : Ω) < 1 := by
      intro h
      apply hn
      rw [← hA]
      simpa using h
    have h2 : A.valuation (n : Ω) ≤ 1 := by
      simpa using A.valuation_le_one (n : A)
    exact le_antisymm h2 (not_lt.1 h1)
  have hn0 : (n : Ω) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  obtain ⟨s, hsdef⟩ : ∃ s : Ω → Ω, ∀ z, s z = ∑ i ∈ Finset.range n, (σ ^ i) z :=
    ⟨_, fun _ => rfl⟩
  have hs : ∀ z, (σ ^ n) z = z → σ (s z) = s z := by
    intro z hz
    have e1 := Finset.sum_range_succ (fun i => (σ ^ i) z) n
    have e2 := Finset.sum_range_succ' (fun i => (σ ^ i) z) n
    simp only [hz, pow_zero, AlgEquiv.one_apply] at e1 e2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsdef, map_sum]
    have e3 : ∑ i ∈ Finset.range n, σ ((σ ^ i) z) = ∑ i ∈ Finset.range n, (σ ^ (i + 1)) z :=
      Finset.sum_congr rfl fun i _ => by rw [pow_succ', AlgEquiv.mul_apply]
    rw [e3]
    exact add_right_cancel (e2.symm.trans e1)
  have hk : ∀ w, σ w = w → ∀ k : ℕ, (σ ^ k) w = w := by
    intro w hw k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hw]
  have hne : ∀ z, z ≠ 0 → s z ≠ 0 := by
    intro z hz h0
    have hlt : A.valuation (∑ i ∈ Finset.range n, ((σ ^ i) z / z - 1)) < 1 :=
      Valuation.map_sum_lt _ one_ne_zero
        (fun i _ => _root_.GlobalTheory.valuation_pow_apply_div_sub_one_lt A σ hσ z hz i)
    have e : ∑ i ∈ Finset.range n, ((σ ^ i) z / z - 1) = s z / z - n := by
      simp [hsdef, Finset.sum_sub_distrib, Finset.sum_div]
    rw [e, h0, zero_div, zero_sub, Valuation.map_neg, hv] at hlt
    exact lt_irrefl _ hlt
  have hfix : ∀ y : Ω, (σ ^ n) y = y → σ y = y := by
    intro y hy
    have hsy := hs y hy
    have h1 : ∀ i, (σ ^ i) ((n : Ω) * y - s y) = n * (σ ^ i) y - s y := fun i => by
      rw [map_sub, map_mul, map_natCast, hk (s y) hsy i]
    have hsz : s ((n : Ω) * y - s y) = 0 := by
      rw [hsdef, Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← hsdef, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_self]
    have hz : (n : Ω) * y - s y = 0 := by
      by_contra h
      exact hne _ h hsz
    have hy' : s y = n * y := (sub_eq_zero.1 hz).symm
    have e := congrArg σ hy'
    rw [hsy, map_mul, map_natCast, hy'] at e
    exact (mul_left_cancel₀ hn0 e).symm
  haveI : IsGalois E Ω := inferInstance
  have hcl : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) := H.isClosed_of_isOpen hH
  have hH' := InfiniteGalois.fixingSubgroup_fixedField (⟨H, hcl⟩ : ClosedSubgroup (Ω ≃ₐ[E] Ω))
  have hmem : σ ∈ (IntermediateField.fixedField H).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    apply hfix
    exact (IntermediateField.mem_fixedField_iff H y).1 hy _ hpow
  rw [hH'] at hmem
  exact hmem

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSet
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSet
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.StabGal
theorem klm_sl_gal_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l M : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (ζ : Ω) (d : ℤ) (γ γ'' : SL(2, ℤ)), 0 < M → IsPrimitiveRoot ζ M → s ζ = ζ ^ d → ((en γ 0 0 : ZMod M) = en γ'' 0 0 ∧ (en γ 0 1 : ZMod M) = d * en γ'' 0 1 ∧ (d : ZMod M) * en γ 1 0 = en γ'' 1 0 ∧ (en γ 1 1 : ZMod M) = en γ'' 1 1) → ∀ y ∈ X.Lev l M, X.klm l (X.sl (ofSL γ)).toRingEquiv (X.klm l (X.gal s) y) = X.klm l (X.gal s) (X.klm l (X.sl (ofSL γ'')).toRingEquiv y) := by
  intro Ω _ _ ε X l M _ s ζ d γ γ'' hM hζ hsd hcong y hy
  refine Submodule.span_induction (p := fun y _ => X.klm l (X.sl (ofSL γ)).toRingEquiv (X.klm l (X.gal s) y) =
      X.klm l (X.gal s) (X.klm l (X.sl (ofSL γ'')).toRingEquiv y)) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨f, hf, rfl⟩
    have hr := X.recip M (f : X.K) hM hf ζ hζ s d hsd γ'' γ hcong
    simp only [Tower.klm, LinearMap.baseChange_tmul]
    congr 1
    apply Additive.toMul.injective
    apply Units.ext
    simp [hr]
  · simp
  · intro x y _ _ hx hy; simp [hx, hy]
  · intro a x _ hx; simp [hx]

theorem galB_mem_Pol : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω), (∀ a ∈ X.A l, X.kmap l (X.gal s) a ∈ X.A l) → ∀ b ∈ X.Pol l w, X.galB l s b ∈ X.Pol l w := by
  intro Ω _ _ ε X l w _ s hA b hb
  obtain ⟨c, hcA, hc⟩ := hb
  refine ⟨fun i => ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ^ (w - (i : ℕ))) • X.kmap l (X.gal s) (c i),
    fun i => Submodule.smul_mem _ _ (hA _ (hcA i)), fun u => ?_⟩
  show X.kmap l (X.gal s) (b ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1]) = _
  rw [hc]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ring

theorem eval_Pol_rep : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (b : X.Fn l), b ∈ X.Pol l w → ∀ n : ℕ, ∃ y : Fin (w + 1) → X.Kl l, ∀ x : Fin 2 → ℤ_[l], ∃ Y ∈ Submodule.span ℤ_[l] (Set.range y), AdicCompletion.eval (idl l) (X.Kl l) n (b x) = Submodule.Quotient.mk Y := by
  intro Ω _ _ ε X l w _ b hb n
  obtain ⟨c, _, hc⟩ := hb
  choose y hy using fun i => Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (c i))
  refine ⟨y, fun x => ⟨∑ i : Fin (w + 1), (x 0 ^ (i : ℕ) * x 1 ^ (w - (i : ℕ))) • y i,
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hc, map_sum]
  simp only [map_smul]
  change _ = Submodule.mkQ _ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, Submodule.mkQ_apply, hy]

theorem eval_Pol_congr : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (b : X.Fn l), b ∈ X.Pol l w → ∀ (n : ℕ) (u v : Fin 2 → ℤ_[l]), (∀ i, PadicInt.toZModPow n (u i) = PadicInt.toZModPow n (v i)) → AdicCompletion.eval (idl l) (X.Kl l) n (b u) = AdicCompletion.eval (idl l) (X.Kl l) n (b v) := by
  intro Ω _ _ ε X l w _ b hb n u v huv
  obtain ⟨c, _, hc⟩ := hb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sub_eq_zero, ← map_sub, hc, hc, ← Finset.sum_sub_distrib, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← sub_smul, map_smul]
  have hmem : (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ)) - v 0 ^ (i : ℕ) * v 1 ^ (w - (i : ℕ))) ∈ (idl l) ^ n := by
    rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow,
      map_pow, map_pow, map_pow, huv 0, huv 1, sub_self]
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (c i))
  rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hmem Submodule.mem_top

theorem twist_congr : ∀ (l n M : ℕ) [Fact l.Prime], l ^ n ∣ M → ∀ (γ γ'' : SL(2, ℤ)) (d : ℤ) (χ : ℤ_[l]), ((en γ 0 0 : ZMod M) = en γ'' 0 0 ∧ (en γ 0 1 : ZMod M) = d * en γ'' 0 1 ∧ (d : ZMod M) * en γ 1 0 = en γ'' 1 0 ∧ (en γ 1 1 : ZMod M) = en γ'' 1 1) → (d : ZMod (l ^ n)) = PadicInt.toZModPow n χ → ∀ (u : Fin 2 → ℤ_[l]) (i : Fin 2), PadicInt.toZModPow n ((![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1] : Fin 2 → ℤ_[l]) i) = PadicInt.toZModPow n ((mZl l (γ'' : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, χ * u 1]) i) := by
  intro l n M _ hlnM γ γ'' d χ hc hd u i
  obtain ⟨h00, h01, h10, h11⟩ := hc
  have cast : ∀ k : ℤ, ZMod.castHom hlnM (ZMod (l ^ n)) (k : ZMod M) = (k : ZMod (l ^ n)) := fun k => map_intCast _ k
  have e00 := congrArg (ZMod.castHom hlnM (ZMod (l ^ n))) h00
  have e01 := congrArg (ZMod.castHom hlnM (ZMod (l ^ n))) h01
  have e10 := congrArg (ZMod.castHom hlnM (ZMod (l ^ n))) h10
  have e11 := congrArg (ZMod.castHom hlnM (ZMod (l ^ n))) h11
  simp only [map_mul, cast] at e00 e01 e10 e11
  simp only [en] at e00 e01 e10 e11
  rw [hd] at e01 e10
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mZl, Matrix.map_apply, map_add (f := _), map_mul, map_intCast]
  · rw [← e00, e01]; ring
  · rw [← e10, ← e11]; ring

theorem toGQ_SL (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
  unfold toGQ
  rw [dite_eq_left h]
  ext i j
  simp [ofSL]

theorem inv_galB {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (N l w : ℕ) [Fact l.Prime] (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (hb : b ∈ X.BSet N l w)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) = X.galB l s b := by
  obtain ⟨hpol, hinv⟩ := hb
  funext u
  apply AdicCompletion.ext
  intro n
  obtain ⟨y, hy⟩ := eval_Pol_rep X l w b hpol n
  obtain ⟨M, hM, hdiv, hlev⟩ := GlobalTheory.T.exists_common_level_span_multiple X l (N * l * l ^ n) y
    (Nat.mul_pos (Nat.mul_pos hN (Nat.Prime.pos Fact.out)) (pow_pos (Nat.Prime.pos Fact.out) n))
  have hNM : N ∣ M := Dvd.dvd.trans ⟨l * l ^ n, by ring⟩ hdiv
  have hlM : l ∣ M := Dvd.dvd.trans ⟨N * l ^ n, by ring⟩ hdiv
  have hlnM : l ^ n ∣ M := Dvd.dvd.trans ⟨N * l, by ring⟩ hdiv
  obtain ⟨γ'', hγ'', ζ, hζ, d, hsd, hcong, hdχ⟩ := GlobalTheory.T.exists_conj_level_elem_exponent_shimura (Ω := Ω) N l n M hM hNM hlM hlnM s γ hγ
  have hspan : Submodule.span ℤ_[l] (Set.range y) ≤ X.Lev l M :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hlev i)
  set χ : ℤ_[l] := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχ
  set v : Fin 2 → ℤ_[l] := ![u 0, χ * u 1] with hv
  have h1 := eval_Pol_congr X l w b hpol n _ _ (twist_congr l n M hlnM γ γ'' d χ hcong hdχ u)
  obtain ⟨Y, hY, hYe⟩ := hy (mZl l (γ'' : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v)
  have hinv' : AdicCompletion.eval (idl l) (X.Kl l) n (X.act l (γ'' : Matrix (Fin 2) (Fin 2) ℤ) b v) =
      AdicCompletion.eval (idl l) (X.Kl l) n (b v) := by rw [hinv γ'' hγ'']
  have hc := klm_sl_gal_comm X l M s ζ d γ γ'' hM hζ hsd hcong Y (hspan hY)
  show (X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (X.kmap l (X.gal s) (b ![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1]))).val n =
    (X.kmap l (X.gal s) (b v)).val n
  rw [toGQ_SL]
  change (X.klm l (X.sl (ofSL γ)).toRingEquiv).reduceModIdeal ((idl l)^n)
      ((X.klm l (X.gal s)).reduceModIdeal ((idl l)^n) (AdicCompletion.eval (idl l) (X.Kl l) n (b _))) =
    (X.klm l (X.gal s)).reduceModIdeal ((idl l)^n) (AdicCompletion.eval (idl l) (X.Kl l) n (b v))
  rw [h1, hYe, ← hinv']
  change _ = (X.klm l (X.gal s)).reduceModIdeal ((idl l)^n)
    ((X.klm l (X.sl (toGQ (γ'' : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv).reduceModIdeal ((idl l)^n)
      (AdicCompletion.eval (idl l) (X.Kl l) n (b (mZl l (γ'' : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v))))
  rw [toGQ_SL, hYe]
  simp only [LinearMap.reduceModIdeal_apply]
  rw [hc]

theorem galB_mem_B : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.galB l s b ∈ X.B N l w := by
  intro Ω _ _ _ ε X hε hj N l w _ _ hN _ _ s b hb
  have hA := (GlobalTheory.T.modular_function_tower_integrality ε X hε hj l).2 s
  have hN0 : 0 < N := by omega
  have himg : X.galB l s '' X.BSet N l w ⊆ X.BSet N l w := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨galB_mem_Pol X l w s hA c hc.1, fun γ hγ => inv_galB X N l w hN0 s c hc γ hγ⟩
  exact Submodule.span_mono himg (Submodule.apply_mem_span_image_of_mem_span (X.galB l s) hb)

end GlobalTheory.KZ.StabGal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSetStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galB_mem_kummer_invariant_set : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.galB l s b ∈ X.B N l w := by
  first | exact @GlobalTheory.KZ.StabGal.galB_mem_B | exact GlobalTheory.KZ.StabGal.galB_mem_B | (intros; apply GlobalTheory.KZ.StabGal.galB_mem_B <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExtClosureInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExtClosureInjective
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_ext_clo_inj : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ (L : Type) [CommRing L] (φ ψ : T.K →+* L), (∀ a, φ (T.io a) = ψ (T.io a)) → φ = ψ) ∧ (∀ (g : GQ) (a : GlobalTheory.FN.ring ε.range), ∃ a' : GlobalTheory.FN.ring ε.range, (a' : ℍ → ℂ) = GlobalTheory.FN.cmp g a ∧ T.sl g (T.io a) = T.io a') ∧ Function.Injective T.exp ∧ Function.Injective T.an := by
  intro Ω _ _ _ ε T
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro L _ φ ψ h
    ext f
    obtain ⟨a, b, hb, hf⟩ := T.io_surj f
    have hb' : T.io b ≠ 0 := by
      intro h0
      exact hb (T.io_inj (by rw [h0, map_zero]))
    have hu : IsUnit (φ (T.io b)) := (IsUnit.mk0 _ hb').map φ
    have h1 : φ f * φ (T.io b) = ψ f * φ (T.io b) := by
      rw [← map_mul, hf, h a, h b, ← map_mul, hf]
    exact hu.mul_left_injective h1
  · intro g a
    have hE := ((GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε).1)
    have hm := (GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1
    have ha : InR ε.range (a : ℍ → ℂ) := (hm _).1 a.2
    have hc : InR ε.range (GlobalTheory.FN.cmp g a) := GlobalTheory.T.hasSomeLevelOver_compGLTwoPosRat ε.range g _ hE ha
    refine ⟨⟨GlobalTheory.FN.cmp g a, (hm _).2 hc⟩, rfl, ?_⟩
    exact T.sl_io g a _ rfl
  · exact T.exp.toRingHom.injective
  · haveI : Nontrivial Mero := (GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units).1
    exact T.an.injective

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExtClosureInjectiveStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionField_ext_closure_injective : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ (L : Type) [CommRing L] (φ ψ : T.K →+* L), (∀ a, φ (T.io a) = ψ (T.io a)) → φ = ψ) ∧ (∀ (g : GQ) (a : GlobalTheory.FN.ring ε.range), ∃ a' : GlobalTheory.FN.ring ε.range, (a' : ℍ → ℂ) = GlobalTheory.FN.cmp g a ∧ T.sl g (T.io a) = T.io a') ∧ Function.Injective T.exp ∧ Function.Injective T.an := by
  first | exact @GlobalTheory.FN.frac_ext_clo_inj | exact GlobalTheory.FN.frac_ext_clo_inj | (intros; apply GlobalTheory.FN.frac_ext_clo_inj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenTheorem
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenTheorem
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.NeedB

theorem tsen : Tsen := by
  intro k K _ _ _ _ _
  exact GlobalTheory.T.isFirstChernClass_of_finiteDimensional_of_forms_have_zeros (RatFunc k) K (GlobalTheory.T.exists_common_zero_homogeneous_ratFunc_of_mul_lt k)

end GlobalTheory.NeedB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenTheoremStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsen_theorem : GlobalTheory.NeedB.Tsen := by
  first | exact @GlobalTheory.NeedB.tsen | exact GlobalTheory.NeedB.tsen | (intros; apply GlobalTheory.NeedB.tsen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRingOfIntegersOfHol
noncomputable section

open scoped MatrixGroups UpperHalfPlane
open Polynomial

namespace GlobalTheory.K4.TopUnits

open GlobalTheory.KZ GlobalTheory.Sieg

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def holSub (X : Tower Ω ε) : Subring X.K where
  carrier := {f | ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an f = (φ : Mero)}
  mul_mem' := by
    rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
    exact ⟨φ * ψ, h1.mul h3, by rw [map_mul, h2, h4, Filter.Germ.coe_mul]⟩
  one_mem' := ⟨1, differentiableOn_const 1, by rw [map_one, Filter.Germ.coe_one]⟩
  add_mem' := by
    rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
    exact ⟨φ + ψ, h1.add h3, by rw [map_add (f := _), h2, h4, Filter.Germ.coe_add]⟩
  zero_mem' := ⟨0, differentiableOn_const 0, by rw [map_zero, Filter.Germ.coe_zero]⟩
  neg_mem' := by
    rintro f ⟨φ, h1, h2⟩
    exact ⟨-φ, h1.neg, by rw [map_neg, h2, Filter.Germ.coe_neg]⟩

theorem siegel_hol [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {c : ℕ} {y : Fin 2 → ℚ} (hy : admitted c y) :
    siegel X c y ∈ holSub X ∧ (siegel X c y)⁻¹ ∈ holSub X := by
  have hd : DifferentiableOn ℂ (sgC c y) Hs :=
    UpperHalfPlane.mdifferentiable_iff.1 (GlobalTheory.Sieg.mdifferentiable_sg c y hy)
  have hne : ∀ z, sgC c y z ≠ 0 := fun z => GlobalTheory.Sieg.sg_ne_zero c y _ hy
  have ha := SiegelMem.an_siegel_eq Ω ε X c y hy
  refine ⟨⟨_, hd, ha⟩, (sgC c y)⁻¹, hd.inv fun z _ => hne z, ?_⟩
  have h1 : X.an (siegel X c y)⁻¹ * X.an (siegel X c y) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (GlobalTheory.T.siegelUnitInTower_ne_zero Ω ε X c y hy), map_one]
  have h2 : X.an (siegel X c y) * (((sgC c y)⁻¹ : ℂ → ℂ) : Mero) = 1 := by
    rw [ha, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_one]
    congr 1
    funext z
    exact mul_inv_cancel₀ (hne z)
  rw [← mul_one (X.an _), ← h2, ← mul_assoc, h1, one_mul]

def IsTopUnit (X : Tower Ω ε) (M : ℕ) (f : X.K) : Prop :=
  f ≠ 0 ∧ f ∈ topF X M ∧ ∃ hf : f ∈ topL X M,
    letI := algPoly X (CongruenceSubgroup.Gamma M)
    (⟨f, hf⟩ : topL X M) ∈ FunctionField.ringOfIntegers Ω (topL X M) ∧
      (⟨f, hf⟩ : topL X M)⁻¹ ∈ FunctionField.ringOfIntegers Ω (topL X M)

end GlobalTheory.K4.TopUnits

namespace GlobalTheory.K4

open GlobalTheory.KZ

end GlobalTheory.K4
end
end
