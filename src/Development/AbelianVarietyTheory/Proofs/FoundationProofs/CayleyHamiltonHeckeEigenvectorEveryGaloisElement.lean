module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommGaloisActionModularTower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraKummerModularUnit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerBettiModuleFreeFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixingMulFrobAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalMulApply
open GlobalTheory.KZ Matrix

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.gal_mul_apply (X : Tower Ω ε) (s s' : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal (s * s') f = X.gal s (X.gal s' f) := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  show (X.exp (X.gal (s * s') f)).coeff r = (X.exp (X.gal s (X.gal s' f))).coeff r
  rw [X.gal_exp, X.gal_exp, X.gal_exp]
  rfl

theorem Tower.galB_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s s' : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) :
    X.galB l (s * s') b = X.galB l s (X.galB l s' b) := by
  funext u
  simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Tower.kmap_kmap]
  have hg : X.gal (s * s') = (X.gal s').trans (X.gal s) := by
    ext f; exact X.gal_mul_apply s s' f
  have hc : (cyclotomicCharacter Ω l (s * s').toRingEquiv : ℤ_[l]) =
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (cyclotomicCharacter Ω l s'.toRingEquiv : ℤ_[l]) := by
    have : (s * s').toRingEquiv = s.toRingEquiv * s'.toRingEquiv := rfl
    rw [this, map_mul, Units.val_mul]
  rw [hg, hc]
  congr 2
  funext i
  fin_cases i <;> simp [mul_comm, mul_left_comm]

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraFrobeniusQuadraticModPrimePow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumActUpperRep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem sum_act_upper_rep : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (N l : ℕ) [Fact l.Prime] (q M : ℕ), 0 < q → Nat.Coprime q M → ∀ b : X.Fn l,
    (∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b) →
    ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] b =
      ∑ j ∈ Finset.range q, X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b := by
  intro Ω _ _ _ ε X N l _ q M hq hqM b hb
  have hT : ∀ t : ℤ, X.act l !![1, t; 0, 1] b = b := by
    intro t
    let T : SL(2, ℤ) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hmem : T ∈ Gam N l := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [CongruenceSubgroup.Gamma1_mem]
        refine ⟨?_, ?_, ?_⟩ <;> simp [T]
      · rw [CongruenceSubgroup.Gamma0_mem]
        simp [T]
    exact hb T hmem
  have he : IsCoprime (M : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa [Int.gcd_natCast_natCast] using hqM.symm
  exact (Tower.sum_act_upper_mul_unit X l b hT q (M : ℤ) hq he).symm

end GlobalTheory.KZ.ES
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MobToGQScalar
open GlobalTheory.KZ GlobalTheory.Ord2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V
open scoped MatrixGroups

namespace GlobalTheory.KZ

theorem Tower.kmap_refl {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (l : ℕ) [Fact l.Prime] (x : X.Khat l) : X.kmap l (RingEquiv.refl X.K) x = x := by
  unfold Tower.kmap
  have : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map (RingEquiv.refl X.K).toMonoidHom))) =
      (LinearMap.id : Additive X.Kˣ →ₗ[ℤ] Additive X.Kˣ) := by
    ext x; rfl
  rw [this, LinearMap.baseChange_id, AdicCompletion.map_id]
  rfl

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraFrobeniusQuadraticModPrimePow
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.ESmod

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem map_mem_smul_top {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (I : Ideal R) (φ : A →ₗ[R] B) {x : A} (hx : x ∈ I • (⊤ : Submodule R A)) :
    φ x ∈ I • (⊤ : Submodule R B) := by
  refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun y z hy hz => ?_)
  · rw [map_smul]; exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

theorem exists_frobV {q : ℕ} (hq : 0 < q) {s : Ω ≃ₐ[ℚ] Ω} (h : FrobAt q s) : ∃ V, ES.FrobV V q s := by
  obtain ⟨V, hV, hs⟩ := h
  refine ⟨V, hV, fun x hx => ⟨(hs x hx).1, ?_, (hs x hx).2⟩⟩
  by_contra hy
  have hy0 : s.symm x ≠ 0 := fun e => hy (e ▸ V.zero_mem)
  have hi : (s.symm x)⁻¹ ∈ V := (V.mem_or_inv_mem _).resolve_left hy
  have h1 : 1 < V.valuation (s.symm x) := by
    by_contra hle
    exact hy ((V.valuation_le_one_iff _).1 (not_lt.1 hle))
  have h2 : V.valuation ((s.symm x)⁻¹) < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ h1
  have h3 : V.valuation (((s.symm x)⁻¹) ^ q) < 1 := by
    rw [map_pow]; exact pow_lt_one₀ zero_le' h2 hq.ne'
  have h4 := (hs _ hi).2
  have h5 : V.valuation (s ((s.symm x)⁻¹)) < 1 := by
    have := Valuation.map_add_lt V.valuation h4 h3
    rwa [sub_add_cancel] at this
  rw [map_inv₀, AlgEquiv.apply_symm_apply] at h5
  have hx0 : x ≠ 0 := fun e => hy0 (by rw [e, map_zero])
  have h6 : V.valuation x ≤ 1 := (V.valuation_le_one_iff _).2 hx
  have h7 : V.valuation (x * x⁻¹) < 1 := by
    rw [map_mul]
    calc V.valuation x * V.valuation x⁻¹ ≤ 1 * V.valuation x⁻¹ := mul_le_mul_left h6 _
      _ < 1 := by rwa [one_mul]
  rw [mul_inv_cancel₀ hx0, map_one] at h7
  exact lt_irrefl _ h7

theorem chi_mul_symm (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) :
    (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (cyclotomicCharacter Ω l s.symm.toRingEquiv : ℤ_[l]) = 1 := by
  rw [← Units.val_mul, ← map_mul]
  have : s.toRingEquiv * s.symm.toRingEquiv = 1 := by
    ext x; exact s.apply_symm_apply x
  rw [this, map_one, Units.val_one]

theorem galB_galB_symm (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) :
    X.galB l s (X.galB l s.symm b) = b := by
  have h1 : ∀ f, X.gal 1 f = f := fun f => by
    apply (X.gal 1).injective
    rw [← X.gal_mul_apply, mul_one]
  have h2 : (X.gal s.symm).trans (X.gal s) = RingEquiv.refl _ := by
    ext f
    have : s * s.symm = 1 := mul_inv_cancel s
    rw [RingEquiv.trans_apply, ← X.gal_mul_apply, this, h1]; rfl
  funext u
  show X.kmap l (X.gal s) (X.kmap l (X.gal s.symm) (b _)) = b u
  rw [X.kmap_kmap, h2, X.kmap_refl]
  congr 1
  funext i
  fin_cases i
  · simp
  · have := chi_mul_symm l s
    simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [← mul_assoc, mul_comm (cyclotomicCharacter Ω l s.symm.toRingEquiv : ℤ_[l]), this, one_mul]

def defect (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (M q : ℕ) (σ : SL(2, ℤ)) (s : Ω ≃ₐ[ℚ] Ω) :
    X.Khat l →ₗ[ℤ_[l]] X.Khat l :=
  (∑ j ∈ Finset.range q, X.kmap l (X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)])).toRingEquiv) +
    X.kmap l (X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]))).toRingEquiv -
    (X.kmap l (X.gal s) + (q : ℤ_[l]) • (X.kmap l (X.gal s.symm)).comp (X.kmap l (X.sl (ofSL σ)).toRingEquiv))

theorem defect_mem (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n M q : ℕ) (σ : SL(2, ℤ)) (s : Ω ≃ₐ[ℚ] Ω)
    (c : X.Khat l) (f g : X.Kˣ) (hc : AdicCompletion.eval (idl l) (X.Kl l) n c = X.cls l n f)
    (h : (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) *
      X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) =
      X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q * (g : X.K) ^ (l ^ n)) :
    defect X l M q σ s c ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  obtain ⟨-, hiff, hmul, hone, -, hk, -⟩ := H3.cls_props Ω ε X l n
  have hprod : ∀ (t : Finset ℕ) (F : ℕ → X.Kˣ), X.cls l n (∏ j ∈ t, F j) = ∑ j ∈ t, X.cls l n (F j) := by
    intro t F
    induction t using Finset.induction_on with
    | empty => simpa using hone
    | insert a t ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, hmul, ih]
  have hpow : ∀ (k : ℕ) (F : X.Kˣ), X.cls l n (F ^ k) = (k : ℤ_[l]) • X.cls l n F := by
    intro k F
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hmul, ih, Nat.cast_succ, add_smul, one_smul]
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [defect, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.sum_apply, map_sub, map_add, map_sum, map_smul]
  rw [hk _ _ _ hc, hk _ _ _ hc, hk _ _ _ (hk _ _ _ hc), Finset.sum_congr rfl (fun j _ => hk _ _ _ hc),
    sub_eq_zero, ← hprod, ← hmul, ← hpow, ← hmul, hiff]
  refine ⟨g, Units.ext ?_⟩
  simpa using h

theorem int_mem_pow {l : ℕ} [Fact l.Prime] {n M : ℕ} (hM : l ^ n ∣ M) {x : ℤ} (hx : (x : ZMod M) = 0) :
    (x : ℤ_[l]) ∈ (idl l) ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x M).1 hx
  obtain ⟨m, hm⟩ := hM
  exact ⟨(m : ℤ_[l]) * (k : ℤ_[l]), by rw [hk, hm]; push_cast; ring⟩

theorem exists_diag (M q : ℕ) (h : Nat.Coprime q M) :
    ∃ σ : SL(2, ℤ), (en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q := by
  have h2 : IsCoprime (q : ℤ) ((M : ℤ) * M) := by
    have := Nat.isCoprime_iff_coprime.2 h
    exact this.mul_right this
  obtain ⟨a, k, e⟩ := h2
  refine ⟨⟨!![a, (M : ℤ); -k * M, (q : ℤ)], ?_⟩, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination e
  all_goals simp [en]

theorem rel_of_defect [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (n M q : ℕ) (σ : SL(2, ℤ))
    (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (hb : b ∈ X.BSet N l w) (hN : N ∣ M) (hl : l ∣ M) (hln : l ^ n ∣ M)
    (hq : 0 < q) (hqM : Nat.Coprime q M) (hχ : (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) = q)
    (h01 : (en σ 0 1 : ZMod M) = 0) (h10 : (en σ 1 0 : ZMod M) = 0) (h11 : (en σ 1 1 : ZMod M) = q)
    (hD : ∀ v, defect X l M q σ s (b v) ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))) (u : Fin 2 → ℤ_[l]) :
    (X.galB l s b - X.heckeT N l q b + ((q : ℤ_[l]) ^ (w + 1)) • X.galB l s.symm (X.diam N l q b)) u ∈
      (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  have hbB : b ∈ X.B N l w := Submodule.subset_span hb
  have cast : ∀ {D : ℕ}, D ∣ M → ∀ {x y : ℤ}, (x : ZMod M) = y → (x : ZMod D) = y := by
    intro D hD x y hxy
    have := congrArg (ZMod.castHom hD (ZMod D)) hxy
    simpa using this
  have hσ : IsDiam N l q σ := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine CongruenceSubgroup.Gamma0_mem.2 ?_
      simpa [en] using cast hN (x := en σ 1 0) (y := 0) (by simpa using h10)
    · refine CongruenceSubgroup.Gamma0_mem.2 ?_
      simpa [en] using cast hl (x := en σ 1 0) (y := 0) (by simpa using h10)
    · simpa using cast hN (x := en σ 1 1) (y := (q : ℤ)) (by simpa using h11)
  have hdet : (0 : ℤ) < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simpa [Matrix.det_fin_two] using hq
  have hdiam : X.diam N l q b = X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b := (X.act_isDiam_eq hbB hσ).symm
  have hT : X.heckeT N l q b = ∑ j ∈ Finset.range q, X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b +
      X.act l ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) b := by
    rw [← ES.sum_act_upper_rep ε X N l q M hq hqM b hb.2, Tower.heckeT, LinearMap.add_apply, LinearMap.sum_apply,
      ← Tower.act_act Ω ε X l _ _ (by simp) hdet, ← Tower.act_act Ω ε X l _ _ (by simp) hdet,
      X.act_isDiam_eq hbB hσ]
  have e01 := int_mem_pow hln h01
  have e10 := int_mem_pow hln h10
  have e11 : ((en σ 1 1 - q : ℤ) : ℤ_[l]) ∈ (idl l) ^ n := int_mem_pow hln (by push_cast; rw [h11, sub_self])
  have e00 : ((en σ 0 0 * q - 1 : ℤ) : ℤ_[l]) ∈ (idl l) ^ n := by
    refine int_mem_pow hln ?_
    have hd : en σ 0 0 * en σ 1 1 - en σ 0 1 * en σ 1 0 = 1 := by
      have := σ.det_coe
      rwa [Matrix.det_fin_two] at this
    have := congrArg (Int.cast : ℤ → ZMod M) hd
    push_cast at this ⊢
    rw [h01, h11] at this
    linear_combination this
  have eM : ((M : ℤ) : ℤ_[l]) ∈ (idl l) ^ n := int_mem_pow hln (by simp)
  push_cast at e11 e00 eM
  set v : Fin 2 → ℤ_[l] := ![u 0, (q : ℤ_[l]) * u 1] with hv
  have hA : ∀ j : ℕ, X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b u -
      X.kmap l (X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)])).toRingEquiv (b v) ∈
      (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
    intro j
    show X.kmap l _ _ - _ ∈ _
    rw [← map_sub]
    refine map_mem_smul_top _ _ (X.B_sub_mem N l w b hbB n _ _ ?_)
    intro i
    fin_cases i
    · have : (mZl l !![1, (j * M : ℤ); 0, (q : ℤ)] *ᵥ u) 0 - v 0 = (M : ℤ_[l]) * (j * u 1) := by
        simp [mZl, hv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
      exact this ▸ Ideal.mul_mem_right _ _ eM
    · have : (mZl l !![1, (j * M : ℤ); 0, (q : ℤ)] *ᵥ u) 1 - v 1 = 0 := by
        simp [mZl, hv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      exact this ▸ Ideal.zero_mem _
  have key : ∀ i, (mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![(q : ℤ_[l]) * u 0, u 1]) i - v i ∈ (idl l) ^ n := by
    intro i
    fin_cases i
    · have : (mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![(q : ℤ_[l]) * u 0, u 1]) 0 - v 0 =
          ((en σ 0 0 : ℤ_[l]) * q - 1) * u 0 + (en σ 0 1 : ℤ_[l]) * u 1 := by
        simp [mZl, hv, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
      exact this ▸ Ideal.add_mem _ (Ideal.mul_mem_right _ _ e00) (Ideal.mul_mem_right _ _ e01)
    · have : (mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![(q : ℤ_[l]) * u 0, u 1]) 1 - v 1 =
          (en σ 1 0 : ℤ_[l]) * (q * u 0) + ((en σ 1 1 : ℤ_[l]) - q) * u 1 := by
        simp [mZl, hv, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
      exact this ▸ Ideal.add_mem _ (Ideal.mul_mem_right _ _ e10) (Ideal.mul_mem_right _ _ e11)
  have hB : X.act l ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) b u -
      X.kmap l (X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]))).toRingEquiv (b v) ∈
      (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
    show X.kmap l _ _ - _ ∈ _
    rw [← map_sub]
    refine map_mem_smul_top _ _ (X.B_sub_mem N l w b hbB n _ _ ?_)
    have : mZl l !![(q : ℤ), 0; 0, 1] *ᵥ u = ![(q : ℤ_[l]) * u 0, u 1] := by
      funext i
      fin_cases i <;> simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [mZl_mul, ← Matrix.mulVec_mulVec, this]
    exact key
  have hhom : ∀ x : Fin 2 → ℤ_[l], ((q : ℤ_[l]) ^ w) • b x = b ((q : ℤ_[l]) • x) := by
    obtain ⟨c, -, hc⟩ := hb.1
    intro x
    rw [hc, hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    congr 1
    have hi : (i : ℕ) + (w - i) = w := Nat.add_sub_cancel' (Nat.lt_succ_iff.1 i.2)
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    have hp : (q : ℤ_[l]) ^ w = (q : ℤ_[l]) ^ (i : ℕ) * (q : ℤ_[l]) ^ (w - i) := by rw [← pow_add, hi]
    rw [hp]; ring
  have hC : (((q : ℤ_[l]) ^ (w + 1)) • X.galB l s.symm (X.diam N l q b)) u -
      (q : ℤ_[l]) • X.kmap l (X.gal s.symm) (X.kmap l (X.sl (ofSL σ)).toRingEquiv (b v)) ∈
      (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
    rw [hdiam, Pi.smul_apply, pow_succ', mul_smul, ← smul_sub]
    refine Submodule.smul_mem _ _ ?_
    show ((q : ℤ_[l]) ^ w) • X.kmap l (X.gal s.symm) (X.kmap l (X.sl (toGQ _)).toRingEquiv (b _)) - _ ∈ _
    rw [MobLaws.toGQ_SL, ← map_smul, ← map_smul, ← map_sub, ← map_sub, hhom]
    refine map_mem_smul_top _ _ (map_mem_smul_top _ _ (X.B_sub_mem N l w b hbB n _ _ ?_))
    have h1 := chi_mul_symm l s
    rw [hχ] at h1
    have : (q : ℤ_[l]) • ![u 0, (cyclotomicCharacter Ω l s.symm.toRingEquiv : ℤ_[l]) * u 1] =
        ![(q : ℤ_[l]) * u 0, u 1] := by
      funext i
      fin_cases i
      · simp
      · simp only [Fin.mk_one, Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul]
        rw [← mul_assoc, h1, one_mul]
    rw [← Matrix.mulVec_smul, this]
    exact key
  have hG : X.galB l s b u = X.kmap l (X.gal s) (b v) := by
    show X.kmap l (X.gal s) (b ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1]) = _
    rw [hχ]
  have hS := Submodule.sum_mem _ (fun j (_ : j ∈ Finset.range q) => hA j)
  have hall := Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ hC hS) hB) (hD v)
  convert hall using 1
  simp only [defect, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.sum_apply, hT, Pi.add_apply, Pi.sub_apply, Finset.sum_apply, hG, Finset.sum_sub_distrib]
  abel

theorem rel_BSet [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (hε : Function.Injective ε)
    (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) (N l w : ℕ) [Fact l.Prime] (hN : 0 < N)
    (n : ℕ) (b : X.Fn l) (hb : b ∈ X.BSet N l w) :
    ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s → ∀ u,
      (X.galB l s b - X.heckeT N l q b + ((q : ℤ_[l]) ^ (w + 1)) • X.galB l s.symm (X.diam N l q b)) u ∈
        (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  classical
  have hl : l.Prime := Fact.out
  obtain ⟨c, hcA, hc⟩ := hb.1
  choose f hfU hf using fun i => ES.exists_un_eval_eq_cls ε X hj l n (c i) (hcA i)
  choose m hm0 hm using fun i => X.level (f i : X.K)
  set M : ℕ := N * (l * l ^ n) * ∏ i, m i with hM
  have hM0 : 0 < M := Nat.mul_pos (Nat.mul_pos hN (Nat.mul_pos hl.pos (pow_pos hl.pos n)))
    (Finset.prod_pos fun i _ => hm0 i)
  have hNM : N ∣ M := ⟨_, by rw [hM, mul_assoc]⟩
  have hlM : l ∣ M := ⟨N * l ^ n * ∏ i, m i, by rw [hM]; ring⟩
  have hnM : l ^ n ∣ M := ⟨N * l * ∏ i, m i, by rw [hM]; ring⟩
  have hmM : ∀ i, m i ∣ M := fun i => Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _
  choose S hS using fun i => GlobalTheory.T.eichlerShimura_kummer_modularUnit ε X hε hj l M n (f i) hM0 hlM (hfU i)
    (fun γ hγ => hm i γ (gamma_le_of_dvd (hmM i) hγ))
  refine ⟨Finset.univ.biUnion S ∪ M.primeFactors, fun q hq hqS s hs u => ?_⟩
  rw [Finset.mem_union, not_or, Finset.mem_biUnion, Nat.mem_primeFactors] at hqS
  have hqM : ¬ q ∣ M := fun h => hqS.2 ⟨hq, h, hM0.ne'⟩
  have hcop : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).2 hqM
  have hql : q ≠ l := fun h => hqM (h ▸ hlM)
  obtain ⟨V, hV⟩ := exists_frobV hq.pos hs
  obtain ⟨σ, h01, h10, h11⟩ := exists_diag M q hcop
  refine rel_of_defect X N l w n M q σ s b hb hNM hlM hnM hq.pos hcop
    (ES.cyclotomicCharacter_frobV l q hq hql V s hV) h01 h10 h11 (fun v => ?_) u
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hc, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  obtain ⟨g, hg⟩ := hS i q hq (fun h => hqS.1 ⟨i, Finset.mem_univ i, h⟩) s hs σ ⟨h01, h10, h11⟩
  exact Submodule.smul_mem _ _ (defect_mem X l n M q σ s (c i) (f i) g (hf i) hg)

end GlobalTheory.KZ.ESmod

namespace GlobalTheory.KZ


open ESmod in
theorem eichlerShimura_B_mod : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ n : ℕ, ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s → ∀ b ∈ X.B N l w, ∀ u, (X.galB l s (X.galB l s b) - X.heckeT N l q (X.galB l s b) + ((q : ℤ_[l]) ^ (w + 1)) • X.diam N l q b) u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  classical
  intro Ω _ _ _ ε X hε hj N l w _ hl2 hN hNl hw n
  have hl : l.Prime := Fact.out
  have hfg : (Submodule.span ℤ_[l] (X.BSet N l w)).FG :=
    Module.Finite.iff_fg.1 (GlobalTheory.T.kummerBettiModule_free_finite ε X hε hj N l w hl2 hN hNl hw).2
  obtain ⟨G, hG, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  choose S hS using fun b : G => rel_BSet X hε hj N l w (by omega) n b (hG b.2)
  refine ⟨Finset.univ.biUnion S ∪ (N * l).primeFactors, fun q hq hqS s hs b hb u => ?_⟩
  rw [Finset.mem_union, not_or, Finset.mem_biUnion, Nat.mem_primeFactors] at hqS
  have hadm : admitted N l (Letter.T q) := ⟨hq, fun h => hqS.2 ⟨hq, h, Nat.mul_ne_zero (by omega) hl.ne_zero⟩⟩
  let L : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
    X.galB l s - X.heckeT N l q + ((q : ℤ_[l]) ^ (w + 1)) • (X.galB l s.symm).comp (X.diam N l q)
  have hL : ∀ u, L b u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
    have hb' : b ∈ Submodule.span ℤ_[l] (G : Set (X.Fn l)) := hspan ▸ hb
    clear hb
    induction hb' using Submodule.span_induction with
    | mem x hx => exact hS ⟨x, hx⟩ q hq (fun h => hqS.1 ⟨_, Finset.mem_univ _, h⟩) s hs
    | zero => intro u; rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => intro u; rw [map_add (f := _)]; exact Submodule.add_mem _ (hx u) (hy u)
    | smul a x _ hx => intro u; rw [map_smul]; exact Submodule.smul_mem _ _ (hx u)
  have hcomm : X.heckeT N l q (X.galB l s b) = X.galB l s (X.heckeT N l q b) :=
    GlobalTheory.T.hecke_operator_comm_galois_action_modular_tower ε X hε hj N l w hl2 hN hNl hw (Letter.T q) hadm s b hb
  have e : X.galB l s (X.galB l s b) - X.heckeT N l q (X.galB l s b) + ((q : ℤ_[l]) ^ (w + 1)) • X.diam N l q b =
      X.galB l s (L b) := by
    simp only [L, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_add (f := _),
      map_sub, map_smul, galB_galB_symm, hcomm]
  rw [e]
  exact map_mem_smul_top _ (X.kmap l (X.gal s)) (hL _)

end GlobalTheory.KZ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraFrobeniusQuadraticModPrimePowStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerShimura_frobenius_quadratic_mod_prime_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ n : ℕ, ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s → ∀ b ∈ X.B N l w, ∀ u, (X.galB l s (X.galB l s b) - X.heckeT N l q (X.galB l s b) + ((q : ℤ_[l]) ^ (w + 1)) • X.diam N l q b) u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  first | exact @GlobalTheory.KZ.eichlerShimura_B_mod | exact GlobalTheory.KZ.eichlerShimura_B_mod | (intros; apply GlobalTheory.KZ.eichlerShimura_B_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRelationOfFrobApprox
open GlobalTheory.KZ Matrix

namespace GlobalTheory

theorem galois_relation_of_frob_approx : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Type} [NormedField E] (r : ℕ) (A : (Ω ≃ₐ[ℚ] Ω) → Matrix (Fin r) (Fin r) E) (t d : (Ω ≃ₐ[ℚ] Ω) → E) (v : Fin r → E), (∀ (s : Ω ≃ₐ[ℚ] Ω) (δ : ℝ), 0 < δ → ∃ E0 : Finset Ω, ∀ s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → (∀ i j, ‖A (s * s') i j - A s i j‖ < δ) ∧ ‖t (s * s') - t s‖ < δ ∧ ‖d (s * s') - d s‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ s, FrobAt q s → ∀ i, ‖(A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v) i‖ < δ) → (∀ (s : Ω ≃ₐ[ℚ] Ω) (E0 : Finset Ω) (S : Finset ℕ), ∃ (s' : Ω ≃ₐ[ℚ] Ω) (q : ℕ), (∀ x ∈ E0, s' x = x) ∧ q.Prime ∧ q ∉ S ∧ FrobAt q (s * s')) → ∀ s, A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v = 0 := by
  intro Ω _ _ E _ r A t d v hcont happrox hdens s
  funext i

  let G : (Fin r → Fin r → E) × E × E → E := fun x =>
    (Matrix.of x.1 *ᵥ (Matrix.of x.1 *ᵥ v) - x.2.1 • (Matrix.of x.1 *ᵥ v) + x.2.2 • v) i
  have hG : Continuous G := by
    simp only [G, Matrix.mulVec, dotProduct, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    fun_prop
  have key : ∀ ε : ℝ, 0 < ε → ‖(A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v) i‖ < ε := by
    intro ε hε
    obtain ⟨η, hη, hGη⟩ := Metric.continuous_iff.mp hG (fun a b => A s a b, t s, d s) (ε / 2) (by linarith)
    obtain ⟨E0, hE0⟩ := hcont s η hη
    obtain ⟨S, hS⟩ := happrox (ε / 2) (by linarith)
    obtain ⟨s', q, hfix, hq, hqS, hfr⟩ := hdens s E0 S
    obtain ⟨hA, ht, hd⟩ := hE0 s' hfix
    have h1 := hS q hq hqS (s * s') hfr i
    have hdist : dist (fun a b => A (s * s') a b, t (s * s'), d (s * s')) (fun a b => A s a b, t s, d s) < η := by
      rw [Prod.dist_eq, Prod.dist_eq]
      refine max_lt ?_ (max_lt ?_ ?_)
      · rw [dist_pi_lt_iff hη]; intro a
        rw [dist_pi_lt_iff hη]; intro b
        rw [dist_eq_norm]; exact hA a b
      · rw [dist_eq_norm]; exact ht
      · rw [dist_eq_norm]; exact hd
    have h2 := hGη _ hdist
    have e1 : G (fun a b => A (s * s') a b, t (s * s'), d (s * s')) = (A (s * s') *ᵥ (A (s * s') *ᵥ v) - t (s * s') • (A (s * s') *ᵥ v) + d (s * s') • v) i := rfl
    have e2 : G (fun a b => A s a b, t s, d s) = (A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v) i := rfl
    rw [e1, e2, dist_eq_norm] at h2
    have := norm_sub_le_norm_sub_add_norm_sub ((A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v) i) ((A (s * s') *ᵥ (A (s * s') *ᵥ v) - t (s * s') • (A (s * s') *ᵥ v) + d (s * s') • v) i) 0
    rw [norm_sub_rev] at h2
    simp only [sub_zero] at this
    linarith
  have : ‖(A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v) i‖ = 0 := by
    by_contra h
    have hpos := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    exact lt_irrefl _ (key _ hpos)
  simpa using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CayleyHamiltonHeckeEigenvectorEveryGaloisElement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.CayleyHamiltonSmallCoefficients

theorem exists_pow_norm_lt (l : ℕ) [Fact l.Prime] {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, ∀ a ∈ (idl l) ^ k, ‖a‖ < δ := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (PadicInt.norm_lt_one_iff_dvd (l : ℤ_[l]) |>.2 dvd_rfl)
  refine ⟨k, fun a ha => ?_⟩
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
  obtain ⟨c, rfl⟩ := ha
  rw [norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one c)) hk

theorem small_coeffs (l : ℕ) [Fact l.Prime] {M U n : Type} [AddCommGroup M] [Module ℤ_[l] M] [Fintype n]
    (b : n → U → AdicCompletion (idl l) M) (hb : LinearIndependent ℤ_[l] b) (k : ℕ) :
    ∃ m : ℕ, ∀ a : n → ℤ_[l], (∀ u, (∑ j, a j • b j) u ∈
      (idl l) ^ m • (⊤ : Submodule ℤ_[l] (AdicCompletion (idl l) M))) → ∀ j, a j ∈ (idl l) ^ k := by
  classical
  by_contra hcon
  simp only [not_exists, not_forall] at hcon
  choose a ha j0 hj0 using hcon
  obtain ⟨c, -, φ, hφ, hlim⟩ := (isCompact_univ (X := n → ℤ_[l])).tendsto_subseq (x := a) (fun _ => Set.mem_univ _)
  have hev : ∀ p : ℕ, ∃ i, p ≤ i ∧ ∀ j, a (φ i) j - c j ∈ (idl l) ^ p := by
    intro p
    have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    obtain ⟨i0, hi0⟩ := Metric.tendsto_atTop.1 hlim ((l : ℝ) ^ (-(p : ℤ))) (zpow_pos hl0 _)
    refine ⟨max p i0, le_max_left _ _, fun j => ?_⟩
    rw [Ideal.span_singleton_pow, ← PadicInt.norm_le_pow_iff_mem_span_pow, ← dist_eq_norm]
    exact (dist_le_pi_dist _ _ j).trans (hi0 _ (le_max_right _ _)).le
  have hc0 : ∑ j, c j • b j = 0 := by
    funext u
    refine IsHausdorff.haus (inferInstance : IsHausdorff (idl l) (AdicCompletion (idl l) M)) _ fun p => ?_
    rw [SModEq.zero]
    obtain ⟨i, hi, h⟩ := hev p
    have e : (∑ j, c j • b j) u = (∑ j, a (φ i) j • b j) u - ∑ j, (a (φ i) j - c j) • b j u := by
      simp only [Finset.sum_apply, Pi.smul_apply, sub_smul, Finset.sum_sub_distrib]
      abel
    rw [e]
    refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (h j) Submodule.mem_top)
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (hi.trans (hφ.id_le i))) (ha (φ i) u)
  have hc := Fintype.linearIndependent_iff.1 hb c hc0
  obtain ⟨i, -, h⟩ := hev k
  exact hj0 (φ i) (by simpa [hc] using h (j0 (φ i)))

theorem matrix_relation {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Type} [NormedField E] (l : ℕ) [Fact l.Prime]
    [Algebra ℤ_[l] E] (hE : ∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) {r : ℕ}
    (A : (Ω ≃ₐ[ℚ] Ω) → Matrix (Fin r) (Fin r) ℤ_[l]) (t d : (Ω ≃ₐ[ℚ] Ω) → E) (z : Fin r → E)
    (hA : ∀ s s', A (s * s') = A s * A s')
    (hAc : ∀ k : ℕ, ∃ E0 : Finset Ω, ∀ s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ∀ i j, (A s' - 1) i j ∈ (idl l) ^ k)
    (ht : ∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖t (s * s') - t s‖ < δ)
    (hd : ∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖d (s * s') - d s‖ < δ)
    (hF : ∀ k : ℕ, ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ σ : Ω ≃ₐ[ℚ] Ω, FrobAt q σ →
      ∃ R : Matrix (Fin r) (Fin r) ℤ_[l], (∀ i j, R i j ∈ (idl l) ^ k) ∧
        ((A σ).map (algebraMap ℤ_[l] E) * (A σ).map (algebraMap ℤ_[l] E) - t σ • (A σ).map (algebraMap ℤ_[l] E)
          + d σ • (1 : Matrix (Fin r) (Fin r) E)) *ᵥ z = R.map (algebraMap ℤ_[l] E) *ᵥ z)
    (hC : ∀ (s : Ω ≃ₐ[ℚ] Ω) (E0 : Finset Ω) (S : Finset ℕ),
      ∃ (s' : Ω ≃ₐ[ℚ] Ω) (q : ℕ), (∀ x ∈ E0, s' x = x) ∧ q.Prime ∧ q ∉ S ∧ FrobAt q (s * s'))
    (s : Ω ≃ₐ[ℚ] Ω) :
    ((A s).map (algebraMap ℤ_[l] E) * (A s).map (algebraMap ℤ_[l] E) - t s • (A s).map (algebraMap ℤ_[l] E)
      + d s • (1 : Matrix (Fin r) (Fin r) E)) *ᵥ z = 0 := by
  classical
  have hexp : ∀ (M : Matrix (Fin r) (Fin r) E) (a b : E), (M * M - a • M + b • (1 : Matrix (Fin r) (Fin r) E)) *ᵥ z =
      M *ᵥ (M *ᵥ z) - a • (M *ᵥ z) + b • z := by
    intro M a b
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_mulVec]
  rw [hexp]
  refine GlobalTheory.galois_relation_of_frob_approx r (fun s => (A s).map (algebraMap ℤ_[l] E)) t d z ?_ ?_ hC s
  · intro s δ hδ
    obtain ⟨k, hk⟩ := exists_pow_norm_lt l hδ
    obtain ⟨E1, h1⟩ := hAc k
    obtain ⟨E2, h2⟩ := ht δ hδ
    obtain ⟨E3, h3⟩ := hd δ hδ
    refine ⟨E1 ∪ E2 ∪ E3, fun s' hs' => ⟨fun i j => ?_, h2 s s' fun x hx => hs' x (by simp [hx]),
      h3 s s' fun x hx => hs' x (by simp [hx])⟩⟩
    have h4 := h1 s' fun x hx => hs' x (by simp [hx])
    rw [Matrix.map_apply, Matrix.map_apply, ← map_sub, hE]
    apply hk
    have e : A (s * s') i j - A s i j = (A s * (A s' - 1)) i j := by
      rw [hA, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply]
    rw [e, Matrix.mul_apply]
    exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (h4 m j)
  · intro δ hδ
    have hz : 0 < ∑ j, ‖z j‖ + 1 := by positivity
    obtain ⟨k, hk⟩ := exists_pow_norm_lt l (div_pos hδ hz)
    obtain ⟨S, hS⟩ := hF k
    refine ⟨S, fun q hq hqS σ hσ i => ?_⟩
    obtain ⟨R, hR, hRz⟩ := hS q hq hqS σ hσ
    rw [← hexp, hRz]
    calc ‖(R.map (algebraMap ℤ_[l] E) *ᵥ z) i‖ ≤ ∑ j, ‖algebraMap ℤ_[l] E (R i j) * z j‖ :=
          norm_sum_le Finset.univ fun j => algebraMap ℤ_[l] E (R i j) * z j
      _ ≤ ∑ j, δ / (∑ j, ‖z j‖ + 1) * ‖z j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, hE]
        exact mul_le_mul_of_nonneg_right (hk _ (hR i j)).le (norm_nonneg _)
      _ < δ := by
        rw [← Finset.mul_sum, div_mul_eq_mul_div, div_lt_iff₀ hz]
        exact mul_lt_mul_of_pos_left (lt_add_one _) hδ

theorem repr_baseChange {R E B ι : Type} [CommRing R] [Field E] [Algebra R E] [AddCommGroup B] [Module R B]
    [Fintype ι] [DecidableEq ι] (β : Module.Basis ι R B) (φ : B →ₗ[R] B) (z : E ⊗[R] B) :
    ⇑((Algebra.TensorProduct.basis E β).repr (φ.baseChange E z)) =
      (LinearMap.toMatrix β β φ).map (algebraMap R E) *ᵥ ⇑((Algebra.TensorProduct.basis E β).repr z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e b =>
    funext i
    rw [LinearMap.baseChange_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
    have h := congrFun (LinearMap.toMatrix_mulVec_repr β β φ b) i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, ← h, Matrix.mulVec, dotProduct,
      Matrix.map_apply, map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  | add a b ha hb => simp [map_add (f := _), ha, hb, Matrix.mulVec_add]

end GlobalTheory.CayleyHamiltonSmallCoefficients

namespace GlobalTheory


set_option maxHeartbeats 1000000 in
open GlobalTheory.CayleyHamiltonSmallCoefficients in
theorem cayleyHamilton_galV : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [NormedField E] [IsAlgClosed E] [Algebra ℤ_[l] E], (∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) → ∀ (lam : Letter → E) (t d : (Ω ≃ₐ[ℚ] Ω) → E) (S0 : Finset ℕ), (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖t (s * s') - t (s)‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖d (s * s') - d (s)‖ < δ) → (∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s → t s = lam (Letter.T q) ∧ d s = (q : E) ^ (w + 1) * lam (Letter.D q)) → ∀ x ∈ X.VB N l w E, (∀ T : Letter, admitted N l T → X.opV N l E T x = lam T • x) → ∀ s : Ω ≃ₐ[ℚ] Ω, X.galV l E s (X.galV l E s x) - t s • X.galV l E s x + d s • x = 0 := by
  intro Ω _ _ _ ε X hε hj N l w _ hl2 hN hNl hw E _ _ _ hE lam t d S0 ht hd hfr x hx heig s
  have hstabG := fun s b hb => GlobalTheory.KZ.StabGal.galB_mem_B ε X hε hj N l w hl2 hN hNl hw s b hb
  have hstabH := fun T hT b hb => GlobalTheory.KZ.B_stable_op ε X hε hj N l w hl2 hN hNl hw T hT b hb
  have hcomm := GlobalTheory.T.hecke_operator_comm_galois_action_modular_tower ε X hε hj N l w hl2 hN hNl hw
  have hcont := GlobalTheory.KZ.GalCont.galB_cont ε X hε hj N l w hl2 hN hNl hw
  have hes := GlobalTheory.T.eichlerShimura_frobenius_quadratic_mod_prime_pow ε X hε hj N l w hl2 hN hNl hw
  obtain ⟨hfree, hfin⟩ := GlobalTheory.KZ.B_free_finite ε X hε hj N l w hl2 hN hNl hw
  classical
  set B := X.B N l w with hBdef
  let ι := Fin (Module.finrank ℤ_[l] B)
  let β : Module.Basis ι ℤ_[l] B := Module.finBasis ℤ_[l] B
  let βE := Algebra.TensorProduct.basis E β
  let gs : (Ω ≃ₐ[ℚ] Ω) → (B →ₗ[ℤ_[l]] B) := fun s => (X.galB l s).restrict (fun b hb => hstabG s b hb)
  let hT : ∀ T : Letter, admitted N l T → (B →ₗ[ℤ_[l]] B) := fun T h => (X.op N l T).restrict (fun b hb => hstabH T h b hb)
  let jm := LinearMap.baseChange E B.subtype

  have halg : Function.Injective (algebraMap ℤ_[l] E) := by
    intro a b hab
    have : ‖algebraMap ℤ_[l] E (a - b)‖ = 0 := by rw [map_sub, hab, sub_self, norm_zero]
    rw [hE, norm_eq_zero, sub_eq_zero] at this
    exact this
  have hflat : Module.Flat ℤ_[l] E := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro e he
    obtain ⟨⟨a, ha⟩, hae⟩ := (Submodule.mem_torsion_iff e).1 he
    have ha0 : a ≠ 0 := fun h => by simp [h] at ha
    change a • e = 0 at hae
    rw [Algebra.smul_def] at hae
    rcases mul_eq_zero.1 hae with h | h
    · exact absurd ((map_eq_zero_iff _ halg).1 h) ha0
    · simp [h]
  have hjinj : Function.Injective jm := by
    rw [show (jm : E ⊗[ℤ_[l]] B → E ⊗[ℤ_[l]] X.Fn l) = LinearMap.lTensor E B.subtype from
      LinearMap.baseChange_eq_ltensor _]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ B.injective_subtype

  have hjG : ∀ s z, X.galV l E s (jm z) = jm ((gs s).baseChange E z) := by
    intro s z
    show ((X.galB l s).baseChange E ∘ₗ B.subtype.baseChange E) z = (B.subtype.baseChange E ∘ₗ (gs s).baseChange E) z
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    rfl
  have hjH : ∀ T (h : admitted N l T) z, X.opV N l E T (jm z) = jm ((hT T h).baseChange E z) := by
    intro T h z
    show ((X.op N l T).baseChange E ∘ₗ B.subtype.baseChange E) z = (B.subtype.baseChange E ∘ₗ (hT T h).baseChange E) z
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    rfl
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hx
  let zc : ι → E := ⇑(βE.repr z)
  let A : (Ω ≃ₐ[ℚ] Ω) → Matrix ι ι ℤ_[l] := fun s => LinearMap.toMatrix β β (gs s)

  have heigc : ∀ T (h : admitted N l T), (LinearMap.toMatrix β β (hT T h)).map (algebraMap ℤ_[l] E) *ᵥ zc = lam T • zc := by
    intro T h
    have h1 : (hT T h).baseChange E z = lam T • z := by
      refine hjinj ?_
      rw [map_smul, ← hjH T h]
      exact heig T h
    rw [show zc = ⇑(βE.repr z) from rfl, ← repr_baseChange, h1, map_smul]
    rfl

  let bF : ι → X.Fn l := fun i => (β i : X.Fn l)
  have hbF : LinearIndependent ℤ_[l] bF := β.linearIndependent.map' B.subtype (by simp)
  have hsum : ∀ (φ : B →ₗ[ℤ_[l]] B) (j : ι), (∑ i, LinearMap.toMatrix β β φ i j • bF i) = ((φ (β j) : B) : X.Fn l) := by
    intro φ j
    simp only [LinearMap.toMatrix_apply, bF]
    have h := congrArg (fun v : B => (v : X.Fn l)) (β.sum_repr (φ (β j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h
  have hgs_mul : ∀ s s', gs (s * s') = gs s ∘ₗ gs s' := by
    intro s s'
    ext b
    simp [gs, Tower.galB_mul]
  have hA : ∀ s s', A (s * s') = A s * A s' := by
    intro s s'
    simp only [A]
    rw [hgs_mul, LinearMap.toMatrix_comp β β β]
  have hone : ∀ j : ι, (∑ i, (1 : Matrix ι ι ℤ_[l]) i j • bF i) = bF j := by
    intro j
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [Matrix.one_apply_ne hi, zero_smul])
      (fun h => absurd (Finset.mem_univ j) h), Matrix.one_apply_eq, one_smul]
  have hAc : ∀ k : ℕ, ∃ E0 : Finset Ω, ∀ s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) →
      ∀ i j, (A s' - 1) i j ∈ (idl l) ^ k := by
    intro k
    obtain ⟨m, hm⟩ := small_coeffs l bF hbF k
    choose E0 hE0 using fun j : ι => hcont (bF j) (β j).2 m
    refine ⟨Finset.univ.biUnion E0, fun s' hs' i j => ?_⟩
    have hfix : ∀ x ∈ E0 j, s' x = x := fun x hx => hs' x (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hx⟩)
    refine hm (fun i => (A s' - 1) i j) ?_ i
    intro u
    have h2 : (∑ i, (A s' - 1) i j • bF i) = X.galB l s' (bF j) - bF j := by
      simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, hone]
      rw [hsum (gs s') j]
      rfl
    rw [h2]
    exact hE0 j s' hfix u
  have hF : ∀ k : ℕ, ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ σ : Ω ≃ₐ[ℚ] Ω, FrobAt q σ →
      ∃ R : Matrix ι ι ℤ_[l], (∀ i j, R i j ∈ (idl l) ^ k) ∧
        ((A σ).map (algebraMap ℤ_[l] E) * (A σ).map (algebraMap ℤ_[l] E) - t σ • (A σ).map (algebraMap ℤ_[l] E)
          + d σ • (1 : Matrix ι ι E)) *ᵥ zc = R.map (algebraMap ℤ_[l] E) *ᵥ zc := by
    intro k
    obtain ⟨m, hm⟩ := small_coeffs l bF hbF k
    obtain ⟨S1, hS1⟩ := hes m
    refine ⟨S1 ∪ S0 ∪ (N * l).primeFactors, fun q hq hqS σ hσ => ?_⟩
    simp only [Finset.mem_union, not_or, Nat.mem_primeFactors] at hqS
    obtain ⟨⟨hq1, hq0⟩, hq2⟩ := hqS
    have hNl0 : N * l ≠ 0 := Nat.mul_ne_zero (by omega) (Fact.out : l.Prime).ne_zero
    have hndvd : ¬ q ∣ N * l := fun h => hq2 ⟨hq, h, hNl0⟩
    have hadmT : admitted N l (Letter.T q) := ⟨hq, hndvd⟩
    have hadmD : admitted N l (Letter.D q) :=
      (Nat.Prime.coprime_iff_not_dvd hq).2 (fun h => hndvd (Dvd.dvd.mul_right h l))
    obtain ⟨htq, hdq⟩ := hfr q hq hq0 σ hσ
    let Rφ : B →ₗ[ℤ_[l]] B := gs σ ∘ₗ gs σ - hT _ hadmT ∘ₗ gs σ + ((q : ℤ_[l]) ^ (w + 1)) • hT _ hadmD
    refine ⟨LinearMap.toMatrix β β Rφ, fun i j => ?_, ?_⟩
    · refine hm (fun i => LinearMap.toMatrix β β Rφ i j) ?_ i
      intro u
      rw [hsum Rφ j]
      exact hS1 q hq hq1 σ hσ (bF j) (β j).2 u
    · have hc : hT _ hadmT ∘ₗ gs σ = gs σ ∘ₗ hT _ hadmT := by
        exact LinearMap.ext fun b => Subtype.ext (hcomm _ hadmT σ b b.2)
      have hcm : LinearMap.toMatrix β β (hT _ hadmT) * A σ = A σ * LinearMap.toMatrix β β (hT _ hadmT) := by
        simp only [A]
        rw [← LinearMap.toMatrix_comp β β β, ← LinearMap.toMatrix_comp β β β, hc]
      have hR : LinearMap.toMatrix β β Rφ = A σ * A σ - LinearMap.toMatrix β β (hT _ hadmT) * A σ
          + ((q : ℤ_[l]) ^ (w + 1)) • LinearMap.toMatrix β β (hT _ hadmD) := by
        simp only [Rφ, map_add (f := _), map_sub, map_smul, LinearMap.toMatrix_comp β β β]
        rfl
      have hmap : (LinearMap.toMatrix β β Rφ).map (algebraMap ℤ_[l] E) =
          (A σ).map (algebraMap ℤ_[l] E) * (A σ).map (algebraMap ℤ_[l] E)
          - (LinearMap.toMatrix β β (hT _ hadmT)).map (algebraMap ℤ_[l] E) * (A σ).map (algebraMap ℤ_[l] E)
          + (algebraMap ℤ_[l] E ((q : ℤ_[l]) ^ (w + 1))) •
            (LinearMap.toMatrix β β (hT _ hadmD)).map (algebraMap ℤ_[l] E) := by
        rw [hR]
        ext i j
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
          smul_eq_mul, map_add, map_sub, map_mul, map_sum]
      have hHa : (LinearMap.toMatrix β β (hT _ hadmT)).map (algebraMap ℤ_[l] E) * (A σ).map (algebraMap ℤ_[l] E) =
          (A σ).map (algebraMap ℤ_[l] E) * (LinearMap.toMatrix β β (hT _ hadmT)).map (algebraMap ℤ_[l] E) := by
        rw [← Matrix.map_mul, hcm, Matrix.map_mul]
      rw [hmap, hHa]
      simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.one_mulVec]
      rw [heigc _ hadmT, heigc _ hadmD, Matrix.mulVec_smul, htq, hdq, smul_smul]
      simp [map_pow, map_natCast]
  have hY := matrix_relation l hE A t d zc hA hAc ht hd hF (fun s E0 S => exists_fixing_mul_frobAt s E0 S) s
  have hW : (gs s).baseChange E ((gs s).baseChange E z) - t s • (gs s).baseChange E z + d s • z = 0 := by
    apply βE.repr.injective
    rw [map_zero]
    apply DFunLike.coe_injective
    rw [Finsupp.coe_zero]
    refine Eq.trans ?_ hY
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec]
    rw [map_add (f := _), map_sub, map_smul, map_smul, Finsupp.coe_add,
      Finsupp.coe_sub, Finsupp.coe_smul, Finsupp.coe_smul, repr_baseChange, repr_baseChange]
  show X.galV l E s (X.galV l E s (jm z)) - t s • X.galV l E s (jm z) + d s • jm z = 0
  calc _ = jm ((gs s).baseChange E ((gs s).baseChange E z) - t s • (gs s).baseChange E z + d s • z) := by
        rw [map_add (f := _), map_sub, map_smul, map_smul, hjG, hjG]
    _ = 0 := by rw [hW, map_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CayleyHamiltonHeckeEigenvectorEveryGaloisElementStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayleyHamilton_heckeEigenvector_every_galois_element : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [NormedField E] [IsAlgClosed E] [Algebra ℤ_[l] E], (∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) → ∀ (lam : Letter → E) (t d : (Ω ≃ₐ[ℚ] Ω) → E) (S0 : Finset ℕ), (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖t (s * s') - t (s)‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖d (s * s') - d (s)‖ < δ) → (∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s → t s = lam (Letter.T q) ∧ d s = (q : E) ^ (w + 1) * lam (Letter.D q)) → ∀ x ∈ X.VB N l w E, (∀ T : Letter, admitted N l T → X.opV N l E T x = lam T • x) → ∀ s : Ω ≃ₐ[ℚ] Ω, X.galV l E s (X.galV l E s x) - t s • X.galV l E s x + d s • x = 0 := by
  first | exact @GlobalTheory.cayleyHamilton_galV | exact GlobalTheory.cayleyHamilton_galV | (intros; apply GlobalTheory.cayleyHamilton_galV <;> assumption)
end
