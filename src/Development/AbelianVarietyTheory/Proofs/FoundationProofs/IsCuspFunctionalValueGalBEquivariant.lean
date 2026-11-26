module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneSubTwoDivLeSquarefreeLabelMass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueGalBEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueGalBEquivariant
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThGal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem exp_gal (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.exp (X.gal s f) = HahnSeries.map (X.exp f) (s : Ω →+* Ω) := by
  ext r; simp [X.gal_exp]

theorem gal_algebraMap (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply X.exp.toRingHom.injective
  show X.exp _ = X.exp _
  rw [exp_gal, AlgHom.commutes, AlgHom.commutes]
  ext r
  have hC : ∀ c : Ω, algebraMap Ω (HahnSeries ℚ Ω) c = HahnSeries.single 0 c := fun c => by
    rw [HahnSeries.algebraMap_apply']
    simp [PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
  simp only [HahnSeries.map_coeff, hC, HahnSeries.coeff_single]
  split_ifs <;> simp

theorem map_mul_gal (s : Ω ≃ₐ[ℚ] Ω) (x y : HahnSeries ℚ Ω) :
    HahnSeries.map (x * y) (s : Ω →+* Ω) = HahnSeries.map x (s : Ω →+* Ω) * HahnSeries.map y (s : Ω →+* Ω) :=
  HahnSeries.map_mul (s : Ω →+* Ω).toNonUnitalRingHom

theorem map_sub_gal (s : Ω ≃ₐ[ℚ] Ω) (x y : HahnSeries ℚ Ω) :
    HahnSeries.map (x - y) (s : Ω →+* Ω) = HahnSeries.map x (s : Ω →+* Ω) - HahnSeries.map y (s : Ω →+* Ω) := by
  ext r; simp

theorem theta_map (s : Ω ≃ₐ[ℚ] Ω) (q : ℚ) (φ : HahnSeries ℚ Ω) :
    theta q (HahnSeries.map φ (s : Ω →+* Ω)) = HahnSeries.map (theta q φ) (s : Ω →+* Ω) := by
  ext r; simp [theta]

theorem cgA_map (A : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) (hA : ∀ x, x ∈ A ↔ s x ∈ A) (l n : ℕ) (x y : Ω)
    (h : CgA A l n x y) : CgA A l n (s x) (s y) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨s z, (hA z).1 hz, by rw [← map_sub, e, map_mul, map_pow, map_natCast]⟩

theorem prim_map (A : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) (hA : ∀ x, x ∈ A ↔ s x ∈ A) (φ : HahnSeries ℚ Ω)
    (h : Prim A φ) : Prim A (HahnSeries.map φ (s : Ω →+* Ω)) := by
  obtain ⟨h1, r, hr, hu⟩ := h
  refine ⟨fun r => by simpa using (hA _).1 (h1 r), r, by simpa using hr, ?_⟩
  simpa [← map_inv₀] using (hA _).1 hu

theorem exists_root [IsAlgClosed Ω] (s : Ω ≃ₐ[ℚ] Ω) (M : ℕ) (hM : 0 < M) :
    ∃ (ζ : Ω) (d e : ℤ), IsPrimitiveRoot ζ M ∧ s ζ = ζ ^ d ∧ (d : ZMod M) * e = 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 hM.ne'⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hs : IsPrimitiveRoot (s ζ) M := hζ.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hs.pow_eq_one
  have hc : i.Coprime M := (hζ.pow_iff_coprime hM i).1 (hi ▸ hs)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
  refine ⟨ζ, i, u, hζ, by rw [zpow_natCast, hi], ?_⟩
  have := congrArg (fun z : ℤ => (z : ZMod M)) huv
  push_cast at this
  rw [ZMod.natCast_self, mul_zero, add_zero] at this
  rw [mul_comm]; exact_mod_cast this

theorem recip_zmod (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (M : ℕ) (hM : 0 < M) (f : X.K)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) (ζ : Ω) (hζ : IsPrimitiveRoot ζ M)
    (d e : ℤ) (hd : s ζ = ζ ^ d) (hde : (d : ZMod M) * e = 1) (δ δ' : SL(2, ℤ))
    (h00 : (en δ' 0 0 : ZMod M) = en δ 0 0) (h01 : (en δ' 0 1 : ZMod M) = e * en δ 0 1)
    (h10 : (en δ' 1 0 : ZMod M) = d * en δ 1 0) (h11 : (en δ' 1 1 : ZMod M) = en δ 1 1) :
    X.gal s (X.sl (ofSL δ') f) = X.sl (ofSL δ) (X.gal s f) := by
  apply X.recip M f hM hf ζ hζ s d hd δ' δ
  refine ⟨h00.symm, ?_, h10.symm, h11.symm⟩
  rw [h01, ← mul_assoc, hde, one_mul]

theorem inv_gal [IsAlgClosed Ω] (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (M : ℕ) (f : X.K)
    (hf : Inv X (CongruenceSubgroup.Gamma1 M) f) : Inv X (CongruenceSubgroup.Gamma1 M) (X.gal s f) := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma1_mem] at hγ
  obtain ⟨M1, hM1, hlev, h00, h11, h10⟩ : ∃ M1 : ℕ, 0 < M1 ∧
      (∀ g ∈ CongruenceSubgroup.Gamma M1, X.sl (ofSL g) f = f) ∧
      ((en γ 0 0 : ℤ) : ZMod M1) = 1 ∧ ((en γ 1 1 : ℤ) : ZMod M1) = 1 ∧ ((en γ 1 0 : ℤ) : ZMod M1) = 0 := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      obtain ⟨M0, h0, hl⟩ := X.level f
      obtain ⟨a, b, c⟩ := hγ
      have a' : en γ 0 0 = 1 := by simpa [en] using a
      have b' : en γ 1 1 = 1 := by simpa [en] using b
      have c' : en γ 1 0 = 0 := by simpa [en] using c
      exact ⟨M0, h0, hl, by simp [a'], by simp [b'], by simp [c']⟩
    · refine ⟨M, h, fun g hg => hf g ?_, hγ⟩
      rw [CongruenceSubgroup.Gamma_mem] at hg
      rw [CongruenceSubgroup.Gamma1_mem]
      exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩
  obtain ⟨ζ, d, e, hζ, hd, hde⟩ := exists_root s M1 hM1
  have hT : ModularGroup.T ^ (e * en γ 0 1) ∈ CongruenceSubgroup.Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.coe_T_zpow]
  have key := recip_zmod X s M1 hM1 f hlev ζ hζ d e hd hde γ (ModularGroup.T ^ (e * en γ 0 1))
    (by simp [en, ModularGroup.coe_T_zpow]; exact h00.symm) (by simp [en, ModularGroup.coe_T_zpow])
    (by simp [en, ModularGroup.coe_T_zpow]; rw [show (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M1) = 0 from h10, mul_zero])
    (by simp [en, ModularGroup.coe_T_zpow]; exact h11.symm)
  rw [hf _ hT] at key
  exact key.symm

end GlobalTheory.ThGal

namespace GlobalTheory.ThGal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cast_of_dvd {a b : ℕ} (h : a ∣ b) (x y : ℤ) (hxy : (x : ZMod b) = y) : (x : ZMod a) = y :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub x y a).2
    (dvd_trans (Int.natCast_dvd_natCast.2 h) ((ZMod.intCast_eq_intCast_iff_dvd_sub x y b).1 hxy))

theorem exists_twist [IsAlgClosed Ω] (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (N l n : ℕ) (hl : 0 < l) (f : X.K)
    (hf : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) f) (δ : SL(2, ℤ))
    (h1 : δ ∈ CongruenceSubgroup.Gamma1 N) (h2 : -δ ∈ CongruenceSubgroup.Gamma (l ^ n)) :
    ∃ δ' : SL(2, ℤ), δ' ∈ CongruenceSubgroup.Gamma1 N ∧ -δ' ∈ CongruenceSubgroup.Gamma (l ^ n) ∧
      X.gal s (X.sl (ofSL δ') f) = X.sl (ofSL δ) (X.gal s f) := by
  rw [CongruenceSubgroup.Gamma1_mem] at h1
  rw [CongruenceSubgroup.Gamma_mem] at h2
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg] at h2
  obtain ⟨g00, g01, g10, g11⟩ := h2
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    obtain ⟨M0, h0, hlev⟩ := X.level f
    obtain ⟨ζ, d, e, hζ, hd, hde⟩ := exists_root s M0 h0
    obtain ⟨a, b, c⟩ := h1
    have a' : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := by simpa using a
    have b' : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by simpa using b
    have c' : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by simpa using c
    refine ⟨ModularGroup.T ^ (e * en δ 0 1), ?_, ?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.coe_T_zpow]
    · rw [CongruenceSubgroup.Gamma_mem]
      rw [a'] at g00
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, ModularGroup.coe_T_zpow, en]
      refine ⟨by simpa using g00, ?_, by simp, by simpa using g00⟩
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_neg, Int.cast_mul]
      rw [mul_comm, ← neg_mul, g01, zero_mul]
    · apply recip_zmod X s M0 h0 f hlev ζ hζ d e hd hde δ
      · simp [en, ModularGroup.coe_T_zpow, a']
      · simp [en, ModularGroup.coe_T_zpow]
      · simp [en, ModularGroup.coe_T_zpow, c']
      · simp [en, ModularGroup.coe_T_zpow, b']
  · set M1 := N * l ^ n with hM1def
    have hM1 : 0 < M1 := Nat.mul_pos hN (pow_pos hl n)
    have hlev : ∀ g ∈ CongruenceSubgroup.Gamma M1, X.sl (ofSL g) f = f := by
      intro g hg
      apply hf g
      rw [CongruenceSubgroup.Gamma_mem] at hg
      rw [CongruenceSubgroup.Gamma1_mem]
      exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩
    obtain ⟨ζ, d, e, hζ, hd, hde⟩ := exists_root s M1 hM1
    let m : Matrix (Fin 2) (Fin 2) (ZMod M1) :=
      !![(en δ 0 0 : ZMod M1), e * en δ 0 1; d * en δ 1 0, en δ 1 1]
    have hm : m.det = 1 := by
      rw [Matrix.det_fin_two_of]
      have hdet : en δ 0 0 * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
        have := δ.det_coe; rw [Matrix.det_fin_two] at this; exact this
      have := congrArg (fun z : ℤ => (z : ZMod M1)) hdet
      push_cast at this
      linear_combination this - ((en δ 0 1 : ZMod M1) * en δ 1 0) * hde
    obtain ⟨δ', hδ'⟩ := GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M1 ⟨m, hm⟩
    have he : ∀ i j, (((δ' : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod M1) = m i j := fun i j => by
      have := congrArg (fun g : SL(2, ZMod M1) => (g : Matrix (Fin 2) (Fin 2) (ZMod M1)) i j) hδ'
      simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this
    have e00 : (en δ' 0 0 : ZMod M1) = en δ 0 0 := he 0 0
    have e01 : (en δ' 0 1 : ZMod M1) = ((e * en δ 0 1 : ℤ) : ZMod M1) := by rw [Int.cast_mul]; exact he 0 1
    have e10 : (en δ' 1 0 : ZMod M1) = ((d * en δ 1 0 : ℤ) : ZMod M1) := by rw [Int.cast_mul]; exact he 1 0
    have e11 : (en δ' 1 1 : ZMod M1) = en δ 1 1 := he 1 1
    have dN : N ∣ M1 := Dvd.intro _ rfl
    have dl : l ^ n ∣ M1 := Dvd.intro_left _ rfl
    refine ⟨δ', ?_, ?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]
      obtain ⟨a, b, c⟩ := h1
      refine ⟨?_, ?_, ?_⟩
      · exact (cast_of_dvd dN _ _ e00).trans a
      · exact (cast_of_dvd dN _ _ e11).trans b
      · refine (cast_of_dvd dN _ _ e10).trans ?_
        rw [Int.cast_mul, show ((en δ 1 0 : ℤ) : ZMod N) = 0 from c, mul_zero]
    · rw [CongruenceSubgroup.Gamma_mem]
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show (((δ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod (l ^ n)) = en δ 0 0 from cast_of_dvd dl _ _ e00]
        exact g00
      · rw [show (((δ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod (l ^ n)) = ((e * en δ 0 1 : ℤ) : ZMod (l ^ n)) from
          cast_of_dvd dl _ _ e01]
        push_cast; rw [← mul_neg]; rw [show -((en δ 0 1 : ℤ) : ZMod (l ^ n)) = 0 from g01, mul_zero]
      · rw [show (((δ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod (l ^ n)) = ((d * en δ 1 0 : ℤ) : ZMod (l ^ n)) from
          cast_of_dvd dl _ _ e10]
        push_cast; rw [← mul_neg]; rw [show -((en δ 1 0 : ℤ) : ZMod (l ^ n)) = 0 from g10, mul_zero]
      · rw [show (((δ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (l ^ n)) = en δ 1 1 from cast_of_dvd dl _ _ e11]
        exact g11
    · exact recip_zmod X s M1 hM1 f hlev ζ hζ d e hd hde δ δ' e00 (by rw [e01]; push_cast; rfl)
        (by rw [e10]; push_cast; rfl) e11

end GlobalTheory.ThGal

namespace GlobalTheory

open GlobalTheory.KZ GlobalTheory.Glue

theorem isThB_galB : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w : ℕ) (s : Ω ≃ₐ[ℚ] Ω), (l : Ω) ∈ A.nonunits → (∀ x, x ∈ A ↔ s x ∈ A) → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n b φ → IsThB X A N l n (X.galB l s b) (HahnSeries.map φ (s : Ω →+* Ω)) := by
  intro Ω _ _ _ ε X A N l _ n w s _ hA b _ φ hb
  obtain ⟨f, hfI, hcls, hδ, hdl⟩ := hb
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hf : ((Units.map (X.gal s).toMonoidHom f : X.Kˣ) : X.K) = X.gal s f := rfl
  refine ⟨Units.map (X.gal s).toMonoidHom f, ?_, ?_, ?_, ?_⟩
  · rw [hf]; exact ThGal.inv_gal X s _ _ hfI
  · have hu : (![(![1, 0] : Fin 2 → ℤ_[l]) 0,
        (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1] : Fin 2 → ℤ_[l]) = ![1, 0] := by
      funext i; fin_cases i <;> simp
    have hg : X.galB l s b ![1, 0] = X.kmap l (X.gal s) (b ![(![1, 0] : Fin 2 → ℤ_[l]) 0,
        (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1]) := rfl
    rw [hu] at hg
    rw [AdicCompletion.eval_apply] at hcls
    rw [hg, AdicCompletion.eval_apply, Tower.kmap]
    erw [AdicCompletion.map_val_apply]
    rw [hcls]
    simp [Tower.cls, LinearMap.reduceModIdeal_apply]
  · intro δ hδ1 hδ2
    obtain ⟨δ', h1, h2, hrec⟩ := ThGal.exists_twist X s N l n hl f hfI δ hδ1 hδ2
    obtain ⟨g, hg, hfg⟩ := hδ δ' h1 h2
    refine ⟨X.gal s g, ThGal.inv_gal X s _ _ hg, ?_⟩
    rw [hf, ← hrec, ← map_mul, hfg, map_pow]
  · obtain ⟨hφ, a, c, κ, hκ, hfa, ha, hc, hcg⟩ := hdl
    refine ⟨fun r => by simpa using (hA _).1 (hφ r), X.gal s a, X.gal s c, s κ, by simpa using hκ, ?_, ?_, ?_, ?_⟩
    · rw [hf, ← ThGal.gal_algebraMap, ← map_mul, ← map_mul, hfa]
    · rw [ThGal.exp_gal]; exact ThGal.prim_map A s hA _ ha
    · rw [ThGal.exp_gal]; exact ThGal.prim_map A s hA _ hc
    · intro r
      rw [ThGal.exp_gal, ThGal.exp_gal, ← ThGal.map_mul_gal, ← ThGal.map_mul_gal, ThGal.theta_map, ThGal.theta_map,
        ← ThGal.map_mul_gal, ← ThGal.map_mul_gal, ← ThGal.map_sub_gal, HahnSeries.map_coeff, HahnSeries.map_coeff]
      exact ThGal.cgA_map A s hA l n _ _ (hcg r)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueGalBEquivariantStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspFunctionalValue_galB_equivariant : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w : ℕ) (s : Ω ≃ₐ[ℚ] Ω), (l : Ω) ∈ A.nonunits → (∀ x, x ∈ A ↔ s x ∈ A) → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n b φ → IsThB X A N l n (X.galB l s b) (HahnSeries.map φ (s : Ω →+* Ω)) := by
  first | exact @GlobalTheory.isThB_galB | exact GlobalTheory.isThB_galB | (intros; apply GlobalTheory.isThB_galB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaDerivationHahnSeriesLeibnizAddConst
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaDerivationHahnSeriesLeibnizAddConst
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue

theorem theta_coeff {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ) (φ : HahnSeries ℚ Ω) (r : ℚ) :
    (theta s φ).coeff r = algebraMap ℚ Ω (s * r) * φ.coeff r := rfl

theorem theta_leibniz_add_const :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ) (P Q : HahnSeries ℚ Ω),
      theta s (P * Q) = theta s P * Q + P * theta s Q ∧ theta s (P + Q) = theta s P + theta s Q ∧
        ∀ c : Ω, theta s (HahnSeries.C c) = 0 := by
  intro Ω _ _ s P Q
  refine ⟨?_, ?_, ?_⟩
  · ext r
    have h1 : (theta s P).support ⊆ P.support := fun t ht h => ht (by simp [theta_coeff, h])
    have h2 : (theta s Q).support ⊆ Q.support := fun t ht h => ht (by simp [theta_coeff, h])
    rw [HahnSeries.coeff_add, HahnSeries.coeff_mul_left' P.isPWO_support h1,
      HahnSeries.coeff_mul_right' Q.isPWO_support h2, theta_coeff, HahnSeries.coeff_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    have := (Finset.mem_addAntidiagonal.1 hij).2.2
    rw [← this, theta_coeff, theta_coeff, mul_add, map_add (f := _)]; ring
  · ext r; simp [theta_coeff, mul_add]
  · intro c; ext r
    rw [theta_coeff]
    by_cases h : r = 0
    · simp [h]
    · simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne h]

end GlobalTheory.Glue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaDerivationHahnSeriesLeibnizAddConstStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaDerivationHahnSeries_leibniz_add_const : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ) (P Q : HahnSeries ℚ Ω), theta s (P * Q) = theta s P * Q + P * theta s Q ∧ theta s (P + Q) = theta s P + theta s Q ∧ ∀ c : Ω, theta s (HahnSeries.C c) = 0 := by
  first | exact @GlobalTheory.Glue.theta_leibniz_add_const | exact GlobalTheory.Glue.theta_leibniz_add_const | (intros; apply GlobalTheory.Glue.theta_leibniz_add_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPrimitiveRootEOmLevel
noncomputable section

namespace GlobalTheory.Glue.Roots

open GlobalTheory.KZ GlobalTheory.K5

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem eOm_pow (ε : Ω →+* ℂ) (x : ℚ) (n : ℕ) : eOm ε x ^ n = eOm ε (n * x) := by
  apply ε.injective
  rw [map_pow, eOm_spec ε ε.injective, eOm_spec ε ε.injective, ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

theorem isPrimitiveRoot_eOm_inv (ε : Ω →+* ℂ) {n : ℕ} (hn : n ≠ 0) :
    IsPrimitiveRoot (eOm ε (1 / (n : ℚ))) n := by
  apply IsPrimitiveRoot.of_map_of_injective (f := ε) _ ε.injective
  rw [eOm_spec ε ε.injective]
  convert Complex.isPrimitiveRoot_exp n hn using 2
  push_cast; ring

theorem isPrimitiveRoot_zt (ε : Ω →+* ℂ) {l : ℕ} (hl : l ≠ 0) (m : ℕ) :
    IsPrimitiveRoot (zt ε l m) (l ^ m) := by
  have h := isPrimitiveRoot_eOm_inv ε (pow_ne_zero m hl)
  rwa [Nat.cast_pow] at h

theorem zt_add_pow (ε : Ω →+* ℂ) {l : ℕ} (hl : l ≠ 0) (m k : ℕ) :
    zt ε l (m + k) ^ l ^ k = zt ε l m := by
  have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl
  rw [zt, zt, eOm_pow]
  congr 1; push_cast; field_simp; ring

theorem zt_succ_pow (ε : Ω →+* ℂ) {l : ℕ} (hl : l ≠ 0) (m : ℕ) :
    zt ε l (m + 1) ^ l = zt ε l m := by
  simpa using zt_add_pow ε hl m 1

theorem eOm_level_pow (ε : Ω →+* ℂ) {N : ℕ} (hN : N ≠ 0) (l m : ℕ) :
    eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ N = zt ε l m := by
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  rw [zt, eOm_pow]
  congr 1
  rw [one_div, one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ hN', one_mul]

theorem isPrimitiveRoot_eOm_level (ε : Ω →+* ℂ) {N l : ℕ} (hN : N ≠ 0) (hl : l ≠ 0) (m : ℕ) :
    IsPrimitiveRoot (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m))) (N * l ^ m) := by
  have h := isPrimitiveRoot_eOm_inv ε (mul_ne_zero hN (pow_ne_zero m hl))
  rwa [Nat.cast_mul, Nat.cast_pow] at h

theorem eOm_isPrimitiveRoot_compatible : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), Function.Injective ε →
    ∀ (l : ℕ), l.Prime → ∀ (N : ℕ), 0 < N → ∀ m : ℕ,
    IsPrimitiveRoot (eOm ε (1 / (l : ℚ) ^ m)) (l ^ m) ∧ eOm ε (1 / (l : ℚ) ^ (m + 1)) ^ l = eOm ε (1 / (l : ℚ) ^ m) ∧
    IsPrimitiveRoot (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m))) (N * l ^ m) ∧
    eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ N = eOm ε (1 / (l : ℚ) ^ m) := by
  intro Ω _ _ _ ε _ l hl N hN m
  have hl0 : l ≠ 0 := hl.ne_zero
  have hN0 : N ≠ 0 := hN.ne'
  exact ⟨isPrimitiveRoot_zt ε hl0 m, zt_succ_pow ε hl0 m, isPrimitiveRoot_eOm_level ε hN0 hl0 m, eOm_level_pow ε hN0 l m⟩

end GlobalTheory.Glue.Roots
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCompletionNoPrimeTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCompletionNoPrimeTorsion
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

theorem rootOfUnity_eq_pow {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Field K] [Algebra Ω K]
    (l : ℕ) (hl : 0 < l) (ζ : Kˣ) (hζ : ζ ^ l = 1) (m : ℕ) (hm : 0 < m) : ∃ η : Kˣ, ζ = η ^ m := by
  have : NeZero l := ⟨hl.ne'⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  have hω' : IsPrimitiveRoot (algebraMap Ω K ω) l := hω.map_of_injective (algebraMap Ω K).injective
  have hζK : (ζ : K) ^ l = 1 := by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
  obtain ⟨i, -, hi⟩ := hω'.eq_pow_of_pow_eq_one hζK
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ω ^ i) hm
  have hz0 : algebraMap Ω K z ≠ 0 := by
    intro h0
    have : (ζ : K) = 0 := by rw [← hi, ← map_pow, ← hz, map_pow, h0, zero_pow hm.ne']
    exact ζ.ne_zero this
  refine ⟨Units.mk0 _ hz0, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, hz, map_pow, hi]

theorem khat_no_l_torsion : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (l : ℕ) [Fact l.Prime] (x : X.Khat l), (l : ℤ_[l]) • x = 0 → x = 0 := by
  intro Ω _ _ _ ε X l _ x hx
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl : 0 < l := (Fact.out : l.Prime).pos
  suffices hn : ∀ n, AdicCompletion.eval (idl l) (X.Kl l) n x = 0 by
    apply AdicCompletion.ext
    intro n
    rw [← AdicCompletion.eval_apply, ← AdicCompletion.eval_apply, hn, map_zero]
  intro n
  obtain ⟨hsurj, hker, hmul, hone, -, -, -⟩ := H3.cls_props Ω ε X l (n + 1)
  obtain ⟨-, hker0, -, hone0, -, -, hred⟩ := H3.cls_props Ω ε X l n
  obtain ⟨f, hf⟩ := hsurj (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x)
  have hpow : ∀ k : ℕ, X.cls l (n + 1) (f ^ k) = k • X.cls l (n + 1) f := by
    intro k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ f k, hmul, ih, succ_nsmul]
  have h1 : X.cls l (n + 1) (f ^ l) = X.cls l (n + 1) 1 := by
    rw [hpow, hone, hf, ← Nat.cast_smul_eq_nsmul ℤ_[l], ← map_smul, hx, map_zero]
  obtain ⟨g, hg⟩ := (hker _ _).1 h1
  rw [one_mul] at hg
  set ζ : X.Kˣ := f * (g ^ (l ^ n))⁻¹ with hζdef
  have hζ : ζ ^ l = 1 := by
    rw [hζdef, mul_pow, hg, inv_pow, ← pow_mul, ← pow_succ, mul_inv_cancel]
  have : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨η, hη⟩ := rootOfUnity_eq_pow (Ω := Ω) l hl ζ hζ (l ^ n) (pow_pos hl n)
  have hf' : f = 1 * (η * g) ^ (l ^ n) := by
    rw [one_mul, mul_pow, ← hη, hζdef, inv_mul_cancel_right]
  rw [hred x f hf.symm, ← hone0]
  exact (hker0 _ _).2 ⟨_, hf'⟩

end GlobalTheory.KZ.BettiB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCompletionNoPrimeTorsionStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCompletion_no_prime_torsion : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (x : X.Khat l), (l : ℤ_[l]) • x = 0 → x = 0 := by
  first | exact @GlobalTheory.KZ.BettiB.khat_no_l_torsion | exact GlobalTheory.KZ.BettiB.khat_no_l_torsion | (intros; apply GlobalTheory.KZ.BettiB.khat_no_l_torsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHahnSeriesScaleTwistRingHom
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHahnSeriesScaleTwistRingHom
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNTwist

noncomputable def twistMap {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h : HahnSeries ℚ Ω) : HahnSeries ℚ Ω' where
  coeff r := χ r * s (h.coeff r)
  isPWO_support' := h.isPWO_support.mono (by
    intro r hr
    simp only [Function.mem_support, ne_eq] at hr ⊢
    intro h0
    exact hr (by rw [h0, map_zero, mul_zero]))

lemma twistMap_coeff {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h : HahnSeries ℚ Ω) (r : ℚ) : (twistMap s χ h).coeff r = χ r * s (h.coeff r) := rfl

lemma twistMap_support {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h : HahnSeries ℚ Ω) : (twistMap s χ h).support ⊆ h.support := by
  intro r hr
  simp only [HahnSeries.mem_support, twistMap_coeff, ne_eq] at hr ⊢
  intro h0
  exact hr (by rw [h0, map_zero, mul_zero])

noncomputable def twistHom {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h0 : χ 0 = 1) (hadd : ∀ r r', χ (r + r') = χ r * χ r') :
    HahnSeries ℚ Ω →+* HahnSeries ℚ Ω' where
  toFun := twistMap s χ
  map_one' := by
    ext r
    rw [twistMap_coeff, HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs with hr
    · subst hr; simp [h0]
    · simp
  map_zero' := by
    ext r
    simp [twistMap_coeff]
  map_add' x y := by
    ext r
    simp [twistMap_coeff, mul_add]
  map_mul' x y := by
    ext a
    show (twistMap s χ (x * y)).coeff a = (twistMap s χ x * twistMap s χ y).coeff a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [twistMap_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_mul, map_sum, Finset.mul_sum]
    have hsub : Finset.antidiagonal (twistMap s χ x).isPWO_support (twistMap s χ y).isPWO_support a ⊆
        Finset.antidiagonal x.isPWO_support y.isPWO_support a :=
      fun ij hij => (Finset.antidiagonal_mono_right (twistMap_support s χ y))
        ((Finset.antidiagonal_mono_left (twistMap_support s χ x)) hij)
    rw [Finset.sum_subset hsub (fun ij hbig hij => ?_)]
    · refine Finset.sum_congr rfl (fun ij hij => ?_)
      have hsum : ij.1 + ij.2 = a := (Finset.mem_antidiagonal.mp hij).2.2
      rw [twistMap_coeff, twistMap_coeff, map_mul, ← hsum, hadd]
      ring
    · have hs : ij.1 + ij.2 = a := (Finset.mem_antidiagonal.mp hbig).2.2
      by_cases h1 : (twistMap s χ x).coeff ij.1 = 0
      · rw [h1, zero_mul]
      · by_cases h2 : (twistMap s χ y).coeff ij.2 = 0
        · rw [h2, mul_zero]
        · exact absurd (Finset.mem_antidiagonal.mpr ⟨h1, h2, hs⟩) hij

end GlobalTheory.FNTwist

theorem GlobalTheory.FNTwist.exists_scale_twist_ringHom : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (s : Ω →+* Ω') (l : ℚ) (χ : ℚ → Ω'), 0 < l → χ 0 = 1 → (∀ r r', χ (r + r') = χ r * χ r') → ∃ Φ : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω', ∀ h r, (Φ h).coeff (r * l) = χ r * s (h.coeff r) := by
  intro Ω Ω' _ _ s l χ hl h0 hadd
  have hinj : Function.Injective (AddMonoidHom.mulRight l) := by
    intro a b hab
    simpa [AddMonoidHom.coe_mulRight, hl.ne'] using hab
  have hmono : ∀ g g' : ℚ, AddMonoidHom.mulRight l g ≤ AddMonoidHom.mulRight l g' ↔ g ≤ g' := by
    intro g g'
    simp only [AddMonoidHom.coe_mulRight]
    exact mul_le_mul_iff_of_pos_right hl
  refine ⟨(HahnSeries.embDomainRingHom (AddMonoidHom.mulRight l) hinj hmono).comp
    (GlobalTheory.FNTwist.twistHom s χ h0 hadd), fun h r => ?_⟩
  rw [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]
  have := HahnSeries.embDomain_coeff (f := ⟨⟨AddMonoidHom.mulRight l, hinj⟩, hmono _ _⟩)
    (x := GlobalTheory.FNTwist.twistHom s χ h0 hadd h) (a := r)
  rw [show χ r * s (h.coeff r) = (GlobalTheory.FNTwist.twistHom s χ h0 hadd h).coeff r from rfl]
  simpa using this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHahnSeriesScaleTwistRingHomStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (s : Ω →+* Ω') (l : ℚ) (χ : ℚ → Ω'), 0 < l → χ 0 = 1 → (∀ r r', χ (r + r') = χ r * χ r') → ∃ Φ : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω', ∀ h r, (Φ h).coeff (r * l) = χ r * s (h.coeff r) := by
  first | exact @GlobalTheory.FNTwist.exists_scale_twist_ringHom | exact GlobalTheory.FNTwist.exists_scale_twist_ringHom | (intros; apply GlobalTheory.FNTwist.exists_scale_twist_ringHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjugateSL2IntLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjugateSL2IntLaws
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.CjLaws

end GlobalTheory.KZ.CjLaws

private lemma mul_eq_cj_mul_of_exists {m : Matrix (Fin 2) (Fin 2) ℤ} {δ : SL(2, ℤ)}
    (h : ∃ δ' : SL(2, ℤ), m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m) :
    m * (δ : Matrix (Fin 2) (Fin 2) ℤ) =
      (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m := by
  unfold _root_.GlobalTheory.KZ.H3.cj
  rw [dite_eq_left h]
  exact h.choose_spec

private lemma eq_of_mul_eq_mul_of_det_ne_zero {m δ₁ δ₂ : Matrix (Fin 2) (Fin 2) ℤ} (hm : m.det ≠ 0)
    (h : δ₁ * m = δ₂ * m) : δ₁ = δ₂ := by
  have h2 : δ₁ * m * adjugate m = δ₂ * m * adjugate m := by rw [h]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.mul_one] at h2
  exact smul_right_injective _ hm h2

private lemma mul_eq_cj_mul_and_cj_mem_gamma (m : Matrix (Fin 2) (Fin 2) ℤ) (M : ℕ) (hm : 0 < m.det)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma (M * m.det.natAbs)) :
    m * (δ : Matrix (Fin 2) (Fin 2) ℤ) =
        (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m ∧
      _root_.GlobalTheory.KZ.H3.cj m δ ∈ CongruenceSubgroup.Gamma M := by
  set d := m.det with hd
  have hd0 : d ≠ 0 := hm.ne'
  have hN : ((M * d.natAbs : ℕ) : ℤ) = (M : ℤ) * d := by
    push_cast
    rw [abs_of_pos hm]
  have hdvd : ∀ i j, ((M : ℤ) * d) ∣
      (δ : Matrix (Fin 2) (Fin 2) ℤ) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    rw [CongruenceSubgroup.Gamma_mem] at hδ
    obtain ⟨h00, h01, h10, h11⟩ := hδ
    intro i j
    rw [← hN, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    fin_cases i <;> fin_cases j <;> simp_all
  choose X hX using hdvd
  set D : Matrix (Fin 2) (Fin 2) ℤ := 1 + (M : ℤ) • (m * Matrix.of X * adjugate m) with hD
  have hδX : (δ : Matrix (Fin 2) (Fin 2) ℤ) = 1 + ((M : ℤ) * d) • Matrix.of X := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← hX i j]
    ring
  have hDm : D * m = m * (δ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [hD, hδX, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      adjugate_mul, ← Matrix.mul_assoc, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_add,
      Matrix.mul_one, Matrix.mul_smul, smul_smul]
  have hdetD : D.det = 1 := by
    have h := congrArg Matrix.det hDm
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one] at h
    exact mul_right_cancel₀ hd0 (by rw [h, one_mul])
  have hex : ∃ δ' : SL(2, ℤ),
      m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m :=
    ⟨⟨D, hdetD⟩, hDm.symm⟩
  have h1 := mul_eq_cj_mul_of_exists hex
  refine ⟨h1, ?_⟩
  have h2 : (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) = D :=
    eq_of_mul_eq_mul_of_det_ne_zero hd0 (by rw [← h1, hDm])
  rw [CongruenceSubgroup.Gamma_mem, h2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hD, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;>
    push_cast <;> simp

theorem _root_.GlobalTheory.KZ.cj_laws : (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (M : ℕ), 0 < m.det →
    ∀ δ ∈ CongruenceSubgroup.Gamma (M * m.det.natAbs),
      m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m ∧
        _root_.GlobalTheory.KZ.H3.cj m δ ∈ CongruenceSubgroup.Gamma M) ∧
    (∀ γ δ : SL(2, ℤ), _root_.GlobalTheory.KZ.H3.cj (γ : Matrix (Fin 2) (Fin 2) ℤ) δ = γ * δ * γ⁻¹) ∧
    (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (δ δ' : SL(2, ℤ)), 0 < m.det →
      m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m →
        ∀ z ∈ _root_.GlobalTheory.KZ.Hs,
          _root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.toGQ m) (_root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.ofSL δ) z) =
            _root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.ofSL δ')
              (_root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.toGQ m) z)) := by
  refine ⟨mul_eq_cj_mul_and_cj_mem_gamma, fun γ δ => ?_, fun m δ δ' hm h => ?_⟩
  · have hex : ∃ δ' : SL(2, ℤ), (γ : Matrix (Fin 2) (Fin 2) ℤ) * (δ : Matrix (Fin 2) (Fin 2) ℤ) =
        (δ' : Matrix (Fin 2) (Fin 2) ℤ) * γ :=
      ⟨γ * δ * γ⁻¹, by simp [Matrix.mul_assoc, Matrix.adjugate_mul]⟩
    have h1 := mul_eq_cj_mul_of_exists hex
    apply Subtype.ext
    refine eq_of_mul_eq_mul_of_det_ne_zero (m := (γ : Matrix (Fin 2) (Fin 2) ℤ)) (by simp) ?_
    rw [← h1]
    simp [Matrix.mul_assoc, Matrix.adjugate_mul]
  · intro z hz
    obtain ⟨-, hmul, -, -, hcoe, hhom⟩ := _root_.GlobalTheory.KZ.mob_laws
    have hδ : (0 : ℤ) < (δ : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
    have hδ' : (0 : ℤ) < (δ' : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
    rw [← hmul _ _ z hz, ← hmul _ _ z hz, ← hcoe, ← hcoe, ← hhom _ _ hm hδ, ← hhom _ _ hδ' hm, h]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjugateSL2IntLawsStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralConjugateSL2Int_laws : (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (M : ℕ), 0 < m.det → ∀ δ ∈ CongruenceSubgroup.Gamma (M * m.det.natAbs), m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m ∧ cj m δ ∈ CongruenceSubgroup.Gamma M) ∧ (∀ γ δ : SL(2, ℤ), cj (γ : Matrix (Fin 2) (Fin 2) ℤ) δ = γ * δ * γ⁻¹) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (δ δ' : SL(2, ℤ)), 0 < m.det → m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m → ∀ z ∈ Hs, mob (toGQ m) (mob (ofSL δ) z) = mob (ofSL δ') (mob (toGQ m) z)) := by
  first | exact @GlobalTheory.KZ.cj_laws | exact GlobalTheory.KZ.cj_laws | (intros; apply GlobalTheory.KZ.cj_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjLevelElemExponentShimura
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjLevelElemExponentShimura
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem _root_.GlobalTheory.exists_primitiveRoot_pow_cyclotomicCharacter {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (l n M : ℕ) [Fact l.Prime] (hM : 0 < M) (hn : l ^ n ∣ M) (s : Ω ≃ₐ[ℚ] Ω) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ M ∧ ∃ i : ℕ, i.Coprime M ∧ s ζ = ζ ^ i ∧
      (i : ZMod (l ^ n)) = PadicInt.toZModPow n (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 hM.ne'⟩
  haveI : NeZero ((l ^ n : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  have hcard : Nat.card (rootsOfUnity M Ω) = M := HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω M
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  set c := modularCyclotomicCharacter Ω hcard s.toRingEquiv with hc
  have hsζ : s ζ = ζ ^ (c : ZMod M).val := by
    have h := modularCyclotomicCharacter.spec Ω hcard s.toRingEquiv hζ.toRootsOfUnity.2
    simpa using h
  refine ⟨ζ, hζ, (c : ZMod M).val, ZMod.val_coe_unit_coprime c, hsζ, ?_⟩
  rw [cyclotomicCharacter.toZModPow]
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hcard' : Nat.card (rootsOfUnity (l ^ n) Ω) = l ^ n :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω (l ^ n)
  set c' := modularCyclotomicCharacter Ω hcard' s.toRingEquiv
  have hζ' : IsPrimitiveRoot (ζ ^ (M / l ^ n)) (l ^ n) :=
    hζ.pow hM (Nat.div_mul_cancel hn).symm
  have h1 : s (ζ ^ (M / l ^ n)) = (ζ ^ (M / l ^ n)) ^ (c : ZMod M).val := by
    rw [map_pow, hsζ, ← pow_mul, ← pow_mul, mul_comm]
  have h2 : s (ζ ^ (M / l ^ n)) = (ζ ^ (M / l ^ n)) ^ (c' : ZMod (l ^ n)).val := by
    have h := modularCyclotomicCharacter.spec Ω hcard' s.toRingEquiv hζ'.toRootsOfUnity.2
    simpa using h
  have hfin : IsOfFinOrder (ζ ^ (M / l ^ n)) :=
    orderOf_pos_iff.1 (by rw [← hζ'.eq_orderOf]; exact Nat.pos_of_ne_zero (NeZero.ne _))
  have h3 := hfin.pow_eq_pow_iff_modEq.1 (h1.symm.trans h2)
  rw [← hζ'.eq_orderOf] at h3
  rw [← ZMod.natCast_zmod_val (c' : ZMod (l ^ n))]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h3

theorem _root_.GlobalTheory.exists_sl2_conj_diag_zmod (M i : ℕ) (hi : i.Coprime M) (γ : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), (_root_.GlobalTheory.KZ.en γ 0 0 : ZMod M) = _root_.GlobalTheory.KZ.en δ 0 0 ∧
      (_root_.GlobalTheory.KZ.en γ 0 1 : ZMod M) = (i : ZMod M) * _root_.GlobalTheory.KZ.en δ 0 1 ∧
      (i : ZMod M) * _root_.GlobalTheory.KZ.en γ 1 0 = _root_.GlobalTheory.KZ.en δ 1 0 ∧
      (_root_.GlobalTheory.KZ.en γ 1 1 : ZMod M) = _root_.GlobalTheory.KZ.en δ 1 1 := by
  set u : (ZMod M)ˣ := ZMod.unitOfCoprime i hi
  have hu : (u : ZMod M) = i := rfl
  have hγdet : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.2
  rw [Matrix.det_fin_two] at hγdet
  set m : Matrix (Fin 2) (Fin 2) (ZMod M) :=
    !![((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod M),
      ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod M);
      (i : ZMod M) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod M),
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod M)] with hm_def
  have hm : m.det = 1 := by
    rw [hm_def, Matrix.det_fin_two_of]
    have h1 : ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * (i : ZMod M) = 1 := by rw [← hu]; exact u.inv_mul
    have h2 := congrArg (Int.cast : ℤ → ZMod M) hγdet
    push_cast at h2
    linear_combination h2 - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod M) *
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod M) * h1
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M ⟨m, hm⟩
  have he : ∀ a b, (((δ : Matrix (Fin 2) (Fin 2) ℤ) a b : ℤ) : ZMod M) = m a b := fun a b => by
    have h := congrArg (fun g : SL(2, ZMod M) => (g : Matrix (Fin 2) (Fin 2) (ZMod M)) a b) hδ
    simpa using h
  refine ⟨δ, ?_, ?_, ?_, ?_⟩ <;> simp only [_root_.GlobalTheory.KZ.en, he, hm_def]
  · simp
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [← mul_assoc, ← hu, Units.mul_inv, one_mul]
  · simp
  · simp

theorem exists_conj_level_exponent :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N l n M : ℕ) [Fact l.Prime], 0 < M → N ∣ M → l ∣ M →
      l ^ n ∣ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (γ : SL(2, ℤ)), γ ∈ Gam N l → ∃ γ'' ∈ Gam N l, ∃ ζ : Ω, IsPrimitiveRoot ζ M ∧
      ∃ d : ℤ, s ζ = ζ ^ d ∧ ((en γ 0 0 : ZMod M) = en γ'' 0 0 ∧ (en γ 0 1 : ZMod M) = d * en γ'' 0 1 ∧
        (d : ZMod M) * en γ 1 0 = en γ'' 1 0 ∧ (en γ 1 1 : ZMod M) = en γ'' 1 1) ∧
        (d : ZMod (l ^ n)) = PadicInt.toZModPow n (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := by
  intro Ω _ _ _ N l n M _ hM hN hl hn s γ hγ
  obtain ⟨ζ, hζ, i, hi, hs, hχ⟩ := exists_primitiveRoot_pow_cyclotomicCharacter l n M hM hn s
  obtain ⟨δ, h00, h01, h10, h11⟩ := exists_sl2_conj_diag_zmod M i hi γ
  have red : ∀ {K : ℕ}, K ∣ M → ∀ {x y : ℤ}, (x : ZMod M) = y → (x : ZMod K) = y := fun {K} hK x y h => by
    simpa only [map_intCast] using congrArg (ZMod.castHom hK (ZMod K)) h
  have h10' : (((i : ℤ) * en γ 1 0 : ℤ) : ZMod M) = en δ 1 0 := by push_cast; exact h10
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨a1, a2, a3⟩ := (CongruenceSubgroup.Gamma1_mem N γ).1 hγ1
  have a4 := CongruenceSubgroup.Gamma0_mem.1 hγ0
  refine ⟨δ, Subgroup.mem_inf.2 ⟨(CongruenceSubgroup.Gamma1_mem N δ).2 ⟨?_, ?_, ?_⟩,
    CongruenceSubgroup.Gamma0_mem.2 ?_⟩, ζ, hζ, i, by rw [zpow_natCast, hs], ⟨h00, ?_, ?_, h11⟩, ?_⟩
  · exact (red hN h00).symm.trans a1
  · exact (red hN h11).symm.trans a2
  · refine (red hN h10').symm.trans ?_
    have : (en γ 1 0 : ZMod N) = 0 := a3
    rw [Int.cast_mul, this, mul_zero]
  · refine (red hl h10').symm.trans ?_
    have : (en γ 1 0 : ZMod l) = 0 := a4
    rw [Int.cast_mul, this, mul_zero]
  · simpa only [Int.cast_natCast] using h01
  · simpa only [Int.cast_natCast] using h10
  · simpa only [Int.cast_natCast] using hχ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjLevelElemExponentShimuraStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_level_elem_exponent_shimura : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N l n M : ℕ) [Fact l.Prime], 0 < M → N ∣ M → l ∣ M → l ^ n ∣ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (γ : SL(2, ℤ)), γ ∈ Gam N l → ∃ γ'' ∈ Gam N l, ∃ ζ : Ω, IsPrimitiveRoot ζ M ∧ ∃ d : ℤ, s ζ = ζ ^ d ∧ ((en γ 0 0 : ZMod M) = en γ'' 0 0 ∧ (en γ 0 1 : ZMod M) = d * en γ'' 0 1 ∧ (d : ZMod M) * en γ 1 0 = en γ'' 1 0 ∧ (en γ 1 1 : ZMod M) = en γ'' 1 1) ∧ (d : ZMod (l ^ n)) = PadicInt.toZModPow n (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := by
  first | exact @GlobalTheory.exists_conj_level_exponent | exact GlobalTheory.exists_conj_level_exponent | (intros; apply GlobalTheory.exists_conj_level_exponent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHasSumReindexNat
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_hasSum_reindex_nat : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (h : HahnSeries ℚ Ω) (N : ℕ) (n₀ : ℤ) (a : ℕ → Ω) (z v : ℂ), 0 < N → (∀ k : ℕ, h.coeff (((n₀ + k : ℤ) : ℚ) / N) = a k) → (∀ r : ℚ, (∀ k : ℕ, r ≠ ((n₀ + k : ℤ) : ℚ) / N) → h.coeff r = 0) → (HasSum (fun r : ℚ => ε (h.coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) v ↔ HasSum (fun k : ℕ => ε (a k) * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k) (v * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N)))) := by
  intro Ω _ ε h N n₀ a z v hN ha h0
  set g : ℕ → ℚ := fun k => (((n₀ + k : ℤ) : ℚ) / N) with hg
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hinj : Function.Injective g := by
    intro k l hkl
    simp only [hg] at hkl
    have := (div_left_inj' hNq).mp hkl
    have h2 : ((n₀ + k : ℤ)) = n₀ + l := by exact_mod_cast this
    omega
  set f : ℚ → ℂ := fun r => ε (h.coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z) with hf
  have hzero : ∀ r, r ∉ Set.range g → f r = 0 := by
    intro r hr
    have : ∀ k : ℕ, r ≠ ((n₀ + k : ℤ) : ℚ) / N := by
      intro k hk; exact hr ⟨k, hk.symm⟩
    simp [hf, h0 r this]
  set c : ℂ := Complex.exp (2 * Real.pi * Complex.I * n₀ * z / N) with hc
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have hcomp : f ∘ g = fun k : ℕ => (ε (a k) * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k) * c := by
    funext k
    simp only [Function.comp, hf, hg, ha k, hc]
    rw [← Complex.exp_nat_mul, mul_assoc (ε (a k)), ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [← hinj.hasSum_iff hzero, hcomp]
  have hv : v = (v * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N))) * c := by
    rw [hc, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  conv_lhs => rw [hv]
  exact hasSum_mul_right_iff hc0

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerEmbeddingInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerEmbeddingInjective
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section

namespace GlobalTheory.K5.EmbInj

theorem emb_injective : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι →
      Function.Injective ι := by
  intro p _ Ω _ _ hc T n hn ι _
  obtain ⟨hdom, -, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p n hn
  obtain ⟨b, -⟩ := GlobalTheory.K5.OnFree.on_free p n
  haveI : Module.Finite (O0 p) (On p n) := Module.Finite.of_basis b
  haveI : Algebra.IsIntegral (O0 p) (On p n) := Algebra.IsIntegral.of_finite _ _
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  have hker : RingHom.ker (ι : On p n →+* Ω) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := O0 p)
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    have : algebraMap (O0 p) Ω a = 0 := by
      rw [← ι.commutes a]; exact ha
    rw [Ideal.mem_bot]
    exact hc.inj (this.trans (map_zero _).symm)
  intro x hx
  have : x ∈ RingHom.ker (ι : On p n →+* Ω) := hx
  rwa [hker, Ideal.mem_bot] at this

end GlobalTheory.K5.EmbInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerEmbeddingInjectiveStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_embedding_injective : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι → Function.Injective ι := by
  first | exact @GlobalTheory.K5.EmbInj.emb_injective | exact GlobalTheory.K5.EmbInj.emb_injective | (intros; apply GlobalTheory.K5.EmbInj.emb_injective <;> assumption)
end
end
