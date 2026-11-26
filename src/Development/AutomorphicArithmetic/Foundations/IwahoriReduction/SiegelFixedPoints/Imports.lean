module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerElementFixedFieldClosedSubgroup
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Mackey
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombination
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.TwistColumnZero
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.NotDvdOfCoprime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CorestrictionCyclotomicShapiroNormalisedTrace

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.ExistsSeries
section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.RedTopCycM
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L.Zc

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private def E1 (X : Tower Ω ε) (l n : ℕ) [Fact l.Prime] (a b : X.Fn l) : Prop :=
  AdicCompletion.eval (idl l) (X.Kl l) n (a ![1, 0]) = AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0])

private theorem galB_col (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) :
    X.galB l s b ![1, 0] = X.kmap l (X.gal s) (b ![1, 0]) := by
  have hu : (![(![1, 0] : Fin 2 → ℤ_[l]) 0,
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1] : Fin 2 → ℤ_[l]) = ![1, 0] := by
    funext i; fin_cases i <;> simp
  have hg : X.galB l s b ![1, 0] = X.kmap l (X.gal s) (b ![(![1, 0] : Fin 2 → ℤ_[l]) 0,
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1]) := rfl
  rw [hu] at hg
  exact hg

private theorem E1.gal {X : Tower Ω ε} {l n : ℕ} [Fact l.Prime] {a b : X.Fn l} (h : E1 X l n a b) (s : Ω ≃ₐ[ℚ] Ω) :
    E1 X l n (X.galB l s a) (X.galB l s b) := by
  unfold E1 at *
  rw [AdicCompletion.eval_apply, AdicCompletion.eval_apply] at h
  rw [galB_col, galB_col, AdicCompletion.eval_apply, AdicCompletion.eval_apply, Tower.kmap]
  erw [AdicCompletion.map_val_apply, AdicCompletion.map_val_apply]
  rw [h]

private theorem cls_mul_pow (X : Tower Ω ε) (l n : ℕ) [Fact l.Prime] (f v : X.Kˣ) :
    X.cls l n (f * v ^ l ^ n) = X.cls l n f := by
  unfold Tower.cls
  rw [Submodule.Quotient.eq, ofMul_mul, TensorProduct.tmul_add, add_sub_cancel_left, ofMul_pow,
    TensorProduct.tmul_smul, ← Nat.cast_smul_eq_nsmul ℤ_[l]]
  apply Submodule.smul_mem_smul _ Submodule.mem_top
  rw [Ideal.span_singleton_pow]
  push_cast
  exact Ideal.mem_span_singleton_self _

private theorem gal_sl_comm [IsAlgClosed Ω] (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) {σ : Ω ≃ₐ[ℚ] Ω} (hσ : σ ∈ fixMu Ω M)
    {f : X.K} (hf : f ∈ topL X M) (g : SL(2, ℤ)) : X.gal σ (X.sl (ofSL g) f) = X.sl (ofSL g) (X.gal σ f) := by
  rw [mem_lev_iff] at hf
  have hζ := isPrimitiveRoot_eOm ε hM
  exact X.recip M f (Nat.pos_of_ne_zero hM) hf _ hζ σ 1
    (by rw [zpow_one]; exact (mem_fixMu_iff σ).1 hσ _ hζ.pow_eq_one) g g (by simp)

private theorem FF_mul [IsAlgClosed Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N] (x : ZMod N) (c d w : ℕ)
    (gm : (ZMod l)ˣ → SL(2, ℤ)) {σ τ : Ω ≃ₐ[ℚ] Ω} (hσ : σ ∈ fixMu Ω (topMu l n m N))
    (hτ : wkMu X l n m N x c d τ ∈ topL X (topMu l n m N)) {u : X.K}
    (hu : wkMu X l n m N x c d (σ * τ) = wkMu X l n m N x c d σ * X.gal σ (wkMu X l n m N x c d τ) * u ^ l ^ n) :
    FF X l n m N x c d w gm (σ * τ) = FF X l n m N x c d w gm σ * X.gal σ (FF X l n m N x c d w gm τ) *
      (∏ r₀ : (ZMod l)ˣ, ∏ γ ∈ Gs N l (topMu l n m N),
        X.sl (ofSL (gm r₀ * liftSL _ γ)) u ^ ex l n w (gm r₀ * liftSL _ γ)) ^ l ^ n := by
  unfold FF
  simp only [map_prod, map_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r₀ _ => Finset.prod_congr rfl fun γ _ => ?_
  rw [hu, map_mul, map_mul, map_pow, gal_sl_comm X (NeZero.ne _) hσ hτ, mul_pow, mul_pow]
  ring

private theorem coc_col [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N]
    (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (hp : Par l N c d gm) (x : ZMod N) (w m n c₀ : ℕ) (hw : Odd w) (hm : 1 ≤ m)
    (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l)
    (hB : ∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) (bB σ))
    {σ τ : Ω ≃ₐ[ℚ] Ω} (hσ : σ ∈ fixMu Ω (topMu l n m N)) (hτ : τ ∈ fixMu Ω (topMu l n m N)) :
    E1 X l n (bB (σ * τ)) (bB σ + X.galB l σ (bB τ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨hmem, hco⟩ := wcoc ε X l N c d gm hp x m n hm
  obtain ⟨u, -, hu0, hu⟩ := hco σ hσ τ hτ
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  obtain ⟨hadd, -, hgal, -⟩ := witalg ε X l N n hN1
  obtain ⟨f₁, e₁, w₁⟩ := wit ε X l N c d gm hp x w m n c₀ hw hm σ _ (hB σ hσ)
  obtain ⟨f₂, e₂, w₂⟩ := wit ε X l N c d gm hp x w m n c₀ hw hm τ _ (hB τ hτ)
  obtain ⟨f₃, e₃, w₃⟩ := wit ε X l N c d gm hp x w m n c₀ hw hm (σ * τ) _ (hB _ (mul_mem hσ hτ))
  have hF := FF_mul X l n m N x c d w gm hσ (hmem τ).1 hu
  set U : X.K := ∏ r₀ : (ZMod l)ˣ, ∏ γ ∈ Gs N l (topMu l n m N),
    X.sl (ofSL (gm r₀ * liftSL _ γ)) u ^ ex l n w (gm r₀ * liftSL _ γ) with hUdef
  have hU0 : U ≠ 0 := Finset.prod_ne_zero_iff.2 fun r₀ _ => Finset.prod_ne_zero_iff.2 fun γ _ =>
    pow_ne_zero _ ((map_ne_zero _).2 hu0)
  let v : X.Kˣ := Units.mk0 (U ^ l ^ c₀) (pow_ne_zero _ hU0)
  have hfv : f₃ = (f₁ * Units.map (X.gal σ).toMonoidHom f₂) * v ^ l ^ n := by
    apply Units.ext
    have hv : ((v ^ l ^ n : X.Kˣ) : X.K) = (U ^ l ^ c₀) ^ l ^ n := by simp [v]
    have hg : ((Units.map (X.gal σ).toMonoidHom f₂ : X.Kˣ) : X.K) = X.gal σ f₂ := rfl
    rw [Units.val_mul, Units.val_mul, hv, hg, e₃, hF, e₁, e₂, map_pow, mul_pow, mul_pow]
    ring
  have h12 := hadd _ _ _ _ w₁ (hgal σ _ _ w₂)
  show AdicCompletion.eval (idl l) (X.Kl l) n _ = AdicCompletion.eval (idl l) (X.Kl l) n _
  rw [w₃.2.1, h12.2.1, hfv, cls_mul_pow]

private theorem cycM_mul' [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] (s t : Ω ≃ₐ[ℚ] Ω) :
    cycM M (s * t) = cycM M s * cycM M t := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have h1 := cycM_apply M (s * t) hζ.pow_eq_one
  rw [AlgEquiv.mul_apply, cycM_apply M t hζ.pow_eq_one, map_pow, cycM_apply M s hζ.pow_eq_one, ← pow_mul] at h1
  apply Units.ext
  apply ZMod.val_injective
  refine hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ?_
  rw [← h1, Units.val_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hζ.pow_eq_one]

private theorem redTop_cycM [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N]
    (y : (ZMod (l ^ (m + n)))ˣ) (s : Ω ≃ₐ[ℚ] Ω)
    (h : s (zt ε l (m + n)) = zt ε l (m + n) ^ (y : ZMod (l ^ (m + n))).val) :
    redTop l n m N (cycM (topM l n m (N * N)) s) = y := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : NeZero l := ⟨hl0⟩
  have hζ : IsPrimitiveRoot (zt ε l (m + n)) (l ^ (m + n)) := by
    have h0 := isPrimitiveRoot_eOm ε (pow_ne_zero (m + n) hl0)
    rw [Nat.cast_pow] at h0
    exact h0
  have hz : zt ε l (m + n) ^ topM l n m (N * N) = 1 := (hζ.pow_eq_one_iff_dvd _).2 (Dvd.intro _ rfl)
  have h1 := cycM_apply (topM l n m (N * N)) s hz
  rw [h] at h1
  have h2 : (y : ZMod (l ^ (m + n))).val ≡ (cycM (topM l n m (N * N)) s : ZMod (topM l n m (N * N))).val [MOD l ^ (m + n)] := by
    have hpos : 0 < l ^ (m + n) := pow_pos (Nat.pos_of_ne_zero hl0) _
    exact hζ.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)
      (by rw [← pow_eq_pow_mod _ hζ.pow_eq_one, ← pow_eq_pow_mod _ hζ.pow_eq_one]; exact h1)
  apply Units.ext
  show ZMod.castHom _ _ ((cycM (topM l n m (N * N)) s : (ZMod (topM l n m (N * N)))ˣ) : ZMod (topM l n m (N * N))) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ← ZMod.natCast_zmod_val (y : ZMod (l ^ (m + n)))]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).2 h2).symm.trans (by simp)

private theorem bTop_coc [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N]
    (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (hp : Par l N c d gm) (x : ZMod N) (w m n c₀ : ℕ) (hw : Odd w) (hm : 1 ≤ m)
    (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l)
    (hB : ∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) (bB σ))
    (s t : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (topM l n m (N * N)))ˣ) :
    E1 X l n (bTop X l n m N bB (s * t) y)
      (bTop X l n m N bB s y + X.galB l s (bTop X l n m N bB t (y * (cycM (topM l n m (N * N)) s)⁻¹))) := by
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have h2 := (witalg ε X l N n hN1).2.2.2
  have hp' : shArg (topM l n m (N * N)) s y ∈ fixMu Ω (topMu l n m N) := shArg_mem_fixMu _ s y
  have hq' : shArg (topM l n m (N * N)) t (y * (cycM (topM l n m (N * N)) s)⁻¹) ∈ fixMu Ω (topMu l n m N) :=
    shArg_mem_fixMu _ t _
  have hc := (coc_col ε X l N c d gm hp x w m n c₀ hw hm bB hB hp' hq').gal (repM (topM l n m (N * N)) y)
  have e : shArg (topM l n m (N * N)) (s * t) y =
      shArg (topM l n m (N * N)) s y * shArg (topM l n m (N * N)) t (y * (cycM (topM l n m (N * N)) s)⁻¹) := by
    unfold shArg
    rw [cycM_mul', mul_inv, mul_assoc y]
    simp only [mul_assoc, mul_inv_cancel_left]
  have e2 : repM (topM l n m (N * N)) y * shArg (topM l n m (N * N)) s y =
      s * repM (topM l n m (N * N)) (y * (cycM (topM l n m (N * N)) s)⁻¹) := by
    unfold shArg
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [← e, map_add (f := _), ← h2, e2, h2] at hc
  exact hc

private theorem bMid_coc [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N]
    (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (hp : Par l N c d gm) (x : ZMod N) (w m n c₀ : ℕ) (hw : Odd w) (hm : 1 ≤ m)
    (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l)
    (hB : ∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) (bB σ))
    (s t : Ω ≃ₐ[ℚ] Ω) (z y₀ : (ZMod (l ^ (m + n)))ˣ) (hy₀ : redTop l n m N (cycM (topM l n m (N * N)) s) = y₀) :
    E1 X l n (bMid X l n m N bB (s * t) z)
      (bMid X l n m N bB s z + X.galB l s (bMid X l n m N bB t (z * y₀⁻¹))) := by
  classical
  have hmul : ∀ a b, redTop l n m N (a * b) = redTop l n m N a * redTop l n m N b := fun a b => map_mul _ _ _
  have hinv : ∀ a, redTop l n m N a⁻¹ = (redTop l n m N a)⁻¹ := fun a => map_inv (Units.map _) a
  unfold E1 bMid
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_apply, map_sum, map_sum (X.galB l s), Pi.add_apply, map_add (f := _), Finset.sum_apply, map_sum,
    Finset.sum_apply, map_sum,
    Finset.sum_congr rfl (fun y _ => bTop_coc ε X l N c d gm hp x w m n c₀ hw hm bB hB s t y)]
  simp only [Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_nbij' (fun y => y * (cycM (topM l n m (N * N)) s)⁻¹) (fun y => y * cycM (topM l n m (N * N)) s)
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [hmul, hinv, hy, hy₀]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [hmul, hy, hy₀, inv_mul_cancel_right]
  · intro y _; simp
  · intro y _; simp
  · intro y _; rfl

end UpperTheory.Kd.L.Zc

open UpperTheory.Kd.L.Zc in
theorem UpperTheory.Kd.L.zcoc :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (x : ZMod N) (w m n c₀ : ℕ), Odd w → 1 ≤ m → ∀ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l, (∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) (bB σ)) → (∀ s z, bMid X l n m N bB s z ∈ X.B N l w) ∧ ∀ χ : (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ (m + n)))ˣ, (∀ s, s (zt ε l (m + n)) = zt ε l (m + n) ^ (χ s : ZMod (l ^ (m + n))).val) → ∀ s t, Stab A s → ∀ z (φ₁ φ₂ φ₃ : HahnSeries ℚ Ω), IsThB X A N l n (bMid X l n m N bB (s * t) z) φ₁ → IsThB X A N l n (bMid X l n m N bB s z) φ₂ → IsThB X A N l n (bMid X l n m N bB t (z * (χ s)⁻¹)) φ₃ → ∀ r, CgA A l n (φ₁.coeff r) (φ₂.coeff r + s (φ₃.coeff r)) := by
  intro Ω _ _ _ _ ε X l _ N _ c d gm hp A hA x w m n c₀ hw hm bB hB
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hcop : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hp.cop).symm
  have hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) := by
    obtain ⟨φ, h1, h2⟩ := X.j_hol
    exact ⟨φ, h2, h1⟩
  have hmem : ∀ s z, bMid X l n m N bB s z ∈ X.B N l w := by
    intro s z
    refine Submodule.sum_mem _ fun y _ => ?_
    exact GlobalTheory.T.galB_mem_kummer_invariant_set ε X ε.injective hj N l w hp.odd hp.five hcop hw _ _
      (hB _ (shArg_mem_fixMu (topM l n m (N * N)) s y)).1
  refine ⟨hmem, fun χ hχ s t hs z φ₁ φ₂ φ₃ h₁ h₂ h₃ r => ?_⟩
  have hg := GlobalTheory.T.isCuspFunctionalValue_galB_equivariant Ω ε X A N l n w s hA (fun x => (hs x).symm) _ (hmem t _) _ h₃
  obtain ⟨f₂, w₂, d₂⟩ := (isThB_iff X A N l n _ _).1 h₂
  obtain ⟨f₃, w₃, d₃⟩ := (isThB_iff X A N l n _ _).1 hg
  have hw' := (witalg ε X l N n hN1).1 _ _ _ _ w₂ w₃
  have hE := bMid_coc ε X l N c d gm hp x w m n c₀ hw hm bB hB s t z (χ s) (redTop_cycM l n m N (χ s) s (hχ s))
  have hT : IsThB X A N l n (bMid X l n m N bB (s * t) z) (φ₂ + HahnSeries.map φ₃ (s : Ω →+* Ω)) :=
    (isThB_iff X A N l n _ _).2 ⟨f₂ * f₃, ⟨hw'.1, hE.trans hw'.2.1, hw'.2.2⟩, GlobalTheory.ThAdd.isDl_mul d₂ d₃⟩
  have := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A N l X.j_hol hp.odd hp.cop hp.five hA n w hw _ (hmem _ _) _ _ h₁ hT r
  simpa using this
end

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L
section Helpers
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem cg_mul {A : ValuationSubring Ω} {l n : ℕ} {x y : Ω} (a : Ω) (ha : a ∈ A) (h : CgA A l n x y) :
    CgA A l n (a * x) (a * y) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨a * z, A.mul_mem _ _ ha hz, by rw [← mul_sub, e]; ring⟩

private theorem cg_trans {A : ValuationSubring Ω} {l n : ℕ} {x y u : Ω} (h : CgA A l n x y) (h' : CgA A l n y u) :
    CgA A l n x u := by
  obtain ⟨z, hz, e⟩ := h
  obtain ⟨z', hz', e'⟩ := h'
  exact ⟨z + z', A.add_mem _ _ hz hz', by rw [mul_add, ← e, ← e']; ring⟩

private theorem lp_mem (A : ValuationSubring Ω) (l k : ℕ) : (l : Ω) ^ k ∈ A := pow_mem (natCast_mem A l) k

private theorem inv_nat_mem {A : ValuationSubring Ω} {l D : ℕ} (hp : l.Prime) (hl : (l : Ω) ∈ A.nonunits) (hD : ¬ l ∣ D) :
    (D : Ω)⁻¹ ∈ A := by
  have hv : A.valuation (l : Ω) < 1 := (A.mem_nonunits_iff).1 hl
  rcases A.valuation_lt_one_or_eq_one ⟨(D : Ω), natCast_mem A D⟩ with h | h
  · exfalso
    have hg := Nat.gcd_eq_gcd_ab l D
    rw [(hp.coprime_iff_not_dvd.2 hD : Nat.gcd l D = 1)] at hg
    have e : (1 : Ω) = (l : Ω) * ((Nat.gcdA l D : ℤ) : Ω) + (D : Ω) * ((Nat.gcdB l D : ℤ) : Ω) := by
      exact_mod_cast congrArg (Int.cast : ℤ → Ω) hg
    have h1 : A.valuation ((l : Ω) * ((Nat.gcdA l D : ℤ) : Ω)) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 (intCast_mem A _))) hv
    have h2 : A.valuation ((D : Ω) * ((Nat.gcdB l D : ℤ) : Ω)) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 (intCast_mem A _))) h
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [← e, map_one] at h3
    exact lt_irrefl _ h3
  · rw [← A.valuation_le_one_iff, map_inv₀]
    exact le_of_eq (by simpa using congrArg (·⁻¹) h)

private theorem root_mem (A : ValuationSubring Ω) {ζ : Ω} {M : ℕ} (hM : 0 < M) (h : ζ ^ M = 1) : ζ ∈ A := by
  rcases A.mem_or_inv_mem ζ with h1 | h1
  · exact h1
  · have h0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow hM.ne'] at h
      exact zero_ne_one h
    have e : ζ = (ζ⁻¹) ^ (M - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
      rw [Nat.add_sub_cancel, inv_pow]
      rw [pow_succ] at h
      exact eq_inv_of_mul_eq_one_right h
    rw [e]
    exact pow_mem h1 _

private theorem inZl_mem [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) {A : ValuationSubring Ω} {l k : ℕ} (hp : l.Prime) [NeZero l]
    (hl : (l : Ω) ∈ A.nonunits) {F : Ω} (h : InZl ε l k F) : F ∈ A := by
  obtain ⟨D, hD, hF⟩ := h
  have hz : zt ε l k ∈ A :=
    root_mem A (pow_pos hp.pos k) (IsNTr.isPrimitiveRoot_zt ε l k).pow_eq_one
  have h1 : (D : Ω) * F ∈ A :=
    (Subring.closure_le (t := A.toSubring)).2 (by simpa using hz) hF
  have hD0 : (D : Ω) ≠ 0 := by
    have := algebraRat.charZero Ω
    exact Nat.cast_ne_zero.2 (fun e => hD (e ▸ dvd_zero l))
  have h2 := A.mul_mem _ _ (inv_nat_mem hp hl hD) h1
  rwa [inv_mul_cancel_left₀ hD0] at h2

private theorem inZl_nat_mul {ε : Ω →+* ℂ} {l k : ℕ} {F : Ω} (a : ℕ) (h : InZl ε l k F) : InZl ε l k ((a : Ω) * F) := by
  obtain ⟨D, hD, hF⟩ := h
  refine ⟨D, hD, ?_⟩
  rw [mul_left_comm]
  exact mul_mem (natCast_mem _ a) hF

private theorem exists_chi [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (l L : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) :
    ∃ u : (ZMod (l ^ L))ˣ, s (zt ε l L) = zt ε l L ^ (u : ZMod (l ^ L)).val := by
  have hp : l.Prime := Fact.out
  haveI : NeZero l := ⟨hp.ne_zero⟩
  have hM : 0 < l ^ L := pow_pos hp.pos L
  haveI : NeZero (l ^ L) := ⟨hM.ne'⟩
  have hz := IsNTr.isPrimitiveRoot_zt ε l L
  have hs : IsPrimitiveRoot (s (zt ε l L)) (l ^ L) := hz.map_of_injective s.injective
  obtain ⟨k, hk, e⟩ := hz.eq_pow_of_pow_eq_one hs.pow_eq_one
  have hc : k.Coprime (l ^ L) := (hz.pow_iff_coprime hM k).1 (e ▸ hs)
  refine ⟨ZMod.unitOfCoprime k hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hk, e]

private theorem exists_series (A : ValuationSubring Ω) (f : ℚ → Ω) (hf : ∀ r, f r ∈ A) :
    ∃ g : HahnSeries ℚ Ω, (∀ r, g.coeff r ∈ A) ∧ ∀ i : ℕ, g.coeff (i : ℚ) = f i := by
  classical
  have hpwo : (Set.range (Nat.cast : ℕ → ℚ)).IsPWO := by
    rw [← Set.image_univ]
    exact (Set.isPWO_of_wellQuasiOrderedLE _).image_of_monotone Nat.mono_cast
  refine ⟨⟨fun r => if r ∈ Set.range (Nat.cast : ℕ → ℚ) then f r else 0, hpwo.mono fun r hr => ?_⟩, fun r => ?_, fun i => ?_⟩
  · by_contra h
    exact hr (if_neg h)
  · show (if r ∈ Set.range (Nat.cast : ℕ → ℚ) then f r else 0) ∈ A
    split_ifs
    · exact hf r
    · exact A.zero_mem
  · exact if_pos ⟨i, rfl⟩

end Helpers

section Fib

private def redZ (l n m : ℕ) (x : (ZMod (l ^ (m + n)))ˣ) : (ZMod (l ^ m))ˣ :=
  Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_add_right m n)) (ZMod (l ^ m))).toMonoidHom x

private theorem redZ_redTop (l n m N : ℕ) (y : (ZMod (topM l n m (N * N)))ˣ) :
    redZ l n m (redTop l n m N y) = redM l n m (N * N) y := by
  apply Units.ext
  show (ZMod.castHom _ (ZMod (l ^ m))) ((ZMod.castHom _ (ZMod (l ^ (m + n)))) (y : ZMod (topM l n m (N * N)))) =
    (ZMod.castHom _ (ZMod (l ^ m))) (y : ZMod (topM l n m (N * N)))
  exact RingHom.congr_fun (Subsingleton.elim ((ZMod.castHom (pow_dvd_pow l (Nat.le_add_right m n)) (ZMod (l ^ m))).comp
    (ZMod.castHom (Dvd.intro _ rfl : l ^ (m + n) ∣ topM l n m (N * N)) (ZMod (l ^ (m + n)))))
    (ZMod.castHom (Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right m n)) (N * N)) (ZMod (l ^ m)))) _

private theorem redZ_coe (l n m : ℕ) [Fact l.Prime] (x : (ZMod (l ^ (m + n)))ˣ) :
    ((redZ l n m x : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) = (((x : ZMod (l ^ (m + n))).val : ℕ) : ZMod (l ^ m)) := by
  haveI : NeZero (l ^ (m + n)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  rw [ZMod.natCast_val]
  rfl

private theorem val_iff (l n m : ℕ) [Fact l.Prime] (x : (ZMod (l ^ (m + n)))ˣ) :
    (x : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m] ↔ redZ l n m x = 1 := by
  haveI : NeZero (l ^ (m + n)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  rw [Units.ext_iff, ← ZMod.natCast_eq_natCast_iff]
  rw [redZ_coe]
  simp

private theorem sum_fib {M : Type*} [AddCommMonoid M] (l n m N : ℕ) [Fact l.Prime] [NeZero (topM l n m (N * N))]
    (f : (ZMod (topM l n m (N * N)))ˣ → M) (zh : (ZMod (l ^ (m + n)))ˣ) (y : (ZMod (l ^ m))ˣ) (hy : redZ l n m zh = y)
    [Fintype (ZMod (l ^ (m + n)))ˣ] [Fintype (ZMod (topM l n m (N * N)))ˣ]
    [DecidablePred fun x : (ZMod (l ^ (m + n)))ˣ => (x : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]]
    [∀ x, DecidablePred fun y' => redTop l n m N y' = x] [DecidablePred fun y' => redM l n m (N * N) y' = y] :
    ∑ x ∈ Finset.univ.filter (fun x : (ZMod (l ^ (m + n)))ˣ => (x : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]),
      ∑ y' ∈ Finset.univ.filter (fun y' => redTop l n m N y' = x * zh), f y' =
    ∑ y' ∈ Finset.univ.filter (fun y' => redM l n m (N * N) y' = y), f y' := by
  classical
  have hmul : ∀ a b, redZ l n m (a * b) = redZ l n m a * redZ l n m b := fun a b => map_mul _ a b
  have hinv : ∀ a, redZ l n m a⁻¹ = (redZ l n m a)⁻¹ := fun a => map_inv (Units.map _) a
  have hmaps : ∀ y' ∈ Finset.univ.filter (fun y' => redM l n m (N * N) y' = y),
      redTop l n m N y' * zh⁻¹ ∈ Finset.univ.filter (fun x : (ZMod (l ^ (m + n)))ˣ => (x : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]) := by
    intro y' hy'
    rw [Finset.mem_filter] at hy' ⊢
    refine ⟨Finset.mem_univ _, (val_iff l n m _).2 ?_⟩
    rw [hmul, hinv, redZ_redTop, hy'.2, hy, mul_inv_cancel]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr ?_ fun _ _ => rfl
  ext y'
  have hx1 := (val_iff l n m x).1 (Finset.mem_filter.1 hx).2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨?_, by rw [h, mul_inv_cancel_right]⟩
    rw [← redZ_redTop, h, hmul, hx1, one_mul, hy]
  · rintro ⟨-, h⟩
    rw [← h, inv_mul_cancel_right]

end Fib

section Th
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem appr_one (l n : ℕ) [Fact l.Prime] (hn : 1 ≤ n) : (1 : ℤ_[l]).appr n = 1 := by
  have h1 := PadicInt.appr_lt (1 : ℤ_[l]) n
  have h2 := PadicInt.appr_spec n (1 : ℤ_[l])
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, map_natCast, sub_eq_zero] at h2
  have h3 : ((1 : ℕ) : ZMod (l ^ n)) = (((1 : ℤ_[l]).appr n : ℕ) : ZMod (l ^ n)) := by simpa using h2
  rw [ZMod.natCast_eq_natCast_iff'] at h3
  have hgt : 1 < l ^ n := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
  rw [Nat.mod_eq_of_lt hgt, Nat.mod_eq_of_lt h1] at h3
  exact h3.symm

private theorem thb_sum [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime]
    (n w : ℕ) (hn : 1 ≤ n) (hl : (l : Ω) ∈ A.nonunits) {ι : Type*} (T : Finset ι) (hT : T.Nonempty) (b : ι → X.Fn l)
    (φ : ι → HahnSeries ℚ Ω) (hb : ∀ i, b i ∈ X.B N l w) (h : ∀ i, IsThB X A N l n (b i) (φ i)) :
    IsThB X A N l n (∑ i ∈ T, b i) (∑ i ∈ T, φ i) := by
  classical
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h a
  | cons a T ha hT ih =>
    have := GlobalTheory.ThAdd.isThB_add Ω ε X A N l n w (b a) (∑ i ∈ T, b i) hl (hb a)
      (Submodule.sum_mem _ fun i _ => hb i) 1 1 (φ a) (∑ i ∈ T, φ i) (h a) ih
    rw [appr_one l n hn] at this
    rw [Finset.sum_cons, Finset.sum_cons]
    simpa using this

private theorem thb_coeff {ε : Ω →+* ℂ} {X : Tower Ω ε} {A : ValuationSubring Ω} {N l n : ℕ} [Fact l.Prime] {b : X.Fn l}
    {φ : HahnSeries ℚ Ω} (h : IsThB X A N l n b φ) (r : ℚ) : φ.coeff r ∈ A := by
  obtain ⟨_, _, _, _, h⟩ := h
  exact h.1 r

private theorem isNT_mul {ε : Ω →+* ℂ} {l L m : ℕ} [NeZero l] {F F' : Ω} (k : ℕ) (h : IsNT ε l L m F F') :
    IsNT ε l L m ((l : Ω) ^ k * F) ((l : Ω) ^ k * F') := by
  obtain ⟨τ, hτ, e⟩ := h
  refine ⟨τ, hτ, ?_⟩
  simp only [map_mul, map_pow, map_natCast]
  rw [← Finset.mul_sum, ← e]
  ring

private theorem exists_kappa (l : ℕ) (hp : l.Prime) (κ : ℚ) : ∃ v : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (A : ValuationSubring Ω), (l : Ω) ∈ A.nonunits → (l : Ω) ^ v * (κ : Ω) ∈ A := by
  obtain ⟨v, b, hb, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd κ.den_nz l hp.ne_one
  refine ⟨v, fun {Ω} _ _ A hl => ?_⟩
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hb (h ▸ dvd_zero l))
  have e' : (l : Ω) ^ v * (κ : Ω) = (κ.num : Ω) * (b : Ω)⁻¹ := by
    rw [Rat.cast_def, e]
    push_cast
    field_simp
  rw [e']
  exact A.mul_mem _ _ (intCast_mem A _) (inv_nat_mem hp hl hb)

private theorem small_close {A : ValuationSubring Ω} {l n C L₀ c₂ v c₀ m : ℕ} (hn : n ≤ L₀) {a κ tt T : Ω} (ha : a ∈ A)
    (hT : (l : Ω) ^ c₂ * T ∈ A) (hκ : (l : Ω) ^ v * κ ∈ A) (htt : tt ∈ A) :
    CgA A l n ((l : Ω) ^ (C + (L₀ + c₂ + v)) * a) ((l : Ω) ^ (C + (L₀ + c₂ + v)) * ((l : Ω) ^ c₀ * κ * tt * (l : Ω) ^ m * T)) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨(l : Ω) ^ C * (l : Ω) ^ q * (l : Ω) ^ c₂ * (l : Ω) ^ v * a -
    (l : Ω) ^ C * (l : Ω) ^ q * (l : Ω) ^ c₀ * ((l : Ω) ^ v * κ) * tt * (l : Ω) ^ m * ((l : Ω) ^ c₂ * T), ?_, ?_⟩
  · refine sub_mem ?_ ?_
    · exact A.mul_mem _ _ (A.mul_mem _ _ (A.mul_mem _ _ (A.mul_mem _ _ (lp_mem A l C) (lp_mem A l q)) (lp_mem A l c₂)) (lp_mem A l v)) ha
    · exact A.mul_mem _ _ (A.mul_mem _ _ (A.mul_mem _ _ (A.mul_mem _ _ (A.mul_mem _ _ (A.mul_mem _ _ (lp_mem A l C) (lp_mem A l q)) (lp_mem A l c₀)) hκ) htt) (lp_mem A l m)) hT
  · simp only [pow_add]
    ring

private theorem final_step {A : ValuationSubring Ω} {l n c cc e c₀ m : ℕ} {a Ψ D F0 T E tt κ : Ω}
    (h0 : CgA A l n a Ψ) (h1 : CgA A l n ((l : Ω) ^ c * ((l : Ω) ^ cc * Ψ)) (D + (l : Ω) ^ c * ((l : Ω) ^ (cc + c₀) * F0 * tt)))
    (hF : F0 = κ * (l : Ω) ^ m * T + (l : Ω) ^ n * E) (hE : E ∈ A) (htt : tt ∈ A) :
    CgA A l n ((l : Ω) ^ (c + cc + e) * a) ((l : Ω) ^ (c + cc + e) * ((l : Ω) ^ c₀ * κ * tt * (l : Ω) ^ m * T) + (l : Ω) ^ e * D) := by
  have s1 := cg_mul ((l : Ω) ^ (c + cc + e)) (lp_mem A l _) h0
  have s2 := cg_mul ((l : Ω) ^ e) (lp_mem A l _) h1
  have s3 : CgA A l n ((l : Ω) ^ e * (D + (l : Ω) ^ c * ((l : Ω) ^ (cc + c₀) * F0 * tt)))
      ((l : Ω) ^ (c + cc + e) * ((l : Ω) ^ c₀ * κ * tt * (l : Ω) ^ m * T) + (l : Ω) ^ e * D) := by
    refine ⟨(l : Ω) ^ e * (l : Ω) ^ c * (l : Ω) ^ (cc + c₀) * E * tt,
      A.mul_mem _ _ (A.mul_mem _ _ (A.mul_mem _ _ (A.mul_mem _ _ (lp_mem A l e) (lp_mem A l c)) (lp_mem A l _)) hE) htt, ?_⟩
    rw [hF]
    simp only [pow_add]
    ring
  have e1 : (l : Ω) ^ (c + cc + e) * Ψ = (l : Ω) ^ e * ((l : Ω) ^ c * ((l : Ω) ^ cc * Ψ)) := by
    simp only [pow_add]; ring
  rw [e1] at s1
  exact cg_trans s1 (cg_trans s2 s3)

end Th
end UpperTheory.Kd.L

theorem UpperTheory.Kd.L.law :
    ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (w : ℕ), Odd w → ∃ (c₁ : ℕ) (κ : ℚ), κ ≠ 0 ∧ ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (x : ZMod N) (m n c₀ : ℕ), 1 ≤ m → m ≤ n → ∀ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l, (∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) (bB σ)) → ∀ y : (ZMod (l ^ m))ˣ, ∃ g : HahnSeries ℚ Ω, (∀ r, g.coeff r ∈ A) ∧ ∀ s, Stab A s → (∀ a ∈ A, A.valuation (s a - a) < 1) → s (zt ε l m) = zt ε l m → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n (GlobalTheory.KA.push (redM l n m (N * N)) (bTop X l n m N bB) s y) φ → ∀ tt : ZMod (l ^ n), IsLamG ε l n m s tt → ∀ (β : ℕ) (t a : ℤ), (a : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) → (β : ZMod (l ^ m)) = (y : ZMod (l ^ m)) → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] → ∀ i : ℕ, CgA A l n ((l : Ω) ^ c₁ * φ.coeff (i : ℚ)) ((l : Ω) ^ c₁ * ((l : Ω) ^ c₀ * (κ : Ω) * (tt.val : Ω) * (l : Ω) ^ m * toQ (l ^ m) (pieceT N l m m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a * t, 0) (a * t, 0) (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β) ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i) + (s (g.coeff (i : ℚ)) - g.coeff (i : ℚ))) := by

  intro l _ N _ w hw
  by_cases hl2 : l = 2
  · exact ⟨0, 1, one_ne_zero, fun ε X c d gm P => absurd hl2 P.odd⟩
  have hp : l.Prime := Fact.out
  haveI : NeZero l := ⟨hp.ne_zero⟩
  obtain ⟨κ, hκ, L₀, har⟩ := arith l N w hw.pos
  obtain ⟨c₂, hsm⟩ := small l w L₀
  obtain ⟨cc, hmk⟩ := mackey l
  obtain ⟨c, hcor⟩ := GlobalTheory.T.corestriction_cyclotomic_shapiro_normalisedTrace l hl2
  obtain ⟨v, hv⟩ := exists_kappa l hp κ
  refine ⟨c + cc + (L₀ + c₂ + v), κ, hκ, ?_⟩
  intro Ω _ _ _ _ ε X c' d gm P A hl x m n c₀ hm hmn bB hbB y
  by_cases hsmall : m + n < L₀
  · refine ⟨0, fun r => by simp, ?_⟩
    intro s hs hres hz φ hφ tt htt β t a ha hβ hβ1 ht i
    simp only [HahnSeries.coeff_zero, map_zero, sub_self, add_zero]
    exact small_close (C := c + cc) (by omega) (thb_coeff hφ _)
      (hsm ε N c' d gm P A hl x m hm (by omega) β t a i) (hv A hl) (natCast_mem A _)
  have hL : L₀ ≤ m + n := not_lt.1 hsmall
  have hn : 1 ≤ n := hm.trans hmn
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hj := X.j_hol
  obtain ⟨hB, hcoc⟩ := zcoc ε X l N c' d gm P A hl x w m n c₀ hw hm bB hbB
  choose Φ hΦ using fun s z => GlobalTheory.T.exists_cuspFunctional_oddWeight_oddPrime Ω ε X A N l halg hj hl2 P.cop P.five hl n w hw (bMid X l n m N bB s z) (hB s z)
  choose χ hχ using fun s => exists_chi ε l (m + n) s
  haveI : NeZero (l ^ (m + n)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨zh, hzh⟩ : ∃ zh, redZ l n m zh = y := ZMod.unitsMap_surjective (pow_dvd_pow l (Nat.le_add_right m n)) y
  have hdv : N * l ∣ topMu l n m N := by
    refine ⟨l ^ (m + n - 1) * N, ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, m + n = k + 1 := ⟨m + n - 1, by omega⟩
    simp only [topMu, hk, Nat.add_sub_cancel, pow_succ]
    ring
  obtain ⟨R, hR⟩ := (reps l N c' d gm P (topMu l n m N) hdv).1
  obtain ⟨hFs, hFa⟩ := har ε c' d gm P x m n hm R hR zh
  obtain ⟨ξ, hξA, hξ⟩ := hmk ε X N c' d gm P A hl x w m n c₀ hw hm hn bB hbB R hR zh
  choose F0 hF0 using fun r => GlobalTheory.T.exists_unique_normalizedCyclotomicTrace ε l (m + n) m hm (by omega) (Fsum ε l n m N x c' d w gm R zh r) (hFs r)
  obtain ⟨ξ', hξ'A, hξ'⟩ := hcor ε A hl (m + n) n m hm hmn (by omega) χ hχ
    (fun s u r => (l : Ω) ^ cc * (Φ s (u * zh)).coeff r)
    (fun s u r => A.mul_mem _ _ (lp_mem A l cc) (thb_coeff (hΦ s _).1 r))
    (fun s t hs ht u r => by
      have h := hcoc χ hχ s t hs (u * zh) _ _ _ (hΦ (s * t) _).1 (hΦ s _).1 (hΦ t (u * zh * (χ s)⁻¹)).1 r
      have h' := cg_mul ((l : Ω) ^ cc) (lp_mem A l cc) h
      rw [mul_add] at h'
      simp only [map_mul, map_pow, map_natCast]
      rwa [show u * (χ s)⁻¹ * zh = u * zh * (χ s)⁻¹ from mul_right_comm _ _ _])
    ξ (fun r => (l : Ω) ^ (cc + c₀) * Fsum ε l n m N x c' d w gm R zh r)
    (fun r => ⟨hξA r, by simpa using inZl_nat_mul (l ^ (cc + c₀)) (hFs r)⟩)
    (fun s hs hres h1 tt htt r => by
      have hz : s (zt ε l (m + n)) = zt ε l (m + n) := by
        have hgt : 1 < l ^ (m + n) := Nat.one_lt_pow (by omega) hp.one_lt
        rw [hχ s, h1, Units.val_one, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hgt, pow_one]
      have h := hξ s hs hres hz tt htt _ (hΦ s zh).1 r
      rw [one_mul]
      have e : (l : Ω) ^ (cc + c₀) * Fsum ε l n m N x c' d w gm R zh r * (tt.val : Ω) =
          (l : Ω) ^ cc * ((l : Ω) ^ c₀ * Fsum ε l n m N x c' d w gm R zh r * (tt.val : Ω)) := by
        rw [pow_add]; ring
      rwa [e])
    (fun r => (l : Ω) ^ (cc + c₀) * F0 r) (fun r => isNT_mul _ (hF0 r).1)
  obtain ⟨g, hgA, hg⟩ := exists_series A (fun r => (l : Ω) ^ (L₀ + c₂ + v) * ξ' r)
    (fun r => A.mul_mem _ _ (lp_mem A l _) (hξ'A r))
  refine ⟨g, hgA, ?_⟩
  intro s hs hres hzm φ hφ tt htt β t a ha hβ hβ1 ht i
  have hone : (1 : (ZMod (l ^ (m + n)))ˣ) ∈ Finset.univ.filter
      (fun u : (ZMod (l ^ (m + n)))ˣ => (u : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, (val_iff l n m 1).2 (map_one (Units.map _))⟩
  have hthb := thb_sum X A N l n w hn hl _ ⟨1, hone⟩ (fun u => bMid X l n m N bB s (u * zh))
    (fun u => Φ s (u * zh)) (fun u => hB s _) (fun u => (hΦ s _).1)
  have hpush : ∑ u ∈ Finset.univ.filter (fun u : (ZMod (l ^ (m + n)))ˣ => (u : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]),
      bMid X l n m N bB s (u * zh) = GlobalTheory.KA.push (redM l n m (N * N)) (bTop X l n m N bB) s y := by
    simp only [bMid, GlobalTheory.KA.push]
    exact sum_fib l n m N (bTop X l n m N bB s) zh y hzh
  rw [hpush] at hthb
  have hmem : GlobalTheory.KA.push (redM l n m (N * N)) (bTop X l n m N bB) s y ∈ X.B N l w := by
    rw [← hpush]
    exact Submodule.sum_mem _ fun u _ => hB s _
  have h0 := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A N l hj hl2 P.cop P.five hl n w hw _ hmem φ _ hφ hthb (i : ℚ)
  have hβ' : β ≡ (zh : ZMod (l ^ (m + n))).val [MOD l ^ m] := by
    rw [← ZMod.natCast_eq_natCast_iff, hβ, ← redZ_coe, hzh]
  obtain ⟨E, hE, hFE⟩ := hFa hL i (F0 i) (hF0 i).1 β t a ha hβ' hβ1 ht
  have h1 := hξ' s hs hres hzm tt htt (i : ℚ)
  simp only [← Finset.mul_sum] at h1
  have hΨ : (∑ u ∈ Finset.univ.filter (fun u : (ZMod (l ^ (m + n)))ˣ => (u : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]),
      Φ s (u * zh)).coeff (i : ℚ) = ∑ u ∈ Finset.univ.filter (fun u : (ZMod (l ^ (m + n)))ˣ => (u : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]),
      (Φ s (u * zh)).coeff (i : ℚ) := HahnSeries.coeff_sum _
  rw [← hΨ] at h1
  have hfin := final_step (e := L₀ + c₂ + v) (c₀ := c₀) h0 h1 hFE (inZl_mem ε hp hl hE) (natCast_mem A tt.val)
  have eg : s (g.coeff (i : ℚ)) - g.coeff (i : ℚ) = (l : Ω) ^ (L₀ + c₂ + v) * (s (ξ' (i : ℚ)) - ξ' (i : ℚ)) := by
    rw [hg i, map_mul, map_pow, map_natCast, mul_sub]
  rw [eg]
  exact hfin
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Actcls
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private noncomputable def evF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) : Submodule ℤ_[l] (X.Fn l) :=
  Submodule.pi Set.univ fun _ => LinearMap.ker (AdicCompletion.eval (idl l) (X.Kl l) n)

private theorem mem_evF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (b : X.Fn l) :
    b ∈ evF X l n ↔ ∀ u, AdicCompletion.eval (idl l) (X.Kl l) n (b u) = 0 := by
  simp only [evF, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_ker]

private theorem eval_eq_zero_of_mem (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) {y : X.Khat l}
    (h : y ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))) : AdicCompletion.eval (idl l) (X.Kl l) n y = 0 := by
  refine Submodule.smul_induction_on h (fun r hr z _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n z)
    rw [← hx, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [map_add (f := _), hx, hy, add_zero]

private theorem lnFn_le_evF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) : lnFn X l n ≤ evF X l n := by
  intro b hb
  rw [mem_evF]
  intro u
  exact eval_eq_zero_of_mem X l n ((Submodule.mem_pi.mp hb) u (Set.mem_univ u))

private theorem eval_kmap_zero (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : X.K ≃+* X.K) {y : X.Khat l}
    (h : AdicCompletion.eval (idl l) (X.Kl l) n y = 0) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ y) = 0 := by
  rw [AdicCompletion.eval_apply] at h ⊢
  simp only [Tower.kmap, LinearMap.coe_restrictScalars, AdicCompletion.map_val_apply, h, map_zero]

private theorem act_mem_evF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) {b : X.Fn l}
    (hb : b ∈ evF X l n) : X.act l m b ∈ evF X l n := by
  rw [mem_evF] at hb ⊢
  intro u
  simp only [Tower.act, LinearMap.coe_mk, AddHom.coe_mk]
  exact eval_kmap_zero X l n _ (hb _)

private noncomputable def sf (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n w : ℕ) (a : X.K) : X.Fn l :=
  fun u => (u 0) ^ w • clsK X l n a

private theorem eval_clsK_eq (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (a : X.K) :
    AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l n a) =
      AdicCompletion.eval (idl l) (X.Kl l) n (GlobalTheory.ZetaB.clsHat X l a) := by
  by_cases ha : a = 0
  · subst ha
    rw [clsK_zero, map_zero, GlobalTheory.ZetaB.eval_clsHat, GlobalTheory.ZetaB.unitOf_zero]
    simp only [Tower.cls, ofMul_one, TensorProduct.tmul_zero, Submodule.Quotient.mk_zero]
  · rw [eval_clsK X l n ha, GlobalTheory.ZetaB.eval_clsHat]
    congr 1
    ext
    rw [Units.val_mk0, GlobalTheory.ZetaB.unitOf_val X ha]

private theorem sf_sub_secT (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n w : ℕ) (a : X.K) :
    sf X l n w a - secT X l w a ∈ evF X l n := by
  rw [mem_evF]
  intro u
  simp only [sf, secT, Pi.sub_apply, map_sub, map_smul, eval_clsK_eq, sub_self]

private theorem act_congr_sf (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {n M : ℕ} (hM : l ^ n ∣ M) (w : ℕ) {a : X.K}
    (ha : a ∈ topL X M) {m m' : SL(2, ℤ)} (h : m * m'⁻¹ ∈ CongruenceSubgroup.Gamma M) :
    X.act l (m : Matrix (Fin 2) (Fin 2) ℤ) (sf X l n w a) - X.act l (m' : Matrix (Fin 2) (Fin 2) ℤ) (sf X l n w a) ∈
      evF X l n := by
  have hd := sf_sub_secT X l n w a
  have h1 := lnFn_le_evF X l n ((invMod_secT X l hM w ha).act_congr h)
  have h2 := Submodule.sub_mem _ (act_mem_evF X l n (m : Matrix (Fin 2) (Fin 2) ℤ) hd)
    (act_mem_evF X l n (m' : Matrix (Fin 2) (Fin 2) ℤ) hd)
  convert add_mem h1 h2 using 1
  simp only [map_sub]
  abel

private theorem conj_mem_Gam {N l : ℕ} [NeZero N] {t h : SL(2, ℤ)}
    (ht : t ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) (hh : h ∈ Gam N l) : t * h * t⁻¹ ∈ Gam N l := by
  unfold Gam at hh ⊢
  obtain ⟨htN, htl⟩ := Subgroup.mem_inf.mp ht
  obtain ⟨hh1, hhl⟩ := Subgroup.mem_inf.mp hh
  refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ htl hhl) (Subgroup.inv_mem _ htl)⟩
  have e := (CongruenceSubgroup.Gamma1_mem N h).mp hh1
  have hh0 : h ∈ CongruenceSubgroup.Gamma0 N := CongruenceSubgroup.Gamma0_mem.mpr e.2.2
  let T : CongruenceSubgroup.Gamma0 N := ⟨t, htN⟩
  let H : CongruenceSubgroup.Gamma0 N := ⟨h, hh0⟩
  have hH : H ∈ CongruenceSubgroup.Gamma1' N := (CongruenceSubgroup.Gamma1_to_Gamma0_mem H).mpr e
  have hC : T * H * T⁻¹ ∈ CongruenceSubgroup.Gamma1' N := by
    rw [CongruenceSubgroup.Gamma1_mem'] at hH ⊢
    rw [map_mul, map_mul, hH, mul_one, ← map_mul, mul_inv_cancel, map_one]
  rw [CongruenceSubgroup.Gamma1_to_Gamma0_mem] at hC
  exact (CongruenceSubgroup.Gamma1_mem N _).mpr hC

private theorem sum_congr_conj (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {n N M : ℕ} [NeZero N] [NeZero M] {f : X.Fn l}
    (S : Finset SL(2, ZMod M))
    (hS : ∀ γ, γ ∈ S ↔ γ ∈ (Gam N l).map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))))
    (hf : ∀ m m' : SL(2, ℤ), m * m'⁻¹ ∈ CongruenceSubgroup.Gamma M →
      X.act l (m : Matrix (Fin 2) (Fin 2) ℤ) f - X.act l (m' : Matrix (Fin 2) (Fin 2) ℤ) f ∈ evF X l n)
    (g : SL(2, ℤ)) {g₀ : SL(2, ℤ)} (h₀ : g₀ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) :
    X.act l (g₀ : Matrix (Fin 2) (Fin 2) ℤ) (∑ γ ∈ S, X.act l ((g * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f) -
      ∑ γ ∈ S, X.act l ((g * g₀ * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f ∈ evF X l n := by
  have hg₀i : g₀⁻¹ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l := inv_mem h₀
  have key : ∀ m m' : SL(2, ℤ), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) m =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) m' → m * m'⁻¹ ∈ CongruenceSubgroup.Gamma M := by
    intro m m' h
    rw [CongruenceSubgroup.Gamma_mem', map_mul, map_inv, h, mul_inv_cancel]
  let e : SL(2, ZMod M) ≃ SL(2, ZMod M) :=
    (MulAut.conj (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g₀)⁻¹).toEquiv
  have he : ∀ γ, e γ = (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g₀)⁻¹ * γ *
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g₀ := fun γ => by
    simp [e, MulAut.conj_apply]
  have hmem : ∀ γ, γ ∈ S ↔ e γ ∈ S := by
    intro γ
    rw [hS, hS, he]
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨g₀⁻¹ * h * g₀⁻¹⁻¹, conj_mem_Gam hg₀i hh, ?_⟩
      simp only [map_mul, map_inv, inv_inv]
    · rintro ⟨h, hh, hE⟩
      refine ⟨g₀ * h * g₀⁻¹, conj_mem_Gam h₀ hh, ?_⟩
      rw [map_mul, map_mul, hE, map_inv]
      group
  have hsum : ∑ γ ∈ S, X.act l ((g * g₀ * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f =
      ∑ γ ∈ S, X.act l ((g * g₀ * liftSL M (e γ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f :=
    (Finset.sum_equiv e hmem (fun _ _ => rfl)).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ (fun γ _ => ?_)
  rw [act_act_SL]
  apply hf
  apply key
  simp only [map_mul, map_liftSL, he]
  group

private theorem par_mul {l : ℕ} [Fact l.Prime] {N c d : ℕ} {gm : (ZMod l)ˣ → SL(2, ℤ)} (hP : Par l N c d gm) {g₀ : SL(2, ℤ)}
    (h₀ : g₀ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) : Par l N c d (fun r => gm r * g₀) := by
  obtain ⟨h0N, h0l⟩ := Subgroup.mem_inf.mp h₀
  have hN := (CongruenceSubgroup.Gamma0_mem).mp h0N
  rw [CongruenceSubgroup.Gamma0_mem] at h0l
  refine ⟨hP.odd, hP.five, hP.cop, hP.c1, hP.d1, hP.cc, hP.dc, fun r => ?_, fun r => ?_, fun r => ?_⟩
  · exact Subgroup.mul_mem _ (hP.g0 r) h0N
  · have h := hP.ga r
    have hx : ((g₀.1 1 0 : ℤ) : ZMod N) = 0 := hN
    simp only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h ⊢
    push_cast
    simp only [hx, mul_zero, add_zero]
    exact congrArg (· * _) h
  · have h := hP.col r
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h0l, h]
    ring

end SlopeTestRemainingChoices

theorem UpperTheory.Kd.L.actcls :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ g₀ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l, Par l N c d (fun r => gm r * g₀) ∧ ∀ (x : ZMod N) (w m n c₀ : ℕ), Odd w → 1 ≤ m → ∀ (σ : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) b → LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) (fun r => gm r * g₀) σ) (X.act l (g₀ : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  intro Ω _ _ _ _ ε X l _ N _ c d gm hP g₀ h₀
  refine ⟨par_mul hP h₀, ?_⟩
  intro x w m n c₀ _ hm σ b hb
  obtain ⟨hbB, hbe⟩ := hb
  have hl : l.Prime := Fact.out
  have hNl : N.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hP.cop).symm
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨h0N, h0l⟩ := Subgroup.mem_inf.mp h₀
  have hdet : ((g₀ 0 0 : ℤ) : ZMod N) * ((g₀ 1 1 : ℤ) : ZMod N) = 1 := by
    have h1 := congrArg (fun z : ℤ => (z : ZMod N)) g₀.2
    simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at h1
    rw [CongruenceSubgroup.Gamma0_mem.mp h0N, mul_zero, sub_zero] at h1
    exact h1
  have hu : IsUnit ((g₀ 1 1 : ℤ) : ZMod N) := ⟨⟨_, _, by rw [mul_comm]; exact hdet, hdet⟩, rfl⟩
  have hdiam : IsDiam N l (((g₀ 1 1 : ℤ) : ZMod N).val) g₀ := by
    refine ⟨h₀, ?_⟩
    rw [ZMod.natCast_zmod_val]
    rfl
  have hdc : (((g₀ 1 1 : ℤ) : ZMod N).val).Coprime N := ZMod.val_coe_unit_coprime hu.unit
  refine ⟨?_, ?_⟩
  · rw [Tower.act_isDiam_eq X hbB hdiam]
    exact GlobalTheory.CyclotomicQExpansion.ThnEx.diam_B X N l w _ hN0 hNl hdc b hbB
  · set A := clsBmu X l n m N x c d (w + 2) gm σ with hAe
    set A' := clsBmu X l n m N x c d (w + 2) (fun r => gm r * g₀) σ with hA'e
    haveI : NeZero (topMu l n m N) :=
      ⟨by unfold topMu; exact mul_ne_zero (pow_ne_zero _ hl.ne_zero) (mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩
    have hdiv : l ^ n ∣ topMu l n m N := by
      unfold topMu
      exact Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_left n m)) _
    have hwk : wkMu X l n m N x c d σ ∈ topL X (topMu l n m N) := by
      unfold wkMu
      exact SetLike.coe_mem _
    have hf : ∀ m1 m2 : SL(2, ℤ), m1 * m2⁻¹ ∈ CongruenceSubgroup.Gamma (topMu l n m N) →
        X.act l (m1 : Matrix (Fin 2) (Fin 2) ℤ) (fun u => u 0 ^ (w + 2 - 2) • clsK X l n (wkMu X l n m N x c d σ)) -
          X.act l (m2 : Matrix (Fin 2) (Fin 2) ℤ) (fun u => u 0 ^ (w + 2 - 2) • clsK X l n (wkMu X l n m N x c d σ)) ∈
            evF X l n :=
      fun m1 m2 hmm => act_congr_sf X l hdiv (w + 2 - 2) hwk hmm
    have hkey : X.act l (g₀ : Matrix (Fin 2) (Fin 2) ℤ) A - A' ∈ evF X l n := by
      simp only [hAe, hA'e, clsBmu]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ (fun r₀ _ => ?_)
      exact sum_congr_conj X l _ (fun γ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) hf (gm r₀) h₀
    clear_value A A'
    have hA : b - (l : ℤ_[l]) ^ c₀ • A ∈ evF X l n := by
      rw [mem_evF]
      exact hbe
    have h1 := act_mem_evF X l n (g₀ : Matrix (Fin 2) (Fin 2) ℤ) hA
    have h2 := Submodule.smul_mem (evF X l n) ((l : ℤ_[l]) ^ c₀) hkey
    have h3 := Submodule.add_mem _ h1 h2
    rw [mem_evF] at h3
    intro u
    convert h3 u using 2
    simp only [map_sub, map_smul, smul_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    abel
end

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.Kd.L.twist :
    ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (w : ℕ), Odd w → ∃ (c₁ : ℕ) (κ : ℚ), κ ≠ 0 ∧ ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → ∀ (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (x : ZMod N) (m n c₀ : ℕ), 1 ≤ m → m ≤ n → ∀ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l, (∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) (bB σ)) → ∀ (y : (ZMod (l ^ m))ˣ) (δ : (ZMod N)ˣ), ∃ g : HahnSeries ℚ Ω, (∀ r, g.coeff r ∈ A) ∧ ∀ s, Stab A s → (∀ a ∈ A, A.valuation (s a - a) < 1) → s (zt ε l m) = zt ε l m → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n (X.diam N l (δ : ZMod N).val (GlobalTheory.KA.push (redM l n m (N * N)) (bTop X l n m N bB) s y)) φ → ∀ tt : ZMod (l ^ n), IsLamG ε l n m s tt → ∀ (β : ℕ) (t : ℤ), (β : ZMod (l ^ m)) = (y : ZMod (l ^ m)) → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] → ∀ i : ℕ, CgA A l n ((l : Ω) ^ c₁ * φ.coeff (i : ℚ)) ((l : Ω) ^ c₁ * ((l : Ω) ^ c₀ * (κ : Ω) * (tt.val : Ω) * (l : Ω) ^ m * toQ (l ^ m) (pieceT N l m m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0) (t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0) (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β) ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i) + (s (g.coeff (i : ℚ)) - g.coeff (i : ℚ))) := by
  intro l _ N _ w hw
  obtain ⟨c₁, κ, hκ, H⟩ := UpperTheory.Kd.L.law l N w hw
  refine ⟨c₁, κ, hκ, ?_⟩
  intro Ω _ _ _ _ ε X c d gm hP hG1 A hA x m n c₀ hm hmn bB hB y δ
  have hl : l.Prime := Fact.out
  have hl0 : l ≠ 0 := hl.ne_zero
  have hcopδ : ((δ : ZMod N).val).Coprime N := ZMod.val_coe_unit_coprime δ
  have hD : IsDiam N l (δ : ZMod N).val (sgD N l (δ : ZMod N).val) :=
    DiamU.isDiam_sgD_of_coprime' hl0 hcopδ
  obtain ⟨hP', hL⟩ := actcls ε X l N c d gm hP _ hD.1
  obtain ⟨g, hgA, hg⟩ := H ε X c d (fun r => gm r * sgD N l (δ : ZMod N).val) hP' A hA x m n c₀ hm hmn
    (fun σ => X.act l ((sgD N l (δ : ZMod N).val : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (bB σ))
    (fun σ hσ => hL x w m n c₀ hw hm σ (bB σ) (hB σ hσ)) y
  refine ⟨g, hgA, ?_⟩
  intro s hs1 hs2 hs3 φ hφ tt htt β t hβy hβ1 hlt i
  have key := hg s hs1 hs2 hs3 φ ?_ tt htt β t (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) ?_ hβy hβ1 hlt i
  · rw [show ((x.val : ℤ) * t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ))
        = (x.val : ℤ) * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) * t by ring,
      show t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) = (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) * t by ring]
    exact key
  · have hNM : NeZero (topM l n m (N * N)) :=
      ⟨by unfold topM; exact mul_ne_zero (pow_ne_zero _ hl0) (mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩
    have hcop : N.Coprime l := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).mpr hP.cop))
    obtain ⟨ψ, hψ1, hψ2⟩ := X.j_hol
    have hpush : GlobalTheory.KA.push (redM l n m (N * N))
        (bTop X l n m N (fun σ => X.act l ((sgD N l (δ : ZMod N).val : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (bB σ))) s y
        = X.diam N l (δ : ZMod N).val (GlobalTheory.KA.push (redM l n m (N * N)) (bTop X l n m N bB) s y) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [GlobalTheory.KA.push, Tower.diam, map_sum]
      refine Finset.sum_congr rfl fun y' _ => ?_
      simp only [bTop]
      exact GlobalTheory.T.galB_act_comm_gamma0CapGamma0Level_shimuraReciprocity ε X ε.injective ⟨ψ, hψ2, hψ1⟩ N l w hP.odd hP.five hcop hw _ hD.1 _ _
        (hB _ (shArg_mem_fixMu _ s y')).1
    rw [hpush]
    exact hφ
  · have h1 := (CongruenceSubgroup.Gamma1_mem N (gm 1)).mp (hG1 1)
    have h2 := CongruenceSubgroup.Gamma0_mem.mp hD.1.1
    have h3 := hD.2
    have hdet := congrArg (fun z : ℤ => (z : ZMod N)) (Matrix.SpecialLinearGroup.det_coe (sgD N l (δ : ZMod N).val))
    simp only [Matrix.det_fin_two] at hdet
    unfold GlobalTheory.KZ.en at h3 ⊢
    push_cast at hdet h3 ⊢
    rw [ZMod.natCast_zmod_val] at h3
    rw [ZMod.natCast_zmod_val, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1.1, h2, mul_zero, add_zero, one_mul]
    rw [h2, mul_zero, sub_zero, h3] at hdet
    exact (Units.eq_inv_of_mul_eq_one_right hdet).symm
