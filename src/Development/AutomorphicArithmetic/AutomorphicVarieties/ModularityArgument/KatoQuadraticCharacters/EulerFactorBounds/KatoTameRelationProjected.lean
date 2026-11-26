module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoNormRelationTwistTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoNormRelationLevelTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoNormRelationTamePrime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.FrobeniusConjugateInertia
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymEx
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.MlTRedCoe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegral

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.BarMul
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

private theorem frac_eq (D D' : ℕ) [NeZero D] (h : D' = D) (a : ℤ) :
    ∃ j : ℤ, (a : ℚ) / (D' : ℚ) = (((a : ZMod D).val : ℕ) : ℚ) / D + j := by
  subst h
  refine ⟨a / (D' : ℤ), ?_⟩
  have h1 : ((((a : ZMod D').val : ℕ) : ℤ)) = a % (D' : ℤ) := ZMod.val_intCast a
  have h2 : (((a : ZMod D').val : ℕ) : ℚ) = ((a % (D' : ℤ) : ℤ) : ℚ) := by
    rw [← h1]
    push_cast
    rfl
  have hD : (D' : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne D'
  have e : a % (D' : ℤ) = a - (D' : ℤ) * (a / (D' : ℤ)) := Int.emod_def a D'
  rw [h2, e]
  push_cast
  field_simp
  ring

private theorem two_ne (l D : ℕ) [Fact l.Prime] (hl : l ≠ 2) (hD : l ∣ D) (a : ℤ) (ha : (a : ZMod l) ≠ 0) :
    (2 : ZMod D) * (a : ZMod D) ≠ 0 := by
  intro h0
  have h1 := congrArg (ZMod.castHom hD (ZMod l)) h0
  simp only [map_mul, map_ofNat, map_intCast, map_zero] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · have h3 : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h3)
  · exact ha h2

private theorem bar_mul' (l L N p : ℕ) (hL : L ≠ 0) (h : Nat.Coprime p (N * l ^ L)) :
    ((bar l L N p : ℤ) : ZMod l) * (p : ZMod l) = 1 := by
  by_cases hM : N * l ^ L = 0
  · have hp : p = 1 := by
      simpa [hM] using h
    subst hp
    have hv : ((1 : ZMod (N * l ^ L))⁻¹).val = 1 := by
      rw [ZMod.inv_one, ZMod.val_one'' (by omega)]
    simp only [bar, Nat.cast_one, hv, Int.cast_one, mul_one]
  · haveI : NeZero (N * l ^ L) := ⟨hM⟩
    have hdvd : l ∣ N * l ^ L := Dvd.dvd.mul_left (dvd_pow_self l hL) N
    have hu : ((p : ZMod (N * l ^ L)) * (p : ZMod (N * l ^ L))⁻¹) = 1 := ZMod.coe_mul_inv_eq_one p h
    have h1 := congrArg (ZMod.castHom hdvd (ZMod l)) hu
    rw [map_mul, map_one, map_natCast] at h1
    have h2 : ((bar l L N p : ℤ) : ZMod l) = ZMod.castHom hdvd (ZMod l) ((p : ZMod (N * l ^ L))⁻¹) := by
      unfold bar
      rw [Int.cast_natCast, ZMod.natCast_val]
      rfl
    rw [h2, mul_comm]
    exact h1

theorem UpperTheory.V.Z.Kato.Nb.sTopT :
    UpperTheory.V.Z.Kato.Nb.STopT := by
  intro Ω _ _ _ ε X l _ N p _ _ x c d w g hH hP hcop hLw hLift n r
  obtain ⟨ws, hws⟩ := hLw
  have api := sApi Ω ε X l
  have inv := sInvApi Ω ε X l N w
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨fun σ _ => (inv 0).2.2.2.2.2.2.1 _, fun σ _ τ _ => (api 0).2.2.2.2.2.2.2.2.1 _ _,
      ⟨∅, fun σ _ τ _ _ => (api 0).2.2.2.2.2.2.2.2.1 _ _⟩⟩
  · have hl2 : l ≠ 2 := hH.odd
    have hlp : l.Prime := Fact.out
    have hL0 : r + n ≠ 0 := by omega
    have hpl : p.Coprime l := Nat.Coprime.coprime_dvd_right ⟨N * c * d, by ring⟩ hcop
    have hpN : p.Coprime N := Nat.Coprime.coprime_dvd_right ⟨l * c * d, by ring⟩ hcop
    have hpc : p.Coprime c := Nat.Coprime.coprime_dvd_right ⟨l * N * d, by ring⟩ hcop
    have hpNL : p.Coprime (N * l ^ (r + n)) := Nat.Coprime.mul_right hpN (Nat.Coprime.pow_right _ hpl)
    have hcN : c.Coprime N := Nat.Coprime.coprime_dvd_right ⟨6 * l, by ring⟩ hH.cc
    have hcl : c.Coprime l := Nat.Coprime.coprime_dvd_right ⟨6 * N, by ring⟩ hH.cc
    have hdN : d.Coprime N := Nat.Coprime.coprime_dvd_right ⟨6 * l, by ring⟩ hH.cd
    have hdl : d.Coprime l := Nat.Coprime.coprime_dvd_right ⟨6 * N, by ring⟩ hH.cd
    have hpd : p.Coprime d := Nat.Coprime.coprime_dvd_right ⟨l * N * c, by ring⟩ hcop
    have hM0 : N * l ^ (r + n) * p ≠ 0 :=
      mul_ne_zero (mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hlp.ne_zero)) (NeZero.ne p)
    haveI : NeZero (N * l ^ (r + n) * p) := ⟨hM0⟩
    have hMeq : lvT l n r N p = N * (N * l ^ (r + n) * p) := by
      unfold lvT
      ring
    haveI : NeZero (lvT l n r N p) := ⟨by rw [hMeq]; exact mul_ne_zero (NeZero.ne N) hM0⟩
    have hLev : Lev l n N (N * l ^ (r + n) * p) (lvT l n r N p) g :=
      ⟨hMeq, ⟨l ^ (r + n) * p, by ring⟩, ⟨N * l ^ r * p, by ring⟩, hn, hH.cop, hH.g0⟩
    have hLv : Lv c d (N * l ^ (r + n) * p) :=
      ⟨Nat.pos_of_ne_zero hM0,
        Nat.Coprime.mul_right (Nat.Coprime.mul_right hcN (Nat.Coprime.pow_right _ hcl)) hpc.symm,
        Nat.Coprime.mul_right (Nat.Coprime.mul_right hdN (Nat.Coprime.pow_right _ hdl)) hpd.symm⟩
    have hdvdl : l ∣ N * l ^ (r + n) * p := Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self l hL0) N) p
    have hbp : ((bar l (r + n) N p : ℤ) : ZMod l) * (p : ZMod l) = 1 := bar_mul' l (r + n) N p hL0 hpNL
    have hlL : ((l : ZMod l)) ^ (r + n) = 0 := by
      rw [ZMod.natCast_self]
      exact zero_pow hL0
    have hN0 : (N : ZMod l) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hlp).mp hH.cop
    have ha0 : (((bar l (r + n) N p * ((N : ℤ) + ((x.val : ℕ) : ℤ) * ((topT l (r + n) N : ℕ) : ℤ) * (l : ℤ) ^ (r + n)) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod l) ≠ 0 := by
      have e : (((bar l (r + n) N p * ((N : ℤ) + ((x.val : ℕ) : ℤ) * ((topT l (r + n) N : ℕ) : ℤ) * (l : ℤ) ^ (r + n)) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod l) = (N : ZMod l) := by
        push_cast
        linear_combination (N : ZMod l) * hbp + (((bar l (r + n) N p : ℤ) : ZMod l) * ((x.val : ℕ) : ZMod l) * ((topT l (r + n) N : ℕ) : ZMod l) * (p : ZMod l) + (N : ZMod l)) * hlL
      rw [e]
      exact hN0
    have hb1 : (((bar l (r + n) N p * (N : ℤ) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod l) ≠ 0 := by
      have e : (((bar l (r + n) N p * (N : ℤ) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod l) = (N : ZMod l) := by
        push_cast
        linear_combination (N : ZMod l) * hbp + (N : ZMod l) * hlL
      rw [e]
      exact hN0
    let x₀ : Row (N * l ^ (r + n) * p) :=
      ![(((bar l (r + n) N p * ((N : ℤ) + ((x.val : ℕ) : ℤ) * ((topT l (r + n) N : ℕ) : ℤ) * (l : ℤ) ^ (r + n)) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod (N * l ^ (r + n) * p)),
        (((0 : ℤ)) : ZMod (N * l ^ (r + n) * p))]
    let y₀ : Row (N * l ^ (r + n) * p) :=
      ![(((bar l (r + n) N p * ((topT l (r + n) N : ℕ) : ℤ) * (l : ℤ) ^ (r + n) * (p : ℤ)) : ℤ) : ZMod (N * l ^ (r + n) * p)),
        (((bar l (r + n) N p * (N : ℤ) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod (N * l ^ (r + n) * p))]
    have hOk : Ok x₀ y₀ := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have h1 := congrFun h 0
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat] at h1
        exact two_ne l _ hl2 hdvdl _ ha0 h1
      · have h1 := congrFun h 1
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat] at h1
        exact two_ne l _ hl2 hdvdl _ hb1 h1
    have hx : ∀ i : Fin 2, ∃ j : ℤ, ixUT l (r + n) N p x i = toQ (N * l ^ (r + n) * p) x₀ i + j := by
      intro i
      fin_cases i
      · exact frac_eq _ _ rfl _
      · exact frac_eq _ _ rfl _
    have hy : ∀ i : Fin 2, ∃ j : ℤ, ixVT l (r + n) N p i = toQ (N * l ^ (r + n) * p) y₀ i + j := by
      intro i
      fin_cases i
      · exact frac_eq _ _ rfl _
      · exact frac_eq _ _ rfl _
    obtain ⟨β, hβ, hcg⟩ := sTopRel Ω ε X l n N (N * l ^ (r + n) * p) (lvT l n r N p) w g hLev hLift c d ws hws hLv
      x₀ y₀ hOk _ _ hx hy
    exact sTopCocG Ω ε X l n N _ _ w g hLev hLift x₀ y₀ hOk (ws n _) (hws.coc n _ hLv) _ β hβ hcg
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.LiftOk
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sLiftOk :
    UpperTheory.V.Z.Kato.Nb.SLiftOk := by
  intro Ω _ _ _ ε X l _ N w _ hl hc hw
  have h : ∃ c, LiftsWith X l N w c :=
    UpperTheory.Kd.K4.liftH ε X l N w hl (Nat.pos_of_ne_zero (NeZero.ne N)) hc hw
  exact Classical.epsilon_spec h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvMemO
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem nle {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] a := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨a, ha⟩ : c.O)).map c.O.val
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem inv_mem_O {l : ℕ} [Fact l.Prime] (c : Coef l) {p : ℕ} (hp : Nat.Coprime l p) :
    ((p : Qbar l))⁻¹ ∈ c.O := by
  have hu : IsUnit (p : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h := congrArg (algebraMap ℤ_[l] (Qbar l)) hv
  rw [map_mul, map_natCast, map_one] at h
  rw [← eq_inv_of_mul_eq_one_right h]
  exact c.O.algebraMap_mem v

theorem UpperTheory.V.Z.Kato.Nb.sEulCg :
    UpperTheory.V.Z.Kato.Nb.SEulCg := by
  intro l hl Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf _ _ p n hp hn hd a δ ha hδ
  obtain ⟨k, hk⟩ := hd
  have hpk : p = l ^ n * k + 1 := by have := hp.pos; omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hcop : Nat.Coprime l p := by
    rw [hpk, pow_succ', mul_assoc]
    simp
  have hq := inv_mem_O cf hcop
  have hp0 : (p : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  refine ⟨?_, ?_⟩
  · unfold eul
    rw [← inv_pow, ← inv_pow]
    exact add_mem (sub_mem (one_mem _) (mul_mem ha (pow_mem hq _))) (mul_mem hδ (pow_mem hq _))
  intro σ hψ he htr hdet
  have hc : (cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) = p := by
    apply Subtype.val_injective
    apply (algebraMap ℚ_[l] (Qbar l)).injective
    have h : eps l σ = algebraMap ℚ_[l] (Qbar l) ((cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) : ℚ_[l]) := rfl
    rw [he] at h
    refine h.symm.trans ?_
    simp
  have hm : ((((cycMod (F := ℚ) (Ω := Ω) l 1 σ : ZMod (l ^ 1))).val : ℕ) : ZMod l) = 1 := by
    have h : ((cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)) =
      PadicInt.toZModPow 1 (cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) := rfl
    rw [h, hc, map_natCast, ZMod.val_natCast, pow_one, ZMod.natCast_mod, hpk]
    simp
  have hth : thK l e ψ σ = ((p : Qbar l) ^ e)⁻¹ := by
    unfold thK
    rw [hm, hψ, he, mul_one]
  unfold rhoK at htr hdet
  rw [hth, inv_inv] at htr hdet
  rw [Matrix.trace_smul, Matrix.trace_fin_two, smul_eq_mul] at htr
  rw [Matrix.det_smul, Fintype.card_fin, ← pow_mul, mul_comm e 2, Matrix.det_fin_two] at hdet
  have hdet' := mul_left_cancel₀ (pow_ne_zero _ hp0) hdet
  have hpc : (p : Qbar l) = (l : Qbar l) ^ (m + 1) * k + 1 := by exact_mod_cast hpk
  have ho : (k : Qbar l) * (a * (p : Qbar l)⁻¹ ^ (e + 1) - δ * (p : Qbar l)⁻¹ ^ 2 * (1 + p)) ∈ cf.O :=
    mul_mem (natCast_mem _ _) (sub_mem (mul_mem ha (pow_mem hq _))
      (mul_mem (mul_mem hδ (pow_mem hq _)) (add_mem (one_mem _) (natCast_mem _ _))))
  have key : eul l e p a δ - 1 * (mat W σ - 1).det =
      (l : Qbar l) ^ (m + 1) * ((k : Qbar l) * (a * (p : Qbar l)⁻¹ ^ (e + 1) - δ * (p : Qbar l)⁻¹ ^ 2 * (1 + p))) := by
    rw [← mul_assoc, ← sub_eq_of_eq_add hpc, Matrix.det_fin_two]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero]
    unfold eul
    rw [← htr, ← hdet']
    simp only [inv_pow]
    field_simp
    ring
  unfold GlobalTheory.Ord2.Cg
  rw [key, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (nle cf ho)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.LiftPush
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem lsq_eq (l p L : ℕ) (h : Nat.Coprime p l) : lsqInv l p L = inv1 p l ^ (2 * L) := by
  have h1 : IsUnit (l : ZMod p) := (ZMod.isUnit_iff_coprime l p).2 h.symm
  have h2 : IsUnit ((l : ZMod p) ^ (2 * L)) := h1.pow _
  unfold lsqInv inv1
  rw [dite_eq_left h1, dite_eq_left h2, inv_pow]
  congr 1
  ext
  simp

private theorem arg_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) [NeZero M]
    (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod M)ˣ) : (repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹) ∈ fixMu Ω M := by
  obtain ⟨-, -, -, -, -, -, -, hM⟩ := sSlD Ω ε X 1 one_pos
  have mul : ∀ a b : Ω ≃ₐ[ℚ] Ω, cycM M (a * b) = cycM M a * cycM M b := fun a b => (hM M a).2.1 b
  have rep : ∀ y : (ZMod M)ˣ, cycM M (repM (Ω := Ω) M y) = y := (hM M s).2.2.1
  let f : (Ω ≃ₐ[ℚ] Ω) →* (ZMod M)ˣ := MonoidHom.mk' (cycM M) mul
  rw [(hM M _).2.2.2.1]
  have e : f ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹)) = 1 := by
    simp only [map_mul, map_inv]
    change (cycM M (repM (Ω := Ω) M y))⁻¹ * cycM M s * cycM M (repM (Ω := Ω) M (y * (cycM M s)⁻¹)) = 1
    rw [rep, rep, mul_comm y, ← mul_assoc, mul_inv_cancel_right, inv_mul_cancel]
  exact e

private theorem lift_push {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (N w n c M : ℕ) [NeZero N] [NeZero M] {T ι : Type} [DecidableEq T] [Fintype ι] (π : (ZMod M)ˣ → T)
    (z : ι → (Ω ≃ₐ[ℚ] Ω) → X.Fn l) (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l)
    (h : ∀ σ ∈ fixMu Ω M, LiftB X l N w n c (∑ i, z i σ) (bB σ)) (s : Ω ≃ₐ[ℚ] Ω) (t : T) :
    LiftB X l N w n c (∑ i, GlobalTheory.KA.push π (shB X l M (z i)) s t) (GlobalTheory.KA.push π (shB X l M bB) s t) := by
  obtain ⟨-, -, -, hSum, -, -, hGal, -⟩ := sApi Ω ε X l n
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have key : ∀ y : (ZMod M)ˣ, LiftB X l N w n c (∑ i, shB X l M (z i) s y) (shB X l M bB s y) := by
    intro y
    have hy := h _ (arg_mem X M s y)
    refine ⟨(sBStab Ω ε X l N w hN _ hy.1).1 _, ?_⟩
    have hc : CgF X l n (bB ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹)))
        ((l : ℤ_[l]) ^ c • ∑ i, z i ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹))) := hy.2
    have hg := hGal (repM M y) _ _ hc
    have e : (l : ℤ_[l]) ^ c • ∑ i, shB X l M (z i) s y = X.galB l (repM M y)
        ((l : ℤ_[l]) ^ c • ∑ i, z i ((repM M y)⁻¹ * s * repM M (y * (cycM M s)⁻¹))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [shB, map_smul, map_sum]
    intro u
    have hu := hg u
    rw [← e] at hu
    exact hu
  have hpush : ∀ Y : (Ω ≃ₐ[ℚ] Ω) → (ZMod M)ˣ → X.Fn l,
      GlobalTheory.KA.push π Y s t = ∑ y ∈ Finset.univ.filter (fun y => π y = t), Y s y := fun Y => rfl
  simp only [hpush]
  rw [Finset.sum_comm]
  refine ⟨Submodule.sum_mem _ (fun y _ => (key y).1), ?_⟩
  have hs := hSum _ (Finset.univ.filter (fun y => π y = t)) (fun y => shB X l M bB s y)
    (fun y => (l : ℤ_[l]) ^ c • ∑ i, shB X l M (z i) s y) (fun y _ => (key y).2)
  rw [← Finset.smul_sum] at hs
  exact hs

theorem UpperTheory.V.Z.Kato.Nb.sRelT :
    UpperTheory.V.Z.Kato.Nb.SRelT := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he p _ hp c₀ Y hY r n
  obtain ⟨bB, hB, b, hb, hC⟩ := hY r n
  obtain ⟨-, -, -, -, hadd, -, -, hgal, -⟩ := hA
  have hw : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  have hB' : ∀ σ ∈ fixMu Ω (lvT l n r N p), LiftB X l N (2 * e - 1) n c₀ (∑ r₀, clsT X l n r N p x c d (2 * e - 1) (gm r₀) σ) (bB σ) := by
    intro σ hσ
    rw [← hw]
    exact hB σ hσ
  refine ⟨fun s y => GlobalTheory.KA.push (rdT l n r N p) (shB X l (lvT l n r N p) bB) s (y.1 * inv1 p l ^ (2 * (r + n)), y.2), b,
    fun s y => lift_push X l N _ n c₀ _ (rdT l n r N p) _ bB hB' s _, hb, fun s y => ?_⟩
  have key : ∀ t, pr (GlobalTheory.KA.push (rdT l n r N p) (shB X l (lvT l n r N p) bB) s t) = YfBT X l pr W e ψ n r N p bB s t := by
    intro t
    have hs := map_sum (AddMonoidHom.mk' pr hadd) (shB X l (lvT l n r N p) bB s)
      (Finset.univ.filter fun y' => rdT l n r N p y' = t)
    refine hs.trans (Finset.sum_congr rfl fun y' _ => ?_)
    exact hgal _ _ (hB' _ (arg_mem X _ s y')).1
  have := hC s y
  rw [lsq_eq l p _ hp, ← key] at this
  exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SRel0
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

theorem UpperTheory.V.Z.Kato.Nb.sRel0 :
    UpperTheory.V.Z.Kato.Nb.SRel0 := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he c₀ Y hY r n
  obtain ⟨bB, hL, b, hb, hC⟩ := hY r n
  obtain ⟨-, -, -, -, hadd, -, -, heq, -⟩ := hA
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h2 : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  rw [h2] at hL
  obtain ⟨-, -, -, -, -, -, -, hcy⟩ := sSlD Ω ε X N hN
  have hfix : ∀ (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (topM l n r (N * N)))ˣ),
      (repM (topM l n r (N * N)) y)⁻¹ * s * repM (topM l n r (N * N)) (y * (cycM (topM l n r (N * N)) s)⁻¹) ∈
        fixMu Ω (topMu l n r N) := by
    intro s y
    have hm : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM (topM l n r (N * N)) (s * t) = cycM (topM l n r (N * N)) s * cycM (topM l n r (N * N)) t :=
      fun s t => (hcy (topM l n r (N * N)) s).2.1 t
    have hr := (hcy (topM l n r (N * N)) s).2.2.1
    refine (hcy (topM l n r (N * N)) _).2.2.2.1.2 ?_
    have h1 : y * cycM (topM l n r (N * N)) ((repM (topM l n r (N * N)) y)⁻¹ * s) = cycM (topM l n r (N * N)) s := by
      conv_lhs => rw [← hr y]
      rw [← hm, hr, mul_inv_cancel_left]
    rw [hm, hr, eq_inv_mul_of_mul_eq h1]
    simp [mul_comm, mul_left_comm]
  have hB := sBStab Ω ε X l N (2 * e - 1) hN
  obtain ⟨-, -, -, hsum, -, -, hgal, -⟩ := sApi Ω ε X l n
  let P : X.Fn l →+ (Fin 2 → Qbar l) := AddMonoidHom.mk' pr hadd
  refine ⟨GlobalTheory.KA.push (redM l n r (N * N)) (shB X l (topM l n r (N * N)) bB), b, fun s y => ⟨?_, ?_⟩, hb, fun s y => ?_⟩
  · exact Submodule.sum_mem _ fun y' _ => (hB _ (hL _ (hfix s y')).1).1 _
  · have h1 := hsum _ (Finset.univ.filter fun y' => redM l n r (N * N) y' = y) _ _
      (fun y' _ => hgal (repM (topM l n r (N * N)) y') _ (((l : ℤ_[l]) ^ c₀) • _) (hL _ (hfix s y')).2)
    have h3 : (∑ r₀, Y0 X l n r N x c d (2 * e - 1) (gm r₀) s y) =
        ∑ y' ∈ Finset.univ.filter (fun y' => redM l n r (N * N) y' = y),
          shB X l (topM l n r (N * N)) (clsBmu X l n r N x c d (2 * e + 1) gm) s y' := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Y0, GlobalTheory.KA.push, shB, clsBmu_eq, h2, map_sum]
      exact Finset.sum_comm
    simp only [map_smul, ← Finset.smul_sum] at h1
    beta_reduce
    rw [h3]
    exact h1
  · have h4 : pr (GlobalTheory.KA.push (redM l n r (N * N)) (shB X l (topM l n r (N * N)) bB) s y) = YfB X l pr W e ψ n r N bB s y := by
      refine (map_sum P _ _).trans (Finset.sum_congr rfl fun y' _ => ?_)
      exact heq _ _ (hL _ (hfix s y')).1
    rw [h4]
    exact hC s y
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.PushPsi
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb.PushforwardPsi

private theorem exF {Γ A C : Type} [Group Γ] [CommGroup A] [CommGroup C] (c : Γ →* A) (ψ : Γ →* C)
    (h : ∀ s, c s = 1 → ψ s = 1) : ∃ f : A → C, ∀ a s, f (a * (c s)⁻¹) = f a * ψ s := by
  have h1 : ∀ a : A, ∃ s, c s = a⁻¹ * (QuotientGroup.mk a : A ⧸ c.range).out := fun a =>
    QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk a : A ⧸ c.range)).symm
  choose σ hσ using h1
  refine ⟨fun a => ψ (σ a), fun a s => ?_⟩
  have e : (QuotientGroup.mk (a * (c s)⁻¹) : A ⧸ c.range) = QuotientGroup.mk a :=
    QuotientGroup.eq.2 ⟨s, by simp⟩
  have h2 := h ((σ (a * (c s)⁻¹))⁻¹ * (σ a * s)) (by
    rw [map_mul, map_mul, map_inv, hσ, hσ, e, inv_mul_eq_one, mul_inv, inv_inv, mul_right_comm])
  rw [map_mul, map_inv, inv_mul_eq_one, map_mul] at h2
  exact h2

private theorem exC (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] :
    ∃ c : (Ω ≃ₐ[ℚ] Ω) →* (ZMod M)ˣ, ∀ s, cycM M s = c s ∧ ∀ z : Ω, z ^ M = 1 → s z = z ^ (c s : ZMod M).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  refine ⟨hζ.autToPow ℚ, fun s => ?_⟩
  have hs : ∀ z : Ω, z ^ M = 1 → s z = z ^ (hζ.autToPow ℚ s : ZMod M).val := fun w hw => by
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hw
    rw [map_pow, ← hζ.autToPow_spec ℚ s, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨?_, hs⟩
  have hM := cycM_spec M s ⟨_, hs⟩
  apply Units.ext
  apply ZMod.val_injective
  exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ((hM ζ hζ.pow_eq_one).symm.trans (hs ζ hζ.pow_eq_one))

private theorem push_prod {Γ A B B' V : Type} [Group Γ] [AddCommMonoid V] [Fintype A] [Fintype B'] [DecidableEq B]
    {i1 : Fintype (A × B')} {i2 : DecidableEq (A × B)} (g : B' → B) (Z : Γ → A × B' → V) (s : Γ) (a : A) (y : B) :
    @push Γ (A × B) (A × B') i1 i2 V _ (Prod.map id g) Z s (a, y) = ∑ y', if g y' = y then Z s (a, y') else 0 := by
  obtain rfl : i1 = instFintypeProd A B' := Subsingleton.elim _ _
  unfold push
  rw [Finset.sum_filter, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun y' _ => ?_
  by_cases h : g y' = y <;> simp [h]

end UpperTheory.V.Z.Kato.Nb.PushforwardPsi

open UpperTheory.V.Z.Kato.Nb.PushforwardPsi in
theorem UpperTheory.V.Z.Kato.Nb.sPushPsi :
    UpperTheory.V.Z.Kato.Nb.SPushPsi := by
  intro l _ Ω _ _ _ cf ρ p n _ ψw hψ Y hc hp hcont hO
  obtain ⟨c, hcs⟩ := exC Ω p
  obtain ⟨f, hf⟩ := exF c ψw fun s hs => hψ s fun z hz => by
    rw [(hcs s).2 z hz, hs, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hz, pow_one]
  refine ⟨fun r s x => ∑ t, if f t = x.1 then Y r s (t, x.2) else 0, fun r s s' x => ?_, fun r x i => ?_,
    fun r s x i => ?_, fun r s => ?_, fun r s y => ?_⟩
  · have e : ∑ t, (if f t = (x * (ψw.prod (cycMod ℚ Ω l r)⁻¹) s).1 then
        Y r s' (t, (x * (ψw.prod (cycMod ℚ Ω l r)⁻¹) s).2) else 0) =
        ∑ t, if f t = x.1 then Y r s' ((t, x.2) * cycT l r p s) else 0 := by
      symm
      refine Fintype.sum_equiv (Equiv.mulRight (c s)⁻¹) _ _ fun t => ?_
      simp [hf, cycT, (hcs s).1]
    beta_reduce
    rw [e, Matrix.mulVec_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs
    · exact hc r s s' _
    · simp
  · simp only [Finset.sum_apply]
    refine continuous_finsetSum _ fun t _ => ?_
    split_ifs
    · exact hcont r _ i
    · exact continuous_const
  · simp only [Finset.sum_apply]
    refine sum_mem fun t _ => ?_
    split_ifs
    · exact hO r s _ i
    · exact zero_mem _
  · funext ⟨a, y⟩
    rw [push_prod]
    have e : ∀ t, Y r s (t, y) = ∑ y', if redL l r y' = y then Y (r + 1) s (t, y') else 0 := fun t => by
      rw [hp r, push_prod]
    simp only [e]
    have e2 : ∀ (P : Prop) [Decidable P] {ι : Type} [Fintype ι] (v : ι → Fin 2 → Qbar l),
        (if P then ∑ j, v j else 0) = ∑ j, if P then v j else 0 := fun P _ _ _ v => by split_ifs <;> simp
    simp only [e2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun t _ => ?_
    change (if f t = a then if redL l r y' = y then _ else 0 else 0) = if redL l r y' = y then if f t = a then _ else 0 else 0
    split_ifs <;> rfl
  · rw [Finset.sum_comm]
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SN2rho
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb.SquareNormRepresentation

private def Sm {l : ℕ} [Fact l.Prime] (n : ℕ) (x : Fin 2 → Qbar l) : Prop := ∀ i, ‖x i‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖

private theorem Sm.add {l : ℕ} [Fact l.Prime] {n : ℕ} {x y : Fin 2 → Qbar l} (hx : Sm n x) (hy : Sm n y) : Sm n (x + y) := by
  unfold Sm at *
  intro i
  rw [Pi.add_apply]
  exact (PadicAlgCl.isNonarchimedean l (x i) (y i)).trans (max_le (hx i) (hy i))

private theorem Sm.smul {l : ℕ} [Fact l.Prime] {n : ℕ} {x : Fin 2 → Qbar l} {k : Qbar l} (hk : ‖k‖ ≤ 1) (hx : Sm n x) :
    Sm n (k • x) := fun i => by
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hk).trans (hx i)

private theorem Sm.sub {l : ℕ} [Fact l.Prime] {n : ℕ} {x y : Fin 2 → Qbar l} (hx : Sm n x) (hy : Sm n y) : Sm n (x - y) := by
  unfold Sm at *
  intro i
  rw [Pi.sub_apply, sub_eq_add_neg]
  refine (PadicAlgCl.isNonarchimedean l _ _).trans (max_le (hx i) ?_)
  rw [norm_neg]
  exact hy i

private theorem Sm.sum {l : ℕ} [Fact l.Prime] {n : ℕ} {T : Type} (S : Finset T) (x : T → Fin 2 → Qbar l) (h : ∀ t, Sm n (x t)) :
    Sm n (∑ t ∈ S, x t) := by
  induction S using Finset.induction_on with
  | empty => intro i; simp
  | insert a S ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

private theorem nle {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] c.O).FG)
  have hB : ∀ x : c.O, ‖(x : PadicAlgCl l)‖ ≤ ∑ g ∈ s, ‖(g : PadicAlgCl l)‖ := by
    intro x
    have hx : x ∈ Submodule.span ℤ_[l] (s : Set c.O) := by
      rw [hs]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem g hg =>
      exact Finset.single_le_sum (f := fun g : c.O => ‖(g : PadicAlgCl l)‖)
        (fun _ _ => norm_nonneg _) hg
    | zero =>
      simp only [ZeroMemClass.coe_zero, norm_zero]
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    | add x y _ _ hx hy =>
      rw [AddMemClass.coe_add]
      exact (PadicAlgCl.isNonarchimedean l _ _).trans (max_le hx hy)
    | smul r x _ hx =>
      rw [SetLike.val_smul, Algebra.smul_def, norm_mul]
      have hr : ‖algebraMap ℤ_[l] (PadicAlgCl l) r‖ ≤ 1 := by
        rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
        exact (PadicAlgCl.norm_extends l _).trans_le (PadicInt.norm_le_one r)
      exact (mul_le_of_le_one_left (norm_nonneg _) hr).trans hx
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (∑ g ∈ s, ‖(g : PadicAlgCl l)‖) hlt
  have hle : ‖a ^ n‖ ≤ ∑ g ∈ s, ‖(g : PadicAlgCl l)‖ := hB ⟨a ^ n, c.O.pow_mem ha n⟩
  rw [norm_pow] at hle
  linarith

end UpperTheory.V.Z.Kato.Nb.SquareNormRepresentation

open UpperTheory.V.Z.Kato.Nb.SquareNormRepresentation in
theorem UpperTheory.V.Z.Kato.Nb.sN2rho :
    UpperTheory.V.Z.Kato.Nb.SN2rho := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hAdm he hmat
  obtain ⟨cp, hcp⟩ := UpperTheory.Kd.K4.pur ε X l N (2 * e - 1)
  refine ⟨cp + cL X l N (2 * e - 1), ?_⟩
  intro p _ hp hcop a δ ha hδ hab c₀ c₁ r n Y Y' z z' hR hR' hC
  obtain ⟨β, b1, hβ, hb1, hY⟩ := hR
  obtain ⟨β', b2, hβ', hb2, hY'⟩ := hR'
  obtain ⟨B0, hB0, hC⟩ := hC
  choose L hL using fun y => (hB0 y).2.2
  obtain ⟨_, _, _, _, hpr_add, hpr_smul, hprO, hprG, _⟩ := hAdm
  obtain ⟨hEqv, hAS, hSm, hSum, _, hAct, hGal, _⟩ := UpperTheory.V.Z.Kato.Nb.sApi Ω ε X l n
  have hStab := UpperTheory.V.Z.Kato.Nb.sBStab Ω ε X l N (2 * e - 1) (NeZero.pos N)
  set w := 2 * e - 1 with hw
  set cl := cL X l N w with hcl
  set i := inv1 (l ^ r) p with hi
  let P : X.Fn l →+ (Fin 2 → Qbar l) := AddMonoidHom.mk' pr hpr_add
  have hPs : ∀ u v, pr (u - v) = pr u - pr v := fun u v => map_sub P u v
  have hPsum : ∀ {T : Type} (S : Finset T) (f : T → X.Fn l), pr (∑ t ∈ S, f t) = ∑ t ∈ S, pr (f t) :=
    fun S f => map_sum P f S
  have hPn : ∀ (k : ℕ) (v : X.Fn l), pr ((k : ℤ_[l]) • v) = (k : Qbar l) • pr v := by
    intro k v
    rw [hpr_smul]
    simp
  have hPl : ∀ (j : ℕ) (v : X.Fn l), pr ((l : ℤ_[l]) ^ j • v) = (l : Qbar l) ^ j • pr v := by
    intro j v
    rw [← Nat.cast_pow, hPn, Nat.cast_pow]
  have hPp : ∀ (j : ℕ) (v : X.Fn l), pr ((p : ℤ_[l]) ^ j • v) = (p : Qbar l) ^ j • pr v := by
    intro j v
    rw [← Nat.cast_pow, hPn, Nat.cast_pow]
  have hnO : ∀ k : ℕ, (k : Qbar l) ∈ cf.O := fun k => natCast_mem cf.O k
  have hTB : ∀ v ∈ X.B N l w, X.heckeT N l p v ∈ X.B N l w := fun v hv => (hStab v hv).2.2 p hp hcop
  have hDB : ∀ v ∈ X.B N l w, X.diam N l p v ∈ X.B N l w := by
    intro v hv
    exact (hStab v hv).2.1 _ (GlobalTheory.KZ.Betti.isDiam_sgD (NeZero.ne N) (Fact.out : l.Prime).ne_zero
      (Nat.Coprime.coprime_mul_left_right hcop)).1
  have hTc : ∀ u v, CgF X l n u v → CgF X l n (X.heckeT N l p u) (X.heckeT N l p v) := by
    intro u v h
    simp only [GlobalTheory.KZ.Tower.heckeT, LinearMap.add_apply, LinearMap.sum_apply]
    exact (hAS _ _ _ _ (hSum _ _ _ _ fun j _ => hAct _ _ _ h) (hAct _ _ _ h)).1
  have hDc : ∀ u v, CgF X l n u v → CgF X l n (X.diam N l p u) (X.diam N l p v) := by
    intro u v h
    exact hAct _ _ _ h
  have hCS : ∀ {u v : Fin 2 → Qbar l}, Cv n u v → Sm n (u - v) := fun h j => h j
  have hSC : ∀ {u v : Fin 2 → Qbar l}, Sm n (u - v) → Cv n u v := fun h j => h j
  let b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l := fun y =>
    ((l : Qbar l) ^ (cp + cl) * p) • ∑ t, b2 (t, y)
      - (l : Qbar l) ^ (cp + cl + c₁) • ((p : Qbar l) • b1 y - a • b1 (y * i)
        + ((p : Qbar l) ^ w * δ) • b1 (y * i ^ 2))
      + (l : Qbar l) ^ (cp + (c₀ + c₁)) • pr (L y)
  refine ⟨b, ?_, ?_⟩
  · intro y j
    simp only [b, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    refine add_mem (sub_mem (mul_mem (mul_mem (pow_mem (hnO l) _) (hnO p))
      (sum_mem fun t _ => hb2 _ _)) (mul_mem (pow_mem (hnO l) _) (add_mem (sub_mem
      (mul_mem (hnO p) (hb1 _ _)) (mul_mem ha (hb1 _ _))) (mul_mem (mul_mem (pow_mem (hnO p) _) hδ)
      (hb1 _ _))))) (mul_mem (pow_mem (hnO l) _) (hprO _ (hL y).1 j))
  intro s y
  have hb : ∀ y', β s y' ∈ X.B N l w := fun y' => (hβ s y').1
  have hβc : ∀ y', CgF X l n (β s y') ((l : ℤ_[l]) ^ c₀ • z s y') := fun y' => (hβ s y').2
  have hβ'c : ∀ t, CgF X l n (β' s (t, y)) ((l : ℤ_[l]) ^ (c₀ + c₁) • z' s (t, y)) := fun t => (hβ' s (t, y)).2
  have hLc : ∀ y', CgF X l n (L y') ((l : ℤ_[l]) ^ cl • B0 y') := fun y' => (hL y').2
  have hadd : ∀ {u v u' v' : X.Fn l}, CgF X l n u v → CgF X l n u' v' → CgF X l n (u + u') (v + v') :=
    fun h h' => (hAS _ _ _ _ h h').1
  have hsub : ∀ {u v u' v' : X.Fn l}, CgF X l n u v → CgF X l n u' v' → CgF X l n (u - u') (v - v') :=
    fun h h' => (hAS _ _ _ _ h h').2
  have hEB : (l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y) ∈ X.B N l w := by
    refine sub_mem (Submodule.smul_mem _ _ (sub_mem (Submodule.smul_mem _ _
      (sum_mem fun t _ => (hβ' s (t, y)).1)) (Submodule.smul_mem _ _ (add_mem (sub_mem
      (Submodule.smul_mem _ _ (hb y)) (hTB _ (hb _))) (Submodule.smul_mem _ _ (hDB _ (hb _)))))))
      (Submodule.smul_mem _ _ (sub_mem ((hStab _ (hL _).1).1 s) (hL y).1))
  have hE1 : CgF X l n ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y)) ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, (l : ℤ_[l]) ^ (c₀ + c₁) • z' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • (l : ℤ_[l]) ^ c₀ • z s y - X.heckeT N l p ((l : ℤ_[l]) ^ c₀ • z s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p ((l : ℤ_[l]) ^ c₀ • z s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s ((l : ℤ_[l]) ^ cl • B0 (y * (cycMod ℚ Ω l r s)⁻¹)) - (l : ℤ_[l]) ^ cl • B0 y)) :=
    hsub (hSm _ _ _ (hsub (hSm _ _ _ (hSum _ _ _ _ fun t _ => hβ'c t)) (hSm _ _ _ (hadd (hsub
      (hSm _ _ _ (hβc y)) (hTc _ _ (hβc _))) (hSm _ _ _ (hDc _ _ (hβc _)))))))
      (hSm _ _ _ (hsub (hGal _ _ _ (hLc _)) (hLc y)))
  have hCsy := hC s y
  beta_reduce at hCsy
  have hzero : ∀ {u v : X.Fn l}, CgF X l n u v → CgF X l n (u - v) 0 := by
    intro u v h
    have h' := hsub h (hEqv.refl v)
    rwa [sub_self] at h'
  have h1 := hzero hCsy
  have h2 := hSm ((l : ℤ_[l]) ^ (cl + (c₀ + c₁))) _ _ h1
  rw [smul_zero] at h2
  have hEz : CgF X l n ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y)) 0 := by
    refine hEqv.trans hE1 ?_
    convert h2 using 2
    simp only [map_smul, ← Finset.smul_sum]
    module
  obtain ⟨E', hE'B, hEE'⟩ := hcp n _ hEB hEz
  have hsmall : Sm n (pr ((l : ℤ_[l]) ^ cp • ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y)))) := by
    rw [hEE', hPl]
    intro j
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (SquareNormRepresentation.nle cf (hprO _ hE'B j))
  have hprE : pr ((l : ℤ_[l]) ^ cp • ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y))) = (l : Qbar l) ^ cp • ((l : Qbar l) ^ cl • ((p : Qbar l) • ∑ t, pr (β' s (t, y)) - (l : Qbar l) ^ c₁ • ((p : Qbar l) • pr (β s y) - a • pr (β s (y * i)) + (p : Qbar l) ^ w • δ • pr (β s (y * i ^ 2)))) - (l : Qbar l) ^ (c₀ + c₁) • (rhoK W e ψ s *ᵥ pr (L (y * (cycMod ℚ Ω l r s)⁻¹)) - pr (L y))) := by
    simp only [hPl, hPs, hpr_add, hPsum, hPn, hPp]
    rw [(hab _ (hb _)).1, (hab _ (hb _)).2, hprG s _ (hL _).1]
  have hk : ∀ {k : Qbar l}, k ∈ cf.O → ‖k‖ ≤ 1 := fun hk => SquareNormRepresentation.nle cf hk
  have hbig : Sm n (((l : Qbar l) ^ (cp + cl) * p) • ∑ t, (Y' s (t, y) - (pr (β' s (t, y)) + (rhoK W e ψ s *ᵥ b2 ((t, y) * kT l r p s) - b2 (t, y)))) - (l : Qbar l) ^ (cp + cl + c₁) • ((p : Qbar l) • (Y s (y) - (pr (β s (y)) + (rhoK W e ψ s *ᵥ b1 ((y) * (cycMod ℚ Ω l r s)⁻¹) - b1 (y)))) - a • (Y s (y * i) - (pr (β s (y * i)) + (rhoK W e ψ s *ᵥ b1 ((y * i) * (cycMod ℚ Ω l r s)⁻¹) - b1 (y * i)))) + ((p : Qbar l) ^ w * δ) • (Y s (y * i ^ 2) - (pr (β s (y * i ^ 2)) + (rhoK W e ψ s *ᵥ b1 ((y * i ^ 2) * (cycMod ℚ Ω l r s)⁻¹) - b1 (y * i ^ 2))))) + pr ((l : ℤ_[l]) ^ cp • ((l : ℤ_[l]) ^ cl • ((p : ℤ_[l]) • ∑ t, β' s (t, y) - (l : ℤ_[l]) ^ c₁ • ((p : ℤ_[l]) • β s y - X.heckeT N l p (β s (y * i)) + (p : ℤ_[l]) ^ w • X.diam N l p (β s (y * i ^ 2)))) - (l : ℤ_[l]) ^ (c₀ + c₁) • (X.galB l s (L (y * (cycMod ℚ Ω l r s)⁻¹)) - L y)))) :=
    Sm.add (Sm.sub (Sm.smul (hk (mul_mem (pow_mem (hnO l) _) (hnO p)))
      (Sm.sum _ _ fun t => hCS (hY' s (t, y)))) (Sm.smul (hk (pow_mem (hnO l) _))
      (Sm.add (Sm.sub (Sm.smul (hk (hnO p)) (hCS (hY s y))) (Sm.smul (hk ha) (hCS (hY s _))))
      (Sm.smul (hk (mul_mem (pow_mem (hnO p) _) hδ)) (hCS (hY s _)))))) hsmall
  apply hSC
  convert hbig using 1
  rw [hprE]
  simp only [b]
  have hre : ∑ t, rhoK W e ψ s *ᵥ b2 ((t, y) * kT l r p s)
      = rhoK W e ψ s *ᵥ ∑ t, b2 (t, y * (cycMod ℚ Ω l r s)⁻¹) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Matrix.mulVecLin_apply, map_sum]
    exact Fintype.sum_equiv (Equiv.mulRight (cycM p s)⁻¹) _ _ (fun t => rfl)
  rw [show y * i * (cycMod ℚ Ω l r s)⁻¹ = y * (cycMod ℚ Ω l r s)⁻¹ * i from mul_right_comm _ _ _,
    show y * i ^ 2 * (cycMod ℚ Ω l r s)⁻¹ = y * (cycMod ℚ Ω l r s)⁻¹ * i ^ 2 from mul_right_comm _ _ _]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hre, Matrix.mulVec_add, Matrix.mulVec_sub,
    Matrix.mulVec_smul]
  module
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem nsum {l : ℕ} [Fact l.Prime] {ι : Type} (S : Finset ι) (f : ι → Qbar l) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i ∈ S, ‖f i‖ ≤ C) : ‖∑ i ∈ S, f i‖ ≤ C :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC h

private theorem cv_wsum {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] (n : ℕ) (cw : ι → Qbar l) (hc : ∀ x, ‖cw x‖ ≤ 1)
    (a b : ι → Fin 2 → Qbar l) (h : ∀ x, Cv n (a x) (b x)) : Cv n (∑ x, cw x • a x) (∑ x, cw x • b x) := by
  intro i
  unfold Cg
  rw [Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib]
  refine nsum _ _ _ (norm_nonneg _) fun x _ => ?_
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_sub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hc x)).trans (h x i)

private theorem coh_sum {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (N w n : ℕ) (hN : 0 < N) (A : Type) [CommGroup A] (κ : (Ω ≃ₐ[ℚ] Ω) → A) {ι : Type} (S : Finset ι)
    (z z' : ι → (Ω ≃ₐ[ℚ] Ω) → A → X.Fn l) (h : ∀ i, CohB X l N w n κ (z i) (z' i)) :
    CohB X l N w n κ (∑ i ∈ S, z i) (∑ i ∈ S, z' i) := by
  obtain ⟨h1, -, h3, -⟩ := sCohApi Ω ε X l N w n hN A κ
  induction S using Finset.induction_on with
  | empty => simpa using h1.refl _
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (h3 _ _ _ _ (h i) ih).1

theorem UpperTheory.V.Z.Kato.Nb.kato_tame_relation_projected :
    UpperTheory.V.Z.Kato.Nb.KatoTameRelationProjected := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ cw c d gm ψ cf S hNf hmat hgm hlN hl2 he hcw hj hadm c₀ Y hY
  obtain ⟨hadm3, hcwO⟩ := hadm
  obtain ⟨x₀, hx₀⟩ := hcw
  have hA0 := hadm3 x₀ hx₀
  have hlp : l.Prime := Fact.out
  obtain ⟨c₁, hc₁⟩ := mlTOf symEx sApi sInvApi sBStab sSlD sCohApi sCycZ sTopT kato_normRelation_twistTower kato_normRelation_levelTower l Ω ε X N e hlN hl2 he
  have hm := fun x : {x // cw x ≠ 0} => sN2rho l Ω ι e gN A W ε X pr N x.1 c d gm ψ cf (hadm3 x.1 x.2) he hmat
  choose m hm using hm
  have hInt := sInteg l Ω ι e gN A W ε X pr N x₀ c d gm ψ cf hA0 he hmat
  obtain ⟨Yx, hYx, hYsum⟩ := hY
  obtain ⟨S', hSS', hS'⟩ := sEuler l Ω ι e gN A W ε X pr N x₀ c d gm ψ cf hA0 he hlN S hNf hmat
  refine ⟨Finset.univ.sup m + c₁, S', fun w hw => hNf.unr w (fun h => hw (hSS' h)), ?_⟩
  intro n hn w hw hdiv ψw hK hsurj
  obtain ⟨hpP, hpcop, a, δ, ha, hδ, hhec, hfrob⟩ := hS' w hw
  haveI : NeZero (normV w) := ⟨hpP.ne_zero⟩
  have hpl : (normV w).Coprime l := Nat.Coprime.coprime_dvd_right ⟨N * c * d, by ring⟩ hpcop
  have hplN : (normV w).Coprime (l * N) := Nat.Coprime.coprime_dvd_right ⟨c * d, by ring⟩ hpcop
  have hY' := fun x : {x // cw x ≠ 0} => hc₁ (c₀ + c₁) (by omega) ι gN A W pr x.1 c d gm ψ cf (hadm3 x.1 x.2)
    (normV w) hpP hpcop
  choose Y' hY'Z hY'coc hY'push hY'cont hY'O using hY'
  have hEC := sEulCg l Ω ι e gN A W ε X pr N x₀ c d gm ψ cf hA0 he (normV w) n hpP hn hdiv a δ ha hδ
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨hc1, hd1, hcc, hdc, -, -, -, -, -, -, hgN, -⟩ := hA0
  have hLaws : ∃ ws, Laws X l c d ws :=
    symEx Ω ε X l c d hlp hc1 hd1 (Nat.Coprime.coprime_dvd_right ⟨l * N, by ring⟩ hcc)
      (Nat.Coprime.coprime_dvd_right ⟨l * N, by ring⟩ hdc)
  have hodd : Odd (2 * e - 1) := ⟨e - 1, by omega⟩
  have hLW := sLiftOk Ω ε X l N (2 * e - 1) hl2 hlN hodd
  have hHyp : ∀ r₀, Hyp l N c d (gm r₀) := fun r₀ => ⟨hl2, hlN, hc1, hd1, hcc, hdc, hgN r₀⟩
  have hkey := fun (x : {x // cw x ≠ 0}) (r : ℕ) =>
    hm x (normV w) hpP hplN a δ ha hδ hhec c₀ c₁ r r (Yx x.1 r) (Y' x r) _ _
      (sRel0 l Ω ι e gN A W ε X pr N x.1 c d gm ψ cf (hadm3 x.1 x.2) he c₀ (Yx x.1) (hYx x.1) r r)
      (sRelT l Ω ι e gN A W ε X pr N x.1 c d gm ψ cf (hadm3 x.1 x.2) he (normV w) hpl (c₀ + c₁) (Y' x) (hY'Z x) r r)
      (by
        clear hc₁ hm hY'Z hY'coc hY'push hY'cont hY'O hYx hYsum hS' hInt hEC hadm3 hmat hNf hgm hj hfrob hhec
        have h := coh_sum X l N (2 * e - 1) r hN0 _ (fun s => ((cycMod ℚ Ω l r) s)⁻¹) Finset.univ _ _
          (fun r₀ => kato_norm_relation_tame_prime Ω ε X l N (normV w) x.1 c d (2 * e - 1) (gm r₀) (hHyp r₀) hpP hpcop hLaws hLW r r)
        convert h using 1
        all_goals try rfl
        all_goals funext s y
        all_goals simp [Finset.sum_apply, Finset.smul_sum, map_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        all_goals exact Finset.sum_comm)
  choose bN hbN hCvN using hkey
  have hO1 : ∀ z ∈ cf.O, ‖z‖ ≤ 1 := fun z hz => GlobalTheory.CoefCoord.norm_le_one cf ⟨z, hz⟩
  have hlO : ((l : ℕ) : Qbar l) ∈ cf.O := natCast_mem cf.O l
  have hldvd : l ∣ normV w - 1 := dvd_trans (dvd_pow_self l (by omega : n ≠ 0)) hdiv
  have hsp := fun (x : {x // cw x ≠ 0}) (r : ℕ) =>
    sSpec l Ω ι e gN A W ε X pr N x.1 c d gm ψ cf (hadm3 x.1 x.2) he hmat (normV w) r hpP hldvd a δ
      (((l : ℕ) : Qbar l) ^ (m x + c₁)) (hO1 a ha) (hO1 δ hδ) (hO1 _ (pow_mem hlO _)) (Yx x.1 r)
      (fun s y => ((l : ℕ) : Qbar l) ^ (m x) • ∑ t, Y' x r s (t, y)) (bN x r)
      ((sInteg l Ω ι e gN A W ε X pr N x.1 c d gm ψ cf (hadm3 x.1 x.2) he hmat).2.2.2.2.2.2 c₀ (Yx x.1) (hYx x.1) r)
      (hbN x r) (fun s y => by
        have h := hCvN x r s y
        rw [mul_comm, ← smul_smul] at h
        exact h)
  choose b' hb'O hb'Cv using hsp
  set M := Finset.univ.sup m with hM
  have hmM : ∀ x, m x ≤ M := fun x => Finset.le_sup (Finset.mem_univ x)
  obtain ⟨Yt, hYt⟩ : ∃ Yt : (r : ℕ) → (Ω ≃ₐ[ℚ] Ω) → (ZMod (normV w))ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
      ∀ r s y, Yt r s y = ∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ M) • Y' x r s y :=
    ⟨fun r s y => _, fun r s y => rfl⟩
  have hcoc : ∀ r s s' y, Yt r (s * s') y = Yt r s y + rhoK W e ψ s *ᵥ Yt r s' (y * cycT l r (normV w) s) := by
    intro r s s' y
    simp only [hYt, hY'coc, smul_add, Finset.sum_add_distrib, Matrix.mulVec_sum, Matrix.mulVec_smul]
  have hpush : ∀ r, Yt r = push (Prod.map id (redL l r)) (Yt (r + 1)) := by
    intro r
    funext s y
    simp only [push, hYt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hY'push x r]
    simp only [push, Finset.smul_sum]
  have hcont : ∀ r y i, Continuous fun s => Yt r s y i := by
    intro r y i
    simp only [hYt, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact continuous_finsetSum _ fun x _ => continuous_const.mul (hY'cont x r y i)
  have hmem : ∀ r s u i, Yt r s u i ∈ cf.O := by
    intro r s u i
    rw [hYt, Finset.sum_apply]
    refine Subalgebra.sum_mem _ fun x _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hcwO x.1) (pow_mem hlO _)) (hY'O x r s u i)
  obtain ⟨Yw, hYw1, hYw2, hYw3, hYw4, hYw5⟩ :=
    sPushPsi l Ω cf (rhoK W e ψ) (normV w) n ψw hK Yt hcoc hpush hcont hmem
  have hsub : ∀ f : ZMod N → (Fin 2 → Qbar l), ∑ x, cw x • f x = ∑ x : {x // cw x ≠ 0}, cw x.1 • f x.1 := by
    intro f
    rw [← Finset.sum_filter_of_ne (p := fun x => cw x ≠ 0) (fun x _ h hc => h (by simp [hc]))]
    exact Finset.sum_subtype _ (fun x => by simp) _
  refine ⟨Yw, eul l e (normV w) a δ, 1, fun r => ∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x)) • b' x r,
    hYw1, hYw2, hYw3, hYw4, hEC.1, by simp, ?_, ?_, ?_⟩
  · intro r i
    beta_reduce
    rw [Finset.sum_apply]
    refine Subalgebra.sum_mem _ fun x _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hcwO x.1) (pow_mem hlO _)) (hb'O x r i)
  · intro r s i
    have hcv := cv_wsum r (fun x => cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x))
      (fun x => by
        rw [norm_mul, norm_pow]
        exact mul_le_one₀ (hO1 _ (hcwO x.1)) (by positivity) (pow_le_one₀ (norm_nonneg _) (hO1 _ hlO)))
      _ _ (fun x => hb'Cv x r s)
    have hL : ∀ η : (ZMod (l ^ r))ˣ → Qbar l, (∑ a, spec η (fun s x => Yw r s (a, x)) s) =
        ∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x)) •
          spec η (fun s y => ((l : ℕ) : Qbar l) ^ (m x) • ∑ t, Y' x r s (t, y)) s := by
      intro η
      simp only [spec]
      calc ∑ a, ∑ y, η y • Yw r s (a, y) = ∑ y, η y • ∑ a, Yw r s (a, y) := by
            rw [Finset.sum_comm]
            simp only [Finset.smul_sum]
        _ = ∑ y, η y • ∑ t, Yt r s (t, y) := by simp only [hYw5]
        _ = _ := by
            simp only [hYt, Finset.smul_sum, smul_smul]
            refine (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
            refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
              Finset.sum_congr rfl fun t _ => ?_
            have hp : ((l : ℕ) : Qbar l) ^ M = ((l : ℕ) : Qbar l) ^ (M - m x) * ((l : ℕ) : Qbar l) ^ (m x) := by
              rw [← pow_add, Nat.sub_add_cancel (hmM x)]
            rw [hp]
            congr 1
            ring
    have hR : ∀ η : (ZMod (l ^ r))ˣ → Qbar l,
        eul l e (normV w) a δ • ((l : ℕ) : Qbar l) ^ (M + c₁) • spec η (Y r) s +
          (mat W s *ᵥ (∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x)) • b' x r) -
            ∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x)) • b' x r) =
        ∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x)) •
          (eul l e (normV w) a δ • ((l : ℕ) : Qbar l) ^ (m x + c₁) • spec η (Yx x.1 r) s +
            (mat W s *ᵥ b' x r - b' x r)) := by
      intro η
      simp only [smul_add, Finset.sum_add_distrib]
      congr 1
      · simp only [spec, hYsum, hsub, Finset.smul_sum, smul_smul]
        refine Finset.sum_comm.trans (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_)
        have hp : ((l : ℕ) : Qbar l) ^ (M + c₁) =
            ((l : ℕ) : Qbar l) ^ (M - m x) * ((l : ℕ) : Qbar l) ^ (m x + c₁) := by
          rw [← pow_add]
          congr 1
          have := hmM x
          omega
        rw [hp]
        congr 1
        ring
      · simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, smul_sub, Finset.sum_sub_distrib]
    beta_reduce
    rw [hL, hR]
    exact hcv i
  · intro B σ hB hF
    obtain ⟨he1, htr, hdet⟩ := hfrob B σ hB hF
    exact hEC.2 σ hInt.2.1 he1 htr hdet
