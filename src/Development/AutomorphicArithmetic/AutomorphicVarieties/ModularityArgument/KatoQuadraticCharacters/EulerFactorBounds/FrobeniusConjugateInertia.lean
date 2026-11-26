module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.FrobeniusConjugateInertia.FrobConjIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelPowPrimeFourthPowerDescent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraKummerFunctionUniformExceptionalPr

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsStmt
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES UpperTheory.Kd.K4
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Z.Kato.Nb

def SEsLev : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ), 1 ≤ N →
    ∀ b ∈ X.BSet N l w, ∀ n : ℕ, (∀ u u' : Fin 2 → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ u i - u' i) →
      AdicCompletion.eval (idl l) (X.Kl l) n (b u - b u') = 0) ∧ (∀ (t : ℤ_[l]) u, b (t • u) = t ^ w • b u) ∧
      ∀ u, ∃ (k : ℕ) (F : X.Kˣ), n ≤ k ∧ F ∈ X.Un (l ^ n) ∧ ES.Lev X (6 * l * N * l ^ k) (F : X.K) ∧ Rep X l n F ((4 : ℤ_[l]) • b u)

def SEsFrob : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (v : Pl) (B : ValuationSubring Ω) (σ : G ℚ Ω),
    (normV v).Prime → normV v ≠ l → IsPlaceOver B v → IsFrob B (normV v) σ →
      FrobV B (normV v) σ ∧ (cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) = (normV v : ℕ)

def SEsT : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w q M : ℕ), 1 ≤ N →
    q.Prime → Nat.Coprime q (l * N) → Nat.Coprime q M → l * N ∣ M → ∀ γ : SL(2, ℤ), DiagMod M q γ → ∀ b ∈ X.BSet N l w,
      X.heckeT N l q b = (∑ j ∈ Finset.range q, X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b) +
        X.act l ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) b ∧
      ∀ s, X.diam N l q (X.galB l s b) = X.galB l s (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b)

def SEs : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), l ≠ 2 → ∀ (N w : ℕ),
    1 ≤ N → ∃ S0 : Finset ℕ, ∀ (v : Pl) (B : ValuationSubring Ω) (σ : G ℚ Ω), normV v ∉ S0 → (normV v).Prime →
      IsPlaceOver B v → IsFrob B (normV v) σ → ∀ b ∈ X.B N l w,
        X.heckeT N l (normV v) b = X.galB l σ b + ((normV v : ℤ_[l]) ^ (w + 1)) • X.diam N l (normV v) (X.galB l σ⁻¹ b)

end UpperTheory.V.Z.Kato.Nb

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsOf
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsFrob
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES
open scoped Matrix MatrixGroups Pointwise

theorem UpperTheory.V.Z.Kato.Nb.sEsFrob : UpperTheory.V.Z.Kato.Nb.SEsFrob := by
  intro Ω _ _ _ l _ v B σ hq hql hB hF
  obtain ⟨hσ, hfr⟩ := hF
  have hmem : ∀ g : Gal(Ω/ℚ), g ∈ ValuationSubring.decompositionSubgroup ℚ B → ∀ y ∈ B, g y ∈ B :=
    fun g hg y hy => (B.subMulAction ℚ).smul_mem' ⟨g, hg⟩ hy
  refine ⟨⟨?_, fun y hy => ⟨hmem σ hσ y hy, hmem σ⁻¹ (inv_mem hσ) y hy,
    hfr y ((B.valuation_le_one_iff y).mpr hy)⟩⟩, ?_⟩
  · rw [ValuationSubring.mem_nonunits_iff]
    have h := (hB ((normV v : ℕ) : 𝓞 ℚ)).mpr ((UpperTheory.V.Z.Kato.Nb.mem_place_iff v _).mpr dvd_rfl)
    simpa using h
  · have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
      rw [UpperTheory.V.Z.Kato.Nb.mem_place_iff]
      intro hd
      exact hql ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp hd)
    exact cycZ_of_isFrob hl hB ⟨hσ, hfr⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.OfDesc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups

theorem UpperTheory.V.Z.Kato.Nb.sEsLev : UpperTheory.V.Z.Kato.Nb.SEsLev := by
  unfold SEsLev
  intro Ω _ _ _ ε X l _ N w hN b hb n
  have hl : Nat.Prime l := Fact.out
  obtain ⟨⟨c, hcA, hbu⟩, hinv⟩ := hb
  have api := sApi Ω ε X l n
  have cls := sCls Ω ε X l n
  have ev := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n
  have hsub : ∀ (x y x' y' : ℤ_[l]) (a e : ℕ), (l : ℤ_[l]) ^ n ∣ x - x' → (l : ℤ_[l]) ^ n ∣ y - y' →
      (l : ℤ_[l]) ^ n ∣ x ^ a * y ^ e - x' ^ a * y' ^ e := by
    intro x y x' y' a e hx hy
    have h : x ^ a * y ^ e - x' ^ a * y' ^ e = (x ^ a - x' ^ a) * y ^ e + x' ^ a * (y ^ e - y' ^ e) := by ring
    rw [h]
    exact dvd_add (dvd_mul_of_dvd_left (hx.trans (sub_dvd_pow_sub_pow x x' a)) _)
      (dvd_mul_of_dvd_right (hy.trans (sub_dvd_pow_sub_pow y y' e)) _)
  have cong : ∀ u u' : Fin 2 → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ u i - u' i) →
      (AdicCompletion.eval (idl l) (X.Kl l) n) (b u - b u') = 0 := by
    intro u u' h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hbu u, hbu u', ← Finset.sum_sub_distrib, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact api.2.2.2.2.1 _ _ _ (hsub _ _ _ _ _ _ (h 0) (h 1))
  refine ⟨cong, ?_, ?_⟩
  · intro t u
    rw [hbu, hbu, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    congr 1
    have hi : (i : ℕ) + (w - i) = w := Nat.add_sub_cancel' (Nat.lt_succ_iff.mp i.2)
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [show t ^ w = t ^ (i : ℕ) * t ^ (w - i) by rw [← pow_add, hi]]
    ring
  · intro u
    have hbA : b u ∈ X.A l := by
      rw [hbu]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hcA i)
    obtain ⟨φ0, hφ, hd⟩ := X.j_hol
    obtain ⟨f, hfU, hf⟩ := GlobalTheory.T.exists_unit_eval_eq_kummer_class ε X ⟨φ0, hd, hφ⟩ l n (b u) hbA
    obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 6 * l * N * l ^ n := ⟨_, rfl⟩
    have hMpos : 0 < M := by
      rw [hM]
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hl.pos) hN) (pow_pos hl.pos n)
    have hMd : 6 * l ∣ M := ⟨N * l ^ n, by rw [hM]; ring⟩
    have hNM : (N : ℤ) ∣ (M : ℤ) := ⟨6 * l * l ^ n, by rw [hM]; push_cast; ring⟩
    have hlM : (l : ℤ) ∣ (M : ℤ) := ⟨6 * N * l ^ n, by rw [hM]; push_cast; ring⟩
    have hlnM : (l : ℤ) ^ n ∣ (M : ℤ) := ⟨6 * l * N, by rw [hM]; push_cast; ring⟩
    have key : ∀ (d : ℕ) (x y : ℤ), (d : ℤ) ∣ y - x → ((x : ZMod d) = (y : ZMod d)) :=
      fun d x y h => (ZMod.intCast_eq_intCast_iff_dvd_sub x y d).mpr h
    have hdl : ∀ x : ℤ, (M : ℤ) ∣ x → (l : ℤ_[l]) ^ n ∣ (x : ℤ_[l]) := by
      intro x hx
      obtain ⟨e, he⟩ := hlnM.trans hx
      exact ⟨(e : ℤ_[l]), by rw [he]; push_cast; ring⟩
    have hγ : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ,
        (X.sl (ofSL γ)) (f : X.K) = (f : X.K) * (g : X.K) ^ l ^ n := by
      intro γ hγM
      rw [CongruenceSubgroup.Gamma_mem] at hγM
      obtain ⟨h00, h01, h10, h11⟩ := hγM
      have d00 : (M : ℤ) ∣ 1 - γ 0 0 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h00)
      have d01 : (M : ℤ) ∣ 0 - γ 0 1 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h01)
      have d10 : (M : ℤ) ∣ 0 - γ 1 0 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h10)
      have d11 : (M : ℤ) ∣ 1 - γ 1 1 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using h11)
      have hG : γ ∈ Gam N l := by
        show γ ∈ CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l
        refine Subgroup.mem_inf.mpr ⟨(CongruenceSubgroup.Gamma1_mem N γ).mpr ⟨?_, ?_, ?_⟩,
          CongruenceSubgroup.Gamma0_mem.mpr ?_⟩
        · simpa using key N _ _ (hNM.trans d00)
        · simpa using key N _ _ (hNM.trans d11)
        · simpa using key N _ _ (hNM.trans d10)
        · simpa using key l _ _ (hlM.trans d10)
      have hact := congrFun (hinv γ hG) u
      simp only [GlobalTheory.KZ.Tower.act, LinearMap.coe_mk, AddHom.coe_mk] at hact
      rw [Betti.toGQ_sl] at hact
      have hcu : ∀ i, (l : ℤ_[l]) ^ n ∣ (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) i - u i := by
        refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · have e : (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 - u 0
              = ((γ 0 0 - 1 : ℤ) : ℤ_[l]) * u 0 + ((γ 0 1 : ℤ) : ℤ_[l]) * u 1 := by
            simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
            ring
          rw [e]
          exact dvd_add (dvd_mul_of_dvd_left (hdl _ (dvd_sub_comm.mp d00)) _)
            (dvd_mul_of_dvd_left (hdl _ (by simpa using d01)) _)
        · have e : (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1 - u 1
              = ((γ 1 0 : ℤ) : ℤ_[l]) * u 0 + ((γ 1 1 - 1 : ℤ) : ℤ_[l]) * u 1 := by
            simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
            ring
          rw [e]
          exact dvd_add (dvd_mul_of_dvd_left (hdl _ (by simpa using d10)) _)
            (dvd_mul_of_dvd_left (hdl _ (dvd_sub_comm.mp d11)) _)
      have heq : (AdicCompletion.eval (idl l) (X.Kl l) n) (b (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u))
          = X.cls l n f := by
        rw [← hf, ← sub_eq_zero, ← map_sub]
        exact cong _ u hcu
      have h2 := KmapA.eval_kmap X l (X.sl (ofSL γ)).toRingEquiv n _ f heq
      rw [hact, hf] at h2
      obtain ⟨g, hg⟩ := (ev.2.1 _ _).mp h2.symm
      refine ⟨g, ?_⟩
      have := congrArg Units.val hg
      simpa using this
    obtain ⟨k', h, hlev⟩ := GlobalTheory.T.exists_level_pow_prime_fourth_power_descent ε X l n M hl hMpos hMd f hγ
    refine ⟨n + k', f ^ 4 * h ^ l ^ n, Nat.le_add_right _ _, ?_, ?_, ?_⟩
    · intro W hW
      obtain ⟨g, hg⟩ := hfU W hW
      refine ⟨g ^ 4 * h, ?_⟩
      have hg0 : (g : X.K) ≠ 0 := g.ne_zero
      have hh0 : (h : X.K) ≠ 0 := h.ne_zero
      have e : ((f ^ 4 * h ^ l ^ n : X.Kˣ) : X.K) / ((g ^ 4 * h : X.Kˣ) : X.K) ^ l ^ n
          = ((f : X.K) / (g : X.K) ^ l ^ n) ^ 4 := by
        push_cast
        field_simp
        ring
      rw [e, map_pow, hg, one_pow]
    · have e : M * l ^ k' = 6 * l * N * l ^ (n + k') := by rw [hM, pow_add]; ring
      rw [← e]
      push_cast
      exact hlev
    · have r1 : UpperTheory.Kd.K4.Rep X l n f (b u) := hf
      have r2 := cls.2.2.1 f (b u) 4 r1
      have r3 : UpperTheory.Kd.K4.Rep X l n (h ^ l ^ n) 0 := by
        show _ = _
        rw [map_zero]
        have h3 := (ev.2.1 (h ^ l ^ n) 1).mpr ⟨h, by simp⟩
        rw [h3, ev.2.2.2.1]
      have h4 := (cls.2.1 _ _ _ _ r2 r3).1
      simpa using h4
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SEsT
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES
open scoped Matrix MatrixGroups Pointwise

theorem UpperTheory.V.Z.Kato.Nb.sEsT : UpperTheory.V.Z.Kato.Nb.SEsT := by
  intro Ω _ _ _ ε X l _ N w q M hN hq hqlN hqM hM γ hγ b hb
  have hb' : ∀ g ∈ Gam N l, X.act l ↑g b = b := by
    unfold Tower.BSet at hb
    exact hb.2
  have hN0 : N ≠ 0 := by omega
  have hl0 : l ≠ 0 := (Fact.out : Nat.Prime l).ne_zero
  have hqN : q.Coprime N := (Nat.coprime_mul_iff_right.mp hqlN).2
  have hSD := Betti.isDiam_sgD (l := l) hN0 hl0 hqN
  unfold IsDiam at hSD
  obtain ⟨hSmem, hSq⟩ := hSD
  obtain ⟨hS0N, hS0l⟩ := Subgroup.mem_inf.mp hSmem
  rw [CongruenceSubgroup.Gamma0_mem] at hS0N hS0l
  unfold en at hSq
  unfold DiagMod at hγ
  obtain ⟨-, hγc, hγd⟩ := hγ
  unfold en at hγc hγd
  have hNM : N ∣ M := (dvd_mul_left N l).trans hM
  have hlM : l ∣ M := (dvd_mul_right l N).trans hM
  have hcN : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0 := by
    simpa using congrArg (ZMod.castHom hNM (ZMod N)) hγc
  have hcl : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod l) = 0 := by
    simpa using congrArg (ZMod.castHom hlM (ZMod l)) hγc
  have hdN : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = q := by
    simpa using congrArg (ZMod.castHom hNM (ZMod N)) hγd
  have hδ : sgD N l q * γ⁻¹ ∈ Gam N l := by
    have hS := congrArg (Int.cast : ℤ → ZMod N) (Matrix.SpecialLinearGroup.det_coe (sgD N l q))
    have hG := congrArg (Int.cast : ℤ → ZMod N) (Matrix.SpecialLinearGroup.det_coe γ)
    rw [Matrix.det_fin_two] at hS hG
    push_cast at hS hG
    unfold Gam
    rw [Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp
    push_cast
    generalize (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) = S at *
    generalize (γ : Matrix (Fin 2) (Fin 2) ℤ) = G at *
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · linear_combination (↑(S 0 0) : ZMod N) * hdN - (↑(S 0 0) : ZMod N) * hSq + hS
        + (↑(S 0 1) : ZMod N) * hS0N - (↑(S 0 1) : ZMod N) * hcN
    · linear_combination (↑(G 0 0) : ZMod N) * hSq - (↑(G 0 0) : ZMod N) * hdN + hG
        + (↑(G 0 1) : ZMod N) * hcN - (↑(G 0 1) : ZMod N) * hS0N
    · linear_combination (↑(G 1 1) : ZMod N) * hS0N - (↑(S 1 1) : ZMod N) * hcN
    · linear_combination (↑(G 1 1) : ZMod l) * hS0l - (↑(S 1 1) : ZMod l) * hcl
  have hAct : X.act l ↑γ b = X.act l ↑(sgD N l q) b := by
    conv_lhs => rw [← hb' _ hδ]
    rw [Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num)
      (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num), ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel_right]
  have hdq : (0 : ℤ) < Matrix.det !![(q : ℤ), 0; 0, 1] := by
    simpa [Matrix.det_fin_two] using hq.pos
  refine ⟨?_, fun s => ?_⟩
  · unfold Tower.heckeT
    simp only [LinearMap.add_apply, LinearMap.sum_apply]
    congr 1
    · symm
      have hinj : ∀ a ∈ Finset.range q, ∀ a' ∈ Finset.range q, a * M % q = a' * M % q → a = a' := by
        intro a ha a' ha' h
        rw [Finset.mem_range] at ha ha'
        have h' : a ≡ a' [MOD q] := Nat.ModEq.cancel_right_of_coprime hqM h
        unfold Nat.ModEq at h'
        rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h'
      refine Finset.sum_nbij (fun j => j * M % q) (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hq.pos))
        (fun a ha a' ha' h => hinj a (Finset.mem_coe.mp ha) a' (Finset.mem_coe.mp ha') h) ?_ ?_
      · intro k hk
        obtain ⟨a, ha, h⟩ := Finset.surj_on_of_inj_on_of_card_le (fun a _ => a * M % q)
          (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hq.pos)) (fun a a' ha ha' h => hinj a ha a' ha' h)
          le_rfl k (Finset.mem_coe.mp hk)
        exact ⟨a, Finset.mem_coe.mpr ha, h.symm⟩
      · intro a _
        have hdm := Nat.mod_add_div (a * M) q
        generalize a * M % q = r at hdm ⊢
        generalize a * M / q = t at hdm
        let T : SL(2, ℤ) := ⟨!![1, (t : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩
        have hT : T ∈ Gam N l := by
          unfold Gam
          rw [Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem]
          simp [T]
        have hz : (a : ℤ) * M = r + q * t := by exact_mod_cast hdm.symm
        have hm : !![1, (a : ℤ) * M; 0, (q : ℤ)] = (T : Matrix (Fin 2) (Fin 2) ℤ) * !![1, (r : ℤ); 0, (q : ℤ)] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [T, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination hz
        rw [hm, ← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num)
          (by simpa [Matrix.det_fin_two] using hq.pos), hb' T hT]
    · rw [← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num) hdq,
        ← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num) hdq, hAct]
  · unfold Tower.diam
    rw [GlobalTheory.T.galois_commutes_hecke_action ε X N l w hN b hb _ hSmem s, hAct]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KZ.ES UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups

private theorem dvd2 {R : Type} [CommRing R] {d a b x y z : R} (ha : d ∣ a) (hb : d ∣ b) (h : z = a * x + b * y) : d ∣ z :=
  h ▸ dvd_add (ha.mul_right x) (hb.mul_right y)

private theorem es_of (h1 : SEsLev) (h2 : SEsFrob) (h3 : SEsT)
    (hU : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → l ∣ M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ (n k : ℕ) (f : X.Kˣ), f ∈ X.Un (l ^ n) → ES.Lev X (M₀ * l ^ k) f → ∀ γ : SL(2, ℤ), DiagMod (M₀ * l ^ k) q γ → ∃ g : X.Kˣ, Nq X (M₀ * l ^ k) q f * X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL γ) (f : X.K))) ^ q * (g : X.K) ^ (l ^ n)) :
    SEs := by
  intro l hl Ω _ _ _ ε X ho N w hN
  have hM0 : 0 < 6 * l * N := by have := hl.out.pos; positivity
  obtain ⟨φ, hφ1, hφ2⟩ := X.j_hol
  obtain ⟨S, hS⟩ := hU ε X ⟨φ, hφ2, hφ1⟩ l (6 * l * N) hl.out hM0 ⟨6 * N, by ring⟩
  refine ⟨S ∪ (6 * l * N).primeFactors, fun v B σ hv hq hB hσ b hb => ?_⟩
  set q := normV v with hqdef
  rw [Finset.mem_union, not_or] at hv
  have hc : Nat.Coprime q (6 * l * N) := (Nat.Prime.coprime_iff_not_dvd hq).2 fun h =>
    hv.2 (Nat.mem_primeFactors.2 ⟨hq, h, hM0.ne'⟩)
  have hcl : Nat.Coprime q l := hc.coprime_dvd_right ⟨6 * N, by ring⟩
  have hql : q ≠ l := fun h => by
    rw [h, Nat.coprime_self] at hcl
    exact hl.out.ne_one hcl
  obtain ⟨hF, hχ⟩ := h2 Ω l v B σ hq hql hB hσ
  induction hb using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy, smul_add]; abel
  | smul a x _ hx => simp only [map_smul, hx, smul_add, smul_comm a]
  | mem b hb =>
  funext u
  rw [← sub_eq_zero]
  have sep : ∀ x : X.Khat l, (∀ n, AdicCompletion.eval (idl l) (X.Kl l) n x = 0) → x = 0 := fun x h =>
    AdicCompletion.ext fun n => by simpa [AdicCompletion.eval_apply] using h n
  refine sep _ fun n => ?_
  obtain ⟨c1, c2, c3⟩ := h1 Ω ε X l N w hN b hb n
  obtain ⟨k, F, hk, hFu, hFl, hR⟩ := c3 ![u 0, (q : ℤ_[l]) * u 1]
  set M := 6 * l * N * l ^ k with hM
  have hMpos : 0 < M := by have := hl.out.pos; positivity
  have hcM : Nat.Coprime q M := Nat.Coprime.mul_right hc (hcl.pow_right k)
  obtain ⟨γ, hγ⟩ : ∃ γ : SL(2, ℤ), DiagMod M q γ := by
    haveI : NeZero M := ⟨hMpos.ne'⟩
    let t := ZMod.unitOfCoprime q hcM
    obtain ⟨γ, hγ⟩ := GlobalTheory.T.specialLinearGroup_int_map_zmod_surjective M (⟨!![((t⁻¹ : (ZMod M)ˣ) : ZMod M), 0; 0, (t : ZMod M)], by simp [Matrix.det_fin_two_of]⟩ : SL(2, ZMod M))
    have e := fun i j => congrArg (fun m : SL(2, ZMod M) => (m : Matrix (Fin 2) (Fin 2) (ZMod M)) i j) hγ
    exact ⟨γ, by simpa [en] using e 0 1, by simpa [en] using e 1 0, by simpa [en, t] using e 1 1⟩
  obtain ⟨g, hg⟩ := hS q hq hv.1 B σ hF n k F hFu hFl γ hγ
  obtain ⟨t1, t2⟩ := h3 Ω ε X l N w q M hN hq (hc.coprime_dvd_right ⟨6, by ring⟩) hcM ⟨6 * l ^ k, by rw [hM]; ring⟩ γ hγ b hb
  obtain ⟨-, r2, r3, r4, r5, -, -⟩ := sCls Ω ε X l n
  have hd : ∀ z : ℤ, (M : ℤ) ∣ z → (l : ℤ_[l]) ^ n ∣ (z : ℤ_[l]) := fun z hz => by
    have : ((l ^ n : ℕ) : ℤ) ∣ z := (Int.natCast_dvd_natCast.2 ((pow_dvd_pow l hk).mul_left _)).trans hz
    simpa using (Int.castRingHom ℤ_[l]).map_dvd this
  have d01 := hd _ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ.1)
  have d10 := hd _ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ.2.1)
  have d11 := hd (en γ 1 1 - q) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by push_cast; rw [hγ.2.2, sub_self]))
  have dM := hd M dvd_rfl
  have hdet : ((en γ 0 0 : ℤ) : ℤ_[l]) * (en γ 1 1 : ℤ) - (en γ 0 1 : ℤ) * (en γ 1 0 : ℤ) = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[l]) this
  push_cast at d11 dM
  have d00 : (l : ℤ_[l]) ^ n ∣ ((en γ 0 0 : ℤ) : ℤ_[l]) * q - 1 :=
    dvd2 (x := -((en γ 0 0 : ℤ) : ℤ_[l])) (y := ((en γ 1 0 : ℤ) : ℤ_[l])) d11 d01 (by linear_combination hdet)
  have near : ∀ u' : Fin 2 → ℤ_[l], (l : ℤ_[l]) ^ n ∣ u' 0 - u 0 → (l : ℤ_[l]) ^ n ∣ u' 1 - q * u 1 →
      Rep X l n F ((4 : ℤ_[l]) • b u') := fun u' a0 a1 => by
    have := c1 u' ![u 0, (q : ℤ_[l]) * u 1] (Fin.forall_fin_two.2 ⟨a0, a1⟩)
    rw [map_sub, sub_eq_zero] at this
    unfold UpperTheory.Kd.K4.Rep at hR ⊢
    rw [map_smul, this, ← map_smul, hR]
  have one : Rep X l n 1 0 := by simpa using (r2 _ _ _ _ hR hR).2
  have A : ∀ s : Finset ℕ, Rep X l n (∏ j ∈ s, Units.map ((X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)])).toRingEquiv : X.K →* X.K) F)
      (∑ j ∈ s, (4 : ℤ_[l]) • X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b u) := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using one
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      refine (r2 _ _ _ _ ?_ ih).1
      have := r5 (X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)])).toRingEquiv _ _
        (near (mZl l !![1, (j * M : ℤ); 0, (q : ℤ)] *ᵥ u)
          (dvd2 (x := j * u 1) (y := 0) dM dM (by simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring))
          (by simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]))
      rwa [map_smul] at this
  have Bq := r5 (X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]))).toRingEquiv _ _
    (near (mZl l ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) *ᵥ u)
      (dvd2 (x := u 0) (y := u 1) d00 d01 (by simp [mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]; ring))
      (dvd2 (x := q * u 0) (y := u 1) d10 d11 (by simp [mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]; ring)))
  have Cq := r5 (X.gal σ) _ _ hR
  set χ' : ℤ_[l] := (cyclotomicCharacter Ω l (σ⁻¹).toRingEquiv : ℤ_[l]) with hχ'
  have hχq : (q : ℤ_[l]) * χ' = 1 := by
    rw [← hχ, hχ', ← Units.val_mul, ← map_mul]
    have : σ.toRingEquiv * (σ⁻¹).toRingEquiv = 1 := by
      ext z; exact σ.apply_symm_apply z
    rw [this, map_one, Units.val_one]
  have D0 := near ((q : ℤ_[l]) • (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, χ' * u 1]))
    (dvd2 (x := u 0) (y := q * χ' * u 1) d00 d01 (by simp [mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring))
    (dvd2 (x := q * u 0) (y := u 1) d10 d11 (by
      simp [mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℤ_[l]) * u 1 * hχq))
  rw [c2] at D0
  have D := r3 _ _ q (r5 (X.gal σ⁻¹) _ _ (r5 (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ D0))
  have fin := r4 _ _ _ _ (r2 _ _ _ _ (A (Finset.range q)) Bq).1 (r2 _ _ _ _ Cq D).1 ⟨g, Units.ext (by
    rw [(sSlD Ω ε X N hN).2.2.1 γ]
    have hg' : Nq X M q F * _ = X.gal σ F * (X.gal σ⁻¹ _) ^ q * _ := hg
    clear_value M
    simpa [Nq, Units.coe_prod] using hg')⟩
  have h4 : IsUnit (4 : ℤ_[l]) := by
    have : IsUnit ((4 : ℕ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact ((Nat.coprime_primes hl.out Nat.prime_two).2 ho).pow_right 2
    simpa using this
  rw [← h4.smul_eq_zero, ← map_smul, ← fin, t1, t2]
  congr 1
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_sub, smul_add, Finset.smul_sum, map_smul]
  congr 1
  change _ + (4 : ℤ_[l]) • (q : ℤ_[l]) ^ (w + 1) • X.kmap l (X.gal σ⁻¹) (X.kmap l _ (b _)) = _
  rw [smul_smul, smul_smul, smul_smul]
  congr 1
  · change (4 : ℤ_[l]) • X.kmap l (X.gal σ) (b _) = _
    rw [hχ]
  · congr 1
    ring

theorem UpperTheory.V.Z.Kato.Nb.sEs : UpperTheory.V.Z.Kato.Nb.SEs := es_of sEsLev sEsFrob sEsT @GlobalTheory.T.eichlerShimura_kummer_function_uniform_exceptional_primes
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DiamChar
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb

open CongruenceSubgroup

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]

private theorem dc_fix (N w : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  unfold Tower.B at hb
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 γ hγ
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

private theorem dc_mul (σ τ : SL(2, ℤ)) (b : X.Fn l) :
    X.act l (τ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b) =
      X.act l ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b := by
  rw [Tower.act_act Ω ε X l _ _ (by rw [σ.2]; norm_num) (by rw [τ.2]; norm_num),
    Matrix.SpecialLinearGroup.coe_mul]

private theorem dc_en (N : ℕ) (σ τ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (hτ : τ ∈ Gamma0 N) :
    (en (σ * τ) 1 1 : ZMod N) = (en σ 1 1 : ZMod N) * (en τ 1 1 : ZMod N) := by
  have h0 := Gamma0_mem.1 hσ
  simp only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [h0]
  ring

private theorem dc_same (N w : ℕ) (σ τ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N ⊓ Gamma0 l) (hτ : τ ∈ Gamma0 N ⊓ Gamma0 l)
    (h : (en σ 1 1 : ZMod N) = (en τ 1 1 : ZMod N)) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b = X.act l (τ : Matrix (Fin 2) (Fin 2) ℤ) b := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = τ * σ⁻¹ := ⟨_, rfl⟩
  have hτ' : τ = ρ * σ := by rw [hρ, inv_mul_cancel_right]
  have hρ0 : ρ ∈ Gamma0 N ⊓ Gamma0 l := by
    rw [hρ]
    exact Subgroup.mul_mem _ hτ (Subgroup.inv_mem _ hσ)
  have det1 : ∀ B : SL(2, ℤ), B ∈ Gamma0 N → (en B 0 0 : ZMod N) * (en B 1 1 : ZMod N) = 1 := by
    intro B hB
    have h0 := Gamma0_mem.1 hB
    have hd := congrArg (fun z : ℤ => (z : ZMod N)) B.2
    simp only [Matrix.det_fin_two] at hd
    push_cast at hd
    rw [h0, mul_zero, sub_zero] at hd
    exact hd
  have hσ11 : (en σ⁻¹ 1 1 : ZMod N) = (en σ 0 0 : ZMod N) := by
    simp [en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hρ11 : (en ρ 1 1 : ZMod N) = 1 := by
    rw [hρ, dc_en N τ σ⁻¹ hτ.1 (Subgroup.inv_mem _ hσ.1), ← h, hσ11, mul_comm]
    exact det1 σ hσ.1
  have hρ00 : (en ρ 0 0 : ZMod N) = 1 := by
    have := det1 ρ hρ0.1
    rw [hρ11, mul_one] at this
    exact this
  have hρG : ρ ∈ Gam N l := ⟨(Gamma1_mem _ _).2 ⟨hρ00, hρ11, Gamma0_mem.1 hρ0.1⟩, hρ0.2⟩
  rw [hτ', ← dc_mul X l ρ σ b, dc_fix X l N w ρ hρG b hb]

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sDiamChar :
    UpperTheory.V.Z.Kato.Nb.SDiamChar := by
  unfold SDiamChar
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he hlN hb
  obtain ⟨-, -, -, -, -, -, -, -, ⟨δ, hδ⟩, -⟩ := hA
  obtain ⟨b0, hb0, hne⟩ := hb
  have hl : l.Prime := Fact.out
  have hN0 : N ≠ 0 := NeZero.ne N
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  have hdiam : ∀ (q : ℕ) (b : X.Fn l),
      X.diam N l q b = X.act l (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) b := fun q b => rfl
  have hcop : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → q.Coprime N := fun q hq hd =>
    (Nat.Prime.coprime_iff_not_dvd hq).2 (fun h => hd (Dvd.dvd.mul_left h l))
  have hisD : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → IsDiam N l q (sgD N l q) :=
    fun q hq hd => Betti.isDiam_sgD hN0 hl.ne_zero (hcop q hq hd)
  have hpr : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b ∈ X.B N l (2 * e - 1),
      pr (X.act l (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) b) = δ q • pr b :=
    fun q hq hd b hb => (hδ q hq hd b hb).2
  have cancel : ∀ a a' : Qbar l, a • pr b0 = a' • pr b0 → a = a' :=
    fun a a' h => smul_left_injective (Qbar l) hne h
  have hQ : ∀ u : (ZMod N)ˣ, ∃ q > l * N, q.Prime ∧ (q : ZMod N) = u :=
    fun u => Nat.forall_exists_prime_gt_and_eq_mod u.isUnit (l * N)
  choose Q hQgt hQp hQu using hQ
  have hQd : ∀ u, ¬ Q u ∣ l * N := fun u h => by
    have h1 := Nat.le_of_dvd (Nat.mul_pos hl.pos hNpos) h
    have h2 := hQgt u
    omega
  have mem : ∀ u, sgD N l (Q u) ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l :=
    fun u => (hisD _ (hQp u) (hQd u)).1
  have en_u : ∀ u, (en (sgD N l (Q u)) 1 1 : ZMod N) = u := fun u => by
    rw [(hisD _ (hQp u) (hQd u)).2, hQu]
  have inB : ∀ u (b : X.Fn l), b ∈ X.B N l (2 * e - 1) →
      X.act l (sgD N l (Q u) : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.B N l (2 * e - 1) :=
    fun u b hb => (sBStab Ω ε X l N (2 * e - 1) hNpos b hb).2.1 _ (mem u)
  have hΔ : ∀ u (b : X.Fn l), b ∈ X.B N l (2 * e - 1) →
      pr (X.act l (sgD N l (Q u) : Matrix (Fin 2) (Fin 2) ℤ) b) = δ (Q u) • pr b :=
    fun u b hb => hpr _ (hQp u) (hQd u) b hb
  have formula : ∀ (q : ℕ) (u : (ZMod N)ˣ), q.Prime → ¬ q ∣ l * N → (u : ZMod N) = q →
      ∀ b ∈ X.B N l (2 * e - 1), pr (X.diam N l q b) = δ (Q u) • pr b := by
    intro q u hq hd hu b hb
    have e1 : X.diam N l q b = X.act l (sgD N l (Q u) : Matrix (Fin 2) (Fin 2) ℤ) b := by
      rw [hdiam]
      exact dc_same X l N (2 * e - 1) _ _ (hisD q hq hd).1 (mem u)
        (by rw [(hisD q hq hd).2, en_u, hu]) b hb
    rw [e1]
    exact hΔ u b hb
  have mul : ∀ u v, δ (Q (u * v)) = δ (Q u) * δ (Q v) := by
    intro u v
    apply cancel
    have e2 : X.act l (((sgD N l (Q u) * sgD N l (Q v) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ) b0 =
        X.act l (sgD N l (Q (u * v)) : Matrix (Fin 2) (Fin 2) ℤ) b0 :=
      dc_same X l N (2 * e - 1) _ _ (Subgroup.mul_mem _ (mem u) (mem v)) (mem (u * v))
        (by rw [dc_en N _ _ (mem u).1 (mem v).1, en_u, en_u, en_u, Units.val_mul]) b0 hb0
    rw [← hΔ (u * v) b0 hb0, ← e2, ← dc_mul X l, hΔ v _ (inB u b0 hb0), hΔ u b0 hb0, smul_smul, mul_comm]
  have one : δ (Q 1) = 1 := by
    apply cancel
    rw [one_smul, ← hΔ 1 b0 hb0]
    have e3 : X.act l (sgD N l (Q 1) : Matrix (Fin 2) (Fin 2) ℤ) b0 =
        X.act l ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b0 :=
      dc_same X l N (2 * e - 1) _ _ (mem 1) (Subgroup.one_mem _) (by rw [en_u]; simp [en]) b0 hb0
    rw [e3, dc_fix X l N (2 * e - 1) 1 (Subgroup.one_mem _) b0 hb0]
  have inv : ∀ u : (ZMod N)ˣ, δ (Q u) * δ (Q u⁻¹) = 1 := fun u => by
    rw [← mul, mul_inv_cancel, one]
  refine ⟨MonoidHom.mk' (fun u => Units.mkOfMulEqOne (δ (Q u)) (δ (Q u⁻¹)) (inv u))
    (fun u v => by
      ext
      simp [mul]), ?_⟩
  intro q u hq hd hu b hb
  simp only [MonoidHom.mk'_apply, Units.val_mkOfMulEqOne]
  exact formula q u hq hd hu b hb
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DetChar
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem fin_places (S : Finset ℕ) : {v : HeightOneSpectrum (𝓞 ℚ) | normV v ∈ S}.Finite := by
  have h : {I : Ideal (𝓞 ℚ) | Ideal.absNorm I ≤ S.sup id}.Finite := Ideal.finite_setOf_absNorm_le _
  refine (h.preimage (f := fun v : HeightOneSpectrum (𝓞 ℚ) => v.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset fun v hv => ?_
  have : normV v ≤ S.sup id := Finset.le_sup (f := id) hv
  simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this

private theorem scal_iff {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K) :
    (∃ t : K, A = t • 1) ↔ A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 0 = A 1 1 := by
  constructor
  · rintro ⟨t, rfl⟩
    simp
  · rintro ⟨h1, h2, h3⟩
    refine ⟨A 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]

private theorem det_of_quad {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K) (a c : K)
    (hA : ¬ ∃ t : K, A = t • 1) (h : A ^ 2 - a • A + c • (1 : Matrix (Fin 2) (Fin 2) K) = 0) : A.det = c := by
  rw [scal_iff] at hA
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have ht : A 0 0 + A 1 1 - a = 0 := by
    by_contra hne
    apply hA
    refine ⟨?_, ?_, ?_⟩
    · exact (mul_eq_zero.1 (by linear_combination h01 : A 0 1 * (A 0 0 + A 1 1 - a) = 0)).resolve_right hne
    · exact (mul_eq_zero.1 (by linear_combination h10 : A 1 0 * (A 0 0 + A 1 1 - a) = 0)).resolve_right hne
    · exact sub_eq_zero.1 ((mul_eq_zero.1
        (by linear_combination h00 - h11 : (A 0 0 - A 1 1) * (A 0 0 + A 1 1 - a) = 0)).resolve_right hne)
  rw [Matrix.det_fin_two]
  linear_combination A 0 0 * ht - h00

theorem UpperTheory.V.Z.Kato.Nb.sDetChar :
    UpperTheory.V.Z.Kato.Nb.SDetChar := by
  intro l _ Ω _ _ _ ρ χ hρ hχ ⟨s₀, hs₀⟩ S hF
  have hc : Continuous fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) := Units.continuous_val.comp hρ
  have hχ' : Continuous fun s => (χ s : Qbar l) := Units.continuous_val.comp hχ
  have he : ∀ i j, Continuous fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) i j := fun i j => hc.matrix_elem i j
  have hU : IsOpen {s | ¬ ∃ t : Qbar l, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = t • 1} := by
    simp only [scal_iff]
    exact (((isClosed_eq (he 0 1) continuous_const).inter
      ((isClosed_eq (he 1 0) continuous_const).inter (isClosed_eq (he 0 0) (he 1 1))))).isOpen_compl
  have hC : IsClosed {s | (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = χ s} := isClosed_eq hc.matrix_det hχ'
  have hD := GlobalTheory.frob_dense_off_finite ℚ Ω _ (fin_places S)
  have key : ∀ s, (¬ ∃ t : Qbar l, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = t • 1) →
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = χ s := by
    intro s hs
    refine hC.closure_subset_iff.2 ?_ (hD.open_subset_closure_inter hU hs)
    rintro σ ⟨hσ, v, hv, B, hB, hf⟩
    obtain ⟨a, ha⟩ := hF v B σ hv hB hf
    exact det_of_quad _ a _ hσ ha
  intro s
  by_cases hs : ∃ t : Qbar l, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = t • 1
  · obtain ⟨t, ht⟩ := hs
    have h0 := key s₀ (fun ⟨u, hu⟩ => hs₀ u hu)
    have h1 := key (s * s₀) (by
      rintro ⟨u, hu⟩
      rw [map_mul, Units.val_mul, ht, smul_mul_assoc, one_mul] at hu
      have t0 : t ≠ 0 := by
        rintro rfl
        exact (ρ s).ne_zero (by simpa using ht)
      exact hs₀ (t⁻¹ * u) (by rw [mul_smul, ← hu, smul_smul, inv_mul_cancel₀ t0, one_smul]))
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, h0] at h1
    exact mul_right_cancel₀ (χ s₀).ne_zero h1
  · exact key s hs
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb.EulerSystemNorms

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem cont_bar : Continuous (cycBar ℚ Ω l) :=
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ ℚ Ω l)

private theorem cont_hom {M : Type} [Monoid M] [TopologicalSpace M] (f : G ℚ Ω →* Mˣ) (h : Continuous fun s => (f s : M)) :
    Continuous f :=
  Units.continuous_iff.2 ⟨h, (h.comp continuous_inv).congr fun s => by simp⟩

private theorem cont_cls [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (δ : (ZMod N)ˣ → Qbar l) :
    Continuous fun s => δ (Chr.cls ℚ Ω N s) := by
  refine (IsLocallyConstant.comp ((IsLocallyConstant.iff_exists_open _).2 fun s => ?_) δ).continuous
  refine ⟨(fun t => s⁻¹ * t) ⁻¹' ((Chr.cls ℚ Ω N).ker : Set (G ℚ Ω)),
    (Chr.clsFacts ℚ Ω N).1.preimage (continuous_const.mul continuous_id), by simp, fun t ht => ?_⟩
  have h : Chr.cls ℚ Ω N (s⁻¹ * t) = 1 := ht
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  exact h.symm

private theorem trace_eq {k : Type} [Field k] (g : GL (Fin 2) k) (a : k)
    (h : (g : Matrix (Fin 2) (Fin 2) k) ^ 2 - a • (g : Matrix (Fin 2) (Fin 2) k) + (g : Matrix (Fin 2) (Fin 2) k).det • 1 = 0) :
    (g : Matrix (Fin 2) (Fin 2) k).trace = a := by
  have hd : (g : Matrix (Fin 2) (Fin 2) k).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  generalize (g : Matrix (Fin 2) (Fin 2) k) = m at h hd
  have e := fun i j => congrFun (congrFun h i) j
  have e00 := e 0 0
  have e01 := e 0 1
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] at e00 e01
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.trace_fin_two]
  have e10 := e 1 0
  have e11 := e 1 1
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] at e10 e11
  apply mul_right_cancel₀ hd
  linear_combination m 1 1 * e00 - m 1 0 * e01

private theorem stable_top {W : R2 Ω l} (h : IsIrr (W.comp (H0g W).subtype)) (U : Submodule (Qbar l) (Fin 2 → Qbar l))
    (h0 : U ≠ ⊥) (hU : ∀ s, ∀ v ∈ U, mat W s *ᵥ v ∈ U) : U = ⊤ :=
  (h.2.2 U le_top fun s v hv => hU s v hv).resolve_left h0

private theorem not_scalar {W : R2 Ω l} (h : IsIrr (W.comp (H0g W).subtype)) : ∃ s, ∀ t : Qbar l, mat W s ≠ t • 1 := by
  by_contra hn
  push Not at hn
  have h1 := stable_top h (Submodule.span (Qbar l) {![1, 0]}) (by simp) fun s v hv => by
    obtain ⟨t, ht⟩ := hn s
    rw [ht, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact Submodule.smul_mem _ _ hv
  have h2 : (![0, 1] : Fin 2 → Qbar l) ∈ Submodule.span (Qbar l) {(![1, 0] : Fin 2 → Qbar l)} := h1 ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h2
  simpa using congrFun hc 1

private theorem inv_mem (cf : Coef l) {q : ℕ} (h : Nat.Coprime q l) : ((q : Qbar l))⁻¹ ∈ cf.O := by
  have hu : IsUnit (q : ℤ_[l]) := PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 h.symm)
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have e := congrArg (algebraMap ℤ_[l] (Qbar l)) hy
  rw [map_mul, map_natCast, map_one] at e
  rw [← eq_inv_of_mul_eq_one_right e]
  exact cf.O.algebraMap_mem y

end UpperTheory.V.Z.Kato.Nb.EulerSystemNorms

open UpperTheory.V.Z.Kato.Nb.EulerSystemNorms in
theorem UpperTheory.V.Z.Kato.Nb.sEuler :
    UpperTheory.V.Z.Kato.Nb.SEuler := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he hlN S hNf hint
  obtain ⟨-, -, -, -, hO, -, -⟩ := sInteg l Ω ι e gN A W ε X pr N x c d gm ψ cf hA he hint
  have hD := sDiamChar l Ω ι e gN A W ε X pr N x c d gm ψ cf hA he hlN
  obtain ⟨hc, hd, -, -, hadd, hsm, -, hgal, ⟨δ', hT⟩, -, -, χ₀, -, -, hχ⟩ := hA
  have hl : l.Prime := Fact.out
  have hN : 0 < N := NeZero.pos N
  obtain ⟨S0, hES⟩ := sEs l Ω ε X hNf.l_odd N (2 * e - 1) hN
  let ρ : R2 Ω l := tw W (cycBar ℚ Ω l ^ e * χ₀⁻¹)
  have hρ : ∀ s, mat ρ s = rhoK W e ψ s := fun s => by
    rw [mat, tw_val, rhoK, thK, ← hχ]
    simp [mul_comm]
  have hn0 : l * N * c * d ≠ 0 := by
    have := hl.pos
    positivity
  have key : ∀ w : Pl, w ∉ S → normV w ∉ S0 → Nat.Coprime (normV w) (l * N) → ∃ a δ : Qbar l,
      (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeT N l (normV w) b) = a • pr b ∧ pr (X.diam N l (normV w) b) = δ • pr b) ∧
      ∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ →
        (rhoK W e ψ σ).trace = a ∧ (rhoK W e ψ σ).det = (normV w : Qbar l) ^ (2 * e) * δ := by
    by_cases hz : ∃ b ∈ X.B N l (2 * e - 1), pr b ≠ 0
    · obtain ⟨δ, hδ⟩ := hD hz
      let χ : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (2 * e) * δ.comp (Chr.cls ℚ Ω N)
      have hspan : Submodule.span (Qbar l) (pr '' (X.B N l (2 * e - 1) : Set (X.Fn l))) = ⊤ := by
        refine stable_top hNf.irr _ (fun h => ?_) fun s v hv => ?_
        · obtain ⟨b, hb, hb0⟩ := hz
          exact hb0 ((Submodule.span_eq_bot.1 h) _ ⟨b, hb, rfl⟩)
        · have h1 : mat W s = ((cycBar ℚ Ω l ^ e * χ₀⁻¹) s⁻¹ : Qbar l) • mat ρ s := by
            rw [mat, mat, tw_val, smul_smul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_smul]
          rw [h1, Matrix.smul_mulVec]
          refine Submodule.smul_mem _ _ ?_
          refine (Submodule.span_le (p := (Submodule.span (Qbar l) (pr '' (X.B N l (2 * e - 1) : Set (X.Fn l)))).comap
            (Matrix.mulVecLin (mat ρ s)))).2 ?_ hv
          rintro _ ⟨b, hb, rfl⟩
          refine Submodule.subset_span ⟨_, (sBStab Ω ε X l N _ hN b hb).1 s, ?_⟩
          rw [hgal s b hb, ← hρ]
          rfl
      have hχF : ∀ (w : Pl), Nat.Coprime (normV w) (l * N) → ∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w →
          IsFrob B (normV w) σ → (χ σ : Qbar l) = (normV w : Qbar l) ^ (2 * e) * δ (Chr.cls ℚ Ω N σ) := fun w hw B σ hB hσ => by
        rw [← eps_frobAt l ((normV_prime w).coprime_iff_not_dvd.1 hw.coprime_mul_right_right) hB hσ]
        simp [χ]
      have hrel : ∀ (w : Pl), normV w ∉ S0 → Nat.Coprime (normV w) (l * N) → ∀ (B : ValuationSubring Ω) (σ : G ℚ Ω),
          IsPlaceOver B w → IsFrob B (normV w) σ →
          mat ρ σ ^ 2 - ι.symm (gN.a (normV w)) • mat ρ σ + (χ σ : Qbar l) • 1 = 0 := fun w hw0 hw B σ hB hσ => by
        have hnd := (normV_prime w).coprime_iff_not_dvd.1 hw
        have h1 : Matrix.mulVecLin (mat ρ σ - ι.symm (gN.a (normV w)) • 1 + (χ σ : Qbar l) • mat ρ σ⁻¹) = 0 := by
          refine LinearMap.ext_on hspan ?_
          rintro _ ⟨b, hb, rfl⟩
          have hb' := (sBStab Ω ε X l N _ hN b hb).1 σ⁻¹
          have h2 := congrArg pr (hES w B σ hw0 (normV_prime w) hB hσ b hb)
          rw [(hT _ (normV_prime w) hnd b hb).1, hadd, hsm, hgal σ b hb,
            hδ _ _ (normV_prime w) hnd (cls_frobAt N hw.coprime_mul_left_right.symm hB hσ) _ hb', hgal _ b hb, smul_smul,
            show 2 * e - 1 + 1 = 2 * e by omega, ← hρ, ← hρ] at h2
          rw [hχF w hw B σ hB hσ, Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
            Matrix.smul_mulVec, Matrix.one_mulVec, h2]
          simp
        have h3 : mat ρ σ - ι.symm (gN.a (normV w)) • 1 + (χ σ : Qbar l) • mat ρ σ⁻¹ = 0 :=
          Matrix.toLin'.injective (h1.trans (map_zero _).symm)
        have h4 := congrArg (· * mat ρ σ) h3
        simp only [add_mul, sub_mul, smul_mul_assoc, one_mul, zero_mul, mat, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
          Units.val_one] at h4
        rw [pow_two, mat, ← Units.val_mul, ← map_mul]
        exact h4
      have hc0 : Continuous fun s => (χ₀ s : Qbar l) := by
        simp only [hχ]
        exact ((GlobalTheory.KZ.IwC.isLocallyConstant_cycMod 1).comp fun u : (ZMod (l ^ 1))ˣ => ψ (((u : ZMod (l ^ 1)).val : ℕ) : ZMod l)).continuous
      have hcρ : Continuous ρ := cont_hom _ (by
        simp only [ρ, tw_val]
        exact (Units.continuous_val.comp ((cont_bar.pow e).mul (cont_hom χ₀ hc0).inv)).smul (Units.continuous_val.comp hNf.cont))
      have hcχ : Continuous χ := (cont_bar.pow (2 * e)).mul (cont_hom (δ.comp (Chr.cls ℚ Ω N)) (cont_cls (Ω := Ω) N fun u => (δ u : Qbar l)))
      have hdet := sDetChar l Ω ρ χ hcρ hcχ (by
        obtain ⟨s, hs⟩ := not_scalar hNf.irr
        refine ⟨s, fun t ht => hs (((cycBar ℚ Ω l ^ e * χ₀⁻¹) s : Qbar l)⁻¹ * t) ?_⟩
        rw [mul_smul, ← ht, tw_val, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]) (S0 ∪ (l * N).primeFactors)
        fun v B σ hv hB hσ => ⟨_, hrel v (fun h => hv (Finset.mem_union_left _ h))
          ((normV_prime v).coprime_iff_not_dvd.2 fun h => hv (Finset.mem_union_right _
            (Nat.mem_primeFactors.2 ⟨normV_prime v, h, (mul_pos hl.pos hN).ne'⟩))) B σ hB hσ⟩
      intro w _ hw0 hw
      have hnd := (normV_prime w).coprime_iff_not_dvd.1 hw
      refine ⟨ι.symm (gN.a (normV w)), δ (ZMod.unitOfCoprime _ hw.coprime_mul_left_right), fun b hb =>
        ⟨(hT _ (normV_prime w) hnd b hb).1, hδ _ _ (normV_prime w) hnd (ZMod.coe_unitOfCoprime _ _) b hb⟩, fun B σ hB hσ => ?_⟩
      rw [← hρ]
      refine ⟨trace_eq _ _ (by rw [hdet]; exact hrel w hw0 hw B σ hB hσ), ?_⟩
      rw [hdet, hχF w hw B σ hB hσ]
      congr 3
      exact Units.ext ((cls_frobAt N hw.coprime_mul_left_right.symm hB hσ).trans (ZMod.coe_unitOfCoprime _ _).symm)
    · push Not at hz
      intro w hwS _ hw
      have hnd := (normV_prime w).coprime_iff_not_dvd.1 hw
      have hnl := (normV_prime w).coprime_iff_not_dvd.1 hw.coprime_mul_right_right
      have hq : ((normV w : ℕ) : Qbar l) ^ (2 * e) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (normV_prime w).ne_zero)
      obtain ⟨B₀, σ₀, hB₀, hσ₀⟩ := exists_frobAt Ω w
      refine ⟨(rhoK W e ψ σ₀).trace, (((normV w : ℕ) : Qbar l) ^ (2 * e))⁻¹ * (rhoK W e ψ σ₀).det, fun b hb => ?_,
        fun B σ hB hσ => ?_⟩
      · rw [(hT _ (normV_prime w) hnd b hb).1, (hT _ (normV_prime w) hnd b hb).2, hz b hb]
        simp
      · have hm := fun h => hnl ((mem_place_iff w l).1 h)
        have h1 : cycZ ℚ Ω l σ = cycZ ℚ Ω l σ₀ := Units.ext ((cycZ_of_isFrob hm hB hσ).trans (cycZ_of_isFrob hm hB₀ hσ₀).symm)
        have h2 : thK l e ψ σ = thK l e ψ σ₀ := by
          simp only [thK, eps, cycBar, cycMod, MonoidHom.comp_apply, h1]
        obtain ⟨h3, h4⟩ := frobInv hNf hwS hB hσ hB₀ hσ₀
        rw [mul_inv_cancel_left₀ hq]
        simp only [rhoK, Matrix.trace_smul, Matrix.det_smul, h2, h3, h4, and_self]
  refine ⟨S ∪ ((finite_normV S0).union (finite_dvd hn0)).toFinset, Finset.subset_union_left, fun w hw => ?_⟩
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or] at hw
  have hcop := (normV_prime w).coprime_iff_not_dvd.2 hw.2.2
  have hw' : Nat.Coprime (normV w) (l * N) := hcop.coprime_mul_right_right.coprime_mul_right_right
  obtain ⟨a, δ, h1, h2⟩ := key w hw.1 hw.2.1 hw'
  obtain ⟨B₀, σ₀, hB₀, hσ₀⟩ := exists_frobAt Ω w
  obtain ⟨h3, h4⟩ := h2 B₀ σ₀ hB₀ hσ₀
  have hq : ((normV w : ℕ) : Qbar l) ^ (2 * e) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (normV_prime w).ne_zero)
  refine ⟨normV_prime w, hcop, a, δ, ?_, ?_, h1, fun B σ hB hσ =>
    ⟨eps_frobAt l ((normV_prime w).coprime_iff_not_dvd.1 hw'.coprime_mul_right_right) hB hσ, h2 B σ hB hσ⟩⟩
  · rw [← h3, Matrix.trace_fin_two]
    exact add_mem (hO _ _ _) (hO _ _ _)
  · rw [← inv_mul_cancel_left₀ hq δ, ← h4, ← inv_pow, Matrix.det_fin_two]
    exact mul_mem (pow_mem (inv_mem cf hw'.coprime_mul_right_right) _)
      (sub_mem (mul_mem (hO _ _ _) (hO _ _ _)) (mul_mem (hO _ _ _) (hO _ _ _)))
