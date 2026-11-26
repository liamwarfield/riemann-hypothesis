module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.EvalSmulCong

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.GalAct
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.GalAct

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem act_sl (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (g h : SL(2, ℤ)) (b : X.Fn l) :
    X.act l (h : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (g : Matrix (Fin 2) (Fin 2) ℤ) b) =
      X.act l ((g * h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos)
    (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos) b

private theorem gam_le (N l : ℕ) : Gam N l ≤ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l :=
  inf_le_inf_right _ (CongruenceSubgroup.Gamma1_in_Gamma0 N)

private theorem conj_mem (N l : ℕ) (γ δ : SL(2, ℤ)) (hγ : γ ∈ Gam N l)
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) : δ * γ * δ⁻¹ ∈ Gam N l := by
  obtain ⟨a1, a2, a3⟩ := (CongruenceSubgroup.Gamma1_mem N γ).1 (Subgroup.mem_inf.1 hγ).1
  have a4 : ((δ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hδ).1
  refine GamComm.mul_inv_mem_Gam N l _ δ (mul_mem hδ (gam_le N l hγ)) hδ ?_ ?_
  · simp [en, Matrix.mul_apply, Fin.sum_univ_two, a1, a3]
  · simp [en, Matrix.mul_apply, Fin.sum_univ_two, a2, a4]

private theorem act_act_conj (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (γ δ : SL(2, ℤ)) (b : X.Fn l) :
    X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b) =
      X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l ((δ * γ * δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  rw [act_sl, act_sl, inv_mul_cancel_right]

private theorem galB_mem [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ) (hN : 0 < N)
    (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (hb : b ∈ X.B N l w) : X.galB l s b ∈ X.B N l w := by
  obtain ⟨φ, h1, h2⟩ := X.j_hol
  have hA := (kmap_A_stable ε X ε.injective ⟨φ, h2, h1⟩ l).2 s
  have himg : X.galB l s '' X.BSet N l w ⊆ X.BSet N l w := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨StabGal.galB_mem_Pol X l w s hA c hc.1, fun γ hγ => StabGal.inv_galB X N l w hN s c hc γ hγ⟩
  exact Submodule.span_mono himg (Submodule.apply_mem_span_image_of_mem_span (X.galB l s) hb)

private theorem act_mem [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ) (δ : SL(2, ℤ))
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.B N l w := by
  obtain ⟨φ, h1, h2⟩ := X.j_hol
  have hA := (kmap_A_stable ε X ε.injective ⟨φ, h2, h1⟩ l).1 (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))
  have himg : X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) '' X.BSet N l w ⊆ X.BSet N l w := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions X l w _ hA c hc.1, fun γ hγ => ?_⟩
    rw [act_act_conj, hc.2 _ (conj_mem N l γ δ hγ hδ)]
  exact Submodule.span_mono himg (Submodule.apply_mem_span_image_of_mem_span (X.act l _) hb)

private theorem eval_congr (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (a t : X.Fn l) (ht : PolMod X l w n t)
    (hat : CgF X l n a t) (u v : Fin 2 → ℤ_[l]) (huv : ∀ i, PadicInt.toZModPow n (u i) = PadicInt.toZModPow n (v i)) :
    AdicCompletion.eval (idl l) (X.Kl l) n (a u) = AdicCompletion.eval (idl l) (X.Kl l) n (a v) := by
  obtain ⟨c, -, hc⟩ := ht
  have e : ∀ x, AdicCompletion.eval (idl l) (X.Kl l) n (a x) = AdicCompletion.eval (idl l) (X.Kl l) n (t x) := fun x => by
    rw [← sub_eq_zero, ← map_sub]; exact hat x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, e, ← sub_eq_zero, ← map_sub, hc, hc, ← Finset.sum_sub_distrib, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← sub_smul, map_smul]
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (c i))
  rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
  simp [huv]

private theorem comm [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n : ℕ) (hN : 0 < N)
    (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (hb : InvM X l N w n b) (δ : SL(2, ℤ))
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) :
    CgF X l n (X.galB l s (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b))
      (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b)) := by
  obtain ⟨⟨t, ht, hbt⟩, hinv, -⟩ := hb
  obtain ⟨hE, -, -, -, -, hact, hgal, -⟩ := sApi Ω ε X l n
  intro u
  have hcls := GlobalTheory.KZ.H3.cls_props Ω ε X l n
  have hF := hcls.2.2.2.2.2.1
  obtain ⟨f, hf⟩ := hcls.1 (AdicCompletion.eval (idl l) (X.Kl l) n
    (b ![(mZl l (δ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0,
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (mZl l (δ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1]))
  obtain ⟨M₀, hM₀, hlev⟩ := X.level (f : X.K)
  have hlp : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨M, hM, hM0, hMN, hMl, hMn⟩ : ∃ M : ℕ, 0 < M ∧ M₀ ∣ M ∧ N ∣ M ∧ l ∣ M ∧ l ^ n ∣ M :=
    ⟨M₀ * N * l * l ^ n, by positivity, ⟨N * l * l ^ n, by ring⟩, ⟨M₀ * l * l ^ n, by ring⟩,
      ⟨M₀ * N * l ^ n, by ring⟩, ⟨M₀ * N * l, by ring⟩⟩
  obtain ⟨ζ, hζ, i, hi, hs, hχ⟩ := GlobalTheory.exists_primitiveRoot_pow_cyclotomicCharacter l n M hM hMn s
  obtain ⟨g, h00, h01, h10, h11⟩ := GlobalTheory.exists_sl2_conj_diag_zmod M i hi δ
  have hc : (en δ 0 0 : ZMod M) = en g 0 0 ∧ (en δ 0 1 : ZMod M) = ((i : ℤ) : ZMod M) * en g 0 1 ∧
      ((i : ℤ) : ZMod M) * en δ 1 0 = en g 1 0 ∧ (en δ 1 1 : ZMod M) = en g 1 1 :=
    ⟨h00, by simpa only [Int.cast_natCast] using h01, by simpa only [Int.cast_natCast] using h10, h11⟩
  have hrec := X.recip M f hM (fun γ hγ => hlev γ (GamComm.gamma_le_of_dvd hM0 hγ)) ζ hζ s i
    (by rw [zpow_natCast, hs]) g δ hc
  have h10' : (((i : ℤ) * en δ 1 0 : ℤ) : ZMod M) = en g 1 0 := by push_cast; exact h10
  have hg0 : ∀ K : ℕ, K ∣ M → δ ∈ CongruenceSubgroup.Gamma0 K → g ∈ CongruenceSubgroup.Gamma0 K := fun K hK h => by
    have a : (en δ 1 0 : ZMod K) = 0 := CongruenceSubgroup.Gamma0_mem.1 h
    refine CongruenceSubgroup.Gamma0_mem.2 ((GamComm.intCast_eq_of_dvd hK h10').symm.trans ?_)
    rw [Int.cast_mul, a, mul_zero]
  have hgam : g * δ⁻¹ ∈ Gam N l :=
    GamComm.mul_inv_mem_Gam N l g δ
      (Subgroup.mem_inf.2 ⟨hg0 N hMN (Subgroup.mem_inf.1 hδ).1, hg0 l hMl (Subgroup.mem_inf.1 hδ).2⟩) hδ
      (GamComm.intCast_eq_of_dvd hMN h00) (GamComm.intCast_eq_of_dvd hMN h11)
  have hdg : CgF X l n (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b) (X.act l (g : Matrix (Fin 2) (Fin 2) ℤ) b) := by
    have h := hact (δ : Matrix (Fin 2) (Fin 2) ℤ) _ _ (hinv _ hgam)
    rw [act_sl, inv_mul_cancel_right] at h
    exact hE.symm h
  have h1 := hgal s _ _ hdg u
  rw [map_sub, sub_eq_zero] at h1 ⊢
  rw [h1]
  have hpol := eval_congr X l w n b t ht hbt _ _
    (StabGal.twist_congr l n M hMn δ g i (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) hc
      (by simpa only [Int.cast_natCast] using hχ) u)
  have hL := hF (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (hF (X.gal s) _ _ hf.symm)
  have hR := hF (X.gal s) _ _ (hF (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (hpol.symm.trans hf.symm))
  refine hR.trans (Eq.trans ?_ hL.symm)
  congr 1
  apply Units.ext
  change X.gal s (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ)) f) = X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ)) (X.gal s f)
  rw [StabGal.toGQ_SL, StabGal.toGQ_SL, hrec]

private theorem polMod_galB [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ)
    (s : Ω ≃ₐ[ℚ] Ω) (t : X.Fn l) (ht : PolMod X l w n t) : PolMod X l w n (X.galB l s t) := by
  obtain ⟨c, hcU, hc⟩ := ht
  obtain ⟨-, -, -, -, hmap, -, hpow⟩ := sCls Ω ε X l n
  obtain ⟨-, -, -, -, -, hgU, hU, -⟩ := sSlD Ω ε X 1 one_pos
  refine ⟨fun i => ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ^ (w - (i : ℕ))) • X.kmap l (X.gal s) (c i),
    fun i => ?_, fun u => ?_⟩
  · obtain ⟨f, hf, hr⟩ := hcU i
    obtain ⟨j, hj⟩ := hpow _ ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ^ (w - (i : ℕ))) _ (hmap (X.gal s) f _ hr)
    refine ⟨_, ?_, hj⟩
    have h0 : Units.map (X.gal s : X.K →* X.K) f ∈ X.Un (l ^ n) := hgU _ s f hf
    clear hj
    induction j with
    | zero => rw [pow_zero]; exact (hU _).1
    | succ k ih => rw [pow_succ]; exact ((hU _).2 _ ih _ h0).1
  · show X.kmap l (X.gal s) (t ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1]) = _
    rw [hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring

end UpperTheory.V.Z.Kato.Nb.GalAct

open UpperTheory.V.Z.Kato.Nb.GalAct in
theorem UpperTheory.V.Z.Kato.Nb.sGalAct :
    UpperTheory.V.Z.Kato.Nb.SGalAct := by
  intro Ω _ _ _ ε X l _ N w n hN s a ha
  have hcomm := comm X l N w n hN s a ha
  obtain ⟨⟨t, ht, hat⟩, hinv, b, hb, hba⟩ := ha
  obtain ⟨hE, -, -, -, -, hact, hgal, -⟩ := sApi Ω ε X l n
  have hba' : CgF X l n b (((l : ℤ_[l]) ^ cL X l N w) • a) := hba
  refine ⟨⟨⟨_, polMod_galB X l w n s t ht, hgal s _ _ hat⟩, fun γ hγ => ?_, X.galB l s b, galB_mem X l N w hN s b hb, ?_⟩,
    fun δ hδ => ⟨⟨⟨_, (sInvApi Ω ε X l N w n).2.2.2.2.2.2.2 _ t
      (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos) ht, hact _ _ _ hat⟩, fun γ hγ => ?_,
      X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b, act_mem X l N w δ hδ b hb, ?_⟩, hcomm δ hδ⟩⟩
  · exact hE.trans (hE.symm (hcomm γ (gam_le N l hγ))) (hgal s _ _ (hinv γ hγ))
  · have h := hgal s _ _ hba'
    rw [map_smul] at h
    exact h
  · rw [act_act_conj]
    exact hact _ _ _ (hinv _ (conj_mem N l γ δ hγ hδ))
  · have h := hact (δ : Matrix (Fin 2) (Fin 2) ℤ) _ _ hba'
    rw [map_smul] at h
    exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.OrbitSum
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

noncomputable section

namespace UpperTheory.V.Z.Kato.Nb

private theorem orbit_sum {G V : Type} [Group G] [Fintype G] [AddCommMonoid V] (K : Subgroup G) (S : Finset G)
    (hS : ∀ m ∈ S, ∀ k ∈ K, m * k ∈ S) (T : G → V) (Q : V → Prop)
    (hsum : ∀ (ι : Type) (s : Finset ι) (a : ι → V), (∀ i ∈ s, Q (a i)) → Q (∑ i ∈ s, a i))
    (ho : ∀ m ∈ S, Q (∑ k : K, T (m * k))) : Q (∑ m ∈ S, T m) := by
  rw [← Finset.sum_fiberwise S (fun m => (QuotientGroup.mk m : G ⧸ K)) T]
  refine hsum _ _ _ fun q _ => ?_
  by_cases h : ∃ m ∈ S, (QuotientGroup.mk m : G ⧸ K) = q
  · obtain ⟨m, hm, rfl⟩ := h
    have e : ∑ k : K, T (m * k) = ∑ i ∈ S with (QuotientGroup.mk i : G ⧸ K) = QuotientGroup.mk m, T i := by
      refine Finset.sum_bij (fun k _ => m * (k : G)) ?_ ?_ ?_ ?_
      · intro k _
        exact Finset.mem_filter.2 ⟨hS m hm k k.2, QuotientGroup.mk_mul_of_mem m k.2⟩
      · intro k _ k' _ hk
        exact Subtype.ext (mul_left_cancel hk)
      · intro i hi
        refine ⟨⟨m⁻¹ * i, QuotientGroup.eq.1 (Finset.mem_filter.1 hi).2.symm⟩, Finset.mem_univ _, by simp⟩
      · intro k _; rfl
    rw [← e]; exact ho m hm
  · rw [Finset.filter_eq_empty_iff.2 fun m hm e => h ⟨m, hm, e⟩]
    exact hsum _ _ _ fun i hi => absurd hi (Finset.notMem_empty i)

private def rho (M : ℕ) : SL(2, ℤ) →* GL (Fin 2) (ZMod M) :=
  Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)))

private theorem rho_coe (M : ℕ) (γ : SL(2, ℤ)) :
    (rho M γ : Matrix (Fin 2) (Fin 2) (ZMod M)) = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) := rfl

private theorem rho_det (M : ℕ) (γ : SL(2, ℤ)) : Matrix.GeneralLinearGroup.det (rho M γ) = 1 := by
  ext
  exact (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ).2

private theorem rho_one (M : ℕ) (γ : SL(2, ℤ)) : rho M γ = 1 ↔ γ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem']
  constructor
  · intro h
    exact Subtype.ext (congrArg Units.val h)
  · intro h
    simp [rho, h]

private theorem val_mul {M : ℕ} [NeZero M] (k : ℕ) (h : k ∣ M) (m : GL (Fin 2) (ZMod M)) (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((((m * rho M γ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) i j).val : ZMod k) =
      (((m : Matrix (Fin 2) (Fin 2) (ZMod M)) i 0).val : ZMod k) * (γ 0 j : ℤ) +
        (((m : Matrix (Fin 2) (Fin 2) (ZMod M)) i 1).val : ZMod k) * (γ 1 j : ℤ) := by
  have hv : ∀ z : ZMod M, (z.val : ZMod k) = ZMod.castHom h (ZMod k) z := fun z => by
    rw [ZMod.natCast_val, ZMod.castHom_apply]
  rw [hv, hv, hv, Units.val_mul, rho_coe, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.map_apply, eq_intCast, map_add (f := _), map_mul, map_intCast]

private theorem cnd_mul {l N M : ℕ} [NeZero M] (hN : N ∣ M) (hl : l ∣ M) (g : SL(2, ℤ)) (m : GL (Fin 2) (ZMod M))
    (hm : Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M))) (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) :
    Cnd l N g ((m * rho M γ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
  obtain ⟨h1, h2⟩ := hγ
  have h1 := (CongruenceSubgroup.Gamma1_mem N γ).1 h1
  have h2 : ((γ 1 0 : ℤ) : ZMod l) = 0 := CongruenceSubgroup.Gamma0_mem.1 h2
  obtain ⟨a, b, c⟩ := hm
  refine ⟨?_, ?_, ?_⟩
  · rw [val_mul N hN, a, h1.2.2]; simp
  · rw [val_mul N hN, b, h1.1, h1.2.2]; simp
  · rw [val_mul l hl, val_mul l hl, h2]
    linear_combination ((γ 0 0 : ℤ) : ZMod l) * c

private theorem gam_le {l n N M : ℕ} (hN : N ∣ M) (hl : l ∣ M) (hn : l ^ n ∣ M) :
    CongruenceSubgroup.Gamma M ≤ Gam N l ⊓ CongruenceSubgroup.Gamma (l ^ n) := by
  have key : ∀ k, k ∣ M → CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma k := by
    intro k hk γ hγ
    rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
    obtain ⟨a, b, c, d⟩ := hγ
    have a := congrArg (ZMod.castHom hk (ZMod k)) a
    have b := congrArg (ZMod.castHom hk (ZMod k)) b
    have c := congrArg (ZMod.castHom hk (ZMod k)) c
    have d := congrArg (ZMod.castHom hk (ZMod k)) d
    simp only [map_intCast, map_one, map_zero] at a b c d
    exact ⟨a, b, c, d⟩
  intro γ hγ
  have h1 := CongruenceSubgroup.Gamma_mem.1 (key N hN hγ)
  have h2 := CongruenceSubgroup.Gamma_mem.1 (key l hl hγ)
  exact ⟨⟨(CongruenceSubgroup.Gamma1_mem N γ).2 ⟨h1.1, h1.2.2.2, h1.2.2.1⟩, CongruenceSubgroup.Gamma0_mem.2 h2.2.2.1⟩,
    key _ hn hγ⟩

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private def FU (X : Tower Ω ε) (N M₀ : ℕ) {M : ℕ} (x y : Row M₀) (a : Fam X M₀) (m : GL (Fin 2) (ZMod M)) : X.Kˣ :=
  slU X (toGQ !![(N : ℤ), 0; 0, 1]) (a (x ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M)))
    (y ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))))

private theorem FU_act (X : Tower Ω ε) {k N M₀ M : ℕ} [NeZero N] [NeZero M₀] [NeZero M] (hM : M = N * M₀)
    (x y : Row M₀) (hxy : Ok x y) (a : Fam X M₀) (ha : Eqv X k M₀ a) (m : GL (Fin 2) (ZMod M))
    (hm : (((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 1 0).val : ZMod N) = 0) :
    FU X N M₀ x y a m ∈ X.Un k ∧ ∀ γ : SL(2, ℤ), ((γ 1 0 : ℤ) : ZMod N) = 0 →
      Cgr k (slU X (ofSL γ) (FU X N M₀ x y a m)) (FU X N M₀ x y a (m * rho M γ)) := by
  obtain ⟨c1, -, c2, c3⟩ := sCdFacts N M₀ M hM
  obtain ⟨-, s1, s2, -, s3, -⟩ := sSlD Ω ε X N (NeZero.pos N)
  obtain ⟨e1, e2⟩ := ha _ _ (c2 m hm x y hxy)
  refine ⟨s3 _ _ _ e1, fun γ hγ => ?_⟩
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rwa [Matrix.det_fin_two] at this
  let γ' : SL(2, ℤ) := ⟨!![γ 0 0, N * γ 0 1; t, γ 1 1], by
    rw [Matrix.det_fin_two_of]; rw [ht] at hdet; linear_combination hdet⟩
  have hc : !![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [γ', Matrix.mul_apply, Fin.sum_univ_two, ht, mul_comm]
  have hN : N ∣ M := ⟨_, hM⟩
  have hr : (((rho M γ : Matrix (Fin 2) (Fin 2) (ZMod M)) 1 0).val : ZMod N) = 0 := by
    have := val_mul N hN 1 γ 1 0
    rw [one_mul] at this
    rw [this, hγ]; simp
  have hcd : cD N M₀ ((m * rho M γ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) =
      cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M)) * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M₀)) := by
    rw [Units.val_mul, c1 _ _ hm hr, rho_coe, c3 _ _ hc]
  obtain ⟨h, hh⟩ := e2 γ'
  refine ⟨slU X (toGQ !![(N : ℤ), 0; 0, 1]) h, ?_⟩
  unfold FU
  rw [hcd, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← map_pow, ← map_mul]
  unfold rt at hh
  rw [← hh]
  ext
  have := s1 _ _ (by rw [γ.2]; exact one_pos) hc
    (a (x ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) (y ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) : X.K)
  rw [s2, s2] at this
  exact this

private def lamOf {M : ℕ} (m : GL (Fin 2) (ZMod M)) : Fin 2 → ℤ :=
  fun j => (((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 j).val : ℤ)

private theorem sec_act (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {n M : ℕ} [NeZero M] (w : ℕ) (hn : l ^ n ∣ M)
    (m : GL (Fin 2) (ZMod M)) (γ : SL(2, ℤ)) (f f' : X.Kˣ) (hf : Cgr (l ^ n) (slU X (ofSL γ) f) f') :
    CgF X l n (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (sec X l w (lamOf m) (clsK X l n (f : X.K))))
      (sec X l w (lamOf (m * rho M γ)) (clsK X l n (f' : X.K))) := by
  obtain ⟨-, -, -, -, a1, -⟩ := sApi Ω ε X l n
  obtain ⟨c1, -, -, c2, c3, -⟩ := sCls Ω ε X l n
  obtain ⟨-, -, s2, -⟩ := sSlD Ω ε X 1 one_pos
  intro u
  have hd : ∀ j, (l : ℤ_[l]) ^ n ∣ ((lamOf m 0 * γ 0 j + lamOf m 1 * γ 1 j - lamOf (m * rho M γ) j : ℤ) : ℤ_[l]) := by
    intro j
    have h : ((lamOf m 0 * γ 0 j + lamOf m 1 * γ 1 j - lamOf (m * rho M γ) j : ℤ) : ZMod (l ^ n)) = 0 := by
      have := val_mul (l ^ n) hn m γ 0 j
      simp only [lamOf, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast]
      rw [this, sub_self]
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h
    exact ⟨t, by rw [ht]; push_cast; rfl⟩
  have hk := c2 _ _ _ _ (c3 (X.sl (ofSL γ)).toRingEquiv f _ (c1 f)) (c1 f') hf
  set A := X.kmap l (X.sl (ofSL γ)).toRingEquiv (clsK X l n (f : X.K)) with hA
  set B := clsK X l n (f' : X.K)
  set k : ℤ_[l] := (lamOf m 0 : ℤ_[l]) * (mZl l γ *ᵥ u) 0 + (lamOf m 1 : ℤ_[l]) * (mZl l γ *ᵥ u) 1 with hk1
  set k' : ℤ_[l] := (lamOf (m * rho M γ) 0 : ℤ_[l]) * u 0 + (lamOf (m * rho M γ) 1 : ℤ_[l]) * u 1 with hk2
  have hkk : (l : ℤ_[l]) ^ n ∣ k ^ w - k' ^ w := by
    refine dvd_trans ?_ (sub_dvd_pow_sub_pow k k' w)
    have := dvd_add (Dvd.dvd.mul_right (hd 0) (u 0)) (Dvd.dvd.mul_right (hd 1) (u 1))
    convert this using 1
    simp only [hk1, hk2, mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, eq_intCast]
    push_cast
    ring
  have e : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (sec X l w (lamOf m) (clsK X l n (f : X.K))) u -
      sec X l w (lamOf (m * rho M γ)) B u = (k ^ w • A - k' ^ w • A) + k' ^ w • (A - B) := by
    show X.kmap l (X.sl (toGQ γ)).toRingEquiv (k ^ w • clsK X l n (f : X.K)) - k' ^ w • B = _
    rw [s2, map_smul, ← hA, smul_sub]; abel
  rw [e, map_add (f := _), a1 _ _ _ hkk, map_smul, hk, smul_zero, add_zero]

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sXiInv :
    UpperTheory.V.Z.Kato.Nb.SXiInv := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL hW x y hxy P a ha
  have hN : N ∣ M := ⟨_, hL.eq⟩
  have hn : l ^ n ∣ M := hL.eq ▸ Dvd.dvd.mul_left hL.dl N
  have hl : l ∣ M := (dvd_pow_self l (Nat.one_le_iff_ne_zero.1 hL.pos)).trans hn
  obtain ⟨-, -, i1, i2, i3, -⟩ := sInvApi Ω ε X l N w n
  obtain ⟨eqv, -, a1, a2, -⟩ := sApi Ω ε X l n
  obtain ⟨c1, -⟩ := sCls Ω ε X l n
  let T : GL (Fin 2) (ZMod M) → X.Fn l := fun m =>
    ((((Matrix.GeneralLinearGroup.det m)⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ_[l]) •
      sec X l w (lamOf m) (clsK X l n (FU X N M₀ x y a m : X.K))
  have hX : Xi X l n N M₀ M w g x y P a = ∑ m ∈ Finset.univ.filter (fun m : GL (Fin 2) (ZMod M) =>
      Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)) ∧ P (Matrix.GeneralLinearGroup.det m)), T m := by
    funext u
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [T, Pi.smul_apply, sec, lamOf, Int.cast_natCast, smul_smul]
    rfl
  rw [hX]
  refine orbit_sum ((Gam N l).map (rho M)) _ ?_ T (InvM X l N w n) i3 ?_
  · rintro m hm _ ⟨γ, hγ, rfl⟩
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨Finset.mem_univ _, cnd_mul hN hl g m hm.2.1 γ hγ, by rw [map_mul, rho_det, mul_one]; exact hm.2.2⟩
  · intro m hm
    obtain ⟨u1, u2⟩ := FU_act X hL.eq x y hxy a ha m (Finset.mem_filter.1 hm).2.1.1
    have h10 : ∀ γ ∈ Gam N l, ((γ 1 0 : ℤ) : ZMod N) = 0 := fun γ hγ => ((CongruenceSubgroup.Gamma1_mem N γ).1 hγ.1).2.2
    choose γ hγ hr using fun k : (Gam N l).map (rho M) => k.2
    have hle := gam_le hN hl hn
    have htr : IsTr (CongruenceSubgroup.Gamma M) (Gam N l) γ := by
      refine ⟨hγ, fun δ hδ => ⟨⟨rho M δ, δ, hδ, rfl⟩, ?_, fun k hk => ?_⟩⟩
      · show _ ∈ _
        rw [← rho_one, map_mul, map_inv, hr, mul_inv_cancel]
      · have hk : _ ∈ _ := hk
        rw [← rho_one, map_mul, map_inv, hr, mul_inv_eq_one] at hk
        exact Subtype.ext hk.symm
    have hinv : InvH X (CongruenceSubgroup.Gamma M) (l ^ n) (FU X N M₀ x y a m) := by
      intro δ hδ
      obtain ⟨h, hh⟩ := u2 δ (h10 δ (hle hδ).1)
      rw [(rho_one M δ).2 hδ, mul_one] at hh
      have h2 := congrArg Units.val hh
      rw [Units.val_mul, Units.val_pow_eq_pow_val] at h2
      exact ⟨h, h2⟩
    obtain ⟨t1, t2, -⟩ := trc ε X l N w n _ hle _ γ htr (lamOf m) _ _ (c1 (FU X N M₀ x y a m))
    have hI : InvM X l N w n (trH X l w γ (lamOf m) (clsK X l n (FU X N M₀ x y a m : X.K))) :=
      ⟨⟨_, t1 u1, eqv.refl _⟩, t2 hinv, hW n _ M (NeZero.pos M) le_rfl hle _ γ htr _ _ _ u1 hinv (c1 _)⟩
    refine i2 _ _ ?_ (i1 ((((Matrix.GeneralLinearGroup.det m)⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ_[l]) _ hI)
    unfold trH
    rw [Finset.smul_sum]
    refine a2 _ _ _ _ fun k _ => ?_
    rw [← hr k]
    simp only [T]
    rw [map_mul, rho_det, mul_one]
    exact a1 _ _ _ (eqv.symm (sec_act X l w hn m (γ k) _ _ (u2 _ (h10 _ (hγ k)))))

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvCg
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

private theorem sadd {l : ℕ} [Fact l.Prime] {δ : ℝ} {a b : Qbar l} (ha : ‖a‖ ≤ δ) (hb : ‖b‖ ≤ δ) : ‖a + b‖ ≤ δ :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

private theorem smul' {l : ℕ} [Fact l.Prime] {δ : ℝ} {a b : Qbar l} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ δ) : ‖a * b‖ ≤ δ := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans hb

private theorem shift {l : ℕ} [Fact l.Prime] {U : Type} [CommGroup U] [Fintype U] {δ : ℝ} (hδ : 0 ≤ δ) (η F : U → Qbar l) (t : U)
    (c : Qbar l) (h : ∀ y, ‖η (y * t) - η y * c‖ ≤ δ) (hF : ∀ y, ‖F y‖ ≤ 1) :
    ‖∑ y, η y * F (y * t⁻¹) - c * ∑ y, η y * F y‖ ≤ δ := by
  have e : ∑ y, η y * F (y * t⁻¹) = ∑ y, η (y * t) * F y :=
    (Fintype.sum_equiv (Equiv.mulRight t) _ _ fun y => by simp).symm
  rw [e, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hδ fun y _ => ?_
  have : η (y * t) * F y - c * (η y * F y) = F y * (η (y * t) - η y * c) := by ring
  rw [this]
  exact smul' (hF y) (h y)

private theorem unit_of {l r : ℕ} [hl : Fact l.Prime] (hr : r ≠ 0) (y : (ZMod (l ^ r))ˣ) :
    ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) = ((y : ZMod (l ^ r)).val : ℕ) := by
  have h := Nat.Coprime.coprime_dvd_right (dvd_pow_self l hr) (ZMod.val_coe_unit_coprime y)
  have : IsUnit (((y : ZMod (l ^ r)).val : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact h.symm
  exact this

private theorem inv_cg {l r : ℕ} [hl : Fact l.Prime] (c : Coef l) (hr : r ≠ 0) (e : ℕ) (y t : (ZMod (l ^ r))ˣ) (τ : ℤ_[l]ˣ)
    (h : PadicInt.toZModPow r (τ : ℤ_[l]) = t) :
    ‖((((((y * t : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : ℕ) : Qbar l)) ^ e)⁻¹ -
      (((((y : ZMod (l ^ r)).val : ℕ) : Qbar l)) ^ e)⁻¹ * ((algebraMap ℤ_[l] (Qbar l) τ) ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  obtain ⟨u, hu⟩ := unit_of hr (y * t)
  obtain ⟨v, hv⟩ := unit_of hr y
  have h1 : (l : ℤ_[l]) ^ r ∣ ((v * τ : ℤ_[l]ˣ) : ℤ_[l]) - u := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, Units.val_mul, map_mul, hu, hv, h,
      map_natCast, map_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, Units.val_mul, sub_self]
  obtain ⟨k, hk⟩ := h1.trans (sub_dvd_pow_sub_pow _ _ e)
  have inv : ∀ w : ℤ_[l]ˣ, (algebraMap ℤ_[l] (Qbar l) w ^ e)⁻¹ = algebraMap ℤ_[l] (Qbar l) ((w⁻¹ : ℤ_[l]ˣ) ^ e) := fun w => by
    apply inv_eq_of_mul_eq_one_right
    rw [← map_pow, ← map_mul, ← mul_pow, Units.mul_inv, one_pow, map_one]
  rw [← map_natCast (algebraMap ℤ_[l] (Qbar l)) (ZMod.val _), ← map_natCast (algebraMap ℤ_[l] (Qbar l)) (ZMod.val _), ← hu, ← hv,
    inv, inv, inv, ← map_mul, ← map_sub]
  have e1 : ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e - ((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e * ((τ⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e =
      (k * ((u⁻¹ * (v * τ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e) * (l : ℤ_[l]) ^ r := by
    have a1 : ((u⁻¹ * (v * τ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e * ((v * τ : ℤ_[l]ˣ) : ℤ_[l]) ^ e = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e := by
      rw [← mul_pow, ← Units.val_mul, inv_mul_cancel_right]
    have a2 : ((u⁻¹ * (v * τ)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e * (u : ℤ_[l]) ^ e =
        ((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e * ((τ⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ e := by
      rw [← mul_pow, ← mul_pow, ← Units.val_mul, ← Units.val_mul, mul_comm u⁻¹, inv_mul_cancel_right, mul_inv]
    rw [← a1, ← a2, ← mul_sub, hk]; ring
  rw [e1, map_mul, map_pow, map_natCast]
  exact smul' (nle c (c.O.algebraMap_mem _)) le_rfl

theorem UpperTheory.V.Z.Kato.Nb.sSpec :
    UpperTheory.V.Z.Kato.Nb.SSpec := by
  intro l hl Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he hW p r hp hlp a δ k ha hδ hk Y V b hY hb H
  obtain ⟨hθ, h1, hmul, hψ, hρ, -, -⟩ := sInteg l Ω ι e gN A W ε X pr N x c d gm ψ cf hA he hW
  rcases eq_or_ne r 0 with rfl | hr
  · refine ⟨0, fun i => zero_mem _, fun s i => ?_⟩
    have z : ∀ y : (ZMod (l ^ 0))ˣ, (y : ZMod (l ^ 0)).val = 0 := fun y =>
      Nat.lt_one_iff.1 (by simpa using ZMod.val_lt (y : ZMod (l ^ 0)))
    simp only [Cg, spec, z, Nat.cast_zero, zero_pow (show e ≠ 0 by omega), inv_zero, zero_mul, zero_smul, Finset.sum_const_zero]
    simp
  have hS := (sSlD Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))).2.2.2.2.2.2.2
  let rd : (ZMod (l ^ r))ˣ →* (ZMod l)ˣ := Units.map (ZMod.castHom (dvd_pow_self l hr) (ZMod l)).toMonoidHom
  have hrd : ∀ y, chiK l ψ r y = ψ (rd y : (ZMod l)ˣ) := fun y => by
    rw [chiK, ZMod.natCast_val]; rfl
  set η : (ZMod (l ^ r))ˣ → Qbar l := fun x => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x with hη
  have uO : ∀ w : ℤ_[l]ˣ, (algebraMap ℤ_[l] (Qbar l) w)⁻¹ ∈ cf.O := fun w => by
    rw [show (algebraMap ℤ_[l] (Qbar l) w)⁻¹ = algebraMap ℤ_[l] (Qbar l) (w⁻¹ : ℤ_[l]ˣ) from
      inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])]
    exact cf.O.algebraMap_mem _
  have ηO : ∀ y, η y ∈ cf.O := fun y => by
    obtain ⟨u, hu⟩ := unit_of hr y
    simp only [hη]
    rw [← map_natCast (algebraMap ℤ_[l] (Qbar l)), ← hu, ← inv_pow, hrd]
    exact mul_mem (pow_mem (uO u) e) (hψ _)
  have key : ∀ (t : (ZMod (l ^ r))ˣ) (τ : ℤ_[l]ˣ), PadicInt.toZModPow r (τ : ℤ_[l]) = t → ∀ y,
      ‖η (y * t) - η y * (((algebraMap ℤ_[l] (Qbar l) τ) ^ e)⁻¹ * ψ (rd t : (ZMod l)ˣ))‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := fun t τ h y => by
    simp only [hη]
    rw [hrd, hrd, map_mul, hmul]
    have := smul' (nle cf (mul_mem (hψ (rd y)) (hψ (rd t)))) (inv_cg cf hr e y t τ h)
    convert this using 2
    ring
  have hp1 : (p : ZMod l) = 1 := by
    obtain ⟨m, hm⟩ := hlp
    rw [show p = l * m + 1 by have := hp.pos; omega]
    simp
  have hcop : Nat.Coprime l p := by
    rw [Nat.Prime.coprime_iff_not_dvd hl.out, ← ZMod.natCast_eq_zero_iff, hp1]
    exact one_ne_zero
  obtain ⟨π, hπ⟩ : IsUnit (p : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]; exact hcop
  have hq : IsUnit (p : ZMod (l ^ r)) := (ZMod.isUnit_iff_coprime _ _).2 (hcop.symm.pow_right r)
  have hinv : inv1 (l ^ r) p = hq.unit⁻¹ := dif_pos hq
  have hπ' : algebraMap ℤ_[l] (Qbar l) π = p := by rw [hπ, map_natCast]
  have hrq : ((rd hq.unit : (ZMod l)ˣ) : ZMod l) = 1 := by
    rw [← hp1]; exact map_natCast (ZMod.castHom (dvd_pow_self l hr) (ZMod l)) p
  have k1 := key hq.unit π (by rw [hπ, map_natCast]; rfl)
  have k2 := key (hq.unit ^ 2) (π ^ 2) (by rw [Units.val_pow_eq_pow_val, map_pow, hπ, map_natCast]; rfl)
  rw [hπ', hrq, h1] at k1
  rw [Units.val_pow_eq_pow_val, map_pow, hπ', map_pow, Units.val_pow_eq_pow_val, hrq, one_pow, h1] at k2
  have hpO : (p : Qbar l)⁻¹ ∈ cf.O := hπ' ▸ uO π
  have hp0 : (p : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpn : ‖(p : Qbar l)‖ ≤ 1 := nle cf (natCast_mem _ p)
  refine ⟨fun i => (p : Qbar l)⁻¹ * ∑ y, η y * b y i, fun i => mul_mem hpO (sum_mem fun y _ => mul_mem (ηO y) (hb y i)), fun s i => ?_⟩
  have k3 := key (cycMod ℚ Ω l r s) (cycZ ℚ Ω l s) rfl
  have hth : ((algebraMap ℤ_[l] (Qbar l) (cycZ ℚ Ω l s : ℤ_[l]ˣ)) ^ e)⁻¹ * ψ (rd (cycMod ℚ Ω l r s) : (ZMod l)ˣ) = thK l e ψ s := by
    have a1 : rd (cycMod ℚ Ω l r s) = cycM l s := by
      rw [(sCycZ Ω l r s).1]; exact (hS (l ^ r) s).2.2.2.2 l (dvd_pow_self l hr)
    have a2 := (hS (l ^ 1) s).2.2.2.2 l (dvd_pow_self l one_ne_zero)
    rw [← (sCycZ Ω l 1 s).1] at a2
    rw [a1, ← a2, thK, ZMod.natCast_val]; rfl
  rw [hth] at k3
  have h0 := norm_nonneg (((l : ℕ) : Qbar l) ^ r)
  have s1 := shift h0 η (fun y => Y s y i) _ _ k1 fun y => hY s y i
  have s2 := shift h0 η (fun y => Y s y i) _ _ k2 fun y => hY s y i
  have s3 := fun j => shift h0 η (fun y => b y j) _ _ k3 fun y => nle cf (hb y j)
  have s0 := IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (s := Finset.univ) h0 fun y _ => smul' (nle cf (ηO y)) (H s y i)
  have hθ0 : thK l e ψ s ≠ 0 := fun h => by simpa [h] using hθ s
  have hWρ : ∀ j, mat W s i j = thK l e ψ s * rhoK W e ψ s i j := fun j => by
    rw [rhoK, Matrix.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hθ0]
  have E : ∑ y, η y * (((p : Qbar l) • V s y) i - (k • ((p : Qbar l) • Y s y - a • Y s (y * inv1 (l ^ r) p) +
          ((p : Qbar l) ^ (2 * e - 1) * δ) • Y s (y * inv1 (l ^ r) p ^ 2)) +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y)) i) =
      p * ∑ y, η y * V s y i - (k * (p * ∑ y, η y * Y s y i - a * ∑ y, η y * Y s (y * hq.unit⁻¹) i +
        ((p : Qbar l) ^ (2 * e - 1) * δ) * ∑ y, η y * Y s (y * (hq.unit ^ 2)⁻¹) i) +
        (rhoK W e ψ s i 0 * ∑ y, η y * b (y * (cycMod ℚ Ω l r s)⁻¹) 0 + rhoK W e ψ s i 1 * ∑ y, η y * b (y * (cycMod ℚ Ω l r s)⁻¹) 1 -
          ∑ y, η y * b y i)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [hinv, inv_pow, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [E] at s0
  have fin := smul' (nle cf hpO) (sadd (sadd (sadd (sadd s0 (smul' (a := -(k * a)) (by rw [norm_neg]; exact smul' hk ha) s1))
    (smul' (a := k * ((p : Qbar l) ^ (2 * e - 1) * δ)) (smul' hk (smul' (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hpn) hδ)) s2))
    (smul' (nle cf (hρ s i 0)) (s3 0))) (smul' (nle cf (hρ s i 1)) (s3 1)))
  unfold Cg
  convert fin using 2
  simp only [spec, eul, Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, hWρ]
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  rw [show 2 * (e' + 1) - 1 = 2 * e' + 1 by omega]
  field_simp
  ring
end
