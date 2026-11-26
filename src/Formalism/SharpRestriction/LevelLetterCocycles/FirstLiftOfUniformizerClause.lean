module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionRingAll

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.FirstLiftOfHypotheses
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.InvariantLetterIdempotentSmul
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.MultVNonneg
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Pass

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem finiteDimensional_filLev (c : ZMod n) (hfd : FiniteDimensional LL ↥(DcrisL PD T.ρ (W.emb c))) (u : ℤ) :
    FiniteDimensional LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 u) := by
  have hc : c - ((0 : ℕ) : ZMod n) = c := by simp
  haveI : FiniteDimensional LL
      ↥(Formalism.WeaklyAdmissibleFiltrations.FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb (c - ((0 : ℕ) : ZMod n)))) := by
    rw [hc]
    exact Submodule.finiteDimensional_of_le inf_le_right
  unfold Formalism.MainNotions.WachCoordinates.FilLev
  infer_instance

theorem multV_nonneg' [NeZero n] (hFD : Sh.FilDim W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hT : IsCrys PD T.ρ) (c : ZMod n) (τ : K →ₐ[Qp] LL) (hτ : Formalism.MainNotions.LiftingTheory.Over W τ c)
    (hfd : FiniteDimensional LL ↥(DcrisL PD T.ρ (W.emb c))) (k : ℤ) : 0 ≤ multV PD T.ρ τ k := by
  obtain ⟨-, hdim⟩ := hFD hA T hT c τ hτ
  have h1 := hdim k (k + 1) (by omega)
  have hI : Finset.Ico k (k + 1) = {k} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [hI, Finset.sum_singleton] at h1

  have hle : Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (k + 1) ≤ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 k := by
    unfold Formalism.MainNotions.WachCoordinates.FilLev
    apply Submodule.map_mono
    apply Submodule.map_mono
    apply inf_le_inf_right
    unfold Formalism.WeaklyAdmissibleFiltrations.FilCris
    apply inf_le_inf_left
    apply Submodule.comap_mono
    unfold Formalism.WeaklyAdmissibleFiltrations.FilV
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    clear hx
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      exact LinearMap.mem_range.mpr ⟨v ⊗ₜ ⟨(w : BdR), PD.Fil_anti k w.2⟩, by simp⟩
    | add y z hy hz =>
      rw [map_add (f := _)]
      exact add_mem hy hz
  haveI := finiteDimensional_filLev W T c hfd k
  have h2 : Module.finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (k + 1)) ≤
      Module.finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 k) :=
    LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)
  have h3 : ((Module.finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (k + 1)) : ℕ) : ℤ) ≤
      Module.finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 k) := by exact_mod_cast h2
  linarith

theorem sum_multV_le [NeZero n] (hFD : Sh.FilDim W) {d : ℕ} {T₁ T₂ : LocLat G Qp LL O}
    {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ} (hS : SetCS W d T₁ T₂ F b S η m)
    (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (c : ZMod n) (hc : c ∈ evens n d) (τ : K →ₐ[Qp] LL)
    (hτ : Formalism.MainNotions.LiftingTheory.Over W τ c) (a : ℕ) (ha : a < b c) :
    ∑ k ∈ Finset.Ico (-(a : ℤ)) 0, multV PD T₂.ρ τ k ≤ (m : ℤ) := by
  have hjump := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS c τ hτ
  have hfd := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fd_letter₂ W hS c
  have hT₂ : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hev : (c.val + d) % 2 = 0 := by simpa [evens] using hc
  rw [← Finset.sum_filter_of_ne (p := fun k => k ∈ Finset.Icc (-(η : ℤ)) η)]
  · calc ∑ k ∈ (Finset.Ico (-(a : ℤ)) 0).filter (fun k => k ∈ Finset.Icc (-(η : ℤ)) η), multV PD T₂.ρ τ k
        ≤ ∑ k ∈ Finset.Icc (-(η : ℤ)) η, multV PD T₂.ρ τ k :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => (Finset.mem_filter.1 hk).2)
            (fun k _ _ => multV_nonneg' W T₂ hFD hS.1 hT₂ c τ hτ hfd k)
      _ ≤ (m : ℤ) := hS.2.2.2.2.2.2.2.1 c τ hτ
  · intro k hk hne
    have hj : IsJumpV PD T₂.ρ τ k := by
      by_contra hnj
      exact hne (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_multV_of_not_jump PD T₂.ρ τ k hnj)
    have hw := hjump k hj
    simp only [Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS, hev, if_true, Set.mem_union, Set.mem_Icc] at hw
    have hk' := Finset.mem_Ico.1 hk
    simp only [Finset.mem_Icc]
    omega

theorem step1Pass_pass [NeZero n] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hT : IsCrys PD T.ρ) (ζ : LL)
    (hζ : IsPrimitiveRoot ζ PD.p) (hEx : Sh.ExpRules W) (hER : Sh.ExpRing W) (hK : Sh.LemK W)
    (hFD : Sh.FilDim W) (c : ZMod n) (τ : K →ₐ[Qp] LL) (hτ : Formalism.MainNotions.LiftingTheory.Over W τ c)
    (hfd : FiniteDimensional LL ↥(DcrisL PD T.ρ (W.emb c))) [IsDomain O] [IsPrincipalIdealRing O]
    [IsFractionRing O LL] {FF : Type} [AddCommGroup FF] [Module O FF] [Module.Finite O FF]
    (u : FF →ₗ[O] W.DD T) (a m : ℕ)
    (hu : ∀ f, Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (u f) ∧ Formalism.MainNotions.LiftingTheory.qp W ^ a • u f ∈ W.N T ∧
      Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 (W.γ T (u f) - u f))
    (hdim : ∑ k ∈ Finset.Ico (-(a : ℤ)) 0, multV PD T.ρ τ k ≤ (m : ℤ)) :
    (∀ (lenO : ℕ∞) (cc : ℝ) (A : Submodule O FF),
      ∃ B, PChain lenO m cc A B 1 0 ∧ ∀ f ∈ B, u f ∈ W.N T) ∧ (m = 0 → ∀ f, u f ∈ W.N T) := by
  have hlev : W.lev c ζ (Formalism.MainNotions.LiftingTheory.qp W ^ a) ≠ 0 := by
    obtain ⟨⟨w, hw, hq⟩, -, -⟩ := hER hA c ζ hζ
    rw [map_pow, hq, mul_pow]
    exact mul_ne_zero (pow_ne_zero _ hw.ne_zero) (pow_ne_zero _ PowerSeries.X_ne_zero)
  have R := hEx hA T hT c ζ hζ
  have hex : ∀ f, ∃! d, Sh.IsExp W T c ζ (u f) d := fun f => R.1 (u f) _ (hu f).2.1 hlev
  choose ex hexs huniq using hex
  have ex_add : ∀ f g, ex (f + g) = ex f + ex g := fun f g =>
    (huniq (f + g) _ (by rw [map_add (f := _)]; exact R.2.2.1 _ _ _ _ (hexs f) (hexs g))).symm
  have ex_smul : ∀ (r : O) f, ex (r • f) = fun k => algebraMap O LL r • ex f k := fun r f =>
    (huniq (r • f) _ (by rw [map_smul]; exact R.2.2.2.1 r _ _ (hexs f))).symm
  set F0 := Formalism.MainNotions.WachCoordinates.FilLev W T c 0 0 with hF0
  set Fa := Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-(a : ℤ)) with hFa
  let φ : FF →+ (T.V ⊗[Qp] BdR) ⧸ F0 :=
    AddMonoidHom.mk' (fun f => Submodule.Quotient.mk (ex f 0)) (fun f g => by
      simp only [ex_add, Pi.add_apply, Submodule.Quotient.mk_add])
  have hφ : ∀ (r : O) f, φ (r • f) = algebraMap O LL r • φ f := by
    intro r f
    simp only [φ, AddMonoidHom.mk'_apply, ex_smul, Submodule.Quotient.mk_smul]
  have hLK : ∀ f, ex f 0 ∈ Fa ∧ (u f ∈ W.N T ↔ ex f 0 ∈ F0) := by
    intro f
    have hj : ∃ j : ℕ, ((PD.p : ℕ) : O) ^ j • (W.γ T (u f) - u f) ∈ W.N T := by
      obtain ⟨y, hy, -, he⟩ := (hu f).2.2
      exact ⟨0, by rw [pow_zero, one_smul, he]; exact (W.N T).smul_mem _ hy⟩
    exact (hK hA T hT c ζ hζ (u f) (ex f) (hu f).1 (hexs f) hj).2 a (hu f).2.1
  have hker : ∀ f, φ f = 0 ↔ u f ∈ W.N T := by
    intro f
    rw [(hLK f).2]
    exact Submodule.Quotient.mk_eq_zero _
  have := finiteDimensional_filLev W T c hfd (-(a : ℤ))
  have := finiteDimensional_filLev W T c hfd 0
  let Aq := Fa.map F0.mkQ
  have hle : F0 ≤ Fa := Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T c 0 (by omega : -(a : ℤ) ≤ 0)
  have hAq : finrank LL ↥Aq ≤ m := by
    let g := F0.mkQ ∘ₗ Fa.subtype
    have hr : LinearMap.range g = Aq := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hk : LinearMap.ker g = F0.comap Fa.subtype := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    have h1 := LinearMap.finrank_range_add_finrank_ker g
    rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at h1
    have h2 := (hFD hA T hT c τ hτ).2 (-(a : ℤ)) 0 (by omega)
    rw [← hF0, ← hFa] at h2
    omega
  have hrange : ∀ f, φ f ∈ Aq := fun f => Submodule.mem_map_of_mem (hLK f).1
  refine ⟨fun lenO cc A => ?_, fun hm0 f => ?_⟩
  · let φA : ↥A →+ (T.V ⊗[Qp] BdR) ⧸ F0 := φ.comp A.subtype.toAddMonoidHom
    have hφA : ∀ (r : O) (x : ↥A), φA (r • x) = algebraMap O LL r • φA x := fun r x => hφ r x
    have hm : finrank LL ↥(Submodule.span LL (Set.range φA)) ≤ m := by
      have : FiniteDimensional LL ↥Aq := inferInstance
      refine le_trans (Submodule.finrank_mono ?_) hAq
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hrange x
    refine ⟨Formalism.MainNotions.N.Pv.LocalLengthBound.zeroSub A φA hφA,
      Formalism.MainNotions.N.Pv.LocalLengthBound.pchain_of_gen (Formalism.MainNotions.N.Pv.LocalLengthBound.pstep_rank A φA hφA hm), ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (hker _).1 hy
  · subst hm0
    have h0 : Aq = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    have := hrange f
    rw [h0, Submodule.mem_bot] at this
    exact (hker f).1 this

end Pass

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.PadicValNatFactorialSucc
namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

theorem padicValNat_factorial_succ (p : ℕ) [Fact p.Prime] (M : ℕ) :
    padicValNat p (M + 1).factorial = padicValNat p M.factorial + padicValNat p (M + 1) := by
  rw [Nat.factorial_succ, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.add_one_ne_zero M) (Nat.factorial_ne_zero M)]
  omega

theorem padicValNat_sum_Ioc_add_factorial (p : ℕ) [Fact p.Prime] (K M : ℕ) (h : K ≤ M) :
    ∑ k ∈ Finset.Ioc K M, padicValNat p k + padicValNat p K.factorial = padicValNat p M.factorial := by
  induction M, h using Nat.le_induction with
  | base => simp
  | succ M hKM ih =>
    rw [Finset.sum_Ioc_succ_top hKM, padicValNat_factorial_succ]
    omega

theorem digits_sum_le_log (p : ℕ) [Fact p.Prime] (K : ℕ) :
    (p.digits K).sum ≤ (p - 1) * (Nat.log p K + 1) := by
  have hp : p.Prime := Fact.out
  have h1 : (p.digits K).sum ≤ (p.digits K).length * (p - 1) := by
    have := List.sum_le_card_nsmul (p.digits K) (p - 1) (fun x hx => by
      have := Nat.digits_lt_base hp.one_lt hx
      omega)
    simpa using this
  have h2 : (p.digits K).length ≤ Nat.log p K + 1 := by
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · rw [Nat.length_digits p K hp.one_lt hK.ne']
  calc (p.digits K).sum ≤ (p.digits K).length * (p - 1) := h1
    _ ≤ (Nat.log p K + 1) * (p - 1) := Nat.mul_le_mul h2 (le_refl _)
    _ = (p - 1) * (Nat.log p K + 1) := Nat.mul_comm _ _

theorem padicValNat_sum_Ioc_le (p : ℕ) [Fact p.Prime] (K M : ℕ) (h : K ≤ M) :
    (p - 1) * ∑ k ∈ Finset.Ioc K M, padicValNat p k ≤ M - K + (p.digits K).sum := by
  have h2 := padicValNat_sum_Ioc_add_factorial p K M h
  have hM : (p - 1) * padicValNat p M.factorial = M - (p.digits M).sum := by
    simpa only [Nat.padicValNat_def] using (Nat.Prime.sub_one_mul_multiplicity_factorial (n := M) (Fact.out : p.Prime))
  have hK : (p - 1) * padicValNat p K.factorial = K - (p.digits K).sum := by
    simpa only [Nat.padicValNat_def] using (Nat.Prime.sub_one_mul_multiplicity_factorial (n := K) (Fact.out : p.Prime))
  have sM := Nat.digit_sum_le p M
  have sK := Nat.digit_sum_le p K
  have e : (p - 1) * ∑ k ∈ Finset.Ioc K M, padicValNat p k + (p - 1) * padicValNat p K.factorial =
      (p - 1) * padicValNat p M.factorial := by
    rw [← Nat.mul_add, h2]
  omega

theorem padicValInt_sum_le_Ioc (p : ℕ) (Y : Finset ℤ) (K M : ℕ) (hY : ∀ x ∈ Y, K < x.natAbs ∧ x.natAbs ≤ M)
    (hinj : ∀ x ∈ Y, ∀ y ∈ Y, x.natAbs = y.natAbs → x = y) :
    ∑ x ∈ Y, padicValInt p x ≤ ∑ k ∈ Finset.Ioc K M, padicValNat p k := by
  have e : ∑ k ∈ Y.image Int.natAbs, padicValNat p k = ∑ x ∈ Y, padicValInt p x :=
    by
      simpa only [padicValInt, Nat.padicValNat_def] using
        (Finset.sum_image (f := fun k => padicValNat p k) (by intro x hx y hy hxy; exact hinj x hx y hy hxy))
  rw [← e]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  rw [Finset.mem_image] at hk
  obtain ⟨x, hx, rfl⟩ := hk
  rw [Finset.mem_Ioc]
  exact hY x hx

private theorem sub_one_mul_sum_padicValInt_le_sub_add_digits_sum (p : ℕ) [Fact p.Prime] (Y : Finset ℤ) (K M : ℕ) (h : K ≤ M)
    (hY : ∀ x ∈ Y, K < x.natAbs ∧ x.natAbs ≤ M)
    (hinj : ∀ x ∈ Y, ∀ y ∈ Y, x.natAbs = y.natAbs → x = y) :
    (p - 1) * ∑ x ∈ Y, padicValInt p x ≤ M - K + (p.digits K).sum :=
  le_trans (Nat.mul_le_mul (le_refl _) (padicValInt_sum_le_Ioc p Y K M hY hinj))
    (padicValNat_sum_Ioc_le p K M h)

theorem padicValInt_sum_le (p : ℕ) [Fact p.Prime] (bb S η a : ℕ) (hab : a + η < bb) (X : Finset ℤ)
    (hX : ∀ x ∈ X, x ≠ 0 ∧ ((1 - ((bb + S : ℕ) : ℤ) ≤ x ∧ x ≤ (a : ℤ) - bb) ∨
      (1 - (η : ℤ) ≤ x ∧ x ≤ ((η + a : ℕ) : ℤ)))) :
    (p - 1) * ∑ x ∈ X, padicValInt p x ≤
      2 * a + 2 * η + S + (p - 1) * (Nat.log p (bb - a - 1) + 1) := by
  have e1 : ∑ x ∈ X.filter (fun x => x ≤ (a : ℤ) - bb), padicValInt p x +
      ∑ x ∈ X.filter (fun x => ¬ x ≤ (a : ℤ) - bb), padicValInt p x = ∑ x ∈ X, padicValInt p x :=
    Finset.sum_filter_add_sum_filter_not X (fun x => x ≤ (a : ℤ) - bb) (padicValInt p)
  have e2 : ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => 0 < x), padicValInt p x +
      ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => ¬ 0 < x), padicValInt p x =
      ∑ x ∈ X.filter (fun x => ¬ x ≤ (a : ℤ) - bb), padicValInt p x :=
    Finset.sum_filter_add_sum_filter_not _ (fun x => 0 < x) (padicValInt p)
  have b1 : (p - 1) * ∑ x ∈ X.filter (fun x => x ≤ (a : ℤ) - bb), padicValInt p x ≤
      (bb + S - 1) - (bb - a - 1) + (p.digits (bb - a - 1)).sum := by
    apply sub_one_mul_sum_padicValInt_le_sub_add_digits_sum p _ _ _ (by omega)
    · intro x hx
      rw [Finset.mem_filter] at hx
      have hx' := hX x hx.1
      push_cast at hx'
      rcases Int.natAbs_eq x with h | h <;> omega
    · intro x hx y hy hxy
      rw [Finset.mem_filter] at hx hy
      rcases Int.natAbs_eq x with h1 | h1 <;> rcases Int.natAbs_eq y with h2 | h2 <;> omega
  have b2 : (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => 0 < x),
      padicValInt p x ≤ (η + a) - 0 + (p.digits 0).sum := by
    apply sub_one_mul_sum_padicValInt_le_sub_add_digits_sum p _ _ _ (by omega)
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_filter] at hx
      have hx' := hX x hx.1.1
      push_cast at hx'
      rcases Int.natAbs_eq x with h | h <;> omega
    · intro x hx y hy hxy
      rw [Finset.mem_filter, Finset.mem_filter] at hx hy
      rcases Int.natAbs_eq x with h1 | h1 <;> rcases Int.natAbs_eq y with h2 | h2 <;> omega
  have b3 : (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => ¬ 0 < x),
      padicValInt p x ≤ η - 0 + (p.digits 0).sum := by
    apply sub_one_mul_sum_padicValInt_le_sub_add_digits_sum p _ _ _ (by omega)
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_filter] at hx
      have hx' := hX x hx.1.1
      push_cast at hx'
      rcases Int.natAbs_eq x with h | h <;> omega
    · intro x hx y hy hxy
      rw [Finset.mem_filter, Finset.mem_filter] at hx hy
      have hx' := hX x hx.1.1
      have hy' := hX y hy.1.1
      rcases Int.natAbs_eq x with h1 | h1 <;> rcases Int.natAbs_eq y with h2 | h2 <;> omega
  have z : (p.digits 0).sum = 0 := by simp
  have d := digits_sum_le_log p (bb - a - 1)
  have total : (p - 1) * ∑ x ∈ X, padicValInt p x =
      (p - 1) * ∑ x ∈ X.filter (fun x => x ≤ (a : ℤ) - bb), padicValInt p x +
      (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => 0 < x), padicValInt p x +
      (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => ¬ 0 < x),
        padicValInt p x := by
    rw [← e1, ← e2]
    ring
  omega

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt
end

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

open Polynomial

section SlopeTestRemainingChoices

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem gammaD_smul_letA' (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem idempotent_mul_self'' (c : ZMod n) : (letE c : LetA O n) * letE c = letE c := by
  funext i
  by_cases h : i = c
  · subst h; simp [letE]
  · simp [letE, h]

theorem invariantLetter_sub {c : ZMod n} {x y : W.DD T} (hx : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x)
    (hy : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c y) : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (x - y) := by
  rw [sub_eq_add_neg, ← neg_one_smul O y]
  exact dl_add W T hx (dl_smul W T (-1) hy)

theorem invariant_letter_idempotent_smul {c : ZMod n} {z : W.DD T} (hz : ∀ δ ∈ W.DelF, W.γD T δ z = z) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c ((letE c : LetA O n) • z) :=
  ⟨by rw [smul_smul, idempotent_mul_self''], fun δ hδ => by rw [gammaD_smul_letA', gammaA_idempotent, hz δ hδ]⟩

theorem uniformizer_smul_inverse_smul (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (x : W.DD T) :
    W.π₀ • (uniformizerInverse W • x) = x := by
  rw [← algebraMap_smul W.EE W.π₀, smul_smul, algebraMap_uniformizer_mul_inverse hU, one_smul]

theorem smul_comm_O_EE (r : O) (e : W.EE) (x : W.DD T) : r • (e • x) = e • (r • x) := by
  rw [← algebraMap_smul (LetA O n) r (e • x), ← algebraMap_smul (LetA O n) r x, smul_comm_letA_EE]

theorem q_pow_smul_inverse_pow_smul (hU : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (a : ℕ) (x : W.DD T) :
    Formalism.MainNotions.LiftingTheory.qp W ^ a • (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a • x) = x := by
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ a), smul_smul, map_pow, ← mul_pow,
    Ring.mul_inverse_cancel _ hU, one_pow, one_smul]

theorem delta_fixes_cocycle_second (x : ↥(W.wachCocyclesDelta T)) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γD T δ (x : W.DD T × W.DD T).2 = (x : W.DD T × W.DD T).2 := by
  have h : (x : W.DD T × W.DD T) ∈ W.wachCocyclesDelta T := x.2
  simp only [LocWach.wachCocyclesDelta, herrZ1Δ, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.prodMap_apply, LinearMap.id_apply, sub_eq_zero] at h
  exact congrArg Prod.snd (h.2 δ hδ)

theorem mem_of_natCast_pow_smul_mem [NeZero n] (hB : Sh.BasTool W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hT : IsCrys PD T.ρ)
    (c : ZMod n) {w : W.DD T} (k : ℕ) (hw : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c w)
    (hN : ((PD.p : ℕ) : O) ^ k • w ∈ W.N T) : w ∈ W.N T := by
  obtain ⟨e, he⟩ := (hB hA T hT c).1
  have hmem : ((PD.p : ℕ) : O) ^ k • w ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T c 0 :=
    Submodule.subset_span ⟨_, ⟨hN, dl_smul W T _ hw⟩, by simp⟩
  have h := ((hB hA T hT c).2 _ e he 0).2 w k hmem
  refine Submodule.span_le.2 ?_ h
  rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
  simpa using hx

theorem exists_embedding_over_letter [NeZero n] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (c : ZMod n) :
    ∃ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ c := by
  let e := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hA.1
  refine ⟨(W.emb c).comp e.symm.toAlgHom, ?_⟩
  ext x
  show (W.emb c) (e.symm (algebraMap K₀ K x)) = W.emb c x
  congr 1
  exact e.symm_apply_apply x

theorem lam_nonneg_of_one_lt (l H : ℕ) (hl : 1 < l) : 0 ≤ lam l H := by
  unfold lam
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · simp
  · have : (1 : ℝ) ≤ 2 * (H : ℝ) := by
      have : (1 : ℝ) ≤ H := by exact_mod_cast hH
      linarith
    have := Real.logb_nonneg (b := (l : ℝ)) (by exact_mod_cast hl) this
    linarith

end SlopeTestRemainingChoices

section Core

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def liftingSection (R : Polynomial O) (a : ℕ) (ν zc : W.DD T) : W.DD T :=
  Polynomial.aeval (derivationOnWachModule W T) R
      (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a • ν) +
    Polynomial.aeval (derivationOnWachModule W T) (Polynomial.divX R) (uniformizerInverse W • zc)

theorem lift_of_killing_polynomial [NeZero n] (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hDS : DerivationPreservesQLattice W)
    (hB : Sh.BasTool W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hT : IsCrys PD T.ρ) (c : ZMod n) (a N s₁ : ℕ)
    (R : Polynomial O) (hR0 : R.coeff 0 = ((PD.p : ℕ) : O) ^ s₁)
    (hkill : ∀ y₀, QLattice W T c a y₀ → Polynomial.aeval (derivationOnWachModule W T) (X * R) y₀ ∈ W.N T)
    (zc μ ν : W.DD T) (hzc : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c zc) (hμ : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c μ)
    (hν : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c ν)
    (h3 : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 (((PD.p : ℕ) : O) ^ N • zc + (W.γ T μ - μ)))
    (h6 : ((PD.p : ℕ) : O) ^ N • ν - Formalism.MainNotions.LiftingTheory.qp W ^ a • μ ∈ W.N T) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (liftingSection W T R a ν zc) ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 (((PD.p : ℕ) : O) ^ s₁ • zc +
      (W.γ T (liftingSection W T R a ν zc) - liftingSection W T R a ν zc)) ∧
    QLattice W T c a (((PD.p : ℕ) : O) ^ N • liftingSection W T R a ν zc - ((PD.p : ℕ) : O) ^ s₁ • μ) ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1
      (W.γ T (((PD.p : ℕ) : O) ^ N • liftingSection W T R a ν zc - ((PD.p : ℕ) : O) ^ s₁ • μ) -
        (((PD.p : ℕ) : O) ^ N • liftingSection W T R a ν zc - ((PD.p : ℕ) : O) ^ s₁ • μ)) := by
  have hU := hR.πU
  have hπΔ := hR.πΔ
  have hqU := hR.qU
  have hqΔ := Formalism.MainNotions.LiftingTheory.lifta_qΔ W hπΔ
  set d := derivationOnWachModule W T with hd
  set pp : O := ((PD.p : ℕ) : O) with hpp
  have ciFix : ∀ δ ∈ W.DelF, W.γE δ (uniformizerInverse W) = uniformizerInverse W :=
    fun δ hδ => delta_fixes_inverse W _ hπΔ hU δ hδ
  have qiFix : ∀ δ ∈ W.DelF, W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a) =
      Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a := by
    intro δ hδ
    rw [map_pow, delta_fixes_inverse W _ hqΔ hqU δ hδ]
  set R1 := Polynomial.divX R with hR1
  have hsplit : R = R1 * X + C (pp ^ s₁) := by
    rw [← hR0, mul_comm]
    exact (Polynomial.X_mul_divX_add R).symm
  set m₀ := Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a • ν with hm₀def
  set dz := uniformizerInverse W • zc with hdzdef
  have hm₀ : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c m₀ := invariantLetter_fixed_smul W T _ qiFix hν
  have hdz : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c dz := invariantLetter_fixed_smul W T _ ciFix hzc
  obtain ⟨y, hyN, hyΔ, hye⟩ := h3
  have he₁ : uniformizerInverse W • (pp ^ N • zc + (W.γ T μ - μ)) = y := by
    rw [hye, pow_one, inverse_smul_uniformizer_smul W T hU]
  have hy_eq : y = pp ^ N • dz + d μ := by
    rw [← he₁, smul_add, hd, derivation_on_wach_module_apply, hdzdef, smul_comm_O_EE]
  have hyDL : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c y := by
    rw [← he₁]
    exact invariantLetter_fixed_smul W T _ ciFix (dl_add W T (dl_smul W T _ hzc) (invariantLetter_gamma_sub W T hμ))
  have hyQ : QLattice W T c 0 y := ⟨hyDL, by simpa using hyN⟩
  set u₀ := pp ^ N • m₀ - μ with hu₀def
  have hu₀ : QLattice W T c a u₀ := by
    refine ⟨invariantLetter_sub W T (dl_smul W T _ hm₀) hμ, ?_⟩
    rw [hu₀def, smul_sub, smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ a) (pp ^ N) m₀, hm₀def, q_pow_smul_inverse_pow_smul W T hqU]
    exact h6
  have hms : liftingSection W T R a ν zc = Polynomial.aeval d R m₀ + Polynomial.aeval d R1 dz := rfl
  have key : Polynomial.aeval d R μ = pp ^ s₁ • μ + Polynomial.aeval d R1 (d μ) := by
    conv_lhs => rw [hsplit]
    rw [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.add_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, add_comm]
  set u := pp ^ N • liftingSection W T R a ν zc - pp ^ s₁ • μ with hudef
  have e1 : Polynomial.aeval d R u₀ = pp ^ N • Polynomial.aeval d R m₀ - Polynomial.aeval d R μ := by
    rw [hu₀def, (Polynomial.aeval d R).map_sub, (Polynomial.aeval d R).map_smul]
  have e2 : Polynomial.aeval d R1 y = pp ^ N • Polynomial.aeval d R1 dz + Polynomial.aeval d R1 (d μ) := by
    rw [hy_eq, (Polynomial.aeval d R1).map_add, (Polynomial.aeval d R1).map_smul]
  have hu_eq : u = Polynomial.aeval d R u₀ + Polynomial.aeval d R1 y := by
    rw [hudef, hms, e1, e2, key, smul_add]
    abel
  have hXP : ∀ (Q : Polynomial O) (x : W.DD T),
      d (Polynomial.aeval d Q x) = Polynomial.aeval d (X * Q) x := by
    intro Q x
    rw [map_mul, Polynomial.aeval_X, Module.End.mul_apply]
  have hDLms : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (liftingSection W T R a ν zc) := by
    rw [hms]
    exact dl_add W T (invariantLetter_polynomial_derivation W T hπΔ hU R hm₀) (invariantLetter_polynomial_derivation W T hπΔ hU R1 hdz)
  have hQu : QLattice W T c a u := by
    rw [hu_eq]
    exact qLattice_add W T (qLattice_polynomial_derivation W T hDS hA hT c a R hu₀)
      (qLattice_mono W T (Nat.zero_le a) (qLattice_polynomial_derivation W T hDS hA hT c 0 R1 hyQ))
  have hdu : d u = Polynomial.aeval d (X * R) u₀ + Polynomial.aeval d (X * R1) y := by
    rw [hu_eq, map_add (f := _), hXP, hXP]
  have hduN : d u ∈ W.N T := by
    rw [hdu]
    refine (W.N T).add_mem (hkill u₀ hu₀) ?_
    have h := (qLattice_polynomial_derivation W T hDS hA hT c 0 (X * R1) hyQ).2
    rw [pow_zero, one_smul] at h
    exact h
  have hduDL : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (d u) := invariantLetter_derivation W T hπΔ hU hQu.1

  set w := pp ^ s₁ • dz + d (liftingSection W T R a ν zc) with hwdef
  have hexpr : pp ^ s₁ • zc + (W.γ T (liftingSection W T R a ν zc) - liftingSection W T R a ν zc) = W.π₀ • w := by
    rw [hwdef, smul_add, smul_comm W.π₀ (pp ^ s₁) dz, hdzdef, uniformizer_smul_inverse_smul W T hU, hd,
      uniformizer_smul_derivation W T hU]
  have hpw : pp ^ N • w = pp ^ s₁ • y + d u := by
    have h1 : pp ^ N • dz = y - d μ := by rw [hy_eq]; abel
    have h2 : pp ^ N • liftingSection W T R a ν zc = u + pp ^ s₁ • μ := by rw [hudef]; abel
    rw [hwdef, smul_add, smul_comm (pp ^ N) (pp ^ s₁) dz, h1, ← d.map_smul (pp ^ N), h2,
      d.map_add, d.map_smul, smul_sub]
    abel
  have hwDL : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c w :=
    dl_add W T (dl_smul W T _ hdz) (invariantLetter_derivation W T hπΔ hU hDLms)
  have hwN : w ∈ W.N T := by
    refine mem_of_natCast_pow_smul_mem W T hB hA hT c N hwDL ?_
    rw [hpw]
    exact (W.N T).add_mem ((W.N T).smul_of_tower_mem _ hyN) hduN
  refine ⟨hDLms, ⟨w, hwN, hwDL.2, by rw [pow_one, hexpr]⟩, hQu, ⟨d u, hduN, hduDL.2, ?_⟩⟩
  rw [pow_one, hd, uniformizer_smul_derivation W T hU]

end Core

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

open Polynomial

theorem first_lift_of_hypotheses [NeZero n] (W : LocWach PD LL O v n) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing O v)
    (h9 : Formalism.MainNotions.LiftingTheory.P9π₀ W) (hRN : Formalism.MainNotions.LiftingTheory.CaseA W → Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W)
    (hDS : DerivationPreservesQLattice W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DssLet W)
    (hEx : Sh.ExpRules W) (hER : Sh.ExpRing W) (hK : Sh.LemK W) (hFD : Sh.FilDim W)
    (hB : Sh.BasTool W) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : Step1 W := by
  intro d T₁ T₂ F b S η m hS
  haveI : Fact PD.p.Prime := ⟨PD.hp⟩
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hl : 11 ≤ PD.p := hS.2.1
  obtain ⟨hdom, hdvr, hfrac⟩ := hS.2.2.2.1
  obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
  have hT₂ : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W h9
  set a := ⌈aR PD.p (hpar n b S + η)⌉₊ with ha_def
  have hp1 : (1 : ℝ) < PD.p := by exact_mod_cast (by omega : 1 < PD.p)
  have hpos : (0 : ℝ) < (PD.p : ℝ) - 1 := by linarith
  have haR : 0 ≤ aR PD.p (hpar n b S + η) := by
    have hlam := lam_nonneg_of_one_lt PD.p (hpar n b S + η) (by omega)
    unfold aR
    have : 0 ≤ ((hpar n b S + η : ℕ) : ℝ) * (2 * (PD.p : ℝ) - 1) / ((PD.p : ℝ) - 1) ^ 2 :=
      div_nonneg (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _)
    linarith
  have hab : ∀ c, a + η < b c := by
    intro c
    have h1 := hS.2.2.2.2.2.2.2.2.1 c
    have h2 : (a : ℝ) < aR PD.p (hpar n b S + η) + 1 := Nat.ceil_lt_add_one haR
    have : (a : ℝ) + η < b c := by linarith
    exact_mod_cast this
  have hbh : ∀ c, b c ≤ hpar n b S := fun c =>
    le_trans (Finset.le_sup (f := b) (Finset.mem_univ c)) (Nat.le_add_right _ _)

  have hjw : ∀ c τ, Formalism.MainNotions.LiftingTheory.Over W τ c → JumpsInV PD T₂.ρ τ (JumpWinS d b S η c) :=
    fun c τ hτ => Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS c τ hτ
  set Mb : ZMod n → ℕ := fun i => b i + S + η with hMb
  have hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₂ Mb Mb := by
    intro i τ hτ x hx
    have h := hjw i τ hτ x hx
    unfold JumpWinS at h
    simp only [hMb, Set.mem_Icc]
    split_ifs at h <;> simp only [Set.mem_union, Set.mem_Icc] at h <;> omega
  obtain ⟨cO, hcO, hc0, hcv⟩ := step1Kill_cO W hV (hRN hA)
  set Sx : ZMod n → Finset ℤ := fun c => (step1Kill_roots W T₂ c (Mb c) (Mb c) a).filter (· ≠ 0)
    with hSx_def
  have hSx : ∀ c ∈ evens n d, ∀ x ∈ Sx c, x ≠ 0 ∧ ((1 - ((b c + S : ℕ) : ℤ) ≤ x ∧ x ≤ (a : ℤ) - b c) ∨
      (1 - (η : ℤ) ≤ x ∧ x ≤ ((η + a : ℕ) : ℤ))) := by
    intro c hc x hx
    have hev : (c.val + d) % 2 = 0 := by simpa [evens] using hc
    rw [hSx_def, Finset.mem_filter, step1Kill_roots, Finset.mem_image] at hx
    obtain ⟨⟨p, hp, rfl⟩, hx0⟩ := hx
    rw [Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨hu, hj1, hj2⟩ := hp
    unfold jumpSetL at hu
    simp only [Finset.mem_filter] at hu
    obtain ⟨-, τ, hτ, hjmp⟩ := hu
    have hw := hjw c τ hτ p.1 hjmp
    simp only [JumpWinS, hev, if_true, Set.mem_union, Set.mem_Icc] at hw
    refine ⟨hx0, ?_⟩
    push_cast at hj1 hj2 ⊢
    omega

  have hbound : ∀ c ∈ evens n d,
      ((∑ x ∈ Sx c, padicValInt PD.p x : ℕ) : ℝ) ≤ B1 PD.p (hpar n b S) η S := by
    intro c hc
    have hv := padicValInt_sum_le PD.p (b c) S η a (hab c) (Sx c) (hSx c hc)
    have hv' : ((PD.p : ℝ) - 1) * ((∑ x ∈ Sx c, padicValInt PD.p x : ℕ) : ℝ) ≤
        2 * (a : ℝ) + 2 * η + S + ((PD.p : ℝ) - 1) * ((Nat.log PD.p (b c - a - 1) : ℝ) + 1) := by
      have := (Nat.cast_le (α := ℝ)).2 hv
      push_cast [Nat.cast_sub (by omega : 1 ≤ PD.p)] at this ⊢
      linarith
    have hH : (1 : ℝ) ≤ 2 * ((hpar n b S + η : ℕ) : ℝ) := by
      have h1 : 1 ≤ hpar n b S + η := by have := hab c; have := hbh c; omega
      have : (1 : ℝ) ≤ ((hpar n b S + η : ℕ) : ℝ) := by exact_mod_cast h1
      linarith
    have hlog : (Nat.log PD.p (b c - a - 1) : ℝ) ≤ Real.logb PD.p (2 * ((hpar n b S + η : ℕ) : ℝ)) := by
      rcases Nat.eq_zero_or_pos (b c - a - 1) with hK0 | hKpos
      · rw [hK0, Nat.log_zero_right, Nat.cast_zero]
        exact Real.logb_nonneg hp1 hH
      · have hKle : ((b c - a - 1 : ℕ) : ℝ) ≤ 2 * ((hpar n b S + η : ℕ) : ℝ) := by
          have : b c - a - 1 ≤ hpar n b S + η := by have := hbh c; omega
          have : ((b c - a - 1 : ℕ) : ℝ) ≤ ((hpar n b S + η : ℕ) : ℝ) := by exact_mod_cast this
          linarith
        calc (Nat.log PD.p (b c - a - 1) : ℝ) ≤ Real.logb PD.p ((b c - a - 1 : ℕ) : ℝ) :=
              Real.natLog_le_logb _ _
          _ ≤ _ := Real.logb_le_logb_of_le hp1 (by exact_mod_cast hKpos) hKle
    unfold B1 lam
    have hm := mul_le_mul_of_nonneg_left hlog hpos.le
    rw [show ((aN PD.p (hpar n b S + η) : ℕ) : ℝ) = (a : ℝ) from rfl, div_add' _ _ _ hpos.ne',
      le_div_iff₀ hpos]
    nlinarith
  have hB1 : 0 ≤ B1 PD.p (hpar n b S) η S := by
    unfold B1
    have := lam_nonneg_of_one_lt PD.p (hpar n b S + η) (by omega)
    have : 0 ≤ (2 * (aN PD.p (hpar n b S + η) : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((PD.p : ℝ) - 1) :=
      div_nonneg (by positivity) hpos.le
    linarith
  set s₁ : ℕ := (evens n d).sup fun c => ∑ x ∈ Sx c, padicValInt PD.p x with hs₁_def
  have hs₁ : (s₁ : ℝ) ≤ B1 PD.p (hpar n b S) η S := by
    have : s₁ ≤ ⌊B1 PD.p (hpar n b S) η S⌋₊ := Finset.sup_le (fun c hc => Nat.le_floor (hbound c hc))
    exact le_trans (by exact_mod_cast this) (Nat.floor_le hB1)
  refine ⟨s₁, hs₁, ?_⟩
  intro FF _ _ _ _ g N y z μ ν hX
  haveI := hdom
  haveI := hdvr
  haveI := hfrac

  have hw : ∀ c, ∃ w : O, c ∈ evens n d →
      (C w * ∏ x ∈ Sx c, (X - C (cO x))).coeff 0 = ((PD.p : ℕ) : O) ^ s₁ := by
    intro c
    by_cases hc : c ∈ evens n d
    · obtain ⟨w, hw⟩ := step1Kill_norm hV W.v_l cO hcv (Sx c) (by simp [hSx_def]) s₁
        (Finset.le_sup (f := fun c => ∑ x ∈ Sx c, padicValInt PD.p x) hc)
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose wc hwc using hw
  set R : ZMod n → Polynomial O := fun c => C (wc c) * ∏ x ∈ Sx c, (X - C (cO x)) with hR_def
  have hkill : ∀ c ∈ evens n d, ∀ y₀, QLattice W T₂ c a y₀ →
      Polynomial.aeval (derivationOnWachModule W T₂) (X * R c) y₀ ∈ W.N T₂ := by
    intro c _ y₀ hy
    have h := step1Kill_kill W T₂ hR hDS hD hA hT₂ Mb Mb hJ c cO hcO hc0 a hy
    have e : X * R c = C (wc c) * (X * ∏ x ∈ Sx c, (X - C (cO x))) := by
      simp only [hR_def]; ring
    rw [e, map_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact (W.N T₂).smul_of_tower_mem _ h

  obtain ⟨hX1, hX2⟩ := hX
  have hzΔ : ∀ f, ∀ δ ∈ W.DelF, W.γD T₂ δ (z f) = z f := by
    intro f δ hδ
    obtain ⟨x, -, hxe, -⟩ := hX1 f
    have h := delta_fixes_cocycle_second W T₂ x δ hδ
    rw [hxe] at h
    exact h
  let smE : W.EE → W.DD T₂ →ₗ[O] W.DD T₂ := fun e =>
    (LinearMap.lsmul W.EE (W.DD T₂) e).restrictScalars O
  let smA : LetA O n → W.DD T₂ →ₗ[O] W.DD T₂ := fun e =>
    (LinearMap.lsmul (LetA O n) (W.DD T₂) e).restrictScalars O
  let ms : ZMod n → FF →ₗ[O] W.DD T₂ := fun c =>
    Polynomial.aeval (derivationOnWachModule W T₂) (R c) ∘ₗ
        smE (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a) ∘ₗ ν c +
      Polynomial.aeval (derivationOnWachModule W T₂) (Polynomial.divX (R c)) ∘ₗ smE (uniformizerInverse W) ∘ₗ
        smA (letE c) ∘ₗ z
  have hcore := fun c (hc : c ∈ evens n d) (f : FF) =>
    lift_of_killing_polynomial W T₂ hR hDS hB hA hT₂ c a N s₁ (R c) (hwc c hc) (hkill c hc)
      ((letE c : LetA O n) • z f) (μ c f) (ν c f) (invariant_letter_idempotent_smul W T₂ (hzΔ f)) (hX2 c f).1
      (hX2 c f).2.1 (hX2 c f).2.2.1 (hX2 c f).2.2.2.2.2
  let uL : ZMod n → FF →ₗ[O] W.DD T₂ := fun c =>
    ((PD.p : ℕ) : O) ^ N • ms c - ((PD.p : ℕ) : O) ^ s₁ • μ c
  have hpass : ∀ c ∈ evens n d, (∀ (lenO : ℕ∞) (cc : ℝ) (A : Submodule O FF),
      ∃ B, PChain lenO m cc A B 1 0 ∧ ∀ f ∈ B, uL c f ∈ W.N T₂) ∧
      (m = 0 → ∀ f, uL c f ∈ W.N T₂) := by
    intro c hc
    obtain ⟨τ, hτ⟩ := exists_embedding_over_letter W hA c
    exact step1Pass_pass W T₂ hA hT₂ ζ hζ hEx hER hK hFD c τ hτ
      (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fd_letter₂ W hS c) (uL c) a m
      (fun f => ⟨(hcore c hc f).2.2.1.1, (hcore c hc f).2.2.1.2, (hcore c hc f).2.2.2⟩)
      (sum_multV_le W hFD hS hE hC hQ c hc τ hτ a (by have := hab c; omega))
  have hout : ∀ F₁ : Submodule O FF, (∀ c ∈ evens n d, ∀ f ∈ F₁, uL c f ∈ W.N T₂) →
      Step1Out W T₂ d a N s₁ z μ F₁ ms := by
    intro F₁ hF c hc f
    exact ⟨(hcore c hc f).1, (hcore c hc f).2.1, (hcore c hc f).2.2.1.2, (hcore c hc f).2.2.2,
      fun hf => hF c hc f hf⟩
  by_cases hm0 : m = 0
  · exact ⟨⊤, ms, (PChain.refl _ _ _ ⊤).mono (Nat.zero_le _) le_rfl, fun _ => rfl,
      hout ⊤ (fun c hc f _ => (hpass c hc).2 hm0 f)⟩
  · obtain ⟨B, hBc, hBP⟩ := iter_chain (lenO := lenOl PD (O := O)) (m := m)
      (c := lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S)
      (fun c B => ∀ f ∈ B, uL c f ∈ W.N T₂) (· ∈ evens n d)
      (fun _ _ _ hBA hP f hf => hP f (hBA hf)) ⊤ 1 0 (fun c hc A _ => (hpass c hc).1 _ _ A)
      (evens n d).toList (fun c hc => Finset.mem_toList.1 hc) ⊤ le_rfl
    refine ⟨B, ms, ?_, fun h => absurd h hm0, hout B (fun c hc => hBP c (Finset.mem_toList.2 hc))⟩
    simpa [Finset.length_toList] using hBc

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem first_lift_of_uniformizer_clause [NeZero n] (W : LocWach PD LL O v n) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing O v)
    (h9 : Formalism.MainNotions.LiftingTheory.P9π₀ W) (hRN : Formalism.MainNotions.LiftingTheory.CaseA W → Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DssLet W) (hEx : Sh.ExpRules W) (hER : Sh.ExpRing W)
    (hK : Sh.LemK W) (hFD : Sh.FilDim W) (hB : Sh.BasTool W) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : Step1 W :=
  first_lift_of_hypotheses W hV h9 hRN (rToolMod_dStab W hP9) hD hEx hER hK hFD hB hE hC hQ

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
