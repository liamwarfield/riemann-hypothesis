module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RadOfDense
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.CountE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNumJE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTypeV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LaArtin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypePSTAltAlt

@[expose] public section

attribute [-instance] Formalism.LFunctionChainParameters.LChain6.FamC.indexKFirst Formalism.LFunctionChainParameters.LChain6.FamC.indexKSecond Formalism.LFunctionChainParameters.LChain6.FamC.indexKThird Formalism.LFunctionChainParameters.LChain6.FamC.indexKFourth Formalism.BasicNotions.NTypes.instMray Formalism.BasicNotions.NTypes.nfMray Formalism.BasicNotions.NTypes.algKM UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CountE
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcOf
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Desc.P
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Desc.P.dense_threshold_bc_of_prop : _root_.UpperTheory.V.Z.J.D.BcOfAlt := by
  intro H E Ω _ _ _ _ _ _ hE l _ hl ι n hn σ hσ R hRc hRi hR
  obtain ⟨r, HT, hc, hs, -, -, hL, -, hQ⟩ := _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH H E Ω hE l hl ι n hn σ hσ
  have hss : Formalism.MainNotions.N.IsSSRep R := by
    intro M hM
    rcases hRi.2.2 M le_top hM with rfl | rfl
    · exact ⟨⊤, hRi.2.1, isCompl_bot_top⟩
    · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
      rw [(Submodule.mem_bot _).1 hv]
      simp
  have hunram : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsUnramU σ w := by
    obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ.ne_bot
    let L : Subgroup (finU (E := E) (n := n)) :=
      { carrier := {k | RU E n k φ = φ}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at *
          rw [Subgroup.coe_mul, map_mul, mul_apply_eq_comp, hb, ha]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq] at *
          conv_lhs => rw [← ha]
          rw [← mul_apply_eq_comp, ← map_mul, Subgroup.coe_inv, inv_mul_cancel,
            map_one, one_apply_eq_self] }
    have hLo : IsOpen (L : Set (finU (E := E) (n := n))) := (hσ.aut φ hφ).level
    filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary
      E n L hLo] with w hw
    exact ⟨φ, hφ, hφ0, fun x hx hxK => hw x hx hxK hx.1⟩
  have hAway : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, (l : 𝓞 E) ∉ w.asIdeal := by
    have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun w hw => Ideal.dvd_span_singleton.mpr (not_not.1 hw)
  have hAgree : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      IsSplitAt w → ∃ B, FrobEig ι R w B ∧ FrobEig ι r w B := by
    filter_upwards [hR, hAway, hunram] with w h1 hw hu hsp
    obtain ⟨τ, -, h2, h3⟩ := GlobalTheory.DefU.exists_locComp_split E n ⟨σ, hσ⟩ w hsp
    obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 (h3.1 hu)
    obtain ⟨b, hb⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results H.toClassicalTheorems E n w τ).1 ⟨v, h0, fun u hu => by simpa using hv ⟨u, hu⟩⟩
    have k : _root_.UpperTheory.V.Z.Win.LocGlobT ι r w τ := (hL w hsp τ h2).1
    exact ⟨_, _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt H.toClassicalTheorems E Ω l ι n R hRc w hw τ b hb (_root_.UpperTheory.V.Z.Desc.P.lgAwayT (h1 hsp τ h2) hw),
      _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt H.toClassicalTheorems E Ω l ι n r hc w hw τ b hb (_root_.UpperTheory.V.Z.Desc.P.lgAwayT k hw)⟩
  have hiso : RepIso R r := by
    have hChar : ∀ g : G E Ω, (R g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
        (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
      intro g
      ext i
      have hRcoeff : Continuous fun g : G E Ω =>
          (R g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
        (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp
          (Units.continuous_val.comp (hRc.comp continuous_inv))
      have hrcoeff : Continuous fun g : G E Ω =>
          (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
        (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp
          (Units.continuous_val.comp (hc.comp continuous_inv))
      refine congrFun (GlobalTheory.Published.chebotarevDegreeOne'.eq_of_frob
        (Filter.eventually_cofinite.1 hAgree) hRcoeff hrcoeff ?_) g
      intro w hw hd A hA s hFrob
      have hSplit := UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E w (hE w) hd
      obtain ⟨B, hB, hB'⟩ := not_not.1 hw hSplit
      have h := ((hB A hA).2 s hFrob).trans ((hB' A hA).2 s hFrob).symm
      have h' := Polynomial.map_injective ι.toRingHom ι.injective h
      rw [h']
    obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix R r hss hs
      (fun g => by simpa using hChar g⁻¹)
    exact ⟨P⁻¹, fun g => by rw [hP g, inv_inv]⟩
  have hirr : IsIrr r := by
    obtain ⟨P, hP⟩ := hiso
    refine ⟨hRi.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
    let T : (Fin n → Qbar l) ≃ₗ[Qbar l] (Fin n → Qbar l) :=
      (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
    have hT : ∀ v, T v = (P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v := fun v => rfl
    have hInv : Formalism.MainNotions.N.IsInv R (M.comap T.toLinearMap) := by
      intro g v hv
      have hComm : T ((R g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v) =
          (r g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec (T v) := by
        rw [hT, hT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP g]
        simp [Matrix.mul_assoc]
      show T _ ∈ M
      rw [hComm]
      exact hM g _ hv
    have hMap := (Submodule.map_comap_eq_of_surjective T.surjective M).symm
    rcases hRi.2.2 _ le_top hInv with h | h
    · left
      rw [hMap, h, Submodule.map_bot]
    · right
      rw [hMap, h, Submodule.map_top, LinearMap.range_eq_top.2 T.surjective]
  obtain ⟨π, h1, h2, -, h4, h5, h6⟩ := hQ hirr
  refine ⟨π, h1, h2, ?_, h4, h5⟩
  filter_upwards [(_root_.UpperTheory.satake_galois_link_of_printed_hida H E n π).2] with w ⟨B, hB⟩ hsp
  obtain ⟨τ, hτ⟩ := (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results H.toClassicalTheorems E n π w).1
  exact ⟨τ, B, h6 w hsp τ hτ, ((_root_.UpperTheory.satake_galois_link_of_printed_hida H E n π).1 w τ hτ B).1 hB, hB⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSphSame
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
private theorem lat {α : Type*} [Lattice α] {Y B f z E : α} (h1 : Y ≤ B) (h2 : Y ≤ f) (h3 : Y ≤ E) :
    Y ⊓ (B ⊓ f ⊓ z ⊓ E) = Y ⊓ z :=
  le_antisymm (le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_right)))
    (le_inf inf_le_left (le_inf (le_inf (le_inf (inf_le_left.trans h1) (inf_le_left.trans h2)) inf_le_right)
      (inf_le_left.trans h3)))
private theorem eig_eq {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {a b : ℂ} {F : M} (h0 : F ≠ 0)
    (hT : T F = a • F) (hF : F ∈ T.maxGenEigenspace b) : a = b := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T b F).1 hF
  have h1 : (T - b • (1 : Module.End ℂ M)) F = (a - b) • F := by
    simp [hT, sub_smul]
  have h : ∀ i : ℕ, ((T - b • (1 : Module.End ℂ M)) ^ i) F = (a - b) ^ i • F := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, pow_succ']
  rw [h k] at hk
  by_contra hne
  exact smul_ne_zero (pow_ne_zero k (sub_ne_zero.2 hne)) h0 hk
private theorem eig_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {b : ℂ} {F : M}
    (hT : T F = b • F) : F ∈ T.maxGenEigenspace b :=
  (Module.End.mem_maxGenEigenspace T b F).2 ⟨1, by simp [hT]⟩
private theorem eig_le {M I : Type*} [AddCommGroup M] [Module ℂ M] (T : I → Module.End ℂ M) (ev : I → ℂ) (i : I) (a : ℂ)
    (O Y Y' : Submodule ℂ M) (hne : Y ⊓ (O ⊓ ⨅ i, (T i).maxGenEigenspace (ev i)) ≠ ⊥)
    (h1 : ∀ F ∈ Y, T i F = a • F) (h2 : ∀ F ∈ Y', T i F = a • F) : Y' ≤ (T i).maxGenEigenspace (ev i) := by
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hFe : F ∈ (T i).maxGenEigenspace (ev i) :=
    (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 (Submodule.mem_inf.1 hF).2).2 i
  have hae : a = ev i := eig_eq _ hF0 (h1 F (Submodule.mem_inf.1 hF).1) hFe
  intro F' hF'
  exact eig_mem _ (hae ▸ h2 F' hF')
private theorem scalar (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GLw n w)) (j : ℕ) :
    ∃ a : ℂ, ∀ v ∈ fixd τ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp τ.ρ j v = a • v := by
  by_cases h : GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.LFun.KGL w (n := n))
  · obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible τ.smooth τ.irred h
    obtain ⟨-, a, -, ha, -⟩ := UpperTheory.V.Hi.satT L n w τ B hB
    exact ⟨a j, ha j⟩
  · refine ⟨0, fun v hv => ?_⟩
    have hv0 : v = 0 := by
      by_contra h0
      rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n] at hv
      exact h ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, h0⟩)
    simp [hv0]
theorem spherical_same_of_z_eq : ZEq → _root_.UpperTheory.V.Z.J.D.SphSameAlt := by
  intro hZ hLit l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ A _ _ _ θ x c0 sp hWt hSp K ev hev σ σ' hσ hσ' hcp hne
  have hAx := _root_.UpperTheory.V.Hi.axU_s hLit l L Ω s n hn V Q c m τ₀
  have hYB : YOf Q ι τ₀ e ξ σ' ≤ (hset Q τ₀).Big ι ξ := inf_le_left
  rw [hZ L Ω l n c (hset Q τ₀) hAx A θ hWt ι x lam d ξ c0 sp hSp K ev hev]
  refine lat hYB ?_ ?_
  · haveI : IsEmpty (hset Q τ₀).Q := ⟨fun q => Q.notS q (by
      have h : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
        rw [Q.range]
        exact Or.inr ⟨q, rfl⟩
      rwa [hV] at h)⟩
    have hl : (hset Q τ₀).lev K = (hset Q τ₀).UQ := by
      simp only [HSet.lev, iSup_of_empty]
      exact sup_bot_eq _
    rw [hl]
    exact hYB.trans inf_le_right
  · refine le_iInf fun p => ?_
    obtain ⟨τ, h1, h2⟩ := hcp p.1.1 p.1.2.2
    obtain ⟨a, ha⟩ := scalar L n p.1.1 τ ((p.2 : ℕ) + 1)
    have hs := fun (σ₁ : Submodule ℂ (UA L n → ℂ)) (hσ₁ : IsAutRepU σ₁) (hτ₁ : Cp σ₁ p.1.1 τ) =>
      UpperTheory.V.Hi.partUR2Sph l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ σ₁ hσ₁ hAx p.1.1 p.1.2.1 p.1.2.2 τ hτ₁ _ a ha
    exact eig_le ((hset Q τ₀).opC ι lam d) ev (.inl p) a ((hset Q τ₀).OrdAt θ ι x.toRingHom lam ξ K c0) _ _ hne
      (hs σ hσ h1) (hs σ' hσ' h2)
end UpperTheory.V.Z.J.D
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAtSame
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
private theorem ev_of_gen {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (μ a : ℂ) (F : M) (hF : F ≠ 0)
    (h : F ∈ T.maxGenEigenspace μ) (ha : T F = a • F) : a = μ := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T μ F).1 h
  have h1 : ∀ j : ℕ, ((T - μ • 1) ^ j) F = (a - μ) ^ j • F := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, ha]
      simp only [LinearMap.smul_apply, Module.End.one_apply]
      rw [← sub_smul, smul_smul, pow_succ]
  rw [h1 k] at hk
  have h2 := (smul_eq_zero.1 hk).resolve_right hF
  by_contra hne
  exact pow_ne_zero k (sub_ne_zero.2 hne) h2
private theorem sat_eq (n q : ℕ) (hq : q ≠ 0) (B B' : Multiset ℂˣ) (a a' : ℕ → ℂ) (haa : ∀ j ≤ n, a j = a' j)
    (h : ((UpperTheory.V.Af.algSat n q B).map fun b => X - C b).prod = heckePol n q a)
    (h' : ((UpperTheory.V.Af.algSat n q B').map fun b => X - C b).prod = heckePol n q a') : B = B' := by
  have hp : heckePol n q a = heckePol n q a' := by
    rw [UpperTheory.V.Hi.heckePol, UpperTheory.V.Hi.heckePol]
    exact Finset.sum_congr rfl fun j hj => by rw [haa j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  have hr : UpperTheory.V.Af.algSat n q B = UpperTheory.V.Af.algSat n q B' := by
    rw [← Polynomial.roots_multiset_prod_X_sub_C (UpperTheory.V.Af.algSat n q B), h, hp, ← h',
      Polynomial.roots_multiset_prod_X_sub_C]
  have hc : ((((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
    exact_mod_cast (Real.rpow_pos_of_pos this _).ne'
  unfold UpperTheory.V.Af.algSat at hr
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map] at hr
  exact Multiset.map_injective (fun x y hxy => Units.ext (mul_left_cancel₀ hc hxy)) hr
private theorem mem_gen {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ)
    (x : A →+* Qbar l) (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) (K : H.Lev) (b : ℕ) (ev : H.Op → ℂ) (i : H.Op)
    (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ zPart H θ ι x lam ξ K b ev) : F ∈ (H.opC ι lam d i).maxGenEigenspace (ev i) :=
  (Submodule.mem_iInf _).1 hF.2 i
private theorem vals (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n) (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hξ : IsBasis ι e ξ) (Z : Submodule ℂ (Fin m → (hset Q τ₀).X.Fn ℂ d))
    (ev : (hset Q τ₀).Op → ℂ) (hZ : ∀ i, ∀ F ∈ Z, F ∈ ((hset Q τ₀).opC ι lam d i).maxGenEigenspace (ev i))
    (σ : Submodule ℂ (UA L n → ℂ)) (hσ : IsAutRepU σ) (hY : YOf Q ι τ₀ e ξ σ ⊓ Z ≠ ⊥)
    (w : (hset Q τ₀).Wp) (τ : SmIrr (GLw n w.1)) (hτ : Cp σ w.1 τ) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w.1 τ.ρ B) :
    ∃ a : ℕ → ℂ, a 0 = 1 ∧ (∀ j : Fin n, a (j + 1) = ev (.inl (w, j))) ∧
      ((UpperTheory.V.Af.algSat n (normV w.1) B).map fun b => X - C b).prod = heckePol n (normV w.1) a := by
  obtain ⟨-, a, ha0, ha, hp⟩ := satT L n w.1 τ B hB
  refine ⟨a, ha0, fun j => ?_, hp⟩
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  have hAx : (hset Q τ₀).Ax := _root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V Q c m τ₀
  have h1 := partUR2Sph l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ hAx w.1 w.2.1 w.2.2 τ hτ (j + 1) _ (ha (j + 1)) F hF.1
  exact ev_of_gen _ _ _ F hF0 (hZ (.inl (w, j)) F hF.2) h1
theorem atSame_alt : _root_.UpperTheory.V.Z.J.D.AtSameAlt := by
  intro hN l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ A _ _ _ θ x c0 sp hWt hSp K ev σ σ' hσ hσ' h1 h2 π hπ
  have hZ := fun i F hF => mem_gen (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev i F hF
  have hY' : YOf Q ι τ₀ e ξ σ' ≠ ⊥ := fun h => h2 (eq_bot_iff.2 (inf_le_left.trans h.le))
  have hU := partUR2Unr l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ σ' hσ' hY'
  have hfin : ∀ᶠ w : Plc L in cofinite, w.under (𝓞 (Lp L)) ∉ V.S' :=
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under (Lp L) L).eventually V.fin.compl_mem_cofinite
  refine (hπ.and hfin).mono ?_
  rintro w ⟨hw, hS⟩ hsp
  obtain ⟨τ, B, hτ, hB, hs⟩ := hw hsp
  obtain ⟨τ', -, h1', h2'⟩ := GlobalTheory.DefU.exists_locComp_split L n ⟨σ', hσ'⟩ w hsp
  obtain ⟨B', hB'⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible τ'.smooth τ'.irred (h2'.1 (hU w hS))
  let w' : (hset Q τ₀).Wp := ⟨w, hS, hsp⟩
  obtain ⟨a, a0, ha, hp⟩ := vals hN s n hn V Q c ι m τ₀ lam d e ξ hξ _ ev hZ σ hσ h1 w' τ hτ B hB
  obtain ⟨a', a0', ha', hp'⟩ := vals hN s n hn V Q c ι m τ₀ lam d e ξ hξ _ ev hZ σ' hσ' h2 w' τ' h1' B' hB'
  have hq : normV w ≠ 0 := by
    have : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
    exact Nat.card_pos.ne'
  have hBB := sat_eq n (normV w) hq B B' a a' (fun j hj => by
    rcases j with _ | j
    · rw [a0, a0']
    · have := ha ⟨j, hj⟩
      have h' := ha' ⟨j, hj⟩
      exact this.trans h'.symm) hp hp'
  subst hBB
  exact ⟨τ', B, h1', hB', hs⟩
end UpperTheory.V.Z.J.D
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ResEq2
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
private def resEquiv {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} (K : Subgroup G) (e : ρ.Equiv ρ') :
    Representation.Equiv (ρ.comp K.subtype) (ρ'.comp K.subtype) :=
  Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v =>
    Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (g : G) v
theorem resEq2_alt : _root_.UpperTheory.V.Z.J.D.TypePS2Alt → PsRes → _root_.UpperTheory.V.Z.J.D.ResidualEqualityRankTwo := by
  intro hT hP hN L Ω _ _ _ _ _ _ n hn π π' w A h τ τ' hτ hτ' χ hx hc hc'
  obtain ⟨ω, hs, ⟨e⟩, hω⟩ := hT hN L Ω n hn π w A h τ hτ χ hx hc
  obtain ⟨ω', hs', ⟨e'⟩, hω'⟩ := hT hN L Ω n hn π' w A h τ' hτ' χ hx hc'
  have ha : IsLocalArtin h (artOf h) := Classical.epsilon_spec (_root_.UpperTheory.V.Z.Win.T2.laArtinLit' hN h)
  have hu : ∀ i (y : Uo (w.adicCompletion L)), ω i y = ω' i y := by
    intro i y
    obtain ⟨σ, hσ⟩ := ha.surj y
    have h1 : valuation (w.adicCompletion L) (artOf h σ : w.adicCompletion L) = 1 := by
      rw [hσ]
      exact y.2
    have h2 := ha.ord_eq σ
    rw [GlobalTheory.SmGL.ord_eq_zero_iff.2 h1] at h2
    have hI : (σ : G L Ω) ∈ Ine (F := L) A := deg_eq_zero_iff.mp (by omega)
    have e1 : artOf h (ineIncl h ⟨σ, hI⟩) = y := hσ
    have h3 := hω i ⟨σ, hI⟩
    have h4 := hω' i ⟨σ, hI⟩
    rw [e1] at h3 h4
    exact h3.trans h4.symm
  obtain ⟨f⟩ := hP (w.adicCompletion L) n ω ω' hs hs' hu
  exact ⟨(resEquiv _ e).trans (f.trans (resEquiv _ e').symm)⟩
end UpperTheory.V.Z.J.D
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPartRep
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
private theorem val_eq {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {F : M} (h0 : F ≠ 0) {a b : ℂ}
    (h : T F = a • F) (hg : F ∈ T.maxGenEigenspace b) : a = b := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T b F).1 hg
  have hp : ∀ k : ℕ, ((T - b • (1 : Module.End ℂ M)) ^ k) F = (a - b) ^ k • F := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h, LinearMap.smul_apply,
        Module.End.one_apply, ← sub_smul, smul_smul, pow_succ]
  rw [hp k] at hk
  rcases smul_eq_zero.1 hk with h1 | h1
  · exact sub_eq_zero.1 (by_contra fun h2 => pow_ne_zero k h2 h1)
  · exact absurd h1 h0
private theorem chi_map {n : ℕ} {R S G : Type} [CommRing R] [CommRing S] [Group G] (D : W.GDet n R G) (f : R →+* S) (g : G) :
    (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
  letI : Algebra R (Polynomial S) := ((algebraMap S (Polynomial S)).comp f).toAlgebra
  let φ : Polynomial R →ₐ[R] Polynomial S :=
    { Polynomial.mapRingHom f with commutes' := fun b => Polynomial.map_C f }
  refine Eq.trans ?_ (D.nat (Polynomial R) (Polynomial S) φ
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1)))
  change D.D (Polynomial S) _ = D.D (Polynomial S) (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
  congr 1
  simp [map_sub, MonoidAlgebra.mapRingHom_single]
private theorem pol_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n q : ℕ) (a : ℕ → R) (b : ℕ → S)
    (h : ∀ j ≤ n, f (a j) = b j) : (Hi.heckePol n q a).map f = Hi.heckePol n q b := by
  unfold Hi.heckePol
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, map_mul, h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  simp
private theorem ss_irr {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} (h : Af.IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp
theorem partRep_s : _root_.UpperTheory.V.Z.J.D.PartRepAlt := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ _ ι x lam d ξ c0 sp _ K a _ _ _ z _ I D ψ hU ρ hρ hirr hD Y hY
  obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
  have hgen : ∀ i, F ∈ (H.opC ι lam d i).maxGenEigenspace (ι (z (H.gen θ a K i))) := fun i =>
    (Submodule.mem_iInf _).1 hF.2.2 i
  have hval : ∀ (w : H.Wp) (j : ℕ), j ≤ n → ι (z (H.genW θ a K w j)) = Y.a w j := by
    intro w j hj
    unfold HSet.genW
    split_ifs with h
    · have e := Y.sph w (j - 1 + 1) F hF.1
      rw [show j - 1 + 1 = j by omega] at e
      have e' : H.opC ι lam d (.inl (w, ⟨j - 1, h.2⟩)) F = Y.a w j • F := by
        have e2 : H.opC ι lam d (.inl (w, ⟨j - 1, h.2⟩)) F = sphOp (H.atW ι d w.1) (j - 1 + 1) F := rfl
        rw [e2, show j - 1 + 1 = j by omega, e]
      exact (val_eq _ hF0 e' (hgen _)).symm
    · rw [show j = 0 by omega, Y.a_zero, map_one, map_one]
  have e : W.GDet.ofRep (W.mat Y.r) = W.GDet.ofRep (W.mat ρ) := by
    refine AlgebraTools.Det.extDense _ _ _ hH.dense (fun i _ => AlgebraTools.Det.repCont _ (Units.continuous_val.comp Y.cont) i)
      (fun i _ => AlgebraTools.Det.repCont _ (Units.continuous_val.comp hρ) i) ?_
    rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    rw [← hD, chi_map, hU.frob ⟨w, hw⟩ B σ hB hσ, (AlgebraTools.Det.repApi _).2.1]
    refine Polynomial.map_injective ι.toRingHom ι.injective ?_
    refine (Y.frob ⟨w, hw⟩ B σ hB hσ).trans ?_
    rw [Polynomial.map_map]
    exact (pol_map _ n _ _ _ fun j hj => hval ⟨w, hw⟩ j hj).symm
  obtain ⟨P, hP⟩ := AlgebraTools.Det.bnRep (W.mat Y.r) (W.mat ρ) Y.ss (ss_irr hirr) fun g => by
    rw [← (AlgebraTools.Det.repApi (W.mat Y.r)).2.1 g, ← (AlgebraTools.Det.repApi (W.mat ρ)).2.1 g, e]
  refine ⟨P, fun g => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact Units.ext (hP g).symm
end UpperTheory.V.Z.J.D
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsEig
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.PRep UpperTheory.V.Hi
namespace UpperTheory.V.Z.J.D.OrdinaryOrderOne
section General
variable {G V : Type} [CommGroup G] [AddCommGroup V] [Module ℂ V]
private theorem gen_map {V' : Type} [AddCommGroup V'] [Module ℂ V'] (F : Submodule ℂ V) {f : Module.End ℂ V}
    {g : Module.End ℂ V'} (p : V →ₗ[ℂ] V') (hF : ∀ v ∈ F, f v ∈ F) (h : ∀ v ∈ F, p (f v) = g (p v)) {c : ℂ} {v : V}
    (hv : v ∈ F) (hc : v ∈ f.maxGenEigenspace c) : p v ∈ g.maxGenEigenspace c := by
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hc
  refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨m, ?_⟩
  have key : ∀ (m : ℕ), ∀ v ∈ F, ((g - c • (1 : Module.End ℂ V')) ^ m) (p v) =
      p (((f - c • (1 : Module.End ℂ V)) ^ m) v) := by
    intro m
    induction m with
    | zero => intro v _; simp
    | succ m ih =>
      intro v hv
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih]
      · simp [h v hv]
      · exact sub_mem (hF v hv) (F.smul_mem c hv)
  rw [key m v hv, hm, map_zero]
private theorem pow_eig {f : Module.End ℂ V} {v : V} {a : ℂ} (h : f v = a • v) (c : ℂ) (m : ℕ) :
    ((f - c • (1 : Module.End ℂ V)) ^ m) v = (a - c) ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h, pow_succ, mul_smul, sub_smul]
    rfl
private theorem eq_of_gen {f : Module.End ℂ V} {v : V} {a c : ℂ} (h : f v = a • v) (h0 : v ≠ 0)
    (hv : v ∈ f.maxGenEigenspace c) : a = c := by
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
  rw [pow_eig h] at hm
  exact sub_eq_zero.1 (pow_eq_zero_iff'.1 ((smul_eq_zero.1 hm).resolve_right h0)).1
private theorem exists_eig [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (E : Submodule ℂ V) (hE0 : E ≠ ⊥)
    (hE : ∀ t, ∀ v ∈ E, ρ t v ∈ E) : ∃ χ : G →* ℂˣ, ∃ v ∈ E, v ≠ 0 ∧ ∀ t, ρ t v = (χ t : ℂ) • v := by
  obtain ⟨S, ⟨hS0, hSE, hS⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ V)).has_min
    {S | S ≠ ⊥ ∧ S ≤ E ∧ ∀ t, ∀ v ∈ S, ρ t v ∈ S} ⟨E, hE0, le_rfl, hE⟩
  have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
  have key : ∀ t, ∃ c : ℂ, ∀ v ∈ S, ρ t v = c • v := fun t => by
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((ρ t).restrict (hS t))
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    have hw1 : ρ t w = c • (w : V) := congrArg Subtype.val hw.apply_eq_smul
    refine ⟨c, fun v hv => ?_⟩
    have h1 : S ⊓ Module.End.eigenspace (ρ t) c = S := by
      by_contra hne
      refine hmin _ ⟨?_, inf_le_left.trans hSE, ?_⟩ (lt_of_le_of_ne inf_le_left hne)
      · exact (Submodule.ne_bot_iff _).2 ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩,
          fun h => hw.2 (Subtype.ext h)⟩
      · rintro s x ⟨hx, hx'⟩
        refine ⟨hS s x hx, Module.End.mem_eigenspace_iff.2 ?_⟩
        rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul,
          Module.End.mul_apply, Module.End.mem_eigenspace_iff.1 hx', map_smul]
    rw [← h1] at hv
    exact Module.End.mem_eigenspace_iff.1 hv.2
  choose c hc using key
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hS0
  let c' : G →* ℂ :=
    { toFun := c
      map_one' := by
        have := hc 1 v hv
        rw [map_one, Module.End.one_apply] at this
        exact smul_left_injective ℂ hv0 (this.symm.trans (one_smul _ _).symm)
      map_mul' := fun s t => by
        have := hc (s * t) v hv
        rw [map_mul, Module.End.mul_apply, hc t v hv, map_smul, hc s v hv, smul_smul, mul_comm] at this
        exact smul_left_injective ℂ hv0 this.symm }
  exact ⟨c'.toHomUnits, v, hSE hv, hv0, fun t => hc t v hv⟩
private theorem le_gen [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (E : Submodule ℂ V)
    (hE : ∀ t, ∀ v ∈ E, ρ t v ∈ E) (μ : G →* ℂˣ)
    (h : ∀ χ : G →* ℂˣ, ∀ v ∈ E, v ≠ 0 → (∀ t, ρ t v = (χ t : ℂ) • v) → χ = μ) (t : G) :
    E ≤ Module.End.maxGenEigenspace (ρ t) (μ t : ℂ) := by
  rw [Submodule.eq_iSup_inf_genEigenspace (p := E) (f := ρ t) ⊤ (hE t)
    (Module.End.iSup_maxGenEigenspace_eq_top (ρ t))]
  refine iSup_le fun c => ?_
  by_cases h0 : E ⊓ Module.End.genEigenspace (ρ t) c ⊤ = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨χ, v, hv, hv0, hχ⟩ := exists_eig ρ _ h0 fun s v hv => ⟨hE s v hv.1,
    gen_map ⊤ (ρ s) (fun _ _ => trivial) (fun v _ => by
      rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]) trivial hv.2⟩
  rw [← h χ v hv.1 hv0 hχ, eq_of_gen (hχ t) hv0 hv.2]
  exact inf_le_right
private theorem eq_of_prod {n : ℕ} {a b : Fin n → ℂ} (hb : ∀ i, b i ≠ 0)
    (h : ∀ j, ∏ i with i ≤ j, a i = ∏ i with i ≤ j, b i) (j : Fin n) : a j = b j := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have e : (Finset.univ.filter fun i => i ≤ j) = insert j (Finset.univ.filter fun i => i < j) := by
      ext i; simp [le_iff_eq_or_lt]
    have := h j
    rw [e, Finset.prod_insert (by simp), Finset.prod_insert (by simp),
      Finset.prod_congr rfl fun i hi => ih i (Finset.mem_filter.1 hi).2] at this
    exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun i _ => hb i) this
variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace.SeparableSpace G]
private theorem exists_form {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ)
    {x : V} (hx : x ≠ 0) : ∃ μ : G →* ℂˣ, IsSmoothChar μ ∧
      ∃ l : V →ₗ[ℂ] ℂ, l ≠ 0 ∧ ∀ g v, l (ρ g v) = (μ g : ℂ) * l v := by
  have hT : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun h =>
    hx ((Submodule.mem_bot ℂ).1 (show x ∈ (⊥ : Subrepresentation ρ).toSubmodule by rw [h]; trivial))
  haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom ⊥).resolve_left hT
  have hi := isIrreducible_subQuot hM.covBy_top
  let p : (⊤ : Subrepresentation ρ).toRepresentation.IntertwiningMap (subQuot ⊤ M) :=
    ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hs : IsSmooth (subQuot ⊤ M) :=
    IsSubquotient.isSmooth ⟨⊤, p, Submodule.Quotient.mk_surjective _⟩ hρ
  obtain ⟨μ, hμ⟩ := GlobalTheory.TorusEigenform.exists_char_of_isIrreducible hs hi
  have hμM : ∀ g v, ρ g v - (μ g : ℂ) • v ∈ M.toSubmodule := fun g v => by
    have := hμ g (Submodule.Quotient.mk ⟨v, trivial⟩)
    exact (Submodule.Quotient.eq (M.toSubmodule.comap (⊤ : Subrepresentation ρ).toSubmodule.subtype)
      (x := ⟨ρ g v, trivial⟩) (y := ⟨(μ g : ℂ) • v, trivial⟩)).1 this
  have hM' : M.toSubmodule < ⊤ := lt_top_iff_ne_top.2 fun h =>
    hM.1 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨l, hl0, hlM⟩ := Submodule.exists_le_ker_of_lt_top _ hM'
  have hle : ∀ g v, l (ρ g v) = (μ g : ℂ) * l v := fun g v => by
    have := hlM (hμM g v)
    rwa [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
  obtain ⟨v, hv⟩ : ∃ v, l v ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hl0 (LinearMap.ext hn)
  refine ⟨μ, ?_, l, hl0, hle⟩
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hρ v).mem_nhds (by simp)) ?_)
    intro g hg
    have hg' : ρ g v = v := hg
    have h := hle g v
    rw [hg'] at h
    exact Units.ext (mul_right_cancel₀ hv (h.symm.trans (one_mul _).symm))
end General
private theorem inj {G M J : Type} [Group G] (I : Iwa G) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ G M)
    (hs : I.Smooth π) (a : J → G) (ha : ∀ j, a j ∈ I.P) (μ : J → ℂ) (hμ : ∀ j, μ j ≠ 0) (l : List G)
    (hz : I.z = l.prod) (hl : ∀ x ∈ l, x = 1 ∨ ∃ j, x = a j) {v : M} (hv : v ∈ fixd π I.N)
    (hv' : ∀ j, v ∈ (I.uOp π (a j)).maxGenEigenspace (μ j)) (h0 : v ∈ I.jacKer π) : v = 0 := by
  let S : M → Prop := fun v => v ∈ fixd π I.N ∧ ∀ j, v ∈ (I.uOp π (a j)).maxGenEigenspace (μ j)
  have st : ∀ x ∈ I.P, ∀ v, S v → S (I.uOp π x v) := fun x hx v hv =>
    ⟨(uOpMul G I ℂ M π _ _ hx hx v hv.1).1, fun j =>
      gen_map (fixd π I.N) (I.uOp π x) (fun w hw => (uOpMul G I ℂ M π _ _ (ha j) hx w hw).1) (fun w hw => by
        rw [(uOpMul G I ℂ M π _ _ hx (ha j) w hw).2.1, (uOpMul G I ℂ M π _ _ (ha j) hx w hw).2.1,
          I.comm x (I.P_le x hx) _ (I.P_le _ (ha j))]) hv.1 (hv.2 j)⟩
  have h1 : (1 : G) ∈ I.P ∧ ∀ v, S v → I.uOp π 1 v = 0 → v = 0 := ⟨one_mem _, fun v hv h => by
    rwa [(uOpMul G I ℂ M π _ _ (one_mem _) (one_mem _) v hv.1).2.2.1] at h⟩
  have hg : I.z ∈ I.P ∧ ∀ v, S v → I.uOp π I.z v = 0 → v = 0 := by
    rw [hz]
    refine List.prod_induction (fun x => x ∈ I.P ∧ ∀ v, S v → I.uOp π x v = 0 → v = 0) ?_ h1 ?_
    · rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
      refine ⟨mul_mem hx hy, fun v hv h => hy' v hv (hx' _ (st y hy v hv) ?_)⟩
      rw [(uOpMul G I ℂ M π _ _ hx hy v hv.1).2.1, h]
    · intro x hx
      obtain rfl | ⟨j, rfl⟩ := hl x hx
      · exact h1
      · exact ⟨ha j, fun v hv h => by_contra fun hn =>
          hμ j (eq_of_gen (h.trans (zero_smul ℂ v).symm) hn (hv.2 j)).symm⟩
  obtain ⟨m, hm⟩ := (propCker G I ℂ M π hs v hv).1 h0
  have key : ∀ (m : ℕ) (v : M), S v → (I.uOp π I.z ^ m) v = 0 → v = 0 := by
    intro m
    induction m with
    | zero => intro v _ h; simpa using h
    | succ m ih =>
      intro v hv h
      rw [pow_succ, Module.End.mul_apply] at h
      exact hg.2 v hv (ih _ (st _ hg.1 v hv) h)
  exact key m v ⟨hv, hv'⟩ hm
section Num
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
private theorem num (ω : Fin n → kˣ →* ℂˣ) {j : ℕ} (hj : j ≤ n) :
    ((Nat.card 𝓀[k] ^ (j * (n - j)) : ℕ) : ℂ) *
      ((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ) *
        (torusChar (fun i => ω i * absPow k (((n : ℂ) - 1) / 2))
          (fun i => unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ)) = psEig ω j := by
  have hd : ∀ (t : Fin n → kˣ) i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) t i) = t i := fun t =>
    congrFun ((leviTorus k (Fin n)).left_inv t)
  have hq : (Nat.card 𝓀[k] : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hn : ((nabs k (unif k) : ℝ) : ℂ) = (Nat.card 𝓀[k] : ℂ)⁻¹ := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one GlAx.unif_spec]
    simp [resCard]
  have h1 : ∀ i : Fin n, ((absPow k ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2)
        (unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ) *
      ((ω i * absPow k (((n : ℂ) - 1) / 2)) (unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ)) =
      (if (i : ℕ) < j then (ω i (unif k) : ℂ) * ((Nat.card 𝓀[k] : ℂ) ^ (i : ℕ))⁻¹ else 1) *
        (Nat.card 𝓀[k] : ℂ) ^ (if (i : ℕ) < j then -((n : ℤ) - 1 - 2 * (i : ℕ)) else 0) := by
    intro i
    split_ifs
    · rw [zpow_one, MonoidHom.mul_apply, Units.val_mul, mul_left_comm, ← Units.val_mul, ← MonoidHom.mul_apply,
        ← absPow_add, modExp_fin _ (fun _ => by simp), mul_assoc, val_absPow, hn,
        show ((((n : ℤ) - 1 - 2 * (i : ℕ) : ℤ) : ℂ) / 2 + ((n : ℂ) - 1) / 2) = (((n : ℤ) - 1 - (i : ℕ) : ℤ) : ℂ) by
          push_cast; ring, Complex.cpow_intCast, ← zpow_natCast, ← _root_.zpow_neg, ← zpow_add₀ hq, _root_.inv_zpow']
      congr 2
      ring
    · simp
  have hp : ∀ (s : Finset (Fin n)) (e : Fin n → ℤ),
      ∏ i ∈ s, (Nat.card 𝓀[k] : ℂ) ^ e i = (Nat.card 𝓀[k] : ℂ) ^ ∑ i ∈ s, e i := by
    intro s e
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hq]
  have h2 : ∑ i : Fin n, (if (i : ℕ) < j then -((n : ℤ) - 1 - 2 * (i : ℕ)) else 0) = -((j * (n - j) : ℕ) : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < j then -((n : ℤ) - 1 - 2 * i) else 0), ← Finset.sum_filter,
      show (Finset.range n).filter (· < j) = Finset.range j by ext; simp; omega, Nat.cast_mul, Nat.cast_sub hj]
    clear h1
    generalize (n : ℤ) = N
    clear hj
    induction j with
    | zero => simp
    | succ j ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [deltaHalf_apply, torusChar_apply, Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  simp only [hd, h1]
  rw [Finset.prod_mul_distrib, hp, h2, psEig, Finset.prod_filter, Nat.cast_pow, _root_.zpow_neg, zpow_natCast]
  field_simp
end Num
end UpperTheory.V.Z.J.D.OrdinaryOrderOne
open UpperTheory.V.Z.J.D
theorem UpperTheory.V.Z.J.D.dense_threshold_order_one :
    _root_.UpperTheory.V.Z.J.D.Ord1Alt := by
  intro H k _ _ _ _ n V _ _ π hπ hirr b φ μ _ ⟨α, hα, hμ⟩
  obtain ⟨hker, hsm, -, -, -, -, -, hidx, hz, -⟩ := glBridge k n V π
  have hq : (Nat.card 𝓀[k] : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hα0 : ∀ i : Fin n, (α i : ℂ) * ((Nat.card 𝓀[k] : ℂ) ^ (i : ℕ))⁻¹ ≠ 0 := fun i =>
    mul_ne_zero (α i).ne_zero (inv_ne_zero (pow_ne_zero _ hq))
  have hL : ∀ v ∈ locEig π b φ μ, v ∈ fixd π (glIwa k n).N ∧
      ∀ j : Fin n, v ∈ ((glIwa k n).uOp π (al k n (j + 1))).maxGenEigenspace (μ j) := fun v hv =>
    ⟨hv.1.1.1, (Submodule.mem_iInf _).1 hv.2⟩
  let p : V →ₗ[ℂ] Jacquet π (unipB k (Fin n)) := Submodule.mkQ _
  have hinj : ∀ v ∈ locEig π b φ μ, p v = 0 → v = 0 := fun v hv h => by
    refine OrdinaryOrderOne.inj _ π (hsm hπ) (fun j : Fin n => al k n (j + 1)) (fun j => al_mem k n _) μ
      (fun j => by rw [hμ]; exact Finset.prod_ne_zero_iff.2 fun i _ => hα0 i) _ hz (fun x hx => ?_) (hL v hv).1 (hL v hv).2
      (hker ▸ (Submodule.Quotient.mk_eq_zero _).1 h)
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hj
    rcases j with _ | j
    · left
      rw [al, upow, ← (diagT k (Fin n)).map_one]
      congr 1
      ext i
      simp
    · exact Or.inr ⟨⟨j, by omega⟩, rfl⟩
  by_cases hne : locEig π b φ μ = ⊥
  · rw [hne, rank_bot]; exact zero_le_one
  have hp : ∀ t v, jacB π t (p v) =
      (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) t))⁻¹ : ℂˣ) : ℂ) • p (π (diagT k (Fin n) t) v) :=
    fun t v => UnramFixed.jacB_apply π t _
  let t : Fin n → Fin n → kˣ := fun j i => unif k ^ (if (i : ℕ) < j + 1 then 1 else 0 : ℤ)
  let c : Fin n → ℂ := fun j => ((Nat.card 𝓀[k] ^ ((j + 1) * (n - (j + 1))) : ℕ) : ℂ) *
    (deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) (t j)) : ℂ)
  let E : Submodule ℂ (Jacquet π (unipB k (Fin n))) :=
    ⨅ j : Fin n, Module.End.maxGenEigenspace (c j • jacB π (t j)) (μ j)
  have hEs : ∀ s, ∀ y ∈ E, jacB π s y ∈ E := fun s y hy => (Submodule.mem_iInf _).2 fun j =>
    OrdinaryOrderOne.gen_map ⊤ (jacB π s) (fun _ _ => trivial) (fun v _ => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul,
        Module.End.mul_apply]) trivial ((Submodule.mem_iInf _).1 hy j)
  have hpE : ∀ v ∈ locEig π b φ μ, p v ∈ E := fun v hv => (Submodule.mem_iInf _).2 fun j => by
    refine OrdinaryOrderOne.gen_map (fixd π (glIwa k n).N) p
      (fun w hw => (uOpMul _ _ ℂ V π _ _ (al_mem k n _) (al_mem k n 0) w hw).1) (fun w hw => ?_) (hL v hv).1 ((hL v hv).2 j)
    have h1 := propCp _ (glIwa k n) ℂ V π _ (al_mem k n (j + 1)) w hw
    rw [hker, hidx (j + 1) j.2] at h1
    have h2 : p _ = 0 := (Submodule.Quotient.mk_eq_zero _).2 h1
    rw [map_sub, map_smul, sub_eq_zero] at h2
    rw [h2, LinearMap.smul_apply, hp, smul_smul, mul_assoc, Units.mul_inv, mul_one]
    rfl
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hl : HasFiniteLength (jacB π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((H.loc.bz k).2.1 _ _ _ (points (Fin n)) _ π hπ (hasFiniteLength_of_isIrreducible hirr))
  haveI := GlobalTheory.TorusEigenform.secondCountableTopology_units k
  obtain ⟨ν, hνs, l, hl0, hle⟩ := OrdinaryOrderOne.exists_form (isSmooth_jacB hπ) hl fun h => hx0 (hinj x hx h)
  obtain ⟨ψ, hψ, rfl⟩ : ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ torusChar ψ = ν := by
    refine ⟨fun i => ν.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
      fun i => hνs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), MonoidHom.ext fun t => ?_⟩
    rw [torusChar_apply]
    conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
    rfl
  have hsq : IsSubquotient π (prinSeries ψ) := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hirr _ l hl0 hle
  obtain ⟨hfd, -, hmult⟩ := UpperTheory.V.AlgebraTools.jqMult H.loc.geo H.loc.bz k n V π ψ hπ hψ hsq
  obtain ⟨ω, rfl⟩ : ∃ ω : Fin n → kˣ →* ℂˣ, (fun i => ω i * absPow k (((n : ℂ) - 1) / 2)) = ψ :=
    ⟨fun i => ψ i * (absPow k (((n : ℂ) - 1) / 2))⁻¹, funext fun i => inv_mul_cancel_right _ _⟩
  set ψ : Fin n → kˣ →* ℂˣ := fun i => ω i * absPow k (((n : ℂ) - 1) / 2) with hψd
  have hval : ∀ w : Equiv.Perm (Fin n), (∀ j, c j * (torusChar (ψ ∘ w) (t j) : ℂ) = μ j) →
      ∀ i, ω (w i) (unif k) = α i := fun w h i => by
    refine Units.ext (mul_right_cancel₀ (inv_ne_zero (pow_ne_zero (i : ℕ) hq))
      (OrdinaryOrderOne.eq_of_prod (a := fun i => (ω (w i) (unif k) : ℂ) * ((Nat.card 𝓀[k] : ℂ) ^ (i : ℕ))⁻¹) hα0 (fun j => ?_) i))
    have h1 := OrdinaryOrderOne.num (fun i => ω (w i)) (j := j + 1) j.2
    rw [← mul_assoc] at h1
    rw [← hμ, ← h j]
    refine Eq.trans ?_ h1.symm
    simp only [psEig, Nat.lt_succ_iff, Fin.val_fin_le]
  have huniq : ∀ w w' : Equiv.Perm (Fin n), (∀ j, c j * (torusChar (ψ ∘ w) (t j) : ℂ) = μ j) →
      (∀ j, c j * (torusChar (ψ ∘ w') (t j) : ℂ) = μ j) → w = w' := fun w w' h h' => by
    refine Equiv.ext fun i => ?_
    have h1 := hval w h (w.symm (w' i))
    rw [Equiv.apply_symm_apply, hval w' h' i] at h1
    conv_lhs => rw [hα h1, Equiv.apply_symm_apply]
  have hχ : ∀ χ : (Fin n → kˣ) →* ℂˣ, ∀ y ∈ E, y ≠ 0 → (∀ s, jacB π s y = (χ s : ℂ) • y) →
      (∀ j, c j * (χ (t j) : ℂ) = μ j) ∧ ∃ w : Equiv.Perm (Fin n), χ = torusChar (ψ ∘ w) := fun χ y hy hy0 hχ => by
    refine ⟨fun j => OrdinaryOrderOne.eq_of_gen ?_ hy0 ((Submodule.mem_iInf _).1 hy j), ?_⟩
    · rw [LinearMap.smul_apply, hχ, smul_smul]
    have h1 : (⨅ t, Module.End.maxGenEigenspace (jacB π t) (χ t : ℂ) : Submodule ℂ _) ≠ ⊥ :=
      (Submodule.ne_bot_iff _).2 ⟨y, (Submodule.mem_iInf _).2 fun t =>
        (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by rw [OrdinaryOrderOne.pow_eig (hχ t)]; simp⟩, hy0⟩
    have h2 := (Nat.pos_of_ne_zero fun h => h1 (Submodule.finrank_eq_zero.1 h)).trans_le (hmult χ)
    obtain ⟨⟨w, hw⟩⟩ := (Nat.card_pos_iff.1 h2).1
    exact ⟨w, hw⟩
  obtain ⟨χ, y, hy, hy0, hχy⟩ := OrdinaryOrderOne.exists_eig (jacB π) E
    ((Submodule.ne_bot_iff _).2 ⟨_, hpE x hx, fun h => hx0 (hinj x hx h)⟩) hEs
  obtain ⟨h0, w, rfl⟩ := hχ χ y hy hy0 hχy
  have hgen : E ≤ ⨅ s, Module.End.maxGenEigenspace (jacB π s) (torusChar (ψ ∘ w) s : ℂ) := by
    refine le_iInf (OrdinaryOrderOne.le_gen _ E hEs _ fun χ y hy hy0 h => ?_)
    obtain ⟨h1, w', rfl⟩ := hχ χ y hy hy0 h
    rw [huniq w w' h0 h1]
  have hE1 : Module.finrank ℂ E ≤ 1 := by
    refine (Submodule.finrank_mono hgen).trans ((hmult _).trans ?_)
    have key : ∀ a : {w' : Equiv.Perm (Fin n) // torusChar (ψ ∘ w) = torusChar (ψ ∘ w')}, w = a.1 := fun a =>
      huniq _ _ h0 (a.2 ▸ h0)
    exact Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => Subtype.ext ((key a).symm.trans (key b))⟩
  refine (LinearMap.rank_le_of_injective (p.restrict hpE) ?_).trans ?_
  · exact (injective_iff_map_eq_zero _).2 fun v h => Subtype.ext (hinj v v.2 (congrArg Subtype.val h))
  · rw [← Module.finrank_eq_rank]
    exact_mod_cast hE1
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TZEqDimE
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.Desc.V0
private theorem ePart_zero {G R W : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W] (ρ : Representation R G W) :
    ePart ρ 0 0 = ⊤ := by
  simp [ePart, opE]
private theorem card_not_dvd {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (j : ℕ) : ¬ l ∣ Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j := by
  have hl : l.Prime := Fact.out
  have hw : (s.w s.v0).under (𝓞 (Lp L)) = s.v0 := by
    ext x
    exact (s.hw s.v0 (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA s.v0 x)
  have h2 : ((s.p : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← s.norm_v0_eq_one, normV, ← nsmul_one]
    exact card_nsmul_eq_zero'
  have h3 : ((s.p : ℕ) : 𝓞 L) ∈ (s.w s.v0).asIdeal := by
    rw [← hw] at h2
    have h4 : algebraMap (𝓞 (Lp L)) (𝓞 L) ((s.p : ℕ) : 𝓞 (Lp L)) ∈ (s.w s.v0).asIdeal := h2
    rwa [map_natCast] at h4
  have hd : Ideal.absNorm (s.w s.v0).asIdeal ∣ Ideal.absNorm (Ideal.span {((s.p : ℕ) : 𝓞 L)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h3)
  have hn : Ideal.absNorm (Ideal.span {((s.p : ℕ) : 𝓞 L)}) = s.p ^ Module.finrank ℤ (𝓞 L) := by
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 L)), Algebra.norm_algebraMap]
    simp [Int.natAbs_pow]
  rw [hn] at hd
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow s.p_prime).1 hd
  have hq : Nat.card 𝓀[(s.w s.v0).adicCompletion L] = s.p ^ e :=
    (resCard_eq_normV _).trans (by rw [normV, ← Ideal.absNorm_eq_natCard, he])
  intro h
  rw [hq] at h
  exact s.p_ne ((Nat.prime_dvd_prime_iff_eq hl s.p_prime).1 (hl.dvd_of_dvd_pow (hl.dvd_of_dvd_pow h))).symm
set_option maxHeartbeats 1600000 in
theorem z_eq_dim_e_of_count_e_res_eq_inv_loc_kir : _root_.UpperTheory.V.Z.Desc.V0.CountEAlt → _root_.UpperTheory.V.Z.J.D.ResidualEqualityRankTwo → InvEq1 → InvBox → LocE → KirCusp → _root_.UpperTheory.V.Z.Desc.V0.ZEqDimEAlt := by
  intro hCount hRes hInv hBox hLoc hKir hP hM hC l _ L Ω _ _ _ _ _ _ s n hn V hV hn4
  obtain ⟨a, j, D₀, hE, hD₀, hdim⟩ := hLoc ((s.w s.v0).adicCompletion L) n
  refine ⟨a, Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j, hE, card_not_dvd s j, ?_⟩
  intro Q c r ι m τ₀ hτ A _ _ _ θ hθ lam K D D' h h'
  obtain ⟨a₀, ha⟩ := hCount hP hM hC l L Ω s n hn V hV hn4 ι lam
  have hTeich : ∃ t, r.IsTeich t := by
    obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
    have : IsAdicComplete (maximalIdeal c.O) c.O := hc
    have : Finite (ResidueField c.O) := hfin
    have : CharP (ResidueField c.O) l := by
      refine (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 ?_
      rwa [← map_natCast (residue c.O), residue_eq_zero_iff]
    have : CharP (c.O ⧸ maximalIdeal c.O) l :=
      inferInstanceAs (CharP (ResidueField c.O) l)
    have : PerfectRing (ResidueField c.O) l := inferInstance
    let lift := Perfection.lift l (ResidueField c.O) (c.O ⧸ maximalIdeal c.O)
    let j := lift (RingHom.id (ResidueField c.O))
    let τ := (Perfection.teichmuller l (maximalIdeal c.O)).comp j.toMonoidHom
    have hτ (x : ResidueField c.O) : residue c.O (τ x) = x :=
      (Perfection.mk_teichmuller (j x)).trans
        (RingHom.congr_fun (lift.symm_apply_apply (RingHom.id (ResidueField c.O))) x)
    refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hτ _, ?_⟩⟩
    rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
  obtain ⟨t, ht⟩ := hTeich
  obtain ⟨χ, hχ, hext⟩ : ∃ χ : ∀ u : s.St, Fin n → Ine (F := L) (s.A u) →* ℂˣ, _root_.UpperTheory.V.Hi.IsTypeAlt (fun u : s.St => s.hw u)
      ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) χ ∧
      ∀ (u : s.St) (i : Fin n), ∃ ψ : Weil (s.hw u) →* ℂˣ, ∀ g, ψ (ineIncl (s.hw u) g) = χ u i g :=
    ⟨_, hτ t ht, fun u i => ⟨W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l)))
      ((t i).comp (V.pr.comp (Weil (s.hw u)).subtype)), fun _ => rfl⟩⟩
  have key : ∀ D : ℕ, _root_.UpperTheory.V.Z.Desc.V0.IsDimEAlt (hset Q τ₀) θ ι lam K (sec0 n s) a (Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j) D →
      ∃ (π : CuspSub L n) (σ : Submodule ℂ (UA L n → ℂ)) (C : Comps V σ), (∀ u : s.St, π.IsLocComp (s.w u) (C.u u)) ∧
        (∀ (u : s.St) rc, _root_.UpperTheory.Zero.LLC.IsRecT (s.hw u) rc → IsTypeWD (s.hw u) (χ u) (rc (algNorm (C.u u)))) ∧
        (D : Cardinal) = a₀ * (Module.rank ℂ (cInv1 C ι τ₀) * D₀) ∧ 1 ≤ D := by
    rintro _ ⟨x, d, ξ, c0, sp, ev, hs, hu, hz, hall, rfl⟩
    obtain ⟨e, he⟩ := hs.alg
    obtain ⟨π, σ, C, h1, h2, h3, h4, h5⟩ := ha Q c r m τ₀ hτ d e ξ he A θ x c0 sp hθ hs K ev hu hz hall
    haveI : FiniteDimensional ℂ (zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev) :=
      haveI := hs.fin K c0 le_rfl
      Submodule.finiteDimensional_of_le (S₂ := (hset Q τ₀).ClAt θ ι x.toRingHom lam ξ K c0)
        (inf_le_left.trans (iSup_le fun _ => inf_le_left))
    have hb := fun (a' : GLw n (s.w s.v0) →₀ ℤ) (N' : ℕ) => hBox _ _ _ _ (piRep fun u => (C.u u).ρ) C.o.ρ m (KT n (wt s)) (Kc _ n 1)
      ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) a' N'
    have h0 := h5 0 0 (by simp)
    have hz0 : Module.finrank ℂ ↥(zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev) ≠ 0 :=
      fun hf => hz (Submodule.finrank_eq_zero.1 hf)
    rw [show eC Q τ₀ d 0 0 = ⊤ from ePart_zero _, inf_top_eq, hb 0 0, ePart_zero, inf_top_eq] at h0
    have hne : (a₀ : Cardinal) * (Module.rank ℂ (cInv1 C ι τ₀) * Module.rank ℂ ↥(fixd C.o.ρ (Kc _ n 1))) ≠ 0 :=
      h0 ▸ Nat.cast_ne_zero.2 hz0
    have ha₀ : (a₀ : Cardinal) ≠ 0 := left_ne_zero_of_mul hne
    have hr : Module.rank ℂ (cInv1 C ι τ₀) ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hne)
    have hf : fixd C.o.ρ (Kc _ n 1) ≠ ⊥ := fun hf => right_ne_zero_of_mul (right_ne_zero_of_mul hne) (by rw [hf]; simp)
    have hd := hdim _ C.o.ρ C.o.smooth (hKir L n hn π (s.w s.v0) C.o h2) hf
    have hD := h5 a (Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j) hE.supp
    rw [hb, hd] at hD
    refine ⟨π, σ, C, h1, fun u rc hrc =>
      _root_.UpperTheory.V.Hi.partUR2Type_alt l L Ω s n hn V Q c ι m τ₀ lam d e ξ he σ h4 h3 χ hχ C.u C.hu u rc hrc, hD, ?_⟩
    refine Nat.one_le_iff_ne_zero.2 fun h0' => ?_
    rw [h0', Nat.cast_zero] at hD
    exact mul_ne_zero ha₀ (mul_ne_zero hr (Nat.cast_ne_zero.2 hD₀.ne')) hD.symm
  obtain ⟨π, σ, C, a1, a3, a5, a6⟩ := key D h
  obtain ⟨π', σ', C', b1, b3, b5, -⟩ := key D' h'
  have hr : Module.rank ℂ (cInv1 C ι τ₀) = Module.rank ℂ (cInv1 C' ι τ₀) :=
    hInv l L Ω s n hn V hV c ι m τ₀ σ σ' C C'
      (fun u => hRes hP.litN L Ω n hn π π' (s.w u) (s.A u) (s.hw u) (C.u u) (C'.u u) (a1 u) (b1 u) (χ u) (hext u) (a3 u) (b3 u))
  rw [hr, ← b5] at a5
  exact ⟨a6, Nat.cast_injective (R := Cardinal) a5⟩
end UpperTheory.V.Z.Desc.V0
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Z.J.D
namespace UpperTheory.V.Z.Desc.V0
theorem countE'_alt : _root_.UpperTheory.V.Z.Desc.V0.CountEAlt :=
  _root_.UpperTheory.V.Z.Desc.V0.count_e_of_sph_same_at_same_bc_dims wtEx (decomp indepS) (zDecE zEq normS) zEq (_root_.UpperTheory.V.Z.J.D.spherical_same_of_z_eq zEq) _root_.UpperTheory.V.Z.J.D.atSame_alt _root_.UpperTheory.V.Z.Desc.P.dense_threshold_bc_of_prop (yDimE flathE eigBoxE secSp) compsEx slope _root_.UpperTheory.V.Z.J.D.dense_threshold_order_one eigPi
theorem numJEDenseThresholdCases : _root_.UpperTheory.V.Z.Desc.V0.NumJEAlt :=
  _root_.UpperTheory.V.Z.Desc.V0.numJE_alt (muZ locSp) (muZE locSp) eEx spec2 normS
    (_root_.UpperTheory.V.Z.Desc.V0.z_eq_dim_e_of_count_e_res_eq_inv_loc_kir _root_.UpperTheory.V.Z.Desc.V0.countE'_alt (_root_.UpperTheory.V.Z.J.D.resEq2_alt _root_.UpperTheory.V.Z.J.D.typePST'_alt psRes) invEq1 invBox (locE kirMove isoNe isoLe eOp) kirCusp) unitEv _root_.UpperTheory.V.Z.J.D.partRep_s
end UpperTheory.V.Z.Desc.V0
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.J.D
theorem numJ'_alt : _root_.UpperTheory.V.Z.J.D.NumJAlt := fun hH hM hC l _ L Ω _ _ _ _ _ _ s n hn V hS h4 Q c r ι B Λ R K J _ =>
  _root_.UpperTheory.V.Z.Desc.V0.numJEDenseThresholdCases hH hM hC l L Ω s n hn V hS h4 Q c r ι B Λ R K J
theorem modularity_n_of_printed_mult_comp (hH : _root_.UpperTheory.V.Af.HypothesesH') (hM : Mult.Mult) (hC : Mult.CompOf) : _root_.UpperTheory.V.J.ModNAlt := _root_.UpperTheory.V.Z.J.D.modularity_n_of_num_j_printed_mult_comp _root_.UpperTheory.V.Z.J.D.numJ'_alt hH hM hC
end UpperTheory.V.Z.J.D
end
