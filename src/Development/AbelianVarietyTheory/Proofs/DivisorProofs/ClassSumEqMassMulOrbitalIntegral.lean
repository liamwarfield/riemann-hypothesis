module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRegroupCommutative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentraliserCompactPartLeIntegralAlmostAll

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStabiliserLeCentraliserCompactPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStabiliserLeCentraliserCompactPart
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.CentLev

theorem loc_cpt_part {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (y : UL n w) (hs : y.1.val.charpoly.Separable) :
    ∃ C : Set (UL n w), IsCompact C ∧ (cptPart (twCent (MonoidHom.id (UL n w)) y) : Set (UL n w)) ⊆ C := by
  obtain ⟨Ω, hΩ, hmem⟩ := GlobalTheory.CentCpt.main E hU n w y hs
  haveI : T2Space (GL (Fin n) (w.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
  have hc : ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y, a * b = b * a := by
    intro a ha b hb
    have ha' : a * y = y * a := ha
    have hb' : b * y = y * b := hb
    have hav : (a : GLw n w).val * (y : GLw n w).val = (y : GLw n w).val * (a : GLw n w).val := by
      have := congrArg (fun z : UL n w => (z : GLw n w).val) ha'; simpa using this
    have hbv : (b : GLw n w).val * (y : GLw n w).val = (y : GLw n w).val * (b : GLw n w).val := by
      have := congrArg (fun z : UL n w => (z : GLw n w).val) hb'; simpa using this
    have := GlobalTheory.commute_of_commute_separable_charpoly _ n _ _ _ hs hav hbv
    apply Subtype.ext; apply Units.ext; simpa using this
  refine ⟨Ω, hΩ, fun z hz => ?_⟩
  obtain ⟨hzT, hzc⟩ := GlobalTheory.LocFinU.cptPart_subset_of_comm _ hc hz
  exact hmem z hzT hzc

theorem stab_le_cptPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ x : finU (E := E) (n := n), twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ) ⊓ (globLev S (KL n)).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ)) ∧ (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ) ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ))) ≠ 0 := by
  intro E _ _ _ hU n hn S hS K' hK' γ hγ x
  set δ : finU (E := E) (n := n) := finPt γ with hδ
  set T := twCent (MonoidHom.id (finU (E := E) (n := n))) δ with hT
  let ρ : ∀ w : Pl E, finU (E := E) (n := n) →* UL n w := fun w =>
    { toFun := fun z => ⟨cLoc w (z : UA E n), GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hρv : ∀ w z, ((ρ w z : UL n w) : GLw n w) = cLoc w (z : UA E n) := fun _ _ => rfl
  have hρc : ∀ w, Continuous (ρ w) := fun w =>
    continuous_induced_rng.2 ((GlobalTheory.DefU.Inert.continuous_cLoc w).comp continuous_subtype_val)
  have hδw : ∀ w, ((ρ w δ : UL n w) : GLw n w) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
    intro w
    rw [hρv, hδ, FinPtLoc.finPt_eq]
    apply Units.ext
    refine Matrix.ext fun i j => ?_
    change pLoc E w (pFin E ((finGL E n (ratF E n γ.1)).val i j)) = algebraMap E _ (γ.1.val i j)
    rw [FinPtLoc.snd_entry]
    rfl
  have hsep : ∀ w, ((ρ w δ : UL n w) : GLw n w).val.charpoly.Separable := by
    intro w
    rw [hδw]
    have e : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val = γ.1.val.map (algebraMap E _) := rfl
    rw [e, Matrix.charpoly_map]
    exact hγ.map
  have hsetK : ∀ K'' : ∀ w : Pl E, Subgroup (UL n w), (globLev S K'' : Set (finU (E := E) (n := n))) =
      {z : finU (E := E) (n := n) | ∀ w ∈ S, toSub (UL n w) (cLoc w (z : UA E n)) ∈ (K'' w : Set (UL n w))} := by
    intro K''
    ext z
    simp only [SetLike.mem_coe, Set.mem_setOf_eq, globLev, Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map,
      MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    refine forall₂_congr fun w _ => ?_
    rw [FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]
    constructor
    · rintro ⟨a, ha, e⟩
      have : a = ⟨_, GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w (z : UA E n)⟩ := Subtype.ext e
      rwa [← this]
    · intro h
      exact ⟨_, h, rfl⟩
  have hKc : IsCompact (globLev S (KL n) : Set (finU (E := E) (n := n))) := by
    rw [hsetK]
    exact GlobalTheory.BCT.LocCpt.loc_cpt E hU n S hS (fun w => (KL n w : Set (UL n w)))
      (fun w => (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2) (Filter.Eventually.of_forall fun _ => rfl)
  have hcf : ⇑((MulAut.conj x).toMonoidHom) = fun g : finU (E := E) (n := n) => x * g * x⁻¹ := by
    ext g; simp
  have hconj : ∀ H : Subgroup (finU (E := E) (n := n)), (H.map (MulAut.conj x).toMonoidHom : Set (finU (E := E) (n := n))) =
      (fun g => x⁻¹ * g * x) ⁻¹' (H : Set (finU (E := E) (n := n))) := by
    intro H; ext g
    rw [Subgroup.coe_map, hcf]
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa [mul_assoc] using hk
    · intro h
      exact ⟨_, h, by group⟩
  refine ⟨?_, ?_⟩
  · rintro t ⟨htT, htK⟩
    apply Subgroup.subset_closure
    refine ⟨htT, ?_⟩
    have hKx : IsCompact ((globLev S (KL n)).map (MulAut.conj x).toMonoidHom : Set (finU (E := E) (n := n))) := by
      rw [Subgroup.coe_map, hcf]
      exact hKc.image (by fun_prop)
    set_option synthInstance.maxHeartbeats 200000 in
      exact hKx.closure_of_subset fun s hs => Subgroup.zpowers_le.2 htK hs
  · have hUo : IsOpen ((globLev S K').map (MulAut.conj x).toMonoidHom : Set (finU (E := E) (n := n))) := by
      rw [hconj]
      exact (GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hU n S K' hK').preimage (by fun_prop)
    choose C0 hC0c hC0 using fun w => loc_cpt_part hU n w (ρ w δ) (hsep w)
    have hcof := GlobalTheory.T.centraliser_compactPart_le_integral_almostAll E hU n γ hγ
    let C : ∀ w : Pl E, Set (UL n w) := fun w =>
      if cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w then (KL n w : Set (UL n w)) else C0 w
    have hCc : ∀ w, IsCompact (C w) := by
      intro w
      by_cases h : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w
      · simp only [C, if_pos h]; exact (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2
      · simp only [C, if_neg h]; exact hC0c w
    have hCK : ∀ᶠ w in cofinite, C w = KL n w := by
      filter_upwards [hcof] with w hw
      have e : ρ w δ = locPt w γ := by
        rw [← GlobalTheory.BCT.locPt_finPt E hU n γ w, FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]
        rfl
      have hw' : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w := by rw [e]; exact hw
      simp only [C, if_pos hw']
    have hsub : ∀ w, (cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) : Set (UL n w)) ⊆ C w := by
      intro w
      by_cases h : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w
      · simp only [C, if_pos h]; exact h
      · simp only [C, if_neg h]; exact hC0 w
    have hD := GlobalTheory.BCT.LocCpt.loc_cpt E hU n S hS C hCc hCK
    have hle : cptPart T ≤ ⨅ w : Pl E, (cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ))).comap (ρ w) := by
      rw [cptPart, Subgroup.closure_le]
      rintro t ⟨htT, htc⟩
      rw [SetLike.mem_coe, Subgroup.mem_iInf]
      intro w
      rw [Subgroup.mem_comap]
      apply Subgroup.subset_closure
      refine ⟨?_, ?_⟩
      · have ht' : t * δ = δ * t := htT
        show ρ w t * ρ w δ = ρ w δ * (MonoidHom.id _) (ρ w t)
        rw [MonoidHom.id_apply, ← map_mul, ht', map_mul]
      · have himc : IsCompact (ρ w '' closure (Subgroup.zpowers t : Set (finU (E := E) (n := n)))) := htc.image (hρc w)
        refine himc.closure_of_subset ?_
        rintro _ ⟨k, rfl⟩
        exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
    have hTD : (cptPart T : Set (finU (E := E) (n := n))) ⊆
        {z : finU (E := E) (n := n) | ∀ w ∈ S, toSub (UL n w) (cLoc w (z : UA E n)) ∈ C w} := by
      intro z hz w _
      have hzw := Subgroup.mem_iInf.1 (hle hz) w
      rw [Subgroup.mem_comap] at hzw
      rw [FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]
      exact hsub w hzw
    have hUo' : IsOpen ((((globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) : Subgroup _) :
        Set (cptPart T)) := by
      rw [Subgroup.coe_subgroupOf]
      exact hUo.preimage continuous_subtype_val
    have hfi := GlobalTheory.LocVec.finiteIndex_of_isOpen (cptPart T) hD hTD _ hUo'
    have hTc : cptPart T ≤ T := (Subgroup.closure_le T).2 fun t ht => ht.1
    have heq : (T ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) =
        ((globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) := by
      ext z
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hTc z.2, h⟩⟩
    rw [Subgroup.relIndex, heq]
    exact hfi.index_ne_zero

end GlobalTheory.BCT.CentLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStabiliserLeCentraliserCompactPartStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_stabiliser_le_centraliser_compact_part : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ x : finU (E := E) (n := n), twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ) ⊓ (globLev S (KL n)).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ)) ∧ (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ) ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ))) ≠ 0 := by
  first | exact @GlobalTheory.BCT.CentLev.stab_le_cptPart | exact GlobalTheory.BCT.CentLev.stab_le_cptPart | (intros; apply GlobalTheory.BCT.CentLev.stab_le_cptPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularRationalPointTestSupportDoubleCosetsFinit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryConjOfCharpolyEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryConjOfCharpolyEq
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.IntUnitConj

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P.Separable →
    ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ y y' : UL n w, y ∈ KL n w → y' ∈ KL n w → y.1.val.charpoly = atPl w P →
      y'.1.val.charpoly = atPl w P → ∃ g ∈ KL n w, y' = g⁻¹ * y * g := by
  intro E _ _ _ hU n P hP
  filter_upwards [UnitInert.eventually_separable P hP] with w hsep γ γ' hγK hγ'K hγ hγ'
  let O := w.adicCompletionIntegers E
  let ι := algebraMap O (w.adicCompletion E)
  have hι : Function.Injective ι := Subtype.val_injective
  change γ.1 ∈ (GeneralLinearGroup.map ι).range at hγK
  change γ'.1 ∈ (GeneralLinearGroup.map ι).range at hγ'K
  obtain ⟨y', hy'⟩ := hγK
  obtain ⟨z', hz'⟩ := hγ'K
  have hch : ∀ x : GL (Fin n) O, x.val.charpoly.map ι = (GeneralLinearGroup.map ι x).val.charpoly := fun x =>
    (Matrix.charpoly_map _ _).symm
  have e1 : y'.val.charpoly.map ι = atPl w P := by rw [hch, hy', hγ]
  have e2 : z'.val.charpoly.map ι = atPl w P := by rw [hch, hz', hγ']
  have e12 : z'.val.charpoly = y'.val.charpoly := Polynomial.map_injective ι hι (e2.trans e1.symm)
  suffices H : ∃ u : GL (Fin n) O, GeneralLinearGroup.map ι u ∈ UL n w ∧ y'.val * u.val = u.val * z'.val by
    obtain ⟨u, hu, hcu⟩ := H
    let g : GLw n w := GeneralLinearGroup.map ι u
    have key : γ.1 * g = g * γ'.1 := by
      rw [← hy', ← hz', ← map_mul, ← map_mul]
      congr 1
      exact Units.ext hcu
    refine ⟨⟨g, hu⟩, Subgroup.mem_subgroupOf.2 ⟨u, rfl⟩, Subtype.ext ?_⟩
    change γ'.1 = g⁻¹ * γ.1 * g
    rw [mul_assoc, key, inv_mul_cancel_left]
  by_cases hw : IsSplitAt w
  · obtain ⟨u, hu⟩ := GlobalTheory.ConjLocal.conj_of_charpoly_local O n y'.val z'.val e12.symm (hsep _ e1)
    refine ⟨u, by rw [UL, if_pos hw]; exact Subgroup.mem_top _, ?_⟩
    rw [hu, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  · obtain ⟨-, hcc, hv, h4, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨ϖ, q, ⟨-, -, -, -, ⟨x₀, hx₀, hx₁⟩, hq2, hcard⟩, -⟩ := (h4 hw).2.1
    have hcard' : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = q ^ 2 := hcard
    haveI := GlobalTheory.HenselSquare.isAdicComplete_integers E w
    haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
      Nat.finite_of_card_ne_zero (by rw [hcard']; positivity)
    let c : O →+* O := (cj w).restrict _ _ (ThBasic.cj_mem_integers hU w)
    have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hcc _)
    have hmapc : ∀ M : Matrix (Fin n) (Fin n) O, (cT c M).map ι = cT (cj w) (M.map ι) := fun M => by
      ext i j; rfl
    have hUL : ∀ x : GLw n w, x ∈ UL n w ↔ cT (cj w) x.val * x.val = 1 := fun x => by
      rw [UL, if_neg hw]
      change cT (cj w) x.val * 1 * x.val = 1 ↔ _
      rw [mul_one]
    have hmv : ∀ x : GL (Fin n) O, (GeneralLinearGroup.map ι x).val = x.val.map ι := fun x => by
      ext i j; rfl
    have hunit : ∀ (x : GL (Fin n) O), GeneralLinearGroup.map ι x ∈ UL n w → cT c x.val * x.val = 1 := fun x hx => by
      refine Matrix.map_injective hι ?_
      show (cT c x.val * x.val).map ι = (1 : Matrix (Fin n) (Fin n) O).map ι
      rw [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι), ← hmv]
      exact (hUL _).1 hx
    obtain ⟨u, hu, hcu⟩ := UnitInert.exists_unitary_conj (IsLocalRing.maximalIdeal O) (σ := c) hc
      (fun x hx => by
        rw [GlobalTheory.InertUQ.mem_max_iff] at hx ⊢
        exact (hv _).trans_lt hx)
      ⟨⟨x₀, hx₀⟩, by
        rw [← IsLocalRing.notMem_maximalIdeal, GlobalTheory.InertUQ.mem_max_iff]
        change ¬ Valued.v (x₀ - cj w x₀) < 1
        rw [Valuation.map_sub_swap, hx₁]
        exact lt_irrefl _⟩
      (hunit y' (hy' ▸ γ.2)) (hunit z' (hz' ▸ γ'.2)) (hsep _ e1) e12
    refine ⟨u, ?_, hcu⟩
    rw [hUL]
    have := congrArg (fun M => M.map ι) hu
    simp only [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι)] at this
    exact this

end GlobalTheory.BCT.IntUnitConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryConjOfCharpolyEqStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integralUnitary_conj_of_charpoly_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P.Separable → ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ y y' : UL n w, y ∈ KL n w → y' ∈ KL n w → y.1.val.charpoly = atPl w P → y'.1.val.charpoly = atPl w P → ∃ g ∈ KL n w, y' = g⁻¹ * y * g := by
  exact @GlobalTheory.BCT.IntUnitConj.main
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularRationalPointTestSupportDoubleCosetsFinit
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.ClsSupp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cLoc_mem_UL' (w : Pl E) (x : UA E n) : cLoc w x ∈ UL n w := by
  by_cases hsp : IsSplitAt w
  · unfold UL; rw [if_pos hsp]; trivial
  · exact GlobalTheory.LocInj.cLoc_mem_UL hsp x

def cw (w : Pl E) : finU (E := E) (n := n) →* UL n w where
  toFun x := ⟨cLoc w (x : UA E n), cLoc_mem_UL' w _⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

theorem toSub_eq (w : Pl E) (x : finU (E := E) (n := n)) : toSub (UL n w) (cLoc w (x : UA E n)) = cw w x :=
  dif_pos (cLoc_mem_UL' w _)

theorem cw_val (w : Pl E) (x : finU (E := E) (n := n)) : (cw w x).1 = cLoc w (x : UA E n) := rfl

theorem ne_zero_of_finprod {S : Set (Pl E)} {g : Pl E → ℂ} (hg : ∀ᶠ w in cofinite, g w = 1)
    (h : ∏ᶠ w ∈ S, g w ≠ 0) : ∀ w ∈ S, g w ≠ 0 := by
  intro w₀ hw₀ h₀
  apply h
  rw [finprod_mem_def]
  refine finprod_eq_zero (S.mulIndicator g) w₀ (by rw [Set.mulIndicator_of_mem hw₀, h₀]) ?_
  show (Function.mulSupport _).Finite
  rw [Set.mulSupport_mulIndicator]
  exact (Filter.eventually_cofinite.1 hg).subset Set.inter_subset_right

end GlobalTheory.BCT.ClsSupp


open GlobalTheory.BCT.ClsSupp in
theorem GlobalTheory.BCT.ClsSupp.finite_supp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ) : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n))) | globFn S f ((Quotient.out q)⁻¹ * finPt γ * (MonoidHom.id (finU (E := E) (n := n))) (Quotient.out q)) ≠ 0}.Finite := by
  intro E _ _ _ hU n hn S hS K' hK' f hf γ hγ
  set δ := finPt γ with hδ
  have hych : ∀ w, (cw w δ).1.val.charpoly = atPl w γ.1.val.charpoly := fun w =>
    by rw [cw_val, RegVan.cLoc_finPt_val, Matrix.charpoly_map]
  have hysep : ∀ w, (cw w δ).1.val.charpoly.Separable := fun w => by rw [hych]; exact hγ.map
  have hconj : ∀ (w : Pl E) (x : finU (E := E) (n := n)),
      cw w (x⁻¹ * δ * (MonoidHom.id (finU (E := E) (n := n))) x) = (cw w x)⁻¹ * cw w δ * cw w x := by
    intro w x; simp [map_mul, map_inv]

  have hsupp : ∀ x : finU (E := E) (n := n), globFn S f x ≠ 0 → ∀ w ∈ S, f w (cw w x) ≠ 0 := by
    intro x hx
    refine ne_zero_of_finprod (g := fun w => f w (cw w x)) ?_ ?_
    · filter_upwards [RegVan.eventually_toSub_mem x, hf.2] with w a b
      rw [toSub_eq] at a
      rw [b, Set.indicator_of_mem a]; rfl
    · have e : globFn S f x = ∏ᶠ w ∈ S, f w (cw w x) := by
        unfold globFn; simp only [toSub_eq]
      rwa [← e]

  have hinvar : ∀ w, ∀ k ∈ K' w, ∀ z, f w (k⁻¹ * z * k) = f w z := by
    intro w k hk z
    rw [mul_assoc, ((hf.1 w).2 k⁻¹ (inv_mem hk) (z * k)).1, ((hf.1 w).2 k hk z).2]
  have hLfin : ∀ w, {p : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) (cw w δ) : Set (UL n w)) (K' w : Set (UL n w)) |
      (Quotient.out p)⁻¹ * cw w δ * Quotient.out p ∈ tsupport (f w)}.Finite := fun w =>
    (GlobalTheory.T.unitary_local_finiteness_regular_semisimple_centralizer E hU n w (cw w δ) (hysep w) (K' w) (hK'.1 w)).2 _ (hf.1 w).1.isCompact
  have hloc : ∀ w (g : UL n w), f w (g⁻¹ * cw w δ * g) ≠ 0 →
      (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) (cw w δ)) (K' w) g))⁻¹ * cw w δ *
        Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) (cw w δ)) (K' w) g) ∈ tsupport (f w) := by
    intro w g hg
    obtain ⟨h, hh, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id (UL n w)) (cw w δ)) (K' w) g
    rw [he]
    apply subset_tsupport
    have hh' : h * cw w δ = cw w δ * h := hh
    have e : (h * g * k)⁻¹ * cw w δ * (h * g * k) = k⁻¹ * (g⁻¹ * cw w δ * g) * k := by
      calc (h * g * k)⁻¹ * cw w δ * (h * g * k) = k⁻¹ * (g⁻¹ * (h⁻¹ * (h * cw w δ)) * g) * k := by
            rw [hh']; group
        _ = _ := by rw [inv_mul_cancel_left]
    rw [Function.mem_support, e, hinvar w k hk]; exact hg

  have hgood : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ g : UL n w, f w (g⁻¹ * cw w δ * g) ≠ 0 →
      ∃ a ∈ twCent (MonoidHom.id (UL n w)) (cw w δ), ∃ k ∈ K' w, g = a * k := by
    filter_upwards [hf.2, hK'.2, RegVan.eventually_toSub_mem δ, GlobalTheory.T.eventually_integralUnitary_conj_of_charpoly_eq E hU n _ hγ] with w hfw hKw hyK hcK
    intro g hg
    rw [hfw] at hg
    have hz : g⁻¹ * cw w δ * g ∈ KL n w := by
      by_contra h; exact hg (Set.indicator_of_notMem h _)
    rw [toSub_eq] at hyK
    have hzc : (g⁻¹ * cw w δ * g).1.val.charpoly = atPl w γ.1.val.charpoly := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
        Matrix.charpoly_units_conj', hych]
    obtain ⟨k, hk, hke⟩ := hcK (cw w δ) _ hyK hz (hych w) hzc
    refine ⟨g * k⁻¹, ?_, k, by rw [hKw]; exact hk, by group⟩
    show g * k⁻¹ * cw w δ = cw w δ * (MonoidHom.id (UL n w)) (g * k⁻¹)
    rw [MonoidHom.id_apply]
    calc g * k⁻¹ * cw w δ = g * (k⁻¹ * cw w δ * k) * k⁻¹ := by group
      _ = g * (g⁻¹ * cw w δ * g) * k⁻¹ := by rw [hke]
      _ = cw w δ * (g * k⁻¹) := by group
  set B : Set (Pl E) := {w | w ∈ S ∧ ¬ ∀ g : UL n w, f w (g⁻¹ * cw w δ * g) ≠ 0 →
      ∃ a ∈ twCent (MonoidHom.id (UL n w)) (cw w δ), ∃ k ∈ K' w, g = a * k} with hBdef
  have hB : B.Finite := (Filter.eventually_cofinite.1 hgood).subset fun w hw => hw.2
  have hBg : ∀ w ∈ S, w ∉ B → ∀ g : UL n w, f w (g⁻¹ * cw w δ * g) ≠ 0 →
      ∃ a ∈ twCent (MonoidHom.id (UL n w)) (cw w δ), ∃ k ∈ K' w, g = a * k := fun w hw hwB =>
    by_contra fun h => hwB ⟨hw, h⟩
  haveI : Finite B := hB.to_subtype
  have hq0 : ∀ q : DoubleCoset.Quotient (twCent (MonoidHom.id (finU (E := E) (n := n))) δ : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n))),
      globFn S f ((Quotient.out q)⁻¹ * δ * (MonoidHom.id (finU (E := E) (n := n))) (Quotient.out q)) ≠ 0 → ∀ w ∈ S,
      f w ((cw w (Quotient.out q))⁻¹ * cw w δ * cw w (Quotient.out q)) ≠ 0 := fun q hq w hw => by
    rw [← hconj]; exact hsupp _ hq w hw
  let Φ := fun (q : DoubleCoset.Quotient (twCent (MonoidHom.id (finU (E := E) (n := n))) δ : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n))))
      (w : B) => DoubleCoset.mk (twCent (MonoidHom.id (UL n (w : Pl E))) (cw (w : Pl E) δ)) (K' w) (cw (w : Pl E) (Quotient.out q))
  refine Set.Finite.of_finite_image (f := Φ) ?_ ?_
  · refine (Set.Finite.pi fun w : B => hLfin (w : Pl E)).subset ?_
    rintro _ ⟨q, hq, rfl⟩
    exact Set.mem_univ_pi.2 fun w => hloc w _ (hq0 q hq w w.2.1)
  · intro q hq q' hq' he
    have hloc' : ∀ w ∈ S, ∃ t ∈ twCent (MonoidHom.id (UL n w)) (cw w δ), ∃ k ∈ K' w,
        cw w (Quotient.out q') = t * cw w (Quotient.out q) * k := by
      intro w hw
      by_cases hwB : w ∈ B
      · exact (@DoubleCoset.eq _ _ _ _ _ _).1 (congrFun he ⟨w, hwB⟩)
      · obtain ⟨a, ha, k, hk, hak⟩ := hBg w hw hwB _ (hq0 q hq w hw)
        obtain ⟨a', ha', k', hk', hak'⟩ := hBg w hw hwB _ (hq0 q' hq' w hw)
        refine ⟨a' * a⁻¹, mul_mem ha' (inv_mem ha), k⁻¹ * k', mul_mem (inv_mem hk) hk', ?_⟩
        rw [hak, hak']; group
    have hex : ∀ w : Pl E, ∃ t k : UL n w, t ∈ twCent (MonoidHom.id (UL n w)) (cw w δ) ∧ k ∈ K' w ∧
        (w ∈ S → cw w (Quotient.out q') = t * cw w (Quotient.out q) * k) ∧ (w ∉ S → t = 1) := by
      intro w
      by_cases hw : w ∈ S
      · obtain ⟨t, ht, k, hk, he⟩ := hloc' w hw
        exact ⟨t, k, ht, hk, fun _ => he, fun h => absurd hw h⟩
      · exact ⟨1, 1, one_mem _, one_mem _, fun h => absurd h hw, fun _ => rfl⟩
    choose t k ht hk hte ht1 using hex
    have hKle : ∀ w, K' w ≤ KL n w := fun w => (hK'.1 w).2.1
    have htint : ∀ᶠ w in (cofinite : Filter (Pl E)), t w ∈ KL n w := by
      filter_upwards [RegVan.eventually_toSub_mem (Quotient.out q), RegVan.eventually_toSub_mem (Quotient.out q')]
        with w a b
      rw [toSub_eq] at a b
      by_cases hw : w ∈ S
      · have e : t w = cw w (Quotient.out q') * (k w)⁻¹ * (cw w (Quotient.out q))⁻¹ := by rw [hte w hw]; group
        rw [e]; exact mul_mem (mul_mem b (inv_mem (hKle w (hk w)))) (inv_mem a)
      · rw [ht1 w hw]; exact one_mem _
    obtain ⟨tt, htt⟩ := exists_finU_of_loc E hU n S hS t htint
    obtain ⟨kk, hkk⟩ := exists_finU_of_loc E hU n S hS k (Filter.Eventually.of_forall fun w => hKle w (hk w))
    simp only [toSub_eq] at htt hkk
    have httT : tt ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) δ := by
      show tt * δ = δ * (MonoidHom.id (finU (E := E) (n := n))) tt
      apply finU_eq_of_loc E hU n S hS
      intro w hw
      have h1 : t w * cw w δ = cw w δ * (MonoidHom.id (UL n w)) (t w) := ht w
      simp only [toSub_eq, MonoidHom.id_apply, map_mul, htt w hw] at h1 ⊢
      exact h1
    have hkkK : kk ∈ globLev S K' := by
      simp only [globLev, Subgroup.mem_iInf]
      intro w hw
      rw [Subgroup.mem_comap]
      exact ⟨k w, hk w, by rw [← hkk w hw]; rfl⟩
    have hgg : Quotient.out q' = tt * Quotient.out q * kk := by
      apply finU_eq_of_loc E hU n S hS
      intro w hw
      simp only [toSub_eq, map_mul, htt w hw, hkk w hw]
      exact hte w hw
    rw [← DoubleCoset.out_eq' q,
      ← DoubleCoset.out_eq' q', DoubleCoset.eq]
    exact ⟨tt, httT, kk, hkkK, hgg⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularRationalPointTestSupportDoubleCosetsFinitStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularRationalPoint_testSupport_doubleCosets_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ) : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n))) | globFn S f ((Quotient.out q)⁻¹ * finPt γ * (MonoidHom.id (finU (E := E) (n := n))) (Quotient.out q)) ≠ 0}.Finite := by
  first | exact @GlobalTheory.BCT.ClsSupp.finite_supp | exact GlobalTheory.BCT.ClsSupp.finite_supp | (intros; apply GlobalTheory.BCT.ClsSupp.finite_supp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumEqMassMulOrbitalIntegral
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.ClsOrb

theorem clsSum_eq_mass_mul_twOrb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → clsSum S K' f γ = mass (MonoidHom.id _) (ratFinU E n) (finPt γ) * twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f) := by
  intro E _ _ _ hU n hn S hS lam K' hK' f hf γ hγ
  obtain ⟨hKo, hKc, hlev⟩ := GlobalTheory.T.productOfLocalLevelsUnitary_isOpen_isCompact_isLevel E hU n hn S hS K' hK'
  have hH := GlobalTheory.T.isHecke_productOfLocalTestFunctions_section E hU n hn S hS K' hK' f hf
  have hcomm := GlobalTheory.T.centralizer_regular_rationalPoint_finiteAdelic_comm E n γ hγ
  have hcpt := GlobalTheory.T.level_stabiliser_le_centraliser_compact_part E hU n hn S hS K' hK' γ hγ
  have hsupp := GlobalTheory.T.regularRationalPoint_testSupport_doubleCosets_finite E hU n hn S hS K' hK' f hf γ hγ
  have horb := GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel (finU (E := E) (n := n)) (MonoidHom.id _) (globLev S (KL n)) hKo hKc
    (fun k hk => hk) (globLev S K') hlev (finPt γ) (globFn S f) hH hcpt hsupp
  set T := twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ) with hT
  have hCT : cptPart T ≤ T := (Subgroup.closure_le T).2 fun t ht => ht.1
  have hU' : ∀ x : finU (E := E) (n := n), T ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom ≤ cptPart T ∧
      (T ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).relIndex (cptPart T) ≠ 0 := fun x =>
    ⟨le_trans (inf_le_inf_left _ (Subgroup.map_mono hlev.2.1)) (hcpt x).1, (hcpt x).2⟩
  have hinv : ∀ t ∈ T, ∀ k ∈ globLev S K', ∀ x : finU (E := E) (n := n),
      globFn S f ((t * x * k)⁻¹ * finPt γ * (t * x * k)) = globFn S f (x⁻¹ * finPt γ * x) := by
    intro t ht k hk x
    have ht' : t * finPt γ = finPt γ * t := ht
    have e1 : t⁻¹ * finPt γ * t = finPt γ := by
      rw [mul_assoc, ← ht', ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 : (t * x * k)⁻¹ * finPt γ * (t * x * k) = k⁻¹ * (x⁻¹ * (t⁻¹ * finPt γ * t) * x) * k := by group
    rw [e2, e1, mul_assoc, (hH.2 k⁻¹ (inv_mem hk) _).1, (hH.2 k hk _).2]
  have hreg := GlobalTheory.T.finsum_doubleCoset_regroup_commutative (finU (E := E) (n := n)) T (ratFinU E n) (cptPart T) (globLev S K')
    (fun x => globFn S f (x⁻¹ * finPt γ * x)) hcomm hCT hU' hinv
  simp only [MonoidHom.id_apply] at horb
  rw [clsSum, horb.1, horb.2, hreg, mass]
  ring

end GlobalTheory.BCT.ClsOrb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumEqMassMulOrbitalIntegralStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_eq_mass_mul_orbitalIntegral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → clsSum S K' f γ = mass (MonoidHom.id _) (ratFinU E n) (finPt γ) * twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f) := by
  first | exact @GlobalTheory.BCT.ClsOrb.clsSum_eq_mass_mul_twOrb | exact GlobalTheory.BCT.ClsOrb.clsSum_eq_mass_mul_twOrb | (intros; apply GlobalTheory.BCT.ClsOrb.clsSum_eq_mass_mul_twOrb <;> assumption)
end
