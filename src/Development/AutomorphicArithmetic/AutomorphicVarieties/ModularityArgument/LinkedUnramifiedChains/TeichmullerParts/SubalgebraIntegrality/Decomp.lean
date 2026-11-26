module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNondegenerateRightInvariantFormOfCompactQu
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNormVEqPrimePowLeFinrank
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsEquivariantProjectionsOfSumIrreducible
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemISupAutomorphicRepsOfInvariantForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreSep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeOperatorsCommuteOnAutomorphicForms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelFiniteSumFixedVectors

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.DecompC
noncomputable section

section Conj

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem UpperTheory.V.Z.J.D.Dc.int_conj (x : UA E n) (u : Pl E)
    (h : cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) u) x ∈ GlobalTheory.LFun.KGL (conjSrc (GlobalTheory.SplitPts.conjE E) u) (n := n)) :
    cLoc u x ∈ GlobalTheory.LFun.KGL u (n := n) := by
  have h1 := GlobalTheory.BCT.LocGlue.intst E n _ u (conjLoc (GlobalTheory.SplitPts.conjE E) u) (conjLoc_spec _ u).2.2 _ h
  have e : cLoc u x = GlobalTheory.CuspRep.invT n _ (GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) u)
      (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) u) x)) := by
    have hce := GlobalTheory.SplitPts.comp_eq x u
    generalize hB : GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) u)
      (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) u) x) = B
    have hB' : (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) u) x).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u) = B.val := by
      rw [← hB]
      rfl
    rw [hB'] at hce
    apply Units.ext
    change (cLoc u x).val = ((B⁻¹ : GL (Fin n) _).val)ᵀ
    have h2 : ((B⁻¹ : GL (Fin n) _).val)ᵀ * (B.val)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    calc (cLoc u x).val = (((B⁻¹ : GL (Fin n) _).val)ᵀ * (B.val)ᵀ) * (cLoc u x).val := by rw [h2, Matrix.one_mul]
      _ = ((B⁻¹ : GL (Fin n) _).val)ᵀ := by rw [Matrix.mul_assoc, hce, Matrix.mul_one]
  rw [e]
  exact h1

theorem UpperTheory.V.Z.J.D.Dc.int_over {w u : Pl E}
    (hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) (x : UA E n)
    (h : cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n)) : cLoc u x ∈ GlobalTheory.LFun.KGL u (n := n) := by
  by_cases e : u = w
  · subst e
    exact h
  · rcases (GlobalTheory.SplitPts.over_split (w := w) ⟨u, e, hu⟩).2.2 u hu with rfl | rfl
    · exact h
    · refine UpperTheory.V.Z.J.D.Dc.int_conj x _ ?_
      have e2 : ∀ v, v = w → cLoc v x ∈ GlobalTheory.LFun.KGL v (n := n) := by
        rintro v rfl
        exact h
      exact e2 _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w)

end Conj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D.Dc

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω]

theorem unrOf (s : HidaSetting l L Ω) : GlobalTheory.BCT.Unr L := fun w => by
  haveI : IsGalois (Lp L) L := inferInstance
  have h := GlobalTheory.RayFromArtin.unramIn_of_ine (K := Lp L) (Ω := Ω) L (v := w.under (𝓞 (Lp L))) fun A hA σ hσ => by
    obtain ⟨g, rfl⟩ := s.unr A _ hA hσ
    ext x
    apply (algebraMap L Ω).injective
    exact (AlgEquiv.restrictNormal_commutes (W.resP L Ω g) L x).trans (g.commutes x)
  have hb : w.asIdeal.inertia Gal(L/Lp L) = ⊥ := by
    rw [eq_bot_iff]
    intro τ hτ
    exact h τ ⟨w.asIdeal, w.isPrime, ⟨rfl⟩, hτ⟩
  have h1 := UpperTheory.V.CF.ineCard.1 (Lp L) L w
  rw [hb, Subgroup.card_bot] at h1
  haveI := w.isPrime
  haveI := w.isMaximal
  haveI : (w.asIdeal.under (𝓞 (Lp L))).IsMaximal := Ideal.IsMaximal.under _ _
  exact Ideal.ramificationIdx_eq_one_iff.1 h1.symm

theorem under_w (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

theorem secRange (s : HidaSetting l L Ω) : GlobalTheory.BCT.IsSection (Set.range s.w) := fun w => by
  refine ⟨s.w (w.under (𝓞 (Lp L))), ⟨⟨_, rfl⟩, under_w s _⟩, ?_⟩
  rintro _ ⟨⟨v, rfl⟩, h⟩
  have e : v = w.under (𝓞 (Lp L)) := (under_w s v).symm.trans h
  rw [e]


open Classical in
def Pc (s : HidaSetting l L Ω) (n c : ℕ) (w : Plc L) : Subgroup (GLw n w) :=
  if w ∈ s.w '' s.S then Kc _ n c else GlobalTheory.LFun.KGL w (n := n)

def Kf (s : HidaSetting l L Ω) (n c : ℕ) (w : GlobalTheory.BCT.Pl L) : Subgroup (GlobalTheory.BCT.UL n w) :=
  (Pc s n c w).subgroupOf (GlobalTheory.BCT.UL n w)

variable (s : HidaSetting l L Ω) (n c : ℕ)

theorem Pc_le (w : Plc L) : Pc s n c w ≤ GlobalTheory.LFun.KGL w (n := n) := by
  unfold Pc
  split_ifs
  · rw [GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel.kgl_eq_ko]
    exact UpperTheory.V.Hi.GlAx.Kc_le c
  · exact le_rfl

theorem Pc_open (w : Plc L) : IsOpen (Pc s n c w : Set (GLw n w)) := by
  unfold Pc
  split_ifs
  · exact (UpperTheory.unitaryAdelic_localComponents_continuous_levels_open L n).2.1 w c
  · rw [GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel.kgl_eq_ko, ← UpperTheory.V.Hi.GlAx.Kc_zero]
    exact (UpperTheory.unitaryAdelic_localComponents_continuous_levels_open L n).2.1 w 0

variable {s n c}

theorem Pc_notS {w : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ s.S) : Pc s n c w = GlobalTheory.LFun.KGL w (n := n) := by
  unfold Pc
  refine if_neg ?_
  rintro ⟨v, hv, rfl⟩
  exact hw ((under_w s v).symm ▸ hv)

theorem Pc_S {v : Plc (Lp L)} (hv : v ∈ s.S) : Pc s n c (s.w v) = Kc _ n c := by
  unfold Pc
  exact if_pos ⟨v, hv, rfl⟩

theorem Kf_notS {w : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ s.S) : Kf s n c w = GlobalTheory.BCT.KL n w := by
  unfold Kf GlobalTheory.BCT.KL
  rw [Pc_notS hw]

theorem levFam (hfin : s.S.Finite) :
    GlobalTheory.BCT.IsLevelFam (fun w : GlobalTheory.BCT.Pl L => MonoidHom.id (GlobalTheory.BCT.UL n w)) (GlobalTheory.BCT.KL n) (Kf s n c) := by
  refine ⟨fun w => ⟨(Pc_open s n c w).preimage continuous_subtype_val, fun k hk => Pc_le s n c w hk, fun k hk => hk⟩, ?_⟩
  filter_upwards [(hfin.image s.w).compl_mem_cofinite] with w hw
  unfold Kf GlobalTheory.BCT.KL Pc
  rw [if_neg hw]

theorem loc_of_glob (hU : GlobalTheory.BCT.Unr L) {k : finU (E := L) (n := n)} (hk : k ∈ GlobalTheory.BCT.globLev (Set.range s.w) (Kf s n c))
    (v : Plc (Lp L)) : cLoc (s.w v) (k : UA L n) ∈ Pc s n c (s.w v) :=
  (GlobalTheory.BCT.HopLev.mem_globLev hU _ _ k).1 hk (s.w v) ⟨v, rfl⟩

theorem glob_of_loc (hU : GlobalTheory.BCT.Unr L) {k : finU (E := L) (n := n)} (h : ∀ v, cLoc (s.w v) (k : UA L n) ∈ Pc s n c (s.w v)) :
    k ∈ GlobalTheory.BCT.globLev (Set.range s.w) (Kf s n c) :=
  (GlobalTheory.BCT.HopLev.mem_globLev hU _ _ k).2 (by
    rintro _ ⟨v, rfl⟩
    exact h v)

theorem cmp_mem {w : Plc L} (U : Subgroup (GLw n w)) (x : UA L n) (hx : cLoc w x ∈ U) :
    cmp n w ((away l L n).rangeRestrict x) ∈ U := by
  unfold CaseU.cmp
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal
  · rw [dite_eq_left h]
    exact hx
  · rw [dite_eq_right h]
    exact one_mem _

private theorem pi_mem_first_iwahori_filtration {σ : Type} [Finite σ] {G : σ → Type} [∀ v, Group (G v)] (I : ∀ v, Iwa (G v)) (b : ℕ)
    (g : ∀ v, G v) (hg : ∀ v, g v ∈ (I v).I1 b) : g ∈ (piIwa I).I1 b := by
  choose x hx t ht y hy e using fun v => (iwMem _ (I v) b (g v)).2.1.1 (hg v)
  exact (iwMem _ (piIwa I) b g).2.1.2 ⟨x, fun v _ => hx v, t, fun v _ => ht v, y, fun v _ => hy v, funext e⟩

theorem Q_empty {V : s.Lev} (hV : V.S' = s.S) (Q : QData V) : IsEmpty Q.Q := ⟨fun q => Q.notS q (by
  have h : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  rwa [hV] at h)⟩

theorem goodOf {V : s.Lev} (hV : V.S' = s.S) (Q : QData V) {cf : Coef l} {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) cf.O)
    (b : ℕ) (hc : ∀ g : KT n (wt s), (∀ u, (g : GV n (wt s)) u ∈ Kc _ n c) → τ₀ g = 1) (h1 : 1 ≤ c) (hb : b + 1 ≤ c)
    (hU : GlobalTheory.BCT.Unr L) (k : finU (E := L) (n := n)) (hk : k ∈ GlobalTheory.BCT.globLev (Set.range s.w) (Kf s n c)) :
    (∃ u : Ub n s, u ∈ UQ n Q ∧ (u : Ga l L n) = (away l L n).rangeRestrict (k : UA L n) ∧ τ₀ (toKT n s u) = 1) ∧
      (fun v : V.frame.Vl => cLoc (s.w v.1) (k : UA L n)) ∈ (hset Q τ₀).X.I.I1 b := by
  haveI := Q_empty hV Q
  have hS : ∀ v ∈ s.S, cLoc (s.w v) (k : UA L n) ∈ Kc _ n c := fun v hv => by
    have := loc_of_glob hU hk v
    rwa [Pc_S hv] at this
  have hu : (away l L n).rangeRestrict (k : UA L n) ∈ Ub n s :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun u => cmp_mem _ _ (UpperTheory.V.Hi.GlAx.Kc_le c (hS u (Or.inr (Or.inl u.2)))),
      cmp_mem _ _ (UpperTheory.V.Hi.GlAx.Kc_anti h1 (hS s.v0 (Or.inr (Or.inr rfl))))⟩
  refine ⟨⟨⟨_, hu⟩, ?_, rfl, ?_⟩, ?_⟩
  · refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => ?_,
      Subgroup.mem_iInf.2 fun q => isEmptyElim q⟩
    rw [hV] at hw
    have h2 := loc_of_glob hU hk (w.under (𝓞 (Lp L)))
    rw [Pc_notS (by rwa [under_w])] at h2
    have h3 := int_over (under_w s (w.under (𝓞 (Lp L)))).symm (k : UA L n) h2
    rw [GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel.kgl_eq_ko] at h3
    exact cmp_mem _ _ h3
  · exact hc _ fun u => cmp_mem _ _ (hS u (Or.inr (Or.inl u.2)))
  · exact pi_mem_first_iwahori_filtration (fun v : V.frame.Vl => glIwa ((s.w v.1).adicCompletion L) n) b _ fun v =>
      (glBridge ((s.w v.1).adicCompletion L) n ℂ 1).2.2.2.2.1 b (UpperTheory.V.Hi.GlAx.Kc_anti hb (hS v.1 (Or.inl v.2)))

theorem exC {cf : Coef l} {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) cf.O) (hτ : IsOpen (τ₀.ker : Set (KT n (wt s)))) :
    ∃ c0 : ℕ, ∀ c, c0 ≤ c → ∀ g : KT n (wt s), (∀ u, (g : GV n (wt s)) u ∈ Kc _ n c) → τ₀ g = 1 := by
  classical
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hτ
  let H : Subgroup (GV n (wt s)) := τ₀.ker.map (KT n (wt s)).subtype
  have hHo : IsOpen (H : Set (GV n (wt s))) := by
    refine H.isOpen_of_mem_nhds (g := 1) ?_
    have h0 : IsOpen (Set.pi Set.univ fun u : s.St => (Kc ((wt s u).adicCompletion L) n 0 : Set (GLw n (wt s u)))) :=
      isOpen_set_pi Set.finite_univ fun u _ => (UpperTheory.unitaryAdelic_localComponents_continuous_levels_open L n).2.1 _ 0
    have h1 : (1 : GV n (wt s)) ∈ U := by
      have : (1 : KT n (wt s)) ∈ Subtype.val ⁻¹' U := by
        rw [hUe]
        exact one_mem τ₀.ker
      exact this
    refine Filter.mem_of_superset ((hU.inter h0).mem_nhds ⟨h1, fun u _ => one_mem _⟩) ?_
    rintro g ⟨hg, hg0⟩
    have hK : g ∈ KT n (wt s) := fun u _ => UpperTheory.V.Hi.GlAx.Kc_le 0 (hg0 u trivial)
    have : (⟨g, hK⟩ : KT n (wt s)) ∈ (τ₀.ker : Set (KT n (wt s))) := by
      rw [← hUe]
      exact hg
    exact ⟨⟨g, hK⟩, this, rfl⟩
  have hloc : ∀ u : s.St, ∃ cu, Kc ((wt s u).adicCompletion L) n cu ≤
      H.comap (MonoidHom.mulSingle (fun u => GLw n (wt s u)) u) := fun u =>
    (glBridge ((wt s u).adicCompletion L) n ℂ 1).2.2.2.1 _ (hHo.preimage (continuous_mulSingle u))
  choose cu hcu using hloc
  refine ⟨Finset.univ.sup cu, fun c hc g hg => ?_⟩
  have hpi : Subgroup.pi Set.univ (fun u : s.St => Kc ((wt s u).adicCompletion L) n c) ≤ H :=
    Subgroup.pi_le_iff.2 fun u => by
      rw [Subgroup.map_le_iff_le_comap]
      exact (UpperTheory.V.Hi.GlAx.Kc_anti ((Finset.le_sup (Finset.mem_univ u)).trans hc)).trans (hcu u)
  obtain ⟨g', hg', e⟩ := hpi (show (g : GV n (wt s)) ∈ _ from fun u _ => hg u)
  have : g' = g := Subtype.ext e
  rw [← this]
  exact hg'

theorem unramOf (hU : GlobalTheory.BCT.Unr L) (π : Submodule ℂ (UA L n → ℂ))
    (hne : π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) (GlobalTheory.BCT.globLev (Set.range s.w) (Kf s n c)) ≠ ⊥) (w : Plc L)
    (hw : w.under (𝓞 (Lp L)) ∉ s.S) : IsUnramU π w := by
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨φ, hφ.1, h0, fun x hx hK => ?_⟩
  have hxf : x ∈ finU (E := L) (n := n) := (Subgroup.mem_inf.1 hx).1
  have hmem : (⟨x, hxf⟩ : finU (E := L) (n := n)) ∈ GlobalTheory.BCT.globLev (Set.range s.w) (Kf s n c) := glob_of_loc hU fun v => by
    by_cases e : v = w.under (𝓞 (Lp L))
    · subst e
      rw [Pc_notS (by rwa [under_w])]
      exact int_over (under_w s _) x hK
    · have h1 : cLoc (s.w v) x = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1
        (Subgroup.mem_inf.1 hx).2 (s.w v)) (by rwa [under_w]))
      change cLoc (s.w v) x ∈ _
      rw [h1]
      exact one_mem _
  have h2 := hφ.2 ⟨⟨x, hxf⟩, hmem⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h2
  exact h2

end UpperTheory.V.Z.J.D.Dc
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.DecompB
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.DecompA
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace UpperTheory.V.Z.J.D.Dc


open GlobalTheory.DefU in
theorem autProj (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (M : Submodule ℂ (autU E n))
    (hM : FiniteDimensional ℂ M) :
    ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Submodule ℂ (UA E n → ℂ)) (P : κ → autU E n →ₗ[ℂ] autU E n),
      (∀ i, IsAutRepU (σ i)) ∧ (∀ i φ, (P i φ).1 ∈ σ i) ∧ (∀ i x φ, P i (autRep E n x φ) = autRep E n x (P i φ)) ∧
      ∀ φ ∈ M, ∑ i, P i φ = φ := by
  obtain ⟨h1, h2, h3, h4⟩ := UpperTheory.unitary_adelic_t2_locallyCompact_secondCountable E n
  obtain ⟨C, hC, hcov⟩ := UpperTheory.exists_compact_fundamental_set_unitary E n
  obtain ⟨B, hdef, hinv⟩ := UpperTheory.exists_nondegenerate_right_invariant_form_of_compact_quotient (UA E n) (ratU E n) C hC hcov
  have hsum := UpperTheory.mem_iSup_automorphicReps_of_invariant_form E n B (fun φ h => hdef φ h.cont h.left)
    (fun x φ ψ h h' => hinv x φ ψ h.cont h.left h'.cont h'.left)
  have hi := Submodule.map_injective_of_injective (autU E n).injective_subtype
  obtain ⟨κ, _, U, P, hU, hP, hPe, hPs⟩ := UpperTheory.exists_equivariant_projections_of_sum_irreducible (UA E n) (autU E n) (autRep E n) (fun x => by
    have key : ∀ (Z : Submodule ℂ (autU E n)), (∀ σ, IsAutRepU σ → σ.comap (autU E n).subtype ≤ Z) → x ∈ Z := by
      intro Z hZ
      have hle : (⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1) ≤ Z.map (autU E n).subtype :=
        iSup_le fun σ φ hφ => ⟨⟨φ, σ.2.aut φ hφ⟩, hZ σ.1 σ.2 hφ, rfl⟩
      obtain ⟨y, hy, e⟩ := hle (hsum x.1 x.2)
      exact Subtype.ext e ▸ hy
    refine key _ fun σ hσ => ?_
    have hm : (σ.comap (autU E n).subtype).map (autU E n).subtype = σ := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 hσ.aut
    refine le_iSup_of_le ⟨σ.comap (autU E n).subtype, fun h => hσ.ne_bot ?_, fun g u hu => hσ.stable g u.1 hu,
      fun N hN hst => ?_⟩ le_rfl
    · rw [← hm, h, Submodule.map_bot]
    · refine (hσ.irred (N.map (autU E n).subtype) (hm ▸ Submodule.map_mono hN) ?_).imp
        (fun h => hi (h.trans (Submodule.map_bot _).symm)) fun h => hi (h.trans hm.symm)
      rintro g _ ⟨u, hu, rfl⟩
      exact ⟨_, hst g u hu, rfl⟩) M hM
  refine ⟨κ, inferInstance, fun i => (U i).map (autU E n).subtype, P, fun i => ⟨?_, ?_, ?_, fun N hN hst => ?_⟩,
    fun i φ => ⟨_, hP i φ, rfl⟩, hPe, hPs⟩
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · rintro g _ ⟨u, hu, rfl⟩
    exact ⟨_, (hU i).2.1 g u hu, rfl⟩
  · exact fun h => (hU i).1 (hi (h.trans (Submodule.map_bot _).symm))
  · have hm : (N.comap (autU E n).subtype).map (autU E n).subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hN.trans (Submodule.map_subtype_le _ _))
    rcases (hU i).2.2 (N.comap (autU E n).subtype) (fun u hu => by
      obtain ⟨w, hw, e⟩ := hN hu
      exact Subtype.ext e ▸ hw) (fun g u hu => hst g u.1 hu) with h | h
    · left; rw [← hm, h, Submodule.map_bot]
    · right; rw [← hm, h]

theorem indepProj {M J : Type} [AddCommGroup M] [Module ℂ M] [Fintype J] (σ : J → Submodule ℂ M) (h : iSupIndep σ) :
    ∃ P : J → ↥(⨆ j, σ j) →ₗ[ℂ] M, (∀ t φ, P t φ ∈ σ t) ∧ (∀ φ, ∑ t, P t φ = φ) ∧
      ∀ (x : J → M), (∀ j, x j ∈ σ j) → ∀ φ : ↥(⨆ j, σ j), (φ : M) = ∑ j, x j → ∀ t, P t φ = x t := by
  classical
  let Ψ : (Π₀ j, σ j) →ₗ[ℂ] M := DFinsupp.lsum ℕ fun j => (σ j).subtype
  have hinj : Function.Injective Ψ := h.dfinsupp_lsum_injective
  have hΨ : ∀ y, Ψ y = ∑ j, (y j : M) := fun y => by
    change DFinsupp.lsum ℕ (fun j => (σ j).subtype) y = _
    rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum_eq_sum_fintype _ (fun j => map_zero _)]
    rfl
  have hr : LinearMap.range Ψ = ⨆ j, σ j := (Submodule.iSup_eq_range_dfinsupp_lsum σ).symm
  let e : (Π₀ j, σ j) ≃ₗ[ℂ] ↥(⨆ j, σ j) := (LinearEquiv.ofInjective Ψ hinj).trans (LinearEquiv.ofEq _ _ hr)
  have he : ∀ y, (e y : M) = Ψ y := fun y => rfl
  refine ⟨fun t => (σ t).subtype ∘ₗ DFinsupp.lapply t ∘ₗ e.symm.toLinearMap, fun t φ => (e.symm φ t).2, fun φ => ?_,
    fun x hx φ hφ t => ?_⟩
  · have := he (e.symm φ)
    rw [e.apply_symm_apply, hΨ] at this
    exact this.symm
  · let y : Π₀ j, σ j := DFinsupp.mk Finset.univ fun j => ⟨x j, hx j⟩
    have hy : ∀ j, (y j : M) = x j := fun j => by
      simp [y, DFinsupp.mk_apply]
    have : e.symm φ = y := by
      rw [LinearEquiv.symm_apply_eq]
      refine Subtype.ext ?_
      rw [he, hΨ, hφ]
      exact Finset.sum_congr rfl fun j _ => (hy j).symm
    change ((e.symm φ) t : M) = x t
    rw [this, hy]

section Core

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n m : ℕ} {Y D : Type} [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup D] [Module ℂ D]

theorem coreP {κ : Type} [Fintype κ] (A : Submodule ℂ Y) (tf : Y →ₗ[ℂ] D →ₗ[ℂ] (UA E n → ℂ))
    (r : UA E n → D → D) (hinj : ∀ F ∈ A, (∀ ℓ, tf F ℓ = 0) → F = 0)
    (hsur : ∀ Φ : D →ₗ[ℂ] (UA E n → ℂ), (∀ ℓ, IsAutFormU (Φ ℓ)) → (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (r x ℓ)) →
      ∃ F ∈ A, ∀ ℓ, tf F ℓ = Φ ℓ)
    (W : Submodule ℂ (UA E n → ℂ)) (hW : ∀ x, ∀ φ ∈ W, RU E n x φ ∈ W)
    (σ : κ → Submodule ℂ (UA E n → ℂ)) (P : κ → W →ₗ[ℂ] (UA E n → ℂ)) (hσ : ∀ t, ∀ φ ∈ σ t, IsAutFormU φ)
    (hP : ∀ t φ, P t φ ∈ σ t) (hPe : ∀ t x (φ : W), P t ⟨RU E n x φ, hW x φ φ.2⟩ = RU E n x (P t φ))
    (F : Fin m → Y) (hFA : ∀ i, F i ∈ A) (hFW : ∀ i ℓ, tf (F i) ℓ ∈ W)
    (hPs : ∀ i ℓ, ∑ t, P t ⟨tf (F i) ℓ, hFW i ℓ⟩ = tf (F i) ℓ)
    (heq : ∀ i ℓ, ∀ x ∈ infU E n, RU E n x (tf (F i) ℓ) = tf (F i) (r x ℓ)) :
    ∃ G : κ → Fin m → Y, (∀ t i, G t i ∈ A) ∧ (∀ t i ℓ, tf (G t i) ℓ ∈ σ t) ∧ ∑ t, G t = F ∧
      ∀ (T : Y → Y) (k : UA E n) (a : Fin m → Fin m → ℂ), (∀ F ∈ A, T F ∈ A) →
        (∀ F ℓ, tf (T F) ℓ = RU E n k (tf F ℓ)) → (∀ i, ∑ j, a i j • T (F j) = F i) →
        ∀ t i, ∑ j, a i j • T (G t j) = G t i := by
  let Φ : Fin m → D →ₗ[ℂ] W := fun i => (tf (F i)).codRestrict W (hFW i)
  have hΦ : ∀ i ℓ, (Φ i ℓ : UA E n → ℂ) = tf (F i) ℓ := fun _ _ => rfl
  have hex : ∀ t i, ∃ G ∈ A, ∀ ℓ, tf G ℓ = P t (Φ i ℓ) := fun t i =>
    hsur (P t ∘ₗ Φ i) (fun ℓ => hσ t _ (hP t _)) fun ℓ x hx => by
      have e : (⟨RU E n x (Φ i ℓ), hW x _ (Φ i ℓ).2⟩ : W) = Φ i (r x ℓ) := Subtype.ext (heq i ℓ x hx)
      exact (hPe t x (Φ i ℓ)).symm.trans (by rw [e]; rfl)
  choose G hGA hG using hex
  refine ⟨G, hGA, fun t i ℓ => hG t i ℓ ▸ hP t _, funext fun i => ?_, fun T k a hTA hT hF t i => ?_⟩
  · rw [Finset.sum_apply]
    refine sub_eq_zero.1 (hinj _ (sub_mem (Submodule.sum_mem _ fun t _ => hGA t i) (hFA i)) fun ℓ => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, hG]
    exact sub_eq_zero.2 (hPs i ℓ)
  · refine sub_eq_zero.1 (hinj _ (sub_mem (Submodule.sum_mem _ fun j _ => A.smul_mem _ (hTA _ (hGA t j))) (hGA t i))
      fun ℓ => ?_)
    have e : ∑ j, a i j • (⟨RU E n k (Φ j ℓ), hW k _ (Φ j ℓ).2⟩ : W) = Φ i ℓ := by
      apply Subtype.ext
      have := congrArg (fun y => tf y ℓ) (hF i)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hT] at this
      rw [Submodule.coe_sum]
      exact this
    have e2 := congrArg (P t) e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hPe] at e2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, hT, hG]
    exact sub_eq_zero.2 e2


open GlobalTheory.DefU in
theorem absMain {I J : Type} [Fintype J] [FiniteDimensional ℂ D] (A : Submodule ℂ Y) (tf : Y →ₗ[ℂ] D →ₗ[ℂ] (UA E n → ℂ))
    (r : UA E n → D → D) (hinj : ∀ F ∈ A, (∀ ℓ, tf F ℓ = 0) → F = 0)
    (hsur : ∀ Φ : D →ₗ[ℂ] (UA E n → ℂ), (∀ ℓ, IsAutFormU (Φ ℓ)) → (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (r x ℓ)) →
      ∃ F ∈ A, ∀ ℓ, tf F ℓ = Φ ℓ)
    (T : I → Y → Y) (k : I → UA E n) (a : I → Fin m → Fin m → ℂ) (hTA : ∀ u, ∀ F ∈ A, T u F ∈ A)
    (hT : ∀ u F ℓ, tf (T u F) ℓ = RU E n (k u) (tf F ℓ)) (Kf : Submodule ℂ (UA E n → ℂ))
    (Pw : Submodule ℂ (UA E n → ℂ) → Prop)
    (haut : ∀ F : Fin m → Y, (∀ i, F i ∈ A) → (∀ u i, ∑ j, a u i j • T u (F j) = F i) → ∀ i ℓ, IsAutFormU (tf (F i) ℓ))
    (heq : ∀ G ∈ A, ∀ ℓ, ∀ x ∈ infU E n, RU E n x (tf G ℓ) = tf G (r x ℓ))
    (hfix : ∀ F : Fin m → Y, (∀ i, F i ∈ A) → (∀ u i, ∑ j, a u i j • T u (F j) = F i) → ∀ i ℓ, tf (F i) ℓ ∈ Kf)
    (hwt : ∀ σ, IsAutRepU σ → ∀ F : Fin m → Y, (∀ i, F i ∈ A) → (∀ u i, ∑ j, a u i j • T u (F j) = F i) → F ≠ 0 →
      (∀ i ℓ, tf (F i) ℓ ∈ σ) → Pw σ)
    (σ : J → Submodule ℂ (UA E n → ℂ)) (hσ : ∀ j, IsAutRepU (σ j)) (hind : iSupIndep σ)
    (hcov : ∀ π, IsAutRepU π → Pw π → π ⊓ Kf ≤ ⨆ j, σ j)
    (F : Fin m → Y) (hFA : ∀ i, F i ∈ A) (hF : ∀ u i, ∑ j, a u i j • T u (F j) = F i) :
    ∃ G : J → Fin m → Y, (∀ j i, G j i ∈ A) ∧ (∀ j u i, ∑ l, a u i l • T u (G j l) = G j i) ∧
      (∀ j i ℓ, tf (G j i) ℓ ∈ σ j) ∧ ∑ j, G j = F := by
  have hFa := haut F hFA hF
  let Φ : Fin m → D →ₗ[ℂ] autU E n := fun i => (tf (F i)).codRestrict (autU E n) (hFa i)
  obtain ⟨κ, _, σ', P, hσ', hP, hPe, hPs⟩ := autProj E n (⨆ i, LinearMap.range (Φ i)) inferInstance
  obtain ⟨G', hG'A, hG', hsum', hinv'⟩ := coreP A tf r hinj hsur (autU E n) (fun x φ hφ => (autRep E n x ⟨φ, hφ⟩).2) σ'
    (fun t => (autU E n).subtype ∘ₗ P t) (fun t φ hφ => (hσ' t).aut φ hφ) hP
    (fun t x φ => congrArg Subtype.val (hPe t x φ)) F hFA hFa
    (fun i ℓ => by
      have e := congrArg Subtype.val (hPs (Φ i ℓ) (Submodule.mem_iSup_of_mem i ⟨ℓ, rfl⟩))
      rw [Submodule.coe_sum] at e
      exact e)
    (fun i ℓ x hx => heq _ (hFA i) ℓ x hx)
  have hinvG : ∀ t u i, ∑ j, a u i j • T u (G' t j) = G' t i := fun t u i =>
    hinv' (T u) (k u) (a u) (hTA u) (hT u) (hF u) t i
  have hmem : ∀ t i ℓ, tf (G' t i) ℓ ∈ ⨆ j, σ j := fun t i ℓ => by
    by_cases h0 : G' t = 0
    · rw [h0]
      simp
    · exact hcov _ (hσ' t) (hwt _ (hσ' t) _ (fun i => hG'A t i) (hinvG t) h0 (hG' t)) ⟨hG' t i ℓ,
        hfix _ (fun i => hG'A t i) (hinvG t) i ℓ⟩
  have hFW : ∀ i ℓ, tf (F i) ℓ ∈ ⨆ j, σ j := fun i ℓ => by
    have e : F i = ∑ t, G' t i := by
      rw [← hsum', Finset.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun t _ => hmem t i ℓ
  obtain ⟨Q, hQ, hQs, hQu⟩ := indepProj σ hind
  have hst : ∀ x, ∀ φ ∈ ⨆ j, σ j, RU E n x φ ∈ ⨆ j, σ j := fun x φ hφ => by
    have hle : (⨆ j, σ j) ≤ (⨆ j, σ j).comap (RU E n x) :=
      iSup_le fun j ψ hψ => Submodule.mem_iSup_of_mem j ((hσ j).stable x ψ hψ)
    exact hle hφ
  obtain ⟨G, hGA, hG, hsum, hinv⟩ := coreP A tf r hinj hsur (⨆ j, σ j) hst σ Q (fun t φ hφ => (hσ t).aut φ hφ) hQ
    (fun t x φ => hQu (fun j => RU E n x (Q j φ)) (fun j => (hσ j).stable x _ (hQ j φ)) _ (by
      change RU E n x (φ : UA E n → ℂ) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, hQs]) t) F hFA hFW (fun i ℓ => hQs _) (fun i ℓ x hx => heq _ (hFA i) ℓ x hx)
  exact ⟨G, hGA, fun j u i => hinv (T u) (k u) (a u) (hTA u) (hT u) (hF u) j i, hG, hsum⟩

theorem indepOf {M N J K : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (σ : J → Submodule ℂ N)
    (hind : iSupIndep σ) (Yv : J → Submodule ℂ M) (Tt : K → M →ₗ[ℂ] N) (hY : ∀ i, ∀ y ∈ Yv i, ∀ t, Tt t y ∈ σ i)
    (hsep : ∀ i, ∀ y ∈ Yv i, (∀ t, Tt t y = 0) → y = 0) : iSupIndep Yv := by
  intro i
  rw [Submodule.disjoint_def]
  intro y hy hy'
  refine hsep i y hy fun t => ?_
  have h1 : (⨆ j, ⨆ _ : j ≠ i, Yv j) ≤ (⨆ j, ⨆ _ : j ≠ i, σ j).comap (Tt t) :=
    iSup₂_le fun j hj z hz => Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (hY j z hz t))
  exact (Submodule.disjoint_def.1 (hind i)) _ (hY i y hy t) (h1 hy')

end Core

end UpperTheory.V.Z.J.D.Dc
end
end

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.V.Hi

namespace UpperTheory.V.Z.J.D.Dc

theorem core3 {E : Type} [Field E] [NumberField E] [IsCMField E] {n m d : ℕ} {Γ Ga Gp D Jx : Type} [Group Γ] [Group Ga]
    [Group Gp] [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D] [Fintype Jx] (X : Frame Γ Ga Gp)
    (ξ : Gp →* GL (Fin d) ℂ) (τ : X.Ub →* GL (Fin m) ℂ) (U₀ : Subgroup X.Ub) (I : Subgroup Gp) (J : UA E n →* Ga × Gp)
    (tf : (Ga × Gp → Fin d → ℂ) →ₗ[ℂ] D →ₗ[ℂ] (UA E n → ℂ)) (r : UA E n → D → D)
    (hJinf : ∀ x ∈ infU E n, J x = 1) (hRfin : ∀ k ∈ finU (E := E) (n := n), ∀ ℓ, r k ℓ = ℓ)
    (hinj : ∀ F ∈ X.AF ξ, (∀ ℓ, tf F ℓ = 0) → F = 0)
    (haut : ∀ F ∈ X.AF ξ, IsOpen {k : finU (E := E) (n := n) | ∀ g, F (g * J k) = F g} → ∀ ℓ, IsAutFormU (tf F ℓ))
    (htr : ∀ F ℓ x, RU E n x (tf F ℓ) = tf (fun g => F (g * J x)) (r x ℓ))
    (hsurj : Function.Surjective fun k : finU (E := E) (n := n) => J k)
    (hsur : ∀ Φ : D →ₗ[ℂ] (UA E n → ℂ), (∀ ℓ, IsAutFormU (Φ ℓ)) → (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (r x ℓ)) →
      ∃ F ∈ X.AF ξ, ∀ ℓ, tf F ℓ = Φ ℓ)
    (hev : ∀ᶠ k : finU (E := E) (n := n) in nhds 1, (∃ u ∈ U₀, (u : Ga) = (J k).1 ∧ τ u = 1) ∧ (J k).2 ∈ I)
    (Kf : Subgroup (finU (E := E) (n := n))) (hKf : ∀ k ∈ Kf, (∃ u ∈ U₀, (u : Ga) = (J k).1 ∧ τ u = 1) ∧ (J k).2 ∈ I)
    (Pw : Submodule ℂ (UA E n → ℂ) → Prop)
    (hwt : ∀ σ, IsAutRepU σ → (Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U₀) ⊓
      Submodule.span ℂ {F : Fin m → X.Fn ℂ d | ∀ i ℓ, tf (F i) ℓ ∈ σ} ≠ ⊥ → Pw σ)
    (σ : Jx → Submodule ℂ (UA E n → ℂ)) (hσ : ∀ j, IsAutRepU (σ j)) (hind : iSupIndep σ)
    (hcov : ∀ π, IsAutRepU π → Pw π → π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF E n) Kf ≤ ⨆ j, σ j)
    (F : Fin m → X.Fn ℂ d) (hF : F ∈ Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U₀)
    (hb : F ∈ fixd (X.rpF ℂ d m) I) :
    F ∈ ⨆ j, ((Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U₀) ⊓
      Submodule.span ℂ {F : Fin m → X.Fn ℂ d | ∀ i ℓ, tf (F i) ℓ ∈ σ j}) ⊓ fixd (X.rpF ℂ d m) I := by
  have hra : ∀ (u : X.Ub) (G : Fin m → Ga × Gp → Fin d → ℂ) (i : Fin m),
      X.raF d τ u G i = ∑ j, (τ u).val i j • fun g => G j (g * ((u : Ga), 1)) := fun u G i => by
    funext g t
    rw [Finset.sum_apply, Finset.sum_apply]
    rfl
  choose k1 hk1 using fun u : U₀ => hsurj (((u : X.Ub) : Ga), 1)
  choose k2 hk2 using fun p : I => hsurj (1, (p : Gp))
  let T : U₀ ⊕ I → (Ga × Gp → Fin d → ℂ) → (Ga × Gp → Fin d → ℂ) :=
    Sum.elim (fun u G g => G (g * (((u : X.Ub) : Ga), 1))) (fun p G g => G (g * (1, (p : Gp))))
  let kk : U₀ ⊕ I → UA E n := Sum.elim (fun u => (k1 u : UA E n)) (fun p => (k2 p : UA E n))
  let a : U₀ ⊕ I → Fin m → Fin m → ℂ := Sum.elim (fun u => (τ u.1).val) (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ))
  have hone : ∀ (p : I) (G : Fin m → Ga × Gp → Fin d → ℂ) (i : Fin m),
      ∑ j, a (.inr p) i j • T (.inr p) (G j) = T (.inr p) (G i) := fun p G i => by
    rw [Finset.sum_eq_single i (fun j _ hj => by
      change (1 : Matrix (Fin m) (Fin m) ℂ) i j • _ = 0
      rw [Matrix.one_apply_ne hj.symm, zero_smul]) (fun h => (h (Finset.mem_univ _)).elim)]
    change (1 : Matrix (Fin m) (Fin m) ℂ) i i • _ = _
    rw [Matrix.one_apply_eq, one_smul]
  have hfixG : ∀ G : Fin m → Ga × Gp → Fin d → ℂ, (∀ u i, ∑ j, a u i j • T u (G j) = G i) →
      ∀ k : finU (E := E) (n := n), ((∃ u ∈ U₀, (u : Ga) = (J k).1 ∧ τ u = 1) ∧ (J k).2 ∈ I) → ∀ i g, G i (g * J k) = G i g := by
    rintro G hG k ⟨⟨u, hu, huk, h1⟩, hk⟩ i g
    have h2 : ∑ j, (τ u).val i j • (fun g => G j (g * ((u : Ga), 1))) = G i := hG (.inl ⟨u, hu⟩) i
    rw [h1] at h2
    have h3 : ∀ g, G i (g * ((u : Ga), 1)) = G i g := fun g => by
      have h4 := congrFun h2 g
      rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by
        rw [Units.val_one, Matrix.one_apply_ne hj.symm, zero_smul]; rfl) (fun h => (h (Finset.mem_univ _)).elim),
        Units.val_one, Matrix.one_apply_eq, one_smul] at h4
      exact h4
    have h5 : ∀ g, G i (g * (1, (J k).2)) = G i g := fun g => by
      have h6 := (hone ⟨_, hk⟩ G i).symm.trans (hG (.inr ⟨_, hk⟩) i)
      exact congrFun h6 g
    have h6 : J k = ((u : Ga), 1) * (1, (J k).2) := Prod.ext (huk.symm.trans (mul_one _).symm) (one_mul _).symm
    rw [h6, ← mul_assoc, h5, h3]
  have hFA : ∀ i, F i ∈ X.AF ξ := fun i => hF.1 i trivial
  have hinvF : ∀ u i, ∑ j, a u i j • T u (F j) = F i := by
    rintro (u | p) i
    · exact (hra u.1 F i).symm.trans (congrFun (hF.2 u.1 u.2) i)
    · exact (hone p F i).trans (congrFun (hb p.1 p.2) i)
  obtain ⟨G, hGA, hGi, hGσ, hsum⟩ := absMain (X.AF ξ) tf r hinj hsur T kk a
    (by
      rintro (u | p) G hG γ g
      · have := hG γ (g * (((u : X.Ub) : Ga), 1))
        rw [← mul_assoc] at this
        exact this
      · have := hG γ (g * (1, (p : Gp)))
        rw [← mul_assoc] at this
        exact this)
    (by
      rintro (u | p) G ℓ
      · have h1 := htr G ℓ (k1 u)
        rw [hRfin _ (k1 u).2, show J (k1 u) = _ from hk1 u] at h1
        exact h1.symm
      · have h1 := htr G ℓ (k2 p)
        rw [hRfin _ (k2 p).2, show J (k2 p) = _ from hk2 p] at h1
        exact h1.symm)
    (GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF E n) Kf) Pw
    (fun G hGA hG i ℓ => haut (G i) (hGA i) (by
      let S : Subgroup (finU (E := E) (n := n)) :=
        { carrier := {k | ∀ g, G i (g * J k) = G i g}
          one_mem' := fun g => by rw [OneMemClass.coe_one, map_one, mul_one]
          mul_mem' := fun {x y} hx hy g => by rw [Subgroup.coe_mul, map_mul, ← mul_assoc, hy, hx]
          inv_mem' := fun {x} hx g => by rw [← hx, Subgroup.coe_inv, map_inv, inv_mul_cancel_right] }
      refine S.isOpen_of_mem_nhds (g := 1) ?_
      filter_upwards [hev] with k hk g
      exact hfixG G hG k hk i g) ℓ)
    (fun G _ ℓ x hx => by
      have h1 := htr G ℓ x
      simp only [hJinf x hx, mul_one] at h1
      exact h1)
    (fun G _ hG i ℓ k => by
      have h1 := htr (G i) ℓ (k.1 : UA E n)
      rw [hRfin _ k.1.2] at h1
      have h2 : (fun g => G i (g * J (k.1 : UA E n))) = G i := funext (hfixG G hG k.1 (hKf k.1 k.2) i)
      rw [h2] at h1
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      exact h1)
    (fun σ' hσ' G hGA hG h0 hm => hwt σ' hσ' fun hbot => h0 <| by
      have hmem : G ∈ (Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U₀) ⊓
          Submodule.span ℂ {F : Fin m → X.Fn ℂ d | ∀ i ℓ, tf (F i) ℓ ∈ σ'} :=
        ⟨⟨fun i _ => hGA i, fun u hu => funext fun i => (hra u G i).trans (hG (.inl ⟨u, hu⟩) i)⟩,
          Submodule.subset_span hm⟩
      rw [hbot] at hmem
      exact (Submodule.mem_bot _).1 hmem)
    σ hσ hind hcov F hFA hinvF
  rw [← hsum]
  refine Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j ⟨⟨⟨fun i _ => hGA j i, fun u hu =>
    funext fun i => (hra u (G j) i).trans (hGi j (.inl ⟨u, hu⟩) i)⟩, Submodule.subset_span (hGσ j)⟩,
    fun p hp => funext fun i => ?_⟩
  exact (hone ⟨p, hp⟩ (G j) i).symm.trans (hGi j (.inr ⟨p, hp⟩) i)

end UpperTheory.V.Z.J.D.Dc
end
end

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

private theorem fixOf {L : Type} [Field L] [NumberField L] [IsCMField L] (hU : GlobalTheory.BCT.Unr L) {n : ℕ} (hn : 1 ≤ n)
    {S : Set (GlobalTheory.BCT.Pl L)} (hS : GlobalTheory.BCT.IsSection S) {lam : InfinitePlace L → DomWeight n}
    {K' : ∀ w : GlobalTheory.BCT.Pl L, Subgroup (GlobalTheory.BCT.UL n w)}
    (hLev : GlobalTheory.BCT.IsLevelFam (fun w : GlobalTheory.BCT.Pl L => MonoidHom.id (GlobalTheory.BCT.UL n w)) (GlobalTheory.BCT.KL n) K')
    (π : Submodule ℂ (UA L n → ℂ)) (h1 : IsAutRepU π) (h2 : ∀ v, HasWeightAt π v.embedding (lam v))
    (h3 : π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) (GlobalTheory.BCT.globLev S K') ≠ ⊥) (w : GlobalTheory.BCT.Pl L) (hw : w ∈ S)
    (hs : IsSplitAt w) (τ : SmIrr (GLw n w)) (hc : Cp π w τ) :
    GlobalTheory.PRep.fixed (τ.ρ.comp (GlobalTheory.BCT.UL n w).subtype) (K' w) ≠ ⊥ := by
  have hUL : GlobalTheory.BCT.UL n w = ⊤ := if_pos hs
  have hsurj : Function.Surjective (GlobalTheory.BCT.UL n w).subtype := fun g =>
    ⟨⟨g, hUL ▸ Subgroup.mem_top g⟩, rfl⟩
  let σ₁ : SmIrr (GlobalTheory.BCT.UL n w) :=
    { V := τ.V
      ρ := τ.ρ.comp (GlobalTheory.BCT.UL n w).subtype
      smooth := fun v => (τ.smooth v).preimage continuous_subtype_val
      irred := GlobalTheory.BCT.LocCompU.isIrreducible_comp_of_surjective τ.ρ _ hsurj τ.irred }
  obtain ⟨-, f, hf0, hfm, hf⟩ := hc
  let p : locU n w →* GlobalTheory.BCT.UL n w :=
    ((cLoc w).comp (locU n w).subtype).codRestrict (GlobalTheory.BCT.UL n w) fun x => hUL ▸ Subgroup.mem_top _
  exact GlobalTheory.T.localComponent_levelFixedVectors_ne_bot L hU n hn S hS lam K' hLev π h1 h2 h3 w hw σ₁
    ⟨p, fun x => rfl, σ₁.irred, f, hf0, hfm, fun x v => hf x v⟩

section Tf

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
  (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))

private def tfOf : (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ]
    Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
  LinearMap.mk₂ ℂ (toForm ι e)
    (fun F F' ℓ => funext fun g => by simp only [toForm, Pi.add_apply, map_add (f := _)])
    (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, map_smul])
    (fun F ℓ ℓ' => funext fun g => by simp only [toForm, Pi.add_apply, LinearMap.add_apply])
    (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, LinearMap.smul_apply])

private theorem yEq {c : Coef l} {m : ℕ} (Q : QData V) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (σ' : Submodule ℂ (UA L n → ℂ)) :
    (Submodule.pi Set.univ (fun _ => (hset Q τ₀).X.AF ξ) ⊓ fixd ((hset Q τ₀).X.raF d ((hset Q τ₀).τC ι)) (hset Q τ₀).UQ) ⊓
      Submodule.span ℂ {F : Fin (hset Q τ₀).m → (hset Q τ₀).X.Fn ℂ d | ∀ i ℓ, tfOf ι e (F i) ℓ ∈ σ'} = YOf Q ι τ₀ e ξ σ' := rfl

end Tf

private theorem wtY {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n) (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hξ : IsBasis ι e ξ)
    (σ' : Submodule ℂ (UA L n → ℂ)) (hσ' : IsAutRepU σ') (hne : YOf Q ι τ₀ e ξ σ' ≠ ⊥) :
    ∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ' (ι.toRingHom.comp y.res) (lam y.res).dual :=
  UpperTheory.V.Hi.partUR2Wt l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ σ' hσ' hne

private theorem wtZ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n)
    (lam' : InfinitePlace L → DomWeight n) (hlink : WtLink V ι lam lam')
    (σ' : Submodule ℂ (UA L n → ℂ)) (hσ' : IsAutRepU σ')
    (h : ∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ' (ι.toRingHom.comp y.res) (lam y.res).dual) :
    ∀ v, HasWeightAt σ' v.embedding (lam' v) :=
  (hlink σ' hσ').1 h

private def PwD {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (lam' : InfinitePlace L → DomWeight n)
    (π : Submodule ℂ (UA L n → ℂ)) : Prop := ∀ v, HasWeightAt π v.embedding (lam' v)

private theorem levLe {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (Q : QData V) (hQ : IsEmpty Q.Q) {c : Coef l} {m : ℕ}
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K : (hset Q τ₀).Lev) : (hset Q τ₀).lev K ≤ (hset Q τ₀).UQ := by
  unfold HSet.lev
  refine sup_le le_rfl (iSup_le fun q => ?_)
  exact (hQ.false q).elim

private theorem mainStep {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n) (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (hτ : IsOpen (τ₀.ker : Set (KT n (wt s)))) (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hξ : IsBasis ι e ξ) (b : ℕ)
    (hQ : IsEmpty Q.Q)
    (Pw : Submodule ℂ (UA L n → ℂ) → Prop)
    (hwtY : ∀ σ' : Submodule ℂ (UA L n → ℂ), IsAutRepU σ' → YOf Q ι τ₀ e ξ σ' ≠ ⊥ → Pw σ')
    (Kf : Subgroup (finU (E := L) (n := n)))
    (hKf : ∀ k ∈ Kf, (∃ u : Ub n s, u ∈ UQ n Q ∧ (u : Ga l L n) = (away l L n).rangeRestrict (k : UA L n) ∧
      τ₀ (toKT n s u) = 1) ∧ (fun v : V.frame.Vl => cLoc (s.w v.1) (k : UA L n)) ∈ (hset Q τ₀).X.I.I1 b)
    {J' : Type} [Fintype J'] (σ : J' → Submodule ℂ (UA L n → ℂ)) (hσ : ∀ j, IsAutRepU (σ j)) (hind : iSupIndep σ)
    (hcov : ∀ π, IsAutRepU π → Pw π → π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) Kf ≤ ⨆ j, σ j) :
    (hset Q τ₀).Big ι ξ ⊓ fixd ((hset Q τ₀).X.rpF ℂ d m) ((hset Q τ₀).X.I.I1 b) ≤
      ⨆ i, YOf Q ι τ₀ e ξ (σ i) ⊓ fixd ((hset Q τ₀).X.rpF ℂ d m) ((hset Q τ₀).X.I.I1 b) := by
  intro F hF
  let J : UA L n →* Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) :=
    MonoidHom.prod (away l L n).rangeRestrict (Pi.monoidHom fun v : V.frame.Vl => cLoc (s.w v.1))
  obtain ⟨hinj, haut, htr, hsurj, hsur⟩ := UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ J (fun _ => rfl)
  haveI := e.finiteDimensional
  have hJinf : ∀ x ∈ infU L n, J x = 1 := fun x hx => by
    have h1 : ∀ w, cLoc w x = 1 := fun w => by
      have h2 : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := hx
      change Matrix.GeneralLinearGroup.map (pLoc L w) (Matrix.GeneralLinearGroup.map (pFin L) x.1) = 1
      rw [h2, map_one]
    exact Prod.ext (Subtype.ext (funext fun w => h1 _)) (funext fun v => h1 _)
  have hRfin : ∀ k ∈ finU (E := L) (n := n), infRep (V := V) ι lam k = 1 := fun k hk => by
    have h1 : ∀ τ, cEmb τ k = 1 := fun τ => by
      change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
      rw [MonoidHom.mem_ker.1 hk, map_one]
    have h2 : (Pi.monoidHom fun e : Emb l (fun v : V.frame.Vl => s.w v.1) =>
        (GlobalTheory.Branching.sqRep ℂ n (lam e.res)).comp (cEmb (E := L) (n := n) (ι.toRingHom.comp e.res))) k = 1 :=
      funext fun y => by
        change GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb _ k) = 1
        rw [h1, map_one]
    unfold infRep
    rw [MonoidHom.comp_apply, h2, map_one]
  refine Dc.core3 (hset Q τ₀).X ξ ((hset Q τ₀).τC ι) (hset Q τ₀).UQ ((hset Q τ₀).X.I.I1 b) J (tfOf ι e)
    (fun x ℓ => ℓ ∘ₗ infRep ι lam x⁻¹) hJinf (fun k hk ℓ => ?_) hinj haut htr hsurj hsur ?_ Kf (fun k hk => ?_) Pw
    (fun σ' hσ' hne => hwtY σ' hσ' (by rw [← yEq ι e Q τ₀ ξ σ']; exact hne))
    σ hσ hind hcov F hF.1 hF.2
  · rw [hRfin _ ((finU (E := L) (n := n)).inv_mem hk)]
    rfl
  · filter_upwards [UpperTheory.eventually_mem_heckeLevel_and_iwahoriCongruence l L Ω s n hn V Q c m τ₀ hτ
      ⟨fun q => (hQ.false q).elim, fun q => (hQ.false q).elim⟩ b] with k ⟨⟨u, hu, huk, hu1⟩, hk⟩
    refine ⟨⟨u, levLe Q hQ τ₀ _ hu, huk, ?_⟩, hk⟩
    change Matrix.GeneralLinearGroup.map _ (τ₀ (toKT n s u)) = 1
    rw [hu1, map_one]
  · obtain ⟨⟨u, hu, huk, hu1⟩, hk'⟩ := hKf k hk
    refine ⟨⟨u, hu, huk, ?_⟩, hk'⟩
    change Matrix.GeneralLinearGroup.map _ (τ₀ (toKT n s u)) = 1
    rw [hu1, map_one]

private theorem yIndep {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n) (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hξ : IsBasis ι e ξ)
    {J' : Type} (σ : J' → Submodule ℂ (UA L n → ℂ)) (hind : iSupIndep σ) :
    iSupIndep (fun i => YOf Q ι τ₀ e ξ (σ i)) := by
  obtain ⟨hinj, -⟩ := UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ
    (MonoidHom.prod (away l L n).rangeRestrict (Pi.monoidHom fun v : V.frame.Vl => cLoc (s.w v.1))) (fun _ => rfl)
  let Tt : Fin m × Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →
      (Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ] (UA L n → ℂ) :=
    fun t => (LinearMap.applyₗ t.2) ∘ₗ tfOf ι e ∘ₗ LinearMap.proj t.1
  refine Dc.indepOf σ hind _ Tt (fun i y hy t => ?_)
    (fun i y hy h0 => funext fun a => hinj (y a) (hy.1.1 a trivial) fun ℓ => h0 (a, ℓ))
  have hle : Submodule.span ℂ {F : Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ |
      ∀ a ℓ, toForm ι e (F a) ℓ ∈ σ i} ≤ (σ i).comap (Tt t) := Submodule.span_le.2 fun F hF => hF t.1 t.2
  exact hle hy.2

set_option Elab.async false in
theorem UpperTheory.V.Z.J.D.decomp :
    IndepS → Decomp := by
  intro hI l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ hτ lam' hlink b
  have hU := Dc.unrOf s
  obtain ⟨c0, hc0⟩ := Dc.exC (n := n) (s := s) τ₀ hτ
  have hcc := hc0 (c0 + b + 1) (by omega)
  have hfin : s.S.Finite := hV ▸ V.fin
  have hS := Dc.secRange s
  have hLev : GlobalTheory.BCT.IsLevelFam (fun w : GlobalTheory.BCT.Pl L => MonoidHom.id (GlobalTheory.BCT.UL n w)) (GlobalTheory.BCT.KL n)
      (Dc.Kf s n (c0 + b + 1)) := Dc.levFam hfin
  obtain ⟨-, J', hJ', σ, hσ, hind, hsup, -⟩ := GlobalTheory.T.unitaryAutForms_weight_level_finite_sum_fixed_vectors L hU n hn _ hS lam' _ hLev
  have hdec : IsDec (Set.range s.w) lam' (Dc.Kf s n (c0 + b + 1)) σ := ⟨hσ, hind, hsup⟩
  have hσind := hI L n _ hS lam' _ hLev J' σ hdec
  refine ⟨Set.range s.w, Dc.Kf s n (c0 + b + 1), J', hJ', σ, hS, hLev, fun w hw => Dc.Kf_notS hw, hdec,
    yIndep s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσind,
    fun i w hw => Dc.unramOf hU _ (hσ i).2.2 w hw,
    fun i w hw hs τ hc => fixOf hU hn hS hLev (σ i) (hσ i).1 (hσ i).2.1 (hσ i).2.2 w hw hs τ hc, ?_⟩
  have hQ := Dc.Q_empty hV Q
  have hgood : ∀ k ∈ GlobalTheory.BCT.globLev (Set.range s.w) (Dc.Kf s n (c0 + b + 1)),
      (∃ u : Ub n s, u ∈ UQ n Q ∧ (u : Ga l L n) = (away l L n).rangeRestrict (k : UA L n) ∧ τ₀ (toKT n s u) = 1) ∧
        (fun v : V.frame.Vl => cLoc (s.w v.1) (k : UA L n)) ∈ (hset Q τ₀).X.I.I1 b := fun k hk =>
    Dc.goodOf hV Q τ₀ b hcc (by omega) (by omega) hU k hk
  have hwtY : ∀ σ' : Submodule ℂ (UA L n → ℂ), IsAutRepU σ' → YOf Q ι τ₀ e ξ σ' ≠ ⊥ → PwD lam' σ' := fun σ' hσ' hne =>
    wtZ V ι lam lam' hlink σ' hσ' (wtY s n hn V Q c ι m τ₀ lam d e ξ hξ σ' hσ' hne)
  have hcov : ∀ π : Submodule ℂ (UA L n → ℂ), IsAutRepU π → PwD lam' π →
      π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) (GlobalTheory.BCT.globLev (Set.range s.w) (Dc.Kf s n (c0 + b + 1))) ≤ ⨆ j, σ j := by
    intro π hπ hP φ hφ
    have h1 : φ ∈ GlobalTheory.BCT.forms (Set.range s.w) lam' (Dc.Kf s n (c0 + b + 1)) :=
      (le_iSup₂_of_le (f := fun (π : Submodule ℂ (UA L n → ℂ))
        (_ : IsAutRepU π ∧ ∀ v, HasWeightAt π v.embedding (lam' v)) =>
          π ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) (GlobalTheory.BCT.globLev (Set.range s.w) (Dc.Kf s n (c0 + b + 1))))
        π ⟨hπ, hP⟩ le_rfl) hφ
    rw [← hsup] at h1
    have h2 : (⨆ i, σ i ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) (GlobalTheory.BCT.globLev (Set.range s.w) (Dc.Kf s n (c0 + b + 1)))) ≤ ⨆ j, σ j :=
      iSup_mono fun i => inf_le_left
    exact h2 h1
  exact mainStep s n hn V Q c ι m τ₀ hτ lam d e ξ hξ b hQ
    (PwD lam') hwtY
    (GlobalTheory.BCT.globLev (Set.range s.w) (Dc.Kf s n (c0 + b + 1))) hgood σ (fun j => (hσ j).1) hσind hcov
