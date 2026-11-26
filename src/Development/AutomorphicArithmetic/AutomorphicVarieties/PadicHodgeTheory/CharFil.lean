module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmHom
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormSubgroupOpen

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.CharFil

section Generic

open GlobalTheory.SplitJump

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V)

private theorem split_fil (a : ℤ) (W W' : Matrix (Fin n) (Fin n) BdR) (hWW : W * W' = 1)
    (hW : ∀ i j, W i j ∈ PD.Fil a) (hW' : ∀ i j, W' i j ∈ PD.Fil (-a))
    (hg : ∀ g, (Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)) * W.map (PD.actdR g) = W)
    (y : V ⊗[Qp] BdR) (hy : y ∈ DdR PD ρ) (b : ℤ) :
    (b ≤ a → y ∈ FilV PD (LL := LL) (V := V) b) ∧ (a < b → y ∈ FilV PD (LL := LL) (V := V) b → y = 0) := by
  obtain ⟨k, hk⟩ := exists_coord PD ρ e W W' hWW hg y hy
  have hc : coord e BdR y = W.mulVec fun i => algebraMap K BdR (k i) := by
    rw [hk, Matrix.mulVec_mulVec, hWW, Matrix.one_mulVec]
  refine ⟨fun hb => ?_, fun hb hF => ?_⟩
  · rw [mem_filV PD e]
    intro i
    rw [hc]
    refine fil_mono PD hb ?_
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [mul_comm, ← Algebra.smul_def]
    exact (PD.Fil a).smul_mem _ (hW i j)
  · rw [mem_filV PD e] at hF
    have hk0 : ∀ i, k i = 0 := fun i => by
      refine eq_zero_of_mem_fil_one PD _ ?_
      rw [congrFun hk i]
      simp only [Matrix.mulVec, dotProduct]
      refine Submodule.sum_mem _ fun j _ => ?_
      exact fil_mono PD (by omega) (PD.Fil_mul _ _ _ _ (hW' i j) (hF j))
    apply (coord e BdR).injective
    rw [hc, map_zero]
    funext i
    simp [hk0, Matrix.mulVec, dotProduct]

end Generic

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E]

private theorem val_integral {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] (μ : G →* Eˣ)
    (hμ : Continuous fun g => (μ g : E)) (g : G) : IsIntegral ℤ_[l] (μ g : E) := by
  let j : E →ₐ[ℚ_[l]] Om l := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hj : Continuous j := IsModuleTopology.continuous_of_linearMap j.toLinearMap
  let d : G →* Om l := (j : E →* Om l).comp ((Units.coeHom E).comp μ)
  have hd : ‖d g‖ = 1 := GlobalTheory.UnramifiedChar.norm_eq_one_of_compact d (hj.comp hμ) g
  let LL : FinExt l := ⟨j.fieldRange, Module.Finite.of_surjective j.rangeRestrict.toLinearMap j.rangeRestrict_surjective⟩
  have h1 : (⟨j (μ g), ⟨_, rfl⟩⟩ : ↥LL.1) ∈ OL LL := (GlobalTheory.Per.Val.mem_OL_iff LL _).2 hd.le
  have h2 : IsIntegral ℤ_[l] (j (μ g)) := IsIntegral.map (LL.1.val.restrictScalars ℤ_[l]) h1
  exact (isIntegral_algHom_iff (j.restrictScalars ℤ_[l]) j.injective).1 h2

omit [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] in
private theorem exists_int_basis : ∃ (n : ℕ) (e : Basis (Fin n) ℚ_[l] E),
    ∀ x : E, IsIntegral ℤ_[l] x ↔ ∀ i, ‖e.repr x i‖ ≤ 1 := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  have : IsTorsionFree ℤ_[l] E := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (algebraMap ℚ_[l] E).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  have : Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] E) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] E _
  have : Module.Free ℤ_[l] ↥(integralClosure ℤ_[l] E) := IsIntegralClosure.module_free ℤ_[l] ℚ_[l] E _
  have : Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] E).toSubmodule := ‹Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] E)›
  have : Module.Free ℤ_[l] ↥(integralClosure ℤ_[l] E).toSubmodule := ‹Module.Free ℤ_[l] ↥(integralClosure ℤ_[l] E)›
  refine GlobalTheory.Cyc.LatBasis.exists_basis_of_submodule (integralClosure ℤ_[l] E).toSubmodule fun x => ?_
  have hx : IsAlgebraic ℤ_[l] x := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  exact hx.exists_integral_multiple

open GlobalTheory.UnramifiedCrys GlobalTheory.UnramifiedRep in
private theorem exists_split [IsTopologicalRing E] (K : FinExt l) (μ : ↥(GK K) →* Eˣ)
    (hμ : Continuous fun g => (μ g : E)) (hI : ∀ g ∈ IK K, μ g = 1) :
    ∃ (n : ℕ) (e : Basis (Fin n) ℚ_[l] E) (W W' : Matrix (Fin n) (Fin n) (Bdr l)), W * W' = 1 ∧
      (∀ i j, W i j ∈ ((PP l).PD K).Fil 0) ∧ (∀ i j, W' i j ∈ ((PP l).PD K).Fil 0) ∧
      ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] (Bdr l) (e.repr (chRep μ g (e j)) i)) *
        W.map (((PP l).PD K).actdR g) = W := by
  have := compactSpace_GK K
  obtain ⟨Ti⟩ := tiedP l
  set P := PP l
  set AI := AIP l
  obtain ⟨n, e, he⟩ := exists_int_basis (l := l) (E := E)
  have hρ : ∀ g x, chRep μ g x = (μ g : E) * x := fun _ _ => rfl
  have hint : ∀ g i j, ‖e.repr (chRep μ g (e j)) i‖ ≤ 1 := fun g i j =>
    (he _).1 ((val_integral μ hμ g).mul ((he (e j)).2 fun k => by
      rw [e.repr_self, Finsupp.single_apply]
      split_ifs <;> simp)) i
  obtain ⟨M, hM⟩ := exists_matrixHom (chRep μ) e hint
  obtain ⟨W, hW, hWg⟩ := exists_witt_matrix (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq AI y m hm hy)) M
    (continuous_pi fun i => continuous_pi fun j => continuous_induced_rng.2 (by
      have h := (IsModuleTopology.continuous_of_linearMap (e.coord i)).comp (hμ.mul (continuous_const (y := e j)))
      exact h.congr fun g => (hM g i j).symm))
    (fun g hg => by
      have h := hI g (Subgroup.subset_closure fun x hx =>
        norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx)
      rw [← map_one M]
      ext i j
      rw [hM, hM, hρ, hρ, h, map_one])
  have hB : ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] P.R.B (e.repr (chRep μ g (e j)) i)) *
      (AI.ιA.mapMatrix W).map ((P.PD K).actB g) = AI.ιA.mapMatrix W := fun g => by
    conv_rhs => rw [← hWg g, map_mul]
    congr 1
    · ext i j
      rw [Matrix.of_apply, ← hM]
      exact (ιA_zlW AI Ti (M g i j)).symm
    · ext i j
      exact (P.PD_actB K g _).trans (AI.ιA_act g _).symm
  let f : Ainf l →+* P.R.BdR := ((P.PD K).ι : P.R.B →+* P.R.BdR).comp AI.ιA
  have hf : ∀ a, f a ∈ (P.PD K).Fil 0 := fun a => by
    change (P.PD K).ι (AI.ιA a) ∈ _
    rw [P.PD_ι]
    exact AI.ainf_image_mem_filtration_zero K a
  refine ⟨n, e, f.mapMatrix W, f.mapMatrix W⁻¹, ?_, fun i j => hf _, fun i j => hf _, fun g => ?_⟩
  · rw [← map_mul, Matrix.mul_nonsing_inv _ hW, map_one]
  · have hι : ∀ c : ℚ_[l], ((P.PD K).ι : P.R.B →+* P.R.BdR) (algebraMap ℚ_[l] P.R.B c) =
        algebraMap ℚ_[l] P.R.BdR c := fun c => (P.PD_ι K _).trans (P.ιB.commutes c)
    exact map_mul_map_eq ((P.PD K).ι : P.R.B →+* P.R.BdR) (hB g) (fun i j => hι _)
      ((P.PD K).ι_comm g)

omit [FiniteDimensional ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] in
private theorem cycA_val (g : GQ l) : cycA l l E g = Units.map (algebraMap ℚ_[l] E : ℚ_[l] →* E) ((PP l).χQ g) := by
  ext
  change algebraMap ℤ_[l] E _ = algebraMap ℚ_[l] E _
  rw [(cycFacts l l).2.2 g, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E]
  rfl

omit [FiniteDimensional ℚ_[l] E] in
private theorem cont_cycA [IsTopologicalRing E] (w : ℤ) : Continuous fun g : GQ l => ((cycA l l E g ^ w : Eˣ) : E) := by
  have h1 : Continuous (algebraMap ℤ_[l] E) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] E)).comp continuous_subtype_val
  have h2 : Continuous fun g : GQ l => cyc l l g ^ w := (cycFacts l l).1.zpow w
  refine (h1.comp (Units.continuous_val.comp h2)).congr fun g => ?_
  exact congrArg Units.val (map_zpow (Units.map (algebraMap ℤ_[l] E : ℤ_[l] →* E)) (cyc l l g) w)

private theorem gk_case [IsTopologicalRing E] (K : FinExt l) (κ : ↥(GK K) →* Eˣ)
    (hκ : Continuous fun g => (κ g : E)) (w : ℤ) (hI : ∀ g ∈ IK K, κ g = cycA l l E g ^ w)
    (y : E ⊗[ℚ_[l]] Bdr l) (hy : y ∈ DdR ((PP l).PD K) (chRep κ)) (b : ℤ) :
    (b ≤ -w → y ∈ FilV ((PP l).PD K) (LL := E) (V := E) b) ∧
      (-w < b → y ∈ FilV ((PP l).PD K) (LL := E) (V := E) b → y = 0) := by
  obtain ⟨T⟩ := tiedP l
  let μ : ↥(GK K) →* Eˣ := κ * ((cycA l l E).comp (GK K).subtype) ^ (-w)
  have hμ : ∀ g, μ g = κ g * cycA l l E g ^ (-w) := fun _ => rfl
  obtain ⟨n, e, W, W', hWW, hW, hW', hg⟩ := exists_split K μ
    (hκ.mul ((cont_cycA (-w)).comp continuous_subtype_val))
    (fun g hg => by rw [hμ, hI g hg, zpow_neg, mul_inv_cancel])
  set t := GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR (PP l) K
  have ht : (t : Bdr l) = ((PP l).PD K).ι ((PP l).PD K).t := rfl
  refine split_fil ((PP l).PD K) (chRep κ) e (-w) (((t ^ (-w) : (Bdr l)ˣ) : Bdr l) • W)
    (((t ^ w : (Bdr l)ˣ) : Bdr l) • W') ?_ (fun i j => ?_) (fun i j => ?_) (fun g => ?_) y hy b
  · rw [Matrix.smul_mul, Matrix.mul_smul, hWW, smul_smul, zpow_neg, Units.inv_mul, one_smul]
  · simpa using ((PP l).PD K).Fil_mul _ _ _ _ (GlobalTheory.DRFil.tdR_zpow_mem T K (-w)) (hW i j)
  · simpa using ((PP l).PD K).Fil_mul _ _ _ _ (GlobalTheory.DRFil.tdR_zpow_mem T K w) (hW' i j)
  · conv_rhs => rw [← hg g]
    ext i j
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, smul_eq_mul, map_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hχ : ((PP l).PD K).χ g = (PP l).χQ g := Units.ext ((PP l).PD_χ K g)
    have h1 : chRep μ g (e k) = (((PP l).χQ g ^ (-w) : ℚ_[l]ˣ) : ℚ_[l]) • chRep κ g (e k) := by
      change (μ g : E) * e k = _ • ((κ g : E) * e k)
      rw [hμ, cycA_val, ← map_zpow, Algebra.smul_def, Units.val_mul, Units.coe_map]
      simp only [MonoidHom.coe_coe]
      ring
    rw [GlobalTheory.DRDual.act_zpow _ t ht, hχ, h1, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]
    ring

end UpperTheory.V.Loc.CharFil

open UpperTheory.V.Loc.CharFil in
theorem UpperTheory.V.Loc.charFil :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] (κ : G →* Eˣ), Continuous (fun g => (κ g : E)) → ∀ w : ℤ, HasWeight φ κ w → IsDr φ (chRep κ) ∧ ∀ i : ℤ, (i ≤ -w → FilD φ (chRep κ) i = Ddr φ (chRep κ)) ∧ (-w < i → FilD φ (chRep κ) i = ⊥) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ _ _ _ κ hκ w ⟨U, hU, hw⟩
  have hφU : IsOpenEmbedding (φ.comp U.subtype) := hφ.comp hU.isOpenEmbedding_subtypeVal
  have hc : ContAction (chRep κ) := (hκ.comp continuous_fst).mul continuous_snd
  have hcU : ContAction ((chRep κ).comp U.subtype : Representation E U E) :=
    (hκ.comp (continuous_subtype_val.comp continuous_fst)).mul continuous_snd
  refine ⟨((isCrys_isDR_restrict_openSubgroup φ hφ _ hc).2 U hU).2.2 ((isCrys_isDR_restrict_openSubgroup _ hφU _ hcU).1 (crUnr _ hφU _ hcU w fun g hg x => ?_)),
    fun i => ?_⟩
  · change (κ g : E) • x = _
    rw [hw g g.2 hg]
    rfl
  obtain ⟨K, e, -, he, hf, -, -, -⟩ := openField _ hφU
  have hf' : ∀ g : ↥(GK K), φ (e.symm g) = g := fun g => by
    have := DFunLike.congr_fun hf (e.symm g)
    simpa using this.symm
  let κ' : ↥(GK K) →* Eˣ := (κ.comp U.subtype).comp e.symm.toMonoidHom
  have hF : FilT E E i = FilV ((PP l).PD K) (LL := E) (V := E) i := by
    have : (((PP l).PD (botExt l)).Fil i).restrictScalars ℚ_[l] = (((PP l).PD K).Fil i).restrictScalars ℚ_[l] :=
      SetLike.coe_injective ((PP l).PD_Fil _ _ i)
    unfold FilT FilV
    rw [this]
  have key : ∀ y ∈ Ddr φ (chRep κ), (i ≤ -w → y ∈ FilT E E i) ∧ (-w < i → y ∈ FilT E E i → y = 0) := by
    intro y hy
    rw [hF]
    refine gk_case K κ' (hκ.comp (continuous_subtype_val.comp he)) w (fun g hg => ?_) y ?_ i
    · have := hw (e.symm g) (e.symm g).2 (by rw [hf']; exact (memIK K g).1 hg)
      rw [hf'] at this
      exact this
    · refine (Submodule.mem_iInf _).2 fun g => ?_
      have h1 := (Submodule.mem_iInf _).1 hy (e.symm g)
      have h2 : actVdR ((PP l).PD K) (chRep κ') g = actD φ (chRep κ) (e.symm g) := by
        unfold actVdR actD
        rw [hf']
        congr 1
        exact LinearMap.ext fun z => (PP l).PD_actdR K g z
      rw [h2]
      exact h1
  exact ⟨fun h => inf_eq_left.2 fun y hy => (key y hy).1 h,
    fun h => (Submodule.eq_bot_iff _).2 fun y hy => (key y hy.1).2 h hy.2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiltByRestrictScalarsOfResidualCharacters
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private def Reach {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (S : Set (G →* Aˣ)) (U : Submodule A V) : Prop :=
  ∃ (n : ℕ) (F : ℕ → Submodule A V), F 0 = ⊥ ∧ F n = U ∧ ∀ i < n, F i ≤ F (i + 1) ∧
    ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ Submodule.span A {x} ∧ ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ F i

private theorem reach_bot {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (S : Set (G →* Aˣ)) : Reach ρ S ⊥ :=
  ⟨0, fun _ => ⊥, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

private theorem reach_step {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    {ρ : Representation A G V} {S : Set (G →* Aˣ)} {U : Submodule A V} (h : Reach ρ S U)
    {κ : G →* Aˣ} (hκ : κ ∈ S) {x : V} (hx : ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ U) :
    Reach ρ S (U ⊔ Submodule.span A {x}) := by
  obtain ⟨n, F, h0, hn, hs⟩ := h
  refine ⟨n + 1, fun i => if i ≤ n then F i else U ⊔ Submodule.span A {x}, by simp [h0], by simp, fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · have h1 : i ≤ n := hi.le
    have h2 : i + 1 ≤ n := hi
    simp only [h1, h2, if_true]
    exact hs i hi
  · have h2 : ¬ (i + 1 ≤ i) := by omega
    simp only [h2, le_refl, if_true, if_false, hn]
    exact ⟨le_sup_left, κ, hκ, x, rfl, hx⟩

private theorem reach_fin {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    {ρ : Representation A G V} {S : Set (G →* Aˣ)} {U : Submodule A V} (h : Reach ρ S U)
    {T : Set V} (hT : T.Finite) :
    (∀ x ∈ T, ∃ κ ∈ S, ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ U) → Reach ρ S (U ⊔ Submodule.span A T) := by
  induction T, hT using Set.Finite.induction_on with
  | empty =>
    intro _
    simpa using h
  | @insert a s ha hs ih =>
    intro hall
    have hr := ih (fun y hy => hall y (Set.mem_insert_of_mem a hy))
    obtain ⟨κ, hκ, hk⟩ := hall a (Set.mem_insert a s)
    have hr2 := reach_step hr hκ (x := a) (fun g => Submodule.mem_sup_left (hk g))
    have e : U ⊔ Submodule.span A (insert a s) = U ⊔ Submodule.span A s ⊔ Submodule.span A {a} := by
      rw [Submodule.span_insert]
      ac_rfl
    rw [e]
    exact hr2

theorem UpperTheory.filtBy_restrictScalars_of_residual_characters :
    ∀ {G E B V : Type} [Group G] [Field E] [CommRing B] [Algebra E B] [Module.Finite E B] [AddCommGroup V] [Module B V] [Module E V] [IsScalarTower E B V] (π : B →ₐ[E] E), (∀ a, π a = 0 → IsNilpotent a) → ∀ (ρ : Representation B G V) (S : Set (G →* Eˣ)) {ι : Type} [Finite ι] (x : ι → V) (κ : ι → G →* Eˣ), Submodule.span B (Set.range x) = ⊤ → (∀ j, κ j ∈ S) → (∀ g j, ρ g (x j) - ((κ j g : Eˣ) : E) • x j ∈ (RingHom.ker (π : B →+* E)) • (⊤ : Submodule B V)) → FiltBy (resCoef E ρ) S := by
  intro G E B V _ _ _ _ _ _ _ _ _ π hπ ρ S ι _ x κ hx hκ hstep
  have hnil : IsNilpotent (RingHom.ker (π : B →+* E)) := by
    haveI : IsNoetherianRing B := isNoetherian_of_tower E inferInstance
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro a ha
    exact mem_nilradical.mpr (hπ a ha)
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨M, hM⟩ : ∃ M : ℕ → Submodule E V, ∀ k,
      M k = ((RingHom.ker (π : B →+* E)) ^ k • (⊤ : Submodule B V)).restrictScalars E :=
    ⟨_, fun _ => rfl⟩
  have hMm : ∀ k v, v ∈ M k ↔ v ∈ (RingHom.ker (π : B →+* E)) ^ k • (⊤ : Submodule B V) := by
    intro k v
    rw [hM, Submodule.restrictScalars_mem]
  have down : ∀ p, Reach (resCoef E ρ) S (M (p + 1)) → Reach (resCoef E ρ) S (M p) := by
    intro p h
    have hfg : (((RingHom.ker (π : B →+* E)) ^ p).restrictScalars E).FG := IsNoetherian.noetherian _
    obtain ⟨s, hsf, hs⟩ := Submodule.fg_def.mp hfg
    have hsub : ∀ a ∈ s, a ∈ (RingHom.ker (π : B →+* E)) ^ p := fun a ha => by
      have : a ∈ ((RingHom.ker (π : B →+* E)) ^ p).restrictScalars E := hs ▸ Submodule.subset_span ha
      exact this
    have hTf : (Set.image2 (fun a j => a • x j) s (Set.univ : Set ι)).Finite :=
      hsf.image2 _ Set.finite_univ
    have hr := reach_fin (ρ := resCoef E ρ) (S := S) h hTf (by
      rintro y ⟨a, ha, j, -, rfl⟩
      refine ⟨κ j, hκ j, fun g => ?_⟩
      rw [hMm]
      show ρ g (a • x j) - ((κ j g : Eˣ) : E) • (a • x j) ∈
        ((RingHom.ker (π : B →+* E)) ^ (p + 1) • (⊤ : Submodule B V))
      rw [map_smul, smul_comm ((κ j g : Eˣ) : E) a, ← smul_sub, pow_succ, Submodule.mul_smul]
      exact Submodule.smul_mem_smul (hsub a ha) (hstep g j))
    have claim : ∀ n ∈ Submodule.span B (Set.range x), ∀ a ∈ (RingHom.ker (π : B →+* E)) ^ p,
        a • n ∈ Submodule.span E (Set.image2 (fun a j => a • x j) s (Set.univ : Set ι)) := by
      intro n hn
      induction hn using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        intro a ha
        have ha' : a ∈ Submodule.span E s := by
          rw [hs]
          exact ha
        clear ha
        induction ha' using Submodule.span_induction with
        | mem b hb => exact Submodule.subset_span ⟨b, hb, j, trivial, rfl⟩
        | zero => simp
        | add b c _ _ hb hc =>
          rw [add_smul]
          exact add_mem hb hc
        | smul c b _ hb =>
          rw [smul_assoc]
          exact Submodule.smul_mem _ c hb
      | zero => intro a _; simp
      | add y z _ _ hy hz =>
        intro a ha
        rw [smul_add]
        exact add_mem (hy a ha) (hz a ha)
      | smul b y _ hy =>
        intro a ha
        rw [smul_smul]
        exact hy (a * b) (Ideal.mul_mem_right b _ ha)
    have e : M p = M (p + 1) ⊔ Submodule.span E (Set.image2 (fun a j => a • x j) s (Set.univ : Set ι)) := by
      apply le_antisymm
      · intro v hv
        apply Submodule.mem_sup_right
        rw [hMm] at hv
        refine Submodule.smul_induction_on hv ?_ ?_
        · intro a ha n _
          exact claim n (by rw [hx]; trivial) a ha
        · intro y z hy hz
          exact add_mem hy hz
      · refine sup_le ?_ ?_
        · intro v hv
          rw [hMm] at hv ⊢
          exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ p)) hv
        · rw [Submodule.span_le]
          rintro y ⟨a, ha, j, -, rfl⟩
          show a • x j ∈ M p
          rw [hMm]
          exact Submodule.smul_mem_smul (hsub a ha) trivial
    rw [e]
    exact hr
  have base : M N = ⊥ := by
    rw [hM, hN, Submodule.zero_eq_bot, Submodule.bot_smul, Submodule.restrictScalars_bot]
  have all : ∀ k, Reach (resCoef E ρ) S (M (N - k)) := by
    intro k
    induction k with
    | zero =>
      rw [Nat.sub_zero, base]
      exact reach_bot _ _
    | succ k ih =>
      rcases Nat.lt_or_ge k N with hk | hk
      · have e : N - k = (N - (k + 1)) + 1 := by omega
        rw [e] at ih
        exact down _ ih
      · have e : N - (k + 1) = N - k := by omega
        rw [e]
        exact ih
  have top : M 0 = ⊤ := by
    rw [hM, pow_zero, Ideal.one_eq_top, Submodule.top_smul, Submodule.restrictScalars_top]
  have fin := all N
  rw [Nat.sub_self, top] at fin
  exact fin
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUniqueUnramifiedCocycleFrobeniusValue
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.UnramifiedCocycles

variable {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]

private def SD (_ρ : Representation A G V) : Type := V × G

private instance instGroupSD (ρ : Representation A G V) : Group (SD ρ) where
  mul p q := (p.1 + ρ p.2 q.1, p.2 * q.2)
  one := (0, 1)
  inv p := (-(ρ p.2⁻¹ p.1), p.2⁻¹)
  mul_assoc p q r := by
    refine Prod.ext ?_ (mul_assoc p.2 q.2 r.2)
    change p.1 + ρ p.2 q.1 + ρ (p.2 * q.2) r.1 = p.1 + ρ p.2 (q.1 + ρ q.2 r.1)
    simp [add_assoc]
  one_mul p := by
    refine Prod.ext ?_ (one_mul p.2)
    change (0 : V) + ρ 1 p.1 = p.1
    simp
  mul_one p := by
    refine Prod.ext ?_ (mul_one p.2)
    change p.1 + ρ p.2 0 = p.1
    simp
  inv_mul_cancel p := by
    refine Prod.ext ?_ (inv_mul_cancel p.2)
    change -(ρ p.2⁻¹ p.1) + ρ p.2⁻¹ p.1 = 0
    simp

private instance instTopSD (ρ : Representation A G V) [TopologicalSpace G] [TopologicalSpace V] :
    TopologicalSpace (SD ρ) := inferInstanceAs (TopologicalSpace (V × G))

private theorem topGroup_SD (ρ : Representation A G V) [TopologicalSpace G] [TopologicalSpace V]
    [IsTopologicalGroup G] [IsTopologicalAddGroup V] (h : ContAction ρ) : IsTopologicalGroup (SD ρ) := by
  have hm : Continuous fun x : (V × G) × (V × G) => ((x.1.1 + ρ x.1.2 x.2.1, x.1.2 * x.2.2) : V × G) :=
    (continuous_fst.fst.add (h.comp (continuous_fst.snd.prodMk continuous_snd.fst))).prodMk
      (continuous_fst.snd.mul continuous_snd.snd)
  have hi : Continuous fun x : V × G => ((-(ρ x.2⁻¹ x.1), x.2⁻¹) : V × G) :=
    (h.comp (continuous_snd.inv.prodMk continuous_fst)).neg.prodMk continuous_snd.inv
  exact { continuous_mul := hm, continuous_inv := hi }

private def SDsub (ρ : Representation A G V) (L : AddSubgroup V) (hL : ∀ g, ∀ y ∈ L, ρ g y ∈ L) :
    Subgroup (SD ρ) where
  carrier := {p | p.1 ∈ L}
  mul_mem' := fun {p q} hp hq => L.add_mem hp (hL _ _ hq)
  one_mem' := L.zero_mem
  inv_mem' := fun {p} hp => L.neg_mem (hL _ _ hp)

private theorem all_of_closed [TopologicalSpace G] [IsTopologicalGroup G] {I : Subgroup G} {σ : G}
    (hd : (I ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤) (H : Subgroup G) (hH : IsClosed (H : Set G))
    (hI : I ≤ H) (hσ : σ ∈ H) (g : G) : g ∈ H := by
  have h1 : I ⊔ Subgroup.zpowers σ ≤ H := sup_le hI (Subgroup.zpowers_le.2 hσ)
  have h2 := Subgroup.topologicalClosure_minimal _ h1 hH
  rw [hd] at h2
  exact h2 (Subgroup.mem_top g)

private theorem exists_lattice {l : ℕ} [Fact l.Prime] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V]
    [TopologicalSpace G] [CompactSpace G] (ρ : Representation A G V) (h : ContAction ρ) (x : V) :
    T2Space V ∧ TotallyDisconnectedSpace V ∧
      ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ x ∈ L ∧ ∀ g, ∀ y ∈ L, ρ g y ∈ L := by
  let e : V ≃ₗ[ℚ_[l]] (Fin (Module.finrank ℚ_[l] V) → ℚ_[l]) := (Module.finBasis ℚ_[l] V).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he' : Continuous e.symm := LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap
  let E : V ≃ₜ (Fin (Module.finrank ℚ_[l] V) → ℚ_[l]) :=
    { toEquiv := e.toEquiv, continuous_toFun := he, continuous_invFun := he' }
  have hT2 : T2Space V := E.isEmbedding.t2Space
  have hTD : TotallyDisconnectedSpace V :=
    E.isEmbedding.isTotallyDisconnected_range.1 (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  refine ⟨hT2, hTD, ?_⟩
  have hρc : ∀ g : G, Continuous fun v : V => ρ g v :=
    fun g => h.comp (continuous_const.prodMk continuous_id)
  have hK : IsCompact (Set.range fun g : G => e (ρ g x)) :=
    isCompact_range (he.comp (h.comp (continuous_id.prodMk continuous_const)))
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hK.isBounded
  have hr1 : Set.range (fun g : G => e (ρ g x)) ⊆ Metric.closedBall 0 (max r 1) :=
    hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  let M := (IsUltrametricDist.closedBall_openAddSubgroup (Fin (Module.finrank ℚ_[l] V) → ℚ_[l])
    (lt_of_lt_of_le one_pos (le_max_right r 1))).toAddSubgroup
  have hM : ∀ y, y ∈ M ↔ y ∈ Metric.closedBall (0 : Fin (Module.finrank ℚ_[l] V) → ℚ_[l]) (max r 1) :=
    fun y => Iff.rfl
  let L : AddSubgroup V := ⨅ g : G, M.comap ((e.toLinearMap.toAddMonoidHom).comp (ρ g).toAddMonoidHom)
  have hL : ∀ v, v ∈ L ↔ ∀ g, e (ρ g v) ∈ Metric.closedBall 0 (max r 1) := by
    intro v
    simp only [L, AddSubgroup.mem_iInf, AddSubgroup.mem_comap, hM]
    rfl
  refine ⟨L, ?_, ?_, ?_⟩
  · have hcl : IsClosed (L : Set V) := by
      have : (L : Set V) = ⋂ g : G, (fun v => e (ρ g v)) ⁻¹' Metric.closedBall 0 (max r 1) := by
        ext v
        simp only [SetLike.mem_coe, hL, Set.mem_iInter, Set.mem_preimage]
      rw [this]
      exact isClosed_iInter fun g => Metric.isClosed_closedBall.preimage (he.comp (hρc g))
    have hsub : (L : Set V) ⊆ E ⁻¹' Metric.closedBall 0 (max r 1) := by
      intro v hv
      have := (hL v).1 hv 1
      simpa [E] using this
    exact (E.isCompact_preimage.2 (isCompact_closedBall _ _)).of_isClosed_subset hcl hsub
  · exact (hL x).2 fun g => hr1 ⟨g, rfl⟩
  · intro g y hy
    refine (hL _).2 fun k => ?_
    have := (hL y).1 hy (k * g)
    simpa [map_mul] using this

end UpperTheory.V.Loc.UnramifiedCocycles

open UpperTheory.V.Loc.UnramifiedCocycles in
theorem UpperTheory.V.Loc.existsUnique_unramified_cocycle_frobenius_value :
    ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A (GQ v) V), ContAction ρ → (∀ g ∈ Iq v, ρ g = 1) → ∀ σ : GQ v, UpperTheory.V.Loc.IsFrob σ → ∀ x : V, ∃! c : GQ v → V, c ∈ Z1 ρ ∧ (∀ g ∈ Iq v, c g = 0) ∧ c σ = x := by
  intro v l _ _ A _ _ V _ _ _ _ _ _ _ _ _ ρ hc hI σ hσ x
  obtain ⟨hT2, hTD, L, hLc, hxL, hLs⟩ := exists_lattice (l := l) ρ hc x
  haveI : IsTopologicalGroup (SD ρ) := topGroup_SD ρ hc
  haveI : T2Space (SD ρ) := inferInstanceAs (T2Space (V × GQ v))
  haveI : TotallyDisconnectedSpace (SD ρ) := inferInstanceAs (TotallyDisconnectedSpace (V × GQ v))
  have hS : IsCompact ((SDsub ρ L hLs : Subgroup (SD ρ)) : Set (SD ρ)) := by
    have h0 : IsCompact ((L : Set V) ×ˢ (Set.univ : Set (GQ v))) := hLc.prod isCompact_univ
    have e0 : ((SDsub ρ L hLs : Subgroup (SD ρ)) : Set (SD ρ)) =
        ((L : Set V) ×ˢ (Set.univ : Set (GQ v)) : Set (V × GQ v)) := by
      ext p
      exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
    rw [e0]
    exact h0
  haveI : CompactSpace (SDsub ρ L hLs) := isCompact_iff_compactSpace.1 hS
  obtain ⟨f, hfc, hf1, hfσ⟩ := frobFree σ hσ (SDsub ρ L hLs) ⟨((x, σ) : V × GQ v), hxL⟩
  have hfv : Continuous fun g => ((f g : SD ρ)) := continuous_subtype_val.comp hfc
  have hmul : ∀ g h, ((f (g * h) : SD ρ)) = (f g : SD ρ) * (f h : SD ρ) := fun g h => by
    rw [map_mul]
    rfl
  let k : GQ v → GQ v := fun g => ((f g : SD ρ)).2
  have hk1 : k 1 = 1 := by
    show ((f 1 : SD ρ)).2 = 1
    rw [map_one]
    rfl
  have hkm : ∀ a b, k (a * b) = k a * k b := fun a b => by
    show ((f (a * b) : SD ρ)).2 = _
    rw [hmul]
    rfl
  have hki : ∀ a, k a⁻¹ = (k a)⁻¹ := fun a => by
    have : k a⁻¹ * k a = 1 := by rw [← hkm, inv_mul_cancel, hk1]
    exact eq_inv_of_mul_eq_one_left this
  have hkc : Continuous k := continuous_snd.comp hfv
  have hgw : ∀ w : V, Continuous fun g : GQ v => ρ g w := fun w => hc.comp (continuous_id.prodMk continuous_const)
  have happ : ∀ (g : GQ v) (w : V), ρ g (ρ g⁻¹ w) = w := fun g w => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have happ' : ∀ (g : GQ v) (w : V), ρ g⁻¹ (ρ g w) = w := fun g w => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  let H : Subgroup (GQ v) :=
    { carrier := {g | ∀ w, ρ (k g) w = ρ g w}
      one_mem' := fun w => by simp [hk1]
      mul_mem' := fun {a b} ha hb w => by
        simp only [Set.mem_setOf_eq] at ha hb
        rw [hkm, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha w => by
        simp only [Set.mem_setOf_eq] at ha
        rw [hki]
        calc ρ (k a)⁻¹ w = ρ (k a)⁻¹ (ρ a (ρ a⁻¹ w)) := by rw [happ]
          _ = ρ (k a)⁻¹ (ρ (k a) (ρ a⁻¹ w)) := by rw [ha]
          _ = ρ a⁻¹ w := happ' _ _ }
  have hH : IsClosed (H : Set (GQ v)) := by
    have e1 : (H : Set (GQ v)) = ⋂ w : V, {g | ρ (k g) w = ρ g w} := by
      ext g
      simp [H]
    rw [e1]
    exact isClosed_iInter fun w => isClosed_eq ((hgw w).comp hkc) (hgw w)
  have hIH : Iq v ≤ H := fun g hg w => by
    show ρ ((f g : SD ρ)).2 w = ρ g w
    rw [hf1 g hg, hI g hg]
    show ρ (1 : GQ v) w = (1 : Module.End A V) w
    simp
  have hσH : σ ∈ H := fun w => by
    show ρ ((f σ : SD ρ)).2 w = ρ σ w
    rw [hfσ]
  have hk : ∀ g w, ρ (k g) w = ρ g w := fun g => all_of_closed (frobDense σ hσ) H hH hIH hσH g
  let c : GQ v → V := fun g => ((f g : SD ρ)).1
  have ccont : Continuous c := continuous_fst.comp hfv
  have cco : ∀ g h, c (g * h) = c g + ρ g (c h) := fun g h => by
    show ((f (g * h) : SD ρ)).1 = ((f g : SD ρ)).1 + ρ g ((f h : SD ρ)).1
    rw [hmul]
    exact congrArg (((f g : SD ρ)).1 + ·) (hk g _)
  have cI : ∀ g ∈ Iq v, c g = 0 := fun g hg => by
    show ((f g : SD ρ)).1 = 0
    rw [hf1 g hg]
    rfl
  have cσ : c σ = x := by
    show ((f σ : SD ρ)).1 = x
    rw [hfσ]
  have h1 : ∀ d : GQ v → V, (∀ g h, d (g * h) = d g + ρ g (d h)) → d 1 = 0 := fun d hd => by
    have := hd 1 1
    simpa using this
  have hinv : ∀ d : GQ v → V, (∀ g h, d (g * h) = d g + ρ g (d h)) → ∀ g, d g⁻¹ = -(ρ g⁻¹ (d g)) :=
    fun d hd g => by
      have := hd g⁻¹ g
      rw [inv_mul_cancel, h1 d hd] at this
      exact eq_neg_of_add_eq_zero_left this.symm
  refine ⟨c, ⟨⟨ccont, cco⟩, cI, cσ⟩, ?_⟩
  rintro c' ⟨hZ, hc'I, hc'σ⟩
  obtain ⟨c'cont, c'co⟩ : Continuous c' ∧ ∀ g h, c' (g * h) = c' g + ρ g (c' h) := hZ
  let H' : Subgroup (GQ v) :=
    { carrier := {g | c' g = c g}
      one_mem' := by
        show c' 1 = c 1
        rw [h1 c' c'co, h1 c cco]
      mul_mem' := fun {a b} ha hb => by
        show c' (a * b) = c (a * b)
        rw [c'co, cco, show c' a = c a from ha, show c' b = c b from hb]
      inv_mem' := fun {a} ha => by
        show c' a⁻¹ = c a⁻¹
        rw [hinv c' c'co, hinv c cco, show c' a = c a from ha] }
  have hH' : IsClosed (H' : Set (GQ v)) := isClosed_eq c'cont ccont
  have hIH' : Iq v ≤ H' := fun g hg => by
    show c' g = c g
    rw [hc'I g hg, cI g hg]
  have hσH' : σ ∈ H' := by
    show c' σ = c σ
    rw [hc'σ, cσ]
  funext g
  exact all_of_closed (frobDense σ hσ) H' hH' hIH' hσH' g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ContinuousUnitsInvOfContinuousCoeFiniteQpAlgebra
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.continuous_units_inv_of_continuous_coe_finite_Qp_algebra :
    ∀ {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] {X : Type} [TopologicalSpace X] (f : X → Bˣ), Continuous (fun x => (f x : B)) → Continuous fun x => (((f x)⁻¹ : Bˣ) : B) := by
  intro l _ B _ _ _ _ _ _ X _ f hf
  classical
  let b := Module.finBasis ℚ_[l] B
  let M := Algebra.leftMulMatrix b
  let E : (Fin (Module.finrank ℚ_[l] B) → ℚ_[l]) →ₗ[ℚ_[l]] B := b.equivFun.symm.toLinearMap
  have key : ∀ u : Bˣ, ((u⁻¹ : Bˣ) : B) = E (Matrix.mulVec (M (u : B))⁻¹ (b.repr 1)) := by
    intro u
    have hinv : (M (u : B))⁻¹ = M ((u⁻¹ : Bˣ) : B) := by
      apply Matrix.inv_eq_left_inv
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hinv, Algebra.leftMulMatrix_mulVec_repr, mul_one]
    simp [E]
  have hM : Continuous fun y : B => M y :=
    IsModuleTopology.continuous_of_linearMap M.toLinearMap
  have hE : Continuous E := LinearMap.continuous_on_pi E
  have hcomp : Continuous fun x => E (Matrix.mulVec (M (f x : B))⁻¹ (b.repr 1)) := by
    refine hE.comp ?_
    refine Continuous.matrix_mulVec ?_ continuous_const
    rw [continuous_iff_continuousAt]
    intro x
    refine ContinuousAt.comp (f := fun x => M (f x : B)) (g := Inv.inv) ?_ (hM.comp hf).continuousAt
    apply continuousAt_matrix_inv
    have hdet : IsUnit (M (f x : B)).det := by
      have : IsUnit (M (f x : B)) := (f x).isUnit.map M
      exact (Matrix.isUnit_iff_isUnit_det _).1 this
    obtain ⟨d, hd⟩ := hdet
    rw [← hd]
    exact NormedRing.inverse_continuousAt d
  simpa only [← key] using hcomp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsAlgebraicElementOfAlgebraicVectorSubspace
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TiltFrobeniusActionPowAndInertiaTrivialOfPowEqSe
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

namespace UpperTheory.V.Loc

variable {l : ℕ} [hl : Fact l.Prime]

open scoped Formalism.Per in
private theorem tf_lift (y : OCb l) {m : ℕ} (hm : 0 < m) (hy : y ^ l ^ m = y) :
    ∃ (z : OC l) (x : Om l), (z : ℂ_[l]) = (x : ℂ_[l]) ∧ x ^ l ^ m = x ∧
      PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) z := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  have hz : y.untilt ^ l ^ m = y.untilt := by rw [← map_pow, hy]
  have hz' : ((y.untilt : OC l) : ℂ_[l]) ^ l ^ m = (y.untilt : OC l) := by
    have := congrArg (fun t : OC l => (t : ℂ_[l])) hz
    simpa using this
  have hint : IsIntegral (Om l) ((y.untilt : OC l) : ℂ_[l]) := by
    refine ⟨X ^ l ^ m - X, monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1), ?_⟩
    simp [hz']
  obtain ⟨x, hx⟩ := minpoly.mem_range_of_degree_eq_one (Om l) _
    (IsAlgClosed.degree_eq_one_of_irreducible (Om l) (minpoly.irreducible hint))
  refine ⟨y.untilt, x, hx.symm, ?_, (PreTilt.mk_untilt_eq_coeff_zero y).symm⟩
  apply (algebraMap (Om l) ℂ_[l]).injective
  have hx' : algebraMap (Om l) ℂ_[l] x = (y.untilt : OC l) := hx
  rw [map_pow, hx', hz']

private theorem tf_act {P : LocPrime l} (AI : LocAinf l P) (y : OCb l) {m : ℕ} (hm : 0 < m) (hy : y ^ l ^ m = y)
    {z : OC l} {x : Om l} (hzx : (z : ℂ_[l]) = (x : ℂ_[l]))
    (h0 : PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) z)
    (g : GQ l) (k : ℕ) (hg : g x = x ^ k) : AI.actT g y = y ^ k := by
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g y 0 _ h0
  rw [hzx, AI.actC_ext, hg, PadicComplex.coe_eq, map_pow, ← PadicComplex.coe_eq, ← hzx] at h1
  have h3 : y' = z ^ k := Subtype.ext (by rw [h1]; simp)
  refine GlobalTheory.UnramifiedCrys.eq_of_coeff_zero hm (by rw [← map_pow, hy])
    (by rw [← pow_mul, mul_comm, pow_mul, hy]) ?_
  rw [h2, map_pow, h0, h3]
  exact map_pow _ _ _

private theorem tf_root {x : Om l} {m : ℕ} (hm : 0 < m) (hx : x ^ l ^ m = x) (h0 : x ≠ 0) :
    ∃ n, 0 < n ∧ ¬ l ∣ n ∧ x ^ n = 1 := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  refine ⟨l ^ m - 1, by omega, fun h => ?_, ?_⟩
  · have h2 := (Nat.dvd_sub_iff_right h1.le (dvd_pow_self l hm.ne')).mp h
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h2)
  · apply mul_right_cancel₀ h0
    rw [← pow_succ, one_mul, Nat.sub_add_cancel h1.le, hx]

end UpperTheory.V.Loc

theorem UpperTheory.tilt_frobenius_action_pow_and_inertia_trivial_of_pow_eq_self :
    ∀ {l : ℕ} [Fact l.Prime] (y : OCb l) (m : ℕ), 0 < m → y ^ l ^ m = y → (∀ σ : GQ l, IsFrob σ → (AIP l).actT σ y = y ^ l) ∧ ∀ g ∈ Iq l, (AIP l).actT g y = y := by
  intro l hl y m hm hy
  obtain ⟨z, x, hzx, hx, h0⟩ := tf_lift y hm hy
  refine ⟨fun σ hσ => tf_act _ y hm hy hzx h0 σ l ?_, fun g hg => ?_⟩
  · by_cases hx0 : x = 0
    · rw [hx0, map_zero, zero_pow hl.out.ne_zero]
    obtain ⟨n, hn0, hn, hxn⟩ := tf_root hm hx hx0
    have hnorm : ‖x‖ = 1 := by
      have h1 : ‖x‖ ^ n = 1 := by rw [← norm_pow, hxn, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn0.ne').mp h1
    exact KStar.IdealValuations.norm_aut_and_roots.2 n _ _ hn (by rw [← map_pow, hxn, map_one])
      (by rw [← pow_mul, mul_comm, pow_mul, hxn, one_pow]) (hσ x hnorm.le)
  · refine (tf_act _ y hm hy hzx h0 g 1 ?_).trans (pow_one y)
    rw [pow_one]
    by_cases hx0 : x = 0
    · rw [hx0, map_zero]
    rw [Iq, IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg x (IntermediateField.subset_adjoin _ _ (tf_root hm hx hx0))
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial
open GlobalTheory.UnramifiedCrys

private theorem exists_alg {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R]
    (ρ : G →* (R ≃+* R)) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [CharP R p]
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (hM : Continuous M)
    (hJ : ∀ g, (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → ρ g y = y) → M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) (WittVector p R), IsUnit W.det ∧
      ∀ g (f : R →+* R), (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → f y = ρ g y) →
        (M g).map (zlW p R) * W.map (WittVector.map f) = W :=
  _root_.UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.exists_alg ρ hopen M hM hJ

theorem UpperTheory.exists_algebraic_element_of_algebraicVectorSubspace :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ_[l]), IsUnit C.det → ∃ N N' : Matrix (Fin n) (Fin n) (Bcr l), N * N' = 1 ∧ (∀ i j, (PP l).ιB (N i j) ∈ ((PP l).PD (botExt l)).Fil 0) ∧ (∀ i j, (PP l).ιB (N' i j) ∈ ((PP l).PD (botExt l)).Fil 0) ∧ N.map (PP l).φB = C.map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l])) * N ∧ ∀ g ∈ Iq l, N.map ((PP l).actQ g) = N := by
  intro l _ n C hC
  obtain ⟨-, -, hI, ⟨σ, hσ⟩, -⟩ := iqBasic l
  obtain ⟨Ti⟩ := tiedP l
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det C).2 hC
  haveI : CompactSpace (Matrix (Fin n) (Fin n) ℤ_[l]) := inferInstanceAs (CompactSpace (Fin n → Fin n → ℤ_[l]))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) ℤ_[l]) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → ℤ_[l]))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) ℤ_[l])ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℤ_[l])).symm.isEmbedding.isTotallyDisconnected_range.1
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) ℤ_[l])ˣ :=
    Units.isEmbedding_embedProduct.isTotallyDisconnected_range.1
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  obtain ⟨f, hf, hfI, hfσ⟩ := frobFree σ hσ (Matrix (Fin n) (Fin n) ℤ_[l])ˣ u⁻¹
  obtain ⟨W, hW, hWg⟩ := exists_alg (p := l) (AIP l).actT (eventually_actT_eq (AIP l))
    ((Units.coeHom _).comp f) (Units.continuous_val.comp hf)
    (fun g hg => congrArg Units.val (hfI g ((hI g).2 (norm_sub_lt_one_of_fix (AIP l) g hg))))
  refine ⟨(AIP l).ιA.mapMatrix W, (AIP l).ιA.mapMatrix W⁻¹, ?_, fun i j => (AIP l).ainf_image_mem_filtration_zero _ _,
    fun i j => (AIP l).ainf_image_mem_filtration_zero _ _, ?_, fun g hg => ?_⟩
  · rw [← map_mul, Matrix.mul_nonsing_inv _ hW, map_one]
  · have h := hWg σ (frobenius _ l) fun m hm y hy => ((UpperTheory.tilt_frobenius_action_pow_and_inertia_trivial_of_pow_eq_self y m hm hy).1 σ hσ).symm
    have h1 : W.map (WittVector.map (frobenius _ l)) = (zlW l (OCb l)).mapMatrix u * W := by
      conv_rhs => rw [← h, ← Matrix.mul_assoc]
      have e : (((Units.coeHom _).comp f) σ).map (zlW l (OCb l)) = (zlW l (OCb l)).mapMatrix (↑u⁻¹) := by
        rw [← hfσ]; rfl
      rw [e, ← map_mul, Units.mul_inv, map_one, Matrix.one_mul]
    have h2 := congrArg (AIP l).ιA.mapMatrix h1
    rw [map_mul] at h2
    convert h2 using 1
    · ext i j
      change (PP l).φB ((AIP l).ιA (W i j)) = (AIP l).ιA (WittVector.map (frobenius _ l) (W i j))
      rw [← (AIP l).ιA_φ, WittVector.frobenius_eq_map_frobenius]
    · congr 1
      ext i j
      exact (ιA_zlW (AIP l) Ti _).symm
  · have h := hWg 1 ((AIP l).actT g).toRingHom fun m hm y hy => by
      rw [map_one, RingAut.one_apply]
      exact (UpperTheory.tilt_frobenius_action_pow_and_inertia_trivial_of_pow_eq_self y m hm hy).2 g hg
    rw [map_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul] at h
    ext i j
    change (PP l).actQ g ((AIP l).ιA (W i j)) = (AIP l).ιA (W i j)
    rw [← (AIP l).ιA_act]
    exact congrArg (AIP l).ιA (congrFun (congrFun h i) j)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RankCohomologyRationalEqRankLattice
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.rank_cohomology_rational_eq_rank_lattice :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] G V), ContAction ρ → ∀ {n : ℕ} (ρT : Representation ℤ_[l] G (Fin n → ℤ_[l])) (j : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] V), ContAction ρT → IsOpenEmbedding j → (∀ g x, j (ρT g x) = ρ g (j x)) → (∀ y : V, ∃ m : ℕ, (l : ℤ_[l]) ^ m • y ∈ LinearMap.range j) → Module.rank ℚ_[l] ↥(H0 ρ) = Module.rank ℤ_[l] ↥(H0 ρT) ∧ Module.rank ℚ_[l] (H1 ρ) = Module.rank ℤ_[l] (H1 ρT) ∧ Module.rank ℚ_[l] (H2 ρ) = Module.rank ℤ_[l] (H2 ρT) := by
  intro l _ G _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ n ρT j hT hj he hm
  haveI : ContinuousConstSMul ℤ_[l] V := ⟨fun c => by
    have h : (fun x : V => c • x) = fun x => (algebraMap ℤ_[l] ℚ_[l] c) • x :=
      funext fun x => (algebraMap_smul ℚ_[l] c x).symm
    rw [h]
    exact continuous_const_smul _⟩
  let L : ReciprocityTheory.Coh.TRep ℤ_[l] G := { V := Fin n → ℤ_[l], rho := ρT, cont := hT }
  let U : ReciprocityTheory.Coh.TRep ℤ_[l] G := { V := V, rho := resCoef ℤ_[l] ρ, cont := hρ }
  let P : ReciprocityTheory.Coh.Pair L U := ⟨MonoidHom.id G, j, continuous_id, hj.continuous, he⟩
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl' : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hloc := ReciprocityTheory.Coh.localise_holds ℤ_[l] G (l : ℤ_[l]) L U P rfl hj
    ⟨Homeomorph.smulOfNeZero (α := V) (l : ℚ_[l]) hl, fun (v : V) => by
      show (l : ℚ_[l]) • v = (l : ℤ_[l]) • v
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]⟩ hm
  have hp : Submonoid.powers (l : ℤ_[l]) ≤ nonZeroDivisors ℤ_[l] :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hl'
  have hr : ∀ k, Module.rank ℤ_[l] (U.H k) = Module.rank ℤ_[l] (L.H k) := fun k =>
    haveI := hloc k
    IsLocalizedModule.rank_eq (Submonoid.powers (l : ℤ_[l])) hp (P.hom.H k)
  obtain ⟨a₀, a₁, a₂, -⟩ := ReciprocityTheory.Coh.exists_isLow L
  obtain ⟨b₀, b₁, b₂, -⟩ := ReciprocityTheory.Coh.exists_isLow U
  obtain ⟨⟨c₀⟩, ⟨c₁⟩, ⟨c₂⟩, -⟩ := UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv ℤ_[l] ρ
  refine ⟨?_, ?_, ?_⟩
  · rw [IsFractionRing.rank_right_eq (R := ℤ_[l]) ℚ_[l]]
    exact (b₀.trans c₀).rank_eq.symm.trans ((hr 0).trans a₀.rank_eq)
  · rw [IsFractionRing.rank_right_eq (R := ℤ_[l]) ℚ_[l]]
    exact (b₁.trans c₁).rank_eq.symm.trans ((hr 1).trans a₁.rank_eq)
  · rw [IsFractionRing.rank_right_eq (R := ℤ_[l]) ℚ_[l]]
    exact (b₂.trans c₂).rank_eq.symm.trans ((hr 2).trans a₂.rank_eq)
end
