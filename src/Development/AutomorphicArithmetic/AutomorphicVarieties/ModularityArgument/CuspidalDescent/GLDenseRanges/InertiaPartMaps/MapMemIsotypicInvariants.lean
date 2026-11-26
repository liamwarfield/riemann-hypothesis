module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.RankInvTBox
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.LinkedUnitaryEndsOfInputs

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.MapMemIsotypicInvariants
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

section Abs

variable {G W W' : Type} [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private theorem map_mem_isotypic_invariants {m : ℕ} (K₁ : Subgroup G) (τ₀ : K₁ →* GL (Fin m) ℂ)
    (ρ : Representation ℂ G W) (ρ' : Representation ℂ G W') (e : W →ₗ[ℂ] W')
    (h₁ : ∀ k ∈ K₁, ∀ x, e (ρ k x) = ρ' k (e x))
    {F : Fin m → W} (hF : F ∈ inv1 K₁ τ₀ ρ) : (fun i => e (F i)) ∈ inv1 K₁ τ₀ ρ' := by
  refine ⟨fun k i => ?_, fun k _ i => ?_⟩
  · have h := congrArg e (hF.1 k i)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, MonoidHom.comp_apply, MonoidHom.coe_fst, h₁ k.1 k.2] at h
    simpa only [MonoidHom.comp_apply, MonoidHom.coe_fst] using h
  · simp

private theorem rank_isotypic_invariants_eq {m : ℕ} (K₁ : Subgroup G) (τ₀ : K₁ →* GL (Fin m) ℂ)
    (ρ : Representation ℂ G W) (ρ' : Representation ℂ G W') (e : W ≃ₗ[ℂ] W')
    (h₁ : ∀ k ∈ K₁, ∀ x, e (ρ k x) = ρ' k (e x)) :
    Module.rank ℂ (inv1 K₁ τ₀ ρ) = Module.rank ℂ (inv1 K₁ τ₀ ρ') := by
  have s₁ : ∀ k ∈ K₁, ∀ x, e.symm (ρ' k x) = ρ k (e.symm x) := fun k hk x =>
    e.injective (by rw [h₁ k hk, e.apply_symm_apply, e.apply_symm_apply])
  let E : (Fin m → W) ≃ₗ[ℂ] (Fin m → W') := LinearEquiv.piCongrRight fun _ => e
  have hE : (inv1 K₁ τ₀ ρ).map (E : (Fin m → W) →ₗ[ℂ] (Fin m → W')) = inv1 K₁ τ₀ ρ' := by
    refine le_antisymm ?_ fun F hF => ?_
    · rintro _ ⟨F, hF, rfl⟩
      exact map_mem_isotypic_invariants K₁ τ₀ ρ ρ' e.toLinearMap h₁ hF
    · refine ⟨fun i => e.symm (F i), map_mem_isotypic_invariants K₁ τ₀ ρ' ρ e.symm.toLinearMap s₁ hF, ?_⟩
      funext i
      exact e.apply_symm_apply (F i)
  exact (LinearEquiv.ofSubmodules E _ _ hE).rank_eq

end Abs

section Fam

variable {I : Type} {Gi Wi Wi' : I → Type} [∀ i, Group (Gi i)]
  [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] [∀ i, AddCommGroup (Wi' i)] [∀ i, Module ℂ (Wi' i)]

private theorem congr_piRep (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (τ' : ∀ i, Representation ℂ (Gi i) (Wi' i))
    (a : ∀ i, Wi i ≃ₗ[ℂ] Wi' i) (g : ∀ i, Gi i) (h : ∀ i x, a i (τ i (g i) x) = τ' i (g i) (a i x))
    (x : ⨂[ℂ] i, Wi i) : PiTensorProduct.congr a (piRep τ g x) = piRep τ' g (PiTensorProduct.congr a x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [piRep, PiTensorProduct.congr, map_smul, MonoidHom.comp_apply, PiTensorProduct.mapMonoidHom_apply, LinearEquiv.ofLinear_apply, PiTensorProduct.map_tprod]
    exact congrArg (fun t => r • PiTensorProduct.tprod ℂ t) (funext fun i => h i (f i))
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end Fam

theorem invEq1 : InvEq1 := by
  intro l _ L Ω _ _ _ _ _ _ s n _ V _ c ι m τ₀ σ σ' C C' hu
  refine rank_isotypic_invariants_eq (KT n (wt s)) _ _ _ (PiTensorProduct.congr fun u => (hu u).some.toLinearEquiv) ?_
  intro g hg x
  refine congr_piRep _ _ _ g (fun u y => ?_) x
  exact LinearMap.congr_fun ((hu u).some.isIntertwining' ⟨g u, hg u (Set.mem_univ u)⟩) y

end UpperTheory.V.Z.Desc.V0
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.CmpOverL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.J.D
open UpperTheory.V.Z.Desc.V0

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.Desc.V0.InertiaSectionNorm

private theorem Kc_conj {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {g x : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (hx : x ∈ Kc k n 1) : g⁻¹ * x * g ∈ Kc k n 1 := by
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨b, hb, rfl⟩ := hx
  refine ⟨a⁻¹ * b * a, ?_, by simp only [map_mul, map_inv]⟩
  have hb' := MonoidHom.mem_ker.1 hb
  exact MonoidHom.mem_ker.2 (by simp only [map_mul, map_inv, hb', mul_one, inv_mul_cancel])

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {n : ℕ}

private theorem cmp_of {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dite_eq_left h]
  rfl

private theorem ext_cmp {x y : Ga l L n} (h : ∀ w, cmp n w x = cmp n w y) : x = y := by
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  obtain ⟨y, rfl⟩ := (away l L n).rangeRestrict_surjective y
  refine Subtype.ext (funext fun w => ?_)
  have e := h w.1
  rwa [cmp_of w.2, cmp_of w.2] at e

private theorem comm_of {a b : Ga l L n} (h : ∀ w, cmp n w a = 1 ∨ cmp n w b = 1) : Commute a b := by
  refine ext_cmp fun w => ?_
  rw [map_mul, map_mul]
  rcases h w with h | h <;> rw [h] <;> simp

variable (s : HidaSetting l L Ω)

private theorem sec_one (w w' : Plc L) (h : GLw n w) (hw : w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) :
    cmp n w' (sec n s w h : Ga l L n) = 1 := by
  unfold CaseU.sec
  split_ifs with hb
  · have hm := ((MulEquiv.ofBijective _ hb).symm h).2
    exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hm w') hw)
  · exact map_one _

private theorem secS_spec (h : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) (g : GS n s) :
    toGS n s (secS n s g) = g ∧ secS n s g ∈ GaS n s := by
  unfold secS
  rw [dite_eq_left h]
  exact ⟨(MulEquiv.ofBijective _ h).apply_symm_apply g, ((MulEquiv.ofBijective _ h).symm g).2⟩

private theorem mem_GaS {x : Ga l L n} (hx : x ∈ GaS n s) {w : Plc L}
    (hw : w.under (𝓞 (Lp L)) ∉ s.St ∧ w.under (𝓞 (Lp L)) ≠ s.v0) : cmp n w x = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx w) hw)

private theorem notS {w : Plc L} (h : w.under (𝓞 (Lp L)) ∉ s.S) :
    w.under (𝓞 (Lp L)) ∉ s.St ∧ w.under (𝓞 (Lp L)) ≠ s.v0 :=
  ⟨fun e => h (Or.inr (Or.inl e)), fun e => h (Or.inr (Or.inr e))⟩

end UpperTheory.V.Z.Desc.V0.InertiaSectionNorm

open UpperTheory.V.Z.Desc.V0.InertiaSectionNorm in
theorem UpperTheory.V.Z.Desc.V0.normS :
    NormS := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V hV Q c m τ₀
  obtain ⟨hb, hcomm, hdesc⟩ := secSp l L Ω s n hn V hV
  have spec := secS_spec (n := n) s hb
  have hq : IsEmpty Q.Q := ⟨fun q => Q.notS q (by
    have h : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
      rw [Q.range]
      exact Or.inr ⟨q, rfl⟩
    rwa [hV] at h)⟩
  have hlev : ∀ K, (hset Q τ₀).lev K = (hset Q τ₀).UQ := fun K => by
    haveI : IsEmpty (hset Q τ₀).Q := hq
    unfold HSet.lev
    rw [iSup_of_empty]
    exact sup_bot_eq _
  have h0 : ∀ (g : GLw n (s.w s.v0)) (t : s.St), cmp n (s.w t) (sec0 n s g) = 1 := fun g t =>
    congrFun (congrArg Prod.fst (spec (1, g)).1) t
  have hτ : ∀ (u u' : Ub n s), (∀ t : s.St, cmp n (s.w t) (u : Ga l L n) = cmp n (s.w t) (u' : Ga l L n)) →
      (hset Q τ₀).τ u = (hset Q τ₀).τ u' := fun u u' h =>
    congrArg τ₀ (Subtype.ext (funext h))
  have huq : ∀ g : GLw n (s.w s.v0), g ∈ KO _ (Fin n) → ∀ u ∈ UQ n Q, ∃ u' ∈ UQ n Q,
      (u' : Ga l L n) = (sec0 n s g)⁻¹ * (u : Ga l L n) * sec0 n s g ∧ (hset Q τ₀).τ u' = (hset Q τ₀).τ u := by
    intro g hg u hu
    obtain ⟨k, hk, p, hp, e⟩ := (hdesc Q (u : Ga l L n)).1 ⟨u, hu, rfl⟩
    have hp' : ((p.1, g⁻¹ * p.2 * g) : GS n s) ∈ (KT n (wt s)).prod (Kc _ n 1) :=
      Subgroup.mem_prod.2 ⟨(Subgroup.mem_prod.1 hp).1, Kc_conj hg (Subgroup.mem_prod.1 hp).2⟩
    have hconj : ((p.1, g⁻¹ * p.2 * g) : GS n s) = ((1, g) : GS n s)⁻¹ * p * (1, g) :=
      Prod.ext (by simp) (by simp)
    have e' : (sec0 n s g)⁻¹ * (u : Ga l L n) * sec0 n s g = secS n s (p.1, g⁻¹ * p.2 * g) * k := by
      have hc : k * sec0 n s g = sec0 n s g * k := (hcomm (1, g) k hk).eq.symm
      rw [hconj, map_mul, map_mul, map_inv, e]
      change (sec0 n s g)⁻¹ * (secS n s p * k) * sec0 n s g = (sec0 n s g)⁻¹ * secS n s p * sec0 n s g * k
      simp only [mul_assoc, hc]
    obtain ⟨u', hu', e''⟩ := (hdesc Q _).2 ⟨k, hk, _, hp', e'⟩
    have e3 : (u' : Ga l L n) = (sec0 n s g)⁻¹ * (u : Ga l L n) * sec0 n s g := e''
    refine ⟨u', hu', e3, hτ _ _ fun t => ?_⟩
    rw [e3, map_mul, map_mul, map_inv, h0, inv_one, one_mul, mul_one]
  refine ⟨fun g hg => ⟨fun K u hu => ?_, fun u hu => huq g hg u hu, fun w hw h => ?_⟩, fun g hg => ?_⟩
  · rw [hlev] at hu
    obtain ⟨u', hu', h⟩ := huq g hg u hu
    exact ⟨u', by rw [hlev]; exact hu', h⟩
  · refine comm_of fun w' => ?_
    by_cases hu : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
    · refine Or.inl (mem_GaS s (spec (1, g)).2 (notS s ?_))
      rw [hu, ← hV]
      exact hw.1
    · exact Or.inr (sec_one s w w' h hu)
  · obtain ⟨u, hu, e⟩ := (hdesc Q (sec0 n s g)).2 ⟨1, one_mem _, (1, g),
      Subgroup.mem_prod.2 ⟨one_mem _, hg⟩, (mul_one _).symm⟩
    have e3 : (u : Ga l L n) = sec0 n s g := e
    refine ⟨u, hu, e3, ?_⟩
    exact (hτ u 1 fun t => by rw [e3, h0]; exact (map_one _).symm).trans (map_one (hset Q τ₀).τ)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.ZeInfRep
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.J.D
open UpperTheory.V.Z.Desc.V0
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

section Abstract

variable {M : Type} [AddCommGroup M] [Module ℂ M] {J : Type} [Fintype J]

private theorem ze_zero (Y : J → Submodule ℂ M) (hY : iSupIndep Y) (x : J → M) (hx : ∀ i, x i ∈ Y i)
    (h : ∑ i, x i = 0) (i : J) : x i = 0 := by
  classical
  have h1 : x i = - ∑ j ∈ Finset.univ.erase i, x j := by
    rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    exact h
  have h2 : x i ∈ ⨆ (j) (_ : j ≠ i), Y j := by
    rw [h1]
    refine neg_mem (sum_mem fun j hj => ?_)
    exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hj) (hx j))
  exact Submodule.disjoint_def.1 (hY i) _ (hx i) h2

private theorem ze_dec (D : J → Submodule ℂ M) {F : M} (h : F ∈ ⨆ i, D i) :
    ∃ x : J → M, (∀ i, x i ∈ D i) ∧ ∑ i, x i = F := by
  classical
  induction h using Submodule.iSup_induction' with
  | mem i y hy =>
    refine ⟨Pi.single i y, fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same]
        exact hy
      · rw [Pi.single_eq_of_ne hj]
        exact zero_mem _
    · rw [Finset.sum_eq_single i (fun j _ hj => Pi.single_eq_of_ne hj _) (fun h => absurd (Finset.mem_univ i) h),
        Pi.single_eq_same]
  | zero => exact ⟨0, fun _ => zero_mem _, Finset.sum_const_zero⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, hb, rfl⟩ := hz
    exact ⟨a + b, fun i => add_mem (ha i) (hb i), Finset.sum_add_distrib⟩

private theorem ze_rank (E : J → Submodule ℂ M) (hE : iSupIndep E) (Z : Submodule ℂ M) [FiniteDimensional ℂ Z]
    (hZ : ∀ i, E i ≤ Z) : Module.finrank ℂ ↥(⨆ i, E i) = ∑ i, Module.finrank ℂ ↥(E i) := by
  classical
  have key : ∀ s : Finset J, Module.finrank ℂ ↥(⨆ i ∈ s, E i) = ∑ i ∈ s, Module.finrank ℂ ↥(E i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 : (⨆ i ∈ (∅ : Finset J), E i) = ⊥ :=
        le_bot_iff.1 (iSup₂_le fun i hi => absurd hi (Finset.notMem_empty i))
      rw [h0, finrank_bot, Finset.sum_empty]
    | insert a s ha ih =>
      have hs : (⨆ i ∈ s, E i) ≤ Z := iSup₂_le fun i _ => hZ i
      haveI : FiniteDimensional ℂ ↥(E a) := Submodule.finiteDimensional_of_le (hZ a)
      haveI : FiniteDimensional ℂ ↥(⨆ i ∈ s, E i) := Submodule.finiteDimensional_of_le hs
      have hd : Disjoint (E a) (⨆ i ∈ s, E i) :=
        hE.disjoint_biSup (y := (s : Set J)) fun h => ha (Finset.mem_coe.1 h)
      have h := Submodule.finrank_sup_add_finrank_inf_eq (E a) (⨆ i ∈ s, E i)
      rw [hd.eq_bot, finrank_bot, add_zero, ih] at h
      rw [Finset.iSup_insert, Finset.sum_insert ha]
      exact h
  have h1 : (⨆ i ∈ (Finset.univ : Finset J), E i) = ⨆ i, E i := iSup_congr fun i => iSup_pos (Finset.mem_univ i)
  rw [← h1]
  exact key Finset.univ

private theorem ze_main (Y : J → Submodule ℂ M) (hY : iSupIndep Y) (Z : Submodule ℂ M) [FiniteDimensional ℂ Z]
    (hZ : Module.finrank ℂ Z = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z)) (P : Module.End ℂ M)
    (hP : ∀ i, ∀ y ∈ Y i, P y ∈ Y i) :
    Module.finrank ℂ ↥(Z ⊓ LinearMap.ker P) = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z ⊓ LinearMap.ker P) := by
  have hE : iSupIndep fun i => Y i ⊓ Z := hY.mono fun _ => inf_le_left
  have h1 := ze_rank (fun i => Y i ⊓ Z) hE Z fun _ => inf_le_right
  have hs : (⨆ i, Y i ⊓ Z) = Z :=
    Submodule.eq_of_le_of_finrank_eq (iSup_le fun _ => inf_le_right) (by rw [h1, hZ])
  have hB : Z ⊓ LinearMap.ker P ≤ ⨆ i, Y i ⊓ (Z ⊓ LinearMap.ker P) := by
    intro F hF
    have hF1 : F ∈ ⨆ i, Y i ⊓ Z := by
      rw [hs]
      exact hF.1
    obtain ⟨x, hx, rfl⟩ := ze_dec (fun i => Y i ⊓ Z) hF1
    refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨(hx i).1, (hx i).2, ?_⟩
    have h0 : ∑ i, P (x i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum]
      exact hF.2
    exact ze_zero Y hY (fun i => P (x i)) (fun i => hP i _ (hx i).1) h0 i
  have hE' : iSupIndep fun i => Y i ⊓ (Z ⊓ LinearMap.ker P) := hY.mono fun _ => inf_le_left
  haveI : FiniteDimensional ℂ ↥(Z ⊓ LinearMap.ker P) := Submodule.finiteDimensional_of_le inf_le_left
  have hs' : (⨆ i, Y i ⊓ (Z ⊓ LinearMap.ker P)) = Z ⊓ LinearMap.ker P :=
    le_antisymm (iSup_le fun _ => inf_le_right) hB
  have h := ze_rank (fun i => Y i ⊓ (Z ⊓ LinearMap.ker P)) hE' (Z ⊓ LinearMap.ker P) fun _ => inf_le_right
  rw [hs'] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => by rw [inf_assoc]

private theorem ze_opE {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (a : G →₀ ℤ)
    (Y : Submodule ℂ W) (h : ∀ g ∈ a.support, ∀ y ∈ Y, ρ g y ∈ Y) (N : ℕ) :
    ∀ y ∈ Y, (opE ρ a - (N : Module.End ℂ W)) y ∈ Y := by
  intro y hy
  rw [LinearMap.sub_apply]
  refine Y.sub_mem ?_ ?_
  · unfold opE Finsupp.sum
    rw [LinearMap.sum_apply]
    exact Y.sum_mem fun g hg => zsmul_mem (h g hg y hy) _
  · rw [Module.End.natCast_apply]
    exact nsmul_mem hy N

end Abstract

section Gen

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ)

private theorem ze_big (g : H.Ga) (hg : Norm H g) : ∀ F ∈ H.Big ι ξ, trF H d g F ∈ H.Big ι ξ := fun F hF => by
  refine ⟨fun i hi γ x => ?_, fun u hu => ?_⟩
  · have := hF.1 i hi γ (x * ((g, 1) : H.Ga × GV n H.Sl))
    rw [← mul_assoc] at this
    exact this
  · obtain ⟨u', hu', e1, e2⟩ := hg.uq u hu
    ext i x k
    have h : ((H.τC ι u' : Matrix (Fin H.m) (Fin H.m) ℂ).mulVec
        fun j => F j (x * ((g, 1) : H.Ga × GV n H.Sl) * ((u' : H.Ga), 1)) k) i =
        F i (x * ((g, 1) : H.Ga × GV n H.Sl)) k :=
      congrFun (congrFun (congrFun (hF.2 u' hu') i) (x * ((g, 1) : H.Ga × GV n H.Sl))) k
    change ((H.τC ι u : Matrix (Fin H.m) (Fin H.m) ℂ).mulVec
      fun j => F j (x * ((u : H.Ga), 1) * ((g, 1) : H.Ga × GV n H.Sl)) k) i = F i (x * ((g, 1) : H.Ga × GV n H.Sl)) k
    have e3 : H.τC ι u' = H.τC ι u :=
      congrArg (Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))) e2
    have e4 : x * ((u : H.Ga), 1) * ((g, 1) : H.Ga × GV n H.Sl) =
        x * ((g, 1) : H.Ga × GV n H.Sl) * ((u' : H.Ga), 1) := by
      rw [mul_assoc, mul_assoc]
      refine congrArg (x * ·) (Prod.ext ?_ rfl)
      change (u : H.Ga) * g = g * (u' : H.Ga)
      rw [e1, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [e4, ← e3]
    exact h

end Gen

section U

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ}

private theorem ze_infRep (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {k : UA L n} (hk : k ∈ finU (E := L) (n := n)) :
    infRep (V := V) ι lam k = 1 := by
  have h1 : ∀ τ : L →+* ℂ, cEmb τ k = 1 := fun τ => by
    change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]
  change PiTensorProduct.mapMonoidHom (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) =>
    GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) k)) = 1
  simp only [h1, map_one]
  exact map_one _

variable {V : s.Lev} {ι : Qbar l ≃+* ℂ} {lam : Wt L l n} {d : ℕ}
  {e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)}
  {ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ}

private theorem ze_form (hn : 1 ≤ n) (Q : QData V) (c : Coef l) {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (hξ : IsBasis ι e ξ) {k : UA L n} (hk : k ∈ finU (E := L) (n := n)) (F : Ga l L n × GL' n V → Fin d → ℂ)
    (ℓ : Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))) :
    toForm ι e (fun g => F (g * ((away l L n).rangeRestrict k, fun v : V.frame.Vl => cLoc (s.w v.1) k))) ℓ =
      RU L n k (toForm ι e F ℓ) := by
  have h := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).2.2.1 F ℓ k
  rw [ze_infRep V ι lam ((finU (E := L) (n := n)).inv_mem hk)] at h
  exact h.symm

private theorem ze_tr (hn : 1 ≤ n) (Q : QData V) (c : Coef l) {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (hξ : IsBasis ι e ξ) {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ) (g : Ga l L n) (hg : Norm (hset Q τ₀) g)
    (F : Fin m → (hset Q τ₀).X.Fn ℂ d) (hF : F ∈ YOf Q ι τ₀ e ξ σ) : trF (hset Q τ₀) d g F ∈ YOf Q ι τ₀ e ξ σ := by
  obtain ⟨hb, hw⟩ := (partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  refine (partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ _).2 ⟨ze_big (hset Q τ₀) ι ξ g hg F hb, fun i ℓ => ?_⟩
  obtain ⟨k, hk⟩ := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).2.2.2.1
    ((g, 1) : Ga l L n × GL' n V)
  have hk' : ((g, 1) : Ga l L n × GL' n V) =
      ((away l L n).rangeRestrict k.1, fun v : V.frame.Vl => cLoc (s.w v.1) k.1) := hk.symm
  change toForm ι e (fun x => F i (x * ((g, 1) : Ga l L n × GL' n V))) ℓ ∈ σ
  rw [hk', ze_form hn Q c τ₀ hξ k.2 (F i) ℓ]
  exact hσ.stable _ _ (hw i ℓ)

end U

section GenE

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) {d : ℕ}

private theorem ze_H {J : Type} [Fintype J] (Y : J → Submodule ℂ (Fin H.m → H.X.Fn ℂ d)) (hY : iSupIndep Y)
    (Z : Submodule ℂ (Fin H.m → H.X.Fn ℂ d)) (hf : FiniteDimensional ℂ Z)
    (hZ : Module.finrank ℂ Z = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z)) {G : Type} [Group G] (β : G →* H.Ga) (a : G →₀ ℤ) (N : ℕ)
    (hP : ∀ i, ∀ g ∈ a.support, ∀ y ∈ Y i, trF H d (β g) y ∈ Y i) :
    Module.finrank ℂ ↥(Z ⊓ ePart ((trF H d).comp β) a N) =
      ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z ⊓ ePart ((trF H d).comp β) a N) :=
  ze_main Y hY Z hZ _ fun i => ze_opE ((trF H d).comp β) a (Y i) (hP i) N

end GenE

theorem UpperTheory.V.Z.Desc.V0.zDecE :
    UpperTheory.V.Z.J.D.ZEq → NormS → ZDecE := by
  intro hE hN l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ A _ _ _ θ x c0 sp hw hs K ev hev J _ σ hσ hind hdec a N ha
  have hZ := UpperTheory.V.Z.J.D.zDec hE l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ hξ A θ x c0 sp hw hs K ev hev J σ hσ hind hdec
  haveI : FiniteDimensional ℂ ↥(zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev) := by
    haveI := hs.fin K c0 le_rfl
    exact Submodule.finiteDimensional_of_le (inf_le_left.trans (iSup_le fun _ => inf_le_left))
  exact ze_H (hset Q τ₀) _ hind _ inferInstance hZ (sec0 n s) a N fun i g hg y hy =>
    ze_tr hn Q c τ₀ hξ (hσ i) _ ((hN l L Ω s n hn V hV Q c m τ₀).norm g (ha g hg)) y hy
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.InvBox
noncomputable section

open UpperTheory.V.Hi UpperTheory.V.Z.J.D
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.Desc.V0

section Lin

variable {W Z : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]

private def sl (l : Z →ₗ[ℂ] ℂ) : W ⊗[ℂ] Z →ₗ[ℂ] W :=
  (TensorProduct.rid ℂ W).toLinearMap ∘ₗ LinearMap.lTensor W l

private def sr (l : W →ₗ[ℂ] ℂ) : W ⊗[ℂ] Z →ₗ[ℂ] Z :=
  (TensorProduct.lid ℂ Z).toLinearMap ∘ₗ LinearMap.rTensor Z l

private theorem sl_tmul (l : Z →ₗ[ℂ] ℂ) (w : W) (z : Z) : sl l (w ⊗ₜ[ℂ] z) = l z • w := by
  simp [sl]

private theorem sr_tmul (l : W →ₗ[ℂ] ℂ) (w : W) (z : Z) : sr l (w ⊗ₜ[ℂ] z) = l w • z := by
  simp [sr]

end Lin

section Box

variable {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

end Box

private theorem sl_rTensor_apply {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (l : B →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] A) (x : A ⊗[ℂ] B) : sl l (LinearMap.rTensor B T x) = T (sl l x) := by
  induction x using TensorProduct.inductionOn with
  | tmul u v => rw [LinearMap.rTensor_tmul, sl_tmul, sl_tmul, map_smul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem sr_lTensor_apply {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (l : A →ₗ[ℂ] ℂ) (T : B →ₗ[ℂ] B) (x : A ⊗[ℂ] B) : sr l (LinearMap.lTensor A T x) = T (sr l x) := by
  induction x using TensorProduct.inductionOn with
  | tmul u v => rw [LinearMap.lTensor_tmul, sr_tmul, sr_tmul, map_smul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem mem_range_rTensor_subtype_of_forall_sl_coord_mem {A B ι : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (𝒞 : Module.Basis ι ℂ B) (U : Submodule ℂ A) (x : A ⊗[ℂ] B) (h : ∀ i, sl (𝒞.coord i) x ∈ U) :
    x ∈ LinearMap.range (LinearMap.rTensor B U.subtype) := by
  classical
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right 𝒞 x
  have hc : ∀ i, c i ∈ U := by
    intro i
    have e1 : (TensorProduct.equivFinsuppOfBasisRight 𝒞) (c.sum fun i m => m ⊗ₜ[ℂ] 𝒞 i) = c := by
      rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.apply_symm_apply]
    have e2 := TensorProduct.equivFinsuppOfBasisRight_apply 𝒞 (c.sum fun i m => m ⊗ₜ[ℂ] 𝒞 i) i
    rw [e1] at e2
    rw [e2]
    exact h i
  rw [Finsupp.sum]
  refine Submodule.sum_mem _ fun i _ => ⟨⟨c i, hc i⟩ ⊗ₜ 𝒞 i, ?_⟩
  rw [LinearMap.rTensor_tmul, Submodule.subtype_apply]

private theorem memL_lemma_4 {A B ι : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (ℬ : Module.Basis ι ℂ A) (V : Submodule ℂ B) (x : A ⊗[ℂ] B) (h : ∀ i, sr (ℬ.coord i) x ∈ V) :
    x ∈ LinearMap.range (LinearMap.lTensor A V.subtype) := by
  classical
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left ℬ x
  have hc : ∀ i, c i ∈ V := by
    intro i
    have e1 : (TensorProduct.equivFinsuppOfBasisLeft ℬ) (c.sum fun i n => ℬ i ⊗ₜ[ℂ] n) = c := by
      rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.apply_symm_apply]
    have e2 := TensorProduct.equivFinsuppOfBasisLeft_apply ℬ (c.sum fun i n => ℬ i ⊗ₜ[ℂ] n) i
    rw [e1] at e2
    rw [e2]
    exact h i
  rw [Finsupp.sum]
  refine Submodule.sum_mem _ fun i _ => ⟨ℬ i ⊗ₜ ⟨c i, hc i⟩, ?_⟩
  rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]

private theorem box_inl_apply_eq_rTensor {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (κ : Representation ℂ H W') (g : G)
    (y : W ⊗[ℂ] W') : box ρ κ (g, 1) y = LinearMap.rTensor W' (ρ g) y := by
  simp only [box, Representation.tprod_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, map_one]
  rfl

private theorem box_inr_apply_eq_lTensor {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (κ : Representation ℂ H W') (h : H)
    (y : W ⊗[ℂ] W') : box ρ κ (1, h) y = LinearMap.lTensor W (κ h) y := by
  simp only [box, Representation.tprod_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, map_one]
  rfl

private theorem opE_box_comp_inr_tmul {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (κ : Representation ℂ H W') (a : H →₀ ℤ)
    (w : W) (y : W') : opE ((box ρ κ).comp (MonoidHom.inr G H)) a (w ⊗ₜ y) = w ⊗ₜ opE κ a y := by
  simp only [opE, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, MonoidHom.comp_apply,
    MonoidHom.inr_apply, box, Representation.tprod_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, map_one,
    TensorProduct.map_tmul, Module.End.one_apply, TensorProduct.tmul_sum, TensorProduct.tmul_smul]

private theorem mem_box_inr_eigenspace_iff_lTensor_opE_sub_eq_zero {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (κ : Representation ℂ H W') (a : H →₀ ℤ)
    (N : ℕ) (y : W ⊗[ℂ] W') :
    y ∈ ePart ((box ρ κ).comp (MonoidHom.inr G H)) a N ↔ LinearMap.lTensor W (opE κ a - (N : Module.End ℂ W')) y = 0 := by
  have e : opE ((box ρ κ).comp (MonoidHom.inr G H)) a - (N : Module.End ℂ (W ⊗[ℂ] W')) =
      LinearMap.lTensor W (opE κ a - (N : Module.End ℂ W')) := by
    apply TensorProduct.ext'
    intro w v
    simp [opE_box_comp_inr_tmul, TensorProduct.tmul_sub, Module.End.natCast_apply, TensorProduct.tmul_smul]
  unfold ePart
  rw [LinearMap.mem_ker, e]

private theorem mem_invT_iff_sum_smul_inl_eq_and_inr_fixed {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] {m : ℕ}
    (K₁ : Subgroup G) (K₂ : Subgroup H) (τ₀ : K₁ →* GL (Fin m) ℂ) (ρ : Representation ℂ (G × H) W)
    (F : Fin m → W) :
    F ∈ invT K₁ K₂ τ₀ ρ ↔ (∀ (k : K₁) (i : Fin m), ∑ j, (τ₀ k : Matrix (Fin m) (Fin m) ℂ) i j • ρ (↑k, 1) (F j) = F i) ∧
      ∀ k ∈ K₂, ∀ i, ρ (1, k) (F i) = F i := Iff.rfl

set_option maxHeartbeats 800000 in
theorem invBox : InvBox := by
  intro G H W W' _ _ _ _ _ _ ρ κ m K₁ K₂ τ₀ a N
  classical
  let Ψ := TensorProduct.piLeft ℂ W' (fun _ : Fin m => W)
  let T : K₁ → Module.End ℂ (Fin m → W) := fun k =>
    LinearMap.pi fun i => ∑ j, (τ₀ k : Matrix (Fin m) (Fin m) ℂ) i j • (ρ k ∘ₗ LinearMap.proj j)
  have hT : ∀ k (F : Fin m → W) i, T k F i = ∑ j, (τ₀ k : Matrix (Fin m) (Fin m) ℂ) i j • ρ k (F j) := by
    intro k F i
    simp only [T, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply]
  haveI indexFFirst : Module.Free ℂ (Fin m → W) := Module.Free.of_divisionRing ℂ _
  haveI indexFSecond : Module.Free ℂ ↥(fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W') := Module.Free.of_divisionRing ℂ _
  haveI indexFThird : Module.Free ℂ ↥(inv1 K₁ τ₀ ρ) := Module.Free.of_divisionRing ℂ _
  haveI iL1 : Module.Flat ℂ (Fin m → W) := Module.Flat.of_free
  haveI iL2 : Module.Flat ℂ ↥(fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W') := Module.Flat.of_free
  have hV1 : ∀ F : Fin m → W, F ∈ inv1 K₁ τ₀ ρ ↔ ∀ k, T k F = F := by
    intro F
    rw [show inv1 K₁ τ₀ ρ = invT K₁ ⊥ τ₀ (ρ.comp (MonoidHom.fst G Unit)) from rfl, mem_invT_iff_sum_smul_inl_eq_and_inr_fixed]
    simp only [MonoidHom.comp_apply, MonoidHom.coe_fst, map_one, Module.End.one_apply, implies_true, and_true,
      funext_iff, hT]
  have hV2 : ∀ w : W', w ∈ fixd κ K₂ ⊓ ePart κ a N ↔ (∀ l ∈ K₂, κ l w = w) ∧ (opE κ a - (N : Module.End ℂ W')) w = 0 := by
    intro w
    rw [Submodule.mem_inf]
    exact Iff.rfl
  have hΨt : ∀ (F : Fin m → W) (w : W') i, Ψ (F ⊗ₜ w) i = F i ⊗ₜ w := by
    intro F w i
    simp [Ψ]
  have hΨl : ∀ (g : W' →ₗ[ℂ] W') x i, Ψ (LinearMap.lTensor _ g x) i = LinearMap.lTensor W g (Ψ x i) := by
    intro g x i
    induction x using TensorProduct.inductionOn with
    | tmul F w => rw [LinearMap.lTensor_tmul, hΨt, hΨt, LinearMap.lTensor_tmul]
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]
  have hΨr : ∀ k x i, Ψ (LinearMap.rTensor W' (T k) x) i =
      ∑ j, (τ₀ k : Matrix (Fin m) (Fin m) ℂ) i j • LinearMap.rTensor W' (ρ k) (Ψ x j) := by
    intro k x i
    induction x using TensorProduct.inductionOn with
    | tmul F w =>
      simp only [LinearMap.rTensor_tmul, hΨt, hT, TensorProduct.sum_tmul, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy, smul_add, Finset.sum_add_distrib]
  let ι : ↥(inv1 K₁ τ₀ ρ) ⊗[ℂ] ↥(fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W') →ₗ[ℂ] (Fin m → W ⊗[ℂ] W') :=
    Ψ.toLinearMap ∘ₗ TensorProduct.map (inv1 K₁ τ₀ ρ).subtype (fixd κ K₂ ⊓ ePart κ a N).subtype
  have hinj : Function.Injective ι :=
    Ψ.injective.comp (TensorProduct.map_injective_of_flat_flat (inv1 K₁ τ₀ ρ).subtype
      (fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W').subtype (Submodule.injective_subtype _) (Submodule.injective_subtype _))
  have hrange : invE K₁ K₂ τ₀ (box ρ κ) a N = LinearMap.range ι := by
    apply le_antisymm
    · intro F hF
      obtain ⟨x, rfl⟩ := Ψ.surjective F
      unfold invE at hF
      rw [Submodule.mem_inf, mem_invT_iff_sum_smul_inl_eq_and_inr_fixed, Submodule.mem_pi] at hF
      obtain ⟨⟨h1, h2⟩, h3⟩ := hF
      have hl : ∀ l ∈ K₂, LinearMap.lTensor _ (κ l) x = x := by
        intro l hl
        apply Ψ.injective
        funext i
        rw [hΨl, ← box_inr_apply_eq_lTensor ρ κ l, h2 l hl i]
      have he : LinearMap.lTensor _ (opE κ a - (N : Module.End ℂ W')) x = 0 := by
        apply Ψ.injective
        funext i
        rw [hΨl, map_zero, Pi.zero_apply, ← mem_box_inr_eigenspace_iff_lTensor_opE_sub_eq_zero ρ κ a N]
        exact h3 i (Set.mem_univ i)
      obtain ⟨y, hy⟩ := memL_lemma_4 (Module.Basis.ofVectorSpace ℂ (Fin m → W)) (fixd κ K₂ ⊓ ePart κ a N) x (fun i => by
        rw [hV2]
        refine ⟨fun l hl' => ?_, ?_⟩
        · rw [← sr_lTensor_apply, hl l hl']
        · rw [← sr_lTensor_apply, he, map_zero])
      have hk : ∀ k, LinearMap.rTensor _ (T k) y = y := by
        intro k
        apply Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype (fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W'))
        have e := LinearMap.congr_fun ((LinearMap.lTensor_comp_rTensor (f := T k) (g := (fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W').subtype)).trans
          (LinearMap.rTensor_comp_lTensor (f := T k) (g := (fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W').subtype)).symm) y
        simp only [LinearMap.comp_apply] at e
        rw [e, hy]
        apply Ψ.injective
        funext i
        rw [hΨr]
        refine (Finset.sum_congr rfl fun j _ => ?_).trans (h1 k i)
        rw [box_inl_apply_eq_rTensor]
      obtain ⟨z, hz⟩ := mem_range_rTensor_subtype_of_forall_sl_coord_mem (Module.Basis.ofVectorSpace ℂ ↥(fixd κ K₂ ⊓ ePart κ a N : Submodule ℂ W')) (inv1 K₁ τ₀ ρ) y (fun i => by
        rw [hV1]
        intro k
        rw [← sl_rTensor_apply, hk k])
      refine ⟨z, ?_⟩
      rw [← hy, ← hz]
      simp only [ι, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply]
    · rintro _ ⟨t, rfl⟩
      induction t using TensorProduct.inductionOn with
      | add s t hs ht => rw [map_add]; exact add_mem hs ht
      | tmul v w =>
        have hv := (hV1 v).1 v.2
        obtain ⟨hw1, hw2⟩ := (hV2 w).1 w.2
        have e : ι (v ⊗ₜ w) = fun i => (v : Fin m → W) i ⊗ₜ (w : W') := by
          funext i
          simp only [ι, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul, Submodule.subtype_apply, hΨt]
        rw [e]
        unfold invE
        rw [Submodule.mem_inf, mem_invT_iff_sum_smul_inl_eq_and_inr_fixed, Submodule.mem_pi]
        refine ⟨⟨fun k i => ?_, fun l hl i => ?_⟩, fun i _ => ?_⟩
        · simp only [box_inl_apply_eq_rTensor, LinearMap.rTensor_tmul]
          conv_rhs => rw [← hv k, hT, TensorProduct.sum_tmul]
          simp only [TensorProduct.smul_tmul']
        · rw [box_inr_apply_eq_lTensor, LinearMap.lTensor_tmul, hw1 l hl]
        · rw [mem_box_inr_eigenspace_iff_lTensor_opE_sub_eq_zero, LinearMap.lTensor_tmul, hw2, TensorProduct.tmul_zero]
  rw [hrange, rank_range_of_injective ι hinj, rank_tensorProduct']

end UpperTheory.V.Z.Desc.V0
end
end
