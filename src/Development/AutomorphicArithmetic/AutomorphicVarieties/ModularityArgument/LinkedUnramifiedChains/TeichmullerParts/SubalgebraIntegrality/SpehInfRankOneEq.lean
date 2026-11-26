module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteSumReduction
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvableCyclicSubextensionOverRat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.IrrComp

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.SpehInfRankOneEq
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af.Gu UpperTheory.V.Z.J.D GlobalTheory.DefiniteBC GlobalTheory.SmGL
open UpperTheory.V.Z.Mult (Cp At)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace SpehDualProof

open Matrix GlobalTheory.ContraPair

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

end SpehDualProof

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.BoxIsot
open UpperTheory.V.Z.J.D
open scoped TensorProduct

namespace UpperTheory.V.Z.J.D

private lemma box_tmul {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (τ : Representation ℂ H W')
    (a : G) (b : H) (w : W) (v : W') :
    box ρ τ (a, b) (w ⊗ₜ[ℂ] v) = ρ a w ⊗ₜ[ℂ] τ b v := by
  simp [box, Representation.tprod_apply]

private lemma isot_factor {G H W W' X Y : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [Nontrivial W] (ρ : Representation ℂ G W) (τ : Representation ℂ H W')
    (κ : Representation ℂ (G × H) X) (κ' : Representation ℂ H Y) (f : W ⊗[ℂ] Y ≃ₗ[ℂ] X)
    (hf : Intw (box ρ κ') κ f.toLinearMap) (h2 : Isot (κ.comp (MonoidHom.inr G H)) τ) :
    Isot κ' τ := by
  obtain ⟨w0, hw0⟩ := exists_ne (0 : W)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W, φ w0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff ℂ w0).1 hcon)
  let p : X →ₗ[ℂ] Y := (TensorProduct.lid ℂ Y).toLinearMap ∘ₗ
    (TensorProduct.map φ LinearMap.id) ∘ₗ f.symm.toLinearMap
  have hp1 : ∀ w y, p (f (w ⊗ₜ[ℂ] y)) = φ w • y := fun w y => by
    simp [p]
  have hp2 : ∀ (h : H) (x : X), p (κ (1, h) x) = κ' h (p x) := by
    intro h x
    obtain ⟨t, rfl⟩ := f.surjective x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul w y =>
      have := hf (1, h) (w ⊗ₜ[ℂ] y)
      simp only [LinearEquiv.coe_coe] at this
      rw [← this, box_tmul, hp1, hp1]
      simp
  unfold Isot
  set S : Submodule ℂ Y := ⨆ g : {g : W' →ₗ[ℂ] Y // Intw τ κ' g}, LinearMap.range g.1 with hS
  have hle : (⊤ : Submodule ℂ X) ≤ S.comap p := by
    refine le_trans h2 (iSup_le fun u => ?_)
    rintro _ ⟨a, rfl⟩
    have hu : Intw τ κ' (p ∘ₗ u.1) := fun h v => by
      have := u.2 h v
      simp only [LinearMap.comp_apply]
      rw [this]
      exact hp2 h (u.1 v)
    exact (le_iSup (fun g : {g : W' →ₗ[ℂ] Y // Intw τ κ' g} => LinearMap.range g.1) ⟨_, hu⟩)
      ⟨a, rfl⟩
  intro y _
  have hy : p (f (w0 ⊗ₜ[ℂ] ((φ w0)⁻¹ • y))) ∈ S := hle (Submodule.mem_top)
  rw [hp1, smul_smul, mul_inv_cancel₀ hφ, one_smul] at hy
  exact hy

private lemma isot_tensor {G H W W' X Y : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G W) (τ : Representation ℂ H W')
    (κ : Representation ℂ (G × H) X) (κ' : Representation ℂ H Y) (f : W ⊗[ℂ] Y ≃ₗ[ℂ] X)
    (hf : Intw (box ρ κ') κ f.toLinearMap) (h : Isot κ' τ) : Isot κ (box ρ τ) := by
  unfold Isot
  set T : Submodule ℂ X :=
    ⨆ F : {F : W ⊗[ℂ] W' →ₗ[ℂ] X // Intw (box ρ τ) κ F}, LinearMap.range F.1 with hT
  have hF : ∀ g : W' →ₗ[ℂ] Y, Intw τ κ' g →
      Intw (box ρ τ) κ (f.toLinearMap ∘ₗ TensorProduct.map LinearMap.id g) := by
    intro g hg ab t
    obtain ⟨a, b⟩ := ab
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [map_add (f := _), hs, ht]
    | tmul w v =>
      have := hf (a, b) (w ⊗ₜ[ℂ] g v)
      simp only [LinearEquiv.coe_coe] at this
      rw [box_tmul] at this
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearEquiv.coe_coe, box_tmul]
      rw [hg b v, this]
  have hw : ∀ (w : W) (y : Y), f (w ⊗ₜ[ℂ] y) ∈ T := by
    intro w y
    have hle : (⊤ : Submodule ℂ Y) ≤
        T.comap (f.toLinearMap ∘ₗ TensorProduct.mk ℂ W Y w) := by
      refine le_trans h (iSup_le fun g => ?_)
      rintro _ ⟨a, rfl⟩
      exact (le_iSup (fun F : {F : W ⊗[ℂ] W' →ₗ[ℂ] X // Intw (box ρ τ) κ F} =>
        LinearMap.range F.1) ⟨_, hF g.1 g.2⟩) ⟨w ⊗ₜ[ℂ] a, by simp⟩
    exact hle (Submodule.mem_top (x := y))
  intro x _
  obtain ⟨t, rfl⟩ := f.surjective x
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht =>
    rw [map_add (f := _)]
    exact T.add_mem (hs (Submodule.mem_top)) (ht (Submodule.mem_top))
  | tmul w y => exact hw w y

end UpperTheory.V.Z.J.D

theorem UpperTheory.V.Z.J.D.boxIsot :
    Step → BoxIsot := by
  intro hStep G H W W' _ _ _ _ _ _ ρ τ hρ _ X _ _ κ h1 h2
  obtain ⟨Y, _, _, κ', f, hf⟩ := hStep G H X W κ ρ hρ h1
  haveI : Nontrivial W := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    obtain ⟨s, t, hst⟩ := hρ.1.toNontrivial.exists_pair_ne
    exact hst (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  exact isot_tensor ρ τ κ κ' f hf (isot_factor ρ τ κ κ' f hf h2)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.IndepS
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StabilizerSubgroup
noncomputable def UpperTheory.Reformulated.B.StabilizerSubgroup.stabG :
    {G V : Type} →
      [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → V → Subgroup G :=
  fun {G _V} _ _ _ ρ v =>
    { carrier := {g : G | ρ g v = v}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ρ a v = v := ha
        have hb' : ρ b v = v := hb
        show ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := by
        show ρ 1 v = v
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {a} ha => by
        have ha' : ρ a v = v := ha
        show ρ a⁻¹ v = v
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = v := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply] }
end

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open GlobalTheory.BCT.GlobLev GlobalTheory.SplitPts GroundTheory.Automorphic

namespace UpperTheory.V.Z.J.D

private theorem exists_avg {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (R : Representation ℂ G V)
    (K H : Subgroup G) (hfin : Finite (K ⧸ H.subgroupOf K)) :
    ∃ A : V →ₗ[ℂ] V, (∀ v, (∀ k ∈ K, R k v = v) → A v = v) ∧
      (∀ v, (∀ h ∈ H, R h v = v) → ∀ k ∈ K, R k (A v) = A v) ∧
      ∀ M : Submodule ℂ V, (∀ x, ∀ v ∈ M, R x v ∈ M) → ∀ v ∈ M, A v ∈ M := by
  classical
  letI := Fintype.ofFinite (K ⧸ H.subgroupOf K)
  have hc : (Fintype.card (K ⧸ H.subgroupOf K) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨(Fintype.card (K ⧸ H.subgroupOf K) : ℂ)⁻¹ • ∑ q : K ⧸ H.subgroupOf K, R ((q.out : K) : G), ?_, ?_, ?_⟩
  · intro v hv
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl fun q _ => hv _ (q.out : K).2]
    simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc]
  · intro v hv k hk
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
    congr 1
    have key : ∀ q : K ⧸ H.subgroupOf K, R k (R ((q.out : K) : G) v) =
        R ((((⟨k, hk⟩ : K) • q).out : K) : G) v := fun q => by
      have e : (QuotientGroup.mk (((⟨k, hk⟩ : K) • q).out) : K ⧸ H.subgroupOf K) =
          QuotientGroup.mk ((⟨k, hk⟩ : K) * q.out) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have h1 := QuotientGroup.eq.1 e
      have h2 : ((((⟨k, hk⟩ : K) • q).out : K) : G)⁻¹ * (k * ((q.out : K) : G)) ∈ H := h1
      have h3 := hv _ h2
      have h4 : k * ((q.out : K) : G) = ((((⟨k, hk⟩ : K) • q).out : K) : G) *
          (((((⟨k, hk⟩ : K) • q).out : K) : G)⁻¹ * (k * ((q.out : K) : G))) := by group
      rw [← Module.End.mul_apply, ← map_mul, h4, map_mul, Module.End.mul_apply, h3]
    rw [Finset.sum_congr rfl fun q _ => key q]
    exact Equiv.sum_comp (MulAction.toPerm (⟨k, hk⟩ : K)) fun q : K ⧸ H.subgroupOf K => R ((q.out : K) : G) v
  · intro M hM v hv
    exact M.smul_mem _ (by
      simp only [LinearMap.sum_apply]
      exact M.sum_mem fun q _ => hM _ v hv)

private theorem is_compact_integral_level {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) :
    IsCompact (globLev S (KL n) : Set (finU (E := E) (n := n))) := by
  have hO : IsOpen (globLev S (KL n) : Set (finU (E := E) (n := n))) := by
    rw [globLev_KL_eq hS]
    exact (AdelicGLn.isOpen_integralFiniteGL E n).preimage continuous_finPart
  refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
    ((AdelicGLn.isCompact_integralFiniteGL E n).image continuous_finGL_ad))
    (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E n x, ?_, ?_⟩
  · rw [globLev_KL_eq hS] at hx
    exact hx
  · have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

private theorem finite_quot {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S : Set (Pl E)} (hS : IsSection S)
    {K' : ∀ w : Pl E, Subgroup (UL n w)} (hle : ∀ w, K' w ≤ KL n w) (U : Subgroup (finU (E := E) (n := n))) (hU : IsOpen (U : Set (finU (E := E) (n := n)))) :
    Finite (globLev S K' ⧸ U.subgroupOf (globLev S K')) := by
  have hK : globLev S K' ≤ globLev S (KL n) := fun k hk =>
    (mem_globLev S _ k).2 fun w hw => hle w ((mem_globLev S _ k).1 hk w hw)
  haveI : CompactSpace (globLev S (KL n)) := isCompact_iff_compactSpace.1 (is_compact_integral_level hS)
  have h0 : Finite (globLev S (KL n) ⧸ U.subgroupOf (globLev S (KL n))) :=
    Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  have h1 : U.relIndex (globLev S (KL n)) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : U.relIndex (globLev S K') ≠ 0 := mt (Subgroup.relIndex_eq_zero_of_le_right hK) h1
  haveI : (U.subgroupOf (globLev S K')).FiniteIndex := ⟨h2⟩
  exact Subgroup.finite_quotient_of_finiteIndex

private noncomputable def stabG {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (R : Representation ℂ G V) (v : V) : Subgroup G :=
  _root_.UpperTheory.Reformulated.B.StabilizerSubgroup.stabG R v

theorem indepS : IndepS := by
  intro E _ _ _ n S hS lam K' hK' J _ σ hd
  classical
  obtain ⟨h1, h2, -⟩ := hd
  have hst : ∀ j x, ∀ φ ∈ σ j, RU E n x φ ∈ σ j := fun j => (h1 j).1.stable
  intro i
  have hT : ∀ x, ∀ φ ∈ ⨆ (j) (_ : j ≠ i), σ j, RU E n x φ ∈ ⨆ (j) (_ : j ≠ i), σ j := by
    intro x φ hφ
    have hc : (⨆ (j) (_ : j ≠ i), σ j) ≤ (⨆ (j) (_ : j ≠ i), σ j).comap (RU E n x) :=
      iSup₂_le fun j hj y hy => Submodule.mem_comap.2 (le_iSup₂_of_le (f := fun j (_ : j ≠ i) => σ j) j hj le_rfl (hst j x y hy))
    exact hc hφ
  rcases (h1 i).1.irred (σ i ⊓ ⨆ (j) (_ : j ≠ i), σ j) inf_le_left
    (fun x φ hφ => ⟨hst i x φ hφ.1, hT x φ hφ.2⟩) with h0 | h0
  · exact disjoint_iff.2 h0
  exfalso
  obtain ⟨φ, hφ, hφ0⟩ := (Submodule.ne_bot_iff _).1 (h1 i).2.2
  have hφT : φ ∈ ⨆ (j) (_ : j ≠ i), σ j := (inf_eq_left.1 h0) hφ.1
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hφT
  have hfσ : ∀ j, f j ∈ σ j := fun j => by
    by_cases hj : j = i
    · have := hf j
      rw [iSup_neg (not_not.2 hj)] at this
      rw [(Submodule.mem_bot ℂ).1 this]
      exact Submodule.zero_mem _
    · have := hf j
      rwa [iSup_pos hj] at this
  have hfi : f i = 0 := by
    have := hf i
    rw [iSup_neg (not_not.2 rfl)] at this
    exact (Submodule.mem_bot ℂ).1 this
  have hsum' : ∑ j, f j = φ := by
    rw [← hsum]
    exact (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => Finsupp.notMem_support_iff.1 hj).symm
  have hopen : IsOpen ((⨅ j, stabG (RF E n) (f j) : Subgroup (finU (E := E) (n := n))) : Set (finU (E := E) (n := n))) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun j => ((h1 j).1.aut _ (hfσ j)).level
  obtain ⟨A, hA1, hA2, hA3⟩ := exists_avg (RF E n) (globLev S K') (⨅ j, stabG (RF E n) (f j))
    (finite_quot hS (fun w => (hK'.1 w).2.1) _ hopen)
  have hφfix : ∀ k ∈ globLev S K', RF E n k φ = φ := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hφ.2 k hk
  have hφA : A φ = φ := hA1 φ hφfix
  have ha : ∀ j, A (f j) ∈ σ j ⊓ fixed (RF E n) (globLev S K') := fun j =>
    ⟨hA3 (σ j) (fun x v hv => hst j _ v hv) _ (hfσ j),
      GlobalTheory.LGrp.mem_fixed.2 fun k hk => hA2 _ (fun h hh => (Subgroup.mem_iInf.1 hh j)) k hk⟩
  have hmem : φ ∈ ⨆ (j) (_ : j ≠ i), σ j ⊓ fixed (RF E n) (globLev S K') := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hφA, ← hsum', map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j = i
    · rw [hj, hfi, map_zero]
      exact Submodule.zero_mem _
    · exact le_iSup₂_of_le (f := fun j (_ : j ≠ i) => σ j ⊓ fixed (RF E n) (globLev S K')) j hj le_rfl (ha j)
  exact hφ0 ((Submodule.disjoint_def.1 (h2 i)) φ hφ hmem)

end UpperTheory.V.Z.J.D
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.PiRepTprod
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrrIff
theorem UpperTheory.Reformulated.B.Ra6.irr_iff :
    ∀ {G W : Type} [inst : Group G] [inst_1 : AddCommGroup W]
    [inst_2 : _root_.Module ℂ W] (ρ : Representation ℂ G W),
    ρ.IsIrreducible ↔
      Nontrivial W ∧
        ∀ (N : Submodule ℂ W), (∀ (g : G), ∀ v ∈ N, ((ρ : G → W →ₗ[ℂ] W) g : W → W) v ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro G W _ _ _ ρ
  constructor
  · intro h
    have h' : IsSimpleOrder (Subrepresentation ρ) := h
    refine ⟨?_, fun N hN => ?_⟩
    · have hne : (⊥ : Submodule ℂ W) ≠ ⊤ := fun e =>
        (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective e)
      exact (Submodule.nontrivial_iff ℂ).mp ⟨⊥, ⊤, hne⟩
    · rcases h'.eq_bot_or_eq_top ⟨N, fun g v hv => hN g v hv⟩ with e | e
      · exact Or.inl (congrArg Subrepresentation.toSubmodule e)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule e)
  · rintro ⟨hW, h⟩
    have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun e =>
      (bot_ne_top (α := Submodule ℂ W)) (congrArg Subrepresentation.toSubmodule e)
    have h' : IsSimpleOrder (Subrepresentation ρ) :=
      { exists_pair_ne := ⟨⊥, ⊤, hne⟩
        eq_bot_or_eq_top := fun σ =>
          (h σ.toSubmodule fun g v hv => σ.apply_mem_toSubmodule g hv).imp
            (fun e => Subrepresentation.toSubmodule_injective e)
            (fun e => Subrepresentation.toSubmodule_injective e) }
    exact h'
end

open UpperTheory.V.Z.J.D
open scoped TensorProduct

section Transfer

variable {G G' W W' : Type} [Group G] [Group G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private lemma irr_iff (ρ : Representation ℂ G W) :
    ρ.IsIrreducible ↔ Nontrivial W ∧
      ∀ N : Submodule ℂ W, (∀ g, ∀ v ∈ N, ρ g v ∈ N) → N = ⊥ ∨ N = ⊤ :=
  _root_.UpperTheory.Reformulated.B.Ra6.irr_iff ρ

private lemma transfer (ρ : Representation ℂ G W) (ρ' : Representation ℂ G' W') (φ : G' → G)
    (hφ : Function.Surjective φ) (e : W' ≃ₗ[ℂ] W)
    (h : ∀ g x, e (ρ' g x) = ρ (φ g) (e x)) (hρ : AbsIrr ρ) : AbsIrr ρ' := by
  obtain ⟨h1, h2⟩ := hρ
  obtain ⟨hW, hN⟩ := (irr_iff ρ).1 h1
  refine ⟨(irr_iff ρ').2 ⟨e.toEquiv.nontrivial, fun N hN' => ?_⟩, fun f hf => ?_⟩
  · have hinv : ∀ g, ∀ v ∈ N.map e.toLinearMap, ρ g v ∈ N.map e.toLinearMap := by
      rintro g _ ⟨x, hx, rfl⟩
      obtain ⟨g', rfl⟩ := hφ g
      exact ⟨ρ' g' x, hN' g' x hx, h g' x⟩
    rcases hN _ hinv with h3 | h3
    · left
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hm : e.toLinearMap x ∈ N.map e.toLinearMap := Submodule.mem_map_of_mem hx
      rw [h3, Submodule.mem_bot] at hm
      exact e.map_eq_zero_iff.1 hm
    · right
      rw [Submodule.eq_top_iff']
      intro x
      have hm : e.toLinearMap x ∈ N.map e.toLinearMap := by rw [h3]; exact Submodule.mem_top
      obtain ⟨y, hy, hyx⟩ := hm
      rwa [← e.injective hyx]
  · have hs : ∀ g' v, e.symm (ρ (φ g') v) = ρ' g' (e.symm v) := fun g' v => by
      rw [LinearEquiv.symm_apply_eq, h g' (e.symm v), LinearEquiv.apply_symm_apply]
    have hF : Intw ρ ρ (e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap) := by
      intro g v
      obtain ⟨g', rfl⟩ := hφ g
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hs, hf, h]
    obtain ⟨a, ha⟩ := h2 _ hF
    refine ⟨a, LinearMap.ext fun x => e.injective ?_⟩
    have := LinearMap.congr_fun ha (e x)
    simpa using this

private lemma pt_eq {ι Z : Type} {s : ι → Type} [∀ i, AddCommGroup (s i)] [∀ i, Module ℂ (s i)]
    [AddCommGroup Z] [Module ℂ Z] (A B : (⨂[ℂ] i, s i) →ₗ[ℂ] Z)
    (h : ∀ m, A (PiTensorProduct.tprod ℂ m) = B (PiTensorProduct.tprod ℂ m)) (x : ⨂[ℂ] i, s i) :
    A x = B x :=
  LinearMap.congr_fun (PiTensorProduct.ext (MultilinearMap.ext h)) x

end Transfer

private lemma piRep_tprod {I : Type} {Gi Wi : I → Type} [∀ i, Group (Gi i)]
    [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)]
    (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (g : ∀ i, Gi i) (m : ∀ i, Wi i) :
    piRep τ g (PiTensorProduct.tprod ℂ m) = PiTensorProduct.tprod ℂ fun i => τ i (g i) (m i) :=
  PiTensorProduct.map_tprod _ _

private def Pp (I : Type) : Prop :=
  ∀ (Gi Wi : I → Type) [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)]
    (τ : ∀ i, Representation ℂ (Gi i) (Wi i)), (∀ i, AbsIrr (τ i)) → AbsIrr (piRep τ)

private lemma Pp_equiv {α β : Type} (f : β ≃ α) (h : Pp α) : Pp β := by
  intro Gi Wi _ _ _ τ hτ
  refine transfer (piRep fun a => τ (f.symm a)) (piRep τ) (Equiv.piCongrLeft' Gi f)
    (Equiv.surjective _) (PiTensorProduct.reindex ℂ Wi f) (fun g x => ?_)
    (h (fun a => Gi (f.symm a)) (fun a => Wi (f.symm a)) (fun a => τ (f.symm a)) fun a => hτ _)
  refine pt_eq ((PiTensorProduct.reindex ℂ Wi f).toLinearMap ∘ₗ piRep τ g)
    ((piRep (fun a => τ (f.symm a)) (Equiv.piCongrLeft' Gi f g)) ∘ₗ
      (PiTensorProduct.reindex ℂ Wi f).toLinearMap) (fun m => ?_) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, piRep_tprod, PiTensorProduct.reindex_tprod]
  rfl

private lemma absIrr_triv : AbsIrr (Representation.trivial ℂ Unit ℂ) := by
  refine ⟨(irr_iff _).2 ⟨inferInstance, fun N _ => eq_bot_or_eq_top N⟩, fun f _ => ⟨f 1, ?_⟩⟩
  refine LinearMap.ext_ring ?_
  simp

private lemma Pp_empty : Pp PEmpty := by
  intro Gi Wi _ _ _ τ _
  refine transfer (Representation.trivial ℂ Unit ℂ) (piRep τ) (fun _ => ()) (fun _ => ⟨1, rfl⟩)
    (PiTensorProduct.isEmptyEquiv PEmpty) (fun g x => ?_) absIrr_triv
  refine pt_eq ((PiTensorProduct.isEmptyEquiv PEmpty).toLinearMap ∘ₗ piRep τ g)
    (Representation.trivial ℂ Unit ℂ () ∘ₗ (PiTensorProduct.isEmptyEquiv PEmpty).toLinearMap)
    (fun m => ?_) x
  simp [piRep_tprod, PiTensorProduct.isEmptyEquiv_apply_tprod]

private lemma Pp_unit : Pp PUnit := by
  intro Gi Wi _ _ _ τ hτ
  refine transfer (τ PUnit.unit) (piRep τ) (fun g => g PUnit.unit) (fun h => ⟨fun _ => h, rfl⟩)
    (PiTensorProduct.subsingletonEquiv PUnit.unit) (fun g x => ?_) (hτ _)
  refine pt_eq ((PiTensorProduct.subsingletonEquiv PUnit.unit).toLinearMap ∘ₗ piRep τ g)
    (τ PUnit.unit (g PUnit.unit) ∘ₗ (PiTensorProduct.subsingletonEquiv PUnit.unit).toLinearMap)
    (fun m => ?_) x
  simp [piRep_tprod, PiTensorProduct.subsingletonEquiv_apply_tprod]

private lemma Pp_sum (hB : BoxIrr) {α β : Type} (ha : Pp α) (hb : Pp β) : Pp (α ⊕ β) := by
  intro Gi Wi _ _ _ τ hτ
  refine transfer (box (piRep fun a => τ (.inl a)) (piRep fun b => τ (.inr b))) (piRep τ)
    (fun g => (fun a => g (.inl a), fun b => g (.inr b)))
    (fun p => ⟨fun s => Sum.rec (motive := Gi) p.1 p.2 s, rfl⟩)
    (PiTensorProduct.tmulEquivDep ℂ Wi).symm (fun g x => ?_)
    (hB _ _ _ _ _ _ (ha _ _ _ fun a => hτ _) (hb _ _ _ fun b => hτ _))
  refine pt_eq ((PiTensorProduct.tmulEquivDep ℂ Wi).symm.toLinearMap ∘ₗ piRep τ g)
    ((box (piRep fun a => τ (.inl a)) (piRep fun b => τ (.inr b))
        (fun a => g (.inl a), fun b => g (.inr b))) ∘ₗ
      (PiTensorProduct.tmulEquivDep ℂ Wi).symm.toLinearMap) (fun m => ?_) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, piRep_tprod,
    PiTensorProduct.tmulEquivDep_symm_apply]
  simp only [box, Representation.tprod_apply, MonoidHom.comp_apply, TensorProduct.map_tmul]
  simp [piRep_tprod]

theorem UpperTheory.V.Z.J.D.piIrr :
    BoxIrr → PiIrr := by
  intro hB I _ _ Gi Wi _ _ _ τ hτ
  have key : ∀ (α : Type) [Fintype α], Pp α := by
    refine Fintype.induction_empty_option (P := fun α _ => Pp α) ?_ Pp_empty ?_
    · intro α β _ e h
      exact Pp_equiv e.symm h
    · intro α _ h
      exact Pp_equiv (Equiv.optionEquivSumPUnit α) (Pp_sum hB h Pp_unit)
  exact key I Gi Wi τ hτ
end
