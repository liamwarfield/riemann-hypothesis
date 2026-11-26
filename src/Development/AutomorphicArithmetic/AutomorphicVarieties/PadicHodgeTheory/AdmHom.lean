module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmHom
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

noncomputable section

namespace UpperTheory.V.Loc

section Generic

variable {G : Type} [Group G] {Q V V' W : Type} [Field Q] [AddCommGroup V] [Module Q V] [AddCommGroup V']
  [Module Q V'] [AddCommGroup W] [Module Q W] [FiniteDimensional Q V]

private theorem exists_inj_dual_tprod (ρ : Representation Q G V) (ρ' : Representation Q G V')
    (π : Representation Q G W) (b : W →ₗ[Q] V →ₗ[Q] V') (hb : ∀ g w x, b (π g w) (ρ g x) = ρ' g (b w x))
    (hi : Function.Injective b) :
    ∃ f : W →ₗ[Q] Module.Dual Q V ⊗[Q] V', (∀ g w, f (π g w) = (ρ.dual.tprod ρ') g (f w)) ∧
      Function.Injective f := by
  let e := dualTensorHomEquiv Q V V'
  refine ⟨e.symm.toLinearMap ∘ₗ b, fun g w => ?_, e.symm.injective.comp hi⟩
  have key : ∀ (t : Module.Dual Q V ⊗[Q] V') (x : V),
      e ((ρ.dual.tprod ρ') g t) (ρ g x) = ρ' g (e t x) := by
    intro t x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [map_add (f := _), LinearMap.add_apply, hs, ht]
    | tmul f y => simp [e, Module.Dual.transpose_apply]
  apply e.injective
  ext x
  obtain ⟨x, rfl⟩ : ∃ y, ρ g y = x := ⟨ρ g⁻¹ x, by simp⟩
  rw [key]
  simp [hb]

end Generic

section Transport

variable {l : ℕ} [Fact l.Prime] {G H A V : Type} [Group G] [Group H] [CommRing A] [Algebra ℚ_[l] A]
  [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]

private theorem admissible_transport_equiv (ψ : H →* GQ l) (e : G ≃* H) (ρ : Representation A G V) :
    (IsCr (ψ.comp e.toMonoidHom) ρ ↔ IsCr ψ (ρ.comp e.symm.toMonoidHom : Representation A H V)) ∧
    (IsDr (ψ.comp e.toMonoidHom) ρ ↔ IsDr ψ (ρ.comp e.symm.toMonoidHom : Representation A H V)) := by
  have hr : (ψ.comp e.toMonoidHom).range = ψ.range := by
    ext x
    exact ⟨fun ⟨g, hg⟩ => ⟨e g, hg⟩, fun ⟨h, hh⟩ => ⟨e.symm h, by simpa using hh⟩⟩
  have h1 : Dcr (ψ.comp e.toMonoidHom) (resCoef ℚ_[l] ρ) =
      Dcr ψ (resCoef ℚ_[l] (ρ.comp e.symm.toMonoidHom : Representation A H V)) := by
    unfold Dcr
    refine e.toEquiv.iInf_congr fun g => ?_
    simp [actC, resCoef]
  have h2 : Ddr (ψ.comp e.toMonoidHom) (resCoef ℚ_[l] ρ) =
      Ddr ψ (resCoef ℚ_[l] (ρ.comp e.symm.toMonoidHom : Representation A H V)) := by
    unfold Ddr
    refine e.toEquiv.iInf_congr fun g => ?_
    simp [actD, resCoef]
  unfold IsCr IsDr
  rw [hr, h1, h2]
  exact ⟨Iff.rfl, Iff.rfl⟩

end Transport

section Field

variable {l : ℕ} [Fact l.Prime] (K : FinExt l) {V V' W : Type} [AddCommGroup V] [Module ℚ_[l] V]
  [AddCommGroup V'] [Module ℚ_[l] V'] [AddCommGroup W] [Module ℚ_[l] W] [FiniteDimensional ℚ_[l] V]
  [FiniteDimensional ℚ_[l] V'] [FiniteDimensional ℚ_[l] W]
  (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V')
  (π : Representation ℚ_[l] ↥(GK K) W) (f : W →ₗ[ℚ_[l]] Module.Dual ℚ_[l] V ⊗[ℚ_[l]] V')
  (hf : ∀ g w, f (π g w) = (ρ.dual.tprod ρ') g (f w)) (hi : Function.Injective f)
include hf hi

private theorem crys_hom (h : IsCrys ((PP l).PD K) ρ) (h' : IsCrys ((PP l).PD K) ρ') :
    IsCrys ((PP l).PD K) π := by
  obtain ⟨T⟩ := tiedP l
  obtain ⟨C, hfit⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l _ _ T
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  have h1 := GlobalTheory.RegularRing.fracInv hfit (GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C) K
  have h2 := GlobalTheory.RegularRing.lineUnit hfit (GlobalTheory.T.bcris_regular_of_tensorInj l C (GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C)) K
  exact GlobalTheory.RegularRing.subCrys _ ℚ_[l] h1 _ _ _ π f hf hi
    (GlobalTheory.RegularRing.tensorCrys _ ℚ_[l] h1 h2 _ _ _ _
      (GlobalTheory.RegularRing.dualCrys _ ℚ_[l] h1 h2 _ ρ h) h')

private theorem dR_hom (h : IsDR ((PP l).PD K) ρ) (h' : IsDR ((PP l).PD K) ρ') :
    IsDR ((PP l).PD K) π := by
  obtain ⟨T⟩ := tiedP l
  have := K.2
  have hF := GlobalTheory.DRFil.isField_dR T
  have s : GlobalTheory.DRFil.Spans ((PP l).PD K) ρ := GlobalTheory.Per.DeRhamSpan.span_of_isField _ ρ hF h
  have s' : GlobalTheory.DRFil.Spans ((PP l).PD K) ρ' := GlobalTheory.Per.DeRhamSpan.span_of_isField _ ρ' hF h'
  have sd : GlobalTheory.DRFil.Spans ((PP l).PD K) ρ.dual :=
    GlobalTheory.DRFil.spans_dual_of_spans _ ρ ρ.dual (Module.Dual.eval ℚ_[l] V) hF
      (fun g x y => by simp [Module.Dual.transpose_apply]) Function.bijective_id s
  have st : GlobalTheory.DRFil.Spans ((PP l).PD K) (ρ.dual.tprod ρ') :=
    GlobalTheory.DRFil.Spans.tensor _ (LinearEquiv.refl _ _) (fun g x y => by simp) sd s'
  have sw := GlobalTheory.DRSubQuot.spans_of_injective _ π _ f hf hF hi st
  obtain ⟨h1, h2⟩ := GlobalTheory.Per.FontaineBound.ddR_finite_le ((PP l).PD K) hF π
  exact le_antisymm h2 (GlobalTheory.DRFil.finrank_mul_le_finrank_DdR_of_spans _ π h1 sw)

end Field

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.isCrys_isDR_internalHom :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A V'] {W : Type} [AddCommGroup W] [Module A W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] A W] [FiniteDimensional ℚ_[l] W] [TopologicalSpace W] [IsModuleTopology ℚ_[l] W] [IsTopologicalAddGroup W] [ContinuousConstSMul A W] (ρ : Representation A G V) (ρ' : Representation A G V') (π : Representation A G W), ContAction ρ → ContAction ρ' → ContAction π → ∀ b : W →ₗ[ℚ_[l]] V →ₗ[ℚ_[l]] V', (∀ g w x, b (π g w) (ρ g x) = ρ' g (b w x)) → Function.Injective b → (IsCr φ ρ → IsCr φ ρ' → IsCr φ π) ∧ (IsDr φ ρ → IsDr φ ρ' → IsDr φ π) := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ _ ρ ρ' π _ _ _ b hb hi
  obtain ⟨K, e, -, -, rfl, -⟩ := openField φ hφ
  obtain ⟨f, hf, hfi⟩ := exists_inj_dual_tprod
    (resCoef ℚ_[l] (ρ.comp e.symm.toMonoidHom : Representation A ↥(GK K) V))
    (resCoef ℚ_[l] (ρ'.comp e.symm.toMonoidHom : Representation A ↥(GK K) V'))
    (resCoef ℚ_[l] (π.comp e.symm.toMonoidHom : Representation A ↥(GK K) W)) b
    (fun g w x => hb (e.symm g) w x) hi
  rw [(admissible_transport_equiv _ e ρ).1, (admissible_transport_equiv _ e ρ').1, (admissible_transport_equiv _ e π).1, (admissible_transport_equiv _ e ρ).2,
    (admissible_transport_equiv _ e ρ').2, (admissible_transport_equiv _ e π).2, (isCrIff K _).1, (isCrIff K _).1, (isCrIff K _).1,
    (isCrIff K _).2, (isCrIff K _).2, (isCrIff K _).2]
  exact ⟨crys_hom K _ _ _ f hf hfi, dR_hom K _ _ _ f hf hfi⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtFinFinite
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PointFinitePower
theorem UpperTheory.Reformulated.B.PointFinitePower.ptFin_pow :
    ∀ {O S : Type} [inst : CommRing O] [inst_1 : CommRing S]
    [inst_2 : Algebra O S] [IsNoetherianRing S] (m : Ideal S),
    (∀ (x : S), ∃ (a : O), x - (Algebra.algebraMap O S : O → S) a ∈ m) →
      ∀ (n : ℕ), ∃ (N : Submodule O S), N.FG ∧ ∀ (x : S), ∃ y ∈ N, x - y ∈ m ^ n := by
  intro O S _ _ _ _ m hm n
  induction n with
  | zero =>
    refine ⟨⊥, Submodule.fg_bot, fun x => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    obtain ⟨N, hN, hx⟩ := ih
    obtain ⟨s, hs⟩ : (m ^ n).FG := IsNoetherian.noetherian (m ^ n)
    have key : ∀ z : S, z ∈ Submodule.span S (s : Set S) →
        ∃ w ∈ Submodule.span O (s : Set S), z - w ∈ m ^ (n + 1) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        exact ⟨z, Submodule.subset_span hz, by rw [sub_self]; exact Submodule.zero_mem _⟩
      | zero =>
        exact ⟨0, Submodule.zero_mem _, by rw [sub_self]; exact Submodule.zero_mem _⟩
      | add z z' _ _ h h' =>
        obtain ⟨w, hw, h⟩ := h
        obtain ⟨w', hw', h'⟩ := h'
        refine ⟨w + w', Submodule.add_mem _ hw hw', ?_⟩
        have e : z + z' - (w + w') = (z - w) + (z' - w') := by ring
        rw [e]
        exact Submodule.add_mem _ h h'
      | smul c z hz h =>
        obtain ⟨w, hw, h⟩ := h
        obtain ⟨a, ha⟩ := hm c
        refine ⟨a • w, Submodule.smul_mem _ a hw, ?_⟩
        have hz' : z ∈ m ^ n := by
          rw [← hs]
          exact hz
        have e : c • z - a • w
            = algebraMap O S a * (z - w) + z * (c - algebraMap O S a) := by
          rw [Algebra.smul_def a w, smul_eq_mul]
          ring
        rw [e]
        refine Submodule.add_mem _ (Ideal.mul_mem_left _ _ h) ?_
        rw [pow_succ]
        exact Ideal.mul_mem_mul hz' ha
    refine ⟨N ⊔ Submodule.span O (s : Set S), hN.sup ⟨s, rfl⟩, fun x => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hx x
    rw [← hs] at hxy
    obtain ⟨w, hw, h⟩ := key (x - y) hxy
    refine ⟨y + w, Submodule.add_mem_sup hy hw, ?_⟩
    rw [← sub_sub]
    exact h
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

private theorem ptFin_int {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem ptFin_pow {O S : Type} [CommRing O] [CommRing S] [Algebra O S] [IsNoetherianRing S] (m : Ideal S)
    (hres : ∀ x : S, ∃ a : O, x - algebraMap O S a ∈ m) (n : ℕ) :
    ∃ N : Submodule O S, N.FG ∧ ∀ x : S, ∃ y ∈ N, x - y ∈ m ^ n :=
  _root_.UpperTheory.Reformulated.B.PointFinitePower.ptFin_pow m hres n

private theorem ptFin_finite {O S : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing S] [Algebra O S] [IsLocalRing S] [IsNoetherianRing S] [Algebra.IsIntegral O S]
    (hloc : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ maximalIdeal S)
    (hres : ∀ x : S, ∃ a : O, x - algebraMap O S a ∈ maximalIdeal S) : Module.Finite O S := by
  set J : Ideal S := (maximalIdeal O).map (algebraMap O S) with hJ
  have hJle : J ≤ maximalIdeal S := Ideal.map_le_iff_le_comap.2 hloc
  have hJne : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 (h ▸ hJle))
  haveI : IsHausdorff (maximalIdeal O) S :=
    IsHausdorff.map_algebraMap_iff.1 (IsHausdorff.of_isLocalRing J S hJne)
  have hrad : maximalIdeal S ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hJP, hP⟩
    have h1 : maximalIdeal O ≤ P.comap (algebraMap O S) := Ideal.map_le_iff_le_comap.1 hJP
    have h2 : P.comap (algebraMap O S) = maximalIdeal O :=
      ((maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) h1).symm
    have h3 : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) P
      (by change (P.comap (algebraMap O S)).IsMaximal; rw [h2]; infer_instance)
    exact (eq_maximalIdeal h3).ge
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  obtain ⟨N, hN, h⟩ := ptFin_pow (maximalIdeal S) hres n
  refine (UpperTheory.V.abelian₂.nakayama O (maximalIdeal O) S).2 ⟨?_⟩
  have : (⊤ : Submodule O (S ⧸ (maximalIdeal O) • (⊤ : Submodule O S))) = N.map (Submodule.mkQ _) := by
    symm
    rw [Submodule.map_mkQ_eq_top, eq_top_iff]
    intro x _
    obtain ⟨y, hy, h1⟩ := h x
    have h2 : x - y ∈ (maximalIdeal O) • (⊤ : Submodule O S) := by
      rw [Ideal.smul_top_eq_map]
      exact hn h1
    simpa using Submodule.add_mem_sup h2 hy
  rw [this]
  exact hN.map _

theorem UpperTheory.V.Loc.ptFin :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (F : R →ₐ[O] DualNumber (PadicAlgCl l)), IsLocPt (dualFst F) → ∃ E' : FinExt l, ∀ a, (F a).fst ∈ E'.1 ∧ (F a).snd ∈ E'.1 := by
  intro l _ O _ _ _ _ _ _ _ _ _ R _ _ _ F hF
  classical
  set f := dualFst F with hf
  have hfa : ∀ a, (F a).fst = f a := fun a => rfl
  have hO : ∀ a : O, IsIntegral ℤ_[l] (algebraMap O (PadicAlgCl l) a) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map (IsScalarTower.toAlgHom ℤ_[l] O (PadicAlgCl l))
  have hint : ∀ a : R, IsIntegral O (f a) := by
    intro a
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
    have h1 : IsIntegral O (f (a - algebraMap O R c)) := ((ptFin_int _).2 (hF _ hc).le).tower_top
    have h2 : f a = f (a - algebraMap O R c) + algebraMap O _ c := by simp
    rw [h2]
    exact h1.add isIntegral_algebraMap
  let g : R →ₐ[O] f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' (g : R →+* f.range) hg
  haveI : IsNoetherianRing f.range := isNoetherianRing_of_surjective R _ (g : R →+* f.range) hg
  haveI : IsLocalHom (g : R →+* f.range) := IsLocalHom.of_surjective _ hg
  have hm : ∀ a ∈ maximalIdeal R, g a ∈ maximalIdeal f.range := fun a ha =>
    map_nonunit (g : R →+* f.range) a ha
  haveI : Algebra.IsIntegral O f.range := ⟨fun x => by
    obtain ⟨a, rfl⟩ := hg x
    exact (isIntegral_algHom_iff f.range.val Subtype.val_injective).1 (hint a)⟩
  haveI : Module.Finite O f.range := ptFin_finite
    (fun a ha => by
      rw [← g.commutes]
      exact hm _ (map_nonunit (algebraMap O R) a ha))
    (fun x => by
      obtain ⟨a, rfl⟩ := hg x
      obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
      exact ⟨c, by simpa using hm _ hc⟩)
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := O) (M := f.range)
  choose b hb using fun i => hg (s i)
  obtain ⟨r', o, ho⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := O)
  obtain ⟨P, hP⟩ : (RingHom.ker f).FG := IsNoetherian.noetherian _
  let T : Set (PadicAlgCl l) := Set.range (fun i => algebraMap O (PadicAlgCl l) (o i)) ∪ Set.range (fun i => f (b i)) ∪
    Set.range (fun i => (F (b i)).snd) ∪ (fun p => (F p).snd) '' (P : Set R)
  have hT : T.Finite :=
    (((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union (P.finite_toSet.image _)
  haveI : Finite T := hT
  let E : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] T
  have hE : FiniteDimensional ℚ_[l] E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hTE : T ⊆ E := IntermediateField.subset_adjoin _ _
  have hOE : ∀ c : O, algebraMap O (PadicAlgCl l) c ∈ E := by
    intro c
    have hc : c ∈ Submodule.span ℤ_[l] (Set.range o) := ho ▸ Submodule.mem_top
    obtain ⟨u, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine sum_mem fun i _ => ?_
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact mul_mem (E.algebraMap_mem _) (hTE (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))))
  have hdec : ∀ a : R, ∃ u : Fin r → O, a - ∑ i, u i • b i ∈ RingHom.ker f := by
    intro a
    have hc : g a ∈ Submodule.span O (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hc
    refine ⟨u, ?_⟩
    have h1 : g (a - ∑ i, u i • b i) = 0 := by simp [hb, hu]
    exact congrArg Subtype.val h1
  have h1 : ∀ a, f a ∈ E := by
    intro a
    obtain ⟨u, hu⟩ := hdec a
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hu
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hu, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, Algebra.smul_def]
    exact mul_mem (hOE _) (hTE (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))
  have h2 : ∀ a ∈ Ideal.span (P : Set R), (F a).snd ∈ E := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem z hz => exact hTE (Or.inr ⟨z, hz, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), TrivSqZeroExt.snd_add]; exact add_mem hx hy
    | smul c x hx0 hx =>
      have h0 : (F x).fst = 0 := by
        have : x ∈ RingHom.ker f := hP ▸ hx0
        exact this
      rw [smul_eq_mul, map_mul, DualNumber.snd_mul, h0, mul_zero, add_zero]
      exact mul_mem (h1 c) hx
  refine ⟨⟨E, hE⟩, fun a => ⟨h1 a, ?_⟩⟩
  obtain ⟨u, hu⟩ := hdec a
  have h3 := h2 _ (hP ▸ hu)
  have h4 : (F (∑ i, u i • b i)).snd ∈ E := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, TrivSqZeroExt.snd_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, TrivSqZeroExt.snd_smul, Algebra.smul_def]
    exact mul_mem (hOE _) (hTE (Or.inl (Or.inr ⟨i, rfl⟩)))
  have h5 := add_mem h3 h4
  rwa [← TrivSqZeroExt.snd_add, ← map_add, sub_add_cancel] at h5
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.BkAbove
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecJFacts
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

theorem UpperTheory.V.Loc.decJFacts :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (j : Ω →+* Om l), IsOpenEmbedding ((MonoidHom.snd _ _).comp (UpperTheory.V.Af.decJ F j).subtype) ∧ IsEmbedding ((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype) ∧ ((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype).range = Dec (F := F) (placeJ j) := by
  intro F Ω _ _ _ _ _ _ l _ j
  haveI : IsAlgClosure ℚ Ω := Examples₂.LB.isAlgClosureQ F Ω
  have hj : ∀ x : Ω, x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := by
    intro x
    change (Valued.v : Valuation (Om l) NNReal) (j x) ≤ 1 ↔ _
    rw [← NNReal.coe_le_coe]
    exact Iff.rfl
  let e := Examples₂.LB.eDec (E := F) hj
  have he : Continuous e := Examples₂.LB.continuous_eDec hj
  have hes : Continuous e.symm := Examples₂.LB.continuous_eDec_symm hj
  have hc : ∀ g x, ((e g : _) : GQ l) (j x) = j ((g : G F Ω) x) := Examples₂.LB.eDec_comm hj
  have hK : ∀ x : ↥(UpperTheory.V.Af.decJ F j), x.1.2 ∈ (Examples₂.LB.KwF (E := F) j).fixingSubgroup := by
    intro x
    refine Examples₂.LB.mem_GK_of_fix j _ fun y => ?_
    have := x.2 (algebraMap F Ω y)
    rw [AlgEquiv.commutes] at this
    exact this
  have hfst : ∀ x : ↥(UpperTheory.V.Af.decJ F j), ((e.symm ⟨x.1.2, hK x⟩ : _) : G F Ω) = x.1.1 := by
    intro x
    refine AlgEquiv.ext fun y => j.injective ?_
    rw [← hc, MulEquiv.apply_symm_apply]
    exact x.2 y
  let h : ↥(UpperTheory.V.Af.decJ F j) ≃ₜ ↥(Examples₂.LB.KwF (E := F) j).fixingSubgroup :=
    { toFun := fun x => ⟨x.1.2, hK x⟩
      invFun := fun σ => ⟨(((e.symm σ : _) : G F Ω), σ.1), fun y => by
        have := hc (e.symm σ) y
        rw [MulEquiv.apply_symm_apply] at this
        exact this⟩
      left_inv := fun x => Subtype.ext (Prod.ext (hfst x) rfl)
      right_inv := fun σ => rfl
      continuous_toFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := ((continuous_subtype_val.comp hes).prodMk continuous_subtype_val).subtype_mk _ }
  let e' : ↥(Examples₂.LB.KwF (E := F) j).fixingSubgroup ≃ₜ ↥(Dec (F := F) (placeJ j)) :=
    { toEquiv := e.symm.toEquiv, continuous_toFun := hes, continuous_invFun := he }
  have h1 : ⇑((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype) = Subtype.val ∘ (h.trans e') :=
    funext fun x => (hfst x).symm
  refine ⟨?_, ?_, ?_⟩
  · exact (IntermediateField.fixingSubgroup_isOpen (Examples₂.LB.KwF (E := F) j)).isOpenEmbedding_subtypeVal.comp
      h.isOpenEmbedding
  · rw [h1]
    exact IsEmbedding.subtypeVal.comp (h.trans e').isEmbedding
  · apply SetLike.coe_injective
    rw [MonoidHom.coe_range, h1, Set.range_comp, (h.trans e').surjective.range_eq, Set.image_univ, Subtype.range_coe_subtype]
    rfl
end

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

private theorem bkAbove_avg {k G W : Type} [Field k] [CharZero k] [Group G] [AddCommGroup W] [Module k W]
    (a : G → W →ₗ[k] W) (hmul : ∀ g h w, a (g * h) w = a g (a h w)) (f : G → W)
    (hf : ∀ g h, f (g * h) = f g + a g (f h)) (H : Subgroup G) [H.FiniteIndex] (x : W)
    (hx : ∀ h ∈ H, f h = a h x - x) : ∃ y, ∀ g, f g = a g y - y := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set f' : G → W := fun g => f g - (a g x - x) with hf'
  have hc : ∀ g h, f' (g * h) = f' g + a g (f' h) := by
    intro g h
    simp only [hf', hf, hmul, map_sub]
    abel
  have hH : ∀ g h, h ∈ H → f' (g * h) = f' g := by
    intro g h hh
    rw [hc]
    have : f' h = 0 := by simp only [hf', hx h hh, sub_self]
    rw [this, map_zero, add_zero]
  let F : G ⧸ H → W := Quotient.lift f' (by
    intro g g' hgg
    have h1 : g⁻¹ * g' ∈ H := QuotientGroup.leftRel_apply.1 hgg
    have := hH g _ h1
    rw [mul_inv_cancel_left] at this
    exact this.symm)
  have hF : ∀ (g : G) (q : G ⧸ H), F (g • q) = f' g + a g (F q) := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H z => exact hc g z
  set S : W := ∑ q, F q with hS
  have hsum : ∀ g, S = (Fintype.card (G ⧸ H) : k) • f' g + a g S := by
    intro g
    have e1 : ∑ q, F (g • q) = S := Equiv.sum_comp (MulAction.toPerm g) F
    refine e1.symm.trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hF, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum,
      Nat.cast_smul_eq_nsmul, ← hS]
  have hn : (Fintype.card (G ⧸ H) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨x - (Fintype.card (G ⧸ H) : k)⁻¹ • S, fun g => ?_⟩
  have e : f' g = (Fintype.card (G ⧸ H) : k)⁻¹ • (S - a g S) := by
    rw [eq_inv_smul_iff₀ hn, eq_sub_iff_add_eq]
    exact (hsum g).symm
  have e2 : f g = f' g + (a g x - x) := by simp only [hf', sub_add_cancel]
  rw [e2, e, map_sub, map_smul, smul_sub]
  abel

theorem UpperTheory.V.Loc.bkAbove :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (j : Ω →+* Om l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →* GQ l) (ψ : H →* G F Ω), IsOpenEmbedding φ → (∀ h y, φ h (j y) = j (ψ h y)) → ∀ {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G F Ω) V), ∀ c ∈ Z1 ρ, ((fun h => c (ψ h)) ∈ finiteCocycles φ (ρ.comp ψ) ↔ (fun x : ↥(UpperTheory.V.Af.decJ F j) => c x.1.1) ∈ finiteCocycles ((MonoidHom.snd _ _).comp (UpperTheory.V.Af.decJ F j).subtype) (ρ.comp ((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype))) := by
  intro F Ω _ _ _ _ _ _ l _ j H _ _ _ φ ψ hφ hj C V _ _ _ _ _ _ _ _ _ ρ c hc
  let θ : H →* ↥(UpperTheory.V.Af.decJ F j) := (ψ.prod φ).codRestrict _ (fun h y => hj h y)
  let s : ↥(UpperTheory.V.Af.decJ F j) →* GQ l := (MonoidHom.snd _ _).comp (UpperTheory.V.Af.decJ F j).subtype
  let p : ↥(UpperTheory.V.Af.decJ F j) →* G F Ω := (MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype
  have hs : IsOpenEmbedding s := (UpperTheory.V.Loc.decJFacts (F := F) j).1
  have hθ : Continuous θ := hs.isEmbedding.continuous_iff.2 hφ.continuous
  have hp : Continuous p := continuous_fst.comp continuous_subtype_val
  have hψ : Continuous ψ := hp.comp hθ
  constructor
  · rintro ⟨-, x, hx⟩
    refine ⟨⟨hc.1.comp hp, fun g h => hc.2 _ _⟩, ?_⟩
    haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))
    haveI : Finite (GQ l ⧸ φ.range) := Subgroup.quotient_finite_of_isOpen _ hφ.isOpen_range
    haveI : φ.range.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    haveI : (φ.range.comap s).FiniteIndex := ⟨by
      rw [Subgroup.index_comap]
      exact Subgroup.FiniteIndex.index_ne_zero⟩
    refine bkAbove_avg (k := ℚ_[l]) (fun g => (actC s (ρ.comp p) g).restrictScalars ℚ_[l]) ?_
      (fun g => c (p g) ⊗ₜ[ℚ_[l]] (1 : Bcr l)) ?_ (φ.range.comap s) x ?_
    · intro g h w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [actC]
      | add u v hu hv => simp only [map_add (f := _), hu, hv]
    · intro g h
      simp [actC, hc.2 (p g) (p h), TensorProduct.add_tmul]
    · rintro g ⟨h, hh⟩
      obtain rfl : θ h = g := hs.injective hh
      exact hx h
  · rintro ⟨-, x, hx⟩
    exact ⟨⟨hc.1.comp hψ, fun g h => (congrArg c (map_mul ψ g h)).trans (hc.2 _ _)⟩, x, fun h => hx (θ h)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobFree
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RootEqOne
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe14.Om :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

private lemma UpperTheory.Reformulated.B.Qe14.pow_close {K : Type*} [NormedField K] [IsUltrametricDist K]
    {η : K} (h : ‖η - 1‖ < 1) (n : ℕ) : ‖η ^ n - 1‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : η ^ (n + 1) - 1 = (η ^ n - 1) * (η - 1) + ((η ^ n - 1) + (η - 1)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) ih h.le
    · exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih h)

private lemma UpperTheory.Reformulated.B.Qe14.sum_close {K : Type*} [NormedField K] [IsUltrametricDist K]
    {η : K} (h : ‖η - 1‖ < 1) (n : ℕ) : ‖∑ i ∈ Finset.range n, η ^ i - (n : K)‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ∑ i ∈ Finset.range (n + 1), η ^ i - ((n + 1 : ℕ) : K)
        = (∑ i ∈ Finset.range n, η ^ i - (n : K)) + (η ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt ih (UpperTheory.Reformulated.B.Qe14.pow_close h n))

theorem UpperTheory.Reformulated.B.Qe14.root_eq_one :
    ∀ {v : ℕ} [inst : Fact (Nat.Prime v)] {m : ℕ},
      ¬v ∣ m →
        ∀ {η : UpperTheory.Reformulated.B.Qe14.Om v},
          η ^ m = (1 : UpperTheory.Reformulated.B.Qe14.Om v) →
            ‖η - (1 : UpperTheory.Reformulated.B.Qe14.Om v)‖ < (1 : ℝ) → η = (1 : UpperTheory.Reformulated.B.Qe14.Om v) := by
  intro v inst m hm η hη h
  by_contra hne
  have h1 : (∑ i ∈ Finset.range m, η ^ i) * (η - 1) = 0 := by
    rw [geom_sum_mul, hη, sub_self]
  have h2 : ∑ i ∈ Finset.range m, η ^ i = 0 :=
    (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hne)
  have h3 := UpperTheory.Reformulated.B.Qe14.sum_close h m
  rw [h2, zero_sub, norm_neg] at h3
  have h4 : ((m : ℕ) : PadicAlgCl v) = algebraMap ℚ_[v] (PadicAlgCl v) (m : ℚ_[v]) := by
    simp
  have h5 : ‖((m : ℕ) : PadicAlgCl v)‖ = ‖(m : ℚ_[v])‖ := by
    rw [h4]; exact PadicAlgCl.norm_extends v _
  rw [h5, Padic.norm_natCast_lt_one_iff] at h3
  exact hm h3
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem graph_ext {G Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] [T2Space Y]
    (I : Subgroup G) (σ : G) (hd : (I ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤)
    (hU : ∀ n : ℕ, 0 < n → ∃ U : Subgroup G, U.Normal ∧ IsOpen (U : Set G) ∧ I ≤ U ∧
      ∀ k : ℤ, σ ^ k ∈ U → (n : ℤ) ∣ k) (y : Y) :
    ∃ f : G →* Y, Continuous f ∧ (∀ g ∈ I, f g = 1) ∧ f σ = y := by
  set Δ : Subgroup (G × Y) := I.prod ⊥ ⊔ Subgroup.zpowers (σ, y) with hΔ
  set Γ : Subgroup (G × Y) := Δ.topologicalClosure with hΓ
  have hΓc : IsClosed (Γ : Set (G × Y)) := Δ.isClosed_topologicalClosure
  have hIΓ : ∀ g ∈ I, (g, (1 : Y)) ∈ Γ := fun g hg =>
    Δ.le_topologicalClosure ((le_sup_left : I.prod ⊥ ≤ Δ) ⟨hg, rfl⟩)
  have hσΓ : (σ, y) ∈ Γ :=
    Δ.le_topologicalClosure ((le_sup_right : Subgroup.zpowers (σ, y) ≤ Δ) (Subgroup.mem_zpowers _))
  have hsurj : Γ.map (MonoidHom.fst G Y) = ⊤ := by
    rw [eq_top_iff, ← hd]
    refine Subgroup.topologicalClosure_minimal _ (sup_le (fun g hg => ⟨_, hIΓ g hg, rfl⟩) ?_) ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨_, hσΓ, rfl⟩
    · exact isClosedMap_fst_of_compactSpace _ hΓc
  have hker : ∀ z : Y, ((1 : G), z) ∈ Γ → z = 1 := by
    intro z hz
    by_contra hne
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (G := Y) (U := {z}ᶜ)
      isOpen_compl_singleton (fun h => hne (Set.mem_singleton_iff.1 h).symm)
    haveI : N.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    obtain ⟨U, hUn, hUo, hIU, hUk⟩ := hU N.toSubgroup.index (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
    have hle : Γ ≤ U.prod N.toSubgroup ⊔ Subgroup.zpowers (σ, y) := by
      refine Subgroup.topologicalClosure_minimal _ (sup_le_sup_right (Subgroup.prod_mono hIU bot_le) _) ?_
      refine Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_left ?_)
      exact hUo.prod N.isOpen
    have h1 := hle hz
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at h1
    obtain ⟨⟨u, w⟩, ⟨hu, hw⟩, _, ⟨k, rfl⟩, h⟩ := h1
    have e1 : u * σ ^ k = 1 := congrArg Prod.fst h
    have e2 : w * y ^ k = z := congrArg Prod.snd h
    have h2 : σ ^ k ∈ U := by
      rw [← (inv_eq_of_mul_eq_one_right e1)]
      exact U.inv_mem hu
    obtain ⟨c, rfl⟩ := hUk k h2
    have h3 : z ∈ N.toSubgroup := by
      rw [← e2, zpow_mul, zpow_natCast]
      exact N.toSubgroup.mul_mem hw (N.toSubgroup.zpow_mem (N.toSubgroup.pow_index_mem y) c)
    exact hN h3 rfl
  obtain ⟨f, hf⟩ := Subgroup.exists_eq_graph (G := Γ) (by
    constructor
    · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
      obtain rfl : a = a' := h
      have := hker (b⁻¹ * b') (by simpa using Γ.mul_mem (Γ.inv_mem hab) hab')
      obtain rfl : b = b' := inv_mul_eq_one.1 this
      rfl
    · intro g
      obtain ⟨p, hp, rfl⟩ : g ∈ Γ.map (MonoidHom.fst G Y) := by rw [hsurj]; trivial
      exact ⟨⟨p, hp⟩, rfl⟩)
  have hmem : ∀ a b, (a, b) ∈ Γ ↔ f a = b := fun a b => by rw [hf]; rfl
  refine ⟨f, continuous_iff_isClosed.2 fun C hC => ?_, fun g hg => (hmem _ _).1 (hIΓ g hg), (hmem _ _).1 hσΓ⟩
  have : f ⁻¹' C = Prod.fst '' ((Γ : Set (G × Y)) ∩ Prod.snd ⁻¹' C) := by
    ext g
    constructor
    · intro hg
      exact ⟨(g, f g), ⟨(hmem _ _).2 rfl, hg⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨h1, h2⟩, rfl⟩
      show f a ∈ C
      rw [(hmem _ _).1 h1]
      exact h2
  rw [this]
  exact isClosedMap_fst_of_compactSpace _ (hΓc.inter (hC.preimage continuous_snd))

private theorem root_eq_one {v : ℕ} [Fact v.Prime] {m : ℕ} (hm : ¬ v ∣ m) {η : Om v} (hη : η ^ m = 1)
    (h : ‖η - 1‖ < 1) : η = 1 :=
  _root_.UpperTheory.Reformulated.B.Qe14.root_eq_one hm hη h

private theorem exists_level {v : ℕ} [Fact v.Prime] (σ : GQ v)
    (hσ : UpperTheory.V.Loc.IsFrob (v := v) σ) (n : ℕ) (hn : 0 < n) :
    ∃ U : Subgroup (GQ v), U.Normal ∧ IsOpen (U : Set (GQ v)) ∧ Iq v ≤ U ∧ ∀ k : ℤ, σ ^ k ∈ U → (n : ℤ) ∣ k := by
  have hv : v.Prime := Fact.out
  have h1 : 1 < v ^ n := Nat.one_lt_pow hn.ne' hv.one_lt
  obtain ⟨m, hm⟩ : ∃ m, m = v ^ n - 1 := ⟨_, rfl⟩
  have hm0 : 0 < m := by omega
  have hvm : ¬ v ∣ m := by
    intro h
    have h2 : v ∣ v ^ n := dvd_pow_self v hn.ne'
    have e : v ^ n = m + 1 := by omega
    rw [e] at h2
    exact hv.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))
  haveI : NeZero m := ⟨hm0.ne'⟩
  haveI : NeZero (m : Om v) := ⟨by exact_mod_cast hm0.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om v) m
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hm0.ne'
  have hnorm : ‖ζ‖ = 1 := by
    have := congrArg norm hζ.pow_eq_one
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0.ne').1 this
  have hg : ∀ g : GQ v, (g ζ) ^ m = 1 := fun g => by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hσζ : σ ζ = ζ ^ v := by
    have hz : ζ ^ v ≠ 0 := pow_ne_zero _ hζ0
    rw [← div_eq_one_iff_eq hz]
    refine root_eq_one hvm ?_ ?_
    · rw [div_pow, hg, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, div_one]
    · rw [div_sub_one hz, norm_div, norm_pow, hnorm, one_pow, div_one]
      exact hσ ζ hnorm.le
  have hpow : ∀ k : ℕ, (σ ^ k) ζ = ζ ^ v ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hσζ, ← pow_mul, ← pow_succ']
  refine ⟨MulAction.stabilizer (GQ v) ζ, ⟨fun g hgζ h => ?_⟩, stabilizer_isOpen_of_isIntegral ζ, fun g hgI => ?_,
    fun k hk => ?_⟩
  · have hgζ' : g ζ = ζ := hgζ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (hg h⁻¹)
    show h (g (h⁻¹ ζ)) = ζ
    rw [← hi, map_pow, hgζ', hi, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  · exact hgI ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨m, hm0, hvm, hζ.pow_eq_one⟩⟩
  · have hk' : σ ^ k.natAbs ∈ MulAction.stabilizer (GQ v) ζ := by
      rcases Int.natAbs_eq k with e | e
      · rwa [e, zpow_natCast] at hk
      · rwa [e, zpow_neg, zpow_natCast, inv_mem_iff] at hk
    have h2 : (σ ^ k.natAbs) ζ = ζ := hk'
    rw [hpow] at h2
    rw [Int.natCast_dvd]
    generalize k.natAbs = j at h2
    have hj : 0 < v ^ j := pow_pos hv.pos j
    have h3 : ζ ^ (v ^ j - 1) = 1 := by
      apply mul_right_cancel₀ hζ0
      rw [← pow_succ, Nat.sub_add_cancel hj, h2, one_mul]
    have h4 : v ^ n - 1 ∣ v ^ j - 1 := hm ▸ (hζ.pow_eq_one_iff_dvd _).1 h3
    have h5 := Nat.pow_sub_one_gcd_pow_sub_one v n j
    rw [Nat.gcd_eq_left h4] at h5
    have h6 : 0 < v ^ n.gcd j := pow_pos hv.pos _
    have h7 : v ^ n = v ^ n.gcd j := by omega
    exact Nat.gcd_eq_left_iff_dvd.1 (Nat.pow_right_injective hv.two_le h7).symm

theorem UpperTheory.V.Loc.frobFree :
    ∀ {v : ℕ} [Fact v.Prime] (σ : GQ v), UpperTheory.V.Loc.IsFrob (v := v) σ →
      ∀ (Y : Type) [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] [T2Space Y] (y : Y), ∃ f : GQ v →* Y, Continuous f ∧ (∀ g ∈ Iq v, f g = 1) ∧ f σ = y := by
  intro v _ σ hσ Y _ _ _ _ _ _ y
  have hd : (Iq v ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ := by
    have hv : v.Prime := Fact.out
    have level : ∀ {x : Om v}, x ∈ MaximalUnramifiedExtension v →
        ∃ m : ℕ, ¬ v ∣ m ∧
          ∀ g h : GQ v, (∀ z : Om v, z ^ m = 1 → g z = h z) → g x = h x := by
      intro x hx
      have combine : ∀ {a b : Om v},
          (∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ z : Om v, z ^ m = 1 → g z = h z) → g a = h a) →
          (∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ z : Om v, z ^ m = 1 → g z = h z) → g b = h b) →
          ∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ z : Om v, z ^ m = 1 → g z = h z) →
            g a = h a ∧ g b = h b := by
        rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
        refine ⟨m * n, fun h => (hv.dvd_mul.mp h).elim hm hn, fun g h hgh => ⟨ha g h ?_, hb g h ?_⟩⟩
        · exact fun z hz => hgh z (by rw [pow_mul, hz, one_pow])
        · exact fun z hz => hgh z (by rw [mul_comm, pow_mul, hz, one_pow])
      unfold MaximalUnramifiedExtension at hx
      induction hx using IntermediateField.adjoin_induction with
      | mem x hx =>
        obtain ⟨m, -, hm, hxm⟩ := hx
        exact ⟨m, hm, fun g h hgh => hgh x hxm⟩
      | algebraMap x =>
        exact ⟨1, hv.not_dvd_one, fun g h _ => by rw [AlgEquiv.commutes, AlgEquiv.commutes]⟩
      | add x y _ _ hx hy =>
        obtain ⟨m, hm, h⟩ := combine hx hy
        exact ⟨m, hm, fun g k hgk => by rw [map_add, map_add, (h g k hgk).1, (h g k hgk).2]⟩
      | inv x _ hx =>
        obtain ⟨m, hm, h⟩ := hx
        exact ⟨m, hm, fun g k hgk => by rw [map_inv₀, map_inv₀, h g k hgk]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨m, hm, h⟩ := combine hx hy
        exact ⟨m, hm, fun g k hgk => by rw [map_mul, map_mul, (h g k hgk).1, (h g k hgk).2]⟩
    let H : ClosedSubgroup (GQ v) :=
      ⟨(Iq v ⊔ Subgroup.zpowers σ).topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
    have hH := InfiniteGalois.fixingSubgroup_fixedField H
    have hle : Iq v ⊔ Subgroup.zpowers σ ≤ (H : Subgroup (GQ v)) := Subgroup.le_topologicalClosure _
    refine eq_top_iff.mpr fun g _ => ?_
    change g ∈ (H : Subgroup (GQ v))
    rw [← hH, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxK : x ∈ MaximalUnramifiedExtension v := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension v),
        IntermediateField.mem_fixedField_iff]
      exact fun f hf => hx f (hle (Subgroup.mem_sup_left hf))
    obtain ⟨m, hm, h⟩ := level hxK
    obtain ⟨j, hj⟩ := KStar.IdealValuations.exists_pow_of_aut g hm
    have frob_pow (z : Om v) (hz : z ^ m = 1) (k : ℕ) : (σ ^ k) z = z ^ v ^ k := by
      have hm0 : m ≠ 0 := fun e => hm (e ▸ dvd_zero v)
      have hnorm : ‖z‖ = 1 := by
        apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp
        rw [← norm_pow, hz, norm_one]
      have hσz : σ z = z ^ v := by
        refine KStar.IdealValuations.norm_aut_and_roots.2 m _ _ hm ?_ ?_ (hσ z hnorm.le)
        · rw [← map_pow, hz, map_one]
        · rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hσz, ← pow_mul, ← pow_succ']
    rw [h g (σ ^ j) fun z hz => (hj z hz).trans (frob_pow z hz j).symm]
    exact hx _ (hle (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers σ j)))
  exact graph_ext (Iq v) σ hd (exists_level σ hσ) y
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.V00
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

theorem UpperTheory.V.Loc.v00 :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)) [U.Normal], IsOpen (U : Set (G F Ω)) → ∀ (g : G F Ω) (Sg : Finset (HeightOneSpectrum (𝓞 F))) (M : ℕ), M ≠ 0 → ∃ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (p : ℕ) (σ : G F Ω), w ∉ Sg ∧ p.Prime ∧ ¬ p ∣ M ∧ ¬ (p : ℤ) ∣ discr F ∧ ((p : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ normV w = p ∧ locDeg w = 1 ∧ IsPlaceOver A w ∧ Ine (F := F) A ≤ U ∧ Formalism.ConjugateSelfDual.IsFrob (F := F) A p σ ∧ σ⁻¹ * g ∈ U := by
  intro F Ω _ _ _ _ _ _ U hU hUo g Sg M hM
  classical
  set N : ℕ := M * (discr F).natAbs with hNdef
  have hN0 : N ≠ 0 := Nat.mul_ne_zero hM (Int.natAbs_ne_zero.mpr (discr_ne_zero F))
  have hI : (Ideal.span {(N : 𝓞 F)} : Ideal (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN0
  have hfin := Ideal.finite_factors hI
  obtain ⟨v, hvA, hinert, hram, B, hB, hBU, σ, hσ, hσg⟩ :=
    GlobalTheory.Published.cheb_holds F Ω U hUo hU g (Sg ∪ hfin.toFinset)
  have hnorm : normV v = Ideal.absNorm v.asIdeal := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hp : (normV v).Prime := by
    rw [hnorm]
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hinert
  have hpv : ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
    rw [hnorm]; exact Ideal.absNorm_mem _
  have hNv : (N : 𝓞 F) ∉ v.asIdeal := by
    intro h
    apply hvA
    apply Finset.mem_union_right
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_le,
      Set.singleton_subset_iff]
    exact h
  have hdvd : ∀ k : ℕ, normV v ∣ k → (k : 𝓞 F) ∈ v.asIdeal := by
    rintro k ⟨c, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ hpv
  refine ⟨v, B, normV v, σ, fun h => hvA (Finset.mem_union_left _ h), hp, ?_, ?_, hpv, rfl,
    ?_, hB, hBU, hσ, ?_⟩
  · intro h
    exact hNv (hdvd N (dvd_mul_of_dvd_left h _))
  · intro h
    apply hNv
    apply hdvd
    apply dvd_mul_of_dvd_right
    exact Int.natCast_dvd.mp h
  · simp [locDeg, hram, hinert]
  · have h1 : g * σ⁻¹ ∈ U := by
      have := U.inv_mem hσg
      simpa using this
    have h2 := hU.conj_mem _ h1 σ⁻¹
    simpa [mul_assoc] using h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NonemptyCohomologyRestrictScalarsLinearEquiv
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private def subEq {Q A X : Type} [CommRing Q] [CommRing A] [Algebra Q A] [AddCommGroup X] [Module A X]
    [Module Q X] [IsScalarTower Q A X] (Z' : Submodule Q X) (Z : Submodule A X)
    (hZ : ∀ x, x ∈ Z' ↔ x ∈ Z) : Z' ≃ₗ[Q] Z where
  toFun x := ⟨x.1, (hZ _).1 x.2⟩
  invFun x := ⟨x.1, (hZ _).2 x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem quotEq {Q A X : Type} [CommRing Q] [CommRing A] [Algebra Q A] [AddCommGroup X] [Module A X]
    [Module Q X] [IsScalarTower Q A X] (Z' B' : Submodule Q X) (Z B : Submodule A X)
    (hZ : ∀ x, x ∈ Z' ↔ x ∈ Z) (hB : ∀ x, x ∈ B' ↔ x ∈ B) :
    Nonempty ((Z' ⧸ B'.comap Z'.subtype) ≃ₗ[Q] (Z ⧸ B.comap Z.subtype)) := by
  refine ⟨(Submodule.Quotient.equiv (B'.comap Z'.subtype) ((B.comap Z.subtype).restrictScalars Q)
    (subEq Z' Z hZ) ?_).trans (Submodule.Quotient.restrictScalarsEquiv Q (B.comap Z.subtype))⟩
  ext ⟨x, hx⟩
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : (y : X) = x := congrArg Subtype.val hyx
    show x ∈ B
    rw [← this]
    exact (hB _).1 hy
  · intro h
    exact ⟨⟨x, (hZ x).2 hx⟩, (hB x).2 h, rfl⟩

theorem UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv :
    ∀ (Q : Type) {A : Type} [CommRing Q] [CommRing A] [Algebra Q A] {G : Type} [Group G] [TopologicalSpace G] {V : Type} [AddCommGroup V] [Module A V] [Module Q V] [IsScalarTower Q A V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] [ContinuousConstSMul Q V] (ρ : Representation A G V), Nonempty (↥(H0 (resCoef Q ρ)) ≃ₗ[Q] ↥(H0 ρ)) ∧ Nonempty (H1 (resCoef Q ρ) ≃ₗ[Q] H1 ρ) ∧ Nonempty (H2 (resCoef Q ρ) ≃ₗ[Q] H2 ρ) ∧ ∀ n, Nonempty (Hn (resCoef Q ρ) n ≃ₗ[Q] Hn ρ n) := by
  intro Q A _ _ _ G _ _ V _ _ _ _ _ _ _ _ ρ
  have hd : ∀ n (f : (Fin n → G) → V), dn (resCoef Q ρ) n f = dn ρ n f := by
    intro n f
    funext g
    rw [dn_apply, dn_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul A ((-1 : Q) ^ ((j : ℕ) + 1))]
    simp
  refine ⟨⟨subEq _ _ fun x => Iff.rfl⟩, quotEq _ _ _ _ (fun x => Iff.rfl) ?_,
    quotEq _ _ _ _ (fun x => Iff.rfl) ?_, fun n => quotEq _ _ _ _ ?_ ?_⟩
  · intro x
    simp only [ReciprocityTheory.Gal.B1, LinearMap.mem_range]
    exact Iff.rfl
  · intro x
    simp only [ReciprocityTheory.Gal.B2, Submodule.mem_map, mem_contMaps]
    exact Iff.rfl
  · intro x
    simp only [ReciprocityTheory.Gal.Zn, Submodule.mem_inf, LinearMap.mem_ker, ReciprocityTheory.Gal.Cn,
      mem_contMaps, hd]
  · intro x
    cases n with
    | zero => simp [ReciprocityTheory.Gal.Bn]
    | succ n => simp only [ReciprocityTheory.Gal.Bn, Submodule.mem_map, ReciprocityTheory.Gal.Cn, mem_contMaps, hd]
end
