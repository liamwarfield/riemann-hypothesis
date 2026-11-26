module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceCoreOfSumPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfIzumiSmallValueIdealMapLeSpanStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SecMoveK
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullbackStructureModuleIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetDimDropClosed
set_option autoImplicit false

open TopologicalSpace

namespace GlobalTheory

theorem exists_finite_topologicalKrullDim_inter_add_one_le {T : Type} [TopologicalSpace T]
    [NoetherianSpace T] [QuasiSober T] (Z : Set T) (hZ : IsClosed Z) :
    ∃ S : Set T, S.Finite ∧ ∀ C : Set T, IsClosed C → Disjoint S C →
      topologicalKrullDim (Z ∩ C : Set T) + 1 ≤ topologicalKrullDim Z := by
  obtain ⟨F, hF, hcl, hirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  choose g hg using fun t : F => QuasiSober.sober (hirr t.1 t.2) (hcl t.1 t.2)
  have := hF.to_subtype
  refine ⟨Set.range g, Set.finite_range g, fun C hC hd => ?_⟩
  refine topologicalKrullDim_add_one_le (hZ.inter hC) hZ ?_
  rintro x ⟨⟨t, ht, hxt⟩, -⟩
  exact ⟨g ⟨t, ht⟩, ⟨t, ht, (hg ⟨t, ht⟩).mem⟩, fun h => Set.disjoint_left.1 hd ⟨_, rfl⟩ h.2,
    (hg ⟨t, ht⟩).specializes hxt⟩

end GlobalTheory
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.FieldProj

theorem chi_eq_length_sections {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (k : Type)
    [Field k] [Algebra k Γ(X, ⊤)] (F : X.Modules) [IsFiniteQC F] (h : suppDim F ≤ 0) :
    chi k F = (Module.length k (sectionsOn F ⊤)).toNat := by
  rw [chi_eq_hdim_zero k fun n hn => subsingleton_coh_of_suppDim_le_zero h hn, hdim_zero,
    Module.length_eq_rank, Cardinal.toNat_toENat]
  rfl

theorem dim_le_zero_of_finite_closed {T : Type} [TopologicalSpace T] {s : Set T} (hs : s.Finite)
    (hc : ∀ x ∈ s, IsClosed ({x} : Set T)) : topologicalKrullDim s ≤ 0 := by
  have : Finite s := hs.to_subtype
  have : T1Space s := ⟨fun x => by
    simpa [← Set.image_singleton, Set.preimage_image_eq _ Subtype.val_injective] using
      (hc x.1 x.2).preimage (continuous_subtype_val (p := (· ∈ s)))⟩
  exact topologicalKrullDim_zero_of_discreteTopology s

theorem eq_empty_of_dim_add_one_le_zero {T : Type} [TopologicalSpace T] {S : Set T}
    (h : topologicalKrullDim S + 1 ≤ ((0 : ℕ) : WithBot ℕ∞)) : S = ∅ := by
  by_contra hS
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hS
  have hne : topologicalKrullDim S ≠ ⊥ :=
    mt topologicalKrullDim_eq_bot_iff.1 (not_isEmpty_iff.2 ⟨⟨x, hx⟩⟩)
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hne
  rw [← ha] at h
  have h' : ((a + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((0 : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
  rw [WithBot.coe_le_coe] at h'
  simp at h'

theorem closure_nonzeroLocus_eq_top {X : Scheme.{0}} [IsLocallyNoetherian X] {A : LB X}
    (hA : IsAmpleLB A) {S : Set X} (hS : S.Finite) :
    AddSubgroup.closure {c : Pic X | ∃ (N : LB X) (hN : N.IsLB) (t : N.Sec),
      S ⊆ nonzeroLocus t ∧ c = cls N hN} = ⊤ := by
  refine eq_top_iff.2 fun c _ => ?_
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  obtain ⟨n, h₁, h₂⟩ := ((hA.eventually_exists_finite_subset_nonzeroLocus hM hS).and
    (hA.eventually_exists_finite_subset_nonzeroLocus (LB.isLB_triv X) hS)).exists
  obtain ⟨P, hP, eP⟩ := cls_surj (cls M hM + n • cls A hA.isLB)
  obtain ⟨Q, hQ, eQ⟩ := cls_surj (cls _ (LB.isLB_triv X) + n • cls A hA.isLB)
  obtain ⟨s, hs⟩ := h₁ P hP eP
  obtain ⟨t, ht⟩ := h₂ Q hQ eQ
  have e : cls M hM = cls P hP - cls Q hQ := by
    rw [eP, eQ, cls_triv, zero_add, add_sub_cancel_right]
  rw [e]
  exact sub_mem (AddSubgroup.subset_closure ⟨P, hP, s, hs, rfl⟩)
    (AddSubgroup.subset_closure ⟨Q, hQ, t, ht, rfl⟩)

theorem nonempty_pullback_structureModule_iso {X Y : Scheme.{0}} (f : X ⟶ Y) :
    Nonempty ((Scheme.Modules.pullback f).obj (QCoh.structureModule Y) ≅ QCoh.structureModule X) :=
  haveI : (TopologicalSpace.Opens.map f.base).Final :=
    final_of_representablyFlat _
  haveI : IsIso (SheafOfModules.pullbackObjUnitToUnit.{0} f.toRingCatSheafHom) := inferInstance
  ⟨asIso (SheafOfModules.pullbackObjUnitToUnit.{0} f.toRingCatSheafHom)⟩

section Main

variable {k : Type} [Field k] {X Y : Scheme.{0}} [Algebra k Γ(X, ⊤)] [Algebra k Γ(Y, ⊤)]
  (f : X ⟶ Y) (hf : ∀ r : k, f.appTop (algebraMap k Γ(Y, ⊤) r) = algebraMap k Γ(X, ⊤) r)
  (V : Y.Opens) (n : ℕ) (hV : IsAffineOpen V) (hV' : IsAffineOpen (f ⁻¹ᵁ V))
  (hfree : letI := (f.app V).hom.toAlgebra
    Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧
      Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V) = n)

include hf hV hV' hfree

theorem chi_pullback_eq_mul [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (G : Y.Modules) [IsFiniteQC G] (hdim : suppDim G ≤ 0) (hsub : support G ⊆ (V : Set Y)) :
    chi k ((Scheme.Modules.pullback f).obj G) = n * chi k G := by
  have hfin : (support G).Finite := finite_support_of_suppDim_le_zero hdim
  have hcl : ∀ x ∈ support G, IsClosed ({x} : Set Y) := fun x hx =>
    isClosed_singleton_of_suppDim_le_zero hdim hx
  have hsupp' : support ((Scheme.Modules.pullback f).obj G) = f.base ⁻¹' support G :=
    QCoh.support_pullback f G
  have hpts : ∀ y ∈ support ((Scheme.Modules.pullback f).obj G), IsClosed ({y} : Set X) := by
    intro y hy
    rw [hsupp'] at hy
    exact (fibre_finite_isClosed_of_affine_finite f V hV hV' hfree.2.1 _ (hsub hy) (hcl _ hy)).2 y rfl
  have hfin' : (support ((Scheme.Modules.pullback f).obj G)).Finite := by
    rw [hsupp']
    refine (Set.Finite.biUnion (t := fun x => f.base ⁻¹' {x}) hfin fun x hx =>
      (fibre_finite_isClosed_of_affine_finite f V hV hV' hfree.2.1 _ (hsub hx) (hcl _ hx)).1).subset
      fun y hy => ?_
    exact Set.mem_biUnion hy rfl
  have hdim' : suppDim ((Scheme.Modules.pullback f).obj G) ≤ 0 :=
    dim_le_zero_of_finite_closed hfin' hpts
  rw [chi_eq_length_sections k _ hdim, chi_eq_length_sections k _ hdim',
    length_sectionsOn_top_eq_sum_of_separating G k (fun _ : Unit => V)
      (fun x hx => Set.mem_iUnion.2 ⟨(), hsub hx⟩) (fun i j hij => absurd rfl hij),
    length_sectionsOn_top_eq_sum_of_separating _ k (fun _ : Unit => f ⁻¹ᵁ V) ?_
      (fun i j hij => absurd rfl hij)]
  · simp_rw [length_sectionsOn_pullback_of_free k f hf _ n hV hV' hfree G]
    rw [← Finset.mul_sum, ENat.toNat_mul]
    simp
  · intro y hy
    rw [hsupp'] at hy
    exact Set.mem_iUnion.2 ⟨(), hsub hy⟩

theorem diffVanish_chiPic_pullback_sub [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Y] {A : LB Y} (hA : IsAmpleLB A)
    (hX : ∀ (F : X.Modules) [IsFiniteQC F], FiniteCohTwists k F)
    (hY : ∀ (F : Y.Modules) [IsFiniteQC F], FiniteCohTwists k F) :
    ∀ (m : ℕ) (G : Y.Modules) [IsFiniteQC G], suppDim G ≤ m →
      topologicalKrullDim (support G ∩ (V : Set Y)ᶜ : Set Y) + 1 ≤ (m : WithBot ℕ∞) →
      DiffVanish m ((chiPic k ((Scheme.Modules.pullback f).obj G) ∘ pull f) -
        (AddMonoidHom.mulLeft (n : ℤ)) ∘ chiPic k G) := by
  intro m
  induction m with
  | zero =>
    intro G _ h0 hk
    have hGU : support G ⊆ (V : Set Y) := fun x hx => by
      by_contra h
      have := eq_empty_of_dim_add_one_le_zero hk
      exact (Set.eq_empty_iff_forall_notMem.1 this) x ⟨hx, h⟩
    refine diffVanish_zero_iff.2 (funext fun c => ?_)
    obtain ⟨M, hM, rfl⟩ := cls_surj c
    have hM' := Semi.LB.isLB_pull hM f
    have := isFiniteQC_twist (F := G) hM
    have e := Twist.pullbackIso G f hM
    have hb := chi_pullback_eq_mul f hf V n hV hV' hfree (twist G M) (by rwa [suppDim_twist hM])
      (by rwa [support_twist hM])
    simp only [Pi.sub_apply, Function.comp_apply, Pi.zero_apply, AddMonoidHom.coe_mulLeft]
    rw [← cls_pull hM f hM', chiPic_cls, chiPic_cls, ← chi_congr k e, hb, sub_self]
  | succ m ih =>
    intro G _ hk hUk
    set G' := (Scheme.Modules.pullback f).obj G
    have hZ : IsClosed (support G ∩ (V : Set Y)ᶜ) :=
      (isClosed_support (F := G)).inter V.isOpen.isClosed_compl
    obtain ⟨S₃, hS₃, hS₃'⟩ := exists_finite_topologicalKrullDim_inter_add_one_le _ hZ
    let S : Set Y := assPoints G ∪ f.base '' assPoints G' ∪ S₃
    have hS : S.Finite := ((finite_assPoints G).union ((finite_assPoints G').image _)).union hS₃
    refine diffVanish_of_generators (closure_nonzeroLocus_eq_top hA hS) fun g hg => ?_
    obtain ⟨N, hN, t, hSt, e⟩ := hg 0
    have hN' := Semi.LB.isLB_pull hN f
    haveI hmono : Mono (cutHom G hN t) :=
      (mono_cutHom_iff G hN t).2 fun x hx => hSt (Or.inl (Or.inl hx))
    haveI hmono' : Mono (cutHom G' hN' (secPull t f)) :=
      (mono_cutHom_iff G' hN' _).2 fun x hx => by
        rw [nonzeroLocus_secPull]
        exact hSt (Or.inl (Or.inr ⟨x, hx, rfl⟩))
    have h₁ := bwdDiff_chiPic_eq_chiPic_cut hN t (hY G)
    have h₂ := bwdDiff_chiPic_eq_chiPic_cut hN' (secPull t f) (hX G')
    obtain ⟨ec⟩ := cut_pullback_iso f G hN t hN'
    have key : bwdDiff (cls N hN) ((chiPic k G' ∘ pull f) -
        (AddMonoidHom.mulLeft (n : ℤ)) ∘ chiPic k G) =
        (chiPic k ((Scheme.Modules.pullback f).obj (cut G hN t)) ∘ pull f) -
          (AddMonoidHom.mulLeft (n : ℤ)) ∘ chiPic k (cut G hN t) := by
      funext c
      have a₁ := congrFun h₁ c
      have a₂ := congrFun h₂ (pull f c)
      rw [chiPic_congr k ec.symm] at a₂
      simp only [bwdDiff_apply] at a₁ a₂
      simp only [bwdDiff_apply, Pi.sub_apply, Function.comp_apply,
        AddMonoidHom.coe_mulLeft, map_sub, cls_pull hN f hN'] at a₂ ⊢
      rw [← a₁, ← a₂]
      ring
    rw [← Fin.cons_self_tail g, multiDiff_cons', e, key]
    refine ih (cut G hN t) (suppDim_cut_le G hN t hk) ?_ _
    have hdim := hS₃' (nonzeroLocus t : Set Y)ᶜ (nonzeroLocus t).isOpen.isClosed_compl
      (Set.disjoint_compl_right_iff_subset.2 fun x hx => hSt (Or.inr hx))
    have hZk : topologicalKrullDim (support G ∩ (V : Set Y)ᶜ : Set Y) ≤ m :=
      ENat.WithBot.add_le_add_one_right_iff.1 (hUk.trans_eq (Nat.cast_succ m))
    refine le_trans ?_ (hdim.trans hZk)
    refine add_le_add_left (topologicalKrullDim_mono ?_) 1
    rw [support_cut]
    rintro x ⟨⟨hx, hx'⟩, hxU⟩
    exact ⟨⟨hx, hxU⟩, hx'⟩

end Main

theorem interNum_pull_eq_mul (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral Y]
    (sY : Y ⟶ Sp k) (f : X ⟶ Y) (hX : IsProjOver (f ≫ sY)) (hY : IsProjOver sY)
    (V : Y.Opens) (n : ℕ) (hgen : genericPoint Y ∈ V) (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (f ⁻¹ᵁ V))
    (hfree : letI := (f.app V).hom.toAlgebra
      Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧
        Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V) = n)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ d) (L : Fin d → LB Y) (hL : ∀ i, (L i).IsLB) :
    letI := GlobalTheory.algebraΓOfHom (f ≫ sY); letI := GlobalTheory.algebraΓOfHom sY
    GlobalTheory.interNum k (GlobalTheory.QCoh.structureModule X) (fun i => (L i).pull f) =
      (n : ℤ) * GlobalTheory.interNum k (GlobalTheory.QCoh.structureModule Y) L := by
  letI := GlobalTheory.algebraΓOfHom (f ≫ sY)
  letI := GlobalTheory.algebraΓOfHom sY
  have := isNoetherian_of_isProjOver hX
  have := isNoetherian_of_isProjOver hY
  obtain ⟨-, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hY
  have hf : ∀ r : k, f.appTop (algebraMap k Γ(Y, ⊤) r) = algebraMap k Γ(X, ⊤) r := fun _ => rfl
  have hVd : topologicalKrullDim ((V : Set Y)ᶜ : Set Y) + 1 ≤ (d : WithBot ℕ∞) := by
    refine (topologicalKrullDim_add_one_le V.isOpen.isClosed_compl isClosed_univ
      fun x _ => ⟨genericPoint Y, trivial, fun h => h hgen, genericPoint_specializes x⟩).trans ?_
    exact (topologicalKrullDim_subspace_le _ _).trans hd
  have hD := diffVanish_chiPic_pullback_sub f hf V n hV hV' hfree hA
    (fun F _ => finiteCohTwists_of_isProjOver (fun _ => rfl) F hX)
    (fun F _ => finiteCohTwists_of_isProjOver (fun _ => rfl) F hY) d (QCoh.structureModule Y)
    (suppDim_structureModule.trans_le hd)
    ((add_le_add_left (topologicalKrullDim_mono Set.inter_subset_right) 1).trans hVd)
  obtain ⟨e⟩ := nonempty_pullback_structureModule_iso f
  have h0 := congrFun (hD fun i => cls (L i) (hL i)) 0
  simp only [multiDiff_sub, multiDiff_map, multiDiff_comap, Pi.sub_apply, Pi.zero_apply,
    Function.comp_apply, chiPic_congr k e, map_zero] at h0
  rw [AddMonoidHom.coe_mulLeft, sub_eq_zero] at h0
  rw [interNum_eq_multiDiff k _ hL,
    interNum_eq_multiDiff k _ fun i => Semi.LB.isLB_pull (hL i) f]
  exact h0

end GlobalTheory.FieldProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IzumiBoundModPrincipalIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IzumiBoundModPrincipalIdeal
noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Izumi

theorem small_mod_principal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ f ∈ M.O x, f ≠ 0 → ∃ C : ℕ → ℕ, ∀ (e : ℕ) (F : M.O x), (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y → ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) f‖ ∨ ∃ h, NonUnitAt M x h ∧ ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) h‖ ^ C e) → ∃ a b : M.O x, (F : Ω) = a * f + b ∧ b ∈ Ideal.span {c : M.O x | ¬ IsUnit c} ^ e := by
  intro o Ω _ _ _ _ M hn U hU x hx f hf hf0
  haveI : IsDedekindDomain o := ArithBase.ded Ω
  haveI : IsNoetherianRing (M.O x) := M.isNoetherianRing_O x
  have hB := GlobalTheory.T.iInf_izumiSmallValueIdeal_map_le_span o Ω M hn U hU x hx f hf hf0
  choose C hC using exists_le_span_sup_pow (M.O x) (smallIdeal M U x f) ⟨f, hf⟩
    (smallIdeal_antitone U x f) (self_mem_smallIdeal U hf) hB
  refine ⟨C, fun e F hF => ?_⟩
  have hmem : F ∈ Ideal.span {(⟨f, hf⟩ : M.O x)} ⊔ maximalIdeal (M.O x) ^ e := hC e (mem_smallIdeal.2 hF)
  obtain ⟨u, hu, b, hb, rfl⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have hm : Ideal.span {c : M.O x | ¬ IsUnit c} = maximalIdeal (M.O x) := Ideal.span_eq (maximalIdeal (M.O x))
  refine ⟨a, b, rfl, ?_⟩
  rw [hm]
  exact hb

end GlobalTheory.Izumi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IzumiBoundModPrincipalIdealStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.izumi_bound_mod_principal_ideal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ f ∈ M.O x, f ≠ 0 → ∃ C : ℕ → ℕ, ∀ (e : ℕ) (F : M.O x), (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y → ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) f‖ ∨ ∃ h, NonUnitAt M x h ∧ ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) h‖ ^ C e) → ∃ a b : M.O x, (F : Ω) = a * f + b ∧ b ∈ Ideal.span {c : M.O x | ¬ IsUnit c} ^ e := by
  first | exact @GlobalTheory.Izumi.small_mod_principal | exact GlobalTheory.Izumi.small_mod_principal | (intros; apply GlobalTheory.Izumi.small_mod_principal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulSecK
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsDomain R]

def mulφB (D : DegPre R) (m : ℕ) (χ : D.X) : Fin 4 ⊕ Fin 4 → (D.P.A.left ⟶ D.P.A.left) :=
  Sum.elim (D.famφB (m • χ)) (fun i => (mulA D.P.A m).left ≫ D.famφB χ i)

def mulεB (k k' : ℕ) : Fin 4 ⊕ Fin 4 → ℤ :=
  Sum.elim (DegPre.famε k') (fun i => - DegPre.famε k i)

def MulSecB (D : DegPre R) (m : ℕ) {k k' : ℕ} (χ : D.X) (b : D.SecB k χ) (b' : D.SecB k' (m • χ)) : Prop :=
  ∃ u : LB.Gen (LB.LinComb D.P.L (mulφB D m χ) (mulεB k k')), u.IsGen ∧
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (eSec D.P.A)) (GeneratorPullback.powGen D.P.L _ _ D.rig (k' - k)) ∧
    GeneratorPullback.SecRel D.P.L (D.famφB (m • χ)) (DegPre.famε k') b' (D.famφB χ) (DegPre.famε k) b (mulA D.P.A m).left
      (mulφB D m χ) (mulεB k k') u

def MulFam {I : Ideal R} {D : DegPre R} (m : ℕ) {k k' : ℕ} (F : IntFam I D k) (G : IntFam I D k') : Prop :=
  (∀ χ, MulSecB D m χ (F.f χ) (G.f (m • χ))) ∧ ∀ β : D.X, (∀ χ, β ≠ m • χ) → ∀ j, (G.f β).f j = 0

end

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}

def MulSecK (C : LabCover D) (m : ℕ) {k k' : ℕ} (θ : SecK C.P.L.L C.α k) (S : SecK C.P.L.L C.α k') : Prop :=
  ∃ u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![(k' : ℤ), -(k : ℤ)]), u.IsGen ∧
    ∀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J, Good C.P.L.L z J →
      sval S p z J = (val u (p ≫ C.α) z J).val * sval θ (p ≫ (mulA C.A.A m).left) z J

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompleteDVRCharZeroOfFiniteInjectiveExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompleteDVRCharZeroOfFiniteInjectiveExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem cDvr_of_finExt : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R → FinExt ρ → GlobalTheory.LN.CDvr R' := by
  intro R R' _ _ _ _ _ _ ρ hR hE
  obtain ⟨hdvr, -, hc0⟩ := hR
  obtain ⟨⟨hnoeth, -, hic, hcomp⟩, hinj, hfin⟩ := hE
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  haveI : Algebra.IsIntegral R R' := inferInstance
  haveI := hnoeth
  haveI := hic
  have hinj' : Function.Injective (algebraMap R R') := hinj
  haveI : Ring.DimensionLEOne R' := Ring.DimensionLEOne.of_isIntegral R R'
  haveI : IsDedekindDomain R' := { }
  have hnf : ¬ IsField R' := fun h =>
    IsDiscreteValuationRing.not_isField R (isField_of_isIntegral_of_isField hinj' h)
  have hdvr' : IsDiscreteValuationRing R' := ((IsDiscreteValuationRing.TFAE R' hnf).out 1 3).2 (inferInstance : IsDedekindDomain R')
  exact ⟨hdvr', hcomp, charZero_of_injective_algebraMap hinj'⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompleteDVRCharZeroOfFiniteInjectiveExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompleteDVRCharZero_of_finiteInjectiveExtension : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R → FinExt ρ → GlobalTheory.LN.CDvr R' := by
  first | exact @GlobalTheory.Mum.cDvr_of_finExt | exact GlobalTheory.Mum.cDvr_of_finExt | (intros; apply GlobalTheory.Mum.cDvr_of_finExt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedPosDefFiniteProjectiveLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedPosDefFiniteProjectiveLattice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.UTrait

theorem balanced_posDef_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c), T.be ∈ balForms H.bar T.P.D.toPre.X ∧ (∀ y, y ≠ 0 → 0 < T.be y y) ∧ Module.Finite (𝓞 E) T.P.D.toPre.X ∧ Module.Projective (𝓞 E) T.P.D.toPre.X ∧ ∃ n : ℕ, Nonempty (T.P.D.toPre.X ≃ₗ[ℤ] (Fin n → ℤ)) := by
  intro E _ _ _ H Dw l Xo c T
  haveI hf : Module.Finite (𝓞 E) T.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  refine ⟨(balForms_eq_levelForms H T.P.D.toPre.X).ge T.lev, fun y hy => ?_, hf, ?_, _,
    ⟨(Module.finBasis ℤ T.P.D.toPre.X).equivFun⟩⟩
  · obtain ⟨i, hi⟩ := IsMonomial.exists_pos (maximalIdeal.isMaximal T.V).ne_top T.mono hy
    simpa using hi
  · exact GlobalTheory.Forms.projective_of_int (𝓞 E) _

end GlobalTheory.UPoinc.UTrait
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedPosDefFiniteProjectiveLatticeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balanced_posDef_finite_projective_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c), T.be ∈ balForms H.bar T.P.D.toPre.X ∧ (∀ y, y ≠ 0 → 0 < T.be y y) ∧ Module.Finite (𝓞 E) T.P.D.toPre.X ∧ Module.Projective (𝓞 E) T.P.D.toPre.X ∧ ∃ n : ℕ, Nonempty (T.P.D.toPre.X ≃ₗ[ℤ] (Fin n → ℤ)) := by
  first | exact @GlobalTheory.UPoinc.UTrait.balanced_posDef_lattice | exact GlobalTheory.UPoinc.UTrait.balanced_posDef_lattice | (intros; apply GlobalTheory.UPoinc.UTrait.balanced_posDef_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusDualAddFinrankKerVerschiebung
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusDualAddFinrankKerVerschiebung
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

namespace GlobalTheory.PDivGroup

theorem finrank_range_relFrob_dual_add_finrank_ker_verschiebung (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (h : (p : k) = 0) (G : PDivGroup p k) : Module.finrank k (LinearMap.range ((relFrob h G.dual).app 1 : (frobTwist h G.dual).A 1 →ₐ[k] G.dual.A 1).toLinearMap) + Module.finrank k (LinearMap.ker ((verschiebung h G).app 1 : G.A 1 →ₐ[k] (frobTwist h G).A 1).toLinearMap) = Module.finrank k (G.A 1) := by
  let e : G.dual.A 1 ≃ₗ[k] Module.Dual k (G.A 1) := CartierDual.toDual k (G.A 1)
  set W := LinearMap.range ((relFrob h G.dual).app 1 : (frobTwist h G.dual).A 1 →ₐ[k] G.dual.A 1).toLinearMap with hW
  have hker : LinearMap.ker ((verschiebung h G).app 1 : G.A 1 →ₐ[k] (frobTwist h G).A 1).toLinearMap
      = (W.map e.toLinearMap).dualCoannihilator := by
    ext a
    rw [Submodule.mem_dualCoannihilator, LinearMap.mem_ker]
    change (verschiebung h G).app 1 a = 0 ↔ _
    constructor
    · rintro ha _ ⟨_, ⟨x, rfl⟩, rfl⟩
      change e ((relFrob h G.dual).app 1 x) a = 0
      induction x using frobTwist_induction h (G := G.dual) 1 with
      | h0 => simp
      | h2 x y hx hy => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
      | h1 r χ =>
        rw [map_smul, map_smul, LinearMap.smul_apply, relFrob_app_frobProj]
        have := frobTwistDual_verschiebung h 1 χ a
        rw [ha, map_zero] at this
        exact (congrArg (r • ·) this.symm).trans (smul_zero r)
    · intro ha
      refine frobTwist_ext_dual h 1 fun χ => ?_
      rw [frobTwistDual_verschiebung, map_zero]
      refine ha _ ⟨_, ⟨(frobProj h G.dual).app 1 χ, rfl⟩, ?_⟩
      exact congrArg e (relFrob_app_frobProj h (G := G.dual) 1 χ)
  rw [hker, ← e.finrank_map_eq W]
  exact Subspace.finrank_add_finrank_dualCoannihilator_eq _

end GlobalTheory.PDivGroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusDualAddFinrankKerVerschiebungStatement
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (h : (p : k) = 0) (G : PDivGroup p k), Module.finrank k (LinearMap.range ((relFrob h G.dual).app 1 : (frobTwist h G.dual).A 1 →ₐ[k] G.dual.A 1).toLinearMap) + Module.finrank k (LinearMap.ker ((verschiebung h G).app 1 : G.A 1 →ₐ[k] (frobTwist h G).A 1).toLinearMap) = Module.finrank k (G.A 1) := by
  first | exact @GlobalTheory.PDivGroup.finrank_range_relFrob_dual_add_finrank_ker_verschiebung | exact GlobalTheory.PDivGroup.finrank_range_relFrob_dual_add_finrank_ker_verschiebung | (intros; apply GlobalTheory.PDivGroup.finrank_range_relFrob_dual_add_finrank_ker_verschiebung <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointFlatOfModificationOfDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointFlatOfModificationOfDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Modif.flat_gp (R : Type) [CommRing R] [IsDomain R] (M : Modif R) : Flat M.gp := by
  haveI := M.integral
  haveI := M.dominant
  refine Flat.of_stalkMap _ fun x => ?_
  have hx : M.gp.base x = genericPoint M.S := by
    have hd : DenseRange M.gp.base := M.gp.denseRange
    have hr : Set.range M.gp.base = {M.gp.base x} := by
      ext y; constructor
      · rintro ⟨z, rfl⟩; rw [Subsingleton.elim z x]; rfl
      · rintro rfl; exact ⟨x, rfl⟩
    have hg : IsGenericPoint (M.gp.base x) ⊤ := by
      rw [IsGenericPoint, ← hr]
      simpa [Set.top_eq_univ] using hd.closure_range
    exact hg.eq (genericPoint_spec M.S)
  have hF : IsField (M.S.presheaf.stalk (M.gp.base x)) := by
    rw [hx]; exact Field.toIsField _
  letI : Field (M.S.presheaf.stalk (M.gp.base x)) := hF.toField
  unfold RingHom.Flat
  exact inferInstance

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointFlatOfModificationOfDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPoint_flat_of_modification_of_domain : ∀ (R : Type) [CommRing R] [IsDomain R] (M : GlobalTheory.Mum.Modif R), Flat M.gp := by
  first | exact @GlobalTheory.Mum.Modif.flat_gp | exact GlobalTheory.Mum.Modif.flat_gp | (intros; apply GlobalTheory.Mum.Modif.flat_gp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFiniteTypeIntOfModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFiniteTypeIntOfModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.RatModel.exists_affineOpen_finiteType_int : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), ∃ U : M.Z.Opens, IsAffineOpen U ∧ x ∈ U ∧ Algebra.FiniteType ℤ Γ(M.Z, U) := by
  intro o' Ω _ _ _ hB M x
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp M.Z.isBasis_affineOpens) (show x ∈ (⊤ : M.Z.Opens) from trivial)
  refine ⟨U, hU, hxU, ?_⟩
  have hl := M.lft
  have h1 : (M.s.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType M.s hl ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of o')).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of o')).commRingCatIsoToRingEquiv.symm.surjective
  have h3 : (Int.castRingHom o').FiniteType := by
    have h := hB.ft
    rw [← RingHom.finiteType_algebraMap] at h
    convert h
  have h4 := (h1.comp h2).comp h3
  have he : algebraMap ℤ Γ(M.Z, U) = ((M.s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of o')).inv.hom).comp (Int.castRingHom o') := RingHom.ext_int _ _
  rw [← RingHom.finiteType_algebraMap, he]
  exact h4
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFiniteTypeIntOfModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_finiteType_int_of_model : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), ∃ U : M.Z.Opens, IsAffineOpen U ∧ x ∈ U ∧ Algebra.FiniteType ℤ Γ(M.Z, U) := by
  first | exact @GlobalTheory.RatModel.exists_affineOpen_finiteType_int | exact GlobalTheory.RatModel.exists_affineOpen_finiteType_int | (intros; apply GlobalTheory.RatModel.exists_affineOpen_finiteType_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFieldOfFieldPointsSamePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFieldOfFieldPointsSamePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_common_field_of_point_eq : ∀ (X : Scheme.{0}) (K₁ K₂ : Type) [Field K₁] [Field K₂] (a : Sp K₁ ⟶ X) (b : Sp K₂ ⟶ X), a (closedPoint K₁) = b (closedPoint K₂) → ∃ (Ω : Type) (_ : Field Ω) (i₁ : K₁ →+* Ω) (i₂ : K₂ →+* Ω), spMap i₁ ≫ a = spMap i₂ ≫ b := by
  intro X K₁ K₂ _ _ a b h
  obtain ⟨⟨x, f⟩, rfl⟩ := (Scheme.SpecToEquivOfField K₁ X).symm.surjective a
  obtain ⟨⟨y, g⟩, rfl⟩ := (Scheme.SpecToEquivOfField K₂ X).symm.surjective b
  have hxy : x = y := by
    have h1 := congrArg Sigma.fst ((Scheme.SpecToEquivOfField K₁ X).apply_symm_apply ⟨x, f⟩)
    have h2 := congrArg Sigma.fst ((Scheme.SpecToEquivOfField K₂ X).apply_symm_apply ⟨y, g⟩)
    exact h1.symm.trans (h.trans h2)
  subst hxy
  letI : Algebra (X.residueField x) K₁ := f.hom.toAlgebra
  letI : Algebra (X.residueField x) K₂ := g.hom.toAlgebra
  haveI : Nontrivial (TensorProduct (X.residueField x) K₁ K₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct (X.residueField x) K₁ K₂)
  letI : Field ((TensorProduct (X.residueField x) K₁ K₂) ⧸ m) := Ideal.Quotient.field m
  refine ⟨(TensorProduct (X.residueField x) K₁ K₂) ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := X.residueField x) (A := K₁) (B := K₂)).toRingHom, ?_⟩
  change Spec.map _ ≫ Spec.map f ≫ X.fromSpecResidueField x = Spec.map _ ≫ Spec.map g ≫ X.fromSpecResidueField x
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext c
  change Ideal.Quotient.mk m (TensorProduct.tmul _ (algebraMap _ K₁ c) 1) = Ideal.Quotient.mk m (TensorProduct.tmul _ 1 (algebraMap _ K₂ c))
  congr 1
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFieldOfFieldPointsSamePointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_field_of_fieldPoints_same_point : ∀ (X : Scheme.{0}) (K₁ K₂ : Type) [Field K₁] [Field K₂] (a : Sp K₁ ⟶ X) (b : Sp K₂ ⟶ X), a (closedPoint K₁) = b (closedPoint K₂) → ∃ (Ω : Type) (_ : Field Ω) (i₁ : K₁ →+* Ω) (i₂ : K₂ →+* Ω), spMap i₁ ≫ a = spMap i₂ ≫ b := by
  first | exact @GlobalTheory.Mum.exists_common_field_of_point_eq | exact GlobalTheory.Mum.exists_common_field_of_point_eq | (intros; apply GlobalTheory.Mum.exists_common_field_of_point_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemFrobeniusKernelOfVerschiebungEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemFrobeniusKernelOfVerschiebungEqZero
set_option autoImplicit false

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

namespace GlobalTheory.PDivGroup

theorem mulP_mem_kerIdeal_of_verschiebung_eq_zero (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (a : G.A 1) (ha : (verschiebung h G).app 1 a = 0) :
    G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp ((relFrob h G).app 1)) := by
  let f := (G.mulP 1).comp ((relFrob h G).app 1)
  let K := kerIdeal f
  let x := Ideal.Quotient.mkₐ R K
  have hx := (kerIdeal_le_ker_iff f x).1
    fun c hc => Ideal.Quotient.eq_zero_iff_mem.2 hc
  let y := x.comp ((relFrob h G).app 2 : (frobTwist h G).A 2 →ₐ[R] G.A 2)
  have hy : torsionIdeal (R := R) (A := (frobTwist h G).A 2) p ≤ RingHom.ker y :=
    (kerIdeal_le_ker_iff (mulBy R ((frobTwist h G).A 2) p) y).2 fun z => by
      change x ((relFrob h G).app 2 (mulBy R ((frobTwist h G).A 2) p z)) = _
      rw [← (frobTwist h G).mulP_res 1 z, PDivGroup.app_mulP (relFrob h G)]
      simpa only [f, BialgHom.coe_comp, Function.comp_apply, CoalgHomClass.counit_comp_apply]
        using hx ((frobTwist h G).res 1 z)
  obtain ⟨b, rfl⟩ := G.res_surjective 1 a
  rw [← PDivGroup.res_app (verschiebung h G)] at ha
  have hb : (verschiebung h G).app 2 b ∈ torsionIdeal (R := R) (A := (frobTwist h G).A 2) p := by
    have : (verschiebung h G).app 2 b ∈ torsionIdeal (R := R) (A := (frobTwist h G).A 2) (p ^ 1) := by
      rw [← (frobTwist h G).ker_res 1]
      exact ha
    rwa [pow_one] at this
  have h1 : x ((relFrob h G).app 2 ((verschiebung h G).app 2 b)) = 0 := hy hb
  rw [relFrob_app_verschiebung_app] at h1
  rw [mulP_res]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

end GlobalTheory.PDivGroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemFrobeniusKernelOfVerschiebungEqZeroStatement
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
      (G : PDivGroup p R) (a : G.A 1),
      (verschiebung h G).app 1 a = 0 →
        G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp ((relFrob h G).app 1)) :=
  @GlobalTheory.PDivGroup.mulP_mem_kerIdeal_of_verschiebung_eq_zero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftReductionStandardFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftReductionStandardFacts
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

theorem abelianLift_facts : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → AllPrim (dp0 R) (𝟙 _) A' ∧ AllPrim (dp0 R₀) (𝟙 _) A₀ ∧ AllPrim (divided₂ hI) (spMap π) A₀ ∧ Function.Bijective (liftMor (divided₂ hI) h').pull ∧ Module.Finite R (Cr hI π A₀.hom) ∧ Module.Projective R (Cr hI π A₀.hom) ∧ IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension g A₀.hom := by
  intro H1 H2 R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg
  have F : AbelianDeRham.Free :=
    GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.Proof.abelianDeRhamFree_of_hodge H1 H2)
  have C : CrystallineDeRham := H1.toCrystallineDeRham
  have Rg : AbelianDeRham.Rigid := AbelianDeRham.rigid_of_free_of_crystallineDeRham F C
  have hA₀ : IsAbelianScheme A₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h'
  have hg₀ : SmoothOfRelativeDimension g A₀.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h'.1 hg
  have p' : AllPrim (dp0 R) (𝟙 _) A' := (F R A' g hA hg).1
  have p₀ : AllPrim (dp0 R₀) (𝟙 _) A₀ := (F R₀ A₀ g hA₀ hg₀).1
  have hκ : IsNilDP (divided₂ hI) := isDPNilpotent_squareZero hI
  have bij := Rg R A' g hA hg I (divided₂ hI) hκ R₀ π hπ hk A₀ i' h'
  have := hA.smooth
  have := hA.proper
  obtain ⟨b₁, -⟩ := C R I (divided₂ hI) hκ R₀ π hπ hk A'.left A₀.left (A'.hom ≫ 𝟙 _) A₀.hom i' inferInstance
    inferInstance inferInstance (by rw [Category.comp_id]; exact h'.1) (liftMor (divided₂ hI) h').isMor
  have pc : AllPrim (divided₂ hI) (spMap π) A₀ := by
    refine Submodule.eq_top_iff'.2 fun c ↦ ?_
    obtain ⟨c', rfl⟩ := b₁.2 c
    have hc' : c' ∈ prim (dp0 R) (𝟙 _) A' := by rw [show prim (dp0 R) (𝟙 _) A' = ⊤ from p']; trivial
    exact (liftMor (divided₂ hI) h').pullback_mem_primitive hc'
  let e := LinearEquiv.ofBijective (liftMor (divided₂ hI) h').isMor.pull1 b₁
  have fin : Module.Finite R (FirstDeRham (A'.hom ≫ 𝟙 _)) := (F R A' g hA hg).2.1
  have proj : Module.Projective R (FirstDeRham (A'.hom ≫ 𝟙 _)) := (F R A' g hA hg).2.2.1
  exact ⟨p', p₀, pc, bij, Module.Finite.equiv e, Module.Projective.of_equiv e, hA₀, hg₀⟩

end GlobalTheory.LiftSys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftReductionStandardFactsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianLift_reduction_standard_facts : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → AllPrim (dp0 R) (𝟙 _) A' ∧ AllPrim (dp0 R₀) (𝟙 _) A₀ ∧ AllPrim (divided₂ hI) (spMap π) A₀ ∧ Function.Bijective (liftMor (divided₂ hI) h').pull ∧ Module.Finite R (Cr hI π A₀.hom) ∧ Module.Projective R (Cr hI π A₀.hom) ∧ IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension g A₀.hom := by
  first | exact @GlobalTheory.LiftSys.abelianLift_facts | exact GlobalTheory.LiftSys.abelianLift_facts | (intros; apply GlobalTheory.LiftSys.abelianLift_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelSectionsLinearRingOfIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelSectionsLinearRingOfIntegers
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModel

theorem sec_linear : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ∀ i : L.B.ι, (s x).f i = ∑ k, ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (L.B.U i) (β k) * (s (u k)).f i := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev m β u x hx i
  have hw : ∃ w' : W, ev w' ≠ 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨N, n, b, g, A, c, gw, -, -, hb, -⟩ := hM.fs
    exact hev (b.ext fun j => by rw [hb j, map_sum]; simp [map_smul, hne])
  obtain ⟨w', hw'⟩ := hw
  apply GlobalTheory.Cartier.fn_ext
  intro hU
  have ha : ψ (ev w') ≠ 0 := (map_ne_zero ψ).mpr hw'
  have hr : ∀ y : W, ψ (ev w') * GlobalTheory.Cartier.fnOf _ hU ((s y).f i) =
      ψ (ev y) * GlobalTheory.Cartier.fnOf _ hU ((s w').f i) := fun y => (hM.ratio y w' i hU).symm
  have hc : ∀ b : 𝓞 K, GlobalTheory.Cartier.fnOf _ hU (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (L.B.U i) b) =
      ψ (algebraMap K Ω (b : K)) := by
    intro b
    rw [hM.base]
    exact RingHom.congr_fun (GlobalTheory.Cartier.fnOf_comp_algX p _ hU) b
  have hex : ψ (ev x) = ∑ k, ψ (algebraMap K Ω (β k : K)) * ψ (ev (u k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← IsScalarTower.algebraMap_smul K (β k) (u k : V), map_smul, Algebra.smul_def, map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_mul, hc]
  apply mul_left_cancel₀ ha
  rw [hr x, hex, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm (ψ (ev w')), hr (u k), mul_assoc]

end GlobalTheory.ImageModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelSectionsLinearRingOfIntegersStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.imageModel_sections_linear_ringOfIntegers : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ∀ i : L.B.ι, (s x).f i = ∑ k, ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (L.B.U i) (β k) * (s (u k)).f i := by
  first | exact @GlobalTheory.ImageModel.sec_linear | exact GlobalTheory.ImageModel.sec_linear | (intros; apply GlobalTheory.ImageModel.sec_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToProjSecPullOfSval
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem toProj_secPull_of_gs {R : Type} [CommRing R] {Y Y' Z : Scheme.{0}} [Subsingleton Z] {A : LB Y} {A' : LB Y'}
    {N : ℕ} (σ : Fin (N + 1) → A.Sec) (τ : Fin (N + 1) → A'.Sec) (s : Y' ⟶ Sp R)
    (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) (p : Z ⟶ Y) (y : Z ⟶ Y')
    (H : ∀ z : Z, ∃ (a : A.ι) (a' : A'.ι) (c : (Z.presheaf.stalk z)ˣ), p z ∈ A.U a ∧ y z ∈ A'.U a' ∧
      ∀ i, gs p z _ ((σ i).f a) = c.val * gs y z _ ((τ i).f a')) :
    (∀ i (z : Z), p z ∈ nonzeroLocus (σ i) ↔ y z ∈ nonzeroLocus (τ i)) ∧
      ∃ hs, GlobalTheory.ProjSpace.toProj (y ≫ s) (fun i => GlobalTheory.secPull (σ i) p) hs = y ≫ GlobalTheory.ProjSpace.toProj s τ hτ := by
  have h1 : ∀ i (z : Z), p z ∈ nonzeroLocus (σ i) ↔ y z ∈ nonzeroLocus (τ i) := by
    intro i z
    obtain ⟨a, a', c, ha, ha', e⟩ := H z
    rw [GlobalTheory.mem_nonzeroLocus_iff_pull (σ i) p z ha, GlobalTheory.mem_nonzeroLocus_iff_pull (τ i) y z ha', e i,
      IsUnit.mul_iff]
    exact ⟨fun h => h.2, fun h => ⟨c.isUnit, h⟩⟩
  have hs : ⨆ i, nonzeroLocus (GlobalTheory.secPull (σ i) p) = ⊤ := by
    refine top_le_iff.1 fun z _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hτ.ge (Set.mem_univ (y z)))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (GlobalTheory.nonzeroLocus_secPull (σ i) p).ge ((h1 i z).2 hi)⟩
  refine ⟨h1, hs, GlobalTheory.ProjSpace.toProj_eq_comp_of_locally hτ y hs fun z => ?_⟩
  obtain ⟨a, a', c, ha, ha', e⟩ := H z
  obtain ⟨W, hW, u, hu⟩ := Z.presheaf.exists_germ_eq c.val
  have hall : ∀ {U : Z.Opens}, z ∈ U → W ≤ U := fun hU x _ => (Subsingleton.elim z x) ▸ hU
  have hl : z ∈ (A.pull p).U fun _ => a := Set.mem_iInter.2 fun _ => ha
  refine ⟨W, hW, a', hall ha', fun _ => a, hall hl, u, fun j => fn_ext fun x hx => ?_⟩
  obtain rfl : z = x := Subsingleton.elim _ _
  have e₁ : gs (𝟙 Z) z W (resG Z (hall hl) ((GlobalTheory.secPull (σ j) p).f fun _ => a)) = gs p z _ ((σ j).f a) :=
    (gs_res (𝟙 Z) z (hall hl) hW _).trans
      ((GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull A p) (σ j) (𝟙 Z) z (fun _ => a) hl).trans (by rw [Category.id_comp]; rfl))
  have e₂ : gs (𝟙 Z) z W u = c.val := (gs_eq (𝟙 Z) z W hW u).trans hu
  have e₃ : gs (𝟙 Z) z W ((y.appLE _ W (hall ha')).hom ((τ j).f a')) = gs y z _ ((τ j).f a') :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_appLE y _ _ _ (𝟙 Z) z hW _).trans (by rw [Category.id_comp])
  rw [e₁, gs_mul (𝟙 Z) z W hW, e₂, e₃, e j]

theorem toProj_secPull_of_sval : ∀ (R Ω : Type) [CommRing R] [Field Ω] (X X' Y Y' : Scheme.{0}) (L : LB X) (L' : LB X') (h : Y ⟶ X) (h' : Y' ⟶ X') (k N : ℕ) (σ : Fin (N + 1) → SecK L h k) (τ : Fin (N + 1) → SecK L' h' k) (s : Y' ⟶ Sp R) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) (p : Sp Ω ⟶ Y) (y : Sp Ω ⟶ Y'), L.IsLB → L'.IsLB → (∀ z J J', Good L z J → Good L' z J' → ∃ c : ((Sp Ω).presheaf.stalk z)ˣ, ∀ i, sval (σ i) p z J = c.val * sval (τ i) y z J') → (∀ i (z : Sp Ω), p z ∈ nonzeroLocus (σ i) ↔ y z ∈ nonzeroLocus (τ i)) ∧ ∃ hs, GlobalTheory.ProjSpace.toProj (y ≫ s) (fun i => GlobalTheory.secPull (σ i) p) hs = y ≫ GlobalTheory.ProjSpace.toProj s τ hτ := by
  intro R Ω _ _ X X' Y Y' L L' h h' k N σ τ s hτ p y hL hL' H
  haveI : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  refine toProj_secPull_of_gs σ τ s hτ p y fun z => ?_
  choose J hJ using fun χ : Sp Ω ⟶ X => exists_chart hL (χ z)
  choose J' hJ' using fun χ : Sp Ω ⟶ X' => exists_chart hL' (χ z)
  obtain ⟨c, hc⟩ := H z J J' hJ hJ'
  exact ⟨_, _, c, Good.mem hJ _ p, Good.mem hJ' _ y, hc⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLabAlt
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {cf : Coeff l} {C : UCompact Xo cf} {X₁ : USetup C}

def UDeep.GalLab (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (a : D.X.S.Gam ≃+ D.X.S.Gam) : Prop :=
  ∃ (P₀ : PolAV (Sp D.X.Ω₁)) (b : P₀.A.left ⟶ D.X.ρ.P.A.left) (t : P₀.A.left ⟶ P₀.A.left),
    IsGrpPullback P₀.A D.X.ρ.P.A (spMap D.X.S.R.val.toRingHom) b ∧
    IsGrpPullback P₀.A P₀.A (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) t ∧
    LBIso P₀.L (D.X.ρ.P.L.pull b) ∧ LBIso P₀.L (P₀.L.pull t) ∧
    ∀ x (w w' : Sp D.X.Ω₁ ⟶ P₀.A.left), w ≫ b = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left →
      w' ≫ t = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ w →
        w' ≫ b = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt (a x)).left

end GlobalTheory.UPoinc
end
end
