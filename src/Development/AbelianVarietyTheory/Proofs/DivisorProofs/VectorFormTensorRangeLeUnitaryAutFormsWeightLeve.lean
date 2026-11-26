module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedVectorFormValuesMemISupFixedParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedVectorFormValuesMemISupFixedParts
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FrameAut.VecSemis

open GlobalTheory.UnitarySemisimple

theorem exists_irred_le_orbSpan {H V : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ H V) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hh : ∀ u v, star (B u v) = B v u)
    (hp : ∀ v, 0 ≤ (B v v).re) (hd : ∀ v, B v v = 0 → v = 0) (hi : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hK0 : ∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H))
    (hsm : ∀ w, IsOpen {k : H | ρ k w = w})
    (hfd : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K))
    (y : V) (hy : y ≠ 0) :
    ∃ U : Submodule ℂ V, U ≠ ⊥ ∧ U ≤ (orbSpan ρ y).toSubmodule ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧
      (∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U) := by
  classical
  set O := orbSpan ρ y with hO
  let ρO := O.toRepresentation
  have hρO : ∀ g (w : O.toSubmodule), (ρO g w : V) = ρ g w := fun _ _ => rfl
  let BO : O.toSubmodule →ₗ⋆[ℂ] O.toSubmodule →ₗ[ℂ] ℂ := (B.comp O.toSubmodule.subtype).compl₂ O.toSubmodule.subtype
  have hBO : ∀ u w : O.toSubmodule, BO u w = B u w := fun _ _ => rfl
  have hsmO : ∀ w : O.toSubmodule, IsOpen {k : H | ρO k w = w} := by
    intro w
    convert hsm w.1 using 1
    ext k
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => by rw [← hρO, h], fun h => Subtype.ext (by rw [hρO, h])⟩
  have hfdO : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρO K) := by
    intro K hK
    haveI := hfd K hK
    have hle : (GlobalTheory.PRep.fixed ρO K).map O.toSubmodule.subtype ≤ GlobalTheory.PRep.fixed ρ K := by
      rintro _ ⟨w, hw, rfl⟩ k
      have h1 := hw k
      show ρ k w.1 = ((1 : K →* ℂˣ) k : ℂ) • w.1
      rw [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
      rw [← hρO, h1]
    haveI : FiniteDimensional ℂ ((GlobalTheory.PRep.fixed ρO K).map O.toSubmodule.subtype) :=
      Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective _ O.toSubmodule.injective_subtype _).symm
  have hy0 : (⟨y, mem_orbSpan ρ y⟩ : O.toSubmodule) ≠ 0 := fun h => hy (congrArg Subtype.val h)
  obtain ⟨U', P, hU0, hUst, hUirr, -, -, -⟩ :=
    GlobalTheory.AdmissibleProjection.exists_irreducible_equivariant_projection H O.toSubmodule ρO BO
      (fun u w => hh u w) (fun v => hp v) (fun v h => Subtype.ext (hd v h)) (fun g u w => hi g u w)
      hK0 hsmO hfdO _ hy0
  refine ⟨U'.map O.toSubmodule.subtype, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hU0
    rw [Submodule.eq_bot_iff]
    intro u hu
    have : u.1 ∈ U'.map O.toSubmodule.subtype := ⟨u, hu, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · rintro g _ ⟨u, hu, rfl⟩
    exact ⟨ρO g u, hUst g u hu, rfl⟩
  · intro N hNU hN
    let N' : Submodule ℂ O.toSubmodule := N.comap O.toSubmodule.subtype
    have hN'U : N' ≤ U' := by
      intro u hu
      obtain ⟨w, hw, hwu⟩ := hNU hu
      rw [← Subtype.ext hwu]
      exact hw
    have hN'st : ∀ g, ∀ u ∈ N', ρO g u ∈ N' := fun g u hu => hN g u.1 hu
    have hNe : N'.map O.toSubmodule.subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hNU.trans (Submodule.map_subtype_le _ _))
    rcases hUirr N' hN'U hN'st with h | h
    · left; rw [← hNe, h, Submodule.map_bot]
    · right; rw [← hNe, h]

end GlobalTheory.FrameAut.VecSemis

namespace GlobalTheory.FrameAut.VecSemis

open GlobalTheory.UnitarySemisimple GlobalTheory.DefU GlobalTheory.FrameAut.VecProj

theorem mem_iSup_of_form (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (hh : ∀ u v, star (B u v) = B v u) (hp : ∀ v, 0 ≤ (B v v).re)
    (hd : ∀ v, B v v = 0 → v = 0) (hi : ∀ g u v, B (autRep E n g u) (autRep E n g v) = B u v)
    (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (infU E n) W)
    (hsp : Submodule.span ℂ (Set.range ρ) = ⊤) (K : Subgroup (finU (E := E) (n := n))) (hK : IsOpen (K : Set (finU (E := E) (n := n))))
    (f : W →ₗ[ℂ] (UA E n → ℂ)) (hfa : ∀ u, IsAutFormU (f u)) (hfe : ∀ (x : infU E n) u, f (ρ x u) = RU E n x (f u))
    (hfK : ∀ u, f u ∈ fixed (RF E n) K) :
    ∀ u, f u ∈ ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧
      (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)), π ⊓ fixed (RF E n) K := by
  classical
  set T : Submodule ℂ (UA E n → ℂ) := ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧
    ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)),
    π ⊓ fixed (RF E n) K with hT
  let Y : Submodule ℂ (forms ρ) :=
    { carrier := {g | ∀ u, g.1 u ∈ T}
      add_mem' := fun ha hb u => by
        rw [Submodule.coe_add, LinearMap.add_apply]; exact add_mem (ha u) (hb u)
      zero_mem' := fun u => by simp
      smul_mem' := fun c g hg u => by
        rw [Submodule.coe_smul, LinearMap.smul_apply]; exact T.smul_mem c (hg u) }
  let X := GlobalTheory.PRep.fixed (rep ρ) K
  haveI : FiniteDimensional ℂ X := rep_fd ρ K hK
  haveI : FiniteDimensional ℂ (X ⊓ Y : Submodule ℂ (forms ρ)) := Submodule.finiteDimensional_of_le inf_le_left
  let Bf := form B ρ
  have hBh := form_herm B hh ρ
  have hBp := form_nonneg B hp ρ
  have hBd := form_def B hh hp hd ρ
  have hBi := form_inv B hi ρ
  have memX : ∀ g : forms ρ, (∀ k ∈ K, rep ρ k g = g) → g ∈ X := by
    intro g hg k
    show rep ρ k g = ((1 : K →* ℂˣ) k : ℂ) • g
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact hg k k.2
  have ofX : ∀ g ∈ X, ∀ k ∈ K, rep ρ k g = g := by
    intro g hg k hk
    have h1 := hg ⟨k, hk⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at h1
    exact h1
  have hfA : f ∈ forms ρ := ⟨fun v => hfa v, hfe⟩
  let ff : forms ρ := ⟨f, hfA⟩
  have hffX : ff ∈ X := by
    refine memX ff fun k hk => Subtype.ext (LinearMap.ext fun u => ?_)
    have h1 := hfK u ⟨k, hk⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at h1
    exact h1
  suffices hY : ff ∈ Y from hY
  by_contra hffY
  obtain ⟨m, hm, hmo⟩ := exists_orth_proj Bf hBd (X ⊓ Y) ff
  obtain ⟨y, hy⟩ : ∃ y, y = ff - m := ⟨_, rfl⟩
  have hyX : y ∈ X := hy ▸ sub_mem hffX (Submodule.mem_inf.1 hm).1
  have hy0 : y ≠ 0 := by
    intro h
    apply hffY
    rw [hy, sub_eq_zero] at h
    rw [h]
    exact (Submodule.mem_inf.1 hm).2
  obtain ⟨U, hU0, hUO, hUst, hUirr⟩ := exists_irred_le_orbSpan (rep ρ) Bf hBh hBp hBd hBi (GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact E n)
    (rep_smooth ρ) (rep_fd ρ) y hy0
  have hadm := GlobalTheory.AdmissibleProjection.hadm_of (rep ρ) (GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact E n) (rep_smooth ρ) (rep_fd ρ)
  let Z : Subrepresentation (rep ρ) := ⟨U, fun g _ hv => hUst g _ hv⟩
  obtain ⟨P, hP1, hP2, hP3⟩ := GlobalTheory.AdmissibleProjection.exists_proj (rep ρ) Bf hBd hBi hadm Z
  obtain ⟨z, hz⟩ : ∃ z, z = P y := ⟨_, rfl⟩
  have hzU : z ∈ U := hz ▸ hP1 y
  have hzX : z ∈ X := memX z fun k hk => by rw [hz, ← hP3, ofX y hyX k hk]
  have hz0 : z ≠ 0 := by
    intro h0
    apply hU0
    have hyo : ∀ w ∈ Z.toSubmodule, Bf w y = 0 := by
      intro w hw
      have := hP2 y w hw
      rwa [← hz, h0, sub_zero] at this
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hle : (orbSpan (rep ρ) y).toSubmodule ≤ LinearMap.ker (Bf w) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      exact orth_stable (rep ρ) Bf hBi Z y hyo g w hw
    exact hBd _ (hle (hUO hw))

  let M : Submodule ℂ (W →ₗ[ℂ] (UA E n → ℂ)) := U.map (forms ρ).subtype
  have hM0 : M ≠ ⊥ := by
    intro h
    apply hU0
    rw [Submodule.eq_bot_iff]
    intro u hu
    have : u.1 ∈ M := ⟨u, hu, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  have hMf : ∀ g ∈ M, (∀ v, IsAutFormU (g v)) ∧ ∀ (x : infU E n) v, g (ρ x v) = RU E n x (g v) := by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨fun v => u.2.1 v, u.2.2⟩
  have hMk : ∀ k ∈ finU (E := E) (n := n), ∀ g ∈ M, (RU E n k) ∘ₗ g ∈ M := by
    rintro k hk _ ⟨u, hu, rfl⟩
    exact ⟨rep ρ ⟨k, hk⟩ u, hUst _ u hu, rfl⟩
  have hMirr : ∀ N ≤ M, (∀ k ∈ finU (E := E) (n := n), ∀ g ∈ N, (RU E n k) ∘ₗ g ∈ N) → N = ⊥ ∨ N = M := by
    intro N hNM hN
    let N' : Submodule ℂ (forms ρ) := N.comap (forms ρ).subtype
    have hN'U : N' ≤ U := by
      intro u hu
      obtain ⟨w, hw, hwu⟩ := hNM hu
      rw [← Subtype.ext hwu]
      exact hw
    have hN'st : ∀ g, ∀ u ∈ N', rep ρ g u ∈ N' := fun g u hu => hN g.1 g.2 u.1 hu
    have hNe : N'.map (forms ρ).subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hNM.trans (Submodule.map_subtype_le _ _))
    rcases hUirr N' hN'U hN'st with h | h
    · left; rw [← hNe, h, Submodule.map_bot]
    · right; rw [← hNe, h]
  have hπ := GlobalTheory.FrameAut.VecForms.isAutRepU_span_values E n W ρ hsp M hM0 hMf hMk hMirr
  have hzY : z ∈ Y := by
    intro u
    have hmemπ : z.1 u ∈ Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ} :=
      Submodule.subset_span ⟨z.1, ⟨z, hzU, rfl⟩, u, rfl⟩
    have hfixu : z.1 u ∈ fixed (RF E n) K := by
      intro k
      rw [MonoidHom.one_apply, Units.val_one, one_smul]
      have h1 := congrArg (fun g : forms ρ => g.1 u) (ofX z hzX k k.2)
      exact h1
    have hidx : IsAutRepU (Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ}) ∧
        ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ}) ∧
          ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u) :=
      ⟨hπ, z.1, fun h => hz0 (Subtype.ext h), fun v => Submodule.subset_span ⟨z.1, ⟨z, hzU, rfl⟩, v, rfl⟩, z.2.2⟩
    exact (le_iSup₂ (f := fun (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧
      ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)) =>
      π ⊓ fixed (RF E n) K) _ hidx) ⟨hmemπ, hfixu⟩
  have hzm : Bf z y = 0 := hy ▸ hmo z ⟨hzX, hzY⟩
  have hzz : Bf z z = 0 := by
    have h2 := hP2 y z hzU
    rw [← hz, map_sub, hzm, zero_sub, neg_eq_zero] at h2
    exact h2
  exact hz0 (hBd z hzz)

end GlobalTheory.FrameAut.VecSemis

namespace GlobalTheory.FrameAut.VecSemis

open GlobalTheory.DefU

theorem mem_iSup_fixed_autRep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (infU E n) W), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ (K : Subgroup (finU (E := E) (n := n))), IsOpen (K : Set (finU (E := E) (n := n))) → ∀ f : W →ₗ[ℂ] (UA E n → ℂ), (∀ u, IsAutFormU (f u)) → (∀ (x : infU E n) u, f (ρ x u) = RU E n x (f u)) → (∀ u, f u ∈ fixed (RF E n) K) → ∀ u, f u ∈ ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)), π ⊓ fixed (RF E n) K := by
  intro E _ _ _ n W _ _ _ ρ hsp K hK f hfa hfe hfK
  obtain ⟨B, hh, hp, hd, hi⟩ := GlobalTheory.T.exists_invariant_positive_petersson_form E n
  exact mem_iSup_of_form E n B hh hp hd hi W ρ hsp K hK f hfa hfe hfK

end GlobalTheory.FrameAut.VecSemis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedVectorFormValuesMemISupFixedPartsStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedVectorForm_values_mem_iSup_fixedParts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (infU E n) W), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ (K : Subgroup (finU (E := E) (n := n))), IsOpen (K : Set (finU (E := E) (n := n))) → ∀ f : W →ₗ[ℂ] (UA E n → ℂ), (∀ u, IsAutFormU (f u)) → (∀ (x : infU E n) u, f (ρ x u) = RU E n x (f u)) → (∀ u, f u ∈ fixed (RF E n) K) → ∀ u, f u ∈ ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)), π ⊓ fixed (RF E n) K := by
  first | exact @GlobalTheory.FrameAut.VecSemis.mem_iSup_fixed_autRep | exact GlobalTheory.FrameAut.VecSemis.mem_iSup_fixed_autRep | (intros; apply GlobalTheory.FrameAut.VecSemis.mem_iSup_fixed_autRep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRealPointsWeightRepresentationEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRealPointsWeightRepresentationEqTop
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

theorem span_range_wInf_comp_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (lam : InfinitePlace E → DomWeight n),
    Submodule.span ℂ (Set.range ((wInf lam).comp (infU E n).subtype)) = ⊤ := by
  intro E _ _ _ n lam
  exact span_wInf lam

end GlobalTheory.BCT.TrKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRealPointsWeightRepresentationEqTopStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_realPoints_weightRepresentation_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n), Submodule.span ℂ (Set.range ((wInf lam).comp (infU E n).subtype)) = ⊤ := by
  first | exact @GlobalTheory.BCT.TrKer.span_range_wInf_comp_infU | exact GlobalTheory.BCT.TrKer.span_range_wInf_comp_infU | (intros; apply GlobalTheory.BCT.TrKer.span_range_wInf_comp_infU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryRationalPointSplitFiniteInfinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryRationalPointSplitFiniteInfinite
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.RatSplit

theorem ratU_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ γ ∈ ratU E n,
    ∃ γ₀ : UE E n, splitFin E n γ = finPt γ₀ ∧
      ∀ v : InfinitePlace E, cEmb v.embedding γ = GeneralLinearGroup.map v.embedding γ₀.1 := by
  intro E _ _ _ n γ hγ
  obtain ⟨g0, hg0⟩ := (Subgroup.mem_subgroupOf.1 hγ : γ.1 ∈ (ratGL E n).range)
  have hval : γ.1.val = g0.val.map (algebraMap E (Ad E)) := by rw [← hg0]; rfl

  have hU : g0 ∈ UE E n := by
    have h2 : cT (conjAd E) γ.1.val * 1 * γ.1.val = 1 := γ.2
    show cT (IsCMField.complexConj E).toRingEquiv.toRingHom g0.val * 1 * g0.val = 1
    have hinj : Function.Injective (algebraMap E (Ad E)) := by
      intro x y hxy
      have τ := (Classical.arbitrary (InfinitePlace E)).embedding
      exact τ.injective (by rw [← coord_algebraMap τ x, ← coord_algebraMap τ y, hxy])
    apply Matrix.map_injective hinj
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul,
      FinPtLoc.map_cT (algebraMap E (Ad E)) _ (conjAd E) (fun x => (conjAd_algebraMap x).symm),
      Matrix.map_one _ (map_zero _) (map_one _), ← hval, h2]
  refine ⟨⟨g0, hU⟩, ?_, ?_⟩
  · set a : finU (E := E) (n := n) := finPt ⟨g0, hU⟩ with ha
    have haval : ((a : UA E n) : GA E n) = finGL E n (ratF E n g0) := by
      rw [ha, FinPtLoc.finPt_eq]
    have hb : (a : UA E n)⁻¹ * γ ∈ infU E n := by
      show GeneralLinearGroup.map (pFin E) (((a : UA E n)⁻¹ * γ : UA E n) : GA E n) = 1
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, haval, pFin_finGL, ← hg0]
      have : GeneralLinearGroup.map (pFin E) (ratGL E n g0) = ratF E n g0 := by
        apply Units.ext; ext i j; rfl
      rw [this, inv_mul_cancel]
    have hγs : γ = (a : UA E n) * ((⟨_, hb⟩ : infU E n) : UA E n) := by
      simp
    rw [hγs, splitFin_mul]
  · intro v
    apply Units.ext
    ext i j
    change coord v.embedding (pInf E (γ.1.val i j)) = v.embedding (g0.val i j)
    rw [hval, Matrix.map_apply, coord_algebraMap]

end GlobalTheory.BCT.RatSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryRationalPointSplitFiniteInfiniteStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryRationalPoint_split_finite_infinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ γ ∈ ratU E n, ∃ γ₀ : UE E n, splitFin E n γ = finPt γ₀ ∧ ∀ v : InfinitePlace E, cEmb v.embedding γ = GeneralLinearGroup.map v.embedding γ₀.1 := by
  first | exact @GlobalTheory.BCT.RatSplit.ratU_split | exact GlobalTheory.BCT.RatSplit.ratU_split | (intros; apply GlobalTheory.BCT.RatSplit.ratU_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFormTensorRangeLeUnitaryAutFormsWeightLeve
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer.RangeLe

theorem contW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n) (u : Wsp lam) (ℓ : Module.Dual ℂ (Wsp lam)), Continuous fun g : UA E n => ℓ (wInf lam g u) := GlobalTheory.T.continuous_matrixCoeff_infinitePlacesWeightRep

theorem ratSplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ γ ∈ ratU E n, ∃ γ₀ : UE E n, splitFin E n γ = finPt γ₀ ∧ ∀ v : InfinitePlace E, cEmb v.embedding γ = GeneralLinearGroup.map v.embedding γ₀.1 := GlobalTheory.T.definiteUnitaryRationalPoint_split_finite_infinite

theorem spanW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n), Submodule.span ℂ (Set.range ((wInf lam).comp (infU E n).subtype)) = ⊤ := GlobalTheory.T.span_realPoints_weightRepresentation_eq_top

theorem semis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (infU E n) W), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ (K : Subgroup (finU (E := E) (n := n))), IsOpen (K : Set (finU (E := E) (n := n))) → ∀ f : W →ₗ[ℂ] (UA E n → ℂ), (∀ u, IsAutFormU (f u)) → (∀ (x : infU E n) u, f (ρ x u) = RU E n x (f u)) → (∀ u, f u ∈ fixed (RF E n) K) → ∀ u, f u ∈ ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)), π ⊓ fixed (RF E n) K := GlobalTheory.T.fixedVectorForm_values_mem_iSup_fixedParts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def dualW (lam : InfinitePlace E → DomWeight n) : UA E n →* Module.End ℂ (Module.Dual ℂ (Wsp lam)) where
  toFun g := (wInf lam g⁻¹).dualMap
  map_one' := by
    refine LinearMap.ext fun φ => LinearMap.ext fun w => ?_
    simp [LinearMap.dualMap_apply]
  map_mul' a b := by
    refine LinearMap.ext fun φ => LinearMap.ext fun w => ?_
    simp [LinearMap.dualMap_apply, _root_.mul_inv_rev, map_mul]

theorem dualW_apply (lam : InfinitePlace E → DomWeight n) (g : UA E n) (φ : Module.Dual ℂ (Wsp lam)) (w : Wsp lam) :
    dualW lam g φ w = φ (wInf lam g⁻¹ w) := rfl

theorem wInf_inv_rat (lam : InfinitePlace E → DomWeight n) (γ : UA E n) (γ₀ : UE E n)
    (h : ∀ v : InfinitePlace E, cEmb v.embedding γ = GeneralLinearGroup.map v.embedding γ₀.1) :
    wInf lam γ⁻¹ = wAt lam γ₀⁻¹ := by
  have e : ∀ v : InfinitePlace E, cEmb v.embedding γ⁻¹ = GeneralLinearGroup.map v.embedding (γ₀⁻¹ : UE E n).1 :=
    fun v => by rw [map_inv, h v, InvMemClass.coe_inv, map_inv]
  unfold wInf wAt
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, e]

theorem phiFun_wInf (lam : InfinitePlace E → DomWeight n) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (x : infU E n)
    (w : Wsp lam) : phiFun lam F (wInf lam x.1 w) = RU E n x.1 (phiFun lam F w) := by
  funext g
  change F (splitFin E n g) (wInf lam g (wInf lam x.1 w)) = F (splitFin E n (g * x.1)) (wInf lam (g * x.1) w)
  rw [map_mul (splitFin E n), splitFin_inf x, mul_one, map_mul (wInf lam), Module.End.mul_apply]

theorem phiFun_mem_fixed (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (hF : F ∈ vecM S lam K') (w : Wsp lam) :
    phiFun lam F w ∈ fixed (RF E n) (globLev S K') := by
  intro k
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  funext g
  change phiFun lam F w (g * ((k : finU (E := E) (n := n)) : UA E n)) = phiFun lam F w g
  rw [phiFun_mul_fin]
  have e : rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) (k : finU (E := E) (n := n)) F = F := funext fun x => hF.2 k k.2 x
  rw [e]

theorem isAutFormU_phiFun (hU : Unr E) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n)
    (K' : ∀ w : Pl E, Subgroup (UL n w)) (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K')
    (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (hF : F ∈ vecM S lam K') (w : Wsp lam) :
    IsAutFormU (phiFun lam F w) := by
  have hfin : ∀ k ∈ finU (E := E) (n := n), dualW lam k = 1 := by
    intro k hk
    refine LinearMap.ext fun φ => LinearMap.ext fun u => ?_
    rw [dualW_apply, wInf_fin lam ⟨k⁻¹, (finU (E := E) (n := n)).inv_mem hk⟩]
    rfl
  have hcont : ∀ (u : Module.Dual ℂ (Wsp lam)) (ℓ : Module.Dual ℂ (Module.Dual ℂ (Wsp lam))),
      Continuous fun g => ℓ (dualW lam g u) := by
    intro u ℓ
    obtain ⟨w', rfl⟩ := (Module.evalEquiv ℂ (Wsp lam)).surjective ℓ
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, dualW_apply]
    exact (contW E n lam w' u).comp continuous_inv
  have hinf : ∀ y ∈ infU E n, ∀ g, (fun g => F (splitFin E n g)) (g * y) = F (splitFin E n g) := by
    intro y hy g
    simp only [map_mul, splitFin_inf ⟨y, hy⟩, mul_one]
  have hrat : ∀ γ ∈ ratU E n, ∀ g, (fun g => F (splitFin E n g)) (γ * g) = dualW lam γ (F (splitFin E n g)) := by
    intro γ hγ g
    obtain ⟨γ₀, h1, h2⟩ := ratSplit E n γ hγ
    simp only [map_mul, h1]
    rw [hF.1 γ₀ (splitFin E n g)]
    refine LinearMap.ext fun u => ?_
    rw [dualW_apply, wInf_inv_rat lam γ γ₀ h2]
    rfl
  have hsm : ∀ᶠ y in 𝓝 (1 : UA E n), ∀ g, (fun g => F (splitFin E n g)) (g * y) = F (splitFin E n g) := by
    have ho : IsOpen ((splitFin E n) ⁻¹' (globLev S K' : Set (finU (E := E) (n := n)))) :=
      (isOpen_globLev E hU n S K' hK).preimage continuous_splitFin
    filter_upwards [ho.mem_nhds (by simp [(globLev S K').one_mem])] with y hy g
    simp only [map_mul]
    exact hF.2 _ hy _
  have h := GlobalTheory.EquivCoef.isAutFormU_coef E n (Module.Dual ℂ (Wsp lam)) (dualW lam) (fun g => F (splitFin E n g))
    hfin hcont hinf hrat hsm (Module.Dual.eval ℂ (Wsp lam) w)
  convert h using 1
  funext g
  simp [dualW_apply]

theorem hasWeightAt_of_wInf (lam : InfinitePlace E → DomWeight n) (π : Submodule ℂ (UA E n → ℂ))
    (f' : Wsp lam →ₗ[ℂ] (UA E n → ℂ)) (h0 : f' ≠ 0) (hπ : ∀ u, f' u ∈ π)
    (heq : ∀ (x : infU E n) u, f' (wInf lam x.1 u) = RU E n x.1 (f' u)) (v : InfinitePlace E) :
    HasWeightAt π v.embedding (lam v) := by
  obtain ⟨e, he⟩ : ∃ e : ∀ v, nablaSq ℂ n (lam v), f' (PiTensorProduct.tprod ℂ e) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (PiTensorProduct.ext (MultilinearMap.ext fun e => by simpa using hc e))
  refine ⟨GlobalTheory.DefU.isIrreducible_sqRep n (lam v), f' ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap e v, ?_,
    fun a => hπ _, fun x a => ?_⟩
  · intro h
    apply he
    have := LinearMap.congr_fun h (e v)
    simpa [MultilinearMap.toLinearMap] using this
  · have hx : x.1 ∈ infU E n := GlobalTheory.DefU.embU_le_infU _ x.2
    have h2 := heq ⟨x.1, hx⟩ (PiTensorProduct.tprod ℂ (Function.update e v a))
    have h3 : wInf lam x.1 (PiTensorProduct.tprod ℂ (Function.update e v a)) =
        PiTensorProduct.tprod ℂ (Function.update e v (GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding x.1) a)) := by
      change PiTensorProduct.map _ _ = _
      rw [PiTensorProduct.map_tprod]
      congr 1
      funext u
      by_cases h : u = v
      · subst h
        simp
      · have h1 := (Subgroup.mem_inf.1 x.2).2
        rw [Subgroup.mem_iInf] at h1
        have h4 := h1 u.embedding
        rw [Subgroup.mem_iInf] at h4
        have h5 : cEmb u.embedding x.1 = 1 := MonoidHom.mem_ker.1 (h4 (by simpa using h))
        simp only [Function.update_of_ne h, h5, map_one, Module.End.one_apply]
    rw [h3] at h2
    simpa [MultilinearMap.toLinearMap] using h2

theorem phiFun_mem_forms (hU : Unr E) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n)
    (K' : ∀ w : Pl E, Subgroup (UL n w)) (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K')
    (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (hF : F ∈ vecM S lam K') (w : Wsp lam) :
    phiFun lam F w ∈ forms S lam K' := by
  have h := semis E n (Wsp lam) ((wInf lam).comp (infU E n).subtype) (spanW E n lam) (globLev S K')
    (isOpen_globLev E hU n S K' hK) (phiFun lam F) (fun u => isAutFormU_phiFun hU S lam K' hK F hF u)
    (fun x u => phiFun_wInf lam F x u) (fun u => phiFun_mem_fixed S lam K' F hF u) w
  refine SetLike.le_def.1 ?_ h
  refine iSup_mono fun π => iSup_mono' fun hP => ⟨⟨hP.1, fun v => ?_⟩, le_rfl⟩
  obtain ⟨f', h0, hπ, heq⟩ := hP.2
  exact hasWeightAt_of_wInf lam π f' h0 hπ (fun x u => heq x u) v

end GlobalTheory.BCT.TrKer.RangeLe

namespace GlobalTheory.BCT.TrKer


open GlobalTheory.BCT.TrKer.RangeLe in
theorem range_Phi_le_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → LinearMap.range (Phi S lam K') ≤ forms S lam K' := by
  intro E _ _ _ hU n _ S _ lam K' hK
  rw [LinearMap.range_eq_map, ← TensorProduct.span_tmul_eq_top, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨F, w, rfl⟩, rfl⟩
  rw [Phi_tmul]
  exact phiFun_mem_forms hU S lam K' hK F.1 F.2 w

end GlobalTheory.BCT.TrKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFormTensorRangeLeUnitaryAutFormsWeightLeveStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vectorFormTensor_range_le_unitaryAutFormsWeightLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → LinearMap.range (Phi S lam K') ≤ forms S lam K' := by
  first | exact @GlobalTheory.BCT.TrKer.range_Phi_le_forms | exact GlobalTheory.BCT.TrKer.range_Phi_le_forms | (intros; apply GlobalTheory.BCT.TrKer.range_Phi_le_forms <;> assumption)
end
