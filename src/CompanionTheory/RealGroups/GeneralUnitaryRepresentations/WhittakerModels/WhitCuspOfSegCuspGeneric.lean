module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.CuspGenericWhittaker.CuspGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm

@[expose] public section

section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.WhittakerModels.WhitLeOneOfDict
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace CompanionTheory.rg.gu.whit

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem whitLeOne_of_dict
    (hU : ∀ n : ℕ, unipB k (Fin n) = GroundTheory.Automorphic.Iwasawa.unipotent k n)
    (hC : ∀ (ψ : AddChar k Circle) (n : ℕ) (u : unipB k (Fin n)),
      ((GlobalTheory.LocGL.whitChar ψ n u : ℂˣ) : ℂ) =
        GroundTheory.Automorphic.Whittaker.psiN (Circle.coeHom.compAddChar ψ) (u : GL (Fin n) k))
    (hR : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (N : Subgroup G)
      (θ : N →* ℂˣ), Module.rank ℂ (TwJacquet ρ N θ) ≤ 1 ↔
        Module.rank ℂ (GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ (fun u : N => ((θ u : ℂˣ) : ℂ))) ≤ 1)
    (hA : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ G V), GlobalTheory.PRep.IsAdmissible ρ ↔ GroundTheory.Automorphic.IsAdmissible ρ) :
    GlobalTheory.BZMir.Whit.WhitLeOne k := by
  intro n ψ V _ _ π hs hirr hψc hψ1
  have hadm : GroundTheory.Automorphic.IsAdmissible π :=
    (hA π).1 (CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k n V π hs hirr)
  have hc : Continuous (Circle.coeHom.compAddChar ψ) := continuous_subtype_val.comp hψc
  have h1 : Circle.coeHom.compAddChar ψ ≠ 1 := by
    intro h
    apply hψ1
    ext x
    have h2 : ((ψ x : Circle) : ℂ) = ((1 : Circle) : ℂ) :=
      (congrArg (fun f : AddChar k ℂ => f x) h).trans Circle.coe_one.symm
    exact h2
  have : π.IsIrreducible := hirr
  have key := GroundTheory.Automorphic.ContragredientTranspose.rank_whittaker_le_one
    (Circle.coeHom.compAddChar ψ) hc h1 π hadm
  rw [hR]
  have heq : GroundTheory.Automorphic.Whittaker.equivariantFunctionals π (fun u : unipB k (Fin n) => ((whitChar ψ n u : ℂˣ) : ℂ)) =
      GroundTheory.Automorphic.Whittaker.equivariantFunctionals π (fun u : GroundTheory.Automorphic.Iwasawa.unipotent k n =>
        GroundTheory.Automorphic.Whittaker.psiN (Circle.coeHom.compAddChar ψ) (u : GL (Fin n) k)) := by
    ext ℓ
    constructor
    · intro h u v
      have hu : (u : GL (Fin n) k) ∈ unipB k (Fin n) := (hU n).symm ▸ u.2
      have := h ⟨u, hu⟩ v
      simp only at this
      rw [hC] at this
      show ℓ (π u v) = GroundTheory.Automorphic.Whittaker.psiN (Circle.coeHom.compAddChar ψ) (u : GL (Fin n) k) * ℓ v
      exact this
    · intro h u v
      have hu : (u : GL (Fin n) k) ∈ GroundTheory.Automorphic.Iwasawa.unipotent k n := (hU n) ▸ u.2
      have := h ⟨u, hu⟩ v
      simp only at this
      show ℓ (π u v) = ((whitChar ψ n u : ℂˣ) : ℂ) * ℓ v
      rw [hC]
      exact this
  rw [heq]
  exact key

end CompanionTheory.rg.gu.whit
end
end

section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.WhittakerModels.RankDual
noncomputable section

open GlobalTheory.PRep Module

namespace CompanionTheory.rg.gu.whit

theorem rank_le_one_iff_dual (W : Type) [AddCommGroup W] [Module ℂ W] :
    Module.rank ℂ W ≤ 1 ↔ Module.rank ℂ (Module.Dual ℂ W) ≤ 1 := by
  by_cases hf : Module.Finite ℂ W
  · rw [Module.dual_rank_eq, Cardinal.lift_id]
  · have h0 : Cardinal.aleph0 ≤ Module.rank ℂ W := not_lt.1 (fun h => hf (rank_lt_aleph0_iff.1 h))
    have h1 := rank_lt_rank_dual h0
    constructor
    · intro h
      exact absurd (h0.trans h) (not_le.2 Cardinal.one_lt_aleph0)
    · intro h
      exact absurd ((h0.trans h1.le).trans h) (not_le.2 Cardinal.one_lt_aleph0)

theorem rank_twJacquet_le_one_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) :
    Module.rank ℂ (TwJacquet ρ N θ) ≤ 1 ↔
      Module.rank ℂ (GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ (fun u : N => ((θ u : ℂˣ) : ℂ))) ≤ 1 := by
  have hE : GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ (fun u : N => ((θ u : ℂˣ) : ℂ)) =
      (twKer ρ N θ).dualAnnihilator := by
    ext ℓ
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro h w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, v, rfl⟩ := hx
        rw [map_sub, map_smul, h n v, smul_eq_mul, sub_self]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
      | smul a x _ hx => rw [map_smul, hx, smul_zero]
    · intro h n v
      have := h _ (Submodule.subset_span ⟨n, v, rfl⟩)
      rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at this
      exact this
  rw [rank_le_one_iff_dual, hE, ← (Submodule.dualQuotEquivDualAnnihilator _).rank_eq]

end CompanionTheory.rg.gu.whit
end
end

section -- merged from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.WhittakerModels.UnipBEqUnipotent
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace CompanionTheory.rg.gu.whit

theorem unipB_eq_unipotent (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) : unipB k (Fin n) = GroundTheory.Automorphic.Iwasawa.unipotent k n := by
  ext g
  rw [mem_unipB]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j hij => h1 i j hij, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j hij => h1 hij, h2⟩

theorem whitChar_eq_psiN (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n : ℕ) (u : unipB k (Fin n)) :
    ((whitChar ψ n u : ℂˣ) : ℂ) =
      GroundTheory.Automorphic.Whittaker.psiN (Circle.coeHom.compAddChar ψ) (u : GL (Fin n) k) := by
  have hs : (∑ p : Fin n × Fin n with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin n) k).val p.1 p.2) =
      GroundTheory.Automorphic.Whittaker.superdiagSum ((u : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    rfl
  show ((Circle.toUnits (ψ _) : ℂˣ) : ℂ) = ((ψ (GroundTheory.Automorphic.Whittaker.superdiagSum _) : Circle) : ℂ)
  rw [hs]
  rfl

theorem isAdmissible_iff {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) : GlobalTheory.PRep.IsAdmissible ρ ↔ GroundTheory.Automorphic.IsAdmissible ρ := by
  have hfix : ∀ K : Subgroup G, fixed ρ K = GroundTheory.Automorphic.fixedVectors ρ K := by
    intro K
    ext v
    constructor
    · intro h g hg
      have := h ⟨g, hg⟩
      simpa using this
    · intro h g
      have := h g g.2
      simpa using this
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun K hc ho => hfix K ▸ h2 K ho hc⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun K ho hc => (hfix K).symm ▸ h2 K hc ho⟩

end CompanionTheory.rg.gu.whit
end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace CompanionTheory.rg.gu.whit

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem whitLeOne : GlobalTheory.BZMir.Whit.WhitLeOne k :=
  whitLeOne_of_dict k (unipB_eq_unipotent k) (whitChar_eq_psiN k)
    (fun ρ N θ => rank_twJacquet_le_one_iff ρ N θ) (fun ρ => isAdmissible_iff ρ)

theorem whitRankIrr : GlobalTheory.BZSeg.WhitRankIrr k :=
  fun ψ hψc hψ1 N V _ _ π hs hirr => whitLeOne k N ψ V π hs hirr hψc hψ1

end CompanionTheory.rg.gu.whit
