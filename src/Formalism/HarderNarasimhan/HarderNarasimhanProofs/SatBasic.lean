module

public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermodZ

@[expose] public section

section -- merged from Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
open Module Submodule

noncomputable section

namespace Formalism.HN

section

variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : V →+ E)

theorem satBasic_zl_mono {A B : Submodule R V} (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro x hx
  rw [satR_mem_zl] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, h hy, rfl⟩

theorem satBasic_zl_bot : zl ρ (⊥ : Submodule R V) = ⊥ := by
  ext x
  rw [satR_mem_zl, Submodule.mem_bot]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Submodule.mem_bot] at hy
    rw [hy, map_zero]
  · intro hx
    exact ⟨0, Submodule.zero_mem _, by rw [hx, map_zero]⟩

end

theorem saturation_basic_properties : SatBasic := by
  intro R V E _ _ _ _ _ _ ρ L hL
  haveI hLd : DiscreteTopology (zl ρ L) := hL.2
  have hdisc : ∀ N : Submodule R V, N ≤ L → DiscreteTopology (zl ρ N) := fun N h =>
    Formalism.F.discreteTopology_of_le (satBasic_zl_mono ρ h)

  have hrev : ∀ A B : Submodule R V, A ≤ L → B ≤ L → zl ρ B ≤ zl ρ A → B ≤ A := by
    intro A B hAL hBL h y hy
    obtain ⟨z, hz, hzy⟩ := (satR_mem_zl ρ A _).mp (h ((satR_mem_zl ρ B _).mpr ⟨y, hy, rfl⟩))
    have := hL.1 (hAL hz) (hBL hy) hzy
    rw [← this]; exact hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N h
    exact ⟨hL.1.mono (fun x hx => h hx), hdisc N h⟩
  · intro A B hAB hBL
    haveI := hdisc B hBL
    haveI := hdisc A (hAB.trans hBL)
    refine ⟨Formalism.F.att_rk_le (satBasic_zl_mono ρ hAB), fun hr => ?_⟩
    have hc := Formalism.F.covolAntiSameRank E (zl ρ A) (zl ρ B) (hdisc B hBL)
      (satBasic_zl_mono ρ hAB) hr
    have hpB := Formalism.F.covol_pos (zl ρ B)
    show -Real.log (Formalism.F.covol (zl ρ A)) ≤ -Real.log (Formalism.F.covol (zl ρ B))
    have := Real.log_le_log hpB hc
    linarith
  · intro S N hS hSN hNL hr
    haveI := hdisc N hNL
    refine le_antisymm (hrev S N hS.1 hNL ?_) hSN
    intro x hx
    obtain ⟨a, ha, hax⟩ :=
      exists_smul_mem_of_finrank_eq (zl ρ N) (zl ρ S) (satBasic_zl_mono ρ hSN) hr x hx
    refine hS.2.2 x (satBasic_zl_mono ρ hNL hx) ?_
    have hx' : x = (a : ℝ)⁻¹ • ((a : ℝ) • x) := by
      rw [inv_smul_smul₀ (by exact_mod_cast ha)]
    rw [hx']
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rw [Int.cast_smul_eq_zsmul]
    exact hax
  · intro N hNL
    haveI := hdisc N hNL
    constructor
    · intro h0
      have h0' : Formalism.F.rk (zl ρ N) = 0 := h0
      have hb : zl ρ N = ⊥ := by
        by_contra hne
        have := Formalism.F.att_rk_pos hne
        omega
      rw [eq_bot_iff]
      intro y hy
      have hy' : ρ y ∈ zl ρ N := (satR_mem_zl ρ N _).mpr ⟨y, hy, rfl⟩
      rw [hb, Submodule.mem_bot] at hy'
      rw [Submodule.mem_bot]
      exact hL.1 (hNL hy) (Submodule.zero_mem L) (by rw [hy', map_zero])
    · rintro rfl
      show Formalism.F.rk (zl ρ ⊥) = 0
      rw [satBasic_zl_bot ρ]
      simp [Formalism.F.rk]
  · show -Real.log (Formalism.F.covol (zl ρ ⊥)) = 0
    rw [satBasic_zl_bot ρ, (Formalism.F.covolBasic E).1]
    simp
  · refine ⟨bot_le, ?_⟩
    rw [satBasic_zl_bot ρ]
    refine ⟨bot_le, fun x _ hx => ?_⟩
    simpa using hx
  · exact ⟨le_rfl, le_rfl, fun x hx _ => hx⟩
  · intro S hS
    haveI := hdisc S hS.1
    obtain ⟨_, h2, h3⟩ := Formalism.F.degQuot E (zl ρ L) (zl ρ S) hLd hS.2
    refine ⟨?_, ?_, ?_⟩
    · show _ = Formalism.F.rk (zl ρ L) - Formalism.F.rk (zl ρ S)
      omega
    · show Formalism.F.rk (zl ρ S) ≤ Formalism.F.rk (zl ρ L)
      omega
    · show _ = Formalism.F.deg (zl ρ L) - Formalism.F.deg (zl ρ S)
      linarith

end Formalism.HN
end
end

section -- merged from Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermod
open Module Submodule

noncomputable section

namespace Formalism.HN

section

variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : V →+ E)

theorem degSupermod_mem_zl (N : Submodule R V) (y : E) :
    y ∈ zl ρ N ↔ ∃ x ∈ N, ρ x = y := Iff.rfl

theorem degSupermod_zl_mono {A B : Submodule R V} (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (degSupermod_mem_zl ρ A y).mp hy
  exact (degSupermod_mem_zl ρ B _).mpr ⟨x, h hx, rfl⟩

theorem degSupermod_zl_sup (A B : Submodule R V) : zl ρ (A ⊔ B) = zl ρ A ⊔ zl ρ B := by
  simp only [zl, Submodule.sup_toAddSubgroup, AddSubgroup.map_sup]
  first
    | exact SupHomClass.map_sup AddSubgroup.toIntSubmodule _ _
    | (ext y; simp [Submodule.mem_sup, AddSubgroup.mem_sup])

theorem degSupermod_zl_inf {L A B : Submodule R V} (hinj : Set.InjOn ρ (L : Set V))
    (hA : A ≤ L) (hB : B ≤ L) : zl ρ (A ⊓ B) = zl ρ A ⊓ zl ρ B := by
  refine le_antisymm (le_inf (degSupermod_zl_mono ρ inf_le_left)
    (degSupermod_zl_mono ρ inf_le_right)) ?_
  rintro y ⟨hyA, hyB⟩
  obtain ⟨a, ha, rfl⟩ := (degSupermod_mem_zl ρ A y).mp hyA
  obtain ⟨b, hb, hba⟩ := (degSupermod_mem_zl ρ B _).mp hyB

  have hab : b = a := hinj (hB hb) (hA ha) hba
  subst hab
  exact (degSupermod_mem_zl ρ (A ⊓ B) _).mpr ⟨b, ⟨ha, hb⟩, rfl⟩

end

universe u v w in
theorem degSupermod_of (h : DegSupermodZ.{w}) : DegSupermod.{u, v, w} := by
  intro R V E _ _ _ _ _ _ ρ L A B hL hA hB
  haveI := hL.2
  have key := h E (zl ρ L) (zl ρ A) (zl ρ B) hL.2 (degSupermod_zl_mono ρ hA)
    (degSupermod_zl_mono ρ hB)
  rw [← degSupermod_zl_sup ρ A B, ← degSupermod_zl_inf ρ hL.1 hA hB] at key
  exact key

theorem degree_supermodular : DegSupermod := degSupermod_of degree_supermodular_integral

end Formalism.HN
end
end
