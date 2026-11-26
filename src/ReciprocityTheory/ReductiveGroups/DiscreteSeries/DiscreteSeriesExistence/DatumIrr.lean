module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumInj
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

def jSm (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) : T.V →ₗ[ℂ] smD ε (rreg ε) where
  toFun v := ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_smooth hP v₀ v⟩
  map_add' v v' := Subtype.ext (datumEmbedding_add hP v₀ v v')
  map_smul' c v := Subtype.ext (datumEmbedding_smul hP v₀ c v)

theorem jSm_coe (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) :
    ((jSm hP v₀ v : smD ε (rreg ε)) : L2 ε) = uniformisationL2 ε Ψ v₀ v := rfl

theorem datumV_eq_range (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) :
    datumV ε Ψ v₀ = LinearMap.range (jSm hP v₀) := by
  ext x
  rw [mem_datumV_iff hP v₀ x, LinearMap.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, Subtype.ext hv.symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, rfl⟩

theorem smE_jSm (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) {a b : Fin n} (hab : ε a = ε b) :
    smE ε (rreg ε) a b (jSm hP v₀ v) = jSm hP v₀ (T.dτ (Matrix.single a b 1) v) :=
  Subtype.ext (rightDerivative_datum_embedding hP v₀ v hab)

theorem jSm_injective (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) :
    Function.Injective (jSm hP v₀) := by
  intro v v' h
  apply uniformisationL2_injective hP hv₀
  have := congrArg (fun x : smD ε (rreg ε) => (x : L2 ε)) h
  simpa [jSm_coe] using this

theorem datumV_isKIrrHW (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) :
    IsKIrrHW ε (smE ε (rreg ε)) (lowK ε lam) (datumV ε Ψ v₀) := by
  rw [datumV_eq_range hP v₀]
  refine ⟨LinearMap.finiteDimensional_range _, ?_, ?_, ?_⟩
  · rintro a b hab x ⟨v, rfl⟩
    exact ⟨T.dτ (Matrix.single a b 1) v, (smE_jSm hP v₀ v hab).symm⟩
  · intro S' hS' hst
    have hW : ∀ a b, ε a = ε b → ∀ v ∈ S'.comap (jSm hP v₀),
        T.dτ (Matrix.single a b 1) v ∈ S'.comap (jSm hP v₀) := by
      intro a b hab v hv
      rw [Submodule.mem_comap] at hv ⊢
      rw [← smE_jSm hP v₀ v hab]
      exact hst a b hab _ hv
    rcases HW.KType.dτ_irred T _ hW with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨v, rfl⟩ := hS' hx
      have hv : v ∈ S'.comap (jSm hP v₀) := hx
      rw [h, Submodule.mem_bot] at hv
      rw [hv, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      rintro x ⟨v, rfl⟩
      have hv : v ∈ S'.comap (jSm hP v₀) := by rw [h]; trivial
      exact hv
  · refine ⟨jSm hP v₀ T.w, ⟨T.w, rfl⟩, ?_, ?_, ?_⟩
    · intro h0
      apply HW.KType.w_ne_zero T
      apply jSm_injective hP hv₀
      rw [h0, map_zero]
    · intro a
      rw [smE_jSm hP v₀ T.w rfl, T.w_wt a, map_smul]
    · intro a b _ hab
      rw [smE_jSm hP v₀ T.w hab, T.w_hw a b ‹_› hab, map_zero]

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsLowK
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem data_lowK_eq (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (S : Submodule ℂ H) (hS : S ≤ closGen E V)
    (hST : Formalism.MainNotions.S.IsKTypeOf ε σ (lowK ε lam) S) : S = V.map D.subtype := by
  have hSK' : ∀ k ∈ Kset ε, ∀ x ∈ S, σ k x ∈ S := by
    intro k hk x hx
    exact hST.2.1 k (by rw [mir_Kset_eq]; exact hk) x hx
  have hSM : S ≤ (genSub E V).map D.subtype := data_kfin_le hgap hσ hD hV hc hVK S hS hST.1 hSK'
  have hSD : S ≤ D := fun x hx => by
    obtain ⟨y, -, rfl⟩ := Submodule.mem_map.1 (hSM hx)
    exact y.2
  obtain ⟨w, hwS, hw0, hwhw⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hST hSD
  have hwG : w ∈ genSub E V := by
    obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hSM hwS)
    have : y = w := Subtype.ext hyw
    exact this ▸ hy
  have hwV : w ∈ V :=
    khw_lowK_mem hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap hwG hwhw
  have hTK : Formalism.MainNotions.S.IsKStableOn ε σ (V.map D.subtype) := by
    intro g hg x hx
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hx
    rw [mir_Kset_eq] at hg
    obtain ⟨u, hu, huv⟩ := hVK g hg v hv
    exact Submodule.mem_map.2 ⟨u, hu, by simpa using huv⟩
  have hwT : (w : H) ∈ V.map D.subtype := Submodule.mem_map_of_mem hwV
  have hle : S ≤ V.map D.subtype := by
    rcases hST.2.2.1 (S ⊓ V.map D.subtype) inf_le_left
        (fun g hg x hx => Submodule.mem_inf.2
          ⟨hST.2.1 g hg x (Submodule.mem_inf.1 hx).1, hTK g hg x (Submodule.mem_inf.1 hx).2⟩) with h | h
    · exfalso
      apply hw0
      have hm : (w : H) ∈ S ⊓ V.map D.subtype := Submodule.mem_inf.2 ⟨hwS, hwT⟩
      rw [h] at hm
      exact (Submodule.coe_eq_zero).1 ((Submodule.mem_bot ℂ).1 hm)
    · rw [← h]
      exact inf_le_right
  rcases (data_isKTypeOf hgap hσ hD hV hc hVK).2.2.1 S hle hST.2.1 with h | h
  · exfalso
    apply hw0
    have hm : (w : H) ∈ S := hwS
    rw [h] at hm
    exact (Submodule.coe_eq_zero).1 ((Submodule.mem_bot ℂ).1 hm)
  · exact h

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsAdm
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem data_admissible (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (μ : Fin n → ℝ) :
    FiniteDimensional ℂ
      (sSup {S : Submodule ℂ H | S ≤ closGen E V ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H) := by
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hE := hD.glRep
  obtain ⟨k, hk⟩ := khw_mem_layer hE hU hV hc hgap μ
  have hLf : FiniteDimensional ℂ (layer ε E V k) := finiteDimensional_layer hV.1 k
  have hLK := kStable_of_isKStableSub hσ hD (layer ε E V k) hLf (layer_kStable hE hV.2.1 k)
  have hMf : FiniteDimensional ℂ ((layer ε E V k).map D.subtype) := Module.Finite.map _ _
  have hle : (sSup {S : Submodule ℂ H | S ≤ closGen E V ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H) ≤
      (layer ε E V k).map D.subtype := by
    refine sSup_le fun S hSmem => ?_
    obtain ⟨hS, hST⟩ := hSmem
    obtain ⟨hSf, hSK, hirr, -, -⟩ := id hST
    have hSM := data_kfin_le hgap hσ hD hV hc hVK S hS hSf (fun g hg x hx => hSK g hg x hx)
    have hSD : S ≤ D := hSM.trans (Submodule.map_subtype_le _ _)
    obtain ⟨w, hwS, hw0, hwμ⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hST hSD
    have hwg : w ∈ genSub E V := by
      obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hSM hwS)
      have : y = w := Subtype.ext hyw
      exact this ▸ hy
    have hwL := hk w hwg hwμ
    have hS'K : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ (layer ε E V k).map D.subtype) := by
      intro g hg v hv
      refine ⟨hSK g hg v hv.1, ?_⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv.2
      obtain ⟨z, hz, hzeq⟩ := hLK g hg y hy
      exact Submodule.mem_map.2 ⟨z, hz, hzeq⟩
    rcases hirr _ inf_le_left hS'K with h0 | hEq
    · exfalso
      have hmem : (w : H) ∈ S ⊓ (layer ε E V k).map D.subtype :=
        ⟨hwS, Submodule.mem_map_of_mem hwL⟩
      rw [h0, Submodule.mem_bot] at hmem
      exact hw0 (Subtype.ext hmem)
    · rw [← hEq]
      exact inf_le_right
  exact Submodule.finiteDimensional_of_le hle

end ReciprocityTheory.ChartRestriction.DS
end
end
