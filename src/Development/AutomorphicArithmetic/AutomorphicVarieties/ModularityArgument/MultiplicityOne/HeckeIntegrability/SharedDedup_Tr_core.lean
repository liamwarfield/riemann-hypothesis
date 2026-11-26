module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.MuConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UnitHecke

@[expose] public section

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.BCT GlobalTheory.LFun GlobalTheory.PRep

noncomputable section

namespace DedupShared

theorem dedup_tr_core_6 (hTr : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.TrLevel) (hCv : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CvOp)
    {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K N : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hNo : IsOpen (N : Set G)) (hNc : IsCompact (N : Set G)) (hNK : N ≤ K)
    (hi : ((N.relIndex K : ℕ) : ℂ) ≠ 0) (hfd : FiniteDimensional ℂ (fixed ρ N))
    (f₁ f₂ F : G → ℂ) (h₁ : IsHecke N f₁) (h₂ : IsHecke N f₂)
    (hFeq : F = fun g => ((N.relIndex K : ℕ) : ℂ)⁻¹ * UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂ g) :
    trOn (fixed ρ N) (Lv ρ N f₁ * Lv ρ N f₂) = ((N.relIndex K : ℕ) : ℂ) ^ 2 * trc ρ K F := by
  set i : ℂ := ((N.relIndex K : ℕ) : ℂ) with hidef
  have hcvH : IsHecke N (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂) :=
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cvHecke _ N hNo hNc f₁ f₂ h₁ h₂
  have hFH : IsHecke N F := by
    refine ⟨?_, ?_⟩
    · rw [hFeq]
      exact hcvH.1.mul_left (f := fun _ => i⁻¹)
    · intro k hk x
      rw [hFeq]
      simp only
      rw [(hcvH.2 k hk x).1, (hcvH.2 k hk x).2]
      exact ⟨rfl, rfl⟩
  have hNK₁ : N ≤ K ⊓ rStab F ⊓ rStab fun y => F y⁻¹ := by
    refine le_inf (le_inf hNK ?_) ?_
    · exact fun k hk x => (hFH.2 k hk x).2
    · intro k hk x
      have e : (x * k)⁻¹ = k⁻¹ * x⁻¹ := by group
      show F (x * k)⁻¹ = F x⁻¹
      rw [e]
      exact (hFH.2 k⁻¹ (N.inv_mem hk) _).1
  have hK₁H : IsHecke (K ⊓ rStab F ⊓ rStab fun y => F y⁻¹) F := by
    refine ⟨hFH.1, fun k hk x => ⟨?_, hk.1.2 x⟩⟩
    have hk' : k⁻¹ ∈ rStab fun y => F y⁻¹ := (rStab _).inv_mem hk.2
    have := hk' x⁻¹
    simpa using this
  have hlev := hTr G K hKo hKc V ρ F _ N hNo hNK₁ (inf_le_left.trans inf_le_left) hK₁H hfd
  have hop : levOp ρ K N F LinearMap.id = i⁻¹ • i⁻¹ • levOp ρ N N (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂) LinearMap.id := by
    rw [hFeq]
    unfold levOp
    rw [Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
    congr 1
    rw [smul_finsum]
    exact finsum_congr fun q => by rw [mul_smul]
  have hmul : ∀ v ∈ fixed ρ N, levOp ρ N N (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂) LinearMap.id v = (Lv ρ N f₁ * Lv ρ N f₂) v :=
    fun v hv => (hCv G N hNo hNc V ρ f₁ f₂ h₁ h₂ v hv).1
  have hpres : ∀ v ∈ fixed ρ N, (Lv ρ N f₁ * Lv ρ N f₂) v ∈ fixed ρ N := fun v hv =>
    (hCv G N hNo hNc V ρ f₂ f₁ h₂ h₁ _ (hCv G N hNo hNc V ρ f₁ f₂ h₁ h₂ v hv).2.1).2.1
  have hstab : ∀ v ∈ fixed ρ N, levOp ρ K N F LinearMap.id v ∈ fixed ρ N := fun v hv => by
    rw [hop]
    simp only [LinearMap.smul_apply]
    rw [hmul v hv]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hpres v hv))
  have hres : (levOp ρ K N F LinearMap.id).restrict hstab = (i⁻¹ * i⁻¹) • (Lv ρ N f₁ * Lv ρ N f₂).restrict hpres := by
    ext v
    simp only [LinearMap.restrict_coe_apply, LinearMap.smul_apply, Submodule.coe_smul]
    rw [hop]
    simp only [LinearMap.smul_apply]
    rw [hmul v v.2, mul_smul]
  unfold trc
  rw [← hlev]
  unfold twTr trOn
  rw [dite_eq_left hstab, dite_eq_left hpres, hres, map_smul, smul_eq_mul]
  field_simp

end DedupShared
end
