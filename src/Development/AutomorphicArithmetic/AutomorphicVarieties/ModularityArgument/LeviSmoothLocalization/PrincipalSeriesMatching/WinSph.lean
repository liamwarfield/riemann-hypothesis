module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinUpDown
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.MatchIndX

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinSph
noncomputable section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.Z.Gam
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem exists_unr {ξ : kˣ →* ℂˣ} (h : IsUnram ξ) : ∃ a : ℂˣ, ξ = unrChar k a := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (K := k) (ValuativeRel.uniformizer k)
  have h0 : x ≠ 0 := fun e => ValuativeRel.uniformizer_ne_zero (R := k) (by rw [← hx, e, map_zero])
  exact ⟨_, eq_unrChar h (ϖ := Units.mk0 x h0) hx⟩

private theorem exists_family {n : ℕ} {s : Multiset (IrrGL (k := k))} (h1 : ∀ y ∈ s, y.1 = 1) (hn : (s.map Sigma.fst).sum = n)
    (hu : ∀ ξ ∈ chars s, IsUnram ξ) : ∃ α : Fin n → ℂˣ,
      s = Finset.univ.val.map fun i => IrrGL.ofChar (unrChar k (α i)) (isSmoothChar_of_isUnram (isUnram_unrChar k (α i))) := by
  have hc : Multiset.card s = n := by
    rw [← hn, Multiset.map_congr rfl h1, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]
  obtain ⟨x, rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_fin_enum s hc
  have key : ∀ i, ∃ a : ℂˣ, x i = IrrGL.ofChar (unrChar k a) (isSmoothChar_of_isUnram (isUnram_unrChar k a)) := fun i => by
    have hm : x i ∈ Finset.univ.val.map x := Multiset.mem_map_of_mem _ (Finset.mem_univ i)
    obtain ⟨θ, hθ, e⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar (x i) (h1 _ hm)
    obtain ⟨a, rfl⟩ := exists_unr (hu θ ⟨hθ, e ▸ hm⟩)
    exact ⟨a, e⟩
  choose α hα using key
  exact ⟨α, congrArg (fun f => Multiset.map f Finset.univ.val) (funext hα)⟩

end Loc

theorem winSph : WinSph := by
  intro K _ _ _ n hn π t v hw hu
  obtain ⟨⟨s, hs⟩, -, h3, -⟩ := suppFacts K n hn π v
  obtain ⟨h4, h5, -⟩ := h3 s hs
  have hl := winUnl K n π t v hw s hs
  obtain ⟨α, rfl⟩ := exists_family (h4.1 hw.1) h5 (hu s hs)
  obtain ⟨σ, hσ, hs⟩ := hs
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
  have hq : GroundTheory.LocalField.residueCard (v.adicCompletion K) = Ideal.absNorm v.asIdeal :=
    GroundTheory.Global.residueCard_adicCompletion
  obtain ⟨e⟩ := unlFull (v.adicCompletion K) n σ.V σ.ρ _ _ hs (hq ▸ hl)
  exact ⟨_, (CG.hasSat_mk π v _).2 (GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ
    (GlobalTheory.PrinSat.hasSatGL_of_equiv e (GlobalTheory.PrinSat.hasSatGL_prinSeries v α)))⟩

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinInd
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.UnrOne
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem unr_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    IsUnram (1 : kˣ →* ℂˣ) := by
  unfold IsUnram
  simp

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.indX :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.IndX := by
  intro K M _ _ _ _ _ _ _ h2 P π hI v s s' hs hs' ξ hξ
  have hM := matchIndX K M h2 P π hI v s s' hs hs' ξ⁻¹ (IsSmoothChar.inv hξ.1)
  have hK := (polFacts (v.adicCompletion K)).2.2.2
  have e : ξ * ξ⁻¹ = 1 := mul_inv_cancel ξ
  have h1 : eval 1 (pol s ξ⁻¹) = 0 :=
    ((hK s _).2.2.1 1).2 ⟨ξ, hξ, by rw [e]; exact unr_one, by rw [e]; simp⟩
  have h0 := congrArg (Polynomial.eval 1) hM
  rw [h1, eval_prod, eq_comm, Finset.prod_eq_zero_iff] at h0
  obtain ⟨w, -, hw⟩ := h0
  rw [eval_comp, eval_pow, eval_X, one_pow] at hw
  have hL := polFacts (w.1.adicCompletion M)
  obtain ⟨ζ, hζ, hu, hval⟩ := ((hL.2.2.2 (s' w) _).2.2.1 1).1 hw
  refine ⟨w, ?_⟩
  have : ζ = ξ.comp (nm w) := by
    refine hL.2.1 _ _ hu ?_
    rw [mul_one, Units.val_eq_one] at hval
    exact mul_inv_eq_one.1 hval
  exact this ▸ hζ
end

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem rootBounds {q x a b : ℝ} {f : ℕ} (hf : 0 < f) (hq : 0 < q) (hx : 0 ≤ x)
    (h1 : ((q ^ f : ℝ)) ^ a < x ^ f) (h2 : x ^ f < ((q ^ f : ℝ)) ^ b) :
    q ^ a < x ∧ x < q ^ b := by
  have e : ∀ c : ℝ, ((q ^ f : ℝ)) ^ c = (q ^ c) ^ f := by
    intro c
    rw [← Real.rpow_natCast q f, ← Real.rpow_mul hq.le, mul_comm, Real.rpow_mul hq.le, Real.rpow_natCast]
  rw [e] at h1 h2
  exact ⟨lt_of_pow_lt_pow_left₀ f hx h1, lt_of_pow_lt_pow_left₀ f (Real.rpow_nonneg hq.le _) h2⟩

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winInd :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.WinInd := by
  intro K M _ _ _ _ _ _ _ h2 P π hsys t v hw
  refine ⟨indTor K M h2 P π hsys v fun w => ⟨(hw w).1.1, (hw w).2⟩, fun s hs ξ hξ => ?_⟩
  have hs' : ∀ w : GroundTheory.Global.SemiLocal.PlacesOver M v, ∃ s', SuppAt π w.1 s' := fun w =>
    (suppFacts M 2 (by norm_num) π w.1).1
  choose s' hs' using hs'
  obtain ⟨w, hζ⟩ := indX K M h2 P π hsys v s s' hs hs' ξ hξ
  obtain ⟨hsm, -⟩ := hξ
  obtain ⟨-, hnorm, hf, hN⟩ := normVal K M v w ξ
  obtain ⟨b1, b2⟩ := (hw w).1.2 (s' w) (hs' w) _ hζ
  have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot))
  simp only [MonoidHom.comp_apply] at b1 b2
  rw [hnorm hsm, hN, Nat.cast_pow] at b1 b2
  exact rootBounds hf hq (norm_nonneg _) b1 b2
end
