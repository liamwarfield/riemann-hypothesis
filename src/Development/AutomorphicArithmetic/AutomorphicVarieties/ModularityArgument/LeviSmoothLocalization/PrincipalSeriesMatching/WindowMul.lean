module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.Bridge

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WindowMul
noncomputable section

open NumberField IsDedekindDomain UpperTheory.V.Z.Gam
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

private lemma window_mul (q : ℕ) (hq : q ≠ 0) (t a : ℝ) (x y : ℂ)
    (hy : ‖y‖ = (q : ℝ) ^ a)
    (hx : (q : ℝ) ^ (t - 1 / 2) < ‖x‖ ∧ ‖x‖ < (q : ℝ) ^ (t + 1 / 2)) :
    (q : ℝ) ^ (t + a - 1 / 2) < ‖x * y‖ ∧ ‖x * y‖ < (q : ℝ) ^ (t + a + 1 / 2) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have ha : (0 : ℝ) < (q : ℝ) ^ a := Real.rpow_pos_of_pos hq0 a
  rw [norm_mul, hy, show t + a - 1 / 2 = (t - 1 / 2) + a by ring,
    show t + a + 1 / 2 = (t + 1 / 2) + a by ring, Real.rpow_add hq0, Real.rpow_add hq0]
  exact ⟨mul_lt_mul_of_pos_right hx.1 ha, mul_lt_mul_of_pos_right hx.2 ha⟩

theorem winTw : WinTw := by
  intro K _ _ _ χ
  obtain ⟨a, ha⟩ := charAbs K χ
  refine ⟨a, fun n hn π t v hw => ?_⟩
  have hq : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  obtain ⟨⟨s, hs⟩, -, hπ, -, -⟩ := suppFacts K n hn π v
  obtain ⟨⟨s₁, hs₁⟩, huniq, hπ', -, -⟩ := suppFacts K n hn (π.twist χ) v
  obtain ⟨s₂, hs₂, -, hchars, hmap⟩ := suppTw K n hn π v χ s hs
  refine ⟨?_, fun s' hs' ζ hζ => ?_⟩
  · refine ((hπ' s₂ hs₂).1).2 fun y hy => ?_
    have hy' : y.1 ∈ s₂.map Sigma.fst := Multiset.mem_map_of_mem _ hy
    rw [hmap] at hy'
    obtain ⟨x, hx, hxy⟩ := Multiset.mem_map.1 hy'
    rw [← hxy]
    exact ((hπ s hs).1).1 hw.1 x hx
  · rw [huniq s' s₂ hs' hs₂] at hζ
    obtain ⟨ξ, hξ, rfl⟩ := (hchars ζ).1 hζ
    simpa [MonoidHom.mul_apply, Units.val_mul] using
      window_mul _ hq t a _ _ (ha v).2 (hw.2 s hs ξ hξ)

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PlainIff
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem valuation_unif : valuation k (unif k : k) = uniformizer k := by
  obtain ⟨⟨h1, h2⟩, -⟩ := polFacts k
  obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
  exact le_antisymm (le_uniformizer_iff.2 h1) (hy ▸ h2 y (hy ▸ uniformizer_lt_one))

private theorem absPow_one_unif :
    ((absPow k 1 (unif k) : ℂˣ) : ℂ) * (resCard k : ℂ) = 1 := by
  have hq : (resCard k : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := IsLocalRing.ResidueField 𝒪[k])
    exact_mod_cast this.ne'
  rw [val_absPow, Complex.cpow_one, GlobalTheory.GLDoubling.nabs_unif valuation_unif]
  push_cast
  exact inv_mul_cancel₀ hq

private theorem link_iff {ξ ξ' : kˣ →* ℂˣ} (hξ : IsSmoothChar ξ) (hξ' : IsSmoothChar ξ') :
    IrrGL.ofChar ξ hξ = (IrrGL.ofChar ξ' hξ').nu 1 ↔
      IsUnram (ξ' * ξ⁻¹) ∧ (((ξ' * ξ⁻¹) (unif k) : ℂˣ) : ℂ) = (resCard k : ℂ) := by
  have hA := absPow_one_unif (k := k)
  have hA0 : ((absPow k 1 (unif k) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
  constructor
  · rintro rfl
    have e : ξ' * (ξ' * absPow k 1)⁻¹ = (absPow k 1)⁻¹ := by
      rw [mul_inv, mul_inv_cancel_left]
    rw [e]
    refine ⟨isUnram_inv (isUnram_absPow k 1), ?_⟩
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    have hq : (resCard k : ℂ) = ((absPow k 1 (unif k) : ℂˣ) : ℂ)⁻¹ := eq_inv_of_mul_eq_one_right hA
    rw [hq]
  · rintro ⟨hu, hv⟩
    obtain ⟨-, h2, -⟩ := polFacts k
    refine h2 ξ (ξ' * absPow k 1) ?_ ?_
    · have e : ξ * (ξ' * absPow k 1)⁻¹ = (ξ' * ξ⁻¹)⁻¹ * (absPow k 1)⁻¹ := by
        simp only [mul_inv, inv_inv]
        ac_rfl
      rw [e]
      exact isUnram_mul (isUnram_inv hu) (isUnram_inv (isUnram_absPow k 1))
    · refine Units.ext ?_
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val] at hv
      rw [← hv] at hA
      rw [MonoidHom.mul_apply, Units.val_mul]
      have h0 : ((ξ (unif k) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      field_simp at hA
      rw [mul_comm, hA]

end Loc

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.plainIff :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.PlainIff := by
  intro K _ _ _ n hn π v
  obtain ⟨-, huniq, -, -, -⟩ := suppFacts K n hn π v
  have hq : (Ideal.absNorm v.asIdeal : ℂ) = (resCard (v.adicCompletion K) : ℂ) := by
    have h : GroundTheory.LocalField.residueCard (v.adicCompletion K) = Ideal.absNorm v.asIdeal :=
      GroundTheory.Global.residueCard_adicCompletion
    rw [← h]
    rfl
  constructor
  · intro h
    refine ⟨fun σ hσ => ?_, fun s hs ξ hξ ξ' hξ' hu e => ?_⟩
    · obtain ⟨s, h1, h2, -⟩ := h σ hσ
      exact ⟨s, h1, h2⟩
    · obtain ⟨σ, hσ, -⟩ := id hs
      obtain ⟨t, ht, -, hl⟩ := h σ hσ
      obtain rfl : s = t := huniq s t hs ⟨σ, hσ, ht.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm⟩
      obtain ⟨a, ha⟩ := hξ
      obtain ⟨b, hb⟩ := hξ'
      exact hl _ hb _ ha ((link_iff b a).2 ⟨hu, e.trans hq⟩)
  · rintro ⟨ht, hu⟩ σ hσ
    obtain ⟨s, hs, h1⟩ := ht σ hσ
    refine ⟨s, hs, h1, fun y hy z hz e => ?_⟩
    obtain ⟨ξ, hξ, rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar y (h1 y hy)
    obtain ⟨ξ', hξ', rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar z (h1 z hz)
    obtain ⟨h2, h3⟩ := (link_iff hξ hξ').1 e
    exact hu s ⟨σ, hσ, hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm⟩ ξ' ⟨hξ', hz⟩ ξ ⟨hξ, hy⟩ h2 (h3.trans hq.symm)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SuppSmo1
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.suppSmo1 :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.SuppSmo1 := by
  intro K _ _ _ π π' h t v hw
  have e : π = π' := GlobalTheory.CuspRep.CuspSub.ext (UpperTheory.V.Af.strongMultOneC K 1 π π' h)
  exact e ▸ hw
end
