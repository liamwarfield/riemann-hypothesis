module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKur

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnWp
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem shortW_map (l : ℕ) [Fact l.Prime] (g2 g3 : ℂ) (ι : ℂ ≃+* ℂ_[l]) :
    A.shortW (ι g2) (ι g3) = (A.shortW g2 g3).map (ι : ℂ →+* ℂ_[l]) := by
  ext <;> simp [A.shortW, WeierstrassCurve.map, map_ofNat]

theorem wp_bridge (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) :
    A.wpReg (A.shortW (ι L.g₂) (ι L.g₃)) = PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L) := by
  have h1 := F.curveBridge (A.shortW L.g₂ L.g₃) L (A.shortInv ℂ _ _).2.1 (A.shortInv ℂ _ _).2.2.1
  have h2 := (A.zMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (A.shortW L.g₂ L.g₃)).2.2.1
  rw [← h1, h2, shortW_map]

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnLat
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem good_lattice (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l])
    (hg : IsGoodModel l L ι g2 g3) :
    ∃ L' : PeriodPair, LatModel l L' ι g2 g3 ∧ ∀ d, HasCMBy d L → HasCMBy d L' := by
  obtain ⟨-, -, h2, h3, -, lam, hlam, e2, e3⟩ := hg
  have hm : ι.symm lam ≠ 0 := by
    intro h
    apply hlam
    have := congrArg ι h
    simpa using this
  have hc : (ι.symm lam)⁻¹ ≠ 0 := inv_ne_zero hm
  obtain ⟨-, -, -, -, -, -, -, -, -, hg2, hg3⟩ := F.homogeneity L (ι.symm lam)⁻¹ hc
  refine ⟨F.scalePair L (ι.symm lam)⁻¹ hc, ⟨?_, ?_, h2, h3⟩,
    fun d hd => F.hasCMByScale d L _ hc hd⟩
  · rw [hg2, e2]
    simp
  · rw [hg3, e3]
    simp

end ReciprocityTheory.ChartRestriction.L1
end
end
