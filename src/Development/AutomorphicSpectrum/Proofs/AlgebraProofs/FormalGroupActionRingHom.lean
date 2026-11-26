module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NEvalSqZero
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanGenericPointSectionInput
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransport

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupActionRingHom
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupActionRingHom
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem rho_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ ρ : O →+* Matrix (Fin d) (Fin d) R, ∀ a, ρ a = rho B a := by
  intro R _ d O _ _ B
  obtain ⟨ρ, h⟩ := GlobalTheory.ChF.linPart_act_ringHom R d B.G O B.A R (RingHom.id R)
  refine ⟨ρ, fun a => ?_⟩
  rw [(h a).2]
  ext i j
  rfl

end GlobalTheory.CompanionTheory.Ar.Conj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupActionRingHomStatement
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_group_action_ring_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ ρ : O →+* Matrix (Fin d) (Fin d) R, ∀ a, ρ a = rho B a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.rho_hom | exact GlobalTheory.CompanionTheory.Ar.Conj.rho_hom | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.rho_hom <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BetaEquivariantFrobenius
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BetaEquivariantFrobenius
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv

theorem beta_rhoH_eq : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O]
    [StarRing O] (B : FB R d O) (a : O) (y : (Fin d → R) × (Fin d → R)),
    beta B p (rhoH B a y) = ((rho B (star a)).transpose.map (· ^ p)).mulVec (beta B p y) := by
  intro R _ p _ _ d O _ _ B a y
  refine dotProduct_eq _ _ fun u => ?_
  have hadj := (GlobalTheory.T.formal_hermitian_action_pairing R d O B).2.2 (star a) (alpha B p u) y
  rw [star_star] at hadj
  have htw := GlobalTheory.T.alpha_equivariant_frobenius R p d O B (star a) u
  rw [dotProduct_comm, dotProduct_beta, ← hadj, ← htw, ← dotProduct_beta, dotProduct_comm _ (beta B p y),
    Matrix.dotProduct_mulVec, Matrix.transpose_map, Matrix.mulVec_transpose]

end GlobalTheory.CompanionTheory.Ar.Conj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BetaEquivariantFrobeniusStatement
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.beta_equivariant_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (a : O) (y : (Fin d → R) × (Fin d → R)), beta B p (rhoH B a y) = ((rho B (star a)).transpose.map (· ^ p)).mulVec (beta B p y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.beta_rhoH_eq | exact GlobalTheory.CompanionTheory.Ar.Conj.beta_rhoH_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.beta_rhoH_eq <;> assumption)
end
end
