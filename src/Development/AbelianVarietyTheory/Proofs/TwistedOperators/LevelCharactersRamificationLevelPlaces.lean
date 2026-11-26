module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGoodRowsFiniteGroupAction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlaces
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRamif

variable {D : D7}

theorem not_two_primes (PP : Pl D.host.E) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h1 : (p : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : (q : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  have hc : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem natCast_mem_conj {PP PP' : Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl PP PP') {n : ℕ}
    (hn : (n : 𝓞 D.host.E) ∈ PP.asIdeal) : (n : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  obtain ⟨c', hc', e⟩ := h _ hn
  have e2 : c' = (n : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    have e3 : (((n : 𝓞 D.host.E)) : D.host.E) = (n : D.host.E) := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) n
    rw [e, e3, star_natCast]
  rwa [e2] at hc'

theorem exists_prime_mem {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) {PP : Pl D.host.E}
    (h : PP ∈ Q) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ∀ i, q ≠ D.host.g i := by
  obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := hQ PP h
  refine ⟨q, hq, ?_, hne⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
  exact card_nsmul_eq_zero'

theorem typePrime_mem {P : Formalism.L2.Host.PiBar D.host} {k : Fin 2} {PP : Pl D.host.E} (h : P.Div k PP) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  have h1 := P.pb_over k
  have h2 : PP.under (𝓞 D.host.K) = P.pb k := h
  rw [← h2] at h1
  have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
  rwa [map_natCast] at h3

theorem isConjPl_of_eq {w w' : Pl D.host.E}
    (h : w'.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) w.asIdeal) : Formalism.IndefR.Lev.IsConjPl w' w := by
  intro c hc
  rw [h, Formalism.L2.Col.mem_conjIdeal] at hc
  exact ⟨_, hc, rfl⟩

theorem ramif_at_levels : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ (t : T0) (j : Fin D.R.m), Disjoint L.Pg (L.Q t) ∧ (∀ PP ∈ L.Q t, (L.C.mu0 j).UnrAt PP) ∧ (∀ PP ∈ L.Pg, (L.xiH t).UnrAt PP) ∧ ∀ PP', PP' ∉ L.Pg → (∀ PP ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → (L.C.mu0 j).UnrAt PP' := by
  classical
  intro D T0 L μ0 hL t j
  have hoff : ∀ (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal →
      PP ∉ L.Q t ∧ ¬ ∃ PP' ∈ L.Q t, Formalism.IndefR.Lev.IsConjPl PP' PP := by
    intro k PP hk
    refine ⟨fun hQ => ?_, fun ⟨PP', hQ, hc⟩ => ?_⟩
    · obtain ⟨q, hq, hm, hne⟩ := exists_prime_mem (hL.Q_pl t) hQ
      exact not_two_primes PP hq (D.host.g_prime k) (hne k) hm hk
    · obtain ⟨q, hq, hm, hne⟩ := exists_prime_mem (hL.Q_pl t) hQ
      exact not_two_primes PP hq (D.host.g_prime k) (hne k) (natCast_mem_conj hc hm) hk
  have hPg : ∀ PP ∈ L.Pg, PP ∉ L.Q t ∧ ¬ ∃ PP' ∈ L.Q t, Formalism.IndefR.Lev.IsConjPl PP' PP := by
    intro PP h
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
    exact hoff k PP (typePrime_mem hk)
  have hM := L.C.isMu0 j
  refine ⟨Finset.disjoint_left.2 fun PP h => (hPg PP h).1, fun PP hQ => ?_, fun PP h => ?_, fun PP h1 h2 => ?_⟩
  · exact hM.unr PP fun k hk => (hoff k PP hk).1 hQ
  · by_contra hn
    rcases (hL.Q_ram t PP).1 hn with h' | h'
    · exact (hPg PP h).1 h'
    · exact (hPg PP h).2 h'
  · refine hM.unr PP fun k hk => ?_
    rcases GlobalTheory.ConjOverQuad.div_or_conj_div D L.C.P k PP hk with h | ⟨PP', h, hc⟩
    · exact h1 ((hL.Pg PP).2 ⟨k, h⟩)
    · exact h2 PP' ((hL.Pg PP').2 ⟨k, h⟩) (isConjPl_of_eq hc)

end GlobalTheory.LevelRamif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlacesStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacters_ramification_levelPlaces : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ (t : T0) (j : Fin D.R.m), Disjoint L.Pg (L.Q t) ∧ (∀ PP ∈ L.Q t, (L.C.mu0 j).UnrAt PP) ∧ (∀ PP ∈ L.Pg, (L.xiH t).UnrAt PP) ∧ ∀ PP', PP' ∉ L.Pg → (∀ PP ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → (L.C.mu0 j).UnrAt PP' := by
  first | exact @GlobalTheory.LevelRamif.ramif_at_levels | exact GlobalTheory.LevelRamif.ramif_at_levels | (intros; apply GlobalTheory.LevelRamif.ramif_at_levels <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepThetaDatumHalfEqSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepThetaDatumHalfEqSmul
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaMove

open GlobalTheory.SplitHecke

variable {D : D7} {S T : HSp D}

theorem act_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := map_add (actAdd S T g h) x y

theorem act_nsmul (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := map_nsmul (actAdd S T g h) k x

theorem act_act_inv (g : GA D S) (h : GA D T) (u : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := by
  have := actO_inv_actO g⁻¹ h⁻¹ u
  rwa [inv_inv, inv_inv] at this

theorem isHalf_of_act {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e (actO S T g h u)) :
    IsHalf e u := by
  have := isHalf_actO g⁻¹ h⁻¹ hu
  rwa [actO_inv_actO] at this

theorem isSBHalf_comp {e : AE D} {Λ : AddSubgroup (WO S T)} (g : GA D S) (h : GA D T)
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) {Ψ : WO S T → ℂ} (hΨ : IsSBHalf e Λ Ψ) :
    IsSBHalf e Λ fun t => Ψ (actO S T g h t) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := hΨ
  refine ⟨fun t ht => isHalf_of_act g h (h1 _ ht), k, hk, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · show Ψ _ = Ψ _
    rw [act_add, act_nsmul]
    exact h2 _ ((hΛ u).1 hu) (isHalf_actO g h hu') _
  · rw [hΛ, act_nsmul]
    exact h3 _ ht

theorem halfInd_act {e : AE D} {Λ : AddSubgroup (WO S T)} (g : GA D S) (h : GA D T)
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) (t : WO S T) :
    halfInd e Λ (actO S T g h t) = halfInd e Λ t := by
  unfold halfInd
  have : (actO S T g h t ∈ Λ ∧ IsHalf e (actO S T g h t)) ↔ (t ∈ Λ ∧ IsHalf e t) :=
    and_congr (hΛ t).symm ⟨isHalf_of_act g h, isHalf_actO g h⟩
  by_cases ht : t ∈ Λ ∧ IsHalf e t
  · rw [if_pos ht, if_pos (this.2 ht)]
  · rw [if_neg ht, if_neg (fun hh => ht (this.1 hh))]

theorem heisO_smul' (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem om_theta_eq_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ), (∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm → ∀ Ψ, IsSBHalf e Λ Ψ → IsThetaFunO ψ S T (Tm Ψ)) → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → ∀ (g : GA D S) (h : GA D T), (∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) → ∀ c c' : ℂ, c ≠ 0 → om (g, h) f₀ = c • f₀ → (∀ x, Φ (actO S T g⁻¹ h⁻¹ x) = c' * Φ x) → om (g, h) f = (c * c') • f := by
  intro D ψ S T χS χT om hom e Λ f₀ Φ f hth hΘ g h hΛ c c' hc hf₀ hΦ
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hΘ
  let Tm' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    c⁻¹ • (om (g, h) ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T g h))
  have hT' : ∀ Ψ, Tm' Ψ = c⁻¹ • om (g, h) (Tm fun t => Ψ (actO S T g h t)) := fun Ψ => rfl
  have hP : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm' := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · have hΨ' := isSBHalf_comp g h hΛ hΨ
      have h1 := hTm.trans _ hΨ' _ (isHalf_actO g⁻¹ h⁻¹ hx)
      simp only [act_add, act_act_inv] at h1
      rw [hT', hT', h1, hom.om_heis _ _ _ _ (hth Tm hTm _ hΨ'), act_act_inv, heisO_smul']
    · have hΨ' := isSBHalf_comp g h hΛ hΨ
      have h1 := hTm.modul _ hΨ' _ (isHalf_actO g⁻¹ h⁻¹ hy)
      have h2 : ∀ t, symplO S T t (actO S T g⁻¹ h⁻¹ y) = symplO S T (actO S T g h t) y := fun t => by
        rw [← symplO_actO S T g h, act_act_inv]
      simp only [h2] at h1
      rw [hT', hT', h1, hom.om_heis _ _ _ _ (hth Tm hTm _ hΨ'), act_act_inv, heisO_smul']
    · have h1 := hTm.vac
      rw [one_smul] at h1 ⊢
      have h2 : (fun t => halfInd e Λ (actO S T g h t)) = halfInd e Λ := funext (halfInd_act g h hΛ)
      rw [hT', h2, h1, hf₀, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have e1 : f = Tm Φ := hall Tm hTm
  have e2 : f = Tm' Φ := hall Tm' hP
  have e3 : Φ = c' • fun t => Φ (actO S T g h t) := by
    funext t
    have := hΦ (actO S T g h t)
    rw [actO_inv_actO] at this
    exact this
  rw [hT'] at e2
  have e4 : om (g, h) (Tm fun t => Φ (actO S T g h t)) = c • f := by
    rw [e2, smul_smul, mul_inv_cancel₀ hc, one_smul]
  calc om (g, h) f = om (g, h) (Tm (c' • fun t => Φ (actO S T g h t))) := by rw [← e3, ← e1]
    _ = (c * c') • f := by rw [map_smul, map_smul, e4, smul_smul, mul_comm]

end GlobalTheory.ThetaMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepThetaDatumHalfEqSmulStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_theta_datum_half_eq_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ), (∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm → ∀ Ψ, IsSBHalf e Λ Ψ → IsThetaFunO ψ S T (Tm Ψ)) → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → ∀ (g : GA D S) (h : GA D T), (∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) → ∀ c c' : ℂ, c ≠ 0 → om (g, h) f₀ = c • f₀ → (∀ x, Φ (actO S T g⁻¹ h⁻¹ x) = c' * Φ x) → om (g, h) f = (c * c') • f := by
  first | exact @GlobalTheory.ThetaMove.om_theta_eq_smul | exact GlobalTheory.ThetaMove.om_theta_eq_smul | (intros; apply GlobalTheory.ThetaMove.om_theta_eq_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElement
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CutIsometry
namespace GlobalTheory.TruncationIsometry

open Matrix

theorem cT_cut {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (ε : R) (hσ : σ ε = ε)
    (M : Matrix (Fin n) (Fin n) R) :
    Formalism.UG.cT σ (ε • M + ((1 : R) - ε) • (1 : Matrix (Fin n) (Fin n) R)) =
      ε • Formalism.UG.cT σ M + ((1 : R) - ε) • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Formalism.UG.cT, hσ]
  · have h' : j ≠ i := fun e => h e.symm
    simp [Formalism.UG.cT, hσ, Matrix.one_apply_ne h, Matrix.one_apply_ne h']

theorem cut_isometry {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (ε : R) (hσ : σ ε = ε) (hε : ε * ε = ε)
    (J M : Matrix (Fin n) (Fin n) R) (hM : Formalism.UG.cT σ M * J * M = J) :
    Formalism.UG.cT σ (ε • M + ((1 : R) - ε) • (1 : Matrix (Fin n) (Fin n) R)) * J *
      (ε • M + ((1 : R) - ε) • (1 : Matrix (Fin n) (Fin n) R)) = J := by
  have h1 : ε * (1 - ε) = 0 := by rw [mul_sub, mul_one, hε, sub_self]
  have h2 : (1 - ε) * ε = 0 := by rw [mul_comm, h1]
  have h3 : (1 - ε) * (1 - ε) = 1 - ε := by rw [mul_sub, mul_one, h2, sub_zero]
  rw [cT_cut σ ε hσ M]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_add, smul_smul, hM, hε, h1, h2, h3, zero_smul, add_zero, zero_add]
  rw [← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.TruncationIsometry
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GfCut

variable {R : Type} [CommRing R] {n : ℕ}

theorem idem_mul (φ : R) (hφ : φ * φ = φ) (A B : Matrix (Fin n) (Fin n) R)
    (h : A * B = 1) : (φ • A + (1 - φ) • (1 : Matrix (Fin n) (Fin n) R)) * (φ • B + (1 - φ) • 1) = 1 := by
  have h1 : φ * (1 - φ) = 0 := by rw [mul_sub, mul_one, hφ, sub_self]
  have h2 : (1 - φ) * φ = 0 := by rw [mul_comm, h1]
  have h3 : (1 - φ) * (1 - φ) = 1 - φ := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [add_mul, mul_add, smul_mul_smul_comm, h, h1, h2, h3, hφ, zero_smul, mul_one, add_zero, zero_add]
  rw [← add_smul, add_sub_cancel, one_smul]

theorem map_idem {T : Type} [CommRing T] (ψ : R →+* T) (f : R) (M : Matrix (Fin n) (Fin n) R) :
    (f • M + (1 - f) • (1 : Matrix (Fin n) (Fin n) R)).map ψ = ψ f • M.map ψ + (1 - ψ f) • 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, map_add (f := _),
    map_mul, map_sub, map_one]
  split_ifs <;> simp

theorem idem_unitary (σ : R →+* R) (ε : R) (hε : σ ε = ε) (hεε : ε * ε = ε) (J M : Matrix (Fin n) (Fin n) R)
    (h : Formalism.UG.cT σ M * J * M = J) :
    Formalism.UG.cT σ (ε • M + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) * J * (ε • M + (1 - ε) • 1) = J :=
  _root_.GlobalTheory.TruncationIsometry.cut_isometry σ ε hε hεε J M h

end GlobalTheory.GfCut

open GlobalTheory.GfCut in
theorem GlobalTheory.GfCut.exists_cut : ∀ {D : D7} (T : HSp D) (g : GA D T) (ε : AE D), g ∈ GfC T → ε * ε = ε → cA D ε = ε → ∃ k : GA D T, k ∈ GfC T ∧ Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
  intro D T g ε hg hεε hε
  set M := Formalism.L2.Theta.mt T g with hM
  have hinv : M * ((matHom T g)⁻¹).1 = 1 := (matHom T g).mul_inv
  have hinv' : ((matHom T g)⁻¹).1 * M = 1 := (matHom T g).inv_mul
  let K : GL (Fin T.rank) (AE D) := ⟨ε • M + (1 - ε) • 1, ε • ((matHom T g)⁻¹).1 + (1 - ε) • 1,
    idem_mul ε hεε _ _ hinv, idem_mul ε hεε _ _ hinv'⟩
  have hgU : Formalism.UG.cT (cA D) M * T.gram.map (incA D) * M = T.gram.map (incA D) :=
    (show HR (AF D.host.F) D.sp.cm.sig T.gram from g).2
  have hKU : K ∈ HR (AF D.host.F) D.sp.cm.sig T.gram :=
    idem_unitary (cA D) ε hε hεε _ M hgU
  let k : GA D T := (⟨K, hKU⟩ : HR (AF D.host.F) D.sp.cm.sig T.gram)
  refine ⟨k, ?_, rfl⟩
  have hg1 : infHom T g = 1 := hg
  show infHom T k = 1
  have hg2 := congrArg Units.val hg1
  apply Units.ext
  change (ε • M + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))).map _ = 1
  rw [map_idem]
  change M.map _ = 1 at hg2
  rw [hg2, ← add_smul, add_sub_cancel, one_smul]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElementStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_component_of_group_element : ∀ {D : D7} (T : HSp D) (g : GA D T) (ε : AE D), g ∈ GfC T → ε * ε = ε → cA D ε = ε → ∃ k : GA D T, k ∈ GfC T ∧ Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
  first | exact @GlobalTheory.GfCut.exists_cut | exact GlobalTheory.GfCut.exists_cut | (intros; apply GlobalTheory.GfCut.exists_cut <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem exists_finite_support {ι : Type} {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    (x : ⨂[ℂ] i, E i) : ∃ F : ∀ i, Submodule ℂ (E i), (∀ i, FiniteDimensional ℂ (F i)) ∧
      ∀ G : ∀ i, Submodule ℂ (E i), (∀ i, F i ≤ G i) →
        x ∈ LinearMap.range (PiTensorProduct.map fun i => (G i).subtype) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine ⟨fun i => ℂ ∙ f i, fun i => inferInstance, fun G hG => ?_⟩
    refine LinearMap.mem_range.mpr
      ⟨r • PiTensorProduct.tprod ℂ (fun i => (⟨f i, hG i (Submodule.mem_span_singleton_self (f i))⟩ : G i)), ?_⟩
    rw [map_smul, PiTensorProduct.map_tprod]
    rfl
  | add x y hx hy =>
    obtain ⟨F₁, h₁, k₁⟩ := hx
    obtain ⟨F₂, h₂, k₂⟩ := hy
    refine ⟨fun i => F₁ i ⊔ F₂ i, fun i => ?_, fun G hG => ?_⟩
    · haveI := h₁ i
      haveI := h₂ i
      infer_instance
    · exact add_mem (k₁ G fun i => le_trans le_sup_left (hG i)) (k₂ G fun i => le_trans le_sup_right (hG i))

theorem ellT_pure (M : DSModel V S) (w v : ∀ τ, M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, ⟪w τ, v τ⟫_ℂ := by
  unfold ellT
  rw [PiTensorProduct.lift.tprod]
  simp

private lemma eq_zero_of_ellT_map_eq_zero (M : DSModel V S) {K : D.what₂.Tau → Type} [∀ τ, NormedAddCommGroup (K τ)]
    [∀ τ, InnerProductSpace ℂ (K τ)] [hK : ∀ τ, FiniteDimensional ℂ (K τ)] (j : ∀ τ, K τ →ₗ[ℂ] M.H τ)
    (hj : ∀ τ a b, ⟪j τ a, j τ b⟫_ℂ = ⟪a, b⟫_ℂ) (z : ⨂[ℂ] τ, K τ)
    (hz : ∀ w, ellT M w (PiTensorProduct.map j z) = 0) : z = 0 := by
  classical
  let b := fun τ => stdOrthonormalBasis ℂ (K τ)
  let B := Basis.piTensorProduct (fun τ => (b τ).toBasis)
  have key : ∀ p, B.coord p = ellT M (fun τ => j τ (b τ (p τ))) ∘ₗ PiTensorProduct.map j := by
    intro p
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, Module.Basis.coord_apply, B,
      Basis.piTensorProduct_repr_tprod_apply, PiTensorProduct.map_tprod, ellT_pure, hj,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  refine B.forall_coord_eq_zero_iff.mp fun p => ?_
  rw [key, LinearMap.comp_apply]
  exact hz _

theorem ellT_separates (M : DSModel V S) (x : ⨂[ℂ] τ, M.H τ) (hx : ∀ w, ellT M w x = 0) : x = 0 := by
  obtain ⟨F, hF, hx'⟩ := exists_finite_support x
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp (hx' F fun _ => le_rfl)
  have hy : y = 0 := eq_zero_of_ellT_map_eq_zero M (K := fun τ => F τ) (hK := hF) (fun τ => (F τ).subtype)
    (fun τ a b => rfl) y hx
  rw [hy, map_zero]

theorem inclT_injective (M : DSModel V S) : Function.Injective (inclT M) := by
  unfold inclT
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨F, hF, hy'⟩ := exists_finite_support y
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp (hy' F fun _ => le_rfl)
  have hz : z = 0 := eq_zero_of_ellT_map_eq_zero M (K := fun τ => F τ) (hK := hF)
    (fun τ => (M.sm τ).subtype ∘ₗ (F τ).subtype) (fun τ a b => rfl) z (by
      intro w
      rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hy, map_zero])
  rw [hz, map_zero]

theorem fr_conj_mem (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have hPQ : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  rw [← M.fr_gram τ] at hg'
  show Formalism.REAL.inUJ (M.ε τ) _
  unfold Formalism.REAL.inUJ
  calc (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹)
      = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ := by rw [hg']
    _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (M.ε τ) := by rw [hPQ]; simp

open Classical in
theorem actT_pure (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : ∀ ρ, M.H ρ) :
    actT M τ g (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ (M.rep τ g (v τ))) := by
  unfold actT
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases h : ρ = τ
  · subst h
    simp
  · simp [Function.update_of_ne h]

theorem tensorLaw : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), TensorLaw M := by
  intro D V S M
  classical
  refine ⟨fun x hx => ellT_separates M x hx, inclT_injective M, ?_, ?_, ?_⟩
  · intro τ
    obtain ⟨-, -, ⟨⟨h1, -⟩, -⟩, -⟩ := M.ds τ
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
    have hr : M.rep τ 1 = 1 := by
      show M.σ τ (M.fr τ * 1 * (M.fr τ)⁻¹) = 1
      rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd, h1]
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.id_apply]
    rw [actT_pure]
    simp [hr]
  · intro τ g hg g' hg'
    obtain ⟨-, -, ⟨⟨-, hmul⟩, -⟩, -⟩ := M.ds τ
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
    have hQP : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hd
    have hsplit : M.fr τ * (g * g') * (M.fr τ)⁻¹ =
        (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * g' * (M.fr τ)⁻¹) := by
      calc M.fr τ * (g * g') * (M.fr τ)⁻¹ = M.fr τ * g * ((M.fr τ)⁻¹ * M.fr τ) * g' * (M.fr τ)⁻¹ := by
            rw [hQP, Matrix.mul_one, Matrix.mul_assoc (M.fr τ) g g']
        _ = _ := by simp only [Matrix.mul_assoc]
    have hr : M.rep τ (g * g') = (M.rep τ g).comp (M.rep τ g') := by
      show M.σ τ (M.fr τ * (g * g') * (M.fr τ)⁻¹) = (M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)).comp (M.σ τ (M.fr τ * g' * (M.fr τ)⁻¹))
      rw [hsplit]
      exact hmul _ (fr_conj_mem M τ hg) _ (fr_conj_mem M τ hg')
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
    rw [actT_pure, actT_pure, actT_pure, hr]
    congr 1
    simp [Function.update_idem]
  · intro τ g _ w
    obtain ⟨hc, -⟩ := M.ds τ
    haveI : CompleteSpace (M.H τ) := hc
    refine ⟨Function.update w τ (ContinuousLinearMap.adjoint (M.rep τ g) (w τ)), ?_⟩
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
    rw [actT_pure, ellT_pure, ellT_pure]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    by_cases h : ρ = τ
    · subst h
      simp [ContinuousLinearMap.adjoint_inner_left]
    · simp [Function.update_of_ne h]

end GlobalTheory.Chain.RealIt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_pureInnerProducts_tensorProduct : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), TensorLaw M := by
  first | exact @GlobalTheory.Chain.RealIt.tensorLaw | exact GlobalTheory.Chain.RealIt.tensorLaw | (intros; apply GlobalTheory.Chain.RealIt.tensorLaw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTwoDiagBlocksProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTwoDiagBlocksProperties
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv.TwoBlockDet

def lowEquiv {n r : ℕ} (hr : r ≤ n) : Fin r ≃ {a : Fin n // a.val < r} where
  toFun i := ⟨Fin.castLE hr i, i.2⟩
  invFun a := ⟨a.1.val, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem det_eq_mul {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (g : GL (Fin n) κ) (h : g ∈ blockTri (blk2 r)) :
    Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) * dBlk (blk2 r) 1 g := by
  apply Units.ext
  rw [Units.val_mul, diag_block_det_val 1 h, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    upper_block_val_submatrix hr h, Matrix.twoBlockTriangular_det (g : Matrix (Fin n) (Fin n) κ) (fun a : Fin n => a.val < r)
      (fun i hi j hj => h (by simp [blk2, hi, hj]))]
  congr 1
  · rw [← Matrix.det_submatrix_equiv_self (lowEquiv hr)]
    rfl
  · rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight
      (show ∀ a : Fin n, blk2 r a = 1 ↔ ¬ a.val < r from fun a => by unfold blk2; split_ifs with h <;> simp [h]))]
    rfl

theorem blockPartitionOf_eq_twoBlock (r t : ℕ) : (blkOf r t : Fin (r + t) → ℕ) = blk2 r := by
  funext a
  unfold blkOf blk2
  split_ifs with h
  · rfl
  · have := a.2
    rw [Nat.div_eq_of_lt (by omega)]

theorem firstDiagBlock_full_rank_eq_self {κ : Type} [CommRing κ] {n : ℕ} (hr : n ≤ n) (g : GL (Fin n) κ) : upperLeftBlock hr g = g := by
  have h : g ∈ blockTri (blk2 n) := fun i j hij => by simp [blk2] at hij
  apply Units.ext
  rw [upper_block_val_submatrix hr h]
  rfl

theorem det_blocks : ∀ (κ : Type) [CommRing κ] (n r t : ℕ) (hr : r ≤ n) (g : GL (Fin n) κ), (g ∈ blockTri (blk2 r) → Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) * dBlk (blk2 r) 1 g) ∧ (n = r + t → g ∈ blockTri (blkOf r t) → dBlk (blkOf r t) 1 g = dBlk (blk2 r) 1 g) ∧ (n = r → Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) = Matrix.GeneralLinearGroup.det g) := by
  intro κ _ n r t hr g
  refine ⟨det_eq_mul hr g, fun e _ => ?_, fun e => ?_⟩
  · subst e
    rw [blockPartitionOf_eq_twoBlock]
  · subst e
    rw [firstDiagBlock_full_rank_eq_self]

end GlobalTheory.VecInv.TwoBlockDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTwoDiagBlocksPropertiesStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_twoDiagBlocks_properties : ∀ (κ : Type) [CommRing κ] (n r t : ℕ) (hr : r ≤ n) (g : GL (Fin n) κ), (g ∈ blockTri (blk2 r) → Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) * dBlk (blk2 r) 1 g) ∧ (n = r + t → g ∈ blockTri (blkOf r t) → dBlk (blkOf r t) 1 g = dBlk (blk2 r) 1 g) ∧ (n = r → Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) = Matrix.GeneralLinearGroup.det g) := by
  first | exact @GlobalTheory.VecInv.TwoBlockDet.det_blocks | exact GlobalTheory.VecInv.TwoBlockDet.det_blocks | (intros; apply GlobalTheory.VecInv.TwoBlockDet.det_blocks <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeOfOddExponentSum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeOfOddExponentSum
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaTildeOddParity

theorem isEta_sq (D : D7) (η : (AF D.host.F)ˣ →* Circle) (h : IsEta D η) (a : (AF D.host.F)ˣ) : η a ^ 2 = 1 := by
  obtain ⟨-, -, hnorm, -⟩ := h
  have hn := hnorm (idF D a)
  rw [Formalism.L2.Theta.norm_idF, map_pow] at hn
  exact hn

private theorem hasInfQ_half_of_isEtaT (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (h : Formalism.L2.Host.IsEtaT D.host χ) :
    χ.HasInfQ (tauE D) (fun _ => 1 / 2) := by
  unfold Formalism.L2.Host.HChar.HasInfQ
  refine ⟨fun _ => 1, fun _ => by norm_num, ?_⟩
  intro k
  rw [h.inf k]
  symm
  exact Fintype.prod_equiv D.eTau _ _ (fun _ => rfl)

private theorem one_mem_intAE_twisted_operators (D : D7) : 1 ∈ intAE D := by
  apply AddSubgroup.subset_closure
  rw [Set.mem_setOf_eq]
  refine ⟨1, ?_, 1, ?_⟩
  · intro v
    first
      | exact one_mem _
      | (rw [map_one]; exact one_mem _)
      | simp [evalV]
  · rw [Algebra.TensorProduct.one_def]
    all_goals simp

theorem isEtaTilde_of_odd : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → Formalism.L2.Host.IsEtaT D.host χ → ∀ (μ : (AE D)ˣ →* Circle) (n m : ℕ), ResEta D μ n → ResEta D (μ * c⁻¹) m → Odd (n + m) → IsEtaTilde D c := by
  intro D c χ hc hχ μ n m hμ hμc hodd
  unfold IsEtaTilde
  refine ⟨hc.1, ?_, ?_, fun τ => GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D c χ (fun _ => 1 / 2) hc
    (hasInfQ_half_of_isEtaT D χ hχ) τ⟩
  ·
    intro x h1 h2 h3
    refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D c χ hc (fun P => ?_) 1 (fun P _ => hχ.unr P) x ⟨h1, h2, h3⟩
      ⟨finPart D (x : AE D) - 1, sub_mem h2 (one_mem_intAE_twisted_operators D), by rw [one_smul]⟩
    intro y hy _
    exact hχ.unr P y hy
  ·
    unfold ResEta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome at hμ hμc ⊢
    refine ⟨hμ.1, fun η hη a => ?_⟩
    have e1 : μ (idF D a) = η a ^ n := hμ.2 η hη a
    have e2 : (μ * c⁻¹) (idF D a) = η a ^ m := hμc.2 η hη a
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, e1] at e2
    have hs : η a ^ 2 = 1 := isEta_sq D η hη a
    have hi : (η a ^ m)⁻¹ = η a ^ m := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, ← two_mul, pow_mul, hs, one_pow]
    have hc' : c (idF D a) = η a ^ n * (η a ^ m)⁻¹ := by
      rw [← e2, mul_inv_rev, inv_inv, mul_comm (c _), mul_inv_cancel_left]
    obtain ⟨k, hk⟩ := hodd
    show c (idF D a) = η a ^ 1
    rw [pow_one, hc', hi, ← pow_add, hk, pow_succ, pow_mul, hs, one_pow, one_mul]

end GlobalTheory.EtaTildeOddParity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeOfOddExponentSumStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramifiedEtaTilde_of_odd_exponentSum : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → Formalism.L2.Host.IsEtaT D.host χ → ∀ (μ : (AE D)ˣ →* Circle) (n m : ℕ), ResEta D μ n → ResEta D (μ * c⁻¹) m → Odd (n + m) → IsEtaTilde D c := by
  first | exact @GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd | exact GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd | (intros; apply GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentComponentMemFrameStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentComponentMemFrameStabilizer
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompStab

theorem idem_mul {R : Type} [CommRing R] {n : ℕ} (φ : R) (hφ : φ * φ = φ) (A B : Matrix (Fin n) (Fin n) R)
    (h : A * B = 1) : (φ • A + (1 - φ) • (1 : Matrix (Fin n) (Fin n) R)) * (φ • B + (1 - φ) • 1) = 1 := by
  have h1 : φ * (1 - φ) = 0 := by rw [mul_sub, mul_one, hφ, sub_self]
  have h2 : (1 - φ) * φ = 0 := by rw [mul_comm, h1]
  have h3 : (1 - φ) * (1 - φ) = 1 - φ := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [add_mul, mul_add, smul_mul_smul_comm, h, h1, h2, h3, hφ, zero_smul, mul_one, add_zero, zero_add]
  rw [← add_smul, add_sub_cancel, one_smul]

theorem map_idem {R T : Type} [CommRing R] [CommRing T] {n : ℕ} (ψ : R →+* T) (f : R)
    (M : Matrix (Fin n) (Fin n) R) :
    (f • M + (1 - f) • (1 : Matrix (Fin n) (Fin n) R)).map ψ = ψ f • M.map ψ + (1 - ψ f) • 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, map_add (f := _),
    map_mul, map_sub, map_one]
  split_ifs <;> simp

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem comp_mem_St (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (φ : Formalism.L2.Herm.intAf F E) (hφ : φ * φ = φ)
    (x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hS : x ∈ St β)
    (h : x'.1 = (φ : E ⊗[F] Formalism.L2.Herm.Af F) • x.1 + (1 - (φ : E ⊗[F] Formalism.L2.Herm.Af F)) • 1) : x' ∈ St β := by
  obtain ⟨y, rfl⟩ := hS
  refine ⟨⟨φ • y.1 + (1 - φ) • 1, φ • (y⁻¹).1 + (1 - φ) • 1, idem_mul φ hφ _ _ y.mul_inv,
    idem_mul φ hφ _ _ y.inv_mul⟩, Units.ext ?_⟩
  rw [h]
  show β.1 * (φ • y.1 + (1 - φ) • (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))).map
      (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 =
    (φ : E ⊗[F] Formalism.L2.Herm.Af F) • (β.1 * y.1.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1) + _
  rw [map_idem, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Units.mul_inv]
  rfl

theorem comm_int {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E}
    (hz : z ∈ AddSubgroup.closure {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E |
      ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}) :
    (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E z : E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.intAf F E := by
  refine AddSubgroup.closure_induction (p := fun z _ =>
    (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E z : E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.intAf F E) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨a, ha, x, rfl⟩
    have : (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E (a ⊗ₜ[F] (x : E)) : E ⊗[F] Formalism.L2.Herm.Af F) =
        ((oToS F E x : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * ((1 : E) ⊗ₜ[F] a) := by
      rw [oToS_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]; rfl
    rw [this]
    exact Subring.mul_mem _ (oToS F E x).2 (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
  · rw [map_zero]; exact Subring.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add (f := _)]; exact Subring.add_mem _ ha hb
  · intro a _ ha
    rw [map_neg]; exact Subring.neg_mem _ ha

end General

theorem component_mem_St : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g g' : GA D V) (f : AE D), f * f = f → finE V g ∈ St β → Formalism.L2.Theta.mt V g' = f • Formalism.L2.Theta.mt V g + (1 - f) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → finE V g' ∈ St β := by
  intro D V β g g' f hf hg h
  let ψ : AE D →+* Lev.EAf D := (swapAE D).comp (finPart D)
  have hi : ψ f ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    comm_int (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D f) (by rw [← RingHom.map_mul, hf]))
  refine comp_mem_St β ⟨ψ f, hi⟩ (Subtype.ext ?_) (finE V g) _ hg ?_
  · show ψ f * ψ f = ψ f
    rw [← RingHom.map_mul, hf]
  · show (Formalism.L2.Theta.mt V g').map ψ = ψ f • (Formalism.L2.Theta.mt V g).map ψ + (1 - ψ f) • 1
    rw [h, map_idem]

end GlobalTheory.CompStab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentComponentMemFrameStabilizerStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentComponent_mem_frameStabilizer : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g g' : GA D V) (f : AE D), f * f = f → finE V g ∈ St β → Formalism.L2.Theta.mt V g' = f • Formalism.L2.Theta.mt V g + (1 - f) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → finE V g' ∈ St β := by
  first | exact @GlobalTheory.CompStab.component_mem_St | exact GlobalTheory.CompStab.component_mem_St | (intros; apply GlobalTheory.CompStab.component_mem_St <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceWeilRepLatticeVacuumCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceWeilRepLatticeVacuumCharacter
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv


open GlobalTheory.SplitScalar GlobalTheory.SplitHecke in
theorem om_latVac_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e, IsSplitIdem D e → ∀ g h, Formalism.L2.Theta.SuppAt e S g → Formalism.L2.Theta.SuppAt e T h → (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • f := by
  intro D ψ S T ΛS ΛT χS χT om hW hS hT e he g h hg hh hlat x y hx hy f hf hv

  set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ

  obtain ⟨hdual, -, -⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hW.std hS hT
  have hdd : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1 := fun u hu u' hu' =>
    (hdual u (GlobalTheory.SplitScalar.latO_fin hu)).1 hu u' hu'
  have he' : IsSplitIdem D (cA D e) := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have hst : ∀ u ∈ Λ, cA D e • u ∈ Λ := GlobalTheory.SplitScalar.idem_smul_mem he'.1
  have hst' : ∀ u ∈ Λ, cA D (cA D e) • u ∈ Λ := by
    rw [GlobalTheory.DualPairCheck.cA_cA]; exact GlobalTheory.SplitScalar.idem_smul_mem he.1

  have hd : ∀ y, IsHalf e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1 :=
    fun y hy hyn => GlobalTheory.SplitScalar.exists_dual_half he hdual hst hy hyn
  have hd' : ∀ y, IsHalf (cA D e) y → y ∉ Λ → ∃ l ∈ Λ, IsHalf e l ∧ ψ (symplO S T l y) ≠ 1 := by
    intro y hy hyn
    have hex := GlobalTheory.SplitScalar.exists_dual_half he' hdual hst' hy hyn
    rwa [GlobalTheory.DualPairCheck.cA_cA] at hex

  have hback : ∀ w, actO S T g h (actO S T g⁻¹ h⁻¹ w) = w := fun w => by
    simpa using GlobalTheory.SplitHecke.actO_inv_actO g⁻¹ h⁻¹ w
  have hmem : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ Λ ↔ w ∈ Λ := fun w => by
    have hw := hlat (actO S T g⁻¹ h⁻¹ w)
    rwa [hback] at hw

  have hR : ∀ u ∈ ({0} : Finset (WO S T)), actO S T g⁻¹ h⁻¹ u ∈ Λ ∧ IsHalf e u := by
    intro u hu
    rw [Finset.mem_singleton] at hu
    subst hu
    exact ⟨(hmem 0).2 (zero_mem _), GlobalTheory.SplitScalar.isHalf_zero e⟩
  have hRu : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ Λ → IsHalf e w → ∃! v, v ∈ ({0} : Finset (WO S T)) ∧ w - v ∈ Λ := by
    intro w hw _
    refine ⟨0, ⟨Finset.mem_singleton_self _, by simpa using (hmem w).1 hw⟩, ?_⟩
    rintro v ⟨hv0, -⟩
    exact Finset.mem_singleton.1 hv0
  have hle : ∀ w ∈ Λ, IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ Λ := fun w hw _ => (hmem w).2 hw
  obtain ⟨r, hr, hom⟩ := GlobalTheory.SplitHecke.om_eq_smul_sum hW he hdd hd hd' hg hh hx hy hR hRu hle
  have key : om (g, h) f = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) • f := by
    have hk := hom f hf (fun u hu hue => hv.2 e he u hu hue) (fun u hu hue => hv.2 (cA D e) he' u hu hue)
    rwa [Finset.sum_singleton, GlobalTheory.WeilVacMove.heisO_zero] at hk

  by_cases hf0 : f = 0
  · subst hf0
    simp
  obtain ⟨htop, hlc, hsc, ht2, hdisc, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI := htop
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI := hdisc
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, h1⟩, hN⟩ :=
    GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (ratL T S) K hK hcov
  haveI := hμ
  have hper := GlobalTheory.WeilVacMove.norm_periodic hW.std hf
  obtain ⟨N, hNf⟩ := hN f hf.cont hper
  obtain ⟨-, -, hI, -⟩ := hNf μ 𝓕 hμ h𝓕
  have hu := hW.om_unit μ 𝓕 hμ h𝓕 (g, h) f hf
  rw [key] at hu
  have hpt : ∀ w, ‖(((r : ℂ) * (splitFacO χS χT x y : ℂ)) • f) w‖ₑ ^ 2 =
      ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖ₑ ^ 2 * ‖f w‖ₑ ^ 2 := fun w => by
    rw [Pi.smul_apply, smul_eq_mul, enorm_mul (a := (r : ℂ) * (splitFacO χS χT x y : ℂ)), mul_pow]
  simp_rw [hpt] at hu
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top), hI, h1, one_mul] at hu
  have hN0 : (N : ENNReal) ≠ 0 := by
    intro hz
    apply hf0
    have h0 : ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = 0 := by rw [hI, hz, mul_zero]
    rw [lintegral_eq_zero_iff' (hf.cont.measurable.enorm.pow_const 2).aemeasurable] at h0
    apply GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 f hf.cont hper
    filter_upwards [h0] with w hw
    simpa using hw
  have hnorm : ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hs1 : ‖(splitFacO χS χT x y : ℂ)‖ = 1 := by
      first
        | exact Circle.norm_coe _
        | exact Circle.abs_coe _
        | simp
    rw [hs1, mul_one]
  have hr1 : r = 1 := by
    have hc : ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖₊ ^ 2 = 1 := by
      rw [enorm_eq_nnnorm] at hu
      have hN0' : N ≠ 0 := fun hz => hN0 (by rw [hz]; rfl)
      have h2 : ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖₊ ^ 2 * N = 1 * N := by
        rw [one_mul]; exact_mod_cast hu
      exact mul_right_cancel₀ hN0' h2
    have hc' : ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖ ^ 2 = 1 := by
      rw [← coe_nnnorm]
      exact_mod_cast hc
    rw [hnorm] at hc'
    nlinarith
  rw [key, hr1]
  simp

end GlobalTheory.VecInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceWeilRepLatticeVacuumCharacterStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_weilRep_latticeVacuum_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e, IsSplitIdem D e → ∀ g h, Formalism.L2.Theta.SuppAt e S g → Formalism.L2.Theta.SuppAt e T h → (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • f := by
  first | exact @GlobalTheory.VecInv.om_latVac_split | exact GlobalTheory.VecInv.om_latVac_split | (intros; apply GlobalTheory.VecInv.om_latVac_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GUnitOfModels
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem gUnit_of_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.toRealDat.IsModels → R.PGUnit F := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hM
  have hE := GlobalTheory.norm_gE_rows R.toRealDat hM.HE hM.gE hM.ν0
  have hW := GlobalTheory.gW_norm_eq R.toRealDat hM.HW hM.gW hM.νW
  refine ⟨fun g x y => ?_, fun j g x y => ?_⟩
  ·     exact congrArg _ (LinearIsometry.inner_map_map (⟨R.gE g, hE g⟩ : R.HE.H →ₗᵢ[ℂ] R.HE.H) (Tw.out x) (Tw.out y))
  ·     exact congrArg _ (LinearIsometry.inner_map_map
      (⟨R.gW j (sg0 D A3.A) g, hW j (sg0 D A3.A) g⟩ : (R.HW j (sg0 D A3.A)).H →ₗᵢ[ℂ] (R.HW j (sg0 D A3.A)).H) (Tw.out x) (Tw.out y))

end GlobalTheory
end
