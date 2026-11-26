module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMatrixOfOrthonormalLocalBasisAllPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOfFinOrderOfCompactConjMemUnitaryRationalPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLocalBasisStandardCoordLeOneInert
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLocalBasisStandardCoordLeOneInert
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

theorem norm_hK_le_one : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → ∀ w a b₀ i, ‖hK D lam P P' b w a b₀ i‖ ≤ 1 := by
  intro D p _ lam σ hσ hcl N N' L L' P P' hP hP' r b hb w a b₀ i
  obtain ⟨h2, hq, -⟩ := GlobalTheory.InertCompare.ne_of_inert D p hcl
  obtain ⟨ρ, hρ⟩ := exists_ringHom_rhoK D lam σ hσ hcl w
  set τ := tauPl D w with hτ
  have hρK : rhoK D lam w = fun y => ρ y := funext fun y => (hρ y).1
  have hρC : ∀ y, ((ρ y : MaximalUnramifiedExtension p) : ℂ_[p]) = GlobalTheory.KerStd.UnitaryMat.rho D lam τ y := fun y => by
    rw [(hρ y).2, GlobalTheory.KerStd.UnitaryMat.tauEmb_eq]
  have hPW : LocBasisW D (GlobalTheory.KerStd.UnitaryMat.rho D lam τ) L (P τ) := by
    rw [← GlobalTheory.KerStd.UnitaryMat.tauEmb_eq]; exact hP.1 τ
  have hP'W : LocBasisW D (GlobalTheory.KerStd.UnitaryMat.rho D lam τ) L' (P' τ) := by
    rw [← GlobalTheory.KerStd.UnitaryMat.tauEmb_eq]; exact hP'.1 τ
  have hdet : IsUnit (P' τ).det := isUnit_iff_ne_zero.2 hP'W.1
  have hQ : (P' τ)⁻¹ * P' τ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hinv : ((P' τ).map (fun y => ρ y))⁻¹ = ((P' τ)⁻¹).map (fun y => ρ y) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [show ((P' τ)⁻¹).map (fun y => ρ y) = ((P' τ)⁻¹).map ρ from rfl,
      show (P' τ).map (fun y => ρ y) = (P' τ).map ρ from rfl, ← Matrix.map_mul, hQ,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := by
    rw [GlobalTheory.PadicPlaceBound.norm_prime_padicComplex]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hint := GlobalTheory.KerStd.UnitaryMat.intIn_of_locBasis hp1
    (fun x hx => GlobalTheory.EigenGenerator.norm_padicEmbedding_le_one_of_mem_inverseHalfDifferent D h2 hq _ hx) hQ hPW hP'W hb i b₀ a
  have e : hK D lam P P' b w a b₀ i = ρ (((P' τ)⁻¹ * b i * P τ) b₀ a) := by
    unfold hK
    rw [← hτ, hρK, hinv]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
  show ‖((hK D lam P P' b w a b₀ i : MaximalUnramifiedExtension p) : ℂ_[p])‖ ≤ 1
  rw [e, hρC]
  exact hint

end GlobalTheory.KerStd.HypCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLocalBasisStandardCoordLeOneInertStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_localBasis_standardCoord_le_one_inert : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → ∀ w a b₀ i, ‖hK D lam P P' b w a b₀ i‖ ≤ 1 := by
  first | exact @GlobalTheory.KerStd.HypCoord.norm_hK_le_one | exact GlobalTheory.KerStd.HypCoord.norm_hK_le_one | (intros; apply GlobalTheory.KerStd.HypCoord.norm_hK_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearFormsHyperbolicCoordinatesEqTarget
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearFormsHyperbolicCoordinatesEqTarget
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord

theorem sum_coef_fOf (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (hdual : ∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 →
      ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0)
    (r₀ : R) (a : Fin N) (b : Fin N') (i : Fin r) (s : ZMod (nP D p)) :
    ∑ k, (if s.val % 2 = 0 then fOf D p σ om R g ((r₀, k), a, b) i * σ^[s.val] (oms k)
      else fOf' D p σ oms R g ((r₀, k), a, b) i * σ^[s.val] (om k)) = g (OrbitPlaces.orbMap D p r₀ s) a b i := by
  by_cases hs : s.val % 2 = 0
  · simp only [hs, if_true, fOf, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_eq_single s]
    · simp only [hs, if_true]
      have h := hdual s s rfl
      rw [if_pos rfl] at h
      calc ∑ k, σ^[s.val] (om k) * g (OrbitPlaces.orbMap D p r₀ s) a b i * σ^[s.val] (oms k)
          = g (OrbitPlaces.orbMap D p r₀ s) a b i * ∑ k, σ^[s.val] (om k) * σ^[s.val] (oms k) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = _ := by rw [h, mul_one]
    · intro t _ hts
      by_cases ht : t.val % 2 = 0
      · simp only [ht, if_true]
        have h := hdual t s (by rw [ht, hs])
        rw [if_neg hts] at h
        calc ∑ k, σ^[t.val] (om k) * g (OrbitPlaces.orbMap D p r₀ t) a b i * σ^[s.val] (oms k)
            = g (OrbitPlaces.orbMap D p r₀ t) a b i * ∑ k, σ^[t.val] (om k) * σ^[s.val] (oms k) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
          _ = 0 := by rw [h, mul_zero]
      · simp [ht]
    · intro h; exact absurd (Finset.mem_univ s) h
  · simp only [hs, if_false, fOf', Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_eq_single s]
    · simp only [hs, if_false]
      have h := hdual s s rfl
      rw [if_pos rfl] at h
      calc ∑ k, σ^[s.val] (oms k) * g (OrbitPlaces.orbMap D p r₀ s) a b i * σ^[s.val] (om k)
          = g (OrbitPlaces.orbMap D p r₀ s) a b i * ∑ k, σ^[s.val] (om k) * σ^[s.val] (oms k) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = _ := by rw [h, mul_one]
    · intro t _ hts
      by_cases ht : t.val % 2 = 0
      · simp [ht]
      · simp only [ht, if_false]
        have h := hdual s t (by omega)
        rw [if_neg (Ne.symm hts)] at h
        calc ∑ k, σ^[t.val] (oms k) * g (OrbitPlaces.orbMap D p r₀ t) a b i * σ^[s.val] (om k)
            = g (OrbitPlaces.orbMap D p r₀ t) a b i * ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
          _ = 0 := by rw [h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ s) h

theorem hypZ_term (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {n : Type} (f f' : (R × Fin (nP D p / 2)) × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension p) (i : n)
    (e : (R × Fin (nP D p / 2)) × Fin N0 × Fin N1) :
    MvPowerSeries.C (f e i : ℂ_[p]) * linEv D p σ (oms e.1.2) e.1.1 e.2.1 e.2.2 +
      MvPowerSeries.C (f' e i : ℂ_[p]) * linOd D p σ (om e.1.2) e.1.1 e.2.1 e.2.2 =
    ∑ s : ZMod (nP D p), MvPowerSeries.C (((if s.val % 2 = 0 then f e i * σ^[s.val] (oms e.1.2)
      else f' e i * σ^[s.val] (om e.1.2) : MaximalUnramifiedExtension p)) : ℂ_[p]) * MvPowerSeries.X (OrbitPlaces.orbMap D p e.1.1 s, e.2.1, e.2.2) := by
  unfold linEv linOd
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s.val % 2 = 0
  · simp [hs, map_mul, mul_assoc]
  · simp [hs, map_mul, mul_assoc]

theorem bijective_orbMap (D : D7) (p : ℕ) (R : Finset (OrbitPlaces.Pl D)) (hR : OrbitPlaces.IsReps D p R) :
    Function.Bijective (fun y : R × ZMod (nP D p) => OrbitPlaces.orbMap D p y.1 y.2) := by
  constructor
  · rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ h
    simp only at h
    have hr : (r₁ : OrbitPlaces.Pl D) = r₂ := by
      obtain ⟨r0, _, hu⟩ := hR (OrbitPlaces.orbMap D p r₁ s₁)
      have e1 := hu r₁ ⟨r₁.2, s₁.val, rfl⟩
      have e2 := hu r₂ ⟨r₂.2, s₂.val, h.symm⟩
      rw [e1, e2]
    have hr' : r₁ = r₂ := Subtype.ext hr
    subst hr'
    have hs : s₁ = s₂ := ZMod.val_injective _ (posPl_inj D p r₁ _ _ (ZMod.val_lt s₁) (ZMod.val_lt s₂) h)
    rw [hs]
  · intro z
    obtain ⟨r0, ⟨hr0, e, he⟩, _⟩ := hR z
    refine ⟨(⟨r0, hr0⟩, (e : ZMod (nP D p))), ?_⟩
    show posPl D p r0 (e : ZMod (nP D p)).val = z
    rw [ZMod.val_natCast, posPl_mod, he]

end GlobalTheory.KerStd.HypCoord

namespace GlobalTheory.KerStd.HypCoord

theorem hypZ_fOf (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (hR : OrbitPlaces.IsReps D p R)
    (hdual : ∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 →
      ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0) (i : Fin r) :
    hypZ D p σ om oms R (fOf D p σ om R g) (fOf' D p σ oms R g) i =
      ∑ j : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C ((g j.1 j.2.1 j.2.2 i : MaximalUnramifiedExtension p) : ℂ_[p]) * MvPowerSeries.X j := by
  set F : (R × Fin (nP D p / 2)) × Fin N × Fin N' → ZMod (nP D p) → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    fun e s => MvPowerSeries.C (((if s.val % 2 = 0 then fOf D p σ om R g e i * σ^[s.val] (oms e.1.2)
      else fOf' D p σ oms R g e i * σ^[s.val] (om e.1.2) : MaximalUnramifiedExtension p)) : ℂ_[p]) *
        MvPowerSeries.X (OrbitPlaces.orbMap D p e.1.1 s, e.2.1, e.2.2) with hF
  have hB : Function.Bijective (fun y : (R × ZMod (nP D p)) × Fin N × Fin N' => ((OrbitPlaces.orbMap D p y.1.1 y.1.2, y.2) :
      OrbitPlaces.Pl D × Fin N × Fin N')) :=
    (bijective_orbMap D p R hR).prodMap Function.bijective_id
  let eqv : ((R × ZMod (nP D p)) × Fin N × Fin N') × Fin (nP D p / 2) ≃
      ((R × Fin (nP D p / 2)) × Fin N × Fin N') × ZMod (nP D p) :=
    { toFun := fun y => (((y.1.1.1, y.2), y.1.2), y.1.1.2)
      invFun := fun x => (((x.1.1.1, x.2), x.1.2), x.1.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold hypZ
  calc ∑ e, (MvPowerSeries.C (fOf D p σ om R g e i : ℂ_[p]) * linEv D p σ (oms e.1.2) e.1.1 e.2.1 e.2.2 +
        MvPowerSeries.C (fOf' D p σ oms R g e i : ℂ_[p]) * linOd D p σ (om e.1.2) e.1.1 e.2.1 e.2.2)
      = ∑ e, ∑ s, F e s := Finset.sum_congr rfl fun e _ => hypZ_term D p σ om oms R _ _ i e
    _ = ∑ x : ((R × Fin (nP D p / 2)) × Fin N × Fin N') × ZMod (nP D p), F x.1 x.2 := (Fintype.sum_prod_type' F).symm
    _ = ∑ y : ((R × ZMod (nP D p)) × Fin N × Fin N') × Fin (nP D p / 2), F ((y.1.1.1, y.2), y.1.2) y.1.1.2 :=
        (Fintype.sum_equiv eqv _ _ fun _ => rfl).symm
    _ = ∑ y : (R × ZMod (nP D p)) × Fin N × Fin N', ∑ k, F ((y.1.1, k), y.2) y.1.2 :=
        Fintype.sum_prod_type' (fun (y : (R × ZMod (nP D p)) × Fin N × Fin N') (k : Fin (nP D p / 2)) => F ((y.1.1, k), y.2) y.1.2)
    _ = ∑ y : (R × ZMod (nP D p)) × Fin N × Fin N',
          MvPowerSeries.C ((g (OrbitPlaces.orbMap D p y.1.1 y.1.2) y.2.1 y.2.2 i : MaximalUnramifiedExtension p) : ℂ_[p]) *
            MvPowerSeries.X ((OrbitPlaces.orbMap D p y.1.1 y.1.2, y.2) : OrbitPlaces.Pl D × Fin N × Fin N') := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← sum_coef_fOf D p σ om oms R g hdual y.1.1 y.2.1 y.2.2 i y.1.2, hF]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [← Finset.sum_mul, ← map_sum]
        congr 2
        push_cast
        rfl
    _ = _ := hB.sum_comp (fun j : OrbitPlaces.Pl D × Fin N × Fin N' =>
          MvPowerSeries.C ((g j.1 j.2.1 j.2.2 i : MaximalUnramifiedExtension p) : ℂ_[p]) * MvPowerSeries.X j)

theorem linForm_hypZ : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (κ : Type) (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p) (Λ : κ → Fin r → ℂ_[p]) (T : κ → OrbitPlaces.Pl D × Fin N × Fin N' → ℂ_[p]), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → (∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 → ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0) → (∀ q z a b, ∑ i, Λ q i * ((g z a b i : MaximalUnramifiedExtension p) : ℂ_[p]) = T q (z, a, b)) → ∀ q, ∑ i, MvPowerSeries.C (Λ q i) * hypZ D p σ om oms R (fOf D p σ om R g) (fOf' D p σ oms R g) i = ∑ j, MvPowerSeries.C (T q j) * MvPowerSeries.X j := by
  intro D p _ σ om oms R N N' r κ g Λ T _ hR hdual hT q
  simp only [hypZ_fOf D p σ om oms R g hR hdual, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hT q j.1 j.2.1 j.2.2, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mul_assoc]

end GlobalTheory.KerStd.HypCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearFormsHyperbolicCoordinatesEqTargetStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearForms_hyperbolicCoordinates_eq_target : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (κ : Type) (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p) (Λ : κ → Fin r → ℂ_[p]) (T : κ → OrbitPlaces.Pl D × Fin N × Fin N' → ℂ_[p]), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → (∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 → ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0) → (∀ q z a b, ∑ i, Λ q i * ((g z a b i : MaximalUnramifiedExtension p) : ℂ_[p]) = T q (z, a, b)) → ∀ q, ∑ i, MvPowerSeries.C (Λ q i) * hypZ D p σ om oms R (fOf D p σ om R g) (fOf' D p σ oms R g) i = ∑ j, MvPowerSeries.C (T q j) * MvPowerSeries.X j := by
  first | exact @GlobalTheory.KerStd.HypCoord.linForm_hypZ | exact GlobalTheory.KerStd.HypCoord.linForm_hypZ | (intros; apply GlobalTheory.KerStd.HypCoord.linForm_hypZ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaTauOrthonormalBasisSumCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaTauOrthonormalBasisSumCoordinates
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

theorem map_inv_field_hom {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  have h1 : A.adjugate.map f = (A.map f).adjugate := by
    have := RingHom.map_adjugate f A; simpa [RingHom.mapMatrix_apply] using this
  have h2 : (A.map f).det = f A.det := by
    have := RingHom.map_det f A; simpa [RingHom.mapMatrix_apply] using this.symm
  rw [Matrix.inv_def, Matrix.inv_def, Matrix.map_smul' _ _ _ (map_mul f), h1, h2, Ring.inverse_eq_inv', Ring.inverse_eq_inv', map_inv₀]

theorem lamB_sum_gK : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), Formalism.L2.KerInert.RepFrame.LamONB D lam b → ∀ (k : D.what₂.Tau × Fin N' × Fin N) (z : Bool × HH D) (a : Fin N) (b₀ : Fin N'), ∑ i, Formalism.L2.KerInert.RepFrame.lamB D lam b k i * ((gK D lam P P' b z a b₀ i : MaximalUnramifiedExtension p) : ℂ_[p]) = chgB D lam P P' k ((0 : ZMod 1), (tauPl D z, a, b₀)) := by
  intro D p _ lam σ hσ hcl N N' L L' P P' _ _ r b hb k z a b₀
  obtain ⟨ρ, hρ⟩ := exists_ringHom_rhoK D lam σ hσ hcl z
  set τ := tauPl D z with hτ
  let ι : MaximalUnramifiedExtension p →+* ℂ_[p] := (MaximalUnramifiedExtension p).subtype
  have hfun : ∀ y, ι (ρ y) = tauEmb D lam τ y := fun y => (hρ y).2
  have hrho : rhoK D lam z = fun y => ρ y := funext fun y => (hρ y).1
  have hinv : ∀ a a₁, ((((P τ).map (rhoK D lam z))⁻¹ a a₁ : MaximalUnramifiedExtension p) : ℂ_[p]) =
      ((P τ).map (tauEmb D lam τ))⁻¹ a a₁ := by
    intro a a₁
    have e2 : (P τ).map (tauEmb D lam τ) = ((P τ).map ρ).map ι := by
      ext u v; simp [hfun]
    rw [hrho, e2, ← map_inv_field_hom ι]; rfl
  have hg : ∀ i, ((gK D lam P P' b z a b₀ i : MaximalUnramifiedExtension p) : ℂ_[p]) = ∑ b₁ : Fin N', ∑ a₁ : Fin N,
      Formalism.L2.KerInert.RepFrame.lamBc D lam b (τ, b₁, a₁) i *
        (tauEmb D lam τ (P' τ b₁ b₀) * ((P τ).map (tauEmb D lam τ))⁻¹ a a₁) := by
    intro i
    rw [gK, ← hτ]
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, coe_rhoK D lam σ hσ hcl, hinv, mul_assoc, ← hτ]
    rfl
  simp_rw [hg, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun b₁ _ => Finset.sum_comm).trans ?_
  simp_rw [← mul_assoc, ← Finset.sum_mul, hb k]
  rcases k with ⟨t, c, d⟩
  by_cases ht : t = τ
  · subst ht
    simp [chgB, Prod.ext_iff, ite_and]
  · simp [chgB, Prod.ext_iff, ht, Ne.symm ht]

end GlobalTheory.KerStd.HypCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaTauOrthonormalBasisSumCoordinatesStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambdaTau_orthonormalBasis_sum_coordinates : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), Formalism.L2.KerInert.RepFrame.LamONB D lam b → ∀ (k : D.what₂.Tau × Fin N' × Fin N) (z : Bool × HH D) (a : Fin N) (b₀ : Fin N'), ∑ i, Formalism.L2.KerInert.RepFrame.lamB D lam b k i * ((gK D lam P P' b z a b₀ i : MaximalUnramifiedExtension p) : ℂ_[p]) = chgB D lam P P' k ((0 : ZMod 1), (tauPl D z, a, b₀)) := by
  first | exact @GlobalTheory.KerStd.HypCoord.lamB_sum_gK | exact GlobalTheory.KerStd.HypCoord.lamB_sum_gK | (intros; apply GlobalTheory.KerStd.HypCoord.lamB_sum_gK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesDual
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesDual
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

theorem posPl_inj_lt (D : D7) (p : ℕ) (z : OrbitPlaces.Pl D) {a b : ℕ} (hab : a ≤ b) (hb : b < nP D p)
    (he : posPl D p z a = posPl D p z b) : a = b := by
  have h1 : posPl D p (posPl D p z a) (b - a) = posPl D p z a := by
    rw [posPl_add, Nat.add_sub_cancel' hab, he]
  have hd := posPl_fix D p _ _ h1
  have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  omega

theorem orbMap_inj (D : D7) (p : ℕ) (z : OrbitPlaces.Pl D) {s s' : ZMod (nP D p)}
    (he : posPl D p z s.val = posPl D p z s'.val) : s = s' := by
  apply ZMod.val_injective
  rcases le_total s.val s'.val with h | h
  · exact posPl_inj_lt D p z h (ZMod.val_lt _) he
  · exact (posPl_inj_lt D p z h (ZMod.val_lt _) he.symm).symm

theorem iterate_mul_ringHom {K : Type*} [Semiring K] (σ : K →+* K) (m : ℕ) (x y : K) :
    σ^[m] (x * y) = σ^[m] x * σ^[m] y := by
  rw [← RingHom.coe_pow, map_mul]

theorem fOf_fOf'_dual : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → TrDual (nP D p) σ om oms → (∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i) → (∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0) → ∀ e e', ∑ i, σ (fOf D p σ om R g e i) * fOf' D p σ oms R g e' i = if e = e' then 1 else 0 := by
  intro D p _ σ om oms R N N' r g h hOK hR hTr hσg hpair e e'
  obtain ⟨⟨⟨r0, hr0⟩, k⟩, a, b⟩ := e
  obtain ⟨⟨⟨r1, hr1⟩, k'⟩, a', b'⟩ := e'
  obtain ⟨m, hm⟩ := hOK.even
  have hn2 := hOK.two
  have hval : ∀ t : ZMod (nP D p), t.val % 2 = 0 → (t + 1).val = t.val + 1 := by
    intro t ht
    have hlt := ZMod.val_lt t
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (show 1 < nP D p by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have reps : ∀ (m0 m1 : ℕ), posPl D p r0 m0 = posPl D p r1 m1 → r0 = r1 := fun m0 m1 he =>
    (hR (posPl D p r1 m1)).unique ⟨hr0, m0, he⟩ ⟨hr1, m1, rfl⟩
  have hf : ∀ i, σ (fOf D p σ om R g ((⟨r0, hr0⟩, k), a, b) i) = ∑ t : ZMod (nP D p),
      (if t.val % 2 = 0 then σ^[t.val + 1] (om k) else 0) * h (posPl D p r0 (t.val + 1)) a b i := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [fOf, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs with ht
    · rw [map_mul, hσg, ← Function.iterate_succ_apply' σ, OrbitPlaces.orbMap, posPl_add]
    · simp
  have hf' : ∀ i, fOf' D p σ oms R g ((⟨r1, hr1⟩, k'), a', b') i = ∑ t : ZMod (nP D p),
      (if t.val % 2 = 0 then 0 else σ^[t.val] (oms k')) * g (posPl D p r1 t.val) a' b' i := by
    intro i
    simp only [fOf', OrbitPlaces.orbMap]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp
  have h2 : ∑ i, σ (fOf D p σ om R g ((⟨r0, hr0⟩, k), a, b) i) * fOf' D p σ oms R g ((⟨r1, hr1⟩, k'), a', b') i =
      ∑ t : ZMod (nP D p), ∑ t' : ZMod (nP D p), (if t.val % 2 = 0 then σ^[t.val + 1] (om k) else 0) *
        (if t'.val % 2 = 0 then 0 else σ^[t'.val] (oms k')) *
        (if posPl D p r0 (t.val + 1) = posPl D p r1 t'.val ∧ a = a' ∧ b = b' then 1 else 0) := by
    rw [Finset.sum_congr rfl fun i _ => by rw [hf i, hf' i, Finset.sum_mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t' _ => ?_
    rw [← hpair, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have key : ∀ t t' : ZMod (nP D p), (if t.val % 2 = 0 then σ^[t.val + 1] (om k) else 0) *
        (if t'.val % 2 = 0 then 0 else σ^[t'.val] (oms k')) *
        (if posPl D p r0 (t.val + 1) = posPl D p r1 t'.val ∧ a = a' ∧ b = b' then 1 else 0) =
      if t' = t + 1 then (if t.val % 2 = 0 then σ^[t.val + 1] (om k * oms k') else 0) *
        (if r0 = r1 ∧ a = a' ∧ b = b' then 1 else 0) else 0 := by
    intro t t'
    by_cases ht : t.val % 2 = 0
    · have h1 := hval t ht
      by_cases htt : t' = t + 1
      · subst htt
        have hodd : ¬ (t.val + 1) % 2 = 0 := by omega
        rw [if_pos rfl, h1, if_pos ht, if_pos ht, if_neg hodd, iterate_mul_ringHom]
        by_cases hc : r0 = r1 ∧ a = a' ∧ b = b'
        · obtain ⟨rfl, rfl, rfl⟩ := hc
          simp
        · rw [if_neg hc, if_neg]
          rintro ⟨hp, ha, hb⟩
          exact hc ⟨reps _ _ hp, ha, hb⟩
      · rw [if_neg htt]
        by_cases ht' : t'.val % 2 = 0
        · simp [ht']
        · by_cases hc : posPl D p r0 (t.val + 1) = posPl D p r1 t'.val
          · exfalso
            have hr := reps _ _ hc
            subst hr
            rw [← h1] at hc
            exact htt (orbMap_inj D p r0 hc).symm
          · simp [hc]
    · simp [ht]
  rw [h2, Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => key t t']
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_mul]
  have h3 : ∑ t : ZMod (nP D p), (if t.val % 2 = 0 then σ^[t.val + 1] (om k * oms k') else 0) =
      σ (∑ t : ZMod (nP D p), if t.val % 2 = 0 then σ^[t.val] (om k * oms k') else 0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs
    · rw [Function.iterate_succ_apply']
    · simp
  rw [h3, hTr.2 k k']
  by_cases hk : k = k' <;> by_cases hr : r0 = r1 <;> by_cases ha : a = a' <;> by_cases hb : b = b' <;>
    simp [hk, hr, ha, hb]

end GlobalTheory.KerStd.HypCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesDualStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolicCoordinates_dual : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → TrDual (nP D p) σ om oms → (∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i) → (∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0) → ∀ e e', ∑ i, σ (fOf D p σ om R g e i) * fOf' D p σ oms R g e' i = if e = e' then 1 else 0 := by
  first | exact @GlobalTheory.KerStd.HypCoord.fOf_fOf'_dual | exact GlobalTheory.KerStd.HypCoord.fOf_fOf'_dual | (intros; apply GlobalTheory.KerStd.HypCoord.fOf_fOf'_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesIntegralSigmaSqFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesIntegralSigmaSqFixed
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord

theorem norm_iterate_le_one {p : ℕ} [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (hσ : ∀ x : MaximalUnramifiedExtension p, ‖x‖ ≤ 1 → ‖σ x‖ ≤ 1) (x : MaximalUnramifiedExtension p) (hx : ‖x‖ ≤ 1) (k : ℕ) : ‖σ^[k] x‖ ≤ 1 := by
  induction k with
  | zero => simpa using hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact hσ _ ih

theorem val_add_two_eq (D : D7) (p : ℕ) (t : ZMod (nP D p)) : (t + 2).val = (t.val + 2) % nP D p := by
  have : t + 2 = ((t.val + 2 : ℕ) : ZMod (nP D p)) := by push_cast; simp [ZMod.natCast_zmod_val]
  rw [this, ZMod.val_natCast]

theorem val_add_two_mod_two (D : D7) (p : ℕ) (hO : OrbitPlaces.OrbOK D p) (t : ZMod (nP D p)) :
    (t + 2).val % 2 = t.val % 2 := by
  have h2 : (2 : ℕ) ∣ nP D p := even_iff_two_dvd.mp hO.even
  rw [val_add_two_eq, Nat.mod_mod_of_dvd _ h2]
  omega

theorem sigma_sq_term (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (c : MaximalUnramifiedExtension p)
    (hc : σ^[nP D p] c = c) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (hg : ∀ z a b i, σ (σ (g z a b i)) = g (posPl D p z 2) a b i) (z : OrbitPlaces.Pl D) (a : Fin N) (b : Fin N')
    (i : Fin r) (t : ZMod (nP D p)) :
    σ (σ (σ^[t.val] c * g (OrbitPlaces.orbMap D p z t) a b i)) =
      σ^[(t + 2).val] c * g (OrbitPlaces.orbMap D p z (t + 2)) a b i := by
  rw [map_mul, map_mul, hg]
  simp only [OrbitPlaces.orbMap]
  rw [val_add_two_eq, posPl_mod, posPl_add]
  congr 1
  rw [(show Function.IsPeriodicPt σ (nP D p) c from hc).iterate_mod_apply,
    Function.iterate_succ_apply', Function.iterate_succ_apply']

theorem sigma_sq_sum_shift (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (F : ZMod (nP D p) → MaximalUnramifiedExtension p) (hF : ∀ t, σ (σ (F t)) = F (t + 2)) :
    σ (σ (∑ t, F t)) = ∑ t, F t := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  simp_rw [hF]
  exact Fintype.sum_equiv (Equiv.addRight 2) _ _ (fun _ => rfl)

theorem fOf_integral_sigma_sq : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → (∀ x : MaximalUnramifiedExtension p, ‖x‖ ≤ 1 → ‖σ x‖ ≤ 1) → OwOK (nP D p) σ om oms → (∀ z a b i, ‖g z a b i‖ ≤ 1) → (∀ z a b i, σ (σ (g z a b i)) = g (posPl D p z 2) a b i) → (∀ e i, ‖fOf D p σ om R g e i‖ ≤ 1 ∧ σ (σ (fOf D p σ om R g e i)) = fOf D p σ om R g e i) ∧ (∀ e i, ‖fOf' D p σ oms R g e i‖ ≤ 1 ∧ σ (σ (fOf' D p σ oms R g e i)) = fOf' D p σ oms R g e i) := by
  intro D p _ σ om oms R N N' r g hO hσ hw hgn hg
  have hterm : ∀ (c : MaximalUnramifiedExtension p), ‖c‖ ≤ 1 → ∀ (z : OrbitPlaces.Pl D) (a : Fin N) (b : Fin N') (i : Fin r) (t : ZMod (nP D p)),
      ‖σ^[t.val] c * g (OrbitPlaces.orbMap D p z t) a b i‖ ≤ 1 := by
    intro c hc z a b i t
    rw [norm_mul]
    exact mul_le_one₀ (norm_iterate_le_one σ hσ c hc _) (norm_nonneg _) (hgn _ _ _ _)
  refine ⟨fun e i => ⟨?_, ?_⟩, fun e i => ⟨?_, ?_⟩⟩
  · unfold fOf
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun t _ => ?_
    split_ifs
    · exact hterm _ (hw.1 _).1 _ _ _ _ _
    · simp
  · unfold fOf
    refine sigma_sq_sum_shift D p σ _ fun t => ?_
    rw [val_add_two_mod_two D p hO t]
    split_ifs
    · exact sigma_sq_term D p σ _ (hw.2 _).1 g hg _ _ _ _ t
    · simp
  · unfold fOf'
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun t _ => ?_
    split_ifs
    · simp
    · exact hterm _ (hw.1 _).2 _ _ _ _ _
  · unfold fOf'
    refine sigma_sq_sum_shift D p σ _ fun t => ?_
    rw [val_add_two_mod_two D p hO t]
    split_ifs
    · simp
    · exact sigma_sq_term D p σ _ (hw.2 _).2 g hg _ _ _ _ t

end GlobalTheory.KerStd.HypCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesIntegralSigmaSqFixedStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolicCoordinates_integral_sigma_sq_fixed : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → (∀ x : MaximalUnramifiedExtension p, ‖x‖ ≤ 1 → ‖σ x‖ ≤ 1) → OwOK (nP D p) σ om oms → (∀ z a b i, ‖g z a b i‖ ≤ 1) → (∀ z a b i, σ (σ (g z a b i)) = g (posPl D p z 2) a b i) → (∀ e i, ‖fOf D p σ om R g e i‖ ≤ 1 ∧ σ (σ (fOf D p σ om R g e i)) = fOf D p σ om R g e i) ∧ (∀ e i, ‖fOf' D p σ oms R g e i‖ ≤ 1 ∧ σ (σ (fOf' D p σ oms R g e i)) = fOf' D p σ oms R g e i) := by
  first | exact @GlobalTheory.KerStd.HypCoord.fOf_integral_sigma_sq | exact GlobalTheory.KerStd.HypCoord.fOf_integral_sigma_sq | (intros; apply GlobalTheory.KerStd.HypCoord.fOf_integral_sigma_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesIsotropic
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesIsotropic
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

theorem posPl_succ_ne_of_parity (D : D7) (p : ℕ) (R : Finset (OrbitPlaces.Pl D)) (hev : Even (nP D p))
    (hR : OrbitPlaces.IsReps D p R) {r r' : OrbitPlaces.Pl D} (hr : r ∈ R) (hr' : r' ∈ R) {s s' : ℕ}
    (hs : s < nP D p) (hs' : s' < nP D p) (hpar : s % 2 = s' % 2) :
    posPl D p (posPl D p r s) 1 ≠ posPl D p r' s' := by
  intro h
  rw [posPl_add] at h
  have hrr : r = r' :=
    (hR (posPl D p r' s')).unique ⟨hr, s + 1, h⟩ ⟨hr', s', rfl⟩
  subst hrr
  have hpos : 0 < nP D p := by omega
  have h2 : posPl D p r ((s + 1) % nP D p) = posPl D p r s' := by rw [posPl_mod, h]
  have h3 : (s + 1) % nP D p = s' := posPl_inj D p r _ _ (Nat.mod_lt _ hpos) hs' h2
  obtain ⟨m, hm⟩ := hev
  rcases Nat.lt_or_ge (s + 1) (nP D p) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h3
    omega
  · have hsn : s + 1 = nP D p := by omega
    rw [hsn, Nat.mod_self] at h3
    omega

theorem sum_sigma_comb_mul_comb (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' n : ℕ} (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin n → MaximalUnramifiedExtension p)
    (hev : Even (nP D p)) (hR : OrbitPlaces.IsReps D p R)
    (hg : ∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i)
    (hp : ∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0)
    {r r' : OrbitPlaces.Pl D} (hr : r ∈ R) (hr' : r' ∈ R) (a a' : Fin N) (b b' : Fin N')
    (c c' : ZMod (nP D p) → MaximalUnramifiedExtension p) (q : ℕ)
    (hc : ∀ t, t.val % 2 ≠ q → c t = 0) (hc' : ∀ t, t.val % 2 ≠ q → c' t = 0) :
    ∑ i, σ (∑ t, c t * g (OrbitPlaces.orbMap D p r t) a b i) * ∑ t, c' t * g (OrbitPlaces.orbMap D p r' t) a' b' i = 0 := by
  have hterm : ∀ t t' : ZMod (nP D p),
      ∑ i, (σ (c t) * h (posPl D p (OrbitPlaces.orbMap D p r t) 1) a b i) *
        (c' t' * g (OrbitPlaces.orbMap D p r' t') a' b' i) = 0 := by
    intro t t'
    by_cases h1 : t.val % 2 = q
    · by_cases h2 : t'.val % 2 = q
      · have hne : posPl D p (OrbitPlaces.orbMap D p r t) 1 ≠ OrbitPlaces.orbMap D p r' t' :=
          posPl_succ_ne_of_parity D p R hev hR hr hr' (ZMod.val_lt t) (ZMod.val_lt t') (h1.trans h2.symm)
        have e : ∀ i, (σ (c t) * h (posPl D p (OrbitPlaces.orbMap D p r t) 1) a b i) *
            (c' t' * g (OrbitPlaces.orbMap D p r' t') a' b' i) =
            (σ (c t) * c' t') * (h (posPl D p (OrbitPlaces.orbMap D p r t) 1) a b i *
              g (OrbitPlaces.orbMap D p r' t') a' b' i) := fun i => by ring
        simp only [e]
        rw [← Finset.mul_sum, hp, if_neg (fun hh => hne hh.1), mul_zero]
      · simp [hc' t' h2]
    · simp [hc t h1]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hg, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun t' _ => hterm t t'

theorem fOf_isotropic : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → (∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i) → (∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0) → (∀ e e', ∑ i, σ (fOf D p σ om R g e i) * fOf D p σ om R g e' i = 0) ∧ (∀ e e', ∑ i, σ (fOf' D p σ oms R g e i) * fOf' D p σ oms R g e' i = 0) := by
  intro D p _ σ om oms R N N' r g h hO hR hg hp
  constructor
  · intro e e'
    have key := sum_sigma_comb_mul_comb D p σ R g h hO.even hR hg hp e.1.1.2 e'.1.1.2 e.2.1 e'.2.1 e.2.2 e'.2.2
      (fun t => if t.val % 2 = 0 then σ^[t.val] (om e.1.2) else 0)
      (fun t => if t.val % 2 = 0 then σ^[t.val] (om e'.1.2) else 0) 0
      (fun t ht => if_neg ht) (fun t ht => if_neg ht)
    simpa only [fOf, ite_mul, zero_mul] using key
  · intro e e'
    have key := sum_sigma_comb_mul_comb D p σ R g h hO.even hR hg hp e.1.1.2 e'.1.1.2 e.2.1 e'.2.1 e.2.2 e'.2.2
      (fun t => if t.val % 2 = 0 then 0 else σ^[t.val] (oms e.1.2))
      (fun t => if t.val % 2 = 0 then 0 else σ^[t.val] (oms e'.1.2)) 1
      (fun t ht => if_pos (by omega)) (fun t ht => if_pos (by omega))
    simpa only [fOf', ite_mul, zero_mul] using key

end GlobalTheory.KerStd.HypCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesIsotropicStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolicCoordinates_isotropic : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → (∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i) → (∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0) → (∀ e e', ∑ i, σ (fOf D p σ om R g e i) * fOf D p σ om R g e' i = 0) ∧ (∀ e e', ∑ i, σ (fOf' D p σ oms R g e i) * fOf' D p σ oms R g e' i = 0) := by
  first | exact @GlobalTheory.KerStd.HypCoord.fOf_isotropic | exact GlobalTheory.KerStd.HypCoord.fOf_isotropic | (intros; apply GlobalTheory.KerStd.HypCoord.fOf_isotropic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalLocalBasisCoordinatesDual
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalLocalBasisCoordinatesDual
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord.Pair

theorem sum_bilin {R : Type*} [CommRing R] {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (F : κ → R) (G : μ → R) (X : ι → κ → R) (Y : ι → μ → R) :
    ∑ i, (∑ k, F k * X i k) * (∑ m, G m * Y i m) = ∑ k, ∑ m, F k * G m * ∑ i, X i k * Y i m := by
  have h1 : ∀ i, (∑ k, F k * X i k) * (∑ m, G m * Y i m) = ∑ k, ∑ m, F k * G m * (X i k * Y i m) := fun i => by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

end GlobalTheory.KerStd.HypCoord.Pair


open GlobalTheory.KerStd.HypCoord.Pair in
theorem GlobalTheory.KerStd.HypCoord.hK_gK_dual : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), Formalism.L2.KerInert.RepFrame.LamONB D lam b → ∀ w z a b₀ a₁ b₁, ∑ i, hK D lam P P' b w a b₀ i * gK D lam P P' b z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b₀ = b₁ then 1 else 0 := by
  intro D p _ lam σ hσ hcl N N' L L' P P' hP hP' r b hL w z a b₀ a₁ b₁

  have hunit : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E) (L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
      StdBases D lam L₀ Q → ∀ v, IsUnit ((Q (tauPl D v)).map (rhoK D lam v)).det := by
    intro n Q L₀ hQ v
    obtain ⟨ρ, hρ⟩ := exists_ringHom_rhoK D lam σ hσ hcl v
    have hf : rhoK D lam v = ⇑ρ := funext fun y => (hρ y).1
    have h1 := hQ.2.1 hcl v
    have hdet : IsUnit (Q (tauPl D v)).det :=
      Matrix.isUnit_det_of_left_inverse h1
    rw [hf, show ((Q (tauPl D v)).map ⇑ρ).det = ρ (Q (tauPl D v)).det from (RingHom.map_det ρ _).symm]
    exact hdet.map ρ

  have hker : ∀ (k m : Fin N' × Fin N), ∑ i, rhoK D lam w (b i k.1 k.2) * rhoK D lam z (D.host.conj (b i m.1 m.2)) =
      if (tauPl D w, k.1, k.2) = (tauPl D z, m.1, m.2) then 1 else 0 := by
    intro k m
    have e := hL (tauPl D w, k.1, k.2) (tauPl D z, m.1, m.2)
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [MulMemClass.coe_mul, coe_rhoK D lam σ hσ hcl]
    convert e using 1 <;> first | rfl | (split_ifs <;> simp)
  set A := ((P' (tauPl D w)).map (rhoK D lam w))⁻¹ with hA
  set B := ((P (tauPl D z)).map (rhoK D lam z))⁻¹ with hB
  have eh : ∀ i, hK D lam P P' b w a b₀ i =
      ∑ k : Fin N' × Fin N, (A b₀ k.1 * rhoK D lam w (P (tauPl D w) k.2 a)) * rhoK D lam w (b i k.1 k.2) := fun i => by
    rw [hK, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have eg : ∀ i, gK D lam P P' b z a₁ b₁ i =
      ∑ m : Fin N' × Fin N, (rhoK D lam z (P' (tauPl D z) m.1 b₁) * B a₁ m.2) * rhoK D lam z (D.host.conj (b i m.1 m.2)) := fun i => by
    rw [gK, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp only [eh, eg]
  rw [sum_bilin]
  simp only [hker]
  by_cases hwz : w = z
  · subst hwz
    have hsimp : ∀ k m : Fin N' × Fin N, ((tauPl D w, k.1, k.2) = (tauPl D w, m.1, m.2)) ↔ k = m := by
      intro k m
      simp [Prod.ext_iff]
    simp only [hsimp, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have e1 : ∑ k : Fin N' × Fin N, A b₀ k.1 * rhoK D lam w (P (tauPl D w) k.2 a) *
        (rhoK D lam w (P' (tauPl D w) k.1 b₁) * B a₁ k.2) =
        (A * (P' (tauPl D w)).map (rhoK D lam w)) b₀ b₁ * (B * (P (tauPl D w)).map (rhoK D lam w)) a₁ a := by
      rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul_sum, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by simp only [Matrix.map_apply]; ring
    rw [e1, hA, hB, Matrix.nonsing_inv_mul _ (hunit P' L' hP' w), Matrix.nonsing_inv_mul _ (hunit P L hP w),
      Matrix.one_apply, Matrix.one_apply]
    by_cases h1 : b₀ = b₁ <;> by_cases h2 : a = a₁ <;> simp [h1, h2, eq_comm]
  · have hne : tauPl D w ≠ tauPl D z := fun h => hwz ((tauPl_bij D).1 h)
    rw [if_neg (fun h => hwz h.1)]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg (fun h => hne (congrArg Prod.fst h)), mul_zero]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalLocalBasisCoordinatesDualStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalLocalBasis_coordinates_dual : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), Formalism.L2.KerInert.RepFrame.LamONB D lam b → ∀ w z a b₀ a₁ b₁, ∑ i, hK D lam P P' b w a b₀ i * gK D lam P P' b z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b₀ = b₁ then 1 else 0 := by
  first | exact @GlobalTheory.KerStd.HypCoord.hK_gK_dual | exact GlobalTheory.KerStd.HypCoord.hK_gK_dual | (intros; apply GlobalTheory.KerStd.HypCoord.hK_gK_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesScaledEqOrthonormalBasisSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesScaledEqOrthonormalBasisSeries
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord

theorem mvPowerSeries_subst_linearForm {σ τ : Type} [Fintype σ] {K : Type} [Field K] {a : σ → MvPowerSeries τ K}
    (ha : MvPowerSeries.HasSubst a) (α : σ → K) :
    MvPowerSeries.subst a (∑ j, MvPowerSeries.C (α j) * MvPowerSeries.X j : MvPowerSeries σ K) =
      ∑ j, MvPowerSeries.C (α j) * a j := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_C]

theorem stdSer_scaled_eq_thOrth : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' r : ℕ) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hz : Fin r → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), (∀ i, MvPowerSeries.constantCoeff (hz i) = 0) → (∀ k, ∑ i, MvPowerSeries.C (Formalism.L2.KerInert.RepFrame.lamB D lam b k i) * hz i = ∑ j : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C (chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) * MvPowerSeries.X j) → ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst hz (thOrth D lam c b G) := by
  intro D p _ lam N N' r P P' b hz hz0 hlin c G
  have hs1 : MvPowerSeries.HasSubst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
      (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => by simp
  have hs2 : MvPowerSeries.HasSubst hz := MvPowerSeries.hasSubst_of_constantCoeff_zero hz0
  have e : ∀ x : ℂ_[p], algebraMap ℂ_[p] (MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) x = MvPowerSeries.C x := fun x => rfl
  rw [stdSer, atLin, thOrth, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp) hs1,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp) hs2]
  congr 1
  funext k
  simp only [e, one_mul]
  rw [mvPowerSeries_subst_linearForm hs1, mvPowerSeries_subst_linearForm hs2]
  have h1 : (∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * hz i :
      MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) =
      MvPowerSeries.C c * ∑ i, MvPowerSeries.C (Formalism.L2.KerInert.RepFrame.lamB D lam b k i) * hz i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, mul_assoc]
    rfl
  rw [h1, hlin k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.KerStd.HypCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesScaledEqOrthonormalBasisSeriesStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardSeries_scaled_eq_orthonormalBasisSeries : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' r : ℕ) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hz : Fin r → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), (∀ i, MvPowerSeries.constantCoeff (hz i) = 0) → (∀ k, ∑ i, MvPowerSeries.C (Formalism.L2.KerInert.RepFrame.lamB D lam b k i) * hz i = ∑ j : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C (chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) * MvPowerSeries.X j) → ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst hz (thOrth D lam c b G) := by
  first | exact @GlobalTheory.KerStd.HypCoord.stdSer_scaled_eq_thOrth | exact GlobalTheory.KerStd.HypCoord.stdSer_scaled_eq_thOrth | (intros; apply GlobalTheory.KerStd.HypCoord.stdSer_scaled_eq_thOrth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusLiftMovesLetterCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusLiftMovesLetterCoordinates
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord.FrobMove

theorem inv_map_field {E K : Type*} [Field E] [Field K] (f : E →+* K) {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n E) : (M.map f)⁻¹ = M⁻¹.map f := by
  have hd : (M.map f).det = f M.det := (RingHom.map_det f M).symm
  have ha : (M.map f).adjugate = M.adjugate.map f := (RingHom.map_adjugate f M).symm
  rw [Matrix.inv_def, Matrix.inv_def, hd, ha]
  ext i j
  simp [Ring.inverse_eq_inv', map_inv₀]

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x :=
  D.host.φ₀.injective (by
    rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])

theorem frob_moves_coords : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ z a b₀ i, σ (gK D lam P P' b z a b₀ i) = hK D lam P P' b (posPl D p z 1) a b₀ i) ∧ (∀ w a b₀ i, σ (hK D lam P P' b w a b₀ i) = gK D lam P P' b (posPl D p w 1) a b₀ i) := by
  intro D p _ lam σ hσ hcl N N' L L' P P' hP hP' r b
  choose ρ hρ using fun z => exists_ringHom_rhoK D lam σ hσ hcl z
  have hfun : ∀ z, rhoK D lam z = ⇑(ρ z) := fun z => funext fun y => (hρ z y).1
  have hs : ∀ z y, σ (ρ z y) = ρ (posPl D p z 1) (D.host.conj y) := fun z y => by
    rw [← (hρ z y).1, ← (hρ _ _).1]; exact sigma_rhoK D lam σ hσ hcl z y
  have hsm : ∀ {n : ℕ} z (Q : Matrix (Fin n) (Fin n) D.host.E),
      (Q.map (ρ z)).map σ = (Q.map D.host.conj).map (ρ (posPl D p z 1)) := fun z Q => by
    ext i j; simp [hs]
  have hinv : ∀ {n : ℕ} z (Q : Matrix (Fin n) (Fin n) D.host.E) i j,
      σ ((Q.map (ρ z))⁻¹ i j) = ((Q.map D.host.conj).map (ρ (posPl D p z 1)))⁻¹ i j := fun z Q i j => by
    rw [← hsm, inv_map_field σ]; rfl
  have K : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E),
      (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z,
      ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose *
        ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) = 1 := by
    intro n Q hQ z
    have e : ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose *
        ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) =
        ((((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z)).map
          (D.host.conj : D.host.E →+* D.host.E)).map (ρ (posPl D p z 1)) := by
      rw [Matrix.map_mul, Matrix.map_mul]
      congr 1
      ext i j
      simp [conj_conj]
    rw [e, hQ z]
    simp
  have K1 : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E),
      (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z,
      (((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)))⁻¹ =
        ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose := fun Q hQ z =>
    Matrix.inv_eq_left_inv (K Q hQ z)
  have K2 : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E),
      (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z,
      ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) =
        (((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1)))⁻¹).transpose := fun Q hQ z => by
    rw [Matrix.transpose_nonsing_inv]; exact (Matrix.inv_eq_right_inv (K Q hQ z)).symm
  have hPc := hP.2.1 hcl
  have hP'c := hP'.2.1 hcl
  refine ⟨fun z a b₀ i => ?_, fun w a b₀ i => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [gK, hK, hfun, map_sum, map_mul]
      refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun a₁ _ => ?_
      rw [hs, hs, conj_conj, hinv, K1 P hPc z]
      have e2 := congrFun (congrFun (K2 P' hP'c z) b₁) b₀
      simp only [Matrix.map_apply, Matrix.transpose_apply] at e2 ⊢
      rw [e2]; ring
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [gK, hK, hfun, map_sum, map_mul]
      refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun a₁ _ => ?_
      rw [hs, hs, hinv, K1 P' hP'c w]
      have e2 := congrFun (congrFun (K2 P hPc w) a₁) a
      simp only [Matrix.map_apply, Matrix.transpose_apply] at e2 ⊢
      rw [e2]; ring

end GlobalTheory.KerStd.HypCoord.FrobMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusLiftMovesLetterCoordinatesStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusLift_moves_letter_coordinates : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ z a b₀ i, σ (gK D lam P P' b z a b₀ i) = hK D lam P P' b (posPl D p z 1) a b₀ i) ∧ (∀ w a b₀ i, σ (hK D lam P P' b w a b₀ i) = gK D lam P P' b (posPl D p w 1) a b₀ i) := by
  first | exact @GlobalTheory.KerStd.HypCoord.FrobMove.frob_moves_coords | exact GlobalTheory.KerStd.HypCoord.FrobMove.frob_moves_coords | (intros; apply GlobalTheory.KerStd.HypCoord.FrobMove.frob_moves_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardBasesHyperbolicPairOrthonormal
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)


open GlobalTheory.KerStd.HypCoord in
theorem GlobalTheory.KerStd.hyp_of_stdBases : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∀ (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p), OwOK (nP D p) σ om oms → TrDual (nP D p) σ om oms → ∀ (R : Finset (OrbitPlaces.Pl D)), OrbitPlaces.IsReps D p R → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → TaylorLogMetric.Orthonormal D b → ∃ f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p, HypPair σ f f' ∧ ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (hypZ D p σ om oms R f f') (thOrth D lam c b G) := by
  intro D p _ lam σ hσ hO hcl om oms hOw hTr R hR N N' L L' P P' hA hP hP' r b hb ho
  have hcl' : IsResidueClassZero D p ∨ IsSg D p := hcl.elim (fun h => Or.inl h.1) Or.inr
  have hONB : Formalism.L2.KerInert.RepFrame.LamONB D lam b :=
    Formalism.L2.KerInert.RepFrame.lamONB_of_cols D lam b
      (Formalism.L2.KerInert.RepFrame.rank_of_locBasis L L' hA.2.2.1 hA.2.2.2 b hb)
      (Formalism.L2.KerInert.RepFrame.cols_of_trace D (Formalism.L2.KerInert.RepFrame.trace_tau_sum D) lam b ho)
  obtain ⟨hg, hh⟩ := GlobalTheory.T.frobeniusLift_moves_letter_coordinates D p lam σ hσ hcl' N N' L L' P P' hP hP' r b
  have hpair := GlobalTheory.T.orthonormalLocalBasis_coordinates_dual D p lam σ hσ hcl' N N' L L' P P' hP hP' r b hONB
  have hiso := norm_sigma_eq p σ hσ
  have hhint := GlobalTheory.T.norm_localBasis_standardCoord_le_one_inert D p lam σ hσ hcl' N N' L L' P P' hP hP' r b hb
  have hgint : ∀ z a b₀ i, ‖gK D lam P P' b z a b₀ i‖ ≤ 1 := fun z a b₀ i => by
    rw [← hiso, hg]; exact hhint _ _ _ _
  have hg2 : ∀ z a b₀ i, σ (σ (gK D lam P P' b z a b₀ i)) = gK D lam P P' b (posPl D p z 2) a b₀ i :=
    fun z a b₀ i => by rw [hg, hh, posPl_add]
  obtain ⟨hf1, hf2⟩ := GlobalTheory.T.hyperbolicCoordinates_integral_sigma_sq_fixed D p σ om oms R N N' r (gK D lam P P' b) hO
    (fun x hx => by rw [hiso]; exact hx) hOw hgint hg2
  obtain ⟨hi1, hi2⟩ := GlobalTheory.T.hyperbolicCoordinates_isotropic D p σ om oms R N N' r (gK D lam P P' b) (hK D lam P P' b) hO hR hg hpair
  have hd := GlobalTheory.T.hyperbolicCoordinates_dual D p σ om oms R N N' r (gK D lam P P' b) (hK D lam P P' b) hO hR hTr hg hpair
  refine ⟨fOf D p σ om R (gK D lam P P' b), fOf' D p σ oms R (gK D lam P P' b), ⟨hf1, hf2, hi1, hi2, hd⟩, ?_⟩
  have hlin := GlobalTheory.T.linearForms_hyperbolicCoordinates_eq_target D p σ om oms R N N' r _ (gK D lam P P' b) (Formalism.L2.KerInert.RepFrame.lamB D lam b)
    (fun k j => chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) hO hR (GlobalTheory.T.traceDual_expansion_orbitLength D p σ om oms hTr)
    (fun q z a b₀ => GlobalTheory.T.lambdaTau_orthonormalBasis_sum_coordinates D p lam σ hσ hcl' N N' L L' P P' hP hP' r b hONB q z a b₀)
  refine GlobalTheory.T.standardSeries_scaled_eq_orthonormalBasisSeries D p lam N N' r P P' b _ (fun i => ?_) hlin
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hypZ, linEv, linOd, map_sum, map_add (f := _), map_mul, MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_X,
    mul_zero, apply_ite MvPowerSeries.constantCoeff, map_zero, ite_self, Finset.sum_const_zero, add_zero]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardBasesHyperbolicPairOrthonormalStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardSeries_scaled_eq_orthonormalSeries_hyperbolicSubst : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∀ (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p), OwOK (nP D p) σ om oms → TrDual (nP D p) σ om oms → ∀ (R : Finset (OrbitPlaces.Pl D)), OrbitPlaces.IsReps D p R → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → TaylorLogMetric.Orthonormal D b → ∃ f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p, HypPair σ f f' ∧ ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (hypZ D p σ om oms R f f') (thOrth D lam c b G) := by
  first | exact @GlobalTheory.KerStd.hyp_of_stdBases | exact GlobalTheory.KerStd.hyp_of_stdBases | (intros; apply GlobalTheory.KerStd.hyp_of_stdBases <;> assumption)
end
