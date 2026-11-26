module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbAddUp
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbAddOne
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EntAtD
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitSumCount.TauPlBijective
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.PrvFOfOrbitLetterBounds
public import Development.AutomorphicArithmetic.OrbitLabellings.KvalGeThetaOfShape
public import Development.AutomorphicArithmetic.OrbitLabellings.FInertSubEatILeOrbitAverageSubErrors

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.KillSubst
noncomputable section

namespace PI.OrbShared

open MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

variable {σ τ υ R : Type*} [CommRing R]

theorem hasSubst_killCompl (e : υ ↪ τ) {a : σ → MvPowerSeries τ R} (ha : HasSubst a) :
    HasSubst (fun s => killCompl e (a s)) where
  const_coeff s := by
    have h : constantCoeff (killCompl e (a s)) = constantCoeff (a s) := by
      rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
        coeff_killCompl, Finsupp.embDomain_zero]
    rw [h]; exact ha.const_coeff s
  coeff_zero d := by
    refine (ha.coeff_zero (Finsupp.embDomain e d)).subset ?_
    intro s hs
    simpa [coeff_killCompl] using hs

theorem continuous_killCompl [UniformSpace R] [DiscreteUniformity R] (e : υ ↪ τ) :
    Continuous (killCompl (R := R) e : MvPowerSeries τ R → MvPowerSeries υ R) := by
  apply continuous_pi
  intro x
  have : (fun p : MvPowerSeries τ R => (killCompl e p) x) = fun p => coeff (Finsupp.embDomain e x) p := by
    funext p; exact coeff_killCompl p x
  rw [this]
  exact WithPiTopology.continuous_coeff R _

theorem killCompl_subst (e : υ ↪ τ) {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (f : MvPowerSeries σ R) :
    killCompl e (subst a f) = subst (fun s => killCompl e (a s)) f := by
  let _ : UniformSpace R := ⊥
  have _ : DiscreteUniformity R := ⟨rfl⟩
  have hb := hasSubst_killCompl e ha
  rw [comp_subst_apply ha (continuous_killCompl e) f, ← coe_substAlgHom hb, substAlgHom_eq_aeval]

theorem killCompl_eq_subst (e : υ ↪ τ) (f : MvPowerSeries τ R) :
    killCompl e f = subst (fun t => killCompl e (X t : MvPowerSeries τ R)) f := by
  have := killCompl_subst e (HasSubst.X (S := R) (σ := τ)) f
  rw [subst_self] at this
  exact this

end PI.OrbShared
end
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumOrbC
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitSumCount.SizeGe
noncomputable section

open scoped BigOperators
open Classical
open Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace SumOrbCW

variable {D : D7}

theorem size_ge {L : SizeData₂ D} {X : Inst D L} {E : Formalism.MainNotions.OrbitPlaces.Ent D} (hS : Formalism.MainNotions.OrbitPlaces.Shape D L X E)
    (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (z : Bool × HH D) :
    ((D.R.k : ℝ) - 1) * wPl D (i + 1) z ≤ E.size u i z := by
  by_cases ht : IsTopPl D z
  · have h1 := (hS.top u i hi z ht).1
    have h2 := hS.top1 u i hi z ht
    linarith
  · have h1 := (hS.low u i hi z ht).1
    linarith

theorem NN_le (i : ℕ) (hi : i < D.R.m) : (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) ≤ Nm D ^ 2 := by
  have h1 : D.R.N i ≤ D.R.N D.R.m := by
    unfold Formalism.BasicNotions.Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul hi.le le_rfl) _
  have h2 : D.R.N (i + 1) ≤ D.R.N D.R.m := by
    unfold Formalism.BasicNotions.Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul (Nat.succ_le_of_lt hi) le_rfl) _
  unfold Formalism.MainNotions.G.Nm
  rw [sq]
  exact mul_le_mul (by exact_mod_cast h1) (by exact_mod_cast h2) (by positivity) (by positivity)

theorem sumOrbC (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : Formalism.MainNotions.OrbitPlaces.Ent D) (C6 C : ℝ)
    (hS : Formalism.MainNotions.OrbitPlaces.Shape D L X E) (hC : Formalism.MainNotions.OrbitPlaces.CLarge C6 C K ce) : Formalism.MainNotions.OrbitPlaces.ValuationSumBound E L ce C := by
  intro p hp hp5 hc0 hh hpX u i hi
  have hp5' : (5 : ℝ) ≤ p := by exact_mod_cast hp5
  have hq : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hp1 : (1 : ℝ) < p := by linarith

  have ha1 := hS.xa
  have hpa : (p : ℝ) ≤ L.sc.a := le_trans hpX ha1.1
  have hLg : 1 ≤ Real.logb p L.sc.a := by
    rw [Real.le_logb_iff_rpow_le hp1 (by linarith), Real.rpow_one]; exact hpa
  have hlog2 : Real.logb p (L.sc.a ^ 2) = 2 * Real.logb p L.sc.a := by
    unfold Real.logb; rw [Real.log_pow]; push_cast; ring

  set S := ∑ τ : D.what₂.Tau, wj D (i + 1) τ with hSdef
  have hFI : FInert D (i + 1) p = ((D.R.k : ℝ) - 1) * S / ((p : ℝ) ^ 2 - 1) := by
    unfold FInert; rw [if_pos ⟨hc0, hh⟩, hSdef, Finset.mul_sum, Finset.sum_div]
  have hS0 : 0 ≤ S := by
    rw [hSdef, ← sum_wPl D (i + 1)]
    exact Finset.sum_nonneg fun z _ => (hS.wpos i hi z).le
  have hsz : ((D.R.k : ℝ) - 1) * S ≤ ∑ z : Bool × HH D, E.size u i z := by
    rw [hSdef, ← sum_wPl D (i + 1), Finset.mul_sum]
    exact Finset.sum_le_sum fun z _ => size_ge hS u i hi z

  have hCL : C * (2 * Real.logb p L.sc.a + 1) ≤ ce.dig * Real.logb p L.sc.a := by
    have e1 : C * (2 * Real.logb p L.sc.a + 1) ≤ 3 * C * Real.logb p L.sc.a := by
      nlinarith [mul_nonneg hC.nonneg (sub_nonneg.2 hLg)]
    have e2 : 3 * C * Real.logb p L.sc.a ≤ ce.dig * Real.logb p L.sc.a :=
      mul_le_mul_of_nonneg_right hC.dig (by linarith)
    linarith
  have hNN := NN_le (D := D) i hi
  have hf : (0 : ℝ) ≤ D.R.f := by positivity
  have hB : (D.R.f : ℝ) * D.R.N i * D.R.N (i + 1) * (C * (2 * Real.logb p L.sc.a + 1)) ≤
      ((D.R.f : ℝ) * Nm D ^ 2) * (ce.dig * Real.logb p L.sc.a) := by
    rw [mul_assoc (D.R.f : ℝ)]
    refine mul_le_mul (mul_le_mul_of_nonneg_left hNN hf) hCL
      (by nlinarith [hC.nonneg, hLg]) (by positivity)
  unfold EatC Formalism.MainNotions.product_zeroth_first_parts.rho
  rw [hFI, hlog2]
  have hdiv : ((D.R.k : ℝ) - 1) * S / ((p : ℝ) ^ 2 - 1) ≤ 1 / ((p : ℝ) ^ 2 - 1) * ∑ z : Bool × HH D, E.size u i z := by
    rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hsz hq.le
  have hS1 : 0 ≤ S / ((p : ℝ) ^ 2 - 1) := div_nonneg hS0 hq.le
  nlinarith [hdiv, hS1, hB]

end SumOrbCW

end
end

theorem PI.SumOrbC : ∀ (D : Formalism.BasicNotions.D7) (L : Formalism.BasicNotions.SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (K : Formalism.MainNotions.G.Consts) (ce : Formalism.BasicNotions.ErrC) (E : Formalism.MainNotions.OrbitPlaces.Ent D) (C6 C : ℝ), Formalism.MainNotions.OrbitPlaces.Shape D L X E → Formalism.MainNotions.OrbitPlaces.CLarge C6 C K ce → Formalism.MainNotions.OrbitPlaces.ValuationSumBound E L ce C :=
  fun D L X K ce E C6 C hS hC => SumOrbCW.sumOrbC D L X K ce E C6 C hS hC
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbBoundF
theorem PI.OrbBoundF : ∀ (D : Formalism.BasicNotions.D7) (L : Formalism.BasicNotions.SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (K : Formalism.MainNotions.G.Consts) (ce : Formalism.BasicNotions.ErrC) (E : Formalism.MainNotions.OrbitPlaces.Ent D) (C6 C : ℝ), Formalism.MainNotions.OrbitPlaces.OrbitLetterBoundsAll C6 C → Formalism.MainNotions.OrbitPlaces.Shape D L X E → Formalism.MainNotions.OrbitPlaces.CLarge C6 C K ce → Formalism.MainNotions.OrbitPlaces.OrbitValuationBound E X K ce :=
  PI.OrbBoundFW.prvF_of_orbitLetterBounds
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbRestr
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetRestriction.OrbitRestriction
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetRestriction.RestrictedJetEquation
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetRestriction.ConstantCoeffZeroOfVanishing
noncomputable section

open Classical

namespace PI.OrbJet.OrbW

open Formalism.BasicNotions Formalism.MainNotions.G MvPowerSeries Finsupp PI.OrbJet PI.OrbShared

variable {σ τ υ R : Type*} [CommRing R]

theorem killCompl_subst_of (e : υ ↪ τ) (g : τ → MvPowerSeries τ R) (K : υ → MvPowerSeries υ R)
    (hg : HasSubst g) (hK : HasSubst K) (h1 : ∀ w, killCompl e (g (e w)) = K w)
    (h0 : ∀ t, (¬ ∃ w, e w = t) → killCompl e (g t) = 0) (f : MvPowerSeries τ R) :
    killCompl e (subst g f) = subst K (killCompl e f) := by
  have hc : ∀ (F : MvPowerSeries τ R) (x : υ →₀ ℕ),
      coeff x (killCompl e F) = coeff (embDomain e x) F := fun F x => coeff_killCompl F x
  have key : ∀ (x : υ →₀ ℕ) (d : τ →₀ ℕ), coeff (embDomain e x) (d.prod fun s n => g s ^ n) =
      coeff x (d.prod fun s n => killCompl e (g s) ^ n) := by
    intro x d
    rw [← hc, map_finsuppProd]
    simp only [map_pow]
  ext x
  rw [hc, coeff_subst hg, coeff_subst hK]
  simp_rw [key x]
  have hRR : (∑ᶠ d' : υ →₀ ℕ, coeff d' (killCompl e f) • coeff x (d'.prod fun s n => K s ^ n)) =
      ∑ᶠ d ∈ Set.range (embDomain e : (υ →₀ ℕ) → τ →₀ ℕ),
        coeff d f • coeff x (d.prod fun s n => killCompl e (g s) ^ n) := by
    rw [finsum_mem_range (embDomain_injective e)]
    refine finsum_congr fun d' => ?_
    rw [Finsupp.prod_embDomain, hc]
    simp only [h1]
  rw [hRR]
  refine finsum_congr fun d => ?_
  rw [finsum_eq_if]
  split_ifs with hd
  · rfl
  · obtain ⟨t, ht, hnot⟩ : ∃ t ∈ d.support, ¬ ∃ w, e w = t := by
      by_contra hall
      push_neg at hall
      exact hd ⟨_, embDomain_comapDomain (f := e) (g := d) (fun t ht => hall t ht)⟩
    have hz : (d.prod fun s n => killCompl e (g s) ^ n) = 0 :=
      Finset.prod_eq_zero ht (by
        show killCompl e (g t) ^ d t = 0
        rw [h0 t hnot]
        exact zero_pow (Finsupp.mem_support_iff.mp ht))
    rw [hz, map_zero, smul_zero]

theorem cc_jetLogG (l d : ℕ) [Fact l.Prime] {β : Type*} (w : ZMod d × β) :
    constantCoeff (jetLogG l d w) = 0 := by
  show jetLogG l d w 0 = 0
  unfold jetLogG
  refine Finset.sum_eq_zero fun e _ => if_neg fun h => ?_
  exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (Finsupp.single_eq_zero.mp h.symm)

theorem cc_logPl (D : D7) (p : ℕ) [Fact p.Prime] {β : Type} (v : Pl D × β) :
    constantCoeff (logPl D p v) = 0 := by
  show logPl D p v 0 = 0
  unfold logPl
  refine Finset.sum_eq_zero fun e _ => if_neg fun h => ?_
  exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) (Finsupp.single_eq_zero.mp h.symm)

theorem constant_coeff_zero_of_vanishing_alt (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]) (h : OJ.B3 l d be) :
    constantCoeff be = 0 := by
  by_contra hc
  unfold OJ.B3 at h
  have h0 := h 0 (by rwa [coeff_zero_eq_constantCoeff_apply])
  exact h0.1 (by simp [OJ.bideg])

private theorem killCompl_X_of_not_mem_range (e : υ ↪ τ) (t : τ) (ht : ¬ ∃ w, e w = t) :
    killCompl e (X t : MvPowerSeries τ R) = 0 := by
  ext x
  rw [show coeff x (killCompl e (X t : MvPowerSeries τ R)) =
      coeff (embDomain e x) (X t : MvPowerSeries τ R) from coeff_killCompl _ _, coeff_X, if_neg, map_zero]
  intro hx
  have h1 : (embDomain e x) t ≠ 0 := by rw [hx]; simp
  rw [← Finsupp.mem_support_iff, Finsupp.support_embDomain, Finset.mem_map] at h1
  obtain ⟨w, _, hw⟩ := h1
  exact ht ⟨w, hw⟩

theorem killCompl_orbX_off (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (R : Finset (Pl D)) (hR : IsReps D p R)
    {r r' : Pl D} (hr : r ∈ R) (hr' : r' ∈ R) (hne : r' ≠ r) (s : ZMod (nP D p)) (a : Fin N0) (b : Fin N1) :
    killCompl (orbEmb D p r (Fin N0 × Fin N1))
      (X (orbMap D p r' s, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) = 0 := by
  unfold IsReps at hR
  refine killCompl_X_of_not_mem_range _ _ ?_
  rintro ⟨⟨s0, c⟩, hw⟩
  have h1 : orbMap D p r s0 = orbMap D p r' s := congrArg Prod.fst hw
  exact hne ((hR (orbMap D p r' s)).unique ⟨hr, s0.val, h1⟩ ⟨hr', s.val, rfl⟩).symm

theorem hasSubst_orbX (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (r : Pl D) (a : Fin N0) (b : Fin N1) :
    HasSubst (fun s : ZMod (nP D p) =>
      (X (orbMap D p r s, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])) := hasSubst_of_constantCoeff_zero (fun s => constantCoeff_X _)

private theorem coeff_killCompl_subst (e : υ ↪ τ) {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (f : MvPowerSeries σ R) (x : υ →₀ ℕ) :
    coeff x (killCompl e (subst a f)) =
      ∑ᶠ d : σ →₀ ℕ, coeff d f • coeff x (d.prod fun s n => killCompl e (a s) ^ n) := by
  rw [coeff_killCompl, coeff_subst ha]
  refine finsum_congr fun d => ?_
  rw [show coeff (embDomain e x) (d.prod fun s n => a s ^ n) =
      coeff x (killCompl e (d.prod fun s n => a s ^ n)) from (coeff_killCompl _ _).symm, map_finsuppProd]
  simp only [map_pow]

private theorem killCompl_X_emb (e : υ ↪ τ) (w : υ) :
    killCompl e (X (e w) : MvPowerSeries τ R) = X w := by
  ext x
  rw [show coeff x (killCompl e (X (e w) : MvPowerSeries τ R)) =
      coeff (embDomain e x) (X (e w) : MvPowerSeries τ R) from coeff_killCompl _ _, coeff_X, coeff_X]
  by_cases hx : x = single w 1
  · rw [if_pos hx, if_pos (by rw [hx, embDomain_single])]
  · rw [if_neg hx, if_neg (fun h => hx (embDomain_injective e (h.trans (embDomain_single e w 1).symm)))]

theorem killCompl_beAll (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (R : Finset (Pl D)) (hR : IsReps D p R)
    (sg : Pl D → ℂ_[p]) (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p])
    (hcc : ∀ r ∈ R, constantCoeff (be r) = 0) {r : Pl D} (hr : r ∈ R) :
    killCompl (orbEmb D p r (Fin N0 × Fin N1)) (beAll D p (N0 := N0) (N1 := N1) R sg be) =
      sg r • ∑ a : Fin N0, ∑ b : Fin N1, subst (fun s : ZMod (nP D p) =>
        (X (s, a, b) : MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p])) (be r) := by
  unfold beAll
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single r ?_ (fun h => absurd hr h)]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hX : ∀ s : ZMod (nP D p), killCompl (orbEmb D p r (Fin N0 × Fin N1))
        (X (orbMap D p r s, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) = X (s, a, b) :=
      fun s => killCompl_X_emb (orbEmb D p r (Fin N0 × Fin N1)) (s, a, b)
    ext x
    rw [coeff_killCompl_subst _ (hasSubst_orbX D p r a b),
      coeff_subst (hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _)]
    simp only [hX]
  · intro r' hr' hne
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, Finset.sum_eq_zero, smul_zero]
    intro a _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    ext x
    rw [coeff_killCompl_subst _ (hasSubst_orbX D p r' a b), map_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    simp only [killCompl_orbX_off D p R hR hr hr' hne]
    by_cases hd : d = 0
    · subst hd
      rw [coeff_zero_eq_constantCoeff_apply, hcc r' hr', zero_smul]
    · obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hd
      refine smul_eq_zero_of_right _ ((congrArg (coeff x) ?_).trans (map_zero _))
      exact Finset.prod_eq_zero hs (zero_pow (Finsupp.mem_support_iff.mp hs))

end PI.OrbJet.OrbW
end
end

noncomputable section

open Classical

namespace PI.OrbJet.OrbW

open Formalism.BasicNotions Formalism.MainNotions.G MvPowerSeries Finsupp PI.OrbJet PI.OrbShared

theorem hasSubst_Clog (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (ep : ℂ_[p]) :
    HasSubst (fun v : Pl D × Fin N0 × Fin N1 => C ep * logPl D p v) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => by rw [map_mul, cc_logPl, mul_zero])

theorem hasSubst_log (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} :
    HasSubst (logPl D p (β := Fin N0 × Fin N1)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => cc_logPl D p v)

theorem hasSubst_Cjet (l d : ℕ) [Fact l.Prime] [NeZero d] {N0 N1 : ℕ} (ep : ℂ_[l]) :
    HasSubst (fun v : ZMod d × Fin N0 × Fin N1 => C ep * jetLogG l d v) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => by rw [map_mul, cc_jetLogG, mul_zero])

theorem hasSubst_jet (l d : ℕ) [Fact l.Prime] [NeZero d] {N0 N1 : ℕ} :
    HasSubst (jetLogG l d (β := Fin N0 × Fin N1)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => cc_jetLogG l d v)

theorem restricted_jet_equation (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (R : Finset (Pl D)) (hR : IsReps D p R)
    (ep : ℂ_[p]) (sg : Pl D → ℂ_[p]) (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p])
    (hcc : ∀ r ∈ R, constantCoeff (be r) = 0)
    (Th U : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])
    (hEq : subst (fun v : Pl D × Fin N0 × Fin N1 => C ep * logPl D p v) Th =
      U * subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (beAll D p R sg be)))
    {r : Pl D} (hr : r ∈ R) :
    subst (fun v : ZMod (nP D p) × Fin N0 × Fin N1 => C ep * jetLogG p (nP D p) v) (restr D p r Th) =
      killCompl (orbEmb D p r (Fin N0 × Fin N1)) U *
        subst (jetLogG p (nP D p) (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (sg r • ∑ a : Fin N0, ∑ b : Fin N1,
          subst (fun s : ZMod (nP D p) =>
            (X (s, a, b) : MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p])) (be r))) := by
  set e := orbEmb D p r (Fin N0 × Fin N1) with he
  have hk := congrArg (killCompl e) hEq
  have hA : killCompl e (subst (fun v : Pl D × Fin N0 × Fin N1 => C ep * logPl D p v) Th) =
      subst (fun v : ZMod (nP D p) × Fin N0 × Fin N1 => C ep * jetLogG p (nP D p) v) (killCompl e Th) := by
    refine killCompl_subst_of e _ _ (hasSubst_Clog D p ep) (hasSubst_Cjet p (nP D p) ep) ?_ ?_ Th
    · intro w
      rw [map_mul, killCompl_C, he, killCompl_logPl_emb]
    · intro t ht
      rw [map_mul, killCompl_logPl_off D p r t ht, mul_zero]
  have hL : ∀ F : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p],
      killCompl e (subst (logPl D p (β := Fin N0 × Fin N1)) F) =
        subst (jetLogG p (nP D p) (β := Fin N0 × Fin N1)) (killCompl e F) := by
    intro F
    refine killCompl_subst_of e _ _ (hasSubst_log D p) (hasSubst_jet p (nP D p)) ?_ ?_ F
    · intro w; rw [he, killCompl_logPl_emb]
    · intro t ht; exact killCompl_logPl_off D p r t ht
  have hccAll : constantCoeff (beAll D p (N0 := N0) (N1 := N1) R sg be) = 0 := by
    unfold beAll
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have hsm : ∀ (c : ℂ_[p]) (f : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]),
        constantCoeff f = 0 → constantCoeff (c • f) = 0 := by
      intro c f h
      rw [← coeff_zero_eq_constantCoeff_apply] at h ⊢
      simp [h]
    refine Finset.sum_eq_zero fun r' hr' => hsm _ _ ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    exact constantCoeff_subst_eq_zero (hasSubst_orbX D p r' a b) (fun s => by simp) (hcc r' hr')
  have hE : killCompl e (OJ.expS ℂ_[p] (beAll D p (N0 := N0) (N1 := N1) R sg be)) =
      OJ.expS ℂ_[p] (killCompl e (beAll D p (N0 := N0) (N1 := N1) R sg be)) := by
    unfold OJ.expS PowerSeries.subst
    exact killCompl_subst e (hasSubst_of_constantCoeff_zero fun _ => hccAll) _
  rw [map_mul, hA, hL, hE, killCompl_beAll D p R hR sg be hcc hr] at hk
  rw [restr_eq_killCompl, ← he]
  exact hk

end PI.OrbJet.OrbW
end
end

noncomputable section

open Classical

namespace PI.OrbJet.OrbW

open Formalism.BasicNotions Formalism.MainNotions.G MvPowerSeries Finsupp PI.OrbJet PI.OrbShared

theorem orbitRestriction : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitRestriction E := by
  intro D E
  unfold PI.OrbJet.OrbitRestriction
  intro p _ h u i R hR ep sg be hbe Th hB r hr
  obtain ⟨U, hU, hEq⟩ := hB
  obtain ⟨-, -, hb⟩ := hbe
  haveI : NeZero (nP D p) := ⟨by have := h.two; omega⟩

  have hcc : ∀ r ∈ R, MvPowerSeries.constantCoeff (be r) = 0 := fun r hr =>
    constant_coeff_zero_of_vanishing_alt p (nP D p) (be r) (hb r hr).2.2.1
  have key := restricted_jet_equation D p R hR ep sg be hcc Th U hEq hr
  unfold PI.OrbJet.OrbitThetaExpansion
  refine ⟨_, ?_, key⟩
  intro m
  change (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1)) →₀ ℕ) at m
  change ‖MvPowerSeries.coeff m (killCompl (orbEmb D p r (Fin (D.R.N i) × Fin (D.R.N (i + 1)))) U)‖ ≤ 1
  rw [MvPowerSeries.coeff_killCompl]
  exact hU _

end PI.OrbJet.OrbW
end
end

theorem PI.OrbRestr : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitRestriction E :=
  PI.OrbJet.OrbW.orbitRestriction
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbRestrOne
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitRestrictionDegreeOne.RestrictedSingleJetEquation
section -- merged from Formalism.PeriodIntegrals.OrbRestrOne
noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet

open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G

variable {D : D7}

def OrbitRestrictionAtConjugate (E : Ent D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p), nP D p = 1 → ∀ (u : D.what₂.Word) (i : ℕ),
    ∀ Th, ThetaExpansionRealPlaces D p Th → ∀ z, (oneLoc E p h5 u i z (restr1 D p z Th)).AdmB

end PI.OrbJet

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitRestrictionDegreeOne.Lemmas
noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet

open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G
open MvPowerSeries PI.OrbShared

variable {D : D7}

def embOne (z : Pl D) (N0 N1 : ℕ) : ZMod 1 × Fin N0 × Fin N1 ↪ Pl D × Fin N0 × Fin N1 where
  toFun v := (z, v.2)
  inj' _ _ h := Prod.ext (Subsingleton.elim _ _) (congrArg (fun x => x.2) h)

theorem restr1_eq_killCompl (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (z : Pl D)
    (Th : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) :
    restr1 D p z Th = killCompl (embOne z N0 N1) Th := by
  ext m
  rw [MvPowerSeries.coeff_killCompl, Finsupp.embDomain_eq_mapDomain]
  rfl

theorem killCompl_X_one (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (z : Pl D) (v : Pl D × Fin N0 × Fin N1) :
    killCompl (embOne z N0 N1) (X v : MvPowerSeries _ ℂ_[p]) =
      if v.1 = z then X ((0 : ZMod 1), v.2) else 0 := by
  split_ifs with h
  · have hv : v = embOne z N0 N1 ((0 : ZMod 1), v.2) := Prod.ext h rfl
    conv_lhs => rw [hv]
    rw [MvPowerSeries.killCompl_X]
  · apply MvPowerSeries.killCompl_X_eq_zero
    rintro ⟨w, hw⟩
    exact h (congrArg Prod.fst hw).symm

theorem subst_killCompl_X_one (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (z : Pl D)
    {B : ZMod 1 × Fin N0 × Fin N1 → MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p]} (hB : HasSubst B)
    (v : Pl D × Fin N0 × Fin N1) :
    subst B (killCompl (embOne z N0 N1) (X v : MvPowerSeries _ ℂ_[p])) =
      if v.1 = z then B ((0 : ZMod 1), v.2) else 0 := by
  rw [killCompl_X_one]
  split_ifs with h
  · exact MvPowerSeries.subst_X hB _
  · rw [← MvPowerSeries.coe_substAlgHom hB, map_zero]

theorem pow_sq_pow_ne_zero (p : ℕ) [hp : Fact p.Prime] (e : ℕ) : (p ^ 2) ^ e ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hp.out.ne_zero)

theorem constantCoeff_logPl (p : ℕ) [Fact p.Prime] {β : Type} (v : Pl D × β) :
    constantCoeff (logPl D p v) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ e ∈ Finset.range (JetTdeg (0 : Pl D × β →₀ ℕ) + 1),
    if (0 : Pl D × β →₀ ℕ) = Finsupp.single (backPl D p v.1 (2 * e), v.2) ((p ^ 2) ^ e)
    then ((p : ℂ_[p]) ^ e)⁻¹ else 0) = 0
  simp only [JetTdeg, Finsupp.sum_zero_index, zero_add, Finset.sum_range_one, pow_zero]
  rw [if_neg]
  intro h
  exact (Finsupp.single_ne_zero.2 one_ne_zero) h.symm

theorem constantCoeff_jetLogG (p : ℕ) [Fact p.Prime] (d : ℕ) {β : Type*} (v : ZMod d × β) :
    constantCoeff (jetLogG p d v) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ e ∈ Finset.range (JetTdeg (0 : ZMod d × β →₀ ℕ) + 1),
    if (0 : ZMod d × β →₀ ℕ) = Finsupp.single (v.1 - 2 * (e : ZMod d), v.2) ((p ^ 2) ^ e)
    then ((p : ℂ_[p]) ^ e)⁻¹ else 0) = 0
  simp only [JetTdeg, Finsupp.sum_zero_index, zero_add, Finset.sum_range_one, pow_zero]
  rw [if_neg]
  intro h
  exact (Finsupp.single_ne_zero.2 one_ne_zero) h.symm

theorem backPl₂ (p : ℕ) (hn : nP D p = 1) (y : Pl D) (e : ℕ) : backPl D p y e = y := by
  simp [backPl, posPl, partner, hn]

theorem JetTdeg_embDomain {α β : Type*} (f : α ↪ β) (m : α →₀ ℕ) :
    JetTdeg (Finsupp.embDomain f m) = JetTdeg m := by
  unfold JetTdeg
  rw [Finsupp.sum_embDomain]

theorem coeff_logPl (p : ℕ) [Fact p.Prime] {β : Type} (v : Pl D × β) (m : Pl D × β →₀ ℕ) :
    coeff m (logPl D p v) = ∑ e ∈ Finset.range (JetTdeg m + 1),
      if m = Finsupp.single (backPl D p v.1 (2 * e), v.2) ((p ^ 2) ^ e) then (((p : ℂ_[p]) ^ e)⁻¹) else 0 := rfl

theorem coeff_jetLogG (p : ℕ) [Fact p.Prime] (d : ℕ) {β : Type*} (v : ZMod d × β) (m : ZMod d × β →₀ ℕ) :
    coeff m (jetLogG p d v) = ∑ e ∈ Finset.range (JetTdeg m + 1),
      if m = Finsupp.single (v.1 - 2 * (e : ZMod d), v.2) ((p ^ 2) ^ e) then (((p : ℂ_[p]) ^ e)⁻¹) else 0 := rfl

theorem killCompl_logPl (p : ℕ) [Fact p.Prime] (hn : nP D p = 1) {N0 N1 : ℕ} (z : Pl D)
    (v : Pl D × Fin N0 × Fin N1) :
    killCompl (embOne z N0 N1) (logPl D p v) =
      if v.1 = z then jetLogG p 1 ((0 : ZMod 1), v.2) else 0 := by
  ext m
  rw [MvPowerSeries.coeff_killCompl, coeff_logPl, JetTdeg_embDomain]
  split_ifs with h
  · rw [coeff_jetLogG]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [backPl₂ p hn]
    have key : Finsupp.embDomain (embOne z N0 N1) m = Finsupp.single (v.1, v.2) ((p ^ 2) ^ e) ↔
        m = Finsupp.single (((0 : ZMod 1), v.2).1 - 2 * (e : ZMod 1), ((0 : ZMod 1), v.2).2) ((p ^ 2) ^ e) := by
      have hv : ((v.1, v.2) : Pl D × Fin N0 × Fin N1) =
          embOne z N0 N1 (((0 : ZMod 1), v.2).1 - 2 * (e : ZMod 1), ((0 : ZMod 1), v.2).2) := Prod.ext h rfl
      rw [hv, ← Finsupp.embDomain_single, Finsupp.embDomain_inj]
    simp only [key]
    split_ifs <;> rfl
  · rw [map_zero]
    apply Finset.sum_eq_zero
    intro e _
    rw [if_neg]
    intro heq
    rw [backPl₂ p hn] at heq
    have hk : (p ^ 2) ^ e ≠ 0 := pow_sq_pow_ne_zero p e
    have hmem : ((v.1, v.2) : Pl D × Fin N0 × Fin N1) ∈ (Finsupp.embDomain (embOne z N0 N1) m).support := by
      rw [heq, Finsupp.support_single_ne_zero _ hk]
      exact Finset.mem_singleton_self _
    rw [Finsupp.support_embDomain, Finset.mem_map] at hmem
    obtain ⟨w, _, hw⟩ := hmem
    exact h (congrArg Prod.fst hw).symm

theorem killCompl_expS {τ υ : Type*} {K : Type*} [Field K] [CharZero K] (e : υ ↪ τ)
    (f : MvPowerSeries τ K) (hf : constantCoeff f = 0) :
    killCompl e (OJ.expS K f) = OJ.expS K (killCompl e f) := by
  unfold OJ.expS PowerSeries.subst
  rw [PI.OrbShared.killCompl_subst e (PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero hf))]

theorem constantCoeff_zero_of_jet_bound (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l])
    (h : OJ.B3 l d be) : constantCoeff be = 0 := by
  by_contra hne
  have h0 := h 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])
  exact h0.1 (by simp [OJ.bideg])

end PI.OrbJet

end
end

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet

open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G
open MvPowerSeries PI.OrbShared

variable {D : D7}

theorem restricted_single_jet_equation (p : ℕ) [Fact p.Prime] (hn : nP D p = 1) {N0 N1 : ℕ} (z : Pl D)
    (Th U : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) (ep0 : ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod 2) ℂ_[p]) (hbe : ∀ z, constantCoeff (be z) = 0)
    (ep sg : Pl D → ℂ_[p])
    (hEq : subst (fun v : Pl D × Fin N0 × Fin N1 => C ep0 * logPl D p v) Th =
        U * subst (logPl D p (β := Fin N0 × Fin N1))
          (OJ.expS ℂ_[p] (∑ z : Pl D, (sg z / 2) • ∑ a : Fin N0, ∑ b : Fin N1,
            subst (fun s : ZMod 2 => if s = 0 then
                (X (z, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])
              else C (ep z) * X (z, a, b)) (be z)))) :
    subst (fun v : ZMod 1 × Fin N0 × Fin N1 => C ep0 * jetLogG p 1 v) (restr1 D p z Th) =
      killCompl (embOne z N0 N1) U * subst (jetLogG p 1 (β := Fin N0 × Fin N1))
        (OJ.expS ℂ_[p] ((sg z / 2) • ∑ a : Fin N0, ∑ b : Fin N1,
          subst (fun s : ZMod 2 => if s = 0 then
              (X ((0 : ZMod 1), a, b) : MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p])
            else C (ep z) * X ((0 : ZMod 1), a, b)) (be z))) := by
  set e := embOne z N0 N1 with he
  have hA : HasSubst (fun v : Pl D × Fin N0 × Fin N1 => (C ep0 * logPl D p v : MvPowerSeries _ ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero (fun v => by simp [constantCoeff_logPl])
  have hL : HasSubst (logPl D p (β := Fin N0 × Fin N1)) :=
    hasSubst_of_constantCoeff_zero (fun v => constantCoeff_logPl p v)
  have hJ : HasSubst (jetLogG p 1 (β := Fin N0 × Fin N1)) :=
    hasSubst_of_constantCoeff_zero (fun v => constantCoeff_jetLogG p 1 v)
  have hB : HasSubst (fun v : ZMod 1 × Fin N0 × Fin N1 => (C ep0 * jetLogG p 1 v : MvPowerSeries _ ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero (fun v => by simp [constantCoeff_jetLogG])
  have hρ : HasSubst (fun v : Pl D × Fin N0 × Fin N1 => killCompl e (X v : MvPowerSeries _ ℂ_[p])) :=
    hasSubst_killCompl e HasSubst.X
  have hσ0 : ∀ (y : Pl D) (a : Fin N0) (b : Fin N1) (s : ZMod 2),
      constantCoeff (if s = 0 then (X (y, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])
        else C (ep y) * X (y, a, b)) = 0 := by
    intro y a b s; split_ifs <;> simp
  have hσ : ∀ (y : Pl D) (a : Fin N0) (b : Fin N1), HasSubst (fun s : ZMod 2 =>
      if s = 0 then (X (y, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])
        else C (ep y) * X (y, a, b)) :=
    fun y a b => hasSubst_of_constantCoeff_zero (hσ0 y a b)
  set S : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p] := ∑ z : Pl D, (sg z / 2) • ∑ a : Fin N0, ∑ b : Fin N1,
      subst (fun s : ZMod 2 => if s = 0 then
          (X (z, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])
        else C (ep z) * X (z, a, b)) (be z) with hSdef
  have hS : constantCoeff S = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hSdef, map_sum]
    apply Finset.sum_eq_zero
    intro y _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← coeff_zero_eq_constantCoeff_apply, map_smul, map_sum]
    rw [Finset.sum_eq_zero, smul_zero]
    intro a _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    apply Finset.sum_eq_zero
    intro b _
    rw [coeff_zero_eq_constantCoeff_apply]
    exact constantCoeff_subst_eq_zero (hσ y a b) (hσ0 y a b) (hbe y)
  have hκS : killCompl e S = (sg z / 2) • ∑ a : Fin N0, ∑ b : Fin N1,
      subst (fun s : ZMod 2 => if s = 0 then
          (X ((0 : ZMod 1), a, b) : MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p])
        else C (ep z) * X ((0 : ZMod 1), a, b)) (be z) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hSdef, map_sum, Finset.sum_eq_single z]
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, map_sum]
      congr 1
      refine Finset.sum_congr rfl (fun a _ => ?_)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [killCompl_subst e (hσ z a b)]
      congr 1
      funext s
      split_ifs
      · rw [he, killCompl_X_one, if_pos rfl]
      · rw [map_mul, killCompl_C, he, killCompl_X_one, if_pos rfl]
    · intro y _ hy
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, map_sum]
      rw [Finset.sum_eq_zero, smul_zero]
      intro a _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      apply Finset.sum_eq_zero
      intro b _
      rw [killCompl_subst e (hσ y a b)]
      have h0 : (fun s : ZMod 2 => killCompl e (if s = 0 then
          (X (y, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])
            else C (ep y) * X (y, a, b))) = 0 := by
        funext s
        have hx : killCompl e (X (y, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) = 0 := by
          rw [he, killCompl_X_one, if_neg hy]
        split_ifs
        · rw [hx]; rfl
        · rw [map_mul, hx, mul_zero]; rfl
      rw [h0, subst_zero_of_constantCoeff_zero (hbe y)]
    · intro h; exact absurd (Finset.mem_univ z) h
  have h1 := congrArg (killCompl e) hEq
  rw [killCompl_subst e hA, map_mul, killCompl_subst e hL] at h1
  rw [restr1_eq_killCompl, ← he, killCompl_eq_subst e Th, subst_comp_subst_apply hρ hB]
  have eA : (fun v : Pl D × Fin N0 × Fin N1 => subst (fun v : ZMod 1 × Fin N0 × Fin N1 =>
      (C ep0 * jetLogG p 1 v : MvPowerSeries _ ℂ_[p])) (killCompl e (X v : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]))) =
      fun v => killCompl e (C ep0 * logPl D p v) := by
    funext v
    rw [he, subst_killCompl_X_one p z hB, map_mul, killCompl_C, killCompl_logPl p hn]
    split_ifs <;> simp
  rw [eA, h1]
  congr 1
  have eL : (fun v : Pl D × Fin N0 × Fin N1 => killCompl e (logPl D p v)) =
      fun v => subst (jetLogG p 1 (β := Fin N0 × Fin N1)) (killCompl e (X v : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])) := by
    funext v
    rw [he, subst_killCompl_X_one p z hJ, killCompl_logPl p hn]
  rw [eL, ← subst_comp_subst_apply hρ hJ, ← killCompl_eq_subst e, killCompl_expS e S hS, hκS]

end PI.OrbJet

end
end

theorem PI.OrbRestrOne : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitRestrictionAtConjugate E := by
  intro D E p _ h5 hn u i Th hTh z
  obtain ⟨ep0, hep0, be, hbe, ep, hep, sg, hsg, U, hU, hEq⟩ := hTh
  have hc : ∀ w, MvPowerSeries.constantCoeff (be w) = 0 := fun w =>
    PI.OrbJet.constantCoeff_zero_of_jet_bound p 2 (be w) (hbe w).2.2.1
  have key := PI.OrbJet.restricted_single_jet_equation (D := D) p hn z Th U ep0 be hc ep sg hEq
  dsimp only [PI.OrbJet.oneLoc, PI.OrbJet.OJ.Loc1.AdmB, PI.OrbJet.OJ.Loc1.B0, PI.OrbJet.OJ.Loc1.Tht]
  refine ⟨ep0, hep0, be z, ⟨ep z, hep z, sg z, hsg z, _, ?_, key⟩,
    (hbe z).1, (hbe z).2.1, (hbe z).2.2.1, (hbe z).2.2.2⟩
  intro m
  rw [MvPowerSeries.coeff_killCompl]
  exact hU _
end

namespace Formalism.MainNotions.DIV.Lemmas.OrbitEntryBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

def toEnt {D : D7} (E : OrbitPlaces.Ent D) : PI.OrbJet.Ent D :=
  ⟨E.nu, E.nu_row, E.nu_rows, E.Th, E.ep, E.be, E.sg⟩

theorem addition_bound_holds (D : D7) (E : OrbitPlaces.Ent D) : OrbitPlaces.OrbitsAddLowerBound E := by
  intro p _ h u i hi R hR ep sg be hbe β hβ Th hTh
  exact PI.OrbAddUp D (toEnt E) p ⟨h.five, h.even, h.two⟩ u i hi R hR ep sg be hbe β hβ Th hTh

theorem orbitsAddAtConjugate_ent (D : D7) (E : OrbitPlaces.Ent D) : OrbitPlaces.OrbitsAddAtConjugate E :=
  PI.OrbAddOne D (toEnt E)

theorem restriction_bound_holds (D : D7) (E : OrbitPlaces.Ent D) : OrbitPlaces.OrbitRestriction E := by
  intro p _ h u i R hR ep sg be hbe Th hTh r hr
  exact PI.OrbRestr D (toEnt E) p ⟨h.five, h.even, h.two⟩ u i R hR ep sg be hbe Th hTh r hr

theorem orbit_restriction_at_conjugate (D : D7) (E : OrbitPlaces.Ent D) : OrbitPlaces.OrbitRestrictionAtConjugate E :=
  PI.OrbRestrOne D (toEnt E)

theorem entry_divisor_bound_holds (D : D7) (E : OrbitPlaces.Ent D) (Dx : DivX D) (hs : OrbitPlaces.ThetaKernelShapeAtD E Dx) : OrbitPlaces.EntriesAtDiscriminant E Dx := by
  intro u μ w hL hc i hi L L'
  exact _root_.jet_bound_ramified_prime D Dx E.nu E.nu_row E.nu_rows E.Th hs u μ w hL hc i hi L L'

private theorem entry_number_bound_holds (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (E : OrbitPlaces.Ent D) (ce : ErrC) (C6 C : ℝ)
    (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge C6 C K ce) : OrbitPlaces.ScaledGeneratorsInSup E L K ce := by
  intro p hp h5 hcs hpX u i hi
  exact ⟨fun Th hTh => UpperTheory.kvalGe_theta_of_shape D L X E hS p h5 hcs.1 hcs.2.2 hpX u i hi Th hTh,
    fun hL => UpperTheory.fInert_sub_eatI_le_orbit_average_sub_errors D L X K E ce C6 C hS hC hL p hp.out h5 hcs hpX i hi⟩

theorem orbit_entry_bounds_of_family (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (E : OrbitPlaces.Ent D) (ce : ErrC) (C6 C : ℝ)
    (hF : OrbitPlaces.OrbitValuationBound E X K ce) (hs : OrbitPlaces.ThetaKernelShapeAtD E Dx) (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge C6 C K ce) :
    OrbitPlaces.Core D L X K Dx E ce C :=
  ⟨addition_bound_holds D E, orbitsAddAtConjugate_ent D E, restriction_bound_holds D E, orbit_restriction_at_conjugate D E, hF, entry_divisor_bound_holds D E Dx hs,
    PI.SumOrbC D L X K ce E C6 C hS hC, entry_number_bound_holds D L X K E ce C6 C hS hC⟩

theorem orbit_entry_bounds_hold (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (E : OrbitPlaces.Ent D) (ce : ErrC) (C6 C : ℝ)
    (hA : OrbitPlaces.OrbitLetterBoundsAll C6 C) (hs : OrbitPlaces.ThetaKernelShapeAtD E Dx) (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge C6 C K ce) :
    OrbitPlaces.Core D L X K Dx E ce C :=
  orbit_entry_bounds_of_family D L X K Dx E ce C6 C (PI.OrbBoundF D L X K ce E C6 C hA hS hC) hs hS hC

end Formalism.MainNotions.DIV.Lemmas.OrbitEntryBounds
