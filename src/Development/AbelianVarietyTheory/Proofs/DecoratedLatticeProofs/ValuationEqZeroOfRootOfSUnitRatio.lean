module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateThetaFunLeSchwartzMajorantLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.RatioUnit

theorem natCast_notMem_of_primes {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ m : ℕ, m ≠ 0 → (∀ p : ℕ, p.Prime → p ∣ m → (p : R) ∉ P) → (m : R) ∉ P := by
  intro m
  induction m using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; rw [Nat.cast_one]; exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)
  | prime p hp => intro _ h; exact h p hp dvd_rfl
  | mul a b ha hb =>
    intro hab h hmem
    rw [Nat.cast_mul] at hmem
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact ha (left_ne_zero_of_mul hab) (fun p hp hd => h p hp (dvd_mul_of_dvd_left hd b)) h1
    · exact hb (right_ne_zero_of_mul hab) (fun p hp hd => h p hp (dvd_mul_of_dvd_right hd a)) h1

theorem not_dvd_both {r : ℚ} {p : ℕ} (hp : p.Prime) (h1 : p ∣ r.num.natAbs) (h2 : p ∣ r.den) : False :=
  hp.not_dvd_one (by simpa [Nat.Coprime.gcd_eq_one r.reduced] using Nat.dvd_gcd h1 h2)

theorem padicValRat_ne_zero_of_dvd_num {r : ℚ} (hr : r ≠ 0) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ r.num.natAbs) : padicValRat p r ≠ 0 := by
  haveI := Fact.mk hp
  have hnd : ¬ p ∣ r.den := fun hd' => not_dvd_both hp hd hd'
  have h0 : r.num.natAbs ≠ 0 := by simpa using hr
  have h1 := one_le_padicValNat_of_dvd h0 hd
  simp only [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hnd]
  omega

theorem padicValRat_ne_zero_of_dvd_den {r : ℚ} {p : ℕ} (hp : p.Prime)
    (hd : p ∣ r.den) : padicValRat p r ≠ 0 := by
  haveI := Fact.mk hp
  have hnd : ¬ p ∣ r.num.natAbs := fun hd' => not_dvd_both hp hd' hd
  have h1 := one_le_padicValNat_of_dvd r.den_nz hd
  simp only [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hnd]
  omega

end GlobalTheory.Fam.RatioUnit

namespace GlobalTheory.Fam
open Formalism.DivisionValues GlobalTheory.Fam.RatioUnit

theorem RatioUnit.intCast_notMem_of_natAbs {R : Type} [CommRing R] (P : Ideal R) (z : ℤ)
    (h : ((z.natAbs : ℕ) : R) ∉ P) : ((z : ℤ) : R) ∉ P := by
  rcases Int.natAbs_eq z with e | e
  · rw [e]; simpa using h
  · rw [e]; simpa [Ideal.neg_mem_iff] using h

theorem vw_eq_zero_of_unitRatio : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (w : HeightOneSpectrum (𝓞 K)) (S : ℕ → Prop) (x y : ℂ), GlobalTheory.Fam.UnitRatio S x y → (∀ p : ℕ, p.Prime → S p → (p : 𝓞 K) ∉ w.asIdeal) → ∀ a : K, σ a = x / y → Formalism.DivisionValues.vw w a = 0 := by
  intro K _ _ σ w S x y hU hS a ha

  letI : StarRing K := starRingOfComm
  obtain ⟨_, n, hn, r, hr0, hpow, hrS⟩ := hU
  have hpow' : a ^ n = (r : K) := by
    apply σ.injective
    rw [map_pow, ha, hpow, map_ratCast]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hpow'
    exact hr0 (by exact_mod_cast hpow'.symm)
  have hnum : ((r.num : ℤ) : 𝓞 K) ∉ w.asIdeal := by
    refine intCast_notMem_of_natAbs _ _ (natCast_notMem_of_primes w.asIdeal _ (by simpa using hr0) ?_)
    intro p hp hd
    exact hS p hp (hrS p hp (padicValRat_ne_zero_of_dvd_num hr0 hp hd))
  have hden : ((r.den : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    refine natCast_notMem_of_primes w.asIdeal _ r.den_nz ?_
    intro p hp hd
    exact hS p hp (hrS p hp (padicValRat_ne_zero_of_dvd_den hp hd))
  have vnum := ReductionFirst.vw_unit w _ hnum
  have vden := ReductionFirst.vw_unit w _ hden
  rw [show (((r.num : ℤ) : 𝓞 K) : K) = (r.num : K) from map_intCast (algebraMap (𝓞 K) K) _] at vnum
  rw [show (((r.den : ℕ) : 𝓞 K) : K) = (r.den : K) from map_natCast (algebraMap (𝓞 K) K) _] at vden
  have hd0 : (r.den : K) ≠ 0 := by exact_mod_cast r.den_nz
  have hrK0 : (r : K) ≠ 0 := by exact_mod_cast hr0
  have key : (r : K) * (r.den : K) = (r.num : K) := by
    rw [Rat.cast_def]; field_simp
  have h1 := ReductionFirst.vw_mul w hrK0 hd0
  rw [key, vnum, vden] at h1
  have h2 := ReductionFirst.vw_pow w a n
  rw [hpow'] at h2
  have h3 : (n : ℤ) * vw w a = 0 := by rw [← h2]; omega
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (by exact_mod_cast h) hn.ne'
  · exact h

end GlobalTheory.Fam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatioStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_eq_zero_of_rootOfSUnitRatio : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (w : HeightOneSpectrum (𝓞 K)) (S : ℕ → Prop) (x y : ℂ), GlobalTheory.Fam.UnitRatio S x y → (∀ p : ℕ, p.Prime → S p → (p : 𝓞 K) ∉ w.asIdeal) → ∀ a : K, σ a = x / y → Formalism.DivisionValues.vw w a = 0 := by
  first | exact @GlobalTheory.Fam.vw_eq_zero_of_unitRatio | exact GlobalTheory.Fam.vw_eq_zero_of_unitRatio | (intros; apply GlobalTheory.Fam.vw_eq_zero_of_unitRatio <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.DisjComb

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem mul_eq_zero_of_disj {P P' : Pl D → Prop} (hd : ∀ p, P p → ¬ P' p) {a b : AE D} (ha : a ∈ idAt D P)
    (hb : b ∈ idAt D P') : a * b = 0 := by
  obtain ⟨ha0, haw⟩ := mem_idAt_iff.1 ha
  obtain ⟨hb0, hbw⟩ := mem_idAt_iff.1 hb
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun w => ?_) fun v => ?_
  · rw [map_mul, compInf_eq_zero ha0, zero_mul, map_zero]
  · rw [map_mul, map_zero, compFin_eq_compAt, compFin_eq_compAt]
    by_cases hv : P v
    · rw [hbw v (hd v hv), mul_zero]
    · rw [haw v hv, zero_mul]

theorem mul_eq_zero_of_off {P : Pl D → Prop} {a b : AE D} (ha : a ∈ idOff D P) (hb : b ∈ idAt D P) : a * b = 0 := by
  obtain ⟨hb0, hbw⟩ := mem_idAt_iff.1 hb
  have haw : ∀ v, P v → compAt D v a = 0 := by
    intro v hv
    unfold idOff at ha
    rw [Submodule.mem_iInf] at ha
    exact RingHom.mem_ker.1 (ha ⟨v, hv⟩)
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun w => ?_) fun v => ?_
  · rw [map_mul, compInf_eq_zero hb0, mul_zero, map_zero]
  · rw [map_mul, map_zero, compFin_eq_compAt, compFin_eq_compAt]
    by_cases hv : P v
    · rw [haw v hv, zero_mul]
    · rw [hbw v hv, mul_zero]

def idem (P : Pl D → Prop) : AE D := pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] (1 : D.host.E)

theorem idem_mem (P : Pl D → Prop) : idem P ∈ idAt D P := tmul_mem_idAt (indicatorAdele_supported D.host.F P) 1

theorem cA_idem (P : Pl D → Prop) : cA D (idem P) = idem P := by
  show pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] star (1 : D.host.E) = _
  rw [star_one]; rfl

theorem idem_mul {P : Pl D → Prop} {a : AE D} (ha : a ∈ idAt D P) : idem P * a = a := by
  rw [mul_comm]; exact mul_indP ha

theorem symplO_disj {S T : HSp D} {P P' : Pl D → Prop} (hd : ∀ p, P p → ¬ P' p) {x y : WO S T} (hx : MxAt P x)
    (hy : MxAt P' y) : symplO S T x y = 0 := by
  refine GlobalTheory.SplitScalar.symplO_eq_zero S T (a := idem P) (b := idem P') ?_ (fun i j => idem_mul (hx i j))
    (fun i j => idem_mul (hy i j))
  rw [cA_idem]
  exact mul_eq_zero_of_disj hd (idem_mem P) (idem_mem P')

theorem mxAt_mono {P Q : Pl D → Prop} (h : ∀ p, P p → Q p) {m n : ℕ} {x : Mx D m n} (hx : MxAt P x) : MxAt Q x := by
  intro i j
  obtain ⟨h0, hw⟩ := mem_idAt_iff.1 (hx i j)
  exact mem_idAt_iff.2 ⟨h0, fun w hw' => hw w fun hp => hw' (h w hp)⟩

theorem comb_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single w 1) f = heisO ψ S T w f := by
  unfold comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]

theorem mem_congGrp' {V : HSp D} {I : Ideal (AE D)} {g : GA D V} (hg : g ∈ congGrp V I) :
    ∀ i j, mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  unfold congGrp at hg
  rw [MonoidHom.mem_ker] at hg
  intro i j
  have := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ I) => x.1 i j) hg
  rw [← Ideal.Quotient.eq]
  simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
  exact this

theorem actO_off {S T : HSp D} {P : Pl D → Prop} {g : GA D S} {h : GA D T} (hg : g ∈ grpOff S P)
    (hh : h ∈ grpOff T P) {u : WO S T} (hu : MxAt P u) : actO S T g h u = u := by
  have hg' := mem_congGrp' (inv_mem hg)
  have hh' := mem_congGrp' hh
  have h1 : HMul.hMul (mt T h - 1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ => mul_eq_zero_of_off (by simpa using hh' i k) (hu k j)
  have h2 : HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹ - 1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ => by
      rw [mul_comm]; exact mul_eq_zero_of_off (by simpa using hg' k j) (hu i k)
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2
  unfold actO
  rw [h1]
  exact h2

end GlobalTheory.DisjComb

namespace GlobalTheory.DisjComb

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem compAt_idem {P : Pl D → Prop} {w : Pl D} (hpw : P w) : compAt D w (idem P) = 1 := by
  rw [← compFin_eq_compAt]
  show evalV D.host.F w (indP D.host.F P) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
  rw [evalV_indP, if_pos hpw]
  rfl

theorem sub_idem_mem {P P' : Pl D → Prop} {a : AE D} (ha : a ∈ idAt D (fun p => P p ∨ P' p)) :
    a - idem P * a ∈ idAt D P' := by
  obtain ⟨h0, hw⟩ := mem_idAt_iff.1 ha
  refine mem_idAt_iff.2 ⟨by rw [RingHom.map_sub, RingHom.map_mul, h0, mul_zero, sub_zero], fun w hw' => ?_⟩
  by_cases hpw : P w
  · rw [RingHom.map_sub, RingHom.map_mul, compAt_idem hpw, one_mul, sub_self]
  · rw [RingHom.map_sub, RingHom.map_mul, hw w (fun h => h.elim hpw hw'), mul_zero, sub_zero]


set_option maxHeartbeats 1000000 in
theorem split_latO (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {LS : Lat S} {LT : Lat T}
    (hLS : IsSelfDualC S LS) (hLT : IsSelfDualC T LT) {P P' : Pl D → Prop} (hd : ∀ p, P p → ¬ P' p) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set _) (LT : Set _) (fun p => P p ∨ P' p)) :
    MxAt P (idem P • u) ∧ MxAt P' (u - idem P • u) ∧ idem P • u ∈ latO S T (LS : Set _) (LT : Set _) P ∧
      u - idem P • u ∈ latO S T (LS : Set _) (LT : Set _) P' := by
  have ann := GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hLS hLT
  have hmono : ∀ (Q Q' : Pl D → Prop), (∀ p, Q p → Q' p) →
      latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) Q' := by
    intro Q Q' hQ
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (hQ v hq), rest⟩
  have huM := latO_mxAt hu
  have hu1 : MxAt P (idem P • u) := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (idem_mem P)
  have hu2 : MxAt P' (u - idem P • u) := fun i j => by
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact sub_idem_mem (huM i j)
  refine ⟨hu1, hu2, (ann P _ hu1).2 fun u' hu' => ?_, (ann P' _ hu2).2 fun u' hu' => ?_⟩
  · have hsub : symplO S T (idem P • u) u' = symplO S T u u' - symplO S T (u - idem P • u) u' := by
      rw [← GlobalTheory.SplitScalar.symplO_sub_left, sub_sub_cancel]
    rw [hsub, symplO_disj (fun p hp' hp => hd p hp hp') hu2 (latO_mxAt hu'), sub_zero]
    exact (ann _ u huM).1 hu u' (hmono _ _ (fun p hp => Or.inl hp) hu')
  · rw [GlobalTheory.SplitScalar.symplO_sub_left, symplO_disj hd hu1 (latO_mxAt hu'), sub_zero]
    exact (ann _ u huM).1 hu u' (hmono _ _ (fun p hp => Or.inr hp) hu')

theorem isHalf_parts {S T : HSp D} {P : Pl D → Prop} {e : AE D} {u : WO S T} (h : IsHalf e u) :
    IsHalf e (idem P • u) ∧ IsHalf e (u - idem P • u) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_left_comm, h i j]
  · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [mul_sub, h i j, mul_left_comm, h i j]

end GlobalTheory.DisjComb

namespace GlobalTheory.DisjComb

open GlobalTheory.FinPl.LatMem

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (P P' : Pl D → Prop), (∀ p, P p → ¬ P' p) → (∀ e e' : WO S T →₀ ℂ, CombAt P e → CombAt P' e' → ∀ f, comb ψ S T e (comb ψ S T e' f) = comb ψ S T e' (comb ψ S T e f)) ∧ (∀ e : WO S T →₀ ℂ, CombAt P e → IsFinComb e ∧ ∀ LS LT f, Vac ψ S T LS LT P' f → Vac ψ S T LS LT P' (comb ψ S T e f)) ∧ (∀ χS χT (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ e : WO S T →₀ ℂ, CombAt P e → ∀ g ∈ grpOff S P, ∀ h ∈ grpOff T P, ∀ f, IsThetaFunO ψ S T f → om (g, h) (comb ψ S T e f) = comb ψ S T e (om (g, h) f)) ∧ (∀ e e' : WO S T →₀ ℂ, CombAt (fun p => P p ∨ P' p) e → CombAt (fun p => P p ∨ P' p) e' → ∃ e'', CombAt (fun p => P p ∨ P' p) e'' ∧ ∀ f, comb ψ S T e'' f = comb ψ S T e (comb ψ S T e' f)) ∧ ∀ LS LT f, IsSelfDualC S LS → IsSelfDualC T LT → (Vac ψ S T LS LT (fun p => P p ∨ P' p) f ↔ Vac ψ S T LS LT P f ∧ Vac ψ S T LS LT P' f) := by
  intro D ψ hψ S T P P' hd
  have HC := GlobalTheory.HeisComb.main D ψ S T
  have hcomm : ∀ (e : WO S T →₀ ℂ), CombAt P e → ∀ w : WO S T, MxAt P' w → ∀ f,
      heisO ψ S T w (comb ψ S T e f) = comb ψ S T e (heisO ψ S T w f) := by
    intro e he w hw f
    have h := HC.2.1 e (Finsupp.single w 1) (fun x hx y hy => by
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hy
      subst hy
      exact symplO_disj hd (he x hx) hw) f
    simp only [comb_single] at h
    exact h.symm
  have hmono : ∀ (LS : Lat S) (LT : Lat T) (Q Q' : Pl D → Prop), (∀ p, Q p → Q' p) →
      latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) Q' := by
    intro LS LT Q Q' hQ
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (hQ v hq), rest⟩
  have hnsmul : ∀ (Q : Pl D → Prop) (x : WO S T), MxAt Q x → MxAt Q ((2 : ℕ) • x) := by
    intro Q x hx i j
    rw [Matrix.smul_apply]
    exact nsmul_mem (hx i j) 2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e e' he he' f
    exact HC.2.1 e e' (fun x hx y hy => symplO_disj hd (he x hx) (he' y hy)) f
  · intro e he
    have hfin : IsFinComb e := fun u hu => Matrix.ext fun i j => (mem_idAt_iff.1 (he u hu i j)).1
    refine ⟨hfin, fun LS LT f hf => ⟨HC.2.2.1 e f hf.1 hfin hψ, fun u hu => ?_, fun e' he' u hu hh => ?_⟩⟩
    · rw [hcomm e he _ (hnsmul P' u (latO_mxAt hu)), hf.2.1 u hu]
    · rw [hcomm e he u (latO_mxAt hu), hf.2.2 e' he' u hu hh]
  · intro χS χT om hom e he g hg h hh f hf
    unfold comb
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [map_smul, hom.om_heis g h u f hf, actO_off hg hh (he u hu)]
  · intro e e' he he'
    obtain ⟨c'', hsupp, heq⟩ := HC.1 e e'
    refine ⟨c'', fun w hw => ?_, heq⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := hsupp w hw
    intro i j
    rw [Matrix.add_apply]
    exact Ideal.add_mem _ (he x hx i j) (he' y hy i j)
  · intro LS LT f hLS hLT
    constructor
    · intro hf
      refine ⟨⟨hf.1, fun u hu => hf.2.1 u (hmono LS LT _ _ (fun p hp => Or.inl hp) hu),
        fun e he u hu hh => hf.2.2 e he u (hmono LS LT _ _ (fun p hp => Or.inl hp) hu) hh⟩,
        ⟨hf.1, fun u hu => hf.2.1 u (hmono LS LT _ _ (fun p hp => Or.inr hp) hu),
        fun e he u hu hh => hf.2.2 e he u (hmono LS LT _ _ (fun p hp => Or.inr hp) hu) hh⟩⟩
    · rintro ⟨hP, hP'⟩
      refine ⟨hP.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
      · obtain ⟨hm1, hm2, hl1, hl2⟩ := split_latO ψ hψ hLS hLT hd hu
        have hsum : u = idem P • u + (u - idem P • u) := (add_sub_cancel _ _).symm
        rw [hsum, nsmul_add, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (symplO_disj hd (hnsmul P _ hm1) (hnsmul P' _ hm2)),
          hP'.2.1 _ hl2, hP.2.1 _ hl1]
      · obtain ⟨hm1, hm2, hl1, hl2⟩ := split_latO ψ hψ hLS hLT hd hu
        obtain ⟨h1, h2⟩ := isHalf_parts (P := P) hh
        have hsum : u = idem P • u + (u - idem P • u) := (add_sub_cancel _ _).symm
        rw [hsum, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (symplO_disj hd hm1 hm2), hP'.2.2 e he _ hl2 h2,
          hP.2.2 e he _ hl1 h1]

end GlobalTheory.DisjComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacuaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (P P' : Pl D → Prop), (∀ p, P p → ¬ P' p) → (∀ e e' : WO S T →₀ ℂ, CombAt P e → CombAt P' e' → ∀ f, comb ψ S T e (comb ψ S T e' f) = comb ψ S T e' (comb ψ S T e f)) ∧ (∀ e : WO S T →₀ ℂ, CombAt P e → IsFinComb e ∧ ∀ LS LT f, Vac ψ S T LS LT P' f → Vac ψ S T LS LT P' (comb ψ S T e f)) ∧ (∀ χS χT (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ e : WO S T →₀ ℂ, CombAt P e → ∀ g ∈ grpOff S P, ∀ h ∈ grpOff T P, ∀ f, IsThetaFunO ψ S T f → om (g, h) (comb ψ S T e f) = comb ψ S T e (om (g, h) f)) ∧ (∀ e e' : WO S T →₀ ℂ, CombAt (fun p => P p ∨ P' p) e → CombAt (fun p => P p ∨ P' p) e' → ∃ e'', CombAt (fun p => P p ∨ P' p) e'' ∧ ∀ f, comb ψ S T e'' f = comb ψ S T e (comb ψ S T e' f)) ∧ ∀ LS LT f, IsSelfDualC S LS → IsSelfDualC T LT → (Vac ψ S T LS LT (fun p => P p ∨ P' p) f ↔ Vac ψ S T LS LT P f ∧ Vac ψ S T LS LT P' f) := by
  first | exact @GlobalTheory.DisjComb.main | exact GlobalTheory.DisjComb.main | (intros; apply GlobalTheory.DisjComb.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelExistsForContinuous
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Collect

variable {D : D7}

theorem theta_sum {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → WO S T → ℂ) (hf : ∀ i, IsThetaFunO ψ S T (f i)) : IsThetaFunO ψ S T (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ S T
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact GlobalTheory.LocMod.LinSpace.isThetaFunO_add (GlobalTheory.LocMod.LinSpace.isThetaFunO_smul _ (hf i)) ih

end GlobalTheory.Core.Rk.Collect

namespace GlobalTheory.Core.Rk.Collect

end GlobalTheory.Core.Rk.Collect
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.RdVal
variable {D : D7}

theorem toEAf_sig (a : AE D) :
    toEAf D (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig a) =
      Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [toEAf, finPart, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR, sigD]
  | add a b ha hb =>
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, RingHom.map_add (f := _), RingHom.map_add (f := _)]

theorem toEAf_incl (e : D.host.E) :
    toEAf D (incA D e) = Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) e := by
  simp [toEAf, finPart, incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Formalism.UG.inclE]

theorem isUnit_det_mt (V : HSp D) (g : GA D V) : IsUnit (mt V g).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (matHom V g))

theorem mt_unitary (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (mt V g) * V.gram.map (incA D) * mt V g =
      V.gram.map (incA D) := by
  exact (show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig V.gram from g).2

theorem finM_mem (V : HSp D) {n : ℕ} (hn : V.rank = n) (J : Matrix (Fin n) (Fin n) D.host.E)
    (hJ : J = V.gram.reindex (finCongr hn) (finCongr hn)) (g : GA D V) :
    ∃ x : UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F), x.1.1 = finM V hn g := by
  have hdet : IsUnit (finM V hn g).det := by
    simp only [finM, Matrix.det_reindex_self]
    have hm := RingHom.map_det (toEAf D) (mt V g)
    rw [RingHom.mapMatrix_apply] at hm
    rw [← hm]
    exact (isUnit_det_mt V g).map _
  refine ⟨⟨((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit, ?_⟩, rfl⟩
  show Formalism.UG.cT _ (finM V hn g) * J.map _ * finM V hn g = J.map _
  have key : Formalism.UG.cT (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (finM V hn g) =
      ((Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (mt V g)).map (toEAf D)).reindex
        (finCongr hn) (finCongr hn) := by
    ext i j; simp [finM, Formalism.UG.cT, Matrix.reindex_apply, toEAf_sig]
  have hJ' : J.map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =
      ((V.gram.map (incA D)).map (toEAf D)).reindex (finCongr hn) (finCongr hn) := by
    subst hJ; ext i j; simp [Matrix.reindex_apply, toEAf_incl]
  rw [key, hJ', finM]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, ← Matrix.map_mul, mt_unitary]

theorem infM_unit (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (τ : D.what₂.Tau) :
    IsUnit (infM θ V hn g τ).det := by
  simp only [infM, Matrix.det_reindex_self]
  have hm := RingHom.map_det ((θ τ).comp (infPart D)) (mt V g)
  rw [RingHom.mapMatrix_apply] at hm
  have e : compAt θ τ (mt V g) = (mt V g).map ((θ τ).comp (infPart D)) := rfl
  rw [e, ← hm]
  exact (isUnit_det_mt V g).map _

theorem atInf_mul_inv {n : ℕ} (γ : GL (Fin n) D.host.E) (τ : D.what₂.Tau) :
    atInf (embT D) (γ : Matrix (Fin n) (Fin n) D.host.E) τ * atInf (embT D) ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ = 1 := by
  simp only [atInf, ← Matrix.map_mul, Units.mul_inv]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end GlobalTheory.AdForm.RdVal


open GlobalTheory.AdForm.RdVal in
theorem GlobalTheory.AdForm.rdS_val : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (hn : V.rank = n) (J : Matrix (Fin n) (Fin n) D.host.E), J = V.gram.reindex (finCongr hn) (finCongr hn) → ∀ (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (cl : Type) (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)) → ∀ Ψ ∈ AdFun S (embT D), ∀ (y : Frames (gramC J (embT D))) (g : GA D V), (∃ x : UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F), x.1.1 = finM V hn g) ∧ (∀ τ, IsUnit (infM θ V hn g τ).det) ∧ ∀ (x : UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (y' : Frames (gramC J (embT D))), x.1.1 = finM V hn g → IsTr (infM θ V hn g) y y' → rdS θ V hn S yc (fun c => Ψ (yc c)) y g = Ψ x y' := by
  intro D θ _ V n hn J hJ T f bad S cl yc hbij Ψ hΨ y g
  refine ⟨finM_mem V hn J hJ g, fun τ => infM_unit θ V hn g τ, ?_⟩
  intro x y' hx hy
  obtain ⟨c, hc⟩ := hbij.2 (Quotient.mk'' x : Cls S)
  have hex : ∃ p, IsDec S yc (finM V hn g) p := by
    obtain ⟨h, hh, k, hk, hxe⟩ := (@DoubleCoset.eq _ _ _ _ _ _).mp hc
    obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hh)
    refine ⟨(c, γ, ⟨k.1, Subgroup.mem_subgroupOf.mp hk⟩), hγ, ?_⟩
    dsimp only
    rw [hγe, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← hxe, hx]
  have hp := hex.choose_spec
  have hfr : ∀ τ, IsUnit (atInf (embT D) ((hex.choose.2.1)⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ * y.1 τ).det := by
    intro τ
    rw [Matrix.det_mul, Matrix.det_mul]
    exact ((Matrix.isUnit_det_of_left_inverse (atInf_mul_inv hex.choose.2.1 τ)).mul (infM_unit θ V hn g τ)).mul (y.2 τ)
  unfold rdS
  rw [dite_eq_left hex, atFr, dite_eq_left hfr]
  have law := hΨ hex.choose.2.1 hp.1 (yc hex.choose.1) x hex.choose.2.2 (Units.ext (hx.trans hp.2)) y' ⟨_, hfr⟩ (by
    intro τ
    show y'.1 τ = _
    rw [hy τ]
    simp only [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul])
  exact law.symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SetCut

variable {D : D7}

def indQ (D : D7) (Q : Finset (Pl D)) : Af D.host.F := ∑ v ∈ Q, singleV D.host.F v 1

def idemQ (D : D7) (Q : Finset (Pl D)) : AF D.host.F := pairA D.host.F 0 (indQ D Q)

def idemQc (D : D7) (Q : Finset (Pl D)) : AF D.host.F := pairA D.host.F 0 (1 - indQ D Q)

open Classical in
theorem evalV_indQ (Q : Finset (Pl D)) (w : Pl D) :
    evalV D.host.F w (indQ D Q) = if w ∈ Q then 1 else 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [indQ, map_sum]
  have h : ∀ v ∈ Q, evalV D.host.F w (singleV D.host.F v 1) = if w = v then 1 else 0 := by
    intro v _
    by_cases hwv : w = v
    · subst hwv
      rw [if_pos rfl]
      change (singleV D.host.F w 1) w = 1
      exact RestrictedProduct.single_eq_same _ _ _
    · rw [if_neg hwv]
      change (singleV D.host.F v 1) w = 0
      exact RestrictedProduct.single_eq_of_ne (fun u : Pl D => u.adicCompletionIntegers D.host.F)
        (1 : Fv D.host.F v) hwv
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]

theorem parts_pairA (α : Af D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) =
        evalV D.host.F w α ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have ha : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  refine ⟨?_, fun w => ?_⟩
  · rw [ha]
    change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  · exact (placeIdempotent_infinite_and_finite_components D w _ α rfl).2 w

open Classical in
theorem parts_idemQ (Q : Finset (Pl D)) :
    infPart D (algebraMap (AF D.host.F) (AE D) (idemQ D Q)) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) (idemQ D Q)) = if w ∈ Q then 1 else 0 := by
  refine ⟨(parts_pairA _).1, fun w => ?_⟩
  rw [idemQ, (parts_pairA _).2 w, evalV_indQ]
  split_ifs
  · rfl
  · exact TensorProduct.zero_tmul _ _

open Classical in
theorem parts_idemQc (Q : Finset (Pl D)) :
    infPart D (algebraMap (AF D.host.F) (AE D) (idemQc D Q)) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) (idemQc D Q)) = if w ∈ Q then 0 else 1 := by
  refine ⟨(parts_pairA _).1, fun w => ?_⟩
  rw [idemQc, (parts_pairA _).2 w, map_sub, map_one, evalV_indQ]
  split_ifs
  · rw [sub_self]; exact TensorProduct.zero_tmul _ _
  · rw [sub_zero]; rfl

theorem mem_idAt_iff_mul (P : Pl D → Prop) [DecidablePred P] (c : AE D) (h0 : infPart D c = 0)
    (hc : ∀ w, compAt D w c = if P w then 1 else 0) (a : AE D) : a ∈ idAt D P ↔ c * a = a := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
  constructor
  · rintro ⟨ha0, haw⟩
    rw [← sub_eq_zero]
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [RingHom.map_sub, RingHom.map_mul, h0, ha0, zero_mul, sub_zero]
    · intro w
      rw [RingHom.map_sub, RingHom.map_mul, hc w]
      by_cases h : P w
      · rw [if_pos h, one_mul, sub_self]
      · rw [if_neg h, haw w h, zero_mul, sub_zero]
  · intro ha
    refine ⟨?_, fun w hw => ?_⟩
    · rw [← ha, RingHom.map_mul, h0, zero_mul]
    · rw [← ha, RingHom.map_mul, hc w, if_neg hw, zero_mul]

theorem mem_idOff_iff_mul (P : Pl D → Prop) [DecidablePred P] (c : AE D) (h0 : infPart D c = 0)
    (hc : ∀ w, compAt D w c = if P w then 1 else 0) (a : AE D) : a ∈ idOff D P ↔ c * a = 0 := by
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]
  constructor
  · intro ha
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [RingHom.map_mul, h0, zero_mul]
    · intro w
      rw [RingHom.map_mul, hc w]
      by_cases h : P w
      · rw [ha w h, mul_zero]
      · rw [if_neg h, zero_mul]
  · intro ha w hw
    have := congrArg (compAt D w) ha
    rwa [RingHom.map_mul, hc w, if_pos hw, one_mul, RingHom.map_zero] at this

open Classical in
theorem mem_idAt_Q_iff (Q : Finset (Pl D)) (a : AE D) :
    a ∈ idAt D (· ∈ Q) ↔ algebraMap (AF D.host.F) (AE D) (idemQ D Q) * a = a :=
  mem_idAt_iff_mul (· ∈ Q) _ (parts_idemQ Q).1 (parts_idemQ Q).2 a

open Classical in
theorem mem_idAt_Qc_iff (Q : Finset (Pl D)) (a : AE D) :
    a ∈ idAt D (· ∉ Q) ↔ algebraMap (AF D.host.F) (AE D) (idemQc D Q) * a = a :=
  mem_idAt_iff_mul (· ∉ Q) _ (parts_idemQc Q).1
    (fun w => by rw [(parts_idemQc Q).2 w]; by_cases h : w ∈ Q <;> simp [h]) a

theorem idemQ_mul_self (Q : Finset (Pl D)) : idemQ D Q * idemQ D Q = idemQ D Q := by
  have e : (idemQ D Q * idemQ D Q : AF D.host.F) = pairA D.host.F 0 (indQ D Q * indQ D Q) :=
    Prod.ext (mul_zero _) rfl
  rw [e, idemQ]
  congr 1
  apply RestrictedProduct.ext
  intro w
  have h := evalV_indQ (D := D) Q w
  change evalV D.host.F w (indQ D Q * indQ D Q) = evalV D.host.F w (indQ D Q)
  rw [map_mul, h]
  split_ifs <;> simp

theorem one_sub_idemQ_mul_self (Q : Finset (Pl D)) :
    (1 - idemQ D Q) * (1 - idemQ D Q) = 1 - idemQ D Q := by
  have h := idemQ_mul_self (D := D) Q
  linear_combination h

theorem mem_congGrp_iff (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, (Formalism.L2.Theta.mt V g - 1) i j ∈ I := by
  rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one]
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
  change ((matHom V g).1.map (Ideal.Quotient.mk I)) i j = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j ↔ _
  rw [Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, map_one]
    rfl
  · simp only [Matrix.one_apply_ne hij, map_zero]
    rfl

def cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) : GA D V →* GA D V :=
  GlobalTheory.UnitaryIdemCut.cutUJ (sigR (AF D.host.F) D.sp.cm.sig) (JR (AF D.host.F) V.gram)
    (algebraMap (AF D.host.F) (AE D) ε) (by rw [← map_mul, hε])
    (GlobalTheory.UnitaryIdemCut.sigR_algebraMap (AF D.host.F) D.sp.cm.sig ε)

theorem mt_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) (g : GA D V) :
    Formalism.L2.Theta.mt V (cutG V ε hε g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt V g +
      (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := rfl

end GlobalTheory.FinPl.SetCut

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionUnitaryLeviRadicalActions
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionUnitaryLeviRadicalActions
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

noncomputable section

namespace GlobalTheory.Core.Rk.SchLaws

variable {D : D7}

theorem isWeilDatumO_zero_one {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χB : (AE D)ˣ →* Circle}
    {omh : WRep (dblSp A) B} (hW : IsWeilDatumO ψ (dblSp A) B 1 χB omh) :
    IsWeilDatumO ψ (zeroSp D) B 1 χB 1 := by
  refine
    { std := hW.std
      hecS := hW.hecS
      hecT := hW.hecT
      resS := ?_
      resT := hW.resT
      om_pres := fun _ _ hf => hf
      om_heis := ?_
      om_aut := fun _ _ _ _ _ _ => rfl
      om_cont := fun _ _ _ => continuous_const
      om_unit := fun _ _ _ _ _ _ _ => rfl
      om_split := ?_ }
  · refine ⟨hW.resS.1, fun η _ a => ?_⟩
    rw [show (zeroSp D).rank = 0 from rfl, pow_zero]
    rfl
  · intro g h w₀ f _
    have e : actO (zeroSp D) B g h w₀ = w₀ := Matrix.ext fun _ j => Fin.elim0 j
    rw [e]
    rfl
  · intro e _ g h _ _ x y hx _
    have hx1 : x = 1 := by
      apply Units.ext
      unfold IsDetAt at hx
      have : IsEmpty (Fin (zeroSp D).rank) := Fin.isEmpty
      rw [Matrix.det_isEmpty] at hx
      rw [hx]
      simp
    refine ⟨1, one_pos, fun ℓ _ f _ => ?_⟩
    simp [splitFacO, hx1]

theorem chr_gramOf_eq (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (x : Mx D B.rank A.rank) (c : skewA D A.rank) :
    chr ψ (gramOf B x) c = ψ ((dblDec A).qS B c x) := by
  rw [chr, HypDec.qS, HypDec.symplOH_extX_extY, pairS, adj_mul, mem_skewA.1 c.2, Matrix.mul_assoc, Matrix.neg_mul,
    Matrix.trace_neg, map_neg (trHalf D), Matrix.trace_mul_comm, gramOf]

theorem sch_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → (∀ h x, sch ψ A B ν 𝓨 (omh (1, h) f) x = sch ψ A B ν 𝓨 f (mt B h⁻¹ ⬝ x)) ∧ (∀ (m : GL (Fin A.rank) (AE D)) x, sch ψ A B ν 𝓨 (omh ((dblDec A).levi m, 1) f) x = ((χB⁻¹ (Matrix.GeneralLinearGroup.det m) : Circle) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det m)) ((B.rank : ℂ) / 2) * sch ψ A B ν 𝓨 f (x ⬝ m.1)) ∧ (∀ c x, sch ψ A B ν 𝓨 (omh ((dblDec A).nC c, 1) f) x = chr ψ (gramOf B x) c * sch ψ A B ν 𝓨 f x) ∧ swSec A B omh ν 𝓨 f 1 = sch ψ A B ν 𝓨 f 0 := by
  intro D ψ A B χB omh hW ν 𝓨 hν f hf
  have h := GlobalTheory.MixSourceFormulas.mixed_source D ψ (dblSp A) (zeroSp D) B A.rank (dblDec A) 1 χB omh 1 hW
    (isWeilDatumO_zero_one hW) ν 𝓨 hν f hf
  refine ⟨fun g x => ?_, fun m x => ?_, fun c x => ?_, ?_⟩
  · exact congrFun (h.target g x) 0
  · calc
      _ = (((χB (Matrix.GeneralLinearGroup.det m))⁻¹ : Circle) : ℂ) *
          (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod B.rank m : ℂ) *
          sch ψ A B ν 𝓨 f (x ⬝ m.1) := congrFun (h.levi m x) 0
      _ = _ := by
        rw [MonoidHom.inv_apply, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod,
          GlobalTheory.Doubling.npow, Complex.ofReal_cpow (NNReal.coe_nonneg _)]
        push_cast
        rfl
  · rw [chr_gramOf_eq ψ A B]
    exact congrFun (h.centre c x) 0
  · rw [sch, mixS_dblDec_zero, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec, Prod.mk_one_one, map_one,
      one_apply_eq_self]

end GlobalTheory.Core.Rk.SchLaws

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionUnitaryLeviRadicalActionsStatement
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerFunction_unitary_levi_radical_actions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → (∀ h x, sch ψ A B ν 𝓨 (omh (1, h) f) x = sch ψ A B ν 𝓨 f (mt B h⁻¹ ⬝ x)) ∧ (∀ (m : GL (Fin A.rank) (AE D)) x, sch ψ A B ν 𝓨 (omh ((dblDec A).levi m, 1) f) x = ((χB⁻¹ (Matrix.GeneralLinearGroup.det m) : Circle) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det m)) ((B.rank : ℂ) / 2) * sch ψ A B ν 𝓨 f (x ⬝ m.1)) ∧ (∀ c x, sch ψ A B ν 𝓨 (omh ((dblDec A).nC c, 1) f) x = chr ψ (gramOf B x) c * sch ψ A B ν 𝓨 f x) ∧ swSec A B omh ν 𝓨 f 1 = sch ψ A B ν 𝓨 f 0 := by
  first | exact @GlobalTheory.Core.Rk.SchLaws.sch_laws | exact GlobalTheory.Core.Rk.SchLaws.sch_laws | (intros; apply GlobalTheory.Core.Rk.SchLaws.sch_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SuppGrp

open GlobalTheory.FinPl

theorem placeIdem_mem_idAt {D : D7} {v : Pl D} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) (P : Pl D → Prop) (hP : P v) :
    algebraMap (AF D.host.F) (AE D) ε ∈ idAt D P := by
  obtain ⟨α, rfl, -, h2⟩ := h
  refine Submodule.mem_inf.2 ⟨?_, (Submodule.mem_iInf _).2 fun u => ?_⟩
  · exact TensorProduct.zero_tmul _ (1 : D.host.E)
  · have hu : u.1 ≠ v := fun e => u.2 (e ▸ hP)
    show (evalV D.host.F u.1 α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [h2 u.1 hu, TensorProduct.zero_tmul]

theorem mem_congGrp {D : D7} (V : HSp D) (I : Ideal (AE D)) (g : GA D V) (h : ∀ i j, (mt V g - 1) i j ∈ I) :
    g ∈ congGrp V I := by
  rw [congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  intro i j
  have h1 := h i j
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at h1
  have : Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [this] at h1
  exact h1

theorem mem_grpAt_of_suppAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V), SuppAt q.e V g → ∀ P : GlobalTheory.FinPl.Pl D → Prop, P q.v → g ∈ GlobalTheory.FinPl.grpAt V P := by
  intro D k _ _ _ _ q V g hg P hP
  obtain ⟨ε, h1, h2⟩ := q.above
  refine mem_congGrp V _ g fun i j => ?_
  have h3 := hg i j
  rw [h2] at h3
  rw [← h3]
  exact Ideal.mul_mem_right _ _ (placeIdem_mem_idAt h1 P hP)

end GlobalTheory.SuppGrp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMemStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_supportedSubgroup_of_suppAt_splitPlace_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V), SuppAt q.e V g → ∀ P : GlobalTheory.FinPl.Pl D → Prop, P q.v → g ∈ GlobalTheory.FinPl.grpAt V P := by
  first | exact @GlobalTheory.SuppGrp.mem_grpAt_of_suppAt | exact GlobalTheory.SuppGrp.mem_grpAt_of_suppAt | (intros; apply GlobalTheory.SuppGrp.mem_grpAt_of_suppAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLocalGLEmbeddingSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLocalGLEmbeddingSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocEmb

theorem exists_gl : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y),
    ∃ gl : GL Y k →* GA D V, Continuous gl ∧ (∀ x, SuppAt q.e V (gl x) ∧ (mt V (gl x)).map q.pr = F.β * x.val * F.γ) ∧
      ∀ g x, SuppAt q.e V g → (mt V g).map q.pr = F.β * x.val * F.γ → g = gl x := by
  intro D k _ _ _ _ q V Y _ _ F
  obtain ⟨h1, -, h3⟩ := (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k (GlobalTheory.LocMod.ofSplit q)).1 V Y F
  choose f hf hu using h1
  have hmul : ∀ x y, f (x * y) = f x * f y := fun x y => (hu (x * y) _ (h3 _ _ _ _ (hf x) (hf y))).symm
  have hone : f 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact (mul_eq_left.1 h.symm)
  let gl : GL Y k →* GA D V := { toFun := f, map_one' := hone, map_mul' := hmul }
  let fr : GlobalTheory.FinPl.Frame q V Y := ⟨F.β, F.γ, F.βγ, F.γβ, gl, fun x => (hf x).1, fun x => (hf x).2⟩
  refine ⟨gl, GlobalTheory.FrameCont.continuous_gl D k q V Y fr, fun x => hf x, fun g x hs hm => hu x g ⟨hs, hm⟩⟩

end GlobalTheory.LocEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLocalGLEmbeddingSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_local_GL_embedding_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y), ∃ gl : GL Y k →* GA D V, Continuous gl ∧ (∀ x, SuppAt q.e V (gl x) ∧ (mt V (gl x)).map q.pr = F.β * x.val * F.γ) ∧ ∀ g x, SuppAt q.e V g → (mt V g).map q.pr = F.β * x.val * F.γ → g = gl x := by
  first | exact @GlobalTheory.LocEmb.exists_gl | exact GlobalTheory.LocEmb.exists_gl | (intros; apply GlobalTheory.LocEmb.exists_gl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateThetaFunLeSchwartzMajorantLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedCoordinate_thetaFun_le_schwartz_majorant_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ≥0, ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ x w, ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ ≤ C * supSob ψ θ N f * ENNReal.ofReal (maj θ K N x) := by
  first | exact @GlobalTheory.Unf.mixS_le_maj | exact GlobalTheory.Unf.mixS_le_maj | (intros; apply GlobalTheory.Unf.mixS_le_maj <;> assumption)
end
