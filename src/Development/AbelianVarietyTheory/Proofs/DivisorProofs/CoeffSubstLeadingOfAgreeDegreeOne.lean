module

public import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnOfCharts
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnRmul
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstLeadingOfAgreeDegreeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstLeadingOfAgreeDegreeOne
noncomputable section

namespace GlobalTheory
namespace LeadSubst

open MvPowerSeries

variable {σ τ R : Type*} [CommRing R]

def Near (n : ℕ) (P Q : MvPowerSeries τ R) : Prop :=
  (n : ℕ∞) ≤ P.order ∧ (n : ℕ∞) ≤ Q.order ∧ ((n + 1 : ℕ) : ℕ∞) ≤ (P - Q).order

theorem Near.one : Near 0 (1 : MvPowerSeries τ R) 1 := by
  simp [Near]

theorem Near.mul {n m : ℕ} {P Q P' Q' : MvPowerSeries τ R} (h : Near n P Q)
    (h' : Near m P' Q') : Near (n + m) (P * P') (Q * Q') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · push_cast; exact (add_le_add h1 h1').trans le_order_mul
  · push_cast; exact (add_le_add h2 h2').trans le_order_mul
  · have e : P * P' - Q * Q' = P * (P' - Q') + (P - Q) * Q' := by ring
    rw [e]
    refine le_trans (le_min ?_ ?_) min_order_le_add
    · refine le_trans ?_ le_order_mul
      refine le_trans (le_of_eq ?_) (add_le_add h1 h3')
      push_cast; ring
    · refine le_trans ?_ le_order_mul
      refine le_trans (le_of_eq ?_) (add_le_add h3 h2')
      push_cast; ring

theorem Near.prod {a b : σ → MvPowerSeries τ R}
    (h : ∀ s, Near 1 (a s) (b s)) (d : σ →₀ ℕ) :
    Near d.degree (d.prod fun s e => a s ^ e) (d.prod fun s e => b s ^ e) := by
  induction d using Finsupp.induction_linear with
  | zero => simpa using (Near.one : Near 0 (1 : MvPowerSeries τ R) 1)
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
      Finsupp.prod_add_index' (by simp) (by simp [pow_add]), map_add (f := _)]
    exact hf.mul hg
  | single s n =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp),
      Finsupp.degree_single]
    induction n with
    | zero => simpa using (Near.one : Near 0 (1 : MvPowerSeries τ R) 1)
    | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul (h s)

theorem near_one {u v : MvPowerSeries τ R} (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (h1 : ∀ γ : τ →₀ ℕ, γ.degree = 1 → coeff γ u = coeff γ v) : Near 1 u v := by
  refine ⟨by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hu,
    by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hv, ?_⟩
  refine nat_le_order fun d hd => ?_
  rw [map_sub, sub_eq_zero]
  rcases (show d.degree = 0 ∨ d.degree = 1 by omega) with h | h
  · rw [(Finsupp.degree_eq_zero_iff d).mp h, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, hu, hv]
  · exact h1 d h

end LeadSubst


open MvPowerSeries in
theorem coeff_subst_leading :
    ∀ (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (u v : σ → MvPowerSeries τ R) (N : ℕ)
      (f : MvPowerSeries σ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      (∀ i (γ : τ →₀ ℕ), γ.degree = 1 → coeff γ (u i) = coeff γ (v i)) →
      (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) →
      ∀ γ : τ →₀ ℕ, (γ.degree < N → coeff γ (subst u f) = 0) ∧
        (γ.degree ≤ N → coeff γ (subst u f) = coeff γ (subst v f)) := by
  intro R _ σ τ _ u v N f hu hv h1 hf γ
  have hn : ∀ s, LeadSubst.Near 1 (u s) (v s) := fun s => LeadSubst.near_one (hu s) (hv s) (h1 s)
  refine ⟨fun hγ => ?_, fun hγ => ?_⟩
  · rw [coeff_subst (hasSubst_of_constantCoeff_zero hu)]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    by_cases hd : d.degree < N
    · rw [hf d hd, zero_smul]
    · rw [coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast (by omega : γ.degree < d.degree))
        (LeadSubst.Near.prod hn d).1), smul_zero]
  · rw [coeff_subst (hasSubst_of_constantCoeff_zero hu),
      coeff_subst (hasSubst_of_constantCoeff_zero hv)]
    refine finsum_congr fun d => ?_
    by_cases hd : d.degree < N
    · rw [hf d hd, zero_smul, zero_smul]
    · congr 1
      have h := coeff_of_lt_order (d := γ) (lt_of_lt_of_le
        (by exact_mod_cast (by omega : γ.degree < d.degree + 1)) (LeadSubst.Near.prod hn d).2.2)
      rwa [map_sub, sub_eq_zero] at h

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstLeadingOfAgreeDegreeOneStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_subst_leading_of_agree_degree_one : ∀ (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (u v : σ → MvPowerSeries τ R) (N : ℕ) (f : MvPowerSeries σ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i (γ : τ →₀ ℕ), γ.degree = 1 → coeff γ (u i) = coeff γ (v i)) → (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ γ : τ →₀ ℕ, (γ.degree < N → coeff γ (subst u f) = 0) ∧ (γ.degree ≤ N → coeff γ (subst u f) = coeff γ (subst v f)) := by
  first | exact @GlobalTheory.coeff_subst_leading | exact GlobalTheory.coeff_subst_leading | (intros; apply GlobalTheory.coeff_subst_leading <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemIntegralDifferentialSubmodule
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemIntegralDifferentialSubmodule
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace Katz

theorem derivation_prod_erase {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    [DecidableEq ι] (D : Derivation R A A) (f : ι → A) (S : Finset ι) :
    D (∏ s ∈ S, f s) = ∑ i ∈ S, (∏ s ∈ S.erase i, f s) * D (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha,
      smul_eq_mul, smul_eq_mul, Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hai : a ≠ i := by rintro rfl; exact ha hi
    rw [Finset.erase_insert_of_ne hai,
      Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)), mul_assoc]

theorem pderiv_prod_pow {R τ σ : Type} [CommRing R] [Fintype σ] [DecidableEq σ]
    (u : σ → MvPowerSeries τ R) (a : σ → ℕ) (j : τ) :
    pderiv j (∏ s, u s ^ a s) =
      ∑ i, a i • ((∏ s ∈ Finset.univ.erase i, u s ^ a s) * (u i ^ (a i - 1) * pderiv j (u i))) := by
  rw [derivation_prod_erase]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pderiv_pow, nsmul_eq_mul, mul_assoc, mul_left_comm]

theorem subst_mem_quasiInt : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u : σ → MvPowerSeries (τ) (Fr p k)) (f : MvPowerSeries (σ) (Fr p k)), (∀ i, constantCoeff (u i) = 0) → (∀ i, u i ∈ intBy p k τ 1) → f ∈ quasiInt p k σ → subst u f ∈ quasiInt p k τ := by
  intro p _ k _ _ _ σ τ _ u f hu0 hu hf
  classical
  have : Fintype σ := Fintype.ofFinite σ
  set φ := algebraMap (WittVector p k) (Fr p k) with hφ
  have ha : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  have hlift : ∀ i, ∃ v : MvPowerSeries τ (WittVector p k), MvPowerSeries.map φ v = u i := by
    intro i
    have hui : ∀ α, ∃ w : WittVector p k, coeff α (u i) = φ (1 * w) := hu i
    let w0 : MvPowerSeries τ (WittVector p k) := fun α => (hui α).choose
    refine ⟨w0, ?_⟩
    ext α
    rw [coeff_map, (hui α).choose_spec, one_mul]
    rfl
  choose v hv using hlift
  intro γ j
  rw [coeff_subst ha]
  have hP : ∀ α : σ →₀ ℕ, (α.prod fun s e => u s ^ e) =
      MvPowerSeries.map φ (∏ s, v s ^ α s) := by
    intro α
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod]
    exact Finset.prod_congr rfl fun s _ => by rw [map_pow, hv]
  have hterm : ∀ α : σ →₀ ℕ,
      (γ j : Fr p k) * (coeff α f • coeff γ (α.prod fun s e => u s ^ e)) ∈ φ.range := by
    intro α
    rw [hP, coeff_map, smul_eq_mul]
    by_cases hγ : γ j = 0
    · rw [hγ, Nat.cast_zero, zero_mul]; exact zero_mem _
    have hle : Finsupp.single j 1 ≤ γ := by
      intro t
      by_cases ht : t = j
      · subst ht; simp only [Finsupp.single_eq_same]; omega
      · rw [Finsupp.single_apply, if_neg (Ne.symm ht)]; exact Nat.zero_le _
    set δ := γ - Finsupp.single j 1 with hδ
    have hδγ : δ + Finsupp.single j 1 = γ := tsub_add_cancel_of_le hle
    have hδj : (δ j : Fr p k) + 1 = γ j := by
      rw [← hδγ, Finsupp.add_apply, Finsupp.single_eq_same]; push_cast; rfl
    have key := coeff_pderiv (R := WittVector p k) (i := j) (∏ s, v s ^ α s) δ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hδγ, pderiv_prod_pow, map_sum] at key
    have hk : (γ j : Fr p k) * φ (coeff γ (∏ s, v s ^ α s)) =
        φ (∑ i, coeff δ (α i • ((∏ s ∈ Finset.univ.erase i, v s ^ α s) *
          (v i ^ (α i - 1) * pderiv j (v i))))) := by
      rw [key, map_mul, map_add (f := _), map_natCast, map_one, ← hδj]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mul_left_comm, hk, map_sum, Finset.mul_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    obtain ⟨w, hw⟩ := (hf : ∀ (α : σ →₀ ℕ) (i : σ), ∃ w : WittVector p k,
      (α i : Fr p k) * coeff α f = φ w) α i
    rw [map_nsmul, map_nsmul, nsmul_eq_mul, ← mul_assoc, mul_comm (coeff α f), hw, ← map_mul]
    exact ⟨_, rfl⟩
  have hfin := coeff_subst_finite ha f γ
  rw [finsum_eq_sum _ hfin, Finset.mul_sum]
  have hmem : (γ j : Fr p k) * ∑ α ∈ hfin.toFinset, coeff α f • coeff γ (α.prod fun s e => u s ^ e)
      ∈ φ.range := by
    rw [Finset.mul_sum]; exact Subring.sum_mem _ fun α _ => hterm α
  rw [← Finset.mul_sum]
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, hw.symm⟩

end Katz

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemIntegralDifferentialSubmoduleStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_mem_integralDifferentialSubmodule : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u : σ → MvPowerSeries (τ) (Fr p k)) (f : MvPowerSeries (σ) (Fr p k)), (∀ i, constantCoeff (u i) = 0) → (∀ i, u i ∈ intBy p k τ 1) → f ∈ quasiInt p k σ → subst u f ∈ quasiInt p k τ := by
  first | exact @GlobalTheory.Katz.subst_mem_quasiInt | exact GlobalTheory.Katz.subst_mem_quasiInt | (intros; apply GlobalTheory.Katz.subst_mem_quasiInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixRepBasicOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixTransport

theorem lbIso_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem lbIso_pull_pull {X Y Y' Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) (G : Z ⟶ Y) (F' : Y' ⟶ X)
    (G' : Z ⟶ Y') (h : G ≫ F = G' ≫ F') : LBIso ((L.pull F).pull G) ((L.pull F').pull G') :=
  LBIso.chartPull
    (chartPullLinComb L F (fun _ : PUnit => G) (fun _ => G ≫ F) (fun _ => 1) (𝟙 Z)
      fun _ => (Category.id_comp _).symm)
    (chartPullLinComb L F' (fun _ : PUnit => G') (fun _ => G ≫ F) (fun _ => 1) (𝟙 Z)
      fun _ => by rw [Category.id_comp, h])
    (lbIso_self (pull_isLB hL (G ≫ F)))

theorem lbIso_pull {X Y : Scheme.{0}} {L M : LB X} (H : LBIso L M) (h : Y ⟶ X) : LBIso (L.pull h) (M.pull h) :=
  LBIso.chartPull (chartPullPull L h h rfl) (chartPullPull M h h rfl) H

theorem lbIso_congr {X : Scheme.{0}} {P P' Q Q' : LB X} (hP : P.IsLB) (hP' : P'.IsLB) (hQ : Q.IsLB) (hQ' : Q'.IsLB)
    (e₁ : LBIso P' P) (H : LBIso P Q) (e₂ : LBIso Q Q') : LBIso P' Q' :=
  LBIso.trans hP' hQ hQ' (LBIso.trans hP' hP hQ e₁ H) e₂

section Transport

variable {S S₁ S₂ : Scheme.{0}} (e : S₁ ≅ S₂) {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
  (hL : L.IsLB) (hM : M.IsLB) {Af Bf : Over S₂} [GrpObj Af] [GrpObj Bf] (φA : Af.left ⟶ A.left)
  (φB : Bf.left ⟶ B.left)

def transport (R : HomFixRep Af Bf (L.pull φA) (M.pull φB)) :
    HomFixRep ((Over.pullback e.hom).obj Af) ((Over.pullback e.hom).obj Bf)
      (L.pull (pullback.fst Af.hom e.hom ≫ φA)) (M.pull (pullback.fst Bf.hom e.hom ≫ φB)) where
  H := R.H
  π := R.π ≫ e.inv
  AH := R.AH
  BH := R.BH
  φA := pullback.lift R.φA (R.AH.hom ≫ R.π ≫ e.inv) (by simp [R.pbA.1.w])
  φB := pullback.lift R.φB (R.BH.hom ≫ R.π ≫ e.inv) (by simp [R.pbB.1.w])
  pbA := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor e.hom (R.π ≫ e.inv) (R.pbA.congr (by simp) rfl)
  pbB := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor e.hom (R.π ≫ e.inv) (R.pbB.congr (by simp) rfl)
  Φ := R.Φ
  hom := R.hom
  iso := lbIso_congr (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)
    (pull_isLB (pull_isLB (pull_isLB hM _) _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _)
    (lbIso_pull_pull hL _ _ _ _ (by erw [pullback.lift_fst_assoc])) R.iso
    (lbIso_pull (lbIso_pull_pull hM _ _ _ _ (by erw [pullback.lift_fst_assoc])) _)
  rep := by
    intro T t A' B' _ _ φA' φB' Φ' hA hB hΦ hI
    have hA₂ := hA.comp (isGrpPullback_pullback Af e.hom)
    have hB₂ := hB.comp (isGrpPullback_pullback Bf e.hom)
    obtain ⟨h, ⟨hπ, ψA, ψB, pA, pB, eA, eB, eΦ⟩, hu⟩ := R.rep T (t ≫ e.hom) A' B'
      (φA' ≫ pullback.fst Af.hom e.hom) (φB' ≫ pullback.fst Bf.hom e.hom) Φ' hA₂ hB₂ hΦ
      (lbIso_congr (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)
        (pull_isLB (pull_isLB (pull_isLB hM _) _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _)
        (lbIso_pull_pull hL φA (φA' ≫ pullback.fst Af.hom e.hom) (pullback.fst Af.hom e.hom ≫ φA) φA' (by simp)) hI
        (lbIso_pull (lbIso_pull_pull hM (pullback.fst Bf.hom e.hom ≫ φB) φB' φB (φB' ≫ pullback.fst Bf.hom e.hom)
          (by simp)) Φ'.left))
    refine ⟨h, ⟨?_, ψA, ψB, pA, pB, ?_, ?_, eΦ⟩, ?_⟩
    · rw [← Category.assoc, hπ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst]; exact eA
      · simp only [Category.assoc, pullback.lift_snd]
        rw [reassoc_of% pA.1.w, reassoc_of% hπ, Iso.hom_inv_id, Category.comp_id]
        exact hA.1.w.symm
    · apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst]; exact eB
      · simp only [Category.assoc, pullback.lift_snd]
        rw [reassoc_of% pB.1.w, reassoc_of% hπ, Iso.hom_inv_id, Category.comp_id]
        exact hB.1.w.symm
    · rintro h' ⟨hπ', ψA', ψB', pA', pB', eA', eB', eΦ'⟩
      refine hu h' ⟨by rw [← hπ']; simp, ψA', ψB', pA', pB', by rw [← eA', Category.assoc]; erw [pullback.lift_fst],
        by rw [← eB', Category.assoc]; erw [pullback.lift_fst], eΦ'⟩

end Transport

end GlobalTheory.HomFixTransport


open GlobalTheory.HomFixTransport in
theorem GlobalTheory.HomFixTransport.homFixRep_basicOpen : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (f : Rg), L.IsLB → M.IsLB → (∀ (Af Bf : Over (Sp (Localization.Away f))) [GrpObj Af] [GrpObj Bf] (φA : Af.left ⟶ A.left) (φB : Bf.left ⟶ B.left), IsGrpPullback Af A (spMap (algebraMap Rg (Localization.Away f))) φA → IsGrpPullback Bf B (spMap (algebraMap Rg (Localization.Away f))) φB → ∃ R : HomFixRep Af Bf (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∀ U : (Sp Rg).Opens, U = PrimeSpectrum.basicOpen f → ∃ (AU : Over U.toScheme) (_ : GrpObj AU) (BU : Over U.toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A U.ι φA ∧ IsGrpPullback BU B U.ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ A B _ _ L M f hL hM hyp U hU
  have hr : Set.range U.ι = Set.range (spMap (algebraMap Rg (Localization.Away f))) := by
    rw [Scheme.Opens.range_ι, hU]
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).symm
  haveI : IsOpenImmersion (spMap (algebraMap Rg (Localization.Away f))) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Rg (Localization.Away f)))))
  let e := IsOpenImmersion.isoOfRangeEq U.ι (spMap (algebraMap Rg (Localization.Away f))) hr
  have he : e.hom ≫ spMap (algebraMap Rg (Localization.Away f)) = U.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  obtain ⟨R, h₁, h₂, h₃⟩ := hyp _ _ _ _ (isGrpPullback_pullback A (spMap (algebraMap Rg (Localization.Away f))))
    (isGrpPullback_pullback B (spMap (algebraMap Rg (Localization.Away f))))
  refine ⟨_, inferInstance, _, inferInstance, _, _,
    ((isGrpPullback_pullback _ e.hom).comp (isGrpPullback_pullback A _)).congr he rfl,
    ((isGrpPullback_pullback _ e.hom).comp (isGrpPullback_pullback B _)).congr he rfl,
    transport e hL hM _ _ R, ?_, ?_, ?_⟩
  · show QuasiCompact (R.π ≫ e.inv); infer_instance
  · show IsSeparated (R.π ≫ e.inv); infer_instance
  · show LocallyOfFiniteType (R.π ≫ e.inv); infer_instance
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarIntegralEqUnitriangularChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarIntegralEqUnitriangularChart
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal Matrix

namespace GlobalTheory.FlagQuotHaar

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def baseGL (X : Data E r) (τ : X.Ψ) : GL (Fin r) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (mat (baseFr X) τ) (PeterssonCompare.det_baseFr X τ)

theorem val_baseGL (X : Data E r) (τ : X.Ψ) : (baseGL X τ : Matrix (Fin r) (Fin r) ℂ) = mat (baseFr X) τ := rfl


omit [NumberField E] [IsCMField E] in
theorem gram_mul_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (A g : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (A * g) = gᵀ * gram τ G A * g.map (starRingEnd ℂ) := by
  rw [UnitaryFrames.gram_eq_mul, UnitaryFrames.gram_eq_mul, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]


omit [NumberField E] [IsCMField E] in
theorem isometry_iff_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (n : Matrix (Fin r) (Fin r) ℂ)
    (P : GL (Fin r) ℂ) :
    (∀ u w, hermC τ G (n *ᵥ u) (n *ᵥ w) = hermC τ G u w) ↔
      gram τ G (n * (P : Matrix (Fin r) (Fin r) ℂ)) = gram τ G P := by
  constructor
  · intro h
    ext a b
    simp only [gram, Matrix.of_apply, UnitaryFrames.col_mul', h]
  · intro h u w
    obtain ⟨u', rfl⟩ : ∃ u', u = (P : Matrix (Fin r) (Fin r) ℂ) *ᵥ u' :=
      ⟨((P⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ u, by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
    obtain ⟨w', rfl⟩ : ∃ w', w = (P : Matrix (Fin r) (Fin r) ℂ) *ᵥ w' :=
      ⟨((P⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ w, by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, UnitaryFrames.hermC_mulVec, UnitaryFrames.hermC_mulVec, h]

def toIso (X : Data E r) (g : RealGrp X) : UnitaryFrames.unitarySubgroup X :=
  ⟨fun τ => baseGL X τ * ((g τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹, by
    intro τ
    refine (isometry_iff_gram τ.1 X.Gm _ (baseGL X τ)).2 ?_
    rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul, gram_mul_right, val_baseGL, baseFr_mem X τ]
    exact (g τ).2⟩

def ofIso (X : Data E r) (h : UnitaryFrames.unitarySubgroup X) : RealGrp X :=
  fun τ => ⟨(baseGL X τ)⁻¹ * (h : X.Ψ → GL (Fin r) ℂ) τ * baseGL X τ, by
    have hu : gram τ.1 X.Gm (((h : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) *
        (baseGL X τ : Matrix (Fin r) (Fin r) ℂ)) = gram τ.1 X.Gm (baseGL X τ) :=
      (isometry_iff_gram τ.1 X.Gm _ (baseGL X τ)).1 (h.2 τ)
    have e : ((h : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * (baseGL X τ : Matrix (Fin r) (Fin r) ℂ) =
        (baseGL X τ : Matrix (Fin r) (Fin r) ℂ) *
          (((baseGL X τ)⁻¹ * (h : X.Ψ → GL (Fin r) ℂ) τ * baseGL X τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [e, gram_mul_right, val_baseGL, baseFr_mem X τ] at hu
    exact hu⟩

def isoEquiv (X : Data E r) : RealGrp X ≃ₜ* UnitaryFrames.unitarySubgroup X where
  toFun := toIso X
  invFun := ofIso X
  left_inv g := by
    funext τ
    apply Subtype.ext
    show (baseGL X τ)⁻¹ * (baseGL X τ * ((g τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹) * baseGL X τ = _
    group
  right_inv h := by
    apply Subtype.ext
    funext τ
    show baseGL X τ * ((baseGL X τ)⁻¹ * (h : X.Ψ → GL (Fin r) ℂ) τ * baseGL X τ) * (baseGL X τ)⁻¹ = _
    group
  map_mul' g g' := by
    apply Subtype.ext
    funext τ
    show baseGL X τ * (((g * g') τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹ =
      (baseGL X τ * ((g τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹) *
        (baseGL X τ * ((g' τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹)
    simp only [Pi.mul_apply, Subgroup.coe_mul]
    group
  continuous_toFun := by
    refine continuous_induced_rng.2 (continuous_pi fun τ => ?_)
    exact (continuous_const.mul (continuous_subtype_val.comp (continuous_apply τ))).mul continuous_const
  continuous_invFun := by
    refine continuous_pi fun τ => continuous_induced_rng.2 ?_
    exact (continuous_const.mul ((continuous_apply τ).comp continuous_subtype_val)).mul continuous_const

theorem frameOf_eq_lmulC (X : Data E r) (g : RealGrp X) :
    frameOf X g = X.lmulC (fun τ => (((toIso X g : UnitaryFrames.unitarySubgroup X) : X.Ψ → GL (Fin r) ℂ) τ :
      Matrix (Fin r) (Fin r) ℂ)) (baseFr X) := by
  funext τ
  have key : mat (frameOf X g) τ = mat (X.lmulC (fun τ => (((toIso X g : UnitaryFrames.unitarySubgroup X) :
      X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) (baseFr X)) τ := by
    rw [PeterssonCompare.mat_frameOf, show ∀ (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (x : Frame X.Ψ r),
    mat (X.lmulC n x) τ = n τ * mat x τ from fun _ _ => rfl, ← val_baseGL]
    show _ = ((baseGL X τ * ((g τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹ : GL (Fin r) ℂ) :
    Matrix (Fin r) (Fin r) ℂ) * _
    rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
  exact key

theorem muF_univ_ne_zero (X : Data E r) {x0 : Frame X.Ψ r} (h : IsOrth X x0) : muF X x0 Set.univ ≠ 0 := by
  have hO := OntoB.isOpen_OmF X x0
  unfold muF
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  intro h0
  have hm : AEMeasurable (fun z => ENNReal.ofReal (densF X x0 z)) (volume.restrict (OmF X x0)) :=
    (OntoB.densF_continuousOn.aemeasurable hO.measurableSet).ennreal_ofReal
  rw [lintegral_eq_zero_iff' hm] at h0
  have h1 : ∀ᵐ z ∂(volume.restrict (OmF X x0)), False := by
    filter_upwards [h0, ae_restrict_mem hO.measurableSet] with z hz hz'
    have := OntoB.densF_pos hz'
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hz
    linarith
  rw [ae_iff] at h1
  simp only [not_false_eq_true, Set.setOf_true, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter] at h1
  exact (hO.measure_pos volume ⟨0, IW.zero_mem_OmF X x0 h⟩).ne' h1

theorem exists_haarChart (X : Data E r) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ HaarChart X c := by
  classical
  set H := UnitaryFrames.unitarySubgroup X with hHdef
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  have hHm : ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ) := fun _ => Iff.rfl
  obtain ⟨hLC, hSC, -⟩ := UnitaryFrames.unitary_group_frames.2 r X H hHm
  haveI := hLC
  haveI := hSC
  have hx0 : IsOrth X (baseFr X) := fun τ => baseFr_mem X τ
  obtain ⟨ν, hνl, hνf, hν⟩ := UnitaryInvMeasure.invMeas FrameMeasureClosed.measure_statements.2.1
    GramSchmidtCont.exists_continuous_gramSchmidt isOrth_rmul_iff_unitary_diagonal
    (SatFin.muF_sat_lt_top FrameMeasureClosed.measure_statements.2.1)
    UnitaryFrames.unitary_group_frames.2 r X H hHm (baseFr X) hx0
  haveI := hνl
  haveI := hνf
  haveI : (haarR X).IsHaarMeasure := by unfold haarR; infer_instance
  set e := isoEquiv X
  set μ : Measure H := (haarR X).map e with hμdef
  haveI : μ.IsHaarMeasure := e.isHaarMeasure_map (haarR X)
  have hs := Measure.isMulLeftInvariant_eq_smul ν μ
  set s := ν.haarScalarFactor μ
  set L : H → Frame X.Ψ r := fun h =>
    X.lmulC (fun τ => ((h : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) (baseFr X)

  have hR : ∀ F : H → ℝ≥0∞, ∫⁻ g, F (e g) ∂haarR X = ∫⁻ h, F h ∂μ := by
    intro F
    have := lintegral_map_equiv F (e.toHomeomorph.toMeasurableEquiv) (μ := haarR X)
    exact this.symm
  have hs0 : s ≠ 0 := by
    intro h0
    have h1 := hν (fun _ => 1) measurable_const (fun _ _ _ _ => rfl)
    simp only [lintegral_const, one_mul] at h1
    rw [hs, h0, zero_smul, Measure.coe_zero, Pi.zero_apply] at h1
    exact muF_univ_ne_zero X hx0 h1.symm
  refine ⟨((s : ℝ≥0∞))⁻¹, ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top,
    ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2 hs0), fun φ hφ hφb => ?_⟩
  have h1 := hν φ hφ hφb
  rw [hs, lintegral_smul_measure] at h1
  have h2 : ∫⁻ g, φ (frameOf X g) ∂haarR X = ∫⁻ h, φ (L h) ∂μ := by
    rw [← hR]
    refine lintegral_congr fun g => ?_
    rw [frameOf_eq_lmulC]
    rfl
  rw [h2, ← h1, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hs0)
    ENNReal.coe_ne_top, one_mul]

end

end GlobalTheory.FlagQuotHaar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarIntegralEqUnitriangularChartStatement
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haarIntegral_eq_unitriangularChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r), ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ HaarChart X c := by
  first | exact @GlobalTheory.FlagQuotHaar.exists_haarChart | exact GlobalTheory.FlagQuotHaar.exists_haarChart | (intros; apply GlobalTheory.FlagQuotHaar.exists_haarChart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMemOfSpanBaseChange
namespace GlobalTheory.LKInv

open Module Polynomial TensorProduct

theorem isUnit_of_isUnit_mulLeft {k A : Type} [Field k] [Ring A] [Algebra k A] (x : A)
    (h : IsUnit (LinearMap.mulLeft k x)) : IsUnit x := by
  set u := h.unit with hu
  set y : A := ((u⁻¹ : (Module.End k A)ˣ) : Module.End k A) 1 with hy
  have hxy : x * y = 1 := by
    change LinearMap.mulLeft k x (((u⁻¹ : (Module.End k A)ˣ) : Module.End k A) 1) = 1
    rw [← Module.End.mul_apply]
    have : LinearMap.mulLeft k x = (u : Module.End k A) := rfl
    rw [this, Units.mul_inv, Module.End.one_apply]
  have hly : LinearMap.mulLeft k y = ((u⁻¹ : (Module.End k A)ˣ) : Module.End k A) := by
    have e : (u : Module.End k A) * LinearMap.mulLeft k y = 1 := by
      change LinearMap.mulLeft k x * LinearMap.mulLeft k y = 1
      ext z
      simp [← mul_assoc, hxy]
    calc LinearMap.mulLeft k y = ((u⁻¹ : (Module.End k A)ˣ) : Module.End k A) *
          ((u : Module.End k A) * LinearMap.mulLeft k y) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [e, mul_one]
  have hyx : y * x = 1 := by
    have := congrArg (fun f : Module.End k A => f 1) (Units.inv_mul u)
    simp only [← hly] at this
    change y * (x * 1) = 1 at this
    rwa [mul_one] at this
  exact ⟨⟨x, y, hxy, hyx⟩, rfl⟩

theorem baseChange_mulLeft {k A K : Type} [Field k] [Ring A] [Algebra k A] [Field K] [Algebra k K]
    (a : A) : (LinearMap.mulLeft k a).baseChange K = LinearMap.mulLeft K ((1 : K) ⊗ₜ[k] a) := by
  ext x
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem exists_isUnit_mem_of_span_baseChange {k A K : Type} [Field k] [Infinite k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] [Field K] [Algebra k K] (V : Submodule k A) (u : K ⊗[k] A)
    (hu : u ∈ Submodule.span K ((fun a : A => (1 : K) ⊗ₜ[k] a) '' (V : Set A))) (hunit : IsUnit u) :
    ∃ x ∈ V, IsUnit x := by
  classical
  set r := finrank k V
  let b : Basis (Fin r) k V := Module.finBasis k V
  set m := finrank k A
  let bA : Basis (Fin m) k A := Module.finBasis k A
  let M : Fin r → Matrix (Fin m) (Fin m) k := fun i => LinearMap.toMatrix bA bA (LinearMap.mulLeft k (b i : A))
  set D : MvPolynomial (Fin r) k := (∑ i, (MvPolynomial.X i : MvPolynomial (Fin r) k) •
      (M i).map (MvPolynomial.C : k →+* MvPolynomial (Fin r) k)).det with hD
  have key : ∀ {T : Type} [CommRing T] (ψ : MvPolynomial (Fin r) k →+* T),
      ψ D = (∑ i, ψ (MvPolynomial.X i) • (M i).map (ψ.comp (MvPolynomial.C : k →+* MvPolynomial (Fin r) k))).det := by
    intro T _ ψ
    rw [hD, RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    ext p q
    simp [Matrix.sum_apply]

  have hlin : ∀ t : Fin r → k, ∑ i, t i • M i =
      LinearMap.toMatrix bA bA (LinearMap.mulLeft k (∑ i, t i • (b i : A))) := by
    intro t
    have : LinearMap.mulLeft k (∑ i, t i • (b i : A)) = ∑ i, t i • LinearMap.mulLeft k (b i : A) := by
      ext z; simp [Finset.sum_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    simp [M, map_smul]

  have hD0 : D ≠ 0 := by
    have hspan : Submodule.span K ((fun a : A => (1 : K) ⊗ₜ[k] a) '' (V : Set A)) ≤
        Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[k] (b i : A)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      have hrep := b.sum_repr ⟨a, ha⟩
      have : (1 : K) ⊗ₜ[k] a = ∑ i, (algebraMap k K (b.repr ⟨a, ha⟩ i)) • ((1 : K) ⊗ₜ[k] (b i : A)) := by
        conv_lhs => rw [show a = ((⟨a, ha⟩ : V) : A) from rfl, ← hrep]
        simp only [Submodule.coe_sum, Submodule.coe_smul, TensorProduct.tmul_sum, TensorProduct.tmul_smul,
          algebraMap_smul]
      show (1 : K) ⊗ₜ[k] a ∈ Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[k] (b i : A))
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hspan hu)
    intro h0
    have h1 := key (MvPolynomial.eval₂Hom (algebraMap k K) s)
    rw [h0, map_zero] at h1
    have hmat : ∑ i, (MvPolynomial.eval₂Hom (algebraMap k K) s) (MvPolynomial.X i) •
        (M i).map ((MvPolynomial.eval₂Hom (algebraMap k K) s).comp MvPolynomial.C) =
        LinearMap.toMatrix (Algebra.TensorProduct.basis K bA) (Algebra.TensorProduct.basis K bA)
          (LinearMap.mulLeft K u) := by
      rw [← hs]
      have : LinearMap.mulLeft K (∑ i, s i • (1 : K) ⊗ₜ[k] (b i : A)) =
          ∑ i, s i • LinearMap.mulLeft K ((1 : K) ⊗ₜ[k] (b i : A)) := by
        ext z; simp [Finset.sum_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← baseChange_mulLeft, LinearMap.toMatrix_baseChange]
      simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      rw [MvPolynomial.eval₂Hom_comp_C]
    rw [hmat, LinearMap.det_toMatrix] at h1
    have hu' : IsUnit (LinearMap.mulLeft K u) := by
      obtain ⟨w, rfl⟩ := hunit
      refine ⟨⟨LinearMap.mulLeft K (w : K ⊗[k] A), LinearMap.mulLeft K ((w⁻¹ : (K ⊗[k] A)ˣ) : K ⊗[k] A),
        ?_, ?_⟩, rfl⟩ <;> ext z <;> simp [← mul_assoc]
    have := (LinearMap.isUnit_iff_isUnit_det _).1 hu'
    rw [← h1] at this
    exact not_isUnit_zero this

  obtain ⟨t, ht⟩ : ∃ t : Fin r → k, MvPolynomial.eval t D ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hD0 (MvPolynomial.funext fun x => by rw [hne x, map_zero])
  refine ⟨∑ i, t i • (b i : A), Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2, ?_⟩
  apply isUnit_of_isUnit_mulLeft (k := k)
  rw [LinearMap.isUnit_iff_isUnit_det, ← LinearMap.det_toMatrix bA, ← hlin, isUnit_iff_ne_zero]
  rw [key] at ht
  convert ht using 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval_X]
  congr 1
  ext p q
  simp

end GlobalTheory.LKInv

namespace GlobalTheory.LKInv

open Module Polynomial TensorProduct

theorem exists_unit_conj_of_baseChange {k A K : Type} [Field k] [Infinite k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [Field K] [Algebra k K] (x₀ x : A) (w : (K ⊗[k] A)ˣ)
    (hw : (w : K ⊗[k] A) * ((1 : K) ⊗ₜ[k] x₀) = ((1 : K) ⊗ₜ[k] x) * w) :
    ∃ g : Aˣ, (g : A) * x₀ = x * g := by
  let a : A →ₗ[k] A := LinearMap.mulRight k x₀ - LinearMap.mulLeft k x
  let a' : K ⊗[k] A →ₗ[K] K ⊗[k] A :=
    LinearMap.mulRight K ((1 : K) ⊗ₜ[k] x₀) - LinearMap.mulLeft K ((1 : K) ⊗ₜ[k] x)
  have hbc := (GlobalTheory.BadCount.finrank_iInf_ker_baseChange k K A (K ⊗[k] A) Unit
    (TensorProduct.mk k K A 1) (TensorProduct.isBaseChange k A K) (fun _ => a) (fun _ => a')
    (fun _ v => by simp [a, a', Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub])).2
  rw [_root_.iInf_const, _root_.iInf_const] at hbc
  have hwmem : (w : K ⊗[k] A) ∈ LinearMap.ker a' := by
    rw [LinearMap.mem_ker]
    simp [a', hw]
  rw [hbc] at hwmem
  obtain ⟨y, hyV, hyu⟩ := exists_isUnit_mem_of_span_baseChange (K := K) (LinearMap.ker a)
    (w : K ⊗[k] A) hwmem w.isUnit
  refine ⟨hyu.unit, ?_⟩
  rw [LinearMap.mem_ker] at hyV
  simpa [a, sub_eq_zero] using hyV

theorem charpoly_eq_map_minpoly {F B : Type} [Field F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    {n : ℕ} (e : AlgebraicClosure F ⊗[F] B ≃ₐ[AlgebraicClosure F] Matrix (Fin n) (Fin n) (AlgebraicClosure F))
    (y : B) (hsep : (minpoly F y).Separable) (hdeg : (minpoly F y).natDegree = n) :
    (e ((1 : AlgebraicClosure F) ⊗ₜ[F] y)).charpoly = (minpoly F y).map (algebraMap F (AlgebraicClosure F)) := by
  set K := AlgebraicClosure F
  set z : K ⊗[F] B := (1 : K) ⊗ₜ[F] y with hz
  have hzi : IsIntegral K z := IsIntegral.of_finite K z
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hzr : z = Algebra.TensorProduct.includeRight y := rfl
  have hdvd : minpoly K z ∣ (minpoly F y).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hzr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := GlobalTheory.CentSep.natDegree_minpoly_le_baseChange K y hzi
  have hmap0 : (minpoly F y).map (algebraMap F K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap F K).injective).mpr (minpoly.ne_zero hyi)
  have hzdeg : (minpoly K z).natDegree = n := by
    refine le_antisymm ?_ (hdeg ▸ hge)
    calc (minpoly K z).natDegree ≤ ((minpoly F y).map (algebraMap F K)).natDegree :=
          natDegree_le_of_dvd hdvd hmap0
      _ = n := by rw [natDegree_map, hdeg]
  have hzeq : minpoly K z = (minpoly F y).map (algebraMap F K) := by
    have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hdvd
      (by rw [natDegree_map, hdeg, hzdeg])
    rw [this, ((minpoly.monic hyi).map _).leadingCoeff, C_1, one_mul]
  set N := e z with hN
  have hmN : minpoly K N = minpoly K z := minpoly.algEquiv_eq e z
  have hd : minpoly K N ∣ N.charpoly := minpoly.dvd K N (Matrix.aeval_self_charpoly N)
  rw [hmN] at hd
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hd
    (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hzdeg])
  rw [this, (Matrix.charpoly_monic N).leadingCoeff, C_1, one_mul, hzeq]

theorem exists_unit_conj_of_minpoly_eq (F B : Type) [Field F] [Infinite F] [Ring B] [Algebra F B]
    [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ)
    (hn : Module.finrank F B = n ^ 2) (x₀ x : B) (hsep : (minpoly F x₀).Separable)
    (hdeg : (minpoly F x₀).natDegree = n) (hmin : minpoly F x = minpoly F x₀) :
    ∃ g : Bˣ, (g : B) * x₀ = x * g := by
  classical
  obtain ⟨m, hm0, hmB, ⟨e⟩⟩ := GroundTheory.Brauer.exists_algEquiv_matrix_algebraicClosure F B
  have hmn : m = n := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hmB.symm.trans hn)
  subst hmn
  set K := AlgebraicClosure F
  set N₀ := e ((1 : K) ⊗ₜ[F] x₀) with hN₀
  set N := e ((1 : K) ⊗ₜ[F] x) with hN
  have hc₀ := charpoly_eq_map_minpoly e x₀ hsep hdeg
  have hc := charpoly_eq_map_minpoly e x (hmin ▸ hsep) (hmin ▸ hdeg)
  rw [hmin] at hc
  have hsepK : (Matrix.toLin' N₀).charpoly.Separable := by
    rw [Matrix.charpoly_toLin', hc₀]; exact hsep.map
  obtain ⟨e', he'⟩ := GroundTheory.Automorphic.exists_conj_of_charpoly_eq hsepK
    (f' := Matrix.toLin' N) (by rw [Matrix.charpoly_toLin', Matrix.charpoly_toLin', hc₀, hc])
  set P := LinearMap.toMatrix' (e' : (Fin m → K) →ₗ[K] (Fin m → K)) with hP
  set Q := LinearMap.toMatrix' (e'.symm : (Fin m → K) →ₗ[K] (Fin m → K)) with hQ
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, ← LinearMap.toMatrix'_comp]
    have : (e' : (Fin m → K) →ₗ[K] (Fin m → K)) ∘ₗ (e'.symm : (Fin m → K) →ₗ[K] (Fin m → K)) =
        LinearMap.id := by ext v; simp
    rw [this, LinearMap.toMatrix'_id]
  have hQP : Q * P = 1 := by
    rw [hP, hQ, ← LinearMap.toMatrix'_comp]
    have : (e'.symm : (Fin m → K) →ₗ[K] (Fin m → K)) ∘ₗ (e' : (Fin m → K) →ₗ[K] (Fin m → K)) =
        LinearMap.id := by ext v; simp
    rw [this, LinearMap.toMatrix'_id]
  have hPN : P * N₀ = N * P := by
    have : (e' : (Fin m → K) →ₗ[K] (Fin m → K)) ∘ₗ Matrix.toLin' N₀ =
        Matrix.toLin' N ∘ₗ (e' : (Fin m → K) →ₗ[K] (Fin m → K)) :=
      LinearMap.ext fun v => he' v
    have h2 := congrArg LinearMap.toMatrix' this
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_toLin'] at h2

  set w : (K ⊗[F] B)ˣ := ⟨e.symm P, e.symm Q, by rw [← map_mul, hPQ, map_one],
    by rw [← map_mul, hQP, map_one]⟩ with hw
  refine exists_unit_conj_of_baseChange x₀ x w ?_
  apply e.injective
  rw [map_mul, map_mul]
  simp only [hw, Units.val_mk, AlgEquiv.apply_symm_apply]
  rw [← hN₀, ← hN, hPN]

end GlobalTheory.LKInv
end
