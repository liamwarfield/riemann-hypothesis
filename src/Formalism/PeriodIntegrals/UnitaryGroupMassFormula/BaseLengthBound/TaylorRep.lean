module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorRep
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

section Gen

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {d : ℕ} (g : Fin d → R)

def monSpan (k : ℕ) : Submodule R M where
  carrier := {x | ∃ cf : (Fin d → ℕ) → M, x = ∑ α ∈ Finset.Nat.antidiagonalTuple d k, (∏ i, g i ^ α i) • cf α}
  add_mem' := by
    rintro x y ⟨c1, rfl⟩ ⟨c2, rfl⟩
    exact ⟨c1 + c2, by simp [smul_add, Finset.sum_add_distrib]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro r x ⟨c1, rfl⟩
    exact ⟨r • c1, by simp [Finset.smul_sum, smul_comm r]⟩

theorem single_mem_monSpan {k : ℕ} {α : Fin d → ℕ} (hα : α ∈ Finset.Nat.antidiagonalTuple d k) (m : M) :
    (∏ i, g i ^ α i) • m ∈ monSpan (M := M) g k := by
  refine ⟨fun β => if β = α then m else 0, ?_⟩
  rw [Finset.sum_eq_single α]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hα h

theorem prod_pow_add_single (α : Fin d → ℕ) (i : Fin d) :
    (∏ l, g l ^ (α + Pi.single i 1 : Fin d → ℕ) l) = g i * ∏ l, g l ^ α l := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem pow_smul_top_le_monSpan (k : ℕ) :
    (Ideal.span (Set.range g)) ^ k • (⊤ : Submodule R M) ≤ monSpan (M := M) g k := by
  induction k with
  | zero =>
    intro x _
    refine ⟨fun _ => x, ?_⟩
    simp [Finset.Nat.antidiagonalTuple_zero_right]
  | succ k ih =>
    rw [pow_succ', Submodule.mul_smul, Submodule.smul_le]
    intro r hr n hn
    obtain ⟨cf, rfl⟩ := ih hn
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hr
    rw [Finset.sum_smul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun β hβ => ?_
    have hβ' : β + Pi.single i 1 ∈ Finset.Nat.antidiagonalTuple d (k + 1) := by
      rw [Finset.Nat.mem_antidiagonalTuple] at hβ ⊢
      simp [Finset.sum_add_distrib, hβ]
    have e : (a i • g i) • ((∏ l, g l ^ β l) • cf β) =
        (∏ l, g l ^ (β + Pi.single i 1 : Fin d → ℕ) l) • (a i • cf β) := by
      rw [smul_smul, smul_smul, prod_pow_add_single g β i, smul_eq_mul]
      congr 1
      ring
    rw [e]
    exact single_mem_monSpan g hβ' _

end Gen

theorem taylorRep_holds : TaylorRep := by
  intro D B P j X ka wL wF G la k x hx
  obtain ⟨cf, hcf⟩ := pow_smul_top_le_monSpan (M := ↥(HK X la G.w wF))
    (fun i : Fin (WeightFamilies.dimY D j) => sfr X la G.w i.succ) k hx
  refine ⟨cf, ?_⟩
  have : x - ∑ α ∈ mon D j k, ym G la α • cf α = 0 := by
    rw [sub_eq_zero]; exact hcf
  rw [this]
  exact Submodule.zero_mem _

end PoleLengthBounds
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.Column
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem inc_cast {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) {u u' : WeightFamilies.Wt D j}
    (h : u = u') (F : B.Cusp j u) : X.inc u' (h ▸ F) = X.inc u F := by
  subst h; rfl

theorem one_le_of_nonneg_of_ne {a : WithTop ℤ} (h0 : 0 ≤ a) (h1 : a ≠ 0) : 1 ≤ a := by
  induction a using WithTop.recTopCoe with
  | top => exact le_top
  | coe n =>
    have h2 : (0 : ℤ) ≤ n := by exact_mod_cast h0
    have h3 : n ≠ 0 := fun h => h1 (by rw [h]; rfl)
    exact_mod_cast (show (1 : ℤ) ≤ n by omega)

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem wfr_eq (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (jj : Fin G.N) :
    fr0 X la G.w 1 ⟨emb X la G.N (X.inc _ ((add_zero_weight_one_eq wL).symm ▸ G.w jj : B.Cusp j (addL (wt0 D j) wL 1))),
      emb_mem_Vw X la G.N _ _⟩ = wfr G la jj := by
  unfold wfr
  congr 1
  exact Subtype.ext (congrArg (emb X la G.N) (inc_cast X (add_zero_weight_one_eq wL).symm (G.w jj)))

theorem ord_wfr_nonneg (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B)
    (hT : Q.InTie S) (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (ζ : PtsG G la) (jj : Fin G.N) :
    0 ≤ ord (unifO X la G.N) ζ (toOsK X la G.w (wfr G la jj)) := by
  obtain ⟨hd1, hd2, -, -, -, hk, -⟩ := hT ζ
  have e := hk 1 ((add_zero_weight_one_eq wL).symm ▸ G.w jj : B.Cusp j (addL (wt0 D j) wL 1))
  rw [wfr_eq, inc_cast] at e
  have hv : X.depth S.sW wL la (Q.y ζ) ≤ X.vAt la (Q.y ζ) (X.inc wL (G.w jj)) := iInf₂_le _ (hw jj)
  have hd : X.depth S.sW wL la (Q.y ζ) = (((X.depth S.sW wL la (Q.y ζ)).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hd1 hd2).symm
  have hv' : (((X.depth S.sW wL la (Q.y ζ)).toReal : ℝ) : EReal) ≤ X.vAt la (Q.y ζ) (X.inc wL (G.w jj)) := by
    rw [← hd]; exact hv
  have hb := ereal_bound (ep := ep (unifO X la G.N) ζ) (T := 1) hd hv'
  have key : (((0 : ℤ) : ℝ) : EReal) ≤ toE (ord (unifO X la G.N) ζ (toOsK X la G.w (wfr G la jj))) := by
    rw [e]
    refine le_trans (le_of_eq ?_) hb
    simp
  simpa using le_of_coe_le_toE key

theorem one_eq_sum_wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    (1 : ↥(Frac0 X la G.w)) = ∑ k, (@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (Tv X la G.N (0, k))) • wfr G la k := by
  have h1 : frac X la G.w 1 (sec X la G.w 0) = 1 := by rw [frac_apply, pow_one, section_mul_inverse_eq_one]
  have h2 : frac X la G.w 1 (sec X la G.w 0) = ∑ k, (@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (Tv X la G.N (0, k))) •
      frac X la G.w 1 (emb X la G.N (X.inc wL (G.w k))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sec, map_sum]
    simp only [map_smul]
  apply Subtype.ext
  rw [OneMemClass.coe_one, ← h1, h2, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

theorem one_eq_sum_toOsK (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    (1 : OsK X la G.w) = ∑ k, algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N (0, k)) *
      toOsK X la G.w (wfr G la k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_one (toOsK X la G.w), one_eq_sum_wfr G la, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Algebra.smul_def, (IsScalarTower.algebraMap_apply (Op X la G.N) (Kp X la G.N) (OsK X la G.w) _).symm]

theorem one_le_ord_sum (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (ζ : PtsG G la) [IsDVRAt ζ]
    (h : IsUnif (OsK X la G.w) (unifO X la G.N)) (s : Finset (Fin G.N)) (f : Fin G.N → OsK X la G.w)
    (hf : ∀ k, 1 ≤ ord (unifO X la G.N) ζ (f k)) : 1 ≤ ord (unifO X la G.N) ζ (∑ k ∈ s, f k) := by
  classical
  refine Finset.induction_on s (by rw [Finset.sum_empty, ord_zero ζ h]; exact le_top) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha]
  exact (le_min (hf a) ih).trans (ord_add ζ h _ _)

theorem column_holds : Column := by
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw ζ
  have hC := hOk.2.1
  have hT := hOk.2.2.1
  have h := isUnif_of_curve Q hC
  have := isDVRAt_of_curve Q hC ζ
  refine ⟨fun jj => ord_wfr_nonneg G la Q S hT hw ζ jj, ?_⟩
  by_contra hne
  push Not at hne
  have hall : ∀ k, 1 ≤ ord (unifO X la G.N) ζ (algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N (0, k)) *
      toOsK X la G.w (wfr G la k)) := by
    intro k
    rw [ord_mul ζ h]
    have h0 : 0 ≤ ord (unifO X la G.N) ζ (algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N (0, k))) :=
      ord_nonneg ζ h (Subalgebra.algebraMap_mem _ _)
    have h1 := one_le_of_nonneg_of_ne (ord_wfr_nonneg G la Q S hT hw ζ k) (hne k)
    simpa using add_le_add h0 h1
  have h2 := one_le_ord_sum G la ζ h Finset.univ _ hall
  rw [← one_eq_sum_toOsK, ord_one ζ h] at h2
  exact absurd (WithTop.coe_le_coe.1 (show ((1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) from h2)) (by norm_num)

end PoleLengthBounds
end
end
