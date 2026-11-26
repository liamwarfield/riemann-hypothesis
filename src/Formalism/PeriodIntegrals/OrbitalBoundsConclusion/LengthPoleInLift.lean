module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.LeOrdASmulOsK
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorHasse
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FiltLenF
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiffGenLoc
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BallQuotLen

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PoleLengthBound
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiBallFromAlt
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

def PiLen : Prop :=
  ∀ (R M ι : Type) [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] (P Q : Submodule R M), Q ≤ P →
    Module.length R (↥(Submodule.pi Set.univ fun _ : ι => P) ⧸
        (Submodule.pi Set.univ fun _ : ι => Q).comap (Submodule.pi Set.univ fun _ : ι => P).subtype) =
      (Fintype.card ι : ℕ∞) * Module.length R (↥P ⧸ Q.comap P.subtype)

def BallQuot : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [IsReduced A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A]
    (ϖ : O), Irreducible ϖ → Module.Finite O ↥(As O A) → ∀ [∀ ζ : Pts O A, IsDVRAt ζ],
    ∀ (V : Type) [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower K A V] [Module O V]
      [IsScalarTower O A V] (e : V), IsGen A e → ∀ (c : Pts O A → ℤ) (m : Pts O A → ℕ),
      Module.length O (↥(ballO ϖ e (fun ζ => c ζ + m ζ)) ⧸
          (ballO ϖ e c).comap (ballO ϖ e (fun ζ => c ζ + m ζ)).subtype) =
        ((∑ᶠ ζ : Pts O A, m ζ * fdeg ζ : ℕ) : ℕ∞)

def PiBallFrom : Prop :=
  PiLen → BallQuot →
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T e : ℕ) (c : ℝ),
    Q.Ok S CRm T c → PiBallLen G la Q (Q.mm S T e)

end PI.PoleLengthCount
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.StepsOf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Closed
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.UnitCols
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem coe_wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (col : Fin G.N) :
    (PoleLengthBounds.wfr G la col : Lw X la G.w) =
      algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wL (G.w col))) * w0inv X la G.w := by
  simp only [PoleLengthBounds.wfr, coe_weightZeroFraction, frac_apply, pow_one]

theorem uSpec_wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    uSpec G la (fun col => toOsK X la G.w (PoleLengthBounds.wfr G la col)) :=
  fun col => ⟨PoleLengthBounds.wfr G la col, coe_wfr G la col, rfl⟩

theorem sum_T_wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    ∑ col, algebraMap (Kp X la G.N) ↥(Frac0 X la G.w)
      (@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col))) *
        PoleLengthBounds.wfr G la col = 1 := by
  apply Subtype.ext
  have h : ∀ col, ((algebraMap (Kp X la G.N) ↥(Frac0 X la G.w)
      (@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col))) *
        PoleLengthBounds.wfr G la col : ↥(Frac0 X la G.w)) : Lw X la G.w) =
      frac X la G.w 1 ((@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col))) •
        emb X la G.N (X.inc wL (G.w col))) := by
    intro col
    rw [LinearMap.map_smul, Algebra.smul_def]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_congr rfl fun col _ => h col, ← map_sum]
  show frac X la G.w 1 (sec X la G.w 0) = _
  rw [frac_apply, pow_one, section_mul_inverse_eq_one]
  rfl

theorem sum_T_u (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    ∑ col, algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col)) *
      toOsK X la G.w (PoleLengthBounds.wfr G la col) = 1 := by
  have := congrArg (toOsK X la G.w) (sum_T_wfr G la)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_one, map_sum] at this
  rw [← this]
  refine Finset.sum_congr rfl fun col _ => ?_
  rw [map_mul, AlgHom.commutes]
  rfl

theorem unitCols_of (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (hOrd : ∀ (ζ : PtsG G la) (col : Fin G.N), 0 ≤ ord (unifO X la G.N) ζ (toOsK X la G.w (PoleLengthBounds.wfr G la col))) :
    UnitCols G la :=
  ⟨fun col => toOsK X la G.w (PoleLengthBounds.wfr G la col), uSpec_wfr G la, sum_T_u G la, hOrd⟩

theorem unitCols_of_column (hCol : PoleLengthBounds.Column) (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la)
    (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ) (hOk : Q.Ok S CRm T c) (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) :
    UnitCols G la :=
  unitCols_of G la fun ζ col => (hCol G la Q S CRm T c hOk hw ζ).1 col

end PI.PoleLengthCount
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.ColDeriv
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem u_eq_wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) {u : Fin G.N → OsK X la G.w}
    (hu : uSpec G la u) (col : Fin G.N) : u col = toOsK X la G.w (PoleLengthBounds.wfr G la col) := by
  obtain ⟨f, hf, hfu⟩ := hu col
  have : f = PoleLengthBounds.wfr G la col := by
    apply Subtype.ext
    rw [hf]
    simp only [PoleLengthBounds.wfr, coe_weightZeroFraction, frac_apply, pow_one]
  rw [← hfu, this]

theorem uC_eq_pow (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (col : Fin G.N) {k : ℕ}
    (α : Mon (WeightFamilies.dimY D j) k) :
    PoleLengthBounds.uC G la col α.1 = toOsK X la G.w (PoleLengthBounds.wfr G la col) ^ k := by
  have h := α.2
  rw [Finset.Nat.mem_antidiagonalTuple] at h
  rw [PoleLengthBounds.uC, Finset.prod_pow_eq_pow_sum, h]

theorem colDeriv_of (hTH : PoleLengthBounds.TaylorHasse) (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    ColDeriv G la := by
  classical
  intro u hu k α α' col cf
  have hx : ((yPow X la G.w α.1 • cf : ↥(HK X la G.w wF)) : Lw X la G.w) ∈ HK X la G.w wF :=
    (yPow X la G.w α.1 • cf).2
  have h := hasse_preserves_kernel G la (colIdx D j col α'.1) _ hx
  let cf' : (Fin (WeightFamilies.dimY D j) → ℕ) → ↥(HK X la G.w wF) := fun β => if β = α.1 then cf else 0
  have hrem : (yPow X la G.w α.1 • cf : ↥(HK X la G.w wF)) -
      ∑ β ∈ PoleLengthBounds.mon D j k, PoleLengthBounds.ym G la β • cf' β ∈
        (Jid X la G.w ^ (k + 1) • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))) := by
    have : ∑ β ∈ PoleLengthBounds.mon D j k, PoleLengthBounds.ym G la β • cf' β = yPow X la G.w α.1 • cf := by
      rw [Finset.sum_eq_single α.1]
      · simp only [cf', if_pos rfl]; rfl
      · intro b _ hb; simp only [cf', if_neg hb, smul_zero]
      · intro hn; exact absurd α.2 hn
    rw [this, sub_self]
    exact Submodule.zero_mem _
  have key := hTH G la k _ cf' hrem col α'.1 α'.2 h
  rw [rD, dite_eq_left h]
  refine Eq.trans key ?_
  rw [uC_eq_pow G la col α', u_eq_wfr G la hu col]
  by_cases hαα : α = α'
  · subst hαα
    simp only [cf', ↓reduceIte]
  · have hne : α'.1 ≠ α.1 := fun e => hαα (Subtype.ext e.symm)
    simp only [cf', if_neg hne, if_neg hαα, map_zero, smul_zero]

end PI.PoleLengthCount
end
end

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem column_derivative (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : ColDeriv G la :=
  colDeriv_of PoleLengthBounds.taylorHasse_holds G la

theorem unit_columns_holds (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la)
    (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ) (hOk : Q.Ok S CRm T c) (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) :
    UnitCols G la :=
  unitCols_of_column PoleLengthBounds.column_holds G la Q S CRm T c hOk hw

end PI.PoleLengthCount
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Taylor
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem taylor_holds (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Taylor G la := by
  intro k x hx
  obtain ⟨cf, hcf⟩ := PoleLengthBounds.pow_smul_top_le_monSpan (M := ↥(HK X la G.w wF))
    (fun i : Fin (WeightFamilies.dimY D j) => sfr X la G.w i.succ) k hx
  refine ⟨fun α => cf α.1, 0, Submodule.zero_mem _, ?_⟩
  rw [add_zero, hcf]
  exact (Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple (WeightFamilies.dimY D j) k)
    (fun α => (∏ i, sfr X la G.w i.succ ^ α i) • cf α)).symm

end PI.PoleLengthCount
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Assemble
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.FiltOk
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps Finset.HasAntidiagonal

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem image_filtration_decreasing (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (T : ℕ) : FiltOk G la T := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    unfold Fk
    exact Submodule.span_mono (Set.image_mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)))
  · unfold Fk
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, Submodule.top_coe, Set.image_univ,
      (toWK_surjective X la G.w wF _).range_eq, Submodule.span_univ]
  · unfold Fk
    rw [eq_bot_iff, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_bot]
    exact (toWK_eq_zero_iff X la G.w wF _ x).2 hx

end PI.PoleLengthCount
end
end

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem colIdx_sum {N : ℕ} (col : Fin N) (α : Fin (WeightFamilies.dimY D j) → ℕ) :
    ((colIdx D j col α).sum fun _ n => n) = ∑ i, α i := by
  classical
  unfold colIdx
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp [Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem mon_sum {d k : ℕ} (α : Mon d k) : ∑ i, α.1 i = k := Finset.Nat.mem_antidiagonalTuple.1 α.2

theorem colIdx_mon {N : ℕ} (col : Fin N) {k : ℕ} (α : Mon (WeightFamilies.dimY D j) k) :
    ((colIdx D j col α.1).sum fun _ n => n) = k := by
  rw [colIdx_sum, mon_sum]

theorem exists_coef {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (hC : Q.InCurve)
    (u : Fin G.N → OsK X la G.w)
    (hs : ∑ col, algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col)) * u col = 1)
    (ho : ∀ (ζ : PtsG G la) col, 0 ≤ ord (unifO X la G.N) ζ (u col)) (k : ℕ) :
    ∃ a : Fin G.N → OsK X la G.w, (∀ col (ζ : PtsG G la), 0 ≤ ord (unifO X la G.N) ζ (a col)) ∧
      ∑ col, a col * u col ^ k = 1 := by
  have : ∀ ζ : PtsG G la, IsDVRAt ζ := isDVRAt_of_curve Q hC
  have hU := isUnif_of_curve Q hC
  have hu : ∀ col, u col ∈ As (Op X la G.N) (OsK X la G.w) := fun col => (mem_As_iff hU _).2 fun ζ => ho ζ col
  let u' : Fin G.N → ↥(As (Op X la G.N) (OsK X la G.w)) := fun col => ⟨u col, hu col⟩
  have h1 : Ideal.span (Set.range u') = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have e : (1 : ↥(As (Op X la G.N) (OsK X la G.w))) =
        ∑ col, algebraMap (Op X la G.N) ↥(As (Op X la G.N) (OsK X la G.w))
          (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col)) * u' col := by
      apply Subtype.ext
      simp only [u', OneMemClass.coe_one, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
        Subalgebra.coe_algebraMap]
      exact hs.symm
    rw [e]
    exact Ideal.sum_mem _ fun col _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨col, rfl⟩)
  have h2 := Ideal.span_pow_eq_top _ h1 k
  rw [← Set.range_comp] at h2
  have h3 : (1 : ↥(As (Op X la G.N) (OsK X la G.w))) ∈
      Ideal.span (Set.range ((fun x => x ^ k) ∘ u')) := by rw [h2]; trivial
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h3
  refine ⟨fun col => (c col : OsK X la G.w), fun col ζ => ord_nonneg ζ hU (c col).2, ?_⟩
  have := congrArg Subtype.val hc
  simpa [u'] using this

section

variable (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))

def psiRaw (a : Fin G.N → OsK X la G.w) (k : ℕ) (x : ↥(HK X la G.w wF)) : Vk G la k :=
  fun α => ∑ col, a col • rD G la (colIdx D j col α.1) x

theorem psiRaw_add (a : Fin G.N → OsK X la G.w) (k : ℕ) (x y : ↥(HK X la G.w wF)) :
    psiRaw G la a k (x + y) = psiRaw G la a k x + psiRaw G la a k y := by
  funext α
  simp only [psiRaw, Pi.add_apply, rD_add, smul_add, Finset.sum_add_distrib]

theorem psiRaw_smul (a : Fin G.N → OsK X la G.w) (k : ℕ) (r : Op X la G.N) (x : ↥(HK X la G.w wF))
    (hx : x ∈ Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))) :
    psiRaw G la a k (@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ r • x) = r • psiRaw G la a k x := by
  funext α
  simp only [psiRaw, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun col _ => ?_
  calc
    _ = a col • (r • rD G la (colIdx D j col α.1) x) :=
      congrArg (fun y => a col • y)
        (restricted_derivative_linear G la k _ r x hx (le_of_eq (colIdx_mon col α)))
    _ = _ := smul_comm _ _ _

theorem psiRaw_congr (a : Fin G.N → OsK X la G.w) {k T : ℕ} (hk : k < a0 D j T) {x x' : ↥(HK X la G.w wF)}
    (h : toWK X la G.w wF (a0 D j T) x = toWK X la G.w wF (a0 D j T) x') : psiRaw G la a k x = psiRaw G la a k x' := by
  have hd : x - x' ∈ Jid X la G.w ^ a0 D j T • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) := by
    rw [← toWK_eq_zero_iff, map_sub, h, sub_self]
  have hd' : x - x' ∈ Jid X la G.w ^ (k + 1) • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right hk) hd
  funext α
  unfold psiRaw
  refine Finset.sum_congr rfl fun col _ => ?_
  have e : x = x' + (x - x') := by abel
  rw [e, rD_add, vanishingOnQuadric G la (k + 1) _ _ hd' (by rw [colIdx_mon col α]; omega), add_zero]

theorem exists_of_mem_Fk {T k : ℕ} {z : WK X la G.w wF (a0 D j T)} (hz : z ∈ Fk G la T k) :
    ∃ x : ↥(HK X la G.w wF), x ∈ Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) ∧
      toWK X la G.w wF (a0 D j T) x = z := by
  unfold Fk at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, hx, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add z1 z2 _ _ h1 h2 =>
    obtain ⟨x1, hx1, rfl⟩ := h1
    obtain ⟨x2, hx2, rfl⟩ := h2
    exact ⟨x1 + x2, Submodule.add_mem _ hx1 hx2, map_add _ _ _⟩
  | smul r z _ h =>
    obtain ⟨x, hx, rfl⟩ := h
    refine ⟨@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ r • x, Submodule.smul_of_tower_mem _ _ hx, ?_⟩
    rw [LinearMap.map_smul_of_tower]
    rfl

def pre {T k : ℕ} {z : WK X la G.w wF (a0 D j T)} (hz : z ∈ Fk G la T k) : ↥(HK X la G.w wF) :=
  Classical.choose (exists_of_mem_Fk G la hz)

theorem pre_mem {T k : ℕ} {z : WK X la G.w wF (a0 D j T)} (hz : z ∈ Fk G la T k) :
    pre G la hz ∈ Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) :=
  (Classical.choose_spec (exists_of_mem_Fk G la hz)).1

theorem pre_eq {T k : ℕ} {z : WK X la G.w wF (a0 D j T)} (hz : z ∈ Fk G la T k) :
    toWK X la G.w wF (a0 D j T) (pre G la hz) = z :=
  (Classical.choose_spec (exists_of_mem_Fk G la hz)).2

def psiL (a : Fin G.N → OsK X la G.w) (T k : ℕ) (hk : k < a0 D j T) :
    ↥(Fk G la T k) →ₗ[Op X la G.N] Vk G la k where
  toFun z := psiRaw G la a k (pre G la z.2)
  map_add' z1 z2 := by
    rw [← psiRaw_add]
    apply psiRaw_congr G la a hk
    rw [map_add (f := _), pre_eq, pre_eq, pre_eq]
    rfl
  map_smul' r z := by
    rw [RingHom.id_apply, ← psiRaw_smul G la a k r _ (pre_mem G la z.2)]
    apply psiRaw_congr G la a hk
    rw [LinearMap.map_smul_of_tower, pre_eq, pre_eq]
    rfl

def psiF (a : ℕ → Fin G.N → OsK X la G.w) (T : ℕ) : ∀ k, ↥(Fk G la T k) →ₗ[Op X la G.N] Vk G la k :=
  fun k => if hk : k < a0 D j T then psiL G la (a k) T k hk else 0

theorem psiF_lt (a : ℕ → Fin G.N → OsK X la G.w) {T k : ℕ} (hk : k < a0 D j T) (z : ↥(Fk G la T k))
    (x : ↥(HK X la G.w wF)) (hx : toWK X la G.w wF (a0 D j T) x = z) :
    psiF G la a T k z = psiRaw G la (a k) k x := by
  unfold psiF
  rw [dite_eq_left hk]
  exact psiRaw_congr G la (a k) hk ((pre_eq G la z.2).trans hx.symm)

theorem taylorRead (hE5 : ColDeriv G la) (u : Fin G.N → OsK X la G.w) (hu : uSpec G la u) (k : ℕ)
    (a : Fin G.N → OsK X la G.w) (ha : ∑ col, a col * u col ^ k = 1) (cf : Mon (WeightFamilies.dimY D j) k → ↥(HK X la G.w wF))
    (r : ↥(HK X la G.w wF))
    (hr : r ∈ Jid X la G.w ^ (k + 1) • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)))
    (α' : Mon (WeightFamilies.dimY D j) k) :
    psiRaw G la a k (∑ α, yPow X la G.w α.1 • cf α + r) α' = toA0K X la G.w wF (cf α') := by
  have h1 : ∀ col, rD G la (colIdx D j col α'.1) (∑ α, yPow X la G.w α.1 • cf α + r) =
      u col ^ k • toA0K X la G.w wF (cf α') := by
    intro col
    rw [rD_add, rD_sum, vanishingOnQuadric G la (k + 1) _ r hr (by rw [colIdx_mon col α']; omega), add_zero]
    simp only [hE5 u hu k _ α' col]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  unfold psiRaw
  simp only [h1, smul_smul]
  rw [← Finset.sum_smul, ha, one_smul]

end

theorem ordV_shift (t : WithTop ℤ) (c m : ℤ) (h : ((-m : ℤ) : WithTop ℤ) ≤ t + (c : WithTop ℤ)) :
    0 ≤ t + ((c + m : ℤ) : WithTop ℤ) := by
  induction t using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    rw [← WithTop.coe_add] at h ⊢
    have := WithTop.coe_le_coe.1 h
    exact_mod_cast (show (0 : ℤ) ≤ n + (c + m) by omega)

theorem pole_length_assemble : Assemble := by
  intro D B P j X ka wL wF G la Q S CRm T e c hOk hw hL _ _ hE3 hE4 hE5 _ hE7
  have hC := hOk.2.1
  have : ∀ ζ : PtsG G la, IsDVRAt ζ := isDVRAt_of_curve Q hC
  have hU := isUnif_of_curve Q hC
  obtain ⟨u, hu, hs, ho⟩ := hE3
  choose a ha1 ha2 using exists_coef Q hC u hs ho
  refine ⟨psiF G la a T, ?_, ?_, ?_⟩
  · intro k z hz0
    by_cases hk : k < a0 D j T
    · obtain ⟨x, hx, hxz⟩ := exists_of_mem_Fk G la z.2
      rw [psiF_lt G la a hk z x hxz] at hz0
      obtain ⟨cf, r, hr, hxe⟩ := hE4 k x hx
      have hc : ∀ α, toA0K X la G.w wF (cf α) = 0 := fun α => by
        rw [← taylorRead G la hE5 u hu k (a k) (ha2 k) cf r hr α, ← hxe, hz0]
        rfl
      have hx' : x ∈ Jid X la G.w ^ (k + 1) • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) := by
        rw [hxe]
        refine Submodule.add_mem _ (Submodule.sum_mem _ fun α _ => ?_) hr
        have h1 : yPow X la G.w α.1 ∈ Jid X la G.w ^ k := by
          have := prod_sfr_mem X la G.w α.1
          rwa [mon_sum] at this
        have h2 : cf α ∈ Jid X la G.w • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) :=
          (reduction_eq_zero_iff_mem_ideal_smul X la G.w wF _).1 (hc α)
        rw [pow_succ, Submodule.mul_smul]
        exact Submodule.smul_mem_smul h1 h2
      rw [← hxz]
      exact Submodule.subset_span ⟨x, hx', rfl⟩
    · have h0 : (z : WK X la G.w wF (a0 D j T)) ∈ Fk G la T (a0 D j T) :=
        (image_filtration_decreasing G la T).1 (by omega) z.2
      rw [(image_filtration_decreasing G la T).2.2, Submodule.mem_bot] at h0
      rw [h0]
      exact Submodule.zero_mem _
  · intro k hk
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨x, -, hxz⟩ := exists_of_mem_Fk G la z.2
    have hg := good_of_mem_AAp hC (m := Q.mm S T e) (by omega) hz x hxz
    rw [psiF_lt G la a hk z x hxz]
    unfold Pk
    rw [Submodule.mem_pi]
    intro α _
    rw [mem_ballO_iff _ hU hC.2.2]
    intro ζ
    have key : ((-(Q.mm S T e ζ : ℤ) : ℤ) : WithTop ℤ) ≤ Q.ordA ζ (psiRaw G la (a k) k x α) :=
      le_ordA_sum Q hC ζ _ _ _ fun col _ => le_ordA_smul_OsK Q hC ζ _ (ha1 k col ζ) _ _
        (hg _ (by rw [colIdx_mon col α]; omega) ζ)
    exact ordV_shift _ _ _ key
  · intro k hk b hb
    unfold Qk at hb
    rw [Submodule.mem_pi] at hb
    choose x hx1 hx2 using fun α => hL (b α) (hb α (Set.mem_univ _))
    set Xs : ↥(HK X la G.w wF) := ∑ α, yPow X la G.w α.1 • x α with hXs
    have hX : Xs ∈ Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) := by
      refine Submodule.sum_mem _ fun α _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
      have := prod_sfr_mem X la G.w α.1
      rwa [mon_sum] at this
    have hXA : toWK X la G.w wF (a0 D j T) Xs ∈ Q.AA T := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hXs, map_sum]
      exact Submodule.sum_mem _ fun α _ => hE7 (x α) α.1 (hx2 α)
    refine ⟨⟨_, Submodule.subset_span ⟨Xs, hX, rfl⟩⟩, hXA, ?_⟩
    rw [psiF_lt G la a hk _ Xs rfl]
    funext α'
    have := taylorRead G la hE5 u hu k (a k) (ha2 k) x 0 (Submodule.zero_mem _) α'
    rw [add_zero] at this
    rw [this, hx1]

end PI.PoleLengthCount
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.LiftMul
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps Finset.HasAntidiagonal

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

section

variable {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la)

def IntD (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (f : Lw X la G.w) : Prop :=
  ∀ γ : Idx D j G.N →₀ ℕ, ∃ g : ↥(Frac0 X la G.w), (g : Lw X la G.w) = hasse X la G.w γ f ∧
    ∀ ζ : PtsG G la, 0 ≤ ord (unifO X la G.N) ζ (toOsK X la G.w g)

variable {Q}

theorem ord_sum_nonneg (hC : Q.InCurve) (ζ : PtsG G la) {ι : Type*} (s : Finset ι) (f : ι → OsK X la G.w)
    (h : ∀ i ∈ s, 0 ≤ ord (unifO X la G.N) ζ (f i)) : 0 ≤ ord (unifO X la G.N) ζ (∑ i ∈ s, f i) := by
  classical
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, ord_zero ζ hU]; exact le_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))
      (ord_add ζ hU _ _)

theorem ord_mul_nonneg (hC : Q.InCurve) (ζ : PtsG G la) {x y : OsK X la G.w} (hx : 0 ≤ ord (unifO X la G.N) ζ x)
    (hy : 0 ≤ ord (unifO X la G.N) ζ y) : 0 ≤ ord (unifO X la G.N) ζ (x * y) := by
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  rw [ord_mul ζ hU]
  exact add_nonneg hx hy

theorem ord_prod_nonneg (hC : Q.InCurve) (ζ : PtsG G la) {ι : Type*} (s : Finset ι) (f : ι → OsK X la G.w)
    (h : ∀ i ∈ s, 0 ≤ ord (unifO X la G.N) ζ (f i)) : 0 ≤ ord (unifO X la G.N) ζ (∏ i ∈ s, f i) := by
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  refine Finset.prod_induction f (fun x => 0 ≤ ord (unifO X la G.N) ζ x) (fun x y hx hy => ord_mul_nonneg hC ζ hx hy)
    ?_ h
  rw [ord_one ζ hU]

theorem ord_pow_nonneg (hC : Q.InCurve) (ζ : PtsG G la) {x : OsK X la G.w} (hx : 0 ≤ ord (unifO X la G.N) ζ x)
    (n : ℕ) : 0 ≤ ord (unifO X la G.N) ζ (x ^ n) := by
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  rw [ord_pow ζ hU]
  exact nsmul_nonneg hx n

theorem intD_mul (hC : Q.InCurve) {f1 f2 : Lw X la G.w} (h1 : IntD G la f1) (h2 : IntD G la f2) :
    IntD G la (f1 * f2) := by
  intro γ
  choose g1 hg1 ho1 using h1
  choose g2 hg2 ho2 using h2
  refine ⟨∑ q ∈ antidiagonal γ, g1 q.1 * g2 q.2, ?_, fun ζ => ?_⟩
  · show _ = PI.HJP.H X la G.w γ (f1 * f2)
    rw [PI.HJP.H_mul]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hg1, hg2]
    rfl
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine ord_sum_nonneg hC ζ _ _ fun q _ => ?_
    rw [map_mul]
    exact ord_mul_nonneg hC ζ (ho1 _ ζ) (ho2 _ ζ)

theorem intD_one (hC : Q.InCurve) : IntD G la (1 : Lw X la G.w) := by
  classical
  have hU := isUnif_of_curve Q hC
  intro γ
  refine ⟨if γ = 0 then 1 else 0, ?_, fun ζ => ?_⟩
  · show _ = MvPowerSeries.coeff γ (tayLc X la G.w 1)
    rw [map_one, MvPowerSeries.coeff_one]
    split_ifs <;> rfl
  · have := isDVRAt_of_curve Q hC ζ
    split_ifs
    · rw [map_one, ord_one ζ hU]
    · rw [map_zero, ord_zero ζ hU]; exact le_top

theorem intD_prod (hC : Q.InCurve) {ι : Type*} (s : Finset ι) (f : ι → Lw X la G.w) (h : ∀ i ∈ s, IntD G la (f i)) :
    IntD G la (∏ i ∈ s, f i) :=
  Finset.prod_induction f (fun x => IntD G la x) (fun _ _ hx hy => intD_mul hC hx hy) (intD_one hC) h

theorem intD_pow (hC : Q.InCurve) {f : Lw X la G.w} (hf : IntD G la f) (n : ℕ) : IntD G la (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact intD_one hC
  | succ n ih => rw [pow_succ]; exact intD_mul hC ih hf

theorem intD_sfr (hC : Q.InCurve) (u : Fin G.N → OsK X la G.w) (hu : uSpec G la u)
    (ho : ∀ (ζ : PtsG G la) col, 0 ≤ ord (unifO X la G.N) ζ (u col)) (i : Fin (WeightFamilies.dimY D j + 1)) :
    IntD G la (sfr X la G.w i : Lw X la G.w) := by
  classical
  have hU := isUnif_of_curve Q hC
  choose fk hfk1 hfk2 using hu
  choose mq hmq hfq using fun q : Idx D j G.N →₀ ℕ => PI.HasseOrdBdW.compositionalInverseSymm X la G.w 1 q
  intro γ
  set c : (Idx D j G.N →₀ ℕ) → Fin G.N → Kp X la G.N :=
    fun q k => @algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (hasseOp X la G.N q (Tv X la G.N (i, k))) with hc
  refine ⟨∑ q ∈ antidiagonal γ, (mq q.2 : ↥(Frac0 X la G.w)) *
      ((∑ k, c q.1 k • fk k) * ∏ k, fk k ^ q.2 ((0 : Fin (WeightFamilies.dimY D j + 1)), k)), ?_, fun ζ => ?_⟩
  · have e0 : (sfr X la G.w i : Lw X la G.w) =
        algebraMap (Rp X la G.N) (Lw X la G.w) (sec X la G.w i) * w0inv X la G.w ^ 1 := by
      rw [coe_sfr, frac_apply]
    show _ = PI.HJP.H X la G.w γ (sfr X la G.w i : Lw X la G.w)
    rw [e0, PI.HJP.H_mul]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    have hA : PI.HJP.H X la G.w q.1 (algebraMap (Rp X la G.N) (Lw X la G.w) (sec X la G.w i)) =
        algebraMap (Rp X la G.N) (Lw X la G.w) (∑ k, c q.1 k • emb X la G.N (X.inc wL (G.w k))) := by
      exact (hasse_algebraMap X la G.w q.1 (sec X la G.w i)).trans
        (congrArg (algebraMap (Rp X la G.N) (Lw X la G.w)) (by
          simpa only [hc] using hasseRp_sec X la G.w q.1 i))
    have hB : PI.HJP.H X la G.w q.2 (w0inv X la G.w ^ 1) = (mq q.2 : Lw X la G.w) *
        algebraMap (Rp X la G.N) (Lw X la G.w) (∏ k, emb X la G.N (X.inc wL (G.w k)) ^ q.2 (0, k)) *
          w0inv X la G.w ^ (1 + q.2.sum fun _ n => n) := hfq q.2
    rw [hA, hB]
    by_cases hm : mq q.2 = 0
    · simp [hm]
    · have hn := hmq q.2 hm
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hfk1, map_sum, map_prod, map_pow, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply (Kp X la G.N) (Rp X la G.N) (Lw X la G.w)]
      rw [← hn, pow_add, ← Finset.prod_pow_eq_pow_sum]
      simp only [mul_pow, Finset.prod_mul_distrib]
      have e1 : ∀ (A E : Fin G.N → Lw X la G.w) (y : Lw X la G.w),
          ∑ k, A k * (E k * y) = (∑ k, A k * E k) * y := fun A E y => by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
      rw [e1]
      ring
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine ord_sum_nonneg hC ζ _ _ fun q _ => ?_
    have := isDVRAt_of_curve Q hC ζ
    rw [map_mul, map_mul, map_intCast]
    refine ord_mul_nonneg hC ζ (ord_nonneg ζ hU (intCast_mem _ _)) (ord_mul_nonneg hC ζ ?_ ?_)
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine ord_sum_nonneg hC ζ _ _ fun k _ => ?_
      rw [map_smul, hfk2, hc, algebraMap_smul, Algebra.smul_def]
      exact ord_mul_nonneg hC ζ (ord_nonneg ζ hU (Subalgebra.algebraMap_mem _ _)) (ho ζ k)
    · rw [map_prod]
      refine ord_prod_nonneg hC ζ _ _ fun k _ => ?_
      rw [map_pow, hfk2]
      exact ord_pow_nonneg hC ζ (ho ζ k) _

theorem intD_yPow (hC : Q.InCurve) (u : Fin G.N → OsK X la G.w) (hu : uSpec G la u)
    (ho : ∀ (ζ : PtsG G la) col, 0 ≤ ord (unifO X la G.N) ζ (u col)) (α : Fin (WeightFamilies.dimY D j) → ℕ) :
    IntD G la (yPow X la G.w α : Lw X la G.w) := by
  have e : (yPow X la G.w α : Lw X la G.w) = ∏ i, (sfr X la G.w i.succ : Lw X la G.w) ^ α i := by
    unfold yPow
    push_cast
    rfl
  rw [e]
  exact intD_prod hC _ _ fun i _ => intD_pow hC (intD_sfr hC u hu ho i.succ) _

theorem good_mul (hC : Q.InCurve) {T : ℕ} {f : ↥(Frac0 X la G.w)} (hf : IntD G la (f : Lw X la G.w))
    {x : ↥(HK X la G.w wF)} (hx : GoodP Q T (fun _ => 0) x) : GoodP Q T (fun _ => 0) (f • x) := by
  choose g hg ho using hf
  have hP := hasse_preserves_kernel G la
  intro β hβ ζ
  rw [rD_eq G la β _ (hP β _ (f • x).2)]
  have e : (⟨_, hP β _ (f • x).2⟩ : ↥(HK X la G.w wF)) =
      ∑ q ∈ antidiagonal β, g q.1 • (⟨_, hP q.2 _ x.2⟩ : ↥(HK X la G.w wF)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    show PI.HJP.H X la G.w β ((f : Lw X la G.w) * (x : Lw X la G.w)) = _
    rw [PI.HJP.H_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Submodule.coe_smul]
    exact (congrArg (· * hasse X la G.w q.2 (x : Lw X la G.w)) (hg q.1)).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  refine le_ordA_sum Q hC ζ _ _ _ fun q hq => ?_
  rw [LinearMap.map_smul, ← algebraMap_smul (OsK X la G.w) (g q.1)]
  refine le_ordA_smul_OsK Q hC ζ _ (ho q.1 ζ) _ _ ?_
  have hq2 : (q.2.sum fun _ n => n) ≤ a0 D j T - 1 := by
    rw [mem_antidiagonal] at hq
    rw [PI.HJP.sum_eq_degree] at hβ ⊢
    have : Finsupp.degree β = Finsupp.degree q.1 + Finsupp.degree q.2 := by rw [← hq, map_add (f := _)]
    omega
  have := hx q.2 hq2 ζ
  rwa [rD_eq G la q.2 x (hP q.2 _ x.2)] at this

end

theorem liftMul_of {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (T : ℕ) (hC : Q.InCurve)
    (h3 : UnitCols G la) : LiftMul G la Q T := by
  obtain ⟨u, hu, -, ho⟩ := h3
  intro x α hx
  by_cases ha : 0 < a0 D j T
  · have hg := good_of_mem_AAp hC ha hx x rfl
    have hg' := good_mul hC (intD_yPow (Q := Q) hC u hu ho α) hg
    have hP := hasse_preserves_kernel G la
    refine Submodule.subset_span ⟨yPow X la G.w α • x, ⟨fun β _ => hP β _ (yPow X la G.w α • x).2, fun β hβ ζ => ?_⟩, rfl⟩
    have := hg' β hβ ζ
    rwa [rD_eq G la β _ (hP β _ (yPow X la G.w α • x).2)] at this
  · have h0 : ∀ y : ↥(HK X la G.w wF), toWK X la G.w wF (a0 D j T) y = 0 := fun y => by
      rw [toWK_eq_zero_iff, show a0 D j T = 0 by omega, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    rw [h0]
    exact Submodule.zero_mem _

end PI.PoleLengthCount
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiBallFrom
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

theorem ball_product_length : PiBallFrom := by
  intro hPi hBQ D B P j X ka wL wF G la Q S CRm T e c hOk k

  have hC : Q.InCurve := hOk.2.1
  haveI : FiniteDimensional (Kp X la G.N) (OsK X la G.w) := hC.1
  haveI : IsReduced (OsK X la G.w) := hC.2.1
  haveI : ∀ ζ : PtsG G la, IsDVRAt ζ := isDVRAt_of_curve Q hC
  have hU := isUnif_of_curve Q hC

  have hle : ballO (unifO X la G.N) Q.e Q.c ≤
      ballO (unifO X la G.N) Q.e (fun ζ => Q.c ζ + ((Q.mm S T e ζ : ℕ) : ℤ)) := by
    intro v hv
    exact ball_mono hU hC.2.2 (fun ζ => by dsimp only; omega) hv

  have h1 := hPi (Op X la G.N) (SectionSheafQuotient X la G.w wF) (Mon (WeightFamilies.dimY D j) k)
    (ballO (unifO X la G.N) Q.e (fun ζ => Q.c ζ + ((Q.mm S T e ζ : ℕ) : ℤ)))
    (ballO (unifO X la G.N) Q.e Q.c) hle
  have h2 := hBQ (Op X la G.N) (Kp X la G.N) (OsK X la G.w) (unifO X la G.N)
    (unifO_irreducible X la G.N) (finite_As_of_curve Q hC) (SectionSheafQuotient X la G.w wF) Q.e hC.2.2 Q.c (Q.mm S T e)
  refine h1.trans ?_
  rw [h2, Fintype.card_coe, Nat.cast_mul]

end PI.PoleLengthCount
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiLenHolds
noncomputable section

namespace PI.PoleLengthCount

open Module

theorem piLen_holds : PiLen := by
  intro R M ι _ _ _ _ P Q _
  classical
  set PP := Submodule.pi Set.univ fun _ : ι => P
  set QQ := Submodule.pi Set.univ fun _ : ι => Q
  let q : Submodule R ↥P := Q.comap P.subtype
  let g : ι → (↥PP →ₗ[R] ↥P) := fun i =>
    ((LinearMap.proj i).comp PP.subtype).codRestrict P (fun x => x.2 i (Set.mem_univ i))
  let f : ↥PP →ₗ[R] (ι → ↥P ⧸ q) := LinearMap.pi fun i => q.mkQ.comp (g i)
  have hker : QQ.comap PP.subtype = LinearMap.ker f := by
    ext x
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker, f, QQ,
      Submodule.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h
      funext i
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      exact h i
    · intro h i
      have := congrFun h i
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero] at this
      exact this
  have hsurj : Function.Surjective f := by
    intro y
    choose p hp using fun i => Submodule.Quotient.mk_surjective q (y i)
    refine ⟨⟨fun i => (p i : M), fun i _ => (p i).2⟩, ?_⟩
    funext i
    simp only [f, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [← hp i]
    rfl
  have e1 := (Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective f hsurj)
  rw [e1.length_eq, Module.length_pi, ENat.card_eq_coe_fintype_card]

end PI.PoleLengthCount
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.AALeAAp
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem AA_le_AAp' (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (T : ℕ)
    (m : PtsG G la → ℕ) : Q.AA T ≤ Q.AAp T m := by
  refine Submodule.span_mono (Set.image_mono ?_)
  rintro x ⟨hx, hb⟩
  refine ⟨hx, fun β hβ ζ => le_trans (WithTop.coe_le_coe.2 ?_) (hb β hβ ζ)⟩
  dsimp only
  omega

theorem bound (hF : FiltStep) (hM : MonCount) (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (Q : LocalPointData G la) (T : ℕ) (m : PtsG G la → ℕ)
    (h1 : FiltOk G la T) (h2 : GradedCoef G la Q T m) (h3 : PiBallLen G la Q m) :
    Module.length (Op X la G.N) (↥(Q.AAp T m) ⧸ (Q.AA T).comap (Q.AAp T m).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * ∑ᶠ ζ, m ζ * fdeg ζ : ℕ) : ℕ∞) := by
  obtain ⟨ψ, hker, hP, hQ⟩ := h2
  refine (hF (Op X la G.N) (WK X la G.w wF (a0 D j T)) (Fk G la T) (a0 D j T) h1.1 h1.2.1 h1.2.2
    (fun k => Vk G la k) ψ hker (Q.AAp T m) (Q.AA T) (fun k => Pk G la Q m k) (fun k => Qk G la Q k)
    (AA_le_AAp' G la Q T m) hP hQ).trans ?_
  refine (Finset.sum_le_sum (fun k _ => (h3 k).le)).trans ?_
  rw [← Nat.cast_sum, Nat.cast_le, ← Finset.sum_mul]
  refine Nat.mul_le_mul_right _ ?_
  by_cases hT : WeightFamilies.dimY D j < T
  · rw [show a0 D j T = T - WeightFamilies.dimY D j from rfl, hM _ _ hT]
  · rw [show a0 D j T = 0 from by simp only [a0]; omega]
    simp

theorem target (hF : FiltStep) (hM : MonCount) (hS : Steps) : PI.LengthPoleInLift := by
  intro D B P j X ka wL wF G la Q S CRm T e c hOk hw hL
  obtain ⟨h1, h2, h3⟩ := hS G la Q S CRm T e c hOk hw hL
  exact bound hF hM G la Q T _ h1 h2 h3

end PI.PoleLengthCount
end
end

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

theorem steps_of (hBQ : BallQuot) : Steps := by
  intro D B P j X ka wL wF G la Q S CRm T e c hOk hw hL
  have h3 := unit_columns_holds G la Q S CRm T c hOk hw
  exact ⟨image_filtration_decreasing G la T,
    pole_length_assemble G la Q S CRm T e c hOk hw hL (hasse_preserves_kernel G la) (vanishingOnQuadric G la) h3 (taylor_holds G la)
      (column_derivative G la) (restricted_derivative_linear G la) (liftMul_of Q T hOk.2.1 h3),
    ball_product_length piLen_holds hBQ G la Q S CRm T e c hOk⟩

theorem pole_length_bound_of_balls (hBQ : BallQuot) : PI.LengthPoleInLift := target filtration_length_bound sum_antidiagonalTuple (steps_of hBQ)

end PI.PoleLengthCount
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.BallQuot
noncomputable section

namespace PI.PoleLengthCount

theorem pole_ballQuot : BallQuot := ball_quotient_length

end PI.PoleLengthCount
end
end

namespace PI.PoleLengthCount

theorem pole_length_bound : PI.LengthPoleInLift := pole_length_bound_of_balls pole_ballQuot

end PI.PoleLengthCount
end

theorem length_pole_t0 : PI.LengthPoleInLift := PI.PoleLengthCount.pole_length_bound
